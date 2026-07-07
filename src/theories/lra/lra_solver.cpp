#include "theories/lra/lra_solver.h"

#include <algorithm>
#include <cassert>
#include <limits>
#include <set>
#include <sstream>
#include <stdexcept>
#include <utility>

namespace llm2smt::lra {

void LinearExpr::add_var(const std::string& name, const Rational& coeff) {
    if (coeff.is_zero()) return;
    auto& slot = coeffs[name];
    slot += coeff;
    if (slot.is_zero()) coeffs.erase(name);
}

void LinearExpr::add(const LinearExpr& other, const Rational& scale_by) {
    constant += other.constant * scale_by;
    for (const auto& [v, c] : other.coeffs) add_var(v, c * scale_by);
}

void LinearExpr::scale(const Rational& q) {
    constant *= q;
    if (q.is_zero()) {
        coeffs.clear();
        return;
    }
    for (auto& [_, c] : coeffs) c *= q;
}

void LraSolver::declare_real(const std::string& name) {
    if (real_decl_seen_.emplace(name, true).second) real_decls_.push_back(name);
    ensure_real_var(name);
}

Relation LraSolver::negate_rel(Relation r) {
    switch (r) {
    case Relation::Le: return Relation::Gt;
    case Relation::Lt: return Relation::Ge;
    case Relation::Ge: return Relation::Lt;
    case Relation::Gt: return Relation::Le;
    case Relation::Eq: return Relation::Ne;
    case Relation::Ne: return Relation::Eq;
    }
    return Relation::Eq;
}

std::string LraSolver::atom_key(const Atom& atom) {
    std::ostringstream os;
    os << static_cast<int>(atom.rel) << ":" << atom.lhs_minus_rhs.constant << ":";
    for (const auto& [v, c] : atom.lhs_minus_rhs.coeffs) os << v << "=" << c << ";";
    return os.str();
}

int LraSolver::new_tableau_var(bool basic) {
    int v = next_lra_var_++;
    if (static_cast<int>(is_basic_.size()) <= v) {
        is_basic_.resize(v + 1);
        row_of_basic_.resize(v + 1, -1);
        beta_.resize(v + 1);
        lower_.resize(v + 1);
        upper_.resize(v + 1);
        var_to_real_.resize(v + 1);
        atoms_by_var_.resize(v + 1);
        lower_atoms_by_var_.resize(v + 1);
        upper_atoms_by_var_.resize(v + 1);
        prop_var_dirty_.resize(v + 1);
        if (row_index_enabled()) rows_by_var_.resize(v + 1);
    }
    is_basic_[v] = basic;
    if (basic) basic_vars_.push_back(v);
    else nonbasic_vars_.push_back(v);
    if (stats_) stats_->lra_max_columns = std::max<uint64_t>(
        stats_->lra_max_columns, static_cast<uint64_t>(next_lra_var_));
    return v;
}

void LraSolver::register_row_coeffs(int row_idx) {
    if (!row_index_enabled()) return;
    if (row_idx < 0 || static_cast<size_t>(row_idx) >= rows_.size()) return;
    for (const auto& [v, _] : rows_[row_idx].coeffs) {
        if (v < 0) continue;
        if (static_cast<size_t>(v) >= rows_by_var_.size()) rows_by_var_.resize(v + 1);
        rows_by_var_[v].push_back(row_idx);
    }
}

void LraSolver::unregister_row_coeffs(int row_idx) {
    if (!row_index_enabled()) return;
    if (row_idx < 0 || static_cast<size_t>(row_idx) >= rows_.size()) return;
    for (const auto& [v, _] : rows_[row_idx].coeffs) {
        if (v < 0 || static_cast<size_t>(v) >= rows_by_var_.size()) continue;
        auto& rs = rows_by_var_[v];
        auto it = std::find(rs.begin(), rs.end(), row_idx);
        if (it != rs.end()) {
            *it = rs.back();
            rs.pop_back();
        }
    }
}

int LraSolver::ensure_real_var(const std::string& name) {
    auto it = real_to_var_.find(name);
    if (it != real_to_var_.end()) return it->second;
    int v = new_tableau_var(false);
    real_to_var_[name] = v;
    var_to_real_[v] = name;
    if (stats_) ++stats_->lra_real_vars;
    return v;
}

int LraSolver::ensure_term_var(const LinearExpr& expr) {
    std::ostringstream os;
    os << expr.constant << ":";
    for (const auto& [name, coeff] : expr.coeffs) os << name << "=" << coeff << ";";
    std::string key = os.str();
    auto it = term_var_keys_.find(key);
    if (it != term_var_keys_.end()) return it->second;

    int s = new_tableau_var(true);
    if (stats_) ++stats_->lra_term_vars;
    TableauRow row;
    row.constant = DeltaRational(expr.constant);
    for (const auto& [name, coeff] : expr.coeffs) row.coeffs[ensure_real_var(name)] += coeff;
    for (auto rit = row.coeffs.begin(); rit != row.coeffs.end();) {
        if (rit->second.is_zero()) rit = row.coeffs.erase(rit);
        else ++rit;
    }
    beta_[s] = row.constant;
    row_of_basic_[s] = static_cast<int>(rows_.size());
    if (row_index_enabled()) row_basic_.push_back(s);
    rows_.push_back(std::move(row));
    register_row_coeffs(row_of_basic_[s]);
    if (stats_) stats_->lra_max_rows = std::max<uint64_t>(
        stats_->lra_max_rows, static_cast<uint64_t>(rows_.size()));
    term_var_keys_[std::move(key)] = s;
    return s;
}

DeltaRational LraSolver::strict_value(const Rational& q, BoundKind kind, bool strict) {
    if (!strict) return DeltaRational(q);
    return DeltaRational(q, kind == BoundKind::Lower ? Rational(1) : Rational(-1));
}

int LraSolver::register_atom(const Atom& atom) {
    if (atom.rel == Relation::Ne)
        throw std::runtime_error("native QF_LRA expects disequality to be encoded as strict-bound disjunction");
    std::string key = atom_key(atom);
    auto it = atom_keys_.find(key);
    if (it != atom_keys_.end()) return it->second;

    int sat_var = new_var();
    if (static_cast<int>(atom_assignment_.size()) <= sat_var)
        atom_assignment_.resize(sat_var + 1, 0);
    if (stats_) ++stats_->lra_atoms;
    if (stats_ && atom.rel == Relation::Eq && atom.lhs_minus_rhs.coeffs.size() == 2) {
        auto itc = atom.lhs_minus_rhs.coeffs.begin();
        const Rational& a = itc++->second;
        const Rational& b = itc->second;
        if ((a == Rational(1) && b == Rational(-1)) ||
            (a == Rational(-1) && b == Rational(1)))
            ++stats_->lra_offset_equalities;
    }
    atoms_[sat_var] = atom;
    atom_keys_[std::move(key)] = sat_var;
    observed_vars_.push_back(sat_var);

    LinearExpr expr = atom.lhs_minus_rhs;
    int var = ensure_term_var(expr);
    ElementaryAtom ea;
    ea.var = var;

    switch (atom.rel) {
    case Relation::Le:
        ea.positive_kind = BoundKind::Upper;
        ea.positive_value = DeltaRational(Rational(0));
        break;
    case Relation::Lt:
        ea.positive_kind = BoundKind::Upper;
        ea.positive_value = DeltaRational(Rational(0), Rational(-1));
        break;
    case Relation::Ge:
        ea.positive_kind = BoundKind::Lower;
        ea.positive_value = DeltaRational(Rational(0));
        break;
    case Relation::Gt:
        ea.positive_kind = BoundKind::Lower;
        ea.positive_value = DeltaRational(Rational(0), Rational(1));
        break;
    case Relation::Eq:
        ea.equality = true;
        ea.positive_kind = BoundKind::Lower;
        ea.positive_value = DeltaRational(Rational(0));
        break;
    case Relation::Ne:
        break;
    }
    elementary_atoms_[sat_var] = ea;
    if (static_cast<int>(atoms_by_var_.size()) <= ea.var) atoms_by_var_.resize(ea.var + 1);
    if (static_cast<int>(lower_atoms_by_var_.size()) <= ea.var) lower_atoms_by_var_.resize(ea.var + 1);
    if (static_cast<int>(upper_atoms_by_var_.size()) <= ea.var) upper_atoms_by_var_.resize(ea.var + 1);
    atoms_by_var_[ea.var].push_back(sat_var);
    if (ea.positive_kind == BoundKind::Lower)
        lower_atoms_by_var_[ea.var].push_back(BoundAtomRef{sat_var, ea.positive_value});
    else
        upper_atoms_by_var_[ea.var].push_back(BoundAtomRef{sat_var, ea.positive_value});
    if (auto simple = make_simple_graph_atom(atom)) {
        simple_graph_atoms_[sat_var] = std::move(*simple);
        if (stats_) ++stats_->lra_simple_graph_atoms;
    } else if (stats_) {
        ++stats_->lra_simple_graph_skipped;
    }
    if (rdl_propagation_enabled()) {
        if (auto rdl = make_rdl_atom(atom)) {
            rdl_atoms_[sat_var] = std::move(*rdl);
            rdl_labels_[sat_var] = RdlLabel::Lambda;
            if (atom.rel != Relation::Eq) rdl_labels_[-sat_var] = RdlLabel::Lambda;
        }
    }
    return sat_var;
}

int LraSolver::graph_node_for_var(int var, bool negated) const {
    return 1 + 2 * var + (negated ? 1 : 0);
}

size_t LraSolver::graph_node_count() const {
    return 1 + 2 * static_cast<size_t>(next_lra_var_);
}

std::optional<LraSolver::SimpleGraphAtom> LraSolver::make_simple_graph_atom(const Atom& atom) {
    auto strict_bound = [](Rational bound, bool strict) {
        return DeltaRational(std::move(bound), strict ? Rational(-1) : Rational(0));
    };

    auto edges_for_le = [&](const LinearExpr& expr, bool strict)
        -> std::optional<std::vector<GraphEdgeTemplate>> {
        std::vector<std::pair<std::string, Rational>> coeffs;
        coeffs.reserve(expr.coeffs.size());
        for (const auto& [name, coeff] : expr.coeffs) {
            if (!coeff.is_zero()) coeffs.push_back({name, coeff});
        }
        Rational bound = -expr.constant;
        if (coeffs.empty()) return std::nullopt;

        if (coeffs.size() == 1) {
            const auto& [name, coeff] = coeffs[0];
            if (coeff.is_zero()) return std::nullopt;
            int var = ensure_real_var(name);
            if (coeff > Rational(0)) {
                DeltaRational w = strict_bound(bound / coeff, strict);
                return std::vector<GraphEdgeTemplate>{
                    {graph_node_for_var(var, true), graph_node_for_var(var, false), w * Rational(2)}};
            }
            DeltaRational w = strict_bound(bound / (-coeff), strict);
            return std::vector<GraphEdgeTemplate>{
                {graph_node_for_var(var, false), graph_node_for_var(var, true), w * Rational(2)}};
        }

        if (coeffs.size() != 2) return std::nullopt;
        const auto& [name_a, coeff_a] = coeffs[0];
        const auto& [name_b, coeff_b] = coeffs[1];
        Rational abs_a = coeff_a < Rational(0) ? -coeff_a : coeff_a;
        Rational abs_b = coeff_b < Rational(0) ? -coeff_b : coeff_b;
        if (abs_a.is_zero() || !(abs_a == abs_b)) return std::nullopt;

        bool a_neg = coeff_a < Rational(0);
        bool b_neg = coeff_b < Rational(0);
        int var_a = ensure_real_var(name_a);
        int var_b = ensure_real_var(name_b);
        DeltaRational w = strict_bound(bound / abs_a, strict);

        if (a_neg != b_neg) {
            int from = coeff_a < Rational(0) ? var_a : var_b;
            int to = coeff_a < Rational(0) ? var_b : var_a;
            return std::vector<GraphEdgeTemplate>{
                {graph_node_for_var(from, false), graph_node_for_var(to, false), w}};
        }

        // UTVPI constraints ±x ± y <= c reduce to two difference-logic
        // edges over signed variables; see the signed-variable graph
        // construction used by Lahiri/Musuvathi-style UTVPI solvers. The
        // complete mixed LRA check remains the Dutertre/de Moura simplex core.
        int node_a = graph_node_for_var(var_a, a_neg);
        int node_not_a = graph_node_for_var(var_a, !a_neg);
        int node_b = graph_node_for_var(var_b, b_neg);
        int node_not_b = graph_node_for_var(var_b, !b_neg);
        return std::vector<GraphEdgeTemplate>{{node_not_b, node_a, w},
                                              {node_not_a, node_b, w}};
    };

    auto scaled = [](LinearExpr e, const Rational& q) {
        e.scale(q);
        return e;
    };
    auto edges_for_relation = [&](Relation rel)
        -> std::optional<std::vector<GraphEdgeTemplate>> {
        switch (rel) {
        case Relation::Le: return edges_for_le(atom.lhs_minus_rhs, false);
        case Relation::Lt: return edges_for_le(atom.lhs_minus_rhs, true);
        case Relation::Ge: return edges_for_le(scaled(atom.lhs_minus_rhs, Rational(-1)), false);
        case Relation::Gt: return edges_for_le(scaled(atom.lhs_minus_rhs, Rational(-1)), true);
        case Relation::Eq: {
            auto le = edges_for_le(atom.lhs_minus_rhs, false);
            auto ge = edges_for_le(scaled(atom.lhs_minus_rhs, Rational(-1)), false);
            if (!le || !ge) return std::nullopt;
            le->insert(le->end(), ge->begin(), ge->end());
            return le;
        }
        case Relation::Ne:
            return std::nullopt;
        }
        return std::nullopt;
    };

    auto pos = edges_for_relation(atom.rel);
    if (!pos) return std::nullopt;
    SimpleGraphAtom out;
    out.positive_edges = std::move(*pos);
    if (atom.rel != Relation::Eq && atom.rel != Relation::Ne) {
        if (auto neg = edges_for_relation(negate_rel(atom.rel)))
            out.negative_edges = std::move(*neg);
    }
    return out;
}

std::optional<LraSolver::RdlAtom> LraSolver::make_rdl_atom(const Atom& atom) {
    auto strict_bound = [](Rational bound, bool strict) {
        return DeltaRational(std::move(bound), strict ? Rational(-1) : Rational(0));
    };

    auto edges_for_le = [&](const LinearExpr& expr, bool strict)
        -> std::optional<std::vector<GraphEdgeTemplate>> {
        std::vector<std::pair<std::string, Rational>> coeffs;
        coeffs.reserve(expr.coeffs.size());
        for (const auto& [name, coeff] : expr.coeffs)
            if (!coeff.is_zero()) coeffs.push_back({name, coeff});

        Rational bound = -expr.constant;
        if (coeffs.empty()) return std::nullopt;

        if (coeffs.size() == 1) {
            const auto& [name, coeff] = coeffs[0];
            if (coeff.is_zero()) return std::nullopt;
            int var = ensure_real_var(name);
            if (coeff > Rational(0)) {
                return std::vector<GraphEdgeTemplate>{
                    {rdl_zero_node(), rdl_node_for_var(var), strict_bound(bound / coeff, strict)}};
            }
            return std::vector<GraphEdgeTemplate>{
                {rdl_node_for_var(var), rdl_zero_node(), strict_bound(bound / (-coeff), strict)}};
        }

        if (coeffs.size() != 2) return std::nullopt;
        const auto& [name_a, coeff_a] = coeffs[0];
        const auto& [name_b, coeff_b] = coeffs[1];
        Rational abs_a = coeff_a < Rational(0) ? -coeff_a : coeff_a;
        Rational abs_b = coeff_b < Rational(0) ? -coeff_b : coeff_b;
        if (abs_a.is_zero() || !(abs_a == abs_b)) return std::nullopt;
        if (!((coeff_a > Rational(0) && coeff_b < Rational(0)) ||
              (coeff_a < Rational(0) && coeff_b > Rational(0))))
            return std::nullopt;

        int var_a = ensure_real_var(name_a);
        int var_b = ensure_real_var(name_b);
        int to = coeff_a > Rational(0) ? var_a : var_b;
        int from = coeff_a > Rational(0) ? var_b : var_a;
        return std::vector<GraphEdgeTemplate>{
            {rdl_node_for_var(from), rdl_node_for_var(to), strict_bound(bound / abs_a, strict)}};
    };

    auto scaled = [](LinearExpr e, const Rational& q) {
        e.scale(q);
        return e;
    };
    auto edges_for_relation = [&](Relation rel)
        -> std::optional<std::vector<GraphEdgeTemplate>> {
        switch (rel) {
        case Relation::Le: return edges_for_le(atom.lhs_minus_rhs, false);
        case Relation::Lt: return edges_for_le(atom.lhs_minus_rhs, true);
        case Relation::Ge: return edges_for_le(scaled(atom.lhs_minus_rhs, Rational(-1)), false);
        case Relation::Gt: return edges_for_le(scaled(atom.lhs_minus_rhs, Rational(-1)), true);
        case Relation::Eq: {
            auto le = edges_for_le(atom.lhs_minus_rhs, false);
            auto ge = edges_for_le(scaled(atom.lhs_minus_rhs, Rational(-1)), false);
            if (!le || !ge) return std::nullopt;
            le->insert(le->end(), ge->begin(), ge->end());
            return le;
        }
        case Relation::Ne:
            return std::nullopt;
        }
        return std::nullopt;
    };

    auto pos = edges_for_relation(atom.rel);
    if (!pos) return std::nullopt;
    RdlAtom out;
    out.positive_edges = std::move(*pos);
    if (atom.rel != Relation::Eq && atom.rel != Relation::Ne) {
        if (auto neg = edges_for_relation(negate_rel(atom.rel)))
            out.negative_edges = std::move(*neg);
    }
    return out;
}

bool LraSolver::apply_bound(int var, BoundKind kind, const DeltaRational& value, int source_lit) {
    Bound& b = kind == BoundKind::Lower ? lower_[var] : upper_[var];
    bool stronger = !b.active ||
                    (kind == BoundKind::Lower ? value > b.value : value < b.value);
    if (!stronger) return true;

    Bound opposite = kind == BoundKind::Lower ? upper_[var] : lower_[var];
    if (opposite.active) {
        bool conflict = kind == BoundKind::Lower ? value > opposite.value : opposite.value > value;
        if (conflict) {
            std::vector<int> clause{-source_lit, -opposite.source_lit};
            std::sort(clause.begin(), clause.end());
            clause.erase(std::unique(clause.begin(), clause.end()), clause.end());
            set_conflict(std::move(clause));
            return false;
        }
    }

    bound_trail_.push_back(BoundTrailEntry{var, kind, b});
    bound_level_counts_.back()++;
    b = Bound{true, value, source_lit};
    if (stats_) {
        if (kind == BoundKind::Lower) ++stats_->lra_lower_bound_applications;
        else ++stats_->lra_upper_bound_applications;
    }
    if (static_cast<int>(prop_var_dirty_.size()) <= var) prop_var_dirty_.resize(var + 1);
    if (!prop_var_dirty_[var]) {
        prop_var_dirty_[var] = true;
        prop_dirty_vars_.push_back(var);
    }

    if (!is_basic_[var]) {
        if (kind == BoundKind::Lower && beta_[var] < value) update(var, value);
        if (kind == BoundKind::Upper && beta_[var] > value) update(var, value);
    }
    return true;
}

void LraSolver::notify_assignment(int lit, bool) {
    int sat_var = std::abs(lit);
    if (static_cast<int>(atom_assignment_.size()) <= sat_var)
        atom_assignment_.resize(sat_var + 1, 0);
    int new_value = lit > 0 ? 1 : -1;
    if (atom_assignment_[sat_var] == new_value) return;
    atom_assignment_[sat_var] = new_value;
    trail_.push_back(lit);
    level_counts_.back()++;
    if (simple_graph_conflicts_enabled() && simple_graph_atoms_.contains(sat_var))
        add_active_simple_graph_edges(sat_var, lit);
    if (rdl_propagation_enabled() && rdl_atoms_.contains(sat_var))
        add_active_rdl_edges(sat_var, lit);

    auto it = elementary_atoms_.find(sat_var);
    if (it == elementary_atoms_.end()) return;
    if (stats_) ++stats_->lra_assignments;
    tableau_dirty_ = true;

    const ElementaryAtom& ea = it->second;
    bool positive = lit > 0;
    if (ea.equality) {
        if (!positive)
            throw std::runtime_error("negative LRA equality atom must be encoded as strict-bound disjunction");
        if (stats_) ++stats_->lra_fixed_equalities;
        bool ok = apply_bound(ea.var, BoundKind::Lower, DeltaRational(Rational(0)), lit);
        if (ok) apply_bound(ea.var, BoundKind::Upper, DeltaRational(Rational(0)), lit);
        return;
    }
    BoundKind kind = ea.positive_kind;
    DeltaRational value = ea.positive_value;
    if (!positive) {
        kind = kind == BoundKind::Lower ? BoundKind::Upper : BoundKind::Lower;
        value = kind == BoundKind::Lower
            ? DeltaRational(ea.positive_value.real, ea.positive_value.delta + Rational(1))
            : DeltaRational(ea.positive_value.real, ea.positive_value.delta - Rational(1));
    }
    apply_bound(ea.var, kind, value, lit);
}

void LraSolver::notify_new_decision_level() {
    level_counts_.push_back(0);
    bound_level_counts_.push_back(0);
    graph_edge_level_counts_.push_back(0);
    rdl_edge_level_counts_.push_back(0);
}

void LraSolver::notify_backtrack(size_t new_level) {
    while (level_counts_.size() > new_level + 1) {
        size_t n = level_counts_.back();
        level_counts_.pop_back();
        while (n-- > 0) {
            int lit = trail_.back();
            trail_.pop_back();
            int sat_var = std::abs(lit);
            if (static_cast<int>(atom_assignment_.size()) > sat_var)
                atom_assignment_[sat_var] = 0;
        }
    }
    while (graph_edge_level_counts_.size() > new_level + 1) {
        size_t n = graph_edge_level_counts_.back();
        graph_edge_level_counts_.pop_back();
        while (n-- > 0 && !active_simple_graph_edges_.empty())
            active_simple_graph_edges_.pop_back();
        active_simple_graph_dirty_ = true;
    }
    while (rdl_edge_level_counts_.size() > new_level + 1) {
        size_t n = rdl_edge_level_counts_.back();
        rdl_edge_level_counts_.pop_back();
        while (n-- > 0 && !active_rdl_edges_.empty())
            active_rdl_edges_.pop_back();
    }
    while (bound_level_counts_.size() > new_level + 1) {
        size_t n = bound_level_counts_.back();
        bound_level_counts_.pop_back();
        while (n-- > 0) {
            auto e = bound_trail_.back();
            bound_trail_.pop_back();
            (e.kind == BoundKind::Lower ? lower_[e.var] : upper_[e.var]) = e.previous;
        }
    }
    has_conflict_ = false;
    conflict_clause_.clear();
    conflict_idx_ = 0;
    tableau_dirty_ = true;
    prop_queue_.clear();
    prop_head_ = 0;
    prop_enqueued_.clear();
    mark_all_bound_vars_for_propagation();
    rebuild_rdl_sigma_from_active();
    reason_serving_lit_ = 0;
    reason_serving_idx_ = 0;
}

void LraSolver::update(int x, const DeltaRational& v) {
    DeltaRational delta = v - beta_[x];
    if (delta.is_zero()) return;
    beta_[x] = v;
    if (tableau_row_index_ && x >= 0 && static_cast<size_t>(x) < rows_by_var_.size()) {
        for (int r : rows_by_var_[x]) {
            if (r < 0 || static_cast<size_t>(r) >= rows_.size() ||
                static_cast<size_t>(r) >= row_basic_.size())
                continue;
            int b = row_basic_[r];
            if (b < 0) continue;
            auto it = rows_[r].coeffs.find(x);
            if (it != rows_[r].coeffs.end()) beta_[b] += delta * it->second;
        }
        return;
    }
    for (int b : basic_vars_) {
        int r = row_of_basic_[b];
        if (r < 0) continue;
        auto it = rows_[r].coeffs.find(x);
        if (it != rows_[r].coeffs.end()) beta_[b] += delta * it->second;
    }
}

bool LraSolver::pivot(int basic, int nonbasic) {
    int r = row_of_basic_[basic];
    if (r < 0) return false;
    auto ait = rows_[r].coeffs.find(nonbasic);
    if (ait == rows_[r].coeffs.end() || ait->second.is_zero()) return false;
    Rational a = ait->second;

    TableauRow solved;
    solved.constant = (DeltaRational(Rational(0)) - rows_[r].constant) / a;
    solved.coeffs[basic] = Rational(1) / a;
    for (const auto& [v, c] : rows_[r].coeffs) {
        if (v == nonbasic) continue;
        solved.coeffs[v] = -c / a;
    }

    std::vector<int> affected_rows;
    if (tableau_row_index_ && nonbasic >= 0 && static_cast<size_t>(nonbasic) < rows_by_var_.size()) {
        affected_rows = rows_by_var_[nonbasic];
        for (int rb : affected_rows) {
            if (rb == r || rb < 0 || static_cast<size_t>(rb) >= rows_.size() ||
                static_cast<size_t>(rb) >= row_basic_.size())
                continue;
            int b = row_basic_[rb];
            if (b < 0 || b == basic) continue;
            auto it = rows_[rb].coeffs.find(nonbasic);
            if (it == rows_[rb].coeffs.end() || it->second.is_zero()) continue;
            Rational factor = it->second;
            unregister_row_coeffs(rb);
            rows_[rb].coeffs.erase(it);
            rows_[rb].constant += solved.constant * factor;
            for (const auto& [v, c] : solved.coeffs) rows_[rb].coeffs[v] += c * factor;
            for (auto cit = rows_[rb].coeffs.begin(); cit != rows_[rb].coeffs.end();) {
                if (cit->second.is_zero()) cit = rows_[rb].coeffs.erase(cit);
                else ++cit;
            }
            register_row_coeffs(rb);
        }
    } else {
        for (int b : basic_vars_) {
            if (b == basic) continue;
            int rb = row_of_basic_[b];
            auto it = rows_[rb].coeffs.find(nonbasic);
            if (it == rows_[rb].coeffs.end() || it->second.is_zero()) continue;
            Rational factor = it->second;
            unregister_row_coeffs(rb);
            rows_[rb].coeffs.erase(it);
            rows_[rb].constant += solved.constant * factor;
            for (const auto& [v, c] : solved.coeffs) rows_[rb].coeffs[v] += c * factor;
            for (auto cit = rows_[rb].coeffs.begin(); cit != rows_[rb].coeffs.end();) {
                if (cit->second.is_zero()) cit = rows_[rb].coeffs.erase(cit);
                else ++cit;
            }
            register_row_coeffs(rb);
        }
    }

    unregister_row_coeffs(r);
    rows_[r] = std::move(solved);
    register_row_coeffs(r);
    if (row_index_enabled()) row_basic_[r] = nonbasic;
    row_of_basic_[nonbasic] = r;
    row_of_basic_[basic] = -1;
    is_basic_[basic] = false;
    is_basic_[nonbasic] = true;
    auto replace = [](std::vector<int>& xs, int old_v, int new_v) {
        auto it = std::find(xs.begin(), xs.end(), old_v);
        if (it != xs.end()) *it = new_v;
        std::sort(xs.begin(), xs.end());
    };
    replace(basic_vars_, basic, nonbasic);
    replace(nonbasic_vars_, nonbasic, basic);
    if (stats_) ++stats_->lra_pivots;
    return true;
}

bool LraSolver::pivot_and_update(int basic, int nonbasic, const DeltaRational& value) {
    // Dutertre/de Moura Figure 3.1 PivotAndUpdate.
    if (!pivot(basic, nonbasic)) return false;
    int r = row_of_basic_[nonbasic];
    auto it = rows_[r].coeffs.find(basic);
    if (it == rows_[r].coeffs.end() || it->second.is_zero()) return false;

    // Pivoting rewrites the tableau algebraically, so the current beta values
    // still satisfy every row. Only the old basic, now nonbasic, needs to move.
    DeltaRational rest = rows_[r].constant;
    for (const auto& [x, a] : rows_[r].coeffs) {
        if (x == basic) continue;
        rest += beta_[x] * a;
    }
    update(basic, (value - rest) / it->second);
    return true;
}

size_t LraSolver::column_length(int var) const {
    if (var < 0) return 0;
    if (row_index_enabled() && static_cast<size_t>(var) < rows_by_var_.size())
        return rows_by_var_[var].size();
    size_t n = 0;
    for (int b : basic_vars_) {
        int r = row_of_basic_[b];
        if (r >= 0 && static_cast<size_t>(r) < rows_.size() && rows_[r].coeffs.contains(var))
            ++n;
    }
    return n;
}

int LraSolver::choose_entering_var(int bad, bool below, bool bland_mode, DeltaRational& target) {
    int entering = -1;
    size_t best_column = std::numeric_limits<size_t>::max();
    const auto& row = rows_[row_of_basic_[bad]];

    auto repair_target = [&](int x, const Rational& a) {
        DeltaRational repair = beta_[x] + ((below ? lower_[bad].value : upper_[bad].value) - beta_[bad]) / a;
        if (below) {
            if (a > Rational(0))
                return upper_[x].active && upper_[x].value < repair ? upper_[x].value : repair;
            return lower_[x].active && lower_[x].value > repair ? lower_[x].value : repair;
        }
        if (a < Rational(0))
            return upper_[x].active && upper_[x].value < repair ? upper_[x].value : repair;
        return lower_[x].active && lower_[x].value > repair ? lower_[x].value : repair;
    };

    for (const auto& [x, a] : row.coeffs) {
        bool ok = below
            ? ((a > Rational(0) && (!upper_[x].active || beta_[x] < upper_[x].value)) ||
               (a < Rational(0) && (!lower_[x].active || beta_[x] > lower_[x].value)))
            : ((a < Rational(0) && (!upper_[x].active || beta_[x] < upper_[x].value)) ||
               (a > Rational(0) && (!lower_[x].active || beta_[x] > lower_[x].value)));
        if (!ok) continue;
        if (stats_) ++stats_->lra_pivot_candidates;

        if (bland_mode || pivot_heuristic_ == PivotHeuristic::MinVar) {
            if (entering < 0 || x < entering) {
                entering = x;
                target = repair_target(x, a);
            }
            continue;
        }

        // King/Barrett/Dutertre's SOI paper notes that many SMT solvers use
        // local pivot heuristics such as choosing a short entering column, with
        // Bland-style fallback for termination. This option keeps the
        // Dutertre/de Moura simplex core and only changes that local choice.
        size_t len = column_length(x);
        if (entering < 0 || len < best_column || (len == best_column && x < entering)) {
            entering = x;
            best_column = len;
            target = repair_target(x, a);
        }
    }

    if (entering >= 0 && stats_) {
        if (bland_mode && pivot_heuristic_ != PivotHeuristic::MinVar)
            ++stats_->lra_pivot_bland_fallbacks;
        else if (pivot_heuristic_ == PivotHeuristic::MinColumn)
            ++stats_->lra_pivot_min_column_choices;
    }
    return entering;
}

std::vector<int> LraSolver::explain_lower_conflict(int basic) const {
    // Section 3.2.2, Figure 3.2 line 8 explanation.
    std::vector<int> clause;
    if (lower_[basic].active) clause.push_back(-lower_[basic].source_lit);
    const auto& row = rows_[row_of_basic_[basic]];
    for (const auto& [x, a] : row.coeffs) {
        if (a > Rational(0) && upper_[x].active) clause.push_back(-upper_[x].source_lit);
        if (a < Rational(0) && lower_[x].active) clause.push_back(-lower_[x].source_lit);
    }
    std::sort(clause.begin(), clause.end());
    clause.erase(std::unique(clause.begin(), clause.end()), clause.end());
    return clause;
}

std::vector<int> LraSolver::explain_upper_conflict(int basic) const {
    // Section 3.2.2, Figure 3.2 line 13 explanation.
    std::vector<int> clause;
    if (upper_[basic].active) clause.push_back(-upper_[basic].source_lit);
    const auto& row = rows_[row_of_basic_[basic]];
    for (const auto& [x, a] : row.coeffs) {
        if (a > Rational(0) && lower_[x].active) clause.push_back(-lower_[x].source_lit);
        if (a < Rational(0) && upper_[x].active) clause.push_back(-upper_[x].source_lit);
    }
    std::sort(clause.begin(), clause.end());
    clause.erase(std::unique(clause.begin(), clause.end()), clause.end());
    return clause;
}

bool LraSolver::check() {
    detect_simple_graph_conflict();
    if (has_conflict_) return false;
    // Dutertre/de Moura Figure 3.2 Check. The default path keeps the
    // Bland-style smallest-variable rule; option-backed experiments may use
    // local heuristics from the SMT simplex literature with Bland fallback.
    if (stats_) ++stats_->lra_check_calls;
    size_t pivots_this_check = 0;
    while (true) {
        int bad = -1;
        bool below = false;
        for (int b : basic_vars_) {
            if (lower_[b].active && beta_[b] < lower_[b].value) {
                if (bad < 0 || b < bad) { bad = b; below = true; }
            }
            if (upper_[b].active && beta_[b] > upper_[b].value) {
                if (bad < 0 || b < bad) { bad = b; below = false; }
            }
        }
        if (bad < 0) {
            if (stats_) stats_->lra_check_max_pivots =
                std::max<uint64_t>(stats_->lra_check_max_pivots, pivots_this_check);
            return true;
        }

        DeltaRational target;
        bool bland_mode = pivot_bland_after_ > 0 && pivots_this_check >= pivot_bland_after_;
        int entering = choose_entering_var(bad, below, bland_mode, target);
        if (entering < 0) {
            set_conflict(below ? explain_lower_conflict(bad) : explain_upper_conflict(bad));
            if (stats_) stats_->lra_check_max_pivots =
                std::max<uint64_t>(stats_->lra_check_max_pivots, pivots_this_check);
            return false;
        }
        if (!pivot_and_update(bad, entering, target)) {
            set_conflict({-trail_.back()});
            if (stats_) stats_->lra_check_max_pivots =
                std::max<uint64_t>(stats_->lra_check_max_pivots, pivots_this_check);
            return false;
        }
        ++pivots_this_check;
    }
}

void LraSolver::set_conflict(std::vector<int> clause) {
    if (clause.empty()) clause.push_back(1);
    conflict_clause_ = std::move(clause);
    last_conflict_size_ = conflict_clause_.size();
    if (stats_) {
        ++stats_->lra_conflicts;
        stats_->lra_conflict_lits_total += last_conflict_size_;
    }
    conflict_idx_ = 0;
    has_conflict_ = true;
}

Rational LraSolver::choose_delta() const {
    std::optional<Rational> upper;
    for (size_t i = 0; i < beta_.size(); ++i) {
        auto constrain = [&](const Bound& b, bool is_lower) {
            if (!b.active) return;
            DeltaRational diff = is_lower ? beta_[i] - b.value : b.value - beta_[i];
            if (diff.real < Rational(0)) return;
            if (diff.delta < Rational(0)) {
                Rational lim = diff.real / (-diff.delta);
                if (lim > Rational(0) && (!upper || lim < *upper)) upper = lim;
            }
        };
        constrain(lower_[i], true);
        constrain(upper_[i], false);
    }
    if (!upper) return Rational(1);
    return *upper / Rational(2);
}

void LraSolver::rebuild_model() {
    last_model_.clear();
    Rational d = choose_delta();
    for (const auto& [name, v] : real_to_var_)
        last_model_[name] = beta_[v].real + beta_[v].delta * d;
}

void LraSolver::mark_all_bound_vars_for_propagation() {
    for (size_t var = 0; var < atoms_by_var_.size(); ++var) {
        if (atoms_by_var_[var].empty()) continue;
        if ((var < lower_.size() && lower_[var].active) ||
            (var < upper_.size() && upper_[var].active)) {
            if (prop_var_dirty_.size() <= var) prop_var_dirty_.resize(var + 1);
            if (!prop_var_dirty_[var]) {
                prop_var_dirty_[var] = true;
                prop_dirty_vars_.push_back(static_cast<int>(var));
            }
        }
    }
}

int LraSolver::current_lit_value(int lit) const {
    int sat_var = std::abs(lit);
    if (static_cast<int>(atom_assignment_.size()) <= sat_var) return 0;
    int value = atom_assignment_[sat_var];
    if (value == 0) return 0;
    return lit > 0 ? value : -value;
}

bool LraSolver::enqueue_propagation(int lit, std::vector<int> reason, bool row_bound) {
    if (has_conflict_) return false;
    if (stats_) {
        ++stats_->lra_prop_enqueue_attempts;
        if (row_bound) ++stats_->lra_row_prop_enqueue_attempts;
    }
    if (std::find(reason.begin(), reason.end(), -lit) != reason.end()) {
        if (stats_) {
            ++stats_->lra_prop_duplicates;
            if (row_bound) ++stats_->lra_row_prop_duplicates;
        }
        return false;
    }
    std::sort(reason.begin(), reason.end());
    reason.erase(std::unique(reason.begin(), reason.end()), reason.end());
    reason.erase(std::remove(reason.begin(), reason.end(), lit), reason.end());
    reason.insert(reason.begin(), lit);

    int assigned = current_lit_value(lit);
    if (assigned > 0) {
        if (stats_) {
            ++stats_->lra_prop_duplicates;
            if (row_bound) ++stats_->lra_row_prop_duplicates;
        }
        return false;
    }
    if (assigned < 0) {
        if (stats_) ++stats_->lra_prop_conflicts;
        set_conflict(reason);
        return false;
    }

    if (prop_enqueued_.insert(lit).second) {
        prop_queue_.push_back(lit);
        reason_clauses_[lit] = std::move(reason);
        if (row_bound) {
            ++row_bound_window_enqueues_;
            if (stats_) ++stats_->lra_row_bound_propagations;
        }
        return true;
    }
    if (stats_) {
        ++stats_->lra_prop_duplicates;
        if (row_bound) ++stats_->lra_row_prop_duplicates;
    }
    return false;
}

bool LraSolver::enqueue_graph_propagation(int lit, std::vector<int> reason) {
    bool had_conflict = has_conflict_;
    bool enqueued = enqueue_propagation(lit, std::move(reason), false);
    if (enqueued && stats_) ++stats_->lra_simple_graph_propagations;
    if (!had_conflict && has_conflict_ && stats_) ++stats_->lra_simple_graph_conflicts;
    return enqueued;
}

bool LraSolver::enqueue_rdl_propagation(int lit, std::vector<int> reason) {
    bool had_conflict = has_conflict_;
    bool enqueued = enqueue_propagation(lit, std::move(reason), false);
    if (enqueued) {
        rdl_labels_[lit] = RdlLabel::Delta;
        if (stats_) ++stats_->lra_rdl_prop_enqueues;
    } else if (!had_conflict && has_conflict_) {
        if (stats_) ++stats_->lra_rdl_prop_conflicts;
    } else if (stats_) {
        ++stats_->lra_rdl_prop_duplicates;
    }
    return enqueued;
}

std::vector<LraSolver::ActiveGraphEdge> LraSolver::active_simple_graph_edges(
    const std::vector<int>* model) const {
    std::unordered_set<int> model_lits;
    if (model) model_lits.insert(model->begin(), model->end());

    std::vector<ActiveGraphEdge> edges;
    for (const auto& [sat_var, atom] : simple_graph_atoms_) {
        if (sat_var < 0 || static_cast<size_t>(sat_var) >= atom_assignment_.size()) continue;
        int value = atom_assignment_[sat_var];
        if (value == 0 && !model_lits.empty()) {
            if (model_lits.contains(sat_var)) value = 1;
            else if (model_lits.contains(-sat_var)) value = -1;
        }
        if (value == 0) continue;
        int lit = value > 0 ? sat_var : -sat_var;
        const auto& templates = value > 0 ? atom.positive_edges : atom.negative_edges;
        for (const auto& edge : templates)
            edges.push_back(ActiveGraphEdge{edge.from, edge.to, edge.weight, lit});
    }
    return edges;
}

void LraSolver::add_active_simple_graph_edges(int sat_var, int lit) {
    auto it = simple_graph_atoms_.find(sat_var);
    if (it == simple_graph_atoms_.end()) return;
    const auto& templates = lit > 0 ? it->second.positive_edges : it->second.negative_edges;
    for (const auto& edge : templates)
        active_simple_graph_edges_.push_back(ActiveGraphEdge{edge.from, edge.to, edge.weight, lit});
    graph_edge_level_counts_.back() += templates.size();
    active_simple_graph_dirty_ = true;
    if (stats_) stats_->lra_simple_graph_active_edges = active_simple_graph_edges_.size();
}

std::vector<LraSolver::ActiveGraphEdge> LraSolver::active_rdl_edges(
    const std::vector<int>* model) const {
    std::unordered_set<int> model_lits;
    if (model) model_lits.insert(model->begin(), model->end());

    std::vector<ActiveGraphEdge> edges;
    for (const auto& [sat_var, atom] : rdl_atoms_) {
        if (sat_var < 0 || static_cast<size_t>(sat_var) >= atom_assignment_.size()) continue;
        int value = atom_assignment_[sat_var];
        if (value == 0 && !model_lits.empty()) {
            if (model_lits.contains(sat_var)) value = 1;
            else if (model_lits.contains(-sat_var)) value = -1;
        }
        if (value == 0) continue;
        int lit = value > 0 ? sat_var : -sat_var;
        const auto& templates = value > 0 ? atom.positive_edges : atom.negative_edges;
        for (const auto& edge : templates)
            edges.push_back(ActiveGraphEdge{edge.from, edge.to, edge.weight, lit});
    }
    return edges;
}

void LraSolver::add_active_rdl_edges(int sat_var, int lit) {
    auto it = rdl_atoms_.find(sat_var);
    if (it == rdl_atoms_.end()) return;
    const auto& templates = lit > 0 ? it->second.positive_edges : it->second.negative_edges;
    // Cotton/Maler labels: Lambda=unassigned, Sigma=assigned/unpropagated,
    // Pi=assigned/propagated, Delta=implied before SAT assigns it.
    rdl_labels_[lit] = RdlLabel::Sigma;
    for (const auto& edge : templates) {
        active_rdl_edges_.push_back(ActiveGraphEdge{edge.from, edge.to, edge.weight, lit});
        rdl_sigma_edge_indices_.push_back(active_rdl_edges_.size() - 1);
    }
    rdl_edge_level_counts_.back() += templates.size();
    if (stats_) {
        stats_->lra_rdl_prop_edges_active = active_rdl_edges_.size();
        stats_->lra_rdl_prop_sigma = rdl_sigma_edge_indices_.size();
    }
}

void LraSolver::rebuild_rdl_sigma_from_active() {
    rdl_sigma_edge_indices_.clear();
    for (auto& [_, label] : rdl_labels_) label = RdlLabel::Lambda;
    for (size_t edge_idx = 0; edge_idx < active_rdl_edges_.size(); ++edge_idx) {
        int lit = active_rdl_edges_[edge_idx].source_lit;
        rdl_labels_[lit] = RdlLabel::Sigma;
        rdl_sigma_edge_indices_.push_back(edge_idx);
    }
    if (stats_) {
        stats_->lra_rdl_prop_edges_active = active_rdl_edges_.size();
        stats_->lra_rdl_prop_sigma = rdl_sigma_edge_indices_.size();
    }
}

std::optional<LraSolver::ShortestPaths> LraSolver::shortest_paths_from(
    int source, const std::vector<ActiveGraphEdge>& edges, size_t node_count,
    bool count_rdl_stats) const {
    if (source < 0 || static_cast<size_t>(source) >= node_count) return std::nullopt;
    ShortestPaths out;
    out.dist.resize(node_count);
    out.pred_edge.assign(node_count, -1);
    out.dist[source] = DeltaRational(Rational(0));

    for (size_t iter = 1; iter < node_count; ++iter) {
        bool changed = false;
        for (size_t edge_idx = 0; edge_idx < edges.size(); ++edge_idx) {
            if (count_rdl_stats && stats_) ++stats_->lra_rdl_prop_sssp_relaxations;
            const auto& edge = edges[edge_idx];
            if (edge.from < 0 || edge.to < 0 ||
                static_cast<size_t>(edge.from) >= node_count ||
                static_cast<size_t>(edge.to) >= node_count ||
                !out.dist[edge.from])
                continue;
            DeltaRational candidate = *out.dist[edge.from] + edge.weight;
            if (!out.dist[edge.to] || candidate < *out.dist[edge.to]) {
                out.dist[edge.to] = candidate;
                out.pred_edge[edge.to] = static_cast<int>(edge_idx);
                changed = true;
            }
        }
        if (!changed) break;
    }
    return out;
}

std::optional<LraSolver::ShortestPaths> LraSolver::shortest_paths_from_excluding(
    int source, const std::vector<ActiveGraphEdge>& edges, size_t node_count,
    size_t skip_edge, bool count_rdl_stats) const {
    if (source < 0 || static_cast<size_t>(source) >= node_count) return std::nullopt;
    ShortestPaths out;
    out.dist.resize(node_count);
    out.pred_edge.assign(node_count, -1);
    out.dist[source] = DeltaRational(Rational(0));

    for (size_t iter = 1; iter < node_count; ++iter) {
        bool changed = false;
        for (size_t edge_idx = 0; edge_idx < edges.size(); ++edge_idx) {
            if (edge_idx == skip_edge) continue;
            if (count_rdl_stats && stats_) ++stats_->lra_rdl_prop_sssp_relaxations;
            const auto& edge = edges[edge_idx];
            if (edge.from < 0 || edge.to < 0 ||
                static_cast<size_t>(edge.from) >= node_count ||
                static_cast<size_t>(edge.to) >= node_count ||
                !out.dist[edge.from])
                continue;
            DeltaRational candidate = *out.dist[edge.from] + edge.weight;
            if (!out.dist[edge.to] || candidate < *out.dist[edge.to]) {
                out.dist[edge.to] = candidate;
                out.pred_edge[edge.to] = static_cast<int>(edge_idx);
                changed = true;
            }
        }
        if (!changed) break;
    }
    return out;
}

std::optional<LraSolver::ShortestPaths> LraSolver::shortest_paths_from_disabled(
    int source, const std::vector<ActiveGraphEdge>& edges, size_t node_count,
    const std::vector<char>& disabled_edges, bool count_rdl_stats) const {
    if (source < 0 || static_cast<size_t>(source) >= node_count) return std::nullopt;
    ShortestPaths out;
    out.dist.resize(node_count);
    out.pred_edge.assign(node_count, -1);
    out.dist[source] = DeltaRational(Rational(0));

    for (size_t iter = 1; iter < node_count; ++iter) {
        bool changed = false;
        for (size_t edge_idx = 0; edge_idx < edges.size(); ++edge_idx) {
            if (edge_idx < disabled_edges.size() && disabled_edges[edge_idx]) continue;
            if (count_rdl_stats && stats_) ++stats_->lra_rdl_prop_sssp_relaxations;
            const auto& edge = edges[edge_idx];
            if (edge.from < 0 || edge.to < 0 ||
                static_cast<size_t>(edge.from) >= node_count ||
                static_cast<size_t>(edge.to) >= node_count ||
                !out.dist[edge.from])
                continue;
            DeltaRational candidate = *out.dist[edge.from] + edge.weight;
            if (!out.dist[edge.to] || candidate < *out.dist[edge.to]) {
                out.dist[edge.to] = candidate;
                out.pred_edge[edge.to] = static_cast<int>(edge_idx);
                changed = true;
            }
        }
        if (!changed) break;
    }
    return out;
}

std::optional<LraSolver::ShortestPaths> LraSolver::shortest_paths_to(
    int target, const std::vector<ActiveGraphEdge>& edges, size_t node_count,
    bool count_rdl_stats) const {
    if (target < 0 || static_cast<size_t>(target) >= node_count) return std::nullopt;
    std::vector<ActiveGraphEdge> reversed;
    reversed.reserve(edges.size());
    for (const auto& edge : edges)
        reversed.push_back(ActiveGraphEdge{edge.to, edge.from, edge.weight, edge.source_lit});
    return shortest_paths_from(target, reversed, node_count, count_rdl_stats);
}

std::optional<LraSolver::ShortestPaths> LraSolver::shortest_paths_to_excluding(
    int target, const std::vector<ActiveGraphEdge>& edges, size_t node_count,
    size_t skip_edge, bool count_rdl_stats) const {
    if (target < 0 || static_cast<size_t>(target) >= node_count) return std::nullopt;
    std::vector<ActiveGraphEdge> reversed;
    reversed.reserve(edges.size());
    for (const auto& edge : edges)
        reversed.push_back(ActiveGraphEdge{edge.to, edge.from, edge.weight, edge.source_lit});
    return shortest_paths_from_excluding(target, reversed, node_count, skip_edge, count_rdl_stats);
}

std::optional<LraSolver::ShortestPaths> LraSolver::shortest_paths_to_disabled(
    int target, const std::vector<ActiveGraphEdge>& edges, size_t node_count,
    const std::vector<char>& disabled_edges, bool count_rdl_stats) const {
    if (target < 0 || static_cast<size_t>(target) >= node_count) return std::nullopt;
    std::vector<ActiveGraphEdge> reversed;
    reversed.reserve(edges.size());
    for (const auto& edge : edges)
        reversed.push_back(ActiveGraphEdge{edge.to, edge.from, edge.weight, edge.source_lit});
    return shortest_paths_from_disabled(target, reversed, node_count, disabled_edges, count_rdl_stats);
}

std::vector<int> LraSolver::graph_path_reason(
    int source, int target, const ShortestPaths& paths,
    const std::vector<ActiveGraphEdge>& edges) const {
    std::vector<int> reason;
    std::vector<char> seen_node(paths.pred_edge.size(), 0);
    int cur = target;
    while (cur != source) {
        if (cur < 0 || static_cast<size_t>(cur) >= paths.pred_edge.size()) break;
        if (seen_node[cur]) break;
        seen_node[cur] = 1;
        int edge_idx = paths.pred_edge[cur];
        if (edge_idx < 0 || static_cast<size_t>(edge_idx) >= edges.size()) break;
        const auto& edge = edges[edge_idx];
        reason.push_back(-edge.source_lit);
        cur = edge.from;
    }
    std::sort(reason.begin(), reason.end());
    reason.erase(std::unique(reason.begin(), reason.end()), reason.end());
    return reason;
}

std::vector<int> LraSolver::graph_negative_cycle_reason(
    const std::vector<ActiveGraphEdge>& edges, size_t node_count) const {
    std::vector<DeltaRational> dist(node_count, DeltaRational(Rational(0)));
    std::vector<int> pred_edge(node_count, -1);
    int changed_node = -1;

    for (size_t iter = 0; iter < node_count; ++iter) {
        changed_node = -1;
        for (size_t edge_idx = 0; edge_idx < edges.size(); ++edge_idx) {
            const auto& edge = edges[edge_idx];
            if (edge.from < 0 || edge.to < 0 ||
                static_cast<size_t>(edge.from) >= node_count ||
                static_cast<size_t>(edge.to) >= node_count)
                continue;
            DeltaRational candidate = dist[edge.from] + edge.weight;
            if (candidate < dist[edge.to]) {
                dist[edge.to] = candidate;
                pred_edge[edge.to] = static_cast<int>(edge_idx);
                changed_node = edge.to;
            }
        }
        if (changed_node < 0) return {};
    }

    int cycle_node = changed_node;
    for (size_t i = 0; i < node_count && cycle_node >= 0; ++i) {
        int edge_idx = pred_edge[cycle_node];
        if (edge_idx < 0 || static_cast<size_t>(edge_idx) >= edges.size()) break;
        cycle_node = edges[edge_idx].from;
    }

    std::vector<int> reason;
    std::vector<char> seen(node_count, 0);
    int cur = cycle_node;
    while (cur >= 0 && static_cast<size_t>(cur) < node_count && !seen[cur]) {
        seen[cur] = 1;
        int edge_idx = pred_edge[cur];
        if (edge_idx < 0 || static_cast<size_t>(edge_idx) >= edges.size()) break;
        const auto& edge = edges[edge_idx];
        reason.push_back(-edge.source_lit);
        cur = edge.from;
    }
    std::sort(reason.begin(), reason.end());
    reason.erase(std::unique(reason.begin(), reason.end()), reason.end());
    return reason;
}

void LraSolver::detect_simple_graph_conflict(const std::vector<int>* model) {
    if (!simple_graph_conflicts_enabled() || has_conflict_ || simple_graph_atoms_.empty()) return;
    std::vector<ActiveGraphEdge> model_edges;
    const std::vector<ActiveGraphEdge>* edges = &active_simple_graph_edges_;
    if (model) {
        model_edges = active_simple_graph_edges(model);
        edges = &model_edges;
    } else if (!active_simple_graph_dirty_) {
        if (stats_) ++stats_->lra_simple_graph_clean_skips;
        return;
    } else if (stats_) {
        ++stats_->lra_simple_graph_rebuilds_avoided;
    }
    if (stats_) {
        stats_->lra_simple_graph_edges = edges->size();
        stats_->lra_simple_graph_active_edges = active_simple_graph_edges_.size();
    }
    if (edges->empty()) {
        active_simple_graph_dirty_ = false;
        return;
    }
    if (stats_) ++stats_->lra_simple_graph_conflict_checks;
    std::vector<int> cycle_reason = graph_negative_cycle_reason(*edges, graph_node_count());
    active_simple_graph_dirty_ = false;
    if (!cycle_reason.empty()) {
        if (stats_) ++stats_->lra_simple_graph_conflicts;
        set_conflict(std::move(cycle_reason));
    }
}

void LraSolver::discover_simple_graph_propagations(const std::vector<int>* model) {
    if (!simple_graph_propagation_ || !propagation_enabled_ || simple_graph_atoms_.empty()) return;

    std::vector<ActiveGraphEdge> model_edges;
    const std::vector<ActiveGraphEdge>* edges = &active_simple_graph_edges_;
    if (model) model_edges = active_simple_graph_edges(model), edges = &model_edges;
    else if (stats_) ++stats_->lra_simple_graph_rebuilds_avoided;
    if (stats_) {
        stats_->lra_simple_graph_edges = edges->size();
        stats_->lra_simple_graph_active_edges = active_simple_graph_edges_.size();
    }
    if (edges->empty()) return;

    size_t node_count = graph_node_count();
    if (stats_) ++stats_->lra_simple_graph_conflict_checks;
    std::vector<int> cycle_reason = graph_negative_cycle_reason(*edges, node_count);
    if (!cycle_reason.empty()) {
        if (stats_) ++stats_->lra_simple_graph_conflicts;
        set_conflict(std::move(cycle_reason));
        return;
    }

    std::unordered_map<int, ShortestPaths> path_cache;
    size_t candidates = 0;
    bool budget_cutoff = false;

    auto implied = [&](const std::vector<GraphEdgeTemplate>& templates,
                       std::vector<int>& reason) {
        reason.clear();
        if (templates.empty()) return false;
        for (const auto& tmpl : templates) {
            auto pit = path_cache.find(tmpl.from);
            if (pit == path_cache.end()) {
                auto paths = shortest_paths_from(tmpl.from, *edges, node_count);
                if (!paths) return false;
                pit = path_cache.emplace(tmpl.from, std::move(*paths)).first;
            }
            const ShortestPaths& paths = pit->second;
            if (tmpl.to < 0 || static_cast<size_t>(tmpl.to) >= paths.dist.size() ||
                !paths.dist[tmpl.to] || *paths.dist[tmpl.to] > tmpl.weight)
                return false;
            std::vector<int> path_reason = graph_path_reason(tmpl.from, tmpl.to, paths, *edges);
            reason.insert(reason.end(), path_reason.begin(), path_reason.end());
        }
        std::sort(reason.begin(), reason.end());
        reason.erase(std::unique(reason.begin(), reason.end()), reason.end());
        return true;
    };

    auto inspect = [&](int lit, const std::vector<GraphEdgeTemplate>& templates) {
        if (has_conflict_ || templates.empty()) return;
        if (simple_graph_budget_ > 0 && candidates >= simple_graph_budget_) {
            budget_cutoff = true;
            return;
        }
        ++candidates;
        if (stats_) ++stats_->lra_simple_graph_candidates;
        if (current_lit_value(lit) > 0) return;
        std::vector<int> reason;
        if (implied(templates, reason)) enqueue_graph_propagation(lit, std::move(reason));
    };

    for (const auto& [sat_var, atom] : simple_graph_atoms_) {
        if (has_conflict_) break;
        inspect(sat_var, atom.positive_edges);
        inspect(-sat_var, atom.negative_edges);
    }
    if (budget_cutoff && stats_) ++stats_->lra_simple_graph_budget_cutoffs;
}

void LraSolver::discover_rdl_propagations(const std::vector<int>* model) {
    if (!rdl_propagation_enabled() || !propagation_enabled_ || rdl_atoms_.empty() || has_conflict_)
        return;

    std::vector<ActiveGraphEdge> model_edges;
    const std::vector<ActiveGraphEdge>* edges = &active_rdl_edges_;
    std::vector<size_t> model_sigma;
    const std::vector<size_t>* sigma = &rdl_sigma_edge_indices_;
    if (model) {
        model_edges = active_rdl_edges(model);
        edges = &model_edges;
        model_sigma.reserve(model_edges.size());
        for (size_t i = 0; i < model_edges.size(); ++i) model_sigma.push_back(i);
        sigma = &model_sigma;
    }

    if (stats_) {
        stats_->lra_rdl_prop_edges_active = edges->size();
        stats_->lra_rdl_prop_sigma = sigma->size();
    }
    if (edges->empty() || sigma->empty()) return;

    size_t node_count = rdl_node_count();
    std::unordered_map<int, ShortestPaths> path_cache;
    std::vector<char> disabled_future(edges->size(), 0);
    for (size_t edge_idx : *sigma) {
        if (edge_idx < disabled_future.size()) disabled_future[edge_idx] = 1;
    }
    auto implied = [&](const std::vector<GraphEdgeTemplate>& templates,
                       const std::vector<char>& disabled_edges,
                       std::vector<int>& reason) {
        reason.clear();
        if (templates.empty()) return false;
        for (const auto& tmpl : templates) {
            auto pit = path_cache.find(tmpl.from);
            if (pit == path_cache.end()) {
                auto paths = shortest_paths_from_disabled(
                    tmpl.from, *edges, node_count, disabled_edges, true);
                if (!paths) return false;
                pit = path_cache.emplace(tmpl.from, std::move(*paths)).first;
            }
            const ShortestPaths& paths = pit->second;
            if (tmpl.to < 0 || static_cast<size_t>(tmpl.to) >= paths.dist.size() ||
                !paths.dist[tmpl.to] || *paths.dist[tmpl.to] > tmpl.weight)
                return false;
            std::vector<int> path_reason = graph_path_reason(tmpl.from, tmpl.to, paths, *edges);
            reason.insert(reason.end(), path_reason.begin(), path_reason.end());
        }
        std::sort(reason.begin(), reason.end());
        reason.erase(std::unique(reason.begin(), reason.end()), reason.end());
        return true;
    };

    size_t candidates = 0;
    bool budget_cutoff = false;
    auto inspect = [&](int lit, const std::vector<GraphEdgeTemplate>& templates,
                       const ShortestPaths& reaches_new_from,
                       const ShortestPaths& from_new_to,
                       const std::vector<char>& disabled_edges) {
        if (has_conflict_ || templates.empty()) return;
        if (rdl_propagation_budget_ > 0 && candidates >= rdl_propagation_budget_) {
            budget_cutoff = true;
            return;
        }
        ++candidates;
        if (stats_) ++stats_->lra_rdl_prop_candidates;
        if (current_lit_value(lit) > 0) {
            if (stats_) ++stats_->lra_rdl_prop_duplicates;
            return;
        }

        bool relevant = false;
        for (const auto& tmpl : templates) {
            if (tmpl.from < 0 || tmpl.to < 0 ||
                static_cast<size_t>(tmpl.from) >= reaches_new_from.dist.size() ||
                static_cast<size_t>(tmpl.to) >= from_new_to.dist.size())
                continue;
            if (reaches_new_from.dist[tmpl.from] && from_new_to.dist[tmpl.to]) {
                relevant = true;
                break;
            }
        }
        if (!relevant) return;
        if (stats_) ++stats_->lra_rdl_prop_relevant_candidates;

        std::vector<int> reason;
        if (implied(templates, disabled_edges, reason))
            enqueue_rdl_propagation(lit, std::move(reason));
    };

    size_t processed_sigma = 0;
    for (size_t sigma_pos = 0; sigma_pos < sigma->size() && !has_conflict_; ++sigma_pos) {
        size_t edge_idx = (*sigma)[sigma_pos];
        if (edge_idx >= edges->size()) {
            ++processed_sigma;
            continue;
        }
        const ActiveGraphEdge& new_edge = (*edges)[edge_idx];
        if (edge_idx < disabled_future.size()) disabled_future[edge_idx] = 0;
        std::vector<char> disabled_without_current = disabled_future;
        if (edge_idx < disabled_without_current.size()) disabled_without_current[edge_idx] = 1;

        auto reaches_new_from = shortest_paths_to_disabled(
            new_edge.from, *edges, node_count, disabled_without_current, true);
        auto from_new_to = shortest_paths_from_disabled(
            new_edge.to, *edges, node_count, disabled_without_current, true);
        if (!reaches_new_from || !from_new_to) {
            ++processed_sigma;
            continue;
        }

        if (new_edge.from >= 0 && static_cast<size_t>(new_edge.from) < from_new_to->dist.size() &&
            from_new_to->dist[new_edge.from] &&
            *from_new_to->dist[new_edge.from] + new_edge.weight < DeltaRational(Rational(0))) {
            std::vector<int> reason = graph_path_reason(
                new_edge.to, new_edge.from, *from_new_to, *edges);
            reason.push_back(-new_edge.source_lit);
            std::sort(reason.begin(), reason.end());
            reason.erase(std::unique(reason.begin(), reason.end()), reason.end());
            if (stats_) ++stats_->lra_rdl_prop_conflicts;
            set_conflict(std::move(reason));
            break;
        }

        for (const auto& [sat_var, atom] : rdl_atoms_) {
            path_cache.clear();
            inspect(sat_var, atom.positive_edges, *reaches_new_from, *from_new_to,
                    disabled_future);
            inspect(-sat_var, atom.negative_edges, *reaches_new_from, *from_new_to,
                    disabled_future);
            if (has_conflict_ || budget_cutoff) break;
        }
        rdl_labels_[new_edge.source_lit] = RdlLabel::Pi;
        ++processed_sigma;
        if (budget_cutoff) break;
    }

    if (!model) {
        if (processed_sigma >= rdl_sigma_edge_indices_.size()) {
            rdl_sigma_edge_indices_.clear();
        } else {
            rdl_sigma_edge_indices_.erase(rdl_sigma_edge_indices_.begin(),
                                          rdl_sigma_edge_indices_.begin() + processed_sigma);
        }
        if (stats_) stats_->lra_rdl_prop_sigma = rdl_sigma_edge_indices_.size();
    }
    if (budget_cutoff && stats_) ++stats_->lra_rdl_prop_budget_cutoffs;
}

void LraSolver::discover_row_bound_propagations() {
    if (!row_bound_propagation_) return;
    if (row_bound_hit_cutoff_) return;
    size_t candidates_this_discovery = 0;

    auto enqueue = [&](int lit, std::vector<int> reason) {
        enqueue_propagation(lit, std::move(reason), true);
    };

    auto inspect_candidate = [&]() {
        if (row_bound_propagation_budget_ > 0 &&
            candidates_this_discovery >= row_bound_propagation_budget_)
            return false;
        ++candidates_this_discovery;
        if (stats_) ++stats_->lra_row_prop_candidates_considered;
        ++row_bound_window_candidates_;
        return true;
    };

    auto inspect_lower_atom = [&](const BoundAtomRef& atom,
                                  const std::optional<DeltaRational>& lower_value,
                                  const std::vector<int>& lower_sources,
                                  const std::optional<DeltaRational>& upper_value,
                                  const std::vector<int>& upper_sources) {
        if (!inspect_candidate()) return;
        if (lower_value) {
            if (*lower_value >= atom.value)
                enqueue(atom.sat_var, lower_sources);
        }
        if (upper_value) {
            if (*upper_value < atom.value)
                enqueue(-atom.sat_var, upper_sources);
        }
    };

    auto inspect_upper_atom = [&](const BoundAtomRef& atom,
                                  const std::optional<DeltaRational>& lower_value,
                                  const std::vector<int>& lower_sources,
                                  const std::optional<DeltaRational>& upper_value,
                                  const std::vector<int>& upper_sources) {
        if (!inspect_candidate()) return;
        if (lower_value) {
            if (*lower_value > atom.value)
                enqueue(-atom.sat_var, lower_sources);
        }
        if (upper_value) {
            if (*upper_value <= atom.value)
                enqueue(atom.sat_var, upper_sources);
        }
    };

    auto maybe_apply_hit_cutoff = [&]() {
        if (row_bound_min_hit_rate_ == 0 || row_bound_hit_window_ == 0 ||
            row_bound_hit_cutoff_ || row_bound_window_candidates_ < row_bound_hit_window_)
            return;
        if (row_bound_window_enqueues_ * 1000000 < row_bound_window_candidates_ * row_bound_min_hit_rate_) {
            row_bound_hit_cutoff_ = true;
            if (stats_) ++stats_->lra_row_prop_hit_cutoffs;
        }
        row_bound_window_candidates_ = 0;
        row_bound_window_enqueues_ = 0;
    };

    auto inspect_row = [&](int basic) {
        if (has_conflict_) return;
        if (row_bound_hit_cutoff_) return;
        if (row_bound_propagation_budget_ > 0 &&
            candidates_this_discovery >= row_bound_propagation_budget_)
            return;
        bool has_lower_atoms = static_cast<size_t>(basic) < lower_atoms_by_var_.size() &&
                               !lower_atoms_by_var_[basic].empty();
        bool has_upper_atoms = static_cast<size_t>(basic) < upper_atoms_by_var_.size() &&
                               !upper_atoms_by_var_[basic].empty();
        if (!has_lower_atoms && !has_upper_atoms)
            return;
        int row_idx = row_of_basic_[basic];
        if (row_idx < 0) return;
        const TableauRow& row = rows_[row_idx];

        std::optional<DeltaRational> row_lower = row.constant;
        std::optional<DeltaRational> row_upper = row.constant;
        std::vector<int> lower_sources;
        std::vector<int> upper_sources;

        for (const auto& [x, a] : row.coeffs) {
            if (a > Rational(0)) {
                if (row_lower && lower_[x].active) {
                    *row_lower += lower_[x].value * a;
                    lower_sources.push_back(-lower_[x].source_lit);
                } else {
                    row_lower.reset();
                }
                if (row_upper && upper_[x].active) {
                    *row_upper += upper_[x].value * a;
                    upper_sources.push_back(-upper_[x].source_lit);
                } else {
                    row_upper.reset();
                }
            } else if (a < Rational(0)) {
                if (row_lower && upper_[x].active) {
                    *row_lower += upper_[x].value * a;
                    lower_sources.push_back(-upper_[x].source_lit);
                } else {
                    row_lower.reset();
                }
                if (row_upper && lower_[x].active) {
                    *row_upper += lower_[x].value * a;
                    upper_sources.push_back(-lower_[x].source_lit);
                } else {
                    row_upper.reset();
                }
            }
            if (!row_lower && !row_upper) break;
        }

        if (!row_lower && !row_upper) return;
        if (has_lower_atoms)
            for (const BoundAtomRef& atom : lower_atoms_by_var_[basic])
                inspect_lower_atom(atom, row_lower, lower_sources, row_upper, upper_sources);
        if (has_upper_atoms)
            for (const BoundAtomRef& atom : upper_atoms_by_var_[basic])
                inspect_upper_atom(atom, row_lower, lower_sources, row_upper, upper_sources);
        maybe_apply_hit_cutoff();
    };

    auto row_is_dirty = [&](int basic, const TableauRow& row) {
        if (!row_bound_dirty_scan_ || !incremental_prop_scan_) return true;
        if (basic >= 0 && static_cast<size_t>(basic) < prop_var_dirty_.size() &&
            prop_var_dirty_[basic])
            return true;
        for (const auto& [x, _] : row.coeffs) {
            if (x >= 0 && static_cast<size_t>(x) < prop_var_dirty_.size() &&
                prop_var_dirty_[x])
                return true;
        }
        return false;
    };

    if (!row_bound_indexed_dirty_scan_ || !row_bound_dirty_scan_ || !incremental_prop_scan_) {
        for (int basic : basic_vars_) {
            int row_idx = row_of_basic_[basic];
            if (row_idx < 0) continue;
            if (!row_is_dirty(basic, rows_[row_idx])) continue;
            inspect_row(basic);
        }
        return;
    }

    if (rows_by_var_.empty()) {
        for (int basic : basic_vars_) inspect_row(basic);
        return;
    }

    std::vector<char> row_seen(rows_.size(), 0);
    std::vector<int> dirty_rows;
    auto mark_row = [&](int row_idx) {
        if (row_idx < 0 || static_cast<size_t>(row_idx) >= rows_.size()) return;
        if (row_seen[row_idx]) return;
        row_seen[row_idx] = 1;
        dirty_rows.push_back(row_idx);
    };

    for (int var : prop_dirty_vars_) {
        if (var < 0) continue;
        if (static_cast<size_t>(var) < is_basic_.size() && is_basic_[var])
            mark_row(row_of_basic_[var]);
        if (static_cast<size_t>(var) >= rows_by_var_.size()) continue;
        for (int row_idx : rows_by_var_[var]) mark_row(row_idx);
    }

    for (int row_idx : dirty_rows) {
        if (has_conflict_) return;
        if (row_bound_hit_cutoff_) return;
        if (static_cast<size_t>(row_idx) >= row_basic_.size()) continue;
        int basic = row_basic_[row_idx];
        inspect_row(basic);
    }
}

void LraSolver::discover_bound_propagations() {
    if (!propagation_enabled_) return;
    detect_simple_graph_conflict();
    if (has_conflict_) return;
    discover_rdl_propagations();
    if (has_conflict_) return;
    auto enqueue = [&](int lit, std::vector<int> reason) {
        enqueue_propagation(lit, std::move(reason), false);
    };
    auto inspect_lower_atom = [&](const BoundAtomRef& atom, int var) {
        if (stats_) ++stats_->lra_prop_candidates_considered;
        if (lower_[var].active) {
            DeltaRational implied = lower_[var].value;
            if (implied >= atom.value)
                enqueue(atom.sat_var, {atom.sat_var, -lower_[var].source_lit});
        }
        if (upper_[var].active) {
            DeltaRational implied = upper_[var].value;
            if (implied < atom.value)
                enqueue(-atom.sat_var, {-atom.sat_var, -upper_[var].source_lit});
        }
    };

    auto inspect_upper_atom = [&](const BoundAtomRef& atom, int var) {
        if (stats_) ++stats_->lra_prop_candidates_considered;
        if (lower_[var].active) {
            DeltaRational implied = lower_[var].value;
            if (implied > atom.value)
                enqueue(-atom.sat_var, {-atom.sat_var, -lower_[var].source_lit});
        }
        if (upper_[var].active) {
            DeltaRational implied = upper_[var].value;
            if (implied <= atom.value)
                enqueue(atom.sat_var, {atom.sat_var, -upper_[var].source_lit});
        }
    };

    if (!incremental_prop_scan_) {
        for (size_t var = 0; var < lower_atoms_by_var_.size(); ++var) {
            for (const BoundAtomRef& atom : lower_atoms_by_var_[var])
                inspect_lower_atom(atom, static_cast<int>(var));
        }
        for (size_t var = 0; var < upper_atoms_by_var_.size(); ++var) {
            for (const BoundAtomRef& atom : upper_atoms_by_var_[var])
                inspect_upper_atom(atom, static_cast<int>(var));
        }
        if (has_conflict_) return;
        discover_rdl_propagations();
        if (has_conflict_) return;
        discover_simple_graph_propagations();
        if (has_conflict_) return;
        discover_row_bound_propagations();
        for (int var : prop_dirty_vars_) {
            if (var >= 0 && static_cast<size_t>(var) < prop_var_dirty_.size())
                prop_var_dirty_[var] = false;
        }
        prop_dirty_vars_.clear();
        return;
    }

    for (int var : prop_dirty_vars_) {
        if (has_conflict_) return;
        if (var < 0) continue;
        if (static_cast<size_t>(var) < lower_atoms_by_var_.size())
            for (const BoundAtomRef& atom : lower_atoms_by_var_[var])
                inspect_lower_atom(atom, var);
        if (static_cast<size_t>(var) < upper_atoms_by_var_.size())
            for (const BoundAtomRef& atom : upper_atoms_by_var_[var])
                inspect_upper_atom(atom, var);
    }
    discover_rdl_propagations();
    if (has_conflict_) return;
    discover_simple_graph_propagations();
    if (has_conflict_) return;
    discover_row_bound_propagations();
    for (int var : prop_dirty_vars_) {
        if (var >= 0 && static_cast<size_t>(var) < prop_var_dirty_.size())
            prop_var_dirty_[var] = false;
    }
    prop_dirty_vars_.clear();
}

bool LraSolver::cb_check_found_model(const std::vector<int>& model) {
    if (stats_) ++stats_->lra_final_checks;
    if (has_conflict_) return false;
    detect_simple_graph_conflict(&model);
    if (has_conflict_) return false;
    discover_rdl_propagations(&model);
    if (has_conflict_) return false;
    discover_simple_graph_propagations(&model);
    if (has_conflict_) return false;
    if (tableau_dirty_) {
        if (!check()) return false;
        tableau_dirty_ = false;
    }
    rebuild_model();
    discover_bound_propagations();
    return true;
}

bool LraSolver::cb_has_external_clause(bool& is_forgettable) {
    if (!has_conflict_) return false;
    is_forgettable = false;
    return true;
}

int LraSolver::cb_add_external_clause_lit() {
    if (conflict_idx_ >= conflict_clause_.size()) {
        has_conflict_ = false;
        conflict_clause_.clear();
        conflict_idx_ = 0;
        return 0;
    }
    return conflict_clause_[conflict_idx_++];
}

int LraSolver::cb_propagate() {
    if (has_conflict_) return 0;
    while (prop_head_ < prop_queue_.size()) {
        if (stats_) ++stats_->lra_propagations;
        return prop_queue_[prop_head_++];
    }
    prop_queue_.clear();
    prop_head_ = 0;
    if (!tableau_dirty_) return 0;
    discover_rdl_propagations();
    if (has_conflict_) return 0;
    while (prop_head_ < prop_queue_.size()) {
        if (stats_) ++stats_->lra_propagations;
        return prop_queue_[prop_head_++];
    }
    if (!check()) return 0;
    tableau_dirty_ = false;
    discover_bound_propagations();
    if (has_conflict_) return 0;
    while (prop_head_ < prop_queue_.size()) {
        if (stats_) ++stats_->lra_propagations;
        return prop_queue_[prop_head_++];
    }
    prop_queue_.clear();
    prop_head_ = 0;
    return 0;
}

void LraSolver::add_branch_hint(int lit) {
    if (lit == 0) return;
    int sat_var = std::abs(lit);
    if (static_cast<int>(atom_assignment_.size()) <= sat_var)
        atom_assignment_.resize(sat_var + 1, 0);
    if (branch_hints_seen_.insert(lit).second) {
        branch_hints_.push_back(lit);
        observed_vars_.push_back(sat_var);
    }
}

int LraSolver::cb_decide() {
    while (branch_hint_head_ < branch_hints_.size()) {
        int lit = branch_hints_[branch_hint_head_];
        int value = current_lit_value(lit);
        if (value == 0) {
            if (stats_) ++stats_->lra_branch_decisions;
            return lit;
        }
        ++branch_hint_head_;
    }
    return 0;
}

int LraSolver::cb_add_reason_clause_lit(int propagated_lit) {
    if (propagated_lit != reason_serving_lit_) {
        reason_serving_lit_ = propagated_lit;
        reason_serving_idx_ = 0;
    }
    auto it = reason_clauses_.find(propagated_lit);
    if (it == reason_clauses_.end()) return 0;
    if (reason_serving_idx_ >= it->second.size()) {
        reason_serving_lit_ = 0;
        reason_serving_idx_ = 0;
        return 0;
    }
    return it->second[reason_serving_idx_++];
}

std::optional<Rational> LraSolver::value_of(const std::string& name) const {
    auto it = last_model_.find(name);
    if (it == last_model_.end()) return Rational(0);
    return it->second;
}

bool LraSolver::feasible_for_literals(const std::vector<int>& lits,
                                      std::map<std::string, Rational>* model) const {
    LraSolver tmp;
    for (const auto& name : real_decls_) tmp.declare_real(name);
    for (int lit : lits) {
        auto ait = atoms_.find(std::abs(lit));
        if (ait == atoms_.end()) continue;
        int v = tmp.register_atom(ait->second);
        tmp.notify_assignment(lit > 0 ? v : -v, false);
        if (tmp.has_conflict_) return false;
    }
    if (!tmp.check()) return false;
    tmp.rebuild_model();
    if (model) *model = std::move(tmp.last_model_);
    return true;
}

std::vector<int> LraSolver::minimize_conflict(std::vector<int> active) const {
    if (conflict_minimize_limit_ == 0 || active.size() > conflict_minimize_limit_) return active;
    for (size_t i = 0; i < active.size();) {
        std::vector<int> candidate;
        candidate.reserve(active.size() - 1);
        for (size_t j = 0; j < active.size(); ++j)
            if (j != i) candidate.push_back(active[j]);
        if (!candidate.empty() && !feasible_for_literals(candidate, nullptr)) active = std::move(candidate);
        else ++i;
    }
    return active;
}

} // namespace llm2smt::lra
