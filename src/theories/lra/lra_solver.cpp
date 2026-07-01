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
        prop_var_dirty_.resize(v + 1);
    }
    is_basic_[v] = basic;
    if (basic) basic_vars_.push_back(v);
    else nonbasic_vars_.push_back(v);
    return v;
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
    rows_.push_back(std::move(row));
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
    if (stats_) ++stats_->lra_atoms;
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
    atoms_by_var_[ea.var].push_back(sat_var);
    return sat_var;
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
    auto it = elementary_atoms_.find(std::abs(lit));
    if (it == elementary_atoms_.end()) return;
    if (stats_) ++stats_->lra_assignments;
    tableau_dirty_ = true;
    trail_.push_back(lit);
    level_counts_.back()++;

    const ElementaryAtom& ea = it->second;
    bool positive = lit > 0;
    if (ea.equality) {
        if (!positive)
            throw std::runtime_error("negative LRA equality atom must be encoded as strict-bound disjunction");
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
}

void LraSolver::notify_backtrack(size_t new_level) {
    while (level_counts_.size() > new_level + 1) {
        size_t n = level_counts_.back();
        level_counts_.pop_back();
        while (n-- > 0) trail_.pop_back();
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
    reason_serving_lit_ = 0;
    reason_serving_idx_ = 0;
}

void LraSolver::update(int x, const DeltaRational& v) {
    DeltaRational delta = v - beta_[x];
    if (delta.is_zero()) return;
    beta_[x] = v;
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

    for (int b : basic_vars_) {
        if (b == basic) continue;
        int rb = row_of_basic_[b];
        auto it = rows_[rb].coeffs.find(nonbasic);
        if (it == rows_[rb].coeffs.end() || it->second.is_zero()) continue;
        Rational factor = it->second;
        rows_[rb].coeffs.erase(it);
        rows_[rb].constant += solved.constant * factor;
        for (const auto& [v, c] : solved.coeffs) rows_[rb].coeffs[v] += c * factor;
        for (auto cit = rows_[rb].coeffs.begin(); cit != rows_[rb].coeffs.end();) {
            if (cit->second.is_zero()) cit = rows_[rb].coeffs.erase(cit);
            else ++cit;
        }
    }

    rows_[r] = std::move(solved);
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

void LraSolver::recompute_basic_values() {
    for (int b : basic_vars_) {
        int r = row_of_basic_[b];
        DeltaRational value = rows_[r].constant;
        for (const auto& [x, a] : rows_[r].coeffs) value += beta_[x] * a;
        beta_[b] = value;
    }
}

bool LraSolver::pivot_and_update(int basic, int nonbasic, const DeltaRational& value) {
    // Dutertre/de Moura Figure 3.1 PivotAndUpdate.
    if (!pivot(basic, nonbasic)) return false;
    recompute_basic_values();
    int r = row_of_basic_[nonbasic];
    auto it = rows_[r].coeffs.find(basic);
    if (it == rows_[r].coeffs.end() || it->second.is_zero()) return false;
    DeltaRational rest = rows_[r].constant;
    for (const auto& [x, a] : rows_[r].coeffs) {
        if (x == basic) continue;
        rest += beta_[x] * a;
    }
    update(basic, (value - rest) / it->second);
    return true;
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
    // Dutertre/de Moura Figure 3.2 Check, using Bland's smallest-variable rule.
    if (stats_) ++stats_->lra_check_calls;
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
        if (bad < 0) return true;

        int entering = -1;
        DeltaRational target;
        const auto& row = rows_[row_of_basic_[bad]];
        if (below) {
            for (const auto& [x, a] : row.coeffs) {
                bool ok = (a > Rational(0) && (!upper_[x].active || beta_[x] < upper_[x].value)) ||
                          (a < Rational(0) && (!lower_[x].active || beta_[x] > lower_[x].value));
                if (ok && (entering < 0 || x < entering)) {
                    entering = x;
                    DeltaRational repair = beta_[x] + (lower_[bad].value - beta_[bad]) / a;
                    if (a > Rational(0))
                        target = upper_[x].active && upper_[x].value < repair ? upper_[x].value : repair;
                    else
                        target = lower_[x].active && lower_[x].value > repair ? lower_[x].value : repair;
                }
            }
            if (entering < 0) {
                set_conflict(explain_lower_conflict(bad));
                return false;
            }
        } else {
            for (const auto& [x, a] : row.coeffs) {
                bool ok = (a < Rational(0) && (!upper_[x].active || beta_[x] < upper_[x].value)) ||
                          (a > Rational(0) && (!lower_[x].active || beta_[x] > lower_[x].value));
                if (ok && (entering < 0 || x < entering)) {
                    entering = x;
                    DeltaRational repair = beta_[x] + (upper_[bad].value - beta_[bad]) / a;
                    if (a < Rational(0))
                        target = upper_[x].active && upper_[x].value < repair ? upper_[x].value : repair;
                    else
                        target = lower_[x].active && lower_[x].value > repair ? lower_[x].value : repair;
                }
            }
            if (entering < 0) {
                set_conflict(explain_upper_conflict(bad));
                return false;
            }
        }
        if (!pivot_and_update(bad, entering, target)) {
            set_conflict({-trail_.back()});
            return false;
        }
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

void LraSolver::discover_bound_propagations() {
    if (!propagation_enabled_) return;
    auto enqueue = [&](int lit, std::vector<int> reason) {
        if (reason.size() > 1 && lit == -reason[1]) return;
        if (prop_enqueued_.insert(lit).second) {
            prop_queue_.push_back(lit);
            reason_clauses_[lit] = std::move(reason);
        }
    };
    auto inspect_atom = [&](int sat_var, const ElementaryAtom& ea) {
        if (stats_) ++stats_->lra_prop_candidates_considered;
        if (lower_[ea.var].active) {
            DeltaRational implied = lower_[ea.var].value;
            if (ea.positive_kind == BoundKind::Lower && implied >= ea.positive_value)
                enqueue(sat_var, {sat_var, -lower_[ea.var].source_lit});
            if (ea.positive_kind == BoundKind::Upper && implied > ea.positive_value)
                enqueue(-sat_var, {-sat_var, -lower_[ea.var].source_lit});
        }
        if (upper_[ea.var].active) {
            DeltaRational implied = upper_[ea.var].value;
            if (ea.positive_kind == BoundKind::Upper && implied <= ea.positive_value)
                enqueue(sat_var, {sat_var, -upper_[ea.var].source_lit});
            if (ea.positive_kind == BoundKind::Lower && implied < ea.positive_value)
                enqueue(-sat_var, {-sat_var, -upper_[ea.var].source_lit});
        }
    };

    if (!incremental_prop_scan_) {
        for (const auto& [sat_var, ea] : elementary_atoms_) inspect_atom(sat_var, ea);
        for (int var : prop_dirty_vars_) {
            if (var >= 0 && static_cast<size_t>(var) < prop_var_dirty_.size())
                prop_var_dirty_[var] = false;
        }
        prop_dirty_vars_.clear();
        return;
    }

    for (int var : prop_dirty_vars_) {
        if (var < 0 || static_cast<size_t>(var) >= atoms_by_var_.size()) continue;
        for (int sat_var : atoms_by_var_[var]) {
            auto it = elementary_atoms_.find(sat_var);
            if (it == elementary_atoms_.end()) continue;
            inspect_atom(sat_var, it->second);
        }
    }
    for (int var : prop_dirty_vars_) {
        if (var >= 0 && static_cast<size_t>(var) < prop_var_dirty_.size())
            prop_var_dirty_[var] = false;
    }
    prop_dirty_vars_.clear();
}

bool LraSolver::cb_check_found_model(const std::vector<int>&) {
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
    if (!check()) return 0;
    tableau_dirty_ = false;
    discover_bound_propagations();
    while (prop_head_ < prop_queue_.size()) {
        if (stats_) ++stats_->lra_propagations;
        return prop_queue_[prop_head_++];
    }
    prop_queue_.clear();
    prop_head_ = 0;
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
