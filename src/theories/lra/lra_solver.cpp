#include "theories/lra/lra_solver.h"

#include <algorithm>
#include <sstream>
#include <stdexcept>
#include <set>
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
    if (real_decl_seen_.emplace(name, true).second)
        real_decls_.push_back(name);
}

void LraSolver::set_fm_elim_order(std::string order) {
    if (order == "min-fill") {
        use_min_fill_elim_ = true;
        return;
    }
    if (order == "name") {
        use_min_fill_elim_ = false;
        return;
    }
    throw std::runtime_error("unknown LRA Fourier-Motzkin elimination order: " + order);
}

void LraSolver::set_conflict_minimize_limit(size_t limit) {
    conflict_minimize_limit_ = limit;
}

std::string LraSolver::atom_key(const Atom& atom) {
    std::ostringstream os;
    os << static_cast<int>(atom.rel) << ":" << atom.lhs_minus_rhs.constant << ":";
    for (const auto& [v, c] : atom.lhs_minus_rhs.coeffs) os << v << "=" << c << ";";
    return os.str();
}

int LraSolver::register_atom(const Atom& atom) {
    std::string key = atom_key(atom);
    auto it = atom_keys_.find(key);
    if (it != atom_keys_.end()) return it->second;
    int var = new_var();
    atoms_[var] = atom;
    atom_keys_[std::move(key)] = var;
    observed_vars_.push_back(var);
    return var;
}

void LraSolver::notify_assignment(int lit, bool) {
    if (!atoms_.contains(std::abs(lit))) return;
    trail_.push_back(lit);
    level_counts_.back()++;
}

void LraSolver::notify_new_decision_level() {
    level_counts_.push_back(0);
}

void LraSolver::notify_backtrack(size_t new_level) {
    while (level_counts_.size() > new_level + 1) {
        size_t n = level_counts_.back();
        level_counts_.pop_back();
        while (n-- > 0) trail_.pop_back();
    }
    has_conflict_ = false;
    conflict_clause_.clear();
    conflict_idx_ = 0;
}

static Relation negate_rel(Relation r) {
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

void LraSolver::add_ineq_for_literal(const Atom& atom, int lit, std::vector<Inequality>& out) {
    Relation rel = lit > 0 ? atom.rel : negate_rel(atom.rel);
    auto push_le_zero = [&](const LinearExpr& e, bool strict) {
        Inequality in;
        in.coeffs = e.coeffs;
        in.rhs = -e.constant;
        in.strict = strict;
        out.push_back(std::move(in));
    };
    auto neg = atom.lhs_minus_rhs;
    neg.scale(Rational(-1));

    switch (rel) {
    case Relation::Le: push_le_zero(atom.lhs_minus_rhs, false); break;
    case Relation::Lt: push_le_zero(atom.lhs_minus_rhs, true); break;
    case Relation::Ge: push_le_zero(neg, false); break;
    case Relation::Gt: push_le_zero(neg, true); break;
    case Relation::Eq:
        push_le_zero(atom.lhs_minus_rhs, false);
        push_le_zero(neg, false);
        break;
    case Relation::Ne:
        throw std::runtime_error("internal LRA disequality literal reached inequality encoder");
    }
}

void LraSolver::add_diseq_for_literal(const Atom& atom, int lit, std::vector<LinearExpr>& out) {
    Relation rel = lit > 0 ? atom.rel : negate_rel(atom.rel);
    if (rel == Relation::Ne) {
        out.push_back(atom.lhs_minus_rhs);
        return;
    }
    if (rel == Relation::Eq) return;
    throw std::runtime_error("internal LRA non-disequality literal reached disequality encoder");
}

bool LraSolver::check_ineqs(const std::vector<Inequality>& ineqs,
                            const std::map<std::string, Rational>& model) {
    for (const auto& in : ineqs) {
        Rational lhs(0);
        for (const auto& [v, c] : in.coeffs) {
            auto it = model.find(v);
            lhs += c * (it == model.end() ? Rational(0) : it->second);
        }
        if (in.strict ? !(lhs < in.rhs) : !(lhs <= in.rhs)) return false;
    }
    return true;
}

bool LraSolver::choose_value_for(const std::string& var,
                                 const std::vector<Inequality>& ineqs,
                                 const std::map<std::string, Rational>& model,
                                 Rational& value) {
    struct Bound { Rational value; bool strict = false; };
    std::optional<Bound> lower;
    std::optional<Bound> upper;

    for (const auto& in : ineqs) {
        auto ait = in.coeffs.find(var);
        if (ait == in.coeffs.end() || ait->second.is_zero()) continue;

        Rational rest(0);
        for (const auto& [v, c] : in.coeffs) {
            if (v == var) continue;
            auto mit = model.find(v);
            rest += c * (mit == model.end() ? Rational(0) : mit->second);
        }

        Rational a = ait->second;
        Rational b = (in.rhs - rest) / a;
        if (a > Rational(0)) {
            if (!upper || b < upper->value || (b == upper->value && in.strict && !upper->strict))
                upper = Bound{b, in.strict};
        } else {
            if (!lower || b > lower->value || (b == lower->value && in.strict && !lower->strict))
                lower = Bound{b, in.strict};
        }
    }

    if (lower && upper) {
        if (lower->value > upper->value) return false;
        if (lower->value == upper->value) {
            if (lower->strict || upper->strict) return false;
            value = lower->value;
            return true;
        }
        value = (lower->value + upper->value) / Rational(2);
        return true;
    }
    if (lower) {
        value = lower->strict ? lower->value + Rational(1) : lower->value;
        return true;
    }
    if (upper) {
        value = upper->strict ? upper->value - Rational(1) : upper->value;
        return true;
    }
    value = Rational(0);
    return true;
}

bool LraSolver::solve_projected(std::vector<Inequality> ineqs,
                                std::vector<std::string> vars,
                                std::map<std::string, Rational>& model,
                                bool use_min_fill_elim) {
    // Complete Fourier-Motzkin elimination over exact rationals. The recursive
    // form also reconstructs a satisfying point for model printing. The choice
    // of eliminated variable is the main performance lever: eliminating x
    // creates |lower(x)|*|upper(x)| projected inequalities. Pick the currently
    // cheapest variable instead of using declaration/name order.
    while (!vars.empty()) {
        size_t best_idx = use_min_fill_elim ? vars.size() : vars.size() - 1;
        size_t best_pairs = 0;
        size_t best_occurs = 0;
        if (use_min_fill_elim) {
            for (size_t i = 0; i < vars.size(); ++i) {
                size_t pos = 0, neg = 0, occurs = 0;
                for (const auto& in : ineqs) {
                    auto it = in.coeffs.find(vars[i]);
                    if (it == in.coeffs.end() || it->second.is_zero()) continue;
                    ++occurs;
                    if (it->second > Rational(0)) ++pos;
                    else ++neg;
                }
                size_t pairs = pos * neg;
                if (best_idx == vars.size() || pairs < best_pairs ||
                    (pairs == best_pairs && occurs < best_occurs)) {
                    best_idx = i;
                    best_pairs = pairs;
                    best_occurs = occurs;
                    if (pairs == 0 && occurs == 0) break;
                }
            }
        } else {
            for (const auto& in : ineqs) {
                auto it = in.coeffs.find(vars[best_idx]);
                if (it == in.coeffs.end() || it->second.is_zero()) continue;
                ++best_occurs;
            }
        }

        std::string var = vars[best_idx];
        vars.erase(vars.begin() + static_cast<std::ptrdiff_t>(best_idx));

        if (best_occurs == 0) {
            model[var] = Rational(0);
            continue;
        }

        std::vector<Inequality> pos, neg, zero;
        for (auto in : ineqs) {
            auto it = in.coeffs.find(var);
            if (it == in.coeffs.end() || it->second.is_zero()) {
                in.coeffs.erase(var);
                zero.push_back(std::move(in));
            } else if (it->second > Rational(0)) {
                pos.push_back(std::move(in));
            } else {
                neg.push_back(std::move(in));
            }
        }

        std::vector<Inequality> projected = std::move(zero);
        for (const auto& p : pos) {
            Rational ap = p.coeffs.at(var);
            for (const auto& n : neg) {
                Rational an = n.coeffs.at(var);
                Inequality c;
                c.strict = p.strict || n.strict;
                for (const auto& [v, coeff] : p.coeffs)
                    if (v != var) c.coeffs[v] += coeff / ap;
                for (const auto& [v, coeff] : n.coeffs)
                    if (v != var) c.coeffs[v] += coeff / (-an);
                c.rhs = p.rhs / ap + n.rhs / (-an);
                for (auto it = c.coeffs.begin(); it != c.coeffs.end(); ) {
                    if (it->second.is_zero()) it = c.coeffs.erase(it);
                    else ++it;
                }
                projected.push_back(std::move(c));
            }
        }

        if (!solve_projected(projected, vars, model, use_min_fill_elim)) return false;

        Rational value;
        if (!choose_value_for(var, ineqs, model, value)) return false;
        model[var] = value;
        return check_ineqs(ineqs, model);
    }

    for (const auto& in : ineqs) {
        if (in.coeffs.empty()) {
            if (in.strict ? !(Rational(0) < in.rhs) : !(Rational(0) <= in.rhs))
                return false;
        }
    }
    return true;
}

bool LraSolver::feasible(std::vector<Inequality> ineqs,
                         std::map<std::string, Rational>* model,
                         bool use_min_fill_elim) {
    std::set<std::string> vars_set;
    for (const auto& in : ineqs)
        for (const auto& [v, _] : in.coeffs) vars_set.insert(v);
    std::vector<std::string> vars(vars_set.begin(), vars_set.end());

    std::map<std::string, Rational> candidate;
    if (!solve_projected(std::move(ineqs), std::move(vars), candidate, use_min_fill_elim))
        return false;
    if (model) *model = std::move(candidate);
    return true;
}

bool LraSolver::feasible_with_disequalities(std::vector<Inequality> ineqs,
                                            const std::vector<LinearExpr>& diseqs,
                                            size_t diseq_idx,
                                            std::map<std::string, Rational>* model,
                                            bool use_min_fill_elim) {
    if (diseq_idx == diseqs.size())
        return feasible(std::move(ineqs), model, use_min_fill_elim);

    auto push_le_zero = [](const LinearExpr& e, bool strict) {
        Inequality in;
        in.coeffs = e.coeffs;
        in.rhs = -e.constant;
        in.strict = strict;
        return in;
    };

    // A disequality e != 0 is the non-convex split e < 0 ∨ -e < 0.
    // This is only used for complete final checks and false equality atoms.
    auto left = ineqs;
    left.push_back(push_le_zero(diseqs[diseq_idx], true));
    if (feasible_with_disequalities(std::move(left), diseqs, diseq_idx + 1, model,
                                    use_min_fill_elim))
        return true;

    auto neg = diseqs[diseq_idx];
    neg.scale(Rational(-1));
    auto right = std::move(ineqs);
    right.push_back(push_le_zero(neg, true));
    return feasible_with_disequalities(std::move(right), diseqs, diseq_idx + 1, model,
                                       use_min_fill_elim);
}

bool LraSolver::feasible_for_literals(const std::vector<int>& lits,
                                      std::map<std::string, Rational>* model) const {
    std::vector<Inequality> ineqs;
    std::vector<LinearExpr> diseqs;
    for (int lit : lits) {
        auto it = atoms_.find(std::abs(lit));
        if (it == atoms_.end()) continue;
        Relation rel = lit > 0 ? it->second.rel : negate_rel(it->second.rel);
        if (rel == Relation::Ne)
            add_diseq_for_literal(it->second, lit, diseqs);
        else
            add_ineq_for_literal(it->second, lit, ineqs);
    }
    return feasible_with_disequalities(std::move(ineqs), diseqs, 0, model, use_min_fill_elim_);
}

std::vector<int> LraSolver::minimize_conflict(std::vector<int> active) const {
    // Section 3.2.2 explanations need only be sufficient, not globally
    // minimal. This deletion pass computes a subset-minimal exact explanation
    // by asking the same complete LRA checker whether each literal is needed.
    // On large industrial formulas that can dominate solving time because each
    // trial re-runs Fourier-Motzkin. Keep the precise minimization for small
    // explanations and return the sufficient full clause for larger conflicts.
    if (conflict_minimize_limit_ == 0 || active.size() > conflict_minimize_limit_)
        return active;
    for (size_t i = 0; i < active.size();) {
        std::vector<int> candidate;
        candidate.reserve(active.size() - 1);
        for (size_t j = 0; j < active.size(); ++j)
            if (j != i) candidate.push_back(active[j]);
        if (!candidate.empty() && !feasible_for_literals(candidate, nullptr)) {
            active = std::move(candidate);
        } else {
            ++i;
        }
    }
    return active;
}

bool LraSolver::cb_check_found_model(const std::vector<int>&) {
    std::vector<int> active;
    for (int lit : trail_) {
        auto it = atoms_.find(std::abs(lit));
        if (it == atoms_.end()) continue;
        active.push_back(lit);
    }

    std::map<std::string, Rational> model;
    if (feasible_for_literals(active, &model)) {
        last_model_ = std::move(model);
        return true;
    }

    active = minimize_conflict(std::move(active));
    conflict_clause_.clear();
    for (int lit : active) conflict_clause_.push_back(-lit);
    if (conflict_clause_.empty()) conflict_clause_.push_back(1);
    last_conflict_size_ = conflict_clause_.size();
    conflict_idx_ = 0;
    has_conflict_ = true;
    return false;
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

std::optional<Rational> LraSolver::value_of(const std::string& name) const {
    auto it = last_model_.find(name);
    if (it == last_model_.end()) return Rational(0);
    return it->second;
}

} // namespace llm2smt::lra
