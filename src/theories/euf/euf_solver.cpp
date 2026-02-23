#include "theories/euf/euf_solver.h"

#include <cassert>
#include <stdexcept>

namespace llm2smt {

EufSolver::EufSolver(NodeManager& nm, Stats& stats)
    : nm_(nm), cc_(), flattener_(nm, cc_), stats_(stats) {
    diseq_level_counts_.push_back(0);
    eq_lit_level_counts_.push_back(0);
}

// ============================================================================
// Equality registration
// ============================================================================

int EufSolver::register_equality(NodeId lhs, NodeId rhs) {
    uint64_t key = atom_key(lhs, rhs);
    auto it = atom_to_lit_.find(key);
    if (it != atom_to_lit_.end()) return it->second;

    // Pre-flatten at registration time (level 0) so structural equations are
    // permanent in the CC and never need re-registration after backtracking.
    NodeId flat_lhs = flattener_.flatten_and_register(lhs);
    NodeId flat_rhs = flattener_.flatten_and_register(rhs);


    int var = next_var_++;
    EqAtom atom{lhs, rhs, flat_lhs, flat_rhs};
    lit_to_atom_[var]  = atom;
    lit_to_atom_[-var] = atom;
    atom_to_lit_[key]  = var;
    // Also index by flat node ids so build_conflict can find equations whose
    // lhs/rhs are the flat representatives (not the original NodeIds).
    flat_atom_to_lit_[atom_key(flat_lhs, flat_rhs)] = var;
    return var;
}

void EufSolver::register_permanent_equality(NodeId lhs, NodeId rhs) {
    NodeId flat_lhs = flattener_.flatten_and_register(lhs);
    NodeId flat_rhs = flattener_.flatten_and_register(rhs);
    uint64_t key = atom_key(flat_lhs, flat_rhs);
    if (!permanent_flat_eqs_.insert(key).second) return;  // already done
    cc_.add_equation(flat_lhs, flat_rhs);
}

// ============================================================================
// ExternalPropagator callbacks
// ============================================================================

void EufSolver::notify_assignment(int lit, bool /*is_fixed*/) {
    int var = (lit > 0) ? lit : -lit;
    auto it = lit_to_atom_.find(var);
    if (it == lit_to_atom_.end()) return;

    const EqAtom& atom = it->second;
    ++stats_.euf_assignments;

    if (lit > 0) {
        // Equality asserted: a = b
        ++stats_.euf_eq_assignments;
        active_eq_lits_.push_back(lit);
        eq_lit_level_counts_.back()++;
        cur_eq_assigned_.insert(lit);
        cc_.add_equation(atom.flat_lhs, atom.flat_rhs);
        // Discover any equalities now implied by the CC.
        // Skip `lit` itself — it was just assigned, already in CaDiCaL's trail.
        // Also suppress the needs_rescan_ flag: we are about to scan right now,
        // so the lazy rescan in cb_propagate would be a redundant O(n) pass.
        if (!has_conflict_) {
            needs_rescan_ = false;
            discover_propagations(lit);
        }
    } else {
        // Disequality asserted: a ≠ b
        ++stats_.euf_diseq_assignments;
        active_diseqs_.push_back(Disequality{atom.flat_lhs, atom.flat_rhs, lit});
        diseq_level_counts_.back()++;
        // Early conflict: the CC may already have merged these nodes.
        if (!has_conflict_ && cc_.are_congruent(atom.flat_lhs, atom.flat_rhs)) {
            std::vector<EqId> expl = cc_.explain(atom.flat_lhs, atom.flat_rhs);
            build_conflict(expl, lit);
        }
    }
}

void EufSolver::notify_new_decision_level() {
    cc_.push_level();
    current_level_++;
    diseq_level_counts_.push_back(0);
    eq_lit_level_counts_.push_back(0);
}

void EufSolver::notify_backtrack(size_t new_level) {
    cc_.pop_level(new_level);
    current_level_ = new_level;

    // Pop active disequalities introduced after new_level.
    while (diseq_level_counts_.size() > new_level + 1) {
        size_t count = diseq_level_counts_.back();
        diseq_level_counts_.pop_back();
        for (size_t i = 0; i < count; ++i)
            active_diseqs_.pop_back();
    }

    // Pop positive equality assignments introduced after new_level.
    while (eq_lit_level_counts_.size() > new_level + 1) {
        size_t count = eq_lit_level_counts_.back();
        eq_lit_level_counts_.pop_back();
        for (size_t i = 0; i < count; ++i) {
            cur_eq_assigned_.erase(active_eq_lits_.back());
            active_eq_lits_.pop_back();
        }
    }

    // Discard the propagation queue.  Any not-yet-served items were computed
    // against the now-undone CC state and must be recomputed.
    // reason_clauses_ is intentionally kept: theory-propagated literals that
    // survive the backtrack (at levels <= new_level) remain in CaDiCaL's trail
    // and CaDiCaL may call cb_add_reason_clause_lit for them during future
    // conflict analysis.  Stale entries for literals that were undone are
    // harmless — CaDiCaL will not ask for their reasons after backtracking
    // past them, and the entries are overwritten if the literals are
    // re-propagated.
    prop_queue_.clear();
    prop_queue_head_ = 0;
    prop_enqueued_.clear();

    // Schedule a re-scan: equalities at levels <= new_level are still in
    // CaDiCaL's trail (notify_assignment won't fire for them again), but
    // their CC implications must be re-queued for propagation.
    needs_rescan_ = true;

    has_conflict_     = false;
    conflict_clause_.clear();
    conflict_lit_idx_ = 0;
}

bool EufSolver::cb_check_found_model(const std::vector<int>& /*model*/) {
    ++stats_.euf_check_model_calls;
    for (const Disequality& d : active_diseqs_) {
        if (cc_.are_congruent(d.flat_lhs, d.flat_rhs)) {
            std::vector<EqId> expl = cc_.explain(d.flat_lhs, d.flat_rhs);
            build_conflict(expl, d.orig_lit);
            return false;
        }
    }
    return true;
}

void EufSolver::build_conflict(const std::vector<EqId>& explanation, int diseq_lit) {
    // The conflict clause is:
    //   (¬e1) ∨ (¬e2) ∨ ... ∨ (¬diseq_lit)
    // where ei are the equalities in the explanation.
    conflict_clause_.clear();
    conflict_clause_.push_back(-diseq_lit);  // negate the disequality literal
    for (EqId eq : explanation) {
        const Equation& e = cc_.get_equation(eq);
        // explain() only returns EqIds from DirectLabel edges, which are always
        // Atomic equations (rhs != NULL_NODE).  App equations only appear in
        // CongruenceLabel edges and are never surfaced in the explanation set.
        assert(e.kind == EqKind::Atomic && e.rhs != NULL_NODE);
        // CC stores flat node ids in e.lhs/e.rhs; flat_atom_to_lit_ is keyed
        // by those same flat ids, so the lookup is always correct.
        uint64_t key = atom_key(e.lhs, e.rhs);
        // Permanent equalities are always true; their negation is vacuously
        // false in the conflict clause, so dropping them keeps the clause valid
        // (it becomes a subclause, hence stronger).
        if (permanent_flat_eqs_.count(key)) continue;
        auto it = flat_atom_to_lit_.find(key);
        assert(it != flat_atom_to_lit_.end() && "equation in explanation has no SAT literal");
        conflict_clause_.push_back(-(it->second));  // negate positive literal
    }
    ++stats_.euf_conflicts;
    stats_.euf_conflict_lits_total += conflict_clause_.size();
    has_conflict_     = true;
    conflict_lit_idx_ = 0;
}

bool EufSolver::cb_has_external_clause(bool& is_forgettable) {
    if (!has_conflict_) return false;
    is_forgettable = false;
    return true;
}

int EufSolver::cb_add_external_clause_lit() {
    if (conflict_lit_idx_ >= conflict_clause_.size()) {
        has_conflict_ = false;
        conflict_clause_.clear();
        conflict_lit_idx_ = 0;
        return 0;  // end of clause
    }
    return conflict_clause_[conflict_lit_idx_++];
}

// ============================================================================
// Theory propagation
// ============================================================================

int EufSolver::cb_propagate() {
    if (needs_rescan_) {
        needs_rescan_ = false;
        discover_propagations(-1);
    }
    // Never produce propagations while a conflict is pending; let CaDiCaL
    // consume the conflict clause first (via cb_has_external_clause).
    if (has_conflict_) return 0;
    if (prop_queue_head_ < prop_queue_.size())
        return prop_queue_[prop_queue_head_++];
    return 0;
}

int EufSolver::cb_add_reason_clause_lit(int propagated_lit) {
    if (propagated_lit != reason_serving_lit_) {
        reason_serving_lit_ = propagated_lit;
        reason_serving_idx_ = 0;
    }
    auto it = reason_clauses_.find(propagated_lit);
    if (it == reason_clauses_.end()) return 0;
    const std::vector<int>& clause = it->second;
    if (reason_serving_idx_ >= clause.size()) return 0;
    return clause[reason_serving_idx_++];
}

void EufSolver::discover_propagations(int skip_lit) {
    // Step 1: check for conflicts with active disequalities first.
    // If a conflict exists, report it and skip propagation entirely.
    for (const Disequality& d : active_diseqs_) {
        if (cc_.are_congruent(d.flat_lhs, d.flat_rhs)) {
            std::vector<EqId> expl = cc_.explain(d.flat_lhs, d.flat_rhs);
            build_conflict(expl, d.orig_lit);
            return;
        }
    }

    // Step 2: scan all registered positive equality atoms for implied ones.
    for (const auto& [lit, atom] : lit_to_atom_) {
        if (lit <= 0) continue;                          // only positive literals
        if (lit == skip_lit) continue;                   // just assigned by caller
        if (prop_enqueued_.count(lit)) continue;         // already queued this pass
        if (cur_eq_assigned_.count(lit)) continue;       // already in CaDiCaL's trail
        if (!cc_.are_congruent(atom.flat_lhs, atom.flat_rhs)) continue;

        std::vector<EqId> expl = cc_.explain(atom.flat_lhs, atom.flat_rhs);
        reason_clauses_[lit] = build_reason_clause(lit, expl);
        prop_queue_.push_back(lit);
        prop_enqueued_.insert(lit);
    }
}

std::vector<int> EufSolver::build_reason_clause(int plit,
                                                  const std::vector<EqId>& expl) {
    // Reason clause: plit ∨ ¬e1 ∨ ¬e2 ∨ …
    // If all antecedent equalities hold, the CC derives plit.
    std::vector<int> clause;
    clause.push_back(plit);
    for (EqId eq : expl) {
        const Equation& e = cc_.get_equation(eq);
        assert(e.kind == EqKind::Atomic && e.rhs != NULL_NODE);
        uint64_t key = atom_key(e.lhs, e.rhs);
        if (permanent_flat_eqs_.count(key)) continue;  // no SAT var; drop
        auto it = flat_atom_to_lit_.find(key);
        assert(it != flat_atom_to_lit_.end() &&
               "explanation equation has no SAT literal");
        clause.push_back(-(it->second));
    }
    return clause;
}

} // namespace llm2smt
