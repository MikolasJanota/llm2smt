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
    lit_to_atom_[var] = atom;   // positive literal only; notify_assignment uses |lit|
    atom_to_lit_[key] = var;
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
    permanent_eq_pairs_.push_back({lhs, rhs});  // original nodes (not flat) for proof emission
    permanent_flat_to_orig_[key] = {lhs, rhs};
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
        if (!has_conflict_) {
            if (record_proofs_) {
                // In proof mode run the scan immediately: the SAT solver may find
                // a propositional contradiction via BCP alone and never call
                // cb_propagate, which would leave proof_conflicts_ empty and
                // bv_decide unable to reconstruct the EUF transitivity reasoning.
                needs_rescan_ = false;
                discover_propagations();
            } else {
                // Non-proof mode: defer to cb_propagate (called once per BCP
                // batch) to avoid O(assignments × atoms) quadratic work.
                needs_rescan_ = true;
            }
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
    // Reset the reason-clause cursor.  After backtrack the same literal may be
    // re-propagated (new reason stored in reason_clauses_[lit]).  If the cursor
    // were left at a non-zero position from a previous iteration of the same
    // literal's reason clause, cb_add_reason_clause_lit would resume mid-clause,
    // skipping the mandatory propagated-literal at index 0.
    reason_serving_lit_ = 0;
    reason_serving_idx_ = 0;

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
    std::vector<std::pair<NodeId,NodeId>> perm_deps;
    for (EqId eq : explanation) {
        const Equation& e = cc_.get_equation(eq);
        // explain() only returns EqIds from DirectLabel edges, which are always
        // Atomic equations (rhs != NULL_NODE).  App equations only appear in
        // CongruenceLabel edges and are never surfaced in the explanation set.
        assert(e.kind == EqKind::Atomic && e.rhs != NULL_NODE);
        // CC stores flat node ids in e.lhs/e.rhs; flat_atom_to_lit_ is keyed
        // by those same flat ids, so the lookup is always correct.
        uint64_t key = atom_key(e.lhs, e.rhs);
        // Permanent equalities have no SAT literal; skipping them keeps the
        // clause valid (it becomes a subclause, hence stronger).
        // An equality may be BOTH in flat_atom_to_lit_ (pre-registered before
        // preprocessing decided it was permanent) AND in permanent_flat_eqs_.
        // In that case treat it as permanent: including the pre-registered SAT
        // literal would produce a tautological clause {V, ¬V} that crashes
        // CaDiCaL's analyze().
        if (permanent_flat_eqs_.count(key)) {
            // Record original-node pair for proof emission.
            auto pit = permanent_flat_to_orig_.find(key);
            if (pit != permanent_flat_to_orig_.end())
                perm_deps.push_back(pit->second);
            continue;
        }
        auto it = flat_atom_to_lit_.find(key);
        if (it == flat_atom_to_lit_.end()) {
            assert(false && "equation in explanation has no SAT literal and is not permanent");
            continue;
        }
        conflict_clause_.push_back(-(it->second));  // negate positive literal
    }
    ++stats_.euf_conflicts;
    stats_.euf_conflict_lits_total += conflict_clause_.size();
    has_conflict_     = true;
    conflict_lit_idx_ = 0;
    if (record_proofs_) {
        proof_conflicts_.push_back(conflict_clause_);
        // Record permanent-equality deps for ALL conflict clauses.
        // For unit clauses these become implication premises (transitivity form).
        // For non-unit clauses they also become premises so that grind can use
        // congruence over permanent equalities that were dropped from the SAT clause.
        proof_unit_perm_deps_.push_back(std::move(perm_deps));
    }
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
    // Always run the propagation scan when needed, even if a conflict is already
    // pending.  The scan (Step 1 of discover_propagations) must record reason
    // clauses in proof_conflicts_ for proof completeness.  When notify_assignment
    // detects an early conflict before cb_propagate runs, the scan would be
    // skipped by the old !has_conflict_ guard, leaving transitivity lemmas out
    // of the proof and causing bv_decide to fail with a spurious counterexample.
    if (needs_rescan_) {
        needs_rescan_ = false;
        discover_propagations();
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

void EufSolver::discover_propagations() {
    // Step 1: scan all registered equality atoms for implied ones.
    // Must run before conflict detection so that theory propagation reason
    // clauses are always recorded in proof_conflicts_ even when a disequality
    // conflict is about to be reported (which would cause an early return).
    // lit_to_atom_ stores only positive literals, so no sign filter needed.
    //
    // In proof-recording mode we also process already-assigned atoms: SAT may
    // have assigned an equality TRUE before the theory could propagate it, so
    // there would be no reason clause recorded for it.  Without the clause,
    // bv_decide cannot derive the EUF transitivity step and fails with a
    // spurious counterexample.  We mark such atoms in prop_enqueued_ to avoid
    // re-processing them on the next rescan.
    for (const auto& [lit, atom] : lit_to_atom_) {
        if (prop_enqueued_.count(lit)) continue;         // already handled this pass
        bool already_assigned = cur_eq_assigned_.count(lit) > 0;
        if (already_assigned && !record_proofs_) continue; // skip if assigned (non-proof mode)
        if (!cc_.are_congruent(atom.flat_lhs, atom.flat_rhs)) continue;

        std::vector<EqId> expl = cc_.explain(atom.flat_lhs, atom.flat_rhs);
        std::vector<std::pair<NodeId,NodeId>> perm_deps;
        reason_clauses_[lit] = build_reason_clause(lit, expl,
                                                    record_proofs_ ? &perm_deps : nullptr);
        if (record_proofs_) {
            const auto& rc = reason_clauses_[lit];
            // Unit clauses (size==1) for already-assigned atoms must always be
            // skipped.  Two sub-cases:
            //   (a) perm_deps empty: the atom is directly in the hypothesis axioms
            //       and bv_decide can use it without a separate lemma.
            //   (b) perm_deps non-empty: the permanent equalities in the explanation
            //       are artifacts of the CC union-by-size proof forest traversal
            //       (the class containing lhs/rhs was merged INTO the other class,
            //       so the proof path goes through permanent edges that are not
            //       genuine reason premises for this atom).  The theorem produced
            //       would be false (perm_deps ⇏ lhs=rhs in general).
            // In both cases the atom was SAT-assigned directly, so bv_decide can
            // recover it from the propositional encoding of the hypothesis axioms.
            if (already_assigned && rc.size() == 1) {
                // skip — redundant or incorrect for already-assigned unit atoms
            } else {
                proof_conflicts_.push_back(rc);
                proof_unit_perm_deps_.push_back(std::move(perm_deps));
            }
        }
        prop_enqueued_.insert(lit);  // mark as handled (prevent duplicate recording)
        if (!already_assigned) {
            prop_queue_.push_back(lit);
        }
    }

    // Step 2: check for conflicts with active disequalities.
    // Skip if a conflict was already detected by notify_assignment (early
    // detection path): in that case has_conflict_ is true and build_conflict
    // has already been called, so we must not overwrite the conflict clause
    // with a duplicate or corrupt the conflict_lit_idx_ that CaDiCaL will
    // consume via cb_has_external_clause / cb_add_external_clause_lit.
    if (!has_conflict_) {
        for (const Disequality& d : active_diseqs_) {
            if (cc_.are_congruent(d.flat_lhs, d.flat_rhs)) {
                std::vector<EqId> expl = cc_.explain(d.flat_lhs, d.flat_rhs);
                build_conflict(expl, d.orig_lit);
                return;
            }
        }
    }
}

std::vector<int> EufSolver::build_reason_clause(int plit,
                                                  const std::vector<EqId>& expl,
                                                  std::vector<std::pair<NodeId,NodeId>>* out_perm_deps) {
    // Reason clause: plit ∨ ¬e1 ∨ ¬e2 ∨ …
    // If all antecedent equalities hold, the CC derives plit.
    std::vector<int> clause;
    clause.push_back(plit);
    for (EqId eq : expl) {
        const Equation& e = cc_.get_equation(eq);
        assert(e.kind == EqKind::Atomic && e.rhs != NULL_NODE);
        uint64_t key = atom_key(e.lhs, e.rhs);
        // Same dual-registration guard as build_conflict: an equality may be
        // both in flat_atom_to_lit_ and permanent_flat_eqs_ if register_equality
        // was called before the simplifier decided it was permanent.  Treat as
        // permanent so the reason clause stays non-tautological.
        if (permanent_flat_eqs_.count(key)) {
            // Collect perm_deps when requested (for proof emission).
            if (out_perm_deps) {
                auto pit = permanent_flat_to_orig_.find(key);
                if (pit != permanent_flat_to_orig_.end())
                    out_perm_deps->push_back(pit->second);
            }
            continue;
        }
        auto it = flat_atom_to_lit_.find(key);
        if (it == flat_atom_to_lit_.end()) {
            assert(false && "explanation equation has no SAT literal and is not permanent");
            continue;
        }
        // Skip self-referential equation: when the SAT assignment for plit was
        // processed before the CC had established congruence via permanents, the
        // CC proof forest received a direct edge for that atom.  explain() then
        // returns that edge alongside the permanent chain, causing clause [+L, -L].
        // Skipping the self-edge leaves only the permanent chain in the reason.
        if (it->second == plit) continue;
        clause.push_back(-(it->second));
    }
    return clause;
}

} // namespace llm2smt
