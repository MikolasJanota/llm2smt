#include "theories/euf/euf_solver.h"

#include <algorithm>
#include <cassert>

namespace llm2smt {

EufSolver::EufSolver(NodeManager& nm, Stats& stats)
    : nm_(nm), cc_(), flattener_(nm, cc_), stats_(stats) {
    diseq_level_counts_.push_back(0);
    eq_lit_level_counts_.push_back(0);
    prop_delivered_level_counts_.push_back(0);
    assign_level_counts_.push_back(0);
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
    ++cur_total_assigned_;
    assign_level_counts_.back()++;
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
            std::vector<CC::RawCongStep> raw_congs;
            std::vector<EqId> expl = cc_.explain(atom.flat_lhs, atom.flat_rhs,
                                                  record_proofs_ ? &raw_congs : nullptr);
            build_conflict(expl, lit);
            if (record_proofs_) record_cong_steps(raw_congs);
        }
    }
}

void EufSolver::notify_new_decision_level() {
    cc_.push_level();
    current_level_++;
    diseq_level_counts_.push_back(0);
    eq_lit_level_counts_.push_back(0);
    prop_delivered_level_counts_.push_back(0);
    assign_level_counts_.push_back(0);
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

    // Pop total assignment counts introduced after new_level.
    while (assign_level_counts_.size() > new_level + 1) {
        assert(cur_total_assigned_ >= assign_level_counts_.back());
        cur_total_assigned_ -= assign_level_counts_.back();
        assign_level_counts_.pop_back();
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
    // Repair prop_enqueued_: only clear entries whose theory propagation was
    // undone by this backtrack.  Surviving literals (delivered at levels <=
    // new_level) remain in prop_enqueued_ so the post-backtrack rescan does not
    // re-explain and re-propagate them — the bulk of the per-backtrack overhead
    // with the old "clear everything" approach.
    //
    // Step 1 — unconsumed (queued but never delivered to CaDiCaL): CaDiCaL
    // never saw them so they need re-propagation after backtrack.
    for (size_t i = prop_queue_head_; i < prop_queue_.size(); ++i)
        prop_enqueued_.erase(prop_queue_[i]);
    // Step 2 — delivered literals at levels > new_level: CaDiCaL undid them.
    while (prop_delivered_level_counts_.size() > new_level + 1) {
        const size_t count = prop_delivered_level_counts_.back();
        prop_delivered_level_counts_.pop_back();
        for (size_t i = 0; i < count; ++i) {
            prop_enqueued_.erase(prop_delivered_lits_.back());
            prop_delivered_lits_.pop_back();
        }
    }
    prop_queue_.clear();
    prop_queue_head_ = 0;
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
    // Do NOT reset prop_adaptive_interval_ here.  The level-aware
    // prop_enqueued_ already cleared entries for undone literals, so the next
    // scan will naturally rediscover only those.  Resetting the interval on
    // every backtrack would restart frequent full scans on each of the
    // O(conflicts) backtracks, recreating the O(|atoms| × |backtracks|)
    // overhead this heuristic is designed to avoid.

    has_conflict_     = false;
    conflict_clause_.clear();
    conflict_lit_idx_ = 0;
}

bool EufSolver::cb_check_found_model(const std::vector<int>& /*model*/) {
    ++stats_.euf_check_model_calls;
    for (const Disequality& d : active_diseqs_) {
        if (cc_.are_congruent(d.flat_lhs, d.flat_rhs)) {
            std::vector<CC::RawCongStep> raw_congs;
            std::vector<EqId> expl = cc_.explain(d.flat_lhs, d.flat_rhs,
                                                  record_proofs_ ? &raw_congs : nullptr);
            build_conflict(expl, d.orig_lit);
            if (record_proofs_) record_cong_steps(raw_congs);
            return false;
        }
    }
    return true;
}

// ── Proof helpers ─────────────────────────────────────────────────────────────

std::vector<int> EufSolver::eqids_to_lits(const std::vector<EqId>& eqids) const {
    std::vector<int> lits;
    for (EqId eq : eqids) {
        const Equation& e = cc_.get_equation(eq);
        if (e.kind != EqKind::Atomic || e.rhs == NULL_NODE) continue;
        uint64_t key = atom_key(e.lhs, e.rhs);
        if (permanent_flat_eqs_.count(key)) continue;
        auto it = flat_atom_to_lit_.find(key);
        if (it != flat_atom_to_lit_.end())
            lits.push_back(it->second);
    }
    std::sort(lits.begin(), lits.end());
    lits.erase(std::unique(lits.begin(), lits.end()), lits.end());
    return lits;
}

void EufSolver::record_cong_steps(const std::vector<CC::RawCongStep>& raw_congs) {
    for (const auto& rcs : raw_congs) {
        if (rcs.result_lhs == NULL_NODE || rcs.result_rhs == NULL_NODE) continue;
        if (rcs.result_lhs == rcs.result_rhs) continue;
        uint64_t key = atom_key(rcs.result_lhs, rcs.result_rhs);
        if (!proof_cong_seen_.insert(key).second) continue;

        // Collect leaf SAT atoms for each premise pair.
        std::vector<int> prem_lits;
        if (rcs.fn_lhs != NULL_NODE && rcs.fn_lhs != rcs.fn_rhs) {
            auto sub = cc_.explain(rcs.fn_lhs, rcs.fn_rhs);
            auto lits = eqids_to_lits(sub);
            prem_lits.insert(prem_lits.end(), lits.begin(), lits.end());
        }
        if (rcs.arg_lhs != NULL_NODE && rcs.arg_lhs != rcs.arg_rhs) {
            auto sub = cc_.explain(rcs.arg_lhs, rcs.arg_rhs);
            auto lits = eqids_to_lits(sub);
            prem_lits.insert(prem_lits.end(), lits.begin(), lits.end());
        }
        std::sort(prem_lits.begin(), prem_lits.end());
        prem_lits.erase(std::unique(prem_lits.begin(), prem_lits.end()), prem_lits.end());

        proof_cong_steps_.push_back({rcs.result_lhs, rcs.result_rhs, std::move(prem_lits)});
    }
}

// ── Conflict clause building ───────────────────────────────────────────────────

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
        // Global content dedup: skip if this exact set of literals was already recorded
        // (e.g., a propagation reason and a conflict clause may be identical).
        auto ckey = conflict_clause_;
        std::sort(ckey.begin(), ckey.end());
        if (!proof_clause_content_seen_.insert(ckey).second) {
            // exact duplicate — nothing to do
        } else {
            auto it = proof_recorded_conflict_diseqs_.find(diseq_lit);
            if (it == proof_recorded_conflict_diseqs_.end()) {
                // First occurrence: store it.
                proof_recorded_conflict_diseqs_[diseq_lit] = proof_conflicts_.size();
                proof_conflicts_.push_back(conflict_clause_);
                proof_unit_perm_deps_.push_back(std::move(perm_deps));
            } else if (conflict_clause_.size() < proof_conflicts_[it->second].size()) {
                // Shorter clause derived after CDCL backtrack: replace the stored one.
                proof_conflicts_[it->second] = conflict_clause_;
                proof_unit_perm_deps_[it->second] = std::move(perm_deps);
            }
        }
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
    if (prop_queue_head_ < prop_queue_.size()) {
        const int lit = prop_queue_[prop_queue_head_++];
        // Record which level this literal is being delivered at so
        // notify_backtrack can correctly clear only undone propagations.
        prop_delivered_lits_.push_back(lit);
        prop_delivered_level_counts_.back()++;
        // Delivery budget: permanently disable Step 1 once exhausted.
        // prop_delivery_budget_ == 0 means unlimited; guard against that case
        // because static_cast<size_t>(0) == 0 and the comparison would fire
        // immediately on the very first delivery.
        if (prop_delivery_budget_ > 0 &&
                ++prop_total_delivered_ >= static_cast<size_t>(prop_delivery_budget_))
            prop_budget_exhausted_ = true;
        return lit;
    }
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
    // Skipped when propagation_enabled_ is false (ablation mode): conflict
    // detection (Step 2) still runs so the solver remains correct.
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
    if (propagation_enabled_ && !prop_budget_exhausted_ &&
            (++prop_call_count_ % prop_adaptive_interval_ == 0)) {
        // Assign-fraction guard: skip the O(|atoms|) scan when the search is
        // already deep.  Deep in the search, most equalities that are going to
        // be propagated have already been delivered; skipping saves overhead at
        // little cost in pruning power.
        //
        // The fraction is (currently assigned EUF vars) / (total EUF vars).
        // All SAT variables in this solver are registered through EufSolver
        // (via register_equality or new_var), so next_var_-1 is the correct
        // denominator and cur_total_assigned_ is the correct numerator.
        //
        // Semantics:
        //   0.0  → guard disabled; scan always runs (threshold can never be met
        //          because 0/N >= 0 would always be true, so we special-case 0).
        //   0.25 → skip when ≥25 % of vars are assigned (default).
        //   1.0  → skip only when every registered var is assigned.
        //
        // The guard is suppressed on tiny instances (< kPropMinVarsForThreshold)
        // where the fraction is noisy and the scan is cheap anyway.
        static constexpr size_t kPropMinVarsForThreshold = 20;
        const size_t total_vars = static_cast<size_t>(next_var_ - 1);
        const bool over_threshold = prop_assign_threshold_ > 0.0 &&
            total_vars >= kPropMinVarsForThreshold &&
            static_cast<double>(cur_total_assigned_) / total_vars >= prop_assign_threshold_;
        if (!over_threshold) {
        for (const auto& [lit, atom] : lit_to_atom_) {
                if (prop_enqueued_.contains(lit)) continue;     // already handled this pass
            bool already_assigned = cur_eq_assigned_.contains(lit);
            if (already_assigned && !record_proofs_) continue; // skip if assigned (non-proof mode)
            if (!cc_.are_congruent(atom.flat_lhs, atom.flat_rhs)) continue;

            std::vector<CC::RawCongStep> raw_congs;
            std::vector<EqId> expl = cc_.explain(atom.flat_lhs, atom.flat_rhs,
                                                  record_proofs_ ? &raw_congs : nullptr);
            std::vector<std::pair<NodeId,NodeId>> perm_deps;
            reason_clauses_[lit] = build_reason_clause(lit, expl,
                                                        record_proofs_ ? &perm_deps : nullptr);
            if (record_proofs_) record_cong_steps(raw_congs);
            if (record_proofs_) {
                const auto& rc = reason_clauses_[lit];
                // Already-assigned atoms are SAT-assigned directly from the problem
                // hypotheses.  bv_decide can recover them from the propositional
                // hypothesis axioms without a separate theory lemma.  Crucially, the
                // CC may have found the congruence path AFTER merging other classes
                // (including the atom's own SAT assignment), so the reason clause
                // might use the assignment as part of its own justification — making
                // it invalid as a standalone Lean theorem.  Always skip.
                if (already_assigned) {
                    // skip — bv_decide handles it from hypothesis axioms
                } else {
                    // Global content dedup: skip if already recorded by any path.
                    auto ckey = rc;
                    std::sort(ckey.begin(), ckey.end());
                    if (!proof_clause_content_seen_.insert(ckey).second) {
                        // exact duplicate — nothing to do
                    } else {
                        auto it2 = proof_recorded_prop_lits_.find(lit);
                        if (it2 == proof_recorded_prop_lits_.end()) {
                            // First occurrence: store it.
                            proof_recorded_prop_lits_[lit] = proof_conflicts_.size();
                            proof_conflicts_.push_back(rc);
                            proof_unit_perm_deps_.push_back(std::move(perm_deps));
                        } else if (rc.size() < proof_conflicts_[it2->second].size()) {
                            // Shorter clause after backtrack: replace.
                            proof_conflicts_[it2->second] = rc;
                            proof_unit_perm_deps_[it2->second] = std::move(perm_deps);
                        }
                    }
                }
            }
            prop_enqueued_.insert(lit);  // mark as handled (prevent duplicate recording)
            if (!already_assigned)
                prop_queue_.push_back(lit);
        }
        // Adaptive interval: double after every scan unconditionally.
        // Previously we only doubled on idle scans (no new propagations), but
        // that fails on instances like NEQ where the scan is always productive:
        // the interval never grows, we do O(|atoms|) work on every call, and
        // 16M+ theory propagations flood the SAT trail and wreck the search.
        // Doubling unconditionally caps total scan work to O(|atoms| × log N):
        // after ~10 doublings the interval saturates at kPropMaxInterval and
        // stays there.  Early scans still capture the propagations that matter
        // most (first few decisions); later the solver proceeds with minimal
        // theory-propagation interference.  Conflict detection (Step 2) is
        // unaffected and runs on every call regardless.
        } // end !over_threshold
        prop_adaptive_interval_ = std::min(prop_adaptive_interval_ * 2,
                                           kPropMaxInterval);
    } // end propagation_enabled_ block

    // Step 2: check for conflicts with active disequalities.
    // Skip if a conflict was already detected by notify_assignment (early
    // detection path): in that case has_conflict_ is true and build_conflict
    // has already been called, so we must not overwrite the conflict clause
    // with a duplicate or corrupt the conflict_lit_idx_ that CaDiCaL will
    // consume via cb_has_external_clause / cb_add_external_clause_lit.
    if (!has_conflict_) {
        for (const Disequality& d : active_diseqs_) {
            if (cc_.are_congruent(d.flat_lhs, d.flat_rhs)) {
                std::vector<CC::RawCongStep> raw_congs;
                std::vector<EqId> expl = cc_.explain(d.flat_lhs, d.flat_rhs,
                                                      record_proofs_ ? &raw_congs : nullptr);
                build_conflict(expl, d.orig_lit);
                if (record_proofs_) record_cong_steps(raw_congs);
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
