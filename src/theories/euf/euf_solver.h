#pragma once

#include <set>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "core/node.h"
#include "core/node_manager.h"
#include "core/stats.h"
#include "sat/ipasir_up.h"
#include "theories/euf/cc.h"
#include "theories/euf/flattener.h"

namespace llm2smt {

// An equality atom: literal `var` represents the assertion `lhs = rhs`.
// Positive literal → lhs == rhs; negative literal → lhs != rhs.
// flat_lhs / flat_rhs are the CC-flat nodes pre-computed at registration time.
struct EqAtom {
    NodeId lhs;
    NodeId rhs;
    NodeId flat_lhs;
    NodeId flat_rhs;
};

class EufSolver : public ExternalPropagator {
public:
    explicit EufSolver(NodeManager& nm, Stats& stats);

    // Register an equality atom lhs=rhs.
    // Returns a positive SAT variable (literal). Idempotent.
    int register_equality(NodeId lhs, NodeId rhs);

    // Register a permanently-true equality: merge lhs and rhs in the CC
    // directly (at level 0) without creating any SAT variable.
    // Called for equalities that were forced true by the preprocessor;
    // they never need to be decided by the SAT solver.
    void register_permanent_equality(NodeId lhs, NodeId rhs);

    // ── ExternalPropagator callbacks ─────────────────────────────────────

    void notify_assignment(int lit, bool is_fixed) override;
    void notify_new_decision_level() override;
    void notify_backtrack(size_t new_level) override;

    bool cb_check_found_model(const std::vector<int>& model) override;

    bool cb_has_external_clause(bool& is_forgettable) override;
    int  cb_add_external_clause_lit() override;
    int  cb_propagate() override;
    int  cb_add_reason_clause_lit(int propagated_lit) override;

    // Allocate a fresh SAT variable (for Bool-valued atoms outside EUF).
    int new_var() { return next_var_++; }

    // Enable/disable theory propagation (for ablation studies).
    // Conflict detection is always active regardless of this setting.
    void set_propagation(bool v) { propagation_enabled_ = v; }

    // Run the propagation scan every N discover_propagations() calls.
    // 1 = every call (default); N > 1 reduces overhead on SAT instances.
    void set_prop_interval(int n) { prop_interval_ = n; }

    // Access internals (for testing)
    CC&          cc()          { return cc_; }
    NodeManager& nm()          { return nm_; }
    Flattener&   flattener()   { return flattener_; }

    // ── Proof recording ───────────────────────────────────────────────────
    void enable_proof_recording() { record_proofs_ = true; }

    const std::vector<std::vector<int>>& proof_conflicts() const {
        return proof_conflicts_;
    }

    const std::unordered_map<int, EqAtom>& lit_to_atom() const {
        return lit_to_atom_;
    }

    // Original-node pairs permanently merged by preprocessing (no SAT variable).
    // Used by the Lean emitter to generate transitivity bridge lemmas.
    // The NodeIds are the pre-flattening originals so node_to_lean can render them.
    const std::vector<std::pair<NodeId, NodeId>>& permanent_equalities() const {
        return permanent_eq_pairs_;
    }

    // For each entry in proof_conflicts(), the permanent equalities (original
    // NodeId pairs) that were in the EUF explanation but skipped because they
    // are permanent.  Non-empty only for unit conflict clauses.
    const std::vector<std::vector<std::pair<NodeId,NodeId>>>& proof_unit_perm_deps() const {
        return proof_unit_perm_deps_;
    }

    // A fully-resolved congruence step:
    //   decide(orig(result_lhs) = orig(result_rhs))  is implied by  ∧ premise_lits
    // where premise_lits are positive SAT literal ids for the leaf atoms.
    // The Lean emitter renders this as:
    //   theorem cong_N : decide(r1=r2) ∨ ¬P1 ∨ ¬P2 ∨ ... := by grind
    struct CongStep {
        NodeId result_lhs;
        NodeId result_rhs;
        std::vector<int> premise_lits;  // positive SAT literals
    };

    const std::vector<CongStep>& proof_cong_steps() const {
        return proof_cong_steps_;
    }

private:
    NodeManager& nm_;
    CC           cc_;
    Flattener    flattener_;

    // SAT literal ↔ equality atom mapping
    std::unordered_map<int, EqAtom>            lit_to_atom_;
    // Reverse: atom → literal (keyed by ordered pair min(lhs,rhs), max(lhs,rhs))
    std::unordered_map<uint64_t, int>          atom_to_lit_;
    // Same as atom_to_lit_ but keyed by the FLAT node ids (as stored in CC equations).
    // Used in build_conflict where the CC returns flat-node equation records.
    std::unordered_map<uint64_t, int>          flat_atom_to_lit_;
    // Flat-node pairs for equalities that were permanently merged in the CC
    // without a SAT variable (registered via register_permanent_equality).
    std::unordered_set<uint64_t>               permanent_flat_eqs_;
    // Same pairs kept as (original_lhs, original_rhs) for proof emission
    // (original = pre-flattening NodeIds, so node_to_lean can render them).
    std::vector<std::pair<NodeId, NodeId>>     permanent_eq_pairs_;
    // Reverse map: flat-key → original NodeId pair for permanent equalities.
    // Used by build_conflict to record perm deps for unit clause proof emission.
    std::unordered_map<uint64_t, std::pair<NodeId,NodeId>> permanent_flat_to_orig_;

    // Next SAT variable to allocate (external to a real SAT solver, so we manage here)
    int next_var_ = 1;

    // Active disequalities (negative literals assigned)
    // Each entry: (flat_lhs, flat_rhs, orig_lit)
    struct Disequality {
        NodeId flat_lhs;
        NodeId flat_rhs;
        int    orig_lit;   // the negative literal that caused this
    };
    std::vector<Disequality> active_diseqs_;

    // Conflict clause being served via cb_add_external_clause_lit
    std::vector<int> conflict_clause_;
    size_t           conflict_lit_idx_ = 0;
    bool             has_conflict_     = false;

    // Current decision level
    size_t current_level_ = 0;
    // Per-level counts of active diseqs (for backtracking)
    std::vector<size_t> diseq_level_counts_;

    // Proof recording
    bool                          record_proofs_   = false;
    std::vector<std::vector<int>> proof_conflicts_;
    // Parallel to proof_conflicts_: permanent eq deps for unit clauses (else empty).
    std::vector<std::vector<std::pair<NodeId,NodeId>>> proof_unit_perm_deps_;
    // Deduplication: maps literal → index into proof_conflicts_ where the
    // clause for that literal was stored.  When a shorter clause arrives for
    // the same literal (after CDCL backtrack + re-derivation), the stored
    // clause is replaced so bv_decide always gets the strongest version.
    std::unordered_map<int, size_t>  proof_recorded_prop_lits_;
    std::unordered_map<int, size_t>  proof_recorded_conflict_diseqs_;
    // Cross-category dedup: prevents recording the exact same set of literals
    // twice (e.g., a propagation reason and a conflict clause that happen to be
    // identical).  Keyed by sorted literal vector for canonical comparison.
    std::set<std::vector<int>>       proof_clause_content_seen_;

    // Congruence steps collected during conflict / propagation proof recording.
    std::vector<CongStep>    proof_cong_steps_;
    // Dedup guard for cong steps: keyed by atom_key(result_lhs, result_rhs).
    std::unordered_set<uint64_t> proof_cong_seen_;

    Stats& stats_;

    // ── Theory propagation ────────────────────────────────────────────────
    // Queue of theory-implied literals awaiting delivery to the SAT solver.
    std::vector<int>        prop_queue_;
    size_t                  prop_queue_head_ = 0;
    std::unordered_set<int> prop_enqueued_;   // guard against duplicates

    // Reason clauses: propagated_lit → [plit, -e1, -e2, …]
    std::unordered_map<int, std::vector<int>> reason_clauses_;
    int    reason_serving_lit_ = 0;
    size_t reason_serving_idx_ = 0;

    // Per-level tracking of positive equality assignments (mirrors diseq tracking).
    // Used so discover_propagations can skip lits already in CaDiCaL's trail.
    std::vector<int>         active_eq_lits_;
    std::vector<size_t>      eq_lit_level_counts_;
    std::unordered_set<int>  cur_eq_assigned_;

    // Set whenever the CC state changes (new equality merged or after backtrack).
    // Consumed (and cleared) by cb_propagate.  Defers the O(|atoms|) scan out of
    // notify_assignment (called per assignment) into cb_propagate (called once
    // after a full BCP batch), avoiding O(K × N) quadratic work.
    bool needs_rescan_ = false;

    // Theory propagation control.
    // propagation_enabled_: when false, the equality-implication scan is
    //   skipped entirely (ablation mode); conflict detection is unaffected.
    // prop_interval_: run the scan every N calls (1 = every call, default).
    // prop_call_count_: call counter used to implement the interval.
    bool propagation_enabled_ = true;
    int  prop_interval_       = 1;
    int  prop_call_count_     = 0;

    // Make a 64-bit key for an unordered pair of NodeIds
    static uint64_t atom_key(NodeId a, NodeId b) {
        if (a > b) std::swap(a, b);
        return (static_cast<uint64_t>(a) << 32) | static_cast<uint64_t>(b);
    }

    // Build conflict clause from an explanation
    void build_conflict(const std::vector<EqId>& explanation, int diseq_lit);

    // Scan all registered equality atoms for theory-implied literals and
    // enqueue them.  Already-assigned literals are excluded via cur_eq_assigned_.
    void discover_propagations();

    // Build the reason clause [plit, -e1_lit, -e2_lit, …] for a propagated
    // equality literal.  Permanent equalities (no SAT var) are dropped.
    std::vector<int> build_reason_clause(int plit, const std::vector<EqId>& expl,
                                          std::vector<std::pair<NodeId,NodeId>>* out_perm_deps = nullptr);

    // Resolve a vector of EqIds (from cc_.explain) to SAT literal ids,
    // skipping permanent equalities.  Returns sorted, deduplicated literals.
    std::vector<int> eqids_to_lits(const std::vector<EqId>& eqids) const;

    // Process raw congruence steps (from cc_.explain with out_cong) into
    // fully-resolved CongStep records and append to proof_cong_steps_.
    void record_cong_steps(const std::vector<CC::RawCongStep>& raw_congs);
};

} // namespace llm2smt
