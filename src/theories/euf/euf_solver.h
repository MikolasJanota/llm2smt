#pragma once

#include <unordered_map>
#include <utility>
#include <vector>

#include "core/node.h"
#include "core/node_manager.h"
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
    explicit EufSolver(NodeManager& nm);

    // Register an equality atom lhs=rhs.
    // Returns a positive SAT variable (literal). Idempotent.
    int register_equality(NodeId lhs, NodeId rhs);

    // ── ExternalPropagator callbacks ─────────────────────────────────────

    void notify_assignment(int lit, bool is_fixed) override;
    void notify_new_decision_level() override;
    void notify_backtrack(size_t new_level) override;

    bool cb_check_found_model(const std::vector<int>& model) override;

    bool cb_has_external_clause(bool& is_forgettable) override;
    int  cb_add_external_clause_lit() override;

    // Allocate a fresh SAT variable (for Bool-valued atoms outside EUF).
    int new_var() { return next_var_++; }

    // Access internals (for testing)
    CC&          cc()          { return cc_; }
    NodeManager& nm()          { return nm_; }
    Flattener&   flattener()   { return flattener_; }

private:
    NodeManager& nm_;
    CC           cc_;
    Flattener    flattener_;

    // SAT literal ↔ equality atom mapping
    std::unordered_map<int, EqAtom>            lit_to_atom_;
    // Reverse: atom → literal (keyed by ordered pair min(lhs,rhs), max(lhs,rhs))
    std::unordered_map<uint64_t, int>          atom_to_lit_;

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

    // Make a 64-bit key for an unordered pair of NodeIds
    static uint64_t atom_key(NodeId a, NodeId b) {
        if (a > b) std::swap(a, b);
        return (static_cast<uint64_t>(a) << 32) | static_cast<uint64_t>(b);
    }

    // Build conflict clause from an explanation
    void build_conflict(const std::vector<EqId>& explanation, int diseq_lit);
};

} // namespace llm2smt
