#include "theories/euf/euf_solver.h"

#include <cassert>
#include <stdexcept>

namespace llm2smt {

EufSolver::EufSolver(NodeManager& nm)
    : nm_(nm), cc_(), flattener_(nm, cc_) {
    diseq_level_counts_.push_back(0);
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

// ============================================================================
// ExternalPropagator callbacks
// ============================================================================

void EufSolver::notify_assignment(int lit, bool /*is_fixed*/) {
    int var = (lit > 0) ? lit : -lit;
    auto it = lit_to_atom_.find(var);
    if (it == lit_to_atom_.end()) return;

    const EqAtom& atom = it->second;

    if (lit > 0) {
        // Equality asserted: a = b
        cc_.add_equation(atom.flat_lhs, atom.flat_rhs);
    } else {
        // Disequality asserted: a ≠ b
        active_diseqs_.push_back(Disequality{atom.flat_lhs, atom.flat_rhs, lit});
        diseq_level_counts_.back()++;
    }
}

void EufSolver::notify_new_decision_level() {
    cc_.push_level();
    current_level_++;
    diseq_level_counts_.push_back(0);
}

void EufSolver::notify_backtrack(size_t new_level) {
    cc_.pop_level(new_level);
    current_level_ = new_level;

    // Pop active disequalities introduced after new_level
    while (diseq_level_counts_.size() > new_level + 1) {
        size_t count = diseq_level_counts_.back();
        diseq_level_counts_.pop_back();
        for (size_t i = 0; i < count; ++i) {
            active_diseqs_.pop_back();
        }
    }

    has_conflict_    = false;
    conflict_clause_.clear();
    conflict_lit_idx_ = 0;
}

bool EufSolver::cb_check_found_model(const std::vector<int>& /*model*/) {
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
        auto it = flat_atom_to_lit_.find(key);
        assert(it != flat_atom_to_lit_.end() && "equation in explanation has no SAT literal");
        conflict_clause_.push_back(-(it->second));  // negate positive literal
    }
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

} // namespace llm2smt
