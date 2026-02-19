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

    int var = next_var_++;
    lit_to_atom_[var]  = EqAtom{lhs, rhs};
    lit_to_atom_[-var] = EqAtom{lhs, rhs};
    atom_to_lit_[key]  = var;
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
        NodeId flat_lhs = flattener_.flatten_and_register(atom.lhs);
        NodeId flat_rhs = flattener_.flatten_and_register(atom.rhs);
        cc_.add_equation(flat_lhs, flat_rhs);
    } else {
        // Disequality asserted: a ≠ b
        NodeId flat_lhs = flattener_.flatten_and_register(atom.lhs);
        NodeId flat_rhs = flattener_.flatten_and_register(atom.rhs);
        active_diseqs_.push_back(Disequality{flat_lhs, flat_rhs, lit});
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
            // Conflict: a≠b but CC says a≡b
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
        // Find the SAT literal for this equation
        uint64_t key = atom_key(e.lhs, e.rhs != NULL_NODE ? e.rhs : e.lhs);
        auto it = atom_to_lit_.find(key);
        if (it != atom_to_lit_.end()) {
            conflict_clause_.push_back(-(it->second));  // negate positive literal
        }
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
