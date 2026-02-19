#pragma once

#include <cstddef>
#include <span>
#include <vector>

namespace llm2smt {

enum class SolveResult { SAT, UNSAT, UNKNOWN };

// Abstract external propagator interface matching CaDiCaL 2.x / IPASIR-UP spec.
class ExternalPropagator {
public:
    virtual ~ExternalPropagator() = default;

    // Called when the SAT solver assigns a literal (or makes it fixed/unit).
    virtual void notify_assignment(int lit, bool is_fixed) {}

    // Called when the SAT solver opens a new decision level.
    virtual void notify_new_decision_level() {}

    // Called when the SAT solver backtracks to new_level.
    virtual void notify_backtrack(size_t new_level) {}

    // Called when the SAT solver has found a complete model.
    // Return true to accept, false to add an external clause.
    virtual bool cb_check_found_model(const std::vector<int>& model) { return true; }

    // Called to let the propagator decide the next branching literal.
    // Return 0 to let the SAT solver decide.
    virtual int cb_decide() { return 0; }

    // Called to ask the propagator for an implied literal.
    // Return 0 if none.
    virtual int cb_propagate() { return 0; }

    // Called to get the reason clause for a propagated literal.
    // Return 0 to indicate end of clause.
    virtual int cb_add_reason_clause_lit(int propagated_lit) { return 0; }

    // Called to check whether the propagator has an external clause to add.
    // Set is_forgettable to indicate whether the clause can be deleted.
    virtual bool cb_has_external_clause(bool& is_forgettable) { return false; }

    // Called to iterate the literals of the current external clause.
    // Return 0 to indicate end of clause.
    virtual int cb_add_external_clause_lit() { return 0; }
};

// Abstract SAT solver interface.
class SatSolver {
public:
    virtual ~SatSolver() = default;

    // Allocate and return a new variable (positive literal).
    virtual int new_var() = 0;

    // Add a clause.
    virtual void add_clause(std::span<const int> lits) = 0;

    // Register an external propagator.
    virtual void connect_propagator(ExternalPropagator& prop) = 0;

    // Run the solver.
    virtual SolveResult solve() = 0;
};

} // namespace llm2smt
