#include "sat/cadical_solver.h"

#include <algorithm>
#include <cadical.hpp>

namespace llm2smt {

// ============================================================================
// Adapter: bridges CaDiCaL 3.x ExternalPropagator → our ExternalPropagator
//
// The only non-trivial translation is notify_assignment: CaDiCaL batches a
// vector of literals, while our interface uses one call per literal.
// The is_fixed parameter (level-0 propagation) is not tracked by CaDiCaL's
// batch interface, so we pass false; callers that care should connect a
// FixedAssignmentListener separately.
// ============================================================================

// Fully qualify our interface to avoid shadowing by CaDiCaL::ExternalPropagator.
using OurPropagator = llm2smt::ExternalPropagator;

struct CaDiCaLSolver::Adapter : public CaDiCaL::ExternalPropagator {
    explicit Adapter(OurPropagator& p) : prop_(p) {}

    // CaDiCaL 3.x batches assignment notifications; we fan them out one-by-one.
    void notify_assignment(const std::vector<int>& lits) override {
        for (int lit : lits)
            prop_.notify_assignment(lit, /*is_fixed=*/false);
    }

    void notify_new_decision_level() override { prop_.notify_new_decision_level(); }
    void notify_backtrack(size_t new_level)   override { prop_.notify_backtrack(new_level); }

    bool cb_check_found_model(const std::vector<int>& model) override {
        return prop_.cb_check_found_model(model);
    }

    int  cb_decide() override                       { return prop_.cb_decide(); }
    int  cb_propagate() override                    { return prop_.cb_propagate(); }
    int  cb_add_reason_clause_lit(int lit) override { return prop_.cb_add_reason_clause_lit(lit); }

    bool cb_has_external_clause(bool& is_forgettable) override {
        return prop_.cb_has_external_clause(is_forgettable);
    }
    int cb_add_external_clause_lit() override { return prop_.cb_add_external_clause_lit(); }

private:
    OurPropagator& prop_;
};

// ============================================================================
// CaDiCaLSolver
// ============================================================================

CaDiCaLSolver::CaDiCaLSolver()
    : solver_(std::make_unique<CaDiCaL::Solver>()) {}

CaDiCaLSolver::~CaDiCaLSolver() {
    if (adapter_)
        solver_->disconnect_external_propagator();
}

int CaDiCaLSolver::new_var() {
    return ++next_var_;
}

void CaDiCaLSolver::add_clause(std::span<const int> lits) {
    // CaDiCaL 3.x requires variables to be declared before use.
    // Compute max var in this clause and call resize() once before add().
    int max_var = 0;
    for (int lit : lits) max_var = std::max(max_var, std::abs(lit));
    if (max_var > max_clause_var_) {
        max_clause_var_ = max_var;
        solver_->resize(max_clause_var_);
    }
    for (int lit : lits) solver_->add(lit);
    solver_->add(0);  // terminate clause
}

void CaDiCaLSolver::connect_propagator(ExternalPropagator& prop) {
    adapter_ = std::make_unique<Adapter>(prop);
    solver_->connect_external_propagator(adapter_.get());
}

SolveResult CaDiCaLSolver::solve() {
    // Register every known variable as observed so the propagator receives
    // assignment notifications.  We do this incrementally to avoid redundant
    // calls on subsequent solves.
    if (adapter_) {
        int max_var = std::max(next_var_, max_clause_var_);
        for (int v = last_observed_ + 1; v <= max_var; ++v)
            solver_->add_observed_var(v);
        last_observed_ = max_var;
    }

    int result = solver_->solve();
    if (result == 10) return SolveResult::SAT;
    if (result == 20) return SolveResult::UNSAT;
    return SolveResult::UNKNOWN;
}

int CaDiCaLSolver::val(int lit) const {
    return solver_->val(lit);
}

} // namespace llm2smt
