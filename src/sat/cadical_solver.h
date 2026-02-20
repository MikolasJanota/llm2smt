#pragma once

#include "sat/ipasir_up.h"

#include <memory>

// Forward-declare CaDiCaL types so we don't pull cadical.hpp into every
// translation unit that includes this header.
namespace CaDiCaL { class Solver; }

namespace llm2smt {

// SatSolver implementation backed by CaDiCaL with IPASIR-UP propagation.
//
// Design: our ExternalPropagator interface (ipasir_up.h) uses single-literal
// notifications  notify_assignment(int lit, bool is_fixed)  while CaDiCaL 3.x
// batches them into  notify_assignment(const std::vector<int>& lits).
// An internal Adapter class bridges the two, so nothing above this layer
// needs to know about CaDiCaL internals.
class CaDiCaLSolver : public SatSolver {
public:
    CaDiCaLSolver();
    ~CaDiCaLSolver() override;

    // SatSolver interface
    int         new_var() override;
    void        add_clause(std::span<const int> lits) override;
    void        connect_propagator(ExternalPropagator& prop) override;
    SolveResult solve() override;

private:
    struct Adapter;  // defined in cadical_solver.cpp

    std::unique_ptr<CaDiCaL::Solver> solver_;
    std::unique_ptr<Adapter>         adapter_;

    int next_var_      = 0;   // highest variable allocated via new_var()
    int max_clause_var_ = 0;  // highest |lit| seen in add_clause()
    int last_observed_ = 0;   // highest variable registered with add_observed_var()
};

} // namespace llm2smt
