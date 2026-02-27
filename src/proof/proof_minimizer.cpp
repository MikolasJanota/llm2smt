#include "proof/proof_minimizer.h"

#include <algorithm>
#include <cadical.hpp>

namespace llm2smt {

std::vector<std::vector<int>> minimize_proof_conflicts(
    const std::vector<std::vector<int>>& original_clauses,
    const std::vector<std::vector<int>>& theory_conflicts)
{
    if (theory_conflicts.empty()) return {};

    // Find the highest variable appearing in either clause set.
    int max_var = 0;
    for (const auto& cl : original_clauses)
        for (int lit : cl) max_var = std::max(max_var, std::abs(lit));
    for (const auto& cl : theory_conflicts)
        for (int lit : cl) max_var = std::max(max_var, std::abs(lit));

    // Activation literals occupy variables max_var+1 .. max_var+n.
    const int base = max_var;
    const int n    = static_cast<int>(theory_conflicts.size());

    CaDiCaL::Solver solver;
    solver.resize(base + n);

    // Add original formula clauses unchanged.
    for (const auto& cl : original_clauses) {
        for (int lit : cl) solver.add(lit);
        solver.add(0);
    }

    // Add each theory conflict gated by its activation literal:
    //   -a_i ∨ l1 ∨ l2 ∨ ...
    // When a_i is assumed true the clause reduces to l1 ∨ l2 ∨ ...
    for (int i = 0; i < n; ++i) {
        int act = base + 1 + i;
        solver.add(-act);
        for (int lit : theory_conflicts[i]) solver.add(lit);
        solver.add(0);
    }

    // Assume all activation literals true.
    for (int i = 0; i < n; ++i)
        solver.assume(base + 1 + i);

    const int res = solver.solve();
    if (res != 20) {
        // Unexpected non-UNSAT — fall back to the full set.
        return theory_conflicts;
    }

    // Retain only conflicts whose activation literal is in the UNSAT core.
    std::vector<std::vector<int>> core;
    for (int i = 0; i < n; ++i) {
        if (solver.failed(base + 1 + i))
            core.push_back(theory_conflicts[i]);
    }
    return core;
}

} // namespace llm2smt
