#pragma once

#include <vector>

namespace llm2smt {

// Given the original formula clauses (recorded during SAT encoding) and a set
// of theory conflict clauses, return the subset of theory conflicts that form
// an UNSAT core together with the original clauses.
//
// Uses a fresh CaDiCaL instance with assumption-based core extraction:
// each theory clause is gated by a fresh activation literal; after solving
// with all activations assumed, only the clauses whose activation literals
// appear in the failed-assumption set are retained.
//
// Falls back to the full set when the minimization solve is unexpectedly SAT.
std::vector<std::vector<int>> minimize_proof_conflicts(
    const std::vector<std::vector<int>>& original_clauses,
    const std::vector<std::vector<int>>& theory_conflicts);

} // namespace llm2smt
