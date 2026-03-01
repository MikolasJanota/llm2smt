#pragma once

#include <vector>
#include "preprocessor/fml.h"

namespace llm2smt {

// Equality bridging under disjunctions.
//
// For every Or(...) subformula in the input, compute the EUF-closure of
// equalities in each branch and extract the equalities common to ALL
// branches.  These common consequences are added as new unit Eq formulas
// to the formula list.
//
// Example: (x=y ∧ y=z) ∨ (x=w ∧ w=z)
//   branch 1 closure: {x,y,z}   branch 2 closure: {x,w,z}
//   shared nodes: {x,z}         common pair x~z in both → add Eq(x,z)
//
// This eliminates the exponential blowup that arises in lazy SMT when
// solving "diamond" instances:
//   (xi=yi ∧ yi=x_{i+1}) ∨ (xi=zi ∧ zi=x_{i+1})   for i=0..n-1
//   ¬(x0=xn)
// Without bridging the SAT solver explores 2^n branch combinations;
// with bridging each disjunction immediately yields xi=x_{i+1}, the EUF
// derives x0=xn by transitivity, and the contradiction is found in O(n).
//
// The pass is sound (only adds logical consequences) and runs in time
// O(sum over Or-nodes of branches×equalities×shared_vars²).
void bridge_disjunctions(std::vector<FmlRef>& fmls);

} // namespace llm2smt
