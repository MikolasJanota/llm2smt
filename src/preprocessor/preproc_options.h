#pragma once

#include <string>

namespace llm2smt {

// Options that control formula preprocessing and SAT encoding.
struct PreprocOptions {
    int         passes     = 0;      // number of simplifier passes (0 = disabled)
    bool        flatten    = true;   // And-in-And / Or-in-Or flattening in the simplifier
    bool        nnf        = false;  // convert to Negation Normal Form before encoding
    bool        selectors  = false;  // selector variable technique (requires nnf = true)
    std::string proof_file;          // empty = no proof output
    bool        proof_minimize = false; // remove unnecessary theory lemmas via UNSAT core
    bool        eq_bridge  = false;  // add common EUF consequences of disjunction branches
    bool        theory_propagation = true; // enable EUF theory propagation
};

} // namespace llm2smt
