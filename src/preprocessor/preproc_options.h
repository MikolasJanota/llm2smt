#pragma once

#include <string>

namespace llm2smt {

// Options that control formula preprocessing and SAT encoding.
struct PreprocOptions {
    int         passes     = 0;      // number of simplifier passes (0 = disabled)
    bool        flatten    = true;   // And-in-And / Or-in-Or flattening in the simplifier
    bool        nnf        = false;  // convert to Negation Normal Form before encoding
    bool        nnf_memo   = false;  // memoize NNF traversal (helps on DAG-heavy inputs)
    bool        selectors  = false;  // selector variable technique (requires nnf = true)
    std::string proof_file;          // empty = no proof output
    bool        proof_minimize = false; // remove unnecessary theory lemmas via UNSAT core
    bool        eq_bridge  = false;  // add common EUF consequences of disjunction branches
    bool        theory_propagation = true; // enable EUF theory propagation
    int         prop_interval = 32;        // run propagation scan every N cb_propagate calls, adaptive doubling up to 1024 (default 32)
    double      prop_assign_threshold = 0.25; // skip scan when (assigned/total) >= threshold; 0 = guard disabled
    int         prop_delivery_budget = 1000;  // permanently stop scan after this many propagations delivered (0 = unlimited)
};

} // namespace llm2smt
