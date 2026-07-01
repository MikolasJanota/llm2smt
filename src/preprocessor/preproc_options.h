#pragma once

#include <string>

namespace llm2smt {

// Options that control formula preprocessing and SAT encoding.
struct PreprocOptions {
    int         passes     = 0;      // number of simplifier passes (0 = disabled)
    bool        flatten    = true;   // And-in-And / Or-in-Or flattening in the simplifier
    bool        nary       = true;   // use n-ary AND/OR nodes (false = left-nested binary)
    bool        nnf        = false;  // convert to Negation Normal Form before encoding
    bool        nnf_memo   = false;  // memoize NNF traversal (helps on DAG-heavy inputs)
    std::string proof_file;          // empty = no proof output
    bool        proof_minimize = false; // remove unnecessary theory lemmas via UNSAT core
    bool        eq_bridge  = false;  // add common EUF consequences of disjunction branches
    bool        finite_domain_amo = true; // add SAT AMO clauses from top-level distinct endpoints
    bool        finite_domain_eq_defs = true; // define equalities between finite-domain terms via their value choices
    bool        theory_propagation = true; // enable EUF theory propagation
    int         prop_interval = 32;        // process propagation candidates every N discovery calls, adaptive doubling up to 1024 (default 32)
    double      prop_assign_threshold = 0.25; // skip candidate processing when (assigned/total) >= threshold; 0 = guard disabled
    int         prop_delivery_budget = 1000;  // permanently stop discovery after this many propagations delivered (0 = unlimited)
    bool        lra_print_conflict_size = false; // debug: print final minimized LRA conflict size
    bool        lra_bool_cache = true; // reuse SAT literals for repeated QF_LRA Boolean compounds
};

} // namespace llm2smt
