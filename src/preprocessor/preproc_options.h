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
    bool        lra_bool_cache_and = true; // reuse repeated QF_LRA Boolean and compounds
    bool        lra_bool_cache_or = true;  // reuse repeated QF_LRA Boolean or compounds
    bool        lra_bool_cache_eq = true;  // reuse repeated QF_LRA Boolean equality/distinct compounds
    bool        lra_term_cache = true; // reuse normalized QF_LRA arithmetic terms
    bool        lra_eq_elim = true; // eliminate variables using unconditional top-level QF_LRA equalities
    size_t      lra_eq_elim_limit = 10000; // maximum top-level equality rows processed by QF_LRA elimination
    bool        lra_const_simplify = true; // fold constant QF_LRA Boolean/arithmetic subexpressions before encoding
    bool        lra_ite_eq_direct = true; // encode (= t (ite c a b)) as a Boolean ITE over equality literals
    bool        lra_finite_domain_bounds = true; // link QF_LRA finite-domain choices to simple bound atoms
    bool        lra_finite_domain_eq_defs = true; // propagate QF_LRA variable equalities through finite-domain choices
    bool        lra_finite_domain_branch = false; // experimental: prefer selected QF_LRA finite-domain choice literals as SAT decisions
    bool        lra_direct_eq_atoms = false; // experimental: assert positive top-level QF_LRA equalities as direct LRA Eq atoms
    bool        lra_incremental_prop_scan = true; // scan only LRA vars whose bounds changed during propagation discovery
    bool        lra_row_bound_prop = true; // propagate elementary atoms implied by tableau row bounds
    bool        lra_row_bound_dirty_scan = true; // restrict row-bound propagation to rows touching dirty bounds
    bool        lra_row_bound_indexed_dirty_scan = false; // experimental: use a reverse row index for dirty row-bound propagation scans
    size_t      lra_row_bound_prop_budget = 0; // max row-bound atom candidates per discovery; 0 means unlimited
    bool        lra_tableau_row_index = false; // experimental: use reverse row index for simplex update/pivot scans
    bool        lra_simple_graph_prop = false; // experimental: propagate from unary/DL/UTVPI graph constraints
    size_t      lra_simple_graph_budget = 20000; // max simple-graph atom candidates per discovery; 0 means unlimited
    bool        lra_dl_fast_path = true; // prove pure top-level unary/DL/UTVPI contradictions before SAT/LRA encoding
};

} // namespace llm2smt
