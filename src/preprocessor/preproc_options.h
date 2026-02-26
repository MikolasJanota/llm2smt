#pragma once

namespace llm2smt {

// Options that control formula preprocessing and SAT encoding.
struct PreprocOptions {
    int  passes    = 0;      // number of simplifier passes (0 = disabled)
    bool flatten   = true;   // And-in-And / Or-in-Or flattening in the simplifier
    bool selectors = false;  // selector variable technique for Or-with-compound-disjuncts
};

} // namespace llm2smt
