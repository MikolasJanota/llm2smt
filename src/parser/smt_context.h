#pragma once

#include <string>
#include <unordered_map>
#include <vector>

#include "core/node.h"
#include "core/node_manager.h"
#include "theories/euf/euf_solver.h"
#include "sat/ipasir_up.h"

namespace llm2smt {

// Holds the global state for one SMT-LIB2 parse session.
struct SmtContext {
    NodeManager& nm;
    EufSolver&   euf;
    SatSolver&   sat;

    // Sort declarations (QF_EUF has only user-declared uninterpreted sorts)
    std::unordered_map<std::string, uint32_t> declared_sorts;  // name → arity

    // Function/constant declarations
    // name → NodeId (0-arity) or SymbolId (for functions to be applied later)
    std::unordered_map<std::string, SymbolId>  declared_fns;

    // Accumulated assertions (SAT literals)
    std::vector<int> assertions;

    // Logic
    std::string logic;

    SmtContext(NodeManager& nm_, EufSolver& euf_, SatSolver& sat_)
        : nm(nm_), euf(euf_), sat(sat_) {}
};

} // namespace llm2smt
