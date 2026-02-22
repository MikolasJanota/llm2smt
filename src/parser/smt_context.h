#pragma once

#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "core/node.h"
#include "core/node_manager.h"
#include "theories/euf/euf_solver.h"
#include "sat/ipasir_up.h"

namespace llm2smt {

// Information about a user-declared function, for get-model output.
struct FnDecl {
    SymbolId                 sym;
    std::string              return_sort;
    std::vector<std::string> param_sorts;
};

// Holds the global state for one SMT-LIB2 parse session.
struct SmtContext {
    NodeManager& nm;
    EufSolver&   euf;
    SatSolver&   sat;

    std::unordered_map<std::string, uint32_t> declared_sorts;
    std::unordered_map<std::string, SymbolId>  declared_fns;
    // Symbols whose return sort is Bool (predicates, propositional constants)
    std::unordered_set<SymbolId>               bool_fns;
    // Bool-valued node → SAT literal (for predicate applications)
    std::unordered_map<NodeId, int>            node_to_lit;
    // User-declared functions in declaration order (for deterministic get-model output)
    std::vector<FnDecl>                        declared_fn_order;

    std::vector<int> assertions;
    std::string      logic;

    SmtContext(NodeManager& nm_, EufSolver& euf_, SatSolver& sat_)
        : nm(nm_), euf(euf_), sat(sat_) {}

    // Return (allocating if necessary) the SAT literal for a Bool-valued node.
    int lit_for_node(NodeId n) {
        auto it = node_to_lit.find(n);
        if (it != node_to_lit.end()) return it->second;
        int lit = euf.new_var();
        node_to_lit[n] = lit;
        return lit;
    }
};

} // namespace llm2smt
