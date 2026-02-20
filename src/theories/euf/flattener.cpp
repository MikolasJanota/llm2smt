#include "theories/euf/flattener.h"

#include <cassert>
#include <string>

namespace llm2smt {

Flattener::Flattener(NodeManager& nm, CC& cc)
    : nm_(nm), cc_(cc) {}

NodeId Flattener::fresh_const() {
    std::string name = "__flat_" + std::to_string(fresh_counter_++);
    SymbolId sym = nm_.declare_symbol(name, 0);
    NodeId n = nm_.mk_const(sym);
    cc_.add_node(n);
    return n;
}

NodeId Flattener::do_flatten(NodeId term, std::vector<FlatEq>& eqs) {
    // Check cache
    auto it = node_to_cc_.find(term);
    if (it != node_to_cc_.end()) return it->second;

    const NodeData& data = nm_.get(term);

    if (data.children.empty()) {
        // Constant: register directly in CC
        cc_.add_node(term);
        node_to_cc_[term] = term;
        return term;
    }

    // n-ary application: curry to binary via left-nesting with "@" apply symbol.
    // g(t1, t2, ..., tn) becomes (@((@(g_flat, t1_flat)), t2_flat), ..., tn_flat)
    // First, get flat CC constant for the function symbol itself (as a 0-arity node)
    SymbolId fn_sym = data.sym;
    NodeId fn_const;
    {
        // Create a 0-arity node for the function symbol if not already present
        NodeId sym_node = nm_.mk_const(fn_sym);
        fn_const = do_flatten(sym_node, eqs);
    }

    // Now iteratively curry: start with fn_const, apply each argument
    NodeId cur = fn_const;
    SymbolId at = nm_.apply_symbol();

    for (NodeId child : data.children) {
        NodeId arg_flat = do_flatten(child, eqs);

        // The application node @(cur, arg_flat) needs a fresh constant to represent it
        // unless it already exists in the node manager
        std::vector<NodeId> app_children = {cur, arg_flat};
        NodeId app_node = nm_.mk_app(at, std::span<const NodeId>(app_children));

        NodeId app_const;
        auto it2 = node_to_cc_.find(app_node);
        if (it2 != node_to_cc_.end()) {
            app_const = it2->second;
        } else {
            app_const = fresh_const();
            node_to_cc_[app_node] = app_const;
            FlatEq feq{app_const, cur, arg_flat};
            eqs.push_back(feq);
        }
        cur = app_const;
    }

    node_to_cc_[term] = cur;
    return cur;
}

FlatResult Flattener::flatten(NodeId term) {
    FlatResult result;
    result.equations.clear();
    result.flat_node = do_flatten(term, result.equations);
    return result;
}

NodeId Flattener::flatten_and_register(NodeId term) {
    FlatResult fr = flatten(term);
    for (const FlatEq& eq : fr.equations) {
        cc_.add_app_equation(eq.result, eq.fn, eq.arg);
    }
    return fr.flat_node;
}


} // namespace llm2smt
