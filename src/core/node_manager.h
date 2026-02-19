#pragma once

#include <cstdint>
#include <span>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "core/node.h"
#include "core/symbol_table.h"

namespace llm2smt {

class NodeManager {
public:
    NodeManager();

    // Declare a function/constant symbol and return its id.
    // Idempotent if same arity is used.
    SymbolId declare_symbol(std::string_view name, uint32_t arity);

    // Look up a symbol by name (returns NULL_SYMBOL if not found).
    SymbolId lookup_symbol(std::string_view name) const;

    // Create a constant node (0-arity application).
    NodeId mk_const(SymbolId sym);

    // Create an application node. Looks up hash table; inserts if new.
    NodeId mk_app(SymbolId sym, std::span<const NodeId> children);

    // Convenience: mk_app with no children (same as mk_const).
    NodeId mk_app(SymbolId sym) { return mk_const(sym); }

    // Get the data for a node.
    const NodeData& get(NodeId id) const { return nodes_.at(id); }

    // Check if a node is a constant (no children).
    bool is_const(NodeId id) const { return nodes_.at(id).children.empty(); }

    // Number of registered nodes (including sentinel 0).
    std::size_t num_nodes() const { return nodes_.size(); }

    // The special "apply" symbol used by the flattener for currying.
    SymbolId apply_symbol() const { return apply_sym_; }

    SymbolTable& symbol_table() { return symtab_; }
    const SymbolTable& symbol_table() const { return symtab_; }

private:
    SymbolTable symtab_;
    // nodes_[0] is a sentinel/null node
    std::vector<NodeData>                                    nodes_;
    std::unordered_map<NodeData, NodeId, NodeDataHash>       table_;

    SymbolId apply_sym_;  // The "@" apply symbol for currying
};

} // namespace llm2smt
