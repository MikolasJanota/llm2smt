#include "core/node_manager.h"

#include <stdexcept>

namespace llm2smt {

NodeManager::NodeManager() {
    // Sentinel node at index 0 (NULL_NODE)
    nodes_.push_back(NodeData{NULL_SYMBOL, {}});

    // Register the built-in "@" apply symbol (arity 2)
    apply_sym_ = symtab_.intern("@", 2);
}

SymbolId NodeManager::declare_symbol(std::string_view name, uint32_t arity) {
    return symtab_.intern(name, arity);
}

SymbolId NodeManager::lookup_symbol(std::string_view name) const {
    return symtab_.lookup(name);
}

NodeId NodeManager::mk_const(SymbolId sym) {
    NodeData nd{sym, {}};
    auto it = table_.find(nd);
    if (it != table_.end()) return it->second;

    NodeId id = static_cast<NodeId>(nodes_.size());
    nodes_.push_back(nd);
    table_[nd] = id;
    return id;
}

NodeId NodeManager::mk_app(SymbolId sym, std::span<const NodeId> children) {
    if (children.empty()) return mk_const(sym);

    NodeData nd{sym, std::vector<NodeId>(children.begin(), children.end())};
    auto it = table_.find(nd);
    if (it != table_.end()) return it->second;

    NodeId id = static_cast<NodeId>(nodes_.size());
    nodes_.push_back(nd);
    table_[nd] = id;
    return id;
}

} // namespace llm2smt
