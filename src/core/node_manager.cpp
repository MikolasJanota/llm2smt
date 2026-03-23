#include "core/node_manager.h"

#include <algorithm>

namespace llm2smt {

NodeManager::NodeManager() {
    // Sentinel node at index 0 (NULL_NODE)
    nodes_.push_back(NodeData{NULL_SYMBOL, {}});

    // Register the built-in "@" apply symbol (arity 2, U-sorted result)
    apply_sym_ = symtab_.intern("@", 2, NULL_SORT);

    // Register built-in Boolean connective symbols.
    // Names start with "__" so they cannot clash with user-declared symbols.
    true_sym_     = symtab_.intern("__true",     0, BOOL_SORT);
    false_sym_    = symtab_.intern("__false",    0, BOOL_SORT);
    not_sym_      = symtab_.intern("__not",      1, BOOL_SORT);
    and_sym_      = symtab_.intern("__and",      0, BOOL_SORT);  // 0 = variadic
    or_sym_       = symtab_.intern("__or",       0, BOOL_SORT);  // 0 = variadic
    implies_sym_  = symtab_.intern("__implies",  2, BOOL_SORT);
    xor_sym_      = symtab_.intern("__xor",      2, BOOL_SORT);
    iff_sym_      = symtab_.intern("__iff",      2, BOOL_SORT);
    ite_bool_sym_ = symtab_.intern("__ite_bool", 3, BOOL_SORT);
    eq_sym_       = symtab_.intern("__eq",       2, BOOL_SORT);
}

SymbolId NodeManager::declare_symbol(std::string_view name, uint32_t arity,
                                     SortId return_sort) {
    return symtab_.intern(name, arity, return_sort);
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

// ============================================================================
// Built-in Boolean connective builders
// ============================================================================

NodeId NodeManager::mk_true()  { return mk_const(true_sym_);  }
NodeId NodeManager::mk_false() { return mk_const(false_sym_); }

NodeId NodeManager::mk_not(NodeId a) {
    // Smart folding: avoid creating trivially-reducible nodes.
    if (is_true_node(a))  return mk_false();
    if (is_false_node(a)) return mk_true();
    if (is_not(a))        return get(a).children[0];  // ¬¬x = x
    NodeId args[] = {a};
    return mk_app(not_sym_, args);
}

NodeId NodeManager::mk_and(NodeId a, NodeId b) {
    NodeId args[] = {a, b};
    return mk_app(and_sym_, args);
}

NodeId NodeManager::mk_or(NodeId a, NodeId b) {
    NodeId args[] = {a, b};
    return mk_app(or_sym_, args);
}

NodeId NodeManager::mk_and(std::span<const NodeId> children) {
    if (children.empty()) return mk_true();
    if (children.size() == 1) return children[0];
    return mk_app(and_sym_, children);
}

NodeId NodeManager::mk_or(std::span<const NodeId> children) {
    if (children.empty()) return mk_false();
    if (children.size() == 1) return children[0];
    return mk_app(or_sym_, children);
}

NodeId NodeManager::mk_implies(NodeId a, NodeId b) {
    NodeId args[] = {a, b};
    return mk_app(implies_sym_, args);
}

NodeId NodeManager::mk_xor(NodeId a, NodeId b) {
    NodeId args[] = {a, b};
    return mk_app(xor_sym_, args);
}

NodeId NodeManager::mk_iff(NodeId a, NodeId b) {
    NodeId args[] = {a, b};
    return mk_app(iff_sym_, args);
}

NodeId NodeManager::mk_ite_bool(NodeId cond, NodeId t, NodeId e) {
    NodeId args[] = {cond, t, e};
    return mk_app(ite_bool_sym_, args);
}

NodeId NodeManager::mk_eq(NodeId a, NodeId b) {
    // Reflexivity: a = a is always true.
    if (a == b) return mk_true();
    // Canonicalise so that mk_eq(a,b) == mk_eq(b,a).
    if (a > b) std::swap(a, b);
    NodeId args[] = {a, b};
    return mk_app(eq_sym_, args);
}

} // namespace llm2smt
