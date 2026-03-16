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
    // Idempotent if same name+arity is used.
    SymbolId declare_symbol(std::string_view name, uint32_t arity,
                            SortId return_sort = NULL_SORT);

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

    // -----------------------------------------------------------------------
    // Sort queries
    // -----------------------------------------------------------------------

    // True iff the node's head symbol has BOOL_SORT as its return sort.
    bool is_bool(NodeId id) const {
        return symtab_.get(nodes_.at(id).sym).return_sort == BOOL_SORT;
    }

    // -----------------------------------------------------------------------
    // Built-in Boolean connective builders
    // All return a Bool-sorted NodeId; inputs to mk_eq must be U-sorted.
    // -----------------------------------------------------------------------

    NodeId mk_true();
    NodeId mk_false();
    NodeId mk_not(NodeId a);
    NodeId mk_and(NodeId a, NodeId b);
    NodeId mk_or(NodeId a, NodeId b);
    NodeId mk_implies(NodeId a, NodeId b);
    NodeId mk_xor(NodeId a, NodeId b);
    NodeId mk_iff(NodeId a, NodeId b);
    NodeId mk_ite_bool(NodeId cond, NodeId t, NodeId e);
    // EUF equality between two U-sorted terms; result is Bool-sorted.
    // Canonicalises: mk_eq(a,b) == mk_eq(b,a).
    NodeId mk_eq(NodeId a, NodeId b);

    // -----------------------------------------------------------------------
    // Built-in connective predicates
    // -----------------------------------------------------------------------

    bool is_true_node (NodeId id) const { return nodes_.at(id).sym == true_sym_;     }
    bool is_false_node(NodeId id) const { return nodes_.at(id).sym == false_sym_;    }
    bool is_not       (NodeId id) const { return nodes_.at(id).sym == not_sym_;      }
    bool is_and       (NodeId id) const { return nodes_.at(id).sym == and_sym_;      }
    bool is_or        (NodeId id) const { return nodes_.at(id).sym == or_sym_;       }
    bool is_implies   (NodeId id) const { return nodes_.at(id).sym == implies_sym_;  }
    bool is_xor       (NodeId id) const { return nodes_.at(id).sym == xor_sym_;      }
    bool is_iff       (NodeId id) const { return nodes_.at(id).sym == iff_sym_;      }
    bool is_ite_bool  (NodeId id) const { return nodes_.at(id).sym == ite_bool_sym_; }
    bool is_eq        (NodeId id) const { return nodes_.at(id).sym == eq_sym_;       }

    // True iff the node is a Bool-sorted predicate atom: Bool-sorted but not
    // one of the built-in connectives.  These are user-declared Bool functions.
    bool is_atom_node (NodeId id) const {
        return is_bool(id)
            && !is_true_node(id) && !is_false_node(id)
            && !is_eq(id)        && !is_not(id)
            && !is_and(id)       && !is_or(id)
            && !is_implies(id)   && !is_xor(id)
            && !is_iff(id)       && !is_ite_bool(id);
    }

    // -----------------------------------------------------------------------
    // Built-in connective symbol accessors
    // -----------------------------------------------------------------------

    SymbolId true_symbol()     const { return true_sym_;     }
    SymbolId false_symbol()    const { return false_sym_;    }
    SymbolId not_symbol()      const { return not_sym_;      }
    SymbolId and_symbol()      const { return and_sym_;      }
    SymbolId or_symbol()       const { return or_sym_;       }
    SymbolId implies_symbol()  const { return implies_sym_;  }
    SymbolId xor_symbol()      const { return xor_sym_;      }
    SymbolId iff_symbol()      const { return iff_sym_;      }
    SymbolId ite_bool_symbol() const { return ite_bool_sym_; }
    SymbolId eq_symbol()       const { return eq_sym_;       }

private:
    SymbolTable symtab_;
    // nodes_[0] is a sentinel/null node
    std::vector<NodeData>                                    nodes_;
    std::unordered_map<NodeData, NodeId, NodeDataHash>       table_;

    SymbolId apply_sym_;  // The "@" apply symbol for currying

    // Built-in Boolean connective symbols (registered in constructor).
    // Named with "__" prefix to avoid clashing with user-declared symbols.
    SymbolId true_sym_, false_sym_;
    SymbolId not_sym_;
    SymbolId and_sym_, or_sym_;
    SymbolId implies_sym_, xor_sym_, iff_sym_;
    SymbolId ite_bool_sym_;
    SymbolId eq_sym_;
};

} // namespace llm2smt
