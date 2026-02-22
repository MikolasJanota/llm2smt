#pragma once

#include <unordered_map>
#include <vector>

#include "core/node.h"
#include "core/node_manager.h"
#include "theories/euf/cc.h"

namespace llm2smt {

// A flat equation to feed into the CC after flattening.
struct FlatEq {
    NodeId result;  // constant = fn(arg)
    NodeId fn;
    NodeId arg;
};

struct FlatResult {
    NodeId flat_node;               // CC constant representing the term
    std::vector<FlatEq> equations;  // flat equations to feed to CC
};

// Transforms arbitrary NodeId terms into flat CC nodes + flat equations.
// Uses the "@" apply symbol from NodeManager for currying n-ary → binary.
class Flattener {
public:
    explicit Flattener(NodeManager& nm, CC& cc);

    // Flatten a term. The resulting flat_node is registered in the CC.
    // All generated equations must be fed to cc.add_app_equation().
    FlatResult flatten(NodeId term);

    // Convenience: flatten and immediately register equations in CC.
    NodeId flatten_and_register(NodeId term);

    // Look up the flat CC node for an original NodeId (NULL_NODE if not cached).
    NodeId get_flat(NodeId n) const {
        auto it = node_to_cc_.find(n);
        return (it != node_to_cc_.end()) ? it->second : NULL_NODE;
    }

private:
    NodeManager& nm_;
    CC&          cc_;

    // Maps original NodeId → flat CC constant NodeId
    std::unordered_map<NodeId, NodeId> node_to_cc_;

    // Flatten and return the CC constant for this term, accumulating equations.
    NodeId do_flatten(NodeId term, std::vector<FlatEq>& eqs);

    // Make a fresh constant node in NodeManager and register in CC.
    NodeId fresh_const();

    uint32_t fresh_counter_ = 0;
};

} // namespace llm2smt
