#pragma once

#include <cstddef>
#include <cstdint>
#include <deque>
#include <functional>
#include <unordered_map>
#include <utility>
#include <variant>
#include <vector>
#include <numeric>

#include "core/node.h"

namespace llm2smt {

// An EqId identifies one input equation fed to the CC.
using EqId = uint32_t;
constexpr EqId NULL_EQ = 0;

enum class EqKind { Atomic, App };

// An equation stored inside CC.
struct Equation {
    EqKind kind;
    NodeId lhs;       // constant on the left-hand side (or result for App)
    NodeId rhs;       // constant on the right-hand side (Atomic), or NULL_NODE (App)
    NodeId app_fn;    // fn node in fn(arg)=lhs, or NULL_NODE
    NodeId app_arg;   // arg node in fn(arg)=lhs, or NULL_NODE
};

// Hash for pairs of NodeIds
struct PairHash {
    std::size_t operator()(std::pair<NodeId, NodeId> p) const noexcept {
        std::size_t h = std::hash<uint32_t>{}(p.first);
        h ^= std::hash<uint32_t>{}(p.second) + 0x9e3779b9u + (h << 6) + (h >> 2);
        return h;
    }
};

// Edge label in the proof forest:
//   Direct(eq)           — equation eq directly justifies this edge
//   Congruence(eq1,eq2)  — two app equations with same-class arguments
struct DirectLabel   { EqId eq; };
struct CongruenceLabel { EqId eq1; EqId eq2; };
using EdgeLabel = std::variant<DirectLabel, CongruenceLabel>;

// Pending entry: two nodes to merge, plus how to justify the merge
struct PendingEntry {
    NodeId a, b;
    EdgeLabel label;
};

// Undo action for backtracking
struct UndoAction {
    enum class Kind {
        SetRepr,
        ClassListPop,
        UseListPop,
        LookupRemove,
        ProofEdge,
        EquationPop
    } kind;

    NodeId node          = NULL_NODE;
    NodeId old_val       = NULL_NODE;
    std::pair<NodeId,NodeId> lookup_key = {NULL_NODE, NULL_NODE};
};

class CC {
public:
    CC();

    // Register a node with the CC (idempotent).
    NodeId add_node(NodeId n);

    // Add atomic equation: lhs = rhs (both must be registered constants).
    EqId add_equation(NodeId lhs, NodeId rhs);

    // Add flat application equation: result = fn(arg) (all registered constants).
    EqId add_app_equation(NodeId result, NodeId fn, NodeId arg);

    // Query: are a and b in the same equivalence class?
    bool are_congruent(NodeId a, NodeId b) const;

    // Find the representative of n's class.
    NodeId find(NodeId n) const;

    // Backtracking support.
    void push_level();
    void pop_level(size_t target_level);

    // Produce a set of EqIds that jointly justify a ≡ b.
    // Precondition: are_congruent(a, b).
    std::vector<EqId> explain(NodeId a, NodeId b);

    // Resize internal structures to accommodate node id n.
    void ensure_node(NodeId n);

    std::size_t num_nodes() const { return repr_.size(); }

    const Equation& get_equation(EqId id) const { return equations_.at(id); }

private:
    // ── Five core data structures (§3.3) ──────────────────────────────────
    std::vector<NodeId>                repr_;
    std::vector<std::vector<NodeId>>   class_list_;
    std::vector<std::vector<EqId>>     use_list_;
    std::unordered_map<std::pair<NodeId,NodeId>, EqId, PairHash> lookup_;
    std::deque<PendingEntry>           pending_;

    // ── Equations table ───────────────────────────────────────────────────
    std::vector<Equation> equations_;   // [0] = sentinel

    // ── Proof forest (§5) ─────────────────────────────────────────────────
    std::vector<NodeId>    proof_parent_;
    std::vector<EdgeLabel> proof_label_;

    // ── Backtracking ──────────────────────────────────────────────────────
    size_t current_level_ = 0;
    std::vector<std::vector<UndoAction>> trail_;

    // ── Internal helpers ──────────────────────────────────────────────────
    EqId alloc_equation(Equation eq);
    void propagate();
    void do_merge(NodeId ra, NodeId rb);  // ra=kept rep, rb=merged rep
    void set_proof_edge(NodeId from, NodeId to, const EdgeLabel& label);

    void record(UndoAction ua);
    void record_set_repr(NodeId node, NodeId old_repr);
    void record_class_list_pop(NodeId r);
    void record_use_list_pop(NodeId r);
    void record_lookup_remove(std::pair<NodeId,NodeId> key);
    void record_proof_edge(NodeId node);

    // ── Explain helpers ────────────────────────────────────────────────────
    // Simple union-find used only inside explain()
    struct PathUF {
        std::vector<NodeId> parent;
        NodeId find(NodeId x) {
            while (parent[x] != x) { parent[x] = parent[parent[x]]; x = parent[x]; }
            return x;
        }
        void unite(NodeId x, NodeId y) {
            x = find(x); y = find(y);
            if (x != y) parent[y] = x;
        }
        void init(size_t n) {
            parent.resize(n);
            std::iota(parent.begin(), parent.end(), NodeId(0));
        }
    };

    // Find LCA of a and b in the proof forest.
    NodeId find_lca(NodeId a, NodeId b);

    // Walk from a up to lca, collecting justifications into result.
    void explain_path(NodeId a, NodeId lca, PathUF& uf,
                      std::deque<std::pair<NodeId,NodeId>>& pending_pairs,
                      std::vector<EqId>& result);
};

} // namespace llm2smt
