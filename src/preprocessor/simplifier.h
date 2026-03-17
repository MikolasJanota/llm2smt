#pragma once

#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "core/node.h"
#include "core/node_manager.h"

namespace llm2smt {

// Simplifies Boolean formula trees over the NodeId IR (NodeManager).
//
// Atoms are mk_eq(NodeId,NodeId) and is_atom_node(NodeId) (Bool-sorted
// user predicates); they are treated as opaque propositions.
//
// Implemented passes (applied in order per iteration):
//   1. Constant folding: propagate True/False through all connectives.
//   2. Unit clause propagation: identify unit assertions (a single atom or its
//      negation) and substitute them into all other assertions, then fold.
//   3. Equality normalization: maintain a union-find over NodeIds forced equal.
//      Rewrite every mk_eq(x,y) to mk_eq(find(x), find(y)); if find(x)==find(y)
//      the atom collapses to True.  This handles transitivity that boolean
//      substitution alone cannot see.
//
// After run(), forced_atoms() lists every atom that was forced along with its
// polarity (true = forced true, false = forced false).
class Simplifier {
public:
    explicit Simplifier(NodeManager& nm);

    // Constant-fold (and optionally flatten) a single formula.
    NodeId fold(NodeId root);

    // Substitute atom (or its negation) → True/False in f, then fold.
    // forced_positive=true means the atom is known to be true.
    NodeId subst_and_fold(NodeId f, NodeId atom, bool forced_positive);

    // One pass of constant folding + unit propagation.
    // Returns true if any formula changed.
    bool run_pass(std::vector<NodeId>& assertions);

    // Up to `passes` iterations (stops early when stable).
    void run(std::vector<NodeId>& assertions, int passes);

    // Enable/disable And-in-And / Or-in-Or flattening during fold().
    // Default: true.
    void set_flatten(bool v) { flatten_ = v; }
    bool flatten() const     { return flatten_; }

    struct ForcedAtom { NodeId atom; bool positive; };
    const std::vector<ForcedAtom>& forced_atoms() const { return forced_; }

    // Number of passes that changed at least one assertion (capped at `passes`).
    int passes_run() const { return passes_run_; }

private:
    NodeManager&                       nm_;
    bool                               flatten_ = true;
    std::vector<ForcedAtom>            forced_;
    std::unordered_set<NodeId>         forced_set_;  // shadow set for O(1) dedup
    int                                passes_run_ = 0;

    // Memoization cache for fold(): NodeId → folded NodeId.
    // fold() is pure (NodeManager nodes are immutable), so the result is stable.
    std::unordered_map<NodeId, NodeId> fold_cache_;

    // Cache for subst_many_and_fold(): cleared before each batch substitution.
    std::unordered_map<NodeId, NodeId> subst_cache_;

    // Cache for normalize_eq_fml(): cleared at the start of each Phase 4.
    // Pure given fixed UF state (parent_ is read-only during Phase 4).
    std::unordered_map<NodeId, NodeId> norm_cache_;

    // Substitute all atoms in `subst` simultaneously (atom → True/False), then fold.
    // Memoized via subst_cache_ for a single batch (caller must clear before use).
    NodeId subst_many_and_fold(NodeId root,
                               const std::unordered_map<NodeId, NodeId>& subst);

    // Equality union-find over NodeIds (for transitivity-aware normalization).
    // Accumulates across all passes: equalities forced in pass k remain in
    // parent_ for passes k+1, k+2, … (transitive equalities are permanent).
    std::unordered_map<NodeId, NodeId> parent_;
    NodeId uf_find(NodeId n);       // path-compressing find
    void   uf_union(NodeId a, NodeId b);

    // Rewrite every mk_eq(x,y) in f to mk_eq(find(x), find(y)), folding as needed.
    NodeId normalize_eq_fml(NodeId root);

    // True iff f is a Bool-sorted predicate atom (not a connective).
    bool is_atom(NodeId f) const { return nm_.is_atom_node(f); }
};

} // namespace llm2smt
