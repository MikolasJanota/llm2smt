#pragma once

#include <unordered_map>
#include <vector>

#include "core/node_manager.h"

namespace llm2smt {

// Converts a formula to Negation Normal Form (NNF).
//
// Memoized to O(DAG-size): each (node, polarity) pair is visited at most once.
// Children are copied to a local vector before recursing to avoid dangling
// references into NodeManager::nodes_ if the vector is reallocated.
class NnfTransformer {
public:
    explicit NnfTransformer(NodeManager& nm, bool memo = false)
        : nm_(nm), memo_(memo) {}

    NodeId pos(NodeId f);
    NodeId neg(NodeId f);

private:
    NodeManager&                        nm_;
    bool                                memo_;
    std::unordered_map<NodeId, NodeId>  pos_cache_;
    std::unordered_map<NodeId, NodeId>  neg_cache_;
};

inline NodeId NnfTransformer::pos(NodeId f)
{
    if (memo_) {
        if (auto it = pos_cache_.find(f); it != pos_cache_.end()) return it->second;
    }

    NodeId r;
    if (nm_.is_true_node(f) || nm_.is_false_node(f) ||
        nm_.is_eq(f)        || nm_.is_atom_node(f)) {
        r = f;
    } else if (nm_.is_not(f)) {
        r = neg(nm_.get(f).children[0]);
    } else if (nm_.is_and(f)) {
        std::vector<NodeId> ch(nm_.get(f).children);   // copy before recursing
        std::vector<NodeId> new_ch;
        new_ch.reserve(ch.size());
        for (NodeId c : ch) new_ch.push_back(pos(c));
        r = nm_.mk_and(new_ch);
    } else if (nm_.is_or(f)) {
        std::vector<NodeId> ch(nm_.get(f).children);
        std::vector<NodeId> new_ch;
        new_ch.reserve(ch.size());
        for (NodeId c : ch) new_ch.push_back(pos(c));
        r = nm_.mk_or(new_ch);
    } else if (nm_.is_implies(f)) {
        NodeId c0 = nm_.get(f).children[0];
        NodeId c1 = nm_.get(f).children[1];
        r = nm_.mk_or(neg(c0), pos(c1));
    } else if (nm_.is_xor(f)) {
        NodeId c0 = nm_.get(f).children[0];
        NodeId c1 = nm_.get(f).children[1];
        r = nm_.mk_or(nm_.mk_and(pos(c0), neg(c1)),
                      nm_.mk_and(neg(c0), pos(c1)));
    } else if (nm_.is_iff(f)) {
        NodeId c0 = nm_.get(f).children[0];
        NodeId c1 = nm_.get(f).children[1];
        r = nm_.mk_and(nm_.mk_or(neg(c0), pos(c1)),
                       nm_.mk_or(pos(c0), neg(c1)));
    } else if (nm_.is_ite_bool(f)) {
        NodeId c0 = nm_.get(f).children[0];
        NodeId c1 = nm_.get(f).children[1];
        NodeId c2 = nm_.get(f).children[2];
        r = nm_.mk_and(nm_.mk_or(neg(c0), pos(c1)),
                       nm_.mk_or(pos(c0), pos(c2)));
    } else {
        r = f;  // unreachable for well-formed input
    }

    if (memo_) pos_cache_[f] = r;
    return r;
}

inline NodeId NnfTransformer::neg(NodeId f)
{
    if (memo_) {
        if (auto it = neg_cache_.find(f); it != neg_cache_.end()) return it->second;
    }

    NodeId r;
    if (nm_.is_true_node(f)) {
        r = nm_.mk_false();
    } else if (nm_.is_false_node(f)) {
        r = nm_.mk_true();
    } else if (nm_.is_eq(f) || nm_.is_atom_node(f)) {
        r = nm_.mk_not(f);
    } else if (nm_.is_not(f)) {
        r = pos(nm_.get(f).children[0]);
    } else if (nm_.is_and(f)) {
        // De Morgan: ¬(A₁ ∧ … ∧ Aₙ) = (¬A₁ ∨ … ∨ ¬Aₙ)
        std::vector<NodeId> ch(nm_.get(f).children);   // copy before recursing
        std::vector<NodeId> new_ch;
        new_ch.reserve(ch.size());
        for (NodeId c : ch) new_ch.push_back(neg(c));
        r = nm_.mk_or(new_ch);
    } else if (nm_.is_or(f)) {
        // De Morgan: ¬(A₁ ∨ … ∨ Aₙ) = (¬A₁ ∧ … ∧ ¬Aₙ)
        std::vector<NodeId> ch(nm_.get(f).children);
        std::vector<NodeId> new_ch;
        new_ch.reserve(ch.size());
        for (NodeId c : ch) new_ch.push_back(neg(c));
        r = nm_.mk_and(new_ch);
    } else if (nm_.is_implies(f)) {
        // ¬(A → B) = (A ∧ ¬B)
        NodeId c0 = nm_.get(f).children[0];
        NodeId c1 = nm_.get(f).children[1];
        r = nm_.mk_and(pos(c0), neg(c1));
    } else if (nm_.is_xor(f)) {
        // ¬(A ⊕ B) = (A ↔ B)
        NodeId c0 = nm_.get(f).children[0];
        NodeId c1 = nm_.get(f).children[1];
        r = nm_.mk_and(nm_.mk_or(neg(c0), pos(c1)),
                       nm_.mk_or(pos(c0), neg(c1)));
    } else if (nm_.is_iff(f)) {
        // ¬(A ↔ B) = (A ⊕ B)
        NodeId c0 = nm_.get(f).children[0];
        NodeId c1 = nm_.get(f).children[1];
        r = nm_.mk_or(nm_.mk_and(pos(c0), neg(c1)),
                      nm_.mk_and(neg(c0), pos(c1)));
    } else if (nm_.is_ite_bool(f)) {
        // ¬ite(c,t,e) = ite(c,¬t,¬e)
        NodeId c0 = nm_.get(f).children[0];
        NodeId c1 = nm_.get(f).children[1];
        NodeId c2 = nm_.get(f).children[2];
        r = nm_.mk_or(nm_.mk_and(pos(c0), neg(c1)),
                      nm_.mk_and(neg(c0), neg(c2)));
    } else {
        r = nm_.mk_not(f);  // unreachable
    }

    if (memo_) neg_cache_[f] = r;
    return r;
}

// Entry point: convert f to NNF.
// Pass memo=true to memoize per-node results (helps on DAG-heavy inputs,
// but adds hash-map overhead that slows tree-shaped inputs).
inline NodeId to_nnf(NodeId f, NodeManager& nm, bool memo = false)
{
    NnfTransformer t(nm, memo);
    return t.pos(f);
}

} // namespace llm2smt
