#pragma once

#include "core/node_manager.h"

namespace llm2smt {

// Forward declarations for mutual recursion.
inline NodeId nnf_pos(NodeId f, NodeManager& nm);
inline NodeId nnf_neg(NodeId f, NodeManager& nm);

// nnf_pos: convert f (at positive polarity) to NNF.
inline NodeId nnf_pos(NodeId f, NodeManager& nm)
{
    if (nm.is_true_node(f) || nm.is_false_node(f)) return f;
    if (nm.is_eq(f) || nm.is_atom_node(f)) return f;

    if (nm.is_not(f))
        return nnf_neg(nm.get(f).children[0], nm);

    if (nm.is_and(f)) {
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        return nm.mk_and(nnf_pos(c0, nm), nnf_pos(c1, nm));
    }
    if (nm.is_or(f)) {
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        return nm.mk_or(nnf_pos(c0, nm), nnf_pos(c1, nm));
    }
    if (nm.is_implies(f)) {
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        return nm.mk_or(nnf_neg(c0, nm), nnf_pos(c1, nm));
    }
    if (nm.is_xor(f)) {
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        return nm.mk_or(
            nm.mk_and(nnf_pos(c0, nm), nnf_neg(c1, nm)),
            nm.mk_and(nnf_neg(c0, nm), nnf_pos(c1, nm)));
    }
    if (nm.is_iff(f)) {
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        return nm.mk_and(
            nm.mk_or(nnf_neg(c0, nm), nnf_pos(c1, nm)),
            nm.mk_or(nnf_pos(c0, nm), nnf_neg(c1, nm)));
    }
    if (nm.is_ite_bool(f)) {
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        NodeId c2 = nm.get(f).children[2];
        return nm.mk_and(
            nm.mk_or(nnf_neg(c0, nm), nnf_pos(c1, nm)),
            nm.mk_or(nnf_pos(c0, nm), nnf_pos(c2, nm)));
    }
    return f; // unreachable for well-formed input
}

// nnf_neg: convert ¬f (negation pushed inward) to NNF.
inline NodeId nnf_neg(NodeId f, NodeManager& nm)
{
    if (nm.is_true_node(f))  return nm.mk_false();
    if (nm.is_false_node(f)) return nm.mk_true();
    if (nm.is_eq(f) || nm.is_atom_node(f))
        return nm.mk_not(f);  // wrap atom; mk_not won't double-negate
    if (nm.is_not(f))
        return nnf_pos(nm.get(f).children[0], nm);

    if (nm.is_and(f)) {
        // De Morgan: ¬(A ∧ B) = (¬A ∨ ¬B)
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        return nm.mk_or(nnf_neg(c0, nm), nnf_neg(c1, nm));
    }
    if (nm.is_or(f)) {
        // De Morgan: ¬(A ∨ B) = (¬A ∧ ¬B)
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        return nm.mk_and(nnf_neg(c0, nm), nnf_neg(c1, nm));
    }
    if (nm.is_implies(f)) {
        // ¬(A → B) = (A ∧ ¬B)
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        return nm.mk_and(nnf_pos(c0, nm), nnf_neg(c1, nm));
    }
    if (nm.is_xor(f)) {
        // ¬(A ⊕ B) = (A ↔ B)
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        return nm.mk_and(
            nm.mk_or(nnf_neg(c0, nm), nnf_pos(c1, nm)),
            nm.mk_or(nnf_pos(c0, nm), nnf_neg(c1, nm)));
    }
    if (nm.is_iff(f)) {
        // ¬(A ↔ B) = (A ⊕ B)
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        return nm.mk_or(
            nm.mk_and(nnf_pos(c0, nm), nnf_neg(c1, nm)),
            nm.mk_and(nnf_neg(c0, nm), nnf_pos(c1, nm)));
    }
    if (nm.is_ite_bool(f)) {
        // ¬ite(c,t,e) = ite(c,¬t,¬e)
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        NodeId c2 = nm.get(f).children[2];
        return nm.mk_or(
            nm.mk_and(nnf_pos(c0, nm), nnf_neg(c1, nm)),
            nm.mk_and(nnf_neg(c0, nm), nnf_neg(c2, nm)));
    }
    return nm.mk_not(f); // unreachable
}

// Entry point: convert f to NNF.
inline NodeId to_nnf(NodeId f, NodeManager& nm) { return nnf_pos(f, nm); }

} // namespace llm2smt
