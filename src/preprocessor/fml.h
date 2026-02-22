#pragma once

#include <memory>
#include <vector>

#include "core/node.h"  // NodeId, NULL_NODE

namespace llm2smt {

// ── Formula kind ──────────────────────────────────────────────────────────────

enum class FmlKind {
    True,
    False,
    Eq,      // equality atom    (= eq_lhs eq_rhs),  both U-sorted NodeIds
    Pred,    // predicate atom   pred is a Bool-sorted NodeId (0-ary or n-ary app)
    Not,     // ¬child[0]
    And,     // ∧ children
    Or,      // ∨ children
    Ite,     // children: cond, then, else  (Bool-sorted)
    Implies, // children: antecedent, consequent
    Xor,     // children: left, right
    BoolEq,  // children: left, right  (biconditional / iff)
};

// ── Formula node ─────────────────────────────────────────────────────────────

struct Fml {
    FmlKind kind = FmlKind::True;

    // Atom fields — only valid for the atom kinds:
    NodeId eq_lhs = NULL_NODE;  // Eq: left-hand side
    NodeId eq_rhs = NULL_NODE;  // Eq: right-hand side
    NodeId pred   = NULL_NODE;  // Pred: the Bool-sorted NodeId

    // Sub-formulas (all non-atom kinds):
    std::vector<std::shared_ptr<Fml>> children;
};

using FmlRef = std::shared_ptr<Fml>;

// ── Atom factories ────────────────────────────────────────────────────────────

inline FmlRef fml_true()  { return std::make_shared<Fml>(Fml{FmlKind::True}); }
inline FmlRef fml_false() { return std::make_shared<Fml>(Fml{FmlKind::False}); }

inline FmlRef fml_eq(NodeId lhs, NodeId rhs)
{
    auto f    = std::make_shared<Fml>();
    f->kind   = FmlKind::Eq;
    f->eq_lhs = lhs;
    f->eq_rhs = rhs;
    return f;
}

inline FmlRef fml_pred(NodeId n)
{
    auto f  = std::make_shared<Fml>();
    f->kind = FmlKind::Pred;
    f->pred = n;
    return f;
}

// ── Atom equality (needed by the simplifier for substitution) ─────────────────
// Eq is symmetric: (= a b) ≡ (= b a).

inline bool fml_atoms_equal(const Fml& a, const Fml& b)
{
    if (a.kind != b.kind) return false;
    if (a.kind == FmlKind::Pred) return a.pred == b.pred;
    if (a.kind == FmlKind::Eq)
        return (a.eq_lhs == b.eq_lhs && a.eq_rhs == b.eq_rhs)
            || (a.eq_lhs == b.eq_rhs && a.eq_rhs == b.eq_lhs);
    return false;
}

// ── Smart negation ────────────────────────────────────────────────────────────

inline FmlRef fml_not(FmlRef child)
{
    if (child->kind == FmlKind::True)  return fml_false();
    if (child->kind == FmlKind::False) return fml_true();
    // Double negation elimination:
    if (child->kind == FmlKind::Not)   return child->children[0];
    auto f  = std::make_shared<Fml>();
    f->kind = FmlKind::Not;
    f->children = {child};
    return f;
}

// ── Compound factories ────────────────────────────────────────────────────────

inline FmlRef fml_and(std::vector<FmlRef> ch)
{
    auto f  = std::make_shared<Fml>();
    f->kind = FmlKind::And;
    f->children = std::move(ch);
    return f;
}

inline FmlRef fml_or(std::vector<FmlRef> ch)
{
    auto f  = std::make_shared<Fml>();
    f->kind = FmlKind::Or;
    f->children = std::move(ch);
    return f;
}

inline FmlRef fml_ite(FmlRef c, FmlRef t, FmlRef el)
{
    auto f  = std::make_shared<Fml>();
    f->kind = FmlKind::Ite;
    f->children = {c, t, el};
    return f;
}

inline FmlRef fml_implies(FmlRef a, FmlRef b)
{
    auto f  = std::make_shared<Fml>();
    f->kind = FmlKind::Implies;
    f->children = {a, b};
    return f;
}

inline FmlRef fml_xor(FmlRef a, FmlRef b)
{
    auto f  = std::make_shared<Fml>();
    f->kind = FmlKind::Xor;
    f->children = {a, b};
    return f;
}

inline FmlRef fml_booleq(FmlRef a, FmlRef b)
{
    auto f  = std::make_shared<Fml>();
    f->kind = FmlKind::BoolEq;
    f->children = {a, b};
    return f;
}

} // namespace llm2smt
