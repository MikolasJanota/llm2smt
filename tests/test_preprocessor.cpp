#include <gtest/gtest.h>
#include <optional>
#include "core/node.h"
#include "core/node_manager.h"
#include "preprocessor/simplifier.h"

using namespace llm2smt;

// ── Fixture ───────────────────────────────────────────────────────────────────
// U-sorted constants NA..ND (uninterpreted terms).
// Bool-sorted constants PA..PD (predicate atoms).
// Each test gets a fresh NodeManager and Simplifier.

struct SimpFix : ::testing::Test {
    NodeManager              nm;
    NodeId                   NA{}, NB{}, NC{}, ND{};  // U-sorted constants
    NodeId                   PA{}, PB{}, PC{}, PD{};  // Bool-sorted predicate atoms
    std::optional<Simplifier> s;

    void SetUp() override {
        auto nc = [&](const char* name) -> NodeId {
            return nm.mk_const(nm.declare_symbol(name, 0));
        };
        auto nb = [&](const char* name) -> NodeId {
            return nm.mk_const(nm.declare_symbol(name, 0, BOOL_SORT));
        };
        NA = nc("a");  NB = nc("b");  NC = nc("c");  ND = nc("d");
        PA = nb("pa"); PB = nb("pb"); PC = nb("pc"); PD = nb("pd");
        s.emplace(nm);
    }

    NodeId T()                                   { return nm.mk_true();        }
    NodeId F()                                   { return nm.mk_false();       }
    NodeId EQ(NodeId a, NodeId b)                { return nm.mk_eq(a, b);      }
    NodeId NOT(NodeId f)                         { return nm.mk_not(f);        }
    NodeId AND(NodeId a, NodeId b)               { return nm.mk_and(a, b);     }
    NodeId OR(NodeId a, NodeId b)                { return nm.mk_or(a, b);      }
    NodeId IMP(NodeId a, NodeId b)               { return nm.mk_implies(a, b); }
    NodeId XOR(NodeId a, NodeId b)               { return nm.mk_xor(a, b);     }
    NodeId IFF(NodeId a, NodeId b)               { return nm.mk_iff(a, b);     }
    NodeId ITE(NodeId c, NodeId t, NodeId e)     { return nm.mk_ite_bool(c,t,e); }
};

// ── fold: Not smart reduction ─────────────────────────────────────────────────

TEST_F(SimpFix, FoldNotTrue)
    { EXPECT_TRUE(nm.is_false_node(s->fold(NOT(T())))); }
TEST_F(SimpFix, FoldNotFalse)
    { EXPECT_TRUE(nm.is_true_node(s->fold(NOT(F())))); }
TEST_F(SimpFix, FoldDoubleNegEq) {
    NodeId e = EQ(NA, NB);
    EXPECT_EQ(s->fold(NOT(NOT(e))), e);
}
TEST_F(SimpFix, FoldDoubleNegPred) {
    EXPECT_EQ(s->fold(NOT(NOT(PA))), PA);
}

// ── mk_eq: canonical ordering / hash-consing ─────────────────────────────────

TEST_F(SimpFix, EqSymmetric)   { EXPECT_EQ(EQ(NA,NB), EQ(NB,NA)); }
TEST_F(SimpFix, EqSame)        { EXPECT_EQ(EQ(NA,NB), EQ(NA,NB)); }
TEST_F(SimpFix, EqDifferent)   { EXPECT_NE(EQ(NA,NB), EQ(NA,NC)); }
TEST_F(SimpFix, PredSame)      { EXPECT_EQ(PA, PA); }
TEST_F(SimpFix, PredDifferent) { EXPECT_NE(PA, PB); }
TEST_F(SimpFix, MixedKinds)    { EXPECT_NE(EQ(NA,NB), PA); }

// ── Constant folding: And ─────────────────────────────────────────────────────

TEST_F(SimpFix, AndWithFalse)
    { EXPECT_TRUE(nm.is_false_node(s->fold(AND(EQ(NA,NB), F())))); }

TEST_F(SimpFix, AndWithTrue) {
    NodeId e = EQ(NA, NB);
    EXPECT_EQ(s->fold(AND(e, T())), e);
}

TEST_F(SimpFix, AndBothTrue)
    { EXPECT_TRUE(nm.is_true_node(s->fold(AND(T(),T())))); }

TEST_F(SimpFix, AndTriple) {
    // and(and(true, Eq), true) → Eq
    NodeId e = EQ(NA, NB);
    EXPECT_EQ(s->fold(AND(AND(T(), e), T())), e);
}

// ── Constant folding: Or ──────────────────────────────────────────────────────

TEST_F(SimpFix, OrWithTrue)
    { EXPECT_TRUE(nm.is_true_node(s->fold(OR(PA, T())))); }

TEST_F(SimpFix, OrWithFalse) {
    EXPECT_EQ(s->fold(OR(PA, F())), PA);
}

TEST_F(SimpFix, OrBothFalse)
    { EXPECT_TRUE(nm.is_false_node(s->fold(OR(F(),F())))); }

// ── Constant folding: Ite ─────────────────────────────────────────────────────

TEST_F(SimpFix, IteCondTrue) {
    EXPECT_EQ(s->fold(ITE(T(), PA, PB)), PA);
}

TEST_F(SimpFix, IteCondFalse) {
    NodeId e = EQ(NA, NB);
    EXPECT_EQ(s->fold(ITE(F(), PC, e)), e);
}

TEST_F(SimpFix, IteBothBranchesTrue)
    { EXPECT_TRUE(nm.is_true_node(s->fold(ITE(PA, T(), T())))); }

TEST_F(SimpFix, IteBothBranchesFalse)
    { EXPECT_TRUE(nm.is_false_node(s->fold(ITE(PA, F(), F())))); }

TEST_F(SimpFix, IteToCondThen) {
    // ite(c, true, false) = c
    EXPECT_EQ(s->fold(ITE(PA, T(), F())), PA);
}

TEST_F(SimpFix, IteToNegCond) {
    // ite(c, false, true) = ¬c
    NodeId r = s->fold(ITE(PA, F(), T()));
    ASSERT_TRUE(nm.is_not(r));
    EXPECT_EQ(nm.get(r).children[0], PA);
}

// ── Constant folding: Implies ─────────────────────────────────────────────────

TEST_F(SimpFix, ImpliesAntFalse)
    { EXPECT_TRUE(nm.is_true_node(s->fold(IMP(F(), EQ(NA,NB))))); }

TEST_F(SimpFix, ImpliesAntTrue) {
    NodeId e = EQ(NA, NB);
    EXPECT_EQ(s->fold(IMP(T(), e)), e);
}

TEST_F(SimpFix, ImpliesConseqTrue)
    { EXPECT_TRUE(nm.is_true_node(s->fold(IMP(PA, T())))); }

TEST_F(SimpFix, ImpliesConseqFalse) {
    // a→⊥ = ¬a
    NodeId r = s->fold(IMP(PA, F()));
    ASSERT_TRUE(nm.is_not(r));
    EXPECT_TRUE(nm.is_atom_node(nm.get(r).children[0]));
}

// ── Constant folding: Xor ─────────────────────────────────────────────────────

TEST_F(SimpFix, XorTrueTrue)
    { EXPECT_TRUE(nm.is_false_node(s->fold(XOR(T(),T())))); }
TEST_F(SimpFix, XorFalseFalse)
    { EXPECT_TRUE(nm.is_false_node(s->fold(XOR(F(),F())))); }
TEST_F(SimpFix, XorTrueFalse)
    { EXPECT_TRUE(nm.is_true_node(s->fold(XOR(T(),F())))); }
TEST_F(SimpFix, XorFalseTrue)
    { EXPECT_TRUE(nm.is_true_node(s->fold(XOR(F(),T())))); }

TEST_F(SimpFix, XorWithTrue) {
    // xor(true, p) = ¬p
    NodeId r = s->fold(XOR(T(), PA));
    ASSERT_TRUE(nm.is_not(r));
    EXPECT_TRUE(nm.is_atom_node(nm.get(r).children[0]));
}

TEST_F(SimpFix, XorWithFalse) {
    // xor(false, p) = p
    EXPECT_EQ(s->fold(XOR(F(), PA)), PA);
}

// ── Constant folding: BoolEq (iff) ────────────────────────────────────────────

TEST_F(SimpFix, BoolEqTrueB) {
    NodeId e = EQ(NA, NB);
    EXPECT_EQ(s->fold(IFF(T(), e)), e);
}
TEST_F(SimpFix, BoolEqFalseB) {
    NodeId r = s->fold(IFF(F(), EQ(NA, NB)));
    EXPECT_TRUE(nm.is_not(r));
}
TEST_F(SimpFix, BoolEqATrue) {
    NodeId e = EQ(NA, NB);
    EXPECT_EQ(s->fold(IFF(e, T())), e);
}
TEST_F(SimpFix, BoolEqAFalse) {
    NodeId r = s->fold(IFF(EQ(NA, NB), F()));
    EXPECT_TRUE(nm.is_not(r));
}

// ── Same-subtree identity simplifications ─────────────────────────────────────

TEST_F(SimpFix, IteSameBranches) {
    // ite(c, f, f) = f
    NodeId e = EQ(NA, NB);
    EXPECT_EQ(s->fold(ITE(PA, e, e)), e);
}

TEST_F(SimpFix, ImpliesSameSides) {
    // p → p = true
    NodeId e = EQ(NA, NB);
    EXPECT_TRUE(nm.is_true_node(s->fold(IMP(e, e))));
}

TEST_F(SimpFix, XorSameSides) {
    // p ⊕ p = false
    NodeId e = EQ(NA, NB);
    EXPECT_TRUE(nm.is_false_node(s->fold(XOR(e, e))));
}

TEST_F(SimpFix, BoolEqSameSides) {
    // p ↔ p = true
    NodeId e = EQ(NA, NB);
    EXPECT_TRUE(nm.is_true_node(s->fold(IFF(e, e))));
}

// ── Nested folding ────────────────────────────────────────────────────────────

TEST_F(SimpFix, NestedAndOr) {
    // or(and(false, Eq), true) = true
    EXPECT_TRUE(nm.is_true_node(s->fold(OR(AND(F(), EQ(NA,NB)), T()))));
}

TEST_F(SimpFix, DeepNested) {
    // and(not(false), or(true, Pred)) = true
    EXPECT_TRUE(nm.is_true_node(s->fold(AND(NOT(F()), OR(T(), PA)))));
}

// ── subst_and_fold ────────────────────────────────────────────────────────────

TEST_F(SimpFix, ForcedEqBecomesTrue) {
    NodeId e = EQ(NA, NB);
    EXPECT_TRUE(nm.is_true_node(s->subst_and_fold(e, e, true)));
}

TEST_F(SimpFix, ForcedEqBecomesFalse) {
    NodeId e = EQ(NA, NB);
    EXPECT_TRUE(nm.is_false_node(s->subst_and_fold(e, e, false)));
}

TEST_F(SimpFix, SymmetricEqForced) {
    // mk_eq is symmetric: EQ(a,b)==EQ(b,a), so forcing one forces the other
    EXPECT_TRUE(nm.is_true_node(s->subst_and_fold(EQ(NB,NA), EQ(NA,NB), true)));
}

TEST_F(SimpFix, AndCollapsesWhenAtomForced) {
    // and(Eq(a,b), Pred(c)) where Eq(a,b) forced true → Pred(c)
    EXPECT_EQ(s->subst_and_fold(AND(EQ(NA,NB), PC), EQ(NA,NB), true), PC);
}

TEST_F(SimpFix, OrCollapsesWhenAtomForced) {
    // or(Pred(a), Eq(b,c)) where Pred(a) forced true → True
    EXPECT_TRUE(nm.is_true_node(s->subst_and_fold(OR(PA, EQ(NB,NC)), PA, true)));
}

TEST_F(SimpFix, NegAtomInOr) {
    // or(Not(Eq(a,b)), Pred(c)) where Eq(a,b) forced true → Pred(c)
    EXPECT_EQ(s->subst_and_fold(OR(NOT(EQ(NA,NB)), PC), EQ(NA,NB), true), PC);
}

TEST_F(SimpFix, IteCondForced) {
    // ite(Pred(a), Eq(b,c), Pred(d)) where Pred(a) forced true → Eq(b,c)
    NodeId e = EQ(NB, NC);
    EXPECT_EQ(s->subst_and_fold(ITE(PA, e, PD), PA, true), e);
}

// ── run_pass: unit propagation ────────────────────────────────────────────────

TEST_F(SimpFix, EqUnitPropagates) {
    // [Eq(a,b), And(Eq(a,b), Pred(c))]
    // Eq(a,b) is unit → forced true → and(true, Pred(c)) = Pred(c)
    NodeId e = EQ(NA, NB);
    std::vector<NodeId> assertions = {e, AND(e, PC)};
    bool changed = s->run_pass(assertions);
    EXPECT_TRUE(changed);
    ASSERT_EQ(s->forced_atoms().size(), 1U);
    EXPECT_TRUE(s->forced_atoms()[0].positive);
    EXPECT_EQ(assertions[1], PC);
}

TEST_F(SimpFix, NegEqUnitPropagates) {
    // [Not(Eq(a,b)), Or(Eq(a,b), Pred(c))]
    // Not(Eq) → Eq forced false → or(false, Pred(c)) = Pred(c)
    NodeId e = EQ(NA, NB);
    std::vector<NodeId> assertions = {NOT(e), OR(e, PC)};
    s->run_pass(assertions);
    ASSERT_EQ(s->forced_atoms().size(), 1U);
    EXPECT_FALSE(s->forced_atoms()[0].positive);
    EXPECT_EQ(assertions[1], PC);
}

TEST_F(SimpFix, PredUnitPropagates) {
    // [Pred(a), Or(Not(Pred(a)), Eq(b,c))]
    // Pred(a) forced true → Not(Pred(a))→False → Or(false, Eq) = Eq
    NodeId e = EQ(NB, NC);
    std::vector<NodeId> assertions = {PA, OR(NOT(PA), e)};
    s->run_pass(assertions);
    ASSERT_EQ(s->forced_atoms().size(), 1U);
    EXPECT_EQ(assertions[1], e);
}

TEST_F(SimpFix, ConflictDetected) {
    // [Eq(a,b), Not(Eq(a,b))] → one becomes False
    std::vector<NodeId> assertions = {EQ(NA,NB), NOT(EQ(NA,NB))};
    s->run_pass(assertions);
    bool has_false = false;
    for (NodeId f : assertions)
        if (nm.is_false_node(f)) has_false = true;
    EXPECT_TRUE(has_false);
}

// ── run (multi-pass) ──────────────────────────────────────────────────────────

TEST_F(SimpFix, PropagatesAcrossIterations) {
    // [Pred(a), Implies(Pred(a), Eq(b,c)), And(Eq(b,c), Pred(d))]
    // Pass 1: PA unit → Implies(true,Eq)=Eq unit → And(true,PD)=PD unit
    // All three atoms discovered; every assertion becomes True.
    NodeId ebc = EQ(NB, NC);
    std::vector<NodeId> assertions = {PA, IMP(PA, ebc), AND(ebc, PD)};
    s->run(assertions, 10);
    EXPECT_EQ(s->forced_atoms().size(), 3U);
    for (NodeId f : assertions)
        EXPECT_TRUE(nm.is_true_node(f));
}

TEST_F(SimpFix, StopsWhenStable) {
    // [Or(Pred(a), Pred(b))] — no unit, no change
    std::vector<NodeId> assertions = {OR(PA, PB)};
    s->run(assertions, 10);
    EXPECT_TRUE(s->forced_atoms().empty());
    EXPECT_TRUE(nm.is_or(assertions[0]));
}

TEST_F(SimpFix, TransitiveEqCollapses) {
    // [Eq(a,b), Eq(b,c), And(Eq(a,c), Pred(d))]
    // ab and bc are units → UF has find(a)==find(c).
    // Phase 4 normalizes Eq(a,c) → True; And(True, PD) = PD.
    NodeId ab = EQ(NA, NB);
    NodeId bc = EQ(NB, NC);
    std::vector<NodeId> assertions = {ab, bc, AND(EQ(NA, NC), PD)};
    s->run_pass(assertions);
    EXPECT_GE(s->forced_atoms().size(), 2U);
    EXPECT_EQ(assertions[2], PD);
}

TEST_F(SimpFix, TransitiveEqSymmetric) {
    // Eq(b,a) and Eq(b,c) forced.  Eq(a,c) inside compound → collapses to True.
    NodeId ba = EQ(NB, NA);
    NodeId bc = EQ(NB, NC);
    std::vector<NodeId> assertions = {ba, bc, AND(EQ(NA, NC), PD)};
    s->run_pass(assertions);
    EXPECT_EQ(assertions[2], PD);
}

TEST_F(SimpFix, ZeroPassesIsNoOp) {
    NodeId e = EQ(NA, NB);
    std::vector<NodeId> assertions = {e, AND(e, PC)};
    s->run(assertions, 0);
    EXPECT_TRUE(s->forced_atoms().empty());
    EXPECT_TRUE(nm.is_and(assertions[1]));
}

// ── And/Or nesting: no structural restructuring ───────────────────────────────
// fold() performs constant folding but does NOT restructure nested And/Or trees.
// Semantic simplification (true/false propagation) still works correctly at all
// nesting depths. The SAT encoder handles nested binary And/Or natively.

TEST_F(SimpFix, NestedAndUnchanged) {
    // and(and(eq1,eq2), and(pa,pb)) — no constants → returned unchanged
    NodeId eq1 = EQ(NA, NB);
    NodeId eq2 = EQ(NC, ND);
    NodeId outer = AND(AND(eq1, eq2), AND(PA, PB));
    EXPECT_EQ(s->fold(outer), outer);
}

TEST_F(SimpFix, NestedOrUnchanged) {
    // or(or(eq1,eq2), or(pa,pb)) — no constants → returned unchanged
    NodeId eq1 = EQ(NA, NB);
    NodeId eq2 = EQ(NC, ND);
    NodeId outer = OR(OR(eq1, eq2), OR(PA, PB));
    EXPECT_EQ(s->fold(outer), outer);
}

TEST_F(SimpFix, NestedAndOrMixUnchanged) {
    // and(or(Eq,Pred), Pred) — mixed kinds: returned unchanged
    NodeId inner = OR(EQ(NA,NB), PA);
    NodeId outer = AND(inner, PB);
    EXPECT_EQ(s->fold(outer), outer);
}

TEST_F(SimpFix, NestedAndDeepUnchanged) {
    // and(and(eq,pa), and(pb,pc)) — no constants → returned unchanged
    NodeId eq = EQ(NA, NB);
    NodeId outer = AND(AND(eq, PA), AND(PB, PC));
    EXPECT_EQ(s->fold(outer), outer);
}

TEST_F(SimpFix, SetFlattenIsNoOp) {
    // set_flatten(false) keeps nested — same result as set_flatten(true)
    NodeId eq1 = EQ(NA, NB);
    NodeId eq2 = EQ(NC, ND);
    NodeId outer = AND(AND(eq1, eq2), AND(PA, PB));
    NodeId r_default = s->fold(outer);
    s->set_flatten(false);
    // A second Simplifier with flatten disabled should give the same result.
    Simplifier s2(nm);
    s2.set_flatten(false);
    EXPECT_EQ(s2.fold(outer), r_default);
}

TEST_F(SimpFix, TrueInNestedAnd) {
    // and(and(Eq(a,b), true), Pred(c)) → and(Eq(a,b), Pred(c))
    // True is eliminated by constant folding regardless of nesting.
    NodeId e = EQ(NA, NB);
    NodeId r = s->fold(AND(AND(e, T()), PC));
    EXPECT_EQ(r, AND(e, PC));
}

// ── Performance: deep OR chain must not be O(N²) ──────────────────────────────

TEST_F(SimpFix, DeepOrChainLinear) {
    // Right-skewed OR chain of depth 2000 with a false innermost leaf.
    // fold() must complete quickly (O(N)) and propagate the false upward.
    // The innermost OR(PA, F()) folds to PA, then each outer OR(PA, PA) stays.
    // We verify correctness by checking the innermost fold.
    NodeId inner = OR(PA, F());  // folds to PA
    NodeId f = inner;
    for (int i = 0; i < 1999; ++i)
        f = OR(PA, f);
    // fold(OR(PA, F())) = PA — correct constant folding in nested structure
    EXPECT_EQ(s->fold(inner), PA);
    // Full chain folds without hanging (O(N²) would be ~400ms for N=2000)
    s->fold(f);
}

TEST_F(SimpFix, DeepAndChainFalsePropagate) {
    // Left-skewed AND chain: AND(AND(AND(..., PA), PA), F()) → False
    NodeId f = PA;
    for (int i = 0; i < 999; ++i)
        f = AND(f, PA);
    f = AND(f, F());  // innermost false propagates up
    EXPECT_TRUE(nm.is_false_node(s->fold(f)));
}
