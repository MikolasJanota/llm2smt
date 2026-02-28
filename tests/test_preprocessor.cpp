#include <gtest/gtest.h>
#include "preprocessor/fml.h"
#include "preprocessor/simplifier.h"

using namespace llm2smt;

// ── Helpers ───────────────────────────────────────────────────────────────────

// Fake NodeIds — arbitrary values for testing structural equality.
static constexpr NodeId NA = 10, NB = 20, NC = 30, ND = 40;

static FmlRef T()            { return fml_true(); }
static FmlRef F()            { return fml_false(); }
static FmlRef EQ(NodeId a, NodeId b) { return fml_eq(a, b); }
static FmlRef PR(NodeId n)           { return fml_pred(n); }
static FmlRef NOT(FmlRef f)          { return fml_not(f); }
static FmlRef AND(FmlRef a, FmlRef b){ return fml_and({a, b}); }
static FmlRef AND3(FmlRef a, FmlRef b, FmlRef c){ return fml_and({a, b, c}); }
static FmlRef OR(FmlRef a, FmlRef b) { return fml_or({a, b}); }
static FmlRef OR3(FmlRef a, FmlRef b, FmlRef c) { return fml_or({a, b, c}); }
static FmlRef IMP(FmlRef a, FmlRef b){ return fml_implies(a, b); }
static FmlRef XOR(FmlRef a, FmlRef b){ return fml_xor(a, b); }
static FmlRef IFF(FmlRef a, FmlRef b){ return fml_booleq(a, b); }
static FmlRef ITE(FmlRef c, FmlRef t, FmlRef e) { return fml_ite(c, t, e); }

// ── fml_not smart negation ────────────────────────────────────────────────────

TEST(FmlNot, NegatesTrue)   { EXPECT_EQ(fml_not(T())->kind, FmlKind::False); }
TEST(FmlNot, NegatesFalse)  { EXPECT_EQ(fml_not(F())->kind, FmlKind::True); }
TEST(FmlNot, DoubleNegEq)   { auto e = EQ(NA,NB); EXPECT_EQ(fml_not(NOT(e)).get(), e.get()); }
TEST(FmlNot, DoubleNegPred) { auto p = PR(NA); EXPECT_EQ(fml_not(NOT(p)).get(), p.get()); }

// ── fml_atoms_equal ───────────────────────────────────────────────────────────

TEST(AtomsEqual, EqSymmetric)    { EXPECT_TRUE(fml_atoms_equal(*EQ(NA,NB), *EQ(NB,NA))); }
TEST(AtomsEqual, EqSame)         { EXPECT_TRUE(fml_atoms_equal(*EQ(NA,NB), *EQ(NA,NB))); }
TEST(AtomsEqual, EqDifferent)    { EXPECT_FALSE(fml_atoms_equal(*EQ(NA,NB), *EQ(NA,NC))); }
TEST(AtomsEqual, PredSame)       { EXPECT_TRUE(fml_atoms_equal(*PR(NA), *PR(NA))); }
TEST(AtomsEqual, PredDifferent)  { EXPECT_FALSE(fml_atoms_equal(*PR(NA), *PR(NB))); }
TEST(AtomsEqual, MixedKinds)     { EXPECT_FALSE(fml_atoms_equal(*EQ(NA,NB), *PR(NA))); }

// ── Constant folding: And ─────────────────────────────────────────────────────

TEST(Fold, AndWithFalse)
{
    Simplifier s;
    EXPECT_EQ(s.fold(AND(EQ(NA,NB), F()))->kind, FmlKind::False);
}

TEST(Fold, AndWithTrue)
{
    Simplifier s;
    auto e = EQ(NA, NB);
    FmlRef r = s.fold(AND(e, T()));
    EXPECT_EQ(r.get(), e.get());  // dropped trivially-true child; single child returned
}

TEST(Fold, AndBothTrue) { Simplifier s; EXPECT_EQ(s.fold(AND(T(),T()))->kind, FmlKind::True); }

TEST(Fold, AndTriple)
{
    Simplifier s;
    // and(true, Eq, true) → Eq
    auto e = EQ(NA, NB);
    FmlRef r = s.fold(fml_and({T(), e, T()}));
    EXPECT_EQ(r.get(), e.get());
}

// ── Constant folding: Or ──────────────────────────────────────────────────────

TEST(Fold, OrWithTrue)
{
    Simplifier s;
    EXPECT_EQ(s.fold(OR(PR(NA), T()))->kind, FmlKind::True);
}

TEST(Fold, OrWithFalse)
{
    Simplifier s;
    auto p = PR(NA);
    FmlRef r = s.fold(OR(p, F()));
    EXPECT_EQ(r.get(), p.get());
}

TEST(Fold, OrBothFalse) { Simplifier s; EXPECT_EQ(s.fold(OR(F(),F()))->kind, FmlKind::False); }

// ── Constant folding: Ite ─────────────────────────────────────────────────────

TEST(Fold, IteCondTrue)
{
    Simplifier s;
    auto t = PR(NA);
    FmlRef r = s.fold(ITE(T(), t, PR(NB)));
    EXPECT_EQ(r.get(), t.get());
}

TEST(Fold, IteCondFalse)
{
    Simplifier s;
    auto e = EQ(NA, NB);
    FmlRef r = s.fold(ITE(F(), PR(NC), e));
    EXPECT_EQ(r.get(), e.get());
}

TEST(Fold, IteBothBranchesTrue)
{
    Simplifier s;
    EXPECT_EQ(s.fold(ITE(PR(NA), T(), T()))->kind, FmlKind::True);
}

TEST(Fold, IteBothBranchesFalse)
{
    Simplifier s;
    EXPECT_EQ(s.fold(ITE(PR(NA), F(), F()))->kind, FmlKind::False);
}

TEST(Fold, IteToCondThen)
{
    // ite(c, true, false) = c
    Simplifier s;
    auto c = PR(NA);
    FmlRef r = s.fold(ITE(c, T(), F()));
    EXPECT_EQ(r.get(), c.get());
}

TEST(Fold, IteToNegCond)
{
    // ite(c, false, true) = ¬c
    Simplifier s;
    FmlRef c = PR(NA);
    FmlRef r = s.fold(ITE(c, F(), T()));
    ASSERT_EQ(r->kind, FmlKind::Not);
    EXPECT_EQ(r->children[0].get(), c.get());
}

// ── Constant folding: Implies ─────────────────────────────────────────────────

TEST(Fold, ImpliesAntFalse)
{
    Simplifier s;
    EXPECT_EQ(s.fold(IMP(F(), EQ(NA,NB)))->kind, FmlKind::True);
}

TEST(Fold, ImpliesAntTrue)
{
    Simplifier s;
    auto e = EQ(NA, NB);
    FmlRef r = s.fold(IMP(T(), e));
    EXPECT_EQ(r.get(), e.get());
}

TEST(Fold, ImpliesConseqTrue)
{
    Simplifier s;
    EXPECT_EQ(s.fold(IMP(PR(NA), T()))->kind, FmlKind::True);
}

TEST(Fold, ImpliesConseqFalse)
{
    Simplifier s;
    // a→⊥ = ¬a
    FmlRef r = s.fold(IMP(PR(NA), F()));
    ASSERT_EQ(r->kind, FmlKind::Not);
    EXPECT_EQ(r->children[0]->kind, FmlKind::Pred);
}

// ── Constant folding: Xor ─────────────────────────────────────────────────────

TEST(Fold, XorTrueTrue)  { Simplifier s; EXPECT_EQ(s.fold(XOR(T(),T()))->kind, FmlKind::False); }
TEST(Fold, XorFalseFalse){ Simplifier s; EXPECT_EQ(s.fold(XOR(F(),F()))->kind, FmlKind::False); }
TEST(Fold, XorTrueFalse) { Simplifier s; EXPECT_EQ(s.fold(XOR(T(),F()))->kind, FmlKind::True); }
TEST(Fold, XorFalseTrue) { Simplifier s; EXPECT_EQ(s.fold(XOR(F(),T()))->kind, FmlKind::True); }

TEST(Fold, XorWithTrue)
{
    Simplifier s;
    // xor(true, p) = ¬p
    FmlRef r = s.fold(XOR(T(), PR(NA)));
    ASSERT_EQ(r->kind, FmlKind::Not);
    ASSERT_EQ(r->children[0]->kind, FmlKind::Pred);
}

TEST(Fold, XorWithFalse)
{
    Simplifier s;
    // xor(false, p) = p
    auto p = PR(NA);
    FmlRef r = s.fold(XOR(F(), p));
    EXPECT_EQ(r.get(), p.get());
}

// ── Constant folding: BoolEq ──────────────────────────────────────────────────

TEST(Fold, BoolEqTrueB)
{
    Simplifier s;
    auto e = EQ(NA, NB);
    EXPECT_EQ(s.fold(IFF(T(), e)).get(), e.get());
}
TEST(Fold, BoolEqFalseB)
{
    Simplifier s;
    FmlRef r = s.fold(IFF(F(), EQ(NA, NB)));
    EXPECT_EQ(r->kind, FmlKind::Not);
}
TEST(Fold, BoolEqATrue)
{
    Simplifier s;
    auto e = EQ(NA, NB);
    EXPECT_EQ(s.fold(IFF(e, T())).get(), e.get());
}
TEST(Fold, BoolEqAFalse)
{
    Simplifier s;
    FmlRef r = s.fold(IFF(EQ(NA, NB), F()));
    EXPECT_EQ(r->kind, FmlKind::Not);
}

// ── Same-subtree identity simplifications ─────────────────────────────────────

TEST(Fold, IteSameBranches)
{
    // ite(c, f, f) = f  (both branches identical pointer)
    Simplifier s;
    auto e = EQ(NA, NB);
    FmlRef r = s.fold(ITE(PR(NA), e, e));
    EXPECT_EQ(r.get(), e.get());
}

TEST(Fold, ImpliesSameSides)
{
    // p → p = true
    Simplifier s;
    auto e = EQ(NA, NB);
    EXPECT_EQ(s.fold(IMP(e, e))->kind, FmlKind::True);
}

TEST(Fold, XorSameSides)
{
    // p ⊕ p = false
    Simplifier s;
    auto e = EQ(NA, NB);
    EXPECT_EQ(s.fold(XOR(e, e))->kind, FmlKind::False);
}

TEST(Fold, BoolEqSameSides)
{
    // p ↔ p = true
    Simplifier s;
    auto e = EQ(NA, NB);
    EXPECT_EQ(s.fold(IFF(e, e))->kind, FmlKind::True);
}

// ── Nested folding ────────────────────────────────────────────────────────────

TEST(Fold, NestedAndOr)
{
    Simplifier s;
    // or(and(false, Eq), true) = true
    FmlRef r = s.fold(OR(AND(F(), EQ(NA,NB)), T()));
    EXPECT_EQ(r->kind, FmlKind::True);
}

TEST(Fold, DeepNested)
{
    Simplifier s;
    // and(not(false), or(true, Pred)) = true
    FmlRef r = s.fold(AND(NOT(F()), OR(T(), PR(NA))));
    EXPECT_EQ(r->kind, FmlKind::True);
}

// ── subst_and_fold ────────────────────────────────────────────────────────────

TEST(Subst, ForcedEqBecomesTrue)
{
    Simplifier s;
    auto e = EQ(NA, NB);
    FmlRef r = s.subst_and_fold(e, *e, true);
    EXPECT_EQ(r->kind, FmlKind::True);
}

TEST(Subst, ForcedEqBecomesFalse)
{
    Simplifier s;
    auto e = EQ(NA, NB);
    FmlRef r = s.subst_and_fold(e, *e, false);
    EXPECT_EQ(r->kind, FmlKind::False);
}

TEST(Subst, SymmetricEqForced)
{
    Simplifier s;
    // Eq(a,b) forced true → Eq(b,a) should also become True
    FmlRef r = s.subst_and_fold(EQ(NB, NA), *EQ(NA, NB), true);
    EXPECT_EQ(r->kind, FmlKind::True);
}

TEST(Subst, AndCollapsesWhenAtomForced)
{
    Simplifier s;
    // and(Eq(a,b), Pred(c)) where Eq(a,b) is forced true → Pred(c)
    auto p = PR(NC);
    FmlRef r = s.subst_and_fold(AND(EQ(NA,NB), p), *EQ(NA,NB), true);
    EXPECT_EQ(r.get(), p.get());
}

TEST(Subst, OrCollapsesWhenAtomForced)
{
    Simplifier s;
    // or(Pred(a), Eq(b,c)) where Pred(a) is forced true → True
    FmlRef r = s.subst_and_fold(OR(PR(NA), EQ(NB,NC)), *PR(NA), true);
    EXPECT_EQ(r->kind, FmlKind::True);
}

TEST(Subst, NegAtomInOr)
{
    Simplifier s;
    // or(Not(Eq(a,b)), Pred(c)) where Eq(a,b) is forced true → Pred(c)
    auto p = PR(NC);
    FmlRef r = s.subst_and_fold(OR(NOT(EQ(NA,NB)), p), *EQ(NA,NB), true);
    EXPECT_EQ(r.get(), p.get());
}

TEST(Subst, IteCondForced)
{
    Simplifier s;
    // ite(Pred(a), Eq(b,c), Pred(d)) where Pred(a) is forced true → Eq(b,c)
    auto e = EQ(NB, NC);
    FmlRef r = s.subst_and_fold(ITE(PR(NA), e, PR(ND)), *PR(NA), true);
    EXPECT_EQ(r.get(), e.get());
}

// ── run_pass: unit propagation ────────────────────────────────────────────────

TEST(RunPass, EqUnitPropagates)
{
    Simplifier s;
    // [Eq(a,b),  And(Eq(a,b), Pred(c))]
    // Eq(a,b) is unit → forced true → and(true, Pred(c)) = Pred(c)
    auto e = EQ(NA, NB);
    auto p = PR(NC);
    std::vector<FmlRef> assertions = {e, AND(e, p)};
    bool changed = s.run_pass(assertions);
    EXPECT_TRUE(changed);
    ASSERT_EQ(s.forced_atoms().size(), 1u);
    EXPECT_TRUE(s.forced_atoms()[0].positive);
    EXPECT_EQ(assertions[1].get(), p.get());
}

TEST(RunPass, NegEqUnitPropagates)
{
    Simplifier s;
    // [Not(Eq(a,b)),  Or(Eq(a,b), Pred(c))]
    // Not(Eq) → Eq forced false → or(false, Pred(c)) = Pred(c)
    auto e = EQ(NA, NB);
    auto p = PR(NC);
    std::vector<FmlRef> assertions = {NOT(e), OR(e, p)};
    s.run_pass(assertions);
    ASSERT_EQ(s.forced_atoms().size(), 1u);
    EXPECT_FALSE(s.forced_atoms()[0].positive);
    EXPECT_EQ(assertions[1].get(), p.get());
}

TEST(RunPass, PredUnitPropagates)
{
    Simplifier s;
    auto p = PR(NA);
    // [Pred(a), Or(Not(Pred(a)), Eq(b,c))]
    // Pred(a) forced true → Not(Pred(a))→False → Or(false, Eq) = Eq
    auto e = EQ(NB, NC);
    std::vector<FmlRef> assertions = {p, OR(NOT(p), e)};
    s.run_pass(assertions);
    ASSERT_EQ(s.forced_atoms().size(), 1u);
    EXPECT_EQ(assertions[1].get(), e.get());
}

TEST(RunPass, ConflictDetected)
{
    Simplifier s;
    // [Eq(a,b), Not(Eq(a,b))] → one becomes False
    std::vector<FmlRef> assertions = {EQ(NA,NB), NOT(EQ(NA,NB))};
    s.run_pass(assertions);
    bool has_false = false;
    for (auto& f : assertions)
        if (f->kind == FmlKind::False) has_false = true;
    EXPECT_TRUE(has_false);
}

// ── run (multi-pass) ──────────────────────────────────────────────────────────

TEST(Run, PropagatesAcrossIterations)
{
    Simplifier s;
    // [Pred(a), Implies(Pred(a), Eq(b,c)), And(Eq(b,c), Pred(d))]
    // Pass 1: Pred(a) unit → Implies(true, Eq(b,c))=Eq(b,c) forced
    //         → And(true, Pred(d)) = Pred(d)... but Eq(b,c) is a new unit in pass 2
    // Pass 2: Eq(b,c) unit → And(true, Pred(d)) already resolved → no change needed
    //         actually: And(Eq(b,c), Pred(d)) after pass 1 → Eq(b,c) is forced
    //         so And(true, Pred(d)) = Pred(d)
    auto pa = PR(NA);
    auto ebc = EQ(NB, NC);
    auto pd = PR(ND);
    std::vector<FmlRef> assertions = {pa, IMP(pa, ebc), AND(ebc, pd)};
    s.run(assertions, 10);
    // PA forced → IMP(PA,ebc) becomes ebc (new unit) → AND(ebc,pd) becomes pd
    // (new unit) → pd forced. All three atoms are discovered.
    EXPECT_EQ(s.forced_atoms().size(), 3u);
    // Every assertion should be trivially True after full propagation.
    for (auto& f : assertions)
        EXPECT_EQ(f->kind, FmlKind::True);
}

TEST(Run, StopsWhenStable)
{
    Simplifier s;
    // [Or(Pred(a), Pred(b))] — no unit, no change
    std::vector<FmlRef> assertions = {OR(PR(NA), PR(NB))};
    s.run(assertions, 10);
    EXPECT_TRUE(s.forced_atoms().empty());
    EXPECT_EQ(assertions[0]->kind, FmlKind::Or);
}

TEST(Run, TransitiveEqCollapses)
{
    Simplifier s;
    // [Eq(a,b), Eq(b,c), And(Eq(a,c), Pred(d))]
    // ab and bc are top-level units → forced.  UF has find(a)=find(c)=some root.
    // Eq(a,c) is NOT a top-level unit (it's inside And), so it survives Phase 3
    // substitution.  Phase 4 (UF normalization) collapses Eq(a,c) → True, and
    // fold(And(True, Pred(d))) = Pred(d).
    auto ab = EQ(NA, NB);
    auto bc = EQ(NB, NC);
    auto pd = PR(ND);
    std::vector<FmlRef> assertions = {ab, bc, AND(EQ(NA, NC), pd)};
    s.run_pass(assertions);
    EXPECT_GE(s.forced_atoms().size(), 2u);
    // And(Eq(a,c), Pred(d)) → And(True, Pred(d)) → Pred(d)
    EXPECT_EQ(assertions[2].get(), pd.get());
}

TEST(Run, TransitiveEqSymmetric)
{
    Simplifier s;
    // Eq(b,a) and Eq(b,c) forced.  Eq(a,c) inside compound → collapses to True.
    auto ba = EQ(NB, NA);
    auto bc = EQ(NB, NC);
    auto pd = PR(ND);
    std::vector<FmlRef> assertions = {ba, bc, AND(EQ(NA, NC), pd)};
    s.run_pass(assertions);
    EXPECT_EQ(assertions[2].get(), pd.get());
}

TEST(Run, ZeroPassesIsNoOp)
{
    Simplifier s;
    auto e = EQ(NA, NB);
    std::vector<FmlRef> assertions = {e, AND(e, PR(NC))};
    s.run(assertions, 0);
    EXPECT_TRUE(s.forced_atoms().empty());
    EXPECT_EQ(assertions[1]->kind, FmlKind::And);
}

// ── And/Or flattening ─────────────────────────────────────────────────────────

TEST(Fold, FlattenAndInAnd)
{
    // and(and(Eq(a,b), Pred(c)), Pred(d)) → and(Eq(a,b), Pred(c), Pred(d))
    Simplifier s;
    FmlRef inner = AND(EQ(NA,NB), PR(NC));
    FmlRef outer = AND(inner, PR(ND));
    FmlRef r = s.fold(outer);
    ASSERT_EQ(r->kind, FmlKind::And);
    EXPECT_EQ(r->children.size(), 3u);
    EXPECT_EQ(r->children[0]->kind, FmlKind::Eq);
    EXPECT_EQ(r->children[1]->kind, FmlKind::Pred);
    EXPECT_EQ(r->children[2]->kind, FmlKind::Pred);
}

TEST(Fold, FlattenOrInOr)
{
    // or(or(Eq(a,b), Pred(c)), Pred(d)) → or(Eq(a,b), Pred(c), Pred(d))
    Simplifier s;
    FmlRef inner = OR(EQ(NA,NB), PR(NC));
    FmlRef outer = OR(inner, PR(ND));
    FmlRef r = s.fold(outer);
    ASSERT_EQ(r->kind, FmlKind::Or);
    EXPECT_EQ(r->children.size(), 3u);
}

TEST(Fold, FlattenAndNotCrossOr)
{
    // and(or(Eq(a,b), Pred(c)), Pred(d)) — Or inside And: should NOT flatten
    Simplifier s;
    FmlRef inner = OR(EQ(NA,NB), PR(NC));
    FmlRef outer = AND(inner, PR(ND));
    FmlRef r = s.fold(outer);
    ASSERT_EQ(r->kind, FmlKind::And);
    EXPECT_EQ(r->children.size(), 2u);  // not flattened across kinds
}

TEST(Fold, FlattenDeepAnd)
{
    // and(and(and(Eq(a,b), Pred(c)), Pred(d)), Pred(e)) → and of 4 children
    Simplifier s;
    FmlRef eq  = EQ(NA, NB);
    FmlRef pc  = PR(NC);
    FmlRef pd  = PR(ND);
    FmlRef pe  = PR(10u + 4u);  // arbitrary NodeId
    FmlRef r   = s.fold(AND(AND(AND(eq, pc), pd), pe));
    ASSERT_EQ(r->kind, FmlKind::And);
    EXPECT_EQ(r->children.size(), 4u);
}

TEST(Fold, FlattenDisabledKeepsNested)
{
    // With flatten=false, and(and(a,b),c) stays nested.
    Simplifier s;
    s.set_flatten(false);
    FmlRef eq  = EQ(NA, NB);
    FmlRef pc  = PR(NC);
    FmlRef outer = AND(AND(eq, pc), PR(ND));
    FmlRef r = s.fold(outer);
    // No change: pointer identity holds
    EXPECT_EQ(r.get(), outer.get());
}

TEST(Fold, FlattenAndWithTrueChild)
{
    // and(and(Eq(a,b), true), Pred(c)) → and(Eq(a,b), Pred(c))
    // Flattening + True-dropping happen together.
    Simplifier s;
    FmlRef r = s.fold(AND(AND(EQ(NA,NB), T()), PR(NC)));
    ASSERT_EQ(r->kind, FmlKind::And);
    EXPECT_EQ(r->children.size(), 2u);
    EXPECT_EQ(r->children[0]->kind, FmlKind::Eq);
    EXPECT_EQ(r->children[1]->kind, FmlKind::Pred);
}
