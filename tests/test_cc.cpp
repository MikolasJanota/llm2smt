#include <gtest/gtest.h>
#include "core/node_manager.h"
#include "theories/euf/cc.h"

using namespace llm2smt;

// Helper: create a CC with n fresh constant nodes (ids 1..n)
struct CCFixture {
    NodeManager nm;
    CC cc;

    // Create a fresh 0-arity constant, register in CC, return NodeId
    NodeId make_const(const std::string& name) {
        SymbolId sym = nm.declare_symbol(name, 0);
        NodeId n = nm.mk_const(sym);
        cc.add_node(n);
        return n;
    }
};

TEST(CC, BasicMerge) {
    CCFixture f;
    NodeId a = f.make_const("a");
    NodeId b = f.make_const("b");
    NodeId c = f.make_const("c");

    EXPECT_FALSE(f.cc.are_congruent(a, b));
    EXPECT_FALSE(f.cc.are_congruent(b, c));

    f.cc.add_equation(a, b);
    EXPECT_TRUE(f.cc.are_congruent(a, b));
    EXPECT_FALSE(f.cc.are_congruent(a, c));

    f.cc.add_equation(b, c);
    EXPECT_TRUE(f.cc.are_congruent(a, c));
}

TEST(CC, Reflexivity) {
    CCFixture f;
    NodeId a = f.make_const("a");
    EXPECT_TRUE(f.cc.are_congruent(a, a));
}

TEST(CC, Symmetry) {
    CCFixture f;
    NodeId a = f.make_const("a");
    NodeId b = f.make_const("b");
    f.cc.add_equation(a, b);
    EXPECT_TRUE(f.cc.are_congruent(a, b));
    EXPECT_TRUE(f.cc.are_congruent(b, a));
}

TEST(CC, Transitivity) {
    CCFixture f;
    NodeId a = f.make_const("a");
    NodeId b = f.make_const("b");
    NodeId c = f.make_const("c");

    f.cc.add_equation(a, b);
    f.cc.add_equation(b, c);
    EXPECT_TRUE(f.cc.are_congruent(a, c));
}

TEST(CC, CongruenceClosure) {
    // f(a) = f(b) follows from a = b
    CCFixture f;
    // Nodes: a, b, fa (result of f@a), fb (result of f@b), fa_flat, fb_flat
    NodeId a    = f.make_const("a");
    NodeId b    = f.make_const("b");
    NodeId fa   = f.make_const("fa");   // represents f(a)
    NodeId fb   = f.make_const("fb");   // represents f(b)
    NodeId fsym = f.make_const("f_sym");  // symbol for f

    // Add app equations: fa = fsym(a), fb = fsym(b)
    f.cc.add_app_equation(fa, fsym, a);
    f.cc.add_app_equation(fb, fsym, b);

    EXPECT_FALSE(f.cc.are_congruent(fa, fb));

    // Now assert a = b
    f.cc.add_equation(a, b);

    // Congruence closure should derive f(a) = f(b)
    EXPECT_TRUE(f.cc.are_congruent(fa, fb));
}

TEST(CC, ExplainAtomicEquality) {
    CCFixture f;
    NodeId a = f.make_const("a");
    NodeId b = f.make_const("b");

    EqId eq = f.cc.add_equation(a, b);
    ASSERT_TRUE(f.cc.are_congruent(a, b));

    auto expl = f.cc.explain(a, b);
    EXPECT_EQ(expl.size(), 1u);
    EXPECT_EQ(expl[0], eq);
}

TEST(CC, ExplainTransitive) {
    CCFixture f;
    NodeId a = f.make_const("a");
    NodeId b = f.make_const("b");
    NodeId c = f.make_const("c");

    EqId eq1 = f.cc.add_equation(a, b);
    EqId eq2 = f.cc.add_equation(b, c);

    ASSERT_TRUE(f.cc.are_congruent(a, c));
    auto expl = f.cc.explain(a, c);

    // Should contain both eq1 and eq2
    EXPECT_EQ(expl.size(), 2u);
    EXPECT_TRUE(std::find(expl.begin(), expl.end(), eq1) != expl.end());
    EXPECT_TRUE(std::find(expl.begin(), expl.end(), eq2) != expl.end());
}

TEST(CC, Backtracking) {
    CCFixture f;
    NodeId a = f.make_const("a");
    NodeId b = f.make_const("b");

    EXPECT_FALSE(f.cc.are_congruent(a, b));

    f.cc.push_level();
    f.cc.add_equation(a, b);
    EXPECT_TRUE(f.cc.are_congruent(a, b));

    f.cc.pop_level(0);
    EXPECT_FALSE(f.cc.are_congruent(a, b));
}

TEST(CC, BacktrackingNested) {
    CCFixture f;
    NodeId a = f.make_const("a");
    NodeId b = f.make_const("b");
    NodeId c = f.make_const("c");

    f.cc.push_level();           // level 1
    f.cc.add_equation(a, b);

    f.cc.push_level();           // level 2
    f.cc.add_equation(b, c);

    EXPECT_TRUE(f.cc.are_congruent(a, c));

    f.cc.pop_level(1);           // pop level 2
    EXPECT_TRUE(f.cc.are_congruent(a, b));
    EXPECT_FALSE(f.cc.are_congruent(a, c));
    EXPECT_FALSE(f.cc.are_congruent(b, c));

    f.cc.pop_level(0);           // pop level 1
    EXPECT_FALSE(f.cc.are_congruent(a, b));
}

TEST(CC, ExplainCongruence) {
    // given a=b, fa=f(a), fb=f(b) → fa≡fb
    // Full explanation must include both app equations AND the atomic a=b.
    CCFixture f;
    NodeId a    = f.make_const("a");
    NodeId b    = f.make_const("b");
    NodeId fa   = f.make_const("fa");
    NodeId fb   = f.make_const("fb");
    NodeId fsym = f.make_const("f_sym");

    EqId app_eq1 = f.cc.add_app_equation(fa, fsym, a);
    EqId app_eq2 = f.cc.add_app_equation(fb, fsym, b);
    EqId ab_eq   = f.cc.add_equation(a, b);

    ASSERT_TRUE(f.cc.are_congruent(fa, fb));

    auto expl = f.cc.explain(fa, fb);
    // Must contain both app equations and the atomic justification
    EXPECT_EQ(expl.size(), 3u);
    EXPECT_TRUE(std::find(expl.begin(), expl.end(), app_eq1) != expl.end());
    EXPECT_TRUE(std::find(expl.begin(), expl.end(), app_eq2) != expl.end());
    EXPECT_TRUE(std::find(expl.begin(), expl.end(), ab_eq)   != expl.end());
}

// ── New tests ──────────────────────────────────────────────────────────────

// BUG-1 regression: after backtrack, merging the reverted node must work correctly.
// Previously class_list_[rb].clear() was not undone, leaving rb with an empty
// class list so no repr updates happened in the next merge.
TEST(CC, BacktrackAndReMerge) {
    CCFixture f;
    NodeId a = f.make_const("a");
    NodeId b = f.make_const("b");
    NodeId c = f.make_const("c");

    f.cc.push_level();
    f.cc.add_equation(a, b);
    EXPECT_TRUE(f.cc.are_congruent(a, b));
    f.cc.pop_level(0);
    EXPECT_FALSE(f.cc.are_congruent(a, b));

    // After backtrack b's class list must be restored to {b}.
    // Merging b=c must make them congruent.
    f.cc.push_level();
    f.cc.add_equation(b, c);
    EXPECT_TRUE(f.cc.are_congruent(b, c));
    // And b's representative should now also cover c
    EXPECT_EQ(f.cc.find(b), f.cc.find(c));
    f.cc.pop_level(0);
    EXPECT_FALSE(f.cc.are_congruent(b, c));
}

// ExplainLongChain: a=b, b=c, c=d — tests explain over a 3-step proof path.
TEST(CC, ExplainLongChain) {
    CCFixture f;
    NodeId a = f.make_const("a");
    NodeId b = f.make_const("b");
    NodeId c = f.make_const("c");
    NodeId d = f.make_const("d");

    EqId e1 = f.cc.add_equation(a, b);
    EqId e2 = f.cc.add_equation(b, c);
    EqId e3 = f.cc.add_equation(c, d);

    ASSERT_TRUE(f.cc.are_congruent(a, d));
    auto expl = f.cc.explain(a, d);

    EXPECT_EQ(expl.size(), 3u);
    EXPECT_TRUE(std::find(expl.begin(), expl.end(), e1) != expl.end());
    EXPECT_TRUE(std::find(expl.begin(), expl.end(), e2) != expl.end());
    EXPECT_TRUE(std::find(expl.begin(), expl.end(), e3) != expl.end());
}

// CongruenceViaLookupHit: when the second add_app_equation finds a matching
// lookup entry immediately (args already congruent at time of insertion).
TEST(CC, CongruenceViaLookupHit) {
    CCFixture f;
    NodeId a    = f.make_const("a");
    NodeId b    = f.make_const("b");
    NodeId fa   = f.make_const("fa");
    NodeId fb   = f.make_const("fb");
    NodeId fsym = f.make_const("f_sym");

    // First merge a=b so reprs match, then add both app equations.
    // The second add_app_equation hits the lookup immediately.
    f.cc.add_equation(a, b);
    f.cc.add_app_equation(fa, fsym, a);
    // repr(a) == repr(b) now, so adding fb=fsym(b) hits lookup[(fsym,repr(a))].
    f.cc.add_app_equation(fb, fsym, b);

    EXPECT_TRUE(f.cc.are_congruent(fa, fb));
}

// BacktrackCongruence: congruence derived at level 1 must vanish after pop.
TEST(CC, BacktrackCongruence) {
    CCFixture f;
    NodeId a    = f.make_const("a");
    NodeId b    = f.make_const("b");
    NodeId fa   = f.make_const("fa");
    NodeId fb   = f.make_const("fb");
    NodeId fsym = f.make_const("f_sym");

    // App equations are permanent (level 0)
    f.cc.add_app_equation(fa, fsym, a);
    f.cc.add_app_equation(fb, fsym, b);

    EXPECT_FALSE(f.cc.are_congruent(fa, fb));

    f.cc.push_level();          // level 1
    f.cc.add_equation(a, b);   // triggers congruence fa≡fb
    EXPECT_TRUE(f.cc.are_congruent(fa, fb));

    f.cc.pop_level(0);
    EXPECT_FALSE(f.cc.are_congruent(a,  b));
    EXPECT_FALSE(f.cc.are_congruent(fa, fb));
}

// MultiLevelPop: push three levels, pop directly to 0 in one call.
TEST(CC, MultiLevelPop) {
    CCFixture f;
    NodeId a = f.make_const("a");
    NodeId b = f.make_const("b");
    NodeId c = f.make_const("c");
    NodeId d = f.make_const("d");

    f.cc.push_level();  f.cc.add_equation(a, b);
    f.cc.push_level();  f.cc.add_equation(b, c);
    f.cc.push_level();  f.cc.add_equation(c, d);
    EXPECT_TRUE(f.cc.are_congruent(a, d));

    f.cc.pop_level(0);  // skip back 3 levels at once
    EXPECT_FALSE(f.cc.are_congruent(a, b));
    EXPECT_FALSE(f.cc.are_congruent(b, c));
    EXPECT_FALSE(f.cc.are_congruent(c, d));
}
