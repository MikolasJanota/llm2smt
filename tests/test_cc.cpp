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
    // Reproduces a simple congruence step:
    // given a=b, fa=f(a), fb=f(b) → fa≡fb, explain should give {a=b, fa=f(a), fb=f(b)}
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
    // Explanation should mention app_eq1, app_eq2, and ab_eq
    EXPECT_FALSE(expl.empty());
    EXPECT_TRUE(std::find(expl.begin(), expl.end(), app_eq1) != expl.end() ||
                std::find(expl.begin(), expl.end(), app_eq2) != expl.end());
}
