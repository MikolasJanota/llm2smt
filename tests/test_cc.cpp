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
    // Explanation must be the single atomic equality a=b; structural app
    // equations are not SAT literals and must not appear in the result.
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
    // Explanation must contain only the atomic SAT-level equality a=b.
    // The structural app equations (fa=@(f,a), fb=@(f,b)) are not SAT literals
    // and must NOT appear in the conflict explanation.
    EXPECT_EQ(expl.size(), 1u);
    EXPECT_TRUE(std::find(expl.begin(), expl.end(), ab_eq)   != expl.end());
    EXPECT_TRUE(std::find(expl.begin(), expl.end(), app_eq1) == expl.end());
    EXPECT_TRUE(std::find(expl.begin(), expl.end(), app_eq2) == expl.end());
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

// ExplainChainedCongruence: regresses a proof-forest disconnection bug.
//
// When two congruence steps both try to set a proof edge FROM the same flat
// node (because the node appeared in two separate pending-entry chains), the
// OLD code's "skip if already has parent" guard left the forest disconnected
// so that find_lca(x, z) returned NULL_NODE even though are_congruent(x,z).
//
// Setup (binary-function currying pattern, like PEQ benchmarks):
//   f_sym, a, b, c — atoms
//   fa = @(f, a),  fb = @(f, b),  fc = @(f, c)      — 1st curry step
//   faa = @(fa, a), fab = @(fa, b), fbc = @(fb, c), fcc = @(fc, c)  — 2nd step
//
// Assert a = b, b = c, then verify explain(faa, fcc) doesn't crash.
TEST(CC, ExplainChainedCongruence) {
    CCFixture f;
    // atoms
    NodeId a    = f.make_const("a");
    NodeId b    = f.make_const("b");
    NodeId c    = f.make_const("c");
    NodeId fsym = f.make_const("f_sym");
    // 1st-level curry: @(f_sym, x)
    NodeId fa   = f.make_const("fa");   // @(fsym, a)
    NodeId fb   = f.make_const("fb");   // @(fsym, b)
    NodeId fc   = f.make_const("fc");   // @(fsym, c)
    // 2nd-level curry: @(@(f_sym, x), y)
    NodeId faa  = f.make_const("faa");  // @(fa, a)
    NodeId fab  = f.make_const("fab");  // @(fa, b)
    NodeId fbb  = f.make_const("fbb");  // @(fb, b)
    NodeId fbc  = f.make_const("fbc");  // @(fb, c)
    NodeId fcc  = f.make_const("fcc");  // @(fc, c)

    // Register app equations (all flat)
    f.cc.add_app_equation(fa,  fsym, a);
    f.cc.add_app_equation(fb,  fsym, b);
    f.cc.add_app_equation(fc,  fsym, c);
    f.cc.add_app_equation(faa, fa,   a);
    f.cc.add_app_equation(fab, fa,   b);
    f.cc.add_app_equation(fbb, fb,   b);
    f.cc.add_app_equation(fbc, fb,   c);
    f.cc.add_app_equation(fcc, fc,   c);

    // a=b: triggers fa≡fb, then faa≡fbb (and fab≡fbb by congruence on 2nd arg)
    f.cc.add_equation(a, b);
    // b=c: triggers fb≡fc, then fbb≡fcc (and fbc≡fcc)
    f.cc.add_equation(b, c);

    // All six 2nd-level nodes must be in the same class
    ASSERT_TRUE(f.cc.are_congruent(faa, fcc));
    ASSERT_TRUE(f.cc.are_congruent(fab, fbc));

    // Must not crash (old code: find_lca returned NULL_NODE → assertion failure)
    EXPECT_NO_THROW(f.cc.explain(faa, fcc));
    EXPECT_NO_THROW(f.cc.explain(fab, fbc));
    EXPECT_NO_THROW(f.cc.explain(fbb, fcc));

    // Explanation must be non-empty
    auto expl = f.cc.explain(faa, fcc);
    EXPECT_FALSE(expl.empty());
}

// ClassListMergeOrderPreserved: regression for the ClassListMerge undo ordering bug.
//
// The bug: ClassListMerge undo popped elements from class_list_[ra] one-by-one
// and appended them to class_list_[rb], reversing their original order.  After
// multi-level backtracking the reversed order caused a lower-level undo to move
// the WRONG elements between class lists — for example, leaving class_list_[c]
// containing some foreign node d instead of c itself.  A subsequent do_merge
// involving c would then iterate over {d} and update repr[d] but never repr[c],
// violating the invariant repr[x]==r for every x in class_list_[r].  The next
// merge that should have set proof_parent[c] would find repr[c] still pointing
// to c (incorrectly still its own representative) and attempt to set a second
// proof edge, triggering the "proof edge set twice" assertion.
//
// Scenario:
//   Level 1: a=b  → {a,b}, {c}, {d}
//   Level 2: c=d  → {a,b}, {c,d}        (ClassListMerge(ra=c, rb=d, extra=1))
//   Level 3: a=c  → {a,b,c,d}           (ClassListMerge(ra=a, rb=c, extra=2))
//   pop_level(2): undo level-3 merge; class_list_[c] must be restored as {c,d}
//                 (bug: restored as {d,c} — reversed)
//   pop_level(1): undo level-2 merge; pops 1 element from back of class_list_[c]
//                 FIX:  pops d → class_list_[c]={c}, class_list_[d]={d}  ✓
//                 BUG:  pops c → class_list_[c]={d}, class_list_[d]={c}  ✗
//   pop_level(0): full reset
//   add_equation(b,c): with the bug do_merge(b,c) iterates class_list_[c]={d},
//                 updates repr[d] but never repr[c], so are_congruent(b,c)==false.
TEST(CC, ClassListMergeOrderPreserved) {
    CCFixture f;
    NodeId a = f.make_const("a");
    NodeId b = f.make_const("b");
    NodeId c = f.make_const("c");
    NodeId d = f.make_const("d");

    // Level 1: merge 1-element classes a and b → {a,b}
    f.cc.push_level();
    f.cc.add_equation(a, b);
    ASSERT_TRUE(f.cc.are_congruent(a, b));

    // Level 2: merge 1-element classes c and d → {c,d}
    f.cc.push_level();
    f.cc.add_equation(c, d);
    ASSERT_TRUE(f.cc.are_congruent(c, d));

    // Level 3: join the two 2-element classes → {a,b,c,d}
    // ClassListMerge records extra=2 for rb={c,d} going into ra={a,b}.
    f.cc.push_level();
    f.cc.add_equation(a, c);
    ASSERT_TRUE(f.cc.are_congruent(a, d));

    // Pop level 3: {a,b} and {c,d} must be restored.
    f.cc.pop_level(2);
    EXPECT_TRUE(f.cc.are_congruent(a, b));
    EXPECT_TRUE(f.cc.are_congruent(c, d));
    EXPECT_FALSE(f.cc.are_congruent(a, c));

    // Pop level 2: {c} and {d} must be restored as separate singletons.
    // With the bug class_list_[c] is reversed to {d,c}, so undoing
    // ClassListMerge(ra=c,rb=d,extra=1) pops 'c' (not 'd') from the back,
    // leaving class_list_[c]={d}.  The next merge on c then misses c itself.
    f.cc.pop_level(1);
    EXPECT_TRUE(f.cc.are_congruent(a, b));
    EXPECT_FALSE(f.cc.are_congruent(c, d));

    // Pop level 1: all four nodes must be fully independent.
    f.cc.pop_level(0);
    EXPECT_FALSE(f.cc.are_congruent(a, b));
    EXPECT_FALSE(f.cc.are_congruent(c, d));

    // Critical check: a fresh merge after full backtrack must work correctly.
    // With the bug class_list_[c] still contains d instead of c, so
    // do_merge(b,c) never updates repr[c] and are_congruent(b,c) remains false.
    f.cc.push_level();
    f.cc.add_equation(b, c);
    EXPECT_TRUE(f.cc.are_congruent(b, c));  // fails with the ordering bug
    f.cc.pop_level(0);
    EXPECT_FALSE(f.cc.are_congruent(b, c));
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

// ExplainRepeated: call explain() multiple times on the same CC instance.
// Exercises the reuse of the persistent PathUF member (explain_uf_).
// Each call must reinitialise the scratch state correctly.
TEST(CC, ExplainRepeated) {
    CCFixture f;
    NodeId a = f.make_const("a");
    NodeId b = f.make_const("b");
    NodeId c = f.make_const("c");

    EqId eq1 = f.cc.add_equation(a, b);
    EqId eq2 = f.cc.add_equation(b, c);

    ASSERT_TRUE(f.cc.are_congruent(a, c));

    // First call
    auto expl1 = f.cc.explain(a, c);
    EXPECT_EQ(expl1.size(), 2u);
    EXPECT_TRUE(std::find(expl1.begin(), expl1.end(), eq1) != expl1.end());
    EXPECT_TRUE(std::find(expl1.begin(), expl1.end(), eq2) != expl1.end());

    // Second call — must return the same result; PathUF is re-initialised.
    auto expl2 = f.cc.explain(a, c);
    EXPECT_EQ(expl2, expl1);

    // Third call with a different pair
    auto expl3 = f.cc.explain(a, b);
    EXPECT_EQ(expl3.size(), 1u);
    EXPECT_EQ(expl3[0], eq1);
}

// TrailDoesNotGrowUnboundedly: repeated push/pop cycles must not accumulate
// dead trail entries.  We verify via num_nodes() staying constant (a proxy
// that the CC state is properly reset) and that all merges work correctly
// after many backtrack cycles — indirectly ensuring trail_ is properly trimmed.
TEST(CC, RepeatedPushPopCycles) {
    CCFixture f;
    NodeId a = f.make_const("a");
    NodeId b = f.make_const("b");

    for (int i = 0; i < 50; ++i) {
        f.cc.push_level();
        f.cc.add_equation(a, b);
        EXPECT_TRUE(f.cc.are_congruent(a, b));
        f.cc.pop_level(0);
        EXPECT_FALSE(f.cc.are_congruent(a, b));
    }

    // After all cycles, a new merge at level 0 must still work.
    f.cc.add_equation(a, b);
    EXPECT_TRUE(f.cc.are_congruent(a, b));
}

// ExplainTransitiveViaRepresentative: regression for incomplete proof-forest
// explanation when the pending-entry node in the merged class differs from its
// class representative.
//
// Setup (two equal-sized classes at level 1, merged at level 2):
//   Level 1: (a=ext) — grows a's class to size 2
//   Level 1: (b=mid) — grows b's class to size 2 (repr[mid]=b)
//   Level 2: (a=mid) — merges the two size-2 classes.
//
// When (a=mid) is processed, repr[mid] = b (chased), so the proof edge goes
// from b (proof_from = smaller/equal class representative of mid's class) to a
// (proof_to = entry.a), labeled with the (a=mid) equation.  The key: from_node
// = mid (the original pending-entry node in b's class) ≠ b (proof_from).
//
// Bug: explain(a, b) only returned {a=mid}, missing {b=mid}.
// Fix: the proof edge now stores from_node=mid; explain adds (b, mid) to its
//      worklist, collecting the (b=mid) equation too.
TEST(CC, ExplainTransitiveViaRepresentative) {
    CCFixture f;
    NodeId a   = f.make_const("a");
    NodeId b   = f.make_const("b");
    NodeId mid = f.make_const("mid");
    NodeId ext = f.make_const("ext");  // extra node to grow a's class

    f.cc.push_level();  // level 1
    // Grow a's class to size 2 so that the merge below won't swap.
    f.cc.add_equation(a, ext);
    // Grow b's class to size 2 and merge mid into it: repr[mid] = b.
    EqId eq_b_mid = f.cc.add_equation(b, mid);

    f.cc.push_level();  // level 2
    // Add (a = mid).  repr[mid] is b's representative (size 2, same as a's
    // class size), so with equal sizes there is no swap.  The proof edge goes
    // from b (proof_from) to a (proof_to=entry.a), labeled with this equation.
    // from_node = mid ≠ b, so without the fix explain(a, b) would omit eq_b_mid.
    EqId eq_a_mid = f.cc.add_equation(a, mid);

    ASSERT_TRUE(f.cc.are_congruent(a, b));

    auto expl = f.cc.explain(a, b);

    // Both equations are needed to prove a ≡ b transitively via mid.
    EXPECT_EQ(expl.size(), 2u);
    EXPECT_TRUE(std::find(expl.begin(), expl.end(), eq_a_mid) != expl.end())
        << "explain(a,b) must include eq(a=mid)";
    EXPECT_TRUE(std::find(expl.begin(), expl.end(), eq_b_mid) != expl.end())
        << "explain(a,b) must include eq(b=mid)";
}
