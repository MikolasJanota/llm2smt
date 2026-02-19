#include <gtest/gtest.h>
#include "core/node_manager.h"
#include "theories/euf/euf_solver.h"
#include "theories/euf/flattener.h"

using namespace llm2smt;

// Helper: create NM + EufSolver
struct EufFixture {
    NodeManager nm;
    EufSolver   euf{nm};

    NodeId make_const(const std::string& name) {
        SymbolId sym = nm.declare_symbol(name, 0);
        return nm.mk_const(sym);
    }

    // Make an application node (not yet flat)
    NodeId make_app(const std::string& fname, uint32_t arity,
                    std::vector<NodeId> args) {
        SymbolId sym = nm.declare_symbol(fname, arity);
        return nm.mk_app(sym, std::span<const NodeId>(args));
    }
};

TEST(EufSolver, RegisterEquality) {
    EufFixture f;
    NodeId a = f.make_const("a");
    NodeId b = f.make_const("b");

    int lit = f.euf.register_equality(a, b);
    EXPECT_GT(lit, 0);

    // Idempotent
    int lit2 = f.euf.register_equality(a, b);
    EXPECT_EQ(lit, lit2);

    // Symmetric
    int lit3 = f.euf.register_equality(b, a);
    EXPECT_EQ(lit, lit3);
}

TEST(EufSolver, EqualityTriggersCC) {
    EufFixture f;
    NodeId a = f.make_const("a");
    NodeId b = f.make_const("b");

    int lit = f.euf.register_equality(a, b);

    // Before assignment, CC doesn't know
    // (We haven't flattened yet so we can't check directly)

    // Assign the equality literal
    f.euf.notify_assignment(lit, false);

    // Now flatten both constants and check CC
    Flattener flat(f.nm, f.euf.cc());
    NodeId fa = flat.flatten_and_register(a);
    NodeId fb = flat.flatten_and_register(b);
    EXPECT_TRUE(f.euf.cc().are_congruent(fa, fb));
}

TEST(EufSolver, DisequalityConflict) {
    // a=b and a≠b → conflict
    EufFixture f;
    NodeId a = f.make_const("a");
    NodeId b = f.make_const("b");

    int lit = f.euf.register_equality(a, b);

    f.euf.notify_assignment(lit, false);   // assert a=b
    f.euf.notify_assignment(-lit, false);  // assert a≠b

    std::vector<int> model = {lit, -lit};
    bool ok = f.euf.cb_check_found_model(model);
    EXPECT_FALSE(ok) << "Should detect conflict a=b ∧ a≠b";

    bool forgettable = false;
    EXPECT_TRUE(f.euf.cb_has_external_clause(forgettable));
}

TEST(EufSolver, CongruenceConflict) {
    // a=b and f(a)≠f(b) → conflict via congruence
    EufFixture f;
    NodeId a    = f.make_const("a");
    NodeId b    = f.make_const("b");
    NodeId fa   = f.make_app("f", 1, {a});
    NodeId fb   = f.make_app("f", 1, {b});

    int lit_ab   = f.euf.register_equality(a, b);
    int lit_fafb = f.euf.register_equality(fa, fb);

    // Assert a=b and f(a)≠f(b)
    f.euf.notify_assignment(lit_ab, false);
    f.euf.notify_assignment(-lit_fafb, false);

    std::vector<int> model = {lit_ab, -lit_fafb};
    bool ok = f.euf.cb_check_found_model(model);
    EXPECT_FALSE(ok) << "Should detect congruence conflict";
}

// BUG-9 regression: the conflict clause for a congruence conflict must contain
// the negation of the triggering atomic equality, not just the disequality literal.
TEST(EufSolver, ConflictClauseContainsEqualityJustification) {
    EufFixture f;
    NodeId a  = f.make_const("a");
    NodeId b  = f.make_const("b");
    NodeId fa = f.make_app("f", 1, {a});
    NodeId fb = f.make_app("f", 1, {b});

    int lit_ab   = f.euf.register_equality(a, b);
    int lit_fafb = f.euf.register_equality(fa, fb);

    f.euf.notify_assignment(lit_ab,   false);   // a = b
    f.euf.notify_assignment(-lit_fafb, false);  // f(a) ≠ f(b)

    std::vector<int> model = {lit_ab, -lit_fafb};
    ASSERT_FALSE(f.euf.cb_check_found_model(model));

    bool forgettable = false;
    ASSERT_TRUE(f.euf.cb_has_external_clause(forgettable));

    // Collect the conflict clause
    std::vector<int> clause;
    int lit;
    while ((lit = f.euf.cb_add_external_clause_lit()) != 0)
        clause.push_back(lit);

    // Clause must contain lit_fafb (negation of the disequality) ...
    EXPECT_TRUE(std::find(clause.begin(), clause.end(), lit_fafb) != clause.end())
        << "clause missing lit_fafb (negated disequality)";
    // ... and -lit_ab (negation of the equality that caused the congruence).
    EXPECT_TRUE(std::find(clause.begin(), clause.end(), -lit_ab) != clause.end())
        << "clause missing -lit_ab (equality justification)";
    // Total: at least two literals
    EXPECT_GE(clause.size(), 2u);
}

// After backtrack, new assignments in the same or higher level must be handled
// correctly — in particular, the CC state must be clean for new merges.
TEST(EufSolver, PostBacktrackNewAssignment) {
    EufFixture f;
    NodeId a = f.make_const("a");
    NodeId b = f.make_const("b");
    NodeId c = f.make_const("c");

    int lit_ab = f.euf.register_equality(a, b);
    int lit_ac = f.euf.register_equality(a, c);

    // Level 1: assert a=b
    f.euf.notify_new_decision_level();
    f.euf.notify_assignment(lit_ab, false);
    {
        Flattener flat(f.nm, f.euf.cc());
        EXPECT_TRUE(f.euf.cc().are_congruent(
            flat.flatten_and_register(a), flat.flatten_and_register(b)));
    }

    // Backtrack
    f.euf.notify_backtrack(0);

    // Level 1 again: assert a=c instead
    f.euf.notify_new_decision_level();
    f.euf.notify_assignment(lit_ac, false);
    {
        Flattener flat(f.nm, f.euf.cc());
        NodeId fa = flat.flatten_and_register(a);
        NodeId fb = flat.flatten_and_register(b);
        NodeId fc = flat.flatten_and_register(c);
        EXPECT_FALSE(f.euf.cc().are_congruent(fa, fb))
            << "a and b should be separate after backtrack";
        EXPECT_TRUE(f.euf.cc().are_congruent(fa, fc))
            << "a and c should be congruent";
    }
}

TEST(EufSolver, BacktrackRestoresState) {
    EufFixture f;
    NodeId a = f.make_const("a");
    NodeId b = f.make_const("b");

    int lit = f.euf.register_equality(a, b);

    f.euf.notify_new_decision_level();
    f.euf.notify_assignment(lit, false);

    {
        Flattener flat(f.nm, f.euf.cc());
        NodeId fa = flat.flatten_and_register(a);
        NodeId fb = flat.flatten_and_register(b);
        EXPECT_TRUE(f.euf.cc().are_congruent(fa, fb));
    }

    f.euf.notify_backtrack(0);

    {
        // After backtrack, a and b should no longer be congruent
        // (We need a fresh flattener to avoid stale cache)
        // Actually the CC is reset; the Flattener cache might still hold
        // registered flat nodes that are no longer congruent.
        // The CC should report them as separate after backtrack.
        // But the flattener cache maps term→flat_const which persist.
        // In a real implementation, flattener nodes are added lazily.
        // Here we just check the CC state directly via the euf's flattener.
        // Since we used a local flattener above, those nodes were registered
        // in the CC. After backtrack the CC state is restored.
        // The constants themselves (a, b → flat a, flat b) are still separate classes.
        // Note: add_node is idempotent but the class-list starts with {node} if registered.
        // After pop_level, the equality is undone.
        // Use the euf's internal flattener to check:
        // (We know the flat nodes from the previous registration.)
        // Let's just check that the CC no longer says they're congruent
        // by re-examining via a fresh flattener:
        Flattener flat2(f.nm, f.euf.cc());
        NodeId fa2 = flat2.flatten_and_register(a);
        NodeId fb2 = flat2.flatten_and_register(b);
        // After backtrack, they should be separate
        EXPECT_FALSE(f.euf.cc().are_congruent(fa2, fb2));
    }
}
