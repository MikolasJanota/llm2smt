#include "theories/lra/lra_solver.h"

#include <gtest/gtest.h>

using namespace llm2smt::lra;

TEST(DeltaRational, OrdersPositiveInfinitesimal) {
    DeltaRational five(Rational(5));
    DeltaRational five_plus_delta(Rational(5), Rational(1));
    DeltaRational six(Rational(6));

    EXPECT_LT(five, five_plus_delta);
    EXPECT_LT(five_plus_delta, six);
    EXPECT_EQ((five_plus_delta - five), DeltaRational(Rational(0), Rational(1)));
}

TEST(Rational, FastPathsPreserveCanonicalForm) {
    Rational zero(0);
    zero += Rational(BigInt(2), BigInt(4));
    EXPECT_EQ(zero, Rational(BigInt(1), BigInt(2)));
    EXPECT_EQ(zero.den, BigInt(2));

    Rational ints(3);
    ints += Rational(4);
    EXPECT_EQ(ints, Rational(7));
    EXPECT_EQ(ints.den, BigInt(1));

    Rational product(BigInt(2), BigInt(3));
    product *= Rational(0);
    EXPECT_EQ(product, Rational(0));
    EXPECT_EQ(product.den, BigInt(1));

    Rational neg(BigInt(3), BigInt(5));
    neg *= Rational(-1);
    EXPECT_EQ(neg, Rational(BigInt(-3), BigInt(5)));
    EXPECT_EQ(neg.den, BigInt(5));

    Rational quotient(BigInt(6), BigInt(7));
    quotient /= Rational(-1);
    EXPECT_EQ(quotient, Rational(BigInt(-6), BigInt(7)));
    EXPECT_EQ(quotient.den, BigInt(7));

    Rational half(BigInt(1), BigInt(2));
    Rational neg_half = -half;
    EXPECT_EQ(neg_half, Rational(BigInt(-1), BigInt(2)));
    EXPECT_EQ(neg_half.den, BigInt(2));

    Rational subtract(BigInt(7), BigInt(5));
    subtract -= Rational(BigInt(2), BigInt(5));
    EXPECT_EQ(subtract, Rational(1));
    EXPECT_EQ(subtract.den, BigInt(1));

    EXPECT_LT(Rational(BigInt(1), BigInt(3)), Rational(BigInt(2), BigInt(3)));
}

TEST(LraSolver, StrictBoundModelUsesConcreteRational) {
    LraSolver solver;
    solver.declare_real("x");

    LinearExpr x_minus_five;
    x_minus_five.add_var("x", Rational(1));
    x_minus_five.constant = Rational(-5);
    int gt = solver.register_atom({x_minus_five, Relation::Gt});
    solver.notify_assignment(gt, false);

    EXPECT_TRUE(solver.cb_check_found_model({}));
    auto value = solver.value_of("x");
    ASSERT_TRUE(value.has_value());
    EXPECT_GT(*value, Rational(5));
}

TEST(LraSolver, TableauDetectsRowBoundConflict) {
    LraSolver solver;
    solver.declare_real("x");
    solver.declare_real("y");

    LinearExpr sum_minus_three;
    sum_minus_three.add_var("x", Rational(1));
    sum_minus_three.add_var("y", Rational(1));
    sum_minus_three.constant = Rational(-3);

    LinearExpr x_minus_two;
    x_minus_two.add_var("x", Rational(1));
    x_minus_two.constant = Rational(-2);

    LinearExpr y_minus_two;
    y_minus_two.add_var("y", Rational(1));
    y_minus_two.constant = Rational(-2);

    int sum_le = solver.register_atom({sum_minus_three, Relation::Le});
    int sum_ge = solver.register_atom({sum_minus_three, Relation::Ge});
    int x_ge = solver.register_atom({x_minus_two, Relation::Ge});
    int y_ge = solver.register_atom({y_minus_two, Relation::Ge});

    solver.notify_assignment(sum_le, false);
    solver.notify_assignment(sum_ge, false);
    solver.notify_assignment(x_ge, false);
    solver.notify_assignment(y_ge, false);

    EXPECT_FALSE(solver.cb_check_found_model({}));
    bool forgettable = true;
    EXPECT_TRUE(solver.cb_has_external_clause(forgettable));
    EXPECT_FALSE(forgettable);
}

TEST(LraSolver, RowBoundPropagationExplainsWithSourceBounds) {
    LraSolver solver;
    solver.set_row_bound_propagation(true);
    solver.declare_real("x");
    solver.declare_real("y");

    LinearExpr x_minus_two;
    x_minus_two.add_var("x", Rational(1));
    x_minus_two.constant = Rational(-2);

    LinearExpr y_minus_three;
    y_minus_three.add_var("y", Rational(1));
    y_minus_three.constant = Rational(-3);

    LinearExpr sum_minus_five;
    sum_minus_five.add_var("x", Rational(1));
    sum_minus_five.add_var("y", Rational(1));
    sum_minus_five.constant = Rational(-5);

    int x_ge = solver.register_atom({x_minus_two, Relation::Ge});
    int y_ge = solver.register_atom({y_minus_three, Relation::Ge});
    int sum_ge = solver.register_atom({sum_minus_five, Relation::Ge});

    solver.notify_assignment(x_ge, false);
    solver.notify_assignment(y_ge, false);

    EXPECT_EQ(solver.cb_propagate(), sum_ge);
    EXPECT_EQ(solver.cb_add_reason_clause_lit(sum_ge), sum_ge);

    std::vector<int> antecedents;
    for (int lit = solver.cb_add_reason_clause_lit(sum_ge); lit != 0;
         lit = solver.cb_add_reason_clause_lit(sum_ge)) {
        antecedents.push_back(lit);
    }
    std::sort(antecedents.begin(), antecedents.end());
    EXPECT_EQ(antecedents, (std::vector<int>{-y_ge, -x_ge}));
}

TEST(LraSolver, SimpleGraphPropagatesDifferenceConstraint) {
    llm2smt::Stats stats;
    LraSolver solver(&stats);
    solver.set_simple_graph_propagation(true);
    solver.declare_real("x");
    solver.declare_real("y");
    solver.declare_real("z");

    LinearExpr x_minus_y_minus_one;
    x_minus_y_minus_one.add_var("x", Rational(1));
    x_minus_y_minus_one.add_var("y", Rational(-1));
    x_minus_y_minus_one.constant = Rational(-1);

    LinearExpr y_minus_z_minus_one;
    y_minus_z_minus_one.add_var("y", Rational(1));
    y_minus_z_minus_one.add_var("z", Rational(-1));
    y_minus_z_minus_one.constant = Rational(-1);

    LinearExpr x_minus_z_minus_two;
    x_minus_z_minus_two.add_var("x", Rational(1));
    x_minus_z_minus_two.add_var("z", Rational(-1));
    x_minus_z_minus_two.constant = Rational(-2);

    int xy = solver.register_atom({x_minus_y_minus_one, Relation::Le});
    int yz = solver.register_atom({y_minus_z_minus_one, Relation::Le});
    int xz = solver.register_atom({x_minus_z_minus_two, Relation::Le});

    solver.notify_assignment(xy, false);
    solver.notify_assignment(yz, false);

    EXPECT_EQ(solver.cb_propagate(), xz);
    EXPECT_GT(stats.lra_simple_graph_propagations, 0u);

    EXPECT_EQ(solver.cb_add_reason_clause_lit(xz), xz);
    std::vector<int> antecedents;
    for (int lit = solver.cb_add_reason_clause_lit(xz); lit != 0;
         lit = solver.cb_add_reason_clause_lit(xz)) {
        antecedents.push_back(lit);
    }
    std::sort(antecedents.begin(), antecedents.end());
    EXPECT_EQ(antecedents, (std::vector<int>{-yz, -xy}));
}

TEST(LraSolver, SimpleGraphPropagatesUtvpiConstraint) {
    llm2smt::Stats stats;
    LraSolver solver(&stats);
    solver.set_simple_graph_propagation(true);
    solver.declare_real("x");
    solver.declare_real("y");

    LinearExpr sum_minus_one;
    sum_minus_one.add_var("x", Rational(1));
    sum_minus_one.add_var("y", Rational(1));
    sum_minus_one.constant = Rational(-1);

    LinearExpr y_minus_one;
    y_minus_one.add_var("y", Rational(1));
    y_minus_one.constant = Rational(-1);

    LinearExpr x;
    x.add_var("x", Rational(1));

    int sum_le = solver.register_atom({sum_minus_one, Relation::Le});
    int y_ge = solver.register_atom({y_minus_one, Relation::Ge});
    int x_le_zero = solver.register_atom({x, Relation::Le});

    solver.notify_assignment(sum_le, false);
    solver.notify_assignment(y_ge, false);

    EXPECT_EQ(solver.cb_propagate(), x_le_zero);
    EXPECT_GT(stats.lra_simple_graph_propagations, 0u);
}

TEST(LraSolver, SimpleGraphConflictOnlyFindsNegativeCycle) {
    llm2smt::Stats stats;
    LraSolver solver(&stats);
    solver.set_simple_graph_conflicts(true);
    solver.declare_real("x");
    solver.declare_real("y");
    solver.declare_real("z");

    LinearExpr x_minus_y;
    x_minus_y.add_var("x", Rational(1));
    x_minus_y.add_var("y", Rational(-1));

    LinearExpr y_minus_z;
    y_minus_z.add_var("y", Rational(1));
    y_minus_z.add_var("z", Rational(-1));

    LinearExpr z_minus_x;
    z_minus_x.add_var("z", Rational(1));
    z_minus_x.add_var("x", Rational(-1));

    int xy = solver.register_atom({x_minus_y, Relation::Le});
    int yz = solver.register_atom({y_minus_z, Relation::Le});
    int zx = solver.register_atom({z_minus_x, Relation::Lt});

    solver.notify_assignment(xy, false);
    solver.notify_assignment(yz, false);
    solver.notify_assignment(zx, false);

    EXPECT_FALSE(solver.cb_check_found_model({}));
    bool forgettable = true;
    EXPECT_TRUE(solver.cb_has_external_clause(forgettable));
    EXPECT_FALSE(forgettable);
    EXPECT_GT(stats.lra_simple_graph_conflicts, 0u);
    EXPECT_GT(stats.lra_simple_graph_conflict_checks, 0u);
    EXPECT_EQ(stats.lra_simple_graph_propagations, 0u);
}

TEST(LraSolver, RdlCottonPropagatesDifferenceConstraint) {
    llm2smt::Stats stats;
    LraSolver solver(&stats);
    solver.set_rdl_propagation("cotton");
    solver.declare_real("x");
    solver.declare_real("y");
    solver.declare_real("z");

    LinearExpr x_minus_y_minus_one;
    x_minus_y_minus_one.add_var("x", Rational(1));
    x_minus_y_minus_one.add_var("y", Rational(-1));
    x_minus_y_minus_one.constant = Rational(-1);

    LinearExpr y_minus_z_minus_one;
    y_minus_z_minus_one.add_var("y", Rational(1));
    y_minus_z_minus_one.add_var("z", Rational(-1));
    y_minus_z_minus_one.constant = Rational(-1);

    LinearExpr x_minus_z_minus_two;
    x_minus_z_minus_two.add_var("x", Rational(1));
    x_minus_z_minus_two.add_var("z", Rational(-1));
    x_minus_z_minus_two.constant = Rational(-2);

    int xy = solver.register_atom({x_minus_y_minus_one, Relation::Le});
    int yz = solver.register_atom({y_minus_z_minus_one, Relation::Le});
    int xz = solver.register_atom({x_minus_z_minus_two, Relation::Le});

    solver.notify_assignment(xy, false);
    solver.notify_assignment(yz, false);

    EXPECT_EQ(solver.cb_propagate(), xz);
    EXPECT_GT(stats.lra_rdl_prop_enqueues, 0u);
    EXPECT_GT(stats.lra_rdl_prop_relevant_candidates, 0u);

    EXPECT_EQ(solver.cb_add_reason_clause_lit(xz), xz);
    std::vector<int> antecedents;
    for (int lit = solver.cb_add_reason_clause_lit(xz); lit != 0;
         lit = solver.cb_add_reason_clause_lit(xz)) {
        antecedents.push_back(lit);
    }
    std::sort(antecedents.begin(), antecedents.end());
    EXPECT_EQ(antecedents, (std::vector<int>{-yz, -xy}));
}

TEST(LraSolver, RdlCottonDetectsNegativeCycleConflict) {
    llm2smt::Stats stats;
    LraSolver solver(&stats);
    solver.set_rdl_propagation("cotton");
    solver.declare_real("x");
    solver.declare_real("y");

    LinearExpr x_minus_y;
    x_minus_y.add_var("x", Rational(1));
    x_minus_y.add_var("y", Rational(-1));

    LinearExpr y_minus_x_minus_one;
    y_minus_x_minus_one.add_var("y", Rational(1));
    y_minus_x_minus_one.add_var("x", Rational(-1));
    y_minus_x_minus_one.constant = Rational(1);

    int xy = solver.register_atom({x_minus_y, Relation::Le});
    int yx = solver.register_atom({y_minus_x_minus_one, Relation::Le});

    solver.notify_assignment(xy, false);
    solver.notify_assignment(yx, false);

    EXPECT_EQ(solver.cb_propagate(), 0);
    bool forgettable = true;
    EXPECT_TRUE(solver.cb_has_external_clause(forgettable));
    EXPECT_FALSE(forgettable);
    EXPECT_GT(stats.lra_rdl_prop_conflicts, 0u);
}

TEST(LraSolver, RdlCottonBacktrackingRestoresActiveEdges) {
    llm2smt::Stats stats;
    LraSolver solver(&stats);
    solver.set_rdl_propagation("cotton");
    solver.declare_real("x");
    solver.declare_real("y");
    solver.declare_real("z");

    LinearExpr x_minus_y_minus_one;
    x_minus_y_minus_one.add_var("x", Rational(1));
    x_minus_y_minus_one.add_var("y", Rational(-1));
    x_minus_y_minus_one.constant = Rational(-1);

    LinearExpr y_minus_z_minus_one;
    y_minus_z_minus_one.add_var("y", Rational(1));
    y_minus_z_minus_one.add_var("z", Rational(-1));
    y_minus_z_minus_one.constant = Rational(-1);

    LinearExpr x_minus_z_minus_two;
    x_minus_z_minus_two.add_var("x", Rational(1));
    x_minus_z_minus_two.add_var("z", Rational(-1));
    x_minus_z_minus_two.constant = Rational(-2);

    int xy = solver.register_atom({x_minus_y_minus_one, Relation::Le});
    int yz = solver.register_atom({y_minus_z_minus_one, Relation::Le});
    int xz = solver.register_atom({x_minus_z_minus_two, Relation::Le});

    solver.notify_assignment(xy, false);
    solver.notify_new_decision_level();
    solver.notify_assignment(yz, false);
    EXPECT_EQ(solver.cb_propagate(), xz);

    solver.notify_backtrack(0);
    EXPECT_EQ(stats.lra_rdl_prop_edges_active, 1u);
    EXPECT_EQ(solver.cb_propagate(), 0);
}

TEST(LraSolver, RdlCottonIsLazyUntilPropagationCallback) {
    llm2smt::Stats stats;
    LraSolver solver(&stats);
    solver.set_rdl_propagation("cotton");
    solver.declare_real("x");
    solver.declare_real("y");

    LinearExpr x_minus_y;
    x_minus_y.add_var("x", Rational(1));
    x_minus_y.add_var("y", Rational(-1));
    int xy = solver.register_atom({x_minus_y, Relation::Le});

    solver.notify_assignment(xy, false);
    EXPECT_EQ(stats.lra_rdl_prop_sigma, 1u);
    EXPECT_EQ(stats.lra_rdl_prop_candidates, 0u);
}

TEST(LraSolver, RdlCottonBudgetReportsCutoff) {
    llm2smt::Stats stats;
    LraSolver solver(&stats);
    solver.set_rdl_propagation("cotton");
    solver.set_rdl_propagation_budget(1);
    solver.declare_real("x");
    solver.declare_real("y");
    solver.declare_real("z");

    LinearExpr x_minus_y;
    x_minus_y.add_var("x", Rational(1));
    x_minus_y.add_var("y", Rational(-1));

    LinearExpr y_minus_z;
    y_minus_z.add_var("y", Rational(1));
    y_minus_z.add_var("z", Rational(-1));

    LinearExpr x_minus_z;
    x_minus_z.add_var("x", Rational(1));
    x_minus_z.add_var("z", Rational(-1));

    int xy = solver.register_atom({x_minus_y, Relation::Le});
    (void)solver.register_atom({y_minus_z, Relation::Le});
    (void)solver.register_atom({x_minus_z, Relation::Le});

    solver.notify_assignment(xy, false);
    EXPECT_EQ(solver.cb_propagate(), 0);
    EXPECT_GT(stats.lra_rdl_prop_budget_cutoffs, 0u);
}

TEST(LraSolver, RdlCottonPreservesStrictInequalityOrdering) {
    llm2smt::Stats stats;
    LraSolver solver(&stats);
    solver.set_rdl_propagation("cotton");
    solver.declare_real("x");
    solver.declare_real("y");

    LinearExpr x_minus_y;
    x_minus_y.add_var("x", Rational(1));
    x_minus_y.add_var("y", Rational(-1));

    LinearExpr y_minus_x;
    y_minus_x.add_var("y", Rational(1));
    y_minus_x.add_var("x", Rational(-1));

    int x_lt_y = solver.register_atom({x_minus_y, Relation::Lt});
    int y_le_x = solver.register_atom({y_minus_x, Relation::Le});

    solver.notify_assignment(x_lt_y, false);
    solver.notify_assignment(y_le_x, false);

    EXPECT_EQ(solver.cb_propagate(), 0);
    bool forgettable = true;
    EXPECT_TRUE(solver.cb_has_external_clause(forgettable));
    EXPECT_GT(stats.lra_rdl_prop_conflicts, 0u);
}

TEST(LraSolver, MinColumnPivotHeuristicReportsChoices) {
    llm2smt::Stats stats;
    LraSolver solver(&stats);
    solver.set_pivot_heuristic("min-column");
    solver.declare_real("x");
    solver.declare_real("y");

    LinearExpr sum_minus_three;
    sum_minus_three.add_var("x", Rational(1));
    sum_minus_three.add_var("y", Rational(1));
    sum_minus_three.constant = Rational(-3);

    LinearExpr x_minus_two;
    x_minus_two.add_var("x", Rational(1));
    x_minus_two.constant = Rational(-2);

    LinearExpr y_minus_two;
    y_minus_two.add_var("y", Rational(1));
    y_minus_two.constant = Rational(-2);

    int sum_eq = solver.register_atom({sum_minus_three, Relation::Eq});
    int x_ge = solver.register_atom({x_minus_two, Relation::Ge});
    int y_ge = solver.register_atom({y_minus_two, Relation::Ge});

    solver.notify_assignment(sum_eq, false);
    solver.notify_assignment(x_ge, false);
    solver.notify_assignment(y_ge, false);

    EXPECT_FALSE(solver.cb_check_found_model({}));
    EXPECT_GT(stats.lra_pivots, 0u);
    EXPECT_GT(stats.lra_pivot_candidates, 0u);
    EXPECT_GT(stats.lra_pivot_min_column_choices, 0u);
    EXPECT_GT(stats.lra_check_max_pivots, 0u);
}

TEST(LraSolver, DirectEqualityAtomAppliesBothBounds) {
    LraSolver solver;
    solver.declare_real("x");

    LinearExpr x;
    x.add_var("x", Rational(1));

    int eq_zero = solver.register_atom({x, Relation::Eq});
    int gt_zero = solver.register_atom({x, Relation::Gt});

    solver.notify_assignment(eq_zero, false);
    solver.notify_assignment(gt_zero, false);

    EXPECT_FALSE(solver.cb_check_found_model({}));
}

TEST(LraSolver, DirectNegatedEqualityAtomIsRejected) {
    LraSolver solver;
    solver.declare_real("x");

    LinearExpr x;
    x.add_var("x", Rational(1));
    int eq_zero = solver.register_atom({x, Relation::Eq});

    EXPECT_THROW(solver.notify_assignment(-eq_zero, false), std::runtime_error);
}
