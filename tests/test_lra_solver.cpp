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
