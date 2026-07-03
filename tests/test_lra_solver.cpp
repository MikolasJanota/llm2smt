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
