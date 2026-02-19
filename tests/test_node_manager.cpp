#include <gtest/gtest.h>
#include "core/node_manager.h"

using namespace llm2smt;

TEST(NodeManager, ConstantHashConsing) {
    NodeManager nm;
    SymbolId sa = nm.declare_symbol("a", 0);
    SymbolId sb = nm.declare_symbol("b", 0);

    NodeId a1 = nm.mk_const(sa);
    NodeId a2 = nm.mk_const(sa);
    NodeId b1 = nm.mk_const(sb);

    EXPECT_EQ(a1, a2) << "Same constant should map to same NodeId";
    EXPECT_NE(a1, b1) << "Different constants should have different NodeIds";
    EXPECT_NE(a1, NULL_NODE);
    EXPECT_NE(b1, NULL_NODE);
}

TEST(NodeManager, ApplicationHashConsing) {
    NodeManager nm;
    SymbolId sf = nm.declare_symbol("f", 1);
    SymbolId sa = nm.declare_symbol("a", 0);
    SymbolId sb = nm.declare_symbol("b", 0);

    NodeId a = nm.mk_const(sa);
    NodeId b = nm.mk_const(sb);

    std::array<NodeId,1> args_a = {a};
    std::array<NodeId,1> args_b = {b};

    NodeId fa1 = nm.mk_app(sf, std::span<const NodeId>(args_a));
    NodeId fa2 = nm.mk_app(sf, std::span<const NodeId>(args_a));
    NodeId fb  = nm.mk_app(sf, std::span<const NodeId>(args_b));

    EXPECT_EQ(fa1, fa2)  << "f(a) twice should return same NodeId";
    EXPECT_NE(fa1, fb)   << "f(a) and f(b) should differ";
    EXPECT_NE(fa1, a);
}

TEST(NodeManager, IsConst) {
    NodeManager nm;
    SymbolId sf = nm.declare_symbol("f", 1);
    SymbolId sa = nm.declare_symbol("a", 0);
    NodeId a = nm.mk_const(sa);
    std::array<NodeId,1> args = {a};
    NodeId fa = nm.mk_app(sf, std::span<const NodeId>(args));

    EXPECT_TRUE(nm.is_const(a));
    EXPECT_FALSE(nm.is_const(fa));
}

TEST(NodeManager, StructuralSharing) {
    NodeManager nm;
    SymbolId sf = nm.declare_symbol("f", 2);
    SymbolId sa = nm.declare_symbol("a", 0);
    SymbolId sb = nm.declare_symbol("b", 0);

    NodeId a = nm.mk_const(sa);
    NodeId b = nm.mk_const(sb);
    std::array<NodeId,2> args = {a, b};
    NodeId fab1 = nm.mk_app(sf, std::span<const NodeId>(args));
    NodeId fab2 = nm.mk_app(sf, std::span<const NodeId>(args));

    EXPECT_EQ(fab1, fab2);

    // Different order is different
    std::array<NodeId,2> args_rev = {b, a};
    NodeId fba = nm.mk_app(sf, std::span<const NodeId>(args_rev));
    EXPECT_NE(fab1, fba);
}

TEST(NodeManager, DeclareSymbolIdempotent) {
    NodeManager nm;
    SymbolId s1 = nm.declare_symbol("f", 2);
    SymbolId s2 = nm.declare_symbol("f", 2);
    EXPECT_EQ(s1, s2);
}

TEST(NodeManager, ApplySymbolRegistered) {
    NodeManager nm;
    SymbolId at = nm.apply_symbol();
    EXPECT_NE(at, NULL_SYMBOL);
    const SymbolInfo& info = nm.symbol_table().get(at);
    EXPECT_EQ(info.name, "@");
    EXPECT_EQ(info.arity, 2u);
}
