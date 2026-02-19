#include "parser/smt2_visitor.h"

#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

namespace llm2smt {

Smt2Visitor::Smt2Visitor(SmtContext& ctx) : ctx_(ctx) {}

// ============================================================================
// Helpers
// ============================================================================

std::string Smt2Visitor::symbol_name(
    smt2parser::SMTLIBv2Parser::SymbolContext* sym)
{
    return sym->getText();
}

std::string Smt2Visitor::identifier_name(
    smt2parser::SMTLIBv2Parser::IdentifierContext* id)
{
    return id->symbol()->getText();
}

// ============================================================================
// Helpers: true/false literal
// ============================================================================

int Smt2Visitor::get_true_lit()
{
    if (true_lit_ != 0) return true_lit_;
    true_lit_ = ctx_.euf.new_var();
    std::array<int, 1> cl = {true_lit_};
    ctx_.sat.add_clause(std::span<const int>(cl));
    return true_lit_;
}

// ============================================================================
// Top-level
// ============================================================================

std::any Smt2Visitor::visitStart(
    smt2parser::SMTLIBv2Parser::StartContext* ctx)
{
    return visitChildren(ctx);
}

// ============================================================================
// Command dispatch
// ============================================================================

std::any Smt2Visitor::visitCommand(
    smt2parser::SMTLIBv2Parser::CommandContext* ctx)
{
    if (ctx->cmd_setLogic()) {
        std::string logic = symbol_name(ctx->symbol(0));
        ctx_.logic = logic;
        if (logic != "QF_EUF" && logic != "QF_UF") {
            std::cerr << "Warning: unsupported logic " << logic
                      << ", proceeding as QF_UF\n";
        }
    }
    else if (ctx->cmd_declareSort()) {
        std::string name  = symbol_name(ctx->symbol(0));
        uint32_t    arity = std::stoul(ctx->numeral()->getText());
        ctx_.declared_sorts[name] = arity;
    }
    else if (ctx->cmd_declareFun()) {
        std::string name  = symbol_name(ctx->symbol(0));
        auto sorts = ctx->sort();
        uint32_t arity = (sorts.size() > 0)
                         ? static_cast<uint32_t>(sorts.size() - 1)
                         : 0;
        SymbolId sym = ctx_.nm.declare_symbol(name, arity);
        ctx_.declared_fns[name] = sym;
        // Mark if return sort is Bool
        if (!sorts.empty() && sorts.back()->getText() == "Bool") {
            ctx_.bool_fns.insert(sym);
        }
    }
    else if (ctx->cmd_assert()) {
        auto terms = ctx->term();
        if (terms.empty()) throw std::runtime_error("assert: missing term");
        assert_formula(terms[0]);
    }
    else if (ctx->cmd_checkSat()) {
        SolveResult result = ctx_.sat.solve();
        switch (result) {
        case SolveResult::SAT:     std::cout << "sat\n";     break;
        case SolveResult::UNSAT:   std::cout << "unsat\n";   break;
        case SolveResult::UNKNOWN: std::cout << "unknown\n"; break;
        }
    }
    return nullptr;
}

// ============================================================================
// Term parsing (U-sorted)
// ============================================================================

NodeId Smt2Visitor::visit_term(
    smt2parser::SMTLIBv2Parser::TermContext* ctx)
{
    // Let expression
    if (ctx->GRW_Let()) {
        let_env_.emplace_back();
        for (auto* vb : ctx->var_binding())
            let_env_.back()[vb->symbol()->getText()] = vb->term();
        NodeId result = visit_term(ctx->term()[0]);
        let_env_.pop_back();
        return result;
    }

    if (ctx->qual_identifier() == nullptr)
        throw std::runtime_error("Unsupported term form");

    std::string name = identifier_name(ctx->qual_identifier()->identifier());

    // Let variable lookup (search innermost frame first)
    if (ctx->term().empty()) {
        for (auto it = let_env_.rbegin(); it != let_env_.rend(); ++it) {
            auto jt = it->find(name);
            if (jt != it->end()) return visit_term(jt->second);
        }
    }

    auto fit = ctx_.declared_fns.find(name);
    if (fit == ctx_.declared_fns.end())
        throw std::runtime_error("Undeclared symbol: " + name);
    SymbolId sym = fit->second;

    if (ctx->term().empty())
        return ctx_.nm.mk_const(sym);

    std::vector<NodeId> args;
    for (auto* sub : ctx->term())
        args.push_back(visit_term(sub));
    return ctx_.nm.mk_app(sym, std::span<const NodeId>(args));
}

// ============================================================================
// Formula parsing
// ============================================================================

// Add all SAT clauses for "this formula must hold".
void Smt2Visitor::assert_formula(
    smt2parser::SMTLIBv2Parser::TermContext* ctx)
{
    // Let expression: push bindings, recurse on body, pop.
    if (ctx->GRW_Let()) {
        let_env_.emplace_back();
        for (auto* vb : ctx->var_binding())
            let_env_.back()[vb->symbol()->getText()] = vb->term();
        assert_formula(ctx->term()[0]);
        let_env_.pop_back();
        return;
    }

    if (ctx->qual_identifier() != nullptr) {
        std::string op = identifier_name(ctx->qual_identifier()->identifier());

        // true: trivially satisfied
        if (op == "true") return;

        // false: contradiction — add empty clause
        if (op == "false") {
            ctx_.sat.add_clause(std::span<const int>{});
            return;
        }

        // (and φ1 φ2 ...) — add each conjunct separately
        if (op == "and") {
            for (auto* sub : ctx->term())
                assert_formula(sub);
            return;
        }

        // (=> A B ...) right-assoc: clause {¬A, ¬B, ..., last}
        if (op == "=>") {
            auto terms = ctx->term();
            std::vector<int> lits;
            for (size_t i = 0; i < terms.size() - 1; ++i)
                lits.push_back(-eval_lit(terms[i]));
            lits.push_back(eval_lit(terms.back()));
            ctx_.sat.add_clause(std::span<const int>(lits));
            return;
        }

        // (xor A B): assert (A ∨ B) ∧ (¬A ∨ ¬B)
        if (op == "xor" && ctx->term().size() == 2) {
            int a = eval_lit(ctx->term()[0]);
            int b = eval_lit(ctx->term()[1]);
            std::array<int, 2> c1 = {a, b};
            std::array<int, 2> c2 = {-a, -b};
            ctx_.sat.add_clause(std::span<const int>(c1));
            ctx_.sat.add_clause(std::span<const int>(c2));
            return;
        }

        // (ite C T F): assert (¬C ∨ T) ∧ (C ∨ F)
        if (op == "ite" && ctx->term().size() == 3) {
            int c = eval_lit(ctx->term()[0]);
            int t = eval_lit(ctx->term()[1]);
            int f = eval_lit(ctx->term()[2]);
            std::array<int, 2> c1 = {-c, t};
            std::array<int, 2> c2 = {c, f};
            ctx_.sat.add_clause(std::span<const int>(c1));
            ctx_.sat.add_clause(std::span<const int>(c2));
            return;
        }

        // (distinct t1 t2 ... tn) — pairwise disequalities as unit clauses
        if (op == "distinct") {
            auto terms = ctx->term();
            for (size_t i = 0; i < terms.size(); ++i) {
                for (size_t j = i + 1; j < terms.size(); ++j) {
                    NodeId ti = visit_term(terms[i]);
                    NodeId tj = visit_term(terms[j]);
                    int lit = ctx_.euf.register_equality(ti, tj);
                    std::array<int, 1> cl = {-lit};
                    ctx_.sat.add_clause(std::span<const int>(cl));
                }
            }
            return;
        }
    }

    // Everything else: collect literals and add as a clause (handles or, atoms, not).
    std::vector<int> lits;
    collect_clause_lits(ctx, lits);
    if (!lits.empty())
        ctx_.sat.add_clause(std::span<const int>(lits));
}

// Collect SAT literals for a disjunction (or atom/negation) into `lits`.
void Smt2Visitor::collect_clause_lits(
    smt2parser::SMTLIBv2Parser::TermContext* ctx,
    std::vector<int>& lits)
{
    // Let expression: push, collect from body, pop.
    if (ctx->GRW_Let()) {
        let_env_.emplace_back();
        for (auto* vb : ctx->var_binding())
            let_env_.back()[vb->symbol()->getText()] = vb->term();
        collect_clause_lits(ctx->term()[0], lits);
        let_env_.pop_back();
        return;
    }

    if (ctx->qual_identifier() != nullptr) {
        std::string op = identifier_name(ctx->qual_identifier()->identifier());
        if (op == "or") {
            for (auto* sub : ctx->term())
                collect_clause_lits(sub, lits);
            return;
        }
    }

    lits.push_back(eval_lit(ctx));
}

// Evaluate a Bool-sorted formula to a SAT literal.
int Smt2Visitor::eval_lit(
    smt2parser::SMTLIBv2Parser::TermContext* ctx)
{
    // Let expression
    if (ctx->GRW_Let()) {
        let_env_.emplace_back();
        for (auto* vb : ctx->var_binding())
            let_env_.back()[vb->symbol()->getText()] = vb->term();
        int result = eval_lit(ctx->term()[0]);
        let_env_.pop_back();
        return result;
    }

    if (ctx->qual_identifier() == nullptr)
        throw std::runtime_error("Unsupported formula form");

    std::string op = identifier_name(ctx->qual_identifier()->identifier());

    // (not φ)
    if (op == "not" && ctx->term().size() == 1)
        return -eval_lit(ctx->term()[0]);

    // (= t1 t2)
    if (op == "=" && ctx->term().size() == 2) {
        NodeId lhs = visit_term(ctx->term()[0]);
        NodeId rhs = visit_term(ctx->term()[1]);
        return ctx_.euf.register_equality(lhs, rhs);
    }

    // (distinct t1 t2) in literal position — same as (not (= t1 t2))
    if (op == "distinct" && ctx->term().size() == 2) {
        NodeId lhs = visit_term(ctx->term()[0]);
        NodeId rhs = visit_term(ctx->term()[1]);
        return -ctx_.euf.register_equality(lhs, rhs);
    }

    // (or A B ...) in literal position — Tseitin proxy x ↔ (A ∨ B ∨ ...)
    if (op == "or") {
        auto cit = tseitin_cache_.find(ctx);
        if (cit != tseitin_cache_.end()) return cit->second;
        int x = ctx_.euf.new_var();
        tseitin_cache_[ctx] = x;
        std::vector<int> sub_lits;
        for (auto* sub : ctx->term())
            collect_clause_lits(sub, sub_lits);
        // x → (A ∨ B ∨ ...)
        std::vector<int> fwd = {-x};
        for (int l : sub_lits) fwd.push_back(l);
        ctx_.sat.add_clause(std::span<const int>(fwd));
        // A → x, B → x, ...
        for (int l : sub_lits) {
            std::array<int, 2> cl = {-l, x};
            ctx_.sat.add_clause(std::span<const int>(cl));
        }
        return x;
    }

    // (and A B ...) in literal position — Tseitin proxy y ↔ (A ∧ B ∧ ...)
    if (op == "and") {
        auto cit = tseitin_cache_.find(ctx);
        if (cit != tseitin_cache_.end()) return cit->second;
        int y = ctx_.euf.new_var();
        tseitin_cache_[ctx] = y;
        std::vector<int> sub_lits;
        for (auto* sub : ctx->term()) sub_lits.push_back(eval_lit(sub));
        for (int l : sub_lits) {                     // y → each conjunct
            std::array<int, 2> cl = {-y, l};
            ctx_.sat.add_clause(std::span<const int>(cl));
        }
        std::vector<int> bwd = {y};                  // ¬A ∨ ¬B ∨ ... ∨ y
        for (int l : sub_lits) bwd.push_back(-l);
        ctx_.sat.add_clause(std::span<const int>(bwd));
        return y;
    }

    // (=> A B ...) right-assoc: Tseitin proxy x ↔ (¬A ∨ ¬B ∨ ... ∨ last)
    if (op == "=>") {
        auto cit = tseitin_cache_.find(ctx);
        if (cit != tseitin_cache_.end()) return cit->second;
        int x = ctx_.euf.new_var();
        tseitin_cache_[ctx] = x;
        auto terms = ctx->term();
        std::vector<int> sub_lits;
        for (size_t i = 0; i < terms.size() - 1; ++i)
            sub_lits.push_back(-eval_lit(terms[i]));
        sub_lits.push_back(eval_lit(terms.back()));
        // x → disjunction
        std::vector<int> fwd = {-x};
        for (int l : sub_lits) fwd.push_back(l);
        ctx_.sat.add_clause(std::span<const int>(fwd));
        // each disjunct → x
        for (int l : sub_lits) {
            std::array<int, 2> cl = {-l, x};
            ctx_.sat.add_clause(std::span<const int>(cl));
        }
        return x;
    }

    // (xor A B) — Tseitin proxy x ↔ (A ⊕ B)
    if (op == "xor" && ctx->term().size() == 2) {
        auto cit = tseitin_cache_.find(ctx);
        if (cit != tseitin_cache_.end()) return cit->second;
        int x = ctx_.euf.new_var();
        tseitin_cache_[ctx] = x;
        int a = eval_lit(ctx->term()[0]);
        int b = eval_lit(ctx->term()[1]);
        // x → (A ∨ B):    ¬x ∨ A ∨ B
        { std::array<int,3> cl = {-x,  a,  b}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        // x → (¬A ∨ ¬B):  ¬x ∨ ¬A ∨ ¬B
        { std::array<int,3> cl = {-x, -a, -b}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        // (A ∧ ¬B) → x:   ¬A ∨ B ∨ x
        { std::array<int,3> cl = {-a,  b,  x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        // (¬A ∧ B) → x:    A ∨ ¬B ∨ x
        { std::array<int,3> cl = { a, -b,  x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        return x;
    }

    // (ite C T F) — Tseitin proxy x ↔ (C ? T : F)
    if (op == "ite" && ctx->term().size() == 3) {
        auto cit = tseitin_cache_.find(ctx);
        if (cit != tseitin_cache_.end()) return cit->second;
        int x = ctx_.euf.new_var();
        tseitin_cache_[ctx] = x;
        int c = eval_lit(ctx->term()[0]);
        int t = eval_lit(ctx->term()[1]);
        int f = eval_lit(ctx->term()[2]);
        // C ∧ T → x:   ¬C ∨ ¬T ∨ x
        { std::array<int,3> cl = {-c, -t,  x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        // C ∧ ¬T → ¬x: ¬C ∨  T ∨ ¬x
        { std::array<int,3> cl = {-c,  t, -x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        // ¬C ∧ F → x:   C ∨ ¬F ∨  x
        { std::array<int,3> cl = { c, -f,  x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        // ¬C ∧ ¬F → ¬x: C ∨  F ∨ ¬x
        { std::array<int,3> cl = { c,  f, -x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        return x;
    }

    // 0-arity: built-in constants, let variable, or Bool propositional constant
    if (ctx->term().empty()) {
        // Built-in Boolean constants
        if (op == "true")  return get_true_lit();
        if (op == "false") return -get_true_lit();
        // Search let environment first
        for (auto it = let_env_.rbegin(); it != let_env_.rend(); ++it) {
            auto jt = it->find(op);
            if (jt != it->end()) return eval_lit(jt->second);
        }
        // Bool-valued 0-ary declared symbol
        auto fit = ctx_.declared_fns.find(op);
        if (fit != ctx_.declared_fns.end()
            && ctx_.bool_fns.count(fit->second)) {
            NodeId n = ctx_.nm.mk_const(fit->second);
            return ctx_.lit_for_node(n);
        }
        throw std::runtime_error("Unknown Bool variable: " + op);
    }

    // n-ary Bool predicate application
    auto fit = ctx_.declared_fns.find(op);
    if (fit != ctx_.declared_fns.end()
        && ctx_.bool_fns.count(fit->second)) {
        std::vector<NodeId> args;
        for (auto* sub : ctx->term())
            args.push_back(visit_term(sub));
        NodeId n = ctx_.nm.mk_app(fit->second, std::span<const NodeId>(args));
        return ctx_.lit_for_node(n);
    }

    throw std::runtime_error(
        "Unsupported formula: " + op
        + " (supported: true, false, not, =>, and, or, xor, ite, =, distinct, predicates)");
}

} // namespace llm2smt
