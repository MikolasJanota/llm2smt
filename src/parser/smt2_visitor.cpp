#include "parser/smt2_visitor.h"

#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

namespace llm2smt {

Smt2Visitor::Smt2Visitor(SmtContext& ctx) : ctx_(ctx) {}

// ============================================================================
// Helper: symbol / identifier names
// ============================================================================

std::string Smt2Visitor::symbol_name(
    smt2parser::SMTLIBv2Parser::SymbolContext* sym)
{
    return sym->getText();
}

std::string Smt2Visitor::identifier_name(
    smt2parser::SMTLIBv2Parser::IdentifierContext* id)
{
    // identifier : symbol | '(' '_' symbol index+ ')'
    return id->symbol()->getText();
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
    // Dispatch on which sub-command marker is present
    if (ctx->cmd_setLogic()) {
        // (set-logic SYMBOL)
        std::string logic = symbol_name(ctx->symbol(0));
        ctx_.logic = logic;
        if (logic != "QF_EUF" && logic != "QF_UF") {
            std::cerr << "Warning: unsupported logic " << logic
                      << ", proceeding as QF_UF\n";
        }
    }
    else if (ctx->cmd_declareSort()) {
        // (declare-sort SYMBOL NUMERAL)
        std::string name  = symbol_name(ctx->symbol(0));
        uint32_t    arity = std::stoul(ctx->numeral()->getText());
        ctx_.declared_sorts[name] = arity;
    }
    else if (ctx->cmd_declareFun()) {
        // (declare-fun SYMBOL (SORT*) SORT)
        // symbol(0) = function name; sort(0..n-1) = param sorts; sort(n) = return sort
        std::string name  = symbol_name(ctx->symbol(0));
        auto sorts = ctx->sort();
        uint32_t arity = (sorts.size() > 0)
                         ? static_cast<uint32_t>(sorts.size() - 1)
                         : 0;
        SymbolId sym = ctx_.nm.declare_symbol(name, arity);
        ctx_.declared_fns[name] = sym;
    }
    else if (ctx->cmd_assert()) {
        // (assert TERM)
        auto terms = ctx->term();
        if (terms.empty()) {
            throw std::runtime_error("assert: missing term");
        }
        int lit = visit_formula(terms[0]);
        ctx_.assertions.push_back(lit);
        std::array<int, 1> cl = {lit};
        ctx_.sat.add_clause(std::span<const int>(cl));
    }
    else if (ctx->cmd_checkSat()) {
        // (check-sat)
        SolveResult result = ctx_.sat.solve();
        switch (result) {
        case SolveResult::SAT:     std::cout << "sat\n";     break;
        case SolveResult::UNSAT:   std::cout << "unsat\n";   break;
        case SolveResult::UNKNOWN: std::cout << "unknown\n"; break;
        }
    }
    // Other commands (set-info, exit, etc.) are silently ignored

    return nullptr;
}

// ============================================================================
// Term parsing
// ============================================================================

NodeId Smt2Visitor::visit_term(smt2parser::SMTLIBv2Parser::TermContext* term_ctx)
{
    // Simple qualified identifier (constant or 0-arity symbol)
    if (term_ctx->qual_identifier() != nullptr && term_ctx->term().empty()) {
        std::string name = identifier_name(
            term_ctx->qual_identifier()->identifier());
        auto it = ctx_.declared_fns.find(name);
        if (it == ctx_.declared_fns.end()) {
            throw std::runtime_error("Undeclared function/constant: " + name);
        }
        SymbolId sym = it->second;
        return ctx_.nm.mk_const(sym);
    }

    // Application: (f t1 t2 ...)
    // In SMTLIBv2 grammar: term ::= '(' qual_identifier term+ ')'
    if (term_ctx->qual_identifier() != nullptr && !term_ctx->term().empty()) {
        std::string name = identifier_name(
            term_ctx->qual_identifier()->identifier());
        auto it = ctx_.declared_fns.find(name);
        if (it == ctx_.declared_fns.end()) {
            throw std::runtime_error("Undeclared function: " + name);
        }
        SymbolId sym = it->second;
        std::vector<NodeId> args;
        for (auto* sub : term_ctx->term()) {
            args.push_back(visit_term(sub));
        }
        return ctx_.nm.mk_app(sym, std::span<const NodeId>(args));
    }

    throw std::runtime_error("Unsupported term form");
}

int Smt2Visitor::visit_formula(smt2parser::SMTLIBv2Parser::TermContext* term_ctx)
{
    // Check for application of a predefined symbol
    if (term_ctx->qual_identifier() != nullptr) {
        std::string op = identifier_name(term_ctx->qual_identifier()->identifier());

        if (op == "=" && term_ctx->term().size() == 2) {
            NodeId lhs = visit_term(term_ctx->term(0));
            NodeId rhs = visit_term(term_ctx->term(1));
            return ctx_.euf.register_equality(lhs, rhs);
        }

        if (op == "not" && term_ctx->term().size() == 1) {
            int inner = visit_formula(term_ctx->term(0));
            return -inner;
        }
    }

    throw std::runtime_error(
        "Only equalities and their negations are supported in QF_EUF assertions");
}

} // namespace llm2smt
