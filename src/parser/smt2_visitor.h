#pragma once

#include <string>
#include <vector>
#include <any>

#include "SMTLIBv2BaseVisitor.h"
#include "SMTLIBv2Parser.h"

#include "core/node.h"
#include "parser/smt_context.h"

namespace llm2smt {

// Visits the ANTLR4 parse tree and populates the SmtContext.
class Smt2Visitor : public smt2parser::SMTLIBv2BaseVisitor {
public:
    explicit Smt2Visitor(SmtContext& ctx);

    // Top-level: visit the start rule
    std::any visitStart(
        smt2parser::SMTLIBv2Parser::StartContext* ctx) override;

    // Command dispatch
    std::any visitCommand(
        smt2parser::SMTLIBv2Parser::CommandContext* ctx) override;

private:
    SmtContext& ctx_;

    // Parse a term and return a NodeId
    NodeId visit_term(smt2parser::SMTLIBv2Parser::TermContext* term_ctx);

    // Parse a formula term and return a SAT literal
    int visit_formula(smt2parser::SMTLIBv2Parser::TermContext* term_ctx);

    // Get symbol name from a symbol context
    static std::string symbol_name(smt2parser::SMTLIBv2Parser::SymbolContext* sym);

    // Get symbol name from an identifier context
    static std::string identifier_name(
        smt2parser::SMTLIBv2Parser::IdentifierContext* id);
};

} // namespace llm2smt
