#pragma once

#include <any>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "SMTLIBv2BaseVisitor.h"
#include "SMTLIBv2Parser.h"

#include "core/node.h"
#include "parser/smt_context.h"

namespace llm2smt {

class Smt2Visitor : public smt2parser::SMTLIBv2BaseVisitor {
public:
    explicit Smt2Visitor(SmtContext& ctx);

    std::any visitStart(smt2parser::SMTLIBv2Parser::StartContext*) override;
    std::any visitCommand(smt2parser::SMTLIBv2Parser::CommandContext*) override;

private:
    SmtContext& ctx_;

    // Let environment: stack of (variable-name → bound TermContext*)
    // Bindings are evaluated lazily on first use.
    using LetFrame = std::unordered_map<std::string,
                                        smt2parser::SMTLIBv2Parser::TermContext*>;
    std::vector<LetFrame> let_env_;

    // Tseitin proxy cache: TermContext* → SAT literal
    // Used when a sub-formula (e.g. or/and) is used in literal position.
    std::unordered_map<smt2parser::SMTLIBv2Parser::TermContext*, int> tseitin_cache_;

    // Cache for U-sorted ite terms: TermContext* → fresh NodeId
    std::unordered_map<smt2parser::SMTLIBv2Parser::TermContext*, NodeId> ite_node_cache_;
    int ite_counter_ = 0;  // for generating unique names

    // A literal that is always forced true (for `true`/`false` constants).
    int true_lit_ = 0;   // 0 = not yet allocated
    int get_true_lit();  // allocates on first call

    // EUF nodes for the Bool constants `true` and `false` used as U-sorted terms
    // (e.g. as arguments to a UF that accepts Bool-sorted arguments).
    // Both nodes are created together on first use; the axiom true≠false is
    // added at that point so the SAT solver always sees them as distinct.
    NodeId true_node_  = NULL_NODE;
    NodeId false_node_ = NULL_NODE;
    NodeId get_bool_term_node(bool val);  // allocates both on first call

    // Bool-sorted EUF nodes that have already had bridging clauses added.
    // Bridging: lit → (node=true_n) and ¬lit → (node=false_n).
    std::unordered_set<NodeId> linked_bool_terms_;
    void link_bool_term_to_euf(NodeId node);  // idempotent

    static std::string symbol_name(smt2parser::SMTLIBv2Parser::SymbolContext*);
    static std::string identifier_name(smt2parser::SMTLIBv2Parser::IdentifierContext*);

    // Evaluate a U-sorted term → NodeId.
    NodeId visit_term(smt2parser::SMTLIBv2Parser::TermContext*);

    // Add all SAT clauses required by "this formula must be true".
    // Handles and, or, distinct, let, atoms, negations.
    void assert_formula(smt2parser::SMTLIBv2Parser::TermContext*);

    // Evaluate a Bool-sorted formula → SAT literal.
    // Valid for atoms (=, predicate apps), `not`, let, and variable references.
    // For `or` use collect_clause_lits; for `and` use assert_formula.
    int eval_lit(smt2parser::SMTLIBv2Parser::TermContext*);

    // Append all literals of a disjunction (or atom) into `lits`.
    void collect_clause_lits(smt2parser::SMTLIBv2Parser::TermContext*,
                              std::vector<int>& lits);

    // Return true if the top-level term is Bool-sorted
    // (built-in boolean op or declared Bool function).
    bool is_bool_sorted(smt2parser::SMTLIBv2Parser::TermContext*) const;
};

} // namespace llm2smt
