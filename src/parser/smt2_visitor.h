#pragma once

#include <any>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "SMTLIBv2BaseVisitor.h"
#include "SMTLIBv2Parser.h"

#include "core/node.h"
#include "core/stats.h"
#include "parser/smt_context.h"
#include "preprocessor/fml.h"
#include "preprocessor/preproc_options.h"

namespace llm2smt {

class Smt2Visitor : public smt2parser::SMTLIBv2BaseVisitor {
public:
    explicit Smt2Visitor(SmtContext& ctx, const PreprocOptions& opts, Stats& stats);

    std::any visitStart(smt2parser::SMTLIBv2Parser::StartContext*) override;
    std::any visitCommand(smt2parser::SMTLIBv2Parser::CommandContext*) override;

private:
    SmtContext& ctx_;

    // Let environment: stack of (variable-name → bound TermContext*)
    // Bindings are evaluated lazily on first use.
    using LetFrame = std::unordered_map<std::string,
                                        smt2parser::SMTLIBv2Parser::TermContext*>;
    std::vector<LetFrame> let_env_;

    // define-fun macros (0-arity only): name → body TermContext*.
    // Expanded inline wherever the name is referenced.
    std::unordered_map<std::string, smt2parser::SMTLIBv2Parser::TermContext*>
        defined_fns_;
    std::unordered_set<std::string> defined_bool_fns_; // Bool-returning ones

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

    // ── Preprocessing ─────────────────────────────────────────────────────
    PreprocOptions opts_;
    Stats&         stats_;

    // FmlRef assertions accumulated during parsing (when preprocessing is on).
    std::vector<FmlRef> pending_fmls_;

    // Cache: Fml object address → Tseitin SAT literal (for lit_of_fml reuse).
    std::unordered_map<const Fml*, int> fml_lit_cache_;

    // Build a FmlRef tree from a Bool-sorted parse-tree node.
    // Eagerly calls visit_term for U-sorted sub-terms.
    FmlRef build_fml(smt2parser::SMTLIBv2Parser::TermContext*);

    // Assert a FmlRef by adding the required SAT clauses (top-level assertion).
    void encode_fml(FmlRef f);

    // Return (or create) a SAT literal equivalent to a FmlRef sub-formula.
    int lit_of_fml(FmlRef f);

    // Encode all pending_fmls_ (run simplifier first if preprocess_passes_ > 0).
    void flush_pending_fmls();

    // True iff f is an atom or negated atom (usable as a SAT literal directly).
    bool is_literal_fml(FmlRef f) const;

    // Assert: if all literals in conds are true, then f must hold.
    void encode_conditioned(FmlRef f, const std::vector<int>& conds);

    // Assert: if all conds hold, at least one child in children must hold.
    // Introduces a fresh selector variable to binary-split when a child is non-literal.
    void encode_or_conditioned(const std::vector<FmlRef>& children,
                                std::vector<int> conds);

    // ── Model extraction ─────────────────────────────────────────────────
    SolveResult last_result_ = SolveResult::UNKNOWN;

    // Record of one function application seen during parsing (for get-model).
    struct AppRecord {
        std::vector<NodeId> args;     // original (unflattened) NodeIds
        NodeId              app_node; // original (unflattened) NodeId of the application
    };
    // Per user-declared symbol: all distinct applications seen during parsing.
    std::unordered_map<SymbolId, std::vector<AppRecord>> fn_applications_;
    // Deduplication set: NodeIds already recorded in fn_applications_.
    std::unordered_set<NodeId> seen_app_nodes_;

    // Print (model ...) to stdout using CC representatives and SAT model values.
    void print_model();
};

} // namespace llm2smt
