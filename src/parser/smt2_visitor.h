#pragma once

#include <any>
#include <cstdint>
#include <optional>
#include <span>
#include <string>
#include <utility>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "SMTLIBv2BaseVisitor.h"
#include "SMTLIBv2Parser.h"

#include "core/node.h"
#include "core/stats.h"
#include "parser/smt_context.h"
#include "preprocessor/preproc_options.h"
#include "theories/lra/lra_solver.h"

namespace llm2smt {

class Smt2Visitor : public smt2parser::SMTLIBv2BaseVisitor {
public:
    explicit Smt2Visitor(SmtContext& ctx, PreprocOptions opts, Stats& stats);

    std::any visitStart(smt2parser::SMTLIBv2Parser::StartContext*) override;
    std::any visitCommand(smt2parser::SMTLIBv2Parser::CommandContext*) override;

    SolveResult                  last_result() const { return last_result_; }
    const std::vector<NodeId>& proof_fmls()  const { return proof_fmls_; }

private:
    SmtContext& ctx_;

    // Let environment: stack of (variable-name → bound TermContext* plus lazy
    // NodeId caches). Formula and term uses are cached separately because a
    // Bool expression in formula position is a SAT formula, while the same
    // expression in U-sorted position may need EUF Bool-value bridging.
    struct LetBinding {
        smt2parser::SMTLIBv2Parser::TermContext* term = nullptr;
        NodeId term_node = NULL_NODE;
        NodeId fml_node = NULL_NODE;
    };
    using LetFrame = std::unordered_map<std::string, LetBinding>;
    std::vector<LetFrame> let_env_;
    LetBinding* find_let_binding(const std::string& name);
    const LetBinding* find_let_binding(const std::string& name) const;

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

    // Symbol → return sort name; populated from declare-fun commands and
    // from internal __ite_N node creation (so that nested ITEs can look up
    // the sort of their branches).
    std::unordered_map<SymbolId, std::string> sym_to_sort_;

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
    bool compute_is_bool_sorted(smt2parser::SMTLIBv2Parser::TermContext*) const;
    mutable std::unordered_map<smt2parser::SMTLIBv2Parser::TermContext*, bool>
        bool_sort_cache_;

    // ── Preprocessing ─────────────────────────────────────────────────────
    PreprocOptions opts_;
    Stats&         stats_;

    // NodeId assertions accumulated during parsing (when preprocessing is on).
    std::vector<NodeId> pending_fmls_;

    // Original (pre-NNF, pre-simplification) assertions for proof output.
    std::vector<NodeId> proof_fmls_;

    // Cache: NodeId formula → Tseitin SAT literal (for lit_of_fml reuse).
    std::unordered_map<NodeId, int> fml_lit_cache_;

    // Top-level asserted disequalities, keyed as unordered NodeId pairs.
    // Used to strengthen finite-domain "x equals one of these distinct values"
    // disjunctions with SAT-level at-most-one clauses.
    struct EqEndpointLit { NodeId other; int lit; };
    struct FiniteDomainInfo {
        std::vector<NodeId> values;
        std::vector<int>    choice_lits;
    };
    std::unordered_set<uint64_t> top_level_diseq_pairs_;
    std::unordered_set<uint64_t> finite_domain_amo_seen_;
    std::unordered_set<int> finite_domain_eq_lits_seen_;
    std::unordered_map<NodeId, std::vector<EqEndpointLit>> finite_domain_eqs_by_endpoint_;
    std::unordered_map<NodeId, FiniteDomainInfo> finite_domain_terms_;
    std::unordered_set<uint64_t> finite_domain_eq_defs_seen_;

    // Build a NodeId formula from a Bool-sorted parse-tree node.
    // Eagerly calls visit_term for U-sorted sub-terms.
    NodeId build_fml(smt2parser::SMTLIBv2Parser::TermContext*);

    // Assert a NodeId formula by adding the required SAT clauses (top-level assertion).
    void encode_fml(NodeId f);

    // Return (or create) a SAT literal equivalent to a NodeId sub-formula.
    int lit_of_fml(NodeId f);

    // Encode all pending_fmls_ (run simplifier first if preprocess_passes_ > 0).
    void flush_pending_fmls();

    void collect_top_level_disequalities(NodeId f);
    void collect_finite_domain_terms(NodeId f);
    void encode_finite_domain_eq_defs(NodeId f);
    void remember_finite_domain_eq_lit(NodeId lhs, NodeId rhs, int lit);
    bool known_equality_lit(NodeId lhs, NodeId rhs, int& lit);

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

    // ── QF_LRA parse-tree encoding ───────────────────────────────────────
    bool is_lra_mode() const { return ctx_.is_lra_logic(); }
    bool is_real_decl(const std::string& name) const;
    lra::LinearExpr lra_term(smt2parser::SMTLIBv2Parser::TermContext*);
    int lra_eval_lit(smt2parser::SMTLIBv2Parser::TermContext*);
    void lra_assert_formula(smt2parser::SMTLIBv2Parser::TermContext*);
    void lra_collect_clause_lits(smt2parser::SMTLIBv2Parser::TermContext*, std::vector<int>&);
    lra::Rational lra_number(smt2parser::SMTLIBv2Parser::TermContext*) const;
    std::optional<lra::Rational> lra_const_value(smt2parser::SMTLIBv2Parser::TermContext*) const;
    bool is_lra_number_term(smt2parser::SMTLIBv2Parser::TermContext*) const;
    bool is_lra_term_syntax(smt2parser::SMTLIBv2Parser::TermContext*) const;
    bool is_lra_bool_syntax(smt2parser::SMTLIBv2Parser::TermContext*) const;
    int fresh_bool_var();
};

} // namespace llm2smt
