#include "parser/smt2_visitor.h"

#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

#include "preprocessor/simplifier.h"

namespace llm2smt {

Smt2Visitor::Smt2Visitor(SmtContext& ctx, int preprocess_passes, bool flatten,
                         Stats& stats)
    : ctx_(ctx), preprocess_passes_(preprocess_passes), flatten_(flatten),
      stats_(stats) {}

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

NodeId Smt2Visitor::get_bool_term_node(bool val)
{
    // Create both nodes together on first call.
    if (true_node_ == NULL_NODE) {
        SymbolId st = ctx_.nm.declare_symbol("__bool_true",  0);
        true_node_  = ctx_.nm.mk_const(st);
        SymbolId sf = ctx_.nm.declare_symbol("__bool_false", 0);
        false_node_ = ctx_.nm.mk_const(sf);
        // Axiom: true ≠ false — the SAT literal for (true = false) is forced false.
        int eq_var = ctx_.euf.register_equality(true_node_, false_node_);
        std::array<int,1> cl = {-eq_var};
        ctx_.sat.add_clause(std::span<const int>(cl));
    }
    return val ? true_node_ : false_node_;
}

// Add SAT clauses that bridge a Bool-sorted EUF node to __bool_true/__bool_false:
//   lit → (node = true_n)    as  {-lit, eq_true}
//   ¬lit → (node = false_n)  as  { lit, eq_false}
// This is what lets the EUF theory "see" the SAT assignment for Bool-sorted
// symbols that appear as arguments to uninterpreted functions.
void Smt2Visitor::link_bool_term_to_euf(NodeId node)
{
    if (!linked_bool_terms_.insert(node).second) return;  // already linked
    NodeId true_n  = get_bool_term_node(true);
    NodeId false_n = get_bool_term_node(false);
    int lit      = ctx_.lit_for_node(node);
    int eq_true  = ctx_.euf.register_equality(node, true_n);
    int eq_false = ctx_.euf.register_equality(node, false_n);
    // Forward implications: SAT value of node drives EUF equalities.
    { std::array<int,2> cl = {-lit,  eq_true};  ctx_.sat.add_clause(std::span<const int>(cl)); }
    { std::array<int,2> cl = { lit,  eq_false}; ctx_.sat.add_clause(std::span<const int>(cl)); }
    // Mutual exclusivity: SAT solver must not assert both equalities simultaneously.
    // Without this, the solver can freely set both eq_true and eq_false to TRUE,
    // causing CC to merge __bool_true with __bool_false and producing false conflicts.
    { std::array<int,2> cl = {-eq_true, -eq_false}; ctx_.sat.add_clause(std::span<const int>(cl)); }
}

// ============================================================================
// Sort detection helper
// ============================================================================

bool Smt2Visitor::is_bool_sorted(
    smt2parser::SMTLIBv2Parser::TermContext* ctx) const
{
    if (ctx->GRW_Exclamation()) return is_bool_sorted(ctx->term()[0]);
    if (ctx->qual_identifier() == nullptr) return false;
    std::string name = identifier_name(ctx->qual_identifier()->identifier());
    // ite is polymorphic (Bool × α × α → α); check the branch sort.
    if (name == "ite" && ctx->term().size() == 3)
        return is_bool_sorted(ctx->term()[1]);
    static const std::unordered_set<std::string> bool_ops = {
        "not", "and", "or", "=>", "xor", "true", "false", "=", "distinct"
    };
    if (bool_ops.count(name)) return true;
    if (defined_bool_fns_.count(name)) return true;
    auto fit = ctx_.declared_fns.find(name);
    return fit != ctx_.declared_fns.end() && ctx_.bool_fns.count(fit->second);
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
    else if (ctx->cmd_defineFun()) {
        auto* fdef = ctx->function_def();
        std::string name = fdef->symbol()->getText();
        if (!fdef->sorted_var().empty())
            throw std::runtime_error("define-fun with parameters not supported: " + name);
        std::string ret_sort = fdef->sort()->getText();
        defined_fns_[name] = fdef->term();
        if (ret_sort == "Bool") defined_bool_fns_.insert(name);
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
        // Record declaration order and sort info for get-model
        FnDecl decl;
        decl.sym = sym;
        if (!sorts.empty()) {
            decl.return_sort = sorts.back()->getText();
            for (size_t i = 0; i + 1 < sorts.size(); ++i)
                decl.param_sorts.push_back(sorts[i]->getText());
        }
        ctx_.declared_fn_order.push_back(std::move(decl));
    }
    else if (ctx->cmd_assert()) {
        auto terms = ctx->term();
        if (terms.empty()) throw std::runtime_error("assert: missing term");
        if (preprocess_passes_ > 0)
            pending_fmls_.push_back(build_fml(terms[0]));
        else
            assert_formula(terms[0]);
    }
    else if (ctx->cmd_checkSat()) {
        flush_pending_fmls();
        last_result_ = ctx_.sat.solve();
        switch (last_result_) {
        case SolveResult::SAT:     std::cout << "sat\n";     break;
        case SolveResult::UNSAT:   std::cout << "unsat\n";   break;
        case SolveResult::UNKNOWN: std::cout << "unknown\n"; break;
        }
    }
    else if (ctx->cmd_getModel()) {
        if (last_result_ == SolveResult::SAT)
            print_model();
        else
            std::cerr << "(error \"get-model called before a satisfying check-sat\")\n";
    }
    return nullptr;
}

// ============================================================================
// Term parsing (U-sorted)
// ============================================================================

NodeId Smt2Visitor::visit_term(
    smt2parser::SMTLIBv2Parser::TermContext* ctx)
{
    // (! term :attr...) — strip annotation
    if (ctx->GRW_Exclamation()) return visit_term(ctx->term()[0]);

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

    // Bool constants used as U-sorted terms (e.g. argument to a UF that takes Bool).
    if (name == "true")  return get_bool_term_node(true);
    if (name == "false") return get_bool_term_node(false);

    // Compound Bool-sorted expression (built-in operator: and, or, not, =, ite
    // with Bool branches, etc.) used in a U-sorted position, e.g. (wrap (and p q)).
    // Only fires for names not in declared_fns (built-in operators have no UF entry).
    // Introduce a fresh EUF constant bridged to __bool_true/__bool_false so the EUF
    // theory observes the SAT-level truth value of the compound formula.
    if (ctx_.declared_fns.find(name) == ctx_.declared_fns.end() && is_bool_sorted(ctx)) {
        auto cit = ite_node_cache_.find(ctx);
        if (cit != ite_node_cache_.end()) return cit->second;
        int lit = eval_lit(ctx);
        SymbolId fresh = ctx_.nm.declare_symbol(
            "__bool_fml_" + std::to_string(ite_counter_++), 0);
        NodeId node = ctx_.nm.mk_const(fresh);
        ite_node_cache_[ctx] = node;
        // Record lit so bool_for() can read the truth value for get-model output
        // (the node is U-sorted but node_to_lit is NodeId→int with no sort restriction).
        ctx_.node_to_lit[node] = lit;
        NodeId true_n  = get_bool_term_node(true);
        NodeId false_n = get_bool_term_node(false);
        int eq_true  = ctx_.euf.register_equality(node, true_n);
        int eq_false = ctx_.euf.register_equality(node, false_n);
        { std::array<int,2> cl = {-lit, eq_true};  ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,2> cl = { lit, eq_false}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,2> cl = {-eq_true, -eq_false}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        return node;
    }

    // U-sorted (ite cond t-then t-else): introduce a fresh EUF constant r with
    // conditional equalities  cond→r=then  and  ¬cond→r=else.
    if (name == "ite" && ctx->term().size() == 3) {
        auto cit = ite_node_cache_.find(ctx);
        if (cit != ite_node_cache_.end()) return cit->second;
        int cond_lit    = eval_lit(ctx->term()[0]);
        NodeId then_node = visit_term(ctx->term()[1]);
        NodeId else_node = visit_term(ctx->term()[2]);
        SymbolId fresh = ctx_.nm.declare_symbol(
            "__ite_" + std::to_string(ite_counter_++), 0);
        NodeId result = ctx_.nm.mk_const(fresh);
        ite_node_cache_[ctx] = result;
        int eq_then = ctx_.euf.register_equality(result, then_node);
        { std::array<int,2> cl = {-cond_lit, eq_then}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        int eq_else = ctx_.euf.register_equality(result, else_node);
        { std::array<int,2> cl = { cond_lit, eq_else}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        return result;
    }

    auto fit = ctx_.declared_fns.find(name);
    if (fit == ctx_.declared_fns.end())
        throw std::runtime_error("Undeclared symbol: " + name);
    SymbolId sym = fit->second;

    if (ctx->term().empty()) {
        NodeId node = ctx_.nm.mk_const(sym);
        if (ctx_.bool_fns.count(sym)) link_bool_term_to_euf(node);
        return node;
    }

    std::vector<NodeId> args;
    for (auto* sub : ctx->term())
        args.push_back(visit_term(sub));
    NodeId node = ctx_.nm.mk_app(sym, std::span<const NodeId>(args));
    if (ctx_.bool_fns.count(sym)) link_bool_term_to_euf(node);
    // Record for get-model (dedup via hash-consed NodeId)
    if (seen_app_nodes_.insert(node).second)
        fn_applications_[sym].push_back({args, node});
    return node;
}

// ============================================================================
// Formula parsing
// ============================================================================

// Add all SAT clauses for "this formula must hold".
void Smt2Visitor::assert_formula(
    smt2parser::SMTLIBv2Parser::TermContext* ctx)
{
    // (! term :attr...) — strip annotation
    if (ctx->GRW_Exclamation()) { assert_formula(ctx->term()[0]); return; }

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

        // (= Bool Bool) — propositional biconditional: (p→q) ∧ (q→p)
        if (op == "=" && ctx->term().size() == 2 &&
            (is_bool_sorted(ctx->term()[0]) || is_bool_sorted(ctx->term()[1]))) {
            int p = eval_lit(ctx->term()[0]);
            int q = eval_lit(ctx->term()[1]);
            std::array<int, 2> c1 = {-p,  q};
            std::array<int, 2> c2 = { p, -q};
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

        // 0-arity define-fun macro: expand body inline so the top-level
        // structure (and, or, …) is handled structurally, not via Tseitin.
        if (ctx->term().empty()) {
            auto dit = defined_fns_.find(op);
            if (dit != defined_fns_.end() && defined_bool_fns_.count(op)) {
                assert_formula(dit->second);
                return;
            }
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
    // (! term :attr...) — strip annotation
    if (ctx->GRW_Exclamation()) { collect_clause_lits(ctx->term()[0], lits); return; }

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
    // (! term :attr...) — strip annotation
    if (ctx->GRW_Exclamation()) return eval_lit(ctx->term()[0]);

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
        // Bool-Bool equality is propositional biconditional, not a theory atom.
        if (is_bool_sorted(ctx->term()[0]) || is_bool_sorted(ctx->term()[1])) {
            auto cit = tseitin_cache_.find(ctx);
            if (cit != tseitin_cache_.end()) return cit->second;
            int x = ctx_.euf.new_var();
            tseitin_cache_[ctx] = x;
            int p = eval_lit(ctx->term()[0]);
            int q = eval_lit(ctx->term()[1]);
            // x ↔ (p ↔ q)
            { std::array<int,3> cl = {-x, -p,  q}; ctx_.sat.add_clause(std::span<const int>(cl)); }
            { std::array<int,3> cl = {-x,  p, -q}; ctx_.sat.add_clause(std::span<const int>(cl)); }
            { std::array<int,3> cl = {-p, -q,  x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
            { std::array<int,3> cl = { p,  q,  x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
            return x;
        }
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

    // (distinct t1 t2 ... tn) n≥3 in literal position — Tseitin proxy
    // x ↔ ∧_{i<j} (t_i ≠ t_j)
    if (op == "distinct") {
        auto cit = tseitin_cache_.find(ctx);
        if (cit != tseitin_cache_.end()) return cit->second;
        int x = ctx_.euf.new_var();
        tseitin_cache_[ctx] = x;
        std::vector<NodeId> nodes;
        for (auto* t : ctx->term()) nodes.push_back(visit_term(t));
        std::vector<int> eq_lits;
        for (size_t i = 0; i < nodes.size(); ++i) {
            for (size_t j = i + 1; j < nodes.size(); ++j) {
                int eq = ctx_.euf.register_equality(nodes[i], nodes[j]);
                eq_lits.push_back(eq);
                // x → (t_i ≠ t_j): ¬x ∨ ¬eq
                std::array<int,2> cl = {-x, -eq};
                ctx_.sat.add_clause(std::span<const int>(cl));
            }
        }
        // (∀ pairs equal) → ¬x (contrapositive: x → ∃ pair distinct)
        // Combined as: x ∨ eq₁ ∨ eq₂ ∨ … (any equality falsifies x)
        std::vector<int> bwd = {x};
        for (int eq : eq_lits) bwd.push_back(eq);
        ctx_.sat.add_clause(std::span<const int>(bwd));
        return x;
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
            link_bool_term_to_euf(n);
            return ctx_.lit_for_node(n);
        }
        // 0-arity define-fun macro expansion
        {
            auto dit = defined_fns_.find(op);
            if (dit != defined_fns_.end() && defined_bool_fns_.count(op))
                return eval_lit(dit->second);
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
        link_bool_term_to_euf(n);
        // Record for get-model (dedup via hash-consed NodeId)
        if (seen_app_nodes_.insert(n).second)
            fn_applications_[fit->second].push_back({args, n});
        return ctx_.lit_for_node(n);
    }

    throw std::runtime_error(
        "Unsupported formula: " + op
        + " (supported: true, false, not, =>, and, or, xor, ite, =, distinct, predicates)");
}

// ============================================================================
// Formula building (parse-tree → FmlRef)
// ============================================================================

FmlRef Smt2Visitor::build_fml(
    smt2parser::SMTLIBv2Parser::TermContext* ctx)
{
    if (ctx->GRW_Exclamation()) return build_fml(ctx->term()[0]);

    if (ctx->GRW_Let()) {
        let_env_.emplace_back();
        for (auto* vb : ctx->var_binding())
            let_env_.back()[vb->symbol()->getText()] = vb->term();
        FmlRef result = build_fml(ctx->term()[0]);
        let_env_.pop_back();
        return result;
    }

    if (ctx->qual_identifier() == nullptr)
        throw std::runtime_error("Unsupported formula form in build_fml");

    std::string op = identifier_name(ctx->qual_identifier()->identifier());

    // Boolean constants
    if (op == "true")  return fml_true();
    if (op == "false") return fml_false();

    // Connectives
    if (op == "not" && ctx->term().size() == 1)
        return fml_not(build_fml(ctx->term()[0]));

    if (op == "and") {
        std::vector<FmlRef> ch;
        for (auto* sub : ctx->term()) ch.push_back(build_fml(sub));
        return fml_and(std::move(ch));
    }

    if (op == "or") {
        std::vector<FmlRef> ch;
        for (auto* sub : ctx->term()) ch.push_back(build_fml(sub));
        return fml_or(std::move(ch));
    }

    // (=> A B ...) right-assoc: flatten to Or(Not(A), Not(B), ..., last)
    if (op == "=>") {
        auto terms = ctx->term();
        std::vector<FmlRef> disj;
        for (size_t i = 0; i + 1 < terms.size(); ++i)
            disj.push_back(fml_not(build_fml(terms[i])));
        disj.push_back(build_fml(terms.back()));
        return fml_or(std::move(disj));
    }

    if (op == "xor" && ctx->term().size() == 2)
        return fml_xor(build_fml(ctx->term()[0]), build_fml(ctx->term()[1]));

    if (op == "ite" && ctx->term().size() == 3 && is_bool_sorted(ctx))
        return fml_ite(build_fml(ctx->term()[0]),
                       build_fml(ctx->term()[1]),
                       build_fml(ctx->term()[2]));

    // (= Bool Bool) — biconditional
    if (op == "=" && ctx->term().size() == 2 &&
        (is_bool_sorted(ctx->term()[0]) || is_bool_sorted(ctx->term()[1])))
        return fml_booleq(build_fml(ctx->term()[0]), build_fml(ctx->term()[1]));

    // (= t1 t2) — EUF equality atom: evaluate both sub-terms eagerly
    if (op == "=" && ctx->term().size() == 2) {
        NodeId lhs = visit_term(ctx->term()[0]);
        NodeId rhs = visit_term(ctx->term()[1]);
        return fml_eq(lhs, rhs);
    }

    // (distinct t1 t2) — single disequality
    if (op == "distinct" && ctx->term().size() == 2) {
        NodeId lhs = visit_term(ctx->term()[0]);
        NodeId rhs = visit_term(ctx->term()[1]);
        return fml_not(fml_eq(lhs, rhs));
    }

    // (distinct t1 t2 ... tn) — expand to pairwise And(Not(Eq(...)))
    if (op == "distinct") {
        auto terms = ctx->term();
        std::vector<NodeId> nodes;
        nodes.reserve(terms.size());
        for (auto* sub : terms) nodes.push_back(visit_term(sub));
        std::vector<FmlRef> pairs;
        for (size_t i = 0; i < nodes.size(); ++i)
            for (size_t j = i + 1; j < nodes.size(); ++j)
                pairs.push_back(fml_not(fml_eq(nodes[i], nodes[j])));
        return fml_and(std::move(pairs));
    }

    // Let variable reference (0-ary, not a declared symbol)
    if (ctx->term().empty()) {
        for (auto it = let_env_.rbegin(); it != let_env_.rend(); ++it) {
            auto jt = it->find(op);
            if (jt != it->end()) return build_fml(jt->second);
        }
    }

    // Bool-sorted 0-ary or n-ary predicate application — Pred atom.
    // visit_term handles node creation and link_bool_term_to_euf eagerly.
    {
        auto fit = ctx_.declared_fns.find(op);
        if (fit != ctx_.declared_fns.end() && ctx_.bool_fns.count(fit->second)) {
            if (ctx->term().empty()) {
                NodeId n = ctx_.nm.mk_const(fit->second);
                link_bool_term_to_euf(n);
                return fml_pred(n);
            }
            std::vector<NodeId> args;
            for (auto* sub : ctx->term()) args.push_back(visit_term(sub));
            NodeId n = ctx_.nm.mk_app(fit->second, std::span<const NodeId>(args));
            link_bool_term_to_euf(n);
            if (seen_app_nodes_.insert(n).second)
                fn_applications_[fit->second].push_back({args, n});
            return fml_pred(n);
        }
    }

    // 0-arity define-fun macro expansion
    if (ctx->term().empty()) {
        auto dit = defined_fns_.find(op);
        if (dit != defined_fns_.end() && defined_bool_fns_.count(op))
            return build_fml(dit->second);
    }

    throw std::runtime_error("Unsupported formula in build_fml: " + op);
}

// ============================================================================
// Formula encoding (FmlRef → SAT clauses)
// ============================================================================

// Return a SAT literal for a sub-formula; introduce Tseitin variable if needed.
int Smt2Visitor::lit_of_fml(FmlRef f)
{
    switch (f->kind) {
    case FmlKind::True:  return get_true_lit();
    case FmlKind::False: return -get_true_lit();
    case FmlKind::Eq:    return ctx_.euf.register_equality(f->eq_lhs, f->eq_rhs);
    case FmlKind::Pred:  return ctx_.lit_for_node(f->pred);
    case FmlKind::Not:
        return -lit_of_fml(f->children[0]);
    default:
        break;
    }

    // Compound — check Tseitin cache first.
    auto cit = fml_lit_cache_.find(f.get());
    if (cit != fml_lit_cache_.end()) return cit->second;
    int x = ctx_.euf.new_var();
    fml_lit_cache_[f.get()] = x;

    switch (f->kind) {
    case FmlKind::And: {
        std::vector<int> sub;
        for (auto& ch : f->children) sub.push_back(lit_of_fml(ch));
        for (int l : sub) { std::array<int,2> cl = {-x, l}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        std::vector<int> bwd = {x};
        for (int l : sub) bwd.push_back(-l);
        ctx_.sat.add_clause(std::span<const int>(bwd));
        break;
    }
    case FmlKind::Or: {
        std::vector<int> sub;
        for (auto& ch : f->children) sub.push_back(lit_of_fml(ch));
        for (int l : sub) { std::array<int,2> cl = {-l, x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        std::vector<int> fwd = {-x};
        for (int l : sub) fwd.push_back(l);
        ctx_.sat.add_clause(std::span<const int>(fwd));
        break;
    }
    case FmlKind::Ite: {
        int c = lit_of_fml(f->children[0]);
        int t = lit_of_fml(f->children[1]);
        int e = lit_of_fml(f->children[2]);
        { std::array<int,3> cl = {-c,-t, x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,3> cl = {-c, t,-x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,3> cl = { c,-e, x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,3> cl = { c, e,-x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        break;
    }
    case FmlKind::Implies: {
        int a = lit_of_fml(f->children[0]);
        int b = lit_of_fml(f->children[1]);
        // x ↔ (¬a ∨ b)
        { std::array<int,2> cl = { a, x};   ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,2> cl = {-b, x};   ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,3> cl = {-x,-a, b}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        break;
    }
    case FmlKind::Xor: {
        int a = lit_of_fml(f->children[0]);
        int b = lit_of_fml(f->children[1]);
        { std::array<int,3> cl = {-x, a, b}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,3> cl = {-x,-a,-b}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,3> cl = {-a, b, x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,3> cl = { a,-b, x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        break;
    }
    case FmlKind::BoolEq: {
        int p = lit_of_fml(f->children[0]);
        int q = lit_of_fml(f->children[1]);
        { std::array<int,3> cl = {-x,-p, q}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,3> cl = {-x, p,-q}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,3> cl = {-p,-q, x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,3> cl = { p, q, x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        break;
    }
    default:
        throw std::runtime_error("lit_of_fml: unexpected kind");
    }
    return x;
}

// Assert a FmlRef at the top level (add required SAT clauses).
void Smt2Visitor::encode_fml(FmlRef f)
{
    switch (f->kind) {
    case FmlKind::True:  return;
    case FmlKind::False: ctx_.sat.add_clause(std::span<const int>{}); return;
    case FmlKind::Eq: {
        int l = ctx_.euf.register_equality(f->eq_lhs, f->eq_rhs);
        std::array<int,1> cl = {l};
        ctx_.sat.add_clause(std::span<const int>(cl));
        return;
    }
    case FmlKind::Pred: {
        std::array<int,1> cl = {ctx_.lit_for_node(f->pred)};
        ctx_.sat.add_clause(std::span<const int>(cl));
        return;
    }
    case FmlKind::Not: {
        std::array<int,1> cl = {-lit_of_fml(f->children[0])};
        ctx_.sat.add_clause(std::span<const int>(cl));
        return;
    }
    case FmlKind::And:
        for (auto& ch : f->children) encode_fml(ch);
        return;
    case FmlKind::Or: {
        std::vector<int> lits;
        for (auto& ch : f->children) lits.push_back(lit_of_fml(ch));
        ctx_.sat.add_clause(std::span<const int>(lits));
        return;
    }
    case FmlKind::Ite: {
        int c = lit_of_fml(f->children[0]);
        int t = lit_of_fml(f->children[1]);
        int e = lit_of_fml(f->children[2]);
        { std::array<int,2> cl = {-c, t}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,2> cl = { c, e}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        return;
    }
    case FmlKind::Implies: {
        int a = lit_of_fml(f->children[0]);
        int b = lit_of_fml(f->children[1]);
        std::array<int,2> cl = {-a, b};
        ctx_.sat.add_clause(std::span<const int>(cl));
        return;
    }
    case FmlKind::Xor: {
        int a = lit_of_fml(f->children[0]);
        int b = lit_of_fml(f->children[1]);
        { std::array<int,2> cl = {a, b};   ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,2> cl = {-a, -b}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        return;
    }
    case FmlKind::BoolEq: {
        int p = lit_of_fml(f->children[0]);
        int q = lit_of_fml(f->children[1]);
        { std::array<int,2> cl = {-p, q}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,2> cl = { p,-q}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        return;
    }
    }
}

// Run simplifier (if enabled), assert forced atoms, encode remaining formulas.
void Smt2Visitor::flush_pending_fmls()
{
    if (pending_fmls_.empty()) return;

    if (preprocess_passes_ > 0) {
        stats_.preproc_fmls_in += static_cast<uint64_t>(pending_fmls_.size());

        Simplifier simp;
        simp.set_flatten(flatten_);
        simp.run(pending_fmls_, preprocess_passes_);

        stats_.preproc_passes_run    += static_cast<uint64_t>(simp.passes_run());
        stats_.preproc_forced_atoms  += static_cast<uint64_t>(simp.forced_atoms().size());
        for (const auto& f : pending_fmls_) {
            if (f->kind == FmlKind::True)  ++stats_.preproc_fmls_true_out;
            if (f->kind == FmlKind::False) ++stats_.preproc_fmls_false_out;
        }

        // Assert every atom that was forced by unit propagation.
        // Positive Eq atoms are merged directly in the CC (no SAT variable
        // needed — the CC carries the merge permanently at level 0, and the
        // SAT solver never has to decide or undo it).  All other forced atoms
        // are still asserted as SAT unit clauses.
        for (auto& [atom, positive] : simp.forced_atoms()) {
            if (atom->kind == FmlKind::Eq && positive) {
                ctx_.euf.register_permanent_equality(atom->eq_lhs, atom->eq_rhs);
            } else {
                int lit = (atom->kind == FmlKind::Eq)
                          ? ctx_.euf.register_equality(atom->eq_lhs, atom->eq_rhs)
                          : ctx_.lit_for_node(atom->pred);
                int forced = positive ? lit : -lit;
                std::array<int,1> cl = {forced};
                ctx_.sat.add_clause(std::span<const int>(cl));
            }
        }
    }

    for (auto& f : pending_fmls_)
        encode_fml(f);
    pending_fmls_.clear();
    fml_lit_cache_.clear();
}

// ============================================================================
// Model printing
// ============================================================================

void Smt2Visitor::print_model()
{
    Flattener& flattener = ctx_.euf.flattener();
    CC&        cc        = ctx_.euf.cc();

    // Map CC representative → abstract value index (assigned lazily).
    std::unordered_map<NodeId, int> repr_to_idx;
    int next_abstract = 0;

    // Return (or assign) the abstract value index for an original node.
    auto abstract_for = [&](NodeId original) -> int {
        NodeId flat = flattener.get_flat(original);
        NodeId repr = (flat != NULL_NODE) ? cc.find(flat) : original;
        auto [it, inserted] = repr_to_idx.emplace(repr, 0);
        if (inserted) it->second = next_abstract++;
        return it->second;
    };

    // Return "true" or "false" for a Bool-valued node using the SAT model.
    auto bool_for = [&](NodeId node) -> std::string {
        auto it = ctx_.node_to_lit.find(node);
        if (it == ctx_.node_to_lit.end()) return "false";
        int v = ctx_.sat.val(it->second);
        return (v > 0) ? "true" : "false";
    };

    // Format an abstract value with sort annotation.
    auto as_val = [](int idx, const std::string& sort) -> std::string {
        return "(as @" + std::to_string(idx) + " " + sort + ")";
    };

    std::cout << "(model\n";

    for (const auto& decl : ctx_.declared_fn_order) {
        SymbolId           sym      = decl.sym;
        const std::string& ret_sort = decl.return_sort;
        bool               ret_bool = (ret_sort == "Bool");
        size_t             arity    = decl.param_sorts.size();
        const std::string  sym_name = ctx_.nm.symbol_table().get(sym).name;

        // Print function header: (define-fun name (params) return-sort
        std::cout << "  (define-fun " << sym_name << " (";
        for (size_t i = 0; i < arity; ++i) {
            if (i > 0) std::cout << " ";
            std::cout << "(x!" << i << " " << decl.param_sorts[i] << ")";
        }
        std::cout << ") " << ret_sort << "\n";

        if (arity == 0) {
            // Constant: look up its model value directly.
            NodeId node = ctx_.nm.mk_const(sym);
            if (ret_bool) {
                std::cout << "    " << bool_for(node) << ")\n";
            } else {
                std::cout << "    " << as_val(abstract_for(node), ret_sort) << ")\n";
            }
        } else {
            // Function: build ite-chain over seen applications.

            // Helper: format result value for an application node.
            auto ret_val_for = [&](NodeId app_node) -> std::string {
                if (ret_bool) return bool_for(app_node);
                return as_val(abstract_for(app_node), ret_sort);
            };

            // Helper: build the condition string "(= x!i <abstract-val-of-arg>)"
            //         or "(and (= x!0 ...) (= x!1 ...) ...)" for multiple args.
            auto cond_for = [&](const AppRecord& app) -> std::string {
                auto arg_val = [&](size_t i) -> std::string {
                    bool arg_bool = (decl.param_sorts[i] == "Bool");
                    if (arg_bool) {
                        // true_node_ / false_node_ are U-sorted EUF constants used
                        // as stand-ins for the Bool literals true/false when they
                        // appear as UF arguments.  They are NOT in node_to_lit, so
                        // bool_for() would return "false" for both — wrong.
                        if (app.args[i] == true_node_)  return "true";
                        if (app.args[i] == false_node_) return "false";
                        return bool_for(app.args[i]);  // user-declared Bool node
                    }
                    return as_val(abstract_for(app.args[i]), decl.param_sorts[i]);
                };
                if (arity == 1) {
                    return "(= x!0 " + arg_val(0) + ")";
                }
                std::string cond = "(and";
                for (size_t i = 0; i < arity; ++i)
                    cond += " (= x!" + std::to_string(i) + " " + arg_val(i) + ")";
                cond += ")";
                return cond;
            };

            auto apps_it = fn_applications_.find(sym);
            if (apps_it == fn_applications_.end() || apps_it->second.empty()) {
                // No applications seen — output a constant default value.
                if (ret_bool)
                    std::cout << "    false)\n";
                else
                    std::cout << "    " << as_val(next_abstract++, ret_sort) << ")\n";
            } else {
                const auto& apps = apps_it->second;

                // Collect (condition, value) pairs, deduplicating by condition string.
                struct Entry { std::string cond, val; };
                std::vector<Entry>              entries;
                std::unordered_set<std::string> seen_conds;
                for (const auto& app : apps) {
                    std::string cond = cond_for(app);
                    if (!seen_conds.insert(cond).second) continue;
                    entries.push_back({cond, ret_val_for(app.app_node)});
                }

                // Build nested ite-chain; the first entry's value is the default.
                // entries is always non-empty when apps is non-empty.
                std::string body = entries[0].val;
                for (int i = (int)entries.size() - 1; i >= 1; --i) {
                    body = "(ite " + entries[i].cond + "\n        "
                         + entries[i].val + "\n        " + body + ")";
                }
                std::cout << "    " << body << ")\n";
            }
        }
    }

    std::cout << ")\n";
}

} // namespace llm2smt
