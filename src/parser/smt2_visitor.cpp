#include "parser/smt2_visitor.h"

#include <algorithm>
#include <array>
#include <chrono>
#include <cctype>
#include <functional>
#include <iostream>
#include <ranges>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

#include "preprocessor/disjunction_bridge.h"
#include "preprocessor/nnf.h"
#include "preprocessor/simplifier.h"

namespace llm2smt {

Smt2Visitor::Smt2Visitor(SmtContext& ctx, PreprocOptions opts, Stats& stats)
    : ctx_(ctx), opts_(std::move(opts)), stats_(stats) {}

// ============================================================================
// Helpers
// ============================================================================

Smt2Visitor::LetBinding* Smt2Visitor::find_let_binding(const std::string& name)
{
    for (auto it = let_env_.rbegin(); it != let_env_.rend(); ++it) {
        auto jt = it->find(name);
        if (jt != it->end()) return &jt->second;
    }
    return nullptr;
}

const Smt2Visitor::LetBinding* Smt2Visitor::find_let_binding(const std::string& name) const
{
    for (auto it = let_env_.rbegin(); it != let_env_.rend(); ++it) {
        auto jt = it->find(name);
        if (jt != it->end()) return &jt->second;
    }
    return nullptr;
}

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
    true_lit_ = fresh_bool_var();
    std::array<int, 1> cl = {true_lit_};
    ctx_.sat.add_clause(std::span<const int>(cl));
    return true_lit_;
}

int Smt2Visitor::fresh_bool_var()
{
    return is_lra_mode() && ctx_.lra ? ctx_.lra->new_var() : ctx_.euf.new_var();
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
    auto it = bool_sort_cache_.find(ctx);
    if (it != bool_sort_cache_.end()) return it->second;
    bool result = compute_is_bool_sorted(ctx);
    bool_sort_cache_[ctx] = result;
    return result;
}

bool Smt2Visitor::compute_is_bool_sorted(
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
    if (bool_ops.contains(name)) return true;
    if (defined_bool_fns_.contains(name)) return true;
    auto fit = ctx_.declared_fns.find(name);
    return fit != ctx_.declared_fns.end() && ctx_.bool_fns.contains(fit->second);
}

// ============================================================================
// QF_LRA helpers
// ============================================================================

bool Smt2Visitor::is_real_decl(const std::string& name) const
{
    auto fit = ctx_.declared_fns.find(name);
    if (fit == ctx_.declared_fns.end()) return false;
    auto sit = sym_to_sort_.find(fit->second);
    return sit != sym_to_sort_.end() && sit->second == "Real";
}

bool Smt2Visitor::is_lra_number_term(
    smt2parser::SMTLIBv2Parser::TermContext* t) const
{
    return lra_const_value(t).has_value();
}

lra::Rational Smt2Visitor::lra_number(
    smt2parser::SMTLIBv2Parser::TermContext* t) const
{
    auto v = lra_const_value(t);
    if (!v)
        throw std::runtime_error("expected Real numeral, got: " + t->getText());
    return *v;
}

std::optional<lra::Rational> Smt2Visitor::lra_const_value(
    smt2parser::SMTLIBv2Parser::TermContext* t) const
{
    while (t->GRW_Exclamation()) t = t->term()[0];
    if (t->spec_constant() != nullptr) return lra::Rational::parse(t->getText());
    if (t->qual_identifier() == nullptr) return std::nullopt;
    std::string op = identifier_name(t->qual_identifier()->identifier());
    auto terms = t->term();
    if (op == "-" && terms.size() == 1) {
        auto v = lra_const_value(terms[0]);
        if (!v) return std::nullopt;
        return -*v;
    }
    if (op == "/" && terms.size() == 2) {
        auto a = lra_const_value(terms[0]);
        auto b = lra_const_value(terms[1]);
        if (!a || !b) return std::nullopt;
        return *a / *b;
    }
    if (op == "+" || op == "-" || op == "*") {
        if (terms.empty()) return std::nullopt;
        auto acc = lra_const_value(terms[0]);
        if (!acc) return std::nullopt;
        for (size_t i = 1; i < terms.size(); ++i) {
            auto v = lra_const_value(terms[i]);
            if (!v) return std::nullopt;
            if (op == "+") *acc += *v;
            else if (op == "-") *acc -= *v;
            else *acc *= *v;
        }
        return acc;
    }
    return std::nullopt;
}

bool Smt2Visitor::is_lra_term_syntax(
    smt2parser::SMTLIBv2Parser::TermContext* t) const
{
    while (t->GRW_Exclamation()) t = t->term()[0];
    if (t->spec_constant() != nullptr) return true;
    if (t->qual_identifier() == nullptr) return false;
    std::string op = identifier_name(t->qual_identifier()->identifier());
    if (t->term().empty()) {
        if (auto* binding = find_let_binding(op))
            return is_lra_term_syntax(binding->term);
    }
    if (is_real_decl(op)) return true;
    if (op == "ite")
        return t->term().size() == 3 && is_lra_term_syntax(t->term()[1]);
    static const std::unordered_set<std::string> arith_ops = {"+", "-", "*", "/"};
    return arith_ops.contains(op);
}

bool Smt2Visitor::is_lra_ite_term(
    smt2parser::SMTLIBv2Parser::TermContext* t) const
{
    while (t->GRW_Exclamation()) t = t->term()[0];
    if (t->GRW_Let()) return false;
    if (t->qual_identifier() == nullptr) return false;
    std::string op = identifier_name(t->qual_identifier()->identifier());
    if (t->term().empty()) {
        if (auto* binding = find_let_binding(op))
            return is_lra_ite_term(binding->term);
        return false;
    }
    return op == "ite" && t->term().size() == 3 && is_lra_term_syntax(t);
}

bool Smt2Visitor::is_lra_bool_syntax(
    smt2parser::SMTLIBv2Parser::TermContext* t) const
{
    while (t->GRW_Exclamation()) t = t->term()[0];
    if (t->qual_identifier() == nullptr) return false;
    std::string op = identifier_name(t->qual_identifier()->identifier());
    if (op == "true" || op == "false") return true;
    if (t->term().empty()) {
        if (auto* binding = find_let_binding(op))
            return is_lra_bool_syntax(binding->term);
    }
    static const std::unordered_set<std::string> bool_ops = {
        "not", "and", "or", "=>", "xor", "=", "distinct", "<", "<=", ">", ">="
    };
    if (bool_ops.contains(op) && !is_lra_term_syntax(t)) return true;
    if (t->term().empty()) {
        auto fit = ctx_.declared_fns.find(op);
        return fit != ctx_.declared_fns.end() && ctx_.bool_fns.contains(fit->second);
    }
    return false;
}

std::string Smt2Visitor::lra_expr_key(const lra::LinearExpr& e) const
{
    std::ostringstream os;
    os << e.constant << ":";
    for (const auto& [name, coeff] : e.coeffs) os << name << "=" << coeff << ";";
    return os.str();
}

std::string Smt2Visitor::lra_atom_key(const lra::LinearExpr& e, lra::Relation rel) const
{
    return std::to_string(static_cast<int>(rel)) + ":" + lra_expr_key(e);
}

std::string Smt2Visitor::lra_bool_lit_key(const std::string& op, std::span<const int> lits) const
{
    std::vector<int> canonical(lits.begin(), lits.end());
    if (op == "and" || op == "or" || op == "=" || op == "xor")
        std::ranges::sort(canonical);
    std::ostringstream os;
    os << op << ":";
    for (int lit : canonical) os << lit << ",";
    return os.str();
}

lra::LinearExpr Smt2Visitor::lra_canonical_zero_test(lra::LinearExpr e) const
{
    if (e.coeffs.empty()) return e;
    const auto& first_coeff = e.coeffs.begin()->second;
    if (first_coeff < lra::Rational(0)) e.scale(lra::Rational(-1));
    return e;
}

lra::LinearExpr Smt2Visitor::lra_rewrite_expr(const lra::LinearExpr& e) const
{
    lra::LinearExpr out;
    out.constant = e.constant;
    for (const auto& [name, coeff] : e.coeffs) {
        auto it = lra_eq_elim_subst_.find(name);
        if (it == lra_eq_elim_subst_.end()) {
            out.add_var(name, coeff);
        } else {
            out.add(it->second, coeff);
        }
    }
    return out;
}

std::optional<std::pair<std::string, lra::Rational>>
Smt2Visitor::lra_simple_equality(const lra::LinearExpr& e) const
{
    if (e.coeffs.size() != 1) return std::nullopt;
    const auto& [name, coeff] = *e.coeffs.begin();
    if (coeff.is_zero()) return std::nullopt;
    return std::make_pair(name, -e.constant / coeff);
}

std::optional<std::tuple<std::string, lra::Relation, lra::Rational>>
Smt2Visitor::lra_simple_bound(const lra::LinearExpr& e, lra::Relation rel) const
{
    if (rel == lra::Relation::Eq || rel == lra::Relation::Ne) return std::nullopt;
    if (e.coeffs.size() != 1) return std::nullopt;
    const auto& [name, coeff] = *e.coeffs.begin();
    if (coeff.is_zero()) return std::nullopt;
    lra::Relation out_rel = rel;
    if (coeff < lra::Rational(0)) {
        if (rel == lra::Relation::Le) out_rel = lra::Relation::Ge;
        else if (rel == lra::Relation::Lt) out_rel = lra::Relation::Gt;
        else if (rel == lra::Relation::Ge) out_rel = lra::Relation::Le;
        else if (rel == lra::Relation::Gt) out_rel = lra::Relation::Lt;
    }
    return std::make_tuple(name, out_rel, -e.constant / coeff);
}

std::optional<std::pair<std::string, std::string>>
Smt2Visitor::lra_var_var_equality(const lra::LinearExpr& e) const
{
    if (e.constant != lra::Rational(0) || e.coeffs.size() != 2) return std::nullopt;
    auto it = e.coeffs.begin();
    const auto& [a, ca] = *it++;
    const auto& [b, cb] = *it;
    if (ca == lra::Rational(1) && cb == lra::Rational(-1)) return std::make_pair(a, b);
    if (ca == lra::Rational(-1) && cb == lra::Rational(1)) return std::make_pair(a, b);
    return std::nullopt;
}

bool Smt2Visitor::lra_bound_holds(
    const lra::Rational& choice,
    lra::Relation rel,
    const lra::Rational& bound) const
{
    switch (rel) {
    case lra::Relation::Le: return choice <= bound;
    case lra::Relation::Lt: return choice <  bound;
    case lra::Relation::Ge: return choice >= bound;
    case lra::Relation::Gt: return choice >  bound;
    case lra::Relation::Eq: return choice == bound;
    case lra::Relation::Ne: return choice != bound;
    }
    return false;
}

void Smt2Visitor::lra_encode_finite_domain_bound_defs_for_var(const std::string& var)
{
    if (!opts_.finite_domain_amo || !opts_.lra_finite_domain_bounds) return;
    auto cit = lra_simple_eqs_by_var_.find(var);
    auto bit = lra_bound_lits_by_var_.find(var);
    if (cit == lra_simple_eqs_by_var_.end() || bit == lra_bound_lits_by_var_.end()) return;

    for (const auto& choice : cit->second) {
        for (const auto& bound : bit->second) {
            const std::string key = var + "|" + choice.value_key + "|" +
                std::to_string(static_cast<int>(bound.rel)) + "|" +
                bound.value.str() + "|" + std::to_string(bound.lit);
            if (!lra_finite_domain_bound_defs_seen_.insert(key).second) continue;

            if (lra_bound_holds(choice.value, bound.rel, bound.value)) {
                std::array<int,2> cl = {-choice.lit, bound.lit};
                ctx_.sat.add_clause(std::span<const int>(cl));
            } else {
                std::array<int,2> cl = {-choice.lit, -bound.lit};
                ctx_.sat.add_clause(std::span<const int>(cl));
            }
            ++stats_.preproc_finite_domain_bound_clauses;
        }
    }
}

void Smt2Visitor::lra_remember_bound_lit(
    const std::string& var,
    lra::Relation rel,
    const lra::Rational& value,
    int lit)
{
    const std::string key = var + "|" + std::to_string(static_cast<int>(rel)) + "|" +
        value.str() + "|" + std::to_string(lit);
    if (!lra_bound_lits_seen_.insert(key).second) return;
    lra_bound_lits_by_var_[var].push_back({value, rel, lit});
    lra_encode_finite_domain_bound_defs_for_var(var);
}

void Smt2Visitor::lra_encode_finite_domain_eq_defs_for_pair(
    const std::string& a,
    const std::string& b,
    int eq_lit)
{
    if (!opts_.finite_domain_amo || !opts_.finite_domain_eq_defs ||
        !opts_.lra_finite_domain_eq_defs) return;
    if (a == b) return;
    auto ait = lra_simple_eqs_by_var_.find(a);
    auto bit = lra_simple_eqs_by_var_.find(b);
    if (ait == lra_simple_eqs_by_var_.end() || bit == lra_simple_eqs_by_var_.end()) return;

    const std::string lo = std::min(a, b);
    const std::string hi = std::max(a, b);
    for (const auto& ac : ait->second) {
        for (const auto& bc : bit->second) {
            if (ac.value != bc.value) continue;
            const std::string key = lo + "|" + hi + "|" + std::to_string(eq_lit) + "|" + ac.value_key;
            if (!lra_finite_domain_eq_defs_seen_.insert(key).second) continue;

            { std::array<int,3> cl = {-eq_lit, -ac.lit, bc.lit};
              ctx_.sat.add_clause(std::span<const int>(cl)); }
            { std::array<int,3> cl = {-eq_lit, -bc.lit, ac.lit};
              ctx_.sat.add_clause(std::span<const int>(cl)); }
            stats_.preproc_finite_domain_eq_def_clauses += 2;
        }
    }
}

void Smt2Visitor::lra_remember_var_eq_lit(
    const std::string& a,
    const std::string& b,
    int lit)
{
    lra_var_eq_lits_by_var_[a].push_back({b, lit});
    lra_var_eq_lits_by_var_[b].push_back({a, lit});
    lra_encode_finite_domain_eq_defs_for_pair(a, b, lit);
}

std::optional<bool> Smt2Visitor::lra_const_relation(
    const lra::LinearExpr& e,
    lra::Relation rel) const
{
    if (!e.coeffs.empty()) return std::nullopt;
    const auto& c = e.constant;
    switch (rel) {
    case lra::Relation::Le: return c <= lra::Rational(0);
    case lra::Relation::Lt: return c <  lra::Rational(0);
    case lra::Relation::Ge: return c >= lra::Rational(0);
    case lra::Relation::Gt: return c >  lra::Rational(0);
    case lra::Relation::Eq: return c == lra::Rational(0);
    case lra::Relation::Ne: return c != lra::Rational(0);
    }
    return std::nullopt;
}

std::optional<bool> Smt2Visitor::lra_lit_const(int lit) const
{
    if (true_lit_ == 0) return std::nullopt;
    if (lit == true_lit_) return true;
    if (lit == -true_lit_) return false;
    return std::nullopt;
}

bool Smt2Visitor::lra_simplify_clause_lits(std::vector<int>& lits)
{
    if (!opts_.lra_const_simplify) return false;

    std::vector<int> simplified;
    simplified.reserve(lits.size());
    std::unordered_set<int> seen;
    for (int lit : lits) {
        if (auto c = lra_lit_const(lit)) {
            ++stats_.lra_const_bool_folds;
            if (*c) {
                lits.clear();
                return true;
            }
            continue;
        }
        if (seen.contains(-lit)) {
            ++stats_.lra_const_bool_folds;
            lits.clear();
            return true;
        }
        if (seen.insert(lit).second) simplified.push_back(lit);
        else ++stats_.lra_const_bool_folds;
    }
    lits.swap(simplified);
    return false;
}

bool Smt2Visitor::lra_simplify_conj_lits(std::vector<int>& lits)
{
    if (!opts_.lra_const_simplify) return false;

    std::vector<int> simplified;
    simplified.reserve(lits.size());
    std::unordered_set<int> seen;
    for (int lit : lits) {
        if (auto c = lra_lit_const(lit)) {
            ++stats_.lra_const_bool_folds;
            if (!*c) {
                lits.clear();
                return true;
            }
            continue;
        }
        if (seen.contains(-lit)) {
            ++stats_.lra_const_bool_folds;
            lits.clear();
            return true;
        }
        if (seen.insert(lit).second) simplified.push_back(lit);
        else ++stats_.lra_const_bool_folds;
    }
    lits.swap(simplified);
    return false;
}

int Smt2Visitor::lra_register_atom(lra::LinearExpr e, lra::Relation rel)
{
    e = lra_rewrite_expr(e);
    if (auto v = lra_const_relation(e, rel)) {
        if (opts_.lra_const_simplify) ++stats_.lra_const_arith_folds;
        return *v ? get_true_lit() : -get_true_lit();
    }

    // Canonicalize lower bounds to equivalent upper bounds. This keeps the SAT
    // abstraction smaller before the tableau's own atom table sees the atom.
    if (rel == lra::Relation::Ge) {
        e.scale(lra::Rational(-1));
        rel = lra::Relation::Le;
    } else if (rel == lra::Relation::Gt) {
        e.scale(lra::Rational(-1));
        rel = lra::Relation::Lt;
    }

    auto simple_bound = lra_simple_bound(e, rel);
    std::string key = lra_atom_key(e, rel);
    auto it = lra_atom_lit_cache_.find(key);
    if (it != lra_atom_lit_cache_.end()) {
        ++stats_.lra_atom_cache_hits;
        if (simple_bound) {
            const auto& [var, bound_rel, value] = *simple_bound;
            lra_remember_bound_lit(var, bound_rel, value, it->second);
        }
        return it->second;
    }
    int lit = ctx_.lra->register_atom({e, rel});
    lra_atom_lit_cache_[std::move(key)] = lit;
    if (simple_bound) {
        const auto& [var, bound_rel, value] = *simple_bound;
        lra_remember_bound_lit(var, bound_rel, value, lit);
    }
    return lit;
}

int Smt2Visitor::lra_register_direct_asserted_equality(lra::LinearExpr e)
{
    if (!opts_.lra_direct_eq_atoms) return lra_register_equality(std::move(e));
    e = lra_rewrite_expr(e);
    e = lra_canonical_zero_test(std::move(e));
    if (auto v = lra_const_relation(e, lra::Relation::Eq)) {
        if (opts_.lra_const_simplify) ++stats_.lra_const_arith_folds;
        return *v ? get_true_lit() : -get_true_lit();
    }

    std::string key = lra_expr_key(e);
    auto it = lra_direct_eq_lit_cache_.find(key);
    if (it != lra_direct_eq_lit_cache_.end()) {
        ++stats_.lra_eq_cache_hits;
        return it->second;
    }

    int lit = ctx_.lra->register_atom({e, lra::Relation::Eq});
    lra_direct_eq_lit_cache_[std::move(key)] = lit;
    return lit;
}

int Smt2Visitor::lra_register_equality(lra::LinearExpr e)
{
    e = lra_rewrite_expr(e);
    e = lra_canonical_zero_test(std::move(e));
    if (auto v = lra_const_relation(e, lra::Relation::Eq)) {
        if (opts_.lra_const_simplify) ++stats_.lra_const_arith_folds;
        return *v ? get_true_lit() : -get_true_lit();
    }

    std::optional<std::pair<std::string, lra::Rational>> simple = lra_simple_equality(e);
    std::optional<std::pair<std::string, std::string>> var_eq = lra_var_var_equality(e);
    std::string simple_key;
    if (simple) {
        simple_key = simple->first + "=" + simple->second.str();
        auto sit = lra_simple_eq_lit_cache_.find(simple_key);
        if (sit != lra_simple_eq_lit_cache_.end()) {
            ++stats_.lra_eq_cache_hits;
            return sit->second;
        }
    }

    std::string key = lra_expr_key(e);
    auto it = lra_eq_lit_cache_.find(key);
    if (it != lra_eq_lit_cache_.end()) {
        ++stats_.lra_eq_cache_hits;
        return it->second;
    }
    int ge = lra_register_atom(e, lra::Relation::Ge);
    int le = lra_register_atom(e, lra::Relation::Le);
    int y = fresh_bool_var();
    { std::array<int,2> cl = {-y, ge}; ctx_.sat.add_clause(std::span<const int>(cl)); }
    { std::array<int,2> cl = {-y, le}; ctx_.sat.add_clause(std::span<const int>(cl)); }
    { std::array<int,3> cl = {-ge, -le, y}; ctx_.sat.add_clause(std::span<const int>(cl)); }
    lra_eq_lit_cache_[std::move(key)] = y;
    if (var_eq) lra_remember_var_eq_lit(var_eq->first, var_eq->second, y);
    if (simple) {
        const std::string value_key = simple->second.str();
        lra_simple_eq_lit_cache_[std::move(simple_key)] = y;
        if (opts_.lra_finite_domain_branch && simple->second == lra::Rational(2))
            ctx_.lra->add_branch_hint(y);
        if (!opts_.finite_domain_amo) return y;

        auto& previous = lra_simple_eqs_by_var_[simple->first];
        for (const auto& other : previous) {
            if (other.value == simple->second) continue;
            std::array<int,2> cl = {-y, -other.lit};
            ctx_.sat.add_clause(std::span<const int>(cl));
            ++stats_.preproc_finite_domain_amo_clauses;
        }
        previous.push_back({value_key, simple->second, y});
        lra_encode_finite_domain_bound_defs_for_var(simple->first);
        if (auto vit = lra_var_eq_lits_by_var_.find(simple->first);
            vit != lra_var_eq_lits_by_var_.end()) {
            for (const auto& entry : vit->second)
                lra_encode_finite_domain_eq_defs_for_pair(simple->first, entry.other, entry.lit);
        }
    }
    return y;
}

int Smt2Visitor::lra_register_disequality(lra::LinearExpr e)
{
    e = lra_rewrite_expr(e);
    e = lra_canonical_zero_test(std::move(e));
    if (auto v = lra_const_relation(e, lra::Relation::Ne)) {
        if (opts_.lra_const_simplify) ++stats_.lra_const_arith_folds;
        return *v ? get_true_lit() : -get_true_lit();
    }
    std::string key = lra_expr_key(e);
    auto it = lra_diseq_lit_cache_.find(key);
    if (it != lra_diseq_lit_cache_.end()) return it->second;
    int lt = lra_register_atom(e, lra::Relation::Lt);
    int gt = lra_register_atom(e, lra::Relation::Gt);
    int y = fresh_bool_var();
    { std::array<int,3> cl = {-y, lt, gt}; ctx_.sat.add_clause(std::span<const int>(cl)); }
    { std::array<int,2> cl = {-lt, y}; ctx_.sat.add_clause(std::span<const int>(cl)); }
    { std::array<int,2> cl = {-gt, y}; ctx_.sat.add_clause(std::span<const int>(cl)); }
    lra_diseq_lit_cache_[std::move(key)] = y;
    return y;
}

lra::LinearExpr Smt2Visitor::lra_term(
    smt2parser::SMTLIBv2Parser::TermContext* t)
{
    while (t->GRW_Exclamation()) t = t->term()[0];
    auto remember = [&](const lra::LinearExpr& e) {
        if (opts_.lra_term_cache) lra_term_cache_[t] = e;
        return e;
    };
    if (opts_.lra_term_cache) {
        auto it = lra_term_cache_.find(t);
        if (it != lra_term_cache_.end()) {
            ++stats_.lra_term_cache_hits;
            return it->second;
        }
    }
    auto rewritten_expr_key = [&](const lra::LinearExpr& e) {
        return lra_expr_key(lra_rewrite_expr(e));
    };

    if (t->GRW_Let()) {
        auto* original = t;
        int frames = 0;
        while (t->GRW_Let() || t->GRW_Exclamation()) {
            if (t->GRW_Exclamation()) { t = t->term()[0]; continue; }
            let_env_.emplace_back();
            for (auto* vb : t->var_binding())
                let_env_.back()[vb->symbol()->getText()].term = vb->term();
            t = t->term()[0];
            ++frames;
        }
        auto result = lra_term(t);
        for (int i = 0; i < frames; ++i) let_env_.pop_back();
        if (opts_.lra_term_cache) lra_term_cache_[original] = result;
        return result;
    }

    if (t->spec_constant() != nullptr) {
        lra::LinearExpr e;
        e.constant = lra_number(t);
        return remember(e);
    }
    if (auto c = lra_const_value(t)) {
        lra::LinearExpr e;
        e.constant = *c;
        return remember(e);
    }
    if (t->qual_identifier() == nullptr)
        throw std::runtime_error("unsupported arithmetic term: " + t->getText());

    std::string op = identifier_name(t->qual_identifier()->identifier());
    if (t->term().empty()) {
        if (auto* binding = find_let_binding(op)) return lra_term(binding->term);
        if (!is_real_decl(op))
            throw std::runtime_error("undeclared or non-Real arithmetic symbol: " + op);
        auto sit = lra_eq_elim_subst_.find(op);
        if (sit != lra_eq_elim_subst_.end()) return remember(sit->second);
        lra::LinearExpr e;
        e.add_var(op, lra::Rational(1));
        return remember(e);
    }

    if (op == "+") {
        lra::LinearExpr sum;
        for (auto* sub : t->term()) sum.add(lra_term(sub));
        return remember(sum);
    }
    if (op == "-") {
        auto terms = t->term();
        if (terms.size() == 1) {
            auto e = lra_term(terms[0]);
            e.scale(lra::Rational(-1));
            return remember(e);
        }
        auto e = lra_term(terms[0]);
        for (size_t i = 1; i < terms.size(); ++i)
            e.add(lra_term(terms[i]), lra::Rational(-1));
        return remember(e);
    }
    if (op == "*") {
        auto terms = t->term();
        lra::Rational factor(1);
        smt2parser::SMTLIBv2Parser::TermContext* nonconst = nullptr;
        for (auto* sub : terms) {
            if (auto c = lra_const_value(sub)) {
                factor *= *c;
            } else if (nonconst == nullptr) {
                nonconst = sub;
            } else {
                throw std::runtime_error("QF_LRA supports multiplication only by rational constants");
            }
        }
        if (nonconst == nullptr) {
            lra::LinearExpr e;
            e.constant = factor;
            return remember(e);
        }
        auto e = lra_term(nonconst);
        e.scale(factor);
        return remember(e);
    }
    if (op == "/") {
        auto terms = t->term();
        if (terms.size() != 2 || !is_lra_number_term(terms[1]))
            throw std::runtime_error("QF_LRA supports division only by rational constants");
        auto e = lra_term(terms[0]);
        e.scale(lra::Rational(1) / lra_number(terms[1]));
        return remember(e);
    }
    if (op == "ite" && t->term().size() == 3) {
        struct IteBranch {
            int cond = 0;
            smt2parser::SMTLIBv2Parser::TermContext* term = nullptr;
        };
        std::vector<IteBranch> branches;
        smt2parser::SMTLIBv2Parser::TermContext* tail = t;
        bool reduced_by_const_cond = false;
        while (true) {
            while (tail->GRW_Exclamation()) tail = tail->term()[0];
            if (tail->GRW_Let() || tail->qual_identifier() == nullptr) break;
            std::string tail_op = identifier_name(tail->qual_identifier()->identifier());
            if (tail_op != "ite" || tail->term().size() != 3) break;

            int cond = lra_eval_lit(tail->term()[0]);
            if (opts_.lra_const_simplify) {
                if (auto c = lra_lit_const(cond)) {
                    ++stats_.lra_const_bool_folds;
                    ++stats_.lra_ite_terms_simplified;
                    reduced_by_const_cond = true;
                    tail = tail->term()[*c ? 1 : 2];
                    if (*c) break;
                    continue;
                }
            }
            branches.push_back({cond, tail->term()[1]});
            tail = tail->term()[2];
        }

        if (opts_.lra_const_simplify && reduced_by_const_cond && branches.empty())
            return remember(lra_term(tail));

        if (opts_.lra_const_simplify &&
            (branches.size() >= 2 || (reduced_by_const_cond && !branches.empty()))) {
            std::vector<lra::LinearExpr> branch_exprs;
            branch_exprs.reserve(branches.size());
            for (const auto& branch : branches)
                branch_exprs.push_back(lra_term(branch.term));
            auto default_e = lra_term(tail);
            bool all_constant_branches = default_e.coeffs.empty();
            for (const auto& e : branch_exprs)
                all_constant_branches = all_constant_branches && e.coeffs.empty();

            bool all_same = true;
            const std::string default_key = lra_expr_key(lra_rewrite_expr(default_e));
            for (const auto& e : branch_exprs) {
                if (lra_expr_key(lra_rewrite_expr(e)) != default_key) {
                    all_same = false;
                    break;
                }
            }
            if (opts_.lra_const_simplify && all_same) {
                ++stats_.lra_ite_terms_simplified;
                return remember(default_e);
            }
            if (!all_constant_branches) {
                int cond = lra_eval_lit(t->term()[0]);
                auto then_e = lra_term(t->term()[1]);
                auto else_e = lra_term(t->term()[2]);
                std::string aux = "__lra_ite_" + std::to_string(ite_counter_++);
                ++stats_.lra_ite_terms;
                ctx_.lra->declare_real(aux);
                lra::LinearExpr aux_e;
                aux_e.add_var(aux, lra::Rational(1));
                auto eq_then = aux_e;
                eq_then.add(then_e, lra::Rational(-1));
                auto eq_else = aux_e;
                eq_else.add(else_e, lra::Rational(-1));
                int l_then = lra_register_equality(eq_then);
                int l_else = lra_register_equality(eq_else);
                { std::array<int,2> cl = {-cond, l_then}; ctx_.sat.add_clause(std::span<const int>(cl)); }
                { std::array<int,2> cl = { cond, l_else}; ctx_.sat.add_clause(std::span<const int>(cl)); }
                return remember(aux_e);
            }

            std::string aux = "__lra_ite_" + std::to_string(ite_counter_++);
            ++stats_.lra_ite_terms;
            ctx_.lra->declare_real(aux);
            lra::LinearExpr aux_e;
            aux_e.add_var(aux, lra::Rational(1));

            std::vector<int> previous_conds;
            previous_conds.reserve(branches.size());
            for (size_t i = 0; i < branches.size(); ++i) {
                auto eq = aux_e;
                eq.add(branch_exprs[i], lra::Rational(-1));
                int lit = lra_register_equality(eq);
                std::vector<int> clause = previous_conds;
                clause.push_back(-branches[i].cond);
                clause.push_back(lit);
                if (!lra_simplify_clause_lits(clause))
                    ctx_.sat.add_clause(std::span<const int>(clause));
                previous_conds.push_back(branches[i].cond);
            }

            auto eq_default = aux_e;
            eq_default.add(default_e, lra::Rational(-1));
            int default_lit = lra_register_equality(eq_default);
            std::vector<int> default_clause = previous_conds;
            default_clause.push_back(default_lit);
            if (!lra_simplify_clause_lits(default_clause))
                ctx_.sat.add_clause(std::span<const int>(default_clause));
            return remember(aux_e);
        }

        int cond = lra_eval_lit(t->term()[0]);
        if (opts_.lra_const_simplify) {
            if (auto c = lra_lit_const(cond)) {
                ++stats_.lra_const_bool_folds;
                ++stats_.lra_ite_terms_simplified;
                return remember(lra_term(t->term()[*c ? 1 : 2]));
            }
        }
        auto then_e = lra_term(t->term()[1]);
        auto else_e = lra_term(t->term()[2]);
        if (opts_.lra_const_simplify &&
            lra_expr_key(lra_rewrite_expr(then_e)) == lra_expr_key(lra_rewrite_expr(else_e))) {
            ++stats_.lra_ite_terms_simplified;
            return remember(then_e);
        }
        const std::string key = "ite:" + std::to_string(cond) + ":" +
            rewritten_expr_key(then_e) + ":" + rewritten_expr_key(else_e);
        std::string aux = "__lra_ite_" + std::to_string(ite_counter_++);
        ++stats_.lra_ite_terms;
        ctx_.lra->declare_real(aux);
        lra::LinearExpr aux_e;
        aux_e.add_var(aux, lra::Rational(1));
        auto eq_then = aux_e;
        eq_then.add(then_e, lra::Rational(-1));
        auto eq_else = aux_e;
        eq_else.add(else_e, lra::Rational(-1));
        int l_then = lra_register_equality(eq_then);
        int l_else = lra_register_equality(eq_else);
        { std::array<int,2> cl = {-cond, l_then}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,2> cl = { cond, l_else}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        return remember(aux_e);
    }

    throw std::runtime_error("unsupported QF_LRA arithmetic operator: " + op);
}

bool Smt2Visitor::lra_term_is_elim_safe(
    smt2parser::SMTLIBv2Parser::TermContext* t) const
{
    while (t->GRW_Exclamation()) t = t->term()[0];
    if (t->GRW_Let()) return false;
    if (t->spec_constant() != nullptr) return true;
    if (t->qual_identifier() == nullptr) return false;
    std::string op = identifier_name(t->qual_identifier()->identifier());
    if (t->term().empty()) return is_real_decl(op);
    if (op == "ite") return false;
    if (op != "+" && op != "-" && op != "*" && op != "/") return false;
    for (auto* sub : t->term())
        if (!lra_term_is_elim_safe(sub)) return false;
    return true;
}

void Smt2Visitor::lra_try_eliminate_equality(lra::LinearExpr e)
{
    if (!opts_.lra_eq_elim || lra_eq_elim_unsat_) return;
    if (stats_.lra_eq_elim_rows >= opts_.lra_eq_elim_limit) return;

    e = lra_rewrite_expr(e);
    ++stats_.lra_eq_elim_rows;
    if (e.coeffs.empty()) {
        if (e.constant != lra::Rational(0)) {
            ctx_.sat.add_clause(std::span<const int>{});
            lra_eq_elim_unsat_ = true;
            ++stats_.lra_eq_elim_contradictions;
        }
        return;
    }

    auto pivot_it = e.coeffs.end();
    for (auto it = e.coeffs.begin(); it != e.coeffs.end(); ++it) {
        if (it->first.rfind("__lra_", 0) == 0) {
            pivot_it = it;
            break;
        }
        if (pivot_it == e.coeffs.end()) pivot_it = it;
    }
    if (pivot_it == e.coeffs.end() || pivot_it->second.is_zero()) return;

    const std::string pivot = pivot_it->first;
    const lra::Rational pivot_coeff = pivot_it->second;
    e.coeffs.erase(pivot_it);

    lra::LinearExpr rhs;
    rhs.constant = -e.constant / pivot_coeff;
    for (const auto& [name, coeff] : e.coeffs)
        rhs.add_var(name, -coeff / pivot_coeff);

    for (auto& [name, subst] : lra_eq_elim_subst_) {
        auto it = subst.coeffs.find(pivot);
        if (it == subst.coeffs.end()) continue;
        lra::Rational coeff = it->second;
        subst.coeffs.erase(it);
        subst.add(rhs, coeff);
    }
    lra_eq_elim_subst_[pivot] = std::move(rhs);
    ++stats_.lra_eq_elim_vars;
}

void Smt2Visitor::lra_collect_unconditional_equalities(
    smt2parser::SMTLIBv2Parser::TermContext* t)
{
    if (!opts_.lra_eq_elim || lra_eq_elim_unsat_) return;
    while (t->GRW_Exclamation()) t = t->term()[0];
    if (t->GRW_Let()) return;
    if (t->qual_identifier() == nullptr) return;
    std::string op = identifier_name(t->qual_identifier()->identifier());
    if (op == "and") {
        for (auto* sub : t->term()) lra_collect_unconditional_equalities(sub);
        return;
    }
    if (op != "=" || t->term().size() < 2 || !is_lra_term_syntax(t->term()[0]))
        return;

    auto terms = t->term();
    for (auto* term : terms) {
        if (!is_lra_term_syntax(term) || !lra_term_is_elim_safe(term)) return;
    }

    auto first = lra_term(terms[0]);
    for (size_t i = 1; i < terms.size(); ++i) {
        auto e = first;
        e.add(lra_term(terms[i]), lra::Rational(-1));
        lra_try_eliminate_equality(std::move(e));
        if (stats_.lra_eq_elim_rows >= opts_.lra_eq_elim_limit || lra_eq_elim_unsat_)
            break;
    }
}

bool Smt2Visitor::lra_try_dl_fast_path_unsat()
{
    if (!opts_.lra_dl_fast_path || pending_lra_asserts_.empty()) return false;
    ++stats_.lra_dl_fast_path_attempts;

    struct Edge {
        int from = 0;
        int to = 0;
        lra::DeltaRational weight;
    };

    std::vector<Edge> edges;
    std::map<std::string, int> vars;
    size_t accepted_atoms = 0;
    bool rejected = false;
    bool contradiction = false;

    auto var_id = [&](const std::string& name) -> int {
        auto [it, inserted] = vars.emplace(name, static_cast<int>(vars.size()));
        (void)inserted;
        return it->second;
    };
    auto node_for = [](int id, bool negated) {
        return 1 + 2 * id + (negated ? 1 : 0);
    };
    auto strict_bound = [](lra::Rational bound, bool strict) {
        return lra::DeltaRational(std::move(bound), strict ? lra::Rational(-1) : lra::Rational(0));
    };

    auto add_le = [&](lra::LinearExpr expr, bool strict) -> bool {
        expr = lra_rewrite_expr(expr);
        std::vector<std::pair<std::string, lra::Rational>> coeffs;
        coeffs.reserve(expr.coeffs.size());
        for (const auto& [name, coeff] : expr.coeffs) {
            if (!coeff.is_zero()) coeffs.push_back({name, coeff});
        }

        if (coeffs.empty()) {
            const auto zero = lra::Rational(0);
            if (strict ? !(expr.constant < zero) : !(expr.constant <= zero))
                contradiction = true;
            return true;
        }

        lra::Rational bound = -expr.constant;
        if (coeffs.size() == 1) {
            const auto& [name, coeff] = coeffs[0];
            if (coeff.is_zero()) return false;
            int id = var_id(name);
            if (coeff > lra::Rational(0)) {
                auto w = strict_bound(bound / coeff, strict);
                edges.push_back({0, node_for(id, false), w});
                edges.push_back({node_for(id, true), node_for(id, false), w * lra::Rational(2)});
            } else {
                auto w = strict_bound(bound / (-coeff), strict);
                edges.push_back({node_for(id, false), 0, w});
                edges.push_back({node_for(id, false), node_for(id, true), w * lra::Rational(2)});
            }
            return true;
        }

        if (coeffs.size() != 2) return false;
        const auto& [name_a, coeff_a] = coeffs[0];
        const auto& [name_b, coeff_b] = coeffs[1];
        lra::Rational abs_a = coeff_a < lra::Rational(0) ? -coeff_a : coeff_a;
        lra::Rational abs_b = coeff_b < lra::Rational(0) ? -coeff_b : coeff_b;
        if (abs_a.is_zero() || !(abs_a == abs_b)) return false;

        bool a_neg = coeff_a < lra::Rational(0);
        bool b_neg = coeff_b < lra::Rational(0);
        int id_a = var_id(name_a);
        int id_b = var_id(name_b);
        lra::DeltaRational w = strict_bound(bound / abs_a, strict);

        if (a_neg != b_neg) {
            int from = a_neg ? id_a : id_b;
            int to = a_neg ? id_b : id_a;
            edges.push_back({node_for(from, false), node_for(to, false), w});
            return true;
        }

        // UTVPI constraints over ±x±y reduce to two DL edges over signed
        // variables; satisfiable pure cases still fall through to simplex for models.
        int node_a = node_for(id_a, a_neg);
        int node_not_a = node_for(id_a, !a_neg);
        int node_b = node_for(id_b, b_neg);
        int node_not_b = node_for(id_b, !b_neg);
        edges.push_back({node_not_b, node_a, w});
        edges.push_back({node_not_a, node_b, w});
        return true;
    };

    auto add_relation = [&](lra::LinearExpr expr, lra::Relation rel) -> bool {
        switch (rel) {
        case lra::Relation::Le:
            return add_le(std::move(expr), false);
        case lra::Relation::Lt:
            return add_le(std::move(expr), true);
        case lra::Relation::Ge:
            expr.scale(lra::Rational(-1));
            return add_le(std::move(expr), false);
        case lra::Relation::Gt:
            expr.scale(lra::Rational(-1));
            return add_le(std::move(expr), true);
        case lra::Relation::Eq: {
            auto neg = expr;
            neg.scale(lra::Rational(-1));
            return add_le(std::move(expr), false) && add_le(std::move(neg), false);
        }
        case lra::Relation::Ne:
            return false;
        }
        return false;
    };

    using Term = smt2parser::SMTLIBv2Parser::TermContext;
    std::function<bool(Term*)> collect = [&](Term* t) -> bool {
        while (t->GRW_Exclamation()) t = t->term()[0];
        if (t->GRW_Let() || t->qual_identifier() == nullptr) return false;

        std::string op = identifier_name(t->qual_identifier()->identifier());
        if (op == "true") return true;
        if (op == "false") {
            contradiction = true;
            return true;
        }
        if (op == "and") {
            for (auto* sub : t->term()) {
                if (!collect(sub)) return false;
                if (contradiction) return true;
            }
            return true;
        }

        static const std::unordered_map<std::string, lra::Relation> rels = {
            {"<", lra::Relation::Lt}, {"<=", lra::Relation::Le},
            {">", lra::Relation::Gt}, {">=", lra::Relation::Ge}
        };

        if (op == "=" && t->term().size() >= 2 && is_lra_term_syntax(t->term()[0])) {
            auto terms = t->term();
            for (auto* term : terms) {
                if (!is_lra_term_syntax(term) || !lra_term_is_elim_safe(term)) return false;
            }
            auto first = lra_term(terms[0]);
            for (size_t i = 1; i < terms.size(); ++i) {
                auto e = first;
                e.add(lra_term(terms[i]), lra::Rational(-1));
                ++accepted_atoms;
                if (!add_relation(std::move(e), lra::Relation::Eq)) return false;
                if (contradiction) return true;
            }
            return true;
        }

        auto rit = rels.find(op);
        if (rit != rels.end() && t->term().size() == 2) {
            if (!is_lra_term_syntax(t->term()[0]) || !is_lra_term_syntax(t->term()[1]) ||
                !lra_term_is_elim_safe(t->term()[0]) || !lra_term_is_elim_safe(t->term()[1]))
                return false;
            auto e = lra_term(t->term()[0]);
            e.add(lra_term(t->term()[1]), lra::Rational(-1));
            ++accepted_atoms;
            return add_relation(std::move(e), rit->second);
        }

        return false;
    };

    for (auto* t : pending_lra_asserts_) {
        if (!collect(t)) {
            rejected = true;
            break;
        }
        if (contradiction) break;
    }

    stats_.lra_dl_fast_path_atoms += accepted_atoms;
    if (rejected) {
        ++stats_.lra_dl_fast_path_rejected;
        ++stats_.lra_dl_fast_path_fallbacks;
        return false;
    }
    if (!contradiction) {
        const size_t node_count = 1 + 2 * vars.size();
        std::vector<lra::DeltaRational> dist(node_count, lra::DeltaRational(lra::Rational(0)));
        for (size_t iter = 0; iter < node_count; ++iter) {
            bool changed = false;
            for (const auto& edge : edges) {
                lra::DeltaRational candidate = dist[edge.from] + edge.weight;
                if (candidate < dist[edge.to]) {
                    if (iter + 1 == node_count) {
                        contradiction = true;
                        break;
                    }
                    dist[edge.to] = candidate;
                    changed = true;
                }
            }
            if (contradiction || !changed) break;
        }
    }

    if (!contradiction) {
        ++stats_.lra_dl_fast_path_fallbacks;
        return false;
    }

    ctx_.sat.add_clause(std::span<const int>{});
    ++stats_.lra_dl_fast_path_unsats;
    return true;
}

void Smt2Visitor::lra_flush_assertions()
{
    if (pending_lra_asserts_.empty()) return;
    if (opts_.lra_eq_elim) {
        lra_term_cache_.clear();
        for (auto* t : pending_lra_asserts_)
            lra_collect_unconditional_equalities(t);
        lra_term_cache_.clear();
    }
    if (lra_eq_elim_unsat_) {
        pending_lra_asserts_.clear();
        return;
    }
    if (lra_try_dl_fast_path_unsat()) {
        pending_lra_asserts_.clear();
        return;
    }
    for (auto* t : pending_lra_asserts_)
        lra_assert_formula(t);
    pending_lra_asserts_.clear();
}

std::optional<lra::Rational> Smt2Visitor::lra_model_value(
    const std::string& name) const
{
    if (auto cached = lra_model_value_cache_.find(name);
        cached != lra_model_value_cache_.end()) {
        return cached->second;
    }

    auto subst_it = lra_eq_elim_subst_.find(name);
    if (subst_it == lra_eq_elim_subst_.end()) {
        auto direct = ctx_.lra->value_of(name);
        if (direct) lra_model_value_cache_[name] = *direct;
        return direct;
    }

    lra::Rational value = subst_it->second.constant;
    for (const auto& [sub_name, coeff] : subst_it->second.coeffs) {
        auto sub_value = lra_model_value(sub_name).value_or(lra::Rational(0));
        value += coeff * sub_value;
    }
    lra_model_value_cache_[name] = value;
    return value;
}

void Smt2Visitor::lra_collect_clause_lits(
    smt2parser::SMTLIBv2Parser::TermContext* t,
    std::vector<int>& lits)
{
    while (t->GRW_Exclamation()) t = t->term()[0];
    if (t->qual_identifier() != nullptr) {
        std::string op = identifier_name(t->qual_identifier()->identifier());
        if (op == "or") {
            for (auto* sub : t->term()) lra_collect_clause_lits(sub, lits);
            return;
        }
    }
    lits.push_back(lra_eval_lit(t));
}

int Smt2Visitor::lra_encode_bool_ite_lit(int cond, int then_lit, int else_lit)
{
    if (opts_.lra_const_simplify) {
        if (auto c = lra_lit_const(cond)) {
            ++stats_.lra_const_bool_folds;
            return *c ? then_lit : else_lit;
        }
        if (then_lit == else_lit) {
            ++stats_.lra_const_bool_folds;
            return then_lit;
        }
        if (auto tv = lra_lit_const(then_lit)) {
            ++stats_.lra_const_bool_folds;
            if (auto ev = lra_lit_const(else_lit)) {
                if (*tv == *ev) return *tv ? get_true_lit() : -get_true_lit();
                return *tv ? cond : -cond;
            }
        }
    }

    const std::array<int,3> key_lits = {cond, then_lit, else_lit};
    std::string structural_key;
    if (opts_.lra_bool_cache) {
        structural_key = lra_bool_lit_key("ite", std::span<const int>(key_lits));
        auto sit = lra_bool_lit_cache_.find(structural_key);
        if (sit != lra_bool_lit_cache_.end()) {
            ++stats_.lra_bool_cache_hits;
            ++stats_.lra_bool_cache_hits_ite;
            return sit->second;
        }
    }

    int y = fresh_bool_var();
    if (opts_.lra_bool_cache) lra_bool_lit_cache_[std::move(structural_key)] = y;
    { std::array<int,3> cl = {-cond, -then_lit,  y}; ctx_.sat.add_clause(std::span<const int>(cl)); }
    { std::array<int,3> cl = {-cond,  then_lit, -y}; ctx_.sat.add_clause(std::span<const int>(cl)); }
    { std::array<int,3> cl = { cond, -else_lit,  y}; ctx_.sat.add_clause(std::span<const int>(cl)); }
    { std::array<int,3> cl = { cond,  else_lit, -y}; ctx_.sat.add_clause(std::span<const int>(cl)); }
    return y;
}

int Smt2Visitor::lra_eval_ite_equality(
    smt2parser::SMTLIBv2Parser::TermContext* other,
    smt2parser::SMTLIBv2Parser::TermContext* ite)
{
    while (ite->GRW_Exclamation()) ite = ite->term()[0];
    if (ite->qual_identifier() != nullptr && ite->term().empty()) {
        std::string op = identifier_name(ite->qual_identifier()->identifier());
        if (auto* binding = find_let_binding(op))
            return lra_eval_ite_equality(other, binding->term);
    }
    if (ite->qual_identifier() == nullptr)
        throw std::runtime_error("expected QF_LRA arithmetic ite term");
    std::string op = identifier_name(ite->qual_identifier()->identifier());
    if (op != "ite" || ite->term().size() != 3)
        throw std::runtime_error("expected QF_LRA arithmetic ite term");

    int cond = lra_eval_lit(ite->term()[0]);
    auto other_e = lra_term(other);
    auto then_e = other_e;
    then_e.add(lra_term(ite->term()[1]), lra::Rational(-1));
    int then_lit = lra_register_equality(std::move(then_e));

    int else_lit = 0;
    if (is_lra_ite_term(ite->term()[2])) {
        else_lit = lra_eval_ite_equality(other, ite->term()[2]);
    } else {
        auto else_e = other_e;
        else_e.add(lra_term(ite->term()[2]), lra::Rational(-1));
        else_lit = lra_register_equality(std::move(else_e));
    }
    ++stats_.lra_ite_terms_simplified;
    return lra_encode_bool_ite_lit(cond, then_lit, else_lit);
}

int Smt2Visitor::lra_eval_lit(
    smt2parser::SMTLIBv2Parser::TermContext* t)
{
    while (t->GRW_Exclamation()) t = t->term()[0];
    if (t->GRW_Let()) {
        int frames = 0;
        while (t->GRW_Let() || t->GRW_Exclamation()) {
            if (t->GRW_Exclamation()) { t = t->term()[0]; continue; }
            let_env_.emplace_back();
            for (auto* vb : t->var_binding())
                let_env_.back()[vb->symbol()->getText()].term = vb->term();
            t = t->term()[0];
            ++frames;
        }
        int result = lra_eval_lit(t);
        for (int i = 0; i < frames; ++i) let_env_.pop_back();
        return result;
    }
    if (t->qual_identifier() == nullptr)
        throw std::runtime_error("unsupported QF_LRA formula: " + t->getText());
    std::string op = identifier_name(t->qual_identifier()->identifier());

    if (op == "true") return get_true_lit();
    if (op == "false") return -get_true_lit();
    if (op == "not" && t->term().size() == 1) {
        auto* inner = t->term()[0];
        while (inner->GRW_Exclamation()) inner = inner->term()[0];
        if (inner->qual_identifier() != nullptr &&
            identifier_name(inner->qual_identifier()->identifier()) == "=" &&
            inner->term().size() == 2 &&
            is_lra_term_syntax(inner->term()[0])) {
            auto e = lra_term(inner->term()[0]);
            e.add(lra_term(inner->term()[1]), lra::Rational(-1));
            return lra_register_disequality(e);
        }
        return -lra_eval_lit(inner);
    }

    auto cacheable_bool_term = [&]() {
        if (op == "and" || op == "or" || op == "=>" || op == "xor") return true;
        if (op == "ite" && !is_lra_term_syntax(t)) return true;
        if ((op == "=" || op == "distinct") && !t->term().empty()) return true;
        return false;
    };
    auto bool_cache_enabled = [&]() {
        if (!opts_.lra_bool_cache) return false;
        if (op == "and") return opts_.lra_bool_cache_and;
        if (op == "or") return opts_.lra_bool_cache_or;
        if (op == "=" || op == "distinct") return opts_.lra_bool_cache_eq;
        return true;
    };
    bool use_bool_cache = cacheable_bool_term() && bool_cache_enabled();
    if (use_bool_cache) {
        auto it = tseitin_cache_.find(t);
        if (it != tseitin_cache_.end()) {
            ++stats_.lra_bool_cache_hits;
            if (op == "and") ++stats_.lra_bool_cache_hits_and;
            else if (op == "or") ++stats_.lra_bool_cache_hits_or;
            else if (op == "ite") ++stats_.lra_bool_cache_hits_ite;
            else if (op == "=" || op == "distinct") ++stats_.lra_bool_cache_hits_eq;
            return it->second;
        }
    }

    if (op == "and") {
        std::vector<int> sub;
        for (auto* c : t->term()) sub.push_back(lra_eval_lit(c));
        if (lra_simplify_conj_lits(sub)) return -get_true_lit();
        if (opts_.lra_const_simplify) {
            if (sub.empty()) return get_true_lit();
            if (sub.size() == 1) return sub.front();
        }
        std::string structural_key;
        if (use_bool_cache) {
            structural_key = lra_bool_lit_key(op, std::span<const int>(sub));
            auto sit = lra_bool_lit_cache_.find(structural_key);
            if (sit != lra_bool_lit_cache_.end()) {
                ++stats_.lra_bool_cache_hits;
                ++stats_.lra_bool_cache_hits_and;
                return sit->second;
            }
        }
        int y = fresh_bool_var();
        if (use_bool_cache) tseitin_cache_[t] = y;
        if (use_bool_cache) lra_bool_lit_cache_[std::move(structural_key)] = y;
        for (int l : sub) { std::array<int,2> cl = {-y, l}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        std::vector<int> back{y};
        for (int l : sub) back.push_back(-l);
        ctx_.sat.add_clause(std::span<const int>(back));
        return y;
    }
    if (op == "or") {
        std::vector<int> sub;
        for (auto* c : t->term()) lra_collect_clause_lits(c, sub);
        if (lra_simplify_clause_lits(sub)) return get_true_lit();
        if (opts_.lra_const_simplify) {
            if (sub.empty()) return -get_true_lit();
            if (sub.size() == 1) return sub.front();
        }
        std::string structural_key;
        if (use_bool_cache) {
            structural_key = lra_bool_lit_key(op, std::span<const int>(sub));
            auto sit = lra_bool_lit_cache_.find(structural_key);
            if (sit != lra_bool_lit_cache_.end()) {
                ++stats_.lra_bool_cache_hits;
                ++stats_.lra_bool_cache_hits_or;
                return sit->second;
            }
        }
        int y = fresh_bool_var();
        if (use_bool_cache) tseitin_cache_[t] = y;
        if (use_bool_cache) lra_bool_lit_cache_[std::move(structural_key)] = y;
        std::vector<int> fwd{-y};
        for (int l : sub) fwd.push_back(l);
        ctx_.sat.add_clause(std::span<const int>(fwd));
        for (int l : sub) { std::array<int,2> cl = {-l, y}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        return y;
    }
    if (op == "=>" || op == "xor" || (op == "ite" && !is_lra_term_syntax(t))) {
        if (op == "=>") {
            auto terms = t->term();
            std::vector<int> ds;
            for (size_t i = 0; i + 1 < terms.size(); ++i) ds.push_back(-lra_eval_lit(terms[i]));
            ds.push_back(lra_eval_lit(terms.back()));
            if (lra_simplify_clause_lits(ds)) return get_true_lit();
            if (opts_.lra_const_simplify) {
                if (ds.empty()) return -get_true_lit();
                if (ds.size() == 1) return ds.front();
            }
            std::string structural_key;
            if (use_bool_cache) {
                structural_key = lra_bool_lit_key(op, std::span<const int>(ds));
                auto sit = lra_bool_lit_cache_.find(structural_key);
                if (sit != lra_bool_lit_cache_.end()) {
                    ++stats_.lra_bool_cache_hits;
                    return sit->second;
                }
            }
            int y = fresh_bool_var();
            if (use_bool_cache) tseitin_cache_[t] = y;
            if (use_bool_cache) lra_bool_lit_cache_[std::move(structural_key)] = y;
            ds.insert(ds.begin(), -y);
            ctx_.sat.add_clause(std::span<const int>(ds));
            for (size_t i = 1; i < ds.size(); ++i) {
                std::array<int,2> cl = {-ds[i], y};
                ctx_.sat.add_clause(std::span<const int>(cl));
            }
            return y;
        }
        if (op == "ite") {
            int c = lra_eval_lit(t->term()[0]);
            if (opts_.lra_const_simplify) {
                if (auto cv = lra_lit_const(c)) {
                    ++stats_.lra_const_bool_folds;
                    return lra_eval_lit(t->term()[*cv ? 1 : 2]);
                }
            }
            int a = lra_eval_lit(t->term()[1]);
            int b = lra_eval_lit(t->term()[2]);
            if (opts_.lra_const_simplify) {
                if (a == b) {
                    ++stats_.lra_const_bool_folds;
                    return a;
                }
                if (auto av = lra_lit_const(a)) {
                    ++stats_.lra_const_bool_folds;
                    if (auto bv = lra_lit_const(b)) {
                        if (*av == *bv) return *av ? get_true_lit() : -get_true_lit();
                        return *av ? c : -c;
                    }
                    if (*av) {
                        std::vector<int> ds{c, b};
                        if (lra_simplify_clause_lits(ds)) return get_true_lit();
                        if (ds.size() == 1) return ds.front();
                    }
                }
                if (auto bv = lra_lit_const(b)) {
                    ++stats_.lra_const_bool_folds;
                    if (*bv) {
                        std::vector<int> ds{-c, a};
                        if (lra_simplify_clause_lits(ds)) return get_true_lit();
                        if (ds.size() == 1) return ds.front();
                    }
                }
            }
            std::array<int,3> key_lits = {c, a, b};
            std::string structural_key;
            if (use_bool_cache) {
                structural_key = lra_bool_lit_key(op, std::span<const int>(key_lits));
                auto sit = lra_bool_lit_cache_.find(structural_key);
                if (sit != lra_bool_lit_cache_.end()) {
                    ++stats_.lra_bool_cache_hits;
                    ++stats_.lra_bool_cache_hits_ite;
                    return sit->second;
                }
            }
            int y = fresh_bool_var();
            if (use_bool_cache) tseitin_cache_[t] = y;
            if (use_bool_cache) lra_bool_lit_cache_[std::move(structural_key)] = y;
            { std::array<int,3> cl = {-c, -a,  y}; ctx_.sat.add_clause(std::span<const int>(cl)); }
            { std::array<int,3> cl = {-c,  a, -y}; ctx_.sat.add_clause(std::span<const int>(cl)); }
            { std::array<int,3> cl = { c, -b,  y}; ctx_.sat.add_clause(std::span<const int>(cl)); }
            { std::array<int,3> cl = { c,  b, -y}; ctx_.sat.add_clause(std::span<const int>(cl)); }
            return y;
        }
        auto terms = t->term();
        std::vector<int> xs;
        xs.reserve(terms.size());
        for (auto* term : terms) xs.push_back(lra_eval_lit(term));
        if (opts_.lra_const_simplify && xs.size() == 2) {
            if (xs[0] == xs[1]) {
                ++stats_.lra_const_bool_folds;
                return -get_true_lit();
            }
            if (xs[0] == -xs[1]) {
                ++stats_.lra_const_bool_folds;
                return get_true_lit();
            }
        }
        std::string structural_key;
        if (use_bool_cache) {
            structural_key = lra_bool_lit_key(op, std::span<const int>(xs));
            auto sit = lra_bool_lit_cache_.find(structural_key);
            if (sit != lra_bool_lit_cache_.end()) {
                ++stats_.lra_bool_cache_hits;
                return sit->second;
            }
        }
        int y = fresh_bool_var();
        if (use_bool_cache) tseitin_cache_[t] = y;
        if (use_bool_cache) lra_bool_lit_cache_[std::move(structural_key)] = y;
        int acc = xs[0];
        for (size_t i = 1; i < xs.size(); ++i) {
            int a = acc, b = xs[i];
            acc = (i + 1 == xs.size()) ? y : fresh_bool_var();
            { std::array<int,3> cl = {-acc,  a,  b}; ctx_.sat.add_clause(std::span<const int>(cl)); }
            { std::array<int,3> cl = {-acc, -a, -b}; ctx_.sat.add_clause(std::span<const int>(cl)); }
            { std::array<int,3> cl = {-a,  b,  acc}; ctx_.sat.add_clause(std::span<const int>(cl)); }
            { std::array<int,3> cl = { a, -b,  acc}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        }
        return y;
    }

    if (op == "=" && t->term().size() == 2 &&
        (is_lra_bool_syntax(t->term()[0]) || is_lra_bool_syntax(t->term()[1]))) {
        int p = lra_eval_lit(t->term()[0]);
        int q = lra_eval_lit(t->term()[1]);
        if (opts_.lra_const_simplify) {
            if (p == q) {
                ++stats_.lra_const_bool_folds;
                return get_true_lit();
            }
            if (p == -q) {
                ++stats_.lra_const_bool_folds;
                return -get_true_lit();
            }
            if (auto pv = lra_lit_const(p)) {
                ++stats_.lra_const_bool_folds;
                return *pv ? q : -q;
            }
            if (auto qv = lra_lit_const(q)) {
                ++stats_.lra_const_bool_folds;
                return *qv ? p : -p;
            }
        }
        std::array<int,2> key_lits = {p, q};
        std::string structural_key;
        if (use_bool_cache) {
            structural_key = lra_bool_lit_key(op, std::span<const int>(key_lits));
            auto sit = lra_bool_lit_cache_.find(structural_key);
            if (sit != lra_bool_lit_cache_.end()) {
                ++stats_.lra_bool_cache_hits;
                ++stats_.lra_bool_cache_hits_eq;
                return sit->second;
            }
        }
        int y = fresh_bool_var();
        if (use_bool_cache) tseitin_cache_[t] = y;
        if (use_bool_cache) lra_bool_lit_cache_[std::move(structural_key)] = y;
        { std::array<int,3> cl = {-y, -p,  q}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,3> cl = {-y,  p, -q}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,3> cl = {-p, -q,  y}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,3> cl = { p,  q,  y}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        return y;
    }

    if (op == "=" && t->term().size() >= 2 && is_lra_term_syntax(t->term()[0])) {
        auto terms = t->term();
        if (opts_.lra_ite_eq_direct && terms.size() == 2) {
            const bool lhs_ite = is_lra_ite_term(terms[0]);
            const bool rhs_ite = is_lra_ite_term(terms[1]);
            if (lhs_ite != rhs_ite)
                return lhs_ite ? lra_eval_ite_equality(terms[1], terms[0])
                               : lra_eval_ite_equality(terms[0], terms[1]);
        }
        std::vector<int> eq_lits;
        eq_lits.reserve(terms.size() - 1);
        auto first = lra_term(terms[0]);
        for (size_t i = 1; i < terms.size(); ++i) {
            if (!is_lra_term_syntax(terms[i])) break;
            auto e = first;
            e.add(lra_term(terms[i]), lra::Rational(-1));
            eq_lits.push_back(lra_register_equality(e));
        }
        if (eq_lits.size() == terms.size() - 1) {
            if (lra_simplify_conj_lits(eq_lits)) return -get_true_lit();
            if (opts_.lra_const_simplify) {
                if (eq_lits.empty()) return get_true_lit();
                if (eq_lits.size() == 1) return eq_lits.front();
            }
            if (eq_lits.size() == 1) return eq_lits.front();
            int y = fresh_bool_var();
            if (use_bool_cache) tseitin_cache_[t] = y;
            for (int l : eq_lits) {
                std::array<int,2> cl = {-y, l};
                ctx_.sat.add_clause(std::span<const int>(cl));
            }
            std::vector<int> back{y};
            for (int l : eq_lits) back.push_back(-l);
            ctx_.sat.add_clause(std::span<const int>(back));
            return y;
        }
    }

    static const std::unordered_map<std::string, lra::Relation> rels = {
        {"<", lra::Relation::Lt}, {"<=", lra::Relation::Le},
        {">", lra::Relation::Gt}, {">=", lra::Relation::Ge}
    };
    if (auto rit = rels.find(op); rit != rels.end() && t->term().size() == 2) {
        auto e = lra_term(t->term()[0]);
        e.add(lra_term(t->term()[1]), lra::Rational(-1));
        return lra_register_atom(e, rit->second);
    }
    if (op == "distinct" && t->term().size() >= 2 && is_lra_term_syntax(t->term()[0])) {
        auto terms = t->term();
        std::vector<int> diseqs;
        for (size_t i = 0; i < terms.size(); ++i) {
            if (!is_lra_term_syntax(terms[i])) break;
            for (size_t j = i + 1; j < terms.size(); ++j) {
                if (!is_lra_term_syntax(terms[j])) break;
                auto e = lra_term(terms[i]);
                e.add(lra_term(terms[j]), lra::Rational(-1));
                diseqs.push_back(lra_register_disequality(e));
            }
        }
        const size_t expected = terms.size() * (terms.size() - 1) / 2;
        if (diseqs.size() == expected) {
            if (lra_simplify_conj_lits(diseqs)) return -get_true_lit();
            if (opts_.lra_const_simplify) {
                if (diseqs.empty()) return get_true_lit();
                if (diseqs.size() == 1) return diseqs.front();
            }
            if (diseqs.empty()) return get_true_lit();
            if (diseqs.size() == 1) return diseqs.front();
            int y = fresh_bool_var();
            if (use_bool_cache) tseitin_cache_[t] = y;
            for (int l : diseqs) {
                std::array<int,2> cl = {-y, l};
                ctx_.sat.add_clause(std::span<const int>(cl));
            }
            std::vector<int> back{y};
            for (int l : diseqs) back.push_back(-l);
            ctx_.sat.add_clause(std::span<const int>(back));
            return y;
        }
    }
    if (t->term().empty()) {
        if (auto* binding = find_let_binding(op)) return lra_eval_lit(binding->term);
        auto dit = defined_fns_.find(op);
        if (dit != defined_fns_.end() && defined_bool_fns_.contains(op))
            return lra_eval_lit(dit->second);
        auto fit = ctx_.declared_fns.find(op);
        if (fit != ctx_.declared_fns.end() && ctx_.bool_fns.contains(fit->second)) {
            NodeId n = ctx_.nm.mk_const(fit->second);
            return ctx_.lit_for_node(n);
        }
    }

    throw std::runtime_error("unsupported QF_LRA formula operator: " + op);
}

void Smt2Visitor::lra_assert_formula(
    smt2parser::SMTLIBv2Parser::TermContext* t)
{
    while (t->GRW_Exclamation()) t = t->term()[0];
    if (t->GRW_Let()) {
        int frames = 0;
        while (t->GRW_Let() || t->GRW_Exclamation()) {
            if (t->GRW_Exclamation()) { t = t->term()[0]; continue; }
            let_env_.emplace_back();
            for (auto* vb : t->var_binding())
                let_env_.back()[vb->symbol()->getText()].term = vb->term();
            t = t->term()[0];
            ++frames;
        }
        lra_assert_formula(t);
        for (int i = 0; i < frames; ++i) let_env_.pop_back();
        return;
    }
    if (t->qual_identifier() != nullptr) {
        std::string op = identifier_name(t->qual_identifier()->identifier());
        if (op == "true") return;
        if (op == "false") { ctx_.sat.add_clause(std::span<const int>{}); return; }
        if (op == "and") {
            for (auto* sub : t->term()) lra_assert_formula(sub);
            return;
        }
        if (op == "=" && opts_.lra_direct_eq_atoms && t->term().size() >= 2 &&
            is_lra_term_syntax(t->term()[0])) {
            auto terms = t->term();
            std::vector<int> units;
            units.reserve(terms.size() - 1);
            auto first = lra_term(terms[0]);
            for (size_t i = 1; i < terms.size(); ++i) {
                if (!is_lra_term_syntax(terms[i])) break;
                auto e = first;
                e.add(lra_term(terms[i]), lra::Rational(-1));
                units.push_back(lra_register_direct_asserted_equality(e));
            }
            if (units.size() == terms.size() - 1) {
                for (int lit : units) {
                    std::array<int,1> cl = {lit};
                    ctx_.sat.add_clause(std::span<const int>(cl));
                }
                return;
            }
        }
        if (op == "or") {
            std::vector<int> lits;
            lra_collect_clause_lits(t, lits);
            if (lra_simplify_clause_lits(lits)) return;
            ctx_.sat.add_clause(std::span<const int>(lits));
            return;
        }
        if (op == "=>" && t->term().size() >= 2) {
            auto terms = t->term();
            std::vector<int> lits;
            for (size_t i = 0; i + 1 < terms.size(); ++i) lits.push_back(-lra_eval_lit(terms[i]));
            lits.push_back(lra_eval_lit(terms.back()));
            if (lra_simplify_clause_lits(lits)) return;
            ctx_.sat.add_clause(std::span<const int>(lits));
            return;
        }
    }
    int lit = lra_eval_lit(t);
    std::array<int,1> cl = {lit};
    ctx_.sat.add_clause(std::span<const int>(cl));
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
        if (logic == "QF_LRA" && !opts_.proof_file.empty())
            throw std::runtime_error("--proof is supported for QF_UF only, not QF_LRA");
        if (logic != "QF_EUF" && logic != "QF_UF" && logic != "QF_LRA") {
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
        uint32_t arity = !sorts.empty()
                         ? static_cast<uint32_t>(sorts.size() - 1)
                         : 0;
        bool ret_is_bool = !sorts.empty() && sorts.back()->getText() == "Bool";
        if (ctx_.is_lra_logic()) {
            if (arity != 0 || (sorts.back()->getText() != "Real" && sorts.back()->getText() != "Bool"))
                throw std::runtime_error("QF_LRA supports only 0-arity Real/Bool declarations");
        }
        SortId ret_sort_id = ret_is_bool ? BOOL_SORT : NULL_SORT;
        SymbolId sym = ctx_.nm.declare_symbol(name, arity, ret_sort_id);
        ctx_.declared_fns[name] = sym;
        // Mark if return sort is Bool
        if (ret_is_bool) {
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
        sym_to_sort_[sym] = decl.return_sort;
        if (ctx_.is_lra_logic() && decl.return_sort == "Real")
            ctx_.lra->declare_real(name);
        ctx_.declared_fn_order.push_back(std::move(decl));
    }
    else if (ctx->cmd_assert()) {
        auto terms = ctx->term();
        if (terms.empty()) throw std::runtime_error("assert: missing term");
        if (ctx_.is_lra_logic()) {
            pending_lra_asserts_.push_back(terms[0]);
            return nullptr;
        }
        // Assertions accumulate in pending_fmls_ and are encoded on check-sat.
        // This keeps one path for structural preprocessing and SAT-strengthening.
        // As an optimization, top-level (distinct t1 ... tn) with n>=3 is split
        // into n*(n-1)/2 individual NOT(EQ) assertions so the simplifier never
        // receives a single O(n^2)-deep AND tree.
        auto* term0 = terms[0];
        if (term0->qual_identifier() != nullptr) {
            std::string top_op = identifier_name(term0->qual_identifier()->identifier());
            if (top_op == "distinct" && term0->term().size() >= 3) {
                auto sub_terms = term0->term();
                std::vector<NodeId> nodes;
                nodes.reserve(sub_terms.size());
                for (auto* sub : sub_terms) nodes.push_back(visit_term(sub));
                NodeManager& nm = ctx_.nm;
                for (size_t i = 0; i < nodes.size(); ++i)
                    for (size_t j = i + 1; j < nodes.size(); ++j)
                        pending_fmls_.push_back(nm.mk_not(nm.mk_eq(nodes[i], nodes[j])));
                return nullptr;
            }
        }
        pending_fmls_.push_back(build_fml(terms[0]));
    }
    else if (ctx->cmd_checkSat()) {
        if (ctx_.is_lra_logic()) lra_flush_assertions();
        else flush_pending_fmls();
        last_result_ = ctx_.sat.solve();
        switch (last_result_) {
        case SolveResult::SAT:     std::cout << "sat\n";     break;
        case SolveResult::UNSAT:   std::cout << "unsat\n";   break;
        case SolveResult::UNKNOWN: std::cout << "unknown\n"; break;
        }
        if (opts_.lra_print_conflict_size && ctx_.is_lra_logic() &&
            last_result_ == SolveResult::UNSAT) {
            std::cerr << "lra-conflict-size: "
                      << (ctx_.lra ? ctx_.lra->last_conflict_size() : 0)
                      << "\n";
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

    // Let expression — handle nested lets iteratively to avoid stack overflow.
    if (ctx->GRW_Let()) {
        int frames = 0;
        while (ctx->GRW_Let() || ctx->GRW_Exclamation()) {
            if (ctx->GRW_Exclamation()) { ctx = ctx->term()[0]; continue; }
            let_env_.emplace_back();
            for (auto* vb : ctx->var_binding())
                let_env_.back()[vb->symbol()->getText()].term = vb->term();
            ctx = ctx->term()[0];
            ++frames;
        }
        NodeId result = visit_term(ctx);
        for (int i = 0; i < frames; ++i)
            let_env_.pop_back();
        return result;
    }

    if (ctx->qual_identifier() == nullptr)
        throw std::runtime_error("Unsupported term form");

    std::string name = identifier_name(ctx->qual_identifier()->identifier());

    // Let variable lookup (search innermost frame first)
    if (ctx->term().empty()) {
        if (auto* binding = find_let_binding(name)) {
            if (binding->term_node == NULL_NODE)
                binding->term_node = visit_term(binding->term);
            return binding->term_node;
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
        // Record the formula for proof emission so node_to_lean can inline-expand it.
        if (!opts_.proof_file.empty())
            ctx_.bool_fml_nodes[node] = build_fml(ctx);  // NodeId formula
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
        // Infer the sort from the then-branch symbol (works for both 0-ary
        // constants and n-ary function applications, since NodeData::sym is
        // always the head symbol whose return sort is in sym_to_sort_).
        std::string ite_sort;
        auto sit = sym_to_sort_.find(ctx_.nm.get(then_node).sym);
        if (sit != sym_to_sort_.end()) ite_sort = sit->second;

        SymbolId fresh = ctx_.nm.declare_symbol(
            "__ite_" + std::to_string(ite_counter_++), 0);
        sym_to_sort_[fresh] = ite_sort;  // allow nested ITEs to look this up
        NodeId result = ctx_.nm.mk_const(fresh);
        ite_node_cache_[ctx] = result;
        // Register as a declared constant so the Lean emitter can emit a
        // variable declaration for it.
        { FnDecl d; d.sym = fresh; d.return_sort = ite_sort;
          ctx_.declared_fn_order.push_back(std::move(d)); }
        // Store ite info for proof emission (inline expansion in Lean).
        if (!opts_.proof_file.empty())
            ctx_.ite_nodes[result] = IteInfo{build_fml(ctx->term()[0]), then_node, else_node};  // cond is NodeId
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
        if (ctx_.bool_fns.contains(sym)) link_bool_term_to_euf(node);
        return node;
    }

    std::vector<NodeId> args;
    for (auto* sub : ctx->term())
        args.push_back(visit_term(sub));
    NodeId node = ctx_.nm.mk_app(sym, std::span<const NodeId>(args));
    if (ctx_.bool_fns.contains(sym)) link_bool_term_to_euf(node);
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

    // Let expression: push bindings iteratively to avoid stack overflow.
    if (ctx->GRW_Let()) {
        int frames = 0;
        while (ctx->GRW_Let() || ctx->GRW_Exclamation()) {
            if (ctx->GRW_Exclamation()) { ctx = ctx->term()[0]; continue; }
            let_env_.emplace_back();
            for (auto* vb : ctx->var_binding())
                let_env_.back()[vb->symbol()->getText()].term = vb->term();
            ctx = ctx->term()[0];
            ++frames;
        }
        assert_formula(ctx);
        for (int i = 0; i < frames; ++i)
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

        // (xor A B [C ...]) — left-assoc; assert the whole expression is true.
        // For binary: directly add 2 clauses; for n-ary: use eval_lit + unit clause.
        if (op == "xor" && ctx->term().size() == 2) {
            int a = eval_lit(ctx->term()[0]);
            int b = eval_lit(ctx->term()[1]);
            std::array<int, 2> c1 = {a, b};
            std::array<int, 2> c2 = {-a, -b};
            ctx_.sat.add_clause(std::span<const int>(c1));
            ctx_.sat.add_clause(std::span<const int>(c2));
            return;
        }
        if (op == "xor" && ctx->term().size() >= 3) {
            int lit = eval_lit(ctx);
            std::array<int, 1> cl = {lit};
            ctx_.sat.add_clause(std::span<const int>(cl));
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

        // (= t1 t2 ... tn) n >= 3 — chained equality: assert each consecutive pair.
        if (op == "=" && ctx->term().size() >= 3) {
            auto terms = ctx->term();
            if (is_bool_sorted(terms[0])) {
                for (size_t i = 0; i + 1 < terms.size(); ++i) {
                    int p = eval_lit(terms[i]);
                    int q = eval_lit(terms[i + 1]);
                    std::array<int, 2> c1 = {-p, q};
                    std::array<int, 2> c2 = { p, -q};
                    ctx_.sat.add_clause(std::span<const int>(c1));
                    ctx_.sat.add_clause(std::span<const int>(c2));
                }
            } else {
                for (size_t i = 0; i + 1 < terms.size(); ++i) {
                    NodeId ti = visit_term(terms[i]);
                    NodeId tj = visit_term(terms[i + 1]);
                    int lit = ctx_.euf.register_equality(ti, tj);
                    std::array<int, 1> cl = {lit};
                    ctx_.sat.add_clause(std::span<const int>(cl));
                }
            }
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
            if (dit != defined_fns_.end() && defined_bool_fns_.contains(op)) {
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

    // Let expression: push bindings iteratively to avoid stack overflow.
    if (ctx->GRW_Let()) {
        int frames = 0;
        while (ctx->GRW_Let() || ctx->GRW_Exclamation()) {
            if (ctx->GRW_Exclamation()) { ctx = ctx->term()[0]; continue; }
            let_env_.emplace_back();
            for (auto* vb : ctx->var_binding())
                let_env_.back()[vb->symbol()->getText()].term = vb->term();
            ctx = ctx->term()[0];
            ++frames;
        }
        collect_clause_lits(ctx, lits);
        for (int i = 0; i < frames; ++i)
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

    // Let expression — handle nested lets iteratively to avoid stack overflow.
    if (ctx->GRW_Let()) {
        int frames = 0;
        while (ctx->GRW_Let() || ctx->GRW_Exclamation()) {
            if (ctx->GRW_Exclamation()) { ctx = ctx->term()[0]; continue; }
            let_env_.emplace_back();
            for (auto* vb : ctx->var_binding())
                let_env_.back()[vb->symbol()->getText()].term = vb->term();
            ctx = ctx->term()[0];
            ++frames;
        }
        int result = eval_lit(ctx);
        for (int i = 0; i < frames; ++i)
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

    // (= t1 t2 ... tn) n >= 3 — chained equality: Tseitin y ↔ (∧_i (= ti t{i+1}))
    if (op == "=" && ctx->term().size() >= 3) {
        auto cit = tseitin_cache_.find(ctx);
        if (cit != tseitin_cache_.end()) return cit->second;
        int y = ctx_.euf.new_var();
        tseitin_cache_[ctx] = y;
        auto terms = ctx->term();
        std::vector<int> sub_lits;
        if (is_bool_sorted(terms[0])) {
            for (size_t i = 0; i + 1 < terms.size(); ++i) {
                int p = eval_lit(terms[i]);
                int q = eval_lit(terms[i + 1]);
                int x = ctx_.euf.new_var();
                { std::array<int,3> cl = {-x, -p,  q}; ctx_.sat.add_clause(std::span<const int>(cl)); }
                { std::array<int,3> cl = {-x,  p, -q}; ctx_.sat.add_clause(std::span<const int>(cl)); }
                { std::array<int,3> cl = {-p, -q,  x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
                { std::array<int,3> cl = { p,  q,  x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
                sub_lits.push_back(x);
            }
        } else {
            for (size_t i = 0; i + 1 < terms.size(); ++i) {
                NodeId ti = visit_term(terms[i]);
                NodeId tj = visit_term(terms[i + 1]);
                sub_lits.push_back(ctx_.euf.register_equality(ti, tj));
            }
        }
        for (int l : sub_lits) {
            std::array<int,2> cl = {-y, l};
            ctx_.sat.add_clause(std::span<const int>(cl));
        }
        std::vector<int> bwd = {y};
        for (int l : sub_lits) bwd.push_back(-l);
        ctx_.sat.add_clause(std::span<const int>(bwd));
        return y;
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

    // (xor A B [C ...]) — left-associative fold; each step: x ↔ (prev ⊕ arg)
    if (op == "xor" && ctx->term().size() >= 2) {
        auto cit = tseitin_cache_.find(ctx);
        if (cit != tseitin_cache_.end()) return cit->second;
        auto terms = ctx->term();
        int x = eval_lit(terms[0]);
        for (size_t i = 1; i < terms.size(); ++i) {
            int a = x;
            int b = eval_lit(terms[i]);
            x = ctx_.euf.new_var();
            // x → (A ∨ B):    ¬x ∨ A ∨ B
            { std::array<int,3> cl = {-x,  a,  b}; ctx_.sat.add_clause(std::span<const int>(cl)); }
            // x → (¬A ∨ ¬B):  ¬x ∨ ¬A ∨ ¬B
            { std::array<int,3> cl = {-x, -a, -b}; ctx_.sat.add_clause(std::span<const int>(cl)); }
            // (A ∧ ¬B) → x:   ¬A ∨ B ∨ x
            { std::array<int,3> cl = {-a,  b,  x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
            // (¬A ∧ B) → x:    A ∨ ¬B ∨ x
            { std::array<int,3> cl = { a, -b,  x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        }
        tseitin_cache_[ctx] = x;
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
        if (auto* binding = find_let_binding(op))
            return eval_lit(binding->term);
        // Bool-valued 0-ary declared symbol
        auto fit = ctx_.declared_fns.find(op);
        if (fit != ctx_.declared_fns.end()
            && ctx_.bool_fns.contains(fit->second)) {
            NodeId n = ctx_.nm.mk_const(fit->second);
            return ctx_.lit_for_node(n);
        }
        // 0-arity define-fun macro expansion
        {
            auto dit = defined_fns_.find(op);
            if (dit != defined_fns_.end() && defined_bool_fns_.contains(op))
                return eval_lit(dit->second);
        }
        throw std::runtime_error("Unknown Bool variable: " + op);
    }

    // n-ary Bool predicate application
    auto fit = ctx_.declared_fns.find(op);
    if (fit != ctx_.declared_fns.end()
        && ctx_.bool_fns.contains(fit->second)) {
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
// Formula building (parse-tree → NodeId)
// ============================================================================

NodeId Smt2Visitor::build_fml(
    smt2parser::SMTLIBv2Parser::TermContext* ctx)
{
    NodeManager& nm = ctx_.nm;

    // Unwrap annotation wrappers iteratively.
    while (ctx->GRW_Exclamation()) ctx = ctx->term()[0];

    // Handle nested lets iteratively to avoid stack overflow on deeply-nested let chains.
    if (ctx->GRW_Let()) {
        int frames = 0;
        while (ctx->GRW_Let() || ctx->GRW_Exclamation()) {
            if (ctx->GRW_Exclamation()) { ctx = ctx->term()[0]; continue; }
            let_env_.emplace_back();
            for (auto* vb : ctx->var_binding())
                let_env_.back()[vb->symbol()->getText()].term = vb->term();
            ctx = ctx->term()[0];
            ++frames;
        }
        NodeId result = build_fml(ctx);
        for (int i = 0; i < frames; ++i)
            let_env_.pop_back();
        return result;
    }

    if (ctx->qual_identifier() == nullptr)
        throw std::runtime_error("Unsupported formula form in build_fml");

    std::string op = identifier_name(ctx->qual_identifier()->identifier());

    // Boolean constants
    if (op == "true")  return nm.mk_true();
    if (op == "false") return nm.mk_false();

    // Connectives
    if (op == "not" && ctx->term().size() == 1) {
        // Unroll NOT chains iteratively to avoid stack overflow on deep nesting.
        int neg_count = 1;
        auto* inner = ctx->term()[0];
        while (inner->GRW_Exclamation()) inner = inner->term()[0];
        while (!inner->GRW_Let() && inner->qual_identifier() != nullptr &&
               identifier_name(inner->qual_identifier()->identifier()) == "not" &&
               inner->term().size() == 1) {
            ++neg_count;
            inner = inner->term()[0];
            while (inner->GRW_Exclamation()) inner = inner->term()[0];
        }
        NodeId result = build_fml(inner);
        if (neg_count % 2 == 1) result = nm.mk_not(result);
        return result;
    }

    if (op == "and") {
        auto terms = ctx->term();
        if (terms.empty()) return nm.mk_true();
        // Flatten nested ANDs iteratively to avoid stack overflow on deeply-nested formulas.
        using TC = smt2parser::SMTLIBv2Parser::TermContext;
        std::vector<TC*> work, flat;
        for (auto* t : terms | std::views::reverse) work.push_back(t);
        while (!work.empty()) {
            TC* t = work.back(); work.pop_back();
            while (t->GRW_Exclamation()) t = t->term()[0];
            if (!t->GRW_Let() && t->qual_identifier() != nullptr &&
                identifier_name(t->qual_identifier()->identifier()) == "and") {
                auto sub = t->term();
                for (auto* s : sub | std::views::reverse) work.push_back(s);
            } else {
                flat.push_back(t);
            }
        }
        std::vector<NodeId> ids;
        ids.reserve(flat.size());
        for (auto* t : flat) ids.push_back(build_fml(t));
        if (opts_.nary) return nm.mk_and(ids);
        NodeId r = ids[0];
        for (size_t i = 1; i < ids.size(); ++i) r = nm.mk_and(r, ids[i]);
        return r;
    }

    if (op == "or") {
        auto terms = ctx->term();
        if (terms.empty()) return nm.mk_false();
        // Flatten nested ORs iteratively to avoid stack overflow on deeply-nested formulas.
        using TC = smt2parser::SMTLIBv2Parser::TermContext;
        std::vector<TC*> work, flat;
        for (auto* t : terms | std::views::reverse) work.push_back(t);
        while (!work.empty()) {
            TC* t = work.back(); work.pop_back();
            while (t->GRW_Exclamation()) t = t->term()[0];
            if (!t->GRW_Let() && t->qual_identifier() != nullptr &&
                identifier_name(t->qual_identifier()->identifier()) == "or") {
                auto sub = t->term();
                for (auto* s : sub | std::views::reverse) work.push_back(s);
            } else {
                flat.push_back(t);
            }
        }
        std::vector<NodeId> ids;
        ids.reserve(flat.size());
        for (auto* t : flat) ids.push_back(build_fml(t));
        if (opts_.nary) return nm.mk_or(ids);
        NodeId r = ids[0];
        for (size_t i = 1; i < ids.size(); ++i) r = nm.mk_or(r, ids[i]);
        return r;
    }

    // (=> A B ...) right-assoc: build as implies chain (A → (B → ... → last))
    if (op == "=>") {
        auto terms = ctx->term();
        // Build right-associatively: A → (B → C)
        NodeId result = build_fml(terms.back());
        for (int i = static_cast<int>(terms.size()) - 2; i >= 0; --i)
            result = nm.mk_implies(build_fml(terms[i]), result);
        return result;
    }

    if (op == "xor" && ctx->term().size() >= 2) {
        auto terms = ctx->term();
        NodeId result = build_fml(terms[0]);
        for (size_t i = 1; i < terms.size(); ++i)
            result = nm.mk_xor(result, build_fml(terms[i]));
        return result;
    }

    if (op == "ite" && ctx->term().size() == 3 && is_bool_sorted(ctx))
        return nm.mk_ite_bool(build_fml(ctx->term()[0]),
                               build_fml(ctx->term()[1]),
                               build_fml(ctx->term()[2]));

    // (= Bool Bool) — biconditional
    if (op == "=" && ctx->term().size() == 2 &&
        (is_bool_sorted(ctx->term()[0]) || is_bool_sorted(ctx->term()[1])))
        return nm.mk_iff(build_fml(ctx->term()[0]), build_fml(ctx->term()[1]));

    // (= t1 t2) — EUF equality atom: evaluate both sub-terms eagerly
    if (op == "=" && ctx->term().size() == 2) {
        NodeId lhs = visit_term(ctx->term()[0]);
        NodeId rhs = visit_term(ctx->term()[1]);
        return nm.mk_eq(lhs, rhs);
    }

    // (= t1 t2 ... tn) n >= 3 — chained: and of consecutive equality pairs
    if (op == "=" && ctx->term().size() >= 3) {
        auto terms = ctx->term();
        NodeId result = 0;
        if (is_bool_sorted(terms[0])) {
            result = nm.mk_iff(build_fml(terms[0]), build_fml(terms[1]));
            for (size_t i = 1; i + 1 < terms.size(); ++i)
                result = nm.mk_and(result, nm.mk_iff(build_fml(terms[i]),
                                                      build_fml(terms[i + 1])));
        } else {
            NodeId lhs = visit_term(terms[0]);
            NodeId rhs = visit_term(terms[1]);
            result = nm.mk_eq(lhs, rhs);
            for (size_t i = 1; i + 1 < terms.size(); ++i) {
                lhs = visit_term(terms[i]);
                rhs = visit_term(terms[i + 1]);
                result = nm.mk_and(result, nm.mk_eq(lhs, rhs));
            }
        }
        return result;
    }

    // (distinct t1 t2) — single disequality
    if (op == "distinct" && ctx->term().size() == 2) {
        NodeId lhs = visit_term(ctx->term()[0]);
        NodeId rhs = visit_term(ctx->term()[1]);
        return nm.mk_not(nm.mk_eq(lhs, rhs));
    }

    // (distinct t1 t2 ... tn) — expand to pairwise And(Not(Eq(...)))
    if (op == "distinct") {
        auto terms = ctx->term();
        std::vector<NodeId> nodes;
        nodes.reserve(terms.size());
        for (auto* sub : terms) nodes.push_back(visit_term(sub));
        NodeId result = nm.mk_not(nm.mk_eq(nodes[0], nodes[1]));
        for (size_t i = 0; i < nodes.size(); ++i)
            for (size_t j = i + 1; j < nodes.size(); ++j)
                if (i != 0 || j != 1)
                    result = nm.mk_and(result, nm.mk_not(nm.mk_eq(nodes[i], nodes[j])));
        return result;
    }

    // Let variable reference (0-ary, not a declared symbol)
    if (ctx->term().empty()) {
        if (auto* binding = find_let_binding(op)) {
            if (binding->fml_node == NULL_NODE)
                binding->fml_node = build_fml(binding->term);
            return binding->fml_node;
        }
    }

    // Bool-sorted 0-ary or n-ary predicate application — atom is the NodeId itself.
    // visit_term handles node creation and link_bool_term_to_euf eagerly.
    {
        auto fit = ctx_.declared_fns.find(op);
        if (fit != ctx_.declared_fns.end() && ctx_.bool_fns.contains(fit->second)) {
            if (ctx->term().empty()) {
                NodeId n = ctx_.nm.mk_const(fit->second);
                // A 0-ary Bool in formula position is pure SAT.  It only needs
                // EUF true/false bridging if visit_term sees it in a U-sorted
                // position, for example as an argument to an uninterpreted
                // function.  Bridging all propositional constants pollutes the
                // EUF trail on Boolean-circuit-heavy benchmarks.
                return n;  // Bool-sorted node IS the atom
            }
            std::vector<NodeId> args;
            for (auto* sub : ctx->term()) args.push_back(visit_term(sub));
            NodeId n = ctx_.nm.mk_app(fit->second, std::span<const NodeId>(args));
            link_bool_term_to_euf(n);
            if (seen_app_nodes_.insert(n).second)
                fn_applications_[fit->second].push_back({args, n});
            return n;  // Bool-sorted node IS the atom
        }
    }

    // 0-arity define-fun macro expansion
    if (ctx->term().empty()) {
        auto dit = defined_fns_.find(op);
        if (dit != defined_fns_.end() && defined_bool_fns_.contains(op))
            return build_fml(dit->second);
    }

    throw std::runtime_error("Unsupported formula in build_fml: " + op);
}

// ============================================================================
// Formula encoding (NodeId → SAT clauses)
// ============================================================================

static uint64_t node_pair_key(NodeId a, NodeId b)
{
    if (a > b) std::swap(a, b);
    return (static_cast<uint64_t>(a) << 32) | static_cast<uint64_t>(b);
}

static uint64_t lit_pair_key(int a, int b)
{
    if (a > b) std::swap(a, b);
    return (static_cast<uint64_t>(static_cast<uint32_t>(a)) << 32)
         | static_cast<uint32_t>(b);
}

static void split_top_level_conjunctions(std::vector<NodeId>& fmls, NodeManager& nm)
{
    std::vector<NodeId> split;
    split.reserve(fmls.size());

    for (NodeId f : fmls) {
        std::vector<NodeId> work{f};
        while (!work.empty()) {
            NodeId n = work.back();
            work.pop_back();
            if (nm.is_and(n)) {
                const auto& children = nm.get(n).children;
                for (NodeId child : children | std::views::reverse)
                    work.push_back(child);
            } else {
                split.push_back(n);
            }
        }
    }

    fmls = std::move(split);
}

// Smaller finite domains (notably NEQ004_size7 and NEQ027_size9) do not
// benefit enough from the extra clauses; size 10+ is where this paid off.
static constexpr size_t kMinFiniteDomainEqDefSize = 10;

void Smt2Visitor::collect_top_level_disequalities(NodeId f)
{
    if (!opts_.finite_domain_amo) return;

    NodeManager& nm = ctx_.nm;
    std::vector<NodeId> work{f};
    while (!work.empty()) {
        NodeId n = work.back();
        work.pop_back();
        if (nm.is_and(n)) {
            for (NodeId c : nm.get(n).children)
                work.push_back(c);
            continue;
        }
        if (!nm.is_not(n)) continue;
        NodeId child = nm.get(n).children[0];
        if (!nm.is_eq(child)) continue;
        NodeId a = nm.get(child).children[0];
        NodeId b = nm.get(child).children[1];
        if (a != b)
            top_level_diseq_pairs_.insert(node_pair_key(a, b));
    }
}

void Smt2Visitor::remember_finite_domain_eq_lit(NodeId lhs, NodeId rhs, int lit)
{
    if (!opts_.finite_domain_amo || top_level_diseq_pairs_.empty() || lhs == rhs) return;
    if (!finite_domain_eq_lits_seen_.insert(lit).second) return;

    auto add_for_endpoint = [&](NodeId endpoint, NodeId other) {
        auto& seen = finite_domain_eqs_by_endpoint_[endpoint];
        for (const EqEndpointLit& prev : seen) {
            if (prev.other == other) continue;
            if (!top_level_diseq_pairs_.contains(node_pair_key(prev.other, other))) continue;
            uint64_t key = lit_pair_key(prev.lit, lit);
            if (!finite_domain_amo_seen_.insert(key).second) continue;
            std::array<int,2> cl = {-prev.lit, -lit};
            ctx_.sat.add_clause(std::span<const int>(cl));
            ++stats_.preproc_finite_domain_amo_clauses;
        }
        seen.push_back({other, lit});
    };

    add_for_endpoint(lhs, rhs);
    add_for_endpoint(rhs, lhs);
}

bool Smt2Visitor::known_equality_lit(NodeId lhs, NodeId rhs, int& lit)
{
    if (lhs == rhs) {
        lit = get_true_lit();
        return true;
    }
    if (!top_level_diseq_pairs_.empty() &&
        top_level_diseq_pairs_.contains(node_pair_key(lhs, rhs))) {
        lit = -get_true_lit();
        return true;
    }
    return false;
}

void Smt2Visitor::collect_finite_domain_terms(NodeId f)
{
    if (!opts_.finite_domain_amo || !opts_.finite_domain_eq_defs) return;

    NodeManager& nm = ctx_.nm;
    std::vector<NodeId> work{f};
    while (!work.empty()) {
        NodeId n = work.back();
        work.pop_back();

        if (nm.is_and(n)) {
            for (NodeId c : nm.get(n).children)
                work.push_back(c);
            continue;
        }
        if (!nm.is_or(n)) continue;

        const auto& children = nm.get(n).children;
        if (children.size() < 2) continue;

        auto try_candidate = [&](NodeId term) -> bool {
            std::vector<NodeId> values;
            values.reserve(children.size());

            for (NodeId child : children) {
                if (!nm.is_eq(child)) return false;
                NodeId a = nm.get(child).children[0];
                NodeId b = nm.get(child).children[1];
                if (a == term && b != term) {
                    values.push_back(b);
                } else if (b == term && a != term) {
                    values.push_back(a);
                } else {
                    return false;
                }
            }
            if (values.size() < kMinFiniteDomainEqDefSize) return false;

            for (size_t i = 0; i < values.size(); ++i) {
                for (size_t j = i + 1; j < values.size(); ++j) {
                    if (!top_level_diseq_pairs_.contains(node_pair_key(values[i], values[j])))
                        return false;
                }
            }

            auto [it, inserted] = finite_domain_terms_.try_emplace(term);
            if (!inserted && it->second.values.size() >= values.size()) return true;

            FiniteDomainInfo info;
            info.values = std::move(values);
            info.choice_lits.reserve(info.values.size());
            for (NodeId value : info.values) {
                int lit = ctx_.euf.register_equality(term, value);
                remember_finite_domain_eq_lit(term, value, lit);
                info.choice_lits.push_back(lit);
            }
            it->second = std::move(info);
            return true;
        };

        NodeId first = children.front();
        if (!nm.is_eq(first)) continue;
        NodeId a = nm.get(first).children[0];
        NodeId b = nm.get(first).children[1];
        if (try_candidate(a)) continue;
        (void)try_candidate(b);
    }
}

static int finite_domain_value_pos(const std::vector<NodeId>& values, NodeId value)
{
    auto it = std::find(values.begin(), values.end(), value);
    if (it == values.end()) return -1;
    return static_cast<int>(it - values.begin());
}

void Smt2Visitor::encode_finite_domain_eq_defs(NodeId f)
{
    if (!opts_.finite_domain_amo || !opts_.finite_domain_eq_defs) return;
    if (finite_domain_terms_.empty()) return;

    NodeManager& nm = ctx_.nm;
    std::vector<NodeId> work{f};
    while (!work.empty()) {
        NodeId n = work.back();
        work.pop_back();

        if (nm.is_not(n)) {
            work.push_back(nm.get(n).children[0]);
            continue;
        }
        if (nm.is_and(n) || nm.is_or(n) || nm.is_implies(n) || nm.is_xor(n) ||
            nm.is_iff(n) || nm.is_ite_bool(n)) {
            for (NodeId c : nm.get(n).children)
                work.push_back(c);
            continue;
        }
        if (!nm.is_eq(n)) continue;

        NodeId lhs = nm.get(n).children[0];
        NodeId rhs = nm.get(n).children[1];
        if (lhs == rhs) continue;

        auto lit = finite_domain_terms_.find(lhs);
        auto rit = finite_domain_terms_.find(rhs);
        if (lit == finite_domain_terms_.end() || rit == finite_domain_terms_.end()) continue;

        const FiniteDomainInfo& linfo = lit->second;
        const FiniteDomainInfo& rinfo = rit->second;
        if (linfo.values.size() != rinfo.values.size() || linfo.values.empty()) continue;
        if (linfo.values.size() < kMinFiniteDomainEqDefSize) continue;
        if (!finite_domain_eq_defs_seen_.insert(node_pair_key(lhs, rhs)).second) continue;

        std::vector<int> rpos_for_lval;
        rpos_for_lval.reserve(linfo.values.size());
        bool same_domain = true;
        for (NodeId value : linfo.values) {
            int pos = finite_domain_value_pos(rinfo.values, value);
            if (pos < 0) {
                same_domain = false;
                break;
            }
            rpos_for_lval.push_back(pos);
        }
        if (!same_domain) continue;

        int eq = ctx_.euf.register_equality(lhs, rhs);

        for (size_t i = 0; i < linfo.values.size(); ++i) {
            int li = linfo.choice_lits[i];
            int ri = rinfo.choice_lits[static_cast<size_t>(rpos_for_lval[i])];

            { std::array<int,3> cl = {-li, -ri, eq}; ctx_.sat.add_clause(std::span<const int>(cl)); }
            { std::array<int,3> cl = {-eq, -li, ri}; ctx_.sat.add_clause(std::span<const int>(cl)); }
            { std::array<int,3> cl = {-eq, -ri, li}; ctx_.sat.add_clause(std::span<const int>(cl)); }
            stats_.preproc_finite_domain_eq_def_clauses += 3;
        }
    }
}

// Return a SAT literal for a sub-formula; introduce Tseitin variable if needed.
int Smt2Visitor::lit_of_fml(NodeId f)
{
    NodeManager& nm = ctx_.nm;

    if (nm.is_true_node(f))  return get_true_lit();
    if (nm.is_false_node(f)) return -get_true_lit();
    if (nm.is_eq(f)) {
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        int known = 0;
        if (known_equality_lit(c0, c1, known))
            return known;
        int lit = ctx_.euf.register_equality(c0, c1);
        remember_finite_domain_eq_lit(c0, c1, lit);
        return lit;
    }
    if (nm.is_atom_node(f)) return ctx_.lit_for_node(f);
    if (nm.is_not(f))       return -lit_of_fml(nm.get(f).children[0]);

    // Compound — check Tseitin cache first.
    auto cit = fml_lit_cache_.find(f);
    if (cit != fml_lit_cache_.end()) return cit->second;
    int x = ctx_.euf.new_var();
    fml_lit_cache_[f] = x;

    if (nm.is_and(f)) {
        // N-ary Tseitin: one var x, N binary forward clauses {-x,leaf_i},
        // one backward clause {x,-l1,...,-lN}.
        std::vector<int> sub;
        for (NodeId c : nm.get(f).children) sub.push_back(lit_of_fml(c));
        for (int l : sub) { std::array<int,2> cl = {-x, l}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        std::vector<int> bwd{x};
        for (int l : sub) bwd.push_back(-l);
        ctx_.sat.add_clause(std::span<const int>(bwd));
    } else if (nm.is_or(f)) {
        std::vector<int> sub;
        for (NodeId c : nm.get(f).children) sub.push_back(lit_of_fml(c));
        for (int l : sub) { std::array<int,2> cl = {-l, x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        std::vector<int> fwd{-x};
        for (int l : sub) fwd.push_back(l);
        ctx_.sat.add_clause(std::span<const int>(fwd));
    } else if (nm.is_ite_bool(f)) {
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        NodeId c2 = nm.get(f).children[2];
        int c = lit_of_fml(c0);
        int t = lit_of_fml(c1);
        int e = lit_of_fml(c2);
        { std::array<int,3> cl = {-c,-t, x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,3> cl = {-c, t,-x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,3> cl = { c,-e, x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,3> cl = { c, e,-x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
    } else if (nm.is_implies(f)) {
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        int a = lit_of_fml(c0);
        int b = lit_of_fml(c1);
        // x ↔ (¬a ∨ b)
        { std::array<int,2> cl = { a, x};    ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,2> cl = {-b, x};    ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,3> cl = {-x,-a, b}; ctx_.sat.add_clause(std::span<const int>(cl)); }
    } else if (nm.is_xor(f)) {
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        int a = lit_of_fml(c0);
        int b = lit_of_fml(c1);
        { std::array<int,3> cl = {-x, a, b}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,3> cl = {-x,-a,-b}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,3> cl = {-a, b, x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,3> cl = { a,-b, x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
    } else if (nm.is_iff(f)) {
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        int p = lit_of_fml(c0);
        int q = lit_of_fml(c1);
        { std::array<int,3> cl = {-x,-p, q}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,3> cl = {-x, p,-q}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,3> cl = {-p,-q, x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,3> cl = { p, q, x}; ctx_.sat.add_clause(std::span<const int>(cl)); }
    } else {
        throw std::runtime_error("lit_of_fml: unexpected node kind");
    }
    return x;
}

// Assert a NodeId formula at the top level (add required SAT clauses).
void Smt2Visitor::encode_fml(NodeId f)
{
    NodeManager& nm = ctx_.nm;

    if (nm.is_true_node(f)) return;
    if (nm.is_false_node(f)) { ctx_.sat.add_clause(std::span<const int>{}); return; }

    if (nm.is_eq(f)) {
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        int known = 0;
        if (known_equality_lit(c0, c1, known)) {
            if (known < 0) ctx_.sat.add_clause(std::span<const int>{});
            return;
        }
        int l = ctx_.euf.register_equality(c0, c1);
        std::array<int,1> cl = {l};
        ctx_.sat.add_clause(std::span<const int>(cl));
        return;
    }
    if (nm.is_atom_node(f)) {
        std::array<int,1> cl = {ctx_.lit_for_node(f)};
        ctx_.sat.add_clause(std::span<const int>(cl));
        return;
    }
    if (nm.is_not(f)) {
        NodeId child = nm.get(f).children[0];
        if (nm.is_eq(child)) {
            NodeId c0 = nm.get(child).children[0];
            NodeId c1 = nm.get(child).children[1];
            if (c0 == c1) {
                ctx_.sat.add_clause(std::span<const int>{});
                return;
            }
            int l = ctx_.euf.register_equality(c0, c1);
            remember_finite_domain_eq_lit(c0, c1, l);
            std::array<int,1> cl = {-l};
            ctx_.sat.add_clause(std::span<const int>(cl));
            return;
        }
        if (nm.is_and(child)) {
            // NOT(AND(leaf1,...,leafN)): Tseitin variable x for the AND, then assert NOT(x).
            //   {-x, leaf_i}  for each i   (x → leaf_i)
            //   {x, -leaf1, ..., -leafN}   (all leaves → x)
            //   {-x}                        (NOT AND)
            // After BCP of {-x} the binary clauses are satisfied and the large clause
            // reduces to {-leaf1,...,-leafN}.  The binary clauses seed VSIDS activity
            // on the leaf literals before the main search begins.
            std::vector<int> leaf_lits;
            for (NodeId c : nm.get(child).children) leaf_lits.push_back(lit_of_fml(c));
            int x = ctx_.euf.new_var();
            for (int l : leaf_lits) {
                std::array<int,2> cl = {-x, l};
                ctx_.sat.add_clause(std::span<const int>(cl));
            }
            std::vector<int> back{x};
            for (int l : leaf_lits) back.push_back(-l);
            ctx_.sat.add_clause(std::span<const int>(back));
            { std::array<int,1> unit = {-x}; ctx_.sat.add_clause(std::span<const int>(unit)); }
            return;
        }
        std::array<int,1> cl = {-lit_of_fml(child)};
        ctx_.sat.add_clause(std::span<const int>(cl));
        return;
    }
    if (nm.is_and(f)) {
        for (NodeId c : nm.get(f).children) encode_fml(c);
        return;
    }
    if (nm.is_or(f)) {
        std::vector<int> lits;
        for (NodeId c : nm.get(f).children) lits.push_back(lit_of_fml(c));
        ctx_.sat.add_clause(std::span<const int>(lits));
        return;
    }
    if (nm.is_ite_bool(f)) {
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        NodeId c2 = nm.get(f).children[2];
        int c = lit_of_fml(c0);
        int t = lit_of_fml(c1);
        int e = lit_of_fml(c2);
        { std::array<int,2> cl = {-c, t}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,2> cl = { c, e}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        return;
    }
    if (nm.is_implies(f)) {
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        int a = lit_of_fml(c0);
        int b = lit_of_fml(c1);
        std::array<int,2> cl = {-a, b};
        ctx_.sat.add_clause(std::span<const int>(cl));
        return;
    }
    if (nm.is_xor(f)) {
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        int a = lit_of_fml(c0);
        int b = lit_of_fml(c1);
        { std::array<int,2> cl = {a, b};   ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,2> cl = {-a, -b}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        return;
    }
    if (nm.is_iff(f)) {
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        int p = lit_of_fml(c0);
        int q = lit_of_fml(c1);
        { std::array<int,2> cl = {-p, q}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        { std::array<int,2> cl = { p,-q}; ctx_.sat.add_clause(std::span<const int>(cl)); }
        return;
    }
    // Fallback: add a unit clause.
    std::array<int,1> cl = {lit_of_fml(f)};
    ctx_.sat.add_clause(std::span<const int>(cl));
}

// Run simplifier (if enabled), assert forced atoms, encode remaining formulas.
void Smt2Visitor::flush_pending_fmls()
{
    if (pending_fmls_.empty()) return;

    auto flush_t0 = std::chrono::steady_clock::now();

    NodeManager& nm = ctx_.nm;

    // Step A: NNF.
    if (opts_.nnf) {
        for (auto& f : pending_fmls_)
            f = to_nnf(f, nm, opts_.nnf_memo);
    }

    if (opts_.passes == 0)
        split_top_level_conjunctions(pending_fmls_, nm);

    // Preserve top-level disequality facts before simplification rewrites unit
    // disequality assertions to True.  Finite-domain AMO strengthening needs
    // these facts later when equality-choice disjunctions are encoded.
    if (opts_.finite_domain_amo) {
        for (NodeId f : pending_fmls_)
            collect_top_level_disequalities(f);
    }

    // Step A.5: Equality bridging under disjunctions.
    // Bridge-derived equalities are applied as permanent CC merges immediately
    // so they take effect regardless of whether the Simplifier is enabled.
    if (opts_.eq_bridge) {
        const size_t before = pending_fmls_.size();
        std::vector<BridgeEquality> bridge_equalities;
        BridgeStats bridge_stats;
        bridge_disjunctions(pending_fmls_, nm,
                            !opts_.proof_file.empty() ? &bridge_equalities : nullptr,
                            &bridge_stats);
        stats_.preproc_bridge_eqs += static_cast<uint64_t>(bridge_stats.derived_equalities);
        stats_.preproc_bridge_skipped += static_cast<uint64_t>(bridge_stats.skipped_or_nodes);
        for (size_t i = before; i < pending_fmls_.size(); ++i) {
            NodeId f = pending_fmls_[i];
            if (nm.is_eq(f)) {
                NodeId c0 = nm.get(f).children[0];
                NodeId c1 = nm.get(f).children[1];
                ctx_.euf.register_permanent_equality(c0, c1);
            }
        }
        for (const auto& be : bridge_equalities) {
            NodeId a = be.lhs, b = be.rhs;
            if (a > b) std::swap(a, b);
            ctx_.eq_bridge_sources[{a, b}] = {be.top_fml_idx, be.source_or};
        }
        pending_fmls_.resize(before);  // already in CC, don't re-encode
    }

    // Step B: Simplifier (only if passes > 0).
    // forced_proof_fmls: forced atoms to append to the proof snapshot.
    std::vector<NodeId> forced_proof_fmls;
    if (opts_.passes > 0) {
        stats_.preproc_fmls_in += static_cast<uint64_t>(pending_fmls_.size());

        Simplifier simp(nm);
        simp.set_flatten(opts_.flatten);
        {
            auto t0 = std::chrono::steady_clock::now();
            simp.run(pending_fmls_, opts_.passes);
            auto t1 = std::chrono::steady_clock::now();
            stats_.preproc_simp_ms += static_cast<uint64_t>(
                std::chrono::duration_cast<std::chrono::milliseconds>(t1 - t0).count());
        }

        stats_.preproc_passes_run    += static_cast<uint64_t>(simp.passes_run());
        stats_.preproc_forced_atoms  += static_cast<uint64_t>(simp.forced_atoms().size());
        stats_.preproc_diseq_folds   += static_cast<uint64_t>(simp.diseq_folds());
        for (NodeId f : pending_fmls_) {
            if (nm.is_true_node(f))  ++stats_.preproc_fmls_true_out;
            if (nm.is_false_node(f)) ++stats_.preproc_fmls_false_out;
        }

        // Assert every atom that was forced by unit propagation.
        // Positive Eq atoms are merged directly in the CC (no SAT variable
        // needed — the CC carries the merge permanently at level 0, and the
        // SAT solver never has to decide or undo it).  All other forced atoms
        // are still asserted as SAT unit clauses.
        for (const auto& [atom, positive] : simp.forced_atoms()) {
            if (nm.is_eq(atom) && positive) {
                NodeId c0 = nm.get(atom).children[0];
                NodeId c1 = nm.get(atom).children[1];
                ctx_.euf.register_permanent_equality(c0, c1);
            } else {
                int lit = 0;
                if (nm.is_eq(atom)) {
                    NodeId c0 = nm.get(atom).children[0];
                    NodeId c1 = nm.get(atom).children[1];
                    lit = ctx_.euf.register_equality(c0, c1);
                } else {
                    lit = ctx_.lit_for_node(atom);
                }
                int forced = positive ? lit : -lit;
                std::array<int,1> cl = {forced};
                ctx_.sat.add_clause(std::span<const int>(cl));
            }
            // Collect for proof snapshot: the EUF may propagate permanent
            // equalities (and forced negative atoms) as SAT unit literals
            // during solving; those literals may appear in theory clause
            // premises.  Without explicit hypotheses, bv_decide cannot
            // discharge those premises.
            if (!opts_.proof_file.empty())
                forced_proof_fmls.push_back(positive ? atom : nm.mk_not(atom));
        }
    }

    // Snapshot for proof output: taken after all simplification so that
    // the formula representation matches the SAT encoding (perm-equality
    // substitutions have already been applied by the simplifier).
    // Forced atoms are appended as additional hypotheses (see above).
    if (!opts_.proof_file.empty()) {
        proof_fmls_ = pending_fmls_;
        for (NodeId f : forced_proof_fmls)
            proof_fmls_.push_back(f);
    }

    // Step C: Encode.
    if (opts_.finite_domain_amo) {
        for (NodeId f : pending_fmls_)
            collect_top_level_disequalities(f);
        if (opts_.finite_domain_eq_defs && opts_.proof_file.empty()) {
            for (NodeId f : pending_fmls_)
                collect_finite_domain_terms(f);
            for (NodeId f : pending_fmls_)
                encode_finite_domain_eq_defs(f);
        }
    }

    for (NodeId f : pending_fmls_)
        encode_fml(f);
    pending_fmls_.clear();
    fml_lit_cache_.clear();

    auto flush_t1 = std::chrono::steady_clock::now();
    stats_.preproc_flush_ms += static_cast<uint64_t>(
        std::chrono::duration_cast<std::chrono::milliseconds>(flush_t1 - flush_t0).count());
}

// ============================================================================
// Model printing
// ============================================================================

void Smt2Visitor::print_model()
{
    if (ctx_.is_lra_logic()) {
        lra_model_value_cache_.clear();
        std::cout << "(model\n";
        for (const auto& decl : ctx_.declared_fn_order) {
            const std::string sym_name = ctx_.nm.symbol_table().get(decl.sym).name;
            if (decl.param_sorts.empty() && decl.return_sort == "Real") {
                auto v = lra_model_value(sym_name).value_or(lra::Rational(0));
                std::cout << "  (define-fun " << sym_name << " () Real\n"
                          << "    " << v << ")\n";
            } else if (decl.param_sorts.empty() && decl.return_sort == "Bool") {
                NodeId node = ctx_.nm.mk_const(decl.sym);
                auto it = ctx_.node_to_lit.find(node);
                bool val = it != ctx_.node_to_lit.end() && ctx_.sat.val(it->second) == it->second;
                std::cout << "  (define-fun " << sym_name << " () Bool\n"
                          << "    " << (val ? "true" : "false") << ")\n";
            }
        }
        std::cout << ")\n";
        return;
    }

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
    // sat.val(lit) returns lit when lit is satisfied, -lit when falsified.
    // We check v == stored (not v > 0) to handle negative literals correctly:
    // node_to_lit may store negative literals (e.g. -eq from binary distinct).
    auto bool_for = [&](NodeId node) -> std::string {
        auto it = ctx_.node_to_lit.find(node);
        if (it == ctx_.node_to_lit.end()) return "false";
        int stored = it->second;
        int v = ctx_.sat.val(stored);
        return (v == stored) ? "true" : "false";
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
                         + entries[i].val + "\n        " + std::move(body) + ")";
                }
                std::cout << "    " << body << ")\n";
            }
        }
    }

    std::cout << ")\n";
}

} // namespace llm2smt
