#include "proof/lean_emitter.h"

#include <algorithm>
#include <cctype>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace llm2smt {

// ============================================================================
// Helpers
// ============================================================================

// Lean 4 syntax keywords and common Prelude/Std identifiers that cannot be
// used as plain declaration names.  Any SMT symbol matching one of these is
// wrapped in «» guillemets.
static bool is_lean_reserved(const std::string& s)
{
    // Keep this list sorted for easy auditing.
    static const std::unordered_set<std::string> reserved = {
        // Lean 4 syntax keywords
        "abbrev", "attribute", "axiom", "by", "calc", "class", "def",
        "deriving", "do", "else", "end", "example", "export", "extends",
        "finally", "for", "from", "fun", "have", "if", "import", "in",
        "infix", "infixl", "infixr", "instance", "let", "macro", "match",
        "mutual", "namespace", "noncomputable", "notation", "open", "opaque",
        "partial", "postfix", "prefix", "private", "protected", "return",
        "section", "show", "structure", "syntax", "theorem", "then", "try",
        "unless", "unsafe", "universe", "where", "with",
        // Common Lean 4 Prelude / Std identifiers that conflict as axiom names
        "and", "bool", "char", "false", "id", "int", "list", "not", "or",
        "option", "prod", "string", "true", "type", "unit",
    };
    return reserved.count(s) != 0;
}

// Convert an SMT-LIB symbol name to a valid Lean identifier.
// Strips |...| quoting.  Names that contain non-alphanumeric/underscore
// characters, or that clash with Lean 4 keywords / Prelude names, are
// wrapped in «» guillemets so Lean accepts them as raw identifiers.
static std::string lean_ident(const std::string& name)
{
    std::string inner = name;
    // Strip | | quoting if present
    if (inner.size() >= 2 && inner.front() == '|' && inner.back() == '|')
        inner = inner.substr(1, inner.size() - 2);

    if (inner.empty()) return "x";

    // Check whether the name is a valid plain Lean identifier syntactically.
    bool plain = std::isalpha(static_cast<unsigned char>(inner[0])) || inner[0] == '_';
    if (plain) {
        for (size_t i = 1; i < inner.size(); ++i) {
            char c = inner[i];
            if (!std::isalnum(static_cast<unsigned char>(c)) && c != '_') {
                plain = false;
                break;
            }
        }
    }

    // Syntactically non-plain: wrap in «» (guillemets allow arbitrary characters).
    if (!plain)
        return "«" + inner + "»";
    // Reserved Lean 4 keyword / Prelude name: append _ to get a fresh identifier.
    // Note: «foo» and foo are the SAME identifier in Lean 4, so wrapping doesn't help.
    if (is_lean_reserved(inner))
        return inner + "_";
    return inner;
}

// Map an SMT-LIB sort name to its Lean type string.
// "Bool" → "Prop"; everything else → lean_ident(name).
static std::string sort_to_lean_type(const std::string& sort_name)
{
    if (sort_name == "Bool") return "Prop";
    return lean_ident(sort_name);
}

// ============================================================================
// LeanEmitter member functions
// ============================================================================

std::string LeanEmitter::node_to_lean(NodeId n, const NodeManager& nm) const
{
    const NodeData& d = nm.get(n);
    const std::string& raw_name = nm.symbol_table().get(d.sym).name;
    // Map internal Bool-bridging sentinels to Lean's Prop constants so that
    // conflict clauses involving Bool-sorted predicates stay syntactically
    // valid (True and False are Prop values, matching `h : U → Prop`).
    if (raw_name == "__bool_true")  return "True";
    if (raw_name == "__bool_false") return "False";
    // Inline-expand U-sorted ite nodes to `(if cond then t else e)` so that
    // Lean has the full ite semantics without needing abstract constants.
    if (ctx_) {
        auto it = ctx_->ite_nodes.find(n);
        if (it != ctx_->ite_nodes.end()) {
            const IteInfo& info = it->second;
            return "(if " + fml_to_lean_cond(info.cond, nm)
                   + " then " + node_to_lean(info.then_node, nm)
                   + " else " + node_to_lean(info.else_node, nm) + ")";
        }
        auto bit = ctx_->bool_fml_nodes.find(n);
        if (bit != ctx_->bool_fml_nodes.end()) {
            // Inline-expand __bool_fml_N as a Prop expression (no decide wrapper),
            // so that equality comparisons with __bool_true/__bool_false (Prop) are
            // type-correct, and so it can be passed to functions with Bool parameter
            // sort (mapped to Prop in Lean).
            const FmlRef& f = bit->second;
            if (f->kind == FmlKind::Eq) {
                if (f->eq_lhs == f->eq_rhs) return "True";
                NodeId lhs = f->eq_lhs, rhs = f->eq_rhs;
                if (lhs > rhs) std::swap(lhs, rhs);
                return "(" + node_to_lean(lhs, nm) + " = " + node_to_lean(rhs, nm) + ")";
            }
            if (f->kind == FmlKind::Pred)
                return node_to_lean(f->pred, nm);
            // Compound formulas: fml_to_lean returns Prop via Bool→Prop coercion.
            return "(" + fml_to_lean(f, nm) + ")";
        }
    }
    std::string sanitized = lean_ident(raw_name);
    if (d.children.empty()) return sanitized;
    std::string result = "(" + sanitized;
    for (NodeId c : d.children) {
        result += " ";
        result += node_to_lean(c, nm);
    }
    result += ")";
    return result;
}

// Render formula as a Lean Prop WITHOUT wrapping atomic propositions in
// `decide (...)`.  Used as the condition of `if cond then X else Y` so that
// Lean's Classical ite (`@ite`) is used instead of Bool if-then-else.
// This avoids grind internally simplifying `if decide (p) then ...` to
// `if p then ...` while the goal atoms still say `if decide (p) then ...`.
std::string LeanEmitter::fml_to_lean_cond(FmlRef f, const NodeManager& nm) const
{
    switch (f->kind) {
    case FmlKind::True:  return "True";
    case FmlKind::False: return "False";
    case FmlKind::Eq: {
        if (f->eq_lhs == f->eq_rhs) return "True";
        NodeId lhs = f->eq_lhs, rhs = f->eq_rhs;
        if (lhs > rhs) std::swap(lhs, rhs);
        return node_to_lean(lhs, nm) + " = " + node_to_lean(rhs, nm);
    }
    case FmlKind::Pred:
        return node_to_lean(f->pred, nm);
    case FmlKind::Not:
        if (f->children[0]->kind == FmlKind::Eq &&
            f->children[0]->eq_lhs == f->children[0]->eq_rhs)
            return "False";
        return "¬(" + fml_to_lean_cond(f->children[0], nm) + ")";
    case FmlKind::And: {
        std::string s = "(";
        for (size_t i = 0; i < f->children.size(); ++i) {
            if (i > 0) s += " ∧ ";
            s += fml_to_lean_cond(f->children[i], nm);
        }
        return s + ")";
    }
    case FmlKind::Or: {
        std::string s = "(";
        for (size_t i = 0; i < f->children.size(); ++i) {
            if (i > 0) s += " ∨ ";
            s += fml_to_lean_cond(f->children[i], nm);
        }
        return s + ")";
    }
    case FmlKind::Implies:
        return "(" + fml_to_lean_cond(f->children[0], nm) + " → "
               + fml_to_lean_cond(f->children[1], nm) + ")";
    case FmlKind::Xor:
        return "¬(" + fml_to_lean_cond(f->children[0], nm) + " ↔ "
               + fml_to_lean_cond(f->children[1], nm) + ")";
    case FmlKind::BoolEq:
        return "(" + fml_to_lean_cond(f->children[0], nm) + " ↔ "
               + fml_to_lean_cond(f->children[1], nm) + ")";
    case FmlKind::Ite: {
        const std::string c = fml_to_lean_cond(f->children[0], nm);
        const std::string t = fml_to_lean_cond(f->children[1], nm);
        const std::string e = fml_to_lean_cond(f->children[2], nm);
        return "((" + c + " → " + t + ") ∧ (¬(" + c + ") → " + e + "))";
    }
    }
    return "True";  // unreachable
}

std::string LeanEmitter::fml_to_lean(FmlRef f, const NodeManager& nm) const
{
    switch (f->kind) {
    case FmlKind::True:
        return "True";
    case FmlKind::False:
        return "False";
    case FmlKind::Eq: {
        // a = a is always true; emit "True" so bv_decide doesn't treat it as
        // an opaque atom that it could assign false (reflexivity is not built in).
        if (f->eq_lhs == f->eq_rhs) return "True";
        // Canonical order by NodeId so that a=b and b=a produce the same
        // string — bv_decide must not see them as distinct opaque atoms.
        NodeId lhs = f->eq_lhs, rhs = f->eq_rhs;
        if (lhs > rhs) std::swap(lhs, rhs);
        return "decide (" + node_to_lean(lhs, nm) + " = " + node_to_lean(rhs, nm) + ")";
    }
    case FmlKind::Pred:
        return "decide (" + node_to_lean(f->pred, nm) + ")";
    case FmlKind::Not:
        // ¬(a = a) is always false; emit "False" so bv_decide can't satisfy it.
        if (f->children[0]->kind == FmlKind::Eq &&
            f->children[0]->eq_lhs == f->children[0]->eq_rhs)
            return "False";
        return "¬(" + fml_to_lean(f->children[0], nm) + ")";
    case FmlKind::And: {
        std::string s = "(";
        for (size_t i = 0; i < f->children.size(); ++i) {
            if (i > 0) s += " ∧ ";
            s += fml_to_lean(f->children[i], nm);
        }
        s += ")";
        return s;
    }
    case FmlKind::Or: {
        std::string s = "(";
        for (size_t i = 0; i < f->children.size(); ++i) {
            if (i > 0) s += " ∨ ";
            s += fml_to_lean(f->children[i], nm);
        }
        s += ")";
        return s;
    }
    case FmlKind::Implies:
        return "(" + fml_to_lean(f->children[0], nm) + " → "
               + fml_to_lean(f->children[1], nm) + ")";
    case FmlKind::Xor:
        // xor(a,b) ≡ ¬(a ↔ b)  — avoids non-standard Xor identifier
        return "¬(" + fml_to_lean(f->children[0], nm) + " ↔ "
               + fml_to_lean(f->children[1], nm) + ")";
    case FmlKind::BoolEq:
        return "(" + fml_to_lean(f->children[0], nm) + " ↔ "
               + fml_to_lean(f->children[1], nm) + ")";
    case FmlKind::Ite: {
        // ite(c,t,e) ≡ (c → t) ∧ (¬c → e)  — avoids `if` which requires Decidable c.
        // The condition is expanded twice; parenthesise each occurrence so that
        // negation in the else-arm binds correctly for any condition shape.
        const std::string c = fml_to_lean(f->children[0], nm);
        const std::string t = fml_to_lean(f->children[1], nm);
        const std::string e = fml_to_lean(f->children[2], nm);
        return "((" + c + " → " + t + ") ∧ (¬(" + c + ") → " + e + "))";
    }
    }
    return "True";  // unreachable
}

std::string LeanEmitter::fn_type(const FnDecl& fn, bool is_pred) const
{
    std::string result;
    for (const std::string& ps : fn.param_sorts)
        result += sort_to_lean_type(ps) + " → ";
    result += is_pred ? "Prop" : sort_to_lean_type(fn.return_sort);
    return result;
}

void LeanEmitter::emit(std::ostream& out,
                       const SmtContext& ctx,
                       const std::vector<FmlRef>& proof_fmls,
                       const std::vector<std::vector<int>>& proof_conflicts)
{
    ctx_ = &ctx;
    ite_proxy_for_.clear();
    const NodeManager& nm = ctx.nm;

    // Precompute ite_id → proxy_id and ite_id → hyp_name from assertions of
    // the form (proxy = ite_node).  We only record the first proxy found for
    // each ite node.  The hyp_name is used to add the single relevant
    // hypothesis to standalone theorems that need it (judicious context loading).
    std::unordered_map<NodeId, std::string> ite_proxy_hyp_name;
    for (size_t i = 0; i < proof_fmls.size(); ++i) {
        const FmlRef& f = proof_fmls[i];
        if (f->kind != FmlKind::Eq) continue;
        NodeId a = f->eq_lhs, b = f->eq_rhs;
        std::string hname = "hyp" + std::to_string(i + 1);
        if (ctx.ite_nodes.count(a) && !ctx.ite_nodes.count(b)
                && !ite_proxy_for_.count(a)) {
            ite_proxy_for_[a] = b;
            ite_proxy_hyp_name[a] = hname;
        } else if (ctx.ite_nodes.count(b) && !ctx.ite_nodes.count(a)
                && !ite_proxy_for_.count(b)) {
            ite_proxy_for_[b] = a;
            ite_proxy_hyp_name[b] = hname;
        }
    }

    out << "import Std.Tactic.BVDecide\n\n";
    out << "noncomputable section\n";
    out << "open Classical\n\n";

    // ── Sorts ──────────────────────────────────────────────────────────────
    std::vector<std::string> sort_names;
    sort_names.reserve(ctx.declared_sorts.size());
    for (const auto& [name, arity] : ctx.declared_sorts)
        sort_names.push_back(name);
    std::sort(sort_names.begin(), sort_names.end());

    for (const std::string& sname : sort_names)
        out << "axiom " << lean_ident(sname) << " : Type\n";

    // ── Declared functions (each on its own line, in declaration order) ─────
    for (const FnDecl& decl : ctx.declared_fn_order) {
        const std::string& fname = nm.symbol_table().get(decl.sym).name;
        // Skip Bool-bridging sentinels and ite proxy constants (__ite_N).
        // Ite nodes are inlined as `(if cond then t else e)` in node_to_lean,
        // so they need no Lean axiom declaration.
        if (fname == "__bool_true" || fname == "__bool_false"
            || fname.rfind("__ite_", 0) == 0)
            continue;
        bool is_bool = (decl.return_sort == "Bool");
        out << "axiom " << lean_ident(fname) << " : " << fn_type(decl, is_bool) << "\n";
    }

    // ── Assertions ─────────────────────────────────────────────────────────
    // Collections used in `theorem contradiction`:
    //   hyp_names        — hyp axioms loaded via (have X := X) for bv_decide
    //   standalone_names — all theory lemmas proved as standalone theorems,
    //                      loaded via (have X := X) in contradiction
    //
    // All EUF theory lemmas (ite_pos_k, ite_neg_k, ite_bridge_k, cl_k) are
    // emitted as standalone `theorem X : body := by grind` declarations.
    // Grind sees global `axiom hyp_k` declarations without needing local
    // `have hyp_k := hyp_k` bindings, so standalone theorems can use
    // problem hypotheses directly.
    std::vector<std::string> hyp_names;
    std::vector<std::string> standalone_names;

    for (size_t i = 0; i < proof_fmls.size(); ++i) {
        std::string hname = "hyp" + std::to_string(i + 1);
        out << "axiom " << hname << " : " << fml_to_lean(proof_fmls[i], nm) << "\n";
        hyp_names.push_back(hname);
    }

    out << "\n";

    // ── Build reverse maps ──────────────────────────────────────────────────

    // SAT literal → NodeId (for Bool-sorted nodes)
    std::unordered_map<int, NodeId> lit_to_node;
    lit_to_node.reserve(ctx.node_to_lit.size());
    for (const auto& [nid, lit] : ctx.node_to_lit)
        lit_to_node[lit] = nid;

    const auto& lit_to_atom = ctx.euf.lit_to_atom();

    // Canonical equality atom (min_id, max_id) → hyp_name for Eq hypotheses.
    // Used to load only the specific hypothesis needed when a theory lemma
    // has a positive literal that is directly asserted in the problem.
    std::unordered_map<uint64_t, std::string> eq_atom_to_hyp;
    for (size_t i = 0; i < proof_fmls.size(); ++i) {
        const FmlRef& f = proof_fmls[i];
        if (f->kind != FmlKind::Eq) continue;
        NodeId a = f->eq_lhs, b = f->eq_rhs;
        if (a == b) continue;
        if (a > b) std::swap(a, b);
        uint64_t key = ((uint64_t)a << 32) | (uint64_t)b;
        if (!eq_atom_to_hyp.count(key))
            eq_atom_to_hyp[key] = hyp_names[i];
    }

    // ── Ite semantic clauses ────────────────────────────────────────────────
    // For each U-sorted ite node, add two clauses encoding its semantics:
    //   ¬cond ∨ decide(eff = then)   (if cond: eff equals then-branch)
    //   cond ∨ decide(eff = else)    (if ¬cond: eff equals else-branch)
    //
    // "eff" is the proxy constant if one exists (preferred), otherwise the
    // inlined ite expression.  All are emitted as standalone theorems;
    // grind sees the global `axiom hyp_k` declarations directly.
    size_t ite_clause_idx = 0;
    for (const auto& [ite_id, info] : ctx.ite_nodes) {
        const std::string cond_lean = fml_to_lean(info.cond, nm);

        auto proxy_it = ite_proxy_for_.find(ite_id);
        bool has_proxy = (proxy_it != ite_proxy_for_.end());
        NodeId eff_id = has_proxy ? proxy_it->second : ite_id;

        // then-branch: ¬cond ∨ decide(canon(eff, then))
        {
            NodeId lhs_id = eff_id, rhs_id = info.then_node;
            if (lhs_id > rhs_id) std::swap(lhs_id, rhs_id);
            std::string tname = "ite_pos_" + std::to_string(ite_clause_idx);
            std::string body = "¬(" + cond_lean + ") ∨ decide ("
                + node_to_lean(lhs_id, nm) + " = " + node_to_lean(rhs_id, nm) + ")";
            out << "theorem " << tname << " : " << body << " := by";
            if (has_proxy) {
                // Proxy-based: need the proxy=ite axiom in scope for grind.
                const std::string& pname = ite_proxy_hyp_name.at(ite_id);
                out << "\n  have " << pname << " := " << pname << "\n  grind\n";
            } else {
                out << " grind\n";
            }
            standalone_names.push_back(tname);
        }
        // else-branch: cond ∨ decide(canon(eff, else))
        {
            NodeId lhs_id = eff_id, rhs_id = info.else_node;
            if (lhs_id > rhs_id) std::swap(lhs_id, rhs_id);
            std::string tname = "ite_neg_" + std::to_string(ite_clause_idx);
            std::string body = "(" + cond_lean + ") ∨ decide ("
                + node_to_lean(lhs_id, nm) + " = " + node_to_lean(rhs_id, nm) + ")";
            out << "theorem " << tname << " : " << body << " := by";
            if (has_proxy) {
                const std::string& pname = ite_proxy_hyp_name.at(ite_id);
                out << "\n  have " << pname << " := " << pname << "\n  grind\n";
            } else {
                out << " grind\n";
            }
            standalone_names.push_back(tname);
        }
        ++ite_clause_idx;
    }

    // ── Ite bridging lemmas ─────────────────────────────────────────────────
    // When preprocessing substitutes a proxy node with the inlined ite expression
    // directly, new "shortcut" EUF atoms are created (e.g. __ite_N = X$next rather
    // than proxy = X$next).  These atoms appear in theory clauses but have no
    // corresponding Lean hypothesis, so bv_decide cannot derive the equality by
    // transitivity.
    //
    // For each such shortcut atom (ite_id = X where X is not the then/else
    // branch and not a known proxy), emit:
    //   decide(ite = X) ∨ ¬(decide(proxy = X))  := by grind
    {
        // Step 1: collect proxy nodes for each ite node from proof_fmls.
        std::unordered_map<NodeId, std::vector<NodeId>> ite_proxies;
        for (const FmlRef& f : proof_fmls) {
            if (f->kind != FmlKind::Eq) continue;
            NodeId a = f->eq_lhs, b = f->eq_rhs;
            if (ctx.ite_nodes.count(a) && !ctx.ite_nodes.count(b))
                ite_proxies[a].push_back(b);
            else if (ctx.ite_nodes.count(b) && !ctx.ite_nodes.count(a))
                ite_proxies[b].push_back(a);
        }

        // Step 2: for each ite node, find shortcut atoms and emit bridges.
        size_t bridge_idx = 0;
        for (const auto& [ite_id, info] : ctx.ite_nodes) {
            auto pxit = ite_proxies.find(ite_id);
            if (pxit == ite_proxies.end()) continue;
            const std::vector<NodeId>& proxies = pxit->second;

            bool has_proxy_for_ite = ite_proxy_for_.count(ite_id) != 0;

            // For proxied ites, emit bridges for ALL atoms involving the ite node,
            // including then/else branches.  Hypothesis formulas can create opaque
            // atoms d(branch = ite_inline) that bv_decide treats independently from
            // d(branch = proxy).  For non-proxied ites, then/else are handled by the
            // standalone ite_pos/ite_neg theorems so exclude them here.
            std::unordered_set<NodeId> non_shortcut;
            if (!has_proxy_for_ite) {
                non_shortcut.insert(info.then_node);
                non_shortcut.insert(info.else_node);
            }
            for (NodeId p : proxies) non_shortcut.insert(p);

            for (const auto& [var, atom] : lit_to_atom) {
                NodeId a = atom.lhs, b = atom.rhs;
                if (a != ite_id && b != ite_id) continue;
                NodeId other = (a == ite_id) ? b : a;
                if (non_shortcut.count(other)) continue;
                if (ctx.ite_nodes.count(other)) continue;  // other ite — skip

                // Canonical ordering for ite = other
                NodeId lhs_id = ite_id, rhs_id = other;
                if (lhs_id > rhs_id) std::swap(lhs_id, rhs_id);
                const std::string ite_eq_other =
                    "decide (" + node_to_lean(lhs_id, nm) + " = " + node_to_lean(rhs_id, nm) + ")";

                for (NodeId proxy : proxies) {
                    // Canonical ordering for proxy = other
                    NodeId p_lhs = proxy, p_rhs = other;
                    if (p_lhs > p_rhs) std::swap(p_lhs, p_rhs);
                    const std::string proxy_eq_other =
                        "decide (" + node_to_lean(p_lhs, nm) + " = " + node_to_lean(p_rhs, nm) + ")";

                    if (has_proxy_for_ite) {
                        // Emit BOTH bridge directions as standalone theorems.
                        // They need the proxy=ite axiom to prove, so load it explicitly.
                        //   Dir 1: d(ite=X) ∨ ¬d(proxy=X)
                        //     eliminates spurious: d(proxy=X)=true ∧ d(ite=X)=false
                        //   Dir 2: d(proxy=X) ∨ ¬d(ite=X)
                        //     eliminates spurious: d(ite=X)=true ∧ d(proxy=X)=false
                        // Also needed for branch atoms (then/else): hypothesis formulas
                        // like d(branch=ite_inline) appear as opaque atoms that bv_decide
                        // can assign independently of d(branch=proxy).
                        const std::string& pname = ite_proxy_hyp_name.at(ite_id);
                        std::string tname1 = "ite_bridge_" + std::to_string(bridge_idx++);
                        out << "theorem " << tname1 << " : " << ite_eq_other
                            << " ∨ ¬(" << proxy_eq_other << ") := by\n"
                            << "  have " << pname << " := " << pname << "\n  grind\n";
                        standalone_names.push_back(tname1);
                        std::string tname2 = "ite_bridge_" + std::to_string(bridge_idx++);
                        out << "theorem " << tname2 << " : " << proxy_eq_other
                            << " ∨ ¬(" << ite_eq_other << ") := by\n"
                            << "  have " << pname << " := " << pname << "\n  grind\n";
                        standalone_names.push_back(tname2);
                    } else {
                        // Ite has no proxy — pure EUF tautology.
                        std::string tname = "ite_bridge_" + std::to_string(bridge_idx++);
                        out << "theorem " << tname << " : " << ite_eq_other
                            << " ∨ ¬(" << proxy_eq_other << ") := by grind\n";
                        standalone_names.push_back(tname);
                    }
                }
            }
        }
    }

    // ── Eq-bridge lemmas ────────────────────────────────────────────────────
    // For each permanent equality (pa=pb) established by the eq-bridge preprocessor,
    // the source is an Or formula whose disjuncts encode the ways pa=pb can hold.
    // For each disjunct (typically a conjunction of EUF atoms), emit a simple
    // implication theorem that grind can prove in isolation:
    //   theorem eq_bridge_K : decide(A1) → decide(A2) → decide(pa=pb) := by grind
    // bv_decide then does the propositional case-split over the source hypothesis.
    {
        size_t ebr_idx = 0;
        for (const auto& [canonical_pair, bridge_info] : ctx.eq_bridge_sources) {
            NodeId pa = canonical_pair.first, pb = canonical_pair.second;
            // Conclusion: decide(pa=pb) — canonical pair is already min<max.
            std::string concl = "decide (" + node_to_lean(pa, nm)
                                 + " = " + node_to_lean(pb, nm) + ")";
            FmlRef src_fml = bridge_info.second;
            // Decompose Or into disjuncts (or treat atom as a single disjunct).
            std::vector<FmlRef> disjuncts;
            if (src_fml->kind == FmlKind::Or)
                disjuncts = src_fml->children;
            else
                disjuncts.push_back(src_fml);
            for (const FmlRef& disj : disjuncts) {
                // Decompose And into conjuncts (or treat atom as a single conjunct).
                std::vector<FmlRef> conjuncts;
                if (disj->kind == FmlKind::And)
                    conjuncts = disj->children;
                else
                    conjuncts.push_back(disj);
                std::string tname = "eq_bridge_" + std::to_string(ebr_idx++);
                out << "theorem " << tname << " : ";
                for (const FmlRef& atom : conjuncts)
                    out << fml_to_lean(atom, nm) << " → ";
                out << concl << " := by grind\n";
                standalone_names.push_back(tname);
            }
        }
    }

    // ── Theory lemmas (standalone theorems proved by grind) ─────────────────
    // EUF theory clauses are emitted as standalone `theorem cl_k : body := by grind`.
    // Grind sees global `axiom hyp_k` declarations directly, so no inline
    // `have hyp_k` bindings are needed.  After all theorems are declared,
    // `theorem contradiction` loads them via `have cl_k := cl_k` then calls
    // `bv_decide` for propositional closure.
    const auto& perm_deps_vec = ctx.euf.proof_unit_perm_deps();
    for (size_t i = 0; i < proof_conflicts.size(); ++i) {
        const auto& clause = proof_conflicts[i];
        std::string tname = "cl_" + std::to_string(i);
        std::string body;

        // Unit clause with perm deps: pure EUF transitivity / congruence chain.
        //   decide(pa0=pb0) → decide(pa1=pb1) → ... → decide(lhs=rhs)
        if (clause.size() == 1 && i < perm_deps_vec.size() && !perm_deps_vec[i].empty()) {
            int lit = clause[0];
            int var = (lit > 0) ? lit : -lit;
            auto eit = lit_to_atom.find(var);
            if (lit > 0 && eit != lit_to_atom.end()) {
                NodeId lhs_id = eit->second.lhs, rhs_id = eit->second.rhs;
                if (lhs_id > rhs_id) std::swap(lhs_id, rhs_id);
                for (const auto& [pa, pb] : perm_deps_vec[i]) {
                    NodeId a = pa, b = pb;
                    if (a > b) std::swap(a, b);
                    body += "decide (" + node_to_lean(a, nm) + " = "
                          + node_to_lean(b, nm) + ") → ";
                }
                body += "decide (" + node_to_lean(lhs_id, nm) + " = "
                      + node_to_lean(rhs_id, nm) + ")";
                out << "theorem " << tname << " : " << body << " := by grind\n";
                standalone_names.push_back(tname);
                continue;
            }
        }

        // Normal clause: optional perm-dep implications, then a disjunction.
        if (i < perm_deps_vec.size()) {
            for (const auto& [pa, pb] : perm_deps_vec[i]) {
                NodeId a = pa, b = pb;
                if (a > b) std::swap(a, b);
                body += "decide (" + node_to_lean(a, nm) + " = "
                      + node_to_lean(b, nm) + ") → ";
            }
        }
        bool first = true;
        for (int lit : clause) {
            if (!first) body += " ∨ ";
            first = false;

            int var = (lit > 0) ? lit : -lit;
            auto eit = lit_to_atom.find(var);
            if (eit != lit_to_atom.end()) {
                const EqAtom& atom = eit->second;
                NodeId lhs_id = atom.lhs, rhs_id = atom.rhs;
                if (lhs_id == rhs_id) {
                    body += (lit > 0 ? "True" : "False");
                    continue;
                }
                // Replace ite nodes with their proxy constants so that
                // theory-clause atoms are opaque names — grind can then handle
                // them as pure EUF equalities without case-splitting the ite.
                {
                    auto pit = ite_proxy_for_.find(lhs_id);
                    if (pit != ite_proxy_for_.end()) lhs_id = pit->second;
                }
                {
                    auto pit = ite_proxy_for_.find(rhs_id);
                    if (pit != ite_proxy_for_.end()) rhs_id = pit->second;
                }
                if (lhs_id == rhs_id) {
                    body += (lit > 0 ? "True" : "False");
                    continue;
                }
                if (lhs_id > rhs_id) std::swap(lhs_id, rhs_id);
                std::string lhs_str = node_to_lean(lhs_id, nm);
                std::string rhs_str = node_to_lean(rhs_id, nm);
                // Normalize Bool-bridging sentinel equalities so theory-clause
                // atoms match the fml_to_lean Pred rendering used in hypotheses.
                // decide(True = p) → decide(p); decide(False = p) → ¬decide(p)
                // The literal sign then negates the whole thing as usual.
                bool sent_true  = (lhs_str == "True"  || rhs_str == "True");
                bool sent_false = (lhs_str == "False" || rhs_str == "False");
                const std::string& pred_str =
                    (lhs_str == "True" || lhs_str == "False") ? rhs_str : lhs_str;
                if (sent_true) {
                    body += (lit > 0) ? "decide (" + pred_str + ")"
                                      : "¬(decide (" + pred_str + "))";
                } else if (sent_false) {
                    body += (lit > 0) ? "¬(decide (" + pred_str + "))"
                                      : "decide (" + pred_str + ")";
                } else if (lit > 0) {
                    body += "decide (" + lhs_str + " = " + rhs_str + ")";
                } else {
                    body += "¬(decide (" + lhs_str + " = " + rhs_str + "))";
                }
            } else {
                auto nit = lit_to_node.find(var);
                if (nit != lit_to_node.end()) {
                    std::string node_str = node_to_lean(nit->second, nm);
                    if (lit > 0)
                        body += "decide (" + node_str + ")";
                    else
                        body += "¬(decide (" + node_str + "))";
                }
            }
        }
        // Collect hypotheses for positive equality literals that are direct
        // problem assertions.  Some theory clauses are valid only because a
        // positive literal is permanently asserted (e.g. decide(c3=c0) ∨ ¬…
        // is only a tautology when c3=c0 holds globally).  Load only the
        // specific needed hypotheses — do not load all hyps indiscriminately.
        std::vector<std::string> needed_hyps;
        {
            std::unordered_set<std::string> seen;
            for (int lit : clause) {
                if (lit <= 0) continue;  // only positive literals can be direct assertions
                auto eit = lit_to_atom.find(lit);
                if (eit == lit_to_atom.end()) continue;
                NodeId a = eit->second.lhs, b = eit->second.rhs;
                // Apply same proxy substitution used when building the body.
                { auto pit = ite_proxy_for_.find(a); if (pit != ite_proxy_for_.end()) a = pit->second; }
                { auto pit = ite_proxy_for_.find(b); if (pit != ite_proxy_for_.end()) b = pit->second; }
                if (a == b) continue;
                if (a > b) std::swap(a, b);
                uint64_t key = ((uint64_t)a << 32) | (uint64_t)b;
                auto hit = eq_atom_to_hyp.find(key);
                if (hit == eq_atom_to_hyp.end()) continue;
                if (seen.insert(hit->second).second)
                    needed_hyps.push_back(hit->second);
            }
        }
        out << "theorem " << tname << " : " << body << " := by";
        if (needed_hyps.empty()) {
            out << " grind\n";
        } else {
            out << "\n";
            for (const auto& h : needed_hyps)
                out << "  have " << h << " := " << h << "\n";
            out << "  grind\n";
        }
        standalone_names.push_back(tname);
    }

    // ── Contradiction theorem ──────────────────────────────────────────────
    // Load all hypothesis axioms and pre-proved theory theorems into the local
    // tactic context, then let bv_decide close the propositional contradiction.
    // All EUF reasoning has already been captured in the standalone theorems.
    out << "\ntheorem contradiction : False := by\n";
    for (const std::string& name : hyp_names)
        out << "  have " << name << " := " << name << "\n";
    for (const std::string& name : standalone_names)
        out << "  have " << name << " := " << name << "\n";
    out << "  bv_decide\n";
}

} // namespace llm2smt
