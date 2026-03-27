#include "proof/lean_emitter.h"

#include <algorithm>
#include <array>
#include <cctype>
#include <climits>
#include <cstdint>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "theories/euf/flattener.h"

namespace llm2smt {

// Canonical 64-bit key for an unordered pair of NodeIds (min << kNodeIdBits | max).
static constexpr int kNodeIdBits = sizeof(NodeId) * CHAR_BIT;
static uint64_t node_pair_key(NodeId a, NodeId b)
{
    if (a > b) std::swap(a, b);
    return (static_cast<uint64_t>(a) << kNodeIdBits) | static_cast<uint64_t>(b);
}

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
    return reserved.contains(s);
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
    bool plain = (std::isalpha(static_cast<unsigned char>(inner[0])) != 0) || inner[0] == '_';
    if (plain) {
        for (size_t i = 1; i < inner.size(); ++i) {
            char c = inner[i];
            if ((std::isalnum(static_cast<unsigned char>(c)) == 0) && c != '_') {
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
            // Fold constant conditions to avoid `if False then ... else e` in Lean
            // which bv_decide cannot reduce (it treats the ite as an opaque term).
            if (nm.is_false_node(info.cond)) return node_to_lean(info.else_node, nm);
            if (nm.is_true_node(info.cond))  return node_to_lean(info.then_node, nm);
            // Both branches identical: fold away the condition entirely.
            if (info.then_node == info.else_node) return node_to_lean(info.then_node, nm);
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
            NodeId fml = bit->second;
            if (nm.is_eq(fml)) {
                NodeId lhs = nm.get(fml).children[0], rhs = nm.get(fml).children[1];
                if (lhs == rhs) return "True";
                // mk_eq already canonicalized (min first)
                return "(" + node_to_lean(lhs, nm) + " = " + node_to_lean(rhs, nm) + ")";
            }
            if (nm.is_atom_node(fml))
                return node_to_lean(fml, nm);
            // Compound formulas: fml_to_lean returns Prop via Bool→Prop coercion.
            return "(" + fml_to_lean(fml, nm) + ")";
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
std::string LeanEmitter::fml_to_lean_cond(NodeId f, const NodeManager& nm) const
{
    if (nm.is_true_node(f))  return "True";
    if (nm.is_false_node(f)) return "False";
    if (nm.is_eq(f)) {
        NodeId lhs = nm.get(f).children[0], rhs = nm.get(f).children[1];
        if (lhs == rhs) return "True";
        // mk_eq already canonicalized (min first)
        return node_to_lean(lhs, nm) + " = " + node_to_lean(rhs, nm);
    }
    if (nm.is_atom_node(f))
        return node_to_lean(f, nm);
    if (nm.is_not(f)) {
        NodeId c = nm.get(f).children[0];
        if (nm.is_eq(c) && nm.get(c).children[0] == nm.get(c).children[1])
            return "False";
        return "¬(" + fml_to_lean_cond(c, nm) + ")";
    }
    if (nm.is_and(f)) {
        const auto& ch = nm.get(f).children;
        std::string r = fml_to_lean_cond(ch[0], nm);
        for (size_t i = 1; i < ch.size(); ++i)
            r = "(" + r + " ∧ " + fml_to_lean_cond(ch[i], nm) + ")";
        return r;
    }
    if (nm.is_or(f)) {
        const auto& ch = nm.get(f).children;
        std::string r = fml_to_lean_cond(ch[0], nm);
        for (size_t i = 1; i < ch.size(); ++i)
            r = "(" + r + " ∨ " + fml_to_lean_cond(ch[i], nm) + ")";
        return r;
    }
    if (nm.is_implies(f)) {
        NodeId c0 = nm.get(f).children[0], c1 = nm.get(f).children[1];
        return "(" + fml_to_lean_cond(c0, nm) + " → " + fml_to_lean_cond(c1, nm) + ")";
    }
    if (nm.is_xor(f)) {
        NodeId c0 = nm.get(f).children[0], c1 = nm.get(f).children[1];
        return "¬(" + fml_to_lean_cond(c0, nm) + " ↔ " + fml_to_lean_cond(c1, nm) + ")";
    }
    if (nm.is_iff(f)) {
        NodeId c0 = nm.get(f).children[0], c1 = nm.get(f).children[1];
        return "(" + fml_to_lean_cond(c0, nm) + " ↔ " + fml_to_lean_cond(c1, nm) + ")";
    }
    if (nm.is_ite_bool(f)) {
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        NodeId c2 = nm.get(f).children[2];
        const std::string c = fml_to_lean_cond(c0, nm);
        const std::string t = fml_to_lean_cond(c1, nm);
        const std::string e = fml_to_lean_cond(c2, nm);
        return "((" + c + " → " + t + ") ∧ (¬(" + c + ") → " + e + "))";
    }
    return "True";  // unreachable
}

std::string LeanEmitter::fml_to_lean(NodeId f, const NodeManager& nm) const
{
    if (nm.is_true_node(f))  return "True";
    if (nm.is_false_node(f)) return "False";
    if (nm.is_eq(f)) {
        NodeId lhs = nm.get(f).children[0], rhs = nm.get(f).children[1];
        // a = a is always true; emit "True" so bv_decide doesn't treat it as
        // an opaque atom that it could assign false (reflexivity is not built in).
        if (lhs == rhs) return "True";
        // mk_eq already canonicalized (min first)
        std::string lhs_str = node_to_lean(lhs, nm);
        std::string rhs_str = node_to_lean(rhs, nm);
        // After ITE constant folding two nodes may render identically (e.g.
        // eq(c3, ite(False,c0,c3)) renders as "c3 = c3").  Treat as True.
        if (lhs_str == rhs_str) return "True";
        return "decide (" + lhs_str + " = " + rhs_str + ")";
    }
    if (nm.is_atom_node(f))
        return "decide (" + node_to_lean(f, nm) + ")";
    if (nm.is_not(f)) {
        NodeId c = nm.get(f).children[0];
        // ¬(a = a) is always false; emit "False" so bv_decide can't satisfy it.
        if (nm.is_eq(c) && nm.get(c).children[0] == nm.get(c).children[1])
            return "False";
        std::string inner = fml_to_lean(c, nm);
        // Fold ¬True → False and ¬False → True so bv_decide sees canonical atoms.
        if (inner == "True")  return "False";
        if (inner == "False") return "True";
        return "¬(" + inner + ")";
    }
    if (nm.is_and(f)) {
        const auto& ch = nm.get(f).children;
        std::string r = fml_to_lean(ch[0], nm);
        for (size_t i = 1; i < ch.size(); ++i)
            r = "(" + r + " ∧ " + fml_to_lean(ch[i], nm) + ")";
        return r;
    }
    if (nm.is_or(f)) {
        const auto& ch = nm.get(f).children;
        std::string r = fml_to_lean(ch[0], nm);
        for (size_t i = 1; i < ch.size(); ++i)
            r = "(" + r + " ∨ " + fml_to_lean(ch[i], nm) + ")";
        return r;
    }
    if (nm.is_implies(f)) {
        NodeId c0 = nm.get(f).children[0], c1 = nm.get(f).children[1];
        return "(" + fml_to_lean(c0, nm) + " → " + fml_to_lean(c1, nm) + ")";
    }
    if (nm.is_xor(f)) {
        NodeId c0 = nm.get(f).children[0], c1 = nm.get(f).children[1];
        // xor(a,b) ≡ ¬(a ↔ b)  — avoids non-standard Xor identifier
        return "¬(" + fml_to_lean(c0, nm) + " ↔ " + fml_to_lean(c1, nm) + ")";
    }
    if (nm.is_iff(f)) {
        NodeId c0 = nm.get(f).children[0], c1 = nm.get(f).children[1];
        return "(" + fml_to_lean(c0, nm) + " ↔ " + fml_to_lean(c1, nm) + ")";
    }
    if (nm.is_ite_bool(f)) {
        NodeId c0 = nm.get(f).children[0];
        NodeId c1 = nm.get(f).children[1];
        NodeId c2 = nm.get(f).children[2];
        // ite(c,t,e) ≡ (c → t) ∧ (¬c → e)  — avoids `if` which requires Decidable c.
        const std::string c = fml_to_lean(c0, nm);
        const std::string t = fml_to_lean(c1, nm);
        const std::string e = fml_to_lean(c2, nm);
        return "((" + c + " → " + t + ") ∧ (¬(" + c + ") → " + e + "))";
    }
    return "True";  // unreachable
}

std::string LeanEmitter::fn_type(const FnDecl& fn, bool is_pred)
{
    std::string result;
    for (const std::string& ps : fn.param_sorts)
        result += sort_to_lean_type(ps) + " → ";
    result += is_pred ? "Prop" : sort_to_lean_type(fn.return_sort);
    return result;
}

void LeanEmitter::emit(std::ostream& out,
                       const SmtContext& ctx,
                       const std::vector<NodeId>& proof_fmls,
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
        NodeId f = proof_fmls[i];
        if (!nm.is_eq(f)) continue;
        NodeId a = nm.get(f).children[0], b = nm.get(f).children[1];
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

    out << "import Mathlib.Tactic\n";
    out << "set_option maxRecDepth 10000\n";
    out << "set_option maxHeartbeats 4000000\n";
    out << "set_option linter.unusedVariables false\n";
    out << "set_option linter.unusedSimpArgs false\n\n";
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
            || fname.starts_with("__ite_"))
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
        NodeId f = proof_fmls[i];
        if (!nm.is_eq(f)) continue;
        NodeId a = nm.get(f).children[0], b = nm.get(f).children[1];
        if (a == b) continue;
        uint64_t key = node_pair_key(a, b);
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
        for (NodeId f : proof_fmls) {
            if (!nm.is_eq(f)) continue;
            NodeId a = nm.get(f).children[0], b = nm.get(f).children[1];
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
            std::string concl = "decide (" + node_to_lean(pa, nm) + " = " + node_to_lean(pb, nm) + ")";
            NodeId src_fml = bridge_info.second;
            // Collect Or leaves from the binary Or tree.
            std::vector<NodeId> disjuncts;
            {
                std::vector<NodeId> stk = {src_fml};
                while (!stk.empty()) {
                    NodeId n = stk.back(); stk.pop_back();
                    if (nm.is_or(n)) {
                        NodeId c0 = nm.get(n).children[0], c1 = nm.get(n).children[1];
                        stk.push_back(c1);
                        stk.push_back(c0);
                    } else {
                        disjuncts.push_back(n);
                    }
                }
            }
            for (NodeId disj : disjuncts) {
                // Collect And leaves from the binary And tree.
                std::vector<NodeId> conjuncts;
                {
                    std::vector<NodeId> stk = {disj};
                    while (!stk.empty()) {
                        NodeId n = stk.back(); stk.pop_back();
                        if (nm.is_and(n)) {
                            NodeId c0 = nm.get(n).children[0], c1 = nm.get(n).children[1];
                            stk.push_back(c1);
                            stk.push_back(c0);
                        } else {
                            conjuncts.push_back(n);
                        }
                    }
                }
                std::string tname = "eq_bridge_" + std::to_string(ebr_idx++);
                out << "theorem " << tname << " : ";
                for (NodeId atom : conjuncts)
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
        // Determine which hypotheses this theory clause needs.
        //
        // Theory clauses fall into two categories:
        //   1. Direct-assertion clauses: a positive literal is an equality that
        //      is explicitly asserted in the problem.  Only that specific hyp is
        //      needed (e.g. "decide(c3=c0) ∨ ¬(decide(c1=c0))" needs hyp3).
        //   2. Closure-derived clauses: a positive literal is derivable from the
        //      conjunction of problem hypotheses via EUF closure, but is NOT
        //      directly asserted (e.g. "decide(c_2=f1 c_2 c_2) ∨ …" in SEQ
        //      problems is derived from the problem's equational axiom set).
        //      Grind needs ALL hypotheses in scope to derive it.
        //
        // Heuristic: scan positive equality atoms.  If every non-trivial one is
        // found in eq_atom_to_hyp, load only those specific hypotheses.  If any
        // non-trivial positive atom is NOT directly asserted, load all hyps.
        std::vector<std::string> needed_hyps;
        {
            std::unordered_set<std::string> seen;
            for (int lit : clause) {
                if (lit <= 0) continue;  // only positive literals
                auto eit = lit_to_atom.find(lit);
                if (eit == lit_to_atom.end()) continue;
                NodeId a = eit->second.lhs, b = eit->second.rhs;
                // Apply same proxy substitution used when building the body.
                { auto pit = ite_proxy_for_.find(a); if (pit != ite_proxy_for_.end()) a = pit->second; }
                { auto pit = ite_proxy_for_.find(b); if (pit != ite_proxy_for_.end()) b = pit->second; }
                if (a == b) continue;  // trivial (True) — no hyp needed
                uint64_t key = node_pair_key(a, b);
                auto hit = eq_atom_to_hyp.find(key);
                if (hit == eq_atom_to_hyp.end()) {
                    // Positive atom not directly asserted → EUF-derived. The clause body
                    // is self-contained; plain grind handles it without extra hypotheses.
                    needed_hyps.clear();
                    break;
                }
                if (seen.insert(hit->second).second)
                    needed_hyps.push_back(hit->second);
            }
        }
        // Empty needed_hyps → plain grind (either all atoms matched or one was EUF-derived).
        if (needed_hyps.empty()) {
            out << "theorem " << tname << " : " << body << " := by grind\n";
        } else {
            // Specific hyp(s) matched: load only those.
            out << "theorem " << tname << " : " << body << " := by\n";
            for (const auto& h : needed_hyps)
                out << "  have " << h << " := " << h << "\n";
            out << "  grind\n";
        }
        standalone_names.push_back(tname);
    }

    // ── Transitivity completeness lemmas ──────────────────────────────────
    // For every pair of registered atoms (A=X, B=X) sharing a common
    // effective term X, if decide(A=B) is also a registered atom, emit:
    //   theorem trans_N : decide(A=B) ∨ ¬decide(A=X) ∨ ¬decide(B=X) := by grind
    // These pure EUF tautologies give bv_decide the propositional backbone to
    // close the contradiction (the conflict clauses alone may have premises that
    // are SAT-decision atoms, so bv_decide needs these simpler lemmas to chain).
    {
        // Effective node ID after ite-proxy substitution.
        auto eff = [&](NodeId n) -> NodeId {
            auto it = ite_proxy_for_.find(n);
            return it != ite_proxy_for_.end() ? it->second : n;
        };
        // Canonical key for an unordered pair of already-effective node IDs.
        auto pair_key = node_pair_key;

        // Returns true if node n is a Bool-bridging sentinel (True/False).
        // Sentinel atoms use a different rendering in theory clauses
        // (decide((h a)) not decide((h a)=True)), so skip them to avoid
        // emitting transitivity lemmas with mismatched atom forms.
        auto is_bool_sent = [&](NodeId n) -> bool {
            const std::string s = node_to_lean(n, nm);
            return s == "True" || s == "False";
        };

        // Map effective-pair key → positive literal.
        std::unordered_map<uint64_t, int> eff_to_lit;
        for (const auto& [lit, atom] : lit_to_atom) {
            if (lit <= 0) continue;
            NodeId ea = eff(atom.lhs), eb = eff(atom.rhs);
            if (ea == eb) continue;
            if (is_bool_sent(ea) || is_bool_sent(eb)) continue;
            eff_to_lit[pair_key(ea, eb)] = lit;
        }

        // Map effective term → list of (other_eff_term, literal).
        std::unordered_map<NodeId, std::vector<std::pair<NodeId, int>>> by_term;
        for (const auto& [lit, atom] : lit_to_atom) {
            if (lit <= 0) continue;
            NodeId ea = eff(atom.lhs), eb = eff(atom.rhs);
            if (ea == eb) continue;
            if (is_bool_sent(ea) || is_bool_sent(eb)) continue;
            by_term[ea].emplace_back(eb, lit);
            by_term[eb].emplace_back(ea, lit);
        }

        // Emit one trans_N per unique (litAB, min(litAX,litBX), max(litAX,litBX)) triple.
        std::set<std::array<int, 3>> seen_trans;
        int trans_idx = 0;
        for (const auto& [X, eps] : by_term) {
            for (size_t i = 0; i < eps.size(); ++i) {
                auto [A, litAX] = eps[i];
                for (size_t j = i + 1; j < eps.size(); ++j) {
                    auto [B, litBX] = eps[j];
                    if (A == B) continue;
                    auto it = eff_to_lit.find(pair_key(A, B));
                    if (it == eff_to_lit.end()) continue;
                    int litAB = it->second;
                    std::array<int, 3> key = {
                        litAB,
                        std::min(litAX, litBX),
                        std::max(litAX, litBX)};
                    if (!seen_trans.insert(key).second) continue;

                    // Emit each atom with the smaller NodeId first so that
                    // all decide(P = Q) expressions use the same canonical
                    // form as theory-clause atoms.  Without this, bv_decide
                    // treats decide(a = b) and decide(b = a) as distinct
                    // opaque Bool variables and cannot close the goal.
                    auto atom_str = [&](NodeId P, NodeId Q) {
                        if (P > Q) std::swap(P, Q);
                        return "decide (" + node_to_lean(P, nm) +
                               " = " + node_to_lean(Q, nm) + ")";
                    };
                    std::string tname = "trans_" + std::to_string(trans_idx++);
                    out << "theorem " << tname << " : "
                        << atom_str(A, B) << " ∨ "
                        << "¬(" << atom_str(A, X) << ") ∨ "
                        << "¬(" << atom_str(B, X) << ") := by grind\n";
                    standalone_names.push_back(tname);
                }
            }
        }
    }

    // ── Congruence lemmas ──────────────────────────────────────────────────
    // For every congruence step recorded during CDCL proof tracing, emit a
    // standalone theorem that grind can prove.  Each step says:
    //   decide(orig(r1) = orig(r2)) ∨ ¬decide(P1) ∨ ¬decide(P2) ∨ ...
    // The r1/r2 pair is a fully-applied original term (not a partial app).
    // bv_decide uses these as propositional clauses bridging complex function
    // atoms to the simple registered SAT atoms.
    {
        const Flattener& flattener = ctx.euf.flattener();
        const auto& cong_steps = ctx.euf.proof_cong_steps();
        int cong_idx = 0;
        for (const auto& cs : cong_steps) {
            NodeId orig_r1 = flattener.get_orig(cs.result_lhs);
            NodeId orig_r2 = flattener.get_orig(cs.result_rhs);
            // Skip partial-application flat nodes (no full-term inverse).
            if (orig_r1 == NULL_NODE || orig_r2 == NULL_NODE) continue;
            if (orig_r1 == orig_r2) continue;
            // Canonical order (smaller NodeId first).
            if (orig_r1 > orig_r2) std::swap(orig_r1, orig_r2);
            std::string body = "decide (" + node_to_lean(orig_r1, nm) +
                               " = " + node_to_lean(orig_r2, nm) + ")";
            for (int prem_lit : cs.premise_lits) {
                auto eit = lit_to_atom.find(prem_lit);
                if (eit == lit_to_atom.end()) continue;
                NodeId lhs = eit->second.lhs, rhs = eit->second.rhs;
                if (lhs > rhs) std::swap(lhs, rhs);
                body += " ∨ ¬(decide (" + node_to_lean(lhs, nm) +
                        " = " + node_to_lean(rhs, nm) + "))";
            }
            std::string tname = "cong_" + std::to_string(cong_idx++);
            out << "theorem " << tname << " : " << body << " := by grind\n";
            standalone_names.push_back(tname);
        }
    }

    // ── Contradiction theorem ──────────────────────────────────────────────
    // Load all hypothesis axioms and pre-proved theory theorems into the local
    // tactic context, then bv_decide closes the propositional contradiction.
    // All EUF reasoning is captured in the standalone theorems above.
    out << "\ntheorem contradiction : False := by\n";
    for (const std::string& name : hyp_names)
        out << "  have " << name << " := " << name << "\n";
    for (const std::string& name : standalone_names)
        out << "  have " << name << " := " << name << "\n";
    out << "  bv_decide\n";
}

} // namespace llm2smt
