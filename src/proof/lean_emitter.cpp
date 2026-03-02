#include "proof/lean_emitter.h"

#include <algorithm>
#include <cctype>
#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace llm2smt {

// ============================================================================
// Helpers
// ============================================================================

// Convert an SMT-LIB symbol name to a valid Lean identifier.
// Strips |...| quoting.  If the resulting string is a valid plain Lean
// identifier (letter/underscore start, then alphanumeric/underscore), it is
// returned as-is.  Otherwise it is wrapped in «» so that any characters
// (hyphens, '?', spaces, etc.) are accepted by Lean.
static std::string lean_ident(const std::string& name)
{
    std::string inner = name;
    // Strip | | quoting if present
    if (inner.size() >= 2 && inner.front() == '|' && inner.back() == '|')
        inner = inner.substr(1, inner.size() - 2);

    if (inner.empty()) return "x";

    // Check whether the name is already a valid plain Lean identifier.
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

    // Plain identifiers are used as-is; everything else is wrapped in «».
    if (!plain)
        return "«" + inner + "»";
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
            return "(if " + fml_to_lean(info.cond, nm)
                   + " then " + node_to_lean(info.then_node, nm)
                   + " else " + node_to_lean(info.else_node, nm) + ")";
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
    const NodeManager& nm = ctx.nm;

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
    std::vector<std::string> theorem_names;
    for (size_t i = 0; i < proof_fmls.size(); ++i) {
        std::string hname = "hyp" + std::to_string(i + 1);
        out << "axiom " << hname << " : " << fml_to_lean(proof_fmls[i], nm) << "\n";
        theorem_names.push_back(hname);
    }

    out << "\n";

    // ── Build reverse map: SAT literal → NodeId (for Bool-sorted nodes) ───
    std::unordered_map<int, NodeId> lit_to_node;
    lit_to_node.reserve(ctx.node_to_lit.size());
    for (const auto& [nid, lit] : ctx.node_to_lit)
        lit_to_node[lit] = nid;

    const auto& lit_to_atom = ctx.euf.lit_to_atom();

    // ── Ite semantic clauses ────────────────────────────────────────────────
    // For each U-sorted ite node, add two clauses that encode its semantics:
    //   ¬cond ∨ decide(ite = then)   (if cond holds, ite result equals the then-branch)
    //   cond ∨ decide(ite = else)    (if cond fails, ite result equals the else-branch)
    // These clauses are provable by grind via if_pos/if_neg.
    size_t ite_clause_idx = 0;
    for (const auto& [ite_id, info] : ctx.ite_nodes) {
        const std::string cond_lean = fml_to_lean(info.cond, nm);

        // then-branch clause: ¬cond ∨ decide(canon(ite, then))
        {
            NodeId lhs_id = ite_id, rhs_id = info.then_node;
            if (lhs_id > rhs_id) std::swap(lhs_id, rhs_id);
            std::string tname = "ite_pos_" + std::to_string(ite_clause_idx);
            out << "theorem " << tname << " : ¬(" << cond_lean << ") ∨ decide ("
                << node_to_lean(lhs_id, nm) << " = " << node_to_lean(rhs_id, nm)
                << ") := by grind\n";
            theorem_names.push_back(tname);
        }
        // else-branch clause: cond ∨ decide(canon(ite, else))
        {
            NodeId lhs_id = ite_id, rhs_id = info.else_node;
            if (lhs_id > rhs_id) std::swap(lhs_id, rhs_id);
            std::string tname = "ite_neg_" + std::to_string(ite_clause_idx);
            out << "theorem " << tname << " : (" << cond_lean << ") ∨ decide ("
                << node_to_lean(lhs_id, nm) << " = " << node_to_lean(rhs_id, nm)
                << ") := by grind\n";
            theorem_names.push_back(tname);
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

            // Sides that are NOT shortcuts: then-branch, else-branch, proxies.
            std::unordered_set<NodeId> non_shortcut;
            non_shortcut.insert(info.then_node);
            non_shortcut.insert(info.else_node);
            for (NodeId p : proxies) non_shortcut.insert(p);

            for (const auto& [var, atom] : lit_to_atom) {
                NodeId a = atom.lhs, b = atom.rhs;
                if (a != ite_id && b != ite_id) continue;
                NodeId other = (a == ite_id) ? b : a;
                if (non_shortcut.count(other)) continue;   // not a shortcut
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

                    std::string tname = "ite_bridge_" + std::to_string(bridge_idx++);
                    out << "theorem " << tname << " : " << ite_eq_other
                        << " ∨ ¬(" << proxy_eq_other << ") := by grind\n";
                    theorem_names.push_back(tname);
                }
            }
        }
    }

    // ── Permanent-equality bridge lemmas ───────────────────────────────────
    // When preprocessing establishes a permanent equality (pa = pb), theory-clause
    // atoms may refer to one representative while proof hypotheses only mention the
    // other.  bv_decide treats pa=Z and pb=Z as independent opaque atoms and cannot
    // derive one from the other by EUF transitivity.
    //
    // For each permanent pair and each SAT atom touching either endpoint, emit:
    //   decide(pa = Z) ∨ ¬(decide(pb = Z)) ∨ ¬(decide(pb = pa))  := by grind
    {
        std::set<std::tuple<NodeId,NodeId,NodeId,NodeId,NodeId,NodeId>> seen;

        size_t pbr_idx = 0;
        for (const auto& [pa, pb] : ctx.euf.permanent_equalities()) {
            for (const auto& [var, atom] : lit_to_atom) {
                for (int side = 0; side < 2; ++side) {
                    NodeId pivot = (side == 0) ? pa : pb;
                    NodeId other = (side == 0) ? pb : pa;
                    NodeId a = atom.lhs, b = atom.rhs;
                    NodeId Z;
                    if      (a == pivot) Z = b;
                    else if (b == pivot) Z = a;
                    else continue;
                    if (Z == other) continue;  // the pair itself — not needed

                    // Bridge: other = Z  ∨  ¬(pivot = Z)  ∨  ¬(pivot = other)
                    NodeId l1 = other, r1 = Z;      if (l1 > r1) std::swap(l1, r1);
                    NodeId l2 = pivot, r2 = Z;      if (l2 > r2) std::swap(l2, r2);
                    NodeId l3 = pivot, r3 = other;  if (l3 > r3) std::swap(l3, r3);

                    auto key = std::make_tuple(l1, r1, l2, r2, l3, r3);
                    if (!seen.insert(key).second) continue;

                    std::string tname = "perm_bridge_" + std::to_string(pbr_idx++);
                    out << "theorem " << tname << " : "
                        << "decide (" << node_to_lean(l1, nm) << " = " << node_to_lean(r1, nm) << ")"
                        << " ∨ ¬(decide (" << node_to_lean(l2, nm) << " = " << node_to_lean(r2, nm) << "))"
                        << " ∨ ¬(decide (" << node_to_lean(l3, nm) << " = " << node_to_lean(r3, nm) << "))"
                        << " := by grind\n";
                    theorem_names.push_back(tname);
                }
            }
        }
    }

    // ── Theory lemmas ──────────────────────────────────────────────────────
    // For each theory lemma we also store how to apply it in the contradiction
    // theorem.  Most theorems use the trivial "have NAME := NAME" form, but
    // eq-bridge unit clauses are stated as implications SOURCE_OR → decide(...)
    // and must be applied: have NAME : decide(...) := NAME (by have hyp_j := hyp_j; grind)
    std::vector<std::string> contradiction_applications;  // parallel to theorem_names

    // Seed with axiom applications already in theorem_names (hyps).
    for (const auto& name : theorem_names)
        contradiction_applications.push_back("");  // trivial form

    for (size_t i = 0; i < proof_conflicts.size(); ++i) {
        const auto& clause = proof_conflicts[i];
        std::string tname = "cl_" + std::to_string(i);

        // Check whether this is an eq-bridge unit clause with a known source Or.
        // If so, emit as implication form: SOURCE_OR → decide (lhs = rhs) := by grind
        if (clause.size() == 1) {
            int lit = clause[0];
            int var = (lit > 0) ? lit : -lit;
            if (lit > 0) {
                auto eit = lit_to_atom.find(var);
                if (eit != lit_to_atom.end()) {
                    NodeId lhs_id = eit->second.lhs, rhs_id = eit->second.rhs;
                    NodeId canon_lhs = lhs_id, canon_rhs = rhs_id;
                    if (canon_lhs > canon_rhs) std::swap(canon_lhs, canon_rhs);
                    auto src_it = ctx.eq_bridge_sources.find({canon_lhs, canon_rhs});
                    if (src_it != ctx.eq_bridge_sources.end()) {
                        size_t hyp_idx = src_it->second.first + 1;  // 1-based
                        FmlRef source_or = src_it->second.second;
                        std::string src_str = fml_to_lean(source_or, nm);
                        std::string lhs_str = node_to_lean(canon_lhs, nm);
                        std::string rhs_str = node_to_lean(canon_rhs, nm);
                        std::string concl = "decide (" + lhs_str + " = " + rhs_str + ")";

                        // Theorem: SOURCE_OR → decide (lhs = rhs)
                        // This is a pure EUF tautology; grind proves it standalone.
                        out << "theorem " << tname << " : " << src_str
                            << " → " << concl << " := by grind\n";
                        theorem_names.push_back(tname);

                        // In contradiction: apply the implication to hyp_j
                        std::string app = "have " + tname + " : " + concl
                            + " := " + tname
                            + " (by have hyp" + std::to_string(hyp_idx)
                            + " := hyp" + std::to_string(hyp_idx) + "; grind)";
                        contradiction_applications.push_back(app);
                        continue;
                    }
                }
            }
        }

        // Normal clause emission.
        out << "theorem " << tname << " : ";
        bool first = true;
        for (int lit : clause) {
            if (!first) out << " ∨ ";
            first = false;

            int var = (lit > 0) ? lit : -lit;
            auto eit = lit_to_atom.find(var);
            if (eit != lit_to_atom.end()) {
                const EqAtom& atom = eit->second;
                NodeId lhs_id = atom.lhs, rhs_id = atom.rhs;
                // Reflexivity: emit propositionally-correct constant.
                if (lhs_id == rhs_id) {
                    out << (lit > 0 ? "True" : "False");
                    continue;
                }
                if (lhs_id > rhs_id) std::swap(lhs_id, rhs_id);
                std::string lhs_str = node_to_lean(lhs_id, nm);
                std::string rhs_str = node_to_lean(rhs_id, nm);
                if (lit > 0)
                    out << "decide (" << lhs_str << " = " << rhs_str << ")";
                else
                    out << "¬(decide (" << lhs_str << " = " << rhs_str << "))";
            } else {
                auto nit = lit_to_node.find(var);
                if (nit != lit_to_node.end()) {
                    std::string node_str = node_to_lean(nit->second, nm);
                    if (lit > 0)
                        out << "decide (" << node_str << ")";
                    else
                        out << "¬(decide (" << node_str << "))";
                }
            }
        }
        // Non-bridge unit clauses (e.g. from preproc forced equalities) are not
        // universal EUF tautologies; include all hypotheses so grind can derive them.
        const bool is_unit = (clause.size() == 1) && !proof_fmls.empty();
        if (!is_unit) {
            out << " := by grind\n";
        } else {
            out << " := by\n";
            for (size_t j = 0; j < proof_fmls.size(); ++j)
                out << "  have hyp" << (j + 1) << " := hyp" << (j + 1) << "\n";
            out << "  grind\n";
        }
        theorem_names.push_back(tname);
        contradiction_applications.push_back("");  // trivial form
    }

    // ── Contradiction theorem ──────────────────────────────────────────────
    out << "\ntheorem contradiction : False := by\n";
    for (size_t i = 0; i < theorem_names.size(); ++i) {
        const std::string& name = theorem_names[i];
        const std::string& app  = contradiction_applications[i];
        if (app.empty())
            out << "  have " << name << " := " << name << "\n";
        else
            out << "  " << app << "\n";
    }
    out << "  bv_decide\n";
}

} // namespace llm2smt
