#include "proof/lean_emitter.h"

#include <algorithm>
#include <cctype>
#include <map>
#include <string>
#include <unordered_map>
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
        // Canonical order by NodeId so that a=b and b=a produce the same
        // string — sat_decide must not see them as distinct opaque atoms.
        NodeId lhs = f->eq_lhs, rhs = f->eq_rhs;
        if (lhs > rhs) std::swap(lhs, rhs);
        return node_to_lean(lhs, nm) + " = " + node_to_lean(rhs, nm);
    }
    case FmlKind::Pred:
        return node_to_lean(f->pred, nm);
    case FmlKind::Not:
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
                       const std::vector<std::vector<int>>& proof_conflicts,
                       const std::string& lean_project)
{
    const NodeManager& nm = ctx.nm;

    if (lean_project.empty())
        out << "import Mathlib.Tactic\n\nexample\n";
    else
        out << "import " << lean_project << ".ConvertProp\n\nexample\n";

    // ── Sorts ──────────────────────────────────────────────────────────────
    std::vector<std::string> sort_names;
    sort_names.reserve(ctx.declared_sorts.size());
    for (const auto& [name, arity] : ctx.declared_sorts)
        sort_names.push_back(name);
    std::sort(sort_names.begin(), sort_names.end());

    for (const std::string& sname : sort_names) {
        std::string lname = lean_ident(sname);
        out << "    (" << lname << " : Type)\n";
    }

    // ── Categorise declared functions ──────────────────────────────────────
    // 0-ary U-sorted constants grouped by return sort (preserving decl order within group)
    std::map<std::string, std::vector<std::string>> constants_by_sort;
    std::vector<const FnDecl*> nary_u;       // n-ary, non-Bool
    std::vector<const FnDecl*> zerory_bool;  // 0-ary, Bool
    std::vector<const FnDecl*> nary_bool;    // n-ary, Bool

    for (const FnDecl& decl : ctx.declared_fn_order) {
        const std::string& fname = nm.symbol_table().get(decl.sym).name;
        // Skip internal symbols (e.g., __bool_true, __bool_false)
        if (!fname.empty() && fname[0] == '_' && fname.size() > 1 && fname[1] == '_')
            continue;
        bool is_bool    = (decl.return_sort == "Bool");
        bool is_zerory  = decl.param_sorts.empty();

        if (!is_bool && is_zerory)
            constants_by_sort[decl.return_sort].push_back(lean_ident(fname));
        else if (!is_bool && !is_zerory)
            nary_u.push_back(&decl);
        else if (is_bool && is_zerory)
            zerory_bool.push_back(&decl);
        else
            nary_bool.push_back(&decl);
    }

    // 0-ary U-sorted constants (one line per sort, space-separated names)
    for (const auto& [sort, names] : constants_by_sort) {
        out << "    (";
        for (size_t i = 0; i < names.size(); ++i) {
            if (i > 0) out << " ";
            out << names[i];
        }
        out << " : " << lean_ident(sort) << ")\n";
    }

    // n-ary U-sorted functions
    for (const FnDecl* decl : nary_u) {
        const std::string& fname = nm.symbol_table().get(decl->sym).name;
        out << "    (" << lean_ident(fname) << " : " << fn_type(*decl, false) << ")\n";
    }

    // 0-ary Bool (propositional constants)
    for (const FnDecl* decl : zerory_bool) {
        const std::string& fname = nm.symbol_table().get(decl->sym).name;
        out << "    (" << lean_ident(fname) << " : Prop)\n";
    }

    // n-ary Bool predicates
    for (const FnDecl* decl : nary_bool) {
        const std::string& fname = nm.symbol_table().get(decl->sym).name;
        out << "    (" << lean_ident(fname) << " : " << fn_type(*decl, true) << ")\n";
    }

    // ── Assertions ─────────────────────────────────────────────────────────
    for (size_t i = 0; i < proof_fmls.size(); ++i)
        out << "    (hyp" << (i + 1) << " : " << fml_to_lean(proof_fmls[i], nm) << ")\n";

    out << "    : False := by\n";

    // ── Build reverse map: SAT literal → NodeId (for Bool-sorted nodes) ───
    std::unordered_map<int, NodeId> lit_to_node;
    lit_to_node.reserve(ctx.node_to_lit.size());
    for (const auto& [nid, lit] : ctx.node_to_lit)
        lit_to_node[lit] = nid;

    // ── Theory lemmas ──────────────────────────────────────────────────────
    const auto& lit_to_atom = ctx.euf.lit_to_atom();
    for (size_t i = 0; i < proof_conflicts.size(); ++i) {
        const auto& clause = proof_conflicts[i];
        out << "  have cl_" << i << " : ";
        bool first = true;
        for (int lit : clause) {
            if (!first) out << " ∨ ";
            first = false;

            int var = (lit > 0) ? lit : -lit;
            auto eit = lit_to_atom.find(var);
            if (eit != lit_to_atom.end()) {
                const EqAtom& atom = eit->second;
                // Same canonical order as fml_to_lean(FmlKind::Eq, ...)
                NodeId lhs_id = atom.lhs, rhs_id = atom.rhs;
                if (lhs_id > rhs_id) std::swap(lhs_id, rhs_id);
                std::string lhs_str = node_to_lean(lhs_id, nm);
                std::string rhs_str = node_to_lean(rhs_id, nm);
                if (lit > 0)
                    out << lhs_str << " = " << rhs_str;
                else
                    out << "¬(" << lhs_str << " = " << rhs_str << ")";
            } else {
                auto nit = lit_to_node.find(var);
                if (nit != lit_to_node.end()) {
                    std::string node_str = node_to_lean(nit->second, nm);
                    if (lit > 0)
                        out << node_str;
                    else
                        out << "¬(" << node_str << ")";
                }
            }
        }
        out << " := by grind\n";
    }

    out << "  sat_decide\n";
}

} // namespace llm2smt
