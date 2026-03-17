#include "preprocessor/simplifier.h"

#include <cassert>
#include <span>

namespace llm2smt {

Simplifier::Simplifier(NodeManager& nm) : nm_(nm) {}

// ============================================================================
// Constant folding + optional And/Or flattening
// ============================================================================

NodeId Simplifier::fold(NodeId root)
{
    // Check memoization cache — fold() is pure so result is stable.
    if (auto it = fold_cache_.find(root); it != fold_cache_.end())
        return it->second;

    // fold_one: compute fold_cache_[f] for a single node, given that all
    // children of f in the ORIGINAL subtree are already in fold_cache_.
    // AND/OR work-lists may call fold() on fold-result nodes (not original
    // subtree nodes); those calls are at most 1–2 C++ levels deep.
    auto fold_one = [&](NodeId f) {
        if (nm_.is_true_node(f) || nm_.is_false_node(f)) {
            fold_cache_[f] = f; return;
        }
        if (nm_.is_eq(f) || is_atom(f)) {
            fold_cache_[f] = f; return;
        }

        if (nm_.is_not(f)) {
            NodeId child = nm_.get(f).children[0];
            NodeId fc    = fold(child);
            if (nm_.is_true_node(fc))  { fold_cache_[f] = nm_.mk_false(); return; }
            if (nm_.is_false_node(fc)) { fold_cache_[f] = nm_.mk_true();  return; }
            if (nm_.is_not(fc))        { fold_cache_[f] = nm_.get(fc).children[0]; return; }
            fold_cache_[f] = (fc == child) ? f : nm_.mk_not(fc);
            return;
        }

        if (nm_.is_and(f)) {
            NodeId c0 = nm_.get(f).children[0];
            NodeId c1 = nm_.get(f).children[1];

            std::vector<NodeId> leaves;
            bool found_false = false;
            std::vector<NodeId> work;
            work.push_back(c1);
            work.push_back(c0);

            while (!work.empty() && !found_false) {
                NodeId n  = work.back(); work.pop_back();
                NodeId fn = fold(n);
                if (nm_.is_false_node(fn)) { found_false = true; break; }
                if (nm_.is_true_node(fn))  continue;
                if (flatten_ && nm_.is_and(fn)) {
                    NodeId fa = nm_.get(fn).children[0];
                    NodeId fb = nm_.get(fn).children[1];
                    work.push_back(fb);
                    work.push_back(fa);
                } else {
                    leaves.push_back(fn);
                }
            }

            if (found_false)         { fold_cache_[f] = nm_.mk_false(); return; }
            if (leaves.empty())      { fold_cache_[f] = nm_.mk_true();  return; }
            if (leaves.size() == 1)  { fold_cache_[f] = leaves[0];     return; }
            if (leaves.size() == 2 && leaves[0] == c0 && leaves[1] == c1) {
                fold_cache_[f] = f; return;
            }
            NodeId result = nm_.mk_and(leaves[0], leaves[1]);
            for (size_t i = 2; i < leaves.size(); ++i)
                result = nm_.mk_and(result, leaves[i]);
            fold_cache_[f] = result;
            return;
        }

        if (nm_.is_or(f)) {
            NodeId c0 = nm_.get(f).children[0];
            NodeId c1 = nm_.get(f).children[1];

            std::vector<NodeId> leaves;
            bool found_true = false;
            std::vector<NodeId> work;
            work.push_back(c1);
            work.push_back(c0);

            while (!work.empty() && !found_true) {
                NodeId n  = work.back(); work.pop_back();
                NodeId fn = fold(n);
                if (nm_.is_true_node(fn))  { found_true = true; break; }
                if (nm_.is_false_node(fn)) continue;
                if (flatten_ && nm_.is_or(fn)) {
                    NodeId fa = nm_.get(fn).children[0];
                    NodeId fb = nm_.get(fn).children[1];
                    work.push_back(fb);
                    work.push_back(fa);
                } else {
                    leaves.push_back(fn);
                }
            }

            if (found_true)          { fold_cache_[f] = nm_.mk_true();  return; }
            if (leaves.empty())      { fold_cache_[f] = nm_.mk_false(); return; }
            if (leaves.size() == 1)  { fold_cache_[f] = leaves[0];     return; }
            if (leaves.size() == 2 && leaves[0] == c0 && leaves[1] == c1) {
                fold_cache_[f] = f; return;
            }
            NodeId result = nm_.mk_or(leaves[0], leaves[1]);
            for (size_t i = 2; i < leaves.size(); ++i)
                result = nm_.mk_or(result, leaves[i]);
            fold_cache_[f] = result;
            return;
        }

        if (nm_.is_ite_bool(f)) {
            NodeId c0 = nm_.get(f).children[0];
            NodeId c1 = nm_.get(f).children[1];
            NodeId c2 = nm_.get(f).children[2];
            NodeId c  = fold(c0);
            if (nm_.is_true_node(c))  { fold_cache_[f] = fold(c1); return; }
            if (nm_.is_false_node(c)) { fold_cache_[f] = fold(c2); return; }
            NodeId t  = fold(c1);
            NodeId el = fold(c2);
            if (t == el)                                         { fold_cache_[f] = t;             return; }
            if (nm_.is_true_node(t)  && nm_.is_true_node(el))   { fold_cache_[f] = nm_.mk_true();  return; }
            if (nm_.is_false_node(t) && nm_.is_false_node(el))  { fold_cache_[f] = nm_.mk_false(); return; }
            if (nm_.is_true_node(t)  && nm_.is_false_node(el))  { fold_cache_[f] = c;              return; }
            if (nm_.is_false_node(t) && nm_.is_true_node(el))   { fold_cache_[f] = nm_.mk_not(c);  return; }
            fold_cache_[f] = (c == c0 && t == c1 && el == c2) ? f : nm_.mk_ite_bool(c, t, el);
            return;
        }

        if (nm_.is_implies(f)) {
            NodeId c0 = nm_.get(f).children[0];
            NodeId c1 = nm_.get(f).children[1];
            NodeId a  = fold(c0);
            NodeId b  = fold(c1);
            if (a == b)               { fold_cache_[f] = nm_.mk_true();  return; }
            if (nm_.is_false_node(a)) { fold_cache_[f] = nm_.mk_true();  return; }
            if (nm_.is_true_node(a))  { fold_cache_[f] = b;              return; }
            if (nm_.is_true_node(b))  { fold_cache_[f] = nm_.mk_true();  return; }
            if (nm_.is_false_node(b)) { fold_cache_[f] = nm_.mk_not(a);  return; }
            fold_cache_[f] = (a == c0 && b == c1) ? f : nm_.mk_implies(a, b);
            return;
        }

        if (nm_.is_xor(f)) {
            NodeId c0 = nm_.get(f).children[0];
            NodeId c1 = nm_.get(f).children[1];
            NodeId a  = fold(c0);
            NodeId b  = fold(c1);
            if (a == b)               { fold_cache_[f] = nm_.mk_false(); return; }
            if (nm_.is_true_node(a))  { fold_cache_[f] = nm_.mk_not(b);  return; }
            if (nm_.is_false_node(a)) { fold_cache_[f] = b;              return; }
            if (nm_.is_true_node(b))  { fold_cache_[f] = nm_.mk_not(a);  return; }
            if (nm_.is_false_node(b)) { fold_cache_[f] = a;              return; }
            fold_cache_[f] = (a == c0 && b == c1) ? f : nm_.mk_xor(a, b);
            return;
        }

        if (nm_.is_iff(f)) {
            NodeId c0 = nm_.get(f).children[0];
            NodeId c1 = nm_.get(f).children[1];
            NodeId a  = fold(c0);
            NodeId b  = fold(c1);
            if (a == b)               { fold_cache_[f] = nm_.mk_true();  return; }
            if (nm_.is_true_node(a))  { fold_cache_[f] = b;              return; }
            if (nm_.is_false_node(a)) { fold_cache_[f] = nm_.mk_not(b);  return; }
            if (nm_.is_true_node(b))  { fold_cache_[f] = a;              return; }
            if (nm_.is_false_node(b)) { fold_cache_[f] = nm_.mk_not(a);  return; }
            fold_cache_[f] = (a == c0 && b == c1) ? f : nm_.mk_iff(a, b);
            return;
        }

        fold_cache_[f] = f;  // unreachable for well-formed input
    };

    // Iterative post-order (bottom-up) traversal of the formula DAG.
    // Pre-populates fold_cache_ for every node in the subtree before fold_one
    // is called, so all child lookups inside fold_one are O(1) cache hits.
    struct Frame { NodeId n; bool ready; };
    std::vector<Frame> stk;
    stk.push_back({root, false});

    while (!stk.empty()) {
        // Snapshot n and ready as values — stk may reallocate during push_back.
        NodeId n     = stk.back().n;
        bool   ready = stk.back().ready;

        if (fold_cache_.count(n)) { stk.pop_back(); continue; }

        if (!ready) {
            // Mark ready before pushing children (survives potential realloc).
            stk.back().ready = true;
            // Leaf nodes need no child traversal.
            if (!nm_.is_true_node(n) && !nm_.is_false_node(n) &&
                !nm_.is_eq(n)        && !is_atom(n)) {
                const NodeData& d   = nm_.get(n);
                const uint32_t  nch = static_cast<uint32_t>(d.children.size());
                NodeId          ch[3];
                for (uint32_t i = 0; i < nch; ++i) ch[i] = d.children[i];
                for (uint32_t i = 0; i < nch; ++i)
                    if (!fold_cache_.count(ch[i]))
                        stk.push_back({ch[i], false});
            }
        } else {
            stk.pop_back();
            fold_one(n);
        }
    }

    return fold_cache_[root];
}

// ============================================================================
// Batch substitution + folding
// ============================================================================

// Substitute all atoms in `subst` simultaneously, then constant-fold.
// Memoized via subst_cache_ — caller must clear subst_cache_ before each batch.
NodeId Simplifier::subst_many_and_fold(NodeId root,
                                        const std::unordered_map<NodeId, NodeId>& subst)
{
    if (auto it = subst_cache_.find(root); it != subst_cache_.end())
        return it->second;

    // compute: store subst_cache_[f] for a single node whose children are cached.
    auto compute = [&](NodeId f) {
        if (nm_.is_true_node(f) || nm_.is_false_node(f)) {
            subst_cache_[f] = f; return;
        }
        if (nm_.is_eq(f) || is_atom(f)) {
            auto it = subst.find(f);
            subst_cache_[f] = (it != subst.end()) ? it->second : f;
            return;
        }
        const NodeData& d   = nm_.get(f);
        SymbolId         sym = d.sym;
        NodeId           old_ch[3];
        const uint32_t   nch = static_cast<uint32_t>(d.children.size());
        assert(nch <= 3 && "Boolean connectives have at most 3 children");
        for (uint32_t i = 0; i < nch; ++i) old_ch[i] = d.children[i];

        NodeId new_ch[3];
        bool   any_change = false;
        for (uint32_t i = 0; i < nch; ++i) {
            new_ch[i] = subst_cache_.at(old_ch[i]);
            if (new_ch[i] != old_ch[i]) any_change = true;
        }
        if (!any_change) { subst_cache_[f] = f; return; }
        subst_cache_[f] = fold(nm_.mk_app(sym, std::span<const NodeId>(new_ch, nch)));
    };

    struct Frame { NodeId n; bool ready; };
    std::vector<Frame> stk;
    stk.push_back({root, false});

    while (!stk.empty()) {
        NodeId n     = stk.back().n;
        bool   ready = stk.back().ready;

        if (subst_cache_.count(n)) { stk.pop_back(); continue; }

        if (!ready) {
            stk.back().ready = true;
            if (!nm_.is_true_node(n) && !nm_.is_false_node(n) &&
                !nm_.is_eq(n)        && !is_atom(n)) {
                const NodeData& d   = nm_.get(n);
                const uint32_t  nch = static_cast<uint32_t>(d.children.size());
                NodeId          ch[3];
                for (uint32_t i = 0; i < nch; ++i) ch[i] = d.children[i];
                for (uint32_t i = 0; i < nch; ++i)
                    if (!subst_cache_.count(ch[i]))
                        stk.push_back({ch[i], false});
            }
        } else {
            stk.pop_back();
            compute(n);
        }
    }

    return subst_cache_[root];
}

// ============================================================================
// Single-atom substitution + folding (used by tests / callers outside run_pass)
// ============================================================================

NodeId Simplifier::subst_and_fold(NodeId f, NodeId atom, bool forced_positive)
{
    // If f is exactly the atom: replace with its forced value.
    if (f == atom)
        return forced_positive ? nm_.mk_true() : nm_.mk_false();

    // Leaf nodes that are not the target atom are left unchanged.
    if (nm_.is_true_node(f) || nm_.is_false_node(f)) return f;
    if (nm_.is_eq(f) || is_atom(f)) return f;

    // Compound node: recurse into children.
    // Snapshot sym + children into stack locals before any nm_ call that might
    // reallocate the nodes_ vector.  All Boolean connectives have ≤3 children.
    const NodeData& d  = nm_.get(f);
    SymbolId         sym = d.sym;
    NodeId           old_ch[3];
    const uint32_t   nch = static_cast<uint32_t>(d.children.size());
    assert(nch <= 3 && "Boolean connectives have at most 3 children");
    for (uint32_t i = 0; i < nch; ++i) old_ch[i] = d.children[i];
    // d is no longer safe to use after this point (nm_ calls may reallocate).

    NodeId new_ch[3];
    bool any_change = false;
    for (uint32_t i = 0; i < nch; ++i) {
        new_ch[i] = subst_and_fold(old_ch[i], atom, forced_positive);
        if (new_ch[i] != old_ch[i]) any_change = true;
    }

    if (!any_change) return f;

    return fold(nm_.mk_app(sym, std::span<const NodeId>(new_ch, nch)));
}

// ============================================================================
// Equality union-find
// ============================================================================

NodeId Simplifier::uf_find(NodeId n)
{
    // Pass 1: walk to root.
    NodeId root = n;
    while (true) {
        auto it = parent_.find(root);
        if (it == parent_.end()) break;
        root = it->second;
    }
    // Pass 2: path compression — point every node on the path directly to root.
    while (n != root) {
        auto it   = parent_.find(n);
        NodeId nx = it->second;
        it->second = root;
        n = nx;
    }
    return root;
}

void Simplifier::uf_union(NodeId a, NodeId b)
{
    NodeId ra = uf_find(a);
    NodeId rb = uf_find(b);
    if (ra != rb) parent_[ra] = rb;
}

// Rewrite mk_eq(x,y) → mk_eq(find(x), find(y)) throughout f.
// If find(x)==find(y) the atom collapses to True (via mk_eq's reflexivity rule).
// Compound nodes whose children changed are re-folded.
NodeId Simplifier::normalize_eq_fml(NodeId root)
{
    if (auto it = norm_cache_.find(root); it != norm_cache_.end())
        return it->second;

    auto compute = [&](NodeId f) {
        if (nm_.is_eq(f)) {
            NodeId lhs = nm_.get(f).children[0];
            NodeId rhs = nm_.get(f).children[1];
            norm_cache_[f] = nm_.mk_eq(uf_find(lhs), uf_find(rhs));
            return;
        }
        if (nm_.is_true_node(f) || nm_.is_false_node(f) || is_atom(f)) {
            norm_cache_[f] = f; return;
        }
        const NodeData& d   = nm_.get(f);
        SymbolId         sym = d.sym;
        NodeId           old_ch[3];
        const uint32_t   nch = static_cast<uint32_t>(d.children.size());
        assert(nch <= 3 && "Boolean connectives have at most 3 children");
        for (uint32_t i = 0; i < nch; ++i) old_ch[i] = d.children[i];

        NodeId new_ch[3];
        bool   any_change = false;
        for (uint32_t i = 0; i < nch; ++i) {
            new_ch[i] = norm_cache_.at(old_ch[i]);
            if (new_ch[i] != old_ch[i]) any_change = true;
        }
        if (!any_change) { norm_cache_[f] = f; return; }
        norm_cache_[f] = fold(nm_.mk_app(sym, std::span<const NodeId>(new_ch, nch)));
    };

    struct Frame { NodeId n; bool ready; };
    std::vector<Frame> stk;
    stk.push_back({root, false});

    while (!stk.empty()) {
        NodeId n     = stk.back().n;
        bool   ready = stk.back().ready;

        if (norm_cache_.count(n)) { stk.pop_back(); continue; }

        if (!ready) {
            stk.back().ready = true;
            // eq nodes are formula-level leaves (don't recurse into U-sorted children).
            if (!nm_.is_true_node(n) && !nm_.is_false_node(n) &&
                !nm_.is_eq(n)        && !is_atom(n)) {
                const NodeData& d   = nm_.get(n);
                const uint32_t  nch = static_cast<uint32_t>(d.children.size());
                NodeId          ch[3];
                for (uint32_t i = 0; i < nch; ++i) ch[i] = d.children[i];
                for (uint32_t i = 0; i < nch; ++i)
                    if (!norm_cache_.count(ch[i]))
                        stk.push_back({ch[i], false});
            }
        } else {
            stk.pop_back();
            compute(n);
        }
    }

    return norm_cache_[root];
}

// ============================================================================
// Unit propagation pass
// ============================================================================

bool Simplifier::run_pass(std::vector<NodeId>& assertions)
{
    bool changed = false;

    // Phase 1: constant-fold (and optionally flatten) everything.
    for (auto& f : assertions) {
        NodeId folded = fold(f);
        if (folded != f) {
            f       = folded;
            changed = true;
        }
    }

    // Phase 2: collect unit atoms + build O(1) lookup maps for unit assertions.
    // A unit is an assertion that is exactly an atom or not(atom).
    struct Unit { NodeId atom; bool positive; };
    std::vector<Unit> units;
    // Maps atom → assertion index for direct O(1) update when the unit is forced.
    std::unordered_map<NodeId, size_t> pos_unit_idx;  // atom where assertions[k] == atom
    std::unordered_map<NodeId, size_t> neg_unit_idx;  // atom where assertions[k] == NOT(atom)
    for (size_t k = 0; k < assertions.size(); ++k) {
        const NodeId f = assertions[k];
        if (nm_.is_eq(f) || is_atom(f)) {
            units.push_back({f, true});
            pos_unit_idx[f] = k;
        } else if (nm_.is_not(f)) {
            NodeId ch = nm_.get(f).children[0];
            if (nm_.is_eq(ch) || is_atom(ch)) {
                units.push_back({ch, false});
                neg_unit_idx[ch] = k;
            }
        }
    }

    if (units.empty()) return changed;

    // Phase 3: propagate all newly forced units into compound assertions.
    //
    // Batched approach: collect all new units first, then apply them in a
    // single memoized pass over each compound formula (O(total_formula_nodes)
    // rather than O(K × total_formula_nodes)).
    // Unit assertions themselves are updated via O(1) index maps.
    std::unordered_map<NodeId, NodeId> subst;  // atom → mk_true()/mk_false()

    for (auto& [atom, positive] : units) {
        if (!forced_set_.insert(atom).second) continue;  // already forced
        forced_.push_back({atom, positive});

        // For positive Eq units, record the merge in the union-find so that
        // Phase 4 can collapse transitive equalities.
        if (nm_.is_eq(atom) && positive) {
            NodeId lhs = nm_.get(atom).children[0];
            NodeId rhs = nm_.get(atom).children[1];
            uf_union(lhs, rhs);
        }

        // Update the unit assertion that IS exactly this atom (O(1) lookup).
        if (auto it = pos_unit_idx.find(atom); it != pos_unit_idx.end()) {
            NodeId& f = assertions[it->second];
            if (!nm_.is_true_node(f) && !nm_.is_false_node(f)) {
                f       = positive ? nm_.mk_true() : nm_.mk_false();
                changed = true;
            }
        }
        // Update the unit assertion that IS NOT(atom) (O(1) lookup).
        if (auto it = neg_unit_idx.find(atom); it != neg_unit_idx.end()) {
            NodeId& f = assertions[it->second];
            if (!nm_.is_true_node(f) && !nm_.is_false_node(f)) {
                f       = positive ? nm_.mk_false() : nm_.mk_true();
                changed = true;
            }
        }

        subst[atom] = positive ? nm_.mk_true() : nm_.mk_false();
    }

    // Apply all substitutions to compound assertions in one memoized sweep.
    if (!subst.empty()) {
        subst_cache_.clear();
        for (size_t k = 0; k < assertions.size(); ++k) {
            NodeId& f = assertions[k];
            if (nm_.is_true_node(f) || nm_.is_false_node(f)) continue;
            if (nm_.is_eq(f) || is_atom(f)) continue;
            if (nm_.is_not(f)) {
                NodeId ch = nm_.get(f).children[0];
                if (nm_.is_eq(ch) || is_atom(ch)) continue;
            }
            NodeId new_f = subst_many_and_fold(f, subst);
            if (new_f != f) {
                f       = new_f;
                changed = true;
            }
        }
    }

    // Phase 4: normalize Eq atoms by the equality union-find.
    // Handles transitivity: if a=b and b=c are forced, Eq(a,c) collapses to True.
    if (!parent_.empty()) {
        norm_cache_.clear();
        for (auto& f : assertions) {
            if (nm_.is_true_node(f) || nm_.is_false_node(f)) continue;
            NodeId nf = normalize_eq_fml(f);
            if (nf != f) {
                f       = nf;
                changed = true;
            }
        }
    }

    return changed;
}

// ============================================================================
// Top-level driver
// ============================================================================

void Simplifier::run(std::vector<NodeId>& assertions, int passes)
{
    for (int i = 0; i < passes; ++i) {
        if (!run_pass(assertions)) break;
        ++passes_run_;
    }
}

} // namespace llm2smt
