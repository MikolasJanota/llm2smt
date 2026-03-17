#include "preprocessor/simplifier.h"

#include <cassert>
#include <span>

namespace llm2smt {

Simplifier::Simplifier(NodeManager& nm) : nm_(nm) {}

// ============================================================================
// Constant folding + optional And/Or flattening
// ============================================================================

NodeId Simplifier::fold(NodeId f)
{
    // Check memoization cache — fold() is pure so result is stable.
    {
        auto it = fold_cache_.find(f);
        if (it != fold_cache_.end()) return it->second;
    }

    auto cache = [&](NodeId result) -> NodeId {
        fold_cache_[f] = result;
        return result;
    };

    if (nm_.is_true_node(f) || nm_.is_false_node(f)) return cache(f);
    if (nm_.is_eq(f) || is_atom(f)) return cache(f);

    if (nm_.is_not(f)) {
        NodeId child = nm_.get(f).children[0];
        NodeId fc    = fold(child);
        if (nm_.is_true_node(fc))  return cache(nm_.mk_false());
        if (nm_.is_false_node(fc)) return cache(nm_.mk_true());
        if (nm_.is_not(fc))        return cache(nm_.get(fc).children[0]); // ¬¬x = x
        if (fc == child) return cache(f);
        return cache(nm_.mk_not(fc));
    }

    if (nm_.is_and(f)) {
        NodeId c0 = nm_.get(f).children[0];
        NodeId c1 = nm_.get(f).children[1];

        std::vector<NodeId> leaves;
        bool found_false = false;

        auto collect = [&](auto& self, NodeId n) -> void {
            if (found_false) return;
            NodeId fn = fold(n);
            if (nm_.is_false_node(fn)) { found_false = true; return; }
            if (nm_.is_true_node(fn))  return;  // identity element, skip
            if (flatten_ && nm_.is_and(fn)) {
                NodeId fa = nm_.get(fn).children[0];
                NodeId fb = nm_.get(fn).children[1];
                self(self, fa);
                self(self, fb);
            } else {
                leaves.push_back(fn);
            }
        };

        collect(collect, c0);
        collect(collect, c1);

        if (found_false) return cache(nm_.mk_false());
        if (leaves.empty()) return cache(nm_.mk_true());
        if (leaves.size() == 1) return cache(leaves[0]);
        if (leaves.size() == 2 && leaves[0] == c0 && leaves[1] == c1) return cache(f);
        NodeId result = nm_.mk_and(leaves[0], leaves[1]);
        for (size_t i = 2; i < leaves.size(); ++i)
            result = nm_.mk_and(result, leaves[i]);
        return cache(result);
    }

    if (nm_.is_or(f)) {
        NodeId c0 = nm_.get(f).children[0];
        NodeId c1 = nm_.get(f).children[1];

        std::vector<NodeId> leaves;
        bool found_true = false;

        auto collect = [&](auto& self, NodeId n) -> void {
            if (found_true) return;
            NodeId fn = fold(n);
            if (nm_.is_true_node(fn))  { found_true = true; return; }
            if (nm_.is_false_node(fn)) return;  // identity element, skip
            if (flatten_ && nm_.is_or(fn)) {
                NodeId fa = nm_.get(fn).children[0];
                NodeId fb = nm_.get(fn).children[1];
                self(self, fa);
                self(self, fb);
            } else {
                leaves.push_back(fn);
            }
        };

        collect(collect, c0);
        collect(collect, c1);

        if (found_true) return cache(nm_.mk_true());
        if (leaves.empty()) return cache(nm_.mk_false());
        if (leaves.size() == 1) return cache(leaves[0]);
        if (leaves.size() == 2 && leaves[0] == c0 && leaves[1] == c1) return cache(f);
        NodeId result = nm_.mk_or(leaves[0], leaves[1]);
        for (size_t i = 2; i < leaves.size(); ++i)
            result = nm_.mk_or(result, leaves[i]);
        return cache(result);
    }

    if (nm_.is_ite_bool(f)) {
        NodeId c0 = nm_.get(f).children[0];
        NodeId c1 = nm_.get(f).children[1];
        NodeId c2 = nm_.get(f).children[2];
        NodeId c  = fold(c0);
        if (nm_.is_true_node(c))  return cache(fold(c1));
        if (nm_.is_false_node(c)) return cache(fold(c2));
        NodeId t  = fold(c1);
        NodeId el = fold(c2);
        if (t == el)                                           return cache(t);
        if (nm_.is_true_node(t)  && nm_.is_true_node(el))    return cache(nm_.mk_true());
        if (nm_.is_false_node(t) && nm_.is_false_node(el))   return cache(nm_.mk_false());
        if (nm_.is_true_node(t)  && nm_.is_false_node(el))   return cache(c);
        if (nm_.is_false_node(t) && nm_.is_true_node(el))    return cache(nm_.mk_not(c));
        if (c == c0 && t == c1 && el == c2) return cache(f);
        return cache(nm_.mk_ite_bool(c, t, el));
    }

    if (nm_.is_implies(f)) {
        NodeId c0 = nm_.get(f).children[0];
        NodeId c1 = nm_.get(f).children[1];
        NodeId a  = fold(c0);
        NodeId b  = fold(c1);
        if (a == b)               return cache(nm_.mk_true());   // P → P
        if (nm_.is_false_node(a)) return cache(nm_.mk_true());
        if (nm_.is_true_node(a))  return cache(b);
        if (nm_.is_true_node(b))  return cache(nm_.mk_true());
        if (nm_.is_false_node(b)) return cache(nm_.mk_not(a));
        if (a == c0 && b == c1) return cache(f);
        return cache(nm_.mk_implies(a, b));
    }

    if (nm_.is_xor(f)) {
        NodeId c0 = nm_.get(f).children[0];
        NodeId c1 = nm_.get(f).children[1];
        NodeId a  = fold(c0);
        NodeId b  = fold(c1);
        if (a == b)               return cache(nm_.mk_false());  // P ⊕ P = false
        if (nm_.is_true_node(a))  return cache(nm_.mk_not(b));
        if (nm_.is_false_node(a)) return cache(b);
        if (nm_.is_true_node(b))  return cache(nm_.mk_not(a));
        if (nm_.is_false_node(b)) return cache(a);
        if (a == c0 && b == c1) return cache(f);
        return cache(nm_.mk_xor(a, b));
    }

    if (nm_.is_iff(f)) {
        NodeId c0 = nm_.get(f).children[0];
        NodeId c1 = nm_.get(f).children[1];
        NodeId a  = fold(c0);
        NodeId b  = fold(c1);
        if (a == b)               return cache(nm_.mk_true());   // P ↔ P = true
        if (nm_.is_true_node(a))  return cache(b);
        if (nm_.is_false_node(a)) return cache(nm_.mk_not(b));
        if (nm_.is_true_node(b))  return cache(a);
        if (nm_.is_false_node(b)) return cache(nm_.mk_not(a));
        if (a == c0 && b == c1) return cache(f);
        return cache(nm_.mk_iff(a, b));
    }

    return cache(f);  // unreachable for well-formed input
}

// ============================================================================
// Batch substitution + folding
// ============================================================================

// Substitute all atoms in `subst` simultaneously, then constant-fold.
// Memoized via subst_cache_ — caller must clear subst_cache_ before each batch.
NodeId Simplifier::subst_many_and_fold(NodeId f,
                                        const std::unordered_map<NodeId, NodeId>& subst)
{
    {
        auto it = subst_cache_.find(f);
        if (it != subst_cache_.end()) return it->second;
    }
    auto cache = [&](NodeId r) -> NodeId { subst_cache_[f] = r; return r; };

    if (nm_.is_true_node(f) || nm_.is_false_node(f)) return cache(f);

    if (nm_.is_eq(f) || is_atom(f)) {
        auto it = subst.find(f);
        return cache(it != subst.end() ? it->second : f);
    }

    // Compound node: snapshot children, recurse, then fold.
    const NodeData& d  = nm_.get(f);
    SymbolId         sym = d.sym;
    NodeId           old_ch[3];
    const uint32_t   nch = static_cast<uint32_t>(d.children.size());
    assert(nch <= 3 && "Boolean connectives have at most 3 children");
    for (uint32_t i = 0; i < nch; ++i) old_ch[i] = d.children[i];

    NodeId new_ch[3];
    bool any_change = false;
    for (uint32_t i = 0; i < nch; ++i) {
        new_ch[i] = subst_many_and_fold(old_ch[i], subst);
        if (new_ch[i] != old_ch[i]) any_change = true;
    }
    if (!any_change) return cache(f);
    return cache(fold(nm_.mk_app(sym, std::span<const NodeId>(new_ch, nch))));
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
NodeId Simplifier::normalize_eq_fml(NodeId f)
{
    {
        auto it = norm_cache_.find(f);
        if (it != norm_cache_.end()) return it->second;
    }
    auto cache = [&](NodeId r) -> NodeId { norm_cache_[f] = r; return r; };

    if (nm_.is_eq(f)) {
        NodeId lhs  = nm_.get(f).children[0];
        NodeId rhs  = nm_.get(f).children[1];
        NodeId nx   = uf_find(lhs);
        NodeId ny   = uf_find(rhs);
        NodeId norm = nm_.mk_eq(nx, ny);  // handles reflexivity + canonical ordering
        return cache(norm);
    }

    if (nm_.is_true_node(f) || nm_.is_false_node(f) || is_atom(f)) return cache(f);

    // Snapshot children into stack locals before any nm_ calls.
    const NodeData& d  = nm_.get(f);
    SymbolId         sym = d.sym;
    NodeId           old_ch[3];
    const uint32_t   nch = static_cast<uint32_t>(d.children.size());
    assert(nch <= 3 && "Boolean connectives have at most 3 children");
    for (uint32_t i = 0; i < nch; ++i) old_ch[i] = d.children[i];

    NodeId new_ch[3];
    bool any_change = false;
    for (uint32_t i = 0; i < nch; ++i) {
        new_ch[i] = normalize_eq_fml(old_ch[i]);
        if (new_ch[i] != old_ch[i]) any_change = true;
    }

    if (!any_change) return cache(f);
    return cache(fold(nm_.mk_app(sym, std::span<const NodeId>(new_ch, nch))));
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
