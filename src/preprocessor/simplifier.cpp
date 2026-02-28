#include "preprocessor/simplifier.h"

#include <cassert>

namespace llm2smt {

// ============================================================================
// Constant folding + optional And/Or flattening
// ============================================================================

FmlRef Simplifier::fold(FmlRef f)
{
    switch (f->kind) {
    case FmlKind::True:
    case FmlKind::False:
    case FmlKind::Eq:
    case FmlKind::Pred:
        return f;

    case FmlKind::Not: {
        FmlRef fc = fold(f->children[0]);
        if (fc->kind == FmlKind::True)  return fml_false();
        if (fc->kind == FmlKind::False) return fml_true();
        if (fc->kind == FmlKind::Not)   return fc->children[0];
        if (fc.get() == f->children[0].get()) return f;
        return fml_not(fc);
    }

    case FmlKind::And: {
        // Lazy allocation: scan for the first change; only then build new_ch.
        // This avoids any heap allocation when the formula is already stable.
        for (size_t i = 0; i < f->children.size(); ++i) {
            FmlRef fc = fold(f->children[i]);
            if (fc->kind == FmlKind::False) return fml_false();
            const bool changed = fc->kind == FmlKind::True
                              || (flatten_ && fc->kind == FmlKind::And)
                              || fc.get() != f->children[i].get();
            if (!changed) continue;

            // Build output: unchanged prefix + current + fold remaining.
            std::vector<FmlRef> new_ch;
            new_ch.reserve(f->children.size());
            for (size_t j = 0; j < i; ++j)
                new_ch.push_back(f->children[j]);

            auto push = [&](FmlRef c) {
                if (c->kind == FmlKind::True) return;
                if (flatten_ && c->kind == FmlKind::And)
                    for (auto& sub : c->children) new_ch.push_back(sub);
                else
                    new_ch.push_back(std::move(c));
            };
            push(std::move(fc));
            for (size_t j = i + 1; j < f->children.size(); ++j) {
                FmlRef fj = fold(f->children[j]);
                if (fj->kind == FmlKind::False) return fml_false();
                push(std::move(fj));
            }
            if (new_ch.empty()) return fml_true();
            if (new_ch.size() == 1) return new_ch[0];
            return fml_and(std::move(new_ch));
        }
        return f;
    }

    case FmlKind::Or: {
        // Symmetric to And.
        for (size_t i = 0; i < f->children.size(); ++i) {
            FmlRef fc = fold(f->children[i]);
            if (fc->kind == FmlKind::True) return fml_true();
            const bool changed = fc->kind == FmlKind::False
                              || (flatten_ && fc->kind == FmlKind::Or)
                              || fc.get() != f->children[i].get();
            if (!changed) continue;

            std::vector<FmlRef> new_ch;
            new_ch.reserve(f->children.size());
            for (size_t j = 0; j < i; ++j)
                new_ch.push_back(f->children[j]);

            auto push = [&](FmlRef c) {
                if (c->kind == FmlKind::False) return;
                if (flatten_ && c->kind == FmlKind::Or)
                    for (auto& sub : c->children) new_ch.push_back(sub);
                else
                    new_ch.push_back(std::move(c));
            };
            push(std::move(fc));
            for (size_t j = i + 1; j < f->children.size(); ++j) {
                FmlRef fj = fold(f->children[j]);
                if (fj->kind == FmlKind::True) return fml_true();
                push(std::move(fj));
            }
            if (new_ch.empty()) return fml_false();
            if (new_ch.size() == 1) return new_ch[0];
            return fml_or(std::move(new_ch));
        }
        return f;
    }

    case FmlKind::Ite: {
        assert(f->children.size() == 3);
        FmlRef c = fold(f->children[0]);
        if (c->kind == FmlKind::True)  return fold(f->children[1]);
        if (c->kind == FmlKind::False) return fold(f->children[2]);
        FmlRef t  = fold(f->children[1]);
        FmlRef el = fold(f->children[2]);
        if (t.get() == el.get())                                      return t;  // Ite(C,F,F) ≡ F
        if (t->kind == FmlKind::True  && el->kind == FmlKind::True)  return fml_true();
        if (t->kind == FmlKind::False && el->kind == FmlKind::False) return fml_false();
        if (t->kind == FmlKind::True  && el->kind == FmlKind::False) return c;
        if (t->kind == FmlKind::False && el->kind == FmlKind::True)  return fml_not(c);
        if (c.get() == f->children[0].get() &&
            t.get() == f->children[1].get() &&
            el.get() == f->children[2].get()) return f;
        return fml_ite(c, t, el);
    }

    case FmlKind::Implies: {
        assert(f->children.size() == 2);
        FmlRef a = fold(f->children[0]);
        FmlRef b = fold(f->children[1]);
        if (a.get() == b.get())        return fml_true();   // P → P
        if (a->kind == FmlKind::False) return fml_true();
        if (a->kind == FmlKind::True)  return b;
        if (b->kind == FmlKind::True)  return fml_true();
        if (b->kind == FmlKind::False) return fml_not(a);
        if (a.get() == f->children[0].get() && b.get() == f->children[1].get()) return f;
        return fml_implies(a, b);
    }

    case FmlKind::Xor: {
        assert(f->children.size() == 2);
        FmlRef a = fold(f->children[0]);
        FmlRef b = fold(f->children[1]);
        if (a.get() == b.get())                                       return fml_false(); // P ⊕ P
        if (a->kind == FmlKind::True  && b->kind == FmlKind::True)  return fml_false();
        if (a->kind == FmlKind::False && b->kind == FmlKind::False) return fml_false();
        if (a->kind == FmlKind::True  && b->kind == FmlKind::False) return fml_true();
        if (a->kind == FmlKind::False && b->kind == FmlKind::True)  return fml_true();
        if (a->kind == FmlKind::True)  return fml_not(b);
        if (a->kind == FmlKind::False) return b;
        if (b->kind == FmlKind::True)  return fml_not(a);
        if (b->kind == FmlKind::False) return a;
        if (a.get() == f->children[0].get() && b.get() == f->children[1].get()) return f;
        return fml_xor(a, b);
    }

    case FmlKind::BoolEq: {
        assert(f->children.size() == 2);
        FmlRef a = fold(f->children[0]);
        FmlRef b = fold(f->children[1]);
        if (a.get() == b.get())        return fml_true();   // P ↔ P
        if (a->kind == FmlKind::True)  return b;
        if (a->kind == FmlKind::False) return fml_not(b);
        if (b->kind == FmlKind::True)  return a;
        if (b->kind == FmlKind::False) return fml_not(a);
        if (a.get() == f->children[0].get() && b.get() == f->children[1].get()) return f;
        return fml_booleq(a, b);
    }
    }
    return f; // unreachable
}

// ============================================================================
// Substitution + folding
// ============================================================================

// Returns whether `f` is the same atom as `atom` (ignoring sign).
static bool is_matching_atom(const Fml& f, const Fml& atom)
{
    return (f.kind == FmlKind::Eq || f.kind == FmlKind::Pred)
        && fml_atoms_equal(f, atom);
}

FmlRef Simplifier::subst_and_fold(FmlRef f, const Fml& atom, bool forced_positive)
{
    // If f is the atom itself: replace with its forced value.
    if (is_matching_atom(*f, atom))
        return forced_positive ? fml_true() : fml_false();

    switch (f->kind) {
    case FmlKind::True:
    case FmlKind::False:
    case FmlKind::Eq:
    case FmlKind::Pred:
        return f;  // different atom, leave it

    default: {
        // Lazy: find first changed child; only then allocate a new node.
        for (size_t i = 0; i < f->children.size(); ++i) {
            FmlRef nc = subst_and_fold(f->children[i], atom, forced_positive);
            if (nc.get() == f->children[i].get()) continue;

            // First change at index i.
            std::vector<FmlRef> new_children;
            new_children.reserve(f->children.size());
            for (size_t j = 0; j < i; ++j)
                new_children.push_back(f->children[j]);
            new_children.push_back(std::move(nc));
            for (size_t j = i + 1; j < f->children.size(); ++j)
                new_children.push_back(
                    subst_and_fold(f->children[j], atom, forced_positive));

            auto new_f = std::make_shared<Fml>();
            new_f->kind     = f->kind;
            new_f->eq_lhs   = f->eq_lhs;
            new_f->eq_rhs   = f->eq_rhs;
            new_f->pred     = f->pred;
            new_f->children = std::move(new_children);
            return fold(new_f);
        }
        return fold(f);
    }
    }
}

// ============================================================================
// Equality union-find
// ============================================================================

NodeId Simplifier::uf_find(NodeId n)
{
    auto it = parent_.find(n);
    if (it == parent_.end()) return n;
    NodeId root = uf_find(it->second);
    it->second = root;  // path compression
    return root;
}

void Simplifier::uf_union(NodeId a, NodeId b)
{
    NodeId ra = uf_find(a);
    NodeId rb = uf_find(b);
    if (ra != rb) parent_[ra] = rb;
}

// Rewrite Eq(x,y) → Eq(find(x), find(y)) throughout f.
// If find(x)==find(y) the atom collapses to True.
// Compound nodes whose children changed are re-folded.
FmlRef Simplifier::normalize_eq_fml(FmlRef f)
{
    if (f->kind == FmlKind::Eq) {
        NodeId nx = uf_find(f->eq_lhs);
        NodeId ny = uf_find(f->eq_rhs);
        if (nx == ny) return fml_true();
        if (nx == f->eq_lhs && ny == f->eq_rhs) return f;
        if (nx == f->eq_rhs && ny == f->eq_lhs) return f;
        return fml_eq(nx, ny);
    }
    if (f->children.empty()) return f;  // True, False, Pred — nothing to normalize

    // Lazy: find first changed child; only then allocate a new node.
    for (size_t i = 0; i < f->children.size(); ++i) {
        FmlRef nc = normalize_eq_fml(f->children[i]);
        if (nc.get() == f->children[i].get()) continue;

        // First change at index i.
        std::vector<FmlRef> new_ch;
        new_ch.reserve(f->children.size());
        for (size_t j = 0; j < i; ++j)
            new_ch.push_back(f->children[j]);
        new_ch.push_back(std::move(nc));
        for (size_t j = i + 1; j < f->children.size(); ++j)
            new_ch.push_back(normalize_eq_fml(f->children[j]));

        auto new_f = std::make_shared<Fml>();
        new_f->kind     = f->kind;
        new_f->eq_lhs   = f->eq_lhs;
        new_f->eq_rhs   = f->eq_rhs;
        new_f->pred     = f->pred;
        new_f->children = std::move(new_ch);
        return fold(new_f);
    }
    return f;
}

// ============================================================================
// Helpers
// ============================================================================

bool Simplifier::already_forced(const Fml& atom) const
{
    for (auto& fa : forced_)
        if (fml_atoms_equal(*fa.atom, atom))
            return true;
    return false;
}

// ============================================================================
// Unit propagation pass
// ============================================================================

bool Simplifier::run_pass(std::vector<FmlRef>& assertions)
{
    bool changed = false;

    // Phase 1: constant-fold (and flatten) everything.
    for (auto& f : assertions) {
        FmlRef folded = fold(f);
        if (folded.get() != f.get()) {
            f       = folded;
            changed = true;
        }
    }

    // Phase 2: collect unit atoms.
    // A unit is a formula that is exactly an atom or Not(atom).
    struct Unit { FmlRef atom; bool positive; };
    std::vector<Unit> units;
    for (auto& f : assertions) {
        if (f->kind == FmlKind::Eq || f->kind == FmlKind::Pred) {
            units.push_back({f, true});
        } else if (f->kind == FmlKind::Not) {
            auto& ch = f->children[0];
            if (ch->kind == FmlKind::Eq || ch->kind == FmlKind::Pred)
                units.push_back({ch, false});
        }
    }

    if (units.empty()) return changed;

    // Phase 3: propagate each new unit into all other assertions.
    for (auto& [atom, positive] : units) {
        if (already_forced(*atom)) continue;
        forced_.push_back({atom, positive});

        // For positive Eq atoms, record the merge in the union-find so that
        // Phase 4 can collapse transitive equalities (e.g. Eq(a,c) once
        // both Eq(a,b) and Eq(b,c) are forced).
        if (atom->kind == FmlKind::Eq && positive)
            uf_union(atom->eq_lhs, atom->eq_rhs);

        for (auto& f : assertions) {
            if (f->kind == FmlKind::True || f->kind == FmlKind::False) continue;
            FmlRef new_f = subst_and_fold(f, *atom, positive);
            if (new_f.get() != f.get()) {
                f       = new_f;
                changed = true;
            }
        }
    }

    // Phase 4: normalize Eq atoms by the equality union-find.
    // Handles transitivity: if a=b and b=c are forced, Eq(a,c) collapses to True.
    if (!parent_.empty()) {
        for (auto& f : assertions) {
            if (f->kind == FmlKind::True || f->kind == FmlKind::False) continue;
            FmlRef nf = normalize_eq_fml(f);
            if (nf.get() != f.get()) {
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

void Simplifier::run(std::vector<FmlRef>& assertions, int passes)
{
    for (int i = 0; i < passes; ++i) {
        if (!run_pass(assertions)) break;
        ++passes_run_;
    }
}

} // namespace llm2smt
