#include "preprocessor/simplifier.h"

#include <cassert>

namespace llm2smt {

// ============================================================================
// Constant folding
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
        // Apply simplification rules first (True/False/double-negation).
        if (fc->kind == FmlKind::True)  return fml_false();
        if (fc->kind == FmlKind::False) return fml_true();
        if (fc->kind == FmlKind::Not)   return fc->children[0];
        // No simplification; only allocate if child actually changed.
        if (fc.get() == f->children[0].get()) return f;
        return fml_not(fc);
    }

    case FmlKind::And: {
        std::vector<FmlRef> new_ch;
        new_ch.reserve(f->children.size());
        bool any_changed = false;
        for (auto& ch : f->children) {
            FmlRef fc = fold(ch);
            if (fc->kind == FmlKind::False) return fml_false();   // short-circuit
            if (fc->kind == FmlKind::True)  { any_changed = true; continue; }  // drop
            if (fc.get() != ch.get()) any_changed = true;
            new_ch.push_back(std::move(fc));
        }
        if (!any_changed) return f;
        if (new_ch.empty())     return fml_true();
        if (new_ch.size() == 1) return new_ch[0];
        return fml_and(std::move(new_ch));
    }

    case FmlKind::Or: {
        std::vector<FmlRef> new_ch;
        new_ch.reserve(f->children.size());
        bool any_changed = false;
        for (auto& ch : f->children) {
            FmlRef fc = fold(ch);
            if (fc->kind == FmlKind::True)  return fml_true();    // short-circuit
            if (fc->kind == FmlKind::False) { any_changed = true; continue; }  // drop
            if (fc.get() != ch.get()) any_changed = true;
            new_ch.push_back(std::move(fc));
        }
        if (!any_changed) return f;
        if (new_ch.empty())     return fml_false();
        if (new_ch.size() == 1) return new_ch[0];
        return fml_or(std::move(new_ch));
    }

    case FmlKind::Ite: {
        assert(f->children.size() == 3);
        FmlRef c = fold(f->children[0]);
        if (c->kind == FmlKind::True)  return fold(f->children[1]);  // ite(⊤,T,F) = T
        if (c->kind == FmlKind::False) return fold(f->children[2]);  // ite(⊥,T,F) = F
        FmlRef t  = fold(f->children[1]);
        FmlRef el = fold(f->children[2]);
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
        if (a->kind == FmlKind::False) return fml_true();   // ⊥→b = ⊤
        if (a->kind == FmlKind::True)  return b;             // ⊤→b = b
        if (b->kind == FmlKind::True)  return fml_true();   // a→⊤ = ⊤
        if (b->kind == FmlKind::False) return fml_not(a);   // a→⊥ = ¬a
        if (a.get() == f->children[0].get() && b.get() == f->children[1].get()) return f;
        return fml_implies(a, b);
    }

    case FmlKind::Xor: {
        assert(f->children.size() == 2);
        FmlRef a = fold(f->children[0]);
        FmlRef b = fold(f->children[1]);
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
        if (a->kind == FmlKind::True)  return b;             // ⊤↔b = b
        if (a->kind == FmlKind::False) return fml_not(b);   // ⊥↔b = ¬b
        if (b->kind == FmlKind::True)  return a;             // a↔⊤ = a
        if (b->kind == FmlKind::False) return fml_not(a);   // a↔⊥ = ¬a
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
        return f;

    case FmlKind::Eq:
    case FmlKind::Pred:
        return f;  // different atom, leave it

    default: {
        // Recurse into all children; only allocate a new node if something changed.
        bool any_changed = false;
        std::vector<FmlRef> new_children;
        new_children.reserve(f->children.size());
        for (auto& ch : f->children) {
            FmlRef new_ch = subst_and_fold(ch, atom, forced_positive);
            if (new_ch.get() != ch.get()) any_changed = true;
            new_children.push_back(std::move(new_ch));
        }
        if (!any_changed) return fold(f);
        auto new_f = std::make_shared<Fml>();
        new_f->kind     = f->kind;
        new_f->eq_lhs   = f->eq_lhs;
        new_f->eq_rhs   = f->eq_rhs;
        new_f->pred     = f->pred;
        new_f->children = std::move(new_children);
        return fold(new_f);
    }
    }
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

    // Phase 1: constant-fold everything.
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

        for (auto& f : assertions) {
            if (f->kind == FmlKind::True || f->kind == FmlKind::False) continue;
            FmlRef new_f = subst_and_fold(f, *atom, positive);
            if (new_f.get() != f.get()) {
                f       = new_f;
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
    }
}

} // namespace llm2smt
