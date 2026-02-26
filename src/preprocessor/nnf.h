#pragma once

#include "preprocessor/fml.h"

namespace llm2smt {

// Forward declarations for mutual recursion.
inline FmlRef nnf_pos(FmlRef f);
inline FmlRef nnf_neg(FmlRef f);

// nnf_pos: convert f (at positive polarity) to NNF.
inline FmlRef nnf_pos(FmlRef f)
{
    switch (f->kind) {
    case FmlKind::True:
    case FmlKind::False:
    case FmlKind::Eq:
    case FmlKind::Pred:
        return f;
    case FmlKind::Not:
        return nnf_neg(f->children[0]);
    case FmlKind::And: {
        std::vector<FmlRef> ch;
        ch.reserve(f->children.size());
        for (auto& c : f->children) ch.push_back(nnf_pos(c));
        return fml_and(std::move(ch));
    }
    case FmlKind::Or: {
        std::vector<FmlRef> ch;
        ch.reserve(f->children.size());
        for (auto& c : f->children) ch.push_back(nnf_pos(c));
        return fml_or(std::move(ch));
    }
    case FmlKind::Implies:
        return fml_or({nnf_neg(f->children[0]), nnf_pos(f->children[1])});
    case FmlKind::Xor:
        return fml_or({
            fml_and({nnf_pos(f->children[0]), nnf_neg(f->children[1])}),
            fml_and({nnf_neg(f->children[0]), nnf_pos(f->children[1])})
        });
    case FmlKind::BoolEq:
        return fml_and({
            fml_or({nnf_neg(f->children[0]), nnf_pos(f->children[1])}),
            fml_or({nnf_pos(f->children[0]), nnf_neg(f->children[1])})
        });
    case FmlKind::Ite:
        return fml_and({
            fml_or({nnf_neg(f->children[0]), nnf_pos(f->children[1])}),
            fml_or({nnf_pos(f->children[0]), nnf_pos(f->children[2])})
        });
    }
    return f; // unreachable
}

// nnf_neg: convert ¬f (negation pushed inward) to NNF.
inline FmlRef nnf_neg(FmlRef f)
{
    switch (f->kind) {
    case FmlKind::True:
        return fml_false();
    case FmlKind::False:
        return fml_true();
    case FmlKind::Eq:
        return fml_not(fml_eq(f->eq_lhs, f->eq_rhs));
    case FmlKind::Pred:
        return fml_not(fml_pred(f->pred));
    case FmlKind::Not:
        return nnf_pos(f->children[0]);
    case FmlKind::And: {
        std::vector<FmlRef> ch;
        ch.reserve(f->children.size());
        for (auto& c : f->children) ch.push_back(nnf_neg(c));
        return fml_or(std::move(ch));
    }
    case FmlKind::Or: {
        std::vector<FmlRef> ch;
        ch.reserve(f->children.size());
        for (auto& c : f->children) ch.push_back(nnf_neg(c));
        return fml_and(std::move(ch));
    }
    case FmlKind::Implies:
        return fml_and({nnf_pos(f->children[0]), nnf_neg(f->children[1])});
    case FmlKind::Xor:
        // ¬(a⊕b) = (a↔b)
        return fml_and({
            fml_or({nnf_neg(f->children[0]), nnf_pos(f->children[1])}),
            fml_or({nnf_pos(f->children[0]), nnf_neg(f->children[1])})
        });
    case FmlKind::BoolEq:
        // ¬(a↔b) = (a⊕b)
        return fml_or({
            fml_and({nnf_pos(f->children[0]), nnf_neg(f->children[1])}),
            fml_and({nnf_neg(f->children[0]), nnf_pos(f->children[1])})
        });
    case FmlKind::Ite:
        // ¬ite(c,t,e) = ite(c,¬t,¬e)
        return fml_or({
            fml_and({nnf_pos(f->children[0]), nnf_neg(f->children[1])}),
            fml_and({nnf_neg(f->children[0]), nnf_neg(f->children[2])})
        });
    }
    return fml_not(f); // unreachable
}

// Entry point: convert f to NNF.
inline FmlRef to_nnf(FmlRef f) { return nnf_pos(f); }

} // namespace llm2smt
