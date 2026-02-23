#pragma once

#include "preprocessor/fml.h"

#include <unordered_map>
#include <vector>

namespace llm2smt {

// Simplifies Boolean formula trees over the SMT formula IR (FmlRef).
//
// Atoms are Eq(NodeId,NodeId) and Pred(NodeId); they are treated as opaque
// propositions for the purpose of structural simplification.
//
// Implemented passes (applied in order per iteration):
//   1. Constant folding: propagate True/False through all connectives.
//   2. Unit clause propagation: identify unit assertions (a single atom or its
//      negation) and substitute them into all other assertions, then fold.
//   3. Equality normalization: maintain a union-find over NodeIds forced equal.
//      Rewrite every Eq(x,y) to Eq(find(x), find(y)); if find(x)==find(y) the
//      atom collapses to True.  This handles transitivity that boolean
//      substitution alone cannot see (e.g. forcing Eq(a,b) and Eq(b,c) makes
//      any Eq(a,c) trivially true).
//
// After run(), forced_atoms() lists every atom that was forced along with its
// polarity (true = forced true, false = forced false).  The caller must assert
// these atoms in the SAT/theory solver before the search begins.
class Simplifier {
public:
    // Constant-fold a single formula.
    FmlRef fold(FmlRef f);

    // Substitute atom (or its negation) → True/False in f, then fold.
    // forced_positive=true means the atom is known to be true.
    FmlRef subst_and_fold(FmlRef f, const Fml& atom, bool forced_positive);

    // One pass of constant folding + unit propagation.
    // Returns true if any formula changed.
    bool run_pass(std::vector<FmlRef>& assertions);

    // Up to `passes` iterations (stops early when stable).
    void run(std::vector<FmlRef>& assertions, int passes);

    struct ForcedAtom { FmlRef atom; bool positive; };
    const std::vector<ForcedAtom>& forced_atoms() const { return forced_; }

    // Number of passes that changed at least one assertion (capped at `passes`).
    int passes_run() const { return passes_run_; }

private:
    std::vector<ForcedAtom>            forced_;
    int                                passes_run_ = 0;

    // Equality union-find over NodeIds (for transitivity-aware normalization).
    std::unordered_map<NodeId, NodeId> parent_;
    NodeId uf_find(NodeId n);       // path-compressing find
    void   uf_union(NodeId a, NodeId b);

    // Rewrite every Eq(x,y) in f to Eq(find(x), find(y)), folding as needed.
    FmlRef normalize_eq_fml(FmlRef f);

    // Check whether atom has already been forced (in either polarity).
    bool already_forced(const Fml& atom) const;
};

} // namespace llm2smt
