#pragma once

#include <ostream>
#include <unordered_map>
#include <vector>

#include "core/node.h"
#include "core/node_manager.h"
#include "parser/smt_context.h"
#include "preprocessor/fml.h"
#include "theories/euf/euf_solver.h"

namespace llm2smt {

class LeanEmitter {
public:
    // Emit a Lean 4 proof to `out`.
    // proof_fmls: original assertions (pre-NNF/simplification)
    // proof_conflicts: theory lemma clauses from EufSolver::proof_conflicts()
    void emit(std::ostream& out,
              const SmtContext& ctx,
              const std::vector<FmlRef>& proof_fmls,
              const std::vector<std::vector<int>>& proof_conflicts);

private:
    // Set during emit(); used by node_to_lean / fml_to_lean.
    const SmtContext* ctx_ = nullptr;

    // ite_id → proxy NodeId: populated from proof_fmls equalities of the form
    // (proxy = ite_node).  When node_to_lean encounters an ite_id that has a
    // proxy, it returns the proxy's name instead of inlining the ite expression.
    // This keeps theory-clause atoms as opaque constants, which grind handles
    // reliably without case-splitting on the if-expression.
    std::unordered_map<NodeId, NodeId> ite_proxy_for_;

    // NodeId → Lean expression string (handles constants, n-ary apps, ite nodes)
    std::string node_to_lean(NodeId n, const NodeManager& nm) const;

    // FmlRef → Lean proposition string (atomic Eq/Pred wrapped in `decide (...)`)
    std::string fml_to_lean(FmlRef f, const NodeManager& nm) const;

    // FmlRef → Lean Prop condition string (atomic Eq/Pred NOT wrapped in decide).
    // Used for ite conditions so grind sees `if p then ...` (Prop) rather than
    // `if decide (p) then ...` (Bool), avoiding Bool→Prop normalisation mismatches.
    std::string fml_to_lean_cond(FmlRef f, const NodeManager& nm) const;

    // Build Lean type string for a function (e.g., "U → U → V" or "U → U → Prop")
    std::string fn_type(const FnDecl& fn, bool is_pred) const;
};

} // namespace llm2smt
