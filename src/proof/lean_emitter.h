#pragma once

#include <ostream>
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
              const std::vector<std::vector<int>>& proof_conflicts,
              const std::string& lean_project = {});

private:
    // NodeId → Lean expression string (handles constants and n-ary apps)
    std::string node_to_lean(NodeId n, const NodeManager& nm) const;

    // FmlRef → Lean proposition string
    std::string fml_to_lean(FmlRef f, const NodeManager& nm) const;

    // Build Lean type string for a function (e.g., "U → U → V" or "U → U → Prop")
    std::string fn_type(const FnDecl& fn, bool is_pred) const;
};

} // namespace llm2smt
