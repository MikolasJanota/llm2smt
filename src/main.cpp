#include <fstream>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>

#include "antlr4-runtime.h"
#include "SMTLIBv2Lexer.h"
#include "SMTLIBv2Parser.h"

#include "core/node_manager.h"
#include "theories/euf/euf_solver.h"
#include "parser/smt_context.h"
#include "parser/smt2_visitor.h"
#include "sat/ipasir_up.h"

namespace llm2smt {

// ============================================================================
// Stub SAT solver (for bootstrapping before integrating CaDiCaL)
// ============================================================================

class StubSatSolver : public SatSolver {
public:
    int new_var() override { return ++next_var_; }

    void add_clause(std::span<const int> lits) override {
        clauses_.emplace_back(lits.begin(), lits.end());
    }

    void connect_propagator(ExternalPropagator& prop) override {
        propagator_ = &prop;
    }

    // Very naive DPLL-like solver for small QF_EUF instances.
    // In practice this will be replaced by CaDiCaL with IPASIR-UP.
    SolveResult solve() override {
        if (!propagator_) return SolveResult::UNKNOWN;

        // Collect all variables
        int max_var = next_var_;

        // Check unit clauses first
        assignment_.assign(max_var + 1, 0);
        if (!assign_units()) return SolveResult::UNSAT;

        // Try to propagate and check
        std::vector<int> model;
        for (int v = 1; v <= max_var; ++v) {
            model.push_back(assignment_[v] >= 0 ? v : -v);
        }

        // Notify the propagator of assignments
        for (int lit : model) {
            propagator_->notify_assignment(lit, false);
        }

        if (!propagator_->cb_check_found_model(model)) {
            // Conflict detected — report UNSAT for now
            return SolveResult::UNSAT;
        }

        // Check if all clauses are satisfied
        for (const auto& clause : clauses_) {
            bool satisfied = false;
            for (int lit : clause) {
                int v = std::abs(lit);
                if (v <= max_var && ((lit > 0 && assignment_[v] > 0) ||
                                     (lit < 0 && assignment_[v] < 0))) {
                    satisfied = true;
                    break;
                }
            }
            if (!satisfied) return SolveResult::UNKNOWN;
        }

        return SolveResult::SAT;
    }

private:
    int next_var_ = 0;
    std::vector<std::vector<int>> clauses_;
    ExternalPropagator* propagator_ = nullptr;
    std::vector<int> assignment_;  // 0=unset, >0=true, <0=false

    bool assign_units() {
        bool changed = true;
        while (changed) {
            changed = false;
            for (const auto& clause : clauses_) {
                int unset_count = 0;
                int unset_lit   = 0;
                bool satisfied  = false;
                for (int lit : clause) {
                    int v = std::abs(lit);
                    if (v >= static_cast<int>(assignment_.size())) continue;
                    int val = assignment_[v];
                    if (val == 0) { unset_count++; unset_lit = lit; }
                    else if ((lit > 0 && val > 0) || (lit < 0 && val < 0)) {
                        satisfied = true; break;
                    }
                }
                if (satisfied) continue;
                if (unset_count == 0) return false;  // empty clause
                if (unset_count == 1) {
                    int v = std::abs(unset_lit);
                    assignment_[v] = (unset_lit > 0) ? 1 : -1;
                    changed = true;
                }
            }
        }
        // Default unset vars to true
        for (int& a : assignment_) if (a == 0) a = 1;
        return true;
    }
};

} // namespace llm2smt

int main(int argc, char** argv) {
    using namespace llm2smt;
    using namespace smt2parser;

    try {
        antlr4::ANTLRInputStream* input_stream = nullptr;
        std::ifstream file;

        if (argc >= 2) {
            file.open(argv[1]);
            if (!file) {
                std::cerr << "Error: cannot open file " << argv[1] << "\n";
                return 1;
            }
            input_stream = new antlr4::ANTLRInputStream(file);
        } else {
            input_stream = new antlr4::ANTLRInputStream(std::cin);
        }

        NodeManager   nm;
        StubSatSolver sat;
        EufSolver     euf(nm);
        sat.connect_propagator(euf);

        SmtContext ctx(nm, euf, sat);

        SMTLIBv2Lexer  lexer(input_stream);
        antlr4::CommonTokenStream tokens(&lexer);
        SMTLIBv2Parser parser(&tokens);

        auto* tree = parser.start();
        Smt2Visitor visitor(ctx);
        visitor.visitStart(tree);

        delete input_stream;
        return 0;

    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << "\n";
        return 1;
    }
}
