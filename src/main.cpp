#include <chrono>
#include <csignal>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>
#include <unistd.h>

#include <CLI/CLI.hpp>

#include "antlr4-runtime.h"
#include "SMTLIBv2Lexer.h"
#include "SMTLIBv2Parser.h"

#include "core/node_manager.h"
#include "core/stats.h"
#include "theories/euf/euf_solver.h"
#include "theories/lra/lra_solver.h"
#include "parser/smt_context.h"
#include "parser/smt2_visitor.h"
#include "preprocessor/preproc_options.h"
#include "proof/lean_emitter.h"
#include "proof/proof_minimizer.h"
#include "sat/cadical_solver.h"

// Global state used by the atexit handler so stats are printed even when
// the process is killed (SIGTERM / timeout).
static llm2smt::Stats*                                    g_stats       = nullptr;
static bool                                               g_print_stats = false;
static std::chrono::steady_clock::time_point              g_start_time;

static void print_stats_atexit() {
    if (g_print_stats && g_stats) {
        auto now = std::chrono::steady_clock::now();
        g_stats->total_ms = static_cast<uint64_t>(
            std::chrono::duration_cast<std::chrono::milliseconds>(now - g_start_time).count());
        g_stats->print(std::cerr);
    }
}

static void sigterm_handler(int) {
    // write() is async-signal-safe; std::cout is not (buffered, not safe in handlers).
    [[maybe_unused]] auto r = write(STDOUT_FILENO, "unknown\n", 8);
    // exit() triggers atexit handlers (including print_stats_atexit).
    // Using exit() instead of _Exit() is technically not async-signal-safe, but
    // this is the standard approach for solver timeouts and acceptable in practice.
    std::exit(0);
}

class CombinedPropagator : public llm2smt::ExternalPropagator {
public:
    CombinedPropagator(llm2smt::EufSolver& euf, llm2smt::lra::LraSolver& lra)
        : euf_(euf), lra_(lra) {}

    void notify_assignment(int lit, bool is_fixed) override {
        euf_.notify_assignment(lit, is_fixed);
        lra_.notify_assignment(lit, is_fixed);
    }
    void notify_new_decision_level() override {
        euf_.notify_new_decision_level();
        lra_.notify_new_decision_level();
    }
    void notify_backtrack(size_t new_level) override {
        euf_.notify_backtrack(new_level);
        lra_.notify_backtrack(new_level);
    }
    const std::vector<int>& observed_vars() const override {
        observed_cache_.clear();
        observed_cache_.insert(observed_cache_.end(),
                               euf_.observed_vars().begin(), euf_.observed_vars().end());
        observed_cache_.insert(observed_cache_.end(),
                               lra_.observed_vars().begin(), lra_.observed_vars().end());
        return observed_cache_;
    }
    bool cb_check_found_model(const std::vector<int>& model) override {
        return euf_.cb_check_found_model(model) && lra_.cb_check_found_model(model);
    }
    bool cb_has_external_clause(bool& is_forgettable) override {
        if (euf_.cb_has_external_clause(is_forgettable)) {
            serving_ = Serving::Euf;
            return true;
        }
        if (lra_.cb_has_external_clause(is_forgettable)) {
            serving_ = Serving::Lra;
            return true;
        }
        serving_ = Serving::None;
        return false;
    }
    int cb_add_external_clause_lit() override {
        if (serving_ == Serving::Euf) return euf_.cb_add_external_clause_lit();
        if (serving_ == Serving::Lra) return lra_.cb_add_external_clause_lit();
        return 0;
    }
    int cb_propagate() override {
        int lit = euf_.cb_propagate();
        if (lit != 0) {
            reason_serving_ = Serving::Euf;
            return lit;
        }
        lit = lra_.cb_propagate();
        if (lit != 0) {
            reason_serving_ = Serving::Lra;
            return lit;
        }
        reason_serving_ = Serving::None;
        return 0;
    }
    int cb_decide() override {
        int lit = lra_.cb_decide();
        if (lit != 0) return lit;
        return euf_.cb_decide();
    }
    int cb_add_reason_clause_lit(int lit) override {
        if (reason_serving_ == Serving::Lra) return lra_.cb_add_reason_clause_lit(lit);
        if (reason_serving_ == Serving::Euf) return euf_.cb_add_reason_clause_lit(lit);

        // CaDiCaL may ask for a reason after intervening propagation callbacks
        // have returned 0. Dispatch by availability so a stale serving tag does
        // not produce an empty reason clause for a theory-propagated literal.
        int lra_lit = lra_.cb_add_reason_clause_lit(lit);
        if (lra_lit != 0) return lra_lit;
        return euf_.cb_add_reason_clause_lit(lit);
    }

private:
    enum class Serving { None, Euf, Lra };
    llm2smt::EufSolver& euf_;
    llm2smt::lra::LraSolver& lra_;
    mutable std::vector<int> observed_cache_;
    Serving serving_ = Serving::None;
    Serving reason_serving_ = Serving::None;
};

int main(int argc, char** argv) {
    g_start_time = std::chrono::steady_clock::now();
    std::signal(SIGTERM, sigterm_handler);
    using namespace llm2smt;
    using namespace smt2parser;

    CLI::App app{"llm2smt — QF_EUF SMT solver"};
    app.set_version_flag("--version", []() -> std::string {
        std::string v;
        v += "llm2smt " LLM2SMT_VERSION " (" LLM2SMT_GIT_DESCRIBE ")\n";
        v += "Git commit: " LLM2SMT_GIT_COMMIT "\n";
        v += "Build:  " LLM2SMT_BUILD_TYPE "\n";
        v += "SAT:    " LLM2SMT_SAT_SOLVER " ";
        v += CaDiCaLSolver::version();
        v += " (";
        v += CaDiCaLSolver::signature();
        v += ")";
#ifndef NDEBUG
        v += "\nAssertions: enabled";
#endif
        return v;
    }());

    std::string input_file;
    app.add_option("file", input_file, "SMT2 input file (reads stdin if omitted)")
       ->check(CLI::ExistingFile);
    bool quiet = false;
    app.add_flag("-q,--quiet", quiet, "Suppress version/provenance diagnostics");

    PreprocOptions opts;
    app.add_option("--preprocess-passes", opts.passes,
                   "Number of simplifier passes (0 = disabled)")
       ->check(CLI::NonNegativeNumber);
    app.add_flag("!--no-nary", opts.nary,
                 "Build left-nested binary AND/OR nodes instead of n-ary");
    app.add_flag("!--no-flatten", opts.flatten,
                 "Disable And/Or flattening in the simplifier");
    auto* nnf_flag = app.add_flag("--nnf", opts.nnf,
                 "Convert to Negation Normal Form before encoding");
    app.add_flag("--nnf-memo", opts.nnf_memo,
                 "Memoize NNF traversal (helps on DAG-heavy inputs)")
       ->needs(nnf_flag);
    auto* proof_flag = app.add_option("--proof", opts.proof_file,
                   "Write Lean 4 UNSAT proof to this file (QF_UF only)");
    app.add_flag("--proof-minimize", opts.proof_minimize,
                 "Remove unnecessary theory lemmas via UNSAT-core extraction (requires --proof)")
       ->needs(proof_flag);
    app.add_flag("--eq-bridge", opts.eq_bridge,
                 "Add common EUF consequences of disjunction branches (eliminates diamond-like exponential blowup)");
    app.add_flag("!--no-finite-domain-amo", opts.finite_domain_amo,
                 "Disable SAT at-most-one clauses inferred from top-level distinct endpoints");
    app.add_flag("!--no-finite-domain-eqdefs", opts.finite_domain_eq_defs,
                 "Disable SAT definitions for equalities between finite-domain terms");
    app.add_flag("!--no-theory-prop", opts.theory_propagation,
                 "Disable EUF/LRA theory propagation (ablation: conflict detection is preserved)");
    app.add_option("--prop-interval", opts.prop_interval,
                   "Process EUF propagation candidates every N discovery calls; adaptive doubling up to 1024 (default 32)")
       ->check(CLI::PositiveNumber);
    app.add_option("--prop-assign-threshold", opts.prop_assign_threshold,
                   "Skip EUF propagation candidate processing when (assigned vars)/(total vars) >= THRESHOLD; 0=guard disabled, 1=skip only when all vars assigned (default 0.25)")
       ->check(CLI::Range(0.0, 1.0));
    app.add_option("--prop-delivery-budget", opts.prop_delivery_budget,
                   "Permanently stop EUF propagation discovery after delivering this many theory literals (default 1000; 0=unlimited)")
       ->check(CLI::NonNegativeNumber);
    app.add_flag("--lra-print-conflict-size", opts.lra_print_conflict_size,
                 "Debug: print the minimized LRA conflict clause size after UNSAT QF_LRA checks");
    app.add_flag("!--no-lra-bool-cache", opts.lra_bool_cache,
                 "Disable QF_LRA Boolean compound SAT-literal reuse");
    app.add_flag("!--no-lra-bool-cache-and", opts.lra_bool_cache_and,
                 "Disable QF_LRA Boolean AND SAT-literal reuse");
    app.add_flag("!--no-lra-bool-cache-or", opts.lra_bool_cache_or,
                 "Disable QF_LRA Boolean OR SAT-literal reuse");
    app.add_flag("!--no-lra-bool-cache-eq", opts.lra_bool_cache_eq,
                 "Disable QF_LRA Boolean equality/distinct SAT-literal reuse");
    app.add_flag("!--no-lra-term-cache", opts.lra_term_cache,
                 "Disable QF_LRA arithmetic term normalization reuse");
    app.add_flag("!--no-lra-eq-elim", opts.lra_eq_elim,
                 "Disable QF_LRA top-level linear equality elimination");
    app.add_option("--lra-eq-elim-limit", opts.lra_eq_elim_limit,
                   "Maximum top-level QF_LRA equality rows processed for elimination")
       ->check(CLI::NonNegativeNumber);
    app.add_flag("!--no-lra-const-simplify", opts.lra_const_simplify,
                 "Disable QF_LRA constant/connective simplification before SAT/LRA encoding");
    app.add_flag("!--no-lra-finite-domain-bounds", opts.lra_finite_domain_bounds,
                 "Disable QF_LRA SAT links between finite-domain choices and simple bounds");
    app.add_flag("--lra-finite-domain-eqdefs", opts.lra_finite_domain_eq_defs,
                 "Enable experimental QF_LRA SAT definitions for variable equalities over finite-domain choices");
    app.add_flag("--lra-finite-domain-branch", opts.lra_finite_domain_branch,
                 "Enable experimental QF_LRA finite-domain choice literals as SAT decision hints");
    app.add_flag("!--no-lra-incremental-prop-scan", opts.lra_incremental_prop_scan,
                 "Disable dirty-variable scanning for QF_LRA propagation discovery");
    app.add_flag("--lra-row-bound-prop", opts.lra_row_bound_prop,
                 "Enable QF_LRA propagation from tableau row-derived bounds");
    app.add_flag("!--no-lra-row-bound-prop", opts.lra_row_bound_prop,
                 "Disable QF_LRA row-bound propagation");
    app.add_flag("--lra-row-bound-dirty-scan", opts.lra_row_bound_dirty_scan,
                 "Restrict QF_LRA row-bound propagation to rows touching recently changed bounds");
    app.add_option("--lra-row-bound-prop-budget", opts.lra_row_bound_prop_budget,
                   "Maximum QF_LRA row-bound propagation candidates per discovery (0 = unlimited)");

    app.add_flag("--stats", g_print_stats, "Print solver statistics to stderr after solving");

    CLI11_PARSE(app, argc, argv);

    if (!quiet) {
        std::cerr << "llm2smt " << LLM2SMT_VERSION
                  << " git " << LLM2SMT_GIT_COMMIT
                  << " sat " << LLM2SMT_SAT_SOLVER << " "
                  << CaDiCaLSolver::version()
                  << " (" << CaDiCaLSolver::signature() << ")\n";
    }

    try {
        std::ifstream file;
        std::unique_ptr<antlr4::ANTLRInputStream> input_stream;

        if (!input_file.empty()) {
            file.open(input_file);
            if (!file) {
                std::cerr << "Error: cannot open file " << input_file << "\n";
                return 1;
            }
            input_stream = std::make_unique<antlr4::ANTLRInputStream>(file);
        } else {
            input_stream = std::make_unique<antlr4::ANTLRInputStream>(std::cin);
        }

        Stats          stats;
        g_stats = &stats;
        std::atexit(print_stats_atexit);
        NodeManager    nm;
        // euf must be declared before sat so that sat is destroyed first.
        // CaDiCaL's destructor calls disconnect_external_propagator() which
        // triggers notify_backtrack() callbacks; if euf were already destroyed
        // at that point the callbacks would access freed memory.
        EufSolver      euf(nm, stats);
        lra::LraSolver lra(&stats);
        CombinedPropagator theory(euf, lra);
        CaDiCaLSolver  sat(&stats);
        sat.connect_propagator(theory);

        if (!opts.theory_propagation) {
            euf.set_propagation(false);
            lra.set_propagation(false);
        }
        lra.set_incremental_prop_scan(opts.lra_incremental_prop_scan);
        lra.set_row_bound_propagation(opts.lra_row_bound_prop);
        lra.set_row_bound_dirty_scan(opts.lra_row_bound_dirty_scan);
        lra.set_row_bound_propagation_budget(opts.lra_row_bound_prop_budget);
        euf.set_prop_interval(opts.prop_interval);
        euf.set_prop_assign_threshold(opts.prop_assign_threshold);
        euf.set_prop_delivery_budget(opts.prop_delivery_budget);

        const bool proof_mode = !opts.proof_file.empty();
        if (proof_mode) {
            euf.enable_proof_recording();
            if (opts.proof_minimize)
                sat.enable_clause_recording();
        }

        SmtContext ctx(nm, euf, lra, sat);

        SMTLIBv2Lexer  lexer(input_stream.get());
        antlr4::CommonTokenStream tokens(&lexer);
        SMTLIBv2Parser parser(&tokens);

        auto* tree = parser.start();
        Smt2Visitor visitor(ctx, opts, stats);
        visitor.visitStart(tree);

        if (proof_mode && visitor.last_result() == SolveResult::UNSAT) {
            const auto& conflicts_raw = euf.proof_conflicts();
            std::vector<std::vector<int>> conflicts;
            if (opts.proof_minimize)
                conflicts = minimize_proof_conflicts(sat.recorded_clauses(), conflicts_raw);
            else
                conflicts = conflicts_raw;

            std::ofstream proof_out(opts.proof_file);
            LeanEmitter emitter;
            emitter.emit(proof_out, ctx, visitor.proof_fmls(), conflicts);
        }

        if (g_print_stats) {
            auto now = std::chrono::steady_clock::now();
            stats.total_ms = static_cast<uint64_t>(
                std::chrono::duration_cast<std::chrono::milliseconds>(now - g_start_time).count());
            stats.print(std::cerr);
            g_stats = nullptr;  // prevent double-print from atexit handler
        }

        return 0;

    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << "\n";
        return 1;
    }
}
