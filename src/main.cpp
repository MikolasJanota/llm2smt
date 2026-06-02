#include <chrono>
#include <csignal>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <unistd.h>

#include <CLI/CLI.hpp>

#include "antlr4-runtime.h"
#include "SMTLIBv2Lexer.h"
#include "SMTLIBv2Parser.h"

#include "core/node_manager.h"
#include "core/stats.h"
#include "theories/euf/euf_solver.h"
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

int main(int argc, char** argv) {
    g_start_time = std::chrono::steady_clock::now();
    std::signal(SIGTERM, sigterm_handler);
    using namespace llm2smt;
    using namespace smt2parser;

    CLI::App app{"llm2smt — QF_EUF SMT solver"};
    app.set_version_flag("--version", []() -> std::string {
        std::string v;
        v += "llm2smt " LLM2SMT_VERSION " (" LLM2SMT_GIT_DESCRIBE ")\n";
        v += "Build:  " LLM2SMT_BUILD_TYPE "\n";
        v += "SAT:    " LLM2SMT_SAT_SOLVER;
#ifndef NDEBUG
        v += "\nAssertions: enabled";
#endif
        return v;
    }());

    std::string input_file;
    app.add_option("file", input_file, "SMT2 input file (reads stdin if omitted)")
       ->check(CLI::ExistingFile);

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
    app.add_flag("--selectors", opts.selectors,
                 "[DEPRECATED] Use selector variable technique for Or-with-compound-disjuncts encoding")
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
                 "Disable EUF theory propagation (ablation: conflict detection is preserved)");
    app.add_option("--prop-interval", opts.prop_interval,
                   "Process EUF propagation candidates every N discovery calls; adaptive doubling up to 1024 (default 32)")
       ->check(CLI::PositiveNumber);
    app.add_option("--prop-assign-threshold", opts.prop_assign_threshold,
                   "Skip EUF propagation candidate processing when (assigned vars)/(total vars) >= THRESHOLD; 0=guard disabled, 1=skip only when all vars assigned (default 0.25)")
       ->check(CLI::Range(0.0, 1.0));
    app.add_option("--prop-delivery-budget", opts.prop_delivery_budget,
                   "Permanently stop EUF propagation discovery after delivering this many theory literals (default 1000; 0=unlimited)")
       ->check(CLI::NonNegativeNumber);

    app.add_flag("--stats", g_print_stats, "Print solver statistics to stderr after solving");

    CLI11_PARSE(app, argc, argv);

    if (opts.selectors)
        std::cerr << "Warning: --selectors is deprecated and may be removed in a future version.\n";

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
        CaDiCaLSolver  sat;
        sat.connect_propagator(euf);

        if (!opts.theory_propagation)
            euf.set_propagation(false);
        euf.set_prop_interval(opts.prop_interval);
        euf.set_prop_assign_threshold(opts.prop_assign_threshold);
        euf.set_prop_delivery_budget(opts.prop_delivery_budget);

        const bool proof_mode = !opts.proof_file.empty();
        if (proof_mode) {
            euf.enable_proof_recording();
            if (opts.proof_minimize)
                sat.enable_clause_recording();
        }

        SmtContext ctx(nm, euf, sat);

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
