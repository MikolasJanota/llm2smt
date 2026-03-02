#include <csignal>
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

static void sigterm_handler(int) {
    // write() is async-signal-safe; std::cout is not (buffered, not safe in handlers).
    // _Exit skips destructors and stdio flushing, but write() bypasses the buffer.
    write(STDOUT_FILENO, "unknown\n", 8);
    _Exit(0);
}

int main(int argc, char** argv) {
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
    app.add_flag("!--no-flatten", opts.flatten,
                 "Disable And/Or flattening in the simplifier");
    auto* nnf_flag = app.add_flag("--nnf", opts.nnf,
                 "Convert to Negation Normal Form before encoding");
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

    bool print_stats = false;
    app.add_flag("--stats", print_stats, "Print solver statistics to stderr after solving");

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
        NodeManager    nm;
        // euf must be declared before sat so that sat is destroyed first.
        // CaDiCaL's destructor calls disconnect_external_propagator() which
        // triggers notify_backtrack() callbacks; if euf were already destroyed
        // at that point the callbacks would access freed memory.
        EufSolver      euf(nm, stats);
        CaDiCaLSolver  sat;
        sat.connect_propagator(euf);

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

        if (print_stats) stats.print(std::cerr);

        return 0;

    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << "\n";
        return 1;
    }
}
