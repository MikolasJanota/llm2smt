#include <csignal>
#include <fstream>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <unistd.h>

#include "antlr4-runtime.h"
#include "SMTLIBv2Lexer.h"
#include "SMTLIBv2Parser.h"

#include "core/node_manager.h"
#include "theories/euf/euf_solver.h"
#include "parser/smt_context.h"
#include "parser/smt2_visitor.h"
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

    int preprocess_passes = 0;
    int file_arg = -1;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--preprocess-passes" && i + 1 < argc)
            preprocess_passes = std::stoi(argv[++i]);
        else if (file_arg < 0 && a[0] != '-')
            file_arg = i;
    }

    if (argc >= 2 && std::string(argv[1]) == "--version") {
        std::cout << "llm2smt " << LLM2SMT_VERSION
                  << " (" << LLM2SMT_GIT_DESCRIBE << ")\n"
                  << "Build:  " << LLM2SMT_BUILD_TYPE << "\n"
                  << "SAT:    " << LLM2SMT_SAT_SOLVER << "\n";
#ifndef NDEBUG
        std::cout << "Assertions: enabled\n";
#endif
        return 0;
    }

    try {
        std::ifstream file;
        std::unique_ptr<antlr4::ANTLRInputStream> input_stream;

        if (file_arg >= 0) {
            file.open(argv[file_arg]);
            if (!file) {
                std::cerr << "Error: cannot open file " << argv[file_arg] << "\n";
                return 1;
            }
            input_stream = std::make_unique<antlr4::ANTLRInputStream>(file);
        } else {
            input_stream = std::make_unique<antlr4::ANTLRInputStream>(std::cin);
        }

        NodeManager    nm;
        // euf must be declared before sat so that sat is destroyed first.
        // CaDiCaL's destructor calls disconnect_external_propagator() which
        // triggers notify_backtrack() callbacks; if euf were already destroyed
        // at that point the callbacks would access freed memory.
        EufSolver      euf(nm);
        CaDiCaLSolver  sat;
        sat.connect_propagator(euf);

        SmtContext ctx(nm, euf, sat);

        SMTLIBv2Lexer  lexer(input_stream.get());
        antlr4::CommonTokenStream tokens(&lexer);
        SMTLIBv2Parser parser(&tokens);

        auto* tree = parser.start();
        Smt2Visitor visitor(ctx, preprocess_passes);
        visitor.visitStart(tree);

        return 0;

    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << "\n";
        return 1;
    }
}
