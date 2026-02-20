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
#include "sat/cadical_solver.h"

int main(int argc, char** argv) {
    using namespace llm2smt;
    using namespace smt2parser;

    if (argc >= 2 && std::string(argv[1]) == "--version") {
        std::cout << "llm2smt " << LLM2SMT_VERSION << "\n"
                  << "Build:  " << LLM2SMT_BUILD_TYPE << "\n"
                  << "SAT:    " << LLM2SMT_SAT_SOLVER << "\n";
#ifndef NDEBUG
        std::cout << "Assertions: enabled\n";
#endif
        return 0;
    }

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

        NodeManager    nm;
        CaDiCaLSolver  sat;
        EufSolver      euf(nm);
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
