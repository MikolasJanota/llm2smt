# Generate ANTLR4 parser files
set(ANTLR4_OUTPUT_DIR ${CMAKE_CURRENT_BINARY_DIR}/antlr4_generated)
file(MAKE_DIRECTORY ${ANTLR4_OUTPUT_DIR})

add_antlr4_target(SMTLIBv2 ${SMTLIBV2_GRAMMAR_FILE} ${ANTLR4_OUTPUT_DIR} smt2parser)

add_library(smt_parser STATIC
  smt2_visitor.cpp
  ${ANTLR4_SMTLIBv2_GENERATED_SRCS}
)

target_include_directories(smt_parser
  PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}/..
    ${CMAKE_CURRENT_SOURCE_DIR}
    ${ANTLR4_OUTPUT_DIR}
)

# antlr4-runtime target name varies by version; try both
if(TARGET antlr4_static)
  target_link_libraries(smt_parser PUBLIC core euf antlr4_static)
elseif(TARGET antlr4-runtime)
  target_link_libraries(smt_parser PUBLIC core euf antlr4-runtime)
else()
  message(FATAL_ERROR "Could not find antlr4 runtime target")
endif()

target_compile_features(smt_parser PUBLIC cxx_std_20)
