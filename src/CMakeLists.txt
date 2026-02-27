add_subdirectory(core)
add_subdirectory(sat)
add_subdirectory(theories/euf)
add_subdirectory(preprocessor)
add_subdirectory(parser)
add_subdirectory(proof)

add_executable(llm2smt main.cpp)
target_link_libraries(llm2smt
  PRIVATE
    core
    sat
    euf
    preprocessor
    smt_parser
    proof
    CLI11::CLI11
)
target_include_directories(llm2smt PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
target_compile_definitions(llm2smt PRIVATE
    LLM2SMT_VERSION="${PROJECT_VERSION}"
    LLM2SMT_GIT_DESCRIBE="${LLM2SMT_GIT_DESCRIBE}"
    LLM2SMT_BUILD_TYPE="$<CONFIG>"
    LLM2SMT_SAT_SOLVER="CaDiCaL"
)
