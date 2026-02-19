include(FetchContent)

# ANTLR4 complete JAR (for code generation at configure/build time)
FetchContent_Declare(
  antlr4_jar
  URL https://www.antlr.org/download/antlr-4.13.2-complete.jar
  DOWNLOAD_NO_EXTRACT TRUE
)
FetchContent_MakeAvailable(antlr4_jar)
# The jar lands in the antlr4_jar_SOURCE_DIR (actually the download dir)
FetchContent_GetProperties(antlr4_jar SOURCE_DIR antlr4_jar_SOURCE_DIR)
set(ANTLR4_JAR_PATH "${antlr4_jar_SOURCE_DIR}/antlr-4.13.2-complete.jar" CACHE FILEPATH "Path to ANTLR4 JAR")

# ANTLR4 C++ runtime
set(ANTLR4_INSTALL OFF CACHE BOOL "" FORCE)
set(ANTLR_BUILD_CPP_TESTS OFF CACHE BOOL "" FORCE)
FetchContent_Declare(
  antlr4_runtime
  GIT_REPOSITORY https://github.com/antlr/antlr4.git
  GIT_TAG        4.13.2
  SOURCE_SUBDIR  runtime/Cpp
)
FetchContent_MakeAvailable(antlr4_runtime)

# smtlibv2-grammar (julianthome/smtlibv2-grammar)
FetchContent_Declare(
  smtlibv2_grammar
  GIT_REPOSITORY https://github.com/julianthome/smtlibv2-grammar.git
  GIT_TAG        master
)
FetchContent_GetProperties(smtlibv2_grammar)
if(NOT smtlibv2_grammar_POPULATED)
  FetchContent_Populate(smtlibv2_grammar)
endif()
set(SMTLIBV2_GRAMMAR_FILE
  "${smtlibv2_grammar_SOURCE_DIR}/src/main/resources/SMTLIBv2.g4"
  CACHE FILEPATH "Path to SMTLIBv2.g4 grammar file"
)

# GoogleTest
FetchContent_Declare(
  googletest
  GIT_REPOSITORY https://github.com/google/googletest.git
  GIT_TAG        v1.14.0
)
set(INSTALL_GTEST OFF CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(googletest)
