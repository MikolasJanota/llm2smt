cmake_minimum_required(VERSION 3.25)
project(llm2smt VERSION 0.2.2 LANGUAGES CXX)

# Capture git description (tag + commit hash) at configure time.
# Result: "v0.2.0" on a tagged commit, "v0.2.0-N-gHASH[-dirty]" otherwise.
find_package(Git QUIET)
if(GIT_FOUND)
    execute_process(
        COMMAND ${GIT_EXECUTABLE} describe --tags --always --dirty
        WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
        OUTPUT_VARIABLE LLM2SMT_GIT_DESCRIBE
        OUTPUT_STRIP_TRAILING_WHITESPACE
        ERROR_QUIET
    )
else()
    set(LLM2SMT_GIT_DESCRIBE "unknown")
endif()
message(STATUS "llm2smt version: ${PROJECT_VERSION}  git: ${LLM2SMT_GIT_DESCRIBE}")

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# Export compile_commands.json for IDE/tooling support
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# AddressSanitizer + UBSan: enabled by default for Debug builds.
# Override with -DLLM2SMT_ASAN=OFF if you need a clean Debug build.
if(CMAKE_BUILD_TYPE STREQUAL "Debug")
    option(LLM2SMT_ASAN "Enable AddressSanitizer + UBSan" ON)
else()
    option(LLM2SMT_ASAN "Enable AddressSanitizer + UBSan" OFF)
endif()
if(LLM2SMT_ASAN)
    message(STATUS "AddressSanitizer + UBSan: ON")
    add_compile_options(-fsanitize=address,undefined -fno-omit-frame-pointer)
    add_link_options(-fsanitize=address,undefined)
endif()

# Place all executables under <build>/bin/
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

# Helper function must be defined BEFORE add_subdirectory calls
find_package(Java COMPONENTS Runtime QUIET)

function(add_antlr4_target name grammar_file output_dir namespace)
  if(NOT Java_JAVA_EXECUTABLE)
    message(FATAL_ERROR "Java runtime not found. Required for ANTLR4 code generation.")
  endif()

  set(ANTLR4_GENERATED_SRCS
    ${output_dir}/${name}Lexer.cpp
    ${output_dir}/${name}Lexer.h
    ${output_dir}/${name}Parser.cpp
    ${output_dir}/${name}Parser.h
    ${output_dir}/${name}BaseVisitor.h
    ${output_dir}/${name}Visitor.h
  )

  add_custom_command(
    OUTPUT ${ANTLR4_GENERATED_SRCS}
    COMMAND ${Java_JAVA_EXECUTABLE} -jar ${ANTLR4_JAR_PATH}
            -Dlanguage=Cpp
            -visitor
            -package ${namespace}
            -o ${output_dir}
            ${grammar_file}
    DEPENDS ${grammar_file}
    COMMENT "Running ANTLR4 on ${grammar_file}"
  )

  set(ANTLR4_${name}_GENERATED_SRCS ${ANTLR4_GENERATED_SRCS} PARENT_SCOPE)
endfunction()

include(cmake/FetchDependencies.cmake)

enable_testing()
add_subdirectory(src)
add_subdirectory(tests)
