include(GoogleTest)

# ── End-to-end SMT2 regression tests ─────────────────────────────────────────
# Each test runs llm2smt on an .smt2 file and checks the output line.
function(add_smt2_test name file expected)
    add_test(
        NAME "smt2/${name}"
        COMMAND $<TARGET_FILE:llm2smt> "${CMAKE_CURRENT_SOURCE_DIR}/smt2/${file}"
    )
    set_tests_properties("smt2/${name}" PROPERTIES
        PASS_REGULAR_EXPRESSION "^${expected}"
    )
endfunction()

# t01: a=b  ∧  a≠b  →  unsat  (direct contradiction)
add_smt2_test(unsat_direct          t01_unsat_direct.smt2          unsat)
# t02: a=b  ∧  b=c  ∧  a≠c   →  unsat  (transitivity)
add_smt2_test(unsat_transitive      t02_unsat_transitive.smt2      unsat)
# t03: a=b  ∧  f(a)≠f(b)      →  unsat  (congruence)
add_smt2_test(unsat_congruence      t03_unsat_congruence.smt2      unsat)
# t04: a=b                     →  sat   (trivially satisfiable)
add_smt2_test(sat_trivial           t04_sat_trivial.smt2           sat)
# t05: a≠b  ∧  b≠c            →  sat   (two disequalities, no conflict)
add_smt2_test(sat_two_diseq         t05_sat_two_diseq.smt2         sat)
# t06: a=b  ∧  b=c  ∧  f(a)=d  ∧  f(c)≠d  →  unsat  (transitive congruence)
add_smt2_test(unsat_trans_congruence t06_unsat_trans_congruence.smt2 unsat)
# t07: a=b  ∧  f(a)=f(b)      →  sat   (consistent equalities)
add_smt2_test(sat_no_conflict       t07_sat_no_conflict.smt2       sat)
# t08: a=b  ∧  c=d  ∧  g(a,c)≠g(b,d) →  unsat  (binary congruence)
add_smt2_test(unsat_binary_congruence t08_unsat_binary_congruence.smt2 unsat)

# ── Unit test binaries ────────────────────────────────────────────────────────
add_executable(test_node_manager test_node_manager.cpp)
target_link_libraries(test_node_manager PRIVATE core GTest::gtest_main)
target_include_directories(test_node_manager PRIVATE ${CMAKE_SOURCE_DIR}/src)
gtest_discover_tests(test_node_manager)

add_executable(test_cc test_cc.cpp)
target_link_libraries(test_cc PRIVATE euf GTest::gtest_main)
target_include_directories(test_cc PRIVATE ${CMAKE_SOURCE_DIR}/src)
gtest_discover_tests(test_cc)

add_executable(test_euf_solver test_euf_solver.cpp)
target_link_libraries(test_euf_solver PRIVATE euf GTest::gtest_main)
target_include_directories(test_euf_solver PRIVATE ${CMAKE_SOURCE_DIR}/src)
gtest_discover_tests(test_euf_solver)
