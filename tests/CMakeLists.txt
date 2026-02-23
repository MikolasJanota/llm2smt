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

# Like add_smt2_test but runs with --preprocess-passes 1.
function(add_smt2_test_preproc name file expected)
    add_test(
        NAME "smt2/${name}"
        COMMAND $<TARGET_FILE:llm2smt> --preprocess-passes 1
                "${CMAKE_CURRENT_SOURCE_DIR}/smt2/${file}"
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

# Core theory — true / false
# t09: (assert true) ∧ (assert (not false))  →  sat
add_smt2_test(true_false_sat          t09_true_false.smt2            sat)
# t10: (assert false)                          →  unsat
add_smt2_test(false_unsat             t10_false_unsat.smt2           unsat)

# Core theory — => (implication)
# t11: (=> a=b b=c) ∧ a=b ∧ ¬(a=c)          →  unsat  (transitivity via =>)
add_smt2_test(implies_unsat           t11_implies.smt2               unsat)
# t12: (=> a=b b=a) alone                     →  sat   (trivially true)
add_smt2_test(implies_sat             t12_implies_sat.smt2           sat)

# Core theory — xor
# t13: xor(P, P) = false                      →  unsat
add_smt2_test(xor_unsat               t13_xor.smt2                   unsat)
# t14: xor(P, ¬P) = true                      →  sat
add_smt2_test(xor_sat                 t14_xor_sat.smt2               sat)

# Core theory — ite
# t15: ite(true, P, ¬P) = P  ∧  ¬P           →  unsat
add_smt2_test(ite_unsat               t15_ite.smt2                   unsat)
# t16: ite(false, P, true) = true             →  sat
add_smt2_test(ite_sat                 t16_ite_sat.smt2               sat)

# Parsing regressions — annotation syntax, Bool equality, U-sorted ite
# t17: (! term :named label) annotation stripped correctly → unsat
add_smt2_test(named_annotation_unsat  t17_named_annotation.smt2      unsat)
# t18: (! term :named label) annotation — sat case
add_smt2_test(named_annotation_sat    t18_named_annotation_sat.smt2  sat)
# t19: (= Bool Bool) biconditional — p=(not p) → unsat
add_smt2_test(bool_eq_unsat           t19_bool_eq_biconditional.smt2 unsat)
# t20: (= Bool Bool) biconditional — p=q ∧ p → sat
add_smt2_test(bool_eq_sat             t20_bool_eq_sat.smt2           sat)
# t21: U-sorted ite encoded as conditional EUF equality → unsat
add_smt2_test(ite_usort_unsat         t21_ite_usort.smt2             unsat)
# t22: U-sorted ite — satisfiable case
add_smt2_test(ite_usort_sat           t22_ite_usort_sat.smt2         sat)
# t23: Bool-sorted UF argument — SAT assignment must be bridged to EUF → unsat
add_smt2_test(bool_uf_arg_unsat       t23_bool_uf_arg_unsat.smt2     unsat)
# t24: Bool-sorted UF argument — satisfiable case (p=true, q=false → f(p)≠f(q))
add_smt2_test(bool_uf_arg_sat         t24_bool_uf_arg_sat.smt2       sat)
# t25: Regression: Bool-as-UF-arg mutual exclusivity (link_bool_term_to_euf fix)
add_smt2_test(bool_uf_mutual_excl     t25_bool_uf_mutual_exclusivity.smt2  sat)
# t26: Regression: proof-forest incomplete explanation via representative (from_node fix)
add_smt2_test(explain_via_repr        t26_explain_via_representative.smt2  sat)
# t27: Regression: heap-use-after-free in Flattener::do_flatten (NodeData ref invalidated by nm_.mk_const)
add_smt2_test(flatten_uaf             t27_flatten_uaf.smt2                 sat)
# t28: Regression: Bool-UF result nodes not registered in EUF when only in Bool-eq context (eval_lit path)
add_smt2_test(bool_uf_result_cong     t28_bool_uf_result_congruence.smt2   unsat)
# t29: Regression: permanent equality optimization — forced (= a b) merged in CC without SAT variable
add_smt2_test_preproc(preproc_perm_eq_cong   t29_preproc_perm_eq_congruence.smt2  unsat)
# t30: Regression: permanent equality with transitivity — two forced equalities imply a third
add_smt2_test_preproc(preproc_perm_eq_trans  t30_preproc_perm_eq_transitive.smt2  unsat)

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

add_executable(test_preprocessor test_preprocessor.cpp)
target_link_libraries(test_preprocessor PRIVATE preprocessor GTest::gtest_main)
target_include_directories(test_preprocessor PRIVATE ${CMAKE_SOURCE_DIR}/src)
gtest_discover_tests(test_preprocessor)
