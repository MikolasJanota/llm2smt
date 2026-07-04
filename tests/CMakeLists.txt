include(GoogleTest)

# ── End-to-end SMT2 regression tests ─────────────────────────────────────────
# Each test runs llm2smt on an .smt2 file and checks the output line.
function(add_smt2_test name file expected)
    add_test(
        NAME "smt2/${name}"
        COMMAND $<TARGET_FILE:llm2smt> --quiet
                "${CMAKE_CURRENT_SOURCE_DIR}/smt2/${file}"
    )
    set_tests_properties("smt2/${name}" PROPERTIES
        PASS_REGULAR_EXPRESSION "^${expected}"
    )
endfunction()

# Like add_smt2_test but runs with --preprocess-passes 1.
function(add_smt2_test_preproc name file expected)
    add_test(
        NAME "smt2/${name}"
        COMMAND $<TARGET_FILE:llm2smt> --quiet --preprocess-passes 1
                "${CMAKE_CURRENT_SOURCE_DIR}/smt2/${file}"
    )
    set_tests_properties("smt2/${name}" PROPERTIES
        PASS_REGULAR_EXPRESSION "^${expected}"
    )
endfunction()

# Like add_smt2_test but runs with --preprocess-passes 1 --nnf.
function(add_smt2_test_nnf name file expected)
    add_test(
        NAME "smt2/${name}"
        COMMAND $<TARGET_FILE:llm2smt> --quiet --preprocess-passes 1 --nnf
                "${CMAKE_CURRENT_SOURCE_DIR}/smt2/${file}"
    )
    set_tests_properties("smt2/${name}" PROPERTIES
        PASS_REGULAR_EXPRESSION "^${expected}"
    )
endfunction()

# Like add_smt2_test but runs with --eq-bridge.
function(add_smt2_test_eq_bridge name file expected)
    add_test(
        NAME "smt2/${name}"
        COMMAND $<TARGET_FILE:llm2smt> --quiet --eq-bridge
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

# QF_LRA regressions
add_smt2_test(lra_bound_conflict      lra01_bound_conflict.smt2      unsat)
add_smt2_test(lra_linear_eq_unsat     lra02_linear_eq_unsat.smt2     unsat)
add_smt2_test(lra_strict_unsat        lra03_strict_unsat.smt2        unsat)
add_smt2_test(lra_diseq_sat           lra04_diseq_sat.smt2           sat)
add_smt2_test(lra_arith_ite_sat       lra05_arith_ite_sat.smt2       sat)
add_smt2_test(lra_large_rational_sat  lra06_large_rational_sat.smt2  sat)
add_smt2_test(lra_false_equality_unsat lra07_false_equality_unsat.smt2 unsat)
add_smt2_test(lra_const_fold_unsat    lra10_const_fold_unsat.smt2    unsat)
add_smt2_test(lra_nary_distinct_unsat lra11_nary_distinct_unsat.smt2 unsat)
add_smt2_test(lra_eq_elim_triangular  lra15_eq_elim_triangular.smt2  unsat)
add_smt2_test(lra_eq_elim_inconsistent lra16_eq_elim_inconsistent.smt2 unsat)
add_smt2_test(lra_eq_elim_rational    lra17_eq_elim_rational.smt2    sat)
add_smt2_test(lra_eq_elim_guarded     lra18_eq_elim_guarded.smt2     sat)
add_smt2_test(lra_const_simplify_bool  lra21_const_simplify_bool.smt2  sat)
add_smt2_test(lra_arith_ite_const_cond lra22_arith_ite_const_cond.smt2 sat)
add_smt2_test(lra_arith_ite_equal_branches lra23_arith_ite_equal_branches.smt2 sat)
add_smt2_test(lra_bool_ite_const_branches lra24_bool_ite_const_branches.smt2 unsat)
add_smt2_test(lra_finite_domain_eqdefs lra25_finite_domain_eqdefs.smt2 sat)
add_smt2_test(lra_finite_domain_bounds lra26_finite_domain_bounds.smt2 sat)
add_smt2_test(lra_direct_eq_atom lra27_direct_eq_atom.smt2 sat)
add_smt2_test(lra_direct_eq_guarded_negation lra28_direct_eq_guarded_negation.smt2 sat)
add_smt2_test(lra_structural_bool_cache lra30_structural_bool_cache.smt2 sat)
add_smt2_test(lra_flatten_ite_chain lra31_flatten_ite_chain.smt2 sat)
add_test(
    NAME "smt2/lra_eq_elim_model"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet ${CMAKE_CURRENT_SOURCE_DIR}/smt2/lra19_eq_elim_model.smt2 | \
         tee ${CMAKE_BINARY_DIR}/lra19_model.out && \
         grep -q '^sat' ${CMAKE_BINARY_DIR}/lra19_model.out && \
         grep -q 'define-fun x' ${CMAKE_BINARY_DIR}/lra19_model.out && \
         grep -q '    5)' ${CMAKE_BINARY_DIR}/lra19_model.out && \
         grep -q 'define-fun y' ${CMAKE_BINARY_DIR}/lra19_model.out && \
         grep -q '    3)' ${CMAKE_BINARY_DIR}/lra19_model.out"
)
add_test(
    NAME "smt2/lra_eq_elim_cli_gate"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --stats \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/lra20_eq_elim_disabled_stats.smt2 \
         >/tmp/lra20_on.out 2>/tmp/lra20_on.err && \
         grep -q '^sat' /tmp/lra20_on.out && \
         grep -Eq 'lra\\.eq_elim_vars[[:space:]]+2$' /tmp/lra20_on.err && \
         $<TARGET_FILE:llm2smt> --quiet --stats --no-lra-eq-elim \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/lra20_eq_elim_disabled_stats.smt2 \
         >/tmp/lra20_off.out 2>/tmp/lra20_off.err && \
         grep -q '^sat' /tmp/lra20_off.out && \
         grep -Eq 'lra\\.eq_elim_vars[[:space:]]+0$' /tmp/lra20_off.err"
)
add_test(
    NAME "smt2/lra_simple_eq_amo_cli_gate"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --stats \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/lra12_simple_eq_amo.smt2 \
         >/tmp/lra12_on.out 2>/tmp/lra12_on.err && \
         grep -q '^sat' /tmp/lra12_on.out && \
         grep -q 'preproc.finite_domain_amo     3' /tmp/lra12_on.err && \
         $<TARGET_FILE:llm2smt> --quiet --stats --no-finite-domain-amo \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/lra12_simple_eq_amo.smt2 \
         >/tmp/lra12_off.out 2>/tmp/lra12_off.err && \
         grep -q '^sat' /tmp/lra12_off.out && \
         grep -q 'preproc.finite_domain_amo     0' /tmp/lra12_off.err"
)
add_test(
    NAME "smt2/lra_term_cache_ite_cli_gate"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --stats \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/lra13_term_cache_ite.smt2 \
         >/tmp/lra13_on.out 2>/tmp/lra13_on.err && \
         grep -q '^sat' /tmp/lra13_on.out && \
         grep -q 'lra.term_cache_hits' /tmp/lra13_on.err && \
         grep -q 'lra.ite_terms                 1' /tmp/lra13_on.err && \
         $<TARGET_FILE:llm2smt> --quiet --stats --no-lra-term-cache \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/lra13_term_cache_ite.smt2 \
         >/tmp/lra13_off.out 2>/tmp/lra13_off.err && \
         grep -q '^sat' /tmp/lra13_off.out && \
         grep -q 'lra.ite_terms                 2' /tmp/lra13_off.err"
)
add_test(
    NAME "smt2/lra_symmetric_eq_cache"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --stats --no-lra-eq-elim \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/lra14_symmetric_eq_cache.smt2 \
         >/tmp/lra14.out 2>/tmp/lra14.err && \
         grep -q '^sat' /tmp/lra14.out && \
         grep -Eq 'lra\\.eq_cache_hits[[:space:]]+1$' /tmp/lra14.err && \
         grep -Eq 'lra\\.atoms[[:space:]]+2$' /tmp/lra14.err"
)
add_test(
    NAME "smt2/lra_const_simplify_stats"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --stats --no-lra-eq-elim \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/lra21_const_simplify_bool.smt2 \
         >/tmp/lra21.out 2>/tmp/lra21.err && \
         grep -q '^sat' /tmp/lra21.out && \
         grep -Eq 'lra\\.const_bool_folds[[:space:]]+[1-9][0-9]*$' /tmp/lra21.err && \
         grep -Eq 'lra\\.const_arith_folds[[:space:]]+[1-9][0-9]*$' /tmp/lra21.err"
)
add_test(
    NAME "smt2/lra_const_simplify_ite_cli_gate"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --stats --no-lra-eq-elim \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/lra22_arith_ite_const_cond.smt2 \
         >/tmp/lra22_on.out 2>/tmp/lra22_on.err && \
         grep -q '^sat' /tmp/lra22_on.out && \
         grep -Eq 'lra\\.ite_terms[[:space:]]+0$' /tmp/lra22_on.err && \
         grep -Eq 'lra\\.ite_terms_simplified[[:space:]]+1$' /tmp/lra22_on.err && \
         $<TARGET_FILE:llm2smt> --quiet --stats --no-lra-eq-elim --no-lra-const-simplify --no-lra-ite-eq-direct \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/lra22_arith_ite_const_cond.smt2 \
         >/tmp/lra22_off.out 2>/tmp/lra22_off.err && \
         grep -q '^sat' /tmp/lra22_off.out && \
         grep -Eq 'lra\\.ite_terms[[:space:]]+1$' /tmp/lra22_off.err && \
         grep -Eq 'lra\\.ite_terms_simplified[[:space:]]+0$' /tmp/lra22_off.err"
)
add_test(
    NAME "smt2/lra_finite_domain_eqdefs_stats"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --stats --no-lra-eq-elim \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/lra25_finite_domain_eqdefs.smt2 \
         >/tmp/lra25_on.out 2>/tmp/lra25_on.err && \
         grep -q '^sat' /tmp/lra25_on.out && \
         grep -Eq 'preproc\\.finite_domain_eq_defs[[:space:]]+4$' /tmp/lra25_on.err && \
         $<TARGET_FILE:llm2smt> --quiet --stats --no-lra-eq-elim --no-lra-finite-domain-eqdefs \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/lra25_finite_domain_eqdefs.smt2 \
         >/tmp/lra25_off.out 2>/tmp/lra25_off.err && \
         grep -q '^sat' /tmp/lra25_off.out && \
         grep -Eq 'preproc\\.finite_domain_eq_defs[[:space:]]+0$' /tmp/lra25_off.err"
)
add_test(
    NAME "smt2/lra_finite_domain_bounds_stats"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --stats --no-lra-eq-elim \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/lra26_finite_domain_bounds.smt2 \
         >/tmp/lra26_on.out 2>/tmp/lra26_on.err && \
         grep -q '^sat' /tmp/lra26_on.out && \
         grep -Eq 'preproc\\.finite_domain_bounds[[:space:]]+[1-9][0-9]*$' /tmp/lra26_on.err && \
         $<TARGET_FILE:llm2smt> --quiet --stats --no-lra-eq-elim --no-lra-finite-domain-bounds \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/lra26_finite_domain_bounds.smt2 \
         >/tmp/lra26_off.out 2>/tmp/lra26_off.err && \
         grep -q '^sat' /tmp/lra26_off.out && \
         grep -Eq 'preproc\\.finite_domain_bounds[[:space:]]+0$' /tmp/lra26_off.err"
)
add_test(
    NAME "smt2/lra_direct_eq_atom_stats"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --stats --no-lra-eq-elim --lra-direct-eq-atoms \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/lra27_direct_eq_atom.smt2 \
         >/tmp/lra27_on.out 2>/tmp/lra27_on.err && \
         grep -q '^sat' /tmp/lra27_on.out && \
         grep -Eq 'arith-fixed-eqs[[:space:]]+1$' /tmp/lra27_on.err && \
         grep -Eq 'arith-offset-eqs[[:space:]]+1$' /tmp/lra27_on.err && \
         $<TARGET_FILE:llm2smt> --quiet --stats --no-lra-eq-elim \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/lra27_direct_eq_atom.smt2 \
         >/tmp/lra27_off.out 2>/tmp/lra27_off.err && \
         grep -q '^sat' /tmp/lra27_off.out && \
         grep -Eq 'arith-fixed-eqs[[:space:]]+0$' /tmp/lra27_off.err"
)
add_test(
    NAME "smt2/lra_direct_eq_guarded_negation_cli_gate"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --stats --lra-direct-eq-atoms \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/lra28_direct_eq_guarded_negation.smt2 \
         >/tmp/lra28.out 2>/tmp/lra28.err && \
         grep -q '^sat' /tmp/lra28.out"
)
add_test(
    NAME "smt2/lra_structural_bool_cache_stats"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --stats --no-lra-eq-elim \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/lra30_structural_bool_cache.smt2 \
         >/tmp/lra30.out 2>/tmp/lra30.err && \
         grep -q '^sat' /tmp/lra30.out && \
         grep -Eq 'lra\\.bool_cache_hits\\.or[[:space:]]+1$' /tmp/lra30.err"
)
add_test(
    NAME "smt2/lra_flatten_ite_chain_stats"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --stats --no-lra-ite-eq-direct \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/lra31_flatten_ite_chain.smt2 \
         >/tmp/lra31.out 2>/tmp/lra31.err && \
         grep -q '^sat' /tmp/lra31.out && \
         grep -Eq 'lra\\.ite_terms[[:space:]]+1$' /tmp/lra31.err && \
         $<TARGET_FILE:llm2smt> --quiet --stats \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/lra31_flatten_ite_chain.smt2 \
         >/tmp/lra31_direct.out 2>/tmp/lra31_direct.err && \
         grep -q '^sat' /tmp/lra31_direct.out && \
         grep -Eq 'lra\\.ite_terms[[:space:]]+0$' /tmp/lra31_direct.err && \
         grep -Eq 'lra\\.ite_terms_simplified[[:space:]]+2$' /tmp/lra31_direct.err"
)
add_test(
    NAME "smt2/lra_model_gt"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet ${CMAKE_CURRENT_SOURCE_DIR}/smt2/lra08_model_gt.smt2 | \
         tee ${CMAKE_BINARY_DIR}/lra08_model.out && \
         grep -q '^sat' ${CMAKE_BINARY_DIR}/lra08_model.out && \
         grep -q '    6)' ${CMAKE_BINARY_DIR}/lra08_model.out && \
         ! grep -q '    0)' ${CMAKE_BINARY_DIR}/lra08_model.out"
)
add_test(
    NAME "smt2/lra_min_conflict_size"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --lra-print-conflict-size \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/lra09_min_conflict.smt2 \
         > ${CMAKE_BINARY_DIR}/lra09.out 2> ${CMAKE_BINARY_DIR}/lra09.err && \
         grep -q '^unsat' ${CMAKE_BINARY_DIR}/lra09.out && \
         grep -q '^lra-conflict-size: 2$' ${CMAKE_BINARY_DIR}/lra09.err"
)

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
# t31: Regression: define-fun with quoted (space-containing) name used as assertion
add_smt2_test(define_fun_quoted      t31_define_fun_quoted.smt2       unsat)
# t32: Regression: define-fun with conjunction body — must be expanded structurally
add_smt2_test(define_fun_and_body    t32_define_fun_and_body.smt2     unsat)
# t33: Regression: compound Bool expression (and/or/not) as UF argument — unsat
add_smt2_test(bool_compound_uf_arg_unsat  t33_bool_compound_uf_arg_unsat.smt2  unsat)
# t34: Regression: compound Bool expression (or) as UF argument — sat case
add_smt2_test(bool_compound_uf_arg_sat   t34_bool_compound_uf_arg_sat.smt2    sat)
# t35: Regression: distinct with 3 args in formula position (eval_lit Tseitin path) — unsat
add_smt2_test(distinct_nary_formula_unsat  t35_distinct_nary_formula_unsat.smt2  unsat)
# t36: Regression: distinct with 3 args in formula position — sat case
add_smt2_test(distinct_nary_formula_sat   t36_distinct_nary_formula_sat.smt2    sat)
# t37: Regression: get-model for Bool-arg UF with compound Bool argument — model was wrong
#      (b0 (= c1 c2)) with c1=c2 gave b0(true)=b0(false) because __bool_fml_N not in node_to_lit
add_smt2_test(bool_compound_arg_model  t37_bool_compound_arg_model.smt2  sat)
# t38: Regression: get-model with (distinct ...) as Bool UF arg — bool_for polarity wrong
#      binary distinct returns -eq (negative lit); bool_for checked v>0 instead of v==stored
add_smt2_test(bool_distinct_arg_model  t38_bool_distinct_arg_model.smt2  sat)
# t39: NNF + preproc for Implies — unsat (simplifier can unit-propagate after NNF expansion)
add_smt2_test_nnf(nnf_implies_preproc_unsat  t39_nnf_implies_preproc_unsat.smt2  unsat)
# t40: NNF + preproc for Xor — xor(P,P) = false → unsat
add_smt2_test_nnf(nnf_xor_preproc_unsat      t40_nnf_xor_preproc_unsat.smt2      unsat)
# t41: NNF/preproc SAT — compound Or disjuncts; right disjunct (= b c) satisfiable
add_smt2_test_nnf(selector_or_sat           t41_selector_or_sat.smt2            sat)
# t42: NNF/preproc UNSAT — both alternatives require b=c, which is negated
add_smt2_test_nnf(selector_or_unsat         t42_selector_or_unsat.smt2          unsat)
# t43: Regression: crash in CaDiCaL analyze() when register_equality is called before
#      register_permanent_equality for the same pair — tautological conflict/reason clause
add_smt2_test_preproc(preproc_perm_eq_preregistered_crash  t43_preproc_perm_eq_preregistered_crash.smt2  sat)
# t44: --proof generates a Lean file with standalone theorem cl_k proved by grind
add_test(
    NAME "smt2/lean_proof_generates"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --proof ${CMAKE_BINARY_DIR}/t44_proof.lean \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/t44_lean_proof.smt2 && \
         grep -q '^theorem cl_' ${CMAKE_BINARY_DIR}/t44_proof.lean && \
         grep -q 'grind' ${CMAKE_BINARY_DIR}/t44_proof.lean"
)

# t51: --proof with U-sorted ite inlines (if c then a else b) and adds ite_pos/ite_neg clauses
add_test(
    NAME "smt2/ite_proof_generates"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --proof ${CMAKE_BINARY_DIR}/t51_proof.lean \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/t51_ite_proof.smt2 && \
         grep -q 'ite_pos_0' ${CMAKE_BINARY_DIR}/t51_proof.lean && \
         grep -q 'open Classical' ${CMAKE_BINARY_DIR}/t51_proof.lean"
)

# t52: --proof with --preprocess-passes 1 must not emit __flat_N proxy names in unit clauses.
#      Regression for bug where permanent_eq_pairs_ stored flat NodeIds instead of originals.
#      Unit clause cl_0 must use user-visible names (e.g. "(f b)") not "__flat_N".
add_test(
    NAME "smt2/preproc_perm_eq_proof_no_flat_nodes"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --preprocess-passes 1 --proof ${CMAKE_BINARY_DIR}/t52_proof.lean \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/t52_preproc_perm_eq_proof.smt2 && \
         grep -q 'have cl_0' ${CMAKE_BINARY_DIR}/t52_proof.lean && \
         grep -c '__flat_' ${CMAKE_BINARY_DIR}/t52_proof.lean | grep -q '^0\$'"
)

# t53: --proof with --eq-bridge: eq_bridge lemmas must be emitted for each disjunct of the
#      source Or formula, as simple implications decide(A) → decide(B) → decide(pa=pb).
#      Regression: previously emitted complex (Or-formula) → decide(x0=x1) which grind timed out on.
add_test(
    NAME "smt2/eq_bridge_proof_simple_bridge_lemmas"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --preprocess-passes 1 --eq-bridge \
         --proof ${CMAKE_BINARY_DIR}/t53_proof.lean \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/t53_eq_bridge_proof.smt2 && \
         grep -q 'eq_bridge_0' ${CMAKE_BINARY_DIR}/t53_proof.lean && \
         grep -q 'eq_bridge_1' ${CMAKE_BINARY_DIR}/t53_proof.lean"
)

# t54: --proof with --eq-bridge on 2-diamond chain (eq_diamond3): cl_0 must be a simple
#      2-hop EUF transitivity x0=x1 → x1=x2 → x0=x2.
#      Regression: previously emitted complex (Or ∧ Or) → x0=x2 which grind timed out on.
add_test(
    NAME "smt2/eq_bridge_proof_transitive_unit_clause"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --preprocess-passes 1 --eq-bridge \
         --proof ${CMAKE_BINARY_DIR}/t54_proof.lean \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/t54_eq_bridge_diamond3_proof.smt2 && \
         grep -q 'eq_bridge_' ${CMAKE_BINARY_DIR}/t54_proof.lean && \
         grep -q 'cl_0 :.*→.*→' ${CMAKE_BINARY_DIR}/t54_proof.lean"
)

# t56: --proof with non-unit conflict clause that has a permanent equality dep.
#      Regression: previously dropped perm deps for non-unit clauses, causing grind
#      to fail (it couldn't prove the clause without the premise a=b).
add_test(
    NAME "smt2/perm_dep_nonunit_clause_proof"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --preprocess-passes 1 --proof ${CMAKE_BINARY_DIR}/t56_proof.lean \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/t56_eq_bridge_perm_dep_nonunit.smt2 && \
         grep -q 'cl_0 :.*→.*∨' ${CMAKE_BINARY_DIR}/t56_proof.lean"
)

# t55: --proof with Bool-formula argument (b0 : Bool → U applied to (= c1 c2)).
#      Regression: previously emitted __bool_fml_N as undefined Lean identifier.
#      Must not contain __bool_fml_ in proof; must contain (c1 = c2) expansion.
add_test(
    NAME "smt2/bool_fml_arg_proof"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --proof ${CMAKE_BINARY_DIR}/t55_proof.lean \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/t55_bool_fml_arg_proof.smt2 && \
         ! grep -q '__bool_fml_' ${CMAKE_BINARY_DIR}/t55_proof.lean && \
         grep -q 'b0 (c1 = c2)' ${CMAKE_BINARY_DIR}/t55_proof.lean"
)

# t57: --proof where SAT assigns equalities before EUF can propagate them.
#      Regression: the CC explanation for already-assigned atoms included the
#      self-referential SAT edge, producing tautological reason clauses [+L,-L].
#      Trivial unit reason clauses with no perm deps must not be emitted (grind
#      cannot prove them in isolation without local hypothesis context).
add_test(
    NAME "smt2/proof_perm_dep_unit_assign"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --proof ${CMAKE_BINARY_DIR}/t57_proof.lean \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/t57_proof_perm_dep_unit_assign.smt2 && \
         ! grep -qP '^theorem cl_\\d+ : \\w+ = \\w+ := by grind' ${CMAKE_BINARY_DIR}/t57_proof.lean"
)

# t58: --proof with --preprocess-passes 1 where perm equalities (c0=c1, c3=c2) change
#      the canonical form of Eq atoms.  The proof snapshot must be taken AFTER the
#      simplifier runs so that atom representations match the SAT encoding.
#      Regression: previously the snapshot was taken before simplification, causing
#      c2=c0 in the proof — grind fails if the atom form mismatches the SAT encoding.
add_test(
    NAME "smt2/proof_preproc_snapshot_after_simp"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --preprocess-passes 1 \
         --proof ${CMAKE_BINARY_DIR}/t58_proof.lean \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/t58_proof_preproc_snapshot.smt2 && \
         ! grep -q 'decide (c2 = c0)' ${CMAKE_BINARY_DIR}/t58_proof.lean"
)

# t59: --proof with --preprocess-passes 1 where Not(Eq(x,x)) must fold to False
#      in Phase 1 so it doesn't survive as a True hypothesis in the proof snapshot.
#      Regression: proof_fail_000006 — simplifier::fold() was missing the reflexive
#      Eq(x,x)->True case, causing Not(Eq(x,x)) to be self-substituted to True.
add_test(
    NAME "smt2/proof_reflexive_eq_preproc"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --preprocess-passes 1 \
         --proof ${CMAKE_BINARY_DIR}/t59_proof.lean \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/t59_proof_reflexive_eq_preproc.smt2 && \
         grep -q 'hyp2 : False' ${CMAKE_BINARY_DIR}/t59_proof.lean"
)

# t60: --proof with --preprocess-passes 1 where the EUF propagates permanently-forced
#      equalities as SAT unit literals that appear in theory clause premises.
#      The proof snapshot must include those forced atoms as explicit hypotheses so
#      grind can discharge the premises.
#      Regression: proof_fail_000064 — forced atoms were not added to the proof snapshot.
add_test(
    NAME "smt2/proof_forced_atoms_preproc"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --preprocess-passes 1 \
         --proof ${CMAKE_BINARY_DIR}/t60_proof.lean \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/t60_proof_forced_atoms_preproc.smt2 && \
         grep -q 'c1 = (b1 p1)' ${CMAKE_BINARY_DIR}/t60_proof.lean"
)

# t48-t49: n-ary xor (:left-assoc)
# t61: --proof with no preprocessing: EUF theory clauses are emitted as standalone
#      theorems (theorem cl_k : ... := by grind).  When a positive literal in the
#      clause is a direct problem assertion, the relevant hypothesis is loaded
#      inside the theorem via (have hyp_j := hyp_j) before grind.
#      Regression: proof_fail_000469.
add_test(
    NAME "smt2/proof_hyp_dep_cl"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --proof ${CMAKE_BINARY_DIR}/t61_proof.lean \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/t61_proof_hyp_dep_cl.smt2 && \
         grep -q '^theorem cl_' ${CMAKE_BINARY_DIR}/t61_proof.lean && \
         grep -q 'have cl_.* := cl_' ${CMAKE_BINARY_DIR}/t61_proof.lean"
)

# t62: same class of bug as t61, different input.
#      Regression: proof_fail_000944.
#      t62 has a direct SAT contradiction (c0=c3 vs ¬(c0=c3)), so no EUF
#      theory clause is needed.  Already-assigned atoms are no longer emitted
#      as standalone theorem cl_ lemmas (they would require problem hypotheses
#      to prove and are unnecessary for the final grind step).
add_test(
    NAME "smt2/proof_hyp_dep_cl2"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --proof ${CMAKE_BINARY_DIR}/t62_proof.lean \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/t62_proof_hyp_dep_cl2.smt2 && \
         grep -q '^theorem contradiction' ${CMAKE_BINARY_DIR}/t62_proof.lean && \
         ! grep -q '^theorem cl_' ${CMAKE_BINARY_DIR}/t62_proof.lean"
)

# t63: Regression: Bool-sorted predicate atoms in theory clauses were emitted as
#      (True = (h a)) instead of (h a), causing grind to fail when --proof-minimize
#      was used.  The normalized form should just be the predicate application.
add_test(
    NAME "smt2/proof_minimize_bool_pred"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --proof ${CMAKE_BINARY_DIR}/t63_proof.lean --proof-minimize \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/t63_proof_minimize_bool_pred.smt2 && \
         ! grep -q 'True = ' ${CMAKE_BINARY_DIR}/t63_proof.lean && \
         grep -q '(h ' ${CMAKE_BINARY_DIR}/t63_proof.lean"
)

# t64: Regression: ite nodes inlined as `(if cond then a else b)` inside
#      decide(... = ...) in theory clauses caused grind to fail via
#      case-splitting.  Fix: use proxy constant name when available.
add_test(
    NAME "smt2/proof_ite_proxy_grind"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --proof ${CMAKE_BINARY_DIR}/t64_proof.lean \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/t64_proof_ite_proxy_grind.smt2 && \
         ! grep 'have cl_\\|have ite_pos_\\|have ite_neg_' ${CMAKE_BINARY_DIR}/t64_proof.lean | grep -q '(if '"
)

# t65: Regression: ite branch atoms excluded from ite_bridge emission caused
#      grind to not have the bridge between (branch=ite_inline) and (branch=proxy),
#      allowing spurious contradictions.
add_test(
    NAME "smt2/proof_ite_branch_atom_bridge"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --proof ${CMAKE_BINARY_DIR}/t65_proof.lean \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/t65_proof_ite_branch_atom_bridge.smt2 && \
         grep -q 'have ite_bridge_' ${CMAKE_BINARY_DIR}/t65_proof.lean"
)

add_smt2_test(nary_xor_unsat  t48_nary_xor_unsat.smt2  unsat)
add_smt2_test(nary_xor_sat    t49_nary_xor_sat.smt2    sat)

# Regression: theorem contradiction must end with bv_decide, never grind.
# (bv_decide is the correct SAT-closure tactic for the propositional contradiction
# once all EUF reasoning is captured in standalone theory lemmas proved by grind.)
add_test(
    NAME "smt2/proof_contradiction_uses_bv_decide"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --proof ${CMAKE_BINARY_DIR}/t_bvd_proof.lean \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/t01_unsat_direct.smt2 && \
         awk '/^theorem contradiction/,0' ${CMAKE_BINARY_DIR}/t_bvd_proof.lean | grep -q '  bv_decide' && \
         ! awk '/^theorem contradiction/,0' ${CMAKE_BINARY_DIR}/t_bvd_proof.lean | grep -q '  grind'"
)

# t50: --eq-bridge eliminates exponential blowup on 19-diamond chain (diamond20)
add_smt2_test_eq_bridge(eq_bridge_diamond  t50_eq_bridge_diamond.smt2  unsat)

# t45-t47: chained equality (= t1 t2 ... tn) (:chainable)
add_smt2_test(chained_eq_unsat         t45_chained_eq_unsat.smt2          unsat)
add_smt2_test(chained_eq_sat           t46_chained_eq_sat.smt2            sat)
add_smt2_test(chained_eq_nested_unsat  t47_chained_eq_nested_unsat.smt2   unsat)

# t66: Regression: deeply-nested let (300 levels) must not stack-overflow in build_fml
add_smt2_test_preproc(nested_let_deep  t66_nested_let_deep.smt2  unsat)

# t67: Regression: deeply-nested OR (500 levels) must not stack-overflow in
#      build_fml (parsing) or simplifier fold/subst (--preprocess-passes 1).
add_smt2_test_preproc(deep_or_nostack  t67_deep_or_nostack.smt2  unsat)

# t68: NOT(AND(eq1,...,eqN)) is encoded as one N-literal clause without
#      introducing Tseitin variables for intermediate AND nodes.
add_smt2_test(not_and_direct_clause  t68_not_and_direct_clause.smt2  unsat)

# t69: Repeated let-bound Bool formulas and U-terms are cached separately while
#      building preprocessing NodeId formulas.
add_smt2_test(let_cache_repeated_bool_and_term  t69_let_cache_repeated_bool_and_term.smt2  unsat)

# t70: Unit disequalities simplified to True must still feed finite-domain AMO
#      strengthening before finite-domain equality choices are encoded.
add_test(
    NAME "smt2/preproc_keeps_finite_domain_amo"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --preprocess-passes 1 --stats \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/t70_preproc_keeps_finite_domain_amo.smt2 \
         >/tmp/t70.out 2>/tmp/t70.err && \
         grep -q '^sat' /tmp/t70.out && \
         grep -q 'preproc.finite_domain_amo     1' /tmp/t70.err"
)

# t71: Keep a one-assertion top-level conjunction as one pending formula when
#      preprocessing is enabled. Splitting generated NEQ assertions into many
#      unit assertions lets simplification force disequalities early and causes
#      much worse EUF propagation under aggressive propagation settings.
add_test(
    NAME "smt2/preproc_keeps_top_level_and_unsplit"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --quiet --preprocess-passes 1 --stats \
         ${CMAKE_CURRENT_SOURCE_DIR}/smt2/t71_preproc_keeps_top_level_and_unsplit.smt2 \
         >/tmp/t71.out 2>/tmp/t71.err && \
         grep -q '^sat' /tmp/t71.out && \
         grep -q 'preproc.fmls_in               1' /tmp/t71.err && \
         grep -q 'preproc.finite_domain_amo     6' /tmp/t71.err"
)

# Normal command-line runs print build provenance, including the git commit and
# SAT backend version.  --quiet suppresses that banner.
add_test(
    NAME "cli/provenance_banner"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> ${CMAKE_CURRENT_SOURCE_DIR}/smt2/t01_unsat_direct.smt2 2>&1 | \
         grep -q 'llm2smt .* git .* sat CaDiCaL'"
)
add_test(
    NAME "cli/quiet_suppresses_provenance"
    COMMAND bash -c
        "out=$($<TARGET_FILE:llm2smt> --quiet ${CMAKE_CURRENT_SOURCE_DIR}/smt2/t01_unsat_direct.smt2 2>&1) && \
         test \"$out\" = unsat"
)
add_test(
    NAME "cli/help_groups_solver_options"
    COMMAND bash -c
        "$<TARGET_FILE:llm2smt> --help > ${CMAKE_BINARY_DIR}/llm2smt_help.out && \
         grep -q '\\[Option Group: QF_LRA\\]' ${CMAKE_BINARY_DIR}/llm2smt_help.out && \
         grep -q '\\[Option Group: QF_UF/EUF\\]' ${CMAKE_BINARY_DIR}/llm2smt_help.out && \
         grep -q '\\[Option Group: Theory propagation\\]' ${CMAKE_BINARY_DIR}/llm2smt_help.out && \
         grep -A80 '\\[Option Group: QF_LRA\\]' ${CMAKE_BINARY_DIR}/llm2smt_help.out | grep -q -- '--no-lra-eq-elim' && \
         grep -A80 '\\[Option Group: QF_LRA\\]' ${CMAKE_BINARY_DIR}/llm2smt_help.out | grep -q -- '--no-lra-ite-eq-direct'"
)

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

add_executable(test_lra_solver test_lra_solver.cpp)
target_link_libraries(test_lra_solver PRIVATE lra GTest::gtest_main)
target_include_directories(test_lra_solver PRIVATE ${CMAKE_SOURCE_DIR}/src)
gtest_discover_tests(test_lra_solver)

add_executable(test_preprocessor test_preprocessor.cpp)
target_link_libraries(test_preprocessor PRIVATE preprocessor core GTest::gtest_main)
target_include_directories(test_preprocessor PRIVATE ${CMAKE_SOURCE_DIR}/src)
gtest_discover_tests(test_preprocessor)
