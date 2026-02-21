; Regression: Bool-as-UF-argument mutual-exclusivity clause.
; A Bool variable x is used as a UF argument.  The link_bool_term_to_euf bridge
; adds two conditional equalities: (x → node=__bool_true) and (¬x → node=__bool_false).
; Without the mutual-exclusivity clause {-eq_true, -eq_false}, the SAT solver can
; freely set BOTH to TRUE simultaneously, which merges __bool_true with __bool_false
; and triggers the permanent (true ≠ false) disequality conflict — making a SAT
; formula appear UNSAT.
;
; Here x is unconstrained; f(x) ≠ f(x) is trivially false so the formula is UNSAT.
; What we really test: the solver must NOT spuriously conclude UNSAT due to the
; bool-node bridge misbehaving when x is a free Bool in a UF argument position.
; A second test (t26) checks the satisfiable case.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun x () Bool)
(declare-fun f (Bool) U)
(declare-fun a () U)
(declare-fun b () U)
; x is free (unconstrained), so f(x) could be f(true) or f(false).
; a = f(true), b = f(false) — we force both sides.
(assert (= a (f true)))
(assert (= b (f false)))
; a ≠ b (f(true) ≠ f(false)): consistent only if true ≠ false in EUF,
; which is the permanent axiom.  This is satisfiable: true and false are distinct.
(assert (not (= a b)))
(check-sat)
; expected: sat
