; Regression: Bool-sorted symbols used as arguments to a UF must have their
; SAT assignment bridged to __bool_true/__bool_false via EUF equalities, so
; that congruence closure can see when two Bool arguments are equal.
;
; Here p and q are both assigned false by the unit clauses, so they both equal
; false_node in EUF.  Congruence then derives f(p)=f(q), contradicting f(p)≠f(q).
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun f (Bool) U)
(assert (not p))
(assert (not q))
(assert (not (= (f p) (f q))))
(check-sat)
; expected: unsat
