(set-logic QF_LRA)
(declare-fun b () Bool)
(assert (not (= (ite b false true) (not b))))
(check-sat)
