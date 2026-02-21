; Regression: Bool-valued UF results were not registered in EUF when only
; appearing in Bool-equality contexts (eval_lit path), so congruence over them
; was never triggered.
;
; Setup:
;   Extract : U -> Bool,  Concat : Bool x V -> W,  n1s : W (constant)
;   a, b, c : U;   p : Bool;   w2, w4 : W
;
;   (assert (= a b))                     — a = b in EUF
;   (assert (= p (Extract a)))           — Bool equality; links p ↔ Extract(a)
;   (assert (= w2 (Concat p v)))         — w2 = Concat(p, v)
;   (assert (= w4 (Concat (Extract b) v))) — w4 = Concat(Extract(b), v)
;   (assert (= w2 n1s))                  — w2 = n1s
;   (assert (not (= w4 n1s)))            — w4 ≠ n1s
;
; Chain:
;   a = b  →  Extract(a) = Extract(b)  [EUF congruence]
;   p ↔ Extract(a) and Extract(a) = Extract(b)
;   → both Extract(a) and Extract(b) map to __bool_true/__bool_false
;   → p_node = Extract(a)_node = Extract(b)_node
;   → Concat(p, v) = Concat(Extract(b), v)  [congruence]
;   → w2 = w4 = n1s  → contradiction with w4 ≠ n1s
;
; Expected: unsat
(set-logic QF_UF)
(declare-sort U 0)
(declare-sort V 0)
(declare-sort W 0)
(declare-fun Extract (U) Bool)
(declare-fun Concat  (Bool V) W)
(declare-fun a   () U)
(declare-fun b   () U)
(declare-fun p   () Bool)
(declare-fun v   () V)
(declare-fun w2  () W)
(declare-fun w4  () W)
(declare-fun n1s () W)
(assert (= a b))
(assert (= p (Extract a)))
(assert (= w2 (Concat p v)))
(assert (= w4 (Concat (Extract b) v)))
(assert (= w2 n1s))
(assert (not (= w4 n1s)))
(check-sat)
; expected: unsat
