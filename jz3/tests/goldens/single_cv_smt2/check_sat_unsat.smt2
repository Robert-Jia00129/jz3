(set-logic QF_LIA)
(declare-fun x () Int)
(assert (= x 1))
(assert (= x 2))
(check-sat)
; Result: unsat
