(set-logic QF_LIA)
(declare-fun x () Int)
(assert (>= x 0))
(check-sat)
; Result: sat
(check-sat-assuming ((< x 0)))
; Result: unsat
(assert (= x 0))
(check-sat)
; Result: sat
