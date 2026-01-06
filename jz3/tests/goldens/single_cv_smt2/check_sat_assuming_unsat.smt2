(set-logic QF_LIA)
(declare-fun x () Int)
(assert (>= x 0))
(check-sat-assuming ((< x 0)))
; Result: unsat
