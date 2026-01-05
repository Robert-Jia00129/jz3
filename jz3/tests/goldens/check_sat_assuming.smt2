(set-logic QF_LIA)

(declare-fun x () Int)
(declare-fun p () Bool)
(declare-fun q () Bool)

; Base constraint
(assert (>= x 0))

; Assumption-controlled constraints (portable: assumptions are literals)
(assert (=> p (= x 1)))
(assert (=> q (= x (- 1))))

; Case 1: SAT (p forces x = 1, consistent with x >= 0)
(check-sat-assuming (p))

; Case 2: UNSAT (q forces x = -1, contradicts x >= 0)
(check-sat-assuming (q))
