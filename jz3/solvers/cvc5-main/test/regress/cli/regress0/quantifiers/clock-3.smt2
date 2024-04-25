(set-logic LIA)
(set-info :status unsat)
(declare-fun t () Int)
(assert (forall ((s Int) (m Int)) (or (not (= (+ (* 3 m) s) t)) (< s 0) (>= s 3))))
(check-sat)
