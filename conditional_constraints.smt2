; benchmark generated from python API
(set-info :status unknown)
(declare-fun x () Int)
(assert
 (or (and (>= x 8) (< x 12)) (and (> x 12) (<= x 17))))
(check-sat)
