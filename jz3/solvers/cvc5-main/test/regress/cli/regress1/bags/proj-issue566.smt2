(set-logic ALL)
(set-info :status sat)
(set-option :debug-check-models true)
(declare-const x (Bag Bool))
(assert (= (bag.card (bag.union_disjoint x x)) (bag.card (bag.duplicate_removal (bag.union_disjoint x x)))))
(check-sat)
