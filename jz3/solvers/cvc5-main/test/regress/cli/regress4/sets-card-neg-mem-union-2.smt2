(set-logic QF_ALL)
(set-info :status unsat)
(set-option :produce-models true)
(set-option :sets-ext true)
(declare-fun A () (Set Int))
(declare-fun B () (Set Int))
(declare-fun C () (Set Int))
(declare-fun D () (Set Int))

(declare-fun x () Int)
(assert (not (set.member x A)))
(assert (not (set.member x B)))
(assert (not (set.member x C)))
(assert (not (set.member x D)))
(declare-fun y () Int)
(assert (not (set.member y A)))
(assert (not (set.member y B)))
(assert (not (set.member y C)))
(assert (not (set.member y D)))
(declare-fun z () Int)
(assert (not (set.member z A)))
(assert (not (set.member z B)))
(assert (not (set.member z C)))
(assert (not (set.member z D)))

(assert (distinct x y z))

(assert (= (set.card (set.union A (set.union B (set.union C D)))) 6))

(assert (= (set.card (as set.universe (Set Int))) 8))

(check-sat)
