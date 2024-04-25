; EXPECT: sat
(set-option :incremental false)
(set-logic ALL)


(declare-fun x () (Relation Int Int))
(declare-fun y () (Relation Int Int))
(declare-fun w () (Relation Int Int))
(declare-fun z () (Relation (Relation Int Int) (Relation Int Int)))
(declare-fun a () (Tuple Int Int))
(declare-fun b () (Tuple Int Int))
(assert (not (= a b)))
(assert (set.member a x))
(assert (set.member b y))
(assert (set.member b w))
(assert (set.member (tuple x y) z))
(assert (set.member (tuple w x) z))
(assert (not (set.member (tuple x x) (rel.join z z))))
(assert (set.member (tuple x (set.singleton (tuple 0 0))) (rel.join z z)))
(check-sat)
