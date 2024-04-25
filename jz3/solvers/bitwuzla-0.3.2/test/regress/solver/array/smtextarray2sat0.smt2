(set-logic QF_AUFBV)
(set-info :status sat)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(assert (= (select a (_ bv1 2)) (select b (_ bv1 2))))
(assert (= (select a (_ bv2 2)) (select b (_ bv2 2))))
(assert (= (select a (_ bv3 2)) (select b (_ bv3 2))))
(assert (not (= a b)))
(check-sat)

