; COMMAND-LINE: --unconstrained-simp
(set-logic QF_AUFBVLIA)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status sat)
(declare-fun v1 () Int)
(declare-fun v2 () Int)
(declare-fun a2 (Int) (_ BitVec 1024))
(declare-fun v3 () (_ BitVec 1024))
(declare-fun v4 () (_ BitVec 1024))
(declare-fun v5 () (_ BitVec 1024))
(assert (< v2 100))
(assert (not (= (a2 (- (+ v1 5) v2)) (bvudiv (bvudiv v4 v5) (bvudiv (bvudiv v3 v4) (bvudiv v3 v5))))))
(check-sat)
(exit)
