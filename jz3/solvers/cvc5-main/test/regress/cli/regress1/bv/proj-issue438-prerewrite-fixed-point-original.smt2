; DISABLE-TESTER: lfsc
(set-logic QF_BV)
(declare-const T (_ BitVec 1))
(assert (and (bvsle (_ bv0 32) (bvadd (bvadd (_ bv1 32) (_ bv0 32)) ((_ zero_extend 24) ((_ extract 15 8) (bvshl ((_ zero_extend 24) ((_ extract 15 8) (bvsub (bvxor ((_ zero_extend 24) ((_ extract 15 8) (bvsub ((_ zero_extend 24) ((_ extract 7 0) (bvxor (bvadd ((_ zero_extend 24) ((_ extract 7 0) ((_ extract 7 0) (bvsub (bvadd ((_ zero_extend 24) ((_ extract 7 0) (bvadd (_ bv0 32) ((_ zero_extend 24) ((_ extract 15 8) (bvsub (bvadd ((_ zero_extend 24) ((_ extract 7 0) (bvsub (bvxor (bvadd ((_ zero_extend 24) ((_ extract 7 0) (bvadd (_ bv0 32) ((_ zero_extend 24) (bvxor (bvxor (_ bv0 8) ((_ extract 7 0) ((_ extract 7 0) (bvxor (bvadd (_ bv0 32) ((_ zero_extend 24) ((_ extract 15 8) (bvsub ((_ zero_extend 24) ((_ extract 7 0) (bvsub (bvxor ((_ zero_extend 24) ((_ extract 7 0) (bvadd (_ bv0 32) (bvshl ((_ zero_extend 24) (bvxor (bvxor (_ bv0 8) ((_ extract 7 0) (bvadd (_ bv0 32) ((_ zero_extend 24) (bvxor (_ bv0 8) ((_ extract 7 0) (bvxor (bvadd (_ bv0 32) ((_ zero_extend 24) (bvxor (_ bv0 8) ((_ extract 7 0) (bvsub (_ bv0 32) ((_ zero_extend 24) ((_ zero_extend 7) T))))))) (_ bv0 32)))))))) (_ bv0 8))) (_ bv0 32))))) (_ bv0 32)) (_ bv1 32)))) (_ bv1 32))))) (_ bv0 32))))) (_ bv0 8)))))) (_ bv0 32)) (_ bv0 32)) (_ bv0 32)))) (_ bv0 32)) (_ bv1 32))))))) (_ bv0 32)) (_ bv0 32))))) (_ bv0 32)) (_ bv0 32)))) (_ bv1 32)))) (_ bv0 32)) (_ bv1 32)))) (_ bv1 32)))))) (= (_ bv0 32) (bvxor (_ bv0 32) (bvadd (bvadd (_ bv1 32) (_ bv0 32)) ((_ zero_extend 24) ((_ extract 15 8) (bvshl ((_ zero_extend 24) ((_ extract 15 8) (bvsub (bvxor ((_ zero_extend 24) ((_ extract 15 8) (bvsub ((_ zero_extend 24) ((_ extract 7 0) (bvxor (bvadd ((_ zero_extend 24) ((_ extract 7 0) ((_ extract 7 0) (bvsub (bvadd ((_ zero_extend 24) ((_ extract 7 0) (bvadd (_ bv0 32) ((_ zero_extend 24) ((_ extract 15 8) (bvsub (bvadd ((_ zero_extend 24) ((_ extract 7 0) (bvsub (bvxor (bvadd ((_ zero_extend 24) ((_ extract 7 0) (bvadd (_ bv0 32) ((_ zero_extend 24) (bvxor (bvxor (_ bv0 8) ((_ extract 7 0) ((_ extract 7 0) (bvxor (bvadd (_ bv0 32) ((_ zero_extend 24) ((_ extract 15 8) (bvsub ((_ zero_extend 24) ((_ extract 7 0) (bvsub (bvxor ((_ zero_extend 24) ((_ extract 7 0) (bvadd (_ bv0 32) (bvshl ((_ zero_extend 24) (bvxor (bvxor (_ bv0 8) ((_ extract 7 0) (bvadd (_ bv0 32) ((_ zero_extend 24) (bvxor (_ bv0 8) ((_ extract 7 0) (bvxor (bvadd (_ bv0 32) ((_ zero_extend 24) (bvxor (_ bv0 8) ((_ extract 7 0) (bvsub (_ bv0 32) ((_ zero_extend 24) ((_ zero_extend 7) T))))))) (_ bv0 32)))))))) (_ bv0 8))) (_ bv0 32))))) (_ bv0 32)) (_ bv1 32)))) (_ bv1 32))))) (_ bv0 32))))) (_ bv0 8)))))) (_ bv0 32)) (_ bv0 32)) (_ bv0 32)))) (_ bv0 32)) (_ bv1 32))))))) (_ bv0 32)) (_ bv0 32))))) (_ bv0 32)) (_ bv0 32)))) (_ bv1 32)))) (_ bv0 32)) (_ bv1 32)))) (_ bv1 32)))))))))
(set-info :status unsat)
(check-sat)
