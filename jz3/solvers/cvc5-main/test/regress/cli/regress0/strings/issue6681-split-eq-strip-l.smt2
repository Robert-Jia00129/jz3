(set-logic QF_SLIA)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)
(assert (= (str.++ "A" a "CBA" b "BA" d) (str.++ b "BA" d a "CBA" c)))
(set-info :status sat)
(check-sat)
