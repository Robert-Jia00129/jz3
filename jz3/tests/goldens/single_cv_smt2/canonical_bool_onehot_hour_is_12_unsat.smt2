(set-logic QF_LIA)
(declare-fun hour_is_10 () Bool)
(declare-fun hour_is_11 () Bool)
(declare-fun hour_is_12 () Bool)
(declare-fun hour_is_13 () Bool)
(declare-fun hour_is_14 () Bool)
(declare-fun hour_is_15 () Bool)
(declare-fun hour_is_16 () Bool)
(declare-fun hour_is_17 () Bool)
(declare-fun hour_is_8 () Bool)
(declare-fun hour_is_9 () Bool)
(assert ((_ pbeq 1 1 1 1 1 1 1 1 1 1 1)
  hour_is_8
  hour_is_9
  hour_is_10
  hour_is_11
  hour_is_12
  hour_is_13
  hour_is_14
  hour_is_15
  hour_is_16
  hour_is_17))
(assert (not hour_is_12))
(check-sat-assuming (hour_is_12))
; Result: unsat
