signature int_arith = sig
  val INT_ARITH_CONV : Term.term -> Thm.thm
  val INT_ARITH_PROVE : Term.term -> Thm.thm
  val is_presburger : Term.term -> bool
  val decide_pure_presburger_term : Term.term -> Thm.thm
end
