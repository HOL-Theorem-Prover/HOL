signature numSyntax = sig
  val num_ty : Type.hol_type
  val zero_t : Term.term
  val SUC_t  : Term.term

  val is_numeral : Term.term -> bool
  val mk_numeral : Arbnum.num -> Term.term
  val dest_numeral : Term.term -> Arbnum.num

  val mk_plus : Term.term * Term.term -> Term.term

  val mk_SUC : Term.term -> Term.term
  val is_SUC : Term.term -> bool

end
