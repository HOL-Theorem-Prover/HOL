signature intLib = sig

  (* terms and types *)
  val int_ty : Type.hol_type
  val zero_tm : Term.term
  val plus_tm : Term.term
  val mult_tm : Term.term
  val less_tm : Term.term
  val divides_tm : Term.term
  val MIN_tm : Term.term
  val int_injection : Term.term (* the injection from :num -> :int *)
  val int_negation : Term.term  (* the negation function *)

  (* discriminators, constructors, etc *)
  val is_int_literal : Term.term -> bool
  val is_int_negated : Term.term -> bool
  val int_of_term : Term.term -> Arbint.int
  val term_of_int : Arbint.int -> Term.term

  val is_plus : Term.term -> bool
  val mk_plus : (Term.term * Term.term) -> Term.term
  val list_mk_plus : (* non-empty *) Term.term list -> Term.term
  val strip_plus : Term.term -> Term.term list

  val is_mult : Term.term -> bool
  val mk_mult : (Term.term * Term.term) -> Term.term
  val list_mk_mult : (* non-empty *) Term.term list -> Term.term
  val strip_mult : Term.term -> Term.term list

  val is_less : Term.term -> bool
  val mk_less : (Term.term * Term.term) -> Term.term

  val is_divides : Term.term -> bool
  val mk_divides : (Term.term * Term.term) -> Term.term

end (* sig *)