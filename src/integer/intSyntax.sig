signature intSyntax = 
sig

  (* terms and types *)
  val int_ty : Type.hol_type
  val zero_tm : Term.term
  val negate_tm : Term.term
  val absval_tm : Term.term
  val plus_tm : Term.term
  val minus_tm : Term.term
  val mult_tm : Term.term
  val less_tm : Term.term
  val leq_tm : Term.term
  val great_tm : Term.term
  val geq_tm : Term.term
  val divides_tm : Term.term
  val min_tm : Term.term
  val int_injection : Term.term (* the injection from :num -> :int *)

  (* discriminators, constructors, etc *)
  val is_int_literal : Term.term -> bool
  val is_negated : Term.term -> bool  (* if a term is of form ~ e *)
  val mk_negated : Term.term -> Term.term
  val int_of_term : Term.term -> Arbint.int
  val term_of_int : Arbint.int -> Term.term

  val is_plus : Term.term -> bool
  val mk_plus : (Term.term * Term.term) -> Term.term
  val list_mk_plus : (* non-empty *) Term.term list -> Term.term
  val strip_plus : Term.term -> Term.term list

  val is_minus : Term.term -> bool
  val mk_minus : (Term.term * Term.term) -> Term.term

  val is_mult : Term.term -> bool
  val mk_mult : (Term.term * Term.term) -> Term.term
  val list_mk_mult : (* non-empty *) Term.term list -> Term.term
  val strip_mult : Term.term -> Term.term list

  val is_absval : Term.term -> bool
  val mk_absval : Term.term -> Term.term

  val is_less : Term.term -> bool
  val mk_less : (Term.term * Term.term) -> Term.term

  val is_leq : Term.term -> bool
  val mk_leq : (Term.term * Term.term) -> Term.term

  val is_great : Term.term -> bool
  val mk_great : (Term.term * Term.term) -> Term.term

  val is_geq : Term.term -> bool
  val mk_geq : (Term.term * Term.term) -> Term.term

  val is_divides : Term.term -> bool
  val mk_divides : (Term.term * Term.term) -> Term.term

end (* sig *)
