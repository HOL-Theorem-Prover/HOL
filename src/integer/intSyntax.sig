signature intSyntax =
sig
  include Abbrev

  (* terms and types *)
  val int_ty         : hol_type
  val zero_tm        : term
  val one_tm         : term
  val negate_tm      : term
  val absval_tm      : term
  val plus_tm        : term
  val minus_tm       : term
  val mult_tm        : term
  val less_tm        : term
  val leq_tm         : term
  val great_tm       : term
  val geq_tm         : term
  val divides_tm     : term
  val min_tm         : term
  val int_injection  : term (* the injection from :num -> :int *)

  (* discriminators, constructors, etc *)

  val is_int_literal : term -> bool
  val is_negated     : term -> bool  (* if a term is of form ~ e *)
  val mk_negated     : term -> term
  val int_of_term    : term -> Arbint.int
  val term_of_int    : Arbint.int -> term

  val is_plus        : term -> bool
  val mk_plus        : (term * term) -> term
  val dest_plus      : term -> (term * term)
  val list_mk_plus   : (* non-empty *) term list -> term
  val strip_plus     : term -> term list

  val is_minus       : term -> bool
  val dest_minus     : term -> (term * term)
  val mk_minus       : (term * term) -> term

  val is_mult        : term -> bool
  val mk_mult        : (term * term) -> term
  val dest_mult      : term -> (term * term)
  val list_mk_mult   : (* non-empty *) term list -> term
  val strip_mult     : term -> term list

  val is_absval      : term -> bool
  val mk_absval      : term -> term

  val is_less        : term -> bool
  val dest_less      : term -> (term * term)
  val mk_less        : (term * term) -> term

  val is_leq         : term -> bool
  val dest_leq       : term -> (term * term)
  val mk_leq         : (term * term) -> term

  val is_great       : term -> bool
  val dest_great     : term -> (term * term)
  val mk_great       : (term * term) -> term

  val is_geq         : term -> bool
  val dest_geq       : term -> (term * term)
  val mk_geq         : (term * term) -> term

  val is_divides     : term -> bool
  val dest_divides   : term -> (term * term)
  val mk_divides     : (term * term) -> term

end
