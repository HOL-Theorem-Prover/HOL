signature realSyntax =
sig
  include Abbrev

  (* terms and types *)
  val real_ty        : hol_type
  val zero_tm        : term
  val one_tm         : term
  val negate_tm      : term
  val absval_tm      : term
  val plus_tm        : term
  val minus_tm       : term
  val mult_tm        : term
  val div_tm         : term
  val exp_tm         : term
  val real_eq_tm     : term
  val less_tm        : term
  val leq_tm         : term
  val great_tm       : term
  val geq_tm         : term
  val min_tm         : term
  val max_tm         : term
  val real_injection  : term (* the injection from :num -> :real *)

  (* discriminators, constructors, etc *)

  val is_real_literal : term -> bool
  val term_of_int     : Arbint.int -> term
  val int_of_term     : term -> Arbint.int

  val mk_injected    : term -> term
  val dest_injected  : term -> term
  val is_injected    : term -> bool

  val is_negated     : term -> bool  (* if a term is of form ~ e *)
  val mk_negated     : term -> term
  val dest_negated   : term -> term

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

  val is_div         : term -> bool
  val dest_div       : term -> (term * term)
  val mk_div         : (term * term) -> term

  val is_absval      : term -> bool
  val mk_absval      : term -> term
  val dest_absval    : term -> term

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

  val is_min         : term -> bool
  val dest_min       : term -> (term * term)
  val mk_min         : (term * term) -> term

  val is_max         : term -> bool
  val dest_max       : term -> (term * term)
  val mk_max         : (term * term) -> term

end
