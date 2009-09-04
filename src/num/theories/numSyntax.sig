signature numSyntax =
sig
  include Abbrev

  val num           : hol_type

  val zero_tm       : term
  val suc_tm        : term
  val pre_tm        : term
  val numeral_tm    : term
  val alt_zero_tm   : term
  val bit1_tm       : term
  val bit2_tm       : term
  val plus_tm       : term
  val minus_tm      : term
  val mult_tm       : term
  val exp_tm        : term
  val div_tm        : term
  val mod_tm        : term
  val div2_tm       : term
  val mod_2exp_tm   : term
  val less_tm       : term
  val greater_tm    : term
  val geq_tm        : term
  val leq_tm        : term
  val even_tm       : term
  val odd_tm        : term
  val min_tm        : term
  val max_tm        : term
  val num_case_tm   : term
  val fact_tm       : term
  val funpow_tm     : term
  val while_tm      : term
  val least_tm      : term
  val divmod_tm     : term
  val measure_tm    : term

  val mk_suc        : term -> term
  val mk_pre        : term -> term
  val mk_plus       : term * term -> term
  val mk_minus      : term * term -> term
  val mk_mult       : term * term -> term
  val mk_exp        : term * term -> term
  val mk_div        : term * term -> term
  val mk_mod        : term * term -> term
  val mk_div2       : term -> term
  val mk_mod_2exp   : term * term -> term
  val mk_less       : term * term -> term
  val mk_greater    : term * term -> term
  val mk_geq        : term * term -> term
  val mk_leq        : term * term -> term
  val mk_even       : term -> term
  val mk_odd        : term -> term
  val mk_min        : term * term -> term
  val mk_max        : term * term -> term
  val mk_num_case   : term * term * term -> term
  val mk_fact       : term -> term
  val mk_funpow     : term * term * term -> term
  val mk_while      : term * term * term -> term
  val mk_least      : term -> term
  val mk_divmod     : term * term * term -> term
  val mk_cmeasure   : term -> term
  val mk_measure    : term * term * term -> term

  val dest_suc      : term -> term
  val dest_pre      : term -> term
  val dest_plus     : term -> term * term
  val dest_minus    : term -> term * term
  val dest_mult     : term -> term * term
  val dest_exp      : term -> term * term
  val dest_div      : term -> term * term
  val dest_mod      : term -> term * term
  val dest_div2     : term -> term
  val dest_mod_2exp : term -> term * term
  val dest_less     : term -> term * term
  val dest_greater  : term -> term * term
  val dest_geq      : term -> term * term
  val dest_leq      : term -> term * term
  val dest_even     : term -> term
  val dest_odd      : term -> term
  val dest_min      : term -> term * term
  val dest_max      : term -> term * term
  val dest_num_case : term -> term * term * term
  val dest_fact     : term -> term
  val dest_funpow   : term -> term * term * term
  val dest_while    : term -> term * term * term
  val dest_least    : term -> term
  val dest_divmod   : term -> term * term * term
  val dest_measure  : term -> term * term * term
  val dest_cmeasure : term -> term

  val is_suc        : term -> bool
  val is_pre        : term -> bool
  val is_plus       : term -> bool
  val is_minus      : term -> bool
  val is_mult       : term -> bool
  val is_exp        : term -> bool
  val is_div        : term -> bool
  val is_mod        : term -> bool
  val is_div2       : term -> bool
  val is_mod_2exp   : term -> bool
  val is_less       : term -> bool
  val is_greater    : term -> bool
  val is_geq        : term -> bool
  val is_leq        : term -> bool
  val is_even       : term -> bool
  val is_odd        : term -> bool
  val is_min        : term -> bool
  val is_max        : term -> bool
  val is_num_case   : term -> bool
  val is_fact       : term -> bool
  val is_funpow     : term -> bool
  val is_while      : term -> bool
  val is_least      : term -> bool
  val is_divmod     : term -> bool
  val is_measure    : term -> bool

  val is_numeral    : term -> bool
  val mk_numeral    : Arbnum.num -> Term.term
  val dest_numeral  : term -> Arbnum.num

  val int_of_term   : term -> int
  val term_of_int   : int -> term

  val list_mk_plus  : term list -> term
  val list_mk_mult  : term list -> term
  val strip_plus    : term -> term list
  val strip_mult    : term -> term list

  val lift_num      : hol_type -> Arbnum.num -> term

end
