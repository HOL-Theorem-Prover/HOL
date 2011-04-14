signature combinSyntax =
sig
  include Abbrev

  val K_tm      : term
  val S_tm      : term
  val I_tm      : term
  val C_tm      : term
  val W_tm      : term
  val o_tm      : term
  val update_tm : term
  val fail_tm   : term

  val mk_K      : term * term -> term
  val mk_K_1    : term * hol_type -> term
  val mk_S      : term * term * term -> term
  val mk_I      : term -> term
  val mk_C      : term * term * term -> term
  val mk_W      : term * term -> term
  val mk_o      : term * term -> term
  val mk_update : term * term -> term
  val mk_fail   : term * string * term list -> term

  val dest_K           : term -> term * term
  val dest_K_1         : term -> term
  val dest_S           : term -> term * term * term
  val dest_I           : term -> term
  val dest_C           : term -> term * term * term
  val dest_W           : term -> term * term
  val dest_o           : term -> term * term
  val dest_update      : term -> term * term
  val dest_update_comb : term -> (term * term) * term
  val strip_update     : term -> (term * term) list * term
  val dest_fail        : term -> term * string * term list

  val is_K           : term -> bool
  val is_K_1         : term -> bool
  val is_S           : term -> bool
  val is_I           : term -> bool
  val is_C           : term -> bool
  val is_W           : term -> bool
  val is_o           : term -> bool
  val is_update      : term -> bool
  val is_update_comb : term -> bool
  val is_fail        : term -> bool

end
