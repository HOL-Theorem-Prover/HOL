signature Term =
sig

  include FinalTerm where type hol_type = KernelTypes.hol_type
                          and type term = KernelTypes.term

  val termsig       : KernelTypes.holty KernelSig.symboltable

  val lazy_beta_conv : term -> term
  val imp            : term
  val dest_eq_ty     : term -> term * term * hol_type
  val prim_mk_eq     : hol_type -> term -> term -> term
  val prim_mk_imp    : term -> term -> term
  val break_const    : term -> KernelTypes.id * hol_type
  val break_abs      : term -> term
  val trav           : (term -> unit) -> term -> unit
  val pp_raw_term    : (term -> int) -> Portable.ppstream -> term -> unit
  val is_bvar        : term -> bool

end;
