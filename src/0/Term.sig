signature Term =
sig

  include FinalTerm where type hol_type = Type_dtype.hol_type
                          and type term = KernelTypes.term

  val termsig        : unit -> Type_dtype.holty KernelSig.symboltable

  val lazy_beta_conv : term -> term
  val imp            : term
  val dest_eq_ty     : term -> term * term * hol_type
  val prim_mk_eq     : hol_type -> term -> term -> term
  val prim_mk_imp    : term -> term -> term
  val break_const    : term -> Type_dtype.id * hol_type
  val break_abs      : term -> term
  val is_bvar        : term -> bool
  val kernelid       : string

end
