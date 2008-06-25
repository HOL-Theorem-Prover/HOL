signature Term =
sig

  include FinalTerm where type hol_type = Type.hol_type
  val uptodate_term     : term -> bool

  val thy_consts        : string -> term list
  val del_segment       : string -> unit

  val prim_new_const    : KernelSig.kernelname -> hol_type -> term
  val prim_delete_const : KernelSig.kernelname -> unit
  val prim_mk_eq        : hol_type -> term -> term -> term
  val prim_mk_imp       : term -> term -> term
  val imp               : term
  val dest_eq_ty        : term -> term * term * hol_type
  val lazy_beta_conv    : term -> term

end
