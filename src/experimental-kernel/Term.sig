signature Term =
sig

  include FinalTerm where type hol_type = Type.hol_type
  val prim_mk_eq        : hol_type -> term -> term -> term
  val prim_mk_imp       : term -> term -> term
  val imp               : term
  val dest_eq_ty        : term -> term * term * hol_type
  val lazy_beta_conv    : term -> term

end
