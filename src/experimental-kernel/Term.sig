signature Term =
sig

  include RestrictedTerm

  val prim_mk_eq    : hol_type -> term -> term -> term
  val prim_mk_imp   : term -> term -> term

end
