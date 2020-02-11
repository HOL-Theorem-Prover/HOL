signature finite_setSyntax =
sig

  include Abbrev
  val fset_ty : hol_type
  val mk_fset_ty : hol_type -> hol_type
  val empty_tm : term
  val in_tm : term
  val insert_tm : term
  val inter_tm : term
  val union_tm : term

  val mk_empty : hol_type -> term
  val mk_in : term * term -> term
  val mk_insert : term * term -> term
  val mk_union : term * term -> term
  val mk_inter : term * term -> term
  val mk_set : term list * hol_type -> term
  val mk_set1 : term list -> term


end
