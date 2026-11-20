signature hhStature =
sig
  type stature =
    {simp : bool, local_ : bool, def : bool, induction : bool}
  type statures
  type induction_concls

  val simp_thmids_of_deltas : ThmSetData.setdelta list -> string list
  val induction_concls_of : Thm.thm list -> induction_concls
  val induction_by_concl : induction_concls -> Term.term -> bool
  val induction_by_shape : string -> Term.term -> bool

  val create_statures_for : string -> statures
  val create_statures : unit -> statures
  val stature_of : statures -> string -> stature
end
