signature hhStature =
sig
  (* A fact's flags: in the simp set, from the target theory, a definition,
     an induction principle. *)
  type stature =
    {simp : bool, local_ : bool, def : bool, induction : bool}
  type statures
  type induction_concls

  (* The simp set the deltas build, in String.compare order. *)
  val simp_thmids_of_deltas : ThmSetData.setdelta list -> string list
  val induction_concls_of : Thm.thm list -> induction_concls
  val induction_by_concl : induction_concls -> Term.term -> bool
  (* The name contains "induct" and an outer universal quantifier binds a
     predicate. *)
  val induction_by_shape : string -> Term.term -> bool

  (* The statures of the facts of a theory and its ancestors. *)
  val create_statures_for : string -> statures
  val create_statures : unit -> statures
  (* All flags false for an unknown fact or a namespace value. *)
  val stature_of : statures -> string -> stature
end
