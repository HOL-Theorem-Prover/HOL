signature prob_extraTools =
sig

  (* Simple *)
  val pred_set_ss : simpLib.simpset
  val PRED_SET_TAC : Thm.thm list -> Abbrev.tactic

  (* More powerful, but require the element type *)
  val pset_ss_ty : Type.hol_type -> simpLib.simpset
  val PSET_TAC_ty : Type.hol_type -> Thm.thm list -> Abbrev.tactic

  (* The powerful tools with element type :num->bool *)
  val pset_ss : simpLib.simpset
  val PSET_TAC : Thm.thm list -> Abbrev.tactic

end
