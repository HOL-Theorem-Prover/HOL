signature probExtraTools =
sig
  include Abbrev

  (* Simple *)
  val pred_set_ss : simpLib.simpset
  val PRED_SET_TAC : thm list -> tactic

  (* More powerful, but require the element type *)
  val pset_ss_ty : hol_type -> simpLib.simpset
  val PSET_TAC_ty : hol_type -> thm list -> tactic

  (* The powerful tools with element type :num->bool *)
  val pset_ss  : simpLib.simpset
  val PSET_TAC : thm list -> tactic

end