signature extra_pred_setTools =
sig

  (* Simple *)
  val pset_set_ss : simpLib.simpset
  val pset_elt_ss : simpLib.simpset

  val pset_ss : simpLib.simpset
  val PSET_TAC : Thm.thm list -> Abbrev.tactic

end