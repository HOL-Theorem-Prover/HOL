signature PSet_ind =
sig 
   type tactic = Abbrev.tactic

  val SET_INDUCT_TAC : Thm.thm -> tactic
end;
