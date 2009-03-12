signature reductionEval =
sig

  val betafy : simpLib.simpset -> simpLib.simpset
  val unvarify_tac : Tactic.tactic

end
