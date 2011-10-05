signature reductionEval =
sig
  include Abbrev

  val betafy : simpLib.simpset -> simpLib.simpset
  val whfy : simpLib.simpset -> simpLib.simpset
  val bsrw_ss : unit -> simpLib.simpset
  val BETA_ss : simpLib.ssfrag


  val unvarify_tac : thm -> Tactic.tactic
  val NORMSTAR_ss : simpLib.ssfrag
  val export_betarwt : string -> unit
  val bstore_thm : string * term * tactic -> thm


end
