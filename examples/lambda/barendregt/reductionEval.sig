signature reductionEval =
sig
  include Abbrev

  val betafy : simpLib.simpset -> simpLib.simpset
  val whfy : simpLib.simpset -> simpLib.simpset
  val bsrw_ss : unit -> simpLib.simpset
  val unvarify_tac : thm -> Tactic.tactic
  val NORMSTAR_ss : simpLib.ssfrag
  val export_betarwt : string -> unit

end
