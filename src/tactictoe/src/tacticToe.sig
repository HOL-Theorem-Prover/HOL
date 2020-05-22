signature tacticToe =
sig

  include Abbrev

  val set_timeout : real -> unit
  val ttt : tactic
  val tactictoe : term -> thm

  (* allow reloading of tactic data *)
  val clean_ttt_tacdata_cache : unit -> unit
  (* evaluation *)
  val ttt_eval : mlThmData.thmdata * mlTacticData.tacdata -> goal -> unit

end
