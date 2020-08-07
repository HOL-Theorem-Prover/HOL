signature tacticToe =
sig

  include Abbrev

  type tnn = mlTreeNeuralNetwork.tnn

  val main_tactictoe : 
    mlThmData.thmdata * mlTacticData.tacdata ->
    tnn option * tnn option ->
    goal -> tttSearch.proofstatus * tttSearch.tree

  val clean_ttt_tacdata_cache : unit -> unit
  val disable_warnings : unit -> unit
  val enable_warnings : unit -> unit
  val set_timeout : real -> unit

  val ttt : tactic
  val tactictoe : term -> thm

end
