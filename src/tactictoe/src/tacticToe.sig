signature tacticToe =
sig

  include Abbrev

  type tnn = mlTreeNeuralNetwork.tnn

  val main_tactictoe :
    mlThmData.thmdata * mlTacticData.tacdata ->
    tnn option * tnn option ->
    goal -> tttSearch.proofstatus * tttSearch.tree
  
  val build_searchobj : mlThmData.thmdata * mlTacticData.tacdata ->
    tnn option * tnn option ->
    goal -> tttSearch.searchobj

  val main_tactictoe_mini :
    mlThmData.thmdata ->
    tnn option * tnn option ->
    goal -> tttSearch.proofstatus * tttSearch.tree

  val clean_ttt_tacdata_cache : unit -> unit
  val set_timeout : real -> unit

  val ttt : tactic
  val tactictoe : term -> thm

  val ttt_mini : tactic
  val tactictoe_mini : term -> thm

end
