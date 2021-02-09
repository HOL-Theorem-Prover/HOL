signature tacticToe =
sig

  include Abbrev

  type tnn = mlTreeNeuralNetwork.tnn

  val build_searchobj : mlThmData.thmdata * mlTacticData.tacdata ->
    tnn option * tnn option * tnn option ->
    goal -> tttSearch.searchobj
  val main_tactictoe :
    mlThmData.thmdata * mlTacticData.tacdata ->
    tnn option * tnn option * tnn option ->
    goal -> tttSearch.proofstatus * tttSearch.tree

  val clean_ttt_tacdata_cache : unit -> unit
  val set_timeout : real -> unit
  val prioritize_stacl : string list ref
  (* tactics on prioritize_stacl are added to tactictoe and
     first tactics on the list are applied first *)

  val ttt : tactic
  val tactictoe : term -> thm


end
