signature tacticToe =
sig

  include Abbrev
  
  val main_tactictoe : (mlThmData.thmdata * mlTacticData.tacdata) * 
    mlTreeNeuralNetwork.tnn option -> 
    goal -> tttSearch.proofstatus * tttSearch.tree
  val set_timeout : real -> unit
  val clean_ttt_tacdata_cache : unit -> unit
  val ttt : tactic
  val tactictoe : term -> thm

end
