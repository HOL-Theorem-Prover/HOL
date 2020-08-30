signature tttBigSteps =
sig

  include Abbrev

  type ex = (term * real) list
  type tnn = mlTreeNeuralNetwork.tnn

  datatype bstatus = BigStepsProved | BigStepsSaturated | BigStepsTimeout
    
  val run_bigsteps : tttSearch.searchobj -> goal -> bstatus * (ex * ex * ex)

  val run_bigsteps_eval :  string * int ->
    mlThmData.thmdata * mlTacticData.tacdata -> tnn option * 'tnn option -> 
    goal -> unit

end
