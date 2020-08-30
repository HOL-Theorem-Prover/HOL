signature tttEval =
sig

  include Abbrev

  type tnn = mlTreeNeuralNetwork.tnn
  type pvfiles = string option * string option

  val ttt_eval : (mlThmData.thmdata * mlTacticData.tacdata) ->
    tnn option * tnn option ->
    goal -> unit

  val write_evalscript : string -> pvfiles -> string -> unit
  val run_evalscript : string -> string -> pvfiles -> string -> unit
  val run_evalscript_thyl : string -> string -> bool * int -> 
    pvfiles -> string list -> unit

  (* statistics *)
  val cumul_graph : real -> string -> unit
  val compare_stats : string list -> string -> unit

end
