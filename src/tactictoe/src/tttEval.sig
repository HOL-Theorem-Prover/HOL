signature tttEval =
sig

  include Abbrev

  type tnn = mlTreeNeuralNetwork.tnn
  type nnfiles = string option * string option * string option

  val ttt_eval : mlThmData.thmdata * mlTacticData.tacdata ->
    tnn option * tnn option * tnn option ->
    goal -> unit

  val write_evalscript : string -> nnfiles -> string -> unit
  val run_evalscript : string -> string -> nnfiles -> string -> unit
  val run_evalscript_thyl : string -> string -> bool * int -> 
    nnfiles -> string list -> unit

  (* statistics *)
  val cumul_graph : real -> string -> unit
  val compare_stats : string list -> string -> unit

end
