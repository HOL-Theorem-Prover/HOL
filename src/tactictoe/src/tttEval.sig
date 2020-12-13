signature tttEval =
sig

  include Abbrev

  type tnn = mlTreeNeuralNetwork.tnn
  type nnfiles = string option * string option * string option

  val export_pb_flag : bool ref

  val prepare_global_data : (string * int) -> unit
  val ttt_eval : string -> (string * int) -> 
    mlThmData.thmdata * mlTacticData.tacdata ->
    tnn option * tnn option * tnn option ->
    goal -> unit

  val write_evalscript : string -> string -> nnfiles -> string -> unit
  val run_evalscript : string -> string -> nnfiles -> string -> unit
  val run_evalscript_thyl : string -> string -> bool * int ->
    nnfiles -> string list -> unit

  (* statistics *)
  val cumul_graph : real -> string -> unit
  val compare_stats : string list -> string -> unit

  (* reinforcement learning for the value *)
  val rlvalue : string -> string list -> int -> unit
  val rlvalue_loop: string -> string list -> int * int -> unit

end
