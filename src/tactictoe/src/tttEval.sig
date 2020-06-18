signature tttEval =
sig

  include Abbrev
  type tnn =  mlTreeNeuralNetwork.tnn

  val ttt_eval : (mlThmData.thmdata * mlTacticData.tacdata) * tnn option -> 
    goal -> unit  

  val write_evalscript : string option -> string -> unit
  val run_evalscript : string -> string option -> string -> unit
  val run_evalscript_thyl : string -> bool * string option * int -> 
    string list -> unit

  (* statistics *)
  val cumul_graph : real -> string -> unit
  val compare_stats : string list -> string -> unit

  (* training *)
  val train_value : real -> string -> tnn
  val train_policy : real -> string -> tnn

end
