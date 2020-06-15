signature tttEval =
sig

  include Abbrev
  type tnn =  mlTreeNeuralNetwork.tnn

  val ttt_eval : (mlThmData.thmdata * mlTacticData.tacdata) * tnn option -> 
    goal -> unit  

  val write_evalscript : tnn option -> string -> unit
  val run_evalscript : string -> tnn option -> string -> unit
  val run_evalscript_thyl : string -> bool * tnn option * int -> 
    string list -> unit

  (* statistics *)
  val cumul_graph : real -> string -> unit


end
