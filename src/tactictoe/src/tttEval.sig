signature tttEval =
sig

  include Abbrev
  type tnn =  mlTreeNeuralNetwork.tnn
  type pvfiles = string option * string option  

  val ttt_clean_eval : unit -> unit
  val ttt_eval : (mlThmData.thmdata * mlTacticData.tacdata) ->
    tnn option * tnn option -> 
    goal -> unit  

  val write_evalscript : pvfiles -> string -> unit
  val run_evalscript : string -> pvfiles -> string -> unit
  val run_evalscript_thyl : string -> bool * int -> pvfiles -> 
    string list -> unit

  (* statistics *)
  val cumul_graph : real -> string -> unit
  val compare_stats : string list -> string -> unit

  (* training *)
  val train_value : real -> string -> tnn
  val train_policy : real -> string -> tnn

end
