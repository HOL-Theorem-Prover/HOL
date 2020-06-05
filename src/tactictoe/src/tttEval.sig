signature tttEval =
sig

  include Abbrev

  val ttt_eval : mlThmData.thmdata * mlTacticData.tacdata -> goal -> unit  

  val write_evalscript : string -> string -> unit
  val run_evalscript : string -> string -> unit
  val run_evalscript_thyl : string -> bool -> int -> string list -> unit

  (* statistics *)
  val cumul_graph : real -> string -> unit


end
