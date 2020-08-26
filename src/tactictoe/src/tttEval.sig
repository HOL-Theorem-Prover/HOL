signature tttEval =
sig

  include Abbrev

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

end
