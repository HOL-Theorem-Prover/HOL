signature HM_Progress =
sig

  val init : (string -> unit) -> int -> unit
  val note_completion : 'a HM_DepGraph.t -> bool -> HM_DepGraph.command ->
                        string option

end
