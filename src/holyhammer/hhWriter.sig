signature hhWriter =
sig

  include Abbrev

  val write_thyl       :
    string ->
    (string -> (string * thm) * string -> bool) ->
    string list ->
    unit
  val write_problem    :
    string ->
    (string -> (string * thm) * string -> bool) ->
    (string * thm) list ->
    string list ->
    term ->
    unit

  val write_thydep     : string -> string list -> unit
  val reserved_names   : string list

end
