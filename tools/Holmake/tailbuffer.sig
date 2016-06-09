signature tailbuffer =
sig

  type t
  val new : {numlines : int, pattern : string option} -> t
  val append : string -> t -> t
  val output : t -> {fulllines : string list, lastpartial : string,
                     pattern_seen: bool}
  val last_line : t -> string option

end
