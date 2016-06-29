signature tailbuffer =
sig

  type t
  val new : {numlines : int, patterns : string list} -> t
  val append : string -> t -> t
  val output : t -> {fulllines : string list, lastpartial : string,
                     patterns_seen: string list}
  val last_line : t -> string option

end
