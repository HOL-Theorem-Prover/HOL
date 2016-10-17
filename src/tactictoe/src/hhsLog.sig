signature hhsLog =
sig

  include Abbrev
  val readl        : string -> string list
  val append_file  : string -> string -> unit
  val hhs_log      : string -> string -> unit
  val hhs_print    : string -> unit
  val hhs_time     : string -> ('a -> 'b) -> 'a -> 'b
  val hhs_add_time : ('a -> 'b) -> 'a -> ('b * real)

end
