signature hhWriter =
sig

  val write_hh_thyl    : string -> string list -> unit
  val write_conjecture : string -> term -> unit
  val write_thydep     : string -> string list -> unit

  val minimize_flag    : bool ref
  val replay_atpfile   : (string * string) -> term -> unit
  val replay_atpfilel  : (string * string) list -> term -> unit

  val writehh_names    : (Dep.depid, string) Redblackmap.dict ref
  val readhh_names     : (string, Dep.depid) Redblackmap.dict ref

end
