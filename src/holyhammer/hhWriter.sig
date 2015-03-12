signature hhWriter =
sig
  
  val fetch_conj       : (thm * string) -> thm
  val write_thf_thyl   : string -> string list -> unit
  val write_conjecture : string -> term -> unit
  val write_thydep     : string -> string list -> unit
  val replay_atpfile   : (string * string) -> term -> unit
  val replay_atpfilel  : (string * string) list -> term -> unit
  val minimize_flag    : bool ref

end
