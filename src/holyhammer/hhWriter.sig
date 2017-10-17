signature hhWriter =
sig

  include Abbrev

  val hh_escape        : string -> string
  val thm_of_depid     : Dep.depid -> (string * Thm.thm)

  val write_thyl       : string -> (string * string) list -> string list -> unit
  val write_conjecture : string -> term -> unit
  val write_thydep     : string -> string list -> unit

  val reserved_names   : string list

end
