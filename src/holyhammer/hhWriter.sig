signature hhWriter =
sig

  val thm_of_depid     : Dep.depid -> (string * Thm.thm)

  val write_hh_thyl    : string -> string list -> unit
  val write_conjecture : string -> term -> unit
  val write_thydep     : string -> string list -> unit
  val write_hh_thml    : string -> string -> string list -> (string * Thm.thm) list -> unit

  val reserved_names_escaped : string list

end
