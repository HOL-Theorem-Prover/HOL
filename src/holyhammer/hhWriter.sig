signature hhWriter =
sig

  val thm_of_depid     : Dep.depid -> (string * Thm.thm)

  val write_hh_thyl    : string -> string list -> unit
  val write_conjecture : string -> term -> unit
  val write_thydep     : string -> string list -> unit

  val writehh_names    : (Dep.depid, string) Redblackmap.dict ref
  val readhh_names     : (string, Dep.depid) Redblackmap.dict ref
  val reserved_names_escaped : string list

end
