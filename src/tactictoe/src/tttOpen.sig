signature tttOpen =
sig

  val core_theories : string list
  val theory_files : string -> string list
  val find_heapname : string -> string
  val find_genscriptdep : string -> string list
  val run_buildheap : bool -> string -> unit
  val run_rm_script : bool -> string -> unit

  val tactictoe_cleanval : unit -> unit
  val tactictoe_cleanstruct : string -> unit
  val tactictoe_export : string -> unit

  val export_struct : string -> string -> unit
  val import_struct :
    string -> (string list * string list * string list * string list)
  val export_import_struct :
    string -> string ->
    (string list * string list * string list * string list)

end
