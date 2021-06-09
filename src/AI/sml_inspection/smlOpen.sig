signature smlOpen =
sig

  val core_theories : string list
  val theory_files : string -> string list
  val find_heapname : string -> string -> string
  val find_genscriptdep : string -> string -> string list
  val run_buildheap : string -> bool -> string -> unit
  val run_buildheap_nodep : string -> string -> unit
  val buildheap_options : string ref

  val run_rm_script : bool -> string -> unit

  val sml_cleanval : unit -> unit
  val sml_cleanstruct : string -> unit
  val sml_export : string -> unit

  val export_struct : string -> unit
  val import_struct :
    string -> (string list * string list * string list * string list)
  val export_import_struct :
    string -> (string list * string list * string list * string list)

end
