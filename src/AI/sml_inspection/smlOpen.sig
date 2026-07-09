signature smlOpen =
sig
  val open_dir : string ref
  val openscript_dir : string ref
  val openscript_run_dir : string option ref
  val openscript_includes : string list ref

  exception OpenStruct of string * exn

  (* functions called in the generated script which opens a structure *)
   val sml_cleanval : unit -> unit
   val sml_cleanstruct : string -> unit
   val sml_exportstruct : string -> unit

  (* shows values, exceptions, constructors, and substructures *)
  val view_struct :
    string -> (string list * string list * string list * string list)
  val view_struct_in_context :
    {dir : string, includes : string list} -> string ->
    (string list * string list * string list * string list)
  (* used by tactictoe: cached files in sml_inspection/open *)
  val view_struct_cached :
    string -> (string list * string list * string list * string list)
  val view_struct_cached_in_context :
    {dir : string, includes : string list} -> string ->
    (string list * string list * string list * string list)

end
