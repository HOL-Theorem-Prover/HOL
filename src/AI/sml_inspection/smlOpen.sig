signature smlOpen =
sig
  (* directory the generated open-script is run from, and the extra
     INCLUDES it needs; both default to the scratch openscript directory *)
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
  (* used by tactictoe: cached files under aiLib.scratch_dir *)
  val view_struct_cached :
    string -> (string list * string list * string list * string list)

end
