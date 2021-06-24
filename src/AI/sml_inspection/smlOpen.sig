signature smlOpen =
sig
  (* functions called in the generated script which opens a structure *)
   val sml_cleanval : unit -> unit
   val sml_cleanstruct : string -> unit
   val sml_exportstruct : string -> unit

  (* shows values, exceptions, constructors, and substructures *)
  val view_struct :
    string -> (string list * string list * string list * string list)
  (* used by tactictoe: cached files in sml_inspection/open *)
  val view_struct_cached : 
    string -> (string list * string list * string list * string list)

end
