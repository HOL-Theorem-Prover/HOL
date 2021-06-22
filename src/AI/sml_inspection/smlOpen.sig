signature smlOpen =
sig
  (* Functions called in the generated script which opens the structures *)
   val sml_cleanval : unit -> unit
   val sml_cleanstruct : string -> unit
   val sml_exportstruct : string -> unit

  (* Shows identifiers in a structure: 
     values, expressions, constructors, and substructures *)
  val view_struct :
    string -> (string list * string list * string list * string list)
  val view_struct_cached :
    string -> (string list * string list * string list * string list)

end
