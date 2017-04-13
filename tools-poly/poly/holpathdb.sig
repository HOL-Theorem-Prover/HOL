signature holpathdb =
sig

  val lookup_holpath : {vname : string} -> string option
  val extend_db : {vname: string, path : string} -> unit
  val reverse_lookup : {path : string} -> string
  val subst_pathvars : string -> string
                  (* may complain to stdErr about malformed variable things *)

end
