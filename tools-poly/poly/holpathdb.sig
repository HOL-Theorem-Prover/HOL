signature holpathdb =
sig

  val lookup_holpath : {vname : string} -> string option
  val extend_db : {vname: string, path : string} -> unit
  val reverse_lookup : {path : string} -> string
  val subst_pathvars : string -> string
                  (* may complain to stdErr about malformed variable things *)
  val search_for_extensions : (string -> string list) -> string list ->
                              {vname:string, path:string} list

end
