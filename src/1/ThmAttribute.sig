signature ThmAttribute =
sig

  type attrfun = {name:string,attrname:string,thm:Thm.thm} -> unit
  type attrfuns = {localf : attrfun, storedf : attrfun}
  val register_attribute : string * attrfuns -> unit

  val is_attribute : string -> bool
  val all_attributes : unit -> string list
  val store_at_attribute : attrfun
  val local_attribute    : attrfun
  val extract_attributes : string -> string * string list
  val toString : string * string list -> string

  val insert_attribute : {attr: string} -> string -> string

end

(*
   [extract_attributes thmstr] takes a string of the form
   thmname[attr1,attr2,...] or of the form thmname and returns the thmname
   along with the list of attributes.

   [toString thmname attrs] reverses the extract_attributes function above.
*)
