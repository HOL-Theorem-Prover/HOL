signature ThmAttribute =
sig

  type attrfun = {name:string,attrname:string,thm:Thm.thm} -> unit
  val register_attribute : string * attrfun -> unit

  val store_at_attribute : attrfun
  val extract_attributes : string -> string * string list


end
