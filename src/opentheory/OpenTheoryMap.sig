signature OpenTheoryMap =
sig
  structure Map : Redblackmap

  type otname    = string list * string
  type 'a to_ot  = ('a,otname) Map.dict
  type 'a from_ot= (otname,'a) Map.dict
  val otname_to_string : otname -> string
  val string_to_otname : string -> otname
  val otname_cmp : otname * otname -> order

  type thy_tyop  = {Thy:string,Tyop:string}
  type thy_const = {Thy:string,Name:string}
  val thy_tyop_cmp  : thy_tyop  * thy_tyop  -> order
  val thy_const_cmp : thy_const * thy_const -> order

  val temp_OpenTheory_tyop_name  : {tyop :thy_tyop , name:otname} -> unit
  val temp_OpenTheory_const_name : {const:thy_const, name:otname} -> unit
  val OpenTheory_tyop_name  : {tyop :thy_tyop , name:otname} -> unit
  val OpenTheory_const_name : {const:thy_const, name:otname} -> unit

  val tyop_to_ot_map   : unit -> thy_tyop to_ot
  val tyop_from_ot_map : unit -> thy_tyop from_ot
  val const_to_ot_map  : unit -> thy_const to_ot
  val const_from_ot_map: unit -> thy_const from_ot
end
