signature OpenTheoryMap =
sig
  structure Map : Redblackmap

  type thy_tyop  = {Thy:string,Tyop:string}
  type thy_const = {Thy:string,Name:string}
  type 'a to_ot  = ('a,string) Map.dict
  type 'a from_ot= (string,'a) Map.dict

  val temp_OpenTheory_tyop_name  : {tyop :thy_tyop , name:string} -> unit
  val temp_OpenTheory_const_name : {const:thy_const, name:string} -> unit
  val OpenTheory_tyop_name  : {tyop :thy_tyop , name:string} -> unit
  val OpenTheory_const_name : {const:thy_const, name:string} -> unit

  val tyop_to_ot_map   : unit -> thy_tyop to_ot
  val tyop_from_ot_map : unit -> thy_tyop from_ot
  val const_to_ot_map  : unit -> thy_const to_ot
  val const_from_ot_map: unit -> thy_const from_ot
end
