signature mleCombinLibHp =
sig

  include Abbrev

  datatype pose = Left | Right
  val pos_to_string : pose list -> string
  val string_to_pos: string -> pose list
  val pos_compare : pose list * pose list -> order
  val next_pos : pose list -> pose list
  
  datatype combin = V1 | V2 | V3 | S | K | A of combin * combin 
  val combin_to_string : combin -> string
  val string_to_combin : string -> combin
  val combin_compare : combin * combin -> order
  val combin_size : combin -> int
  val strip_A : combin -> combin list
  val list_mk_A : combin list -> combin

  val hp_norm : int -> combin -> combin option 
  val hp_nf : combin -> bool
  val cterm_to_hp : term -> combin
  val hp_to_cterm : combin -> term

  val gen_headnf : int ->
    (combin, combin) Redblackmap.dict ->
    (combin, combin) Redblackmap.dict * int
  
  val export_data : (combin * combin) list * (combin * combin) list -> unit
  val import_data : string -> (combin * combin) list

end
