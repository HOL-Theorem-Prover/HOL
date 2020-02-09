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
  val combin_compare : combin * combin -> order
  
  val hp_norm : int -> combin -> combin option 
  val hp_nf : combin -> bool
  val cterm_to_hp : term -> combin
  val hp_to_cterm : combin -> term

  
end
