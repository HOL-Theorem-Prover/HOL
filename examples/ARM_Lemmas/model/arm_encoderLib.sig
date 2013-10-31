signature arm_encoderLib =
sig

  val arm_encode               : arm_parserLib.arm_code -> string

  val arm_encode_from_string   : string -> string

  val arm_assemble_from_file   : string -> (Arbnum.num * string) list *
                                           (string, Arbnum.num) Redblackmap.dict

  val arm_assemble_from_string : string -> (Arbnum.num * string) list *
                                           (string, Arbnum.num) Redblackmap.dict

  val arm_assemble_from_quote  : string frag list ->
                                   (Arbnum.num * string) list *
                                   (string, Arbnum.num) Redblackmap.dict

end
