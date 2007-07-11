signature assemblerML =
sig
   val register2int    : Data.register -> int
   val register2int_   : Data.register_ -> int
   val int2register    : int -> Data.register
   val int2register_   : int -> Data.register_

   val num_to_arm      : Arbnum.num -> Data.instruction
   val num_to_thumb    : Arbnum.num -> Data.instruction
   val arm_to_num      : Data.instruction -> Arbnum.num
   val arm_to_string   : Arbnum.num option -> bool -> Data.instruction -> string
   val string_to_arm   : string -> Data.instruction
   val branch_to_arm   : Data.condition * bool * Arbnum.num ->
                         Arbnum.num -> Data.instruction
   val branch_to_thumb : Data.condition * bool * Arbnum.num ->
                         Arbnum.num -> Data.instruction

   val encode_arm      : string -> Arbnum.num

   val decode_arm       : Arbnum.num option -> Arbnum.num -> string
   val decode_arm_dec   : Arbnum.num option -> string -> string
   val decode_arm_hex   : Arbnum.num option -> string -> string
   val decode_thumb     : Arbnum.num option -> Arbnum.num -> string
   val decode_thumb_dec : Arbnum.num option -> string -> string
   val decode_thumb_hex : Arbnum.num option -> string -> string


   val assembler_to_string  : Arbnum.num option -> Data.assembler ->
                              string option -> string
   val string_to_code       : string -> Data.assembler list
   val parse_arm            : string -> Data.assembler list
   val validate_instruction : Data.instruction -> Data.instruction
end
