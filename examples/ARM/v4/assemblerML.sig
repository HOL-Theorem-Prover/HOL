signature assemblerML =
sig
   val register2int   : Data.register -> int
   val int2register   : int -> Data.register

   val num_to_arm     : Arbnum.num -> Data.instruction
   val arm_to_num     : Data.instruction -> Arbnum.num
   val arm_to_string  : Arbnum.num option -> bool -> Data.instruction -> string
   val string_to_arm  : string -> Data.instruction
   val branch_to_arm  : Data.condition * bool * Arbnum.num ->
                        Arbnum.num -> Data.instruction

   val encode_arm             : string -> Arbnum.num
   val decode_arm             : Arbnum.num option -> Arbnum.num -> string
   val decode_arm_dec         : Arbnum.num option -> string -> string
   val decode_arm_hex         : Arbnum.num option -> string -> string

   val assembler_to_string    : Arbnum.num option -> Data.assembler ->
                                string option -> string
   val string_to_code         : string -> Data.assembler list
   val parse_arm              : string -> Data.assembler list
   val validate_instruction   : Data.instruction -> Data.instruction
end
