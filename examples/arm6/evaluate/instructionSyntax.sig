signature instructionSyntax =
sig
   include Abbrev

   val num_to_arm     : Arbnum.num -> Data.instruction
   val arm_to_num     : Data.instruction -> Arbnum.num
   val arm_to_string  : Arbnum.num option -> bool -> Data.instruction -> string
   val string_to_arm  : string -> Data.instruction
   val arm_to_term    : Data.instruction -> term
   val term_to_arm    : term -> Data.instruction
   val branch_to_arm  : Data.condition * bool * Arbnum.num ->
                        Arbnum.num -> Data.instruction

   val encode_arm             : string -> Arbnum.num
   val decode_arm             : Arbnum.num option -> Arbnum.num -> string
   val decode_arm_dec         : Arbnum.num option -> string -> string
   val decode_arm_hex         : Arbnum.num option -> string -> string

   val encode_instruction     : term -> Arbnum.num
   val decode_instruction     : Arbnum.num -> term
   val decode_instruction_dec : string -> term
   val decode_instruction_hex : string -> term

   val mk_instruction         : string -> term
   val dest_instruction       : Arbnum.num option -> term -> string

   val assembler_to_string    : Arbnum.num option -> Data.assembler ->
                                string option -> string
   val parse_arm_buf          : Lexing.lexbuf -> Data.assembler list
   val parse_arm              : string -> Data.assembler list
   val validate_instruction   : Data.instruction -> Data.instruction
end
