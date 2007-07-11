signature instructionSyntax =
sig
   include Abbrev

   val arm_to_term    : Data.instruction -> term
   val term_to_arm    : term -> Data.instruction

   val encode_instruction      : term -> Arbnum.num

   val decode_instruction      : Arbnum.num -> term
   val decode_instruction_dec  : string -> term
   val decode_instruction_hex  : string -> term

   val decode_instruction_     : Arbnum.num -> term
   val decode_instruction_dec_ : string -> term
   val decode_instruction_hex_ : string -> term

   val mk_instruction          : string -> term
   val dest_instruction        : Arbnum.num option -> term -> string
end
