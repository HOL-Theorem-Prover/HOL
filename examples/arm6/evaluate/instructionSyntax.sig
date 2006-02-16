signature instructionSyntax =
sig
   include Abbrev

   val num_to_arm             : Arbnum.num -> Data.instruction
   val arm_to_num             : Data.instruction -> Arbnum.num
   val arm_to_string          : bool -> Data.instruction -> string
   val string_to_arm          : string -> Data.instruction
   val arm_to_term            : Data.instruction -> term
   val term_to_arm            : term -> Data.instruction

   val encode_arm             : string -> Arbnum.num
   val decode_arm             : Arbnum.num -> string
   val decode_arm_dec         : string -> string
   val decode_arm_hex         : string -> string

   val encode_instruction     : term -> Arbnum.num
   val decode_instruction     : Arbnum.num -> term
   val decode_instruction_dec : string -> term
   val decode_instruction_hex : string -> term

   val mk_instruction         : string -> term
   val dest_instruction       : term -> string

   val pp_instruction         : unit -> unit
   val remove_pp_instruction  : unit -> unit
end
