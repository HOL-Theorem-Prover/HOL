signature armLib =
sig

  include arm_parserLib where
    type arm_code = arm_parserLib.arm_code

  include arm_encoderLib arm_disassemblerLib arm_stepLib

  val arm_decode     : string -> arm_code
  val thumb_decode   : int -> string -> arm_code
  val thumbee_decode : int -> string -> arm_code

  val arm_disassemble_decode     : string -> string
  val thumb_disassemble_decode   : int -> string -> string
  val thumbee_disassemble_decode : int -> string -> string

  val arm_steps_from_quote  : string -> string frag list ->
                              (Abbrev.thm * Abbrev.thm option) list

  val arm_steps_from_string : string -> string ->
                              (Abbrev.thm * Abbrev.thm option) list

  val arm_steps_from_file   : string -> string ->
                              (Abbrev.thm * Abbrev.thm option) list

  val print_arm_assemble_from_quote  : string -> string frag list -> unit
  val print_arm_assemble_from_string : string -> string -> unit
  val print_arm_assemble_from_file   : string -> string -> unit

  val arm_assemble_to_file_from_quote  : string -> string ->
                                         string frag list -> unit
  val arm_assemble_to_file_from_string : string -> string -> string -> unit
  val arm_assemble_to_file_from_file   : string -> string -> string -> unit

(* ------------------------------------------------------------------------

   Usage (see "EXAMPLES"):

   encode AST to machine code (HEX string):
     arm_encode <code>

   decode machine code (HEX string) to AST:
     arm_decode <hex>
     thumb_decode <IT value> <hex>

   disassamble AST to assembler:
     arm_disassemble <code>

   decode to assembler:
     arm_disassemble_decode   <hex>
     thumb_disassemble_decode <IT value> <hex>

   encode assembler to byte position and machine code (HEX string):
     arm_assemble_from_file   <filename>
     arm_assemble_from_quote  <quotation>
     arm_assemble_from_string <string>

   encode assembler and print to screen:
     print_arm_assemble_from_file   <start address> <filename>
     print_arm_assemble_from_quote  <start address> <quotation>
     print_arm_assemble_from_string <start address> <string>

   encode assembler and save to file:
     arm_assemble_to_file_from_file   <start address> <output file> <input file>
     arm_assemble_to_file_from_quote  <start address> <output file> <quotation>
     arm_assemble_to_file_from_string <start address> <output file> <string>

   parse assembler to byte position and AST list:
     arm_parse_from_file   <filename>
     arm_parse_from_quote  <quotation>
     arm_parse_from_string <string>

   derive next step theorem for machine code (HEX string):
     arm_step <options> <hex>

   derive next step theorems for assembly code:
     arm_steps_from_file   <options> <filename>
     arm_steps_from_quote  <options> <quotation>
     arm_steps_from_string <options> <string>

   Trace variables:

     "add disassembler comments"
       - controls output for print_arm_assemble_from_file etc.

     "arm step"
       - controls feedback for arm_step

     "arm steps"
       - controls feedback for arm_steps

     "label arm steps"
       - controls theorem tagging for arm_steps

   ------------------------------------------------------------------------ *)

end
