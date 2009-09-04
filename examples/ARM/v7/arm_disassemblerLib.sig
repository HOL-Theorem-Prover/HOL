signature arm_disassemblerLib =
sig

  val arm_disassemble : arm_parserLib.arm_code -> string * string

  val arm_disassemble_from_file   : string -> (string * string) list

  val arm_disassemble_from_string : string -> (string * string) list

  val arm_disassemble_from_quote  : string frag list -> (string * string) list

end
