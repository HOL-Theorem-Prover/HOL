signature arm_disassemblerLib =
sig

  val arm_disassemble : arm_parserLib.arm_code -> string * string

end
