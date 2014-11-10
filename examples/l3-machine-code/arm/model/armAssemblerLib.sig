signature armAssemblerLib =
sig
   val init: unit -> unit
   val arm_code: string quotation -> string list
   val arm_code_with_warnings:
      string quotation -> string list * assemblerLib.lines
   val arm_disassemble: string quotation -> string list
   val print_arm_code: string quotation -> unit
   val print_arm_disassemble: string quotation -> unit
end
