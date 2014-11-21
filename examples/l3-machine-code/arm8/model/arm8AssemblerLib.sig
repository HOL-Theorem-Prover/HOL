signature arm8AssemblerLib =
sig
   val arm8_code: string quotation -> string list
   val arm8_disassemble: string quotation -> string list
   val instructionEncode: arm8.instruction -> arm8.MachineCode
   val m32 : Term.term
   val m64 : Term.term
   val print_arm8_code: string quotation -> unit
   val print_arm8_disassemble: string quotation -> unit
end
