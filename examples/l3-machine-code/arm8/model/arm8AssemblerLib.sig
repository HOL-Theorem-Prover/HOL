signature arm8AssemblerLib =
sig
   val arm8_code: string quotation -> string list
   val arm8_disassemble: string quotation -> string list
   val print_arm8_code: string quotation -> unit
   val print_arm8_disassemble: string quotation -> unit
end
