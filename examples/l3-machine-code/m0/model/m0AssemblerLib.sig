signature m0AssemblerLib =
sig
   val m0_code: string quotation -> string list
   val m0_disassemble: string quotation -> string list
   val print_m0_code: string quotation -> unit
   val print_m0_disassemble: string quotation -> unit
   val thumbCondition: BitsN.nbit -> BitsN.nbit
end
