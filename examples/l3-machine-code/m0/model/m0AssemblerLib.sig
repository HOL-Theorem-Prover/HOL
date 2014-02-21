signature m0AssemblerLib =
sig
   val m0_code: 'a frag list -> string list
   val print_m0_code: 'a frag list -> unit
   val thumbCondition: BitsN.nbit -> BitsN.nbit
end
