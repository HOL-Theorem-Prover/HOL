signature machine_ieeeLib =
sig
   val mk_fp_encoding: string * int * int * string option -> Thm.thm list
end
