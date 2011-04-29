structure stringSimps :> stringSimps =
struct

open HolKernel boolLib simpLib stringTheory stringLib;

val char_rewrites = [CHR_ORD];
val STRING_ss = BasicProvers.thy_ssfrag "string"
val string_rewrites = frag_rewrites STRING_ss

end

