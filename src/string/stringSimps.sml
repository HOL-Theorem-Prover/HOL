structure stringSimps :> stringSimps =
struct

open HolKernel boolLib simpLib stringTheory stringLib;

val char_rewrites = [CHR_ORD];
val string_rwts = BasicProvers.thy_ssfrag "string"

val SSFRAG { rewrs = string_rewrites, ...} = string_rwts

val STRING_ss = string_rwts


end

