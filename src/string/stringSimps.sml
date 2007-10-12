structure stringSimps :> stringSimps =
struct

open HolKernel boolLib simpLib stringTheory stringLib;

val char_rewrites = [CHR_ORD];

val SSFRAG { rewrs = string_rewrites, ...} = stringTheory.string_rwts

val STRING_ss = stringTheory.string_rwts


end

