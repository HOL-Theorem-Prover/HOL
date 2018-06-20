structure numeralConvLib :> numeralConvLib = struct

open HolKernel boolLib numSyntax numeralConvTheory

val refl_zero = REFL zero_tm

val SUC_0 =
  BIT1_def |> SPEC zero_tm
  |> CONV_RULE(RAND_CONV(RAND_CONV(REWR_CONV BIT0_0)))
  |> SYM

val SUC_BIT0 = GSYM BIT1_def

val SUC_BIT1 =
  BIT0_SUC |> GSYM
  |> CONV_RULE(QUANT_CONV(LAND_CONV(RAND_CONV(REWR_CONV SUC_BIT0))))

val BIT2_def =
  numeralTheory.numeral_suc
  |> CONJUNCTS |> el 2 |> GSYM

fun binc tm = tm |> (
  (REWR_CONV SUC_0) ORELSEC
  (REWR_CONV SUC_BIT0) ORELSEC
  (REWR_CONV SUC_BIT1 THENC (RAND_CONV binc)))

fun to_binary tm =
  if tm = alt_zero_tm then
    arithmeticTheory.ALT_ZERO
  else if is_bit1 tm then
    RAND_CONV to_binary tm
  else
    (RAND_CONV to_binary THENC
     REWR_CONV BIT2_def THENC
     binc) tm

end
