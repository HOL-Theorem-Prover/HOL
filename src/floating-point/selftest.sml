open HolKernel boolLib testutils bossLib binary_ieeeLib

local open fp64Syntax in end
open fp16Syntax

val _ = tprint "mk_fp_isZero(16) has correct rator"
val _ = require_msg (check_result (same_const “machine_ieee$fp16_isZero”))
                    term_to_string
                    (rator o mk_fp_isZero) (mk_var("x", “:word16”))

val f14 =
  “<| Sign := 0w; Exponent := 130w; Significand := 0x600000w |> : (23,8)float”
val f3 =
  “<| Sign := 0w; Exponent := 128w; Significand := 0x400000w |> : (23,8)float”

val _ = tprint "float_add 14 + 3"
val _ = require_msg (check_result (aconv “17r”))
                    term_to_string
                    (rhs o concl o EVAL)
                    “float_to_real $ SND $ float_add roundTiesToEven ^f14 ^f3”

val _ = tprint "float_add 14 + -3"
val _ = require_msg (check_result (aconv “11r”))
                    term_to_string
                    (rhs o concl o EVAL)
                    “float_to_real $ SND $
                       float_add roundTiesToEven ^f14 (float_negate ^f3)”
