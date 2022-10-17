open HolKernel boolLib testutils bossLib binary_ieeeLib

local open fp64Syntax in end
open fp16Syntax

val _ = tprint "mk_fp_isZero(16) has correct rator"
val _ = require_msg (check_result (same_const “machine_ieee$fp16_isZero”))
                    term_to_string
                    (rator o fp16Syntax.mk_fp_isZero) (mk_var("x", “:word16”))

val f14 =
  “<| Sign := 0w; Exponent := 130w; Significand := 0x600000w |> : (23,8)float”
val f3 =
  “<| Sign := 0w; Exponent := 128w; Significand := 0x400000w |> : (23,8)float”
val f6 =
  “<| Sign := 0w; Exponent := 129w; Significand := 0x400000w |> : (23,8)float”

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

val _ = tprint "fma 14 * 3 + 6"
val _ = require_msg (check_result (aconv “48r”))
                    term_to_string
                    (rhs o concl o EVAL)
                    “float_to_real $ SND $
                       float_mul_add roundTiesToEven ^f14 ^f3 ^f6”

(* IBM's FPgen has: b32*+ =0 i +1.000000P-126 -1.2801D9P-113 -Zero -> -Zero xu
    -- via Michael Roe on https://github.com/HOL-Theorem-Prover/HOL/issues/1011
*)
val fma1 = “<| Sign := 0w; Exponent := 1w; Significand := 0w |> : (23,8)float”
val fma2 =
  “<| Sign := 1w; Exponent := 14w; Significand := 0x2801d9w |> : (23,8)float”
val fma3 =
  “<| Sign := 1w; Exponent := 0w; Significand := 0x0w |> : (23,8)float”;
val neg0 = fma3

val _ = tprint "fma signedness of zeroes (1)"
val _ = require_msg (check_result (aconv neg0)) term_to_string
                    (rhs o concl o EVAL)
                    “SND $ float_mul_add roundTiesToEven ^fma1 ^fma2 ^fma3”;
