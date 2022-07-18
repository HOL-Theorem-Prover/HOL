open HolKernel boolLib testutils

local open fp64Syntax in end
open fp16Syntax

val _ = tprint "mk_fp_isZero(16) has correct rator"
val _ = require_msg (check_result (same_const “machine_ieee$fp16_isZero”))
                    term_to_string
                    (rator o mk_fp_isZero) (mk_var("x", “:word16”))
