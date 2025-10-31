Theory machine_ieee
Ancestors
  binary_ieee
Libs
  machine_ieeeLib

(* ------------------------------------------------------------------------
   Bit-vector Encodings
   ------------------------------------------------------------------------ *)

(* 16-bit, 32-bit and 64-bit encodings *)

val thms = (List.concat o List.map machine_ieeeLib.mk_fp_encoding)
   [("fp16", 10, 5, SOME "half"),
    ("fp32", 23, 8, SOME "single"),
    ("fp64", 52, 11, SOME "double")];

(* ------------------------------------------------------------------------
   Encoding conversions
   ------------------------------------------------------------------------ *)

Definition convert_def:
  convert (to_float: 'a word -> ('b, 'c) float)
          (from_float: ('d, 'e) float -> 'f word) from_real_with_flags
          (m: rounding) w =
  let f = to_float w in
  case float_value f of
     Float r => from_real_with_flags m r
   | NaN => (check_for_signalling [f], from_float (@fp. float_is_nan fp))
   | Infinity =>
       (clear_flags,
        from_float (if f.Sign = 0w then
                      float_plus_infinity (:'d # 'e)
                    else
                      float_minus_infinity (:'d # 'e)))
End

(* These can only set InvalidOp *)

Definition fp16_to_fp32_with_flags_def:
  fp16_to_fp32_with_flags =
  convert fp16_to_float float_to_fp32 real_to_fp32_with_flags roundTiesToEven
End

Definition fp16_to_fp64_with_flags_def:
  fp16_to_fp64_with_flags =
  convert fp16_to_float float_to_fp64 real_to_fp64_with_flags roundTiesToEven
End

Definition fp32_to_fp64_with_flags_def:
  fp32_to_fp64_with_flags =
  convert fp32_to_float float_to_fp64 real_to_fp64_with_flags roundTiesToEven
End

(* These can set InvalidOp, Overflow, Precision and Underflow_* *)

Definition fp64_to_fp32_with_flags_def:
  fp64_to_fp32_with_flags =
  convert fp64_to_float float_to_fp32 real_to_fp32_with_flags
End

Definition fp64_to_fp16_with_flags_def:
  fp64_to_fp16_with_flags =
  convert fp64_to_float float_to_fp16 real_to_fp16_with_flags
End

Definition fp32_to_fp16_with_flags_def:
  fp32_to_fp16_with_flags =
  convert fp32_to_float float_to_fp16 real_to_fp16_with_flags
End

(* Versions without flags *)

Definition fp16_to_fp32_def:   fp16_to_fp32 = SND o fp16_to_fp32_with_flags
End
Definition fp16_to_fp64_def:   fp16_to_fp64 = SND o fp16_to_fp64_with_flags
End
Definition fp32_to_fp64_def:   fp32_to_fp64 = SND o fp32_to_fp64_with_flags
End

Definition fp64_to_fp32_def:   fp64_to_fp32 m = SND o fp64_to_fp32_with_flags m
End
Definition fp64_to_fp16_def:   fp64_to_fp16 m = SND o fp64_to_fp16_with_flags m
End
Definition fp32_to_fp16_def:   fp32_to_fp16 m = SND o fp32_to_fp16_with_flags m
End
