structure FPConvert :> FPConvert =
struct
  fun err s = raise Fail (s ^ ": not supported")

  fun fp32_to_fp64 _ = err "fp32_to_fp64"
  fun fp64_to_fp32 _ = err "fp64_to_fp32"
end (* FPConvert *)
