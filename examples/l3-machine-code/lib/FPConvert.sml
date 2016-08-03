structure FPConvert :> FPConvert =
struct
  val fp32_to_fp64 = FP64.fromLargeReal IEEEReal.TO_NEAREST o FP32.toLargeReal
  fun fp64_to_fp32 (m, w) = FP32.fromLargeReal m (FP64.toLargeReal w)
end (* FPConvert *)
