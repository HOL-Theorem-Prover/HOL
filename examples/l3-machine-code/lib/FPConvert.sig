signature FPConvert =
sig
   val fp32_to_fp64: BitsN.nbit -> BitsN.nbit
   val fp64_to_fp32: IEEEReal.rounding_mode * BitsN.nbit -> BitsN.nbit
end
