structure machine_ieeeSyntax :> machine_ieeeSyntax =
struct

structure fp16Syntax =
   fpSyntax (val thy = "machine_ieee"
             val fp = "fp16"
             val ty = ``:word16``)

structure fp32Syntax =
   fpSyntax (val thy = "machine_ieee"
             val fp = "fp32"
             val ty = ``:word32``)

structure fp64Syntax =
   fpSyntax (val thy = "machine_ieee"
             val fp = "fp64"
             val ty = ``:word64``)

val (fp32_to_fp64_tm, mk_fp32_to_fp64, dest_fp32_to_fp64, is_fp32_to_fp64) =
   HolKernel.syntax_fns1 "machine_ieee" "fp32_to_fp64"

val (fp64_to_fp32_tm, mk_fp64_to_fp32, dest_fp64_to_fp32, is_fp64_to_fp32) =
   HolKernel.syntax_fns2 "machine_ieee" "fp64_to_fp32"

end
