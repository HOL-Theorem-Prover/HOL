structure machine_ieeeSyntax :> machine_ieeeSyntax =
struct

open HolKernel Parse boolLib bossLib
open machine_ieeeTheory

val (fp16_to_fp32_tm, mk_fp16_to_fp32, dest_fp16_to_fp32, is_fp16_to_fp32) =
   HolKernel.syntax_fns1 "machine_ieee" "fp16_to_fp32"

val (fp16_to_fp64_tm, mk_fp16_to_fp64, dest_fp16_to_fp64, is_fp16_to_fp64) =
   HolKernel.syntax_fns1 "machine_ieee" "fp16_to_fp64"

val (fp32_to_fp64_tm, mk_fp32_to_fp64, dest_fp32_to_fp64, is_fp32_to_fp64) =
   HolKernel.syntax_fns1 "machine_ieee" "fp32_to_fp64"

val (fp16_to_fp32_with_flags_tm, mk_fp16_to_fp32_with_flags,
     dest_fp16_to_fp32_with_flags, is_fp16_to_fp32_with_flags) =
   HolKernel.syntax_fns1 "machine_ieee" "fp16_to_fp32_with_flags"

val (fp16_to_fp64_with_flags_tm, mk_fp16_to_fp64_with_flags,
     dest_fp16_to_fp64_with_flags, is_fp16_to_fp64_with_flags) =
   HolKernel.syntax_fns1 "machine_ieee" "fp16_to_fp64_with_flags"

val (fp32_to_fp64_with_flags_tm, mk_fp32_to_fp64_with_flags,
     dest_fp32_to_fp64_with_flags, is_fp32_to_fp64_with_flags) =
   HolKernel.syntax_fns1 "machine_ieee" "fp32_to_fp64_with_flags"

val (fp64_to_fp32_tm, mk_fp64_to_fp32, dest_fp64_to_fp32, is_fp64_to_fp32) =
   HolKernel.syntax_fns2 "machine_ieee" "fp64_to_fp32"

val (fp64_to_fp16_tm, mk_fp64_to_fp16, dest_fp64_to_fp16, is_fp64_to_fp16) =
   HolKernel.syntax_fns2 "machine_ieee" "fp64_to_fp16"

val (fp32_to_fp16_tm, mk_fp32_to_fp16, dest_fp32_to_fp16, is_fp32_to_fp16) =
   HolKernel.syntax_fns2 "machine_ieee" "fp32_to_fp16"

val (fp64_to_fp32_with_flags_tm, mk_fp64_to_fp32_with_flags,
     dest_fp64_to_fp32_with_flags, is_fp64_to_fp32_with_flags) =
   HolKernel.syntax_fns2 "machine_ieee" "fp64_to_fp32_with_flags"

val (fp64_to_fp16_with_flags_tm, mk_fp64_to_fp16_with_flags,
     dest_fp64_to_fp16_with_flags, is_fp64_to_fp16_with_flags) =
   HolKernel.syntax_fns2 "machine_ieee" "fp64_to_fp16_with_flags"

val (fp32_to_fp16_with_flags_tm, mk_fp32_to_fp16_with_flags,
     dest_fp32_to_fp16_with_flags, is_fp32_to_fp16_with_flags) =
   HolKernel.syntax_fns2 "machine_ieee" "fp32_to_fp16_with_flags"

end
