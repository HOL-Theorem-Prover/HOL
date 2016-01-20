open HolKernel Parse boolLib bossLib;
open arm8_decompLib

val () = new_theory "arm8_decomp_demo";

val (test1_cert, test1_def) = arm8_decompile_no_status "test1"
   `54000048
    1b000001
    `

val (test2_cert, test2_def) = arm8_decompile_code_no_status "test2"
   `mov x1, #4
    add x2, x3, x4
    str x2, [x1, #8]!
    `

val (test3_cert, test3_def) = arm8_decompLib.arm8_decompile_code "test3"
  `loop: mul  x1, x1, x2
         subs x0, x0, #1
         b.ne  loop`

val () = export_theory()
