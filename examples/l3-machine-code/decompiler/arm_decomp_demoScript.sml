
open HolKernel Parse boolLib bossLib;

val _ = new_theory "arm_decomp_demo";

val (result,func) = arm_decompLib.l3_arm_decompile "PID_C" `
            (* ------ PID example ------- *)
  ed907a00  (*  vldr      s14, [r0]       *)
  edd16a00  (*  vldr      s13, [r1]       *)
  ee676a26  (*  vmul.f32  s13, s14, s13   *)
  e3001000  (*  movw      r1, #0          *)
  e3401000  (*  movt      r1, #0          *)
  edd15a00  (*  vldr      s11, [r1]       *)
  ed936a00  (*  vldr      s12, [r3]       *)
  ed925a00  (*  vldr      s10, [r2]       *)
  edd17a01  (*  vldr      s15, [r1, #4]   *)
  e59d3000  (*  ldr       r3, [sp]        *)
  ed817a00  (*  vstr      s14, [r1]       *)
  ee775a65  (*  vsub.f32  s11, s14, s11   *)
  ee477a05  (*  vmla.f32  s15, s14, s10   *)
  ee456a86  (*  vmla.f32  s13, s11, s12   *)
  edc17a01  (*  vstr      s15, [r1, #4]   *)
  ee767aa7  (*  vadd.f32  s15, s13, s15   *)
  edc37a00  (*  vstr      s15, [r3]       *)`;

val _ = save_thm("PID_C_cert",result);

val (result,func) = arm_decompLib.l3_arm_decompile "PID_ADA" `
  e3003000  (*  movw      r3, #0          *)
  e3403000  (*  movt      r3, #0          *)
  ed937a00  (*  vldr      s14, [r3]       *)
  edd37a03  (*  vldr      s15, [r3, #12]  *)
  ee676a27  (*  vmul.f32  s13, s14, s15   *)
  edd35a01  (*  vldr      s11, [r3, #4]   *)
  edd37a05  (*  vldr      s15, [r3, #20]  *)
  ed936a02  (*  vldr      s12, [r3, #8]   *)
  ed935a04  (*  vldr      s10, [r3, #16]  *)
  ed837a01  (*  vstr      s14, [r3, #4]   *)
  ee775a65  (*  vsub.f32  s11, s14, s11   *)
  ee477a05  (*  vmla.f32  s15, s14, s10   *)
  ee456a86  (*  vmla.f32  s13, s11, s12   *)
  edc37a05  (*  vstr      s15, [r3, #20]  *)
  ee767aa7  (*  vadd.f32  s15, s13, s15   *)
  edc37a06  (*  vstr      s15, [r3, #24]  *)`

val _ = save_thm("PID_ADA_cert",result);

val _ = export_theory();
