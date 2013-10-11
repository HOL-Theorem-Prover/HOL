open HolKernel Parse boolLib bossLib
open tripleTheory arm_decompTheory

val () = new_theory "arm_core_decomp"

(* definition of ARM_ASSERT and L3_ARM *)

val _ = Parse.hide "mem"

val () = Hol_datatype`
   arm_assertion = ARM_ASSERTION of
                    (* mode *) word5 =>
                    (* r0 *) word32 =>
                    (* r1 *) word32 =>
                    (* r2 *) word32 =>
                    (* r3 *) word32 =>
                    (* r4 *) word32 =>
                    (* r5 *) word32 =>
                    (* r6 *) word32 =>
                    (* r7 *) word32 =>
                    (* r8 *) word32 =>
                    (* r9 *) word32 =>
                    (* r10 *) word32 =>
                    (* r11 *) word32 =>
                    (* r12 *) word32 =>
                    (* r13 *) word32 =>
                    (* r14 *) word32 =>
                    (* n *) bool =>
                    (* z *) bool =>
                    (* c *) bool =>
                    (* v *) bool =>
                    (* domain of fps *) word5 set =>
                    (* fp registers *) (word5 -> word64) =>
                    (* rmode *) word2 =>
                    (* fp_n *) bool =>
                    (* fp_z *) bool =>
                    (* fp_c *) bool =>
                    (* fp_v *) bool =>
                    (* domain of memory *) word32 set =>
                    (* memory *) (word32 -> word8) =>
                    (* pc *) word32`;

val ARM_ASSERT_def = Define`
   ARM_ASSERT
      (ARM_ASSERTION mode r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
                     n z c v dfpr fpr rmode fp_n fp_z fp_c fp_v dmem mem r15) =
     arm_OK mode *
     arm_REG (R_mode mode 0w) r0 *
     arm_REG (R_mode mode 1w) r1 *
     arm_REG (R_mode mode 2w) r2 *
     arm_REG (R_mode mode 3w) r3 *
     arm_REG (R_mode mode 4w) r4 *
     arm_REG (R_mode mode 5w) r5 *
     arm_REG (R_mode mode 6w) r6 *
     arm_REG (R_mode mode 7w) r7 *
     arm_REG (R_mode mode 8w) r8 *
     arm_REG (R_mode mode 9w) r9 *
     arm_REG (R_mode mode 10w) r10 *
     arm_REG (R_mode mode 11w) r11 *
     arm_REG (R_mode mode 12w) r12 *
     arm_REG (R_mode mode 13w) r13 *
     arm_REG (R_mode mode 14w) r14 *
     arm_CPSR_N n *
     arm_CPSR_Z z *
     arm_CPSR_C c *
     arm_CPSR_V v *
     arm_FP_REGISTERS dfpr fpr *
     arm_FP_FPSCR_RMode rmode *
     arm_FP_FPSCR_N fp_n *
     arm_FP_FPSCR_Z fp_z *
     arm_FP_FPSCR_C fp_c *
     arm_FP_FPSCR_V fp_v *
     arm_MEMORY dmem mem *
     arm_PC r15`;

val L3_ARM_def = Define `L3_ARM = (ARM_ASSERT, ARM_MODEL)`

val () = export_theory()
