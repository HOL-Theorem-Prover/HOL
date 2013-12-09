open HolKernel Parse boolLib bossLib
open tripleTheory m0_decompTheory

val () = new_theory "m0_core_decomp"

val _ = Parse.hide "mem"

(* definition of M0_ASSERT *)

val _ = Hol_datatype`
   m0_assertion =
   M0_ASSERTION of bool => bool => bool => bool =>    (* n z c v      *)
                   num =>                             (* count        *)
                   RName set => (RName -> word32) =>  (* gp registers *)
                   word32 set => (word32 -> word8) => (* memory       *)
                   word32                             (* pc           *)`

val M0_ASSERT_def = Define`
   M0_ASSERT (M0_ASSERTION n z c v count dreg reg dmem mem pc) =
     m0_PSR_N n *
     m0_PSR_Z z *
     m0_PSR_C c *
     m0_PSR_V v *
     m0_COUNT count *
     m0_REGISTERS dreg reg *
     m0_MEMORY dmem mem *
     m0_PC pc`

val L3_M0_def = Define `L3_M0 = (M0_ASSERT, M0_MODEL)`

val () = export_theory()
