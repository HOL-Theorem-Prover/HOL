open HolKernel boolLib bossLib
open stateLib x64_stepTheory

val () = new_theory "x64_prog"

(* ------------------------------------------------------------------------ *)

val _ = stateLib.sep_definitions "x64" [] [] x64_stepTheory.NextStateX64_def

val x64_mem_def = Define`
   x64_mem a (i: word8 list) =
   set (GENLIST (\x. (x64_c_MEM (a + n2w x),
                      x64_d_word8_option (SOME (EL x i)))) (LENGTH i))`

val x64_instr_def = Define`
   x64_instr (a, i) =
   x64_mem a i UNION
   set (GENLIST (\x. (x64_c_ICACHE (a + n2w x),
                      x64_d_word8_option (SOME (EL x i)))) (LENGTH i))`

val x64_mem16_def = Define`
   x64_mem16 a (v: word16) = { x64_mem a [(7 >< 0) v; (15 >< 8) v] }`

val x64_mem32_def = Define`
   x64_mem32 a (v: word32) =
   { x64_mem a [(7 >< 0) v; (15 >< 8) v; (23 >< 16) v; (31 >< 24) v] }`

val x64_mem64_def = Define`
   x64_mem64 a (v: word64) =
   { x64_mem a [( 7 ><  0) v; (15 ><  8) v; (23 >< 16) v; (31 >< 24) v;
                (39 >< 32) v; (47 >< 40) v; (55 >< 48) v; (63 >< 56) v] }`

val X64_MODEL_def = Define`
  X64_MODEL = (STATE x64_proj, NEXT_REL (=) NextStateX64, x64_instr,
               ($= :x64_state -> x64_state -> bool))`

val X64_IMP_SPEC = Theory.save_thm ("X64_IMP_SPEC",
   stateTheory.IMP_SPEC
   |> Q.ISPECL [`x64_proj`, `NextStateX64`, `x64_instr`]
   |> REWRITE_RULE [GSYM X64_MODEL_def]
   )

(* ------------------------------------------------------------------------ *)

val () = export_theory()
