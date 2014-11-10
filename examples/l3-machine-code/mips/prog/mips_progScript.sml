open HolKernel boolLib bossLib
open stateLib mips_stepTheory

val () = new_theory "mips_prog"

(* ------------------------------------------------------------------------ *)

val _ =
   stateLib.sep_definitions "mips" [["CP0", "Status"], ["CP0", "Config"]] []
      mips_stepTheory.NextStateMIPS_def

val mips_instr_def = Define`
   mips_instr (a, i: word32) =
   { (mips_c_MEM a, mips_d_word8 ((7 >< 0) i));
     (mips_c_MEM (a + 1w), mips_d_word8 ((15 >< 8) i));
     (mips_c_MEM (a + 2w), mips_d_word8 ((23 >< 16) i));
     (mips_c_MEM (a + 3w), mips_d_word8 ((31 >< 24) i)) }`;

val MIPS_MODEL_def = Define`
  MIPS_MODEL =
    (STATE mips_proj, NEXT_REL (=) NextStateMIPS, mips_instr,
     ($= :mips_state -> mips_state -> bool), K F : mips_state -> bool)`

val MIPS_IMP_SPEC = Theory.save_thm ("MIPS_IMP_SPEC",
   stateTheory.IMP_SPEC
   |> Q.ISPECL [`mips_proj`, `NextStateMIPS`, `mips_instr`]
   |> REWRITE_RULE [GSYM MIPS_MODEL_def]
   )

val MIPS_IMP_TEMPORAL = Theory.save_thm ("MIPS_IMP_TEMPORAL",
   temporal_stateTheory.IMP_TEMPORAL
   |> Q.ISPECL [`mips_proj`, `NextStateMIPS`, `mips_instr`,
                `(=) : mips_state -> mips_state -> bool`,
                `K F : mips_state -> bool`]
   |> REWRITE_RULE [GSYM MIPS_MODEL_def]
   )

(* ------------------------------------------------------------------------ *)

val () = export_theory()
