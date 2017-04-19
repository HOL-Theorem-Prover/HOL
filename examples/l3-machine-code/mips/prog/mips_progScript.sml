open HolKernel boolLib bossLib
open stateLib set_sepTheory progTheory mips_stepTheory

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

val mips_CONFIG_def = Define`
   mips_CONFIG be =
   mips_exception NoException * mips_exceptionSignalled F *
   mips_CP0_Status_RE F * mips_CP0_Config_BE be * mips_BranchTo NONE`

val mips_LE_def = Define `mips_LE = mips_CONFIG F`
val mips_BE_def = Define `mips_BE = mips_CONFIG T`

val MIPS_PC_def = Define`
   MIPS_PC pc = mips_BranchDelay NONE * mips_PC pc * cond (aligned 2 pc)`

(* ------------------------------------------------------------------------ *)

val MIPS_PC_INTRO = Q.store_thm("MIPS_PC_INTRO",
   `SPEC m (p1 * MIPS_PC pc) code
           (p2 * mips_BranchDelay NONE * mips_PC pc') ==>
    (aligned 2 pc ==> aligned 2 pc') ==>
    SPEC m (p1 * MIPS_PC pc) code (p2 * MIPS_PC pc')`,
   REPEAT STRIP_TAC
   \\ FULL_SIMP_TAC std_ss
        [MIPS_PC_def, SPEC_MOVE_COND, STAR_ASSOC, SEP_CLAUSES]
   )

(* ------------------------------------------------------------------------ *)

val () = export_theory()
