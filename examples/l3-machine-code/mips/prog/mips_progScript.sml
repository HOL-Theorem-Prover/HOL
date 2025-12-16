Theory mips_prog
Ancestors
  set_sep prog mips_step temporal_state
Libs
  stateLib

(* ------------------------------------------------------------------------ *)

val _ =
   stateLib.sep_definitions "mips"
      [["CP0", "Status"], ["CP0", "Config"], ["fcsr"], ["fir"]] []
      mips_stepTheory.NextStateMIPS_def

Definition mips_instr_def:
   mips_instr (a, i: word32) =
   { (mips_c_MEM a, mips_d_word8 ((7 >< 0) i));
     (mips_c_MEM (a + 1w), mips_d_word8 ((15 >< 8) i));
     (mips_c_MEM (a + 2w), mips_d_word8 ((23 >< 16) i));
     (mips_c_MEM (a + 3w), mips_d_word8 ((31 >< 24) i)) }
End

Definition MIPS_MODEL_def:
  MIPS_MODEL =
    (STATE mips_proj, NEXT_REL (=) NextStateMIPS, mips_instr,
     ($= :mips_state -> mips_state -> bool), K F : mips_state -> bool)
End

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

Definition mips_CONFIG_def:
   mips_CONFIG (be, flush_to_zero, rounding_mode, abs2008) =
   mips_exception NoException * mips_exceptionSignalled F *
   mips_CP0_Status_CU1 T * mips_CP0_Status_RE F *
   mips_fcsr_ABS2008 abs2008 * mips_fcsr_FS flush_to_zero *
   mips_fcsr_RM rounding_mode * mips_CP0_Config_BE be * mips_BranchTo NONE
End

Definition mips_LE_def:   mips_LE = mips_CONFIG (F, F, 0w, T)
End
Definition mips_BE_def:   mips_BE = mips_CONFIG (T, F, 0w, T)
End

Definition MIPS_PC_def:
   MIPS_PC pc = mips_BranchDelay NONE * mips_PC pc * cond (aligned 2 pc)
End

(* ------------------------------------------------------------------------ *)

Theorem MIPS_PC_INTRO:
    SPEC m (p1 * MIPS_PC pc) code
           (p2 * mips_BranchDelay NONE * mips_PC pc') ==>
    (aligned 2 pc ==> aligned 2 pc') ==>
    SPEC m (p1 * MIPS_PC pc) code (p2 * MIPS_PC pc')
Proof
   REPEAT STRIP_TAC
   \\ FULL_SIMP_TAC std_ss
        [MIPS_PC_def, SPEC_MOVE_COND, STAR_ASSOC, SEP_CLAUSES]
QED

(* ------------------------------------------------------------------------ *)
