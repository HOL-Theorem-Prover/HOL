Theory prog_armLibContext[bare]
Ancestors
  pred_set words set_sep prog prog_arm marker address combin
  arm_coretypes arm_step arm_seq_monad
Libs
  HolKernel Parse boolLib bossLib wordsLib armLib

(* ------------------------------------------------------------------------- *)
(* Lemmas prog_armLib.sml formerly proved as it loaded.  A library is loaded  *)
(* before its client's new_theory, so there was no current theory to prove    *)
(* against; proving them in a theory of their own removes that.               *)
(* ------------------------------------------------------------------------- *)

Theorem SING_SUBSET:
  !x:'a y. {x} SUBSET y <=> x IN y
Proof
  REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET]
QED

Theorem cond_STAR_cond:
  !x y. cond (x /\ y) = cond x * (cond y):'a set -> bool
Proof
  SIMP_TAC (std_ss) [SEP_CLAUSES]
QED

Theorem precond_INTRO:
  !x. cond (Abbrev x) = precond x:'a set -> bool
Proof
  SIMP_TAC (std_ss) [SEP_CLAUSES, precond_def, markerTheory.Abbrev_def]
QED

Theorem ARM_WRITE_STATUS_T_IGNORE_UPDATE:
  (~ARM_READ_STATUS psrT s ==> (ARM_WRITE_STATUS psrT F s = s)) /\
  (ARM_WRITE_STATUS psrT b (ARM_WRITE_REG r w s) =
   ARM_WRITE_REG r w (ARM_WRITE_STATUS psrT b s))
Proof
  EVAL_TAC \\ SRW_TAC [] [FUN_EQ_THM, APPLY_UPDATE_THM,
    arm_seq_monadTheory.arm_state_component_equality,
    arm_coretypesTheory.ARMpsr_component_equality] \\ SRW_TAC [] []
  \\ ASM_SIMP_TAC std_ss []
QED

Theorem aligned_bx_lemma:
  !w:word32. aligned (w,4) ==> aligned_bx w /\ ~(w ' 0)
Proof
  SIMP_TAC std_ss [aligned4_thm, ALIGNED_BITS, arm_stepTheory.aligned_bx_thm]
QED
