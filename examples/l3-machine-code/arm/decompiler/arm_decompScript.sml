
open HolKernel Parse boolLib bossLib;

val _ = new_theory "arm_decomp";

open helperLib set_sepTheory addressTheory progTheory;
open pred_setTheory combinTheory pairTheory;

infix \\
val op \\ = op THEN;

(* definitions *)

val L3_ARM_MODEL_def = Define `
  L3_ARM_MODEL =
    (STATE arm_proj,
     NEXT_REL ($= :arm_state -> arm_state -> bool) NextStateARM,arm_instr,
     ($= :arm_state -> arm_state -> bool))`;

val arm_OK_def = Define `
  arm_OK =
    arm_Extensions Extension_VFP T *
    arm_Architecture ARMv7_A *
    arm_exception NoException * arm_CPSR_J F *
    arm_CPSR_E F * arm_CPSR_T F * arm_CPSR_M 16w`;

val arm_PC_def = Define `
  arm_PC pc = arm_OK * arm_REG RName_PC pc * cond (Aligned (pc,4))`;

val arm_MEMORY_SET_def = Define `
  arm_MEMORY_SET df f = { (arm_c_MEM a,arm_d_word8 (f a)) | a | a IN df }`;

val arm_MEMORY_def = Define `arm_MEMORY df f = SEP_EQ (arm_MEMORY_SET df f)`;

val aS_def = Define `
  aS (n,z,c,v) = arm_CPSR_N n * arm_CPSR_Z z * arm_CPSR_C c * arm_CPSR_V v`;

(* theorems *)

val aS_HIDE = store_thm("aS_HIDE",
  ``~aS = ~arm_CPSR_N * ~arm_CPSR_Z * ~arm_CPSR_C * ~arm_CPSR_V``,
  SIMP_TAC std_ss [SEP_HIDE_def,aS_def,SEP_CLAUSES,FUN_EQ_THM]
  \\ SIMP_TAC std_ss [SEP_EXISTS] \\ METIS_TAC [aS_def,PAIR]);

val arm_PC_INTRO1 = store_thm("arm_PC_INTRO1",
  ``p * arm_OK * arm_REG RName_PC pc * cond (Aligned (pc,4)) =
    p * arm_PC pc``,
  SIMP_TAC std_ss [STAR_ASSOC,arm_PC_def]);

val arm_PC_INTRO2 = store_thm("arm_PC_INTRO2",
  ``SPEC m (p1 * arm_PC pc) code (p2 * arm_OK * arm_REG RName_PC pc') ==>
    (Aligned (pc,4) ==> Aligned (pc',4)) ==>
    SPEC m (p1 * arm_PC pc) code (p2 * arm_PC pc')``,
  REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [arm_PC_def,SPEC_MOVE_COND,
    STAR_ASSOC,SEP_CLAUSES]);

val Aligned_EQ_ALIGNED = store_thm("Aligned_EQ_ALIGNED",
  ``!w:word32. Aligned (w,4) = ALIGNED w``,
  SIMP_TAC std_ss [arm_stepTheory.Aligned,ALIGNED_def]
  THEN blastLib.BBLAST_TAC);

val IN_arm_MEMORY_SET = prove(
  ``a IN df ==>
    (arm_MEMORY_SET df g =
     (arm_c_MEM a,arm_d_word8 (g a)) INSERT arm_MEMORY_SET (df DELETE a) g)``,
  SIMP_TAC std_ss [EXTENSION,IN_INSERT,arm_MEMORY_SET_def,GSPECIFICATION]
  \\ REWRITE_TAC [IN_DELETE] \\ METIS_TAC []);

val DELETE_arm_MEMORY_SET = prove(
  ``arm_MEMORY_SET (df DELETE a) ((a =+ w) g) =
    arm_MEMORY_SET (df DELETE a) g``,
  SIMP_TAC std_ss [EXTENSION,IN_INSERT,arm_MEMORY_SET_def,GSPECIFICATION]
  \\ REWRITE_TAC [IN_DELETE,APPLY_UPDATE_THM] \\ METIS_TAC []);

val arm_MEM_thm = prove(
  ``arm_MEM a b = SEP_EQ {(arm_c_MEM a,arm_d_word8 b)}``,
  SIMP_TAC std_ss [arm_progTheory.arm_MEM_def,SEP_EQ_def,
    EXTENSION,IN_INSERT,NOT_IN_EMPTY] THEN SIMP_TAC std_ss [IN_DEF]);

val arm_MEMORY_INSERT = store_thm("arm_MEMORY_INSERT",
  ``a IN df ==>
    (arm_MEM a w * arm_MEMORY (df DELETE a) g =
     arm_MEMORY df ((a =+ w) g))``,
  ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [arm_MEMORY_def,arm_MEM_thm,FUN_EQ_THM,EQ_STAR]
  \\ SIMP_TAC std_ss [SEP_EQ_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (GEN_ALL IN_arm_MEMORY_SET)
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET,DIFF_INSERT,DIFF_EMPTY]
  \\ REWRITE_TAC [DELETE_arm_MEMORY_SET,APPLY_UPDATE_THM]
  \\ REWRITE_TAC [EXTENSION,IN_INSERT,IN_DELETE]
  \\ REVERSE (`~((arm_c_MEM a,arm_d_word8 w) IN
                 arm_MEMORY_SET (df DELETE a) g)` by ALL_TAC)
  THEN1 METIS_TAC []
  \\ SIMP_TAC (srw_ss()) [arm_MEMORY_SET_def,GSPECIFICATION,IN_DELETE]);

val _ = export_theory();
