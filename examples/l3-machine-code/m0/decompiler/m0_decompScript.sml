
open HolKernel Parse boolLib bossLib;

val _ = new_theory "m0_decomp";

open helperLib set_sepTheory addressTheory progTheory wordsTheory;
open pred_setTheory combinTheory m0_progTheory listTheory;

infix \\
val op \\ = op THEN;

(* definitions *)

val L3_M0_MODEL_def = Define `
  L3_M0_MODEL =
     (STATE m0_proj,
      NEXT_REL ($= :m0_state -> m0_state -> bool) NextStateARM,
      m0_instr,($= :m0_state -> m0_state -> bool))`;

val m0_PC_def = Define `
  m0_PC pc =
    SEP_EXISTS aircr.
      m0_exception NoException * m0_CONTROL_SPSEL F *
      m0_AIRCR aircr * m0_REG RName_PC pc *
      cond (¬aircr.ENDIANNESS /\ Aligned (pc,2))`;

val m0_NZCV_def = Define `
  m0_NZCV = ~m0_PSR_N * ~m0_PSR_Z * ~m0_PSR_C * ~m0_PSR_V`;

val m0_MEMORY_def = Define `
  m0_MEMORY dm m =
    { BIGUNION { BIGUNION (m0_MEM a (m a)) | a IN dm } }`;

(* theorems *)

val SEP_EQ_THM = prove(
  ``SEP_EQ x = {x}``,
  SIMP_TAC (srw_ss()) [SEP_EQ_def,EXTENSION]);

val SEP_EQ_STAR = prove(
  ``((q = p1 UNION p2) /\ DISJOINT p1 p2) ==>
    ((SEP_EQ p1 * SEP_EQ p2) = (SEP_EQ q))``,
  REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [SEP_EQ_def,Once FUN_EQ_THM,STAR_def,SPLIT_def]
  \\ METIS_TAC []);

val m0_MEMORY_INSERT = store_thm("m0_MEMORY_INSERT",
  ``a IN dm ==>
    (m0_MEM a w * m0_MEMORY (dm DELETE a) m =
     m0_MEMORY dm ((a =+ w) m))``,
  SIMP_TAC std_ss [m0_MEMORY_def,m0_MEM_def] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [GSYM SEP_EQ_THM] \\ MATCH_MP_TAC SEP_EQ_STAR
  \\ SIMP_TAC std_ss [SEP_EQ_THM,BIGUNION_SING,DISJOINT_DEF,EXTENSION]
  \\ SIMP_TAC (srw_ss()) [PULL_EXISTS,APPLY_UPDATE_THM]
  \\ METIS_TAC []);

val m0_PC_INTRO = store_thm("m0_PC_INTRO",
  ``(!aircr.
        ~aircr.ENDIANNESS /\ Aligned (pc,2) ==>
        SPEC L3_M0_MODEL
         (p * m0_exception NoException * m0_CONTROL_SPSEL F *
          m0_AIRCR aircr * m0_REG RName_PC pc) code
         (q * m0_exception NoException * m0_CONTROL_SPSEL F *
          m0_AIRCR aircr * m0_REG RName_PC pc')) ==>
    SPEC L3_M0_MODEL
      (p * m0_PC pc * cond ((Aligned (pc,2) ==> Aligned (pc',2))))
      code (q * m0_PC pc')``,
  SIMP_TAC std_ss [m0_PC_def,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
  \\ ASM_SIMP_TAC std_ss [SPEC_MOVE_COND,STAR_ASSOC]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ IMP_RES_TAC SPEC_WEAKEN \\ POP_ASSUM MATCH_MP_TAC
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `aircr`
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]);

val Aligned_2 = prove(
  ``!x:word32. Aligned (x,2) <=> ~(x ' 0)``,
  Cases
  \\ FULL_SIMP_TAC (srw_ss()) [m0Theory.Aligned_def,m0Theory.Align_def]
  \\ `0 < dimindex (:32)` by EVAL_TAC \\ IMP_RES_TAC word_index
  \\ FULL_SIMP_TAC std_ss [bitTheory.BIT_def,bitTheory.BITS_THM]
  \\ STRIP_ASSUME_TAC (Q.SPEC `n` (MATCH_MP
       arithmeticTheory.DIVISION (DECIDE ``0<2:num``)))
  \\ ONCE_REWRITE_TAC [arithmeticTheory.MULT_COMM]
  \\ Q.PAT_ASSUM `n = cc` (fn th => SIMP_TAC std_ss [Once th])
  \\ `(n DIV 2) < 2147483648` by ALL_TAC
  THEN1 (ASM_SIMP_TAC std_ss [arithmeticTheory.DIV_LT_X])
  \\ `(n DIV 2 * 2) < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ DECIDE_TAC);

val Aligned_2_SELECT = prove(
  ``!pc:word32. Aligned ((((31 >< 1) pc:31 word) @@ (0w:1 word)):word32,2)``,
  SIMP_TAC std_ss [Aligned_2] \\ blastLib.BBLAST_TAC);

val Aligned_2_ADD = prove(
  ``!pc x:word32. Aligned (pc,2) ==> (Aligned (pc+x,2) = Aligned (x,2)) /\
                                     (Aligned (pc-x,2) = Aligned (x,2))``,
  SIMP_TAC std_ss [Aligned_2] \\ blastLib.BBLAST_TAC);

val Aligned_n2w = prove(
  ``!n. Aligned ((n2w n):word32,2) <=> (n MOD 2 <> 1)``,
  SIMP_TAC std_ss [Aligned_2]
  \\ `0 < dimindex (:32)` by EVAL_TAC \\ IMP_RES_TAC word_index
  \\ FULL_SIMP_TAC std_ss [bitTheory.BIT_def,bitTheory.BITS_THM]);

val Aligned_2_SIMP = save_thm("Aligned_2_SIMP",
  LIST_CONJ [Aligned_2_ADD,Aligned_n2w,Aligned_2_SELECT]);

val _ = export_theory();
