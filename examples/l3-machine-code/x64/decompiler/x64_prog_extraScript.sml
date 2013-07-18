
open HolKernel Parse boolLib bossLib;

val _ = new_theory "x64_prog_extra";

open helperLib set_sepTheory addressTheory progTheory;
open pred_setTheory combinTheory x64_progTheory listTheory;

infix \\
val op \\ = op THEN;

(* definitions *)

val L3_X64_MODEL_def = Define `
  L3_X64_MODEL =
     (STATE x64_proj,
      NEXT_REL ($= :x64_state -> x64_state -> bool) NextStateX64,
      x64_instr,($= :x64_state -> x64_state -> bool))`;

val x64_PC_def = Define `
  x64_PC pc = x64_RIP pc * x64_exception NoException`;

val x64_ALL_EFLAGS_def = Define `
  x64_ALL_EFLAGS =
    ~(x64_EFLAGS Z_AF) *
    ~(x64_EFLAGS Z_CF) *
    ~(x64_EFLAGS Z_OF) *
    ~(x64_EFLAGS Z_PF) *
    ~(x64_EFLAGS Z_SF) *
    ~(x64_EFLAGS Z_ZF)`;

val x64_BYTE_MEMORY_def = Define `
  x64_BYTE_MEMORY df f =
    { BIGUNION { BIGUNION (x64_MEM a (SOME (f a))) | a IN df } }`;

val x64_MEMORY_def = Define `
  x64_MEMORY df f =
    { BIGUNION { BIGUNION (x64_mem64 a (f a)) | a IN df } } *
    cond (!a. a IN df ==> (a && 7w = 0w))`;

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

val STAR_cond_EQ = prove(
  ``(b1 = b2) /\ (b1 ==> (p = q)) ==> (p * cond b1 = q * cond b2)``,
  SIMP_TAC std_ss [cond_STAR,FUN_EQ_THM] \\ METIS_TAC []);

val x64_BYTE_MEMORY_INSERT = store_thm("x64_BYTE_MEMORY_INSERT",
  ``a IN df ==>
    (x64_MEM a (SOME w) * x64_BYTE_MEMORY (df DELETE a) f =
     x64_BYTE_MEMORY df ((a =+ w) f))``,
  SIMP_TAC std_ss [x64_BYTE_MEMORY_def,x64_MEM_def] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [GSYM SEP_EQ_THM] \\ MATCH_MP_TAC SEP_EQ_STAR
  \\ SIMP_TAC std_ss [SEP_EQ_THM,BIGUNION_SING,DISJOINT_DEF,EXTENSION]
  \\ SIMP_TAC (srw_ss()) [PULL_EXISTS,APPLY_UPDATE_THM]
  \\ METIS_TAC []);

val x64_MEMORY_INSERT = store_thm("x64_MEMORY_INSERT",
  ``a IN df /\ (a && 7w = 0w) ==>
    (x64_mem64 a w * x64_MEMORY (df DELETE a) f =
     x64_MEMORY df ((a =+ w) f))``,
  SIMP_TAC std_ss [x64_MEMORY_def,x64_mem64_def] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [GSYM SEP_EQ_THM,STAR_ASSOC]
  \\ MATCH_MP_TAC STAR_cond_EQ \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC []) \\ STRIP_TAC
  \\ MATCH_MP_TAC SEP_EQ_STAR
  \\ SIMP_TAC std_ss [SEP_EQ_THM,BIGUNION_SING,DISJOINT_DEF,EXTENSION]
  \\ SIMP_TAC (srw_ss()) [PULL_EXISTS,APPLY_UPDATE_THM]
  \\ STRIP_TAC THEN1 METIS_TAC []
  \\ REPEAT STRIP_TAC
  \\ Cases_on `a' = a` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `a' IN df` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC bool_ss [x64_mem_def,LENGTH,GENLIST,EL,HD,TL,
       SNOC_APPEND,APPEND,LIST_TO_SET,IN_INSERT,NOT_IN_EMPTY]
  \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `a'`)
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `aa <> bb:word64` MP_TAC
  \\ Q.PAT_ASSUM `aa = bb:word64` MP_TAC
  \\ Q.PAT_ASSUM `aa = bb:word64` MP_TAC
  \\ blastLib.BBLAST_TAC);

val x64_mem64_APPEND = prove(
  ``x64_mem32 a v * x64_mem32 (a + 4w) ((63 >< 32) w) =
    x64_mem64 a ((((63 >< 32) w):word32) @@ v)``,
  SIMP_TAC std_ss [x64_mem64_def,x64_mem32_def]
  \\ SIMP_TAC std_ss [GSYM SEP_EQ_THM] \\ MATCH_MP_TAC SEP_EQ_STAR
  \\ SIMP_TAC std_ss [SEP_EQ_THM,BIGUNION_SING,DISJOINT_DEF,EXTENSION]
  \\ SIMP_TAC (srw_ss()) [PULL_EXISTS,APPLY_UPDATE_THM,x64_mem_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  THEN1 (REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [addressTheory.WORD_EQ_ADD_CANCEL]
    \\ blastLib.BBLAST_TAC)
  \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [addressTheory.WORD_EQ_ADD_CANCEL]);

val lemma = blastLib.BBLAST_PROVE
  ``(((63 >< 32) w):word32) @@ ((w2w w):word32) = (w:word64)``

val lemma2 = blastLib.BBLAST_PROVE
  ``((((63 :num) >< (32 :num))
       (((((63 :num) >< (32 :num)) (w:word64) :word32)
          @@ (v:word32)) :word64) :word32) =
    ((63 >< 32) w):word32) /\
    (w2w (((((63 >< 32) w):word32) @@ v):word64) = v)``

val x64_mem32_READ_EXTEND = store_thm("x64_mem32_READ_EXTEND",
  ``SPEC m (p * x64_mem32 a (w2w w)) c (q * x64_mem32 a (w2w w)) ==>
    SPEC m (p * x64_mem64 a w) c (q * x64_mem64 a w)``,
  REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [GSYM lemma]
  \\ SIMP_TAC std_ss [GSYM x64_mem64_APPEND,STAR_ASSOC]
  \\ SIMP_TAC std_ss [lemma] \\ METIS_TAC [SPEC_FRAME]);

val x64_mem32_WRITE_EXTEND = store_thm("x64_mem32_WRITE_EXTEND",
  ``SPEC m (p * x64_mem32 a (w2w w)) c (q * x64_mem32 a v) ==>
    SPEC m (p * x64_mem64 a w) c (q * x64_mem64 a ((((63 >< 32) w):word32) @@ v))``,
  REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [GSYM lemma]
  \\ SIMP_TAC std_ss [GSYM x64_mem64_APPEND,STAR_ASSOC]
  \\ SIMP_TAC std_ss [lemma,lemma2] \\ METIS_TAC [SPEC_FRAME]);

val _ = export_theory();
