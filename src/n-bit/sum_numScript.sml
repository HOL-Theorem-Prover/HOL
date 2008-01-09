(* ========================================================================= *)
(* FILE          : sum_numScript.sml                                         *)
(* DESCRIPTION   : Defines a big-sigma (sum) function for the                *)
(*                 natural numbers.                                          *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2002                                                      *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib
open Q arithmeticTheory;

val _ = new_theory "sum_num";

(* ------------------------------------------------------------------------- *)

val GSUM_def = Define`
  (GSUM (n,0) f = 0) /\
  (GSUM (n,SUC m) f = GSUM (n,m) f + f (n + m))`;

val GSUM_1 = store_thm("GSUM_1",
  `!m f. GSUM (m,1) f = f m`, REWRITE_TAC [ONE,GSUM_def,ADD_CLAUSES]);

val GSUM_ADD = store_thm("GSUM_ADD",
  `!p m n f. GSUM (p,m + n) f = GSUM (p,m) f + GSUM (p + m,n) f`,
   Induct_on `n` THEN1 REWRITE_TAC [GSUM_def,ADD_CLAUSES]
     THEN ASM_SIMP_TAC arith_ss [GSYM ADD_SUC,GSUM_def]);

val GSUM_ZERO = store_thm("GSUM_ZERO",
  `!p n f. (!m. p <= m /\ m < p + n ==> (f m = 0)) = (GSUM (p,n) f = 0)`,
  Induct_on `n`
    THEN ASM_SIMP_TAC arith_ss [GSUM_def] THEN NTAC 2 STRIP_TAC
    THEN POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
    THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC arith_ss []
    THEN PAT_ASSUM `!m. P` (SPEC_THEN `m` IMP_RES_TAC)
    THEN Cases_on `m < p + n` THEN1 PROVE_TAC []
    THEN `m = n + p` by DECIDE_TAC
    THEN ASM_REWRITE_TAC []);

val GSUM_MONO = store_thm("GSUM_MONO",
  `!p m n f. m <= n /\ ~(f (p + n) = 0) ==> GSUM (p,m) f < GSUM (p,SUC n) f`,
  RW_TAC arith_ss [GSUM_def]
    THEN IMP_RES_TAC LESS_EQUAL_ADD
    THEN FULL_SIMP_TAC arith_ss [GSUM_ADD]);

val GSUM_MONO2 = prove(
  `!p m n f. GSUM (p,m) f < GSUM (p,n) f ==> m < n`,
  Induct_on `n` THEN1 REWRITE_TAC [prim_recTheory.NOT_LESS_0,GSUM_def]
    THEN SPOSE_NOT_THEN STRIP_ASSUME_TAC
    THEN RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS,GSYM LESS_EQ])
    THEN IMP_RES_TAC LESS_ADD_1 THEN POP_ASSUM (K ALL_TAC)
    THEN POP_ASSUM (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSUM_ADD,
           REWRITE_RULE [DECIDE (Term `!a b. a + (b + 1) = SUC a + b`)] th]))
    THEN DECIDE_TAC);

val GSUM_LESS = store_thm("GSUM_LESS",
  `!p m n f. (?q. m + p <= q /\ q < n + p /\ ~(f q = 0)) = GSUM (p,m) f < GSUM (p,n) f`,
  Induct_on `n` THEN1 SIMP_TAC arith_ss [GSUM_def]
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC THEN REPEAT STRIP_TAC
    THENL [
      Cases_on `GSUM (p,m) f < GSUM (p,n) f`
        THEN1 ASM_SIMP_TAC arith_ss [GSUM_def]
        THEN PAT_ASSUM `!p m f. P` (fn th => FULL_SIMP_TAC arith_ss [GSYM th])
        THEN Cases_on `q < n + p` THEN1 PROVE_TAC []
        THEN `m <= n /\ (q = n + p)` by DECIDE_TAC
        THEN IMP_RES_TAC (ONCE_REWRITE_RULE [ADD_COMM] GSUM_MONO)
        THEN PROVE_TAC [],
      Cases_on `GSUM (p,m) f < GSUM (p,n) f`
        THENL [
          PAT_ASSUM `!p m f. P` IMP_RES_TAC
            THEN `q < SUC n + p` by DECIDE_TAC
            THEN PROVE_TAC [],
          FULL_SIMP_TAC bool_ss [GSUM_def]
            THEN `~(f (p + n) = 0)` by DECIDE_TAC
            THEN EXISTS_TAC `p + n`
            THEN ASM_SIMP_TAC arith_ss []
            THEN FULL_SIMP_TAC bool_ss [GSYM GSUM_def]
            THEN IMP_RES_TAC GSUM_MONO2
            THEN DECIDE_TAC]]);

val GSUM_EQUAL_LEM = prove(
  `!p m n f. n < m /\ (!q. p + n <= q /\ q < p + m ==> (f q = 0)) ==>
            (GSUM (p,m) f = GSUM (p,n) f)`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC LESS_ADD
    THEN POP_ASSUM (fn th => FULL_SIMP_TAC arith_ss [GSUM_ADD,GSUM_ZERO,SYM th])
    THEN Induct_on `p'` THEN RW_TAC arith_ss [GSUM_def]
    THEN Cases_on `p'` THEN FULL_SIMP_TAC arith_ss [GSUM_def]);

val GSUM_EQUAL_LEM2 = prove(
  `!p m n f. (GSUM (p,m) f = GSUM (p,n) f) =
           ((m = n) \/
            (m < n /\ (!q. p + m <= q /\ q < p + n ==> (f q = 0))) \/
            (n < m /\ (!q. p + n <= q /\ q < p + m ==> (f q = 0))))`,
  REPEAT STRIP_TAC THEN Tactical.REVERSE EQ_TAC
    THEN1 PROVE_TAC [GSUM_EQUAL_LEM]
    THEN Cases_on `m = n` THEN1 ASM_REWRITE_TAC []
    THEN IMP_RES_TAC (DECIDE (Term `!(a:num) b. ~(a = b) ==> (a < b) \/ (b < a)`))
    THEN ASM_SIMP_TAC arith_ss []
    THEN SPOSE_NOT_THEN STRIP_ASSUME_TAC
    THEN IMP_RES_TAC GSUM_LESS THEN DECIDE_TAC);

val GSUM_EQUAL = store_thm("GSUM_EQUAL",
  `!p m n f. (GSUM (p,m) f = GSUM (p,n) f) =
           ((m <= n /\ (!q. p + m <= q /\ q < p + n ==> (f q = 0))) \/
            (n < m /\ (!q. p + n <= q /\ q < p + m ==> (f q = 0))))`,
  RW_TAC arith_ss [GSUM_EQUAL_LEM2]
    THEN Cases_on `m = n` THEN1 ASM_SIMP_TAC arith_ss []
    THEN IMP_RES_TAC (DECIDE (Term `!(a:num) b. ~(a = b) ==> (a < b) \/ (b < a)`))
    THEN ASM_SIMP_TAC arith_ss []);

val GSUM_FUN_EQUAL = store_thm("GSUM_FUN_EQUAL",
  `!p n f g. (!x. p <= x /\ x < p + n ==> (f x = g x)) ==>
       (GSUM (p,n) f = GSUM (p,n) g)`,
  Induct_on `n` THEN RW_TAC arith_ss [GSUM_def]);

(* ------------------------------------------------------------------------- *)

val SUM_def = Define`
  (SUM 0 f = 0) /\
  (SUM (SUC m) f = SUM m f + f m)`;

val SUM = store_thm("SUM",
  `!m f. SUM m f = GSUM (0,m) f`,
  Induct THEN ASM_SIMP_TAC arith_ss [SUM_def,GSUM_def]);

val SYM_SUM = GSYM SUM;

val SUM_1 = save_thm("SUM_1",
  (REWRITE_RULE [SYM_SUM] o SPEC `0`) GSUM_1);

val SUM_MONO = save_thm("SUM_MONO",
  (REWRITE_RULE [SYM_SUM,ADD] o SPEC `0`) GSUM_MONO);

val SUM_LESS = save_thm("SUM_LESS",
  (REWRITE_RULE [SYM_SUM,ADD_CLAUSES] o SPEC `0`) GSUM_LESS);

val SUM_EQUAL = save_thm("SUM_EQUAL",
  (SIMP_RULE arith_ss [SYM_SUM] o SPEC `0`) GSUM_EQUAL);

val SUM_FUN_EQUAL = save_thm("SUM_FUN_EQUAL",
  (SIMP_RULE arith_ss [SYM_SUM] o SPECL [`0`,`n`]) GSUM_FUN_EQUAL);

val SUM_ZERO = save_thm("SUM_ZERO",
  (SIMP_RULE arith_ss [SYM_SUM] o SPEC `0`) GSUM_ZERO);

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
