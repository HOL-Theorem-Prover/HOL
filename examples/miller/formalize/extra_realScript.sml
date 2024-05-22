open HolKernel Parse boolLib bossLib;

open realTheory realLib
     hurdUtils subtypeTheory extra_numTheory transcTheory
     pred_setTheory arithmeticTheory seqTheory combinTheory pairTheory
     extra_pred_setTheory extra_boolTheory real_sigmaTheory
     sumTheory limTheory listTheory rich_listTheory;

val _ = new_theory "extra_real";

(* ------------------------------------------------------------------------- *)
(* Tools.                                                                    *)
(* ------------------------------------------------------------------------- *)

val Simplify = RW_TAC arith_ss;

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

val zreal_def = Define `zreal (x : real) = (x = 0)`;
val nzreal_def = Define `nzreal (x : real) = ~(x = 0)`;
val posreal_def = Define `posreal (x : real) = (0 < x)`;
val nnegreal_def = Define `nnegreal (x : real) = (0 <= x)`;
val negreal_def = Define `negreal (x : real) = (0 < ~x)`;
val nposreal_def = Define `nposreal (x : real) = (0 <= ~x)`;

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val REAL_LE_EQ = store_thm
  ("REAL_LE_EQ",
   ``!(x:real) y. x <= y /\ y <= x ==> (x = y)``,
   REAL_ARITH_TAC);

(* the same theorem in realTheory is slightly different *)
val REAL_INF_MIN = store_thm
  ("REAL_INF_MIN",
   ``!p z. z IN p /\ (!x. x IN p ==> z <= x) ==> (inf p = z)``,
   RW_TAC std_ss [SPECIFICATION]
   >> MP_TAC (SPECL [``(\r. (p:real->bool) (~r))``, ``~(z:real)``]
              REAL_SUP_MAX)
   >> RW_TAC std_ss [REAL_NEGNEG, INF_DEF_ALT, SPECIFICATION]
   >> Suff `!x. p ~x ==> x <= ~z`
   >- PROVE_TAC [REAL_ARITH ``~~(x:real) = x``]
   >> REPEAT STRIP_TAC
   >> Suff `z <= ~x` >- (KILL_TAC >> REAL_ARITH_TAC)
   >> PROVE_TAC []);

val POW_HALF_TWICE = store_thm
  ("POW_HALF_TWICE",
   ``!n. (1 / 2) pow n = 2 * (1 / 2) pow (SUC n)``,
   RW_TAC std_ss [pow, REAL_MUL_ASSOC]
   >> PROVE_TAC [HALF_CANCEL, REAL_MUL_LID]);

val REAL_INVINV_ALL = store_thm
  ("REAL_INVINV_ALL",
   ``!x. inv (inv x) = x``,
   STRIP_TAC
   >> reverse (Cases_on `x = 0`) >- RW_TAC std_ss [REAL_INVINV]
   >> RW_TAC std_ss [REAL_INV_0]);

val ABS_BETWEEN_LE = store_thm
  ("ABS_BETWEEN_LE",
   ``!x y d. 0 <= d /\ x - d <= y /\ y <= x + d <=> abs (y - x) <= d``,
   RW_TAC std_ss [abs] >|
   [EQ_TAC >- REAL_ARITH_TAC
    >> STRIP_TAC
    >> Know `0 <= d` >- PROVE_TAC [REAL_LE_TRANS]
    >> STRIP_TAC
    >> RW_TAC std_ss [] >|
    [Suff `x <= y`
     >- (POP_ASSUM MP_TAC >> KILL_TAC >> REAL_ARITH_TAC)
     >> Q.PAT_ASSUM `0 <= y - x` MP_TAC
     >> KILL_TAC
     >> REAL_ARITH_TAC,
     Q.PAT_ASSUM `y - x <= d` MP_TAC
     >> KILL_TAC
     >> REAL_ARITH_TAC],
    EQ_TAC >- REAL_ARITH_TAC
    >> Know `y - x <= 0` >- PROVE_TAC [REAL_NOT_LE, REAL_LT_LE]
    >> STRIP_TAC
    >> Know `~0 <= ~(y - x)` >- PROVE_TAC [REAL_LE_NEG]
    >> KILL_TAC
    >> REWRITE_TAC [REAL_NEG_SUB, REAL_NEG_0]
    >> NTAC 2 STRIP_TAC
    >> Know `0 <= d` >- PROVE_TAC [REAL_LE_TRANS]
    >> STRIP_TAC
    >> RW_TAC std_ss [] >|
    [Q.PAT_ASSUM `x - y <= d` MP_TAC
     >> KILL_TAC
     >> REAL_ARITH_TAC,
     Suff `y <= x`
     >- (POP_ASSUM MP_TAC >> KILL_TAC >> REAL_ARITH_TAC)
     >> Q.PAT_ASSUM `0 <= x - y` MP_TAC
     >> KILL_TAC
     >> REAL_ARITH_TAC]]);

val POW_HALF_EXP = store_thm
  ("POW_HALF_EXP",
   ``!n. (1 / 2) pow n = inv (&(2 EXP n))``,
   RW_TAC std_ss [GSYM REAL_POW, GSYM REAL_INV_1OVER]
   >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
   >> MATCH_MP_TAC POW_INV
   >> REAL_ARITH_TAC);

val REAL_LE_INV_LE = store_thm
  ("REAL_LE_INV_LE",
   ``!x y. 0 < x /\ x <= y ==> inv y <= inv x``,
   RW_TAC std_ss []
   >> Know `0 < inv x` >- PROVE_TAC [REAL_INV_POS]
   >> STRIP_TAC
   >> Suff `~(inv x < inv y)` >- PROVE_TAC [REAL_NOT_LT]
   >> STRIP_TAC
   >> Know `inv (inv y) < inv (inv x)` >- PROVE_TAC [REAL_LT_INV]
   >> RW_TAC std_ss [REAL_INVINV_ALL, REAL_NOT_LT]);

val INV_SUC_POS = store_thm
  ("INV_SUC_POS",
   ``!n. 0 < 1 / & (SUC n)``,
   RW_TAC real_ss [GSYM REAL_INV_1OVER, REAL_LT_INV_EQ, REAL_LT]);

val INV_SUC_MAX = store_thm
  ("INV_SUC_MAX",
   ``!n. 1 / & (SUC n) <= 1``,
   REWRITE_TAC [GSYM REAL_INV_1OVER]
   >> Induct
   >- RW_TAC std_ss [GSYM ONE, REAL_INV1, REAL_LE_REFL]
   >> Suff `inv (& (SUC (SUC n))) <= inv (& (SUC n))`
   >- PROVE_TAC [REAL_LE_TRANS]
   >> Suff `inv (& (SUC (SUC n))) < inv (& (SUC n))` >- REAL_ARITH_TAC
   >> MATCH_MP_TAC REAL_LT_INV
   >> RW_TAC arith_ss [REAL_LT]);

val INV_SUC = store_thm
  ("INV_SUC",
   ``!n. 0 < 1 / & (SUC n) /\ 1 / & (SUC n) <= 1``,
   PROVE_TAC [INV_SUC_POS, INV_SUC_MAX])

val ABS_UNIT_INTERVAL = store_thm
  ("ABS_UNIT_INTERVAL",
   ``!x y. 0 <= x /\ x <= 1 /\ 0 <= y /\ y <= 1 ==> abs (x - y) <= 1``,
   REAL_ARITH_TAC);

val REAL_LE_LT_MUL = store_thm
  ("REAL_LE_LT_MUL",
   ``!x y : real. 0 <= x /\ 0 < y ==> 0 <= x * y``,
   rpt STRIP_TAC
   >> MP_TAC (Q.SPECL [`0`, `x`, `y`] REAL_LE_RMUL)
   >> RW_TAC std_ss [REAL_MUL_LZERO]);

val REAL_LT_LE_MUL = store_thm
  ("REAL_LT_LE_MUL",
   ``!x y : real. 0 < x /\ 0 <= y ==> 0 <= x * y``,
   PROVE_TAC [REAL_LE_LT_MUL, REAL_MUL_SYM]);

val REAL_INV_NEG = store_thm
  ("REAL_INV_NEG",
   ``!x. 0 < ~x ==> 0 < ~inv x``,
   rpt STRIP_TAC
   >> Know `~(x = 0)` >- (POP_ASSUM MP_TAC >> REAL_ARITH_TAC)
   >> RW_TAC std_ss [REAL_NEG_INV]
   >> PROVE_TAC [REAL_INV_POS]);

val IN_ZREAL = store_thm
  ("IN_ZREAL",
   ``!x. x IN zreal <=> (x = 0)``,
   RW_TAC std_ss [zreal_def, SPECIFICATION]);

val IN_NZREAL = store_thm
  ("IN_NZREAL",
   ``!x. x IN nzreal <=> ~(x = 0)``,
   RW_TAC std_ss [nzreal_def, SPECIFICATION]);

val IN_POSREAL = store_thm
  ("IN_POSREAL",
   ``!x. x IN posreal <=> 0 < x``,
   RW_TAC std_ss [posreal_def, SPECIFICATION]);

val IN_NNEGREAL = store_thm
  ("IN_NNEGREAL",
   ``!x. x IN nnegreal <=> 0 <= x``,
   RW_TAC std_ss [nnegreal_def, SPECIFICATION]);

val IN_NEGREAL = store_thm
  ("IN_NEGREAL",
   ``!x. x IN negreal <=> 0 < ~x``,
   RW_TAC std_ss [negreal_def, SPECIFICATION]);

val IN_NPOSREAL = store_thm
  ("IN_NPOSREAL",
   ``!x. x IN nposreal <=> 0 <= ~x``,
   RW_TAC std_ss [nposreal_def, SPECIFICATION]);

val POSREAL_ALT = store_thm
  ("POSREAL_ALT",
   ``posreal = nnegreal INTER nzreal``,
   RW_TAC std_ss [SET_EQ, IN_INTER, IN_POSREAL, IN_NNEGREAL, IN_NZREAL]
   >> REAL_ARITH_TAC);

val NEGREAL_ALT = store_thm
  ("NEGREAL_ALT",
   ``negreal = nposreal INTER nzreal``,
   RW_TAC std_ss [SET_EQ, IN_INTER, IN_NEGREAL, IN_NPOSREAL, IN_NZREAL]
   >> REAL_ARITH_TAC);

val REAL_ZERO_SUBTYPE = store_thm
  ("REAL_ZERO_SUBTYPE",
   ``0 IN zreal``,
   RW_TAC std_ss [IN_ZREAL, SPECIFICATION]);

val REAL_OF_NUM_SUBTYPE = store_thm
  ("REAL_OF_NUM_SUBTYPE",
   ``real_of_num IN ((UNIV -> nnegreal) INTER (gtnum 0 -> posreal))``,
   RW_TAC std_ss [IN_INTER, IN_FUNSET, IN_NNEGREAL, REAL_POS, IN_GTNUM,
                  IN_ZREAL, IN_POSREAL]
   >> Suff `~(& x = 0)`
   >- (Know `0 <= & x` >- RW_TAC std_ss [REAL_POS]
       >> REAL_ARITH_TAC)
   >> Cases_on `x` >- DECIDE_TAC
   >> RW_TAC std_ss [REAL]
   >> Know `0 <= & n` >- RW_TAC std_ss [REAL_POS]
   >> REAL_ARITH_TAC);

val NEG_SUBTYPE = store_thm
  ("NEG_SUBTYPE",
   ``real_neg IN
     ((negreal -> posreal) INTER (posreal -> negreal) INTER
      (nnegreal -> nposreal) INTER (nposreal -> nnegreal) INTER
      (nzreal -> nzreal) INTER (zreal -> zreal))``,
   RW_TAC std_ss [IN_FUNSET, IN_NEGREAL, IN_POSREAL, IN_INTER,
                  IN_NPOSREAL, IN_NNEGREAL, IN_NZREAL, IN_ZREAL]
   >> TRY (POP_ASSUM MP_TAC)
   >> REAL_ARITH_TAC);

val INV_SUBTYPE = store_thm
  ("INV_SUBTYPE",
   ``inv IN
     ((nzreal -> nzreal) INTER (posreal -> posreal) INTER
      (negreal -> negreal))``,
   RW_TAC std_ss [IN_NZREAL, REAL_INV_NZ, IN_FUNSET, IN_INTER, IN_POSREAL,
                  IN_NEGREAL, REAL_INV_POS, REAL_INV_NEG]
   >> REAL_ARITH_TAC);

val SQRT_SUBTYPE = store_thm
  ("SQRT_SUBTYPE",
   ``sqrt IN ((nnegreal -> nnegreal) INTER (posreal -> posreal))``,
   RW_TAC std_ss [IN_INTER, IN_FUNSET, IN_NNEGREAL, SQRT_POS_LE, IN_POSREAL,
                  SQRT_POS_LT]);

val REAL_ADD_SUBTYPE = store_thm
  ("REAL_ADD_SUBTYPE",
   ``!x. $+ IN ((posreal -> nnegreal -> posreal) INTER
                (nnegreal -> posreal -> posreal) INTER
                (nnegreal -> nnegreal -> nnegreal) INTER
                (negreal -> nposreal -> negreal) INTER
                (nposreal -> negreal -> negreal) INTER
                (nposreal -> nposreal -> nposreal) INTER
                (zreal -> x -> x) INTER
                (x -> zreal -> x))``,
  RW_TAC real_ss [IN_FUNSET, IN_NEGREAL, IN_POSREAL, IN_INTER,
                  IN_NPOSREAL, IN_NNEGREAL, IN_NZREAL, IN_ZREAL]
   >> REPEAT (POP_ASSUM MP_TAC)
   >> REAL_ARITH_TAC);

val REAL_SUB_SUBTYPE = store_thm
  ("REAL_SUB_SUBTYPE",
   ``!x. $- IN ((posreal -> nposreal -> posreal) INTER
                (nnegreal -> negreal -> posreal) INTER
                (nnegreal -> nposreal -> nnegreal) INTER
                (negreal -> nnegreal -> negreal) INTER
                (nposreal -> posreal -> negreal) INTER
                (nposreal -> nnegreal -> nposreal) INTER
                (x -> zreal -> x))``,
  RW_TAC real_ss [IN_FUNSET, IN_NEGREAL, IN_POSREAL, IN_INTER,
                  IN_NPOSREAL, IN_NNEGREAL, IN_NZREAL, IN_ZREAL,
                  REAL_SUB_RZERO]
   >> REPEAT (POP_ASSUM MP_TAC)
   >> REAL_ARITH_TAC);

val REAL_MULT_SUBTYPE = store_thm
  ("REAL_MULT_SUBTYPE",
   ``$* IN ((posreal -> nnegreal -> nnegreal) INTER
            (nnegreal -> posreal -> nnegreal) INTER
            (posreal -> posreal -> posreal) INTER
            (negreal -> nposreal -> nnegreal) INTER
            (nposreal -> negreal -> nnegreal) INTER
            (negreal -> negreal -> posreal) INTER
            (posreal -> nposreal -> nposreal) INTER
            (nnegreal -> negreal -> nposreal) INTER
            (posreal -> negreal -> negreal) INTER
            (negreal -> nnegreal -> nposreal) INTER
            (nposreal -> posreal -> nposreal) INTER
            (negreal -> posreal -> negreal) INTER
            (zreal -> UNIV -> zreal) INTER
            (UNIV -> zreal -> zreal) INTER
            (nzreal -> nzreal -> nzreal))``,
   RW_TAC std_ss [IN_FUNSET, IN_NEGREAL, IN_POSREAL, IN_INTER,
                  IN_NPOSREAL, IN_NNEGREAL, IN_NZREAL, IN_ZREAL,
                  REAL_ENTIRE, IN_UNIV]
   >> PROVE_TAC [REAL_LE_MUL, REAL_LT_MUL, REAL_NEGNEG, REAL_MUL_LNEG,
                 REAL_MUL_RNEG, REAL_LE_LT_MUL, REAL_LT_LE_MUL]);

val REAL_DIV_SUBTYPE = store_thm
  ("REAL_DIV_SUBTYPE",
   ``$/ IN ((nnegreal -> posreal -> nnegreal) INTER
            (posreal -> posreal -> posreal) INTER
            (nposreal -> negreal -> nnegreal) INTER
            (negreal -> negreal -> posreal) INTER
            (nnegreal -> negreal -> nposreal) INTER
            (posreal -> negreal -> negreal) INTER
            (nposreal -> posreal -> nposreal) INTER
            (negreal -> posreal -> negreal) INTER
            (zreal -> nzreal -> zreal) INTER
            (nzreal -> nzreal -> nzreal))``,
   MP_TAC INV_SUBTYPE
   >> MP_TAC REAL_MULT_SUBTYPE
   >> RW_TAC std_ss [IN_FUNSET, IN_INTER, real_div, IN_UNIV]);

val REAL_MULT_EQ_CANCEL = store_thm
  ("REAL_MULT_EQ_CANCEL",
   ``!x y z : real. ~(x = 0) ==> ((x * y = z) <=> (y = inv x * z))``,
   Strip
   >> Suff `(x * y = z) <=> (x = 0) \/ (y = inv x * z)` >- PROVE_TAC []
   >> REWRITE_TAC [GSYM REAL_EQ_MUL_LCANCEL]
   >> RW_TAC std_ss [REAL_MUL_ASSOC, REAL_MUL_RINV]
   >> RW_TAC real_ss []);

val REAL_MULT_LE_CANCEL = store_thm
  ("REAL_MULT_LE_CANCEL",
   ``!x y z : real. 0 < x ==> ((x * y <= z) <=> (y <= inv x * z))``,
   Strip
   >> Suff `(x * y <= z) = (x * y <= x * (inv x * z))`
   >- PROVE_TAC [REAL_LE_LMUL]
   >> RW_TAC std_ss [REAL_MUL_ASSOC, REAL_MUL_RINV, REAL_LT_IMP_NE]
   >> RW_TAC real_ss []);

val INV_DIFF_SUC = store_thm
  ("INV_DIFF_SUC",
   ``!n : num. 0 < n ==> (1 / &n - 1 / (&n + 1) = 1 / &(n * (n + 1)))``,
   RW_TAC std_ss [GSYM REAL_INV_1OVER]
   >> Know `~(&n = 0) /\ ~(&n + 1 = 0)`
   >- RW_TAC arith_ss [REAL_LT_NZ, REAL_NZ_IMP_LT, GSYM REAL]
   >> RW_TAC std_ss [REAL_SUB_INV2]
   >> Know `&n + 1 - &n = 1` >- REAL_ARITH_TAC
   >> RW_TAC std_ss [GSYM REAL_INV_1OVER]
   >> RW_TAC std_ss [GSYM REAL, REAL_MUL, GSYM ADD1]);

val ABS_TRIANGLE = store_thm
  ("ABS_TRIANGLE",
   ``!x y z. abs (x - z) <= abs (x - y) + abs (y - z)``,
   RW_TAC std_ss [abs]
   >> rpt (POP_ASSUM MP_TAC)
   >> REAL_ARITH_TAC);

val ABS_TRANS = store_thm
  ("ABS_TRANS",
   ``!x y z e. abs (x - y) + abs (y - z) < e ==> abs (x - z) < e``,
   rpt GEN_TAC
   >> MP_TAC (Q.SPECL [`x`, `y`, `z`] ABS_TRIANGLE)
   >> REAL_ARITH_TAC);

val INCREASING_SEQ = store_thm
  ("INCREASING_SEQ",
   ``!f l.
       (!n. f n <= f (SUC n)) /\
       (!n. f n <= l) /\
       (!e. 0 < e ==> ?n. l < f n + e) ==>
       f --> l``,
   RW_TAC std_ss [SEQ, GREATER_EQ]
   >> Q.PAT_X_ASSUM `!e. P e` (MP_TAC o Q.SPEC `e`)
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `n`
   >> ONCE_REWRITE_TAC [ABS_SUB]
   >> reverse (RW_TAC std_ss [abs])
   >- (Q.PAT_X_ASSUM `~x` MP_TAC
       >> Q.PAT_X_ASSUM `!n. P n` (MP_TAC o Q.SPEC `n'`)
       >> REAL_ARITH_TAC)
   >> Know `?d. n' = n + d` >- PROVE_TAC [LESS_EQ_EXISTS]
   >> RW_TAC std_ss []
   >> Suff `l < f (n + d) + e` >- REAL_ARITH_TAC
   >> NTAC 2 (POP_ASSUM K_TAC)
   >> Induct_on `d` >- RW_TAC arith_ss []
   >> RW_TAC std_ss [ADD_CLAUSES]
   >> Q.PAT_X_ASSUM `!n. f n <= f (SUC n)` (MP_TAC o Q.SPEC `n + d`)
   >> POP_ASSUM MP_TAC
   >> REAL_ARITH_TAC);

val SUM_CONST = store_thm
  ("SUM_CONST",
   ``!n r. sum (0,n) (K r) = &n * r``,
   Induct >- RW_TAC real_ss [sum]
   >> RW_TAC bool_ss [sum, ADD1, K_THM, GSYM REAL_ADD, REAL_ADD_RDISTRIB]
   >> RW_TAC real_ss []);

val LOG2_SUC = store_thm
  ("LOG2_SUC",
   ``!n t.
       0 < n /\ 2 * log2 (n + 1) <= t ==>
       (1 / 2) pow t <= 1 / &n - 1 / (&n + 1)``,
   REPEAT STRIP_TAC
   >> RW_TAC std_ss [INV_DIFF_SUC, POW_HALF_EXP, GSYM REAL_INV_1OVER]
   >> MATCH_MP_TAC REAL_LE_INV_LE
   >> REPEAT STRIP_TAC
   >- (MATCH_MP_TAC REAL_NZ_IMP_LT
       >> RW_TAC arith_ss [GSYM ADD1, MULT])
   >> RW_TAC std_ss [REAL_LE]
   >> Suff `(n + 1) * (n + 1) <= 2 EXP t`
   >- (Suff `n * (n + 1) <= (n + 1) * (n + 1)` >- DECIDE_TAC
       >> RW_TAC std_ss [GSYM ADD1, MULT]
       >> DECIDE_TAC)
   >> Suff `(n + 1) EXP 2 <= (2 EXP log2 (n + 1)) EXP 2`
   >- (RW_TAC bool_ss [TWO, EXP, EXP_1, EXP_MULT]
       >> POP_ASSUM MP_TAC
       >> ONCE_REWRITE_TAC [MULT_COMM]
       >> RW_TAC std_ss [GSYM TWO]
       >> MATCH_MP_TAC LESS_EQ_TRANS
       >> Q.EXISTS_TAC `2 EXP (2 * log2 (n + 1))`
       >> CONJ_TAC >- RW_TAC std_ss []
       >> MATCH_MP_TAC EXP1_MONO_LE
       >> RW_TAC arith_ss [])
   >> MATCH_MP_TAC EXP2_MONO_LE
   >> MP_TAC (Q.SPEC `n + 1` LOG2_LOWER)
   >> RW_TAC arith_ss []);

val SER_POS_COMPAR = store_thm
  ("SER_POS_COMPAR",
   ``!f g. (!n. 0 <= f n) /\ summable g /\ (!n. f n <= g n) ==> summable f``,
   PROVE_TAC [SER_POS_COMPARE]);

val SUM_SUMINF = store_thm
  ("SUM_SUMINF",
   ``!p f n.
       (summable (\m. if m < n then f m else 0) ==>
        p (suminf (\m. if m < n then f m else 0))) ==>
       p (sum (0, n) f)``,
   RW_TAC std_ss []
   >> Suff `(\m. (if m < n then f m else 0)) sums (sum (0, n) f)`
   >- (RW_TAC std_ss [SUMS_EQ]
       >> PROVE_TAC [])
   >> Suff `sum (0, n) f = sum (0, n) (\m. (if m < n then f m else 0))`
   >- (Rewr
       >> MATCH_MP_TAC SER_0
       >> RW_TAC arith_ss [])
   >> MATCH_MP_TAC SUM_EQ
   >> RW_TAC arith_ss []);

val SUMS_PICK = store_thm
  ("SUMS_PICK",
   ``!k x. (\n. if n = k then x else 0) sums x``,
   RW_TAC std_ss []
   >> Know `sum (0, SUC k) (\n. if n = k then x else 0) = x`
   >- RW_TAC arith_ss [SUM_PICK]
   >> DISCH_THEN (CONV_TAC o RAND_CONV o ONCE_REWRITE_CONV o wrap o SYM)
   >> MATCH_MP_TAC SER_0
   >> RW_TAC arith_ss []);

val SUM_REORDER_LE = store_thm
  ("SUM_REORDER_LE",
   ``!f n1 n2 j1 j2.
       (!n. 0 <= f n) /\ INJ j1 (count n1) UNIV /\
       IMAGE j1 (count n1) SUBSET IMAGE j2 (count n2) ==>
       sum (0, n1) (f o j1) <= sum (0, n2) (f o j2)``,
   Induct_on `n1`
   >- (RW_TAC std_ss [sum, COUNT_ZERO, EMPTY_SUBSET, IMAGE_EMPTY]
       >> Suff `!n. 0 <= (f o j2) n` >- RW_TAC std_ss [SUM_POS]
       >> RW_TAC std_ss [o_THM])
   >> RW_TAC std_ss [sum, o_THM, INSERT_SUBSET, COUNT_SUC, IMAGE_INSERT,
                     IN_IMAGE, IN_COUNT]
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Q.EXISTS_TAC
      `f (j1 n1) + sum (0,n2) ((\a. if a = j1 n1 then 0 else f a) o j2)`
   >> CONJ_TAC
   >- (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [REAL_ADD_COMM]))
       >> RW_TAC std_ss [REAL_LE_LADD]
       >> Know
          `sum (0, n1) (f o j1) =
           sum (0, n1) ((\a. (if a = j2 x then 0 else f a)) o j1)`
       >- (MATCH_MP_TAC SUM_EQ
           >> RW_TAC arith_ss [o_THM]
           >> Suff `F` >- PROVE_TAC []
           >> Q.PAT_X_ASSUM `INJ j1 X Y` MP_TAC
           >> RW_TAC std_ss [INJ_DEF, IN_INSERT, IN_COUNT, IN_UNIV]
           >> PROVE_TAC [prim_recTheory.LESS_NOT_EQ])
       >> Rewr
       >> Q.PAT_X_ASSUM `!f n2. P f n2` MATCH_MP_TAC
       >> RW_TAC std_ss [REAL_LE_REFL]
       >> Q.PAT_X_ASSUM `INJ j1 X Y` MP_TAC
       >> RW_TAC bool_ss [INJ_DEF, IN_INSERT, IN_COUNT, IN_UNIV])
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Q.EXISTS_TAC
      `f (j1 n1) + sum (0, n2) (\i. if i = x then 0 else f (j2 i))`
   >> CONJ_TAC
   >- (RW_TAC std_ss [REAL_LE_LADD]
       >> MATCH_MP_TAC SUM_LE
       >> RW_TAC arith_ss [o_THM, REAL_LE_REFL])
   >> Know
      `f o j2 =
       (\i. (if i = x then 0 else f (j2 i)) +
            (if i = x then f (j2 i) else 0))`
   >- (FUN_EQ_TAC
       >> RW_TAC real_ss [o_THM])
   >> Rewr
   >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [REAL_ADD_COMM]))
   >> RW_TAC real_ss [SUM_ADD, SUM_PICK, REAL_LE_LADD, REAL_LE_REFL]);

val SER_BIJ_COMPRESS1 = store_thm
  ("SER_BIJ_COMPRESS1",
   ``!f h s.
       (!n. 0 <= f n) /\ summable f /\ BIJ h UNIV s /\
       (!n. ~(n IN s) ==> (f n = 0)) ==>
       (f o h) sums suminf f``,
   RW_TAC std_ss [sums, SEQ]
   >> ONCE_REWRITE_TAC [ABS_SUB]
   >> RW_TAC std_ss [abs]
   >> Know `!n. sum (0, n) (f o h) <= suminf f`
   >- (Know `!n. ?N. !m. m < n ==> h m < N`
       >- (Induct >- RW_TAC arith_ss []
           >> POP_ASSUM MP_TAC
           >> STRIP_TAC
           >> Q.EXISTS_TAC `SUC (MAX N (h n))`
           >> STRIP_TAC
           >> DISCH_THEN (MP_TAC o REWRITE_RULE [prim_recTheory.LESS_THM])
           >> Know `!a b. a < SUC b <=> a <= b`
           >- (Cases >> STRIP_TAC >> KILL_TAC >> DECIDE_TAC)
           >> RW_TAC std_ss [X_LE_MAX]
           >> PROVE_TAC [LESS_IMP_LESS_OR_EQ, LESS_EQ_REFL])
       >> DISCH_THEN (MP_TAC o CONV_RULE SKOLEM_CONV)
       >> STRIP_TAC
       >> STRIP_TAC
       >> MATCH_MP_TAC REAL_LE_TRANS
       >> Q.EXISTS_TAC `sum (0, N n) f`
       >> reverse CONJ_TAC
       >- (MATCH_MP_TAC SER_POS_LE
           >> RW_TAC std_ss [])
       >> Know `sum (0, N n) f = sum (0, N n) (f o I)`
       >- RW_TAC std_ss [I_o_ID]
       >> Rewr
       >> MATCH_MP_TAC SUM_REORDER_LE
       >> Q.PAT_X_ASSUM `BIJ h X Y` MP_TAC
       >> RW_TAC std_ss [INJ_DEF, BIJ_DEF, IN_UNIV, IN_COUNT, SUBSET_DEF,
                         I_THM, IN_IMAGE]
       >> PROVE_TAC [])
   >> STRIP_TAC
   >> Know `!n. 0 <= suminf f - sum (0, n) (f o h)`
   >- (STRIP_TAC
       >> POP_ASSUM (MP_TAC o Q.SPEC `n`)
       >> REAL_ARITH_TAC)
   >> Rewr
   >> Know `f sums suminf f` >- PROVE_TAC [SUMMABLE_SUM]
   >> RW_TAC std_ss [sums, SEQ]
   >> POP_ASSUM (MP_TAC o Q.SPEC `e`)
   >> RW_TAC std_ss [GREATER_EQ]
   >> (MP_TAC o
       Q.SPECL [`h`, `s`, `count N INTER s`] o
       INST_TYPE [alpha |-> ``:num``])
      BIJ_FINITE_SUBSET
   >> Know `FINITE (count N INTER s)`
   >- PROVE_TAC [FINITE_COUNT, FINITE_INTER, INTER_COMM]
   >> Rewr
   >> RW_TAC std_ss [INTER_SUBSET, IN_INTER]
   >> Q.EXISTS_TAC `N'`
   >> RW_TAC std_ss []
   >> Suff `suminf f - e < sum (0, n) (f o h)` >- REAL_ARITH_TAC
   >> MATCH_MP_TAC REAL_LTE_TRANS
   >> Q.EXISTS_TAC `sum (0, N) f`
   >> CONJ_TAC
   >- (Q.PAT_X_ASSUM `!n. P n ==> Q n < e` (MP_TAC o Q.SPEC `N`)
       >> ONCE_REWRITE_TAC [ABS_SUB]
       >> RW_TAC arith_ss [abs]
       >- (POP_ASSUM MP_TAC
           >> REAL_ARITH_TAC)
       >> Suff `F` >- PROVE_TAC []
       >> POP_ASSUM K_TAC
       >> POP_ASSUM MP_TAC
       >> Suff `sum (0, N) f <= suminf f` >- REAL_ARITH_TAC
       >> MATCH_MP_TAC SER_POS_LE
       >> RW_TAC std_ss [])
   >> Know
      `sum (0, N) f =
       sum (0, N) ((\x. sum_CASE x f (K 0)) o
                   (\n. if n IN s then INL n else INR n))`
   >- (MATCH_MP_TAC SUM_EQ
       >> RW_TAC std_ss [sum_case_def, o_THM, K_DEF])
   >> Rewr
   >> Know
      `sum (0, n) (f o h) =
       sum (0, n + N)
       ((\x. sum_CASE x f (K 0)) o
        (\i. if i < n then INL (h i) else INR (i - n)))`
   >- (KILL_TAC
       >> reverse (Induct_on `N`)
       >- RW_TAC arith_ss [sum, o_THM, ADD_CLAUSES, K_THM, REAL_ADD_RID]
       >> RW_TAC arith_ss []
       >> MATCH_MP_TAC SUM_EQ
       >> RW_TAC arith_ss [sum_case_def, o_THM])
   >> Rewr
   >> MATCH_MP_TAC SUM_REORDER_LE
   >> Q.PAT_X_ASSUM `BIJ h X Y` MP_TAC
   >> ASM_SIMP_TAC (srw_ss()) [sumTheory.FORALL_SUM]
   >> BasicProvers.NORM_TAC std_ss [SUBSET_DEF, IN_IMAGE, INJ_DEF, IN_UNIV,
                                    IN_COUNT, INJ_DEF, BIJ_DEF, SURJ_DEF] >|
   [Q.PAT_X_ASSUM `!x. P x` (MP_TAC o Q.SPEC `n'`)
    >> RW_TAC std_ss []
    >> Q.EXISTS_TAC `y`
    >> RW_TAC std_ss []
    >> Suff `y < n` >- RW_TAC arith_ss []
    >> Q.PAT_X_ASSUM `!n. P n ==> Q n` (MP_TAC o Q.SPEC `y`)
    >> RW_TAC std_ss [IN_COUNT]
    >> POP_ASSUM MP_TAC
    >> Q.PAT_X_ASSUM `N' <= n` MP_TAC
    >> KILL_TAC
    >> DECIDE_TAC,
    Q.EXISTS_TAC `n' + n`
    >> RW_TAC arith_ss []]);

val SER_BIJ_COMPRESS2 = store_thm
  ("SER_BIJ_COMPRESS2",
   ``!f h s.
       (!n. 0 <= f n) /\ summable (f o h) /\ BIJ h UNIV s /\
       (!n. ~(n IN s) ==> (f n = 0)) ==>
       f sums suminf (f o h)``,
   RW_TAC std_ss [sums, SEQ]
   >> ONCE_REWRITE_TAC [ABS_SUB]
   >> RW_TAC std_ss [abs]
   >> Know `!n. sum (0, n) f <= suminf (f o h)`
   >- (STRIP_TAC
       >> (MP_TAC o
           Q.SPECL [`h`, `s`, `count n INTER s`] o
           INST_TYPE [alpha |-> ``:num``])
           BIJ_FINITE_SUBSET
       >> Know `FINITE (count n INTER s)`
       >- PROVE_TAC [FINITE_COUNT, FINITE_INTER, INTER_COMM]
       >> Rewr
       >> RW_TAC std_ss [INTER_SUBSET, IN_INTER]
       >> MATCH_MP_TAC REAL_LE_TRANS
       >> Q.EXISTS_TAC `sum (0, N) (f o h)`
       >> reverse CONJ_TAC
       >- (MATCH_MP_TAC SER_POS_LE
           >> RW_TAC std_ss [o_THM])
       >> Know
       `sum (0, n) f =
        sum (0, n) ((\x. sum_CASE x f (K 0)) o
                    (\n. if n IN s then INL n else INR n))`
        >- (MATCH_MP_TAC SUM_EQ
            >> RW_TAC std_ss [sum_case_def, o_THM, K_DEF])
       >> Rewr
       >> Know
       `sum (0, N) (f o h) =
        sum (0, N + n)
        ((\x. sum_CASE x f (K 0)) o
         (\i. if i < N then INL (h i) else INR (i - N)))`
       >- (KILL_TAC
           >> reverse (Induct_on `n`)
           >- RW_TAC arith_ss [sum, o_THM, ADD_CLAUSES, K_THM, REAL_ADD_RID]
           >> RW_TAC arith_ss []
           >> MATCH_MP_TAC SUM_EQ
           >> RW_TAC arith_ss [sum_case_def, o_THM])
       >> Rewr
       >> MATCH_MP_TAC SUM_REORDER_LE
       >> ASM_SIMP_TAC (srw_ss()) [sumTheory.FORALL_SUM]
       >> Q.PAT_X_ASSUM `BIJ h X Y` MP_TAC
       >> BasicProvers.NORM_TAC std_ss [SUBSET_DEF, IN_IMAGE, INJ_DEF, IN_UNIV,
                                        IN_COUNT, INJ_DEF, BIJ_DEF, SURJ_DEF] >|
       [Q.PAT_X_ASSUM `!x. P x` (MP_TAC o Q.SPEC `n'`)
        >> RW_TAC std_ss []
        >> Q.EXISTS_TAC `y`
        >> Suff `y < N` >- RW_TAC arith_ss []
        >> Q.PAT_X_ASSUM `!n'. N <= n' ==> P n'` (MP_TAC o Q.SPEC `y`)
        >> RW_TAC std_ss [IN_COUNT]
        >> POP_ASSUM MP_TAC
        >> KILL_TAC
        >> DECIDE_TAC,
        Q.EXISTS_TAC `n' + N`
        >> RW_TAC arith_ss []])
   >> STRIP_TAC
   >> Know `!n. 0 <= suminf (f o h) - sum (0, n) f`
   >- (STRIP_TAC
       >> POP_ASSUM (MP_TAC o Q.SPEC `n`)
       >> REAL_ARITH_TAC)
   >> Rewr
   >> Know `(f o h) sums suminf (f o h)` >- PROVE_TAC [SUMMABLE_SUM]
   >> RW_TAC std_ss [sums, SEQ]
   >> POP_ASSUM (MP_TAC o Q.SPEC `e`)
   >> RW_TAC std_ss [GREATER_EQ]
   >> Know `!n. ?N. !m. m < n ==> h m < N`
   >- (Induct >- RW_TAC arith_ss []
       >> POP_ASSUM MP_TAC
       >> STRIP_TAC
       >> Q.EXISTS_TAC `SUC (MAX N' (h n))`
       >> STRIP_TAC
       >> DISCH_THEN (MP_TAC o REWRITE_RULE [prim_recTheory.LESS_THM])
       >> Know `!a b. a < SUC b <=> a <= b`
       >- (Cases >> STRIP_TAC >> KILL_TAC >> DECIDE_TAC)
       >> RW_TAC std_ss [X_LE_MAX]
       >> PROVE_TAC [LESS_IMP_LESS_OR_EQ, LESS_EQ_REFL])
   >> DISCH_THEN (MP_TAC o CONV_RULE SKOLEM_CONV)
   >> STRIP_TAC
   >> Q.EXISTS_TAC `N' N`
   >> RW_TAC std_ss []
   >> Suff `suminf (f o h) - e < sum (0, n) f` >- REAL_ARITH_TAC
   >> MATCH_MP_TAC REAL_LTE_TRANS
   >> Q.EXISTS_TAC `sum (0, N) (f o h)`
   >> CONJ_TAC
   >- (Suff `suminf (f o h) - sum (0, N) (f o h) < e` >- REAL_ARITH_TAC
       >> Q.PAT_X_ASSUM `!n. N <= n ==> P n` (MP_TAC o Q.SPEC `N`)
       >> ONCE_REWRITE_TAC [ABS_SUB]
       >> RW_TAC arith_ss [abs]
       >> Suff `F` >- PROVE_TAC []
       >> POP_ASSUM K_TAC
       >> POP_ASSUM MP_TAC
       >> Suff `sum (0, N) (f o h) <= suminf (f o h)` >- REAL_ARITH_TAC
       >> MATCH_MP_TAC SER_POS_LE
       >> RW_TAC std_ss [o_THM])
   >> Know `sum (0, n) f = sum (0, n) (f o I)`
   >- RW_TAC std_ss [I_o_ID]
   >> Rewr
   >> MATCH_MP_TAC SUM_REORDER_LE
   >> Q.PAT_X_ASSUM `BIJ h X Y` MP_TAC
   >> RW_TAC std_ss [INJ_DEF, BIJ_DEF, IN_UNIV, IN_COUNT, SUBSET_DEF,
                     I_THM, IN_IMAGE]
   >> Q.PAT_X_ASSUM `N' N <= n` MP_TAC
   >> Suff `h x' < N' N` >- (KILL_TAC >> DECIDE_TAC)
   >> PROVE_TAC []);

val SER_BIJ_COMPRESS = store_thm
  ("SER_BIJ_COMPRESS",
   ``!f h s l.
       (!n. 0 <= f n) /\ BIJ h UNIV s /\ (!n. ~(n IN s) ==> (f n = 0)) ==>
       ((f o h) sums l <=> f sums l)``,
   RW_TAC std_ss [SUMS_EQ]
   >> EQ_TAC >|
   [STRIP_TAC
    >> REWRITE_TAC [GSYM SUMS_EQ]
    >> RW_TAC std_ss []
    >> PROVE_TAC [SER_BIJ_COMPRESS2],
    STRIP_TAC
    >> REWRITE_TAC [GSYM SUMS_EQ]
    >> RW_TAC std_ss []
    >> PROVE_TAC [SER_BIJ_COMPRESS1]]);

val SER_BIJ = store_thm
  ("SER_BIJ",
   ``!f g h l.
       (!n. 0 <= f n) /\ BIJ h UNIV UNIV ==>
       ((f o h) sums l <=> f sums l)``,
   RW_TAC std_ss []
   >> MATCH_MP_TAC SER_BIJ_COMPRESS
   >> Q.EXISTS_TAC `UNIV`
   >> RW_TAC std_ss [IN_UNIV]);

val SUMS_ZERO = store_thm
  ("SUMS_ZERO",
   ``(K 0) sums 0``,
   RW_TAC real_ss [sums, SEQ, SUM_CONST, abs, REAL_SUB_REFL, REAL_LE_REFL]);

val GP_REC = store_thm
  ("GP_REC",
   ``!a b x : real. abs b < 1 /\ (x = a + b * x) ==> (x = a / (1 - b))``,
   RW_TAC std_ss []
   >> Know `x * (1 - b) = a`
   >- (RW_TAC std_ss [REAL_SUB_LDISTRIB, REAL_MUL_RID]
       >> ONCE_REWRITE_TAC [REAL_MUL_SYM]
       >> POP_ASSUM MP_TAC
       >> REAL_ARITH_TAC)
   >> POP_ASSUM K_TAC
   >> Know `~(1 - b = 0)`
   >- (POP_ASSUM MP_TAC
       >> RW_TAC real_ss [abs]
       >> REPEAT (POP_ASSUM MP_TAC)
       >> REAL_ARITH_TAC)
   >> POP_ASSUM K_TAC
   >> REPEAT STRIP_TAC
   >> Suff `x * (1 - b) = (a / (1 - b)) * (1 - b)`
   >- (POP_ASSUM K_TAC
       >> RW_TAC std_ss [REAL_EQ_RMUL])
   >> RW_TAC std_ss [real_div, GSYM REAL_INV_1OVER, GSYM REAL_MUL_ASSOC,
                     REAL_MUL_LINV, REAL_MUL_RID]);

val REAL_DIV_EQ = store_thm
  ("REAL_DIV_EQ",
   ``!a b c d : real.
       ~(b = 0) /\ ~(d = 0) /\ (a * d = c * b) ==> (a / b = c / d)``,
   RW_TAC std_ss [real_div]
   >> Suff `(a * inv b) * b = (c * inv d) * b`
   >- RW_TAC std_ss [REAL_EQ_RMUL]
   >> RW_TAC std_ss [GSYM REAL_MUL_ASSOC, REAL_MUL_LINV, REAL_MUL_RID]
   >> Suff `a * d = (c * (inv d * b)) * d`
   >- RW_TAC std_ss [REAL_EQ_RMUL]
   >> Know `inv d * b = b * inv d` >- PROVE_TAC [REAL_MUL_SYM]
   >> Rewr
   >> RW_TAC std_ss [GSYM REAL_MUL_ASSOC, REAL_MUL_LINV, REAL_MUL_RID]);

val REAL_DIV_MUL = store_thm
  ("REAL_DIV_MUL",
   ``!x y z. ~(x = 0) /\ ~(z = 0) ==> ((x * y) / (x * z) = y / z)``,
   PROVE_TAC [REAL_DIV_MUL2]);

val REAL_LDIV_EQ = store_thm
  ("REAL_LDIV_EQ",
   ``!x y z. ~(y = 0) /\ (x = y * z) ==> (x / y = z)``,
   REPEAT STRIP_TAC
   >> Know `z = z / 1` >- RW_TAC std_ss [REAL_OVER1]
   >> Rewr'
   >> MATCH_MP_TAC REAL_DIV_EQ
   >> RW_TAC real_ss []
   >> REAL_ARITH_TAC);

val ADD1_HALF_MULT = store_thm
  ("ADD1_HALF_MULT",
   ``!x y. x + (1 / 2) * y = (1 / 2) * (2 * x + y)``,
   RW_TAC std_ss [REAL_ADD_LDISTRIB, REAL_MUL_ASSOC]
   >> Know `(1 / 2) * 2 = 2 * (1 / 2)` >- PROVE_TAC [REAL_MUL_SYM]
   >> Rewr
   >> RW_TAC std_ss [HALF_CANCEL, REAL_MUL_LID]);

val ADD2_HALF_MULT = store_thm
  ("ADD2_HALF_MULT",
   ``!x y. (1 / 2) * y + x = (1 / 2) * (y + 2 * x)``,
   PROVE_TAC [ADD1_HALF_MULT, REAL_ADD_SYM]);

val HALF_CANCEL_REV = store_thm
  ("HALF_CANCEL_REV",
   ``(1 / 2) * 2 = 1``,
   PROVE_TAC [HALF_CANCEL, REAL_MUL_SYM]);

val HALF_CANCEL_MULT = store_thm
  ("HALF_CANCEL_MULT",
   ``!x. 2 * ((1 / 2) * x) = x``,
   RW_TAC std_ss [HALF_CANCEL, REAL_MUL_ASSOC, REAL_MUL_LID]);

val HALF_CANCEL_MULT_REV = store_thm
  ("HALF_CANCEL_MULT_REV",
   ``!x. (1 / 2) * (2 * x) = x``,
   RW_TAC std_ss [HALF_CANCEL_REV, REAL_MUL_ASSOC, REAL_MUL_LID]);

val ABS_EQ = store_thm
  ("ABS_EQ",
   ``!x y. (!e. 0 < e ==> abs (x - y) < e) ==> (x = y)``,
   RW_TAC std_ss []
   >> MATCH_MP_TAC SEQ_UNIQ
   >> Q.EXISTS_TAC `\n. x`
   >> RW_TAC std_ss [SEQ_CONST]
   >> RW_TAC std_ss [SEQ]);

val POW_LE_1 = store_thm
  ("POW_LE_1",
   ``!p n. 0 < p /\ p <= 1 ==> p pow n <= 1``,
   STRIP_TAC
   >> Induct
   >> RW_TAC std_ss [pow, REAL_LE_REFL]
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Q.EXISTS_TAC `p * 1`
   >> reverse CONJ_TAC >- RW_TAC real_ss []
   >> RW_TAC std_ss [REAL_LE_LMUL]);

val POW_LE_1_MONO = store_thm
  ("POW_LE_1_MONO",
   ``!p m n. 0 < p /\ p <= 1 /\ m <= n ==> p pow n <= p pow m``,
   RW_TAC std_ss []
   >> POP_ASSUM MP_TAC
   >> Q.SPEC_TAC (`n`, `n`)
   >> Q.SPEC_TAC (`m`, `m`)
   >> HO_MATCH_MP_TAC TRIANGLE_2D_NUM
   >> Induct >- RW_TAC real_ss [REAL_LE_REFL]
   >> RW_TAC std_ss [ADD_CLAUSES, pow]
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Q.EXISTS_TAC `1 * p pow (d + m)`
   >> reverse CONJ_TAC >- RW_TAC real_ss []
   >> RW_TAC std_ss [REAL_LE_RMUL, REAL_POW_LT]);

val REAL_LE_MUL_EPSILON = store_thm
  ("REAL_LE_MUL_EPSILON",
   ``!x y. (!z. 0 < z /\ z < 1 ==> z * x <= y) ==> x <= y``,
    REPEAT STRIP_TAC
    >> Cases_on `x = 0`
    >- (Q.PAT_X_ASSUM `!z. P z` (MP_TAC o Q.SPEC `1/2`) >> RW_TAC real_ss [REAL_HALF_BETWEEN])
    >> Cases_on `0 < x`
    >- (MATCH_MP_TAC REAL_LE_EPSILON
        >> RW_TAC std_ss [GSYM REAL_LE_SUB_RADD]
        >> Cases_on `e < x`
        >- (MATCH_MP_TAC REAL_LE_TRANS
            >> Q.EXISTS_TAC `(1-(e/x))*x`
            >> CONJ_TAC
            >- (RW_TAC real_ss [REAL_SUB_RDISTRIB] >> METIS_TAC [REAL_DIV_RMUL, REAL_LE_REFL])
            >> Q.PAT_X_ASSUM `!z. P z` MATCH_MP_TAC
            >> RW_TAC real_ss [REAL_LT_SUB_RADD, REAL_LT_ADDR, REAL_LT_DIV, REAL_LT_SUB_LADD, REAL_LT_1, REAL_LT_IMP_LE])
        >> FULL_SIMP_TAC std_ss [REAL_NOT_LT]
        >> MATCH_MP_TAC REAL_LE_TRANS
        >> Q.EXISTS_TAC `0`
        >> RW_TAC real_ss [REAL_LE_SUB_RADD]
        >> MATCH_MP_TAC REAL_LE_TRANS
        >> Q.EXISTS_TAC `(1/2)*x`
        >> RW_TAC real_ss [REAL_LE_MUL, REAL_LT_IMP_LE])
    >> MATCH_MP_TAC REAL_LE_TRANS
    >> Q.EXISTS_TAC `(1/2)*x`
    >> RW_TAC real_ss []
    >> RW_TAC std_ss [Once (GSYM REAL_LE_NEG), GSYM REAL_MUL_RNEG]
    >> Suff `1/2 * ~x <= 1 * ~x` >- RW_TAC real_ss []
    >> METIS_TAC [REAL_NEG_GT0, REAL_LT_TOTAL, REAL_LE_REFL, REAL_HALF_BETWEEN, REAL_LE_RMUL]);

val _ = export_theory ();
