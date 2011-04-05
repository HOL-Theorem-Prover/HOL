(* ========================================================================= *)
(* FILE          : blastScript.sml                                           *)
(* DESCRIPTION   : A bitwise treatment of addition, multiplication           *)
(*                 and shifting.                                             *)
(* AUTHOR        : Anthony Fox, University of Cambridge                      *)
(* DATE          : 2010,2011                                                 *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;
open fcpLib arithmeticTheory bitTheory wordsTheory wordsLib;

val _ = new_theory "blast";

infix \\ <<

val op \\ = op THEN;
val op << = op THENL;

(* -------------------------------------------------------------------------
   Ripple carry addition
   ------------------------------------------------------------------------- *)

(* --------------------------------------------------------
   "BCARRY i x y c" is the i-th carry-out bit for the
   summuation of bit streams "x" and "y" with carry-in "c"
   -------------------------------------------------------- *)

val bcarry_def = new_definition ("bcarry_def",
  ``bcarry x y c = x /\ y \/ (x \/ y) /\ c``);

val BCARRY_def = Define`
  (BCARRY 0 x y c = c) /\
  (BCARRY (SUC i) x y c = bcarry (x i) (y i) (BCARRY i x y c))`;

(* --------------------------------------------------------
   "BSUM i x y c" is the i-th bit for the summuation of
   bit streams "x" and "y" with carry-in "c"
   -------------------------------------------------------- *)

val bsum_def = new_definition ("bsum_def",
  ``bsum (x:bool) y c = ((x = ~y) = ~c)``);

val BSUM_def = new_definition ("BSUM_def",
  ``BSUM i x y c = bsum (x i) (y i) (BCARRY i x y c)``);

(* ------------------------------------------------------------------------- *)

val BIT_CASES = Q.prove(
  `!b n. (BITS b b n = 0) \/ (BITS b b n = 1)`,
  SIMP_TAC std_ss [GSYM NOT_BITS2]);

val BITS_SUC_cor =
  BITS_SUC |> Q.SPECL [`n`,`0`,`x`]
           |> SIMP_RULE std_ss []
           |> GSYM
           |> GEN_ALL;

val BITS_SUM_cor =
  BITS_SUM |> SPEC_ALL
           |> Q.INST [`a` |-> `1`]
           |> SIMP_RULE std_ss []
           |> GEN_ALL;

val lem =
  bitTheory.TWOEXP_MONO
  |> Q.SPECL [`0`,`n`]
  |> SIMP_RULE bool_ss [ZERO_LESS_EQ, EXP]
  |> GEN_ALL;

val lem1 = Q.prove (
  `!n. 0 < n ==> 2 ** n + 1 < 2 ** SUC n`,
  SRW_TAC [] [EXP, TIMES2, lem]);

val lem2 =
  NOT_BIT_GT_TWOEXP
  |> Q.SPECL [`SUC n`,`1`]
  |> SIMP_RULE std_ss [lem]
  |> GEN_ALL;

val BCARRY_LEM = Q.store_thm("BCARRY_LEM",
  `!i x y c.
     0 < i ==>
     (BCARRY i (\i. BIT i x) (\i. BIT i y) c =
      BIT i (BITS (i - 1) 0 x + BITS (i - 1) 0 y + (if c then 1 else 0)))`,
  Induct
  \\ SRW_TAC [] [BCARRY_def, bcarry_def]
  \\ Cases_on `i`
  << [SRW_TAC [] [BCARRY_def, BIT_def]
      \\ Q.SPECL_THEN [`0`,`x`] STRIP_ASSUME_TAC BIT_CASES
      \\ Q.SPECL_THEN [`0`,`y`] STRIP_ASSUME_TAC BIT_CASES
      \\ ASM_SIMP_TAC std_ss [BITS_THM],

      POP_ASSUM (fn th => SIMP_TAC std_ss [th])
      \\ Q.SPECL_THEN [`n`,`0`,`x`] (ASSUME_TAC o SIMP_RULE std_ss [])
           BITSLT_THM
      \\ Q.SPECL_THEN [`n`,`0`,`y`] (ASSUME_TAC o SIMP_RULE std_ss [])
           BITSLT_THM
      \\ `BITS n 0 x + BITS n 0 y + 1 < 2 * 2 ** SUC n` by DECIDE_TAC
      \\ Cases_on `BIT (SUC n) x`
      \\ Cases_on `BIT (SUC n) y`
      \\ FULL_SIMP_TAC arith_ss
           [BITS_SUC_cor, SBIT_def, BIT_def, GSYM EXP, BITS_SUM_cor]
      \\ FULL_SIMP_TAC std_ss [GSYM BIT_def, BIT_B, NOT_BIT_GT_TWOEXP]
      \\ `BITS n 0 x + (BITS n 0 y + 1) = BITS n 0 x + BITS n 0 y + 1`
      by DECIDE_TAC
      \\ POP_ASSUM SUBST_ALL_TAC
      \\ Cases_on `BITS n 0 x + BITS n 0 y = 0`
      \\ ASM_SIMP_TAC std_ss [lem1, lem2, BIT_ZERO, NOT_BIT_GT_TWOEXP]
      \\ (Cases_on `BIT (SUC n) (BITS n 0 x + BITS n 0 y + 1)`
      \\ ASM_SIMP_TAC std_ss []
      << [IMP_RES_TAC
            (METIS_PROVE [NOT_BIT_GT_TWOEXP, NOT_LESS]
               ``BIT i (a + b + 1) ==> 2 ** i <= (a + b + 1)``)
          \\ IMP_RES_TAC LESS_EQUAL_ADD
          \\ `p < 2 ** SUC (SUC n)`
          by FULL_SIMP_TAC arith_ss []
          \\ Q.PAT_ASSUM `a + b = c + d:num` SUBST1_TAC
          \\ ASM_SIMP_TAC arith_ss [BIT_def, GSYM EXP,
               ONCE_REWRITE_RULE [ADD_COMM] BITS_SUM_cor]
          \\ SIMP_TAC std_ss [GSYM BIT_def, BIT_B],
          `BITS n 0 x + BITS n 0 y + 1 <> 0`
          by DECIDE_TAC
          \\ `BITS n 0 x + BITS n 0 y + 1 < 2 ** SUC n`
          by METIS_TAC [NOT_LESS, LOG2_UNIQUE, BIT_LOG2]
          \\ `2 ** SUC n + (BITS n 0 x + BITS n 0 y + 1) < 2 * 2 ** SUC n`
          by DECIDE_TAC
          \\ FULL_SIMP_TAC std_ss [GSYM EXP, NOT_BIT_GT_TWOEXP]]),

      SRW_TAC [] [BCARRY_def, BIT_def]
      \\ Q.SPECL_THEN [`0`,`x`] STRIP_ASSUME_TAC BIT_CASES
      \\ Q.SPECL_THEN [`0`,`y`] STRIP_ASSUME_TAC BIT_CASES
      \\ ASM_SIMP_TAC std_ss [BITS_THM],

      POP_ASSUM (fn th => SIMP_TAC std_ss [th])
      \\ Q.SPECL_THEN [`n`,`0`,`x`] (ASSUME_TAC o SIMP_RULE std_ss [])
           BITSLT_THM
      \\ Q.SPECL_THEN [`n`,`0`,`y`] (ASSUME_TAC o SIMP_RULE std_ss [])
           BITSLT_THM
      \\ `BITS n 0 x + BITS n 0 y < 2 * 2 ** SUC n` by DECIDE_TAC
      \\ Cases_on `BIT (SUC n) x`
      \\ Cases_on `BIT (SUC n) y`
      \\ FULL_SIMP_TAC arith_ss
           [BITS_SUC_cor, SBIT_def, BIT_def, GSYM EXP, BITS_SUM_cor]
      \\ FULL_SIMP_TAC std_ss [GSYM BIT_def, BIT_B, NOT_BIT_GT_TWOEXP]
      \\ Cases_on `BITS n 0 x + BITS n 0 y = 0`
      \\ ASM_SIMP_TAC std_ss [BIT_ZERO, NOT_BIT_GT_TWOEXP]
      \\ (Cases_on `BIT (SUC n) (BITS n 0 x + BITS n 0 y)`
      \\ ASM_SIMP_TAC std_ss []
      << [IMP_RES_TAC
            (METIS_PROVE [NOT_BIT_GT_TWOEXP, NOT_LESS]
               ``BIT i (a + b) ==> 2 ** i <= (a + b)``)
          \\ IMP_RES_TAC LESS_EQUAL_ADD
          \\ `p < 2 ** SUC (SUC n)`
          by FULL_SIMP_TAC arith_ss []
          \\ Q.PAT_ASSUM `a + b = c + d:num` SUBST1_TAC
          \\ ASM_SIMP_TAC arith_ss [BIT_def, GSYM EXP,
               ONCE_REWRITE_RULE [ADD_COMM] BITS_SUM_cor]
          \\ SIMP_TAC std_ss [GSYM BIT_def, BIT_B],
          `BITS n 0 x + BITS n 0 y < 2 ** SUC n`
          by METIS_TAC [NOT_LESS, LOG2_UNIQUE, BIT_LOG2]
          \\ `2 ** SUC n + (BITS n 0 x + BITS n 0 y) < 2 * 2 ** SUC n`
          by DECIDE_TAC
          \\ FULL_SIMP_TAC std_ss [GSYM EXP, NOT_BIT_GT_TWOEXP]
      ])
  ]
);

(* ------------------------------------------------------------------------ *)

val BCARRY_EQ = Q.store_thm("BCARRY_EQ",
  `!n c x1 x2 y1 y2.
     (!i. i < n ==> (x1 i = x2 i) /\ (y1 i = y2 i)) ==>
     (BCARRY n x1 y1 c = BCARRY n x2 y2 c)`,
  Induct \\ SRW_TAC [] [BCARRY_def]
  \\ `!i. i < n ==> (x1 i = x2 i) /\ (y1 i = y2 i)`
  by ASM_SIMP_TAC arith_ss []
  \\ RES_TAC \\ ASM_REWRITE_TAC []);

val BSUM_EQ = Q.store_thm("BSUM_EQ",
  `!n c x1 x2 y1 y2.
     (!i. i <= n ==> (x1 i = x2 i) /\ (y1 i = y2 i)) ==>
     (BSUM n x1 y1 c = BSUM n x2 y2 c)`,
  SRW_TAC [] [BSUM_def]
  \\ `!i. i < n ==> (x1 i = x2 i) /\ (y1 i = y2 i)`
  by ASM_SIMP_TAC arith_ss []
  \\ IMP_RES_TAC BCARRY_EQ
  \\ ASM_REWRITE_TAC []);

val word_1comp =
  word_1comp_def |> SIMP_RULE (std_ss++fcpLib.FCP_ss) [] |> GSYM

val BCARRY_BIT_EQ = Q.prove(
  `!n x y c.
     n <= dimindex (:'a) /\ y < dimword (:'a) ==>
     (BCARRY n ($' (n2w x :'a word)) ($~ o $' (n2w y :'a word)) c =
      BCARRY n (\i. BIT i x) (\i. BIT i (dimword (:'a) - 1 - y)) c)`,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC BCARRY_EQ
  \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC arith_ss [word_1comp, word_1comp_n2w]
  \\ SRW_TAC [fcpLib.FCP_ss, numSimps.ARITH_ss] [word_index]);

val BSUM_BIT_EQ = Q.prove(
  `!n x y c.
     n < dimindex (:'a) ==>
     (BSUM n ($' (n2w x :'a word)) ($' (n2w y :'a word)) c =
      BSUM n (\i. BIT i x) (\i. BIT i y) c)`,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC BSUM_EQ
  \\ SRW_TAC [fcpLib.FCP_ss, numSimps.ARITH_ss] [word_index]);

(* ------------------------------------------------------------------------ *)

val BITS_DIVISION =
   DIVISION |> Q.SPEC `2 ** SUC n`
            |> SIMP_RULE std_ss [ZERO_LT_TWOEXP, GSYM BITS_ZERO3]
            |> GEN_ALL;

val ADD_BITS_SUC_CIN = Q.prove(
  `!n a b.
     BITS (SUC n) (SUC n) (a + b + 1) =
     (BITS (SUC n) (SUC n) a + BITS (SUC n) (SUC n) b +
      BITS (SUC n) (SUC n) (BITS n 0 a + BITS n 0 b + 1)) MOD 2`,
  REPEAT STRIP_TAC
    \\ Q.SPECL_THEN [`n`,`a`] ASSUME_TAC BITS_DIVISION
    \\ POP_ASSUM (fn th => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [th])))
    \\ Q.SPECL_THEN [`n`,`b`] ASSUME_TAC BITS_DIVISION
    \\ POP_ASSUM (fn th => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [th])))
    \\ SRW_TAC [] [BITS_THM, SUC_SUB]
    \\ Cases_on `(a DIV 2 ** SUC n) MOD 2 = 1`
    \\ Cases_on `(b DIV 2 ** SUC n) MOD 2 = 1`
    \\ FULL_SIMP_TAC arith_ss [NOT_MOD2_LEM2, ADD_MODULUS]
    \\ REWRITE_TAC [DECIDE ``a * n + (b * n + c) = (a + b) * n + c:num``]
    \\ SIMP_TAC std_ss [ADD_DIV_ADD_DIV, ZERO_LT_TWOEXP]
    \\ CONV_TAC (LHS_CONV
         (SIMP_CONV std_ss [Once (GSYM MOD_PLUS), ZERO_LT_TWOEXP]))
    \\ CONV_TAC (LHS_CONV (RATOR_CONV
         (SIMP_CONV std_ss [Once (GSYM MOD_PLUS), ZERO_LT_TWOEXP])))
    \\ ASM_SIMP_TAC arith_ss []
    );

val ADD_BIT_SUC_CIN = Q.prove(
  `!n a b.
     BIT (SUC n) (a + b + 1) =
     if BIT (SUC n) (BITS n 0 a + BITS n 0 b + 1) then
       BIT (SUC n) a = BIT (SUC n) b
     else
       BIT (SUC n) a <> BIT (SUC n) b`,
  SRW_TAC [] [BIT_def]
    \\ CONV_TAC (LHS_CONV (SIMP_CONV std_ss [Once ADD_BITS_SUC_CIN]))
    \\ Cases_on `BITS (SUC n) (SUC n) a = 1`
    \\ Cases_on `BITS (SUC n) (SUC n) b = 1`
    \\ FULL_SIMP_TAC std_ss [NOT_BITS2]);

val BSUM_LEM = Q.store_thm("BSUM_LEM",
  `!i x y c.
      BSUM i (\i. BIT i x) (\i. BIT i y) c =
      BIT i (x + y + if c then 1 else 0)`,
  Induct
  <<[SRW_TAC [] [ADD_BIT0, BSUM_def, BCARRY_def, bsum_def, bcarry_def,
                 BIT_def, BITS_THM2]
     \\ DECIDE_TAC,
     SRW_TAC [] [BSUM_def, BCARRY_LEM]
     \\ FULL_SIMP_TAC std_ss [BITS_COMP_THM2, BIT_OF_BITS_THM2, bsum_def]
     \\ METIS_TAC [ADD_BIT_SUC,ADD_BIT_SUC_CIN]]);

(* ------------------------------------------------------------------------ *)

val BITWISE_ADD = Q.store_thm("BITWISE_ADD",
  `!x y. x + y = FCP i. BSUM i ($' x) ($' y) F`,
  Cases \\ Cases
  \\ SRW_TAC [fcpLib.FCP_ss] [word_add_n2w, word_index, BSUM_LEM, BSUM_BIT_EQ]);

val BSUM_LEM_COR =
  BSUM_LEM |> SPEC_ALL |> SYM |> Q.INST [`c` |-> `T`] |> SIMP_RULE std_ss []

val BITWISE_SUB = Q.store_thm("BITWISE_SUB",
  `!x y. x - y = FCP i. BSUM i ($' x) ((~) o ($' y)) T`,
  Cases \\ Cases
  \\ REWRITE_TAC [word_sub_def, word_add_n2w, word_1comp_n2w, WORD_NEG]
  \\ SRW_TAC [fcpLib.FCP_ss] [word_index, ADD_ASSOC, BSUM_LEM_COR]
  \\ MATCH_MP_TAC BSUM_EQ
  \\ SRW_TAC [numSimps.ARITH_ss] [word_index, word_1comp, word_1comp_n2w]);

(* ------------------------------------------------------------------------ *)

val SUB1_SUC = DECIDE (Term `!n. 0 < n ==> (SUC (n - 1) = n)`);

val BITWISE_LO = Q.store_thm("BITWISE_LO",
  `!x y:'a word. x <+ y = ~BCARRY (dimindex (:'a)) ($' x) ((~) o ($' y)) T`,
  Cases \\ Cases
  \\ SRW_TAC [fcpLib.FCP_ss, boolSimps.LET_ss]
       [DIMINDEX_GT_0, word_lo_def, nzcv_def, BCARRY_BIT_EQ, BCARRY_LEM]
  \\ Cases_on `n' = 0`
  \\ FULL_SIMP_TAC arith_ss [dimword_def, bitTheory.BITS_ZERO3, SUB1_SUC,
       DIMINDEX_GT_0, word_2comp_n2w, w2n_n2w]
  \\ ASM_SIMP_TAC std_ss [BIT_def,
       BITS_SUM |> SPEC_ALL |> Q.INST [`a` |-> `1n`]
                |> SIMP_RULE std_ss [Once ADD_COMM]]
   \\ SIMP_TAC std_ss [GSYM BIT_def, BIT_B]);

(* ------------------------------------------------------------------------- *)

val BITWISE_MUL_lem = Q.prove(
  `!n w m : 'a word.
     0 < n /\ n <= dimindex(:'a) ==>
     (FOLDL (\a j. a + FCP i. w ' j /\ (m << j) ' i) 0w (COUNT_LIST n) =
      (n - 1 -- 0) w * m)`,
  Induct_on `n`
  \\ SRW_TAC [] [rich_listTheory.COUNT_LIST_SNOC, listTheory.FOLDL_SNOC]
  \\ Cases_on `n = 0`
  THENL [
    Cases_on `w` \\ Cases_on `m`
    \\ SRW_TAC [fcpLib.FCP_ss]
         [rich_listTheory.COUNT_LIST_compute, word_bits_n2w, word_mul_n2w,
          word_index, BITS_THM, bitTheory.ODD_MOD2_LEM]
    \\ Cases_on `n' MOD 2 = 1`
    \\ FULL_SIMP_TAC std_ss [bitTheory.NOT_MOD2_LEM2, bitTheory.BIT_ZERO],
    `0 < n` by DECIDE_TAC
    \\ `(n '' n) w && (n - 1 -- 0) w = 0w`
    by (SRW_TAC [wordsLib.WORD_BIT_EQ_ss, ARITH_ss] []
        \\ Cases_on `i = n` \\ SRW_TAC [ARITH_ss] []
        \\ Cases_on `i < n` \\ SRW_TAC [ARITH_ss] [])
    \\ IMP_RES_TAC wordsTheory.WORD_ADD_OR
    \\ `(n -- 0) w = (n '' n) w + (n - 1 -- 0) w`
    by (SRW_TAC [wordsLib.WORD_BIT_EQ_ss] []
        \\ Cases_on `i = n` \\ SRW_TAC [ARITH_ss] []
        \\ Cases_on `i < n` \\ SRW_TAC [ARITH_ss] [])
    \\ POP_ASSUM SUBST1_TAC
    \\ SRW_TAC [ARITH_ss] [wordsTheory.WORD_LEFT_ADD_DISTRIB,
         EQT_ELIM (wordsLib.WORD_ARITH_CONV
           ``(a + b = b + c) = (a = c : 'a word)``)]
    \\ Cases_on `w` \\ Cases_on `m`
    \\ SRW_TAC [fcpLib.FCP_ss, ARITH_ss]
          [word_mul_n2w, word_slice_n2w, word_index, word_lsl_n2w, MIN_DEF]
    THENL [ALL_TAC,
      `dimindex(:'a) - 1 = n` by SRW_TAC [ARITH_ss] []
      \\ FULL_SIMP_TAC std_ss []
    ]
    \\ Cases_on `BIT n n'`
    \\ FULL_SIMP_TAC (srw_ss())
         [bitTheory.SLICE_ZERO2, bitTheory.BIT_SLICE_THM2,
          bitTheory.BIT_SLICE_THM3]
  ]);

val BITWISE_MUL_lem2 = Q.prove(
  `!w m : 'a word.
     w * m =
     FOLDL (\a j. a + FCP i. w ' j /\ (m << j) ' i) 0w
           (COUNT_LIST (dimindex(:'a)))`,
  SRW_TAC [wordsLib.WORD_EXTRACT_ss] [BITWISE_MUL_lem]
  \\ SRW_TAC [] [GSYM wordsTheory.WORD_w2w_EXTRACT, w2w_id]);

val BITWISE_MUL = Q.store_thm("BITWISE_MUL",
  `!w m : 'a word.
     w * m =
     FOLDL (\a j. a + FCP i. w ' j /\ j <= i /\ m ' (i - j)) 0w
           (COUNT_LIST (dimindex(:'a)))`,
  SRW_TAC [] [BITWISE_MUL_lem2]
  \\ MATCH_MP_TAC listTheory.FOLDL_CONG
  \\ SRW_TAC [] [FUN_EQ_THM, rich_listTheory.MEM_COUNT_LIST]
  \\ SRW_TAC [fcpLib.FCP_ss] [word_lsl_def]);

(* ------------------------------------------------------------------------ *)

val word_bv_fold_zero = Q.prove(
  `!P n f.
     (!j. j < n ==> ~P j) ==>
     (FOLDL (\a j. a \/ P j /\ f j) F (COUNT_LIST n) = F)`,
  Induct_on `n`
  \\ SRW_TAC [] [rich_listTheory.COUNT_LIST_SNOC, listTheory.FOLDL_SNOC]
  \\ `!j. j < n ==> ~P j` by SRW_TAC [ARITH_ss] []
  \\ METIS_TAC []
);

fun DROPN_TAC n = NTAC n (POP_ASSUM (K ALL_TAC));

val word_bv_lem = Q.prove(
  `!f P i n.
     i < n /\ P i /\
     (!i j. P i /\ P j /\ i < n /\ j < n ==> (i = j)) ==>
     (FOLDL (\a j. a \/ P j /\ (f j)) F (COUNT_LIST n) = f i)`,
  Induct_on `n`
  \\ SRW_TAC [] [rich_listTheory.COUNT_LIST_SNOC, listTheory.FOLDL_SNOC]
  \\ `!i j. P i /\ P j /\ i < n /\ j < n ==> (i = j)` by SRW_TAC [ARITH_ss] []
  \\ Cases_on `i < n`
  THENL [
    `(FOLDL (\a j. a \/ P j /\ f j) F (COUNT_LIST n) <=> f i)` by METIS_TAC []
    \\ ASM_SIMP_TAC std_ss []
    \\ Q.PAT_ASSUM `!i j. P i /\ P j /\ i < SUC n /\ j < SUC n ==> x`
          (Q.SPECL_THEN [`n`,`i`] (IMP_RES_TAC o SIMP_RULE arith_ss []))
    \\ METIS_TAC [],
    `i = n` by DECIDE_TAC
    \\ FULL_SIMP_TAC arith_ss []
    \\ `!j. j < n ==> ~P j`
    by (REPEAT STRIP_TAC
        \\ `j < SUC n` by DECIDE_TAC
        \\ Q.PAT_ASSUM `!i j. P i /\ P j /\ i < SUC n /\ j < SUC n ==> x`
             (Q.SPECL_THEN [`j`,`n`] (IMP_RES_TAC o SIMP_RULE arith_ss []))
        \\ `j <> n` by DECIDE_TAC
        \\ METIS_TAC [])
    \\ ASM_SIMP_TAC std_ss [word_bv_fold_zero]
  ]);

(* ------------------------------------------------------------------------ *)

val lem = Q.prove(
  `!h w P a:'a word.
     (((dimindex(:'a) - 1) -- h + 1) w = 0w) ==>
     (((h -- 0) a = w) /\ (((dimindex(:'a) - 1) -- h + 1) a = 0w) = (a = w))`,
  STRIP_TAC
  \\ Cases_on `dimindex(:'a) - 1 < h + 1`
  \\ SRW_TAC [wordsLib.WORD_EXTRACT_ss, ARITH_ss] []
  \\ `h + 1 <= dimindex(:'a) - 1` by SRW_TAC [ARITH_ss] []
  \\ IMP_RES_TAC
       (wordsTheory.EXTRACT_JOIN_ADD
        |> Q.SPECL [`dimindex(:'a) - 1`, `h`, `h + 1`, `0`, `h + 1`, `a`]
        |> Thm.INST_TYPE [Type.beta |-> Type.alpha]
        |> SIMP_RULE std_ss [GSYM wordsTheory.WORD_w2w_EXTRACT, w2w_id]
        |> GSYM)
  \\ POP_ASSUM (Q.SPEC_THEN `a`
       (fn thm => CONV_TAC (RHS_CONV (LHS_CONV (REWR_CONV thm)))))
  \\ Cases_on `(dimindex (:'a) - 1 >< h + 1) a = 0w : 'a word`
  \\ SRW_TAC [] []
  \\ SRW_TAC [wordsLib.WORD_EXTRACT_ss] []
  \\ FULL_SIMP_TAC (srw_ss()++wordsLib.WORD_BIT_EQ_ss) []
  \\ Q.EXISTS_TAC `h + (i + 1)`
  \\ SRW_TAC [ARITH_ss] []
  \\ METIS_TAC []);

val lem2 = Q.prove(
  `!l i p b.
      (FOLDL (\a j. a \/ p j) i l /\ b =
       FOLDL (\a j. a \/ b /\ p j) (i /\ b) l)`,
  Induct \\ SRW_TAC [] [listTheory.FOLDL,
    DECIDE ``((i \/ p h) /\ b = i /\ b \/ b /\ p h)``]);

val FOLDL_LOG2_INTRO = Q.prove(
  `!P n m:'a word.
     1 < n /\ n <= dimindex (:'a) ==>
       (FOLDL (\a j. a \/ (m = n2w j) /\ P j) F (COUNT_LIST n) =
        FOLDL (\a j. a \/ ((LOG2 (n - 1) -- 0) m = n2w j) /\ P j) F
              (COUNT_LIST n) /\
        ((dimindex(:'a) - 1 -- LOG2 (n - 1) + 1) m = 0w))`,
  SRW_TAC [] [lem2]
  \\ MATCH_MP_TAC listTheory.FOLDL_CONG
  \\ SRW_TAC [] [FUN_EQ_THM, rich_listTheory.MEM_COUNT_LIST]
  \\ Cases_on `P x` \\ Cases_on `a` \\ SRW_TAC [] []
  \\ `x <= n - 1` by DECIDE_TAC
  \\ `0 < n - 1` by DECIDE_TAC
  \\ IMP_RES_TAC (logrootTheory.LOG |> Q.SPEC `2` |> SIMP_RULE std_ss [])
  \\ `x < 2 ** (LOG2 (n - 1) + 1)`
  by METIS_TAC [LOG2_def, ADD1, arithmeticTheory.LESS_EQ_LESS_TRANS]
  \\ `((dimindex(:'a) - 1) -- LOG2 (n - 1) + 1) (n2w x) = 0w : 'a word`
  by SRW_TAC [] [word_bits_n2w, bitTheory.BITS_LT_LOW]
  \\ METIS_TAC [lem]);

(* ------------------------------------------------------------------------ *)

val word_lsl_bv_expand = Q.prove(
  `!w m. word_lsl_bv (w:'a word) m =
         FCP k.
           FOLDL (\a j. a \/ (m = n2w j) /\ ((j <= k) /\ w ' (k - j))) F
                 (COUNT_LIST (dimindex(:'a)))`,
  Cases_on `m`
  \\ SRW_TAC [fcpLib.FCP_ss] [word_lsl_bv_def, word_lsl_def]
  \\ Q.ABBREV_TAC `P = (\j. n = j MOD dimword(:'a))`
  \\ Cases_on `n < dimindex (:'a)`
  THENL [
    `P n` by SRW_TAC [] [Abbr `P`]
    \\ `!i j. P i /\ P j /\ i < dimindex(:'a) /\ j < dimindex(:'a) ==> (i = j)`
    by (SRW_TAC [] [Abbr `P`] \\ FULL_SIMP_TAC arith_ss [dimindex_lt_dimword])
    \\ Q.SPECL_THEN [`\j. j <= i /\ w ' (i - j)`, `P`, `n`, `dimindex(:'a)`]
          IMP_RES_TAC word_bv_lem
    \\ DROPN_TAC 17
    \\ FULL_SIMP_TAC std_ss [Abbr `P`],
    `!j. j < n ==> ~P j` by SRW_TAC [ARITH_ss] [Abbr `P`]
    \\ ASM_SIMP_TAC arith_ss [word_0, word_bv_fold_zero]
  ]);

val word_lsl_bv_expand = Q.store_thm("word_lsl_bv_expand",
  `!w m.
      word_lsl_bv (w:'a word) m =
        if dimindex(:'a) = 1 then
          $FCP (K (~m ' 0 /\ w ' 0))
        else
          FCP k.
             FOLDL (\a j. a \/ ((LOG2 (dimindex(:'a) - 1) -- 0) m = n2w j) /\
                          ((j <= k) /\ w ' (k - j))) F
                   (COUNT_LIST (dimindex(:'a))) /\
             ((dimindex(:'a) - 1 -- LOG2 (dimindex(:'a) - 1) + 1) m = 0w)`,
  SRW_TAC [] [word_lsl_bv_expand]
  THEN1 SRW_TAC [wordsLib.WORD_BIT_EQ_ss] [rich_listTheory.COUNT_LIST_compute]
  \\ `1 < dimindex(:'a)` by SRW_TAC [] [DECIDE ``0n < n /\ n <> 1 ==> 1 < n``]
  \\ ONCE_REWRITE_TAC [fcpTheory.CART_EQ]
  \\ SRW_TAC [] [fcpTheory.FCP_BETA]
  \\ METIS_TAC [arithmeticTheory.LESS_EQ_REFL, FOLDL_LOG2_INTRO]);

val word_lsr_bv_expand = Q.prove(
  `!w m. word_lsr_bv (w:'a word) m =
         FCP k.
           FOLDL (\a j. a \/ (m = n2w j) /\ k + j < dimindex(:'a) /\
                        w ' (k + j)) F
                 (COUNT_LIST (dimindex(:'a)))`,
  Cases_on `m`
  \\ SRW_TAC [fcpLib.FCP_ss] [word_lsr_bv_def, word_lsr_def]
  \\ Q.ABBREV_TAC `P = (\j. n = j MOD dimword(:'a))`
  \\ Cases_on `n < dimindex (:'a)`
  THENL [
    `P n` by SRW_TAC [] [Abbr `P`]
    \\ `!i j. P i /\ P j /\ i < dimindex(:'a) /\ j < dimindex(:'a) ==> (i = j)`
    by (SRW_TAC [] [Abbr `P`] \\ FULL_SIMP_TAC arith_ss [dimindex_lt_dimword])
    \\ Q.SPECL_THEN [`\j. i + j < dimindex(:'a) /\ w ' (i + j)`, `P`, `n`,
                     `dimindex(:'a)`] IMP_RES_TAC word_bv_lem
    \\ DROPN_TAC 17
    \\ FULL_SIMP_TAC std_ss [Abbr `P`],
    `!j. j < n ==> ~P j` by SRW_TAC [ARITH_ss] [Abbr `P`]
    \\ ASM_SIMP_TAC arith_ss [word_bv_fold_zero]
  ]);

val word_lsr_bv_expand = Q.store_thm("word_lsr_bv_expand",
  `!w m.
      word_lsr_bv (w:'a word) m =
        if dimindex(:'a) = 1 then
          $FCP (K (~m ' 0 /\ w ' 0))
        else
          FCP k.
            FOLDL (\a j. a \/ ((LOG2 (dimindex(:'a) - 1) -- 0) m = n2w j) /\
                         k + j < dimindex(:'a) /\ w ' (k + j)) F
                  (COUNT_LIST (dimindex(:'a))) /\
            ((dimindex(:'a) - 1 -- LOG2 (dimindex(:'a) - 1) + 1) m = 0w)`,
  SRW_TAC [] [word_lsr_bv_expand]
  THEN1 SRW_TAC [wordsLib.WORD_BIT_EQ_ss] [rich_listTheory.COUNT_LIST_compute]
  \\ `1 < dimindex(:'a)` by SRW_TAC [] [DECIDE ``0n < n /\ n <> 1 ==> 1 < n``]
  \\ ONCE_REWRITE_TAC [fcpTheory.CART_EQ]
  \\ SRW_TAC [] [fcpTheory.FCP_BETA]
  \\ METIS_TAC [arithmeticTheory.LESS_EQ_REFL, FOLDL_LOG2_INTRO]);

val word_asr_bv_expand = Q.prove(
  `!w m. word_asr_bv (w:'a word) m =
         (FCP k.
           FOLDL (\a j. a \/ (m = n2w j) /\ (w >> j) ' k) F
                 (COUNT_LIST (dimindex(:'a)))) !!
         ($FCP (K (n2w (dimindex(:'a) - 1) <+ m /\ word_msb w)))`,
  `dimindex(:'a) - 1 < dimword(:'a)` by SRW_TAC [ARITH_ss] [dimindex_lt_dimword]
  \\ Cases_on `m`
  \\ SRW_TAC [fcpLib.FCP_ss, ARITH_ss]
       [word_asr_bv_def, word_or_def, word_lo_n2w, dimindex_lt_dimword]
  \\ Q.ABBREV_TAC `P = (\i. n = i MOD dimword(:'a))`
  \\ Cases_on `n < dimindex (:'a)`
  THENL [
    `P n` by SRW_TAC [] [Abbr `P`]
    \\ `!i j. P i /\ P j /\ i < dimindex(:'a) /\ j < dimindex(:'a) ==> (i = j)`
    by (SRW_TAC [] [Abbr `P`] \\ FULL_SIMP_TAC arith_ss [dimindex_lt_dimword])
    \\ Q.SPECL_THEN [`\j. (w >> j) ' i`, `P`, `n`, `dimindex(:'a)`]
         IMP_RES_TAC word_bv_lem
    \\ DROPN_TAC 17
    \\ FULL_SIMP_TAC arith_ss [Abbr `P`],
    `!j. j < n ==> ~P j` by SRW_TAC [ARITH_ss] [Abbr `P`]
    \\ ASM_SIMP_TAC arith_ss [ASR_LIMIT, word_bv_fold_zero]
    \\ SRW_TAC [] [SIMP_RULE (srw_ss()) [] word_T, word_0]
  ]);

val fcp_or = Q.prove(
  `!b g. $FCP f !! $FCP g = $FCP (\i. f i \/ g i)`,
  SRW_TAC [fcpLib.FCP_ss] [word_or_def]);

val word_asr_bv_expand = Q.prove(
  `!w m.
      word_asr_bv (w:'a word) m =
        if dimindex(:'a) = 1 then
          $FCP (K (w ' 0))
        else
          (FCP k.
             FOLDL (\a j. a \/ ((LOG2 (dimindex(:'a) - 1) -- 0) m = n2w j) /\
                          (w >> j) ' k) F (COUNT_LIST (dimindex(:'a))) /\
             ((dimindex(:'a) - 1 -- LOG2 (dimindex(:'a) - 1) + 1) m = 0w)) !!
           ($FCP (K (n2w (dimindex(:'a) - 1) <+ m /\ word_msb w)))`,
  SRW_TAC [] [word_asr_bv_expand, fcp_or]
  THENL [
    Cases_on `m`
    \\ `(n = 0) \/ (n = 1)`
    by Q.PAT_ASSUM `x = 1` (fn th => FULL_SIMP_TAC arith_ss [dimword_def,th])
    \\ SRW_TAC [wordsLib.WORD_BIT_EQ_ss]
         [wordsTheory.word_lo_n2w, rich_listTheory.COUNT_LIST_compute],
    `1 < dimindex(:'a)` by SRW_TAC [] [DECIDE ``0n < n /\ n <> 1 ==> 1 < n``]
    \\ ONCE_REWRITE_TAC [fcpTheory.CART_EQ]
    \\ SRW_TAC [] [fcpTheory.FCP_BETA]
    \\ METIS_TAC [arithmeticTheory.LESS_EQ_REFL, FOLDL_LOG2_INTRO]
  ]);

val word_asr_bv_expand = Theory.save_thm("word_asr_bv_expand",
  SIMP_RULE std_ss [fcp_or, word_msb_def] word_asr_bv_expand);

val word_ror_bv_expand = Q.store_thm("word_ror_bv_expand",
  `!w m.
     word_ror_bv (w:'a word) m =
     FCP k.
       FOLDL (\a j. a \/ (word_mod m (n2w (dimindex(:'a))) = n2w j) /\
              w ' ((j + k) MOD dimindex(:'a))) F (COUNT_LIST (dimindex(:'a)))`,
  Cases_on `m`
  \\ SRW_TAC [ARITH_ss] [word_mod_def, mod_dimindex, dimindex_lt_dimword]
  \\ SRW_TAC [fcpLib.FCP_ss] [word_ror_bv_def, word_ror_def]
  \\ Q.ABBREV_TAC `P = (\j. n MOD dimindex(:'a) = j MOD dimword(:'a))`
  \\ `P (n MOD dimindex(:'a))` by SRW_TAC [] [Abbr `P`, mod_dimindex]
  \\ `!i j. P i /\ P j /\ i < dimindex(:'a) /\ j < dimindex(:'a) ==> (i = j)`
  by (SRW_TAC [] [Abbr `P`] \\ FULL_SIMP_TAC arith_ss [dimindex_lt_dimword])
  \\ `n MOD dimindex(:'a) < dimindex(:'a)`
  by SRW_TAC [] [DIMINDEX_GT_0, arithmeticTheory.MOD_LESS]
  \\ Q.SPECL_THEN [`\j. w ' ((j + i) MOD dimindex(:'a))`, `P`,
                   `n MOD dimindex (:'a)`, `dimindex(:'a)`]
                   IMP_RES_TAC word_bv_lem
  \\ DROPN_TAC 2
  \\ FULL_SIMP_TAC std_ss [Abbr `P`, AC ADD_COMM ADD_ASSOC,
       MOD_PLUS_RIGHT, DIMINDEX_GT_0]
  );

val word_rol_bv_expand = Q.store_thm("word_rol_bv_expand",
  `!w m.
     word_rol_bv (w:'a word) m =
     FCP k.
       FOLDL
         (\a j. a \/ (word_mod m (n2w (dimindex(:'a))) = n2w j) /\
           w ' ((k + (dimindex(:'a) - j) MOD dimindex(:'a)) MOD dimindex(:'a)))
           F (COUNT_LIST (dimindex(:'a)))`,
  Cases_on `m`
  \\ SRW_TAC [ARITH_ss] [word_mod_def, mod_dimindex, dimindex_lt_dimword]
  \\ SRW_TAC [fcpLib.FCP_ss] [word_rol_bv_def, word_rol_def, word_ror_def]
  \\ Q.ABBREV_TAC `P = (\j. n MOD dimindex(:'a) = j MOD dimword(:'a))`
  \\ `P (n MOD dimindex(:'a))` by SRW_TAC [] [Abbr `P`, mod_dimindex]
  \\ `!i j. P i /\ P j /\ i < dimindex(:'a) /\ j < dimindex(:'a) ==> (i = j)`
  by (SRW_TAC [] [Abbr `P`] \\ FULL_SIMP_TAC arith_ss [dimindex_lt_dimword])
  \\ `n MOD dimindex(:'a) < dimindex(:'a)`
  by SRW_TAC [] [DIMINDEX_GT_0, arithmeticTheory.MOD_LESS]
  \\ Q.SPECL_THEN
       [`\j. w ' ((i + (dimindex (:'a) - j) MOD dimindex (:'a))
               MOD dimindex (:'a))`, `P`, `n MOD dimindex (:'a)`,
               `dimindex(:'a)`] IMP_RES_TAC word_bv_lem
  \\ DROPN_TAC 2
  \\ FULL_SIMP_TAC std_ss [Abbr `P`, MOD_PLUS_RIGHT, DIMINDEX_GT_0]
  );

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
