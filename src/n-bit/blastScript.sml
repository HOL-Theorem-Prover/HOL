(* ========================================================================= *)
(* FILE          : blastScript.sml                                           *)
(* DESCRIPTION   : A bitwise treatment of n-bit addition.                    *)
(* AUTHOR        : Anthony Fox, University of Cambridge                      *)
(* DATE          : 2010                                                      *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory bitTheory wordsTheory;

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
  \\ `!i. i < n ==> (x1 i = x2 i) ∧ (y1 i = y2 i)`
  by ASM_SIMP_TAC arith_ss []
  \\ RES_TAC \\ ASM_REWRITE_TAC []);

val BSUM_EQ = Q.store_thm("BSUM_EQ",
  `!n c x1 x2 y1 y2.
     (!i. i <= n ==> (x1 i = x2 i) /\ (y1 i = y2 i)) ==>
     (BSUM n x1 y1 c = BSUM n x2 y2 c)`,
  SRW_TAC [] [BSUM_def]
  \\ `!i. i < n ==> (x1 i = x2 i) ∧ (y1 i = y2 i)`
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

(* ------------------------------------------------------------------------ *)

val _ = export_theory();
