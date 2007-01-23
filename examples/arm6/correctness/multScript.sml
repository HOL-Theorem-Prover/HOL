(* ========================================================================= *)
(* FILE          : multScript.sml                                            *)
(* DESCRIPTION   : A collection of lemmas used to verify the multiply        *)
(*                 instructions                                              *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2003 - 2005                                               *)
(* ========================================================================= *)

(* interactive use:
  app load ["pred_setSimps", "wordsLib", "armLib", "iclass_compLib",
            "armTheory", "coreTheory", "lemmasTheory", "interruptsTheory"];
*)

open HolKernel boolLib bossLib;
open Q arithmeticTheory whileTheory bitTheory wordsTheory wordsLib;
open iclass_compLib io_onestepTheory;
open armTheory coreTheory lemmasTheory interruptsTheory;

val _ = new_theory "mult";

(* ------------------------------------------------------------------------- *)

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val Abbr = BasicProvers.Abbr;

val std_ss = std_ss ++ boolSimps.LET_ss;
val arith_ss = arith_ss ++ boolSimps.LET_ss;

val fcp_ss   = armLib.fcp_ss;

val WL = ``dimindex (:'a)``;

val tt = set_trace "types";

val FST_COND_RAND = ISPEC `FST` COND_RAND;
val SND_COND_RAND = ISPEC `SND` COND_RAND;

(* ------------------------------------------------------------------------- *)

val MULT_ALU6_ZERO = store_thm("MULT_ALU6_ZERO",
  `!ireg borrow2 mul dataabt alua alub c.
     SND (ALU6 mla_mul t3 ireg borrow2 mul dataabt alua alub c) =
       if ireg %% 21 then alub else 0w`,
  RW_TAC std_ss [ALUOUT_ALU_logic,ALU6_def]);

val COMM_MULT_DIV = ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV;
val COMM_DIV_MULT = ONCE_REWRITE_RULE [MULT_COMM] DIV_MULT;

val COMP_VAL_BIT2 = prove(
  `!a b c d. (~(\(w,a). w /\ (a = 15))
     if (c = 15) \/ (c = d) then (F,b) else (T,c))`,
  RW_TAC std_ss [] \\ FULL_SIMP_TAC bool_ss []);

val MIN_LEM = prove(
  `!x t. 0 < t ==> (MIN 31 (2 * t + 29) = 31)`,
  RW_TAC arith_ss [MIN_DEF]);

val BORROW2 = prove(
  `!n rs. 2 * n <= 32 ==>
      (BORROW2 rs n =
       ~(n = 0) /\ (((2 * (n - 1) + 1) >< (2 * (n - 1))) rs):word2 %% 1)`,
  STRIP_TAC \\ Cases_on `n = 0` \\
    RW_TAC (fcp_ss++ARITH_ss++SIZES_ss) [MIN_DEF,LEFT_SUB_DISTRIB,BORROW2_def,
      w2w,word_extract_def,word_bits_def]);

val MULX_DONE_def = prove(
  `!n rs.  2 * (SUC n) <= 32 ==>
     (MULX mla_mul tn (MULZ mla_mul tn ((31 -- (2 * SUC n)) rs))
        (BORROW2 rs (SUC n))
        (MSHIFT mla_mul (BORROW2 rs n)
           ((1 >< 0) ((31 -- (2 * n)) rs)) (n2w n)) =
      MLA_MUL_DONE rs (SUC n))`,
  STRIP_TAC \\ Cases_word
    \\ RW_TAC (arith_ss++SIZES_ss) [MULX_def,MULZ_def,MSHIFT,MLA_MUL_DONE_def,
         MIN_LEM,BITS_COMP_THM2,NOT_LESS,word_bits_n2w,word_extract_def]
    \\ FULL_SIMP_TAC (arith_ss++SIZES_ss)
         [w2w_def,w2n_n2w,word_mul_n2w,word_add_n2w,word_bits_n2w,n2w_11,
          BITS_THM,COMM_DIV_MULT,COMM_MULT_DIV,
          DECIDE ``!a b c. (a \/ b = a \/ c) = (~a ==> (b = c))``]);

val word_extract = (GSYM o SIMP_RULE std_ss [] o
  REWRITE_RULE [FUN_EQ_THM]) word_extract_def;

val MULX_DONE_ZERO =
  (SIMP_RULE std_ss [word_extract,GSYM w2w_def] o
   SIMP_RULE (arith_ss++SIZES_ss) [w2w_def,word_extract_def,n2w_w2n,w2n_n2w,
     WORD_ADD_0,WORD_MULT_CLAUSES,MSHIFT,BORROW2,WORD_BITS_COMP_THM] o
   SPEC `0`) MULX_DONE_def;

(* ------------------------------------------------------------------------- *)

val EXISTS_DONE = prove(
  `!rs. ?n. MLA_MUL_DONE rs n`,
  RW_TAC bool_ss [MLA_MUL_DONE_def]
    \\ EXISTS_TAC `16` \\ SIMP_TAC arith_ss []);

val lem = (SIMP_RULE bool_ss [EXISTS_DONE] o
  SPECL [`\x. 2 * x <= WL`,`MLA_MUL_DONE rs`]) LEAST_ELIM;

val SPEC_LESS_MULT_MONO =
  (GEN_ALL o numLib.REDUCE_RULE o INST [`n` |-> `1`] o
   SPEC_ALL) LESS_MULT_MONO;

val DIV_TWO_MONO_EVEN = prove(
  `!a b. a < 2 * b = a DIV 2 < b`,
  REPEAT STRIP_TAC
    \\ Cases_on `EVEN a`
    >> (IMP_RES_TAC EVEN_EXISTS \\
          ASM_SIMP_TAC arith_ss [COMM_MULT_DIV,SPEC_LESS_MULT_MONO])
    \\ RULE_ASSUM_TAC (REWRITE_RULE [GSYM ODD_EVEN])
    \\ IMP_RES_TAC ODD_EXISTS
    \\ ASM_SIMP_TAC arith_ss [ADD1,COMM_DIV_MULT,SPEC_LESS_MULT_MONO]);

val DONE_LESS_EQUAL_WL = prove(
  `!n. (!m. m < n ==> ~MLA_MUL_DONE rs m) /\
        MLA_MUL_DONE rs n ==> 2 * n <= 32`,
  RW_TAC bool_ss [MLA_MUL_DONE_def,NOT_LESS]
    << [
       FULL_SIMP_TAC arith_ss [BORROW2_def]
         \\ SPOSE_NOT_THEN STRIP_ASSUME_TAC
         \\ RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS_EQUAL])
         \\ IMP_RES_TAC DIV_TWO_MONO_EVEN
         \\ PAT_ASSUM `!m. m < n ==> P` IMP_RES_TAC
         \\ FULL_SIMP_TAC arith_ss [],
       Cases_on `2 * n = 32` >> ASM_SIMP_TAC arith_ss []
         \\ `32 < 2 * n` by DECIDE_TAC
         \\ IMP_RES_TAC DIV_TWO_MONO_EVEN
         \\ PAT_ASSUM `!m. m < n ==> P` IMP_RES_TAC
         \\ FULL_SIMP_TAC arith_ss []]);

val DUR_LT_EQ_HWL = prove(
  `!rs. 2 * (MLA_MUL_DUR rs) <= 32`,
  REWRITE_TAC [MLA_MUL_DUR_def] \\ CONV_TAC (DEPTH_CONV ETA_CONV)
    \\ PROVE_TAC [DONE_LESS_EQUAL_WL,lem]);

(* ------------------------------------------------------------------------- *)

val lem = (SIMP_RULE arith_ss [EXISTS_DONE,MLA_MUL_DONE_def] o
           SPECL [`\x. ~(x = 0)`,`MLA_MUL_DONE rs`]) LEAST_ELIM;

val DUR_NEQ_ZERO = prove(
  `!rs. ~(MLA_MUL_DUR rs = 0)`,
  REWRITE_TAC [MLA_MUL_DUR_def] \\ CONV_TAC (DEPTH_CONV ETA_CONV)
    \\ PROVE_TAC [lem]);

(* ------------------------------------------------------------------------- *)

val DONE_DUR = prove(
  `!rs. MLA_MUL_DONE rs (MLA_MUL_DUR rs)`,
  REWRITE_TAC [MLA_MUL_DUR_def]
    \\ CONV_TAC (DEPTH_CONV ETA_CONV)
    \\ PROVE_TAC [LEAST_EXISTS_IMP,EXISTS_DONE]);

val NOT_DONE_SUC = prove(
  `!rs n. SUC n <= MLA_MUL_DUR rs ==> ~MLA_MUL_DONE rs n`,
  RW_TAC bool_ss [MLA_MUL_DUR_def]
    \\ RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV))
    \\ ASM_SIMP_TAC arith_ss [LESS_LEAST]);

(* ------------------------------------------------------------------------- *)

val MIN_LEM = prove(
  `!x t. 0 < t ==> (MIN x (x - 2 + 2 * t) = x)`,
  RW_TAC arith_ss [MIN_DEF]);

val BITS_X_SUB2 = prove(
  `!n x rs. ~(n = 0) ==>
     (((x - 2) -- 0) ((x -- (2 * n)) rs) = (x -- (2 * n)) rs)`,
  SIMP_TAC arith_ss [WORD_BITS_COMP_THM,MIN_LEM]);

val SPEC_MULT_LESS_EQ_SUC =
  (GEN_ALL o REWRITE_RULE [SYM TWO] o INST [`p` |-> `1`] o
   SPEC_ALL) MULT_LESS_EQ_SUC;

val LEQ_MLA_MUL_DUR = prove(
  `!n rs. n <= MLA_MUL_DUR rs ==> 2 * n <= 32`,
  REPEAT STRIP_TAC
    \\ RULE_ASSUM_TAC (ONCE_REWRITE_RULE [SPEC_MULT_LESS_EQ_SUC])
    \\ PROVE_TAC [LESS_EQ_TRANS,DUR_LT_EQ_HWL]);

val MUL1 = prove(
  `!rs n. SUC n <= MLA_MUL_DUR rs ==>
     ((1 >< 0) ((31 -- (2 * n)) rs):word2 = ((2 * n + 1) >< (2 * n)) rs)`,
  RW_TAC arith_ss [ADD1,WORD_BITS_COMP_THM,MIN_DEF,word_extract_def]
    \\ IMP_RES_TAC LEQ_MLA_MUL_DUR
    \\ FULL_SIMP_TAC arith_ss []);

val MUL1_SUC = prove(
  `!n x. (x -- 2) ((x -- (2 * (n + 1))) rs) =
         (x -- (2 * (n + 2))) rs`,
  SIMP_TAC arith_ss [WORD_BITS_COMP_THM,MIN_DEF,LEFT_ADD_DISTRIB]);

val COUNT1 = prove(
  `!n b. (n * 2 + (if b then 1 else 0)) DIV 2 = n`,
  RW_TAC arith_ss [COMM_MULT_DIV,COMM_DIV_MULT]);

val BITS_X_SUB2_1 = (SIMP_RULE arith_ss [] o SPEC `1`) BITS_X_SUB2;
val MUL1_SUC_1 = (SIMP_RULE arith_ss [] o SPEC `0`) MUL1_SUC;
val COUNT1_ZERO = (SIMP_RULE arith_ss [] o SPEC `0`) COUNT1;

val SPEC_MULX_DONE =
  (GEN_ALL o SIMP_RULE bool_ss [] o DISCH `~(n = 0)` o
   CONV_RULE (RAND_CONV (REWRITE_CONV [ADD1])) o
   SIMP_RULE arith_ss [MUL1,MSHIFT,AND_IMP_INTRO,
     MATCH_MP (DECIDE ``!a b. (a ==> b) ==> (a /\ b = a)``)
              (SPECL [`SUC n`,`rs`] LEQ_MLA_MUL_DUR)] o
   DISCH `SUC n <= MLA_MUL_DUR rs` o
   SIMP_RULE arith_ss [SPEC `SUC n` BORROW2] o  SPEC_ALL) MULX_DONE_def;

val DONE_NEQ_ZERO = prove(
  `!rs. ~MLA_MUL_DONE rs 0`,
  SIMP_TAC arith_ss [MLA_MUL_DONE_def]);

(* ------------------------------------------------------------------------- *)

val LESS_THM =
  CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV prim_recTheory.LESS_THM;

val word2_VALUES = prove(
  `!w:word2. (w = 0w) \/ (w = 1w) \/ (w = 2w) \/ (w = 3w)`,
  STRIP_TAC \\ ISPEC_THEN `w` ASSUME_TAC w2n_lt
    \\ FULL_SIMP_TAC (arith_ss++SIZES_ss) [GSYM w2n_11,w2n_n2w,LESS_THM]);

val word2_bits = map (fn i => CONJ (EVAL ``BIT 0 ^i``) (EVAL ``BIT 1 ^i``))
  [``0``,``1``,``2``,``3``];

val word2_BITS = prove(
  `(!w:word2. (w = 0w) = ~(w %% 1) /\ ~(w %% 0)) /\
   (!w:word2. (w = 1w) = ~(w %% 1) /\  (w %% 0)) /\
   (!w:word2. (w = 2w) =  (w %% 1) /\ ~(w %% 0)) /\
    !w:word2. (w = 3w) =  (w %% 1) /\  (w %% 0)`,
  REPEAT STRIP_TAC \\ Cases_on_word `w`
    \\ SIMP_TAC (fcp_ss++ARITH_ss++SIZES_ss) [LESS_THM,n2w_def]
    \\ PROVE_TAC word2_bits);

val BIT_VAR = prove(
  `!w:word2. ~(w = 0w) /\ ~(w = 1w) ==> w %% 1`,
  METIS_TAC [word2_VALUES,word2_BITS]);

(* ------------------------------------------------------------------------- *)

val CARRY_LEM = store_thm("CARRY_LEM",
  `!cpsr. NZCV cpsr = FST (DECODE_PSR cpsr)`,
  SIMP_TAC std_ss [DECODE_PSR_def]);

val LSL_CARRY_SUBST = prove(
  `!n C x c. ~(n = 0w) ==> (LSL x n c = LSL x n C)`,
  SIMP_TAC std_ss [LSL_def]);

(* ------------------------------------------------------------------------- *)

val lem = (SIMP_RULE bool_ss [EXISTS_DONE] o
  SPECL [`\x. 2 * x < 32 ==> ~(BORROW2 rs x)`,`MLA_MUL_DONE rs`]) LEAST_ELIM;

val DONE_EARLY_NOT_BORROW = prove(
  `!n. (!m. m < n ==> ~MLA_MUL_DONE rs m) /\ MLA_MUL_DONE rs n ==>
          2 * n < 32 ==>
          ~BORROW2 rs n`,
  RW_TAC arith_ss [MLA_MUL_DONE_def,BORROW2_def]
    \\ FULL_SIMP_TAC bool_ss []);

val DONE_EARLY_NOT_BORROW2 = prove(
  `!rs. 2 * (MLA_MUL_DUR rs) < 32 ==> ~BORROW2 rs (MLA_MUL_DUR rs)`,
  REWRITE_TAC [MLA_MUL_DUR_def]
    \\ CONV_TAC (DEPTH_CONV ETA_CONV)
    \\ PROVE_TAC [MATCH_MP lem DONE_EARLY_NOT_BORROW]);

val BORROW_IMP_WL = prove(
  `!rs. BORROW2 rs (MLA_MUL_DUR rs) ==> (2 * (MLA_MUL_DUR rs) = 32)`,
  REPEAT STRIP_TAC
    \\ Cases_on `2 * (MLA_MUL_DUR rs) < 32`
    >> IMP_RES_TAC DONE_EARLY_NOT_BORROW2
    \\ ASSUME_TAC (SPEC `rs` DUR_LT_EQ_HWL)
    \\ DECIDE_TAC);

val lem = (SIMP_RULE bool_ss [EXISTS_DONE] o
  SPECL [`\x. w2n rs MOD 2 ** (2 * x) = w2n rs`,`MLA_MUL_DONE rs`]) LEAST_ELIM;

val DONE_IMP_ZERO_MSBS = prove(
  `!n. (!m. m < n ==> ~MLA_MUL_DONE rs m) /\ MLA_MUL_DONE rs n ==>
        (w2n rs MOD 2 ** (2 * n) = w2n rs)`,
  Cases_on_word `rs`
    \\ STRIP_ASSUME_TAC (Thm.INST_TYPE [alpha |-> ``:32``] EXISTS_HB)
    \\ `Abbrev (m = 31)`
    by FULL_SIMP_TAC (arith_ss++SIZES_ss) [markerTheory.Abbrev_def]
    \\ RW_TAC bool_ss [dimword_def,SUC_SUB1,w2n_n2w,MLA_MUL_DONE_def]
    << [
      Cases_on `n'` >> FULL_SIMP_TAC arith_ss [ZERO_MOD]
        \\ FULL_SIMP_TAC bool_ss [GSYM BITS_ZERO3,
             DECIDE ``!n. 2 * SUC n = SUC (2 * n + 1)``]
        \\ RW_TAC arith_ss [BITS_COMP_THM2,MIN_DEF]
        \\ Cases_on `2 * n'' + 1 = 31`
        >> FULL_SIMP_TAC (std_ss++SIZES_ss) [Abbr`m`]
        \\ `2 * n'' + 2 <= 31`
        by FULL_SIMP_TAC (arith_ss++SIZES_ss) [NOT_LESS]
        \\ `SLICE 31 (SUC (2 * n'' + 1)) n = 0`
        by (PAT_ASSUM `q = 0w` MP_TAC \\
              ASM_SIMP_TAC arith_ss [dimword_def,GSYM BITS_ZERO3,SLICE_THM,MIN_DEF,
                BITS_COMP_THM2,ZERO_LT_TWOEXP,word_bits_n2w,n2w_11] \\
              SIMP_TAC arith_ss [Abbr`m`])
        \\ IMP_RES_TAC ((GSYM o SIMP_RULE arith_ss [ADD1,SLICE_ZERO_THM] o
                         SPECL [`31`,`2 * n'' + 1`,`0`]) SLICE_COMP_THM)
        \\ POP_ASSUM (ASSUME_TAC o SPEC `n`)
        \\ FULL_SIMP_TAC arith_ss [ADD1,Abbr`m`],
      FULL_SIMP_TAC bool_ss [NOT_LESS]
        \\ IMP_RES_TAC LESS_EQUAL_ADD
        \\ POP_ASSUM (fn th => `2 * n' = SUC (31 + p)`
        by SIMP_TAC arith_ss [th])
        \\ RW_TAC bool_ss [ADD_0,GSYM BITS_ZERO3,BITS_COMP_THM2,MIN_DEF]
        \\ `p = 0` by DECIDE_TAC
        \\ FULL_SIMP_TAC arith_ss [ADD1]]);

val DUR_IMP_ZERO_MSBS = prove(
  `!rs. w2n rs MOD 2 ** (2 * (MLA_MUL_DUR rs)) = w2n rs`,
  REWRITE_TAC [MLA_MUL_DUR_def]
    \\ CONV_TAC (DEPTH_CONV ETA_CONV)
    \\ PROVE_TAC [MATCH_MP lem DONE_IMP_ZERO_MSBS]);

val SPEC_LSL_LIMIT = (GEN_ALL o
  SIMP_RULE (std_ss++SIZES_ss) [] o SPECL [`a`,`32`] o
  Thm.INST_TYPE [alpha |-> ``:32``]) LSL_LIMIT;

val RD_INVARIANT_def = Define`
  RD_INVARIANT A (rm:word32) rs rn n =
    (if BORROW2 rs n then
       rm * n2w (w2n rs MOD 2 ** (2 * n)) - rm << (2 * n)
     else
       rm * n2w (w2n rs MOD 2 ** (2 * n))) +
    (if A then rn else 0w)`;

val BORROW2_LEM1 = prove(
  `!rs:word32. rs %% 1 = ((1 >< 0) rs):word2 %% 1`,
  Cases_word \\ SIMP_TAC (fcp_ss++SIZES_ss)
    [n2w_def,word_extract_def,word_bits_def,w2w]);

val MOD_4_BITS = prove(
  `!a:word32. w2n a MOD 4 = w2n ((1 -- 0) a)`,
  Cases_word
    \\ STRIP_ASSUME_TAC (Thm.INST_TYPE [alpha |-> ``:32``] EXISTS_HB)
    \\ ASM_SIMP_TAC bool_ss [dimword_def,GSYM BITS_ZERO3,BITS_COMP_THM2,
         (EQT_ELIM o EVAL) ``4 = 2 ** SUC 1``,word_bits_n2w,w2n_n2w]
    \\ FULL_SIMP_TAC (arith_ss++SIZES_ss) [MIN_DEF]);

val RD_INVARIANT_ZERO =
  (GEN_ALL o
   SIMP_RULE arith_ss [BORROW2_def,WORD_MULT_CLAUSES,WORD_ADD_0] o
   INST [`n` |-> `0`] o SPEC_ALL) RD_INVARIANT_def;

val RD_INVARIANT_ONE = (GEN_ALL o
   SIMP_RULE arith_ss [BORROW2_def,MOD_4_BITS,BORROW2_LEM1,
     n2w_w2n,GSYM word_bits_n2w] o
   INST [`n` |-> `1`] o SPEC_ALL) RD_INVARIANT_def;

val RD_INVARIANT_LAST = store_thm("RD_INVARIANT_LAST",
  `!a rm rs rn.
     RD_INVARIANT a rm rs rn (MLA_MUL_DUR rs) =
       rm * rs + (if a then rn else 0w)`,
   RW_TAC bool_ss [RD_INVARIANT_def,BORROW_IMP_WL,DUR_IMP_ZERO_MSBS,
     SPEC_LSL_LIMIT,n2w_w2n,WORD_ADD_0,WORD_SUB_RZERO]);

(* ------------------------------------------------------------------------- *)

val MUST_BE_TWO = PROVE [word2_VALUES]
  ``!w:word2. ~(w = 0w) /\ ~(w = 1w) /\ ~(w = 3w) ==> (w = 2w)``;

val MUST_BE_THREE = PROVE [word2_VALUES]
  ``!w:word2. ~(w = 0w) /\ ~(w = 1w) /\ ~(w = 2w) ==> (w = 3w)``;

(* ------------------------------------------------------------------------- *)

val SPEC_SLICE_COMP = prove(
  `!t a. ~(t = 0) ==>
         (a MOD 2 ** (2 * (t + 1)) =
          SLICE (2 * t + 1) (2 * t) a + a MOD 2 ** (2 * t))`,
  REPEAT STRIP_TAC
    \\ IMP_RES_TAC NOT_ZERO_ADD1
    \\ ASM_SIMP_TAC arith_ss [DECIDE ``!p. 2 * SUC p = SUC (2 * p + 1)``,
         GSYM BITS_ZERO3,GSYM SLICE_ZERO_THM,SLICE_COMP_RWT]
    \\ SIMP_TAC arith_ss [SLICE_ZERO_THM,BITS_ZERO3,ADD1,LEFT_ADD_DISTRIB]);

val SLICE_BITS_THM = prove(
  `!h m l n. SLICE h l (BITS m 0 n) = SLICE (MIN h m) l n`,
  RW_TAC arith_ss [SLICE_THM,BITS_COMP_THM2,MIN_DEF]
    \\ `h = m` by DECIDE_TAC \\ ASM_REWRITE_TAC []);
      
val MULT_MOD_SUC_T = prove(
  `!t (a:word32) (b:word32).
            a * n2w (w2n b MOD 2 ** (2 * (t + 1))) =
           (a * n2w (w2n b MOD 2 ** (2 * t))) +
           (a * w2w ((((2 * t + 1) >< (2 * t)) b):word2) << (2 * t))`,
  REPEAT STRIP_TAC
    \\ Cases_on `t = 0`
    >> ASM_SIMP_TAC (arith_ss++SIZES_ss) [WORD_MULT_CLAUSES,WORD_ADD_0,
         MOD_4_BITS,WORD_BITS_COMP_THM,WORD_SLICE_BITS_THM,SHIFT_ZERO,
         word_extract_def,n2w_w2n,w2w_w2w,w2w_id]
    \\ ASM_SIMP_TAC (arith_ss++SIZES_ss) [WORD_EQ_ADD_LCANCEL,SPEC_SLICE_COMP,
         word_extract_def,w2w_w2w,w2w_id,GSYM word_add_n2w,GSYM WORD_SLICE_THM,
         WORD_BITS_COMP_THM,WORD_LEFT_ADD_DISTRIB,WORD_ADD_COMM]
    \\ Cases_on_word `b` \\ POP_ASSUM (K ALL_TAC)
    \\ STRIP_ASSUME_TAC (Thm.INST_TYPE [alpha |-> ``:32``] EXISTS_HB)
    \\ ASM_SIMP_TAC std_ss [dimword_def,GSYM BITS_ZERO3,SLICE_BITS_THM,SUC_SUB1,
         word_slice_n2w,w2n_n2w]);

val MULT_MOD_SUC_T = save_thm("MULT_MOD_SUC_T",
  REWRITE_RULE [WORD_SLICE_THM] MULT_MOD_SUC_T);

(* ------------------------------------------------------------------------- *)

val LSL_MULT_EXP = prove(
  `!w n. w << n = w * n2w (2 ** n)`,
  Cases_word \\ POP_ASSUM (K ALL_TAC)
    \\ RW_TAC bool_ss [word_lsl_n2w,word_mul_n2w]
    \\ IMP_RES_TAC LESS_ADD_1
    \\ POP_ASSUM (SUBST1_TAC o SIMP_RULE std_ss [DIMINDEX_GT_0,
         DECIDE ``0 < n ==> (n - 1 + (p + 1) = p + n)``])
    \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
    \\ SIMP_TAC std_ss
         [dimword_def,EXP_ADD,MULT_ASSOC,MOD_EQ_0,ZERO_MOD,ZERO_LT_TWOEXP]);

val MULT_TWO_LSL = prove(
  `!rm t. rm << (2 * t + 1) = (rm << (2 * t)) * n2w 2`,
  SIMP_TAC arith_ss [LSL_MULT_EXP,GSYM WORD_MULT_ASSOC,word_mul_n2w,
    GSYM ADD1,EXP]);

val MULT_FOUR_LSL = prove(
  `!t rm. rm << (2 * (t + 1)) = (rm << (2 * t)) * n2w 4`,
  SIMP_TAC arith_ss [LSL_MULT_EXP,GSYM WORD_MULT_ASSOC,word_mul_n2w,
    LEFT_ADD_DISTRIB,EXP_ADD]);

val ALU6_MUL_def = Define`
  ALU6_MUL borrow2 (mul:word2) (alua:word32) alub =
    if ~borrow2 /\ (mul = 0w) \/ borrow2 /\ (mul = 3w) then
      alua
    else if borrow2 /\ (mul = 0w) \/ (mul = 1w) then
      alua + alub
    else
      alua - alub`;

val BORROW_LEM2 = prove(
  `!rs n. 2 * (n + 1) <= 32 ==>
          ((((2 * n + 1) >< (2 * n)) rs = 0w:word2) \/
           (((2 * n + 1) >< (2 * n)) rs = 1w:word2) ==> ~BORROW2 rs (n + 1)) /\
          ((((2 * n + 1) >< (2 * n)) rs = 2w:word2) \/
           (((2 * n + 1) >< (2 * n)) rs = 3w:word2) ==> BORROW2 rs (n + 1))`,
   RW_TAC arith_ss [word_extract_def,word2_BITS,
          (SIMP_RULE arith_ss [] o SPEC `n + 1`) BORROW2]
     \\ FULL_SIMP_TAC (fcp_ss++SIZES_ss) [w2w,word_bits_def]);

val WORD_ADD_SUB_LCANCEL = prove(
  `!a b. (a + b = a - c) = (b = $- c)`,
  METIS_TAC [WORD_EQ_ADD_LCANCEL,word_sub_def]);

val word2_word32 =
  LIST_CONJ [EVAL ``w2w:word2->word32 0w``,EVAL ``w2w:word2->word32 1w``,
             EVAL ``w2w:word2->word32 2w``,EVAL ``w2w:word2->word32 3w``];

val MSHIFT_lem = prove(
  `!n. 2 * (n + 1) <= 32 ==> (w2n ((w2w:word4->word5) (n2w n) * 2w) = 2 * n)`,
  RW_TAC (arith_ss++SIZES_ss) [w2w_def,w2n_n2w,word_mul_n2w]);

val MSHIFT_lem2 = prove(
  `!n. 2 * (n + 1) <= 32 ==>
      (w2n ((w2w:word4->word5) (n2w n) * 2w + 1w) = 2 * n + 1)`,
  RW_TAC (arith_ss++SIZES_ss) [w2w_def,w2n_n2w,word_mul_n2w,word_add_n2w]);

val MUL_1EXP = prove(
  `!a n. a * 1w << n = a << n`,
  Cases_word \\ RW_TAC arith_ss [WORD_MULT_CLAUSES,word_lsl_n2w,word_mul_n2w]);

val MUL_2EXP = prove(
  `!a n. a * 2w << n = a << (n + 1)`,
  Cases_word
    \\ RW_TAC arith_ss [WORD_MULT_CLAUSES,EXP_ADD,word_lsl_n2w,word_mul_n2w]
    \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ FULL_SIMP_TAC arith_ss [NOT_LESS]
    << [`n' = m` by DECIDE_TAC, `m = 0` by DECIDE_TAC]
    \\ ASM_SIMP_TAC arith_ss [Once (GSYM n2w_mod),ZERO_LT_TWOEXP,MOD_EQ_0,
         simpLib.SIMP_PROVE arith_ss [EXP]
           ``2 * (a * 2 ** b) = a * 2 ** SUC b``,
         dimword_def,ONCE_REWRITE_RULE [MULT_COMM] MOD_EQ_0]);

val MUL_3EXP = prove(
  `!a n. a * 3w << n = a << (n + 1) + a << n`,
  Cases_word
    \\ RW_TAC arith_ss [WORD_MULT_CLAUSES,EXP_ADD,GSYM LEFT_ADD_DISTRIB,
         word_lsl_n2w,word_mul_n2w,word_add_n2w]
    \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ FULL_SIMP_TAC arith_ss [NOT_LESS]
    << [`n' = m` by DECIDE_TAC,
        `m = 0` by DECIDE_TAC \\
           ONCE_REWRITE_TAC [DECIDE ``3 * n = n * 2 + n``]]
    \\ ASM_SIMP_TAC std_ss [Once (GSYM n2w_mod),LEFT_ADD_DISTRIB,
         ZERO_LT_TWOEXP,MOD_TIMES,dimword_def,
         simpLib.SIMP_PROVE arith_ss [EXP]
           ``3 * (a * 2 ** b) = a * 2 ** SUC b + a * 2 ** b``]
    \\ METIS_TAC [n2w_mod,dimword_def,EVAL ``2 ** (SUC 0) = 2``]);

val WORD_LEFT_ADD_DISTRIB_1 =
  (GEN_ALL o REWRITE_RULE [WORD_MULT_CLAUSES] o
   SPECL [`v`,`1w`] o GSYM) WORD_LEFT_ADD_DISTRIB;

val WORD_NEG_RMUL_1 =
  (GEN_ALL o REWRITE_RULE [WORD_MULT_CLAUSES] o
   SPECL [`v << n`,`1w`]) WORD_NEG_RMUL;

fun MUST_BE_TAC th =
  TRY (armLib.RES_MP1_TAC [`w` |-> `(2 * n + 1 >< 2 * n) (rs:word32)`] th
         >> ASM_SIMP_TAC bool_ss []);

val word_add_n2w_mod = prove(
  `!m n. ((n2w m):bool ** 'a) + n2w n = n2w ((m + n) MOD 2 ** ^WL)`,
  PROVE_TAC [dimword_def,n2w_mod,word_add_n2w]);

val _ = computeLib.add_thms [word_add_n2w_mod] computeLib.the_compset;

val RD_INVARIANT_THM = store_thm("RD_INVARIANT_THM",
  `!n a rm rs rn. 2 * (n + 1) <= 32 ==>
     (RD_INVARIANT a rm rs rn (n + 1) =
        let borrow2 = BORROW2 rs n
        and mul = ((2 * n + 1) >< (2 * n)) rs
        in
          ALU6_MUL borrow2 mul (RD_INVARIANT a rm rs rn n)
            (rm << w2n (MSHIFT2 borrow2 mul (n2w n))))`,
  RW_TAC std_ss [BORROW_LEM2,MSHIFT2_def,RD_INVARIANT_def,ALU6_MUL_def]
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [BORROW_LEM2,n2w_11]
    \\ MAP_EVERY MUST_BE_TAC [MUST_BE_TWO, MUST_BE_THREE]
    \\ FULL_SIMP_TAC std_ss [BORROW_LEM2]
    \\ ASM_SIMP_TAC bool_ss [MULT_MOD_SUC_T,WORD_EQ_ADD_LCANCEL,WORD_SUB_LZERO,
         WORD_RCANCEL_SUB,WORD_ADD_SUB_LCANCEL,GSYM WORD_ADD_ASSOC,
         WORD_ADD_SUB_ASSOC,GSYM WORD_ADD_SUB_SYM,WORD_ADD_0,WORD_SUB_REFL,
         WORD_MULT_CLAUSES,CONJUNCT1 ZERO_SHIFT,MSHIFT_lem,MSHIFT_lem2,
         MUL_1EXP,MUL_2EXP,MUL_3EXP,word2_word32]
    \\ SIMP_TAC bool_ss [MULT_TWO_LSL,MULT_FOUR_LSL,word_sub_def,
         AC WORD_ADD_ASSOC WORD_ADD_COMM,WORD_EQ_ADD_LCANCEL,
         WORD_NEG_RMUL,GSYM WORD_LEFT_ADD_DISTRIB,WORD_LEFT_ADD_DISTRIB_1]
    \\ REWRITE_TAC [WORD_NEG_RMUL_1,GSYM WORD_LEFT_ADD_DISTRIB]
    \\ EVAL_TAC \\ REWRITE_TAC [WORD_MULT_CLAUSES]);

val RD_INVARIANT_SUC = prove(
  `!n a rs.
    ~(n = 0) /\ SUC n <= MLA_MUL_DUR rs ==>
    (((2 * n + 1) >< (2 * n)) rs = mul) ==>
    ((if ~BORROW2 rs n /\ (mul = 0w:word2) \/ BORROW2 rs n /\ (mul = 3w) then
        RD_INVARIANT a rm rs rn n
      else
        (if BORROW2 rs n /\ (mul = 0w) \/ (mul = 1w) then
           RD_INVARIANT a rm rs rn n +
           rm << w2n (w2w ((n2w n):word4) * (2w:word5) +
                       (if BORROW2 rs n /\ (mul = 1w) \/
                          ~BORROW2 rs n /\ (mul = 2w) then 1w else 0w))
         else
           RD_INVARIANT a rm rs rn n -
           rm << w2n (w2w ((n2w n):word4) * (2w:word5) +
                       (if ~BORROW2 rs n /\ (mul = 2w) then 1w else 0w)))) =
      RD_INVARIANT a rm rs rn (n + 1))`,
  NTAC 4 STRIP_TAC
    \\ IMP_RES_TAC (SPEC `SUC n` LEQ_MLA_MUL_DUR)
    \\ RW_TAC arith_ss [RD_INVARIANT_THM,ALU6_MUL_def,MSHIFT2_def,
         MSHIFT_lem,MSHIFT_lem2,WORD_ADD_0,ADD_0]);

val RD_ONE = (GSYM o
   SIMP_RULE arith_ss [RD_INVARIANT_def,BORROW2,MOD_4_BITS,n2w_w2n] o
   SIMP_RULE (arith_ss++SIZES_ss) [RD_INVARIANT_ZERO,BORROW2_def,MSHIFT2_def,
     ALU6_MUL_def,SHIFT_ZERO,WORD_MULT_CLAUSES,WORD_ADD_0,w2w_def,
     w2n_n2w,EVAL ``1w:word2 = 2w``] o SPEC `0`) RD_INVARIANT_THM;

val BORROW2_SUC = prove(
  `!rs n. SUC n <= MLA_MUL_DUR rs ==>
      (((2 * n + 1 >< 2 * n) rs):word2 %% 1 = BORROW2 rs (n + 1))`,
  REPEAT STRIP_TAC \\ IMP_RES_TAC (SPEC `SUC n` LEQ_MLA_MUL_DUR)
    \\ FULL_SIMP_TAC arith_ss [ADD1,BORROW2]);

(* ------------------------------------------------------------------------- *)

fun Cases_on_nzc tm =
  SPEC_THEN tm FULL_STRUCT_CASES_TAC (armLib.tupleCases
  ``(n,z,c):bool#bool#bool``);

val SET_NZC_IDEM = prove(
  `!a b xpsr. SET_NZC a (SET_NZC b xpsr) = SET_NZC a xpsr`,
  REPEAT STRIP_TAC \\ Cases_on_nzc `a` \\ Cases_on_nzc `b`
    \\ SIMP_TAC bool_ss [SET_NZC_def,SET_NZCV_IDEM,DECODE_NZCV_SET_NZCV]);

val DECODE_MODE_SET_NZC = prove(
  `!a psr. DECODE_MODE ((4 >< 0) (SET_NZC a psr)) =
           DECODE_MODE ((4 >< 0) psr)`,
  STRIP_TAC \\ Cases_on_nzc `a`
    \\ SIMP_TAC bool_ss [SET_NZC_def,DECODE_MODE_def,DECODE_IFMODE_SET_NZCV]);

val IF_FLAGS_SET_NZC = prove(
  `!a psr n. (n = 6) \/ (n = 7) ==> ((SET_NZC a psr) %% n = psr %% n)`,
  STRIP_TAC \\ Cases_on_nzc `a` \\ RW_TAC bool_ss [SET_NZC_def]
    \\ SIMP_TAC bool_ss [DECODE_IFMODE_SET_NZCV]);

val IF_FLAGS_SET_NZC_COND = prove(
  `!a psr b n. (n = 6) \/ (n = 7) ==>
     ((if b then SET_NZC a psr else psr) %% n = psr %% n)`,
  METIS_TAC [IF_FLAGS_SET_NZC]);

(* ------------------------------------------------------------------------- *)

val MSHIFT_ZERO = prove(
  `!a. w2w (((4 >< 1) (if a then 1w:word5 else 0w)) + 1w:word4) =
       w2w (1w:word4):word5`,
  RW_TAC std_ss [] \\ EVAL_TAC);

val MSHIFT_SUC = prove(
  `!n. (4 >< 1)
         (w2w ((n2w n):word4) * (2w:word5) + (if b then 1w else 0w)) + 1w =
       n2w (n + 1):word4`,
  RW_TAC (arith_ss++SIZES_ss) [BITS_COMP_THM2,
        (SIMP_RULE arith_ss [] o SPECL [`4`,`1`]) BITS_ZERO4,
        (SIMP_RULE arith_ss [] o SPECL [`4`,`1`,`a`,`1`]) BITS_SUM,
        word_extract_def,word_bits_n2w,n2w_11,MOD_DIMINDEX,
        word_mul_n2w,word_add_n2w,w2w_n2w]
    \\ SIMP_TAC std_ss [BITS_ZERO3,ONCE_REWRITE_RULE [ADD_COMM] MOD_PLUS_RIGHT]
);

val MSHIFT_lem3 = prove(
  `SUC n <= MLA_MUL_DUR rs ==> n < 16`,
  REPEAT STRIP_TAC \\ IMP_RES_TAC (SPEC `SUC n` LEQ_MLA_MUL_DUR)
    \\ FULL_SIMP_TAC arith_ss [ADD1]);

(* ------------------------------------------------------------------------- *)

val arithi_ss = let open armLib in
  arith_ss++ICLASS_ss++PBETA_ss++STATE_INP_ss++SIZES_ss end;

val MLA_MUL_INVARIANT = Count.apply prove(
  `!n x i mem reg psr alua pipeb ireg ointstart obaselatch onfq ooonfq
    oniq oooniq pipeaabt pipebabt dataabt2 aregn2 sctrl psrfb orp.
    Abbrev (pc = REG_READ6 reg usr 15w) /\ Abbrev (cpsr = CPSR_READ psr) /\
    Abbrev (nbs = DECODE_MODE ((4 >< 0) cpsr)) /\
    Abbrev (w = MLA_MUL_DUR (REG_READ6 reg nbs ((11 >< 8) ireg))) /\
    (!t. t < w + 1 ==> ~IS_RESET i t) /\ n <= w ==>
    ?ointstart' obaselatch' onfq' ooonfq' oniq' oooniq' pipeaabt' pipebabt'
     iregabt' dataabt' aregn'.
      ~(aregn' IN {0w; 1w; 2w; 5w}) /\
      ((aregn' = 7w) ==> ~(CPSR_READ psr %% 6)) /\
      ((aregn' = 6w) ==> ~(CPSR_READ psr %% 7)) /\
      let Rm = (3 >< 0) ireg and Rd = (19 >< 16) ireg
      and rs = REG_READ6 reg nbs ((11 >< 8) ireg)
      and rn = REG_READ6 reg nbs ((15 >< 12) ireg) in
      let rm = REG_READ6 (INC_PC reg) nbs Rm in
      (FUNPOW (SNEXT NEXT_ARM6) n <|state := ARM6 (DP
                (if (Rd = 15w) \/ (Rd = Rm) then
                   REG_WRITE reg nbs 15w (pc + 4w)
                 else
                   REG_WRITE (REG_WRITE reg nbs 15w (pc + 4w)) nbs Rd
                     (if ireg %% 21 then rn else 0w))
                 psr (pc + 4w) ireg alua rn dout)
           (CTRL pipea T pipeb T ireg T ointstart F F obaselatch F mla_mul tn
              F F F onfq ooonfq oniq oooniq pipeaabt pipebabt pipebabt dataabt2
              aregn2 F T F sctrl psrfb ((1 >< 0) pc) ARB ARB orp ((1 >< 0) rs)
              ((31 -- 2) rs) F (if (1 >< 0) rs = 2w:word2 then 1w else 0w));
           inp := ADVANCE 1 i|> =
        (let mul = (1 >< 0) ((31 -- (2 * (n - 1))) rs) in
         let rd = RD_INVARIANT (ireg %% 21) rm rs rn (n - 1)
         and mshift = MSHIFT mla_mul (BORROW2 rs (n - 1)) mul (n2w (n - 1))
         and mul' = (1 >< 0) ((31 -- (2 * n)) rs)
         and borrow2 = BORROW2 rs n in
         let rd' = RD_INVARIANT (ireg %% 21) rm rs rn n
         and newinst = MLA_MUL_DONE rs n in
         let nxtic = if newinst then
                       if ointstart' then swi_ex else DECODE_INST pipeb
                     else mla_mul in
          <| state := ARM6 (DP
              (if (Rd = 15w) \/ (Rd = Rm) then
                 REG_WRITE reg nbs 15w (pc + 4w)
               else
                 REG_WRITE (REG_WRITE reg nbs 15w (pc + 4w)) nbs Rd rd')
              (if (n = 0) \/ ~(ireg %% 20) \/ (Rd = 15w) \/ (Rd = Rm) then
                 psr
               else
                 CPSR_WRITE psr (SET_NZC (word_msb rd',rd' = 0w,
                    FST (LSL rm (w2w mshift)
                      (CARRY (FST (DECODE_PSR cpsr))))) cpsr))
              (pc + 4w) (if newinst then pipeb else ireg)
              (if n = 0 then
                 alua
               else if (Rd = 15w) \/ (Rd = Rm) then
                 REG_READ6 (REG_WRITE reg nbs 15w (pc + 4w)) nbs Rd
               else
                 rd)
              (if n = 0 then rn else rm << w2n mshift)
              (if n = 0 then dout else rm))
             (CTRL
                pipea T (if newinst then pipea else pipeb) T
                (if newinst then pipeb else ireg) T ointstart' newinst newinst
                obaselatch' newinst nxtic (if newinst then t3 else tn)
                F F F onfq' ooonfq' oniq' oooniq' pipeaabt' pipebabt'
                (if newinst then iregabt' else pipebabt') dataabt'
                (if n = 0 then aregn2 else if ointstart' then aregn' else 2w)
                (~(n = 0) /\ newinst) T F sctrl psrfb
                (if n = 0 then (1 >< 0) pc else (1 >< 0) (pc + n2w 4))
                (MASK nxtic (if newinst then t3 else tn) ARB ARB)
                ARB (if n = 0 then orp else ARB) mul' ((31 -- (2 * (n + 1))) rs)
                borrow2 (MSHIFT mla_mul borrow2 mul' (n2w n)));
            inp := ADVANCE n (ADVANCE 1 i)|>))`,
  REPEAT STRIP_TAC
    \\ SIMP_TAC bool_ss [LET_THM]
    \\ ABBREV_TAC `Rm:word4 = (3 >< 0) ireg`
    \\ ABBREV_TAC `Rd:word4 = (19 >< 16) ireg`
    \\ ABBREV_TAC `rs = REG_READ6 reg nbs ((11 >< 8) ireg)`
    \\ ABBREV_TAC `rn = REG_READ6 reg nbs ((15 >< 12) ireg)`
    \\ ABBREV_TAC `rm = REG_READ6 (INC_PC reg) nbs Rm`
    \\ Induct_on `n`
    >> (SIMP_TAC (arith_ss++armLib.ICLASS_ss++armLib.STATE_INP_ss)
          [state_arm6_11,ctrl_11,io_onestepTheory.state_out_literal_11,FUNPOW,
           BORROW2_def,MSHIFT,RD_INVARIANT_ZERO,MASK_def,WORD_MULT_CLAUSES,
           DONE_NEQ_ZERO,io_onestepTheory.ADVANCE_ZERO,EVAL ``w2w (0w:word4)``,
           WORD_ADD_0] \\ SIMP_TAC std_ss [word_extract_def,WORD_BITS_COMP_THM]
          \\ METIS_TAC [interrupt_exists])
    \\ REWRITE_TAC [FUNPOW_SUC]
    \\ Cases_on `n = 0`
    << [
      PAT_ASSUM `x ==> P` (K ALL_TAC)
        \\ ASM_REWRITE_TAC [FUNPOW]
        \\ REPEAT STRIP_TAC
        \\ FULL_SIMP_TAC bool_ss [Abbr`pc`,REG_READ_WRITE,TO_WRITE_READ6]
        \\ `~IS_RESET i 1` by ASM_SIMP_TAC arith_ss []
        \\ IMP_RES_TAC NOT_RESET_EXISTS
        \\ ASM_SIMP_TAC std_ss [SNEXT,ADVANCE_def] \\ MLA_MUL_TAC
        \\ ASM_SIMP_TAC arithi_ss
             [FST_COND_RAND,SND_COND_RAND,IF_NEG,COMP_VAL_BIT2,BITS_X_SUB2_1,
              LSL_ZERO,ALUOUT_ADD,ALUOUT_SUB,COUNT1_ZERO,MUL1_SUC_1,BORROW2,
              MULX_DONE_ZERO,BITS_ZEROL,RD_INVARIANT_ZERO,SND_LSL,NZ_SUB,
              ALUOUT_ALU_logic,NZ_ALU_logic,NZ_ADD,WORD_BITS_COMP_THM,
              COND_PAIR,CARRY_LEM,state_arm6_11,dp_11]
        \\ Cases_on `~(Rd = 15w) /\ ~(Rd = Rm)`
        \\ FULL_SIMP_TAC (armLib.stdi_ss++SIZES_ss)
            [(GSYM o ISPEC `word_msb`) COND_RAND,SHIFT_ZERO,n2w_11,word_0_n2w,
             AREGN1_def,(GSYM o BETA_RULE o ISPEC `\x. x = 0w`) COND_RAND,
             REG_READ_WRITE,TO_WRITE_READ6,REG_WRITE_WRITE,REG_READ_WRITE_PC,
             MSHIFT_ZERO,IF_NEG,RD_INVARIANT_ONE,RD_ONE,WORD_EXTRACT_BITS_COMP,
             EVAL ``w2w (0w:word4)``,WORD_MULT_CLAUSES,WORD_ADD_0,
             w2n_w2w,ctrl_11]
        \\ UNABBREV_TAC `rm` \\ POP_ASSUM_LIST (K ALL_TAC)
        \\ EXISTS_TAC `pipebabt`
        \\ EXISTS_TAC `if dataabt2 \/ ~(cpsr %% 6) /\ ~ooonfq \/ pipebabt \/
                          ~(cpsr %% 7) /\ ~oooniq
                       then
                         AREGN1 F dataabt2 (~(cpsr %% 6) /\ ~ooonfq)
                           (~(cpsr %% 7) /\ ~oooniq) F pipebabt
                       else 3w`
        \\ RW_TAC std_ss [AREGN1_def]
        \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [pred_setTheory.IN_INSERT,n2w_11,
             pred_setTheory.NOT_IN_EMPTY],
      STRIP_TAC
        \\ `n <= w` by DECIDE_TAC
        \\ PAT_ASSUM `n ==> P` IMP_RES_TAC
        \\ ASM_SIMP_TAC arith_ss [NOT_DONE_SUC,BORROW2,
             GSYM io_onestepTheory.ADVANCE_COMP,ADD1]
        \\ POP_ASSUM (K ALL_TAC)
        \\ FULL_SIMP_TAC bool_ss [Abbr`pc`,REG_READ_WRITE,TO_WRITE_READ6]
        \\ `~IS_RESET i (n + 1)` by ASM_SIMP_TAC arith_ss []
        \\ IMP_RES_TAC NOT_RESET_EXISTS
        \\ ASM_SIMP_TAC arith_ss [Abbr`w`,SNEXT,ADVANCE_def] \\ MLA_MUL_TAC
        \\ ASM_SIMP_TAC arithi_ss
             [GSYM ADVANCE_COMP,COND_PAIR,FST_COND_RAND,SND_COND_RAND,
              (REWRITE_RULE [combinTheory.o_THM] o
               ISPEC `DECODE_MODE o (4 >< 0)`) COND_RAND,
               ISPEC `CPSR_READ` COND_RAND,IF_NEG,COMP_VAL_BIT2,COUNT1,ADD1,
              (SIMP_RULE std_ss [] o SPECL [`n`,`31`]) BITS_X_SUB2,MSHIFT_SUC,
              CPSR_WRITE_WRITE,CPSR_WRITE_READ,DECODE_MODE_SET_NZC,w2n_w2w,
              SPEC_MULX_DONE,ALUOUT_ADD,ALUOUT_SUB,SND_LSL,ALUOUT_ALU_logic,
              NZ_ALU_logic,NZ_ADD,NZ_SUB,CARRY_LEM,MUL1,MUL1_SUC,state_arm6_11]
        \\ Cases_on `~(Rd = 15w) /\ ~(Rd = Rm)`
        \\ FULL_SIMP_TAC bool_ss [dp_11,ctrl_11,RD_INVARIANT_SUC,BORROW2_SUC,
             (GSYM o ISPEC `word_msb`) COND_RAND,IF_FLAGS_SET_NZC_COND,
             (GSYM o BETA_RULE o ISPEC `\x. x = 0w`) COND_RAND,
             TO_WRITE_READ6,REG_READ_WRITE,REG_READ_WRITE_PC,
             SET_NZC_IDEM,REG_WRITE_WRITE,IF_NEG]
        \\ EXISTS_TAC `pipebabt'`
        \\ EXISTS_TAC `if dataabt' \/ ~(cpsr %% 6) /\ ~ooonfq' \/
                         pipebabt' \/ ~(cpsr %% 7) /\ ~oooniq'
                       then
                         AREGN1 F dataabt' (~(cpsr %% 6) /\ ~ooonfq')
                           (~(cpsr %% 7) /\ ~oooniq') F pipebabt'
                         else 3w`
        << [
          PAT_ABBREV_TAC `bigc = CARRY (FST (DECODE_PSR (SET_NZC (a,b,c) x)))`
            \\ ABBREV_TAC `mul:word2 = ((2 * n + 1) >< (2 * n)) rs`
            \\ PAT_ABBREV_TAC `mshift:word8 = w2w (w:word5)`
            \\ `~(mshift = 0w)`
            by (IMP_RES_TAC MSHIFT_lem3 \\
                RW_TAC (arith_ss++SIZES_ss)
                 [Abbr`mshift`,BITS_COMP_THM2,BITS_ZERO2,w2w_n2w,word_mul_n2w,
                  word_add_n2w,REWRITE_RULE [MOD_DIMINDEX] n2w_11,
                  (SIMP_RULE std_ss [] o SPEC `3`) BITS_ZEROL] \\
                 ASM_SIMP_TAC arith_ss [
                   (SIMP_RULE std_ss [] o SPEC `4`) BITS_ZEROL])
            \\ POP_ASSUM (fn th => ASSUME_TAC (MATCH_MP LSL_CARRY_SUBST th))
            \\ POP_ASSUM (fn th => SUBST1_TAC (SPECL
                 [`CARRY (FST (DECODE_PSR cpsr))`,`rm`,`bigc`] th))
            \\ REWRITE_TAC [], ALL_TAC, ALL_TAC]
        \\ POP_ASSUM_LIST (K ALL_TAC)
        \\ RW_TAC armLib.stdi_ss [AREGN1_def]
        \\ FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss++SIZES_ss) [n2w_11]
    ]
);

(* ------------------------------------------------------------------------- *)

val MLA_MUL_INVARIANT = save_thm("MLA_MUL_INVARIANT",
  (GEN_ALL o SIMP_RULE std_ss []) MLA_MUL_INVARIANT);

val lem = SPEC `w = MLA_MUL_DUR (REG_READ6 reg nbs ((11 >< 8) ireg))`
  markerTheory.Abbrev_def;

val MLA_MUL_TN = save_thm("MLA_MUL_TN",
  (GEN_ALL o SIMP_RULE std_ss [] o ONCE_REWRITE_RULE [GSYM lem] o
   SIMP_RULE arith_ss [lem,TO_WRITE_READ6,RD_INVARIANT_LAST,
     DONE_DUR,DUR_NEQ_ZERO] o
   INST [`n` |-> `w`] o SPEC_ALL) MLA_MUL_INVARIANT);

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
