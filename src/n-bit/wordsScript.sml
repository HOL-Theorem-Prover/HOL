(* ========================================================================= *)
(* FILE          : wordsScript.sml                                           *)
(* DESCRIPTION   : A model of binary words. Based on John Harrison's         *)
(*                 treatment of finite Cartesian products (TPHOLs 2005)      *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2005                                                      *)
(* ========================================================================= *)

(* interactive use:
  app load ["pred_setTheory", "bitTheory", "sum_numTheory", "fcpTheory"];
*)

open HolKernel Parse boolLib bossLib;
open Q arithmeticTheory pred_setTheory;
open bitTheory sum_numTheory fcpTheory;

val _ = new_theory "words";

(* ------------------------------------------------------------------------- *)

val Abbr = BasicProvers.Abbr;
val fcp_ss = std_ss ++ rewrites [FCP_BETA,FCP_ETA,CART_EQ];

val WL = ``dimindex (UNIV:'a->bool)``;
val HB = ``^WL - 1``;
val TOP = ``2 ** ^WL``;
val MSB = ``2 ** ^HB``;

fun Def s = curry Definition.new_definition s o Parse.Term;
fun xDef s n t = boolSyntax.new_infixr_definition(s, Parse.Term t, n);
fun xlDef s n t = boolSyntax.new_infixl_definition(s, Parse.Term t, n);

(* ------------------------------------------------------------------------- *)
(*  Domain transforming maps : definitions                                   *)
(* ------------------------------------------------------------------------- *)

val w2n_def = Def "w2n_def"
  `w2n (w:bool ** 'a) = SUM ^WL (\i. SBIT (w %% i) i)`;

val n2w_def = Def "n2w_def"
  `(n2w:num->(bool ** 'a)) n = FCP i. BIT i n`;

val w2w_def = Define`
  (w2w:bool ** 'a -> bool ** 'b) w = n2w (w2n w)`;

val sw2sw_def = Define`
  (sw2sw:bool ** 'a -> bool ** 'b) w =
    n2w (SIGN_EXTEND (dimindex(UNIV:'a->bool))
                     (dimindex(UNIV:'b->bool)) (w2n w))`;

val _ = add_bare_numeral_form (#"w", SOME "n2w");

(* ------------------------------------------------------------------------- *)
(*  The Boolean operations : definitions                                     *)
(* ------------------------------------------------------------------------- *)

val word_T_def = Define`
  word_T = n2w:num->(bool ** 'a) (^TOP - 1)`;

val word_L_def = Define`
  word_L = n2w:num->(bool ** 'a) ^MSB`;

val word_H_def = Define`
  word_H = n2w:num->(bool ** 'a) (^MSB - 1)`;

val word_1comp_def = Def "word_1comp_def"
  `word_1comp (w:bool ** 'a) = (FCP i. ~(w %% i)):bool ** 'a`;

val word_and_def = xDef "word_and_def" 400
  `$&& (v:bool ** 'a) (w:bool ** 'a) =
    (FCP i. (v %% i) /\ (w %% i)):bool ** 'a`;

val word_or_def = xDef "word_or_def" 300
  `$!! (v:bool ** 'a) (w:bool ** 'a) =
    (FCP i. (v %% i) \/ (w %% i)):bool ** 'a`;

val word_xor_def = xDef "word_xor_def" 300
  `$?? (v:bool ** 'a) (w:bool ** 'a) =
    (FCP i. ~((v %% i) = (w %% i))):bool ** 'a`;

val bool_not = Term`$~`
val _ = overload_on ("~", Term`$word_1comp`);
val _ = overload_on ("~", bool_not);
val _ = overload_on ("Tw", ``word_T``);

(* ------------------------------------------------------------------------- *)
(*  Bit field operations : definitions                                       *)
(* ------------------------------------------------------------------------- *)

val word_lsb_def = Def "word_lsb_def"
  `word_lsb (w:bool ** 'a) = w %% 0`;

val word_msb_def = Def "word_msb_def"
  `word_msb (w:bool ** 'a) = w %% ^HB`;

val word_slice_def = xDef "word_slice_def" 350
  `$<> h l = \w:bool ** 'a.
    (FCP i. l <= i /\ i <= MIN h ^HB /\ w %% i):bool ** 'a`;

val word_bits_def = xDef "word_bits_def" 350
  `$-- h l = \w:bool ** 'a.
    (FCP i. i + l <= MIN h ^HB /\ w %% (i + l)):bool ** 'a`;

val _ = set_fixity "><" (Infixr 350);

val word_extract_def = xDefine "word_extract" `h >< l = w2w o (h -- l)`;

val word_bit_def = Def "word_bit_def"
  `word_bit b (w:bool ** 'a) = b <= ^HB /\ w %% b`;

val word_reverse_def = Def "word_reverse_def"
  `word_reverse (w:bool ** 'a) = (FCP i. w %% (^HB - i)):bool ** 'a`;

val word_modify_def = Def "word_modify_def"
  `word_modify f (w:bool ** 'a) = (FCP i. f i (w %% i)):bool ** 'a`;

(* ------------------------------------------------------------------------- *)
(*  Word arithmetic: definitions                                             *)
(* ------------------------------------------------------------------------- *)

val word_2comp_def = Def "word_2comp_def"
  `word_2comp (w:bool ** 'a) =
    n2w:num->(bool ** 'a) (^TOP - w2n w)`;

val word_add_def = Def "word_add_def"
  `word_add (v:bool ** 'a) (w:bool ** 'a) =
    n2w:num->(bool ** 'a) (w2n v + w2n w)`;

val word_sub_def = Define`
  word_sub (v:bool ** 'a) (w:bool ** 'a) = word_add v (word_2comp w)`;

val word_mul_def = Def "word_mul_def"
  `word_mul (v:bool ** 'a) (w:bool ** 'a) =
    n2w:num->(bool ** 'a) (w2n v * w2n w)`;

val word_log2_def = Def "word_log2_def"
  `word_log2 (w:bool ** 'a) = (n2w (LOG2 (w2n w)):bool ** 'a)`;

val _ = overload_on ("+",   Term`$word_add`);
val _ = overload_on ("-",   Term`$word_sub`);
val _ = overload_on ("-",   Term`$word_2comp`);
val _ = overload_on ("*",   Term`$word_mul`);

(* ------------------------------------------------------------------------- *)
(*  Shifts : definitions                                                     *)
(* ------------------------------------------------------------------------- *)

val word_lsl_def = xlDef "word_lsl_def" 680
  `$<< (w:bool ** 'a) n =
    (FCP i. i < ^WL /\ n <= i /\ w %% (i - n)):bool ** 'a`;

val word_lsr_def = xlDef "word_lsr_def" 680
  `$>>> (w:bool ** 'a) n =
    (FCP i. i + n < ^WL /\ w %% (i + n)):bool ** 'a`;

val word_asr_def = xlDef "word_asr_def" 680
  `$>> (w:bool ** 'a) n =
    (FCP i. if ^WL <= i + n then
              word_msb w
            else
              w %% (i + n)):bool ** 'a`;

val word_ror_def = xlDef "word_ror_def" 680
  `$#>> (w:bool ** 'a) n =
    (FCP i. w %% ((i + n) MOD ^WL)):bool ** 'a`;

val word_rol_def = xlDef "word_rol_def" 680
  `$#<< (w:bool ** 'a) n =
    w #>> (^WL - n MOD ^WL)`;

val word_rrx_def = Def "word_rrx_def"
  `word_rrx (w:bool ** 'a) c =
    (FCP i. if i = ^HB then
              c
            else
              (w >>> 1) %% i):bool ** 'a`;

(* ------------------------------------------------------------------------- *)
(*  Concatenation : definition                                               *)
(* ------------------------------------------------------------------------- *)

val word_concat_def = xDef "word_concat_def" 700
  `($@@ (v:bool ** 'a) (w:bool ** 'b)):bool ** ('a + 'b) =
    let cv = (w2w v):bool ** ('a + 'b)
    and cw = (w2w w):bool ** ('a + 'b)
    in word_add (cv << (dimindex (UNIV:'b->bool))) cw`;

(* ------------------------------------------------------------------------- *)
(*  Orderings : definitions                                                  *)
(* ------------------------------------------------------------------------- *)

val nzcv_def = Define `
  nzcv (a:bool ** 'a) (b:bool ** 'a) =
    let q = w2n a + w2n ($- b) in
    let r = (n2w q):bool ** 'a in
      (word_msb r,r = 0w,BIT ^WL q \/ (b = 0w),
     ~(word_msb a = word_msb b) /\ ~(word_msb r = word_msb a))`;

val word_lt_def = Def "word_lt_def"
  `word_lt a b = let (n,z,c,v) = nzcv a b in ~(n = v)`;

val word_gt_def = Def "word_gt_def"
  `word_gt a b = let (n,z,c,v) = nzcv a b in ~z /\ (n = v)`;

val word_le_def = Def "word_le_def"
  `word_le a b = let (n,z,c,v) = nzcv a b in z \/ ~(n = v)`;

val word_ge_def = Def "word_ge_def"
  `word_ge a b = let (n,z,c,v) = nzcv a b in n = v`;

val word_ls_def = xDef "word_ls_def" 450
  `$<=+ a b = let (n,z,c,v) = nzcv a b in ~c \/ z`;

val word_hi_def = xDef "word_hi_def" 450
  `$>+ a b = let (n,z,c,v) = nzcv a b in c /\ ~z`;

val word_lo_def = xDef "word_lo_def" 450
  `$<+ a b = let (n,z,c,v) = nzcv a b in ~c`;

val word_hs_def = xDef "word_hs_def" 450
  `$>=+ a b = let (n,z,c,v) = nzcv a b in c`;

val _ = overload_on ("<",  Term`word_lt`);
val _ = overload_on ("<=", Term`word_le`);
val _ = overload_on (">",  Term`word_gt`);
val _ = overload_on (">=", Term`word_ge`);

(* ------------------------------------------------------------------------- *)
(*  Theorems                                                                 *)
(* ------------------------------------------------------------------------- *)

val DIMINDEX_GT_0 =
  PROVE [DECIDE ``!s. 1 <= s ==> 0 < s``,DIMINDEX_GE_1] ``!s. 0 < dimindex s``;

val DIMINDEX_LT =
  (GEN_ALL o CONJUNCT2 o SPEC_ALL o SIMP_RULE std_ss [DIMINDEX_GT_0] o
   SPEC `^WL`) DIVISION;

val EXISTS_HB =
  PROVE [DIMINDEX_GT_0,LESS_ADD_1,ADD1,ADD] ``?m. ^WL = SUC m``;

val SUB1_SUC = DECIDE (Term `!n. 0 < n ==> (SUC (n - 1) = n)`);
val SUB_SUC1 = DECIDE (Term `!n. ~(n = 0) ==> (SUC (n - 1) = n)`);
val SUC_SUB2 = DECIDE (Term `!n. ~(n = 0) ==> (SUC n - 2 = n - 1)`);

(* ------------------------------------------------------------------------- *)
(*  Domain transforming maps : theorems                                      *)
(* ------------------------------------------------------------------------- *)

val WORD_ss = rewrites [w2n_def,n2w_def];

val SUM_SLICE = prove(
  `!n x. SUM n (\i. SLICE i i x) = x MOD 2 ** n`,
  Induct THEN ASM_SIMP_TAC arith_ss [SUM_def]
    THEN Cases_on `n`
    THEN SIMP_TAC arith_ss [GSYM BITS_ZERO3,GSYM SLICE_ZERO_THM,
           ONCE_REWRITE_RULE [ADD_COMM] SLICE_COMP_THM]);

val SUM_SBIT_LT = prove(
  `!n f. SUM n (\i. SBIT (f i) i) < 2 ** n`,
  Induct THEN ASM_SIMP_TAC arith_ss [SUM_def,ZERO_LT_TWOEXP]
    THEN STRIP_TAC THEN `SBIT (f n) n <= 2 ** n` by RW_TAC arith_ss [SBIT_def]
    THEN METIS_TAC [EXP,DECIDE ``!a b c. a <= b /\ c < b ==> a + c < 2 * b``]
);

val w2n_n2w_lem = prove(
  `!n. SUM ^WL (\i. SBIT ((FCP i. BIT i n):bool ** 'a %% i) i) =
       SUM ^WL (\i. SLICE i i n)`,
  STRIP_TAC THEN REWRITE_TAC [SUM] THEN MATCH_MP_TAC GSUM_FUN_EQUAL
    THEN RW_TAC (fcp_ss++ARITH_ss) [BIT_SLICE_THM]);

val w2n_n2w = store_thm("w2n_n2w",
  `!n. w2n (n2w:num->(bool ** 'a) n) = n MOD ^TOP`,
  SIMP_TAC (fcp_ss++WORD_ss) [w2n_n2w_lem,SUM_SLICE]);

val n2w_w2n_lem = prove(
  `!n f i. BIT i (SUM n (\j. SBIT (f j) j)) = f i /\ i < n`,
  Induct THEN ASM_SIMP_TAC arith_ss [SUM_def,BIT_ZERO]
    THEN REPEAT STRIP_TAC THEN Cases_on `i < n`
    THEN FULL_SIMP_TAC arith_ss [NOT_LESS,prim_recTheory.LESS_THM]
    THENL [
      IMP_RES_TAC LESS_ADD_1
        THEN `SBIT (f n) n = (if f n then 1 else 0) * 2 ** p * 2 ** (SUC i)`
          by RW_TAC (arith_ss++numSimps.ARITH_AC_ss) [SBIT_def,EXP_ADD,EXP]
        THEN FULL_SIMP_TAC std_ss [BITS_SUM2,BIT_def],
      PAT_ASSUM `!f i. P` (SPECL_THEN [`f`,`i`] ASSUME_TAC)
        THEN `SUM n (\i. SBIT (f i) i) < 2 ** n` by METIS_TAC [SUM_SBIT_LT]
        THEN IMP_RES_TAC LESS_EQUAL_ADD
        THEN `SBIT (f n) n = (if f n then 1 else 0) * 2 ** n`
          by RW_TAC arith_ss [SBIT_def]
         THEN ASM_SIMP_TAC arith_ss [BITS_SUM,
                (GSYM o REWRITE_RULE [LESS_EQ_REFL] o
                 SPECL [`p`,`n + p`,`n`]) BIT_OF_BITS_THM]
         THEN FULL_SIMP_TAC arith_ss [BIT_def,BITS_COMP_THM2]
         THEN Cases_on `p = 0` THEN RW_TAC arith_ss [BITS_ZERO2]
         THEN ASM_SIMP_TAC arith_ss [GSYM BIT_def,BIT_B,BIT_B_NEQ]
    ]
);

val n2w_w2n = store_thm("n2w_w2n",
  `!w. n2w (w2n (w:bool ** 'a)) = w`,
  SIMP_TAC (fcp_ss++WORD_ss) [n2w_w2n_lem]);

val word_nchotomy = store_thm("word_nchotomy",
  `!w. ?n. w = n2w n`, PROVE_TAC [n2w_w2n]);

fun Cases_on_word tm = FULL_STRUCT_CASES_TAC (SPEC tm word_nchotomy);
fun Cases_word (g as (_,w)) =
  let val (Bvar,_) = with_exn dest_forall w (ERR "Cases_word" "not a forall")
  in (STRIP_TAC THEN STRUCT_CASES_TAC (Thm.SPEC Bvar word_nchotomy)) g
  end

val n2w_mod = store_thm("n2w_mod",
  `!n. n2w:num -> bool ** 'a (n MOD ^TOP) = n2w n`,
  RW_TAC fcp_ss []
    THEN STRIP_ASSUME_TAC EXISTS_HB
    THEN ASM_SIMP_TAC (fcp_ss++ARITH_ss)
           [n2w_def,MIN_DEF,BIT_def,GSYM BITS_ZERO3,BITS_COMP_THM2]);

val n2w_11 = store_thm("n2w_11",
  `!m n. ((n2w m):bool **'a = n2w n) = (m MOD ^TOP = n MOD ^TOP)`,
  NTAC 2 STRIP_TAC
    THEN STRIP_ASSUME_TAC EXISTS_HB
    THEN ASM_SIMP_TAC (fcp_ss++WORD_ss) [GSYM BITS_ZERO3]
    THEN EQ_TAC THEN RW_TAC arith_ss [DECIDE ``i < SUC p = i <= p``]
    THEN PROVE_TAC [(REWRITE_RULE [ZERO_LESS_EQ] o SPECL [`p`,`0`]) BIT_BITS_THM]
);

val w2n_11 = store_thm("w2n_11",
  `!v w. (w2n v = w2n w) = (v = w)`,
  REPEAT Cases_word
    THEN REWRITE_TAC [w2n_n2w,n2w_11]);

val w2n_lt = store_thm("w2n_lt",
  `!w:bool ** 'a. w2n w < ^TOP`,
  SIMP_TAC std_ss [w2n_def,SUM_SBIT_LT]);

val word_add_n2w = store_thm("word_add_n2w",
  `!m n. n2w m + n2w n = n2w (m + n)`,
  SIMP_TAC fcp_ss [word_add_def,w2n_n2w] THEN ONCE_REWRITE_TAC [GSYM n2w_mod]
    THEN SIMP_TAC arith_ss [MOD_PLUS,ZERO_LT_TWOEXP]);

val word_mul_n2w = store_thm("word_mul_n2w",
  `!m n. n2w m * n2w n = n2w (m * n)`,
  SIMP_TAC fcp_ss [word_mul_def,w2n_n2w] THEN ONCE_REWRITE_TAC [GSYM n2w_mod]
    THEN SIMP_TAC arith_ss [MOD_TIMES2,ZERO_LT_TWOEXP]);

val word_log2_n2w = store_thm("word_log2_n2w",
  `!n. word_log2 (n2w n):bool ** 'a = (n2w (LOG2 (n MOD ^TOP))):bool ** 'a`,
  SIMP_TAC fcp_ss [word_log2_def,w2n_n2w]);

val top = ``2 ** wl``;

val BITWISE_ONE_COMP_THM = prove(
  `!wl a b. 0 < wl ==>
     (BITWISE wl (\x y. ~x) a b = ^top - 1 - a MOD ^top)`,
  REPEAT STRIP_TAC
    THEN `?b. wl = SUC b` by PROVE_TAC [LESS_ADD_1,ADD1,ADD]
    THEN ASM_SIMP_TAC bool_ss [BITWISE_ONE_COMP_LEM,BITS_ZERO3]);

val ONE_COMP_THM = prove(
  `!wl a x. 0 < wl /\ x < wl ==> (BIT x (^top - 1 - a MOD ^top) = ~BIT x a)`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC (GSYM BITWISE_ONE_COMP_THM)
    THEN ASM_REWRITE_TAC []
    THEN ASM_SIMP_TAC bool_ss [BITWISE_THM]);

val word_1comp_n2w = store_thm("word_1comp_n2w",
  `!n. ~(n2w n):bool ** 'a  = (n2w (^TOP - 1 - n MOD ^TOP)):bool ** 'a`,
  RW_TAC fcp_ss [word_1comp_def,n2w_def,ONE_COMP_THM,DIMINDEX_GT_0]);

val word_2comp_n2w = store_thm("word_2comp_n2w",
  `!n. $- (n2w n):bool ** 'a  = (n2w (^TOP - n MOD ^TOP)):bool ** 'a`,
  SIMP_TAC std_ss [word_2comp_def,n2w_11,w2n_n2w]);

val word_lsb_n2w = store_thm("word_lsb_n2w",
  `!n. word_lsb ((n2w n):bool ** 'a)  = BIT 0 n`,
  SIMP_TAC fcp_ss [word_lsb_def,n2w_def,DIMINDEX_GT_0]);

val word_msb_n2w = store_thm("word_msb_n2w",
  `!n. word_msb ((n2w n):bool ** 'a)  = BIT ^HB n`,
  SIMP_TAC (fcp_ss++ARITH_ss) [word_msb_def,n2w_def,DIMINDEX_GT_0]);

val word_and_n2w = store_thm("word_and_n2w",
  `!n m. (n2w n):bool ** 'a && (n2w m) = n2w (BITWISE ^WL (/\) n m)`,
  SIMP_TAC fcp_ss [word_and_def,n2w_11,n2w_def,BITWISE_THM]);

val word_or_n2w = store_thm("word_or_n2w",
  `!n m. (n2w n):bool ** 'a !! (n2w m) = n2w (BITWISE ^WL (\/) n m)`,
  SIMP_TAC fcp_ss [word_or_def,n2w_11,n2w_def,BITWISE_THM]);

val word_xor_n2w = store_thm("word_xor_n2w",
  `!n m. (n2w n):bool ** 'a ?? (n2w m) = n2w (BITWISE ^WL (\x y. ~(x = y)) n m)`,
  SIMP_TAC fcp_ss [word_xor_def,n2w_11,n2w_def,BITWISE_THM]);

(* ------------------------------------------------------------------------- *)
(*  The Boolean operations : theorems                                        *)
(* ------------------------------------------------------------------------- *)

val ONE_COMP_0_THM =
  (SIMP_RULE arith_ss [BIT_ZERO,ZERO_MOD,ZERO_LT_TWOEXP] o
   SPECL [`wl`,`0`]) ONE_COMP_THM;

val word_0 = store_thm("word_0",
  `!i. i < ^WL ==> ~((0w:bool ** 'a) %% i)`,
  SIMP_TAC fcp_ss [n2w_def,BIT_ZERO]);

val word_T = store_thm("word_T",
  `!i. i < ^WL ==> (Tw:bool ** 'a) %% i`,
  SIMP_TAC fcp_ss [word_T_def,n2w_def,ONE_COMP_0_THM,DIMINDEX_GT_0]);

val WORD_ss =
  rewrites [word_1comp_def,word_and_def,word_or_def,word_xor_def,
    word_0,word_T];

val BOOL_WORD_TAC = SIMP_TAC (fcp_ss++WORD_ss) [] THEN DECIDE_TAC;

val WORD_NOT_NOT = store_thm("WORD_NOT_NOT",
  `!a:bool ** 'a. ~(~a) = a`, BOOL_WORD_TAC);

val WORD_DE_MORGAN_THM = store_thm("WORD_DE_MORGAN_THM",
  `!a b. ~(a && b) = ~a !! ~b`, BOOL_WORD_TAC);

val WORD_DE_MORGAN_THM = store_thm("WORD_DE_MORGAN_THM",
  `!a b. ~(a && b) = ~a !! ~b`, BOOL_WORD_TAC);

val WORD_AND_CLAUSES = store_thm("WORD_AND_CLAUSES",
  `!a:bool ** 'a.
      (Tw && a = a) /\ (a && Tw = a) /\
      (0w && a = 0w) /\ (a && 0w = 0w) /\
      (a && a = a)`, BOOL_WORD_TAC);

val WORD_OR_CLAUSES = store_thm("WORD_OR_CLAUSES",
  `!a:bool ** 'a.
      (Tw !! a = Tw) /\ (a !! Tw = Tw) /\
      (0w !! a = a) /\ (a !! 0w = a) /\
      (a !! a = a)`, BOOL_WORD_TAC);

val WORD_XOR_CLAUSES = store_thm("WORD_XOR_CLAUSES",
  `!a:bool ** 'a.
      (Tw ?? a = ~a) /\ (a ?? Tw = ~a) /\
      (0w ?? a = a) /\ (a ?? 0w = a) /\
      (a ?? a = 0w)`, BOOL_WORD_TAC);

val WORD_AND_ASSOC = store_thm("WORD_AND_ASSOC",
  `!a b c. (a && b) && c = a && b && c`, BOOL_WORD_TAC);

val WORD_OR_ASSOC = store_thm("WORD_OR_ASSOC",
  `!a b c. (a !! b) !! c = a !! b !! c`, BOOL_WORD_TAC);

val WORD_XOR_ASSOC = store_thm("WORD_XOR_ASSOC",
  `!a b c. (a ?? b) ?? c = a ?? b ?? c`, BOOL_WORD_TAC);

val WORD_AND_COMM = store_thm("WORD_AND_COMM",
  `!a b. a && b = b && a`, BOOL_WORD_TAC);

val WORD_OR_COMM = store_thm("WORD_OR_COMM",
  `!a b. a !! b = b !! a`, BOOL_WORD_TAC);

val WORD_XOR_COMM = store_thm("WORD_XOR_COMM",
  `!a b. a ?? b = b ?? a`, BOOL_WORD_TAC);

val WORD_AND_IDEM = store_thm("WORD_AND_IDEM",
  `!a. a && a = a`, BOOL_WORD_TAC);

val WORD_OR_IDEM = store_thm("WORD_OR_IDEM",
  `!a. a !! a = a`, BOOL_WORD_TAC);

val WORD_AND_ABSORD = store_thm("WORD_AND_ABSORD",
  `!a b. a !! a && b = a`, BOOL_WORD_TAC);

val WORD_OR_ABSORB = store_thm("WORD_OR_ABSORB",
  `!a b. a && (a !! b) = a`, BOOL_WORD_TAC);

val WORD_AND_COMP = store_thm("WORD_AND_COMP",
  `!a. a && ~a = 0w`, BOOL_WORD_TAC);

val WORD_OR_COMP = store_thm("WORD_OR_COMP",
  `!a. a !! ~a = Tw`, BOOL_WORD_TAC);

val WORD_XOR_COMP = store_thm("WORD_XOR_COMP",
  `!a. a ?? ~a = Tw`, BOOL_WORD_TAC);

val WORD_RIGHT_AND_OVER_OR = store_thm("WORD_RIGHT_AND_OVER_OR",
  `!a b c. (a !! b) && c = a && c !! b && c`, BOOL_WORD_TAC);

val WORD_RIGHT_OR_OVER_AND = store_thm("WORD_RIGHT_OR_OVER_AND",
  `!a b c. (a && b) !! c = (a !! c) && (b !! c)`, BOOL_WORD_TAC);

val WORD_XOR = store_thm("WORD_XOR",
  `!a b. a ?? b = a && ~b !! b && ~a`, BOOL_WORD_TAC);

(* ------------------------------------------------------------------------- *)
(*  Bit field operations : theorems                                          *)
(* ------------------------------------------------------------------------- *)

val WORD_ss = rewrites [word_slice_def,word_bits_def,word_bit_def,
  word_lsl_def,word_lsr_def,word_and_def,word_or_def,word_xor_def,
  word_reverse_def,word_modify_def,n2w_def,SUC_SUB1,BIT_SLICE_THM4];

val FIELD_WORD_TAC = RW_TAC (fcp_ss++WORD_ss++ARITH_ss) [];

val word_slice_n2w = store_thm("word_slice_n2w",
  `!h l n. (h <> l) (n2w n):bool ** 'a =
             (n2w (SLICE (MIN h ^HB) l n)):bool ** 'a`,
  FIELD_WORD_TAC);

val word_bits_n2w = store_thm("word_bits_n2w",
  `!h l n. (h -- l) (n2w n):bool ** 'a =
             (n2w (BITS (MIN h ^HB) l n)):bool ** 'a`,
  FIELD_WORD_TAC THEN Cases_on `i + l <= MIN h ^HB`
    THEN FULL_SIMP_TAC (fcp_ss++ARITH_ss) [MIN_DEF,NOT_LESS_EQUAL,
           BIT_OF_BITS_THM,BIT_OF_BITS_THM2]);

val word_bit_n2w = store_thm("word_bit_n2w",
  `!b n. word_bit b ((n2w n):bool ** 'a) = b <= ^HB /\ BIT b n`,
  FIELD_WORD_TAC THEN Cases_on `b <= ^HB`
    THEN ASM_SIMP_TAC fcp_ss [DIMINDEX_GT_0,
           DECIDE ``0 < b /\ a <= b - 1 ==> a < b:num``]);

val word_reverse_n2w = store_thm("word_reverse_n2w",
  `!n. word_reverse ((n2w n):bool ** 'a) =
         (n2w (BIT_REVERSE ^WL n)):bool ** 'a`,
  FIELD_WORD_TAC THEN ASM_SIMP_TAC arith_ss [BIT_REVERSE_THM]);

val word_modify_n2w = store_thm("word_modify_n2w",
  `!f n. word_modify f ((n2w n):bool ** 'a) =
         (n2w (BIT_MODIFY ^WL f n)):bool ** 'a`,
  FIELD_WORD_TAC THEN ASM_SIMP_TAC arith_ss [BIT_MODIFY_THM]);

val WORD_EQ = store_thm("WORD_EQ",
  `!v:bool ** 'a w. (!x. x < ^WL ==> (word_bit x v = word_bit x w)) = (v = w)`,
  REPEAT Cases_word THEN FIELD_WORD_TAC);

val TWO_EXP_DIMINDEX =
  (SIMP_RULE arith_ss [DIMINDEX_GE_1] o SPECL [`1`,`^WL`]) TWOEXP_MONO2;

val lem = GEN_ALL (MATCH_MP LESS_LESS_EQ_TRANS (CONJ
  ((REWRITE_RULE [SUC_SUB,EXP_1] o SPECL [`b`,`b`,`n`]) BITSLT_THM)
  TWO_EXP_DIMINDEX));

val lem2 = GEN_ALL (MATCH_MP LESS_LESS_EQ_TRANS (CONJ
   (DECIDE ``1 < 2``) TWO_EXP_DIMINDEX));

val WORD_BIT_BITS = store_thm("WORD_BIT_BITS",
  `!b w. word_bit b w = ((b -- b) w = 1w)`,
  STRIP_TAC THEN Cases_word
    THEN RW_TAC arith_ss [MIN_DEF,BIT_def,word_bit_n2w,word_bits_n2w,n2w_11,
           LESS_MOD,lem,lem2]
    THEN STRIP_ASSUME_TAC EXISTS_HB
    THEN FULL_SIMP_TAC arith_ss [MIN_DEF,GSYM BITS_ZERO3,SUC_SUB1,BITS_COMP_THM2]
    THEN Cases_on `b = 0` THEN FULL_SIMP_TAC arith_ss []
    THENL [`m = 0` by DECIDE_TAC THEN ASM_REWRITE_TAC [],
      Cases_on `m = b` THEN ASM_SIMP_TAC arith_ss [BITS_ZERO]]);

val lem = prove(`MIN d (l1 + MIN h2 d) = MIN (h2 + l1) d`,
  RW_TAC arith_ss [MIN_DEF]);

val WORD_BITS_COMP_THM = store_thm("WORD_BITS_COMP_THM",
  `!h1 l1 h2 l2 w. (h2 -- l2) ((h1 -- l1) w) =
                   ((MIN h1 (h2 + l1)) -- (l2 + l1)) w`,
  REPEAT STRIP_TAC THEN Cases_on_word `w`
    THEN RW_TAC arith_ss [word_bits_n2w,lem,BITS_COMP_THM2,
           AC MIN_ASSOC MIN_COMM]);

val WORD_BITS_LSR = store_thm("WORD_BITS_LSR",
  `!h l w. (h -- l) w >>> n = (h -- (l + n)) w`,
  FIELD_WORD_TAC THEN Cases_on `i + n < dimindex (UNIV:'a->bool)`
    THEN ASM_SIMP_TAC (fcp_ss++ARITH_ss) []);

val WORD_BITS_ZERO = store_thm("WORD_BITS_ZERO",
  `!h l w. h < l ==> ((h -- l) w = 0w)`,
  NTAC 2 STRIP_TAC THEN Cases_word
    THEN RW_TAC arith_ss [word_bits_n2w,BITS_ZERO,MIN_DEF]);

val WORD_BITS_LT = store_thm("WORD_BITS_LT",
  `!h l w. w2n ((h -- l) w) < 2 ** (SUC h - l)`,
  NTAC 2 STRIP_TAC THEN Cases_word
    THEN STRIP_ASSUME_TAC EXISTS_HB
    THEN RW_TAC arith_ss [word_bits_n2w,w2n_n2w,GSYM BITS_ZERO3,
           BITS_COMP_THM2,MIN_DEF,BITSLT_THM]
    THEN FULL_SIMP_TAC std_ss []
    THENL [`SUC m - l <= SUC h - l` by DECIDE_TAC,
     `SUC (l + m) - l <= SUC h - l` by DECIDE_TAC]
    THEN PROVE_TAC [TWOEXP_MONO2,BITSLT_THM,LESS_LESS_EQ_TRANS]);

val WORD_SLICE_THM = store_thm("WORD_SLICE_THM",
  `!h l w. (h <> l) w = (h -- l) w << l`,
  FIELD_WORD_TAC THEN Cases_on `l <= i` THEN ASM_SIMP_TAC arith_ss []);

val WORD_SLICE_ZERO = store_thm("WORD_SLICE_ZERO",
  `!h l w. h < l ==> ((h <> l) w = 0w)`,
  NTAC 2 STRIP_TAC THEN Cases_word
    THEN RW_TAC arith_ss [word_slice_n2w,SLICE_ZERO,MIN_DEF]);

val WORD_SLICE_BITS_THM = store_thm("WORD_SLICE_BITS_THM",
  `!h w. (h <> 0) w = (h -- 0) w`, FIELD_WORD_TAC);

val WORD_BITS_SLICE_THM = store_thm("WORD_BITS_SLICE_THM",
  `!h l w. (h -- l) ((h <> l) w) = (h -- l) w`,
  NTAC 2 STRIP_TAC THEN Cases_word
    THEN RW_TAC arith_ss [word_slice_n2w,word_bits_n2w,BITS_SLICE_THM]);

val WORD_SLICE_COMP_THM = store_thm("WORD_SLICE_COMP_THM",
  `!h m' m l w:bool ** 'a. l <= m /\ (m' = m + 1) /\ m < h ==>
     (((h <> m') w):bool ** 'a !! (m <> l) w =
      ((h <> l) w):bool ** 'a)`,
  FIELD_WORD_TAC THEN `i <= m \/ m + 1 <= i` by DECIDE_TAC
    THEN ASM_SIMP_TAC arith_ss []);

val WORD_SLICE_OVER_BITWISE = store_thm("WORD_SLICE_OVER_BITWISE",
  `(!h l v:bool ** 'a w:bool ** 'a.
      (h <> l) v && (h <> l) w = (h <> l) (v && w)) /\
   (!h l v:bool ** 'a w:bool ** 'a.
      (h <> l) v !! (h <> l) w = (h <> l) (v !! w)) /\
   (!h l v:bool ** 'a w:bool ** 'a.
      (h <> l) v ?? (h <> l) w = (h <> l) (v ?? w))`,
  FIELD_WORD_TAC THENL [PROVE_TAC [], PROVE_TAC [], ALL_TAC]
    THEN Cases_on `l <= i /\ i <= h` THEN FULL_SIMP_TAC arith_ss []);

val WORD_BITS_OVER_BITWISE = store_thm("WORD_BITS_OVER_BITWISE",
  `(!h l v:bool ** 'a w:bool ** 'a.
      (h -- l) v && (h -- l) w = (h -- l) (v && w)) /\
   (!h l v:bool ** 'a w:bool ** 'a.
      (h -- l) v !! (h -- l) w = (h -- l) (v !! w)) /\
   (!h l v:bool ** 'a w:bool ** 'a.
      (h -- l) v ?? (h -- l) w = (h -- l) (v ?? w))`,
  FIELD_WORD_TAC
    THEN Cases_on `i + l <= h /\ i + l <= dimindex (UNIV:'a->bool) - 1`
    THEN FULL_SIMP_TAC (fcp_ss++ARITH_ss) []);

(* ------------------------------------------------------------------------- *)
(*  Word arithmetic: theorems                                                *)
(* ------------------------------------------------------------------------- *)

val _ = set_fixity "==" (Infixr 450);

val equiv = ``\x y. x MOD ^top = y MOD ^top``;

val lift_rule = REWRITE_RULE [GSYM n2w_11] o INST [`wl` |-> `^WL`];
val LET_RULE = CONV_RULE (DEPTH_CONV pairLib.let_CONV);
val LET_TAC = CONV_TAC (DEPTH_CONV pairLib.let_CONV);

val MOD_ADD = (REWRITE_RULE [ZERO_LT_TWOEXP] o SPEC `^top`) MOD_PLUS;
val ONE_LT_EQ_TWOEXP = REWRITE_RULE [SYM ONE,LESS_EQ] ZERO_LT_TWOEXP;

val SUC_EQUIV_mod = LET_RULE (prove(
  `!a b. let $== = ^equiv in
           SUC a == b ==> a == (b + (^top - 1))`,
  LET_TAC THEN REPEAT STRIP_TAC
    THEN ONCE_REWRITE_TAC [GSYM MOD_ADD]
    THEN POP_ASSUM (fn th => REWRITE_TAC [SYM th])
    THEN SIMP_TAC std_ss [MOD_ADD,ADD1,GSYM LESS_EQ_ADD_SUB,ONE_LT_EQ_TWOEXP]
    THEN SIMP_TAC arith_ss [ADD_MODULUS,ZERO_LT_TWOEXP]));

val INV_SUC_EQ_mod = LET_RULE (prove(
  `!m n. let $== = ^equiv in
           (SUC m == SUC n) = (m == n)`,
  LET_TAC THEN REPEAT STRIP_TAC THEN EQ_TAC THENL [
    STRIP_TAC THEN IMP_RES_TAC SUC_EQUIV_mod
      THEN FULL_SIMP_TAC arith_ss [GSYM LESS_EQ_ADD_SUB,ADD1,ADD_MODULUS,
             ZERO_LT_TWOEXP,ONE_LT_EQ_TWOEXP],
    REWRITE_TAC [ADD1] THEN ONCE_REWRITE_TAC [GSYM MOD_ADD]
      THEN RW_TAC std_ss []]));

val ADD_INV_0_mod = LET_RULE (prove(
  `!m n. let $== = ^equiv in
           (m + n == m) ==> (n == 0)`,
  LET_TAC THEN Induct THEN RW_TAC bool_ss [ADD_CLAUSES]
    THEN FULL_SIMP_TAC bool_ss [INV_SUC_EQ_mod]));

val ADD_INV_0_EQ_mod = LET_RULE (prove(
  `!m n. let $== = ^equiv in
           (m + n == m) = (n == 0)`,
  LET_TAC THEN REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC
    THEN IMP_RES_TAC ADD_INV_0_mod
    THEN ONCE_REWRITE_TAC [GSYM MOD_ADD]
    THEN ASM_SIMP_TAC arith_ss [ZERO_MOD,ADD_MODULUS,ZERO_LT_TWOEXP]));

val EQ_ADD_LCANCEL_mod = LET_RULE (prove(
  `!m n p. let $== = ^equiv in
           (m + n == m + p) = (n == p)`,
  LET_TAC THEN Induct THEN ASM_REWRITE_TAC [ADD_CLAUSES,INV_SUC_EQ_mod]));

val WORD_NEG_mod = LET_RULE (prove(
  `!n. let $== = ^equiv in
         ^top - n MOD ^top == (^top - 1 - n MOD ^top) + 1`,
  LET_TAC THEN STRIP_TAC
    THEN `1 + n MOD ^top <= ^top`
      by SIMP_TAC std_ss [DECIDE ``a < b ==> 1 + a <= b``,MOD_2EXP_LT]
    THEN ASM_SIMP_TAC arith_ss [SUB_RIGHT_SUB,SUB_RIGHT_ADD]
    THEN Tactical.REVERSE (Cases_on `1 + n MOD ^top = ^top`)
    THEN1 FULL_SIMP_TAC arith_ss []
    THEN RULE_ASSUM_TAC
         (SIMP_RULE bool_ss [GSYM SUC_ONE_ADD,GSYM PRE_SUC_EQ,ZERO_LT_TWOEXP])
    THEN ASM_SIMP_TAC arith_ss [PRE_SUB1]));

val n2w_TOP = prove(
  `n2w ^TOP = 0w:bool ** 'a`,
  ONCE_REWRITE_TAC [GSYM n2w_mod]
    THEN SIMP_TAC std_ss [DIVMOD_ID,ZERO_MOD,ZERO_LT_TWOEXP]);

val WORD_ss = rewrites [word_add_n2w,word_mul_n2w,word_sub_def,word_2comp_def,
  w2n_n2w,n2w_w2n,word_0,n2w_TOP,ZERO_LT_TWOEXP,
  LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB,
  LEFT_SUB_DISTRIB,RIGHT_SUB_DISTRIB];

val ARITH_WORD_TAC =
  REPEAT Cases_word
    THEN ASM_SIMP_TAC (fcp_ss++ARITH_ss++numSimps.ARITH_AC_ss++WORD_ss) [];

(* -- *)

val WORD_ADD_0 = store_thm("WORD_ADD_0",
  `(!w:bool ** 'a. w + 0w = w) /\ (!w:bool ** 'a. 0w + w = w)`,
   CONJ_TAC THEN ARITH_WORD_TAC);

val WORD_ADD_ASSOC = store_thm("WORD_ADD_ASSOC",
  `!v:bool ** 'a w x. v + (w + x) = v + w + x`, ARITH_WORD_TAC);

val WORD_MULT_ASSOC = store_thm("WORD_MULT_ASSOC",
  `!v:bool ** 'a w x. v * (w * x) = v * w * x`, ARITH_WORD_TAC);

val WORD_ADD_COMM = store_thm("WORD_ADD_COMM",
  `!v:bool ** 'a w. v + w = w + v`, ARITH_WORD_TAC);

val WORD_MULT_COMM = store_thm("WORD_MULT_COMM",
  `!v:bool ** 'a w. v * w = w * v`, ARITH_WORD_TAC);

val WORD_MULT_CLAUSES = store_thm("WORD_MULT_CLAUSES",
  `!v:bool ** 'a w.
     (0w * v = 0w) /\ (v * 0w = 0w) /\
     (1w * v = v) /\ (v * 1w = v) /\
     ((v + 1w) * w = v * w + w) /\ (v * (w + 1w) = v + v * w)`,
  ARITH_WORD_TAC);

val WORD_LEFT_ADD_DISTRIB = store_thm("WORD_LEFT_ADD_DISTRIB",
  `!v:bool ** 'a w x. v * (w + x) = v * w + v * x`, ARITH_WORD_TAC);

val WORD_RIGHT_ADD_DISTRIB = store_thm("WORD_RIGHT_ADD_DISTRIB",
  `!v:bool ** 'a w x. (v + w) * x = v * x + w * x`, ARITH_WORD_TAC);

val WORD_ADD_SUB_ASSOC = store_thm("WORD_ADD_SUB_ASSOC",
  `!v:bool ** 'a w x. v + w - x = v + (w - x)`, ARITH_WORD_TAC);

val WORD_ADD_SUB_SYM = store_thm("WORD_ADD_SUB_SYM",
  `!v:bool ** 'a w x. v + w - x = v - x + w`, ARITH_WORD_TAC);

val WORD_ADD_LINV = store_thm("WORD_ADD_LINV",
  `!w:bool ** 'a. $- w + w = 0w`,
  ARITH_WORD_TAC
    THEN STRIP_ASSUME_TAC ((REWRITE_RULE [ZERO_LT_TWOEXP] o SPECL [`n`,`^TOP`]) DA)
    THEN ASM_SIMP_TAC std_ss [MOD_MULT]
    THEN ONCE_REWRITE_TAC [GSYM n2w_mod]
    THEN ASM_SIMP_TAC arith_ss [GSYM MULT,MOD_EQ_0,ZERO_LT_TWOEXP,word_0]);

val WORD_ADD_RINV = store_thm("WORD_ADD_RINV",
  `!w:bool ** 'a. w + $- w = 0w`,
  METIS_TAC [WORD_ADD_COMM,WORD_ADD_LINV]);

val WORD_SUB_REFL = store_thm("WORD_SUB_REFL",
  `!w:bool ** 'a. w - w = 0w`,
  REWRITE_TAC [word_sub_def,WORD_ADD_RINV]);

val WORD_SUB_ADD2 = store_thm("WORD_SUB_ADD2",
  `!v:bool ** 'a w. v + (w - v) = w`,
  REWRITE_TAC [GSYM WORD_ADD_SUB_ASSOC,WORD_ADD_SUB_SYM,
    WORD_SUB_REFL,WORD_ADD_0]);

val WORD_ADD_SUB = store_thm("WORD_ADD_SUB",
  `!v:bool ** 'a w. v + w - w = v`,
  REWRITE_TAC [WORD_ADD_SUB_ASSOC,WORD_SUB_REFL,WORD_ADD_0]);

val WORD_SUB_ADD = save_thm("WORD_SUB_ADD",
  REWRITE_RULE [WORD_ADD_SUB_SYM] WORD_ADD_SUB);

val WORD_ADD_EQ_SUB = store_thm("WORD_ADD_EQ_SUB",
  `!v:bool ** 'a w x. (v + w = x) = (v = (x - w))`,
  METIS_TAC [WORD_ADD_SUB,WORD_SUB_ADD]);

val WORD_ADD_INV_0_EQ = store_thm("WORD_ADD_INV_0_EQ",
  `!v:bool ** 'a w. (v + w = v) = (w = 0w)`,
  REPEAT Cases_word
    THEN ASM_SIMP_TAC std_ss [word_add_n2w,lift_rule ADD_INV_0_EQ_mod]);

val WORD_EQ_ADD_LCANCEL = store_thm("WORD_EQ_ADD_LCANCEL",
  `!v:bool ** 'a w x. (v + w = v + x) = (w = x)`,
  REPEAT Cases_word
    THEN ASM_SIMP_TAC std_ss [word_add_n2w,lift_rule EQ_ADD_LCANCEL_mod]);

val WORD_EQ_ADD_RCANCEL = store_thm("WORD_EQ_ADD_RCANCEL",
  `!v:bool ** 'a w x. (v + w = x + w) = (v = x)`,
  METIS_TAC [WORD_ADD_COMM,WORD_EQ_ADD_LCANCEL]);

val WORD_NEG = store_thm("WORD_NEG",
  `!w:bool ** 'a. $- w = ~w + 1w`,
  REPEAT Cases_word
    THEN ASM_SIMP_TAC (fcp_ss++ARITH_ss) [word_add_n2w,word_2comp_n2w,
           word_1comp_n2w,lift_rule WORD_NEG_mod]);

val WORD_NOT = store_thm("WORD_NOT",
  `!w:bool ** 'a. ~w = $- w - 1w`,
  REWRITE_TAC [WORD_NEG,WORD_ADD_SUB]);

val WORD_NEG_0 = store_thm("WORD_NEG_0",
  `$- 0w = 0w`,
   ARITH_WORD_TAC);

val WORD_NEG_ADD = store_thm("WORD_NEG_ADD",
  `!v:bool ** 'a w. $- (v + w) = $- v + $- w`,
  REPEAT STRIP_TAC
    THEN `$- v + v + ($-w + w) = 0w`
      by REWRITE_TAC [WORD_ADD_LINV,WORD_ADD_0]
    THEN `$- v + v + ($-w + w) = $- v + $- w + (v + w)`
      by SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]
    THEN METIS_TAC [GSYM WORD_ADD_LINV,WORD_EQ_ADD_RCANCEL]);

val WORD_NEG_NEG = store_thm("WORD_NEG_NEG",
  `!w:bool ** 'a. $- ($- w) = w`,
  STRIP_TAC
     THEN `$- ($- w) + $- w = w + $- w`
       by SIMP_TAC std_ss [WORD_NEG_0,WORD_ADD_0,WORD_ADD_LINV,WORD_ADD_RINV]
     THEN METIS_TAC [WORD_EQ_ADD_RCANCEL]);

val WORD_SUB_LNEG = save_thm("WORD_SUB_LNEG",
  (REWRITE_RULE [GSYM word_sub_def] o GSYM) WORD_NEG_ADD);

val WORD_SUB_RNEG = save_thm("WORD_SUB_RNEG",
  (GEN `v` o GEN `w` o REWRITE_RULE [WORD_NEG_NEG] o
   SPECL [`v`,`$- w`]) word_sub_def);

val WORD_SUB_SUB = store_thm("WORD_SUB_SUB",
  `!v:bool ** 'a w x. v - (w - x) = v + x - w`,
  SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM,
    word_sub_def,WORD_NEG_ADD,WORD_NEG_NEG]);

val WORD_SUB_SUB2 = save_thm("WORD_SUB_SUB2",
 (GEN `v` o GEN `w` o REWRITE_RULE [WORD_ADD_SUB_SYM,WORD_SUB_REFL,WORD_ADD_0] o
  SPECL [`v`,`v`,`w`]) WORD_SUB_SUB);

val WORD_EQ_SUB_LADD = store_thm("WORD_EQ_SUB_LADD",
  `!v:bool ** 'a w x. (v = w - x) = (v + x = w)`,
  METIS_TAC [word_sub_def,WORD_ADD_ASSOC,WORD_ADD_LINV,WORD_ADD_RINV,WORD_ADD_0]);

val WORD_EQ_SUB_RADD = store_thm("WORD_EQ_SUB_RADD",
  `!v:bool ** 'a w x. (v - w = x) = (v = x + w)`,
  METIS_TAC [WORD_EQ_SUB_LADD]);

val WORD_LCANCEL_SUB = store_thm("WORD_LCANCEL_SUB",
  `!v:bool ** 'a w x. (v - w = x - w) = (v = x)`,
  REWRITE_TAC [word_sub_def,WORD_EQ_ADD_RCANCEL]);

val WORD_RCANCEL_SUB = store_thm("WORD_RCANCEL_SUB",
  `!v:bool ** 'a w x. (v - w = v - x) = (w = x)`,
  REWRITE_TAC [word_sub_def,WORD_EQ_ADD_LCANCEL]
    THEN METIS_TAC [WORD_NEG_NEG]);

val WORD_SUB_PLUS = store_thm("WORD_SUB_PLUS",
  `!v:bool ** 'a w x. v - (w + x) = v - w - x`,
  REWRITE_TAC [word_sub_def,WORD_NEG_ADD,WORD_ADD_ASSOC]);

val WORD_SUB_LZERO = store_thm("WORD_SUB_LZERO",
  `!w:bool ** 'a. 0w - w = $- w`,
  REWRITE_TAC [word_sub_def,WORD_ADD_0]);

val WORD_SUB_RZERO = store_thm("WORD_SUB_RZERO",
  `!w:bool ** 'a. w - 0w = w`,
  REWRITE_TAC [word_sub_def,WORD_ADD_0,WORD_NEG_0]);

val WORD_ADD_LID_UNIQ = save_thm("WORD_ADD_LID_UNIQ",
  (GEN `v` o GEN `w` o REWRITE_RULE [WORD_SUB_REFL] o
    SPECL [`v`,`w`,`w`]) WORD_ADD_EQ_SUB);

val WORD_ADD_RID_UNIQ = save_thm("WORD_ADD_RID_UNIQ",
  (GEN `v` o GEN `w` o ONCE_REWRITE_RULE [WORD_ADD_COMM] o
   SPECL [`w`,`v`]) WORD_ADD_LID_UNIQ);

val WORD_ADD_SUB2 = save_thm("WORD_ADD_SUB2",
  ONCE_REWRITE_RULE [WORD_ADD_COMM] WORD_ADD_SUB);

val WORD_ADD_SUB3 = save_thm("WORD_ADD_SUB3",
  (GEN_ALL o REWRITE_RULE [WORD_SUB_REFL,WORD_SUB_LZERO] o
   SPECL [`v`,`v`]) WORD_SUB_PLUS);

val WORD_SUB_SUB3 = save_thm("WORD_SUB_SUB3",
  (REWRITE_RULE [WORD_ADD_SUB3] o ONCE_REWRITE_RULE [WORD_ADD_COMM] o
   SPECL [`v`,`w`,`v`] o GSYM) WORD_SUB_PLUS);

val WORD_EQ_NEG = store_thm("WORD_EQ_NEG",
  `!v:bool ** 'a w. ($- v = $- w) = (v = w)`,
  REWRITE_TAC [GSYM WORD_SUB_LZERO,WORD_RCANCEL_SUB]);

val WORD_NEG_EQ = save_thm("WORD_NEG_EQ",
  (REWRITE_RULE [WORD_NEG_NEG] o SPECL [`v`,`$- w`]) WORD_EQ_NEG);

val WORD_NEG_EQ_0 = save_thm("WORD_NEG_EQ_0",
  (REWRITE_RULE [WORD_NEG_0] o SPECL [`v`,`0w`]) WORD_EQ_NEG);

val WORD_SUB = save_thm("WORD_SUB",
  (ONCE_REWRITE_RULE [WORD_ADD_COMM] o GSYM) word_sub_def);

val WORD_SUB_NEG = save_thm("WORD_SUB_NEG",
  (GEN_ALL o REWRITE_RULE [WORD_SUB] o SPEC `$- v`) WORD_SUB_RNEG);

val WORD_NEG_SUB = save_thm("WORD_NEG_SUB",
  (REWRITE_RULE [WORD_SUB_NEG,GSYM word_sub_def] o
   SPECL [`v`,`$- w`] o GSYM) WORD_SUB_LNEG);

val WORD_SUB_TRIANGLE = store_thm("WORD_SUB_TRIANGLE",
  `!v:bool ** 'a w x. v - w + (w - x) = v - x`,
  REWRITE_TAC [GSYM WORD_ADD_SUB_SYM,WORD_ADD_SUB_ASSOC,WORD_SUB_SUB3]
    THEN REWRITE_TAC [word_sub_def]);

val WORD_NEG_1 = store_thm("WORD_NEG_1",
  `$- 1w:bool ** 'a = Tw:bool ** 'a`,
  REWRITE_TAC [word_T_def,word_2comp_def,w2n_n2w]
    THEN Cases_on `2 ** dimindex (UNIV:'a->bool) = 1`
    THEN1 ASM_SIMP_TAC arith_ss [n2w_11]
    THEN ASM_SIMP_TAC arith_ss [DECIDE ``0 < x /\ ~(x = 1) ==> 1 < x``,
           LESS_MOD,ZERO_LT_TWOEXP]);

val WORD_NOT_0 = save_thm("WORD_NOT_0",
  (GEN_ALL o REWRITE_RULE [WORD_NEG_1,WORD_NEG_0,WORD_SUB_LZERO] o
   SPEC `0w`) WORD_NOT);

val WORD_NOT_T = store_thm("WORD_NOT_T",
  `~Tw = 0w`, REWRITE_TAC [GSYM WORD_NOT_0,WORD_NOT_NOT]);

val WORD_NEG_T = store_thm("WORD_NEG_T",
  `$- Tw = 1w`, REWRITE_TAC [GSYM WORD_NEG_1,WORD_NEG_NEG]);

val WORD_MULT_SUC  = store_thm("WORD_MULT_SUC",
  `!v:bool ** 'a n. v * n2w (n + 1) = v * n2w n + v`,
  Cases_word THEN
    SIMP_TAC arith_ss [word_mul_n2w,word_add_n2w,LEFT_ADD_DISTRIB]);

val WORD_NEG_LMUL = store_thm("WORD_NEG_LMUL",
  `!v:bool ** 'a w. $- (v * w) = ($- v) * w`,
  REPEAT Cases_word
    THEN Induct_on `n'` THEN1 REWRITE_TAC [WORD_MULT_CLAUSES,WORD_NEG_0]
    THEN ASM_REWRITE_TAC [WORD_NEG_ADD,ADD1,WORD_MULT_SUC,GSYM word_mul_n2w]);

val WORD_NEG_RMUL = save_thm("WORD_NEG_RMUL",
  (GEN `v` o GEN `w` o ONCE_REWRITE_RULE [WORD_MULT_COMM] o
    SPECL [`w`,`v`]) WORD_NEG_LMUL);

val WORD_LEFT_SUB_DISTRIB = store_thm("WORD_LEFT_SUB_DISTRIB",
  `!v:bool ** 'a w x. v * (w - x) = v * w - v * x`,
  REWRITE_TAC [word_sub_def,WORD_LEFT_ADD_DISTRIB,WORD_NEG_RMUL]);

val WORD_RIGHT_SUB_DISTRIB = save_thm("WORD_RIGHT_SUB_DISTRIB",
  ONCE_REWRITE_RULE [WORD_MULT_COMM] WORD_LEFT_SUB_DISTRIB);

(* ------------------------------------------------------------------------- *)
(*  Shifts : theorems                                                        *)
(* ------------------------------------------------------------------------- *)

val WORD_ss = rewrites [word_msb_def,word_lsl_def,word_lsr_def,word_asr_def,
  word_ror_def,word_rol_def,word_rrx_def,word_T,word_or_def,
  word_and_def,word_xor_def,n2w_def,BIT_ZERO,DIMINDEX_LT,MOD_PLUS_RIGHT];

val SHIFT_WORD_TAC = RW_TAC (fcp_ss++ARITH_ss++WORD_ss) [];

val ASR_ADD = store_thm("ASR_ADD",
  `!w m n. w >> m >> n = w >> (m + n)`,
  NTAC 2 SHIFT_WORD_TAC
    THEN FULL_SIMP_TAC arith_ss [DECIDE ``!m. m < 1 = (m = 0)``,NOT_LESS_EQUAL]
);

val LSR_ADD = store_thm("LSR_ADD",
  `!w m n. w >>> m >>> n = w >>> (m + n)`,
  SHIFT_WORD_TAC THEN Cases_on `i + n < ^WL`
    THEN SHIFT_WORD_TAC);

val ROR_ADD = store_thm("ROR_ADD",
  `!w m n. w #>> m #>> n = w #>> (m + n)`,
  SHIFT_WORD_TAC);

val LSL_ADD = store_thm("LSL_ADD",
  `!w m n. w << m << n = w << (m + n)`,
  SHIFT_WORD_TAC THEN EQ_TAC THEN RW_TAC arith_ss []);

val ASR_LIMIT = store_thm("ASR_LIMIT",
  `!w:bool ** 'a n. ^WL < n ==>
           (w >> n = if word_msb w then Tw else 0w)`,
  SHIFT_WORD_TAC);

val ASR_TRUE = store_thm("ASR_TRUE",
  `!w:bool ** 'a n. Tw >> n = Tw`, SHIFT_WORD_TAC);

val LSR_LIMIT = store_thm("LSR_LIMIT",
  `!w:bool ** 'a n. ^WL < n ==> (w >>> n = 0w)`,
  SHIFT_WORD_TAC);

val LSL_LIMIT = store_thm("LSL_LIMIT",
  `!w:bool ** 'a n. ^WL <= n ==> (w << n = 0w)`,
  SHIFT_WORD_TAC);

val MOD_TIMES_COMM = ONCE_REWRITE_RULE [ADD_COMM] MOD_TIMES;

val ROR_CYCLE = store_thm("ROR_CYCLE",
  `!w:bool ** 'a n. (w #>> (n * ^WL) = w)`,
  SHIFT_WORD_TAC THEN ASM_SIMP_TAC arith_ss [MOD_TIMES_COMM,DIMINDEX_GT_0]);

val ROR_MOD = store_thm("ROR_MOD",
  `!w:bool ** 'a n. (w #>> (n MOD ^WL) = w #>> n)`,
  SHIFT_WORD_TAC);

val SPEC1_RULE = (GEN_ALL o REWRITE_RULE [EXP_1] o
  ONCE_REWRITE_RULE [MULT_COMM] o SPECL [`i`,`x`,`1`]);

val LSL_ONE = store_thm("LSL_ONE",
  `!w:bool ** 'a. w << 1 = w + w`,
  STRIP_TAC THEN Cases_on_word `w` THEN REWRITE_TAC [word_add_def,w2n_n2w]
    THEN SHIFT_WORD_TAC THEN Cases_on `1 <= i`
    THEN ASM_SIMP_TAC arith_ss [SPEC1_RULE BIT_SHIFT_THM2,SPEC1_RULE BIT_SHIFT_THM3]
    THEN STRIP_ASSUME_TAC EXISTS_HB THEN POP_ASSUM SUBST_ALL_TAC
    THEN ASM_SIMP_TAC arith_ss [BIT_def,GSYM BITS_ZERO3,BITS_COMP_THM2,MIN_DEF]);

val ROR_TRUE = store_thm("ROR_TRUE",
  `!n. Tw #>> n = Tw`, SHIFT_WORD_TAC);

val ROR_ROL = store_thm("ROR_ROL",
  `!w n. (w #>> n #<< n = w) /\ (w #<< n #>> n = w)`,
  SHIFT_WORD_TAC
    THEN SPECL_THEN [`n`,`^WL`]
           (STRIP_ASSUME_TAC o SIMP_RULE std_ss [DIMINDEX_GT_0]) DA
    THEN1 ASM_SIMP_TAC std_ss [MOD_TIMES,GSYM ADD_ASSOC,DIMINDEX_GT_0,LESS_MOD,
             DECIDE ``!a:num b c. a < c ==> (a + (b + (c - a)) = b + c)``,
             ADD_MODULUS_LEFT]
    THEN ONCE_REWRITE_TAC [ADD_COMM]
    THEN ASM_SIMP_TAC std_ss [MOD_PLUS_RIGHT,MOD_TIMES,DIMINDEX_GT_0,LESS_MOD,
           DECIDE ``!a:num b c d. a < c ==> ((c - a + b + d + a) = c + b + d)``,
           ADD_MODULUS_RIGHT,ONCE_REWRITE_RULE [ADD_COMM] MOD_TIMES,ADD_ASSOC]);

val ZERO_SHIFT = store_thm("ZERO_SHIFT",
  `(!n. 0w:bool ** 'a << n  = 0w) /\
   (!n. 0w:bool ** 'a >> n  = 0w) /\
   (!n. 0w:bool ** 'a >>> n = 0w) /\
   (!n. 0w:bool ** 'a #>> n = 0w)`,
  SHIFT_WORD_TAC THEN Cases_on `i + n < ^WL`
    THEN ASM_SIMP_TAC fcp_ss []);

val SHIFT_ZERO = store_thm("SHIFT_ZERO",
  `(!a. a << 0 = a) /\ (!a. a >> 0 = a) /\
   (!a. a >>> 0 = a) /\ (!a. a #>> 0 = a)`,
  SHIFT_WORD_TAC);

val LSR_BITWISE = store_thm("LSR_BITWISE",
  `(!n v:bool ** 'a w:bool ** 'a. w >>> n && v >>> n = ((w && v) >>> n)) /\
   (!n v:bool ** 'a w:bool ** 'a. w >>> n !! v >>> n = ((w !! v) >>> n)) /\
   (!n v:bool ** 'a w:bool ** 'a. w >>> n ?? v >>> n = ((w ?? v) >>> n))`,
  SHIFT_WORD_TAC THEN Cases_on `i + n < dimindex UNIV`
    THEN ASM_SIMP_TAC fcp_ss []);

val LSL_BITWISE = store_thm("LSL_BITWISE",
  `(!n v:bool ** 'a w:bool ** 'a. w << n && v << n = ((w && v) << n)) /\
   (!n v:bool ** 'a w:bool ** 'a. w << n !! v << n = ((w !! v) << n)) /\
   (!n v:bool ** 'a w:bool ** 'a. w << n ?? v << n = ((w ?? v) << n))`,
  SHIFT_WORD_TAC THENL [PROVE_TAC [], PROVE_TAC [], ALL_TAC]
    THEN Cases_on `n <= i` THEN ASM_SIMP_TAC arith_ss []);

val ROR_BITWISE = store_thm("ROR_BITWISE",
  `(!n v:bool ** 'a w:bool ** 'a. w #>> n && v #>> n = ((w && v) #>> n)) /\
   (!n v:bool ** 'a w:bool ** 'a. w #>> n !! v #>> n = ((w !! v) #>> n)) /\
   (!n v:bool ** 'a w:bool ** 'a. w #>> n ?? v #>> n = ((w ?? v) #>> n))`,
  SHIFT_WORD_TAC);

val word_lsl_n2w = store_thm("word_lsl_n2w",
  `!n m. (n2w m):bool ** 'a << n =
      if ^HB < n then 0w else n2w (m * 2 ** n)`,
  Induct THEN1 SIMP_TAC arith_ss [SHIFT_ZERO]
    THEN ASM_REWRITE_TAC [ADD1,GSYM LSL_ADD]
    THEN Cases_on `dimindex (UNIV:'a -> bool) - 1 < n`
    THEN ASM_SIMP_TAC arith_ss [ZERO_SHIFT]
    THEN RW_TAC (arith_ss++numSimps.ARITH_AC_ss)
           [LSL_ONE,EXP_ADD,word_add_n2w]
    THEN `n = dimindex (UNIV:'a -> bool) - 1` by DECIDE_TAC
    THEN ONCE_REWRITE_TAC [GSYM n2w_mod]
    THEN ASM_SIMP_TAC std_ss [GSYM EXP,SUB1_SUC,MOD_EQ_0,ZERO_MOD,
           ZERO_LT_TWOEXP,DIMINDEX_GT_0]);

val word_lsr_n2w = store_thm("word_lsr_n2w",
  `!w:bool ** 'a n. w >>> n = (^HB -- n) w`,
  SIMP_TAC arith_ss [word_lsr_def,word_bits_def,MIN_IDEM,DIMINDEX_GT_0,
    DECIDE ``0 < m ==> (a <= m - 1 = a < m)``]);

val lem = (GEN_ALL o REWRITE_RULE [MATCH_MP (DECIDE ``0 < n ==> 1 <= n``)
  (SPEC_ALL ZERO_LT_TWOEXP),MULT_LEFT_1] o SPECL [`1`,`2 ** n`]) LESS_MONO_MULT;

val TRUE_LSL = store_thm("TRUE_LSL",
  `!n. Tw << n = n2w (^TOP - 2 ** n):bool ** 'a`,
  RW_TAC arith_ss [n2w_11,word_T_def,word_lsl_n2w]
    THENL [
      `^WL <= n` by DECIDE_TAC THEN IMP_RES_TAC TWOEXP_MONO2
        THEN ASM_SIMP_TAC std_ss [LESS_MOD,ZERO_MOD,ZERO_LT_TWOEXP,
               DECIDE ``a <= b ==> (a - b = 0)``],
      FULL_SIMP_TAC arith_ss [NOT_LESS,RIGHT_SUB_DISTRIB]
        THEN `n < ^WL` by DECIDE_TAC THEN IMP_RES_TAC TWOEXP_MONO
        THEN `^TOP * 2 ** n - 2 ** n =
              (2 ** n - 1) * ^TOP + (^TOP - 2 ** n)`
          by (`^TOP <= 2 ** n * ^TOP` by ASM_SIMP_TAC arith_ss [lem]
                THEN ASM_SIMP_TAC std_ss [MULT_LEFT_1,RIGHT_SUB_DISTRIB,
                       GSYM LESS_EQ_ADD_SUB,LESS_IMP_LESS_OR_EQ,SUB_ADD]
                THEN PROVE_TAC [MULT_COMM])
        THEN ASM_SIMP_TAC std_ss [MOD_TIMES,ZERO_LT_TWOEXP]]);

val word_asr_n2w = prove(
  `!n w. w:bool ** 'a >> n =
     if word_msb w then
       Tw << (^WL - MIN n ^WL) !! w >>> n
     else
       w >>> n`,
  NTAC 2 STRIP_TAC THEN Cases_on `^WL < n`
    THEN1 RW_TAC arith_ss [MIN_DEF,SHIFT_ZERO,LSR_LIMIT,ASR_LIMIT,WORD_OR_CLAUSES]
    THEN SHIFT_WORD_TAC THEN Cases_on `^WL <= i + n`
    THEN FULL_SIMP_TAC arith_ss [MIN_DEF]);

val word_asr_n2w = save_thm("word_asr_n2w", REWRITE_RULE [TRUE_LSL] word_asr_n2w);

val BITS_SUM1 =
  (GEN_ALL o REWRITE_RULE [MULT_LEFT_1] o
   INST [`a` |-> `1`] o SPEC_ALL) BITS_SUM;

val MIN_lem = prove(
 `(!m n. MIN m (m + n) = m) /\ !m n. MIN (m + n) m = m`,
  RW_TAC arith_ss [MIN_DEF]);

val lem = (GSYM o SIMP_RULE arith_ss [] o
  SPECL [`p`,`SUC m - n MOD SUC m + p`,
         `SUC m - n MOD SUC m`]) BIT_OF_BITS_THM;

val lem2 = (GSYM o REWRITE_RULE [ADD] o
   SPECL [`p`,`n MOD SUC m - 1`,`0`]) BIT_OF_BITS_THM;

val word_ror_n2w = store_thm("word_ror_n2w",
  `!n a. (n2w a):bool ** 'a #>> n =
     let x = n MOD ^WL in
       n2w (BITS ^HB x a + (BITS (x - 1) 0 a) * 2 ** (^WL - x))`,
  SIMP_TAC (bool_ss++boolSimps.LET_ss) [Once (GSYM ROR_MOD)]
    THEN RW_TAC fcp_ss [word_ror_def,n2w_def,DIVISION,DIMINDEX_GT_0]
    THEN STRIP_ASSUME_TAC EXISTS_HB
    THEN FULL_SIMP_TAC arith_ss []
    THEN Cases_on `i < SUC m - n MOD SUC m`
    THENL [
      `i + n MOD SUC m < SUC m` by DECIDE_TAC
        THEN PAT_ASSUM `i < y - z` (fn th => (STRIP_ASSUME_TAC o REWRITE_RULE
              [DECIDE ``a + (b + 1) = b + SUC a``]) (MATCH_MP LESS_ADD_1 th))
        THEN ASM_SIMP_TAC std_ss [BITS_SUM2,EXP_ADD,BIT_def,MULT_ASSOC]
        THEN ASM_SIMP_TAC arith_ss [GSYM BIT_def,BIT_OF_BITS_THM],
      RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS])
        THEN IMP_RES_TAC LESS_EQUAL_ADD
        THEN ASSUME_TAC (SPECL [`m`,`n MOD SUC m`,`a`] BITSLT_THM)
        THEN ASM_SIMP_TAC std_ss [lem,BITS_SUM]
        THEN REWRITE_TAC [GSYM lem]
        THEN ASM_SIMP_TAC std_ss [ONCE_REWRITE_RULE [ADD_COMM] BIT_SHIFT_THM]
        THEN `p < SUC m /\ p <= n MOD SUC m - 1` by DECIDE_TAC
        THEN `SUC m - n MOD SUC m + p + n MOD SUC m = SUC m + p`
          by SIMP_TAC arith_ss [DIVISION,
               DECIDE ``b < a ==> (a - b + c + b = a + c:num)``]
        THEN ASM_SIMP_TAC std_ss [LESS_MOD,prim_recTheory.LESS_0,
               ADD_MODULUS,lem2]]);

val word_rrx_n2w = store_thm("word_rrx_n2w",
  `!c a. word_rrx ((n2w a):bool ** 'a) c =
       (n2w (BITS ^HB 1 a + SBIT c ^HB)):bool ** 'a`,
  SHIFT_WORD_TAC THEN RW_TAC arith_ss [SBIT_def,BIT_OF_BITS_THM]
    THEN STRIP_ASSUME_TAC EXISTS_HB THEN FULL_SIMP_TAC arith_ss []
    THENL [
      METIS_TAC [BITSLT_THM,SUC_SUB1,BITS_SUM1,BIT_def,BIT_B],
      SIMP_TAC arith_ss [BIT_def,BITS_COMP_THM2,MIN_lem,BITS_ZERO],
      `i < m` by DECIDE_TAC
        THEN POP_ASSUM (fn th => (STRIP_ASSUME_TAC o REWRITE_RULE
              [DECIDE ``a + (b + 1) = b + SUC a``]) (MATCH_MP LESS_ADD_1 th))
        THEN ASM_SIMP_TAC std_ss [EXP_ADD,BIT_def,BITS_SUM2,BITS_COMP_THM2]
        THEN SIMP_TAC std_ss [ADD1,ONCE_REWRITE_RULE [ADD_COMM] MIN_lem]]);

(* ------------------------------------------------------------------------- *)
(*  Orderings : theorems                                                     *)
(* ------------------------------------------------------------------------- *)

val EQUAL_THEN_SUB_ZERO = GEN_ALL (PROVE [WORD_SUB_REFL,WORD_LCANCEL_SUB]
  ``((a - b) = 0w) = (a = b)``);

val order_rule =
   SIMP_RULE (std_ss++boolSimps.LET_ss)
     [nzcv_def,GSYM word_add_n2w,n2w_w2n,GSYM word_sub_def,EQUAL_THEN_SUB_ZERO];

val word_lt = order_rule word_lt_def;
val word_gt = order_rule word_gt_def;
val word_le = order_rule word_le_def;
val word_ge = order_rule word_ge_def;
val word_ls = order_rule word_ls_def;
val word_hi = order_rule word_hi_def;
val word_lo = order_rule word_lo_def;
val word_hs = order_rule word_hs_def;

val SPEC_LESS_EXP_SUC_MONO =
  (GEN_ALL o SIMP_RULE arith_ss
     [DIMINDEX_GT_0,SUB1_SUC] o
   SPECL [`^HB`,`0`]) LESS_EXP_SUC_MONO;

val SPEC_LESS_EXP_SUC_MONO2 =
  (GEN_ALL o SIMP_RULE arith_ss [DIMINDEX_GT_0] o
   SPECL [`^HB`,`0`]) LESS_EXP_SUC_MONO;

val SPLIT_2_EXP_WL = prove(
  `^TOP = ^MSB + ^MSB`,
  STRIP_ASSUME_TAC EXISTS_HB
    THEN ASM_SIMP_TAC arith_ss [EXP]);

val WORD_NEG_L = store_thm("WORD_NEG_L",
  `$- word_L = word_L`,
  SIMP_TAC bool_ss [word_2comp_n2w,word_L_def,n2w_11,
           LESS_MOD,SPEC_LESS_EXP_SUC_MONO,BITS_ZERO3]
    THEN REWRITE_TAC [SPLIT_2_EXP_WL]
    THEN SIMP_TAC arith_ss [GSYM EXP,LESS_MOD,
           SPEC_LESS_EXP_SUC_MONO,SPEC_LESS_EXP_SUC_MONO2]);

(* ------------------------------------------------------------------------- *)

val BITS_COMP_MSB = (SIMP_RULE arith_ss [] o
  SPECL [`m`,`0`,`m - 1`,`0`]) BITS_COMP_THM;

val SLICE_COMP_MSB = prove(
  `!b n. ~(b = 0) ==> (SLICE b b n + SLICE (b - 1) 0 n = SLICE b 0 n)`,
   REPEAT STRIP_TAC
     THEN POP_ASSUM (fn th => REWRITE_TAC [(SIMP_RULE arith_ss [SUB_SUC1,th] o
            SPECL [`b`,`b - 1`,`0`,`n`]) SLICE_COMP_THM]));

val MSB_THM1 = prove(
  `!a:bool ** 'a. ~(^HB = 0) /\ word_msb a ==>
        (w2n a = ^MSB + BITS (^HB - 1) 0 (w2n a))`,
  Cases_word THEN STRIP_ASSUME_TAC EXISTS_HB
    THEN RW_TAC arith_ss [word_msb_n2w,w2n_n2w,GSYM BITS_ZERO3,BITS_COMP_MSB]
    THEN IMP_RES_TAC BIT_SLICE_THM2 THEN POP_ASSUM (SUBST1_TAC o SYM)
    THEN ASM_SIMP_TAC arith_ss [SLICE_COMP_MSB,GSYM SLICE_ZERO_THM]);

val MSB_THM2 = prove(
  `!a:bool ** 'a. ~(^HB = 0) /\ word_msb a ==>
        (w2n ($- a) = ^MSB - BITS (^HB - 1) 0 (w2n a))`,
  Cases_word THEN REPEAT STRIP_TAC THEN IMP_RES_TAC MSB_THM1
    THEN STRIP_ASSUME_TAC EXISTS_HB
    THEN FULL_SIMP_TAC arith_ss [word_msb_n2w,word_2comp_n2w,w2n_n2w,
           BITS_COMP_MSB,GSYM BITS_ZERO3]
    THEN ASM_SIMP_TAC arith_ss [BITS_ZERO3,GSYM ADD1,ADD_MODULUS,MOD_MOD,
           ZERO_LT_TWOEXP,SUB_SUC1]
    THEN REWRITE_TAC [EXP,TIMES2,SUB_PLUS,ADD_SUB]
    THEN `2 ** m - n MOD 2 ** m < 2 ** SUC m` by METIS_TAC
           [DECIDE ``a - b <= a /\ a < SUC a``,TWOEXP_MONO,LESS_EQ_LESS_TRANS]
    THEN ASM_SIMP_TAC arith_ss [GSYM EXP,LESS_MOD]);

val MSB_THM3 = prove(
  `!a:bool ** 'a. ~(^HB = 0) /\ ~word_msb a ==>
        (w2n a = BITS (^HB - 1) 0 (w2n a))`,
  Cases_word THEN STRIP_ASSUME_TAC EXISTS_HB
    THEN RW_TAC arith_ss [word_msb_n2w,w2n_n2w,GSYM BITS_ZERO3,BITS_COMP_MSB]
    THEN `~(m = 0)` by DECIDE_TAC
    THEN MAP_EVERY IMP_RES_TAC [BIT_SLICE_THM3,SLICE_COMP_MSB]
    THEN POP_ASSUM (SPEC_THEN `n` ASSUME_TAC)
    THEN PAT_ASSUM `SLICE m m n = 0` (fn th =>
           FULL_SIMP_TAC arith_ss [th,GSYM SLICE_ZERO_THM]));

val MSB_THM4 = prove(
  `!a:bool ** 'a. ~(^HB = 0) /\ ~(a = 0w) /\ ~word_msb a ==>
       (w2n ($- a) = ^TOP - BITS (^HB - 1) 0 (w2n a)) /\
       ~(BITS (^HB - 1) 0 (w2n a) = 0)`,
  Cases_word THEN REPEAT STRIP_TAC THEN IMP_RES_TAC MSB_THM3
    THEN STRIP_ASSUME_TAC EXISTS_HB
    THEN FULL_SIMP_TAC arith_ss [word_msb_n2w,word_2comp_n2w,w2n_n2w,n2w_11,
           GSYM BITS_ZERO3,BITS_ZERO2,BITS_COMP_MSB]
    THEN FULL_SIMP_TAC arith_ss [BITS_COMP_THM2,MIN_DEF]
    THEN `2 ** SUC m - BITS (m - 1) 0 n < 2 ** SUC m`
      by ASM_SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
    THEN ASM_SIMP_TAC bool_ss [BITS_ZEROL]);

val HB_0_MSB = prove(
  `!a:bool ** 'a. (^HB = 0) /\ word_msb a ==> (a = 1w)`,
  Cases_word THEN STRIP_ASSUME_TAC EXISTS_HB
    THEN RW_TAC bool_ss [word_msb_n2w,w2n_n2w,n2w_11,BIT_def,SUC_SUB1]
    THEN FULL_SIMP_TAC arith_ss [BITS_ZERO3]);

val HB_0_NOT_MSB = prove(
  `!a:bool ** 'a. (^HB = 0) /\ ~word_msb a ==> (a = 0w)`,
  Cases_word THEN STRIP_ASSUME_TAC EXISTS_HB
    THEN RW_TAC fcp_ss [word_msb_n2w,n2w_11,ZERO_MOD,ZERO_LT_TWOEXP,GSYM BITS_ZERO3]
    THEN METIS_TAC [DECIDE ``(SUC m - 1 = 0) ==> (m = 0)``,BIT_def,NOT_BITS2]);

val DIMINDEX_1 = prove(
  `(^WL - 1 = 0) ==> (^WL = 1)`,
  STRIP_ASSUME_TAC EXISTS_HB THEN ASM_SIMP_TAC arith_ss []);

val MSB_THM1b = prove(
  `!a:bool ** 'a. (^HB = 0) /\ word_msb a ==> (w2n a = 1)`,
  METIS_TAC [HB_0_MSB,DIMINDEX_1,EXP_1,LESS_MOD,DECIDE ``1 < 2``,w2n_n2w]);

val MSB_THM2b = prove(
  `!a:bool ** 'a. (^HB = 0) /\ word_msb a ==> (w2n (word_2comp a) = 1)`,
  REPEAT STRIP_TAC THEN MAP_EVERY IMP_RES_TAC [HB_0_MSB,DIMINDEX_1]
    THEN ASM_SIMP_TAC arith_ss [w2n_n2w,word_2comp_n2w]);

val MSB_THM3b = prove(
  `!a:bool ** 'a. (^HB = 0) /\ ~word_msb a ==> (w2n a = 0)`,
  REPEAT STRIP_TAC THEN MAP_EVERY IMP_RES_TAC [HB_0_NOT_MSB,DIMINDEX_1]
    THEN ASM_SIMP_TAC arith_ss [w2n_n2w]);

val MSB_THM4b = prove(
  `!a:bool ** 'a. (^HB = 0) /\ ~word_msb a ==> (w2n (word_2comp a) = 0)`,
  REPEAT STRIP_TAC THEN MAP_EVERY IMP_RES_TAC [HB_0_NOT_MSB,DIMINDEX_1]
    THEN ASM_SIMP_TAC arith_ss [w2n_n2w,WORD_NEG_0]);

(* ------------------------------------------------------------------------- *)

val w2n_mod = PROVE [n2w_w2n,n2w_mod]
   ``(w2n (a:bool ** 'a) = n) ==> (a = n2w (n MOD ^TOP))``;

val BITS_MSB_LT = (GEN_ALL o SIMP_RULE arith_ss [SUB_SUC1] o
  DISCH `~(b = 0)` o SPECL [`b - 1`,`0`,`a`]) BITSLT_THM;

val SLICE_MSB_LT = REWRITE_RULE [GSYM SLICE_ZERO_THM] BITS_MSB_LT;

val BITS_MSB_LTEQ = prove(
  `!b a. ~(b = 0) ==> BITS (b - 1) 0 a <= 2 ** b`,
  PROVE_TAC [LESS_IMP_LESS_OR_EQ,BITS_MSB_LT]);

val TWO_COMP_POS = store_thm("TWO_COMP_POS",
  `!a:bool ** 'a. ~word_msb a ==>
          (if a = 0w then ~word_msb ($- a) else word_msb ($- a))`,
  Cases_word
    THEN STRIP_ASSUME_TAC EXISTS_HB
    THEN RW_TAC bool_ss [WORD_NEG_0]
    THEN Cases_on `^HB = 0` THEN1 PROVE_TAC [HB_0_NOT_MSB]
    THEN `~(m = 0)` by DECIDE_TAC
    THEN MAP_EVERY IMP_RES_TAC [MSB_THM4,w2n_mod]
    THEN PAT_ASSUM `dimindex UNIV = SUC m` (fn th =>
           FULL_SIMP_TAC arith_ss [word_msb_n2w,BITS_COMP_THM2,MIN_DEF,BIT_def,th])
    THEN `2 ** SUC m - BITS (m - 1) 0 (w2n ((n2w n):bool ** 'a)) < 2 ** SUC m /\
          2 ** m - BITS (m - 1) 0 (w2n ((n2w n):bool ** 'a)) < 2 ** m`
      by ASM_SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
    THEN ASM_SIMP_TAC std_ss [LESS_MOD] THEN IMP_RES_TAC BITS_MSB_LTEQ
    THEN ASM_SIMP_TAC bool_ss [SPECL [`m`,`m`] BITS_THM,SUC_SUB,EXP_1,EXP,
           TIMES2,LESS_EQ_ADD_SUB,DIV_MULT_1] THEN numLib.REDUCE_TAC);

val TWO_COMP_NEG_lem = prove(
  `!n. ~(^HB = 0) /\ ~((n2w n):bool ** 'a = word_L) /\
       word_msb ((n2w n):bool ** 'a) ==>
       ~(BITS (^WL - 2) 0 (w2n ((n2w n):bool ** 'a)) = 0)`,
  REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC EXISTS_HB
    THEN FULL_SIMP_TAC arith_ss [BITS_COMP_THM2,MIN_DEF,GSYM BITS_ZERO3,
           word_msb_n2w,w2n_n2w]
    THEN IMP_RES_TAC BIT_SLICE_THM2
    THEN RULE_ASSUM_TAC (REWRITE_RULE [GSYM SLICE_ZERO_THM])
    THEN `~(m = 0)` by DECIDE_TAC THEN IMP_RES_TAC SLICE_COMP_MSB
    THEN POP_ASSUM (SPEC_THEN `n` ASSUME_TAC)
    THEN FULL_SIMP_TAC arith_ss [word_L_def,n2w_11,LESS_MOD,
           SUC_SUB1,SUC_SUB2,TWOEXP_MONO]
    THEN FULL_SIMP_TAC bool_ss [GSYM BITS_ZERO3,GSYM SLICE_ZERO_THM]
    THEN PROVE_TAC [ADD_0]);

val TWO_COMP_NEG = store_thm("TWO_COMP_NEG",
  `!a:bool ** 'a. word_msb a ==>
       if (^HB = 0) \/ (a = word_L) then
         word_msb (word_2comp a)
       else
        ~word_msb (word_2comp a)`,
  RW_TAC bool_ss [] THENL [
    IMP_RES_TAC HB_0_MSB
      THEN ASM_SIMP_TAC arith_ss [word_msb_n2w,word_T_def,WORD_NEG_1,
             DIMINDEX_GT_0,ONE_COMP_0_THM],
    ASM_REWRITE_TAC [WORD_NEG_L],
    FULL_SIMP_TAC bool_ss [] THEN Cases_on_word `a`
      THEN MAP_EVERY IMP_RES_TAC [MSB_THM2,w2n_mod,TWO_COMP_NEG_lem]
      THEN STRIP_ASSUME_TAC EXISTS_HB THEN `~(m = 0)` by DECIDE_TAC
      THEN FULL_SIMP_TAC arith_ss [BITS_COMP_THM2,MIN_DEF,BIT_def,
             word_msb_n2w,w2n_n2w,GSYM BITS_ZERO3,SUC_SUB2]
      THEN `2 ** m - BITS (m - 1) 0 n < 2 ** m`
        by ASM_SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
      THEN ASM_SIMP_TAC arith_ss [BITS_THM,SUC_SUB,EXP_1,LESS_DIV_EQ_ZERO]]);

val TWO_COMP_POS_NEG = store_thm("TWO_COMP_POS_NEG",
  `!a:bool ** 'a. ~((^HB = 0) \/ (a = 0w) \/ (a = word_L)) ==>
     (~word_msb a = word_msb (word_2comp a))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
    THEN1 METIS_TAC [TWO_COMP_POS]
    THEN METIS_TAC [WORD_NEG_L,WORD_NEG_EQ,WORD_NEG_NEG,TWO_COMP_NEG]);

val TWO_COMP_NEG_POS = METIS_PROVE [TWO_COMP_POS_NEG]
  ``!a:bool ** 'a. ~((^HB = 0) \/ (a = 0w) \/ (a = word_L)) ==>
     (word_msb a = ~word_msb (word_2comp a))``;

val WORD_0_POS = store_thm("WORD_0_POS",
  `~word_msb 0w`, REWRITE_TAC [word_msb_n2w,BIT_ZERO]);

val WORD_H_POS = store_thm("WORD_H_POS",
  `~word_msb word_H`,
  `^MSB - 1 < ^MSB` by ASM_SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
     THEN ASM_SIMP_TAC bool_ss [word_H_def,word_msb_n2w,BIT_def,BITS_THM,
            LESS_DIV_EQ_ZERO,ZERO_MOD,ZERO_LT_TWOEXP] THEN DECIDE_TAC);

val WORD_L_NEG = store_thm("WORD_L_NEG",
  `word_msb word_L`, REWRITE_TAC [word_L_def,word_msb_n2w,BIT_ZERO,BIT_B]);

(* ------------------------------------------------------------------------- *)

val NOT_EQUAL_THEN_NOT =
  PROVE [EQUAL_THEN_SUB_ZERO] ``!a b. ~(a = b) = ~(b - a = 0w)``;

val SUB_EQUAL_WORD_L_MSB = prove(
  `!a:bool ** 'a b:bool ** 'a. ~(^HB = 0) /\ (a - b = word_L) ==>
      ~(word_msb a = word_msb b)`,
  RW_TAC bool_ss [WORD_EQ_SUB_RADD] THEN STRIP_ASSUME_TAC EXISTS_HB
    THEN `~(m = 0)` by DECIDE_TAC THEN Cases_on_word `b`
    THEN ASM_REWRITE_TAC [word_msb_n2w,word_L_def,SUC_SUB1]
    THEN SUBST1_TAC ((SYM o SPEC `n`) n2w_mod)
    THEN ASM_REWRITE_TAC [word_msb_n2w,word_add_n2w,SUC_SUB1,
           GSYM BITS_ZERO3,GSYM SLICE_ZERO_THM]
    THEN `SLICE m 0 n = SLICE m m n + SLICE (m - 1) 0 n`
      by METIS_TAC [SLICE_COMP_MSB,SUC_SUB2]
    THEN Cases_on `BIT m n`
    THENL [IMP_RES_TAC BIT_SLICE_THM2,IMP_RES_TAC BIT_SLICE_THM3]
    THEN ASM_SIMP_TAC arith_ss [BIT_def,BITS_THM,SUC_SUB,EXP_1,SLICE_MSB_LT,
           DIV_MULT,DIV_MULT_1]);

val LEM1_TAC =
  REPEAT STRIP_TAC
    THEN MAP_EVERY Cases_on [`word_msb a`,`word_msb b`,`a = b`]
    THEN FULL_SIMP_TAC bool_ss [word_lt,word_gt,word_le,word_ge,
           WORD_SUB_REFL,WORD_0_POS,DECIDE (Term `~(a = ~a)`)]
    THEN GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV)
           empty_rewrites [GSYM WORD_NEG_SUB]
    THEN IMP_RES_TAC NOT_EQUAL_THEN_NOT THEN Cases_on `b - a = word_L`
    THEN PROVE_TAC [SUB_EQUAL_WORD_L_MSB,TWO_COMP_POS_NEG];

val LEM2_TAC =
  REPEAT STRIP_TAC THEN MAP_EVERY Cases_on [`word_msb a`,`word_msb b`]
    THEN MAP_EVERY IMP_RES_TAC [MSB_THM1b,MSB_THM2b,MSB_THM3b,MSB_THM4b]
    THEN ASM_SIMP_TAC arith_ss [word_lt,word_gt,word_le,word_ge,word_sub_def,
           word_add_def,word_add_n2w,word_msb_n2w,n2w_11,BITS_ZERO2,BIT_def]
    THEN ASM_SIMP_TAC arith_ss [BITS_ZERO3]
    THEN PROVE_TAC [w2n_11];

val WORD_GREATER = store_thm("WORD_GREATER",
  `!a:bool ** 'a b. a > b = b < a`,
  Cases_on `^HB = 0` THENL [LEM2_TAC,LEM1_TAC]);

val WORD_GREATER_EQ = store_thm("WORD_GREATER_EQ",
  `!a:bool ** 'a b. a >= b = b <= a`,
  Cases_on `^HB = 0` THENL [LEM2_TAC,LEM1_TAC]);

val WORD_NOT_LESS = store_thm("WORD_NOT_LESS",
  `!a:bool ** 'a b. ~(a < b) = b <= a`,
  Cases_on `^HB = 0` THENL [LEM2_TAC,LEM1_TAC]);

(* ------------------------------------------------------------------------- *)

val LESS_EQ_ADD2 = DECIDE (Term `!a:num b c. a + b <= a + c ==> b <= c`);
val LESS_ADD2 = DECIDE (Term `!a:num b c. a + b < a + c ==> b < c`);
val LESS_EQ_ADD_SUB2 =
   DECIDE (Term `!m:num n p. p <= n ==> (m + p - n = m - (n - p))`);
val SUB_SUC1 = DECIDE ``!m. ~(m = 0) ==> (SUC (m - 1) = m)``;

val start_tac =
  REWRITE_TAC [word_sub_def,word_add_def] THEN RW_TAC bool_ss [word_msb_n2w]
    THEN POP_ASSUM MP_TAC THEN Cases_on `w2n a < w2n b`
    THEN ASM_REWRITE_TAC [] THEN IMP_RES_TAC MSB_THM1
    THEN `w2n ($- b) = ^MSB - BITS (^HB - 1) 0 (w2n b)` by IMP_RES_TAC MSB_THM2
    THEN ABBREV_TAC `x = BITS (^HB - 1) 0 (w2n a)`
    THEN ABBREV_TAC `y = BITS (^HB - 1) 0 (w2n b)`
    THEN FULL_SIMP_TAC bool_ss [NOT_LESS,GSYM LESS_EQ_ADD_SUB,BITS_MSB_LT,
           DECIDE (Term `!a b. a + b + a = 2 * a + b`)];

val WORD_LT_lem = prove(
  `!a:bool ** 'a b. ~(^HB = 0) /\ word_msb a /\
         word_msb b /\ word_msb (a - b) ==> w2n a < w2n b`,
  start_tac THEN IMP_RES_TAC LESS_EQ_ADD2
    THEN ASM_SIMP_TAC bool_ss [Abbr`x`,Abbr`y`,LESS_EQ_ADD_SUB2,BIT_def,
           BITS_THM,SUC_SUB,EXP_1,DIV_1,SUB_0,CONJUNCT1 EXP,LESS_EQ_ADD_SUB,
           NOT_MOD2_LEM2,SUB_SUC1]
    THEN SIMP_TAC arith_ss [MOD_2EXP_LT,SUB_LEFT_ADD,
           DECIDE ``a < b ==> ~(b <= a:num)``]
    THEN PAT_ASSUM `~(x = 0)` ASSUME_TAC THEN STRIP_ASSUME_TAC EXISTS_HB
    THEN FULL_SIMP_TAC bool_ss [SUC_SUB1,BITS_ZERO3,LESS_EQ_ADD_SUB,SUB_SUC1,
           DECIDE ``a < c /\ b < c ==> (a - b) < c:num``,MOD_2EXP_LT,DIV_MULT,
           DIVMOD_ID,DECIDE ``0 < 2``]);

val WORD_LT_lem2 = prove(
  `!a:bool ** 'a b. ~(^HB = 0) /\ word_msb a /\ word_msb b /\
         ~word_msb (a - b) ==> ~(w2n a < w2n b)`,
  start_tac
    THEN ONCE_REWRITE_TAC [DECIDE (Term `!a b c. (a:num) + b + c = a + c + b`)]
    THEN PAT_ASSUM `x + y < x + z` (ASSUME_TAC o (MATCH_MP LESS_ADD2))
    THEN IMP_RES_TAC LESS_ADD_1
    THEN `y < ^MSB` by METIS_TAC [BITS_MSB_LT]
    THEN `p + 1 <= ^MSB` by DECIDE_TAC
    THEN ASM_SIMP_TAC arith_ss [SUB_LEFT_ADD] THEN IMP_RES_TAC LESS_EQUAL_ADD
    THEN ASM_SIMP_TAC std_ss [TIMES2,DECIDE ``x + (y + p) = x + p + y:num``,
           DECIDE ``a + b + c - (c + b) = a:num``]
    THEN `p' < p + 1 + p'` by DECIDE_TAC
    THEN ASM_SIMP_TAC bool_ss [BIT_def,BITS_THM,SUC_SUB,EXP_1,DIV_MULT_1]
    THEN numLib.REDUCE_TAC);

val w2n_0 =
  SIMP_CONV arith_ss [w2n_n2w,ZERO_MOD,ZERO_LT_TWOEXP] ``w2n 0w``;

val start_tac = REWRITE_TAC [word_sub_def,word_add_def]
    THEN NTAC 2 STRIP_TAC
    THEN Cases_on `b = 0w`
    THEN1 (ASM_REWRITE_TAC [WORD_NEG_0,w2n_0,ADD_0,n2w_w2n]
             THEN PROVE_TAC [prim_recTheory.NOT_LESS_0])
    THEN RW_TAC bool_ss [word_msb_n2w]
    THEN POP_ASSUM MP_TAC
    THEN Cases_on `w2n a < w2n b` THEN ASM_REWRITE_TAC []
    THEN IMP_RES_TAC MSB_THM3
    THEN `w2n ($- b) = ^TOP - BITS (^HB - 1) 0 (w2n b)` by IMP_RES_TAC MSB_THM4
    THEN ABBREV_TAC `x = BITS (^HB - 1) 0 (w2n a)`
    THEN ABBREV_TAC `y = BITS (^HB - 1) 0 (w2n b)`
    THEN `y <= ^MSB` by METIS_TAC [BITS_MSB_LTEQ]
    THEN `y <= ^TOP` by METIS_TAC [SPEC_LESS_EXP_SUC_MONO,
                          LESS_IMP_LESS_OR_EQ,LESS_EQ_TRANS]
    THEN FULL_SIMP_TAC bool_ss [NOT_LESS,GSYM LESS_EQ_ADD_SUB]
    THEN ONCE_REWRITE_TAC [ADD_COMM];

val WORD_LT_lem3 = prove(
  `!a:bool ** 'a b. ~(^HB = 0) /\ ~word_msb a /\ ~word_msb b /\
         word_msb (a - b) ==> w2n a < w2n b`,
  start_tac THEN `x < ^MSB` by METIS_TAC [BITS_MSB_LT]
    THEN `x - y < ^MSB` by DECIDE_TAC
    THEN STRIP_ASSUME_TAC EXISTS_HB
    THEN FULL_SIMP_TAC bool_ss [BIT_def,BITS_THM,SUC_SUB,EXP_1,
           LESS_EQ_ADD_SUB,EXP,DIV_MULT,SUC_SUB1]
    THEN numLib.REDUCE_TAC);

val WORD_LT_lem4 = prove(
  `!a:bool ** 'a b. ~(^HB = 0) /\ ~word_msb a /\ ~word_msb b /\
        ~word_msb (a - b) ==> ~(w2n a < w2n b)`,
  start_tac
    THEN `y <= ^MSB + x` by DECIDE_TAC
    THEN ASM_SIMP_TAC bool_ss [SPLIT_2_EXP_WL,GSYM ADD_ASSOC,LESS_EQ_ADD_SUB]
    THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
    THEN `^MSB - (y - x) < ^MSB` by DECIDE_TAC
    THEN STRIP_ASSUME_TAC EXISTS_HB
    THEN FULL_SIMP_TAC bool_ss [LESS_EQ_ADD_SUB2,DIV_MULT_1,BIT_def,
           BITS_THM,SUC_SUB,EXP_1]
    THEN numLib.REDUCE_TAC);

val WORD_LT = store_thm("WORD_LT",
  `!a b. word_lt a b = (word_msb a = word_msb b) /\ w2n a < w2n b \/
                        word_msb a /\ ~word_msb b`,
  Tactical.REVERSE (Cases_on `^HB = 0`) THEN REPEAT STRIP_TAC
    THEN1 METIS_TAC [word_lt,WORD_LT_lem,WORD_LT_lem2,WORD_LT_lem3,WORD_LT_lem4]
    THEN MAP_EVERY Cases_on [`word_msb a`,`word_msb b`,
           `word_msb (n2w (w2n a + w2n ($- b)):bool ** 'a)`]
    THEN ASM_REWRITE_TAC [word_lt] THEN POP_ASSUM MP_TAC
    THEN Cases_on `w2n a < w2n b`
    THEN ASM_REWRITE_TAC [word_msb_n2w,word_sub_def,word_add_def]
    THEN MAP_EVERY IMP_RES_TAC [MSB_THM1b,MSB_THM2b,MSB_THM3b,MSB_THM4b]
    THEN ASM_SIMP_TAC arith_ss [BIT_def,BITS_THM]);

val WORD_GT = save_thm("WORD_GT",
  (GEN `a` o GEN `b` o REWRITE_CONV [WORD_GREATER,WORD_LT,GSYM GREATER_DEF])
  ``a:bool ** 'a > b``);

val WORD_LE = store_thm("WORD_LE",
  `!a:bool **'a b. a <= b = (word_msb a = word_msb b) /\ (w2n a <= w2n b) \/
                             word_msb a /\ ~word_msb b`,
  SIMP_TAC bool_ss [WORD_LT,GSYM WORD_NOT_LESS,NOT_LESS] THEN DECIDE_TAC);

val WORD_GE = save_thm("WORD_GE",
  (GEN `a` o GEN `b` o REWRITE_CONV [WORD_GREATER_EQ,WORD_LE,GSYM GREATER_EQ])
  ``a:bool ** 'a >= b``);

val w2n_2comp = prove(
  `!a:bool ** 'a. w2n ($- a) = if a = 0w then 0 else ^TOP - w2n a`,
  RW_TAC bool_ss [WORD_NEG_0,w2n_0] THEN Cases_on_word `a`
    THEN FULL_SIMP_TAC bool_ss [GSYM w2n_11,w2n_0,w2n_n2w,word_2comp_n2w]
    THEN `^TOP - n MOD ^TOP < ^TOP` by ASM_SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
    THEN ASM_SIMP_TAC bool_ss [LESS_MOD]);

val WORD_LO = store_thm("WORD_LO",
  `!a b. a <+ b = w2n a < w2n b`,
  RW_TAC bool_ss [word_lo] THEN Cases_on `b = 0w`
    THEN ASM_SIMP_TAC arith_ss [w2n_2comp,w2n_0,GSYM LESS_EQ_ADD_SUB,
           MATCH_MP LESS_IMP_LESS_OR_EQ (SPEC `b` w2n_lt)]
    THEN Cases_on `a = b` THEN1 ASM_SIMP_TAC arith_ss [BIT_B]
    THEN Cases_on `w2n a < w2n b` THEN ASM_REWRITE_TAC []
    THEN ONCE_REWRITE_TAC [ADD_COMM]
    THEN RULE_ASSUM_TAC (REWRITE_RULE [GSYM w2n_11,w2n_0,w2n_n2w]) THENL [
      IMP_RES_TAC LESS_IMP_LESS_OR_EQ
        THEN `~(w2n b - w2n a = 0)` by DECIDE_TAC
        THEN POP_ASSUM (fn th => `^TOP - (w2n b - w2n a) < ^TOP`
          by SIMP_TAC arith_ss [th,ZERO_LT_TWOEXP])
        THEN ASM_SIMP_TAC arith_ss [GSYM SUB_SUB,BIT_def,BITS_THM,SUC_SUB,
               EXP_1,LESS_DIV_EQ_ZERO],
      RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS])
        THEN ASSUME_TAC (SPEC `a` w2n_lt)
        THEN `w2n a - w2n b < ^TOP` by ASM_SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
        THEN ASM_SIMP_TAC bool_ss [LESS_EQ_ADD_SUB,BIT_def,BITS_THM,SUC_SUB,EXP_1,DIV_MULT_1]
        THEN numLib.REDUCE_TAC]);

val WORD_LS_LO_EQ  = PROVE [word_ls,word_lo] ``a <=+ b = a <+ b \/ (a = b)``;
val WORD_HI_NOT_LS = PROVE [word_ls,word_hi] ``a >+ b = ~(a <=+ b)``;
val WORD_HS_NOT_LO = PROVE [word_hs,word_lo] ``a >=+ b = ~(a <+ b)``;

val WORD_LS = store_thm("WORD_LS",
  `!a b. a <=+ b = w2n a <= w2n b`,
  PROVE_TAC [w2n_11,WORD_LO,WORD_LS_LO_EQ,LESS_OR_EQ]);

val WORD_HI = store_thm("WORD_HI",
  `!a b. a >+ b = w2n a > w2n b`,
  REWRITE_TAC [WORD_HI_NOT_LS,WORD_LS,GSYM NOT_GREATER]);

val WORD_HS = store_thm("WORD_HS",
  `!a b. a >=+ b = w2n a >= w2n b`,
  REWRITE_TAC [WORD_HS_NOT_LO,WORD_LO,DECIDE ``~(a < b) = a >= b:num``]);

(* ------------------------------------------------------------------------- *)

val WORD_NOT_LESS_EQUAL = store_thm("WORD_NOT_LESS_EQUAL",
  `!a:bool ** 'a b. ~(a <= b) = b < a`, PROVE_TAC [WORD_NOT_LESS]);

val WORD_LESS_OR_EQ = store_thm("WORD_LESS_OR_EQ",
  `!a:bool ** 'a b. a <= b = a < b \/ (a = b)`, LEM1_TAC);

val WORD_GREATER_OR_EQ = store_thm("WORD_GREATER_OR_EQ",
  `!a:bool ** 'a b. a >= b = a > b \/ (a = b)`,
  PROVE_TAC [WORD_GREATER,WORD_GREATER_EQ,WORD_LESS_OR_EQ]);

val WORD_LESS_TRANS = store_thm("WORD_LESS_TRANS",
  `!a:bool ** 'a b c. a < b /\ b < c ==> a < c`,
  RW_TAC bool_ss [WORD_LT] THEN IMP_RES_TAC LESS_TRANS
     THEN ASM_REWRITE_TAC [] THEN PROVE_TAC []);

val WORD_LESS_EQ_TRANS = store_thm("WORD_LESS_EQ_TRANS",
  `!a:bool ** 'a b c. a <= b /\ b <= c ==> a <= c`,
  RW_TAC bool_ss [WORD_LE] THEN IMP_RES_TAC LESS_EQ_TRANS
     THEN ASM_REWRITE_TAC [] THEN PROVE_TAC []);

val WORD_LESS_EQ_LESS_TRANS = store_thm("WORD_LESS_EQ_LESS_TRANS",
  `!a:bool ** 'a b c. a <= b /\ b < c ==> a < c`,
  RW_TAC bool_ss [WORD_LE,WORD_LT] THEN IMP_RES_TAC LESS_EQ_LESS_TRANS
     THEN ASM_REWRITE_TAC [] THEN PROVE_TAC []);

val WORD_LESS_LESS_EQ_TRANS = store_thm("WORD_LESS_LESS_EQ_TRANS",
  `!a:bool ** 'a b c. a < b /\ b <= c ==> a < c`,
  RW_TAC bool_ss [WORD_LE,WORD_LT] THEN IMP_RES_TAC LESS_LESS_EQ_TRANS
     THEN ASM_REWRITE_TAC [] THEN PROVE_TAC []);

val WORD_LESS_EQ_CASES = store_thm("WORD_LESS_EQ_CASES",
  `!a:bool ** 'a b. a <= b \/ b <= a`,
  RW_TAC bool_ss [WORD_LE] THEN PROVE_TAC [LESS_EQ_CASES]);

val WORD_LESS_CASES = store_thm("WORD_LESS_CASES",
  `!a:bool ** 'a b. a < b \/ b <= a`,
  PROVE_TAC [WORD_LESS_OR_EQ,WORD_LESS_EQ_CASES]);

val WORD_LESS_CASES_IMP = store_thm("WORD_LESS_CASES_IMP",
  `!a:bool ** 'a b. ~(a < b) /\ ~(a = b) ==> b < a`,
  PROVE_TAC [WORD_NOT_LESS,WORD_LESS_OR_EQ]);

val WORD_LESS_ANTISYM = store_thm("WORD_LESS_ANTISYM",
  `!a:bool ** 'a b. ~(a < b /\ b < a)`,
  PROVE_TAC [WORD_NOT_LESS,WORD_LESS_EQ_CASES]);

val WORD_LESS_EQ_ANTISYM = store_thm("WORD_LESS_EQ_ANTISYM",
  `!a:bool ** 'a b. ~(a < b /\ b <= a)`,
  PROVE_TAC [WORD_NOT_LESS]);

val WORD_LESS_EQ_REFL = store_thm("WORD_LESS_EQ_REFL",
  `!a:bool ** 'a. a <= a`,
  REWRITE_TAC [WORD_LESS_OR_EQ]);

val WORD_LESS_EQUAL_ANTISYM = store_thm("WORD_LESS_EQUAL_ANTISYM",
  `!a:bool ** 'a b. a <= b /\ b <= a ==> (a = b)`,
  PROVE_TAC [WORD_LESS_OR_EQ,WORD_LESS_ANTISYM]);

val WORD_LESS_IMP_LESS_OR_EQ = store_thm("WORD_LESS_IMP_LESS_OR_EQ",
  `!a:bool ** 'a b. a < b ==> a <= b`,
  PROVE_TAC [WORD_LESS_OR_EQ]);

val WORD_LESS_REFL = store_thm("WORD_LESS_REFL",
  `!a:bool ** 'a. ~(a < a)`,
  RW_TAC bool_ss [WORD_NOT_LESS,WORD_LESS_OR_EQ]);

val WORD_LESS_LESS_CASES = store_thm("WORD_LESS_LESS_CASES",
  `!a:bool ** 'a b. (a = b) \/ a < b \/ b < a`,
  PROVE_TAC [WORD_LESS_CASES,WORD_LESS_OR_EQ]);

val WORD_NOT_GREATER = store_thm("WORD_NOT_GREATER",
  `!a:bool ** 'a b. ~(a > b) = a <= b`,
  PROVE_TAC [WORD_GREATER,WORD_NOT_LESS]);

val WORD_LESS_NOT_EQ = store_thm("WORD_LESS_NOT_EQ",
  `!a:bool ** 'a b. a < b ==> ~(a = b)`,
  PROVE_TAC [WORD_LESS_REFL,WORD_LESS_OR_EQ]);

val WORD_NOT_LESS_EQ = store_thm("WORD_NOT_LESS_EQ",
  `!a:bool ** 'a b. (a = b) ==> ~(a < b)`,
  PROVE_TAC [WORD_LESS_REFL]);

val WORD_HIGHER = prove(
  `!a b. a >+ b = b <+ a`,
  RW_TAC arith_ss [WORD_HI,WORD_LO]);

val WORD_HIGHER_EQ = store_thm("WORD_HIGHER_EQ",
  `!a b. a >=+ b = b <=+ a`,
  RW_TAC arith_ss [WORD_HS,WORD_LS]);

val WORD_NOT_LOWER = store_thm("WORD_NOT_LOWER",
  `!a b. ~(a <+ b) = b <=+ a`,
  RW_TAC arith_ss [WORD_LO,WORD_LS]);

val WORD_NOT_LOWER_EQUAL = store_thm("WORD_NOT_LOWER_EQUAL",
  `!a b. ~(a <=+ b) = b <+ a`,
  PROVE_TAC [WORD_NOT_LOWER]);

val WORD_LOWER_OR_EQ = store_thm("WORD_LOWER_OR_EQ",
  `!a b. a <=+ b = a <+ b \/ (a = b)`,
  REWRITE_TAC [LESS_OR_EQ,WORD_LS,WORD_LO,w2n_11]);

val WORD_HIGHER_OR_EQ = store_thm("WORD_HIGHER_OR_EQ",
  `!a b. a >=+ b = a >+ b \/ (a = b)`,
  REWRITE_TAC [GREATER_OR_EQ,WORD_HS,WORD_HI,w2n_11]);

val WORD_LOWER_TRANS = store_thm("WORD_LOWER_TRANS",
  `!a b c. a <+ b /\ b <+ c ==> a <+ c`,
  PROVE_TAC [WORD_LO,LESS_TRANS]);

val WORD_LOWER_EQ_TRANS = store_thm("WORD_LOWER_EQ_TRANS",
  `!a b c. a <=+ b /\ b <=+ c ==> a <=+ c`,
  PROVE_TAC [WORD_LS,LESS_EQ_TRANS]);

val WORD_LOWER_EQ_LOWER_TRANS = store_thm("WORD_LOWER_EQ_LOWER_TRANS",
  `!a b c. a <=+ b /\ b <+ c ==> a <+ c`,
  PROVE_TAC [WORD_LS,WORD_LO,LESS_EQ_LESS_TRANS]);

val WORD_LOWER_LOWER_EQ_TRANS = store_thm("WORD_LOWER_LOWER_EQ_TRANS",
  `!a b c. a <+ b /\ b <=+ c ==> a <+ c`,
  PROVE_TAC [WORD_LS,WORD_LO,LESS_LESS_EQ_TRANS]);

val WORD_LOWER_EQ_CASES = store_thm("WORD_LOWER_EQ_CASES",
  `!a b. a <=+ b \/ b <=+ a`,
  RW_TAC bool_ss [WORD_LS,LESS_EQ_CASES]);

val WORD_LOWER_CASES = store_thm("WORD_LOWER_CASES",
  `!a b. a <+ b \/ b <=+ a`,
  PROVE_TAC [WORD_LOWER_OR_EQ,WORD_LOWER_EQ_CASES]);

val WORD_LOWER_CASES_IMP = store_thm("WORD_LOWER_CASES_IMP",
  `!a b. ~(a <+ b) /\ ~(a = b) ==> b <+ a`,
  PROVE_TAC [WORD_NOT_LOWER,WORD_LOWER_OR_EQ]);

val WORD_LOWER_ANTISYM = store_thm("WORD_LOWER_ANTISYM",
  `!a b. ~(a <+ b /\ b <+ a)`,
  PROVE_TAC [WORD_NOT_LOWER,WORD_LOWER_EQ_CASES]);

val WORD_LOWER_EQ_ANTISYM = store_thm("WORD_LOWER_EQ_ANTISYM",
  `!a b. ~(a <+ b /\ b <=+ a)`,
  PROVE_TAC [WORD_NOT_LOWER]);

val WORD_LOWER_EQ_REFL = store_thm("WORD_LOWER_EQ_REFL",
  `!a. a <=+ a`,
  REWRITE_TAC [WORD_LOWER_OR_EQ]);

val WORD_LOWER_EQUAL_ANTISYM = store_thm("WORD_LOWER_EQUAL_ANTISYM",
  `!a b. a <=+ b /\ b <=+ a ==> (a = b)`,
  PROVE_TAC [WORD_LOWER_OR_EQ,WORD_LOWER_ANTISYM]);

val WORD_LOWER_IMP_LOWER_OR_EQ = store_thm("WORD_LOWER_IMP_LOWER_OR_EQ",
  `!a b. a <+ b ==> a <=+ b`,
  PROVE_TAC [WORD_LOWER_OR_EQ]);

val WORD_LOWER_REFL = store_thm("WORD_LOWER_REFL",
  `!a. ~(a <+ a)`,
  RW_TAC bool_ss [WORD_NOT_LOWER,WORD_LOWER_OR_EQ]);

val WORD_LOWER_LOWER_CASES = store_thm("WORD_LOWER_LOWER_CASES",
  `!a b. (a = b) \/ a <+ b \/ b <+ a`,
  PROVE_TAC [WORD_LOWER_CASES,WORD_LOWER_OR_EQ]);

val WORD_NOT_HIGHER = store_thm("WORD_NOT_HIGHER",
  `!a b. ~(a >+ b) = a <=+ b`,
  PROVE_TAC [WORD_HIGHER,WORD_NOT_LOWER]);

val WORD_LOWER_NOT_EQ = store_thm("WORD_LOWER_NOT_EQ",
  `!a b. a <+ b ==> ~(a = b)`,
  PROVE_TAC [WORD_LOWER_REFL,WORD_LOWER_OR_EQ]);

val WORD_NOT_LOWER_EQ = store_thm("WORD_NOT_LOWER_EQ",
  `!a b. (a = b) ==> ~(a <+ b)`,
  PROVE_TAC [WORD_LOWER_REFL]);

(* ------------------------------------------------------------------------- *)

val w2n_word_L = SIMP_CONV arith_ss
  [word_L_def,w2n_n2w,LESS_MOD,SPEC_LESS_EXP_SUC_MONO] ``w2n word_L``;

val w2n_word_H = prove(
  `w2n (word_H:bool ** 'a) = ^MSB - 1`,
  `^MSB - 1 < ^MSB` by SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
    THEN ASSUME_TAC SPEC_LESS_EXP_SUC_MONO THEN IMP_RES_TAC LESS_TRANS
    THEN ASM_SIMP_TAC arith_ss [word_H_def,w2n_n2w,LESS_MOD]);

val WORD_L_PLUS_H = store_thm("WORD_L_PLUS_H",
  `word_L + word_H = word_T`,
  REWRITE_TAC [word_add_def,w2n_word_L,w2n_word_H,n2w_def]
    THEN RW_TAC (fcp_ss++ARITH_ss) [word_T,GSYM EXP,DIMINDEX_GT_0,
           DECIDE ``0 < m ==> (SUC (m - 1) = m)``,ONE_COMP_0_THM]);

fun bound_tac th1 th2 =
  RW_TAC bool_ss [WORD_LE,WORD_L_NEG,WORD_LE,WORD_H_POS,w2n_word_H,w2n_word_L]
    THEN Cases_on `word_msb a` THEN ASM_REWRITE_TAC []
    THEN Cases_on `^HB = 0`
    THEN1 (IMP_RES_TAC th1 THEN ASM_SIMP_TAC arith_ss [])
    THEN Cases_on_word `a`
    THEN FULL_SIMP_TAC bool_ss [w2n_n2w,word_msb_n2w]
    THEN MAP_EVERY IMP_RES_TAC [th2,SLICE_COMP_MSB]
    THEN POP_ASSUM (SPEC_THEN `n` ASSUME_TAC)
    THEN STRIP_ASSUME_TAC EXISTS_HB
    THEN FULL_SIMP_TAC arith_ss [GSYM SLICE_ZERO_THM,GSYM BITS_ZERO3];

val WORD_L_LESS_EQ = store_thm("WORD_L_LESS_EQ",
  `!a:bool ** 'a. word_L <= a`,
  bound_tac MSB_THM1b BIT_SLICE_THM2
);

val WORD_LESS_EQ_H = store_thm("WORD_LESS_EQ_H",
  `!a:bool ** 'a. a <= word_H`,
  bound_tac MSB_THM3b BIT_SLICE_THM3
    THEN `~(m = 0)` by DECIDE_TAC
    THEN METIS_TAC [SUB_LESS_OR,SLICE_MSB_LT,ADD]
);

val WORD_NOT_L_EQ_H = prove(
  `~(word_L = word_H)`,
  SIMP_TAC arith_ss [GSYM w2n_11,w2n_word_L,w2n_word_H,
    GSYM ADD_EQ_SUB,ONE_LT_EQ_TWOEXP]);

val WORD_L_LESS_H = store_thm("WORD_L_LESS_H",
  `word_L < word_H`,
  PROVE_TAC [WORD_L_LESS_EQ,WORD_LESS_EQ_H,WORD_LESS_EQ_TRANS,
    WORD_NOT_L_EQ_H,WORD_LESS_OR_EQ]);

(* ------------------------------------------------------------------------- *)

val WORD_ss = rewrites
  [WORD_LT,WORD_GT,WORD_LE,WORD_GE,WORD_LS,WORD_HI,WORD_LO,WORD_HS,
   word_msb_n2w,w2n_n2w];

val ORDER_WORD_TAC =
  SIMP_TAC (bool_ss++boolSimps.LET_ss++WORD_ss) [] THEN DECIDE_TAC;

val word_lt_n2w = store_thm("word_lt_n2w",
  `!a b. (n2w a):bool ** 'a < n2w b = let sa = BIT ^HB a and sb = BIT ^HB b in
    (sa = sb) /\ a MOD ^TOP < b MOD ^TOP \/ sa /\ ~sb`, ORDER_WORD_TAC);

val word_gt_n2w = store_thm("word_gt_n2w",
  `!a b. (n2w a):bool ** 'a > n2w b = let sa = BIT ^HB a and sb = BIT ^HB b in
    (sa = sb) /\ a MOD ^TOP > b MOD ^TOP \/ ~sa /\ sb`, ORDER_WORD_TAC);

val word_le_n2w = store_thm("word_le_n2w",
  `!a b. (n2w a):bool ** 'a <= n2w b = let sa = BIT ^HB a and sb = BIT ^HB b in
    (sa = sb) /\ a MOD ^TOP <= b MOD ^TOP \/ sa /\ ~sb`, ORDER_WORD_TAC);

val word_ge_n2w = store_thm("word_ge_n2w",
  `!a b. (n2w a):bool ** 'a >= n2w b = let sa = BIT ^HB a and sb = BIT ^HB b in
    (sa = sb) /\ a MOD ^TOP >= b MOD ^TOP \/ ~sa /\ sb`, ORDER_WORD_TAC);

val word_ls_n2w = store_thm("word_ls_n2w",
  `!a b. (n2w a):bool ** 'a <=+ n2w b = a MOD ^TOP <= b MOD ^TOP`,
  ORDER_WORD_TAC);

val word_hi_n2w = store_thm("word_hi_n2w",
  `!a b. (n2w a):bool ** 'a >+ n2w b = a MOD ^TOP > b MOD ^TOP`,
  ORDER_WORD_TAC);

val word_lo_n2w = store_thm("word_lo_n2w",
  `!a b. (n2w a):bool ** 'a <+ n2w b = a MOD ^TOP < b MOD ^TOP`,
  ORDER_WORD_TAC);

val word_hs_n2w = store_thm("word_hs_n2w",
  `!a b. (n2w a):bool ** 'a >=+ n2w b = a MOD ^TOP >= b MOD ^TOP`,
  ORDER_WORD_TAC);

(* ------------------------------------------------------------------------- *)
(* Support for termination proofs                                            *)
(* ------------------------------------------------------------------------- *)

val WORD_PRED_THM = store_thm("WORD_PRED_THM",
  `!m:bool ** 'a. ~(m = 0w) ==> w2n (m - 1w) < w2n m`,
  Cases_word THEN Cases_on `n` THEN  RW_TAC arith_ss [w2n_n2w]
    THEN POP_ASSUM MP_TAC THEN SIMP_TAC arith_ss [ZERO_MOD,ZERO_LT_TWOEXP,
           ADD1,WORD_ADD_SUB,GSYM word_add_n2w,w2n_n2w,n2w_11,
           (SIMP_RULE arith_ss [ZERO_LT_TWOEXP] o SPEC `^TOP`) MOD_ADD_1]);

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
