(* ========================================================================= *)
(* FILE          : wordsScript.sml                                           *)
(* DESCRIPTION   : A model of binary words. Based on John Harrison's         *)
(*                 treatment of finite Cartesian products (TPHOLs 2005)      *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2005                                                      *)
(* ========================================================================= *)

(* interactive use:
  app load ["pred_setTheory", "bitTheory", "sum_numTheory", "fcpLib"];
*)

open HolKernel Parse boolLib bossLib;
open Q arithmeticTheory pred_setTheory;
open bitTheory sum_numTheory fcpTheory;

val _ = new_theory "words";

(* ------------------------------------------------------------------------- *)

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val Abbr = BasicProvers.Abbr;
val fcp_ss = std_ss ++ fcpLib.FCP_ss;

val WL = ``dimindex (UNIV:'a set)``;
val HB = ``^WL - 1``;
val TOP = ``2 ** ^WL``;
val MSB = ``2 ** ^HB``;

fun Def s q = Definition.new_definition(s,Parse.Term q) handle e => Raise e;

val _ = type_abbrev("word", ``:bool ** 'a``);

(* ------------------------------------------------------------------------- *)
(*  Domain transforming maps : definitions                                   *)
(* ------------------------------------------------------------------------- *)

val w2n_def = Def "w2n_def"
  `w2n (w:'a word) = SUM ^WL (\i. SBIT (w %% i) i)`;

val n2w_def = Def "n2w_def"
  `(n2w:num->('a word)) n = FCP i. BIT i n`;

val w2w_def = Define`
  (w2w:'a word -> 'b word) w = n2w (w2n w)`;

val sw2sw_def = Define`
  (sw2sw:'a word -> 'b word) w =
    n2w (SIGN_EXTEND (dimindex(UNIV:'a set))
                     (dimindex(UNIV:'b set)) (w2n w))`;

val _ = add_bare_numeral_form (#"w", SOME "n2w");

(* ------------------------------------------------------------------------- *)
(*  The Boolean operations : definitions                                     *)
(* ------------------------------------------------------------------------- *)

val word_T_def = Define`
  word_T = n2w:num->('a word) (^TOP - 1)`;

val word_L_def = Define`
  word_L = n2w:num->('a word) ^MSB`;

val word_H_def = Define`
  word_H = n2w:num->('a word) (^MSB - 1)`;

val word_1comp_def = Def "word_1comp_def"
  `word_1comp (w:'a word) = (FCP i. ~(w %% i)):'a word`;

val word_and_def = Def "word_and_def"
  `word_and (v:'a word) (w:'a word) =
    (FCP i. (v %% i) /\ (w %% i)):'a word`;

val word_or_def = Def "word_or_def"
  `word_or (v:'a word) (w:'a word) =
    (FCP i. (v %% i) \/ (w %% i)):'a word`;

val word_xor_def = Def "word_xor_def"
  `word_xor (v:'a word) (w:'a word) =
    (FCP i. ~((v %% i) = (w %% i))):'a word`;

val _ = overload_on ("~", Term`$word_1comp`);
val _ = overload_on ("~", Term`bool$~`);
val _ = overload_on ("&&",Term`$word_and`);
val _ = overload_on ("!!",Term`$word_or`);
val _ = overload_on ("??",Term`$word_xor`);
val _ = overload_on ("Tw",Term`word_T`);

val _ = add_infix("&&",400,HOLgrammars.RIGHT);
val _ = add_infix("!!",300,HOLgrammars.RIGHT);
val _ = add_infix("??",300,HOLgrammars.RIGHT);

(* ------------------------------------------------------------------------- *)
(*  Bit field operations : definitions                                       *)
(* ------------------------------------------------------------------------- *)

val word_lsb_def = Def "word_lsb_def"
  `word_lsb (w:'a word) = w %% 0`;

val word_msb_def = Def "word_msb_def"
  `word_msb (w:'a word) = w %% ^HB`;

val word_slice_def = Def "word_slice_def"
  `word_slice h l = \w:'a word.
    (FCP i. l <= i /\ i <= MIN h ^HB /\ w %% i):'a word`;

val word_bits_def = Def "word_bits_def"
  `word_bits h l = \w:'a word.
    (FCP i. i + l <= MIN h ^HB /\ w %% (i + l)):'a word`;

val word_extract_def = Def "word_extract_def"
  `word_extract h l = w2w o word_bits h l`;

val word_bit_def = Def "word_bit_def"
  `word_bit b (w:'a word) = b <= ^HB /\ w %% b`;

val word_reverse_def = Def "word_reverse_def"
  `word_reverse (w:'a word) = (FCP i. w %% (^HB - i)):'a word`;

val word_modify_def = Def "word_modify_def"
  `word_modify f (w:'a word) = (FCP i. f i (w %% i)):'a word`;

val word_len_def = Define`
  word_len (w:'a word) = dimindex (UNIV:'a set)`;

val _ = overload_on ("<>",Term`$word_slice`);
val _ = overload_on ("--",Term`$word_bits`);
val _ = overload_on ("><",Term`$word_extract`);

val _ = add_infix("<>",350,HOLgrammars.RIGHT);
val _ = add_infix("--",350,HOLgrammars.RIGHT);
val _ = add_infix("><",350,HOLgrammars.RIGHT);

(* ------------------------------------------------------------------------- *)
(*  Word arithmetic: definitions                                             *)
(* ------------------------------------------------------------------------- *)

val word_2comp_def = Def "word_2comp_def"
  `word_2comp (w:'a word) =
    n2w:num->('a word) (^TOP - w2n w)`;

val word_add_def = Def "word_add_def"
  `word_add (v:'a word) (w:'a word) =
    n2w:num->('a word) (w2n v + w2n w)`;

val word_sub_def = Define`
  word_sub (v:'a word) (w:'a word) = word_add v (word_2comp w)`;

val word_mul_def = Def "word_mul_def"
  `word_mul (v:'a word) (w:'a word) =
    n2w:num->('a word) (w2n v * w2n w)`;

val word_log2_def = Def "word_log2_def"
  `word_log2 (w:'a word) = (n2w (LOG2 (w2n w)):'a word)`;

val word_div_def = Define`
  word_div (v: 'a word) (w: 'a word) =
    n2w:num->('a word) (w2n v DIV w2n w)`;

val word_sdiv_def = Define`
  word_sdiv a b =
    if word_msb a then
      if word_msb b then
        word_div (word_2comp a) (word_2comp b)
      else
        word_2comp (word_div (word_2comp a) b)
    else
      if word_msb b then
        word_2comp (word_div a (word_2comp b))
      else
        word_div a b`;

val _ = overload_on ("+", Term`$word_add`);
val _ = overload_on ("-", Term`$word_sub`);
val _ = overload_on ("-", Term`$word_2comp`);
val _ = overload_on ("*", Term`$word_mul`);
val _ = overload_on ("//",Term`$word_div`);
val _ = overload_on ("/", Term`$word_sdiv`);

val _ = set_fixity "//" (Infixl 600);
val _ = set_fixity "/"  (Infixl 600);

(* ------------------------------------------------------------------------- *)
(*  Shifts : definitions                                                     *)
(* ------------------------------------------------------------------------- *)

val word_lsl_def = Def "word_lsl_def"
  `word_lsl (w:'a word) n =
    (FCP i. i < ^WL /\ n <= i /\ w %% (i - n)):'a word`;

val word_lsr_def = Def "word_lsr_def"
  `word_lsr (w:'a word) n =
    (FCP i. i + n < ^WL /\ w %% (i + n)):'a word`;

val word_asr_def = Def "word_asr_def"
  `word_asr (w:'a word) n =
    (FCP i. if ^WL <= i + n then
              word_msb w
            else
              w %% (i + n)):'a word`;

val word_ror_def = Def "word_ror_def"
  `word_ror (w:'a word) n =
    (FCP i. w %% ((i + n) MOD ^WL)):'a word`;

val word_rol_def = Def "word_rol_def"
  `word_rol (w:'a word) n =
    word_ror w (^WL - n MOD ^WL)`;

val word_rrx_def = Def "word_rrx_def"
  `word_rrx(c, w:'a word) =
    (word_lsb w,
     (FCP i. if i = ^HB then c else (word_lsr w 1) %% i):'a word)`;

val _ = overload_on ("<<", Term`$word_lsl`);
val _ = overload_on (">>", Term`$word_asr`);
val _ = overload_on (">>>",Term`$word_lsr`);
val _ = overload_on ("#>>",Term`$word_ror`);
val _ = overload_on ("#<<",Term`$word_rol`);

val _ = add_infix("<<", 680,HOLgrammars.LEFT);
val _ = add_infix(">>", 680,HOLgrammars.LEFT);
val _ = add_infix(">>>",680,HOLgrammars.LEFT);
val _ = add_infix("#>>",680,HOLgrammars.LEFT);
val _ = add_infix("#<<",680,HOLgrammars.LEFT);

(* ------------------------------------------------------------------------- *)
(*  Concatenation : definition                                               *)
(* ------------------------------------------------------------------------- *)

val word_join_def = Define`
  (word_join (v:'a word) (w:'b word)):bool ** ('a + 'b) =
    let cv = (w2w v):bool ** ('a + 'b)
    and cw = (w2w w):bool ** ('a + 'b)
    in  (cv << (dimindex (UNIV:'b set))) !! cw`;

val word_concat_def = Define`
  word_concat (v:'a word) (w:'b word) = w2w (word_join v w)`;

val _ = overload_on ("@@",Term`$word_concat`);

val _ = add_infix("@@",700,HOLgrammars.RIGHT);

(* ------------------------------------------------------------------------- *)
(*  Orderings : definitions                                                  *)
(* ------------------------------------------------------------------------- *)

val nzcv_def = Define `
  nzcv (a:'a word) (b:'a word) =
    let q = w2n a + w2n ($- b) in
    let r = (n2w q):'a word in
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

val word_ls_def = Def "word_ls_def"
  `word_ls a b = let (n,z,c,v) = nzcv a b in ~c \/ z`;

val word_hi_def = Def "word_hi_def"
  `word_hi a b = let (n,z,c,v) = nzcv a b in c /\ ~z`;

val word_lo_def = Def "word_lo_def"
  `word_lo a b = let (n,z,c,v) = nzcv a b in ~c`;

val word_hs_def = Def "word_hs_def"
  `word_hs a b = let (n,z,c,v) = nzcv a b in c`;

val _ = overload_on ("<",  Term`word_lt`);
val _ = overload_on (">",  Term`word_gt`);
val _ = overload_on ("<=", Term`word_le`);
val _ = overload_on (">=", Term`word_ge`);
val _ = overload_on ("<=+",Term`word_ls`);
val _ = overload_on (">+", Term`word_hi`);
val _ = overload_on ("<+", Term`word_lo`);
val _ = overload_on (">=+",Term`word_hs`);

val _ = add_infix("<+", 450,HOLgrammars.RIGHT);
val _ = add_infix(">+", 450,HOLgrammars.RIGHT);
val _ = add_infix("<=+",450,HOLgrammars.RIGHT);
val _ = add_infix(">=+",450,HOLgrammars.RIGHT);

(* ------------------------------------------------------------------------- *)
(*  Theorems                                                                 *)
(* ------------------------------------------------------------------------- *)

val DIMINDEX_GT_0 = save_thm("DIMINDEX_GT_0",
  PROVE [DECIDE ``!s. 1 <= s ==> 0 < s``,DIMINDEX_GE_1] ``!s. 0 < dimindex s``);

val DIMINDEX_LT =
  (GEN_ALL o CONJUNCT2 o SPEC_ALL o SIMP_RULE std_ss [DIMINDEX_GT_0] o
   SPEC `^WL`) DIVISION;

val EXISTS_HB = save_thm("EXISTS_HB",
  PROVE [DIMINDEX_GT_0,LESS_ADD_1,ADD1,ADD] ``?m. ^WL = SUC m``);

val MOD_DIMINDEX = store_thm("MOD_DIMINDEX",
  `!n. n MOD 2 ** ^WL = BITS (^WL - 1) 0 n`,
  STRIP_ASSUME_TAC EXISTS_HB \\ ASM_SIMP_TAC arith_ss [BITS_ZERO3]);

val SUB1_SUC = DECIDE (Term `!n. 0 < n ==> (SUC (n - 1) = n)`);
val SUB_SUC1 = DECIDE (Term `!n. ~(n = 0) ==> (SUC (n - 1) = n)`);
val SUC_SUB2 = DECIDE (Term `!n. ~(n = 0) ==> (SUC n - 2 = n - 1)`);

(* ------------------------------------------------------------------------- *)
(*  Domain transforming maps : theorems                                      *)
(* ------------------------------------------------------------------------- *)

val WORD_ss = rewrites [w2n_def,n2w_def];

val SUM_SLICE = prove(
  `!n x. SUM n (\i. SLICE i i x) = x MOD 2 ** n`,
  Induct \\ ASM_SIMP_TAC arith_ss [SUM_def]
    \\ Cases_on `n`
    \\ SIMP_TAC arith_ss [GSYM BITS_ZERO3,GSYM SLICE_ZERO_THM,
         ONCE_REWRITE_RULE [ADD_COMM] SLICE_COMP_THM]);

val SUM_SBIT_LT = prove(
  `!n f. SUM n (\i. SBIT (f i) i) < 2 ** n`,
  Induct \\ ASM_SIMP_TAC arith_ss [SUM_def,ZERO_LT_TWOEXP]
    \\ STRIP_TAC \\ `SBIT (f n) n <= 2 ** n` by RW_TAC arith_ss [SBIT_def]
    \\ METIS_TAC [EXP,DECIDE ``!a b c. a <= b /\ c < b ==> a + c < 2 * b``]);

val w2n_n2w_lem = prove(
  `!n. SUM ^WL (\i. SBIT ((FCP i. BIT i n):'a word %% i) i) =
       SUM ^WL (\i. SLICE i i n)`,
  STRIP_TAC \\ REWRITE_TAC [SUM] \\ MATCH_MP_TAC GSUM_FUN_EQUAL
    \\ RW_TAC (fcp_ss++ARITH_ss) [BIT_SLICE_THM]);

val w2n_n2w = store_thm("w2n_n2w",
  `!n. w2n (n2w:num->('a word) n) = n MOD ^TOP`,
  SIMP_TAC (fcp_ss++WORD_ss) [w2n_n2w_lem,SUM_SLICE]);
val _ = BasicProvers.export_rewrites ["w2n_n2w"]

val n2w_w2n_lem = prove(
  `!n f i. BIT i (SUM n (\j. SBIT (f j) j)) = f i /\ i < n`,
  Induct \\ ASM_SIMP_TAC arith_ss [SUM_def,BIT_ZERO]
    \\ REPEAT STRIP_TAC \\ Cases_on `i < n`
    \\ FULL_SIMP_TAC arith_ss [NOT_LESS,prim_recTheory.LESS_THM]
    << [
      IMP_RES_TAC LESS_ADD_1
        \\ `SBIT (f n) n = (if f n then 1 else 0) * 2 ** p * 2 ** (SUC i)`
        by RW_TAC (std_ss++numSimps.ARITH_AC_ss) [SBIT_def,EXP_ADD,EXP]
        \\ FULL_SIMP_TAC std_ss [BITS_SUM2,BIT_def],
      PAT_ASSUM `!f i. P` (SPECL_THEN [`f`,`i`] ASSUME_TAC)
        \\ `SUM n (\i. SBIT (f i) i) < 2 ** n` by METIS_TAC [SUM_SBIT_LT]
        \\ IMP_RES_TAC LESS_EQUAL_ADD
        \\ `SBIT (f n) n = (if f n then 1 else 0) * 2 ** n`
        by RW_TAC arith_ss [SBIT_def]
        \\ ASM_SIMP_TAC std_ss [BITS_SUM,
             (GSYM o REWRITE_RULE [LESS_EQ_REFL] o
              SPECL [`p`,`n + p`,`n`]) BIT_OF_BITS_THM]
        \\ FULL_SIMP_TAC std_ss [BIT_def,BITS_COMP_THM2]
        \\ Cases_on `p = 0` \\ RW_TAC std_ss [BITS_ZERO2]
        \\ ASM_SIMP_TAC arith_ss [GSYM BIT_def,BIT_B,BIT_B_NEQ]]);

val n2w_w2n = store_thm("n2w_w2n",
  `!w. n2w (w2n (w:'a word)) = w`,
  SIMP_TAC (fcp_ss++WORD_ss) [n2w_w2n_lem]);
val _ = BasicProvers.export_rewrites ["n2w_w2n"]

val word_nchotomy = store_thm("word_nchotomy",
  `!w. ?n. w = n2w n`, PROVE_TAC [n2w_w2n]);

fun Cases_on_word tm = FULL_STRUCT_CASES_TAC (SPEC tm word_nchotomy);
fun Cases_word (g as (_,w)) =
  let val (Bvar,_) = with_exn dest_forall w (ERR "Cases_word" "not a forall")
  in (STRIP_TAC \\ STRUCT_CASES_TAC (Thm.SPEC Bvar word_nchotomy)) g
  end

val n2w_mod = store_thm("n2w_mod",
  `!n. n2w:num -> 'a word (n MOD ^TOP) = n2w n`,
  RW_TAC fcp_ss []
    \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ ASM_SIMP_TAC (fcp_ss++ARITH_ss)
         [n2w_def,MIN_DEF,BIT_def,GSYM BITS_ZERO3,BITS_COMP_THM2]);

val n2w_11 = store_thm("n2w_11",
  `!m n. ((n2w m):bool **'a = n2w n) = (m MOD ^TOP = n MOD ^TOP)`,
  NTAC 2 STRIP_TAC
    \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ ASM_SIMP_TAC (fcp_ss++WORD_ss) [GSYM BITS_ZERO3]
    \\ EQ_TAC \\ RW_TAC arith_ss [DECIDE ``i < SUC p = i <= p``]
    \\ PROVE_TAC [(REWRITE_RULE [ZERO_LESS_EQ] o SPECL [`p`,`0`]) BIT_BITS_THM]
);
val _ = BasicProvers.export_rewrites ["n2w_11"]

val ranged_word_nchotomy = store_thm("ranged_word_nchotomy",
  `!w : bool ** 'a. ?n. (w = n2w n) /\ n < ^TOP`,
  STRIP_TAC
    \\ Q.ISPEC_THEN `w` STRUCT_CASES_TAC word_nchotomy
    \\ SIMP_TAC (srw_ss()) [n2w_11]
    \\ Q.EXISTS_TAC `n MOD 2 ** dimindex (UNIV: 'a set)`
    \\ SIMP_TAC (srw_ss()) [ZERO_LT_TWOEXP, MOD_MOD, MOD_2EXP_LT])

val w2n_11 = store_thm("w2n_11",
  `!v w. (w2n v = w2n w) = (v = w)`,
  REPEAT Cases_word
    \\ REWRITE_TAC [w2n_n2w,n2w_11]);
val _ = BasicProvers.export_rewrites ["w2n_11"]

val w2n_lt = store_thm("w2n_lt",
  `!w:'a word. w2n w < ^TOP`,
  SIMP_TAC std_ss [w2n_def,SUM_SBIT_LT]);

val word_0_n2w = store_thm("word_0_n2w",
  `w2n 0w = 0`, SIMP_TAC arith_ss [w2n_n2w,ZERO_LT_TWOEXP]);

val w2n_eq_0 = store_thm("w2n_eq_0",
  `(w2n w = 0) = (w = 0w)`,
  Q.SPEC_THEN `w` STRUCT_CASES_TAC word_nchotomy \\ SRW_TAC [][]);
val _ = BasicProvers.export_rewrites ["w2n_eq_0"]

val word_add_n2w = store_thm("word_add_n2w",
  `!m n. n2w m + n2w n = n2w (m + n)`,
  SIMP_TAC fcp_ss [word_add_def,w2n_n2w] \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
    \\ SIMP_TAC arith_ss [MOD_PLUS,ZERO_LT_TWOEXP]);

val word_mul_n2w = store_thm("word_mul_n2w",
  `!m n. n2w m * n2w n = n2w (m * n)`,
  SIMP_TAC fcp_ss [word_mul_def,w2n_n2w] \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
    \\ SIMP_TAC arith_ss [MOD_TIMES2,ZERO_LT_TWOEXP]);

val word_log2_n2w = store_thm("word_log2_n2w",
  `!n. word_log2 (n2w n):'a word = (n2w (LOG2 (n MOD ^TOP))):'a word`,
  SIMP_TAC fcp_ss [word_log2_def,w2n_n2w]);

val top = ``2 ** wl``;

val BITWISE_ONE_COMP_THM = prove(
  `!wl a b. 0 < wl ==>
     (BITWISE wl (\x y. ~x) a b = ^top - 1 - a MOD ^top)`,
  REPEAT STRIP_TAC
    \\ `?b. wl = SUC b` by PROVE_TAC [LESS_ADD_1,ADD1,ADD]
    \\ ASM_SIMP_TAC bool_ss [BITWISE_ONE_COMP_LEM,BITS_ZERO3]);

val ONE_COMP_THM = prove(
  `!wl a x. 0 < wl /\ x < wl ==> (BIT x (^top - 1 - a MOD ^top) = ~BIT x a)`,
  REPEAT STRIP_TAC \\ IMP_RES_TAC (GSYM BITWISE_ONE_COMP_THM)
    \\ ASM_REWRITE_TAC []
    \\ ASM_SIMP_TAC bool_ss [BITWISE_THM]);

val word_1comp_n2w = store_thm("word_1comp_n2w",
  `!n. ~(n2w n):'a word  = (n2w (^TOP - 1 - n MOD ^TOP)):'a word`,
  RW_TAC fcp_ss [word_1comp_def,n2w_def,ONE_COMP_THM,DIMINDEX_GT_0]);

val word_2comp_n2w = store_thm("word_2comp_n2w",
  `!n. $- (n2w n):'a word  = (n2w (^TOP - n MOD ^TOP)):'a word`,
  SIMP_TAC std_ss [word_2comp_def,n2w_11,w2n_n2w]);

val word_lsb_n2w = store_thm("word_lsb_n2w",
  `!n. word_lsb ((n2w n):'a word)  = BIT 0 n`,
  SIMP_TAC fcp_ss [word_lsb_def,n2w_def,DIMINDEX_GT_0]);

val word_msb_n2w = store_thm("word_msb_n2w",
  `!n. word_msb ((n2w n):'a word)  = BIT ^HB n`,
  SIMP_TAC (fcp_ss++ARITH_ss) [word_msb_def,n2w_def,DIMINDEX_GT_0]);

val word_msb_n2w_numeric = store_thm(
  "word_msb_n2w_numeric",
  `word_msb (n2w n : 'a word) =
       2 ** (dimindex (UNIV : 'a set) - 1) <=
       n MOD (2 ** dimindex (UNIV : 'a set))`,
  Q.ABBREV_TAC `HB = 2n ** (dimindex (UNIV : 'a set) - 1)` THEN
  Q.ABBREV_TAC `WL = 2n ** dimindex (UNIV : 'a set)` THEN
  `WL = 2 * HB`
     by (SRW_TAC [][Abbr`WL`, Abbr`HB`] THEN
         `0 < dimindex (UNIV : 'a set)` by SRW_TAC [][DIMINDEX_GT_0] THEN
         `?m. dimindex (UNIV : 'a set) = SUC m`
             by (Cases_on `dimindex (UNIV : 'a set)` THEN
                 FULL_SIMP_TAC (srw_ss()) []) THEN
         SRW_TAC [][EXP]) THEN
  `0 < WL` by SRW_TAC [][Abbr`WL`, DIMINDEX_GT_0] THEN
  `(n = (n DIV WL) * WL + n MOD WL) /\ n MOD WL < WL`
     by METIS_TAC [DIVISION] THEN
  Q.ABBREV_TAC `q = n DIV WL` THEN
  Q.ABBREV_TAC `r = n MOD WL` THEN
  ASM_SIMP_TAC (srw_ss())[word_msb_n2w, bitTheory.BIT_def, bitTheory.BITS_def,
             bitTheory.MOD_2EXP_def, bitTheory.DIV_2EXP_def,
             DECIDE ``SUC x - x = 1``, EQ_IMP_THM] THEN REPEAT STRIP_TAC
  THENL [
    SPOSE_NOT_THEN ASSUME_TAC THEN
    `r < HB` by SRW_TAC [ARITH_ss][Abbr`r`] THEN
    `n DIV HB = 2 * q`
       by (SRW_TAC [][] THEN METIS_TAC [DIV_MULT,
                                        MULT_COMM,
                                        MULT_ASSOC]) THEN
    METIS_TAC [DECIDE ``~(0n = 1) /\ 0 < 2n``, MOD_EQ_0, MULT_COMM],

    MATCH_MP_TAC MOD_UNIQUE THEN
    Q.EXISTS_TAC `q` THEN ASM_SIMP_TAC (srw_ss()) [] THEN
    MATCH_MP_TAC DIV_UNIQUE THEN
    Q.EXISTS_TAC `r - HB` THEN
    DECIDE_TAC
  ])

val word_and_n2w = store_thm("word_and_n2w",
  `!n m. (n2w n):'a word && (n2w m) = n2w (BITWISE ^WL (/\) n m)`,
  SIMP_TAC fcp_ss [word_and_def,n2w_11,n2w_def,BITWISE_THM]);

val word_or_n2w = store_thm("word_or_n2w",
  `!n m. (n2w n):'a word !! (n2w m) = n2w (BITWISE ^WL (\/) n m)`,
  SIMP_TAC fcp_ss [word_or_def,n2w_11,n2w_def,BITWISE_THM]);

val word_xor_n2w = store_thm("word_xor_n2w",
  `!n m. (n2w n):'a word ?? (n2w m) =
     n2w (BITWISE ^WL (\x y. ~(x = y)) n m)`,
  SIMP_TAC fcp_ss [word_xor_def,n2w_11,n2w_def,BITWISE_THM]);

(* ------------------------------------------------------------------------- *)
(*  The Boolean operations : theorems                                        *)
(* ------------------------------------------------------------------------- *)

val ONE_COMP_0_THM =
  (SIMP_RULE arith_ss [BIT_ZERO,ZERO_MOD,ZERO_LT_TWOEXP] o
   SPECL [`wl`,`0`]) ONE_COMP_THM;

val word_0 = store_thm("word_0",
  `!i. i < ^WL ==> ~((0w:'a word) %% i)`,
  SIMP_TAC fcp_ss [n2w_def,BIT_ZERO]);

val word_T = store_thm("word_T",
  `!i. i < ^WL ==> (Tw:'a word) %% i`,
  SIMP_TAC fcp_ss [word_T_def,n2w_def,ONE_COMP_0_THM,DIMINDEX_GT_0]);

val WORD_ss =
  rewrites [word_1comp_def,word_and_def,word_or_def,word_xor_def,
    word_0,word_T];

val BOOL_WORD_TAC = SIMP_TAC (fcp_ss++WORD_ss) [] \\ DECIDE_TAC;

val WORD_NOT_NOT = store_thm("WORD_NOT_NOT",
  `!a:'a word. ~(~a) = a`, BOOL_WORD_TAC);

val WORD_DE_MORGAN_THM = store_thm("WORD_DE_MORGAN_THM",
  `!a b. ~(a && b) = ~a !! ~b`, BOOL_WORD_TAC);

val WORD_DE_MORGAN_THM = store_thm("WORD_DE_MORGAN_THM",
  `!a b. ~(a && b) = ~a !! ~b`, BOOL_WORD_TAC);

val WORD_AND_CLAUSES = store_thm("WORD_AND_CLAUSES",
  `!a:'a word.
      (Tw && a = a) /\ (a && Tw = a) /\
      (0w && a = 0w) /\ (a && 0w = 0w) /\
      (a && a = a)`, BOOL_WORD_TAC);

val WORD_OR_CLAUSES = store_thm("WORD_OR_CLAUSES",
  `!a:'a word.
      (Tw !! a = Tw) /\ (a !! Tw = Tw) /\
      (0w !! a = a) /\ (a !! 0w = a) /\
      (a !! a = a)`, BOOL_WORD_TAC);

val WORD_XOR_CLAUSES = store_thm("WORD_XOR_CLAUSES",
  `!a:'a word.
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

val w2w = store_thm("w2w",
  `!w:'a word i. i < dimindex (UNIV:'b set) ==>
      ((w2w w):'b word %% i = i < ^WL /\ w %% i)`,
  Cases_word \\ SIMP_TAC std_ss [w2w_def,w2n_n2w]
    \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ STRIP_ASSUME_TAC (Thm.INST_TYPE [alpha |-> beta] EXISTS_HB)
    \\ RW_TAC (fcp_ss++ARITH_ss) [n2w_def,BIT_def,BITS_COMP_THM2,
         GSYM BITS_ZERO3]
    \\ Cases_on `i < SUC m`
    \\ ASM_SIMP_TAC (fcp_ss++ARITH_ss) [MIN_DEF,BITS_ZERO]);

val WORD_ss = rewrites [word_slice_def,word_bits_def,word_bit_def,
  word_lsl_def,word_lsr_def,word_and_def,word_or_def,word_xor_def,
  word_reverse_def,word_modify_def,n2w_def,w2w,SUC_SUB1,BIT_SLICE_THM4];

val FIELD_WORD_TAC = RW_TAC (fcp_ss++WORD_ss++ARITH_ss) [];

val w2w_id = store_thm("w2w_id",
  `!w:'a word. w2w w:'a word = w`, FIELD_WORD_TAC);

val w2w_w2w = store_thm("w2w_w2w",
  `!w:'a word. (w2w ((w2w w):'b word)):'c word =
        w2w ((dimindex (UNIV:'b set) - 1 -- 0) w)`,
  FIELD_WORD_TAC
    \\ Cases_on `i < ^WL` \\ FIELD_WORD_TAC
    \\ Cases_on `i < dimindex (UNIV:'b set)` \\ FIELD_WORD_TAC
    \\ PROVE_TAC [DECIDE ``0 < n /\ ~(i < n) ==> ~(i <= n - 1)``,
         DIMINDEX_GT_0]);

val word_bit = store_thm("word_bit",
  `!w:'a word b.  b < dimindex (UNIV:'a set) ==>
     (w %% b = word_bit b w)`, RW_TAC arith_ss [word_bit_def]);

val word_slice_n2w = store_thm("word_slice_n2w",
  `!h l n. (h <> l) (n2w n):'a word =
             (n2w (SLICE (MIN h ^HB) l n)):'a word`,
  FIELD_WORD_TAC);

val word_bits_n2w = store_thm("word_bits_n2w",
  `!h l n. (h -- l) (n2w n):'a word =
             (n2w (BITS (MIN h ^HB) l n)):'a word`,
  FIELD_WORD_TAC \\ Cases_on `i + l <= MIN h ^HB`
    \\ FULL_SIMP_TAC (fcp_ss++ARITH_ss) [MIN_DEF,NOT_LESS_EQUAL,
         BIT_OF_BITS_THM,BIT_OF_BITS_THM2]);

val word_bit_n2w = store_thm("word_bit_n2w",
  `!b n. word_bit b ((n2w n):'a word) = b <= ^HB /\ BIT b n`,
  FIELD_WORD_TAC \\ Cases_on `b <= ^HB`
    \\ ASM_SIMP_TAC fcp_ss [DIMINDEX_GT_0,
         DECIDE ``0 < b /\ a <= b - 1 ==> a < b:num``]);

val word_index_n2w = store_thm("word_index_n2w",
  `!n. (n2w n):'a word %% i =
      if i < dimindex (UNIV:'a set) then
        BIT i n
      else
        (n2w n):'a word %% i`,
  RW_TAC arith_ss [word_bit,word_bit_n2w]);

val MIN_lem = prove(
 `(!m n. MIN m (m + n) = m) /\ !m n. MIN (m + n) m = m`,
  RW_TAC arith_ss [MIN_DEF]);

val MIN_lem2 = prove(
  `MIN a (MIN b (MIN (c + a) (c + b))) = MIN a b`,
  RW_TAC arith_ss [MIN_DEF]);

val word_bits_w2w = store_thm("word_bits_w2w",
  `!w. (h -- l) (w2w (w:'a word)):'b word =
       w2w ((MIN h (dimindex (UNIV:'b set) - 1) -- l) w)`,
  Cases_word \\ SIMP_TAC arith_ss [word_bits_n2w,w2w_def,w2n_n2w]
    \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ STRIP_ASSUME_TAC (Thm.INST_TYPE [alpha |-> beta] EXISTS_HB)
    \\ ASM_SIMP_TAC arith_ss [n2w_11,GSYM BITS_ZERO3,BITS_COMP_THM2,
         AC MIN_ASSOC MIN_COMM,ONCE_REWRITE_RULE [ADD_COMM] MIN_lem,
         MIN_lem2]);

val word_reverse_n2w = store_thm("word_reverse_n2w",
  `!n. word_reverse ((n2w n):'a word) =
         (n2w (BIT_REVERSE ^WL n)):'a word`,
  FIELD_WORD_TAC \\ ASM_SIMP_TAC arith_ss [BIT_REVERSE_THM]);

val word_modify_n2w = store_thm("word_modify_n2w",
  `!f n. word_modify f ((n2w n):'a word) =
         (n2w (BIT_MODIFY ^WL f n)):'a word`,
  FIELD_WORD_TAC \\ ASM_SIMP_TAC arith_ss [BIT_MODIFY_THM]);

val fcp_n2w = store_thm("fcp_n2w",
  `!f. $FCP f = word_modify (\i b. f i) 0w`,
  RW_TAC fcp_ss [word_modify_def]);

val w2n_w2w = store_thm("w2n_w2w",
  `!w:'a word. w2n ((w2w w):'b word) =
      if ^WL <= dimindex (UNIV:'b set) then
        w2n w
      else
        w2n ((dimindex (UNIV:'b set) - 1 -- 0) w)`,
  Cases_word
    \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ STRIP_ASSUME_TAC (Thm.INST_TYPE [alpha |-> beta] EXISTS_HB)
    \\ ASM_SIMP_TAC arith_ss [BITS_COMP_THM2,w2w_def,word_bits_n2w,
          REWRITE_RULE [MOD_DIMINDEX] w2n_n2w]
    \\ RW_TAC arith_ss [MIN_DEF]
    \\ `m' = m` by DECIDE_TAC \\ ASM_REWRITE_TAC []);

val w2w_n2w = store_thm("w2w_n2w",
  `!n. w2w ((n2w n):'a word):'b word =
         if dimindex (UNIV:'b set) <= ^WL then
           n2w n
         else
           n2w (BITS (^WL - 1) 0 n)`,
  RW_TAC arith_ss [MIN_DEF,MOD_DIMINDEX,BITS_COMP_THM2,w2n_n2w,w2w_def,n2w_11]);

val WORD_EQ = store_thm("WORD_EQ",
  `!v:'a word w. (!x. x < ^WL ==> (word_bit x v = word_bit x w)) = (v = w)`,
  REPEAT Cases_word \\ FIELD_WORD_TAC);

val TWO_EXP_DIMINDEX = prove(
  `2 <= ^TOP`,
  METIS_TAC [EXP_BASE_LE_MONO, DECIDE ``1 < 2``, EXP_1, DIMINDEX_GE_1])

val lem = GEN_ALL (MATCH_MP LESS_LESS_EQ_TRANS (CONJ
  ((REWRITE_RULE [SUC_SUB,EXP_1] o SPECL [`b`,`b`,`n`]) BITSLT_THM)
  TWO_EXP_DIMINDEX));

val lem2 = GEN_ALL (MATCH_MP LESS_LESS_EQ_TRANS (CONJ
   (DECIDE ``1 < 2``) TWO_EXP_DIMINDEX));

val WORD_BIT_BITS = store_thm("WORD_BIT_BITS",
  `!b w. word_bit b w = ((b -- b) w = 1w)`,
  STRIP_TAC \\ Cases_word
    \\ RW_TAC arith_ss [MIN_DEF,BIT_def,word_bit_n2w,word_bits_n2w,n2w_11,
         LESS_MOD,lem,lem2]
    \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ FULL_SIMP_TAC arith_ss [MIN_DEF,GSYM BITS_ZERO3,SUC_SUB1,BITS_COMP_THM2]
    \\ Cases_on `b = 0` \\ FULL_SIMP_TAC arith_ss []
    << [`m = 0` by DECIDE_TAC \\ ASM_REWRITE_TAC [],
      Cases_on `m = b` \\ ASM_SIMP_TAC arith_ss [BITS_ZERO]]);

val lem = prove(`MIN d (l1 + MIN h2 d) = MIN (h2 + l1) d`,
  RW_TAC arith_ss [MIN_DEF]);

val WORD_BITS_COMP_THM = store_thm("WORD_BITS_COMP_THM",
  `!h1 l1 h2 l2 w. (h2 -- l2) ((h1 -- l1) w) =
                   ((MIN h1 (h2 + l1)) -- (l2 + l1)) w`,
  REPEAT STRIP_TAC \\ Cases_on_word `w`
    \\ RW_TAC arith_ss [word_bits_n2w,lem,BITS_COMP_THM2,
         AC MIN_ASSOC MIN_COMM]);

val WORD_BITS_LSR = store_thm("WORD_BITS_LSR",
  `!h l w. (h -- l) w >>> n = (h -- (l + n)) w`,
  FIELD_WORD_TAC \\ Cases_on `i + n < dimindex (UNIV:'a set)`
    \\ ASM_SIMP_TAC (fcp_ss++ARITH_ss) []);

val WORD_BITS_ZERO = store_thm("WORD_BITS_ZERO",
  `!h l w. h < l ==> ((h -- l) w = 0w)`,
  NTAC 2 STRIP_TAC \\ Cases_word
    \\ RW_TAC arith_ss [word_bits_n2w,BITS_ZERO,MIN_DEF]);

val WORD_BITS_LT = store_thm("WORD_BITS_LT",
  `!h l w. w2n ((h -- l) w) < 2 ** (SUC h - l)`,
  NTAC 2 STRIP_TAC \\ Cases_word
    \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ RW_TAC arith_ss [word_bits_n2w,w2n_n2w,GSYM BITS_ZERO3,
         BITS_COMP_THM2,MIN_DEF,BITSLT_THM]
    \\ FULL_SIMP_TAC std_ss []
    << [`SUC m - l <= SUC h - l` by DECIDE_TAC,
     `SUC (l + m) - l <= SUC h - l` by DECIDE_TAC]
    \\ PROVE_TAC [TWOEXP_MONO2,BITSLT_THM,LESS_LESS_EQ_TRANS]);

val WORD_SLICE_THM = store_thm("WORD_SLICE_THM",
  `!h l w. (h <> l) w = (h -- l) w << l`,
  FIELD_WORD_TAC \\ Cases_on `l <= i` \\ ASM_SIMP_TAC arith_ss []);

val WORD_SLICE_ZERO = store_thm("WORD_SLICE_ZERO",
  `!h l w. h < l ==> ((h <> l) w = 0w)`,
  NTAC 2 STRIP_TAC \\ Cases_word
    \\ RW_TAC arith_ss [word_slice_n2w,SLICE_ZERO,MIN_DEF]);

val WORD_SLICE_BITS_THM = store_thm("WORD_SLICE_BITS_THM",
  `!h w. (h <> 0) w = (h -- 0) w`, FIELD_WORD_TAC);

val WORD_BITS_SLICE_THM = store_thm("WORD_BITS_SLICE_THM",
  `!h l w. (h -- l) ((h <> l) w) = (h -- l) w`,
  NTAC 2 STRIP_TAC \\ Cases_word
    \\ RW_TAC arith_ss [word_slice_n2w,word_bits_n2w,BITS_SLICE_THM]);

val WORD_SLICE_COMP_THM = store_thm("WORD_SLICE_COMP_THM",
  `!h m' m l w:'a word. l <= m /\ (m' = m + 1) /\ m < h ==>
     (((h <> m') w):'a word !! (m <> l) w =
      ((h <> l) w):'a word)`,
  FIELD_WORD_TAC \\ `i <= m \/ m + 1 <= i` by DECIDE_TAC
    \\ ASM_SIMP_TAC arith_ss []);

val word_extract = (GSYM o SIMP_RULE std_ss [] o
  REWRITE_RULE [FUN_EQ_THM]) word_extract_def;

val WORD_EXTRACT_BITS_COMP = save_thm("WORD_EXTRACT_BITS_COMP",
 (SIMP_RULE std_ss [word_extract] o
  SIMP_CONV std_ss [word_extract_def,WORD_BITS_COMP_THM])
  ``(j >< k) ((h -- l) n)``);

val WORD_SLICE_OVER_BITWISE = store_thm("WORD_SLICE_OVER_BITWISE",
  `(!h l v:'a word w:'a word.
      (h <> l) v && (h <> l) w = (h <> l) (v && w)) /\
   (!h l v:'a word w:'a word.
      (h <> l) v !! (h <> l) w = (h <> l) (v !! w)) /\
   (!h l v:'a word w:'a word.
      (h <> l) v ?? (h <> l) w = (h <> l) (v ?? w))`,
  FIELD_WORD_TAC << [PROVE_TAC [], PROVE_TAC [], ALL_TAC]
    \\ Cases_on `l <= i /\ i <= h` \\ FULL_SIMP_TAC arith_ss []);

val WORD_BITS_OVER_BITWISE = store_thm("WORD_BITS_OVER_BITWISE",
  `(!h l v:'a word w:'a word.
      (h -- l) v && (h -- l) w = (h -- l) (v && w)) /\
   (!h l v:'a word w:'a word.
      (h -- l) v !! (h -- l) w = (h -- l) (v !! w)) /\
   (!h l v:'a word w:'a word.
      (h -- l) v ?? (h -- l) w = (h -- l) (v ?? w))`,
  FIELD_WORD_TAC
    \\ Cases_on `i + l <= h /\ i + l <= dimindex (UNIV:'a set) - 1`
    \\ FULL_SIMP_TAC (fcp_ss++ARITH_ss) []);

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
  LET_TAC \\ REPEAT STRIP_TAC
    \\ ONCE_REWRITE_TAC [GSYM MOD_ADD]
    \\ POP_ASSUM (fn th => REWRITE_TAC [SYM th])
    \\ SIMP_TAC std_ss [MOD_ADD,ADD1,GSYM LESS_EQ_ADD_SUB,ONE_LT_EQ_TWOEXP]
    \\ SIMP_TAC arith_ss [ADD_MODULUS,ZERO_LT_TWOEXP]));

val INV_SUC_EQ_mod = LET_RULE (prove(
  `!m n. let $== = ^equiv in
           (SUC m == SUC n) = (m == n)`,
  LET_TAC \\ REPEAT STRIP_TAC \\ EQ_TAC << [
    STRIP_TAC \\ IMP_RES_TAC SUC_EQUIV_mod
      \\ FULL_SIMP_TAC arith_ss [GSYM LESS_EQ_ADD_SUB,ADD1,ADD_MODULUS,
           ZERO_LT_TWOEXP,ONE_LT_EQ_TWOEXP],
    REWRITE_TAC [ADD1] \\ ONCE_REWRITE_TAC [GSYM MOD_ADD]
      \\ RW_TAC std_ss []]));

val ADD_INV_0_mod = LET_RULE (prove(
  `!m n. let $== = ^equiv in
           (m + n == m) ==> (n == 0)`,
  LET_TAC \\ Induct \\ RW_TAC bool_ss [ADD_CLAUSES]
    \\ FULL_SIMP_TAC bool_ss [INV_SUC_EQ_mod]));

val ADD_INV_0_EQ_mod = LET_RULE (prove(
  `!m n. let $== = ^equiv in
           (m + n == m) = (n == 0)`,
  LET_TAC \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC
    \\ IMP_RES_TAC ADD_INV_0_mod
    \\ ONCE_REWRITE_TAC [GSYM MOD_ADD]
    \\ ASM_SIMP_TAC arith_ss [ZERO_MOD,ADD_MODULUS,ZERO_LT_TWOEXP]));

val EQ_ADD_LCANCEL_mod = LET_RULE (prove(
  `!m n p. let $== = ^equiv in
           (m + n == m + p) = (n == p)`,
  LET_TAC \\ Induct \\ ASM_REWRITE_TAC [ADD_CLAUSES,INV_SUC_EQ_mod]));

val WORD_NEG_mod = LET_RULE (prove(
  `!n. let $== = ^equiv in
         ^top - n MOD ^top == (^top - 1 - n MOD ^top) + 1`,
  LET_TAC \\ STRIP_TAC
    \\ `1 + n MOD ^top <= ^top`
    by SIMP_TAC std_ss [DECIDE ``a < b ==> 1 + a <= b``,MOD_2EXP_LT]
    \\ ASM_SIMP_TAC arith_ss [SUB_RIGHT_SUB,SUB_RIGHT_ADD]
    \\ Tactical.REVERSE (Cases_on `1 + n MOD ^top = ^top`)
    >> FULL_SIMP_TAC arith_ss []
    \\ RULE_ASSUM_TAC
         (SIMP_RULE bool_ss [GSYM SUC_ONE_ADD,GSYM PRE_SUC_EQ,ZERO_LT_TWOEXP])
    \\ ASM_SIMP_TAC arith_ss [PRE_SUB1]));

val n2w_TOP = prove(
  `n2w ^TOP = 0w:'a word`,
  ONCE_REWRITE_TAC [GSYM n2w_mod]
    \\ SIMP_TAC std_ss [DIVMOD_ID,ZERO_MOD,ZERO_LT_TWOEXP]);

val WORD_ss = rewrites [word_add_n2w,word_mul_n2w,word_sub_def,word_2comp_def,
  w2n_n2w,n2w_w2n,word_0,n2w_TOP,ZERO_LT_TWOEXP,
  LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB,
  LEFT_SUB_DISTRIB,RIGHT_SUB_DISTRIB];

val ARITH_WORD_TAC =
  REPEAT Cases_word
    \\ ASM_SIMP_TAC (fcp_ss++ARITH_ss++numSimps.ARITH_AC_ss++WORD_ss) [];

(* -- *)

val WORD_ADD_0 = store_thm("WORD_ADD_0",
  `(!w:'a word. w + 0w = w) /\ (!w:'a word. 0w + w = w)`,
   CONJ_TAC \\ ARITH_WORD_TAC);

val WORD_ADD_ASSOC = store_thm("WORD_ADD_ASSOC",
  `!v:'a word w x. v + (w + x) = v + w + x`, ARITH_WORD_TAC);

val WORD_MULT_ASSOC = store_thm("WORD_MULT_ASSOC",
  `!v:'a word w x. v * (w * x) = v * w * x`,
  REPEAT Cases_word \\ ASM_SIMP_TAC (fcp_ss++WORD_ss) [MULT_ASSOC]);

val WORD_ADD_COMM = store_thm("WORD_ADD_COMM",
  `!v:'a word w. v + w = w + v`, ARITH_WORD_TAC);

val WORD_MULT_COMM = store_thm("WORD_MULT_COMM",
  `!v:'a word w. v * w = w * v`, ARITH_WORD_TAC);

val WORD_MULT_CLAUSES = store_thm("WORD_MULT_CLAUSES",
  `!v:'a word w.
     (0w * v = 0w) /\ (v * 0w = 0w) /\
     (1w * v = v) /\ (v * 1w = v) /\
     ((v + 1w) * w = v * w + w) /\ (v * (w + 1w) = v + v * w)`,
  ARITH_WORD_TAC);

val WORD_LEFT_ADD_DISTRIB = store_thm("WORD_LEFT_ADD_DISTRIB",
  `!v:'a word w x. v * (w + x) = v * w + v * x`, ARITH_WORD_TAC);

val WORD_RIGHT_ADD_DISTRIB = store_thm("WORD_RIGHT_ADD_DISTRIB",
  `!v:'a word w x. (v + w) * x = v * x + w * x`, ARITH_WORD_TAC);

val WORD_ADD_SUB_ASSOC = store_thm("WORD_ADD_SUB_ASSOC",
  `!v:'a word w x. v + w - x = v + (w - x)`, ARITH_WORD_TAC);

val WORD_ADD_SUB_SYM = store_thm("WORD_ADD_SUB_SYM",
  `!v:'a word w x. v + w - x = v - x + w`, ARITH_WORD_TAC);

val WORD_ADD_LINV = store_thm("WORD_ADD_LINV",
  `!w:'a word. $- w + w = 0w`,
  ARITH_WORD_TAC
    \\ STRIP_ASSUME_TAC
         ((REWRITE_RULE [ZERO_LT_TWOEXP] o SPECL [`n`,`^TOP`]) DA)
    \\ ASM_SIMP_TAC std_ss [MOD_MULT]
    \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
    \\ ASM_SIMP_TAC arith_ss [GSYM MULT,MOD_EQ_0,ZERO_LT_TWOEXP,word_0]);

val WORD_ADD_RINV = store_thm("WORD_ADD_RINV",
  `!w:'a word. w + $- w = 0w`,
  METIS_TAC [WORD_ADD_COMM,WORD_ADD_LINV]);

val WORD_SUB_REFL = store_thm("WORD_SUB_REFL",
  `!w:'a word. w - w = 0w`,
  REWRITE_TAC [word_sub_def,WORD_ADD_RINV]);

val WORD_SUB_ADD2 = store_thm("WORD_SUB_ADD2",
  `!v:'a word w. v + (w - v) = w`,
  REWRITE_TAC [GSYM WORD_ADD_SUB_ASSOC,WORD_ADD_SUB_SYM,
    WORD_SUB_REFL,WORD_ADD_0]);

val WORD_ADD_SUB = store_thm("WORD_ADD_SUB",
  `!v:'a word w. v + w - w = v`,
  REWRITE_TAC [WORD_ADD_SUB_ASSOC,WORD_SUB_REFL,WORD_ADD_0]);

val WORD_SUB_ADD = save_thm("WORD_SUB_ADD",
  REWRITE_RULE [WORD_ADD_SUB_SYM] WORD_ADD_SUB);

val WORD_ADD_EQ_SUB = store_thm("WORD_ADD_EQ_SUB",
  `!v:'a word w x. (v + w = x) = (v = (x - w))`,
  METIS_TAC [WORD_ADD_SUB,WORD_SUB_ADD]);

val WORD_ADD_INV_0_EQ = store_thm("WORD_ADD_INV_0_EQ",
  `!v:'a word w. (v + w = v) = (w = 0w)`,
  REPEAT Cases_word
    \\ ASM_SIMP_TAC std_ss [word_add_n2w,lift_rule ADD_INV_0_EQ_mod]);

val WORD_EQ_ADD_LCANCEL = store_thm("WORD_EQ_ADD_LCANCEL",
  `!v:'a word w x. (v + w = v + x) = (w = x)`,
  REPEAT Cases_word
    \\ ASM_SIMP_TAC std_ss [word_add_n2w,lift_rule EQ_ADD_LCANCEL_mod]);

val WORD_EQ_ADD_RCANCEL = store_thm("WORD_EQ_ADD_RCANCEL",
  `!v:'a word w x. (v + w = x + w) = (v = x)`,
  METIS_TAC [WORD_ADD_COMM,WORD_EQ_ADD_LCANCEL]);

val WORD_NEG = store_thm("WORD_NEG",
  `!w:'a word. $- w = ~w + 1w`,
  REPEAT Cases_word
    \\ ASM_SIMP_TAC (fcp_ss++ARITH_ss) [word_add_n2w,word_2comp_n2w,
         word_1comp_n2w,lift_rule WORD_NEG_mod]);

val WORD_NOT = store_thm("WORD_NOT",
  `!w:'a word. ~w = $- w - 1w`,
  REWRITE_TAC [WORD_NEG,WORD_ADD_SUB]);

val WORD_NEG_0 = store_thm("WORD_NEG_0",
  `$- 0w = 0w`,
   ARITH_WORD_TAC);
val _ = BasicProvers.export_rewrites ["WORD_NEG_0"]

val WORD_NEG_ADD = store_thm("WORD_NEG_ADD",
  `!v:'a word w. $- (v + w) = $- v + $- w`,
  REPEAT STRIP_TAC
    \\ `$- v + v + ($-w + w) = 0w`
    by REWRITE_TAC [WORD_ADD_LINV,WORD_ADD_0]
    \\ `$- v + v + ($-w + w) = $- v + $- w + (v + w)`
    by SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]
    \\ METIS_TAC [GSYM WORD_ADD_LINV,WORD_EQ_ADD_RCANCEL]);

val WORD_NEG_NEG = store_thm("WORD_NEG_NEG",
  `!w:'a word. $- ($- w) = w`,
  STRIP_TAC
    \\ `$- ($- w) + $- w = w + $- w`
    by SIMP_TAC std_ss [WORD_NEG_0,WORD_ADD_0,WORD_ADD_LINV,WORD_ADD_RINV]
    \\ METIS_TAC [WORD_EQ_ADD_RCANCEL]);
val _ = BasicProvers.export_rewrites ["WORD_NEG_NEG"]

val WORD_SUB_LNEG = save_thm("WORD_SUB_LNEG",
  (REWRITE_RULE [GSYM word_sub_def] o GSYM) WORD_NEG_ADD);

val WORD_SUB_RNEG = save_thm("WORD_SUB_RNEG",
  (GEN `v` o GEN `w` o REWRITE_RULE [WORD_NEG_NEG] o
   SPECL [`v`,`$- w`]) word_sub_def);

val WORD_SUB_SUB = store_thm("WORD_SUB_SUB",
  `!v:'a word w x. v - (w - x) = v + x - w`,
  SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM,
    word_sub_def,WORD_NEG_ADD,WORD_NEG_NEG]);

val WORD_SUB_SUB2 = save_thm("WORD_SUB_SUB2",
 (GEN `v` o GEN `w` o REWRITE_RULE [WORD_ADD_SUB_SYM,WORD_SUB_REFL,WORD_ADD_0] o
  SPECL [`v`,`v`,`w`]) WORD_SUB_SUB);

val WORD_EQ_SUB_LADD = store_thm("WORD_EQ_SUB_LADD",
  `!v:'a word w x. (v = w - x) = (v + x = w)`,
  METIS_TAC [word_sub_def,WORD_ADD_ASSOC,WORD_ADD_LINV,WORD_ADD_RINV,WORD_ADD_0]);

val WORD_EQ_SUB_RADD = store_thm("WORD_EQ_SUB_RADD",
  `!v:'a word w x. (v - w = x) = (v = x + w)`,
  METIS_TAC [WORD_EQ_SUB_LADD]);

val WORD_LCANCEL_SUB = store_thm("WORD_LCANCEL_SUB",
  `!v:'a word w x. (v - w = x - w) = (v = x)`,
  REWRITE_TAC [word_sub_def,WORD_EQ_ADD_RCANCEL]);

val WORD_RCANCEL_SUB = store_thm("WORD_RCANCEL_SUB",
  `!v:'a word w x. (v - w = v - x) = (w = x)`,
  REWRITE_TAC [word_sub_def,WORD_EQ_ADD_LCANCEL]
    \\ METIS_TAC [WORD_NEG_NEG]);

val WORD_SUB_PLUS = store_thm("WORD_SUB_PLUS",
  `!v:'a word w x. v - (w + x) = v - w - x`,
  REWRITE_TAC [word_sub_def,WORD_NEG_ADD,WORD_ADD_ASSOC]);

val WORD_SUB_LZERO = store_thm("WORD_SUB_LZERO",
  `!w:'a word. 0w - w = $- w`,
  REWRITE_TAC [word_sub_def,WORD_ADD_0]);

val WORD_SUB_RZERO = store_thm("WORD_SUB_RZERO",
  `!w:'a word. w - 0w = w`,
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
  `!v:'a word w. ($- v = $- w) = (v = w)`,
  REWRITE_TAC [GSYM WORD_SUB_LZERO,WORD_RCANCEL_SUB]);

val WORD_NEG_EQ = save_thm("WORD_NEG_EQ",
  (REWRITE_RULE [WORD_NEG_NEG] o SPECL [`v`,`$- w`]) WORD_EQ_NEG);

val WORD_NEG_EQ_0 = save_thm("WORD_NEG_EQ_0",
  (REWRITE_RULE [WORD_NEG_0] o SPECL [`v`,`0w`]) WORD_EQ_NEG);
val _ = BasicProvers.export_rewrites ["WORD_NEG_EQ_0"]

val WORD_SUB = save_thm("WORD_SUB",
  (ONCE_REWRITE_RULE [WORD_ADD_COMM] o GSYM) word_sub_def);

val WORD_SUB_NEG = save_thm("WORD_SUB_NEG",
  (GEN_ALL o REWRITE_RULE [WORD_SUB] o SPEC `$- v`) WORD_SUB_RNEG);

val WORD_NEG_SUB = save_thm("WORD_NEG_SUB",
  (REWRITE_RULE [WORD_SUB_NEG,GSYM word_sub_def] o
   SPECL [`v`,`$- w`] o GSYM) WORD_SUB_LNEG);

val WORD_SUB_TRIANGLE = store_thm("WORD_SUB_TRIANGLE",
  `!v:'a word w x. v - w + (w - x) = v - x`,
  REWRITE_TAC [GSYM WORD_ADD_SUB_SYM,WORD_ADD_SUB_ASSOC,WORD_SUB_SUB3]
    \\ REWRITE_TAC [word_sub_def]);

val WORD_NEG_1 = store_thm("WORD_NEG_1",
  `$- 1w:'a word = Tw:'a word`,
  REWRITE_TAC [word_T_def,word_2comp_def,w2n_n2w]
    \\ Cases_on `2 ** dimindex (UNIV:'a set) = 1`
    >> ASM_SIMP_TAC arith_ss [n2w_11]
    \\ ASM_SIMP_TAC arith_ss [DECIDE ``0 < x /\ ~(x = 1) ==> 1 < x``,
         LESS_MOD,ZERO_LT_TWOEXP]);

val WORD_NOT_0 = save_thm("WORD_NOT_0",
  (GEN_ALL o REWRITE_RULE [WORD_NEG_1,WORD_NEG_0,WORD_SUB_LZERO] o
   SPEC `0w`) WORD_NOT);

val WORD_NOT_T = store_thm("WORD_NOT_T",
  `~Tw = 0w`, REWRITE_TAC [GSYM WORD_NOT_0,WORD_NOT_NOT]);

val WORD_NEG_T = store_thm("WORD_NEG_T",
  `$- Tw = 1w`, REWRITE_TAC [GSYM WORD_NEG_1,WORD_NEG_NEG]);

val WORD_MULT_SUC  = store_thm("WORD_MULT_SUC",
  `!v:'a word n. v * n2w (n + 1) = v * n2w n + v`,
  Cases_word \\
    SIMP_TAC arith_ss [word_mul_n2w,word_add_n2w,LEFT_ADD_DISTRIB]);

val WORD_NEG_LMUL = store_thm("WORD_NEG_LMUL",
  `!v:'a word w. $- (v * w) = ($- v) * w`,
  REPEAT Cases_word
    \\ Induct_on `n'` >> REWRITE_TAC [WORD_MULT_CLAUSES,WORD_NEG_0]
    \\ ASM_REWRITE_TAC [WORD_NEG_ADD,ADD1,WORD_MULT_SUC,GSYM word_mul_n2w]);

val WORD_NEG_RMUL = save_thm("WORD_NEG_RMUL",
  (GEN `v` o GEN `w` o ONCE_REWRITE_RULE [WORD_MULT_COMM] o
    SPECL [`w`,`v`]) WORD_NEG_LMUL);

val WORD_LEFT_SUB_DISTRIB = store_thm("WORD_LEFT_SUB_DISTRIB",
  `!v:'a word w x. v * (w - x) = v * w - v * x`,
  REWRITE_TAC [word_sub_def,WORD_LEFT_ADD_DISTRIB,WORD_NEG_RMUL]);

val WORD_RIGHT_SUB_DISTRIB = save_thm("WORD_RIGHT_SUB_DISTRIB",
  ONCE_REWRITE_RULE [WORD_MULT_COMM] WORD_LEFT_SUB_DISTRIB);

(* ------------------------------------------------------------------------- *)
(*  Shifts : theorems                                                        *)
(* ------------------------------------------------------------------------- *)

val WORD_ss = rewrites [word_msb_def,word_lsl_def,word_lsr_def,word_asr_def,
  word_ror_def,word_rol_def,word_rrx_def,word_T,word_or_def,word_lsb_def,
  word_and_def,word_xor_def,n2w_def,DIMINDEX_GT_0,BIT_ZERO,DIMINDEX_LT,
  MOD_PLUS_RIGHT];

val SHIFT_WORD_TAC = RW_TAC (fcp_ss++ARITH_ss++WORD_ss) [];

val ASR_ADD = store_thm("ASR_ADD",
  `!w m n. w >> m >> n = w >> (m + n)`,
  NTAC 2 SHIFT_WORD_TAC
    \\ FULL_SIMP_TAC arith_ss [DECIDE ``!m. m < 1 = (m = 0)``,NOT_LESS_EQUAL]);

val LSR_ADD = store_thm("LSR_ADD",
  `!w m n. w >>> m >>> n = w >>> (m + n)`,
  SHIFT_WORD_TAC \\ Cases_on `i + n < ^WL`
    \\ SHIFT_WORD_TAC);

val ROR_ADD = store_thm("ROR_ADD",
  `!w m n. w #>> m #>> n = w #>> (m + n)`,
  SHIFT_WORD_TAC);

val LSL_ADD = store_thm("LSL_ADD",
  `!w m n. w << m << n = w << (m + n)`,
  SHIFT_WORD_TAC \\ EQ_TAC \\ RW_TAC arith_ss []);

val ASR_LIMIT = store_thm("ASR_LIMIT",
  `!w:'a word n. ^WL < n ==>
           (w >> n = if word_msb w then Tw else 0w)`,
  SHIFT_WORD_TAC);

val ASR_TRUE = store_thm("ASR_TRUE",
  `!w:'a word n. Tw >> n = Tw`, SHIFT_WORD_TAC);

val LSR_LIMIT = store_thm("LSR_LIMIT",
  `!w:'a word n. ^WL < n ==> (w >>> n = 0w)`,
  SHIFT_WORD_TAC);

val LSL_LIMIT = store_thm("LSL_LIMIT",
  `!w:'a word n. ^WL <= n ==> (w << n = 0w)`,
  SHIFT_WORD_TAC);

val MOD_TIMES_COMM = ONCE_REWRITE_RULE [ADD_COMM] MOD_TIMES;

val ROR_CYCLE = store_thm("ROR_CYCLE",
  `!w:'a word n. (w #>> (n * ^WL) = w)`,
  SHIFT_WORD_TAC \\ ASM_SIMP_TAC arith_ss [MOD_TIMES_COMM,DIMINDEX_GT_0]);

val ROR_MOD = store_thm("ROR_MOD",
  `!w:'a word n. (w #>> (n MOD ^WL) = w #>> n)`,
  SHIFT_WORD_TAC);

val SPEC1_RULE = (GEN_ALL o REWRITE_RULE [EXP_1] o
  ONCE_REWRITE_RULE [MULT_COMM] o SPECL [`i`,`x`,`1`]);

val LSL_ONE = store_thm("LSL_ONE",
  `!w:'a word. w << 1 = w + w`,
  STRIP_TAC \\ Cases_on_word `w` \\ REWRITE_TAC [word_add_def,w2n_n2w]
    \\ SHIFT_WORD_TAC \\ Cases_on `1 <= i`
    \\ ASM_SIMP_TAC arith_ss [SPEC1_RULE BIT_SHIFT_THM2,
                              SPEC1_RULE BIT_SHIFT_THM3]
    \\ STRIP_ASSUME_TAC EXISTS_HB \\ POP_ASSUM SUBST_ALL_TAC
    \\ ASM_SIMP_TAC arith_ss [BIT_def,GSYM BITS_ZERO3,BITS_COMP_THM2,MIN_DEF]);

val ROR_TRUE = store_thm("ROR_TRUE",
  `!n. Tw #>> n = Tw`, SHIFT_WORD_TAC);

val ROR_ROL = store_thm("ROR_ROL",
  `!w n. (w #>> n #<< n = w) /\ (w #<< n #>> n = w)`,
  SHIFT_WORD_TAC
    \\ SPECL_THEN [`n`,`^WL`]
         (STRIP_ASSUME_TAC o SIMP_RULE std_ss [DIMINDEX_GT_0]) DA
    >> ASM_SIMP_TAC std_ss [MOD_TIMES,GSYM ADD_ASSOC,DIMINDEX_GT_0,LESS_MOD,
         DECIDE ``!a:num b c. a < c ==> (a + (b + (c - a)) = b + c)``,
         ADD_MODULUS_LEFT]
    \\ ONCE_REWRITE_TAC [ADD_COMM]
    \\ ASM_SIMP_TAC std_ss [MOD_PLUS_RIGHT,MOD_TIMES,DIMINDEX_GT_0,LESS_MOD,
         DECIDE ``!a:num b c d. a < c ==> ((c - a + b + d + a) = c + b + d)``,
         ADD_MODULUS_RIGHT,ONCE_REWRITE_RULE [ADD_COMM] MOD_TIMES,ADD_ASSOC]);

val ZERO_SHIFT = store_thm("ZERO_SHIFT",
  `(!n. 0w:'a word << n  = 0w) /\
   (!n. 0w:'a word >> n  = 0w) /\
   (!n. 0w:'a word >>> n = 0w) /\
   (!n. 0w:'a word #>> n = 0w)`,
  SHIFT_WORD_TAC \\ Cases_on `i + n < ^WL`
    \\ ASM_SIMP_TAC fcp_ss []);

val SHIFT_ZERO = store_thm("SHIFT_ZERO",
  `(!a. a << 0 = a) /\ (!a. a >> 0 = a) /\
   (!a. a >>> 0 = a) /\ (!a. a #>> 0 = a)`,
  SHIFT_WORD_TAC);

val LSR_BITWISE = store_thm("LSR_BITWISE",
  `(!n v:'a word w:'a word. w >>> n && v >>> n = ((w && v) >>> n)) /\
   (!n v:'a word w:'a word. w >>> n !! v >>> n = ((w !! v) >>> n)) /\
   (!n v:'a word w:'a word. w >>> n ?? v >>> n = ((w ?? v) >>> n))`,
  SHIFT_WORD_TAC \\ Cases_on `i + n < dimindex UNIV`
    \\ ASM_SIMP_TAC fcp_ss []);

val LSL_BITWISE = store_thm("LSL_BITWISE",
  `(!n v:'a word w:'a word. w << n && v << n = ((w && v) << n)) /\
   (!n v:'a word w:'a word. w << n !! v << n = ((w !! v) << n)) /\
   (!n v:'a word w:'a word. w << n ?? v << n = ((w ?? v) << n))`,
  SHIFT_WORD_TAC << [PROVE_TAC [], PROVE_TAC [], ALL_TAC]
    \\ Cases_on `n <= i` \\ ASM_SIMP_TAC arith_ss []);

val ROR_BITWISE = store_thm("ROR_BITWISE",
  `(!n v:'a word w:'a word. w #>> n && v #>> n = ((w && v) #>> n)) /\
   (!n v:'a word w:'a word. w #>> n !! v #>> n = ((w !! v) #>> n)) /\
   (!n v:'a word w:'a word. w #>> n ?? v #>> n = ((w ?? v) #>> n))`,
  SHIFT_WORD_TAC);

val word_lsl_n2w = store_thm("word_lsl_n2w",
  `!n m. (n2w m):'a word << n =
      if ^HB < n then 0w else n2w (m * 2 ** n)`,
  Induct >> SIMP_TAC arith_ss [SHIFT_ZERO]
    \\ ASM_REWRITE_TAC [ADD1,GSYM LSL_ADD]
    \\ Cases_on `dimindex (UNIV:'a set) - 1 < n`
    \\ ASM_SIMP_TAC arith_ss [ZERO_SHIFT]
    \\ RW_TAC arith_ss [LSL_ONE,EXP_ADD,word_add_n2w]
    \\ `n = dimindex (UNIV:'a set) - 1` by DECIDE_TAC
    \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
    \\ ASM_SIMP_TAC (std_ss++numSimps.ARITH_AC_ss) [GSYM EXP,SUB1_SUC,
         MOD_EQ_0,ZERO_MOD,ZERO_LT_TWOEXP,DIMINDEX_GT_0]);

val word_lsr_n2w = store_thm("word_lsr_n2w",
  `!w:'a word n. w >>> n = (^HB -- n) w`,
  SIMP_TAC arith_ss [word_lsr_def,word_bits_def,MIN_IDEM,DIMINDEX_GT_0,
    DECIDE ``0 < m ==> (a <= m - 1 = a < m)``]);

val lem = (GEN_ALL o REWRITE_RULE [MATCH_MP (DECIDE ``0 < n ==> 1 <= n``)
  (SPEC_ALL ZERO_LT_TWOEXP),MULT_LEFT_1] o SPECL [`1`,`2 ** n`]) LESS_MONO_MULT;

val LSL_TRUE = store_thm("LSL_TRUE",
  `!n. Tw << n = n2w (^TOP - 2 ** n):'a word`,
  RW_TAC arith_ss [n2w_11,word_T_def,word_lsl_n2w]
    \\ FULL_SIMP_TAC arith_ss [NOT_LESS,RIGHT_SUB_DISTRIB]
    \\ `n < ^WL` by DECIDE_TAC \\ IMP_RES_TAC TWOEXP_MONO
    \\ `2 ** n * ^TOP - 2 ** n = (2 ** n - 1) * ^TOP + (^TOP - 2 ** n)`
    by (`^TOP <= 2 ** n * ^TOP` by ASM_SIMP_TAC arith_ss [lem]
          \\ ASM_SIMP_TAC std_ss [MULT_LEFT_1,RIGHT_SUB_DISTRIB,
               GSYM LESS_EQ_ADD_SUB,LESS_IMP_LESS_OR_EQ,SUB_ADD]
          \\ PROVE_TAC [MULT_COMM])
    \\ ASM_SIMP_TAC std_ss [MOD_TIMES,ZERO_LT_TWOEXP]);

val word_asr_n2w = prove(
  `!n w. w:'a word >> n =
     if word_msb w then
       Tw << (^WL - MIN n ^WL) !! w >>> n
     else
       w >>> n`,
  NTAC 2 STRIP_TAC \\ Cases_on `^WL < n`
    >> RW_TAC arith_ss [MIN_DEF,SHIFT_ZERO,LSR_LIMIT,ASR_LIMIT,WORD_OR_CLAUSES]
    \\ SHIFT_WORD_TAC \\ Cases_on `^WL <= i + n`
    \\ FULL_SIMP_TAC arith_ss [MIN_DEF]);

val word_asr_n2w = save_thm("word_asr_n2w",
  REWRITE_RULE [LSL_TRUE] word_asr_n2w);

val BITS_SUM1 =
  (GEN_ALL o REWRITE_RULE [MULT_LEFT_1] o
   INST [`a` |-> `1`] o SPEC_ALL) BITS_SUM;

val lem = (GSYM o SIMP_RULE arith_ss [] o
  SPECL [`p`,`SUC m - n MOD SUC m + p`,
         `SUC m - n MOD SUC m`]) BIT_OF_BITS_THM;

val lem2 = (GSYM o REWRITE_RULE [ADD] o
   SPECL [`p`,`n MOD SUC m - 1`,`0`]) BIT_OF_BITS_THM;

val word_ror_n2w = store_thm("word_ror_n2w",
  `!n a. (n2w a):'a word #>> n =
     let x = n MOD ^WL in
       n2w (BITS ^HB x a + (BITS (x - 1) 0 a) * 2 ** (^WL - x))`,
  SIMP_TAC (bool_ss++boolSimps.LET_ss) [Once (GSYM ROR_MOD)]
    \\ RW_TAC fcp_ss [word_ror_def,n2w_def,DIVISION,DIMINDEX_GT_0]
    \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ FULL_SIMP_TAC arith_ss [] \\ ONCE_REWRITE_TAC [MULT_COMM]
    \\ Cases_on `i < SUC m - n MOD SUC m`
    << [
      `i + n MOD SUC m < SUC m` by DECIDE_TAC
        \\ PAT_ASSUM `i < y - z` (fn th => (STRIP_ASSUME_TAC o REWRITE_RULE
             [DECIDE ``a + (b + 1) = b + SUC a``]) (MATCH_MP LESS_ADD_1 th))
        \\ ASM_SIMP_TAC std_ss [BITS_SUM2,EXP_ADD,BIT_def,MULT_ASSOC]
        \\ ASM_SIMP_TAC arith_ss [GSYM BIT_def,BIT_OF_BITS_THM],
      RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS])
        \\ IMP_RES_TAC LESS_EQUAL_ADD
        \\ ASSUME_TAC (SPECL [`m`,`n MOD SUC m`,`a`] BITSLT_THM)
        \\ ASM_SIMP_TAC std_ss [lem,BITS_SUM]
        \\ REWRITE_TAC [GSYM lem]
        \\ ASM_SIMP_TAC std_ss [ONCE_REWRITE_RULE [ADD_COMM] BIT_SHIFT_THM]
        \\ `p < SUC m /\ p <= n MOD SUC m - 1` by DECIDE_TAC
        \\ `SUC m - n MOD SUC m + p + n MOD SUC m = SUC m + p`
        by SIMP_TAC arith_ss [DIVISION,
             DECIDE ``b < a ==> (a - b + c + b = a + c:num)``]
        \\ ASM_SIMP_TAC std_ss [LESS_MOD,prim_recTheory.LESS_0,
             ADD_MODULUS,lem2]]);

val word_rrx_n2w = store_thm("word_rrx_n2w",
  `!c a. word_rrx(c, (n2w a):'a word) =
       (ODD a, (n2w (BITS ^HB 1 a + SBIT c ^HB)):'a word)`,
  SHIFT_WORD_TAC
    \\ RW_TAC arith_ss [GSYM LSB_def,LSB_ODD,SBIT_def,BIT_OF_BITS_THM]
    \\ STRIP_ASSUME_TAC EXISTS_HB \\ FULL_SIMP_TAC arith_ss []
    << [
      METIS_TAC [BITSLT_THM,SUC_SUB1,BITS_SUM1,BIT_def,BIT_B],
      SIMP_TAC arith_ss [BIT_def,BITS_COMP_THM2,MIN_lem,BITS_ZERO],
      `i < m` by DECIDE_TAC
        \\ POP_ASSUM (fn th => (STRIP_ASSUME_TAC o REWRITE_RULE
             [DECIDE ``a + (b + 1) = b + SUC a``]) (MATCH_MP LESS_ADD_1 th))
        \\ ASM_SIMP_TAC std_ss [EXP_ADD,BIT_def,BITS_SUM2,BITS_COMP_THM2]
        \\ SIMP_TAC std_ss [ADD1,ONCE_REWRITE_RULE [ADD_COMM] MIN_lem]]);

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

val SPEC_LESS_EXP_SUC_MONO = prove(
  `2 ** ^HB < 2 ** dimindex (UNIV : 'a set)`,
  SRW_TAC [][DIMINDEX_GT_0])

val SPLIT_2_EXP_WL = prove(
  `^TOP = ^MSB + ^MSB`,
  STRIP_ASSUME_TAC EXISTS_HB
    \\ ASM_SIMP_TAC arith_ss [EXP]);

val WORD_NEG_L = store_thm("WORD_NEG_L",
  `$- word_L = word_L`,
  SRW_TAC [][word_2comp_n2w, word_L_def, LESS_MOD, DIMINDEX_GT_0,
             SUB_RIGHT_EQ, SPLIT_2_EXP_WL])

(* ------------------------------------------------------------------------- *)

val BITS_COMP_MSB = (SIMP_RULE arith_ss [] o
  SPECL [`m`,`0`,`m - 1`,`0`]) BITS_COMP_THM;

val SLICE_COMP_MSB = prove(
  `!b n. ~(b = 0) ==> (SLICE b b n + SLICE (b - 1) 0 n = SLICE b 0 n)`,
   REPEAT STRIP_TAC
     \\ POP_ASSUM (fn th => REWRITE_TAC [(SIMP_RULE arith_ss [SUB_SUC1,th] o
          SPECL [`b`,`b - 1`,`0`,`n`]) SLICE_COMP_THM]));

val MSB_THM1 = prove(
  `!a:'a word. ~(^HB = 0) /\ word_msb a ==>
        (w2n a = ^MSB + BITS (^HB - 1) 0 (w2n a))`,
  Cases_word \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ RW_TAC arith_ss [word_msb_n2w,w2n_n2w,GSYM BITS_ZERO3,BITS_COMP_MSB]
    \\ IMP_RES_TAC BIT_SLICE_THM2 \\ POP_ASSUM (SUBST1_TAC o SYM)
    \\ ASM_SIMP_TAC arith_ss [SLICE_COMP_MSB,GSYM SLICE_ZERO_THM]);

val MSB_THM2 = prove(
  `!a:'a word. ~(^HB = 0) /\ word_msb a ==>
        (w2n ($- a) = ^MSB - BITS (^HB - 1) 0 (w2n a))`,
  Cases_word \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MSB_THM1
    \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ FULL_SIMP_TAC arith_ss [word_msb_n2w,word_2comp_n2w,w2n_n2w,
         BITS_COMP_MSB,GSYM BITS_ZERO3]
    \\ ASM_SIMP_TAC arith_ss [BITS_ZERO3,GSYM ADD1,ADD_MODULUS,MOD_MOD,
         ZERO_LT_TWOEXP,SUB_SUC1]
    \\ REWRITE_TAC [EXP,TIMES2,SUB_PLUS,ADD_SUB]
    \\ `2 ** m - n MOD 2 ** m < 2 ** SUC m` by METIS_TAC
         [DECIDE ``a - b <= a /\ a < SUC a``,TWOEXP_MONO,LESS_EQ_LESS_TRANS]
    \\ ASM_SIMP_TAC arith_ss [GSYM EXP,LESS_MOD]);

val MSB_THM3 = prove(
  `!a:'a word. ~(^HB = 0) /\ ~word_msb a ==>
        (w2n a = BITS (^HB - 1) 0 (w2n a))`,
  Cases_word \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ RW_TAC arith_ss [word_msb_n2w,w2n_n2w,GSYM BITS_ZERO3,BITS_COMP_MSB]
    \\ `~(m = 0)` by DECIDE_TAC
    \\ MAP_EVERY IMP_RES_TAC [BIT_SLICE_THM3,SLICE_COMP_MSB]
    \\ POP_ASSUM (SPEC_THEN `n` ASSUME_TAC)
    \\ PAT_ASSUM `SLICE m m n = 0` (fn th =>
         FULL_SIMP_TAC arith_ss [th,GSYM SLICE_ZERO_THM]));

val MSB_THM4 = prove(
  `!a:'a word. ~(^HB = 0) /\ ~(a = 0w) /\ ~word_msb a ==>
       (w2n ($- a) = ^TOP - BITS (^HB - 1) 0 (w2n a)) /\
       ~(BITS (^HB - 1) 0 (w2n a) = 0)`,
  Cases_word \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MSB_THM3
    \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ FULL_SIMP_TAC arith_ss [word_msb_n2w,word_2comp_n2w,w2n_n2w,n2w_11,
         GSYM BITS_ZERO3,BITS_ZERO2,BITS_COMP_MSB]
    \\ FULL_SIMP_TAC arith_ss [BITS_COMP_THM2,MIN_DEF]
    \\ `2 ** SUC m - BITS (m - 1) 0 n < 2 ** SUC m`
    by ASM_SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
    \\ ASM_SIMP_TAC bool_ss [BITS_ZEROL]);

val HB_0_MSB = prove(
  `!a:'a word. (^HB = 0) /\ word_msb a ==> (a = 1w)`,
  Cases_word \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ RW_TAC bool_ss [word_msb_n2w,w2n_n2w,n2w_11,BIT_def,SUC_SUB1]
    \\ FULL_SIMP_TAC arith_ss [BITS_ZERO3]);

val HB_0_NOT_MSB = prove(
  `!a:'a word. (^HB = 0) /\ ~word_msb a ==> (a = 0w)`,
  Cases_word \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ RW_TAC fcp_ss [word_msb_n2w,n2w_11,ZERO_MOD,ZERO_LT_TWOEXP,
         GSYM BITS_ZERO3]
    \\ METIS_TAC [DECIDE ``SUC m <= 1 = (m = 0)``,BIT_def,NOT_BITS2]);

val DIMINDEX_1 = prove(
  `(^WL - 1 = 0) ==> (^WL = 1)`,
  STRIP_ASSUME_TAC EXISTS_HB \\ ASM_SIMP_TAC arith_ss []);

val MSB_THM1b = prove(
  `!a:'a word. (^HB = 0) /\ word_msb a ==> (w2n a = 1)`,
  METIS_TAC [HB_0_MSB,DIMINDEX_1,EXP_1,LESS_MOD,DECIDE ``1 < 2``,w2n_n2w]);

val MSB_THM2b = prove(
  `!a:'a word. (^HB = 0) /\ word_msb a ==> (w2n (word_2comp a) = 1)`,
  REPEAT STRIP_TAC \\ MAP_EVERY IMP_RES_TAC [HB_0_MSB,DIMINDEX_1]
    \\ ASM_SIMP_TAC arith_ss [w2n_n2w,word_2comp_n2w]);

val MSB_THM3b = prove(
  `!a:'a word. (^HB = 0) /\ ~word_msb a ==> (w2n a = 0)`,
  REPEAT STRIP_TAC \\ MAP_EVERY IMP_RES_TAC [HB_0_NOT_MSB,DIMINDEX_1]
    \\ ASM_SIMP_TAC arith_ss [w2n_n2w]);

val MSB_THM4b = prove(
  `!a:'a word. (^HB = 0) /\ ~word_msb a ==> (w2n (word_2comp a) = 0)`,
  REPEAT STRIP_TAC \\ MAP_EVERY IMP_RES_TAC [HB_0_NOT_MSB,DIMINDEX_1]
    \\ ASM_SIMP_TAC arith_ss [w2n_n2w,WORD_NEG_0]);

(* ------------------------------------------------------------------------- *)

val w2n_mod = PROVE [n2w_w2n,n2w_mod]
   ``(w2n (a:'a word) = n) ==> (a = n2w (n MOD ^TOP))``;

val BITS_MSB_LT = (GEN_ALL o SIMP_RULE arith_ss [SUB_SUC1] o
  DISCH `~(b = 0)` o SPECL [`b - 1`,`0`,`a`]) BITSLT_THM;

val SLICE_MSB_LT = REWRITE_RULE [GSYM SLICE_ZERO_THM] BITS_MSB_LT;

val BITS_MSB_LTEQ = prove(
  `!b a. ~(b = 0) ==> BITS (b - 1) 0 a <= 2 ** b`,
  PROVE_TAC [LESS_IMP_LESS_OR_EQ,BITS_MSB_LT]);

val TWO_COMP_POS = store_thm("TWO_COMP_POS",
  `!a:'a word. ~word_msb a ==>
          (if a = 0w then ~word_msb ($- a) else word_msb ($- a))`,
  Cases_word
    \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ RW_TAC bool_ss [WORD_NEG_0]
    \\ Cases_on `^HB = 0` >> PROVE_TAC [HB_0_NOT_MSB]
    \\ `~(m = 0)` by DECIDE_TAC
    \\ MAP_EVERY IMP_RES_TAC [MSB_THM4,w2n_mod]
    \\ PAT_ASSUM `dimindex UNIV = SUC m` (fn t =>
         FULL_SIMP_TAC arith_ss [word_msb_n2w,BITS_COMP_THM2,MIN_DEF,BIT_def,t])
    \\ `2 ** SUC m - BITS (m - 1) 0 (w2n ((n2w n):'a word)) < 2 ** SUC m /\
        2 ** m - BITS (m - 1) 0 (w2n ((n2w n):'a word)) < 2 ** m`
    by ASM_SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
    \\ ASM_SIMP_TAC std_ss [LESS_MOD] \\ IMP_RES_TAC BITS_MSB_LTEQ
    \\ ASM_SIMP_TAC bool_ss [SPECL [`m`,`m`] BITS_THM,SUC_SUB,EXP_1,EXP,
         TIMES2,LESS_EQ_ADD_SUB,DIV_MULT_1] \\ numLib.REDUCE_TAC);

val TWO_COMP_NEG_lem = prove(
  `!n. ~(^HB = 0) /\ ~((n2w n):'a word = word_L) /\
       word_msb ((n2w n):'a word) ==>
       ~(BITS (^WL - 2) 0 (w2n ((n2w n):'a word)) = 0)`,
  REPEAT STRIP_TAC \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ FULL_SIMP_TAC arith_ss [BITS_COMP_THM2,MIN_DEF,GSYM BITS_ZERO3,
         word_msb_n2w,w2n_n2w]
    \\ IMP_RES_TAC BIT_SLICE_THM2
    \\ RULE_ASSUM_TAC (REWRITE_RULE [GSYM SLICE_ZERO_THM])
    \\ `~(m = 0)` by DECIDE_TAC \\ IMP_RES_TAC SLICE_COMP_MSB
    \\ POP_ASSUM (SPEC_THEN `n` ASSUME_TAC)
    \\ FULL_SIMP_TAC arith_ss [word_L_def,n2w_11,LESS_MOD,
         SUC_SUB1,SUC_SUB2,TWOEXP_MONO]
    \\ FULL_SIMP_TAC bool_ss [GSYM BITS_ZERO3,GSYM SLICE_ZERO_THM]
    \\ PROVE_TAC [ADD_0]);

val TWO_COMP_NEG = store_thm("TWO_COMP_NEG",
  `!a:'a word. word_msb a ==>
       if (^HB = 0) \/ (a = word_L) then
         word_msb (word_2comp a)
       else
        ~word_msb (word_2comp a)`,
  RW_TAC bool_ss [] << [
    IMP_RES_TAC HB_0_MSB
      \\ ASM_SIMP_TAC arith_ss [word_msb_n2w,word_T_def,WORD_NEG_1,
           DIMINDEX_GT_0,ONE_COMP_0_THM],
    ASM_REWRITE_TAC [WORD_NEG_L],
    FULL_SIMP_TAC bool_ss [] \\ Cases_on_word `a`
      \\ MAP_EVERY IMP_RES_TAC [MSB_THM2,w2n_mod,TWO_COMP_NEG_lem]
      \\ STRIP_ASSUME_TAC EXISTS_HB \\ `~(m = 0)` by DECIDE_TAC
      \\ FULL_SIMP_TAC arith_ss [BITS_COMP_THM2,MIN_DEF,BIT_def,
           word_msb_n2w,w2n_n2w,GSYM BITS_ZERO3,SUC_SUB2]
      \\ `2 ** m - BITS (m - 1) 0 n < 2 ** m`
      by ASM_SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
      \\ ASM_SIMP_TAC arith_ss [BITS_THM,SUC_SUB,EXP_1,LESS_DIV_EQ_ZERO]]);

val TWO_COMP_POS_NEG = store_thm("TWO_COMP_POS_NEG",
  `!a:'a word. ~((^HB = 0) \/ (a = 0w) \/ (a = word_L)) ==>
     (~word_msb a = word_msb (word_2comp a))`,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
    >> METIS_TAC [TWO_COMP_POS]
    \\ METIS_TAC [WORD_NEG_L,WORD_NEG_EQ,WORD_NEG_NEG,TWO_COMP_NEG]);

val TWO_COMP_NEG_POS = METIS_PROVE [TWO_COMP_POS_NEG]
  ``!a:'a word. ~((^HB = 0) \/ (a = 0w) \/ (a = word_L)) ==>
     (word_msb a = ~word_msb (word_2comp a))``;

val WORD_0_POS = store_thm("WORD_0_POS",
  `~word_msb 0w`, REWRITE_TAC [word_msb_n2w,BIT_ZERO]);

val WORD_H_POS = store_thm("WORD_H_POS",
  `~word_msb word_H`,
  `^MSB - 1 < ^MSB` by ASM_SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
     \\ ASM_SIMP_TAC bool_ss [word_H_def,word_msb_n2w,BIT_def,BITS_THM,
          LESS_DIV_EQ_ZERO,ZERO_MOD,ZERO_LT_TWOEXP] \\ DECIDE_TAC);

val WORD_L_NEG = store_thm("WORD_L_NEG",
  `word_msb word_L`, REWRITE_TAC [word_L_def,word_msb_n2w,BIT_ZERO,BIT_B]);

(* ------------------------------------------------------------------------- *)

val NOT_EQUAL_THEN_NOT =
  PROVE [EQUAL_THEN_SUB_ZERO] ``!a b. ~(a = b) = ~(b - a = 0w)``;

val SUB_EQUAL_WORD_L_MSB = prove(
  `!a:'a word b:'a word. ~(^HB = 0) /\ (a - b = word_L) ==>
      ~(word_msb a = word_msb b)`,
  RW_TAC bool_ss [WORD_EQ_SUB_RADD] \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ `~(m = 0)` by DECIDE_TAC \\ Cases_on_word `b`
    \\ ASM_REWRITE_TAC [word_msb_n2w,word_L_def,SUC_SUB1]
    \\ SUBST1_TAC ((SYM o SPEC `n`) n2w_mod)
    \\ ASM_REWRITE_TAC [word_msb_n2w,word_add_n2w,SUC_SUB1,
         GSYM BITS_ZERO3,GSYM SLICE_ZERO_THM]
    \\ `SLICE m 0 n = SLICE m m n + SLICE (m - 1) 0 n`
    by METIS_TAC [SLICE_COMP_MSB,SUC_SUB2]
    \\ Cases_on `BIT m n`
    << [IMP_RES_TAC BIT_SLICE_THM2,IMP_RES_TAC BIT_SLICE_THM3]
    \\ ASM_SIMP_TAC arith_ss [BIT_def,BITS_THM,SUC_SUB,EXP_1,SLICE_MSB_LT,
         DIV_MULT,DIV_MULT_1]);

val LEM1_TAC =
  REPEAT STRIP_TAC
    \\ MAP_EVERY Cases_on [`word_msb a`,`word_msb b`,`a = b`]
    \\ FULL_SIMP_TAC bool_ss [word_lt,word_gt,word_le,word_ge,
         WORD_SUB_REFL,WORD_0_POS,DECIDE (Term `~(a = ~a)`)]
    \\ GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV)
         empty_rewrites [GSYM WORD_NEG_SUB]
    \\ IMP_RES_TAC NOT_EQUAL_THEN_NOT \\ Cases_on `b - a = word_L`
    \\ PROVE_TAC [SUB_EQUAL_WORD_L_MSB,TWO_COMP_POS_NEG];

val LEM2_TAC =
  REPEAT STRIP_TAC \\ MAP_EVERY Cases_on [`word_msb a`,`word_msb b`]
    \\ MAP_EVERY IMP_RES_TAC [MSB_THM1b,MSB_THM2b,MSB_THM3b,MSB_THM4b]
    \\ ASM_SIMP_TAC arith_ss [word_lt,word_gt,word_le,word_ge,word_sub_def,
         word_add_def,word_add_n2w,word_msb_n2w,n2w_11,BITS_ZERO2,BIT_def]
    \\ ASM_SIMP_TAC arith_ss [BITS_ZERO3]
    \\ PROVE_TAC [w2n_11];

val WORD_GREATER = store_thm("WORD_GREATER",
  `!a:'a word b. a > b = b < a`,
  Cases_on `^HB = 0` << [LEM2_TAC,LEM1_TAC]);

val WORD_GREATER_EQ = store_thm("WORD_GREATER_EQ",
  `!a:'a word b. a >= b = b <= a`,
  Cases_on `^HB = 0` << [LEM2_TAC,LEM1_TAC]);

val WORD_NOT_LESS = store_thm("WORD_NOT_LESS",
  `!a:'a word b. ~(a < b) = b <= a`,
  Cases_on `^HB = 0` << [LEM2_TAC,LEM1_TAC]);

(* ------------------------------------------------------------------------- *)

val LESS_EQ_ADD2 = DECIDE (Term `!a:num b c. a + b <= a + c ==> b <= c`);
val LESS_ADD2 = DECIDE (Term `!a:num b c. a + b < a + c ==> b < c`);
val LESS_EQ_ADD_SUB2 =
   DECIDE (Term `!m:num n p. p <= n ==> (m + p - n = m - (n - p))`);
val SUB_SUC1 = DECIDE ``!m. ~(m = 0) ==> (SUC (m - 1) = m)``;

val start_tac =
  REWRITE_TAC [word_sub_def,word_add_def] \\ RW_TAC bool_ss [word_msb_n2w]
    \\ POP_ASSUM MP_TAC \\ Cases_on `w2n a < w2n b`
    \\ ASM_REWRITE_TAC [] \\ IMP_RES_TAC MSB_THM1
    \\ `w2n ($- b) = ^MSB - BITS (^HB - 1) 0 (w2n b)` by IMP_RES_TAC MSB_THM2
    \\ ABBREV_TAC `x = BITS (^HB - 1) 0 (w2n a)`
    \\ ABBREV_TAC `y = BITS (^HB - 1) 0 (w2n b)`
    \\ FULL_SIMP_TAC bool_ss [NOT_LESS,GSYM LESS_EQ_ADD_SUB,BITS_MSB_LT,
         DECIDE (Term `!a b. a + b + a = 2 * a + b`)];

val WORD_LT_lem = prove(
  `!a:'a word b. ~(^HB = 0) /\ word_msb a /\
         word_msb b /\ word_msb (a - b) ==> w2n a < w2n b`,
  start_tac \\ IMP_RES_TAC LESS_EQ_ADD2
    \\ ASM_SIMP_TAC bool_ss [Abbr`x`,Abbr`y`,LESS_EQ_ADD_SUB2,BIT_def,
         BITS_THM,SUC_SUB,EXP_1,DIV_1,SUB_0,CONJUNCT1 EXP,LESS_EQ_ADD_SUB,
         NOT_MOD2_LEM2,SUB_SUC1]
    \\ SIMP_TAC arith_ss [MOD_2EXP_LT,SUB_LEFT_ADD,
         DECIDE ``a < b ==> ~(b <= a:num)``]
    \\ PAT_ASSUM `~(x = 0)` ASSUME_TAC \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ FULL_SIMP_TAC bool_ss [SUC_SUB1,BITS_ZERO3,LESS_EQ_ADD_SUB,SUB_SUC1,
         DECIDE ``a < c /\ b < c ==> (a - b) < c:num``,MOD_2EXP_LT,DIV_MULT,
         DIVMOD_ID,DECIDE ``0 < 2``]);

val WORD_LT_lem2 = prove(
  `!a:'a word b. ~(^HB = 0) /\ word_msb a /\ word_msb b /\
         ~word_msb (a - b) ==> ~(w2n a < w2n b)`,
  start_tac
    \\ ONCE_REWRITE_TAC [DECIDE (Term `!a b c. (a:num) + b + c = a + c + b`)]
    \\ PAT_ASSUM `x + y < x + z` (ASSUME_TAC o (MATCH_MP LESS_ADD2))
    \\ IMP_RES_TAC LESS_ADD_1
    \\ `y < ^MSB` by METIS_TAC [BITS_MSB_LT]
    \\ `p + 1 <= ^MSB` by DECIDE_TAC
    \\ ASM_SIMP_TAC arith_ss [SUB_LEFT_ADD] \\ IMP_RES_TAC LESS_EQUAL_ADD
    \\ ASM_SIMP_TAC std_ss [TIMES2,DECIDE ``x + (y + p) = x + p + y:num``,
         DECIDE ``a + b + c - (c + b) = a:num``]
    \\ `p' < p + 1 + p'` by DECIDE_TAC
    \\ ASM_SIMP_TAC bool_ss [BIT_def,BITS_THM,SUC_SUB,EXP_1,DIV_MULT_1]
    \\ numLib.REDUCE_TAC);

val w2n_0 =
  SIMP_CONV arith_ss [w2n_n2w,ZERO_MOD,ZERO_LT_TWOEXP] ``w2n 0w``;

val start_tac = REWRITE_TAC [word_sub_def,word_add_def]
    \\ NTAC 2 STRIP_TAC
    \\ Cases_on `b = 0w`
    >> (ASM_REWRITE_TAC [WORD_NEG_0,w2n_0,ADD_0,n2w_w2n]
          \\ PROVE_TAC [prim_recTheory.NOT_LESS_0])
    \\ RW_TAC bool_ss [word_msb_n2w]
    \\ POP_ASSUM MP_TAC
    \\ Cases_on `w2n a < w2n b` \\ ASM_REWRITE_TAC []
    \\ IMP_RES_TAC MSB_THM3
    \\ `w2n ($- b) = ^TOP - BITS (^HB - 1) 0 (w2n b)` by IMP_RES_TAC MSB_THM4
    \\ ABBREV_TAC `x = BITS (^HB - 1) 0 (w2n a)`
    \\ ABBREV_TAC `y = BITS (^HB - 1) 0 (w2n b)`
    \\ `y <= ^MSB` by METIS_TAC [BITS_MSB_LTEQ]
    \\ `y <= ^TOP` by METIS_TAC [SPEC_LESS_EXP_SUC_MONO,
                        LESS_IMP_LESS_OR_EQ,LESS_EQ_TRANS]
    \\ FULL_SIMP_TAC bool_ss [NOT_LESS,GSYM LESS_EQ_ADD_SUB]
    \\ ONCE_REWRITE_TAC [ADD_COMM];

val WORD_LT_lem3 = prove(
  `!a:'a word b. ~(^HB = 0) /\ ~word_msb a /\ ~word_msb b /\
         word_msb (a - b) ==> w2n a < w2n b`,
  start_tac \\ `x < ^MSB` by METIS_TAC [BITS_MSB_LT]
    \\ `x - y < ^MSB` by DECIDE_TAC
    \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ FULL_SIMP_TAC bool_ss [BIT_def,BITS_THM,SUC_SUB,EXP_1,
         LESS_EQ_ADD_SUB,EXP,DIV_MULT,SUC_SUB1]
    \\ numLib.REDUCE_TAC);

val WORD_LT_lem4 = prove(
  `!a:'a word b. ~(^HB = 0) /\ ~word_msb a /\ ~word_msb b /\
        ~word_msb (a - b) ==> ~(w2n a < w2n b)`,
  start_tac
    \\ `y <= ^MSB + x` by DECIDE_TAC
    \\ ASM_SIMP_TAC bool_ss [SPLIT_2_EXP_WL,GSYM ADD_ASSOC,LESS_EQ_ADD_SUB]
    \\ IMP_RES_TAC LESS_IMP_LESS_OR_EQ
    \\ `^MSB - (y - x) < ^MSB` by DECIDE_TAC
    \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ FULL_SIMP_TAC bool_ss [LESS_EQ_ADD_SUB2,DIV_MULT_1,BIT_def,
         BITS_THM,SUC_SUB,EXP_1]
    \\ numLib.REDUCE_TAC);

val WORD_LT = store_thm("WORD_LT",
  `!a b. word_lt a b = (word_msb a = word_msb b) /\ w2n a < w2n b \/
                        word_msb a /\ ~word_msb b`,
  Tactical.REVERSE (Cases_on `^HB = 0`) \\ REPEAT STRIP_TAC
    >> METIS_TAC [word_lt,WORD_LT_lem,WORD_LT_lem2,WORD_LT_lem3,WORD_LT_lem4]
    \\ MAP_EVERY Cases_on [`word_msb a`,`word_msb b`,
         `word_msb (n2w (w2n a + w2n ($- b)):'a word)`]
    \\ ASM_REWRITE_TAC [word_lt] \\ POP_ASSUM MP_TAC
    \\ Cases_on `w2n a < w2n b`
    \\ ASM_REWRITE_TAC [word_msb_n2w,word_sub_def,word_add_def]
    \\ MAP_EVERY IMP_RES_TAC [MSB_THM1b,MSB_THM2b,MSB_THM3b,MSB_THM4b]
    \\ ASM_SIMP_TAC arith_ss [BIT_def,BITS_THM]);

val WORD_GT = save_thm("WORD_GT",
  (GEN `a` o GEN `b` o REWRITE_CONV [WORD_GREATER,WORD_LT,GSYM GREATER_DEF])
  ``a:'a word > b``);

val WORD_LE = store_thm("WORD_LE",
  `!a:bool **'a b. a <= b = (word_msb a = word_msb b) /\ (w2n a <= w2n b) \/
                             word_msb a /\ ~word_msb b`,
  SIMP_TAC bool_ss [WORD_LT,GSYM WORD_NOT_LESS,NOT_LESS] \\ DECIDE_TAC);

val WORD_GE = save_thm("WORD_GE",
  (GEN `a` o GEN `b` o REWRITE_CONV [WORD_GREATER_EQ,WORD_LE,GSYM GREATER_EQ])
  ``a:'a word >= b``);

val w2n_2comp = prove(
  `!a:'a word. w2n ($- a) = if a = 0w then 0 else ^TOP - w2n a`,
  RW_TAC bool_ss [WORD_NEG_0,w2n_0] \\ Cases_on_word `a`
    \\ FULL_SIMP_TAC bool_ss [GSYM w2n_11,w2n_0,w2n_n2w,word_2comp_n2w]
    \\ `^TOP - n MOD ^TOP < ^TOP` by ASM_SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
    \\ ASM_SIMP_TAC bool_ss [LESS_MOD]);

val WORD_LO = store_thm("WORD_LO",
  `!a b. a <+ b = w2n a < w2n b`,
  RW_TAC bool_ss [word_lo] \\ Cases_on `b = 0w`
    \\ ASM_SIMP_TAC arith_ss [w2n_2comp,w2n_0,GSYM LESS_EQ_ADD_SUB,
         MATCH_MP LESS_IMP_LESS_OR_EQ (SPEC `b` w2n_lt)]
    \\ Cases_on `a = b` >> ASM_SIMP_TAC arith_ss [BIT_B]
    \\ Cases_on `w2n a < w2n b` \\ ASM_REWRITE_TAC []
    \\ ONCE_REWRITE_TAC [ADD_COMM]
    \\ RULE_ASSUM_TAC (REWRITE_RULE [GSYM w2n_11,w2n_0,w2n_n2w]) << [
      IMP_RES_TAC LESS_IMP_LESS_OR_EQ
        \\ `~(w2n b - w2n a = 0)` by DECIDE_TAC
        \\ POP_ASSUM (fn th => `^TOP - (w2n b - w2n a) < ^TOP`
        by SIMP_TAC arith_ss [th,ZERO_LT_TWOEXP])
        \\ ASM_SIMP_TAC arith_ss [GSYM SUB_SUB,BIT_def,BITS_THM,SUC_SUB,
             EXP_1,LESS_DIV_EQ_ZERO],
      RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS])
        \\ ASSUME_TAC (SPEC `a` w2n_lt)
        \\ `w2n a - w2n b < ^TOP` by ASM_SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
        \\ ASM_SIMP_TAC bool_ss [LESS_EQ_ADD_SUB,BIT_def,BITS_THM,SUC_SUB,
             EXP_1,DIV_MULT_1]
        \\ numLib.REDUCE_TAC]);

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
  `!a:'a word b. ~(a <= b) = b < a`, PROVE_TAC [WORD_NOT_LESS]);

val WORD_LESS_OR_EQ = store_thm("WORD_LESS_OR_EQ",
  `!a:'a word b. a <= b = a < b \/ (a = b)`, LEM1_TAC);

val WORD_GREATER_OR_EQ = store_thm("WORD_GREATER_OR_EQ",
  `!a:'a word b. a >= b = a > b \/ (a = b)`,
  PROVE_TAC [WORD_GREATER,WORD_GREATER_EQ,WORD_LESS_OR_EQ]);

val WORD_LESS_TRANS = store_thm("WORD_LESS_TRANS",
  `!a:'a word b c. a < b /\ b < c ==> a < c`,
  RW_TAC bool_ss [WORD_LT] \\ IMP_RES_TAC LESS_TRANS
     \\ ASM_REWRITE_TAC [] \\ PROVE_TAC []);

val WORD_LESS_EQ_TRANS = store_thm("WORD_LESS_EQ_TRANS",
  `!a:'a word b c. a <= b /\ b <= c ==> a <= c`,
  RW_TAC bool_ss [WORD_LE] \\ IMP_RES_TAC LESS_EQ_TRANS
     \\ ASM_REWRITE_TAC [] \\ PROVE_TAC []);

val WORD_LESS_EQ_LESS_TRANS = store_thm("WORD_LESS_EQ_LESS_TRANS",
  `!a:'a word b c. a <= b /\ b < c ==> a < c`,
  RW_TAC bool_ss [WORD_LE,WORD_LT] \\ IMP_RES_TAC LESS_EQ_LESS_TRANS
     \\ ASM_REWRITE_TAC [] \\ PROVE_TAC []);

val WORD_LESS_LESS_EQ_TRANS = store_thm("WORD_LESS_LESS_EQ_TRANS",
  `!a:'a word b c. a < b /\ b <= c ==> a < c`,
  RW_TAC bool_ss [WORD_LE,WORD_LT] \\ IMP_RES_TAC LESS_LESS_EQ_TRANS
     \\ ASM_REWRITE_TAC [] \\ PROVE_TAC []);

val WORD_LESS_EQ_CASES = store_thm("WORD_LESS_EQ_CASES",
  `!a:'a word b. a <= b \/ b <= a`,
  RW_TAC bool_ss [WORD_LE] \\ PROVE_TAC [LESS_EQ_CASES]);

val WORD_LESS_CASES = store_thm("WORD_LESS_CASES",
  `!a:'a word b. a < b \/ b <= a`,
  PROVE_TAC [WORD_LESS_OR_EQ,WORD_LESS_EQ_CASES]);

val WORD_LESS_CASES_IMP = store_thm("WORD_LESS_CASES_IMP",
  `!a:'a word b. ~(a < b) /\ ~(a = b) ==> b < a`,
  PROVE_TAC [WORD_NOT_LESS,WORD_LESS_OR_EQ]);

val WORD_LESS_ANTISYM = store_thm("WORD_LESS_ANTISYM",
  `!a:'a word b. ~(a < b /\ b < a)`,
  PROVE_TAC [WORD_NOT_LESS,WORD_LESS_EQ_CASES]);

val WORD_LESS_EQ_ANTISYM = store_thm("WORD_LESS_EQ_ANTISYM",
  `!a:'a word b. ~(a < b /\ b <= a)`,
  PROVE_TAC [WORD_NOT_LESS]);

val WORD_LESS_EQ_REFL = store_thm("WORD_LESS_EQ_REFL",
  `!a:'a word. a <= a`,
  REWRITE_TAC [WORD_LESS_OR_EQ]);

val WORD_LESS_EQUAL_ANTISYM = store_thm("WORD_LESS_EQUAL_ANTISYM",
  `!a:'a word b. a <= b /\ b <= a ==> (a = b)`,
  PROVE_TAC [WORD_LESS_OR_EQ,WORD_LESS_ANTISYM]);

val WORD_LESS_IMP_LESS_OR_EQ = store_thm("WORD_LESS_IMP_LESS_OR_EQ",
  `!a:'a word b. a < b ==> a <= b`,
  PROVE_TAC [WORD_LESS_OR_EQ]);

val WORD_LESS_REFL = store_thm("WORD_LESS_REFL",
  `!a:'a word. ~(a < a)`,
  RW_TAC bool_ss [WORD_NOT_LESS,WORD_LESS_OR_EQ]);

val WORD_LESS_LESS_CASES = store_thm("WORD_LESS_LESS_CASES",
  `!a:'a word b. (a = b) \/ a < b \/ b < a`,
  PROVE_TAC [WORD_LESS_CASES,WORD_LESS_OR_EQ]);

val WORD_NOT_GREATER = store_thm("WORD_NOT_GREATER",
  `!a:'a word b. ~(a > b) = a <= b`,
  PROVE_TAC [WORD_GREATER,WORD_NOT_LESS]);

val WORD_LESS_NOT_EQ = store_thm("WORD_LESS_NOT_EQ",
  `!a:'a word b. a < b ==> ~(a = b)`,
  PROVE_TAC [WORD_LESS_REFL,WORD_LESS_OR_EQ]);

val WORD_NOT_LESS_EQ = store_thm("WORD_NOT_LESS_EQ",
  `!a:'a word b. (a = b) ==> ~(a < b)`,
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
  `w2n (word_H:'a word) = ^MSB - 1`,
  `^MSB - 1 < ^MSB` by SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
    \\ ASSUME_TAC SPEC_LESS_EXP_SUC_MONO \\ IMP_RES_TAC LESS_TRANS
    \\ ASM_SIMP_TAC arith_ss [word_H_def,w2n_n2w,LESS_MOD]);

val WORD_L_PLUS_H = store_thm("WORD_L_PLUS_H",
  `word_L + word_H = word_T`,
  REWRITE_TAC [word_add_def,w2n_word_L,w2n_word_H,n2w_def]
    \\ RW_TAC (fcp_ss++ARITH_ss) [word_T,GSYM EXP,DIMINDEX_GT_0,
         DECIDE ``0 < m ==> (SUC (m - 1) = m)``,ONE_COMP_0_THM]);

fun bound_tac th1 th2 =
  RW_TAC bool_ss [WORD_LE,WORD_L_NEG,WORD_LE,WORD_H_POS,w2n_word_H,w2n_word_L]
    \\ Cases_on `word_msb a` \\ ASM_REWRITE_TAC []
    \\ Cases_on `^HB = 0`
    >> (IMP_RES_TAC th1 \\ ASM_SIMP_TAC arith_ss [])
    \\ Cases_on_word `a`
    \\ FULL_SIMP_TAC bool_ss [w2n_n2w,word_msb_n2w]
    \\ MAP_EVERY IMP_RES_TAC [th2,SLICE_COMP_MSB]
    \\ POP_ASSUM (SPEC_THEN `n` ASSUME_TAC)
    \\ STRIP_ASSUME_TAC EXISTS_HB
    \\ FULL_SIMP_TAC arith_ss [GSYM SLICE_ZERO_THM,GSYM BITS_ZERO3];

val WORD_L_LESS_EQ = store_thm("WORD_L_LESS_EQ",
  `!a:'a word. word_L <= a`,
  bound_tac MSB_THM1b BIT_SLICE_THM2);

val WORD_LESS_EQ_H = store_thm("WORD_LESS_EQ_H",
  `!a:'a word. a <= word_H`,
  bound_tac MSB_THM3b BIT_SLICE_THM3
    \\ `~(m = 0)` by DECIDE_TAC
    \\ METIS_TAC [SUB_LESS_OR,SLICE_MSB_LT,ADD]);

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
  SIMP_TAC (bool_ss++boolSimps.LET_ss++WORD_ss) [] \\ DECIDE_TAC;

val word_lt_n2w = store_thm("word_lt_n2w",
  `!a b. (n2w a):'a word < n2w b = let sa = BIT ^HB a and sb = BIT ^HB b in
    (sa = sb) /\ a MOD ^TOP < b MOD ^TOP \/ sa /\ ~sb`, ORDER_WORD_TAC);

val word_gt_n2w = store_thm("word_gt_n2w",
  `!a b. (n2w a):'a word > n2w b = let sa = BIT ^HB a and sb = BIT ^HB b in
    (sa = sb) /\ a MOD ^TOP > b MOD ^TOP \/ ~sa /\ sb`, ORDER_WORD_TAC);

val word_le_n2w = store_thm("word_le_n2w",
  `!a b. (n2w a):'a word <= n2w b = let sa = BIT ^HB a and sb = BIT ^HB b in
    (sa = sb) /\ a MOD ^TOP <= b MOD ^TOP \/ sa /\ ~sb`, ORDER_WORD_TAC);

val word_ge_n2w = store_thm("word_ge_n2w",
  `!a b. (n2w a):'a word >= n2w b = let sa = BIT ^HB a and sb = BIT ^HB b in
    (sa = sb) /\ a MOD ^TOP >= b MOD ^TOP \/ ~sa /\ sb`, ORDER_WORD_TAC);

val word_ls_n2w = store_thm("word_ls_n2w",
  `!a b. (n2w a):'a word <=+ n2w b = a MOD ^TOP <= b MOD ^TOP`,
  ORDER_WORD_TAC);

val word_hi_n2w = store_thm("word_hi_n2w",
  `!a b. (n2w a):'a word >+ n2w b = a MOD ^TOP > b MOD ^TOP`,
  ORDER_WORD_TAC);

val word_lo_n2w = store_thm("word_lo_n2w",
  `!a b. (n2w a):'a word <+ n2w b = a MOD ^TOP < b MOD ^TOP`,
  ORDER_WORD_TAC);

val word_hs_n2w = store_thm("word_hs_n2w",
  `!a b. (n2w a):'a word >=+ n2w b = a MOD ^TOP >= b MOD ^TOP`,
  ORDER_WORD_TAC);

(* ------------------------------------------------------------------------- *)
(* Support for termination proofs                                            *)
(* ------------------------------------------------------------------------- *)

val WORD_PRED_THM = store_thm("WORD_PRED_THM",
  `!m:'a word. ~(m = 0w) ==> w2n (m - 1w) < w2n m`,
  Cases_word \\ Cases_on `n` \\  RW_TAC arith_ss [w2n_n2w]
    \\ POP_ASSUM MP_TAC \\ SIMP_TAC arith_ss [ZERO_MOD,ZERO_LT_TWOEXP,
         ADD1,WORD_ADD_SUB,GSYM word_add_n2w,w2n_n2w,n2w_11,
         (SIMP_RULE arith_ss [ZERO_LT_TWOEXP] o SPEC `^TOP`) MOD_ADD_1]);

(* ------------------------------------------------------------------------- *)
(* Create a few word sizes                                                   *)
(* ------------------------------------------------------------------------- *)

val sizes = [2, 3, 4, 5, 6, 7, 8, 12, 16, 20, 24, 28, 32, 64];

fun mk_word_size n =
  let val _ = fcpLib.mk_index_type n
      val sn = Int.toString n
      val TYPE = mk_type("cart", [bool, mk_type("i"^sn, [])])
  in
    type_abbrev("word"^sn, TYPE)
  end;

val _ = List.app mk_word_size sizes;

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
