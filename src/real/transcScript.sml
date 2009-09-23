(*===========================================================================*)
(* Definitions of the transcendental functions etc.                          *)
(*===========================================================================*)

(*
*)
structure transcScript =
struct

(*
app load ["hol88Lib",
          "numLib",
          "reduceLib",
          "pairTheory",
          "jrhUtils",
          "powserTheory",
          "Diff",
          "mesonLib",
          "RealArith"];

*)

open HolKernel Parse boolLib;
infix THEN THENC THENL ORELSE ORELSEC ##;

open hol88Lib
     reduceLib
     pairTheory
     numTheory
     prim_recTheory
     arithmeticTheory
     realTheory
     topologyTheory
     netsTheory
     seqTheory
     limTheory
     powserTheory
     numLib
     PairedLambda
     jrhUtils
     Diff
     mesonLib
     RealArith;

val _ = new_theory "transc";


val _ = Parse.reveal "B";

(*---------------------------------------------------------------------------*)
(* Some miscellaneous lemmas                                                 *)
(*---------------------------------------------------------------------------*)

val MULT_DIV_2 = prove
 ((--`!n. (2 * n) DIV 2 = n`--),
  GEN_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  MP_TAC(SPECL [(--`2:num`--), (--`0:num`--)] DIV_MULT) THEN REDUCE_TAC THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_ACCEPT_TAC);

val EVEN_DIV2 = prove
 ((--`!n. ~(EVEN n) ==> ((SUC n) DIV 2 = SUC((n - 1) DIV 2))`--),
  GEN_TAC THEN REWRITE_TAC[EVEN_ODD, ODD_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`m:num`--) SUBST1_TAC) THEN
  REWRITE_TAC[SUC_SUB1] THEN REWRITE_TAC[ADD1, GSYM ADD_ASSOC] THEN
  SUBST1_TAC(EQT_ELIM(REDUCE_CONV (--`1 + 1:num = 2 * 1`--))) THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB, MULT_DIV_2]);


(*---------------------------------------------------------------------------*)
(* The three functions we define by series are exp, sin, cos                 *)
(*---------------------------------------------------------------------------*)

val sin_ser =
 (--`\n. if EVEN n then &0
         else ((~(&1)) pow ((n - 1) DIV 2)) / &(FACT n)`--);

val cos_ser =
   (--`\n. if EVEN n then ((~(&1)) pow (n DIV 2)) / &(FACT n) else &0`--);

val exp_ser = (--`\n. inv(&(FACT n))`--);

val exp = new_definition("exp",
  (--`exp(x) = suminf(\n. (^exp_ser) n * (x pow n))`--));

val cos = new_definition("cos",
  (--`cos(x) = suminf(\n. (^cos_ser) n * (x pow n))`--));

val sin = new_definition("sin",
  (--`sin(x) = suminf(\n. (^sin_ser) n * (x pow n))`--));

(*---------------------------------------------------------------------------*)
(* Show the series for exp converges, using the ratio test                   *)
(*---------------------------------------------------------------------------*)

val EXP_CONVERGES = store_thm("EXP_CONVERGES",
  (--`!x. (\n. (^exp_ser) n * (x pow n)) sums exp(x)`--),
  let fun fnz tm =
    (GSYM o MATCH_MP REAL_LT_IMP_NE o
     REWRITE_RULE[GSYM REAL_LT] o C SPEC FACT_LESS) tm in
  GEN_TAC THEN REWRITE_TAC[exp] THEN MATCH_MP_TAC SUMMABLE_SUM THEN
  MATCH_MP_TAC SER_RATIO THEN
  MP_TAC (SPEC (--`&1`--) REAL_DOWN) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`c:real`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`c:real`--) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC (--`c:real`--) REAL_ARCH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC (--`abs(x)`--)) THEN
  DISCH_THEN(X_CHOOSE_TAC (--`N:num`--)) THEN EXISTS_TAC (--`N:num`--) THEN
  X_GEN_TAC (--`n:num`--) THEN REWRITE_TAC[GREATER_EQ] THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[ADD1, POW_ADD, ABS_MUL, REAL_MUL_ASSOC, POW_1] THEN
  GEN_REWR_TAC LAND_CONV  [REAL_MUL_SYM] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL_IMP THEN
  REWRITE_TAC[ABS_POS] THEN REWRITE_TAC[GSYM ADD1, FACT] THEN
  REWRITE_TAC[GSYM REAL_MUL, MATCH_MP REAL_INV_MUL (CONJ
   (REWRITE_RULE[GSYM REAL_INJ] (SPEC (--`n:num`--) NOT_SUC)) (fnz (--`n:num`--)))] THEN
  REWRITE_TAC[ABS_MUL, REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL_IMP THEN REWRITE_TAC[ABS_POS] THEN
  MP_TAC(SPEC (--`n:num`--) LESS_0) THEN REWRITE_TAC[GSYM REAL_LT] THEN
  DISCH_THEN(ASSUME_TAC o GSYM o MATCH_MP REAL_LT_IMP_NE) THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP ABS_INV th]) THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_LE_LDIV THEN
  ASM_REWRITE_TAC[GSYM ABS_NZ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[REWRITE_RULE[GSYM ABS_REFL, GSYM REAL_LE] ZERO_LESS_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`&N * c`--) THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC,
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_LE_RMUL th]) THEN
    REWRITE_TAC[REAL_LE] THEN MATCH_MP_TAC LESS_EQ_TRANS THEN
    EXISTS_TAC (--`n:num`--) THEN ASM_REWRITE_TAC[LESS_EQ_SUC_REFL]] end);

(*---------------------------------------------------------------------------*)
(* Show by the comparison test that sin and cos converge                     *)
(*---------------------------------------------------------------------------*)

val SIN_CONVERGES = store_thm("SIN_CONVERGES",
  (--`!x. (\n. (^sin_ser) n * (x pow n)) sums sin(x)`--),
  GEN_TAC THEN REWRITE_TAC[sin] THEN MATCH_MP_TAC SUMMABLE_SUM THEN
  MATCH_MP_TAC SER_COMPAR THEN
  EXISTS_TAC (--`\n. ^exp_ser n * (abs(x) pow n)`--) THEN
  REWRITE_TAC[MATCH_MP SUM_SUMMABLE (SPEC_ALL EXP_CONVERGES)] THEN
  EXISTS_TAC (--`0:num`--) THEN X_GEN_TAC (--`n:num`--) THEN
  DISCH_THEN(K ALL_TAC) THEN BETA_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[ABS_MUL, POW_ABS] THENL
   [REWRITE_TAC[ABS_0, REAL_MUL_LZERO] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[ABS_POS],
    REWRITE_TAC[real_div, ABS_MUL, POW_M1, REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL_IMP THEN REWRITE_TAC[ABS_POS] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[ABS_REFL]] THEN
  MAP_EVERY MATCH_MP_TAC [REAL_LT_IMP_LE, REAL_INV_POS] THEN
  REWRITE_TAC[REAL_LT, FACT_LESS]);

val COS_CONVERGES = store_thm("COS_CONVERGES",
  (--`!x. (\n. (^cos_ser) n * (x pow n)) sums cos(x)`--),
  GEN_TAC THEN REWRITE_TAC[cos] THEN MATCH_MP_TAC SUMMABLE_SUM THEN
  MATCH_MP_TAC SER_COMPAR THEN
  EXISTS_TAC (--`\n. (^exp_ser) n * (abs(x) pow n)`--) THEN
  REWRITE_TAC[MATCH_MP SUM_SUMMABLE (SPEC_ALL EXP_CONVERGES)] THEN
  EXISTS_TAC (--`0:num`--) THEN X_GEN_TAC (--`n:num`--) THEN
  DISCH_THEN(K ALL_TAC) THEN BETA_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[ABS_MUL, POW_ABS] THENL
   [REWRITE_TAC[real_div, ABS_MUL, POW_M1, REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL_IMP THEN REWRITE_TAC[ABS_POS] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[ABS_REFL],
    REWRITE_TAC[ABS_0, REAL_MUL_LZERO] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[ABS_POS]] THEN
  MAP_EVERY MATCH_MP_TAC [REAL_LT_IMP_LE, REAL_INV_POS] THEN
  REWRITE_TAC[REAL_LT, FACT_LESS]);

(*---------------------------------------------------------------------------*)
(* Show what the formal derivatives of these series are                      *)
(*---------------------------------------------------------------------------*)

val EXP_FDIFF = store_thm("EXP_FDIFF",
  (--`diffs ^exp_ser = ^exp_ser`--),
  REWRITE_TAC[diffs] THEN BETA_TAC THEN
  CONV_TAC(X_FUN_EQ_CONV (--`n:num`--)) THEN GEN_TAC THEN BETA_TAC THEN
  REWRITE_TAC[FACT, GSYM REAL_MUL] THEN
  SUBGOAL_THEN (--`~(&(SUC n) = &0) /\ ~(&(FACT n) = &0)`--) ASSUME_TAC THENL
   [CONJ_TAC THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN
    REWRITE_TAC[REAL_LT, LESS_0, FACT_LESS],
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_INV_MUL th]) THEN
    GEN_REWR_TAC RAND_CONV  [GSYM REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_MUL_ASSOC, REAL_EQ_RMUL] THEN DISJ2_TAC THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REWRITE_TAC[]]);

val SIN_FDIFF = store_thm("SIN_FDIFF",
  (--`diffs ^sin_ser = ^cos_ser`--),
  REWRITE_TAC[diffs] THEN BETA_TAC THEN
  CONV_TAC(X_FUN_EQ_CONV (--`n:num`--)) THEN GEN_TAC THEN BETA_TAC THEN
  COND_CASES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[EVEN]) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN REWRITE_TAC[SUC_SUB1] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FACT, GSYM REAL_MUL] THEN
  SUBGOAL_THEN (--`~(&(SUC n) = &0) /\ ~(&(FACT n) = &0)`--) ASSUME_TAC THENL
   [CONJ_TAC THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN
    REWRITE_TAC[REAL_LT, LESS_0, FACT_LESS],
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_INV_MUL th]) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    GEN_REWR_TAC RAND_CONV  [GSYM REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_MUL_ASSOC, REAL_EQ_RMUL] THEN DISJ2_TAC THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REWRITE_TAC[]]);

val COS_FDIFF = store_thm("COS_FDIFF",
  (--`diffs ^cos_ser = (\n. ~((^sin_ser) n))`--),
  REWRITE_TAC[diffs] THEN BETA_TAC THEN
  CONV_TAC(X_FUN_EQ_CONV (--`n:num`--)) THEN GEN_TAC THEN BETA_TAC THEN
  COND_CASES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[EVEN]) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO, REAL_NEG_0] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[real_div, REAL_NEG_LMUL] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN BINOP_TAC THENL
   [POP_ASSUM(SUBST1_TAC o MATCH_MP EVEN_DIV2) THEN
    REWRITE_TAC[pow] THEN REWRITE_TAC[GSYM REAL_NEG_MINUS1],
    REWRITE_TAC[FACT, GSYM REAL_MUL] THEN
    SUBGOAL_THEN (--`~(&(SUC n) = &0) /\ ~(&(FACT n) = &0)`--) ASSUME_TAC THENL
     [CONJ_TAC THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN
      REWRITE_TAC[REAL_LT, LESS_0, FACT_LESS],
      FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_INV_MUL th]) THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      GEN_REWR_TAC RAND_CONV  [GSYM REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_MUL_ASSOC, REAL_EQ_RMUL] THEN DISJ2_TAC THEN
      MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REWRITE_TAC[]]]);

(*---------------------------------------------------------------------------*)
(* Now at last we can get the derivatives of exp, sin and cos                *)
(*---------------------------------------------------------------------------*)

val SIN_NEGLEMMA = store_thm("SIN_NEGLEMMA",
  (--`!x. ~(sin x) = suminf (\n. ~((^sin_ser) n * (x pow n)))`--),
  GEN_TAC THEN MATCH_MP_TAC SUM_UNIQ THEN
  MP_TAC(MATCH_MP SER_NEG (SPEC (--`x:real`--) SIN_CONVERGES)) THEN
  BETA_TAC THEN DISCH_THEN ACCEPT_TAC);

val DIFF_EXP = store_thm("DIFF_EXP",
  (--`!x. (exp diffl exp(x))(x)`--),
  GEN_TAC THEN REWRITE_TAC[HALF_MK_ABS exp] THEN
  GEN_REWR_TAC (LAND_CONV o ONCE_DEPTH_CONV)  [GSYM EXP_FDIFF] THEN
  CONV_TAC(LAND_CONV BETA_CONV) THEN
  MATCH_MP_TAC TERMDIFF THEN EXISTS_TAC (--`abs(x) + &1`--) THEN
  REWRITE_TAC[EXP_FDIFF, MATCH_MP SUM_SUMMABLE (SPEC_ALL EXP_CONVERGES)] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`abs(x) + &1`--) THEN
  REWRITE_TAC[ABS_LE, REAL_LT_ADDR] THEN
  REWRITE_TAC[REAL_LT, ONE, LESS_0]);

val DIFF_SIN = store_thm("DIFF_SIN",
  (--`!x. (sin diffl cos(x))(x)`--),
  GEN_TAC THEN REWRITE_TAC[HALF_MK_ABS sin, cos] THEN
  ONCE_REWRITE_TAC[GSYM SIN_FDIFF] THEN
  MATCH_MP_TAC TERMDIFF THEN EXISTS_TAC (--`abs(x) + &1`--) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MATCH_MP SUM_SUMMABLE (SPEC_ALL SIN_CONVERGES)],
    REWRITE_TAC[SIN_FDIFF, MATCH_MP SUM_SUMMABLE (SPEC_ALL COS_CONVERGES)],
    REWRITE_TAC[SIN_FDIFF, COS_FDIFF] THEN BETA_TAC THEN
    MP_TAC(SPEC (--`abs(x) + &1`--) SIN_CONVERGES) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SER_NEG) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN BETA_TAC THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL],
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`abs(x) + &1`--) THEN
    REWRITE_TAC[ABS_LE, REAL_LT_ADDR] THEN
    REWRITE_TAC[REAL_LT, ONE, LESS_0]]);

val DIFF_COS = store_thm("DIFF_COS",
  (--`!x. (cos diffl ~(sin(x)))(x)`--),
  GEN_TAC THEN REWRITE_TAC[HALF_MK_ABS cos, SIN_NEGLEMMA] THEN
  ONCE_REWRITE_TAC[REAL_NEG_LMUL] THEN
  REWRITE_TAC[GSYM(CONV_RULE(RAND_CONV BETA_CONV)
    (AP_THM COS_FDIFF (--`n:num`--)))] THEN
  MATCH_MP_TAC TERMDIFF THEN EXISTS_TAC (--`abs(x) + &1`--) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MATCH_MP SUM_SUMMABLE (SPEC_ALL COS_CONVERGES)],
    REWRITE_TAC[COS_FDIFF] THEN
    MP_TAC(SPEC (--`abs(x) + &1`--) SIN_CONVERGES) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SER_NEG) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN BETA_TAC THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL],
    REWRITE_TAC[COS_FDIFF, DIFFS_NEG] THEN
    MP_TAC SIN_FDIFF THEN BETA_TAC THEN
    DISCH_THEN(fn th => REWRITE_TAC[th]) THEN
    MP_TAC(SPEC (--`abs(x) + &1`--) COS_CONVERGES) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SER_NEG) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN BETA_TAC THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL],
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`abs(x) + &1`--) THEN
    REWRITE_TAC[ABS_LE, REAL_LT_ADDR] THEN
    REWRITE_TAC[REAL_LT, ONE, LESS_0]]);

val _ = basic_diffs := !basic_diffs@[DIFF_EXP, DIFF_SIN, DIFF_COS];


(* ------------------------------------------------------------------------- *)
(* Processed versions of composition theorems.                               *)
(* ------------------------------------------------------------------------- *)

val DIFF_COMPOSITE = store_thm("DIFF_COMPOSITE",
 Term
  `((f diffl l)(x) /\ ~(f(x) = &0) ==>
        ((\x. inv(f x)) diffl ~(l / (f(x) pow 2)))(x)) /\
   ((f diffl l)(x) /\ (g diffl m)(x) /\ ~(g(x) = &0) ==>
    ((\x. f(x) / g(x)) diffl (((l * g(x)) - (m * f(x)))
                               / (g(x) pow 2)))(x)) /\
   ((f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) + g(x)) diffl (l + m))(x)) /\
   ((f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) * g(x)) diffl ((l * g(x)) + (m * f(x))))(x)) /\
   ((f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) - g(x)) diffl (l - m))(x)) /\
   ((f diffl l)(x) ==> ((\x. ~(f x)) diffl ~l)(x)) /\
   ((g diffl m)(x) ==>
         ((\x. (g x) pow n) diffl ((&n * (g x) pow (n - 1)) * m))(x)) /\
   ((g diffl m)(x) ==> ((\x. exp(g x)) diffl (exp(g x) * m))(x)) /\
   ((g diffl m)(x) ==> ((\x. sin(g x)) diffl (cos(g x) * m))(x)) /\
   ((g diffl m)(x) ==> ((\x. cos(g x)) diffl (~(sin(g x)) * m))(x))`,
  REWRITE_TAC[DIFF_INV, DIFF_DIV, DIFF_ADD, DIFF_SUB, DIFF_MUL, DIFF_NEG] THEN
  REPEAT CONJ_TAC THEN DISCH_TAC THEN
  TRY(MATCH_MP_TAC DIFF_CHAIN THEN
  ASM_REWRITE_TAC[DIFF_SIN, DIFF_COS, DIFF_EXP]) THEN
  MATCH_MP_TAC(BETA_RULE (SPEC (Term`\x. x pow n`) DIFF_CHAIN)) THEN
  ASM_REWRITE_TAC[DIFF_POW]);

val _ = basic_diffs := !basic_diffs @ CONJUNCTS DIFF_COMPOSITE;


(*---------------------------------------------------------------------------*)
(* Properties of the exponential function                                    *)
(*---------------------------------------------------------------------------*)

val EXP_0 = store_thm("EXP_0",
  (--`exp(&0) = &1`--),
  REWRITE_TAC[exp] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SUM_UNIQ THEN BETA_TAC THEN
  W(MP_TAC o C SPEC SER_0 o rand o rator o snd) THEN
  DISCH_THEN(MP_TAC o SPEC (--`1:num`--)) THEN
  REWRITE_TAC[ONE, sum] THEN
  REWRITE_TAC[ADD_CLAUSES, REAL_ADD_LID] THEN BETA_TAC THEN
  REWRITE_TAC[FACT, pow, REAL_MUL_RID, REAL_INV1] THEN
  REWRITE_TAC[SYM(ONE)] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC (--`n:num`--) THEN REWRITE_TAC[ONE, GSYM LESS_EQ] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
  REWRITE_TAC[GSYM ADD1, POW_0, REAL_MUL_RZERO, ADD_CLAUSES]);

val EXP_LE_X = store_thm("EXP_LE_X",
(--`!x. &0 <= x ==> (&1 + x) <= exp(x)`--),
GEN_TAC THEN DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
 [MP_TAC(SPECL [Term`\n. ^exp_ser n * (x pow n)`,Term`2:num`] SER_POS_LE) THEN
    REWRITE_TAC[MATCH_MP SUM_SUMMABLE (SPEC_ALL EXP_CONVERGES)] THEN
    REWRITE_TAC[GSYM exp] THEN BETA_TAC THEN
    W(C SUBGOAL_THEN (fn t => REWRITE_TAC[t]) o
    funpow 2 (fst o dest_imp) o snd) THENL
     [GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_INV_POS THEN
        REWRITE_TAC[REAL_LT, FACT_LESS],
        MATCH_MP_TAC POW_POS THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        FIRST_ASSUM ACCEPT_TAC],
      CONV_TAC(TOP_DEPTH_CONV num_CONV) THEN REWRITE_TAC[sum] THEN
      BETA_TAC THEN REWRITE_TAC[ADD_CLAUSES, FACT, pow, REAL_ADD_LID] THEN
      (* new term nets require change in proof; old:
        REWRITE_TAC[MULT_CLAUSES, REAL_INV1, REAL_MUL_LID, ADD_CLAUSES] THEN
        REWRITE_TAC[REAL_MUL_RID, SYM(ONE)]
       *)
      REWRITE_TAC[MULT_RIGHT_1, CONJUNCT1 MULT,REAL_INV1,
      REAL_MUL_LID, ADD_CLAUSES,REAL_MUL_RID, SYM(ONE)]],
    POP_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[EXP_0, REAL_ADD_RID, REAL_LE_REFL]]);

val EXP_LT_1 = store_thm("EXP_LT_1",
  (--`!x. &0 < x ==> &1 < exp(x)`--),
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC (--`&1 + x`--) THEN ASM_REWRITE_TAC[REAL_LT_ADDR] THEN
  MATCH_MP_TAC EXP_LE_X THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  POP_ASSUM ACCEPT_TAC);

val EXP_ADD_MUL = store_thm("EXP_ADD_MUL",
  (--`!x y. exp(x + y) * exp(~x) = exp(y)`--),
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(X_BETA_CONV (--`x:real`--))) THEN
  SUBGOAL_THEN (--`exp(y) = (\x. exp(x + y) * exp(~x))(&0)`--) SUBST1_TAC THENL
   [BETA_TAC THEN REWRITE_TAC[REAL_ADD_LID, REAL_NEG_0] THEN
    REWRITE_TAC[EXP_0, REAL_MUL_RID],
    MATCH_MP_TAC DIFF_ISCONST_ALL THEN X_GEN_TAC (--`x:real`--) THEN
    W(MP_TAC o DIFF_CONV o rand o funpow 2 rator o snd) THEN
    DISCH_THEN(MP_TAC o SPEC (--`x:real`--)) THEN
    MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC[GSYM real_sub, REAL_SUB_0, REAL_MUL_RID, REAL_ADD_RID] THEN
    MATCH_ACCEPT_TAC REAL_MUL_SYM]);

val EXP_NEG_MUL = store_thm("EXP_NEG_MUL",
  (--`!x. exp(x) * exp(~x) = &1`--),
  GEN_TAC THEN MP_TAC(SPECL [(--`x:real`--), (--`&0`--)] EXP_ADD_MUL) THEN
  REWRITE_TAC[REAL_ADD_RID, EXP_0]);

val EXP_NEG_MUL2 = store_thm("EXP_NEG_MUL2",
  (--`!x. exp(~x) * exp(x) = &1`--),
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_ACCEPT_TAC EXP_NEG_MUL);

val EXP_NEG = store_thm("EXP_NEG",
  (--`!x. exp(~x) = inv(exp(x))`--),
  GEN_TAC THEN MATCH_MP_TAC REAL_RINV_UNIQ THEN
  MATCH_ACCEPT_TAC EXP_NEG_MUL);

val EXP_ADD = store_thm("EXP_ADD",
  (--`!x y. exp(x + y) = exp(x) * exp(y)`--),
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [(--`x:real`--), (--`y:real`--)] EXP_ADD_MUL) THEN
  DISCH_THEN(MP_TAC o C AP_THM (--`exp(x)`--) o AP_TERM (--`$*`--)) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] EXP_NEG_MUL, REAL_MUL_RID] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_ACCEPT_TAC REAL_MUL_SYM);

val EXP_POS_LE = store_thm("EXP_POS_LE",
  (--`!x. &0 <= exp(x)`--),
  GEN_TAC THEN
  GEN_REWR_TAC (funpow 2 RAND_CONV)  [GSYM REAL_HALF_DOUBLE] THEN
  REWRITE_TAC[EXP_ADD] THEN MATCH_ACCEPT_TAC REAL_LE_SQUARE);

val EXP_NZ = store_thm("EXP_NZ",
  (--`!x. ~(exp(x) = &0)`--),
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC (--`x:real`--) EXP_NEG_MUL) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  MATCH_ACCEPT_TAC REAL_10);

val EXP_POS_LT = store_thm("EXP_POS_LT",
  (--`!x. &0 < exp(x)`--),
  GEN_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  REWRITE_TAC[EXP_POS_LE, EXP_NZ]);

val EXP_N = store_thm("EXP_N",
  (--`!n x. exp(&n * x) = exp(x) pow n`--),
  INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO, EXP_0, pow] THEN
  REWRITE_TAC[ADD1] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[GSYM REAL_ADD, EXP_ADD, REAL_RDISTRIB] THEN
  GEN_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LID]);

val EXP_SUB = store_thm("EXP_SUB",
  (--`!x y. exp(x - y) = exp(x) / exp(y)`--),
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_sub, real_div, EXP_ADD, EXP_NEG]);

val EXP_MONO_IMP = store_thm("EXP_MONO_IMP",
  (--`!x y. x < y ==> exp(x) < exp(y)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o
    MATCH_MP EXP_LT_1 o ONCE_REWRITE_RULE[GSYM REAL_SUB_LT]) THEN
  REWRITE_TAC[EXP_SUB] THEN
  SUBGOAL_THEN (--`&1 < exp(y) / exp(x) =
                 (&1 * exp(x)) < ((exp(y) / exp(x)) * exp(x))`--) SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LT_RMUL THEN
    MATCH_ACCEPT_TAC EXP_POS_LT,
    REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC, EXP_NEG_MUL2, GSYM EXP_NEG] THEN
    REWRITE_TAC[REAL_MUL_LID, REAL_MUL_RID]]);

val EXP_MONO_LT = store_thm("EXP_MONO_LT",
  (--`!x y. exp(x) < exp(y) = x < y`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[REAL_NOT_LT] THEN
    REWRITE_TAC[REAL_LE_LT] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    REWRITE_TAC[] THEN DISJ1_TAC THEN MATCH_MP_TAC EXP_MONO_IMP THEN
    POP_ASSUM ACCEPT_TAC,
    MATCH_ACCEPT_TAC EXP_MONO_IMP]);

val EXP_MONO_LE = store_thm("EXP_MONO_LE",
  (--`!x y. exp(x) <= exp(y) = x <= y`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  REWRITE_TAC[EXP_MONO_LT]);

val EXP_INJ = store_thm("EXP_INJ",
  (--`!x y. (exp(x) = exp(y)) = (x = y)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  REWRITE_TAC[EXP_MONO_LE]);

val EXP_TOTAL_LEMMA = store_thm("EXP_TOTAL_LEMMA",
  (--`!y. &1 <= y ==> ?x. &0 <= x /\ x <= y - &1 /\ (exp(x) = y)`--),
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC IVT THEN
  ASM_REWRITE_TAC[EXP_0, REAL_LE_SUB_LADD, REAL_ADD_LID] THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM REAL_SUB_LE]) THEN
    POP_ASSUM(MP_TAC o MATCH_MP EXP_LE_X) THEN REWRITE_TAC[REAL_SUB_ADD2],
    X_GEN_TAC (--`x:real`--) THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC (--`exp(x)`--) THEN
    MATCH_ACCEPT_TAC DIFF_EXP]);

val EXP_TOTAL = store_thm("EXP_TOTAL",
  (--`!y. &0 < y ==> ?x. exp(x) = y`--),
  GEN_TAC THEN DISCH_TAC THEN
  DISJ_CASES_TAC(SPECL [(--`&1`--), (--`y:real`--)] REAL_LET_TOTAL) THENL
   [FIRST_ASSUM(X_CHOOSE_TAC (--`x:real`--) o MATCH_MP EXP_TOTAL_LEMMA) THEN
    EXISTS_TAC (--`x:real`--) THEN ASM_REWRITE_TAC[],
    MP_TAC(SPEC (--`y:real`--) REAL_INV_LT1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
    DISCH_THEN(X_CHOOSE_TAC (--`x:real`--) o MATCH_MP EXP_TOTAL_LEMMA) THEN
    EXISTS_TAC (--`~x`--) THEN ASM_REWRITE_TAC[EXP_NEG] THEN
    MATCH_MP_TAC REAL_INVINV THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN ASM_REWRITE_TAC[]]);

(* new
let REAL_EXP_BOUND_LEMMA = prove
 (`!x. &0 <= x /\ x <= inv(&2) ==> exp(x) <= &1 + &2 * x`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `suminf (\n. x pow n)` THEN CONJ_TAC THENL
   [REWRITE_TAC[exp; BETA_THM] THEN MATCH_MP_TAC SER_LE THEN
    REWRITE_TAC[summable; BETA_THM] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL_IMP THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_INV_LE_1 THEN
        REWRITE_TAC[REAL_OF_NUM_LE; num_CONV `1`; LE_SUC_LT] THEN
        REWRITE_TAC[FACT_LT]];
      EXISTS_TAC `exp x` THEN REWRITE_TAC[BETA_RULE REAL_EXP_CONVERGES];
      EXISTS_TAC `inv(&1 - x)` THEN MATCH_MP_TAC GP THEN
      ASM_REWRITE_TAC[real_abs] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&2)` THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    SUBGOAL_THEN `suminf (\n. x pow n) = inv (&1 - x)` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_UNIQ THEN
      MATCH_MP_TAC GP THEN
      ASM_REWRITE_TAC[real_abs] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&2)` THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
      EXISTS_TAC `&1 - x` THEN
      SUBGOAL_THEN `(&1 - x) * inv (&1 - x) = &1` SUBST1_TAC THENL
       [MATCH_MP_TAC REAL_MUL_RINV THEN
        REWRITE_TAC[REAL_ARITH `(&1 - x = &0) = (x = &1)`] THEN
        DISCH_THEN SUBST_ALL_TAC THEN
        POP_ASSUM MP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LET_TRANS THEN
          EXISTS_TAC `inv(&2) - x` THEN
          ASM_REWRITE_TAC[REAL_ARITH `&0 <= x - y = y <= x`] THEN
          ASM_REWRITE_TAC[REAL_ARITH `a - x < b - x = a < b`] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV;
          REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_SUB_RDISTRIB] THEN
          REWRITE_TAC[REAL_MUL_RID; REAL_MUL_LID] THEN
          REWRITE_TAC[REAL_ARITH `&1 <= (&1 + &2 * x) - (x + x * &2 * x) =
                                  x * (&2 * x) <= x * &1`] THEN
          MATCH_MP_TAC REAL_LE_LMUL_IMP THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `inv(&2)` THEN
          REWRITE_TAC[REAL_MUL_ASSOC] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV THEN
          ASM_REWRITE_TAC[REAL_MUL_LID; real_div]]]]]);;
end new*)

(*---------------------------------------------------------------------------*)
(* Properties of the logarithmic function                                    *)
(*---------------------------------------------------------------------------*)

val ln = new_definition("ln",
  (--`ln x = @u. exp(u) = x`--));

val LN_EXP = store_thm("LN_EXP",
  (--`!x. ln(exp x) = x`--),
  GEN_TAC THEN REWRITE_TAC[ln, EXP_INJ] THEN
  CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN MATCH_MP_TAC SELECT_AX THEN
  EXISTS_TAC (--`x:real`--) THEN REFL_TAC);

val EXP_LN = store_thm("EXP_LN",
  (--`!x. (exp(ln x) = x) = &0 < x`--),
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC EXP_POS_LT,
    DISCH_THEN(X_CHOOSE_THEN (--`y:real`--) MP_TAC o MATCH_MP EXP_TOTAL) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[EXP_INJ, LN_EXP]]);

val LN_MUL = store_thm("LN_MUL",
  (--`!x y. &0 < x /\ &0 < y ==> (ln(x * y) = ln(x) + ln(y))`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM EXP_INJ] THEN
  REWRITE_TAC[EXP_ADD] THEN SUBGOAL_THEN (--`&0 < x * y`--) ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[],
    EVERY_ASSUM(fn th => REWRITE_TAC[ONCE_REWRITE_RULE[GSYM EXP_LN] th])]);

val LN_INJ = store_thm("LN_INJ",
  (--`!x y. &0 < x /\ &0 < y ==> ((ln(x) = ln(y)) = (x = y))`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EVERY_ASSUM(fn th => GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV)
    [SYM(REWRITE_RULE[GSYM EXP_LN] th)]) THEN
  CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC EXP_INJ);

val LN_1 = store_thm("LN_1",
  (--`ln(&1) = &0`--),
  ONCE_REWRITE_TAC[GSYM EXP_INJ] THEN
  REWRITE_TAC[EXP_0, EXP_LN, REAL_LT_01]);

val LN_INV = store_thm("LN_INV",
  (--`!x. &0 < x ==> (ln(inv x) = ~(ln x))`--),
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_RNEG_UNIQ] THEN
  SUBGOAL_THEN (--`&0 < x /\ &0 < inv(x)`--) MP_TAC THENL
   [CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_INV_POS) THEN ASM_REWRITE_TAC[],
    DISCH_THEN(fn th => REWRITE_TAC[GSYM(MATCH_MP LN_MUL th)]) THEN
    SUBGOAL_THEN (--`x * (inv x) = &1`--) SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_RINV THEN
      POP_ASSUM(ACCEPT_TAC o MATCH_MP REAL_POS_NZ),
      REWRITE_TAC[LN_1]]]);

val LN_DIV = store_thm("LN_DIV",
  (--`!x y. &0 < x /\ &0 < y ==> (ln(x / y) = ln(x) - ln(y))`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (--`&0 < x /\ &0 < inv(y)`--) MP_TAC THENL
   [CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_INV_POS) THEN ASM_REWRITE_TAC[],
    REWRITE_TAC[real_div] THEN
    DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP LN_MUL th]) THEN
    REWRITE_TAC[MATCH_MP LN_INV (ASSUME (--`&0 < y`--))] THEN
    REWRITE_TAC[real_sub]]);

val LN_MONO_LT = store_thm("LN_MONO_LT",
  (--`!x y. &0 < x /\ &0 < y ==> (ln(x) < ln(y) = x < y)`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EVERY_ASSUM(fn th => GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV)
    [SYM(REWRITE_RULE[GSYM EXP_LN] th)]) THEN
  CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC EXP_MONO_LT);

val LN_MONO_LE = store_thm("LN_MONO_LE",
  (--`!x y. &0 < x /\ &0 < y ==> (ln(x) <= ln(y) = x <= y)`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EVERY_ASSUM(fn th => GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV)
    [SYM(REWRITE_RULE[GSYM EXP_LN] th)]) THEN
  CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC EXP_MONO_LE);

val LN_POW = store_thm("LN_POW",
  (--`!n x. &0 < x ==> (ln(x pow n) = &n * ln(x))`--),
  REPEAT GEN_TAC THEN
  DISCH_THEN(CHOOSE_THEN (SUBST1_TAC o SYM) o MATCH_MP EXP_TOTAL) THEN
  REWRITE_TAC[GSYM EXP_N, LN_EXP]);


val LN_LE = store_thm("LN_LE",
  Term `!x. &0 <= x ==> ln(&1 + x) <= x`,
  GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC RAND_CONV  [] [GSYM LN_EXP] THEN
  MP_TAC(SPECL [Term`&1 + x`, Term`exp x`] LN_MONO_LE) THEN
  W(C SUBGOAL_THEN (fn t => REWRITE_TAC[t]) o funpow 2 (fst o dest_imp) o snd)
  THENL
   [REWRITE_TAC[EXP_POS_LT] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (Term`x:real`) THEN ASM_REWRITE_TAC[REAL_LT_ADDL, REAL_LT_01],
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC EXP_LE_X THEN ASM_REWRITE_TAC[]]);;


val LN_LT_X = store_thm("LN_LT_X",
  (--`!x. &0 < x ==> ln(x) < x`--),
  GEN_TAC THEN DISCH_TAC THEN
  GEN_REWR_TAC I  [TAUT_CONV (--`a:bool = ~~a`--)] THEN
  PURE_REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPEC (--`ln(x)`--) EXP_LE_X) THEN
  SUBGOAL_THEN (--`&0 <= ln(x)`--) ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`x:real`--) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE, ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MP_TAC(SPEC (--`x:real`--) EXP_LN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN (--`(&1 + ln(x)) <= ln(x)`--) MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`x:real`--), ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_NOT_LE] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`&0 + ln(x)`--) THEN
  REWRITE_TAC[REAL_LT_RADD, REAL_LT_01] THEN
  REWRITE_TAC[REAL_ADD_LID, REAL_LE_REFL]);

val LN_POS = store_thm("LN_POS",
  Term `!x. &1 <= x ==> &0 <= ln(x)`,
  GEN_TAC THEN DISCH_TAC THEN SUBGOAL_THEN (Term `&0 < x`) ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (Term`&1`) THEN
    ASM_REWRITE_TAC[REAL_LT_01],
    UNDISCH_TAC (Term`&1 <= x`) THEN SUBST1_TAC(SYM EXP_0) THEN
    POP_ASSUM(MP_TAC o REWRITE_RULE[GSYM EXP_LN]) THEN
    DISCH_THEN(fn th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [] [SYM th])
    THEN REWRITE_TAC[EXP_MONO_LE]]);;


val DIFF_LN = store_thm("DIFF_LN",
  Term `!x. &0 < x ==> (ln diffl (inv x))(x)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[GSYM EXP_LN]) THEN
  FIRST_ASSUM (fn th =>  GEN_REWRITE_TAC RAND_CONV [] [GSYM th]) THEN
  MATCH_MP_TAC DIFF_INVERSE_LT THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_POS_NZ) THEN
  ASM_REWRITE_TAC[MATCH_MP DIFF_CONT (SPEC_ALL DIFF_EXP)] THEN
  MP_TAC(SPEC (Term`ln(x)`) DIFF_EXP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[LN_EXP] THEN
  EXISTS_TAC (Term`&1`) THEN MATCH_ACCEPT_TAC REAL_LT_01);;


(*---------------------------------------------------------------------------*)
(* Some properties of roots (easier via logarithms)                          *)
(*---------------------------------------------------------------------------*)

val root = new_definition("root",
  (--`root(n) x = @u. (&0 < x ==> &0 < u) /\ (u pow n = x)`--));

val sqrt = new_definition("sqrt",
  (--`sqrt(x) = root(2) x`--));

val ROOT_LT_LEMMA = store_thm("ROOT_LT_LEMMA",
  (--`!n x. &0 < x ==> (exp(ln(x) / &(SUC n)) pow (SUC n) = x)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM EXP_N] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN
  SUBGOAL_THEN (--`inv(&(SUC n)) * &(SUC n) = &1`--) SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC[REAL_INJ, NOT_SUC],
    ASM_REWRITE_TAC[REAL_MUL_RID, EXP_LN]]);

val ROOT_LN = store_thm("ROOT_LN",
  (--`!n x. &0 < x ==> (root(SUC n) x = exp(ln(x) / &(SUC n)))`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[root] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC (--`y:real`--) THEN BETA_TAC THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    SUBGOAL_THEN (--`!z. &0 < y /\ &0 < exp(z)`--) MP_TAC THENL
     [ASM_REWRITE_TAC[EXP_POS_LT], ALL_TAC] THEN
    DISCH_THEN(MP_TAC o GEN_ALL o SYM o MATCH_MP LN_INJ o SPEC_ALL) THEN
    DISCH_THEN(fn th => GEN_REWR_TAC I  [th]) THEN
    REWRITE_TAC[LN_EXP] THEN
    SUBGOAL_THEN (--`ln(y) * &(SUC n) = (ln(y pow(SUC n)) / &(SUC n)) * &(SUC n)`--)
    MP_TAC THENL
     [REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN
      SUBGOAL_THEN (--`inv(&(SUC n)) * &(SUC n) = &1`--) SUBST1_TAC THENL
       [MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC[REAL_INJ, NOT_SUC],
        REWRITE_TAC[REAL_MUL_RID] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC LN_POW THEN
        ASM_REWRITE_TAC[]],
      REWRITE_TAC[REAL_EQ_RMUL, REAL_INJ, NOT_SUC]],
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXP_POS_LT] THEN
    MATCH_MP_TAC ROOT_LT_LEMMA THEN ASM_REWRITE_TAC[]]);

val ROOT_0 = store_thm("ROOT_0",
  (--`!n. root(SUC n) (&0) = &0`--),
  GEN_TAC THEN REWRITE_TAC[root] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC (--`y:real`--) THEN
  BETA_TAC THEN REWRITE_TAC[REAL_LT_REFL] THEN EQ_TAC THENL
   [SPEC_TAC((--`n:num`--),(--`n:num`--)) THEN INDUCT_TAC THEN ONCE_REWRITE_TAC[pow] THENL
     [REWRITE_TAC[pow, REAL_MUL_RID],
      REWRITE_TAC[REAL_ENTIRE] THEN DISCH_THEN DISJ_CASES_TAC THEN
      ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]],
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[pow, REAL_MUL_LZERO]]);

val ROOT_1 = store_thm("ROOT_1",
  (--`!n. root(SUC n) (&1) = &1`--),
  GEN_TAC THEN REWRITE_TAC[MATCH_MP ROOT_LN REAL_LT_01] THEN
  REWRITE_TAC[LN_1, REAL_DIV_LZERO, EXP_0]);

val ROOT_POS_LT = store_thm("ROOT_POS_LT",
  (--`!n x. &0 < x ==> &0 < root(SUC n) x`--),
  REPEAT GEN_TAC THEN
  DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP ROOT_LN th]) THEN
  REWRITE_TAC[EXP_POS_LT]);

val ROOT_POW_POS = store_thm("ROOT_POW_POS",
  (--`!n x. &0 <= x ==> ((root(SUC n) x) pow (SUC n) = x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [FIRST_ASSUM(fn th => REWRITE_TAC
     [MATCH_MP ROOT_LN th, MATCH_MP ROOT_LT_LEMMA th]),
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[ROOT_0] THEN
    MATCH_ACCEPT_TAC POW_0]);

val POW_ROOT_POS = store_thm("POW_ROOT_POS",
  (--`!n x. &0 <= x ==> (root(SUC n)(x pow (SUC n)) = x)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[root] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC (--`y:real`--) THEN BETA_TAC THEN EQ_TAC THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THENL
   [DISJ_CASES_THEN MP_TAC (REWRITE_RULE[REAL_LE_LT] (ASSUME (--`&0 <= x`--))) THENL
     [DISCH_TAC THEN FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
      FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP POW_POS_LT th]) THEN
      DISCH_TAC THEN MATCH_MP_TAC POW_EQ THEN EXISTS_TAC (--`n:num`--) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      ASM_REWRITE_TAC[],
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
      REWRITE_TAC[POW_0, REAL_LT_REFL, POW_ZERO]],
    ASM_REWRITE_TAC[REAL_LT_LE] THEN CONV_TAC CONTRAPOS_CONV THEN
    REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[POW_0]]);


(* Known in GTT as ROOT_POS_POSITIVE *)
val ROOT_POS = store_thm("ROOT_POS",
  (--`!n x. &0 <= x ==> &0 <= root(SUC n) x`--),
  REPEAT GEN_TAC THEN
  DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [MAP_EVERY MATCH_MP_TAC [REAL_LT_IMP_LE, ROOT_POS_LT] THEN
    POP_ASSUM ACCEPT_TAC,
    POP_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[ROOT_0, REAL_LE_REFL]]);

val ROOT_POS_UNIQ = store_thm("ROOT_POS_UNIQ",
 Term`!n x y. &0 <= x /\ &0 <= y /\ (y pow (SUC n) = x)
           ==> (root (SUC n) x = y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[POW_ROOT_POS]);;

val ROOT_MUL = store_thm("ROOT_MUL",
 Term`!n x y. &0 <= x /\ &0 <= y
           ==> (root(SUC n) (x * y) = root(SUC n) x * root(SUC n) y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ROOT_POS_UNIQ THEN
  REWRITE_TAC [POW_MUL] THEN REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[],
   MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC ROOT_POS
   THEN ASM_REWRITE_TAC[],
   IMP_RES_TAC ROOT_POW_POS THEN ASM_REWRITE_TAC[]]);


val ROOT_INV = store_thm("ROOT_INV",
 Term`!n x. &0 <= x ==> (root(SUC n) (inv x) = inv(root(SUC n) x))`,
REPEAT STRIP_TAC THEN MATCH_MP_TAC ROOT_POS_UNIQ THEN REPEAT CONJ_TAC THENL
 [IMP_RES_THEN ACCEPT_TAC REAL_LE_INV,
  MATCH_MP_TAC REAL_LE_INV THEN IMP_RES_THEN (TRY o MATCH_ACCEPT_TAC) ROOT_POS,
  IMP_RES_TAC ROOT_POW_POS THEN MP_TAC (SPEC_ALL ROOT_POS)
   THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [REAL_LE_LT]
    THEN STRIP_TAC THENL
    [IMP_RES_TAC REAL_POS_NZ THEN IMP_RES_THEN (fn th =>
       REWRITE_TAC [GSYM th]) POW_INV THEN ASM_REWRITE_TAC[],
     POP_ASSUM (ASSUME_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
     PAT_ASSUM (Term `$! M`) (SUBST1_TAC o SYM o SPEC_ALL)
      THEN ASM_REWRITE_TAC[REAL_INV_0,POW_0]]])

val ROOT_DIV = store_thm("ROOT_DIV",
 Term`!n x y. &0 <= x /\ &0 <= y
           ==> (root(SUC n) (x / y) = root(SUC n) x / root(SUC n) y)`,
REWRITE_TAC [real_div] THEN REPEAT STRIP_TAC THEN IMP_RES_TAC REAL_LE_INV
 THEN MP_TAC (SPECL [Term`n:num`, Term`x:real`, Term`inv y`] ROOT_MUL)
 THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
 THEN IMP_RES_TAC (SPECL [Term`n:num`, Term`y:real`] ROOT_INV)
 THEN ASM_REWRITE_TAC[]);


val ROOT_MONO_LE = store_thm("ROOT_MONO_LE",
 Term`!x y. &0 <= x /\ x <= y ==> root(SUC n) x <= root(SUC n) y`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN (Term`&0 <= y`) ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS], ALL_TAC] THEN
  UNDISCH_TAC (Term`x <= y`) THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN (Term `(x = (root(SUC n) x) pow (SUC n)) /\
                      (y = (root(SUC n) y) pow (SUC n))`)
   (CONJUNCTS_THEN SUBST1_TAC)
  THENL [IMP_RES_TAC (GSYM ROOT_POW_POS) THEN ASM_MESON_TAC[], ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LT2 THEN
  ASM_REWRITE_TAC[NOT_SUC] THEN MATCH_MP_TAC ROOT_POS THEN ASM_REWRITE_TAC[]);

val SQRT_0 = store_thm("SQRT_0",
  (--`sqrt(&0) = &0`--),
  REWRITE_TAC[sqrt, TWO, ROOT_0]);

val SQRT_1 = store_thm("SQRT_1",
  (--`sqrt(&1) = &1`--),
  REWRITE_TAC[sqrt, TWO, ROOT_1]);

val SQRT_POS_LT = store_thm("SQRT_POS_LT",
 Term`!x. &0 < x ==> &0 < sqrt(x)`,
 REWRITE_TAC [sqrt,TWO] THEN REPEAT STRIP_TAC
  THEN IMP_RES_TAC ROOT_LN THEN ASM_REWRITE_TAC[EXP_POS_LT]);

val SQRT_POS_LE = store_thm("SQRT_POS_LE",
 Term`!x. &0 <= x ==> &0 <= sqrt(x)`,
  REWRITE_TAC[REAL_LE_LT] THEN MESON_TAC[SQRT_POS_LT, SQRT_0]);;

val SQRT_POW2 = store_thm("SQRT_POW2",
  (--`!x. (sqrt(x) pow 2 = x) = &0 <= x`--),
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC REAL_LE_POW2,
    REWRITE_TAC[sqrt, TWO, ROOT_POW_POS]]);

val SQRT_POW_2 = store_thm("SQRT_POW_2",
 Term `!x. &0 <= x ==> (sqrt(x) pow 2 = x)`,
  REWRITE_TAC[SQRT_POW2]);;

val POW_2_SQRT = store_thm("POW_2_SQRT",
 Term`&0 <= x ==> (sqrt(x pow 2) = x)`,
 REWRITE_TAC [sqrt,TWO,POW_ROOT_POS]);

val SQRT_POS_UNIQ = store_thm("SQRT_POS_UNIQ",
 Term`!x y. &0 <= x /\ &0 <= y /\ (y pow 2 = x)
           ==> (sqrt x = y)`,
  REWRITE_TAC[sqrt, TWO, ROOT_POS_UNIQ]);

val SQRT_MUL = store_thm("SQRT_MUL",
 Term`!x y. &0 <= x /\ &0 <= y
           ==> (sqrt(x * y) = sqrt x * sqrt y)`,
  REWRITE_TAC[sqrt, TWO, ROOT_MUL]);;

val SQRT_INV = store_thm("SQRT_INV",
 Term`!x. &0 <= x ==> (sqrt (inv x) = inv(sqrt x))`,
  REWRITE_TAC[sqrt, TWO, ROOT_INV]);;

val SQRT_DIV = store_thm("SQRT_DIV",
 Term`!x y. &0 <= x /\ &0 <= y
           ==> (sqrt (x / y) = sqrt x / sqrt y)`,
  REWRITE_TAC[sqrt, TWO, ROOT_DIV]);;

val SQRT_MONO_LE = store_thm("SQRT_MONO_LE",
 Term`!x y. &0 <= x /\ x <= y ==> sqrt(x) <= sqrt(y)`,
  REWRITE_TAC[sqrt, TWO, ROOT_MONO_LE]);;

val lem = prove(Term`0<2:num`, REWRITE_TAC[TWO,LESS_0]);

val EVEN_MOD = prove
 (Term `!n. EVEN(n) = (n MOD 2 = 0)`,
  GEN_TAC THEN REWRITE_TAC[EVEN_EXISTS] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  EQ_TAC THEN STRIP_TAC THENL
  [ASM_REWRITE_TAC [MP (SPEC (Term`2:num`) MOD_EQ_0) lem],
   EXISTS_TAC (Term `n DIV 2`) THEN
     MP_TAC (CONJUNCT1 (SPEC (Term `n:num`) (MATCH_MP DIVISION lem))) THEN
     ASM_REWRITE_TAC [ADD_CLAUSES]]);

val SQRT_EVEN_POW2 = store_thm("SQRT_EVEN_POW2",
 Term`!n. EVEN n ==> (sqrt(&2 pow n) = &2 pow (n DIV 2))`,
 GEN_TAC THEN REWRITE_TAC[EVEN_MOD] THEN DISCH_TAC THEN
  MATCH_MP_TAC SQRT_POS_UNIQ THEN REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC POW_POS THEN REWRITE_TAC [REAL_POS],
   MATCH_MP_TAC POW_POS THEN REWRITE_TAC [REAL_POS],
   REWRITE_TAC [REAL_POW_POW] THEN AP_TERM_TAC THEN
   MP_TAC (CONJUNCT1 (SPEC (Term `n:num`) (MATCH_MP DIVISION lem)))
   THEN ASM_REWRITE_TAC [ADD_CLAUSES] THEN DISCH_THEN (SUBST1_TAC o SYM)
   THEN REFL_TAC]);


val REAL_DIV_SQRT = store_thm("REAL_DIV_SQRT",
 Term`!x. &0 <= x ==> (x / sqrt(x) = sqrt(x))`,
 GEN_TAC THEN ASM_CASES_TAC (Term`x = &0`) THENL
   [ASM_REWRITE_TAC[SQRT_0, real_div, REAL_MUL_LZERO], ALL_TAC] THEN
  DISCH_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_POS_UNIQ THEN
  ASM_REWRITE_TAC[] THEN IMP_RES_TAC SQRT_POS_LE THEN
  MP_TAC (SPECL[Term`x:real`, Term`sqrt x`] REAL_LE_DIV) THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN (fn th => CONJ_TAC THENL [ACCEPT_TAC th, ALL_TAC]) THEN
  REWRITE_TAC[real_div, POW_MUL] THEN PAT_ASSUM (Term`x <= sqrt y`) MP_TAC
  THEN REWRITE_TAC [REAL_LE_LT] THEN STRIP_TAC THENL
  [IMP_RES_TAC REAL_POS_NZ THEN IMP_RES_THEN (fn th =>
    REWRITE_TAC [GSYM th]) POW_INV THEN IMP_RES_THEN (fn th =>
    REWRITE_TAC [th]) SQRT_POW_2 THEN REWRITE_TAC[POW_2, GSYM REAL_MUL_ASSOC]
    THEN IMP_RES_THEN (fn th => REWRITE_TAC [th]) REAL_MUL_RINV THEN
    REWRITE_TAC [REAL_MUL_RID],
   PAT_ASSUM (Term `& 0 <= x`) MP_TAC THEN
   REWRITE_TAC [REAL_LE_LT] THEN STRIP_TAC THENL
   [IMP_RES_TAC SQRT_POS_LT THEN
     PAT_ASSUM (Term `& 0 = x`) (SUBST_ALL_TAC o SYM) THEN
     IMP_RES_TAC REAL_LT_REFL,
   PAT_ASSUM (Term `& 0 = x`) (SUBST_ALL_TAC o SYM)
   THEN REWRITE_TAC [POW_0, TWO, REAL_MUL_LZERO]]]);

val SQRT_EQ = store_thm("SQRT_EQ",
  (--`!x y. (x pow 2 = y) /\ (&0 <= x) ==> (x = (sqrt(y)))`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (--`&0 <= y`--) ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[POW_2, REAL_LE_SQUARE],
    ALL_TAC] THEN
  MP_TAC(SPECL [(--`1:num`--), (--`y:real`--)] ROOT_POW_POS) THEN
  ASM_REWRITE_TAC[GSYM(TWO), GSYM sqrt] THEN
  FIRST_ASSUM(fn th => GEN_REWR_TAC (LAND_CONV o RAND_CONV)  [SYM th]) THEN
  GEN_REWR_TAC LAND_CONV  [GSYM REAL_SUB_0] THEN
  REWRITE_TAC[POW_2, GSYM REAL_DIFFSQ, REAL_ENTIRE] THEN
  REWRITE_TAC[REAL_SUB_0] THEN
  DISCH_THEN DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (--`&0 <= sqrt(y)`--) ASSUME_TAC THENL
   [REWRITE_TAC[sqrt, TWO] THEN MATCH_MP_TAC ROOT_POS THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN (--`x = &0`--) SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
    GEN_REWR_TAC I  [TAUT_CONV (--`a:bool = ~~a`--)] THEN
    PURE_REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC (--`sqrt(y) + x = &0`--) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POS_NZ THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`sqrt(y)`--) THEN
    ASM_REWRITE_TAC[REAL_LT_ADDR],
    UNDISCH_TAC (--`&0 pow 2 = y`--) THEN REWRITE_TAC[POW_0, TWO] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[SQRT_0]]);

(*---------------------------------------------------------------------------*)
(* Basic properties of the trig functions                                    *)
(*---------------------------------------------------------------------------*)

val SIN_0 = store_thm("SIN_0",
  (--`sin(&0) = &0`--),
  REWRITE_TAC[sin] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SUM_UNIQ THEN BETA_TAC THEN
  W(MP_TAC o C SPEC SER_0 o rand o rator o snd) THEN
  DISCH_THEN(MP_TAC o SPEC (--`0:num`--)) THEN REWRITE_TAC[ZERO_LESS_EQ] THEN
  BETA_TAC THEN
  REWRITE_TAC[sum] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC (--`n:num`--) THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  MP_TAC(SPEC (--`n:num`--) ODD_EXISTS) THEN ASM_REWRITE_TAC[ODD_EVEN] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GSYM ADD1, POW_0, REAL_MUL_RZERO]);

val COS_0 = store_thm("COS_0",
  (--`cos(&0) = &1`--),
  REWRITE_TAC[cos] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SUM_UNIQ THEN BETA_TAC THEN
  W(MP_TAC o C SPEC SER_0 o rand o rator o snd) THEN
  DISCH_THEN(MP_TAC o SPEC (--`1:num`--)) THEN
  REWRITE_TAC[ONE, sum, ADD_CLAUSES] THEN BETA_TAC THEN
  REWRITE_TAC[EVEN, pow, FACT] THEN
  REWRITE_TAC[REAL_ADD_LID, REAL_MUL_RID] THEN
  SUBGOAL_THEN (--`0 DIV 2 = 0`--) SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQUE THEN EXISTS_TAC (--`0:num`--) THEN
    REWRITE_TAC[MULT_CLAUSES, ADD_CLAUSES] THEN
    REWRITE_TAC[TWO, LESS_0],
    REWRITE_TAC[pow]] THEN
  SUBGOAL_THEN (--`&1 / &1 = &(SUC 0)`--) SUBST1_TAC THENL
   [REWRITE_TAC[SYM(ONE)] THEN MATCH_MP_TAC REAL_DIV_REFL THEN
    MATCH_ACCEPT_TAC REAL_10,
    DISCH_THEN MATCH_MP_TAC] THEN
  X_GEN_TAC (--`n:num`--) THEN REWRITE_TAC[GSYM LESS_EQ] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
  REWRITE_TAC[GSYM ADD1, POW_0, REAL_MUL_RZERO, ADD_CLAUSES]);

val SIN_CIRCLE = store_thm("SIN_CIRCLE",
  (--`!x. (sin(x) pow 2) + (cos(x) pow 2) = &1`--),
  GEN_TAC THEN CONV_TAC(LAND_CONV(X_BETA_CONV (--`x:real`--))) THEN
  SUBGOAL_THEN (--`&1 = (\x.(sin(x) pow 2) + (cos(x) pow 2))(&0)`--) SUBST1_TAC THENL
   [BETA_TAC THEN REWRITE_TAC[SIN_0, COS_0] THEN
    REWRITE_TAC[TWO, POW_0] THEN
    REWRITE_TAC[pow, POW_1] THEN REWRITE_TAC[REAL_ADD_LID, REAL_MUL_LID],
    MATCH_MP_TAC DIFF_ISCONST_ALL THEN X_GEN_TAC (--`x:real`--) THEN
    W(MP_TAC o DIFF_CONV o rand o funpow 2 rator o snd) THEN
    DISCH_THEN(MP_TAC o SPEC (--`x:real`--)) THEN
    MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC[GSYM real_sub, REAL_SUB_0] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC, REAL_MUL_RID] THEN
    AP_TERM_TAC THEN REWRITE_TAC[TWO, SUC_SUB1] THEN
    REWRITE_TAC[POW_1] THEN MATCH_ACCEPT_TAC REAL_MUL_SYM]);

val SIN_BOUND = store_thm("SIN_BOUND",
  (--`!x. abs(sin x) <= &1`--),
  GEN_TAC THEN GEN_REWR_TAC I  [TAUT_CONV (--`a:bool = ~~a`--)] THEN
  PURE_ONCE_REWRITE_TAC[REAL_NOT_LE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT1_POW2) THEN
  REWRITE_TAC[REAL_POW2_ABS] THEN
  DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[GSYM REAL_SUB_LT]) THEN
  DISCH_THEN(MP_TAC o C CONJ(SPEC (--`cos(x)`--) REAL_LE_SQUARE)) THEN
  REWRITE_TAC[GSYM POW_2] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LTE_ADD) THEN
  REWRITE_TAC[real_sub, GSYM REAL_ADD_ASSOC] THEN
  ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
    (--`a + (b + c) = (a + c) + b`--)] THEN
  REWRITE_TAC[SIN_CIRCLE, REAL_ADD_RINV, REAL_LT_REFL]);

val SIN_BOUNDS = store_thm("SIN_BOUNDS",
  (--`!x. ~(&1) <= sin(x) /\ sin(x) <= &1`--),
  GEN_TAC THEN REWRITE_TAC[GSYM ABS_BOUNDS, SIN_BOUND]);

val COS_BOUND = store_thm("COS_BOUND",
  (--`!x. abs(cos x) <= &1`--),
  GEN_TAC THEN GEN_REWR_TAC I  [TAUT_CONV (--`a:bool = ~~a`--)] THEN
  PURE_ONCE_REWRITE_TAC[REAL_NOT_LE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT1_POW2) THEN
  REWRITE_TAC[REAL_POW2_ABS] THEN
  DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[GSYM REAL_SUB_LT]) THEN
  DISCH_THEN(MP_TAC o CONJ(SPEC (--`sin(x)`--) REAL_LE_SQUARE)) THEN
  REWRITE_TAC[GSYM POW_2] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LET_ADD) THEN
  REWRITE_TAC[real_sub, REAL_ADD_ASSOC, SIN_CIRCLE,
    REAL_ADD_ASSOC, SIN_CIRCLE, REAL_ADD_RINV, REAL_LT_REFL]);

val COS_BOUNDS = store_thm("COS_BOUNDS",
  (--`!x. ~(&1) <= cos(x) /\ cos(x) <= &1`--),
  GEN_TAC THEN REWRITE_TAC[GSYM ABS_BOUNDS, COS_BOUND]);

val SIN_COS_ADD = store_thm("SIN_COS_ADD",
  (--`!x y. ((sin(x + y) - ((sin(x) * cos(y)) + (cos(x) * sin(y)))) pow 2) +
         ((cos(x + y) - ((cos(x) * cos(y)) - (sin(x) * sin(y)))) pow 2) = &0`--),
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(X_BETA_CONV (--`x:real`--))) THEN
  W(C SUBGOAL_THEN (SUBST1_TAC o SYM) o subst[((--`&0`--),(--`x:real`--))] o snd) THENL
   [BETA_TAC THEN REWRITE_TAC[SIN_0, COS_0] THEN
    REWRITE_TAC[REAL_ADD_LID, REAL_MUL_LZERO, REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_SUB_RZERO, REAL_SUB_REFL] THEN
    REWRITE_TAC[TWO, POW_0, REAL_ADD_LID],
    MATCH_MP_TAC DIFF_ISCONST_ALL THEN GEN_TAC THEN
    W(MP_TAC o DIFF_CONV o rand o funpow 2 rator o snd) THEN
    REDUCE_TAC THEN REWRITE_TAC[POW_1] THEN
    REWRITE_TAC[REAL_MUL_LZERO, REAL_ADD_RID, REAL_MUL_RID] THEN
    DISCH_THEN(MP_TAC o SPEC (--`x:real`--)) THEN
    MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_NEG_LMUL] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EQ_SUB_LADD] THEN
    REWRITE_TAC[REAL_SUB_LZERO, GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_NEG_RMUL] THEN AP_TERM_TAC THEN
    GEN_REWR_TAC RAND_CONV  [REAL_MUL_SYM] THEN BINOP_TAC THENL
     [REWRITE_TAC[real_sub, REAL_NEG_ADD, REAL_NEGNEG, REAL_NEG_RMUL],
      REWRITE_TAC[GSYM REAL_NEG_RMUL, GSYM real_sub]]]);

val SIN_COS_NEG = store_thm("SIN_COS_NEG",
  (--`!x. ((sin(~x) + (sin x)) pow 2) +
       ((cos(~x) - (cos x)) pow 2) = &0`--),
  GEN_TAC THEN CONV_TAC(LAND_CONV(X_BETA_CONV (--`x:real`--))) THEN
  W(C SUBGOAL_THEN (SUBST1_TAC o SYM) o subst[((--`&0`--),(--`x:real`--))] o snd) THENL
   [BETA_TAC THEN REWRITE_TAC[SIN_0, COS_0, REAL_NEG_0] THEN
    REWRITE_TAC[REAL_ADD_LID, REAL_SUB_REFL] THEN
    REWRITE_TAC[TWO, POW_0, REAL_ADD_LID],
    MATCH_MP_TAC DIFF_ISCONST_ALL THEN GEN_TAC THEN
    W(MP_TAC o DIFF_CONV o rand o funpow 2 rator o snd) THEN
    REDUCE_TAC THEN REWRITE_TAC[POW_1] THEN
    DISCH_THEN(MP_TAC o SPEC (--`x:real`--)) THEN
    MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC[REAL_MUL_RID, real_sub, REAL_NEGNEG, GSYM REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EQ_SUB_LADD] THEN
    REWRITE_TAC[REAL_SUB_LZERO, REAL_NEG_RMUL] THEN AP_TERM_TAC THEN
    GEN_REWR_TAC RAND_CONV  [REAL_MUL_SYM] THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL, REAL_NEG_RMUL] THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_NEG_ADD, REAL_NEGNEG]]);

val SIN_ADD = store_thm("SIN_ADD",
  (--`!x y. sin(x + y) = (sin(x) * cos(y)) + (cos(x) * sin(y))`--),
  REPEAT GEN_TAC THEN MP_TAC(SPECL [(--`x:real`--), (--`y:real`--)] SIN_COS_ADD) THEN
  REWRITE_TAC[POW_2, REAL_SUMSQ] THEN REWRITE_TAC[REAL_SUB_0] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]));

val COS_ADD = store_thm("COS_ADD",
  (--`!x y. cos(x + y) = (cos(x) * cos(y)) - (sin(x) * sin(y))`--),
  REPEAT GEN_TAC THEN MP_TAC(SPECL [(--`x:real`--), (--`y:real`--)] SIN_COS_ADD) THEN
  REWRITE_TAC[POW_2, REAL_SUMSQ] THEN REWRITE_TAC[REAL_SUB_0] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]));

val SIN_NEG = store_thm("SIN_NEG",
  (--`!x. sin(~x) = ~(sin(x))`--),
  GEN_TAC THEN MP_TAC(SPEC (--`x:real`--) SIN_COS_NEG) THEN
  REWRITE_TAC[POW_2, REAL_SUMSQ] THEN REWRITE_TAC[REAL_LNEG_UNIQ] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]));

val COS_NEG = store_thm("COS_NEG",
  (--`!x. cos(~x) = cos(x)`--),
  GEN_TAC THEN MP_TAC(SPEC (--`x:real`--) SIN_COS_NEG) THEN
  REWRITE_TAC[POW_2, REAL_SUMSQ] THEN REWRITE_TAC[REAL_SUB_0] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]));

val SIN_DOUBLE = store_thm("SIN_DOUBLE",
  (--`!x. sin(&2 * x) = &2 * (sin(x) * cos(x))`--),
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_DOUBLE, SIN_ADD] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_MUL_SYM);

val COS_DOUBLE = store_thm("COS_DOUBLE",
  (--`!x. cos(&2 * x) = (cos(x) pow 2) - (sin(x) pow 2)`--),
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_DOUBLE, COS_ADD, POW_2]);

(*---------------------------------------------------------------------------*)
(* Show that there's a least positive x with cos(x) = 0; hence define pi     *)
(*---------------------------------------------------------------------------*)

val SIN_PAIRED = store_thm("SIN_PAIRED",
  (--`!x. (\n. (((~(&1)) pow n) / &(FACT((2 * n) + 1)))
         * (x pow ((2 * n) + 1))) sums (sin x)`--),
  GEN_TAC THEN MP_TAC(SPEC (--`x:real`--) SIN_CONVERGES) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_PAIR) THEN REWRITE_TAC[GSYM sin] THEN
  BETA_TAC THEN REWRITE_TAC[SUM_2] THEN BETA_TAC THEN
  REWRITE_TAC[GSYM ADD1, EVEN_DOUBLE, REWRITE_RULE[ODD_EVEN] ODD_DOUBLE] THEN
  REWRITE_TAC[REAL_MUL_LZERO, REAL_ADD_LID, SUC_SUB1, MULT_DIV_2]);

val SIN_POS = store_thm("SIN_POS",
  (--`!x. &0 < x /\ x < &2 ==> &0 < sin(x)`--),
  GEN_TAC THEN STRIP_TAC THEN MP_TAC(SPEC (--`x:real`--) SIN_PAIRED) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_PAIR) THEN
  REWRITE_TAC[SYM(MATCH_MP SUM_UNIQ (SPEC (--`x:real`--) SIN_PAIRED))] THEN
  REWRITE_TAC[SUM_2] THEN BETA_TAC THEN REWRITE_TAC[GSYM ADD1] THEN
  REWRITE_TAC[pow, GSYM REAL_NEG_MINUS1, POW_MINUS1] THEN
  REWRITE_TAC[real_div, GSYM REAL_NEG_LMUL, GSYM real_sub] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN REWRITE_TAC[ADD1] THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP SUM_UNIQ) THEN
  W(C SUBGOAL_THEN SUBST1_TAC o curry mk_eq (--`&0`--) o curry mk_comb (--`sum(0,0)`--) o
  funpow 2 rand o snd) THENL [REWRITE_TAC[sum], ALL_TAC] THEN
  MATCH_MP_TAC SER_POS_LT THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP SUM_SUMMABLE th]) THEN
  X_GEN_TAC (--`n:num`--) THEN DISCH_THEN(K ALL_TAC) THEN BETA_TAC THEN
  REWRITE_TAC[GSYM ADD1, MULT_CLAUSES] THEN
  REWRITE_TAC[TWO, ADD_CLAUSES, pow, FACT, GSYM REAL_MUL] THEN
  REWRITE_TAC[SYM(TWO)] THEN
  REWRITE_TAC[ONE, ADD_CLAUSES, pow, FACT, GSYM REAL_MUL] THEN
  REWRITE_TAC[REAL_SUB_LT] THEN ONCE_REWRITE_TAC[GSYM pow] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LT_RMUL_IMP THEN CONJ_TAC THENL
   [ALL_TAC, MATCH_MP_TAC POW_POS_LT THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC, GSYM POW_2] THEN
  SUBGOAL_THEN (--`!n. &0 < &(SUC n)`--) ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_LT, LESS_0], ALL_TAC] THEN
  SUBGOAL_THEN (--`!n. &0 < &(FACT n)`--) ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_LT, FACT_LESS], ALL_TAC] THEN
  SUBGOAL_THEN (--`!n. ~(&(SUC n) = &0)`--) ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_INJ, NOT_SUC], ALL_TAC] THEN
  SUBGOAL_THEN (--`!n. ~(&(FACT n) = &0)`--) ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_POS_NZ THEN
    REWRITE_TAC[REAL_LT, FACT_LESS], ALL_TAC] THEN
  REPEAT(IMP_SUBST_TAC REAL_INV_MUL THEN ASM_REWRITE_TAC[REAL_ENTIRE]) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    (--`a * (b * (c * (d * e))) =
        (a * (b * e)) * (c * d)`--)] THEN
  GEN_REWR_TAC RAND_CONV  [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LT_RMUL_IMP THEN CONJ_TAC THENL
   [ALL_TAC, MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_INV_POS THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  IMP_SUBST_TAC ((CONV_RULE(RAND_CONV SYM_CONV) o SPEC_ALL) REAL_INV_MUL) THEN
  ASM_REWRITE_TAC[REAL_ENTIRE] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_LT_1 THEN
  REWRITE_TAC[POW_2] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC,
    MATCH_MP_TAC REAL_LT_MUL2 THEN REPEAT CONJ_TAC] THEN
  TRY(MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[] THEN NO_TAC) THENL
   [W(curry op THEN (MATCH_MP_TAC REAL_LT_TRANS) o EXISTS_TAC o
      curry mk_comb (--`(&)`--) o funpow 3 rand o snd) THEN
    REWRITE_TAC[REAL_LT, LESS_SUC_REFL], ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`&2`--) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(REDEPTH_CONV num_CONV) THEN
  REWRITE_TAC[REAL_LE, LESS_EQ_MONO, ZERO_LESS_EQ]);

val COS_PAIRED = store_thm("COS_PAIRED",
  (--`!x. (\n. (((~(&1)) pow n) / &(FACT(2 * n)))
         * (x pow (2 * n))) sums (cos x)`--),
  GEN_TAC THEN MP_TAC(SPEC (--`x:real`--) COS_CONVERGES) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_PAIR) THEN REWRITE_TAC[GSYM cos] THEN
  BETA_TAC THEN REWRITE_TAC[SUM_2] THEN BETA_TAC THEN
  REWRITE_TAC[GSYM ADD1, EVEN_DOUBLE, REWRITE_RULE[ODD_EVEN] ODD_DOUBLE] THEN
  REWRITE_TAC[REAL_MUL_LZERO, REAL_ADD_RID, MULT_DIV_2]);

val COS_2 = store_thm("COS_2",
  (--`cos(&2) < &0`--),
  GEN_REWR_TAC LAND_CONV  [GSYM REAL_NEGNEG] THEN
  REWRITE_TAC[REAL_NEG_LT0] THEN MP_TAC(SPEC (--`&2`--) COS_PAIRED) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_NEG) THEN BETA_TAC THEN
  DISCH_TAC THEN FIRST_ASSUM(SUBST1_TAC o MATCH_MP SUM_UNIQ) THEN
  MATCH_MP_TAC REAL_LT_TRANS THEN
  EXISTS_TAC (--`sum(0,3) (\n. ~((((~(&1)) pow n) / &(FACT(2 * n)))
                * (&2 pow (2 * n))))`--) THEN CONJ_TAC THENL
   [REWRITE_TAC[num_CONV (--`3:num`--), sum, SUM_2] THEN BETA_TAC THEN
    REWRITE_TAC[MULT_CLAUSES, ADD_CLAUSES, pow, FACT] THEN
    REWRITE_TAC[REAL_MUL_RID, POW_1, POW_2, GSYM REAL_NEG_RMUL] THEN
    IMP_SUBST_TAC REAL_DIV_REFL THEN REWRITE_TAC[REAL_NEGNEG, REAL_10] THEN
    REDUCE_TAC THEN
    REWRITE_TAC[num_CONV (--`4:num`--), num_CONV (--`3:num`--), FACT, pow] THEN
    REWRITE_TAC[SYM(num_CONV (--`4:num`--)), SYM(num_CONV (--`3:num`--))] THEN
    REWRITE_TAC[TWO, ONE, FACT, pow] THEN
    REWRITE_TAC[SYM(ONE), SYM(TWO)] THEN
    REWRITE_TAC[REAL_MUL] THEN REDUCE_TAC THEN
    REWRITE_TAC[real_div, REAL_NEG_LMUL, REAL_NEGNEG, REAL_MUL_LID] THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL, REAL_ADD_ASSOC] THEN
    REWRITE_TAC[GSYM real_sub, REAL_SUB_LT] THEN
    SUBGOAL_THEN (--`inv(&2) * &4 = &1 + &1`--) SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_EQ_LMUL_IMP THEN EXISTS_TAC (--`&2`--) THEN
      REWRITE_TAC[REAL_INJ] THEN REDUCE_TAC THEN
      REWRITE_TAC[REAL_ADD, REAL_MUL] THEN REDUCE_TAC THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN
      SUBGOAL_THEN (--`&2 * inv(&2) = &1`--) SUBST1_TAC THEN
      REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC REAL_MUL_RINV THEN
      REWRITE_TAC[REAL_INJ] THEN REDUCE_TAC,
      REWRITE_TAC[REAL_MUL_LID, REAL_ADD_ASSOC] THEN
      REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
      MATCH_MP_TAC REAL_LT_1 THEN REWRITE_TAC[REAL_LE, REAL_LT] THEN
      REDUCE_TAC], ALL_TAC] THEN
  MATCH_MP_TAC SER_POS_LT_PAIR THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP SUM_SUMMABLE th]) THEN
  X_GEN_TAC (--`d:num`--) THEN BETA_TAC THEN
  REWRITE_TAC[POW_ADD, POW_MINUS1, REAL_MUL_RID] THEN
  REWRITE_TAC[num_CONV (--`3:num`--), pow] THEN REWRITE_TAC[SYM(num_CONV (--`3:num`--))] THEN
  REWRITE_TAC[POW_2, POW_1] THEN
  REWRITE_TAC[GSYM REAL_NEG_MINUS1, REAL_NEGNEG] THEN
  REWRITE_TAC[real_div, GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL] THEN
  REWRITE_TAC[REAL_MUL_LID, REAL_NEGNEG] THEN
  REWRITE_TAC[GSYM real_sub, REAL_SUB_LT] THEN
  REWRITE_TAC[GSYM ADD1, ADD_CLAUSES, MULT_CLAUSES] THEN
  REWRITE_TAC[POW_ADD, REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LT_RMUL_IMP THEN CONJ_TAC THENL
   [ALL_TAC,
    REWRITE_TAC[TWO, MULT_CLAUSES] THEN
    REWRITE_TAC[num_CONV (--`3:num`--), ADD_CLAUSES] THEN
    MATCH_MP_TAC POW_POS_LT THEN REWRITE_TAC[REAL_LT] THEN
    REDUCE_TAC] THEN
  REWRITE_TAC[TWO, ADD_CLAUSES, FACT] THEN
  REWRITE_TAC[SYM(TWO)] THEN
  REWRITE_TAC[ONE, ADD_CLAUSES, FACT] THEN
  REWRITE_TAC[SYM(ONE)] THEN
  SUBGOAL_THEN (--`!n. &0 < &(SUC n)`--) ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_LT, LESS_0], ALL_TAC] THEN
  SUBGOAL_THEN (--`!n. &0 < &(FACT n)`--) ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_LT, FACT_LESS], ALL_TAC] THEN
  SUBGOAL_THEN (--`!n. ~(&(SUC n) = &0)`--) ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_INJ, NOT_SUC], ALL_TAC] THEN
  SUBGOAL_THEN (--`!n. ~(&(FACT n) = &0)`--) ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_POS_NZ THEN
    REWRITE_TAC[REAL_LT, FACT_LESS], ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL] THEN
  REPEAT(IMP_SUBST_TAC REAL_INV_MUL THEN ASM_REWRITE_TAC[REAL_ENTIRE]) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    (--`a * (b * (c * d)) = (a * (b * d)) * c`--)] THEN
  GEN_REWR_TAC RAND_CONV  [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LT_RMUL_IMP THEN CONJ_TAC THENL
   [ALL_TAC,
    MATCH_MP_TAC REAL_INV_POS THEN REWRITE_TAC[REAL_LT, FACT_LESS]] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  IMP_SUBST_TAC ((CONV_RULE(RAND_CONV SYM_CONV) o SPEC_ALL) REAL_INV_MUL) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_LT_1 THEN
  REWRITE_TAC[POW_2, REAL_MUL, REAL_LE, REAL_LT] THEN REDUCE_TAC THEN
  REWRITE_TAC[num_CONV (--`4:num`--), num_CONV (--`3:num`--),
              MULT_CLAUSES, ADD_CLAUSES] THEN
  REWRITE_TAC[LESS_MONO_EQ] THEN
  REWRITE_TAC[TWO, ADD_CLAUSES, MULT_CLAUSES] THEN
  REWRITE_TAC[ONE, LESS_MONO_EQ, LESS_0]);

val COS_ISZERO = store_thm("COS_ISZERO",
  (--`?!x. &0 <= x /\ x <= &2 /\ (cos x = &0)`--),
  REWRITE_TAC[EXISTS_UNIQUE_DEF] THEN BETA_TAC THEN
  W(C SUBGOAL_THEN ASSUME_TAC o hd o strip_conj o snd) THENL
   [MATCH_MP_TAC IVT2 THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE, ZERO_LESS_EQ],
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ACCEPT_TAC COS_2,
      REWRITE_TAC[COS_0, REAL_LE_01],
      X_GEN_TAC (--`x:real`--) THEN DISCH_THEN(K ALL_TAC) THEN
      MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC (--`~(sin x)`--) THEN
      REWRITE_TAC[DIFF_COS]],
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN
    MAP_EVERY X_GEN_TAC [(--`x1:real`--), (--`x2:real`--)] THEN
    GEN_REWR_TAC I  [TAUT_CONV (--`a:bool = ~~a`--)] THEN
    PURE_REWRITE_TAC[NOT_IMP] THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [(--`x1:real`--), (--`x2:real`--)] REAL_LT_TOTAL) THEN
    SUBGOAL_THEN (--`(!x. cos differentiable x) /\ (!x. cos contl x)`--)
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN GEN_TAC THENL
       [REWRITE_TAC[differentiable], MATCH_MP_TAC DIFF_CONT] THEN
      EXISTS_TAC (--`~(sin x)`--) THEN REWRITE_TAC[DIFF_COS], ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN DISJ_CASES_TAC THENL
     [MP_TAC(SPECL [(--`cos`--), (--`x1:real`--), (--`x2:real`--)] ROLLE),
      MP_TAC(SPECL [(--`cos`--), (--`x2:real`--), (--`x1:real`--)] ROLLE)] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`x:real`--) MP_TAC) THEN REWRITE_TAC[CONJ_ASSOC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o CONJ(SPEC (--`x:real`--) DIFF_COS)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_UNIQ) THEN
    REWRITE_TAC[REAL_NEG_EQ0] THEN MATCH_MP_TAC REAL_POS_NZ THEN
    MATCH_MP_TAC SIN_POS THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`x1:real`--) THEN
        ASM_REWRITE_TAC[],
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`x2:real`--) THEN
        ASM_REWRITE_TAC[]],
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`x2:real`--) THEN
        ASM_REWRITE_TAC[],
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`x1:real`--) THEN
        ASM_REWRITE_TAC[]]]]);

val pi = new_definition("pi",
  Term `pi = &2 * @x. &0 <= x /\ x <= &2 /\ (cos x = &0)`);

(*---------------------------------------------------------------------------*)
(* Periodicity and related properties of the trig functions                  *)
(*---------------------------------------------------------------------------*)

val PI2 = store_thm("PI2",
  (--`pi / &2 = @x. &0 <= x /\ x <= &2 /\ (cos(x) = &0)`--),
  REWRITE_TAC[pi, real_div] THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    (--`(a * b) * c = (c * a) * b`--)] THEN
  IMP_SUBST_TAC REAL_MUL_LINV THEN REWRITE_TAC[REAL_INJ] THEN
  REDUCE_TAC THEN REWRITE_TAC[REAL_MUL_LID]);

val COS_PI2 = store_thm("COS_PI2",
  (--`cos(pi / &2) = &0`--),
  MP_TAC(SELECT_RULE (EXISTENCE COS_ISZERO)) THEN
  REWRITE_TAC[GSYM PI2] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]));

val PI2_BOUNDS = store_thm("PI2_BOUNDS",
  (--`&0 < (pi / &2) /\ (pi / &2) < &2`--),
  MP_TAC(SELECT_RULE (EXISTENCE COS_ISZERO)) THEN
  REWRITE_TAC[GSYM PI2] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL
   [DISCH_TAC THEN MP_TAC COS_0 THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM REAL_10],
    DISCH_TAC THEN MP_TAC COS_PI2 THEN FIRST_ASSUM SUBST1_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
    MATCH_ACCEPT_TAC COS_2]);

val PI_POS = store_thm("PI_POS",
  (--`&0 < pi`--),
  GEN_REWR_TAC RAND_CONV  [GSYM REAL_HALF_DOUBLE] THEN
  MATCH_MP_TAC REAL_LT_ADD THEN REWRITE_TAC[PI2_BOUNDS]);

val SIN_PI2 = store_thm("SIN_PI2",
  (--`sin(pi / &2) = &1`--),
  MP_TAC(SPEC (--`pi / &2`--) SIN_CIRCLE) THEN
  REWRITE_TAC[COS_PI2, POW_2, REAL_MUL_LZERO, REAL_ADD_RID] THEN
  GEN_REWR_TAC (LAND_CONV o RAND_CONV)  [GSYM REAL_MUL_LID] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  REWRITE_TAC[GSYM REAL_DIFFSQ, REAL_ENTIRE] THEN
  DISCH_THEN DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[REAL_LNEG_UNIQ] THEN DISCH_THEN(MP_TAC o AP_TERM (--`$~`--)) THEN
  REWRITE_TAC[REAL_NEGNEG] THEN DISCH_TAC THEN
  MP_TAC REAL_LT_01 THEN POP_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_GT THEN
  REWRITE_TAC[REAL_NEG_LT0] THEN MATCH_MP_TAC SIN_POS THEN
  REWRITE_TAC[PI2_BOUNDS]);

val COS_PI = store_thm("COS_PI",
  (--`cos(pi) = ~(&1)`--),
  MP_TAC(SPECL [(--`pi / &2`--), (--`pi / &2`--)] COS_ADD) THEN
  REWRITE_TAC[SIN_PI2, COS_PI2, REAL_MUL_LZERO, REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_SUB_LZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN REWRITE_TAC[REAL_DOUBLE] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
  REWRITE_TAC[REAL_INJ] THEN REDUCE_TAC);

val SIN_PI = store_thm("SIN_PI",
  (--`sin(pi) = &0`--),
  MP_TAC(SPECL [(--`pi / &2`--), (--`pi / &2`--)] SIN_ADD) THEN
  REWRITE_TAC[COS_PI2, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_ADD_LID] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_DOUBLE] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC REAL_DIV_LMUL THEN
  REWRITE_TAC[REAL_INJ] THEN REDUCE_TAC);

val SIN_COS = store_thm("SIN_COS",
  (--`!x. sin(x) = cos((pi / &2) - x)`--),
  GEN_TAC THEN REWRITE_TAC[real_sub, COS_ADD] THEN
  REWRITE_TAC[SIN_PI2, COS_PI2, REAL_MUL_LZERO] THEN
  REWRITE_TAC[REAL_ADD_LID, REAL_MUL_LID] THEN
  REWRITE_TAC[SIN_NEG, REAL_NEGNEG]);

val COS_SIN = store_thm("COS_SIN",
  (--`!x. cos(x) = sin((pi / &2) - x)`--),
  GEN_TAC THEN REWRITE_TAC[real_sub, SIN_ADD] THEN
  REWRITE_TAC[SIN_PI2, COS_PI2, REAL_MUL_LZERO] THEN
  REWRITE_TAC[REAL_MUL_LID, REAL_ADD_RID] THEN
  REWRITE_TAC[COS_NEG]);

val SIN_PERIODIC_PI = store_thm("SIN_PERIODIC_PI",
  (--`!x. sin(x + pi) = ~(sin(x))`--),
  GEN_TAC THEN REWRITE_TAC[SIN_ADD, SIN_PI, COS_PI] THEN
  REWRITE_TAC[REAL_MUL_RZERO, REAL_ADD_RID, GSYM REAL_NEG_RMUL] THEN
  REWRITE_TAC[REAL_MUL_RID]);

val COS_PERIODIC_PI = store_thm("COS_PERIODIC_PI",
  (--`!x. cos(x + pi) = ~(cos(x))`--),
  GEN_TAC THEN REWRITE_TAC[COS_ADD, SIN_PI, COS_PI] THEN
  REWRITE_TAC[REAL_MUL_RZERO, REAL_SUB_RZERO, GSYM REAL_NEG_RMUL] THEN
  REWRITE_TAC[REAL_MUL_RID]);

val SIN_PERIODIC = store_thm("SIN_PERIODIC",
  (--`!x. sin(x + (&2 * pi)) = sin(x)`--),
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_DOUBLE, REAL_ADD_ASSOC] THEN
  REWRITE_TAC[SIN_PERIODIC_PI, REAL_NEGNEG]);

val COS_PERIODIC = store_thm("COS_PERIODIC",
  (--`!x. cos(x + (&2 * pi)) = cos(x)`--),
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_DOUBLE, REAL_ADD_ASSOC] THEN
  REWRITE_TAC[COS_PERIODIC_PI, REAL_NEGNEG]);

val COS_NPI = store_thm("COS_NPI",
  (--`!n. cos(&n * pi) = ~(&1) pow n`--),
  INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO, COS_0, pow] THEN
  REWRITE_TAC[ADD1, GSYM REAL_ADD, REAL_RDISTRIB, COS_ADD] THEN
  REWRITE_TAC[REAL_MUL_LID, SIN_PI, REAL_MUL_RZERO, REAL_SUB_RZERO] THEN
  ASM_REWRITE_TAC[COS_PI] THEN
  MATCH_ACCEPT_TAC REAL_MUL_SYM);

val SIN_NPI = store_thm("SIN_NPI",
  (--`!n. sin(&n * pi) = &0`--),
  INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO, SIN_0, pow] THEN
  REWRITE_TAC[ADD1, GSYM REAL_ADD, REAL_RDISTRIB, SIN_ADD] THEN
  REWRITE_TAC[REAL_MUL_LID, SIN_PI, REAL_MUL_RZERO, REAL_ADD_RID] THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO]);

val SIN_POS_PI2 = store_thm("SIN_POS_PI2",
  (--`!x. &0 < x /\ x < pi / &2 ==> &0 < sin(x)`--),
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SIN_POS THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_TRANS THEN
  EXISTS_TAC (--`pi / &2`--) THEN ASM_REWRITE_TAC[PI2_BOUNDS]);

val COS_POS_PI2 = store_thm("COS_POS_PI2",
  (--`!x. &0 < x /\ x < pi / &2 ==> &0 < cos(x)`--),
  GEN_TAC THEN STRIP_TAC THEN
  GEN_REWR_TAC I  [TAUT_CONV (--`a:bool = ~~a`--)] THEN
  PURE_REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [(--`cos`--), (--`&0`--), (--`x:real`--), (--`&0`--)] IVT2) THEN
  ASM_REWRITE_TAC[COS_0, REAL_LE_01, NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
    X_GEN_TAC (--`z:real`--) THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC (--`~(sin z)`--) THEN
    REWRITE_TAC[DIFF_COS],
    DISCH_THEN(X_CHOOSE_TAC (--`z:real`--)) THEN
    MP_TAC(CONJUNCT2 (CONV_RULE EXISTS_UNIQUE_CONV COS_ISZERO)) THEN
    DISCH_THEN(MP_TAC o SPECL [(--`z:real`--), (--`pi / &2`--)]) THEN
    ASM_REWRITE_TAC[COS_PI2] THEN REWRITE_TAC[NOT_IMP] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`x:real`--) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (--`pi / &2`--) THEN ASM_REWRITE_TAC[] THEN CONJ_TAC,
      ALL_TAC,
      ALL_TAC,
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (--`x < pi / &2`--) THEN
      ASM_REWRITE_TAC[REAL_NOT_LT]] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[PI2_BOUNDS]]);

val COS_POS_PI = store_thm("COS_POS_PI",
  (--`!x. ~(pi / &2) < x /\ x < pi / &2 ==> &0 < cos(x)`--),
  GEN_TAC THEN STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
        (SPECL [(--`x:real`--), (--`&0`--)] REAL_LT_TOTAL) THENL
   [ASM_REWRITE_TAC[COS_0, REAL_LT_01],
    ONCE_REWRITE_TAC[GSYM COS_NEG] THEN MATCH_MP_TAC COS_POS_PI2 THEN
    ONCE_REWRITE_TAC[GSYM REAL_NEG_LT0] THEN ASM_REWRITE_TAC[REAL_NEGNEG] THEN
    ONCE_REWRITE_TAC[GSYM REAL_LT_NEG] THEN ASM_REWRITE_TAC[REAL_NEGNEG],
    MATCH_MP_TAC COS_POS_PI2 THEN ASM_REWRITE_TAC[]]);

val SIN_POS_PI = store_thm("SIN_POS_PI",
  (--`!x. &0 < x /\ x < pi ==> &0 < sin(x)`--),
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SIN_COS] THEN ONCE_REWRITE_TAC[GSYM COS_NEG] THEN
  REWRITE_TAC[REAL_NEG_SUB] THEN
  MATCH_MP_TAC COS_POS_PI THEN
  REWRITE_TAC[REAL_LT_SUB_LADD, REAL_LT_SUB_RADD] THEN
  ASM_REWRITE_TAC[REAL_HALF_DOUBLE, REAL_ADD_LINV]);

val COS_POS_PI2_LE = store_thm("COS_POS_PI2_LE",
  (--`!x. &0 <= x /\ x <= (pi / &2) ==> &0 <= cos(x)`--),
  GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN DISJ_CASES_TAC) THEN
  ASM_REWRITE_TAC[COS_PI2] THEN
  TRY(DISJ1_TAC THEN MATCH_MP_TAC COS_POS_PI2 THEN
      ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  SUBST1_TAC(SYM(ASSUME (--`&0 = x`--))) THEN
  REWRITE_TAC[COS_0, REAL_LT_01]);

val COS_POS_PI_LE = store_thm("COS_POS_PI_LE",
  (--`!x. ~(pi / &2) <= x /\ x <= (pi / &2) ==> &0 <= cos(x)`--),
  GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN DISJ_CASES_TAC) THEN
  ASM_REWRITE_TAC[COS_PI2] THENL
   [DISJ1_TAC THEN MATCH_MP_TAC COS_POS_PI THEN ASM_REWRITE_TAC[],
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[COS_NEG, COS_PI2, REAL_LT_01]]);

val SIN_POS_PI2_LE = store_thm("SIN_POS_PI2_LE",
  (--`!x. &0 <= x /\ x <= (pi / &2) ==> &0 <= sin(x)`--),
  GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN DISJ_CASES_TAC) THEN
  ASM_REWRITE_TAC[SIN_PI2, REAL_LT_01] THENL
   [DISJ1_TAC THEN MATCH_MP_TAC SIN_POS_PI2 THEN ASM_REWRITE_TAC[],
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[SIN_0],
    MP_TAC PI2_BOUNDS THEN ASM_REWRITE_TAC[REAL_LT_REFL]]);

val SIN_POS_PI_LE = store_thm("SIN_POS_PI_LE",
  (--`!x. &0 <= x /\ x <= pi ==> &0 <= sin(x)`--),
  GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN DISJ_CASES_TAC) THEN
  ASM_REWRITE_TAC[SIN_PI] THENL
   [DISJ1_TAC THEN MATCH_MP_TAC SIN_POS_PI THEN ASM_REWRITE_TAC[],
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[SIN_0]]);


val COS_TOTAL = store_thm("COS_TOTAL",
  (--`!y. ~(&1) <= y /\ y <= &1 ==> ?!x. &0 <= x /\ x <= pi /\ (cos(x) = y)`--),
  GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC EXISTS_UNIQUE_CONV THEN CONJ_TAC THENL
   [MATCH_MP_TAC IVT2 THEN ASM_REWRITE_TAC[COS_0, COS_PI] THEN
    REWRITE_TAC[MATCH_MP REAL_LT_IMP_LE PI_POS] THEN
    GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC (--`~(sin x)`--) THEN
    REWRITE_TAC[DIFF_COS],
    MAP_EVERY X_GEN_TAC [(--`x1:real`--), (--`x2:real`--)] THEN STRIP_TAC THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
         (SPECL [(--`x1:real`--), (--`x2:real`--)] REAL_LT_TOTAL) THENL
     [FIRST_ASSUM ACCEPT_TAC,
      MP_TAC(SPECL [(--`cos`--), (--`x1:real`--), (--`x2:real`--)] ROLLE),
      MP_TAC(SPECL [(--`cos`--), (--`x2:real`--), (--`x1:real`--)] ROLLE)]] THEN
  ASM_REWRITE_TAC[] THEN
  (W(C SUBGOAL_THEN (fn t => REWRITE_TAC[t]) o funpow 2
                    (fst o dest_imp) o snd) THENL
    [CONJ_TAC THEN X_GEN_TAC (--`x:real`--) THEN DISCH_THEN(K ALL_TAC) THEN
     TRY(MATCH_MP_TAC DIFF_CONT) THEN REWRITE_TAC[differentiable] THEN
     EXISTS_TAC (--`~(sin x)`--) THEN REWRITE_TAC[DIFF_COS], ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`x:real`--) STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC (--`(cos diffl &0)(x)`--) THEN
  DISCH_THEN(MP_TAC o CONJ (SPEC (--`x:real`--) DIFF_COS)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_UNIQ) THEN
  REWRITE_TAC[REAL_NEG_EQ0] THEN DISCH_TAC THEN
  MP_TAC(SPEC (--`x:real`--) SIN_POS_PI) THEN
  ASM_REWRITE_TAC[REAL_LT_REFL] THEN
  CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`x1:real`--),
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`x2:real`--),
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`x2:real`--),
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`x1:real`--)] THEN
  ASM_REWRITE_TAC[]);

val SIN_TOTAL = store_thm("SIN_TOTAL",
  (--`!y. ~(&1) <= y /\ y <= &1 ==>
        ?!x.  ~(pi / &2) <= x /\ x <= pi / &2 /\ (sin(x) = y)`--),
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN (--`!x. ~(pi / &2) <= x /\ x <= pi / &2 /\ (sin(x) = y)
                           =
                       &0 <= (x + pi / &2) /\
                       (x + pi / &2) <= pi  /\
                       (cos(x + pi / &2) = ~y)`--)
  (fn th => REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[COS_ADD, SIN_PI2, COS_PI2] THEN
    REWRITE_TAC[REAL_MUL_RZERO, REAL_MUL_RZERO, REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_SUB_LZERO] THEN
    REWRITE_TAC[GSYM REAL_LE_SUB_RADD, GSYM REAL_LE_SUB_LADD] THEN
    REWRITE_TAC[REAL_SUB_LZERO] THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_EQ_NEG] THEN AP_THM_TAC THEN
    REPEAT AP_TERM_TAC THEN
    GEN_REWR_TAC (RAND_CONV o LAND_CONV)  [GSYM REAL_HALF_DOUBLE] THEN
    REWRITE_TAC[REAL_ADD_SUB], ALL_TAC] THEN
  MP_TAC(SPEC (--`~y`--) COS_TOTAL) THEN ASM_REWRITE_TAC[REAL_LE_NEG] THEN
  ONCE_REWRITE_TAC[GSYM REAL_LE_NEG] THEN ASM_REWRITE_TAC[REAL_NEGNEG] THEN
  REWRITE_TAC[REAL_LE_NEG] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
  DISCH_THEN(curry op THEN CONJ_TAC o MP_TAC) THENL
   [DISCH_THEN(X_CHOOSE_TAC (--`x:real`--) o CONJUNCT1) THEN
    EXISTS_TAC (--`x - pi / &2`--) THEN ASM_REWRITE_TAC[REAL_SUB_ADD],
    POP_ASSUM(K ALL_TAC) THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    REWRITE_TAC[REAL_EQ_RADD]]);

val COS_ZERO_LEMMA = store_thm("COS_ZERO_LEMMA",
  (--`!x. &0 <= x /\ (cos(x) = &0) ==>
      ?n. ~EVEN n /\ (x = &n * (pi / &2))`--),
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC (--`x:real`--) (MATCH_MP REAL_ARCH_LEAST PI_POS)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`n:num`--) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN (--`&0 <= x - &n * pi /\ (x - &n * pi) <= pi /\
                (cos(x - &n * pi) = &0)`--) ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_LE] THEN
    REWRITE_TAC[REAL_LE_SUB_RADD] THEN
    REWRITE_TAC[real_sub, COS_ADD, SIN_NEG, COS_NEG, SIN_NPI, COS_NPI] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO, REAL_ADD_LID] THEN
    REWRITE_TAC[REAL_NEG_RMUL, REAL_NEGNEG, REAL_MUL_RZERO] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN UNDISCH_TAC (--`x < &(SUC n) * pi`--) THEN
    REWRITE_TAC[ADD1] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    REWRITE_TAC[GSYM REAL_ADD, REAL_RDISTRIB, REAL_MUL_LID],
    MP_TAC(SPEC (--`&0`--) COS_TOTAL) THEN
    REWRITE_TAC[REAL_LE_01, REAL_NEG_LE0] THEN
    DISCH_THEN(MP_TAC o CONV_RULE EXISTS_UNIQUE_CONV) THEN
    DISCH_THEN(MP_TAC o SPECL [(--`x - &n * pi`--), (--`pi / &2`--)] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[COS_PI2] THEN
    W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN MP_TAC PI2_BOUNDS THEN
      REWRITE_TAC[REAL_LT_HALF1, REAL_LT_HALF2] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[],
      DISCH_THEN(fn th => REWRITE_TAC[th])] THEN
    REWRITE_TAC[REAL_EQ_SUB_RADD] THEN DISCH_TAC THEN
    EXISTS_TAC (--`SUC(2 * n)`--) THEN REWRITE_TAC[EVEN_ODD, ODD_DOUBLE] THEN
    REWRITE_TAC[ADD1, GSYM REAL_ADD, GSYM REAL_MUL] THEN
    REWRITE_TAC[REAL_RDISTRIB, REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    REWRITE_TAC[REAL_INJ] THEN REDUCE_TAC]);

val SIN_ZERO_LEMMA = store_thm("SIN_ZERO_LEMMA",
  (--`!x. &0 <= x /\ (sin(x) = &0) ==>
        ?n. EVEN n /\ (x = &n * (pi / &2))`--),
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC (--`x + pi / &2`--) COS_ZERO_LEMMA) THEN
  W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`x:real`--) THEN
      ASM_REWRITE_TAC[REAL_LE_ADDR] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      REWRITE_TAC[PI2_BOUNDS],
      ASM_REWRITE_TAC[COS_ADD, COS_PI2, REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
      MATCH_ACCEPT_TAC REAL_SUB_REFL],
    DISCH_THEN(fn th => REWRITE_TAC[th])] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`n:num`--) STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC (--`n:num`--) ODD_EXISTS) THEN ASM_REWRITE_TAC[ODD_EVEN] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`m:num`--) SUBST_ALL_TAC) THEN
  EXISTS_TAC (--`2 * m:num`--) THEN REWRITE_TAC[EVEN_DOUBLE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_EQ_SUB_LADD]) THEN
  FIRST_ASSUM SUBST1_TAC THEN
  REWRITE_TAC[ADD1, GSYM REAL_ADD, REAL_RDISTRIB, REAL_MUL_LID] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[REAL_ADD_SYM] REAL_ADD_SUB]);

val COS_ZERO = store_thm("COS_ZERO",
  (--`!x. (cos(x) = &0) = (?n. ~EVEN n /\ (x = &n * (pi / &2))) \/
                       (?n. ~EVEN n /\ (x = ~(&n * (pi / &2))))`--),
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN DISJ_CASES_TAC (SPECL [(--`&0`--), (--`x:real`--)] REAL_LE_TOTAL) THENL
     [DISJ1_TAC THEN MATCH_MP_TAC COS_ZERO_LEMMA THEN ASM_REWRITE_TAC[],
      DISJ2_TAC THEN REWRITE_TAC[GSYM REAL_NEG_EQ] THEN
      MATCH_MP_TAC COS_ZERO_LEMMA THEN ASM_REWRITE_TAC[COS_NEG] THEN
      ONCE_REWRITE_TAC[GSYM REAL_LE_NEG] THEN
      ASM_REWRITE_TAC[REAL_NEGNEG, REAL_NEG_0]],
    DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_TAC (--`n:num`--))) THEN
    ASM_REWRITE_TAC[COS_NEG] THEN MP_TAC(SPEC (--`n:num`--) ODD_EXISTS) THEN
    ASM_REWRITE_TAC[ODD_EVEN] THEN DISCH_THEN(X_CHOOSE_THEN (--`m:num`--) SUBST1_TAC) THEN
    REWRITE_TAC[ADD1] THEN SPEC_TAC((--`m:num`--),(--`m:num`--)) THEN INDUCT_TAC THEN
    REWRITE_TAC[MULT_CLAUSES, ADD_CLAUSES, REAL_MUL_LID, COS_PI2] THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN ONCE_REWRITE_TAC[GSYM REAL_ADD] THEN
    REWRITE_TAC[REAL_RDISTRIB] THEN REWRITE_TAC[COS_ADD] THEN
    REWRITE_TAC[GSYM REAL_DOUBLE, REAL_HALF_DOUBLE] THEN
    ASM_REWRITE_TAC[COS_PI, SIN_PI, REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
    REWRITE_TAC[REAL_SUB_RZERO]]);

val SIN_ZERO = store_thm("SIN_ZERO",
  (--`!x. (sin(x) = &0) = (?n. EVEN n /\ (x = &n * (pi / &2))) \/
                       (?n. EVEN n /\ (x = ~(&n * (pi / &2))))`--),
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN DISJ_CASES_TAC (SPECL [(--`&0`--), (--`x:real`--)] REAL_LE_TOTAL) THENL
     [DISJ1_TAC THEN MATCH_MP_TAC SIN_ZERO_LEMMA THEN ASM_REWRITE_TAC[],
      DISJ2_TAC THEN REWRITE_TAC[GSYM REAL_NEG_EQ] THEN
      MATCH_MP_TAC SIN_ZERO_LEMMA THEN
      ASM_REWRITE_TAC[SIN_NEG, REAL_NEG_0, REAL_NEG_GE0]],
    DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_TAC (--`n:num`--))) THEN
    ASM_REWRITE_TAC[SIN_NEG, REAL_NEG_EQ0] THEN
    MP_TAC(SPEC (--`n:num`--) EVEN_EXISTS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`m:num`--) SUBST1_TAC) THEN
    REWRITE_TAC[GSYM REAL_MUL] THEN
    ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
      (--`(a * b) * c = b * (a * c)`--)] THEN
    REWRITE_TAC[GSYM REAL_DOUBLE, REAL_HALF_DOUBLE, SIN_NPI]]);

(*---------------------------------------------------------------------------*)
(* Tangent                                                                   *)
(*---------------------------------------------------------------------------*)

val tan = new_definition("tan",
  (--`tan(x) = sin(x) / cos(x)`--));

val TAN_0 = store_thm("TAN_0",
  (--`tan(&0) = &0`--),
  REWRITE_TAC[tan, SIN_0, REAL_DIV_LZERO]);

val TAN_PI = store_thm("TAN_PI",
  (--`tan(pi) = &0`--),
  REWRITE_TAC[tan, SIN_PI, REAL_DIV_LZERO]);

val TAN_NPI = store_thm("TAN_NPI",
  (--`!n. tan(&n * pi) = &0`--),
  GEN_TAC THEN REWRITE_TAC[tan, SIN_NPI, REAL_DIV_LZERO]);

val TAN_NEG = store_thm("TAN_NEG",
  (--`!x. tan(~x) = ~(tan x)`--),
  GEN_TAC THEN REWRITE_TAC[tan, SIN_NEG, COS_NEG] THEN
  REWRITE_TAC[real_div, REAL_NEG_LMUL]);

val TAN_PERIODIC = store_thm("TAN_PERIODIC",
  (--`!x. tan(x + &2 * pi) = tan(x)`--),
  GEN_TAC THEN REWRITE_TAC[tan, SIN_PERIODIC, COS_PERIODIC]);

val TAN_ADD = store_thm("TAN_ADD",
  (--`!x y. ~(cos(x) = &0) /\ ~(cos(y) = &0) /\ ~(cos(x + y) = &0) ==>
           (tan(x + y) = (tan(x) + tan(y)) / (&1 - tan(x) * tan(y)))`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tan] THEN
  MP_TAC(SPECL [(--`cos(x) * cos(y)`--),
                (--`&1 - (sin(x) / cos(x)) * (sin(y) / cos(y))`--)]
         REAL_DIV_MUL2) THEN ASM_REWRITE_TAC[REAL_ENTIRE] THEN
  W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
   [DISCH_THEN(MP_TAC o AP_TERM (--`$* (cos(x) * cos(y))`--)) THEN
    REWRITE_TAC[real_div, REAL_SUB_LDISTRIB, GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_MUL_RID, REAL_MUL_RZERO] THEN
    UNDISCH_TAC (--`~(cos(x + y) = &0)`--) THEN
    MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[COS_ADD] THEN AP_TERM_TAC,
    DISCH_THEN(fn th => DISCH_THEN(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(fn th => ONCE_REWRITE_TAC[th]) THEN BINOP_TAC THENL
     [REWRITE_TAC[real_div, REAL_LDISTRIB, GSYM REAL_MUL_ASSOC] THEN
      REWRITE_TAC[SIN_ADD] THEN BINOP_TAC THENL
       [ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
          (--`a * (b * (c * d)) = (d * a) * (c * b)`--)] THEN
        IMP_SUBST_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[REAL_MUL_LID],
        ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
          (--`a * (b * (c * d)) = (d * b) * (a * c)`--)] THEN
        IMP_SUBST_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[REAL_MUL_LID]],
      REWRITE_TAC[COS_ADD, REAL_SUB_LDISTRIB, REAL_MUL_RID] THEN
      AP_TERM_TAC THEN REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC]]] THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    (--`a * (b * (c * (d * (e * f)))) =
        (f * b) * ((d * a) * (c * e))`--)] THEN
  REPEAT(IMP_SUBST_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[REAL_MUL_LID]);

val TAN_DOUBLE = store_thm("TAN_DOUBLE",
  (--`!x. ~(cos(x) = &0) /\ ~(cos(&2 * x) = &0) ==>
            (tan(&2 * x) = (&2 * tan(x)) / (&1 - (tan(x) pow 2)))`--),
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [(--`x:real`--), (--`x:real`--)] TAN_ADD) THEN
  ASM_REWRITE_TAC[REAL_DOUBLE, POW_2]);

val TAN_POS_PI2 = store_thm("TAN_POS_PI2",
  (--`!x. &0 < x /\ x < pi / &2 ==> &0 < tan(x)`--),
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[tan, real_div] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SIN_POS_PI2,
    MATCH_MP_TAC REAL_INV_POS THEN MATCH_MP_TAC COS_POS_PI2] THEN
  ASM_REWRITE_TAC[]);

val DIFF_TAN = store_thm("DIFF_TAN",
  (--`!x. ~(cos(x) = &0) ==> (tan diffl inv(cos(x) pow 2))(x)`--),
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(DIFF_CONV (--`\x. sin(x) / cos(x)`--)) THEN
  DISCH_THEN(MP_TAC o SPEC (--`x:real`--)) THEN ASM_REWRITE_TAC[REAL_MUL_RID] THEN
  REWRITE_TAC[GSYM tan, GSYM REAL_NEG_LMUL, REAL_NEGNEG, real_sub] THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[GSYM POW_2, SIN_CIRCLE, GSYM REAL_INV_1OVER]);


val TAN_TOTAL_LEMMA = store_thm("TAN_TOTAL_LEMMA",
  (--`!y. &0 < y ==> ?x. &0 < x /\ x < pi / &2 /\ y < tan(x)`--),
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN (--`((\x. cos(x) / sin(x)) -> &0) (pi / &2)`--)
  MP_TAC THENL
   [SUBST1_TAC(SYM(SPEC (--`&1`--) REAL_DIV_LZERO)) THEN
    CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN MATCH_MP_TAC LIM_DIV THEN
    REWRITE_TAC[REAL_10] THEN CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
    SUBST1_TAC(SYM COS_PI2) THEN SUBST1_TAC(SYM SIN_PI2) THEN
    REWRITE_TAC[GSYM CONTL_LIM] THEN CONJ_TAC THEN MATCH_MP_TAC DIFF_CONT THENL
     [EXISTS_TAC (--`~(sin(pi / &2))`--),
      EXISTS_TAC (--`cos(pi / &2)`--)] THEN
    REWRITE_TAC[DIFF_SIN, DIFF_COS], ALL_TAC] THEN
  REWRITE_TAC[LIM] THEN DISCH_THEN(MP_TAC o SPEC (--`inv(y)`--)) THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_INV_POS th]) THEN
  BETA_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:real`--) STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [(--`d:real`--), (--`pi / &2`--)] REAL_DOWN2) THEN
  ASM_REWRITE_TAC[PI2_BOUNDS] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`e:real`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`(pi / &2) - e`--) THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[real_sub, GSYM REAL_NOT_LE, REAL_LE_ADDR, REAL_NEG_GE0] THEN
    ASM_REWRITE_TAC[REAL_NOT_LE], ALL_TAC] THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
  DISCH_THEN(MP_TAC o SPEC (--`(pi / &2) - e`--)) THEN
  REWRITE_TAC[REAL_SUB_SUB, ABS_NEG] THEN
  SUBGOAL_THEN (--`abs(e) = e`--) (fn th => ASM_REWRITE_TAC[th]) THENL
   [REWRITE_TAC[ABS_REFL] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
  SUBGOAL_THEN (--`&0 < cos((pi / &2) - e) / sin((pi / &2) - e)`--)
  MP_TAC THENL
   [ONCE_REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC COS_POS_PI2,
      MATCH_MP_TAC REAL_INV_POS THEN MATCH_MP_TAC SIN_POS_PI2] THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE, real_sub, REAL_LE_ADDR, REAL_NEG_GE0] THEN
    ASM_REWRITE_TAC[REAL_NOT_LE], ALL_TAC] THEN
  DISCH_THEN(fn th => ASSUME_TAC th THEN MP_TAC(MATCH_MP REAL_POS_NZ th)) THEN
  REWRITE_TAC[ABS_NZ, TAUT_CONV (--`a ==> b ==> c = a /\ b ==> c`--)] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_INV) THEN REWRITE_TAC[tan] THEN
  MATCH_MP_TAC (TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN BINOP_TAC THENL
   [MATCH_MP_TAC REAL_INVINV THEN MATCH_MP_TAC REAL_POS_NZ THEN
    FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
  MP_TAC(ASSUME(--`&0 < cos((pi / &2) - e) / sin((pi / &2) - e)`--)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  REWRITE_TAC[GSYM ABS_REFL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[real_div] THEN IMP_SUBST_TAC REAL_INV_MUL THENL
   [REWRITE_TAC[GSYM DE_MORGAN_THM, GSYM REAL_ENTIRE, GSYM real_div] THEN
    MATCH_MP_TAC REAL_POS_NZ THEN FIRST_ASSUM ACCEPT_TAC,
    GEN_REWR_TAC RAND_CONV  [REAL_MUL_SYM] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC REAL_INVINV THEN MATCH_MP_TAC REAL_POS_NZ THEN
    MATCH_MP_TAC SIN_POS_PI2 THEN REWRITE_TAC[REAL_SUB_LT, GSYM real_div] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE, real_sub, REAL_LE_ADDR, REAL_NEG_GE0] THEN
    ASM_REWRITE_TAC[REAL_NOT_LE]]);

val TAN_TOTAL_POS = store_thm("TAN_TOTAL_POS",
  (--`!y. &0 <= y ==> ?x. &0 <= x /\ x < pi / &2 /\ (tan(x) = y)`--),
  GEN_TAC THEN DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP TAN_TOTAL_LEMMA) THEN
    DISCH_THEN(X_CHOOSE_THEN (--`x:real`--) STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [(--`tan`--), (--`&0`--), (--`x:real`--), (--`y:real`--)] IVT) THEN
    W(C SUBGOAL_THEN (fn th => DISCH_THEN(MP_TAC o C MATCH_MP th)) o
         funpow 2 (fst o dest_imp) o snd) THENL
     [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LT_IMP_LE) THEN
      ASM_REWRITE_TAC[TAN_0] THEN X_GEN_TAC (--`z:real`--) THEN STRIP_TAC THEN
      MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC (--`inv(cos(z) pow 2)`--) THEN
      MATCH_MP_TAC DIFF_TAN THEN UNDISCH_TAC (--`&0 <= z`--) THEN
      REWRITE_TAC[REAL_LE_LT] THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
       [DISCH_TAC THEN MATCH_MP_TAC REAL_POS_NZ THEN
        MATCH_MP_TAC COS_POS_PI2 THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`x:real`--) THEN
        ASM_REWRITE_TAC[],
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[COS_0, REAL_10]],
      DISCH_THEN(X_CHOOSE_THEN (--`z:real`--) STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (--`z:real`--) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`x:real`--) THEN
      ASM_REWRITE_TAC[]],
    POP_ASSUM(SUBST1_TAC o SYM) THEN EXISTS_TAC (--`&0`--) THEN
    REWRITE_TAC[TAN_0, REAL_LE_REFL, PI2_BOUNDS]]);

val TAN_TOTAL = store_thm("TAN_TOTAL",
  (--`!y. ?!x. ~(pi / &2) < x /\ x < (pi / &2) /\ (tan(x) = y)`--),
  GEN_TAC THEN CONV_TAC EXISTS_UNIQUE_CONV THEN CONJ_TAC THENL
   [DISJ_CASES_TAC(SPEC (--`y:real`--) REAL_LE_NEGTOTAL) THEN
    POP_ASSUM(X_CHOOSE_TAC (--`x:real`--) o MATCH_MP TAN_TOTAL_POS) THENL
     [EXISTS_TAC (--`x:real`--) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`&0`--) THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM REAL_LT_NEG] THEN
      REWRITE_TAC[REAL_NEGNEG, REAL_NEG_0, PI2_BOUNDS],
      EXISTS_TAC (--`~x`--) THEN ASM_REWRITE_TAC[REAL_LT_NEG] THEN
      ASM_REWRITE_TAC[TAN_NEG, REAL_NEG_EQ, REAL_NEGNEG] THEN
      ONCE_REWRITE_TAC[GSYM REAL_LT_NEG] THEN
      REWRITE_TAC[REAL_LT_NEG] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC (--`x:real`--) THEN ASM_REWRITE_TAC[REAL_LE_NEGL]],
    MAP_EVERY X_GEN_TAC [(--`x1:real`--), (--`x2:real`--)] THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
         (SPECL [(--`x1:real`--), (--`x2:real`--)] REAL_LT_TOTAL) THENL
     [DISCH_THEN(K ALL_TAC) THEN POP_ASSUM ACCEPT_TAC,
      ALL_TAC,
      POP_ASSUM MP_TAC THEN SPEC_TAC((--`x1:real`--),(--`z1:real`--)) THEN
      SPEC_TAC((--`x2:real`--),(--`z2:real`--)) THEN
      MAP_EVERY X_GEN_TAC [(--`x1:real`--), (--`x2:real`--)] THEN DISCH_TAC THEN
      CONV_TAC(RAND_CONV SYM_CONV) THEN ONCE_REWRITE_TAC[CONJ_SYM]] THEN
    (STRIP_TAC THEN MP_TAC(SPECL [(--`tan`--), (--`x1:real`--), (--`x2:real`--)] ROLLE) THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC CONTRAPOS_CONV THEN
     DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[NOT_IMP] THEN
     REPEAT CONJ_TAC THENL
      [X_GEN_TAC (--`x:real`--) THEN STRIP_TAC THEN MATCH_MP_TAC DIFF_CONT THEN
       EXISTS_TAC (--`inv(cos(x) pow 2)`--) THEN MATCH_MP_TAC DIFF_TAN,
       X_GEN_TAC (--`x:real`--) THEN
       DISCH_THEN(CONJUNCTS_THEN (ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE)) THEN
       REWRITE_TAC[differentiable] THEN EXISTS_TAC (--`inv(cos(x) pow 2)`--) THEN
       MATCH_MP_TAC DIFF_TAN,
       REWRITE_TAC[CONJ_ASSOC] THEN DISCH_THEN(X_CHOOSE_THEN (--`x:real`--)
         (CONJUNCTS_THEN2 (CONJUNCTS_THEN (ASSUME_TAC o MATCH_MP
          REAL_LT_IMP_LE)) ASSUME_TAC)) THEN
       MP_TAC(SPEC (--`x:real`--) DIFF_TAN) THEN
       SUBGOAL_THEN (--`~(cos(x) = &0)`--) ASSUME_TAC THENL
        [ALL_TAC,
         ASM_REWRITE_TAC[] THEN
         DISCH_THEN(MP_TAC o C CONJ (ASSUME (--`(tan diffl &0)(x)`--))) THEN
         DISCH_THEN(MP_TAC o MATCH_MP DIFF_UNIQ) THEN REWRITE_TAC[] THEN
         MATCH_MP_TAC REAL_INV_NZ THEN MATCH_MP_TAC POW_NZ THEN
         ASM_REWRITE_TAC[]]] THEN
     (MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC COS_POS_PI THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`x1:real`--),
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`x2:real`--)] THEN
     ASM_REWRITE_TAC[]))]);

(*---------------------------------------------------------------------------*)
(* Inverse trig functions                                                    *)
(*---------------------------------------------------------------------------*)

val asn = new_definition("asn",
  (--`asn(y) = @x. ~(pi / &2) <= x /\ x <= pi / &2 /\ (sin x = y)`--));

val acs = new_definition("acs",
  (--`acs(y) = @x. &0 <= x /\ x <= pi /\ (cos x = y)`--));

val atn = new_definition("atn",
  (--`atn(y) = @x. ~(pi / &2) < x /\ x < pi / &2 /\ (tan x = y)`--));

val ASN = store_thm("ASN",
  (--`!y. ~(&1) <= y /\ y <= &1 ==>
           ~(pi / &2) <= asn(y) /\ (asn(y) <= pi / &2 /\ (sin(asn y) = y))`--),
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP SIN_TOTAL) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[GSYM asn]);

val ASN_SIN = store_thm("ASN_SIN",
  (--`!y. ~(&1) <= y /\ y <= &1 ==> (sin(asn(y)) = y)`--),
  GEN_TAC THEN DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP ASN th]));

val ASN_BOUNDS = store_thm("ASN_BOUNDS",
  (--`!y. ~(&1) <= y /\ y <= &1
           ==> ~(pi / &2) <= asn(y) /\ asn(y) <= pi / &2`--),
GEN_TAC THEN DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP ASN th]));

val ASN_BOUNDS_LT = store_thm("ASN_BOUNDS_LT",
  (--`!y. ~(&1) < y /\ y < &1 ==> ~(pi / &2) < asn(y) /\ asn(y) < pi / &2`--),
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (--`~(pi / &2) <= asn(y) /\ asn(y) <= pi / &2`--) ASSUME_TAC THENL
   [MATCH_MP_TAC ASN_BOUNDS THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
    ASM_REWRITE_TAC[REAL_LT_LE]] THEN
  CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM (--`sin`--)) THEN
  REWRITE_TAC[SIN_NEG, SIN_PI2] THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
  SUBGOAL_THEN (--`sin(asn y) = y`--) (fn th => ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC ASN_SIN THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]);

val SIN_ASN = store_thm("SIN_ASN",
  (--`!x. ~(pi / &2) <= x /\ x <= pi / &2 ==> (asn(sin(x)) = x)`--),
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(MATCH_MP SIN_TOTAL (SPEC (--`x:real`--) SIN_BOUNDS)) THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ASN THEN
  MATCH_ACCEPT_TAC SIN_BOUNDS);

val ACS = store_thm("ACS",
  (--`!y. ~(&1) <= y /\ y <= &1 ==>
     &0 <= acs(y) /\ acs(y) <= pi  /\ (cos(acs y) = y)`--),
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP COS_TOTAL) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[GSYM acs]);

val ACS_COS = store_thm("ACS_COS",
  (--`!y. ~(&1) <= y /\ y <= &1 ==> (cos(acs(y)) = y)`--),
  GEN_TAC THEN DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP ACS th]));

val ACS_BOUNDS = store_thm("ACS_BOUNDS",
  (--`!y. ~(&1) <= y /\ y <= &1 ==> &0 <= acs(y) /\ acs(y) <= pi`--),
  GEN_TAC THEN DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP ACS th]));

val ACS_BOUNDS_LT = store_thm("ACS_BOUNDS_LT",
  (--`!y. ~(&1) < y /\ y < &1 ==> &0 < acs(y) /\ acs(y) < pi`--),
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (--`&0 <= acs(y) /\ acs(y) <= pi`--) ASSUME_TAC THENL
   [MATCH_MP_TAC ACS_BOUNDS THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
    ASM_REWRITE_TAC[REAL_LT_LE]] THEN
  CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM (--`cos`--)) THEN
  REWRITE_TAC[COS_0, COS_PI] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  MATCH_MP_TAC REAL_LT_IMP_NE THEN
  SUBGOAL_THEN (--`cos(acs y) = y`--) (fn th => ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC ACS_COS THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]);

val COS_ACS = store_thm("COS_ACS",
  (--`!x. &0 <= x /\ x <= pi ==> (acs(cos(x)) = x)`--),
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(MATCH_MP COS_TOTAL (SPEC (--`x:real`--) COS_BOUNDS)) THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ACS THEN
  MATCH_ACCEPT_TAC COS_BOUNDS);

val ATN = store_thm("ATN",
  (--`!y. ~(pi / &2) < atn(y) /\ atn(y) < (pi / &2) /\ (tan(atn y) = y)`--),
  GEN_TAC THEN MP_TAC(SPEC (--`y:real`--) TAN_TOTAL) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[GSYM atn]);

val ATN_TAN = store_thm("ATN_TAN",
  (--`!y. tan(atn y) = y`--),
  REWRITE_TAC[ATN]);

val ATN_BOUNDS = store_thm("ATN_BOUNDS",
  (--`!y. ~(pi / &2) < atn(y) /\ atn(y) < (pi / &2)`--),
  REWRITE_TAC[ATN]);

val TAN_ATN = store_thm("TAN_ATN",
  (--`!x. ~(pi / &2) < x /\ x < (pi / &2) ==> (atn(tan(x)) = x)`--),
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC (--`tan(x)`--) TAN_TOTAL) THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  ASM_REWRITE_TAC[ATN]);

(*---------------------------------------------------------------------------*)
(* A few additional results about the trig functions                         *)
(*---------------------------------------------------------------------------*)

val TAN_SEC = store_thm("TAN_SEC",
  (--`!x. ~(cos(x) = &0) ==> (&1 + (tan(x) pow 2) = inv(cos x) pow 2)`--),
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[tan] THEN
  FIRST_ASSUM(fn th => ONCE_REWRITE_TAC[GSYM
   (MATCH_MP REAL_DIV_REFL (SPEC (--`2:num`--) (MATCH_MP POW_NZ th)))]) THEN
  REWRITE_TAC[real_div, POW_MUL] THEN
  POP_ASSUM(fn th => REWRITE_TAC[MATCH_MP POW_INV th]) THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[GSYM REAL_RDISTRIB, SIN_CIRCLE, REAL_MUL_LID]);

val SIN_COS_SQ = store_thm("SIN_COS_SQ",
  (--`!x. &0 <= x /\ x <= pi ==> (sin(x) = sqrt(&1 - (cos(x) pow 2)))`--),
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC SQRT_EQ THEN
  REWRITE_TAC[REAL_EQ_SUB_LADD, SIN_CIRCLE] THEN
  MATCH_MP_TAC SIN_POS_PI_LE THEN ASM_REWRITE_TAC[]);

val COS_SIN_SQ = store_thm("COS_SIN_SQ",
  (--`!x. ~(pi / &2) <= x /\ x <= (pi / &2) ==>
             (cos(x) = sqrt(&1 - (sin(x) pow 2)))`--),
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC SQRT_EQ THEN
  REWRITE_TAC[REAL_EQ_SUB_LADD] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[SIN_CIRCLE] THEN
  MATCH_MP_TAC COS_POS_PI_LE THEN ASM_REWRITE_TAC[]);

val COS_ATN_NZ = store_thm("COS_ATN_NZ",
  (--`!x. ~(cos(atn(x)) = &0)`--),
  GEN_TAC THEN MATCH_MP_TAC REAL_POS_NZ THEN
  MATCH_MP_TAC COS_POS_PI THEN MATCH_ACCEPT_TAC ATN_BOUNDS);

val COS_ASN_NZ = store_thm("COS_ASN_NZ",
  (--`!x. ~(&1) < x /\ x < &1 ==> ~(cos(asn(x)) = &0)`--),
  GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY MATCH_MP_TAC [REAL_POS_NZ, COS_POS_PI, ASN_BOUNDS_LT] THEN
  POP_ASSUM ACCEPT_TAC);

val SIN_ACS_NZ = store_thm("SIN_ACS_NZ",
  (--`!x. ~(&1) < x /\ x < &1 ==> ~(sin(acs(x)) = &0)`--),
  GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY MATCH_MP_TAC [REAL_POS_NZ, SIN_POS_PI, ACS_BOUNDS_LT] THEN
  POP_ASSUM ACCEPT_TAC);

val COS_SIN_SQRT = store_thm("COS_SIN_SQRT",
  Term `!x. &0 <= cos(x) ==> (cos(x) = sqrt(&1 - (sin(x) pow 2)))`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (ONCE_REWRITE_RULE[REAL_ADD_SYM] (SPEC (Term`x:real`) SIN_CIRCLE))
  THEN REWRITE_TAC[GSYM REAL_EQ_SUB_LADD] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[sqrt, TWO] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC POW_ROOT_POS THEN
  ASM_REWRITE_TAC[]);;

val SIN_COS_SQRT = store_thm("SIN_COS_SQRT",
  Term`!x. &0 <= sin(x) ==> (sin(x) = sqrt(&1 - (cos(x) pow 2)))`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (SPEC (Term`x:real`) SIN_CIRCLE) THEN
  REWRITE_TAC[GSYM REAL_EQ_SUB_LADD] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[sqrt, TWO] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC POW_ROOT_POS THEN
  ASM_REWRITE_TAC[]);;


(*---------------------------------------------------------------------------*)
(* Derivatives of the inverse functions, starting with natural log           *)
(*---------------------------------------------------------------------------*)

val DIFF_LN = store_thm("DIFF_LN",
  (--`!x. &0 < x ==> (ln diffl (inv x))(x)`--),
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN (--`(ln diffl (inv x))(exp(ln(x)))`--) MP_TAC THENL
   [MATCH_MP_TAC DIFF_INVERSE_OPEN,
    MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[EXP_LN]] THEN
  MAP_EVERY EXISTS_TAC [(--`ln(x) - &1`--), (--`ln(x) + &1`--)] THEN
  REWRITE_TAC[REAL_LT_SUB_RADD, REAL_LT_ADDR, REAL_LT_01, LN_EXP,
    MATCH_MP DIFF_CONT (SPEC_ALL DIFF_EXP)] THEN
  CONJ_TAC THENL
   [MP_TAC(SPEC (--`ln(x)`--) DIFF_EXP) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM EXP_LN]), MATCH_MP_TAC REAL_POS_NZ] THEN
  ASM_REWRITE_TAC[]);

(* Known as DIFF_ASN_COS in GTT *)
val DIFF_ASN_LEMMA = store_thm("DIFF_ASN_LEMMA",
  (--`!x. ~(&1) < x /\ x < &1 ==> (asn diffl (inv(cos(asn x))))(x)`--),
  GEN_TAC THEN STRIP_TAC THEN IMP_RES_TAC REAL_LT_IMP_LE THEN
  MP_TAC(SPEC (--`x:real`--) ASN_SIN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fn th => GEN_REWR_TAC RAND_CONV  [SYM th]) THEN
  MATCH_MP_TAC DIFF_INVERSE_OPEN THEN REWRITE_TAC[DIFF_SIN] THEN
  MAP_EVERY EXISTS_TAC [(--`~(pi / &2)`--), (--`pi / &2`--)] THEN
  MP_TAC(SPEC (--`x:real`--) ASN_BOUNDS_LT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]) THEN CONJ_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN IMP_RES_TAC REAL_LT_IMP_LE THEN
    REWRITE_TAC[MATCH_MP DIFF_CONT (SPEC_ALL DIFF_SIN)] THEN
    MATCH_MP_TAC SIN_ASN THEN ASM_REWRITE_TAC[],
    MATCH_MP_TAC COS_ASN_NZ THEN ASM_REWRITE_TAC[]]);

val DIFF_ASN = store_thm("DIFF_ASN",
  (--`!x. ~(&1) < x /\ x < &1 ==> (asn diffl (inv(sqrt(&1 - (x pow 2)))))(x)`--),
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIFF_ASN_LEMMA) THEN
  MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN (--`cos(asn(x)) = sqrt(&1 - (sin(asn x) pow 2))`--) SUBST1_TAC THENL
   [MATCH_MP_TAC COS_SIN_SQ THEN MATCH_MP_TAC ASN_BOUNDS,
    SUBGOAL_THEN (--`sin(asn x) = x`--) SUBST1_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC ASN_SIN] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]);

(* Known as DIFF_ACS_SIN in GTT *)
val DIFF_ACS_LEMMA = store_thm("DIFF_ACS_LEMMA",
  (--`!x. ~(&1) < x /\ x < &1 ==> (acs diffl inv(~(sin(acs x))))(x)`--),
  GEN_TAC THEN STRIP_TAC THEN IMP_RES_TAC REAL_LT_IMP_LE THEN
  MP_TAC(SPEC (--`x:real`--) ACS_COS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fn th => GEN_REWR_TAC RAND_CONV  [SYM th]) THEN
  MATCH_MP_TAC DIFF_INVERSE_OPEN THEN REWRITE_TAC[DIFF_COS] THEN
  MAP_EVERY EXISTS_TAC [(--`&0`--), (--`pi`--)] THEN
  MP_TAC(SPEC (--`x:real`--) ACS_BOUNDS_LT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]) THEN CONJ_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN IMP_RES_TAC REAL_LT_IMP_LE THEN
    REWRITE_TAC[MATCH_MP DIFF_CONT (SPEC_ALL DIFF_COS)] THEN
    MATCH_MP_TAC COS_ACS THEN ASM_REWRITE_TAC[],
    REWRITE_TAC[REAL_NEG_EQ, REAL_NEG_0] THEN
    MATCH_MP_TAC SIN_ACS_NZ THEN ASM_REWRITE_TAC[]]);

val DIFF_ACS = store_thm("DIFF_ACS",
  (--`!x. ~(&1) < x /\ x <  &1 ==> (acs diffl ~(inv(sqrt(&1 - (x pow 2)))))(x)`--),
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIFF_ACS_LEMMA) THEN
  MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN (--`sin(acs(x)) = sqrt(&1 - (cos(acs x) pow 2))`--) SUBST1_TAC THENL
   [MATCH_MP_TAC SIN_COS_SQ THEN MATCH_MP_TAC ACS_BOUNDS,
    SUBGOAL_THEN (--`cos(acs x) = x`--) SUBST1_TAC THENL
     [MATCH_MP_TAC ACS_COS,
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_NEG_INV THEN
      MATCH_MP_TAC REAL_POS_NZ THEN REWRITE_TAC[sqrt, TWO] THEN
      MATCH_MP_TAC ROOT_POS_LT THEN
      REWRITE_TAC[REAL_LT_SUB_LADD, REAL_ADD_LID] THEN
      REWRITE_TAC[SYM(TWO), POW_2] THEN
      GEN_REWR_TAC RAND_CONV  [GSYM REAL_MUL_LID] THEN
      DISJ_CASES_TAC (SPEC (--`x:real`--) REAL_LE_NEGTOTAL) THENL
       [ALL_TAC, GEN_REWR_TAC LAND_CONV  [GSYM REAL_NEG_MUL2]] THEN
      MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC [GSYM REAL_LT_NEG] THEN
      ASM_REWRITE_TAC[REAL_NEGNEG]]] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]);

val DIFF_ATN = store_thm("DIFF_ATN",
  (--`!x. (atn diffl (inv(&1 + (x pow 2))))(x)`--),
  GEN_TAC THEN
  SUBGOAL_THEN (--`(atn diffl (inv(&1 + (x pow 2))))(tan(atn x))`--) MP_TAC THENL
   [MATCH_MP_TAC DIFF_INVERSE_OPEN, REWRITE_TAC[ATN_TAN]] THEN
  MAP_EVERY EXISTS_TAC [(--`~(pi / &2)`--), (--`pi / &2`--)] THEN
  REWRITE_TAC[ATN_BOUNDS] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC (--`x:real`--) THEN DISCH_TAC THEN
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP TAN_ATN th]) THEN
    MATCH_MP_TAC DIFF_CONT THEN
    EXISTS_TAC (--`inv(cos(x) pow 2)`--) THEN
    MATCH_MP_TAC DIFF_TAN THEN
    MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC COS_POS_PI THEN
    ASM_REWRITE_TAC[],
    MP_TAC(SPEC (--`atn(x)`--) DIFF_TAN) THEN REWRITE_TAC[COS_ATN_NZ] THEN
    REWRITE_TAC[MATCH_MP POW_INV (SPEC (--`x:real`--) COS_ATN_NZ)] THEN
    REWRITE_TAC[GSYM(MATCH_MP TAN_SEC (SPEC (--`x:real`--) COS_ATN_NZ))] THEN
    REWRITE_TAC[ATN_TAN],
    MATCH_MP_TAC REAL_POS_NZ THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`&1`--) THEN
    REWRITE_TAC[REAL_LT_01, REAL_LE_ADDR, POW_2, REAL_LE_SQUARE]]);



(* ======================================================================== *)
(* Formalization of Kurzweil-Henstock gauge integral                        *)
(* ======================================================================== *)

fun LE_MATCH_TAC th (asl,w) =
  let val thi = PART_MATCH (rand o rator) th (rand(rator w))
      val tm = rand(concl thi)
  in
   (MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC tm THEN CONJ_TAC THENL
    [MATCH_ACCEPT_TAC th, ALL_TAC]) (asl,w)
  end;

(* ------------------------------------------------------------------------ *)
(* Some miscellaneous lemmas                                                *)
(* ------------------------------------------------------------------------ *)
(*
let LESS_SUC_EQ = prove(
  `!m n. m < SUC n = m <= n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJUNCT2 LT; LE_LT] THEN
  EQ_TAC THEN DISCH_THEN(DISJ_CASES_THEN(fun th -> REWRITE_TAC[th])));;
*)
(* ------------------------------------------------------------------------ *)
(* Divisions and tagged divisions etc.                                      *)
(* ------------------------------------------------------------------------ *)

val division = new_definition("division",
Term`division(a,b) D =
     (D 0 = a) /\
     (?N. (!n. n < N ==> D(n) < D(SUC n)) /\
          (!n. n >= N ==> (D(n) = b)))`);

val dsize = new_definition("dsize",
 Term`dsize D =
      @N. (!n. n < N ==> D(n) < D(SUC n)) /\
          (!n. n >= N ==> (D(n) = D(N)))`);

val tdiv = new_definition("tdiv",
 Term`tdiv(a,b) (D,p) =
     division(a,b) D /\
     (!n. D(n) <= p(n) /\ p(n) <= D(SUC n))`);

(* ------------------------------------------------------------------------ *)
(* Gauges and gauge-fine divisions                                          *)
(* ------------------------------------------------------------------------ *)

val gauge = new_definition("gauge",
  Term`gauge(E) (g:real->real) = !x. E x ==> &0 < g(x)`);;

val fine = new_definition("fine",
 Term`fine(g:real->real) (D,p) =
     !n. n < dsize D ==> D(SUC n) - D(n) < g(p(n))`);

(* ------------------------------------------------------------------------ *)
(* Riemann sum                                                              *)
(* ------------------------------------------------------------------------ *)

val rsum = new_definition("rsum",
  Term`rsum (D,(p:num->real)) f =
        sum(0,dsize(D))(\n. f(p n) * (D(SUC n) - D(n)))`);

(* ------------------------------------------------------------------------ *)
(* Gauge integrability (definite)                                           *)
(* ------------------------------------------------------------------------ *)

val Dint = new_definition("Dint",
 Term `Dint(a,b) f k =
        !e. &0 < e ==>
           ?g. gauge(\x. a <= x /\ x <= b) g /\
               !D p. tdiv(a,b) (D,p) /\ fine(g)(D,p) ==>
                   abs(rsum(D,p) f - k) < e`);;

(* ------------------------------------------------------------------------ *)
(* Useful lemmas about the size of `trivial` divisions etc.                 *)
(* ------------------------------------------------------------------------ *)

val DIVISION_0 = store_thm("DIVISION_0",
 Term `!a b. (a = b) ==> (dsize(\n:num. if (n = 0) then a else b) = 0)`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[COND_ID] THEN
  REWRITE_TAC[dsize] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC (Term `n:num`) THEN BETA_TAC THEN
  REWRITE_TAC[REAL_LT_REFL, NOT_LESS] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC (Term `0:num`)) THEN
     REWRITE_TAC[LESS_OR_EQ,NOT_LESS_0],
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ZERO_LESS_EQ]]);;

val DIVISION_1 = store_thm("DIVISION_1",
  Term `!a b. a < b ==> (dsize(\n. if (n = 0) then a else b) = 1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[dsize] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC (Term `n:num`) THEN BETA_TAC THEN
  REWRITE_TAC[NOT_SUC] THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC LESS_EQUAL_ANTISYM THEN CONJ_TAC THENL
     [POP_ASSUM(MP_TAC o SPEC (Term`1:num`) o CONJUNCT1) THEN
      REWRITE_TAC[ONE, GSYM SUC_NOT] THEN
      REWRITE_TAC[REAL_LT_REFL, NOT_LESS],
      POP_ASSUM(MP_TAC o SPEC (Term `2:num`) o CONJUNCT2) THEN
      REWRITE_TAC[TWO, GSYM SUC_NOT, GREATER_EQ] THEN
      CONV_TAC CONTRAPOS_CONV THEN
      REWRITE_TAC[ONE, NOT_SUC_LESS_EQ, CONJUNCT1 LE] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NOT_SUC, NOT_IMP] THEN
      REWRITE_TAC[LE] THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN POP_ASSUM ACCEPT_TAC],
    DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[ONE,LESS_THM, NOT_LESS_0] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[],
      X_GEN_TAC (Term `n:num`) THEN REWRITE_TAC[GREATER_EQ,ONE]
      THEN ASM_CASES_TAC (Term `n:num = 0`) THEN
      ASM_REWRITE_TAC[CONJUNCT1 LE, GSYM NOT_SUC, NOT_SUC]]]);

val LESS_1 = prove (Term`!x:num. x < 1 = (x = 0)`,
 INDUCT_TAC THEN
  REWRITE_TAC [ONE,LESS_0,LESS_MONO_EQ,NOT_LESS_0,GSYM SUC_NOT]);

val DIVISION_SINGLE = store_thm("DIVISION_SINGLE",
  Term `!a b. a <= b ==> division(a,b)(\n. if (n = 0) then a else b)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[division] THEN
  BETA_TAC THEN REWRITE_TAC[] THEN
  POP_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [EXISTS_TAC (Term `1:num`) THEN CONJ_TAC THEN X_GEN_TAC (Term `n:num`) THENL
     [REWRITE_TAC[LESS_1] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[NOT_SUC],
      REWRITE_TAC[GREATER_EQ] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[ONE] THEN
      REWRITE_TAC[LE, NOT_SUC]],
    EXISTS_TAC (Term `0:num`) THEN REWRITE_TAC[NOT_LESS_0] THEN
    ASM_REWRITE_TAC[COND_ID]]);

val DIVISION_LHS = store_thm("DIVISION_LHS",
  Term `!D a b. division(a,b) D ==> (D(0) = a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[division] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]));

val DIVISION_THM = store_thm("DIVISION_THM",
 Term `!D a b.
         division(a,b) D
           =
         (D(0) = a) /\
         (!n. n < (dsize D) ==> D(n) < D(SUC n)) /\
         (!n. n >= (dsize D) ==> (D(n) = b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[division] THEN
  EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC, EXISTS_TAC (Term `dsize D`) THEN ASM_REWRITE_TAC[]] THEN
  POP_ASSUM(X_CHOOSE_THEN (Term `N:num`) STRIP_ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN (Term `dsize D:num = N`) (fn th => ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[dsize] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC (Term `M:num`) THEN BETA_TAC THEN EQ_TAC THENL
   [ALL_TAC, DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC (Term `N:num`) (ASSUME (Term `!n:num. n >= N ==> (D n:real = b)`)))
    THEN DISCH_THEN(MP_TAC o REWRITE_RULE[GREATER_EQ, LESS_EQ_REFL]) THEN
    DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC] THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL [Term `M:num`, Term `N:num`] LESS_LESS_CASES) THEN
  ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(MP_TAC o SPEC (Term `SUC M`) o CONJUNCT2) THEN
    REWRITE_TAC[GREATER_EQ, LESS_EQ_SUC_REFL] THEN DISCH_TAC THEN
    UNDISCH_TAC (Term `!n:num. n < N ==> (D n) < (D(SUC n))`) THEN
    DISCH_THEN(MP_TAC o SPEC (Term`M:num`)) THEN ASM_REWRITE_TAC[REAL_LT_REFL],
    DISCH_THEN(MP_TAC o SPEC (Term`N:num`) o CONJUNCT1) THEN ASM_REWRITE_TAC[]
    THEN UNDISCH_TAC (Term`!n:num. n >= N ==> (D n:real = b)`) THEN
    DISCH_THEN(fn th => MP_TAC(SPEC (Term`N:num`) th) THEN
    MP_TAC(SPEC (Term`SUC N`) th)) THEN
    REWRITE_TAC[GREATER_EQ, LESS_EQ_SUC_REFL, LESS_EQ_REFL] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_LT_REFL]]);

val DIVISION_RHS = store_thm("DIVISION_RHS",
  Term`!D a b. division(a,b) D ==> (D(dsize D) = b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DIVISION_THM] THEN
  DISCH_THEN(MP_TAC o SPEC (Term`dsize D`) o last o CONJUNCTS) THEN
  REWRITE_TAC[GREATER_EQ, LESS_EQ_REFL]);

val DIVISION_LT_GEN = store_thm("DIVISION_LT_GEN",
Term`!D a b m n. division(a,b) D /\ m < n /\ n <= (dsize D) ==> D(m) < D(n)`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC (Term`m:num < n`) THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`d:num`) MP_TAC o MATCH_MP LESS_ADD_1) THEN
  REWRITE_TAC[GSYM ADD1] THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC (Term `m + SUC d <= dsize D`) THEN
  SPEC_TAC(Term`d:num`,Term`d:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OR_LESS) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DIVISION_THM]) THEN ASM_REWRITE_TAC[],
    REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OR_LESS) THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC (Term`D(m + SUC d):real`) THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
      MATCH_MP_TAC LESS_IMP_LESS_OR_EQ THEN ASM_REWRITE_TAC[],
      REWRITE_TAC[ADD_CLAUSES] THEN
      FIRST_ASSUM(MATCH_MP_TAC o el 2 o
        CONJUNCTS o REWRITE_RULE[DIVISION_THM]) THEN
      ASM_REWRITE_TAC[]]]);;

val DIVISION_LT = store_thm("DIVISION_LT",
  Term`!D a b. division(a,b) D ==> !n. n < (dsize D) ==> D(0) < D(SUC n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DIVISION_THM] THEN STRIP_TAC THEN
  INDUCT_TAC THEN DISCH_THEN(fn th => ASSUME_TAC th THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (Term`D(SUC n):real`) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC (Term`D(0:num):real = a`) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (Term`SUC n`) THEN
  ASM_REWRITE_TAC[LESS_SUC_REFL]);

val DIVISION_LE = store_thm("DIVISION_LE",
  Term`!D a b. division(a,b) D ==> a <= b`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIVISION_LT) THEN
  POP_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DIVISION_THM]) THEN
  UNDISCH_TAC (Term`D(0:num):real = a`) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC (Term`!n. n >= (dsize D) ==> (D n = b)`) THEN
  DISCH_THEN(MP_TAC o SPEC (Term`dsize D`)) THEN
  REWRITE_TAC[GREATER_EQ, LESS_EQ_REFL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(MP_TAC o SPEC (Term`PRE(dsize D)`)) THEN
  STRUCT_CASES_TAC(SPEC (Term`dsize D`) num_CASES) THEN
  ASM_REWRITE_TAC[PRE, REAL_LE_REFL, LESS_SUC_REFL, REAL_LT_IMP_LE]);;

val DIVISION_GT = store_thm("DIVISION_GT",
  Term`!D a b. division(a,b) D ==> !n. n < (dsize D) ==> D(n) < D(dsize D)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIVISION_LT_GEN THEN
  MAP_EVERY EXISTS_TAC [Term`a:real`, Term`b:real`] THEN
  ASM_REWRITE_TAC[LESS_EQ_REFL]);;

val DIVISION_EQ = store_thm("DIVISION_EQ",
  Term`!D a b. division(a,b) D ==> ((a = b) = (dsize D = 0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIVISION_LT) THEN
  POP_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DIVISION_THM]) THEN
  UNDISCH_TAC (Term`D(0:num):real = a`) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC (Term`!n. n >= (dsize D) ==> (D n = b)`) THEN
  DISCH_THEN(MP_TAC o SPEC (Term`dsize D`)) THEN
  REWRITE_TAC[GREATER_EQ, LESS_EQ_REFL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(MP_TAC o SPEC (Term`PRE(dsize D)`)) THEN
  STRUCT_CASES_TAC(SPEC (Term`dsize D`) num_CASES) THEN
  ASM_REWRITE_TAC[PRE, NOT_SUC, LESS_SUC_REFL, REAL_LT_IMP_NE]);

val DIVISION_LBOUND = store_thm("DIVISION_LBOUND",
  Term`!D a b. division(a,b) D ==> !r. a <= D(r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DIVISION_THM] THEN STRIP_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISJ_CASES_TAC(SPECL [Term`SUC r`, Term`dsize D`] LESS_CASES) THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (Term`(D:num->real) r`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (Term`SUC r`) THEN
    ASM_REWRITE_TAC[LESS_SUC_REFL],
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (Term`b:real`) THEN CONJ_TAC
    THENL
     [MATCH_MP_TAC DIVISION_LE THEN
      EXISTS_TAC (Term`D:num->real`) THEN ASM_REWRITE_TAC[DIVISION_THM],
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[GREATER_EQ]]]);;

val DIVISION_LBOUND_LT = store_thm("DIVISION_LBOUND_LT",
 Term`!D a b. division(a,b) D /\ ~(dsize D = 0) ==> !n. a < D(SUC n)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP DIVISION_LHS) THEN
  DISJ_CASES_TAC(SPECL [Term`dsize D`, Term`SUC n`] LESS_CASES) THENL
   [FIRST_ASSUM(MP_TAC o el 3 o CONJUNCTS o REWRITE_RULE[DIVISION_THM]) THEN
    DISCH_THEN(MP_TAC o SPEC (Term`SUC n`)) THEN REWRITE_TAC[GREATER_EQ] THEN
    IMP_RES_THEN ASSUME_TAC LESS_IMP_LESS_OR_EQ THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP DIVISION_RHS) THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP DIVISION_GT) THEN
    ASM_REWRITE_TAC[GSYM NOT_LESS_EQUAL, CONJUNCT1 LE],
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP DIVISION_LT) THEN
    MATCH_MP_TAC OR_LESS THEN ASM_REWRITE_TAC[]]);;

val DIVISION_UBOUND = store_thm("DIVISION_UBOUND",
 Term`!D a b. division(a,b) D ==> !r. D(r) <= b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DIVISION_THM] THEN STRIP_TAC THEN
  GEN_TAC THEN DISJ_CASES_TAC(SPECL [Term`r:num`, Term`dsize D`] LESS_CASES)
  THENL [ALL_TAC,
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[GREATER_EQ]] THEN
  SUBGOAL_THEN (Term`!r. D((dsize D) - r) <= b`) MP_TAC THENL
   [ALL_TAC,
    DISCH_THEN(MP_TAC o SPEC (Term`(dsize D) - r`)) THEN
    MATCH_MP_TAC(TAUT_CONV (Term`(a = b) ==> a ==> b`)) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP SUB_SUB
         (MATCH_MP LESS_IMP_LESS_OR_EQ th)])
    THEN ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB]] THEN
  UNDISCH_TAC (Term`r < dsize D`) THEN DISCH_THEN(K ALL_TAC) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[SUB_0] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[GREATER_EQ, LESS_EQ_REFL],
    ALL_TAC] THEN
  DISJ_CASES_TAC(SPECL [Term`r:num`, Term`dsize D`] LESS_CASES) THENL
   [ALL_TAC,
    SUBGOAL_THEN (Term`(dsize D) - (SUC r) = 0`) SUBST1_TAC THENL
     [REWRITE_TAC[SUB_EQ_0] THEN MATCH_MP_TAC LESS_EQ_TRANS THEN
      EXISTS_TAC (Term`r:num`) THEN ASM_REWRITE_TAC[LESS_EQ_SUC_REFL],
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIVISION_LE THEN
      EXISTS_TAC (Term`D:num->real`) THEN ASM_REWRITE_TAC[DIVISION_THM]]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC (Term`D((dsize D) - r):real`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (Term`(dsize D) - r = SUC((dsize D) - (SUC r))`)
  SUBST1_TAC THENL
   [ALL_TAC,
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LESS_CASES_IMP THEN
    REWRITE_TAC[NOT_LESS, SUB_LESS_EQ] THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    REWRITE_TAC[SUB_EQ_EQ_0, NOT_SUC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC (Term`r:num < 0`) THEN REWRITE_TAC[NOT_LESS_0]] THEN
  MP_TAC(SPECL [Term`dsize D`, Term`SUC r`] (CONJUNCT2 SUB)) THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[SUB_EQ_0, LESS_EQ_MONO] THEN
    ASM_REWRITE_TAC[GSYM NOT_LESS],
    DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC[SUB_MONO_EQ]]);

val DIVISION_UBOUND_LT = store_thm("DIVISION_UBOUND_LT",
 Term`!D a b n. division(a,b) D /\ n < dsize D ==> D(n) < b`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP DIVISION_RHS) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP DIVISION_GT) THEN
  ASM_REWRITE_TAC[]);

(* ------------------------------------------------------------------------ *)
(* Divisions of adjacent intervals can be combined into one                 *)
(* ------------------------------------------------------------------------ *)

val D_tm = Term`\n. if n < dsize D1 then D1(n) else D2(n - dsize D1)`
and p_tm = Term`\n. if n < dsize D1 then (p1:num->real)(n) else p2(n - dsize D1)`;

val DIVISION_APPEND_LEMMA1 = prove(
 Term `!a b c D1 D2.
   division(a,b) D1 /\ division(b,c) D2
    ==>
    (!n. n < dsize D1 + dsize D2
         ==>
         (\n. if n < dsize D1 then D1(n) else D2(n - dsize D1)) (n)
            <
         (\n. if n < dsize D1 then D1(n) else D2(n - dsize D1)) (SUC n)) /\
    (!n. n >= dsize D1 + dsize D2
         ==>
         ((\n. if n<dsize D1 then D1(n) else D2(n - dsize D1)) (n)
           =
          (\n. if n<dsize D1 then D1(n) else D2(n - dsize D1)) (dsize D1 + dsize D2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
  X_GEN_TAC (Term`n:num`) THEN DISCH_TAC THEN BETA_TAC THENL
   [ASM_CASES_TAC (Term`SUC n < dsize D1`) THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN (Term`n < dsize D1`) ASSUME_TAC THEN
      ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (Term`SUC n`) THEN
        ASM_REWRITE_TAC[LESS_SUC_REFL],
        UNDISCH_TAC (Term`division(a,b) D1`) THEN REWRITE_TAC[DIVISION_THM] THEN
        STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
        FIRST_ASSUM ACCEPT_TAC],
      ASM_CASES_TAC (Term`n < dsize D1`) THEN ASM_REWRITE_TAC[] THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[NOT_LESS]) THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (Term`b:real`) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC DIVISION_UBOUND_LT THEN
          EXISTS_TAC (Term`a:real`) THEN ASM_REWRITE_TAC[],
          MATCH_MP_TAC DIVISION_LBOUND THEN
          EXISTS_TAC (Term`c:real`) THEN ASM_REWRITE_TAC[]],
        UNDISCH_TAC (Term`~(n < dsize D1)`) THEN
        REWRITE_TAC[NOT_LESS] THEN
        DISCH_THEN(X_CHOOSE_THEN (Term`d:num`) SUBST_ALL_TAC o
          REWRITE_RULE[LESS_EQ_EXISTS]) THEN
        REWRITE_TAC[SUB, GSYM NOT_LESS_EQUAL, LESS_EQ_ADD] THEN
        ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
        FIRST_ASSUM(MATCH_MP_TAC o Lib.trye el 2 o CONJUNCTS o
          REWRITE_RULE[DIVISION_THM]) THEN
        UNDISCH_TAC (Term`dsize D1 + d < dsize D1 + dsize D2`) THEN
        ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[LESS_MONO_ADD_EQ]]],
    REWRITE_TAC[GSYM NOT_LESS_EQUAL, LESS_EQ_ADD] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
    REWRITE_TAC[NOT_LESS_EQUAL] THEN COND_CASES_TAC THEN
    UNDISCH_TAC (Term`n >= dsize D1 + dsize D2`) THENL
     [CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN
      REWRITE_TAC[GREATER_EQ, NOT_LESS_EQUAL] THEN
      MATCH_MP_TAC LESS_IMP_LESS_ADD THEN ASM_REWRITE_TAC[],
      REWRITE_TAC[GREATER_EQ, LESS_EQ_EXISTS] THEN
      DISCH_THEN(X_CHOOSE_THEN (Term`d:num`) SUBST_ALL_TAC) THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[ADD_SUB] THEN
      FIRST_ASSUM(CHANGED_TAC o
       (SUBST1_TAC o MATCH_MP DIVISION_RHS)) THEN
      FIRST_ASSUM(MATCH_MP_TAC o el 3 o CONJUNCTS o
        REWRITE_RULE[DIVISION_THM]) THEN
      REWRITE_TAC[GREATER_EQ, LESS_EQ_ADD]]]);

val DIVISION_APPEND_LEMMA2 = prove(
 Term`!a b c D1 D2.
    division(a,b) D1 /\ division(b,c) D2
      ==>
      (dsize(\n. if n < dsize D1 then D1(n) else D2(n - dsize D1))
         =
       dsize D1 + dsize D2)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [] [dsize] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC (Term`N:num`) THEN BETA_TAC THEN EQ_TAC THENL
   [DISCH_THEN(curry op THEN (MATCH_MP_TAC LESS_EQUAL_ANTISYM) o MP_TAC) THEN
    CONV_TAC CONTRAPOS_CONV THEN
    REWRITE_TAC[DE_MORGAN_THM, NOT_LESS_EQUAL] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [DISJ1_TAC THEN
      DISCH_THEN(MP_TAC o SPEC (Term`dsize D1 + dsize D2`)) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM NOT_LESS_EQUAL, LESS_EQ_ADD] THEN
      SUBGOAL_THEN (Term`!x y. x <= SUC(x + y)`) ASSUME_TAC THENL
       [REPEAT GEN_TAC THEN MATCH_MP_TAC LESS_EQ_TRANS THEN
        EXISTS_TAC (Term`(x:num) + y`) THEN
        REWRITE_TAC[LESS_EQ_ADD, LESS_EQ_SUC_REFL], ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUB, GSYM NOT_LESS_EQUAL] THEN
      REWRITE_TAC[LESS_EQ_ADD] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[ADD_SUB] THEN
      MP_TAC(ASSUME (Term`division(b,c) D2`)) THEN REWRITE_TAC[DIVISION_THM]
      THEN DISCH_THEN(MP_TAC o SPEC (Term`SUC(dsize D2)`) o el 3 o CONJUNCTS)
      THEN REWRITE_TAC[GREATER_EQ, LESS_EQ_SUC_REFL] THEN
      DISCH_THEN SUBST1_TAC THEN
      FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o MATCH_MP DIVISION_RHS) THEN
      REWRITE_TAC[REAL_LT_REFL],
      DISJ2_TAC THEN
      DISCH_THEN(MP_TAC o SPEC (Term`dsize D1 + dsize D2`)) THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP LESS_IMP_LESS_OR_EQ) THEN
      ASM_REWRITE_TAC[GREATER_EQ] THEN
      REWRITE_TAC[GSYM NOT_LESS_EQUAL, LESS_EQ_ADD] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
      COND_CASES_TAC THENL
       [SUBGOAL_THEN (Term`D1(N:num) < D2(dsize D2)`) MP_TAC THENL
         [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (Term`b:real`) THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC DIVISION_UBOUND_LT THEN EXISTS_TAC (Term`a:real`) THEN
            ASM_REWRITE_TAC[GSYM NOT_LESS_EQUAL],
            MATCH_MP_TAC DIVISION_LBOUND THEN
            EXISTS_TAC (Term`c:real`) THEN ASM_REWRITE_TAC[]],
          CONV_TAC CONTRAPOS_CONV THEN ASM_REWRITE_TAC[] THEN
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LT_REFL]],
        RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
        SUBGOAL_THEN (Term`D2(N - dsize D1) < D2(dsize D2)`) MP_TAC THENL
         [MATCH_MP_TAC DIVISION_LT_GEN THEN
          MAP_EVERY EXISTS_TAC [Term`b:real`, Term`c:real`] THEN
          ASM_REWRITE_TAC[LESS_EQ_REFL] THEN
          REWRITE_TAC[GSYM NOT_LESS_EQUAL] THEN
          REWRITE_TAC[SUB_LEFT_LESS_EQ, DE_MORGAN_THM] THEN
          ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[NOT_LESS_EQUAL] THEN
          UNDISCH_TAC (Term`dsize(D1) <= N`) THEN
          REWRITE_TAC[LESS_EQ_EXISTS] THEN
          DISCH_THEN(X_CHOOSE_THEN (Term`d:num`) SUBST_ALL_TAC) THEN
          RULE_ASSUM_TAC(ONCE_REWRITE_RULE[ADD_SYM]) THEN
          RULE_ASSUM_TAC(REWRITE_RULE[LESS_MONO_ADD_EQ]) THEN
          MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN EXISTS_TAC (Term`d:num`) THEN
          ASM_REWRITE_TAC[ZERO_LESS_EQ],
          CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LT_REFL]]]],
  DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC (Term`n:num`) THEN DISCH_TAC THEN
    ASM_CASES_TAC (Term`SUC n < dsize D1`) THEN
    ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN (Term`n < dsize D1`) ASSUME_TAC THENL
       [MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (Term`SUC n`) THEN
        ASM_REWRITE_TAC[LESS_SUC_REFL], ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIVISION_LT_GEN THEN
      MAP_EVERY EXISTS_TAC [Term`a:real`, Term`b:real`] THEN
      ASM_REWRITE_TAC[LESS_SUC_REFL] THEN
      MATCH_MP_TAC LESS_IMP_LESS_OR_EQ THEN ASM_REWRITE_TAC[],
      COND_CASES_TAC THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (Term`b:real`) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC DIVISION_UBOUND_LT THEN EXISTS_TAC (Term`a:real`) THEN
          ASM_REWRITE_TAC[],
          FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP DIVISION_LBOUND)],
        MATCH_MP_TAC DIVISION_LT_GEN THEN
        MAP_EVERY EXISTS_TAC [Term`b:real`, Term`c:real`] THEN
        ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC[SUB, LESS_SUC_REFL], ALL_TAC] THEN
        REWRITE_TAC[REWRITE_RULE[GREATER_EQ] SUB_LEFT_GREATER_EQ] THEN
        ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[GSYM LESS_EQ]]],
    X_GEN_TAC (Term`n:num`) THEN REWRITE_TAC[GREATER_EQ] THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM NOT_LESS_EQUAL,LESS_EQ_ADD] THEN
    SUBGOAL_THEN (Term`dsize D1 <= n`) ASSUME_TAC THENL
     [MATCH_MP_TAC LESS_EQ_TRANS THEN
      EXISTS_TAC (Term `dsize D1 + dsize D2`) THEN
      ASM_REWRITE_TAC[LESS_EQ_ADD],
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[ADD_SUB] THEN
      FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o MATCH_MP DIVISION_RHS) THEN
      FIRST_ASSUM(MATCH_MP_TAC o el 3 o
        CONJUNCTS o REWRITE_RULE[DIVISION_THM]) THEN
      REWRITE_TAC[GREATER_EQ, SUB_LEFT_LESS_EQ] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[]]]]);

val DIVISION_APPEND = store_thm("DIVISION_APPEND",
  Term`!a b c.
      (?D1 p1. tdiv(a,b) (D1,p1) /\ fine(g) (D1,p1)) /\
      (?D2 p2. tdiv(b,c) (D2,p2) /\ fine(g) (D2,p2)) ==>
        ?D p. tdiv(a,c) (D,p) /\ fine(g) (D,p)`,
  REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [D_tm, p_tm] THEN
  DISJ_CASES_TAC(GSYM (SPEC (Term`dsize(D1)`) LESS_0_CASES)) THENL
   [ASM_REWRITE_TAC[NOT_LESS_0, SUB_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
    SUBGOAL_THEN (Term`a:real = b`) (fn th => ASM_REWRITE_TAC[th]) THEN
    MP_TAC(SPECL [Term`D1:num->real`, Term`a:real`,Term`b:real`] DIVISION_EQ)
    THEN RULE_ASSUM_TAC(REWRITE_RULE[tdiv]) THEN ASM_REWRITE_TAC[], ALL_TAC]
  THEN CONJ_TAC THENL
   [ALL_TAC,
    REWRITE_TAC[fine] THEN X_GEN_TAC (Term`n:num`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[tdiv]) THEN
    MP_TAC(SPECL [Term`a:real`, Term`b:real`, Term`c:real`,
                  Term`D1:num->real`, Term`D2:num->real`]
           DIVISION_APPEND_LEMMA2) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_TAC THEN
    ASM_CASES_TAC (Term`SUC n < dsize D1`) THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN (Term`n < dsize D1`) ASSUME_TAC THENL
       [MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (Term`SUC n`) THEN
        ASM_REWRITE_TAC[LESS_SUC_REFL], ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[fine]) THEN
      ASM_REWRITE_TAC[], ALL_TAC] THEN
    ASM_CASES_TAC (Term`n < dsize D1`) THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN (Term`SUC n = dsize D1`) ASSUME_TAC THENL
       [MATCH_MP_TAC LESS_EQUAL_ANTISYM THEN
        ASM_REWRITE_TAC[GSYM NOT_LESS] THEN
        REWRITE_TAC[NOT_LESS] THEN MATCH_MP_TAC LESS_OR THEN
        ASM_REWRITE_TAC[],
        ASM_REWRITE_TAC[SUB_EQUAL_0] THEN
        FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o MATCH_MP DIVISION_LHS o
          CONJUNCT1) THEN
        FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o SYM o
          MATCH_MP DIVISION_RHS o  CONJUNCT1) THEN
        SUBST1_TAC(SYM(ASSUME (Term`SUC n = dsize D1`))) THEN
        FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[fine]) THEN
        ASM_REWRITE_TAC[]],
      ASM_REWRITE_TAC[SUB] THEN UNDISCH_TAC (Term`~(n < (dsize D1))`) THEN
      REWRITE_TAC[LESS_EQ_EXISTS, NOT_LESS] THEN
      DISCH_THEN(X_CHOOSE_THEN (Term`d:num`) SUBST_ALL_TAC) THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[fine]) THEN
      RULE_ASSUM_TAC(ONCE_REWRITE_RULE[ADD_SYM]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[LESS_MONO_ADD_EQ]) THEN
      FIRST_ASSUM ACCEPT_TAC]] THEN
  REWRITE_TAC[tdiv] THEN BETA_TAC THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[tdiv]) THEN
    REWRITE_TAC[DIVISION_THM] THEN CONJ_TAC THENL
     [BETA_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC DIVISION_LHS THEN EXISTS_TAC (Term`b:real`) THEN
      ASM_REWRITE_TAC[], ALL_TAC] THEN
    SUBGOAL_THEN (Term`c = (\n. if n < dsize D1 then D1(n) else D2(n - dsize D1))
                           (dsize D1 + dsize D2)`) SUBST1_TAC THENL
     [BETA_TAC THEN REWRITE_TAC[GSYM NOT_LESS_EQUAL, LESS_EQ_ADD] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC DIVISION_RHS THEN
      EXISTS_TAC (Term`b:real`) THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
    MP_TAC(SPECL [Term`a:real`, Term`b:real`, Term`c:real`,
                  Term`D1:num->real`, Term`D2:num->real`]
            DIVISION_APPEND_LEMMA2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fn th => REWRITE_TAC[th]) THEN
    MATCH_MP_TAC DIVISION_APPEND_LEMMA1 THEN
    MAP_EVERY EXISTS_TAC [Term`a:real`, Term`b:real`, Term`c:real`] THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  X_GEN_TAC (Term`n:num`) THEN RULE_ASSUM_TAC(REWRITE_RULE[tdiv]) THEN
  ASM_CASES_TAC (Term`SUC n < dsize D1`) THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN (Term`n < dsize D1`) ASSUME_TAC THENL
     [MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (Term`SUC n`) THEN
      ASM_REWRITE_TAC[LESS_SUC_REFL], ALL_TAC] THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[SUB] THEN
    FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o MATCH_MP DIVISION_LHS o
      CONJUNCT1) THEN
    FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o SYM o
      MATCH_MP DIVISION_RHS o  CONJUNCT1) THEN
    SUBGOAL_THEN (Term`dsize D1 = SUC n`) (fn th => ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC LESS_EQUAL_ANTISYM THEN
    ASM_REWRITE_TAC[GSYM NOT_LESS] THEN REWRITE_TAC[NOT_LESS] THEN
    MATCH_MP_TAC LESS_OR THEN ASM_REWRITE_TAC[],
    ASM_REWRITE_TAC[SUB]]);

(* ------------------------------------------------------------------------ *)
(* We can always find a division which is fine wrt any gauge                *)
(* ------------------------------------------------------------------------ *)

val DIVISION_EXISTS = store_thm("DIVISION_EXISTS",
 Term `!a b g. a <= b /\ gauge(\x. a <= x /\ x <= b) g
                ==>
                ?D p. tdiv(a,b) (D,p) /\ fine(g) (D,p)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  (MP_TAC o C SPEC BOLZANO_LEMMA)
    (Term `\(u,v). a <= u /\ v <= b
                   ==> ?D p. tdiv(u,v) (D,p) /\ fine(g) (D,p)`) THEN
  CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV) THEN
  W(C SUBGOAL_THEN (fn t => REWRITE_TAC[t]) o
  funpow 2 (fst o dest_imp) o snd) THENL
   [CONJ_TAC,
    DISCH_THEN(MP_TAC o SPECL [Term`a:real`, Term`b:real`]) THEN
    REWRITE_TAC[REAL_LE_REFL]]
  THENL
   [MAP_EVERY X_GEN_TAC [Term`u:real`, Term`v:real`, Term`w:real`] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC DIVISION_APPEND THEN
    EXISTS_TAC (Term`v:real`) THEN CONJ_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (Term`w:real`),
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (Term`u:real`)] THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  X_GEN_TAC (Term`x:real`) THEN ASM_CASES_TAC (Term`a <= x /\ x <= b`) THENL
   [ALL_TAC,
    EXISTS_TAC (Term`&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
    MAP_EVERY X_GEN_TAC [Term`w:real`, Term`y:real`] THEN STRIP_TAC THEN
    CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_neg o concl) THEN
    REWRITE_TAC[DE_MORGAN_THM, REAL_NOT_LE] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [DISJ1_TAC THEN MATCH_MP_TAC REAL_LET_TRANS,
      DISJ2_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS] THEN
    EXISTS_TAC (Term`x:real`) THEN ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC (Term`gauge(\x. a <= x /\ x <= b) g`) THEN
  REWRITE_TAC[gauge] THEN BETA_TAC THEN
  DISCH_THEN(fn th => FIRST_ASSUM(ASSUME_TAC o MATCH_MP th)) THEN
  EXISTS_TAC (Term`(g:real->real) x`) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [Term`w:real`, Term`y:real`] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC (Term`\n:num. if (n = 0) then (w:real) else y`) THEN
  EXISTS_TAC (Term`\n:num. if (n = 0) then (x:real) else y`) THEN
  SUBGOAL_THEN (Term`w <= y`) ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (Term`x:real`) THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[tdiv] THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIVISION_SINGLE THEN FIRST_ASSUM ACCEPT_TAC,
      X_GEN_TAC (Term`n:num`) THEN BETA_TAC THEN REWRITE_TAC[NOT_SUC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]],
    REWRITE_TAC[fine] THEN BETA_TAC THEN REWRITE_TAC[NOT_SUC] THEN
    X_GEN_TAC (Term`n:num`) THEN
    DISJ_CASES_THEN MP_TAC (REWRITE_RULE[REAL_LE_LT] (ASSUME(Term`w <= y`)))
    THENL
     [DISCH_THEN(ASSUME_TAC o MATCH_MP DIVISION_1) THEN
      ASM_REWRITE_TAC[num_CONV (Term`1:num`), LESS_THM, NOT_LESS_0] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[],
      DISCH_THEN(SUBST1_TAC o MATCH_MP DIVISION_0) THEN
      REWRITE_TAC[NOT_LESS_0]]]);

(* ------------------------------------------------------------------------ *)
(* Lemmas about combining gauges                                            *)
(* ------------------------------------------------------------------------ *)

val GAUGE_MIN = store_thm("GAUGE_MIN",
  Term`!E g1 g2. gauge(E) g1 /\ gauge(E) g2 ==>
        gauge(E) (\x. if g1(x) < g2(x) then g1(x) else g2(x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gauge] THEN STRIP_TAC THEN
  X_GEN_TAC (Term`x:real`) THEN BETA_TAC THEN DISCH_TAC THEN
  COND_CASES_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM ACCEPT_TAC);;

val FINE_MIN = store_thm("FINE_MIN",
  Term`!g1 g2 D p.
        fine (\x. if g1(x) < g2(x) then g1(x) else g2(x)) (D,p) ==>
        fine(g1) (D,p) /\ fine(g2) (D,p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fine] THEN
  BETA_TAC THEN DISCH_TAC THEN CONJ_TAC THEN
  X_GEN_TAC (Term`n:num`) THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT]) THEN
    MATCH_MP_TAC REAL_LTE_TRANS,
    MATCH_MP_TAC REAL_LT_TRANS] THEN
  FIRST_ASSUM(fn th => EXISTS_TAC(rand(concl th)) THEN
                   ASM_REWRITE_TAC[] THEN NO_TAC));;

(* ------------------------------------------------------------------------ *)
(* The integral is unique if it exists                                      *)
(* ------------------------------------------------------------------------ *)

val DINT_UNIQ = store_thm("DINT_UNIQ",
 Term`!a b f k1 k2.
        a <= b /\ Dint(a,b) f k1 /\ Dint(a,b) f k2 ==> (k1 = k2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC RAND_CONV [] [GSYM REAL_SUB_0] THEN
  CONV_TAC CONTRAPOS_CONV THEN ONCE_REWRITE_TAC[ABS_NZ] THEN DISCH_TAC THEN
  REWRITE_TAC[Dint] THEN
  DISCH_THEN(CONJUNCTS_THEN(MP_TAC o SPEC (Term`abs(k1 - k2) / &2`))) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`g1:real->real`) STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`g2:real->real`) STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [Term`\x. a <= x /\ x <= b`,
                Term`g1:real->real`, Term`g2:real->real`] GAUGE_MIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [Term`a:real`, Term`b:real`,
                Term`\x:real. if g1(x) < g2(x) then g1(x) else g2(x)`]
         DIVISION_EXISTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`D:num->real`)
     (X_CHOOSE_THEN(Term`p:num->real`) STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FINE_MIN) THEN
  REPEAT(FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPECL [Term`D:num->real`, Term`p:num->real`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
  SUBGOAL_THEN (Term`abs((rsum(D,p) f - k2) - (rsum(D,p) f - k1))
                     < abs(k1 - k2)`) MP_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (Term`abs(rsum(D,p) f - k2) + abs(rsum(D,p) f - k1)`) THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [] [real_sub] THEN
      GEN_REWRITE_TAC (funpow 2 RAND_CONV) [] [GSYM ABS_NEG] THEN
      MATCH_ACCEPT_TAC ABS_TRIANGLE,
      GEN_REWRITE_TAC RAND_CONV [] [GSYM REAL_HALF_DOUBLE] THEN
      MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[]],
    REWRITE_TAC[real_sub, REAL_NEG_ADD, REAL_NEG_SUB] THEN
    ONCE_REWRITE_TAC[AC (REAL_ADD_ASSOC,REAL_ADD_SYM)
      (Term`(a + b) + (c + d) = (d + a) + (c + b)`)] THEN
    REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID, REAL_LT_REFL]]);

(* ------------------------------------------------------------------------ *)
(* Integral over a null interval is 0                                       *)
(* ------------------------------------------------------------------------ *)

val INTEGRAL_NULL = store_thm("INTEGRAL_NULL",
  Term`!f a. Dint(a,a) f (&0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[Dint] THEN GEN_TAC THEN
  DISCH_TAC THEN EXISTS_TAC (Term`\x:real. &1`) THEN
  REWRITE_TAC[gauge, REAL_LT_01] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[tdiv] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIVISION_EQ) THEN
  REWRITE_TAC[rsum] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[sum, REAL_SUB_REFL, ABS_0]);;

(* ------------------------------------------------------------------------ *)
(* Fundamental theorem of calculus (Part I)                                 *)
(* ------------------------------------------------------------------------ *)

val STRADDLE_LEMMA = prove(
 Term
  `!f f' a b e. (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\ &0 < e
    ==> ?g. gauge(\x. a <= x /\ x <= b) g /\
            !x u v. a <= u /\ u <= x /\
                    x <= v /\ v <= b /\ (v - u) < g(x)
                ==> abs((f(v) - f(u)) - (f'(x) * (v - u)))
                    <= e * (v - u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gauge] THEN BETA_TAC THEN
  SUBGOAL_THEN
   (Term`!x. a <= x /\ x <= b ==>
        ?d. &0 < d /\
          !u v. u <= x /\ x <= v /\ (v - u) < d
                ==>
               abs((f(v) - f(u)) - (f'(x) * (v - u)))
               <= e * (v - u)`) MP_TAC THENL
   [ALL_TAC,
    FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN(MP_TAC o CONV_RULE
      ((ONCE_DEPTH_CONV RIGHT_IMP_EXISTS_CONV) THENC SKOLEM_CONV)) THEN
    DISCH_THEN(X_CHOOSE_THEN (Term`g:real->real`) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (Term`g:real->real`) THEN CONJ_TAC THENL
     [GEN_TAC THEN
      DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
      DISCH_THEN(fn th => REWRITE_TAC[th]),
      REPEAT STRIP_TAC THEN
      C SUBGOAL_THEN (fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th))
      (Term`a <= x /\ x <= b`) THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
         [EXISTS_TAC (Term`u:real`), EXISTS_TAC (Term`v:real`)] THEN
        ASM_REWRITE_TAC[],
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]]]] THEN
  X_GEN_TAC (Term`x:real`) THEN
  DISCH_THEN(fn th => STRIP_ASSUME_TAC th THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[diffl, LIM] THEN
  DISCH_THEN(MP_TAC o SPEC (Term`e / &2`)) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
  BETA_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`d:real`) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN (Term`!z. abs(z - x) < d ==>
        abs((f(z) - f(x)) - (f'(x) * (z - x)))
        <= (e / &2) * abs(z - x)`)
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_CASES_TAC (Term`&0 < abs(z - x)`) THENL
     [ALL_TAC,
      UNDISCH_TAC (Term`~(&0 < abs(z - x))`) THEN
      REWRITE_TAC[GSYM ABS_NZ, REAL_SUB_0] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[REAL_SUB_REFL, REAL_MUL_RZERO, ABS_0, REAL_LE_REFL]] THEN
    DISCH_THEN(MP_TAC o CONJ (ASSUME (Term`&0 < abs(z - x)`))) THEN
    DISCH_THEN(curry op THEN (MATCH_MP_TAC REAL_LT_IMP_LE) o MP_TAC) THEN
    DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    FIRST_ASSUM(fn th => GEN_REWRITE_TAC LAND_CONV []
      [GSYM(MATCH_MP REAL_LT_RMUL th)]) THEN
    MATCH_MP_TAC (TAUT_CONV (Term`(a = b) ==> a ==> b`)) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM ABS_MUL] THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_SUB_RDISTRIB] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_SUB_ADD2] THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    ASM_REWRITE_TAC[ABS_NZ], ALL_TAC] THEN
  EXISTS_TAC (Term`d:real`) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN (Term`u <= v`) (DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT])
  THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (Term`x:real`) THEN
    ASM_REWRITE_TAC[],
    ALL_TAC,
    ASM_REWRITE_TAC[REAL_SUB_REFL, REAL_MUL_RZERO, ABS_0, REAL_LE_REFL]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC (Term`abs((f(v) - f(x)) - (f'(x) * (v - x))) +
                   abs((f(x) - f(u)) - (f'(x) * (x - u)))`) THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL[Term`(f(v) - f(x)) - (f'(x) * (v - x))`,
                 Term`(f(x) - f(u)) - (f'(x) * (x - u))`] ABS_TRIANGLE)
    THEN MATCH_MP_TAC(TAUT_CONV (Term`(a = b) ==> a ==> b`)) THEN
    AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[GSYM REAL_ADD2_SUB2] THEN
    REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
    SUBGOAL_THEN (Term`!a b c. (a - b) + (b - c) = (a - c)`)
      (fn th => REWRITE_TAC[th]) THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[real_sub] THEN
    ONCE_REWRITE_TAC[AC (REAL_ADD_ASSOC,REAL_ADD_SYM)
      (Term`(a + b) + (c + d) = (b + c) + (a + d)`)] THEN
    REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID], ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [] [GSYM REAL_HALF_DOUBLE] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (Term`(e / &2) * abs(v - x)`) THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[abs, REAL_SUB_LE] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (Term`v - u`) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_sub, REAL_LE_LADD] THEN
      ASM_REWRITE_TAC[REAL_LE_NEG],
      ASM_REWRITE_TAC[abs, REAL_SUB_LE] THEN REWRITE_TAC[real_div] THEN
      GEN_REWRITE_TAC LAND_CONV [] [AC (REAL_MUL_ASSOC,REAL_MUL_SYM)
         (Term`(a * b) * c = (a * c) * b`)] THEN
     REWRITE_TAC[GSYM REAL_MUL_ASSOC,
        MATCH_MP REAL_LE_LMUL (ASSUME (Term`&0 < e`))] THEN
      SUBGOAL_THEN (Term`!x y. (x * inv(&2)) <= (y * inv(&2)) = x <= y`)
      (fn th => ASM_REWRITE_TAC[th, real_sub, REAL_LE_LADD, REAL_LE_NEG]) THEN
      REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      MATCH_MP_TAC REAL_INV_POS THEN
      REWRITE_TAC[REAL_LT, TWO, LESS_0]],
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (Term`(e / &2) * abs(x - u)`) THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [] [real_sub] THEN
      ONCE_REWRITE_TAC[GSYM ABS_NEG] THEN
      REWRITE_TAC[REAL_NEG_ADD, REAL_NEG_SUB] THEN
      ONCE_REWRITE_TAC[REAL_NEG_RMUL] THEN
      REWRITE_TAC[REAL_NEG_SUB] THEN REWRITE_TAC[GSYM real_sub] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[ABS_SUB] THEN
      ASM_REWRITE_TAC[abs, REAL_SUB_LE] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (Term`v - u`) THEN
      ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[real_sub, REAL_LE_RADD],
      ASM_REWRITE_TAC[abs, REAL_SUB_LE] THEN REWRITE_TAC[real_div] THEN
      GEN_REWRITE_TAC LAND_CONV [] [AC (REAL_MUL_ASSOC,REAL_MUL_SYM)
        (Term `(a * b) * c = (a * c) * b`)] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC,
        MATCH_MP REAL_LE_LMUL (ASSUME (Term`&0 < e`))] THEN
      SUBGOAL_THEN (Term`!x y. (x * inv(&2)) <= (y * inv(&2)) = x <= y`)
      (fn th => ASM_REWRITE_TAC[th, real_sub, REAL_LE_RADD, REAL_LE_NEG]) THEN
      REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      MATCH_MP_TAC REAL_INV_POS THEN
      REWRITE_TAC[REAL_LT, TWO, LESS_0]]]);

val FTC1 = store_thm("FTC1",
 Term `!f f' a b.
       a <= b /\ (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x))
        ==> Dint(a,b) f' (f(b) - f(a))`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC (Term`a <= b`) THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [ALL_TAC, ASM_REWRITE_TAC[REAL_SUB_REFL, INTEGRAL_NULL]] THEN
  REWRITE_TAC[Dint] THEN X_GEN_TAC (Term`e:real`) THEN DISCH_TAC THEN
  SUBGOAL_THEN
    (Term`!e. &0 < e ==>
              ?g. gauge(\x. a <= x /\ x <= b) g /\
                  (!D p. tdiv(a,b)(D,p) /\ fine g(D,p)
                         ==>
                         (abs((rsum(D,p)f') - (f b - f a))) <= e)`)
  MP_TAC THENL
   [ALL_TAC,
    DISCH_THEN(MP_TAC o SPEC (Term`e / &2`)) THEN
    ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
    DISCH_THEN(X_CHOOSE_THEN (Term`g:real->real`) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (Term`g:real->real`) THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(fn th => FIRST_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (Term`e / &2`) THEN
    ASM_REWRITE_TAC[REAL_LT_HALF2]] THEN
  UNDISCH_TAC (Term`&0 < e`) THEN DISCH_THEN(K ALL_TAC) THEN
  X_GEN_TAC (Term`e:real`) THEN DISCH_TAC THEN
  MP_TAC(SPECL [Term`f:real->real`, Term`f':real->real`,
    Term`a:real`, Term`b:real`, Term`e / (b - a)`] STRADDLE_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (Term`&0 < e / (b - a)`) (fn th => REWRITE_TAC[th]) THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INV_POS THEN
    ASM_REWRITE_TAC[REAL_SUB_LT], ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`g:real->real`) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (Term`g:real->real`) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [Term`D:num->real`, Term`p:num->real`] THEN
  REWRITE_TAC[tdiv] THEN STRIP_TAC THEN REWRITE_TAC[rsum] THEN
  SUBGOAL_THEN (Term`f b - f a = sum(0,dsize D)(\n. f(D(SUC n)) - f(D(n)))`)
  SUBST1_TAC THENL
   [MP_TAC(SPECL [Term`\n:num. (f:real->real)(D(n))`, Term`0:num`, Term`dsize D`]
      SUM_CANCEL) THEN BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    MAP_EVERY (IMP_RES_THEN SUBST1_TAC) [DIVISION_LHS, DIVISION_RHS] THEN
    REFL_TAC, ALL_TAC] THEN
  ONCE_REWRITE_TAC[ABS_SUB] THEN REWRITE_TAC[GSYM SUM_SUB] THEN BETA_TAC THEN
  LE_MATCH_TAC ABS_SUM THEN BETA_TAC THEN
  SUBGOAL_THEN (Term`e = sum(0,dsize D)
                            (\n. (e / (b - a)) * (D(SUC n) - D n))`)
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[SYM(BETA_CONV (Term`(\n. (D(SUC n) - D n)) n`))] THEN
    ASM_REWRITE_TAC[SUM_CMUL, SUM_CANCEL, ADD_CLAUSES] THEN
    MAP_EVERY (IMP_RES_THEN SUBST1_TAC) [DIVISION_LHS, DIVISION_RHS] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    REWRITE_TAC[REAL_SUB_0] THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
  MATCH_MP_TAC SUM_LE THEN X_GEN_TAC (Term`r:num`) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN BETA_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [IMP_RES_THEN (fn th => REWRITE_TAC[th]) DIVISION_LBOUND,
    IMP_RES_THEN (fn th => REWRITE_TAC[th]) DIVISION_UBOUND,
    UNDISCH_TAC (Term`fine(g)(D,p)`) THEN REWRITE_TAC[fine] THEN
    DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);

(* ======================================================================== *)
(* MacLaurin's theorem.                                                     *)
(* ======================================================================== *)

(* ------------------------------------------------------------------------ *)
(* SYM_CANON_CONV - Canonicalizes single application of symmetric operator  *)
(* Rewrites `so as to make fn true`, e.g. fn = (<<) or fn = curry(=) `1` o fst*)
(* ------------------------------------------------------------------------ *)

fun SYM_CANON_CONV sym f =
  REWR_CONV sym o assert
   (not o f o ((snd o dest_comb) ## I) o dest_comb);;

(* ----------------------------------------------------------- *)
(* EXT_CONV `!x. f x = g x` = |- (!x. f x = g x) = (f = g)     *)
(* ----------------------------------------------------------- *)

val EXT_CONV =  SYM o uncurry X_FUN_EQ_CONV o
      (I ## (mk_eq o (rator ## rator) o dest_eq)) o dest_forall;;

(* ======================================================================== *)
(* Mclaurin's theorem with Lagrange form of remainder                       *)
(* We could weaken the hypotheses slightly, but it's not worth it           *)
(* ======================================================================== *)

val _ = Parse.hide "B";

val MCLAURIN = store_thm("MCLAURIN",
 Term
  `!f diff h n.
    &0 < h /\ 0 < n /\ (diff(0) = f) /\
    (!m t. m < n /\ &0 <= t /\ t <= h ==>
           (diff(m) diffl diff(SUC m)(t))(t)) ==>
   (?t. &0 < t /\ t < h /\
        (f(h) = sum(0,n)(\m. (diff(m)(&0) / &(FACT m)) * (h pow m))
                +
                ((diff(n)(t) / &(FACT n)) * (h pow n))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC (Term`0 < n:num`) THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN (Term`r:num`) MP_TAC)
   (SPEC (Term`n:num`) num_CASES) THEN REWRITE_TAC[LESS_REFL] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN
   (Term`?B. f(h) = sum(0,n)
                       (\m. (diff(m)(&0) / &(FACT m)) * (h pow m))
                    + (B * ((h pow n) / &(FACT n)))`) MP_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EQ_SUB_RADD] THEN
    EXISTS_TAC (Term
       `(f h - sum(0,n) (\m. (diff(m)(&0) / &(FACT m)) * (h pow m)))
        * &(FACT n) / (h pow n)`) THEN REWRITE_TAC[real_div] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [] [GSYM REAL_MUL_RID] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    ONCE_REWRITE_TAC[AC (REAL_MUL_ASSOC,REAL_MUL_SYM)
        (Term`a * (b * (c * d)) = (d * a) * (b * c)`)] THEN
    GEN_REWRITE_TAC RAND_CONV [] [GSYM REAL_MUL_LID] THEN BINOP_TAC THEN
    MATCH_MP_TAC REAL_MUL_LINV THENL
     [MATCH_MP_TAC REAL_POS_NZ THEN REWRITE_TAC[REAL_LT, FACT_LESS],
      MATCH_MP_TAC POW_NZ THEN MATCH_MP_TAC REAL_POS_NZ THEN
      ASM_REWRITE_TAC[]], ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`B:real`) (ASSUME_TAC o SYM)) THEN
  ABBREV_TAC (Term`g =
   \t. f(t) - (sum(0,n)(\m. (diff(m)(&0) / &(FACT m)) * (t pow m))
                + (B * ((t pow n) / &(FACT n))))`) THEN
  SUBGOAL_THEN (Term`(g(&0) = &0) /\ (g(h) = &0)`) ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN BETA_TAC THEN ASM_REWRITE_TAC[REAL_SUB_REFL] THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[POW_0, REAL_DIV_LZERO] THEN
    REWRITE_TAC[REAL_MUL_RZERO, REAL_ADD_RID] THEN REWRITE_TAC[REAL_SUB_0] THEN
    MP_TAC(GEN (Term`j:num->real`)
     (SPECL [Term`j:num->real`, Term`r:num`, Term`1:num`] SUM_OFFSET)) THEN
    REWRITE_TAC[ADD1, REAL_EQ_SUB_LADD] THEN
    DISCH_THEN(fn th => REWRITE_TAC[GSYM th]) THEN BETA_TAC THEN
    REWRITE_TAC[SUM_1] THEN BETA_TAC THEN REWRITE_TAC[pow, FACT] THEN
    ASM_REWRITE_TAC[real_div, REAL_INV1, REAL_MUL_RID] THEN
    CONV_TAC SYM_CONV THEN REWRITE_TAC[REAL_ADD_LID_UNIQ] THEN
    REWRITE_TAC[GSYM ADD1, POW_0, REAL_MUL_RZERO, SUM_0], ALL_TAC] THEN
  ABBREV_TAC (Term`difg =
    \m t. diff(m) t - (sum(0,n-m)(\p. (diff(m+p)(&0) / &(FACT p)) * (t pow p))
       + (B * ((t pow (n - m)) / &(FACT(n - m)))))`) THEN
  SUBGOAL_THEN (Term`difg(0:num):real->real = g`) ASSUME_TAC THENL
   [EXPAND_TAC "difg" THEN BETA_TAC THEN EXPAND_TAC "g" THEN
    CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES, SUB_0], ALL_TAC] THEN
  SUBGOAL_THEN (Term
     `(!m t. m < n /\ (& 0) <= t /\ t <= h
              ==> (difg(m) diffl difg(SUC m)(t))(t))`) ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "difg" THEN BETA_TAC THEN
    CONV_TAC((funpow 2 RATOR_CONV o RAND_CONV) HABS_CONV) THEN
    MATCH_MP_TAC DIFF_SUB THEN CONJ_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
    CONV_TAC((funpow 2 RATOR_CONV o RAND_CONV) HABS_CONV) THEN
    MATCH_MP_TAC DIFF_ADD THEN CONJ_TAC THENL
     [ALL_TAC,
      W(MP_TAC o DIFF_CONV o rand o funpow 2 rator o snd) THEN
      REWRITE_TAC[REAL_MUL_LZERO, REAL_MUL_RID, REAL_ADD_LID] THEN
      REWRITE_TAC[REAL_FACT_NZ, REAL_SUB_RZERO] THEN
      DISCH_THEN(MP_TAC o SPEC (Term`t:real`)) THEN
      MATCH_MP_TAC(TAUT_CONV (Term`(a = b) ==> a ==> b`)) THEN
      AP_THM_TAC THEN CONV_TAC(ONCE_DEPTH_CONV(ALPHA_CONV (Term`t:real`))) THEN
      AP_TERM_TAC THEN GEN_REWRITE_TAC RAND_CONV [] [REAL_MUL_SYM] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC, POW_2] THEN
      ONCE_REWRITE_TAC[AC (REAL_MUL_ASSOC,REAL_MUL_SYM)
        (Term`a * (b * (c * d)) = b * (a * (d * c))`)] THEN
      FIRST_ASSUM(X_CHOOSE_THEN (Term`d:num`) SUBST1_TAC o
        MATCH_MP LESS_ADD_1 o CONJUNCT1) THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] (GSYM ADD1)] THEN
      REWRITE_TAC[ADD_SUB] THEN AP_TERM_TAC THEN
      (IMP_SUBST_TAC REAL_INV_MUL:tactic) THEN REWRITE_TAC[REAL_FACT_NZ] THEN
      REWRITE_TAC[GSYM ADD1, FACT, GSYM REAL_MUL] THEN
      REPEAT(IMP_SUBST_TAC REAL_INV_MUL THEN
             REWRITE_TAC[REAL_FACT_NZ] THEN
             REWRITE_TAC [REAL_INJ, NOT_SUC]) THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      ONCE_REWRITE_TAC[AC (REAL_MUL_ASSOC,REAL_MUL_SYM)
       (Term `a * (b * (c * (d * (e * (f * g))))) =
              (b * a) * ((d * f) * ((c * g) * e))`)] THEN
      REPEAT(IMP_SUBST_TAC REAL_MUL_LINV THEN REWRITE_TAC[REAL_FACT_NZ] THEN
             REWRITE_TAC[REAL_INJ, NOT_SUC]) THEN
      REWRITE_TAC[REAL_MUL_LID]] THEN
    FIRST_ASSUM(X_CHOOSE_THEN (Term`d:num`) SUBST1_TAC o
        MATCH_MP LESS_ADD_1 o CONJUNCT1) THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] (GSYM ADD1)] THEN
    REWRITE_TAC[ADD_SUB] THEN
    REWRITE_TAC[GSYM(REWRITE_RULE[REAL_EQ_SUB_LADD] SUM_OFFSET)] THEN
    BETA_TAC THEN REWRITE_TAC[SUM_1] THEN BETA_TAC THEN
    CONV_TAC (funpow 2 RATOR_CONV (RAND_CONV HABS_CONV)) THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [] [GSYM REAL_ADD_RID] THEN
    MATCH_MP_TAC DIFF_ADD THEN REWRITE_TAC[pow, DIFF_CONST] THEN
    (MP_TAC o C SPECL DIFF_SUM)
     [Term`\p x. (diff((p + 1) + m)(&0) / &(FACT(p + 1)))
                * (x pow (p + 1))`,
      Term`\p x. (diff(p + (SUC m))(&0) / &(FACT p)) * (x pow p)`,
      Term`0:num`, Term`d:num`, Term`t:real`] THEN BETA_TAC THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
    X_GEN_TAC (Term`k:num`) THEN STRIP_TAC THEN
    W(MP_TAC o DIFF_CONV o rand o funpow 2 rator o snd) THEN
    DISCH_THEN(MP_TAC o SPEC (Term`t:real`)) THEN
    MATCH_MP_TAC(TAUT_CONV (Term`(a = b) ==> a ==> b`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV(ALPHA_CONV (Term`z:real`))) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_MUL_LZERO, REAL_ADD_LID, REAL_MUL_RID] THEN
    REWRITE_TAC[GSYM ADD1, ADD_CLAUSES, real_div, GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[SUC_SUB1] THEN
    ONCE_REWRITE_TAC[AC (REAL_MUL_ASSOC,REAL_MUL_SYM)
       (Term`a * (b * (c * d)) = c * ((a * d) * b)`)] THEN
    AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN (Term`&(SUC k) = inv(inv(&(SUC k)))`) SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INVINV THEN
      REWRITE_TAC[REAL_INJ, NOT_SUC], ALL_TAC] THEN
    (IMP_SUBST_TAC(GSYM REAL_INV_MUL):tactic) THENL
     [CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN REWRITE_TAC[REAL_FACT_NZ] THEN
      MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_INV_POS THEN
      REWRITE_TAC[REAL_LT, LESS_0], ALL_TAC] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FACT, GSYM REAL_MUL, REAL_MUL_ASSOC] THEN
    (IMP_SUBST_TAC REAL_MUL_LINV:tactic) THEN REWRITE_TAC[REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_INJ, NOT_SUC], ALL_TAC] THEN
  SUBGOAL_THEN (Term`!m. m < n ==>
        ?t. &0 < t /\ t < h /\ (difg(SUC m)(t) = &0)`) MP_TAC THENL
   [ALL_TAC,
    DISCH_THEN(MP_TAC o SPEC (Term`r:num`)) THEN EXPAND_TAC "n" THEN
    REWRITE_TAC[LESS_SUC_REFL] THEN
    DISCH_THEN(X_CHOOSE_THEN (Term`t:real`) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (Term`t:real`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC (Term`difg(SUC r)(t:real) = &0`) THEN EXPAND_TAC "difg" THEN
    ASM_REWRITE_TAC[SUB_EQUAL_0, sum, pow, FACT] THEN
    REWRITE_TAC[REAL_SUB_0, REAL_ADD_LID, real_div] THEN
    REWRITE_TAC[REAL_INV1, REAL_MUL_RID] THEN DISCH_THEN SUBST1_TAC THEN
    GEN_REWRITE_TAC (funpow 2 RAND_CONV) []
     [AC (REAL_MUL_ASSOC,REAL_MUL_SYM)
         (Term`(a * b) * c = a * (c * b)`)] THEN
    ASM_REWRITE_TAC[GSYM real_div]] THEN
  SUBGOAL_THEN (Term`!m:num. m<n ==> (difg(m)(&0) = &0)`) ASSUME_TAC THENL
   [X_GEN_TAC (Term`m:num`) THEN EXPAND_TAC "difg" THEN
    DISCH_THEN(X_CHOOSE_THEN (Term`d:num`) SUBST1_TAC o MATCH_MP LESS_ADD_1)
    THEN ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
    MP_TAC(GEN (Term`j:num->real`)
     (SPECL [Term`j:num->real`, Term`d:num`, Term`1:num`] SUM_OFFSET)) THEN
    REWRITE_TAC[ADD1, REAL_EQ_SUB_LADD] THEN
    DISCH_THEN(fn th => REWRITE_TAC[GSYM th]) THEN BETA_TAC THEN
    REWRITE_TAC[SUM_1] THEN BETA_TAC THEN
    REWRITE_TAC[FACT, pow, REAL_INV1, ADD_CLAUSES, real_div, REAL_MUL_RID] THEN
    REWRITE_TAC[GSYM ADD1, POW_0, REAL_MUL_RZERO, SUM_0, REAL_ADD_LID] THEN
    REWRITE_TAC[REAL_MUL_LZERO, REAL_MUL_RZERO,REAL_ADD_RID] THEN
    REWRITE_TAC[REAL_SUB_REFL], ALL_TAC] THEN
  SUBGOAL_THEN (Term`!m:num. m < n ==> ?t. &0 < t /\ t < h /\
                        (difg(m) diffl &0)(t)`) MP_TAC THENL
   [ALL_TAC,
    DISCH_THEN(fn th => GEN_TAC THEN
      DISCH_THEN(fn t => ASSUME_TAC t THEN MP_TAC(MATCH_MP th t))) THEN
    DISCH_THEN(X_CHOOSE_THEN (Term`t:real`) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (Term`t:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DIFF_UNIQ THEN EXISTS_TAC (Term`difg(m:num):real->real`) THEN
    EXISTS_TAC (Term`t:real`) THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_ASSUM ACCEPT_TAC] THEN
  INDUCT_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC ROLLE THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN (Term`!t. &0 <= t /\ t <= h ==> g differentiable t`)
    MP_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[differentiable] THEN
      EXISTS_TAC (Term`difg(SUC 0)(t:real):real`) THEN
      SUBST1_TAC(SYM(ASSUME (Term`difg(0:num):real->real = g`))) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC DIFF_CONT THEN
      REWRITE_TAC[GSYM differentiable] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[],
      GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]],
    DISCH_TAC THEN SUBGOAL_THEN (Term`m < n:num`)
    (fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THENL
     [MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (Term`SUC m`) THEN
      ASM_REWRITE_TAC[LESS_SUC_REFL], ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN (Term`t0:real`) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (Term`?t. (& 0) < t /\ t < t0 /\
                           ((difg(SUC m)) diffl (& 0))t`) MP_TAC THENL
     [MATCH_MP_TAC ROLLE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [SUBGOAL_THEN (Term`difg(SUC m)(&0) = &0`) SUBST1_TAC THENL
         [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC,
          MATCH_MP_TAC DIFF_UNIQ THEN EXISTS_TAC (Term`difg(m:num):real->real`)
          THEN EXISTS_TAC (Term`t0:real`) THEN ASM_REWRITE_TAC[] THEN
          FIRST_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (Term`SUC m`) THEN
            ASM_REWRITE_TAC[LESS_SUC_REFL],
            MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
            MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]]], ALL_TAC] THEN
      SUBGOAL_THEN (Term`!t. &0 <= t /\ t <= t0 ==>
                       difg(SUC m) differentiable t`) ASSUME_TAC THENL
       [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[differentiable] THEN
        EXISTS_TAC (Term`difg(SUC(SUC m))(t:real):real`) THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (Term`t0:real`) THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
      CONJ_TAC THENL
       [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC DIFF_CONT THEN
        REWRITE_TAC[GSYM differentiable] THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[],
        GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
        CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]],
      DISCH_THEN(X_CHOOSE_THEN (Term`t:real`) STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (Term`t:real`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (Term`t0:real`) THEN
      ASM_REWRITE_TAC[]]]);

val MCLAURIN_NEG = store_thm("MCLAURIN_NEG",
 Term `!f diff h n.
    h < &0 /\ 0<n /\ (diff(0) = f) /\
    (!m t. m < n /\ h <= t /\ t <= &0 ==>
           (diff(m) diffl diff(SUC m)(t))(t)) ==>
   (?t. h < t /\ t < &0 /\
        (f(h) = sum(0,n)(\m. (diff(m)(&0) / &(FACT m)) * (h pow m))
                + ((diff(n)(t) / &(FACT n)) * (h pow n))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL[Term`\x. (f(~x):real)`,
               Term`\n x. ((~(&1)) pow n) * (diff:num->real->real)(n)(~x)`,
               Term`~h`, Term`n:num`] MCLAURIN) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[REAL_NEG_GT0, pow, REAL_MUL_LID] THEN
  ONCE_REWRITE_TAC[GSYM REAL_LE_NEG] THEN
  REWRITE_TAC[REAL_NEGNEG, REAL_NEG_0] THEN
  ONCE_REWRITE_TAC[TAUT_CONV (Term`a /\ b /\ c = a /\ c /\ b`)] THEN
  W(C SUBGOAL_THEN (fn t => REWRITE_TAC[t]) o funpow 2 (fst o dest_imp) o snd)
  THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(MP_TAC o
     C CONJ (SPEC (Term`t:real`) (DIFF_CONV (Term`\x. ~x`)))) THEN
    CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_CHAIN) THEN
    DISCH_THEN(MP_TAC o GEN_ALL o MATCH_MP DIFF_CMUL) THEN
    DISCH_THEN(MP_TAC o SPEC (Term`(~(&1)) pow m`)) THEN BETA_TAC THEN
    MATCH_MP_TAC(TAUT_CONV (Term`(a = b) ==> a ==> b`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV(ALPHA_CONV (Term`z:real`))) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC(AC_CONV (REAL_MUL_ASSOC,REAL_MUL_SYM)),
    DISCH_THEN(X_CHOOSE_THEN (Term`t:real`) STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC (Term`~t`) THEN ONCE_REWRITE_TAC[GSYM REAL_LT_NEG] THEN
  ASM_REWRITE_TAC[REAL_NEGNEG, REAL_NEG_0] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC (Term`m:num`) THEN REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN BETA_TAC, ALL_TAC] THEN
  REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[AC (REAL_MUL_ASSOC,REAL_MUL_SYM)
    (Term`a * (b * (c * d)) = (b * c) * (a * d)`)] THEN
  REWRITE_TAC[GSYM POW_MUL, GSYM REAL_NEG_MINUS1, REAL_NEGNEG] THEN
  REWRITE_TAC[REAL_MUL_ASSOC]);

(* ------------------------------------------------------------------------- *)
(* Simple strong form if a function is differentiable everywhere.            *)
(* ------------------------------------------------------------------------- *)

val MCLAURIN_ALL_LT = store_thm("MCLAURIN_ALL_LT",
 Term`!f diff.
      (diff 0 = f) /\
      (!m x. ((diff m) diffl (diff(SUC m) x)) x)
      ==> !x n. ~(x = &0) /\ 0 < n
            ==> ?t. &0 < abs(t) /\ abs(t) < abs(x) /\
                    (f(x) = sum(0,n)
                                (\m. (diff m (&0) / &(FACT m)) * x pow m)
                            +
                            (diff n t / &(FACT n)) * x pow n)`,
  REPEAT STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN MP_TAC
   (SPECL [Term`x:real`, Term`&0`] REAL_LT_TOTAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [MP_TAC(SPECL [Term`f:real->real`, Term`diff:num->real->real`,
                  Term`x:real`, Term`n:num`] MCLAURIN_NEG) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN (Term`t:real`) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (Term`t:real`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC (Term`t < &0`) THEN UNDISCH_TAC (Term`x < t`)
    THEN REAL_ARITH_TAC,
    MP_TAC(SPECL [Term`f:real->real`, Term`diff:num->real->real`,
                  Term`x:real`, Term`n:num`] MCLAURIN) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN (Term`t:real`) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (Term`t:real`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC (Term`&0 < t`) THEN UNDISCH_TAC (Term`t < x`)
    THEN REAL_ARITH_TAC]);

val MCLAURIN_ZERO = store_thm("MCLAURIN_ZERO",
 Term`!diff n x. (x = &0) /\ 0 < n
       ==>
       (sum(0,n) (\m. (diff m (&0) / &(FACT m)) * x pow m)
        =
       diff 0 (&0))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
  SPEC_TAC(Term`n:num`,Term`n:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[LESS_REFL] THEN REWRITE_TAC[LESS_THM] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (SUBST1_TAC o SYM) MP_TAC) THENL
   [REWRITE_TAC[sum, ADD_CLAUSES] THEN BETA_TAC THEN
    REWRITE_TAC[FACT, pow, real_div] THEN MP_TAC(SPEC(Term`&1`) REAL_DIV_REFL)
    THEN DISCH_THEN (MP_TAC o REWRITE_RULE
        [REAL_OF_NUM_EQ,ONE,NOT_SUC])
    THEN REWRITE_TAC [GSYM REAL_INV_1OVER,  GSYM (ONE)]
    THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_ADD_LID, REAL_MUL_RID],
    REWRITE_TAC[sum] THEN
    DISCH_THEN(fn th => ASSUME_TAC th THEN ANTE_RES_THEN SUBST1_TAC th) THEN
    UNDISCH_TAC (Term`0 < n:num`) THEN SPEC_TAC(Term`n:num`,Term`n:num`) THEN
    INDUCT_TAC THEN BETA_TAC THEN REWRITE_TAC[LESS_REFL] THEN
    REWRITE_TAC[ADD_CLAUSES, pow, REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
    REWRITE_TAC[REAL_ADD_RID]]);



val LET_CASES = prove(Term`!m n:num. m <= n \/ n < m`,
ONCE_REWRITE_TAC [DISJ_SYM] THEN MATCH_ACCEPT_TAC LESS_CASES);

val REAL_POW_EQ_0 = prove
 (Term`!x n. (x pow n = &0) = (x = &0) /\ ~(n = 0)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[NOT_SUC, pow, REAL_ENTIRE] THENL
   [REWRITE_TAC [REAL_OF_NUM_EQ, ONE,NOT_SUC],
    EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]);

val MCLAURIN_ALL_LE = store_thm("MCLAURIN_ALL_LE",
 Term`!f diff.
      (diff 0 = f) /\
      (!m x. ((diff m) diffl (diff(SUC m) x)) x)
      ==> !x n. ?t. abs t  <= abs x /\
                   (f(x) = sum(0,n)
                             (\m. (diff m (&0) / &(FACT m)) * x pow m)
                           +
                            (diff n t / &(FACT n)) * x pow n)`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_THEN MP_TAC(SPECL [Term`n:num`, Term`0:num`] LET_CASES) THENL
   [REWRITE_TAC[LE] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[sum, REAL_ADD_LID, FACT] THEN EXISTS_TAC (Term`x:real`)
    THEN REWRITE_TAC[REAL_LE_REFL, pow, REAL_MUL_RID, REAL_OVER1],
    DISCH_TAC THEN ASM_CASES_TAC (Term`x = &0`) THENL
     [MP_TAC(SPEC_ALL MCLAURIN_ZERO) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN EXISTS_TAC (Term`&0`) THEN
      REWRITE_TAC[REAL_LE_REFL] THEN
      SUBGOAL_THEN (Term`&0 pow n = &0`) SUBST1_TAC THENL
       [ASM_REWRITE_TAC[REAL_POW_EQ_0, GSYM (CONJUNCT1 LE), NOT_LESS_EQUAL],
        REWRITE_TAC[REAL_ADD_RID, REAL_MUL_RZERO]],
      MP_TAC(SPEC_ALL MCLAURIN_ALL_LT) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC_ALL) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN (Term`t:real`) STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (Term`t:real`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]]]);


(* ------------------------------------------------------------------------- *)
(* Version for exp.                                                          *)
(* ------------------------------------------------------------------------- *)

val MCLAURIN_EXP_LEMMA = prove
 (Term`((\n:num. exp) 0 = exp) /\
   (!m x. (((\n:num. exp) m) diffl ((\n:num. exp) (SUC m) x)) x)`,
  REWRITE_TAC[DIFF_EXP]);

val MCLAURIN_EXP_LT = store_thm("MCLAURIN_EXP_LT",
 Term`!x n. ~(x = &0) /\ 0 < n
         ==> ?t. &0 < abs(t) /\
                 abs(t) < abs(x) /\
                 (exp(x) = sum(0,n)(\m. x pow m / &(FACT m)) +
                           (exp(t) / &(FACT n)) * x pow n)`,
  MP_TAC (MATCH_MP MCLAURIN_ALL_LT MCLAURIN_EXP_LEMMA) THEN BETA_TAC THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN
  EXISTS_TAC (Term`t:real`) THEN
  ASM_REWRITE_TAC [EXP_0,real_div,REAL_MUL_LID,REAL_MUL_RID]
  THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC FUN_EQ_CONV
  THEN GEN_TAC THEN BETA_TAC THEN GEN_REWRITE_TAC LAND_CONV [] [REAL_MUL_SYM]
  THEN REFL_TAC);

val MCLAURIN_EXP_LE = store_thm("MCLAURIN_EXP_LE",
 Term`!x n. ?t. abs(t) <= abs(x) /\
             (exp(x) = sum(0,n)(\m. x pow m / &(FACT m)) +
                       (exp(t) / &(FACT n)) * x pow n)`,
  MP_TAC (MATCH_MP MCLAURIN_ALL_LE MCLAURIN_EXP_LEMMA) THEN
  DISCH_THEN (fn th => REPEAT GEN_TAC THEN STRIP_ASSUME_TAC (SPEC_ALL th))
  THEN EXISTS_TAC (Term`t:real`) THEN  ASM_REWRITE_TAC [] THEN
  AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN CONV_TAC FUN_EQ_CONV
  THEN GEN_TAC THEN BETA_TAC THEN
  REWRITE_TAC[EXP_0, real_div, REAL_MUL_LID, REAL_MUL_RID] THEN
  GEN_REWRITE_TAC LAND_CONV [] [REAL_MUL_SYM] THEN REFL_TAC);

(* ------------------------------------------------------------------------- *)
(* Version for ln(1 - x).                                                    *)
(* ------------------------------------------------------------------------- *)

val DIFF_LN_COMPOSITE = store_thm("DIFF_LN_COMPOSITE",
 Term`!g m x. (g diffl m)(x) /\ &0 < g x
           ==> ((\x. ln(g x)) diffl (inv(g x) * m))(x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFF_CHAIN THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIFF_LN THEN
  ASM_REWRITE_TAC[]);

val _ = basic_diffs := !basic_diffs@[SPEC_ALL DIFF_LN_COMPOSITE];

val lem = prove(Term`!n:num. 0 < n ==> ~(n=0)`,
INDUCT_TAC THEN ASM_REWRITE_TAC [NOT_SUC,NOT_LESS_0]);

(*
val MCLAURIN_LN_POS = store_thm("MCLAURIN_LN_POS",
 Term`!x n.
     &0 < x /\ 0 < n
     ==> ?t. &0 < t /\
             t < x  /\
             (ln(&1 + x)
              = sum(0,n) (\m. ~(&1) pow (SUC m) * (x pow m) / &m)
                +
               ~(&1) pow (SUC n) * x pow n / (&n * (&1 + t) pow n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC (Term`\x. ln(&1 + x)`) MCLAURIN) THEN
  DISCH_THEN(MP_TAC o SPEC
    (Term`\n x. (n=0) => ln(&1 + x)
                      |  ~(&1) pow (SUC n)
                         *  &(FACT(PRE n)) * inv((&1 + x) pow n)`)) THEN
  DISCH_THEN(MP_TAC o SPECL [Term`x:real`, Term`n:num`]) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NOT_SUC, REAL_ADD_RID, POW_ONE, LN_1, REAL_INV1,REAL_MUL_RID] THEN
  SUBGOAL_THEN (Term`~(n = 0)`) ASSUME_TAC THENL
   [IMP_RES_TAC lem, ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN (Term`!p. ~(p = 0) ==> (&(FACT(PRE p)) / &(FACT p) = inv(&p))`)
  ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[NOT_SUC, PRE] THEN
    REWRITE_TAC[real_div, FACT, GSYM REAL_OF_NUM_MUL] THEN
    SUBGOAL_THEN (Term `~(& (SUC p) = &0) /\ ~(& (FACT p) = &0)`)
     (fn th => REWRITE_TAC [MATCH_MP REAL_INV_MUL th]) THENL
    [REWRITE_TAC[REAL_OF_NUM_EQ,NOT_SUC] THEN MATCH_MP_TAC lem THEN
     MATCH_ACCEPT_TAC FACT_LESS,
     ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
     GEN_REWRITE_TAC RAND_CONV [] [GSYM REAL_MUL_RID] THEN
     REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
     AP_TERM_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN
     REWRITE_TAC[REAL_OF_NUM_EQ] THEN MATCH_MP_TAC lem THEN
     MATCH_ACCEPT_TAC FACT_LESS], ALL_TAC] THEN
  SUBGOAL_THEN (Term
   `!p. (p = 0 => &0 | ~(&1) pow (SUC p) * &(FACT (PRE p)))
         / &(FACT p)
         =
        ~(&1) pow (SUC p) * inv(&p)`)
   (fn th => REWRITE_TAC[th]) THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[REAL_INV_0, real_div, REAL_MUL_LZERO, REAL_MUL_RZERO],
      REWRITE_TAC[NOT_SUC] THEN
      REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM real_div] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[NOT_SUC]], ALL_TAC] THEN
  SUBGOAL_THEN (Term -- what does this parse to???
    `!t. ((~(&1) pow (SUC n) * &(FACT(PRE n)) * inv ((&1 + t) pow n))
          / &(FACT n)) * x pow n
        =
         ~(&1) pow (SUC n) * x pow n / (&n * (&1 + t) pow n)`)
   (fn th => REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN
    AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC LAND_CONV [] [REAL_MUL_SYM] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN (Term`~(& n = &0) /\ ~((& 1 + t) pow n = &0)`)
      (fn th => REWRITE_TAC [MATCH_MP REAL_INV_MUL th]) THENL
    [CONJ_TAC THENL
      [REWRITE_TAC [REAL_OF_NUM_EQ] THEN IMP_RES_TAC lem,
       MATCH_MP_TAC POW_NZ THEN REWRITE_TAC [REAL_OF_NUM_EQ]
    ,GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  REWRITE_TAC[real_div, REAL_MUL_AC] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `m:num` THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[] THENL
   [W(MP_TAC o SPEC `u:real` o DIFF_CONV o lhand o rator o snd) THEN
    REWRITE_TAC[PRE, real_pow, REAL_ADD_LID, REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_MUL_RNEG, REAL_MUL_LNEG, REAL_MUL_RID] THEN
    REWRITE_TAC[FACT, REAL_MUL_RID, REAL_NEG_NEG] THEN
    DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC `&0 <= u` THEN REAL_ARITH_TAC,
    W(MP_TAC o SPEC `u:real` o DIFF_CONV o lhand o rator o snd) THEN
    SUBGOAL_THEN `~((&1 + u) pow m = &0)` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 <= u` THEN REAL_ARITH_TAC,
      MATCH_MP_TAC (TAUT `(a = b) ==> a ==> b`) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[REAL_MUL_LZERO, REAL_ADD_RID] THEN
      REWRITE_TAC[REAL_ADD_LID, REAL_MUL_RID] THEN
      REWRITE_TAC[real_div, real_pow, REAL_MUL_LNEG, REAL_MUL_RNEG] THEN
      REWRITE_TAC[REAL_NEG_NEG, REAL_MUL_RID, REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `~(m = 0)` THEN SPEC_TAC(`m:num`,`p:num`) THEN
      INDUCT_TAC THEN REWRITE_TAC[NOT_SUC] THEN
      REWRITE_TAC[SUC_SUB1, PRE] THEN REWRITE_TAC[FACT] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
      REWRITE_TAC[real_pow, REAL_POW_2] THEN REWRITE_TAC[REAL_INV_MUL] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN
      REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[DE_MORGAN_THM] THEN DISJ1_TAC THEN
      UNDISCH_TAC `&0 <= u` THEN REAL_ARITH_TAC]]),,

let MCLAURIN_LN_NEG = prove
 (`!x n. &0 < x /\ x < &1 /\ 0 < n
         ==> ?t. &0 < t /\
                 t < x /\
                 (--(ln(&1 - x)) = Sum(0,n) (\m. (x pow m) / &m) +
                                    x pow n / (&n * (&1 - t) pow n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `\x. --(ln(&1 - x))` MCLAURIN) THEN
  DISCH_THEN(MP_TAC o SPEC
    `\n x. if n = 0 then --(ln(&1 - x))
           else &(FACT(PRE n)) * inv((&1 - x) pow n)`) THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real`, `n:num`]) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  REWRITE_TAC[NOT_SUC, LN_1, REAL_POW_ONE] THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `0 < n` THEN ARITH_TAC, ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[REAL_INV_1, REAL_MUL_RID, REAL_MUL_LID] THEN
  SUBGOAL_THEN `!p. ~(p = 0) ==> (&(FACT(PRE p)) / &(FACT p) = inv(&p))`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[NOT_SUC, PRE] THEN
    REWRITE_TAC[real_div, FACT, GSYM REAL_OF_NUM_MUL] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN
    REWRITE_TAC[REAL_OF_NUM_EQ] THEN
    MP_TAC(SPEC `p:num` FACT_LT) THEN ARITH_TAC, ALL_TAC] THEN
  REWRITE_TAC[REAL_NEG_0] THEN
  SUBGOAL_THEN `!p. (if p = 0 then &0 else &(FACT (PRE p))) / &(FACT p) =
                    inv(&p)`
  (fun th -> REWRITE_TAC[th]) THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[REAL_INV_0, real_div, REAL_MUL_LZERO],
      REWRITE_TAC[NOT_SUC] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[NOT_SUC]], ALL_TAC] THEN
  SUBGOAL_THEN
    `!t. (&(FACT(PRE n)) * inv ((&1 - t) pow n)) / &(FACT n) * x pow n
         = x pow n / (&n * (&1 - t) pow n)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[real_div, REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_INV_MUL] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  REWRITE_TAC[real_div, REAL_MUL_AC] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `m:num` THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[] THENL
   [W(MP_TAC o SPEC `u:real` o DIFF_CONV o lhand o rator o snd) THEN
    REWRITE_TAC[PRE, pow, FACT, REAL_SUB_LZERO] THEN
    REWRITE_TAC[REAL_MUL_RNEG, REAL_NEG_NEG, REAL_MUL_RID] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `x < &1` THEN UNDISCH_TAC `u:real <= x` THEN
    REAL_ARITH_TAC,
    W(MP_TAC o SPEC `u:real` o DIFF_CONV o lhand o rator o snd) THEN
    SUBGOAL_THEN `~((&1 - u) pow m = &0)` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `x < &1` THEN UNDISCH_TAC `u:real <= x` THEN
      REAL_ARITH_TAC,
      MATCH_MP_TAC (TAUT `(a = b) ==> a ==> b`) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[REAL_SUB_LZERO, real_div, PRE] THEN
      REWRITE_TAC[REAL_MUL_LZERO, REAL_ADD_RID] THEN
      REWRITE_TAC
       [REAL_MUL_RNEG, REAL_MUL_LNEG, REAL_NEG_NEG, REAL_MUL_RID] THEN
      UNDISCH_TAC `~(m = 0)` THEN SPEC_TAC(`m:num`,`p:num`) THEN
      INDUCT_TAC THEN REWRITE_TAC[NOT_SUC] THEN
      REWRITE_TAC[SUC_SUB1, PRE] THEN REWRITE_TAC[FACT] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
      REWRITE_TAC[real_pow, REAL_POW_2] THEN REWRITE_TAC[REAL_INV_MUL] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN
      REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `x < &1` THEN UNDISCH_TAC `u:real <= x` THEN
      REAL_ARITH_TAC]]);
endnew*)

val _ = export_theory();

end;
