(*===========================================================================*)
(* Definitions of the transcendental functions etc.                          *)
(*===========================================================================*)

(* ----------------------------------------------------------------------
    Exponentiation with real exponents (rpow)

    Contributed by

       Umair Siddique

       Email: umair.siddique@rcms.nust.edu.pk
       DATE: 29-12-2010

       System Analysis & Verification (sAvE)  LAB

       National University of Sciences and Technology (NUST)
       Ialamabad,Pakistan
    ---------------------------------------------------------------------- *)

open HolKernel Parse bossLib boolLib;

open reduceLib
     pairTheory
     numTheory
     prim_recTheory
     arithmeticTheory
     realTheory realSimps realLib
     metricTheory
     netsTheory
     real_sigmaTheory
     numLib
     jrhUtils
     Diff
     pred_setTheory
     mesonLib;

open iterateTheory real_topologyTheory derivativeTheory;
open seqTheory limTheory powserTheory;

val _ = new_theory "transc";
val _ = Parse.reveal "B";

(* Mini hurdUtils *)
val Suff = Q_TAC SUFF_TAC;
val Know = Q_TAC KNOW_TAC;
fun wrap a = [a];
val Rewr' = DISCH_THEN (ONCE_REWRITE_TAC o wrap);
val POP_ORW = POP_ASSUM (ONCE_REWRITE_TAC o wrap);
val art = ASM_REWRITE_TAC;

val MVT            = limTheory.MVT;
val ROLLE          = limTheory.ROLLE;
val summable       = seqTheory.summable;
val differentiable = limTheory.differentiable;

(*---------------------------------------------------------------------------*)
(* The three functions we define by series are exp, sin, cos                 *)
(*---------------------------------------------------------------------------*)

val sin_ser =
 “\n. if EVEN n then &0
         else ((~(&1)) pow ((n - 1) DIV 2)) / &(FACT n)”;

val cos_ser =
   “\n. if EVEN n then ((~(&1)) pow (n DIV 2)) / &(FACT n) else &0”;

val exp_ser = “\n. inv(&(FACT n))”;

Theorem exp = derivativeTheory.exp

val cos = new_definition("cos",
  “cos(x) = suminf(\n. (^cos_ser) n * (x pow n))”);

val sin = new_definition("sin",
  “sin(x) = suminf(\n. (^sin_ser) n * (x pow n))”);

(*---------------------------------------------------------------------------*)
(* Show the series for exp converges, using the ratio test                   *)
(*---------------------------------------------------------------------------*)

(* TODO: use derivativeTheory.EXP_CONVERGES to simply this proof
   also known as REAL_EXP_CONVERGES *)
val EXP_CONVERGES = store_thm("EXP_CONVERGES",
  “!x. (\n. (^exp_ser) n * (x pow n)) sums exp(x)”,
  let fun fnz tm =
    (GSYM o MATCH_MP REAL_LT_IMP_NE o
     REWRITE_RULE[GSYM REAL_LT] o C SPEC FACT_LESS) tm in
  GEN_TAC THEN REWRITE_TAC[exp] THEN MATCH_MP_TAC SUMMABLE_SUM THEN
  MATCH_MP_TAC SER_RATIO THEN
  MP_TAC (SPEC “&1” REAL_DOWN) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN “c:real” STRIP_ASSUME_TAC) THEN
  EXISTS_TAC “c:real” THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC “c:real” REAL_ARCH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC “abs(x)”) THEN
  DISCH_THEN(X_CHOOSE_TAC “N:num”) THEN EXISTS_TAC “N:num” THEN
  X_GEN_TAC “n:num” THEN REWRITE_TAC[GREATER_EQ] THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[ADD1, POW_ADD, ABS_MUL, REAL_MUL_ASSOC, POW_1] THEN
  GEN_REWR_TAC LAND_CONV  [REAL_MUL_SYM] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL_IMP THEN
  REWRITE_TAC[ABS_POS] THEN REWRITE_TAC[GSYM ADD1, FACT] THEN
  REWRITE_TAC[GSYM REAL_MUL, MATCH_MP REAL_INV_MUL (CONJ
   (REWRITE_RULE[GSYM REAL_INJ] (SPEC “n:num” NOT_SUC)) (fnz “n:num”))] THEN
  REWRITE_TAC[ABS_MUL, REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL_IMP THEN REWRITE_TAC[ABS_POS] THEN
  MP_TAC(SPEC “n:num” LESS_0) THEN REWRITE_TAC[GSYM REAL_LT] THEN
  DISCH_THEN(ASSUME_TAC o GSYM o MATCH_MP REAL_LT_IMP_NE) THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP ABS_INV th]) THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_LE_LDIV THEN
  ASM_REWRITE_TAC[GSYM ABS_NZ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[REWRITE_RULE[GSYM ABS_REFL, GSYM REAL_LE] ZERO_LESS_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC “&N * c” THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC,
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_LE_RMUL th]) THEN
    REWRITE_TAC[REAL_LE] THEN MATCH_MP_TAC LESS_EQ_TRANS THEN
    EXISTS_TAC “n:num” THEN ASM_REWRITE_TAC[LESS_EQ_SUC_REFL]] end);

(*---------------------------------------------------------------------------*)
(* Show by the comparison test that sin and cos converge                     *)
(*---------------------------------------------------------------------------*)

val SIN_CONVERGES = store_thm("SIN_CONVERGES",
  “!x. (\n. (^sin_ser) n * (x pow n)) sums sin(x)”,
  GEN_TAC THEN REWRITE_TAC[sin] THEN MATCH_MP_TAC SUMMABLE_SUM THEN
  MATCH_MP_TAC SER_COMPAR THEN
  EXISTS_TAC “\n. ^exp_ser n * (abs(x) pow n)” THEN
  REWRITE_TAC[MATCH_MP SUM_SUMMABLE (SPEC_ALL EXP_CONVERGES)] THEN
  EXISTS_TAC “0:num” THEN X_GEN_TAC “n:num” THEN
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
  “!x. (\n. (^cos_ser) n * (x pow n)) sums cos(x)”,
  GEN_TAC THEN REWRITE_TAC[cos] THEN MATCH_MP_TAC SUMMABLE_SUM THEN
  MATCH_MP_TAC SER_COMPAR THEN
  EXISTS_TAC “\n. (^exp_ser) n * (abs(x) pow n)” THEN
  REWRITE_TAC[MATCH_MP SUM_SUMMABLE (SPEC_ALL EXP_CONVERGES)] THEN
  EXISTS_TAC “0:num” THEN X_GEN_TAC “n:num” THEN
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

(* also known as REAL_EXP_FDIFF *)
val EXP_FDIFF = store_thm("EXP_FDIFF",
  “diffs ^exp_ser = ^exp_ser”,
  REWRITE_TAC[diffs] THEN BETA_TAC THEN
  CONV_TAC(X_FUN_EQ_CONV “n:num”) THEN GEN_TAC THEN BETA_TAC THEN
  REWRITE_TAC[FACT, GSYM REAL_MUL] THEN
  SUBGOAL_THEN “~(&(SUC n) = &0) /\ ~(&(FACT n) = &0)” ASSUME_TAC THENL
   [CONJ_TAC THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN
    REWRITE_TAC[REAL_LT, LESS_0, FACT_LESS],
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_INV_MUL th]) THEN
    GEN_REWR_TAC RAND_CONV  [GSYM REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_MUL_ASSOC, REAL_EQ_RMUL] THEN DISJ2_TAC THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REWRITE_TAC[]]);

val SIN_FDIFF = store_thm("SIN_FDIFF",
  “diffs ^sin_ser = ^cos_ser”,
  REWRITE_TAC[diffs] THEN BETA_TAC THEN
  CONV_TAC(X_FUN_EQ_CONV “n:num”) THEN GEN_TAC THEN BETA_TAC THEN
  COND_CASES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[EVEN]) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN REWRITE_TAC[SUC_SUB1] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FACT, GSYM REAL_MUL] THEN
  SUBGOAL_THEN “~(&(SUC n) = &0) /\ ~(&(FACT n) = &0)” ASSUME_TAC THENL
   [CONJ_TAC THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN
    REWRITE_TAC[REAL_LT, LESS_0, FACT_LESS],
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_INV_MUL th]) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    GEN_REWR_TAC RAND_CONV  [GSYM REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_MUL_ASSOC, REAL_EQ_RMUL] THEN DISJ2_TAC THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REWRITE_TAC[]]);

val COS_FDIFF = store_thm("COS_FDIFF",
  “diffs ^cos_ser = (\n. ~((^sin_ser) n))”,
  REWRITE_TAC[diffs] THEN BETA_TAC THEN
  CONV_TAC(X_FUN_EQ_CONV “n:num”) THEN GEN_TAC THEN BETA_TAC THEN
  COND_CASES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[EVEN]) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO, REAL_NEG_0] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[real_div, REAL_NEG_LMUL] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN BINOP_TAC THENL
   [POP_ASSUM(SUBST1_TAC o MATCH_MP EVEN_DIV_2) THEN
    REWRITE_TAC[pow] THEN REWRITE_TAC[GSYM REAL_NEG_MINUS1],
    REWRITE_TAC[FACT, GSYM REAL_MUL] THEN
    SUBGOAL_THEN “~(&(SUC n) = &0) /\ ~(&(FACT n) = &0)” ASSUME_TAC THENL
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
  “!x. ~(sin x) = suminf (\n. ~((^sin_ser) n * (x pow n)))”,
  GEN_TAC THEN MATCH_MP_TAC SUM_UNIQ THEN
  MP_TAC(MATCH_MP SER_NEG (SPEC “x:real” SIN_CONVERGES)) THEN
  BETA_TAC THEN DISCH_THEN ACCEPT_TAC);

Theorem DIFF_EXP[difftool]:
  !x. (exp diffl exp(x))(x)
Proof
  GEN_TAC THEN REWRITE_TAC[HALF_MK_ABS exp] THEN
  GEN_REWR_TAC (LAND_CONV o ONCE_DEPTH_CONV)  [GSYM EXP_FDIFF] THEN
  CONV_TAC(LAND_CONV BETA_CONV) THEN
  MATCH_MP_TAC TERMDIFF THEN EXISTS_TAC “abs(x) + &1” THEN
  REWRITE_TAC[EXP_FDIFF, MATCH_MP SUM_SUMMABLE (SPEC_ALL EXP_CONVERGES)] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC “abs(x) + &1” THEN
  REWRITE_TAC[ABS_LE, REAL_LT_ADDR] THEN
  REWRITE_TAC[REAL_LT, ONE, LESS_0]
QED

Theorem DIFF_SIN[difftool]:
  !x. (sin diffl cos(x))(x)
Proof
  GEN_TAC THEN REWRITE_TAC[HALF_MK_ABS sin, cos] THEN
  ONCE_REWRITE_TAC[GSYM SIN_FDIFF] THEN
  MATCH_MP_TAC TERMDIFF THEN EXISTS_TAC “abs(x) + &1” THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MATCH_MP SUM_SUMMABLE (SPEC_ALL SIN_CONVERGES)],
    REWRITE_TAC[SIN_FDIFF, MATCH_MP SUM_SUMMABLE (SPEC_ALL COS_CONVERGES)],
    REWRITE_TAC[SIN_FDIFF, COS_FDIFF] THEN BETA_TAC THEN
    MP_TAC(SPEC “abs(x) + &1” SIN_CONVERGES) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SER_NEG) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN BETA_TAC THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL],
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC “abs(x) + &1” THEN
    REWRITE_TAC[ABS_LE, REAL_LT_ADDR] THEN
    REWRITE_TAC[REAL_LT, ONE, LESS_0]]
QED

Theorem DIFF_COS[difftool]:
  !x. (cos diffl ~(sin(x)))(x)
Proof
  GEN_TAC THEN REWRITE_TAC[HALF_MK_ABS cos, SIN_NEGLEMMA] THEN
  ONCE_REWRITE_TAC[REAL_NEG_LMUL] THEN
  REWRITE_TAC[GSYM(CONV_RULE(RAND_CONV BETA_CONV)
    (AP_THM COS_FDIFF “n:num”))] THEN
  MATCH_MP_TAC TERMDIFF THEN EXISTS_TAC “abs(x) + &1” THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MATCH_MP SUM_SUMMABLE (SPEC_ALL COS_CONVERGES)],
    REWRITE_TAC[COS_FDIFF] THEN
    MP_TAC(SPEC “abs(x) + &1” SIN_CONVERGES) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SER_NEG) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN BETA_TAC THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL],
    REWRITE_TAC[COS_FDIFF, DIFFS_NEG] THEN
    MP_TAC SIN_FDIFF THEN BETA_TAC THEN
    DISCH_THEN(fn th => REWRITE_TAC[th]) THEN
    MP_TAC(SPEC “abs(x) + &1” COS_CONVERGES) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SER_NEG) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN BETA_TAC THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL],
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC “abs(x) + &1” THEN
    REWRITE_TAC[ABS_LE, REAL_LT_ADDR] THEN
    REWRITE_TAC[REAL_LT, ONE, LESS_0]]
QED

(* ------------------------------------------------------------------------- *)
(* Processed versions of composition theorems.                               *)
(* ------------------------------------------------------------------------- *)

Theorem DIFF_COMPOSITE[difftool]:
   ((f diffl l)(x) /\ ~(f(x) = &0) ==>
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
   ((g diffl m)(x) ==> ((\x. cos(g x)) diffl (~(sin(g x)) * m))(x))
Proof
  REWRITE_TAC[DIFF_INV, DIFF_DIV, DIFF_ADD, DIFF_SUB, DIFF_MUL, DIFF_NEG] THEN
  REPEAT CONJ_TAC THEN DISCH_TAC THEN
  TRY(MATCH_MP_TAC DIFF_CHAIN THEN
  ASM_REWRITE_TAC[DIFF_SIN, DIFF_COS, DIFF_EXP]) THEN
  MATCH_MP_TAC(BETA_RULE (SPEC (Term`\x. x pow n`) DIFF_CHAIN)) THEN
  ASM_REWRITE_TAC[DIFF_POW]
QED

(*---------------------------------------------------------------------------*)
(* Properties of the exponential function                                    *)
(*---------------------------------------------------------------------------*)

(* also known as REAL_EXP_0 *)
val EXP_0 = store_thm("EXP_0",
  “exp(&0) = &1”,
  REWRITE_TAC[exp] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SUM_UNIQ THEN BETA_TAC THEN
  W(MP_TAC o C SPEC SER_0 o rand o rator o snd) THEN
  DISCH_THEN(MP_TAC o SPEC “1:num”) THEN
  REWRITE_TAC[ONE, sum] THEN
  REWRITE_TAC[ADD_CLAUSES, REAL_ADD_LID] THEN BETA_TAC THEN
  REWRITE_TAC[FACT, pow, REAL_MUL_RID, REAL_INV1] THEN
  REWRITE_TAC[SYM(ONE)] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC “n:num” THEN REWRITE_TAC[ONE, GSYM LESS_EQ] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
  REWRITE_TAC[GSYM ADD1, POW_0, REAL_MUL_RZERO, ADD_CLAUSES]);

(* also known as REAL_EXP_LE_X *)
val EXP_LE_X = store_thm("EXP_LE_X",
“!x. &0 <= x ==> (&1 + x) <= exp(x)”,
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

(* also known REAL_EXP_LT_1 *)
val EXP_LT_1 = store_thm("EXP_LT_1",
  “!x. &0 < x ==> &1 < exp(x)”,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC “&1 + x” THEN ASM_REWRITE_TAC[REAL_LT_ADDR] THEN
  MATCH_MP_TAC EXP_LE_X THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  POP_ASSUM ACCEPT_TAC);

(* also known as REAL_EXP_ADD_MUL *)
val EXP_ADD_MUL = store_thm("EXP_ADD_MUL",
  “!x y. exp(x + y) * exp(~x) = exp(y)”,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(X_BETA_CONV “x:real”)) THEN
  SUBGOAL_THEN “exp(y) = (\x. exp(x + y) * exp(~x))(&0)” SUBST1_TAC THENL
   [BETA_TAC THEN REWRITE_TAC[REAL_ADD_LID, REAL_NEG_0] THEN
    REWRITE_TAC[EXP_0, REAL_MUL_RID],
    MATCH_MP_TAC DIFF_ISCONST_ALL THEN X_GEN_TAC “x:real” THEN
    W(MP_TAC o DIFF_CONV o rand o funpow 2 rator o snd) THEN
    DISCH_THEN(MP_TAC o SPEC “x:real”) THEN
    MATCH_MP_TAC(TAUT_CONV “(a <=> b) ==> a ==> b”) THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC[GSYM real_sub, REAL_SUB_0, REAL_MUL_RID, REAL_ADD_RID] THEN
    MATCH_ACCEPT_TAC REAL_MUL_SYM]);

(* also known as REAL_EXP_NEG_MUL *)
val EXP_NEG_MUL = store_thm("EXP_NEG_MUL",
  “!x. exp(x) * exp(~x) = &1”,
  GEN_TAC THEN MP_TAC(SPECL [“x:real”, “&0”] EXP_ADD_MUL) THEN
  REWRITE_TAC[REAL_ADD_RID, EXP_0]);

(* also known as REAL_EXP_NEG_MUL2 *)
val EXP_NEG_MUL2 = store_thm("EXP_NEG_MUL2",
  “!x. exp(~x) * exp(x) = &1”,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_ACCEPT_TAC EXP_NEG_MUL);

(* also known as REAL_EXP_NEG *)
val EXP_NEG = store_thm("EXP_NEG",
  “!x. exp(~x) = inv(exp(x))”,
  GEN_TAC THEN MATCH_MP_TAC REAL_RINV_UNIQ THEN
  MATCH_ACCEPT_TAC EXP_NEG_MUL);

val EXP_ADD = store_thm("EXP_ADD",
  “!x y. exp(x + y) = exp(x) * exp(y)”,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [“x:real”, “y:real”] EXP_ADD_MUL) THEN
  DISCH_THEN(MP_TAC o C AP_THM “exp(x)” o AP_TERM “$*”) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] EXP_NEG_MUL, REAL_MUL_RID] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_ACCEPT_TAC REAL_MUL_SYM);

Theorem REAL_EXP_ADD = EXP_ADD

(* also known as REAL_EXP_POS_LE *)
val EXP_POS_LE = store_thm("EXP_POS_LE",
  “!x. &0 <= exp(x)”,
  GEN_TAC THEN
  GEN_REWR_TAC (funpow 2 RAND_CONV)  [GSYM REAL_HALF_DOUBLE] THEN
  REWRITE_TAC[EXP_ADD] THEN MATCH_ACCEPT_TAC REAL_LE_SQUARE);

(* also known as REAL_EXP_NZ *)
val EXP_NZ = store_thm("EXP_NZ",
  “!x. ~(exp(x) = &0)”,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC “x:real” EXP_NEG_MUL) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  MATCH_ACCEPT_TAC REAL_10);

(* also known as REAL_EXP_POS_LT *)
val EXP_POS_LT = store_thm("EXP_POS_LT",
  “!x. &0 < exp(x)”,
  GEN_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  REWRITE_TAC[EXP_POS_LE, EXP_NZ]);

(* also known as REAL_EXP_N *)
val EXP_N = store_thm("EXP_N",
  “!n x. exp(&n * x) = exp(x) pow n”,
  INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO, EXP_0, pow] THEN
  REWRITE_TAC[ADD1] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[GSYM REAL_ADD, EXP_ADD, REAL_RDISTRIB] THEN
  GEN_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LID]);

(* also known as REAL_EXP_SUB *)
val EXP_SUB = store_thm("EXP_SUB",
  “!x y. exp(x - y) = exp(x) / exp(y)”,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_sub, real_div, EXP_ADD, EXP_NEG]);

(* also known as REAL_EXP_MONO_IMP *)
val EXP_MONO_IMP = store_thm("EXP_MONO_IMP",
  “!x y. x < y ==> exp(x) < exp(y)”,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o
    MATCH_MP EXP_LT_1 o ONCE_REWRITE_RULE[GSYM REAL_SUB_LT]) THEN
  REWRITE_TAC[EXP_SUB] THEN
  SUBGOAL_THEN “&1 < exp(y) / exp(x) <=>
                 (&1 * exp(x)) < ((exp(y) / exp(x)) * exp(x))” SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LT_RMUL THEN
    MATCH_ACCEPT_TAC EXP_POS_LT,
    REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC, EXP_NEG_MUL2, GSYM EXP_NEG] THEN
    REWRITE_TAC[REAL_MUL_LID, REAL_MUL_RID]]);

(* also known as REAL_EXP_MONO_LT *)
val EXP_MONO_LT = store_thm("EXP_MONO_LT",
  “!x y. exp(x) < exp(y) <=> x < y”,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[REAL_NOT_LT] THEN
    REWRITE_TAC[REAL_LE_LT] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    REWRITE_TAC[] THEN DISJ1_TAC THEN MATCH_MP_TAC EXP_MONO_IMP THEN
    POP_ASSUM ACCEPT_TAC,
    MATCH_ACCEPT_TAC EXP_MONO_IMP]);

(* also known as REAL_EXP_MONO_LE *)
val EXP_MONO_LE = store_thm("EXP_MONO_LE",
  “!x y. exp(x) <= exp(y) <=> x <= y”,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  REWRITE_TAC[EXP_MONO_LT]);

(* also known as REAL_EXP_INJ *)
val EXP_INJ = store_thm("EXP_INJ",
  “!x y. (exp(x) = exp(y)) <=> (x = y)”,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  REWRITE_TAC[EXP_MONO_LE]);

(* also known as REAL_EXP_TOTAL_LEMMA *)
val EXP_TOTAL_LEMMA = store_thm("EXP_TOTAL_LEMMA",
  “!y. &1 <= y ==> ?x. &0 <= x /\ x <= y - &1 /\ (exp(x) = y)”,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC IVT THEN
  ASM_REWRITE_TAC[EXP_0, REAL_LE_SUB_LADD, REAL_ADD_LID] THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM REAL_SUB_LE]) THEN
    POP_ASSUM(MP_TAC o MATCH_MP EXP_LE_X) THEN REWRITE_TAC[REAL_SUB_ADD2],
    X_GEN_TAC “x:real” THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC “exp(x)” THEN
    MATCH_ACCEPT_TAC DIFF_EXP]);

(* also known as REAL_EXP_TOTAL *)
val EXP_TOTAL = store_thm("EXP_TOTAL",
  “!y. &0 < y ==> ?x. exp(x) = y”,
  GEN_TAC THEN DISCH_TAC THEN
  DISJ_CASES_TAC(SPECL [“&1”, “y:real”] REAL_LET_TOTAL) THENL
   [FIRST_ASSUM(X_CHOOSE_TAC “x:real” o MATCH_MP EXP_TOTAL_LEMMA) THEN
    EXISTS_TAC “x:real” THEN ASM_REWRITE_TAC[],
    MP_TAC(SPEC “y:real” REAL_INV_LT1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
    DISCH_THEN(X_CHOOSE_TAC “x:real” o MATCH_MP EXP_TOTAL_LEMMA) THEN
    Q.EXISTS_TAC ‘~x’ THEN ASM_REWRITE_TAC[EXP_NEG] THEN
    MATCH_MP_TAC REAL_INVINV THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN ASM_REWRITE_TAC[]]);

(* recovered from transc.ml *)
Theorem REAL_EXP_BOUND_LEMMA :
    !x. &0 <= x /\ x <= inv(&2) ==> exp(x) <= &1 + &2 * x
Proof
  GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  Q.EXISTS_TAC `suminf (\n. x pow n)` THEN CONJ_TAC >| (* 2 subgoals *)
  [ (* goal 1 (of 2) *)
    SIMP_TAC std_ss [exp] THEN MATCH_MP_TAC SER_LE THEN
    SIMP_TAC std_ss [summable] THEN REPEAT CONJ_TAC >| (* 3 subgoals *)
    [ (* goal 1.1 (of 3) *)
      GEN_TAC THEN
      GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL_IMP THEN CONJ_TAC >| (* 2 subgoals *)
      [ (* goal 1.1.1 (of 2) *)
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[],
        (* goal 1.1.2 (of 2) *)
        MATCH_MP_TAC REAL_INV_LE_1 THEN
        REWRITE_TAC[REAL_OF_NUM_LE, num_CONV ``1:num``, GSYM LESS_EQ] THEN
        REWRITE_TAC[FACT_LESS] ],
      (* goal 1.2 (of 3) *)
      Q.EXISTS_TAC `exp x` THEN REWRITE_TAC[BETA_RULE EXP_CONVERGES],
      (* goal 1.3 (of 3) *)
      Q.EXISTS_TAC `inv(&1 - x)` THEN MATCH_MP_TAC GP THEN
      ASM_REWRITE_TAC[abs] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN Q.EXISTS_TAC `inv(&2)` >> rw [] ],
    (* goal 2 (of 2) *)
    Q.SUBGOAL_THEN `suminf (\n. x pow n) = inv (&1 - x)` SUBST1_TAC >| (* 2 subgoals *)
    [ (* goal 2.1 (of 2) *)
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_UNIQ THEN
      MATCH_MP_TAC GP THEN
      ASM_REWRITE_TAC[abs] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN Q.EXISTS_TAC `inv(&2)` >> rw [],
      (* goal 2.2 (of 2) *)
      MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
      Q.EXISTS_TAC `&1 - x` THEN
      Q.SUBGOAL_THEN `(&1 - x) * inv (&1 - x) = &1` SUBST1_TAC >| (* 2 subgoals *)
      [ (* goal 2.2.1 (of 2) *)
        MATCH_MP_TAC REAL_MUL_RINV THEN
        REWRITE_TAC[REAL_ARITH ``(&1 - x = &0) <=> (x = &1)``] THEN
        DISCH_THEN SUBST_ALL_TAC THEN
        POP_ASSUM MP_TAC >> rw [],
        (* goal 2.2.2 (of 2) *)
        CONJ_TAC >| (* 2 subgoals *)
        [ (* goal 2.2.2.1 (of 2) *)
          MATCH_MP_TAC REAL_LET_TRANS THEN
          Q.EXISTS_TAC `inv(&2) - x` THEN
          ASM_REWRITE_TAC[REAL_ARITH ``&0 <= x - y <=> y <= x``] THEN
          ASM_REWRITE_TAC[REAL_ARITH ``a - x < b - x <=> a < b``] THEN
          rw [],
          (* goal 2.2.2.2 (of 2) *)
          REWRITE_TAC[REAL_ADD_LDISTRIB, REAL_SUB_RDISTRIB] THEN
          REWRITE_TAC[REAL_MUL_RID, REAL_MUL_LID] THEN
          REWRITE_TAC[REAL_ARITH ``&1 <= (&1 + &2 * x) - (x + x * (&2 * x)) <=>
                                   x * (&2 * x) <= x * &1``] THEN
          MATCH_MP_TAC REAL_LE_LMUL_IMP THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN Q.EXISTS_TAC `inv(&2)` THEN
          REWRITE_TAC[REAL_MUL_ASSOC] THEN
          CONJ_TAC >- REWRITE_TAC [REAL_INV_1OVER, REAL_HALF_BETWEEN] \\
          ASM_SIMP_TAC real_ss [REAL_MUL_RID, REAL_MUL_LINV] ] ] ] ]
QED

(*---------------------------------------------------------------------------*)
(* Properties of the logarithmic function                                    *)
(*---------------------------------------------------------------------------*)

val ln = new_definition("ln",
  “ln x = @u. exp(u) = x”);

val LN_EXP = store_thm("LN_EXP",
  “!x. ln(exp x) = x”,
  GEN_TAC THEN REWRITE_TAC[ln, EXP_INJ] THEN
  CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN MATCH_MP_TAC SELECT_AX THEN
  EXISTS_TAC “x:real” THEN REFL_TAC);

(* also known as REAL_EXP_LN *)
val EXP_LN = store_thm("EXP_LN",
  “!x. (exp(ln x) = x) <=> &0 < x”,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC EXP_POS_LT,
    DISCH_THEN(X_CHOOSE_THEN “y:real” MP_TAC o MATCH_MP EXP_TOTAL) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[EXP_INJ, LN_EXP]]);

val LN_MUL = store_thm("LN_MUL",
  “!x y. &0 < x /\ &0 < y ==> (ln(x * y) = ln(x) + ln(y))”,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM EXP_INJ] THEN
  REWRITE_TAC[EXP_ADD] THEN SUBGOAL_THEN “&0 < x * y” ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[],
    EVERY_ASSUM(fn th => REWRITE_TAC[ONCE_REWRITE_RULE[GSYM EXP_LN] th])]);

val LN_INJ = store_thm("LN_INJ",
  “!x y. &0 < x /\ &0 < y ==> ((ln(x) = ln(y)) = (x = y))”,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EVERY_ASSUM(fn th => GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV)
    [SYM(REWRITE_RULE[GSYM EXP_LN] th)]) THEN
  CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC EXP_INJ);

val LN_1 = store_thm("LN_1",
  “ln(&1) = &0”,
  ONCE_REWRITE_TAC[GSYM EXP_INJ] THEN
  REWRITE_TAC[EXP_0, EXP_LN, REAL_LT_01]);

val LN_INV = store_thm("LN_INV",
  “!x. &0 < x ==> (ln(inv x) = ~(ln x))”,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_RNEG_UNIQ] THEN
  SUBGOAL_THEN “&0 < x /\ &0 < inv(x)” MP_TAC THENL
   [CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_INV_POS) THEN ASM_REWRITE_TAC[],
    DISCH_THEN(fn th => REWRITE_TAC[GSYM(MATCH_MP LN_MUL th)]) THEN
    SUBGOAL_THEN “x * (inv x) = &1” SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_RINV THEN
      POP_ASSUM(ACCEPT_TAC o MATCH_MP REAL_POS_NZ),
      REWRITE_TAC[LN_1]]]);

val LN_DIV = store_thm("LN_DIV",
  “!x y. &0 < x /\ &0 < y ==> (ln(x / y) = ln(x) - ln(y))”,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN “&0 < x /\ &0 < inv(y)” MP_TAC THENL
   [CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_INV_POS) THEN ASM_REWRITE_TAC[],
    REWRITE_TAC[real_div] THEN
    DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP LN_MUL th]) THEN
    REWRITE_TAC[MATCH_MP LN_INV (ASSUME “&0 < y”)] THEN
    REWRITE_TAC[real_sub]]);

val LN_MONO_LT = store_thm("LN_MONO_LT",
  “!x y. &0 < x /\ &0 < y ==> (ln(x) < ln(y) <=> x < y)”,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EVERY_ASSUM(fn th => GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV)
    [SYM(REWRITE_RULE[GSYM EXP_LN] th)]) THEN
  CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC EXP_MONO_LT);

val LN_MONO_LE = store_thm("LN_MONO_LE",
  “!x y. &0 < x /\ &0 < y ==> (ln(x) <= ln(y) <=> x <= y)”,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EVERY_ASSUM(fn th => GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV)
    [SYM(REWRITE_RULE[GSYM EXP_LN] th)]) THEN
  CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC EXP_MONO_LE);

val LN_POW = store_thm("LN_POW",
  “!n x. &0 < x ==> (ln(x pow n) = &n * ln(x))”,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CHOOSE_THEN (SUBST1_TAC o SYM) o MATCH_MP EXP_TOTAL) THEN
  REWRITE_TAC[GSYM EXP_N, LN_EXP]);

val LN_LE = store_thm("LN_LE",
  Term `!x. &0 <= x ==> ln(&1 + x) <= x`,
  GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM LN_EXP] THEN
  MP_TAC(SPECL [Term`&1 + x`, Term`exp x`] LN_MONO_LE) THEN
  W(C SUBGOAL_THEN (fn t => REWRITE_TAC[t]) o funpow 2 (fst o dest_imp) o snd)
  THENL
   [REWRITE_TAC[EXP_POS_LT] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (Term`x:real`) THEN ASM_REWRITE_TAC[REAL_LT_ADDL, REAL_LT_01],
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC EXP_LE_X THEN ASM_REWRITE_TAC[]]);

val LN_LT_X = store_thm("LN_LT_X",
  “!x. &0 < x ==> ln(x) < x”,
  GEN_TAC THEN DISCH_TAC THEN
  GEN_REWR_TAC I  [TAUT_CONV “a:bool = ~~a”] THEN
  PURE_REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPEC “ln(x)” EXP_LE_X) THEN
  SUBGOAL_THEN “&0 <= ln(x)” ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC “x:real” THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE, ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MP_TAC(SPEC “x:real” EXP_LN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN “(&1 + ln(x)) <= ln(x)” MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC “x:real”, ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_NOT_LE] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC “&0 + ln(x)” THEN
  REWRITE_TAC[REAL_LT_RADD, REAL_LT_01] THEN
  REWRITE_TAC[REAL_ADD_LID, REAL_LE_REFL]);

Theorem LN_POS_LT :
    !(x :real). 1 < x ==> 0 < ln x
Proof
    RW_TAC std_ss [GSYM LN_1]
 >> ASSUME_TAC REAL_LT_01
 >> ‘0 < x’ by PROVE_TAC [REAL_LT_TRANS]
 >> RW_TAC std_ss [LN_MONO_LT]
QED

Theorem LN_POS :
    !(x :real). 1 <= x ==> 0 <= ln x
Proof
    rpt STRIP_TAC
 >> ‘x = 1 \/ 1 < x’ by PROVE_TAC [REAL_LE_LT] >- rw [LN_1]
 >> MATCH_MP_TAC REAL_LT_IMP_LE
 >> MATCH_MP_TAC LN_POS_LT >> art []
QED

Theorem LN_NEG_LT :
    !(x :real). 0 < x /\ x < 1 ==> ln x < 0
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘y = inv x’
 >> ‘1 < y’ by METIS_TAC [REAL_INV_LT1]
 >> Know ‘x = inv y’
 >- (MATCH_MP_TAC REAL_RINV_UNIQ \\
     Q.UNABBREV_TAC ‘y’ \\
     MATCH_MP_TAC REAL_MUL_LINV \\
     PROVE_TAC [REAL_LT_IMP_NE])
 >> Rewr'
 >> ‘0 < y’ by PROVE_TAC [REAL_LT_01, REAL_LT_TRANS]
 >> rw [LN_INV]
 >> MATCH_MP_TAC LN_POS_LT >> art []
QED

Theorem LN_NEG :
    !(x :real). 0 < x /\ x <= 1 ==> ln x <= 0
Proof
    rpt STRIP_TAC
 >> ‘x = 1 \/ x < 1’ by PROVE_TAC [REAL_LE_LT] >- rw [LN_1]
 >> MATCH_MP_TAC REAL_LT_IMP_LE
 >> MATCH_MP_TAC LN_NEG_LT >> art []
QED

Theorem DIFF_LN[difftool]:
   !x. &0 < x ==> (ln diffl (inv x))(x)
Proof
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[GSYM EXP_LN]) THEN
  FIRST_ASSUM (fn th =>  GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM th]) THEN
  MATCH_MP_TAC DIFF_INVERSE_LT THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_POS_NZ) THEN
  ASM_REWRITE_TAC[MATCH_MP DIFF_CONT (SPEC_ALL DIFF_EXP)] THEN
  MP_TAC(SPEC (Term`ln(x)`) DIFF_EXP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[LN_EXP] THEN
  EXISTS_TAC (Term`&1`) THEN MATCH_ACCEPT_TAC REAL_LT_01
QED

(*---------------------------------------------------------------------------*)
(* Some properties of roots (easier via logarithms)                          *)
(*---------------------------------------------------------------------------*)

Definition root:
    root(n) x = @u. (&0 < x ==> &0 < u) /\ (u pow n = x)
End

Theorem sqrt :
    !x. sqrt(x) = root(2) x
Proof
    REWRITE_TAC [sqrt_def, root]
QED

val ROOT_LT_LEMMA = store_thm("ROOT_LT_LEMMA",
  “!n x. &0 < x ==> (exp(ln(x) / &(SUC n)) pow (SUC n) = x)”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM EXP_N] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN
  SUBGOAL_THEN “inv(&(SUC n)) * &(SUC n) = &1” SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC[REAL_INJ, NOT_SUC],
    ASM_REWRITE_TAC[REAL_MUL_RID, EXP_LN]]);

val ROOT_LN = store_thm("ROOT_LN",
  “!n x. &0 < x ==> (root(SUC n) x = exp(ln(x) / &(SUC n)))”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[root] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC “y:real” THEN BETA_TAC THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    SUBGOAL_THEN “!z. &0 < y /\ &0 < exp(z)” MP_TAC THENL
     [ASM_REWRITE_TAC[EXP_POS_LT], ALL_TAC] THEN
    DISCH_THEN(MP_TAC o GEN_ALL o SYM o MATCH_MP LN_INJ o SPEC_ALL) THEN
    DISCH_THEN(fn th => GEN_REWR_TAC I  [th]) THEN
    REWRITE_TAC[LN_EXP] THEN
    SUBGOAL_THEN “ln(y) * &(SUC n) = (ln(y pow(SUC n)) / &(SUC n)) * &(SUC n)”
    MP_TAC THENL
     [REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN
      SUBGOAL_THEN “inv(&(SUC n)) * &(SUC n) = &1” SUBST1_TAC THENL
       [MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC[REAL_INJ, NOT_SUC],
        REWRITE_TAC[REAL_MUL_RID] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC LN_POW THEN
        ASM_REWRITE_TAC[]],
      REWRITE_TAC[REAL_EQ_RMUL, REAL_INJ, NOT_SUC]],
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXP_POS_LT] THEN
    MATCH_MP_TAC ROOT_LT_LEMMA THEN ASM_REWRITE_TAC[]]);

val ROOT_0 = store_thm("ROOT_0",
  “!n. root(SUC n) (&0) = &0”,
  GEN_TAC THEN REWRITE_TAC[root] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC “y:real” THEN
  BETA_TAC THEN REWRITE_TAC[REAL_LT_REFL] THEN EQ_TAC THENL
   [SPEC_TAC(“n:num”,“n:num”) THEN INDUCT_TAC THEN ONCE_REWRITE_TAC[pow] THENL
     [REWRITE_TAC[pow, REAL_MUL_RID],
      REWRITE_TAC[REAL_ENTIRE] THEN DISCH_THEN DISJ_CASES_TAC THEN
      ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]],
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[pow, REAL_MUL_LZERO]]);

val ROOT_1 = store_thm("ROOT_1",
  “!n. root(SUC n) (&1) = &1”,
  GEN_TAC THEN REWRITE_TAC[MATCH_MP ROOT_LN REAL_LT_01] THEN
  REWRITE_TAC[LN_1, REAL_DIV_LZERO, EXP_0]);

val ROOT_POS_LT = store_thm("ROOT_POS_LT",
  “!n x. &0 < x ==> &0 < root(SUC n) x”,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP ROOT_LN th]) THEN
  REWRITE_TAC[EXP_POS_LT]);

val ROOT_POW_POS = store_thm("ROOT_POW_POS",
  “!n x. &0 <= x ==> ((root(SUC n) x) pow (SUC n) = x)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [FIRST_ASSUM(fn th => REWRITE_TAC
     [MATCH_MP ROOT_LN th, MATCH_MP ROOT_LT_LEMMA th]),
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[ROOT_0] THEN
    MATCH_ACCEPT_TAC POW_0]);

Theorem ROOT_11 :
    !n x y. &0 <= x /\ &0 <= y /\ root(SUC n) x = root(SUC n) y ==> x = y
Proof
    rpt STRIP_TAC
 >> ‘(root (SUC n) x) pow (SUC n) = (root (SUC n) y) pow (SUC n)’
      by PROVE_TAC []
 >> rfs [ROOT_POW_POS]
QED

val POW_ROOT_POS = store_thm("POW_ROOT_POS",
  “!n x. &0 <= x ==> (root(SUC n)(x pow (SUC n)) = x)”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[root] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC “y:real” THEN BETA_TAC THEN EQ_TAC THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THENL
   [DISJ_CASES_THEN MP_TAC (REWRITE_RULE[REAL_LE_LT] (ASSUME “&0 <= x”)) THENL
     [DISCH_TAC THEN FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
      FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP POW_POS_LT th]) THEN
      DISCH_TAC THEN MATCH_MP_TAC POW_EQ THEN EXISTS_TAC “n:num” THEN
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
  “!n x. &0 <= x ==> &0 <= root(SUC n) x”,
  REPEAT GEN_TAC THEN
  DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [MAP_EVERY MATCH_MP_TAC [REAL_LT_IMP_LE, ROOT_POS_LT] THEN
    POP_ASSUM ACCEPT_TAC,
    POP_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[ROOT_0, REAL_LE_REFL]]);

Theorem ROOT_POS_UNIQ :
   !n x y. &0 <= x /\ &0 <= y /\ (y pow (SUC n) = x)
           ==> (root (SUC n) x = y)
Proof
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[POW_ROOT_POS]
QED

Theorem ROOT_MUL :
   !n x y. &0 <= x /\ &0 <= y
           ==> (root(SUC n) (x * y) = root(SUC n) x * root(SUC n) y)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ROOT_POS_UNIQ THEN
  REWRITE_TAC [POW_MUL] THEN REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[],
   MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC ROOT_POS
   THEN ASM_REWRITE_TAC[],
   IMP_RES_TAC ROOT_POW_POS THEN ASM_REWRITE_TAC[]]
QED

Theorem ROOT_INV :
   !n x. &0 <= x ==> (root(SUC n) (inv x) = inv(root(SUC n) x))
Proof
 REPEAT STRIP_TAC THEN MATCH_MP_TAC ROOT_POS_UNIQ THEN REPEAT CONJ_TAC THENL
 [IMP_RES_THEN ACCEPT_TAC REAL_LE_INV,
  MATCH_MP_TAC REAL_LE_INV THEN IMP_RES_THEN (TRY o MATCH_ACCEPT_TAC) ROOT_POS,
  IMP_RES_TAC ROOT_POW_POS THEN MP_TAC (SPEC_ALL ROOT_POS)
   THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [REAL_LE_LT]
    THEN STRIP_TAC THENL
    [IMP_RES_TAC REAL_POS_NZ THEN IMP_RES_THEN (fn th =>
       REWRITE_TAC [GSYM th]) POW_INV THEN ASM_REWRITE_TAC[],
     POP_ASSUM (ASSUME_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
     PAT_X_ASSUM (Term `$! M`) (SUBST1_TAC o SYM o SPEC_ALL)
      THEN ASM_REWRITE_TAC[REAL_INV_0,POW_0]]]
QED

Theorem ROOT_DIV :
   !n x y. &0 <= x /\ &0 <= y
           ==> (root(SUC n) (x / y) = root(SUC n) x / root(SUC n) y)
Proof
 REWRITE_TAC [real_div] THEN REPEAT STRIP_TAC THEN IMP_RES_TAC REAL_LE_INV
 THEN MP_TAC (SPECL [Term`n:num`, Term`x:real`, Term`inv y`] ROOT_MUL)
 THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
 THEN IMP_RES_TAC (SPECL [Term`n:num`, Term`y:real`] ROOT_INV)
 THEN ASM_REWRITE_TAC[]
QED

(* added ‘n’ into quantifiers *)
Theorem ROOT_MONO_LE :
   !n x y. &0 <= x /\ x <= y ==> root(SUC n) x <= root(SUC n) y
Proof
  REPEAT STRIP_TAC THEN SUBGOAL_THEN (Term`&0 <= y`) ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS], ALL_TAC] THEN
  UNDISCH_TAC (Term`x <= y`) THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN (Term `(x = (root(SUC n) x) pow (SUC n)) /\
                      (y = (root(SUC n) y) pow (SUC n))`)
   (CONJUNCTS_THEN SUBST1_TAC)
  THENL [IMP_RES_TAC (GSYM ROOT_POW_POS) THEN ASM_MESON_TAC[], ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LT2 THEN
  ASM_REWRITE_TAC[NOT_SUC] THEN MATCH_MP_TAC ROOT_POS THEN ASM_REWRITE_TAC[]
QED

Theorem ROOT_MONO_LE_EQ :
   !n x y. &0 <= x /\ &0 <= y ==> (root (SUC n) x <= root (SUC n) y <=> x <= y)
Proof
    rpt STRIP_TAC
 >> reverse EQ_TAC >- (DISCH_TAC >> MATCH_MP_TAC ROOT_MONO_LE >> art [])
 >> DISCH_TAC
 >> CCONTR_TAC >> FULL_SIMP_TAC std_ss [GSYM real_lt]
 >> IMP_RES_TAC REAL_LT_IMP_LE
 >> ‘root(SUC n) y <= root(SUC n) x’ by PROVE_TAC [ROOT_MONO_LE]
 >> ‘root(SUC n) x = root(SUC n) y’ by PROVE_TAC [REAL_LE_ANTISYM]
 >> METIS_TAC [ROOT_11, REAL_LT_LE]
QED

val lem = prove(Term`0<2:num`, REWRITE_TAC[TWO,LESS_0]);

Theorem EVEN_MOD[local] :
    !n. EVEN(n) = (n MOD 2 = 0)
Proof
  GEN_TAC THEN REWRITE_TAC[EVEN_EXISTS] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  EQ_TAC THEN STRIP_TAC THENL
  [ASM_REWRITE_TAC [MP (SPEC (Term`2:num`) MOD_EQ_0) lem],
   EXISTS_TAC (Term `n DIV 2`) THEN
     MP_TAC (CONJUNCT1 (SPEC (Term `n:num`) (MATCH_MP DIVISION lem))) THEN
     ASM_REWRITE_TAC [ADD_CLAUSES]]
QED

Theorem SQRT_EVEN_POW2 :
    !n. EVEN n ==> (sqrt(&2 pow n) = &2 pow (n DIV 2))
Proof
  GEN_TAC THEN REWRITE_TAC[EVEN_MOD] THEN DISCH_TAC THEN
  MATCH_MP_TAC SQRT_POS_UNIQ THEN REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC POW_POS THEN REWRITE_TAC [REAL_POS],
   MATCH_MP_TAC POW_POS THEN REWRITE_TAC [REAL_POS],
   REWRITE_TAC [REAL_POW_POW] THEN AP_TERM_TAC THEN
   MP_TAC (CONJUNCT1 (SPEC (Term `n:num`) (MATCH_MP DIVISION lem)))
   THEN ASM_REWRITE_TAC [ADD_CLAUSES] THEN DISCH_THEN (SUBST1_TAC o SYM)
   THEN REFL_TAC]
QED

Theorem REAL_DIV_SQRT :
    !x. &0 <= x ==> (x / sqrt(x) = sqrt(x))
Proof
  GEN_TAC THEN ASM_CASES_TAC (Term`x = &0`) THENL
   [ASM_REWRITE_TAC[SQRT_0, real_div, REAL_MUL_LZERO], ALL_TAC] THEN
  DISCH_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_POS_UNIQ THEN
  ASM_REWRITE_TAC[] THEN IMP_RES_TAC SQRT_POS_LE THEN
  MP_TAC (SPECL[Term`x:real`, Term`sqrt x`] REAL_LE_DIV) THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN (fn th => CONJ_TAC THENL [ACCEPT_TAC th, ALL_TAC]) THEN
  REWRITE_TAC[real_div, POW_MUL] THEN PAT_X_ASSUM (Term`_ <= sqrt _`) MP_TAC
  THEN REWRITE_TAC [REAL_LE_LT] THEN STRIP_TAC THENL
  [IMP_RES_TAC REAL_POS_NZ THEN IMP_RES_THEN (fn th =>
    REWRITE_TAC [GSYM th]) POW_INV THEN IMP_RES_THEN (fn th =>
    REWRITE_TAC [th]) SQRT_POW_2 THEN REWRITE_TAC[POW_2, GSYM REAL_MUL_ASSOC]
    THEN IMP_RES_THEN (fn th => REWRITE_TAC [th]) REAL_MUL_RINV THEN
    REWRITE_TAC [REAL_MUL_RID],
   PAT_X_ASSUM (Term `& 0 <= x`) MP_TAC THEN
   REWRITE_TAC [REAL_LE_LT] THEN STRIP_TAC THENL
   [IMP_RES_TAC SQRT_POS_LT THEN
     PAT_X_ASSUM (Term `& 0 = _`) (SUBST_ALL_TAC o SYM) THEN
     IMP_RES_TAC REAL_LT_REFL,
   PAT_X_ASSUM (Term `& 0 = _`) (SUBST_ALL_TAC o SYM)
   THEN REWRITE_TAC [POW_0, TWO, REAL_MUL_LZERO]]]
QED

(*---------------------------------------------------------------------------*)
(* Basic properties of the trig functions                                    *)
(*---------------------------------------------------------------------------*)

val SIN_0 = store_thm("SIN_0",
  “sin(&0) = &0”,
  REWRITE_TAC[sin] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SUM_UNIQ THEN BETA_TAC THEN
  W(MP_TAC o C SPEC SER_0 o rand o rator o snd) THEN
  DISCH_THEN(MP_TAC o SPEC “0:num”) THEN REWRITE_TAC[ZERO_LESS_EQ] THEN
  BETA_TAC THEN
  REWRITE_TAC[sum] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC “n:num” THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  MP_TAC(SPEC “n:num” ODD_EXISTS) THEN ASM_REWRITE_TAC[ODD_EVEN] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GSYM ADD1, POW_0, REAL_MUL_RZERO]);

val COS_0 = store_thm("COS_0",
  “cos(&0) = &1”,
  REWRITE_TAC[cos] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SUM_UNIQ THEN BETA_TAC THEN
  W(MP_TAC o C SPEC SER_0 o rand o rator o snd) THEN
  DISCH_THEN(MP_TAC o SPEC “1:num”) THEN
  REWRITE_TAC[ONE, sum, ADD_CLAUSES] THEN BETA_TAC THEN
  REWRITE_TAC[EVEN, pow, FACT] THEN
  REWRITE_TAC[REAL_ADD_LID, REAL_MUL_RID] THEN
  SUBGOAL_THEN “0 DIV 2 = 0” SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQUE THEN EXISTS_TAC “0:num” THEN
    REWRITE_TAC[MULT_CLAUSES, ADD_CLAUSES] THEN
    REWRITE_TAC[TWO, LESS_0],
    REWRITE_TAC[pow]] THEN
  SUBGOAL_THEN “&1 / &1 = &(SUC 0)” SUBST1_TAC THENL
   [REWRITE_TAC[SYM(ONE)] THEN MATCH_MP_TAC REAL_DIV_REFL THEN
    MATCH_ACCEPT_TAC REAL_10,
    DISCH_THEN MATCH_MP_TAC] THEN
  X_GEN_TAC “n:num” THEN REWRITE_TAC[GSYM LESS_EQ] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
  REWRITE_TAC[GSYM ADD1, POW_0, REAL_MUL_RZERO, ADD_CLAUSES]);

val SIN_CIRCLE = store_thm("SIN_CIRCLE",
  “!x. (sin(x) pow 2) + (cos(x) pow 2) = &1”,
  GEN_TAC THEN CONV_TAC(LAND_CONV(X_BETA_CONV “x:real”)) THEN
  SUBGOAL_THEN “&1 = (\x.(sin(x) pow 2) + (cos(x) pow 2))(&0)” SUBST1_TAC THENL
   [BETA_TAC THEN REWRITE_TAC[SIN_0, COS_0] THEN
    REWRITE_TAC[TWO, POW_0] THEN
    REWRITE_TAC[pow, POW_1] THEN REWRITE_TAC[REAL_ADD_LID, REAL_MUL_LID],
    MATCH_MP_TAC DIFF_ISCONST_ALL THEN X_GEN_TAC “x:real” THEN
    W(MP_TAC o DIFF_CONV o rand o funpow 2 rator o snd) THEN
    DISCH_THEN(MP_TAC o SPEC “x:real”) THEN
    MATCH_MP_TAC(TAUT_CONV “(a <=> b) ==> a ==> b”) THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC[GSYM real_sub, REAL_SUB_0] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC, REAL_MUL_RID] THEN
    AP_TERM_TAC THEN REWRITE_TAC[TWO, SUC_SUB1] THEN
    REWRITE_TAC[POW_1] THEN MATCH_ACCEPT_TAC REAL_MUL_SYM]);

val SIN_BOUND = store_thm("SIN_BOUND",
  “!x. abs(sin x) <= &1”,
  GEN_TAC THEN GEN_REWR_TAC I  [TAUT_CONV “a:bool = ~~a”] THEN
  PURE_ONCE_REWRITE_TAC[REAL_NOT_LE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT1_POW2) THEN
  REWRITE_TAC[REAL_POW2_ABS] THEN
  DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[GSYM REAL_SUB_LT]) THEN
  DISCH_THEN(MP_TAC o C CONJ(SPEC “cos(x)” REAL_LE_SQUARE)) THEN
  REWRITE_TAC[GSYM POW_2] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LTE_ADD) THEN
  REWRITE_TAC[real_sub, GSYM REAL_ADD_ASSOC] THEN
  ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
    “a + (b + c) = (a + c) + b”] THEN
  REWRITE_TAC[SIN_CIRCLE, REAL_ADD_RINV, REAL_LT_REFL]);

val SIN_BOUNDS = store_thm("SIN_BOUNDS",
  “!x. ~(&1) <= sin(x) /\ sin(x) <= &1”,
  GEN_TAC THEN REWRITE_TAC[GSYM ABS_BOUNDS, SIN_BOUND]);

val COS_BOUND = store_thm("COS_BOUND",
  “!x. abs(cos x) <= &1”,
  GEN_TAC THEN GEN_REWR_TAC I  [TAUT_CONV “a:bool = ~~a”] THEN
  PURE_ONCE_REWRITE_TAC[REAL_NOT_LE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT1_POW2) THEN
  REWRITE_TAC[REAL_POW2_ABS] THEN
  DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[GSYM REAL_SUB_LT]) THEN
  DISCH_THEN(MP_TAC o CONJ(SPEC “sin(x)” REAL_LE_SQUARE)) THEN
  REWRITE_TAC[GSYM POW_2] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LET_ADD) THEN
  REWRITE_TAC[real_sub, REAL_ADD_ASSOC, SIN_CIRCLE,
    REAL_ADD_ASSOC, SIN_CIRCLE, REAL_ADD_RINV, REAL_LT_REFL]);

val COS_BOUNDS = store_thm("COS_BOUNDS",
  “!x. ~(&1) <= cos(x) /\ cos(x) <= &1”,
  GEN_TAC THEN REWRITE_TAC[GSYM ABS_BOUNDS, COS_BOUND]);

val SIN_COS_ADD = store_thm("SIN_COS_ADD",
  “!x y. ((sin(x + y) - ((sin(x) * cos(y)) + (cos(x) * sin(y)))) pow 2) +
         ((cos(x + y) - ((cos(x) * cos(y)) - (sin(x) * sin(y)))) pow 2) = &0”,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(X_BETA_CONV “x:real”)) THEN
  W(C SUBGOAL_THEN (SUBST1_TAC o SYM) o hol88Lib.subst[(“&0”,“x:real”)] o snd) THENL
   [BETA_TAC THEN REWRITE_TAC[SIN_0, COS_0] THEN
    REWRITE_TAC[REAL_ADD_LID, REAL_MUL_LZERO, REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_SUB_RZERO, REAL_SUB_REFL] THEN
    REWRITE_TAC[TWO, POW_0, REAL_ADD_LID],
    MATCH_MP_TAC DIFF_ISCONST_ALL THEN GEN_TAC THEN
    W(MP_TAC o DIFF_CONV o rand o funpow 2 rator o snd) THEN
    REDUCE_TAC THEN REWRITE_TAC[POW_1] THEN
    REWRITE_TAC[REAL_MUL_LZERO, REAL_ADD_RID, REAL_MUL_RID] THEN
    DISCH_THEN(MP_TAC o SPEC “x:real”) THEN
    MATCH_MP_TAC(TAUT_CONV “(a <=> b) ==> a ==> b”) THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_NEG_LMUL] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EQ_SUB_LADD] THEN
    REWRITE_TAC[REAL_SUB_LZERO, GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_NEG_RMUL] THEN AP_TERM_TAC THEN
    GEN_REWR_TAC RAND_CONV  [REAL_MUL_SYM] THEN BINOP_TAC THENL
     [REWRITE_TAC[real_sub, REAL_NEG_ADD, REAL_NEGNEG, REAL_NEG_RMUL],
      REWRITE_TAC[GSYM REAL_NEG_RMUL, GSYM real_sub]]]);

val SIN_COS_NEG = store_thm("SIN_COS_NEG",
  “!x. ((sin(~x) + (sin x)) pow 2) +
       ((cos(~x) - (cos x)) pow 2) = &0”,
  GEN_TAC THEN CONV_TAC(LAND_CONV(X_BETA_CONV “x:real”)) THEN
  W(C SUBGOAL_THEN (SUBST1_TAC o SYM) o hol88Lib.subst[(“&0”,“x:real”)] o snd) THENL
   [BETA_TAC THEN REWRITE_TAC[SIN_0, COS_0, REAL_NEG_0] THEN
    REWRITE_TAC[REAL_ADD_LID, REAL_SUB_REFL] THEN
    REWRITE_TAC[TWO, POW_0, REAL_ADD_LID],
    MATCH_MP_TAC DIFF_ISCONST_ALL THEN GEN_TAC THEN
    W(MP_TAC o DIFF_CONV o rand o funpow 2 rator o snd) THEN
    REDUCE_TAC THEN REWRITE_TAC[POW_1] THEN
    DISCH_THEN(MP_TAC o SPEC “x:real”) THEN
    MATCH_MP_TAC(TAUT_CONV “(a <=> b) ==> a ==> b”) THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC[REAL_MUL_RID, real_sub, REAL_NEGNEG, GSYM REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EQ_SUB_LADD] THEN
    REWRITE_TAC[REAL_SUB_LZERO, REAL_NEG_RMUL] THEN AP_TERM_TAC THEN
    GEN_REWR_TAC RAND_CONV  [REAL_MUL_SYM] THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL, REAL_NEG_RMUL] THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_NEG_ADD, REAL_NEGNEG]]);

val SIN_ADD = store_thm("SIN_ADD",
  “!x y. sin(x + y) = (sin(x) * cos(y)) + (cos(x) * sin(y))”,
  REPEAT GEN_TAC THEN MP_TAC(SPECL [“x:real”, “y:real”] SIN_COS_ADD) THEN
  REWRITE_TAC[POW_2, REAL_SUMSQ] THEN REWRITE_TAC[REAL_SUB_0] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]));

val COS_ADD = store_thm("COS_ADD",
  “!x y. cos(x + y) = (cos(x) * cos(y)) - (sin(x) * sin(y))”,
  REPEAT GEN_TAC THEN MP_TAC(SPECL [“x:real”, “y:real”] SIN_COS_ADD) THEN
  REWRITE_TAC[POW_2, REAL_SUMSQ] THEN REWRITE_TAC[REAL_SUB_0] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]));

val SIN_NEG = store_thm("SIN_NEG",
  “!x. sin(~x) = ~(sin(x))”,
  GEN_TAC THEN MP_TAC(SPEC “x:real” SIN_COS_NEG) THEN
  REWRITE_TAC[POW_2, REAL_SUMSQ] THEN REWRITE_TAC[REAL_LNEG_UNIQ] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]));

val COS_NEG = store_thm("COS_NEG",
  “!x. cos(~x) = cos(x)”,
  GEN_TAC THEN MP_TAC(SPEC “x:real” SIN_COS_NEG) THEN
  REWRITE_TAC[POW_2, REAL_SUMSQ] THEN REWRITE_TAC[REAL_SUB_0] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]));

val SIN_DOUBLE = store_thm("SIN_DOUBLE",
  “!x. sin(&2 * x) = &2 * (sin(x) * cos(x))”,
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_DOUBLE, SIN_ADD] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_MUL_SYM);

val COS_DOUBLE = store_thm("COS_DOUBLE",
  “!x. cos(&2 * x) = (cos(x) pow 2) - (sin(x) pow 2)”,
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_DOUBLE, COS_ADD, POW_2]);

(*---------------------------------------------------------------------------*)
(* Show that there's a least positive x with cos(x) = 0; hence define pi     *)
(*---------------------------------------------------------------------------*)

val SIN_PAIRED = store_thm("SIN_PAIRED",
  “!x. (\n. (((~(&1)) pow n) / &(FACT((2 * n) + 1)))
         * (x pow ((2 * n) + 1))) sums (sin x)”,
  GEN_TAC THEN MP_TAC(SPEC “x:real” SIN_CONVERGES) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_PAIR) THEN REWRITE_TAC[GSYM sin] THEN
  BETA_TAC THEN REWRITE_TAC[SUM_2] THEN BETA_TAC THEN
  REWRITE_TAC[GSYM ADD1, EVEN_DOUBLE, REWRITE_RULE[ODD_EVEN] ODD_DOUBLE] THEN
  REWRITE_TAC[REAL_MUL_LZERO, REAL_ADD_LID, SUC_SUB1, MULT_DIV_2]);

val SIN_POS = store_thm("SIN_POS",
  “!x. &0 < x /\ x < &2 ==> &0 < sin(x)”,
  GEN_TAC THEN STRIP_TAC THEN MP_TAC(SPEC “x:real” SIN_PAIRED) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_PAIR) THEN
  REWRITE_TAC[SYM(MATCH_MP SUM_UNIQ (SPEC “x:real” SIN_PAIRED))] THEN
  REWRITE_TAC[SUM_2] THEN BETA_TAC THEN REWRITE_TAC[GSYM ADD1] THEN
  REWRITE_TAC[pow, GSYM REAL_NEG_MINUS1, POW_MINUS1] THEN
  REWRITE_TAC[real_div, GSYM REAL_NEG_LMUL, GSYM real_sub] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN REWRITE_TAC[ADD1] THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP SUM_UNIQ) THEN
  W(C SUBGOAL_THEN SUBST1_TAC o curry mk_eq “&0” o curry mk_comb “sum(0,0)” o
  funpow 2 rand o snd) THENL [REWRITE_TAC[sum], ALL_TAC] THEN
  MATCH_MP_TAC SER_POS_LT THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP SUM_SUMMABLE th]) THEN
  X_GEN_TAC “n:num” THEN DISCH_THEN(K ALL_TAC) THEN BETA_TAC THEN
  REWRITE_TAC[GSYM ADD1, MULT_CLAUSES] THEN
  REWRITE_TAC[TWO, ADD_CLAUSES, pow, FACT, GSYM REAL_MUL] THEN
  REWRITE_TAC[SYM(TWO)] THEN
  REWRITE_TAC[ONE, ADD_CLAUSES, pow, FACT, GSYM REAL_MUL] THEN
  REWRITE_TAC[REAL_SUB_LT] THEN ONCE_REWRITE_TAC[GSYM pow] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LT_RMUL_IMP THEN CONJ_TAC THENL
   [ALL_TAC, MATCH_MP_TAC POW_POS_LT THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC, GSYM POW_2] THEN
  SUBGOAL_THEN “!n. &0 < &(SUC n)” ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_LT, LESS_0], ALL_TAC] THEN
  SUBGOAL_THEN “!n. &0 < &(FACT n)” ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_LT, FACT_LESS], ALL_TAC] THEN
  SUBGOAL_THEN “!n. ~(&(SUC n) = &0)” ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_INJ, NOT_SUC], ALL_TAC] THEN
  SUBGOAL_THEN “!n. ~(&(FACT n) = &0)” ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_POS_NZ THEN
    REWRITE_TAC[REAL_LT, FACT_LESS], ALL_TAC] THEN
  REPEAT(IMP_SUBST_TAC REAL_INV_MUL THEN ASM_REWRITE_TAC[REAL_ENTIRE]) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    “a * (b * (c * (d * e))) =
        (a * (b * e)) * (c * d)”] THEN
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
      curry mk_comb “(&)” o funpow 3 rand o snd) THEN
    REWRITE_TAC[REAL_LT, LESS_SUC_REFL], ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC “&2” THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(REDEPTH_CONV num_CONV) THEN
  REWRITE_TAC[REAL_LE, LESS_EQ_MONO, ZERO_LESS_EQ]);

val COS_PAIRED = store_thm("COS_PAIRED",
  “!x. (\n. (((~(&1)) pow n) / &(FACT(2 * n)))
         * (x pow (2 * n))) sums (cos x)”,
  GEN_TAC THEN MP_TAC(SPEC “x:real” COS_CONVERGES) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_PAIR) THEN REWRITE_TAC[GSYM cos] THEN
  BETA_TAC THEN REWRITE_TAC[SUM_2] THEN BETA_TAC THEN
  REWRITE_TAC[GSYM ADD1, EVEN_DOUBLE, REWRITE_RULE[ODD_EVEN] ODD_DOUBLE] THEN
  REWRITE_TAC[REAL_MUL_LZERO, REAL_ADD_RID, MULT_DIV_2]);

val COS_2 = store_thm("COS_2",
  “cos(&2) < &0”,
  GEN_REWR_TAC LAND_CONV  [GSYM REAL_NEGNEG] THEN
  REWRITE_TAC[REAL_NEG_LT0] THEN MP_TAC(SPEC “&2” COS_PAIRED) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_NEG) THEN BETA_TAC THEN
  DISCH_TAC THEN FIRST_ASSUM(SUBST1_TAC o MATCH_MP SUM_UNIQ) THEN
  MATCH_MP_TAC REAL_LT_TRANS THEN
  EXISTS_TAC “sum(0,3) (\n. ~((((~(&1)) pow n) / &(FACT(2 * n)))
                * (&2 pow (2 * n))))” THEN CONJ_TAC THENL
   [REWRITE_TAC[num_CONV “3:num”, sum, SUM_2] THEN BETA_TAC THEN
    REWRITE_TAC[MULT_CLAUSES, ADD_CLAUSES, pow, FACT] THEN
    REWRITE_TAC[REAL_MUL_RID, POW_1, POW_2, GSYM REAL_NEG_RMUL] THEN
    IMP_SUBST_TAC REAL_DIV_REFL THEN REWRITE_TAC[REAL_NEGNEG, REAL_10] THEN
    REDUCE_TAC THEN
    REWRITE_TAC[num_CONV “4:num”, num_CONV “3:num”, FACT, pow] THEN
    REWRITE_TAC[SYM(num_CONV “4:num”), SYM(num_CONV “3:num”)] THEN
    REWRITE_TAC[TWO, ONE, FACT, pow] THEN
    REWRITE_TAC[SYM(ONE), SYM(TWO)] THEN
    REWRITE_TAC[REAL_MUL] THEN REDUCE_TAC THEN
    REWRITE_TAC[real_div, REAL_NEG_LMUL, REAL_NEGNEG, REAL_MUL_LID] THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL, REAL_ADD_ASSOC] THEN
    REWRITE_TAC[GSYM real_sub, REAL_SUB_LT] THEN
    SUBGOAL_THEN “inv(&2) * &4 = &1 + &1” SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_EQ_LMUL_IMP THEN EXISTS_TAC “&2” THEN
      REWRITE_TAC[REAL_INJ] THEN REDUCE_TAC THEN
      REWRITE_TAC[REAL_ADD, REAL_MUL] THEN REDUCE_TAC THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN
      SUBGOAL_THEN “&2 * inv(&2) = &1” SUBST1_TAC THEN
      REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC REAL_MUL_RINV THEN
      REWRITE_TAC[REAL_INJ] THEN REDUCE_TAC,
      REWRITE_TAC[REAL_MUL_LID, REAL_ADD_ASSOC] THEN
      REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
      MATCH_MP_TAC REAL_LT_1 THEN REWRITE_TAC[REAL_LE, REAL_LT] THEN
      REDUCE_TAC], ALL_TAC] THEN
  MATCH_MP_TAC SER_POS_LT_PAIR THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP SUM_SUMMABLE th]) THEN
  X_GEN_TAC “d:num” THEN BETA_TAC THEN
  REWRITE_TAC[POW_ADD, POW_MINUS1, REAL_MUL_RID] THEN
  REWRITE_TAC[num_CONV “3:num”, pow] THEN REWRITE_TAC[SYM(num_CONV “3:num”)] THEN
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
    REWRITE_TAC[num_CONV “3:num”, ADD_CLAUSES] THEN
    MATCH_MP_TAC POW_POS_LT THEN REWRITE_TAC[REAL_LT] THEN
    REDUCE_TAC] THEN
  REWRITE_TAC[TWO, ADD_CLAUSES, FACT] THEN
  REWRITE_TAC[SYM(TWO)] THEN
  REWRITE_TAC[ONE, ADD_CLAUSES, FACT] THEN
  REWRITE_TAC[SYM(ONE)] THEN
  SUBGOAL_THEN “!n. &0 < &(SUC n)” ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_LT, LESS_0], ALL_TAC] THEN
  SUBGOAL_THEN “!n. &0 < &(FACT n)” ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_LT, FACT_LESS], ALL_TAC] THEN
  SUBGOAL_THEN “!n. ~(&(SUC n) = &0)” ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_INJ, NOT_SUC], ALL_TAC] THEN
  SUBGOAL_THEN “!n. ~(&(FACT n) = &0)” ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_POS_NZ THEN
    REWRITE_TAC[REAL_LT, FACT_LESS], ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL] THEN
  REPEAT(IMP_SUBST_TAC REAL_INV_MUL THEN ASM_REWRITE_TAC[REAL_ENTIRE]) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    “a * (b * (c * d)) = (a * (b * d)) * c”] THEN
  GEN_REWR_TAC RAND_CONV  [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LT_RMUL_IMP THEN CONJ_TAC THENL
   [ALL_TAC,
    MATCH_MP_TAC REAL_INV_POS THEN REWRITE_TAC[REAL_LT, FACT_LESS]] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  IMP_SUBST_TAC ((CONV_RULE(RAND_CONV SYM_CONV) o SPEC_ALL) REAL_INV_MUL) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_LT_1 THEN
  REWRITE_TAC[POW_2, REAL_MUL, REAL_LE, REAL_LT] THEN REDUCE_TAC THEN
  REWRITE_TAC[num_CONV “4:num”, num_CONV “3:num”,
              MULT_CLAUSES, ADD_CLAUSES] THEN
  REWRITE_TAC[LESS_MONO_EQ] THEN
  REWRITE_TAC[TWO, ADD_CLAUSES, MULT_CLAUSES] THEN
  REWRITE_TAC[ONE, LESS_MONO_EQ, LESS_0]);

val COS_ISZERO = store_thm("COS_ISZERO",
  “?!x. &0 <= x /\ x <= &2 /\ (cos x = &0)”,
  REWRITE_TAC[EXISTS_UNIQUE_DEF] THEN BETA_TAC THEN
  W(C SUBGOAL_THEN ASSUME_TAC o hd o strip_conj o snd) THENL
   [MATCH_MP_TAC IVT2 THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE, ZERO_LESS_EQ],
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ACCEPT_TAC COS_2,
      REWRITE_TAC[COS_0, REAL_LE_01],
      X_GEN_TAC “x:real” THEN DISCH_THEN(K ALL_TAC) THEN
      MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC “~(sin x)” THEN
      REWRITE_TAC[DIFF_COS]],
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN
    MAP_EVERY X_GEN_TAC [“x1:real”, “x2:real”] THEN
    GEN_REWR_TAC I  [TAUT_CONV “a:bool <=> ~~a”] THEN
    PURE_REWRITE_TAC[NOT_IMP] THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [“x1:real”, “x2:real”] REAL_LT_TOTAL) THEN
    SUBGOAL_THEN “(!x. cos differentiable x) /\ (!x. cos contl x)”
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN GEN_TAC THENL
       [REWRITE_TAC[differentiable], MATCH_MP_TAC DIFF_CONT] THEN
      EXISTS_TAC “~(sin x)” THEN REWRITE_TAC[DIFF_COS], ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN DISJ_CASES_TAC THENL
     [MP_TAC(SPECL [“cos”, “x1:real”, “x2:real”] ROLLE),
      MP_TAC(SPECL [“cos”, “x2:real”, “x1:real”] ROLLE)] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN “x:real” MP_TAC) THEN REWRITE_TAC[CONJ_ASSOC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o CONJ(SPEC “x:real” DIFF_COS)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_UNIQ) THEN
    REWRITE_TAC[REAL_NEG_EQ0] THEN MATCH_MP_TAC REAL_POS_NZ THEN
    MATCH_MP_TAC SIN_POS THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC “x1:real” THEN
        ASM_REWRITE_TAC[],
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC “x2:real” THEN
        ASM_REWRITE_TAC[]],
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC “x2:real” THEN
        ASM_REWRITE_TAC[],
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC “x1:real” THEN
        ASM_REWRITE_TAC[]]]]);

val pi = new_definition("pi",
  Term `pi = &2 * @x. &0 <= x /\ x <= &2 /\ (cos x = &0)`);

(*---------------------------------------------------------------------------*)
(* Periodicity and related properties of the trig functions                  *)
(*---------------------------------------------------------------------------*)

val PI2 = store_thm("PI2",
  “pi / &2 = @x. &0 <= x /\ x <= &2 /\ (cos(x) = &0)”,
  REWRITE_TAC[pi, real_div] THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    “(a * b) * c = (c * a) * b”] THEN
  IMP_SUBST_TAC REAL_MUL_LINV THEN REWRITE_TAC[REAL_INJ] THEN
  REDUCE_TAC THEN REWRITE_TAC[REAL_MUL_LID]);

val COS_PI2 = store_thm("COS_PI2",
  “cos(pi / &2) = &0”,
  MP_TAC(SELECT_RULE (EXISTENCE COS_ISZERO)) THEN
  REWRITE_TAC[GSYM PI2] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]));

val PI2_BOUNDS = store_thm("PI2_BOUNDS",
  “&0 < (pi / &2) /\ (pi / &2) < &2”,
  MP_TAC(SELECT_RULE (EXISTENCE COS_ISZERO)) THEN
  REWRITE_TAC[GSYM PI2] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL
   [DISCH_TAC THEN MP_TAC COS_0 THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM REAL_10],
    DISCH_TAC THEN MP_TAC COS_PI2 THEN FIRST_ASSUM SUBST1_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
    MATCH_ACCEPT_TAC COS_2]);

val PI_POS = store_thm("PI_POS",
  “&0 < pi”,
  GEN_REWR_TAC RAND_CONV  [GSYM REAL_HALF_DOUBLE] THEN
  MATCH_MP_TAC REAL_LT_ADD THEN REWRITE_TAC[PI2_BOUNDS]);

val SIN_PI2 = store_thm("SIN_PI2",
  “sin(pi / &2) = &1”,
  MP_TAC(SPEC “pi / &2” SIN_CIRCLE) THEN
  REWRITE_TAC[COS_PI2, POW_2, REAL_MUL_LZERO, REAL_ADD_RID] THEN
  GEN_REWR_TAC (LAND_CONV o RAND_CONV)  [GSYM REAL_MUL_LID] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  REWRITE_TAC[GSYM REAL_DIFFSQ, REAL_ENTIRE] THEN
  DISCH_THEN DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[REAL_LNEG_UNIQ] THEN DISCH_THEN(MP_TAC o AP_TERM “$real_neg”) THEN
  REWRITE_TAC[REAL_NEGNEG] THEN DISCH_TAC THEN
  MP_TAC REAL_LT_01 THEN POP_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_GT THEN
  REWRITE_TAC[REAL_NEG_LT0] THEN MATCH_MP_TAC SIN_POS THEN
  REWRITE_TAC[PI2_BOUNDS]);

val COS_PI = store_thm("COS_PI",
  “cos(pi) = ~(&1)”,
  MP_TAC(SPECL [“pi / &2”, “pi / &2”] COS_ADD) THEN
  REWRITE_TAC[SIN_PI2, COS_PI2, REAL_MUL_LZERO, REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_SUB_LZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN REWRITE_TAC[REAL_DOUBLE] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
  REWRITE_TAC[REAL_INJ] THEN REDUCE_TAC);

val SIN_PI = store_thm("SIN_PI",
  “sin(pi) = &0”,
  MP_TAC(SPECL [“pi / &2”, “pi / &2”] SIN_ADD) THEN
  REWRITE_TAC[COS_PI2, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_ADD_LID] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_DOUBLE] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC REAL_DIV_LMUL THEN
  REWRITE_TAC[REAL_INJ] THEN REDUCE_TAC);

val SIN_COS = store_thm("SIN_COS",
  “!x. sin(x) = cos((pi / &2) - x)”,
  GEN_TAC THEN REWRITE_TAC[real_sub, COS_ADD] THEN
  REWRITE_TAC[SIN_PI2, COS_PI2, REAL_MUL_LZERO] THEN
  REWRITE_TAC[REAL_ADD_LID, REAL_MUL_LID] THEN
  REWRITE_TAC[SIN_NEG, REAL_NEGNEG]);

val COS_SIN = store_thm("COS_SIN",
  “!x. cos(x) = sin((pi / &2) - x)”,
  GEN_TAC THEN REWRITE_TAC[real_sub, SIN_ADD] THEN
  REWRITE_TAC[SIN_PI2, COS_PI2, REAL_MUL_LZERO] THEN
  REWRITE_TAC[REAL_MUL_LID, REAL_ADD_RID] THEN
  REWRITE_TAC[COS_NEG]);

val SIN_PERIODIC_PI = store_thm("SIN_PERIODIC_PI",
  “!x. sin(x + pi) = ~(sin(x))”,
  GEN_TAC THEN REWRITE_TAC[SIN_ADD, SIN_PI, COS_PI] THEN
  REWRITE_TAC[REAL_MUL_RZERO, REAL_ADD_RID, GSYM REAL_NEG_RMUL] THEN
  REWRITE_TAC[REAL_MUL_RID]);

val COS_PERIODIC_PI = store_thm("COS_PERIODIC_PI",
  “!x. cos(x + pi) = ~(cos(x))”,
  GEN_TAC THEN REWRITE_TAC[COS_ADD, SIN_PI, COS_PI] THEN
  REWRITE_TAC[REAL_MUL_RZERO, REAL_SUB_RZERO, GSYM REAL_NEG_RMUL] THEN
  REWRITE_TAC[REAL_MUL_RID]);

val SIN_PERIODIC = store_thm("SIN_PERIODIC",
  “!x. sin(x + (&2 * pi)) = sin(x)”,
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_DOUBLE, REAL_ADD_ASSOC] THEN
  REWRITE_TAC[SIN_PERIODIC_PI, REAL_NEGNEG]);

val COS_PERIODIC = store_thm("COS_PERIODIC",
  “!x. cos(x + (&2 * pi)) = cos(x)”,
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_DOUBLE, REAL_ADD_ASSOC] THEN
  REWRITE_TAC[COS_PERIODIC_PI, REAL_NEGNEG]);

val COS_NPI = store_thm("COS_NPI",
  “!n. cos(&n * pi) = ~(&1) pow n”,
  INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO, COS_0, pow] THEN
  REWRITE_TAC[ADD1, GSYM REAL_ADD, REAL_RDISTRIB, COS_ADD] THEN
  REWRITE_TAC[REAL_MUL_LID, SIN_PI, REAL_MUL_RZERO, REAL_SUB_RZERO] THEN
  ASM_REWRITE_TAC[COS_PI] THEN
  MATCH_ACCEPT_TAC REAL_MUL_SYM);

val SIN_NPI = store_thm("SIN_NPI",
  “!n. sin(&n * pi) = &0”,
  INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO, SIN_0, pow] THEN
  REWRITE_TAC[ADD1, GSYM REAL_ADD, REAL_RDISTRIB, SIN_ADD] THEN
  REWRITE_TAC[REAL_MUL_LID, SIN_PI, REAL_MUL_RZERO, REAL_ADD_RID] THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO]);

val SIN_POS_PI2 = store_thm("SIN_POS_PI2",
  “!x. &0 < x /\ x < pi / &2 ==> &0 < sin(x)”,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SIN_POS THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_TRANS THEN
  EXISTS_TAC “pi / &2” THEN ASM_REWRITE_TAC[PI2_BOUNDS]);

val COS_POS_PI2 = store_thm("COS_POS_PI2",
  “!x. &0 < x /\ x < pi / &2 ==> &0 < cos(x)”,
  GEN_TAC THEN STRIP_TAC THEN
  GEN_REWR_TAC I  [TAUT_CONV “a:bool = ~~a”] THEN
  PURE_REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [“cos”, “&0”, “x:real”, “&0”] IVT2) THEN
  ASM_REWRITE_TAC[COS_0, REAL_LE_01, NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
    X_GEN_TAC “z:real” THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC “~(sin z)” THEN
    REWRITE_TAC[DIFF_COS],
    DISCH_THEN(X_CHOOSE_TAC “z:real”) THEN
    MP_TAC(CONJUNCT2 (CONV_RULE EXISTS_UNIQUE_CONV COS_ISZERO)) THEN
    DISCH_THEN(MP_TAC o SPECL [“z:real”, “pi / &2”]) THEN
    ASM_REWRITE_TAC[COS_PI2] THEN REWRITE_TAC[NOT_IMP] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC “x:real” THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC “pi / &2” THEN ASM_REWRITE_TAC[] THEN CONJ_TAC,
      ALL_TAC,
      ALL_TAC,
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC “x < pi / &2” THEN
      ASM_REWRITE_TAC[REAL_NOT_LT]] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[PI2_BOUNDS]]);

val COS_POS_PI = store_thm("COS_POS_PI",
  “!x. ~(pi / &2) < x /\ x < pi / &2 ==> &0 < cos(x)”,
  GEN_TAC THEN STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
        (SPECL [“x:real”, “&0”] REAL_LT_TOTAL) THENL
   [ASM_REWRITE_TAC[COS_0, REAL_LT_01],
    ONCE_REWRITE_TAC[GSYM COS_NEG] THEN MATCH_MP_TAC COS_POS_PI2 THEN
    ONCE_REWRITE_TAC[GSYM REAL_NEG_LT0] THEN ASM_REWRITE_TAC[REAL_NEGNEG] THEN
    ONCE_REWRITE_TAC[GSYM REAL_LT_NEG] THEN ASM_REWRITE_TAC[REAL_NEGNEG],
    MATCH_MP_TAC COS_POS_PI2 THEN ASM_REWRITE_TAC[]]);

val SIN_POS_PI = store_thm("SIN_POS_PI",
  “!x. &0 < x /\ x < pi ==> &0 < sin(x)”,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SIN_COS] THEN ONCE_REWRITE_TAC[GSYM COS_NEG] THEN
  REWRITE_TAC[REAL_NEG_SUB] THEN
  MATCH_MP_TAC COS_POS_PI THEN
  REWRITE_TAC[REAL_LT_SUB_LADD, REAL_LT_SUB_RADD] THEN
  ASM_REWRITE_TAC[REAL_HALF_DOUBLE, REAL_ADD_LINV]);

val COS_POS_PI2_LE = store_thm("COS_POS_PI2_LE",
  “!x. &0 <= x /\ x <= (pi / &2) ==> &0 <= cos(x)”,
  GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN DISJ_CASES_TAC) THEN
  ASM_REWRITE_TAC[COS_PI2] THEN
  TRY(DISJ1_TAC THEN MATCH_MP_TAC COS_POS_PI2 THEN
      ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  SUBST1_TAC(SYM(ASSUME “&0 = x”)) THEN
  REWRITE_TAC[COS_0, REAL_LT_01]);

val COS_POS_PI_LE = store_thm("COS_POS_PI_LE",
  “!x. ~(pi / &2) <= x /\ x <= (pi / &2) ==> &0 <= cos(x)”,
  GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN DISJ_CASES_TAC) THEN
  ASM_REWRITE_TAC[COS_PI2] THENL
   [DISJ1_TAC THEN MATCH_MP_TAC COS_POS_PI THEN ASM_REWRITE_TAC[],
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[COS_NEG, COS_PI2, REAL_LT_01]]);

val SIN_POS_PI2_LE = store_thm("SIN_POS_PI2_LE",
  “!x. &0 <= x /\ x <= (pi / &2) ==> &0 <= sin(x)”,
  GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN DISJ_CASES_TAC) THEN
  ASM_REWRITE_TAC[SIN_PI2, REAL_LT_01] THENL
   [DISJ1_TAC THEN MATCH_MP_TAC SIN_POS_PI2 THEN ASM_REWRITE_TAC[],
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[SIN_0],
    MP_TAC PI2_BOUNDS THEN ASM_REWRITE_TAC[REAL_LT_REFL]]);

val SIN_POS_PI_LE = store_thm("SIN_POS_PI_LE",
  “!x. &0 <= x /\ x <= pi ==> &0 <= sin(x)”,
  GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN DISJ_CASES_TAC) THEN
  ASM_REWRITE_TAC[SIN_PI] THENL
   [DISJ1_TAC THEN MATCH_MP_TAC SIN_POS_PI THEN ASM_REWRITE_TAC[],
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[SIN_0]]);

val COS_TOTAL = store_thm("COS_TOTAL",
  “!y. ~(&1) <= y /\ y <= &1 ==> ?!x. &0 <= x /\ x <= pi /\ (cos(x) = y)”,
  GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC EXISTS_UNIQUE_CONV THEN CONJ_TAC THENL
   [MATCH_MP_TAC IVT2 THEN ASM_REWRITE_TAC[COS_0, COS_PI] THEN
    REWRITE_TAC[MATCH_MP REAL_LT_IMP_LE PI_POS] THEN
    GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC “~(sin x)” THEN
    REWRITE_TAC[DIFF_COS],
    MAP_EVERY X_GEN_TAC [“x1:real”, “x2:real”] THEN STRIP_TAC THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
         (SPECL [“x1:real”, “x2:real”] REAL_LT_TOTAL) THENL
     [FIRST_ASSUM ACCEPT_TAC,
      MP_TAC(SPECL [“cos”, “x1:real”, “x2:real”] ROLLE),
      MP_TAC(SPECL [“cos”, “x2:real”, “x1:real”] ROLLE)]] THEN
  ASM_REWRITE_TAC[] THEN
  (W(C SUBGOAL_THEN (fn t => REWRITE_TAC[t]) o funpow 2
                    (fst o dest_imp) o snd) THENL
    [CONJ_TAC THEN X_GEN_TAC “x:real” THEN DISCH_THEN(K ALL_TAC) THEN
     TRY(MATCH_MP_TAC DIFF_CONT) THEN REWRITE_TAC[differentiable] THEN
     EXISTS_TAC “~(sin x)” THEN REWRITE_TAC[DIFF_COS], ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN “x:real” STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC “(cos diffl &0)(x)” THEN
  DISCH_THEN(MP_TAC o CONJ (SPEC “x:real” DIFF_COS)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_UNIQ) THEN
  REWRITE_TAC[REAL_NEG_EQ0] THEN DISCH_TAC THEN
  MP_TAC(SPEC “x:real” SIN_POS_PI) THEN
  ASM_REWRITE_TAC[REAL_LT_REFL] THEN
  CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC “x1:real”,
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC “x2:real”,
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC “x2:real”,
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC “x1:real”] THEN
  ASM_REWRITE_TAC[]);

val SIN_TOTAL = store_thm("SIN_TOTAL",
  “!y. ~(&1) <= y /\ y <= &1 ==>
        ?!x.  ~(pi / &2) <= x /\ x <= pi / &2 /\ (sin(x) = y)”,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN “!x. ~(pi / &2) <= x /\ x <= pi / &2 /\ (sin(x) = y)
                           <=>
                       &0 <= (x + pi / &2) /\
                       (x + pi / &2) <= pi  /\
                       (cos(x + pi / &2) = ~y)”
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
  MP_TAC(Q.SPEC ‘~y’ COS_TOTAL) THEN ASM_REWRITE_TAC[REAL_LE_NEG] THEN
  ONCE_REWRITE_TAC[GSYM REAL_LE_NEG] THEN ASM_REWRITE_TAC[REAL_NEGNEG] THEN
  REWRITE_TAC[REAL_LE_NEG] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
  DISCH_THEN(curry op THEN CONJ_TAC o MP_TAC) THENL
   [DISCH_THEN(X_CHOOSE_TAC “x:real” o CONJUNCT1) THEN
    EXISTS_TAC “x - pi / &2” THEN ASM_REWRITE_TAC[REAL_SUB_ADD],
    POP_ASSUM(K ALL_TAC) THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    REWRITE_TAC[REAL_EQ_RADD]]);

val COS_ZERO_LEMMA = store_thm("COS_ZERO_LEMMA",
  “!x. &0 <= x /\ (cos(x) = &0) ==>
      ?n. ~EVEN n /\ (x = &n * (pi / &2))”,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC “x:real” (MATCH_MP REAL_ARCH_LEAST PI_POS)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN “n:num” STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN “&0 <= x - &n * pi /\ (x - &n * pi) <= pi /\
                (cos(x - &n * pi) = &0)” ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_LE] THEN
    REWRITE_TAC[REAL_LE_SUB_RADD] THEN
    REWRITE_TAC[real_sub, COS_ADD, SIN_NEG, COS_NEG, SIN_NPI, COS_NPI] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO, REAL_ADD_LID] THEN
    REWRITE_TAC[REAL_NEG_RMUL, REAL_NEGNEG, REAL_MUL_RZERO] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN UNDISCH_TAC “x < &(SUC n) * pi” THEN
    REWRITE_TAC[ADD1] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    REWRITE_TAC[GSYM REAL_ADD, REAL_RDISTRIB, REAL_MUL_LID],
    MP_TAC(SPEC “&0” COS_TOTAL) THEN
    REWRITE_TAC[REAL_LE_01, REAL_NEG_LE0] THEN
    DISCH_THEN(MP_TAC o CONV_RULE EXISTS_UNIQUE_CONV) THEN
    DISCH_THEN(MP_TAC o SPECL [“x - &n * pi”, “pi / &2”] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[COS_PI2] THEN
    W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN MP_TAC PI2_BOUNDS THEN
      REWRITE_TAC[REAL_LT_HALF1, REAL_LT_HALF2] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[],
      DISCH_THEN(fn th => REWRITE_TAC[th])] THEN
    REWRITE_TAC[REAL_EQ_SUB_RADD] THEN DISCH_TAC THEN
    EXISTS_TAC “SUC(2 * n)” THEN REWRITE_TAC[EVEN_ODD, ODD_DOUBLE] THEN
    REWRITE_TAC[ADD1, GSYM REAL_ADD, GSYM REAL_MUL] THEN
    REWRITE_TAC[REAL_RDISTRIB, REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    REWRITE_TAC[REAL_INJ] THEN REDUCE_TAC]);

val SIN_ZERO_LEMMA = store_thm("SIN_ZERO_LEMMA",
  “!x. &0 <= x /\ (sin(x) = &0) ==>
        ?n. EVEN n /\ (x = &n * (pi / &2))”,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC “x + pi / &2” COS_ZERO_LEMMA) THEN
  W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC “x:real” THEN
      ASM_REWRITE_TAC[REAL_LE_ADDR] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      REWRITE_TAC[PI2_BOUNDS],
      ASM_REWRITE_TAC[COS_ADD, COS_PI2, REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
      MATCH_ACCEPT_TAC REAL_SUB_REFL],
    DISCH_THEN(fn th => REWRITE_TAC[th])] THEN
  DISCH_THEN(X_CHOOSE_THEN “n:num” STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC “n:num” ODD_EXISTS) THEN ASM_REWRITE_TAC[ODD_EVEN] THEN
  DISCH_THEN(X_CHOOSE_THEN “m:num” SUBST_ALL_TAC) THEN
  EXISTS_TAC “2 * m:num” THEN REWRITE_TAC[EVEN_DOUBLE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_EQ_SUB_LADD]) THEN
  FIRST_ASSUM SUBST1_TAC THEN
  REWRITE_TAC[ADD1, GSYM REAL_ADD, REAL_RDISTRIB, REAL_MUL_LID] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[REAL_ADD_SYM] REAL_ADD_SUB]);

val COS_ZERO = store_thm("COS_ZERO",
  “!x. (cos(x) = &0) <=> (?n. ~EVEN n /\ (x = &n * (pi / &2))) \/
                         (?n. ~EVEN n /\ (x = ~(&n * (pi / &2))))”,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN DISJ_CASES_TAC (SPECL [“&0”, “x:real”] REAL_LE_TOTAL) THENL
     [DISJ1_TAC THEN MATCH_MP_TAC COS_ZERO_LEMMA THEN ASM_REWRITE_TAC[],
      DISJ2_TAC THEN REWRITE_TAC[GSYM REAL_NEG_EQ] THEN
      MATCH_MP_TAC COS_ZERO_LEMMA THEN ASM_REWRITE_TAC[COS_NEG] THEN
      ONCE_REWRITE_TAC[GSYM REAL_LE_NEG] THEN
      ASM_REWRITE_TAC[REAL_NEGNEG, REAL_NEG_0]],
    DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_TAC “n:num”)) THEN
    ASM_REWRITE_TAC[COS_NEG] THEN MP_TAC(SPEC “n:num” ODD_EXISTS) THEN
    ASM_REWRITE_TAC[ODD_EVEN] THEN DISCH_THEN(X_CHOOSE_THEN “m:num” SUBST1_TAC) THEN
    REWRITE_TAC[ADD1] THEN SPEC_TAC(“m:num”,“m:num”) THEN INDUCT_TAC THEN
    REWRITE_TAC[MULT_CLAUSES, ADD_CLAUSES, REAL_MUL_LID, COS_PI2] THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN ONCE_REWRITE_TAC[GSYM REAL_ADD] THEN
    REWRITE_TAC[REAL_RDISTRIB] THEN REWRITE_TAC[COS_ADD] THEN
    REWRITE_TAC[GSYM REAL_DOUBLE, REAL_HALF_DOUBLE] THEN
    ASM_REWRITE_TAC[COS_PI, SIN_PI, REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
    REWRITE_TAC[REAL_SUB_RZERO]]);

val SIN_ZERO = store_thm("SIN_ZERO",
  “!x. (sin(x) = &0) <=> (?n. EVEN n /\ (x = &n * (pi / &2))) \/
                         (?n. EVEN n /\ (x = ~(&n * (pi / &2))))”,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN DISJ_CASES_TAC (SPECL [“&0”, “x:real”] REAL_LE_TOTAL) THENL
     [DISJ1_TAC THEN MATCH_MP_TAC SIN_ZERO_LEMMA THEN ASM_REWRITE_TAC[],
      DISJ2_TAC THEN REWRITE_TAC[GSYM REAL_NEG_EQ] THEN
      MATCH_MP_TAC SIN_ZERO_LEMMA THEN
      ASM_REWRITE_TAC[SIN_NEG, REAL_NEG_0, REAL_NEG_GE0]],
    DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_TAC “n:num”)) THEN
    ASM_REWRITE_TAC[SIN_NEG, REAL_NEG_EQ0] THEN
    MP_TAC(SPEC “n:num” EVEN_EXISTS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN “m:num” SUBST1_TAC) THEN
    REWRITE_TAC[GSYM REAL_MUL] THEN
    ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
      “(a * b) * c = b * (a * c)”] THEN
    REWRITE_TAC[GSYM REAL_DOUBLE, REAL_HALF_DOUBLE, SIN_NPI]]);

(*---------------------------------------------------------------------------*)
(* Tangent                                                                   *)
(*---------------------------------------------------------------------------*)

val tan = new_definition("tan",
  “tan(x) = sin(x) / cos(x)”);

val TAN_0 = store_thm("TAN_0",
  “tan(&0) = &0”,
  REWRITE_TAC[tan, SIN_0, REAL_DIV_LZERO]);

val TAN_PI = store_thm("TAN_PI",
  “tan(pi) = &0”,
  REWRITE_TAC[tan, SIN_PI, REAL_DIV_LZERO]);

val TAN_NPI = store_thm("TAN_NPI",
  “!n. tan(&n * pi) = &0”,
  GEN_TAC THEN REWRITE_TAC[tan, SIN_NPI, REAL_DIV_LZERO]);

val TAN_NEG = store_thm("TAN_NEG",
  “!x. tan(~x) = ~(tan x)”,
  GEN_TAC THEN REWRITE_TAC[tan, SIN_NEG, COS_NEG] THEN
  REWRITE_TAC[real_div, REAL_NEG_LMUL]);

val TAN_PERIODIC = store_thm("TAN_PERIODIC",
  “!x. tan(x + &2 * pi) = tan(x)”,
  GEN_TAC THEN REWRITE_TAC[tan, SIN_PERIODIC, COS_PERIODIC]);

val TAN_ADD = store_thm("TAN_ADD",
  “!x y. ~(cos(x) = &0) /\ ~(cos(y) = &0) /\ ~(cos(x + y) = &0) ==>
           (tan(x + y) = (tan(x) + tan(y)) / (&1 - tan(x) * tan(y)))”,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tan] THEN
  MP_TAC(SPECL [“cos(x) * cos(y)”,
                “&1 - (sin(x) / cos(x)) * (sin(y) / cos(y))”]
         REAL_DIV_MUL2) THEN ASM_REWRITE_TAC[REAL_ENTIRE] THEN
  W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
   [DISCH_THEN(MP_TAC o AP_TERM “$* (cos(x) * cos(y))”) THEN
    REWRITE_TAC[real_div, REAL_SUB_LDISTRIB, GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_MUL_RID, REAL_MUL_RZERO] THEN
    UNDISCH_TAC “~(cos(x + y) = &0)” THEN
    MATCH_MP_TAC(TAUT_CONV “(a <=> b) ==> a ==> b”) THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[COS_ADD] THEN AP_TERM_TAC,
    DISCH_THEN(fn th => DISCH_THEN(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(fn th => ONCE_REWRITE_TAC[th]) THEN BINOP_TAC THENL
     [REWRITE_TAC[real_div, REAL_LDISTRIB, GSYM REAL_MUL_ASSOC] THEN
      REWRITE_TAC[SIN_ADD] THEN BINOP_TAC THENL
       [ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
          “a * (b * (c * d)) = (d * a) * (c * b)”] THEN
        IMP_SUBST_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[REAL_MUL_LID],
        ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
          “a * (b * (c * d)) = (d * b) * (a * c)”] THEN
        IMP_SUBST_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[REAL_MUL_LID]],
      REWRITE_TAC[COS_ADD, REAL_SUB_LDISTRIB, REAL_MUL_RID] THEN
      AP_TERM_TAC THEN REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC]]] THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    “a * (b * (c * (d * (e * f)))) =
        (f * b) * ((d * a) * (c * e))”] THEN
  REPEAT(IMP_SUBST_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[REAL_MUL_LID]);

val TAN_DOUBLE = store_thm("TAN_DOUBLE",
  “!x. ~(cos(x) = &0) /\ ~(cos(&2 * x) = &0) ==>
            (tan(&2 * x) = (&2 * tan(x)) / (&1 - (tan(x) pow 2)))”,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [“x:real”, “x:real”] TAN_ADD) THEN
  ASM_REWRITE_TAC[REAL_DOUBLE, POW_2]);

val TAN_POS_PI2 = store_thm("TAN_POS_PI2",
  “!x. &0 < x /\ x < pi / &2 ==> &0 < tan(x)”,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[tan, real_div] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SIN_POS_PI2,
    MATCH_MP_TAC REAL_INV_POS THEN MATCH_MP_TAC COS_POS_PI2] THEN
  ASM_REWRITE_TAC[]);

Theorem DIFF_TAN[difftool]:
  !x. ~(cos(x) = &0) ==> (tan diffl inv(cos(x) pow 2))(x)
Proof
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(DIFF_CONV “\x. sin(x) / cos(x)”) THEN
  DISCH_THEN(MP_TAC o SPEC “x:real”) THEN ASM_REWRITE_TAC[REAL_MUL_RID] THEN
  REWRITE_TAC[GSYM tan, GSYM REAL_NEG_LMUL, REAL_NEGNEG, real_sub] THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[GSYM POW_2, SIN_CIRCLE, GSYM REAL_INV_1OVER]
QED

Theorem TAN_TOTAL_LEMMA :
  !y. &0 < y ==> ?x. &0 < x /\ x < pi / &2 /\ y < tan(x)
Proof
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN “((\x. cos(x) / sin(x)) -> &0) (pi / &2)”
  MP_TAC THENL
   [SUBST1_TAC(SYM(SPEC “&1” REAL_DIV_LZERO)) THEN
    CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN MATCH_MP_TAC LIM_DIV THEN
    REWRITE_TAC[REAL_10] THEN CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
    SUBST1_TAC(SYM COS_PI2) THEN SUBST1_TAC(SYM SIN_PI2) THEN
    REWRITE_TAC[GSYM CONTL_LIM] THEN CONJ_TAC THEN MATCH_MP_TAC DIFF_CONT THENL
     [EXISTS_TAC “~(sin(pi / &2))”,
      EXISTS_TAC “cos(pi / &2)”] THEN
    REWRITE_TAC[DIFF_SIN, DIFF_COS], ALL_TAC] THEN
  REWRITE_TAC[LIM] THEN DISCH_THEN(MP_TAC o SPEC “inv(y)”) THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_INV_POS th]) THEN
  BETA_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN “d:real” STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [“d:real”, “pi / &2”] REAL_DOWN2) THEN
  ASM_REWRITE_TAC[PI2_BOUNDS] THEN
  DISCH_THEN(X_CHOOSE_THEN “e:real” STRIP_ASSUME_TAC) THEN
  EXISTS_TAC “(pi / &2) - e” THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[real_sub, GSYM REAL_NOT_LE, REAL_LE_ADDR, REAL_NEG_GE0] THEN
    ASM_REWRITE_TAC[REAL_NOT_LE], ALL_TAC] THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
  DISCH_THEN(MP_TAC o SPEC “(pi / &2) - e”) THEN
  REWRITE_TAC[REAL_SUB_SUB, ABS_NEG] THEN
  SUBGOAL_THEN “abs(e) = e” (fn th => ASM_REWRITE_TAC[th]) THENL
   [REWRITE_TAC[ABS_REFL] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
  SUBGOAL_THEN “&0 < cos((pi / &2) - e) / sin((pi / &2) - e)”
  MP_TAC THENL
   [ONCE_REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC COS_POS_PI2,
      MATCH_MP_TAC REAL_INV_POS THEN MATCH_MP_TAC SIN_POS_PI2] THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE, real_sub, REAL_LE_ADDR, REAL_NEG_GE0] THEN
    ASM_REWRITE_TAC[REAL_NOT_LE], ALL_TAC] THEN
  DISCH_THEN(fn th => ASSUME_TAC th THEN MP_TAC(MATCH_MP REAL_POS_NZ th)) THEN
  REWRITE_TAC[ABS_NZ, TAUT_CONV “a ==> b ==> c <=> a /\ b ==> c”] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_INV) THEN REWRITE_TAC[tan] THEN
  MATCH_MP_TAC (TAUT_CONV “(a <=> b) ==> a ==> b”) THEN BINOP_TAC THENL
   [MATCH_MP_TAC REAL_INVINV THEN MATCH_MP_TAC REAL_POS_NZ THEN
    FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
  MP_TAC(ASSUME“&0 < cos((pi / &2) - e) / sin((pi / &2) - e)”) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  REWRITE_TAC[GSYM ABS_REFL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[real_div] THEN IMP_SUBST_TAC REAL_INV_MUL THENL
   [REWRITE_TAC[GSYM DE_MORGAN_THM, GSYM REAL_ENTIRE, GSYM real_div] THEN
    MATCH_MP_TAC REAL_POS_NZ THEN FIRST_ASSUM ACCEPT_TAC,
    GEN_REWR_TAC RAND_CONV  [REAL_MUL_SYM] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC REAL_INVINV THEN MATCH_MP_TAC REAL_POS_NZ THEN
    MATCH_MP_TAC SIN_POS_PI2 THEN REWRITE_TAC[REAL_SUB_LT, GSYM real_div] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE, real_sub, REAL_LE_ADDR, REAL_NEG_GE0] THEN
    ASM_REWRITE_TAC[REAL_NOT_LE]]
QED

val TAN_TOTAL_POS = store_thm("TAN_TOTAL_POS",
  “!y. &0 <= y ==> ?x. &0 <= x /\ x < pi / &2 /\ (tan(x) = y)”,
  GEN_TAC THEN DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP TAN_TOTAL_LEMMA) THEN
    DISCH_THEN(X_CHOOSE_THEN “x:real” STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [“tan”, “&0”, “x:real”, “y:real”] IVT) THEN
    W(C SUBGOAL_THEN (fn th => DISCH_THEN(MP_TAC o C MATCH_MP th)) o
         funpow 2 (fst o dest_imp) o snd) THENL
     [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LT_IMP_LE) THEN
      ASM_REWRITE_TAC[TAN_0] THEN X_GEN_TAC “z:real” THEN STRIP_TAC THEN
      MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC “inv(cos(z) pow 2)” THEN
      MATCH_MP_TAC DIFF_TAN THEN UNDISCH_TAC “&0 <= z” THEN
      REWRITE_TAC[REAL_LE_LT] THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
       [DISCH_TAC THEN MATCH_MP_TAC REAL_POS_NZ THEN
        MATCH_MP_TAC COS_POS_PI2 THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC “x:real” THEN
        ASM_REWRITE_TAC[],
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[COS_0, REAL_10]],
      DISCH_THEN(X_CHOOSE_THEN “z:real” STRIP_ASSUME_TAC) THEN
      EXISTS_TAC “z:real” THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC “x:real” THEN
      ASM_REWRITE_TAC[]],
    POP_ASSUM(SUBST1_TAC o SYM) THEN EXISTS_TAC “&0” THEN
    REWRITE_TAC[TAN_0, REAL_LE_REFL, PI2_BOUNDS]]);

val TAN_TOTAL = store_thm("TAN_TOTAL",
  “!y. ?!x. ~(pi / &2) < x /\ x < (pi / &2) /\ (tan(x) = y)”,
  GEN_TAC THEN CONV_TAC EXISTS_UNIQUE_CONV THEN CONJ_TAC THENL
   [DISJ_CASES_TAC(SPEC “y:real” REAL_LE_NEGTOTAL) THEN
    POP_ASSUM(X_CHOOSE_TAC “x:real” o MATCH_MP TAN_TOTAL_POS) THENL
     [EXISTS_TAC “x:real” THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC “&0” THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM REAL_LT_NEG] THEN
      REWRITE_TAC[REAL_NEGNEG, REAL_NEG_0, PI2_BOUNDS],
      Q.EXISTS_TAC ‘~x’ THEN ASM_REWRITE_TAC[REAL_LT_NEG] THEN
      ASM_REWRITE_TAC[TAN_NEG, REAL_NEG_EQ, REAL_NEGNEG] THEN
      ONCE_REWRITE_TAC[GSYM REAL_LT_NEG] THEN
      REWRITE_TAC[REAL_LT_NEG] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC “x:real” THEN ASM_REWRITE_TAC[REAL_LE_NEGL]],
    MAP_EVERY X_GEN_TAC [“x1:real”, “x2:real”] THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
         (SPECL [“x1:real”, “x2:real”] REAL_LT_TOTAL) THENL
     [DISCH_THEN(K ALL_TAC) THEN POP_ASSUM ACCEPT_TAC,
      ALL_TAC,
      POP_ASSUM MP_TAC THEN SPEC_TAC(“x1:real”,“z1:real”) THEN
      SPEC_TAC(“x2:real”,“z2:real”) THEN
      MAP_EVERY X_GEN_TAC [“x1:real”, “x2:real”] THEN DISCH_TAC THEN
      CONV_TAC(RAND_CONV SYM_CONV) THEN ONCE_REWRITE_TAC[CONJ_SYM]] THEN
    (STRIP_TAC THEN MP_TAC(SPECL [“tan”, “x1:real”, “x2:real”] ROLLE) THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC CONTRAPOS_CONV THEN
     DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[NOT_IMP] THEN
     REPEAT CONJ_TAC THENL
      [X_GEN_TAC “x:real” THEN STRIP_TAC THEN MATCH_MP_TAC DIFF_CONT THEN
       EXISTS_TAC “inv(cos(x) pow 2)” THEN MATCH_MP_TAC DIFF_TAN,
       X_GEN_TAC “x:real” THEN
       DISCH_THEN(CONJUNCTS_THEN (ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE)) THEN
       REWRITE_TAC[differentiable] THEN EXISTS_TAC “inv(cos(x) pow 2)” THEN
       MATCH_MP_TAC DIFF_TAN,
       REWRITE_TAC[CONJ_ASSOC] THEN DISCH_THEN(X_CHOOSE_THEN “x:real”
         (CONJUNCTS_THEN2 (CONJUNCTS_THEN (ASSUME_TAC o MATCH_MP
          REAL_LT_IMP_LE)) ASSUME_TAC)) THEN
       MP_TAC(SPEC “x:real” DIFF_TAN) THEN
       SUBGOAL_THEN “~(cos(x) = &0)” ASSUME_TAC THENL
        [ALL_TAC,
         ASM_REWRITE_TAC[] THEN
         DISCH_THEN(MP_TAC o C CONJ (ASSUME “(tan diffl &0)(x)”)) THEN
         DISCH_THEN(MP_TAC o MATCH_MP DIFF_UNIQ) THEN REWRITE_TAC[] THEN
         MATCH_MP_TAC REAL_INV_NZ THEN MATCH_MP_TAC POW_NZ THEN
         ASM_REWRITE_TAC[]]] THEN
     (MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC COS_POS_PI THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC “x1:real”,
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC “x2:real”] THEN
     ASM_REWRITE_TAC[]))]);

(*---------------------------------------------------------------------------*)
(* Inverse trig functions                                                    *)
(*---------------------------------------------------------------------------*)

val asn = new_definition("asn",
  “asn(y) = @x. ~(pi / &2) <= x /\ x <= pi / &2 /\ (sin x = y)”);

val acs = new_definition("acs",
  “acs(y) = @x. &0 <= x /\ x <= pi /\ (cos x = y)”);

val atn = new_definition("atn",
  “atn(y) = @x. ~(pi / &2) < x /\ x < pi / &2 /\ (tan x = y)”);

val ASN = store_thm("ASN",
  “!y. ~(&1) <= y /\ y <= &1 ==>
           ~(pi / &2) <= asn(y) /\ (asn(y) <= pi / &2 /\ (sin(asn y) = y))”,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP SIN_TOTAL) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[GSYM asn]);

val ASN_SIN = store_thm("ASN_SIN",
  “!y. ~(&1) <= y /\ y <= &1 ==> (sin(asn(y)) = y)”,
  GEN_TAC THEN DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP ASN th]));

val ASN_BOUNDS = store_thm("ASN_BOUNDS",
  “!y. ~(&1) <= y /\ y <= &1
           ==> ~(pi / &2) <= asn(y) /\ asn(y) <= pi / &2”,
GEN_TAC THEN DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP ASN th]));

val ASN_BOUNDS_LT = store_thm("ASN_BOUNDS_LT",
  “!y. ~(&1) < y /\ y < &1 ==> ~(pi / &2) < asn(y) /\ asn(y) < pi / &2”,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN “~(pi / &2) <= asn(y) /\ asn(y) <= pi / &2” ASSUME_TAC THENL
   [MATCH_MP_TAC ASN_BOUNDS THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
    ASM_REWRITE_TAC[REAL_LT_LE]] THEN
  CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM “sin”) THEN
  REWRITE_TAC[SIN_NEG, SIN_PI2] THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
  SUBGOAL_THEN “sin(asn y) = y” (fn th => ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC ASN_SIN THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]);

val SIN_ASN = store_thm("SIN_ASN",
  “!x. ~(pi / &2) <= x /\ x <= pi / &2 ==> (asn(sin(x)) = x)”,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(MATCH_MP SIN_TOTAL (SPEC “x:real” SIN_BOUNDS)) THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ASN THEN
  MATCH_ACCEPT_TAC SIN_BOUNDS);

val ACS = store_thm("ACS",
  “!y. ~(&1) <= y /\ y <= &1 ==>
     &0 <= acs(y) /\ acs(y) <= pi  /\ (cos(acs y) = y)”,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP COS_TOTAL) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[GSYM acs]);

val ACS_COS = store_thm("ACS_COS",
  “!y. ~(&1) <= y /\ y <= &1 ==> (cos(acs(y)) = y)”,
  GEN_TAC THEN DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP ACS th]));

val ACS_BOUNDS = store_thm("ACS_BOUNDS",
  “!y. ~(&1) <= y /\ y <= &1 ==> &0 <= acs(y) /\ acs(y) <= pi”,
  GEN_TAC THEN DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP ACS th]));

val ACS_BOUNDS_LT = store_thm("ACS_BOUNDS_LT",
  “!y. ~(&1) < y /\ y < &1 ==> &0 < acs(y) /\ acs(y) < pi”,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN “&0 <= acs(y) /\ acs(y) <= pi” ASSUME_TAC THENL
   [MATCH_MP_TAC ACS_BOUNDS THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
    ASM_REWRITE_TAC[REAL_LT_LE]] THEN
  CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM “cos”) THEN
  REWRITE_TAC[COS_0, COS_PI] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  MATCH_MP_TAC REAL_LT_IMP_NE THEN
  SUBGOAL_THEN “cos(acs y) = y” (fn th => ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC ACS_COS THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]);

val COS_ACS = store_thm("COS_ACS",
  “!x. &0 <= x /\ x <= pi ==> (acs(cos(x)) = x)”,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(MATCH_MP COS_TOTAL (SPEC “x:real” COS_BOUNDS)) THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ACS THEN
  MATCH_ACCEPT_TAC COS_BOUNDS);

val ATN = store_thm("ATN",
  “!y. ~(pi / &2) < atn(y) /\ atn(y) < (pi / &2) /\ (tan(atn y) = y)”,
  GEN_TAC THEN MP_TAC(SPEC “y:real” TAN_TOTAL) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[GSYM atn]);

val ATN_TAN = store_thm("ATN_TAN",
  “!y. tan(atn y) = y”,
  REWRITE_TAC[ATN]);

val ATN_BOUNDS = store_thm("ATN_BOUNDS",
  “!y. ~(pi / &2) < atn(y) /\ atn(y) < (pi / &2)”,
  REWRITE_TAC[ATN]);

val TAN_ATN = store_thm("TAN_ATN",
  “!x. ~(pi / &2) < x /\ x < (pi / &2) ==> (atn(tan(x)) = x)”,
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC “tan(x)” TAN_TOTAL) THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  ASM_REWRITE_TAC[ATN]);

(*---------------------------------------------------------------------------*)
(* A few additional results about the trig functions                         *)
(*---------------------------------------------------------------------------*)

val TAN_SEC = store_thm("TAN_SEC",
  “!x. ~(cos(x) = &0) ==> (&1 + (tan(x) pow 2) = inv(cos x) pow 2)”,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[tan] THEN
  FIRST_ASSUM(fn th => ONCE_REWRITE_TAC[GSYM
   (MATCH_MP REAL_DIV_REFL (SPEC “2:num” (MATCH_MP POW_NZ th)))]) THEN
  REWRITE_TAC[real_div, POW_MUL] THEN
  POP_ASSUM(fn th => REWRITE_TAC[MATCH_MP POW_INV th]) THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[GSYM REAL_RDISTRIB, SIN_CIRCLE, REAL_MUL_LID]);

val SIN_COS_SQ = store_thm("SIN_COS_SQ",
  “!x. &0 <= x /\ x <= pi ==> (sin(x) = sqrt(&1 - (cos(x) pow 2)))”,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC SQRT_EQ THEN
  REWRITE_TAC[REAL_EQ_SUB_LADD, SIN_CIRCLE] THEN
  MATCH_MP_TAC SIN_POS_PI_LE THEN ASM_REWRITE_TAC[]);

val COS_SIN_SQ = store_thm("COS_SIN_SQ",
  “!x. ~(pi / &2) <= x /\ x <= (pi / &2) ==>
             (cos(x) = sqrt(&1 - (sin(x) pow 2)))”,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC SQRT_EQ THEN
  REWRITE_TAC[REAL_EQ_SUB_LADD] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[SIN_CIRCLE] THEN
  MATCH_MP_TAC COS_POS_PI_LE THEN ASM_REWRITE_TAC[]);

val COS_ATN_NZ = store_thm("COS_ATN_NZ",
  “!x. ~(cos(atn(x)) = &0)”,
  GEN_TAC THEN MATCH_MP_TAC REAL_POS_NZ THEN
  MATCH_MP_TAC COS_POS_PI THEN MATCH_ACCEPT_TAC ATN_BOUNDS);

val COS_ASN_NZ = store_thm("COS_ASN_NZ",
  “!x. ~(&1) < x /\ x < &1 ==> ~(cos(asn(x)) = &0)”,
  GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY MATCH_MP_TAC [REAL_POS_NZ, COS_POS_PI, ASN_BOUNDS_LT] THEN
  POP_ASSUM ACCEPT_TAC);

val SIN_ACS_NZ = store_thm("SIN_ACS_NZ",
  “!x. ~(&1) < x /\ x < &1 ==> ~(sin(acs(x)) = &0)”,
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
  “!x. &0 < x ==> (ln diffl (inv x))(x)”,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN “(ln diffl (inv x))(exp(ln(x)))” MP_TAC THENL
   [MATCH_MP_TAC DIFF_INVERSE_OPEN,
    MATCH_MP_TAC(TAUT_CONV “(a <=> b) ==> a ==> b”) THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[EXP_LN]] THEN
  MAP_EVERY EXISTS_TAC [“ln(x) - &1”, “ln(x) + &1”] THEN
  REWRITE_TAC[REAL_LT_SUB_RADD, REAL_LT_ADDR, REAL_LT_01, LN_EXP,
    MATCH_MP DIFF_CONT (SPEC_ALL DIFF_EXP)] THEN
  CONJ_TAC THENL
   [MP_TAC(SPEC “ln(x)” DIFF_EXP) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM EXP_LN]), MATCH_MP_TAC REAL_POS_NZ] THEN
  ASM_REWRITE_TAC[]);

(* Known as DIFF_ASN_COS in GTT *)
val DIFF_ASN_LEMMA = store_thm("DIFF_ASN_LEMMA",
  “!x. ~(&1) < x /\ x < &1 ==> (asn diffl (inv(cos(asn x))))(x)”,
  GEN_TAC THEN STRIP_TAC THEN IMP_RES_TAC REAL_LT_IMP_LE THEN
  MP_TAC(SPEC “x:real” ASN_SIN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fn th => GEN_REWR_TAC RAND_CONV  [SYM th]) THEN
  MATCH_MP_TAC DIFF_INVERSE_OPEN THEN REWRITE_TAC[DIFF_SIN] THEN
  MAP_EVERY EXISTS_TAC [“~(pi / &2)”, “pi / &2”] THEN
  MP_TAC(SPEC “x:real” ASN_BOUNDS_LT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]) THEN CONJ_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN IMP_RES_TAC REAL_LT_IMP_LE THEN
    REWRITE_TAC[MATCH_MP DIFF_CONT (SPEC_ALL DIFF_SIN)] THEN
    MATCH_MP_TAC SIN_ASN THEN ASM_REWRITE_TAC[],
    MATCH_MP_TAC COS_ASN_NZ THEN ASM_REWRITE_TAC[]]);

Theorem DIFF_ASN[difftool]:
  !x. ~(&1) < x /\ x < &1 ==> (asn diffl (inv(sqrt(&1 - (x pow 2)))))(x)
Proof
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIFF_ASN_LEMMA) THEN
  MATCH_MP_TAC(TAUT_CONV “(a <=> b) ==> a ==> b”) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN “cos(asn(x)) = sqrt(&1 - (sin(asn x) pow 2))” SUBST1_TAC THENL
   [MATCH_MP_TAC COS_SIN_SQ THEN MATCH_MP_TAC ASN_BOUNDS,
    SUBGOAL_THEN “sin(asn x) = x” SUBST1_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC ASN_SIN] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]
QED

(* Known as DIFF_ACS_SIN in GTT *)
val DIFF_ACS_LEMMA = store_thm("DIFF_ACS_LEMMA",
  “!x. ~(&1) < x /\ x < &1 ==> (acs diffl inv(~(sin(acs x))))(x)”,
  GEN_TAC THEN STRIP_TAC THEN IMP_RES_TAC REAL_LT_IMP_LE THEN
  MP_TAC(SPEC “x:real” ACS_COS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fn th => GEN_REWR_TAC RAND_CONV  [SYM th]) THEN
  MATCH_MP_TAC DIFF_INVERSE_OPEN THEN REWRITE_TAC[DIFF_COS] THEN
  MAP_EVERY EXISTS_TAC [“&0”, “pi”] THEN
  MP_TAC(SPEC “x:real” ACS_BOUNDS_LT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th]) THEN CONJ_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN IMP_RES_TAC REAL_LT_IMP_LE THEN
    REWRITE_TAC[MATCH_MP DIFF_CONT (SPEC_ALL DIFF_COS)] THEN
    MATCH_MP_TAC COS_ACS THEN ASM_REWRITE_TAC[],
    REWRITE_TAC[REAL_NEG_EQ, REAL_NEG_0] THEN
    MATCH_MP_TAC SIN_ACS_NZ THEN ASM_REWRITE_TAC[]]);

Theorem DIFF_ACS[difftool]:
  !x. ~(&1) < x /\ x < &1 ==> (acs diffl ~(inv(sqrt(&1 - (x pow 2)))))(x)
Proof
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIFF_ACS_LEMMA) THEN
  MATCH_MP_TAC(TAUT_CONV “(a <=> b) ==> a ==> b”) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN “sin(acs(x)) = sqrt(&1 - (cos(acs x) pow 2))” SUBST1_TAC THENL
   [MATCH_MP_TAC SIN_COS_SQ THEN MATCH_MP_TAC ACS_BOUNDS,
    SUBGOAL_THEN “cos(acs x) = x” SUBST1_TAC THENL
     [MATCH_MP_TAC ACS_COS,
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_NEG_INV THEN
      MATCH_MP_TAC REAL_POS_NZ THEN REWRITE_TAC[sqrt, TWO] THEN
      MATCH_MP_TAC ROOT_POS_LT THEN
      REWRITE_TAC[REAL_LT_SUB_LADD, REAL_ADD_LID] THEN
      REWRITE_TAC[SYM(TWO), POW_2] THEN
      GEN_REWR_TAC RAND_CONV  [GSYM REAL_MUL_LID] THEN
      DISJ_CASES_TAC (SPEC “x:real” REAL_LE_NEGTOTAL) THENL
       [ALL_TAC, GEN_REWR_TAC LAND_CONV  [GSYM REAL_NEG_MUL2]] THEN
      MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC [GSYM REAL_LT_NEG] THEN
      ASM_REWRITE_TAC[REAL_NEGNEG]]] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]
QED

Theorem DIFF_ATN[difftool]:
  !x. (atn diffl (inv(&1 + (x pow 2))))(x)
Proof
  GEN_TAC THEN
  SUBGOAL_THEN “(atn diffl (inv(&1 + (x pow 2))))(tan(atn x))” MP_TAC THENL
   [MATCH_MP_TAC DIFF_INVERSE_OPEN, REWRITE_TAC[ATN_TAN]] THEN
  MAP_EVERY EXISTS_TAC [“~(pi / &2)”, “pi / &2”] THEN
  REWRITE_TAC[ATN_BOUNDS] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC “x:real” THEN DISCH_TAC THEN
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP TAN_ATN th]) THEN
    MATCH_MP_TAC DIFF_CONT THEN
    EXISTS_TAC “inv(cos(x) pow 2)” THEN
    MATCH_MP_TAC DIFF_TAN THEN
    MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC COS_POS_PI THEN
    ASM_REWRITE_TAC[],
    MP_TAC(SPEC “atn(x)” DIFF_TAN) THEN REWRITE_TAC[COS_ATN_NZ] THEN
    REWRITE_TAC[MATCH_MP POW_INV (SPEC “x:real” COS_ATN_NZ)] THEN
    REWRITE_TAC[GSYM(MATCH_MP TAN_SEC (SPEC “x:real” COS_ATN_NZ))] THEN
    REWRITE_TAC[ATN_TAN],
    MATCH_MP_TAC REAL_POS_NZ THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC “&1” THEN
    REWRITE_TAC[REAL_LT_01, REAL_LE_ADDR, POW_2, REAL_LE_SQUARE]]
QED

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

Theorem MCLAURIN :
   !f diff h n.
    &0 < h /\ 0 < n /\ (diff(0) = f) /\
    (!m t. m < n /\ &0 <= t /\ t <= h ==>
           (diff(m) diffl diff(SUC m)(t))(t)) ==>
    (?t. &0 < t /\ t < h /\
        (f(h) = sum(0,n)(\m. (diff(m)(&0) / &(FACT m)) * (h pow m))
                +
                ((diff(n)(t) / &(FACT n)) * (h pow n))))
Proof
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
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM REAL_MUL_RID] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    ONCE_REWRITE_TAC[AC (REAL_MUL_ASSOC,REAL_MUL_SYM)
        (Term`a * (b * (c * d)) = (d * a) * (b * c)`)] THEN
    GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM REAL_MUL_LID] THEN BINOP_TAC THEN
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
      MATCH_MP_TAC(TAUT_CONV “(a <=> b) ==> a ==> b”) THEN
      AP_THM_TAC THEN CONV_TAC(ONCE_DEPTH_CONV(ALPHA_CONV (Term`t:real`))) THEN
      AP_TERM_TAC THEN GEN_REWRITE_TAC RAND_CONV empty_rewrites [REAL_MUL_SYM] THEN
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
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM REAL_ADD_RID] THEN
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
    MATCH_MP_TAC(TAUT_CONV “(a <=> b) ==> a ==> b”) THEN
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
    GEN_REWRITE_TAC (funpow 2 RAND_CONV) empty_rewrites
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
      ASM_REWRITE_TAC[]]]
QED

Theorem MCLAURIN_NEG:
  !f diff h n.
    h < &0 /\ 0 < n /\ (diff(0) = f) /\
    (!m t. m < n /\ h <= t /\ t <= &0 ==>
           (diff(m) diffl diff(SUC m)(t))(t)) ==>
    (?t. h < t /\ t < &0 /\
         (f(h) = sum(0,n)(\m. (diff(m)(&0) / &(FACT m)) * (h pow m))
                 + ((diff(n)(t) / &(FACT n)) * (h pow n))))
Proof
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(Q.SPECL[‘\x. (f(~x):real)’,
                 ‘\n x. ((~(&1)) pow n) * (diff:num->real->real)(n)(~x)’,
                 ‘~h’, ‘n:num’] MCLAURIN) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[REAL_NEG_GT0, pow, REAL_MUL_LID] THEN
  ONCE_REWRITE_TAC[GSYM REAL_LE_NEG] THEN
  REWRITE_TAC[REAL_NEGNEG, REAL_NEG_0] THEN
  ONCE_REWRITE_TAC[TAUT_CONV (Term`a /\ b /\ c <=> a /\ c /\ b`)] THEN
  W(C SUBGOAL_THEN (fn t => REWRITE_TAC[t]) o funpow 2 (fst o dest_imp) o snd)
  THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(MP_TAC o
               C CONJ (SPEC “t:real” (DIFF_CONV “\x. -x”))) THEN
    CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_CHAIN) THEN
    DISCH_THEN(MP_TAC o GEN_ALL o MATCH_MP DIFF_CMUL) THEN
    DISCH_THEN(MP_TAC o SPEC (Term`(~(&1)) pow m`)) THEN BETA_TAC THEN
    MATCH_MP_TAC(TAUT_CONV “(a <=> b) ==> a ==> b”) THEN
    CONV_TAC(ONCE_DEPTH_CONV(ALPHA_CONV (Term`z:real`))) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC(AC_CONV (REAL_MUL_ASSOC,REAL_MUL_SYM)),
    DISCH_THEN(X_CHOOSE_THEN (Term`t:real`) STRIP_ASSUME_TAC)] THEN
  Q.EXISTS_TAC ‘-t’ THEN ONCE_REWRITE_TAC[GSYM REAL_LT_NEG] THEN
  ASM_REWRITE_TAC[REAL_NEGNEG, REAL_NEG_0] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC (Term`m:num`) THEN REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN BETA_TAC, ALL_TAC] THEN
  REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[AC (REAL_MUL_ASSOC,REAL_MUL_SYM)
    (Term`a * (b * (c * d)) = (b * c) * (a * d)`)] THEN
  REWRITE_TAC[GSYM POW_MUL, GSYM REAL_NEG_MINUS1, REAL_NEGNEG] THEN
  REWRITE_TAC[REAL_MUL_ASSOC]
QED

(* ------------------------------------------------------------------------- *)
(* Simple strong form if a function is differentiable everywhere.            *)
(* ------------------------------------------------------------------------- *)

Theorem MCLAURIN_ALL_LT :
   !f diff.
      (diff 0 = f) /\
      (!m x. ((diff m) diffl (diff(SUC m) x)) x)
      ==> !x n. ~(x = &0) /\ 0 < n
            ==> ?t. &0 < abs(t) /\ abs(t) < abs(x) /\
                    (f(x) = sum(0,n)
                                (\m. (diff m (&0) / &(FACT m)) * x pow m)
                            +
                            (diff n t / &(FACT n)) * x pow n)
Proof
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
    THEN REAL_ARITH_TAC]
QED

Theorem MCLAURIN_ZERO :
   !diff n x. (x = &0) /\ 0 < n ==>
       (sum(0,n) (\m. (diff m (&0) / &(FACT m)) * x pow m) = diff 0 (&0))
Proof
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
    REWRITE_TAC[REAL_ADD_RID]]
QED

Theorem LET_CASES[local] :
   !m n:num. m <= n \/ n < m
Proof
  ONCE_REWRITE_TAC [DISJ_SYM] THEN MATCH_ACCEPT_TAC LESS_CASES
QED

Theorem REAL_POW_EQ_0[local] :
   !x n. (x pow n = &0) <=> (x = &0) /\ ~(n = 0)
Proof
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[NOT_SUC, pow, REAL_ENTIRE] THENL
   [REWRITE_TAC [REAL_OF_NUM_EQ, ONE,NOT_SUC],
    EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]
QED

Theorem MCLAURIN_ALL_LE :
   !f diff.
      (diff 0 = f) /\
      (!m x. ((diff m) diffl (diff(SUC m) x)) x)
      ==> !x n. ?t. abs t  <= abs x /\
                   (f(x) = sum(0,n)
                             (\m. (diff m (&0) / &(FACT m)) * x pow m)
                           +
                            (diff n t / &(FACT n)) * x pow n)
Proof
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
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]]]
QED

(* ------------------------------------------------------------------------- *)
(* Version for exp.                                                          *)
(* ------------------------------------------------------------------------- *)

Theorem MCLAURIN_EXP_LEMMA[local] :
   ((\n:num. exp) 0 = exp) /\
   (!m x. (((\n:num. exp) m) diffl ((\n:num. exp) (SUC m) x)) x)
Proof
  REWRITE_TAC[DIFF_EXP]
QED

Theorem MCLAURIN_EXP_LT :
   !x n. ~(x = &0) /\ 0 < n
         ==> ?t. &0 < abs(t) /\
                 abs(t) < abs(x) /\
                 (exp(x) = sum(0,n)(\m. x pow m / &(FACT m)) +
                           (exp(t) / &(FACT n)) * x pow n)
Proof
  MP_TAC (MATCH_MP MCLAURIN_ALL_LT MCLAURIN_EXP_LEMMA) THEN BETA_TAC THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN
  EXISTS_TAC (Term`t:real`) THEN
  ASM_REWRITE_TAC [EXP_0,real_div,REAL_MUL_LID,REAL_MUL_RID]
  THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC FUN_EQ_CONV
  THEN GEN_TAC THEN BETA_TAC THEN GEN_REWRITE_TAC LAND_CONV empty_rewrites [REAL_MUL_SYM]
  THEN REFL_TAC
QED

Theorem MCLAURIN_EXP_LE :
   !x n. ?t. abs(t) <= abs(x) /\
             (exp(x) = sum(0,n)(\m. x pow m / &(FACT m)) +
                       (exp(t) / &(FACT n)) * x pow n)
Proof
  MP_TAC (MATCH_MP MCLAURIN_ALL_LE MCLAURIN_EXP_LEMMA) THEN
  DISCH_THEN (fn th => REPEAT GEN_TAC THEN STRIP_ASSUME_TAC (SPEC_ALL th))
  THEN EXISTS_TAC (Term`t:real`) THEN  ASM_REWRITE_TAC [] THEN
  AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN CONV_TAC FUN_EQ_CONV
  THEN GEN_TAC THEN BETA_TAC THEN
  REWRITE_TAC[EXP_0, real_div, REAL_MUL_LID, REAL_MUL_RID] THEN
  GEN_REWRITE_TAC LAND_CONV empty_rewrites [REAL_MUL_SYM] THEN REFL_TAC
QED

(* ------------------------------------------------------------------------- *)
(* Version for ln(1 - x).                                                    *)
(* ------------------------------------------------------------------------- *)

Theorem DIFF_LN_COMPOSITE:
   !g m x. (g diffl m)(x) /\ &0 < g x
           ==> ((\x. ln(g x)) diffl (inv(g x) * m))(x)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFF_CHAIN THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIFF_LN THEN
  ASM_REWRITE_TAC[]
QED

Theorem DIFF_LN_COMPOSITE'[difftool] = SPEC_ALL DIFF_LN_COMPOSITE

(* ------------------------------------------------------------------------- *)
(* Exponentiation with real exponents (rpow)                                 *)
(* ------------------------------------------------------------------------- *)

fun K_TAC _ = ALL_TAC;

(* Definition *)
val _ = set_fixity "rpow" (Infixr 700);

val rpow = Define `a rpow b = exp (b * ln a)`;

(* Properties *)

val  GEN_RPOW = store_thm
        ("GEN_RPOW",
        ``! a n. 0 < a ==> (a pow n = a rpow  &n)``,
 Induct_on `n` THENL [
 RW_TAC real_ss [pow,POW_1, rpow, GSYM EXP_0],

GEN_TAC THEN
        RW_TAC std_ss[rpow,pow,REAL,REAL_RDISTRIB,EXP_ADD,REAL_MUL_LID] THEN

        KNOW_TAC ``exp(ln a)= a`` THEN1
          PROVE_TAC[EXP_LN] THEN
        DISCH_TAC THEN ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC THEN
        KNOW_TAC ``a* exp (&n * ln a) = exp (&n * ln a)*a`` THEN1
          RW_TAC std_ss[REAL_MUL_COMM] THEN
        DISCH_TAC THEN ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC]);

val  RPOW_SUC_N = store_thm
        ("RPOW_SUC_N",
        ``!(a:real) (n:num). 0 < a ==>(a rpow (&n+1)= a pow SUC n)``,
 RW_TAC std_ss [] THEN
 KNOW_TAC``&n + (1:real)= & SUC n`` THEN1
     RW_TAC std_ss [REAL]THEN
       DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
       RW_TAC std_ss [GEN_RPOW]) ;

val RPOW_0= store_thm
        ("RPOW_0",
        ``! a. (0 < a)==> (a rpow  &0 = &1)``,
  RW_TAC std_ss [rpow]THEN
  RW_TAC std_ss [REAL_MUL_LZERO]THEN
  RW_TAC std_ss [EXP_0]);

val  RPOW_1= store_thm
        ("RPOW_1",
        ``! a. (0 < a)==> ( a rpow  &1 = a)``,
   RW_TAC std_ss [GSYM GEN_RPOW,POW_1]);

val  ONE_RPOW= store_thm
        ("ONE_RPOW",
        ``! a. (0 < a)==> (1 rpow a  = 1)``,
RW_TAC real_ss [rpow,LN_1,EXP_0]);

val  RPOW_POS_LT= store_thm
        ("RPOW_POS_LT",
        ``! a b. (0 < a)==> (0 < a rpow b)``,
              RW_TAC std_ss [rpow, EXP_POS_LT]);

val  RPOW_NZ= store_thm
        ("RPOW_NZ",
        ``! a b. (0 <> a)==> ( a rpow b <>0)``,
RW_TAC std_ss [rpow,EXP_NZ]);


val  LN_RPOW= store_thm
        ("LN_RPOW",
        ``! a b. (0 < a)==> (ln (a rpow b)= (b*ln a))``,
 RW_TAC std_ss [rpow,LN_EXP]);

val  RPOW_ADD= store_thm
        ("RPOW_ADD",
        ``! a b c. a rpow (b + c)= (a rpow  b)*(a rpow  c)``,
 RW_TAC std_ss [rpow, EXP_ADD, REAL_RDISTRIB] );

val  RPOW_ADD_MUL= store_thm
        ("RPOW_ADD_MUL",
        ``! a b c. a rpow (b + c)* a rpow (-b)= (a rpow c)``,
 RW_TAC std_ss [rpow, REAL_RDISTRIB, GSYM EXP_ADD]THEN
 KNOW_TAC`` ((b * ln a + c * ln a + -b * ln a)=(b * ln a  -b * ln a + c*ln a)) ``THEN1
    REAL_ARITH_TAC THEN
         DISCH_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM K_TAC THEN
     KNOW_TAC``((b * ln a - b * ln a + c * ln a) = (c*ln a )) ``THEN1
         REAL_ARITH_TAC THEN
         RW_TAC real_ss []);

val  RPOW_SUB= store_thm
        ("RPOW_SUB",
        ``! a b c. a rpow (b - c)= (a rpow b)/(a rpow c)``,
RW_TAC std_ss [rpow, REAL_SUB_RDISTRIB, EXP_SUB]);

val  RPOW_DIV= store_thm
        ("RPOW_DIV",
        ``! a b c.  (0 < a)/\ (0<b)==> ((a/b) rpow  c= (a rpow c)/(b rpow c))``,
   RW_TAC std_ss [rpow ,LN_DIV, REAL_SUB_LDISTRIB, EXP_SUB]);

val  RPOW_INV= store_thm
        ("RPOW_INV",
        ``! a b .  (0 < a)==>((inv a) rpow b= inv (a rpow b))``,

RW_TAC real_ss [rpow, REAL_INV_1OVER, LN_DIV, REAL_SUB_LDISTRIB, EXP_SUB, LN_1, EXP_0]);


val  RPOW_MUL= store_thm
        ("RPOW_MUL",
        ``! a b c. (0<a) /\ (0<b)==> (((a*b) rpow c)=(a rpow c)*(b rpow c))``,
RW_TAC std_ss [rpow, LN_MUL, REAL_LDISTRIB, EXP_ADD]);

val  RPOW_RPOW= store_thm
        ("RPOW_RPOW",
        ``! a b c. (0<a)==> ((a rpow b) rpow c = a rpow (b*c))``,
  RW_TAC real_ss [rpow, LN_EXP, REAL_MUL_ASSOC] THEN
  PROVE_TAC[ REAL_MUL_COMM] );

Theorem RPOW_LT :
   !(a:real) (b:real) (c:real). 1 < a ==> (a rpow b < a rpow c <=> b < c)
Proof
 RW_TAC std_ss [rpow]  THEN
 KNOW_TAC`` exp (b * ln a) < exp (c * ln a) <=> (b*ln a < c*ln a)``  THEN1
      RW_TAC real_ss [EXP_MONO_LT]  THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM K_TAC  THEN
      KNOW_TAC``((b:real)*ln a < (c:real)*ln a) <=> (b < c)``  THENL   [
      MATCH_MP_TAC REAL_LT_RMUL  THEN
      KNOW_TAC``0 < ln a <=> exp (0) < exp (ln a)``  THEN1
         PROVE_TAC[EXP_MONO_LT]  THEN
         DISCH_TAC  THEN
         FULL_SIMP_TAC real_ss[]  THEN
         RW_TAC real_ss [EXP_0]  THEN
         KNOW_TAC``1 < (a:real) ==> 0 <(a:real)``  THENL [
             RW_TAC real_ss []  THEN
             MATCH_MP_TAC REAL_LT_TRANS  THEN
             EXISTS_TAC``(1:real)`` THEN
             RW_TAC real_ss [],
             RW_TAC real_ss []  THEN
             KNOW_TAC``exp (ln a)=(a:real)``  THEN1
                  RW_TAC real_ss [EXP_LN] THEN
                  DISCH_TAC THEN ASM_REWRITE_TAC[]],
            RW_TAC real_ss []]
QED

Theorem RPOW_LE :
   !a b c. 1 < a ==> (a rpow b <= a rpow c <=> b <= c)
Proof
 RW_TAC std_ss [rpow] THEN
 KNOW_TAC ``exp ((b:real) * ln a) <= exp ((c:real) * ln a) <=>
            ((b:real)*ln a <= (c:real)*ln a)`` THEN1
      RW_TAC real_ss [EXP_MONO_LE] THEN
 DISCH_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM K_TAC THEN
 KNOW_TAC``(b*ln a <= c*ln a) <=> ((b:real) <= (c:real))`` THENL[
          MATCH_MP_TAC REAL_LE_RMUL THEN
     KNOW_TAC``0 < ln a <=> exp (0) < exp (ln a)`` THEN1
         PROVE_TAC[EXP_MONO_LT] THEN
          DISCH_TAC THEN
          FULL_SIMP_TAC real_ss[] THEN
          RW_TAC real_ss [EXP_0] THEN
     KNOW_TAC``1 < (a:real) ==> 0 <(a:real)`` THENL[
          RW_TAC real_ss [] THEN
          MATCH_MP_TAC REAL_LT_TRANS THEN
          EXISTS_TAC``(1:real)`` THEN
          RW_TAC real_ss [] ,
          RW_TAC real_ss [] THEN
          KNOW_TAC``exp (ln a)=(a:real)`` THEN1
             RW_TAC real_ss [EXP_LN] THEN
             DISCH_TAC THEN ASM_REWRITE_TAC[]],
 RW_TAC real_ss []]
QED

Theorem BASE_RPOW_LE :
   !a b c. 0 < a /\ 0 < c /\ 0 < b ==> (a rpow b <= c rpow b <=> a <= c)
Proof
RW_TAC std_ss [rpow, EXP_MONO_LE] THEN
KNOW_TAC`` (((b:real) * ln a) <= ((b:real) * ln c)) <=> ((ln a <= ln c))`` THENL[
  MATCH_MP_TAC REAL_LE_LMUL   THEN
  RW_TAC real_ss [],

  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM K_TAC  THEN
  RW_TAC real_ss [LN_MONO_LE]]
QED

Theorem BASE_RPOW_LT :
   !a b c. 0 < a /\ 0 < c /\ 0 < b ==> (a rpow b < c rpow b <=> a < c)
Proof
 RW_TAC std_ss [rpow, EXP_MONO_LT]  THEN
 KNOW_TAC ``((b * ln a) < (b * ln c)) <=> ln a < ln c``  THENL[
       MATCH_MP_TAC REAL_LT_LMUL  THEN
       RW_TAC real_ss [],

       DISCH_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM K_TAC  THEN
       RW_TAC real_ss [LN_MONO_LT] ]
QED

Theorem RPOW_UNIQ_BASE :
   !a b c. 0 < a /\ 0 < c /\ 0 <> b /\ (a rpow b = c rpow b) ==> (a = c)
Proof
 RW_TAC std_ss [rpow, GSYM LN_INJ] THEN
 POP_ASSUM MP_TAC  THEN
 KNOW_TAC ``(exp (b * ln a) = exp (b * ln c)) <=>
            (ln (exp (b * ln a)) = ln (exp (b * ln c)))``THEN1
     PROVE_TAC[LN_EXP]THEN
     DISCH_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM K_TAC THEN
     FULL_SIMP_TAC real_ss[LN_EXP] THEN
     FULL_SIMP_TAC real_ss[REAL_EQ_MUL_LCANCEL]
QED

Theorem RPOW_UNIQ_EXP :
   !a b c. 1 < a /\ 0 < c /\ 0 < b /\ (a rpow b = a rpow c) ==> (b = c)
Proof
 RW_TAC std_ss [rpow, GSYM LN_INJ] THEN
 POP_ASSUM MP_TAC THEN
 KNOW_TAC ``(exp (b * ln a) = exp (c * ln a)) <=>
            (ln (exp (b * ln a)) = ln (exp (c * ln a)))`` THEN1
      PROVE_TAC[LN_EXP] THEN
          DISCH_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM K_TAC THEN
          FULL_SIMP_TAC real_ss[LN_EXP] THEN
          FULL_SIMP_TAC real_ss[REAL_EQ_RMUL] THEN
          KNOW_TAC``(1 < (a:real))==> 0 < ln a`` THENL[
      RW_TAC real_ss [] THEN
      KNOW_TAC``0 < ln a <=> exp (0) < exp (ln a)`` THEN1
          PROVE_TAC[EXP_MONO_LT] THEN
          DISCH_TAC THEN
          FULL_SIMP_TAC real_ss[] THEN
          RW_TAC real_ss [EXP_0] THEN
              KNOW_TAC``1 < (a:real) ==> 0 <(a:real)`` THENL[
                   RW_TAC real_ss [] THEN
                   MATCH_MP_TAC REAL_LT_TRANS THEN
                   EXISTS_TAC``(1:real)`` THEN
                   RW_TAC real_ss [] ,
                   RW_TAC real_ss [] THEN
                   KNOW_TAC``exp (ln a)=(a:real)`` THEN1
                      RW_TAC real_ss [EXP_LN] THEN
       DISCH_TAC THEN ASM_REWRITE_TAC[] THEN  RW_TAC real_ss []],
 FULL_SIMP_TAC real_ss[REAL_POS_NZ] ]
QED

Theorem RPOW_DIV_BASE :
   !x t. 0 < x ==> ((x rpow t)/x = x rpow (t-1))
Proof
RW_TAC std_ss [rpow, REAL_SUB_RDISTRIB, EXP_SUB, REAL_MUL_LID] THEN
KNOW_TAC``exp(ln x)= (x:real)`` THEN1
    PROVE_TAC[EXP_LN] THEN
DISCH_TAC THEN ASM_REWRITE_TAC []
QED

(* Convert ‘root’ to ‘rpow’,
   NOTE: hol-light's version is more general: ‘0 <= x \/ ODD n’
  *)
Theorem REAL_ROOT_RPOW :
    !n x. ~(n = 0) /\ &0 < x ==> root n x = x rpow inv (&n)
Proof
    rpt STRIP_TAC
 >> Cases_on ‘n’ >- fs []
 >> rename1 ‘SUC n <> 0’
 >> rw [ROOT_LN, rpow, real_div]
QED

Theorem SQRT_RPOW :
    !(x :real). 0 < x ==> sqrt x = x rpow (inv 2)
Proof
    rw [sqrt, REAL_ROOT_RPOW]
QED

(*----------------------------------------------------------------*)
(* Differentiability of real powers                               *)
(*----------------------------------------------------------------*)

Theorem DIFF_COMPOSITE_EXP :
   !g m x. ((g diffl m) x ==> ((\x. exp (g x)) diffl (exp (g x) * m)) x)
Proof
  RW_TAC std_ss [DIFF_COMPOSITE]
QED

Theorem DIFF_RPOW :
   !x y. 0 < x ==> ((\x. (x rpow y)) diffl (y * (x rpow (y - 1)))) x
Proof
RW_TAC real_ss [rpow,GSYM RPOW_DIV_BASE] THEN
RW_TAC real_ss [REAL_MUL_ASSOC,real_div,REAL_MUL_COMM]THEN
RW_TAC real_ss [GSYM real_div] THEN
KNOW_TAC ``!x'. exp ((y * ln x')) = exp ((\x'. y *ln x') x')`` THEN1
     RW_TAC real_ss [] THEN
DISCH_TAC THEN ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC THEN
KNOW_TAC `` ((y / x) * exp ((\x'. y * ln x') x))= ( exp ((\x'. y * ln x') x)*(y/x) ) `` THEN1
     RW_TAC std_ss [REAL_MUL_COMM] THEN
DISCH_TAC THEN ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC THEN
MATCH_MP_TAC DIFF_COMPOSITE_EXP THEN
KNOW_TAC ``((\x. y * ln x) diffl (y/x)) x = ((\x. y * (\x.ln x) x) diffl (y/x)) x`` THEN1
     RW_TAC real_ss [] THEN
DISCH_TAC THEN ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC THEN
RW_TAC real_ss [real_div] THEN
MATCH_MP_TAC DIFF_CMUL THEN
MATCH_MP_TAC DIFF_LN THEN
RW_TAC real_ss []
QED

Theorem lem[local] :
   !n:num. 0 < n ==> ~(n=0)
Proof
  INDUCT_TAC THEN ASM_REWRITE_TAC [NOT_SUC,NOT_LESS_0]
QED

val real_pow = pow;
val REAL_POW_2 = POW_2;
val REAL_INV_1 = REAL_INV1;

Theorem MCLAURIN_LN_POS :
   !x n.
     &0 < x /\ 0 < n
     ==> ?t. &0 < t /\
             t < x  /\
             (ln(&1 + x)
              = sum(0,n) (\m. ~(&1) pow (SUC m) * (x pow m) / &m)
                +
               ~(&1) pow (SUC n) * x pow n / (&n * (&1 + t) pow n))
Proof
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC (Term`\x. ln(&1 + x)`) MCLAURIN) THEN
  DISCH_THEN(MP_TAC o SPEC
    (Term`\n x. if (n=0) then ln(&1 + x)
                         else ~(&1) pow (SUC n)
                              * &(FACT(PRE n)) * inv((&1 + x) pow n)`)) THEN
  DISCH_THEN(MP_TAC o SPECL [Term`x:real`, Term`n:num`]) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NOT_SUC, REAL_ADD_RID, POW_ONE, LN_1, REAL_INV1,REAL_MUL_RID] THEN
  SUBGOAL_THEN (Term`~((n :num) = 0)`) ASSUME_TAC THENL
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
     GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM REAL_MUL_RID] THEN
     REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
     AP_TERM_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN
     REWRITE_TAC[REAL_OF_NUM_EQ] THEN MATCH_MP_TAC lem THEN
     MATCH_ACCEPT_TAC FACT_LESS], ALL_TAC] THEN
  SUBGOAL_THEN (Term
   `!p. (if p = 0 then &0 else ~(&1) pow (SUC p) * &(FACT (PRE p)))
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
  SUBGOAL_THEN (Term
    `!t. ((~(&1) pow (SUC n) * &(FACT(PRE n)) * inv ((&1 + t) pow n))
          / &(FACT n)) * x pow n
        =
         ~(&1) pow (SUC n) * x pow n / (&n * (&1 + t) pow n)`)
   (fn th => REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN
    AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC LAND_CONV empty_rewrites [REAL_MUL_SYM] THEN AP_TERM_TAC THEN
    REWRITE_TAC [REAL_INV_MUL'] THEN
    GEN_REWRITE_TAC LAND_CONV empty_rewrites [REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[], ALL_TAC] THEN

  rw [real_div] THEN POP_ASSUM MATCH_MP_TAC THEN
  qx_genl_tac [`m`, `u`] THEN STRIP_TAC THEN

  Cases_on `m = 0` THEN ASM_REWRITE_TAC[] THENL
  [ (* goal 1 (of 2) *)
    W(MP_TAC o Q.SPEC `u:real` o DIFF_CONV o lhand o rator o snd) THEN
    REWRITE_TAC[PRE, real_pow, REAL_ADD_LID, REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_MUL_RNEG, REAL_MUL_LNEG, REAL_MUL_RID] THEN
    REWRITE_TAC[FACT, REAL_MUL_RID, REAL_MUL_LID, REAL_NEG_NEG] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    Q.UNDISCH_TAC `&0 <= u` THEN REAL_ARITH_TAC,
    (* goal 2 (of 2) *)
    W(MP_TAC o Q.SPEC `u:real` o DIFF_CONV o lhand o rator o snd) THEN
    Q.SUBGOAL_THEN `~((&1 + u) pow m = &0)` (fn th => REWRITE_TAC[th]) THENL
    [ REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REWRITE_TAC[] THEN
      Q.UNDISCH_TAC `&0 <= u` THEN REAL_ARITH_TAC,
      MATCH_MP_TAC (TAUT_CONV “(a <=> b) ==> a ==> b”) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[REAL_MUL_LZERO, REAL_ADD_RID] THEN
      REWRITE_TAC[REAL_ADD_LID, REAL_MUL_RID] THEN
      REWRITE_TAC[real_div, real_pow, REAL_MUL_LNEG, REAL_MUL_RNEG] THEN
      REWRITE_TAC[REAL_NEG_NEG, REAL_MUL_RID, REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN
      Know ‘&FACT m * -1 pow m * inv ((1 + u) * (1 + u) pow m) =
            &FACT m * inv ((1 + u) * (1 + u) pow m) * -1 pow m’
      >- (METIS_TAC [REAL_MUL_COMM, REAL_MUL_ASSOC]) THEN
      DISCH_THEN (fn th => ONCE_REWRITE_TAC [th]) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      Q.UNDISCH_TAC `~(m = 0)` THEN Q.SPEC_TAC(`m:num`,`p:num`) THEN
      INDUCT_TAC THEN REWRITE_TAC[NOT_SUC] THEN
      REWRITE_TAC[SUC_SUB1, PRE] THEN REWRITE_TAC[FACT] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN
      Know ‘&SUC p * &FACT p * inv ((1 + u) * (1 + u) pow SUC p) =
            &SUC p * inv ((1 + u) * (1 + u) pow SUC p) * &FACT p’
      >- (METIS_TAC [REAL_MUL_COMM, REAL_MUL_ASSOC]) THEN
      DISCH_THEN (fn th => ONCE_REWRITE_TAC [th]) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
      REWRITE_TAC[real_pow, REAL_POW_2] THEN REWRITE_TAC[REAL_INV_MUL'] THEN

      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN
      REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[DE_MORGAN_THM] THEN DISJ1_TAC THEN
      Q.UNDISCH_TAC `&0 <= u` THEN REAL_ARITH_TAC ] ]
QED

Theorem MCLAURIN_LN_NEG :
   !x n. &0 < x /\ x < &1 /\ 0 < n
         ==> ?t. &0 < t /\
                 t < x /\
                 (~(ln(&1 - x)) = sum (0,n) (\m. (x pow m) / &m) +
                                  x pow n / (&n * (&1 - t) pow n))
Proof
  REPEAT STRIP_TAC THEN
  MP_TAC(Q.SPEC `\x. ~(ln(&1 - x))` MCLAURIN) THEN BETA_TAC THEN
  DISCH_THEN(MP_TAC o Q.SPEC
    `\n x. if n = 0 then ~(ln(&1 - x))
           else &(FACT(PRE n)) * inv((&1 - x) pow n)`) THEN
  DISCH_THEN(MP_TAC o Q.SPECL [`x:real`, `n:num`]) THEN BETA_TAC THEN

  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  REWRITE_TAC[NOT_SUC, LN_1, POW_ONE] THEN
  Q.SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [Q.UNDISCH_TAC `0 < n` THEN ARITH_TAC, ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[REAL_INV_1, REAL_MUL_RID, REAL_MUL_LID] THEN
  Q.SUBGOAL_THEN `!p. ~(p = 0) ==> (&(FACT(PRE p)) / &(FACT p) = inv(&p))`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[NOT_SUC, PRE] THEN
    REWRITE_TAC[real_div, FACT, GSYM REAL_OF_NUM_MUL] THEN
    REWRITE_TAC[REAL_INV_MUL'] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM REAL_MUL_RID] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN
    REWRITE_TAC[REAL_OF_NUM_EQ] THEN
    MP_TAC(Q.SPEC `p:num` FACT_LESS) THEN ARITH_TAC, ALL_TAC] THEN
  REWRITE_TAC[REAL_NEG_0] THEN
  Q.SUBGOAL_THEN `!p. (if p = 0 then &0 else &(FACT (PRE p))) / &(FACT p) =
                      inv(&p)`
  (fn th => REWRITE_TAC[th]) THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[REAL_INV_0, real_div, REAL_MUL_LZERO],
      REWRITE_TAC[NOT_SUC] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[NOT_SUC]], ALL_TAC] THEN
  Q.SUBGOAL_THEN
    `!t. (&(FACT(PRE n)) * inv ((&1 - t) pow n)) / &(FACT n) * x pow n
         = x pow n / (&n * (&1 - t) pow n)`
  (fn th => REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[real_div, REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC LAND_CONV empty_rewrites [REAL_MUL_SYM] THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_INV_MUL'] THEN
    GEN_REWRITE_TAC LAND_CONV empty_rewrites [REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN
  Know ‘!m. inv (&m) * x pow m = x pow m * inv (&m)’
  >- METIS_TAC [REAL_MUL_COMM] >> DISCH_THEN (fn th => ONCE_REWRITE_TAC [th]) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  qx_genl_tac [`m:num`, `u:real`] THEN STRIP_TAC THEN
  Cases_on `m = 0` THEN ASM_REWRITE_TAC[] THENL
  [ (* goal 1 (of 2) *)
    W(MP_TAC o Q.SPEC `u` o DIFF_CONV o lhand o rator o snd) THEN
    REWRITE_TAC[PRE, pow, FACT, REAL_SUB_LZERO] THEN
    REWRITE_TAC[REAL_MUL_RNEG, REAL_NEG_NEG, REAL_MUL_RID, REAL_MUL_LID] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    Know ‘u < 1’ >- PROVE_TAC [REAL_LET_TRANS] THEN
    REAL_ARITH_TAC,
    (* goal 2 (of 2) *)
    W(MP_TAC o Q.SPEC `u:real` o DIFF_CONV o lhand o rator o snd) THEN
    Q.SUBGOAL_THEN `~((&1 - u) pow m = &0)` (fn th => REWRITE_TAC[th]) THENL
    [ REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REWRITE_TAC[] THEN
      Q.UNDISCH_TAC `x < &1` THEN Q.UNDISCH_TAC `u:real <= x` THEN
      REAL_ARITH_TAC,
      MATCH_MP_TAC (TAUT_CONV “(a <=> b) ==> a ==> b”) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[REAL_SUB_LZERO, real_div, PRE] THEN
      REWRITE_TAC[REAL_MUL_LZERO, REAL_ADD_RID, REAL_ADD_LID] THEN
      REWRITE_TAC
       [REAL_MUL_RNEG, REAL_MUL_LNEG, REAL_NEG_NEG, REAL_MUL_RID] THEN
      Q.UNDISCH_TAC `~(m = 0)` THEN Q.SPEC_TAC(`m:num`,`p:num`) THEN
      INDUCT_TAC THEN REWRITE_TAC[NOT_SUC] THEN
      REWRITE_TAC[SUC_SUB1, PRE] THEN REWRITE_TAC[FACT] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN
      Know ‘&SUC p * &FACT p * inv ((1 - u) pow SUC (SUC p)) =
            &SUC p * inv ((1 - u) pow SUC (SUC p)) * &FACT p’
      >- (METIS_TAC [REAL_MUL_COMM, REAL_MUL_ASSOC]) THEN
      DISCH_THEN (fn th => ONCE_REWRITE_TAC [th]) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
      REWRITE_TAC[real_pow, REAL_POW_2] THEN REWRITE_TAC[REAL_INV_MUL'] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN
      REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REWRITE_TAC[] THEN
      Q.UNDISCH_TAC `x < &1` THEN Q.UNDISCH_TAC `u:real <= x` THEN
      REAL_ARITH_TAC ] ]
QED

(* ------------------------------------------------------------------------- *)
(* ----------- exp is a convex function (from "miller" example) ------------ *)
(* ------------------------------------------------------------------------- *)

val exp_convex_lemma1 = prove (
   ``!t. (t + (1 - t) * exp 0 - exp ((1 - t) * 0) = 0) /\
         (t * exp 0 + (1 - t) - exp (t * 0) = 0)``,
   RW_TAC real_ss [EXP_0] >> REAL_ARITH_TAC);

val exp_convex_lemma2 = prove (
   ``!t x. ((\x. (1 - t) * exp x - exp ((1 - t) * x)) diffl
            (\x. (1-t) * exp x - (1 - t)*exp ((1-t)*x)) x) x``,
   RW_TAC std_ss []
   >> `(\x. (1 - t) * exp x - exp ((1 - t) * x)) =
       (\x. (\x. (1 - t) * exp x) x - (\x. exp ((1 - t) * x)) x)`
        by RW_TAC std_ss [FUN_EQ_THM]
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> `((1 - t) * exp x - (1 - t) * exp ((1 - t) * x)) =
       (\x. (1 - t) * exp x) x - (\x. (1-t) * exp ((1- t) * x)) x`
        by RW_TAC std_ss []
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> Suff `((\x. (1 - t) * exp x) diffl (\x. (1 - t) * exp x) x) x /\
                ((\x. exp ((1 - t) * x)) diffl (\x. (1 - t) * exp ((1 - t) * x)) x) x`
   >- METIS_TAC [DIFF_SUB]
   >> CONJ_TAC
   >- (`(\x. (1 - t) * exp x) x = 0 * exp x + (exp x) * (\x. 1 - t) x` by RW_TAC real_ss [REAL_MUL_COMM]
       >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
       >> Q.ABBREV_TAC `foo = (0 * exp x + exp x * (\x. 1 - t) x)`
       >> `(\x. (1 - t) * exp x) = (\x. (\x. 1 - t) x * exp x)` by RW_TAC std_ss [FUN_EQ_THM]
       >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
       >> Q.UNABBREV_TAC `foo`
       >> MATCH_MP_TAC DIFF_MUL
       >> RW_TAC std_ss [DIFF_CONST, DIFF_EXP])
   >> `(\x. exp ((1 - t) * x)) = (\x. exp ((\x. (1-t)*x) x))` by RW_TAC std_ss [FUN_EQ_THM]
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> `(\x. (1 - t) * exp ((1 - t) * x)) x = exp ((\x. (1-t)*x) x) * (1-t)`
        by RW_TAC real_ss [REAL_MUL_COMM]
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> Suff `((\x. (1 - t) * x) diffl (1-t)) x` >- METIS_TAC [DIFF_COMPOSITE]
   >> `(1 - t) = (1 - t) * 1` by RW_TAC real_ss []
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> `(\x. (1 - t) * 1 * x) = (\x. (1-t) * (\x. x) x)` by RW_TAC real_ss [FUN_EQ_THM]
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> MATCH_MP_TAC DIFF_CMUL
   >> RW_TAC std_ss [DIFF_X]);

val exp_convex_lemma3 = prove (
   ``!t x. (\x. (1-t) * exp x - exp ((1-t)*x)) contl x``,
   METIS_TAC [DIFF_CONT, exp_convex_lemma2]);

val exp_convex_lemma4 = prove (
   ``!x. 0 < x /\ 0 < t /\ t < 1 ==> 0 < (\x. (1-t) * exp x - (1 - t)*exp ((1-t)*x)) x``,
   RW_TAC real_ss [REAL_LT_SUB_LADD] >> MATCH_MP_TAC REAL_LT_LMUL_IMP
   >> RW_TAC real_ss [REAL_LT_SUB_LADD, EXP_MONO_LT, REAL_SUB_RDISTRIB]
   >> RW_TAC real_ss [REAL_LT_SUB_RADD, REAL_LT_ADDR] >> MATCH_MP_TAC REAL_LT_MUL
   >> RW_TAC real_ss []);

val exp_convex_lemma5 = prove (
   ``!f f' i j. (!x. (f diffl f' x) x) /\
                (!x. f contl x) /\
                (0 <= i /\ i < j) /\
                (!x. i < x /\ x < j ==> 0 < f' x) ==>
                        f i < f j``,
   REPEAT STRIP_TAC
   >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `0 + f i` >> CONJ_TAC >- RW_TAC real_ss []
   >> RW_TAC real_ss [GSYM REAL_LT_SUB_LADD]
   >> `?l z. i < z /\ z < j /\ (f diffl l) z /\ (f j - f i = (j - i) * l)`
        by (MATCH_MP_TAC MVT >> METIS_TAC [differentiable])
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> MATCH_MP_TAC REAL_LT_MUL
   >> RW_TAC real_ss [REAL_LT_SUB_LADD]
   >> `l = f' z`
        by (MATCH_MP_TAC DIFF_UNIQ >> Q.EXISTS_TAC `f` >> Q.EXISTS_TAC `z` >> RW_TAC std_ss [])
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> Q.PAT_X_ASSUM `!x. i < x /\ x < j ==> 0 < f' x` MATCH_MP_TAC >> RW_TAC std_ss []);

val exp_convex_lemma6 = prove (
   ``!x y t. 0 < t /\ t < 1 /\ x < y ==>
                exp (t * x + (1 - t) * y) <= t * exp x + (1 - t) * exp y``,
   REPEAT STRIP_TAC
   >> Q.ABBREV_TAC `z = y - x`
   >> `0 < z` by (Q.UNABBREV_TAC `z` >> RW_TAC real_ss [REAL_LT_SUB_LADD])
   >> Suff `exp (t * x + (1 - t) * (x+z)) <= t * exp x + (1 - t) * exp (x+z)`
   >- (Q.UNABBREV_TAC `z` >> RW_TAC real_ss [])
   >> `t * x + (1 - t) * (x + z) = x + (1 - t) * z` by REAL_ARITH_TAC
   >> ASM_REWRITE_TAC [] >> POP_ASSUM (K ALL_TAC)
   >> PURE_REWRITE_TAC [EXP_ADD]
   >> `t * exp x + (1 - t) * (exp x * exp z) = exp x * (t + (1 - t) * exp z)`
                by REAL_ARITH_TAC
   >> ASM_REWRITE_TAC [] >> POP_ASSUM (K ALL_TAC)
   >> MATCH_MP_TAC REAL_LE_LMUL_IMP >> CONJ_TAC >- SIMP_TAC std_ss [EXP_POS_LE]
   >> MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `0 + exp ((1 - t) * z)` >> CONJ_TAC >- RW_TAC real_ss []
   >> ONCE_REWRITE_TAC [GSYM REAL_LE_SUB_LADD]
   >> MATCH_MP_TAC REAL_LT_IMP_LE
   >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `t + (1 - t) * exp 0 - exp ((1 - t) * 0)`
   >> CONJ_TAC >- RW_TAC real_ss [exp_convex_lemma1]
   >> `t + (1 - t) * exp 0 - exp ((1 - t) * 0) = ((1 - t) * exp 0 - exp ((1 - t) * 0)) + t`
                by REAL_ARITH_TAC >> ASM_REWRITE_TAC [] >> POP_ASSUM (K ALL_TAC)
   >> ONCE_REWRITE_TAC [REAL_LT_ADD_SUB]
   >> `t + (1 - t) * exp z - exp ((1 - t) * z) - t = (1 - t) * exp z - exp ((1 - t) * z)`
                by REAL_ARITH_TAC
   >> ASM_REWRITE_TAC [] >> POP_ASSUM (K ALL_TAC)
   >> Q.ABBREV_TAC `f = (\x. (1-t) * exp x - exp ((1-t)*x))`
   >> Suff `f 0 < f z` >- (Q.UNABBREV_TAC `f` >> RW_TAC std_ss [])
   >> MATCH_MP_TAC exp_convex_lemma5
   >> Q.EXISTS_TAC `(\x. (1-t) * exp x - (1 - t)*exp ((1-t)*x))`
   >> Q.UNABBREV_TAC `f`
   >> RW_TAC real_ss [exp_convex_lemma2, exp_convex_lemma3, exp_convex_lemma4]);

val exp_convex = store_thm
  ("exp_convex",
   ``exp IN convex_fn``,
   RW_TAC std_ss [convex_fn, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION]
   >> Cases_on `t = 0` >- RW_TAC real_ss []
   >> Cases_on `t = 1` >- RW_TAC real_ss []
   >> `0 < t /\ t < 1` by METIS_TAC [REAL_LT_LE]
   >> Cases_on `x = y` >- RW_TAC real_ss []
   >> (MP_TAC o Q.SPECL [`x`, `y`]) REAL_LT_TOTAL >> RW_TAC std_ss []
   >- (MATCH_MP_TAC exp_convex_lemma6 >> RW_TAC std_ss [])
   >> Q.ABBREV_TAC `t' = 1 - t`
   >> `t = 1 - t'` by (Q.UNABBREV_TAC `t'` >> REAL_ARITH_TAC)
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> `0 < t'` by (Q.UNABBREV_TAC `t'` >> RW_TAC real_ss [REAL_LT_SUB_LADD])
   >> `t' < 1` by (Q.UNABBREV_TAC `t'` >> RW_TAC real_ss [REAL_LT_SUB_RADD, REAL_LT_ADDR])
   >> ONCE_REWRITE_TAC [REAL_ADD_COMM]
   >> MATCH_MP_TAC exp_convex_lemma6 >> RW_TAC std_ss []);

(* ------------------------------------------------------------------------- *)
(* ------------ ln and lg are concave on (0,infty] ------------------------- *)
(* ------------------------------------------------------------------------- *)

Theorem pos_concave_ln :
    ln IN pos_concave_fn
Proof
   RW_TAC std_ss [pos_concave_fn, pos_convex_fn, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION]
   >> Cases_on `t = 0` >- RW_TAC real_ss []
   >> Cases_on `t = 1` >- RW_TAC real_ss []
   >> `0 < t /\ t < 1` by RW_TAC std_ss [REAL_LT_LE]
   >> `t * ~ln x + (1 - t) * ~ln y = ~ (t * ln x + (1 - t)* ln y)` by REAL_ARITH_TAC
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> RW_TAC std_ss [REAL_LE_NEG, ln]
   >> MATCH_MP_TAC SELECT_ELIM_THM
   >> RW_TAC std_ss [] >- (MATCH_MP_TAC EXP_TOTAL
                           >> MATCH_MP_TAC REAL_LT_ADD >> CONJ_TAC >> MATCH_MP_TAC REAL_LT_MUL
                           >> RW_TAC real_ss [GSYM REAL_LT_ADD_SUB])
   >> Suff `(\v. t * v + (1 - t) * (@u. exp u = y) <= x') (@u. exp u = x)`
   >- RW_TAC std_ss []
   >> MATCH_MP_TAC SELECT_ELIM_THM
   >> RW_TAC std_ss [] >- (MATCH_MP_TAC EXP_TOTAL >> RW_TAC std_ss [])
   >> Suff `(\v. t * x'' + (1 - t) * v <= x') (@u. exp u = y)`
   >- RW_TAC std_ss []
   >> MATCH_MP_TAC SELECT_ELIM_THM
   >> RW_TAC std_ss [] >- (MATCH_MP_TAC EXP_TOTAL >> RW_TAC std_ss [])
   >> ONCE_REWRITE_TAC [GSYM EXP_MONO_LE]
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> MP_TAC exp_convex
   >> RW_TAC std_ss [convex_fn, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION]
QED

Theorem convex_lemma[local] :
    !x y t. 0 < x /\ 0 < y /\ 0 <= t /\ t <= 1 ==> 0 < x * t + y * (1 - t)
Proof
    rpt STRIP_TAC
 >> Cases_on ‘t = 0’ >- rw []
 >> Cases_on ‘t = 1’ >- rw []
 >> MATCH_MP_TAC REAL_LT_ADD
 >> CONJ_TAC
 >| [ MATCH_MP_TAC REAL_LT_MUL >> rw [REAL_LT_LE],
      MATCH_MP_TAC REAL_LT_MUL >> rw [REAL_LT_SUB_LADD, REAL_LT_LE] ]
QED

(* inv is pos_convex *)
Theorem pos_convex_inv :
    inv IN pos_convex_fn
Proof
    simp [pos_convex_fn]
 >> qx_genl_tac [‘x’, ‘y’, ‘t’]
 >> STRIP_TAC
 >> ‘x <> 0 /\ y <> 0’ by PROVE_TAC [REAL_POS_NZ]
 >> Know ‘t * inv x + inv y * (1 - t) = (y * t + x * (1 - t)) / (x * y)’
 >- (rw [real_div, REAL_ADD_RDISTRIB, REAL_ADD_LDISTRIB])
 >> Rewr'
 >> Know ‘(y * t + x * (1 - t)) / (x * y) = inv (x * y / (y * t + x * (1 - t)))’
 >- (rw [real_div, REAL_INV_MUL'])
 >> Rewr'
 >> Know ‘inv (t * x + y * (1 - t)) <= inv (x * y / (y * t + x * (1 - t))) <=>
          x * y / (y * t + x * (1 - t)) <= t * x + y * (1 - t)’
 >- (MATCH_MP_TAC REAL_INV_LE_ANTIMONO \\
     simp [real_div] \\
     CONJ_TAC >- PROVE_TAC [REAL_MUL_COMM, convex_lemma] \\
     MATCH_MP_TAC REAL_LT_MUL \\
     CONJ_TAC >- (MATCH_MP_TAC REAL_LT_MUL >> art []) \\
     REWRITE_TAC [REAL_LT_INV_EQ] \\
     PROVE_TAC [REAL_MUL_COMM, convex_lemma])
 >> Rewr'
 >> Know ‘x * y / (y * t + x * (1 - t)) <= t * x + y * (1 - t) <=>
          x * y <= (t * x + y * (1 - t)) * (y * t + x * (1 - t))’
 >- (MATCH_MP_TAC REAL_LE_LDIV_EQ \\
     PROVE_TAC [convex_lemma])
 >> Rewr'
 >> rw [REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB, REAL_ADD_ASSOC]
 >> Know ‘x * y = t pow 2 * x * y + t * (2 * x * y) * (1 - t) +
                  x * y * (1 - t) pow 2’
 >- (GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM REAL_MUL_RID] \\
     Know ‘1 = (t + (1 - t)) pow 2’
     >- (‘t + (1 - t) = 1’ by REAL_ARITH_TAC >> POP_ORW \\
         rw [pow]) \\
     DISCH_THEN ((GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites) o wrap) \\
     REWRITE_TAC [POW_2, REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB] \\
     REAL_ARITH_TAC)
 >> DISCH_THEN ((GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites) o wrap)
 >> REWRITE_TAC [REAL_LE_RADD]
 >> REWRITE_TAC [GSYM REAL_ADD_ASSOC, REAL_LE_LADD]
 >> REWRITE_TAC [GSYM REAL_ADD_LDISTRIB, GSYM REAL_ADD_RDISTRIB]
 >> MATCH_MP_TAC REAL_LE_RMUL_IMP
 >> CONJ_TAC >- (rw [REAL_LE_SUB_LADD])
 >> MATCH_MP_TAC REAL_LE_LMUL_IMP >> art []
 >> Know ‘0 <= (x - y) pow 2’ >- PROVE_TAC [REAL_LE_POW2]
 >> Know ‘(x - y) pow 2 = x pow 2 + y pow 2 - 2 * x * y’
 >- (REWRITE_TAC [POW_2] >> REAL_ARITH_TAC)
 >> Rewr'
 >> rw [REAL_LE_SUB_LADD]
QED

(* |- 0 < -x /\ -x < 1 ==>
      ?t. 0 < t /\ t < -x /\ ln (1 + x) = x * realinv (1 - t)
 *)
val lemma =
    SIMP_RULE real_ss [REAL_NEG_0, real_div, REAL_INV_0, POW_1, REAL_EQ_NEG]
                      (REWRITE_RULE [sum, ONE]
                                    (Q.SPECL [‘-x’, ‘1’] MCLAURIN_LN_NEG));

(* An extended version of EXP_LE_X to entire reals, based on MCLAURIN_LN_NEG *)
Theorem EXP_LE_X_FULL :
    !x :real. &1 + x <= exp x
Proof
    Q.X_GEN_TAC ‘x’
 >> Cases_on `0 <= x`
 >- (MATCH_MP_TAC EXP_LE_X >> art [])
 >> FULL_SIMP_TAC std_ss [GSYM real_lt]
 >> Cases_on `x <= -1`
 >- (MATCH_MP_TAC REAL_LE_TRANS \\
     Q.EXISTS_TAC `0` >> REWRITE_TAC [EXP_POS_LE] \\
    `0r = 1 + -1` by RW_TAC real_ss [] \\
     POP_ORW >> art [REAL_LE_LADD])
 >> FULL_SIMP_TAC std_ss [GSYM real_lt]
 >> MP_TAC lemma
 >> ‘0 < -x /\ -x < 1’ by REAL_ASM_ARITH_TAC
 >> RW_TAC std_ss []
 >> MATCH_MP_TAC REAL_LT_IMP_LE
 >> Know ‘1 + x < exp x <=> ln (1 + x) < ln (exp x)’
 >- (MATCH_MP_TAC (GSYM LN_MONO_LT) \\
     REWRITE_TAC [EXP_POS_LT] >> REAL_ASM_ARITH_TAC)
 >> Rewr'
 >> POP_ORW
 >> REWRITE_TAC [LN_EXP]
 >> GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM REAL_MUL_RID]
 >> Know ‘x * inv (1 - t) < x * 1 <=> 1 < inv (1 - t)’
 >- (MATCH_MP_TAC REAL_LT_LMUL_NEG >> art [])
 >> Rewr'
 >> MATCH_MP_TAC REAL_INV_LT1
 >> REAL_ASM_ARITH_TAC
QED

(* ------------------------------------------------------------------------- *)
(*   Transcendental functions and ‘product’                                  *)
(* ------------------------------------------------------------------------- *)

Theorem LN_PRODUCT :
    !f s. FINITE s /\ (!x. x IN s ==> &0 < f x) ==>
          ln (product s f) = sum s (\x. ln (f x))
Proof
    rpt STRIP_TAC
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> Q.SPEC_TAC (‘s’, ‘s’)
 >> HO_MATCH_MP_TAC FINITE_INDUCT
 >> rw [PRODUCT_CLAUSES, SUM_CLAUSES, LN_1]
 >> ‘0 < f e’ by PROVE_TAC []
 >> ‘0 < product s f’ by (MATCH_MP_TAC PRODUCT_POS_LT >> rw [])
 >> rw [LN_MUL]
QED

(* NOTE: added ‘n <> 0 /\ (!x. x IN s ==> &0 <= f x)’ to hol-light's statements *)
Theorem ROOT_PRODUCT :
    !n f s. FINITE s /\ n <> 0 /\ (!x. x IN s ==> &0 <= f x)
        ==> root n (product s f) = product s (\i. root n (f i))
Proof
    rpt STRIP_TAC
 >> Cases_on ‘n’ >- fs []
 >> rename1 ‘SUC n <> 0’
 >> POP_ASSUM MP_TAC
 >> Q.PAT_X_ASSUM ‘FINITE s’ MP_TAC
 >> Q.SPEC_TAC (‘s’, ‘s’)
 >> HO_MATCH_MP_TAC FINITE_INDUCT
 >> rw [PRODUCT_CLAUSES, ROOT_1]
 >> ‘0 <= f e’ by PROVE_TAC []
 >> ‘0 <= product s f’ by (MATCH_MP_TAC PRODUCT_POS_LE >> rw [])
 >> rw [ROOT_MUL]
QED

(* ------------------------------------------------------------------------- *)
(* Some convexity-derived inequalities including AGM and Young's inequality. *)
(* Ported from hol-light (AGM stands for "arithmetic and geometric means")   *)
(* ------------------------------------------------------------------------- *)

(* NOTE: changed ‘0 <= x i’ (hol-light) to ‘0 < x i’ *)
Theorem AGM_GEN :
    !a x s. FINITE s /\ sum s a = &1 /\ (!i. i IN s ==> &0 <= a i /\ &0 < x i)
        ==> product s (\i. x i rpow a i) <= sum s (\i. a i * x i)
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘f = \i. x i rpow a i’
 >> Know ‘!n. n IN s ==> 0 < f n’
 >- (rw [Abbr ‘f’] \\
     MATCH_MP_TAC RPOW_POS_LT >> rw [])
 >> DISCH_TAC
 >> Know ‘product s f <= sum s (\i. a i * x i) <=>
          ln (product s f) <= ln (sum s (\i. a i * x i))’
 >- (MATCH_MP_TAC (GSYM LN_MONO_LE) >> CONJ_TAC >|
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC PRODUCT_POS_LT >> simp [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC SUM_POS_LT >> simp [] \\
       CONJ_TAC >- (Q.X_GEN_TAC ‘n’ >> DISCH_TAC \\
                    MATCH_MP_TAC REAL_LE_MUL >> rw [] \\
                    MATCH_MP_TAC REAL_LT_IMP_LE >> rw []) \\
       Cases_on ‘?i. i IN s /\ 0 < a i’
       >- (POP_ASSUM STRIP_ASSUME_TAC >> Q.EXISTS_TAC ‘i’ >> art [] \\
           MATCH_MP_TAC REAL_LT_MUL >> rw []) \\
       FULL_SIMP_TAC std_ss [GSYM IMP_DISJ_THM, GSYM real_lte] \\
       Know ‘sum s a <= &CARD s * 0’
       >- (MATCH_MP_TAC SUM_BOUND' >> rw []) >> rw [] ])
 >> Rewr'
 >> Know ‘ln (product s f) = sum s (\x. ln (f x))’
 >- (MATCH_MP_TAC LN_PRODUCT >> rw [])
 >> Rewr'
 >> Know ‘!g. sum s g = SIGMA g s’
 >- (Q.X_GEN_TAC ‘g’ \\
     MATCH_MP_TAC (GSYM REAL_SUM_IMAGE_sum) >> art [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> simp [Abbr ‘f’]
 >> Know ‘SIGMA (\x'. ln (x x' rpow a x')) s = SIGMA (\i. a i * ln (x i)) s’
 >- (MATCH_MP_TAC REAL_SUM_IMAGE_EQ >> art [] \\
     Q.X_GEN_TAC ‘i’ >> rw [] \\
     MATCH_MP_TAC LN_RPOW >> rw [])
 >> Rewr'
 >> MP_TAC (Q.SPECL [‘ln’, ‘a’, ‘x’]
                    (MATCH_MP jensen_pos_concave_SIGMA (ASSUME “FINITE s”)))
 >> rw [pos_concave_ln]
 >> POP_ASSUM MATCH_MP_TAC
 >> MATCH_MP_TAC SUM_POS_BOUND >> rw []
 >> Suff ‘sum s a = SIGMA a s’ >- rw [REAL_LE_REFL]
 >> MATCH_MP_TAC (GSYM REAL_SUM_IMAGE_sum) >> art []
QED

(* NOTE: changed ‘0 <= x i’ (hol-light) to ‘0 < x i’ *)
Theorem AGM_RPOW :
    !s x n. s HAS_SIZE n /\ ~(n = 0) /\ (!i. i IN s ==> &0 < x(i))
        ==> product s (\i. x(i) rpow (&1 / &n)) <= sum s (\i. x(i) / &n)
Proof
    RW_TAC std_ss [HAS_SIZE]
 >> MP_TAC (Q.SPECL [‘\i. &1 / &CARD (s :'a set)’, ‘x’, ‘s’] AGM_GEN)
 >> rw [SUM_CONST, GSYM real_div]
QED

Theorem AGM_ROOT :
    !s x n. s HAS_SIZE n /\ ~(n = 0) /\ (!i. i IN s ==> &0 <= x(i))
        ==> root n (product s x) <= sum s x / &n
Proof
    RW_TAC std_ss [HAS_SIZE]
 >> Cases_on ‘!i. i IN s ==> &0 < x(i)’
 >- (RW_TAC std_ss [ROOT_PRODUCT, real_div] \\
     Know ‘product s (\i. root (CARD s) (x i)) =
           product s (\i. (x i) rpow (inv &CARD s))’
     >- (MATCH_MP_TAC PRODUCT_EQ \\
         Q.X_GEN_TAC ‘i’ >> rw [REAL_ROOT_RPOW]) >> Rewr' \\
     REWRITE_TAC [GSYM SUM_RMUL] \\
     REWRITE_TAC [GSYM real_div, REAL_INV_1OVER] \\
     MATCH_MP_TAC AGM_RPOW >> rw [HAS_SIZE])
 (* extra work to support ‘!i. i IN s ==> 0 <= x i’ *)
 >> FULL_SIMP_TAC std_ss [real_lt]
 >> ‘x i = 0’ by PROVE_TAC [REAL_LE_ANTISYM]
 >> Know ‘product s x = 0’
 >- (REWRITE_TAC [MATCH_MP PRODUCT_EQ_0 (ASSUME “FINITE s”)] \\
     Q.EXISTS_TAC ‘i’ >> art [])
 >> Rewr'
 >> Q.ABBREV_TAC ‘n = CARD s’
 >> Cases_on ‘n’ >- fs []
 >> rw [ROOT_0]
 >> MATCH_MP_TAC SUM_POS_LE >> rw []
QED

Theorem AGM_SQRT :
    !x y. &0 <= x /\ &0 <= y ==> sqrt(x * y) <= (x + y) / &2
Proof
    rpt STRIP_TAC
 >> MP_TAC (ISPECL [“{0; (1:num)}”,
                    “\(n :num). if n = 0 then (x:real) else (y:real)”,
                    “(2:num)”] AGM_ROOT)
 >> ‘FINITE {0; (1:num)}’ by PROVE_TAC [FINITE_INSERT, FINITE_SING]
 >> simp [SUM_CLAUSES, PRODUCT_CLAUSES, sqrt]
 >> DISCH_THEN MATCH_MP_TAC
 >> rw [HAS_SIZE]
QED

Theorem AGM :
    !s x n. s HAS_SIZE n /\ ~(n = 0) /\ (!i. i IN s ==> &0 <= x(i))
        ==> product s x <= (sum s x / &n) pow n
Proof
    rpt STRIP_TAC
 >> Cases_on ‘n’ >- fs []
 >> rename1 ‘SUC n <> 0’
 >> Know ‘0 <= sum s x / &SUC n’
 >- (MATCH_MP_TAC REAL_LE_DIV >> rw [] \\
     MATCH_MP_TAC SUM_POS_LE >> rw [])
 >> DISCH_TAC
 >> Know ‘product s x <= (sum s x / &SUC n) pow (SUC n) <=>
          root (SUC n) (product s x) <=
          root (SUC n) ((sum s x / &(SUC n)) pow (SUC n))’
 >- (MATCH_MP_TAC (GSYM ROOT_MONO_LE_EQ) >> rw [] \\
     MATCH_MP_TAC PRODUCT_POS_LE >> fs [HAS_SIZE])
 >> Rewr'
 >> RW_TAC std_ss [POW_ROOT_POS]
 >> MATCH_MP_TAC AGM_ROOT >> rw []
QED

(* NOTE: changed ‘0 <= x /\ 0 <= y’ (hol-light) to ‘0 < x /\ 0 < y’ *)
Theorem AGM_2 :
    !x y u v. &0 < x /\ &0 < y /\ &0 <= u /\ &0 <= v /\ u + v = &1
          ==> x rpow u * y rpow v <= u * x + v * y
Proof
    rpt STRIP_TAC
 >> qspecl_then [‘\i. if i = 0n then u else v’, ‘\i. if i = 0 then x else y’,
                 ‘{0..SUC 0}’] MP_TAC AGM_GEN
 >> simp [SUM_CLAUSES_NUMSEG, PRODUCT_CLAUSES_NUMSEG, FINITE_NUMSEG]
 >> DISCH_THEN MATCH_MP_TAC
 >> rw []
QED

(* NOTE: changed ‘0 <= a /\ 0 <= b’ (hol-light) to ‘0 < a /\ 0 < b’ *)
Theorem YOUNG_INEQUALITY :
    !a b p q. &0 < a /\ &0 < b /\ &0 < p /\ &0 < q /\ inv(p) + inv(q) = &1
          ==> a * b <= a rpow p / p + b rpow q / q
Proof
    rpt STRIP_TAC
 >> ‘p <> 0 /\ q <> 0’ by PROVE_TAC [REAL_LT_IMP_NE]
 >> ‘0 <= p /\ 0 <= q’ by PROVE_TAC [REAL_LT_IMP_LE]
 >> MP_TAC (Q.SPECL [`a rpow p`, `b rpow q`, `inv p:real`, `inv q:real`] AGM_2)
 >> rw [RPOW_RPOW, RPOW_1, RPOW_POS_LT, real_div]
QED

val _ = export_theory();
