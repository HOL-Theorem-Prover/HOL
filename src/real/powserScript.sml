(*===========================================================================*)
(* Properties of power series.                                               *)
(*===========================================================================*)

(*
*)
structure powserScript =
struct

(*
app load ["numLib",
          "reduceLib",
          "pairTheory",
          "numLib",
          "PairedLambda",
          "jrhUtils",
          "topologyTheory",
          "netsTheory",
          "seqTheory",
          "limTheory"];
*)

open HolKernel Parse boolLib hol88Lib numLib reduceLib pairLib
     pairTheory arithmeticTheory numTheory prim_recTheory
     jrhUtils realTheory topologyTheory netsTheory seqTheory limTheory;

infix THEN THENL ORELSE ORELSEC ##;

val _ = new_theory "powser";


(*---------------------------------------------------------------------------*)
(* More theorems about rearranging finite sums                               *)
(*---------------------------------------------------------------------------*)

val POWDIFF_LEMMA = store_thm("POWDIFF_LEMMA",
  (--`!n x y. sum(0,SUC n)(\p. (x pow p) * y pow ((SUC n) - p)) =
                y * sum(0,SUC n)(\p. (x pow p) * (y pow (n - p)))`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_CMUL] THEN
  MATCH_MP_TAC SUM_SUBST THEN X_GEN_TAC (--`p:num`--) THEN DISCH_TAC THEN
  BETA_TAC THEN GEN_REWR_TAC RAND_CONV [REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN (--`~(n:num < p)`--) ASSUME_TAC THENL
   [POP_ASSUM(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[ADD_CLAUSES] THEN
    REWRITE_TAC[NOT_LESS, LESS_THM] THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THEN
    REWRITE_TAC[LESS_EQ_REFL, LESS_IMP_LESS_OR_EQ],
    ASM_REWRITE_TAC[SUB] THEN REWRITE_TAC[pow] THEN
    MATCH_ACCEPT_TAC REAL_MUL_SYM]);

val POWDIFF = store_thm("POWDIFF",
  (--`!n x y.
      (x pow (SUC n)) - (y pow (SUC n))
         =
      (x - y) * sum(0,SUC n) (\p. (x pow p) * (y pow (n-p)))`--),
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[sum] THEN
    REWRITE_TAC[REAL_ADD_LID, ADD_CLAUSES, SUB_0] THEN
    BETA_TAC THEN REWRITE_TAC[pow] THEN
    REWRITE_TAC[REAL_MUL_RID],
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[sum] THEN
    REWRITE_TAC[ADD_CLAUSES] THEN BETA_TAC THEN
    REWRITE_TAC[POWDIFF_LEMMA] THEN REWRITE_TAC[REAL_LDISTRIB] THEN
    ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
      (--`a * (b * c) = b * (a * c)`--)] THEN
    POP_ASSUM(fn th => ONCE_REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[SUB_EQUAL_0] THEN
    SPEC_TAC((--`SUC n`--),(--`n:num`--)) THEN GEN_TAC THEN
    REWRITE_TAC[pow, REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_LDISTRIB, REAL_SUB_LDISTRIB] THEN
    REWRITE_TAC[real_sub] THEN
    ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
      (--`(a + b) + (c + d) = (d + a) + (c + b)`--)] THEN
    GEN_REWR_TAC (funpow 2 LAND_CONV) [REAL_MUL_SYM] THEN
    CONV_TAC SYM_CONV THEN REWRITE_TAC[REAL_ADD_LID_UNIQ] THEN
    GEN_REWR_TAC (LAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_ADD_LINV]]);

val POWREV = store_thm("POWREV",
  (--`!n x y. sum(0,SUC n)(\p. (x pow p) * (y pow (n - p))) =
                sum(0,SUC n)(\p. (x pow (n - p)) * (y pow p))`--),
  let val REAL_EQ_LMUL2' = CONV_RULE(REDEPTH_CONV FORALL_IMP_CONV) REAL_EQ_LMUL2 in
  REPEAT GEN_TAC THEN ASM_CASES_TAC (--`x:real = y`--) THENL
   [ASM_REWRITE_TAC[GSYM POW_ADD] THEN
    MATCH_MP_TAC SUM_SUBST THEN X_GEN_TAC (--`p:num`--) THEN
    BETA_TAC THEN DISCH_TAC THEN AP_TERM_TAC THEN
    MATCH_ACCEPT_TAC ADD_SYM,
    GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV)  [REAL_MUL_SYM] THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM REAL_SUB_0]) THEN
    FIRST_ASSUM(fn th => GEN_REWR_TAC I  [MATCH_MP REAL_EQ_LMUL2' th]) THEN
    GEN_REWR_TAC RAND_CONV  [GSYM REAL_NEGNEG] THEN
    ONCE_REWRITE_TAC[REAL_NEG_LMUL] THEN
    ONCE_REWRITE_TAC[REAL_NEG_SUB] THEN
    REWRITE_TAC[GSYM POWDIFF] THEN REWRITE_TAC[REAL_NEG_SUB]] end);

(*---------------------------------------------------------------------------*)
(* Show (essentially) that a power series has a "circle" of convergence, i.e.*)
(* if it sums for x, then it sums absolutely for z with |z| < |x|            *)
(*---------------------------------------------------------------------------*)

val POWSER_INSIDEA = store_thm("POWSER_INSIDEA",
  (--`!f x z. summable (\n. f(n) * (x pow n)) /\ abs(z) < abs(x)
        ==> summable (\n. abs(f(n)) * (z pow n))`--),
  let val th = (GEN_ALL o CONV_RULE LEFT_IMP_EXISTS_CONV o snd o
              EQ_IMP_RULE o SPEC_ALL) convergent in
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_ZERO) THEN
  DISCH_THEN(MP_TAC o MATCH_MP th) THEN REWRITE_TAC[GSYM SEQ_CAUCHY] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SEQ_CBOUNDED) THEN
  REWRITE_TAC[SEQ_BOUNDED] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC (--`k':real`--)) THEN MATCH_MP_TAC SER_COMPAR THEN
  EXISTS_TAC (--`\n. (k' * abs(z pow n)) / abs(x pow n)`--) THEN CONJ_TAC THENL
   [EXISTS_TAC (--`0:num`--) THEN X_GEN_TAC (--`n:num`--) THEN DISCH_THEN(K ALL_TAC) THEN
    BETA_TAC THEN MATCH_MP_TAC REAL_LE_RDIV THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM ABS_NZ] THEN MATCH_MP_TAC POW_NZ THEN
      REWRITE_TAC[ABS_NZ] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC (--`abs(z)`--) THEN ASM_REWRITE_TAC[ABS_POS],
      REWRITE_TAC[ABS_MUL, ABS_ABS, GSYM REAL_MUL_ASSOC] THEN
      ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
       (--`a * (b * c) = (a * c) * b`--)] THEN
      DISJ_CASES_TAC(SPEC (--`z pow n`--) ABS_CASES) THEN
      ASM_REWRITE_TAC[ABS_0, REAL_MUL_RZERO, REAL_LE_REFL] THEN
      FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_LE_RMUL th]) THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[GSYM ABS_MUL]],
    REWRITE_TAC[summable] THEN
    EXISTS_TAC (--`k' * inv(&1 - (abs(z) / abs(x)))`--) THEN
    REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN
    CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SER_CMUL THEN
    GEN_REWR_TAC (RATOR_CONV o ONCE_DEPTH_CONV)  [GSYM real_div] THEN
    SUBGOAL_THEN (--`!n. abs(z pow n) / abs(x pow n) =
                        (abs(z) / abs(x)) pow n`--)
    (fn th => ONCE_REWRITE_TAC[th]) THENL
     [ALL_TAC, REWRITE_TAC[GSYM real_div] THEN
      MATCH_MP_TAC GP THEN REWRITE_TAC[real_div, ABS_MUL] THEN
      SUBGOAL_THEN (--`~(abs(x) = &0)`--) (SUBST1_TAC o MATCH_MP ABS_INV) THENL
       [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (--`abs(z) < &0`--) THEN
        REWRITE_TAC[REAL_NOT_LT, ABS_POS],
        REWRITE_TAC[ABS_ABS, GSYM real_div] THEN
        MATCH_MP_TAC REAL_LT_1 THEN ASM_REWRITE_TAC[ABS_POS]]] THEN
    REWRITE_TAC[GSYM POW_ABS] THEN X_GEN_TAC (--`n:num`--) THEN
    REWRITE_TAC[real_div, POW_MUL] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC POW_INV THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`abs(z)`--) THEN
    ASM_REWRITE_TAC[ABS_POS]] end);

(*---------------------------------------------------------------------------*)
(* Weaker but more commonly useful form for non-absolute convergence         *)
(*---------------------------------------------------------------------------*)

val POWSER_INSIDE = store_thm("POWSER_INSIDE",
  (--`!f x z. summable (\n. f(n) * (x pow n)) /\ abs(z) < abs(x)
        ==> summable (\n. f(n) * (z pow n))`--),
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPEC (--`z:real`--) ABS_ABS)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP POWSER_INSIDEA) THEN
  REWRITE_TAC[POW_ABS, GSYM ABS_MUL] THEN
  DISCH_THEN(curry op THEN (MATCH_MP_TAC SER_ACONV) o MP_TAC) THEN
  BETA_TAC THEN DISCH_THEN ACCEPT_TAC);

(*---------------------------------------------------------------------------*)
(* Define formal differentiation of power series                             *)
(*---------------------------------------------------------------------------*)

val diffs = new_definition("diffs",
  (--`diffs c = (\n. &(SUC n) * c(SUC n))`--));

(*---------------------------------------------------------------------------*)
(* Lemma about distributing negation over it                                 *)
(*---------------------------------------------------------------------------*)

val DIFFS_NEG = store_thm("DIFFS_NEG",
  (--`!c. diffs(\n. ~(c n)) = \n. ~((diffs c) n)`--),
  GEN_TAC THEN REWRITE_TAC[diffs] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_NEG_RMUL]);

(*---------------------------------------------------------------------------*)
(* Show that we can shift the terms down one                                 *)
(*---------------------------------------------------------------------------*)

val DIFFS_LEMMA = store_thm("DIFFS_LEMMA",
  (--`!n c x. sum(0,n) (\n. (diffs c)(n) * (x pow n)) =
           sum(0,n) (\n. &n * (c(n) * (x pow (n - 1)))) +
             (&n * (c(n) * x pow (n - 1)))`--),
  INDUCT_TAC THEN ASM_REWRITE_TAC[sum, REAL_MUL_LZERO, REAL_ADD_LID] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN
  AP_TERM_TAC THEN BETA_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
  AP_TERM_TAC THEN REWRITE_TAC[diffs] THEN BETA_TAC THEN
  REWRITE_TAC[SUC_SUB1, REAL_MUL_ASSOC]);

val DIFFS_LEMMA2 = store_thm("DIFFS_LEMMA2",
  (--`!n c x. sum(0,n) (\n. &n * (c(n) * (x pow (n - 1)))) =
           sum(0,n) (\n. (diffs c)(n) * (x pow n)) -
                (&n * (c(n) * x pow (n - 1)))`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_EQ_SUB_LADD, DIFFS_LEMMA]);

val DIFFS_EQUIV = store_thm("DIFFS_EQUIV",
  (--`!c x. summable(\n. (diffs c)(n) * (x pow n)) ==>
      (\n. &n * (c(n) * (x pow (n - 1)))) sums
         (suminf(\n. (diffs c)(n) * (x pow n)))`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[diffs] o MATCH_MP SER_ZERO) THEN
  BETA_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN DISCH_TAC THEN
  SUBGOAL_THEN (--`(\n. &n * (c(n) * (x pow (n - 1)))) --> &0`--)
  MP_TAC THENL
   [ONCE_REWRITE_TAC[SEQ_SUC] THEN BETA_TAC THEN
    ASM_REWRITE_TAC[SUC_SUB1], ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJ (MATCH_MP SUMMABLE_SUM
   (ASSUME (--`summable(\n. (diffs c)(n) * (x pow n))`--)))) THEN
  REWRITE_TAC[sums] THEN DISCH_THEN(MP_TAC o MATCH_MP SEQ_SUB) THEN
  BETA_TAC THEN REWRITE_TAC[GSYM DIFFS_LEMMA2] THEN
  REWRITE_TAC[REAL_SUB_RZERO]);

(*===========================================================================*)
(* Show term-by-term differentiability of power series                       *)
(* (NB we hypothesize convergence of first two derivatives; we could prove   *)
(*  they all have the same radius of convergence, but we don't need to.)     *)
(*===========================================================================*)

val TERMDIFF_LEMMA1 = store_thm("TERMDIFF_LEMMA1",
  (--`!m z h.
     sum(0,m)(\p. (((z + h) pow (m - p)) * (z pow p)) - (z pow m)) =
       sum(0,m)(\p. (z pow p) *
       (((z + h) pow (m - p)) - (z pow (m - p))))`--),
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_SUBST THEN
  X_GEN_TAC (--`p:num`--) THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB, GSYM POW_ADD] THEN BINOP_TAC THENL
   [MATCH_ACCEPT_TAC REAL_MUL_SYM,
    AP_TERM_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUB_ADD THEN
    MATCH_MP_TAC LESS_IMP_LESS_OR_EQ THEN
    POP_ASSUM(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[ADD_CLAUSES]]);

val TERMDIFF_LEMMA2 = store_thm("TERMDIFF_LEMMA2",
  (--`!z h n. ~(h = &0) ==>
       (((((z + h) pow n) - (z pow n)) / h) - (&n * (z pow (n - 1))) =
        h * sum(0,n - 1)(\p. (z pow p) *
              sum(0,(n - 1) - p)
                (\q. ((z + h) pow q) *
                       (z pow (((n - 2) - p) - q)))))`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fn th => GEN_REWR_TAC I  [MATCH_MP REAL_EQ_LMUL2 th]) THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_DIV_LMUL th]) THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN (--`m:num`--) SUBST1_TAC)
  (SPEC (--`n:num`--) num_CASES) THENL
   [REWRITE_TAC[pow, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_SUB_REFL] THEN
    REWRITE_TAC[SUB_0, sum, REAL_MUL_RZERO], ALL_TAC] THEN
  REWRITE_TAC[POWDIFF, REAL_ADD_SUB] THEN
  ASM_REWRITE_TAC[GSYM REAL_SUB_LDISTRIB, REAL_EQ_LMUL] THEN
  REWRITE_TAC[SUC_SUB1] THEN
  GEN_REWR_TAC (RATOR_CONV o ONCE_DEPTH_CONV)  [POWREV] THEN
  REWRITE_TAC[sum] THEN REWRITE_TAC[ADD_CLAUSES] THEN BETA_TAC THEN
  REWRITE_TAC[SUB_EQUAL_0] THEN REWRITE_TAC[REAL, pow] THEN
  REWRITE_TAC[REAL_MUL_LID, REAL_MUL_RID, REAL_RDISTRIB] THEN
  REWRITE_TAC[REAL_ADD2_SUB2, REAL_SUB_REFL, REAL_ADD_RID] THEN
  REWRITE_TAC[SUM_NSUB] THEN BETA_TAC THEN
  REWRITE_TAC[TERMDIFF_LEMMA1] THEN
  ONCE_REWRITE_TAC[GSYM SUM_CMUL] THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_SUBST THEN X_GEN_TAC (--`p:num`--) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN BETA_TAC THEN
  GEN_REWR_TAC RAND_CONV  [REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:num`--) SUBST_ALL_TAC o MATCH_MP LESS_ADD_1) THEN
  REWRITE_TAC[GSYM ADD1] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[ADD_SUB] THEN REWRITE_TAC[POWDIFF, REAL_ADD_SUB] THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV)  [REAL_MUL_SYM] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC SUM_SUBST THEN X_GEN_TAC (--`q:num`--) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC(TOP_DEPTH_CONV num_CONV) THEN
  REWRITE_TAC[SUB_MONO_EQ, SUB_0, ADD_SUB]);

val TERMDIFF_LEMMA3 = store_thm("TERMDIFF_LEMMA3",
  (--`!z h n k'. ~(h = &0) /\ abs(z) <= k' /\ abs(z + h) <= k' ==>
    abs(((((z + h) pow n) - (z pow n)) / h) - (&n * (z pow (n - 1))))
        <= &n * (&(n - 1) * ((k' pow (n - 2)) * abs(h)))`--),
  let val tac = W(curry op THEN (MATCH_MP_TAC REAL_LE_TRANS) o
           EXISTS_TAC o rand o concl o PART_MATCH (rand o rator) ABS_SUM o
           rand o rator o snd)  THEN REWRITE_TAC[ABS_SUM] in
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP TERMDIFF_LEMMA2 th]) THEN
  REWRITE_TAC[ABS_MUL] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
  GEN_REWR_TAC RAND_CONV  [REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  FIRST_ASSUM(ASSUME_TAC o CONV_RULE(REWR_CONV ABS_NZ)) THEN
  FIRST_ASSUM(fn th => GEN_REWR_TAC I  [MATCH_MP REAL_LE_LMUL th]) THEN
  tac THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  GEN_REWR_TAC RAND_CONV  [REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC SUM_BOUND THEN X_GEN_TAC (--`p:num`--) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  BETA_TAC THEN REWRITE_TAC[ABS_MUL] THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN (--`r:num`--) SUBST_ALL_TAC)
  (SPEC (--`n:num`--) num_CASES) THENL
   [REWRITE_TAC[SUB_0, sum, ABS_0, REAL_MUL_RZERO, REAL_LE_REFL],
    ALL_TAC] THEN
  REWRITE_TAC[SUC_SUB1, TWO, SUB_MONO_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUC_SUB1]) THEN MP_TAC(ASSUME (--`p:num < r`--)) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:num`--) SUBST_ALL_TAC o MATCH_MP LESS_ADD_1) THEN
  REWRITE_TAC[GSYM ADD1] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[ADD_SUB] THEN REWRITE_TAC[ADD_CLAUSES, SUC_SUB1, ADD_SUB] THEN
  REWRITE_TAC[POW_ADD] THEN GEN_REWR_TAC RAND_CONV
   [AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
        (--`(a * b) * c = b * (c * a)`--)] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[ABS_POS] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM POW_ABS] THEN MATCH_MP_TAC POW_LE THEN
    ASM_REWRITE_TAC[ABS_POS], ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`&(SUC d) * (k' pow d)`--) THEN
  CONJ_TAC THENL
   [ALL_TAC, SUBGOAL_THEN (--`&0 <= k'`--) MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`abs z`--) THEN
      ASM_REWRITE_TAC[ABS_POS],
      DISCH_THEN(MP_TAC o SPEC (--`d:num`--) o MATCH_MP POW_POS) THEN
      DISCH_THEN(DISJ_CASES_THEN MP_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
       [DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP REAL_LE_RMUL th]) THEN
        REWRITE_TAC[REAL_LE, LESS_EQ_MONO] THEN
        MATCH_MP_TAC LESS_EQ_TRANS THEN EXISTS_TAC (--`SUC d`--) THEN
        REWRITE_TAC[LESS_EQ_MONO, LESS_EQ_ADD] THEN
        MATCH_MP_TAC LESS_IMP_LESS_OR_EQ THEN REWRITE_TAC[LESS_SUC_REFL],
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[REAL_MUL_RZERO, REAL_LE_REFL]]]] THEN
  tac THEN MATCH_MP_TAC SUM_BOUND THEN X_GEN_TAC (--`q:num`--) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN BETA_TAC THEN
  UNDISCH_TAC (--`q < SUC d`--) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`e:num`--) MP_TAC o MATCH_MP LESS_ADD_1) THEN
  REWRITE_TAC[GSYM ADD1, ADD_CLAUSES, INV_SUC_EQ] THEN
  DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[POW_ADD] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
  REWRITE_TAC[ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  REWRITE_TAC[ABS_POS, GSYM POW_ABS] THEN
  CONJ_TAC THEN MATCH_MP_TAC POW_LE THEN ASM_REWRITE_TAC[ABS_POS] end);

val TERMDIFF_LEMMA4 = store_thm("TERMDIFF_LEMMA4",
  (--`!f k' k. &0 < k /\
           (!h. &0 < abs(h) /\ abs(h) < k ==> abs(f h) <= k' * abs(h))
        ==> (f -> &0)(&0)`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[LIM, REAL_SUB_RZERO] THEN
  SUBGOAL_THEN (--`&0 <= k'`--) MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC (--`k / &2`--)) THEN
    MP_TAC(ONCE_REWRITE_RULE[GSYM REAL_LT_HALF1] (ASSUME (--`&0 < k`--))) THEN
    DISCH_THEN(fn th => ASSUME_TAC th THEN MP_TAC th) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
    DISCH_THEN(fn th => REWRITE_TAC[th, abs]) THEN
    REWRITE_TAC[GSYM abs] THEN
    ASM_REWRITE_TAC[REAL_LT_HALF1, REAL_LT_HALF2] THEN DISCH_TAC THEN
    MP_TAC(GEN_ALL(MATCH_MP REAL_LE_RMUL (ASSUME (--`&0 < k / &2`--)))) THEN
    DISCH_THEN(fn th => GEN_REWR_TAC I  [GSYM th]) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`abs(f(k / &2))`--) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO, ABS_POS], ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THEN
  X_GEN_TAC (--`e:real`--) THEN DISCH_TAC THENL
   [ALL_TAC, EXISTS_TAC (--`k:real`--) THEN REWRITE_TAC[ASSUME (--`&0 < k`--)] THEN
    GEN_TAC THEN DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
    DISCH_THEN(MP_TAC o C CONJ(SPEC (--`(f:real->real) x`--) ABS_POS)) THEN
    REWRITE_TAC[REAL_LE_ANTISYM] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM ACCEPT_TAC] THEN
  SUBGOAL_THEN (--`&0 < (e / k') / &2`--) ASSUME_TAC THENL
   [REWRITE_TAC[real_div] THEN
    REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_INV_POS) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_LT, TWO, LESS_0], ALL_TAC] THEN
  MP_TAC(SPECL [(--`(e / k') / &2`--), (--`k:real`--)] REAL_DOWN2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:real`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`d:real`--) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC (--`h:real`--) THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`k' * abs(h)`--) THEN CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (--`d:real`--) THEN
    ASM_REWRITE_TAC[],
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (--`k' * d`--) THEN
    ASM_REWRITE_TAC[MATCH_MP REAL_LT_LMUL (ASSUME (--`&0 < k'`--))] THEN
    ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LT_RDIV (ASSUME (--`&0 < k'`--)))] THEN
    REWRITE_TAC[real_div] THEN
    ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
      (--`(a * b) * c = (c * a) * b`--)] THEN
    ASSUME_TAC(GSYM(MATCH_MP REAL_LT_IMP_NE (ASSUME (--`&0 < k'`--)))) THEN
    REWRITE_TAC[MATCH_MP REAL_MUL_LINV (ASSUME (--`~(k' = &0)`--))] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (--`(e / k') / &2`--) THEN
    ASM_REWRITE_TAC[GSYM real_div] THEN REWRITE_TAC[REAL_LT_HALF2] THEN
    ONCE_REWRITE_TAC[GSYM REAL_LT_HALF1] THEN ASM_REWRITE_TAC[]]);

val TERMDIFF_LEMMA5 = store_thm("TERMDIFF_LEMMA5",
  (--`!f g k.
      &0 < k /\
      summable(f) /\
      (!h. &0 < abs(h) /\ abs(h) < k
           ==> !n. abs(g(h) n) <= (f(n) * abs(h)))
      ==> ((\h. suminf(g h)) -> &0)(&0)`--),
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o MATCH_MP SUMMABLE_SUM) MP_TAC) THEN
  ASSUME_TAC((GEN (--`h:real`--) o SPEC (--`abs(h)`--) o
    MATCH_MP SER_CMUL) (ASSUME (--`f sums (suminf f)`--))) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[REAL_MUL_SYM]) THEN
  FIRST_ASSUM(ASSUME_TAC o GEN (--`h:real`--) o
    MATCH_MP SUM_UNIQ o SPEC (--`h:real`--)) THEN DISCH_TAC THEN
  C SUBGOAL_THEN ASSUME_TAC (--`!h. &0 < abs(h) /\ abs(h) < k ==>
    abs(suminf(g h)) <= (suminf(f) * abs(h))`--) THENL
   [GEN_TAC THEN DISCH_THEN(fn th => ASSUME_TAC th THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN DISCH_TAC THEN
    SUBGOAL_THEN (--`summable(\n. f(n) * abs(h))`--) ASSUME_TAC THENL
     [MATCH_MP_TAC SUM_SUMMABLE THEN
      EXISTS_TAC (--`suminf(f) * abs(h)`--) THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
    SUBGOAL_THEN (--`summable(\n. abs(g(h:real)(n:num)))`--) ASSUME_TAC THENL
     [MATCH_MP_TAC SER_COMPAR THEN
      EXISTS_TAC (--`\n:num. f(n) * abs(h)`--) THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC (--`0:num`--) THEN X_GEN_TAC (--`n:num`--) THEN
      DISCH_THEN(K ALL_TAC) THEN BETA_TAC THEN
      REWRITE_TAC[ABS_ABS] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[], ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (--`suminf(\n. abs(g(h:real)(n:num)))`--) THEN CONJ_TAC THENL
     [MATCH_MP_TAC SER_ABS THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SER_LE THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    GEN_TAC THEN BETA_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  MATCH_MP_TAC TERMDIFF_LEMMA4 THEN
  MAP_EVERY EXISTS_TAC [(--`suminf(f)`--), (--`k:real`--)] THEN
  BETA_TAC THEN ASM_REWRITE_TAC[]);

val TERMDIFF = store_thm("TERMDIFF",
  (--`!c k' x.
      summable(\n. c(n) * (k' pow n)) /\
      summable(\n. (diffs c)(n) * (k' pow n)) /\
      summable(\n. (diffs(diffs c))(n) * (k' pow n)) /\
      abs(x) < abs(k')
      ==> ((\x. suminf (\n. c(n) * (x pow n)))
           diffl
           (suminf (\n. (diffs c)(n) * (x pow n)))) (x)`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[diffl] THEN BETA_TAC THEN
  MATCH_MP_TAC LIM_TRANSFORM THEN
  EXISTS_TAC
   (--`\h. suminf(\n. ((c(n) * ((x + h) pow n)) -
                       (c(n) * (x pow n))) / h)`--) THEN CONJ_TAC
  THENL
   [BETA_TAC THEN REWRITE_TAC[LIM] THEN BETA_TAC THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN X_GEN_TAC (--`e:real`--) THEN
    DISCH_TAC THEN EXISTS_TAC (--`abs(k') - abs(x)`--) THEN
    REWRITE_TAC[REAL_SUB_LT] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC (--`h:real`--) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP ABS_CIRCLE) THEN
    W(fn (asl,w) => SUBGOAL_THEN (mk_eq(rand(rator w),(--`&0`--))) SUBST1_TAC)
    THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[ABS_ZERO] THEN
    REWRITE_TAC[REAL_SUB_0] THEN C SUBGOAL_THEN MP_TAC
      (--`(\n. (c n) * (x pow n)) sums
           (suminf(\n. (c n) * (x pow n))) /\
       (\n. (c n) * ((x + h) pow n)) sums
           (suminf(\n. (c n) * ((x + h) pow n)))`--)
    THENL
      [CONJ_TAC THEN MATCH_MP_TAC SUMMABLE_SUM THEN
       MATCH_MP_TAC POWSER_INSIDE THEN EXISTS_TAC (--`k':real`--) THEN
       ASM_REWRITE_TAC[], ALL_TAC] THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SER_SUB) THEN BETA_TAC THEN
    DISCH_THEN(MP_TAC o SPEC (--`h:real`--) o MATCH_MP SER_CDIV) THEN
    BETA_TAC THEN DISCH_THEN(ACCEPT_TAC o MATCH_MP SUM_UNIQ), ALL_TAC]
  THEN
  ONCE_REWRITE_TAC[LIM_NULL] THEN BETA_TAC THEN
  MATCH_MP_TAC LIM_TRANSFORM THEN EXISTS_TAC
    (--`\h. suminf
             (\n. c(n) *
                  (((((x + h) pow n) - (x pow n)) / h)
                   - (&n * (x pow (n - 1)))))`--) THEN
  BETA_TAC THEN CONJ_TAC
  THENL
   [REWRITE_TAC[LIM] THEN X_GEN_TAC (--`e:real`--) THEN DISCH_TAC THEN
    EXISTS_TAC (--`abs(k') - abs(x)`--) THEN
    REWRITE_TAC[REAL_SUB_LT] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC (--`h:real`--) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP ABS_CIRCLE) THEN
    W(fn (asl,w) => SUBGOAL_THEN (mk_eq(rand(rator w),(--`&0`--))) SUBST1_TAC)
    THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_SUB_RZERO, ABS_ZERO] THEN
    BETA_TAC THEN REWRITE_TAC[REAL_SUB_0] THEN
    SUBGOAL_THEN (--`summable(\n. (diffs c)(n) * (x pow n))`--) MP_TAC
    THENL
     [MATCH_MP_TAC POWSER_INSIDE THEN EXISTS_TAC (--`k':real`--) THEN
      ASM_REWRITE_TAC[], ALL_TAC] THEN
    DISCH_THEN(fn th => ASSUME_TAC th THEN MP_TAC (MATCH_MP DIFFS_EQUIV th))
    THEN DISCH_THEN(fn th => SUBST1_TAC (MATCH_MP SUM_UNIQ th) THEN MP_TAC th)
    THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_SUB_RZERO]) THEN
    C SUBGOAL_THEN MP_TAC
      (--`(\n. (c n) * (x pow n)) sums
           (suminf(\n. (c n) * (x pow n))) /\
       (\n. (c n) * ((x + h) pow n)) sums
           (suminf(\n. (c n) * ((x + h) pow n)))`--)
    THENL
     [CONJ_TAC THEN MATCH_MP_TAC SUMMABLE_SUM THEN
      MATCH_MP_TAC POWSER_INSIDE THEN EXISTS_TAC (--`k':real`--) THEN
      ASM_REWRITE_TAC[], ALL_TAC] THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SER_SUB) THEN BETA_TAC THEN
    DISCH_THEN(MP_TAC o SPEC (--`h:real`--) o MATCH_MP SER_CDIV) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUMMABLE_SUM o MATCH_MP SUM_SUMMABLE) THEN
    BETA_TAC THEN DISCH_THEN(fn th => DISCH_THEN (MP_TAC o
      MATCH_MP SUMMABLE_SUM o MATCH_MP SUM_SUMMABLE) THEN MP_TAC th) THEN
    DISCH_THEN(fn th1 => DISCH_THEN(fn th2 => MP_TAC(CONJ th1 th2))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SER_SUB) THEN BETA_TAC THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP SUM_UNIQ) THEN AP_TERM_TAC THEN
    ABS_TAC THEN REWRITE_TAC[real_div] THEN
    REWRITE_TAC[REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN (* break *)
  MATCH_ACCEPT_TAC REAL_MUL_SYM,
    ALL_TAC] THEN
  MP_TAC(SPECL [(--`abs(x)`--), (--`abs(k')`--)] REAL_MEAN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`R:real`--) STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL
   [--`\n. abs(c n) * (&n * (&(n - 1) * (R pow (n - 2))))`--,
    --`\h n. c(n) * (((((x + h) pow n) - (x pow n)) / h)
                            -
                            (&n * (x pow (n - 1))))`--,
    --`R - abs(x)`--] TERMDIFF_LEMMA5) THEN
  BETA_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC
  THENL
   [ASM_REWRITE_TAC[REAL_SUB_LT],
    SUBGOAL_THEN (--`summable(\n. abs(diffs(diffs c) n) * (R pow n))`--)
                 MP_TAC
    THENL
     [MATCH_MP_TAC POWSER_INSIDEA THEN
      EXISTS_TAC (--`k':real`--) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN (--`abs(R) = R`--) (fn th => ASM_REWRITE_TAC[th]) THEN
      REWRITE_TAC[ABS_REFL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (--`abs(x)`--) THEN REWRITE_TAC[ABS_POS] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
    REWRITE_TAC[diffs] THEN BETA_TAC THEN REWRITE_TAC[ABS_MUL] THEN
    REWRITE_TAC[ABS_N] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    C SUBGOAL_THEN (fn th => ONCE_REWRITE_TAC[GSYM th])
      (--`!n. diffs(diffs (\n. abs(c n))) n * (R pow n) =
           &(SUC n) * (&(SUC(SUC n)) * (abs(c(SUC(SUC n)))
           * (R pow n)))`--)
    THENL
     [GEN_TAC THEN REWRITE_TAC[diffs] THEN BETA_TAC THEN
      REWRITE_TAC[REAL_MUL_ASSOC], ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFFS_EQUIV) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
    REWRITE_TAC[diffs] THEN BETA_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    SUBGOAL_THEN (--`(\n. &n * (&(SUC n) * (abs(c(SUC n))
                          * (R pow (n - 1))))) =
         \n. diffs(\m. &(m - 1) * (abs(c m) / R)) n * (R pow n)`--)
    SUBST1_TAC
    THENL
     [REWRITE_TAC[diffs] THEN BETA_TAC THEN REWRITE_TAC[SUC_SUB1] THEN
      ABS_TAC THEN
      DISJ_CASES_THEN2 (SUBST1_TAC) (X_CHOOSE_THEN (--`m:num`--) SUBST1_TAC)
       (SPEC (--`n:num`--) num_CASES) THEN
      REWRITE_TAC[REAL_MUL_LZERO, REAL_MUL_RZERO, SUC_SUB1] THEN
      REWRITE_TAC[ADD1, POW_ADD] THEN REWRITE_TAC[GSYM ADD1, POW_1] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC, real_div] THEN
      ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
        (--`a * (b * (c * (d * (e * f)))) =
            b * (a * (c * (e * (d * f))))`--)] THEN
      REPEAT AP_TERM_TAC THEN SUBGOAL_THEN (--`inv(R) * R = &1`--)
                                           SUBST1_TAC
      THENL
       [MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC[ABS_NZ] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`abs(x)`--) THEN
        ASM_REWRITE_TAC[ABS_POS] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
        EXISTS_TAC (--`R:real`--) THEN ASM_REWRITE_TAC[ABS_LE],
        REWRITE_TAC[REAL_MUL_RID]], ALL_TAC]
    THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFFS_EQUIV) THEN BETA_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
    MATCH_MP_TAC (TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN AP_TERM_TAC THEN
    CONV_TAC(X_FUN_EQ_CONV (--`n:num`--)) THEN BETA_TAC THEN GEN_TAC THEN
    REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN
    GEN_REWR_TAC RAND_CONV
     [AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
      (--`a * (b * (c * d)) =  b * (c * (a * d))`--)] THEN
    DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN (--`m:num`--) SUBST1_TAC)
     (SPEC (--`n:num`--) num_CASES) THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
    REWRITE_TAC[TWO, SUC_SUB1, SUB_MONO_EQ] THEN
    AP_TERM_TAC THEN
    DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN (--`n:num`--) SUBST1_TAC)
     (SPEC (--`m:num`--) num_CASES) THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
    REPEAT AP_TERM_TAC THEN REWRITE_TAC[SUC_SUB1] THEN
    REWRITE_TAC[ADD1, POW_ADD, POW_1] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    SUBGOAL_THEN (--`R * inv(R) = &1`--)
                 (fn th => REWRITE_TAC[th, REAL_MUL_RID]) THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (--`abs(x)`--) THEN ASM_REWRITE_TAC[ABS_POS],

    X_GEN_TAC (--`h:real`--) THEN DISCH_TAC THEN X_GEN_TAC (--`n:num`--) THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC[ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_LMUL_IMP THEN REWRITE_TAC[ABS_POS] THEN
    MATCH_MP_TAC TERMDIFF_LEMMA3 THEN ASM_REWRITE_TAC[ABS_NZ] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (--`abs(x) + abs(h)`--) THEN
      REWRITE_TAC[ABS_TRIANGLE] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
      ASM_REWRITE_TAC[GSYM REAL_LT_SUB_LADD]]]);

val _ = export_theory();

end;
