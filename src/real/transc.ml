(* ======================================================================== *)
(* Properties of power series.                                              *)
(* ======================================================================== *)

(* ------------------------------------------------------------------------ *)
(* More theorems about rearranging finite sums                              *)
(* ------------------------------------------------------------------------ *)

let POWDIFF_LEMMA = prove(
  `!n x y. Sum(0,SUC n)(\p. (x pow p) * y pow ((SUC n) - p)) =
                y * Sum(0,SUC n)(\p. (x pow p) * (y pow (n - p)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_CMUL] THEN
  MATCH_MP_TAC SUM_SUBST THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  BETA_TAC THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `~(n < p:num)` ASSUME_TAC THENL
   [POP_ASSUM(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[ADD_CLAUSES] THEN
    REWRITE_TAC[NOT_LT; CONJUNCT2 LT] THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THEN
    REWRITE_TAC[LE_REFL; LT_IMP_LE];
    ASM_REWRITE_TAC[SUB_OLD] THEN REWRITE_TAC[pow] THEN
    MATCH_ACCEPT_TAC REAL_MUL_SYM]);;

let POWDIFF = prove(
  `!n x y. (x pow (SUC n)) - (y pow (SUC n)) =
                (x - y) * Sum(0,SUC n)(\p. (x pow p) * (y pow (n - p)))`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[Sum] THEN
    REWRITE_TAC[REAL_ADD_LID; ADD_CLAUSES; SUB_0] THEN
    BETA_TAC THEN REWRITE_TAC[pow] THEN
    REWRITE_TAC[REAL_MUL_RID];
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[Sum] THEN
    REWRITE_TAC[ADD_CLAUSES] THEN BETA_TAC THEN
    REWRITE_TAC[POWDIFF_LEMMA] THEN REWRITE_TAC[REAL_LDISTRIB] THEN
    ONCE_REWRITE_TAC[AC REAL_MUL_AC
      `a * (b * c) = b * (a * c)`] THEN
    POP_ASSUM(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[SUB_REFL] THEN
    SPEC_TAC(`SUC n`,`n:num`) THEN GEN_TAC THEN
    REWRITE_TAC[pow; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_LDISTRIB; REAL_SUB_LDISTRIB] THEN
    REWRITE_TAC[real_sub] THEN
    ONCE_REWRITE_TAC[AC REAL_ADD_AC
      `(a + b) + (c + d) = (d + a) + (c + b)`] THEN
    GEN_REWRITE_TAC (funpow 2 LAND_CONV) [REAL_MUL_SYM] THEN
    CONV_TAC SYM_CONV THEN REWRITE_TAC[REAL_ADD_LID_UNIQ] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_ADD_LINV]]);;

let POWREV = prove(
  `!n x y. Sum(0,SUC n)(\p. (x pow p) * (y pow (n - p))) =
                Sum(0,SUC n)(\p. (x pow (n - p)) * (y pow p))`,
  let REAL_EQ_LMUL2' = CONV_RULE(REDEPTH_CONV FORALL_IMP_CONV) REAL_EQ_LMUL2 in
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x:real = y` THENL
   [ASM_REWRITE_TAC[GSYM POW_ADD] THEN
    MATCH_MP_TAC SUM_SUBST THEN X_GEN_TAC `p:num` THEN
    BETA_TAC THEN DISCH_TAC THEN AP_TERM_TAC THEN
    MATCH_ACCEPT_TAC ADD_SYM;
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM REAL_SUB_0]) THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [MATCH_MP REAL_EQ_LMUL2' th]) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_NEGNEG] THEN
    ONCE_REWRITE_TAC[REAL_NEG_LMUL] THEN
    ONCE_REWRITE_TAC[REAL_NEG_SUB] THEN
    REWRITE_TAC[GSYM POWDIFF] THEN REWRITE_TAC[REAL_NEG_SUB]]);;

(* ------------------------------------------------------------------------ *)
(* Show (essentially) that a power series has a `circle` of convergence,    *)
(* i.e. if it sums for x, then it sums absolutely for z with |z| < |x|.     *)
(* ------------------------------------------------------------------------ *)

let POWSER_INSIDEA = prove(
  `!f x z. summable (\n. f(n) * (x pow n)) /\ abs(z) < abs(x)
        ==> summable (\n. abs(f(n)) * (z pow n))`,
  let th = (GEN_ALL o CONV_RULE LEFT_IMP_EXISTS_CONV o snd o
              EQ_IMP_RULE o SPEC_ALL) convergent in
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_ZERO) THEN
  DISCH_THEN(MP_TAC o MATCH_MP th) THEN REWRITE_TAC[GSYM SEQ_CAUCHY] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SEQ_CBOUNDED) THEN
  REWRITE_TAC[SEQ_BOUNDED] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC `K:real`) THEN MATCH_MP_TAC SER_COMPAR THEN
  EXISTS_TAC `\n. (K * abs(z pow n)) / abs(x pow n)` THEN CONJ_TAC THENL
   [EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
    BETA_TAC THEN MATCH_MP_TAC REAL_LE_RDIV THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM ABS_NZ] THEN MATCH_MP_TAC POW_NZ THEN
      REWRITE_TAC[ABS_NZ] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `abs(z)` THEN ASM_REWRITE_TAC[ABS_POS];
      REWRITE_TAC[ABS_MUL; ABS_ABS; GSYM REAL_MUL_ASSOC] THEN
      ONCE_REWRITE_TAC[AC REAL_MUL_AC
       `a * b * c = (a * c) * b`] THEN
      DISJ_CASES_TAC(SPEC `z pow n` ABS_CASES) THEN
      ASM_REWRITE_TAC[ABS_0; REAL_MUL_RZERO; REAL_LE_REFL] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_LE_RMUL_EQ th]) THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[GSYM ABS_MUL]];
    REWRITE_TAC[summable] THEN
    EXISTS_TAC `K * inv(&1 - (abs(z) / abs(x)))` THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SER_CMUL THEN
    GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [GSYM real_div] THEN
    SUBGOAL_THEN `!n. abs(z pow n) / abs(x pow n) =
                        (abs(z) / abs(x)) pow n`
    (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [ALL_TAC; REWRITE_TAC[GSYM real_div] THEN
      MATCH_MP_TAC GP THEN REWRITE_TAC[real_div; ABS_MUL] THEN
      SUBGOAL_THEN `~(abs(x) = &0)` (SUBST1_TAC o MATCH_MP ABS_INV) THENL
       [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `abs(z) < &0` THEN
        REWRITE_TAC[REAL_NOT_LT; ABS_POS];
        REWRITE_TAC[ABS_ABS; GSYM real_div] THEN
        MATCH_MP_TAC REAL_LT_1 THEN ASM_REWRITE_TAC[ABS_POS]]] THEN
    REWRITE_TAC[GSYM POW_ABS] THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[real_div; POW_MUL] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC POW_INV THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs(z)` THEN
    ASM_REWRITE_TAC[ABS_POS]]);;

(* ------------------------------------------------------------------------ *)
(* Weaker but more commonly useful form for non-absolute convergence        *)
(* ------------------------------------------------------------------------ *)

let POWSER_INSIDE = prove(
  `!f x z. summable (\n. f(n) * (x pow n)) /\ abs(z) < abs(x)
        ==> summable (\n. f(n) * (z pow n))`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPEC `z:real` ABS_ABS)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP POWSER_INSIDEA) THEN
  REWRITE_TAC[POW_ABS; GSYM ABS_MUL] THEN
  DISCH_THEN(prefix THEN (MATCH_MP_TAC SER_ACONV) o MP_TAC) THEN
  BETA_TAC THEN DISCH_THEN ACCEPT_TAC);;

(* ------------------------------------------------------------------------ *)
(* Define formal differentiation of power series                            *)
(* ------------------------------------------------------------------------ *)

let diffs = new_definition
  `diffs c = (\n. &(SUC n) * c(SUC n))`;;

(* ------------------------------------------------------------------------ *)
(* Lemma about distributing negation over it                                *)
(* ------------------------------------------------------------------------ *)

let DIFFS_NEG = prove(
  `!c. diffs(\n. --(c n)) = \n. --((diffs c) n)`,
  GEN_TAC THEN REWRITE_TAC[diffs] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_NEG_RMUL]);;

(* ------------------------------------------------------------------------ *)
(* Show that we can shift the terms down one                                *)
(* ------------------------------------------------------------------------ *)

let DIFFS_LEMMA = prove(
  `!n c x. Sum(0,n) (\n. (diffs c)(n) * (x pow n)) =
           Sum(0,n) (\n. &n * c(n) * (x pow (n - 1))) +
             (&n * c(n) * x pow (n - 1))`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[Sum; REAL_MUL_LZERO; REAL_ADD_LID] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN
  AP_TERM_TAC THEN BETA_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
  AP_TERM_TAC THEN REWRITE_TAC[diffs] THEN BETA_TAC THEN
  REWRITE_TAC[SUC_SUB1; REAL_MUL_ASSOC]);;

let DIFFS_LEMMA2 = prove(
  `!n c x. Sum(0,n) (\n. &n * c(n) * (x pow (n - 1))) =
           Sum(0,n) (\n. (diffs c)(n) * (x pow n)) -
                (&n * c(n) * x pow (n - 1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_EQ_SUB_LADD; DIFFS_LEMMA]);;

let DIFFS_EQUIV = prove(
  `!c x. summable(\n. (diffs c)(n) * (x pow n)) ==>
      (\n. &n * c(n) * (x pow (n - 1))) sums
         (suminf(\n. (diffs c)(n) * (x pow n)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[diffs] o MATCH_MP SER_ZERO) THEN
  BETA_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\n. &n * c(n) * (x pow (n - 1))) tends_num_real &0`
  MP_TAC THENL
   [ONCE_REWRITE_TAC[SEQ_SUC] THEN BETA_TAC THEN
    ASM_REWRITE_TAC[SUC_SUB1]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJ (MATCH_MP SUMMABLE_SUM
   (ASSUME `summable(\n. (diffs c)(n) * (x pow n))`))) THEN
  REWRITE_TAC[sums] THEN DISCH_THEN(MP_TAC o MATCH_MP SEQ_SUB) THEN
  BETA_TAC THEN REWRITE_TAC[GSYM DIFFS_LEMMA2] THEN
  REWRITE_TAC[REAL_SUB_RZERO]);;

(* ======================================================================== *)
(* Show term-by-term differentiability of power series                      *)
(* (NB we hypothesize convergence of first two derivatives; we could prove  *)
(*  they all have the same radius of convergence, but we don't need to.)    *)
(* ======================================================================== *)

let TERMDIFF_LEMMA1 = prove(
  `!m z h.
     Sum(0,m)(\p. (((z + h) pow (m - p)) * (z pow p)) - (z pow m)) =
       Sum(0,m)(\p. (z pow p) *
       (((z + h) pow (m - p)) - (z pow (m - p))))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_SUBST THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; GSYM POW_ADD] THEN BINOP_TAC THENL
   [MATCH_ACCEPT_TAC REAL_MUL_SYM;
    AP_TERM_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUB_ADD THEN
    MATCH_MP_TAC LT_IMP_LE THEN
    POP_ASSUM(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[ADD_CLAUSES]]);;

let TERMDIFF_LEMMA2 = prove(
  `!z h. ~(h = &0) ==>
       (((((z + h) pow n) - (z pow n)) / h) - (&n * (z pow (n - 1))) =
        h * Sum(0,n - 1)(\p. (z pow p) *
              Sum(0,(n - 1) - p)
                (\q. ((z + h) pow q) *
                       (z pow (((n - 2) - p) - q)))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [MATCH_MP REAL_EQ_LMUL2 th]) THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_DIV_LMUL th]) THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `m:num` SUBST1_TAC)
  (SPEC `n:num` num_CASES) THENL
   [REWRITE_TAC[pow; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_SUB_REFL] THEN
    REWRITE_TAC[SUB_0; Sum; REAL_MUL_RZERO]; ALL_TAC] THEN
  REWRITE_TAC[POWDIFF; REAL_ADD_SUB] THEN
  ASM_REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_EQ_LMUL] THEN
  REWRITE_TAC[SUC_SUB1] THEN
  GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [POWREV] THEN
  REWRITE_TAC[Sum] THEN REWRITE_TAC[ADD_CLAUSES] THEN BETA_TAC THEN
  REWRITE_TAC[SUB_REFL] THEN REWRITE_TAC[REAL; pow] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RID; REAL_RDISTRIB] THEN
  REWRITE_TAC[REAL_ADD2_SUB2; REAL_SUB_REFL; REAL_ADD_RID] THEN
  REWRITE_TAC[SUM_NSUB] THEN BETA_TAC THEN
  REWRITE_TAC[TERMDIFF_LEMMA1] THEN
  ONCE_REWRITE_TAC[GSYM SUM_CMUL] THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_SUBST THEN X_GEN_TAC `p:num` THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN BETA_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC o MATCH_MP LESS_ADD_1) THEN
  REWRITE_TAC[GSYM ADD1] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[ADD_SUB] THEN REWRITE_TAC[POWDIFF; REAL_ADD_SUB] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC SUM_SUBST THEN X_GEN_TAC `q:num` THEN
  REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC(TOP_DEPTH_CONV num_CONV) THEN
  REWRITE_TAC[SUB_SUC; SUB_0; ADD_SUB]);;

let TERMDIFF_LEMMA3 = prove(
  `!z h n K. ~(h = &0) /\ abs(z) <= K /\ abs(z + h) <= K ==>
    abs(((((z + h) pow n) - (z pow n)) / h) - (&n * (z pow (n - 1))))
        <= &n * &(n - 1) * (K pow (n - 2)) * abs(h)`,
  let tac = W(prefix THEN (MATCH_MP_TAC REAL_LE_TRANS) o
           EXISTS_TAC o rand o concl o PART_MATCH (rand o rator) ABS_SUM o
           rand o rator o snd)  THEN REWRITE_TAC[ABS_SUM] in
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP TERMDIFF_LEMMA2 th]) THEN
  REWRITE_TAC[ABS_MUL] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  FIRST_ASSUM(ASSUME_TAC o CONV_RULE(REWR_CONV ABS_NZ)) THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [MATCH_MP REAL_LE_LMUL_LOCAL th]) THEN
  tac THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC SUM_BOUND THEN X_GEN_TAC `p:num` THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  BETA_TAC THEN REWRITE_TAC[ABS_MUL] THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `r:num` SUBST_ALL_TAC)
  (SPEC `n:num` num_CASES) THENL
   [REWRITE_TAC[SUB_0; Sum; ABS_0; REAL_MUL_RZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[SUC_SUB1; num_CONV `2`; SUB_SUC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUC_SUB1]) THEN
  SUBGOAL_THEN `p < r:num` MP_TAC THENL
   [FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC o MATCH_MP LESS_ADD_1) THEN
  REWRITE_TAC[GSYM ADD1] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[ADD_SUB] THEN REWRITE_TAC[ADD_CLAUSES; SUC_SUB1; ADD_SUB] THEN
  REWRITE_TAC[POW_ADD] THEN GEN_REWRITE_TAC RAND_CONV
   [AC REAL_MUL_AC
        `(a * b) * c = b * (c * a)`] THEN
  MATCH_MP_TAC REAL_LE_MUL2V THEN REWRITE_TAC[ABS_POS] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM POW_ABS] THEN MATCH_MP_TAC POW_LE THEN
    ASM_REWRITE_TAC[ABS_POS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(SUC d) * (K pow d)` THEN
  CONJ_TAC THENL
   [ALL_TAC; SUBGOAL_THEN `&0 <= K` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs z` THEN
      ASM_REWRITE_TAC[ABS_POS];
      DISCH_THEN(MP_TAC o SPEC `d:num` o MATCH_MP POW_POS) THEN
      DISCH_THEN(DISJ_CASES_THEN MP_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
       [DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP REAL_LE_RMUL_EQ th]) THEN
        REWRITE_TAC[REAL_LE; LE_SUC] THEN
        MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `SUC d` THEN
        REWRITE_TAC[LE_SUC; LE_ADD] THEN
        MATCH_MP_TAC LT_IMP_LE THEN REWRITE_TAC[LESS_SUC_REFL];
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL]]]] THEN
  tac THEN MATCH_MP_TAC SUM_BOUND THEN X_GEN_TAC `q:num` THEN
  REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN BETA_TAC THEN
  UNDISCH_TAC `q < (SUC d)` THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num` MP_TAC o MATCH_MP LESS_ADD_1) THEN
  REWRITE_TAC[GSYM ADD1; ADD_CLAUSES; EQ_SUC] THEN
  DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[POW_ADD] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
  REWRITE_TAC[ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2V THEN
  REWRITE_TAC[ABS_POS; GSYM POW_ABS] THEN
  CONJ_TAC THEN MATCH_MP_TAC POW_LE THEN ASM_REWRITE_TAC[ABS_POS]);;

let TERMDIFF_LEMMA4 = prove(
  `!f K k. &0 < k /\
           (!h. &0 < abs(h) /\ abs(h) < k ==> abs(f h) <= K * abs(h))
        ==> (f tends_real_real &0)(&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[LIM; REAL_SUB_RZERO] THEN
  SUBGOAL_THEN `&0 <= K` MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `k / &2`) THEN
    MP_TAC(ONCE_REWRITE_RULE[GSYM REAL_LT_HALF1] (ASSUME `&0 < k`)) THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; real_abs]) THEN
    REWRITE_TAC[GSYM real_abs] THEN
    ASM_REWRITE_TAC[REAL_LT_HALF1; REAL_LT_HALF2] THEN DISCH_TAC THEN
    MP_TAC(GEN_ALL(MATCH_MP REAL_LE_RMUL_EQ (ASSUME `&0 < k / &2`))) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC I [GSYM th]) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(f(k / &2))` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; ABS_POS]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THENL
   [ALL_TAC; EXISTS_TAC `k:real` THEN REWRITE_TAC[ASSUME `&0 < k`] THEN
    GEN_TAC THEN DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
    DISCH_THEN(MP_TAC o C CONJ(SPEC `(f:real->real) x` ABS_POS)) THEN
    REWRITE_TAC[REAL_LE_ANTISYM] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM ACCEPT_TAC] THEN
  SUBGOAL_THEN `&0 < (e / K) / &2` ASSUME_TAC THENL
   [REWRITE_TAC[real_div] THEN
    REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_INV_POS) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_LT; num_CONV `2`; LT_0]; ALL_TAC] THEN
  MP_TAC(SPECL [`(e / K) / &2`; `k:real`] REAL_DOWN2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `h:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `K * abs(h)` THEN CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `K * d` THEN
    ASM_REWRITE_TAC[MATCH_MP REAL_LT_LMUL_EQ (ASSUME `&0 < K`)] THEN
    ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LT_RDIV (ASSUME `&0 < K`))] THEN
    REWRITE_TAC[real_div] THEN
    ONCE_REWRITE_TAC[AC REAL_MUL_AC
      `(a * b) * c = (c * a) * b`] THEN
    ASSUME_TAC(GSYM(MATCH_MP REAL_LT_IMP_NE (ASSUME `&0 < K`))) THEN
    REWRITE_TAC[MATCH_MP REAL_MUL_LINV (ASSUME `~(K = &0)`)] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `(e / K) / &2` THEN
    ASM_REWRITE_TAC[GSYM real_div] THEN REWRITE_TAC[REAL_LT_HALF2] THEN
    ONCE_REWRITE_TAC[GSYM REAL_LT_HALF1] THEN ASM_REWRITE_TAC[]]);;

let TERMDIFF_LEMMA5 = prove(
  `!f g k. &0 < k /\
         summable(f) /\
         (!h. &0 < abs(h) /\ abs(h) < k ==> !n. abs(g(h) n) <= (f(n) * abs(h)))
             ==> ((\h. suminf(g h)) tends_real_real &0)(&0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o MATCH_MP SUMMABLE_SUM) MP_TAC) THEN
  ASSUME_TAC((GEN `h:real` o SPEC `abs(h)` o
    MATCH_MP SER_CMUL) (ASSUME `f sums (suminf f)`)) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[REAL_MUL_SYM]) THEN
  FIRST_ASSUM(ASSUME_TAC o GEN `h:real` o
    MATCH_MP SUM_UNIQ o SPEC `h:real`) THEN DISCH_TAC THEN
  C SUBGOAL_THEN ASSUME_TAC `!h. &0 < abs(h) /\ abs(h) < k ==>
    abs(suminf(g h)) <= (suminf(f) * abs(h))` THENL
   [GEN_TAC THEN DISCH_THEN(fun th -> ASSUME_TAC th THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN DISCH_TAC THEN
    SUBGOAL_THEN `summable(\n. f(n) * abs(h))` ASSUME_TAC THENL
     [MATCH_MP_TAC SUM_SUMMABLE THEN
      EXISTS_TAC `suminf(f) * abs(h)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `summable(\n. abs(g(h:real)(n:num)))` ASSUME_TAC THENL
     [MATCH_MP_TAC SER_COMPAR THEN
      EXISTS_TAC `\n:num. f(n) * abs(h)` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN
      DISCH_THEN(K ALL_TAC) THEN BETA_TAC THEN
      REWRITE_TAC[ABS_ABS] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `suminf(\n. abs(g(h:real)(n:num)))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SER_ABS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SER_LE THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    GEN_TAC THEN BETA_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC TERMDIFF_LEMMA4 THEN
  MAP_EVERY EXISTS_TAC [`suminf(f)`; `k:real`] THEN
  BETA_TAC THEN ASM_REWRITE_TAC[]);;

let TERMDIFF = prove(
  `!c K. summable(\n. c(n) * (K pow n)) /\
         summable(\n. (diffs c)(n) * (K pow n)) /\
         summable(\n. (diffs(diffs c))(n) * (K pow n)) /\
         abs(x) < abs(K)
        ==> ((\x. suminf (\n. c(n) * (x pow n))) diffl
             (suminf (\n. (diffs c)(n) * (x pow n))))(x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[diffl] THEN BETA_TAC THEN
  MATCH_MP_TAC LIM_TRANSFORM THEN
  EXISTS_TAC `\h. suminf(\n. ((c(n) * ((x + h) pow n)) -
                             (c(n) * (x pow n))) / h)` THEN CONJ_TAC THENL
   [BETA_TAC THEN REWRITE_TAC[LIM] THEN BETA_TAC THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    EXISTS_TAC `abs(K) - abs(x)` THEN REWRITE_TAC[REAL_SUB_LT] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `h:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP ABS_CIRCLE) THEN
    W(fun (asl,w) -> SUBGOAL_THEN (mk_eq(rand(rator w),`&0`)) SUBST1_TAC) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[ABS_ZERO] THEN
    REWRITE_TAC[REAL_SUB_0] THEN C SUBGOAL_THEN MP_TAC
      `(\n. (c n) * (x pow n)) sums
           (suminf(\n. (c n) * (x pow n))) /\
       (\n. (c n) * ((x + h) pow n)) sums
           (suminf(\n. (c n) * ((x + h) pow n)))` THENL
     [CONJ_TAC THEN MATCH_MP_TAC SUMMABLE_SUM THEN
      MATCH_MP_TAC POWSER_INSIDE THEN EXISTS_TAC `K:real` THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SER_SUB) THEN BETA_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `h:real` o MATCH_MP SER_CDIV) THEN
    BETA_TAC THEN DISCH_THEN(ACCEPT_TAC o MATCH_MP SUM_UNIQ); ALL_TAC] THEN
  ONCE_REWRITE_TAC[LIM_NULL] THEN BETA_TAC THEN
  MATCH_MP_TAC LIM_TRANSFORM THEN EXISTS_TAC
   `\h. suminf (\n. c(n) *
    (((((x + h) pow n) - (x pow n)) / h) - (&n * (x pow (n - 1)))))` THEN
  BETA_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[LIM] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    EXISTS_TAC `abs(K) - abs(x)` THEN REWRITE_TAC[REAL_SUB_LT] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `h:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP ABS_CIRCLE) THEN
    W(fun (asl,w) -> SUBGOAL_THEN (mk_eq(rand(rator w),`&0`)) SUBST1_TAC) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_SUB_RZERO; ABS_ZERO] THEN
    BETA_TAC THEN REWRITE_TAC[REAL_SUB_0] THEN
    SUBGOAL_THEN `summable(\n. (diffs c)(n) * (x pow n))` MP_TAC THENL
     [MATCH_MP_TAC POWSER_INSIDE THEN EXISTS_TAC `K:real` THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN
        MP_TAC (MATCH_MP DIFFS_EQUIV th)) THEN
    DISCH_THEN(fun th -> SUBST1_TAC (MATCH_MP SUM_UNIQ th) THEN MP_TAC th) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_SUB_RZERO]) THEN C SUBGOAL_THEN MP_TAC
      `(\n. (c n) * (x pow n)) sums
           (suminf(\n. (c n) * (x pow n))) /\
       (\n. (c n) * ((x + h) pow n)) sums
           (suminf(\n. (c n) * ((x + h) pow n)))` THENL
     [CONJ_TAC THEN MATCH_MP_TAC SUMMABLE_SUM THEN
      MATCH_MP_TAC POWSER_INSIDE THEN EXISTS_TAC `K:real` THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SER_SUB) THEN BETA_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `h:real` o MATCH_MP SER_CDIV) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUMMABLE_SUM o MATCH_MP SUM_SUMMABLE) THEN
    BETA_TAC THEN DISCH_THEN(fun th -> DISCH_THEN (MP_TAC o
      MATCH_MP SUMMABLE_SUM o MATCH_MP SUM_SUMMABLE) THEN MP_TAC th) THEN
    DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 -> MP_TAC(CONJ th1 th2))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SER_SUB) THEN BETA_TAC THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP SUM_UNIQ) THEN AP_TERM_TAC THEN
    ABS_TAC THEN REWRITE_TAC[real_div] THEN
    REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_SUB_RDISTRIB] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_MUL_SYM;
    ALL_TAC] THEN
  MP_TAC(SPECL [`abs(x)`; `abs(K)`] REAL_MEAN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL
   [`\n. abs(c n) * &n * &(n - 1) * (R pow (n - 2))`;
    `\h n. c(n) * (((((x + h) pow n) - (x pow n)) / h) -
                     (&n * (x pow (n - 1))))`;
    `R - abs(x)`] TERMDIFF_LEMMA5) THEN
  BETA_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_LT];

    SUBGOAL_THEN `summable(\n. abs(diffs(diffs c) n) * (R pow n))` MP_TAC THENL
     [MATCH_MP_TAC POWSER_INSIDEA THEN
      EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `abs(R) = R` (fun th -> ASM_REWRITE_TAC[th]) THEN
      REWRITE_TAC[ABS_REFL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `abs(x)` THEN REWRITE_TAC[ABS_POS] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[diffs] THEN BETA_TAC THEN REWRITE_TAC[ABS_MUL] THEN
    REWRITE_TAC[ABS_N] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    C SUBGOAL_THEN (fun th -> ONCE_REWRITE_TAC[GSYM th])
      `!n. diffs(diffs (\n. abs(c n))) n * (R pow n) =
           &(SUC n) * &(SUC(SUC n)) * abs(c(SUC(SUC n))) * (R pow n)` THENL
     [GEN_TAC THEN REWRITE_TAC[diffs] THEN BETA_TAC THEN
      REWRITE_TAC[REAL_MUL_ASSOC]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFFS_EQUIV) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
    REWRITE_TAC[diffs] THEN BETA_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    SUBGOAL_THEN `(\n. &n * &(SUC n) * abs(c(SUC n)) * (R pow (n - 1))) =
           \n. diffs(\m. &(m - 1) * abs(c m) / R) n * (R pow n)`
    SUBST1_TAC THENL
     [REWRITE_TAC[diffs] THEN BETA_TAC THEN REWRITE_TAC[SUC_SUB1] THEN
      ABS_TAC THEN
      DISJ_CASES_THEN2 (SUBST1_TAC) (X_CHOOSE_THEN `m:num` SUBST1_TAC)
       (SPEC `n:num` num_CASES) THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; SUC_SUB1] THEN
      REWRITE_TAC[ADD1; POW_ADD] THEN REWRITE_TAC[GSYM ADD1; POW_1] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC; real_div] THEN
      ONCE_REWRITE_TAC[AC REAL_MUL_AC
        `a * b * c * d * e * f = b * a * c * e * d * f`] THEN
      REPEAT AP_TERM_TAC THEN SUBGOAL_THEN `inv(R) * R = &1` SUBST1_TAC THENL
       [MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC[ABS_NZ] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs(x)` THEN
        ASM_REWRITE_TAC[ABS_POS] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
        EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[ABS_LE];
        REWRITE_TAC[REAL_MUL_RID]]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFFS_EQUIV) THEN BETA_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
    MATCH_MP_TAC (TAUT `(a = b) ==> a ==> b`) THEN AP_TERM_TAC THEN
    CONV_TAC(X_FUN_EQ_CONV `n:num`) THEN BETA_TAC THEN GEN_TAC THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV
     [AC REAL_MUL_AC
      `a * b * c * d = b * c * a * d`] THEN
    DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `m:num` SUBST1_TAC)
     (SPEC `n:num` num_CASES) THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
    REWRITE_TAC[num_CONV `2`; SUC_SUB1; SUB_SUC] THEN AP_TERM_TAC THEN
    DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `n:num` SUBST1_TAC)
     (SPEC `m:num` num_CASES) THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
    REPEAT AP_TERM_TAC THEN REWRITE_TAC[SUC_SUB1] THEN
    REWRITE_TAC[ADD1; POW_ADD; POW_1] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    SUBGOAL_THEN `R * inv(R) = &1`
    (fun th -> REWRITE_TAC[th; REAL_MUL_RID]) THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `abs(x)` THEN ASM_REWRITE_TAC[ABS_POS];

    X_GEN_TAC `h:real` THEN DISCH_TAC THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC[ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_LMUL_IMP THEN REWRITE_TAC[ABS_POS] THEN
    MATCH_MP_TAC TERMDIFF_LEMMA3 THEN ASM_REWRITE_TAC[ABS_NZ] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(x) + abs(h)` THEN
      REWRITE_TAC[ABS_TRIANGLE] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
      ASM_REWRITE_TAC[GSYM REAL_LT_SUB_LADD]]]);;

(* ======================================================================== *)
(* Definitions of the transcendental functions etc.                         *)
(* ======================================================================== *)


prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* To avoid all those beta redexes vanishing without trace...                *)
(* ------------------------------------------------------------------------- *)

set_basic_rewrites (subtract (basic_rewrites()) [SPEC_ALL BETA_THM]);;

(* ------------------------------------------------------------------------ *)
(* Some miscellaneous lemmas                                                *)
(* ------------------------------------------------------------------------ *)

let MULT_DIV_2 = prove
 (`!n. (2 * n) DIV 2 = n`,
  GEN_TAC THEN MATCH_MP_TAC DIV_MULT THEN
  REWRITE_TAC[ARITH]);;

let EVEN_DIV2 = prove
 (`!n. ~(EVEN n) ==> ((SUC n) DIV 2 = SUC((n - 1) DIV 2))`,
  GEN_TAC THEN REWRITE_TAC[GSYM NOT_ODD; ODD_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
  REWRITE_TAC[SUC_SUB1] THEN REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
  SUBST1_TAC(EQT_ELIM(NUM_REDUCE_CONV `1 + 1 = 2 * 1`)) THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; MULT_DIV_2]);;

(* ------------------------------------------------------------------------ *)
(* Now set up real numbers interface                                        *)
(* ------------------------------------------------------------------------ *)

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Another lost lemma.                                                       *)
(* ------------------------------------------------------------------------- *)

let POW_ZERO = prove(
  `!n x. (x pow n = &0) ==> (x = &0)`,
  INDUCT_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[pow] THEN
  REWRITE_TAC[REAL_10; REAL_ENTIRE] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC ASSUME_TAC) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let POW_ZERO_EQ = prove(
  `!n x. (x pow (SUC n) = &0) = (x = &0)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[POW_ZERO] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[POW_0]);;

let POW_LT = prove(
  `!n x y. &0 <= x /\ x < y ==> (x pow (SUC n)) < (y pow (SUC n))`,
  REPEAT STRIP_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL
   [ASM_REWRITE_TAC[pow; REAL_MUL_RID];
    ONCE_REWRITE_TAC[pow] THEN MATCH_MP_TAC REAL_LT_MUL2_ALT THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC POW_POS THEN ASM_REWRITE_TAC[]]);;

let POW_EQ = prove(
  `!n x y. &0 <= x /\ &0 <= y /\ (x pow (SUC n) = y pow (SUC n))
        ==> (x = y)`,
  REPEAT STRIP_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
    (SPECL [`x:real`; `y:real`] REAL_LT_TOTAL) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `x pow (SUC n) = y pow (SUC n)` THEN
  CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THENL
   [ALL_TAC; CONV_TAC(RAND_CONV SYM_CONV)] THEN
  MATCH_MP_TAC REAL_LT_IMP_NE THEN
  MATCH_MP_TAC POW_LT THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Basic differentiation theorems --- none yet.                              *)
(* ------------------------------------------------------------------------- *)

let diff_net = ref empty_net;;

let add_to_diff_net th =
  let t = lhand(rator(rand(concl th))) in
  let net = !diff_net in
  let net' = enter [] (t,PART_MATCH (lhand o rator o rand) th) net in
  diff_net := net';;

(* ------------------------------------------------------------------------ *)
(* The three functions we define by series are exp, sin, cos                *)
(* ------------------------------------------------------------------------ *)

let exp = new_definition
  `exp(x) = suminf(\n. ((\n. inv(&(FACT n)))) n * (x pow n))`;;

let sin = new_definition
  `sin(x) = suminf(\n. ((\n. EVEN n => &0 |
      ((--(&1)) pow ((n - 1) DIV 2)) / &(FACT n))) n * (x pow n))`;;

let cos = new_definition
  `cos(x) = suminf(\n. ((\n. EVEN n => ((--(&1)) pow (n DIV 2)) / &(FACT n)
       | &0)) n * (x pow n))`;;

(* ------------------------------------------------------------------------ *)
(* Show the series for exp converges, using the ratio test                  *)
(* ------------------------------------------------------------------------ *)

let REAL_EXP_CONVERGES = prove(
  `!x. (\n. ((\n. inv(&(FACT n)))) n * (x pow n)) sums exp(x)`,
  let fnz tm =
    (GSYM o MATCH_MP REAL_LT_IMP_NE o
     REWRITE_RULE[GSYM REAL_LT] o C SPEC FACT_LT) tm in
  GEN_TAC THEN REWRITE_TAC[exp] THEN MATCH_MP_TAC SUMMABLE_SUM THEN
  MATCH_MP_TAC SER_RATIO THEN
  MP_TAC (SPEC `&1` REAL_DOWN) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `c:real` REAL_ARCH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `abs(x)`) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[GE] THEN DISCH_TAC THEN
  BETA_TAC THEN
  REWRITE_TAC[ADD1; POW_ADD; ABS_MUL; REAL_MUL_ASSOC; POW_1] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL_IMP THEN
  REWRITE_TAC[ABS_POS] THEN REWRITE_TAC[GSYM ADD1; FACT] THEN
  REWRITE_TAC[GSYM REAL_MUL; MATCH_MP REAL_INV_MUL_WEAK (CONJ
   (REWRITE_RULE[GSYM REAL_INJ] (SPEC `n:num` NOT_SUC)) (fnz `n:num`))] THEN
  REWRITE_TAC[ABS_MUL; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL_IMP THEN REWRITE_TAC[ABS_POS] THEN
  MP_TAC(SPEC `n:num` LT_0) THEN REWRITE_TAC[GSYM REAL_LT] THEN
  DISCH_THEN(ASSUME_TAC o GSYM o MATCH_MP REAL_LT_IMP_NE) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP ABS_INV th]) THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_LE_LDIV THEN
  ASM_REWRITE_TAC[GSYM ABS_NZ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[REWRITE_RULE[GSYM ABS_REFL; GSYM REAL_LE] LE_0] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N * c` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_LE_RMUL_EQ th]) THEN
    REWRITE_TAC[REAL_LE] THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[LESS_EQ_SUC_REFL]]);;

(* ------------------------------------------------------------------------ *)
(* Show by the comparison test that sin and cos converge                    *)
(* ------------------------------------------------------------------------ *)

let SIN_CONVERGES = prove(
  `!x. (\n. ((\n. EVEN n => &0 |
  ((--(&1)) pow ((n - 1) DIV 2)) / &(FACT n))) n * (x pow n)) sums
  sin(x)`,
  GEN_TAC THEN REWRITE_TAC[sin] THEN MATCH_MP_TAC SUMMABLE_SUM THEN
  MATCH_MP_TAC SER_COMPAR THEN
  EXISTS_TAC `\n. ((\n. inv(&(FACT n)))) n * (abs(x) pow n)` THEN
  REWRITE_TAC[MATCH_MP SUM_SUMMABLE (SPEC_ALL REAL_EXP_CONVERGES)] THEN
  EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN
  DISCH_THEN(K ALL_TAC) THEN BETA_TAC THEN LCOND_CASES_TAC THEN
  REWRITE_TAC[ABS_MUL; POW_ABS] THENL
   [REWRITE_TAC[ABS_0; REAL_MUL_LZERO] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[ABS_POS];
    REWRITE_TAC[real_div; ABS_MUL; POW_M1; REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL_IMP THEN REWRITE_TAC[ABS_POS] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[ABS_REFL]] THEN
  MAP_EVERY MATCH_MP_TAC [REAL_LT_IMP_LE; REAL_INV_POS] THEN
  REWRITE_TAC[REAL_LT; FACT_LT]);;

let COS_CONVERGES = prove(
  `!x. (\n. ((\n. EVEN n => ((--(&1)) pow (n DIV 2)) / &(FACT n) | &0)) n
    * (x pow n)) sums cos(x)`,
  GEN_TAC THEN REWRITE_TAC[cos] THEN MATCH_MP_TAC SUMMABLE_SUM THEN
  MATCH_MP_TAC SER_COMPAR THEN
  EXISTS_TAC `\n. ((\n. inv(&(FACT n)))) n * (abs(x) pow n)` THEN
  REWRITE_TAC[MATCH_MP SUM_SUMMABLE (SPEC_ALL REAL_EXP_CONVERGES)] THEN
  EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN
  DISCH_THEN(K ALL_TAC) THEN BETA_TAC THEN LCOND_CASES_TAC THEN
  REWRITE_TAC[ABS_MUL; POW_ABS] THENL
   [REWRITE_TAC[real_div; ABS_MUL; POW_M1; REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL_IMP THEN REWRITE_TAC[ABS_POS] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[ABS_REFL];
    REWRITE_TAC[ABS_0; REAL_MUL_LZERO] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[ABS_POS]] THEN
  MAP_EVERY MATCH_MP_TAC [REAL_LT_IMP_LE; REAL_INV_POS] THEN
  REWRITE_TAC[REAL_LT; FACT_LT]);;

(* ------------------------------------------------------------------------ *)
(* Show what the formal derivatives of these series are                     *)
(* ------------------------------------------------------------------------ *)

let REAL_EXP_FDIFF = prove(
  `diffs (\n. inv(&(FACT n))) = (\n. inv(&(FACT n)))`,
  REWRITE_TAC[diffs] THEN BETA_TAC THEN
  CONV_TAC(X_FUN_EQ_CONV `n:num`) THEN GEN_TAC THEN BETA_TAC THEN
  REWRITE_TAC[FACT; GSYM REAL_MUL] THEN
  SUBGOAL_THEN `~(&(SUC n) = &0) /\ ~(&(FACT n) = &0)` ASSUME_TAC THENL
   [CONJ_TAC THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN
    REWRITE_TAC[REAL_LT; LT_0; FACT_LT];
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_INV_MUL_WEAK th]) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_MUL_ASSOC; REAL_EQ_RMUL] THEN DISJ2_TAC THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REWRITE_TAC[]]);;

let SIN_FDIFF = prove(
  `diffs (\n. EVEN n => &0 | ((--(&1)) pow ((n - 1) DIV 2)) / &(FACT n))
   = (\n. EVEN n => ((--(&1)) pow (n DIV 2)) / &(FACT n) | &0)`,
  REWRITE_TAC[diffs] THEN BETA_TAC THEN
  CONV_TAC(X_FUN_EQ_CONV `n:num`) THEN GEN_TAC THEN BETA_TAC THEN
  LCOND_CASES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[EVEN]) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN REWRITE_TAC[SUC_SUB1] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FACT; GSYM REAL_MUL] THEN
  SUBGOAL_THEN `~(&(SUC n) = &0) /\ ~(&(FACT n) = &0)` ASSUME_TAC THENL
   [CONJ_TAC THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN
    REWRITE_TAC[REAL_LT; LT_0; FACT_LT];
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_INV_MUL_WEAK th]) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_MUL_ASSOC; REAL_EQ_RMUL] THEN DISJ2_TAC THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REWRITE_TAC[]]);;

let COS_FDIFF = prove(
  `diffs (\n. EVEN n => ((--(&1)) pow (n DIV 2)) / &(FACT n) | &0) =
  (\n. --(((\n. EVEN n => &0 | ((--(&1)) pow ((n - 1) DIV 2)) /
   &(FACT n))) n))`,
  REWRITE_TAC[diffs] THEN BETA_TAC THEN
  CONV_TAC(X_FUN_EQ_CONV `n:num`) THEN GEN_TAC THEN BETA_TAC THEN
  LCOND_CASES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[EVEN]) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_NEG_0] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[real_div; REAL_NEG_LMUL] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN BINOP_TAC THENL
   [POP_ASSUM(SUBST1_TAC o MATCH_MP EVEN_DIV2) THEN
    REWRITE_TAC[pow] THEN REWRITE_TAC[GSYM REAL_NEG_MINUS1];
    REWRITE_TAC[FACT; GSYM REAL_MUL] THEN
    SUBGOAL_THEN `~(&(SUC n) = &0) /\ ~(&(FACT n) = &0)` ASSUME_TAC THENL
     [CONJ_TAC THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN
      REWRITE_TAC[REAL_LT; LT_0; FACT_LT];
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_INV_MUL_WEAK th]) THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_MUL_ASSOC; REAL_EQ_RMUL] THEN DISJ2_TAC THEN
      MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------ *)
(* Now at last we can get the derivatives of exp, sin and cos               *)
(* ------------------------------------------------------------------------ *)

let SIN_NEGLEMMA = prove(
  `!x. --(sin x) = suminf (\n. --(((\n. EVEN n => &0 | ((--(&1))
        pow ((n - 1) DIV 2)) / &(FACT n))) n * (x pow n)))`,
  GEN_TAC THEN MATCH_MP_TAC SUM_UNIQ THEN
  MP_TAC(MATCH_MP SER_NEG (SPEC `x:real` SIN_CONVERGES)) THEN
  BETA_TAC THEN DISCH_THEN ACCEPT_TAC);;

let DIFF_EXP = prove(
  `!x. (exp diffl exp(x))(x)`,
  GEN_TAC THEN REWRITE_TAC[HALF_MK_ABS exp] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_EXP_FDIFF] THEN
  CONV_TAC(LAND_CONV BETA_CONV) THEN
  MATCH_MP_TAC TERMDIFF THEN EXISTS_TAC `abs(x) + &1` THEN
  REWRITE_TAC[REAL_EXP_FDIFF; MATCH_MP SUM_SUMMABLE (SPEC_ALL REAL_EXP_CONVERGES)] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `abs(x) + &1` THEN
  REWRITE_TAC[ABS_LE; REAL_LT_ADDR] THEN
  REWRITE_TAC[REAL_LT; num_CONV `1`; LT_0]);;

let DIFF_SIN = prove(
  `!x. (sin diffl cos(x))(x)`,
  GEN_TAC THEN REWRITE_TAC[HALF_MK_ABS sin; cos] THEN
  ONCE_REWRITE_TAC[GSYM SIN_FDIFF] THEN
  MATCH_MP_TAC TERMDIFF THEN EXISTS_TAC `abs(x) + &1` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MATCH_MP SUM_SUMMABLE (SPEC_ALL SIN_CONVERGES)];
    REWRITE_TAC[SIN_FDIFF; MATCH_MP SUM_SUMMABLE (SPEC_ALL COS_CONVERGES)];
    REWRITE_TAC[SIN_FDIFF; COS_FDIFF] THEN BETA_TAC THEN
    MP_TAC(SPEC `abs(x) + &1` SIN_CONVERGES) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SER_NEG) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN BETA_TAC THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL];
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `abs(x) + &1` THEN
    REWRITE_TAC[ABS_LE; REAL_LT_ADDR] THEN
    REWRITE_TAC[REAL_LT; num_CONV `1`; LT_0]]);;

let DIFF_COS = prove(
  `!x. (cos diffl --(sin(x)))(x)`,
  GEN_TAC THEN REWRITE_TAC[HALF_MK_ABS cos; SIN_NEGLEMMA] THEN
  ONCE_REWRITE_TAC[REAL_NEG_LMUL] THEN
  REWRITE_TAC[GSYM(CONV_RULE(RAND_CONV BETA_CONV)
    (AP_THM COS_FDIFF `n:num`))] THEN
  MATCH_MP_TAC TERMDIFF THEN EXISTS_TAC `abs(x) + &1` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MATCH_MP SUM_SUMMABLE (SPEC_ALL COS_CONVERGES)];
    REWRITE_TAC[COS_FDIFF] THEN
    MP_TAC(SPEC `abs(x) + &1` SIN_CONVERGES) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SER_NEG) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN BETA_TAC THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL];
    REWRITE_TAC[COS_FDIFF; DIFFS_NEG] THEN
    MP_TAC SIN_FDIFF THEN BETA_TAC THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(SPEC `abs(x) + &1` COS_CONVERGES) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SER_NEG) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN BETA_TAC THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL];
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `abs(x) + &1` THEN
    REWRITE_TAC[ABS_LE; REAL_LT_ADDR] THEN
    REWRITE_TAC[REAL_LT; num_CONV `1`; LT_0]]);;

(* ------------------------------------------------------------------------- *)
(* Differentiation conversion.                                               *)
(* ------------------------------------------------------------------------- *)

let DIFF_CONV =
  let CONJ_ACI_RULE = EQT_ELIM o PURE_REWRITE_CONV[CONJ_ACI; EQ_REFL_T] in
  let lookup_expr tm =
    tryfind (fun f -> f tm) (lookup tm (!diff_net)) in
  let v = `x:real` and k = `k:real` and diffl_tm = `(diffl)` in
  let DIFF_var = SPEC v DIFF_X
  and DIFF_const = SPECL [k;v] DIFF_CONST in
  let uneta_CONV = REWR_CONV (GSYM ETA_AX) in
  let rec DIFF_CONV tm =
    if not is_abs tm then
      let th0 = uneta_CONV tm in
      let th1 = DIFF_CONV (rand(concl th0)) in
      CONV_RULE (RATOR_CONV(LAND_CONV(K(SYM th0)))) th1 else
    let x,bod = dest_abs tm in
    if bod = x then INST [x,v] DIFF_var
    else if not free_in x bod then INST [bod,k; x,v] DIFF_const else
    let th = lookup_expr tm in
    let hyp = fst(dest_imp(concl th)) in
    let hyps = conjuncts hyp in
    let dhyps,sides = partition
      (fun t -> try funpow 3 rator t = diffl_tm
                with Failure _ -> false) hyps in
    let tha = CONJ_ACI_RULE(mk_eq(hyp,list_mk_conj(dhyps@sides))) in
    let thb = CONV_RULE (LAND_CONV (K tha)) th in
    let dths = map (DIFF_CONV o lhand o rator) dhyps in
    MATCH_MP thb (end_itlist CONJ (dths @ map ASSUME sides)) in
  fun tm ->
    let xv = try bndvar tm with Failure _ -> v in
    GEN xv (DISCH_ALL(DIFF_CONV tm));;

(* ------------------------------------------------------------------------- *)
(* Processed versions of composition theorems.                               *)
(* ------------------------------------------------------------------------- *)

let DIFF_COMPOSITE = prove
 (`((f diffl l)(x) /\ ~(f(x) = &0) ==>
        ((\x. inv(f x)) diffl --(l / (f(x) pow 2)))(x)) /\
   ((f diffl l)(x) /\ (g diffl m)(x) /\ ~(g(x) = &0) ==>
    ((\x. f(x) / g(x)) diffl (((l * g(x)) - (m * f(x))) / (g(x) pow 2)))(x)) /\
   ((f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) + g(x)) diffl (l + m))(x)) /\
   ((f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) * g(x)) diffl ((l * g(x)) + (m * f(x))))(x)) /\
   ((f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) - g(x)) diffl (l - m))(x)) /\
   ((f diffl l)(x) ==> ((\x. --(f x)) diffl --l)(x)) /\
   ((g diffl m)(x) ==>
         ((\x. (g x) pow n) diffl ((&n * (g x) pow (n - 1)) * m))(x)) /\
   ((g diffl m)(x) ==> ((\x. exp(g x)) diffl (exp(g x) * m))(x)) /\
   ((g diffl m)(x) ==> ((\x. sin(g x)) diffl (cos(g x) * m))(x)) /\
   ((g diffl m)(x) ==> ((\x. cos(g x)) diffl (--(sin(g x)) * m))(x))`,
  REWRITE_TAC[DIFF_INV; DIFF_DIV; DIFF_ADD; DIFF_SUB; DIFF_MUL; DIFF_NEG] THEN
  REPEAT CONJ_TAC THEN DISCH_TAC THEN
  TRY(MATCH_MP_TAC DIFF_CHAIN THEN
  ASM_REWRITE_TAC[DIFF_SIN; DIFF_COS; DIFF_EXP]) THEN
  MATCH_MP_TAC(BETA_RULE (SPEC `\x. x pow n` DIFF_CHAIN)) THEN
  ASM_REWRITE_TAC[DIFF_POW]);;

do_list add_to_diff_net (CONJUNCTS DIFF_COMPOSITE);;

(* ------------------------------------------------------------------------ *)
(* Properties of the exponential function                                   *)
(* ------------------------------------------------------------------------ *)

let REAL_EXP_0 = prove(
  `exp(&0) = &1`,
  REWRITE_TAC[exp] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SUM_UNIQ THEN BETA_TAC THEN
  W(MP_TAC o C SPEC SER_0 o rand o rator o snd) THEN
  DISCH_THEN(MP_TAC o SPEC `1`) THEN
  REWRITE_TAC[num_CONV `1`; Sum] THEN
  REWRITE_TAC[ADD_CLAUSES; REAL_ADD_LID] THEN BETA_TAC THEN
  REWRITE_TAC[FACT; pow; REAL_MUL_RID; REAL_INV1] THEN
  REWRITE_TAC[SYM(num_CONV `1`)] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[num_CONV `1`; LE_SUC_LT] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
  REWRITE_TAC[GSYM ADD1; POW_0; REAL_MUL_RZERO; ADD_CLAUSES]);;

let REAL_EXP_LE_X = prove(
  `!x. &0 <= x ==> (&1 + x) <= exp(x)`,
  GEN_TAC THEN DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [MP_TAC(SPECL [`\n. ((\n. inv(&(FACT n)))) n * (x pow n)`; `2`]
     SER_POS_LE) THEN
    REWRITE_TAC[MATCH_MP SUM_SUMMABLE (SPEC_ALL REAL_EXP_CONVERGES)] THEN
    REWRITE_TAC[GSYM exp] THEN BETA_TAC THEN
    W(C SUBGOAL_THEN (fun t ->REWRITE_TAC[t]) o
    funpow 2 (fst o dest_imp) o snd) THENL
     [GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_INV_POS THEN
        REWRITE_TAC[REAL_LT; FACT_LT];
        MATCH_MP_TAC POW_POS THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        FIRST_ASSUM ACCEPT_TAC];
      CONV_TAC(TOP_DEPTH_CONV num_CONV) THEN REWRITE_TAC[Sum] THEN
      BETA_TAC THEN REWRITE_TAC[ADD_CLAUSES; FACT; pow; REAL_ADD_LID] THEN
      REWRITE_TAC[MULT_CLAUSES; REAL_INV1; REAL_MUL_LID; ADD_CLAUSES] THEN
      REWRITE_TAC[REAL_MUL_RID; SYM(num_CONV `1`)]];
    POP_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_EXP_0; REAL_ADD_RID; REAL_LE_REFL]]);;

let REAL_EXP_LT_1 = prove(
  `!x. &0 < x ==> &1 < exp(x)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `&1 + x` THEN ASM_REWRITE_TAC[REAL_LT_ADDR] THEN
  MATCH_MP_TAC REAL_EXP_LE_X THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  POP_ASSUM ACCEPT_TAC);;

let REAL_EXP_ADD_MUL = prove(
  `!x y. exp(x + y) * exp(--x) = exp(y)`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(X_BETA_CONV `x:real`)) THEN
  SUBGOAL_THEN `exp(y) = (\x. exp(x + y) * exp(--x))(&0)` SUBST1_TAC THENL
   [BETA_TAC THEN REWRITE_TAC[REAL_ADD_LID; REAL_NEG_0] THEN
    REWRITE_TAC[REAL_EXP_0; REAL_MUL_RID];
    MATCH_MP_TAC DIFF_ISCONST_ALL THEN X_GEN_TAC `x:real` THEN
    W(MP_TAC o DIFF_CONV o rand o funpow 2 rator o snd) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real`) THEN
    MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_NEG_LMUL; GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC[GSYM real_sub; REAL_SUB_0; REAL_MUL_RID; REAL_ADD_RID] THEN
    MATCH_ACCEPT_TAC REAL_MUL_SYM]);;

let REAL_EXP_NEG_MUL = prove(
  `!x. exp(x) * exp(--x) = &1`,
  GEN_TAC THEN MP_TAC(SPECL [`x:real`; `&0`] REAL_EXP_ADD_MUL) THEN
  REWRITE_TAC[REAL_ADD_RID; REAL_EXP_0]);;

let REAL_EXP_NEG_MUL2 = prove(
  `!x. exp(--x) * exp(x) = &1`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_ACCEPT_TAC REAL_EXP_NEG_MUL);;

let REAL_EXP_NEG = prove(
  `!x. exp(--x) = inv(exp(x))`,
  GEN_TAC THEN MATCH_MP_TAC REAL_RINV_UNIQ THEN
  MATCH_ACCEPT_TAC REAL_EXP_NEG_MUL);;

let REAL_EXP_ADD = prove(
  `!x y. exp(x + y) = exp(x) * exp(y)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`x:real`; `y:real`] REAL_EXP_ADD_MUL) THEN
  DISCH_THEN(MP_TAC o C AP_THM `exp(x)` o AP_TERM `(*)`) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] REAL_EXP_NEG_MUL; REAL_MUL_RID] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_ACCEPT_TAC REAL_MUL_SYM);;

let REAL_EXP_POS_LE = prove(
  `!x. &0 <= exp(x)`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (funpow 2 RAND_CONV) [GSYM REAL_HALF_DOUBLE] THEN
  REWRITE_TAC[REAL_EXP_ADD] THEN MATCH_ACCEPT_TAC REAL_LE_SQUARE);;

let REAL_EXP_NZ = prove(
  `!x. ~(exp(x) = &0)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:real` REAL_EXP_NEG_MUL) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  MATCH_ACCEPT_TAC REAL_10);;

let REAL_EXP_POS_LT = prove(
  `!x. &0 < exp(x)`,
  GEN_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  REWRITE_TAC[REAL_EXP_POS_LE; REAL_EXP_NZ]);;

let REAL_EXP_N = prove(
  `!n x. exp(&n * x) = exp(x) pow n`,
  INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_EXP_0; pow] THEN
  REWRITE_TAC[ADD1] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[GSYM REAL_ADD; REAL_EXP_ADD; REAL_RDISTRIB] THEN
  GEN_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LID]);;

let REAL_EXP_SUB = prove(
  `!x y. exp(x - y) = exp(x) / exp(y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_sub; real_div; REAL_EXP_ADD; REAL_EXP_NEG]);;

let REAL_EXP_MONO_IMP = prove(
  `!x y. x < y ==> exp(x) < exp(y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o
    MATCH_MP REAL_EXP_LT_1 o ONCE_REWRITE_RULE[GSYM REAL_SUB_LT]) THEN
  REWRITE_TAC[REAL_EXP_SUB] THEN
  SUBGOAL_THEN `&1 < exp(y) / exp(x) =
                 (&1 * exp(x)) < ((exp(y) / exp(x)) * exp(x))` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LT_RMUL_EQ THEN
    MATCH_ACCEPT_TAC REAL_EXP_POS_LT;
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_EXP_NEG_MUL2; GSYM REAL_EXP_NEG] THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RID]]);;

let REAL_EXP_MONO_LT = prove(
  `!x y. exp(x) < exp(y) = x < y`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[REAL_NOT_LT] THEN
    REWRITE_TAC[REAL_LE_LT] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    REWRITE_TAC[] THEN DISJ1_TAC THEN MATCH_MP_TAC REAL_EXP_MONO_IMP THEN
    POP_ASSUM ACCEPT_TAC;
    MATCH_ACCEPT_TAC REAL_EXP_MONO_IMP]);;

let REAL_EXP_MONO_LE = prove(
  `!x y. exp(x) <= exp(y) = x <= y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  REWRITE_TAC[REAL_EXP_MONO_LT]);;

let REAL_EXP_INJ = prove(
  `!x y. (exp(x) = exp(y)) = (x = y)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE]);;

let REAL_EXP_TOTAL_LEMMA = prove(
  `!y. &1 <= y ==> ?x. &0 <= x /\ x <= y - &1 /\ (exp(x) = y)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC IVT THEN
  ASM_REWRITE_TAC[REAL_EXP_0; REAL_LE_SUB_LADD; REAL_ADD_LID] THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM REAL_SUB_LE]) THEN
    POP_ASSUM(MP_TAC o MATCH_MP REAL_EXP_LE_X) THEN REWRITE_TAC[REAL_SUB_ADD2];
    X_GEN_TAC `x:real` THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC `exp(x)` THEN
    MATCH_ACCEPT_TAC DIFF_EXP]);;

let REAL_EXP_TOTAL = prove(
  `!y. &0 < y ==> ?x. exp(x) = y`,
  GEN_TAC THEN DISCH_TAC THEN
  DISJ_CASES_TAC(SPECL [`&1`; `y:real`] REAL_LET_TOTAL) THENL
   [FIRST_ASSUM(X_CHOOSE_TAC `x:real` o MATCH_MP REAL_EXP_TOTAL_LEMMA) THEN
    EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[];
    MP_TAC(SPEC `y:real` REAL_INV_LT1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real` o MATCH_MP REAL_EXP_TOTAL_LEMMA) THEN
    EXISTS_TAC `--x` THEN ASM_REWRITE_TAC[REAL_EXP_NEG] THEN
    MATCH_MP_TAC REAL_INVINV THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN ASM_REWRITE_TAC[]]);;

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

(* ------------------------------------------------------------------------ *)
(* Properties of the logarithmic function                                   *)
(* ------------------------------------------------------------------------ *)

let ln = new_definition
  `ln x = @u. exp(u) = x`;;

let LN_EXP = prove(
  `!x. ln(exp x) = x`,
  GEN_TAC THEN REWRITE_TAC[ln; REAL_EXP_INJ] THEN
  CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN MATCH_MP_TAC SELECT_AX THEN
  EXISTS_TAC `x:real` THEN REFL_TAC);;

let REAL_EXP_LN = prove(
  `!x. (exp(ln x) = x) = &0 < x`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC REAL_EXP_POS_LT;
    DISCH_THEN(X_CHOOSE_THEN `y:real` MP_TAC o MATCH_MP REAL_EXP_TOTAL) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[REAL_EXP_INJ; LN_EXP]]);;

let LN_MUL = prove(
  `!x y. &0 < x /\ &0 < y ==> (ln(x * y) = ln(x) + ln(y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_EXP_INJ] THEN
  REWRITE_TAC[REAL_EXP_ADD] THEN SUBGOAL_THEN `&0 < x * y` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    EVERY_ASSUM(fun th -> REWRITE_TAC[ONCE_REWRITE_RULE[GSYM REAL_EXP_LN] th])]);;

let LN_INJ = prove(
  `!x y. &0 < x /\ &0 < y ==> ((ln(x) = ln(y)) = (x = y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EVERY_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
    [SYM(REWRITE_RULE[GSYM REAL_EXP_LN] th)]) THEN
  CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC REAL_EXP_INJ);;

let LN_1 = prove(
  `ln(&1) = &0`,
  ONCE_REWRITE_TAC[GSYM REAL_EXP_INJ] THEN
  REWRITE_TAC[REAL_EXP_0; REAL_EXP_LN; REAL_LT_01]);;

let LN_INV = prove(
  `!x. &0 < x ==> (ln(inv x) = --(ln x))`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_RNEG_UNIQ] THEN
  SUBGOAL_THEN `&0 < x /\ &0 < inv(x)` MP_TAC THENL
   [CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_INV_POS) THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP LN_MUL th)]) THEN
    SUBGOAL_THEN `x * (inv x) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_RINV THEN
      POP_ASSUM(ACCEPT_TAC o MATCH_MP REAL_POS_NZ);
      REWRITE_TAC[LN_1]]]);;

let LN_DIV = prove(
  `!x. &0 < x /\ &0 < y ==> (ln(x / y) = ln(x) - ln(y))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < x /\ &0 < inv(y)` MP_TAC THENL
   [CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_INV_POS) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[real_div] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LN_MUL th]) THEN
    REWRITE_TAC[MATCH_MP LN_INV (ASSUME `&0 < y`)] THEN
    REWRITE_TAC[real_sub]]);;

let LN_MONO_LT = prove(
  `!x y. &0 < x /\ &0 < y ==> (ln(x) < ln(y) = x < y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EVERY_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
    [SYM(REWRITE_RULE[GSYM REAL_EXP_LN] th)]) THEN
  CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC REAL_EXP_MONO_LT);;

let LN_MONO_LE = prove(
  `!x y. &0 < x /\ &0 < y ==> (ln(x) <= ln(y) = x <= y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EVERY_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
    [SYM(REWRITE_RULE[GSYM REAL_EXP_LN] th)]) THEN
  CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC REAL_EXP_MONO_LE);;

let LN_POW = prove(
  `!n x. &0 < x ==> (ln(x pow n) = &n * ln(x))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CHOOSE_THEN (SUBST1_TAC o SYM) o MATCH_MP REAL_EXP_TOTAL) THEN
  REWRITE_TAC[GSYM REAL_EXP_N; LN_EXP]);;

let LN_LE = prove(
  `!x. &0 <= x ==> ln(&1 + x) <= x`,
  GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC RAND_CONV  [GSYM LN_EXP] THEN
  MP_TAC(SPECL [`&1 + x`; `exp(x)`] LN_MONO_LE) THEN
  W(C SUBGOAL_THEN (fun t -> REWRITE_TAC[t]) o funpow 2 (fst o dest_imp) o snd) THENL
   [REWRITE_TAC[REAL_EXP_POS_LT] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[REAL_LT_ADDL; REAL_LT_01];
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC REAL_EXP_LE_X THEN ASM_REWRITE_TAC[]]);;

let LN_LT_X = prove(
  `!x. &0 < x ==> ln(x) < x`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `ln(&1 + x)` THEN CONJ_TAC THENL
   [IMP_SUBST_TAC LN_MONO_LT THEN
    ASM_REWRITE_TAC[REAL_LT_ADDL; REAL_LT_01] THEN
    MATCH_MP_TAC REAL_LT_ADD THEN ASM_REWRITE_TAC[REAL_LT_01];
    MATCH_MP_TAC LN_LE THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ASM_REWRITE_TAC[]]);;

let LN_POS = prove(
  `!x. &1 <= x ==> &0 <= ln(x)`,
  GEN_TAC THEN DISCH_TAC THEN SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[REAL_LT_01];
    UNDISCH_TAC `&1 <= x` THEN SUBST1_TAC(SYM REAL_EXP_0) THEN
    POP_ASSUM(MP_TAC o REWRITE_RULE[GSYM REAL_EXP_LN]) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[REAL_EXP_MONO_LE]]);;

let DIFF_LN = prove(
  `!x. &0 < x ==> (ln diffl (inv x))(x)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[GSYM REAL_EXP_LN]) THEN
  FIRST_ASSUM (fun th ->  GEN_REWRITE_TAC RAND_CONV  [GSYM th]) THEN
  MATCH_MP_TAC DIFF_INVERSE_LT THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_POS_NZ) THEN
  ASM_REWRITE_TAC[MATCH_MP DIFF_CONT (SPEC_ALL DIFF_EXP)] THEN
  MP_TAC(SPEC `ln(x)` DIFF_EXP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[LN_EXP] THEN
  EXISTS_TAC `&1` THEN MATCH_ACCEPT_TAC REAL_LT_01);;

(* ------------------------------------------------------------------------ *)
(* Some properties of roots (easier via logarithms)                         *)
(* ------------------------------------------------------------------------ *)

let root = new_definition
  `root(n) x = @u. (&0 < x ==> &0 < u) /\ (u pow n = x)`;;

let sqrt = new_definition
  `sqrt(x) = root(2) x`;;

let ROOT_LT_LEMMA = prove(
  `!n x. &0 < x ==> (exp(ln(x) / &(SUC n)) pow (SUC n) = x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_EXP_N] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  SUBGOAL_THEN `inv(&(SUC n)) * &(SUC n) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC[REAL_INJ; NOT_SUC];
    ASM_REWRITE_TAC[REAL_MUL_RID; REAL_EXP_LN]]);;

let ROOT_LN = prove(
  `!x. &0 < x ==> !n. root(SUC n) x = exp(ln(x) / &(SUC n))`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC[root] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `y:real` THEN BETA_TAC THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    SUBGOAL_THEN `!z. &0 < y /\ &0 < exp(z)` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o GEN_ALL o SYM o MATCH_MP LN_INJ o SPEC_ALL) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC I [th]) THEN
    REWRITE_TAC[LN_EXP] THEN
    SUBGOAL_THEN `ln(y) * &(SUC n) = (ln(y pow(SUC n)) / &(SUC n)) * &(SUC n)`
    MP_TAC THENL
     [REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
      SUBGOAL_THEN `inv(&(SUC n)) * &(SUC n) = &1` SUBST1_TAC THENL
       [MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC[REAL_INJ; NOT_SUC];
        REWRITE_TAC[REAL_MUL_RID] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC LN_POW THEN
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[REAL_EQ_RMUL; REAL_INJ; NOT_SUC]];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    MATCH_MP_TAC ROOT_LT_LEMMA THEN ASM_REWRITE_TAC[]]);;

let ROOT_0 = prove(
  `!n. root(SUC n) (&0) = &0`,
  GEN_TAC THEN REWRITE_TAC[root] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `y:real` THEN
  BETA_TAC THEN REWRITE_TAC[REAL_LT_REFL] THEN EQ_TAC THENL
   [SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN ONCE_REWRITE_TAC[pow] THENL
     [REWRITE_TAC[pow; REAL_MUL_RID];
      REWRITE_TAC[REAL_ENTIRE] THEN DISCH_THEN DISJ_CASES_TAC THEN
      ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[pow; REAL_MUL_LZERO]]);;

let ROOT_1 = prove(
  `!n. root(SUC n) (&1) = &1`,
  GEN_TAC THEN REWRITE_TAC[MATCH_MP ROOT_LN REAL_LT_01] THEN
  REWRITE_TAC[LN_1; REAL_DIV_LZERO; REAL_EXP_0]);;

let ROOT_POW_POS = prove(
  `!n x. &0 <= x ==> ((root(SUC n) x) pow (SUC n) = x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC
     [MATCH_MP ROOT_LN th; MATCH_MP ROOT_LT_LEMMA th]);
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[ROOT_0] THEN
    MATCH_ACCEPT_TAC POW_0]);;

let POW_ROOT_POS = prove(
  `!n x. &0 <= x ==> (root(SUC n)(x pow (SUC n)) = x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[root] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `y:real` THEN BETA_TAC THEN EQ_TAC THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THENL
   [DISJ_CASES_THEN MP_TAC (REWRITE_RULE[REAL_LE_LT] (ASSUME `&0 <= x`)) THENL
     [DISCH_TAC THEN FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
      FIRST_ASSUM(fun th ->  REWRITE_TAC[MATCH_MP POW_POS_LT th]) THEN
      DISCH_TAC THEN MATCH_MP_TAC POW_EQ THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
      REWRITE_TAC[POW_0; REAL_LT_REFL; POW_ZERO]];
    ASM_REWRITE_TAC[REAL_LT_LE] THEN CONV_TAC CONTRAPOS_CONV THEN
    REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[POW_0]]);;

let ROOT_POS_POSITIVE = prove
 (`!x n. &0 <= x ==> &0 <= root(SUC n) x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [POP_ASSUM(fun th -> REWRITE_TAC[MATCH_MP ROOT_LN th]) THEN
    REWRITE_TAC[REAL_EXP_POS_LE];
    POP_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[ROOT_0] THEN
    REWRITE_TAC[REAL_LE_REFL]]);;

let ROOT_POS_UNIQ = prove
 (`!n x y. &0 <= x /\ &0 <= y /\ (y pow (SUC n) = x)
           ==> (root (SUC n) x = y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
  ASM_SIMP_TAC[POW_ROOT_POS]);;

let ROOT_MUL = prove
 (`!n x y. &0 <= x /\ &0 <= y
           ==> (root(SUC n) (x * y) = root(SUC n) x * root(SUC n) y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ROOT_POS_UNIQ THEN
  ASM_SIMP_TAC[REAL_POW_MUL; ROOT_POW_POS; REAL_LE_MUL;
               ROOT_POS_POSITIVE]);;

let ROOT_INV = prove
 (`!n x. &0 <= x ==> (root(SUC n) (inv x) = inv(root(SUC n) x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ROOT_POS_UNIQ THEN
  ASM_SIMP_TAC[REAL_LE_INV; ROOT_POS_POSITIVE; REAL_POW_INV;
               ROOT_POW_POS]);;

let ROOT_DIV = prove
 (`!n x y. &0 <= x /\ &0 <= y
           ==> (root(SUC n) (x / y) = root(SUC n) x / root(SUC n) y)`,
  SIMP_TAC[real_div; ROOT_MUL; ROOT_INV; REAL_LE_INV]);;

let ROOT_MONO_LE = prove
 (`!x y. &0 <= x /\ x <= y ==> root(SUC n) x <= root(SUC n) y`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `&0 <= y` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
  UNDISCH_TAC `x <= y` THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x = (root(SUC n) x) pow (SUC n)) /\
                (y = (root(SUC n) y) pow (SUC n))`
   (CONJUNCTS_THEN SUBST1_TAC)
  THENL [ASM_SIMP_TAC[GSYM ROOT_POW_POS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LT2 THEN
  ASM_SIMP_TAC[NOT_SUC; ROOT_POS_POSITIVE]);;

let SQRT_0 = prove(
  `sqrt(&0) = &0`,
  REWRITE_TAC[sqrt; num_CONV `2`; ROOT_0]);;

let SQRT_1 = prove(
  `sqrt(&1) = &1`,
  REWRITE_TAC[sqrt; num_CONV `2`; ROOT_1]);;

let SQRT_POS_LT = prove
 (`!x. &0 < x ==> &0 < sqrt(x)`,
  SIMP_TAC[sqrt; num_CONV `2`; ROOT_LN; REAL_EXP_POS_LT]);;

let SQRT_POS_LE = prove
 (`!x. &0 <= x ==> &0 <= sqrt(x)`,
  REWRITE_TAC[REAL_LE_LT] THEN MESON_TAC[SQRT_POS_LT; SQRT_0]);;

let SQRT_POW2 = prove(
  `!x. (sqrt(x) pow 2 = x) = &0 <= x`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC REAL_LE_POW2;
    REWRITE_TAC[sqrt; num_CONV `2`; ROOT_POW_POS]]);;

let SQRT_POW_2 = prove
 (`!x. &0 <= x ==> (sqrt(x) pow 2 = x)`,
  REWRITE_TAC[SQRT_POW2]);;

let POW_2_SQRT = prove
 (`&0 <= x ==> (sqrt(x pow 2) = x)`,
  SIMP_TAC[sqrt; num_CONV `2`; POW_ROOT_POS]);;

let SQRT_POS_UNIQ = prove
 (`!x y. &0 <= x /\ &0 <= y /\ (y pow 2 = x)
           ==> (sqrt x = y)`,
  REWRITE_TAC[sqrt; num_CONV `2`; ROOT_POS_UNIQ]);;

let SQRT_MUL = prove
 (`!x y. &0 <= x /\ &0 <= y
           ==> (sqrt(x * y) = sqrt x * sqrt y)`,
  REWRITE_TAC[sqrt; num_CONV `2`; ROOT_MUL]);;

let SQRT_INV = prove
 (`!x. &0 <= x ==> (sqrt (inv x) = inv(sqrt x))`,
  REWRITE_TAC[sqrt; num_CONV `2`; ROOT_INV]);;

let SQRT_DIV = prove
 (`!x y. &0 <= x /\ &0 <= y
           ==> (sqrt (x / y) = sqrt x / sqrt y)`,
  REWRITE_TAC[sqrt; num_CONV `2`; ROOT_DIV]);;

let SQRT_MONO_LE = prove
 (`!x y. &0 <= x /\ x <= y ==> sqrt(x) <= sqrt(y)`,
  REWRITE_TAC[sqrt; num_CONV `2`; ROOT_MONO_LE]);;

let SQRT_EVEN_POW2 = prove
 (`!n. EVEN n ==> (sqrt(&2 pow n) = &2 pow (n DIV 2))`,
  GEN_TAC THEN REWRITE_TAC[EVEN_MOD] THEN DISCH_TAC THEN
  MATCH_MP_TAC SQRT_POS_UNIQ THEN
  SIMP_TAC[REAL_POW_LE; REAL_POS; REAL_POW_POW] THEN
  AP_TERM_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [MATCH_MP DIVISION (ARITH_RULE `~(2 = 0)`)] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES]);;

let REAL_DIV_SQRT = prove
 (`!x. &0 <= x ==> (x / sqrt(x) = sqrt(x))`,
  GEN_TAC THEN ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[SQRT_0; real_div; REAL_MUL_LZERO]; ALL_TAC] THEN
  DISCH_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_POS_UNIQ THEN
  ASM_SIMP_TAC[SQRT_POS_LE; REAL_LE_DIV] THEN
  REWRITE_TAC[real_div; REAL_POW_MUL; REAL_POW_INV] THEN
  ASM_SIMP_TAC[SQRT_POW_2] THEN
  REWRITE_TAC[REAL_POW_2; GSYM REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_RID]);;

(* ------------------------------------------------------------------------ *)
(* Basic properties of the trig functions                                   *)
(* ------------------------------------------------------------------------ *)

let SIN_0 = prove(
  `sin(&0) = &0`,
  REWRITE_TAC[sin] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SUM_UNIQ THEN BETA_TAC THEN
  W(MP_TAC o C SPEC SER_0 o rand o rator o snd) THEN
  DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LE_0] THEN
  BETA_TAC THEN
  REWRITE_TAC[Sum] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `n:num` THEN LCOND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  MP_TAC(SPEC `n:num` ODD_EXISTS) THEN ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GSYM ADD1; POW_0; REAL_MUL_RZERO]);;

let COS_0 = prove(
  `cos(&0) = &1`,
  REWRITE_TAC[cos] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SUM_UNIQ THEN BETA_TAC THEN
  W(MP_TAC o C SPEC SER_0 o rand o rator o snd) THEN
  DISCH_THEN(MP_TAC o SPEC `1`) THEN
  REWRITE_TAC[num_CONV `1`; Sum; ADD_CLAUSES] THEN BETA_TAC THEN
  REWRITE_TAC[EVEN; pow; FACT] THEN
  REWRITE_TAC[REAL_ADD_LID; REAL_MUL_RID] THEN
  SUBGOAL_THEN `0 DIV 2 = 0` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[num_CONV `2`; LT_0];
    REWRITE_TAC[pow]] THEN
  SUBGOAL_THEN `&1 / &1 = &(SUC 0)` SUBST1_TAC THENL
   [REWRITE_TAC[SYM(num_CONV `1`)] THEN MATCH_MP_TAC REAL_DIV_REFL THEN
    MATCH_ACCEPT_TAC REAL_10;
    DISCH_THEN MATCH_MP_TAC] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[LE_SUC_LT] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
  REWRITE_TAC[GSYM ADD1; POW_0; REAL_MUL_RZERO; ADD_CLAUSES]);;

let SIN_CIRCLE = prove(
  `!x. (sin(x) pow 2) + (cos(x) pow 2) = &1`,
  GEN_TAC THEN CONV_TAC(LAND_CONV(X_BETA_CONV `x:real`)) THEN
  SUBGOAL_THEN `&1 = (\x.(sin(x) pow 2) + (cos(x) pow 2))(&0)` SUBST1_TAC THENL
   [BETA_TAC THEN REWRITE_TAC[SIN_0; COS_0] THEN
    REWRITE_TAC[num_CONV `2`; POW_0] THEN
    REWRITE_TAC[pow; POW_1] THEN REWRITE_TAC[REAL_ADD_LID; REAL_MUL_LID];
    MATCH_MP_TAC DIFF_ISCONST_ALL THEN X_GEN_TAC `x:real` THEN
    W(MP_TAC o DIFF_CONV o rand o funpow 2 rator o snd) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real`) THEN
    MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_NEG_LMUL; GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC[GSYM real_sub; REAL_SUB_0] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC; REAL_MUL_RID] THEN
    AP_TERM_TAC THEN REWRITE_TAC[num_CONV `2`; SUC_SUB1] THEN
    REWRITE_TAC[POW_1] THEN MATCH_ACCEPT_TAC REAL_MUL_SYM]);;

let SIN_BOUND = prove(
  `!x. abs(sin x) <= &1`,
  GEN_TAC THEN GEN_REWRITE_TAC I [TAUT `a = ~ ~a`] THEN
  PURE_ONCE_REWRITE_TAC[REAL_NOT_LE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT1_POW2) THEN
  REWRITE_TAC[REAL_POW2_ABS] THEN
  DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[GSYM REAL_SUB_LT]) THEN
  DISCH_THEN(MP_TAC o C CONJ(SPEC `cos(x)` REAL_LE_SQUARE)) THEN
  REWRITE_TAC[GSYM POW_2] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LTE_ADD) THEN
  REWRITE_TAC[real_sub; GSYM REAL_ADD_ASSOC] THEN
  ONCE_REWRITE_TAC[AC REAL_ADD_AC
    `a + b + c = (a + c) + b`] THEN
  REWRITE_TAC[SIN_CIRCLE; REAL_ADD_RINV; REAL_LT_REFL]);;

let SIN_BOUNDS = prove(
  `!x. --(&1) <= sin(x) /\ sin(x) <= &1`,
  GEN_TAC THEN REWRITE_TAC[GSYM ABS_BOUNDS; SIN_BOUND]);;

let COS_BOUND = prove(
  `!x. abs(cos x) <= &1`,
  GEN_TAC THEN GEN_REWRITE_TAC I [TAUT `a = ~ ~a`] THEN
  PURE_ONCE_REWRITE_TAC[REAL_NOT_LE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT1_POW2) THEN
  REWRITE_TAC[REAL_POW2_ABS] THEN
  DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[GSYM REAL_SUB_LT]) THEN
  DISCH_THEN(MP_TAC o CONJ(SPEC `sin(x)` REAL_LE_SQUARE)) THEN
  REWRITE_TAC[GSYM POW_2] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LET_ADD) THEN
  REWRITE_TAC[real_sub; REAL_ADD_ASSOC; SIN_CIRCLE;
    REAL_ADD_ASSOC; SIN_CIRCLE; REAL_ADD_RINV; REAL_LT_REFL]);;

let COS_BOUNDS = prove(
  `!x. --(&1) <= cos(x) /\ cos(x) <= &1`,
  GEN_TAC THEN REWRITE_TAC[GSYM ABS_BOUNDS; COS_BOUND]);;

let SIN_COS_ADD = prove(
  `!x y. ((sin(x + y) - ((sin(x) * cos(y)) + (cos(x) * sin(y)))) pow 2) +
         ((cos(x + y) - ((cos(x) * cos(y)) - (sin(x) * sin(y)))) pow 2) = &0`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(X_BETA_CONV `x:real`)) THEN
  W(C SUBGOAL_THEN (SUBST1_TAC o SYM) o subst[`&0`,`x:real`] o snd) THENL
   [BETA_TAC THEN REWRITE_TAC[SIN_0; COS_0] THEN
    REWRITE_TAC[REAL_ADD_LID; REAL_MUL_LZERO; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_SUB_RZERO; REAL_SUB_REFL] THEN
    REWRITE_TAC[num_CONV `2`; POW_0; REAL_ADD_LID];
    MATCH_MP_TAC DIFF_ISCONST_ALL THEN GEN_TAC THEN
    W(MP_TAC o DIFF_CONV o rand o funpow 2 rator o snd) THEN
    NUM_REDUCE_TAC THEN REWRITE_TAC[POW_1] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; REAL_MUL_RID] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real`) THEN
    MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_NEG_LMUL] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EQ_SUB_LADD] THEN
    REWRITE_TAC[REAL_SUB_LZERO; GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_NEG_RMUL] THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN BINOP_TAC THENL
     [REWRITE_TAC[real_sub; REAL_NEG_ADD; REAL_NEGNEG; REAL_NEG_RMUL];
      REWRITE_TAC[GSYM REAL_NEG_RMUL; GSYM real_sub]]]);;

let SIN_COS_NEG = prove(
  `!x. ((sin(--x) + (sin x)) pow 2) +
       ((cos(--x) - (cos x)) pow 2) = &0`,
  GEN_TAC THEN CONV_TAC(LAND_CONV(X_BETA_CONV `x:real`)) THEN
  W(C SUBGOAL_THEN (SUBST1_TAC o SYM) o subst[`&0`,`x:real`] o snd) THENL
   [BETA_TAC THEN REWRITE_TAC[SIN_0; COS_0; REAL_NEG_0] THEN
    REWRITE_TAC[REAL_ADD_LID; REAL_SUB_REFL] THEN
    REWRITE_TAC[num_CONV `2`; POW_0; REAL_ADD_LID];
    MATCH_MP_TAC DIFF_ISCONST_ALL THEN GEN_TAC THEN
    W(MP_TAC o DIFF_CONV o rand o funpow 2 rator o snd) THEN
    NUM_REDUCE_TAC THEN REWRITE_TAC[POW_1] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real`) THEN
    MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC[REAL_MUL_RID; real_sub; REAL_NEGNEG; GSYM REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EQ_SUB_LADD] THEN
    REWRITE_TAC[REAL_SUB_LZERO; REAL_NEG_RMUL] THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL; REAL_NEG_RMUL] THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_NEG_ADD; REAL_NEGNEG]]);;

let SIN_ADD = prove(
  `!x y. sin(x + y) = (sin(x) * cos(y)) + (cos(x) * sin(y))`,
  REPEAT GEN_TAC THEN MP_TAC(SPECL [`x:real`; `y:real`] SIN_COS_ADD) THEN
  REWRITE_TAC[POW_2; REAL_SUMSQ] THEN REWRITE_TAC[REAL_SUB_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let COS_ADD = prove(
  `!x y. cos(x + y) = (cos(x) * cos(y)) - (sin(x) * sin(y))`,
  REPEAT GEN_TAC THEN MP_TAC(SPECL [`x:real`; `y:real`] SIN_COS_ADD) THEN
  REWRITE_TAC[POW_2; REAL_SUMSQ] THEN REWRITE_TAC[REAL_SUB_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let SIN_NEG = prove(
  `!x. sin(--x) = --(sin(x))`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` SIN_COS_NEG) THEN
  REWRITE_TAC[POW_2; REAL_SUMSQ] THEN REWRITE_TAC[REAL_LNEG_UNIQ] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let COS_NEG = prove(
  `!x. cos(--x) = cos(x)`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` SIN_COS_NEG) THEN
  REWRITE_TAC[POW_2; REAL_SUMSQ] THEN REWRITE_TAC[REAL_SUB_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let SIN_DOUBLE = prove(
  `!x. sin(&2 * x) = &2 * sin(x) * cos(x)`,
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_DOUBLE; SIN_ADD] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_MUL_SYM);;

let COS_DOUBLE = prove(
  `!x. cos(&2 * x) = (cos(x) pow 2) - (sin(x) pow 2)`,
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_DOUBLE; COS_ADD; POW_2]);;

(* ------------------------------------------------------------------------ *)
(* Show that there's a least positive x with cos(x) = 0; hence define pi    *)
(* ------------------------------------------------------------------------ *)

let SIN_PAIRED = prove(
  `!x. (\n. (((--(&1)) pow n) / &(FACT((2 * n) + 1)))
         * (x pow ((2 * n) + 1))) sums (sin x)`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` SIN_CONVERGES) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_PAIR) THEN REWRITE_TAC[GSYM sin] THEN
  BETA_TAC THEN REWRITE_TAC[SUM_2] THEN BETA_TAC THEN
  REWRITE_TAC[GSYM ADD1; EVEN_DOUBLE;
              REWRITE_RULE[GSYM NOT_EVEN] ODD_DOUBLE] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID; SUC_SUB1; MULT_DIV_2]);;

let SIN_POS = prove(
  `!x. &0 < x /\ x < &2 ==> &0 < sin(x)`,
  GEN_TAC THEN STRIP_TAC THEN MP_TAC(SPEC `x:real` SIN_PAIRED) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_PAIR) THEN
  REWRITE_TAC[SYM(MATCH_MP SUM_UNIQ (SPEC `x:real` SIN_PAIRED))] THEN
  REWRITE_TAC[SUM_2] THEN BETA_TAC THEN REWRITE_TAC[GSYM ADD1] THEN
  REWRITE_TAC[pow; GSYM REAL_NEG_MINUS1; POW_MINUS1] THEN
  REWRITE_TAC[real_div; GSYM REAL_NEG_LMUL; GSYM real_sub] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN REWRITE_TAC[ADD1] THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP SUM_UNIQ) THEN
  W(C SUBGOAL_THEN SUBST1_TAC o curry mk_eq `&0` o curry mk_comb `Sum(0,0)` o
  funpow 2 rand o snd) THENL [REWRITE_TAC[Sum]; ALL_TAC] THEN
  MATCH_MP_TAC SER_POS_LT THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP SUM_SUMMABLE th]) THEN
  X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN BETA_TAC THEN
  REWRITE_TAC[GSYM ADD1; MULT_CLAUSES] THEN
  REWRITE_TAC[num_CONV `2`; ADD_CLAUSES; pow; FACT; GSYM REAL_MUL] THEN
  REWRITE_TAC[SYM(num_CONV `2`)] THEN
  REWRITE_TAC[num_CONV `1`; ADD_CLAUSES; pow; FACT; GSYM REAL_MUL] THEN
  REWRITE_TAC[REAL_SUB_LT] THEN ONCE_REWRITE_TAC[GSYM pow] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LT_RMUL_IMP THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC POW_POS_LT THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM POW_2] THEN
  SUBGOAL_THEN `!n. &0 < &(SUC n)` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_LT; LT_0]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 < &(FACT n)` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_LT; FACT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. ~(&(SUC n) = &0)` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_INJ; NOT_SUC]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. ~(&(FACT n) = &0)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_POS_NZ THEN
    REWRITE_TAC[REAL_LT; FACT_LT]; ALL_TAC] THEN
  REPEAT(IMP_SUBST_TAC REAL_INV_MUL_WEAK THEN ASM_REWRITE_TAC[REAL_ENTIRE]) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC
    `a * b * c * d * e = (a * b * e) * (c * d)`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LT_RMUL_IMP THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_INV_POS THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  IMP_SUBST_TAC ((CONV_RULE(RAND_CONV SYM_CONV) o SPEC_ALL) REAL_INV_MUL_WEAK) THEN
  ASM_REWRITE_TAC[REAL_ENTIRE] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_LT_1 THEN
  REWRITE_TAC[POW_2] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC;
    MATCH_MP_TAC REAL_LT_MUL2_ALT THEN REPEAT CONJ_TAC] THEN
  TRY(MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[] THEN NO_TAC) THENL
   [W(prefix THEN (MATCH_MP_TAC REAL_LT_TRANS) o EXISTS_TAC o
      curry mk_comb `&` o funpow 3 rand o snd) THEN
    REWRITE_TAC[REAL_LT; LESS_SUC_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&2` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(REDEPTH_CONV num_CONV) THEN
  REWRITE_TAC[REAL_LE; LE_SUC; LE_0]);;

let COS_PAIRED = prove(
  `!x. (\n. (((--(&1)) pow n) / &(FACT(2 * n)))
         * (x pow (2 * n))) sums (cos x)`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` COS_CONVERGES) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_PAIR) THEN REWRITE_TAC[GSYM cos] THEN
  BETA_TAC THEN REWRITE_TAC[SUM_2] THEN BETA_TAC THEN
  REWRITE_TAC[GSYM ADD1; EVEN_DOUBLE;
              REWRITE_RULE[GSYM NOT_EVEN] ODD_DOUBLE] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; MULT_DIV_2]);;

let COS_2 = prove(
  `cos(&2) < &0`,
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_NEGNEG] THEN
  REWRITE_TAC[REAL_NEG_LT0] THEN MP_TAC(SPEC `&2` COS_PAIRED) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_NEG) THEN BETA_TAC THEN
  DISCH_TAC THEN FIRST_ASSUM(SUBST1_TAC o MATCH_MP SUM_UNIQ) THEN
  MATCH_MP_TAC REAL_LT_TRANS THEN
  EXISTS_TAC `Sum(0,3) (\n. --((((--(&1)) pow n) / &(FACT(2 * n)))
                * (&2 pow (2 * n))))` THEN CONJ_TAC THENL
   [REWRITE_TAC[num_CONV `3`; Sum; SUM_2] THEN BETA_TAC THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; pow; FACT] THEN
    REWRITE_TAC[REAL_MUL_RID; POW_1; POW_2; GSYM REAL_NEG_RMUL] THEN
    IMP_SUBST_TAC REAL_DIV_REFL THEN REWRITE_TAC[REAL_NEGNEG; REAL_10] THEN
    NUM_REDUCE_TAC THEN REWRITE_TAC[num_CONV `4`; num_CONV `3`; FACT; pow] THEN
    REWRITE_TAC[SYM(num_CONV `4`); SYM(num_CONV `3`)] THEN
    REWRITE_TAC[num_CONV `2`; num_CONV `1`; FACT; pow] THEN
    REWRITE_TAC[SYM(num_CONV `1`); SYM(num_CONV `2`)] THEN
    REWRITE_TAC[REAL_MUL] THEN NUM_REDUCE_TAC THEN
    REWRITE_TAC[real_div; REAL_NEG_LMUL; REAL_NEGNEG; REAL_MUL_LID] THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL; REAL_ADD_ASSOC] THEN
    REWRITE_TAC[GSYM real_sub; REAL_SUB_LT] THEN
    SUBGOAL_THEN `inv(&2) * &4 = &1 + &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_EQ_LMUL_IMP THEN EXISTS_TAC `&2` THEN
      REWRITE_TAC[REAL_INJ] THEN NUM_REDUCE_TAC THEN
      REWRITE_TAC[REAL_ADD; REAL_MUL] THEN NUM_REDUCE_TAC THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN
      SUBGOAL_THEN `&2 * inv(&2) = &1` SUBST1_TAC THEN
      REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC REAL_MUL_RINV THEN
      REWRITE_TAC[REAL_INJ] THEN NUM_REDUCE_TAC;
      REWRITE_TAC[REAL_MUL_LID; REAL_ADD_ASSOC] THEN
      REWRITE_TAC[REAL_ADD_LINV; REAL_ADD_LID] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
      MATCH_MP_TAC REAL_LT_1 THEN REWRITE_TAC[REAL_LE; REAL_LT] THEN
      NUM_REDUCE_TAC]; ALL_TAC] THEN
  MATCH_MP_TAC SER_POS_LT_PAIR THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP SUM_SUMMABLE th]) THEN
  X_GEN_TAC `d:num` THEN BETA_TAC THEN
  REWRITE_TAC[POW_ADD; POW_MINUS1; REAL_MUL_RID] THEN
  REWRITE_TAC[num_CONV `3`; pow] THEN REWRITE_TAC[SYM(num_CONV `3`)] THEN
  REWRITE_TAC[POW_2; POW_1] THEN
  REWRITE_TAC[GSYM REAL_NEG_MINUS1; REAL_NEGNEG] THEN
  REWRITE_TAC[real_div; GSYM REAL_NEG_LMUL; GSYM REAL_NEG_RMUL] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_NEGNEG] THEN
  REWRITE_TAC[GSYM real_sub; REAL_SUB_LT] THEN
  REWRITE_TAC[GSYM ADD1; ADD_CLAUSES; MULT_CLAUSES] THEN
  REWRITE_TAC[POW_ADD; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LT_RMUL_IMP THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[num_CONV `2`; MULT_CLAUSES] THEN
    REWRITE_TAC[num_CONV `3`; ADD_CLAUSES] THEN
    MATCH_MP_TAC POW_POS_LT THEN REWRITE_TAC[REAL_LT] THEN
    NUM_REDUCE_TAC] THEN
  REWRITE_TAC[num_CONV `2`; ADD_CLAUSES; FACT] THEN
  REWRITE_TAC[SYM(num_CONV `2`)] THEN
  REWRITE_TAC[num_CONV `1`; ADD_CLAUSES; FACT] THEN
  REWRITE_TAC[SYM(num_CONV `1`)] THEN
  SUBGOAL_THEN `!n. &0 < &(SUC n)` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_LT; LT_0]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 < &(FACT n)` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_LT; FACT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. ~(&(SUC n) = &0)` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_INJ; NOT_SUC]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. ~(&(FACT n) = &0)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_POS_NZ THEN
    REWRITE_TAC[REAL_LT; FACT_LT]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL] THEN
  REPEAT(IMP_SUBST_TAC REAL_INV_MUL_WEAK THEN ASM_REWRITE_TAC[REAL_ENTIRE]) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC
    `a * b * c * d = (a * b * d) * c`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LT_RMUL_IMP THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_INV_POS THEN REWRITE_TAC[REAL_LT; FACT_LT]] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  IMP_SUBST_TAC ((CONV_RULE(RAND_CONV SYM_CONV) o SPEC_ALL) REAL_INV_MUL_WEAK) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_LT_1 THEN
  REWRITE_TAC[POW_2; REAL_MUL; REAL_LE; REAL_LT] THEN NUM_REDUCE_TAC THEN
  REWRITE_TAC[num_CONV `4`; num_CONV `3`; MULT_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[LT_SUC] THEN
  REWRITE_TAC[num_CONV `2`; ADD_CLAUSES; MULT_CLAUSES] THEN
  REWRITE_TAC[num_CONV `1`; LT_SUC; LT_0]);;

let COS_ISZERO = prove(
  `?!x. &0 <= x /\ x <= &2 /\ (cos x = &0)`,
  REWRITE_TAC[EXISTS_UNIQUE_DEF] THEN BETA_TAC THEN
  W(C SUBGOAL_THEN ASSUME_TAC o hd o conjuncts o snd) THENL
   [MATCH_MP_TAC IVT2 THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE; LE_0];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ACCEPT_TAC COS_2;
      REWRITE_TAC[COS_0; REAL_LE_01];
      X_GEN_TAC `x:real` THEN DISCH_THEN(K ALL_TAC) THEN
      MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC `--(sin x)` THEN
      REWRITE_TAC[DIFF_COS]];
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN
    MAP_EVERY X_GEN_TAC [`x1:real`; `x2:real`] THEN
    GEN_REWRITE_TAC I [TAUT `a = ~ ~a`] THEN
    PURE_REWRITE_TAC[NOT_IMP] THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`x1:real`; `x2:real`] REAL_LT_TOTAL) THEN
    SUBGOAL_THEN `(!x. cos differentiable x) /\
                  (!x. cos contl x)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN GEN_TAC THENL
       [REWRITE_TAC[differentiable]; MATCH_MP_TAC DIFF_CONT] THEN
      EXISTS_TAC `--(sin x)` THEN REWRITE_TAC[DIFF_COS]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN DISJ_CASES_TAC THENL
     [MP_TAC(SPECL [`cos`; `x1:real`; `x2:real`] ROLLE);
      MP_TAC(SPECL [`cos`; `x2:real`; `x1:real`] ROLLE)] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real` MP_TAC) THEN REWRITE_TAC[CONJ_ASSOC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o CONJ(SPEC `x:real` DIFF_COS)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_UNIQ) THEN
    REWRITE_TAC[REAL_NEG_EQ0] THEN MATCH_MP_TAC REAL_POS_NZ THEN
    MATCH_MP_TAC SIN_POS THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `x1:real` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `x2:real` THEN
        ASM_REWRITE_TAC[]];
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `x2:real` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `x1:real` THEN
        ASM_REWRITE_TAC[]]]]);;

let pi = new_definition
  `pi = &2 * @x. &0 <= x /\ x <= &2 /\ (cos x = &0)`;;

(* ------------------------------------------------------------------------ *)
(* Periodicity and related properties of the trig functions                 *)
(* ------------------------------------------------------------------------ *)

let PI2 = prove(
  `pi / &2 = @x. &0 <= x /\ x <= &2 /\ (cos(x) = &0)`,
  REWRITE_TAC[pi; real_div] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC
    `(a * b) * c = (c * a) * b`] THEN
  IMP_SUBST_TAC REAL_MUL_LINV THEN REWRITE_TAC[REAL_INJ] THEN
  NUM_REDUCE_TAC THEN REWRITE_TAC[REAL_MUL_LID]);;

let COS_PI2 = prove(
  `cos(pi / &2) = &0`,
  MP_TAC(SELECT_RULE (EXISTENCE COS_ISZERO)) THEN
  REWRITE_TAC[GSYM PI2] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let PI2_BOUNDS = prove(
  `&0 < (pi / &2) /\ (pi / &2) < &2`,
  MP_TAC(SELECT_RULE (EXISTENCE COS_ISZERO)) THEN
  REWRITE_TAC[GSYM PI2] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL
   [DISCH_TAC THEN MP_TAC COS_0 THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM REAL_10];
    DISCH_TAC THEN MP_TAC COS_PI2 THEN FIRST_ASSUM SUBST1_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
    MATCH_ACCEPT_TAC COS_2]);;

let PI_POS = prove(
  `&0 < pi`,
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_HALF_DOUBLE] THEN
  MATCH_MP_TAC REAL_LT_ADD THEN REWRITE_TAC[PI2_BOUNDS]);;

let SIN_PI2 = prove(
  `sin(pi / &2) = &1`,
  MP_TAC(SPEC `pi / &2` SIN_CIRCLE) THEN
  REWRITE_TAC[COS_PI2; POW_2; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_MUL_LID] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  REWRITE_TAC[GSYM REAL_DIFFSQ; REAL_ENTIRE] THEN
  DISCH_THEN DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[REAL_LNEG_UNIQ] THEN DISCH_THEN(MP_TAC o AP_TERM `--`) THEN
  REWRITE_TAC[REAL_NEGNEG] THEN DISCH_TAC THEN
  MP_TAC REAL_LT_01 THEN POP_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_GT THEN
  REWRITE_TAC[REAL_NEG_LT0] THEN MATCH_MP_TAC SIN_POS THEN
  REWRITE_TAC[PI2_BOUNDS]);;

let COS_PI = prove(
  `cos(pi) = --(&1)`,
  MP_TAC(SPECL [`pi / &2`; `pi / &2`] COS_ADD) THEN
  REWRITE_TAC[SIN_PI2; COS_PI2; REAL_MUL_LZERO; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_SUB_LZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN REWRITE_TAC[REAL_DOUBLE] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
  REWRITE_TAC[REAL_INJ] THEN NUM_REDUCE_TAC);;

let SIN_PI = prove(
  `sin(pi) = &0`,
  MP_TAC(SPECL [`pi / &2`; `pi / &2`] SIN_ADD) THEN
  REWRITE_TAC[COS_PI2; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_DOUBLE] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC REAL_DIV_LMUL THEN
  REWRITE_TAC[REAL_INJ] THEN NUM_REDUCE_TAC);;

let SIN_COS = prove(
  `!x. sin(x) = cos((pi / &2) - x)`,
  GEN_TAC THEN REWRITE_TAC[real_sub; COS_ADD] THEN
  REWRITE_TAC[SIN_PI2; COS_PI2; REAL_MUL_LZERO] THEN
  REWRITE_TAC[REAL_ADD_LID; REAL_MUL_LID] THEN
  REWRITE_TAC[SIN_NEG; REAL_NEGNEG]);;

let COS_SIN = prove(
  `!x. cos(x) = sin((pi / &2) - x)`,
  GEN_TAC THEN REWRITE_TAC[real_sub; SIN_ADD] THEN
  REWRITE_TAC[SIN_PI2; COS_PI2; REAL_MUL_LZERO] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_ADD_RID] THEN
  REWRITE_TAC[COS_NEG]);;

let SIN_PERIODIC_PI = prove(
  `!x. sin(x + pi) = --(sin(x))`,
  GEN_TAC THEN REWRITE_TAC[SIN_ADD; SIN_PI; COS_PI] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; GSYM REAL_NEG_RMUL] THEN
  REWRITE_TAC[REAL_MUL_RID]);;

let COS_PERIODIC_PI = prove(
  `!x. cos(x + pi) = --(cos(x))`,
  GEN_TAC THEN REWRITE_TAC[COS_ADD; SIN_PI; COS_PI] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO; GSYM REAL_NEG_RMUL] THEN
  REWRITE_TAC[REAL_MUL_RID]);;

let SIN_PERIODIC = prove(
  `!x. sin(x + (&2 * pi)) = sin(x)`,
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_DOUBLE; REAL_ADD_ASSOC] THEN
  REWRITE_TAC[SIN_PERIODIC_PI; REAL_NEGNEG]);;

let COS_PERIODIC = prove(
  `!x. cos(x + (&2 * pi)) = cos(x)`,
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_DOUBLE; REAL_ADD_ASSOC] THEN
  REWRITE_TAC[COS_PERIODIC_PI; REAL_NEGNEG]);;

let COS_NPI = prove(
  `!n. cos(&n * pi) = --(&1) pow n`,
  INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO; COS_0; pow] THEN
  REWRITE_TAC[ADD1; GSYM REAL_ADD; REAL_RDISTRIB; COS_ADD] THEN
  REWRITE_TAC[REAL_MUL_LID; SIN_PI; REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
  ASM_REWRITE_TAC[COS_PI] THEN
  MATCH_ACCEPT_TAC REAL_MUL_SYM);;

let SIN_NPI = prove(
  `!n. sin(&n * pi) = &0`,
  INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO; SIN_0; pow] THEN
  REWRITE_TAC[ADD1; GSYM REAL_ADD; REAL_RDISTRIB; SIN_ADD] THEN
  REWRITE_TAC[REAL_MUL_LID; SIN_PI; REAL_MUL_RZERO; REAL_ADD_RID] THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO]);;

let SIN_POS_PI2 = prove(
  `!x. &0 < x /\ x < pi / &2 ==> &0 < sin(x)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SIN_POS THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_TRANS THEN
  EXISTS_TAC `pi / &2` THEN ASM_REWRITE_TAC[PI2_BOUNDS]);;

let COS_POS_PI2 = prove(
  `!x. &0 < x /\ x < pi / &2 ==> &0 < cos(x)`,
  GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [TAUT `a = ~ ~a`] THEN
  PURE_REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cos`; `&0`; `x:real`; `&0`] IVT2) THEN
  ASM_REWRITE_TAC[COS_0; REAL_LE_01; NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `z:real` THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC `--(sin z)` THEN
    REWRITE_TAC[DIFF_COS];
    DISCH_THEN(X_CHOOSE_TAC `z:real`) THEN
    MP_TAC(CONJUNCT2 (CONV_RULE EXISTS_UNIQUE_CONV COS_ISZERO)) THEN
    DISCH_THEN(MP_TAC o SPECL [`z:real`; `pi / &2`]) THEN
    ASM_REWRITE_TAC[COS_PI2] THEN REWRITE_TAC[NOT_IMP] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `x:real` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `pi / &2` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC;
      ALL_TAC;
      ALL_TAC;
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `x < pi / &2` THEN
      ASM_REWRITE_TAC[REAL_NOT_LT]] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[PI2_BOUNDS]]);;

let COS_POS_PI = prove(
  `!x. --(pi / &2) < x /\ x < pi / &2 ==> &0 < cos(x)`,
  GEN_TAC THEN STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
        (SPECL [`x:real`; `&0`] REAL_LT_TOTAL) THENL
   [ASM_REWRITE_TAC[COS_0; REAL_LT_01];
    ONCE_REWRITE_TAC[GSYM COS_NEG] THEN MATCH_MP_TAC COS_POS_PI2 THEN
    ONCE_REWRITE_TAC[GSYM REAL_NEG_LT0] THEN ASM_REWRITE_TAC[REAL_NEGNEG] THEN
    ONCE_REWRITE_TAC[GSYM REAL_LT_NEG] THEN ASM_REWRITE_TAC[REAL_NEGNEG];
    MATCH_MP_TAC COS_POS_PI2 THEN ASM_REWRITE_TAC[]]);;

let SIN_POS_PI = prove(
  `!x. &0 < x /\ x < pi ==> &0 < sin(x)`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SIN_COS] THEN ONCE_REWRITE_TAC[GSYM COS_NEG] THEN
  REWRITE_TAC[REAL_NEG_SUB] THEN
  MATCH_MP_TAC COS_POS_PI THEN
  REWRITE_TAC[REAL_LT_SUB_LADD; REAL_LT_SUB_RADD] THEN
  ASM_REWRITE_TAC[REAL_HALF_DOUBLE; REAL_ADD_LINV]);;

let COS_TOTAL = prove(
  `!y. --(&1) <= y /\ y <= &1 ==> ?!x. &0 <= x /\ x <= pi /\ (cos(x) = y)`,
  GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC EXISTS_UNIQUE_CONV THEN CONJ_TAC THENL
   [MATCH_MP_TAC IVT2 THEN ASM_REWRITE_TAC[COS_0; COS_PI] THEN
    REWRITE_TAC[MATCH_MP REAL_LT_IMP_LE PI_POS] THEN
    GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC `--(sin x)` THEN
    REWRITE_TAC[DIFF_COS];
    MAP_EVERY X_GEN_TAC [`x1:real`; `x2:real`] THEN STRIP_TAC THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
         (SPECL [`x1:real`; `x2:real`] REAL_LT_TOTAL) THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MP_TAC(SPECL [`cos`; `x1:real`; `x2:real`] ROLLE);
      MP_TAC(SPECL [`cos`; `x2:real`; `x1:real`] ROLLE)]] THEN
  ASM_REWRITE_TAC[] THEN
  (W(C SUBGOAL_THEN (fun t -> REWRITE_TAC[t]) o funpow 2
                    (fst o dest_imp) o snd) THENL
    [CONJ_TAC THEN X_GEN_TAC `x:real` THEN DISCH_THEN(K ALL_TAC) THEN
     TRY(MATCH_MP_TAC DIFF_CONT) THEN REWRITE_TAC[differentiable] THEN
     EXISTS_TAC `--(sin x)` THEN REWRITE_TAC[DIFF_COS]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(cos diffl &0)(x)` THEN
  DISCH_THEN(MP_TAC o CONJ (SPEC `x:real` DIFF_COS)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_UNIQ) THEN
  REWRITE_TAC[REAL_NEG_EQ0] THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:real` SIN_POS_PI) THEN
  ASM_REWRITE_TAC[REAL_LT_REFL] THEN
  CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `x1:real`;
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `x2:real`;
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `x2:real`;
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `x1:real`] THEN
  ASM_REWRITE_TAC[]);;

let SIN_TOTAL = prove(
  `!y. --(&1) <= y /\ y <= &1 ==>
        ?!x.  --(pi / &2) <= x /\ x <= pi / &2 /\ (sin(x) = y)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x. --(pi / &2) <= x /\ x <= pi / &2 /\ (sin(x) = y) =
    &0 <= (x + pi / &2) /\ (x + pi / &2) <= pi /\ (cos(x + pi / &2) = --y)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[COS_ADD; SIN_PI2; COS_PI2] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RZERO; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_SUB_LZERO] THEN
    REWRITE_TAC[GSYM REAL_LE_SUB_RADD; GSYM REAL_LE_SUB_LADD] THEN
    REWRITE_TAC[REAL_SUB_LZERO] THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_EQ_NEG] THEN AP_THM_TAC THEN
    REPEAT AP_TERM_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM REAL_HALF_DOUBLE] THEN
    REWRITE_TAC[REAL_ADD_SUB]; ALL_TAC] THEN
  MP_TAC(SPEC `--y` COS_TOTAL) THEN ASM_REWRITE_TAC[REAL_LE_NEG] THEN
  ONCE_REWRITE_TAC[GSYM REAL_LE_NEG] THEN ASM_REWRITE_TAC[REAL_NEGNEG] THEN
  REWRITE_TAC[REAL_LE_NEG] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
  DISCH_THEN(prefix THEN CONJ_TAC o MP_TAC) THENL
   [DISCH_THEN(X_CHOOSE_TAC `x:real` o CONJUNCT1) THEN
    EXISTS_TAC `x - pi / &2` THEN ASM_REWRITE_TAC[REAL_SUB_ADD];
    POP_ASSUM(K ALL_TAC) THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    REWRITE_TAC[REAL_EQ_RADD]]);;

let COS_ZERO_LEMMA = prove(
  `!x. &0 <= x /\ (cos(x) = &0) ==>
      ?n. ~EVEN n /\ (x = &n * (pi / &2))`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `x:real` (MATCH_MP REAL_ARCH_LEAST PI_POS)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 <= x - &n * pi /\ (x - &n * pi) <= pi /\
                (cos(x - &n * pi) = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_LE] THEN
    REWRITE_TAC[REAL_LE_SUB_RADD] THEN
    REWRITE_TAC[real_sub; COS_ADD; SIN_NEG; COS_NEG; SIN_NPI; COS_NPI] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
    REWRITE_TAC[REAL_NEG_RMUL; REAL_NEGNEG; REAL_MUL_RZERO] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN UNDISCH_TAC `x < &(SUC n) * pi` THEN
    REWRITE_TAC[ADD1] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    REWRITE_TAC[GSYM REAL_ADD; REAL_RDISTRIB; REAL_MUL_LID];
    MP_TAC(SPEC `&0` COS_TOTAL) THEN
    REWRITE_TAC[REAL_LE_01; REAL_NEG_LE0] THEN
    DISCH_THEN(MP_TAC o CONV_RULE EXISTS_UNIQUE_CONV) THEN
    DISCH_THEN(MP_TAC o SPECL [`x - &n * pi`; `pi / &2`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[COS_PI2] THEN
    W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN MP_TAC PI2_BOUNDS THEN
      REWRITE_TAC[REAL_LT_HALF1; REAL_LT_HALF2] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    REWRITE_TAC[REAL_EQ_SUB_RADD] THEN DISCH_TAC THEN
    EXISTS_TAC `SUC(2 * n)` THEN
    REWRITE_TAC[GSYM NOT_ODD; ODD_DOUBLE] THEN
    REWRITE_TAC[ADD1; GSYM REAL_ADD; GSYM REAL_MUL] THEN
    REWRITE_TAC[REAL_RDISTRIB; REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    REWRITE_TAC[REAL_INJ] THEN NUM_REDUCE_TAC]);;

let SIN_ZERO_LEMMA = prove(
  `!x. &0 <= x /\ (sin(x) = &0) ==>
        ?n. EVEN n /\ (x = &n * (pi / &2))`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `x + pi / &2` COS_ZERO_LEMMA) THEN
  W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `x:real` THEN
      ASM_REWRITE_TAC[REAL_LE_ADDR] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      REWRITE_TAC[PI2_BOUNDS];
      ASM_REWRITE_TAC[COS_ADD; COS_PI2; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
      MATCH_ACCEPT_TAC REAL_SUB_REFL];
    DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `n:num` ODD_EXISTS) THEN ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  EXISTS_TAC `2 * m` THEN REWRITE_TAC[EVEN_DOUBLE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_EQ_SUB_LADD]) THEN
  FIRST_ASSUM SUBST1_TAC THEN
  REWRITE_TAC[ADD1; GSYM REAL_ADD; REAL_RDISTRIB; REAL_MUL_LID] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[REAL_ADD_SYM] REAL_ADD_SUB]);;

let COS_ZERO = prove(
  `!x. (cos(x) = &0) = (?n. ~EVEN n /\ (x = &n * (pi / &2))) \/
                       (?n. ~EVEN n /\ (x = --(&n * (pi / &2))))`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN DISJ_CASES_TAC (SPECL [`&0`; `x:real`] REAL_LE_TOTAL) THENL
     [DISJ1_TAC THEN MATCH_MP_TAC COS_ZERO_LEMMA THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN REWRITE_TAC[GSYM REAL_NEG_EQ] THEN
      MATCH_MP_TAC COS_ZERO_LEMMA THEN ASM_REWRITE_TAC[COS_NEG] THEN
      ONCE_REWRITE_TAC[GSYM REAL_LE_NEG] THEN
      ASM_REWRITE_TAC[REAL_NEGNEG; REAL_NEG_0]];
    DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_TAC `n:num`)) THEN
    ASM_REWRITE_TAC[COS_NEG] THEN MP_TAC(SPEC `n:num` ODD_EXISTS) THEN
    ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
    REWRITE_TAC[ADD1] THEN SPEC_TAC(`m:num`,`m:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; REAL_MUL_LID; COS_PI2] THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN ONCE_REWRITE_TAC[GSYM REAL_ADD] THEN
    REWRITE_TAC[REAL_RDISTRIB] THEN REWRITE_TAC[COS_ADD] THEN
    REWRITE_TAC[GSYM REAL_DOUBLE; REAL_HALF_DOUBLE] THEN
    ASM_REWRITE_TAC[COS_PI; SIN_PI; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
    REWRITE_TAC[REAL_SUB_RZERO]]);;

let SIN_ZERO = prove(
  `!x. (sin(x) = &0) = (?n. EVEN n /\ (x = &n * (pi / &2))) \/
                       (?n. EVEN n /\ (x = --(&n * (pi / &2))))`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN DISJ_CASES_TAC (SPECL [`&0`; `x:real`] REAL_LE_TOTAL) THENL
     [DISJ1_TAC THEN MATCH_MP_TAC SIN_ZERO_LEMMA THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN REWRITE_TAC[GSYM REAL_NEG_EQ] THEN
      MATCH_MP_TAC SIN_ZERO_LEMMA THEN
      ASM_REWRITE_TAC[SIN_NEG; REAL_NEG_0; REAL_NEG_GE0]];
    DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_TAC `n:num`)) THEN
    ASM_REWRITE_TAC[SIN_NEG; REAL_NEG_EQ0] THEN
    MP_TAC(SPEC `n:num` EVEN_EXISTS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
    REWRITE_TAC[GSYM REAL_MUL] THEN
    ONCE_REWRITE_TAC[AC REAL_MUL_AC
      `(a * b) * c = b * (a * c)`] THEN
    REWRITE_TAC[GSYM REAL_DOUBLE; REAL_HALF_DOUBLE; SIN_NPI]]);;

(* ------------------------------------------------------------------------ *)
(* Tangent                                                                  *)
(* ------------------------------------------------------------------------ *)

let tan = new_definition
  `tan(x) = sin(x) / cos(x)`;;

let TAN_0 = prove(
  `tan(&0) = &0`,
  REWRITE_TAC[tan; SIN_0; REAL_DIV_LZERO]);;

let TAN_PI = prove(
  `tan(pi) = &0`,
  REWRITE_TAC[tan; SIN_PI; REAL_DIV_LZERO]);;

let TAN_NPI = prove(
  `!n. tan(&n * pi) = &0`,
  GEN_TAC THEN REWRITE_TAC[tan; SIN_NPI; REAL_DIV_LZERO]);;

let TAN_NEG = prove(
  `!x. tan(--x) = --(tan x)`,
  GEN_TAC THEN REWRITE_TAC[tan; SIN_NEG; COS_NEG] THEN
  REWRITE_TAC[real_div; REAL_NEG_LMUL]);;

let TAN_PERIODIC = prove(
  `!x. tan(x + &2 * pi) = tan(x)`,
  GEN_TAC THEN REWRITE_TAC[tan; SIN_PERIODIC; COS_PERIODIC]);;

let TAN_ADD = prove(
  `!x y. ~(cos(x) = &0) /\ ~(cos(y) = &0) /\ ~(cos(x + y) = &0) ==>
           (tan(x + y) = (tan(x) + tan(y)) / (&1 - tan(x) * tan(y)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tan] THEN
  MP_TAC(SPECL [`cos(x) * cos(y)`;
                `&1 - (sin(x) / cos(x)) * (sin(y) / cos(y))`]
         REAL_DIV_MUL2) THEN ASM_REWRITE_TAC[REAL_ENTIRE] THEN
  W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
   [DISCH_THEN(MP_TAC o AP_TERM `(*) (cos(x) * cos(y))`) THEN
    REWRITE_TAC[real_div; REAL_SUB_LDISTRIB; GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO] THEN
    UNDISCH_TAC `~(cos(x + y) = &0)` THEN
    MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[COS_ADD] THEN AP_TERM_TAC;
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN BINOP_TAC THENL
     [REWRITE_TAC[real_div; REAL_LDISTRIB; GSYM REAL_MUL_ASSOC] THEN
      REWRITE_TAC[SIN_ADD] THEN BINOP_TAC THENL
       [ONCE_REWRITE_TAC[AC REAL_MUL_AC
          `a * b * c * d = (d * a) * (c * b)`] THEN
        IMP_SUBST_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[REAL_MUL_LID];
        ONCE_REWRITE_TAC[AC REAL_MUL_AC
          `a * b * c * d = (d * b) * (a * c)`] THEN
        IMP_SUBST_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[REAL_MUL_LID]];
      REWRITE_TAC[COS_ADD; REAL_SUB_LDISTRIB; REAL_MUL_RID] THEN
      AP_TERM_TAC THEN REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC]]] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC
    `a * b * c * d * e * f = (f * b) * (d * a) * (c * e)`] THEN
  REPEAT(IMP_SUBST_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[REAL_MUL_LID]);;

let TAN_DOUBLE = prove(
  `!x. ~(cos(x) = &0) /\ ~(cos(&2 * x) = &0) ==>
            (tan(&2 * x) = (&2 * tan(x)) / (&1 - (tan(x) pow 2)))`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `x:real`] TAN_ADD) THEN
  ASM_REWRITE_TAC[REAL_DOUBLE; POW_2]);;

let TAN_POS_PI2 = prove(
  `!x. &0 < x /\ x < pi / &2 ==> &0 < tan(x)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[tan; real_div] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SIN_POS_PI2;
    MATCH_MP_TAC REAL_INV_POS THEN MATCH_MP_TAC COS_POS_PI2] THEN
  ASM_REWRITE_TAC[]);;

let DIFF_TAN = prove(
  `!x. ~(cos(x) = &0) ==> (tan diffl inv(cos(x) pow 2))(x)`,
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(DIFF_CONV `\x. sin(x) / cos(x)`) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[REAL_MUL_RID] THEN
  REWRITE_TAC[GSYM tan; GSYM REAL_NEG_LMUL; REAL_NEGNEG; real_sub] THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[GSYM POW_2; SIN_CIRCLE; GSYM REAL_INV_1OVER]);;

let TAN_TOTAL_LEMMA = prove(
  `!y. &0 < y ==> ?x. &0 < x /\ x < pi / &2 /\ y < tan(x)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `((\x. cos(x) / sin(x)) tends_real_real &0)(pi / &2)`
  MP_TAC THENL
   [SUBST1_TAC(SYM(SPEC `&1` REAL_DIV_LZERO)) THEN
    CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN MATCH_MP_TAC LIM_DIV THEN
    REWRITE_TAC[REAL_10] THEN CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
    SUBST1_TAC(SYM COS_PI2) THEN SUBST1_TAC(SYM SIN_PI2) THEN
    REWRITE_TAC[GSYM CONTL_LIM] THEN CONJ_TAC THEN MATCH_MP_TAC DIFF_CONT THENL
     [EXISTS_TAC `--(sin(pi / &2))`;
      EXISTS_TAC `cos(pi / &2)`] THEN
    REWRITE_TAC[DIFF_SIN; DIFF_COS]; ALL_TAC] THEN
  REWRITE_TAC[LIM] THEN DISCH_THEN(MP_TAC o SPEC `inv(y)`) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_INV_POS th]) THEN
  BETA_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`d:real`; `pi / &2`] REAL_DOWN2) THEN
  ASM_REWRITE_TAC[PI2_BOUNDS] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(pi / &2) - e` THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[real_sub; GSYM REAL_NOT_LE; REAL_LE_ADDR; REAL_NEG_GE0] THEN
    ASM_REWRITE_TAC[REAL_NOT_LE]; ALL_TAC] THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
  DISCH_THEN(MP_TAC o SPEC `(pi / &2) - e`) THEN
  REWRITE_TAC[REAL_SUB_SUB; ABS_NEG] THEN
  SUBGOAL_THEN `abs(e) = e` (fun th -> ASM_REWRITE_TAC[th]) THENL
   [REWRITE_TAC[ABS_REFL] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < cos((pi / &2) - e) / sin((pi / &2) - e)`
  MP_TAC THENL
   [ONCE_REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC COS_POS_PI2;
      MATCH_MP_TAC REAL_INV_POS THEN MATCH_MP_TAC SIN_POS_PI2] THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE; real_sub; REAL_LE_ADDR; REAL_NEG_GE0] THEN
    ASM_REWRITE_TAC[REAL_NOT_LE]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC(MATCH_MP REAL_POS_NZ th)) THEN
  REWRITE_TAC[ABS_NZ; TAUT `a ==> b ==> c = a /\ b ==> c`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_INV2) THEN REWRITE_TAC[tan] THEN
  MATCH_MP_TAC (TAUT `(a = b) ==> a ==> b`) THEN BINOP_TAC THENL
   [MATCH_MP_TAC REAL_INVINV THEN MATCH_MP_TAC REAL_POS_NZ THEN
    FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ASSUME `&0 < cos((pi / &2) - e) / sin((pi / &2) - e)`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  REWRITE_TAC[GSYM ABS_REFL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[real_div] THEN IMP_SUBST_TAC REAL_INV_MUL_WEAK THENL
   [REWRITE_TAC[GSYM DE_MORGAN_THM; GSYM REAL_ENTIRE; GSYM real_div] THEN
    MATCH_MP_TAC REAL_POS_NZ THEN FIRST_ASSUM ACCEPT_TAC;
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC REAL_INVINV THEN MATCH_MP_TAC REAL_POS_NZ THEN
    MATCH_MP_TAC SIN_POS_PI2 THEN REWRITE_TAC[REAL_SUB_LT; GSYM real_div] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE; real_sub; REAL_LE_ADDR; REAL_NEG_GE0] THEN
    ASM_REWRITE_TAC[REAL_NOT_LE]]);;

let TAN_TOTAL_POS = prove(
  `!y. &0 <= y ==> ?x. &0 <= x /\ x < pi / &2 /\ (tan(x) = y)`,
  GEN_TAC THEN DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP TAN_TOTAL_LEMMA) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`tan`; `&0`; `x:real`; `y:real`] IVT) THEN
    W(C SUBGOAL_THEN (fun th -> DISCH_THEN(MP_TAC o C MATCH_MP th)) o
         funpow 2 (fst o dest_imp) o snd) THENL
     [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LT_IMP_LE) THEN
      ASM_REWRITE_TAC[TAN_0] THEN X_GEN_TAC `z:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC `inv(cos(z) pow 2)` THEN
      MATCH_MP_TAC DIFF_TAN THEN UNDISCH_TAC `&0 <= z` THEN
      REWRITE_TAC[REAL_LE_LT] THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
       [DISCH_TAC THEN MATCH_MP_TAC REAL_POS_NZ THEN
        MATCH_MP_TAC COS_POS_PI2 THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `x:real` THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[COS_0; REAL_10]];
      DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `z:real` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `x:real` THEN
      ASM_REWRITE_TAC[]];
    POP_ASSUM(SUBST1_TAC o SYM) THEN EXISTS_TAC `&0` THEN
    REWRITE_TAC[TAN_0; REAL_LE_REFL; PI2_BOUNDS]]);;

let TAN_TOTAL = prove(
  `!y. ?!x. --(pi / &2) < x /\ x < (pi / &2) /\ (tan(x) = y)`,
  GEN_TAC THEN CONV_TAC EXISTS_UNIQUE_CONV THEN CONJ_TAC THENL
   [DISJ_CASES_TAC(SPEC `y:real` REAL_LE_NEGTOTAL) THEN
    POP_ASSUM(X_CHOOSE_TAC `x:real` o MATCH_MP TAN_TOTAL_POS) THENL
     [EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&0` THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM REAL_LT_NEG] THEN
      REWRITE_TAC[REAL_NEGNEG; REAL_NEG_0; PI2_BOUNDS];
      EXISTS_TAC `--x` THEN ASM_REWRITE_TAC[REAL_LT_NEG] THEN
      ASM_REWRITE_TAC[TAN_NEG; REAL_NEG_EQ; REAL_NEGNEG] THEN
      ONCE_REWRITE_TAC[GSYM REAL_LT_NEG] THEN
      REWRITE_TAC[REAL_LT_NEG] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[REAL_LE_NEGL]];
    MAP_EVERY X_GEN_TAC [`x1:real`; `x2:real`] THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
         (SPECL [`x1:real`; `x2:real`] REAL_LT_TOTAL) THENL
     [DISCH_THEN(K ALL_TAC) THEN POP_ASSUM ACCEPT_TAC;
      ALL_TAC;
      POP_ASSUM MP_TAC THEN SPEC_TAC(`x1:real`,`z1:real`) THEN
      SPEC_TAC(`x2:real`,`z2:real`) THEN
      MAP_EVERY X_GEN_TAC [`x1:real`; `x2:real`] THEN DISCH_TAC THEN
      CONV_TAC(RAND_CONV SYM_CONV) THEN ONCE_REWRITE_TAC[CONJ_SYM]] THEN
    (STRIP_TAC THEN MP_TAC(SPECL [`tan`; `x1:real`; `x2:real`] ROLLE) THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC CONTRAPOS_CONV THEN
     DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[NOT_IMP] THEN
     REPEAT CONJ_TAC THENL
      [X_GEN_TAC `x:real` THEN STRIP_TAC THEN MATCH_MP_TAC DIFF_CONT THEN
       EXISTS_TAC `inv(cos(x) pow 2)` THEN MATCH_MP_TAC DIFF_TAN;
       X_GEN_TAC `x:real` THEN
       DISCH_THEN(CONJUNCTS_THEN (ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE)) THEN
       REWRITE_TAC[differentiable] THEN EXISTS_TAC `inv(cos(x) pow 2)` THEN
       MATCH_MP_TAC DIFF_TAN;
       REWRITE_TAC[CONJ_ASSOC] THEN DISCH_THEN(X_CHOOSE_THEN `x:real`
         (CONJUNCTS_THEN2 (CONJUNCTS_THEN (ASSUME_TAC o MATCH_MP
          REAL_LT_IMP_LE)) ASSUME_TAC)) THEN
       MP_TAC(SPEC `x:real` DIFF_TAN) THEN
       SUBGOAL_THEN `~(cos(x) = &0)` ASSUME_TAC THENL
        [ALL_TAC;
         ASM_REWRITE_TAC[] THEN
         DISCH_THEN(MP_TAC o C CONJ (ASSUME `(tan diffl &0)(x)`)) THEN
         DISCH_THEN(MP_TAC o MATCH_MP DIFF_UNIQ) THEN REWRITE_TAC[] THEN
         MATCH_MP_TAC REAL_INV_NZ THEN MATCH_MP_TAC POW_NZ THEN
         ASM_REWRITE_TAC[]]] THEN
     (MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC COS_POS_PI THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `x1:real`;
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `x2:real`] THEN
     ASM_REWRITE_TAC[]))]);;

(* ------------------------------------------------------------------------ *)
(* Inverse trig functions                                                   *)
(* ------------------------------------------------------------------------ *)

let asn = new_definition
  `asn(y) = @x. --(pi / &2) <= x /\ x <= pi / &2 /\ (sin x = y)`;;

let acs = new_definition
  `acs(y) = @x. &0 <= x /\ x <= pi /\ (cos x = y)`;;

let atn = new_definition
  `atn(y) = @x. --(pi / &2) < x /\ x < pi / &2 /\ (tan x = y)`;;

let ASN = prove(
  `!y. --(&1) <= y /\ y <= &1 ==>
     --(pi / &2) <= asn(y) /\ asn(y) <= pi / &2 /\ (sin(asn y) = y)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP SIN_TOTAL) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[GSYM asn]);;

let ASN_SIN = prove(
  `!y. --(&1) <= y /\ y <= &1 ==> (sin(asn(y)) = y)`,
  GEN_TAC THEN DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP ASN th]));;

let ASN_BOUNDS = prove(
  `!y. --(&1) <= y /\ y <= &1 ==> --(pi / &2) <= asn(y) /\ asn(y) <= pi / &2`,
  GEN_TAC THEN DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP ASN th]));;

let ASN_BOUNDS_LT = prove(
  `!y. --(&1) < y /\ y < &1 ==> --(pi / &2) < asn(y) /\ asn(y) < pi / &2`,
  GEN_TAC THEN STRIP_TAC THEN
  EVERY_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  MP_TAC(SPEC `y:real` ASN_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_LT_LE] THEN
  CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `sin`) THEN
  IMP_SUBST_TAC ASN_SIN THEN ASM_REWRITE_TAC[SIN_NEG; SIN_PI2] THEN
  DISCH_THEN(prefix THEN (POP_ASSUM_LIST (MP_TAC o end_itlist CONJ)) o
    ASSUME_TAC) THEN ASM_REWRITE_TAC[REAL_LT_REFL]);;

let SIN_ASN = prove(
  `!x. --(pi / &2) <= x /\ x <= pi / &2 ==> (asn(sin(x)) = x)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(MATCH_MP SIN_TOTAL (SPEC `x:real` SIN_BOUNDS)) THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ASN THEN
  MATCH_ACCEPT_TAC SIN_BOUNDS);;

let ACS = prove(
  `!y. --(&1) <= y /\ y <= &1 ==>
     &0 <= acs(y) /\ acs(y) <= pi  /\ (cos(acs y) = y)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP COS_TOTAL) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[GSYM acs]);;

let ACS_COS = prove(
  `!y. --(&1) <= y /\ y <= &1 ==> (cos(acs(y)) = y)`,
  GEN_TAC THEN DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP ACS th]));;

let ACS_BOUNDS = prove(
  `!y. --(&1) <= y /\ y <= &1 ==> &0 <= acs(y) /\ acs(y) <= pi`,
  GEN_TAC THEN DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP ACS th]));;

let ACS_BOUNDS_LT = prove(
  `!y. --(&1) < y /\ y < &1 ==> &0 < acs(y) /\ acs(y) < pi`,
  GEN_TAC THEN STRIP_TAC THEN
  EVERY_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  MP_TAC(SPEC `y:real` ACS_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_LT_LE] THEN
  CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `cos`) THEN
  IMP_SUBST_TAC ACS_COS THEN ASM_REWRITE_TAC[COS_0; COS_PI] THEN
  DISCH_THEN(prefix THEN (POP_ASSUM_LIST (MP_TAC o end_itlist CONJ)) o
    ASSUME_TAC) THEN ASM_REWRITE_TAC[REAL_LT_REFL]);;

let COS_ACS = prove(
  `!x. &0 <= x /\ x <= pi ==> (acs(cos(x)) = x)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(MATCH_MP COS_TOTAL (SPEC `x:real` COS_BOUNDS)) THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ACS THEN
  MATCH_ACCEPT_TAC COS_BOUNDS);;

let ATN = prove(
  `!y. --(pi / &2) < atn(y) /\ atn(y) < (pi / &2) /\ (tan(atn y) = y)`,
  GEN_TAC THEN MP_TAC(SPEC `y:real` TAN_TOTAL) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[GSYM atn]);;

let ATN_TAN = prove(
  `!y. tan(atn y) = y`,
  REWRITE_TAC[ATN]);;

let ATN_BOUNDS = prove(
  `!y. --(pi / &2) < atn(y) /\ atn(y) < (pi / &2)`,
  REWRITE_TAC[ATN]);;

let TAN_ATN = prove(
  `!x. --(pi / &2) < x /\ x < (pi / &2) ==> (atn(tan(x)) = x)`,
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC `tan(x)` TAN_TOTAL) THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  ASM_REWRITE_TAC[ATN]);;

(* ------------------------------------------------------------------------- *)
(* Differentiation of arctan.                                                *)
(* ------------------------------------------------------------------------- *)

let COS_ATN_NZ = prove(
  `!x. ~(cos(atn(x)) = &0)`,
  GEN_TAC THEN REWRITE_TAC[COS_ZERO; DE_MORGAN_THM] THEN CONJ_TAC THEN
  CONV_TAC NOT_EXISTS_CONV THEN X_GEN_TAC `n:num` THEN
  STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  REWRITE_TAC[EVEN; DE_MORGAN_THM] THEN DISJ2_TAC THEN
  DISCH_TAC THEN MP_TAC(SPEC `x:real` ATN_BOUNDS) THEN
  ASM_REWRITE_TAC[DE_MORGAN_THM] THENL
   [DISJ2_TAC; DISJ1_TAC THEN REWRITE_TAC[REAL_LT_NEG]] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)  [GSYM REAL_MUL_LID] THEN
  REWRITE_TAC[MATCH_MP REAL_LT_RMUL_EQ (CONJUNCT1 PI2_BOUNDS)] THEN
  REWRITE_TAC[ADD1; GSYM REAL_ADD; REAL_NOT_LT] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[REAL_LE_ADDR; REAL_LE; LE_0]);;

let TAN_SEC = prove(
  `!x. ~(cos(x) = &0) ==> (&1 + (tan(x) pow 2) = inv(cos x) pow 2)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[tan] THEN
  FIRST_ASSUM(fun th ->  ONCE_REWRITE_TAC[GSYM
   (MATCH_MP REAL_DIV_REFL (SPEC `2` (MATCH_MP POW_NZ th)))]) THEN
  REWRITE_TAC[real_div; POW_MUL] THEN
  POP_ASSUM(fun th ->  REWRITE_TAC[MATCH_MP POW_INV th]) THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[GSYM REAL_RDISTRIB; SIN_CIRCLE; REAL_MUL_LID]);;

let DIFF_ATN = prove(
  `!x. (atn diffl (inv(&1 + (x pow 2))))(x)`,
  GEN_TAC THEN
  SUBGOAL_THEN `(atn diffl (inv(&1 + (x pow 2))))(tan(atn x))`
  MP_TAC THENL [MATCH_MP_TAC DIFF_INVERSE_LT; REWRITE_TAC[ATN_TAN]] THEN
  SUBGOAL_THEN
    `?d. &0 < d /\
         !z. abs(z - atn(x)) < d ==>  (--(pi / (& 2))) < z /\ z < (pi / (& 2))`
  (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THENL
   [ONCE_REWRITE_TAC[ABS_SUB] THEN MATCH_MP_TAC INTERVAL_LEMMA_LT THEN
    MATCH_ACCEPT_TAC ATN_BOUNDS;
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC TAN_ATN THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC `inv(cos(z) pow 2)` THEN
      MATCH_MP_TAC DIFF_TAN THEN MATCH_MP_TAC REAL_POS_NZ THEN
      MATCH_MP_TAC COS_POS_PI THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ASSUME_TAC(SPEC `x:real` COS_ATN_NZ) THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP DIFF_TAN) THEN
      FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP TAN_SEC) THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP POW_INV) THEN
      ASM_REWRITE_TAC[ATN_TAN];
      UNDISCH_TAC `&1 + (x pow 2) = &0` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POS_NZ THEN
      MATCH_MP_TAC REAL_LTE_ADD THEN
      REWRITE_TAC[REAL_LT_01; REAL_LE_SQUARE; POW_2]]]);;

(* ------------------------------------------------------------------------- *)
(* Differentiation of arcsin.                                                *)
(* ------------------------------------------------------------------------- *)

let COS_SIN_SQRT = prove(
  `!x. &0 <= cos(x) ==> (cos(x) = sqrt(&1 - (sin(x) pow 2)))`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (ONCE_REWRITE_RULE[REAL_ADD_SYM] (SPEC `x:real` SIN_CIRCLE)) THEN
  REWRITE_TAC[GSYM REAL_EQ_SUB_LADD] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[sqrt; num_CONV `2`] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC POW_ROOT_POS THEN
  ASM_REWRITE_TAC[]);;

let COS_ASN_NZ = prove(
  `!x. --(&1) < x /\ x < &1 ==> ~(cos(asn(x)) = &0)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ASN_BOUNDS_LT) THEN
  REWRITE_TAC[COS_ZERO; DE_MORGAN_THM] THEN
  CONJ_TAC THEN CONV_TAC NOT_EXISTS_CONV THEN
  X_GEN_TAC `n:num` THEN STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  REWRITE_TAC[EVEN] THEN STRIP_TAC THENL
   [UNDISCH_TAC `asn(x) < (pi / &2)` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `--(pi / &2) < asn(x)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_LT_NEG]] THEN
  REWRITE_TAC[ADD1; GSYM REAL_ADD; REAL_RDISTRIB; REAL_MUL_LID] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE; REAL_LE_ADDL] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE; LE_0] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[PI2_BOUNDS]);;

let DIFF_ASN_COS = prove(
  `!x. --(&1) < x /\ x < &1 ==> (asn diffl (inv(cos(asn x))))(x)`,
  REPEAT STRIP_TAC THEN
  EVERY_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  MP_TAC(SPEC `x:real` ASN_SIN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(fun th ->  GEN_REWRITE_TAC RAND_CONV  [GSYM th]) THEN
  MATCH_MP_TAC DIFF_INVERSE_LT THEN
  MP_TAC(SPEC `x:real` ASN_BOUNDS_LT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th ->  STRIP_ASSUME_TAC th THEN
    MP_TAC(MATCH_MP INTERVAL_LEMMA_LT th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(ASSUME_TAC o ONCE_REWRITE_RULE[ABS_SUB]) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SIN_ASN THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPEC `z:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC `cos(z)` THEN
    REWRITE_TAC[DIFF_SIN];
    REWRITE_TAC[DIFF_SIN];
    POP_ASSUM MP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC COS_ASN_NZ THEN
    ASM_REWRITE_TAC[]]);;

let DIFF_ASN = prove(
  `!x. --(&1) < x /\ x < &1 ==> (asn diffl (inv(sqrt(&1 - (x pow 2)))))(x)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIFF_ASN_COS) THEN
  MATCH_MP_TAC (TAUT `(a = b) ==> a ==> b`) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `sin(asn x) = x` MP_TAC THENL
   [MATCH_MP_TAC ASN_SIN THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th ->  GEN_REWRITE_TAC
      (RAND_CONV o ONCE_DEPTH_CONV)  [GSYM th]) THEN
    MATCH_MP_TAC COS_SIN_SQRT THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP ASN_BOUNDS_LT) THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC COS_POS_PI THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Differentiation of arccos.                                                *)
(* ------------------------------------------------------------------------- *)

let SIN_COS_SQRT = prove(
  `!x. &0 <= sin(x) ==> (sin(x) = sqrt(&1 - (cos(x) pow 2)))`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (SPEC `x:real` SIN_CIRCLE) THEN
  REWRITE_TAC[GSYM REAL_EQ_SUB_LADD] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[sqrt; num_CONV `2`] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC POW_ROOT_POS THEN
  ASM_REWRITE_TAC[]);;

let SIN_ACS_NZ = prove(
  `!x. --(&1) < x /\ x < &1 ==> ~(sin(acs(x)) = &0)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ACS_BOUNDS_LT) THEN
  REWRITE_TAC[SIN_ZERO; REAL_NEG_EQ0] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN
  CONJ_TAC THEN CONV_TAC NOT_EXISTS_CONV THEN
  (INDUCT_TAC THENL
    [REWRITE_TAC[REAL_MUL_LZERO; EVEN; REAL_NEG_0] THEN
     DISCH_THEN SUBST_ALL_TAC THEN
     RULE_ASSUM_TAC(REWRITE_RULE[REAL_LT_REFL]) THEN
     CONTR_TAC(ASSUME `F`); ALL_TAC] THEN
   SPEC_TAC(`n:num`,`n:num`) THEN REWRITE_TAC[EVEN] THEN
   INDUCT_TAC THEN REWRITE_TAC[EVEN] THEN STRIP_TAC) THENL
    [UNDISCH_TAC `acs(x) < pi` THEN
     ASM_REWRITE_TAC[ADD1; GSYM REAL_ADD; REAL_RDISTRIB] THEN
     REWRITE_TAC[REAL_MUL_LID; GSYM REAL_ADD_ASSOC] THEN
     REWRITE_TAC[REAL_HALF_DOUBLE] THEN
     REWRITE_TAC[GSYM REAL_NOT_LE; REAL_LE_ADDL] THEN
     MATCH_MP_TAC REAL_LE_MUL THEN
     REWRITE_TAC[REAL_LE; LE_0] THEN
     MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[PI2_BOUNDS];
     UNDISCH_TAC `&0 < acs(x)` THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[REAL_NOT_LT] THEN ONCE_REWRITE_TAC[GSYM REAL_LE_NEG] THEN
     REWRITE_TAC[REAL_NEGNEG; REAL_NEG_LMUL; REAL_NEG_0] THEN
     MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE; LE_0] THEN
     MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[PI2_BOUNDS]]);;

let DIFF_ACS_SIN = prove(
  `!x. --(&1) < x /\ x < &1 ==> (acs diffl (inv(--(sin(acs x)))))(x)`,
  REPEAT STRIP_TAC THEN
  EVERY_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  MP_TAC(SPEC `x:real` ACS_COS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(fun th ->  GEN_REWRITE_TAC RAND_CONV  [GSYM th]) THEN
  MATCH_MP_TAC DIFF_INVERSE_LT THEN
  MP_TAC(SPEC `x:real` ACS_BOUNDS_LT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th ->  STRIP_ASSUME_TAC th THEN
    MP_TAC(MATCH_MP INTERVAL_LEMMA_LT th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(ASSUME_TAC o ONCE_REWRITE_RULE[ABS_SUB]) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC COS_ACS THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPEC `z:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC `--(sin(z))` THEN
    REWRITE_TAC[DIFF_COS];
    REWRITE_TAC[DIFF_COS];
    POP_ASSUM MP_TAC THEN REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EQ_NEG] THEN
    REWRITE_TAC[REAL_NEGNEG; REAL_NEG_0] THEN
    MATCH_MP_TAC SIN_ACS_NZ THEN ASM_REWRITE_TAC[]]);;

let DIFF_ACS = prove(
  `!x. --(&1) < x /\ x < &1 ==> (acs diffl --(inv(sqrt(&1 - (x pow 2)))))(x)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIFF_ACS_SIN) THEN
  MATCH_MP_TAC (TAUT `(a = b) ==> a ==> b`) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  IMP_SUBST_TAC (GSYM REAL_NEG_INV) THENL
   [CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC SIN_ACS_NZ THEN ASM_REWRITE_TAC[];
    REPEAT AP_TERM_TAC] THEN
  SUBGOAL_THEN `cos(acs x) = x` MP_TAC THENL
   [MATCH_MP_TAC ACS_COS THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th ->  GEN_REWRITE_TAC
      (RAND_CONV o ONCE_DEPTH_CONV)  [GSYM th]) THEN
    MATCH_MP_TAC SIN_COS_SQRT THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP ACS_BOUNDS_LT) THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC SIN_POS_PI THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Back to normal service!                                                   *)
(* ------------------------------------------------------------------------- *)

extend_basic_rewrites [BETA_THM];;

(* ======================================================================== *)
(* Formalization of Kurzweil-Henstock gauge integral                        *)
(* ======================================================================== *)

let LE_MATCH_TAC th (asl,w) =
  let thi = PART_MATCH (rand o rator) th (rand(rator w)) in
  let tm = rand(concl thi) in
  (MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC tm THEN CONJ_TAC THENL
    [MATCH_ACCEPT_TAC th; ALL_TAC]) (asl,w);;

(* ------------------------------------------------------------------------ *)
(* Some miscellaneous lemmas                                                *)
(* ------------------------------------------------------------------------ *)

let LESS_SUC_EQ = prove(
  `!m n. m < SUC n = m <= n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJUNCT2 LT; LE_LT] THEN
  EQ_TAC THEN DISCH_THEN(DISJ_CASES_THEN(fun th -> REWRITE_TAC[th])));;

let LESS_1 = prove(
  `!n. n < 1 = (n = 0)`,
  REWRITE_TAC[num_CONV `1`; LESS_SUC_EQ; CONJUNCT1 LE]);;

(* ------------------------------------------------------------------------ *)
(* Divisions and tagged divisions etc.                                      *)
(* ------------------------------------------------------------------------ *)

let division = new_definition
  `division(a,b) D =
     (D 0 = a) /\
     (?N. (!n. n < N ==> D(n) < D(SUC n)) /\
          (!n. n >= N ==> (D(n) = b)))`;;

let dsize = new_definition
  `dsize D =
      @N. (!n. n < N ==> D(n) < D(SUC n)) /\
          (!n. n >= N ==> (D(n) = D(N)))`;;

let tdiv = new_definition
  `tdiv(a,b) (D,p) =
     division(a,b) D /\
     (!n. D(n) <= p(n) /\ p(n) <= D(SUC n))`;;

(* ------------------------------------------------------------------------ *)
(* Gauges and gauge-fine divisions                                          *)
(* ------------------------------------------------------------------------ *)

let gauge = new_definition
  `gauge(E) (g:real->real) = !x. E x ==> &0 < g(x)`;;

let fine = new_definition
  `fine(g:real->real) (D,p) =
     !n. n < (dsize D) ==> (D(SUC n) - D(n)) < g(p(n))`;;

(* ------------------------------------------------------------------------ *)
(* Riemann sum                                                              *)
(* ------------------------------------------------------------------------ *)

let rsum = new_definition
  `rsum (D,(p:num->real)) f =
        Sum(0,dsize(D))(\n. f(p n) * (D(SUC n) - D(n)))`;;

(* ------------------------------------------------------------------------ *)
(* Gauge integrability (definite)                                           *)
(* ------------------------------------------------------------------------ *)

let Dint = new_definition
  `Dint(a,b) f k =
     !e. &0 < e ==>
        ?g. gauge(\x. a <= x /\ x <= b) g /\
            !D p. tdiv(a,b) (D,p) /\ fine(g)(D,p) ==>
                abs(rsum(D,p) f - k) < e`;;

(* ------------------------------------------------------------------------ *)
(* Useful lemmas about the size of `trivial` divisions etc.                 *)
(* ------------------------------------------------------------------------ *)

let DIVISION_0 = prove(
  `!a b. (a = b) ==> (dsize(\n. (n = 0) => a | b) = 0)`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[COND_ID] THEN
  REWRITE_TAC[dsize] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `n:num` THEN BETA_TAC THEN
  REWRITE_TAC[REAL_LT_REFL; NOT_LT] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[CONJUNCT1 LE];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LE_0]]);;

let DIVISION_1 = prove(
  `!a b. a < b ==> (dsize(\n. (n = 0) => a | b) = 1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[dsize] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `n:num` THEN BETA_TAC THEN
  REWRITE_TAC[NOT_SUC] THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC LESS_EQUAL_ANTISYM THEN CONJ_TAC THENL
     [POP_ASSUM(MP_TAC o SPEC `1` o CONJUNCT1) THEN
      REWRITE_TAC[ARITH] THEN
      REWRITE_TAC[REAL_LT_REFL; NOT_LT];
      POP_ASSUM(MP_TAC o SPEC `2` o CONJUNCT2) THEN
      REWRITE_TAC[num_CONV `2`; GE] THEN
      CONV_TAC CONTRAPOS_CONV THEN
      REWRITE_TAC[num_CONV `1`; NOT_SUC_LESS_EQ; CONJUNCT1 LE] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NOT_SUC; NOT_IMP] THEN
      REWRITE_TAC[LE_0] THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN POP_ASSUM ACCEPT_TAC];
    DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[num_CONV `1`; CONJUNCT2 LT; NOT_LESS_0] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `n:num` THEN REWRITE_TAC[GE; num_CONV `1`] THEN
      ASM_CASES_TAC `n = 0` THEN
      ASM_REWRITE_TAC[CONJUNCT1 LE; GSYM NOT_SUC; NOT_SUC]]]);;

let DIVISION_SINGLE = prove(
  `!a b. a <= b ==> division(a,b)(\n. (n = 0) => a | b)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[division] THEN
  BETA_TAC THEN REWRITE_TAC[] THEN
  POP_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [EXISTS_TAC `1` THEN CONJ_TAC THEN X_GEN_TAC `n:num` THENL
     [REWRITE_TAC[LESS_1] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[NOT_SUC];
      REWRITE_TAC[GE] THEN
      LCOND_CASES_TAC THEN ASM_REWRITE_TAC[num_CONV `1`] THEN
      REWRITE_TAC[GSYM NOT_LT; LESS_SUC_REFL]];
    EXISTS_TAC `0` THEN REWRITE_TAC[NOT_LESS_0] THEN
    ASM_REWRITE_TAC[COND_ID]]);;

let DIVISION_LHS = prove(
  `!D a b. division(a,b) D ==> (D(0) = a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[division] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let DIVISION_THM = prove(
  `!D a b. division(a,b) D =
        (D(0) = a) /\
        (!n. n < (dsize D) ==> D(n) < D(SUC n)) /\
        (!n. n >= (dsize D) ==> (D(n) = b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[division] THEN
  EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; EXISTS_TAC `dsize D` THEN ASM_REWRITE_TAC[]] THEN
  POP_ASSUM(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `dsize D = N` (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[dsize] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `M:num` THEN BETA_TAC THEN EQ_TAC THENL
   [ALL_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `N:num` (ASSUME `!n:num. n >= N ==> (D n :real = b)`)) THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[GE; LE_REFL]) THEN
    DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC] THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL [`M:num`; `N:num`] LESS_LESS_CASES) THEN
  ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(MP_TAC o SPEC `SUC M` o CONJUNCT2) THEN
    REWRITE_TAC[GE; LESS_EQ_SUC_REFL] THEN DISCH_TAC THEN
    UNDISCH_TAC `!n. n < N ==> (D n) < (D(SUC n))` THEN
    DISCH_THEN(MP_TAC o SPEC `M:num`) THEN ASM_REWRITE_TAC[REAL_LT_REFL];
    DISCH_THEN(MP_TAC o SPEC `N:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!n:num. n >= N ==> (D n :real = b)` THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `N:num` th) THEN
    MP_TAC(SPEC `SUC N` th)) THEN
    REWRITE_TAC[GE; LESS_EQ_SUC_REFL; LE_REFL] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_LT_REFL]]);;

let DIVISION_RHS = prove(
  `!D a b. division(a,b) D ==> (D(dsize D) = b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DIVISION_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `dsize D` o last o CONJUNCTS) THEN
  REWRITE_TAC[GE; LE_REFL]);;

let DIVISION_LT_GEN = prove(
  `!D a b m n. division(a,b) D /\
               m < n /\
               n <= (dsize D) ==> D(m) < D(n)`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `m:num < n` THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` MP_TAC o MATCH_MP LESS_ADD_1) THEN
  REWRITE_TAC[GSYM ADD1] THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `(m + (SUC d)) <= (dsize D)` THEN
  SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OR_LESS) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DIVISION_THM]) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OR_LESS) THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC `D(m + (SUC d)):real` THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
      MATCH_MP_TAC LT_IMP_LE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[ADD_CLAUSES] THEN
      FIRST_ASSUM(MATCH_MP_TAC o el 1 o
        CONJUNCTS o REWRITE_RULE[DIVISION_THM]) THEN
      ASM_REWRITE_TAC[]]]);;

let DIVISION_LT = prove(
  `!D a b. division(a,b) D ==> !n. n < (dsize D) ==> D(0) < D(SUC n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DIVISION_THM] THEN STRIP_TAC THEN
  INDUCT_TAC THEN DISCH_THEN(fun th -> ASSUME_TAC th THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `D(SUC n):real` THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `D(0):real = a` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `SUC n` THEN
  ASM_REWRITE_TAC[LESS_SUC_REFL]);;

let DIVISION_LE = prove(
  `!D a b. division(a,b) D ==> a <= b`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIVISION_LT) THEN
  POP_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DIVISION_THM]) THEN
  UNDISCH_TAC `D(0):real = a` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `!n. n >= (dsize D) ==> (D n = b)` THEN
  DISCH_THEN(MP_TAC o SPEC `dsize D`) THEN
  REWRITE_TAC[GE; LE_REFL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(MP_TAC o SPEC `PRE(dsize D)`) THEN
  STRUCT_CASES_TAC(SPEC `dsize D` num_CASES) THEN
  ASM_REWRITE_TAC[PRE; REAL_LE_REFL; LESS_SUC_REFL; REAL_LT_IMP_LE]);;

let DIVISION_GT = prove(
  `!D a b. division(a,b) D ==> !n. n < (dsize D) ==> D(n) < D(dsize D)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIVISION_LT_GEN THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
  ASM_REWRITE_TAC[LE_REFL]);;

let DIVISION_EQ = prove(
  `!D a b. division(a,b) D ==> ((a = b) = (dsize D = 0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIVISION_LT) THEN
  POP_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DIVISION_THM]) THEN
  UNDISCH_TAC `D(0):real = a` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `!n. n >= (dsize D) ==> (D n = b)` THEN
  DISCH_THEN(MP_TAC o SPEC `dsize D`) THEN
  REWRITE_TAC[GE; LE_REFL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(MP_TAC o SPEC `PRE(dsize D)`) THEN
  STRUCT_CASES_TAC(SPEC `dsize D` num_CASES) THEN
  ASM_REWRITE_TAC[PRE; NOT_SUC; LESS_SUC_REFL; REAL_LT_IMP_NE]);;

let DIVISION_LBOUND = prove(
  `!D a b. division(a,b) D ==> !r. a <= D(r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DIVISION_THM] THEN STRIP_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISJ_CASES_TAC(SPECL [`SUC r`; `dsize D`] LTE_CASES) THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(D:num->real) r` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `SUC r` THEN
    ASM_REWRITE_TAC[LESS_SUC_REFL];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `b:real` THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIVISION_LE THEN
      EXISTS_TAC `D:num->real` THEN ASM_REWRITE_TAC[DIVISION_THM];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[GE]]]);;

let DIVISION_LBOUND_LT = prove(
  `!D a b. division(a,b) D /\ ~(dsize D = 0) ==> !n. a < D(SUC n)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP DIVISION_LHS) THEN
  DISJ_CASES_TAC(SPECL [`dsize D`; `SUC n`] LTE_CASES) THENL
   [FIRST_ASSUM(MP_TAC o el 2 o CONJUNCTS o REWRITE_RULE[DIVISION_THM]) THEN
    DISCH_THEN(MP_TAC o SPEC `SUC n`) THEN REWRITE_TAC[GE] THEN
    IMP_RES_THEN ASSUME_TAC LT_IMP_LE THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP DIVISION_RHS) THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP DIVISION_GT) THEN
    ASM_REWRITE_TAC[GSYM NOT_LE; CONJUNCT1 LE];
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP DIVISION_LT) THEN
    MATCH_MP_TAC OR_LESS THEN ASM_REWRITE_TAC[]]);;

let DIVISION_UBOUND = prove(
  `!D a b. division(a,b) D ==> !r. D(r) <= b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DIVISION_THM] THEN STRIP_TAC THEN
  GEN_TAC THEN DISJ_CASES_TAC(SPECL [`r:num`; `dsize D`] LTE_CASES) THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[GE]] THEN
  SUBGOAL_THEN `!r. D((dsize D) - r) <= b` MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `(dsize D) - r`) THEN
    MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP SUB_SUB
      (MATCH_MP LT_IMP_LE th)]) THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB]] THEN
  UNDISCH_TAC `r < (dsize D)` THEN DISCH_THEN(K ALL_TAC) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[SUB_0] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[GE; LE_REFL];
    ALL_TAC] THEN
  DISJ_CASES_TAC(SPECL [`r:num`; `dsize D`] LTE_CASES) THENL
   [ALL_TAC;
    SUBGOAL_THEN `(dsize D) - (SUC r) = 0` SUBST1_TAC THENL
     [REWRITE_TAC[SUB_EQ_0] THEN MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[LESS_EQ_SUC_REFL];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIVISION_LE THEN
      EXISTS_TAC `D:num->real` THEN ASM_REWRITE_TAC[DIVISION_THM]]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `D((dsize D) - r):real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(dsize D) - r = SUC((dsize D) - (SUC r))`
  SUBST1_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LESS_CASES_IMP THEN
    REWRITE_TAC[NOT_LT; LE_LT; SUB_LESS_EQ] THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    REWRITE_TAC[SUB_EQ_EQ_0; NOT_SUC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `r < 0` THEN REWRITE_TAC[NOT_LESS_0]] THEN
  MP_TAC(SPECL [`dsize D`; `SUC r`] (CONJUNCT2 SUB_OLD)) THEN
  LCOND_CASES_TAC THENL
   [REWRITE_TAC[SUB_EQ_0; LE_SUC] THEN
    ASM_REWRITE_TAC[GSYM NOT_LT];
    DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC[SUB_SUC]]);;

let DIVISION_UBOUND_LT = prove(
  `!D a b n. division(a,b) D /\
             n < dsize D ==> D(n) < b`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP DIVISION_RHS) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP DIVISION_GT) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------ *)
(* Divisions of adjacent intervals can be combined into one                 *)
(* ------------------------------------------------------------------------ *)

let D_tm = `\n. (n < (dsize D1)) =>  D1(n) | D2(n - (dsize D1))`
and p_tm = `\n. (n < (dsize D1)) =>
                   (p1:num->real)(n) | p2(n - (dsize D1))`;;

let DIVISION_APPEND_LEMMA1 = prove(
  `!a b c D1 D2. division(a,b) D1 /\ division(b,c) D2 ==>
        (!n. n < ((dsize D1) + (dsize D2)) ==>
                (\n. (n < (dsize D1)) =>  D1(n) |
                     D2(n - (dsize D1)))(n) <
   (\n. (n < (dsize D1)) =>  D1(n) | D2(n - (dsize D1)))(SUC n)) /\
        (!n. n >= ((dsize D1) + (dsize D2)) ==>
               ((\n. (n < (dsize D1)) =>  D1(n) |
   D2(n - (dsize D1)))(n) = (\n. (n < (dsize D1)) =>  D1(n) |
   D2(n - (dsize D1)))((dsize D1) + (dsize D2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN BETA_TAC THENL
   [ASM_CASES_TAC `(SUC n) < (dsize D1)` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `n < (dsize D1)` ASSUME_TAC THEN
      ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `SUC n` THEN
        ASM_REWRITE_TAC[LESS_SUC_REFL];
        UNDISCH_TAC `division(a,b) D1` THEN REWRITE_TAC[DIVISION_THM] THEN
        STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
        FIRST_ASSUM ACCEPT_TAC];
      ASM_CASES_TAC `n < (dsize D1)` THEN ASM_REWRITE_TAC[] THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `b:real` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC DIVISION_UBOUND_LT THEN
          EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC DIVISION_LBOUND THEN
          EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[]];
        UNDISCH_TAC `~(n < (dsize D1))` THEN
        REWRITE_TAC[NOT_LT] THEN
        DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC o
          REWRITE_RULE[LE_EXISTS]) THEN
        REWRITE_TAC[SUB_OLD; GSYM NOT_LE; LE_ADD] THEN
        ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
        FIRST_ASSUM(MATCH_MP_TAC o el 1 o CONJUNCTS o
          REWRITE_RULE[DIVISION_THM]) THEN
        UNDISCH_TAC `((dsize D1) + d) <
                     ((dsize D1) + (dsize D2))` THEN
        ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[LT_ADD_RCANCEL]]];
    REWRITE_TAC[GSYM NOT_LE; LE_ADD] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
    REWRITE_TAC[NOT_LE] THEN LCOND_CASES_TAC THEN
    UNDISCH_TAC `n >= ((dsize D1) + (dsize D2))` THENL
     [CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN
      REWRITE_TAC[GE; NOT_LE] THEN
      MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `dsize D1` THEN
      ASM_REWRITE_TAC[LE_ADD];
      REWRITE_TAC[GE; LE_EXISTS] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC) THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[ADD_SUB] THEN
      FIRST_ASSUM(CHANGED_TAC o
       (SUBST1_TAC o MATCH_MP DIVISION_RHS)) THEN
      FIRST_ASSUM(MATCH_MP_TAC o el 2 o CONJUNCTS o
        REWRITE_RULE[DIVISION_THM]) THEN
      REWRITE_TAC[GE; LE_ADD]]]);;

let DIVISION_APPEND_LEMMA2 = prove(
  `!a b c D1 D2. division(a,b) D1 /\ division(b,c) D2 ==>
                   (dsize(\n. (n < (dsize D1)) =>  D1(n) |
       D2(n - (dsize D1))) = dsize(D1) + dsize(D2))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [dsize] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `N:num` THEN BETA_TAC THEN EQ_TAC THENL
   [DISCH_THEN(prefix THEN (MATCH_MP_TAC LESS_EQUAL_ANTISYM) o MP_TAC) THEN
    CONV_TAC CONTRAPOS_CONV THEN
    REWRITE_TAC[DE_MORGAN_THM; NOT_LE] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [DISJ1_TAC THEN
      DISCH_THEN(MP_TAC o SPEC `dsize(D1) + dsize(D2)`) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM NOT_LE; LE_ADD] THEN
      SUBGOAL_THEN `!x y. x <= SUC(x + y)` ASSUME_TAC THENL
       [REPEAT GEN_TAC THEN MATCH_MP_TAC LE_TRANS THEN
        EXISTS_TAC `x + y:num` THEN
        REWRITE_TAC[LE_ADD; LESS_EQ_SUC_REFL]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUB_OLD; GSYM NOT_LE] THEN
      REWRITE_TAC[LE_ADD] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[ADD_SUB] THEN
      MP_TAC(ASSUME `division(b,c) D2`) THEN REWRITE_TAC[DIVISION_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `SUC(dsize D2)` o el 2 o CONJUNCTS) THEN
      REWRITE_TAC[GE; LESS_EQ_SUC_REFL] THEN
      DISCH_THEN SUBST1_TAC THEN
      FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o MATCH_MP DIVISION_RHS) THEN
      REWRITE_TAC[REAL_LT_REFL];
      DISJ2_TAC THEN
      DISCH_THEN(MP_TAC o SPEC `dsize(D1) + dsize(D2)`) THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP LT_IMP_LE) THEN
      ASM_REWRITE_TAC[GE] THEN
      REWRITE_TAC[GSYM NOT_LE; LE_ADD] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
      LCOND_CASES_TAC THENL
       [SUBGOAL_THEN `D1(N:num) < D2(dsize D2)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `b:real` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC DIVISION_UBOUND_LT THEN EXISTS_TAC `a:real` THEN
            ASM_REWRITE_TAC[GSYM NOT_LE];
            MATCH_MP_TAC DIVISION_LBOUND THEN
            EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[]];
          CONV_TAC CONTRAPOS_CONV THEN ASM_REWRITE_TAC[] THEN
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LT_REFL]];
        RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
        SUBGOAL_THEN `D2(N - (dsize D1)) < D2(dsize D2)` MP_TAC THENL
         [MATCH_MP_TAC DIVISION_LT_GEN THEN
          MAP_EVERY EXISTS_TAC [`b:real`; `c:real`] THEN
          ASM_REWRITE_TAC[LE_REFL] THEN
          REWRITE_TAC[GSYM NOT_LE] THEN
          REWRITE_TAC[SUB_LEFT_LESS_EQ; DE_MORGAN_THM] THEN
          ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[NOT_LE] THEN
          UNDISCH_TAC `dsize(D1) <= N` THEN
          REWRITE_TAC[LE_EXISTS] THEN
          DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC) THEN
          RULE_ASSUM_TAC(ONCE_REWRITE_RULE[ADD_SYM]) THEN
          RULE_ASSUM_TAC(REWRITE_RULE[LT_ADD_RCANCEL]) THEN
          MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `d:num` THEN
          ASM_REWRITE_TAC[LE_0];
          CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LT_REFL]]]];
  DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(SUC n) < (dsize(D1))` THEN
    ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `n < (dsize(D1))` ASSUME_TAC THENL
       [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `SUC n` THEN
        ASM_REWRITE_TAC[LESS_SUC_REFL]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIVISION_LT_GEN THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[LESS_SUC_REFL] THEN
      MATCH_MP_TAC LT_IMP_LE THEN ASM_REWRITE_TAC[];
      LCOND_CASES_TAC THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `b:real` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC DIVISION_UBOUND_LT THEN EXISTS_TAC `a:real` THEN
          ASM_REWRITE_TAC[];
          FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP DIVISION_LBOUND)];
        MATCH_MP_TAC DIVISION_LT_GEN THEN
        MAP_EVERY EXISTS_TAC [`b:real`; `c:real`] THEN
        ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC[SUB_OLD; LESS_SUC_REFL]; ALL_TAC] THEN
        REWRITE_TAC[REWRITE_RULE[GE] SUB_LEFT_GREATER_EQ] THEN
        ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[LE_SUC_LT]]];
    X_GEN_TAC `n:num` THEN REWRITE_TAC[GE] THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM NOT_LE; LE_ADD] THEN
    SUBGOAL_THEN `(dsize D1) <= n` ASSUME_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `dsize D1 + dsize D2` THEN
      ASM_REWRITE_TAC[LE_ADD];
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[ADD_SUB] THEN
      FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o MATCH_MP DIVISION_RHS) THEN
      FIRST_ASSUM(MATCH_MP_TAC o el 2 o
        CONJUNCTS o REWRITE_RULE[DIVISION_THM]) THEN
      REWRITE_TAC[GE; SUB_LEFT_LESS_EQ] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[]]]]);;

let DIVISION_APPEND = prove(
  `!a b c.
      (?D1 p1. tdiv(a,b) (D1,p1) /\ fine(g) (D1,p1)) /\
      (?D2 p2. tdiv(b,c) (D2,p2) /\ fine(g) (D2,p2)) ==>
        ?D p. tdiv(a,c) (D,p) /\ fine(g) (D,p)`,
  REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [D_tm; p_tm] THEN
  DISJ_CASES_TAC(GSYM (SPEC `dsize(D1)` LESS_0_CASES)) THENL
   [ASM_REWRITE_TAC[NOT_LESS_0; SUB_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
    SUBGOAL_THEN `a:real = b` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MP_TAC(SPECL [`D1:num->real`; `a:real`; `b:real`] DIVISION_EQ) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[tdiv]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[fine] THEN X_GEN_TAC `n:num` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[tdiv]) THEN
    MP_TAC(SPECL [`a:real`; `b:real`; `c:real`;
                  `D1:num->real`; `D2:num->real`] DIVISION_APPEND_LEMMA2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN BETA_TAC THEN
    DISCH_TAC THEN ASM_CASES_TAC `(SUC n) < (dsize D1)` THEN
    ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `n < (dsize D1)` ASSUME_TAC THENL
       [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `SUC n` THEN
        ASM_REWRITE_TAC[LESS_SUC_REFL]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[fine]) THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `n < (dsize D1)` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `SUC n = dsize D1` ASSUME_TAC THENL
       [MATCH_MP_TAC LESS_EQUAL_ANTISYM THEN
        ASM_REWRITE_TAC[GSYM NOT_LT] THEN
        REWRITE_TAC[NOT_LT] THEN MATCH_MP_TAC LESS_OR THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[SUB_REFL] THEN
        FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o MATCH_MP DIVISION_LHS o
          CONJUNCT1) THEN
        FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o SYM o
          MATCH_MP DIVISION_RHS o  CONJUNCT1) THEN
        SUBST1_TAC(SYM(ASSUME `SUC n = dsize D1`)) THEN
        FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[fine]) THEN
        ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[SUB_OLD] THEN UNDISCH_TAC `~(n < (dsize D1))` THEN
      REWRITE_TAC[LE_EXISTS; NOT_LT] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC) THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[fine]) THEN
      RULE_ASSUM_TAC(ONCE_REWRITE_RULE[ADD_SYM]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[LT_ADD_RCANCEL]) THEN
      FIRST_ASSUM ACCEPT_TAC]] THEN
  REWRITE_TAC[tdiv] THEN BETA_TAC THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[tdiv]) THEN
    REWRITE_TAC[DIVISION_THM] THEN CONJ_TAC THENL
     [BETA_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC DIVISION_LHS THEN EXISTS_TAC `b:real` THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `c = (\n. (n < (dsize D1)) =>  D1(n) | D2(n -
                  (dsize D1))) (dsize(D1) + dsize(D2))` SUBST1_TAC THENL
     [BETA_TAC THEN REWRITE_TAC[GSYM NOT_LE; LE_ADD] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC DIVISION_RHS THEN
      EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`a:real`; `b:real`; `c:real`;
                 `D1:num->real`; `D2:num->real`] DIVISION_APPEND_LEMMA2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC (BETA_RULE DIVISION_APPEND_LEMMA1) THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`; `c:real`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN RULE_ASSUM_TAC(REWRITE_RULE[tdiv]) THEN
  ASM_CASES_TAC `(SUC n) < (dsize D1)` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `n < (dsize D1)` ASSUME_TAC THENL
     [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `SUC n` THEN
      ASM_REWRITE_TAC[LESS_SUC_REFL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  LCOND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[SUB_OLD] THEN
    FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o MATCH_MP DIVISION_LHS o
      CONJUNCT1) THEN
    FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o SYM o
      MATCH_MP DIVISION_RHS o  CONJUNCT1) THEN
    SUBGOAL_THEN `dsize D1 = SUC n` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC LESS_EQUAL_ANTISYM THEN
    ASM_REWRITE_TAC[GSYM NOT_LT] THEN REWRITE_TAC[NOT_LT] THEN
    MATCH_MP_TAC LESS_OR THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[SUB_OLD]]);;

(* ------------------------------------------------------------------------ *)
(* We can always find a division which is fine wrt any gauge                *)
(* ------------------------------------------------------------------------ *)

let DIVISION_EXISTS = prove(
  `!a b g. a <= b /\ gauge(\x. a <= x /\ x <= b) g ==>
        ?D p. tdiv(a,b) (D,p) /\ fine(g) (D,p)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  (MP_TAC o C SPEC BOLZANO_LEMMA)
    `\(u,v). a <= u /\ v <= b ==> ?D p. tdiv(u,v) (D,p) /\ fine(g) (D,p)` THEN
  CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV) THEN
  W(C SUBGOAL_THEN (fun t ->REWRITE_TAC[t]) o
  funpow 2 (fst o dest_imp) o snd) THENL
   [CONJ_TAC;
    DISCH_THEN(MP_TAC o SPECL [`a:real`; `b:real`]) THEN
    REWRITE_TAC[REAL_LE_REFL]]
  THENL
   [MAP_EVERY X_GEN_TAC [`u:real`; `v:real`; `w:real`] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC DIVISION_APPEND THEN
    EXISTS_TAC `v:real` THEN CONJ_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `w:real`;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `u:real`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN ASM_CASES_TAC `a <= x /\ x <= b` THENL
   [ALL_TAC;
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    MAP_EVERY X_GEN_TAC [`w:real`; `y:real`] THEN STRIP_TAC THEN
    CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_neg o concl) THEN
    REWRITE_TAC[DE_MORGAN_THM; REAL_NOT_LE] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [DISJ1_TAC THEN MATCH_MP_TAC REAL_LET_TRANS;
      DISJ2_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS] THEN
    EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC `gauge(\x. a <= x /\ x <= b) g` THEN
  REWRITE_TAC[gauge] THEN BETA_TAC THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP th)) THEN
  EXISTS_TAC `(g:real->real) x` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`w:real`; `y:real`] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `\n. (n = 0) => (w:real) | y` THEN
  EXISTS_TAC `\n. (n = 0) => (x:real) | y` THEN
  SUBGOAL_THEN `w <= y` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `x:real` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[tdiv] THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIVISION_SINGLE THEN FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `n:num` THEN BETA_TAC THEN REWRITE_TAC[NOT_SUC] THEN
      LCOND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]];
    REWRITE_TAC[fine] THEN BETA_TAC THEN REWRITE_TAC[NOT_SUC] THEN
    X_GEN_TAC `n:num` THEN
    DISJ_CASES_THEN MP_TAC (REWRITE_RULE[REAL_LE_LT] (ASSUME `w <= y`)) THENL
     [DISCH_THEN(ASSUME_TAC o MATCH_MP DIVISION_1) THEN
      ASM_REWRITE_TAC[num_CONV `1`; CONJUNCT2 LT; NOT_LESS_0] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(SUBST1_TAC o MATCH_MP DIVISION_0) THEN
      REWRITE_TAC[NOT_LESS_0]]]);;

(* ------------------------------------------------------------------------ *)
(* Lemmas about combining gauges                                            *)
(* ------------------------------------------------------------------------ *)

let GAUGE_MIN = prove(
  `!E g1 g2. gauge(E) g1 /\ gauge(E) g2 ==>
        gauge(E) (\x. g1(x) < g2(x) => g1(x) | g2(x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gauge] THEN STRIP_TAC THEN
  X_GEN_TAC `x:real` THEN BETA_TAC THEN DISCH_TAC THEN
  LCOND_CASES_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM ACCEPT_TAC);;

let FINE_MIN = prove(
  `!g1 g2 D p. fine (\x. g1(x) < g2(x) => g1(x) | g2(x)) (D,p) ==>
        fine(g1) (D,p) /\ fine(g2) (D,p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fine] THEN
  BETA_TAC THEN DISCH_TAC THEN CONJ_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  LCOND_CASES_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT]) THEN
    MATCH_MP_TAC REAL_LTE_TRANS;
    MATCH_MP_TAC REAL_LT_TRANS] THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC(rand(concl th)) THEN
                   ASM_REWRITE_TAC[] THEN NO_TAC));;

(* ------------------------------------------------------------------------ *)
(* The integral is unique if it exists                                      *)
(* ------------------------------------------------------------------------ *)

let DINT_UNIQ = prove(
  `!a b f k1 k2. a <= b /\ Dint(a,b) f k1 /\ Dint(a,b) f k2 ==> (k1 = k2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_SUB_0] THEN
  CONV_TAC CONTRAPOS_CONV THEN ONCE_REWRITE_TAC[ABS_NZ] THEN DISCH_TAC THEN
  REWRITE_TAC[Dint] THEN
  DISCH_THEN(CONJUNCTS_THEN(MP_TAC o SPEC `abs(k1 - k2) / &2`)) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real->real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `g2:real->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`\x. a <= x /\ x <= b`;
                `g1:real->real`; `g2:real->real`] GAUGE_MIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a:real`; `b:real`;
         `\x:real. g1(x) < g2(x) => g1(x) | g2(x)`] DIVISION_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:num->real` (X_CHOOSE_THEN `p:num->real`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FINE_MIN) THEN
  REPEAT(FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPECL [`D:num->real`; `p:num->real`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
  SUBGOAL_THEN `abs((rsum(D,p) f - k2) - (rsum(D,p) f - k1)) < abs(k1 - k2)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `abs(rsum(D,p) f - k2) + abs(rsum(D,p) f - k1)` THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [real_sub] THEN
      GEN_REWRITE_TAC (funpow 2 RAND_CONV) [GSYM ABS_NEG] THEN
      MATCH_ACCEPT_TAC ABS_TRIANGLE;
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_HALF_DOUBLE] THEN
      MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[real_sub; REAL_NEG_ADD; REAL_NEG_SUB] THEN
    ONCE_REWRITE_TAC[AC REAL_ADD_AC
      `(a + b) + (c + d) = (d + a) + (c + b)`] THEN
    REWRITE_TAC[REAL_ADD_LINV; REAL_ADD_LID; REAL_LT_REFL]]);;

(* ------------------------------------------------------------------------ *)
(* Integral over a null interval is 0                                       *)
(* ------------------------------------------------------------------------ *)

let INTEGRAL_NULL = prove(
  `!f a. Dint(a,a) f (&0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[Dint] THEN GEN_TAC THEN
  DISCH_TAC THEN EXISTS_TAC `\x:real. &1` THEN
  REWRITE_TAC[gauge; REAL_LT_01] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[tdiv] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIVISION_EQ) THEN
  REWRITE_TAC[rsum] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[Sum; REAL_SUB_REFL; ABS_0]);;

(* ------------------------------------------------------------------------ *)
(* Fundamental theorem of calculus (Part I)                                 *)
(* ------------------------------------------------------------------------ *)

let STRADDLE_LEMMA = prove(
  `!f f' a b e. (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\ &0 < e
    ==> ?g. gauge(\x. a <= x /\ x <= b) g /\
            !x u v. a <= u /\ u <= x /\ x <= v /\ v <= b /\ (v - u) < g(x)
                ==> abs((f(v) - f(u)) - (f'(x) * (v - u))) <= e * (v - u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gauge] THEN BETA_TAC THEN
  SUBGOAL_THEN
   `!x. a <= x /\ x <= b ==>
        ?d. &0 < d /\
          !u v. u <= x /\ x <= v /\ (v - u) < d ==>
            abs((f(v) - f(u)) - (f'(x) * (v - u))) <= e * (v - u)` MP_TAC THENL
   [ALL_TAC;
    FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN(MP_TAC o CONV_RULE
      ((ONCE_DEPTH_CONV RIGHT_IMP_EXISTS_CONV) THENC OLD_SKOLEM_CONV)) THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real->real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `g:real->real` THEN CONJ_TAC THENL
     [GEN_TAC THEN
      DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]);
      REPEAT STRIP_TAC THEN
      C SUBGOAL_THEN (fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th))
      `a <= x /\ x <= b` THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
         [EXISTS_TAC `u:real`; EXISTS_TAC `v:real`] THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]]]] THEN
  X_GEN_TAC `x:real` THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[diffl; LIM] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
  BETA_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!z. abs(z - x) < d ==>
        abs((f(z) - f(x)) - (f'(x) * (z - x))) <= (e / &2) * abs(z - x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_CASES_TAC `&0 < abs(z - x)` THENL
     [ALL_TAC;
      UNDISCH_TAC `~(&0 < abs(z - x))` THEN
      REWRITE_TAC[GSYM ABS_NZ; REAL_SUB_0] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; ABS_0; REAL_LE_REFL]] THEN
    DISCH_THEN(MP_TAC o CONJ (ASSUME `&0 < abs(z - x)`)) THEN
    DISCH_THEN(prefix THEN (MATCH_MP_TAC REAL_LT_IMP_LE) o MP_TAC) THEN
    DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV
      [GSYM(MATCH_MP REAL_LT_RMUL_EQ th)]) THEN
    MATCH_MP_TAC (TAUT `(a = b) ==> a ==> b`) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM ABS_MUL] THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_SUB_RDISTRIB] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_SUB_ADD2] THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    ASM_REWRITE_TAC[ABS_NZ]; ALL_TAC] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `u <= v` (DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `x:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC;
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; ABS_0; REAL_LE_REFL]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs((f(v) - f(x)) - (f'(x) * (v - x))) +
              abs((f(x) - f(u)) - (f'(x) * (x - u)))` THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL[`(f(v) - f(x)) - (f'(x) * (v - x))`;
                 `(f(x) - f(u)) - (f'(x) * (x - u))`] ABS_TRIANGLE) THEN
    MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN
    AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[GSYM REAL_ADD2_SUB2] THEN
    REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
    SUBGOAL_THEN `!a b c. (a - b) + (b - c) = (a - c)`
      (fun th -> REWRITE_TAC[th]) THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[real_sub] THEN
    ONCE_REWRITE_TAC[AC REAL_ADD_AC
      `(a + b) + (c + d) = (b + c) + (a + d)`] THEN
    REWRITE_TAC[REAL_ADD_LINV; REAL_ADD_LID]; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_HALF_DOUBLE] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(e / &2) * abs(v - x)` THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[real_abs; REAL_SUB_LE] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `v - u` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_sub; REAL_LE_LADD] THEN
      ASM_REWRITE_TAC[REAL_LE_NEG];
      ASM_REWRITE_TAC[real_abs; REAL_SUB_LE] THEN REWRITE_TAC[real_div] THEN
      GEN_REWRITE_TAC LAND_CONV
       [AC REAL_MUL_AC `(a * b) * c = (a * c) * b`] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC;
        MATCH_MP REAL_LE_LMUL_LOCAL (ASSUME `&0 < e`)] THEN
      SUBGOAL_THEN `!x y. (x * inv(&2)) <= (y * inv(&2)) = x <= y`
      (fun th -> ASM_REWRITE_TAC[th; real_sub; REAL_LE_LADD; REAL_LE_NEG]) THEN
      REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_RMUL_EQ THEN
      MATCH_MP_TAC REAL_INV_POS THEN
      REWRITE_TAC[REAL_LT; num_CONV `2`; LT_0]];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(e / &2) * abs(x - u)` THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [real_sub] THEN
      ONCE_REWRITE_TAC[GSYM ABS_NEG] THEN
      REWRITE_TAC[REAL_NEG_ADD; REAL_NEG_SUB] THEN
      ONCE_REWRITE_TAC[REAL_NEG_RMUL] THEN
      REWRITE_TAC[REAL_NEG_SUB] THEN REWRITE_TAC[GSYM real_sub] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[ABS_SUB] THEN
      ASM_REWRITE_TAC[real_abs; REAL_SUB_LE] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `v - u` THEN
      ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[real_sub; REAL_LE_RADD];
      ASM_REWRITE_TAC[real_abs; REAL_SUB_LE] THEN REWRITE_TAC[real_div] THEN
      GEN_REWRITE_TAC LAND_CONV
       [AC REAL_MUL_AC `(a * b) * c = (a * c) * b`] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC;
        MATCH_MP REAL_LE_LMUL_LOCAL (ASSUME `&0 < e`)] THEN
      SUBGOAL_THEN `!x y. (x * inv(&2)) <= (y * inv(&2)) = x <= y`
      (fun th -> ASM_REWRITE_TAC[th; real_sub; REAL_LE_RADD; REAL_LE_NEG]) THEN
      REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_RMUL_EQ THEN
      MATCH_MP_TAC REAL_INV_POS THEN
      REWRITE_TAC[REAL_LT; num_CONV `2`; LT_0]]]);;

let FTC1 = prove(
  `!f f' a b. a <= b /\ (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x))
        ==> Dint(a,b) f' (f(b) - f(a))`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `a <= b` THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[REAL_SUB_REFL; INTEGRAL_NULL]] THEN
  REWRITE_TAC[Dint] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `!e. &0 < e ==>
      ?g. gauge(\x. a <= x /\ x <= b)g /\
          (!D p.
            tdiv(a,b)(D,p) /\ fine g(D,p) ==>
            (abs((rsum(D,p)f') - ((f b) - (f a)))) <= e)`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real->real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `g:real->real` THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(fun th -> FIRST_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `e / &2` THEN
    ASM_REWRITE_TAC[REAL_LT_HALF2]] THEN
  UNDISCH_TAC `&0 < e` THEN DISCH_THEN(K ALL_TAC) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`f:real->real`; `f':real->real`;
    `a:real`; `b:real`; `e / (b - a)`] STRADDLE_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < e / (b - a)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INV_POS THEN
    ASM_REWRITE_TAC[REAL_SUB_LT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `g:real->real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`D:num->real`; `p:num->real`] THEN
  REWRITE_TAC[tdiv] THEN STRIP_TAC THEN REWRITE_TAC[rsum] THEN
  SUBGOAL_THEN `f(b) - f(a) = Sum(0,dsize D)(\n. f(D(SUC n)) - f(D(n)))`
  SUBST1_TAC THENL
   [MP_TAC(SPECL [`\n:num. (f:real->real)(D(n))`; `0`; `dsize D`]
      SUM_CANCEL) THEN BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    MAP_EVERY (IMP_RES_THEN SUBST1_TAC) [DIVISION_LHS; DIVISION_RHS] THEN
    REFL_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[ABS_SUB] THEN REWRITE_TAC[GSYM SUM_SUB] THEN BETA_TAC THEN
  LE_MATCH_TAC ABS_SUM THEN BETA_TAC THEN
  SUBGOAL_THEN `e = Sum(0,dsize D)(\n. (e / (b - a)) * (D(SUC n) - D(n)))`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[SYM(BETA_CONV `(\n. (D(SUC n) - D(n))) n`)] THEN
    ASM_REWRITE_TAC[SUM_CMUL; SUM_CANCEL; ADD_CLAUSES] THEN
    MAP_EVERY (IMP_RES_THEN SUBST1_TAC) [DIVISION_LHS; DIVISION_RHS] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    REWRITE_TAC[REAL_SUB_0] THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN
  REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN BETA_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [IMP_RES_THEN (fun th -> REWRITE_TAC[th]) DIVISION_LBOUND;
    IMP_RES_THEN (fun th -> REWRITE_TAC[th]) DIVISION_UBOUND;
    UNDISCH_TAC `fine(g)(D,p)` THEN REWRITE_TAC[fine] THEN
    DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

(* ======================================================================== *)
(* MacLaurin's theorem.                                                     *)
(* ======================================================================== *)

(* ------------------------------------------------------------------------ *)
(* SYM_CANON_CONV - Canonicalizes single application of symmetric operator  *)
(* Rewrites `so as to make fn true`, e.g. fn = (<<) or fn = curry(=) `1` o fst*)
(* ------------------------------------------------------------------------ *)

let SYM_CANON_CONV sym fn =
  REWR_CONV sym o assert
   (prefix not o fn o ((snd o dest_comb) F_F I) o dest_comb);;

(* ----------------------------------------------------------- *)
(* EXT_CONV `!x. f x = g x` = |- (!x. f x = g x) = (f = g)     *)
(* ----------------------------------------------------------- *)

let EXT_CONV =  SYM o uncurry X_FUN_EQ_CONV o
      (I F_F (mk_eq o (rator F_F rator) o dest_eq)) o dest_forall;;

(* ======================================================================== *)
(* Mclaurin's theorem with Lagrange form of remainder                       *)
(* We could weaken the hypotheses slightly, but it's not worth it           *)
(* ======================================================================== *)

hide_constant "B";;

let MCLAURIN = prove(
  `!f diff h n.
    &0 < h /\
    0 < n /\
    (diff(0) = f) /\
    (!m t. m < n /\ &0 <= t /\ t <= h ==>
           (diff(m) diffl diff(SUC m)(t))(t)) ==>
   (?t. &0 < t /\ t < h /\
        (f(h) = Sum(0,n)(\m. (diff(m)(&0) / &(FACT m)) * (h pow m)) +
                ((diff(n)(t) / &(FACT n)) * (h pow n))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `0 < n` THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `r:num` MP_TAC)
   (SPEC `n:num` num_CASES) THEN REWRITE_TAC[LT_REFL] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `?B. f(h) = Sum(0,n)(\m. (diff(m)(&0) / &(FACT m)) * (h pow m))
                  + (B * ((h pow n) / &(FACT n)))` MP_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EQ_SUB_RADD] THEN
    EXISTS_TAC `(f(h) - Sum(0,n)(\m. (diff(m)(&0) / &(FACT m)) * (h pow m)))
        * &(FACT n) / (h pow n)` THEN REWRITE_TAC[real_div] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_MUL_RID] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    ONCE_REWRITE_TAC[AC REAL_MUL_AC
      `a * b * c * d = (d * a) * (b * c)`] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN BINOP_TAC THEN
    MATCH_MP_TAC REAL_MUL_LINV THENL
     [MATCH_MP_TAC REAL_POS_NZ THEN REWRITE_TAC[REAL_LT; FACT_LT];
      MATCH_MP_TAC POW_NZ THEN MATCH_MP_TAC REAL_POS_NZ THEN
      ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (ASSUME_TAC o SYM)) THEN
  ABBREV_TAC `g = \t. f(t) -
                      (Sum(0,n)(\m. (diff(m)(&0) / &(FACT m)) * (t pow m)) +
                       (B * ((t pow n) / &(FACT n))))` THEN
  SUBGOAL_THEN `(g(&0) = &0) /\ (g(h) = &0)` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN BETA_TAC THEN ASM_REWRITE_TAC[REAL_SUB_REFL] THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[POW_0; REAL_DIV_LZERO] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN REWRITE_TAC[REAL_SUB_0] THEN
    MP_TAC(GEN `j:num->real`
     (SPECL [`j:num->real`; `r:num`; `1`] SUM_OFFSET)) THEN
    REWRITE_TAC[ADD1; REAL_EQ_SUB_LADD] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN BETA_TAC THEN
    REWRITE_TAC[SUM_1] THEN BETA_TAC THEN REWRITE_TAC[pow; FACT] THEN
    ASM_REWRITE_TAC[real_div; REAL_INV1; REAL_MUL_RID] THEN
    CONV_TAC SYM_CONV THEN REWRITE_TAC[REAL_ADD_LID_UNIQ] THEN
    REWRITE_TAC[GSYM ADD1; POW_0; REAL_MUL_RZERO; SUM_0]; ALL_TAC] THEN
  ABBREV_TAC `difg = \m t. diff(m) t -
      (Sum(0,n - m)(\p. (diff(m + p)(&0) / &(FACT p)) * (t pow p))
       + (B * ((t pow (n - m)) / &(FACT(n - m)))))` THEN
  SUBGOAL_THEN `difg(0):real->real = g` ASSUME_TAC THENL
   [EXPAND_TAC "difg" THEN BETA_TAC THEN EXPAND_TAC "g" THEN
    CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; SUB_0]; ALL_TAC] THEN
  SUBGOAL_THEN `(!m t. m < n /\ (& 0) <= t /\ t <= h ==>
                   (difg(m) diffl difg(SUC m)(t))(t))` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "difg" THEN BETA_TAC THEN
    CONV_TAC((funpow 2 RATOR_CONV o RAND_CONV) HABS_CONV) THEN
    MATCH_MP_TAC DIFF_SUB THEN CONJ_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC((funpow 2 RATOR_CONV o RAND_CONV) HABS_CONV) THEN
    MATCH_MP_TAC DIFF_ADD THEN CONJ_TAC THENL
     [ALL_TAC;
      W(MP_TAC o DIFF_CONV o rand o funpow 2 rator o snd) THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RID; REAL_ADD_LID] THEN
      REWRITE_TAC[REAL_FACT_NZ; REAL_SUB_RZERO] THEN
      DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
      MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN
      AP_THM_TAC THEN CONV_TAC(ONCE_DEPTH_CONV(ALPHA_CONV `t:real`)) THEN
      AP_TERM_TAC THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC; POW_2] THEN
      ONCE_REWRITE_TAC[AC REAL_MUL_AC
        `a * b * c * d = b * (a * (d * c))`] THEN
      FIRST_ASSUM(X_CHOOSE_THEN `d:num` SUBST1_TAC o
        MATCH_MP LESS_ADD_1 o CONJUNCT1) THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] (GSYM ADD1)] THEN
      REWRITE_TAC[ADD_SUB] THEN AP_TERM_TAC THEN
      IMP_SUBST_TAC REAL_INV_MUL_WEAK THEN REWRITE_TAC[REAL_FACT_NZ] THEN
      REWRITE_TAC[GSYM ADD1; FACT; GSYM REAL_MUL] THEN
      REPEAT(IMP_SUBST_TAC REAL_INV_MUL_WEAK THEN
             REWRITE_TAC[REAL_FACT_NZ; REAL_INJ; NOT_SUC]) THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      ONCE_REWRITE_TAC[AC REAL_MUL_AC
       `a * b * c * d * e * f * g = (b * a) * (d * f) * (c * g) * e`] THEN
      REPEAT(IMP_SUBST_TAC REAL_MUL_LINV THEN REWRITE_TAC[REAL_FACT_NZ] THEN
             REWRITE_TAC[REAL_INJ; NOT_SUC]) THEN
      REWRITE_TAC[REAL_MUL_LID]] THEN
    FIRST_ASSUM(X_CHOOSE_THEN `d:num` SUBST1_TAC o
        MATCH_MP LESS_ADD_1 o CONJUNCT1) THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] (GSYM ADD1)] THEN
    REWRITE_TAC[ADD_SUB] THEN
    REWRITE_TAC[GSYM(REWRITE_RULE[REAL_EQ_SUB_LADD] SUM_OFFSET)] THEN
    BETA_TAC THEN REWRITE_TAC[SUM_1] THEN BETA_TAC THEN
    CONV_TAC (funpow 2 RATOR_CONV (RAND_CONV HABS_CONV)) THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_ADD_RID] THEN
    MATCH_MP_TAC DIFF_ADD THEN REWRITE_TAC[pow; DIFF_CONST] THEN
    (MP_TAC o C SPECL DIFF_SUM)
     [`\p x. (diff((p + 1) + m)(&0) / &(FACT(p + 1)))
                * (x pow (p + 1))`;
      `\p x. (diff(p + (SUC m))(&0) / &(FACT p)) * (x pow p)`;
      `0`; `d:num`; `t:real`] THEN BETA_TAC THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    W(MP_TAC o DIFF_CONV o rand o funpow 2 rator o snd) THEN
    DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
    MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN
    CONV_TAC(ONCE_DEPTH_CONV(ALPHA_CONV `z:real`)) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID; REAL_MUL_RID] THEN
    REWRITE_TAC[GSYM ADD1; ADD_CLAUSES; real_div; GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[SUC_SUB1] THEN
    ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c * d = c * (a * d) * b`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `&(SUC k) = inv(inv(&(SUC k)))` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INVINV THEN
      REWRITE_TAC[REAL_INJ; NOT_SUC]; ALL_TAC] THEN
    IMP_SUBST_TAC(GSYM REAL_INV_MUL_WEAK) THENL
     [CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN REWRITE_TAC[REAL_FACT_NZ] THEN
      MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_INV_POS THEN
      REWRITE_TAC[REAL_LT; LT_0]; ALL_TAC] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FACT; GSYM REAL_MUL; REAL_MUL_ASSOC] THEN
    IMP_SUBST_TAC REAL_MUL_LINV THEN REWRITE_TAC[REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_INJ; NOT_SUC]; ALL_TAC] THEN
  SUBGOAL_THEN `!m. m < n ==>
        ?t. &0 < t /\ t < h /\ (difg(SUC m)(t) = &0)` MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `r:num`) THEN EXPAND_TAC "n" THEN
    REWRITE_TAC[LESS_SUC_REFL] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `difg(SUC r)(t:real) = &0` THEN EXPAND_TAC "difg" THEN
    ASM_REWRITE_TAC[SUB_REFL; Sum; pow; FACT] THEN
    REWRITE_TAC[REAL_SUB_0; REAL_ADD_LID; real_div] THEN
    REWRITE_TAC[REAL_INV1; REAL_MUL_RID] THEN DISCH_THEN SUBST1_TAC THEN
    GEN_REWRITE_TAC (funpow 2 RAND_CONV)
     [AC REAL_MUL_AC
      `(a * b) * c = a * (c * b)`] THEN
    ASM_REWRITE_TAC[GSYM real_div]] THEN
  SUBGOAL_THEN `!m:num. m < n ==> (difg(m)(&0) = &0)` ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN EXPAND_TAC "difg" THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
    MP_TAC(GEN `j:num->real`
     (SPECL [`j:num->real`; `d:num`; `1`] SUM_OFFSET)) THEN
    REWRITE_TAC[ADD1; REAL_EQ_SUB_LADD] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN BETA_TAC THEN
    REWRITE_TAC[SUM_1] THEN BETA_TAC THEN
    REWRITE_TAC[FACT; pow; REAL_INV1; ADD_CLAUSES; real_div; REAL_MUL_RID] THEN
    REWRITE_TAC[GSYM ADD1; POW_0; REAL_MUL_RZERO; SUM_0; REAL_ADD_LID] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID] THEN
    REWRITE_TAC[REAL_SUB_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `!m:num. m < n ==> ?t. &0 < t /\ t < h /\
                        (difg(m) diffl &0)(t)` MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(fun th -> GEN_TAC THEN
      DISCH_THEN(fun t -> ASSUME_TAC t THEN MP_TAC(MATCH_MP th t))) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DIFF_UNIQ THEN EXISTS_TAC `difg(m:num):real->real` THEN
    EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_ASSUM ACCEPT_TAC] THEN
  INDUCT_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC ROLLE THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!t. &0 <= t /\ t <= h ==> g differentiable t` MP_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[differentiable] THEN
      EXISTS_TAC `difg(SUC 0)(t:real):real` THEN
      SUBST1_TAC(SYM(ASSUME `difg(0):real->real = g`)) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC DIFF_CONT THEN
      REWRITE_TAC[GSYM differentiable] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]];
    DISCH_TAC THEN
    SUBGOAL_THEN `m < n:num`
    (fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THENL
     [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `SUC m` THEN
      ASM_REWRITE_TAC[LESS_SUC_REFL]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?t. (& 0) < t /\ t < t0 /\ ((difg(SUC m)) diffl (& 0))t`
    MP_TAC THENL
     [MATCH_MP_TAC ROLLE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `difg(SUC m)(&0) = &0` SUBST1_TAC THENL
         [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
          MATCH_MP_TAC DIFF_UNIQ THEN EXISTS_TAC `difg(m:num):real->real` THEN
          EXISTS_TAC `t0:real` THEN ASM_REWRITE_TAC[] THEN
          FIRST_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `SUC m` THEN
            ASM_REWRITE_TAC[LESS_SUC_REFL];
            MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
            MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]]]; ALL_TAC] THEN
      SUBGOAL_THEN `!t. &0 <= t /\ t <= t0 ==>
                       difg(SUC m) differentiable t` ASSUME_TAC THENL
       [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[differentiable] THEN
        EXISTS_TAC `difg(SUC(SUC m))(t:real):real` THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `t0:real` THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC DIFF_CONT THEN
        REWRITE_TAC[GSYM differentiable] THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
        CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `t0:real` THEN
      ASM_REWRITE_TAC[]]]);;

let MCLAURIN_NEG = prove
 (`!f diff h n.
    h < &0 /\
    0 < n /\
    (diff(0) = f) /\
    (!m t. m < n /\ h <= t /\ t <= &0 ==>
           (diff(m) diffl diff(SUC m)(t))(t)) ==>
   (?t. h < t /\ t < &0 /\
        (f(h) = Sum(0,n)(\m. (diff(m)(&0) / &(FACT m)) * (h pow m)) +
                ((diff(n)(t) / &(FACT n)) * (h pow n))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`\x. (f(--x):real)`;
                `\n x. ((--(&1)) pow n) * (diff:num->real->real)(n)(--x)`;
                `--h`; `n:num`] MCLAURIN) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[REAL_NEG_GT0; pow; REAL_MUL_LID] THEN
  ONCE_REWRITE_TAC[GSYM REAL_LE_NEG] THEN
  REWRITE_TAC[REAL_NEGNEG; REAL_NEG_0] THEN
  ONCE_REWRITE_TAC[AC CONJ_ACI `a /\ b /\ c = a /\ c /\ b`] THEN
  W(C SUBGOAL_THEN (fun t -> REWRITE_TAC[t]) o
  funpow 2 (fst o dest_imp) o snd) THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(MP_TAC o C CONJ (SPEC `t:real` (DIFF_CONV `\x. --x`))) THEN
    CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_CHAIN) THEN
    DISCH_THEN(MP_TAC o GEN_ALL o MATCH_MP DIFF_CMUL) THEN
    DISCH_THEN(MP_TAC o SPEC `(--(&1)) pow m`) THEN BETA_TAC THEN
    MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN
    CONV_TAC(ONCE_DEPTH_CONV(ALPHA_CONV `z:real`)) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC(AC REAL_MUL_AC);
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `--t` THEN ONCE_REWRITE_TAC[GSYM REAL_LT_NEG] THEN
  ASM_REWRITE_TAC[REAL_NEGNEG; REAL_NEG_0] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `m:num` THEN REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN BETA_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC
    `a * b * c * d = (b * c) * (a * d)`] THEN
  REWRITE_TAC[GSYM POW_MUL; GSYM REAL_NEG_MINUS1; REAL_NEGNEG] THEN
  REWRITE_TAC[REAL_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Simple strong form if a function is differentiable everywhere.            *)
(* ------------------------------------------------------------------------- *)

let MCLAURIN_ALL_LT = prove
 (`!f diff.
      (diff 0 = f) /\
      (!m x. ((diff m) diffl (diff(SUC m) x)) x)
      ==> !x n. ~(x = &0) /\ 0 < n
            ==> ?t. &0 < abs(t) /\ abs(t) < abs(x) /\
                    (f(x) = Sum(0,n)(\m. (diff m (&0) / &(FACT m)) * x pow m) +
                            (diff n t / &(FACT n)) * x pow n)`,
  REPEAT STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN MP_TAC
   (SPECL [`x:real`; `&0`] REAL_LT_TOTAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [MP_TAC(SPECL [`f:real->real`; `diff:num->real->real`;
                  `x:real`; `n:num`] MCLAURIN_NEG) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `t < &0` THEN UNDISCH_TAC `x < t` THEN REAL_ARITH_TAC;
    MP_TAC(SPECL [`f:real->real`; `diff:num->real->real`;
                  `x:real`; `n:num`] MCLAURIN) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < t` THEN UNDISCH_TAC `t < x` THEN REAL_ARITH_TAC]);;

let MCLAURIN_ZERO = prove
 (`!diff n x. (x = &0) /\ 0 < n ==>
       (Sum(0,n)(\m. (diff m (&0) / &(FACT m)) * x pow m) = diff 0 (&0))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN REWRITE_TAC[LT_REFL] THEN
  REWRITE_TAC[LT] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (SUBST1_TAC o SYM) MP_TAC) THENL
   [REWRITE_TAC[Sum; ADD_CLAUSES; FACT; real_pow; real_div; REAL_INV_1] THEN
    REWRITE_TAC[REAL_ADD_LID; REAL_MUL_RID];
    REWRITE_TAC[Sum] THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN ANTE_RES_THEN SUBST1_TAC th) THEN
    UNDISCH_TAC `0 < n` THEN SPEC_TAC(`n:num`,`n:num`) THEN
    INDUCT_TAC THEN REWRITE_TAC[LT_REFL] THEN
    REWRITE_TAC[ADD_CLAUSES; real_pow; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
    REWRITE_TAC[REAL_ADD_RID]]);;

let MCLAURIN_ALL_LE = prove
 (`!f diff.
      (diff 0 = f) /\
      (!m x. ((diff m) diffl (diff(SUC m) x)) x)
      ==> !x n. ?t. abs(t) <= abs(x) /\
                    (f(x) = Sum(0,n)(\m. (diff m (&0) / &(FACT m)) * x pow m) +
                            (diff n t / &(FACT n)) * x pow n)`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_THEN MP_TAC(SPECL [`n:num`; `0`] LET_CASES) THENL
   [REWRITE_TAC[LE] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[Sum; REAL_ADD_LID; FACT] THEN EXISTS_TAC `x:real` THEN
    REWRITE_TAC[REAL_LE_REFL; real_pow; REAL_MUL_RID; REAL_DIV_1];
    DISCH_TAC THEN ASM_CASES_TAC `x = &0` THENL
     [MP_TAC(SPEC_ALL MCLAURIN_ZERO) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `&0` THEN
      REWRITE_TAC[REAL_LE_REFL] THEN
      SUBGOAL_THEN `&0 pow n = &0` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[REAL_POW_EQ_0; GSYM (CONJUNCT1 LE); NOT_LE];
        REWRITE_TAC[REAL_ADD_RID; REAL_MUL_RZERO]];
      MP_TAC(SPEC_ALL MCLAURIN_ALL_LT) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC_ALL) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Version for exp.                                                          *)
(* ------------------------------------------------------------------------- *)

let MCLAURIN_EXP_LEMMA = prove
 (`((\n:num. exp) 0 = exp) /\
   (!m x. (((\n:num. exp) m) diffl ((\n:num. exp) (SUC m) x)) x)`,
  REWRITE_TAC[DIFF_EXP]);;

let MCLAURIN_EXP_LT = prove
 (`!x n. ~(x = &0) /\ 0 < n
         ==> ?t. &0 < abs(t) /\
                 abs(t) < abs(x) /\
                 (exp(x) = Sum(0,n)(\m. x pow m / &(FACT m)) +
                           (exp(t) / &(FACT n)) * x pow n)`,
  MP_TAC (MATCH_MP MCLAURIN_ALL_LT MCLAURIN_EXP_LEMMA) THEN
  REWRITE_TAC[REAL_EXP_0; real_div; REAL_MUL_AC; REAL_MUL_LID; REAL_MUL_RID]);;

let MCLAURIN_EXP_LE = prove
 (`!x n. ?t. abs(t) <= abs(x) /\
             (exp(x) = Sum(0,n)(\m. x pow m / &(FACT m)) +
                       (exp(t) / &(FACT n)) * x pow n)`,
  MP_TAC (MATCH_MP MCLAURIN_ALL_LE MCLAURIN_EXP_LEMMA) THEN
  REWRITE_TAC[REAL_EXP_0; real_div; REAL_MUL_AC; REAL_MUL_LID; REAL_MUL_RID]);;

(* ------------------------------------------------------------------------- *)
(* Version for ln(1 - x).                                                    *)
(* ------------------------------------------------------------------------- *)

let DIFF_LN_COMPOSITE = prove
 (`!g m x. (g diffl m)(x) /\ &0 < g x
           ==> ((\x. ln(g x)) diffl (inv(g x) * m))(x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFF_CHAIN THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIFF_LN THEN
  ASM_REWRITE_TAC[]);;

add_to_diff_net (SPEC_ALL DIFF_LN_COMPOSITE);;

let MCLAURIN_LN_POS = prove
 (`!x n.
     &0 < x /\ 0 < n
     ==> ?t. &0 < t /\
             t < x /\
             (ln(&1 + x) = Sum(0,n)
                           (\m. --(&1) pow (SUC m) * (x pow m) / &m) +
               --(&1) pow (SUC n) * x pow n / (&n * (&1 + t) pow n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `\x. ln(&1 + x)` MCLAURIN) THEN
  DISCH_THEN(MP_TAC o SPEC
    `\n x. if n = 0 then ln(&1 + x)
           else --(&1) pow (SUC n) *
                &(FACT(PRE n)) * inv((&1 + x) pow n)`) THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real`; `n:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NOT_SUC; REAL_ADD_RID; REAL_POW_ONE] THEN
  REWRITE_TAC[LN_1; REAL_INV_1; REAL_MUL_RID] THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `0 < n` THEN ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `!p. ~(p = 0) ==> (&(FACT(PRE p)) / &(FACT p) = inv(&p))`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[NOT_SUC; PRE] THEN
    REWRITE_TAC[real_div; FACT; GSYM REAL_OF_NUM_MUL] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN
    REWRITE_TAC[REAL_OF_NUM_EQ] THEN
    MP_TAC(SPEC `p:num` FACT_LT) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. (if p = 0 then &0 else --(&1) pow (SUC p) * &(FACT (PRE p))) /
        &(FACT p) = --(&1) pow (SUC p) * inv(&p)`
  (fun th -> REWRITE_TAC[th]) THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[REAL_INV_0; real_div; REAL_MUL_LZERO; REAL_MUL_RZERO];
      REWRITE_TAC[NOT_SUC] THEN
      REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM real_div] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[NOT_SUC]]; ALL_TAC] THEN
  SUBGOAL_THEN
    `!t. (--(&1) pow (SUC n) * &(FACT(PRE n)) * inv ((&1 + t) pow n)) /
         &(FACT n) * x pow n = --(&1) pow (SUC n) *
                               x pow n / (&n * (&1 + t) pow n)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_INV_MUL] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_AC] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `m:num` THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[] THENL
   [W(MP_TAC o SPEC `u:real` o DIFF_CONV o lhand o rator o snd) THEN
    REWRITE_TAC[PRE; real_pow; REAL_ADD_LID; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_MUL_RNEG; REAL_MUL_LNEG; REAL_MUL_RID] THEN
    REWRITE_TAC[FACT; REAL_MUL_RID; REAL_NEG_NEG] THEN
    DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC `&0 <= u` THEN REAL_ARITH_TAC;
    W(MP_TAC o SPEC `u:real` o DIFF_CONV o lhand o rator o snd) THEN
    SUBGOAL_THEN `~((&1 + u) pow m = &0)` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 <= u` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC (TAUT `(a = b) ==> a ==> b`) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
      REWRITE_TAC[REAL_ADD_LID; REAL_MUL_RID] THEN
      REWRITE_TAC[real_div; real_pow; REAL_MUL_LNEG; REAL_MUL_RNEG] THEN
      REWRITE_TAC[REAL_NEG_NEG; REAL_MUL_RID; REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `~(m = 0)` THEN SPEC_TAC(`m:num`,`p:num`) THEN
      INDUCT_TAC THEN REWRITE_TAC[NOT_SUC] THEN
      REWRITE_TAC[SUC_SUB1; PRE] THEN REWRITE_TAC[FACT] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
      REWRITE_TAC[real_pow; REAL_POW_2] THEN REWRITE_TAC[REAL_INV_MUL] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN
      REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[DE_MORGAN_THM] THEN DISJ1_TAC THEN
      UNDISCH_TAC `&0 <= u` THEN REAL_ARITH_TAC]]);;

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
  DISCH_THEN(MP_TAC o SPECL [`x:real`; `n:num`]) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  REWRITE_TAC[NOT_SUC; LN_1; REAL_POW_ONE] THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `0 < n` THEN ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[REAL_INV_1; REAL_MUL_RID; REAL_MUL_LID] THEN
  SUBGOAL_THEN `!p. ~(p = 0) ==> (&(FACT(PRE p)) / &(FACT p) = inv(&p))`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[NOT_SUC; PRE] THEN
    REWRITE_TAC[real_div; FACT; GSYM REAL_OF_NUM_MUL] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN
    REWRITE_TAC[REAL_OF_NUM_EQ] THEN
    MP_TAC(SPEC `p:num` FACT_LT) THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_NEG_0] THEN
  SUBGOAL_THEN `!p. (if p = 0 then &0 else &(FACT (PRE p))) / &(FACT p) =
                    inv(&p)`
  (fun th -> REWRITE_TAC[th]) THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[REAL_INV_0; real_div; REAL_MUL_LZERO];
      REWRITE_TAC[NOT_SUC] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[NOT_SUC]]; ALL_TAC] THEN
  SUBGOAL_THEN
    `!t. (&(FACT(PRE n)) * inv ((&1 - t) pow n)) / &(FACT n) * x pow n
         = x pow n / (&n * (&1 - t) pow n)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_INV_MUL] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_AC] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `m:num` THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[] THENL
   [W(MP_TAC o SPEC `u:real` o DIFF_CONV o lhand o rator o snd) THEN
    REWRITE_TAC[PRE; pow; FACT; REAL_SUB_LZERO] THEN
    REWRITE_TAC[REAL_MUL_RNEG; REAL_NEG_NEG; REAL_MUL_RID] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `x < &1` THEN UNDISCH_TAC `u:real <= x` THEN
    REAL_ARITH_TAC;
    W(MP_TAC o SPEC `u:real` o DIFF_CONV o lhand o rator o snd) THEN
    SUBGOAL_THEN `~((&1 - u) pow m = &0)` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `x < &1` THEN UNDISCH_TAC `u:real <= x` THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC (TAUT `(a = b) ==> a ==> b`) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[REAL_SUB_LZERO; real_div; PRE] THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
      REWRITE_TAC
       [REAL_MUL_RNEG; REAL_MUL_LNEG; REAL_NEG_NEG; REAL_MUL_RID] THEN
      UNDISCH_TAC `~(m = 0)` THEN SPEC_TAC(`m:num`,`p:num`) THEN
      INDUCT_TAC THEN REWRITE_TAC[NOT_SUC] THEN
      REWRITE_TAC[SUC_SUB1; PRE] THEN REWRITE_TAC[FACT] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
      REWRITE_TAC[real_pow; REAL_POW_2] THEN REWRITE_TAC[REAL_INV_MUL] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN
      REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `x < &1` THEN UNDISCH_TAC `u:real <= x` THEN
      REAL_ARITH_TAC]]);;
