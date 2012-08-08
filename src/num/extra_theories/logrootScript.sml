open HolKernel boolLib Parse

open Parse BasicProvers metisLib simpLib
open arithmeticTheory pairTheory combinTheory

val arith_ss = srw_ss() ++ numSimps.old_ARITH_ss
val Define = TotalDefn.Define


fun DECIDE_TAC (g as (asl,_)) =
    (MAP_EVERY UNDISCH_TAC (filter numSimps.is_arith_asm asl)
     THEN CONV_TAC Arith.ARITH_CONV) g
val DECIDE = EQT_ELIM o Arith.ARITH_CONV

val _ = new_theory "logroot";

val lt_mult2 = prove(``a < c /\ b < d  ==> a * b < c * d:num``,
  STRIP_TAC THEN
  `0 < d` by DECIDE_TAC THEN
  METIS_TAC [LE_MULT_LCANCEL, LT_MULT_RCANCEL, LESS_EQ_LESS_TRANS,
             LESS_OR_EQ]);

val exp_lemma2 = prove(``!a b r. 0 < r ==> a < b ==> a ** r < b ** r``,
  REPEAT STRIP_TAC THEN Induct_on `r` THEN RW_TAC arith_ss [EXP] THEN
  Cases_on `r = 0` THEN RW_TAC arith_ss [EXP] THEN MATCH_MP_TAC lt_mult2 THEN
  RW_TAC arith_ss []);

val exp_lemma3 = prove(``!a b r. 0 < r ==> a <= b ==> a ** r <= b ** r``,
  METIS_TAC [LESS_OR_EQ,exp_lemma2]);

val lem = prove(``1 < a /\ 0 < b ==> 1n < a * b``,
  Induct_on `b` THEN REWRITE_TAC [ADD1,LEFT_ADD_DISTRIB] THEN DECIDE_TAC);

val exp_lemma4 = prove(``!e a b. 1n < e ==> a < b ==> e ** a < e ** b``,
  REPEAT STRIP_TAC THEN
  `?p. b = SUC p + a` by
    (IMP_RES_TAC LESS_ADD_1 THEN Q.EXISTS_TAC `p` THEN DECIDE_TAC) THEN
  ASM_REWRITE_TAC [EXP_ADD,REWRITE_RULE [MULT_CLAUSES]
    (SPEC ``1n`` LT_MULT_RCANCEL),EXP] THEN CONJ_TAC THENL
    [ALL_TAC, MATCH_MP_TAC lem] THEN
    Cases_on `e` THEN REWRITE_TAC [ZERO_LESS_EXP] THEN DECIDE_TAC);

val exp_lemma5 = prove(``!e a b. 1n < e ==> a <= b ==> e ** a <= e ** b``,
  METIS_TAC [LESS_OR_EQ,exp_lemma4]);

val LT_EXP_ISO = store_thm("LT_EXP_ISO",
  ``!e a b. 1n < e ==> (a < b = e ** a < e ** b)``,
  PROVE_TAC [NOT_LESS,exp_lemma4,exp_lemma5]);

val LE_EXP_ISO = store_thm("LE_EXP_ISO",
  ``!e a b. 1n < e ==> (a <= b = e ** a <= e ** b)``,
  PROVE_TAC [exp_lemma4,exp_lemma5,LESS_OR_EQ,NOT_LESS]);

val EXP_LT_ISO = store_thm("EXP_LT_ISO",
  ``!a b r. 0 < r ==> (a < b = a ** r < b ** r)``,
  PROVE_TAC [NOT_LESS,exp_lemma3,exp_lemma2,LESS_OR_EQ,NOT_LESS]);

val EXP_LE_ISO = store_thm("EXP_LE_ISO",
  ``!a b r. 0 < r ==> (a <= b = a ** r <= b ** r)``,
  PROVE_TAC [NOT_LESS,exp_lemma3,exp_lemma2,LESS_OR_EQ,NOT_LESS]);

val ROOT_exists = store_thm("ROOT_exists",
  ``!r n. 0 < r ==> ?rt. rt ** r <= n /\ n < SUC rt ** r``,
  Induct_on `n` THEN RW_TAC arith_ss [] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM (Q.SPEC_THEN `r` MP_TAC) THEN
  SRW_TAC [][] THEN
  Cases_on `SUC n < SUC rt ** r` THEN1
    (Q.EXISTS_TAC `rt` THEN SRW_TAC [numSimps.ARITH_ss][]) THEN
  POP_ASSUM (ASSUME_TAC o SIMP_RULE (srw_ss()) [NOT_LESS]) THEN
  Q.EXISTS_TAC `SUC rt` THEN SRW_TAC [][] THEN
  `SUC n = SUC rt ** r` by RW_TAC arith_ss [] THEN
  RW_TAC arith_ss [])

val ROOT = new_specification("ROOT",
  ["ROOT"],
  SIMP_RULE (srw_ss()) [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] ROOT_exists);

val ROOT_UNIQUE = store_thm("ROOT_UNIQUE",
  ``!r n p. (p ** r <= n /\ n < SUC p ** r) ==> (ROOT r n = p)``,
  REPEAT STRIP_TAC THEN Cases_on `r = 0` THEN
  FULL_SIMP_TAC arith_ss [EXP,DECIDE ``~(r = 0n) = 0 < r``] THEN
  RW_TAC arith_ss [] THEN CCONTR_TAC THEN
  `ROOT r n < p \/ p < ROOT r n` by DECIDE_TAC THEN
  METIS_TAC [DECIDE ``a < b ==> SUC a <= b``,exp_lemma3,LESS_EQ_TRANS,
   DECIDE ``a <= b ==> ~(b < a:num)``,ROOT]);

val log_exists = prove(
  ``!a n. 1 < a /\ 0 < n ==> ?log. a ** log <= n /\ n < a ** SUC log``,
  REPEAT STRIP_TAC THEN
  Q.EXISTS_TAC `LEAST x. n < a ** SUC x` THEN
  CONV_TAC (UNBETA_CONV ``LEAST x. n < a ** SUC x``) THEN
  MATCH_MP_TAC whileTheory.LEAST_ELIM THEN CONJ_TAC THENL [
    SRW_TAC [][EXP] THEN
    `?m. n <= a ** m` by METIS_TAC [EXP_ALWAYS_BIG_ENOUGH] THEN
    Q.EXISTS_TAC `m` THEN MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN
    Q.EXISTS_TAC `a ** m` THEN SRW_TAC [][] THEN
    METIS_TAC [MULT_CLAUSES, LT_MULT_RCANCEL, EXP_EQ_0,
               DECIDE ``1 < x ==> ~(x = 0)``, DECIDE ``~(x = 0) = 0 < x``],
    Q.X_GEN_TAC `m` THEN SRW_TAC [][] THEN
    `(m = 0) \/ ?k. m = SUC k`
       by METIS_TAC [TypeBase.nchotomy_of ``:num``]
    THENL [
      RW_TAC arith_ss [EXP],
      FIRST_X_ASSUM (Q.SPEC_THEN `k` MP_TAC) THEN
      SRW_TAC [][EXP, NOT_LESS]
    ]
  ]);

val LOG_exists = save_thm(
  "LOG_exists",
  SIMP_RULE bool_ss [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM]
            log_exists);

val LOG = new_specification("LOG",["LOG"],LOG_exists);

val LOG_UNIQUE = store_thm("LOG_UNIQUE",
  ``!n:num p. (a ** p <= n /\ n < a ** SUC p) ==> (LOG a n = p)``,
  REPEAT STRIP_TAC THEN Cases_on `~(n = 0)` THEN Cases_on `~(a = 0)` THEN
  RW_TAC arith_ss [] THEN
  Cases_on `a = 1` THEN FULL_SIMP_TAC arith_ss [EXP] THEN
  ((`0 < n /\ 1 < a` by DECIDE_TAC THEN
    REPEAT (PAT_ASSUM ``~(a = b:num)`` (K (ALL_TAC)))) ORELSE
   (Cases_on `a` THEN FULL_SIMP_TAC arith_ss [EXP,ZERO_LESS_EXP])) THEN
  CCONTR_TAC THEN `LOG a n < p \/ p < LOG a n` by DECIDE_TAC THEN
  METIS_TAC [exp_lemma5,DECIDE ``a < b = SUC a <= b``,LESS_EQ_TRANS,
    NOT_LESS,LOG,EXP]);

val LOG_ADD1 = store_thm("LOG_ADD1",
  ``!n a b. 0n < n /\ 1n < a /\ 0 < b ==>
    (LOG a (a ** SUC n * b) = SUC (LOG a (a ** n * b)))``,
  RW_TAC arith_ss [] THEN MATCH_MP_TAC LOG_UNIQUE THEN
  `~(a = 0) /\ 0 < a /\ ~(b = 0)` by DECIDE_TAC THEN
  ASM_SIMP_TAC arith_ss [EXP] THEN
  ASM_REWRITE_TAC [GSYM MULT_ASSOC, LT_MULT_LCANCEL, LE_MULT_LCANCEL] THEN
  REWRITE_TAC [GSYM EXP] THEN MATCH_MP_TAC LOG THEN
  ASM_SIMP_TAC arith_ss [DECIDE ``0 < x = ~(x = 0)``, EXP_EQ_0]);

val square = prove(``a:num ** 2 = a * a``,
  REWRITE_TAC [EXP,EXP_1,TWO]);

val LOG_BASE = store_thm("LOG_BASE",``!a. 1n < a ==> (LOG a a = 1)``,
  RW_TAC arith_ss [] THEN MATCH_MP_TAC LOG_UNIQUE THEN Induct_on `a` THEN
  RW_TAC arith_ss [LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB,EXP_ADD,ADD1,EXP_1,square]);

fun AC_THM term = CONV_RULE bool_EQ_CONV (AC_CONV (MULT_ASSOC,MULT_COMM) term);
val ARITH_ss = numSimps.ARITH_ss

val LOG_EXP = store_thm("LOG_EXP",
  ``!n a b. 1n < a /\ 0 < b ==> (LOG a (a ** n * b) = n + LOG a b)``,
  REPEAT STRIP_TAC  THEN MATCH_MP_TAC LOG_UNIQUE THEN
  RW_TAC arith_ss [EXP, EXP_ADD, EXP_EQ_0] THENL [
    METIS_TAC [LOG],
    Q_TAC SUFF_TAC `a ** n * b < a ** n * (a * a ** LOG a b)`
          THEN1 SIMP_TAC bool_ss [AC MULT_COMM MULT_ASSOC] THEN
    SRW_TAC [ARITH_ss][GSYM NOT_ZERO_LT_ZERO, EXP_EQ_0] THEN
    METIS_TAC [EXP, LOG]
  ]);

val LOG_1 = store_thm("LOG_1",``!a. 1n < a ==> (LOG a 1 = 0)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LOG_UNIQUE THEN
  REWRITE_TAC [EXP] THEN DECIDE_TAC);

val LOG_DIV = store_thm("LOG_DIV",
  ``!a x. 1n < a /\ a <= x ==> (LOG a x = 1 + LOG a (x DIV a))``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LOG_UNIQUE THEN
  REWRITE_TAC [EXP_ADD,DECIDE ``SUC (1 + a) = 1 + SUC a``,EXP_1] THEN
  RW_TAC bool_ss [GSYM (SPEC ``a:num ** b`` MULT_COMM),GSYM X_LE_DIV,
    GSYM DIV_LT_X,DECIDE ``1 < a ==> 0n < a``,LOG] THEN
  PROVE_TAC [X_LE_DIV,MULT_CLAUSES,DECIDE ``1 < a ==> 0n < a``,
    DECIDE ``1 <= a ==> 0n < a``,LOG]);

val LOG_ADD = store_thm("LOG_ADD",
  ``!a b c. 1 < a /\ b < a ** c ==> (LOG a (b + a ** c) = c)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LOG_UNIQUE THEN
  CONJ_TAC THENL [DECIDE_TAC,REWRITE_TAC [EXP]] THEN
  MATCH_MP_TAC (DECIDE ``!a b c. a < b /\ b <= c ==> a < c:num``) THEN
  Q.EXISTS_TAC `2 * a ** c` THEN CONJ_TAC THENL
  [REWRITE_TAC [TIMES2,LT_ADD_RCANCEL],
   REWRITE_TAC [LE_MULT_RCANCEL]] THEN DECIDE_TAC);

val LOG_LE_MONO = store_thm("LOG_LE_MONO",
  ``!a x y. 1 < a /\ 0 < x ==> x <= y ==> LOG a x <= LOG a y``,
  REPEAT STRIP_TAC THEN REWRITE_TAC
    [UNDISCH (SPECL [``a:num``,``LOG a x``,``SUC (LOG a y)``] LT_EXP_ISO),
     DECIDE ``a <= b = a < SUC b``] THEN
  MATCH_MP_TAC
    (DECIDE ``!a b c d. a <= b /\ b <= c /\ c < d ==> a < d:num``) THEN
  Q.EXISTS_TAC `x` THEN Q.EXISTS_TAC `y` THEN
  METIS_TAC [LOG,LESS_TRANS,LESS_OR_EQ]);

val LOG_RWT = store_thm("LOG_RWT",
  ``!m n. 1 < m /\ 0 < n ==>
     (LOG m n = if n < m then 0 else SUC (LOG m (n DIV m)))``,
  SRW_TAC [ARITH_ss] [LOG_DIV, ADD1, LOG_UNIQUE, EXP]);

val less_lemma1 = prove(``a <= c /\ b <= d ==> a * b <= c * d:num``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LESS_EQ_TRANS THEN
  Q.EXISTS_TAC `c * b` THEN
  REWRITE_TAC [LE_MULT_LCANCEL,LE_MULT_RCANCEL] THEN DECIDE_TAC);

val div_lemma1 = prove(
  ``!a b c. 0 < b /\ 0 < c ==> (a DIV b) ** c <= a ** c DIV b ** c``,
  REPEAT STRIP_TAC THEN Induct_on `c` THENL [
    DECIDE_TAC,
    STRIP_TAC THEN Cases_on `0 < c` THENL [
      FULL_SIMP_TAC bool_ss [EXP],
      `c = 0` by DECIDE_TAC] THEN
    ASM_REWRITE_TAC [EXP,LESS_EQ_REFL,MULT_CLAUSES]] THEN
  MATCH_MP_TAC LESS_EQ_TRANS THEN
  Q.EXISTS_TAC `(a DIV b) * (a ** c DIV b ** c)` THEN
  RW_TAC bool_ss [LE_MULT_LCANCEL] THEN
  `0 < b ** c` by
    (Cases_on `b` THEN REWRITE_TAC [ZERO_LESS_EXP] THEN DECIDE_TAC) THEN
  RW_TAC bool_ss [GSYM (CONV_RULE (ONCE_DEPTH_CONV (REWR_CONV MULT_COMM)) DIV_DIV_DIV_MULT),X_LE_DIV] THEN
  ONCE_REWRITE_TAC [AC_THM ``a * b * c * d = (a * c) * (b * d:num)``] THEN
  MATCH_MP_TAC less_lemma1 THEN
  METIS_TAC [DIVISION,DECIDE ``(a = b + c) ==> b <= a:num``]);

val square_add_lemma = prove(``a ** e * b ** e = (a * b:num) ** e``,
  Induct_on `e` THEN RW_TAC arith_ss [EXP] THEN
  METIS_TAC [MULT_COMM,MULT_ASSOC]);

val ROOT_DIV = store_thm("ROOT_DIV",
  ``!r x y. 0 < r /\ 0 < y ==> (ROOT r x DIV y = ROOT r (x DIV (y ** r)))``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC (GSYM ROOT_UNIQUE) THEN
  `0 < y ** r` by
    (Cases_on `y` THEN REWRITE_TAC [ZERO_LESS_EXP] THEN DECIDE_TAC) THEN
  CONJ_TAC THENL [
    MATCH_MP_TAC LESS_EQ_TRANS THEN
    EXISTS_TAC ``(ROOT r x) ** r DIV y ** r`` THEN
    RW_TAC bool_ss [div_lemma1] THEN
    METIS_TAC [DIV_LE_MONOTONE,ROOT],
    RW_TAC bool_ss [DIV_LT_X] THEN
    MATCH_MP_TAC (DECIDE ``!a b c. a < b /\ b <= c ==> a < c:num``) THEN
    EXISTS_TAC ``SUC (ROOT r x) ** r`` THEN RW_TAC bool_ss [ROOT] THEN
    REWRITE_TAC [square_add_lemma] THEN
    MATCH_MP_TAC (UNDISCH (SPEC_ALL exp_lemma3)) THEN
    REWRITE_TAC [ADD1,RIGHT_ADD_DISTRIB,MULT_CLAUSES] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) bool_rewrites
      [SPEC ``ROOT r x`` (UNDISCH (SPEC ``y:num`` DIVISION))] THEN
    REWRITE_TAC [GSYM ADD_ASSOC,LE_ADD_LCANCEL] THEN
    METIS_TAC [DECIDE ``a < b ==> a + 1n <= b``,DIVISION]])

val ROOT_LE_MONO = store_thm("ROOT_LE_MONO",
  ``!r x y. 0 < r ==> x <= y ==> ROOT r x <= ROOT r y``,
  REPEAT STRIP_TAC THEN REWRITE_TAC [DECIDE ``a <= b = a < SUC b``] THEN
  ONCE_REWRITE_TAC [UNDISCH (SPEC_ALL EXP_LT_ISO)] THEN
  MATCH_MP_TAC
    (DECIDE ``!a b c d. a <= b /\ b <= c /\ c < d ==> a < d:num``) THEN
  Q.EXISTS_TAC `x` THEN Q.EXISTS_TAC `y` THEN RW_TAC bool_ss [ROOT]);

val EXP_MUL = store_thm("EXP_MUL",``(a ** b) ** c = a ** (b * c)``,
  Induct_on `c` THEN
  REWRITE_TAC [MULT_CLAUSES,EXP_ADD,ADD1,LEFT_ADD_DISTRIB,EXP,EXP_1] THEN
  PROVE_TAC []);

val LOG_ROOT = store_thm("LOG_ROOT",
 ``1 < a /\ 0 < x /\ 0 < r ==> (LOG a (ROOT r x) = (LOG a x) DIV r)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LOG_UNIQUE THEN CONJ_TAC THENL [
    REWRITE_TAC [DECIDE ``a <= b = a < SUC b``] THEN
    ONCE_REWRITE_TAC [UNDISCH (SPEC_ALL EXP_LT_ISO)] THEN
    MATCH_MP_TAC (DECIDE ``!a b c. a <= b /\ b < c ==> a < c:num``) THEN
    Q.EXISTS_TAC `x` THEN RW_TAC bool_ss [ROOT,EXP_MUL] THEN
    MATCH_MP_TAC LESS_EQ_TRANS THEN Q.EXISTS_TAC `a ** (LOG a x)` THEN
    RW_TAC bool_ss [LOG,GSYM LE_EXP_ISO],
    ONCE_REWRITE_TAC [UNDISCH (SPEC_ALL EXP_LT_ISO)] THEN
    MATCH_MP_TAC (DECIDE ``!a b c d. a <= b /\ b < c ==> a < c:num``) THEN
    Q.EXISTS_TAC `x` THEN RW_TAC bool_ss [ROOT,EXP_MUL] THEN
    MATCH_MP_TAC (DECIDE ``!a b c. a < b /\ b <= c ==> a < c:num``) THEN
    Q.EXISTS_TAC `a ** SUC (LOG a x)` THEN
    RW_TAC bool_ss [LOG,GSYM LE_EXP_ISO] THEN
    RW_TAC bool_ss [ADD1,RIGHT_ADD_DISTRIB,MULT_CLAUSES] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) bool_rewrites
      [SPEC ``LOG a x`` (UNDISCH (SPEC ``r:num`` DIVISION))] THEN
    REWRITE_TAC [LT_ADD_LCANCEL,DECIDE ``a + 1 <= b = a < b:num``]] THEN
    METIS_TAC [DIVISION,DECIDE ``(a = b + c) ==> (b <= a:num)``]);

val zero_lt_twoexp = prove(``!n. 0 < 2 ** n``,
 Induct THEN REWRITE_TAC [EXP] THEN TRY (MATCH_MP_TAC LESS_MULT2) THEN
 DECIDE_TAC);

val LOG2_MOD = store_thm("LOG_MOD",
  ``0 < n ==> (n = 2 ** LOG 2 n + n MOD 2 ** LOG 2 n)``,
  REPEAT STRIP_TAC THEN
  Cases_on `?b c. (n = b + 2 ** c) /\ b < 2 ** c` THEN RW_TAC bool_ss [] THENL [
    RW_TAC bool_ss [LOG_ADD,DECIDE ``1 < 2n``] THEN
    METIS_TAC [ADD_MODULUS_LEFT,ADD_COMM,
      DECIDE ``b < a ==> 0n < a``,LESS_MOD,zero_lt_twoexp],
    POP_ASSUM (fn th => CCONTR_TAC THEN MP_TAC th) THEN RW_TAC arith_ss [] THEN
    POP_ASSUM (K ALL_TAC)] THEN
    Induct_on `n` THEN RW_TAC arith_ss [] THEN
    Cases_on `n` THEN FULL_SIMP_TAC arith_ss [] THENL [
      Q.EXISTS_TAC `0` THEN Q.EXISTS_TAC `0` THEN RW_TAC arith_ss [EXP],
      Cases_on `SUC b < 2 ** c` THENL [
        Q.EXISTS_TAC `SUC b` THEN Q.EXISTS_TAC `c` THEN RW_TAC arith_ss [],
        FULL_SIMP_TAC arith_ss [NOT_LESS] THEN
        `SUC b = 2 ** c` by DECIDE_TAC THEN
         ASM_REWRITE_TAC [DECIDE ``SUC (a + b) = SUC a + b``]]] THEN
    Q.EXISTS_TAC `0` THEN Q.EXISTS_TAC `SUC c` THEN RW_TAC arith_ss [EXP]);

val lem = prove(``0 < r ==> (0 ** r = 0)``, RW_TAC arith_ss [EXP_EQ_0])

val ROOT_COMPUTE = store_thm("ROOT_COMPUTE",
  ``!r n. 0 < r ==> (ROOT r 0 = 0) /\
     (ROOT r n = let x = 2 * ROOT r (n DIV 2 ** r) in
                   if n < SUC x ** r then x else SUC x)``,
  RW_TAC (arith_ss ++ boolSimps.LET_ss) [] THEN MATCH_MP_TAC ROOT_UNIQUE THEN
  CONJ_TAC THEN
  FULL_SIMP_TAC arith_ss [NOT_LESS,EXP_1,lem] THEN
  MAP_FIRST MATCH_MP_TAC
    [LESS_EQ_TRANS,DECIDE ``!a b c. a < b /\ b <= c ==> a < c``] THENL [
     Q.EXISTS_TAC `ROOT r n ** r`,
     Q.EXISTS_TAC `SUC (ROOT r n) ** r`] THEN
  RW_TAC arith_ss [ROOT,GSYM EXP_LE_ISO,GSYM ROOT_DIV,DECIDE ``0 < 2n``] THEN
  METIS_TAC [DIVISION,MULT_COMM,DECIDE ``0 < 2n``,
    DECIDE ``(a = b + c) ==> b <= a:num``,ADD1,LE_ADD_LCANCEL,
    DECIDE ``a <= 1 = a < 2n``]);

val SQRTd_def = Define `SQRTd n = (ROOT 2 n,n - (ROOT 2 n * ROOT 2 n))`;

val iSQRTd_def = Define `iSQRTd (x,n) =
  let p = SQRTd n in
  let next = 4 * SND p + x in
  let ndiff = 4 * FST p + 1 in
  if next < ndiff then (2 * FST p,next) else (2 * FST p + 1,next - ndiff)`;

val sqrt_zero = prove(``ROOT 2 0 = 0``,RW_TAC arith_ss [ROOT_COMPUTE]);
val sqrt_compute = SIMP_RULE arith_ss [] (SPEC ``2n`` ROOT_COMPUTE);


val mult_eq_lemma = prove(``2 * a * (2 * a) = 4n * (a * a)``,
  METIS_TAC [MULT_COMM,MULT_ASSOC,DECIDE ``2 * 2 = 4n``]);

val iSQRT_lemma = prove(``SQRTd m = iSQRTd (m MOD 4,m DIV 4)``,
  REWRITE_TAC [SQRTd_def] THEN REWRITE_TAC [iSQRTd_def,FST,SND] THEN
  REWRITE_TAC [SQRTd_def] THEN
  RW_TAC (bool_ss ++ boolSimps.LET_ss) [FST,SND] THEN
   (SUBGOAL_THEN ``(4 * (ROOT 2 (m DIV 4) * ROOT 2 (m DIV 4)) <= m /\
                         ROOT 2 (m DIV 4) * ROOT 2 (m DIV 4) <= m DIV 4) /\
                         ROOT 2 m * ROOT 2 m <= m`` (fn th =>
    RW_TAC bool_ss [] THEN
    FULL_SIMP_TAC bool_ss [
      SIMP_RULE arith_ss [] (SPEC ``4n`` (GSYM DIVISION)),th,
        DECIDE ``a <= b ==> (4 * (b - a) + c = (b * 4 + c) - (4 * a))``,
        SUB_CANCEL, DECIDE ``a <= b ==> (b - a <= c = b < a + (c + 1n))``] THEN
      ASSUME_TAC (CONJUNCT2 th)) THEN1
    METIS_TAC [EXP,DECIDE ``2 = SUC 1``,EXP_1,ROOT,DECIDE ``0 < 2n``,
      DECIDE ``0 < 4n``,MULT_COMM,X_LE_DIV] THEN
    Cases_on `m = 0` THEN RW_TAC arith_ss [sqrt_zero] THEN
    RW_TAC arith_ss [SUB_CANCEL,
      DECIDE ``~(m < 4 * a + (4 * b + 1)) ==> 4 * a + (2 * b + 1) <= m``] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) bool_rewrites
     [CONJUNCT2 (SPEC_ALL sqrt_compute)] THEN
    RW_TAC (arith_ss ++ boolSimps.LET_ss)
      [mult_eq_lemma,ADD1,LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB] THEN
    PAT_ASSUM ``~(a < b:num)`` MP_TAC THEN
    FULL_SIMP_TAC arith_ss [ADD1,
      METIS_PROVE [DECIDE ``SUC 1 = 2``,EXP,EXP_1] ``a ** 2 = a * a:num``,
      LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB,mult_eq_lemma]));

val numeral_sqrt1 = prove(``
  (SQRTd ZERO = (0,0)) /\
  (SQRTd (BIT1 ZERO)= (1,0)) /\
  (SQRTd (BIT2 ZERO)= (1,1)) /\
  (SQRTd (BIT1 (BIT1 n)) = iSQRTd (3,n)) /\
  (SQRTd (BIT2 (BIT1 n)) = iSQRTd (0,SUC n)) /\
  (SQRTd (BIT1 (BIT2 n)) = iSQRTd (1,SUC n)) /\
  (SQRTd (BIT2 (BIT2 n)) = iSQRTd (2,SUC n)) /\
  (SQRTd (SUC (BIT1 (BIT1 n))) = iSQRTd (0,SUC n)) /\
  (SQRTd (SUC (BIT2 (BIT1 n))) = iSQRTd (1,SUC n)) /\
  (SQRTd (SUC (BIT1 (BIT2 n))) = iSQRTd (2,SUC n)) /\
  (SQRTd (SUC (BIT2 (BIT2 n))) = iSQRTd (3,SUC n))``,
  REWRITE_TAC [BIT1,BIT2,ALT_ZERO,ADD_CLAUSES,NUMERAL_DEF] THEN
  RW_TAC arith_ss [iSQRT_lemma,ADD1] THENL [
    RW_TAC (arith_ss ++ boolSimps.LET_ss) [iSQRTd_def,SQRTd_def,sqrt_zero],
    RW_TAC (arith_ss ++ boolSimps.LET_ss) [iSQRTd_def,SQRTd_def,sqrt_zero],
    RW_TAC (arith_ss ++ boolSimps.LET_ss) [iSQRTd_def,SQRTd_def,sqrt_zero],
    ALL_TAC,ALL_TAC,ALL_TAC,ALL_TAC,ALL_TAC,ALL_TAC,ALL_TAC,ALL_TAC] THEN
 METIS_TAC [DIV_MULT,MOD_MULT,MULT_COMM,
   DECIDE ``0 < 4n /\ 1 < 4n /\ 2 < 4n /\ 3 < 4n``,
   DECIDE ``(4 * n + 4 = 4 * (n + 1) + 0) /\ (4 * n + 5 = 4 * (n + 1) + 1) /\
            (4 * n + 6 = 4 * (n + 1) + 2) /\ (4 * n + 7 = 4 * (n + 1) + 3)``]);

val iSQRT0_def = Define `iSQRT0 n =
  let p = SQRTd n in
  let d = SND p - FST p in
   if d = 0 then (2 * FST p,4 * SND p) else (SUC (2 * FST p),4 * d - 1)`;

val iSQRT1_def = Define `iSQRT1 n =
  let p = SQRTd n in
  let d = (SUC (SND p) - FST p) in
    if d = 0 then (2 * FST p, SUC (4 * SND p))
             else (SUC (2 * FST p),4 * (d - 1))`;

val iSQRT2_def = Define `iSQRT2 n =
  let p = SQRTd n in
  let d = 2 * FST p in
  let c = SUC (2 * SND p) in
  let e = c - d in
  if e = 0 then (d,2 * c) else (SUC d, 2 * e - 1)`;

val iSQRT3_def = Define `iSQRT3 n =
  let p = SQRTd n in
  let d = 2 * FST p in
  let c = SUC (2 * (SND p)) in
  let e = SUC c - d in
    if e = 0 then (d,SUC (2 * c)) else (SUC d, 2 * (e - 1))`;


val numeral_sqrt2 = prove(``
  (SQRTd ZERO = (0,0)) /\
  (SQRTd (BIT1 ZERO) = (1,0)) /\
  (SQRTd (BIT2 ZERO) = (1,1)) /\
  (SQRTd (BIT1 (BIT1 n)) = iSQRT3 n) /\
  (SQRTd (BIT2 (BIT1 n)) = iSQRT0 (SUC n)) /\
  (SQRTd (BIT1 (BIT2 n)) = iSQRT1 (SUC n)) /\
  (SQRTd (BIT2 (BIT2 n)) = iSQRT2 (SUC n)) /\
  (SQRTd (SUC (BIT1 (BIT1 n))) = iSQRT0 (SUC n)) /\
  (SQRTd (SUC (BIT2 (BIT1 n))) = iSQRT1 (SUC n)) /\
  (SQRTd (SUC (BIT1 (BIT2 n))) = iSQRT2 (SUC n)) /\
  (SQRTd (SUC (BIT2 (BIT2 n))) = iSQRT3 (SUC n))``,
  RW_TAC(arith_ss ++ boolSimps.LET_ss) [numeral_sqrt1] THEN
  REWRITE_TAC [iSQRT0_def,iSQRT1_def,iSQRT2_def,iSQRT3_def] THEN
  RW_TAC (arith_ss ++ boolSimps.LET_ss) [iSQRTd_def,ADD1]);


val numeral_root2 = store_thm("numeral_root2",
  ``ROOT 2 (NUMERAL n) = FST (SQRTd n)``,
  REWRITE_TAC [FST,SQRTd_def,NUMERAL_DEF]);


(*

Testing:

open reduceLib computeLib;

val compset1 = num_compset();

val _ = add_thms [numeral_root2,numeral_sqrt2,FST,SND,iSQRT0_def,iSQRT1_def,
                  iSQRT2_def,iSQRT3_def] compset1;

val _ = time (CBV_CONV compset2) ``SQRT 123456789123456789123456789``;
val _ = time (CBV_CONV compset1) ``ROOT 2 123456789123456789123456789``;


val list = map (rand o concl)
  (map (fn x => REDUCE_CONV (mk_mult(``12345678912345678912345678n``,
                             term_of_int x))) (for 0 60 I));

time (map (fn x => CBV_CONV compset1 (mk_comb(``ROOT 2``,x)))) list;
time (map (fn x => CBV_CONV compset2 (mk_comb(``SQRT``,x)))) list;


val compset2 = num_compset();

val SQRT_def = Define `SQRT x = ROOT 2 x`;

val sqrt_thm = prove(
  ``!x p. SQRT x = let q = p * p in
      if (q <= x /\ x < q + 2 * p + 1) then p else SQRT x``,
  RW_TAC (arith_ss ++ boolSimps.LET_ss) [SQRT_def] THEN
  MATCH_MP_TAC ROOT_UNIQUE THEN
  RW_TAC bool_ss [ADD1,EXP_ADD,EXP_1,DECIDE ``2 = SUC 1``,
    LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB] THEN
  DECIDE_TAC);


val dest_sqrt = dest_monop ``$SQRT`` (mk_HOL_ERR "bitsLib" "dest_log2" "");

fun cbv_SQRT_CONV tm =
  let open Arbnum numSyntax
      val x = dest_sqrt tm
      val n = dest_numeral x
      fun sqrt a n = if (a * a <= n andalso n < (a + one) * (a + one)) then a
                     else sqrt (div2 (Arbnum.div (a * a + n,a))) n;
      val p = sqrt one n
      in Drule.SPECL [x, mk_numeral p] sqrt_thm
      end
	 handle HOL_ERR _ => raise (mk_HOL_ERR "ieeeLib" "cbv_SQRT" "")
	      | Domain => raise (mk_HOL_ERR "ieeeLib" "cbv_SQRT" "");

val _ = add_conv (``$SQRT``, 1, cbv_SQRT_CONV) compset2;

time (CBV_CONV compset2) ``SQRT 123456789123456789123456789``;
time (CBV_CONV compset1) ``ROOT 2 123456789123456789123456789``;


*)


val _ = export_theory();
