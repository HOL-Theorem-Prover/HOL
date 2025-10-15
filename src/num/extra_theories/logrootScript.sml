Theory logroot[bare]
Ancestors
  arithmetic pair combin
Libs
  HolKernel boolLib Parse BasicProvers metisLib simpLib
  computeLib

(* ----------------------------------------------------------------------- *)

fun AC_THM term = CONV_RULE bool_EQ_CONV (AC_CONV (MULT_ASSOC, MULT_COMM) term)
val arith_ss = srw_ss() ++ numSimps.old_ARITH_ss
val ARITH_ss = numSimps.ARITH_ss

fun DECIDE_TAC (g as (asl, _)) =
   (MAP_EVERY UNDISCH_TAC (filter numSimps.is_arith_asm asl)
    THEN CONV_TAC Arith.ARITH_CONV) g

val decide_tac = DECIDE_TAC;
val metis_tac = METIS_TAC;

val DECIDE = EQT_ELIM o Arith.ARITH_CONV;
val rw = SRW_TAC [ARITH_ss];
val std_ss = arith_ss;
val qabbrev_tac = Q.ABBREV_TAC;
val qexists_tac = Q.EXISTS_TAC;
fun simp l = ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) l;
fun fs l = FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) l;
fun rfs l = REV_FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) l;

(* ----------------------------------------------------------------------- *)

val lt_mult2 = Q.prove(
   `a < c /\ b < d  ==> a * b < c * d:num`,
   STRIP_TAC
   THEN `0 < d` by DECIDE_TAC
   THEN METIS_TAC [LE_MULT_LCANCEL, LT_MULT_RCANCEL, LESS_EQ_LESS_TRANS,
                   LESS_OR_EQ]);

(* ------------------------------------------------------------------------- *)
(* Exponential Theorems                                                      *)
(* ------------------------------------------------------------------------- *)

val exp_lemma2 = Q.prove(
   `!a b r. 0 < r ==> a < b ==> a ** r < b ** r`,
   REPEAT STRIP_TAC
   THEN Induct_on `r`
   THEN RW_TAC arith_ss [EXP]
   THEN Cases_on `r = 0`
   THEN RW_TAC arith_ss [EXP]
   THEN MATCH_MP_TAC lt_mult2
   THEN RW_TAC arith_ss []);

val exp_lemma3 =
  METIS_PROVE [LESS_OR_EQ, exp_lemma2]
    ``!a b r. 0 < r ==> a <= b ==> a ** r <= b ** r``;

val lem = Q.prove(
   `1 < a /\ 0 < b ==> 1n < a * b`,
   Induct_on `b`
   THEN REWRITE_TAC [ADD1, LEFT_ADD_DISTRIB]
   THEN DECIDE_TAC);

val exp_lemma4 = Q.prove(
   `!e a b. 1n < e ==> a < b ==> e ** a < e ** b`,
   REPEAT STRIP_TAC
   THEN `?p. b = SUC p + a`
     by (IMP_RES_TAC LESS_ADD_1
         THEN Q.EXISTS_TAC `p`
         THEN DECIDE_TAC)
   THEN ASM_REWRITE_TAC
          [EXP_ADD, EXP,
           REWRITE_RULE [MULT_CLAUSES] (SPEC ``1n`` LT_MULT_RCANCEL)]
   THEN CONJ_TAC
   THENL [ALL_TAC, MATCH_MP_TAC lem]
   THEN Cases_on `e`
   THEN REWRITE_TAC [ZERO_LESS_EXP]
   THEN DECIDE_TAC);

val exp_lemma5 =
   METIS_PROVE [LESS_OR_EQ, exp_lemma4]
      ``!e a b. 1n < e ==> a <= b ==> e ** a <= e ** b``;

Theorem LT_EXP_ISO:
    !e a b. 1n < e ==> (a < b <=> e ** a < e ** b)
Proof
   PROVE_TAC [NOT_LESS, exp_lemma4, exp_lemma5]
QED

Theorem LE_EXP_ISO:
    !e a b. 1n < e ==> (a <= b <=> e ** a <= e ** b)
Proof
   PROVE_TAC [exp_lemma4, exp_lemma5, LESS_OR_EQ, NOT_LESS]
QED

Theorem EXP_LT_ISO:
    !a b r. 0 < r ==> (a < b <=> a ** r < b ** r)
Proof
   PROVE_TAC [NOT_LESS, exp_lemma3, exp_lemma2, LESS_OR_EQ, NOT_LESS]
QED

Theorem EXP_LE_ISO:
    !a b r. 0 < r ==> (a <= b <=> a ** r <= b ** r)
Proof
   PROVE_TAC [NOT_LESS, exp_lemma3, exp_lemma2, LESS_OR_EQ, NOT_LESS]
QED

(* Theorem: 0 < m ==> ((n ** m = n) <=> ((m = 1) \/ (n = 0) \/ (n = 1))) *)
(* Proof:
   If part: n ** m = n ==> n = 0 \/ n = 1
      By contradiction, assume n <> 0 /\ n <> 1.
      Then ?k. m = SUC k            by num_CASES, 0 < m
        so  n ** SUC k = n          by n ** m = n
        or  n * n ** k = n          by EXP
       ==>      n ** k = 1          by MULT_EQ_SELF, 0 < n
       ==>      n = 1 or k = 0      by EXP_EQ_1
       ==>      n = 1 or m = 1,
      These contradict n <> 1 and m <> 1.
   Only-if part: n ** 1 = n /\ 0 ** m = 0 /\ 1 ** m = 1
      These are true   by EXP_1, ZERO_EXP.
*)
Theorem EXP_EQ_SELF:
    !n m. 0 < m ==> ((n ** m = n) <=> ((m = 1) \/ (n = 0) \/ (n = 1)))
Proof
  rw_tac std_ss[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `m <> 0` by decide_tac >>
    `?k. m = SUC k` by metis_tac[num_CASES] >>
    `n * n ** k = n` by fs[EXP] >>
    `n ** k = 1` by metis_tac[MULT_EQ_SELF, NOT_ZERO_LT_ZERO] >>
    fs[EXP_EQ_1],
    rw[],
    rw[],
    rw[]
  ]
QED

(* Obtain a theorem *)
Theorem EXP_LE = X_LE_X_EXP |> GEN ``x:num`` |> SPEC ``b:num`` |> GEN_ALL;
(* val EXP_LE = |- !n b. 0 < n ==> b <= b ** n: thm *)

(* Theorem: 1 < b /\ 1 < n ==> b < b ** n *)
(* Proof:
   By contradiction, assume ~(b < b ** n).
   Then b ** n <= b       by arithmetic
    But b <= b ** n       by EXP_LE, 0 < n
    ==> b ** n = b        by EQ_LESS_EQ
    ==> b = 1 or n = 0 or n = 1.
   All these contradict 1 < b and 1 < n.
*)
Theorem EXP_LT:
    !n b. 1 < b /\ 1 < n ==> b < b ** n
Proof
  spose_not_then strip_assume_tac >>
  `b <= b ** n` by rw[EXP_LE] >>
  `b ** n = b` by decide_tac >>
  rfs[EXP_EQ_SELF]
QED

(* Theorem: 0 < a /\ n < m /\ (a ** n * b = a ** m * c) ==> ?d. 0 < d /\ (b = a ** d * c) *)
(* Proof:
   Let d = m - n.
   Then 0 < d, and  m = n + d       by arithmetic
    and 0 < a ==> a ** n <> 0       by EXP_EQ_0
      a ** n * b
    = a ** (n + d) * c              by m = n + d
    = (a ** n * a ** d) * c         by EXP_ADD
    = a ** n * (a ** d * c)         by MULT_ASSOC
   The result follows               by MULT_LEFT_CANCEL
*)
Theorem EXP_LCANCEL:
    !a b c n m. 0 < a /\ n < m /\ (a ** n * b = a ** m * c) ==> ?d. 0 < d /\ (b = a ** d * c)
Proof
  rpt strip_tac >>
  `0 < m - n /\ (m = n + (m - n))` by decide_tac >>
  qabbrev_tac `d = m - n` >>
  `a ** n <> 0` by metis_tac[EXP_EQ_0, NOT_ZERO_LT_ZERO] >>
  metis_tac[EXP_ADD, MULT_ASSOC, MULT_LEFT_CANCEL]
QED

(* Theorem: 0 < a /\ n < m /\ (a ** n * b = a ** m * c) ==> ?d. 0 < d /\ (b = a ** d * c) *)
(* Proof: by EXP_LCANCEL, MULT_COMM. *)
Theorem EXP_RCANCEL:
    !a b c n m. 0 < a /\ n < m /\ (b * a ** n = c * a ** m) ==> ?d. 0 < d /\ (b = c * a ** d)
Proof
  metis_tac[EXP_LCANCEL, MULT_COMM]
QED

(*
EXP_POS      |- !m n. 0 < m ==> 0 < m ** n
ONE_LT_EXP   |- !x y. 1 < x ** y <=> 1 < x /\ 0 < y
ZERO_LT_EXP  |- 0 < x ** y <=> 0 < x \/ (y = 0)
*)

(* Theorem: 0 < m ==> 1 <= m ** n *)
(* Proof:
   0 < m ==>  0 < m ** n      by EXP_POS
          or 1 <= m ** n      by arithmetic
*)
Theorem ONE_LE_EXP:
    !m n. 0 < m ==> 1 <= m ** n
Proof
  metis_tac[EXP_POS, DECIDE``!x. 0 < x <=> 1 <= x``]
QED

(* ------------------------------------------------------------------------- *)
(* ROOT and LOG                                                              *)
(* ------------------------------------------------------------------------- *)

Theorem ROOT_exists:
    !r n. 0 < r ==> ?rt. rt ** r <= n /\ n < SUC rt ** r
Proof
   Induct_on `n`
   THEN RW_TAC arith_ss []
   THEN REPEAT STRIP_TAC
   THEN FIRST_X_ASSUM (Q.SPEC_THEN `r` MP_TAC)
   THEN SRW_TAC [][]
   THEN Cases_on `SUC n < SUC rt ** r`
   THEN1 (Q.EXISTS_TAC `rt` THEN SRW_TAC [numSimps.ARITH_ss][])
   THEN POP_ASSUM (ASSUME_TAC o SIMP_RULE (srw_ss()) [NOT_LESS])
   THEN Q.EXISTS_TAC `SUC rt`
   THEN SRW_TAC [][]
   THEN `SUC n = SUC rt ** r` by RW_TAC arith_ss []
   THEN RW_TAC arith_ss []
QED

val ROOT = new_specification("ROOT", ["ROOT"],
   SIMP_RULE (srw_ss()) [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] ROOT_exists);

Theorem ROOT_UNIQUE:
    !r n p. (p ** r <= n /\ n < SUC p ** r) ==> (ROOT r n = p)
Proof
   REPEAT STRIP_TAC
   THEN Cases_on `r = 0`
   THEN FULL_SIMP_TAC arith_ss [EXP, DECIDE ``~(r = 0n) <=> 0 < r``]
   THEN RW_TAC arith_ss []
   THEN CCONTR_TAC
   THEN `ROOT r n < p \/ p < ROOT r n` by DECIDE_TAC
   THEN METIS_TAC [DECIDE ``a < b ==> SUC a <= b``, exp_lemma3, LESS_EQ_TRANS,
                   DECIDE ``a <= b ==> ~(b < a:num)``, ROOT]
QED

Theorem ROOT_EXP :
    !n r. 0 < r ==> ROOT r (n ** r) = n
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC ROOT_UNIQUE
 >> RW_TAC arith_ss []
QED

val log_exists = Q.prove(
   `!a n. 1 < a /\ 0 < n ==> ?log. a ** log <= n /\ n < a ** SUC log`,
   REPEAT STRIP_TAC
   THEN Q.EXISTS_TAC `LEAST x. n < a ** SUC x`
   THEN CONV_TAC (UNBETA_CONV ``LEAST x. n < a ** SUC x``)
   THEN MATCH_MP_TAC WhileTheory.LEAST_ELIM
   THEN CONJ_TAC
   THENL [
      SRW_TAC [][EXP]
      THEN `?m. n <= a ** m` by METIS_TAC [EXP_ALWAYS_BIG_ENOUGH]
      THEN Q.EXISTS_TAC `m`
      THEN MATCH_MP_TAC LESS_EQ_LESS_TRANS
      THEN Q.EXISTS_TAC `a ** m`
      THEN SRW_TAC [] []
      THEN METIS_TAC
             [MULT_CLAUSES, LT_MULT_RCANCEL, EXP_EQ_0,
              DECIDE ``1 < x ==> ~(x = 0)``, DECIDE ``~(x = 0) <=> 0 < x``],
      Q.X_GEN_TAC `m`
      THEN SRW_TAC [][]
      THEN `(m = 0) \/ ?k. m = SUC k`
        by METIS_TAC [TypeBase.nchotomy_of ``:num``]
      THEN1 RW_TAC arith_ss [EXP]
      THEN FIRST_X_ASSUM (Q.SPEC_THEN `k` MP_TAC)
      THEN SRW_TAC [][EXP, NOT_LESS]
   ]);

Theorem LOG_exists =
   SIMP_RULE bool_ss [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] log_exists;

val LOG = new_specification("LOG", ["LOG"], LOG_exists);

Theorem LOG_UNIQUE:
    !a n:num p. (a ** p <= n /\ n < a ** SUC p) ==> (LOG a n = p)
Proof
   REPEAT STRIP_TAC
   THEN Cases_on `~(n = 0)`
   THEN Cases_on `~(a = 0)`
   THEN RW_TAC arith_ss []
   THEN Cases_on `a = 1`
   THEN FULL_SIMP_TAC arith_ss [EXP]
   THEN ((`0 < n /\ 1 < a` by DECIDE_TAC
          THEN REPEAT (PAT_X_ASSUM ``~(a = b:num)`` (K (ALL_TAC))))
         ORELSE
         (Cases_on `a`
          THEN FULL_SIMP_TAC arith_ss [EXP, ZERO_LESS_EXP]))
   THEN CCONTR_TAC
   THEN `LOG a n < p \/ p < LOG a n` by DECIDE_TAC
   THEN METIS_TAC [exp_lemma5, DECIDE ``a < b <=> SUC a <= b``, LESS_EQ_TRANS,
                   NOT_LESS, LOG, EXP]
QED

Theorem LOG_POW:
   !b n. 1n < b ==> (LOG b (b ** n) = n)
Proof
  REPEAT STRIP_TAC
  THEN irule LOG_UNIQUE
  THEN SRW_TAC [ARITH_ss] [EXP]
QED

Theorem LOG_ADD1:
    !n a b. 0n < n /\ 1n < a /\ 0 < b ==>
            (LOG a (a ** SUC n * b) = SUC (LOG a (a ** n * b)))
Proof
   RW_TAC arith_ss []
   THEN MATCH_MP_TAC LOG_UNIQUE
   THEN `~(a = 0) /\ 0 < a /\ ~(b = 0)` by DECIDE_TAC
   THEN ASM_SIMP_TAC arith_ss [EXP]
   THEN ASM_REWRITE_TAC [GSYM MULT_ASSOC, LT_MULT_LCANCEL, LE_MULT_LCANCEL]
   THEN REWRITE_TAC [GSYM EXP]
   THEN MATCH_MP_TAC LOG
   THEN ASM_SIMP_TAC arith_ss [DECIDE ``0 < x <=> ~(x = 0)``, EXP_EQ_0]
QED

val square = Q.prove(`a:num ** 2 = a * a`, REWRITE_TAC [EXP, EXP_1, TWO]);

Theorem LOG_BASE:
    !a. 1n < a ==> (LOG a a = 1)
Proof
   RW_TAC arith_ss []
   THEN MATCH_MP_TAC LOG_UNIQUE
   THEN Induct_on `a`
   THEN RW_TAC arith_ss [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, EXP_ADD, ADD1,
                         EXP_1, square]
QED

Theorem LOG_EXP:
    !n a b. 1n < a /\ 0 < b ==> (LOG a (a ** n * b) = n + LOG a b)
Proof
   REPEAT STRIP_TAC
   THEN MATCH_MP_TAC LOG_UNIQUE
   THEN RW_TAC arith_ss [EXP, EXP_ADD, EXP_EQ_0]
   THEN1 METIS_TAC [LOG]
   THEN Q_TAC SUFF_TAC `a ** n * b < a ** n * (a * a ** LOG a b)`
   THEN1 SIMP_TAC bool_ss [AC MULT_COMM MULT_ASSOC]
   THEN SRW_TAC [ARITH_ss][GSYM NOT_ZERO_LT_ZERO, EXP_EQ_0]
   THEN METIS_TAC [EXP, LOG]
QED

Theorem LOG_1:
    !a. 1n < a ==> (LOG a 1 = 0)
Proof
   REPEAT STRIP_TAC
   THEN MATCH_MP_TAC LOG_UNIQUE
   THEN REWRITE_TAC [EXP]
   THEN DECIDE_TAC
QED

Theorem LOG_DIV:
    !a x. 1n < a /\ a <= x ==> (LOG a x = 1 + LOG a (x DIV a))
Proof
   REPEAT STRIP_TAC
   THEN MATCH_MP_TAC LOG_UNIQUE
   THEN REWRITE_TAC [EXP_ADD, DECIDE ``SUC (1 + a) = 1 + SUC a``, EXP_1]
   THEN RW_TAC bool_ss [GSYM (SPEC ``a:num ** b`` MULT_COMM), GSYM X_LE_DIV,
                        GSYM DIV_LT_X, DECIDE ``1 < a ==> 0n < a``, LOG]
   THEN PROVE_TAC [X_LE_DIV, MULT_CLAUSES, DECIDE ``1 < a ==> 0n < a``,
                   DECIDE ``1 <= a ==> 0n < a``, LOG]
QED

Theorem LOG_ADD:
    !a b c. 1 < a /\ b < a ** c ==> (LOG a (b + a ** c) = c)
Proof
   REPEAT STRIP_TAC
   THEN MATCH_MP_TAC LOG_UNIQUE
   THEN CONJ_TAC
   THEN1 DECIDE_TAC
   THEN REWRITE_TAC [EXP]
   THEN MATCH_MP_TAC (DECIDE ``!a b c. a < b /\ b <= c ==> a < c:num``)
   THEN Q.EXISTS_TAC `2 * a ** c`
   THEN CONJ_TAC
   THENL [REWRITE_TAC [TIMES2, LT_ADD_RCANCEL],
          REWRITE_TAC [LE_MULT_RCANCEL]]
   THEN DECIDE_TAC
QED

Theorem LOG_LE_MONO:
    !a x y. 1 < a /\ 0 < x ==> x <= y ==> LOG a x <= LOG a y
Proof
   REPEAT STRIP_TAC
   THEN REWRITE_TAC
          [UNDISCH (SPECL [``a:num``,``LOG a x``,``SUC (LOG a y)``] LT_EXP_ISO),
           DECIDE ``a <= b <=> a < SUC b``]
   THEN MATCH_MP_TAC
          (DECIDE ``!a b c d. a <= b /\ b <= c /\ c < d ==> a < d:num``)
   THEN Q.EXISTS_TAC `x`
   THEN Q.EXISTS_TAC `y`
   THEN METIS_TAC [LOG, LESS_TRANS, LESS_OR_EQ]
QED

Theorem LOG_RWT:
    !m n. 1 < m /\ 0 < n ==>
          (LOG m n = if n < m then 0 else SUC (LOG m (n DIV m)))
Proof
   SRW_TAC [ARITH_ss] [LOG_DIV, ADD1, LOG_UNIQUE, EXP]
QED

Theorem LOG_EQ_0:
    !a b. 1 < a /\ 0 < b ==> ((LOG a b = 0) <=> b < a)
Proof
  SRW_TAC[][LOG_RWT]
QED

Theorem LOG_MULT:
    !b x. 1 < b /\ 0 < x ==> (LOG b (b * x) = SUC (LOG b x))
Proof
  SRW_TAC[][] THEN
  `0 < b /\ x <> 0` by DECIDE_TAC THEN
  `0 < b * x` by (
    Cases_on`b` THEN FULL_SIMP_TAC(srw_ss())[ADD1,RIGHT_ADD_DISTRIB] THEN
    DECIDE_TAC ) THEN
  ASM_SIMP_TAC(srw_ss())[LOG_RWT,boolSimps.SimpLHS] THEN
  REWRITE_TAC[Once MULT_COMM] THEN
  ASM_SIMP_TAC(srw_ss())[MULT_DIV]
QED

Theorem LOG_add_digit:
    !b x y. 1 < b /\ 0 < y /\ x < b ==> (LOG b (b * y + x) = SUC (LOG b y))
Proof
  SRW_TAC[][] THEN
  `0 < b * y + x` by (
    Cases_on`x` THEN ASM_SIMP_TAC(srw_ss()++ARITH_ss)[] THEN
    Cases_on`b` THEN FULL_SIMP_TAC(srw_ss()++ARITH_ss)[MULT] THEN
    DECIDE_TAC ) THEN
  ASM_SIMP_TAC(srw_ss()++ARITH_ss)[LOG_RWT,boolSimps.SimpLHS] THEN
  SRW_TAC[][] THEN1 (
    `b <= b * y` by ASM_SIMP_TAC(srw_ss()++ARITH_ss)[] THEN
    DECIDE_TAC ) THEN
  `x + b * y = y * b + x` by SIMP_TAC(srw_ss()++ARITH_ss)[] THEN
  POP_ASSUM SUBST1_TAC THEN
  ASM_SIMP_TAC(srw_ss()++ARITH_ss)[ADD_DIV_ADD_DIV] THEN
  IMP_RES_TAC LESS_DIV_EQ_ZERO THEN
  ASM_SIMP_TAC(srw_ss()++ARITH_ss)[]
QED

Theorem LT_EXP_LOG:
  x < b ** e <=> b = 0 /\ e = 0 /\ x = 0 \/ b = 1 /\ x = 0 \/
                 2 <= b /\ (LOG b x < e \/ x = 0)
Proof
  Cases_on ‘b = 0’
  >- (Cases_on ‘e = 0’ >> simp[ZERO_EXP]) >>
  simp[] >> Cases_on ‘b = 1’ >> simp[] >> iff_tac >>
  simp[DISJ_IMP_THM]
  >- (Cases_on ‘x = 0’ >> simp[] >>
      CCONTR_TAC >> FULL_SIMP_TAC (srw_ss()) [NOT_LESS]>>
      ‘0 < b /\ 1 < b’ by simp[] >>
      drule_all_then assume_tac EXP_BASE_LEQ_MONO_IMP >>
      ‘b ** LOG b x <= x’ by simp[LOG] >>
      DECIDE_TAC) >>
  strip_tac >> Cases_on ‘x = 0’ >> simp[] >>
  CCONTR_TAC >> full_simp_tac (srw_ss()) [NOT_LESS]>>
  ‘x < b ** (SUC (LOG b x))’ by simp[LOG] >>
  ‘b ** e < b ** (SUC (LOG b x))’ by DECIDE_TAC >>
  pop_assum mp_tac >> ‘1 < b’ by simp[] >>
  pop_assum mp_tac >>
  simp_tac (srw_ss()) [] >> simp[]
QED

Theorem NB12_NEQ0[local]:
  NUMERAL (BIT1 n) <> 0 /\ NUMERAL (BIT2 n) <> 0 /\
  0 < NUMERAL (BIT1 n) /\ 0 < NUMERAL (BIT2 n) /\
  (NUMERAL (BIT2 n) <= 1 <=> F) /\ (NUMERAL (BIT2 n) <> 1) /\
  (NUMERAL (BIT1 n) <= 1 <=> NUMERAL (BIT1 n) = 1) /\
  NUMERAL (BIT1 (BIT1 n)) <> 1 /\ NUMERAL (BIT1 (BIT2 n)) <> 1
Proof
  REWRITE_TAC[NUMERAL_DEF, BIT1, BIT2, ADD_CLAUSES, numTheory.NOT_SUC,
              GSYM NOT_ZERO_LT_ZERO, LESS_EQ_MONO] >>
  REWRITE_TAC[ALT_ZERO, ADD_CLAUSES, NOT_SUC_LESS_EQ_0,
              prim_recTheory.INV_SUC_EQ, numTheory.NOT_SUC] >>
  REWRITE_TAC [LESS_OR_EQ, LT]
QED

Theorem LT_EXP_LOG_SIMP[simp] =
        CONJ
        (LT_EXP_LOG |> Q.INST [‘x’ |-> ‘NUMERAL $ BIT1 x’, ‘b’ |-> ‘NUMERAL b’])
        (LT_EXP_LOG |> Q.INST [‘x’ |-> ‘NUMERAL $ BIT2 x’, ‘b’ |-> ‘NUMERAL b’])
        |> REWRITE_RULE[NB12_NEQ0]

Theorem EXP_LE_LOG_SIMP[simp] =
        LT_EXP_LOG_SIMP
          |> ONCE_REWRITE_RULE [tautLib.TAUT_PROVE “(x <=> y) <=> (~x <=> ~y)”]
          |> REWRITE_RULE [NOT_LESS, DE_MORGAN_THM, NOT_LESS_EQUAL]

fun trip f g h x = (f x, g x, h x)
fun conj3 (x,y,z) = CONJ x (CONJ y z)

Theorem LE_EXP_LOG_SIMP[simp] =
        LT_EXP_LOG
        |> Q.INST [‘x’ |-> ‘x - 1’, ‘b’ |-> ‘NUMERAL b’]
        |> SIMP_RULE bool_ss
                     [DECIDE “0 < x ==> (x - 1 < y <=> x <= y)”, ASSUME “0 < x”]
        |> DISCH_ALL
        |> trip (Q.INST [‘x’ |-> ‘NUMERAL (BIT1 (BIT1 x))’])
                (Q.INST [‘x’ |-> ‘NUMERAL (BIT1 (BIT2 x))’])
                (Q.INST [‘x’ |-> ‘NUMERAL (BIT2 x)’])
        |> conj3
        |> REWRITE_RULE[NB12_NEQ0,SUB_RIGHT_EQ, ADD_CLAUSES, LESS_EQ_REFL,
                        DECIDE “x = y \/ x <= y <=> x <= y”]

Theorem EXP_LT_LOG_SIMP[simp] =
        LE_EXP_LOG_SIMP
          |> ONCE_REWRITE_RULE [tautLib.TAUT_PROVE “(x <=> y) <=> (~x <=> ~y)”]
          |> REWRITE_RULE [NOT_LESS, DE_MORGAN_THM, NOT_LESS_EQUAL]

val less_lemma1 = Q.prove(
   `a <= c /\ b <= d ==> a * b <= c * d:num`,
   REPEAT STRIP_TAC
   THEN MATCH_MP_TAC LESS_EQ_TRANS
   THEN Q.EXISTS_TAC `c * b`
   THEN REWRITE_TAC [LE_MULT_LCANCEL, LE_MULT_RCANCEL]
   THEN DECIDE_TAC);

val div_lemma1 = Q.prove(
   `!a b c. 0 < b /\ 0 < c ==> (a DIV b) ** c <= a ** c DIV b ** c`,
   REPEAT STRIP_TAC
   THEN Induct_on `c`
   THEN1 DECIDE_TAC
   THEN STRIP_TAC
   THEN Cases_on `0 < c`
   THENL [FULL_SIMP_TAC bool_ss [EXP], `c = 0` by DECIDE_TAC]
   THEN ASM_REWRITE_TAC [EXP, LESS_EQ_REFL, MULT_CLAUSES]
   THEN MATCH_MP_TAC LESS_EQ_TRANS
   THEN Q.EXISTS_TAC `(a DIV b) * (a ** c DIV b ** c)`
   THEN RW_TAC bool_ss [LE_MULT_LCANCEL]
   THEN `0 < b ** c`
     by (Cases_on `b`
         THEN REWRITE_TAC [ZERO_LESS_EXP]
         THEN DECIDE_TAC)
   THEN RW_TAC bool_ss
           [GSYM (CONV_RULE
                    (ONCE_DEPTH_CONV (REWR_CONV MULT_COMM)) DIV_DIV_DIV_MULT),
            X_LE_DIV]
   THEN ONCE_REWRITE_TAC [AC_THM ``a * b * c * d = (a * c) * (b * d:num)``]
   THEN MATCH_MP_TAC less_lemma1
   THEN METIS_TAC [DIVISION, DECIDE ``(a = b + c) ==> b <= a:num``]);

val square_add_lemma = Q.prove(
   `a ** e * b ** e = (a * b:num) ** e`,
   Induct_on `e`
   THEN RW_TAC arith_ss [EXP]
   THEN METIS_TAC [MULT_COMM, MULT_ASSOC]);

Theorem ROOT_DIV:
    !r x y. 0 < r /\ 0 < y ==> (ROOT r x DIV y = ROOT r (x DIV (y ** r)))
Proof
   REPEAT STRIP_TAC
   THEN MATCH_MP_TAC (GSYM ROOT_UNIQUE)
   THEN `0 < y ** r`
     by (Cases_on `y`
         THEN REWRITE_TAC [ZERO_LESS_EXP]
         THEN DECIDE_TAC)
   THEN CONJ_TAC
   THENL [
      MATCH_MP_TAC LESS_EQ_TRANS
      THEN EXISTS_TAC ``(ROOT r x) ** r DIV y ** r``
      THEN RW_TAC bool_ss [div_lemma1]
      THEN METIS_TAC [DIV_LE_MONOTONE, ROOT],
      RW_TAC bool_ss [DIV_LT_X]
      THEN MATCH_MP_TAC (DECIDE ``!a b c. a < b /\ b <= c ==> a < c:num``)
      THEN EXISTS_TAC ``SUC (ROOT r x) ** r``
      THEN RW_TAC bool_ss [ROOT]
      THEN REWRITE_TAC [square_add_lemma]
      THEN MATCH_MP_TAC (UNDISCH (SPEC_ALL exp_lemma3))
      THEN REWRITE_TAC [ADD1, RIGHT_ADD_DISTRIB, MULT_CLAUSES]
      THEN GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) bool_rewrites
              [SPEC ``ROOT r x`` (UNDISCH (SPEC ``y:num`` DIVISION))]
      THEN REWRITE_TAC [GSYM ADD_ASSOC, LE_ADD_LCANCEL]
      THEN METIS_TAC [DECIDE ``a < b ==> a + 1n <= b``, DIVISION]]
QED

Theorem ROOT_LE_MONO:
    !r x y. 0 < r ==> x <= y ==> ROOT r x <= ROOT r y
Proof
   REPEAT STRIP_TAC
   THEN REWRITE_TAC [DECIDE ``a <= b <=> a < SUC b``]
   THEN ONCE_REWRITE_TAC [UNDISCH (SPEC_ALL EXP_LT_ISO)]
   THEN MATCH_MP_TAC
          (DECIDE ``!a b c d. a <= b /\ b <= c /\ c < d ==> a < d:num``)
   THEN Q.EXISTS_TAC `x`
   THEN Q.EXISTS_TAC `y`
   THEN RW_TAC bool_ss [ROOT]
QED

Theorem EXP_MUL:
    !a b c. (a ** b) ** c = a ** (b * c)
Proof
   Induct_on `c`
   THEN REWRITE_TAC [MULT_CLAUSES, EXP_ADD, ADD1, LEFT_ADD_DISTRIB, EXP, EXP_1]
   THEN PROVE_TAC []
QED

Theorem LOG_ROOT:
    !a x r. 1 < a /\ 0 < x /\ 0 < r ==> (LOG a (ROOT r x) = (LOG a x) DIV r)
Proof
   REPEAT STRIP_TAC
   THEN MATCH_MP_TAC LOG_UNIQUE
   THEN CONJ_TAC
   THENL [
      REWRITE_TAC [DECIDE ``a <= b <=> a < SUC b``]
      THEN ONCE_REWRITE_TAC [UNDISCH (SPEC_ALL EXP_LT_ISO)]
      THEN MATCH_MP_TAC (DECIDE ``!a b c. a <= b /\ b < c ==> a < c:num``)
      THEN Q.EXISTS_TAC `x`
      THEN RW_TAC bool_ss [ROOT, EXP_MUL]
      THEN MATCH_MP_TAC LESS_EQ_TRANS
      THEN Q.EXISTS_TAC `a ** (LOG a x)`
      THEN RW_TAC bool_ss [LOG, GSYM LE_EXP_ISO],
      ONCE_REWRITE_TAC [UNDISCH (SPEC_ALL EXP_LT_ISO)]
      THEN MATCH_MP_TAC (DECIDE ``!a b c d. a <= b /\ b < c ==> a < c:num``)
      THEN Q.EXISTS_TAC `x`
      THEN RW_TAC bool_ss [ROOT, EXP_MUL]
      THEN MATCH_MP_TAC (DECIDE ``!a b c. a < b /\ b <= c ==> a < c:num``)
      THEN Q.EXISTS_TAC `a ** SUC (LOG a x)`
      THEN RW_TAC bool_ss [LOG, GSYM LE_EXP_ISO]
      THEN RW_TAC bool_ss [ADD1, RIGHT_ADD_DISTRIB, MULT_CLAUSES]
      THEN GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) bool_rewrites
              [SPEC ``LOG a x`` (UNDISCH (SPEC ``r:num`` DIVISION))]
      THEN REWRITE_TAC [LT_ADD_LCANCEL, DECIDE ``a + 1 <= b <=> a < b:num``]]
   THEN METIS_TAC [DIVISION, DECIDE ``(a = b + c) ==> (b <= a:num)``]
QED

val zero_lt_twoexp = Q.prove(
   `!n. 0 < 2 ** n`,
   Induct
   THEN REWRITE_TAC [EXP]
   THEN TRY (MATCH_MP_TAC LESS_MULT2)
   THEN DECIDE_TAC);

Theorem LOG_MOD:
    !n. 0 < n ==> (n = 2 ** LOG 2 n + n MOD 2 ** LOG 2 n)
Proof
  REPEAT STRIP_TAC
  THEN Cases_on `?b c. (n = b + 2 ** c) /\ b < 2 ** c`
  THEN RW_TAC bool_ss []
  THEN1 (RW_TAC bool_ss [LOG_ADD, DECIDE ``1 < 2n``]
         THEN METIS_TAC [ADD_MODULUS_LEFT, ADD_COMM, LESS_MOD, zero_lt_twoexp,
                         DECIDE ``b < a ==> 0n < a``])
  THEN POP_ASSUM (fn th => CCONTR_TAC THEN MP_TAC th)
  THEN RW_TAC arith_ss []
  THEN POP_ASSUM (K ALL_TAC)
  THEN Induct_on `n`
  THEN RW_TAC arith_ss []
  THEN Cases_on `n`
  THEN FULL_SIMP_TAC arith_ss []
  THENL [
     Q.EXISTS_TAC `0`
     THEN Q.EXISTS_TAC `0`
     THEN RW_TAC arith_ss [EXP],
     Cases_on `SUC b < 2 ** c`
     THENL [
        Q.EXISTS_TAC `SUC b`
        THEN Q.EXISTS_TAC `c`
        THEN RW_TAC arith_ss [],
        FULL_SIMP_TAC arith_ss [NOT_LESS]
        THEN `SUC b = 2 ** c` by DECIDE_TAC
        THEN ASM_REWRITE_TAC [DECIDE ``SUC (a + b) = SUC a + b``]]]
  THEN Q.EXISTS_TAC `0`
  THEN Q.EXISTS_TAC `SUC c`
  THEN RW_TAC arith_ss [EXP]
QED

local
val numtac = REWRITE_TAC[NUMERAL_DEF, BIT1, BIT2, ALT_ZERO, ADD_CLAUSES,
                         prim_recTheory.LESS_0, prim_recTheory.LESS_MONO_EQ]
fun numpr t = prove(t,numtac)
val one_lt_ths = map numpr [“1 < NUMERAL (BIT1 (BIT1 b))”,
                            “1 < NUMERAL (BIT1 (BIT2 b))”,
                            “1 < NUMERAL (BIT2 b)”]
val zero_lt_ths = map numpr [“0 < NUMERAL (BIT1 n)”,
                             “0 < NUMERAL (BIT2 n)”]
val allths = List.concat $ map (fn lt1 => map (CONJ lt1) zero_lt_ths) one_lt_ths
in
Theorem LOG_NUMERAL[compute,simp] =
        map (MATCH_MP LOG_RWT) allths |> LIST_CONJ |> REWRITE_RULE [ADD1];
end (* local *)


val lem = prove(``0 < r ==> (0 ** r = 0)``, RW_TAC arith_ss [EXP_EQ_0])

Theorem ROOT_COMPUTE:
    !r n.
       0 < r ==>
       (ROOT r 0 = 0) /\
       (ROOT r n = let x = 2 * ROOT r (n DIV 2 ** r) in
                      if n < SUC x ** r then x else SUC x)
Proof
   RW_TAC (arith_ss ++ boolSimps.LET_ss) []
   THEN MATCH_MP_TAC ROOT_UNIQUE
   THEN CONJ_TAC
   THEN FULL_SIMP_TAC arith_ss [NOT_LESS, EXP_1, lem]
   THEN MAP_FIRST MATCH_MP_TAC
          [LESS_EQ_TRANS, DECIDE ``!a b c. a < b /\ b <= c ==> a < c``]
   THENL [
      Q.EXISTS_TAC `ROOT r n ** r`,
      Q.EXISTS_TAC `SUC (ROOT r n) ** r`]
   THEN RW_TAC arith_ss
           [ROOT, GSYM EXP_LE_ISO, GSYM ROOT_DIV, DECIDE ``0 < 2n``]
   THEN METIS_TAC
           [DIVISION, MULT_COMM, DECIDE ``0 < 2n``,
            DECIDE ``(a = b + c) ==> b <= a:num``, ADD1, LE_ADD_LCANCEL,
            DECIDE ``a <= 1 <=> a < 2n``]
QED

(* For evaluation of ROOT r n in HOL4 interactive session. *)
Theorem ROOT_EVAL[compute]:
  !r n. ROOT r n =
    if r = 0 then ROOT 0 n else
    if n = 0 then 0 else
    let m = 2 * (ROOT r (n DIV 2 ** r)) in
    m + if (SUC m) ** r <= n then 1 else 0
Proof
  rpt strip_tac >>
  (Cases_on `r = 0` >> asm_simp_tac arith_ss[LET_THM]) >>
  `0 < r` by asm_simp_tac arith_ss[] >>
  (Cases_on `n = 0` >> asm_simp_tac arith_ss[Once ROOT_COMPUTE, LET_THM]) >>
  `0 DIV 2 ** r = 0` by RW_TAC arith_ss[ZERO_DIV] >>
  METIS_TAC[ROOT_COMPUTE]
QED


Definition SQRTd_def[nocompute]:   SQRTd n = (ROOT 2 n, n - (ROOT 2 n * ROOT 2 n))
End

Definition iSQRTd_def[nocompute]:
   iSQRTd (x,n) =
      let p = SQRTd n in
      let next = 4 * SND p + x in
      let ndiff = 4 * FST p + 1 in
        if next < ndiff then (2 * FST p,next)
        else (2 * FST p + 1,next - ndiff)
End

val sqrt_zero = Q.prove(`ROOT 2 0 = 0`, RW_TAC arith_ss [ROOT_COMPUTE]);
val sqrt_compute = SIMP_RULE arith_ss [] (SPEC ``2n`` ROOT_COMPUTE);

val mult_eq_lemma =
  METIS_PROVE [MULT_COMM, MULT_ASSOC, DECIDE ``2 * 2 = 4n``]
     ``2 * a * (2 * a) = 4n * (a * a)``

val iSQRT_lemma = Q.prove(
   `SQRTd m = iSQRTd (m MOD 4,m DIV 4)`,
   REWRITE_TAC [SQRTd_def]
   THEN REWRITE_TAC [iSQRTd_def, FST, SND]
   THEN REWRITE_TAC [SQRTd_def]
   THEN RW_TAC (bool_ss ++ boolSimps.LET_ss) [FST, SND]
   THEN (SUBGOAL_THEN ``(4 * (ROOT 2 (m DIV 4) * ROOT 2 (m DIV 4)) <= m /\
                         ROOT 2 (m DIV 4) * ROOT 2 (m DIV 4) <= m DIV 4) /\
                         ROOT 2 m * ROOT 2 m <= m``
           (fn th =>
              RW_TAC bool_ss []
              THEN FULL_SIMP_TAC bool_ss
                      [SIMP_RULE arith_ss [] (SPEC ``4n`` (GSYM DIVISION)), th,
                       DECIDE ``a <= b ==> (4 * (b - a) + c =
                                (b * 4 + c) - (4 * a))``,
                       SUB_CANCEL,
                       DECIDE ``a <= b ==> (b - a <= c <=> b < a + (c + 1n))``]
              THEN ASSUME_TAC (CONJUNCT2 th))
   THEN1 METIS_TAC [EXP, DECIDE ``2 = SUC 1``, EXP_1, ROOT, DECIDE ``0 < 2n``,
                    DECIDE ``0 < 4n``, MULT_COMM, X_LE_DIV]
   THEN Cases_on `m = 0`
   THEN RW_TAC arith_ss [sqrt_zero]
   THEN RW_TAC arith_ss
          [SUB_CANCEL,
           DECIDE ``~(m < 4 * a + (4 * b + 1)) ==> 4 * a + (2 * b + 1) <= m``]
   THEN GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) bool_rewrites
           [CONJUNCT2 (SPEC_ALL sqrt_compute)]
   THEN RW_TAC (arith_ss ++ boolSimps.LET_ss)
           [mult_eq_lemma, ADD1, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB]
   THEN PAT_X_ASSUM ``~(a < b:num)`` MP_TAC
   THEN FULL_SIMP_TAC arith_ss
           [ADD1, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, mult_eq_lemma,
            METIS_PROVE [DECIDE ``SUC 1 = 2``, EXP, EXP_1]
               ``a ** 2 = a * a:num``]));

Theorem numeral_sqrt0[local]:
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
  (SQRTd (SUC (BIT2 (BIT2 n))) = iSQRTd (3,SUC n))
Proof
  REWRITE_TAC [BIT1, BIT2, ALT_ZERO, ADD_CLAUSES, NUMERAL_DEF]
  THEN RW_TAC arith_ss [iSQRT_lemma, ADD1]
  THEN RW_TAC (arith_ss ++ boolSimps.LET_ss) [iSQRTd_def, SQRTd_def, sqrt_zero]
QED

Definition iSQRT0_def:
   iSQRT0 n =
      let p = SQRTd n in
      let d = SND p - FST p in
         if d = 0 then (2 * FST p,4 * SND p) else (SUC (2 * FST p),4 * d - 1)
End

Definition iSQRT1_def:
   iSQRT1 n =
      let p = SQRTd n in
      let d = (SUC (SND p) - FST p) in
         if d = 0 then (2 * FST p, SUC (4 * SND p))
         else (SUC (2 * FST p),4 * (d - 1))
End

Definition iSQRT2_def:
   iSQRT2 n =
      let p = SQRTd n in
      let d = 2 * FST p in
      let c = SUC (2 * SND p) in
      let e = c - d in
         if e = 0 then (d,2 * c) else (SUC d, 2 * e - 1)
End

Definition iSQRT3_def:
   iSQRT3 n =
      let p = SQRTd n in
      let d = 2 * FST p in
      let c = SUC (2 * (SND p)) in
      let e = SUC c - d in
         if e = 0 then (d,SUC (2 * c)) else (SUC d, 2 * (e - 1))
End

Theorem numeral_sqrt[compute]:
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
  (SQRTd (SUC (BIT2 (BIT2 n))) = iSQRT3 (SUC n))
Proof
  RW_TAC(arith_ss ++ boolSimps.LET_ss) [numeral_sqrt0]
  THEN REWRITE_TAC [iSQRT0_def, iSQRT1_def, iSQRT2_def, iSQRT3_def]
  THEN RW_TAC (arith_ss ++ boolSimps.LET_ss) [iSQRTd_def, ADD1]
QED

Theorem numeral_root2[compute]:
   ROOT 2 (NUMERAL n) = FST (SQRTd n)
Proof REWRITE_TAC [FST, SQRTd_def, NUMERAL_DEF]
QED

val () = Theory.delete_const "iSQRTd"

(* ------------------------------------------------------------------------- *)
(* ROOT Computation                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: ROOT n (a ** n) = a *)
(* Proof:
   Since   a < SUC a         by LESS_SUC
      a ** n < (SUC a) ** n  by EXP_BASE_LT_MONO
   Let b = a ** n,
   Then  a ** n <= b         by LESS_EQ_REFL
    and  b < (SUC a) ** n    by above
   Hence a = ROOT n b        by ROOT_UNIQUE
*)
Theorem ROOT_POWER:
    !a n. 1 < a /\ 0 < n ==> (ROOT n (a ** n) = a)
Proof
  rw[EXP_BASE_LT_MONO, ROOT_UNIQUE]
QED

(* Theorem: 0 < m /\ (b ** m = n) ==> (b = ROOT m n) *)
(* Proof:
   Note n <= n                  by LESS_EQ_REFL
     so b ** m <= n             by b ** m = n
   Also b < SUC b               by LESS_SUC
     so b ** m < (SUC b) ** m   by EXP_EXP_LT_MONO, 0 < m
     so n < (SUC b) ** m        by b ** m = n
   Thus b = ROOT m n            by ROOT_UNIQUE
*)
Theorem ROOT_FROM_POWER:
    !m n b. 0 < m /\ (b ** m = n) ==> (b = ROOT m n)
Proof
  rpt strip_tac >>
  rw[ROOT_UNIQUE]
QED

(* Theorem: 0 < m ==> (ROOT m 0 = 0) *)
(* Proof:
   Note 0 ** m = 0    by EXP_0
   Thus 0 = ROOT m 0  by ROOT_FROM_POWER
*)
Theorem ROOT_OF_0[simp]:
    !m. 0 < m ==> (ROOT m 0 = 0)
Proof
  rw[ROOT_FROM_POWER]
QED

(* Theorem: 0 < m ==> (ROOT m 1 = 1) *)
(* Proof:
   Note 1 ** m = 1    by EXP_1
   Thus 1 = ROOT m 1  by ROOT_FROM_POWER
*)
Theorem ROOT_OF_1[simp]:
    !m. 0 < m ==> (ROOT m 1 = 1)
Proof
  rw[ROOT_FROM_POWER]
QED

(* Theorem: 0 < r ==> !n p. (ROOT r n = p) <=> (p ** r <= n /\ n < SUC p ** r) *)
(* Proof:
   If part: 0 < r ==> ROOT r n ** r <= n /\ n < SUC (ROOT r n) ** r
      This is true             by ROOT, 0 < r
   Only-if part: p ** r <= n /\ n < SUC p ** r ==> ROOT r n = p
      This is true             by ROOT_UNIQUE
*)
Theorem ROOT_THM:
    !r. 0 < r ==> !n p. (ROOT r n = p) <=> (p ** r <= n /\ n < SUC p ** r)
Proof
  metis_tac[ROOT, ROOT_UNIQUE]
QED

(* Theorem: 0 < m ==> !n. (ROOT m n = 0) <=> (n = 0) *)
(* Proof:
   If part: ROOT m n = 0 ==> n = 0
      Note n < SUC (ROOT m n) ** r      by ROOT
        or n < SUC 0 ** m               by ROOT m n = 0
        so n < 1                        by ONE, EXP_1
        or n = 0                        by arithmetic
   Only-if part: ROOT m 0 = 0, true     by ROOT_OF_0
*)
Theorem ROOT_EQ_0:
    !m. 0 < m ==> !n. (ROOT m n = 0) <=> (n = 0)
Proof
  rw[EQ_IMP_THM] >>
  `n < 1` by metis_tac[ROOT, EXP_1, ONE] >>
  decide_tac
QED

(* Theorem: ROOT 1 n = n *)
(* Proof:
   Note n ** 1 = n      by EXP_1
     so n ** 1 <= n
   Also n < SUC n       by LESS_SUC
     so n < SUC n ** 1  by EXP_1
   Thus ROOT 1 n = n    by ROOT_UNIQUE
*)
Theorem ROOT_1[simp]:
    !n. ROOT 1 n = n
Proof
  rw[ROOT_UNIQUE]
QED

(* Theorem: 0 < r ==>
            (ROOT r (SUC n) = ROOT r n + if SUC n = (SUC (ROOT r n)) ** r then 1 else 0) *)
(* Proof:
   Let x = ROOT r n, y = ROOT r (SUC n).  x <= y.
   Note n < (SUC x) ** r /\ x ** r <= n          by ROOT_THM
    and SUC n < (SUC y) ** r /\ y ** r <= SUC n  by ROOT_THM
   Since n < (SUC x) ** r,
    SUC n <= (SUC x) ** r.
   If SUC n = (SUC x) ** r,
      Then y = ROOT r (SUC n)
             = ROOT r ((SUC x) ** r)
             = SUC x                             by ROOT_POWER
   If SUC n < (SUC x) ** r,
      Then x ** r <= n < SUC n                   by LESS_SUC
      Thus x = y                                 by ROOT_THM
*)
Theorem ROOT_SUC:
    !r n. 0 < r ==>
   (ROOT r (SUC n) = ROOT r n + if SUC n = (SUC (ROOT r n)) ** r then 1 else 0)
Proof
  rpt strip_tac >>
  qabbrev_tac `x = ROOT r n` >>
  qabbrev_tac `y = ROOT r (SUC n)` >>
  Cases_on `n = 0` >| [
    `x = 0` by rw[ROOT_OF_0, Abbr`x`] >>
    `y = 1` by rw[ROOT_OF_1, Abbr`y`] >>
    simp[],
    `x <> 0` by rw[ROOT_EQ_0, Abbr`x`] >>
    `n < (SUC x) ** r /\ x ** r <= n` by metis_tac[ROOT_THM] >>
    `SUC n < (SUC y) ** r /\ y ** r <= SUC n` by metis_tac[ROOT_THM] >>
    `(SUC n = (SUC x) ** r) \/ SUC n < (SUC x) ** r` by decide_tac >| [
      `1 < SUC x` by decide_tac >>
      `y = SUC x` by metis_tac[ROOT_POWER] >>
      simp[],
      `x ** r <= SUC n` by decide_tac >>
      `x = y` by metis_tac[ROOT_THM] >>
      simp[]
    ]
  ]
QED

(*
ROOT_SUC;
|- !r n. 0 < r ==> ROOT r (SUC n) = ROOT r n + if SUC n = SUC (ROOT r n) ** r then 1 else 0
Let z = ROOT r n.

   z(n)
   -------------------------------------------------
                      n   (n+1=(z+1)**r)

> EVAL ``MAP (ROOT 2) [1 .. 20]``;
val it = |- MAP (ROOT 2) [1 .. 20] =
      [1; 1; 1; 2; 2; 2; 2; 2; 3; 3; 3; 3; 3; 3; 3; 4; 4; 4; 4; 4]: thm
       1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 20
*)

(* Theorem: 0 < m ==> !n. (ROOT m n = 1) <=> (0 < n /\ n < 2 ** m) *)
(* Proof:
       ROOT m n = 1
   <=> 1 ** m <= n /\ n < (SUC 1) ** m    by ROOT_THM, 0 < m
   <=> 1 <= n /\ n < 2 ** m               by TWO, EXP_1
   <=> 0 < n /\ n < 2 ** m                by arithmetic
*)
Theorem ROOT_EQ_1:
    !m. 0 < m ==> !n. (ROOT m n = 1) <=> (0 < n /\ n < 2 ** m)
Proof
  rpt strip_tac >>
  `!n. 0 < n <=> 1 <= n` by decide_tac >>
  metis_tac[ROOT_THM, TWO, EXP_1]
QED

(* Theorem: 0 < m ==> ROOT m n <= n *)
(* Proof:
   Let r = ROOT m n.
   Note r <= r ** m   by X_LE_X_EXP, 0 < m
          <= n        by ROOT
*)
Theorem ROOT_LE_SELF:
    !m n. 0 < m ==> ROOT m n <= n
Proof
  metis_tac[X_LE_X_EXP, ROOT, LESS_EQ_TRANS]
QED

(* Theorem: 0 < m ==> ((ROOT m n = n) <=> ((m = 1) \/ (n = 0) \/ (n = 1))) *)
(* Proof:
   If part: ROOT m n = n ==> m = 1 \/ n = 0 \/ n = 1
      Note n ** m <= n               by ROOT, 0 < r
       But n <= n ** m               by X_LE_X_EXP, 0 < m
        so n ** m = n                by EQ_LESS_EQ
       ==> m = 1 or n = 0 or n = 1   by EXP_EQ_SELF
   Only-if part: ROOT 1 n = n /\ ROOT m 0 = 0 /\ ROOT m 1 = 1
      True by ROOT_1, ROOT_OF_0, ROOT_OF_1.
*)
Theorem ROOT_EQ_SELF:
  !m n. 0 < m ==> (ROOT m n = n <=> m = 1 \/ n = 0 \/ n = 1)
Proof
  rw_tac std_ss[EQ_IMP_THM] >> rw[] >>
  `n ** m <= n` by metis_tac[ROOT] >>
  `n <= n ** m` by rw[X_LE_X_EXP] >>
  `n ** m = n` by decide_tac >>
  fs[]
QED

(* Theorem: 0 < m ==> (n <= ROOT m n <=> ((m = 1) \/ (n = 0) \/ (n = 1))) *)
(* Proof:
   Note ROOT m n <= n                     by ROOT_LE_SELF
   Thus n <= ROOT m n <=> ROOT m n = n    by EQ_LESS_EQ
   The result follows                     by ROOT_EQ_SELF
*)
Theorem ROOT_GE_SELF:
    !m n. 0 < m ==> (n <= ROOT m n <=> ((m = 1) \/ (n = 0) \/ (n = 1)))
Proof
  metis_tac[ROOT_LE_SELF, ROOT_EQ_SELF, EQ_LESS_EQ]
QED

(*
EVAL ``MAP (\k. ROOT k 100)  [1 .. 10]``; = [100; 10; 4; 3; 2; 2; 1; 1; 1; 1]: thm

This shows (ROOT k) is a decreasing function of k,
but this is very hard to prove without some real number theory.
Even this is hard to prove: ROOT 3 n <= ROOT 2 n

No! -- this can be proved, see below.
*)

(* Theorem: 0 < a /\ a <= b ==> ROOT b n <= ROOT a n *)
(* Proof:
   Let x = ROOT a n, y = ROOT b n. To show: y <= x.
   By contradiction, suppose x < y.
   Then SUC x <= y.
   Note x ** a <= n /\ n < (SUC x) ** a     by ROOT
    and y ** b <= n /\ n < (SUC y) ** b     by ROOT
    But a <= b
        (SUC x) ** a
     <= (SUC x) ** b       by EXP_BASE_LEQ_MONO_IMP, 0 < SUC x, a <= b
     <=       y ** b       by EXP_EXP_LE_MONO, 0 < b
   This leads to n < (SUC x) ** a <= y ** b <= n, a contradiction.
*)
Theorem ROOT_LE_REVERSE:
    !a b n. 0 < a /\ a <= b ==> ROOT b n <= ROOT a n
Proof
  rpt strip_tac >>
  qabbrev_tac `x = ROOT a n` >>
  qabbrev_tac `y = ROOT b n` >>
  spose_not_then strip_assume_tac >>
  `0 < b /\ SUC x <= y` by decide_tac >>
  `x ** a <= n /\ n < (SUC x) ** a` by rw[ROOT, Abbr`x`] >>
  `y ** b <= n /\ n < (SUC y) ** b` by rw[ROOT, Abbr`y`] >>
  `(SUC x) ** a <= (SUC x) ** b` by rw[EXP_BASE_LEQ_MONO_IMP] >>
  `(SUC x) ** b <= y ** b` by rw[EXP_EXP_LE_MONO] >>
  decide_tac
QED

(* ------------------------------------------------------------------------- *)
(* Square Root                                                               *)
(* ------------------------------------------------------------------------- *)

(* Use overload for SQRT *)
val _ = overload_on ("SQRT", ``\n. ROOT 2 n``);

(* Theorem: 0 < n ==> (SQRT n) ** 2 <= n /\ n < SUC (SQRT n) ** 2 *)
(* Proof: by ROOT:
   |- !r n. 0 < r ==> ROOT r n ** r <= n /\ n < SUC (ROOT r n) ** r
*)
Theorem SQRT_PROPERTY:
    !n. (SQRT n) ** 2 <= n /\ n < SUC (SQRT n) ** 2
Proof
  rw[ROOT]
QED

(* Get a useful theorem *)
Theorem SQRT_UNIQUE = ROOT_UNIQUE |> SPEC ``2``;
(* val SQRT_UNIQUE = |- !n p. p ** 2 <= n /\ n < SUC p ** 2 ==> SQRT n = p: thm *)

(* Obtain a theorem *)
Theorem SQRT_THM =
    ROOT_THM |> SPEC ``2`` |> SIMP_RULE (srw_ss())[];
(* val SQRT_THM = |- !n p. (SQRT n = p) <=> p ** 2 <= n /\ n < SUC p ** 2: thm *)

(* Theorem: n <= m ==> SQRT n <= SQRT m *)
(* Proof: by ROOT_LE_MONO *)
Theorem SQRT_LE:
    !n m. n <= m ==> SQRT n <= SQRT m
Proof
  rw[ROOT_LE_MONO]
QED

(* Theorem: n < m ==> SQRT n <= SQRT m *)
(* Proof:
   Since n < m ==> n <= m   by LESS_IMP_LESS_OR_EQ
   This is true             by ROOT_LE_MONO
*)
Theorem SQRT_LT:
    !n m. n < m ==> SQRT n <= SQRT m
Proof
  rw[ROOT_LE_MONO, LESS_IMP_LESS_OR_EQ]
QED

(* Theorem: SQRT 0 = 0 *)
(* Proof: by ROOT_OF_0 *)
Theorem SQRT_0[simp]:
    SQRT 0 = 0
Proof
  rw[]
QED

(* Theorem: SQRT 1 = 1 *)
(* Proof: by ROOT_OF_1 *)
Theorem SQRT_1[simp]:
    SQRT 1 = 1
Proof
  rw[]
QED

(* Theorem: SQRT n = 0 <=> n = 0 *)
(* Proof:
   If part: SQRT n = 0 ==> n = 0.
   By contradiction, suppose n <> 0.
      This means 1 <= n
      Hence  SQRT 1 <= SQRT n   by SQRT_LE
         so       1 <= SQRT n   by SQRT_1
      This contradicts SQRT n = 0.
   Only-if part: n = 0 ==> SQRT n = 0
      True since SQRT 0 = 0     by SQRT_0
*)
Theorem SQRT_EQ_0:
    !n. (SQRT n = 0) <=> (n = 0)
Proof
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  `1 <= n` by decide_tac >>
  `SQRT 1 <= SQRT n` by rw[SQRT_LE] >>
  `SQRT 1 = 1` by rw[] >>
  decide_tac
QED

(* Theorem: SQRT n = 1 <=> n = 1 \/ n = 2 \/ n = 3 *)
(* Proof:
   If part: SQRT n = 1 ==> (n = 1) \/ (n = 2) \/ (n = 3).
   By contradiction, suppose n <> 1 /\ n <> 2 /\ n <> 3.
      Note n <> 0    by SQRT_EQ_0
      This means 4 <= n
      Hence  SQRT 4 <= SQRT n   by SQRT_LE
         so       2 <= SQRT n   by EVAL_TAC, SQRT 4 = 2
      This contradicts SQRT n = 1.
   Only-if part: n = 1 \/ n = 2 \/ n = 3 ==> SQRT n = 1
      All these are true        by EVAL_TAC
*)
Theorem SQRT_EQ_1:
    !n. (SQRT n = 1) <=> ((n = 1) \/ (n = 2) \/ (n = 3))
Proof
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `n <> 0` by metis_tac[SQRT_EQ_0] >>
    `4 <= n` by decide_tac >>
    `SQRT 4 <= SQRT n` by rw[SQRT_LE] >>
    `SQRT 4 = 2` by EVAL_TAC >>
    decide_tac,
    EVAL_TAC,
    EVAL_TAC,
    EVAL_TAC
  ]
QED

(* Theorem: SQRT (n ** 2) = n *)
(* Proof:
   If 1 < n, true                       by ROOT_POWER, 0 < 2
   Otherwise, n = 0 or n = 1.
      When n = 0,
           SQRT (0 ** 2) = SQRT 0 = 0   by SQRT_0
      When n = 1,
           SQRT (1 ** 2) = SQRT 1 = 1   by SQRT_1
*)
Theorem SQRT_EXP_2:
    !n. SQRT (n ** 2) = n
Proof
  rpt strip_tac >>
  Cases_on `1 < n` >-
  fs[ROOT_POWER] >>
  `(n = 0) \/ (n = 1)` by decide_tac >>
  rw[]
QED

(* Theorem alias *)
Theorem SQRT_OF_SQ = SQRT_EXP_2;
(* val SQRT_OF_SQ = |- !n. SQRT (n ** 2) = n: thm *)

(* Theorem: (n <= SQRT n) <=> ((n = 0) \/ (n = 1)) *)
(* Proof:
   If part: (n <= SQRT n) ==> ((n = 0) \/ (n = 1))
     By contradiction, suppose n <> 0 /\ n <> 1.
     Then 1 < n, implying n ** 2 <= SQRT n ** 2   by EXP_BASE_LE_MONO
      but SQRT n ** 2 <= n                        by SQRT_PROPERTY
       so n ** 2 <= n                             by LESS_EQ_TRANS
       or n * n <= n * 1                          by EXP_2
       or     n <= 1                              by LE_MULT_LCANCEL, n <> 0.
     This contradicts 1 < n.
   Only-if part: ((n = 0) \/ (n = 1)) ==> (n <= SQRT n)
     This is to show:
     (1) 0 <= SQRT 0, true by SQRT 0 = 0          by SQRT_0
     (2) 1 <= SQRT 1, true by SQRT 1 = 1          by SQRT_1
*)
Theorem SQRT_GE_SELF:
    !n. (n <= SQRT n) <=> ((n = 0) \/ (n = 1))
Proof
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `1 < n` by decide_tac >>
    `n ** 2 <= SQRT n ** 2` by rw[EXP_BASE_LE_MONO] >>
    `SQRT n ** 2 <= n` by rw[SQRT_PROPERTY] >>
    `n ** 2 <= n` by metis_tac[LESS_EQ_TRANS] >>
    `n * n <= n * 1` by metis_tac[EXP_2, MULT_RIGHT_1] >>
    `n <= 1` by metis_tac[LE_MULT_LCANCEL] >>
    decide_tac,
    rw[],
    rw[]
  ]
QED

(* Theorem: (SQRT n = n) <=> ((n = 0) \/ (n = 1)) *)
(* Proof: by ROOT_EQ_SELF, 0 < 2 *)
Theorem SQRT_EQ_SELF:
    !n. (SQRT n = n) <=> ((n = 0) \/ (n = 1))
Proof
  rw[ROOT_EQ_SELF]
QED

(* Theorem: SQRT n < m ==> n < m ** 2 *)
(* Proof:
                     SQRT n < m
   ==>        SUC (SQRT n) <= m                by arithmetic
   ==> (SUC (SQRT m)) ** 2 <= m ** 2           by EXP_EXP_LE_MONO
   But n < (SUC (SQRT n)) ** 2                 by SQRT_PROPERTY
   Thus n < m ** 2                             by inequality
*)
Theorem SQRT_LT_IMP:
  !n m. SQRT n < m ==> n < m ** 2
Proof
  rpt strip_tac >>
  `SUC (SQRT n) <= m` by decide_tac >>
  `SUC (SQRT n) ** 2 <= m ** 2` by simp[EXP_EXP_LE_MONO] >>
  `n < SUC (SQRT n) ** 2` by simp[SQRT_PROPERTY] >>
  decide_tac
QED

(* Theorem: n < SQRT m ==> n ** 2 < m *)
(* Proof:
                   n < SQRT m
   ==>        n ** 2 < (SQRT m) ** 2           by EXP_EXP_LT_MONO
   But        (SQRT m) ** 2 <= m               by SQRT_PROPERTY
   Thus       n ** 2 < m                       by inequality
*)
Theorem LT_SQRT_IMP:
  !n m. n < SQRT m ==> n ** 2 < m
Proof
  rpt strip_tac >>
  `n ** 2 < (SQRT m) ** 2` by simp[EXP_EXP_LT_MONO] >>
  `(SQRT m) ** 2 <= m` by simp[SQRT_PROPERTY] >>
  decide_tac
QED

(* Theorem: SQRT n < SQRT m ==> n < m *)
(* Proof:
       SQRT n < SQRT m
   ==>      n < (SQRT m) ** 2      by SQRT_LT_IMP
   and (SQRT m) ** 2 <= m          by SQRT_PROPERTY
    so      n < m                  by inequality
*)
Theorem SQRT_LT_SQRT:
  !n m. SQRT n < SQRT m ==> n < m
Proof
  rpt strip_tac >>
  imp_res_tac SQRT_LT_IMP >>
  `(SQRT m) ** 2 <= m` by simp[SQRT_PROPERTY] >>
  decide_tac
QED

(* Non-theorems:
   SQRT n <= SQRT m ==> n <= m
   counter-example: SQRT 5 = 2 = SQRT 4, but 5 > 4.

   n < m ==> SQRT n < SQRT m
   counter-example: 4 < 5, but SQRT 4 = 2 = SQRT 5.
*)

(* ------------------------------------------------------------------------- *)
(* Logarithm                                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < a ==> LOG a (a ** n) = n *)
(* Proof:
     LOG a (a ** n)
   = LOG a ((a ** n) * 1)     by MULT_RIGHT_1
   = n + LOG a 1              by LOG_EXP
   = n + 0                    by LOG_1
   = n                        by ADD_0
*)
Theorem LOG_EXACT_EXP:
    !a. 1 < a ==> !n. LOG a (a ** n) = n
Proof
  metis_tac[MULT_RIGHT_1, LOG_EXP, LOG_1, ADD_0, DECIDE``0 < 1``]
QED

(* Theorem: 1 < a /\ 0 < b /\ b <= a ** n ==> LOG a b <= n *)
(* Proof:
   Given     b <= a ** n
       LOG a b <= LOG a (a ** n)   by LOG_LE_MONO
                = n                by LOG_EXACT_EXP
*)
Theorem EXP_TO_LOG:
    !a b n. 1 < a /\ 0 < b /\ b <= a ** n ==> LOG a b <= n
Proof
  metis_tac[LOG_LE_MONO, LOG_EXACT_EXP]
QED

(* Theorem: 1 < a /\ 0 < n ==> !p. (LOG a n = p) <=> (a ** p <= n /\ n < a ** SUC p) *)
(* Proof:
   If part: 1 < a /\ 0 < n ==> a ** LOG a n <= n /\ n < a ** SUC (LOG a n)
      This is true by LOG.
   Only-if part: a ** p <= n /\ n < a ** SUC p ==> LOG a n = p
      This is true by LOG_UNIQUE
*)
Theorem LOG_THM:
    !a n. 1 < a /\ 0 < n ==> !p. (LOG a n = p) <=> (a ** p <= n /\ n < a ** SUC p)
Proof
  metis_tac[LOG, LOG_UNIQUE]
QED

(* Theorem: LOG m n = if m <= 1 \/ (n = 0) then LOG m n
            else if n < m then 0 else SUC (LOG m (n DIV m)) *)
(* Proof: by LOG_RWT *)
Theorem LOG_EVAL: (* was: "LOG_EVAL[compute]" *)
    !m n. LOG m n = if m <= 1 \/ (n = 0) then LOG m n
         else if n < m then 0 else SUC (LOG m (n DIV m))
Proof
  rw[LOG_RWT]
QED
(* Put to computeLib for LOG evaluation of any base *)

(*
> EVAL ``MAP (LOG 3) [1 .. 20]``; =
      [0; 0; 1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2]: thm
> EVAL ``MAP (LOG 3) [1 .. 30]``; =
      [0; 0; 1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 3; 3; 3; 3]: thm
*)

(* Theorem: 1 < a /\ 0 < n ==>
           !p. (LOG a n = p) <=> SUC n <= a ** SUC p /\ a ** SUC p <= a * n *)
(* Proof:
   Note !p. LOG a n = p
        <=> n < a ** SUC p /\ a ** p <= n                by LOG_THM
        <=> n < a ** SUC p /\ a * a ** p <= a * n        by LE_MULT_LCANCEL
        <=> n < a ** SUC p /\ a ** SUC p <= a * n        by EXP
        <=> SUC n <= a ** SUC p /\ a ** SUC p <= a * n   by arithmetic
*)
Theorem LOG_TEST:
    !a n. 1 < a /\ 0 < n ==>
   !p. (LOG a n = p) <=> SUC n <= a ** SUC p /\ a ** SUC p <= a * n
Proof
  rw[EQ_IMP_THM] >| [
    `n < a ** SUC (LOG a n)` by metis_tac[LOG_THM] >>
    decide_tac,
    `a ** (LOG a n) <= n` by metis_tac[LOG_THM] >>
    rw[EXP],
    `a * a ** p <= a * n` by fs[EXP] >>
    `a ** p <= n` by fs[] >>
    `n < a ** SUC p` by decide_tac >>
    metis_tac[LOG_THM]
  ]
QED

(* For continuous functions, log_b (x ** y) = y * log_b x. *)

(* Theorem: 1 < b /\ 0 < x /\ 0 < n ==>
           n * LOG b x <= LOG b (x ** n) /\ LOG b (x ** n) < n * SUC (LOG b x) *)
(* Proof:
   Note:
> LOG_THM |> SPEC ``b:num`` |> SPEC ``x:num``;
val it = |- 1 < b /\ 0 < x ==> !p. LOG b x = p <=> b ** p <= x /\ x < b ** SUC p: thm
> LOG_THM |> SPEC ``b:num`` |> SPEC ``(x:num) ** n``;
val it = |- 1 < b /\ 0 < x ** n ==>
   !p. LOG b (x ** n) = p <=> b ** p <= x ** n /\ x ** n < b ** SUC p: thm

   Let y = LOG b x, z = LOG b (x ** n).
   Then b ** y <= x /\ x < b ** SUC y              by LOG_THM, (1)
    and b ** z <= x ** n /\ x ** n < b ** SUC z    by LOG_THM, (2)
   From (1),
        b ** (n * y) <= x ** n /\                  by EXP_EXP_LE_MONO, EXP_EXP_MULT
        x ** n < b ** (n * SUC y)                  by EXP_EXP_LT_MONO, EXP_EXP_MULT, 0 < n
   Cross combine with (2),
        b ** (n * y) <= x ** n < b ** SUC z
    and b ** z <= x ** n < b ** (n * y)
    ==> n * y < SUC z /\ z < n * SUC y             by EXP_BASE_LT_MONO
     or    n * y <= z /\ z < n * SUC y
*)
Theorem LOG_POWER:
    !b x n. 1 < b /\ 0 < x /\ 0 < n ==>
           n * LOG b x <= LOG b (x ** n) /\ LOG b (x ** n) < n * SUC (LOG b x)
Proof
  ntac 4 strip_tac >>
  `0 < x ** n` by rw[] >>
  qabbrev_tac `y = LOG b x` >>
  qabbrev_tac `z = LOG b (x ** n)` >>
  `b ** y <= x /\ x < b ** SUC y` by metis_tac[LOG_THM] >>
  `b ** z <= x ** n /\ x ** n < b ** SUC z` by metis_tac[LOG_THM] >>
  `b ** (y * n) <= x ** n` by rw[EXP_EXP_MULT] >>
  `x ** n < b ** ((SUC y) * n)` by rw[EXP_EXP_MULT] >>
  `b ** (y * n) < b ** SUC z` by decide_tac >>
  `b ** z < b ** (SUC y * n)` by decide_tac >>
  `y * n < SUC z` by metis_tac[EXP_BASE_LT_MONO] >>
  `z < SUC y * n` by metis_tac[EXP_BASE_LT_MONO] >>
  decide_tac
QED

(* Theorem: 1 < a /\ 0 < n /\ a <= b ==> LOG b n <= LOG a n *)
(* Proof:
   Let x = LOG a n, y = LOG b n. To show: y <= x.
   By contradiction, suppose x < y.
   Then SUC x <= y.
   Note a ** x <= n /\ n < a ** SUC x     by LOG_THM
    and b ** y <= n /\ n < b ** SUC y     by LOG_THM
    But a <= b
        a ** SUC x
     <= b ** SUC x         by EXP_EXP_LE_MONO, 0 < SUC x
     <= b ** y             by EXP_BASE_LEQ_MONO_IMP, SUC x <= y
   This leads to n < a ** SUC x <= b ** y <= n, a contradiction.
*)
Theorem LOG_LE_REVERSE:
    !a b n. 1 < a /\ 0 < n /\ a <= b ==> LOG b n <= LOG a n
Proof
  rpt strip_tac >>
  qabbrev_tac `x = LOG a n` >>
  qabbrev_tac `y = LOG b n` >>
  spose_not_then strip_assume_tac >>
  `1 < b /\ SUC x <= y` by decide_tac >>
  `a ** x <= n /\ n < a ** SUC x` by metis_tac[LOG_THM] >>
  `b ** y <= n /\ n < b ** SUC y` by metis_tac[LOG_THM] >>
  `a ** SUC x <= b ** SUC x` by rw[EXP_EXP_LE_MONO] >>
  `b ** SUC x <= b ** y` by rw[EXP_BASE_LEQ_MONO_IMP] >>
  decide_tac
QED

(* ----------------------------------------------------------------------- *)

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


(* Overload LOG base 2 *)
val _ = overload_on ("LOG2", ``\n. LOG 2 n``);

(* Theorem: LOG2 1 = 0 *)
(* Proof:
   LOG_1 |> SPEC ``2``;
   val it = |- 1 < 2 ==> LOG2 1 = 0: thm
*)
Theorem LOG2_1[simp]:
    LOG2 1 = 0
Proof
  rw[LOG_1]
QED

(* Theorem: LOG2 2 = 1 *)
(* Proof:
   LOG_BASE |> SPEC ``2``;
   val it = |- 1 < 2 ==> LOG2 2 = 1: thm
*)
Theorem LOG2_2[simp]:
    LOG2 2 = 1
Proof
  rw[LOG_BASE]
QED

(* Obtain a theorem *)
Theorem LOG2_THM =
    LOG_THM |> SPEC ``2`` |> SIMP_RULE (srw_ss())[];
(* val LOG2_THM = |- !n. 0 < n ==> !p. (LOG2 n = p) <=> 2 ** p <= n /\ n < 2 ** SUC p: thm *)

(* Obtain a theorem *)
Theorem LOG2_PROPERTY = LOG |> SPEC ``2`` |> SIMP_RULE (srw_ss())[];
(* val LOG2_PROPERTY =  |- !n. 0 < n ==> 2 ** LOG2 n <= n /\ n < 2 ** SUC (LOG2 n): thm *)

(* Theorem: 0 < n ==> 2 ** LOG2 n <= n) *)
(* Proof: by LOG2_PROPERTY *)
Theorem TWO_EXP_LOG2_LE:
    !n. 0 < n ==> 2 ** LOG2 n <= n
Proof
  rw[LOG2_PROPERTY]
QED

(* Obtain a theorem *)
Theorem LOG2_UNIQUE =
    LOG_UNIQUE |> SPEC ``2`` |> SPEC ``n:num`` |> SPEC ``m:num`` |> GEN_ALL;
(* val LOG2_UNIQUE = |- !n m. 2 ** m <= n /\ n < 2 ** SUC m ==> LOG2 n = m: thm *)

(* Theorem: 0 < n ==> ((LOG2 n = 0) <=> (n = 1)) *)
(* Proof:
   LOG_EQ_0 |> SPEC ``2``;
   |- !b. 1 < 2 /\ 0 < b ==> (LOG2 b = 0 <=> b < 2)
*)
Theorem LOG2_EQ_0:
    !n. 0 < n ==> ((LOG2 n = 0) <=> (n = 1))
Proof
  rw[LOG_EQ_0]
QED

(* Theorem: 0 < n ==> LOG2 n = 1 <=> (n = 2) \/ (n = 3) *)
(* Proof:
   If part: LOG2 n = 1 ==> n = 2 \/ n = 3
      Note  2 ** 1 <= n /\ n < 2 ** SUC 1  by LOG2_PROPERTY
        or       2 <= n /\ n < 4           by arithmetic
      Thus  n = 2 or n = 3.
   Only-if part: LOG2 2 = 1 /\ LOG2 3 = 1
      Note LOG2 2 = 1                      by LOG2_2
       and LOG2 3 = 1                      by LOG2_UNIQUE
     since 2 ** 1 <= 3 /\ 3 < 2 ** SUC 1 ==> (LOG2 3 = 1)
*)
Theorem LOG2_EQ_1:
    !n. 0 < n ==> ((LOG2 n = 1) <=> ((n = 2) \/ (n = 3)))
Proof
  rw_tac std_ss[EQ_IMP_THM] >| [
    imp_res_tac LOG2_PROPERTY >>
    rfs[],
    rw[],
    irule LOG2_UNIQUE >>
    simp[]
  ]
QED

(* Obtain theorem *)
Theorem LOG2_LE_MONO =
    LOG_LE_MONO |> SPEC ``2`` |> SPEC ``n:num`` |> SPEC ``m:num``
                |> SIMP_RULE (srw_ss())[] |> GEN_ALL;
(* val LOG2_LE_MONO = |- !n m. 0 < n ==> n <= m ==> LOG2 n <= LOG2 m: thm *)

(* Theorem: 0 < n /\ n <= m ==> LOG2 n <= LOG2 m *)
(* Proof: by LOG_LE_MONO *)
Theorem LOG2_LE:
    !n m. 0 < n /\ n <= m ==> LOG2 n <= LOG2 m
Proof
  rw[LOG_LE_MONO, DECIDE``1 < 2``]
QED

(* Note: next is not LOG2_LT_MONO! *)

(* Theorem: 0 < n /\ n < m ==> LOG2 n <= LOG2 m *)
(* Proof:
   Since n < m ==> n <= m   by LESS_IMP_LESS_OR_EQ
   This is true             by LOG_LE_MONO
*)
Theorem LOG2_LT:
    !n m. 0 < n /\ n < m ==> LOG2 n <= LOG2 m
Proof
  rw[LOG_LE_MONO, LESS_IMP_LESS_OR_EQ, DECIDE``1 < 2``]
QED

(* Theorem: 0 < n ==> LOG2 n < n *)
(* Proof:
       LOG2 n
     < 2 ** (LOG2 n)     by X_LT_EXP_X, 1 < 2
    <= n                 by LOG2_PROPERTY, 0 < n
*)
Theorem LOG2_LT_SELF:
    !n. 0 < n ==> LOG2 n < n
Proof
  rpt strip_tac >>
  `LOG2 n < 2 ** (LOG2 n)` by rw[X_LT_EXP_X] >>
  `2 ** LOG2 n <= n` by rw[LOG2_PROPERTY] >>
  decide_tac
QED

(* Theorem: 0 < n ==> LOG2 n <> n *)
(* Proof:
   Note n < LOG2 n     by LOG2_LT_SELF
   Thus n <> LOG2 n    by arithmetic
*)
Theorem LOG2_NEQ_SELF:
    !n. 0 < n ==> LOG2 n <> n
Proof
  rpt strip_tac >>
  `LOG2 n < n` by rw[LOG2_LT_SELF] >>
  decide_tac
QED

(* Theorem: LOG2 n = n ==> n = 0 *)
(* Proof: by LOG2_NEQ_SELF *)
Theorem LOG2_EQ_SELF:
    !n. (LOG2 n = n) ==> (n = 0)
Proof
  metis_tac[LOG2_NEQ_SELF, DECIDE``~(0 < n) <=> (n = 0)``]
QED

(* Theorem: 1 < n ==> 0 < LOG2 n *)
(* Proof:
       1 < n
   ==> 2 <= n
   ==> LOG2 2 <= LOG2 n     by LOG2_LE
   ==>      1 <= LOG2 n     by LOG_BASE, LOG2 2 = 1
    or      0 < LOG2 n
*)
Theorem LOG2_POS[simp]:
    !n. 1 < n ==> 0 < LOG2 n
Proof
  rpt strip_tac >>
  `LOG2 2 = 1` by rw[LOG_BASE, DECIDE``1 < 2``] >>
  `2 <= n` by decide_tac >>
  `LOG2 2 <= LOG2 n` by rw[LOG2_LE] >>
  decide_tac
QED

(* Theorem: 1 < n ==> 1 < 2 * LOG2 n *)
(* Proof:
       1 < n
   ==> 2 <= n
   ==> LOG2 2 <= LOG2 n        by LOG2_LE
   ==>      1 <= LOG2 n        by LOG_BASE, LOG2 2 = 1
   ==>  2 * 1 <= 2 * LOG2 n    by LE_MULT_LCANCEL
    or      1 < 2 * LOG2 n
*)
Theorem LOG2_TWICE_LT:
    !n. 1 < n ==> 1 < 2 * (LOG2 n)
Proof
  rpt strip_tac >>
  `LOG2 2 = 1` by rw[LOG_BASE, DECIDE``1 < 2``] >>
  `2 <= n` by decide_tac >>
  `LOG2 2 <= LOG2 n` by rw[LOG2_LE] >>
  `1 <= LOG2 n` by decide_tac >>
  `2 <= 2 * LOG2 n` by rw_tac arith_ss[LE_MULT_LCANCEL, DECIDE``0 < 2``] >>
  decide_tac
QED

(* Theorem: 1 < n ==> 4 <= (2 * (LOG2 n)) ** 2 *)
(* Proof:
       1 < n
   ==> 2 <= n
   ==> LOG2 2 <= LOG2 n              by LOG2_LE
   ==>      1 <= LOG2 n              by LOG2_2, or LOG_BASE, LOG2 2 = 1
   ==>  2 * 1 <= 2 * LOG2 n          by LE_MULT_LCANCEL
   ==> 2 ** 2 <= (2 * LOG2 n) ** 2   by EXP_EXP_LE_MONO
   ==>      4 <= (2 * LOG2 n) ** 2
*)
Theorem LOG2_TWICE_SQ:
    !n. 1 < n ==> 4 <= (2 * (LOG2 n)) ** 2
Proof
  rpt strip_tac >>
  `LOG2 2 = 1` by rw[] >>
  `2 <= n` by decide_tac >>
  `LOG2 2 <= LOG2 n` by rw[LOG2_LE] >>
  `1 <= LOG2 n` by decide_tac >>
  `2 <= 2 * LOG2 n` by rw_tac arith_ss[LE_MULT_LCANCEL, DECIDE``0 < 2``] >>
  `2 ** 2 <= (2 * LOG2 n) ** 2` by rw[EXP_EXP_LE_MONO, DECIDE``0 < 2``] >>
  `2 ** 2 = 4` by rw_tac arith_ss[] >>
  decide_tac
QED

(* Theorem: 0 < n ==> 4 <= (2 * SUC (LOG2 n)) ** 2 *)
(* Proof:
       0 < n
   ==> 1 <= n
   ==> LOG2 1 <= LOG2 n                    by LOG2_LE
   ==>      0 <= LOG2 n                    by LOG2_1, or LOG_BASE, LOG2 1 = 0
   ==>      1 <= SUC (LOG2 n)              by LESS_EQ_MONO
   ==>  2 * 1 <= 2 * SUC (LOG2 n)          by LE_MULT_LCANCEL
   ==> 2 ** 2 <= (2 * SUC (LOG2 n)) ** 2   by EXP_EXP_LE_MONO
   ==>      4 <= (2 * SUC (LOG2 n)) ** 2
*)
Theorem LOG2_SUC_TWICE_SQ:
    !n. 0 < n ==> 4 <= (2 * SUC (LOG2 n)) ** 2
Proof
  rpt strip_tac >>
  `LOG2 1 = 0` by rw[] >>
  `1 <= n` by decide_tac >>
  `LOG2 1 <= LOG2 n` by rw[LOG2_LE] >>
  `1 <= SUC (LOG2 n)` by decide_tac >>
  `2 <= 2 * SUC (LOG2 n)` by rw_tac arith_ss[LE_MULT_LCANCEL, DECIDE``0 < 2``] >>
  `2 ** 2 <= (2 * SUC (LOG2 n)) ** 2` by rw[EXP_EXP_LE_MONO, DECIDE``0 < 2``] >>
  `2 ** 2 = 4` by rw_tac arith_ss[] >>
  decide_tac
QED

(* Theorem: 1 < n ==> 1 < (SUC (LOG2 n)) ** 2 *)
(* Proof:
   Note 0 < LOG2 n                 by LOG2_POS, 1 < n
     so 1 < SUC (LOG2 n)           by arithmetic
    ==> 1 < (SUC (LOG2 n)) ** 2    by ONE_LT_EXP, 0 < 2
*)
Theorem LOG2_SUC_SQ:
    !n. 1 < n ==> 1 < (SUC (LOG2 n)) ** 2
Proof
  rpt strip_tac >>
  `0 < LOG2 n` by rw[] >>
  `1 < SUC (LOG2 n)` by decide_tac >>
  rw[ONE_LT_EXP]
QED

(* Theorem: LOG2 (2 ** n) = n *)
(* Proof: by LOG_EXACT_EXP *)
Theorem LOG2_2_EXP:
    !n. LOG2 (2 ** n) = n
Proof
  rw[LOG_EXACT_EXP]
QED

(* Theorem: (2 ** (LOG2 n) = n) <=> ?k. n = 2 ** k *)
(* Proof:
   If part: 2 ** LOG2 n = n ==> ?k. n = 2 ** k
      True by taking k = LOG2 n.
   Only-if part: 2 ** LOG2 (2 ** k) = 2 ** k
      Note LOG2 n = k               by LOG_EXACT_EXP, 1 < 2
        or n = 2 ** k = 2 ** LOG2 n.
*)
Theorem LOG2_EXACT_EXP:
    !n. (2 ** (LOG2 n) = n) <=> ?k. n = 2 ** k
Proof
  metis_tac[LOG2_2_EXP]
QED

(* Theorem: 0 < n ==> LOG2 (n * 2 ** m) = (LOG2 n) + m *)
(* Proof:
   LOG_EXP |> SPEC ``m:num`` |> SPEC ``2`` |> SPEC ``n:num``;
   val it = |- 1 < 2 /\ 0 < n ==> LOG2 (2 ** m * n) = m + LOG2 n: thm
*)
Theorem LOG2_MULT_EXP:
    !n m. 0 < n ==> (LOG2 (n * 2 ** m) = (LOG2 n) + m)
Proof
  rw[GSYM LOG_EXP]
QED

(* Theorem: 0 < n ==> (LOG2 (2 * n) = 1 + LOG2 n) *)
(* Proof:
   LOG_MULT |> SPEC ``2`` |> SPEC ``n:num``;
   val it = |- 1 < 2 /\ 0 < n ==> LOG2 (TWICE n) = SUC (LOG2 n): thm
*)
Theorem LOG2_TWICE:
    !n. 0 < n ==> (LOG2 (2 * n) = 1 + LOG2 n)
Proof
  rw[LOG_MULT]
QED

(* ----------------------------------------------------------------------- *)
