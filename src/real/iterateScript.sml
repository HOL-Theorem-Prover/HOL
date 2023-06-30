(* ========================================================================= *)
(*                                                                           *)
(*    Generic iterated operations and special cases of sums over N and R     *)
(*                                                                           *)
(*        (c) Copyright 2014-2015,                                           *)
(*                       Muhammad Qasim,                                     *)
(*                       Osman Hasan,                                        *)
(*                       Hardware Verification Group,                        *)
(*                       Concordia University                                *)
(*                                                                           *)
(*            Contact:  <m_qasi@ece.concordia.ca>                            *)
(*                                                                           *)
(*    Note: This theory was ported from HOL Light's iterate.ml               *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*              (c) Copyright, Lars Schewe 2007                              *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open numLib unwindLib tautLib Arith prim_recTheory combinTheory quotientTheory
     arithmeticTheory jrhUtils pairTheory mesonLib pred_setTheory hurdUtils
     optionTheory relationTheory;

open realTheory RealArith realSimps wellorderTheory cardinalTheory;

val _ = new_theory "iterate";

(* ------------------------------------------------------------------------- *)
(* MESON, METIS, SET_TAC, SET_RULE, ASSERT_TAC, ASM_ARITH_TAC                *)
(* ------------------------------------------------------------------------- *)

fun MESON ths tm = prove(tm,MESON_TAC ths);
fun METIS ths tm = prove(tm,METIS_TAC ths);

val DISC_RW_KILL = DISCH_TAC >> ONCE_ASM_REWRITE_TAC [] \\
                   POP_ASSUM K_TAC;

fun ASSERT_TAC tm = SUBGOAL_THEN tm STRIP_ASSUME_TAC;

val ASM_ARITH_TAC = rpt (POP_ASSUM MP_TAC) >> ARITH_TAC;
val ASM_REAL_ARITH_TAC = REAL_ASM_ARITH_TAC;

(* Minimal hol-light compatibility layer *)
val IMP_CONJ      = CONJ_EQ_IMP;     (* cardinalTheory *)
val FINITE_SUBSET = SUBSET_FINITE_I; (* pred_setTheory *)
val LE_0          = ZERO_LESS_EQ;    (* arithmeticTheory *)

(* ------------------------------------------------------------------------- *)
(* misc.                                                                     *)
(* ------------------------------------------------------------------------- *)

Theorem REAL_LT_BETWEEN: !a b:real. a < b <=> ?x. a < x /\ x < b
Proof metis_tac[REAL_MEAN, REAL_LT_TRANS]
QED

Theorem LOWER_BOUND_FINITE_SET_REAL:
  !f:('a->real) s. FINITE(s) ==> ?a. !x. x IN s ==> a <= f(x)
Proof
  gen_tac >> Induct_on ‘FINITE’ >> rw[DISJ_IMP_THM, FORALL_AND_THM] >>
  METIS_TAC[REAL_LE_TOTAL, REAL_LE_REFL, REAL_LE_TRANS]
QED


Theorem UPPER_BOUND_FINITE_SET_REAL:
  !f:('a->real) s. FINITE(s) ==> ?a. !x. x IN s ==> f(x) <= a
Proof
  gen_tac >> Induct_on ‘FINITE’ >> rw[DISJ_IMP_THM, FORALL_AND_THM] >>
  METIS_TAC[REAL_LE_TOTAL, REAL_LE_REFL, REAL_LE_TRANS]
QED

val REAL_LE_SQUARE_ABS = store_thm ("REAL_LE_SQUARE_ABS",
 ``!x y:real. abs(x) <= abs(y) <=> x pow 2 <= y pow 2``,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  EQ_TAC THEN DISCH_TAC THENL
  [MATCH_MP_TAC POW_LE THEN ASM_REAL_ARITH_TAC,
   CCONTR_TAC THEN UNDISCH_TAC ``abs (x:real) pow 2 <= abs y pow 2`` THEN
   REWRITE_TAC [TWO, REAL_NOT_LE] THEN MATCH_MP_TAC POW_LT THEN
   ASM_REAL_ARITH_TAC]);

val REAL_EQ_SQUARE_ABS = store_thm ("REAL_EQ_SQUARE_ABS",
 ``!x y:real. (abs x = abs y) <=> (x pow 2 = y pow 2)``,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM, REAL_LE_SQUARE_ABS]);

val REAL_HALF = store_thm ("REAL_HALF",
 ``(!e:real. &0 < e / &2 <=> &0 < e) /\
   (!e:real. e / &2 + e / &2 = e) /\
   (!e:real. &2 * (e / &2) = e)``,
  SIMP_TAC std_ss [REAL_LT_HALF1, REAL_HALF_DOUBLE, REAL_DIV_LMUL,
  REAL_ARITH ``2 <> 0:real``]);

val FINITE_SUBSET_IMAGE = store_thm ("FINITE_SUBSET_IMAGE",
 ``!f:'a->'b s t.
        FINITE(t) /\ t SUBSET (IMAGE f s) <=>
        ?s'. FINITE s' /\ s' SUBSET s /\ (t = IMAGE f s')``,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC, ASM_MESON_TAC[IMAGE_FINITE, IMAGE_SUBSET]] THEN
  STRIP_TAC THEN
  EXISTS_TAC ``IMAGE (\y. @x. x IN s /\ ((f:'a->'b)(x) = y)) t`` THEN
  ASM_SIMP_TAC std_ss [IMAGE_FINITE] THEN
  SIMP_TAC std_ss [EXTENSION, SUBSET_DEF, FORALL_IN_IMAGE] THEN CONJ_TAC THENL
   [METIS_TAC[SUBSET_DEF, IN_IMAGE], ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN X_GEN_TAC ``y:'b`` THEN
  SIMP_TAC std_ss [GSYM RIGHT_EXISTS_AND_THM] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[UNWIND_THM2, GSYM CONJ_ASSOC] THEN
  METIS_TAC [SUBSET_DEF, IN_IMAGE]);

val EXISTS_FINITE_SUBSET_IMAGE = store_thm ("EXISTS_FINITE_SUBSET_IMAGE",
 ``!P f s.
    (?t. FINITE t /\ t SUBSET IMAGE f s /\ P t) <=>
    (?t. FINITE t /\ t SUBSET s /\ P (IMAGE f t))``,
  REWRITE_TAC[FINITE_SUBSET_IMAGE, CONJ_ASSOC] THEN MESON_TAC[]);

val FORALL_FINITE_SUBSET_IMAGE = store_thm ("FORALL_FINITE_SUBSET_IMAGE",
 ``!P f s. (!t. FINITE t /\ t SUBSET IMAGE f s ==> P t) <=>
           (!t. FINITE t /\ t SUBSET s ==> P(IMAGE f t))``,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [METIS [] ``(FINITE t /\ t SUBSET IMAGE f s ==> P t) =
                            (\t. FINITE t /\ t SUBSET IMAGE f s ==> P t) t``] THEN
   ONCE_REWRITE_TAC [METIS [] ``(FINITE t /\ t SUBSET s ==> P (IMAGE f t)) =
                            (\t. FINITE t /\ t SUBSET s ==> P (IMAGE f t)) t``] THEN
   ONCE_REWRITE_TAC [MESON[] ``(!x. P x) <=> ~(?x. ~P x)``] THEN
   SIMP_TAC std_ss [NOT_IMP, GSYM CONJ_ASSOC, EXISTS_FINITE_SUBSET_IMAGE]);

val EMPTY_BIGUNION = store_thm ("EMPTY_BIGUNION",
 ``!s. (BIGUNION s = {}) <=> !t. t IN s ==> (t = {})``,
  SET_TAC[]);

Theorem UPPER_BOUND_FINITE_SET:
  !f:('a->num) s. FINITE(s) ==> ?a. !x. x IN s ==> f(x) <= a
Proof
  rpt strip_tac >> qexists ‘MAX_SET (IMAGE f s)’ >>
  rpt strip_tac >> irule X_LE_MAX_SET >> simp[]
QED

val REAL_BOUNDS_LT = store_thm ("REAL_BOUNDS_LT",
 ``!x k:real. -k < x /\ x < k <=> abs(x) < k``,
  REAL_ARITH_TAC);

Theorem LE_EXISTS: !m n:num. (m <= n) <=> (?d. n = m + d)
Proof
  simp[EQ_IMP_THM, PULL_EXISTS] >> rw[] >> qexists ‘n - m’ >> simp[]
QED

Theorem LT_EXISTS:
  !m n. (m < n) <=> (?d. n = m + SUC d)
Proof
  simp[EQ_IMP_THM] >> rw[] >> qexists ‘n - (m + 1)’ >> simp[]
QED

val BOUNDS_LINEAR = store_thm ("BOUNDS_LINEAR",
 ``!A B C. (!n:num. A * n <= B * n + C) <=> A <= B``,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[NOT_LESS_EQUAL] THEN
    DISCH_THEN(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LT_EXISTS]) THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB, LE_ADD_LCANCEL] THEN
    DISCH_THEN(MP_TAC o SPEC ``SUC C``) THEN
    REWRITE_TAC[NOT_LESS_EQUAL, MULT_CLAUSES, ADD_CLAUSES, LT_SUC_LE] THEN
    ARITH_TAC,
    DISCH_THEN(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
    ARITH_TAC]);

val BOUNDS_LINEAR_0 = store_thm ("BOUNDS_LINEAR_0",
 ``!A B. (!n:num. A * n <= B) <=> (A = 0)``,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [``A:num``, ``0:num``, ``B:num``] BOUNDS_LINEAR) THEN
  REWRITE_TAC[MULT_CLAUSES, ADD_CLAUSES, LE]);

val REAL_LE_BETWEEN = store_thm ("REAL_LE_BETWEEN",
 ``!a b. a <= b <=> ?x:real. a <= x /\ x <= b``,
  MESON_TAC[REAL_LE_TRANS, REAL_LE_REFL]);

val BIGUNION_GSPEC = store_thm ("BIGUNION_GSPEC",
 ``(!P f. BIGUNION {f x | P x} = {a | ?x. P x /\ a IN (f x)}) /\
   (!P f. BIGUNION {f x y | P x y} = {a | ?x y. P x y /\ a IN (f x y)}) /\
   (!P f. BIGUNION {f x y z | P x y z} =
            {a | ?x y z. P x y z /\ a IN (f x y z)})``,
  REPEAT STRIP_TAC THEN GEN_REWR_TAC I [EXTENSION] THEN
  SIMP_TAC std_ss [IN_BIGUNION, GSPECIFICATION, EXISTS_PROD] THEN MESON_TAC[]);

val BIGINTER_GSPEC = store_thm ("BIGINTER_GSPEC",
 ``(!P f. BIGINTER {f x | P x} = {a | !x. P x ==> a IN (f x)}) /\
   (!P f. BIGINTER {f x y | P x y} = {a | !x y. P x y ==> a IN (f x y)}) /\
   (!P f. BIGINTER {f x y z | P x y z} =
                {a | !x y z. P x y z ==> a IN (f x y z)})``,
  REPEAT STRIP_TAC THEN GEN_REWR_TAC I [EXTENSION] THEN
  SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION, EXISTS_PROD] THEN MESON_TAC[]);

val FINITE_POWERSET = store_thm ("FINITE_POWERSET",
  ``!s. FINITE s ==> FINITE {t | t SUBSET s}``,
    METIS_TAC [FINITE_POW, POW_DEF]);

val LE_ADD = store_thm ("LE_ADD",
 ``!m n:num. m <= m + n``,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC arith_ss [LE, ADD_CLAUSES, LESS_EQ_REFL]);

val LE_ADDR = store_thm ("LE_ADDR",
 ``!m n:num. n <= m + n``,
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC LE_ADD);

val ADD_SUB2 = store_thm ("ADD_SUB2",
 ``!m n:num. (m + n) - m = n``,
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC ADD_SUB);

val ADD_SUBR2 = store_thm ("ADD_SUBR2",
 ``!m n:num. m - (m + n) = 0``,
  REWRITE_TAC[SUB_EQ_0, LESS_EQ_ADD]);

val ADD_SUBR = store_thm ("ADD_SUBR",
 ``!m n:num. n - (m + n) = 0``,
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC ADD_SUBR2);

val TRANSITIVE_STEPWISE_LE_EQ = store_thm ("TRANSITIVE_STEPWISE_LE_EQ",
 ``!R. (!x. R x x) /\ (!x y z. R x y /\ R y z ==> R x z)
       ==> ((!m n. m <= n ==> R m n) <=> (!n. R n (SUC n)))``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC std_ss [LE, LESS_EQ_REFL] THEN
  DISCH_TAC THEN SIMP_TAC std_ss [LE_EXISTS, LEFT_IMP_EXISTS_THM] THEN
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN ASM_MESON_TAC[]);

val TRANSITIVE_STEPWISE_LE = store_thm ("TRANSITIVE_STEPWISE_LE",
 ``!R. (!x. R x x) /\ (!x y z. R x y /\ R y z ==> R x z) /\
       (!n. R n (SUC n))
       ==> !m n. m <= n ==> R m n``,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(a /\ a' ==> (c <=> b)) ==> a /\ a' /\ b ==> c`) THEN
  MATCH_ACCEPT_TAC TRANSITIVE_STEPWISE_LE_EQ);

val LAMBDA_PAIR = store_thm ("LAMBDA_PAIR",
 ``(\(x,y). P x y) = (\p. P (FST p) (SND p))``,
  SIMP_TAC std_ss [FUN_EQ_THM, FORALL_PROD] THEN
  SIMP_TAC std_ss []);

val NOT_EQ = store_thm ("NOT_EQ",
 ``!a b. (a <> b) = ~(a = b)``, METIS_TAC []);

val ABS_LE_0 = store_thm ("ABS_LE_0",
 ``!x:real. abs x <= &0 <=> (x = 0)``,
  MESON_TAC[REAL_LE_ANTISYM, ABS_ZERO, ABS_POS]);

val REAL_OF_NUM_GE = store_thm ("REAL_OF_NUM_GE",
 ``!m n. &m >= (&n:real) <=> m >= n``,
  REWRITE_TAC[GE, real_ge, REAL_OF_NUM_LE]);

val POWERSET_CLAUSES = store_thm ("POWERSET_CLAUSES",
 ``({s | s SUBSET {}} = {{}}) /\
   ((!a:'a t. {s | s SUBSET (a INSERT t)} =
            {s | s SUBSET t} UNION IMAGE (\s. a INSERT s) {s | s SUBSET t}))``,
  REWRITE_TAC[SUBSET_INSERT_DELETE, SUBSET_EMPTY, SET_RULE
   ``(!a. {x | x = a} = {a}) /\ (!a. {x | a = x} = {a})``] THEN
  MAP_EVERY X_GEN_TAC [``a:'a``, ``t:'a->bool``] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[UNION_SUBSET] THEN
  ONCE_REWRITE_TAC[SUBSET_DEF] THEN
  SIMP_TAC std_ss [FORALL_IN_IMAGE, FORALL_IN_GSPEC] THEN
  SIMP_TAC std_ss [GSPECIFICATION, IN_UNION, IN_IMAGE] THEN
  CONJ_TAC THENL [ALL_TAC, SET_TAC[]] THEN
  X_GEN_TAC ``s:'a->bool`` THEN
  ASM_CASES_TAC ``(a:'a) IN s`` THENL [ALL_TAC, ASM_SET_TAC[]] THEN
  STRIP_TAC THEN DISJ2_TAC THEN EXISTS_TAC ``s DELETE (a:'a)`` THEN
  ASM_SET_TAC[]);

val REAL_LT_LCANCEL_IMP = store_thm ("REAL_LT_LCANCEL_IMP",
 ``!x y z:real. &0 < x /\ x * y < x * z ==> y < z``,
  METIS_TAC [REAL_LT_LMUL]);

val SIMPLE_IMAGE_GEN = store_thm ("SIMPLE_IMAGE_GEN",
 ``!f P. {f x | P x} = IMAGE f {x | P x}``,
  SET_TAC[]);

val REAL_LT_POW2 = store_thm ("REAL_LT_POW2",
 ``!n:num. (&0:real) < &2 pow n``,
  SIMP_TAC arith_ss [REAL_POW_LT, REAL_LT]);

val FUN_IN_IMAGE = store_thm ("FUN_IN_IMAGE",
 ``!f s x. x IN s ==> f(x) IN IMAGE f s``,
  SET_TAC[]);

Theorem DIFF_BIGINTER2 : (* was: DIFF_BIGINTER *)
    !u s. u DIFF BIGINTER s = BIGUNION {u DIFF t | t IN s}
Proof
  SIMP_TAC std_ss [BIGUNION_GSPEC] THEN SET_TAC[]
QED

val BIGINTER_BIGUNION = store_thm ("BIGINTER_BIGUNION",
 ``!s. BIGINTER s = UNIV DIFF (BIGUNION {UNIV DIFF t | t IN s})``,
  REWRITE_TAC[GSYM DIFF_BIGINTER2] THEN SET_TAC[]);

val BIGUNION_BIGINTER = store_thm ("BIGUNION_BIGINTER",
 ``!s. BIGUNION s = UNIV DIFF (BIGINTER {UNIV DIFF t | t IN s})``,
  GEN_TAC THEN GEN_REWR_TAC I [EXTENSION] THEN
  SIMP_TAC std_ss [IN_BIGUNION, IN_UNIV, IN_DIFF, BIGINTER_GSPEC,
   GSPECIFICATION] THEN
  MESON_TAC[]);

(* for HOL-Light compatibility *)
Theorem REAL_LT_INV2 = REAL_LT_INV

val REAL_WLOG_LE = store_thm ("REAL_WLOG_LE",
 ``(!x y:real. P x y <=> P y x) /\ (!x y. x <= y ==> P x y) ==> !x y. P x y``,
  METIS_TAC[REAL_LE_TOTAL]);

val REAL_WLOG_LT = store_thm ("REAL_WLOG_LT",
 ``(!x. P x x) /\ (!x y. P x y <=> P y x) /\ (!x y. x < y ==> P x y)
   ==> !x y:real. P x y``,
  METIS_TAC[REAL_LT_TOTAL]);

(* ------------------------------------------------------------------------- *)
(* Recursion over finite sets; based on Ching-Tsun's code (archive 713).     *)
(* ------------------------------------------------------------------------- *)

val FINREC = Define
  `(FINREC (f:'a->'b->'b) b s a 0 <=> (s = {}) /\ (a = b)) /\
   (FINREC (f:'a->'b->'b) b s a (SUC n) <=>
                ?x c. x IN s /\
                      FINREC f b (s DELETE x) c n /\
                      (a = f x c))`;

val FINREC_1_LEMMA = store_thm ("FINREC_1_LEMMA",
  ``!f b s a. FINREC f b s a (SUC 0) <=> ?x. (s = {x}) /\ (a = f x b)``,
  REWRITE_TAC[FINREC] THEN REPEAT GEN_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  SIMP_TAC std_ss [GSPECIFICATION] THEN EQ_TAC THENL [METIS_TAC [DELETE_EQ_SING],
  STRIP_TAC THEN ASM_REWRITE_TAC [IN_SING, SING_DELETE]]);

val FINREC_SUC_LEMMA = store_thm ("FINREC_SUC_LEMMA",
  ``!(f:'a->'b->'b) b.
           (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
           ==> !n s z.
                  FINREC f b s z (SUC n)
                  ==> !x. x IN s ==> ?w. FINREC f b (s DELETE x) w n /\
                                         (z = f x w)``,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
  [REWRITE_TAC[FINREC_1_LEMMA] THEN REWRITE_TAC[FINREC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_INSERT, NOT_IN_EMPTY] THEN
  DISCH_THEN SUBST1_TAC THEN EXISTS_TAC ``b:'b`` THEN
  ASM_REWRITE_TAC[SING_DELETE], REPEAT GEN_TAC THEN
  GEN_REWR_TAC LAND_CONV [FINREC] THEN
  DISCH_THEN(X_CHOOSE_THEN ``y:'a`` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN ``c:'b`` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC ``x:'a`` THEN DISCH_TAC THEN
  ASM_CASES_TAC ``x:'a = y`` THEN ASM_REWRITE_TAC[] THENL
  [EXISTS_TAC ``c:'b`` THEN ASM_REWRITE_TAC[],
  UNDISCH_TAC ``FINREC (f:'a->'b->'b) b (s DELETE y) c (SUC n)`` THEN
  DISCH_THEN(ANTE_RES_THEN (MP_TAC o SPEC ``x:'a``)) THEN
  ONCE_ASM_REWRITE_TAC[IN_DELETE] THEN ONCE_ASM_REWRITE_TAC[IN_DELETE] THEN
  ONCE_ASM_REWRITE_TAC[IN_DELETE] THEN ONCE_ASM_REWRITE_TAC[IN_DELETE] THEN
  ONCE_ASM_REWRITE_TAC[IN_DELETE] THEN
  DISCH_THEN(X_CHOOSE_THEN ``v:'b`` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC ``(f:'a->'b->'b) y v`` THEN ONCE_ASM_REWRITE_TAC[FINREC] THEN
  CONJ_TAC THENL [MAP_EVERY EXISTS_TAC [``y:'a``, ``v:'b``] THEN
  ONCE_REWRITE_TAC[DELETE_COMM] THEN ONCE_ASM_REWRITE_TAC[IN_DELETE] THEN
  ONCE_ASM_REWRITE_TAC[IN_DELETE] THEN ONCE_ASM_REWRITE_TAC[IN_DELETE] THEN
  METIS_TAC [], METIS_TAC []]]]);

val FINREC_UNIQUE_LEMMA = store_thm ("FINREC_UNIQUE_LEMMA",
  ``!(f:'a->'b->'b) b.
          (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
          ==> !n1 n2 s a1 a2.
                 FINREC f b s a1 n1 /\ FINREC f b s a2 n2
                 ==> (a1 = a2) /\ (n1 = n2)``,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN INDUCT_TAC THENL
  [REWRITE_TAC[FINREC] THEN MESON_TAC[NOT_IN_EMPTY],
  REWRITE_TAC[FINREC] THEN MESON_TAC[NOT_IN_EMPTY],
  REWRITE_TAC[FINREC] THEN MESON_TAC[NOT_IN_EMPTY],
  IMP_RES_THEN ASSUME_TAC FINREC_SUC_LEMMA THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fn th => MP_TAC(CONJUNCT1 th) THEN MP_TAC th) THEN
  DISCH_THEN(CONJUNCTS_THEN (ANTE_RES_THEN ASSUME_TAC)) THEN
  REWRITE_TAC[FINREC] THEN STRIP_TAC THEN ASM_MESON_TAC[]]);

val FINREC_EXISTS_LEMMA = store_thm ("FINREC_EXISTS_LEMMA",
  ``!(f:'a->'b->'b) b s. FINITE s ==> ?a n. FINREC f b s a n``,
  REPEAT GEN_TAC THEN
  KNOW_TAC ``(?a:'b n. FINREC f b s a n) = (\s. ?a:'b n. FINREC f b s a n) s`` THENL
  [FULL_SIMP_TAC std_ss [], DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN REPEAT STRIP_TAC THENL
  [MAP_EVERY EXISTS_TAC [``b:'b``, ``0:num``] THEN REWRITE_TAC[FINREC],
  MAP_EVERY EXISTS_TAC [``(f:'a->'b->'b) e a``, ``SUC n``] THEN
  REWRITE_TAC[FINREC] THEN MAP_EVERY EXISTS_TAC [``e:'a``, ``a:'b``] THEN
  FULL_SIMP_TAC std_ss [IN_INSERT] THEN
  EVAL_TAC THEN FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]]]);

val FINREC_FUN_LEMMA = store_thm ("FINREC_FUN_LEMMA",
  ``!P (R:'a->'b->'c->bool).
      (!s. P s ==> ?a n. R s a n) /\
      (!n1 n2 s a1 a2.
         R s a1 n1 /\ R s a2 n2 ==> (a1 = a2) /\ (n1 = n2)) ==>
      ?f. !s a. P s ==> ((?n. R s a n) <=> (f s = a))``,
  REPEAT STRIP_TAC THEN EXISTS_TAC ``\s:'a. @a:'b. ?n:'c. R s a n`` THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN EQ_TAC THENL [STRIP_TAC THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[],
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SELECT_CONV THEN ASM_MESON_TAC[]]);

Theorem FINREC_FUN :
    !(f:'a->'b->'b) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> ?g. (g {} = b) /\
                !s x. FINITE s /\ x IN s
                      ==> (g s = f x (g (s DELETE x)))
Proof
  REPEAT STRIP_TAC THEN IMP_RES_THEN MP_TAC FINREC_UNIQUE_LEMMA THEN
  REPEAT STRIP_TAC THEN
  KNOW_TAC ``!n1 n2 s a1 a2. FINREC f b s a1 n1 /\
                             FINREC f b s a2 n2 ==> (a1 = a2) /\ (n1 = n2)``
  THEN1 METIS_TAC [] THEN
  DISCH_THEN (MP_TAC o CONJ (SPECL [``f:'a->'b->'b``, ``b:'b``] FINREC_EXISTS_LEMMA)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINREC_FUN_LEMMA) THEN
  DISCH_THEN(X_CHOOSE_TAC ``g:('a->bool)->'b``) THEN
  EXISTS_TAC ``g:('a->bool)->'b`` THEN CONJ_TAC THENL
  [ SUBGOAL_THEN ``FINITE(EMPTY:'a->bool)``
    (ANTE_RES_THEN (fn th => GEN_REWR_TAC I [GSYM th])) THENL
     [REWRITE_TAC[FINITE_EMPTY],
      EXISTS_TAC ``0:num`` THEN REWRITE_TAC[FINREC]],
    REPEAT STRIP_TAC THEN
    ANTE_RES_THEN MP_TAC (ASSUME ``FINITE(s:'a->bool)``) THEN
    DISCH_THEN(ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC ``(g:('a->bool)->'b) s``) THEN
    REWRITE_TAC[] THEN REWRITE_TAC[GSYM LEFT_FORALL_IMP_THM] THEN
    INDUCT_TAC THENL
    [ ASM_REWRITE_TAC[FINREC] THEN DISCH_TAC THEN UNDISCH_TAC ``x:'a IN s`` THEN
      ASM_REWRITE_TAC[NOT_IN_EMPTY],
      IMP_RES_THEN ASSUME_TAC FINREC_SUC_LEMMA THEN
      DISCH_THEN(ANTE_RES_THEN (MP_TAC o SPEC ``x:'a``)) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN ``w:'b`` (CONJUNCTS_THEN ASSUME_TAC)) THEN
      SUBGOAL_THEN ``(g (s DELETE x:'a) = w:'b)`` SUBST1_TAC THENL
      [ SUBGOAL_THEN ``FINITE(s DELETE x:'a)`` MP_TAC THENL
        [ FULL_SIMP_TAC std_ss [FINITE_DELETE],
          DISCH_THEN(ANTE_RES_THEN (MP_TAC o GSYM)) THEN
          DISCH_THEN(fn th => REWRITE_TAC[th]) THEN
          METIS_TAC [] ],
        ASM_REWRITE_TAC [] ] ] ]
QED

val SET_RECURSION_LEMMA = store_thm ("SET_RECURSION_LEMMA",
 ``!(f:'a->'b->'b) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> ?g. (g {} = b) /\
                !x s. FINITE s
                      ==> (g (x INSERT s) =
                                if x IN s then g s else f x (g s))``,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC ``b:'b`` o MATCH_MP FINREC_FUN) THEN
  DISCH_THEN(X_CHOOSE_THEN ``g:('a->bool)->'b`` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC ``g:('a->bool)->'b`` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[GSYM ABSORPTION] THEN ASM_REWRITE_TAC[],
    SUBGOAL_THEN ``FINITE(x:'a INSERT s) /\ x IN (x INSERT s)`` MP_TAC THENL
     [REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[FINITE_INSERT],
      DISCH_THEN(ANTE_RES_THEN SUBST1_TAC) THEN
      REPEAT AP_TERM_TAC THEN UNDISCH_TAC ``~(x:'a IN s)`` THEN DISCH_TAC THEN
      EVAL_TAC THEN FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT, SUBSET_REFL]]]);

(* This is HOL Light's definition of ‘ITSET’ *)
Theorem ITSET_alt :
    !(f:'a->'b->'b) s b.
        (!x y z. f x (f y z) = f y (f x z)) /\ FINITE s ==>
         ITSET f s b =
         (@g. (g {} = b) /\
              !x s. FINITE s ==>
                    (g (x INSERT s) = if x IN s then g s else f x (g s))) s
Proof
    RW_TAC std_ss []
 >> SELECT_ELIM_TAC
 >> CONJ_TAC
 >- (MATCH_MP_TAC SET_RECURSION_LEMMA >> rw [])
 >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘FINITE s’ MP_TAC
 >> Q.SPEC_TAC (‘s’, ‘s’)
 >> HO_MATCH_MP_TAC FINITE_INDUCT
 >> CONJ_TAC >- rw [ITSET_THM, FINITE_EMPTY]
 >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!x s. FINITE s ==> P’
      (fn th => ONCE_REWRITE_TAC [MATCH_MP th (ASSUME “FINITE s”)])
 >> simp []
 >> Know ‘ITSET f (e INSERT s) b = f e (ITSET f (s DELETE e) b)’
 >- (MATCH_MP_TAC COMMUTING_ITSET_RECURSES >> rw [])
 >> Rewr'
 >> Suff ‘s DELETE e = s’ >- rw []
 >> rw [GSYM DELETE_NON_ELEMENT]
QED

Theorem FINITE_RECURSION :
    !(f:'a->'b->'b) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> (ITSET f {} b = b) /\
            !x s. FINITE s
                  ==> (ITSET f (x INSERT s) b =
                       if x IN s then ITSET f s b
                                 else f x (ITSET f s b))
Proof
    RW_TAC std_ss [ITSET_EMPTY]
 >> Cases_on `x IN s`
 >- (`x INSERT s = s` by PROVE_TAC [ABSORPTION] >> art [])
 >> ASM_SIMP_TAC std_ss []
 >> Know `ITSET f s b = ITSET f (s DELETE x) b`
 >- (`s DELETE x = s` by PROVE_TAC [DELETE_NON_ELEMENT] >> art [])
 >> Rewr'
 >> MATCH_MP_TAC COMMUTING_ITSET_RECURSES
 >> rename1 `i IN s` >> RW_TAC std_ss []
 >> Cases_on `x = y` >- art []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

val CARD_UNION_EQ = store_thm ("CARD_UNION_EQ",
  ``!s t u.
         FINITE u /\ (s INTER t = {}) /\ (s UNION t = u)
         ==> (CARD s + CARD t = CARD u)``,
  REPEAT STRIP_TAC THEN KNOW_TAC ``FINITE (s:'a->bool) /\ FINITE (t:'a->bool)``
  THENL [METIS_TAC [FINITE_UNION], ALL_TAC] THEN STRIP_TAC THEN
  ASSUME_TAC CARD_UNION THEN
  POP_ASSUM (MP_TAC o Q.SPEC `s`) THEN FULL_SIMP_TAC std_ss [] THEN
  DISCH_TAC THEN POP_ASSUM (MP_TAC o Q.SPEC `t`) THEN
  FULL_SIMP_TAC std_ss [CARD_EMPTY]);

val SUBSET_RESTRICT = store_thm ("SUBSET_RESTRICT",
 ``!s P. {x | x IN s /\ P x} SUBSET s``,
  SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION]);

val FINITE_RESTRICT = store_thm ("FINITE_RESTRICT",
 ``!s:'a->bool P. FINITE s ==> FINITE {x | x IN s /\ P x}``,
METIS_TAC[SUBSET_RESTRICT, SUBSET_FINITE]);

(* ------------------------------------------------------------------------- *)
(* Non-trivial intervals of reals are infinite.                              *)
(* ------------------------------------------------------------------------- *)

val FINITE_REAL_INTERVAL = store_thm ("FINITE_REAL_INTERVAL",
 ``(!a. ~FINITE {x:real | a < x}) /\
   (!a. ~FINITE {x:real | a <= x}) /\
   (!b. ~FINITE {x:real | x < b}) /\
   (!b. ~FINITE {x:real | x <= b}) /\
   (!a b. FINITE {x:real | a < x /\ x < b} <=> b <= a) /\
   (!a b. FINITE {x:real | a <= x /\ x < b} <=> b <= a) /\
   (!a b. FINITE {x:real | a < x /\ x <= b} <=> b <= a) /\
   (!a b. FINITE {x:real | a <= x /\ x <= b} <=> b <= a)``,
  SUBGOAL_THEN ``!a b. FINITE {x:real | a < x /\ x < b} <=> b <= a``
  ASSUME_TAC THENL
  [ (* goal 1 (of 2) *)
    REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
    ASM_CASES_TAC ``a:real < b`` THEN
    ASM_SIMP_TAC std_ss [REAL_ARITH ``~(a:real < b) ==> ~(a < x /\ x < b)``] THEN
    REWRITE_TAC[GSPEC_F, FINITE_EMPTY] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] SUBSET_FINITE)) THEN
    DISCH_THEN(MP_TAC o SPEC ``IMAGE (\n. a + (b - a) / (&n + &2:real)) univ(:num)``) THEN
    SIMP_TAC std_ss [SUBSET_DEF, FORALL_IN_IMAGE, IN_UNIV, GSPECIFICATION] THEN
    SIMP_TAC std_ss [REAL_LT_ADDR, REAL_ARITH ``a + x / y < b <=> x / y < b - a:real``] THEN
    KNOW_TAC ``!n. &0:real < &n + &2`` THENL [GEN_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC ``&n:real`` THEN RW_TAC std_ss [REAL_POS, REAL_LT_ADDR] THEN
    REAL_ARITH_TAC, ALL_TAC] THEN DISCH_TAC THEN
    ASM_SIMP_TAC std_ss [REAL_LT_DIV, REAL_SUB_LT, REAL_LT_LDIV_EQ, NOT_IMP] THEN
    REWRITE_TAC[REAL_ARITH ``x:real < x * (n + &2) <=> &0 < x * (n + &1)``] THEN
    KNOW_TAC ``!n. &0:real < &n + &1`` THENL [GEN_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC ``&n:real`` THEN RW_TAC std_ss [REAL_POS, REAL_LT_ADDR] THEN
    REAL_ARITH_TAC, ALL_TAC] THEN DISCH_TAC THEN
    ASM_SIMP_TAC std_ss [REAL_SUB_LT, REAL_LT_DIV, REAL_LT_RMUL_0] THEN
    MP_TAC num_INFINITE THEN MATCH_MP_TAC EQ_IMPLIES THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
    KNOW_TAC ``!n m a b. a < b:real ==> ((a + (b - a) / (&n + &2:real) =
                 a + (b - a) / (&m + &2)) <=> (&n:real = &m:real))`` THENL
    [REPEAT STRIP_TAC THEN SIMP_TAC std_ss [REAL_EQ_LADD, real_div, REAL_EQ_LMUL] THEN
    SIMP_TAC std_ss [REAL_INV_INJ, REAL_EQ_RADD] THEN
    METIS_TAC [REAL_SUB_0, REAL_LT_IMP_NE], ALL_TAC] THEN DISCH_TAC THEN
    ASM_SIMP_TAC std_ss [REAL_OF_NUM_EQ],
    (* goal 2 (of 2) *)
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC ``{x:real | a < x /\ x < a + &1}`` o
        MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO] SUBSET_FINITE)) THEN
    ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN REAL_ARITH_TAC,
    DISCH_THEN(MP_TAC o SPEC ``{x:real | a < x /\ x < a + &1}`` o
        MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO] SUBSET_FINITE)) THEN
    ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN REAL_ARITH_TAC,
    DISCH_THEN(MP_TAC o SPEC ``{x:real | b - &1 < x /\ x < b}`` o
        MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO] SUBSET_FINITE)) THEN
    ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN REAL_ARITH_TAC,
    DISCH_THEN(MP_TAC o SPEC ``{x:real | b - &1 < x /\ x < b}`` o
        MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO] SUBSET_FINITE)) THEN
    ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN REAL_ARITH_TAC,
    REWRITE_TAC[REAL_ARITH
     ``a:real <= x /\ x < b <=> (a < x /\ x < b) \/ ~(b <= a) /\ (x = a)``] THEN
     ASM_CASES_TAC ``b:real <= a`` THEN ASM_REWRITE_TAC[GSPEC_F, FINITE_EMPTY] THEN
     KNOW_TAC ``!x a b:real. {x | a < x /\ x < b \/ (x = a)} =
                  {x | a < x /\ x < b} UNION {x | x = a}`` THENL
     [SET_TAC [], ALL_TAC] THEN DISCH_TAC THEN CCONTR_TAC THEN
     UNDISCH_TAC ``~(b <= a:real)`` THEN FULL_SIMP_TAC std_ss [] THEN
     POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC [] THEN METIS_TAC [FINITE_UNION],
    REWRITE_TAC[REAL_ARITH
     ``a:real < x /\ x <= b <=> (a < x /\ x < b) \/ ~(b <= a) /\ (x = b)``] THEN
     ASM_CASES_TAC ``b:real <= a`` THEN ASM_REWRITE_TAC[GSPEC_F, FINITE_EMPTY] THEN
     KNOW_TAC ``!x a b:real. {x | a < x /\ x < b \/ (x = b)} =
                  {x | a < x /\ x < b} UNION {x | x = b}`` THENL
     [SET_TAC [], ALL_TAC] THEN DISCH_TAC THEN CCONTR_TAC THEN
     UNDISCH_TAC ``~(b <= a:real)`` THEN FULL_SIMP_TAC std_ss [] THEN
     POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC [] THEN METIS_TAC [FINITE_UNION],
    ASM_CASES_TAC ``b:real = a`` THEN
    ASM_SIMP_TAC std_ss [REAL_LE_ANTISYM, REAL_LE_REFL, GSPEC_EQ, GSPEC_EQ2, FINITE_SING] THEN
    ASM_SIMP_TAC std_ss [REAL_ARITH
     ``~(b:real = a) ==>
        (a <= x /\ x <= b <=> (a < x /\ x < b) \/ ~(b <= a) /\ (x = a) \/
        ~(b <= a) /\ (x = b))``] THEN
    ASM_REWRITE_TAC[FINITE_UNION, SET_RULE
     ``{x | p x \/ q x} = {x | p x} UNION {x | q x}``] THEN
    ASM_CASES_TAC ``b:real <= a`` THEN
    ASM_REWRITE_TAC[GSPEC_F, FINITE_EMPTY] THEN
    KNOW_TAC ``!x a b:real. {x | a < x /\ x < b \/ (x = a) \/ (x = b)} =
                  {x | a < x /\ x < b} UNION {x | (x = a) \/ (x = b)}`` THENL
    [SET_TAC [], ALL_TAC] THEN DISCH_TAC THEN CCONTR_TAC THEN
     UNDISCH_TAC ``~(b <= a:real)`` THEN FULL_SIMP_TAC std_ss [] THEN
     POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC [] THEN METIS_TAC [FINITE_UNION] ] ]);

val real_INFINITE = store_thm ("real_INFINITE",
 ``INFINITE univ(:real)``,
  DISCH_THEN(MP_TAC o SPEC ``{x:real | 0:real <= x}`` o
        MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO] SUBSET_FINITE)) THEN
  REWRITE_TAC[FINITE_REAL_INTERVAL, SUBSET_UNIV]);

(* ------------------------------------------------------------------------- *)
(* Choosing a smaller subset of a given size.                                *)
(* ------------------------------------------------------------------------- *)

val SET_PROVE_CASES = store_thm ("SET_PROVE_CASES",
 ``!P:('a->bool)->bool.
       P {} /\ (!a s. ~(a IN s) ==> P(a INSERT s))
       ==> !s. P s``,
  MESON_TAC[SET_CASES]);

val CHOOSE_SUBSET_STRONG = store_thm ("CHOOSE_SUBSET_STRONG",
 ``!n s:'a->bool.
        (FINITE s ==> n <= CARD s) ==> ?t. t SUBSET s /\ t HAS_SIZE n``,
  INDUCT_TAC THEN REWRITE_TAC[HAS_SIZE_0, HAS_SIZE_SUC] THENL
   [MESON_TAC[EMPTY_SUBSET], ALL_TAC] THEN
  ONCE_REWRITE_TAC [METIS [] ``((FINITE s ==> SUC n <= CARD s) ==>
   ?t. t SUBSET s /\ t <> {} /\ !a. a IN t ==> t DELETE a HAS_SIZE n) =
                           (\s. (FINITE s ==> SUC n <= CARD s) ==>
   ?t. t SUBSET s /\ t <> {} /\ !a. a IN t ==> t DELETE a HAS_SIZE n) s``] THEN
  MATCH_MP_TAC SET_PROVE_CASES THEN BETA_TAC THEN
  REWRITE_TAC[FINITE_EMPTY, CARD_EMPTY, CARD_INSERT, ARITH_PROVE ``~(SUC n <= 0)``] THEN
  MAP_EVERY X_GEN_TAC [``a:'a``, ``s:'a->bool``] THEN DISCH_TAC THEN
  ASM_SIMP_TAC std_ss [CARD_EMPTY, CARD_INSERT, FINITE_INSERT,
                       DECIDE “x <= SUC y <=> x <= y \/ x = SUC y”] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC ``s:'a->bool``) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN ``t:'a->bool`` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC ``(a:'a) INSERT t`` THEN
  REPEAT(CONJ_TAC THENL [ASM_SET_TAC[], ALL_TAC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ASM_SIMP_TAC std_ss [HAS_SIZE, CARD_DELETE, FINITE_INSERT, FINITE_DELETE,
               CARD_EMPTY, CARD_INSERT] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[SUC_SUB1] THEN
  ASM_SET_TAC[]);

val CHOOSE_SUBSET = store_thm ("CHOOSE_SUBSET",
 ``!s:'a->bool. FINITE s ==> !n. n <= CARD s ==> ?t. t SUBSET s /\ t HAS_SIZE n``,
  MESON_TAC[CHOOSE_SUBSET_STRONG]);

(* ------------------------------------------------------------------------- *)
(* REAL_COMPLETE                                                             *)
(* ------------------------------------------------------------------------- *)

val lemma1 = prove (
 ``!P s. (!x:real. P x ==> x <= s) = (!y:real. (?x. P x /\ y < x) ==> y < s)``,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC ``x:real``) THEN ASM_REWRITE_TAC [] THEN
   METIS_TAC [REAL_LTE_TRANS],
   ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [REAL_NOT_LE, REAL_NOT_LT] THEN
   POP_ASSUM MP_TAC THEN GEN_REWR_TAC LAND_CONV [REAL_LT_BETWEEN] THEN
   STRIP_TAC THEN EXISTS_TAC ``x':real`` THEN ASM_REWRITE_TAC [REAL_LE_LT] THEN
   EXISTS_TAC ``x:real`` THEN ASM_REWRITE_TAC []]);

val lemma2 = prove (
 ``!P s. (!M:real. (!x. P x ==> x <= M) ==> s <= M) = (!y. y < s ==> (?x. P x /\ y < x))``,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
   RW_TAC std_ss [REAL_NOT_LE, REAL_NOT_LT] THEN UNDISCH_TAC ``y < s:real`` THEN
   GEN_REWR_TAC LAND_CONV [REAL_LT_BETWEEN] THEN STRIP_TAC THEN
   EXISTS_TAC ``x:real`` THEN ASM_REWRITE_TAC [] THEN GEN_TAC THEN
   METIS_TAC [REAL_LE_TRANS, REAL_LE_LT],
   ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [REAL_NOT_LE, REAL_NOT_LT] THEN
   EXISTS_TAC ``M:real`` THEN METIS_TAC []]);

val lemma3 = prove (
 ``(?s:real. !y. (?x. P x /\ y < x) <=> y < s) =
   (?M:real. (!x. P x ==> x <= M) /\ (!M'. (!x. P x ==> x <= M') ==> M <= M'))``,
 SIMP_TAC std_ss [lemma1, lemma2] THEN METIS_TAC []);

val lemma4 = prove (
 ``!P:real->bool.
    ((?x. P x) /\ (?z. !x. P x ==> x < z) ==>
     (?s. !y. (?x. P x /\ y < x) <=> y < s)) ==>
    ((?x. P x) /\ (?s. !x. P x ==> x <= s)
       ==> ?s. (!x. P x ==> x <= s) /\
               !M'. (!x. P x ==> x <= M') ==> s <= M')``,
  REPEAT STRIP_TAC THEN REWRITE_TAC [GSYM lemma3] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
  [METIS_TAC [], ALL_TAC] THEN
  EXISTS_TAC ``s + 1:real`` THEN GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC ``x':real``) THEN
  ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC);

val REAL_COMPLETE = store_thm ("REAL_COMPLETE",
 ``!P:real->bool. (?x. P x) /\ (?M. !x. P x ==> x <= M)
       ==> ?M. (!x. P x ==> x <= M) /\
               !M'. (!x. P x ==> x <= M') ==> M <= M'``,
  GEN_TAC THEN MATCH_MP_TAC lemma4 THEN METIS_TAC [REAL_SUP_EXISTS]);

(* ------------------------------------------------------------------------- *)
(* Supremum and infimum.                                                     *)
(* ------------------------------------------------------------------------- *)

(* The original definition is in HOL Light's "sets.ml",
   HOL4's definition is in realTheory *)
val sup_alt = store_thm ("sup_alt",
  ``sup s = @a:real. (!x. x IN s ==> x <= a) /\
                     !b. (!x. x IN s ==> x <= b) ==> a <= b``,
  SIMP_TAC std_ss [sup] THEN AP_TERM_TAC THEN ABS_TAC THEN
  SIMP_TAC std_ss [SPECIFICATION, lemma1, lemma2, lemma3] THEN
  METIS_TAC []);

val SUP_EQ = store_thm ("SUP_EQ",
 ``!s t. (!b:real. (!x. x IN s ==> x <= b) <=> (!x. x IN t ==> x <= b))
         ==> (sup s = sup t)``,
  SIMP_TAC std_ss [sup_alt]);

Theorem SUP:
  !s:real->bool. s <> {} /\ (?b. !x. x IN s ==> x <= b) ==>
                 (!x. x IN s ==> x <= sup s) /\
                 !b. (!x. x IN s ==> x <= b) ==> sup s <= b
Proof
  rw[sup_alt, IN_DEF] >> SELECT_ELIM_TAC >> rw[] >>
  MATCH_MP_TAC REAL_COMPLETE >> metis_tac[MEMBER_NOT_EMPTY, IN_DEF]
QED

Theorem SUP_FINITE_LEMMA:
 !s:real->bool. FINITE s /\ ~(s = {}) ==>
                ?b:real. b IN s /\ !x. x IN s ==> x <= b
Proof
  Induct_on ‘FINITE’ >> dsimp[] >>
  METIS_TAC[REAL_LE_TOTAL, REAL_LE_TRANS, MEMBER_NOT_EMPTY]
QED

Theorem SUP_FINITE:
  !s. FINITE s /\ ~(s = {}) ==> (sup s) IN s /\ !x. x IN s ==> x <= sup s
Proof METIS_TAC [REAL_LE_ANTISYM, REAL_LE_TOTAL, SUP, SUP_FINITE_LEMMA]
QED

Theorem REAL_LE_SUP_FINITE:
  !s a:real. FINITE s /\ ~(s = {}) ==> (a <= sup s <=> ?x. x IN s /\ a <= x)
Proof METIS_TAC[SUP_FINITE, REAL_LE_TRANS]
QED

Theorem REAL_SUP_LE_FINITE:
  !s a:real. FINITE s /\ ~(s = {}) ==> (sup s <= a <=> !x. x IN s ==> x <= a)
Proof MESON_TAC[SUP_FINITE, REAL_LE_TRANS]
QED

Theorem REAL_LT_SUP_FINITE:
  !s a:real. FINITE s /\ ~(s = {}) ==> (a < sup s <=> ?x. x IN s /\ a < x)
Proof MESON_TAC[SUP_FINITE, REAL_LTE_TRANS]
QED

Theorem REAL_SUP_LT_FINITE:
  !s a:real. FINITE s /\ ~(s = {}) ==> (sup s < a <=> !x. x IN s ==> x < a)
Proof MESON_TAC[SUP_FINITE, REAL_LET_TRANS]
QED

Theorem SUP_UNIQUE_FINITE:
  !s. FINITE s /\ s <> {} ==> (sup s = a <=> a IN s /\ !y. y IN s ==> y <= a)
Proof
  simp[GSYM REAL_LE_ANTISYM, REAL_LE_SUP_FINITE, REAL_SUP_LE_FINITE] THEN
  MESON_TAC[REAL_LE_REFL, REAL_LE_TRANS, REAL_LE_ANTISYM]
QED

val REAL_SUP_LE_EQ = store_thm ("REAL_SUP_LE_EQ",
 ``!s y:real. ~(s = {}) /\ (?b. !x. x IN s ==> x <= b) ==>
           (sup s <= y <=> !x. x IN s ==> x <= y)``,
  METIS_TAC[SUP, REAL_LE_TRANS]);

val REAL_SUP_UNIQUE = store_thm ("REAL_SUP_UNIQUE",
 ``!s b:real. (!x. x IN s ==> x <= b) /\
         (!b'. b' < b ==> ?x. x IN s /\ b' < x)
         ==> (sup s = b)``,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sup_alt] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  ASM_MESON_TAC[REAL_NOT_LE, REAL_LE_ANTISYM]);

(* there's another REAL_SUP_LE in HOL's realTheory *)
Theorem REAL_SUP_LE' :
    !s b:real. ~(s = {}) /\ (!x. x IN s ==> x <= b) ==> sup s <= b
Proof
    METIS_TAC [SUP]
QED

val REAL_SUP_LE_SUBSET = store_thm ("REAL_SUP_LE_SUBSET",
 ``!s t:real->bool. ~(s = {}) /\ s SUBSET t /\ (?b. !x. x IN t ==> x <= b)
         ==> sup s <= sup t``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SUP_LE' THEN
  MP_TAC(SPEC ``t:real->bool`` SUP) THEN ASM_SET_TAC[]);

(* there's another REAL_LE_SUP in HOL's realTheory *)
Theorem REAL_LE_SUP' :
    !s a b y:real. y IN s /\ a <= y /\ (!x. x IN s ==> x <= b) ==> a <= sup s
Proof
    MESON_TAC [SUP, MEMBER_NOT_EMPTY, REAL_LE_TRANS]
QED

val REAL_SUP_BOUNDS = store_thm ("REAL_SUP_BOUNDS",
 ``!s a b:real. ~(s = {}) /\ (!x. x IN s ==> a <= x /\ x <= b)
           ==> a <= sup s /\ sup s <= b``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC ``s:real->bool`` SUP) THEN
  KNOW_TAC ``s <> {} /\ (?b. !x. x IN s ==> x <= b:real)`` THENL
   [METIS_TAC[], DISCH_TAC THEN ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC] THEN
  UNDISCH_TAC ``s <> {}:real->bool`` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE [GSYM MEMBER_NOT_EMPTY]) THEN
  METIS_TAC[REAL_LE_TRANS]);

val REAL_ABS_SUP_LE = store_thm ("REAL_ABS_SUP_LE",
 ``!s a:real. ~(s = {}) /\ (!x. x IN s ==> abs(x) <= a) ==> abs(sup s) <= a``,
  SIMP_TAC std_ss [ABS_BOUNDS] THEN METIS_TAC [REAL_SUP_BOUNDS]);

val REAL_SUP_ASCLOSE = store_thm ("REAL_SUP_ASCLOSE",
 ``!s l e:real. ~(s = {}) /\ (!x. x IN s ==> abs(x - l) <= e)
           ==> abs(sup s - l) <= e``,
  SIMP_TAC std_ss [REAL_ARITH ``abs(x - l):real <= e <=> l - e <= x /\ x <= l + e``] THEN
  METIS_TAC[REAL_SUP_BOUNDS]);

val SUP_INSERT_FINITE = store_thm ("SUP_INSERT_FINITE",
 ``!x s. FINITE s ==> (sup(x INSERT s) = if s = {} then x else max x (sup s))``,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC std_ss [SUP_UNIQUE_FINITE, FINITE_INSERT, FINITE_EMPTY,
                       NOT_INSERT_EMPTY, FORALL_IN_INSERT, NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_SING, REAL_LE_REFL] THEN REWRITE_TAC[max_def] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [SUP_FINITE, IN_INSERT, REAL_LE_REFL] THEN
  ASM_MESON_TAC[SUP_FINITE, REAL_LE_TOTAL, REAL_LE_TRANS]);

val SUP_SING = store_thm ("SUP_SING",
 ``!a. sup {a} = a``,
  SIMP_TAC std_ss [SUP_INSERT_FINITE, FINITE_EMPTY]);

val SUP_UNIQUE = store_thm ("SUP_UNIQUE",
 ``!s b:real. (!c. (!x. x IN s ==> x <= c) <=> b <= c) ==> (sup s = b)``,
  REPEAT STRIP_TAC THEN GEN_REWR_TAC RAND_CONV [GSYM SUP_SING] THEN
  MATCH_MP_TAC SUP_EQ THEN ASM_SET_TAC[]);

val SUP_UNION = store_thm ("SUP_UNION",
 ``!s t:real->bool. ~(s = {}) /\ ~(t = {}) /\ (?b. !x. x IN s ==> x <= b) /\
          (?c. !x. x IN t ==> x <= c) ==> (sup(s UNION t) = max (sup s) (sup t))``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUP_UNIQUE THEN
  SIMP_TAC real_ss [FORALL_IN_UNION, REAL_MAX_LE] THEN METIS_TAC[SUP, REAL_LE_TRANS]);

Theorem REAL_IMP_SUP_LE' :
    !p x. (?r. r IN p) /\ (!r. r IN p ==> r <= x) ==> sup p <= x
Proof
    REWRITE_TAC [IN_APP, REAL_IMP_SUP_LE]
QED

Theorem REAL_IMP_LE_SUP' :
    !p x. (?z. !r. r IN p ==> r <= z) /\ (?r. r IN p /\ x <= r) ==> x <= sup p
Proof
    REWRITE_TAC [IN_APP, REAL_IMP_LE_SUP]
QED

Theorem REAL_LE_SUP_EQ :
    !p x : real.
       (?y. y IN p) /\ (?y. !z. z IN p ==> z <= y) ==>
       (x <= sup p <=> !y. (!z. z IN p ==> z <= y) ==> x <= y)
Proof
    REWRITE_TAC [IN_APP, REAL_LE_SUP]
QED

(* This requires REAL_SUP_LE_EQ + REAL_LE_SUP_EQ *)
Theorem SUP_MONO :
    !p q. (?b. !n. p n <= b) /\ (?c. !n. q n <= c) /\
          (!n:num. p n <= q n) ==> sup (IMAGE p UNIV) <= sup (IMAGE q UNIV)
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘y = sup (IMAGE q UNIV)’
 >> Q.ABBREV_TAC ‘s = IMAGE p UNIV’
 >> Know ‘sup s <= y <=> !x. x IN s ==> x <= y’
 >- (MATCH_MP_TAC REAL_SUP_LE_EQ \\
     rw [Abbr ‘s’, Once EXTENSION] \\
     Q.EXISTS_TAC ‘b’ >> rw [] >> art [])
 >> Rewr'
 >> rw [Abbr ‘s’, IN_IMAGE]
 >> rename1 ‘p x <= y’
 >> Q.UNABBREV_TAC ‘y’
 >> Q.ABBREV_TAC ‘s = IMAGE q UNIV’
 >> Know ‘p x <= sup s <=> !y. (!z. z IN s ==> z <= y) ==> p x <= y’
 >- (MATCH_MP_TAC REAL_LE_SUP_EQ \\
     rw [Abbr ‘s’, IN_IMAGE] \\
     Q.EXISTS_TAC ‘c’ >> rw [] >> art [])
 >> Rewr'
 >> rw [Abbr ‘s’, IN_IMAGE]
 (* here it indicates that ‘!n. p n <= q n’ is too strong *)
 >> MATCH_MP_TAC REAL_LE_TRANS
 >> Q.EXISTS_TAC ‘q x’ >> art []
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘x’ >> rw []
QED

(* The original definition of "inf" in HOL Light (sets.ml) *)
val inf_tm = ``@a:real. (!x. x IN s ==> a <= x) /\
                        !b. (!x. x IN s ==> b <= x) ==> b <= a``;

(* `inf s` exists iff s is non-empty and has a lower bound b *)
val inf_criteria = ``s <> {} /\ (?b. !x. x IN s ==> b <= x)``;

(* alternative definition of `inf` *)
Theorem inf_alt :
    !s. ^inf_criteria ==> (inf s = ^inf_tm)
Proof
    RW_TAC std_ss []
 >> Suff `(\f. inf s = f) (^inf_tm)` >- METIS_TAC []
 >> MATCH_MP_TAC SELECT_ELIM_THM
 >> RW_TAC std_ss []
 >- (Q.EXISTS_TAC `inf s` >> CONJ_TAC
     >- (Know `(?y. s y) /\ (?y. !z. s z ==> y <= z)`
         >- (STRONG_CONJ_TAC >- METIS_TAC [MEMBER_NOT_EMPTY, IN_APP] \\
             STRIP_TAC >> `y IN s` by fs [IN_APP] >> RES_TAC \\
             Q.EXISTS_TAC `b` >> rpt STRIP_TAC \\
             FIRST_X_ASSUM MATCH_MP_TAC >> PROVE_TAC [IN_APP]) \\
         DISCH_THEN (MP_TAC o (MATCH_MP REAL_INF_LE)) >> Rewr \\
         Q.X_GEN_TAC `z` >> rpt STRIP_TAC \\
         FIRST_X_ASSUM MATCH_MP_TAC >> fs [IN_APP]) \\
     rpt STRIP_TAC >> MATCH_MP_TAC REAL_IMP_LE_INF \\
     CONJ_TAC >- METIS_TAC [MEMBER_NOT_EMPTY, IN_APP] \\
     fs [IN_APP])
 >> RW_TAC std_ss [GSYM REAL_LE_ANTISYM]
 >- (Know `(?y. s y) /\ (?y. !z. s z ==> y <= z)`
     >- (STRONG_CONJ_TAC >- METIS_TAC [MEMBER_NOT_EMPTY, IN_APP] \\
         STRIP_TAC >> `y IN s` by fs [IN_APP] >> RES_TAC \\
         Q.EXISTS_TAC `b` >> rpt STRIP_TAC \\
         FIRST_X_ASSUM MATCH_MP_TAC >> PROVE_TAC [IN_APP]) \\
     DISCH_THEN (MP_TAC o (MATCH_MP REAL_INF_LE)) >> Rewr \\
     rpt STRIP_TAC \\
     Q.PAT_X_ASSUM `!b. (!x. x IN s ==> b <= x) ==> b <= x`
       MATCH_MP_TAC >> fs [IN_APP])
 >> MATCH_MP_TAC REAL_IMP_LE_INF
 >> CONJ_TAC >- METIS_TAC [MEMBER_NOT_EMPTY, IN_APP]
 >> fs [IN_APP]
QED

(* added `s <> EMPTY /\ (?b. !x. x IN s ==> b <= x) /\
          t <> EMPTY /\ (?b. !x. x IN t ==> b <= x)`
   to make sure that both `inf s` and `inf t` exist. *)
Theorem INF_EQ :
    !s t:real->bool. s <> EMPTY /\ (?b. !x. x IN s ==> b <= x) /\
                     t <> EMPTY /\ (?b. !x. x IN t ==> b <= x) /\
                    (!a. (!x. x IN s ==> a <= x) <=> (!x. x IN t ==> a <= x))
                ==> (inf s = inf t)
Proof
    rpt STRIP_TAC
 >> Know `(inf s = ^inf_tm) /\
          (inf t = @a:real. (!x. x IN t ==> a <= x) /\
                        !b. (!x. x IN t ==> b <= x) ==> b <= a)`
 >- (CONJ_TAC >> MATCH_MP_TAC inf_alt >> PROVE_TAC [])
 >> ASM_SIMP_TAC std_ss []
QED

val INF = store_thm ("INF",
 ``!s:real->bool. ~(s = {}) /\ (?b. !x. x IN s ==> b <= x)
       ==> (!x. x IN s ==> inf s <= x) /\
           !b. (!x. x IN s ==> b <= x) ==> b <= inf s``,
  GEN_TAC THEN STRIP_TAC THEN
  Know `inf s = ^inf_tm` >- (MATCH_MP_TAC inf_alt >> PROVE_TAC []) >> Rewr'
  THEN CONV_TAC(ONCE_DEPTH_CONV SELECT_CONV) THEN
  ONCE_REWRITE_TAC[GSYM REAL_LE_NEG2] THEN
  EXISTS_TAC ``-(sup (IMAGE (\x:real. -x) s))`` THEN
  MP_TAC(SPEC ``IMAGE (\x. -x) (s:real->bool)`` SUP) THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN
  ABBREV_TAC ``a = sup (IMAGE (\x:real. -x) s)`` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY, IN_IMAGE] THEN
  ASM_MESON_TAC[REAL_NEG_NEG, MEMBER_NOT_EMPTY, REAL_LE_NEG2]);

val INF_FINITE_LEMMA = store_thm ("INF_FINITE_LEMMA",
 ``!s. FINITE s /\ ~(s = {}) ==> ?b:real. b IN s /\ !x. x IN s ==> b <= x``,
  REWRITE_TAC[CONJ_EQ_IMP] THEN
  ONCE_REWRITE_TAC [METIS [] ``(s <> {} ==> ?b. b IN s /\ !x. x IN s ==> b <= x) =
                (\s:real->bool. s <> {} ==> ?b. b IN s /\ !x. x IN s ==> b <= x) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  REWRITE_TAC[NOT_INSERT_EMPTY, IN_INSERT] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  METIS_TAC[REAL_LE_TOTAL, REAL_LE_TRANS]);

val INF_FINITE = store_thm ("INF_FINITE",
 ``!s. FINITE s /\ ~(s = {}) ==> (inf s) IN s /\ !x. x IN s ==> inf s <= x``,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INF_FINITE_LEMMA) THEN
  ASM_MESON_TAC[REAL_LE_ANTISYM, REAL_LE_TOTAL, INF]);

val REAL_LE_INF_FINITE = store_thm ("REAL_LE_INF_FINITE",
 ``!s a:real. FINITE s /\ ~(s = {}) ==> (a <= inf s <=> !x. x IN s ==> a <= x)``,
  METIS_TAC[INF_FINITE, REAL_LE_TRANS]);

val REAL_INF_LE_FINITE = store_thm ("REAL_INF_LE_FINITE",
 ``!s a:real. FINITE s /\ ~(s = {}) ==> (inf s <= a <=> ?x. x IN s /\ x <= a)``,
  MESON_TAC[INF_FINITE, REAL_LE_TRANS]);

val REAL_LT_INF_FINITE = store_thm ("REAL_LT_INF_FINITE",
 ``!s a:real. FINITE s /\ ~(s = {}) ==> (a < inf s <=> !x. x IN s ==> a < x)``,
  METIS_TAC[INF_FINITE, REAL_LTE_TRANS]);

val REAL_INF_LT_FINITE = store_thm ("REAL_INF_LT_FINITE",
 ``!s a:real. FINITE s /\ ~(s = {}) ==> (inf s < a <=> ?x. x IN s /\ x < a)``,
  METIS_TAC[INF_FINITE, REAL_LET_TRANS]);

val REAL_INF_UNIQUE = store_thm ("REAL_INF_UNIQUE",
 ``!s b:real. (!x. x IN s ==> b <= x) /\
         (!b'. b < b' ==> ?x. x IN s /\ x < b')
         ==> (inf s = b)``,
  rpt STRIP_TAC THEN
  Know `s <> EMPTY`
  >- (REWRITE_TAC [GSYM MEMBER_NOT_EMPTY] \\
      POP_ASSUM (MP_TAC o (Q.SPEC `b + 1`)) \\
      RW_TAC real_ss [REAL_LT_ADDR, REAL_LT_01] \\
      Q.EXISTS_TAC `x` >> ASM_REWRITE_TAC []) >> DISCH_TAC \\
  Know `inf s = ^inf_tm`
  >- (MATCH_MP_TAC inf_alt >> PROVE_TAC []) >> Rewr' \\
  MATCH_MP_TAC SELECT_UNIQUE THEN
  METIS_TAC[REAL_NOT_LE, REAL_LE_ANTISYM]);

val REAL_LE_INF = store_thm ("REAL_LE_INF",
 ``!s b:real. ~(s = {}) /\ (!x. x IN s ==> b <= x) ==> b <= inf s``,
  MESON_TAC[INF]);

val REAL_LE_INF_SUBSET = store_thm ("REAL_LE_INF_SUBSET",
 ``!s t:real->bool. ~(t = {}) /\ t SUBSET s /\ (?b. !x. x IN s ==> b <= x)
         ==> inf s <= inf t``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_INF THEN
  MP_TAC(SPEC ``s:real->bool`` INF) THEN ASM_SET_TAC[]);

Theorem REAL_INF_LE' :
    !p x:real. (?y. y IN p) /\ (?y. !z. z IN p ==> y <= z) ==>
               (inf p <= x <=> !y. (!z. z IN p ==> y <= z) ==> y <= x)
Proof
    REWRITE_TAC [IN_APP, REAL_INF_LE]
QED

val REAL_INF_BOUNDS = store_thm ("REAL_INF_BOUNDS",
 ``!s a b:real. ~(s = {}) /\ (!x. x IN s ==> a <= x /\ x <= b)
           ==> a <= inf s /\ inf s <= b``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC ``s:real->bool`` INF) THEN
  KNOW_TAC ``s <> {} /\ (?b:real. !x. x IN s ==> b <= x)`` THENL
   [ASM_MESON_TAC[], DISCH_TAC THEN ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC] THEN
  UNDISCH_TAC ``s <> {}:real->bool`` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE [GSYM MEMBER_NOT_EMPTY]) THEN
  METIS_TAC[REAL_LE_TRANS]);

val REAL_ABS_INF_LE = store_thm ("REAL_ABS_INF_LE",
 ``!s a:real. ~(s = {}) /\ (!x. x IN s ==> abs(x) <= a) ==> abs(inf s) <= a``,
  REWRITE_TAC[ABS_BOUNDS] THEN METIS_TAC  [REAL_INF_BOUNDS]);

val REAL_INF_ASCLOSE = store_thm ("REAL_INF_ASCLOSE",
 ``!s l e:real. ~(s = {}) /\ (!x. x IN s ==> abs(x - l) <= e)
           ==> abs(inf s - l) <= e``,
  SIMP_TAC std_ss [REAL_ARITH ``abs(x - l):real <= e <=> l - e <= x /\ x <= l + e``] THEN
  METIS_TAC[REAL_INF_BOUNDS]);

val SUP_UNIQUE_FINITE = store_thm ("SUP_UNIQUE_FINITE",
 ``!s:real->bool a. FINITE s /\ ~(s = {})
       ==> ((sup s = a) <=> a IN s /\ !y. y IN s ==> y <= a)``,
   ASM_SIMP_TAC std_ss [GSYM REAL_LE_ANTISYM, REAL_LE_SUP_FINITE, REAL_SUP_LE_FINITE,
               NOT_INSERT_EMPTY, FINITE_INSERT, FINITE_EMPTY] THEN
   METIS_TAC[REAL_LE_REFL, REAL_LE_TRANS, REAL_LE_ANTISYM]);

val INF_UNIQUE_FINITE = store_thm ("INF_UNIQUE_FINITE",
 ``!s a. FINITE s /\ ~(s = {})
       ==> ((inf s = a) <=> a IN s /\ !y. y IN s ==> a <= y)``,
   ASM_SIMP_TAC std_ss [GSYM REAL_LE_ANTISYM, REAL_LE_INF_FINITE, REAL_INF_LE_FINITE,
               NOT_INSERT_EMPTY, FINITE_INSERT, FINITE_EMPTY] THEN
   MESON_TAC[REAL_LE_REFL, REAL_LE_TRANS, REAL_LE_ANTISYM]);

val SUP_INSERT_FINITE = store_thm ("SUP_INSERT_FINITE",
 ``!x:real s. FINITE s ==> (sup(x INSERT s) = if s = {} then x else max x (sup s))``,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC std_ss [SUP_UNIQUE_FINITE,  FINITE_INSERT, FINITE_EMPTY,
               NOT_INSERT_EMPTY, FORALL_IN_INSERT, NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_SING, REAL_LE_REFL] THEN
  REWRITE_TAC[max_def] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC std_ss [SUP_FINITE, IN_INSERT, REAL_LE_REFL] THEN
  METIS_TAC[SUP_FINITE, REAL_LE_TOTAL, REAL_LE_TRANS]);

val INF_INSERT_FINITE = store_thm ("INF_INSERT_FINITE",
 ``!x s:real->bool. FINITE s ==> (inf(x INSERT s) = if s = {} then x else min x (inf s))``,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC std_ss [INF_UNIQUE_FINITE, FINITE_INSERT, FINITE_EMPTY,
               NOT_INSERT_EMPTY, FORALL_IN_INSERT, NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_SING, REAL_LE_REFL] THEN
  REWRITE_TAC[min_def] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC std_ss [INF_FINITE, IN_INSERT, REAL_LE_REFL] THEN
  ASM_MESON_TAC[INF_FINITE, REAL_LE_TOTAL, REAL_LE_TRANS]);

val REAL_SUP_EQ_INF = store_thm ("REAL_SUP_EQ_INF",
 ``!s:real->bool. ~(s = {}) /\ (?B. !x. x IN s ==> abs(x) <= B)
       ==> ((sup s = inf s) <=> ?a. s = {a})``,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC ``sup (s:real->bool)`` THEN MATCH_MP_TAC
     (SET_RULE ``~(s = {}) /\ (!x. x IN s ==> (x = a)) ==> (s = {a})``) THEN
    ASM_REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
    ASM_MESON_TAC[SUP, ABS_BOUNDS, INF],
    STRIP_TAC THEN
    ASM_SIMP_TAC std_ss [SUP_INSERT_FINITE, INF_INSERT_FINITE, FINITE_EMPTY]]);

val INF_SING = store_thm ("INF_SING",
 ``!a. inf {a} = a``,
  SIMP_TAC std_ss [INF_INSERT_FINITE, FINITE_EMPTY]);

(* ------------------------------------------------------------------------- *)
(* A natural notation for segments of the naturals.                          *)
(* ------------------------------------------------------------------------- *)

Definition numseg:
  numseg m n = {x:num | m <= x /\ x <= n}
End

(* syntax is similar to the version also available for lists, where
   listRangeTheory has  [ m .. n ]
 *)

val _ = add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                   fixity = Closefix,
                   paren_style = OnlyIfNecessary,
                   pp_elements = [TOK "{", TM, HardSpace 1, TOK "..",
                                  BreakSpace(1,1), TM, BreakSpace(0,0),
                                  TOK "}"],
                   term_name = "numseg" }

Theorem IN_NUMSEG[simp]:
  x IN {m .. n} <=> m <= x /\ x <= n
Proof
  simp[numseg]
QED

Theorem FINITE_NUMSEG:
  !m n. FINITE {m..n}
Proof
  rw[numseg] >> irule FINITE_SUBSET >> irule_at Any FINITE_COUNT >>
  qexists_tac ‘n + 1’ >> simp[SUBSET_DEF]
QED

Theorem NUMSEG_COMBINE_R:
   !m p n. m <= p + 1 /\ p <= n ==> {m..p} UNION {p+1..n} = {m..n}
Proof
  simp[EXTENSION]
QED

Theorem NUMSEG_COMBINE_L:
  !m p n. m <= p /\ p <= n + 1 ==> {m..p-1} UNION {p..n} = {m..n}
Proof
  simp[EXTENSION]
QED

Theorem NUMSEG_LREC:
  !m n. m <= n ==> m INSERT {m+1..n} = {m..n}
Proof
  simp[EXTENSION]
QED

Theorem NUMSEG_RREC:
  !m n. m <= n ==> n INSERT {m..n-1} = {m..n}
Proof
  simp[EXTENSION]
QED

Theorem NUMSEG_REC:
  !m n. m <= SUC n ==> {m..SUC n} = SUC n INSERT {m..n}
Proof SIMP_TAC std_ss [GSYM NUMSEG_RREC, SUC_SUB1]
QED

Theorem IN_NUMSEG_0:
   !m n. m IN {0..n} <=> m <= n
Proof simp[]
QED

Theorem NUMSEG_SING: !n. {n..n} = {n}
Proof simp[EXTENSION]
QED

Theorem NUMSEG_EMPTY:
  !m n. {m..n} = {} <=> n < m
Proof
  simp[EXTENSION] >> MESON_TAC[NOT_LESS_EQUAL, LESS_EQ_TRANS, LESS_EQ_REFL]
QED

Theorem CARD_NUMSEG_LEMMA:
  !m d. CARD{m..m+d} = d + 1
Proof
  GEN_TAC THEN INDUCT_TAC THEN
  gs[NUMSEG_SING, ADD_CLAUSES, NUMSEG_REC, FINITE_NUMSEG]
QED

Theorem CARD_NUMSEG:
  !m n. CARD {m..n} = n + 1 - m
Proof
  REPEAT GEN_TAC >> Cases_on ‘m <= n’
  >- gs[LESS_EQ_EXISTS, CARD_NUMSEG_LEMMA] >>
  gs[NOT_LESS_EQUAL] >> drule_then assume_tac (iffRL NUMSEG_EMPTY) >>
  simp[]
QED

val HAS_SIZE_NUMSEG = store_thm ("HAS_SIZE_NUMSEG",
 “!m n. {m..n} HAS_SIZE ((n + 1:num) - m)”,
  REWRITE_TAC[HAS_SIZE, FINITE_NUMSEG, CARD_NUMSEG]);

Theorem CARD_NUMSEG_1:
 !n. CARD{1..n} = n
Proof
  simp[CARD_NUMSEG]
QED

val HAS_SIZE_NUMSEG_1 = store_thm ("HAS_SIZE_NUMSEG_1",
 “!n. {1..n} HAS_SIZE n”,
  REWRITE_TAC[CARD_NUMSEG, HAS_SIZE, FINITE_NUMSEG] THEN ARITH_TAC);

Theorem NUMSEG_CLAUSES:
  (!m. {m..0} = if m = 0 then {0} else {}) /\
  !m n. {m..SUC n} = if m <= SUC n then SUC n INSERT {m..n} else {m..n}
Proof
  rw[] >> simp[NUMSEG_EMPTY, NUMSEG_SING, NUMSEG_REC] >> simp[EXTENSION]
QED

Theorem FINITE_INDEX_NUMSEG:
  !s:'a->bool.
    FINITE s =
    ?f. (!i j. i IN {1..CARD s} /\ j IN {1..CARD s} /\ f i = f j ==> i = j) /\
        s = IMAGE f {1..CARD s}
Proof
  GEN_TAC >> reverse EQ_TAC >- MESON_TAC[FINITE_NUMSEG, IMAGE_FINITE] >>
  qid_spec_tac ‘s’ >> Induct_on ‘FINITE’ >> rw[NUMSEG_EMPTY] >>
  rename [‘e NOTIN s’, ‘s = IMAGE f _’] >> qabbrev_tac ‘C = CARD s’ >>
  qexists_tac ‘f (| SUC C |-> e |)’ >> simp[combinTheory.APPLY_UPDATE_THM] >>
  reverse conj_tac
  >- (simp[EXTENSION, combinTheory.APPLY_UPDATE_THM, AllCaseEqs(), SF DNF_ss] >>
      metis_tac[LE, DECIDE “x <= y ==> x <> SUC y”]) >>
  rpt gen_tac >> simp[AllCaseEqs()] >>
  ‘!i. 1 <= i /\ i <= C ==> f i <> e’ by (gvs[] >> metis_tac[]) >>
  simp[LE] >> rpt strip_tac >> metis_tac[]
QED

val FINITE_INDEX_NUMBERS = store_thm ("FINITE_INDEX_NUMBERS",
 “!s:'a->bool.
        FINITE s =
         ?k:num->bool f. (!i j. i IN k /\ j IN k /\ (f i = f j) ==> (i = j)) /\
                         FINITE k /\ (s = IMAGE f k)”,
  MESON_TAC[FINITE_INDEX_NUMSEG, FINITE_NUMSEG, IMAGE_FINITE]);

Theorem DISJOINT_NUMSEG:
  !m n p q. DISJOINT {m..n} {p..q} <=> n < p \/ q < m \/ n < m \/ q < p
Proof
 simp[DISJOINT_DEF, EXTENSION, NOT_LESS_EQUAL] >> rpt gen_tac >> eq_tac >>
 simp[] >> MESON_TAC[LESS_ANTISYM]
QED

Theorem NUMSEG_ADD_SPLIT:
  !m n p. m <= n + 1 ==> {m..n+p} = {m..n} UNION {n+1..n+p}
Proof
  REWRITE_TAC[EXTENSION, IN_UNION, IN_NUMSEG] THEN ARITH_TAC
QED

Theorem NUMSEG_OFFSET_IMAGE:
  !m n p. {m+p..n+p} = IMAGE (\i. i + p) {m..n}
Proof
  simp[EXTENSION, EQ_IMP_THM] >> rpt strip_tac >> rename [‘m + p <= x’] >>
  qexists_tac ‘x - p’ >> simp[]
QED

Theorem SUBSET_NUMSEG:
  !m n p q. {m..n} SUBSET {p..q} <=> n < m \/ p <= m /\ n <= q
Proof
  simp[SUBSET_DEF, EQ_IMP_THM] >>
  MESON_TAC[LESS_EQ_TRANS, NOT_LESS_EQUAL, LESS_EQ_REFL]
QED

(* ------------------------------------------------------------------------- *)
(* Equivalence with the more ad-hoc comprehension notation.                  *)
(* ------------------------------------------------------------------------- *)

Theorem NUMSEG_LE:
  !n. {x | x <= n} = {0..n}
Proof
  simp[EXTENSION]
QED

Theorem NUMSEG_LT:
  !n. {x | x < n} = if n = 0 then {} else {0..n-1}
Proof
  rw[EXTENSION]
QED

(* ------------------------------------------------------------------------- *)
(* Segment of natural numbers starting at a specific number.                 *)
(* ------------------------------------------------------------------------- *)

val from_def = Define
   `from n = {m:num | n <= m}`;

val FROM_0 = store_thm ("FROM_0",
  ``from 0 = univ(:num)``,
    REWRITE_TAC [from_def, ZERO_LESS_EQ, GSPEC_T]);

val IN_FROM = store_thm ("IN_FROM",
  ``!m n. m IN from n <=> n <= m``,
    SIMP_TAC std_ss [from_def, GSPECIFICATION]);

val DISJOINT_COUNT_FROM = store_thm
  ("DISJOINT_COUNT_FROM", ``!n. DISJOINT (count n) (from n)``,
    RW_TAC arith_ss [from_def, count_def, DISJOINT_DEF, Once EXTENSION, NOT_IN_EMPTY,
                     GSPECIFICATION, IN_INTER]);

val DISJOINT_FROM_COUNT = store_thm
  ("DISJOINT_FROM_COUNT", ``!n. DISJOINT (from n) (count n)``,
    RW_TAC std_ss [Once DISJOINT_SYM, DISJOINT_COUNT_FROM]);

val UNION_COUNT_FROM = store_thm
  ("UNION_COUNT_FROM", ``!n. (count n) UNION (from n) = UNIV``,
    RW_TAC arith_ss [from_def, count_def, Once EXTENSION, NOT_IN_EMPTY,
                     GSPECIFICATION, IN_UNION, IN_UNIV]);

val UNION_FROM_COUNT = store_thm
  ("UNION_FROM_COUNT", ``!n. (from n) UNION (count n) = UNIV``,
    RW_TAC std_ss [Once UNION_COMM, UNION_COUNT_FROM]);

Theorem FROM_NOT_EMPTY :
    !n. from n <> {}
Proof
    RW_TAC std_ss [GSYM MEMBER_NOT_EMPTY, from_def, GSPECIFICATION]
 >> Q.EXISTS_TAC `n` >> REWRITE_TAC [LESS_EQ_REFL]
QED

Theorem COUNTABLE_FROM :
    !n. COUNTABLE (from n)
Proof
    PROVE_TAC [COUNTABLE_NUM]
QED

val FROM_INTER_NUMSEG_GEN = store_thm ("FROM_INTER_NUMSEG_GEN",
 ``!k m n. (from k) INTER {m..n} = if m < k then {k..n} else {m..n}``,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  SIMP_TAC std_ss [from_def, GSPECIFICATION, IN_INTER, IN_NUMSEG, EXTENSION] THEN
  ARITH_TAC);

val FROM_INTER_NUMSEG_MAX = store_thm ("FROM_INTER_NUMSEG_MAX",
 ``!m n p. from p INTER {m..n} = {MAX p m..n}``,
  SIMP_TAC arith_ss [EXTENSION, IN_INTER, IN_NUMSEG, IN_FROM] THEN ARITH_TAC);

val FROM_INTER_NUMSEG = store_thm ("FROM_INTER_NUMSEG",
 ``!k n. (from k) INTER {0..n} = {k..n}``,
  SIMP_TAC std_ss [from_def, GSPECIFICATION, IN_INTER, IN_NUMSEG, EXTENSION] THEN
  ARITH_TAC);

val INFINITE_FROM = store_thm ("INFINITE_FROM",
  ``!n. INFINITE(from n)``,
   GEN_TAC THEN KNOW_TAC ``from n = univ(:num) DIFF {i | i < n}`` THENL
  [SIMP_TAC std_ss [EXTENSION, from_def, IN_DIFF, IN_UNIV, GSPECIFICATION] THEN
   ARITH_TAC, DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC INFINITE_DIFF_FINITE THEN
   REWRITE_TAC [FINITE_NUMSEG_LT, num_INFINITE]]);

(* ------------------------------------------------------------------------- *)
(* Topological sorting of a finite set.                                      *)
(* ------------------------------------------------------------------------- *)

val _ = temp_set_fixity "<<" (Infix(NONASSOC, 450))

val TOPOLOGICAL_SORT = store_thm ("TOPOLOGICAL_SORT",
 ``!(<<). (!x y:'a. x << y /\ y << x ==> (x = y)) /\
          (!x y z. x << y /\ y << z ==> x << z)
          ==> !n s. s HAS_SIZE n
                    ==> ?f. (s = IMAGE f {1..n}) /\
                            (!j k. j IN {1..n} /\ k IN {1..n} /\ j < k
                                   ==> ~(f k << f j))``,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN ``!n s. s HAS_SIZE n /\ ~(s = {})
                      ==> ?a:'a. a IN s /\ !b. b IN (s DELETE a) ==> ~(b << a)``
  ASSUME_TAC THENL
   [INDUCT_TAC THEN
    REWRITE_TAC[HAS_SIZE_0, HAS_SIZE_SUC, TAUT `~(a /\ ~a)`] THEN
    X_GEN_TAC ``s:'a->bool`` THEN STRIP_TAC THEN
    UNDISCH_TAC ``(s:'a->bool) <> {}`` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC ``a:'a``) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC ``a:'a``) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC ``s DELETE (a:'a)``) THEN
    ASM_SIMP_TAC std_ss [SET_RULE ``a IN s ==> ((s DELETE a = {}) <=> (s = {a}))``] THEN
    ASM_CASES_TAC ``s = {a:'a}`` THEN ASM_SIMP_TAC std_ss [] THENL
     [EXISTS_TAC ``a:'a`` THEN SET_TAC[], ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN ``b:'a`` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC ``((a:'a) << (b:'a)) :bool`` THENL
     [EXISTS_TAC ``a:'a``, EXISTS_TAC ``b:'a``] THEN ASM_SET_TAC[],
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [SIMP_TAC arith_ss [HAS_SIZE_0, NUMSEG_CLAUSES, IMAGE_EMPTY, IMAGE_INSERT, NOT_IN_EMPTY],
    ALL_TAC] THEN
  REWRITE_TAC[HAS_SIZE_SUC] THEN X_GEN_TAC ``s:'a->bool`` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [``SUC n``, ``s:'a->bool``]) THEN
  ASM_REWRITE_TAC[HAS_SIZE_SUC] THEN
  DISCH_THEN(X_CHOOSE_THEN ``a:'a`` MP_TAC) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC ``s DELETE (a:'a)``) THEN ASM_SIMP_TAC std_ss [] THEN
  DISCH_THEN(X_CHOOSE_THEN ``f:num->'a`` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC ``\k. if k = 1n then a:'a else f(k - 1)`` THEN
  SIMP_TAC std_ss [ARITH_PROVE ``1 <= k ==> ~(SUC k = 1)``, SUC_SUB1] THEN
  SUBGOAL_THEN ``!i. i IN {1..SUC n} <=> i = 1 \/ 1 < i /\ i - 1 IN {1..n}``
   (fn th => REWRITE_TAC[EXTENSION, IN_IMAGE, th])
  THENL [REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC, ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC ``b:'a`` THEN ASM_CASES_TAC ``b:'a = a`` THENL
     [METIS_TAC[], ALL_TAC] THEN
    FIRST_ASSUM(fn th => ONCE_REWRITE_TAC[MATCH_MP
     (SET_RULE ``~(b = a) ==> (b IN s <=> b IN (s DELETE a))``) th]) THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    ASM_REWRITE_TAC[IN_IMAGE, IN_NUMSEG] THEN
    EQ_TAC THENL [ALL_TAC, METIS_TAC[]] THEN
    DISCH_THEN(X_CHOOSE_TAC ``i:num``) THEN EXISTS_TAC ``i + 1:num`` THEN
    ASM_SIMP_TAC arith_ss [ARITH_PROVE ``1 <= x ==> 1 < x + 1 /\ ~(x + 1 = 1:num)``, ADD_SUB],
    MAP_EVERY X_GEN_TAC [``j:num``, ``k:num``] THEN
    MAP_EVERY ASM_CASES_TAC [``j = 1:num``, ``k = 1:num``] THEN
    ASM_REWRITE_TAC[LESS_REFL] THENL
     [STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SET_TAC[],
      ARITH_TAC,
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC arith_ss []]]);

(* Another form using relationTheory and (count n), added by Chun Tian

   NOTE: the set sorting is slightly different with list sorting, as there are
   no duplicated elements in sets, thus the sorting result (given by an index
   function) has strict orders for each pair of elements.

   Also, the sorting requirements is slightly different: list sorting requires
  ‘transitive’ and ‘total’ (cf. sortingTheory.QSORT_SORTED), while set sorting
   here requires ‘transitive’ and ‘antisymmetric’. (‘~R x y’ also means that
   x and y are incomparable, i.e. some part of ‘f’ is an "antichain".)
 *)
Theorem TOPOLOGICAL_SORT' :
    !R s n. transitive R /\ antisymmetric R /\ s HAS_SIZE n ==>
            ?f. s = IMAGE f (count n) /\
                !j k. j < n /\ k < n /\ j < k ==> ~(R (f k) (f j))
Proof
    RW_TAC std_ss []
 >> MP_TAC (REWRITE_RULE [GSYM transitive_def, GSYM antisymmetric_def]
                         (Q.SPEC ‘R’ TOPOLOGICAL_SORT))
 >> RW_TAC std_ss []
 >> POP_ASSUM (MP_TAC o (Q.SPECL [‘n’, ‘s’]))
 >> RW_TAC std_ss [IN_NUMSEG]
 >> Q.EXISTS_TAC ‘f o SUC’
 >> CONJ_TAC
 >- (rw [Once EXTENSION, IN_IMAGE, IN_COUNT, IN_NUMSEG] \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       rename1 ‘i <= n’ >> Q.EXISTS_TAC ‘PRE i’ >> rw [] \\
       Suff ‘SUC (PRE i) = i’ >- Rewr \\
       rw [GSYM SUC_PRE],
       (* goal 2 (of 2) *)
       rename1 ‘i < n’ >> Q.EXISTS_TAC ‘SUC i’ >> rw [] ])
 >> RW_TAC arith_ss []
QED

(* ------------------------------------------------------------------------- *)
(* Generic iteration of operation over set with finite support.              *)
(* ------------------------------------------------------------------------- *)

val neutral = new_definition ("neutral",
  ``neutral op = @x. !y. (op x y = y) /\ (op y x = y)``);

(* NOTE: The set of all numbers of the involved type, ‘op’ and ‘neutral op’
   actually form an Abelian Monoid (also called Commutative Monoid), i.e.

   |- monoidal op <=>
      AbelianMonoid <| carrier = UNIV, op = op, id = (neutral op) |>

   (see also AbelianMonoid_def in examples/algebra/monoid/monoidScript.sml)
 *)
val monoidal = new_definition ("monoidal",
  ``monoidal op <=> (!x y. op x y = op y x) /\
                    (!x y z. op x (op y z) = op (op x y) z) /\
                    (!x:'a. op (neutral op) x = x)``);

val MONOIDAL_AC = store_thm("MONOIDAL_AC",
  ``!op. monoidal op
         ==> (!a. op (neutral op) a = a) /\
             (!a. op a (neutral op) = a) /\
             (!a b. op a b = op b a) /\
             (!a b c. op (op a b) c = op a (op b c)) /\
             (!a b c. op a (op b c) = op b (op a c))``,
  REWRITE_TAC[monoidal] THEN MESON_TAC[]);

val support = new_definition ("support",
  ``support op (f:'a->'b) s = {x | x IN s /\ ~(f x = neutral op)}``);

val iterate = new_definition ("iterate",
  ``iterate op (s:'a->bool) f =
         if FINITE(support op f s)
         then ITSET (\x a. op (f x) a) (support op f s) (neutral op)
         else neutral op``);

val IN_SUPPORT = store_thm  ("IN_SUPPORT",
  ``!op f x s. x IN (support op f s) <=> x IN s /\ ~(f x = neutral op)``,
   SIMP_TAC std_ss [support, GSPECIFICATION]);

val SUPPORT_SUPPORT = store_thm ("SUPPORT_SUPPORT",
  ``!op f s. support op f (support op f s) = support op f s``,
  SIMP_TAC std_ss [support, GSPECIFICATION, EXTENSION]);

val SUPPORT_EMPTY = store_thm ("SUPPORT_EMPTY",
  ``!op f s. (!x. x IN s ==> (f(x) = neutral op)) <=> (support op f s = {})``,
   SIMP_TAC std_ss [IN_SUPPORT, EXTENSION, GSPECIFICATION, NOT_IN_EMPTY] THEN
   MESON_TAC[]);

val SUPPORT_SUBSET = store_thm ("SUPPORT_SUBSET",
  ``!op f s. (support op f s) SUBSET s``,
  SIMP_TAC std_ss [SUBSET_DEF, IN_SUPPORT]);

val FINITE_SUPPORT = store_thm ("FINITE_SUPPORT",
  ``!op f s. FINITE s ==> FINITE(support op f s)``,
  MESON_TAC[SUPPORT_SUBSET, SUBSET_FINITE]);

val SUPPORT_CLAUSES = store_thm ("SUPPORT_CLAUSES",
 ``(!f. support op f {} = {}) /\
   (!f x s. support op f (x INSERT s) =
       if f(x) = neutral op then support op f s
       else x INSERT (support op f s)) /\
   (!f x s. support op f (s DELETE x) = (support op f s) DELETE x) /\
   (!f s t. support op f (s UNION t) =
                    (support op f s) UNION (support op f t)) /\
   (!f s t. support op f (s INTER t) =
                    (support op f s) INTER (support op f t)) /\
   (!f s t. support op f (s DIFF t) =
                    (support op f s) DIFF (support op f t)) /\
   (!f g s.  support op g (IMAGE f s) = IMAGE f (support op (g o f) s))``,
  SIMP_TAC std_ss [support, EXTENSION, GSPECIFICATION, IN_INSERT, IN_DELETE, o_THM,
    IN_IMAGE, NOT_IN_EMPTY, IN_UNION, IN_INTER, IN_DIFF, COND_RAND] THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN ASM_MESON_TAC[]);

val SUPPORT_DELTA = store_thm ("SUPPORT_DELTA",
 ``!op s f a. support op (\x. if x = a then f(x) else neutral op) s =
              if a IN s then support op f {a} else {}``,
  SIMP_TAC std_ss [EXTENSION, support, GSPECIFICATION, IN_SING] THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
  FULL_SIMP_TAC std_ss [GSPECIFICATION, NOT_IN_EMPTY]);

val FINITE_SUPPORT_DELTA = store_thm ("FINITE_SUPPORT_DELTA",
 ``!op f a. FINITE(support op (\x. if x = a then f(x) else neutral op) s)``,
  REWRITE_TAC[SUPPORT_DELTA] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  SIMP_TAC std_ss [FINITE_EMPTY, FINITE_INSERT, FINITE_SUPPORT]);

(* ------------------------------------------------------------------------- *)
(* Key lemmas about the generic notion.                                      *)
(* ------------------------------------------------------------------------- *)

val ITERATE_SUPPORT = store_thm ("ITERATE_SUPPORT",
 ``!op f s. iterate op (support op f s) f = iterate op s f``,
  SIMP_TAC std_ss [iterate, SUPPORT_SUPPORT]);

val ITERATE_EXPAND_CASES = store_thm ("ITERATE_EXPAND_CASES",
 ``!op f s. iterate op s f =
              if FINITE(support op f s) then iterate op (support op f s) f
              else neutral op``,
  SIMP_TAC std_ss [iterate, SUPPORT_SUPPORT]);

val ITERATE_CLAUSES_GEN = store_thm ("ITERATE_CLAUSES_GEN",
 ``!op. monoidal op
        ==> (!(f:'a->'b). iterate op {} f = neutral op) /\
            (!f x s. monoidal op /\ FINITE(support op (f:'a->'b) s)
                     ==> (iterate op (x INSERT s) f =
                                if x IN s then iterate op s f
                                else op (f x) (iterate op s f)))``,
  GEN_TAC THEN STRIP_TAC THEN CONV_TAC AND_FORALL_CONV THEN
  GEN_TAC THEN MP_TAC(ISPECL [``\x a. (op:'b->'b->'b) ((f:'a->'b)(x)) a``,
                              ``neutral op :'b``] FINITE_RECURSION) THEN
  KNOW_TAC ``(!(x :'a) (y :'a) (s :'b). x <> y ==>
        ((\(x :'a) (a :'b). (op :'b -> 'b -> 'b) ((f :'a -> 'b) x) a) x
        ((\(x :'a) (a :'b). op (f x) a) y s) = (\(x :'a) (a :'b). op (f x) a) y
        ((\(x :'a) (a :'b). op (f x) a) x s)))`` THENL
  [ASM_MESON_TAC [monoidal], FULL_SIMP_TAC std_ss [] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[iterate, SUPPORT_CLAUSES, FINITE_EMPTY, FINITE_INSERT] THEN
  GEN_REWR_TAC (LAND_CONV o RATOR_CONV o LAND_CONV) [COND_RAND] THEN
  ASM_REWRITE_TAC[SUPPORT_CLAUSES, FINITE_INSERT, COND_ID] THEN
  ASM_CASES_TAC ``(f:'a->'b) x = neutral op`` THEN ASM_SIMP_TAC std_ss [IN_SUPPORT] THEN
 COND_CASES_TAC THEN ASM_MESON_TAC[monoidal]]);

val ITERATE_CLAUSES = store_thm ("ITERATE_CLAUSES",
 ``!op. monoidal op
        ==> (!f:('b->'a). iterate op {} f = neutral op) /\
            (!f:('b->'a) x s. FINITE(s)
                     ==> (iterate op (x INSERT s) f =
                          if x IN s then iterate op s f
                          else op (f x) (iterate op s f)))``,
  SIMP_TAC std_ss [ITERATE_CLAUSES_GEN, FINITE_SUPPORT]);

val ITERATE_UNION = store_thm ("ITERATE_UNION",
 ``!op. monoidal op
        ==> !f s t. FINITE s /\ FINITE t /\ DISJOINT s t
                    ==> (iterate op (s UNION t) f =
                         op (iterate op s f) (iterate op t f))``,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC [GSYM AND_IMP_INTRO] THEN SIMP_TAC std_ss [RIGHT_FORALL_IMP_THM] THEN
  REPEAT DISCH_TAC THEN
  KNOW_TAC ``!t. (DISJOINT (s :'b -> bool) (t :'b -> bool) ==>
   (iterate (op :'a -> 'a -> 'a) (s UNION t) (f :'b -> 'a) =
   op (iterate op s f) (iterate op t f))) = (\t. DISJOINT s t ==>
   (iterate op (s UNION t) f = op (iterate op s f) (iterate op t f))) t``
  THENL [FULL_SIMP_TAC std_ss [], DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  ASM_SIMP_TAC std_ss [ITERATE_CLAUSES, UNION_EMPTY] THEN
  SIMP_TAC std_ss [GSYM RIGHT_FORALL_IMP_THM] THEN
  ONCE_REWRITE_TAC [DISJOINT_SYM] THEN FULL_SIMP_TAC std_ss [DISJOINT_INSERT]
  THEN ONCE_REWRITE_TAC [UNION_COMM] THEN SIMP_TAC std_ss [INSERT_UNION] THEN
  ASM_SIMP_TAC std_ss [ITERATE_CLAUSES, IN_UNION, UNION_EMPTY, REAL_ADD_RID,
  FINITE_UNION] THEN ASM_MESON_TAC[monoidal]]);

val ITERATE_UNION_GEN = store_thm ("ITERATE_UNION_GEN",
 ``!op. monoidal op
        ==> !(f:'a->'b) s t. FINITE(support op f s) /\ FINITE(support op f t) /\
                           DISJOINT (support op f s) (support op f t)
                           ==> (iterate op (s UNION t) f =
                                op (iterate op s f) (iterate op t f))``,
  ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
  SIMP_TAC std_ss [SUPPORT_CLAUSES, ITERATE_UNION]);

val lemma = prove (
 ``!t s. t SUBSET s ==> (s = (s DIFF t) UNION t) /\ DISJOINT (s DIFF t) t``,
  REPEAT STRIP_TAC THENL [SIMP_TAC std_ss [UNION_DEF, DIFF_DEF, EXTENSION, GSPECIFICATION]
  THEN GEN_TAC THEN EQ_TAC THENL [FULL_SIMP_TAC std_ss [], STRIP_TAC THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF]], SIMP_TAC std_ss [DISJOINT_DEF, INTER_DEF, DIFF_DEF,
  EXTENSION, GSPECIFICATION] THEN GEN_TAC THEN EQ_TAC THENL [STRIP_TAC,
  FULL_SIMP_TAC std_ss [NOT_IN_EMPTY]]]);

val ITERATE_DIFF = store_thm ("ITERATE_DIFF",
 ``!op. monoidal op
        ==> !f s t. FINITE s /\ t SUBSET s
                    ==> (op (iterate op (s DIFF t) f) (iterate op t f) =
                         iterate op s f)``,
  MESON_TAC[lemma, ITERATE_UNION, FINITE_UNION, SUBSET_FINITE, SUBSET_DIFF]);

val ITERATE_DIFF_GEN = store_thm ("ITERATE_DIFF_GEN",
 ``!op. monoidal op
        ==> !f:'a->'b s t. FINITE (support op f s) /\
                         (support op f t) SUBSET (support op f s)
                         ==> (op (iterate op (s DIFF t) f) (iterate op t f) =
                              iterate op s f)``,
  ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
  SIMP_TAC std_ss [SUPPORT_CLAUSES, ITERATE_DIFF]);


val lemma1 = prove (
 ``!a b. a UNION b = ((a DIFF b) UNION (b DIFF a)) UNION (a INTER b)``,
  REPEAT GEN_TAC THEN REWRITE_TAC [UNION_DEF, DIFF_DEF, INTER_DEF]
  THEN SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN GEN_TAC THEN
  EQ_TAC THEN STRIP_TAC THEN RW_TAC std_ss []);

val lemma2 = prove (
 ``!s t f. op (iterate op s f) (iterate op t f) =
           op (iterate op (s DIFF t UNION s INTER t) f)
              (iterate op (t DIFF s UNION s INTER t) f)``,
  REPEAT GEN_TAC THEN
  KNOW_TAC ``((s:'a->bool) = s DIFF t UNION s INTER t) /\
             ((t:'a->bool)= t DIFF s UNION s INTER t)`` THENL
  [REWRITE_TAC [DIFF_DEF, UNION_DEF, DIFF_DEF, INTER_DEF] THEN
  SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN CONJ_TAC THENL
  [GEN_TAC THEN EQ_TAC THENL [RW_TAC std_ss [], RW_TAC std_ss []],
  GEN_TAC THEN EQ_TAC THENL [RW_TAC std_ss [], RW_TAC std_ss []]],
  DISCH_TAC THEN METIS_TAC []]);

val lemma3 = prove (
  ``!s t. DISJOINT (s DIFF t UNION t DIFF s) (s INTER s') /\
            DISJOINT (s DIFF t) (t DIFF s) /\
            DISJOINT (s DIFF t) (t INTER s) /\
            DISJOINT (s DIFF t) (s INTER t)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [DISJOINT_DEF, DIFF_DEF, UNION_DEF, INTER_DEF] THEN
  SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN
  CONV_TAC CONJ_FORALL_CONV THEN GEN_TAC THEN CONJ_TAC THENL
  [EQ_TAC THENL [RW_TAC std_ss [], RW_TAC std_ss [NOT_IN_EMPTY]], CONJ_TAC THENL
  [EQ_TAC THENL [RW_TAC std_ss [], RW_TAC std_ss [NOT_IN_EMPTY]], CONJ_TAC THENL
  [EQ_TAC THENL [RW_TAC std_ss [], RW_TAC std_ss [NOT_IN_EMPTY]],
  EQ_TAC THENL [RW_TAC std_ss [], RW_TAC std_ss [NOT_IN_EMPTY]]]]]);

val ITERATE_INCL_EXCL = store_thm ("ITERATE_INCL_EXCL",
 ``!op. monoidal op
        ==> !s t f. FINITE s /\ FINITE t
                    ==> (op (iterate op s f) (iterate op t f) =
                         op (iterate op (s UNION t) f)
                            (iterate op (s INTER t) f))``,
 REPEAT STRIP_TAC THEN
 ONCE_REWRITE_TAC [lemma1] THEN GEN_REWR_TAC (LAND_CONV) [lemma2] THEN
 KNOW_TAC ``(FINITE ((s:'b->bool) DIFF (t:'b->bool) UNION (t DIFF s))) /\
  (FINITE (s INTER t)) /\ (DISJOINT (s DIFF t UNION (t DIFF s)) (s INTER t))`` THENL
 [FULL_SIMP_TAC std_ss [FINITE_DIFF, FINITE_UNION, FINITE_INTER] THEN
 SIMP_TAC std_ss [DISJOINT_DEF, DIFF_DEF, UNION_DEF, INTER_DEF, EXTENSION, GSPECIFICATION]
 THEN GEN_TAC THEN EQ_TAC THENL [RW_TAC std_ss [], RW_TAC std_ss [NOT_IN_EMPTY]],
 STRIP_TAC THEN ASM_SIMP_TAC std_ss [ITERATE_UNION, FINITE_UNION, FINITE_DIFF,
 FINITE_INTER, lemma3] THEN METIS_TAC [MONOIDAL_AC]]);

val ITERATE_CLOSED = store_thm ("ITERATE_CLOSED",
 ``!op. monoidal op
        ==> !P. P(neutral op) /\ (!x y. P x /\ P y ==> P (op x y))
                ==> !f:'a->'b s. (!x. x IN s /\ ~(f x = neutral op) ==> P(f x))
                               ==> P(iterate op s f)``,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[GSYM IN_SUPPORT] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(``support op (f:'a->'b) s``,``s:'a->bool``) THEN
  GEN_TAC THEN KNOW_TAC ``(monoidal (op :'b -> 'b -> 'b) ==>
  (P :'b -> bool) (neutral op) ==> (!(x :'b) (y :'b). P x /\
  P y ==> P (op x y)) ==> (!(x :'a). x IN s ==>
  P ((f :'a -> 'b) x)) ==> P (iterate op s f)) =
  ((\s. monoidal op ==> P (neutral op) ==>
  (!x y. P x /\ P y ==> P (op x y)) ==> (!x. x IN s ==> P (f x)) ==>
  P (iterate op s f))s)`` THENL [FULL_SIMP_TAC std_ss [],
  DISCH_TAC THEN ONCE_ASM_REWRITE_TAC []
  THEN MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  ASM_SIMP_TAC std_ss [ITERATE_CLAUSES, FINITE_INSERT, IN_INSERT]]);

val ITERATE_RELATED = store_thm ("ITERATE_RELATED",
 ``!op. monoidal op
        ==> !R. R (neutral op) (neutral op) /\
                (!x1 y1 x2 y2. R x1 x2 /\ R y1 y2 ==> R (op x1 y1) (op x2 y2))
                ==> !f:'a->'b g s.
                      FINITE s /\
                      (!x. x IN s ==> R (f x) (g x))
                      ==> R (iterate op s f) (iterate op s g)``,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  GEN_TAC THEN REWRITE_TAC[GSYM AND_IMP_INTRO] THEN GEN_TAC THEN
  KNOW_TAC ``(!x. x IN s ==> R (f x) (g x)) ==>
    R (iterate op s f) (iterate op s g) <=> (\s. (!x. x IN s ==> R (f x) (g x)) ==>
    R (iterate op s f) (iterate op s g)) s`` THENL [FULL_SIMP_TAC std_ss [],
   DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  ASM_SIMP_TAC std_ss [ITERATE_CLAUSES, FINITE_INSERT, IN_INSERT]]);

val ITERATE_EQ_NEUTRAL = store_thm ("ITERATE_EQ_NEUTRAL",
 ``!op. monoidal op
        ==> !f:'a->'b s. (!x. x IN s ==> (f(x) = neutral op))
                       ==> (iterate op s f = neutral op)``,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN ``support op (f:'a->'b) s = {}`` ASSUME_TAC THENL
   [ASM_MESON_TAC[EXTENSION, NOT_IN_EMPTY, IN_SUPPORT],
    ASM_MESON_TAC[ITERATE_CLAUSES, FINITE_EMPTY, ITERATE_SUPPORT]]);

val ITERATE_SING = store_thm ("ITERATE_SING",
 ``!op. monoidal op ==> !f:'a->'b x. (iterate op {x} f = f x)``,
  SIMP_TAC std_ss [ITERATE_CLAUSES, FINITE_EMPTY, NOT_IN_EMPTY] THEN
  MESON_TAC[monoidal]);

val ITERATE_DELETE = store_thm ("ITERATE_DELETE",
 ``!op. monoidal op
        ==> !(f:'a->'b) s a. FINITE s /\ a IN s
        ==> (op (f a) (iterate op (s DELETE a) f) = iterate op s f)``,
  METIS_TAC[ITERATE_CLAUSES, FINITE_DELETE, IN_DELETE, INSERT_DELETE]);

val ITERATE_DELTA = store_thm ("ITERATE_DELTA",
 ``!op. monoidal op
        ==> !f a s. iterate op s (\x. if x = a then f(x) else neutral op) =
                    if a IN s then f(a) else neutral op``,
  GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
  REWRITE_TAC[SUPPORT_DELTA] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC std_ss [ITERATE_CLAUSES] THEN REWRITE_TAC[SUPPORT_CLAUSES] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [ITERATE_CLAUSES, ITERATE_SING]);

val lemma = prove (
 ``(a <=> a') /\ (a' ==> (b = b'))
      ==> ((if a then b else c) = (if a' then b' else c))``,
  METIS_TAC []);

val ITERATE_IMAGE = store_thm ("ITERATE_IMAGE",
 ``!op. monoidal op
       ==> !f:'a->'b g:'b->'c s.
                (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
                ==> (iterate op (IMAGE f s) g = iterate op s (g o f))``,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN ``!s. FINITE s /\
        (!x y:'a. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
        ==> (iterate op (IMAGE f s) (g:'b->'c) = iterate op s (g o f))``
  ASSUME_TAC THENL [REWRITE_TAC[GSYM AND_IMP_INTRO] THEN GEN_TAC THEN
  KNOW_TAC ``((!x y. x IN s ==> y IN s ==> (f x = f y) ==> (x = y)) ==>
              (iterate op (IMAGE f s) g = iterate op s (g o f))) =
         (\s. (!x y. x IN s ==> y IN s ==> (f x = f y) ==> (x = y)) ==>
              (iterate op (IMAGE f s) g = iterate op s (g o f))) s``
  THENL [FULL_SIMP_TAC std_ss [], DISCH_TAC THEN ONCE_ASM_REWRITE_TAC []
  THEN MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  ASM_SIMP_TAC std_ss [ITERATE_CLAUSES, IMAGE_EMPTY, IMAGE_INSERT, IMAGE_FINITE] THEN
  REWRITE_TAC[o_THM, IN_INSERT] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
  [METIS_TAC[IN_IMAGE], METIS_TAC[IN_IMAGE]]], GEN_TAC THEN DISCH_TAC
  THEN ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC lemma THEN REWRITE_TAC[SUPPORT_CLAUSES] THEN REPEAT STRIP_TAC THENL
  [MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN ASM_MESON_TAC[IN_SUPPORT],
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[IN_SUPPORT]]]);

val ITERATE_BIJECTION = store_thm ("ITERATE_BIJECTION",
 ``!op. monoidal op
        ==>  !(f:'a->'b) p s.
                (!x. x IN s ==> (p x IN s)) /\
                (!y. y IN s ==> ?!x. x IN s /\ (p x = y))
                ==> (iterate op s f = iterate op s (f o p))``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC ``iterate op (IMAGE (p:'a->'a) s) (f:'a->'b)`` THEN CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN SIMP_TAC std_ss[EXTENSION, IN_IMAGE] THEN METIS_TAC [],
    METIS_TAC[ITERATE_IMAGE]]);

Theorem ITERATE_PERMUTES :
    !op. monoidal op
         ==> !(f:'a->'b) p s. p PERMUTES s
                ==> (iterate op s f = iterate op s (f o p))
Proof
    RW_TAC std_ss [BIJ_ALT, IN_FUNSET]
 >> irule ITERATE_BIJECTION
 >> RW_TAC std_ss []
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

val lemma1 = prove (
 ``{a,b | F} = {}``,
  SRW_TAC [][EXTENSION]);

val lemma2 = prove (
 ``{i,j | i IN a INSERT s /\ j IN t i} =
            IMAGE (\j. a,j) (t a) UNION {i,j | i IN s /\ j IN t i}``,
  SRW_TAC [][EXTENSION] THEN SET_TAC []);

val ITERATE_ITERATE_PRODUCT = store_thm ("ITERATE_ITERATE_PRODUCT",
 ``!op. monoidal op
        ==> !s:'a->bool t:'a->'b->bool x:'a->'b->'c.
                FINITE s /\ (!i. i IN s ==> FINITE(t i))
                ==> (iterate op s (\i. iterate op (t i) (x i)) =
                     iterate op {i,j | i IN s /\ j IN t i} (\(i,j). x i j))``,
  GEN_TAC THEN DISCH_TAC THEN
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN
  KNOW_TAC ``(!t:'a->'b->bool. (!i. i IN s ==> FINITE (t i)) ==>
        !x:'a->'b->'c. iterate op s (\i. iterate op (t i) (x i)) =
            iterate op {(i,j) | i IN s /\ j IN t i} (\(i,j). x i j)) =
             (\s. !t:'a->'b->bool. (!i. i IN s ==> FINITE (t i)) ==>
        !x:'a->'b->'c. iterate op s (\i. iterate op (t i) (x i)) =
            iterate op {(i,j) | i IN s /\ j IN t i} (\(i,j). x i j)) (s:'a->bool)``
  THENL [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISC_RW_KILL THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  ASM_SIMP_TAC std_ss [NOT_IN_EMPTY, lemma1, ITERATE_CLAUSES] THEN
  REWRITE_TAC[lemma2] THEN ASM_SIMP_TAC std_ss [FINITE_INSERT, ITERATE_CLAUSES,
  IN_INSERT] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fn th =>
   W(MP_TAC o PART_MATCH (lhand o rand) (MATCH_MP ITERATE_UNION th) o
   rand o snd)) THEN
   KNOW_TAC ``FINITE (IMAGE (\j. (e,j)) ((t:'a->'b->bool) e)) /\
     FINITE {(i,j) | i IN (s:'a->bool) /\ j IN t i} /\
     DISJOINT (IMAGE (\j. (e,j)) (t e)) {(i,j) | i IN s /\ j IN t i}`` THENL
  [ASM_SIMP_TAC std_ss [IMAGE_FINITE, FINITE_PRODUCT_DEPENDENT, IN_INSERT] THEN
    SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_IMAGE, IN_INTER, NOT_IN_EMPTY,
    GSPECIFICATION, EXISTS_PROD, FORALL_PROD, PAIR_EQ] THEN ASM_MESON_TAC[],
    ALL_TAC] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_ASSUM(fn th =>
   W(MP_TAC o PART_MATCH (lhand o rand) (MATCH_MP ITERATE_IMAGE th) o
   rand o snd)) THEN KNOW_TAC ``(!x:'b y:'b. x IN (t:'a->'b->bool) (e:'a) /\
       y IN t e /\ ((\j. (e,j)) x = (\j. (e,j)) y) ==> (x = y))`` THENL
  [SIMP_TAC std_ss [FORALL_PROD], ALL_TAC] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF] THEN
  CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN FULL_SIMP_TAC std_ss [ETA_AX]
  THEN AP_TERM_TAC THEN METIS_TAC []);

val ITERATE_EQ = store_thm("ITERATE_EQ",
 ``!op. monoidal op
        ==> !f:'a->'b g s.
              (!x. x IN s ==> (f x = g x)) ==> (iterate op s f = iterate op s g)``,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  SUBGOAL_THEN ``support op g s = support op (f:'a->'b) s`` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION, IN_SUPPORT] THEN ASM_MESON_TAC[], COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN SUBGOAL_THEN
   ``FINITE(support op (f:'a->'b) s) /\
    (!x. x IN (support op f s) ==> (f x = g x))``
  MP_TAC THENL [ASM_MESON_TAC[IN_SUPPORT], REWRITE_TAC[GSYM AND_IMP_INTRO] THEN
  SPEC_TAC(``support op (f:'a->'b) s``,``t:'a->bool``) THEN GEN_TAC THEN
  KNOW_TAC ``(!x. x IN t ==> (f x = g x)) ==> (iterate op t f = iterate op t g) <=>
        (\t. (!x. x IN t ==> (f x = g x)) ==> (iterate op t f = iterate op t g)) t``
  THENL [FULL_SIMP_TAC std_ss [], DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN ASM_SIMP_TAC std_ss [ITERATE_CLAUSES] THEN
  MESON_TAC[IN_INSERT]]]]);

val ITERATE_EQ_GENERAL = store_thm ("ITERATE_EQ_GENERAL",
 ``!op. monoidal op
        ==> !s:'a->bool t:'b->bool f:'a->'c g h.
                (!y. y IN t ==> ?!x. x IN s /\ (h(x) = y)) /\
                (!x. x IN s ==> h(x) IN t /\ (g(h x) = f x))
                ==> (iterate op s f = iterate op t g)``,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN ``t = IMAGE (h:'a->'b) s`` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION, IN_IMAGE] THEN ASM_MESON_TAC[],
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC ``iterate op s ((g:'b->'c) o (h:'a->'b))`` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[ITERATE_EQ, o_THM],
    CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_IMAGE) THEN
    ASM_MESON_TAC[]]]);

val ITERATE_EQ_GENERAL_INVERSES = store_thm ("ITERATE_EQ_GENERAL_INVERSES",
 ``!op. monoidal op
        ==> !s:'a->bool t:'b->bool f:'a->'c g h k.
                (!y. y IN t ==> k(y) IN s /\ (h(k y) = y)) /\
                (!x. x IN s ==> h(x) IN t /\ (k(h x) = x) /\ (g(h x) = f x))
                ==> (iterate op s f = iterate op t g)``,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_EQ_GENERAL) THEN
  EXISTS_TAC ``h:'a->'b`` THEN ASM_MESON_TAC[]);

val ITERATE_INJECTION = store_thm ("ITERATE_INJECTION",
 ``!op. monoidal op
          ==> !f:'a->'b p:'a->'a s.
                      FINITE s /\
                      (!x. x IN s ==> p x IN s) /\
                      (!x y. x IN s /\ y IN s /\ (p x = p y) ==> (x = y))
                      ==> (iterate op s (f o p) = iterate op s f)``,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_BIJECTION) THEN
  MP_TAC(ISPECL [``s:'a->bool``, ``p:'a->'a``] SURJECTIVE_IFF_INJECTIVE) THEN
  ASM_REWRITE_TAC[SUBSET_DEF, IN_IMAGE] THEN ASM_MESON_TAC[]);

val ITERATE_UNION_NONZERO = store_thm ("ITERATE_UNION_NONZERO",
 ``!op. monoidal op
        ==> !f:'a->'b s t.
                FINITE(s) /\ FINITE(t) /\
                (!x. x IN (s INTER t) ==> (f x = neutral(op)))
                ==> (iterate op (s UNION t) f =
                    op (iterate op s f) (iterate op t f))``,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
  REWRITE_TAC[SUPPORT_CLAUSES] THEN KNOW_TAC
  ``FINITE (support op (f :'a -> 'b) (s :'a -> bool)) /\
    FINITE (support op f (t :'a -> bool)) /\
    DISJOINT (support op f s) (support op f t)`` THENL
  [ASM_SIMP_TAC std_ss [FINITE_SUPPORT, DISJOINT_DEF, IN_INTER,
  IN_SUPPORT, EXTENSION] THEN ASM_MESON_TAC[IN_INTER, NOT_IN_EMPTY],
  ASM_MESON_TAC[ITERATE_UNION]]);

val ITERATE_OP = store_thm ("ITERATE_OP",
 ``!op. monoidal op
        ==> !f g s. FINITE s
                    ==> (iterate op s (\x. op (f x) (g x)) =
                        op (iterate op s f) (iterate op s g))``,
  GEN_TAC THEN DISCH_TAC THEN
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  KNOW_TAC ``((iterate :('a -> 'a -> 'a) -> ('b -> bool) -> ('b -> 'a) -> 'a)
       (op :'a -> 'a -> 'a) s
       (\(x :'b). op ((f :'b -> 'a) x) ((g :'b -> 'a) x)) =
     op (iterate op s f) (iterate op s g)) =
           (\s. ((iterate :('a -> 'a -> 'a) -> ('b -> bool) -> ('b -> 'a) -> 'a)
       (op :'a -> 'a -> 'a) s
       (\(x :'b). op ((f :'b -> 'a) x) ((g :'b -> 'a) x)) =
     op (iterate op s f) (iterate op s g)))s ``THENL [FULL_SIMP_TAC std_ss [],
  DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  ASM_SIMP_TAC std_ss [ITERATE_CLAUSES, MONOIDAL_AC]]);

val ITERATE_SUPERSET = store_thm ("ITERATE_SUPERSET",
 ``!op. monoidal op
        ==> !f:'a->'b u v.
            u SUBSET v /\
            (!x. x IN v /\ ~(x IN u) ==> (f(x) = neutral op))
            ==> (iterate op v f = iterate op u f)``,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC std_ss [support, EXTENSION, GSPECIFICATION] THEN
  ASM_MESON_TAC[SUBSET_DEF]);

val ITERATE_IMAGE_NONZERO = store_thm ("ITERATE_IMAGE_NONZERO",
 ``!op. monoidal op
        ==> !g:'b->'c f:'a->'b s.
                    FINITE s /\
                    (!x y. x IN s /\ y IN s /\ ~(x = y) /\ (f x = f y)
                           ==> (g(f x) = neutral op))
                    ==> (iterate op (IMAGE f s) g = iterate op s (g o f))``,
  GEN_TAC THEN DISCH_TAC THEN
  GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] THEN GEN_TAC THEN
  KNOW_TAC `` ((!(x :'a) (y :'a).
       x IN s /\ y IN s /\ x <> y /\ ((f :'a -> 'b) x = f y) ==>
       ((g :'b -> 'c) (f x) = neutral (op :'c -> 'c -> 'c))) ==>
    (iterate op (IMAGE f s) g = iterate op s (g o f))) = (\s. (!(x :'a) (y :'a).
       x IN s /\ y IN s /\ x <> y /\ ((f :'a -> 'b) x = f y) ==>
       ((g :'b -> 'c) (f x) = neutral (op :'c -> 'c -> 'c))) ==>
    (iterate op (IMAGE f s) g = iterate op s (g o f))) s`` THENL
  [FULL_SIMP_TAC std_ss [], DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  ASM_SIMP_TAC std_ss [IMAGE_EMPTY, IMAGE_INSERT, ITERATE_CLAUSES, IMAGE_FINITE]
  THEN SIMP_TAC std_ss [GSYM RIGHT_FORALL_IMP_THM] THEN
  MAP_EVERY X_GEN_TAC [``s':'a->bool``,``a:'a``] THEN
  REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN ``iterate op s' ((g:'b->'c) o (f:'a->'b)) = iterate op (IMAGE f s') g``
  SUBST1_TAC THENL [ASM_MESON_TAC[], ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN ``(g:'b->'c) ((f:'a->'b) a) = neutral op`` SUBST1_TAC THEN
  ASM_MESON_TAC[MONOIDAL_AC]]);

val lemma = prove (
  ``!s. DISJOINT {x | x IN s /\ P x} {x | x IN s /\ ~P x}``,
  GEN_TAC THEN SIMP_TAC std_ss [DISJOINT_DEF, INTER_DEF, EXTENSION, GSPECIFICATION]
  THEN GEN_TAC THEN EQ_TAC THENL
  [RW_TAC std_ss [], RW_TAC std_ss [NOT_IN_EMPTY]]);

val ITERATE_CASES = store_thm ("ITERATE_CASES",
  ``!op. monoidal op
        ==> !s P f g:'a->'b.
                FINITE s
                ==> (iterate op s (\x. if P x then f x else g x) =
                    op (iterate op {x | x IN s /\ P x} f)
                       (iterate op {x | x IN s /\ ~P x} g))``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   ``op (iterate op {x | x IN s /\ P x} (\x. if P x then f x else (g:'a->'b) x))
       (iterate op {x | x IN s /\ ~P x} (\x. if P x then f x else g x))`` THEN
  CONJ_TAC THENL [KNOW_TAC ``FINITE {(x:'a) | x IN s /\ P x} /\
  FINITE {x | x IN s /\ ~P x} /\ DISJOINT {x | x IN s /\ P x} {x | x IN s /\ ~P x}``
  THENL [FULL_SIMP_TAC std_ss [FINITE_RESTRICT, lemma], STRIP_TAC THEN
  FULL_SIMP_TAC std_ss [GSYM ITERATE_UNION] THEN AP_THM_TAC THEN AP_TERM_TAC
  THEN FULL_SIMP_TAC std_ss [UNION_DEF, EXTENSION, GSPECIFICATION] THEN METIS_TAC []],
  BINOP_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_EQ) THEN
    SIMP_TAC std_ss [GSPECIFICATION]]);

val ITERATE_OP_GEN = store_thm ("ITERATE_OP_GEN",
 ``!op. monoidal op
        ==> !f g:'a->'b s.
                FINITE(support op f s) /\ FINITE(support op g s)
                ==> (iterate op s (\x. op (f x) (g x)) =
                    op (iterate op s f) (iterate op s g))``,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC ``iterate op (support op f s UNION support op g s)
                         (\x. op ((f:'a->'b) x) (g x))`` THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV,
    ASM_SIMP_TAC std_ss [ITERATE_OP, FINITE_UNION] THEN BINOP_TAC] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_SUPERSET) THEN
  SIMP_TAC std_ss [support, GSPECIFICATION, SUBSET_DEF, IN_UNION] THEN
  ASM_MESON_TAC[monoidal]);

val ITERATE_CLAUSES_NUMSEG = store_thm ("ITERATE_CLAUSES_NUMSEG",
  ``!op. monoidal op
        ==> (!m. iterate op {m..0} f = if m = 0 then f(0) else neutral op) /\
            (!m n. iterate op {m..SUC n} f =
                      if m <= SUC n then op (iterate op {m..n} f) (f(SUC n))
                      else iterate op {m..n} f)``,
  REWRITE_TAC[NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC std_ss [ITERATE_CLAUSES, FINITE_NUMSEG, IN_NUMSEG, FINITE_EMPTY] THEN
  REWRITE_TAC[ARITH_PROVE ``~(SUC n <= n)``, NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[monoidal]);

val ITERATE_PAIR = store_thm ("ITERATE_PAIR",
  ``!op. monoidal op
        ==> !f m n. iterate op {2*m..2*n+1} f =
                    iterate op {m..n} (\i. op (f(2*i)) (f(2*i+1)))``,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THEN CONV_TAC REDUCE_CONV THENL
   [REWRITE_TAC [ONE] THEN ASM_SIMP_TAC std_ss [ITERATE_CLAUSES_NUMSEG] THEN
    REWRITE_TAC [ONE] THEN
    REWRITE_TAC[ARITH_PROVE ``2 * m <= SUC 0 <=> (m = 0)``] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[MULT_EQ_0],
    REWRITE_TAC[ARITH_PROVE ``2 * SUC n + 1 = SUC(SUC(2 * n + 1))``] THEN
    ASM_SIMP_TAC std_ss [ITERATE_CLAUSES_NUMSEG] THEN
    REWRITE_TAC[ARITH_PROVE ``2 * m <= SUC(SUC(2 * n + 1)) <=> m <= SUC n``,
                ARITH_PROVE ``2 * m <= SUC(2 * n + 1) <=> m <= SUC n``] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_PROVE ``2 * SUC n = SUC(2 * n + 1)``,
                ARITH_PROVE ``2 * SUC n + 1 = SUC(SUC(2 * n + 1))``] THEN
    ASM_MESON_TAC[monoidal]]);

(* ------------------------------------------------------------------------- *)
(* Sums of natural numbers.                                                  *)
(* ------------------------------------------------------------------------- *)

Definition nsum :
   (nsum :('a->bool)->('a->num)->num) = iterate (+)
End

val NEUTRAL_ADD = store_thm ("NEUTRAL_ADD",
  ``neutral((+):num->num->num) = 0``,
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  MESON_TAC[ADD_CLAUSES]);

val NEUTRAL_MUL = store_thm ("NEUTRAL_MUL",
  ``neutral(( * ):num->num->num) = 1``,
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  MESON_TAC[MULT_CLAUSES, MULT_EQ_1]);

val MONOIDAL_ADD = store_thm ("MONOIDAL_ADD",
  ``monoidal((+):num->num->num)``,
  REWRITE_TAC[monoidal, NEUTRAL_ADD] THEN ARITH_TAC);

val MONOIDAL_MUL = store_thm ("MONOIDAL_MUL",
 ``monoidal(( * ):num->num->num)``,
  REWRITE_TAC[monoidal, NEUTRAL_MUL] THEN ARITH_TAC);

val NSUM_DEGENERATE = store_thm ("NSUM_DEGENERATE",
 ``!f s. ~(FINITE {x | x IN s /\ ~(f x = 0:num)}) ==> (nsum s f = 0:num)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[nsum] THEN
  SIMP_TAC std_ss [iterate, support, NEUTRAL_ADD]);

val NSUM_CLAUSES = store_thm ("NSUM_CLAUSES",
 ``(!f. nsum {} f = 0) /\
   (!x f s. FINITE(s)
            ==> (nsum (x INSERT s) f =
                 if x IN s then nsum s f else f(x) + nsum s f))``,
  REWRITE_TAC[nsum, GSYM NEUTRAL_ADD] THEN
  KNOW_TAC ``monoidal ((+):num->num->num)`` THENL [REWRITE_TAC[MONOIDAL_ADD],
  METIS_TAC [ITERATE_CLAUSES]]);

val NSUM_UNION = store_thm ("NSUM_UNION",
 ``!f s t. FINITE s /\ FINITE t /\ DISJOINT s t
           ==> (nsum (s UNION t) f = nsum s f + nsum t f)``,
  SIMP_TAC std_ss [nsum, ITERATE_UNION, MONOIDAL_ADD]);

val NSUM_DIFF = store_thm ("NSUM_DIFF",
 ``!f s t. FINITE s /\ t SUBSET s
           ==> (nsum (s DIFF t) f = nsum s f - nsum t f)``,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ARITH_PROVE ``(x + z = y:num) ==> (x = y - z)``) THEN
  ASM_SIMP_TAC std_ss [nsum, ITERATE_DIFF, MONOIDAL_ADD]);

val NSUM_INCL_EXCL = store_thm ("NSUM_INCL_EXCL",
 ``!s t (f:'a->num).
     FINITE s /\ FINITE t
     ==> (nsum s f + nsum t f = nsum (s UNION t) f + nsum (s INTER t) f)``,
  REWRITE_TAC[nsum, GSYM NEUTRAL_ADD] THEN
  MATCH_MP_TAC ITERATE_INCL_EXCL THEN REWRITE_TAC[MONOIDAL_ADD]);

val NSUM_SUPPORT = store_thm ("NSUM_SUPPORT",
 ``!f s. nsum (support (+) f s) f = nsum s f``,
  SIMP_TAC std_ss [nsum, iterate, SUPPORT_SUPPORT]);

val NSUM_ADD = store_thm ("NSUM_ADD",
 ``!f g s. FINITE s ==> (nsum s (\x. f(x) + g(x)) = nsum s f + nsum s g)``,
  SIMP_TAC std_ss [nsum, ITERATE_OP, MONOIDAL_ADD]);

val NSUM_ADD_GEN = store_thm ("NSUM_ADD_GEN",
 ``!f g s.
       FINITE {x | x IN s /\ ~(f x = 0)} /\ FINITE {x | x IN s /\ ~(g x = 0:num)}
       ==> (nsum s (\x. f x + g x) = nsum s f + nsum s g)``,
  REWRITE_TAC[GSYM NEUTRAL_ADD, GSYM support, nsum] THEN
  MATCH_MP_TAC ITERATE_OP_GEN THEN ACCEPT_TAC MONOIDAL_ADD);

val NSUM_EQ_0 = store_thm ("NSUM_EQ_0",
 ``!f s. (!x:'a. x IN s ==> (f(x) = 0:num)) ==> (nsum s f = 0:num)``,
  REWRITE_TAC[nsum, GSYM NEUTRAL_ADD] THEN
  SIMP_TAC std_ss [ITERATE_EQ_NEUTRAL, MONOIDAL_ADD]);

val NSUM_0 = store_thm ("NSUM_0",
 ``!s:'a->bool. nsum s (\n. 0:num) = 0:num``,
  SIMP_TAC std_ss [NSUM_EQ_0]);

val NSUM_LMUL = store_thm ("NSUM_LMUL",
 ``!f c s:'a->bool. nsum s (\x. c * f(x)) = c * nsum s f``,
  REPEAT GEN_TAC THEN ASM_CASES_TAC ``c = 0:num`` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES, NSUM_0] THEN REWRITE_TAC[nsum] THEN
  ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  SUBGOAL_THEN ``support (+) (\x:'a. (c:num) * f(x)) s = support (+) f s`` SUBST1_TAC
  THENL [ASM_SIMP_TAC std_ss [support, MULT_EQ_0, NEUTRAL_ADD], ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[NEUTRAL_ADD, MULT_CLAUSES] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(``support (+) f (s:'a->bool)``,``t:'a->bool``) THEN
  REWRITE_TAC[GSYM nsum] THEN Q.ABBREV_TAC `ss = support $+ f s` THEN
  KNOW_TAC ``((nsum ss (\x. c * f x) = c * nsum ss f) =
        (\ss. (nsum ss (\x. c * f x) = c * nsum ss f)) ss)`` THENL
  [FULL_SIMP_TAC  std_ss [], ALL_TAC] THEN DISCH_TAC THEN
  ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FINITE_INDUCT THEN
  BETA_TAC THEN SIMP_TAC std_ss [NSUM_CLAUSES, MULT_CLAUSES, LEFT_ADD_DISTRIB]);

val NSUM_RMUL = store_thm ("NSUM_RMUL",
 ``!f c s:'a->bool. nsum s (\x. f(x) * c) = nsum s f * c``,
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[NSUM_LMUL]);

val NSUM_LE = store_thm ("NSUM_LE",
 ``!f g s. FINITE(s) /\ (!x. x IN s ==> f(x) <= g(x))
           ==> nsum s f <= nsum s g``,
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] THEN REPEAT GEN_TAC THEN
  KNOW_TAC ``((!x. x IN s ==> f x <= g x) ==> nsum s f <= nsum s g) =
         (\s. (!x. x IN s ==> f x <= g x) ==> nsum s f <= nsum s g) s`` THENL
  [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISCH_TAC THEN ONCE_ASM_REWRITE_TAC []
  THEN MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [NSUM_CLAUSES, LESS_EQ_REFL, LESS_EQ_LESS_EQ_MONO, IN_INSERT]);

val NSUM_LT = store_thm ("NSUM_LT",
 ``!f g s:'a->bool.
        FINITE(s) /\ (!x. x IN s ==> f(x) <= g(x)) /\
        (?x. x IN s /\ f(x) < g(x))
         ==> nsum s f < nsum s g``,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN ``a:'a`` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN ``s = (a:'a) INSERT (s DELETE a)`` SUBST1_TAC THENL
   [UNDISCH_TAC ``a:'a IN s`` THEN SET_TAC[], ALL_TAC] THEN
  ASM_SIMP_TAC std_ss [NSUM_CLAUSES, FINITE_DELETE, IN_DELETE] THEN
  ASM_SIMP_TAC std_ss [ARITH_PROVE ``m < p /\ n <= q ==> m + n < p + q:num``,
  NSUM_LE, IN_DELETE, FINITE_DELETE]);

val NSUM_LT_ALL = store_thm ("NSUM_LT_ALL",
 ``!f g s. FINITE s /\ ~(s = {}) /\ (!x. x IN s ==> f(x) < g(x))
           ==> nsum s f < nsum s g``,
  MESON_TAC[MEMBER_NOT_EMPTY, LESS_IMP_LESS_OR_EQ, NSUM_LT]);

val NSUM_EQ = store_thm ("NSUM_EQ",
 ``!f g s. (!x. x IN s ==> (f x = g x)) ==> (nsum s f = nsum s g)``,
  REWRITE_TAC[nsum] THEN
  MATCH_MP_TAC ITERATE_EQ THEN REWRITE_TAC[MONOIDAL_ADD]);

val NSUM_CONST = store_thm ("NSUM_CONST",
 ``!c s. FINITE s ==> (nsum s (\n. c) = (CARD s) * c)``,
  REPEAT GEN_TAC THEN KNOW_TAC ``(nsum s (\n. c) = CARD s * c) =
                            (\s. (nsum s (\n. c) = CARD s * c)) s ``
  THENL [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISCH_TAC THEN
  ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FINITE_INDUCT THEN
  BETA_TAC THEN SIMP_TAC std_ss [NSUM_CLAUSES, CARD_DEF] THEN
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [ADD1, RIGHT_ADD_DISTRIB]
  THEN ARITH_TAC);

val NSUM_POS_BOUND = store_thm ("NSUM_POS_BOUND",
 ``!f b s. FINITE s /\ nsum s f <= b ==> !x:'a. x IN s ==> f x <= b``,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM AND_IMP_INTRO] THEN
  KNOW_TAC ``(nsum s f <= b ==> !x. x IN s ==> f x <= b) =
         (\s. nsum s f <= b ==> !x. x IN s ==> f x <= b) s`` THENL
  [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISCH_TAC THEN
  ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FINITE_INDUCT THEN
  BETA_TAC THEN SIMP_TAC std_ss [NSUM_CLAUSES, NOT_IN_EMPTY, IN_INSERT]
  THEN MESON_TAC[ZERO_LESS_EQ, ARITH_PROVE
   ``0:num <= x /\ 0:num <= y /\ x + y <= b ==> x <= b /\ y <= b``]);

val NSUM_EQ_0_IFF = store_thm ("NSUM_EQ_0_IFF",
 ``!s. FINITE s ==> ((nsum s f = 0:num) <=> !x. x IN s ==> (f x = 0:num))``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC std_ss [NSUM_EQ_0] THEN
  ASM_MESON_TAC[LESS_EQ_0, NSUM_POS_BOUND]);

val NSUM_POS_LT = store_thm ("NSUM_POS_LT",
 ``!f s:'a->bool.
        FINITE s /\ (?x. x IN s /\ 0:num < f x)
        ==> 0:num < nsum s f``,
  SIMP_TAC std_ss [ARITH_PROVE ``0:num < n <=> ~(n = 0:num)``, NSUM_EQ_0_IFF]
  THEN MESON_TAC[]);

val NSUM_POS_LT_ALL = store_thm ("NSUM_POS_LT_ALL",
 ``!s f:'a->num.
     FINITE s /\ ~(s = {}) /\ (!i. i IN s ==> 0:num < f i) ==> 0:num < nsum s f``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NSUM_POS_LT THEN
  ASM_MESON_TAC[MEMBER_NOT_EMPTY, REAL_LT_IMP_LE]);

val NSUM_DELETE = store_thm ("NSUM_DELETE",
 ``!f s a. FINITE s /\ a IN s ==> (f(a) + nsum(s DELETE a) f = nsum s f)``,
  SIMP_TAC std_ss [nsum, ITERATE_DELETE, MONOIDAL_ADD]);

val NSUM_SING = store_thm ("NSUM_SING",
 ``!f x. nsum {x} f = f(x)``,
  SIMP_TAC std_ss [NSUM_CLAUSES, FINITE_EMPTY, FINITE_INSERT,
  NOT_IN_EMPTY, ADD_CLAUSES]);

val NSUM_DELTA = store_thm ("NSUM_DELTA",
 ``!s a. nsum s (\x. if x = a:'a then b else 0:num) = if a IN s then b else 0:num``,
  REWRITE_TAC[nsum, GSYM NEUTRAL_ADD] THEN
  SIMP_TAC std_ss [ITERATE_DELTA, MONOIDAL_ADD]);

val NSUM_SWAP = store_thm ("NSUM_SWAP",
 ``!f:'a->'b->num s t.
      FINITE(s) /\ FINITE(t)
      ==> (nsum s (\i. nsum t (f i)) = nsum t (\j. nsum s (\i. f i j)))``,
  GEN_TAC THEN SIMP_TAC std_ss [GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN KNOW_TAC ``( !t. FINITE t ==>
        (nsum s (\i. nsum t (f i)) = nsum t (\j. nsum s (\i. (f:'a->'b->num) i j)))) =
                      (\s.  !t. FINITE t ==>
        (nsum s (\i. nsum t (f i)) = nsum t (\j. nsum s (\i. (f:'a->'b->num) i j)))) s`` THENL
  [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISCH_TAC THEN ONCE_ASM_REWRITE_TAC []
  THEN MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [NSUM_CLAUSES, NSUM_0, NSUM_ADD, ETA_AX] THEN METIS_TAC []);

val NSUM_IMAGE = store_thm ("NSUM_IMAGE",
 ``!f g s. (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> (nsum (IMAGE f s) g = nsum s (g o f))``,
  REWRITE_TAC[nsum, GSYM NEUTRAL_ADD] THEN
  MATCH_MP_TAC ITERATE_IMAGE THEN REWRITE_TAC[MONOIDAL_ADD]);

val NSUM_SUPERSET = store_thm ("NSUM_SUPERSET",
 ``!f:'a->num u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = 0:num))
        ==> (nsum v f = nsum u f)``,
  SIMP_TAC std_ss [nsum, GSYM NEUTRAL_ADD, ITERATE_SUPERSET, MONOIDAL_ADD]);

val NSUM_UNION_RZERO = store_thm ("NSUM_UNION_RZERO",
 ``!f:'a->num u v.
        FINITE u /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = 0:num))
        ==> (nsum (u UNION v) f = nsum u f)``,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [SET_RULE ``u UNION v = u UNION (v DIFF u)``] THEN
  MATCH_MP_TAC NSUM_SUPERSET THEN ASM_MESON_TAC[IN_UNION, IN_DIFF, SUBSET_DEF]);

val NSUM_UNION_LZERO = store_thm ("NSUM_UNION_LZERO",
 ``!f:'a->num u v.
        FINITE v /\ (!x. x IN u /\ ~(x IN v) ==> (f(x) = 0:num))
        ==> (nsum (u UNION v) f = nsum v f)``,
  MESON_TAC[NSUM_UNION_RZERO, UNION_COMM]);

val NSUM_RESTRICT = store_thm ("NSUM_RESTRICT",
 ``!f s. FINITE s ==> (nsum s (\x. if x IN s then f(x) else 0:num) = nsum s f)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC std_ss []);

val NSUM_BOUND = store_thm ("NSUM_BOUND",
 ``!s f b. FINITE s /\ (!x:'a. x IN s ==> f(x) <= b)
           ==> nsum s f <= (CARD s) * b``,
  SIMP_TAC std_ss [GSYM NSUM_CONST, NSUM_LE]);

val NSUM_BOUND_GEN = store_thm ("NSUM_BOUND_GEN",
 ``!s f b. FINITE s /\ ~(s = {}) /\ (!x:'a. x IN s ==> f(x) <= b DIV (CARD s))
           ==> nsum s f <= b``,
  REPEAT STRIP_TAC THEN KNOW_TAC ``0 < CARD s`` THENL
  [METIS_TAC [CARD_EQ_0, NOT_ZERO_LT_ZERO], ALL_TAC] THEN
  STRIP_TAC THEN FULL_SIMP_TAC std_ss [X_LE_DIV] THEN
  SUBGOAL_THEN ``nsum s (\x. CARD(s:'a->bool) * f x) <= CARD s * b`` MP_TAC THENL
   [ASM_SIMP_TAC arith_ss [NSUM_BOUND],
    ASM_SIMP_TAC std_ss [NSUM_LMUL, LE_MULT_LCANCEL, CARD_EQ_0]]);

val NSUM_BOUND_LT = store_thm ("NSUM_BOUND_LT",
 ``!s f b. FINITE s /\ (!x:'a. x IN s ==> f x <= b) /\ (?x. x IN s /\ f x < b)
           ==> nsum s f < (CARD s) * b``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LESS_LESS_EQ_TRANS THEN
  EXISTS_TAC ``nsum s (\x:'a. b)`` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_LT THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[],
    ASM_SIMP_TAC std_ss [NSUM_CONST, LESS_EQ_REFL]]);

val NSUM_BOUND_LT_ALL = store_thm ("NSUM_BOUND_LT_ALL",
 ``!s f b. FINITE s /\ ~(s = {}) /\ (!x. x IN s ==> f(x) < b)
           ==> nsum s f <  (CARD s) * b``,
  MESON_TAC[MEMBER_NOT_EMPTY, LESS_IMP_LESS_OR_EQ, NSUM_BOUND_LT]);

val NSUM_BOUND_LT_GEN = store_thm ("NSUM_BOUND_LT_GEN",
 ``!s f b. FINITE s /\ ~(s = {}) /\ (!x:'a. x IN s ==> f(x) < b DIV (CARD s))
           ==> nsum s f < b``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LESS_LESS_EQ_TRANS THEN
  EXISTS_TAC ``nsum (s:'a->bool) (\a. f(a) + 1:num)`` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_LT_ALL THEN ASM_SIMP_TAC std_ss [] THEN ARITH_TAC,
    MATCH_MP_TAC NSUM_BOUND_GEN THEN
    ASM_SIMP_TAC std_ss [ARITH_PROVE ``a + 1:num <= b <=> a < b``]]);

val NSUM_UNION_EQ = store_thm ("NSUM_UNION_EQ",
 ``!s t u. FINITE u /\ (s INTER t = {}) /\ (s UNION t = u)
           ==> (nsum s f + nsum t f = nsum u f)``,
  MESON_TAC[NSUM_UNION, DISJOINT_DEF, SUBSET_FINITE, SUBSET_UNION]);

val NSUM_EQ_SUPERSET = store_thm ("NSUM_EQ_SUPERSET",
 ``!f s t:'a->bool.
        FINITE t /\ t SUBSET s /\
        (!x. x IN t ==> (f x = g x)) /\
        (!x. x IN s /\ ~(x IN t) ==> (f(x) = 0:num))
        ==> (nsum s f = nsum t g)``,
  MESON_TAC[NSUM_SUPERSET, NSUM_EQ]);

val NSUM_RESTRICT_SET = store_thm ("NSUM_RESTRICT_SET",
 ``!P s f. nsum {x:'a | x IN s /\ P x} f = nsum s (\x. if P x then f(x) else 0:num)``,
  ONCE_REWRITE_TAC[GSYM NSUM_SUPPORT] THEN
  SIMP_TAC std_ss [support, NEUTRAL_ADD, GSPECIFICATION] THEN
  REWRITE_TAC[METIS []``~((if P x then f x else a) = a) <=> P x /\ ~(f x = a)``,
              GSYM CONJ_ASSOC] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC NSUM_EQ THEN SIMP_TAC std_ss [GSPECIFICATION]);

val NSUM_NSUM_RESTRICT = store_thm ("NSUM_NSUM_RESTRICT",
 ``!R f s t.
        FINITE s /\ FINITE t
        ==> (nsum s (\x. nsum {y | y IN t /\ R x y} (\y. f x y)) =
             nsum t (\y. nsum {x | x IN s /\ R x y} (\x. f x y)))``,
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [NSUM_RESTRICT_SET] THEN
  ASSUME_TAC NSUM_SWAP THEN POP_ASSUM (MP_TAC o Q.SPECL
  [`(\x y. if R x y then f x y else 0)`,`s`, `t`]) THEN
  FULL_SIMP_TAC std_ss []);

val CARD_EQ_NSUM = store_thm ("CARD_EQ_NSUM",
 ``!s. FINITE s ==> ((CARD s) = nsum s (\x. 1:num))``,
  SIMP_TAC std_ss [NSUM_CONST, MULT_CLAUSES]);

val NSUM_MULTICOUNT_GEN = store_thm ("NSUM_MULTICOUNT_GEN",
 ``!R:'a->'b->bool s t k.
        FINITE s /\ FINITE t /\
        (!j. j IN t ==> (CARD {i | i IN s /\ R i j} = k(j)))
        ==> (nsum s (\i. (CARD {j | j IN t /\ R i j})) =
             nsum t (\i. (k i)))``,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC ``nsum s (\i:'a. nsum {j:'b | j IN t /\ R i j} (\j. 1:num))`` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC std_ss [CARD_EQ_NSUM, FINITE_RESTRICT],
    ASSUME_TAC NSUM_NSUM_RESTRICT THEN POP_ASSUM (MP_TAC o Q.SPEC `R`)
    THEN FULL_SIMP_TAC std_ss [] THEN DISCH_TAC THEN MATCH_MP_TAC NSUM_EQ
    THEN ASM_SIMP_TAC std_ss [NSUM_CONST, FINITE_RESTRICT] THEN
    REWRITE_TAC[MULT_CLAUSES]]);

val NSUM_MULTICOUNT = store_thm ("NSUM_MULTICOUNT",
 ``!R:'a->'b->bool s t k.
        FINITE s /\ FINITE t /\
        (!j. j IN t ==> (CARD {i | i IN s /\ R i j} = k))
        ==> (nsum s (\i. (CARD {j | j IN t /\ R i j})) = (k * CARD t))``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC ``nsum t (\i:'b. k)`` THEN CONJ_TAC THENL
  [KNOW_TAC ``?j. !i:'b. &k = &(j i):num`` THENL
  [EXISTS_TAC ``(\i:'b. k:num)`` THEN METIS_TAC [], ALL_TAC] THEN
   STRIP_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC NSUM_MULTICOUNT_GEN THEN FULL_SIMP_TAC std_ss [],
   ASM_SIMP_TAC std_ss [NSUM_CONST] THEN ARITH_TAC]);

val NSUM_IMAGE_GEN = store_thm ("NSUM_IMAGE_GEN",
 ``!f:'a->'b g s.
        FINITE s
        ==> (nsum s g =
             nsum (IMAGE f s) (\y. nsum {x | x IN s /\ (f(x) = y)} g))``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   ``nsum s (\x:'a. nsum {y:'b | y IN IMAGE f s /\ (f x = y)} (\y. g x))`` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC ``x:'a`` THEN
    DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN ``{y | y IN IMAGE (f:'a->'b) s /\ (f x = y)} = {(f x)}``
     (fn th => REWRITE_TAC[th, NSUM_SING, o_THM]) THEN
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_SING, IN_IMAGE] THEN
    ASM_MESON_TAC[],
    GEN_REWR_TAC (funpow 2 RAND_CONV o ABS_CONV o RAND_CONV)
     [GSYM ETA_AX] THEN KNOW_TAC ``FINITE (IMAGE (f:'a->'b) s)`` THENL
    [METIS_TAC [IMAGE_FINITE], ALL_TAC] THEN DISCH_TAC THEN
    ASSUME_TAC NSUM_NSUM_RESTRICT THEN
    POP_ASSUM (MP_TAC o Q.SPEC `(\x y. f x = y)`) THEN
    FULL_SIMP_TAC std_ss []]);

val NSUM_GROUP = store_thm ("NSUM_GROUP",
 ``!f:'a->'b g s t.
        FINITE s /\ IMAGE f s SUBSET t
        ==> (nsum t (\y. nsum {x | x IN s /\ (f(x) = y)} g) = nsum s g)``,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [``f:'a->'b``, ``g:'a->num``, ``s:'a->bool``] NSUM_IMAGE_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC NSUM_SUPERSET THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC NSUM_EQ_0 THEN
  FULL_SIMP_TAC std_ss [GSPECIFICATION, IN_IMAGE] THEN METIS_TAC []);

val NSUM_SUBSET = store_thm ("NSUM_SUBSET",
 ``!u v f. FINITE u /\ FINITE v /\ (!x:'a. x IN (u DIFF v) ==> (f(x) = 0:num))
           ==> nsum u f <= nsum v f``,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [``f:'a->num``, ``u INTER v :'a->bool``] NSUM_UNION) THEN
  DISCH_THEN(fn th => MP_TAC(SPEC ``v DIFF u :'a->bool`` th) THEN
                      MP_TAC(SPEC ``u DIFF v :'a->bool`` th)) THEN
  REWRITE_TAC[SET_RULE ``(u INTER v) UNION (u DIFF v) = u``,
              SET_RULE ``(u INTER v) UNION (v DIFF u) = v``] THEN
  ASM_SIMP_TAC std_ss [FINITE_DIFF, FINITE_INTER] THEN
  KNOW_TAC ``DISJOINT (u INTER v) (u DIFF v) /\ DISJOINT (u INTER v) (v DIFF u)``
  THENL [SET_TAC[], ALL_TAC] THEN RW_TAC std_ss [] THEN
  ASM_SIMP_TAC std_ss [NSUM_EQ_0]);

val NSUM_SUBSET_SIMPLE = store_thm ("NSUM_SUBSET_SIMPLE",
 ``!u v f. FINITE v /\ u SUBSET v ==> nsum u f <= nsum v f``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NSUM_SUBSET THEN
  ASM_MESON_TAC[IN_DIFF, SUBSET_DEF, SUBSET_FINITE]);

val NSUM_LE_GEN = store_thm ("NSUM_LE_GEN",
 ``!f g s. (!x:'a. x IN s ==> f x <= g x) /\ FINITE {x | x IN s /\ ~(g x = 0:num)}
           ==> nsum s f <= nsum s g``,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM NSUM_SUPPORT] THEN
  REWRITE_TAC[support, NEUTRAL_ADD] THEN
  MATCH_MP_TAC LESS_EQ_TRANS THEN
  EXISTS_TAC ``nsum {x | x IN s /\ ~(g(x:'a) = 0:num)} f`` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_SUBSET THEN
    ASM_SIMP_TAC std_ss [GSPECIFICATION, IN_DIFF] THEN
    CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC[LE]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO]
      SUBSET_FINITE)) THEN
    SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN ASM_MESON_TAC[LE],
    MATCH_MP_TAC NSUM_LE THEN ASM_SIMP_TAC std_ss [GSPECIFICATION]]);

val NSUM_IMAGE_NONZERO = store_thm ("NSUM_IMAGE_NONZERO",
 ``!d:'b->num i:'a->'b s.
    FINITE s /\
    (!x y. x IN s /\ y IN s /\ ~(x = y) /\ (i x = i y) ==> (d(i x) = 0:num))
    ==> (nsum (IMAGE i s) d = nsum s (d o i))``,
  REWRITE_TAC[GSYM NEUTRAL_ADD, nsum] THEN
  MATCH_MP_TAC ITERATE_IMAGE_NONZERO THEN REWRITE_TAC[MONOIDAL_ADD]);

val NSUM_BIJECTION = store_thm ("NSUM_BIJECTION",
 ``!f p s:'a->bool.
                (!x. x IN s ==> p(x) IN s) /\
                (!y. y IN s ==> ?!x. x IN s /\ (p(x) = y))
                ==> (nsum s f = nsum s (f o p))``,
  REWRITE_TAC[nsum] THEN MATCH_MP_TAC ITERATE_BIJECTION THEN
  REWRITE_TAC[MONOIDAL_ADD]);

val NSUM_NSUM_PRODUCT = store_thm ("NSUM_NSUM_PRODUCT",
 ``!s:'a->bool t:'a->'b->bool x.
        FINITE s /\ (!i. i IN s ==> FINITE(t i))
        ==> (nsum s (\i. nsum (t i) (x i)) =
             nsum {i,j | i IN s /\ j IN t i} (\(i,j). x i j))``,
  REWRITE_TAC[nsum] THEN MATCH_MP_TAC ITERATE_ITERATE_PRODUCT THEN
  REWRITE_TAC[MONOIDAL_ADD]);

val NSUM_EQ_GENERAL = store_thm ("NSUM_EQ_GENERAL",
 ``!s:'a->bool t:'b->bool f g h.
        (!y. y IN t ==> ?!x. x IN s /\ (h(x) = y)) /\
        (!x. x IN s ==> h(x) IN t /\ (g(h x) = f x))
        ==> (nsum s f = nsum t g)``,
  REWRITE_TAC[nsum] THEN MATCH_MP_TAC ITERATE_EQ_GENERAL THEN
  REWRITE_TAC[MONOIDAL_ADD]);

val NSUM_EQ_GENERAL_INVERSES = store_thm ("NSUM_EQ_GENERAL_INVERSES",
 ``!s:'a->bool t:'b->bool f g h k.
        (!y. y IN t ==> k(y) IN s /\ (h(k y) = y)) /\
        (!x. x IN s ==> h(x) IN t /\ (k(h x) = x) /\ (g(h x) = f x))
        ==> (nsum s f = nsum t g)``,
  REWRITE_TAC[nsum] THEN MATCH_MP_TAC ITERATE_EQ_GENERAL_INVERSES THEN
  REWRITE_TAC[MONOIDAL_ADD]);

val NSUM_INJECTION = store_thm ("NSUM_INJECTION",
 ``!f p s. FINITE s /\
           (!x. x IN s ==> p x IN s) /\
           (!x y. x IN s /\ y IN s /\ (p x = p y) ==> (x = y))
           ==> (nsum s (f o p) = nsum s f)``,
  REWRITE_TAC[nsum] THEN MATCH_MP_TAC ITERATE_INJECTION THEN
  REWRITE_TAC[MONOIDAL_ADD]);

val NSUM_UNION_NONZERO = store_thm ("NSUM_UNION_NONZERO",
 ``!f s t. FINITE s /\ FINITE t /\ (!x. x IN s INTER t ==> (f(x) = 0:num))
           ==> (nsum (s UNION t) f = nsum s f + nsum t f)``,
  REWRITE_TAC[nsum, GSYM NEUTRAL_ADD] THEN
  MATCH_MP_TAC ITERATE_UNION_NONZERO THEN REWRITE_TAC[MONOIDAL_ADD]);

val NSUM_BIGUNION_NONZERO = store_thm ("NSUM_BIGUNION_NONZERO",
 ``!f s. FINITE s /\ (!t:'a->bool. t IN s ==> FINITE t) /\
         (!t1 t2 x. t1 IN s /\ t2 IN s /\ ~(t1 = t2) /\ x IN t1 /\ x IN t2
                    ==> (f x = 0))
         ==> (nsum (BIGUNION s) f = nsum s (\t. nsum t f))``,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] THEN GEN_TAC THEN
  KNOW_TAC ``((!(t:'a->bool). t IN s ==> FINITE t) /\
    (!t1 t2 x.
       t1 IN s /\ t2 IN s /\ t1 <> t2 /\ x IN t1 /\ x IN t2 ==>
       (f x = 0)) ==>
    (nsum (BIGUNION s) f = nsum s (\t. nsum t f))) =
    (\s. (!(t:'a->bool). t IN s ==> FINITE t) /\
    (!t1 t2 x.
       t1 IN s /\ t2 IN s /\ t1 <> t2 /\ x IN t1 /\ x IN t2 ==>
       (f x = 0)) ==>
    (nsum (BIGUNION s) f = nsum s (\t. nsum t f))) s `` THENL
  [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISCH_TAC THEN
  ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  REWRITE_TAC[BIGUNION_EMPTY, BIGUNION_INSERT, NSUM_CLAUSES, IN_INSERT] THEN
  SIMP_TAC std_ss [GSYM RIGHT_FORALL_IMP_THM] THEN
  MAP_EVERY X_GEN_TAC [``(s':('a->bool)->bool)``, ``t:'a->bool``] THEN
  DISCH_THEN(fn th => STRIP_TAC THEN MP_TAC th) THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC ``FINITE (s':('a->bool)->bool)`` THEN
  UNDISCH_TAC ``(t :'a -> bool) NOTIN (s' :('a -> bool) -> bool) `` THEN
  ONCE_REWRITE_TAC[AND_IMP_INTRO] THEN ASM_SIMP_TAC std_ss [NSUM_CLAUSES]
  THEN KNOW_TAC ``nsum (BIGUNION s') f = nsum s' (\t. nsum t f)`` THENL
  [METIS_TAC [], ALL_TAC] THEN GEN_REWR_TAC (LAND_CONV) [EQ_SYM_EQ]
  THEN DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN MATCH_MP_TAC NSUM_UNION_NONZERO THEN
  ASM_SIMP_TAC std_ss [FINITE_BIGUNION, IN_INTER, IN_BIGUNION] THEN
  ASM_MESON_TAC[]);

val NSUM_CASES = store_thm ("NSUM_CASES",
 ``!s P f g. FINITE s
             ==> (nsum s (\x:'a. if P x then f x else g x) =
                  nsum {x | x IN s /\ P x} f + nsum {x | x IN s /\ ~P x} g)``,
  REWRITE_TAC[nsum, GSYM NEUTRAL_ADD] THEN
  MATCH_MP_TAC ITERATE_CASES THEN REWRITE_TAC[MONOIDAL_ADD]);

val NSUM_CLOSED = store_thm ("NSUM_CLOSED",
 ``!P f:'a->num s.
        P(0) /\ (!x y. P x /\ P y ==> P(x + y)) /\ (!a. a IN s ==> P(f a))
        ==> P(nsum s f)``,
  REPEAT STRIP_TAC THEN MP_TAC(MATCH_MP ITERATE_CLOSED MONOIDAL_ADD) THEN
  DISCH_THEN(MP_TAC o SPEC ``P:num->bool``) THEN
  ASM_SIMP_TAC std_ss [NEUTRAL_ADD, GSYM nsum]);

val NSUM_ADD_NUMSEG = store_thm ("NSUM_ADD_NUMSEG",
 ``!f g m n. nsum{m..n} (\i. f(i) + g(i)) = nsum{m..n} f + nsum{m..n} g``,
  SIMP_TAC std_ss [NSUM_ADD, FINITE_NUMSEG]);

val NSUM_LE_NUMSEG = store_thm ("NSUM_LE_NUMSEG",
 ``!f g m n. (!i. m <= i /\ i <= n ==> f(i) <= g(i))
             ==> nsum{m..n} f <= nsum{m..n} g``,
  SIMP_TAC std_ss [NSUM_LE, FINITE_NUMSEG, IN_NUMSEG]);

val NSUM_EQ_NUMSEG = store_thm ("NSUM_EQ_NUMSEG",
 ``!f g m n. (!i. m <= i /\ i <= n ==> (f(i) = g(i)))
             ==> (nsum{m..n} f = nsum{m..n} g)``,
  MESON_TAC[NSUM_EQ, FINITE_NUMSEG, IN_NUMSEG]);

val NSUM_CONST_NUMSEG = store_thm ("NSUM_CONST_NUMSEG",
 ``!c m n. nsum{m..n} (\n. c) = ((n + 1:num) - m) * c``,
  SIMP_TAC std_ss [NSUM_CONST, FINITE_NUMSEG, CARD_NUMSEG]);

val NSUM_EQ_0_NUMSEG = store_thm ("NSUM_EQ_0_NUMSEG",
 ``!f m n. (!i. m <= i /\ i <= n ==> (f(i) = 0:num)) ==> (nsum{m..n} f = 0:num)``,
  SIMP_TAC std_ss [NSUM_EQ_0, IN_NUMSEG]);

val NSUM_EQ_0_IFF_NUMSEG = store_thm ("NSUM_EQ_0_IFF_NUMSEG",
 ``!f m n. (nsum {m..n} f = 0:num) <=> !i. m <= i /\ i <= n ==> (f i = 0:num)``,
  SIMP_TAC std_ss [NSUM_EQ_0_IFF, FINITE_NUMSEG, IN_NUMSEG]);

val NSUM_TRIV_NUMSEG = store_thm ("NSUM_TRIV_NUMSEG",
 ``!f m n. n < m ==> (nsum{m..n} f = 0:num)``,
  MESON_TAC[NSUM_EQ_0_NUMSEG, LESS_EQ_TRANS, NOT_LESS]);

val NSUM_SING_NUMSEG = store_thm ("NSUM_SING_NUMSEG",
 ``!f n. nsum{n..n} f = f(n)``,
  SIMP_TAC std_ss [NSUM_SING, NUMSEG_SING]);

val NSUM_CLAUSES_NUMSEG = store_thm ("NSUM_CLAUSES_NUMSEG",
 ``(!m. nsum{m..0} f = if m = 0:num then f 0 else 0) /\
   (!m n. nsum{m..SUC n} f = if m <= SUC n then nsum{m..n} f + f(SUC n)
                             else nsum{m..n} f)``,
  MP_TAC(MATCH_MP ITERATE_CLAUSES_NUMSEG MONOIDAL_ADD) THEN
  REWRITE_TAC[NEUTRAL_ADD, nsum]);

val NSUM_SWAP_NUMSEG = store_thm ("NSUM_SWAP_NUMSEG",
 ``!a b c d f.
     nsum{a..b} (\i. nsum{c..d} (f i)) =
     nsum{c..d} (\j. nsum{a..b} (\i. f i j))``,
  REPEAT GEN_TAC THEN MATCH_MP_TAC NSUM_SWAP THEN REWRITE_TAC[FINITE_NUMSEG]);

val NSUM_ADD_SPLIT = store_thm ("NSUM_ADD_SPLIT",
 ``!f m n p.
        m <= n + 1:num ==> (nsum {m..n+p} f = nsum{m..n} f + nsum{n+1..n+p} f)``,
  METIS_TAC [NUMSEG_ADD_SPLIT, NSUM_UNION, DISJOINT_NUMSEG, FINITE_NUMSEG,
           ARITH_PROVE ``x:num < x + 1:num``]);

val NSUM_OFFSET = store_thm ("NSUM_OFFSET",
 ``!p f m n. nsum{m+p..n+p} f = nsum{m..n} (\i. f(i + p))``,
  SIMP_TAC std_ss [NUMSEG_OFFSET_IMAGE, NSUM_IMAGE, EQ_ADD_RCANCEL, FINITE_NUMSEG] THEN
  SIMP_TAC std_ss [o_DEF]);

val NSUM_OFFSET_0 = store_thm ("NSUM_OFFSET_0",
 ``!f m n. m <= n ==> (nsum{m..n} f = nsum{0..n-m} (\i. f(i + m)))``,
  SIMP_TAC std_ss [GSYM NSUM_OFFSET, ADD_CLAUSES, SUB_ADD]);

val NSUM_CLAUSES_LEFT = store_thm ("NSUM_CLAUSES_LEFT",
 ``!f m n. m <= n ==> (nsum{m..n} f = f(m) + nsum{m+1..n} f)``,
  SIMP_TAC std_ss [GSYM NUMSEG_LREC, NSUM_CLAUSES, FINITE_NUMSEG, IN_NUMSEG] THEN
  ARITH_TAC);

val NSUM_CLAUSES_RIGHT = store_thm ("NSUM_CLAUSES_RIGHT",
 ``!f m n. 0:num < n /\ m <= n ==> (nsum{m..n} f = nsum{m..n-1} f + f(n))``,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  SIMP_TAC std_ss [LESS_REFL, NSUM_CLAUSES_NUMSEG, SUC_SUB1]);

val NSUM_PAIR = store_thm ("NSUM_PAIR",
 ``!f m n. nsum{2*m..2*n+1} f = nsum{m..n} (\i. f(2*i) + f(2*i+1:num))``,
  MP_TAC(MATCH_MP ITERATE_PAIR MONOIDAL_ADD) THEN
  REWRITE_TAC[nsum, NEUTRAL_ADD]);

val MOD_NSUM_MOD = store_thm ("MOD_NSUM_MOD",
 ``!f:'a->num n s.
        FINITE s /\ ~(n = 0:num)
        ==> ((nsum s f) MOD n = nsum s (\i. f(i) MOD n) MOD n)``,
  GEN_TAC THEN GEN_TAC THEN
  ASM_CASES_TAC ``n = 0:num`` THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN KNOW_TAC ``(nsum s f MOD n = nsum s (\i. f i MOD n) MOD n) =
                     (\s. (nsum s f MOD n = nsum s (\i. f i MOD n) MOD n))s``
  THENL [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISCH_TAC THEN
  ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FINITE_INDUCT THEN
  BETA_TAC THEN FULL_SIMP_TAC std_ss [NSUM_CLAUSES, NOT_ZERO_LT_ZERO] THEN
  REPEAT STRIP_TAC THEN ASSUME_TAC MOD_PLUS THEN
  POP_ASSUM (MP_TAC o Q.SPEC `n`) THEN FULL_SIMP_TAC std_ss [] THEN DISCH_TAC
  THEN POP_ASSUM (MP_TAC o Q.SPECL [`f e`, `nsum s f`]) THEN ASM_REWRITE_TAC []
  THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FULL_SIMP_TAC std_ss [MOD_PLUS, ADD_MOD]);

val MOD_NSUM_MOD_NUMSEG = store_thm ("MOD_NSUM_MOD_NUMSEG",
 ``!f a b n.
        ~(n = 0:num)
        ==> ((nsum{a..b} f) MOD n = nsum{a..b} (\i. f i MOD n) MOD n)``,
  METIS_TAC[MOD_NSUM_MOD, FINITE_NUMSEG]);

val NSUM_CONG = store_thm
  ("NSUM_CONG",
  ``(!f g s.   (!x. x IN s ==> (f(x) = g(x)))
           ==> (nsum s (\i. f(i)) = nsum s g)) /\
    (!f g a b. (!i. a <= i /\ i <= b ==> (f(i) = g(i)))
           ==> (nsum{a..b} (\i. f(i)) = nsum{a..b} g)) /\
    (!f g p.   (!x. p x ==> (f x = g x))
           ==> (nsum {y | p y} (\i. f(i)) = nsum {y | p y} g))``,
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC NSUM_EQ
 >> ASM_SIMP_TAC std_ss [GSPECIFICATION, IN_NUMSEG]);

(* ------------------------------------------------------------------------- *)
(* Thanks to finite sums, we can express cardinality of finite union.        *)
(* ------------------------------------------------------------------------- *)

val CARD_BIGUNION = store_thm ("CARD_BIGUNION",
 ``!s:('a->bool)->bool.
        FINITE s /\ (!t. t IN s ==> FINITE t) /\
        (!t u. t IN s /\ u IN s /\ ~(t = u) ==> (t INTER u = {}))
        ==> (CARD(BIGUNION s) = nsum s CARD)``,
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] THEN GEN_TAC THEN
  KNOW_TAC ``((!t. t IN s ==> FINITE t) /\
    (!t u. t IN s /\ u IN s /\ t <> u ==> (t INTER u = {})) ==>
    (CARD (BIGUNION s) = nsum s CARD)) =
    (\s. (!t. t IN s ==> FINITE t) /\
    (!t u. t IN s /\ u IN s /\ t <> u ==> (t INTER u = {})) ==>
    (CARD (BIGUNION s) = nsum s CARD)) (s:('a->bool)->bool)`` THENL
  [FULL_SIMP_TAC std_ss [], DISC_RW_KILL THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  REWRITE_TAC[BIGUNION_EMPTY, BIGUNION_INSERT, NOT_IN_EMPTY, IN_INSERT] THEN
  REWRITE_TAC[CARD_DEF, NSUM_CLAUSES] THEN
  SIMP_TAC std_ss [GSYM RIGHT_FORALL_IMP_THM] THEN
  MAP_EVERY X_GEN_TAC [``f:('a->bool)->bool``, ``t:'a->bool``] THEN
  DISCH_THEN(fn th => STRIP_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC std_ss [NSUM_CLAUSES] THEN REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC std_ss [] THEN
  UNDISCH_TAC ``CARD (BIGUNION f) = nsum f CARD`` THEN
  GEN_REWR_TAC LAND_CONV [EQ_SYM_EQ] THEN RW_TAC std_ss [] THEN
  MATCH_MP_TAC (GSYM CARD_UNION_EQ) THEN FULL_SIMP_TAC std_ss [] THEN
  CONJ_TAC THENL [METIS_TAC [FINITE_BIGUNION, FINITE_UNION], ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN
  KNOW_TAC ``(!s t. t INTER BIGUNION s = BIGUNION {t INTER x | x IN s})`` THENL
  [ONCE_REWRITE_TAC[EXTENSION] THEN
  SIMP_TAC std_ss [IN_BIGUNION, GSPECIFICATION, IN_INTER] THEN
  MESON_TAC[IN_INTER], ALL_TAC] THEN
  DISC_RW_KILL THEN
  SIMP_TAC std_ss [SET_RULE ``!s. (BIGUNION s = {}) <=> !t. t IN s ==> (t = {})``, GSPECIFICATION] THEN
  METIS_TAC[]]);

(* ------------------------------------------------------------------------- *)
(* Sums of real numbers.                                                     *)
(* ------------------------------------------------------------------------- *)

val sum_def = new_definition ("sum_def",
  ``(Sum :('a->bool)->('a->real)->real) = iterate (+)``);

val _ = overload_on ("sum",``Sum``);

val NEUTRAL_REAL_ADD = store_thm ("NEUTRAL_REAL_ADD",
  ``neutral((+):real->real->real) = &0``,
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  MESON_TAC[REAL_ADD_LID, REAL_ADD_RID]);

val NEUTRAL_REAL_MUL = store_thm ("NEUTRAL_REAL_MUL",
 ``neutral(( * ):real->real->real) = &1``,
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  MESON_TAC[REAL_MUL_LID, REAL_MUL_RID]);

val MONOIDAL_REAL_ADD = store_thm ("MONOIDAL_REAL_ADD",
 ``monoidal((+):real->real->real)``,
  REWRITE_TAC[monoidal, NEUTRAL_REAL_ADD] THEN REAL_ARITH_TAC);

val MONOIDAL_REAL_MUL = store_thm ("MONOIDAL_REAL_MUL",
 ``monoidal(( * ):real->real->real)``,
  REWRITE_TAC[monoidal, NEUTRAL_REAL_MUL] THEN REAL_ARITH_TAC);

val SUM_DEGENERATE = store_thm ("SUM_DEGENERATE",
 ``!f s. ~(FINITE {x | x IN s /\ ~(f x = &0)}) ==> (sum s f = &0)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[sum_def] THEN
  SIMP_TAC std_ss [iterate, support, NEUTRAL_REAL_ADD]);

val SUM_CLAUSES = store_thm ("SUM_CLAUSES",
 ``(!f. sum {} f = &0) /\
   (!x f s. FINITE(s)
            ==> ((sum (x INSERT s) f =
                 if x IN s then sum s f else f(x) + sum s f)))``,
  REWRITE_TAC[sum_def, GSYM NEUTRAL_REAL_ADD] THEN
  KNOW_TAC ``monoidal ((+):real->real->real)`` THENL
  [REWRITE_TAC[MONOIDAL_REAL_ADD], METIS_TAC [ITERATE_CLAUSES]]);

val SUM_UNION = store_thm ("SUM_UNION",
 ``!f s t. FINITE s /\ FINITE t /\ DISJOINT s t
           ==> ((sum (s UNION t) f = sum s f + sum t f))``,
  SIMP_TAC std_ss [sum_def, ITERATE_UNION, MONOIDAL_REAL_ADD]);

(* cf. realTheory.SUM_DIFF *)
Theorem SUM_DIFF' : (* was: SUM_DIFF *)
   !f s t. FINITE s /\ t SUBSET s ==> (sum (s DIFF t) f = sum s f - sum t f)
Proof
  SIMP_TAC std_ss [REAL_EQ_SUB_LADD, sum_def, ITERATE_DIFF, MONOIDAL_REAL_ADD]
QED
val SUM_DIFF = SUM_DIFF';

val SUM_INCL_EXCL = store_thm ("SUM_INCL_EXCL",
 ``!s t (f:'a->real).
     FINITE s /\ FINITE t
     ==> (sum s f + sum t f = sum (s UNION t) f + sum (s INTER t) f)``,
  REWRITE_TAC[sum_def, GSYM NEUTRAL_REAL_ADD] THEN
  MATCH_MP_TAC ITERATE_INCL_EXCL THEN REWRITE_TAC[MONOIDAL_REAL_ADD]);

val SUM_SUPPORT = store_thm ("SUM_SUPPORT",
 ``!f s. sum (support (+) f s) f = sum s f``,
  SIMP_TAC std_ss [sum_def, iterate, SUPPORT_SUPPORT]);

(* cf. realTheory.SUM_ADD *)
Theorem SUM_ADD' : (* was: SUM_ADD *)
   !f g s. FINITE s ==> (sum s (\x. f(x) + g(x)) = sum s f + sum s g)
Proof
  SIMP_TAC std_ss [sum_def, ITERATE_OP, MONOIDAL_REAL_ADD]
QED
val SUM_ADD = SUM_ADD';

Theorem SUM_ADD_COUNT :
    !f g n. sum (count n) (\x. f(x) + g(x)) = sum (count n) f + sum (count n) g
Proof
    rpt GEN_TAC
 >> MATCH_MP_TAC SUM_ADD'
 >> REWRITE_TAC [FINITE_COUNT]
QED

val SUM_ADD_GEN = store_thm ("SUM_ADD_GEN",
 ``!f g s.
       FINITE {x | x IN s /\ ~(f x = &0)} /\ FINITE {x | x IN s /\ ~(g x = &0)}
       ==> (sum s (\x. f x + g x) = sum s f + sum s g)``,
  REWRITE_TAC[GSYM NEUTRAL_REAL_ADD, GSYM support, sum_def] THEN
  MATCH_MP_TAC ITERATE_OP_GEN THEN ACCEPT_TAC MONOIDAL_REAL_ADD);

(* cf. realTheory.SUM_EQ_0 *)
Theorem SUM_EQ_0' : (* was: SUM_EQ_0 *)
   !f s. (!x:'a. x IN s ==> (f(x) = &0)) ==> (sum s f = &0)
Proof
  REWRITE_TAC[sum_def, GSYM NEUTRAL_REAL_ADD] THEN
  SIMP_TAC std_ss [ITERATE_EQ_NEUTRAL, MONOIDAL_REAL_ADD]
QED
val SUM_EQ_0 = SUM_EQ_0';

(* cf. realTheory.SUM_0 *)
Theorem SUM_0' : (* was: SUM_0 *)
   !s:'a->bool. sum s (\n. &0) = &0
Proof
  SIMP_TAC std_ss [SUM_EQ_0]
QED
val SUM_0 = SUM_0';

val SUM_LMUL = store_thm ("SUM_LMUL",
 ``!f c s:'a->bool. sum s (\x. c * f(x)) = c * sum s f``,
  REPEAT GEN_TAC THEN ASM_CASES_TAC ``c = 0:real`` THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO, SUM_0] THEN REWRITE_TAC[sum_def] THEN
  ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  SUBGOAL_THEN ``support (+) (\x:'a. (c:real) * f(x)) s = support (+) f s`` SUBST1_TAC
  THENL [ASM_SIMP_TAC std_ss [support, REAL_ENTIRE, NEUTRAL_REAL_ADD], ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[NEUTRAL_REAL_ADD, REAL_MUL_RZERO] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(``support (+) f (s:'a->bool)``,``t:'a->bool``) THEN
  REWRITE_TAC[GSYM sum_def] THEN Q.ABBREV_TAC `ss = support (+) f s` THEN
  KNOW_TAC ``!ss. ((sum ss (\(x :'a). (c :real) * (f :'a -> real) x) = c * sum ss f)) =
  (\ss. (sum ss (\(x :'a). (c :real) * (f :'a -> real) x) = c * sum ss f))ss`` THENL
  [FULL_SIMP_TAC std_ss [], DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [SUM_CLAUSES, REAL_MUL_RZERO, REAL_MUL_LZERO,
           REAL_ADD_LDISTRIB]]);

val SUM_RMUL = store_thm ("SUM_RMUL",
 ``!f c s:'a->bool. sum s (\x. f(x) * c) = sum s f * c``,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[SUM_LMUL]);

(* cf. realTheory.SUM_NEG *)
Theorem SUM_NEG' : (* was: SUM_NEG *)
   !f s. sum s (\x. -(f(x))) = -(sum s f)
Proof
  ONCE_REWRITE_TAC[REAL_ARITH ``-x = -(1:real) * x``] THEN
  SIMP_TAC std_ss [SUM_LMUL]
QED
val SUM_NEG = SUM_NEG';

(* cf. realTheory.SUM_SUB *)
Theorem SUM_SUB' : (* was: SUM_SUB *)
   !f g s. FINITE s ==> (sum s (\x. f(x) - g(x)) = sum s f - sum s g)
Proof
  ONCE_REWRITE_TAC[real_sub] THEN SIMP_TAC std_ss [SUM_NEG, SUM_ADD]
QED
val SUM_SUB = SUM_SUB';

(* cf. realTheory.SUM_LE *)
Theorem SUM_LE' : (* was: SUM_LE, SUM_MONO_LE *)
   !f g s. FINITE(s) /\ (!x. x IN s ==> f(x) <= g(x)) ==> sum s f <= sum s g
Proof
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] THEN REPEAT GEN_TAC THEN
  KNOW_TAC ``((!(x :'a). x IN s ==> (f :'a -> real) x <= (g :'a -> real) x) ==>
    sum s f <= sum s g) = (\(s:'a->bool). (!(x :'a). x IN s ==>
    (f :'a -> real) x <= (g :'a -> real) x) ==> sum s f <= sum s g) s`` THENL
  [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [SUM_CLAUSES, REAL_LE_REFL, REAL_LE_ADD2, IN_INSERT]
QED
val SUM_LE = SUM_LE';

(* cf. realTheory.SUM_LT *)
Theorem SUM_LT' : (* was: SUM_LT, SUM_MONO_LT *)
   !f g s:'a->bool.
        FINITE(s) /\ (!x. x IN s ==> f(x) <= g(x)) /\
        (?x. x IN s /\ f(x) < g(x))
         ==> sum s f < sum s g
Proof
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN ``a:'a`` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN ``s = (a:'a) INSERT (s DELETE a)`` SUBST1_TAC THENL
   [UNDISCH_TAC ``a:'a IN s`` THEN SIMP_TAC std_ss [INSERT_DELETE], ALL_TAC]
  THEN ASM_SIMP_TAC std_ss [SUM_CLAUSES, FINITE_DELETE, IN_DELETE] THEN
  ASM_SIMP_TAC std_ss [REAL_LTE_ADD2, SUM_LE, IN_DELETE, FINITE_DELETE]
QED
val SUM_LT = SUM_LT';

val SUM_LT_ALL = store_thm ("SUM_LT_ALL",
 ``!f g s. FINITE s /\ ~(s = {}) /\ (!x. x IN s ==> f(x) < g(x))
           ==> sum s f < sum s g``,
  MESON_TAC[MEMBER_NOT_EMPTY, REAL_LT_IMP_LE, SUM_LT]);

val SUM_POS_LT = store_thm ("SUM_POS_LT",
 ``!f s:'a->bool.
        FINITE s /\
        (!x. x IN s ==> &0 <= f x) /\
        (?x. x IN s /\ &0 < f x)
        ==> &0 < sum s f``,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC ``sum (s:'a->bool) (\i. 0:real)`` THEN CONJ_TAC THENL
   [REWRITE_TAC[SUM_0, REAL_LE_REFL], MATCH_MP_TAC SUM_LT] THEN
  ASM_MESON_TAC[]);

val SUM_POS_LT_ALL = store_thm ("SUM_POS_LT_ALL",
 ``!s f:'a->real.
     FINITE s /\ ~(s = {}) /\ (!i. i IN s ==> (0:real) < f i)
       ==> (0:real) < sum s f``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_POS_LT THEN
  ASM_MESON_TAC[MEMBER_NOT_EMPTY, REAL_LT_IMP_LE]);

(* cf. realTheory.SUM_EQ *)
Theorem SUM_EQ' : (* was: SUM_EQ *)
   !f g s. (!x. x IN s ==> (f x = g x)) ==> (sum s f = sum s g)
Proof
  REWRITE_TAC[sum_def] THEN
  MATCH_MP_TAC ITERATE_EQ THEN REWRITE_TAC[MONOIDAL_REAL_ADD]
QED
val SUM_EQ = SUM_EQ';

Theorem SUM_EQ_COUNT :
    !f g n. (!i. i < n ==> (f i = g i)) ==> (sum (count n) f = sum (count n) g)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC SUM_EQ' >> rw []
QED

(* cf. realTheory.SUM_ABS *)
Theorem SUM_ABS' : (* was: SUM_ABS *)
   !f s. FINITE(s) ==> abs(sum s f) <= sum s (\x. abs(f x))
Proof
  REPEAT GEN_TAC THEN
  KNOW_TAC ``(abs(sum s f) <= sum s (\x. abs(f x))) =
  (\s. abs(sum s f) <= sum s (\x. abs(f x))) s`` THENL
  [FULL_SIMP_TAC std_ss [], DISCH_TAC THEN ONCE_ASM_REWRITE_TAC []
  THEN MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [SUM_CLAUSES, ABS_N, REAL_LE_REFL,
    REAL_ARITH ``abs(a) <= b ==> abs(x + a) <= abs(x) + b:real``]]
QED
val SUM_ABS = SUM_ABS';

(* cf. realTheory.SUN_ABS_LE *)
Theorem SUM_ABS_LE' : (* was: SUM_ABS_LE *)
   !f:'a->real g s.
        FINITE s /\ (!x. x IN s ==> abs(f x) <= g x)
        ==> abs(sum s f) <= sum s g
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC ``sum s (\x:'a. abs(f x))`` THEN
  ASM_SIMP_TAC std_ss [SUM_ABS] THEN MATCH_MP_TAC SUM_LE THEN
  ASM_SIMP_TAC std_ss []
QED
val SUM_ABS_LE = SUM_ABS_LE';

val SUM_CONST = store_thm ("SUM_CONST",
 ``!c s. FINITE s ==> (sum s (\n. c) = &(CARD s) * c)``,
  REPEAT GEN_TAC THEN KNOW_TAC ``((sum s (\n. c) = &CARD s * c)) =
  (\s. (sum s (\n. c) = &CARD s * c)) s`` THENL [FULL_SIMP_TAC std_ss [],
  DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [SUM_CLAUSES, CARD_DEF, GSYM REAL_OF_NUM_SUC] THEN
  REPEAT STRIP_TAC THEN REAL_ARITH_TAC]);

val SUM_POS_LE = store_thm ("SUM_POS_LE",
 ``!s:'a->bool. (!x. x IN s ==> (0:real) <= f x) ==> (0:real) <= sum s f``,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC ``FINITE {x:'a | x IN s /\ ~(f x = (0:real))}`` THEN
  ASM_SIMP_TAC std_ss [SUM_DEGENERATE, REAL_LE_REFL] THEN
  ONCE_REWRITE_TAC[GSYM SUM_SUPPORT] THEN
  REWRITE_TAC[support, NEUTRAL_REAL_ADD] THEN
  MP_TAC(ISPECL [``\x:'a. (0:real)``, ``f:'a->real``,
  ``{x:'a | x IN s /\ ~(f x = (0:real))}``] SUM_LE) THEN
  ASM_SIMP_TAC std_ss [SUM_0, GSPECIFICATION]);

val SUM_POS_BOUND = store_thm ("SUM_POS_BOUND",
 ``!f b s. FINITE s /\ (!x. x IN s ==> (0:real) <= f x) /\ sum s f <= b
           ==> !x:'a. x IN s ==> f x <= b``,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM AND_IMP_INTRO] THEN
  KNOW_TAC ``((!x. x IN s ==> 0 <= f x) ==>
    sum s f <= b ==> !x. x IN s ==> f x <= b) =
        (\s. (!x. x IN s ==> 0 <= f x) ==>
    sum s f <= b ==> !x. x IN s ==> f x <= b) s`` THENL
  [FULL_SIMP_TAC std_ss [], DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [SUM_CLAUSES, NOT_IN_EMPTY, IN_INSERT] THEN
  MESON_TAC[SUM_POS_LE, REAL_ARITH
  ``(0:real) <= x /\ (0:real) <= y /\ x + y <= b ==> x <= b /\ y <= b``]]);

val SUM_POS_EQ_0 = store_thm ("SUM_POS_EQ_0",
 ``!f s. FINITE s /\ (!x. x IN s ==> (0:real) <= f x) /\ (sum s f = (0:real))
         ==> !x. x IN s ==> (f x = (0:real))``,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  MESON_TAC[SUM_POS_BOUND, SUM_POS_LE]);

val SUM_ZERO_EXISTS = store_thm ("SUM_ZERO_EXISTS",
 ``!(u:'a->real) s.
         FINITE s /\ (sum s u = (0:real))
         ==> (!i. i IN s ==> (u i = (0:real))) \/
             (?j k. j IN s /\ u j < (0:real) /\ k IN s /\ u k > (0:real))``,
  REPEAT STRIP_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (METIS [REAL_ARITH ``((0:real) <= -u <=> ~(u > (0:real))) /\
    ((0:real) <= u <=> ~(u < (0:real)))``]
     ``(?j k:'a. j IN s /\ u j < (0:real) /\ k IN s /\ u k > (0:real)) \/
      (!i. i IN s ==> (0:real) <= u i) \/ (!i. i IN s ==> (0:real) <= -(u i))``) THEN
  ASM_REWRITE_TAC[] THEN DISJ1_TAC THENL
   [ALL_TAC, ONCE_REWRITE_TAC[GSYM REAL_NEG_EQ0]] THENL
  [MATCH_MP_TAC SUM_POS_EQ_0 THEN ASM_REWRITE_TAC[SUM_NEG, REAL_NEG_0], ALL_TAC]
  THEN GEN_TAC THEN KNOW_TAC ``?(f:'a->real). !i. -(u:'a->real) i = f i`` THENL
  [EXISTS_TAC ``(\x. -(u:'a->real) x)`` THEN SIMP_TAC real_ss [], ALL_TAC] THEN
  STRIP_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUM_POS_EQ_0 THEN
  FULL_SIMP_TAC std_ss [] THEN UNDISCH_TAC ``sum s u = 0`` THEN
  GEN_REWR_TAC LAND_CONV [EQ_SYM_EQ] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC [GSYM REAL_NEG_EQ0] THEN ONCE_REWRITE_TAC [GSYM SUM_NEG]
  THEN ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUM_EQ THEN BETA_TAC THEN
  METIS_TAC [REAL_NEG_EQ]);

val SUM_DELETE = store_thm ("SUM_DELETE",
 ``!f s a. FINITE s /\ a IN s ==> (sum (s DELETE a) f = sum s f - f(a))``,
  SIMP_TAC std_ss [REAL_ARITH ``(y = z - x) <=> (x + y = z:real)``, sum_def, ITERATE_DELETE,
           MONOIDAL_REAL_ADD]);

val SUM_DELETE_CASES = store_thm ("SUM_DELETE_CASES",
 ``!f s a. FINITE s
           ==> (sum (s DELETE a) f = if a IN s then sum s f - f(a)
                                    else sum s f)``,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  METIS_TAC [DELETE_NON_ELEMENT, SUM_DELETE]);

val SUM_SING = store_thm ("SUM_SING",
 ``!f x. sum {x} f = f(x)``,
  SIMP_TAC std_ss [SUM_CLAUSES, FINITE_EMPTY, FINITE_INSERT, NOT_IN_EMPTY, REAL_ADD_RID]);

val SUM_DELTA = store_thm ("SUM_DELTA",
 ``!s a. sum s (\x. if x = a:'a then b else &0) = if a IN s then b else &0``,
  REWRITE_TAC[sum_def, GSYM NEUTRAL_REAL_ADD] THEN
  SIMP_TAC std_ss [ITERATE_DELTA, MONOIDAL_REAL_ADD]);

val SUM_SWAP = store_thm ("SUM_SWAP",
 ``!f:'a->'b->real s t.
      FINITE(s) /\ FINITE(t)
      ==> ((sum s (\i. sum t (f i)) = sum t (\j. sum s (\i. f i j))))``,
  GEN_TAC THEN REWRITE_TAC[GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN KNOW_TAC ``(FINITE (t:'b->bool) ==>
    (sum s (\i. sum t (f i)) = sum t (\j. sum s (\i. f i j)))) = (\s. FINITE t ==>
    (sum s (\i. sum t (f i)) = sum t (\j. sum s (\i. f i j)))) (s:'a->bool)`` THENL
  [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISCH_TAC THEN ONCE_ASM_REWRITE_TAC []
  THEN MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  FULL_SIMP_TAC std_ss [SUM_CLAUSES, SUM_0] THEN METIS_TAC [SUM_ADD, ETA_AX]);

Theorem SUM_SWAP_COUNT :
   !(f:num->num->real) m n.
      sum (count m) (\i. sum (count n) (f i)) = sum (count n) (\j. sum (count m) (\i. f i j))
Proof
    rpt GEN_TAC
 >> MATCH_MP_TAC SUM_SWAP
 >> REWRITE_TAC [FINITE_COUNT]
QED

val SUM_IMAGE = store_thm ("SUM_IMAGE",
 ``!f g s. (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> (sum (IMAGE f s) g = sum s (g o f))``,
  REWRITE_TAC[sum_def, GSYM NEUTRAL_REAL_ADD] THEN
  MATCH_MP_TAC ITERATE_IMAGE THEN REWRITE_TAC[MONOIDAL_REAL_ADD]);

val SUM_SUPERSET = store_thm ("SUM_SUPERSET",
 ``!f:'a->real u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = (0:real)))
        ==> (sum v f = sum u f)``,
  SIMP_TAC std_ss [sum_def, GSYM NEUTRAL_REAL_ADD, ITERATE_SUPERSET, MONOIDAL_REAL_ADD]);

val SUM_UNION_RZERO = store_thm ("SUM_UNION_RZERO",
 ``!f:'a->real u v.
        FINITE u /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = (0:real)))
        ==> (sum (u UNION v) f = sum u f)``,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN ``u UNION v = u UNION (v DIFF u)``
  ASSUME_TAC THENL [SET_TAC [], ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[lemma] THEN
  MATCH_MP_TAC SUM_SUPERSET THEN
  ASM_MESON_TAC[IN_UNION, IN_DIFF, SUBSET_DEF]);

val SUM_UNION_LZERO = store_thm ("SUM_UNION_LZERO",
 ``!f:'a->real u v.
        FINITE v /\ (!x. x IN u /\ ~(x IN v) ==> (f(x) = (0:real)))
        ==> (sum (u UNION v) f = sum v f)``,
  MESON_TAC[SUM_UNION_RZERO, UNION_COMM]);

val SUM_RESTRICT = store_thm ("SUM_RESTRICT",
 ``!f s. FINITE s ==> (sum s (\x. if x IN s then f(x) else (0:real)) = sum s f)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC std_ss []);

(* cf. realTheory.SUM_BOUND *)
Theorem SUM_BOUND' : (* was: SUM_BOUND *)
   !s f b. FINITE s /\ (!x:'a. x IN s ==> f(x) <= b)
           ==> sum s f <= &(CARD s) * b
Proof
  SIMP_TAC std_ss [GSYM SUM_CONST, SUM_LE]
QED
Theorem SUM_BOUND[local] = SUM_BOUND'

val SUM_BOUND_GEN = store_thm ("SUM_BOUND_GEN",
 ``!s f b. FINITE s /\ ~(s = {}) /\ (!x:'a. x IN s ==> f(x) <= b / &(CARD s))
           ==> sum s f <= b``,
  MESON_TAC[SUM_BOUND, REAL_DIV_LMUL, REAL_OF_NUM_EQ, CARD_EQ_0]);

val SUM_ABS_BOUND = store_thm ("SUM_ABS_BOUND",
 ``!s f b. FINITE s /\ (!x:'a. x IN s ==> abs(f(x)) <= b)
           ==> abs(sum s f) <= &(CARD s) * b``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC ``sum s (\x:'a. abs(f x))`` THEN
  ASM_SIMP_TAC std_ss [SUM_BOUND, SUM_ABS]);

val SUM_BOUND_LT = store_thm ("SUM_BOUND_LT",
 ``!s f b. FINITE s /\ (!x:'a. x IN s ==> f x <= b) /\ (?x. x IN s /\ f x < b)
           ==> sum s f < &(CARD s) * b``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC ``sum s (\x:'a. b)`` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LT THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[],
    ASM_SIMP_TAC std_ss [SUM_CONST, REAL_LE_REFL]]);

val SUM_BOUND_LT_ALL = store_thm ("SUM_BOUND_LT_ALL",
 ``!s f b. FINITE s /\ ~(s = {}) /\ (!x. x IN s ==> f(x) < b)
           ==> sum s f <  &(CARD s) * b``,
  MESON_TAC[MEMBER_NOT_EMPTY, REAL_LT_IMP_LE, SUM_BOUND_LT]);

val SUM_BOUND_LT_GEN = store_thm ("SUM_BOUND_LT_GEN",
 ``!s f b. FINITE s /\ ~(s = {}) /\ (!x:'a. x IN s ==> f(x) < b / &(CARD s))
           ==> sum s f < b``,
  MESON_TAC[SUM_BOUND_LT_ALL, REAL_DIV_LMUL, REAL_OF_NUM_EQ, CARD_EQ_0]);

val SUM_UNION_EQ = store_thm ("SUM_UNION_EQ",
 ``!s t u. FINITE u /\ (s INTER t = {}) /\ (s UNION t = u)
           ==> (sum s f + sum t f = sum u f)``,
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN GEN_REWR_TAC LAND_CONV [EQ_SYM_EQ]
  THEN GEN_REWR_TAC RAND_CONV [EQ_SYM_EQ] THEN DISCH_TAC THEN
  ONCE_ASM_REWRITE_TAC [] THEN
  METIS_TAC[SUM_UNION, DISJOINT_DEF, FINITE_UNION]);

val SUM_EQ_SUPERSET = store_thm ("SUM_EQ_SUPERSET",
 ``!f s t:'a->bool.
        FINITE t /\ t SUBSET s /\
        (!x. x IN t ==> (f x = g x)) /\
        (!x. x IN s /\ ~(x IN t) ==> (f(x) = &0))
        ==> (sum s f = sum t g)``,
  MESON_TAC[SUM_SUPERSET, SUM_EQ]);

val SUM_RESTRICT_SET = store_thm ("SUM_RESTRICT_SET",
 ``!P s f. sum {x | x IN s /\ P x} f = sum s (\x. if P x then f x else (0:real))``,
  ONCE_REWRITE_TAC[GSYM SUM_SUPPORT] THEN
  SIMP_TAC std_ss [support, NEUTRAL_REAL_ADD, GSPECIFICATION] THEN
  REWRITE_TAC[METIS [] ``~((if P x then f x else a) = a) <=> P x /\ ~(f x = a)``,
              GSYM CONJ_ASSOC] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_EQ THEN SIMP_TAC std_ss [GSPECIFICATION]);

val SUM_SUM_RESTRICT = store_thm ("SUM_SUM_RESTRICT",
 ``!R f s t.
        FINITE s /\ FINITE t
        ==> (sum s (\x. sum {y | y IN t /\ R x y} (\y. f x y)) =
             sum t (\y. sum {x | x IN s /\ R x y} (\x. f x y)))``,
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [SUM_RESTRICT_SET] THEN ASSUME_TAC SUM_SWAP
  THEN POP_ASSUM (MP_TAC o Q.SPECL [`(\x y. if R x y then f x y else 0)`,
  `s`, `t`]) THEN FULL_SIMP_TAC std_ss []);

val CARD_EQ_SUM = store_thm ("CARD_EQ_SUM",
 ``!s. FINITE s ==> (&(CARD s) = sum s (\x. (1:real)))``,
  SIMP_TAC std_ss [SUM_CONST, REAL_MUL_RID]);

val SUM_MULTICOUNT_GEN = store_thm ("SUM_MULTICOUNT_GEN",
 ``!R:'a->'b->bool s t k.
        FINITE s /\ FINITE t /\
        (!j. j IN t ==> (CARD {i | i IN s /\ R i j} = k(j)))
        ==> (sum s (\i. &(CARD {j | j IN t /\ R i j})) =
             sum t (\i. &(k i)))``,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC ``sum s (\i:'a. sum {j:'b | j IN t /\ R i j} (\j. (1:real)))`` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC std_ss [CARD_EQ_SUM, FINITE_RESTRICT],
    ASSUME_TAC SUM_SUM_RESTRICT THEN POP_ASSUM (MP_TAC o Q.SPEC `R`)
    THEN FULL_SIMP_TAC std_ss [] THEN DISCH_TAC THEN MATCH_MP_TAC SUM_EQ
    THEN ASM_SIMP_TAC std_ss [SUM_CONST, FINITE_RESTRICT] THEN
    REWRITE_TAC[REAL_MUL_RID]]);

val SUM_MULTICOUNT = store_thm ("SUM_MULTICOUNT",
 ``!R:'a->'b->bool s t k.
        FINITE s /\ FINITE t /\
        (!j. j IN t ==> (CARD {i | i IN s /\ R i j} = k))
        ==> (sum s (\i. &(CARD {j | j IN t /\ R i j})) = &(k * CARD t))``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC ``sum t (\i:'b. &k)`` THEN CONJ_TAC THENL
   [KNOW_TAC ``?j. !i:'b. &k = &(j i):real`` THENL
  [EXISTS_TAC ``(\i:'b. k:num)`` THEN METIS_TAC [], ALL_TAC] THEN
  STRIP_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUM_MULTICOUNT_GEN
  THEN FULL_SIMP_TAC std_ss [REAL_OF_NUM_EQ],
  ASM_SIMP_TAC std_ss [SUM_CONST, REAL_OF_NUM_MUL] THEN METIS_TAC[MULT_SYM, MULT_ASSOC]]);

val SUM_IMAGE_GEN = store_thm ("SUM_IMAGE_GEN",
 ``!f:'a->'b g s.
        FINITE s
        ==> (sum s g =
             sum (IMAGE f s) (\y. sum {x | x IN s /\ (f(x) = y)} g))``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   ``sum s (\x:'a. sum {y:'b | y IN IMAGE f s /\ (f x = y)} (\y. g x))`` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC ``x:'a`` THEN
    DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN ``{y | y IN IMAGE (f:'a->'b) s /\ (f x = y)} = {(f x)}``
     (fn th => REWRITE_TAC[th, SUM_SING, o_THM]) THEN
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_SING, IN_IMAGE] THEN
    ASM_MESON_TAC[], GEN_REWR_TAC (funpow 2 RAND_CONV o ABS_CONV o RAND_CONV)
     [GSYM ETA_AX] THEN KNOW_TAC ``FINITE (IMAGE (f:'a->'b) s)`` THENL
    [METIS_TAC [IMAGE_FINITE], ALL_TAC] THEN DISCH_TAC THEN
    ASSUME_TAC SUM_SUM_RESTRICT THEN
    POP_ASSUM (MP_TAC o Q.SPEC `(\x y. f x = y)`) THEN
    FULL_SIMP_TAC std_ss []]);

(* cf. realTheory.SUM_GROUP *)
Theorem SUM_GROUP' : (* was: SUM_GROUP *)
    !f:'a->'b g s t.
        FINITE s /\ (IMAGE f s) SUBSET t
        ==> (sum t (\y. sum {x | x IN s /\ (f(x) = y)} g) = sum s g)
Proof
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [``f:'a->'b``, ``g:'a->real``, ``s:'a->bool``] SUM_IMAGE_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_SUPERSET THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC SUM_EQ_0 THEN
  FULL_SIMP_TAC std_ss [GSPECIFICATION, IN_IMAGE] THEN METIS_TAC []
QED

val REAL_OF_NUM_SUM = store_thm ("REAL_OF_NUM_SUM",
 ``!f s. FINITE s ==> (&(nsum s f) = sum s (\x. &(f x)))``,
  GEN_TAC THEN GEN_TAC THEN
  KNOW_TAC ``((&nsum s f = sum s (\x. &f x))) =
         (\s. (&nsum s f = sum s (\x. &f x))) s`` THENL
  [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISCH_TAC THEN
  ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FINITE_INDUCT THEN
  BETA_TAC THEN SIMP_TAC std_ss[SUM_CLAUSES, NSUM_CLAUSES, GSYM REAL_OF_NUM_ADD]);

val SUM_SUBSET = store_thm ("SUM_SUBSET",
 ``!u v f. FINITE u /\ FINITE v /\
           (!x. x IN (u DIFF v) ==> f(x) <= &0) /\
           (!x:'a. x IN (v DIFF u) ==> &0 <= f(x))
           ==> sum u f <= sum v f``,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [``f:'a->real``, ``u INTER v :'a->bool``] SUM_UNION) THEN
  DISCH_THEN(fn th => MP_TAC(SPEC ``v DIFF u :'a->bool`` th) THEN
                      MP_TAC(SPEC ``u DIFF v :'a->bool`` th)) THEN
  REWRITE_TAC[SET_RULE ``(u INTER v) UNION (u DIFF v) = u``,
              SET_RULE ``(u INTER v) UNION (v DIFF u) = v``] THEN
  ASM_SIMP_TAC std_ss [FINITE_DIFF, FINITE_INTER] THEN
  KNOW_TAC ``DISJOINT (u INTER v) (u DIFF v) /\ DISJOINT (u INTER v) (v DIFF u)``
  THENL [SET_TAC[], ALL_TAC] THEN RW_TAC std_ss [] THEN
  MATCH_MP_TAC(REAL_ARITH ``(0:real) <= -x /\ (0:real) <= y ==> a + x <= a + y``) THEN
  ASM_SIMP_TAC std_ss [GSYM SUM_NEG, FINITE_DIFF] THEN CONJ_TAC THEN
  MATCH_MP_TAC SUM_POS_LE THEN
  ASM_SIMP_TAC std_ss [FINITE_DIFF, REAL_LE_RNEG, REAL_ADD_LID]);

val SUM_SUBSET_SIMPLE = store_thm ("SUM_SUBSET_SIMPLE",
 ``!u v f. FINITE v /\ u SUBSET v /\ (!x:'a. x IN (v DIFF u) ==> (0:real) <= f(x))
           ==> sum u f <= sum v f``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_SUBSET THEN
  ASM_MESON_TAC[IN_DIFF, SUBSET_DEF, SUBSET_FINITE]);

val SUM_IMAGE_NONZERO = store_thm ("SUM_IMAGE_NONZERO",
 ``!d:'b->real i:'a->'b s.
    FINITE s /\
    (!x y. x IN s /\ y IN s /\ ~(x = y) /\ (i x = i y) ==> (d(i x) = (0:real)))
    ==> (sum (IMAGE i s) d = sum s (d o i))``,
  REWRITE_TAC[GSYM NEUTRAL_REAL_ADD, sum_def] THEN
  MATCH_MP_TAC ITERATE_IMAGE_NONZERO THEN REWRITE_TAC[MONOIDAL_REAL_ADD]);

val SUM_BIJECTION = store_thm ("SUM_BIJECTION",
 ``!f p s:'a->bool.
                (!x. x IN s ==> p(x) IN s) /\
                (!y. y IN s ==> ?!x. x IN s /\ (p(x) = y))
                ==> (sum s f = sum s (f o p))``,
  REWRITE_TAC[sum_def] THEN MATCH_MP_TAC ITERATE_BIJECTION THEN
  REWRITE_TAC[MONOIDAL_REAL_ADD]);

val SUM_SUM_PRODUCT = store_thm ("SUM_SUM_PRODUCT",
 ``!s:'a->bool t:'a->'b->bool x.
        FINITE s /\ (!i. i IN s ==> FINITE(t i))
        ==> (sum s (\i. sum (t i) (x i)) =
             sum {i,j | i IN s /\ j IN t i} (\(i,j). x i j))``,
  REWRITE_TAC[sum_def] THEN MATCH_MP_TAC ITERATE_ITERATE_PRODUCT THEN
  REWRITE_TAC[MONOIDAL_REAL_ADD]);

val SUM_EQ_GENERAL = store_thm ("SUM_EQ_GENERAL",
 ``!s:'a->bool t:'b->bool f g h.
        (!y. y IN t ==> ?!x. x IN s /\ (h(x) = y)) /\
        (!x. x IN s ==> h(x) IN t /\ (g(h x) = f x))
        ==> (sum s f = sum t g)``,
  REWRITE_TAC[sum_def] THEN MATCH_MP_TAC ITERATE_EQ_GENERAL THEN
  REWRITE_TAC[MONOIDAL_REAL_ADD]);

val SUM_EQ_GENERAL_INVERSES = store_thm ("SUM_EQ_GENERAL_INVERSES",
 ``!s:'a->bool t:'b->bool f g h k.
        (!y. y IN t ==> k(y) IN s /\ (h(k y) = y)) /\
        (!x. x IN s ==> h(x) IN t /\ (k(h x) = x) /\ (g(h x) = f x))
        ==> (sum s f = sum t g)``,
  REWRITE_TAC[sum_def] THEN MATCH_MP_TAC ITERATE_EQ_GENERAL_INVERSES THEN
  REWRITE_TAC[MONOIDAL_REAL_ADD]);

val SUM_INJECTION = store_thm ("SUM_INJECTION",
 ``!f p s. FINITE s /\
           (!x. x IN s ==> p x IN s) /\
           (!x y. x IN s /\ y IN s /\ (p x = p y) ==> (x = y))
           ==> (sum s (f o p) = sum s f)``,
  REWRITE_TAC[sum_def] THEN MATCH_MP_TAC ITERATE_INJECTION THEN
  REWRITE_TAC[MONOIDAL_REAL_ADD]);

val SUM_UNION_NONZERO = store_thm ("SUM_UNION_NONZERO",
 ``!f s t. FINITE s /\ FINITE t /\ (!x. x IN s INTER t ==> (f(x) = (0:real)))
           ==> (sum (s UNION t) f = sum s f + sum t f)``,
  REWRITE_TAC[sum_def, GSYM NEUTRAL_REAL_ADD] THEN
  MATCH_MP_TAC ITERATE_UNION_NONZERO THEN REWRITE_TAC[MONOIDAL_REAL_ADD]);

val SUM_BIGUNION_NONZERO = store_thm ("SUM_BIGUNION_NONZERO",
 ``!f s. FINITE s /\ (!t:'a->bool. t IN s ==> FINITE t) /\
         (!t1 t2 x. t1 IN s /\ t2 IN s /\ ~(t1 = t2) /\ x IN t1 /\ x IN t2
                    ==> (f x = (0:real)))
         ==> (sum (BIGUNION s) f = sum s (\t. sum t f))``,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] THEN GEN_TAC
  THEN KNOW_TAC ``( (!(t:'a->bool). t IN s ==> FINITE t) /\
    (!t1 t2 x. t1 IN s /\ t2 IN s /\ t1 <> t2 /\ x IN t1 /\ x IN t2 ==>
       (f x = 0)) ==> (sum (BIGUNION s) f = sum s (\t. sum t f))) =
            (\s.  (!t. t IN s ==> FINITE t) /\
    (!t1 t2 x. t1 IN s /\ t2 IN s /\ t1 <> t2 /\ x IN t1 /\ x IN t2 ==>
       (f x = 0)) ==> (sum (BIGUNION s) f = sum s (\t. sum t f))) s`` THENL
  [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISCH_TAC THEN ONCE_ASM_REWRITE_TAC []
  THEN MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  REWRITE_TAC[BIGUNION_EMPTY, BIGUNION_INSERT, SUM_CLAUSES, IN_INSERT] THEN
  SIMP_TAC std_ss [GSYM RIGHT_FORALL_IMP_THM] THEN
  MAP_EVERY X_GEN_TAC [``(s':('a->bool)->bool)``, ``t:'a->bool``] THEN
  DISCH_THEN(fn th => STRIP_TAC THEN MP_TAC th) THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC ``FINITE (s':('a->bool)->bool)`` THEN
  UNDISCH_TAC ``(t :'a -> bool) NOTIN (s' :('a -> bool) -> bool) `` THEN
  ONCE_REWRITE_TAC[AND_IMP_INTRO] THEN ASM_SIMP_TAC std_ss [SUM_CLAUSES]
  THEN KNOW_TAC ``sum (BIGUNION s') f = sum s' (\t. sum t f)`` THENL
  [METIS_TAC [], ALL_TAC] THEN GEN_REWR_TAC (LAND_CONV) [EQ_SYM_EQ]
  THEN DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN MATCH_MP_TAC SUM_UNION_NONZERO THEN
  ASM_SIMP_TAC std_ss [FINITE_BIGUNION, IN_INTER, IN_BIGUNION] THEN
  ASM_MESON_TAC[]);

val SUM_CASES = store_thm ("SUM_CASES",
 ``!s P f g. FINITE s
             ==> (sum s (\x:'a. if P x then f x else g x) =
                  sum {x | x IN s /\ P x} f + sum {x | x IN s /\ ~P x} g)``,
  REWRITE_TAC[sum_def, GSYM NEUTRAL_REAL_ADD] THEN
  MATCH_MP_TAC ITERATE_CASES THEN REWRITE_TAC[MONOIDAL_REAL_ADD]);

val SUM_CASES_1 = store_thm ("SUM_CASES_1",
 ``!s a. FINITE s /\ a IN s
         ==> (sum s (\x. if x = a then y else f(x)) = sum s f + (y - f a))``,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC std_ss [SUM_CASES] THEN
  KNOW_TAC ``{x | x IN s /\ x <> a} = s DELETE a`` THENL
  [FULL_SIMP_TAC std_ss [DELETE_DEF, DIFF_DEF, IN_SING], ALL_TAC] THEN DISCH_TAC
  THEN ASM_SIMP_TAC std_ss [SUM_DELETE] THEN
  ASM_SIMP_TAC std_ss [SET_RULE ``a IN s ==> ({x | x IN s /\ (x = a)} = {a})``] THEN
  REWRITE_TAC[SUM_SING] THEN REAL_ARITH_TAC);

val SUM_LE_INCLUDED = store_thm ("SUM_LE_INCLUDED",
 ``!f:'a->real g:'b->real s t i.
        FINITE s /\ FINITE t /\
        (!y. y IN t ==> (0:real) <= g y) /\
        (!x. x IN s ==> ?y. y IN t /\ (i y = x) /\ f(x) <= g(y))
        ==> sum s f <= sum t g``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC ``sum (IMAGE (i:'b->'a) t) (\y. sum {x | x IN t /\ (i x = y)} g)`` THEN
  CONJ_TAC THENL
   [ALL_TAC,
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MATCH_MP_TAC(GSYM SUM_IMAGE_GEN) THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC ``sum s (\y. sum {x | x IN t /\ ((i:'b->'a) x = y)} g)`` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC ``x:'a`` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC ``x:'a``) THEN
    ASM_SIMP_TAC std_ss [PULL_EXISTS] THEN X_GEN_TAC ``y:'b`` THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC ``sum {y:'b} g`` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[SUM_SING], ALL_TAC],
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_SIMP_TAC std_ss [IMAGE_FINITE] THEN
  ASM_SIMP_TAC std_ss [SUM_POS_LE, FINITE_RESTRICT, GSPECIFICATION] THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF, DIFF_DEF, IN_SING, IN_IMAGE, GSPECIFICATION]
  THEN METIS_TAC []);

val SUM_IMAGE_LE = store_thm ("SUM_IMAGE_LE",
 ``!f:'a->'b g s.
        FINITE s /\
        (!x. x IN s ==> (0:real) <= g(f x))
        ==> sum (IMAGE f s) g <= sum s (g o f)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_LE_INCLUDED THEN
  ASM_SIMP_TAC std_ss [IMAGE_FINITE,
  SET_RULE ``!f s. (!y. y IN IMAGE f s ==> P y) <=> (!x. x IN s ==> P(f x))``] THEN
  ASM_REWRITE_TAC[o_THM] THEN EXISTS_TAC ``f:'a->'b`` THEN
  MESON_TAC[REAL_LE_REFL]);

val SUM_CLOSED = store_thm ("SUM_CLOSED",
 ``!P f:'a->real s.
        P(0:real) /\ (!x y. P x /\ P y ==> P(x + y)) /\ (!a. a IN s ==> P(f a))
        ==> P(sum s f)``,
  REPEAT STRIP_TAC THEN MP_TAC(MATCH_MP ITERATE_CLOSED MONOIDAL_REAL_ADD) THEN
  DISCH_THEN(MP_TAC o SPEC ``P:real->bool``) THEN
  ASM_SIMP_TAC std_ss [NEUTRAL_REAL_ADD, GSYM sum_def]);

(* ------------------------------------------------------------------------- *)
(* Specialize them to sums over intervals of numbers.                        *)
(* ------------------------------------------------------------------------- *)

val SUM_ADD_NUMSEG = store_thm ("SUM_ADD_NUMSEG",
 ``!f g m n. sum{m..n} (\i. f(i) + g(i)) = sum{m..n} f + sum{m..n} g``,
  SIMP_TAC std_ss [SUM_ADD, FINITE_NUMSEG]);

val SUM_SUB_NUMSEG = store_thm ("SUM_SUB_NUMSEG",
 ``!f g m n. sum{m..n} (\i. f(i) - g(i)) = sum{m..n} f - sum{m..n} g``,
   SIMP_TAC std_ss [SUM_SUB, FINITE_NUMSEG]);

val SUM_LE_NUMSEG = store_thm ("SUM_LE_NUMSEG",
 ``!f g m n. (!i. m <= i /\ i <= n ==> f(i) <= g(i))
             ==> sum{m..n} f <= sum{m..n} g``,
  SIMP_TAC std_ss [SUM_LE, FINITE_NUMSEG, IN_NUMSEG]);

val SUM_EQ_NUMSEG = store_thm ("SUM_EQ_NUMSEG",
 ``!f g m n. (!i. m <= i /\ i <= n ==> (f(i) = g(i)))
             ==> (sum{m..n} f = sum{m..n} g)``,
  MESON_TAC[SUM_EQ, FINITE_NUMSEG, IN_NUMSEG]);

val SUM_ABS_NUMSEG = store_thm ("SUM_ABS_NUMSEG",
 ``!f m n. abs(sum{m..n} f) <= sum{m..n} (\i. abs(f i))``,
  SIMP_TAC std_ss [SUM_ABS, FINITE_NUMSEG]);

val SUM_CONST_NUMSEG = store_thm ("SUM_CONST_NUMSEG",
 ``!c m n. sum{m..n} (\n. c) = &((n + 1) - m) * c``,
  SIMP_TAC std_ss [SUM_CONST, FINITE_NUMSEG, CARD_NUMSEG]);

val SUM_EQ_0_NUMSEG = store_thm ("SUM_EQ_0_NUMSEG",
 ``!f m n. (!i. m <= i /\ i <= n ==> (f(i) = &0)) ==> (sum{m..n} f = &0)``,
  SIMP_TAC std_ss [SUM_EQ_0, IN_NUMSEG]);

val SUM_TRIV_NUMSEG = store_thm ("SUM_TRIV_NUMSEG",
 ``!f m n. n < m ==> (sum{m..n} f = &0)``,
  MESON_TAC[SUM_EQ_0_NUMSEG, LESS_EQ_TRANS, NOT_LESS]);

val SUM_POS_LE_NUMSEG = store_thm ("SUM_POS_LE_NUMSEG",
 ``!m n f. (!p. m <= p /\ p <= n ==> &0 <= f(p)) ==> &0 <= sum{m..n} f``,
  SIMP_TAC std_ss [SUM_POS_LE, FINITE_NUMSEG, IN_NUMSEG]);

val SUM_POS_EQ_0_NUMSEG = store_thm ("SUM_POS_EQ_0_NUMSEG",
 ``!f m n. (!p. m <= p /\ p <= n ==> &0 <= f(p)) /\ (sum{m..n} f = &0)
           ==> !p. m <= p /\ p <= n ==> (f(p) = &0)``,
  MESON_TAC[SUM_POS_EQ_0, FINITE_NUMSEG, IN_NUMSEG]);

val SUM_SING_NUMSEG = store_thm ("SUM_SING_NUMSEG",
 ``!f n. sum{n..n} f = f(n)``,
  SIMP_TAC std_ss [SUM_SING, NUMSEG_SING]);

val SUM_CLAUSES_NUMSEG = store_thm ("SUM_CLAUSES_NUMSEG",
 ``(!m. sum{m..0} f = if m = 0 then f(0) else &0) /\
   (!m n. sum{m..SUC n} f = if m <= SUC n then sum{m..n} f + f(SUC n)
                            else sum{m..n} f)``,
  MP_TAC(MATCH_MP ITERATE_CLAUSES_NUMSEG MONOIDAL_REAL_ADD) THEN
  REWRITE_TAC[NEUTRAL_REAL_ADD, sum_def]);

val SUM_SWAP_NUMSEG = store_thm ("SUM_SWAP_NUMSEG",
 ``!a b c d f.
     sum{a..b} (\i. sum{c..d} (f i)) = sum{c..d} (\j. sum{a..b} (\i. f i j))``,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_SWAP THEN
  REWRITE_TAC[FINITE_NUMSEG]);

val SUM_ADD_SPLIT = store_thm ("SUM_ADD_SPLIT",
 “!f m n p.
    m <= n + 1:num ==> ((sum {m..n+p} f = sum{m..n} f + sum{n+1..n+p} f))”,
  REPEAT STRIP_TAC THEN ASSUME_TAC NUMSEG_ADD_SPLIT THEN
  POP_ASSUM (MP_TAC o Q.SPECL [`m`,`n`,`p`]) THEN DISCH_TAC THEN
  ASM_SIMP_TAC std_ss [SUM_UNION, DISJOINT_NUMSEG, FINITE_NUMSEG,
           ARITH_PROVE ``x < x + 1:num``]);

(* cf. realTheory.SUM_OFFSET *)
Theorem SUM_OFFSET' : (* was: SUM_OFFSET *)
    !p f m n. sum{m+p..n+p} f = sum{m..n} (\i. f(i + p))
Proof
  SIMP_TAC std_ss [NUMSEG_OFFSET_IMAGE, SUM_IMAGE,
           EQ_ADD_RCANCEL, FINITE_NUMSEG] THEN
  RW_TAC std_ss [o_DEF]
QED
Theorem SUM_OFFSET[local] = SUM_OFFSET'

val SUM_OFFSET_0 = store_thm ("SUM_OFFSET_0",
 ``!f m n. m <= n ==> (sum{m..n} f = sum{0..n-m} (\i. f(i + m)))``,
  SIMP_TAC std_ss [GSYM SUM_OFFSET, ADD_CLAUSES, SUB_ADD]);

val SUM_CLAUSES_LEFT = store_thm ("SUM_CLAUSES_LEFT",
 ``!f m n. m <= n:num ==> (sum{m..n} f = f(m) + sum{m+1..n} f)``,
  RW_TAC arith_ss [GSYM NUMSEG_LREC, SUM_CLAUSES, FINITE_NUMSEG, IN_NUMSEG]);

val SUM_CLAUSES_RIGHT = store_thm ("SUM_CLAUSES_RIGHT",
 ``!f m n. 0:num < n /\ m <= n ==> (sum{m..n} f = sum{m..n-1} f + f(n))``,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  SIMP_TAC std_ss [LESS_REFL, SUM_CLAUSES_NUMSEG, SUC_SUB1]);

val SUM_PAIR = store_thm ("SUM_PAIR",
 ``!f m n. sum{2*m..2*n+1} f = sum{m..n} (\i. f(2*i) + f(2*i+1))``,
  MP_TAC(MATCH_MP ITERATE_PAIR MONOIDAL_REAL_ADD) THEN
  REWRITE_TAC[sum_def, NEUTRAL_REAL_ADD]);

val REAL_OF_NUM_SUM_NUMSEG = store_thm ("REAL_OF_NUM_SUM_NUMSEG",
 ``!f m n. (&(nsum{m..n} f) = sum {m..n} (\i. &(f i)))``,
  SIMP_TAC std_ss [REAL_OF_NUM_SUM, FINITE_NUMSEG]);

(* connection to realTheory.sum *)
Theorem sum_real :
    !f n. sum{0..n} f = real$sum(0,SUC n) f
Proof
    GEN_TAC
 >> Induct_on `n`
 >- (SIMP_TAC real_ss [sum, SUM_CLAUSES_RIGHT, SUM_SING_NUMSEG])
 >> ASM_SIMP_TAC real_ss [sum, SUM_CLAUSES_RIGHT]
QED

(* ------------------------------------------------------------------------- *)
(* Partial summation and other theorems specific to number segments.         *)
(* ------------------------------------------------------------------------- *)

val SUM_PARTIAL_SUC = store_thm ("SUM_PARTIAL_SUC",
 ``!f g m n.
        sum {m..n} (\k. f(k) * (g(k + 1) - g(k))) =
            if m <= n then f(n + 1) * g(n + 1) - f(m) * g(m) -
                           sum {m..n} (\k. g(k + 1) * (f(k + 1) - f(k)))
            else &0``,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [SUM_TRIV_NUMSEG, GSYM NOT_LESS_EQUAL] THEN
  ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG] THENL
   [COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [] THENL [REAL_ARITH_TAC, FULL_SIMP_TAC std_ss []],
    ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [LE] THEN
  ASM_SIMP_TAC std_ss [GSYM NOT_LESS, SUM_TRIV_NUMSEG, ARITH_PROVE ``n < SUC n``] THEN
  ASM_SIMP_TAC std_ss [GSYM ADD1, ADD_CLAUSES] THEN REAL_ARITH_TAC);

val SUM_PARTIAL_PRE = store_thm ("SUM_PARTIAL_PRE",
 ``!f g m n.
        sum {m..n} (\k. f(k) * (g(k) - g(k - 1))) =
            if m <= n then f(n + 1) * g(n) - f(m) * g(m - 1) -
                           sum {m..n} (\k. g k * (f(k + 1) - f(k)))
            else &0``,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [``f:num->real``, ``\k. (g:num->real)(k - 1)``,
                 ``m:num``, ``n:num``] SUM_PARTIAL_SUC) THEN
  BETA_TAC THEN REWRITE_TAC[ADD_SUB]);

(* cf. realTheory.SUM_DIFFS *)
Theorem SUM_DIFFS' : (* was: SUM_DIFFS *)
   !m n. sum{m..n} (\k. f(k) - f(k + 1)) =
          if m <= n then f(m) - f(n + 1) else (0:real)
Proof
  ONCE_REWRITE_TAC[REAL_ARITH ``a - b = - (1:real) * (b - a)``] THEN
  KNOW_TAC ``?(g:num->real). !k. -1 = g k`` THENL [EXISTS_TAC ``(\k:num. -(1:real))``
  THEN SIMP_TAC std_ss [], ALL_TAC] THEN STRIP_TAC THEN ONCE_ASM_REWRITE_TAC []
  THEN ONCE_REWRITE_TAC[SUM_PARTIAL_SUC] THEN FULL_SIMP_TAC std_ss [EQ_SYM_EQ]
  THEN RW_TAC arith_ss [REAL_SUB_REFL, REAL_MUL_RZERO, SUM_0] THEN
  REAL_ARITH_TAC
QED
val SUM_DIFFS = SUM_DIFFS';

val SUM_DIFFS_ALT = store_thm ("SUM_DIFFS_ALT",
 ``!m n. sum{m..n} (\k. f(k + 1) - f(k)) =
          if m <= n then f(n + 1) - f(m) else &0``,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_NEG_SUB] THEN
  SIMP_TAC std_ss [SUM_NEG, SUM_DIFFS] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_NEG_SUB, REAL_NEG_0]);

val SUM_COMBINE_R = store_thm ("SUM_COMBINE_R",
 ``!f m n p. m <= n + 1 /\ n <= p
             ==> (sum{m..n} f + sum{n+1..p} f = sum{m..p} f)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_UNION_EQ THEN
  REWRITE_TAC[FINITE_NUMSEG, EXTENSION, IN_INTER, IN_UNION, NOT_IN_EMPTY,
              IN_NUMSEG] THEN RW_TAC arith_ss []);

val SUM_COMBINE_L = store_thm ("SUM_COMBINE_L",
 ``!f m n p. 0 < n /\ m <= n /\ n <= p + 1
             ==> (sum{m..n-1} f + sum{n..p} f = sum{m..p} f)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_UNION_EQ THEN
  REWRITE_TAC[FINITE_NUMSEG, EXTENSION, IN_INTER, IN_UNION, NOT_IN_EMPTY,
              IN_NUMSEG] THEN RW_TAC arith_ss []);

val SUM_GP_BASIC = store_thm ("SUM_GP_BASIC",
 ``!x:real n:num. (&1 - x) * sum{0..n} (\i. x pow i) = &1 - x pow (SUC n)``,
  GEN_TAC THEN INDUCT_TAC THEN SIMP_TAC std_ss [SUM_CLAUSES_NUMSEG] THEN
  SIMP_TAC std_ss [pow, REAL_MUL_RID, ZERO_LESS_EQ, POW_1] THEN
  ASM_REWRITE_TAC[REAL_ADD_LDISTRIB, pow] THEN REAL_ARITH_TAC);

val SUM_GP_MULTIPLIED = store_thm ("SUM_GP_MULTIPLIED",
 ``!x m n. m <= n
           ==> ((&1 - x) * sum{m..n} (\i. x pow i) = x pow m - x pow (SUC n))``,
  REPEAT STRIP_TAC THEN
  Q_TAC KNOW_TAC
        ‘(1 - x) * sum {0 .. n - m} (\i. (\i. x pow i) (i + m)) =
         x pow m - x pow SUC n’ THENL [ALL_TAC, METIS_TAC [SUM_OFFSET_0]] THEN
  ASM_SIMP_TAC std_ss
   [REAL_POW_ADD, REAL_MUL_ASSOC, SUM_GP_BASIC, SUM_RMUL] THEN
  SIMP_TAC std_ss [REAL_SUB_RDISTRIB, GSYM REAL_POW_ADD, REAL_MUL_LID] THEN
  ASM_SIMP_TAC std_ss [ARITH_PROVE ``m <= n ==> (SUC(n - m) + m = SUC n)``]);

val SUM_GP = store_thm ("SUM_GP",
 ``!x m n.
        sum{m..n} (\i. x pow i) =
                if n < m then &0
                else if x = &1 then &((n + 1) - m)
                else (x pow m - x pow (SUC n)) / (&1 - x)``,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC(ARITH_PROVE ``n < m \/ ~(n < m) /\ m <= n:num``) THEN
  ASM_SIMP_TAC std_ss [SUM_TRIV_NUMSEG] THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[POW_ONE, SUM_CONST_NUMSEG, REAL_MUL_RID], ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_LMUL_IMP THEN EXISTS_TAC ``&1 - x:real`` THEN
  ASM_SIMP_TAC std_ss [REAL_DIV_LMUL, REAL_SUB_0, SUM_GP_MULTIPLIED]);

val SUMS_SYM = store_thm ("SUMS_SYM",
 ``!s t:real->bool. {x + y | x IN s /\ y IN t} = {y + x | y IN t /\ x IN s}``,
 SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, EXISTS_PROD] THEN
 MESON_TAC[REAL_ADD_SYM]);

val SUM_ABS_TRIANGLE = store_thm ("SUM_ABS_TRIANGLE",
 ``!s f b. FINITE s /\ sum s (\a. abs(f a)) <= b ==> abs(sum s f) <= b``,
  METIS_TAC[SUM_ABS, REAL_LE_TRANS]);

Theorem REAL_MUL_SUM :
   !s t f g.
        FINITE s /\ FINITE t
        ==> sum s f * sum t g = sum s (\i. sum t (\j. f(i) * g(j)))
Proof
    rpt STRIP_TAC
 >> SIMP_TAC std_ss [SUM_LMUL]
 >> ONCE_REWRITE_TAC[REAL_MUL_SYM]
 >> SIMP_TAC std_ss [SUM_LMUL]
QED

Theorem REAL_MUL_SUM_NUMSEG :
   !f g m n p q. sum{m..n} f * sum{p..q} g =
                sum{m..n} (\i. sum{p..q} (\j. f(i) * g(j)))
Proof
    rpt STRIP_TAC
 >> SIMP_TAC std_ss [REAL_MUL_SUM, FINITE_NUMSEG]
QED

(* ------------------------------------------------------------------------- *)
(* Extend congruences to deal with sum. Note that we must have the eta       *)
(* redex or we'll get a loop since f(x) will lambda-reduce recursively.      *)
(* ------------------------------------------------------------------------- *)

val SUM_CONG = store_thm
  ("SUM_CONG",
  ``(!f g s.   (!x. x IN s ==> (f(x) = g(x)))
           ==> (sum s (\i. f(i)) = sum s g)) /\
    (!f g a b. (!i. a <= i /\ i <= b ==> (f(i) = g(i)))
           ==> (sum{a..b} (\i. f(i)) = sum{a..b} g)) /\
    (!f g p.   (!x. p x ==> (f x = g x))
           ==> (sum {y | p y} (\i. f(i)) = sum {y | p y} g))``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN
  ASM_SIMP_TAC std_ss [GSPECIFICATION,  IN_NUMSEG]);

(* ------------------------------------------------------------------------- *)
(* Some special algebraic rearrangements.                                    *)
(* ------------------------------------------------------------------------- *)

val REAL_SUB_POW = store_thm ("REAL_SUB_POW",
 ``!x y n.
        1 <= n ==> (x pow n - y pow n =
                   (x - y) * sum{0n..n-1} (\i. x pow i * y pow (n - 1 - i)))``,
  SIMP_TAC std_ss [GSYM SUM_LMUL] THEN
  REWRITE_TAC[REAL_ARITH
   ``(x - y) * (a * b):real = (x * a) * b - a * (y * b)``] THEN
  SIMP_TAC std_ss [GSYM pow, ADD1, ARITH_PROVE
    ``1 <= n /\ x <= n - 1 ==> (n - 1 - x = n - (x + 1)) /\
    (SUC(n - 1 - x) = n - x)``] THEN REPEAT STRIP_TAC THEN
  Q_TAC KNOW_TAC
        ‘(sum {0n .. n - 1}
          (\i. x pow (i + 1) * y pow (n - 1 - i) -
               x pow i * y pow (n - 1 - i + 1n))) =
         (sum {0n .. n - 1}
          (\i.
             x pow (i + 1) * y pow (n - (i + 1)) -
             x pow i * y pow (n - i)))’ THENL
  [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC [IN_NUMSEG] THEN
  REPEAT STRIP_TAC THEN FULL_SIMP_TAC arith_ss [], DISC_RW_KILL THEN
  ASM_SIMP_TAC std_ss [SUM_DIFFS_ALT, ZERO_LESS_EQ, SUB_0, SUB_ADD,
  SUB_EQUAL_0, pow, REAL_MUL_LID, REAL_MUL_RID]]);

val REAL_SUB_POW_R1 = store_thm ("REAL_SUB_POW_R1",
 ``!x:real n:num. 1 <= n ==> (x pow n - &1 = (x - &1) * sum{0..n-1} (\i. x pow i))``,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPECL [``x:real``, ``1:real``] o MATCH_MP REAL_SUB_POW) THEN
  REWRITE_TAC[POW_ONE, REAL_MUL_RID]);

val REAL_SUB_POW_L1 = store_thm ("REAL_SUB_POW_L1",
 ``!x:real n:num. 1 <= n ==> (&1 - x pow n = (&1 - x) * sum{0..n-1} (\i. x pow i))``,
  ONCE_REWRITE_TAC[GSYM REAL_NEG_SUB] THEN
  SIMP_TAC std_ss [REAL_SUB_POW_R1] THEN REWRITE_TAC[REAL_MUL_LNEG]);

(* ------------------------------------------------------------------------- *)
(* Some useful facts about real polynomial functions.                        *)
(* ------------------------------------------------------------------------- *)

val REAL_SUB_POLYFUN = store_thm ("REAL_SUB_POLYFUN",
 ``!a x y n. 1 <= n
    ==> (sum{0..n} (\i. a i * x pow i) -
         sum{0..n} (\i. a i * y pow i) = (x - y) *
        sum{0..n-1} (\j. sum{j+1..n} (\i. a i * y pow (i - j - 1)) * x pow j))``,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN BETA_TAC THEN
  REWRITE_TAC [GSYM REAL_SUB_LDISTRIB] THEN
  GEN_REWR_TAC LAND_CONV [MATCH_MP SUM_CLAUSES_LEFT (SPEC_ALL ZERO_LESS_EQ)] THEN
  FULL_SIMP_TAC std_ss [REAL_SUB_REFL, pow, REAL_MUL_RZERO, REAL_ADD_LID] THEN
  KNOW_TAC ``sum {1.. n:num} (\i. a i * (x pow i - y pow i)) =
     sum {1.. n} (\i. a i * (x - y) *
       sum {0.. i - 1} (\i'. x pow i' * y pow (i - 1n - i')))`` THENL
  [MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
   FULL_SIMP_TAC std_ss [IN_NUMSEG, REAL_SUB_POW] THEN METIS_TAC [REAL_MUL_ASSOC],
   ALL_TAC] THEN DISC_RW_KILL THEN
  ONCE_REWRITE_TAC[REAL_ARITH ``a * x * s:real = x * a * s``] THEN
  SIMP_TAC std_ss [SUM_LMUL, GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
  SIMP_TAC std_ss [GSYM SUM_LMUL, GSYM SUM_RMUL, SUM_SUM_PRODUCT, FINITE_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
  REPEAT(EXISTS_TAC ``\(x:num,y:num). (y,x)``) THEN
  REWRITE_TAC[FORALL_IN_GSPEC, IN_ELIM_PAIR_THM, IN_NUMSEG] THEN
  SRW_TAC [][] THENL [RW_TAC arith_ss [REAL_MUL_ASSOC],RW_TAC arith_ss [REAL_MUL_ASSOC],
  RW_TAC arith_ss [REAL_MUL_ASSOC],RW_TAC arith_ss [REAL_MUL_ASSOC],
  RW_TAC arith_ss [REAL_MUL_ASSOC, REAL_MUL_SYM]]);

val REAL_SUB_POLYFUN_ALT = store_thm ("REAL_SUB_POLYFUN_ALT",
 ``!a x y n.
    1 <= n
    ==> (sum{0..n} (\i. a i * x pow i) -
         sum{0..n} (\i. a i * y pow i) =
        (x - y) * sum{0..n-1} (\j. sum{0..n-j-1}
                       (\k. a(j+k+1) * y pow k) * x pow j))``,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC std_ss [REAL_SUB_POLYFUN] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC ``j:num`` THEN REPEAT STRIP_TAC THEN
  BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
  MAP_EVERY EXISTS_TAC
   [``\i:num. i - (j + 1)``, ``\k:num. j + k + 1``] THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  RW_TAC arith_ss []);

val REAL_POLYFUN_ROOTBOUND = store_thm ("REAL_POLYFUN_ROOTBOUND",
 ``!n c. ~(!i. i IN {0..n} ==> (c i = 0:real))
         ==> FINITE {x | sum{0..n} (\i. c i * x pow i) = 0:real} /\
             CARD {x | sum{0..n} (\i. c i * x pow i) = 0:real} <= n``,
  REWRITE_TAC[NOT_FORALL_THM, NOT_IMP] THEN INDUCT_TAC THENL
   [REWRITE_TAC[NUMSEG_SING, IN_SING, UNWIND_THM2, SUM_CLAUSES_NUMSEG] THEN
    SIMP_TAC std_ss [pow, REAL_MUL_RID, GSPEC_F, CARD_EMPTY, CARD_INSERT,
             FINITE_EMPTY, LESS_EQ_REFL],
    X_GEN_TAC ``c:num->real`` THEN REWRITE_TAC[IN_NUMSEG] THEN
    DISCH_TAC THEN ASM_CASES_TAC ``(c:num->real) (SUC n) = 0:real`` THENL
     [ASM_SIMP_TAC std_ss [SUM_CLAUSES_NUMSEG, ZERO_LESS_EQ, REAL_MUL_LZERO, REAL_ADD_RID] THEN
      REWRITE_TAC[LE, LEFT_AND_OVER_OR] THEN DISJ2_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[IN_NUMSEG, LE],
      ASM_CASES_TAC ``{x | sum {0..SUC n} (\i. c i * x pow i) = 0:real} = {}`` THEN
      ASM_REWRITE_TAC[FINITE_EMPTY, FINITE_INSERT, CARD_EMPTY, CARD_INSERT, ZERO_LESS_EQ] THEN
      POP_ASSUM MP_TAC THEN GEN_REWR_TAC LAND_CONV [GSYM MEMBER_NOT_EMPTY] THEN
      SIMP_TAC std_ss [GSPECIFICATION, PULL_EXISTS] THEN
      X_GEN_TAC ``r:real`` THEN DISCH_TAC THEN
      MP_TAC(GEN ``x:real`` (ISPECL [``c:num->real``, ``x:real``, ``r:real``, ``SUC n``]
        REAL_SUB_POLYFUN)) THEN
      ASM_REWRITE_TAC[ARITH_PROVE ``1 <= SUC n``, REAL_SUB_RZERO] THEN
      DISCH_THEN(fn th => ASM_REWRITE_TAC [th, REAL_ENTIRE, REAL_SUB_0]) THEN
      SIMP_TAC std_ss [SET_RULE ``{x | (x = c) \/ P x} = c INSERT {x | P x}``] THEN
      MATCH_MP_TAC(METIS[FINITE_INSERT, CARD_EMPTY, CARD_INSERT,
                         ARITH_PROVE ``x <= n ==> SUC x <= SUC n /\ x <= SUC n``]
        ``FINITE s /\ CARD s <= n
         ==> FINITE(r INSERT s) /\ CARD(r INSERT s) <= SUC n``) THEN
      KNOW_TAC “?j. j IN {0..n} /\
                    sum {j + 1..SUC n} (\i. c i * r pow (i - j - 1)) <> 0” THENL
      [EXISTS_TAC ``n:num`` THEN REWRITE_TAC[IN_NUMSEG, ADD1, LESS_EQ_REFL, ZERO_LESS_EQ] THEN
      SIMP_TAC std_ss [SUM_SING_NUMSEG, ARITH_PROVE ``(n + 1) - n - 1 = 0:num``] THEN
      ASM_SIMP_TAC std_ss [GSYM ADD1, pow, REAL_MUL_RID], SRW_TAC [][]]]]);

val REAL_POLYFUN_FINITE_ROOTS = store_thm ("REAL_POLYFUN_FINITE_ROOTS",
 ``!n c. FINITE {x | sum{0..n} (\i. c i * x pow i) = 0:real} <=>
         ?i. i IN {0..n} /\ c i <> 0``,
  REPEAT GEN_TAC THEN REWRITE_TAC[TAUT `a /\ ~b <=> ~(a ==> b)`] THEN
  KNOW_TAC ``(?i. ~(i IN {0 .. n} ==> (c i = 0:real))) =
             (~(!i. i IN {0 .. n} ==> (c i = 0:real)))`` THENL
  [METIS_TAC [NOT_FORALL_THM], ALL_TAC] THEN DISC_RW_KILL THEN
  EQ_TAC THENL [ONCE_REWRITE_TAC[MONO_NOT_EQ] THEN DISCH_TAC THEN
  KNOW_TAC ``!x. (sum {0.. n} (\i. (c:num->real) i * x pow i)) =
             (sum {0.. n} (\i. (0:real) * x pow i))`` THENL
  [GEN_TAC THEN MATCH_MP_TAC SUM_EQ THEN METIS_TAC [], ALL_TAC] THEN
  DISC_RW_KILL THEN SIMP_TAC std_ss [REAL_MUL_LZERO, SUM_0] THEN
  REWRITE_TAC[SET_RULE ``{x | T} = univ(:real)``, real_INFINITE],
  SIMP_TAC std_ss [REAL_POLYFUN_ROOTBOUND]]);

val REAL_POLYFUN_EQ_0 = store_thm ("REAL_POLYFUN_EQ_0",
 ``!n c. (!x. sum{0..n} (\i. c i * x pow i) = 0:real) <=>
         (!i. i IN {0..n} ==> (c i = 0:real))``,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [GEN_REWR_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_THEN(MP_TAC o MATCH_MP
     REAL_POLYFUN_ROOTBOUND) THEN
    ASM_REWRITE_TAC[real_INFINITE, DE_MORGAN_THM,
                    SET_RULE ``{x | T} = univ(:real)``],
  KNOW_TAC ``!x. (sum {0.. n} (\i. (c:num->real) i * x pow i)) =
             (sum {0.. n} (\i. (0:real) * x pow i))`` THENL
  [GEN_TAC THEN MATCH_MP_TAC SUM_EQ THEN METIS_TAC [], ALL_TAC] THEN
  DISC_RW_KILL THEN SIMP_TAC std_ss [REAL_MUL_LZERO, SUM_0]]);

val REAL_POLYFUN_EQ_CONST = store_thm ("REAL_POLYFUN_EQ_CONST",
 ``!n c k. (!x. sum{0..n} (\i. c i * x pow i) = k) <=>
           (c 0 = k) /\ (!i. i IN {1..n} ==> (c i = 0:real))``,
  REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   ``!x. sum{0..n} (\i. (if i = 0 then c 0 - k else c i) * x pow i) = 0:real`` THEN
  CONJ_TAC THENL
   [SIMP_TAC std_ss [SUM_CLAUSES_LEFT, ZERO_LESS_EQ, pow, REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_ARITH ``((c - k) + s = 0:real) <=> (c + s = k)``] THEN
    AP_TERM_TAC THEN ABS_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN GEN_TAC THEN
    REWRITE_TAC[IN_NUMSEG] THEN BETA_TAC THEN
    COND_CASES_TAC THEN RW_TAC arith_ss [],
    SIMP_TAC std_ss [REAL_POLYFUN_EQ_0, IN_NUMSEG, ZERO_LESS_EQ] THEN
    EQ_TAC THENL [RW_TAC arith_ss [] THENL
    [POP_ASSUM (MP_TAC o Q.SPEC `0:num`) THEN COND_CASES_TAC THENL
     [RW_TAC arith_ss [REAL_POS] THEN POP_ASSUM MP_TAC THEN
      REAL_ARITH_TAC, METIS_TAC []], POP_ASSUM MP_TAC THEN
      POP_ASSUM MP_TAC THEN POP_ASSUM (MP_TAC o Q.SPEC `i:num`) THEN
      RW_TAC arith_ss []], RW_TAC arith_ss [REAL_SUB_REFL]]]);

(* ------------------------------------------------------------------------- *)
(* A general notion of polynomial function.                                  *)
(* ------------------------------------------------------------------------- *)

val polynomial_function = new_definition ("polynomial_function",
 ``polynomial_function p <=> ?m c. !x. p x = sum{0..m} (\i. c i * x pow i)``);

val POLYNOMIAL_FUNCTION_CONST = store_thm ("POLYNOMIAL_FUNCTION_CONST",
 ``!c. polynomial_function (\x. c)``,
  GEN_TAC THEN REWRITE_TAC[polynomial_function] THEN
  MAP_EVERY EXISTS_TAC [``0:num``, ``(\i. c):num->real``] THEN
  SIMP_TAC std_ss [SUM_SING_NUMSEG, pow, REAL_MUL_RID]);

val POLYNOMIAL_FUNCTION_ID = store_thm ("POLYNOMIAL_FUNCTION_ID",
 ``polynomial_function (\x. x)``,
  REWRITE_TAC[polynomial_function] THEN
  MAP_EVERY EXISTS_TAC [``SUC 0``, ``\i. if i = 1:num then 1:real else 0:real``] THEN
  SIMP_TAC arith_ss [SUM_CLAUSES_NUMSEG, ZERO_LESS_EQ, pow] THEN REAL_ARITH_TAC);

val POLYNOMIAL_FUNCTION_ADD = store_thm ("POLYNOMIAL_FUNCTION_ADD",
 ``!p q. polynomial_function p /\ polynomial_function q
         ==> polynomial_function (\x. p x + q x)``,
  REPEAT GEN_TAC THEN
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO, polynomial_function, PULL_EXISTS] THEN
  MAP_EVERY X_GEN_TAC  [``m:num``, ``a:num->real``] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [``n:num``, ``b:num->real``] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC ``MAX m n`` THEN EXISTS_TAC
   ``\i:num. (if i <= m then a i else 0:real) + (if i <= n then b i else 0:real)`` THEN
  GEN_TAC THEN SIMP_TAC std_ss [REAL_ADD_RDISTRIB, SUM_ADD_NUMSEG] THEN
  REWRITE_TAC[COND_RAND, COND_RATOR, REAL_MUL_LZERO] THEN
  SIMP_TAC std_ss [GSYM SUM_RESTRICT_SET] THEN
  MATCH_MP_TAC (REAL_ARITH ``(a = b) /\ (c = d) ==> (a + c = b + d:real)``) THEN
  CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_NUMSEG] THEN ARITH_TAC);

val POLYNOMIAL_FUNCTION_LMUL = store_thm ("POLYNOMIAL_FUNCTION_LMUL",
 ``!p c. polynomial_function p ==> polynomial_function (\x. c * p x)``,
  REPEAT GEN_TAC THEN
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO, polynomial_function, PULL_EXISTS] THEN
  MAP_EVERY X_GEN_TAC  [``n:num``, ``a:num->real``] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [``n:num``, ``\i. c * (a:num->real) i``] THEN
  ASM_SIMP_TAC std_ss [SUM_LMUL, GSYM REAL_MUL_ASSOC]);

val POLYNOMIAL_FUNCTION_RMUL = store_thm ("POLYNOMIAL_FUNCTION_RMUL",
 ``!p c. polynomial_function p ==> polynomial_function (\x. p x * c)``,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[POLYNOMIAL_FUNCTION_LMUL]);

val POLYNOMIAL_FUNCTION_NEG = store_thm ("POLYNOMIAL_FUNCTION_NEG",
 ``!p. polynomial_function(\x. -(p x)) <=> polynomial_function p``,
  GEN_TAC THEN EQ_TAC THEN
  DISCH_THEN(MP_TAC o SPEC ``-(1:real)`` o MATCH_MP POLYNOMIAL_FUNCTION_LMUL) THEN
  SIMP_TAC std_ss [REAL_MUL_LNEG, REAL_MUL_LID, ETA_AX, REAL_NEG_NEG]);

val POLYNOMIAL_FUNCTION_SUB = store_thm ("POLYNOMIAL_FUNCTION_SUB",
 ``!p q. polynomial_function p /\ polynomial_function q
         ==> polynomial_function (\x. p x - q x)``,
  SIMP_TAC std_ss [real_sub, POLYNOMIAL_FUNCTION_NEG, POLYNOMIAL_FUNCTION_ADD]);

val POLYNOMIAL_FUNCTION_MUL = store_thm ("POLYNOMIAL_FUNCTION_MUL",
 ``!p q. polynomial_function p /\ polynomial_function q
         ==> polynomial_function (\x. p x * q x)``,
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN
  GEN_REWR_TAC (BINDER_CONV o LAND_CONV) [polynomial_function] THEN
  SIMP_TAC std_ss [PULL_EXISTS] THEN
  SIMP_TAC std_ss [GSYM FUN_EQ_THM] THEN INDUCT_TAC THEN
  ASM_SIMP_TAC std_ss [SUM_SING_NUMSEG, pow, POLYNOMIAL_FUNCTION_RMUL] THEN
  X_GEN_TAC ``c:num->real`` THEN SIMP_TAC std_ss [SUM_CLAUSES_LEFT] THEN
  SIMP_TAC std_ss [ZERO_LESS_EQ, ADD1] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB, pow] THEN
  KNOW_TAC ``polynomial_function
      (\x. p x * (c 0n * 1:real))`` THENL
  [ASM_SIMP_TAC std_ss [POLYNOMIAL_FUNCTION_RMUL], ALL_TAC] THEN
  KNOW_TAC ``polynomial_function
      (\x. p x * sum {1 .. m + 1} (\i. c i * x pow i))`` THENL
  [ONCE_REWRITE_TAC[ARITH_PROVE ``(1:num = 0 + 1)``] THEN
   ONCE_REWRITE_TAC[ARITH_PROVE ``(m + (0 + 1:num) = m + 1)``] THEN
   REWRITE_TAC [SPEC ``1:num`` SUM_OFFSET] THEN BETA_TAC THEN
   SIMP_TAC std_ss [REAL_POW_ADD, POW_1, REAL_MUL_ASSOC, SUM_RMUL] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC ``\i. (c:num->real)(i + 1)``) THEN BETA_TAC THEN
   ABBREV_TAC ``q = \x. p x * sum {0..m} (\i. c (i + 1:num) * x pow i)`` THEN
   RULE_ASSUM_TAC(REWRITE_RULE[FUN_EQ_THM]) THEN POP_ASSUM MP_TAC THEN
   BETA_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
   SIMP_TAC std_ss [polynomial_function] THEN SIMP_TAC std_ss [PULL_EXISTS] THEN
   MAP_EVERY X_GEN_TAC [``n:num``, ``a:num->real``] THEN STRIP_TAC THEN
   EXISTS_TAC ``n + 1:num`` THEN
   EXISTS_TAC ``\i. if i = 0 then 0:real else (a:num->real)(i - 1)`` THEN
   POP_ASSUM MP_TAC THEN GEN_REWR_TAC (LAND_CONV o QUANT_CONV) [EQ_SYM_EQ] THEN
   DISCH_TAC THEN ASM_REWRITE_TAC [] THEN BETA_TAC THEN
   KNOW_TAC ``!x:real. (sum {0.. n + 1}
     (\i. (if i = 0 then 0 else (a:num->real) (i - 1)) * x pow i)) =
    (0:real * x pow 0 + sum {0 + 1..n + 1}
     (\i. (if i = 0 then 0 else (a:num->real) (i - 1)) * x pow i))`` THENL
  [SIMP_TAC std_ss [SUM_CLAUSES_LEFT], ALL_TAC] THEN DISC_RW_KILL THEN
   ASM_SIMP_TAC std_ss [SPEC ``1:num`` SUM_OFFSET, ADD_EQ_0, ADD_SUB] THEN
   POP_ASSUM MP_TAC THEN GEN_REWR_TAC (LAND_CONV o QUANT_CONV) [EQ_SYM_EQ] THEN
   DISCH_TAC THEN ASM_REWRITE_TAC [] THEN SIMP_TAC arith_ss [REAL_POW_ADD,
   REAL_MUL_ASSOC, SUM_RMUL, POW_1, pow] THEN REAL_ARITH_TAC,
   METIS_TAC [POLYNOMIAL_FUNCTION_ADD]]);

val POLYNOMIAL_FUNCTION_SUM = store_thm ("POLYNOMIAL_FUNCTION_SUM",
 ``!s:'a->bool p.
        FINITE s /\ (!i. i IN s ==> polynomial_function(\x. p x i))
        ==> polynomial_function (\x. sum s (p x))``,
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN
  KNOW_TAC ``(!p. (!i. i IN s ==> polynomial_function (\x. p x i)) ==>
                  polynomial_function (\x. sum s (p x))) =
             (\s. !p. (!i. i IN s ==> polynomial_function (\x. p x i)) ==>
                  polynomial_function (\x. sum s (p x))) (s:'a->bool)`` THENL
  [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISC_RW_KILL THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [SUM_CLAUSES, POLYNOMIAL_FUNCTION_CONST] THEN
  SIMP_TAC std_ss [SET_RULE ``!P a s. (!x. x IN a INSERT s ==> P x) <=>
  P a /\ (!x. x IN s ==> P x)``, POLYNOMIAL_FUNCTION_ADD]);

val POLYNOMIAL_FUNCTION_POW = store_thm ("POLYNOMIAL_FUNCTION_POW",
 ``!p n. polynomial_function p ==> polynomial_function (\x. p x pow n)``,
  SIMP_TAC std_ss [RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN
  DISCH_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC std_ss [pow, POLYNOMIAL_FUNCTION_CONST, POLYNOMIAL_FUNCTION_MUL]);

val POLYNOMIAL_FUNCTION_INDUCT = store_thm ("POLYNOMIAL_FUNCTION_INDUCT",
 ``!P. P (\x. x) /\ (!c. P (\x. c)) /\
      (!p q. P p /\ P q ==> P (\x. p x + q x)) /\
      (!p q. P p /\ P q ==> P (\x. p x * q x))
      ==> !p. polynomial_function p ==> P p``,
  GEN_TAC THEN STRIP_TAC THEN
  SIMP_TAC std_ss [polynomial_function, PULL_EXISTS] THEN
  SIMP_TAC std_ss [GSYM FUN_EQ_THM] THEN
  SIMP_TAC std_ss [LEFT_FORALL_IMP_THM, EXISTS_REFL] THEN INDUCT_TAC THEN
  ASM_SIMP_TAC arith_ss [SUM_SING_NUMSEG, pow] THEN
  KNOW_TAC ``!c x:real. (sum {0.. SUC m} (\i. (c:num->real) i * x pow i)) =
      (c 0 * x pow 0 + sum {0 + 1..m + 1} (\i. (c:num->real) i * x pow i))`` THENL
  [REPEAT GEN_TAC THEN ASM_SIMP_TAC arith_ss [SUM_CLAUSES_LEFT, ADD1,
  ZERO_LESS_EQ, pow], ALL_TAC] THEN DISC_RW_KILL THEN GEN_TAC THEN
  KNOW_TAC ``(P :(real -> real) -> bool) (\(x :real).
                (c :num -> real) 0n * x pow 0n) /\
              P (\x. (sum {0+1 .. m+1}
                (\(i :num). c i * x pow i) :real))`` THENL
  [ASM_REWRITE_TAC[pow] THEN
  REWRITE_TAC[SPEC ``1:num`` SUM_OFFSET] THEN
  ASM_SIMP_TAC std_ss [REAL_POW_ADD, POW_1, REAL_MUL_ASSOC, SUM_RMUL],
  METIS_TAC []]);

val POLYNOMIAL_FUNCTION_o = store_thm ("POLYNOMIAL_FUNCTION_o",
 ``!p q. polynomial_function p /\ polynomial_function q
         ==> polynomial_function (p o q)``,
  ONCE_REWRITE_TAC [METIS [] ``(!p q.
      polynomial_function p /\ polynomial_function q ==>
      polynomial_function (p o q)) = (!q p.
      polynomial_function p /\ polynomial_function q ==>
      polynomial_function (p o q))``] THEN ONCE_REWRITE_TAC [CONJ_SYM] THEN
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN
  KNOW_TAC ``!p. polynomial_function (p o q) =
  (\p. polynomial_function (p o q)) (p:real->real)`` THENL
  [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISC_RW_KILL THEN
  MATCH_MP_TAC POLYNOMIAL_FUNCTION_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [o_DEF, POLYNOMIAL_FUNCTION_ADD, POLYNOMIAL_FUNCTION_MUL] THEN
  ASM_REWRITE_TAC[ETA_AX, POLYNOMIAL_FUNCTION_CONST]);

val POLYNOMIAL_FUNCTION_FINITE_ROOTS = store_thm ("POLYNOMIAL_FUNCTION_FINITE_ROOTS",
 ``!p a. polynomial_function p
         ==> (FINITE {x | p x = a} <=> ~(!x. p x = a))``,
  ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  SUBGOAL_THEN
   ``!p. polynomial_function p ==> (FINITE {x | p x = 0:real} <=> ~(!x. p x = 0:real))``
   (fn th =>
      SIMP_TAC std_ss [th, POLYNOMIAL_FUNCTION_SUB, POLYNOMIAL_FUNCTION_CONST]) THEN
  GEN_TAC THEN REWRITE_TAC[polynomial_function] THEN
  STRIP_TAC THEN EQ_TAC THEN ONCE_REWRITE_TAC[MONO_NOT_EQ] THENL
  [SIMP_TAC std_ss [GSPEC_T, real_INFINITE],
   ASM_REWRITE_TAC[REAL_POLYFUN_FINITE_ROOTS] THEN
   SIMP_TAC std_ss [NOT_EXISTS_THM, TAUT `~(p /\ ~q) <=> p ==> q`] THEN DISCH_TAC THEN
   KNOW_TAC ``!x. (sum {0.. m} (\i. (c:num->real) i * x pow i)) =
                  (sum {0.. m} (\i. (0:real) * x pow i))`` THENL
  [GEN_TAC THEN MATCH_MP_TAC SUM_EQ THEN METIS_TAC [], ALL_TAC] THEN DISC_RW_KILL THEN
   REWRITE_TAC[REAL_MUL_LZERO, SUM_0]]);

(* ========================================================================= *)
(*     Products of natural numbers and real numbers (productScript.sml)      *)
(* ========================================================================= *)

Definition nproduct :
   nproduct = iterate(( * ):num->num->num)
End

val NPRODUCT_CLAUSES = store_thm ("NPRODUCT_CLAUSES",
 ``(!f. nproduct {} f = 1) /\
   (!x f s. FINITE(s)
            ==> (nproduct (x INSERT s) f =
                 if x IN s then nproduct s f else f(x) * nproduct s f))``,
  REWRITE_TAC[nproduct, GSYM NEUTRAL_MUL] THEN
  METIS_TAC [SWAP_FORALL_THM, ITERATE_CLAUSES, MONOIDAL_MUL]);

val NPRODUCT_SUPPORT = store_thm ("NPRODUCT_SUPPORT",
 ``!f s. nproduct (support ( * ) f s) f = nproduct s f``,
  REWRITE_TAC[nproduct, ITERATE_SUPPORT]);

val NPRODUCT_UNION = store_thm ("NPRODUCT_UNION",
 ``!f s t. FINITE s /\ FINITE t /\ DISJOINT s t
           ==> ((nproduct (s UNION t) f = nproduct s f * nproduct t f))``,
  SIMP_TAC std_ss [nproduct, ITERATE_UNION, MONOIDAL_MUL]);

val NPRODUCT_IMAGE = store_thm ("NPRODUCT_IMAGE",
 ``!f g s. (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> (nproduct (IMAGE f s) g = nproduct s (g o f))``,
  REWRITE_TAC[nproduct, GSYM NEUTRAL_MUL] THEN
  MATCH_MP_TAC ITERATE_IMAGE THEN REWRITE_TAC[MONOIDAL_MUL]);

val NPRODUCT_ADD_SPLIT = store_thm ("NPRODUCT_ADD_SPLIT",
 ``!f m n p.
        m <= n + 1
        ==> ((nproduct {m..n+p} f = nproduct{m..n} f * nproduct{n+1..n+p} f))``,
  METIS_TAC [NUMSEG_ADD_SPLIT, NPRODUCT_UNION, DISJOINT_NUMSEG, FINITE_NUMSEG,
           ARITH_PROVE ``x < x + 1:num``]);

val NPRODUCT_POS_LT = store_thm ("NPRODUCT_POS_LT",
 ``!f s. FINITE s /\ (!x. x IN s ==> 0 < f x) ==> 0 < nproduct s f``,
  GEN_TAC THEN REWRITE_TAC[CONJ_EQ_IMP] THEN
  ONCE_REWRITE_TAC [METIS []
   ``!s. ((!x. x IN s ==> 0 < f x) ==> 0 < nproduct s f) =
     (\s. (!x. x IN s ==> 0 < f x) ==> 0 < nproduct s f) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC arith_ss [NPRODUCT_CLAUSES, IN_INSERT, ZERO_LESS_MULT]);

val NPRODUCT_POS_LT_NUMSEG = store_thm ("NPRODUCT_POS_LT_NUMSEG",
 ``!f m n. (!x. m <= x /\ x <= n ==> 0 < f x) ==> 0 < nproduct{m..n} f``,
  SIMP_TAC std_ss [NPRODUCT_POS_LT, FINITE_NUMSEG, IN_NUMSEG]);

val NPRODUCT_OFFSET = store_thm ("NPRODUCT_OFFSET",
 ``!f m p. nproduct{m+p..n+p} f = nproduct{m..n} (\i. f(i + p))``,
  SIMP_TAC std_ss [NUMSEG_OFFSET_IMAGE, NPRODUCT_IMAGE,
           EQ_ADD_RCANCEL, FINITE_NUMSEG] THEN
  SIMP_TAC std_ss [o_DEF]);

val NPRODUCT_SING = store_thm ("NPRODUCT_SING",
 ``!f x. nproduct {x} f = f(x)``,
  SIMP_TAC std_ss [NPRODUCT_CLAUSES, FINITE_EMPTY, FINITE_INSERT, NOT_IN_EMPTY, MULT_CLAUSES]);

val NPRODUCT_SING_NUMSEG = store_thm ("NPRODUCT_SING_NUMSEG",
 ``!f n. nproduct{n..n} f = f(n)``,
  REWRITE_TAC[NUMSEG_SING, NPRODUCT_SING]);

val NPRODUCT_CLAUSES_NUMSEG = store_thm ("NPRODUCT_CLAUSES_NUMSEG",
 ``(!m. nproduct{m..0n} f = if m = 0 then f(0) else 1) /\
   (!m n. nproduct{m..SUC n} f = if m <= SUC n then nproduct{m..n} f * f(SUC n)
                                else nproduct{m..n} f)``,
  REWRITE_TAC[NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC std_ss [NPRODUCT_SING, NPRODUCT_CLAUSES, FINITE_NUMSEG, IN_NUMSEG] THEN
  SIMP_TAC arith_ss [ARITH_PROVE ``~(SUC n <= n)``]);

val NPRODUCT_EQ = store_thm ("NPRODUCT_EQ",
 ``!f g s. (!x. x IN s ==> (f x = g x)) ==> (nproduct s f = nproduct s g)``,
  REWRITE_TAC[nproduct] THEN MATCH_MP_TAC ITERATE_EQ THEN
  SIMP_TAC std_ss [MONOIDAL_MUL]);

val NPRODUCT_EQ_NUMSEG = store_thm ("NPRODUCT_EQ_NUMSEG",
 ``!f g m n. (!i. m <= i /\ i <= n ==> (f(i) = g(i)))
             ==> (nproduct{m..n} f = nproduct{m..n} g)``,
  MESON_TAC[NPRODUCT_EQ, FINITE_NUMSEG, IN_NUMSEG]);

val NPRODUCT_EQ_0 = store_thm ("NPRODUCT_EQ_0",
 ``!f s. FINITE s ==> ((nproduct s f = 0) <=> ?x. x IN s /\ (f(x) = 0))``,
  GEN_TAC THEN
  ONCE_REWRITE_TAC [METIS []
   ``!s. ((nproduct s f = 0) <=> ?x. x IN s /\ (f x = 0)) =
         (\s. ((nproduct s f = 0) <=> ?x. x IN s /\ (f x = 0))) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC arith_ss [NPRODUCT_CLAUSES, MULT_EQ_0, IN_INSERT, NOT_IN_EMPTY] THEN
  MESON_TAC[]);

val NPRODUCT_EQ_0_NUMSEG = store_thm ("NPRODUCT_EQ_0_NUMSEG",
 ``!f m n. (nproduct{m..n} f = 0) <=> ?x. m <= x /\ x <= n /\ (f(x) = 0)``,
  SIMP_TAC std_ss [NPRODUCT_EQ_0, FINITE_NUMSEG, IN_NUMSEG, GSYM CONJ_ASSOC]);

val NPRODUCT_LE = store_thm ("NPRODUCT_LE",
 ``!f s. FINITE s /\ (!x. x IN s ==> 0 <= f(x) /\ f(x) <= g(x))
         ==> nproduct s f <= nproduct s g``,
  GEN_TAC THEN REWRITE_TAC[CONJ_EQ_IMP] THEN
  ONCE_REWRITE_TAC [METIS []
   ``!s. ((!x. x IN s ==> 0 <= f x /\ f x <= g x) ==>
  nproduct s f <= nproduct s g) =
     (\s. (!x. x IN s ==> 0 <= f x /\ f x <= g x) ==>
  nproduct s f <= nproduct s g) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [IN_INSERT, NPRODUCT_CLAUSES, NOT_IN_EMPTY, LESS_EQ_REFL] THEN
  MESON_TAC[LESS_MONO_MULT2, ZERO_LESS_EQ]);

val NPRODUCT_LE_NUMSEG = store_thm ("NPRODUCT_LE_NUMSEG",
 ``!f m n. (!i. m <= i /\ i <= n ==> 0 <= f(i) /\ f(i) <= g(i))
           ==> nproduct{m..n} f <= nproduct{m..n} g``,
  SIMP_TAC std_ss [NPRODUCT_LE, FINITE_NUMSEG, IN_NUMSEG]);

val NPRODUCT_EQ_1 = store_thm ("NPRODUCT_EQ_1",
 ``!f s. (!x:'a. x IN s ==> (f(x) = 1)) ==> (nproduct s f = 1)``,
  REWRITE_TAC[nproduct, GSYM NEUTRAL_MUL] THEN
  SIMP_TAC std_ss [ITERATE_EQ_NEUTRAL, MONOIDAL_MUL]);

val NPRODUCT_EQ_1_NUMSEG = store_thm ("NPRODUCT_EQ_1_NUMSEG",
 ``!f m n. (!i. m <= i /\ i <= n ==> (f(i) = 1)) ==> (nproduct{m..n} f = 1)``,
  SIMP_TAC std_ss [NPRODUCT_EQ_1, IN_NUMSEG]);

val NPRODUCT_MUL_GEN = store_thm ("NPRODUCT_MUL_GEN",
 ``!f g s.
       FINITE {x | x IN s /\ ~(f x = 1)} /\ FINITE {x | x IN s /\ ~(g x = 1)}
       ==> (nproduct s (\x. f x * g x) = nproduct s f * nproduct s g)``,
  SIMP_TAC std_ss [GSYM NEUTRAL_MUL, GSYM support, nproduct] THEN
  MATCH_MP_TAC ITERATE_OP_GEN THEN ACCEPT_TAC MONOIDAL_MUL);

val NPRODUCT_MUL = store_thm ("NPRODUCT_MUL",
 ``!f g s. FINITE s
           ==> (nproduct s (\x. f x * g x) = nproduct s f * nproduct s g)``,
  GEN_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC [METIS []
    ``(nproduct s (\x. f x * g x) = nproduct s f * nproduct s g) =
 (\s. (nproduct s (\x. f x * g x) = nproduct s f * nproduct s g)) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC arith_ss [NPRODUCT_CLAUSES, MULT_CLAUSES]);

val NPRODUCT_MUL_NUMSEG = store_thm ("NPRODUCT_MUL_NUMSEG",
 ``!f g m n.
     nproduct{m..n} (\x. f x * g x) = nproduct{m..n} f * nproduct{m..n} g``,
  SIMP_TAC std_ss [NPRODUCT_MUL, FINITE_NUMSEG]);

val NPRODUCT_CONST = store_thm ("NPRODUCT_CONST",
 ``!c s. FINITE s ==> (nproduct s (\x. c) = c EXP (CARD s))``,
  GEN_TAC THEN
  ONCE_REWRITE_TAC [METIS []
   ``(nproduct s (\x. c) = c EXP (CARD s)) =
     (\s. (nproduct s (\x. c) = c EXP (CARD s))) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC arith_ss [NPRODUCT_CLAUSES, CARD_EMPTY, CARD_INSERT, EXP]);

val NPRODUCT_CONST_NUMSEG = store_thm ("NPRODUCT_CONST_NUMSEG",
 ``!c m n. nproduct {m..n} (\x. c) = c EXP ((n + 1) - m)``,
  SIMP_TAC std_ss [NPRODUCT_CONST, CARD_NUMSEG, FINITE_NUMSEG]);

val NPRODUCT_CONST_NUMSEG_1 = store_thm ("NPRODUCT_CONST_NUMSEG_1",
 ``!c n. nproduct{1n..n} (\x. c) = c EXP n``,
  SIMP_TAC arith_ss [NPRODUCT_CONST, CARD_NUMSEG_1, FINITE_NUMSEG]);

val NPRODUCT_ONE = store_thm ("NPRODUCT_ONE",
 ``!s. nproduct s (\n. 1) = 1``,
  SIMP_TAC std_ss [NPRODUCT_EQ_1]);

val NPRODUCT_CLOSED = store_thm ("NPRODUCT_CLOSED",
 ``!P f:'a->num s.
        P(1) /\ (!x y. P x /\ P y ==> P(x * y)) /\ (!a. a IN s ==> P(f a))
        ==> P(nproduct s f)``,
  REPEAT STRIP_TAC THEN MP_TAC(MATCH_MP ITERATE_CLOSED MONOIDAL_MUL) THEN
  DISCH_THEN(MP_TAC o SPEC ``P:num->bool``) THEN
  ASM_SIMP_TAC std_ss [NEUTRAL_MUL, GSYM nproduct]);

val NPRODUCT_CLAUSES_LEFT = store_thm ("NPRODUCT_CLAUSES_LEFT",
 ``!f m n. m <= n ==> (nproduct{m..n} f = f(m) * nproduct{m+1n..n} f)``,
  SIMP_TAC std_ss [GSYM NUMSEG_LREC, NPRODUCT_CLAUSES, FINITE_NUMSEG, IN_NUMSEG] THEN
  ARITH_TAC);

val NPRODUCT_CLAUSES_RIGHT = store_thm ("NPRODUCT_CLAUSES_RIGHT",
 ``!f m n. 0 < n /\ m <= n ==> (nproduct{m..n} f = nproduct{m..n-1n} f * f(n))``,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  SIMP_TAC std_ss [LESS_REFL, NPRODUCT_CLAUSES_NUMSEG, SUC_SUB1]);

val NPRODUCT_SUPERSET = store_thm ("NPRODUCT_SUPERSET",
 ``!f:'a->num u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = 1))
        ==> (nproduct v f = nproduct u f)``,
  SIMP_TAC std_ss [nproduct, GSYM NEUTRAL_MUL, ITERATE_SUPERSET, MONOIDAL_MUL]);

val NPRODUCT_PAIR = store_thm ("NPRODUCT_PAIR",
 ``!f m n. nproduct{2n*m..2n*n+1n} f = nproduct{m..n} (\i. f(2*i) * f(2*i+1))``,
  MP_TAC(MATCH_MP ITERATE_PAIR MONOIDAL_MUL) THEN
  REWRITE_TAC[nproduct, NEUTRAL_MUL]);

val NPRODUCT_DELETE = store_thm ("NPRODUCT_DELETE",
 ``!f s a. FINITE s /\ a IN s
           ==> (f(a) * nproduct(s DELETE a) f = nproduct s f)``,
  SIMP_TAC std_ss [nproduct, ITERATE_DELETE, MONOIDAL_MUL]);

val NPRODUCT_FACT = store_thm ("NPRODUCT_FACT",
 ``!n. nproduct{1n..n} (\m. m) = FACT n``,
  INDUCT_TAC THEN SIMP_TAC arith_ss [NPRODUCT_CLAUSES_NUMSEG, FACT] THEN
  ASM_SIMP_TAC std_ss [ARITH_PROVE ``1 <= SUC n``, MULT_SYM]);

val NPRODUCT_DELTA = store_thm ("NPRODUCT_DELTA",
 ``!s a. nproduct s (\x. if x = a then b else 1) =
         (if a IN s then b else 1)``,
  REWRITE_TAC[nproduct, GSYM NEUTRAL_MUL] THEN
  SIMP_TAC std_ss [ITERATE_DELTA, MONOIDAL_MUL]);

(* ------------------------------------------------------------------------- *)
(* Extend congruences.                                                       *)
(* ------------------------------------------------------------------------- *)

Theorem NPRODUCT_CONG :
    (!f g s.   (!x. x IN s ==> (f(x) = g(x)))
           ==> (nproduct s (\i. f(i)) = nproduct s g)) /\
    (!f g a b. (!i. a <= i /\ i <= b ==> (f(i) = g(i)))
           ==> (nproduct{a..b} (\i. f(i)) = nproduct{a..b} g)) /\
    (!f g p.   (!x. p x ==> (f x = g x))
           ==> (nproduct {y | p y} (\i. f(i)) = nproduct {y | p y} g))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC NPRODUCT_EQ
 >> ASM_SIMP_TAC std_ss [GSPECIFICATION, IN_NUMSEG]
QED

(* ------------------------------------------------------------------------- *)
(* Now products over real numbers.                                           *)
(* ------------------------------------------------------------------------- *)

val product = new_definition ("product",
  ``product = iterate (( * ):real->real->real)``);

val PRODUCT_CLAUSES = store_thm ("PRODUCT_CLAUSES",
 ``(!f. product {} f = &1) /\
   (!x f s. FINITE(s)
            ==> (product (x INSERT s) f =
                 if x IN s then product s f else f(x) * product s f))``,
  REWRITE_TAC[product, GSYM NEUTRAL_REAL_MUL] THEN
  METIS_TAC [SWAP_FORALL_THM, ITERATE_CLAUSES, MONOIDAL_REAL_MUL]);

val PRODUCT_SUPPORT = store_thm ("PRODUCT_SUPPORT",
 ``!f s. product (support ( * ) f s) f = product s f``,
  REWRITE_TAC[product, ITERATE_SUPPORT]);

val PRODUCT_UNION = store_thm ("PRODUCT_UNION",
 ``!f s t. FINITE s /\ FINITE t /\ DISJOINT s t
           ==> (product (s UNION t) f = product s f * product t f)``,
  SIMP_TAC std_ss [product, ITERATE_UNION, MONOIDAL_REAL_MUL]);

val PRODUCT_IMAGE = store_thm ("PRODUCT_IMAGE",
 ``!f g s. (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> (product (IMAGE f s) g = product s (g o f))``,
  REWRITE_TAC[product, GSYM NEUTRAL_REAL_MUL] THEN
  MATCH_MP_TAC ITERATE_IMAGE THEN REWRITE_TAC[MONOIDAL_REAL_MUL]);

val PRODUCT_ADD_SPLIT = store_thm ("PRODUCT_ADD_SPLIT",
 ``!f m n p.
        m <= n + 1
        ==> (product {m..n+p} f = product{m..n} f * product{n+1..n+p} f)``,
  METIS_TAC [NUMSEG_ADD_SPLIT, PRODUCT_UNION, DISJOINT_NUMSEG, FINITE_NUMSEG,
           ARITH_PROVE ``x < x + 1:num``]);

val PRODUCT_POS_LE = store_thm ("PRODUCT_POS_LE",
 ``!f s. FINITE s /\ (!x. x IN s ==> &0 <= f x) ==> &0 <= product s f``,
  GEN_TAC THEN REWRITE_TAC[CONJ_EQ_IMP] THEN
  ONCE_REWRITE_TAC [METIS [] ``!s.
    ((!x. x IN s ==> 0 <= f x) ==> 0 <= product s f) =
    (\s. (!x. x IN s ==> 0 <= f x) ==> 0 <= product s f) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [PRODUCT_CLAUSES, REAL_POS, IN_INSERT, REAL_LE_MUL]);

val PRODUCT_POS_LE_NUMSEG = store_thm ("PRODUCT_POS_LE_NUMSEG",
 ``!f m n. (!x. m <= x /\ x <= n ==> &0 <= f x) ==> &0 <= product{m..n} f``,
  SIMP_TAC std_ss [PRODUCT_POS_LE, FINITE_NUMSEG, IN_NUMSEG]);

val PRODUCT_POS_LT = store_thm ("PRODUCT_POS_LT",
 ``!f s. FINITE s /\ (!x. x IN s ==> &0 < f x) ==> &0 < product s f``,
  GEN_TAC THEN REWRITE_TAC[CONJ_EQ_IMP] THEN
  ONCE_REWRITE_TAC [METIS [] ``!s.
   ((!x. x IN s ==> &0 < f x) ==> &0 < product s f) =
   (\s. (!x. x IN s ==> &0 < f x) ==> &0 < product s f) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [PRODUCT_CLAUSES, REAL_LT_01, IN_INSERT, REAL_LT_MUL]);

val PRODUCT_POS_LT_NUMSEG = store_thm ("PRODUCT_POS_LT_NUMSEG",
 ``!f m n. (!x. m <= x /\ x <= n ==> &0 < f x) ==> &0 < product{m..n} f``,
  SIMP_TAC std_ss [PRODUCT_POS_LT, FINITE_NUMSEG, IN_NUMSEG]);

val PRODUCT_OFFSET = store_thm ("PRODUCT_OFFSET",
 ``!f m p. product{m+p..n+p} f = product{m..n} (\i. f(i + p))``,
  SIMP_TAC std_ss [NUMSEG_OFFSET_IMAGE, PRODUCT_IMAGE,
           EQ_ADD_RCANCEL, FINITE_NUMSEG] THEN
  SIMP_TAC std_ss [o_DEF]);

val PRODUCT_SING = store_thm ("PRODUCT_SING",
 ``!f x. product {x} f = f(x)``,
  SIMP_TAC std_ss [PRODUCT_CLAUSES, FINITE_EMPTY, FINITE_INSERT, NOT_IN_EMPTY,
                   REAL_MUL_RID]);

val PRODUCT_SING_NUMSEG = store_thm ("PRODUCT_SING_NUMSEG",
 ``!f n. product{n..n} f = f(n)``,
  REWRITE_TAC[NUMSEG_SING, PRODUCT_SING]);

val PRODUCT_CLAUSES_NUMSEG = store_thm ("PRODUCT_CLAUSES_NUMSEG",
 ``(!m. product{m..0n} f = if m = 0 then f(0) else &1) /\
   (!m n. product{m..SUC n} f = if m <= SUC n then product{m..n} f * f(SUC n)
                                else product{m..n} f)``,
  REWRITE_TAC[NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC std_ss [PRODUCT_SING, PRODUCT_CLAUSES, FINITE_NUMSEG, IN_NUMSEG] THEN
  SIMP_TAC std_ss [ARITH_PROVE ``~(SUC n <= n)``, REAL_MUL_ASSOC, REAL_MUL_SYM]);

val PRODUCT_EQ = store_thm ("PRODUCT_EQ",
 ``!f g s. (!x. x IN s ==> (f x = g x)) ==> (product s f = product s g)``,
  REWRITE_TAC[product] THEN MATCH_MP_TAC ITERATE_EQ THEN
  REWRITE_TAC[MONOIDAL_REAL_MUL]);

Theorem PRODUCT_EQ_COUNT :
    !f g n. (!i. i < n ==> (f i = g i)) ==>
             product (count n) f = product (count n) g
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC PRODUCT_EQ >> rw []
QED

val PRODUCT_EQ_NUMSEG = store_thm ("PRODUCT_EQ_NUMSEG",
 ``!f g m n. (!i. m <= i /\ i <= n ==> (f(i) = g(i)))
             ==> (product{m..n} f = product{m..n} g)``,
  MESON_TAC[PRODUCT_EQ, FINITE_NUMSEG, IN_NUMSEG]);

val PRODUCT_EQ_0 = store_thm ("PRODUCT_EQ_0",
 ``!f s. FINITE s ==> ((product s f = &0) <=> ?x. x IN s /\ (f(x) = &0))``,
  GEN_TAC THEN
  ONCE_REWRITE_TAC [METIS [] ``!s.
   (((product s f = &0) <=> ?x. x IN s /\ (f(x) = &0))) =
   (\s. ((product s f = &0) <=> ?x. x IN s /\ (f(x) = &0))) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC arith_ss [PRODUCT_CLAUSES, REAL_ENTIRE, IN_INSERT, REAL_OF_NUM_EQ,
           NOT_IN_EMPTY] THEN
  MESON_TAC[]);

Theorem PRODUCT_EQ_0_COUNT :
    !f n. product (count n) f = &0 <=> ?i. i < n /\ (f(i) = &0)
Proof
    rpt GEN_TAC
 >> Suff ‘product (count n) f = &0 <=> ?x. x IN count n /\ (f(x) = &0)’ >- rw []
 >> MATCH_MP_TAC PRODUCT_EQ_0 >> rw []
QED

val PRODUCT_EQ_0_NUMSEG = store_thm ("PRODUCT_EQ_0_NUMSEG",
 ``!f m n. (product{m..n} f = &0) <=> ?x. m <= x /\ x <= n /\ (f(x) = &0)``,
  SIMP_TAC std_ss [PRODUCT_EQ_0, FINITE_NUMSEG, IN_NUMSEG, GSYM CONJ_ASSOC]);

val PRODUCT_LE = store_thm ("PRODUCT_LE",
 ``!f s. FINITE s /\ (!x. x IN s ==> &0 <= f(x) /\ f(x) <= g(x))
         ==> product s f <= product s g``,
  GEN_TAC THEN REWRITE_TAC[CONJ_EQ_IMP] THEN
  ONCE_REWRITE_TAC [METIS [] ``!s.
   ((!x. x IN s ==> &0 <= f(x) /\ f(x) <= g(x))
         ==> product s f <= product s g) =
   (\s. (!x. x IN s ==> &0 <= f(x) /\ f(x) <= g(x))
         ==> product s f <= product s g) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [IN_INSERT, PRODUCT_CLAUSES, NOT_IN_EMPTY, REAL_LE_REFL] THEN
  MESON_TAC[REAL_LE_MUL2, PRODUCT_POS_LE]);

val PRODUCT_LE_NUMSEG = store_thm ("PRODUCT_LE_NUMSEG",
 ``!f m n. (!i. m <= i /\ i <= n ==> &0 <= f(i) /\ f(i) <= g(i))
           ==> product{m..n} f <= product{m..n} g``,
  SIMP_TAC std_ss [PRODUCT_LE, FINITE_NUMSEG, IN_NUMSEG]);

val PRODUCT_EQ_1 = store_thm ("PRODUCT_EQ_1",
 ``!f s. (!x:'a. x IN s ==> (f(x) = &1)) ==> (product s f = &1)``,
  REWRITE_TAC[product, GSYM NEUTRAL_REAL_MUL] THEN
  SIMP_TAC std_ss [ITERATE_EQ_NEUTRAL, MONOIDAL_REAL_MUL]);

Theorem PRODUCT_EQ_1_COUNT :
    !f n. (!i. i < n ==> f i = &1) ==> product (count n) f = &1
Proof
    rpt GEN_TAC
 >> Suff ‘(!i. i IN count n ==> f i = &1) ==> product (count n) f = &1’ >- rw []
 >> DISCH_TAC
 >> MATCH_MP_TAC PRODUCT_EQ_1 >> art []
QED

val PRODUCT_EQ_1_NUMSEG = store_thm ("PRODUCT_EQ_1_NUMSEG",
 ``!f m n. (!i. m <= i /\ i <= n ==> (f(i) = &1)) ==> (product{m..n} f = &1)``,
  SIMP_TAC std_ss [PRODUCT_EQ_1, IN_NUMSEG]);

val PRODUCT_MUL_GEN = store_thm ("PRODUCT_MUL_GEN",
 ``!f g s.
       FINITE {x | x IN s /\ ~(f x = &1)} /\ FINITE {x | x IN s /\ ~(g x = &1)}
       ==> (product s (\x. f x * g x) = product s f * product s g)``,
  REWRITE_TAC[GSYM NEUTRAL_REAL_MUL, GSYM support, product] THEN
  MATCH_MP_TAC ITERATE_OP_GEN THEN ACCEPT_TAC MONOIDAL_REAL_MUL);

val PRODUCT_MUL = store_thm ("PRODUCT_MUL",
 ``!f g s. FINITE s ==> (product s (\x. f x * g x) = product s f * product s g)``,
  GEN_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC [METIS [] ``!s.
   (product s (\x. f x * g x) = product s f * product s g) =
   (\s. product s (\x. f x * g x) = product s f * product s g) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [PRODUCT_CLAUSES, REAL_MUL_ASSOC, REAL_MUL_LID] THEN
  METIS_TAC [REAL_ARITH ``a * b * c * d = a * c * b * d:real``]);

Theorem PRODUCT_MUL_COUNT :
    !f g n. product (count n) (\x. f x * g x) =
            product (count n) f * product (count n) g
Proof
    rpt GEN_TAC
 >> MATCH_MP_TAC PRODUCT_MUL >> rw []
QED

val PRODUCT_MUL_NUMSEG = store_thm ("PRODUCT_MUL_NUMSEG",
 ``!f g m n.
     product{m..n} (\x. f x * g x) = product{m..n} f * product{m..n} g``,
  SIMP_TAC std_ss [PRODUCT_MUL, FINITE_NUMSEG]);

val PRODUCT_CONST = store_thm ("PRODUCT_CONST",
 ``!c s. FINITE s ==> (product s (\x. c) = c pow (CARD s))``,
  GEN_TAC THEN
  ONCE_REWRITE_TAC [METIS [] ``!s.
   (product s (\x. c) = c pow (CARD s)) =
   (\s. product s (\x. c) = c pow (CARD s)) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [PRODUCT_CLAUSES, CARD_EMPTY, CARD_INSERT, pow]);

val PRODUCT_CONST_NUMSEG = store_thm ("PRODUCT_CONST_NUMSEG",
 ``!c m n. product {m..n} (\x. c) = c pow ((n + 1) - m)``,
  SIMP_TAC std_ss [PRODUCT_CONST, CARD_NUMSEG, FINITE_NUMSEG]);

val PRODUCT_CONST_NUMSEG_1 = store_thm ("PRODUCT_CONST_NUMSEG_1",
 ``!c n. product{1n..n} (\x. c) = c pow n``,
  SIMP_TAC std_ss [PRODUCT_CONST, CARD_NUMSEG_1, FINITE_NUMSEG]);

val PRODUCT_NEG = store_thm ("PRODUCT_NEG",
 ``!f s:'a->bool.
     FINITE s ==> (product s (\i. -(f i)) = -(&1) pow (CARD s) * product s f)``,
  SIMP_TAC std_ss [GSYM PRODUCT_CONST, GSYM PRODUCT_MUL] THEN
  REWRITE_TAC[REAL_MUL_LNEG, REAL_MUL_LID]);

val PRODUCT_NEG_NUMSEG = store_thm ("PRODUCT_NEG_NUMSEG",
 ``!f m n. product{m..n} (\i. -(f i)) =
           -(&1) pow ((n + 1) - m) * product{m..n} f``,
  SIMP_TAC std_ss [PRODUCT_NEG, CARD_NUMSEG, FINITE_NUMSEG]);

val PRODUCT_NEG_NUMSEG_1 = store_thm ("PRODUCT_NEG_NUMSEG_1",
 ``!f n. product{1n..n} (\i. -(f i)) = -(&1) pow n * product{1n..n} f``,
  REWRITE_TAC[PRODUCT_NEG_NUMSEG, ADD_SUB]);

val PRODUCT_INV = store_thm ("PRODUCT_INV",
 ``!f s. FINITE s ==> (product s (\x. inv(f x)) = inv(product s f))``,
  GEN_TAC THEN ONCE_REWRITE_TAC [METIS [] ``!s.
   (product s (\x. inv(f x)) = inv(product s f)) =
   (\s. product s (\x. inv(f x)) = inv(product s f)) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC real_ss [PRODUCT_CLAUSES, REAL_INV1] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC ``((f:'a->real) e <> 0) /\ (product s f <> 0:real)`` THENL
  [ASM_SIMP_TAC real_ss [GSYM REAL_INV_MUL], ALL_TAC] THEN
  FULL_SIMP_TAC real_ss [REAL_INV_0]);

val PRODUCT_DIV = store_thm ("PRODUCT_DIV",
 ``!f g s. FINITE s ==> (product s (\x. f x / g x) = product s f / product s g)``,
  SIMP_TAC std_ss [real_div, PRODUCT_MUL, PRODUCT_INV]);

val PRODUCT_DIV_NUMSEG = store_thm ("PRODUCT_DIV_NUMSEG",
 ``!f g m n.
         product{m..n} (\x. f x / g x) = product{m..n} f / product{m..n} g``,
  SIMP_TAC std_ss [PRODUCT_DIV, FINITE_NUMSEG]);

val PRODUCT_ONE = store_thm ("PRODUCT_ONE",
 ``!s. product s (\n. &1) = &1``,
  SIMP_TAC std_ss [PRODUCT_EQ_1]);

val PRODUCT_LE_1 = store_thm ("PRODUCT_LE_1",
 ``!f s. FINITE s /\ (!x. x IN s ==> &0 <= f x /\ f x <= &1)
         ==> product s f <= &1``,
  GEN_TAC THEN REWRITE_TAC[CONJ_EQ_IMP] THEN
  ONCE_REWRITE_TAC [METIS [] ``!s.
   ((!x. x IN s ==> &0 <= f x /\ f x <= &1)
         ==> product s f <= &1) =
   (\s. (!x. x IN s ==> &0 <= f x /\ f x <= &1)
         ==> product s f <= &1) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [PRODUCT_CLAUSES, REAL_LE_REFL, IN_INSERT] THEN
  REPEAT STRIP_TAC THEN GEN_REWR_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC std_ss [PRODUCT_POS_LE]);

val PRODUCT_ABS = store_thm ("PRODUCT_ABS",
 ``!f s. FINITE s ==> (product s (\x. abs(f x)) = abs(product s f))``,
  GEN_TAC THEN ONCE_REWRITE_TAC [METIS [] ``!s.
   (product s (\x. abs(f x)) = abs(product s f)) =
   (\s. product s (\x. abs(f x)) = abs(product s f)) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [PRODUCT_CLAUSES, ABS_MUL, ABS_N]);

val PRODUCT_CLOSED = store_thm ("PRODUCT_CLOSED",
 ``!P f:'a->real s.
        P(&1) /\ (!x y. P x /\ P y ==> P(x * y)) /\ (!a. a IN s ==> P(f a))
        ==> P(product s f)``,
  rpt STRIP_TAC THEN MP_TAC(MATCH_MP ITERATE_CLOSED MONOIDAL_REAL_MUL) THEN
  DISCH_THEN(MP_TAC o SPEC ``P:real->bool``) THEN
  ASM_SIMP_TAC std_ss [NEUTRAL_REAL_MUL, GSYM product]);

val PRODUCT_CLAUSES_LEFT = store_thm ("PRODUCT_CLAUSES_LEFT",
 ``!f m n. m <= n ==> (product{m..n} f = f(m) * product{m+1n..n} f)``,
  SIMP_TAC std_ss [GSYM NUMSEG_LREC, PRODUCT_CLAUSES, FINITE_NUMSEG, IN_NUMSEG] THEN
  SIMP_TAC arith_ss []);

val PRODUCT_CLAUSES_RIGHT = store_thm ("PRODUCT_CLAUSES_RIGHT",
 ``!f m n. 0 < n /\ m <= n ==> (product{m..n} f = product{m..n-1} f * f(n))``,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  SIMP_TAC std_ss [LESS_REFL, PRODUCT_CLAUSES_NUMSEG, SUC_SUB1]);

val REAL_OF_NUM_NPRODUCT = store_thm ("REAL_OF_NUM_NPRODUCT",
 ``!f:'a->num s. FINITE s ==> (&(nproduct s f) = product s (\x. &(f x)))``,
  GEN_TAC THEN ONCE_REWRITE_TAC [METIS [] ``!s.
   (&(nproduct s f) = product s (\x. &(f x))) =
   (\s. &(nproduct s f) = product s (\x. &(f x))) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [PRODUCT_CLAUSES, NPRODUCT_CLAUSES] THEN
  REWRITE_TAC [GSYM REAL_OF_NUM_MUL] THEN METIS_TAC []);

val PRODUCT_SUPERSET = store_thm ("PRODUCT_SUPERSET",
 ``!f:'a->real u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = &1))
        ==> (product v f = product u f)``,
  SIMP_TAC std_ss [product, GSYM NEUTRAL_REAL_MUL,
           ITERATE_SUPERSET, MONOIDAL_REAL_MUL]);

val PRODUCT_PAIR = store_thm ("PRODUCT_PAIR",
 ``!f m n. product{2*m..2*n+1} f = product{m..n} (\i. f(2*i) * f(2*i+1))``,
  MP_TAC(MATCH_MP ITERATE_PAIR MONOIDAL_REAL_MUL) THEN
  SIMP_TAC std_ss [product, NEUTRAL_REAL_MUL]);

val PRODUCT_DELETE = store_thm ("PRODUCT_DELETE",
 ``!f s a. FINITE s /\ a IN s ==> (f(a) * product(s DELETE a) f = product s f)``,
  SIMP_TAC std_ss [product, ITERATE_DELETE, MONOIDAL_REAL_MUL]);

val PRODUCT_DELTA = store_thm ("PRODUCT_DELTA",
 ``!s a. product s (\x. if x = a then b else &1) =
         (if a IN s then b else &1)``,
  REWRITE_TAC[product, GSYM NEUTRAL_REAL_MUL] THEN
  SIMP_TAC std_ss [ITERATE_DELTA, MONOIDAL_REAL_MUL]);

(* ------------------------------------------------------------------------- *)
(* Extend congruences.                                                       *)
(* ------------------------------------------------------------------------- *)

Theorem PRODUCT_CONG :
    (!f g s.   (!x. x IN s ==> (f(x) = g(x)))
           ==> (product s (\i. f(i)) = product s g)) /\
    (!f g a b. (!i. a <= i /\ i <= b ==> (f(i) = g(i)))
           ==> (product{a..b} (\i. f(i)) = product{a..b} g)) /\
    (!f g p.   (!x. p x ==> (f x = g x))
           ==> (product {y | p y} (\i. f(i)) = product {y | p y} g))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC PRODUCT_EQ
 >> ASM_SIMP_TAC std_ss [GSPECIFICATION, IN_NUMSEG]
QED

(* ------------------------------------------------------------------------- *)
(* Real-valued indicator function (cf. extrealTheory.indicator_fn)           *)
(* ------------------------------------------------------------------------- *)

(* This is originally from HOL Light (Multivariate/vectors.ml). Generalized. *)
Definition indicator :
    indicator (s :'a -> bool) :'a -> real = \x. if x IN s then 1 else 0
End

Theorem DROP_INDICATOR :
    !s x. (indicator s x) = if x IN s then &1 else &0
Proof
    SIMP_TAC std_ss [indicator]
QED

Theorem DROP_INDICATOR_POS_LE :
    !s x. &0 <= (indicator s x)
Proof
    RW_TAC real_ss [DROP_INDICATOR]
QED

Theorem DROP_INDICATOR_LE_1 :
    !s x. (indicator s x) <= &1
Proof
    RW_TAC real_ss [DROP_INDICATOR]
QED

Theorem DROP_INDICATOR_ABS_LE_1 :
    !s x. abs(indicator s x) <= &1
Proof
    RW_TAC real_ss [DROP_INDICATOR]
QED

Theorem INDICATOR_EMPTY :
    indicator {} = (\x. 0)
Proof
    SET_TAC [indicator]
QED

Theorem INDICATOR_COMPLEMENT :
    !s. indicator (UNIV DIFF s) = \x. 1 - indicator s x
Proof
    rw [FUN_EQ_THM, indicator]
 >> Cases_on ‘x IN s’ >> rw []
QED

(* ------------------------------------------------------------------------- *)
(* This lemma about iterations comes up in a few places.                     *)
(* ------------------------------------------------------------------------- *)

val ITERATE_NONZERO_IMAGE_LEMMA = store_thm ("ITERATE_NONZERO_IMAGE_LEMMA",
 ``!op s f g a.
   monoidal op /\ FINITE s /\ (g(a) = neutral op) /\
   (!x y. x IN s /\ y IN s /\ (f x = f y) /\ ~(x = y) ==> (g(f x) = neutral op))
    ==> (iterate op {f x | x | x IN s /\ ~(f x = a)} g =
         iterate op s (g o f))``,
  REPEAT STRIP_TAC THEN
  GEN_REWR_TAC RAND_CONV [GSYM ITERATE_SUPPORT] THEN
  REWRITE_TAC [support] THEN
  ONCE_REWRITE_TAC[SET_RULE ``{f x |x| x IN s /\ ~(f x = a)} =
   IMAGE f {x | x IN s /\ ~(f x = a)}``] THEN
  KNOW_TAC ``(!x y.
       x IN {x | x IN s /\ ~((g o f) x = neutral op)} /\
       y IN {x | x IN s /\ ~((g o f) x = neutral op)} /\
       (f x = f y) ==> (x = y))
  ==> (iterate (op:'a->'a->'a) (IMAGE (f:'b->'c) {x | x IN s /\ ~((g o f) x = neutral op)}) g =
       iterate op {x | x IN s /\ ~((g o f) x = neutral op)} ((g:'c->'a) o f))`` THENL
  [SRW_TAC [][ITERATE_IMAGE], ALL_TAC] THEN
  KNOW_TAC ``(!x y.
    x IN {x | x IN s /\ ((g:'c->'a) o (f:'b->'c)) x <> neutral op} /\
    y IN {x | x IN s /\ (g o f) x <> neutral op} /\
    (f x = f y) ==> (x = y))`` THENL
  [SIMP_TAC std_ss [GSPECIFICATION, o_THM] THEN ASM_MESON_TAC[],
   DISCH_TAC THEN ASM_REWRITE_TAC []] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  KNOW_TAC ``IMAGE f {x | x IN s /\ ~(((g:'c->'a) o (f:'b->'c)) x = neutral op)} SUBSET
             IMAGE f {x | x IN s /\ ~(f x = a)} /\
   (!x. x IN IMAGE f {x | x IN s /\ ~(f x = a)} /\
      ~(x IN IMAGE f {x | x IN s /\ ~((g o f) x = neutral op)})
      ==> (g x = neutral (op:'a->'a->'a)))`` THENL
  [ALL_TAC, METIS_TAC [ITERATE_SUPERSET]] THEN
  ASM_SIMP_TAC std_ss [IMAGE_FINITE, FINITE_RESTRICT] THEN
  SIMP_TAC std_ss [IMP_CONJ, FORALL_IN_IMAGE, SUBSET_DEF] THEN
  SIMP_TAC std_ss [GSPECIFICATION, IN_IMAGE, o_THM] THEN
  ASM_MESON_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Using additivity of lifted function to encode definedness.                *)
(* ------------------------------------------------------------------------- *)

(* moved here from integrationTheory *)
Definition lifted :
   (lifted op NONE _ = NONE) /\
   (lifted op _ NONE = NONE) /\
   (lifted op (SOME x) (SOME y) = SOME(op x y))
End

val NEUTRAL_LIFTED = store_thm ("NEUTRAL_LIFTED",
 ``!op. monoidal op ==> (neutral(lifted op) = SOME(neutral op))``,
  REWRITE_TAC[neutral, monoidal] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN
  SIMP_TAC std_ss [FORALL_OPTION, lifted, NOT_NONE_SOME, option_CLAUSES] THEN
  ASM_MESON_TAC[]);

val MONOIDAL_LIFTED = store_thm ("MONOIDAL_LIFTED",
 ``!op. monoidal op ==> monoidal(lifted op)``,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC std_ss [NEUTRAL_LIFTED, monoidal] THEN
  SIMP_TAC std_ss [FORALL_OPTION, lifted, NOT_NONE_SOME, option_CLAUSES] THEN
  ASM_MESON_TAC[monoidal]);

val ITERATE_SOME = store_thm ("ITERATE_SOME",
 ``!op. monoidal op ==> !f s. FINITE s
   ==> (iterate (lifted op) s (\x. SOME(f x)) =
           SOME(iterate op s f))``,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  KNOW_TAC ``!(s :'b -> bool).
               FINITE s ==>
               (\s. (iterate (lifted (op :'a -> 'a -> 'a)) s
                   (\(x :'b). SOME ((f :'b -> 'a) x)) =
                 SOME (iterate op s f))) s`` THENL
  [ALL_TAC, SIMP_TAC std_ss []] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  ASM_SIMP_TAC std_ss [ITERATE_CLAUSES, MONOIDAL_LIFTED, NEUTRAL_LIFTED] THEN
  SIMP_TAC std_ss [lifted]);

val NEUTRAL_AND = store_thm ("NEUTRAL_AND",
 ``neutral(/\) = T``,
  SIMP_TAC std_ss [neutral, FORALL_BOOL] THEN METIS_TAC[]);

val MONOIDAL_AND = store_thm ("MONOIDAL_AND",
 ``monoidal(/\)``,
  REWRITE_TAC [monoidal] THEN
  SIMP_TAC std_ss [NEUTRAL_AND, CONJ_ACI]);

val ITERATE_AND = store_thm ("ITERATE_AND",
 ``!p s. FINITE s ==> (iterate(/\) s p <=> !x. x IN s ==> p x)``,
  GEN_TAC THEN
  ONCE_REWRITE_TAC [METIS [] ``!s. ((iterate(/\) s p <=> !x. x IN s ==> p x)) =
                          (\s. (iterate(/\) s p <=> !x. x IN s ==> p x)) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  ASM_SIMP_TAC std_ss [MONOIDAL_AND, NEUTRAL_AND, ITERATE_CLAUSES] THEN SET_TAC[]);

val _ = export_theory();
