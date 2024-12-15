(* ************************************************************************* *)
(* Sum of a real-valued function on a set: SIGMA f s                         *)
(* ************************************************************************* *)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory combinTheory res_quanTools pairTheory pred_setTheory
     hurdUtils numLib tautLib cardinalTheory mesonLib jrhUtils prim_recTheory
     permutesTheory pred_setLib;

open realTheory RealArith realSimps iterateTheory;

val _ = new_theory "real_sigma";

(* ------------------------------------------------------------------------- *)
(* MESON, METIS, SET_TAC, SET_RULE, ASSERT_TAC, ASM_ARITH_TAC                *)
(* ------------------------------------------------------------------------- *)

fun METIS ths tm = prove(tm,METIS_TAC ths);

val DISC_RW_KILL = DISCH_TAC >> ONCE_ASM_REWRITE_TAC [] \\
                   POP_ASSUM K_TAC;

fun ASSERT_TAC tm = SUBGOAL_THEN tm STRIP_ASSUME_TAC;

val ASM_ARITH_TAC = rpt (POP_ASSUM MP_TAC) >> ARITH_TAC;
val ASM_REAL_ARITH_TAC = REAL_ASM_ARITH_TAC;

(* Minimal hol-light compatibility layer *)
val IMP_CONJ      = CONJ_EQ_IMP;     (* cardinalTheory *)
val FINITE_SUBSET = SUBSET_FINITE_I; (* pred_setTheory *)

Theorem REAL_LT_BETWEEN :
  !a b:real. a < b <=> ?x. a < x /\ x < b
Proof
  metis_tac[REAL_MEAN, REAL_LT_TRANS]
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

Theorem REAL_LE_SQUARE_ABS :
  !x y:real. abs(x) <= abs(y) <=> x pow 2 <= y pow 2
Proof
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  EQ_TAC THEN DISCH_TAC THENL
  [MATCH_MP_TAC POW_LE THEN ASM_REAL_ARITH_TAC,
   CCONTR_TAC THEN UNDISCH_TAC ``abs (x:real) pow 2 <= abs y pow 2`` THEN
   REWRITE_TAC [TWO, REAL_NOT_LE] THEN MATCH_MP_TAC POW_LT THEN
   ASM_REAL_ARITH_TAC]
QED

Theorem REAL_EQ_SQUARE_ABS :
   !x y:real. (abs x = abs y) <=> (x pow 2 = y pow 2)
Proof
  REWRITE_TAC[GSYM REAL_LE_ANTISYM, REAL_LE_SQUARE_ABS]
QED

Theorem REAL_HALF :
   (!e:real. &0 < e / &2 <=> &0 < e) /\
   (!e:real. e / &2 + e / &2 = e) /\
   (!e:real. &2 * (e / &2) = e)
Proof
  SIMP_TAC std_ss [REAL_LT_HALF1, REAL_HALF_DOUBLE, REAL_DIV_LMUL,
                   REAL_ARITH ``2 <> 0:real``]
QED

Theorem REAL_BOUNDS_LT :
    !x k:real. -k < x /\ x < k <=> abs(x) < k
Proof
  REAL_ARITH_TAC
QED

Theorem REAL_LE_BETWEEN :
    !a b. a <= b <=> ?x:real. a <= x /\ x <= b
Proof
  MESON_TAC[REAL_LE_TRANS, REAL_LE_REFL]
QED

Theorem ABS_LE_0 :
    !x:real. abs x <= &0 <=> (x = 0)
Proof
  MESON_TAC[REAL_LE_ANTISYM, ABS_ZERO, ABS_POS]
QED

Theorem REAL_OF_NUM_GE :
    !m n. &m >= (&n:real) <=> m >= n
Proof
  REWRITE_TAC[GE, real_ge, REAL_OF_NUM_LE]
QED

Theorem REAL_LT_LCANCEL_IMP :
    !x y z:real. &0 < x /\ x * y < x * z ==> y < z
Proof
  METIS_TAC [REAL_LT_LMUL]
QED

val REAL_LT_POW2 = store_thm ("REAL_LT_POW2",
 ``!n:num. (&0:real) < &2 pow n``,
  SIMP_TAC arith_ss [REAL_POW_LT, REAL_LT]);

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

val INF_UNIQUE_FINITE = store_thm ("INF_UNIQUE_FINITE",
 ``!s a. FINITE s /\ ~(s = {})
       ==> ((inf s = a) <=> a IN s /\ !y. y IN s ==> a <= y)``,
   ASM_SIMP_TAC std_ss [GSYM REAL_LE_ANTISYM, REAL_LE_INF_FINITE, REAL_INF_LE_FINITE,
               NOT_INSERT_EMPTY, FINITE_INSERT, FINITE_EMPTY] THEN
   MESON_TAC[REAL_LE_REFL, REAL_LE_TRANS, REAL_LE_ANTISYM]);

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

val lemma = prove (
  ``!s. DISJOINT {x | x IN s /\ P x} {x | x IN s /\ ~P x}``,
  GEN_TAC THEN SIMP_TAC std_ss [DISJOINT_DEF, INTER_DEF, EXTENSION, GSPECIFICATION]
  THEN GEN_TAC THEN EQ_TAC THENL
  [RW_TAC std_ss [], RW_TAC std_ss [NOT_IN_EMPTY]]);

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

val REAL_OF_NUM_SUM_NUMSEG = store_thm ("REAL_OF_NUM_SUM_NUMSEG",
 ``!f m n. (&(nsum{m..n} f) = sum {m..n} (\i. &(f i)))``,
  SIMP_TAC std_ss [REAL_OF_NUM_SUM, FINITE_NUMSEG]);

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
(*   Useful Theorems on Real Numbers (from util_probTheory)                  *)
(* ------------------------------------------------------------------------- *)

val REAL_LE_LT_MUL = store_thm
  ("REAL_LE_LT_MUL",
   ``!x y : real. 0 <= x /\ 0 < y ==> 0 <= x * y``,
   rpt STRIP_TAC
   >> MP_TAC (Q.SPECL [`0`, `x`, `y`] REAL_LE_RMUL)
   >> RW_TAC std_ss [REAL_MUL_LZERO]);

val REAL_LT_LE_MUL = store_thm
  ("REAL_LT_LE_MUL",
   ``!x y : real. 0 < x /\ 0 <= y ==> 0 <= x * y``,
   PROVE_TAC [REAL_LE_LT_MUL, REAL_MUL_SYM]);

val REAL_MUL_IDEMPOT = store_thm
  ("REAL_MUL_IDEMPOT",
   ``!r: real. (r * r = r) <=> (r = 0) \/ (r = 1)``,
   GEN_TAC
   >> reverse EQ_TAC
   >- (RW_TAC real_ss [] >> RW_TAC std_ss [REAL_MUL_LZERO, REAL_MUL_LID])
   >> RW_TAC std_ss []
   >> Know `r * r = 1 * r` >- RW_TAC real_ss []
   >> RW_TAC std_ss [REAL_EQ_RMUL]);

val REAL_SUP_LE_X = store_thm
  ("REAL_SUP_LE_X",
   ``!P x:real. (?r. P r) /\ (!r. P r ==> r <= x) ==> sup P <= x``,
   RW_TAC real_ss []
   >> Suff `~(x < sup P)` >- REAL_ARITH_TAC
   >> STRIP_TAC
   >> MP_TAC (SPEC ``P:real->bool`` REAL_SUP_LE)
   >> RW_TAC real_ss [] >|
   [PROVE_TAC [],
    PROVE_TAC [],
    EXISTS_TAC ``x:real``
    >> RW_TAC real_ss []
    >> PROVE_TAC [real_lte]]);

val REAL_X_LE_SUP = store_thm
  ("REAL_X_LE_SUP",
   ``!P x:real. (?r. P r) /\ (?z. !r. P r ==> r <= z) /\ (?r. P r /\ x <= r)
           ==> x <= sup P``,
   RW_TAC real_ss []
   >> Suff `!y. P y ==> y <= sup P` >- PROVE_TAC [REAL_LE_TRANS]
   >> MATCH_MP_TAC REAL_SUP_UBOUND_LE
   >> PROVE_TAC []);

val LE_INF = store_thm
  ("LE_INF",
   ``!p r:real. (?x. x IN p) /\ (!x. x IN p ==> r <= x) ==> r <= inf p``,
   RW_TAC std_ss [INF_DEF_ALT, SPECIFICATION]
   >> POP_ASSUM MP_TAC
   >> ONCE_REWRITE_TAC [GSYM REAL_NEGNEG]
   >> Q.SPEC_TAC (`~r`, `r`)
   >> RW_TAC real_ss [REAL_NEGNEG, REAL_LE_NEG]
   >> MATCH_MP_TAC REAL_SUP_LE_X
   >> RW_TAC std_ss []
   >> PROVE_TAC [REAL_NEGNEG]);

val INF_LE = store_thm
  ("INF_LE",
   ``!p r:real.
       (?z. !x. x IN p ==> z <= x) /\ (?x. x IN p /\ x <= r) ==> inf p <= r``,
   RW_TAC std_ss [INF_DEF_ALT, SPECIFICATION]
   >> POP_ASSUM MP_TAC
   >> ONCE_REWRITE_TAC [GSYM REAL_NEGNEG]
   >> Q.SPEC_TAC (`~r`, `r`)
   >> RW_TAC real_ss [REAL_NEGNEG, REAL_LE_NEG]
   >> MATCH_MP_TAC REAL_X_LE_SUP
   >> RW_TAC std_ss []
   >> PROVE_TAC [REAL_NEGNEG, REAL_LE_NEG]);

val INF_GREATER = store_thm
  ("INF_GREATER",
   ``!p z:real.
       (?x. x IN p) /\ inf p < z ==>
       (?x. x IN p /\ x < z)``,
   RW_TAC std_ss []
   >> Suff `~(!x. x IN p ==> ~(x < z))` >- PROVE_TAC []
   >> REWRITE_TAC [GSYM real_lte]
   >> STRIP_TAC
   >> Q.PAT_X_ASSUM `inf p < z` MP_TAC
   >> RW_TAC std_ss [GSYM real_lte]
   >> MATCH_MP_TAC LE_INF
   >> PROVE_TAC []);

val INF_CLOSE = store_thm
  ("INF_CLOSE",
   ``!p e:real.
       (?x. x IN p) /\ 0 < e ==> (?x. x IN p /\ x < inf p + e)``,
   RW_TAC std_ss []
   >> MATCH_MP_TAC INF_GREATER
   >> CONJ_TAC >- PROVE_TAC []
   >> POP_ASSUM MP_TAC
   >> REAL_ARITH_TAC);

Theorem REAL_NEG_NZ :
    !x:real. x < 0 ==> x <> 0
Proof
    GEN_TAC >> DISCH_TAC
 >> MATCH_MP_TAC REAL_LT_IMP_NE
 >> ASM_REWRITE_TAC []
QED

val REAL_LT_LMUL_0_NEG = store_thm
  ("REAL_LT_LMUL_0_NEG",``!x y:real. 0 < x * y /\ x < 0 ==> y < 0``,
 RW_TAC real_ss []
 >> SPOSE_NOT_THEN ASSUME_TAC
 >> FULL_SIMP_TAC real_ss [REAL_NOT_LT, GSYM REAL_NEG_GT0]
 >> METIS_TAC [REAL_MUL_LNEG, REAL_LT_IMP_LE, REAL_LE_MUL,
               REAL_NEG_GE0, REAL_NOT_LT]);

val REAL_LT_RMUL_0_NEG = store_thm
  ("REAL_LT_RMUL_0_NEG",``!x y:real. 0 < x * y /\ y < 0 ==> x < 0``,
 RW_TAC real_ss []
 >> SPOSE_NOT_THEN ASSUME_TAC
 >> FULL_SIMP_TAC real_ss [REAL_NOT_LT,GSYM REAL_NEG_GT0]
 >> METIS_TAC [REAL_MUL_RNEG, REAL_LT_IMP_LE, REAL_LE_MUL, REAL_NEG_GE0, REAL_NOT_LT]);

val REAL_LT_LMUL_NEG_0 = store_thm
  ("REAL_LT_LMUL_NEG_0",``!x y:real. x * y < 0 /\ 0 < x ==> y < 0``,
 RW_TAC real_ss []
 >> METIS_TAC [REAL_NEG_GT0, REAL_NEG_RMUL, REAL_LT_LMUL_0]);

val REAL_LT_RMUL_NEG_0 = store_thm
  ("REAL_LT_RMUL_NEG_0",``!x y:real. x * y < 0 /\ 0 < y ==> x < 0``,
 RW_TAC real_ss []
 >> METIS_TAC [REAL_NEG_GT0, REAL_NEG_LMUL, REAL_LT_RMUL_0]);

val REAL_LT_LMUL_NEG_0_NEG = store_thm
 ("REAL_LT_LMUL_NEG_0_NEG",``!x y:real. x * y < 0 /\ x < 0 ==> 0 < y``,
 RW_TAC real_ss []
 >> METIS_TAC [REAL_NEG_GT0, REAL_NEG_LMUL, REAL_LT_LMUL_0]);

val REAL_LT_RMUL_NEG_0_NEG = store_thm
 ("REAL_LT_RMUL_NEG_0_NEG",``!x y:real. x * y < 0 /\ y < 0 ==> 0 < x``,
 RW_TAC real_ss []
 >> METIS_TAC [REAL_NEG_GT0, REAL_NEG_RMUL, REAL_LT_RMUL_0]);

val REAL_LT_RDIV_EQ_NEG = store_thm
  ("REAL_LT_RDIV_EQ_NEG", ``!x y z. z < 0:real ==> (y / z < x <=> x * z < y)``,
  RW_TAC real_ss []
  >> `0<-z` by RW_TAC real_ss [REAL_NEG_GT0]
  >> `z<>0` by (METIS_TAC [REAL_LT_IMP_NE])
  >>EQ_TAC
  >- (RW_TAC real_ss []
      >> `y/z*(-z) < x*(-z)` by METIS_TAC [GSYM REAL_LT_RMUL]
      >> FULL_SIMP_TAC real_ss []
      >> METIS_TAC [REAL_DIV_RMUL, REAL_LT_NEG])
  >> RW_TAC real_ss []
  >> `-y < x*(-z)` by FULL_SIMP_TAC real_ss [REAL_LT_NEG]
  >> `-y * inv(-z) < x` by METIS_TAC [GSYM REAL_LT_LDIV_EQ, real_div]
  >> METIS_TAC [REAL_NEG_INV, REAL_NEG_MUL2, GSYM real_div]);

val REAL_LE_RDIV_EQ_NEG = store_thm
  ("REAL_LE_RDIV_EQ_NEG", ``!x y z. z < 0:real ==> (y / z <= x <=> x * z <= y)``,
  RW_TAC real_ss []
  >> `0 < -z` by RW_TAC real_ss [REAL_NEG_GT0]
  >> `z <> 0` by (METIS_TAC [REAL_LT_IMP_NE])
  >>EQ_TAC
  >- (RW_TAC real_ss []
      >> `y / z * (-z) <= x * (-z)` by METIS_TAC [GSYM REAL_LE_RMUL]
      >> FULL_SIMP_TAC real_ss []
      >> METIS_TAC [REAL_DIV_RMUL,REAL_LE_NEG])
  >> RW_TAC real_ss []
  >> `-y <= x * (-z)` by FULL_SIMP_TAC real_ss [REAL_LE_NEG]
  >> `-y * inv (-z) <= x` by METIS_TAC [GSYM REAL_LE_LDIV_EQ, real_div]
  >> METIS_TAC [REAL_NEG_INV, REAL_NEG_MUL2, GSYM real_div]);

val POW_POS_EVEN = store_thm
  ("POW_POS_EVEN",``!x:real. x < 0 ==> ((0 < x pow n) <=> (EVEN n))``,
  Induct_on `n`
  >- RW_TAC std_ss [pow,REAL_LT_01,EVEN]
  >> RW_TAC std_ss [pow,EVEN]
  >> EQ_TAC
  >- METIS_TAC [REAL_LT_ANTISYM, REAL_LT_RMUL_0_NEG, REAL_MUL_COMM]
  >> RW_TAC std_ss []
  >> `x pow n <= 0` by METIS_TAC [real_lt]
  >> `x pow n <> 0` by METIS_TAC [POW_NZ, REAL_LT_IMP_NE]
  >> `x pow n < 0` by METIS_TAC [REAL_LT_LE]
  >> METIS_TAC [REAL_NEG_GT0, REAL_NEG_MUL2, REAL_LT_MUL]);

val POW_NEG_ODD = store_thm
  ("POW_NEG_ODD",``!x:real. x < 0 ==> ((x pow n < 0) <=> (ODD n))``,
  Induct_on `n`
  >- RW_TAC std_ss [pow,GSYM real_lte,REAL_LE_01]
  >> RW_TAC std_ss [pow,ODD]
  >> EQ_TAC
  >- METIS_TAC [REAL_LT_RMUL_NEG_0_NEG, REAL_MUL_COMM, REAL_LT_ANTISYM]
  >> RW_TAC std_ss []
  >> `0 <= x pow n` by METIS_TAC [real_lt]
  >> `x pow n <> 0` by METIS_TAC [POW_NZ, REAL_LT_IMP_NE]
  >> `0 < x pow n` by METIS_TAC [REAL_LT_LE]
  >> METIS_TAC [REAL_NEG_GT0, REAL_MUL_LNEG, REAL_LT_MUL]);

Theorem REAL_MAX_REDUCE :
    !x y :real. x <= y \/ x < y ==> (max x y = y) /\ (max y x = y)
Proof
    PROVE_TAC [REAL_LT_IMP_LE, REAL_MAX_ACI, max_def]
QED

Theorem REAL_MIN_REDUCE :
    !x y :real. x <= y \/ x < y ==> (min x y = x) /\ (min y x = x)
Proof
    PROVE_TAC [REAL_LT_IMP_LE, REAL_MIN_ACI, min_def]
QED

Theorem REAL_LT_MAX_BETWEEN :
    !x b d :real. x < max b d /\ b <= x ==> x < d
Proof
    RW_TAC std_ss [max_def]
 >> fs [real_lte]
QED

Theorem REAL_MIN_LE_BETWEEN :
    !x a c :real. min a c <= x /\ x < a ==> c <= x
Proof
    RW_TAC std_ss [min_def]
 >> PROVE_TAC [REAL_LET_ANTISYM]
QED

Theorem REAL_ARCH_INV_SUC : (* was: reals_Archimedean *)
    !x:real. 0 < x ==> ?n. inv &(SUC n) < x
Proof
  RW_TAC real_ss [REAL_INV_1OVER] THEN SIMP_TAC real_ss [REAL_LT_LDIV_EQ] THEN
  ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
  ASM_SIMP_TAC real_ss [GSYM REAL_LT_LDIV_EQ] THEN
  MP_TAC (ISPEC ``1 / x:real`` SIMP_REAL_ARCH) THEN STRIP_TAC THEN
  Q.EXISTS_TAC `n` THEN FULL_SIMP_TAC real_ss [real_div] THEN
  RULE_ASSUM_TAC (ONCE_REWRITE_RULE [GSYM REAL_LT_INV_EQ]) THEN
  REWRITE_TAC [ADD1, GSYM add_ints] THEN REAL_ASM_ARITH_TAC
QED

Theorem REAL_ARCH_INV' : (* was: ex_inverse_of_nat_less *)
    !x:real. 0 < x ==> ?n. inv (&n) < x
Proof
  RW_TAC std_ss [] THEN FIRST_ASSUM (MP_TAC o MATCH_MP REAL_ARCH_INV_SUC) THEN
  METIS_TAC []
QED

Theorem REAL_LE_MUL' :
    !x y. x <= 0 /\ y <= 0 ==> 0 <= x * y
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘-x’, ‘-y’] REAL_LE_MUL)
 >> REWRITE_TAC [GSYM REAL_NEG_LE0, REAL_NEGNEG, REAL_NEG_MUL2]
 >> DISCH_THEN MATCH_MP_TAC
 >> ASM_REWRITE_TAC []
QED

Theorem REAL_LT_MUL' :
    !x y. x < 0 /\ y < 0 ==> 0 < x * y
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘-x’, ‘-y’] REAL_LT_MUL)
 >> REWRITE_TAC [GSYM REAL_NEG_LT0, REAL_NEGNEG, REAL_NEG_MUL2]
 >> DISCH_THEN MATCH_MP_TAC
 >> ASM_REWRITE_TAC []
QED

Theorem REAL_LT_LMUL' :
    !x y z. x < 0 ==> ((x * y) < (x * z) <=> z < y)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘-x’, ‘z’, ‘y’] REAL_LT_LMUL)
 >> ‘0 < -x’ by PROVE_TAC [GSYM REAL_NEG_LT0, REAL_NEGNEG]
 >> rw [GSYM REAL_NEG_RMUL, REAL_LT_NEG]
QED

Theorem REAL_LT_RMUL' :
    !x y z. z < 0 ==> ((x * z) < (y * z) <=> y < x)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘y’, ‘x’, ‘-z’] REAL_LT_RMUL)
 >> ‘0 < -z’ by PROVE_TAC [GSYM REAL_NEG_LT0, REAL_NEGNEG]
 >> rw [GSYM REAL_NEG_RMUL, REAL_LT_NEG]
QED

Theorem REAL_LT_LDIV_CANCEL :
    !x y (z :real). 0 < x /\ 0 < y /\ 0 < z ==> (z / x < z / y <=> y < x)
Proof
    RW_TAC bool_ss [real_div, REAL_LT_LMUL]
 >> MATCH_MP_TAC REAL_INV_LT_ANTIMONO
 >> ASM_REWRITE_TAC []
QED

Theorem REAL_LE_LDIV_CANCEL :
    !x y (z :real). 0 < x /\ 0 < y /\ 0 < z ==> (z / x <= z / y <=> y <= x)
Proof
    RW_TAC bool_ss [real_div, REAL_LE_LMUL]
 >> MATCH_MP_TAC REAL_INV_LE_ANTIMONO
 >> ASM_REWRITE_TAC []
QED

(* moved here from extrealTheory *)
Theorem ABS_LE_HALF_POW2 :
  !x y :real. abs (x * y) <= 1/2 * (x pow 2 + y pow 2)
Proof
    rpt GEN_TAC
 >> Cases_on `0 <= x * y`
 >- (ASM_SIMP_TAC real_ss [abs] \\
     Know `x * y = (1 / 2) * 2 * x * y`
     >- (Suff `1 / 2 * 2 = 1r`
         >- (Rewr' >> REWRITE_TAC [GSYM REAL_MUL_ASSOC, REAL_MUL_LID]) \\
         MATCH_MP_TAC REAL_DIV_RMUL >> SIMP_TAC real_ss []) >> Rewr' \\
     REWRITE_TAC [GSYM REAL_MUL_ASSOC] \\
     MATCH_MP_TAC REAL_LE_MUL2 >> SIMP_TAC real_ss [REAL_LE_REFL] \\
     CONJ_TAC >- (MATCH_MP_TAC REAL_LT_LE_MUL >> ASM_SIMP_TAC real_ss []) \\
     ONCE_REWRITE_TAC [GSYM REAL_SUB_LE] \\
     Suff `x pow 2 + y pow 2 - 2 * (x * y) = (x - y) pow 2`
     >- (Rewr' >> REWRITE_TAC [REAL_LE_POW2]) \\
     SIMP_TAC real_ss [REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB, REAL_ADD_LDISTRIB,
                       REAL_ADD_RDISTRIB, REAL_ADD_ASSOC, POW_2,
                       GSYM REAL_DOUBLE] \\
     REAL_ARITH_TAC)
 >> ASM_SIMP_TAC real_ss [abs]
 >> fs [GSYM real_lt]
 >> REWRITE_TAC [Once (GSYM REAL_SUB_LE), REAL_SUB_RNEG, REAL_MUL_RNEG]
 >> Suff `x pow 2 + y pow 2 - -2 * (x * y) = (x + y) pow 2`
 >- (Rewr' >> REWRITE_TAC [REAL_LE_POW2])
 >> SIMP_TAC real_ss [REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB, REAL_ADD_LDISTRIB,
                      REAL_ADD_RDISTRIB, REAL_ADD_ASSOC, POW_2,
                      GSYM REAL_DOUBLE]
 >> REAL_ARITH_TAC
QED

(* moved here from extrealTheory *)
Theorem REAL_LE_MUL_EPSILON :
    !x y:real. (!z. 0 < z /\ z < 1 ==> z * x <= y) ==> x <= y
Proof
    rpt STRIP_TAC
 >> Cases_on `x = 0`
 >- (Q.PAT_X_ASSUM `!z. P z` (MP_TAC o Q.SPEC `1/2`)
     >> RW_TAC real_ss [REAL_HALF_BETWEEN])
 >> Cases_on `0 < x`
 >- (MATCH_MP_TAC REAL_LE_EPSILON \\
     RW_TAC std_ss [GSYM REAL_LE_SUB_RADD] \\
     Cases_on `e < x`
     >- (MATCH_MP_TAC REAL_LE_TRANS \\
         Q.EXISTS_TAC `(1 - e/x) * x` \\
         CONJ_TAC
         >- (RW_TAC real_ss [REAL_SUB_RDISTRIB] \\
             METIS_TAC [REAL_DIV_RMUL, REAL_LE_REFL]) \\
         Q.PAT_X_ASSUM `!z. P z` MATCH_MP_TAC \\
         RW_TAC real_ss [REAL_LT_SUB_RADD, REAL_LT_ADDR, REAL_LT_DIV, REAL_LT_SUB_LADD,
                         REAL_LT_1, REAL_LT_IMP_LE]) \\
     FULL_SIMP_TAC std_ss [REAL_NOT_LT] \\
     MATCH_MP_TAC REAL_LE_TRANS \\
     Q.EXISTS_TAC `0` \\
     RW_TAC real_ss [REAL_LE_SUB_RADD] \\
     MATCH_MP_TAC REAL_LE_TRANS \\
     Q.EXISTS_TAC `(1 / 2) * x` \\
     RW_TAC real_ss [REAL_LE_MUL, REAL_LT_IMP_LE])
 >> MATCH_MP_TAC REAL_LE_TRANS
 >> Q.EXISTS_TAC `(1/2)*x`
 >> RW_TAC real_ss []
 >> RW_TAC std_ss [Once (GSYM REAL_LE_NEG), GSYM REAL_MUL_RNEG]
 >> Suff `1/2 * ~x <= 1 * ~x` >- RW_TAC real_ss []
 >> METIS_TAC [REAL_NEG_GT0, REAL_LT_TOTAL, REAL_LE_REFL, REAL_HALF_BETWEEN, REAL_LE_RMUL]
QED

Theorem SUM_PERMUTE :
   !f p s. p permutes s ==> (sum s f = sum s (f o p))
Proof
  REWRITE_TAC[sum_def] THEN MATCH_MP_TAC ITERATE_PERMUTE THEN
  REWRITE_TAC[MONOIDAL_REAL_ADD]
QED

Theorem SUM_PERMUTE_COUNT :
   !f p n. p permutes (count n) ==> (sum (count n) f = sum (count n) (f o p))
Proof
  PROVE_TAC[SUM_PERMUTE, FINITE_COUNT]
QED

Theorem SUM_PERMUTE_NUMSEG :
   !f p m n.
  p permutes (count n DIFF count m) ==>
   (sum (count n DIFF count m) f = sum (count n DIFF count m) (f o p))
Proof
  PROVE_TAC[SUM_PERMUTE, FINITE_COUNT, FINITE_DIFF]
QED

Theorem PRODUCT_PERMUTE :
   !f p s. p permutes s ==> (product s f = product s (f o p))
Proof
  REWRITE_TAC[product] THEN MATCH_MP_TAC ITERATE_PERMUTE THEN
  REWRITE_TAC[MONOIDAL_REAL_MUL]
QED

Theorem PRODUCT_PERMUTE_COUNT :
   !f p n.
    p permutes (count n) ==> (product (count n) f = product (count n) (f o p))
Proof
  PROVE_TAC[PRODUCT_PERMUTE, FINITE_COUNT]
QED

Theorem PRODUCT_PERMUTE_NUMSEG :
  !f p m n.
    p permutes (count n DIFF count m) ==>
    (product (count n DIFF count m) f = product (count n DIFF count m) (f o p))
Proof
  PROVE_TAC[PRODUCT_PERMUTE, FINITE_COUNT, FINITE_DIFF]
QED

Theorem PERMUTES_IN_NUMSEG :
   !p n i. p permutes {1 .. n} /\ i IN {1 .. n} ==> 1 <= p(i) /\ p(i) <= n
Proof
  REWRITE_TAC[permutes, IN_NUMSEG] THEN PROVE_TAC[]
QED

Theorem SUM_PERMUTATIONS_INVERSE :
   !f n. sum {p | p permutes count n } f =
         sum {p | p permutes count n } (\p. f(inverse p))
Proof
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV) empty_rewrites
   [GSYM IMAGE_INVERSE_PERMUTATIONS] THEN
  SIMP_TAC bool_ss
   [Once (Q.prove(`{f x | p x} = IMAGE f {x | p x}`,
     REWRITE_TAC[EXTENSION, IN_IMAGE] THEN
     CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN REWRITE_TAC[]))] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites
                  [GSYM o_DEF] THEN
  MATCH_MP_TAC SUM_IMAGE THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  PROVE_TAC[PERMUTES_INVERSE_INVERSE]
QED

Theorem SUM_PERMUTATIONS_COMPOSE_L :
   !f s q. q permutes s ==>
           sum {p | p permutes s} f =
           sum {p | p permutes s} (\p. f(q o p))
Proof
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fn th => GEN_REWRITE_TAC (funpow 2 LAND_CONV) empty_rewrites
   [GSYM(MATCH_MP IMAGE_COMPOSE_PERMUTATIONS_L th)]) THEN
  SIMP_TAC bool_ss
   [Once (Q.prove(`{f x | p x} = IMAGE f {x | p x}`,
     REWRITE_TAC[EXTENSION, IN_IMAGE] THEN
     CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN REWRITE_TAC[]))] THEN
  REWRITE_TAC[GSYM o_DEF, ETA_THM] THEN
  MATCH_MP_TAC SUM_IMAGE THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM ``\p:'a-> 'a. inverse(q:'a-> 'a) o p``) THEN
  BETA_TAC THEN REWRITE_TAC[o_ASSOC] THEN
  EVERY_ASSUM(CONJUNCTS_THEN SUBST1_TAC o MATCH_MP PERMUTES_INVERSES_o) THEN
  REWRITE_TAC[I_o_ID]
QED

Theorem SUM_PERMUTATIONS_COMPOSE_L_COUNT :
   !f n q. q permutes count n ==>
           sum {p | p permutes count n} f =
           sum {p | p permutes count n} (\p. f(q o p))
Proof
  REWRITE_TAC[SUM_PERMUTATIONS_COMPOSE_L]
QED

Theorem SUM_PERMUTATIONS_COMPOSE_L_NUMSEG :
   !f m n q.
        q permutes (count n DIFF count m)
        ==> sum {p | p permutes (count n DIFF count m)} f =
            sum {p | p permutes (count n DIFF count m)} (\p. f(q o p))
Proof
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fn th => GEN_REWRITE_TAC (funpow 2 LAND_CONV) empty_rewrites
   [GSYM(MATCH_MP IMAGE_COMPOSE_PERMUTATIONS_L th)]) THEN
  SIMP_TAC bool_ss
   [Once (Q.prove(`{f x | p x} = IMAGE f {x | p x}`,
     REWRITE_TAC[EXTENSION, IN_IMAGE] THEN
     CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN REWRITE_TAC[]))] THEN
  REWRITE_TAC[GSYM o_DEF, ETA_THM] THEN
  MATCH_MP_TAC SUM_IMAGE THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM “\p:num-> num. inverse(q:num-> num) o p”) THEN
  BETA_TAC THEN REWRITE_TAC[o_ASSOC] THEN
  EVERY_ASSUM(CONJUNCTS_THEN SUBST1_TAC o MATCH_MP PERMUTES_INVERSES_o) THEN
  REWRITE_TAC[I_o_ID]
QED

Theorem SUM_PERMUTATIONS_COMPOSE_R :
   !f s q.
        q permutes s
        ==> sum {p | p permutes s} f =
            sum {p | p permutes s} (\p. f(p o q))
Proof
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fn th => GEN_REWRITE_TAC (funpow 2 LAND_CONV) empty_rewrites
   [GSYM(MATCH_MP IMAGE_COMPOSE_PERMUTATIONS_R th)]) THEN
  SIMP_TAC bool_ss
   [Once (Q.prove(`{f x | p x} = IMAGE f {x | p x}`,
     REWRITE_TAC[EXTENSION, IN_IMAGE] THEN
     CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN REWRITE_TAC[]))] THEN
  SIMP_TAC bool_ss[GSYM o_ABS_R] THEN
  MATCH_MP_TAC SUM_IMAGE THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM ``\p:'a-> 'a. p o inverse(q:'a-> 'a)``) THEN
  BETA_TAC THEN REWRITE_TAC[GSYM o_ASSOC] THEN
  EVERY_ASSUM(CONJUNCTS_THEN SUBST1_TAC o MATCH_MP PERMUTES_INVERSES_o) THEN
  REWRITE_TAC[I_o_ID]
QED

Theorem SUM_PERMUTATIONS_COMPOSE_R_COUNT :
   !f n q.
        q permutes count n
        ==> sum {p | p permutes count n} f =
            sum {p | p permutes count n} (\p. f(p o q))
Proof
  REWRITE_TAC[SUM_PERMUTATIONS_COMPOSE_R]
QED

Theorem SUM_PERMUTATIONS_COMPOSE_R_NUMSEG :
   !f m n q.
        q permutes (count n DIFF count m)
        ==> sum {p | p permutes (count n DIFF count m)} f =
            sum {p | p permutes (count n DIFF count m)} (\p. f(p o q))
Proof
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fn th => GEN_REWRITE_TAC (funpow 2 LAND_CONV) empty_rewrites
   [GSYM(MATCH_MP IMAGE_COMPOSE_PERMUTATIONS_R th)]) THEN
  SIMP_TAC bool_ss
   [Once (Q.prove(`{f x | p x} = IMAGE f {x | p x}`,
     REWRITE_TAC[EXTENSION, IN_IMAGE] THEN
     CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN REWRITE_TAC[]))] THEN
  SIMP_TAC bool_ss[GSYM o_ABS_R] THEN
  MATCH_MP_TAC SUM_IMAGE THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM “\p:num-> num. p o inverse(q:num-> num)”) THEN
  BETA_TAC THEN REWRITE_TAC[GSYM o_ASSOC] THEN
  EVERY_ASSUM(CONJUNCTS_THEN SUBST1_TAC o MATCH_MP PERMUTES_INVERSES_o) THEN
  REWRITE_TAC[I_o_ID]
QED

(* ----------------------------------------------------------------------
    REAL_SUM_IMAGE

    This constant is the same as standard mathematics \Sigma operator:

     \Sigma_{x\in P}{f(x)} = SUM_IMAGE f P

    Where f's range is the real numbers and P is finite.
   ---------------------------------------------------------------------- *)

Definition REAL_SUM_IMAGE_DEF :
    REAL_SUM_IMAGE f s = ITSET (\e acc. f e + acc) s (0:real)
End

Overload SIGMA = “REAL_SUM_IMAGE”

Theorem REAL_SUM_IMAGE_EMPTY[simp]:
    !f. REAL_SUM_IMAGE f EMPTY = 0
Proof
    simp[REAL_SUM_IMAGE_DEF]
QED

Theorem REAL_SUM_IMAGE_THM :
    !f. (REAL_SUM_IMAGE f {} = 0) /\
        (!e s. FINITE s ==>
               (REAL_SUM_IMAGE f (e INSERT s) =
                f e + REAL_SUM_IMAGE f (s DELETE e)))
Proof
  REPEAT STRIP_TAC
  >- SIMP_TAC (srw_ss()) [ITSET_THM, REAL_SUM_IMAGE_DEF]
  >> SIMP_TAC (srw_ss()) [REAL_SUM_IMAGE_DEF]
  >> Q.ABBREV_TAC `g = \e acc. f e + acc`
  >> Suff `ITSET g (e INSERT s) 0 =
                    g e (ITSET g (s DELETE e) 0)`
  >- (Q.UNABBREV_TAC `g` >> SRW_TAC [] [])
  >> MATCH_MP_TAC COMMUTING_ITSET_RECURSES
  >> Q.UNABBREV_TAC `g`
  >> RW_TAC real_ss []
  >> REAL_ARITH_TAC
QED

(* An equivalent theorem linking REAL_SUM_IMAGE and Sum *)
Theorem REAL_SUM_IMAGE_sum :
    !f s. FINITE s ==> REAL_SUM_IMAGE f s = Sum s f
Proof
    Q.X_GEN_TAC ‘f’
 >> HO_MATCH_MP_TAC FINITE_INDUCT
 >> CONJ_TAC >- rw [REAL_SUM_IMAGE_THM, SUM_CLAUSES]
 >> rpt STRIP_TAC
 >> ‘s DELETE e = s’ by METIS_TAC [DELETE_NON_ELEMENT]
 >> rw [REAL_SUM_IMAGE_THM, SUM_CLAUSES]
QED

(* it translates a sum theorem into a SIGMA theorem *)
fun translate th = SIMP_RULE std_ss [GSYM REAL_SUM_IMAGE_sum] th;

Theorem REAL_SUM_IMAGE_SING[simp] :
    !f e. REAL_SUM_IMAGE f {e} = f e
Proof
    SRW_TAC [][REAL_SUM_IMAGE_THM]
QED

Theorem REAL_SUM_IMAGE_POS :
    !f s. FINITE s /\ (!x. x IN s ==> 0 <= f x) ==>
          0 <= REAL_SUM_IMAGE f s
Proof
    rw [REAL_SUM_IMAGE_sum, SUM_POS_LE]
QED

Theorem REAL_SUM_IMAGE_SPOS :
    !s. FINITE s /\ (~(s = {})) ==>
        !f. (!x. x IN s ==> 0 < f x) ==>
            0 < REAL_SUM_IMAGE f s
Proof
    rw [REAL_SUM_IMAGE_sum]
 >> MATCH_MP_TAC SUM_POS_LT >> art []
 >> CONJ_TAC >- METIS_TAC [REAL_LT_IMP_LE]
 >> fs [GSYM MEMBER_NOT_EMPTY]
 >> Q.EXISTS_TAC ‘x’ >> rw []
QED

(* ‘?x. x IN P’ already indicates ‘P <> {}’, thus the actual conclusion is just
   ‘SIGMA f P <> 0’
 *)
Theorem REAL_SUM_IMAGE_NONZERO :
    !P. FINITE P ==>
        !f. (!x. x IN P ==> 0 <= f x) /\ (?x. x IN P /\ ~(f x = 0)) ==>
            ((~(REAL_SUM_IMAGE f P = 0)) <=> (~(P = {})))
Proof
    rw [REAL_SUM_IMAGE_sum]
 >> ‘P <> {}’ by METIS_TAC [MEMBER_NOT_EMPTY]
 >> rw []
 >> Suff ‘0 < sum P f’ >- METIS_TAC [REAL_LT_IMP_NE]
 >> ‘0 < f x’ by METIS_TAC [REAL_LE_LT]
 >> MATCH_MP_TAC SUM_POS_LT >> rw []
 >> Q.EXISTS_TAC ‘x’ >> art []
QED

(* |- !f s.
        FINITE s /\ (!x. x IN s ==> 0 <= f x) /\ (?x. x IN s /\ 0 < f x) ==>
        0 < SIGMA f s
 *)
Theorem REAL_SUM_IMAGE_POS_LT = translate SUM_POS_LT

val REAL_SUM_IMAGE_IF_ELIM_lem = prove
  (``!s. FINITE s ==>
                (\s. !P f. (!x. x IN s ==> P x) ==>
                        (REAL_SUM_IMAGE (\x. if P x then f x else 0) s =
                         REAL_SUM_IMAGE f s)) s``,
   MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC real_ss [REAL_SUM_IMAGE_THM, IN_INSERT, DELETE_NON_ELEMENT]);

val REAL_SUM_IMAGE_IF_ELIM = store_thm
  ("REAL_SUM_IMAGE_IF_ELIM",
   ``!s P f. FINITE s /\ (!x. x IN s ==> P x) ==>
                (REAL_SUM_IMAGE (\x. if P x then f x else 0) s =
                 REAL_SUM_IMAGE f s)``,
   METIS_TAC [REAL_SUM_IMAGE_IF_ELIM_lem]);

val REAL_SUM_IMAGE_FINITE_SAME_lem = prove
  (``!P. FINITE P ==>
         (\P. !f p.
             p IN P /\ (!q. q IN P ==> (f p = f q)) ==> (REAL_SUM_IMAGE f P = (&(CARD P)) * f p)) P``,
   MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC real_ss [REAL_SUM_IMAGE_THM, CARD_EMPTY, DELETE_NON_ELEMENT]
   >> `f p = f e` by FULL_SIMP_TAC std_ss [IN_INSERT]
   >> FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT] >> POP_ASSUM (K ALL_TAC)
   >> RW_TAC real_ss [CARD_INSERT, ADD1]
   >> ONCE_REWRITE_TAC [GSYM REAL_ADD]
   >> RW_TAC real_ss [REAL_ADD_RDISTRIB]
   >> Suff `REAL_SUM_IMAGE f s = & (CARD s) * f e`
   >- RW_TAC real_ss [REAL_ADD_COMM]
   >> (MP_TAC o Q.SPECL [`s`]) SET_CASES >> RW_TAC std_ss []
   >- RW_TAC real_ss [REAL_SUM_IMAGE_THM, CARD_EMPTY]
   >> `f e = f x` by FULL_SIMP_TAC std_ss [IN_INSERT]
   >> FULL_SIMP_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
   >> Q.PAT_ASSUM `!f p. b` MATCH_MP_TAC >> METIS_TAC [IN_INSERT]);

val REAL_SUM_IMAGE_FINITE_SAME = store_thm
  ("REAL_SUM_IMAGE_FINITE_SAME",
   ``!P. FINITE P ==>
         !f p.
             p IN P /\ (!q. q IN P ==> (f p = f q)) ==> (REAL_SUM_IMAGE f P = (&(CARD P)) * f p)``,
   MP_TAC REAL_SUM_IMAGE_FINITE_SAME_lem >> RW_TAC std_ss []);

val REAL_SUM_IMAGE_FINITE_CONST = store_thm
  ("REAL_SUM_IMAGE_FINITE_CONST",
   ``!P. FINITE P ==>
        !f x. (!y. f y = x) ==> (REAL_SUM_IMAGE f P = (&(CARD P)) * x)``,
   REPEAT STRIP_TAC
   >> (MP_TAC o Q.SPECL [`P`]) REAL_SUM_IMAGE_FINITE_SAME
   >> RW_TAC std_ss []
   >> POP_ASSUM (MP_TAC o (Q.SPECL [`f`]))
   >> RW_TAC std_ss []
   >> (MP_TAC o Q.SPECL [`P`]) SET_CASES
   >> RW_TAC std_ss [] >- RW_TAC real_ss [REAL_SUM_IMAGE_THM, CARD_EMPTY]
   >> POP_ASSUM (K ALL_TAC)
   >> POP_ASSUM MATCH_MP_TAC
   >> Q.EXISTS_TAC `x'` >> RW_TAC std_ss [IN_INSERT]);

val REAL_SUM_IMAGE_FINITE_CONST2 = store_thm (* from "examples/diningcryptos" *)
  ("REAL_SUM_IMAGE_FINITE_CONST2",
   ``!P. FINITE P ==>
        !f x. (!y. y IN P ==> (f y = x)) ==> (REAL_SUM_IMAGE f P = (&(CARD P)) * x)``,
   REPEAT STRIP_TAC
   >> (MP_TAC o Q.SPECL [`P`]) REAL_SUM_IMAGE_FINITE_SAME
   >> RW_TAC std_ss []
   >> POP_ASSUM (MP_TAC o (Q.SPECL [`f`]))
   >> RW_TAC std_ss []
   >> (MP_TAC o Q.SPECL [`P`]) SET_CASES
   >> RW_TAC std_ss [] >- RW_TAC real_ss [REAL_SUM_IMAGE_THM, CARD_EMPTY]
   >> POP_ASSUM (K ALL_TAC)
   >> POP_ASSUM MATCH_MP_TAC
   >> Q.EXISTS_TAC `x'` >> RW_TAC std_ss [IN_INSERT]);

Theorem REAL_SUM_IMAGE_FINITE_CONST3 :
    !P. FINITE P ==>
        !c. (REAL_SUM_IMAGE (\x. c) P = (&(CARD P)) * c)
Proof
    rw [REAL_SUM_IMAGE_sum, SUM_CONST]
QED

val REAL_SUM_IMAGE_IN_IF_lem = prove
  (``!P. FINITE P ==>
                (\P.!f. REAL_SUM_IMAGE f P = REAL_SUM_IMAGE (\x. if x IN P then f x else 0) P) P``,
   MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC real_ss [REAL_SUM_IMAGE_THM]
   >> POP_ASSUM MP_TAC
   >> ONCE_REWRITE_TAC [DELETE_NON_ELEMENT]
   >> SIMP_TAC real_ss [IN_INSERT]
   >> `REAL_SUM_IMAGE (\x. (if (x = e) \/ x IN s then f x else 0)) s =
       REAL_SUM_IMAGE (\x. (if x IN s then f x else 0)) s`
        by (POP_ASSUM (MP_TAC o Q.SPECL [`(\x. (if (x = e) \/ x IN s then f x else 0))`])
            >> RW_TAC std_ss [])
   >> POP_ORW
   >> POP_ASSUM (MP_TAC o Q.SPECL [`f`])
   >> RW_TAC real_ss []);

val REAL_SUM_IMAGE_IN_IF = store_thm
  ("REAL_SUM_IMAGE_IN_IF",
   ``!P. FINITE P ==>
        !f. REAL_SUM_IMAGE f P = REAL_SUM_IMAGE (\x. if x IN P then f x else 0) P``,
   METIS_TAC [REAL_SUM_IMAGE_IN_IF_lem]);

Theorem REAL_SUM_IMAGE_CMUL :
    !P. FINITE P ==>
        !f c. (REAL_SUM_IMAGE (\x. c * f x) P = c * (REAL_SUM_IMAGE f P))
Proof
    rw [REAL_SUM_IMAGE_sum, SUM_LMUL]
QED

Theorem REAL_SUM_IMAGE_NEG :
    !P. FINITE P ==>
        !f. (REAL_SUM_IMAGE (\x. ~ f x) P = ~ (REAL_SUM_IMAGE f P))
Proof
    rw [REAL_SUM_IMAGE_sum, SUM_NEG']
QED

Theorem REAL_SUM_IMAGE_IMAGE :
    !P. FINITE P ==>
        !f'. INJ f' P (IMAGE f' P) ==>
             !f. REAL_SUM_IMAGE f (IMAGE f' P) = REAL_SUM_IMAGE (f o f') P
Proof
    rw [REAL_SUM_IMAGE_sum, INJ_DEF]
 >> MATCH_MP_TAC SUM_IMAGE >> rw []
QED

Theorem REAL_SUM_IMAGE_DISJOINT_UNION :
    !P P'. FINITE P /\ FINITE P' /\ DISJOINT P P' ==>
                (!f. REAL_SUM_IMAGE f (P UNION P') =
                     REAL_SUM_IMAGE f P +
                     REAL_SUM_IMAGE f P')
Proof
    rw [REAL_SUM_IMAGE_sum]
 >> MATCH_MP_TAC SUM_UNION
 >> rw [GSYM DISJOINT_DEF, FINITE_UNION]
QED

val REAL_SUM_IMAGE_EQ_CARD_lem = prove
   (``!P. FINITE P ==>
        (\P. REAL_SUM_IMAGE (\x. if x IN P then 1 else 0) P = (&(CARD P))) P``,
   MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC real_ss [REAL_SUM_IMAGE_THM, CARD_EMPTY, IN_INSERT]
   >> (MP_TAC o Q.SPECL [`s`]) CARD_INSERT
   >> RW_TAC real_ss [ADD1] >> ONCE_REWRITE_TAC [GSYM REAL_ADD]
   >> Suff `REAL_SUM_IMAGE (\x. (if (x = e) \/ x IN s then 1 else 0)) (s DELETE e) =
                REAL_SUM_IMAGE (\x. (if x IN s then 1 else 0)) s`
   >- RW_TAC real_ss []
   >> Q.PAT_ASSUM `REAL_SUM_IMAGE (\x. (if x IN s then 1 else 0)) s = & (CARD s)` (K ALL_TAC)
   >> FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
   >> `REAL_SUM_IMAGE (\x. (if (x = e) \/ x IN s then 1 else 0)) s =
       REAL_SUM_IMAGE (\x. if x IN s then (\x. (if (x = e) \/ x IN s then 1 else 0)) x else 0) s`
        by (METIS_TAC [REAL_SUM_IMAGE_IN_IF])
   >> RW_TAC std_ss []);

val REAL_SUM_IMAGE_EQ_CARD = store_thm
  ("REAL_SUM_IMAGE_EQ_CARD",
   ``!P. FINITE P ==>
        (REAL_SUM_IMAGE (\x. if x IN P then 1 else 0) P = (&(CARD P)))``,
   METIS_TAC [REAL_SUM_IMAGE_EQ_CARD_lem]);

val REAL_SUM_IMAGE_INV_CARD_EQ_1 = store_thm
  ("REAL_SUM_IMAGE_INV_CARD_EQ_1",
   ``!P. (~(P = {})) /\ FINITE P ==>
                (REAL_SUM_IMAGE (\s. if s IN P then inv (& (CARD P)) else 0) P = 1)``,
    REPEAT STRIP_TAC
    >> `(\s. if s IN P then inv (& (CARD P)) else 0) = (\s. inv (& (CARD P)) * (\s. if s IN P then 1 else 0) s)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [])
    >> POP_ORW
    >> `REAL_SUM_IMAGE (\s. inv (& (CARD P)) * (\s. (if s IN P then 1 else 0)) s) P =
        (inv (& (CARD P))) * (REAL_SUM_IMAGE (\s. (if s IN P then 1 else 0)) P)`
                by (MATCH_MP_TAC REAL_SUM_IMAGE_CMUL >> RW_TAC std_ss [])
    >> POP_ORW
    >> `REAL_SUM_IMAGE (\s. (if s IN P then 1 else 0)) P = (&(CARD P))`
                by (MATCH_MP_TAC REAL_SUM_IMAGE_EQ_CARD >> RW_TAC std_ss [])
    >> POP_ORW
    >> MATCH_MP_TAC REAL_MUL_LINV
    >> RW_TAC real_ss []
    >> METIS_TAC [CARD_EQ_0]);

val REAL_SUM_IMAGE_INTER_NONZERO_lem = prove
  (``!P. FINITE P ==>
        (\P. !f. REAL_SUM_IMAGE f (P INTER (\p. ~(f p = 0))) =
                 REAL_SUM_IMAGE f P) P``,
   MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC std_ss [REAL_SUM_IMAGE_THM, INTER_EMPTY, INSERT_INTER]
   >> FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
   >> (RW_TAC std_ss [IN_DEF] >> RW_TAC real_ss [])
   >> `FINITE (s INTER (\p. ~(f p = 0)))` by (MATCH_MP_TAC INTER_FINITE >> RW_TAC std_ss [])
   >> RW_TAC std_ss [REAL_SUM_IMAGE_THM]
   >> FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]
   >> `~(e IN (s INTER (\p. ~(f p = 0))))`
        by RW_TAC std_ss [IN_INTER]
   >> FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]);

val REAL_SUM_IMAGE_INTER_NONZERO = store_thm
  ("REAL_SUM_IMAGE_INTER_NONZERO",
   ``!P. FINITE P ==>
        !f. REAL_SUM_IMAGE f (P INTER (\p. ~(f p = 0))) =
                 REAL_SUM_IMAGE f P``,
   METIS_TAC [REAL_SUM_IMAGE_INTER_NONZERO_lem]);

val REAL_SUM_IMAGE_INTER_ELIM_lem = prove
  (``!P. FINITE P ==>
        (\P. !f P'. (!x. (~(x IN P')) ==> (f x = 0)) ==>
                        (REAL_SUM_IMAGE f (P INTER P') =
                         REAL_SUM_IMAGE f P)) P``,
   MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC std_ss [INTER_EMPTY, REAL_SUM_IMAGE_THM, INSERT_INTER]
   >> Cases_on `e IN P'`
   >- (`~ (e IN (s INTER P'))` by RW_TAC std_ss [IN_INTER]
       >> FULL_SIMP_TAC std_ss [INTER_FINITE, REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT])
   >> FULL_SIMP_TAC real_ss []
   >> FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]);

val REAL_SUM_IMAGE_INTER_ELIM = store_thm
  ("REAL_SUM_IMAGE_INTER_ELIM",
   ``!P. FINITE P ==>
         !f P'. (!x. (~(x IN P')) ==> (f x = 0)) ==>
                        (REAL_SUM_IMAGE f (P INTER P') =
                         REAL_SUM_IMAGE f P)``,
   METIS_TAC [REAL_SUM_IMAGE_INTER_ELIM_lem]);

val REAL_SUM_IMAGE_COUNT = store_thm
  ("REAL_SUM_IMAGE_COUNT",
   ``!f n. REAL_SUM_IMAGE f (pred_set$count n) =
           sum (0,n) f``,
   STRIP_TAC >> Induct
   >- RW_TAC std_ss [pred_setTheory.count_def, REAL_SUM_IMAGE_THM, GSPEC_F, sum]
   >> `pred_set$count (SUC n) = n INSERT pred_set$count n`
        by (RW_TAC std_ss [EXTENSION, IN_INSERT, pred_setTheory.IN_COUNT] >> DECIDE_TAC)
   >> RW_TAC std_ss [REAL_SUM_IMAGE_THM, sum, pred_setTheory.FINITE_COUNT]
   >> `pred_set$count n DELETE n = pred_set$count n`
        by RW_TAC arith_ss [DELETE_DEF, DIFF_DEF, IN_SING, pred_setTheory.IN_COUNT,
                            Once EXTENSION, pred_setTheory.IN_COUNT, GSPECIFICATION,
                            DECIDE ``!(x:num) (y:num). x < y ==> ~(x = y)``]
   >> RW_TAC std_ss [REAL_ADD_SYM]);

Theorem REAL_SUM_IMAGE_MONO :
    !P. FINITE P ==>
        !f f'. (!x. x IN P ==> f x <= f' x) ==>
               REAL_SUM_IMAGE f P <= REAL_SUM_IMAGE f' P
Proof
    rw [REAL_SUM_IMAGE_sum]
 >> MATCH_MP_TAC SUM_LE' >> rw []
QED

(* |- !f g s.
        FINITE s /\ (!x. x IN s ==> f x <= g x) /\ (?x. x IN s /\ f x < g x) ==>
        SIGMA f s < SIGMA g s
 *)
Theorem REAL_SUM_IMAGE_MONO_LT = translate SUM_LT'

val REAL_SUM_IMAGE_POS_MEM_LE = store_thm
  ("REAL_SUM_IMAGE_POS_MEM_LE",
   ``!P. FINITE P ==>
        !f. (!x. x IN P ==> 0 <= f x) ==>
            (!x. x IN P ==> f x <= REAL_SUM_IMAGE f P)``,
   Suff `!P. FINITE P ==>
        (\P. !f. (!x. x IN P ==> 0 <= f x) ==>
            (!x. x IN P ==> f x <= REAL_SUM_IMAGE f P)) P`
   >- PROVE_TAC []
   >> MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC std_ss [REAL_SUM_IMAGE_THM, NOT_IN_EMPTY, IN_INSERT,
                     DISJ_IMP_THM, FORALL_AND_THM,
                     DELETE_NON_ELEMENT]
   >- (Suff `f e + 0 <= f e + REAL_SUM_IMAGE f s` >- RW_TAC real_ss []
       >> MATCH_MP_TAC REAL_LE_LADD_IMP
       >> MATCH_MP_TAC REAL_SUM_IMAGE_POS >> ASM_REWRITE_TAC [])
   >> Suff `0 + f x <= f e + REAL_SUM_IMAGE f s` >- RW_TAC real_ss []
   >> MATCH_MP_TAC REAL_LE_ADD2 >> PROVE_TAC []);

val REAL_SUM_IMAGE_CONST_EQ_1_EQ_INV_CARD = store_thm
  ("REAL_SUM_IMAGE_CONST_EQ_1_EQ_INV_CARD",
   ``!P. FINITE P ==>
        !f. (REAL_SUM_IMAGE f P = 1) /\
            (!x y. x IN P /\ y IN P ==> (f x = f y)) ==>
            (!x. x IN P ==> (f x = inv (& (CARD P))))``,
   Suff `!P. FINITE P ==>
        (\P. !f. (REAL_SUM_IMAGE f P = 1) /\
            (!x y. x IN P /\ y IN P ==> (f x = f y)) ==>
            (!x. x IN P ==> (f x = inv (& (CARD P))))) P`
  >- RW_TAC std_ss []
  >> MATCH_MP_TAC FINITE_INDUCT
  >> RW_TAC real_ss [REAL_SUM_IMAGE_THM, IN_INSERT, DELETE_NON_ELEMENT]
  >- (RW_TAC std_ss [(UNDISCH o Q.SPEC `s`) CARD_INSERT]
      >> FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]
      >> Q.PAT_ASSUM `(f:'a->real) e + REAL_SUM_IMAGE f s = 1`
        (MP_TAC o REWRITE_RULE [Once ((UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_IN_IF)])
      >> `(\x:'a. (if (x IN s) then (f:'a -> real) x else (0:real))) =
               (\x:'a. (if (x IN s) then (\x:'a. (f:'a -> real) e) x else (0:real)))`
        by METIS_TAC []
      >> POP_ORW
      >> ONCE_REWRITE_TAC [(GSYM o UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_IN_IF]
      >> (MP_TAC o Q.SPECL [`(\x. (f:'a->real) e)`, `(f:'a->real) e`] o
          UNDISCH o Q.ISPEC `s:'a -> bool`) REAL_SUM_IMAGE_FINITE_CONST
      >> SIMP_TAC std_ss []
      >> STRIP_TAC >> POP_ASSUM (K ALL_TAC)
      >> `f e + & (CARD s) * f e = f e *( & (CARD s) + 1)` by REAL_ARITH_TAC
      >> POP_ORW
      >> `1:real = &1` by RW_TAC real_ss []
      >> POP_ASSUM (fn thm => SIMP_TAC std_ss [thm, REAL_OF_NUM_ADD, GSYM ADD1])
      >> REPEAT (POP_ASSUM (K ALL_TAC))
      >> METIS_TAC [REAL_NZ_IMP_LT, GSYM REAL_EQ_RDIV_EQ, REAL_INV_1OVER, SUC_NOT])
   >> FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]
   >> RW_TAC std_ss [(UNDISCH o Q.SPEC `s`) CARD_INSERT]
   >> Q.PAT_ASSUM `f e + REAL_SUM_IMAGE f s = 1`
        (MP_TAC o REWRITE_RULE [Once ((UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_IN_IF)])
   >> `(\x:'a. (if (x IN s) then (f:'a -> real) x else (0:real))) =
               (\x:'a. (if (x IN s) then (\x:'a. (f:'a -> real) e) x else (0:real)))`
        by METIS_TAC []
   >> POP_ORW
   >> ONCE_REWRITE_TAC [(GSYM o UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_IN_IF]
   >> (MP_TAC o Q.SPECL [`(\x. (f:'a->real) e)`, `(f:'a->real) e`] o
          UNDISCH o Q.ISPEC `s:'a -> bool`) REAL_SUM_IMAGE_FINITE_CONST
   >> SIMP_TAC std_ss []
   >> STRIP_TAC >> POP_ASSUM (K ALL_TAC)
   >> `f e + & (CARD s) * f e = f e *( & (CARD s) + 1)` by REAL_ARITH_TAC
   >> POP_ORW
   >> `1:real = &1` by RW_TAC real_ss []
   >> POP_ASSUM (fn thm => SIMP_TAC std_ss [thm, REAL_OF_NUM_ADD, GSYM ADD1])
   >> `f x = f e` by METIS_TAC [] >> POP_ORW
   >> REPEAT (POP_ASSUM (K ALL_TAC))
   >> METIS_TAC [REAL_NZ_IMP_LT, GSYM REAL_EQ_RDIV_EQ, REAL_INV_1OVER, SUC_NOT]);

Theorem REAL_SUM_IMAGE_ADD :
    !s. FINITE s ==>
        !f f'. REAL_SUM_IMAGE (\x. f x + f' x) s =
               REAL_SUM_IMAGE f s + REAL_SUM_IMAGE f' s
Proof
    rw [REAL_SUM_IMAGE_sum, SUM_ADD']
QED

val REAL_SUM_IMAGE_REAL_SUM_IMAGE = store_thm
  ("REAL_SUM_IMAGE_REAL_SUM_IMAGE",
   ``!s s' f. FINITE s /\ FINITE s' ==>
        (REAL_SUM_IMAGE (\x. REAL_SUM_IMAGE (f x) s') s =
         REAL_SUM_IMAGE (\x. f (FST x) (SND x)) (s CROSS s'))``,
   Suff `!s. FINITE s ==>
             (\s. !s' f. FINITE s' ==>
        (REAL_SUM_IMAGE (\x. REAL_SUM_IMAGE (f x) s') s =
         REAL_SUM_IMAGE (\x. f (FST x) (SND x)) (s CROSS s'))) s`
   >- RW_TAC std_ss []
   >> MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC std_ss [CROSS_EMPTY, REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT]
   >> `((e INSERT s) CROSS s') = (IMAGE (\x. (e,x)) s') UNION (s CROSS s')`
        by (RW_TAC std_ss [Once EXTENSION, IN_INSERT, IN_SING, IN_CROSS, IN_UNION, IN_IMAGE]
            >> (MP_TAC o Q.ISPEC `x:'a#'b`) pair_CASES
            >> RW_TAC std_ss [] >> FULL_SIMP_TAC std_ss [FST,SND, GSYM DELETE_NON_ELEMENT]
            >> METIS_TAC [])
   >> POP_ORW
   >> `DISJOINT (IMAGE (\x. (e,x)) s') (s CROSS s')`
        by (FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT, DISJOINT_DEF, Once EXTENSION,
                                  NOT_IN_EMPTY, IN_INTER, IN_CROSS, IN_SING, IN_IMAGE]
            >> STRIP_TAC >> (MP_TAC o Q.ISPEC `x:'a#'b`) pair_CASES
            >> RW_TAC std_ss [FST, SND]
            >> METIS_TAC [])
   >> (MP_TAC o REWRITE_RULE [GSYM AND_IMP_INTRO] o
        Q.ISPECL [`IMAGE (\x. (e:'a,x)) (s':'b->bool)`, `(s:'a->bool) CROSS (s':'b->bool)`])
        REAL_SUM_IMAGE_DISJOINT_UNION
   >> RW_TAC std_ss [FINITE_CROSS, IMAGE_FINITE]
   >> POP_ASSUM (K ALL_TAC)
   >> (MP_TAC o Q.SPEC `(\x. (e,x))` o UNDISCH o Q.SPEC `s'` o
        INST_TYPE [``:'c``|->``:'a # 'b``] o INST_TYPE [``:'a``|->``:'b``] o
        INST_TYPE [``:'b``|->``:'c``]) REAL_SUM_IMAGE_IMAGE
   >> RW_TAC std_ss [INJ_DEF, IN_IMAGE, o_DEF] >> METIS_TAC []);

Theorem REAL_SUM_IMAGE_0 :
    !s. FINITE s ==> (REAL_SUM_IMAGE (\x. 0) s = 0)
Proof
    rw [REAL_SUM_IMAGE_sum, SUM_0']
QED

val NESTED_REAL_SUM_IMAGE_REVERSE = store_thm
  ("NESTED_REAL_SUM_IMAGE_REVERSE",
   ``!f s s'. FINITE s /\ FINITE s' ==>
                (REAL_SUM_IMAGE (\x. REAL_SUM_IMAGE (f x) s') s =
                 REAL_SUM_IMAGE (\x. REAL_SUM_IMAGE (\y. f y x) s) s')``,
   RW_TAC std_ss [REAL_SUM_IMAGE_REAL_SUM_IMAGE]
   >> `(s' CROSS s) = IMAGE (\x. (SND x, FST x)) (s CROSS s')`
        by (RW_TAC std_ss [EXTENSION, IN_CROSS, IN_IMAGE]
            >> EQ_TAC >- (STRIP_TAC >> Q.EXISTS_TAC `(SND x, FST x)` >> RW_TAC std_ss [PAIR])
            >> RW_TAC std_ss [] >> RW_TAC std_ss [FST, SND])
   >> POP_ORW
   >> `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
   >> `INJ (\x. (SND x,FST x)) (s CROSS s') (IMAGE (\x. (SND x,FST x)) (s CROSS s'))`
        by (RW_TAC std_ss [INJ_DEF, IN_IMAGE] >- METIS_TAC []
            >> METIS_TAC [PAIR, PAIR_EQ])
   >> `REAL_SUM_IMAGE (\x. f (SND x) (FST x)) (IMAGE (\x. (SND x,FST x)) (s CROSS s')) =
       REAL_SUM_IMAGE ((\x. f (SND x) (FST x)) o (\x. (SND x,FST x))) (s CROSS s')`
        by METIS_TAC [REAL_SUM_IMAGE_IMAGE]
   >> POP_ORW
   >> RW_TAC std_ss [o_DEF]);

val REAL_SUM_IMAGE_EQ_sum = store_thm
("REAL_SUM_IMAGE_EQ_sum", ``!n r. sum (0,n) r = REAL_SUM_IMAGE r (count n)``,
  RW_TAC std_ss []
  >> Induct_on `n`
  >- RW_TAC std_ss [sum,REAL_SUM_IMAGE_THM,COUNT_ZERO]
  >> RW_TAC std_ss [sum,COUNT_SUC,REAL_SUM_IMAGE_THM,FINITE_COUNT]
  >> Suff `count n DELETE n = count n`
  >- RW_TAC std_ss [REAL_ADD_COMM]
  >> RW_TAC std_ss [GSYM DELETE_NON_ELEMENT,IN_COUNT]);

val REAL_SUM_IMAGE_POW = store_thm
 ("REAL_SUM_IMAGE_POW",``!a s. FINITE s
           ==> ((REAL_SUM_IMAGE a s) pow 2 =
                REAL_SUM_IMAGE (\(i,j). a i * a j) (s CROSS s):real)``,
  RW_TAC std_ss []
  >> `(\(i,j). a i * a j) = (\x. (\i j. a i * a j) (FST x) (SND x))`
       by (RW_TAC std_ss [FUN_EQ_THM]
           >> Cases_on `x`
           >> RW_TAC std_ss [])
  >> POP_ORW
  >> (MP_TAC o GSYM o Q.SPECL [`s`,`s`,`(\i j. a i * a j)`] o
          INST_TYPE [``:'b`` |-> ``:'a``]) REAL_SUM_IMAGE_REAL_SUM_IMAGE
  >> RW_TAC std_ss [REAL_SUM_IMAGE_CMUL]
  >> RW_TAC std_ss [Once REAL_MUL_COMM,REAL_SUM_IMAGE_CMUL,POW_2]);

Theorem REAL_SUM_IMAGE_EQ :
    !s (f:'a->real) f'. FINITE s /\ (!x. x IN s ==> (f x = f' x))
                    ==> (REAL_SUM_IMAGE f s = REAL_SUM_IMAGE f' s)
Proof
    rw [REAL_SUM_IMAGE_sum, SUM_EQ']
QED

val REAL_SUM_IMAGE_IN_IF_ALT = store_thm
  ("REAL_SUM_IMAGE_IN_IF_ALT",``!s f z:real.
         FINITE s ==> (REAL_SUM_IMAGE f s = REAL_SUM_IMAGE (\x. if x IN s then f x else z) s)``,
  RW_TAC std_ss []
  >> MATCH_MP_TAC REAL_SUM_IMAGE_EQ
  >> RW_TAC std_ss []);

Theorem REAL_SUM_IMAGE_SUB :
    !s (f:'a -> real) f'. FINITE s ==>
                 (REAL_SUM_IMAGE (\x. f x - f' x) s =
                  REAL_SUM_IMAGE f s - REAL_SUM_IMAGE f' s)
Proof
    rw [REAL_SUM_IMAGE_sum, SUM_SUB']
QED

val REAL_SUM_IMAGE_MONO_SET = store_thm
 ("REAL_SUM_IMAGE_MONO_SET", ``!(f:'a -> real) s t.
         FINITE s /\ FINITE t /\ s SUBSET t /\ (!x. x IN t ==> 0 <= f x)
              ==> REAL_SUM_IMAGE f s <= REAL_SUM_IMAGE f t``,
  RW_TAC std_ss []
  >> `t = s UNION (t DIFF s)` by RW_TAC std_ss [UNION_DIFF]
  >> `FINITE (t DIFF s)` by RW_TAC std_ss [FINITE_DIFF]
  >> `DISJOINT s (t DIFF s)` by (
        RW_TAC std_ss [DISJOINT_DEF,IN_DIFF,EXTENSION,GSPECIFICATION,
                       NOT_IN_EMPTY,IN_INTER] >-
        METIS_TAC [])
  >> `REAL_SUM_IMAGE f t = REAL_SUM_IMAGE f s + REAL_SUM_IMAGE f (t DIFF s)`
      by METIS_TAC [REAL_SUM_IMAGE_DISJOINT_UNION]
  >> POP_ORW
  >> Suff `0 <= REAL_SUM_IMAGE f (t DIFF s)`
  >- REAL_ARITH_TAC
  >> METIS_TAC [REAL_SUM_IMAGE_POS,IN_DIFF]);

val REAL_SUM_IMAGE_CROSS_SYM = store_thm
 ("REAL_SUM_IMAGE_CROSS_SYM", ``!f s1 s2. FINITE s1 /\ FINITE s2 ==>
   (REAL_SUM_IMAGE (\(x,y). f (x,y)) (s1 CROSS s2) = REAL_SUM_IMAGE (\(y,x). f (x,y)) (s2 CROSS s1))``,
  RW_TAC std_ss []
  >> `s2 CROSS s1 = IMAGE (\a. (SND a, FST a)) (s1 CROSS s2)`
        by (RW_TAC std_ss [IN_IMAGE, IN_CROSS,EXTENSION] >> METIS_TAC [FST,SND,PAIR])
  >> POP_ORW
  >> `INJ (\a. (SND a, FST a)) (s1 CROSS s2) (IMAGE (\a. (SND a, FST a)) (s1 CROSS s2))`
       by (RW_TAC std_ss [INJ_DEF, IN_IMAGE, IN_CROSS]
           >> METIS_TAC [FST,SND,PAIR])
  >> RW_TAC std_ss [REAL_SUM_IMAGE_IMAGE, IMAGE_FINITE, FINITE_CROSS, o_DEF]
  >> `(\(x,y). f (x,y)) = (\a. f a)`
       by (RW_TAC std_ss [FUN_EQ_THM]
           >> Cases_on `a`
           >> RW_TAC std_ss [])
  >> RW_TAC std_ss []);

Theorem REAL_SUM_IMAGE_ABS_TRIANGLE :
    !f s. FINITE s ==> abs (REAL_SUM_IMAGE f s) <= REAL_SUM_IMAGE (abs o f) s
Proof
    rw [REAL_SUM_IMAGE_sum, SUM_ABS', o_DEF]
QED

Theorem REAL_SUM_IMAGE_DELETE = translate SUM_DELETE
Theorem REAL_SUM_IMAGE_SWAP = translate SUM_SWAP
Theorem REAL_SUM_IMAGE_BOUND = translate SUM_BOUND'

Theorem REAL_SUM_IMAGE_IMAGE_LE :
    !f:'a->'b g s.
        FINITE s /\
        (!x. x IN s ==> (0:real) <= g (f x))
        ==> REAL_SUM_IMAGE g (IMAGE f s) <= REAL_SUM_IMAGE (g o f) s
Proof
    rpt STRIP_TAC
 >> ‘FINITE (IMAGE f s)’ by METIS_TAC [IMAGE_FINITE]
 >> rw [REAL_SUM_IMAGE_sum]
 >> MATCH_MP_TAC SUM_IMAGE_LE >> art []
QED

Theorem REAL_SUM_IMAGE_PERMUTES :
    !f p s:'a->bool. FINITE s /\ p PERMUTES s ==>
                     REAL_SUM_IMAGE f s = REAL_SUM_IMAGE (f o p) s
Proof
    rw [BIJ_ALT, REAL_SUM_IMAGE_sum, IN_FUNSET]
 >> MATCH_MP_TAC SUM_BIJECTION >> rw []
 >> Q.PAT_X_ASSUM ‘!y. y IN s ==> ?!x. P’ (MP_TAC o Q.SPEC ‘y’)
 >> RW_TAC bool_ss [EXISTS_UNIQUE_DEF] (* why it takes so long time? *)
 >> Q.EXISTS_TAC ‘x’ >> art []
QED

(* ------------------------------------------------------------------------- *)
(* Analogous notion of finite products                                       *)
(*   (generally for use in descendent theories)                              *)
(* ------------------------------------------------------------------------- *)

Definition REAL_PROD_IMAGE_DEF:
    REAL_PROD_IMAGE f s = ITSET (λe acc. f e * acc) s (1:real)
End

Overload PI = “REAL_PROD_IMAGE”
val _ = Unicode.unicode_version {u = UTF8.chr 0x220F, tmnm = "PI"};

Theorem REAL_PROD_IMAGE_EMPTY[simp]:
    !(f:'a -> real). REAL_PROD_IMAGE f EMPTY = 1
Proof
    simp[REAL_PROD_IMAGE_DEF]
QED

Theorem REAL_PROD_IMAGE_INSERT:
    !(f:'a -> real) e s. FINITE s ==>
        REAL_PROD_IMAGE f (e INSERT s) = f e * REAL_PROD_IMAGE f (s DELETE e)
Proof
    rw[REAL_PROD_IMAGE_DEF] >>
    qspecl_then [‘λe acc. f e * acc’,‘e’,‘s’,‘1r’]
        (irule o SIMP_RULE (srw_ss ()) []) COMMUTING_ITSET_RECURSES >>
    simp[]
QED

Theorem REAL_PROD_IMAGE_THM:
    !f. REAL_PROD_IMAGE f EMPTY = 1r /\
        !e s. FINITE s ==> REAL_PROD_IMAGE f (e INSERT s) = f e * REAL_PROD_IMAGE f (s DELETE e)
Proof
    simp[REAL_PROD_IMAGE_EMPTY,REAL_PROD_IMAGE_INSERT]
QED

Theorem REAL_PROD_IMAGE_SING[simp]:
    !f e. REAL_PROD_IMAGE f {e} = f e
Proof
    SRW_TAC [][REAL_PROD_IMAGE_THM]
QED

(* ------------------------------------------------------------------------- *)
(* ---- jensen's inequality (from "miller" example)             ------------ *)
(* ------------------------------------------------------------------------- *)

Definition convex_fn :
    convex_fn =
      {f | !x y t. (0 <= t /\ t <= 1) ==>
                   f (t * x + (1 - t) * y) <= t * f x + (1 - t) * f y}
End

Definition concave_fn :
    concave_fn = {f | (\x. ~(f x)) IN convex_fn}
End

Definition pos_convex_fn :
    pos_convex_fn = {f | !x y t. (0 < x /\ 0 < y /\ 0 <= t /\ t <= 1) ==>
                                 f (t * x + (1 - t) * y) <= t * f x + (1 - t) * f y}
End

Definition pos_concave_fn :
    pos_concave_fn = {f | (\x. ~ (f x)) IN pos_convex_fn}
End

val jensen_convex_SIGMA = store_thm
  ("jensen_convex_SIGMA",
   ``!s. FINITE s ==>
         !f g g'. (SIGMA g s = 1) /\
                  (!x. x IN s ==> 0 <= g x /\ g x <= 1) /\
                  f IN convex_fn ==>
                        f (SIGMA (\x. g x * g' x) s) <= SIGMA (\x. g x * f (g' x)) s``,
   Suff `!s. FINITE s ==>
             (\s. !f g g'. (SIGMA g s = 1) /\
                  (!x. x IN s ==> 0 <= g x /\ g x <= 1) /\
                  f IN convex_fn ==>
                        f (SIGMA (\x. g x * g' x) s) <= SIGMA (\x. g x * f (g' x)) s) s`
   >- RW_TAC std_ss []
   >> MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC real_ss [REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT, IN_INSERT, DISJ_IMP_THM, FORALL_AND_THM]
   >> Cases_on `g e = 0` >- FULL_SIMP_TAC real_ss []
   >> Cases_on `g e = 1`
   >- ( FULL_SIMP_TAC real_ss []
        >> Know `!s. FINITE s ==>
                (\s. !g. (SIGMA g s = 0) /\ (!x. x IN s ==> 0 <= g x /\ g x <= 1) ==>
                            (!x. x IN s ==> (g x = 0))) s`
        >- (MATCH_MP_TAC FINITE_INDUCT \\
            RW_TAC real_ss [REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT, IN_INSERT, DISJ_IMP_THM,
                            FORALL_AND_THM, NOT_IN_EMPTY] >| (* 2 sub-goals *)
            [ (* goal 1 (of 2) *)
              Know `!(x:real) y. 0 <= x /\ 0 <= y /\ (x + y = 0) ==> ((x = 0) /\ (y = 0))`
              >- REAL_ARITH_TAC
              >> PROVE_TAC [REAL_SUM_IMAGE_POS],
              (* goal 2 (of 2) *)
              Know `!(x:real) y. 0 <= x /\ 0 <= y /\ (x + y = 0) ==> ((x = 0) /\ (y = 0))`
              >- REAL_ARITH_TAC
              >> Q.PAT_X_ASSUM `!g. (SIGMA g s' = 0) /\ (!x. x IN s' ==> 0 <= g x /\ g x <= 1) ==>
                                !x. x IN s' ==> (g x = 0)`
                (MP_TAC o Q.SPEC `g'`)
              >> PROVE_TAC [REAL_SUM_IMAGE_POS] ])
        >> Know `!x:real. (1 + x = 1) = (x = 0)` >- REAL_ARITH_TAC
        >> STRIP_TAC >> FULL_SIMP_TAC real_ss []
        >> POP_ASSUM (K ALL_TAC)
        >> (ASSUME_TAC o UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_IN_IF
        >> POP_ORW
        >> DISCH_TAC
        >> POP_ASSUM (ASSUME_TAC o UNDISCH_ALL o (REWRITE_RULE [GSYM AND_IMP_INTRO]) o
                      (Q.SPEC `g`) o UNDISCH o (Q.SPEC `s`))
        >> `(\x. (if x IN s then (\x. g x * g' x) x else 0)) = (\x. 0)`
                by RW_TAC real_ss [FUN_EQ_THM]
        >> POP_ORW
        >> `(\x. (if x IN s then (\x. g x * f (g' x)) x else 0)) = (\x. 0)`
                by RW_TAC real_ss [FUN_EQ_THM]
        >> POP_ORW
        >> Suff `SIGMA (\x. 0) s = 0` >- RW_TAC real_ss []
        >> (MP_TAC o Q.SPECL [`(\x. 0)`, `0`] o
                UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_FINITE_CONST
        >> RW_TAC real_ss [])

   >> Suff `(SIGMA (\x. g x * g' x) s = (1 - g e) * SIGMA (\x. (g x / (1 - g e)) * g' x) s) /\
            (SIGMA (\x. g x * f(g' x)) s = (1 - g e) * SIGMA (\x. (g x / (1 - g e)) * f(g' x)) s)`
   >- (RW_TAC std_ss [] >> FULL_SIMP_TAC std_ss [convex_fn, GSPECIFICATION]
       >> Q.PAT_X_ASSUM `!f' g'' g'''.
        (SIGMA g'' s = 1) /\
        (!x. x IN s ==> 0 <= g'' x /\ g'' x <= 1) /\
        (!x y t.
           0 <= t /\ t <= 1 ==>
           f' (t * x + (1 - t) * y) <= t * f' x + (1 - t) * f' y) ==>
        f' (SIGMA (\x. g'' x * g''' x) s) <=
        SIGMA (\x. g'' x * f' (g''' x)) s` (MP_TAC o Q.SPECL [`f`, `(\x. g x / (1 - g e))`, `g'`])
       >> RW_TAC std_ss []
       >> Q.PAT_X_ASSUM `!x y t. P`
                (MP_TAC o Q.SPECL [`g' e`, `SIGMA (\x. g x / (1 - g e) * g' x) s`, `g e`])
       >> RW_TAC std_ss []
       >> MATCH_MP_TAC REAL_LE_TRANS
       >> Q.EXISTS_TAC `g e * f (g' e) + (1 - g e) * f (SIGMA (\x. g x / (1 - g e) * g' x) s)`
       >> RW_TAC real_ss [REAL_LE_LADD]
       >> Cases_on `g e = 1` >- RW_TAC real_ss []
       >> Know `0 < 1 - g e`
       >- (Q.PAT_X_ASSUM `g e <= 1` MP_TAC >> Q.PAT_X_ASSUM `~ (g e = 1)` MP_TAC >> REAL_ARITH_TAC)
       >> STRIP_TAC
       >> Suff `f (SIGMA (\x. g x / (1 - g e) * g' x) s) <=
                SIGMA (\x. g x / (1 - g e) * f (g' x)) s`
       >- PROVE_TAC [REAL_LE_LMUL]
       >> Q.PAT_X_ASSUM `(SIGMA (\x. g x / (1 - g e)) s = 1) /\
                        (!x. x IN s ==> 0 <= g x / (1 - g e) /\ g x / (1 - g e) <= 1) ==>
                        f (SIGMA (\x. g x / (1 - g e) * g' x) s) <=
                        SIGMA (\x. g x / (1 - g e) * f (g' x)) s` MATCH_MP_TAC
       >> CONJ_TAC
       >- ((MP_TAC o Q.SPECL [`g`, `inv (1- g e)`] o UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_CMUL
           >> RW_TAC real_ss [real_div] >> ASM_REWRITE_TAC [Once REAL_MUL_COMM]
           >> RW_TAC std_ss [Once REAL_MUL_COMM, GSYM real_div]
           >> Suff `SIGMA g s = 1 * (1 - g e)`
           >- PROVE_TAC [REAL_EQ_LDIV_EQ]
           >> Q.PAT_X_ASSUM `g e + SIGMA g s = 1` MP_TAC
           >> REAL_ARITH_TAC)
       >> RW_TAC std_ss [] >- PROVE_TAC [REAL_LE_DIV, REAL_LT_IMP_LE]
       >> Suff `g x <= 1 * (1 - g e)` >- PROVE_TAC [REAL_LE_LDIV_EQ]
       >> Suff `g e + g x <= 1` >- REAL_ARITH_TAC
       >> Q.PAT_X_ASSUM `g e + SIGMA g s = 1` (fn thm => ONCE_REWRITE_TAC [GSYM thm])
       >> MATCH_MP_TAC REAL_LE_ADD2
       >> PROVE_TAC [REAL_LE_REFL, REAL_SUM_IMAGE_POS_MEM_LE])
   >> Know `~(1-g e = 0)` >- (POP_ASSUM MP_TAC >> REAL_ARITH_TAC)
   >> RW_TAC real_ss [(REWRITE_RULE [Once EQ_SYM_EQ] o UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_CMUL,
                     REAL_MUL_ASSOC, REAL_DIV_LMUL]);

val jensen_concave_SIGMA = store_thm
  ("jensen_concave_SIGMA",
   ``!s. FINITE s ==>
         !f g g'. (SIGMA g s = 1) /\
                  (!x. x IN s ==> 0 <= g x /\ g x <= 1) /\
                  f IN concave_fn ==>
                         SIGMA (\x. g x * f (g' x)) s <= f (SIGMA (\x. g x * g' x) s)``,
   REPEAT STRIP_TAC
   >> ONCE_REWRITE_TAC [GSYM REAL_LE_NEG2]
   >> RW_TAC std_ss [(REWRITE_RULE [Once EQ_SYM_EQ]) REAL_SUM_IMAGE_NEG]
   >> Suff `(\x. ~ f x) (SIGMA (\x. g x * g' x) s) <=
            SIGMA (\x. g x * (\x. ~ f x) (g' x)) s`
   >- RW_TAC real_ss []
   >> Q.ABBREV_TAC `f' = (\x. ~f x)`
   >> (MATCH_MP_TAC o UNDISCH o Q.SPEC `s`) jensen_convex_SIGMA
   >> Q.UNABBREV_TAC `f'`
   >> FULL_SIMP_TAC std_ss [concave_fn, GSPECIFICATION]);

val jensen_pos_convex_SIGMA = store_thm
  ("jensen_pos_convex_SIGMA",
   ``!s. FINITE s ==>
         !f g g'. (SIGMA g s = 1) /\
                  (!x. x IN s ==> 0 <= g x /\ g x <= 1) /\
                  (!x. x IN s ==> (0 < g x ==> 0 < g' x)) /\
                  f IN pos_convex_fn ==>
                        f (SIGMA (\x. g x * g' x) s) <= SIGMA (\x. g x * f (g' x)) s``,
   Suff `!s. FINITE s ==>
             (\s. !f g g'. (SIGMA g s = 1) /\
                  (!x. x IN s ==> 0 <= g x /\ g x <= 1) /\
                  (!x. x IN s ==> (0 < g x ==> 0 < g' x)) /\
                  f IN pos_convex_fn ==>
                        f (SIGMA (\x. g x * g' x) s) <= SIGMA (\x. g x * f (g' x)) s) s`
   >- RW_TAC std_ss []
   >> MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC real_ss [REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT, IN_INSERT, DISJ_IMP_THM, FORALL_AND_THM]
   >> Cases_on `g e = 0` >- FULL_SIMP_TAC real_ss []
   >> Cases_on `g e = 1`
   >- ( FULL_SIMP_TAC real_ss []
        >> Know `!s. FINITE s ==>
                (\s. !g. (SIGMA g s = 0) /\ (!x. x IN s ==> 0 <= g x /\ g x <= 1) ==>
                            (!x. x IN s ==> (g x = 0))) s`
        >- (MATCH_MP_TAC FINITE_INDUCT
            >> RW_TAC real_ss [REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT, IN_INSERT, DISJ_IMP_THM,
                               FORALL_AND_THM, NOT_IN_EMPTY] (* 2 sub-goals *)
            >- (Know `!(x:real) y. 0 <= x /\ 0 <= y /\ (x + y = 0) ==> ((x = 0) /\ (y = 0))`
                >- REAL_ARITH_TAC
                >> PROVE_TAC [REAL_SUM_IMAGE_POS])
            >>
            ( Know `!(x:real) y. 0 <= x /\ 0 <= y /\ (x + y = 0) ==> ((x = 0) /\ (y = 0))`
              >- REAL_ARITH_TAC
              >> Q.PAT_X_ASSUM `!g. (SIGMA g s' = 0) /\ (!x. x IN s' ==> 0 <= g x /\ g x <= 1) ==>
                                !x. x IN s' ==> (g x = 0)`
                (MP_TAC o Q.SPEC `g''`)
              >> PROVE_TAC [REAL_SUM_IMAGE_POS] ))
        >> Know `!x:real. (1 + x = 1) = (x = 0)` >- REAL_ARITH_TAC
        >> STRIP_TAC >> FULL_SIMP_TAC real_ss []
        >> POP_ASSUM (K ALL_TAC)
        >> (ASSUME_TAC o UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_IN_IF
        >> POP_ORW
        >> DISCH_TAC
        >> POP_ASSUM (ASSUME_TAC o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
                      (Q.SPEC `g`) o UNDISCH o (Q.SPEC `s`))
        >> `(\x. (if x IN s then (\x. g x * g' x) x else 0)) = (\x. 0)`
                by RW_TAC real_ss [FUN_EQ_THM]
        >> POP_ORW
        >> `(\x. (if x IN s then (\x. g x * f (g' x)) x else 0)) = (\x. 0)`
                by RW_TAC real_ss [FUN_EQ_THM]
        >> POP_ORW
        >> Suff `SIGMA (\x. 0) s = 0` >- RW_TAC real_ss []
        >> (MP_TAC o Q.SPECL [`(\x. 0)`, `0`] o
                UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_FINITE_CONST
        >> RW_TAC real_ss [])
   >> Suff `(SIGMA (\x. g x * g' x) s = (1 - g e) * SIGMA (\x. (g x / (1 - g e)) * g' x) s) /\
            (SIGMA (\x. g x * f(g' x)) s = (1 - g e) * SIGMA (\x. (g x / (1 - g e)) * f(g' x)) s)`
   >- (RW_TAC std_ss [] >> FULL_SIMP_TAC std_ss [pos_convex_fn, GSPECIFICATION]
       >> Q.PAT_X_ASSUM `!f' g'' g'''.
        (SIGMA g'' s = 1) /\
        (!x. x IN s ==> 0 <= g'' x /\ g'' x <= 1) /\
        (!x. x IN s ==> 0 < g'' x ==> 0 < g''' x) /\
        (!x y t.
           0 < x /\ 0 < y /\ 0 <= t /\ t <= 1 ==>
           f' (t * x + (1 - t) * y) <= t * f' x + (1 - t) * f' y) ==>
        f' (SIGMA (\x. g'' x * g''' x) s) <=
        SIGMA (\x. g'' x * f' (g''' x)) s` (MP_TAC o Q.SPECL [`f`, `(\x. g x / (1 - g e))`, `g'`])
       >> RW_TAC std_ss []
       >> Know `0 < 1 - g e`
       >- (Q.PAT_X_ASSUM `g e <= 1` MP_TAC >> Q.PAT_X_ASSUM `~ (g e = 1)` MP_TAC >> REAL_ARITH_TAC)
       >> STRIP_TAC
       >> Know `SIGMA (\x. g x / (1 - g e)) s = 1`
       >- ((MP_TAC o Q.SPECL [`g`, `inv (1- g e)`] o UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_CMUL
           >> RW_TAC real_ss [real_div] >> ASM_REWRITE_TAC [Once REAL_MUL_COMM]
           >> RW_TAC std_ss [Once REAL_MUL_COMM, GSYM real_div]
           >> Suff `SIGMA g s = 1 * (1 - g e)`
           >- PROVE_TAC [REAL_EQ_LDIV_EQ]
           >> Q.PAT_X_ASSUM `g e + SIGMA g s = 1` MP_TAC
           >> REAL_ARITH_TAC)
       >> STRIP_TAC
       >> FULL_SIMP_TAC std_ss []
       >> Cases_on `s = {}` >- FULL_SIMP_TAC real_ss [REAL_SUM_IMAGE_THM]
       >> Know `0 < SIGMA (\x. g x / (1 - g e) * g' x) s`
       >- ( RW_TAC std_ss [REAL_LT_LE]
            >- ((MATCH_MP_TAC o UNDISCH o REWRITE_RULE [GSYM AND_IMP_INTRO] o
                        Q.SPECL [`(\x. g x / (1 - g e) * g' x)`,`s`]) REAL_SUM_IMAGE_POS
                >> RW_TAC real_ss [] >> Cases_on `g x = 0` >- RW_TAC real_ss []
                >> MATCH_MP_TAC REAL_LE_MUL
                >> reverse CONJ_TAC >- PROVE_TAC [REAL_LT_IMP_LE, REAL_LT_LE]
                >> RW_TAC real_ss [] >> MATCH_MP_TAC REAL_LE_DIV
                >> RW_TAC real_ss [] >> PROVE_TAC [REAL_LT_IMP_LE])
            >> Q.PAT_X_ASSUM `SIGMA (\x. g x * g' x) s =
                                (1 - g e) * SIGMA (\x. g x / (1 - g e) * g' x) s`
                (MP_TAC o REWRITE_RULE [Once REAL_MUL_COMM] o GSYM)
            >> RW_TAC std_ss [GSYM REAL_EQ_RDIV_EQ]
            >> RW_TAC std_ss [real_div, REAL_ENTIRE, REAL_INV_EQ_0, REAL_LT_IMP_NE]
            >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
            >> Know `!s. FINITE s ==>
                    (\s. !g g'. (!x. x IN s ==> 0 <= g x) /\ (!x. x IN s ==> 0 < g x ==> 0 < g' x) /\
                                (SIGMA (\x. g x * g' x) s = 0) ==>
                                (!x. x IN s ==> (g x = 0))) s`
            >- ( REPEAT (POP_ASSUM (K ALL_TAC))
                 >> MATCH_MP_TAC FINITE_INDUCT
                 >> RW_TAC std_ss [REAL_SUM_IMAGE_THM, NOT_IN_EMPTY, DELETE_NON_ELEMENT,
                                   IN_INSERT, Once DISJ_IMP_THM, Once FORALL_AND_THM]
                 >- ( SPOSE_NOT_THEN STRIP_ASSUME_TAC
                      >> Cases_on `SIGMA (\x. g x * g' x) s = 0`
                      >- ( FULL_SIMP_TAC real_ss [REAL_ENTIRE] \\
                           PROVE_TAC [REAL_LT_IMP_NE, REAL_LT_LE] )
                      >> `0 < g e * g' e + SIGMA (\x. g x * g' x) s`
                                by (MATCH_MP_TAC REAL_LT_ADD
                                    >> CONJ_TAC
                                    >- (MATCH_MP_TAC REAL_LT_MUL >> PROVE_TAC [REAL_LT_LE])
                                    >> RW_TAC std_ss [REAL_LT_LE]
                                    >> (MATCH_MP_TAC o UNDISCH o REWRITE_RULE [GSYM AND_IMP_INTRO] o
                                        Q.SPECL [`(\x. g x * g' x)`,`s`]) REAL_SUM_IMAGE_POS
                                    >> RW_TAC std_ss []
                                    >> Cases_on `g x = 0` >- RW_TAC real_ss []
                                    >> PROVE_TAC [REAL_LE_MUL, REAL_LT_IMP_LE, REAL_LT_LE])
                      >> PROVE_TAC [REAL_LT_IMP_NE] )
                 >> Cases_on `SIGMA (\x. g x * g' x) s = 0`
                 >- METIS_TAC []
                 >> Cases_on `g e = 0`
                 >- FULL_SIMP_TAC real_ss []
                 >> `0 < g e * g' e + SIGMA (\x. g x * g' x) s`
                        by (MATCH_MP_TAC REAL_LT_ADD
                            >> CONJ_TAC
                            >- (MATCH_MP_TAC REAL_LT_MUL >> METIS_TAC [REAL_LT_LE])
                            >> RW_TAC std_ss [REAL_LT_LE]
                            >> (MATCH_MP_TAC o UNDISCH o REWRITE_RULE [GSYM AND_IMP_INTRO] o
                                Q.SPECL [`(\x. g x * g' x)`,`s`]) REAL_SUM_IMAGE_POS
                            >> RW_TAC std_ss []
                            >> Cases_on `g x' = 0` >- RW_TAC real_ss []
                            >> PROVE_TAC [REAL_LE_MUL, REAL_LT_IMP_LE, REAL_LT_LE])
                 >> METIS_TAC [REAL_LT_IMP_NE] )
            >> DISCH_TAC
            >> POP_ASSUM (ASSUME_TAC o UNDISCH o Q.SPEC `s`)
            >> FULL_SIMP_TAC std_ss [IMP_CONJ_THM, Once FORALL_AND_THM]
            >> POP_ASSUM (ASSUME_TAC o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
                          (Q.SPECL [`g`,`g'`]))
            >> (ASSUME_TAC o Q.SPECL [`(\x. if x IN s then g x else 0)`, `0`] o
                UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_FINITE_CONST
            >> `SIGMA (\x. (if x IN s then g x else 0)) s = SIGMA g s`
                  by METIS_TAC [GSYM REAL_SUM_IMAGE_IN_IF]
            >> FULL_SIMP_TAC real_ss [] )
       >> DISCH_TAC
       >> Q.PAT_X_ASSUM `!x y t. P`
              (MP_TAC o Q.SPECL [`g' e`, `SIGMA (\x. g x / (1 - g e) * g' x) s`, `g e`])
       >> Know `0 < g' e` >- METIS_TAC [REAL_LT_LE]
       >> RW_TAC std_ss []
       >> MATCH_MP_TAC REAL_LE_TRANS
       >> Q.EXISTS_TAC `g e * f (g' e) + (1 - g e) * f (SIGMA (\x. g x / (1 - g e) * g' x) s)`
       >> RW_TAC real_ss [REAL_LE_LADD]
       >> Suff `f (SIGMA (\x. g x / (1 - g e) * g' x) s) <=
                SIGMA (\x. g x / (1 - g e) * f (g' x)) s`
       >- PROVE_TAC [REAL_LE_LMUL]
       >> Q.PAT_X_ASSUM `(!x. x IN s ==> 0 <= g x / (1 - g e) /\ g x / (1 - g e) <= 1) /\
       (!x. x IN s ==> 0 < g x / (1 - g e) ==> 0 < g' x) ==>
       f (SIGMA (\x. g x / (1 - g e) * g' x) s) <=
       SIGMA (\x. g x / (1 - g e) * f (g' x)) s` MATCH_MP_TAC
       >> RW_TAC std_ss [] (* 3 sub-goals *)
       >| [PROVE_TAC [REAL_LE_DIV, REAL_LT_IMP_LE],
           Suff `g x <= 1 * (1 - g e)` >- PROVE_TAC [REAL_LE_LDIV_EQ]
           >> Suff `g e + g x <= 1` >- REAL_ARITH_TAC
           >> Q.PAT_X_ASSUM `g e + SIGMA g s = 1` (fn thm => ONCE_REWRITE_TAC [GSYM thm])
           >> MATCH_MP_TAC REAL_LE_ADD2
           >> PROVE_TAC [REAL_LE_REFL, REAL_SUM_IMAGE_POS_MEM_LE],
           Cases_on `g x = 0` >- FULL_SIMP_TAC real_ss []
           >> PROVE_TAC [REAL_LT_LE] ])
   >> Know `~(1-g e = 0)` >- (POP_ASSUM MP_TAC >> REAL_ARITH_TAC)
   >> RW_TAC real_ss [(REWRITE_RULE [Once EQ_SYM_EQ] o UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_CMUL,
                     REAL_MUL_ASSOC, REAL_DIV_LMUL]);

val jensen_pos_concave_SIGMA = store_thm
  ("jensen_pos_concave_SIGMA",
   ``!s. FINITE s ==>
         !f g g'. (SIGMA g s = 1) /\
                  (!x. x IN s ==> 0 <= g x /\ g x <= 1) /\
                  (!x. x IN s ==> (0 < g x ==> 0 < g' x)) /\
                  f IN pos_concave_fn ==>
                        SIGMA (\x. g x * f (g' x)) s <= f (SIGMA (\x. g x * g' x) s)``,
   REPEAT STRIP_TAC
   >> ONCE_REWRITE_TAC [GSYM REAL_LE_NEG2]
   >> RW_TAC std_ss [(REWRITE_RULE [Once EQ_SYM_EQ]) REAL_SUM_IMAGE_NEG]
   >> Suff `(\x. ~ f x) (SIGMA (\x. g x * g' x) s) <=
            SIGMA (\x. g x * (\x. ~ f x) (g' x)) s`
   >- RW_TAC real_ss []
   >> Q.ABBREV_TAC `f' = (\x. ~f x)`
   >> (MATCH_MP_TAC o UNDISCH o Q.SPEC `s`) jensen_pos_convex_SIGMA
   >> Q.UNABBREV_TAC `f'`
   >> FULL_SIMP_TAC std_ss [pos_concave_fn, GSPECIFICATION]);

val _ = export_theory ();
