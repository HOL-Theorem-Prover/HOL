(* ========================================================================= *)
(*                                                                           *)
(*                  Univariate Derivative Theory in R^1                      *)
(*                                                                           *)
(*        (c) Copyright, John Harrison 1998-2008                             *)
(*        (c) Copyright, Marco Maggesi 2014                                  *)
(*        (c) Copyright 2015,                                                *)
(*                       Muhammad Qasim,                                     *)
(*                       Osman Hasan,                                        *)
(*                       Hardware Verification Group,                        *)
(*                       Concordia University                                *)
(*            Contact:  <m_qasi@ece.concordia.ca>                            *)
(*                                                                           *)
(*    Note: This theory was ported from HOL Light                            *)
(*                                                                           *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open numTheory numLib unwindLib tautLib Arith prim_recTheory pairTheory
     combinTheory quotientTheory arithmeticTheory pred_setTheory hurdUtils
     jrhUtils listTheory mesonLib optionTheory pred_setLib iterateTheory;

open realTheory realLib topologyTheory cardinalTheory metricTheory netsTheory
     real_sigmaTheory real_topologyTheory;

val _ = new_theory "derivative";

fun METIS ths tm = prove(tm,METIS_TAC ths);

val DISC_RW_KILL = DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
                   POP_ASSUM K_TAC;

fun ASSERT_TAC tm = SUBGOAL_THEN tm STRIP_ASSUME_TAC;
val ASM_ARITH_TAC = REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC;

(* Minimal hol-light compatibility layer *)
val ASM_REAL_ARITH_TAC = REAL_ASM_ARITH_TAC; (* realLib *)
val IMP_CONJ           = CONJ_EQ_IMP;        (* cardinalTheory *)
val FINITE_SUBSET      = SUBSET_FINITE_I;    (* pred_setTheory *)
val LIM                = LIM_DEF;            (* real_topologyTheory *)

(* ------------------------------------------------------------------------- *)
(* definition(s) moved from other theories                                   *)
(* ------------------------------------------------------------------------- *)

val exp_ser = “\n. inv(&(FACT n))”;

Definition exp_def :
    exp(x) = infsum UNIV (\n. (^exp_ser) n * (x pow n))
End

(* ------------------------------------------------------------------------- *)
(* convex                                                                    *)
(* ------------------------------------------------------------------------- *)

val convex = new_definition ("convex",
  ``convex (s:real->bool) <=>
        !x y u v. x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
                  ==> ((u * x) + (v * y)) IN s``);

Theorem CONVEX_ALT :
    !s. convex s <=> !x y u. x IN s /\ y IN s /\ &0 <= u /\ u <= &1
                         ==> ((&1 - u) * x + u * y) IN s
Proof
  GEN_TAC >> REWRITE_TAC [convex] THEN
  MESON_TAC [REAL_ARITH ``&0:real <= u /\ &0 <= v /\ (u + v = &1)
                          ==> v <= &1 /\ (u = &1 - v)``,
             REAL_ARITH ``u <= &1 ==> &0:real <= &1 - u /\ ((&1 - u) + u = &1)``]
QED

val IN_CONVEX_SET = store_thm ("IN_CONVEX_SET",
 ``!s a b u.
        convex s /\ a IN s /\ b IN s /\ &0 <= u /\ u <= &1
        ==> ((&1 - u) * a + u * b) IN s``,
  MESON_TAC[CONVEX_ALT]);

val LIMPT_APPROACHABLE = store_thm ("LIMPT_APPROACHABLE",
 ``!x s. x limit_point_of s <=>
                !e. &0 < e ==> ?x'. x' IN s /\ ~(x' = x) /\ dist(x',x) < e``,
  REPEAT GEN_TAC THEN REWRITE_TAC[limit_point_of] THEN
  MESON_TAC[open_def, DIST_SYM, OPEN_BALL, CENTRE_IN_BALL, IN_BALL]);

Theorem LIMPT_OF_CONVEX :
    !s x:real. convex s /\ x IN s ==> (x limit_point_of s <=> ~(s = {x}))
Proof
    rpt STRIP_TAC
 >> ASM_CASES_TAC ``s = {x:real}`` >> art [LIMPT_SING]
 >> `?y:real. y IN s /\ ~(y = x)` by ASM_SET_TAC []
 >> REWRITE_TAC [LIMPT_APPROACHABLE]
 >> Q.X_GEN_TAC `e` >> DISCH_TAC
 >> Q.ABBREV_TAC `u = min (&1 / &2) (e / &2 / abs(y - x:real))`
 >> Know `&0 < u /\ u < &1:real`
 >- (Q.UNABBREV_TAC `u` >> REWRITE_TAC [REAL_LT_MIN, REAL_MIN_LT] \\
     SIMP_TAC std_ss [REAL_HALF_BETWEEN] \\
     ASM_SIMP_TAC real_ss [REAL_HALF, REAL_LT_DIV, GSYM ABS_NZ, REAL_SUB_0])
 >> DISCH_TAC
 >> Q.EXISTS_TAC `(&1 - u) * x + u * y:real`
 >> rpt CONJ_TAC (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      FIRST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE [CONVEX_ALT]) \\
      ASM_SIMP_TAC real_ss [REAL_LT_IMP_LE],
      (* goal 2 (of 3) *)
      ASM_SIMP_TAC std_ss [REAL_ENTIRE, REAL_SUB_0, REAL_ARITH
         ``((&1 - u) * x + u * y:real = x) <=> (u * (y - x) = 0)``] \\
      ASM_REAL_ARITH_TAC,
      (* goal 3 (of 3) *)
      REWRITE_TAC [dist, ABS_MUL, REAL_ARITH
        ``((&1 - u) * x + u * y) - x:real = u * (y - x)``] \\
      ASM_SIMP_TAC std_ss [REAL_ARITH ``&0 < u ==> (abs u = u:real)``] \\
      MATCH_MP_TAC (REAL_ARITH ``x *  2 <= e /\ &0 < e ==> x < e:real``) \\
      ASM_SIMP_TAC real_ss [GSYM REAL_LE_RDIV_EQ, GSYM ABS_NZ, REAL_SUB_0] \\
      Q.UNABBREV_TAC `u` >> FULL_SIMP_TAC real_ss [min_def] ]
QED

val TRIVIAL_LIMIT_WITHIN_CONVEX = store_thm ("TRIVIAL_LIMIT_WITHIN_CONVEX",
 ``!s x:real.
        convex s /\ x IN s ==> (trivial_limit(at x within s) <=> (s = {x}))``,
  SIMP_TAC std_ss [TRIVIAL_LIMIT_WITHIN, LIMPT_OF_CONVEX]);

(* ------------------------------------------------------------------------- *)
(* A general lemma.                                                          *)
(* ------------------------------------------------------------------------- *)

val CONVEX_CONNECTED = store_thm ("CONVEX_CONNECTED",
 ``!s:real->bool. convex s ==> connected s``,
  SIMP_TAC std_ss [CONVEX_ALT, connected, SUBSET_DEF, EXTENSION, IN_INTER,
              IN_UNION, NOT_IN_EMPTY, NOT_FORALL_THM, NOT_EXISTS_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  CCONTR_TAC THEN FULL_SIMP_TAC std_ss [] THEN
  MP_TAC(ISPECL [``\u. (&1 - u) * x + u * (x':real)``,
                 ``&0:real``, ``&1:real``, ``e1:real->bool``, ``e2:real->bool``]
         (SIMP_RULE std_ss [GSYM open_def] CONNECTED_REAL_LEMMA)) THEN
  ASM_SIMP_TAC real_ss [NOT_IMP, REAL_SUB_RZERO, REAL_MUL_LID, REAL_MUL_LZERO,
                  REAL_SUB_REFL, REAL_ADD_RID, REAL_ADD_LID, REAL_POS] THEN
  REPEAT(CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC[]]) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[dist] THEN
  SIMP_TAC real_ss [ABS_MUL, REAL_ARITH
   ``((&1 - a) * x + a * y) - ((&1 - b) * x + b * y) = (a - b) * (y - x:real)``] THEN
  MP_TAC(ISPEC ``(x' - x):real`` ABS_POS) THEN
  REWRITE_TAC[REAL_LE_LT] THEN STRIP_TAC THENL
   [ALL_TAC, METIS_TAC[REAL_MUL_RZERO, REAL_LT_01]] THEN
  EXISTS_TAC ``e / abs((x' - x):real)`` THEN
  ASM_SIMP_TAC real_ss [REAL_LT_RDIV_EQ, REAL_LT_DIV]);

(* ------------------------------------------------------------------------- *)
(* Explicit expressions for convexity in terms of arbitrary sums.            *)
(* ------------------------------------------------------------------------- *)

Theorem CONVEX_SUM :
    !s k u x:'a->real.
        FINITE k /\ convex s /\ (sum k u = &1) /\
        (!i. i IN k ==> &0 <= u i /\ x i IN s)
        ==> sum k (\i. u i * x i) IN s
Proof
  GEN_TAC THEN ASM_CASES_TAC ``convex(s:real->bool)`` THEN
  ASM_SIMP_TAC std_ss [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
  ONCE_REWRITE_TAC [METIS []
   ``!k. (!u. (sum k u = 1) ==>
    !x. (!i. i IN k ==> 0 <= u i /\ x i IN s) ==>
      sum k (\i. u i * x i) IN s) =
    (\k. !u. (sum k u = 1) ==>
    !x. (!i. i IN k ==> 0 <= u i /\ x i IN s) ==>
      sum k (\i. u i * x i) IN s) k``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC real_ss [SUM_CLAUSES, FORALL_IN_INSERT] THEN
  SIMP_TAC std_ss [GSYM RIGHT_FORALL_IMP_THM] THEN
  MAP_EVERY X_GEN_TAC [``k:'a->bool``, ``i:'a``, ``u:'a->real``, ``x:'a->real``] THEN
  REWRITE_TAC[AND_IMP_INTRO] THEN STRIP_TAC THEN
  ASM_CASES_TAC ``(u:'a->real) i = &1`` THENL
   [ASM_REWRITE_TAC[REAL_ARITH ``(&1 + a  = &1) <=> (a = &0:real)``] THEN
    SUBGOAL_THEN ``sum k (\i:'a. u i * x(i):real) = 0``
     (fn th => ASM_SIMP_TAC std_ss [th, REAL_ADD_RID, REAL_MUL_LID]) THEN
    MATCH_MP_TAC SUM_EQ_0' THEN SIMP_TAC std_ss [REAL_ENTIRE] THEN
    REPEAT STRIP_TAC THEN DISJ1_TAC THEN
    POP_ASSUM MP_TAC THEN SPEC_TAC (``x':'a``,``x':'a``) THEN
    MATCH_MP_TAC SUM_POS_EQ_0 THEN ASM_SIMP_TAC std_ss [] THEN
    POP_ASSUM MP_TAC THEN UNDISCH_TAC ``(u:'a->real) i + sum k u = 1`` THEN
    REAL_ARITH_TAC,
    FIRST_X_ASSUM(MP_TAC o SPEC ``(\j. (u:'a->real)(j) / (&1 - u(i)))``) THEN
    ASM_REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC std_ss [SUM_LMUL, GSYM REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    REWRITE_TAC [real_div] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    REWRITE_TAC [REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    ASM_SIMP_TAC std_ss [SUM_LMUL] THEN
    SUBGOAL_THEN ``&0:real < &1 - u(i:'a)`` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUM_POS_LE, REAL_ADD_SYM, REAL_ARITH
       ``&0 <= a /\ &0 <= b /\ (b + a = &1) /\ ~(a = &1) ==> &0 < &1 - a:real``],
      ALL_TAC] THEN
    REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC real_ss [REAL_LE_DIV, REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC real_ss [REAL_EQ_LDIV_EQ, REAL_MUL_LID, REAL_EQ_SUB_LADD] THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    UNDISCH_TAC ``convex s`` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE [convex]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [``sum k (\j. (u j / (&1 - u(i:'a))) * x(j) :real)``,
      ``x(i:'a):real``, ``&1 - u(i:'a):real``, ``u(i:'a):real``]) THEN
    REWRITE_TAC[real_div, REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[real_div, REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC std_ss [GSYM REAL_MUL_ASSOC, SUM_LMUL] THEN
    REWRITE_TAC [REAL_MUL_ASSOC] THEN
    SIMP_TAC real_ss [REAL_ARITH ``a * inv (1 - (u:'a->real) i) * b =
                                   inv (1 - (u:'a->real) i) * a * b``] THEN
    ASM_SIMP_TAC std_ss [GSYM REAL_MUL_ASSOC, SUM_LMUL] THEN
    ASM_SIMP_TAC real_ss [REAL_MUL_ASSOC, REAL_MUL_RINV, REAL_LT_IMP_NE] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC real_ss [REAL_LT_IMP_LE, SUM_LMUL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[REAL_ADD_SYM]]
QED

val CONVEX_INDEXED = store_thm ("CONVEX_INDEXED",
 ``!s:real->bool.
        convex s <=>
            !k u x. (!i:num. 1 <= i /\ i <= k ==> &0 <= u(i) /\ x(i) IN s) /\
                    (sum { 1n..k} u = &1)
                    ==> sum { 1n..k} (\i. u(i) * x(i)) IN s``,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONVEX_SUM THEN
    ASM_SIMP_TAC std_ss [IN_NUMSEG, FINITE_NUMSEG],
    DISCH_TAC THEN REWRITE_TAC[convex] THEN
    MAP_EVERY X_GEN_TAC [``x:real``, ``y:real``, ``u:real``, ``v:real``] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC ``2:num``) THEN
    DISCH_THEN(MP_TAC o SPEC ``\n:num. if n = 1 then u else v:real``) THEN
    DISCH_THEN(MP_TAC o SPEC ``\n:num. if n = 1 then x else y:real``) THEN
    REWRITE_TAC [TWO, SUM_CLAUSES_NUMSEG, NUMSEG_SING, SUM_SING] THEN
    SIMP_TAC arith_ss [] THEN METIS_TAC[]]);

(* ------------------------------------------------------------------------- *)
(* Convexity of general and special intervals.                               *)
(* ------------------------------------------------------------------------- *)

val IS_INTERVAL_CONVEX = store_thm ("IS_INTERVAL_CONVEX",
 ``!s:real->bool. is_interval s ==> convex s``,
  REWRITE_TAC[is_interval, convex] THEN
  REPEAT STRIP_TAC THEN
  KNOW_TAC ``x IN (s:real->bool) /\ y IN s ==>
        x <= (u * x + v * y) /\ (u * x + v * y) <= y \/
        y <= (u * x + v * y) /\ (u * x + v * y) <= x`` THENL
  [ALL_TAC, METIS_TAC []] THEN
  ASM_SIMP_TAC std_ss [] THEN
  DISJ_CASES_TAC(SPECL [``(x:real)``, ``(y:real)``] REAL_LE_TOTAL) THENL
   [DISJ1_TAC, DISJ2_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   ``&1 * a <= b /\ b <= &1 * c ==> a <= b /\ b <= c:real``) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC real_ss [REAL_ADD_RDISTRIB] THEN
  ASM_SIMP_TAC real_ss [REAL_LE_LMUL, REAL_LE_LADD, REAL_LE_RADD] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL_IMP THEN ASM_REWRITE_TAC []);

val IS_INTERVAL_CONNECTED = store_thm ("IS_INTERVAL_CONNECTED",
 ``!s:real->bool. is_interval s ==> connected s``,
  MESON_TAC[IS_INTERVAL_CONVEX, CONVEX_CONNECTED]);

val IS_INTERVAL_CONNECTED_1 = store_thm ("IS_INTERVAL_CONNECTED_1",
 ``!s:real->bool. is_interval s <=> connected s``,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[IS_INTERVAL_CONNECTED] THEN
  ONCE_REWRITE_TAC[MONO_NOT_EQ] THEN
  SIMP_TAC std_ss [IS_INTERVAL, connected, NOT_FORALL_THM,
   LEFT_IMP_EXISTS_THM, NOT_IMP] THEN
  qx_genl_tac [‘a’, ‘b’, ‘x’] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [``{z:real | 1 * z < x}``, ``{z:real | 1 * z > x}``] THEN
  REWRITE_TAC[OPEN_HALFSPACE_LT, OPEN_HALFSPACE_GT] THEN
  SIMP_TAC arith_ss [SUBSET_DEF, EXTENSION, IN_UNION, IN_INTER, NOT_FORALL_THM,
   real_gt, NOT_IN_EMPTY, GSPECIFICATION] THEN
  SIMP_TAC real_ss [] THEN
  REPEAT CONJ_TAC THENL [simp[REAL_NOT_LT, REAL_LE_TOTAL],
   metis_tac[REAL_LT_TOTAL], metis_tac[REAL_LE_LT], metis_tac[REAL_LE_LT]]);

val CONVEX_INTERVAL = store_thm ("CONVEX_INTERVAL",
 ``!a b:real. convex(interval [a,b]) /\ convex(interval (a,b))``,
  METIS_TAC [IS_INTERVAL_CONVEX, IS_INTERVAL_INTERVAL]);


(* ------------------------------------------------------------------------- *)
(* On real, is_interval, convex and connected are all equivalent.            *)
(* ------------------------------------------------------------------------- *)

val IS_INTERVAL_CONVEX_1 = store_thm ("IS_INTERVAL_CONVEX_1",
 ``!s:real->bool. is_interval s <=> convex s``,
  MESON_TAC[IS_INTERVAL_CONVEX, CONVEX_CONNECTED, IS_INTERVAL_CONNECTED_1]);

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val CONNECTED_COMPACT_INTERVAL_1 = store_thm ("CONNECTED_COMPACT_INTERVAL_1",
 ``!s:real->bool. connected s /\ compact s <=> ?a b. s = interval[a,b]``,
  REWRITE_TAC[GSYM IS_INTERVAL_CONNECTED_1, IS_INTERVAL_COMPACT]);

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

val _ = set_fixity "convex_on" (Infix(NONASSOC, 450));

val convex_on = new_definition ("convex_on",
  ``f convex_on s <=>
        !x y u v:real. x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
                  ==> f(u * x + v * y) <= u * f(x) + v * f(y)``);

Theorem REAL_CONVEX_BOUND2_LT :
    !x y a b u v:real. x < a /\ y < b /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
               ==> u * x + v * y < u * a + v * b
Proof
  REPEAT GEN_TAC THEN ASM_CASES_TAC ``u = &0:real`` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO, REAL_ADD_LID] THEN REPEAT STRIP_TAC,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_ADD2 THEN
    ASM_SIMP_TAC real_ss [REAL_LE_LMUL_IMP, REAL_LT_IMP_LE]] THEN
  MATCH_MP_TAC REAL_LT_LMUL_IMP THEN ASM_REAL_ARITH_TAC
QED

val REAL_CONVEX_BOUND_LT = store_thm ("REAL_CONVEX_BOUND_LT",
 ``!x y a u v:real. x < a /\ y < a /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
               ==> u * x + v * y < a``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  Q.EXISTS_TAC `u * a + v * a:real` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC real_ss [REAL_CONVEX_BOUND2_LT],
    ALL_TAC] THEN
   MATCH_MP_TAC REAL_EQ_IMP_LE THEN
   UNDISCH_TAC ``u + v = &1:real`` THEN
   SIMP_TAC real_ss [GSYM REAL_ADD_RDISTRIB]);

val CONVEX_DISTANCE = store_thm ("CONVEX_DISTANCE",
 ``!s a. (\x. dist(a,x)) convex_on s``,
  SIMP_TAC std_ss [convex_on, dist] THEN REPEAT STRIP_TAC THEN
  GEN_REWR_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [GSYM REAL_MUL_LID] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_ARITH
   ``(u + v) * z - (u * x + v * y) = u * (z - x) + v * (z - y:real)``] THEN
  ASM_MESON_TAC[ABS_TRIANGLE, ABS_MUL, ABS_REFL]);

val lemma = REWRITE_RULE[convex_on, IN_UNIV]
   (ISPEC ``univ(:real)`` CONVEX_DISTANCE);

val CONVEX_BALL = store_thm ("CONVEX_BALL",
 ``!x:real e. convex(ball(x,e))``,
  SIMP_TAC std_ss [convex, IN_BALL] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[REAL_LET_TRANS, REAL_CONVEX_BOUND_LT, lemma]);

(* ------------------------------------------------------------------------- *)
(* Derivatives. The definition is slightly tricky since we make it work over *)
(* nets of a particular form. This lets us prove theorems generally and use  *)
(* "at a" or "at a within s" for restriction to a set (1-sided on R etc.)    *)
(* ------------------------------------------------------------------------- *)

val _ = set_fixity "has_derivative" (Infix(NONASSOC, 450));

val has_derivative = new_definition ("has_derivative",
  ``(f has_derivative f') net <=>
        linear f' /\
        ((\y. inv(abs(y - netlimit net)) *
              (f(y) -
               (f(netlimit net) + f'(y - netlimit net)))) --> 0) net``);

(* ------------------------------------------------------------------------- *)
(* These are the only cases we'll care about, probably.                      *)
(* ------------------------------------------------------------------------- *)

val has_derivative_within = store_thm ("has_derivative_within",
 ``!f:real->real f' x s.
    (f has_derivative f') (at x within s) <=>
         linear f' /\
         ((\y. inv(abs(y - x)) * (f(y) - (f(x) + f'(y - x)))) --> 0)
         (at x within s)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_derivative] THEN AP_TERM_TAC THEN
  ASM_CASES_TAC ``trivial_limit(at (x:real) within s)`` THENL
   [ASM_REWRITE_TAC[LIM], ASM_SIMP_TAC std_ss [NETLIMIT_WITHIN]]);

val has_derivative_at = store_thm ("has_derivative_at",
 ``!f:real->real f' x.
    (f has_derivative f') (at x) <=>
         linear f' /\
         ((\y. inv(abs(y - x)) * (f(y) - (f(x) + f'(y - x)))) --> 0)
         (at x)``,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[has_derivative_within]);

(* ------------------------------------------------------------------------- *)
(* More explicit epsilon-delta forms.                                        *)
(* ------------------------------------------------------------------------- *)

Theorem HAS_DERIVATIVE_WITHIN :
   !f f' x s. (f has_derivative f')(at x within s) <=>
        linear f' /\
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x'. x' IN s /\
                         &0 < abs(x' - x) /\ abs(x' - x) < d
                         ==> abs(f(x') - f(x) - f'(x' - x)) /
                             abs(x' - x) < e
Proof
    rpt GEN_TAC
 >> SIMP_TAC std_ss [has_derivative_within, LIM_WITHIN] THEN AP_TERM_TAC
 >> SIMP_TAC std_ss [dist, REAL_ARITH ``(x' - (x + d)) = x' - x - d:real``]
 >> SIMP_TAC std_ss [real_div, REAL_SUB_RZERO, ABS_MUL]
 >> SIMP_TAC std_ss [REAL_MUL_ASSOC, REAL_MUL_SYM, ABS_INV, ABS_ABS, REAL_LT_IMP_NE]
QED

Theorem HAS_DERIVATIVE_AT :
    !f f' x. (f has_derivative f')(at x) <=>
        linear f' /\
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x'. &0 < abs(x' - x) /\ abs(x' - x) < d
                         ==> abs(f(x') - f(x) - f'(x' - x)) /
                             abs(x' - x) < e
Proof
    ONCE_REWRITE_TAC [GSYM WITHIN_UNIV]
 >> REWRITE_TAC [HAS_DERIVATIVE_WITHIN, IN_UNIV]
QED

Theorem HAS_DERIVATIVE_AT_WITHIN :
    !f f' x s. (f has_derivative f') (at x)
           ==> (f has_derivative f') (at x within s)
Proof
    REWRITE_TAC [HAS_DERIVATIVE_WITHIN, HAS_DERIVATIVE_AT]
 >> MESON_TAC []
QED

val HAS_DERIVATIVE_WITHIN_OPEN = store_thm ("HAS_DERIVATIVE_WITHIN_OPEN",
 ``!f f' a s.
         a IN s /\ open s
         ==> ((f has_derivative f') (at a within s) <=>
              (f has_derivative f') (at a))``,
  SIMP_TAC std_ss [has_derivative_within, has_derivative_at, LIM_WITHIN_OPEN]);

(* ------------------------------------------------------------------------- *)
(* Combining theorems.                                                       *)
(* ------------------------------------------------------------------------- *)

val HAS_DERIVATIVE_LINEAR = store_thm ("HAS_DERIVATIVE_LINEAR",
 ``!f net. linear f ==> (f has_derivative f) net``,
  RW_TAC real_ss [has_derivative, real_sub] THEN
  ASM_SIMP_TAC real_ss [GSYM LINEAR_ADD, GSYM LINEAR_CMUL, GSYM LINEAR_NEG] THEN
  ASM_SIMP_TAC real_ss [REAL_ARITH ``a + -(b + (a + -b)) = 0:real``] THEN
  ASM_SIMP_TAC real_ss [LINEAR_0, LIM_CONST]);

val HAS_DERIVATIVE_ID = store_thm ("HAS_DERIVATIVE_ID",
 ``!net. ((\x. x) has_derivative (\h. h)) net``,
  SIMP_TAC real_ss [HAS_DERIVATIVE_LINEAR, LINEAR_ID]);

val HAS_DERIVATIVE_CONST = store_thm ("HAS_DERIVATIVE_CONST",
 ``!c net. ((\x. c) has_derivative (\h. 0)) net``,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_derivative, linear] THEN
  SIMP_TAC real_ss [REAL_ADD_RID, REAL_SUB_REFL, REAL_MUL_RZERO, LIM_CONST]);

val HAS_DERIVATIVE_CMUL = store_thm ("HAS_DERIVATIVE_CMUL",
 ``!f f' net c. (f has_derivative f') net
                ==> ((\x. c * f(x)) has_derivative (\h. c * f'(h))) net``,
  REPEAT GEN_TAC THEN SIMP_TAC real_ss [has_derivative, LINEAR_COMPOSE_CMUL] THEN
  DISCH_THEN(MP_TAC o SPEC ``c:real`` o MATCH_MP LIM_CMUL o CONJUNCT2) THEN
  SIMP_TAC real_ss [REAL_MUL_RZERO] THEN MATCH_MP_TAC EQ_IMPLIES THEN
  AP_THM_TAC THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN REAL_ARITH_TAC);

val HAS_DERIVATIVE_NEG = store_thm ("HAS_DERIVATIVE_NEG",
 ``!f f' net. (f has_derivative f') net
            ==> ((\x. -(f(x))) has_derivative (\h. -(f'(h)))) net``,
  ONCE_REWRITE_TAC[REAL_NEG_MINUS1] THEN
  SIMP_TAC real_ss [HAS_DERIVATIVE_CMUL]);

val HAS_DERIVATIVE_ADD = store_thm ("HAS_DERIVATIVE_ADD",
 ``!f f' g g' net.
        (f has_derivative f') net /\ (g has_derivative g') net
        ==> ((\x. f(x) + g(x)) has_derivative (\h. f'(h) + g'(h))) net``,
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [has_derivative, LINEAR_COMPOSE_ADD] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (TAUT `(a /\ b) /\ (c /\ d) ==> b /\ d`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_ADD) THEN REWRITE_TAC[REAL_ADD_LID] THEN
  MATCH_MP_TAC EQ_IMPLIES THEN SIMP_TAC std_ss [] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN REAL_ARITH_TAC);

val HAS_DERIVATIVE_SUB = store_thm ("HAS_DERIVATIVE_SUB",
 ``!f f' g g' net.
        (f has_derivative f') net /\ (g has_derivative g') net
        ==> ((\x. f(x) - g(x)) has_derivative (\h. f'(h) - g'(h))) net``,
  SIMP_TAC real_ss [real_sub, HAS_DERIVATIVE_ADD, HAS_DERIVATIVE_NEG]);

Theorem HAS_DERIVATIVE_SUM :
    !f f' net s. FINITE s /\ (!a. a IN s ==> ((f a) has_derivative (f' a)) net)
     ==> ((\x. sum s (\a. f a x)) has_derivative (\h. sum s (\a. f' a h))) net
Proof
    NTAC 3 GEN_TAC >> REWRITE_TAC [IMP_CONJ]
 >> SET_INDUCT_TAC
 >> ASM_SIMP_TAC std_ss [SUM_CLAUSES, HAS_DERIVATIVE_CONST]
 >> rpt STRIP_TAC
 >> ONCE_REWRITE_TAC [METIS [] ``sum s (\a. f a x) = (\x. sum s (\a. f a x)) x``]
 >> MATCH_MP_TAC HAS_DERIVATIVE_ADD
 >> SIMP_TAC std_ss [ETA_AX] >> ASM_SIMP_TAC std_ss [IN_INSERT]
QED

(* ------------------------------------------------------------------------- *)
(* Limit transformation for derivatives.                                     *)
(* ------------------------------------------------------------------------- *)

val HAS_DERIVATIVE_TRANSFORM_WITHIN = store_thm ("HAS_DERIVATIVE_TRANSFORM_WITHIN",
 ``!f f' g x s d.
       &0 < d /\ x IN s /\
       (!x'. x' IN s /\ dist (x',x) < d ==> (f x' = g x')) /\
       (f has_derivative f') (at x within s)
       ==> (g has_derivative f') (at x within s)``,
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [has_derivative_within, IMP_CONJ] THEN
  DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
    LIM_TRANSFORM_WITHIN) THEN
  Q.EXISTS_TAC `d:real` THEN ASM_SIMP_TAC std_ss [DIST_REFL]);

val HAS_DERIVATIVE_TRANSFORM_AT = store_thm ("HAS_DERIVATIVE_TRANSFORM_AT",
 ``!f f' g x d.
       &0 < d /\ (!x'. dist (x',x) < d ==> (f x' = g x')) /\
       (f has_derivative f') (at x)
       ==> (g has_derivative f') (at x)``,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  MESON_TAC[HAS_DERIVATIVE_TRANSFORM_WITHIN, IN_UNIV]);

(* ------------------------------------------------------------------------- *)
(* Differentiability.                                                        *)
(* ------------------------------------------------------------------------- *)

val _ = set_fixity "differentiable" (Infix(NONASSOC, 450));
val _ = set_fixity "differentiable_on" (Infix(NONASSOC, 450));

val _ = hide "differentiable";

val differentiable = new_definition ("differentiable",
  ``f differentiable net <=> ?f'. ((f has_derivative f') net)``);

val differentiable_on = new_definition ("differentiable_on",
  ``f differentiable_on s <=> !x. x IN s ==> f differentiable (at x within s)``);

(* ------------------------------------------------------------------------- *)
(* Frechet derivative and Jacobian matrix.                                   *)
(* ------------------------------------------------------------------------- *)

val frechet_derivative = new_definition ("frechet_derivative",
 ``frechet_derivative f net = @f'. (f has_derivative f') net``);

val FRECHET_DERIVATIVE_WORKS = store_thm ("FRECHET_DERIVATIVE_WORKS",
 ``!f net. f differentiable net <=>
           (f has_derivative (frechet_derivative f net)) net``,
  REPEAT GEN_TAC THEN REWRITE_TAC[frechet_derivative] THEN
  CONV_TAC(RAND_CONV SELECT_CONV) THEN REWRITE_TAC[differentiable]);

val LINEAR_FRECHET_DERIVATIVE = store_thm ("LINEAR_FRECHET_DERIVATIVE",
 ``!f net. f differentiable net ==> linear(frechet_derivative f net)``,
  SIMP_TAC std_ss [FRECHET_DERIVATIVE_WORKS, has_derivative]);

(* ------------------------------------------------------------------------- *)
(* Differentiability implies continuity.  377                                *)
(* ------------------------------------------------------------------------- *)

val LIM_MUL_ABS_WITHIN = store_thm ("LIM_MUL_ABS_WITHIN",
 ``!f a s. (f --> 0) (at a within s)
           ==> ((\x. abs(x - a) * f(x)) --> 0) (at a within s)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM_WITHIN] THEN
  DISCH_TAC THEN GEN_TAC THEN POP_ASSUM (MP_TAC o Q.SPEC `e:real`) THEN
  ASM_CASES_TAC ``&0 < e:real`` THEN ASM_REWRITE_TAC[dist, REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN ``d:real`` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC ``min d (&1:real)`` THEN ASM_REWRITE_TAC[REAL_LT_MIN, REAL_LT_01] THEN
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [ABS_MUL, ABS_ABS] THEN
  GEN_REWR_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  ASM_SIMP_TAC std_ss [REAL_LT_MUL2, ABS_POS]);

Theorem DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN :
    !f:real->real x s.
        f differentiable (at x within s) ==> f continuous (at x within s)
Proof
  REWRITE_TAC[differentiable, has_derivative_within, CONTINUOUS_WITHIN] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN ``f':real->real`` MP_TAC) THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP LIM_MUL_ABS_WITHIN) THEN
  SUBGOAL_THEN
   ``((f':real->real) o (\y. y - x)) continuous (at x within s)``
  MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_WITHIN_COMPOSE THEN
    ASM_SIMP_TAC std_ss [LINEAR_CONTINUOUS_WITHIN] THEN
    SIMP_TAC std_ss [CONTINUOUS_SUB, CONTINUOUS_CONST, CONTINUOUS_WITHIN_ID],
    ALL_TAC] THEN
  SIMP_TAC std_ss [CONTINUOUS_WITHIN, o_DEF] THEN
  ASM_REWRITE_TAC[REAL_MUL_ASSOC, AND_IMP_INTRO, IN_UNIV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_ADD) THEN
  SIMP_TAC std_ss [LIM_WITHIN, GSYM DIST_NZ, REAL_MUL_RINV, ABS_ZERO,
           REAL_ARITH ``(x - y = 0) <=> (x = y:real)``,
           REAL_MUL_LID, REAL_SUB_REFL] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP LINEAR_0) THEN
  REWRITE_TAC[dist, REAL_SUB_RZERO, REAL_ADD_ASSOC] THEN
  SIMP_TAC std_ss [REAL_ARITH ``(a + (b - (c + a))) - (0 + 0) = b - c:real``]
QED

val DIFFERENTIABLE_IMP_CONTINUOUS_AT = store_thm ("DIFFERENTIABLE_IMP_CONTINUOUS_AT",
 ``!f:real->real x. f differentiable (at x) ==> f continuous (at x)``,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN]);

val DIFFERENTIABLE_IMP_CONTINUOUS_ON = store_thm ("DIFFERENTIABLE_IMP_CONTINUOUS_ON",
 ``!f:real->real s. f differentiable_on s ==> f continuous_on s``,
  SIMP_TAC std_ss [differentiable_on, CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN,
           DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN]);

Theorem HAS_DERIVATIVE_WITHIN_SUBSET :
    !f f' s t x. (f has_derivative f') (at x within s) /\ t SUBSET s
             ==> (f has_derivative f') (at x within t)
Proof
    REWRITE_TAC[has_derivative_within] THEN MESON_TAC[LIM_WITHIN_SUBSET]
QED

Theorem DIFFERENTIABLE_WITHIN_SUBSET :
    !f:real->real s t x.
      f differentiable (at x within t) /\ s SUBSET t
      ==> f differentiable (at x within s)
Proof
    REWRITE_TAC[differentiable] THEN MESON_TAC[HAS_DERIVATIVE_WITHIN_SUBSET]
QED

val DIFFERENTIABLE_ON_SUBSET = store_thm ("DIFFERENTIABLE_ON_SUBSET",
 ``!f:real->real s t.
      f differentiable_on t /\ s SUBSET t ==> f differentiable_on s``,
  REWRITE_TAC[differentiable_on] THEN
  MESON_TAC[SUBSET_DEF, DIFFERENTIABLE_WITHIN_SUBSET]);

val DIFFERENTIABLE_ON_EMPTY = store_thm ("DIFFERENTIABLE_ON_EMPTY",
 ``!f. f differentiable_on {}``,
  REWRITE_TAC[differentiable_on, NOT_IN_EMPTY]);

(* ------------------------------------------------------------------------- *)
(* Several results are easier using a "multiplied-out" variant.              *)
(* (I got this idea from Dieudonne's proof of the chain rule).               *)
(* ------------------------------------------------------------------------- *)

val HAS_DERIVATIVE_WITHIN_ALT = store_thm ("HAS_DERIVATIVE_WITHIN_ALT",
 ``!f:real->real f' s x.
     (f has_derivative f') (at x within s) <=>
            linear f' /\
            !e. &0 < e
                ==> ?d. &0 < d /\
                        !y. y IN s /\ abs(y - x) < d
                            ==> abs(f(y) - f(x) - f'(y - x)) <=
                                e * abs(y - x)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_derivative_within, LIM_WITHIN] THEN
  ASM_REWRITE_TAC[dist, REAL_SUB_RZERO] THEN
  ASM_CASES_TAC ``linear(f':real->real)`` THEN
  ASM_REWRITE_TAC [ABS_MUL, ABS_INV, ABS_ABS] THEN
  GEN_REWR_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
  SIMP_TAC std_ss [GSYM real_div, REAL_LT_LDIV_EQ] THEN
  REWRITE_TAC[REAL_ARITH ``a - (b + c) = a - b - c :real``] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC ``e:real`` THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC ``e:real``) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN EXISTS_TAC ``d:real`` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC ``y:real`` THEN DISCH_TAC THEN
    ASM_CASES_TAC ``&0 < abs(y - x :real)`` THENL
     [ASM_SIMP_TAC std_ss [GSYM REAL_LE_LDIV_EQ] THEN
      FULL_SIMP_TAC std_ss [REAL_LT_IMP_NE, REAL_LE_LT, ABS_DIV, ABS_ABS],
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE [GSYM ABS_NZ]) THEN
    ASM_SIMP_TAC std_ss [REAL_SUB_0, REAL_SUB_REFL, ABS_0, REAL_MUL_RZERO,
                         REAL_ARITH ``0 - x = -x:real``, ABS_NEG] THEN
    ASM_MESON_TAC[LINEAR_0, ABS_0, REAL_LE_REFL],
    FIRST_X_ASSUM(MP_TAC o SPEC ``e / &2:real``) THEN
    ASM_SIMP_TAC arith_ss [REAL_LT_DIV, REAL_LT] THEN
    STRIP_TAC THEN EXISTS_TAC ``d:real`` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC ``y:real`` THEN STRIP_TAC THEN
    ASM_SIMP_TAC std_ss [REAL_LT_IMP_NE, ABS_DIV, ABS_ABS, REAL_LT_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC ``e / &2 * abs(y - x :real)`` THEN
    ASM_SIMP_TAC arith_ss [REAL_LT_RMUL, REAL_LT_LDIV_EQ, REAL_LT] THEN
    UNDISCH_TAC ``&0 < e:real`` THEN REAL_ARITH_TAC]);

val HAS_DERIVATIVE_AT_ALT = store_thm ("HAS_DERIVATIVE_AT_ALT",
 ``!f:real->real f' x.
     (f has_derivative f') (at x) <=>
        linear f' /\
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !y. abs(y - x) < d
                        ==> abs(f(y) - f(x) - f'(y - x)) <= e * abs(y - x)``,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[HAS_DERIVATIVE_WITHIN_ALT, IN_UNIV]);

(* ------------------------------------------------------------------------- *)
(* The chain rule.    499                                                    *)
(* ------------------------------------------------------------------------- *)

val DIFF_CHAIN_WITHIN = store_thm ("DIFF_CHAIN_WITHIN",
 ``!f:real->real g:real->real f' g' x s.
        (f has_derivative f') (at x within s) /\
        (g has_derivative g') (at (f x) within (IMAGE f s))
        ==> ((g o f) has_derivative (g' o f'))(at x within s)``,
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [HAS_DERIVATIVE_WITHIN_ALT, LINEAR_COMPOSE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(X_CHOOSE_TAC ``B1:real`` o MATCH_MP LINEAR_BOUNDED_POS) THEN
  DISCH_THEN(fn th => X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN MP_TAC th) THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fn th => ASSUME_TAC th THEN X_CHOOSE_TAC ``B2:real`` (MATCH_MP
              LINEAR_BOUNDED_POS th)) MP_TAC) THEN
  FIRST_X_ASSUM(fn th => MP_TAC th THEN MP_TAC(Q.SPEC `e / &2 / B2` th)) THEN
  ASM_SIMP_TAC arith_ss [REAL_LT_DIV, REAL_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN ``d1:real`` STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o Q.SPEC `e / &2 / (&1 + B1)`) THEN
  ASM_SIMP_TAC arith_ss [REAL_LT_DIV, REAL_LT, REAL_LT_ADD] THEN
  DISCH_THEN(X_CHOOSE_THEN ``de:real`` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC ``!e:real. 0 < e ==>
        ?d. 0 < d /\
          !y. y IN s /\ abs (y - x) < d ==>
            abs (f y - f x - f' (y - x)) <= e * abs (y - x)`` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o Q.SPEC `&1`) THEN
  REWRITE_TAC[REAL_LT_01, REAL_MUL_LID] THEN
  DISCH_THEN(X_CHOOSE_THEN ``d2:real`` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [``d1:real``, ``d2:real``] REAL_DOWN2) THEN
  ASM_SIMP_TAC std_ss [REAL_LT_DIV, REAL_LT_ADD, REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN ``d0:real`` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [``d0:real``, ``de / (B1 + &1:real)``] REAL_DOWN2) THEN
  ASM_SIMP_TAC std_ss [REAL_LT_DIV, REAL_LT_ADD, REAL_LT_01] THEN
  DISCH_THEN (X_CHOOSE_TAC ``d:real``) THEN Q.EXISTS_TAC `d` THEN
  POP_ASSUM MP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC ``y:real`` THEN DISCH_TAC THEN UNDISCH_TAC
   ``!y. y IN s /\ abs(y - x) < d2
        ==> abs((f:real->real) y - f x - f'(y - x)) <= abs(y - x)`` THEN
  DISCH_THEN(MP_TAC o SPEC ``y:real``) THEN
  Q_TAC SUFF_TAC `y IN s /\ abs (y - x) < d2` THENL
   [DISCH_TAC, ASM_MESON_TAC[REAL_LT_TRANS]] THEN
  ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
  UNDISCH_TAC ``!y. y IN s /\ abs (y - x) < d1 ==>
        abs (f y - f x - f' (y - x)) <= e / 2 / B2 * abs (y - x:real)`` THEN
  DISCH_THEN(MP_TAC o SPEC ``y:real``) THEN
  Q_TAC SUFF_TAC `y IN s /\ abs (y - x) < d1` THENL
   [DISCH_TAC, ASM_MESON_TAC[REAL_LT_TRANS]] THEN
  ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC ``(f:real->real) y``) THEN
  ASM_SIMP_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `f y IN IMAGE f s /\ abs (f y - f x) < de` THENL
   [DISCH_TAC,
    CONJ_TAC THENL [ASM_MESON_TAC[IN_IMAGE], ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN Q.EXISTS_TAC
     `abs(f'(y - x)) + abs((f:real->real) y - f x - f'(y - x))` THEN
    REWRITE_TAC[ABS_TRIANGLE_SUB] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC ``B1 * abs(y - x) + abs(y - x :real)`` THEN
    ASM_SIMP_TAC real_ss [REAL_LE_ADD2] THEN
    REWRITE_TAC[REAL_ARITH ``a * x + x = x * (a + &1:real)``] THEN
    ASM_SIMP_TAC real_ss [GSYM REAL_LT_RDIV_EQ, REAL_LT_ADD, REAL_LT_01] THEN
    ASM_MESON_TAC[REAL_LT_TRANS]] THEN
  ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  Q.EXISTS_TAC `abs((g:real->real)(f(y:real)) - g(f x) - g'(f y - f x)) +
               abs((g(f y) - g(f x) - g'(f'(y - x))) -
                   (g(f y) - g(f x) - g'(f y - f x)))` THEN
  REWRITE_TAC[ABS_TRIANGLE_SUB] THEN
  REWRITE_TAC[REAL_ARITH ``(a - b - c1) - (a - b - c2) = c2 - c1:real``] THEN
  ASM_SIMP_TAC std_ss [GSYM LINEAR_SUB] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
    ``a <= d ==> b <= ee - d ==> a + b <= ee:real``)) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  Q.EXISTS_TAC `B2 * abs((f:real->real) y - f x - f'(y - x))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  Q.EXISTS_TAC `B2 * e / &2 / B2 * abs(y - x :real)` THEN
  CONJ_TAC THENL
  [SIMP_TAC std_ss [real_div] THEN
   ONCE_REWRITE_TAC [REAL_ARITH ``a * b * c * d * e = a * ((b * c * d) * e:real)``] THEN
   MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC std_ss [GSYM real_div, REAL_LE_REFL] THEN
   ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE, ABS_POS],
   ALL_TAC] THEN
  ASM_SIMP_TAC real_ss [REAL_LE_LMUL, REAL_LT_IMP_LE] THEN REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   ``b * e * h * b' * x <= e * x - d <=>
     d <= e * (&1 - h * (b' * b)) * x:real``] THEN
  ASM_SIMP_TAC real_ss [REAL_MUL_LINV, REAL_LT_IMP_NE] THEN
  SIMP_TAC real_ss [ONE_MINUS_HALF, REAL_INV_1OVER] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC, GSYM REAL_INV_1OVER] THEN
  ASM_SIMP_TAC arith_ss [REAL_LE_LMUL, REAL_LT_DIV, REAL_LT] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC real_ss [REAL_LE_LDIV_EQ, REAL_LT_ADD, REAL_LT_01] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC real_ss [REAL_LE_LDIV_EQ, REAL_LT_ADD, REAL_LT_01] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
   ``abs(f'(y - x)) + abs((f:real->real) y - f x - f'(y - x))`` THEN
  REWRITE_TAC[ABS_TRIANGLE_SUB] THEN SIMP_TAC real_ss [real_div, REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC [REAL_ARITH ``a * b * c * d = (c * a) * b * d:real``] THEN
  SIMP_TAC real_ss [REAL_MUL_LINV] THEN MATCH_MP_TAC(REAL_ARITH
  ``u <= x * b /\ v <= b ==> u + v <= b * (&1 + x:real)``) THEN
  ASM_REWRITE_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Component of the differential must be zero if it exists at a local        *)
(* maximum or minimum for that corresponding component. Start with slightly  *)
(* sharper forms that fix the sign of the derivative on the boundary.        *)
(* ------------------------------------------------------------------------- *)

Theorem DIFFERENTIAL_COMPONENT_POS_AT_MINIMUM :
    !f:real->real f' x s e.
        x IN s /\ convex s /\ (f has_derivative f') (at x within s) /\
        &0 < e /\ (!w. w IN s INTER ball(x,e) ==> (f x) <= (f w))
        ==> !y. y IN s ==> &0 <= (f'(y - x))
Proof
  REWRITE_TAC[has_derivative_within] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC ``y:real = x`` THENL
   [ASM_MESON_TAC[REAL_SUB_REFL, LINEAR_0, REAL_LE_REFL],
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC ``((\y. inv (abs (y - x)) * (f y - (f x + f' (y - x)))) --> 0)
        (at x within s)`` THEN REWRITE_TAC [LIM_WITHIN] THEN
  DISCH_THEN(MP_TAC o Q.SPEC `-((f':real->real)(y - x)) / abs(y - x)`) THEN
  ASM_SIMP_TAC real_ss [REAL_LT_DIV, GSYM ABS_NZ, real_sub,
               NOT_EXISTS_THM, REAL_ARITH ``&0 < -x <=> x < &0:real``] THEN
  CONJ_TAC THENL
  [ONCE_REWRITE_TAC [GSYM REAL_LT_NEG] THEN SIMP_TAC real_ss [REAL_NEG_0, real_div] THEN
   SIMP_TAC std_ss [GSYM real_sub, GSYM real_div] THEN
   Q_TAC SUFF_TAC `0 < abs (y - x:real)` THENL
   [DISCH_TAC,
    REWRITE_TAC [GSYM ABS_NZ] THEN POP_ASSUM MP_TAC THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC] THEN
   ASM_SIMP_TAC real_ss [REAL_LT_LDIV_EQ],
   ALL_TAC] THEN
  X_GEN_TAC ``d:real`` THEN CCONTR_TAC THEN FULL_SIMP_TAC std_ss [] THEN
  Q.ABBREV_TAC `de = min (&1) ((min d e) / &2 / abs(y - x:real))` THEN
  FIRST_X_ASSUM (MP_TAC o Q.SPEC `x + de * (y - x):real`) THEN
  SIMP_TAC real_ss [dist, REAL_ADD_SUB, NOT_IMP, GSYM CONJ_ASSOC] THEN
  SUBGOAL_THEN ``abs(de * (y - x):real) < min d e`` MP_TAC THENL
  [ASM_SIMP_TAC real_ss [ABS_MUL, GSYM REAL_LT_RDIV_EQ,
                 ABS_POS, real_sub] THEN
   Q.UNABBREV_TAC `de` THEN SIMP_TAC real_ss [real_div, REAL_MUL_ASSOC] THEN
   SIMP_TAC std_ss [min_def] THEN REPEAT COND_CASES_TAC THENL
   [FULL_SIMP_TAC real_ss [GSYM real_sub] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    Q.EXISTS_TAC `d / 2` THEN ASM_SIMP_TAC std_ss [REAL_LT_HALF2] THEN
    Q_TAC SUFF_TAC `0 < abs (y - x:real)` THENL
    [DISCH_TAC, REWRITE_TAC [GSYM ABS_NZ] THEN
     UNDISCH_TAC ``y <> x:real`` THEN REAL_ARITH_TAC] THEN
    GEN_REWR_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    ASM_SIMP_TAC real_ss [GSYM REAL_LE_RDIV_EQ, real_div],
    FULL_SIMP_TAC real_ss [GSYM real_sub] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    Q.EXISTS_TAC `e / 2` THEN ASM_SIMP_TAC std_ss [REAL_LT_HALF2] THEN
    Q_TAC SUFF_TAC `0 < abs (y - x:real)` THENL
    [DISCH_TAC, REWRITE_TAC [GSYM ABS_NZ] THEN
     UNDISCH_TAC ``y <> x:real`` THEN REAL_ARITH_TAC] THEN
    GEN_REWR_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    ASM_SIMP_TAC real_ss [GSYM REAL_LE_RDIV_EQ, real_div],
    SIMP_TAC real_ss [ABS_MUL] THEN
    `y - x <> 0` by (UNDISCH_TAC ``y <> x:real`` THEN REAL_ARITH_TAC) THEN
    ASM_SIMP_TAC std_ss [GSYM ABS_INV, ABS_ABS] THEN
    ONCE_REWRITE_TAC [REAL_ARITH ``a * b * c * d = (a * b) * (c * d:real)``] THEN
    ASM_SIMP_TAC real_ss [GSYM ABS_MUL, REAL_MUL_LINV, GSYM real_sub] THEN
    SIMP_TAC real_ss [GSYM real_div] THEN Q_TAC SUFF_TAC `abs (d / 2) = d / 2` THENL
    [ASM_SIMP_TAC real_ss [REAL_LT_HALF2], ALL_TAC] THEN
     ASM_SIMP_TAC real_ss [ABS_REFL, REAL_LE_RDIV_EQ, REAL_LE_LT],
     ALL_TAC] THEN
   SIMP_TAC real_ss [ABS_MUL] THEN
   `y - x <> 0` by (UNDISCH_TAC ``y <> x:real`` THEN REAL_ARITH_TAC) THEN
   ASM_SIMP_TAC std_ss [GSYM ABS_INV, ABS_ABS] THEN
   ONCE_REWRITE_TAC [REAL_ARITH ``a * b * c * d = (a * b) * (c * d:real)``] THEN
   ASM_SIMP_TAC real_ss [GSYM ABS_MUL, REAL_MUL_LINV, GSYM real_sub] THEN
   SIMP_TAC std_ss [GSYM real_div] THEN Q_TAC SUFF_TAC `abs (e / 2) = e / 2` THENL
   [ASM_SIMP_TAC real_ss [REAL_LT_HALF2], ALL_TAC] THEN
    ASM_SIMP_TAC real_ss [ABS_REFL, REAL_LE_RDIV_EQ, REAL_LE_LT],
    ALL_TAC] THEN
   REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN ``&0 < de /\ de <= &1:real`` STRIP_ASSUME_TAC THENL
  [Q.UNABBREV_TAC `de` THEN CONJ_TAC THENL [ALL_TAC, SIMP_TAC std_ss [REAL_MIN_LE1]] THEN
   ASM_SIMP_TAC real_ss [REAL_LT_MIN, REAL_LT_01, REAL_HALF, REAL_LT_DIV, ABS_NZ, real_sub] THEN
   SIMP_TAC real_ss [real_div, min_def] THEN
   Q_TAC SUFF_TAC `0 < abs (y - x:real)` THENL
    [DISCH_TAC, REWRITE_TAC [GSYM ABS_NZ] THEN
     UNDISCH_TAC ``y <> x:real`` THEN REAL_ARITH_TAC] THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC std_ss [REAL_LT_RDIV_EQ, GSYM real_div, GSYM real_sub] THEN
    ASM_SIMP_TAC real_ss [REAL_LT_HALF2],
    ALL_TAC] THEN
   ASM_SIMP_TAC std_ss [REAL_LT_RDIV_EQ, GSYM real_div, GSYM real_sub] THEN
   ASM_SIMP_TAC real_ss [REAL_LT_HALF2],
   ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
  [REWRITE_TAC[REAL_ARITH
    ``x + a * (y - x):real = (&1 - a) * x + a * y``] THEN
   MATCH_MP_TAC IN_CONVEX_SET THEN ASM_SIMP_TAC real_ss [REAL_LT_IMP_LE],
   DISCH_TAC] THEN
  CONJ_TAC THENL
  [SIMP_TAC std_ss [ABS_MUL] THEN MATCH_MP_TAC REAL_LT_MUL THEN
   UNDISCH_TAC ``0 < de:real`` THEN UNDISCH_TAC ``y <> x:real`` THEN
   REAL_ARITH_TAC, ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC std_ss [REAL_NOT_LT, ABS_MUL] THEN
  ONCE_REWRITE_TAC [REAL_ARITH ``a + b + -a = b:real``] THEN
  Q_TAC SUFF_TAC `abs (de * (y - x)) <> 0` THENL
  [DISCH_TAC, SIMP_TAC std_ss [ABS_MUL] THEN
   ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
   MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC real_ss [GSYM ABS_NZ] THEN
   ASM_SIMP_TAC std_ss [REAL_LT_IMP_NE] THEN UNDISCH_TAC ``y <> x:real`` THEN
   REAL_ARITH_TAC] THEN
  ASM_SIMP_TAC std_ss [ABS_INV, ABS_ABS] THEN
  `y - x <> 0` by (UNDISCH_TAC ``y <> x:real`` THEN REAL_ARITH_TAC) THEN
  `0 < abs (y - x)` by (ASM_SIMP_TAC std_ss [GSYM ABS_NZ]) THEN
  ASM_SIMP_TAC std_ss [REAL_LE_LDIV_EQ, GSYM real_sub] THEN
  `abs (y - x) <> 0` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_NE] THEN
  `de <> 0` by (ASM_SIMP_TAC std_ss [REAL_LT_IMP_NE]) THEN
  `0 < abs (de)` by (ASM_SIMP_TAC std_ss [GSYM ABS_NZ]) THEN
  `abs (de) <> 0` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_NE] THEN
  ASM_SIMP_TAC real_ss [REAL_INV_MUL, ABS_MUL] THEN
  ONCE_REWRITE_TAC [REAL_ARITH ``a * b * c * d = (a * c) * (b * d:real)``] THEN
  ASM_SIMP_TAC real_ss [REAL_MUL_LINV] THEN
  Q_TAC SUFF_TAC `x + de * (y - x) IN ball (x,e)` THENL
  [DISCH_TAC, SIMP_TAC real_ss [IN_BALL, dist] THEN
   UNDISCH_TAC ``abs (de * (y - x)) < e:real`` THEN REAL_ARITH_TAC] THEN
  `f x <= f (x + de * (y - x))` by METIS_TAC [IN_INTER] THEN
  Q_TAC SUFF_TAC `abs (f (x + de * (y - x)) - (f x + f' (de * (y - x)))) =
                      (f (x + de * (y - x)) - (f x + f' (de * (y - x))))` THENL
  [DISC_RW_KILL,
   REWRITE_TAC [ABS_REFL] THEN
   ONCE_REWRITE_TAC [REAL_ARITH ``a - (b + c) = (a - b) + -c:real``] THEN
   MATCH_MP_TAC REAL_LE_ADD THEN
   ASM_SIMP_TAC real_ss [REAL_ARITH ``a <= b ==> 0 <= b - a:real``] THEN
   ASM_SIMP_TAC real_ss [LINEAR_CMUL] THEN
   ONCE_REWRITE_TAC [REAL_ARITH ``-(a * b) = a * -b:real``] THEN
   MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC std_ss [REAL_LE_LT] THEN
   ONCE_REWRITE_TAC [GSYM REAL_LT_NEG] THEN ASM_SIMP_TAC real_ss []] THEN
  ONCE_REWRITE_TAC [REAL_MUL_COMM] THEN REWRITE_TAC [GSYM real_div] THEN
  ASM_SIMP_TAC real_ss [REAL_LE_RDIV_EQ] THEN ONCE_REWRITE_TAC [REAL_MUL_COMM] THEN
  `0 <= de` by ASM_SIMP_TAC real_ss [REAL_LE_LT] THEN
  POP_ASSUM (ASSUME_TAC o REWRITE_RULE [GSYM ABS_REFL]) THEN
  ASM_SIMP_TAC real_ss [GSYM LINEAR_CMUL] THEN
  GEN_REWR_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_COMM] THEN
  ONCE_REWRITE_TAC [REAL_ARITH ``-a <= b - (c + a) <=> c <= b:real``] THEN
  METIS_TAC [REAL_MUL_COMM]
QED

val DIFFERENTIAL_COMPONENT_NEG_AT_MAXIMUM = store_thm ("DIFFERENTIAL_COMPONENT_NEG_AT_MAXIMUM",
 ``!f:real->real f' x s e.
        x IN s /\ convex s /\ (f has_derivative f') (at x within s) /\
        &0 < e /\ (!w. w IN s INTER ball(x,e) ==> (f w) <= (f x))
        ==> !y. y IN s ==> (f'(y - x)) <= &0``,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [
   ``\x. -((f:real->real) x)``, ``\x. -((f':real->real) x)``,
   ``x:real``, ``s:real->bool``, ``e:real``]
        DIFFERENTIAL_COMPONENT_POS_AT_MINIMUM) THEN
  ASM_SIMP_TAC real_ss [HAS_DERIVATIVE_NEG] THEN
  ASM_SIMP_TAC real_ss [REAL_LE_NEG2, REAL_NEG_GE0]);

val CONVEX_CBALL = store_thm ("CONVEX_CBALL",
 ``!x:real e. convex(cball(x,e))``,
  REWRITE_TAC[convex, IN_CBALL, dist] THEN MAP_EVERY X_GEN_TAC
   [``x:real``, ``e:real``, ``y:real``, ``z:real``, ``u:real``, ``v:real``] THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_ARITH ``a - b = &1 * a - b:real``] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_ARITH
   ``(a + b) * x - (a * y + b * z) = a * (x - y) + b * (x - z:real)``] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC ``abs(u * (x - y)) + abs(v * (x - z):real)`` THEN
  REWRITE_TAC[ABS_TRIANGLE, ABS_MUL] THEN
  MATCH_MP_TAC REAL_CONVEX_BOUND_LE THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
  ASM_SIMP_TAC real_ss [REAL_ARITH
   ``&0 <= u /\ &0 <= v /\ (u + v = &1) ==> (abs(u) + abs(v) = &1:real)``]);

Theorem DIFFERENTIAL_COMPONENT_ZERO_AT_MAXMIN :
    !f:real->real f' x s.
        x IN s /\ open s /\ (f has_derivative f') (at x) /\
        ((!w. w IN s ==> (f w) <= (f x)) \/
         (!w. w IN s ==> (f x) <= (f w))) ==> !h. (f' h) = &0
Proof
    rpt GEN_TAC
 >> DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)
 >> Q.PAT_ASSUM `open s`
      (MP_TAC o ONCE_REWRITE_RULE [OPEN_CONTAINS_CBALL])
 >> DISCH_THEN(MP_TAC o Q.SPEC `x:real`) >> art [SUBSET_DEF]
 >> DISCH_THEN(X_CHOOSE_THEN ``e:real`` STRIP_ASSUME_TAC)
 >> FIRST_X_ASSUM DISJ_CASES_TAC (* 2 subgoals, shared tactics *)
 >| [ MP_TAC (Q.SPECL [`f`, `f'`, `x`, `cball(x:real,e)`, `e`]
              DIFFERENTIAL_COMPONENT_NEG_AT_MAXIMUM),
      MP_TAC (Q.SPECL [`f`, `f'`, `x`, `cball(x:real,e)`, `e`]
              DIFFERENTIAL_COMPONENT_POS_AT_MINIMUM) ] (* 2 subgoals *)
 >> ASM_SIMP_TAC real_ss [HAS_DERIVATIVE_AT_WITHIN, CENTRE_IN_CBALL,
                          CONVEX_CBALL, REAL_LT_IMP_LE, IN_INTER]
 >> DISCH_TAC THEN X_GEN_TAC ``h:real``
 >> Q.PAT_X_ASSUM `(f has_derivative f') (at x)`
      (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [has_derivative_at]))
 >> (Cases_on `h:real = 0` >- ASM_MESON_TAC [LINEAR_0])
 >> Q.PAT_X_ASSUM `!y. y IN cball (x,e) ==> _`
      (fn th => MP_TAC (Q.SPEC `x + e / abs h * h:real` th) \\
                MP_TAC (Q.SPEC `x - e / abs h * h:real` th))
 >> SIMP_TAC real_ss [IN_CBALL, dist, REAL_ARITH
     ``(abs(x:real - (x - e)) = abs e) /\ (abs(x:real - (x + e)) = abs e)``,
       REAL_ARITH ``x - e / abs h * h - x = -(e / abs h * h):real``]
 >> FIRST_ASSUM (fn th => REWRITE_TAC [MATCH_MP LINEAR_NEG th])
 >| [ ONCE_REWRITE_TAC [METIS [REAL_LE_NEG] ``-e <= 0 <=> -0 <= --e:real``],
      ONCE_REWRITE_TAC [METIS [REAL_LE_NEG] ``0 <= -e <=> --e <= -0:real``] ]
 >> SIMP_TAC std_ss [REAL_NEG_NEG, REAL_NEG_0]
 (* stage work, right-associative from now on *)
 >> (Know `abs (e / abs h * h) <= e`
     >- (Cases_on `0 <= h` (* 2 subgoals, same tactics *)
         >- (REWRITE_TAC [real_div, REAL_ARITH ``a * b * c = a * (b * c:real)``] \\
             FULL_SIMP_TAC real_ss [abs, REAL_MUL_LINV, GSYM REAL_NEG_INV,
                                    REAL_ARITH ``-a * b = -(a * b:real)``] \\
            `0 <= e` by PROVE_TAC [REAL_LT_IMP_LE] >> rw []) \\
         REWRITE_TAC [real_div, REAL_ARITH ``a * b * c = a * (b * c:real)``] \\
         FULL_SIMP_TAC real_ss [abs, REAL_MUL_LINV, GSYM REAL_NEG_INV,
                                REAL_ARITH ``-a * b = -(a * b:real)``] \\
         ONCE_REWRITE_TAC [METIS [REAL_LE_NEG] ``0 <= -e <=> --e <= -0:real``] \\
         SIMP_TAC std_ss [REAL_NEG_NEG, REAL_NEG_0] \\
        `~(e <= 0)` by PROVE_TAC [real_lte] >> rw []) \\
     RW_TAC std_ss [] \\
    `f' (e / abs h * h) = 0` by METIS_TAC [REAL_LE_ANTISYM] \\
     POP_ASSUM MP_TAC >> ASM_SIMP_TAC std_ss [LINEAR_CMUL] \\
     ASM_SIMP_TAC std_ss [REAL_ENTIRE] \\
     Suff `e / abs h <> 0` >- rw [] \\
     ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC REAL_LT_IMP_NE \\
     MATCH_MP_TAC REAL_LT_DIV \\
     ASM_SIMP_TAC std_ss [GSYM ABS_NZ])
QED

Theorem DIFFERENTIAL_ZERO_MAXMIN :
    !f:real->real f' x s.
        x IN s /\ open s /\ (f has_derivative f') (at x) /\
        ((!y. y IN s ==> (f y) <= (f x)) \/
         (!y. y IN s ==> (f x) <= (f y)))
        ==> (f' = \v. 0)
Proof
    rpt STRIP_TAC
 >> MP_TAC (ISPECL [``f:real->real``, ``f':real->real``,
                    ``x:real``, ``s:real->bool``]
                   DIFFERENTIAL_COMPONENT_ZERO_AT_MAXMIN)
 >> ASM_SIMP_TAC real_ss [FUN_EQ_THM, REAL_LE_REFL]
QED

(* ------------------------------------------------------------------------- *)
(* The traditional Rolle theorem in one dimension.      1056                 *)
(* ------------------------------------------------------------------------- *)

val ROLLE = store_thm ("ROLLE",
 ``!f:real->real f' a b.
        a < b /\ (f a = f b) /\
        f continuous_on interval[a,b] /\
        (!x. x IN interval(a,b) ==> (f has_derivative f'(x)) (at x))
        ==> ?x. x IN interval(a,b) /\ (f'(x) = \v. 0)``,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   ``?x. x:real IN interval(a,b) /\
        ((!y. y IN interval(a,b) ==> (f x):real <= (f y)) \/
         (!y. y IN interval(a,b) ==> (f y):real <= (f x)))``
  MP_TAC THENL
   [ALL_TAC, METIS_TAC[DIFFERENTIAL_ZERO_MAXMIN, OPEN_INTERVAL]] THEN
  MAP_EVERY (MP_TAC o ISPECL
            [``(f:real->real)``, ``interval[a:real,b]``])
            [CONTINUOUS_ATTAINS_SUP, CONTINUOUS_ATTAINS_INF] THEN
  REWRITE_TAC[COMPACT_INTERVAL, o_ASSOC] THEN
  ASM_SIMP_TAC real_ss [CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_ID, o_DEF] THEN
  REWRITE_TAC[GSYM INTERVAL_EQ_EMPTY, CONJ_ASSOC, REAL_LE_ANTISYM] THEN
  ASM_SIMP_TAC real_ss [UNWIND_THM1, REAL_NOT_LT, REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN ``d:real`` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC ``(d:real) IN interval(a,b)`` THENL
   [ASM_MESON_TAC[SUBSET_DEF, INTERVAL_OPEN_SUBSET_CLOSED], ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN ``c:real`` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC ``(c:real) IN interval(a,b)`` THENL
   [ASM_MESON_TAC[SUBSET_DEF, INTERVAL_OPEN_SUBSET_CLOSED], ALL_TAC] THEN
  SUBGOAL_THEN ``?x:real. x IN interval(a,b)`` MP_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY, GSYM INTERVAL_EQ_EMPTY] THEN
    ASM_MESON_TAC[REAL_LE_ANTISYM, REAL_NOT_LE],
    ALL_TAC] THEN
  STRIP_TAC THEN Q.EXISTS_TAC `x` THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP INTERVAL_CASES)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC)) THEN
  ASM_MESON_TAC[REAL_LE_ANTISYM, SUBSET_DEF, INTERVAL_OPEN_SUBSET_CLOSED]);

(* ------------------------------------------------------------------------- *)
(* One-dimensional mean value theorem. 1076                                  *)
(* ------------------------------------------------------------------------- *)

val MVT = store_thm ("MVT",
 ``!f:real->real f' a b.
        a < b /\ f continuous_on interval[a,b] /\
        (!x. x IN interval(a,b) ==> (f has_derivative f'(x)) (at x))
        ==> ?x. x IN interval(a,b) /\ (f(b) - f(a) = f'(x) (b - a))``,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [``\x. f(x) - ((f b - f a) / (b - a)) * x:real``,
                ``\k:real x:real.
                    f'(k)(x) - ((f b - f a) / (b - a)) * x:real``,
                ``a:real``, ``b:real``]
               ROLLE) THEN
  REWRITE_TAC[] THEN
  Q_TAC SUFF_TAC `(a < b /\
    ((\x. f x - (f b - f a) / (b - a) * x) a =
     (\x. f x - (f b - f a) / (b - a) * x) b)) /\
   (\x. f x - (f b - f a) / (b - a) * x) continuous_on interval [(a,b)] /\
   (!x. x IN interval (a,b) ==>
      ((\x. f x - (f b - f a) / (b - a) * x) has_derivative
       (\k x. f' k x - (f b - f a) / (b - a) * x) x) (at x))` THENL
   [DISCH_TAC THEN ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC THEN
    STRIP_TAC THEN Q.EXISTS_TAC `x` THEN POP_ASSUM MP_TAC THEN
    ASM_SIMP_TAC std_ss [FUN_EQ_THM] THEN DISCH_THEN (MP_TAC o SPEC ``b - a:real``),
    ASM_SIMP_TAC real_ss [CONTINUOUS_ON_SUB, CONTINUOUS_ON_CMUL, CONTINUOUS_ON_ID] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH
       ``(fa - k * a = fb - k * b) <=> (fb - fa = k * (b - a:real))``] THEN
      SIMP_TAC real_ss [real_div, REAL_ARITH ``a * b * c = a * (b * c:real)``] THEN
      `b - a <> 0` by (UNDISCH_TAC ``a < b:real`` THEN REAL_ARITH_TAC) THEN
      ASM_SIMP_TAC real_ss [REAL_MUL_LINV],
      REPEAT STRIP_TAC THEN
      ONCE_REWRITE_TAC [METIS [] ``(f b - f a) / (b - a) * x =
                              (\x. (f b - f a) / (b - a) * x) x:real``] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
      ASM_SIMP_TAC real_ss [HAS_DERIVATIVE_CMUL, HAS_DERIVATIVE_ID, ETA_AX]]] THEN
  `b - a <> 0` by (UNDISCH_TAC ``a < b:real`` THEN REAL_ARITH_TAC) THEN
  ASM_SIMP_TAC real_ss [REAL_DIV_RMUL] THEN REAL_ARITH_TAC);

(* ------------------------------------------------------------------------- *)
(* A nice generalization (see Havin's proof of 5.19 from Rudin's book).      *)
(* ------------------------------------------------------------------------- *)

val MVT_GENERAL = store_thm ("MVT_GENERAL",
 ``!f:real->real f' a b.
        a < b /\ f continuous_on interval[a,b] /\
        (!x. x IN interval(a,b) ==> (f has_derivative f'(x)) (at x))
        ==> ?x. x IN interval(a,b) /\
                abs(f(b) - f(a)) <= abs(f'(x) (b - a))``,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [``((\y. (f(b) - f(a)) * y)) o (f:real->real)``,
                ``\x t. ((f(b:real) - f(a)) *
                      ((f':real->real->real) x t))``,
                ``a:real``, ``b:real``]  MVT) THEN
  Q_TAC SUFF_TAC `a < b /\ (\y. (f b - f a) * y) o
   f continuous_on interval [(a,b)] /\
   (!x. x IN interval (a,b) ==>
    ((\y. (f b - f a) * y) o f has_derivative
     (\x t. (f b - f a) * f' x t) x) (at x))` THENL
   [ALL_TAC,
    ASM_SIMP_TAC real_ss [] THEN CONJ_TAC THENL
    [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
     ASM_SIMP_TAC std_ss [CONTINUOUS_ON_ID, CONTINUOUS_ON_CONST, CONTINUOUS_ON_MUL],
     ALL_TAC] THEN
    REPEAT STRIP_TAC THEN SIMP_TAC std_ss [o_DEF] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN METIS_TAC []] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC THEN
  STRIP_TAC THEN Q.EXISTS_TAC `x` THEN POP_ASSUM MP_TAC THEN
  ASM_SIMP_TAC real_ss [GSYM REAL_SUB_LDISTRIB, o_THM] THEN
  DISCH_TAC THEN ASM_CASES_TAC ``(f:real->real) b = f a`` THENL
   [ASM_SIMP_TAC std_ss [REAL_SUB_REFL, ABS_0, ABS_POS], ALL_TAC] THEN
  REWRITE_TAC [REAL_LE_LT] THEN DISJ2_TAC THEN
  MATCH_MP_TAC REAL_EQ_LMUL_IMP THEN
  Q.EXISTS_TAC `abs((f:real->real) b - f a)` THEN
  ASM_SIMP_TAC real_ss [GSYM ABS_MUL] THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);

(* ------------------------------------------------------------------------- *)
(* Operator norm.                                                            *)
(* ------------------------------------------------------------------------- *)

val oabs = new_definition ("oabs",
         ``oabs (f:real->real) = sup { abs(f x) | abs(x) = &1 }``);

val ABS_BOUND_GENERALIZE = store_thm ("ABS_BOUND_GENERALIZE",
 ``!f:real->real b.
        linear f
        ==> ((!x. (abs(x) = &1) ==> abs(f x) <= b) <=>
             (!x. abs(f x) <= b * abs(x)))``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [ALL_TAC, ASM_MESON_TAC[REAL_MUL_RID]] THEN
  X_GEN_TAC ``x:real`` THEN ASM_CASES_TAC ``x:real = 0`` THENL
   [ASM_REWRITE_TAC[ABS_0, REAL_MUL_RZERO] THEN
    ASM_MESON_TAC[LINEAR_0, ABS_0, REAL_LE_REFL],
    ALL_TAC] THEN
  `0 < abs x` by (ASM_SIMP_TAC std_ss [GSYM ABS_NZ]) THEN
  ASM_SIMP_TAC real_ss [GSYM REAL_LE_LDIV_EQ, ABS_NZ, real_div] THEN
  MATCH_MP_TAC(REAL_ARITH ``abs(a * b) <= c ==> b * a <= c:real``) THEN
  ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC std_ss [ABS_ABS, GSYM ABS_INV] THEN
  REWRITE_TAC [GSYM ABS_MUL] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[GSYM(MATCH_MP LINEAR_CMUL th)]) THEN
  ASM_SIMP_TAC real_ss [ABS_MUL, ABS_INV, ABS_ABS, REAL_MUL_LINV, ABS_0]);

val OABS = store_thm ("OABS",
 ``!f:real->real.
        linear f
        ==> (!x. abs(f x) <= oabs f * abs(x)) /\
            (!b. (!x. abs(f x) <= b * abs(x)) ==> oabs f <= b)``,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(Q.SPEC `{ abs((f:real->real) x) | abs(x) = &1 }` SUP) THEN
  SIMP_TAC std_ss [GSPECIFICATION, LEFT_IMP_EXISTS_THM] THEN
  SIMP_TAC std_ss [LEFT_FORALL_IMP_THM, RIGHT_EXISTS_AND_THM, EXISTS_REFL] THEN
  ASM_SIMP_TAC std_ss [ABS_BOUND_GENERALIZE, GSYM oabs, GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
  ASM_MESON_TAC[REAL_CHOOSE_SIZE, LINEAR_BOUNDED, REAL_POS]);

(* ------------------------------------------------------------------------- *)
(* Still more general bound theorem.   1168                                  *)
(* ------------------------------------------------------------------------- *)

val DIFFERENTIABLE_BOUND = store_thm ("DIFFERENTIABLE_BOUND",
 ``!f:real->real f' s B.
        convex s /\
        (!x. x IN s ==> (f has_derivative f'(x)) (at x within s)) /\
        (!x. x IN s ==> oabs(f'(x)) <= B)
        ==> !x y. x IN s /\ y IN s ==> abs(f(x) - f(y)) <= B * abs(x - y)``,
  ONCE_REWRITE_TAC[ABS_SUB] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    ``!x y. x IN s ==> abs((f':real->real->real)(x) y) <= B * abs(y)``
  ASSUME_TAC THENL
   [FULL_SIMP_TAC std_ss [has_derivative] THEN RW_TAC std_ss [] THEN
    FIRST_X_ASSUM (MP_TAC o Q.SPEC `x'`) THEN
    FIRST_X_ASSUM (MP_TAC o Q.SPEC `x'`) THEN
    ASM_REWRITE_TAC [] THEN RW_TAC std_ss [] THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP OABS) THEN RW_TAC std_ss [] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `oabs (f' x') * abs y'` THEN
    ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC std_ss [REAL_LE_REFL, ABS_POS] THEN
    SIMP_TAC std_ss [oabs] THEN MATCH_MP_TAC REAL_LE_SUP' THEN
    SIMP_TAC std_ss [GSPECIFICATION] THEN Q.EXISTS_TAC `oabs (f' x') * abs 1` THEN
    Q.EXISTS_TAC `abs (f' x' 1)` THEN METIS_TAC [ABS_POS, ABS_1],
    ALL_TAC] THEN
  SUBGOAL_THEN
   ``!u. u IN interval[0,1] ==> (x + u * (y - x) :real) IN s``
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL] THEN SIMP_TAC std_ss [REAL_LE_REFL] THEN
    REWRITE_TAC[REAL_ARITH ``x + u * (y - x) = (&1 - u) * x + u * y:real``] THEN
    ASM_MESON_TAC[CONVEX_ALT],
    ALL_TAC] THEN
  SUBGOAL_THEN
   ``!u. u IN interval(0,1) ==> (x + u * (y - x) :real) IN s``
  ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_DEF, INTERVAL_OPEN_SUBSET_CLOSED], ALL_TAC] THEN
  MP_TAC(SPECL
   [``(f:real->real) o (\u. x + u * (y - x))``,
    ``(\u. (f':real->real->real) (x + u * (y - x)) o
         (\u. 0 + u * (y - x)))``,
    ``0:real``, ``1:real``] MVT_GENERAL) THEN
  SIMP_TAC real_ss [o_DEF, REAL_ARITH ``x + &1 * (y - x) = y:real``,
              REAL_MUL_LZERO, REAL_SUB_RZERO, REAL_ADD_RID] THEN
  SIMP_TAC real_ss [REAL_MUL_LID] THEN
  Q_TAC SUFF_TAC `(\u. f (x + u * (y - x))) continuous_on interval [(0,1)] /\
   (!x'. x' IN interval (0,1) ==>
    ((\u. f (x + u * (y - x))) has_derivative
     (\u. f' (x + x' * (y - x)) (u * (y - x)))) (at x'))` THENL
  [DISCH_TAC THEN ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC THEN
   ASM_MESON_TAC[REAL_ADD_LID, REAL_LE_TRANS],
   ALL_TAC] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC [METIS [] ``(x + u * (y - x)) = (\u. x + u * (y - x)) u:real``] THEN
    MATCH_MP_TAC (SIMP_RULE std_ss [o_DEF] CONTINUOUS_ON_COMPOSE) THEN
    SIMP_TAC real_ss [CONTINUOUS_ON_ADD, CONTINUOUS_ON_CONST, CONTINUOUS_ON_MUL,
             o_DEF, CONTINUOUS_ON_ID] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC ``s:real->bool`` THEN
    ASM_SIMP_TAC real_ss [SUBSET_DEF, FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN, differentiable,
                  CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN],
    ALL_TAC] THEN
  X_GEN_TAC ``a:real`` THEN DISCH_TAC THEN
  SUBGOAL_THEN ``a IN interval(0:real,1) /\ open(interval(0:real,1))``
  MP_TAC THENL [ASM_MESON_TAC[OPEN_INTERVAL], ALL_TAC] THEN
  DISCH_THEN(fn th => ONCE_REWRITE_TAC[GSYM(MATCH_MP
    HAS_DERIVATIVE_WITHIN_OPEN th)]) THEN
  ONCE_REWRITE_TAC [METIS [] ``(x + u * (y - x) = (\u. x + u * (y - x)) u) /\
                               (u * (y - x) = (\u. u * (y - x)) u:real)``] THEN
  MATCH_MP_TAC (SIMP_RULE std_ss [o_DEF] DIFF_CHAIN_WITHIN) THEN
  CONJ_TAC THENL
  [ALL_TAC,
   MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
   EXISTS_TAC ``s:real->bool`` THEN
   ASM_SIMP_TAC real_ss [SUBSET_DEF, FORALL_IN_IMAGE]] THEN
  Q_TAC SUFF_TAC `((\u. x + u * (y - x)) has_derivative (\u. u * (y - x))) =
   ((\u. (\u. x) u + (\u. u * (y - x)) u) has_derivative
    (\u. (\u:real. 0:real) u + (\u. u * (y - x)) u))` THENL
  [DISC_RW_KILL, SIMP_TAC real_ss []] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC [HAS_DERIVATIVE_CONST] THEN
  ONCE_REWRITE_TAC [REAL_MUL_COMM] THEN
  ONCE_REWRITE_TAC [METIS [] ``(\u. (y - x) * u) = (\u. (y - x) * (\u. u) u:real)``] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN SIMP_TAC std_ss [HAS_DERIVATIVE_ID]);

(* ------------------------------------------------------------------------- *)
(* Uniformly convergent sequence of derivatives.   1948                      *)
(* ------------------------------------------------------------------------- *)

val HAS_DERIVATIVE_SEQUENCE_LIPSCHITZ = store_thm ("HAS_DERIVATIVE_SEQUENCE_LIPSCHITZ",
 ``!s f:num->real->real f' g'.
        convex s /\
        (!n x. x IN s ==> ((f n) has_derivative (f' n x)) (at x within s)) /\
        (!e. &0 < e
             ==> ?N. !n x h. n >= N /\ x IN s
                             ==> abs(f' n x h - g' x h) <= e * abs(h))
        ==> !e. &0 < e
                ==> ?N. !m n x y. m >= N /\ n >= N /\ x IN s /\ y IN s
                                  ==> abs((f m x - f n x) - (f m y - f n y))
                                      <= e * abs(x - y)``,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o Q.SPEC `e / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  Q_TAC SUFF_TAC `!N. (!n x h. n >= N /\ x IN s ==>
       abs (f' n x h - g' x h) <= e / 2 * abs h) ==>
  !m n x y. m >= N /\ n >= N /\ x IN s /\ y IN s ==>
    abs (f m x - f n x - (f m y - f n y)) <= e * abs (x - y)` THENL
  [METIS_TAC [MONO_EXISTS], ALL_TAC] THEN
  X_GEN_TAC ``N:num`` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [``m:num``, ``n:num``] THEN
  ASM_CASES_TAC ``m:num >= N`` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC ``n:num >= N`` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC [METIS [] ``(f m x - f n x - (f m y - f n y)) =
   ((\x. f m x - f n x) x - (\y. (f:num->real->real) m y - f n y) y)``] THEN
  MATCH_MP_TAC DIFFERENTIABLE_BOUND THEN
  Q.EXISTS_TAC `\x h. (f':num->real->real->real) m x h - f' n x h` THEN
  ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
  [METIS_TAC [HAS_DERIVATIVE_SUB], ALL_TAC] THEN
  X_GEN_TAC ``x:real`` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   ``!h. abs((f':num->real->real->real) m x h - f' n x h) <= e * abs(h)``
  MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[HAS_DERIVATIVE_WITHIN_ALT]) THENL
  [ALL_TAC,
   Q_TAC SUFF_TAC `linear (\h. f' m x h - f' n x h)` THENL
   [ALL_TAC, MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN METIS_TAC []] THEN
   DISCH_THEN (MP_TAC o MATCH_MP OABS) THEN RW_TAC std_ss []] THEN
  X_GEN_TAC ``h:real`` THEN SUBST1_TAC(REAL_ARITH
   ``(f':num->real->real->real) m x h - f' n x h =
     (f' m x h - g' x h) + -(f' n x h - g' x h)``) THEN
  MATCH_MP_TAC ABS_TRIANGLE_LE THEN
  Q_TAC SUFF_TAC `!a b h. a <= e / &2 * h /\ b <= e / &2 * h ==> a + b <= e * h:real` THENL
  [DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC real_ss [ABS_NEG], ALL_TAC] THEN
  ONCE_REWRITE_TAC [REAL_MUL_COMM] THEN SIMP_TAC real_ss [real_div] THEN
  ONCE_REWRITE_TAC [REAL_ARITH ``a * (b * c) = (a * b) * c:real``] THEN
  SIMP_TAC real_ss [GSYM real_div, REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC);

val HAS_DERIVATIVE_SEQUENCE = store_thm ("HAS_DERIVATIVE_SEQUENCE",
 ``!s f:num->real->real f' g'.
        convex s /\
        (!n x. x IN s ==> ((f n) has_derivative (f' n x)) (at x within s)) /\
        (!e. &0 < e
             ==> ?N. !n x h. n >= N /\ x IN s
                             ==> abs(f' n x h - g' x h) <= e * abs(h)) /\
        (?x l. x IN s /\ ((\n. f n x) --> l) sequentially)
        ==> ?g. !x. x IN s
                    ==> ((\n. f n x) --> g x) sequentially /\
                        (g has_derivative g'(x)) (at x within s)``,

  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN (* O *)
  DISCH_THEN(X_CHOOSE_THEN ``x0:real`` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN ``!e. &0 < e
        ==> ?N. !m n x y. m >= N /\ n >= N /\ x IN s /\ y IN s
           ==> abs(((f:num->real->real) m x - f n x) - (f m y - f n y))
                               <= e * abs(x - y)`` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_SEQUENCE_LIPSCHITZ THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN
   ``?g:real->real. !x. x IN s ==> ((\n. f n x) --> g x) sequentially``
  MP_TAC THENL
   [SIMP_TAC std_ss [GSYM SKOLEM_THM, RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC ``x:real`` THEN DISCH_TAC THEN
    GEN_REWR_TAC I [CONVERGENT_EQ_CAUCHY] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP CONVERGENT_IMP_CAUCHY) THEN
    SIMP_TAC std_ss [cauchy_def, dist] THEN DISCH_TAC THEN
    X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
    ASM_CASES_TAC ``x:real = x0`` THEN ASM_SIMP_TAC std_ss [] THEN
    FIRST_X_ASSUM (MP_TAC o Q.SPEC `e / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN ``N1:num`` STRIP_ASSUME_TAC) THEN
    `0 < abs(x - x0)` by (UNDISCH_TAC ``x <> x0:real`` THEN REAL_ARITH_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o Q.SPEC `e / &2 / abs(x - x0:real)`) THEN
    ASM_SIMP_TAC real_ss [REAL_LT_DIV, ABS_NZ, REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_TAC ``N2:num``) THEN
    EXISTS_TAC ``N1 + N2:num`` THEN X_GEN_TAC ``m:num`` THEN X_GEN_TAC ``n:num`` THEN
    DISCH_THEN(CONJUNCTS_THEN (STRIP_ASSUME_TAC o MATCH_MP
      (ARITH_PROVE ``m >= N1 + N2:num ==> m >= N1 /\ m >= N2``))) THEN
    SUBST1_TAC(REAL_ARITH
     ``(f:num->real->real) m x - f n x =
       (f m x - f n x - (f m x0 - f n x0)) + (f m x0 - f n x0)``) THEN
    MATCH_MP_TAC ABS_TRIANGLE_LT THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [``m:num``, ``n:num``, ``x:real``, ``x0:real``]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [``m:num``, ``n:num``]) THEN
    SIMP_TAC real_ss [real_div] THEN
    ONCE_REWRITE_TAC [REAL_ARITH ``a * b * c * d = a * b * (c * d:real)``] THEN
    ASM_SIMP_TAC real_ss [REAL_LT_IMP_NE, REAL_MUL_LINV] THEN
    ASM_SIMP_TAC real_ss [GSYM real_div, real_sub] THEN
    SIMP_TAC real_ss [REAL_LT_RDIV_EQ, REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC,
    ALL_TAC] THEN
  STRIP_TAC THEN Q.EXISTS_TAC `g` THEN ASM_SIMP_TAC std_ss [] THEN
  X_GEN_TAC ``x:real`` THEN DISCH_TAC THEN
  REWRITE_TAC[HAS_DERIVATIVE_WITHIN_ALT] THEN
  SUBGOAL_THEN ``!e. &0 < e
        ==> ?N. !n x y. n >= N /\ x IN s /\ y IN s
          ==> abs(((f:num->real->real) n x - f n y) - (g x - g y))
                             <= e * abs(x - y)`` ASSUME_TAC THENL
   [X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
    UNDISCH_TAC ``!e:real. 0 < e ==>
        ?N. !m:num n:num x:real y:real.
            m >= N /\ n >= N /\ x IN s /\ y IN s ==>
            abs (f m x - f n x - (f m y - f n y)) <= e * abs (x - y)`` THEN
    DISCH_THEN (MP_TAC o SPEC ``e:real``) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN Q.EXISTS_TAC `N` THEN GEN_TAC THEN
    POP_ASSUM (MP_TAC o Q.SPEC `n`) THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [``u:real``, ``v:real``] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN ``m:num`` o SPECL
      [``m:num``, ``u:real``, ``v:real``]) THEN
    DISCH_TAC THEN MATCH_MP_TAC(ISPEC ``sequentially`` LIM_ABS_UBOUND) THEN
    Q.EXISTS_TAC
      `\m. ((f:num->real->real) n u - f n v) - (f m u - f m v)` THEN
    REWRITE_TAC[eventually, TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    ASM_SIMP_TAC std_ss [SEQUENTIALLY, LIM_SUB, LIM_CONST] THEN EXISTS_TAC ``N:num`` THEN
    ONCE_REWRITE_TAC[REAL_ARITH
     ``(x - y) - (u - v) = (x - u) - (y -  v):real``] THEN
    ASM_MESON_TAC[GREATER_EQ_REFL], ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
    ``!u. ((\n. (f':num->real->real->real) n x u) --> g' x u) sequentially``
    ASSUME_TAC THENL
     [REWRITE_TAC[LIM_SEQUENTIALLY, dist] THEN REPEAT STRIP_TAC THEN
      UNDISCH_TAC ``!e:real. 0 < e ==>
        ?N:num. !n x:real h:real. n >= N /\ x IN s ==>
         abs (f' n x h - g' x h) <= e * abs h`` THEN
      DISCH_TAC THEN ASM_CASES_TAC ``u = 0:real`` THENL
       [FIRST_X_ASSUM (MP_TAC o SPEC ``e:real``),
        FIRST_X_ASSUM (MP_TAC o SPEC ``e / &2 / abs(u:real)``)] THENL
      [ALL_TAC,
       `0 < abs u` by (UNDISCH_TAC ``u <> 0:real`` THEN REAL_ARITH_TAC)] THEN
      ASM_SIMP_TAC arith_ss [ABS_NZ, REAL_LT_DIV, REAL_LT] THEN
      STRIP_TAC THEN Q.EXISTS_TAC `N` THEN GEN_TAC THEN
      POP_ASSUM (MP_TAC o Q.SPEC `n`) THEN
      DISCH_THEN(MP_TAC o SPECL [``x:real``, ``u:real``]) THEN
      DISCH_THEN(fn th => DISCH_TAC THEN MP_TAC th) THEN
      ASM_SIMP_TAC real_ss [GE, ABS_0, REAL_MUL_RZERO, ABS_POS] THEN
      ASM_SIMP_TAC real_ss [REAL_DIV_RMUL, ABS_0] THENL
      [UNDISCH_TAC ``&0 < e:real`` THEN REAL_ARITH_TAC, ALL_TAC] THEN
      SIMP_TAC std_ss [real_div] THEN
      ONCE_REWRITE_TAC [REAL_ARITH ``a * b * c * d = a * b * (c * d:real)``] THEN
      ASM_SIMP_TAC real_ss [REAL_LT_IMP_NE, REAL_MUL_LINV] THEN
      ASM_SIMP_TAC real_ss [GSYM real_div, REAL_LE_RDIV_EQ] THEN
      UNDISCH_TAC ``&0 < e:real`` THEN REAL_ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC[linear] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [``u:real``, ``v:real``],
      MAP_EVERY X_GEN_TAC [``c:real``, ``u:real``]] THEN
    MATCH_MP_TAC(ISPEC ``sequentially`` LIM_UNIQUE) THENL
     [Q.EXISTS_TAC
       `\n. (f':num->real->real->real) n x (u + v)`,
      Q.EXISTS_TAC
       `\n. (f':num->real->real->real) n x (c * u)`] THEN
    ASM_SIMP_TAC real_ss [TRIVIAL_LIMIT_SEQUENTIALLY, LIM_SUB, LIM_ADD, LIM_CMUL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[has_derivative_within, linear]) THEN
    ASM_SIMP_TAC real_ss [REAL_SUB_REFL, LIM_CONST] THEN
    METIS_TAC [LIM_ADD, LIM_CMUL], ALL_TAC] THEN
  X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
  FIRST_X_ASSUM (MP_TAC o Q.SPEC `e / &3`) THEN
  UNDISCH_TAC ``!e:real. 0 < e ==>
        ?N:num. !n x:real h:real. n >= N /\ x IN s ==>
         abs (f' n x h - g' x h) <= e * abs h`` THEN
  DISCH_THEN (MP_TAC o Q.SPEC `e / &3`) THEN
  ASM_SIMP_TAC arith_ss [REAL_LT_DIV, REAL_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN ``N1:num`` ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN ``N2:num`` ASSUME_TAC) THEN
  UNDISCH_TAC ``!n:num x:real h:real. n >= N1 /\ x IN s ==>
    abs (f' n x h - g' x h) <= e / 3 * abs h`` THEN DISCH_TAC THEN
  FIRST_X_ASSUM (MP_TAC o GEN ``y:real`` o
   Q.SPECL [`N1 + N2:num`, `x:real`, `y - x:real`]) THEN
  FIRST_X_ASSUM (MP_TAC o GEN ``y:real`` o
   Q.SPECL [`N1 + N2:num`, `y:real`, `x:real`]) THEN
  FIRST_X_ASSUM(MP_TAC o Q.SPECL [`N1 + N2:num`, `x:real`]) THEN
  ASM_REWRITE_TAC[ARITH_PROVE ``m + n >= m:num /\ m + n >= n``] THEN
  REWRITE_TAC[HAS_DERIVATIVE_WITHIN_ALT] THEN
  DISCH_THEN(MP_TAC o Q.SPEC `e / &3` o CONJUNCT2) THEN
  ASM_SIMP_TAC arith_ss [REAL_LT_DIV, REAL_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN ``d1:real`` STRIP_ASSUME_TAC) THEN
  DISCH_TAC THEN DISCH_TAC THEN
  Q.EXISTS_TAC `d1:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC ``y:real`` THEN
  DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o Q.SPEC `y:real`) THEN
  FIRST_X_ASSUM (MP_TAC o Q.SPEC `y:real`) THEN
  FIRST_X_ASSUM(MP_TAC o Q.SPEC `y:real`) THEN
  Q_TAC SUFF_TAC `!a b c d n. d <= a + b + c
    ==> a <= e / &3 * n ==> b <= e / &3 * n ==> c <= e / &3 * n
        ==> d <= e * n` THENL
  [ALL_TAC,
   ONCE_REWRITE_TAC [REAL_MUL_COMM] THEN SIMP_TAC real_ss [real_div] THEN
   ONCE_REWRITE_TAC [REAL_ARITH ``a * (b * c) = (a * b) * c:real``] THEN
   SIMP_TAC real_ss [GSYM real_div, REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC] THEN
  ASM_SIMP_TAC real_ss [] THEN DISCH_THEN MATCH_MP_TAC THEN
  Q_TAC SUFF_TAC `abs (f (N1 + N2) y - f (N1 + N2) x - (g y - g x)) =
      abs ((g y - g x) - (f (N1 + N2) y - f (N1 + N2) x))` THENL
  [DISC_RW_KILL, SIMP_TAC real_ss [ABS_SUB]] THEN
  MATCH_MP_TAC(REAL_ARITH
   ``(abs(x + y + z) = abs(a)) /\
     abs(x + y + z) <= abs(x) + abs(y + z) /\
     abs(y + z) <= abs(y) + abs(z)
     ==> abs(a) <= abs(x) + abs(y) + abs(z:real)``) THEN
  ONCE_REWRITE_TAC [REAL_ARITH ``a + b + c = a + (b + c:real)``] THEN
  SIMP_TAC std_ss [ABS_TRIANGLE] THEN AP_TERM_TAC THEN REAL_ARITH_TAC);

(* ------------------------------------------------------------------------- *)
(* Differentiation of a series.   HAS_DERIVATIVE_SEQUENCE     2187               *)
(* ------------------------------------------------------------------------- *)

val HAS_DERIVATIVE_SERIES = store_thm ("HAS_DERIVATIVE_SERIES",
  ``!s f:num->real->real f' g' k.
        convex s /\
        (!n x. x IN s ==> ((f n) has_derivative (f' n x)) (at x within s)) /\
        (!e. &0 < e
             ==> ?N. !n x h. n >= N /\ x IN s
                             ==> abs(sum(k INTER {x | 0 <= x /\ x <= n}) (\i. f' i x h) -
                                      g' x h) <= e * abs(h)) /\
        (?x l. x IN s /\ ((\n. f n x) sums l) k)
        ==> ?g. !x. x IN s ==> ((\n. f n x) sums (g x)) k /\
                               (g has_derivative g'(x)) (at x within s)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[sums_def, GSYM numseg] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ONCE_REWRITE_TAC [METIS [] ``sum (k INTER {0 .. n}) (\n. f n x) =
                        (\n x. sum (k INTER {0 .. n}) (\n. f n x)) n x``] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_SEQUENCE THEN Q.EXISTS_TAC
   `(\n:num x:real h:real. sum(k INTER { 0n .. n}) (\n. f' n x h):real)` THEN
  ASM_SIMP_TAC real_ss [FINITE_INTER_NUMSEG] THEN RW_TAC std_ss [] THEN
  ONCE_REWRITE_TAC [METIS [] ``(\n. f' n x h) = (\n. (\n h. f' n x h) n h)``] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_SUM THEN METIS_TAC [FINITE_INTER_NUMSEG, ETA_AX]);

val HAS_DERIVATIVE_SERIES' = store_thm ("HAS_DERIVATIVE_SERIES'",
 ``!s f f' g' k.
         convex s /\
         (!n x. x IN s
                ==> (f n has_derivative (\y. f' n x * y)) (at x within s)) /\
         (!e. &0 < e
              ==> ?N. !n x. n >= N /\ x IN s
                  ==> abs(sum (k INTER { 0n..n}) (\i. f' i x) - g' x) <= e) /\
         (?x l. x IN s /\ ((\n. f n x) sums l) k)
         ==> ?g. !x. x IN s
                     ==> ((\n. f n x) sums g x) k /\
                         (g has_derivative (\y. g' x * y)) (at x within s)``,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [METIS [] ``(\y. g' x * y) = (\x y. (g':real->real) x * y) x``] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_SERIES THEN
  Q.EXISTS_TAC `\n x h. (f':num->real->real) n x * h` THEN
  ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL [ALL_TAC, METIS_TAC[]] THEN
  ONCE_REWRITE_TAC [METIS [] ``(\i. (f':num->real->real) i x' * h) =
                           (\i. (\i. f' i x') i * h)``] THEN
  SIMP_TAC std_ss [SUM_RMUL, GSYM REAL_SUB_RDISTRIB, ABS_MUL] THEN
  Q_TAC SUFF_TAC `!n. {x | x <= n} = { 0n .. n}` THENL
  [METIS_TAC[REAL_LE_RMUL_IMP, ABS_POS], ALL_TAC] THEN
  RW_TAC arith_ss [EXTENSION, GSPECIFICATION, IN_NUMSEG]);

(* ------------------------------------------------------------------------- *)
(* Derivative with composed bilinear function.                               *)
(* ------------------------------------------------------------------------- *)

val HAS_DERIVATIVE_BILINEAR_WITHIN = store_thm ("HAS_DERIVATIVE_BILINEAR_WITHIN",
 ``!h:real->real->real f g f' g' x:real s.
        (f has_derivative f') (at x within s) /\
        (g has_derivative g') (at x within s) /\
        bilinear h
        ==> ((\x. h (f x) (g x)) has_derivative
             (\d. h (f x) (g' d) + h (f' d) (g x))) (at x within s)``,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN ``((g:real->real) --> g(x)) (at x within s)`` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM CONTINUOUS_WITHIN] THEN
    ASM_MESON_TAC[differentiable, DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN],
    ALL_TAC] THEN
  UNDISCH_TAC ``((f:real->real) has_derivative f') (at x within s)`` THEN
  REWRITE_TAC[has_derivative_within] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN
   ``((\y. (f:real->real)(x) + f'(y - x)) --> f(x)) (at x within s)``
  ASSUME_TAC THENL
   [GEN_REWR_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
    Q_TAC SUFF_TAC `((\y. (\y. f x) y + (\y. f' (y - x)) y)
      --> (f x + 0)) (at x within s)` THENL
    [SIMP_TAC std_ss [], ALL_TAC] THEN
    MATCH_MP_TAC LIM_ADD THEN REWRITE_TAC[LIM_CONST] THEN
    SUBGOAL_THEN ``0 = (f':real->real)(x - x)`` SUBST1_TAC THENL
     [ASM_MESON_TAC[LINEAR_0, REAL_SUB_REFL], ALL_TAC] THEN
    ASM_SIMP_TAC std_ss [LIM_LINEAR, LIM_SUB, LIM_CONST, LIM_WITHIN_ID],
    ALL_TAC] THEN
  UNDISCH_TAC ``(g has_derivative g') (at x within s)`` THEN
  ONCE_REWRITE_TAC [has_derivative_within] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  CONJ_TAC THENL
   [UNDISCH_TAC ``bilinear h`` THEN ONCE_REWRITE_TAC [bilinear] THEN
    STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[linear]) THEN ASM_REWRITE_TAC[linear] THEN
    FULL_SIMP_TAC real_ss [] THEN REPEAT STRIP_TAC THEN REAL_ARITH_TAC,
    ALL_TAC] THEN
  MP_TAC(Q.ISPECL [`at (x:real) within s`, `h:real->real->real`]
         LIM_BILINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC ``(g --> g x) (at x within s)`` THEN
  UNDISCH_TAC ``((\y. inv (abs (y - x)) * (f y - (f x + f' (y - x)))) --> 0)
        (at x within s)`` THEN
  REWRITE_TAC[AND_IMP_INTRO] THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  UNDISCH_TAC ``((\y. inv (abs (y - x)) * (g y - (g x + g' (y - x)))) --> 0)
        (at x within s)`` THEN
  UNDISCH_TAC ``((\y. f x + f' (y - x)) --> f x) (at x within s)`` THEN
  ONCE_REWRITE_TAC[AND_IMP_INTRO] THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  REWRITE_TAC[AND_IMP_INTRO] THEN DISCH_THEN(MP_TAC o MATCH_MP LIM_ADD) THEN
  SUBGOAL_THEN
   ``((\y:real. inv(abs(y - x)) * (h:real->real->real) (f'(y - x)) (g'(y - x)))
    --> 0) (at x within s)``
  MP_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN ``B:real`` STRIP_ASSUME_TAC o MATCH_MP
                BILINEAR_BOUNDED_POS) THEN
    X_CHOOSE_THEN ``C:real`` STRIP_ASSUME_TAC
     (MATCH_MP LINEAR_BOUNDED_POS (ASSUME ``linear (f':real->real)``)) THEN
    X_CHOOSE_THEN ``D:real`` STRIP_ASSUME_TAC
     (MATCH_MP LINEAR_BOUNDED_POS (ASSUME ``linear (g':real->real)``)) THEN
    REWRITE_TAC[LIM_WITHIN, dist, REAL_SUB_RZERO] THEN
    X_GEN_TAC ``e:real`` THEN STRIP_TAC THEN Q.EXISTS_TAC `e / (B * C * D)` THEN
    ASM_SIMP_TAC real_ss [REAL_LT_DIV, ABS_MUL, REAL_LT_MUL] THEN
    X_GEN_TAC ``x':real`` THEN STRIP_TAC THEN
    ASM_SIMP_TAC real_ss [ABS_MUL, ABS_ABS, ABS_INV, REAL_LT_IMP_NE] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    Q.EXISTS_TAC `inv(abs(x' - x :real)) *
                B * (C * abs(x' - x)) * (D * abs(x' - x))` THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC [REAL_ARITH ``a * b * c * d = a * (b * c * d:real)``] THEN
      MATCH_MP_TAC REAL_LE_LMUL_IMP THEN SIMP_TAC real_ss [REAL_LE_INV_EQ, ABS_POS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      Q.EXISTS_TAC `B * abs (f' (x' - x)) * abs (g' (x' - x))` THEN
      ASM_SIMP_TAC std_ss [] THEN REWRITE_TAC [GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL_IMP THEN ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE] THEN
      ONCE_REWRITE_TAC [REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC real_ss [ABS_POS],
      ONCE_REWRITE_TAC[REAL_ARITH
       ``i * b * (c * x) * (d * x) = (i * x) * x * (b * c * d:real)``] THEN
      ASM_SIMP_TAC real_ss [REAL_MUL_LINV, REAL_LT_IMP_NE, REAL_MUL_LID] THEN
      ASM_SIMP_TAC real_ss [GSYM REAL_LT_RDIV_EQ, REAL_LT_MUL]],
    REWRITE_TAC[AND_IMP_INTRO] THEN DISCH_THEN(MP_TAC o MATCH_MP LIM_ADD) THEN
    SIMP_TAC std_ss (map (C MATCH_MP (ASSUME ``bilinear(h:real->real->real)``))
     [BILINEAR_RZERO, BILINEAR_LZERO, BILINEAR_LADD, BILINEAR_RADD,
      BILINEAR_LMUL, BILINEAR_RMUL, BILINEAR_LSUB, BILINEAR_RSUB]) THEN
    MATCH_MP_TAC EQ_IMPLIES THEN AP_THM_TAC THEN
    BINOP_TAC THEN SIMP_TAC real_ss [FUN_EQ_THM] THEN REAL_ARITH_TAC]);

val HAS_DERIVATIVE_BILINEAR_AT = store_thm ("HAS_DERIVATIVE_BILINEAR_AT",
 ``!h:real->real->real f g f' g' x:real.
        (f has_derivative f') (at x) /\
        (g has_derivative g') (at x) /\
        bilinear h
        ==> ((\x. h (f x) (g x)) has_derivative
             (\d. h (f x) (g' d) + h (f' d) (g x))) (at x)``,
  REWRITE_TAC[has_derivative_at] THEN
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[GSYM has_derivative_within, HAS_DERIVATIVE_BILINEAR_WITHIN]);

val HAS_DERIVATIVE_MUL_WITHIN = store_thm ("HAS_DERIVATIVE_MUL_WITHIN",
 ``!f f' g:real->real g' a s.
        ((f) has_derivative (f')) (at a within s) /\
        (g has_derivative g') (at a within s)
        ==> ((\x. f x * g x) has_derivative
             (\h. f a * g' h + f' h * g a)) (at a within s)``,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[BILINEAR_DOT]
   (Q.ISPEC `\x y:real. x * y` HAS_DERIVATIVE_BILINEAR_WITHIN))) THEN
  SIMP_TAC std_ss [o_DEF]);

val HAS_DERIVATIVE_MUL_AT = store_thm ("HAS_DERIVATIVE_MUL_AT",
 ``!f f' g:real->real g' a.
        ((f) has_derivative (f')) (at a) /\
        (g has_derivative g') (at a)
        ==> ((\x. f x * g x) has_derivative
             (\h. f a * g' h + f' h * g a)) (at a)``,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[HAS_DERIVATIVE_MUL_WITHIN]);

(* ------------------------------------------------------------------------- *)
(* Considering derivative R->R as a vector.                                  *)
(* ------------------------------------------------------------------------- *)

val _ = set_fixity "has_vector_derivative" (Infix(NONASSOC, 450));

val has_vector_derivative = new_definition ("has_vector_derivative",
 ``(f has_vector_derivative f') net <=>
        (f has_derivative (\x. (x) * f')) net``);

val vector_derivative = new_definition ("vector_derivative",
 ``vector_derivative (f:real->real) net =
        @f'. (f has_vector_derivative f') net``);

Theorem HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET :
    !f f' s t x. (f has_vector_derivative f') (at x within s) /\ t SUBSET s
             ==> (f has_vector_derivative f') (at x within t)
Proof
    REWRITE_TAC [has_vector_derivative, HAS_DERIVATIVE_WITHIN_SUBSET]
QED

val HAS_VECTOR_DERIVATIVE_BILINEAR_WITHIN = store_thm ("HAS_VECTOR_DERIVATIVE_BILINEAR_WITHIN",
 ``!h:real->real->real f g f' g' x s.
        (f has_vector_derivative f') (at x within s) /\
        (g has_vector_derivative g') (at x within s) /\
        bilinear h
        ==> ((\x. h (f x) (g x)) has_vector_derivative
             (h (f x) g' + h f' (g x))) (at x within s)``,
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [has_vector_derivative] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_DERIVATIVE_BILINEAR_WITHIN) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bilinear, linear]) THEN
  FULL_SIMP_TAC real_ss [REAL_ADD_LDISTRIB]);

val HAS_VECTOR_DERIVATIVE_BILINEAR_AT = store_thm ("HAS_VECTOR_DERIVATIVE_BILINEAR_AT",
 ``!h:real->real->real f g f' g' x.
        (f has_vector_derivative f') (at x) /\
        (g has_vector_derivative g') (at x) /\
        bilinear h
        ==> ((\x. h (f x) (g x)) has_vector_derivative
             (h (f x) g' + h f' (g x))) (at x)``,
  REPEAT GEN_TAC THEN SIMP_TAC real_ss [has_vector_derivative] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_DERIVATIVE_BILINEAR_AT) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bilinear, linear]) THEN
  FULL_SIMP_TAC real_ss [REAL_ADD_LDISTRIB]);

Theorem HAS_VECTOR_DERIVATIVE_AT_WITHIN :
    !f f' x s. (f has_vector_derivative f') (at x)
           ==> (f has_vector_derivative f') (at x within s)
Proof
    SIMP_TAC std_ss [has_vector_derivative, HAS_DERIVATIVE_AT_WITHIN]
QED

(* ------------------------------------------------------------------------- *)
(* CONTINUOUS_ON_EXP                                                         *)
(* ------------------------------------------------------------------------- *)

(* See limTheory.HAS_DERIVATIVE_POW' for a better version without sum *)
val HAS_DERIVATIVE_POW = store_thm ("HAS_DERIVATIVE_POW",
 ``!q0 n.
     ((\q. q pow n) has_derivative
      (\q. sum { 1n..n} (\i. q0 pow (n - i) * q * q0 pow (i - 1))))
     (at q0)``,
  GEN_TAC THEN INDUCT_TAC THENL
  [`0 < 1:num` by SIMP_TAC arith_ss [] THEN
   FULL_SIMP_TAC real_ss [GSYM NUMSEG_EMPTY, SUM_CLAUSES, pow] THEN
   MATCH_ACCEPT_TAC HAS_DERIVATIVE_CONST, ALL_TAC] THEN
  REWRITE_TAC[pow, SUM_CLAUSES_NUMSEG, ARITH_PROVE ``1 <= SUC n``,
              REAL_SUB_REFL, REAL_MUL_LID, ARITH_PROVE ``SUC n - 1 = n``] THEN
  SUBGOAL_THEN
    ``!q. sum { 1n..n} (\i. q0 pow (SUC n - i) * q * q0 pow (i - 1)) =
         q0 * sum { 1n..n} (\i. q0 pow (n - i) * q * q0 pow (i - 1))``
    (fn th => REWRITE_TAC[th]) THENL
  [GEN_TAC THEN SIMP_TAC std_ss [FINITE_NUMSEG, GSYM SUM_LMUL] THEN
   MATCH_MP_TAC SUM_EQ' THEN
   REWRITE_TAC [IN_NUMSEG, FUN_EQ_THM] THEN REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC std_ss [ARITH_PROVE ``x <= n ==> (SUC n - x = SUC (n - x))``,
                pow, GSYM REAL_MUL_ASSOC], ALL_TAC] THEN
  MP_TAC (Q.ISPEC `(at (q0:real))` HAS_DERIVATIVE_ID) THEN DISCH_TAC THEN
  FULL_SIMP_TAC real_ss [] THEN
  Q_TAC SUFF_TAC `((\q. (\q. q) q * (\q. q pow n) q) has_derivative
   (\q. (\q. q) q0 * (\q. sum {1 .. n} (\i. q0 pow (n - i) * q * q0 pow (i - 1))) q +
     (\q. q) q * (\q. q pow n) q0)) (at q0)` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN MATCH_MP_TAC HAS_DERIVATIVE_MUL_AT THEN
  ASM_SIMP_TAC std_ss [HAS_DERIVATIVE_ID]);

val EXP_CONVERGES_UNIFORMLY_CAUCHY = store_thm ("EXP_CONVERGES_UNIFORMLY_CAUCHY",
 ``!R e. &0 < e /\ &0 < R
         ==> ?N. !m n z. m >= N /\ abs(z) <= R
             ==> abs(sum{m..n} (\i. z pow i / (&(FACT i)))) < e``,
  REPEAT STRIP_TAC THEN
  MP_TAC(Q.ISPECL [`&1 / &2:real`, `\i. R pow i / (&(FACT i):real)`,
                 `from 0`] SERIES_RATIO) THEN
  SIMP_TAC real_ss [SERIES_CAUCHY, LEFT_FORALL_IMP_THM] THEN
  MP_TAC(Q.SPEC `&2 * abs(R)` SIMP_REAL_ARCH) THEN
  MATCH_MP_TAC(TAUT `(a ==> b) /\ (c ==> d) ==> a ==> (b ==> c) ==> d`) THEN
  CONJ_TAC THENL
   [DISCH_THEN (X_CHOOSE_TAC ``N:num``) THEN Q.EXISTS_TAC `N:num` THEN
    X_GEN_TAC ``n:num`` THEN REWRITE_TAC[GE] THEN DISCH_TAC THEN
    SIMP_TAC real_ss [FACT, pow, real_div] THEN
    `inv (&(FACT n * SUC n)) = inv (&(FACT n):real) * inv (&(SUC n))` by
     (ONCE_REWRITE_TAC [GSYM REAL_OF_NUM_MUL] THEN MATCH_MP_TAC REAL_INV_MUL THEN
      SIMP_TAC real_ss [] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN MATCH_MP_TAC LESS_NOT_EQ THEN
      SIMP_TAC arith_ss [FACT_LESS]) THEN
    POP_ASSUM (fn th => SIMP_TAC real_ss [th]) THEN SIMP_TAC real_ss [ABS_MUL] THEN
    ONCE_REWRITE_TAC [REAL_ARITH ``a * b * (c * d) = (a * d) * (b * c:real)``] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC real_ss [REAL_LE_REFL] THEN
    SIMP_TAC real_ss [REAL_LE_MUL, ABS_POS, ABS_INV, REAL_INV_1OVER] THEN
    SIMP_TAC real_ss [REAL_LE_RDIV_EQ, REAL_ARITH ``a * b * c = (a * c) * b:real``] THEN
    REWRITE_TAC [GSYM real_div, GSYM REAL_INV_1OVER] THEN
    `0:real < abs (&SUC n)` by SIMP_TAC real_ss [GSYM ABS_NZ] THEN
    ASM_SIMP_TAC real_ss [REAL_LE_LDIV_EQ] THEN ONCE_REWRITE_TAC [REAL_MUL_COMM] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `&N` THEN ASM_SIMP_TAC real_ss [] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN Q.EXISTS_TAC `&n` THEN
    ASM_SIMP_TAC real_ss [REAL_OF_NUM_LE, ADD1] THEN
    REWRITE_TAC [GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC, ALL_TAC] THEN
   DISCH_THEN(MP_TAC o Q.SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
   STRIP_TAC THEN Q.EXISTS_TAC `N` THEN POP_ASSUM MP_TAC THEN
   REWRITE_TAC[FROM_0, INTER_UNIV] THEN DISCH_TAC THEN GEN_TAC THEN
   GEN_TAC THEN POP_ASSUM (MP_TAC o Q.SPECL [`m`,`n`]) THEN
   DISCH_THEN(fn th => REPEAT STRIP_TAC THEN MP_TAC th) THEN
   ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
   Q.EXISTS_TAC `abs (sum {m .. n} (\i. R pow i / &FACT i))` THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
   Q.EXISTS_TAC `sum {m .. n} (\i. R pow i / &FACT i)` THEN
   SIMP_TAC std_ss [ABS_LE] THEN MATCH_MP_TAC SUM_ABS_LE' THEN
   RW_TAC std_ss [FINITE_NUMSEG, ABS_MUL, real_div] THEN
   MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC std_ss [ABS_POS] THEN
   CONJ_TAC THENL
   [REWRITE_TAC [GSYM POW_ABS] THEN MATCH_MP_TAC POW_LE THEN
    ASM_SIMP_TAC std_ss [ABS_POS], ALL_TAC] THEN
   SIMP_TAC std_ss [REAL_LE_LT] THEN DISJ2_TAC THEN
   REWRITE_TAC [ABS_REFL] THEN MATCH_MP_TAC REAL_LE_INV THEN
   SIMP_TAC std_ss [REAL_LE_LT] THEN DISJ1_TAC THEN
   SIMP_TAC std_ss [FACT_LESS, REAL_LT]);

val REAL_MUL_NZ = store_thm ("REAL_MUL_NZ",
  ``!a b:real. a <> 0 /\ b <> 0 ==> a * b <> 0``,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
  SIMP_TAC real_ss [REAL_ENTIRE]);

(* `sum (0, SUC n)` is defined by realTheory.sum
   `sum {0 ..   n}` is defined by iterateTheory.sum_def
 *)
Theorem lemma_sum_eq[local] :
    !n x:real. sum (0, SUC n) (\n. (\n. inv(&(FACT n))) n * (x pow n)) =
               sum {0  ..  n} (\n. (\n. inv(&(FACT n))) n * (x pow n))
Proof
    NTAC 2 GEN_TAC
 >> SIMP_TAC std_ss [sum_def, iterate, support]
 >> Know `FINITE {n' | n' IN {0 .. n} /\ inv(&FACT n') * x pow n' <> neutral $+}`
 >- (MATCH_MP_TAC FINITE_SUBSET \\
     Q.EXISTS_TAC `{0 .. n}` \\
     SIMP_TAC std_ss [FINITE_NUMSEG] >> SET_TAC [])
 >> DISCH_TAC
 >> ASM_SIMP_TAC std_ss []
 >> Know `neutral $+ = 0:real`
 >- (SIMP_TAC std_ss [neutral] >> MATCH_MP_TAC SELECT_UNIQUE \\
     RW_TAC real_ss [] \\
     reverse EQ_TAC >- REAL_ARITH_TAC \\
     DISCH_THEN (MP_TAC o Q.SPEC `1`) >> REAL_ARITH_TAC)
 >> DISCH_THEN ((FULL_SIMP_TAC std_ss) o wrap)
 (* applying ITSET_alt *)
 >> Q.ABBREV_TAC ‘f = (\n a. inv (&FACT n) * x pow n + a)’
 >> Q.ABBREV_TAC ‘s = {n' | n' IN {0 .. n} /\ inv (&FACT n') * x pow n' <> 0}’
 >> Q.ABBREV_TAC ‘b = 0’
 >> Know ‘ITSET f s b =
          (@g. g {} = b /\
               !x s. FINITE s ==>
                     g (x INSERT s) = if x IN s then g s else f x (g s)) s’
 >- (MATCH_MP_TAC ITSET_alt >> rw [Abbr ‘f’] \\
     REAL_ARITH_TAC)
 >> Rewr'
 >> qunabbrevl_tac [‘f’, ‘s’, ‘b’]
 (* end of changes *)
 >> SELECT_ELIM_TAC
 >> CONJ_TAC
 >- (Q.EXISTS_TAC `(\s. sum s (\n. (\n. inv(&(FACT n))) n * (x pow n)))` \\
     SIMP_TAC std_ss [SUM_CLAUSES])
 >> RW_TAC std_ss [] THEN ASM_CASES_TAC ``x = 0:real`` THENL
  [ASM_SIMP_TAC real_ss [ADD1] THEN ONCE_REWRITE_TAC [ADD_COMM] THEN
   SIMP_TAC std_ss [GSYM SUM_TWO] THEN
   Q_TAC SUFF_TAC `{n' | n' IN {0 .. n} /\ inv (&FACT n') * 0r pow n' <> 0} = {0}` THENL
   [DISCH_TAC,
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_SING, IN_NUMSEG] THEN
    GEN_TAC THEN EQ_TAC THENL
    [STRIP_TAC THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
     RW_TAC arith_ss [] THEN `0 < x''` by METIS_TAC [LESS_0_CASES] THEN
     FULL_SIMP_TAC std_ss [SUC_PRE] THEN
     POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
     ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC arith_ss [POW_0] THEN
     REAL_ARITH_TAC, ALL_TAC] THEN
    DISC_RW_KILL THEN SIMP_TAC real_ss [FACT, pow] THEN
    SIMP_TAC real_ss [REAL_INV_1OVER]] THEN
   ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o Q.SPECL [`0`,`{}`]) THEN
   ASM_SIMP_TAC real_ss [FINITE_EMPTY, NOT_IN_EMPTY, FACT, pow, REAL_INV_1OVER] THEN
   DISCH_TAC THEN SIMP_TAC real_ss [SUM_1, FACT, pow, REAL_ADD_RID_UNIQ] THEN
   Q_TAC SUFF_TAC `(!n:num. n >= 1 ==> ((\n'. 1 / &FACT n' * 0 pow n') n = 0:real))` THENL
   [DISCH_THEN (MP_TAC o MATCH_MP SUM_ZERO) THEN DISCH_THEN (MATCH_MP_TAC) THEN
    ARITH_TAC, ALL_TAC] THEN
   RW_TAC arith_ss [GE] THEN `0 < n'` by (ASM_SIMP_TAC arith_ss []) THEN
   FULL_SIMP_TAC std_ss [SUC_PRE] THEN
   POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
   ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC real_ss [POW_0],
   ALL_TAC] THEN
  Q_TAC SUFF_TAC `!n. inv (&FACT n) * x pow n <> 0` THENL
  [DISCH_TAC,
   GEN_TAC THEN MATCH_MP_TAC REAL_MUL_NZ THEN ASM_SIMP_TAC std_ss [POW_NZ] THEN
   ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
   MATCH_MP_TAC REAL_INV_POS THEN SIMP_TAC arith_ss [REAL_LT, FACT_LESS]] THEN
  ASM_SIMP_TAC real_ss [] THEN
  Q_TAC SUFF_TAC `(\p v.
    (!n s. FINITE s ==> (x' (n INSERT s) = if n IN s then x' s else v n + x' s)) ==>
    (sum (FST p, SUC (SND p) - FST p) v = x' {n' | n' IN {FST p .. SND p}}))
      (0, n) (\n. inv (&FACT n) * x pow n)` THENL
  [ASM_SIMP_TAC arith_ss [], ALL_TAC] THEN MATCH_MP_TAC sum_ind THEN RW_TAC std_ss [] THENL
  [SIMP_TAC arith_ss [SUM_1, IN_NUMSEG] THEN
   ASM_CASES_TAC ``n' = 0:num`` THENL
   [ASM_SIMP_TAC arith_ss [SUM_1] THEN
    ONCE_REWRITE_TAC [SET_RULE ``{n'':num | n'' = 0} = {0}``] THEN
    FIRST_X_ASSUM (MP_TAC o Q.SPECL [`0`,`{}`]) THEN
    ASM_SIMP_TAC real_ss [FINITE_EMPTY, NOT_IN_EMPTY, FACT, pow, REAL_INV_1OVER] THEN
    DISCH_THEN (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
    ASM_SIMP_TAC real_ss [], ALL_TAC] THEN
   `1 - n' = 0` by (ASM_SIMP_TAC arith_ss []) THEN
   Q_TAC SUFF_TAC `{n'' | n' <= n'' /\ (n'' = 0)} = {}` THENL
   [DISC_RW_KILL, ASM_SIMP_TAC arith_ss [EXTENSION, NOT_IN_EMPTY, GSPECIFICATION]] THEN
   ASM_SIMP_TAC real_ss [sum], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [] THEN
  ONCE_REWRITE_TAC [SET_RULE “{n'' | n'' IN {n' .. SUC m}} = {n' .. SUC m}”] >>
  ASM_CASES_TAC ``SUC m < n'`` THENL
  [`{n' .. SUC m} = {}` by METIS_TAC [NUMSEG_EMPTY] THEN
   `SUC (SUC m) - n' = 0` by ASM_SIMP_TAC arith_ss [] THEN
   ASM_SIMP_TAC std_ss [sum], ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
  FIRST_X_ASSUM (MP_TAC o Q.SPECL [`SUC (m)`,`{n' .. m}`]) THEN
  RW_TAC arith_ss [FINITE_NUMSEG, IN_NUMSEG] THEN
  Q_TAC SUFF_TAC `(SUC m INSERT {n' .. m}) = {n' .. m + 1}` THENL
  [DISCH_TAC THEN FULL_SIMP_TAC arith_ss [GSYM ADD1],
   ASM_SIMP_TAC arith_ss [EXTENSION, IN_NUMSEG, IN_INSERT, ADD1]] THEN
  `{n'' | n'' IN {n' .. m}} = {n' .. m}` by SET_TAC [] THEN
  FULL_SIMP_TAC std_ss [] THEN
  `SUC (SUC m) - n' = SUC (SUC m - n')` by ASM_SIMP_TAC arith_ss [] THEN
  ASM_SIMP_TAC std_ss [] THEN ONCE_REWRITE_TAC [sum] THEN
  ASM_SIMP_TAC arith_ss [REAL_ADD_COMM]
QED

(* cf. transcTheory.EXP_CONVERGES *)
Theorem EXP_CONVERGES :
    !z. ((\n. z pow n / (&(FACT n))) sums exp(z)) (from 0)
Proof
    RW_TAC std_ss [exp_def, FROM_0]
 >> ONCE_REWRITE_TAC [REAL_MUL_COMM] >> REWRITE_TAC [GSYM real_div]
 >> SIMP_TAC std_ss [SUMS_INFSUM, summable_def, SERIES_CAUCHY]
 >> REWRITE_TAC[INTER_UNIV]
 >> MP_TAC(Q.SPEC `abs(z) + &1` EXP_CONVERGES_UNIFORMLY_CAUCHY)
 >> SIMP_TAC std_ss [REAL_ARITH ``&0 <= x ==> &0 < x + &1:real``, ABS_POS]
 >> METIS_TAC [REAL_ARITH ``x:real <= x + &1``]
QED

val EXP_CONVERGES_UNIQUE = store_thm ("EXP_CONVERGES_UNIQUE",
 ``!w z. ((\n. z pow n / (&(FACT n))) sums w) (from 0) <=> (w = exp(z))``,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC std_ss [EXP_CONVERGES] THEN
  DISCH_THEN(MP_TAC o C CONJ (Q.SPEC `z` EXP_CONVERGES)) THEN
  REWRITE_TAC[SERIES_UNIQUE]);

val EXP_CONVERGES_UNIFORMLY = store_thm ("EXP_CONVERGES_UNIFORMLY",
 ``!R e. &0 < R /\ &0 < e
         ==> ?N. !n z. n >= N /\ abs(z) < R
            ==> abs(sum{ 0n..n} (\i. z pow i / (&(FACT i))) - exp(z)) <= e``,
  REPEAT STRIP_TAC THEN
  MP_TAC(Q.SPECL [`R:real`, `e / &2`] EXP_CONVERGES_UNIFORMLY_CAUCHY) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN STRIP_TAC THEN Q.EXISTS_TAC `N` THEN
  MAP_EVERY X_GEN_TAC [``n:num``, ``z:real``] THEN STRIP_TAC THEN
  MP_TAC(Q.SPEC `z` EXP_CONVERGES) THEN
  SIMP_TAC std_ss [sums_def, LIM_SEQUENTIALLY, FROM_0, INTER_UNIV, dist] THEN
  DISCH_THEN(MP_TAC o Q.SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN ``M:num`` (MP_TAC o Q.SPEC `n + M + 1`)) THEN
  FIRST_X_ASSUM(MP_TAC o Q.SPECL [`n + 1`, `n + M + 1`, `z`]) THEN
  ASM_SIMP_TAC std_ss [ARITH_PROVE ``(n >= N ==> n + 1 >= N) /\ M <= n + M + 1:num``] THEN
  ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE, LE_0] THEN
  Q.ABBREV_TAC `f = (\i. z pow i / &FACT i)` THEN
  `0 <= n + 1` by ASM_SIMP_TAC arith_ss [] THEN
  ONCE_REWRITE_TAC [ARITH_PROVE ``n + M + 1 = n + (M + 1:num)``] THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP SUM_ADD_SPLIT) THEN
  DISCH_THEN (ASSUME_TAC o Q.SPECL [`f`,`M + 1`]) THEN
  ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC THEN
  GEN_REWR_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [GSYM REAL_HALF] THEN
  REAL_ARITH_TAC);

val HAS_DERIVATIVE_EXP = store_thm ("HAS_DERIVATIVE_EXP",
 ``!z. (exp has_derivative (\y. exp z * y)) (at z)``,
  REPEAT GEN_TAC THEN MP_TAC(Q.ISPECL
   [`ball((&0),abs(z:real) + &1)`,
    `\n z. z pow n / (&(FACT n):real)`,
    `\n z:real. if n = 0 then (&0) else z pow (n-1) / (&(FACT(n-1)))`,
    `exp:real->real`, `from (0)`]
   HAS_DERIVATIVE_SERIES') THEN
  SIMP_TAC real_ss [CONVEX_BALL, OPEN_BALL, IN_BALL, dist] THEN
  SIMP_TAC real_ss [HAS_DERIVATIVE_WITHIN_OPEN, OPEN_BALL, IN_BALL,
           dist, REAL_SUB_LZERO, REAL_SUB_RZERO, ABS_NEG] THEN
  Q_TAC SUFF_TAC `(!n x.
    abs x < abs z + 1 ==>
    ((\z. z pow n / &FACT n) has_derivative
     (\y. (if n = 0 then 0 else x pow (n - 1) / &FACT (n - 1)) * y))
      (at x)) /\
   (!e. 0 < e ==>
      ?N. !n x. n >= N /\ abs x < abs z + 1 ==>
        abs (sum (from 0 INTER {0 .. n})
             (\i. if i = 0 then 0 else x pow (i - 1) / &FACT (i - 1)) -
           exp x) <= e) /\
   (?x l. abs x < abs z + 1 /\ ((\n. x pow n / &FACT n) sums l) (from 0))` THENL
 [DISCH_TAC THEN ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN ``g:real->real`` MP_TAC) THEN
  REWRITE_TAC[EXP_CONVERGES_UNIQUE] THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY Q.EXISTS_TAC [`g`, `&1`] THEN
  REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
  [ALL_TAC,
   FIRST_X_ASSUM(MP_TAC o Q.SPEC `z`) THEN
   Q_TAC SUFF_TAC `abs z < abs z + 1` THENL
   [METIS_TAC [ETA_AX], REAL_ARITH_TAC]] THEN
  GEN_TAC THEN POP_ASSUM (MP_TAC o Q.SPEC `x'`) THEN
  MATCH_MP_TAC MONO_IMP THEN SIMP_TAC std_ss [dist] THEN
  REAL_ARITH_TAC, ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC,
    REPEAT STRIP_TAC THEN
    MP_TAC(Q.SPECL [`abs(z) + &1`, `e`] EXP_CONVERGES_UNIFORMLY) THEN
    ASM_SIMP_TAC std_ss [ABS_POS, REAL_ARITH ``&0 <= x ==> &0 < x + &1:real``] THEN
    DISCH_THEN(X_CHOOSE_TAC ``N:num``) THEN Q.EXISTS_TAC `N + 1` THEN
    MAP_EVERY X_GEN_TAC [``n:num``, ``w:real``] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o Q.SPECL [`n - 1`, `w`]) THEN
    ASM_SIMP_TAC std_ss [ARITH_PROVE ``n >= m + 1 ==> n - 1 >= m:num``] THEN
    REWRITE_TAC[FROM_0, INTER_UNIV] THEN MATCH_MP_TAC EQ_IMPLIES THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN ``{ 0n..n} = 0 INSERT (IMAGE SUC { 0n..n-1})`` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION, IN_INSERT, IN_IMAGE, IN_NUMSEG] THEN
     INDUCT_TAC THEN SIMP_TAC arith_ss [] THEN
     UNDISCH_TAC ``n >= N + 1:num`` THEN ARITH_TAC,
     ALL_TAC] THEN
    SIMP_TAC std_ss [SUM_CLAUSES, IMAGE_FINITE, FINITE_NUMSEG] THEN
    SIMP_TAC real_ss [IN_IMAGE, NOT_SUC, SUC_NOT, REAL_ADD_LID] THEN
    SIMP_TAC std_ss [SUM_IMAGE, FINITE_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ' THEN SIMP_TAC real_ss [IN_NUMSEG, NOT_SUC, o_THM, SUC_SUB1],
    MAP_EVERY Q.EXISTS_TAC [`(&0)`, `exp((&0))`] THEN
    REWRITE_TAC[EXP_CONVERGES, ABS_0] THEN
    SIMP_TAC std_ss [REAL_ARITH ``&0 <= z ==> &0 < z + &1:real``, ABS_POS]] THEN
  X_GEN_TAC ``n:num`` THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC ``n = 0:num`` THEN ASM_REWRITE_TAC [] THENL
  [SIMP_TAC real_ss [pow, FACT, HAS_DERIVATIVE_CONST], ALL_TAC] THEN
  SIMP_TAC std_ss [real_div] THEN ONCE_REWRITE_TAC [REAL_MUL_COMM] THEN
  ONCE_REWRITE_TAC [REAL_ARITH ``a * (b * c) = c * b * a:real``] THEN
  Q_TAC SUFF_TAC `!y. inv (&FACT (n - 1)) * x pow (n - 1) * y =
                      inv (&FACT n) * (&n * x pow (n - 1) * y)` THENL
  [DISC_RW_KILL,
   RW_TAC real_ss [REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN `0 < n` by ASM_SIMP_TAC arith_ss [] THEN
   `?m. n = SUC m` by (Q.EXISTS_TAC `PRE n` THEN ASM_SIMP_TAC arith_ss [SUC_PRE]) THEN
   ASM_SIMP_TAC std_ss [SUC_SUB1, FACT, GSYM REAL_OF_NUM_MUL] THEN
   `~(&SUC m = &0:real)` by ASM_SIMP_TAC arith_ss [NOT_SUC, REAL_OF_NUM_EQ] THEN
   ASM_SIMP_TAC real_ss [REAL_FACT_NZ, REAL_INV_MUL] THEN
   ONCE_REWRITE_TAC [REAL_ARITH ``a * b * c = a * c * b:real``] THEN
   ASM_SIMP_TAC real_ss [REAL_MUL_LINV]] THEN
  Q_TAC SUFF_TAC `((\z. inv (&FACT n) * (\z. z pow n) z) has_derivative
             (\y. inv (&FACT n) * (\y. (&n * x pow (n - 1) * y)) y)) (at x)` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
  Q_TAC SUFF_TAC `(\y. &n * x pow (n - 1) * y) =
    (\y. sum {1 .. n} (\i. x pow (n - i) * y * x pow (i - 1)))` THENL
  [DISC_RW_KILL THEN SIMP_TAC std_ss [HAS_DERIVATIVE_POW], ALL_TAC] THEN
  `FINITE {1 .. n}` by SIMP_TAC std_ss [FINITE_NUMSEG] THEN
  POP_ASSUM (MP_TAC o MATCH_MP SUM_CONST) THEN
  DISCH_THEN (MP_TAC o Q.SPEC `x pow (n - 1)`) THEN SIMP_TAC arith_ss [CARD_NUMSEG] THEN
  DISCH_THEN (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
  ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [REAL_ARITH ``a * b * c = (a * c) * b:real``] THEN
  ABS_TAC THEN SIMP_TAC std_ss [SUM_RMUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUM_EQ' THEN SIMP_TAC arith_ss [GSYM POW_ADD, IN_NUMSEG]);

val HAS_DERIVATIVE_IMP_CONTINUOUS_AT = store_thm ("HAS_DERIVATIVE_IMP_CONTINUOUS_AT",
 ``!f f' x. (f has_derivative f') (at x) ==> f continuous at x``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
  METIS_TAC[differentiable]);

val CONTINUOUS_AT_EXP = store_thm ("CONTINUOUS_AT_EXP",
 ``!z. exp continuous at z``,
  METIS_TAC[HAS_DERIVATIVE_EXP, HAS_DERIVATIVE_IMP_CONTINUOUS_AT]);

val CONTINUOUS_WITHIN_EXP = store_thm ("CONTINUOUS_WITHIN_EXP",
 ``!s z. exp continuous (at z within s)``,
  METIS_TAC[CONTINUOUS_AT_WITHIN, CONTINUOUS_AT_EXP]);

val CONTINUOUS_ON_EXP = store_thm ("CONTINUOUS_ON_EXP",
 ``!s. exp continuous_on s``,
  METIS_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON, CONTINUOUS_AT_EXP]);

val _ = export_theory();
