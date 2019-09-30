(* ========================================================================= *)
(*                                                                           *)
(*               Products of natural numbers and real numbers                *)
(*                                                                           *)
(*        (c) Copyright 2015,                                                *)
(*                       Muhammad Qasim,                                     *)
(*                       Osman Hasan,                                        *)
(*                       Hardware Verification Group,                        *)
(*                       Concordia University                                *)
(*                                                                           *)
(*            Contact:  <m_qasi@ece.concordia.ca>                            *)
(*                                                                           *)
(*                                                                           *)
(*    Note: This theory was ported from HOL Light                            *)
(*                                                                           *)
(*                (c) University of Cambridge 1998                           *)
(*                (c) Copyright, John Harrison and others 1998-2012          *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open numLib unwindLib tautLib Arith prim_recTheory combinTheory quotientTheory
     arithmeticTheory realaxTheory realTheory realLib jrhUtils
     pairTheory seqTheory limTheory transcTheory listTheory mesonLib
     boolTheory pred_setTheory optionTheory numTheory hurdUtils
     sumTheory InductiveDefinition ind_typeTheory;

open cardinalTheory iterateTheory;

val _ = new_theory "product";

(* ------------------------------------------------------------------------- *)
(* MESON, METIS, ASSERT_TAC, ASM_ARITH_TAC                                   *)
(* ------------------------------------------------------------------------- *)

fun MESON ths tm = prove(tm,MESON_TAC ths);
fun METIS ths tm = prove(tm,METIS_TAC ths);

val DISC_RW_KILL = DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
                   POP_ASSUM K_TAC;

fun ASSERT_TAC tm = SUBGOAL_THEN tm STRIP_ASSUME_TAC;

val ASM_ARITH_TAC = REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC;
val ASM_REAL_ARITH_TAC = REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;

(* ------------------------------------------------------------------------- *)
(* misc.                                                                     *)
(* ------------------------------------------------------------------------- *)

val REAL_ADD_AC = store_thm ("REAL_ADD_AC",
 ``(m + n = n + m:real) /\
   ((m + n) + p = m + (n + p):real) /\
   (m + (n + p) = n + (m + p):real)``,
  METIS_TAC[REAL_ADD_ASSOC, REAL_ADD_SYM]);

val MULT_AC = store_thm ("MULT_AC",
 ``(m * n = n * m:num) /\
   ((m * n) * p = m * (n * p:num)) /\
   (m * (n * p) = n * (m * p:num))``,
  MESON_TAC[MULT_ASSOC, MULT_SYM]);

(* ========================================================================= *)
(* Products of natural numbers and real numbers.                             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Products over natural numbers.                                            *)
(* ------------------------------------------------------------------------- *)

val nproduct = new_definition ("nproduct",
  ``nproduct = iterate(( * ):num->num->num)``);

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
        ==> ((nproduct (m..(n+p)) f = nproduct(m..n) f * nproduct(n+(1:num)..n+p) f))``,
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
 ``!f m n. (!x. m <= x /\ x <= n ==> 0 < f x) ==> 0 < nproduct(m..n) f``,
  SIMP_TAC std_ss [NPRODUCT_POS_LT, FINITE_NUMSEG, IN_NUMSEG]);

val NPRODUCT_OFFSET = store_thm ("NPRODUCT_OFFSET",
 ``!f m p. nproduct(m+p..n+p) f = nproduct(m..n) (\i. f(i + p))``,
  SIMP_TAC std_ss [NUMSEG_OFFSET_IMAGE, NPRODUCT_IMAGE,
           EQ_ADD_RCANCEL, FINITE_NUMSEG] THEN
  SIMP_TAC std_ss [o_DEF]);

val NPRODUCT_SING = store_thm ("NPRODUCT_SING",
 ``!f x. nproduct {x} f = f(x)``,
  SIMP_TAC std_ss [NPRODUCT_CLAUSES, FINITE_EMPTY, FINITE_INSERT, NOT_IN_EMPTY, MULT_CLAUSES]);

val NPRODUCT_SING_NUMSEG = store_thm ("NPRODUCT_SING_NUMSEG",
 ``!f n. nproduct(n..n) f = f(n)``,
  REWRITE_TAC[NUMSEG_SING, NPRODUCT_SING]);

val NPRODUCT_CLAUSES_NUMSEG = store_thm ("NPRODUCT_CLAUSES_NUMSEG",
 ``(!m. nproduct(m..(0:num)) f = if m = 0 then f(0) else 1) /\
   (!m n. nproduct(m..SUC n) f = if m <= SUC n then nproduct(m..n) f * f(SUC n)
                                else nproduct(m..n) f)``,
  REWRITE_TAC[NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC std_ss [NPRODUCT_SING, NPRODUCT_CLAUSES, FINITE_NUMSEG, IN_NUMSEG] THEN
  SIMP_TAC arith_ss [ARITH_PROVE ``~(SUC n <= n)``, MULT_AC]);

val NPRODUCT_EQ = store_thm ("NPRODUCT_EQ",
 ``!f g s. (!x. x IN s ==> (f x = g x)) ==> (nproduct s f = nproduct s g)``,
  REWRITE_TAC[nproduct] THEN MATCH_MP_TAC ITERATE_EQ THEN
  SIMP_TAC std_ss [MONOIDAL_MUL]);

val NPRODUCT_EQ_NUMSEG = store_thm ("NPRODUCT_EQ_NUMSEG",
 ``!f g m n. (!i. m <= i /\ i <= n ==> (f(i) = g(i)))
             ==> (nproduct(m..n) f = nproduct(m..n) g)``,
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
 ``!f m n. (nproduct(m..n) f = 0) <=> ?x. m <= x /\ x <= n /\ (f(x) = 0)``,
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
           ==> nproduct(m..n) f <= nproduct(m..n) g``,
  SIMP_TAC std_ss [NPRODUCT_LE, FINITE_NUMSEG, IN_NUMSEG]);

val NPRODUCT_EQ_1 = store_thm ("NPRODUCT_EQ_1",
 ``!f s. (!x:'a. x IN s ==> (f(x) = 1)) ==> (nproduct s f = 1)``,
  REWRITE_TAC[nproduct, GSYM NEUTRAL_MUL] THEN
  SIMP_TAC std_ss [ITERATE_EQ_NEUTRAL, MONOIDAL_MUL]);

val NPRODUCT_EQ_1_NUMSEG = store_thm ("NPRODUCT_EQ_1_NUMSEG",
 ``!f m n. (!i. m <= i /\ i <= n ==> (f(i) = 1)) ==> (nproduct(m..n) f = 1)``,
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
  SIMP_TAC std_ss [NPRODUCT_CLAUSES, MULT_AC, MULT_CLAUSES]);

val NPRODUCT_MUL_NUMSEG = store_thm ("NPRODUCT_MUL_NUMSEG",
 ``!f g m n.
     nproduct(m..n) (\x. f x * g x) = nproduct(m..n) f * nproduct(m..n) g``,
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
 ``!c m n. nproduct (m..n) (\x. c) = c EXP ((n + 1) - m)``,
  SIMP_TAC std_ss [NPRODUCT_CONST, CARD_NUMSEG, FINITE_NUMSEG]);

val NPRODUCT_CONST_NUMSEG_1 = store_thm ("NPRODUCT_CONST_NUMSEG_1",
 ``!c n. nproduct((1:num)..n) (\x. c) = c EXP n``,
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
 ``!f m n. m <= n ==> (nproduct(m..n) f = f(m) * nproduct(m+(1:num)..n) f)``,
  SIMP_TAC std_ss [GSYM NUMSEG_LREC, NPRODUCT_CLAUSES, FINITE_NUMSEG, IN_NUMSEG] THEN
  ARITH_TAC);

val NPRODUCT_CLAUSES_RIGHT = store_thm ("NPRODUCT_CLAUSES_RIGHT",
 ``!f m n. 0 < n /\ m <= n ==> (nproduct(m..n) f = nproduct(m..n-(1:num)) f * f(n))``,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  SIMP_TAC std_ss [LESS_REFL, NPRODUCT_CLAUSES_NUMSEG, SUC_SUB1]);

val NPRODUCT_SUPERSET = store_thm ("NPRODUCT_SUPERSET",
 ``!f:'a->num u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = 1))
        ==> (nproduct v f = nproduct u f)``,
  SIMP_TAC std_ss [nproduct, GSYM NEUTRAL_MUL, ITERATE_SUPERSET, MONOIDAL_MUL]);

val NPRODUCT_PAIR = store_thm ("NPRODUCT_PAIR",
 ``!f m n. nproduct((2:num)*m..(2:num)*n+(1:num)) f = nproduct(m..n) (\i. f(2*i) * f(2*i+1))``,
  MP_TAC(MATCH_MP ITERATE_PAIR MONOIDAL_MUL) THEN
  REWRITE_TAC[nproduct, NEUTRAL_MUL]);

val NPRODUCT_DELETE = store_thm ("NPRODUCT_DELETE",
 ``!f s a. FINITE s /\ a IN s
           ==> (f(a) * nproduct(s DELETE a) f = nproduct s f)``,
  SIMP_TAC std_ss [nproduct, ITERATE_DELETE, MONOIDAL_MUL]);

val NPRODUCT_FACT = store_thm ("NPRODUCT_FACT",
 ``!n. nproduct((1:num)..n) (\m. m) = FACT n``,
  INDUCT_TAC THEN SIMP_TAC arith_ss [NPRODUCT_CLAUSES_NUMSEG, FACT] THEN
  ASM_SIMP_TAC std_ss [ARITH_PROVE ``1 <= SUC n``, MULT_SYM]);

val NPRODUCT_DELTA = store_thm ("NPRODUCT_DELTA",
 ``!s a. nproduct s (\x. if x = a then b else 1) =
         (if a IN s then b else 1)``,
  REWRITE_TAC[nproduct, GSYM NEUTRAL_MUL] THEN
  SIMP_TAC std_ss [ITERATE_DELTA, MONOIDAL_MUL]);

val th = store_thm ("th",
   ``(!f g s.   (!x. x IN s ==> (f(x) = g(x)))
                ==> (nproduct s (\i. f(i)) = nproduct s g)) /\
     (!f g a b. (!i. a <= i /\ i <= b ==> (f(i) = g(i)))
                ==> (nproduct(a..b) (\i. f(i)) = nproduct(a..b) g)) /\
     (!f g p.   (!x. p x ==> (f x = g x))
                ==> (nproduct {y | p y} (\i. f(i)) = nproduct {y | p y} g))``,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NPRODUCT_EQ THEN
    ASM_SIMP_TAC std_ss [GSPECIFICATION, IN_NUMSEG]);

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
        ==> (product (m..(n+p)) f = product(m..n) f * product(n+(1:num)..n+p) f)``,
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
 ``!f m n. (!x. m <= x /\ x <= n ==> &0 <= f x) ==> &0 <= product(m..n) f``,
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
 ``!f m n. (!x. m <= x /\ x <= n ==> &0 < f x) ==> &0 < product(m..n) f``,
  SIMP_TAC std_ss [PRODUCT_POS_LT, FINITE_NUMSEG, IN_NUMSEG]);

val PRODUCT_OFFSET = store_thm ("PRODUCT_OFFSET",
 ``!f m p. product(m+p..n+p) f = product(m..n) (\i. f(i + p))``,
  SIMP_TAC std_ss [NUMSEG_OFFSET_IMAGE, PRODUCT_IMAGE,
           EQ_ADD_RCANCEL, FINITE_NUMSEG] THEN
  SIMP_TAC std_ss [o_DEF]);

val PRODUCT_SING = store_thm ("PRODUCT_SING",
 ``!f x. product {x} f = f(x)``,
  SIMP_TAC std_ss [PRODUCT_CLAUSES, FINITE_EMPTY, FINITE_INSERT, NOT_IN_EMPTY,
                   REAL_MUL_RID]);

val PRODUCT_SING_NUMSEG = store_thm ("PRODUCT_SING_NUMSEG",
 ``!f n. product(n..n) f = f(n)``,
  REWRITE_TAC[NUMSEG_SING, PRODUCT_SING]);

val PRODUCT_CLAUSES_NUMSEG = store_thm ("PRODUCT_CLAUSES_NUMSEG",
 ``(!m. product(m..(0:num)) f = if m = 0 then f(0) else &1) /\
   (!m n. product(m..SUC n) f = if m <= SUC n then product(m..n) f * f(SUC n)
                                else product(m..n) f)``,
  REWRITE_TAC[NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC std_ss [PRODUCT_SING, PRODUCT_CLAUSES, FINITE_NUMSEG, IN_NUMSEG] THEN
  SIMP_TAC std_ss [ARITH_PROVE ``~(SUC n <= n)``, REAL_MUL_ASSOC, REAL_MUL_SYM]);

val PRODUCT_EQ = store_thm ("PRODUCT_EQ",
 ``!f g s. (!x. x IN s ==> (f x = g x)) ==> (product s f = product s g)``,
  REWRITE_TAC[product] THEN MATCH_MP_TAC ITERATE_EQ THEN
  REWRITE_TAC[MONOIDAL_REAL_MUL]);

val PRODUCT_EQ_NUMSEG = store_thm ("PRODUCT_EQ_NUMSEG",
 ``!f g m n. (!i. m <= i /\ i <= n ==> (f(i) = g(i)))
             ==> (product(m..n) f = product(m..n) g)``,
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

val PRODUCT_EQ_0_NUMSEG = store_thm ("PRODUCT_EQ_0_NUMSEG",
 ``!f m n. (product(m..n) f = &0) <=> ?x. m <= x /\ x <= n /\ (f(x) = &0)``,
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
           ==> product(m..n) f <= product(m..n) g``,
  SIMP_TAC std_ss [PRODUCT_LE, FINITE_NUMSEG, IN_NUMSEG]);

val PRODUCT_EQ_1 = store_thm ("PRODUCT_EQ_1",
 ``!f s. (!x:'a. x IN s ==> (f(x) = &1)) ==> (product s f = &1)``,
  REWRITE_TAC[product, GSYM NEUTRAL_REAL_MUL] THEN
  SIMP_TAC std_ss [ITERATE_EQ_NEUTRAL, MONOIDAL_REAL_MUL]);

val PRODUCT_EQ_1_NUMSEG = store_thm ("PRODUCT_EQ_1_NUMSEG",
 ``!f m n. (!i. m <= i /\ i <= n ==> (f(i) = &1)) ==> (product(m..n) f = &1)``,
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

val PRODUCT_MUL_NUMSEG = store_thm ("PRODUCT_MUL_NUMSEG",
 ``!f g m n.
     product(m..n) (\x. f x * g x) = product(m..n) f * product(m..n) g``,
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
 ``!c m n. product (m..n) (\x. c) = c pow ((n + 1) - m)``,
  SIMP_TAC std_ss [PRODUCT_CONST, CARD_NUMSEG, FINITE_NUMSEG]);

val PRODUCT_CONST_NUMSEG_1 = store_thm ("PRODUCT_CONST_NUMSEG_1",
 ``!c n. product((1:num)..n) (\x. c) = c pow n``,
  SIMP_TAC std_ss [PRODUCT_CONST, CARD_NUMSEG_1, FINITE_NUMSEG]);

val PRODUCT_NEG = store_thm ("PRODUCT_NEG",
 ``!f s:'a->bool.
     FINITE s ==> (product s (\i. -(f i)) = -(&1) pow (CARD s) * product s f)``,
  SIMP_TAC std_ss [GSYM PRODUCT_CONST, GSYM PRODUCT_MUL] THEN
  REWRITE_TAC[REAL_MUL_LNEG, REAL_MUL_LID]);

val PRODUCT_NEG_NUMSEG = store_thm ("PRODUCT_NEG_NUMSEG",
 ``!f m n. product(m..n) (\i. -(f i)) =
           -(&1) pow ((n + 1) - m) * product(m..n) f``,
  SIMP_TAC std_ss [PRODUCT_NEG, CARD_NUMSEG, FINITE_NUMSEG]);

val PRODUCT_NEG_NUMSEG_1 = store_thm ("PRODUCT_NEG_NUMSEG_1",
 ``!f n. product((1:num)..n) (\i. -(f i)) = -(&1) pow n * product((1:num)..n) f``,
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
         product(m..n) (\x. f x / g x) = product(m..n) f / product(m..n) g``,
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
 ``!f m n. m <= n ==> (product(m..n) f = f(m) * product(m+(1:num)..n) f)``,
  SIMP_TAC std_ss [GSYM NUMSEG_LREC, PRODUCT_CLAUSES, FINITE_NUMSEG, IN_NUMSEG] THEN
  SIMP_TAC arith_ss []);

val PRODUCT_CLAUSES_RIGHT = store_thm ("PRODUCT_CLAUSES_RIGHT",
 ``!f m n. 0 < n /\ m <= n ==> (product(m..n) f = product(m..n-(1:num)) f * f(n))``,
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
 ``!f m n. product((2:num)*m..(2:num)*n+(1:num)) f = product(m..n) (\i. f(2*i) * f(2*i+1))``,
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

val PRODUCT_CONG = store_thm
  ("PRODUCT_CONG",
  ``(!f g s.   (!x. x IN s ==> (f(x) = g(x)))
           ==> (product s (\i. f(i)) = product s g)) /\
    (!f g a b. (!i. a <= i /\ i <= b ==> (f(i) = g(i)))
           ==> (product(a..b) (\i. f(i)) = product(a..b) g)) /\
    (!f g p.   (!x. p x ==> (f x = g x))
           ==> (product {y | p y} (\i. f(i)) = product {y | p y} g))``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC PRODUCT_EQ
 >> ASM_SIMP_TAC std_ss [GSPECIFICATION, IN_NUMSEG]);

val _ = export_theory();
