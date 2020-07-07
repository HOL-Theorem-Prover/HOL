(* ------------------------------------------------------------------------- *)
(* Borel measurable sets defined on reals (from "examples/diningcryptos")    *)
(* Author: Aaron Coble (2010)                                                *)
(* Cambridge University                                                      *)
(* ------------------------------------------------------------------------- *)
(* Updated by Chun Tian (2020) using some materials from:                    *)
(*                                                                           *)
(*        Lebesgue Measure Theory (lebesgue_measure_hvgScript.sml)           *)
(*                                                                           *)
(*        (c) Copyright 2015,                                                *)
(*                       Muhammad Qasim,                                     *)
(*                       Osman Hasan,                                        *)
(*                       Hardware Verification Group,                        *)
(*                       Concordia University                                *)
(*                                                                           *)
(*            Contact:  <m_qasi@ece.concordia.ca>                            *)
(*                                                                           *)
(* Note: This theory is inspired by Isabelle/HOL                             *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open metisLib arithmeticTheory pred_setTheory pred_setLib numTheory numLib
     listTheory combinTheory pairTheory realTheory realLib jrhUtils realSimps
     simpLib seqTheory real_sigmaTheory transcTheory limTheory RealArith;

open hurdUtils util_probTheory sigma_algebraTheory real_topologyTheory;

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "borel" (renamed to "real_borel")               *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "real_borel";

val ASM_ARITH_TAC = REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC;
val ASM_REAL_ARITH_TAC = REAL_ASM_ARITH_TAC;
val DISC_RW_KILL = DISCH_TAC >> ONCE_ASM_REWRITE_TAC [] >> POP_ASSUM K_TAC;
fun METIS ths tm = prove(tm,METIS_TAC ths);

val set_ss = std_ss ++ PRED_SET_ss;

(* ************************************************************************* *)
(* Basic Definitions                                                         *)
(* ************************************************************************* *)

(* New definition based on open sets. See "borel_def" for the old definition *)
Definition borel :
    borel = sigma univ(:real) {s | open s}
End

val _ = overload_on ("borel_measurable", ``\a. measurable a borel``);

val indicator_fn_def = Define
   `indicator_fn s = \x. if x IN s then (1:real) else (0:real)`;

(* MATHEMATICAL DOUBLE-STRUCK DIGIT ONE *)
val _ = Unicode.unicode_version {u = UTF8.chr 0x1D7D9, tmnm = "indicator_fn"};
val _ = TeX_notation {hol = UTF8.chr 0x1D7D9, TeX = ("\\HOLTokenOne{}", 1)};
val _ = TeX_notation {hol = "indicator_fn",   TeX = ("\\HOLTokenOne{}", 1)};

(* ************************************************************************* *)
(* Proofs                                                                    *)
(* ************************************************************************* *)

val space_borel = store_thm
  ("space_borel", ``space borel = UNIV``,
    METIS_TAC [borel, sigma_def, space_def]);

val sigma_algebra_borel = store_thm
  ("sigma_algebra_borel", ``sigma_algebra borel``,
   RW_TAC std_ss [borel]
   >> MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA
   >> RW_TAC std_ss [subset_class_def, IN_UNIV, IN_IMAGE, SUBSET_DEF]);

val in_borel_measurable_open = store_thm
  ("in_borel_measurable_open",
  ``!f M. f IN borel_measurable M <=>
          (sigma_algebra M) /\
          (!s. s IN subsets (sigma UNIV {s | open s}) ==>
           (PREIMAGE f s) INTER (space M) IN subsets M)``,
  REPEAT GEN_TAC THEN RW_TAC std_ss [measurable_def] THEN
  SIMP_TAC std_ss [GSPECIFICATION] THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC std_ss [] THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [borel],
   SIMP_TAC std_ss [sigma_algebra_borel],
   EVAL_TAC THEN SIMP_TAC std_ss [borel, sigma_def, space_def] THEN
   SIMP_TAC std_ss [IN_UNIV] THEN SIMP_TAC std_ss [IN_DEF] THEN rw[IN_FUNSET],
   FIRST_X_ASSUM MATCH_MP_TAC THEN POP_ASSUM MP_TAC THEN
   SIMP_TAC std_ss [borel, sigma_def, subsets_def, IN_BIGINTER] THEN
   SIMP_TAC std_ss [GSPECIFICATION] THEN REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [SUBSET_DEF, sigma_sets_basic] THEN
   MATCH_MP_TAC sigma_algebra_sigma_sets THEN REWRITE_TAC [POW_DEF] THEN
   SET_TAC []]);

val in_borel_measurable_borel = store_thm
  ("in_borel_measurable_borel",
  ``!f M. f IN borel_measurable M <=>
          (sigma_algebra M) /\
          (!s. s IN subsets borel ==> (PREIMAGE f s) INTER (space M) IN subsets M)``,
  SIMP_TAC std_ss [in_borel_measurable_open, borel]);

val space_in_borel = store_thm ("space_in_borel",
  ``UNIV IN subsets borel``,
  SIMP_TAC std_ss [borel, sigma_def, subsets_def] THEN
  SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION, SUBSET_DEF] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SIMP_TAC std_ss [OPEN_UNIV]);

val borel_open = store_thm ("borel_open",
  ``!A. open A ==> A IN subsets borel``,
  SIMP_TAC std_ss [borel, sigma_def, subsets_def] THEN
  SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION, SUBSET_DEF]);

val borel_closed = store_thm ("borel_closed",
  ``!A. closed A ==> A IN subsets borel``,
  GEN_TAC THEN REWRITE_TAC [closed_def] THEN
  DISCH_THEN (ASSUME_TAC o MATCH_MP borel_open) THEN
  FULL_SIMP_TAC std_ss [borel, sigma_def, subsets_def] THEN
  FULL_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION, SUBSET_DEF] THEN
  GEN_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC ``P:(real->bool)->bool``) THEN
  REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [sigma_algebra_def, algebra_def] THEN
  FULL_SIMP_TAC std_ss [subsets_def, space_def] THEN POP_ASSUM K_TAC THEN
  POP_ASSUM K_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC ``univ(:real) DIFF A``) THEN
  ASM_SIMP_TAC std_ss [SET_RULE ``UNIV DIFF (UNIV DIFF A) = A``]);

val borel_singleton = store_thm ("borel_singleton",
  ``!A x. A IN subsets borel ==> x INSERT A IN subsets borel``,
  REPEAT GEN_TAC THEN ASSUME_TAC borel_closed THEN
  FULL_SIMP_TAC std_ss [borel, sigma_def, subsets_def] THEN
  FULL_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION, SUBSET_DEF] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC ``P:(real->bool)->bool``) THEN
  FIRST_X_ASSUM (MP_TAC o SPEC ``{x}:real->bool``) THEN
  SIMP_TAC std_ss [CLOSED_SING] THEN DISCH_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC ``P:(real->bool)->bool``) THEN
  REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [] THEN
  FULL_SIMP_TAC std_ss [sigma_algebra_def, algebra_def, subsets_def] THEN
  REWRITE_TAC [INSERT_DEF] THEN SIMP_TAC std_ss [GSYM IN_SING, GSYM UNION_DEF] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC []);

val borel_comp = store_thm ("borel_comp",
 ``!A. A IN subsets borel ==> (UNIV DIFF A) IN subsets borel``,
  REPEAT GEN_TAC THEN
  FULL_SIMP_TAC std_ss [borel, sigma_def, subsets_def] THEN
  FULL_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION, SUBSET_DEF] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC ``P:(real->bool)->bool``) THEN
FULL_SIMP_TAC std_ss [sigma_algebra_def, algebra_def, subsets_def, space_def]);

val borel_measurable_image = store_thm ("borel_measurable_image",
  ``!f M x. f IN borel_measurable M ==>
            (PREIMAGE f {x}) INTER space M IN subsets M``,
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [measurable_def] THEN
  SIMP_TAC std_ss [GSPECIFICATION] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC borel_closed THEN
  SIMP_TAC std_ss [CLOSED_SING]);

val borel_measurable_const = store_thm ("borel_measurable_const",
  ``!M c. sigma_algebra M ==> (\x. c) IN borel_measurable M``,
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [measurable_def] THEN
  SIMP_TAC std_ss [GSPECIFICATION] THEN ASM_REWRITE_TAC [sigma_algebra_borel] THEN
  CONJ_TAC THENL [EVAL_TAC THEN SIMP_TAC std_ss [space_borel, IN_UNIV] THEN
   SIMP_TAC std_ss[IN_DEF], ALL_TAC] THEN
  SIMP_TAC std_ss [borel, sigma_def, subsets_def] THEN
  SIMP_TAC std_ss [IN_BIGINTER, SUBSET_DEF, GSPECIFICATION] THEN
  REPEAT STRIP_TAC THEN
  simp[PREIMAGE_def, INTER_DEF, GSPECIFICATION,IN_FUNSET] THEN
  ASM_CASES_TAC ``(c:real) IN s`` THENL
  [ASM_SIMP_TAC std_ss [SET_RULE ``{x | x IN s} = s``] THEN
   MATCH_MP_TAC ALGEBRA_SPACE THEN FULL_SIMP_TAC std_ss [sigma_algebra_def],
   ALL_TAC] THEN
  ASM_SIMP_TAC std_ss [GSPEC_F] THEN MATCH_MP_TAC ALGEBRA_EMPTY THEN
  FULL_SIMP_TAC std_ss [sigma_algebra_def]);

val borel_sigma_sets_subset = store_thm ("borel_sigma_sets_subset",
  ``!A. A SUBSET subsets borel ==> (sigma_sets UNIV A) SUBSET subsets borel``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC sigma_sets_subset THEN
  ASM_SIMP_TAC std_ss [GSYM space_borel, SPACE, sigma_algebra_borel]);

val borel_eq_sigmaI1 = store_thm ("borel_eq_sigmaI1",
  ``!X A f. (borel = sigma UNIV X) /\
     (!x. x IN X ==> x IN subsets (sigma UNIV (IMAGE f A))) /\
     (!i. i IN A ==> f i IN subsets borel) ==>
     (borel = sigma UNIV (IMAGE f A))``,
  RW_TAC std_ss [borel] THEN SIMP_TAC std_ss [sigma_def] THEN
  FULL_SIMP_TAC std_ss [sigma_def, subsets_def, GSYM SUBSET_DEF] THEN
  SIMP_TAC std_ss [EXTENSION, IN_BIGINTER, GSPECIFICATION] THEN
  GEN_TAC THEN FULL_SIMP_TAC std_ss [GSPECIFICATION] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SET_TAC []);

val borel_eq_sigmaI2 = store_thm ("borel_eq_sigmaI2",
  ``!G f A B. (borel = sigma UNIV (IMAGE (\(i,j). G i j) B)) /\
            (!i j. (i,j) IN B ==>
                   G i j IN subsets (sigma UNIV (IMAGE (\(i,j). f i j) A))) /\
            (!i j. (i,j) IN A ==> f i j IN subsets borel) ==>
            (borel = sigma UNIV (IMAGE (\(i,j). f i j) A))``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC borel_eq_sigmaI1 THEN
  EXISTS_TAC ``(IMAGE (\(i,j). (G:'a->'b->real->bool) i j) B)`` THEN
  FULL_SIMP_TAC std_ss [sigma_def, subsets_def, borel] THEN
  FULL_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION] THEN
  CONJ_TAC THENL
  [RW_TAC std_ss [IN_IMAGE] THEN MP_TAC (ISPEC ``x':'a#'b`` ABS_PAIR_THM) THEN
   STRIP_TAC THEN FULL_SIMP_TAC std_ss [], ALL_TAC] THEN
  RW_TAC std_ss [] THEN MP_TAC (ISPEC ``i:'c#'d`` ABS_PAIR_THM) THEN
  STRIP_TAC THEN FULL_SIMP_TAC std_ss [] THEN ASM_SET_TAC []);

val borel_eq_sigmaI3 = store_thm ("borel_eq_sigmaI3",
  ``!f A X. (borel = sigma UNIV X) /\
          (!x. x IN X ==> x IN subsets (sigma UNIV (IMAGE (\(i,j). f i j) A))) /\
          (!i j. (i,j) IN A ==> f i j IN subsets borel) ==>
          (borel = sigma UNIV (IMAGE (\(i,j). f i j) A))``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC borel_eq_sigmaI1 THEN
  EXISTS_TAC ``X:(real->bool)->bool`` THEN
  FULL_SIMP_TAC std_ss [sigma_def, subsets_def, borel] THEN
  FULL_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION] THEN
  RW_TAC std_ss [] THEN MP_TAC (ISPEC ``i:'a#'b`` ABS_PAIR_THM) THEN
   STRIP_TAC THEN FULL_SIMP_TAC std_ss [] THEN ASM_SET_TAC []);

val borel_eq_sigmaI4 = store_thm ("borel_eq_sigmaI4",
  ``!G f A. (borel = sigma UNIV (IMAGE (\(i,j). G i j) A)) /\
            (!i j. (i,j) IN A ==>
                   G i j IN subsets (sigma UNIV (IMAGE f UNIV))) /\
            (!i. f i IN subsets borel) ==>
            (borel = sigma UNIV (IMAGE f UNIV))``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC borel_eq_sigmaI1 THEN
  EXISTS_TAC ``(IMAGE (\(i,j). (G:'a->'b->real->bool) i j) A)`` THEN
  FULL_SIMP_TAC std_ss [sigma_def, subsets_def, borel] THEN
  FULL_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION] THEN
  CONJ_TAC THENL
  [RW_TAC std_ss [IN_IMAGE] THEN MP_TAC (ISPEC ``x':'a#'b`` ABS_PAIR_THM) THEN
   STRIP_TAC THEN FULL_SIMP_TAC std_ss [], ALL_TAC] THEN
  RW_TAC std_ss [IN_UNIV] THEN ASM_SET_TAC []);

val borel_eq_sigmaI5 = store_thm ("borel_eq_sigmaI5",
  ``!G f. (borel = sigma UNIV (IMAGE G UNIV)) /\
          (!i. G i IN subsets (sigma UNIV (IMAGE (\(i,j). f i j) UNIV))) /\
          (!i j. f i j IN subsets borel) ==>
          (borel = sigma UNIV (IMAGE (\(i,j). f i j) UNIV))``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC borel_eq_sigmaI1 THEN
  EXISTS_TAC ``(IMAGE (G:'a->real->bool) UNIV)`` THEN
  FULL_SIMP_TAC std_ss [sigma_def, subsets_def, borel] THEN
  FULL_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION] THEN
  CONJ_TAC THENL
  [RW_TAC std_ss [IN_IMAGE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_SIMP_TAC std_ss [], ALL_TAC] THEN
  RW_TAC std_ss [IN_UNIV] THEN
  MP_TAC (ISPEC ``i:'b#'c`` ABS_PAIR_THM) THEN STRIP_TAC THEN
  ASM_SIMP_TAC std_ss [] THEN ASM_SET_TAC []);

val NON_NEG_REAL_RAT_DENSE = store_thm
  ("NON_NEG_REAL_RAT_DENSE",
  ``!(x:real)(y:real). 0 <= x /\ x < y ==> ?(m:num) (n:num). x < &m / & n /\ &m / &n < y``,
   rpt STRIP_TAC
   >> `0 < y - x` by RW_TAC real_ss [REAL_SUB_LT]
   >> (MP_TAC o Q.SPEC `y - x`) REAL_ARCH >> RW_TAC bool_ss []
   >> POP_ASSUM (MP_TAC o Q.SPEC `1`) >> RW_TAC bool_ss []
   >> Q.ABBREV_TAC `m = minimal (\a. y <= & (SUC a) / & n)`
   >> Q.EXISTS_TAC `m` >> Q.EXISTS_TAC `n`
   >> `0 < n`
        by (ONCE_REWRITE_TAC [GSYM REAL_LT]
            >> MATCH_MP_TAC REAL_LT_TRANS
            >> Q.EXISTS_TAC `1/(y-x)`
            >> CONJ_TAC >- (MATCH_MP_TAC REAL_LT_DIV >> RW_TAC real_ss [])
            >> METIS_TAC [REAL_LT_LDIV_EQ])
   >> (MP_TAC o Q.SPEC `inv (&n)`) REAL_ARCH >> ASM_SIMP_TAC real_ss [REAL_INV_POS]
   >> STRIP_TAC
   >> POP_ASSUM (MP_TAC o Q.SPEC `y`) >> STRIP_TAC
   >> `y * &n < &n'`
        by (FULL_SIMP_TAC std_ss [GSYM real_div]
            >> METIS_TAC [REAL_LT, REAL_LT_RDIV_EQ])
   >> FULL_SIMP_TAC std_ss [GSYM real_div]
   >> `minimal (\a. y <= & a / & n) = SUC m`
        by (MATCH_MP_TAC (GSYM MINIMAL_SUC_IMP)
            >> reverse CONJ_TAC
            >- (RW_TAC real_ss [o_DEF,GSYM real_lt] >> METIS_TAC [REAL_LET_TRANS])
            >> Suff `(\a. y <= & (SUC a) / & n) m` >- RW_TAC std_ss []
            >> Q.UNABBREV_TAC `m`
            >> Q.ABBREV_TAC `P = (\a. y <= & (SUC a) / & n)`
            >> Suff `?a. P a` >- METIS_TAC [MINIMAL_EXISTS]
            >> Q.UNABBREV_TAC `P`
            >> RW_TAC std_ss []
            >> Cases_on `n' = 0`
            >- (FULL_SIMP_TAC real_ss [] >> METIS_TAC [REAL_LT_ANTISYM, REAL_LET_TRANS])
            >> METIS_TAC [num_CASES,REAL_LT_IMP_LE])
   >> `y <= & (SUC m) / & n`
        by (POP_ASSUM (MP_TAC o GSYM) >> RW_TAC std_ss []
            >> Q.ABBREV_TAC `P = (\a. y <= & a / & n)`
            >> METIS_TAC [MINIMAL_EXISTS, REAL_LT_IMP_LE])
   >> CONJ_TAC
   >- (Suff `y - (y - x) < (&(SUC m))/(&n) - inv(&n)`
       >- (SIMP_TAC bool_ss [real_div]
            >> ONCE_REWRITE_TAC [REAL_ARITH ``& m * inv (& n) - inv (& n) = (&m - 1) * inv (&n)``]
            >> SIMP_TAC real_ss [ADD1] >> ONCE_REWRITE_TAC [GSYM REAL_ADD]
            >> SIMP_TAC bool_ss [REAL_ADD_SUB_ALT])
       >> RW_TAC bool_ss [real_div]
       >> ONCE_REWRITE_TAC [REAL_ARITH ``& m * inv (& n) - inv (& n) = (&m - 1) * inv (&n)``]
       >> RW_TAC bool_ss [GSYM real_div]
       >> (MP_TAC o Q.SPECL [`y - (y - x)`,`&(SUC m) - 1`,`&n`]) REAL_LT_RDIV_EQ
       >> RW_TAC arith_ss [REAL_LT] >> ONCE_REWRITE_TAC [REAL_SUB_RDISTRIB]
       >> RW_TAC std_ss [REAL_LT_SUB_RADD]
       >> (MP_TAC o GSYM o Q.SPECL [`y`,`(&(SUC m)) - 1 + ((y-x)*(&n))`,`&n`]) REAL_LT_RDIV_EQ
       >> RW_TAC arith_ss [REAL_LT]
       >> RW_TAC bool_ss [real_div]
       >> ONCE_REWRITE_TAC [REAL_ARITH ``(& (SUC m) - 1 + (y - x) * & n) * inv (& n) =
                                         ((&(SUC m))*(inv(&n))) + ((y - x)*(&n)*inv(&n) - inv (&n))``]
       >> `(y - x) * (& n) * inv (& n) = (y - x)`
                by METIS_TAC [REAL_MUL_RINV, GSYM REAL_MUL_ASSOC, REAL_INJ,
                              DECIDE ``!(n:num). 0 < n ==> ~(n=0)``, REAL_MUL_RID]
       >> POP_ORW
       >> RW_TAC bool_ss [GSYM real_div]
       >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `& (SUC m)/(&n)`
       >> RW_TAC bool_ss [REAL_LT_ADDR, Once REAL_SUB_LT, REAL_INV_1OVER]
       >> (MP_TAC o Q.SPECL [`1`,`y - x`,`&n`]) REAL_LT_LDIV_EQ
       >> RW_TAC arith_ss [REAL_LT, REAL_MUL_COMM])
   >> RW_TAC std_ss [real_lt]
   >> Q.ABBREV_TAC `P = (\a. y <= & a / & n)`
   >> Suff `?n. P n` >- METIS_TAC [DECIDE ``m < SUC m``, MINIMAL_EXISTS]
   >> Q.UNABBREV_TAC `P`
   >> RW_TAC std_ss []
   >> Cases_on `n' = 0`
   >- (FULL_SIMP_TAC real_ss [] >> METIS_TAC [REAL_LT_ANTISYM, REAL_LET_TRANS])
   >> METIS_TAC [num_CASES,REAL_LT_IMP_LE]);

(* cf. extrealTheory.Q_set *)
Definition real_rat_set_def :
    real_rat_set = {x:real | ?a b. (x = (&a/(&b))) /\ (0:real < &b)} UNION
                   {x:real | ?a b. (x = -(&a/(&b))) /\ (0:real < &b)}
End

val _ = overload_on ("q_set", ``real_rat_set``);
val q_set_def = save_thm ("Q_set_def", real_rat_set_def);

val QSET_COUNTABLE = store_thm ("QSET_COUNTABLE",
  ``countable q_set``,
  RW_TAC std_ss [q_set_def] THEN
  MATCH_MP_TAC union_countable THEN CONJ_TAC THENL
  [RW_TAC std_ss [pred_setTheory.COUNTABLE_ALT] THEN
   MP_TAC NUM_2D_BIJ_NZ_INV THEN RW_TAC std_ss [] THEN
   Q.EXISTS_TAC `(\(a,b). &a/(&b)) o f` THEN RW_TAC std_ss [GSPECIFICATION] THEN
   FULL_SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF,IN_UNIV] THEN
   PAT_X_ASSUM ``!x. x IN P ==> Q x y`` (MP_TAC o Q.SPEC `(&a,&b)`) THEN
   RW_TAC std_ss [] THEN
   FULL_SIMP_TAC real_ss [IN_CROSS,IN_UNIV,IN_SING,DIFF_DEF,
                          GSPECIFICATION,GSYM REAL_LT_NZ] THEN
   `?y. f y = (a,b)` by METIS_TAC [] THEN
   Q.EXISTS_TAC `y` THEN RW_TAC real_ss [], ALL_TAC] THEN
  RW_TAC std_ss [pred_setTheory.COUNTABLE_ALT] THEN
  MP_TAC NUM_2D_BIJ_NZ_INV THEN
  RW_TAC std_ss [] THEN Q.EXISTS_TAC `(\(a,b). -(&a/(&b))) o f` THEN
  RW_TAC std_ss [GSPECIFICATION] THEN
  FULL_SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF,IN_UNIV] THEN
  PAT_X_ASSUM ``!x. x IN P ==> Q x y`` (MP_TAC o Q.SPEC `(&a,&b)`) THEN
  RW_TAC std_ss [] THEN
  FULL_SIMP_TAC real_ss [IN_CROSS,IN_UNIV,IN_SING,
                         DIFF_DEF,GSPECIFICATION,GSYM REAL_LT_NZ] THEN
  `?y. f y = (a,b)` by METIS_TAC [] THEN Q.EXISTS_TAC `y` THEN
  RW_TAC real_ss []);

val countable_real_rat_set = save_thm
  ("countable_real_rat_set", QSET_COUNTABLE);

val NUM_IN_QSET = store_thm ("NUM_IN_QSET",
  ``!n. &n IN q_set /\ -&n IN q_set``,
  FULL_SIMP_TAC std_ss [q_set_def, IN_UNION, GSPECIFICATION] THEN
  RW_TAC std_ss [] THENL
  [DISJ1_TAC THEN EXISTS_TAC ``n:num`` THEN EXISTS_TAC ``1:num`` THEN
   SIMP_TAC real_ss [],
   DISJ2_TAC THEN EXISTS_TAC ``n:num`` THEN EXISTS_TAC ``1:num`` THEN
   SIMP_TAC real_ss []]);

val OPP_IN_QSET = store_thm ("OPP_IN_QSET",
  ``!x. x IN q_set ==> -x IN q_set``,
  RW_TAC std_ss [q_set_def,EXTENSION,GSPECIFICATION,IN_UNION] THENL
  [DISJ2_TAC THEN Q.EXISTS_TAC `a` THEN Q.EXISTS_TAC `b` THEN
   RW_TAC real_ss [], ALL_TAC] THEN
  DISJ1_TAC THEN Q.EXISTS_TAC `a` THEN Q.EXISTS_TAC `b` THEN
  RW_TAC real_ss [REAL_NEG_NEG]);

val INV_IN_QSET = store_thm ("INV_IN_QSET",
  ``!x. (x IN q_set) /\ (x <> 0) ==> 1/x IN q_set``,
  RW_TAC std_ss [q_set_def,EXTENSION,GSPECIFICATION,IN_UNION] THENL
  [Cases_on `0:real < &a` THENL
   [DISJ1_TAC THEN
    `(&a <> 0:real) /\ (&b <> 0:real)` by FULL_SIMP_TAC real_ss [REAL_POS_NZ,GSYM REAL_LT_NZ] THEN
    Q.EXISTS_TAC `b` THEN Q.EXISTS_TAC `a` THEN FULL_SIMP_TAC std_ss [] THEN
  `1:real / (&a / &b) = (1 / 1) / (&a / &b)` by RW_TAC real_ss [] THEN
    ASM_SIMP_TAC std_ss [] THEN RW_TAC real_ss [div_rat], ALL_TAC] THEN
    DISJ2_TAC THEN
    `&b <> 0:real` by METIS_TAC [REAL_LT_IMP_NE] THEN
    FULL_SIMP_TAC std_ss [] THEN
    `&a <> 0:real` by METIS_TAC [real_div,REAL_ENTIRE] THEN
    FULL_SIMP_TAC real_ss [], ALL_TAC] THEN
  Cases_on `0:real < &a` THENL
  [DISJ2_TAC THEN
   `(&a <> 0:real) /\ (&b <> 0:real)` by
    FULL_SIMP_TAC real_ss [REAL_POS_NZ,GSYM REAL_LT_NZ] THEN
   `&a / &b <> 0:real` by FULL_SIMP_TAC real_ss [REAL_NEG_EQ0] THEN
   Q.EXISTS_TAC `b` THEN Q.EXISTS_TAC `a` THEN FULL_SIMP_TAC std_ss [neg_rat] THEN
   RW_TAC std_ss [real_div, REAL_INV_MUL, REAL_INV_NZ] THEN
   `inv (&b) <> 0:real` by
    FULL_SIMP_TAC real_ss [REAL_POS_NZ,REAL_INV_EQ_0,REAL_POS_NZ] THEN
   RW_TAC real_ss [GSYM REAL_NEG_INV,REAL_NEG_EQ0,REAL_EQ_NEG,REAL_ENTIRE] THEN
   RW_TAC real_ss [REAL_INV_MUL,REAL_INV_INV,REAL_MUL_COMM], ALL_TAC] THEN
  DISJ2_TAC THEN `&b <> 0:real` by METIS_TAC [REAL_LT_IMP_NE] THEN
  `&a <> 0:real` by METIS_TAC [real_div,REAL_ENTIRE,REAL_NEG_EQ0] THEN
  FULL_SIMP_TAC real_ss []);

val ADD_IN_QSET = store_thm ("ADD_IN_QSET",
  ``!x y. (x IN q_set) /\ (y IN q_set) ==> (x+y IN q_set)``,
  RW_TAC std_ss [q_set_def,EXTENSION,GSPECIFICATION,IN_UNION] THENL
  [DISJ1_TAC THEN
   `(&b <> 0:real) /\ (&b' <> 0:real)` by
    FULL_SIMP_TAC real_ss [REAL_LT_IMP_NE] THEN
   `0:real < &(b * b')` by METIS_TAC [REAL_LT_MUL,mult_ints] THEN
   `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE] THEN
   Q.EXISTS_TAC `(a*b' + a'*b)` THEN Q.EXISTS_TAC `b*b'` THEN
   RW_TAC real_ss [REAL_ADD_RAT,REAL_MUL_COMM,REAL_LT_MUL],
   `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [REAL_LT_IMP_NE]
   THEN Cases_on `&a*(&b')-(&a'* (&b)) = 0:real` THENL
   [DISJ1_TAC THEN Q.EXISTS_TAC `0` THEN Q.EXISTS_TAC `1` THEN
    RW_TAC real_ss [REAL_DIV_LZERO, GSYM real_sub] THEN
    RW_TAC std_ss [REAL_SUB_RAT,REAL_DIV_LZERO,REAL_MUL_COMM], ALL_TAC] THEN
   Cases_on `0:real < &a * (&b') - (&a' * (&b))` THENL
   [DISJ1_TAC THEN Q.EXISTS_TAC `(a * b' - a' * b)` THEN
    Q.EXISTS_TAC `b * b'` THEN `0:real < &(b * b')` by
                               METIS_TAC [REAL_LT_MUL,mult_ints] THEN
    `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE] THEN
    RW_TAC std_ss [REAL_SUB_RAT,REAL_MUL_COMM,REAL_LT_MUL,
                   GSYM real_sub,GSYM mult_ints] THEN
    `&a' * &b < &a * (&b'):real` by FULL_SIMP_TAC real_ss [REAL_SUB_LT] THEN
    `a' * b < a * b'` by FULL_SIMP_TAC real_ss [] THEN
    `a' * b <> a * b'` by FULL_SIMP_TAC real_ss [] THEN
    FULL_SIMP_TAC real_ss [REAL_SUB],
    ALL_TAC] THEN
   DISJ2_TAC THEN Q.EXISTS_TAC `(a' * b - a * b')` THEN Q.EXISTS_TAC `b * b'` THEN
   `0:real < &(b * b')` by METIS_TAC [REAL_LT_MUL, mult_ints] THEN
   `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE] THEN
   `&a * &b' - &a' * &b < 0:real` by
    (FULL_SIMP_TAC real_ss [GSYM real_lte,REAL_LE_LT] THEN
    FULL_SIMP_TAC real_ss []) THEN
   `&a * &b' < &a' * (&b):real` by FULL_SIMP_TAC real_ss [REAL_LT_SUB_RADD] THEN
   `a' * b <> a * b'` by FULL_SIMP_TAC real_ss [] THEN
   RW_TAC std_ss [REAL_SUB_RAT,REAL_MUL_COMM,REAL_LT_MUL,GSYM real_sub] THEN
   RW_TAC std_ss [GSYM mult_ints] THEN
   FULL_SIMP_TAC real_ss [REAL_NEG_SUB,REAL_SUB,neg_rat],
   `&b <> 0:real /\ &b' <> 0:real` by
    FULL_SIMP_TAC real_ss [REAL_LT_IMP_NE] THEN
   `0:real < &(b * b')` by METIS_TAC [REAL_LT_MUL,mult_ints] THEN
   `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE] THEN
   Cases_on `&a * (&b')-(&a' * (&b)) = 0:real` THENL
   [DISJ1_TAC THEN Q.EXISTS_TAC `0` THEN Q.EXISTS_TAC `1` THEN
    RW_TAC real_ss [REAL_DIV_LZERO] THEN ONCE_REWRITE_TAC [GSYM REAL_NEG_EQ0] THEN
    RW_TAC std_ss [REAL_NEG_ADD,REAL_NEG_NEG] THEN
    RW_TAC std_ss [REAL_SUB_RAT,REAL_MUL_COMM,REAL_LT_MUL,
                   GSYM real_sub,REAL_DIV_LZERO,REAL_SUB_0],
    ALL_TAC] THEN
   Cases_on `0:real < &a * (&b') - (&a' * (&b))` THENL
   [DISJ2_TAC THEN Q.EXISTS_TAC `(a * b' - a' * b)` THEN Q.EXISTS_TAC `b * b'` THEN
    RW_TAC real_ss [REAL_DIV_LZERO] THEN
    RW_TAC std_ss [REAL_ADD_COMM,GSYM real_sub] THEN
    RW_TAC std_ss [REAL_SUB_RAT,REAL_MUL_COMM,REAL_LT_MUL,
                   GSYM real_sub,GSYM mult_ints] THEN
    `&a' * &b < &a * (&b'):real` by FULL_SIMP_TAC real_ss [REAL_SUB_LT] THEN
    `a' * b < a * b'` by FULL_SIMP_TAC real_ss [] THEN
    `a' * b <> a * b'` by FULL_SIMP_TAC real_ss [] THEN
    FULL_SIMP_TAC real_ss [REAL_SUB,neg_rat], ALL_TAC] THEN
   DISJ1_TAC THEN Q.EXISTS_TAC `(a' * b - a * b')` THEN Q.EXISTS_TAC `b * b'` THEN
   RW_TAC std_ss [REAL_ADD_COMM,GSYM real_sub] THEN
   `&a * &b' - &a' * &b < 0:real` by
    (FULL_SIMP_TAC real_ss [GSYM real_lte,REAL_LE_LT] THEN
    FULL_SIMP_TAC real_ss []) THEN
   `&a * &b' < &a' * (&b):real` by FULL_SIMP_TAC real_ss [REAL_LT_SUB_RADD] THEN
   `a' * b <> a * b'` by FULL_SIMP_TAC real_ss [] THEN
   RW_TAC std_ss [REAL_ADD_COMM,GSYM real_sub,REAL_SUB_RAT,
                  REAL_MUL_COMM,REAL_LT_MUL,GSYM mult_ints] THEN
   FULL_SIMP_TAC real_ss [REAL_NEG_SUB,REAL_SUB,neg_rat],
   DISJ2_TAC THEN
   `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [REAL_LT_IMP_NE] THEN
   `0:real < &(b * b')` by METIS_TAC [REAL_LT_MUL,mult_ints] THEN
   `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE] THEN
   Q.EXISTS_TAC `(a * b' + a' * b)` THEN Q.EXISTS_TAC `b*b'` THEN
   REWRITE_TAC [GSYM mult_ints,GSYM add_ints] THEN
   RW_TAC std_ss [REAL_SUB_LNEG,GSYM real_sub,REAL_EQ_NEG] THEN
   RW_TAC std_ss [REAL_ADD_RAT,REAL_MUL_COMM,REAL_LT_MUL]]);

val SUB_IN_QSET = store_thm ("SUB_IN_QSET",
  ``!x y. (x IN q_set) /\ (y IN q_set) ==> (x - y IN q_set)``,
  RW_TAC std_ss [real_sub] THEN METIS_TAC [OPP_IN_QSET,ADD_IN_QSET]);

val MUL_IN_QSET = store_thm ("MUL_IN_QSET",
  ``!x y. (x IN q_set) /\ (y IN q_set) ==> (x * y IN q_set)``,
  RW_TAC std_ss [q_set_def,EXTENSION,GSPECIFICATION,IN_UNION] THENL
  [DISJ1_TAC THEN
   `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [REAL_LT_IMP_NE] THEN
   `0:real < &(b * b')` by METIS_TAC [REAL_LT_MUL,mult_ints] THEN
   `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE] THEN
   Q.EXISTS_TAC `a * a'` THEN Q.EXISTS_TAC `b * b'` THEN
   FULL_SIMP_TAC real_ss [mult_rat,REAL_LT_REFL,ZERO_LESS_MULT],
   DISJ2_TAC THEN
   `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [REAL_LT_IMP_NE] THEN
   `0:real < &(b * b')` by METIS_TAC [REAL_LT_MUL,mult_ints] THEN
   `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE] THEN
   Q.EXISTS_TAC `a*a'` THEN Q.EXISTS_TAC `b*b'` THEN
   FULL_SIMP_TAC real_ss [mult_rat,REAL_LT_REFL,ZERO_LESS_MULT],
   DISJ2_TAC THEN
   `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [REAL_LT_IMP_NE] THEN
   `0:real < &(b * b')` by METIS_TAC [REAL_LT_MUL,mult_ints] THEN
   `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE] THEN
   Q.EXISTS_TAC `a*a'` THEN Q.EXISTS_TAC `b*b'` THEN
   FULL_SIMP_TAC real_ss [mult_rat,REAL_LT_REFL,ZERO_LESS_MULT],
   DISJ1_TAC THEN
   `&b <> 0:real /\ &b' <> 0:real` by FULL_SIMP_TAC real_ss [REAL_LT_IMP_NE] THEN
   `0:real < &(b * b')` by METIS_TAC [REAL_LT_MUL,mult_ints] THEN
   `&(b * b') <> 0:real` by RW_TAC std_ss [REAL_LT_IMP_NE] THEN
   Q.EXISTS_TAC `a*a'` THEN Q.EXISTS_TAC `b*b'` THEN
   FULL_SIMP_TAC real_ss [mult_rat,REAL_LT_REFL,ZERO_LESS_MULT]]);

val DIV_IN_QSET = store_thm ("DIV_IN_QSET",
  ``!x y. (x IN q_set) /\ (y IN q_set) /\ (y <> 0) ==> (x / y IN q_set)``,
  RW_TAC std_ss [] THEN
  `(inv y) IN q_set` by METIS_TAC [INV_IN_QSET, REAL_INV_1OVER, INV_IN_QSET] THEN
  METIS_TAC [MUL_IN_QSET, real_div]);

val CLG_UBOUND = store_thm ("CLG_UBOUND",
  ``!x. (0 <= x) ==> &(clg(x)) < (x) + 1``,
  RW_TAC std_ss [NUM_CEILING_def] THEN LEAST_ELIM_TAC THEN
  REWRITE_TAC [SIMP_REAL_ARCH] THEN RW_TAC real_ss [] THEN
  FULL_SIMP_TAC real_ss [GSYM real_lt] THEN
  PAT_X_ASSUM ``!m. P`` (MP_TAC o Q.SPEC `n-1`) THEN
  RW_TAC real_ss [] THEN Cases_on `n = 0` THENL
  [METIS_TAC [REAL_LET_ADD2,REAL_LT_01,REAL_ADD_RID], ALL_TAC] THEN
  `0 < n` by RW_TAC real_ss [] THEN
  `&(n - 1) < x:real` by RW_TAC real_ss [] THEN
  `0 <= n-1` by RW_TAC real_ss [] THEN
  `0:real <= (&(n-1))` by RW_TAC real_ss [] THEN
  `0 < x` by METIS_TAC [REAL_LET_TRANS] THEN Cases_on `n = 1` THENL
  [METIS_TAC [REAL_LE_REFL,REAL_ADD_RID,REAL_LTE_ADD2,REAL_ADD_COMM], ALL_TAC] THEN
  `0 <> n-1` by RW_TAC real_ss [] THEN
  `&n - 1 < x` by RW_TAC real_ss [REAL_SUB] THEN
  FULL_SIMP_TAC real_ss [REAL_LT_SUB_RADD]);

val Q_DENSE_IN_REAL_LEMMA = store_thm ("Q_DENSE_IN_REAL_LEMMA",
  ``!x y. (0 <= x) /\ (x < y) ==> ?r. (r IN q_set) /\ (x < r) /\ (r < y)``,
  RW_TAC std_ss [] THEN Cases_on `1:real < y - x` THENL
  [Q.EXISTS_TAC `&(clg y) - 1:real` THEN CONJ_TAC THENL
   [METIS_TAC [SUB_IN_QSET,NUM_IN_QSET], ALL_TAC] THEN
   RW_TAC std_ss [] THENL
   [METIS_TAC [REAL_LT_SUB_LADD,REAL_LT_ADD_SUB,REAL_ADD_COMM,
               REAL_LTE_TRANS,LE_NUM_CEILING], ALL_TAC] THEN
    METIS_TAC [REAL_LT_SUB_RADD,CLG_UBOUND,REAL_LET_TRANS,
               REAL_LT_IMP_LE], ALL_TAC] THEN
  `0 < y - x:real` by RW_TAC real_ss [REAL_SUB_LT] THEN
  (MP_TAC o Q.SPEC `1`) (((UNDISCH o Q.SPEC `y - x`) REAL_ARCH)) THEN
  RW_TAC real_ss [] THEN
  Q_TAC SUFF_TAC `?z. z IN q_set /\ &n * x < z /\ z < &n * y` THENL
  [RW_TAC real_ss [] THEN
   `0 < n` by ( RW_TAC real_ss [] THEN SPOSE_NOT_THEN ASSUME_TAC THEN
   `n = 0` by RW_TAC real_ss [] THEN FULL_SIMP_TAC real_ss []) THEN
   `0 < (&n):real` by RW_TAC real_ss [lt_int] THEN Q.EXISTS_TAC `z / (&n)` THEN
   RW_TAC real_ss [DIV_IN_QSET,NUM_IN_QSET] THENL
   [FULL_SIMP_TAC real_ss [REAL_LT_RDIV_EQ] THEN METIS_TAC [REAL_MUL_SYM],
    ALL_TAC] THEN
   FULL_SIMP_TAC real_ss [REAL_LT_RDIV_EQ,REAL_MUL_COMM,REAL_LT_IMP_NE] THEN
   FULL_SIMP_TAC real_ss [REAL_LT_LDIV_EQ,REAL_MUL_COMM,REAL_LT_IMP_NE],
   ALL_TAC] THEN
  `1 < &n * y - &n * x` by FULL_SIMP_TAC real_ss [REAL_SUB_LDISTRIB] THEN
  Q.EXISTS_TAC `&(clg (&n * y)) - 1` THEN CONJ_TAC THENL
  [METIS_TAC [SUB_IN_QSET,NUM_IN_QSET], ALL_TAC] THEN RW_TAC std_ss [] THENL
  [METIS_TAC [REAL_LT_SUB_LADD,REAL_LT_ADD_SUB,REAL_ADD_COMM,
              REAL_LTE_TRANS,LE_NUM_CEILING], ALL_TAC] THEN
  `0:real <= &n` by RW_TAC real_ss [] THEN
  `0:real <= &n * y` by METIS_TAC [REAL_LE_MUL,REAL_LET_TRANS,REAL_LT_IMP_LE] THEN
  METIS_TAC [REAL_LT_SUB_RADD,CLG_UBOUND,REAL_LET_TRANS,REAL_LT_IMP_LE]);

val Q_DENSE_IN_REAL = store_thm ("Q_DENSE_IN_REAL",
  ``!x y. (x < y) ==> ?r. (r IN q_set) /\ (x < r) /\ (r < y)``,
  RW_TAC std_ss [] THEN Cases_on `0 <= x` THENL
  [RW_TAC std_ss [Q_DENSE_IN_REAL_LEMMA], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [REAL_NOT_LE] THEN
  `-x <= &(clg (-x))` by RW_TAC real_ss [LE_NUM_CEILING] THEN
  `0:real <= x + &clg (-x)` by METIS_TAC [REAL_LE_LNEG] THEN
  `x + &(clg (-x)) < y + &(clg (-x))` by METIS_TAC [REAL_LT_RADD] THEN
  Q_TAC SUFF_TAC `?z. (z IN q_set) /\ (x + &clg (-x) < z) /\
                      (z < y + &clg (-x))` THENL
  [RW_TAC std_ss [] THEN Q.EXISTS_TAC `z - &clg (-x)` THEN
   CONJ_TAC THENL [METIS_TAC [SUB_IN_QSET,NUM_IN_QSET], ALL_TAC] THEN
   RW_TAC std_ss [GSYM REAL_LT_ADD_SUB,REAL_LT_SUB_RADD], ALL_TAC] THEN
  RW_TAC std_ss [Q_DENSE_IN_REAL_LEMMA]);

val REAL_RAT_DENSE = save_thm
  ("REAL_RAT_DENSE", Q_DENSE_IN_REAL);

val BIGUNION_IMAGE_QSET = store_thm
  ("BIGUNION_IMAGE_QSET",
   ``!a f: real -> 'a -> bool. sigma_algebra a /\ f IN (q_set -> subsets a)
            ==> BIGUNION (IMAGE f q_set) IN subsets a``,
   RW_TAC std_ss [SIGMA_ALGEBRA, IN_FUNSET, IN_UNIV, SUBSET_DEF] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN RW_TAC std_ss [IN_IMAGE] THEN
   ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC image_countable THEN
   SIMP_TAC std_ss [QSET_COUNTABLE]);

Definition box : (* `OPEN_interval (a,b)` *)
    box a b = {x:real | a < x /\ x < b}
End

Theorem box_alt :
    !a b. box a b = OPEN_interval (a,b)
Proof
    RW_TAC std_ss [box, OPEN_interval]
QED

val rational_boxes = store_thm ("rational_boxes",
  ``!x e. 0 < e ==> ?a b. a IN q_set /\ b IN q_set /\ x IN box a b /\
                          box a b SUBSET ball (x,e)``,
  RW_TAC std_ss [] THEN
  `0:real < e / 2` by FULL_SIMP_TAC real_ss [] THEN
  KNOW_TAC ``?y. y IN q_set /\ y < x /\ x - y < e / 2`` THENL
  [MP_TAC (ISPECL [``x - e / 2:real``,``x:real``] Q_DENSE_IN_REAL) THEN
   DISCH_TAC THEN
   REWRITE_TAC [REAL_ARITH ``y < x /\ x - y < e:real <=> x - e < y /\ y < x``] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC, STRIP_TAC] THEN
  KNOW_TAC ``?y. y IN q_set /\ x < y /\ y - x < e / 2`` THENL
  [MP_TAC (ISPECL [``x:real``,``x + e / 2:real``] Q_DENSE_IN_REAL) THEN
   DISCH_TAC THEN
   REWRITE_TAC [REAL_ARITH ``x < y /\ y - x < e:real <=> x < y /\ y < x + e``] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC [REAL_LT_ADDR], STRIP_TAC] THEN
  EXISTS_TAC ``y:real`` THEN EXISTS_TAC ``y':real`` THEN
  FULL_SIMP_TAC std_ss [box, GSPECIFICATION, IN_BALL, SUBSET_DEF, dist] THEN
  RW_TAC real_ss [] THEN GEN_REWR_TAC RAND_CONV [GSYM REAL_HALF_DOUBLE] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC ``(x - y) + (y' - x):real`` THEN
  CONJ_TAC THENL [ALL_TAC, METIS_TAC [REAL_LT_ADD2]] THEN
  ASM_REAL_ARITH_TAC);

val open_UNION_box = store_thm ("open_UNION_box",
  ``!M. open M ==> (M = BIGUNION {box a b | box a b SUBSET M})``,
  RW_TAC std_ss [OPEN_CONTAINS_BALL] THEN
  SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, GSPECIFICATION, EXISTS_PROD] THEN
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
  [FIRST_X_ASSUM (MP_TAC o SPEC ``x:real``) THEN ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC ``x:real`` o MATCH_MP rational_boxes) THEN
   STRIP_TAC THEN METIS_TAC [SUBSET_DEF], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF]);

val open_union_box = Q.prove (
   `!M. open M ==>
       (M = BIGUNION
            {box (FST f) (SND f) | f IN {f | box (FST f) (SND f) SUBSET M}})`,
  RW_TAC std_ss [OPEN_CONTAINS_BALL] THEN
  SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, GSPECIFICATION, EXISTS_PROD] THEN
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
  [FIRST_X_ASSUM (MP_TAC o SPEC ``x:real``) THEN ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   FIRST_ASSUM (MP_TAC o SPEC ``x:real`` o MATCH_MP rational_boxes) THEN
   STRIP_TAC THEN METIS_TAC [SUBSET_DEF], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF]);

Theorem open_UNION_rational_box :
    !M. open M ==> (M = BIGUNION {box a b | a IN q_set /\ b IN q_set /\
                                            box a b SUBSET M})
Proof
  RW_TAC std_ss [OPEN_CONTAINS_BALL] THEN
  SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, GSPECIFICATION, EXISTS_PROD] THEN
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
  [FIRST_X_ASSUM (MP_TAC o SPEC ``x:real``) THEN ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC ``x:real`` o MATCH_MP rational_boxes) THEN
   STRIP_TAC THEN METIS_TAC [SUBSET_DEF], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF]
QED

val open_union_rational_box = Q.prove (
   `!M. open M ==>
       (M = BIGUNION
            {box (FST f) (SND f) | f IN {f | (FST f) IN q_set /\ (SND f) IN q_set /\
                                         box (FST f) (SND f) SUBSET M}})`,
  RW_TAC std_ss [OPEN_CONTAINS_BALL] THEN
  SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, GSPECIFICATION, EXISTS_PROD] THEN
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
  [FIRST_X_ASSUM (MP_TAC o SPEC ``x:real``) THEN ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   FIRST_ASSUM (MP_TAC o SPEC ``x:real`` o MATCH_MP rational_boxes) THEN
   STRIP_TAC THEN METIS_TAC [SUBSET_DEF], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF]);

(* key lemma for alternative definitions of ``borel`` *)
Theorem borel_eq_box :
    borel = sigma UNIV (IMAGE (\(a,b). box a b) UNIV)
Proof
    SIMP_TAC std_ss [box] THEN MATCH_MP_TAC borel_eq_sigmaI1
 >> Q.EXISTS_TAC `{s | open s}` >> SIMP_TAC std_ss [borel]
 >> reverse CONJ_TAC
 >- (FULL_SIMP_TAC std_ss [sigma_def, subsets_def] \\
     FULL_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION] \\
     RW_TAC std_ss [] \\
     FULL_SIMP_TAC std_ss [SUBSET_DEF] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     SIMP_TAC std_ss [GSPECIFICATION] \\
     MP_TAC (ISPEC ``i:real#real`` ABS_PAIR_THM) >> STRIP_TAC \\
     FULL_SIMP_TAC std_ss [GSYM interval, OPEN_INTERVAL])
 >> RW_TAC std_ss [GSPECIFICATION]
 >> FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP open_union_rational_box)
 >> ONCE_ASM_REWRITE_TAC []
 >> ONCE_REWRITE_TAC
     [METIS [] ``box (FST f) (SND f) = (\f. box (FST f) (SND f)) f``]
 >> MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UN'
 >> Q.EXISTS_TAC `univ(:real)`
 >> RW_TAC std_ss [] >> fs [GSPECIFICATION]
 >- (Suff `sigma_algebra
       (space (sigma univ(:real)
         (IMAGE (\(a,b). {x | a < x /\ x < b}) univ(:real # real))),
        subsets (sigma univ(:real)
         (IMAGE (\(a,b). {x | a < x /\ x < b}) univ(:real # real))))`
     >- METIS_TAC [SPACE_SIGMA] \\
     SIMP_TAC std_ss [SPACE] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
     SIMP_TAC std_ss [subset_class_def] \\
     SIMP_TAC std_ss [SUBSET_UNIV])
 >- (RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, subsets_def, sigma_def, GSPECIFICATION] \\
     RW_TAC std_ss [IN_BIGINTER, GSPECIFICATION, IN_UNIV] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     rename1 `FST f' IN q_set` \\
     Cases_on `f'` >> Q.EXISTS_TAC `(q, r)` \\
     RW_TAC std_ss [box])
 (* COUNTABLE {f | box (FST f) (SND f) SUBSET x} *)
 >> MATCH_MP_TAC COUNTABLE_SUBSET
 >> EXISTS_TAC ``{f | (?q r. (f = (q,r)) /\ q IN q_set /\ r IN q_set)}``
 >> reverse CONJ_TAC
 >- (ONCE_REWRITE_TAC [SET_RULE ``{f | ?q r. (f = (q,r)) /\ q IN q_set /\ r IN q_set} =
                                  {f | FST f IN q_set /\ SND f IN q_set}``] THEN
     SIMP_TAC std_ss [GSYM CROSS_DEF] THEN
     MATCH_MP_TAC cross_countable THEN
     SIMP_TAC std_ss [QSET_COUNTABLE])
 >> SET_TAC []
QED

Theorem borel_eq_gr_less : (* was: borel_eq_greaterThanLessThan *)
    borel = sigma UNIV (IMAGE (\(a,b). {x | a < x /\ x < b}) UNIV)
Proof
    SIMP_TAC std_ss [borel_eq_box, box]
QED

val halfspace_gt_in_halfspace = prove (
  ``!a. {x | x < a} IN
        subsets (sigma univ(:real) (IMAGE (\(a,i). {x | x < a}) UNIV))``,
  RW_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER, GSPECIFICATION,
                 SUBSET_DEF] THEN ASM_SET_TAC []);

Theorem borel_eq_less : (* was: borel_eq_halfspace_less *)
    borel = sigma UNIV (IMAGE (\a. {x | x < a}) UNIV)
Proof
    ONCE_REWRITE_TAC [SET_RULE
   ``(IMAGE (\a. {x | x < a}) univ(:real)) =
     (IMAGE (\(a:real,i:num). (\a i. {x | x < a}) a i) UNIV)``]
 >> Suff `(borel = sigma univ(:real) (IMAGE (\(i,j). box i j) UNIV)) /\
  (!i j. (i,j) IN UNIV ==>
     box i j IN subsets (sigma univ(:real)
          (IMAGE (\(i,j). (\a i. {x | x < a}) i j)
             univ(:real # num)))) /\
  !i j. (i,j) IN univ(:real # num) ==>
    (\a i. {x | x < a}) i j IN subsets borel`
 >- (DISCH_THEN (MP_TAC o MATCH_MP borel_eq_sigmaI2) \\
     SIMP_TAC std_ss [])
 >> SIMP_TAC std_ss [borel_eq_box]
 >> SIMP_TAC std_ss [GSYM borel_eq_box, IN_UNIV]
 >> KNOW_TAC ``!a b. box a b =
    {x | x IN space (sigma UNIV (IMAGE (\a. {x | x < a}) UNIV)) /\
         (\x. a < x) x /\ (\x. x < b) x}`` THENL
  [SIMP_TAC std_ss [SPACE_SIGMA, box, EXTENSION, GSPECIFICATION, IN_UNIV],
   DISCH_TAC] THEN CONJ_TAC THENL
  [ONCE_ASM_REWRITE_TAC [] THEN
   REPEAT GEN_TAC THEN MATCH_MP_TAC SEMIRING_SETS_COLLECT THEN CONJ_TAC THENL
   [RW_TAC std_ss [semiring_alt] THENL
    [SIMP_TAC std_ss [subset_class_def, SPACE_SIGMA, SUBSET_UNIV],
     RW_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER,
                    GSPECIFICATION, SUBSET_DEF] THEN
     FULL_SIMP_TAC std_ss [sigma_algebra_alt_pow],
     RW_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER,
                    GSPECIFICATION, SUBSET_DEF] THEN
     ONCE_REWRITE_TAC [METIS [subsets_def] ``P = subsets (univ(:real), P)``] THEN
     MATCH_MP_TAC ALGEBRA_INTER THEN
     ASM_SIMP_TAC std_ss [SIGMA_ALGEBRA_ALGEBRA] THEN
     FULL_SIMP_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER,
                           GSPECIFICATION, SUBSET_DEF],
     ALL_TAC] THEN Q.EXISTS_TAC `{s DIFF t}` THEN
    SIMP_TAC std_ss [BIGUNION_SING, FINITE_SING, disjoint_sing] THEN
    FULL_SIMP_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER,
                          GSPECIFICATION, SUBSET_DEF] THEN
    RW_TAC std_ss [IN_SING] THEN
    ONCE_REWRITE_TAC [METIS [subsets_def] ``P = subsets (univ(:real), P)``] THEN
    MATCH_MP_TAC ALGEBRA_DIFF THEN ASM_SIMP_TAC std_ss [SIGMA_ALGEBRA_ALGEBRA] THEN
    FULL_SIMP_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER,
                          GSPECIFICATION, SUBSET_DEF],
    ALL_TAC] THEN CONJ_TAC THENL
   [ALL_TAC, SIMP_TAC std_ss [SPACE_SIGMA, halfspace_gt_in_halfspace, IN_UNIV]] THEN
   SIMP_TAC std_ss [SPACE_SIGMA, IN_UNIV] THEN POP_ASSUM K_TAC THEN
   KNOW_TAC ``!a. {x | a < x} = UNIV DIFF {x:real | x <= a}`` THENL
   [RW_TAC std_ss [GSPECIFICATION, EXTENSION, IN_UNIV, IN_DIFF] THEN
    REAL_ARITH_TAC, DISC_RW_KILL] THEN MATCH_MP_TAC ALGEBRA_DIFF THEN
   RW_TAC std_ss [] THENL
   [RW_TAC std_ss [algebra_def, sigma_def, subsets_def, space_def] THENL
    [SIMP_TAC std_ss [subset_class_def, SUBSET_UNIV],
     SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION] THEN
     FULL_SIMP_TAC std_ss [sigma_algebra_alt_pow],
     FULL_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION] THEN
     RW_TAC std_ss [] THEN FULL_SIMP_TAC std_ss [sigma_algebra_alt_pow],
     FULL_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION] THEN RW_TAC std_ss [] THEN
     ONCE_REWRITE_TAC [METIS [subsets_def] ``P = subsets (univ(:real), P)``] THEN
     MATCH_MP_TAC ALGEBRA_UNION THEN
     FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA_ALGEBRA] THEN
     FULL_SIMP_TAC std_ss [subsets_def]],
    RW_TAC std_ss [algebra_def, sigma_def, subsets_def, space_def] THEN
    SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION] THEN RW_TAC std_ss [] THEN
    FULL_SIMP_TAC std_ss [sigma_algebra_alt_pow] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC ``{}:real->bool``) THEN ASM_REWRITE_TAC [] THEN
    SIMP_TAC std_ss [DIFF_EMPTY],
    ALL_TAC] THEN
   RW_TAC std_ss [] THEN
  KNOW_TAC ``!c. {x:real | x <= c} =
   BIGINTER (IMAGE (\n:num. {x | x < (c + (1/2) pow n)}) UNIV)`` THENL
  [RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_UNIV,IN_INTER] THEN EQ_TAC THENL
   [RW_TAC std_ss [GSPECIFICATION] THEN
     `0:real < (1/2) pow n` by RW_TAC real_ss [REAL_POW_LT] THEN
     `0:real < ((1 / 2) pow n)` by METIS_TAC [util_probTheory.POW_HALF_POS] THEN
     ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    RW_TAC std_ss [GSPECIFICATION] THEN
    `!n. x:real < (c + (1 / 2) pow n)` by METIS_TAC [] THEN
    `(\n. c + (1 / 2) pow n) = (\n. (\n. c) n + (\n. (1 / 2) pow n) n) `
     by RW_TAC real_ss [FUN_EQ_THM] THEN
    ASSUME_TAC (ISPEC ``c:real`` SEQ_CONST) THEN
    MP_TAC (ISPEC ``1 / (2:real)`` SEQ_POWER) THEN
    KNOW_TAC ``abs (1 / 2) < 1:real`` THENL
    [REWRITE_TAC [abs] THEN COND_CASES_TAC THEN
     SIMP_TAC std_ss [REAL_HALF_BETWEEN] THEN
     REWRITE_TAC [real_div, REAL_NEG_LMUL] THEN SIMP_TAC std_ss [GSYM real_div] THEN
     SIMP_TAC real_ss [REAL_LT_LDIV_EQ], DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
     POP_ASSUM K_TAC THEN DISCH_TAC] THEN
    MP_TAC (Q.SPECL [`(\n. c)`,`c`,`(\n. (1/2) pow n)`,`0`] SEQ_ADD) THEN
    ASM_REWRITE_TAC [] THEN BETA_TAC THEN SIMP_TAC std_ss [REAL_ADD_RID] THEN
    DISCH_TAC THEN METIS_TAC [REAL_LT_IMP_LE,
     Q.SPECL [`r`,`c`,`(\n. c + (1 / 2) pow n)`] LE_SEQ_IMP_LE_LIM], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [] THEN DISCH_TAC THEN
   KNOW_TAC ``sigma_algebra  (sigma univ(:real)
               (IMAGE (\(i',j). {x | x < i'}) univ(:real # num)))`` THENL
   [MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA THEN
    SIMP_TAC std_ss [subset_class_def, SUBSET_UNIV],
    DISCH_TAC] THEN
   (MP_TAC o UNDISCH o Q.SPEC `(sigma univ(:real) (IMAGE (\(i',j). {x | x < i'})
                                univ(:real # num)))`)
    (INST_TYPE [alpha |-> ``:real``] SIGMA_ALGEBRA_FN_BIGINTER)  THEN
   RW_TAC std_ss [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   RW_TAC std_ss [IN_FUNSET, IN_UNIV] THEN MATCH_MP_TAC IN_SIGMA THEN
   SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN
   Q.EXISTS_TAC `(i + (1 / 2) pow n, 1)` THEN
   SIMP_TAC std_ss [], ALL_TAC] THEN
  METIS_TAC [OPEN_HALFSPACE_COMPONENT_LT, borel_open]
QED
val borel_eq_halfspace_less = borel_eq_less;

Theorem borel_eq_le : (* was: borel_eq_halfspace_le *)
    borel = sigma UNIV (IMAGE (\a. {x | x <= a}) UNIV)
Proof
  ONCE_REWRITE_TAC [SET_RULE
   `` (IMAGE (\a. {x | x <= a}) univ(:real)) =
      (IMAGE (\(a:real,i:num). (\a i. {x | x <= a}) a i) UNIV)``] THEN
  KNOW_TAC `` (borel = sigma univ(:real)
  (IMAGE (\(i:real,j:num). (\a i. {x | x < a}) i j) UNIV)) /\
  (!i j. (i:real,j:num) IN UNIV ==>
     (\a i. {x | x < a}) i j IN
     subsets (sigma univ(:real)
          (IMAGE (\(i,j). (\a i. {x | x <= a}) i j)
             univ(:real # num)))) /\
  !i j. (i,j) IN univ(:real # num) ==>
    (\a i. {x | x <= a}) i j IN subsets borel`` THENL
  [ALL_TAC, DISCH_THEN (MP_TAC o MATCH_MP borel_eq_sigmaI2) THEN
   SIMP_TAC std_ss []] THEN
  ONCE_REWRITE_TAC [SET_RULE
   ``(IMAGE (\(i:real,j:num). (\a i. {x | x < a}) i j) UNIV) =
     (IMAGE (\a. {x | x < a}) univ(:real))``] THEN
  SIMP_TAC std_ss [borel_eq_less, IN_UNIV] THEN
  KNOW_TAC ``!a:real. {x | x < a} =
    BIGUNION {{x | x <= a - 1 / &(SUC n)} | n IN UNIV}`` THENL
  [RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION, IN_UNIV] THEN
   ASM_CASES_TAC ``x < a:real`` THENL
   [ASM_REWRITE_TAC [] THEN MP_TAC (ISPEC ``a - x:real`` REAL_ARCH_INV_SUC) THEN
    ASM_REWRITE_TAC [REAL_SUB_LT] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC (ONCE_REWRITE_RULE [REAL_ARITH
     ``a < b - c <=> c < b - a:real``]) THEN
    Q.EXISTS_TAC `{x:real | x <= a - inv (&SUC n)}` THEN
    ASM_SIMP_TAC std_ss [GSPECIFICATION] THEN
    GEN_REWR_TAC LAND_CONV [REAL_LE_LT] THEN ASM_SIMP_TAC real_ss [real_div] THEN
    METIS_TAC [], ALL_TAC] THEN
   ASM_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THEN
   ASM_CASES_TAC ``(x:real) NOTIN s`` THEN
   ASM_SIMP_TAC std_ss [] THEN GEN_TAC THEN FULL_SIMP_TAC std_ss [REAL_NOT_LT] THEN
   EXISTS_TAC ``x:real`` THEN ASM_SIMP_TAC std_ss [REAL_NOT_LE] THEN
   KNOW_TAC ``0:real < 1 / &SUC n`` THENL [ALL_TAC, ASM_REAL_ARITH_TAC] THEN
   SIMP_TAC real_ss [REAL_LT_RDIV_EQ], DISCH_TAC] THEN
  ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
  [RW_TAC std_ss [subsets_def, sigma_def, IN_BIGINTER,
                  GSPECIFICATION, SUBSET_DEF] THEN
   FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, subsets_def] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
    MATCH_MP_TAC image_countable THEN
    SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM], ALL_TAC] THEN
   RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   SET_TAC [], ALL_TAC] THEN
  RULE_ASSUM_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN ASM_REWRITE_TAC [] THEN
  SIMP_TAC std_ss [GSYM borel_eq_less] THEN GEN_TAC THEN
  MATCH_MP_TAC borel_closed THEN SIMP_TAC std_ss [CLOSED_HALFSPACE_COMPONENT_LE]
QED
val borel_eq_halfspace_le = borel_eq_le;

Theorem borel_eq_gr : (* borel_eq_greaterThan *)
    borel = sigma UNIV (IMAGE (\a. {x | a < x}) UNIV)
Proof
  KNOW_TAC ``(borel = sigma univ(:real)
                           (IMAGE (\(i,j). (\a i. {x | x <= a}) i j) univ(:real#num))) /\
  (!i j.
     (i:real,j:num) IN UNIV ==>
     (\a i. {x | x <= a}) i j IN
     subsets
       (sigma univ(:real) (IMAGE (\a. {x | a < x}) univ(:real)))) /\
  !i. (\a. {x | a < x}) i IN subsets borel`` THENL
  [ALL_TAC, DISCH_THEN (MP_TAC o MATCH_MP borel_eq_sigmaI4) THEN
   SIMP_TAC std_ss []] THEN SIMP_TAC std_ss [borel_eq_le] THEN
  ONCE_REWRITE_TAC [SET_RULE
   `` (IMAGE (\a. {x | x <= a}) univ(:real)) =
      (IMAGE (\(a:real,i:num). (\a i. {x | x <= a}) a i) UNIV)``] THEN
  SIMP_TAC std_ss [IN_UNIV] THEN CONJ_TAC THENL
  [ALL_TAC,
   ONCE_REWRITE_TAC [SET_RULE ``(IMAGE (\(a:real,i:num). {x | x <= a}) UNIV) =
                                (IMAGE (\a. {x | x <= a}) univ(:real))``] THEN
   SIMP_TAC std_ss [GSYM borel_eq_le] THEN GEN_TAC THEN
   MATCH_MP_TAC borel_open THEN SIMP_TAC std_ss [OPEN_INTERVAL_RIGHT]] THEN
  KNOW_TAC ``!a:real. {x | x <= a} = UNIV DIFF {x | a < x}`` THENL
  [RW_TAC std_ss [EXTENSION, IN_DIFF, GSPECIFICATION, IN_UNIV] THEN
   REAL_ARITH_TAC, DISCH_TAC] THEN
  RW_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER, GSPECIFICATION,
                 IN_UNIV, SUBSET_DEF] THEN
  ONCE_REWRITE_TAC [METIS [subsets_def] ``P = subsets (univ(:real), P)``] THEN
  MATCH_MP_TAC ALGEBRA_DIFF THEN ASM_SIMP_TAC std_ss [SIGMA_ALGEBRA_ALGEBRA] THEN
  CONJ_TAC THENL
  [FULL_SIMP_TAC std_ss [sigma_algebra_alt_pow, subsets_def] THEN
   ONCE_REWRITE_TAC [SET_RULE ``UNIV = UNIV DIFF {}``] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
   ALL_TAC] THEN
  SIMP_TAC std_ss [subsets_def] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN METIS_TAC []
QED
val borel_eq_greaterThan = borel_eq_gr;

Theorem borel_eq_ge_le : (* borel_eq_atLeastAtMost *)
    borel = sigma UNIV (IMAGE (\(a,b). {x | a <= x /\ x <= b}) UNIV)
Proof
  ONCE_REWRITE_TAC [METIS [] ``{x | a <= x /\ x <= b} =
                   (\a b. {x:real | a <= x /\ x <= b}) a b``] THEN
  KNOW_TAC ``(borel = sigma univ(:real) (IMAGE (\a. {x | x <= a}) univ(:real))) /\
  (!i.
     (\a. {x | x <= a}) i IN
     subsets
       (sigma univ(:real)
          (IMAGE (\(i,j). (\a b. {x | a <= x /\ x <= b}) i j)
             univ(:real # real)))) /\
  !i j. (\a b. {x | a <= x /\ x <= b}) i j IN subsets borel`` THENL
  [ALL_TAC,
   DISCH_THEN (MP_TAC o MATCH_MP borel_eq_sigmaI5) THEN SIMP_TAC std_ss []] THEN
  SIMP_TAC std_ss [borel_eq_le] THEN
  KNOW_TAC ``!a. {x | x <= a} =
       BIGUNION {{x:real | -&n <= x /\ x <= a} | n IN UNIV}`` THENL
  [RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION, IN_UNIV] THEN
   EQ_TAC THENL
   [ALL_TAC, STRIP_TAC THEN POP_ASSUM (MP_TAC o SPEC ``x:real``) THEN
    ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC] THEN
   DISCH_TAC THEN MP_TAC (ISPEC ``-x:real`` SIMP_REAL_ARCH) THEN STRIP_TAC THEN
   POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM REAL_LE_NEG]) THEN
   RW_TAC std_ss [REAL_NEG_NEG] THEN Q.EXISTS_TAC `{x | -&n <= x /\ x <= a}` THEN
   ASM_SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [], DISCH_TAC] THEN
  CONJ_TAC THENL
  [ALL_TAC, SIMP_TAC std_ss [GSYM borel_eq_le] THEN
   REPEAT GEN_TAC THEN MATCH_MP_TAC borel_closed THEN
   SIMP_TAC std_ss [GSYM interval, CLOSED_INTERVAL]] THEN
  RW_TAC std_ss [subsets_def, sigma_def, IN_BIGINTER,
                 GSPECIFICATION, SUBSET_DEF] THEN
  ONCE_REWRITE_TAC [METIS [] ``{x | -&n <= x /\ x <= i} =
                     (\n. {x:real | -&n <= x /\ x <= i}) n``] THEN
  MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UN THEN EXISTS_TAC ``univ(:real)`` THEN
  ASM_SIMP_TAC std_ss [COUNTABLE_NUM] THEN
  RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SET_TAC []
QED
val borel_eq_atLeastAtMost = borel_eq_ge_le;

(* this is the original definition *)
val borel_def = save_thm ("borel_def", borel_eq_le);

val in_borel_measurable = store_thm
  ("in_borel_measurable",
   ``!f s. f IN borel_measurable s <=>
           sigma_algebra s /\
           (!s'. s' IN subsets (sigma UNIV (IMAGE (\a. {x | x <= a}) UNIV)) ==>
                 PREIMAGE f s' INTER space s IN subsets s)``,
   RW_TAC std_ss [IN_MEASURABLE, borel_def,
                  SPACE_SIGMA, IN_FUNSET, IN_UNIV]
   >> `sigma_algebra (sigma UNIV (IMAGE (\a. {x | x <= a}) UNIV))`
        by (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA
            >> RW_TAC std_ss [subset_class_def, SUBSET_DEF, IN_UNIV])
   >> ASM_REWRITE_TAC []);

val borel_measurable_indicator = store_thm
  ("borel_measurable_indicator",
   ``!s a. sigma_algebra s /\ a IN subsets s ==>
           indicator_fn a IN borel_measurable s``,
   RW_TAC std_ss [indicator_fn_def, in_borel_measurable]
   >> Cases_on `1 IN s'`
   >- (Cases_on `0 IN s'`
       >- (`PREIMAGE (\x. (if x IN a then 1 else 0)) s' INTER space s = space s`
                by (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_PREIMAGE]
                    >> METIS_TAC [])
           >> POP_ORW
           >> MATCH_MP_TAC ALGEBRA_SPACE >> MATCH_MP_TAC SIGMA_ALGEBRA_ALGEBRA
           >> ASM_REWRITE_TAC [])
       >> `PREIMAGE (\x. (if x IN a then 1 else 0)) s' INTER space s = a`
                by (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_PREIMAGE]
                    >> METIS_TAC [SIGMA_ALGEBRA, algebra_def, subset_class_def, SUBSET_DEF])
       >> ASM_REWRITE_TAC [])
   >> Cases_on `0 IN s'`
   >- (`PREIMAGE (\x. (if x IN a then 1 else 0)) s' INTER space s = space s DIFF a`
                by (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_PREIMAGE, IN_DIFF]
                    >> METIS_TAC [SIGMA_ALGEBRA, algebra_def, subset_class_def, SUBSET_DEF])
        >> METIS_TAC [SIGMA_ALGEBRA, algebra_def])
   >> `PREIMAGE (\x. (if x IN a then 1 else 0)) s' INTER space s = {}`
        by (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_PREIMAGE, NOT_IN_EMPTY] >> METIS_TAC [])
   >> POP_ORW >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, algebra_def]);

(* cf. IN_MEASURABLE_BOREL_RC in borelTheory *)
Theorem in_borel_measurable_le :
    !f m. f IN borel_measurable m <=>
          sigma_algebra m /\ f IN (space m -> UNIV) /\
          !a. {w | w IN space m /\ f w <= a} IN subsets m
Proof
   rpt STRIP_TAC >> EQ_TAC
   >- (RW_TAC std_ss [in_borel_measurable, subsets_def, space_def,
                      IN_FUNSET, IN_UNIV]
       >> POP_ASSUM (MP_TAC o REWRITE_RULE [PREIMAGE_def] o Q.SPEC `{b | b <= a}`)
       >> RW_TAC std_ss [GSPECIFICATION]
       >> `{x | f x <= a} INTER space m =
           {w | w IN space m /\ f w <= a}`
                by (RW_TAC std_ss [Once EXTENSION, IN_INTER, GSPECIFICATION]
                    >> DECIDE_TAC)
       >> FULL_SIMP_TAC std_ss [] >> POP_ASSUM (K ALL_TAC) >> POP_ASSUM MATCH_MP_TAC
       >> MATCH_MP_TAC IN_SIGMA
       >> RW_TAC std_ss [IN_IMAGE, IN_UNIV, Once EXTENSION, GSPECIFICATION]
       >> Q.EXISTS_TAC `a` >> SIMP_TAC std_ss [])
   >> RW_TAC std_ss [borel_def]
   >> MATCH_MP_TAC MEASURABLE_SIGMA
   >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, subset_class_def, space_def, subsets_def, SUBSET_UNIV,
                     IN_IMAGE]
   >> `PREIMAGE f {x | x <= a} INTER space m =
       {w | w IN space m /\ f w <= a}`
        by (RW_TAC std_ss [Once EXTENSION, IN_INTER, GSPECIFICATION, IN_PREIMAGE]
            >> DECIDE_TAC)
   >> RW_TAC std_ss []
QED

(* cf. IN_MEASURABLE_BOREL_IMP in borelTheory *)
val sigma_le_less = store_thm
  ("sigma_le_less",
  ``!f A. sigma_algebra A /\ (!(a:real). {w | w IN space A /\ f w <= a} IN subsets A) ==>
          !a. {w | w IN space A /\ f w < a} IN subsets A``,
   rpt STRIP_TAC
   >> `BIGUNION (IMAGE (\n. {w | w IN space A /\ f w <= a - inv(&(SUC n))}) (UNIV:num->bool)) =
       {w | w IN space A /\ f w < a}`
        by (ONCE_REWRITE_TAC [EXTENSION]
            >> RW_TAC std_ss [GSPECIFICATION, IN_BIGUNION, IN_IMAGE, IN_UNIV]
            >> `(?s. x IN s /\ ?n. s = {w | w IN space A /\ f w <= a - inv (&SUC n)}) =
                (?n. x IN {w | w IN space A /\ f w <= a - inv (& (SUC n))})`
                by METIS_TAC [GSYM EXTENSION]
            >> POP_ORW
            >> RW_TAC std_ss [GSPECIFICATION]
            >> EQ_TAC
            >- (RW_TAC std_ss [] >- METIS_TAC [] >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `a - inv (& (SUC n))`
                >> RW_TAC real_ss [REAL_LT_SUB_RADD, REAL_LT_ADDR, REAL_LT_INV_EQ] >> METIS_TAC [])
            >> RW_TAC std_ss []
            >> `(\n. inv (($& o SUC) n)) --> 0`
                by (MATCH_MP_TAC SEQ_INV0
                    >> RW_TAC std_ss [o_DEF]
                    >> Q.EXISTS_TAC `clg y`
                    >> RW_TAC std_ss [GREATER_EQ, real_gt]
                    >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `&(clg y)`
                    >> RW_TAC std_ss [REAL_LT, LE_NUM_CEILING]
                    >> MATCH_MP_TAC LESS_EQ_LESS_TRANS >> Q.EXISTS_TAC `n`
                    >> RW_TAC arith_ss [])
            >> FULL_SIMP_TAC real_ss [SEQ, o_DEF]
            >> POP_ASSUM (MP_TAC o REWRITE_RULE [REAL_LT_SUB_LADD] o Q.SPEC `a - f x`)
            >> RW_TAC real_ss [ABS_INV, ABS_N, REAL_LE_SUB_LADD]
            >> Q.EXISTS_TAC `N` >> MATCH_MP_TAC REAL_LT_IMP_LE
            >> ONCE_REWRITE_TAC [REAL_ADD_COMM] >> POP_ASSUM MATCH_MP_TAC >> RW_TAC std_ss [])
   >> POP_ASSUM (MP_TAC o GSYM) >> RW_TAC std_ss []
   >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA]
   >> Q.PAT_ASSUM `!c. P c ==> BIGUNION c IN subsets A` MATCH_MP_TAC
   >> RW_TAC std_ss [COUNTABLE_NUM, image_countable, SUBSET_DEF, IN_IMAGE, IN_UNIV]
   >> METIS_TAC []);

val sigma_less_ge = store_thm
  ("sigma_less_ge",
  ``!f A. sigma_algebra A /\ (!(a:real). {w | w IN space A /\ f w < a} IN subsets A) ==>
          !a. {w | w IN space A /\ a <= f w} IN subsets A``,
   rpt STRIP_TAC
   >> `{w | w IN space A /\ a <= f w} =
       space A DIFF {w | w IN space A /\ f w < a}`
        by (RW_TAC std_ss [Once EXTENSION, IN_DIFF, GSPECIFICATION, real_lt]
            >> DECIDE_TAC)
   >> POP_ORW
   >> METIS_TAC [SIGMA_ALGEBRA]);

val sigma_ge_gr = store_thm
  ("sigma_ge_gr",
  ``!f A. sigma_algebra A /\ (!(a:real). {w | w IN space A /\ a <= f w} IN subsets A) ==>
          !a. {w | w IN space A /\ a < f w} IN subsets A``,
   rpt STRIP_TAC
   >> `BIGUNION (IMAGE (\n. {w | w IN space A /\ a <= f w - inv(&(SUC n))}) (UNIV:num->bool)) =
       {w | w IN space A /\ a < f w}`
        by (ONCE_REWRITE_TAC [EXTENSION]
            >> RW_TAC std_ss [GSPECIFICATION, IN_BIGUNION, IN_IMAGE, IN_UNIV]
            >> `(?s. x IN s /\ ?n. s = {w | w IN space A /\ a <= f w - inv (& (SUC n))}) =
                (?n. x IN {w | w IN space A /\ a <= f w - inv (& (SUC n))})`
                by METIS_TAC []
            >> POP_ORW
            >> RW_TAC std_ss [GSPECIFICATION]
            >> EQ_TAC
            >- (RW_TAC std_ss [] >- ASM_REWRITE_TAC [] >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `f x - inv (& (SUC n))`
                >> RW_TAC real_ss [REAL_LT_SUB_RADD, REAL_LT_ADDR, REAL_LT_INV_EQ])
            >> RW_TAC std_ss []
            >> `(\n. inv (($& o SUC) n)) --> 0`
                by (MATCH_MP_TAC SEQ_INV0
                    >> RW_TAC std_ss [o_DEF]
                    >> Q.EXISTS_TAC `clg y`
                    >> RW_TAC std_ss [GREATER_EQ, real_gt]
                    >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `&(clg y)`
                    >> RW_TAC std_ss [REAL_LT, LE_NUM_CEILING]
                    >> MATCH_MP_TAC LESS_EQ_LESS_TRANS >> Q.EXISTS_TAC `n`
                    >> RW_TAC arith_ss [])
            >> FULL_SIMP_TAC real_ss [SEQ, o_DEF]
            >> POP_ASSUM (MP_TAC o REWRITE_RULE [REAL_LT_SUB_LADD] o Q.SPEC `f x - a`)
            >> RW_TAC real_ss [ABS_INV, ABS_N, REAL_LE_SUB_LADD]
            >> Q.EXISTS_TAC `N` >> MATCH_MP_TAC REAL_LT_IMP_LE
            >> ONCE_REWRITE_TAC [REAL_ADD_COMM] >> POP_ASSUM MATCH_MP_TAC >> RW_TAC std_ss [])
   >> POP_ASSUM (MP_TAC o GSYM) >> RW_TAC std_ss []
   >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA]
   >> Q.PAT_X_ASSUM `!c. P c ==> BIGUNION c IN subsets A` MATCH_MP_TAC
   >> RW_TAC std_ss [COUNTABLE_NUM, image_countable, SUBSET_DEF, IN_IMAGE, IN_UNIV, REAL_LE_SUB_LADD]
   >> METIS_TAC []);

val sigma_gr_le = store_thm
  ("sigma_gr_le",
  ``!f A. sigma_algebra A /\ (!(a:real). {w | w IN space A /\ a < f w} IN subsets A) ==>
          !a. {w | w IN space A /\ f w <= a} IN subsets A``,
   rpt STRIP_TAC
   >> `{w | w IN space A /\ f w <= a} =
       space A DIFF {w | w IN space A /\ a < f w}`
        by (RW_TAC std_ss [Once EXTENSION, IN_DIFF, GSPECIFICATION, real_lt]
            >> DECIDE_TAC)
   >> POP_ORW
   >> METIS_TAC [SIGMA_ALGEBRA]);

Theorem in_borel_measurable_gr :
    !f m. f IN borel_measurable m <=>
          sigma_algebra m /\ f IN (space m -> UNIV) /\
          !a. {w | w IN space m /\ a < f w} IN subsets m
Proof
   RW_TAC std_ss [in_borel_measurable_le]
   >> EQ_TAC
   >- (RW_TAC std_ss [IN_FUNSET, IN_UNIV]
       >> `{w | w IN space m /\ a < f w} =
                space m DIFF {w | w IN space m /\ f w <= a}`
        by (ONCE_REWRITE_TAC [EXTENSION]
            >> RW_TAC std_ss [IN_DIFF, GSPECIFICATION, real_lt]
            >> DECIDE_TAC)
       >> POP_ORW
       >> METIS_TAC [SIGMA_ALGEBRA, space_def, subsets_def])
   >> METIS_TAC [sigma_gr_le, SPACE, subsets_def, space_def]
QED

Theorem in_borel_measurable_less :
    !f m. f IN borel_measurable m <=>
          sigma_algebra m /\ f IN (space m -> UNIV) /\
          !a. {w | w IN space m /\ f w < a} IN subsets m
Proof
   RW_TAC std_ss [in_borel_measurable_le, IN_FUNSET, IN_UNIV]
   >> EQ_TAC
   >- (RW_TAC std_ss [] \\
       METIS_TAC [sigma_le_less, SPACE, subsets_def, space_def])
   >> RW_TAC std_ss []
   >> `BIGUNION (IMAGE (\n. {w | w IN space m /\ a <= f w - inv(&(SUC n))}) (UNIV:num->bool)) =
       {w | w IN space m /\ a < f w}`
        by (ONCE_REWRITE_TAC [EXTENSION]
            >> RW_TAC std_ss [GSPECIFICATION, IN_BIGUNION, IN_IMAGE, IN_UNIV]
            >> `(?s. x IN s /\ ?n. s = {w | w IN space m /\ a <= f w - inv (& (SUC n))}) =
                (?n. x IN {w | w IN space m /\ a <= f w - inv (& (SUC n))})`
                by METIS_TAC []
            >> POP_ORW
            >> RW_TAC std_ss [GSPECIFICATION]
            >> EQ_TAC
            >- (RW_TAC std_ss [] >- ASM_REWRITE_TAC [] >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `f x - inv (& (SUC n))`
                >> RW_TAC real_ss [REAL_LT_SUB_RADD, REAL_LT_ADDR, REAL_LT_INV_EQ])
            >> RW_TAC std_ss []
            >> `(\n. inv (($& o SUC) n)) --> 0`
                by (MATCH_MP_TAC SEQ_INV0
                    >> RW_TAC std_ss [o_DEF]
                    >> Q.EXISTS_TAC `clg y`
                    >> RW_TAC std_ss [GREATER_EQ, real_gt]
                    >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `&(clg y)`
                    >> RW_TAC std_ss [REAL_LT, LE_NUM_CEILING]
                    >> MATCH_MP_TAC LESS_EQ_LESS_TRANS >> Q.EXISTS_TAC `n`
                    >> RW_TAC arith_ss [])
            >> FULL_SIMP_TAC real_ss [SEQ, o_DEF]
            >> POP_ASSUM (MP_TAC o REWRITE_RULE [REAL_LT_SUB_LADD] o Q.SPEC `f x - a`)
            >> RW_TAC real_ss [ABS_INV, ABS_N, REAL_LE_SUB_LADD]
            >> Q.EXISTS_TAC `N` >> MATCH_MP_TAC REAL_LT_IMP_LE
            >> ONCE_REWRITE_TAC [REAL_ADD_COMM] >> POP_ASSUM MATCH_MP_TAC >> RW_TAC std_ss [])
   >> `{w | w IN space m /\ f w <= a} =
                space m DIFF {w | w IN space m /\ a < f w}`
        by (RW_TAC std_ss [Once EXTENSION, IN_DIFF, GSPECIFICATION, real_lt]
            >> DECIDE_TAC)
   >> POP_ORW
   >> Suff `{w | w IN space m /\ a < f w} IN subsets m`
   >- METIS_TAC [SPACE, subsets_def, space_def, SIGMA_ALGEBRA]
   >> POP_ASSUM (MP_TAC o GSYM) >> RW_TAC std_ss []
   >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, subsets_def]
   >> Q.PAT_X_ASSUM `!c. P c ==> BIGUNION c IN subsets m` MATCH_MP_TAC
   >> RW_TAC std_ss [COUNTABLE_NUM, image_countable, SUBSET_DEF, IN_IMAGE, IN_UNIV, REAL_LE_SUB_LADD]
   >> `{w | w IN space m /\ a + inv (& (SUC n)) <= f w} =
        space m DIFF {w | w IN space m /\ f w < a + inv (& (SUC n))}`
        by (RW_TAC std_ss [Once EXTENSION, IN_DIFF, GSPECIFICATION, real_lt]
            >> DECIDE_TAC)
   >> POP_ORW
   >> Suff `{w | w IN space m /\ f w < a + inv (& (SUC n))} IN subsets m`
   >- METIS_TAC [SPACE, subsets_def, space_def, SIGMA_ALGEBRA]
   >> METIS_TAC []
QED

Theorem in_borel_measurable_ge :
    !f m. f IN borel_measurable m <=>
          sigma_algebra m /\ f IN (space m -> UNIV) /\
          !a. {w | w IN space m /\ a <= f w} IN subsets m
Proof
   RW_TAC std_ss [in_borel_measurable_less, IN_FUNSET, IN_UNIV]
   >> EQ_TAC
   >- (RW_TAC std_ss []
       >> `{w | w IN space m /\ a <= f w} =
                space m DIFF {w | w IN space m /\ f w < a}`
        by (RW_TAC std_ss [Once EXTENSION, IN_DIFF, GSPECIFICATION, real_lt]
            >> DECIDE_TAC)
       >> POP_ORW
       >> METIS_TAC [SIGMA_ALGEBRA, space_def, subsets_def])
   >> METIS_TAC [sigma_ge_gr, sigma_gr_le, sigma_le_less, SPACE, subsets_def, space_def]
QED

Theorem borel_measurable_sets_le :
    !a. {x | x <= a} IN subsets borel
Proof
    ASSUME_TAC
      (REWRITE_RULE [space_borel, sigma_algebra_borel, IN_FUNSET, IN_UNIV, I_THM]
                    (Q.SPECL [`I`, `borel`]
                             (INST_TYPE [``:'a`` |-> ``:real``] in_borel_measurable_le)))
 >> POP_ASSUM (REWRITE_TAC o wrap o SYM)
 >> MATCH_MP_TAC MEASURABLE_I
 >> ACCEPT_TAC sigma_algebra_borel
QED

Theorem borel_measurable_sets_less :
    !a. {x | x < a} IN subsets borel
Proof
    MATCH_MP_TAC
      (REWRITE_RULE [space_borel, sigma_algebra_borel, IN_UNIV, I_THM]
                    (Q.SPECL [`I`, `borel`]
                             (INST_TYPE [``:'a`` |-> ``:real``] sigma_le_less)))
 >> REWRITE_TAC [borel_measurable_sets_le]
QED

Theorem borel_measurable_sets_ge :
    !a. {x | a <= x} IN subsets borel
Proof
    MATCH_MP_TAC
      (REWRITE_RULE [space_borel, sigma_algebra_borel, IN_UNIV, I_THM]
                    (Q.SPECL [`I`, `borel`]
                             (INST_TYPE [``:'a`` |-> ``:real``] sigma_less_ge)))
 >> REWRITE_TAC [borel_measurable_sets_less]
QED

Theorem borel_measurable_sets_gr :
    !a. {x | a < x} IN subsets borel
Proof
    MATCH_MP_TAC
      (REWRITE_RULE [space_borel, sigma_algebra_borel, IN_UNIV, I_THM]
                    (Q.SPECL [`I`, `borel`]
                             (INST_TYPE [``:'a`` |-> ``:real``] sigma_ge_gr)))
 >> REWRITE_TAC [borel_measurable_sets_ge]
QED

Theorem borel_measurable_sets_gr_less :
    !a b. {x | a < x /\ x < b} IN subsets borel
Proof
    rpt GEN_TAC
 >> `{x | a < x /\ x < b} = {x | a < x} INTER {x | x < b}`
        by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> POP_ORW
 >> MATCH_MP_TAC ALGEBRA_INTER
 >> rw [borel_measurable_sets_gr, borel_measurable_sets_less]
 >> METIS_TAC [SIGMA_ALGEBRA_ALGEBRA, sigma_algebra_borel]
QED

Theorem borel_measurable_sets_gr_le :
    !a b. {x | a < x /\ x <= b} IN subsets borel
Proof
    rpt GEN_TAC
 >> `{x | a < x /\ x <= b} = {x | a < x} INTER {x | x <= b}`
        by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> POP_ORW
 >> MATCH_MP_TAC ALGEBRA_INTER
 >> rw [borel_measurable_sets_gr, borel_measurable_sets_le]
 >> METIS_TAC [SIGMA_ALGEBRA_ALGEBRA, sigma_algebra_borel]
QED

Theorem borel_measurable_sets_ge_less :
    !a b. {x | a <= x /\ x < b} IN subsets borel
Proof
    rpt GEN_TAC
 >> `{x | a <= x /\ x < b} = {x | a <= x} INTER {x | x < b}`
        by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> POP_ORW
 >> MATCH_MP_TAC ALGEBRA_INTER
 >> rw [borel_measurable_sets_ge, borel_measurable_sets_less]
 >> METIS_TAC [SIGMA_ALGEBRA_ALGEBRA, sigma_algebra_borel]
QED

Theorem borel_measurable_sets_ge_le :
    !a b. {x | a <= x /\ x <= b} IN subsets borel
Proof
    rpt GEN_TAC
 >> `{x | a <= x /\ x <= b} = {x | a <= x} INTER {x | x <= b}`
        by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> POP_ORW
 >> MATCH_MP_TAC ALGEBRA_INTER
 >> rw [borel_measurable_sets_ge, borel_measurable_sets_le]
 >> METIS_TAC [SIGMA_ALGEBRA_ALGEBRA, sigma_algebra_borel]
QED

(* also used in borelTheory.lambda_point_eq_zero *)
Theorem REAL_SING_BIGINTER :
    !(c :real). {c} = BIGINTER (IMAGE (\n. {x | c - ((1/2) pow n) <= x /\
                                                x < c + ((1/2) pow n)}) UNIV)
Proof
    RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_UNIV, IN_SING, IN_INTER]
 >> EQ_TAC >- RW_TAC set_ss [REAL_POW_LT, REAL_LT_IMP_LE, REAL_LT_ADDR, REAL_LT_DIV,
                             HALF_POS, REAL_LT_ADDNEG2, real_sub, IN_INTER]
 >> RW_TAC std_ss [GSPECIFICATION]
 >> `!n. c - (1/2) pow n <= x` by FULL_SIMP_TAC real_ss [real_sub]
 >> `!n. x <= c + (1/2) pow n` by FULL_SIMP_TAC real_ss [REAL_LT_IMP_LE]
 >> `(\n. c - (1/2) pow n) = (\n. (\n. c) n - (\n. (1/2) pow n) n)`
       by RW_TAC real_ss [FUN_EQ_THM]
 >> `(\n. c + (1/2) pow n) = (\n. (\n. c) n + (\n. (1/2) pow n) n)`
       by RW_TAC real_ss [FUN_EQ_THM]
 >> `(\n. c) --> c` by RW_TAC std_ss [SEQ_CONST]
 >> `(\n. (1/2) pow n) --> 0` by RW_TAC real_ss [SEQ_POWER]
 >> `(\n. c - (1/2) pow n) --> c`
      by METIS_TAC [Q.SPECL [`(\n. c)`, `c`, `(\n. (1/2) pow n)`, `0`] SEQ_SUB, REAL_SUB_RZERO]
 >> `(\n. c + (1/2) pow n) --> c`
      by METIS_TAC [Q.SPECL [`(\n. c)`, `c`, `(\n. (1/2) pow n)`, `0`] SEQ_ADD, REAL_ADD_RID]
 >> `c <= x` by METIS_TAC [Q.SPECL [`x`, `c`, `(\n. c - (1/2) pow n)`] SEQ_LE_IMP_LIM_LE]
 >> `x <= c` by METIS_TAC [Q.SPECL [`x`, `c`, `(\n. c + (1/2) pow n)`] LE_SEQ_IMP_LE_LIM]
 >> METIS_TAC [REAL_LE_ANTISYM]
QED

Theorem borel_measurable_sets_sing :
    !c. {c} IN subsets borel
Proof
    GEN_TAC >> REWRITE_TAC [REAL_SING_BIGINTER]
 >> ASSUME_TAC sigma_algebra_borel
 >> (MP_TAC o UNDISCH o Q.SPEC `borel` o (INST_TYPE [alpha |-> ``:real``]))
      SIGMA_ALGEBRA_FN_BIGINTER
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM `!f. P f ==> Q f`
     (MP_TAC o
      Q.SPEC `(\n. {x | c - ((1/2) pow n) <= x /\ x < c + ((1/2) pow n)})`)
 >> `(\n. {x | c - ((1/2) pow n) <= x /\ x < c + ((1/2) pow n)}) IN (UNIV -> subsets borel)`
     by RW_TAC std_ss [IN_FUNSET, borel_measurable_sets_ge_less]
 >> METIS_TAC []
QED

Theorem borel_measurable_sets_not_sing :
    !c. {x | x <> c} IN subsets borel
Proof
    RW_TAC std_ss []
 >> `{x | x <> c} = (space borel) DIFF ({c})`
      by RW_TAC std_ss [space_borel, EXTENSION, IN_DIFF, IN_SING, GSPECIFICATION, IN_UNIV]
 >> POP_ORW
 >> METIS_TAC [sigma_algebra_borel, borel_measurable_sets_sing,
               sigma_algebra_def, algebra_def]
QED

(* A summary of all borel-measurable sets *)
Theorem borel_measurable_sets :
   (!a. {x | x < a} IN subsets borel) /\
   (!a. {x | x <= a} IN subsets borel) /\
   (!a. {x | a < x} IN subsets borel) /\
   (!a. {x | a <= x} IN subsets borel) /\
   (!a b. {x | a < x /\ x < b} IN subsets borel) /\
   (!a b. {x | a < x /\ x <= b} IN subsets borel) /\
   (!a b. {x | a <= x /\ x < b} IN subsets borel) /\
   (!a b. {x | a <= x /\ x <= b} IN subsets borel) /\
   (!c. {c} IN subsets borel) /\
   (!c. {x | x <> c} IN subsets borel)
Proof
   RW_TAC std_ss [borel_measurable_sets_less,
                  borel_measurable_sets_le,
                  borel_measurable_sets_gr,
                  borel_measurable_sets_ge,
                  borel_measurable_sets_gr_less,
                  borel_measurable_sets_gr_le,
                  borel_measurable_sets_ge_less,
                  borel_measurable_sets_ge_le,
                  borel_measurable_sets_sing,
                  borel_measurable_sets_not_sing]
QED

(************************************************************)
(*  right-open (left-closed) intervals [a, b) in R          *)
(************************************************************)

(* cf. `open_interval` (extrealTheory), `box` (real_borelTheory),
       `OPEN_interval` and `CLOSE_interval` (real_topologyTheory)

   The name "right_open_interval" is from MML (Mizar Math Library)
 *)
Definition right_open_interval :
    right_open_interval a b = {(x :real) | a <= x /\ x < b}
End

Theorem in_right_open_interval :
    !a b x. x IN right_open_interval a b <=> a <= x /\ x < b
Proof
    SIMP_TAC std_ss [right_open_interval, GSPECIFICATION]
QED

Theorem right_open_interval_interior :
    !a b. a < b ==> a IN (right_open_interval a b)
Proof
    RW_TAC std_ss [right_open_interval, GSPECIFICATION, REAL_LE_REFL]
QED

(* cf. `open_intervals_set` in extrealTheory *)
Definition right_open_intervals :
   right_open_intervals = (univ(:real), {right_open_interval a b | T})
End

Theorem in_right_open_intervals :
    !s. s IN subsets right_open_intervals <=> ?a b. (s = right_open_interval a b)
Proof
    RW_TAC std_ss [subsets_def, right_open_intervals,
                   right_open_interval, GSPECIFICATION]
 >> EQ_TAC >> rpt STRIP_TAC
 >- (Cases_on `x` >> fs [] >> qexistsl_tac [`q`, `r`] >> rw [])
 >> Q.EXISTS_TAC `(a,b)` >> rw []
QED

Theorem right_open_interval_in_intervals :
    !a b. (right_open_interval a b) IN subsets right_open_intervals
Proof
    RW_TAC std_ss [in_right_open_intervals]
 >> qexistsl_tac [`a`, `b`] >> REWRITE_TAC []
QED

Theorem right_open_interval_empty :
    !a b. (right_open_interval a b = {}) <=> ~(a < b)
Proof
    RW_TAC real_ss [right_open_interval, EXTENSION, GSPECIFICATION,
                    NOT_IN_EMPTY, GSYM real_lte]
 >> EQ_TAC >> rpt STRIP_TAC
 >- POP_ASSUM (ACCEPT_TAC o (REWRITE_RULE [REAL_LE_REFL]) o (Q.SPEC `a`))
 >> STRONG_DISJ_TAC
 >> PROVE_TAC [REAL_LE_TRANS]
QED

Theorem in_right_open_intervals_nonempty :
    !s. s <> {} /\ s IN subsets right_open_intervals <=>
        ?a b. a < b /\ (s = right_open_interval a b)
Proof
    RW_TAC std_ss [subsets_def, right_open_intervals, GSPECIFICATION]
 >> EQ_TAC >> rpt STRIP_TAC (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      Cases_on `x` >> fs [right_open_interval_empty] \\
      qexistsl_tac [`q`, `r`] >> art [],
      (* goal 2 (of 3) *)
      METIS_TAC [right_open_interval_empty],
      (* goal 3 (of 3) *)
      Q.EXISTS_TAC `(a,b)` >> ASM_SIMP_TAC std_ss [] ]
QED

Theorem right_open_interval_11 :
    !a b c d. a < b /\ c < d ==>
             ((right_open_interval a b = right_open_interval c d) <=>
              (a = c) /\ (b = d))
Proof
    rpt STRIP_TAC
 >> reverse EQ_TAC >- RW_TAC std_ss []
 >> RW_TAC std_ss [right_open_interval, GSPECIFICATION, Once EXTENSION]
 >| [ (* goal 1 (of 2) *)
     `c <= a /\ a < d` by PROVE_TAC [REAL_LE_REFL] \\
     `a <= c /\ c < d` by PROVE_TAC [REAL_LE_REFL] \\
      rw [GSYM REAL_LE_ANTISYM],
      (* goal 2 (of 2) *)
      CCONTR_TAC \\
     `b < d \/ d < b` by PROVE_TAC [REAL_LT_TOTAL] >| (* 2 subgoals *)
      [ (* goal 2.1 (of 2) *)
        Cases_on `b <= c`
        >- (`a <= c /\ c < b` by PROVE_TAC [REAL_LE_REFL] \\
            PROVE_TAC [REAL_LET_ANTISYM]) \\
        POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [real_lte])) \\
        STRIP_ASSUME_TAC (MATCH_MP REAL_MEAN (ASSUME ``b < d :real``)) \\
       `c <= z` by PROVE_TAC [REAL_LT_IMP_LE, REAL_LT_TRANS] \\
       `a <= z /\ z < b` by PROVE_TAC [] \\
        PROVE_TAC [REAL_LT_ANTISYM],
        (* goal 2.2 (of 2) *)
        Cases_on `d <= a`
        >- (`c <= a /\ a < d` by PROVE_TAC [REAL_LE_REFL] \\
            PROVE_TAC [REAL_LET_ANTISYM]) \\
        POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [real_lte])) \\
        STRIP_ASSUME_TAC (MATCH_MP REAL_MEAN (ASSUME ``d < b :real``)) \\
       `a <= z` by PROVE_TAC [REAL_LT_IMP_LE, REAL_LT_TRANS] \\
       `c <= z /\ z < d` by PROVE_TAC [] \\
        PROVE_TAC [REAL_LT_ANTISYM] ] ]
QED

Theorem right_open_interval_empty_eq :
    !a b. (a = b) ==> (right_open_interval a b = {})
Proof
    RW_TAC std_ss [right_open_interval_empty, REAL_LT_REFL]
QED

val FINITE_TWO = Q.prove (`!s t. FINITE {s; t}`,
    PROVE_TAC [FINITE_INSERT, FINITE_SING]);

Theorem right_open_interval_DISJOINT :
    !a b c d. a <= b /\ b <= c /\ c <= d ==>
              DISJOINT (right_open_interval a b) (right_open_interval c d)
Proof
    RW_TAC std_ss [DISJOINT_DEF, INTER_DEF, right_open_interval,
                   EXTENSION, GSPECIFICATION, NOT_IN_EMPTY]
 >> Suff `x < b ==> ~(c <= x)` >- METIS_TAC []
 >> DISCH_TAC >> REWRITE_TAC [real_lte]
 >> MATCH_MP_TAC REAL_LTE_TRANS
 >> Q.EXISTS_TAC `b` >> art []
QED

Theorem right_open_interval_disjoint :
    !a b c d. a <= b /\ b <= c /\ c <= d ==>
              disjoint {right_open_interval a b; right_open_interval c d}
Proof
    rpt STRIP_TAC
 >> Cases_on `right_open_interval a b = right_open_interval c d`
 >- PROVE_TAC [disjoint_same]
 >> MATCH_MP_TAC disjoint_two >> art []
 >> MATCH_MP_TAC right_open_interval_DISJOINT >> art []
QED

Theorem right_open_interval_inter :
    !a b c d. right_open_interval a b INTER right_open_interval c d =
              right_open_interval (max a c) (min b d)
Proof
    rpt GEN_TAC
 >> `min b d <= b /\ min b d <= d` by PROVE_TAC [REAL_MIN_LE1, REAL_MIN_LE2]
 >> `a <= max a c /\ c <= max a c` by PROVE_TAC [REAL_LE_MAX1, REAL_LE_MAX2]
 >> Cases_on `~(a < b)`
 >- (`right_open_interval a b = {}` by PROVE_TAC [right_open_interval_empty] \\
     fs [GSYM real_lte] \\
     `min b d <= max a c` by PROVE_TAC [REAL_LE_TRANS] \\
     PROVE_TAC [right_open_interval_empty, real_lte])
 >> Cases_on `~(c < d)`
 >- (`right_open_interval c d = {}` by PROVE_TAC [right_open_interval_empty] \\
     fs [GSYM real_lte] \\
     `min b d <= max a c` by PROVE_TAC [REAL_LE_TRANS] \\
     PROVE_TAC [right_open_interval_empty, real_lte])
 >> fs []
 (* now we have assumeed that `a < b /\ c < d`, then there're 4 major cases:
                           ______
       ____________       /      \
  ----/------------\-----/--------\------>  (case 1: b <= c)
     a              b   c          d
              ________
       ______/_____   \  ___
  ----/-----/------\---\----\------------>  (case 2: c < b /\ a <= c)
     a     c        b   d    b'
              ________         _____
             /      __\___________  \
  ----------/------/---\----------\--\--->  (case 3: c < b /\ c < a /\ a <= d)
           c      a     d          b  d'
       _______
      /       \     ______________
  ---/---------\---/--------------\------>  (case 4: c < b /\ c < a /\ d < a)
     c          d a                b
  *)
 >> Cases_on `b <= c` (* case 1 *)
 >- (`min b d <= max a c` by PROVE_TAC [REAL_LE_TRANS] \\
     `right_open_interval (max a c) (min b d) = {}`
        by PROVE_TAC [right_open_interval_empty, real_lte] >> POP_ORW \\
     RW_TAC std_ss [right_open_interval, INTER_DEF, EXTENSION,
                    GSPECIFICATION, NOT_IN_EMPTY] \\
     Suff `x < b ==> ~(c <= x)` >- METIS_TAC [] \\
     RW_TAC std_ss [real_lte] \\
     MATCH_MP_TAC REAL_LTE_TRANS >> Q.EXISTS_TAC `b` >> art [])
 >> POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [real_lte]))
 >> Cases_on `a <= c` (* case 2 *)
 >- (Cases_on `b <= d`
     >- (`(max a c = c) /\ (min b d = b)` by PROVE_TAC [REAL_MAX_REDUCE, REAL_MIN_REDUCE] \\
         RW_TAC std_ss [right_open_interval, INTER_DEF, EXTENSION, GSPECIFICATION] \\
         EQ_TAC >> RW_TAC std_ss [] >|
         [ MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `c` >> art [],
           MATCH_MP_TAC REAL_LTE_TRANS >> Q.EXISTS_TAC `b` >> art [] ]) \\
     POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [real_lte])) \\
    `(max a c = c) /\ (min b d = d)` by PROVE_TAC [REAL_MAX_REDUCE, REAL_MIN_REDUCE] \\
     RW_TAC std_ss [right_open_interval, INTER_DEF, EXTENSION, GSPECIFICATION] \\
     EQ_TAC >> RW_TAC std_ss [] >|
     [ MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `c` >> art [],
       MATCH_MP_TAC REAL_LT_TRANS >> Q.EXISTS_TAC `d` >> art [] ])
 >> POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [real_lte]))
 >> Cases_on `a <= d` (* case 3 *)
 >- (Cases_on `d <= b`
     >- (`(max a c = a) /\ (min b d = d)` by PROVE_TAC [REAL_MAX_REDUCE, REAL_MIN_REDUCE] \\
         RW_TAC std_ss [right_open_interval, INTER_DEF, EXTENSION, GSPECIFICATION] \\
         EQ_TAC >> RW_TAC std_ss [] >|
         [ MATCH_MP_TAC REAL_LTE_TRANS >> Q.EXISTS_TAC `d` >> art [],
           MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `a` >> art [] \\
           MATCH_MP_TAC REAL_LT_IMP_LE >> art [] ]) \\
     POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [real_lte])) \\
    `(max a c = a) /\ (min b d = b)` by PROVE_TAC [REAL_MAX_REDUCE, REAL_MIN_REDUCE] \\
     RW_TAC std_ss [right_open_interval, INTER_DEF, EXTENSION, GSPECIFICATION] \\
     EQ_TAC >> RW_TAC std_ss [] >|
     [ MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `a` >> art [] \\
       MATCH_MP_TAC REAL_LT_IMP_LE >> art [],
       MATCH_MP_TAC REAL_LTE_TRANS >> Q.EXISTS_TAC `b` >> art [] \\
       MATCH_MP_TAC REAL_LT_IMP_LE >> art [] ])
 >> POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [real_lte]))
 >> `min b d < max a c` by PROVE_TAC [REAL_LET_TRANS, REAL_LT_TRANS, REAL_LTE_TRANS]
 >> `right_open_interval (max a c) (min b d) = {}`
       by PROVE_TAC [right_open_interval_empty, REAL_LT_IMP_LE, real_lte]
 >> RW_TAC std_ss [right_open_interval, INTER_DEF, EXTENSION,
                   GSPECIFICATION, NOT_IN_EMPTY]
 >> Suff `a <= x ==> ~(x < d)` >- METIS_TAC []
 >> RW_TAC std_ss [GSYM real_lte]
 >> MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `a` >> art []
 >> MATCH_MP_TAC REAL_LT_IMP_LE >> art []
QED

(* or, they must have non-empty intersections *)
Theorem right_open_interval_union_imp :
    !a b c d. a < b /\ c < d /\
             (right_open_interval a b) UNION (right_open_interval c d)
              IN subsets right_open_intervals ==> a <= d /\ c <= b
Proof
    RW_TAC std_ss [right_open_intervals, right_open_interval, subsets_def,
                   GSPECIFICATION, UNION_DEF, EXTENSION]
 >> Cases_on `x` >> fs [EXTENSION, GSPECIFICATION] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      CCONTR_TAC \\
      POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [real_lte])) \\
     `q <= a /\ a < r` by PROVE_TAC [REAL_LE_REFL] \\
     `q <= c /\ c < r` by PROVE_TAC [REAL_LE_REFL] \\
      STRIP_ASSUME_TAC (MATCH_MP REAL_MEAN (ASSUME ``d < a :real``)) \\

     `c < z` by PROVE_TAC [REAL_LT_TRANS] \\
     `q <= z` by PROVE_TAC [REAL_LET_TRANS, REAL_LT_IMP_LE] \\
     `z < r` by PROVE_TAC [REAL_LT_TRANS] \\
     `a <= z /\ z < b \/ c <= z /\ z < d` by PROVE_TAC []
      >| [ PROVE_TAC [REAL_LET_ANTISYM],
           PROVE_TAC [REAL_LT_ANTISYM] ],
      (* goal 2 (of 2) *)
      CCONTR_TAC \\
      POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [real_lte])) \\
     `q <= a /\ a < r` by PROVE_TAC [REAL_LE_REFL] \\
     `q <= c /\ c < r` by PROVE_TAC [REAL_LE_REFL] \\
      STRIP_ASSUME_TAC (MATCH_MP REAL_MEAN (ASSUME ``b < c :real``)) \\
     `a < z` by PROVE_TAC [REAL_LT_TRANS] \\
     `q <= z` by PROVE_TAC [REAL_LT_IMP_LE, REAL_LET_TRANS] \\
     `z < r` by PROVE_TAC [REAL_LT_TRANS] \\
     `a <= z /\ z < b \/ c <= z /\ z < d` by PROVE_TAC []
      >| [ PROVE_TAC [REAL_LT_ANTISYM],
           PROVE_TAC [REAL_LET_ANTISYM] ] ]
QED

Theorem right_open_interval_union :
    !a b c d. a < b /\ c < d /\ a <= d /\ c <= b ==>
             (right_open_interval a b UNION right_open_interval c d =
              right_open_interval (min a c) (max b d))
Proof
    rpt STRIP_TAC
 >> `min a c <= a /\ min a c <= c` by PROVE_TAC [REAL_MIN_LE1, REAL_MIN_LE2]
 >> `b <= max b d /\ d <= max b d` by PROVE_TAC [REAL_LE_MAX1, REAL_LE_MAX2]
 >> RW_TAC std_ss [right_open_interval, EXTENSION, GSPECIFICATION, IN_UNION]
 >> EQ_TAC >> rpt STRIP_TAC (* 5 subgoals, first 4 are easy *)
 >- (MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `a` >> art [])
 >- (MATCH_MP_TAC REAL_LTE_TRANS >> Q.EXISTS_TAC `b` >> art [])
 >- (MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `c` >> art [])
 >- (MATCH_MP_TAC REAL_LTE_TRANS >> Q.EXISTS_TAC `d` >> art [])
 >> Cases_on `a <= c` (* 2 subgoals *)
 >| [ (* goal 5.1 (of 2) *)
     `min a c = a` by PROVE_TAC [REAL_MIN_REDUCE] >> fs [] \\
      Cases_on `x < c`
      >- (DISJ1_TAC \\
          MATCH_MP_TAC REAL_LTE_TRANS >> Q.EXISTS_TAC `c` >> art []) \\
      POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [GSYM real_lte])) \\
      Cases_on `x < b` >- (DISJ1_TAC >> art []) \\
      POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [GSYM real_lte])) \\
      DISJ2_TAC >> art [] \\
      MATCH_MP_TAC REAL_LT_MAX_BETWEEN >> Q.EXISTS_TAC `b` >> art [],
      (* goal 5.2 (of 2) *)
      POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [real_lte])) \\
      Cases_on `x < a`
      >- (DISJ2_TAC \\
          CONJ_TAC
          >- (MATCH_MP_TAC REAL_MIN_LE_BETWEEN >> Q.EXISTS_TAC `a` >> art []) \\
          MATCH_MP_TAC REAL_LTE_TRANS >> Q.EXISTS_TAC `a` >> art []) \\
      POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [GSYM real_lte])) \\
      Cases_on `x < b` >- (DISJ1_TAC >> art []) \\
      POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [GSYM real_lte])) \\
     `c <= x` by PROVE_TAC [REAL_LTE_TRANS, REAL_LT_IMP_LE] \\
      DISJ2_TAC >> art [] \\
      MATCH_MP_TAC REAL_LT_MAX_BETWEEN >> Q.EXISTS_TAC `b` >> art [] ]
QED

Theorem right_open_interval_DISJOINT_imp :
    !a b c d. a < b /\ c < d /\
              DISJOINT (right_open_interval a b) (right_open_interval c d) ==>
              b <= c \/ d <= a
Proof
    RW_TAC std_ss [DISJOINT_DEF, INTER_DEF, right_open_interval, EXTENSION,
                   GSPECIFICATION, NOT_IN_EMPTY]
 >> Suff `a < d ==> b <= c` >- METIS_TAC [real_lte]
 >> DISCH_TAC
 >> CCONTR_TAC
 >> POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [real_lte]))
 >> Cases_on `c <= a`
 >- (Q.PAT_X_ASSUM `!x. P` (STRIP_ASSUME_TAC o (Q.SPEC `a`)) \\
     fs [REAL_LE_REFL])
 >> POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [real_lte]))
 >> Cases_on `d < b`
 >- (Q.PAT_X_ASSUM `!x. P` (STRIP_ASSUME_TAC o (Q.SPEC `c`)) >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
      `c < a` by PROVE_TAC [real_lte] >> PROVE_TAC [REAL_LT_ANTISYM],
       (* goal 2 (of 2) *)
       PROVE_TAC [REAL_LE_ANTISYM] ])
 >> POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [GSYM real_lte]))
 >> STRIP_ASSUME_TAC (MATCH_MP REAL_MEAN (ASSUME ``c < b :real``))
 >> Q.PAT_X_ASSUM `!x. P` (STRIP_ASSUME_TAC o (Q.SPEC `z`)) (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
     `a < z` by PROVE_TAC [REAL_LT_TRANS] \\
     `z < a` by PROVE_TAC [real_lte] \\
      PROVE_TAC [REAL_LT_ANTISYM],
      (* goal 2 (of 3) *)
     `z < c` by PROVE_TAC [real_lte] \\
      PROVE_TAC [REAL_LT_ANTISYM],
      (* goal 3 (of 3) *)
     `z < d` by PROVE_TAC [REAL_LTE_TRANS] ]
QED

Theorem right_open_intervals_semiring :
    semiring right_open_intervals
Proof
    RW_TAC std_ss [semiring_def, right_open_intervals, space_def, subsets_def,
                   subset_class_def, SUBSET_UNIV] (* 3 subgoals *)
 >- (SIMP_TAC std_ss [GSPECIFICATION, IN_UNIV] \\
     Q.EXISTS_TAC `(0,0)` >> SIMP_TAC std_ss [right_open_interval_empty_eq])
 >- (fs [GSPECIFICATION, IN_UNIV] \\
     Cases_on `x` >> Cases_on `x'` >> fs [] \\
     rename1 `s = right_open_interval a b` \\
     rename1 `t = right_open_interval c d` \\
     Q.EXISTS_TAC `(max a c,min b d)` >> SIMP_TAC std_ss [] \\
     REWRITE_TAC [right_open_interval_inter])
 >> fs [GSPECIFICATION, IN_UNIV]
 >> Cases_on `x` >> Cases_on `x'` >> fs []
 >> rename1 `s = right_open_interval a b`
 >> rename1 `t = right_open_interval c d`
 >> Cases_on `~(a < b)`
 >- (fs [GSYM right_open_interval_empty] \\
     Q.EXISTS_TAC `{}` \\
     ASM_SIMP_TAC std_ss [EMPTY_SUBSET, FINITE_EMPTY, disjoint_empty])
 >> Cases_on `~(c < d)`
 >- (fs [GSYM right_open_interval_empty] \\
     Q.EXISTS_TAC `{right_open_interval a b}` \\
     ASM_SIMP_TAC std_ss [BIGUNION_SING, disjoint_sing, FINITE_SING, SUBSET_DEF,
                          IN_SING, GSPECIFICATION] \\
     Q.EXISTS_TAC `(a,b)` >> SIMP_TAC std_ss [])
 >> fs []
 (* now we have assumeed that `a < b /\ c < d`, then there're 4 major cases:
                           ______
       ____________       /      \
  ----/------------\-----/--------\------>  (case 1: b <= c)
     a              b   c          d
              ________
       ______/_____   \  ___
  ----/-----/------\---\----\------------>  (case 2: c < b /\ a <= c)
     a     c        b   d    b'
              ________         _____
             /      __\___________  \
  ----------/------/---\----------\--\--->  (case 3: c < b /\ c < a /\ a <= d)
           c      a     d          b  d'
       _______
      /       \     ______________
  ---/---------\---/--------------\------>  (case 4: c < b /\ c < a /\ d < a)
     c          d a                b
  *)
 >> Cases_on `b <= c` (* case 1 *)
 >- (Q.EXISTS_TAC `{right_open_interval a b}` \\
     rw [FINITE_SING, disjoint_sing] >- (qexistsl_tac [`a`, `b`] >> rw []) \\
     RW_TAC std_ss [right_open_interval, EXTENSION, IN_DIFF,
                    GSPECIFICATION, NOT_IN_EMPTY, SUBSET_DEF, IN_BIGUNION] \\
     Suff `x < b ==> ~(c <= x)` >- METIS_TAC [] \\
     RW_TAC std_ss [real_lte] \\
     MATCH_MP_TAC REAL_LTE_TRANS >> Q.EXISTS_TAC `b` >> art [])
 >> POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [real_lte]))
 >> Cases_on `a <= c` (* case 2 *)
 >- (Cases_on `b <= d`
     >- (Q.EXISTS_TAC `{right_open_interval a c}` \\
         rw [FINITE_SING, disjoint_sing] >- (qexistsl_tac [`a`, `c`] >> rw []) \\
         RW_TAC std_ss [right_open_interval, IN_DIFF, EXTENSION, GSPECIFICATION] \\
         EQ_TAC >> RW_TAC std_ss [real_lte] >|
         [ PROVE_TAC [REAL_LT_REFL, REAL_LTE_TRANS],
           MATCH_MP_TAC REAL_LT_TRANS >> Q.EXISTS_TAC `c` >> art [] ]) \\
     POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [real_lte])) \\
     Q.EXISTS_TAC `{right_open_interval a c; right_open_interval d b}` \\
     rw [FINITE_TWO]
     >- (qexistsl_tac [`a`, `c`] >> rw [])
     >- (qexistsl_tac [`d`, `b`] >> rw [])
     >- (MATCH_MP_TAC right_open_interval_disjoint >> PROVE_TAC [REAL_LT_IMP_LE]) \\
     RW_TAC std_ss [right_open_interval, IN_DIFF, IN_UNION, EXTENSION, GSPECIFICATION] \\
     EQ_TAC >> RW_TAC real_ss [real_lte] >> fs [] >|
     [ MATCH_MP_TAC REAL_LT_TRANS >> Q.EXISTS_TAC `c` >> art [],
       fs [GSYM real_lte] >> MATCH_MP_TAC REAL_LT_IMP_LE \\
       PROVE_TAC [REAL_LET_TRANS, REAL_LTE_TRANS] ])
 >> POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [real_lte]))
 >> Cases_on `a <= d` (* case 3 *)
 >- (Cases_on `d <= b`
     >- (Q.EXISTS_TAC `{right_open_interval d b}` \\
         rw [FINITE_SING, disjoint_sing] >- (qexistsl_tac [`d`, `b`] >> rw []) \\
         RW_TAC std_ss [right_open_interval, IN_DIFF, EXTENSION, GSPECIFICATION] \\
         EQ_TAC >> RW_TAC std_ss [real_lte] >> fs [GSYM real_lte] >|
         [ PROVE_TAC [REAL_LTE_ANTISYM, REAL_LT_TRANS],
           MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `d` >> art [] ]) \\
     POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [real_lte])) \\
     Q.EXISTS_TAC `{}` \\
     RW_TAC std_ss [right_open_interval, EXTENSION, IN_DIFF, disjoint_empty,
                    GSPECIFICATION, NOT_IN_EMPTY, SUBSET_DEF, IN_BIGUNION,
                    FINITE_EMPTY] \\
     Suff `a <= x /\ x < b ==> c <= x /\ x < d ` >- METIS_TAC [] \\
     RW_TAC std_ss [] >|
     [ MATCH_MP_TAC REAL_LT_IMP_LE \\
       MATCH_MP_TAC REAL_LTE_TRANS >> Q.EXISTS_TAC `a` >> art [],
       MATCH_MP_TAC REAL_LT_TRANS >> Q.EXISTS_TAC `b` >> art [] ])
 (* case 4 *)
 >> POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [real_lte]))
 >> Q.EXISTS_TAC `{right_open_interval a b}`
 >> rw [FINITE_SING, disjoint_sing] >- (qexistsl_tac [`a`, `b`] >> rw [])
 >> RW_TAC std_ss [right_open_interval, IN_DIFF, EXTENSION, GSPECIFICATION]
 >> EQ_TAC >> RW_TAC real_ss [real_lte] >> fs [GSYM real_lte]
 >> DISJ2_TAC
 >> MATCH_MP_TAC REAL_LT_IMP_LE
 >> MATCH_MP_TAC REAL_LTE_TRANS >> Q.EXISTS_TAC `a` >> art []
QED

Theorem right_open_intervals_sigma_borel :
    sigma (space right_open_intervals) (subsets right_open_intervals) = borel
Proof
    ASSUME_TAC space_borel
 >> ASSUME_TAC sigma_algebra_borel
 >> `space (sigma (space right_open_intervals) (subsets right_open_intervals)) = UNIV`
     by PROVE_TAC [SPACE_SIGMA, right_open_intervals, space_def]
 >> Suff `subsets (sigma (space right_open_intervals) (subsets right_open_intervals)) =
          subsets borel` >- PROVE_TAC [SPACE]
 >> MATCH_MP_TAC SUBSET_ANTISYM
 >> CONJ_TAC
 >- (`space right_open_intervals = space borel`
       by PROVE_TAC [right_open_intervals, space_def] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_SUBSET >> art [] \\
     RW_TAC std_ss [SUBSET_DEF, right_open_intervals, subsets_def, GSPECIFICATION, IN_UNIV] \\
     Cases_on `x'` >> fs [right_open_interval] \\
     REWRITE_TAC [borel_measurable_sets_ge_less])
 >> REWRITE_TAC [borel_eq_less]
 >> MATCH_MP_TAC SIGMA_PROPERTY (* this lemma is so useful! *)
 >> STRONG_CONJ_TAC
 >- REWRITE_TAC [subset_class_def, SUBSET_UNIV] >> DISCH_TAC
 >> STRONG_CONJ_TAC
 >- (Suff `{} IN (subsets right_open_intervals)`
     >- PROVE_TAC [SUBSET_DEF, SIGMA_SUBSET_SUBSETS] \\
     RW_TAC std_ss [right_open_intervals, subsets_def, GSPECIFICATION, IN_UNIV] \\
     Q.EXISTS_TAC `(0,0)` >> SIMP_TAC std_ss [right_open_interval_empty_eq])
 >> DISCH_TAC
 >> Know `sigma_algebra (sigma (space right_open_intervals) (subsets right_open_intervals))`
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
     RW_TAC std_ss [subset_class_def, space_def, subsets_def, right_open_intervals,
                    SUBSET_UNIV]) >> DISCH_TAC
 >> STRONG_CONJ_TAC
 >- (RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV, GSPECIFICATION] \\
     Know `{x | x < a} = BIGUNION (IMAGE (\n. right_open_interval (a - &n) a) univ(:num))`
     >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, GSPECIFICATION,
                        right_open_interval] \\
         EQ_TAC >> rw [] \\
         STRIP_ASSUME_TAC (Q.SPEC `a - x` SIMP_REAL_ARCH) \\
         Q.EXISTS_TAC `n` \\
         NTAC 2 (POP_ASSUM MP_TAC) >> REAL_ARITH_TAC) >> Rewr' \\
     MATCH_MP_TAC SIGMA_ALGEBRA_ENUM >> rw [IN_FUNSET, IN_UNIV] \\
     ASSUME_TAC (Q.ISPECL [`space right_open_intervals`, `subsets right_open_intervals`]
                          SIGMA_SUBSET_SUBSETS) \\
     Suff `right_open_interval (a - &n) a IN (subsets right_open_intervals)`
     >- ASM_SET_TAC [] \\
     rw [right_open_intervals, subsets_def, GSPECIFICATION] \\
     Q.EXISTS_TAC `(a - &n, a)` >> rw []) >> DISCH_TAC
 >> CONJ_TAC
 >- (RW_TAC std_ss [IN_INTER] \\
     Q.PAT_X_ASSUM `space (sigma (space right_open_intervals) (subsets right_open_intervals)) = UNIV`
         (ONCE_REWRITE_TAC o wrap o (MATCH_MP EQ_SYM)) \\
     MATCH_MP_TAC ALGEBRA_COMPL >> art [] \\
     fs [sigma_algebra_def])
 >> fs [sigma_algebra_def]
QED

Theorem right_open_intervals_subset_borel :
    (subsets right_open_intervals) SUBSET subsets borel
Proof
    REWRITE_TAC [SYM right_open_intervals_sigma_borel]
 >> PROVE_TAC [SIGMA_SUBSET_SUBSETS]
QED

(* another equivalent definition of `borel` *)
Theorem borel_eq_ge_less :
    borel = sigma UNIV (IMAGE (\(a,b). {x | a <= x /\ x < b}) UNIV)
Proof
    ASSUME_TAC (REWRITE_RULE [space_borel, space_def, subsets_def,
                              right_open_interval, right_open_intervals]
                             (SYM right_open_intervals_sigma_borel))
 >> Suff `IMAGE (\(a,b). {x | a <= x /\ x < b}) univ(:real # real) =
          {{x:real | a <= x /\ x < b} | T}` >- rw []
 >> KILL_TAC
 >> RW_TAC std_ss [Once EXTENSION, IN_IMAGE, IN_UNIV, GSPECIFICATION]
 >> EQ_TAC >> rpt STRIP_TAC
 >> Cases_on `x'` >> fs []
 >> Q.EXISTS_TAC `(q,r)` >> rw []
QED

(* ------------------------------------------------------------------------- *)
(* Standard Cubes                                                            *)
(* ------------------------------------------------------------------------- *)

val _ = hide "line"; (* for satefy purposes only *)

Definition line :
    line n = {x:real | -&n <= x /\ x <= &n}
End

val borel_line = store_thm
  ("borel_line", ``!n. line n IN subsets borel``,
    RW_TAC std_ss [line]
 >> MATCH_MP_TAC borel_closed
 >> SIMP_TAC std_ss [GSYM interval, CLOSED_INTERVAL]);

val line_closed = store_thm
  ("line_closed", ``!n. closed (line n)``,
    RW_TAC std_ss [GSYM interval, line, CLOSED_INTERVAL]);

Theorem LINE_MONO : (* was: line_subset *)
    !n N. n <= N ==> line n SUBSET line N
Proof
  FULL_SIMP_TAC std_ss [line, SUBSET_DEF, GSPECIFICATION] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
  [EXISTS_TAC ``-&n:real`` THEN ASM_SIMP_TAC real_ss [],
   EXISTS_TAC ``&n:real`` THEN ASM_SIMP_TAC real_ss []]
QED

Theorem LINE_MONO_EQ : (* was: line_subset_iff *)
    !n N. line n SUBSET line N <=> n <= N
Proof
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [ALL_TAC, REWRITE_TAC [LINE_MONO]] THEN
  SIMP_TAC std_ss [line, SUBSET_DEF, GSPECIFICATION] THEN
  DISCH_THEN (MP_TAC o SPEC ``&n:real``) THEN
  KNOW_TAC ``-&n <= &n:real /\ &n <= &n:real`` THENL
  [SIMP_TAC std_ss [REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC ``0:real`` THEN
   GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_NEG_0] THEN
   SIMP_TAC std_ss [REAL_LE_NEG, REAL_POS], ALL_TAC] THEN
  DISC_RW_KILL THEN SIMP_TAC real_ss []
QED

Theorem BALL_IN_LINE : (* was: ball_subset_line *)
    !n. ball (0,&n) SUBSET line n
Proof
  GEN_TAC THEN SIMP_TAC std_ss [ball, line, SUBSET_DEF, GSPECIFICATION] THEN
  GEN_TAC THEN SIMP_TAC std_ss [DIST_0] THEN REAL_ARITH_TAC
QED

Theorem REAL_IN_LINE : (* was: mem_big_line *)
    !x. ?n. x IN line n
Proof
 GEN_TAC THEN MP_TAC (ISPEC ``x:real`` SIMP_REAL_ARCH) THEN
 STRIP_TAC THEN SIMP_TAC std_ss [line, GSPECIFICATION] THEN
 ASM_CASES_TAC ``0 <= x:real`` THENL
 [EXISTS_TAC ``n:num`` THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN
 MP_TAC (ISPEC ``-x:real`` SIMP_REAL_ARCH) THEN STRIP_TAC THEN
 EXISTS_TAC ``n':num`` THEN ASM_REAL_ARITH_TAC
QED

Theorem LINE_MONO_SUC : (* was: line_subset_Suc *)
    !n. line n SUBSET line (SUC n)
Proof
    GEN_TAC THEN MATCH_MP_TAC LINE_MONO THEN ARITH_TAC
QED

val _ = export_theory ();
