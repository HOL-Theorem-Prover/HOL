(* ------------------------------------------------------------------------- *)
(* Borel measurable sets defined on reals (from "examples/diningcryptos")    *)
(* Author: Aaron Coble (2010)                                                *)
(* Cambridge University                                                      *)
(* ------------------------------------------------------------------------- *)
(* Extended by Chun Tian (2020-2021) using some materials from:              *)
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
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open metisLib arithmeticTheory pred_setTheory pred_setLib numTheory numLib
     listTheory combinTheory pairTheory realTheory realLib jrhUtils
     seqTheory real_sigmaTheory transcTheory metricTheory topologyTheory;

open cardinalTheory real_topologyTheory iterateTheory real_of_ratTheory;

open hurdUtils util_probTheory sigma_algebraTheory;

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "borel" (renamed to "real_borel")               *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "real_borel";

val ASM_ARITH_TAC = rpt (POP_ASSUM MP_TAC) THEN ARITH_TAC;
val ASM_REAL_ARITH_TAC = REAL_ASM_ARITH_TAC;
val DISC_RW_KILL = DISCH_TAC >> ONCE_ASM_REWRITE_TAC [] >> POP_ASSUM K_TAC;
fun METIS ths tm = prove(tm,METIS_TAC ths);

val set_ss = std_ss ++ PRED_SET_ss;

val _ = intLib.deprecate_int ();
val _ = ratLib.deprecate_rat ();

(* ************************************************************************* *)
(* Basic Definitions                                                         *)
(* ************************************************************************* *)

(* The new definition is based on open sets.

   See martingaleTheory for 2-dimensional Borel space based on pairTheory
   (term: ‘borel CROSS borel’).

   See examples/probability/stochastic_processesTheory for n-dimensional Borel
   spaces based on fcpTheory (term: ‘borel of_dimension(:'N)’).

   See "borel_def" for the old definition.
 *)
Definition borel :
    borel = sigma univ(:real) {s | open s}
End

(* was: borel_measurable [definition] *)
Overload borel_measurable = “\a. measurable a borel”

(* The definition of ‘indicator_fn’ is now merged with iterateTheory.indicator *)
Overload indicator_fn[local] = “indicator”
Theorem indicator_fn_def[local] = indicator

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

(* NOTE: removed ‘sigma_algebra M’ due to changes of ‘measurable’ *)
Theorem in_borel_measurable_open :
    !f M. f IN borel_measurable M <=>
          (!s. s IN subsets (sigma UNIV {s | open s}) ==>
           (PREIMAGE f s) INTER (space M) IN subsets M)
Proof
  REPEAT GEN_TAC THEN RW_TAC std_ss [measurable_def] THEN
  SIMP_TAC std_ss [GSPECIFICATION] THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC std_ss [] THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [borel],
   EVAL_TAC THEN SIMP_TAC std_ss [borel, sigma_def, space_def] THEN
   SIMP_TAC std_ss [IN_UNIV] THEN SIMP_TAC std_ss [IN_DEF] THEN rw[IN_FUNSET],
   FIRST_X_ASSUM MATCH_MP_TAC THEN POP_ASSUM MP_TAC THEN
   SIMP_TAC std_ss [borel, sigma_def, subsets_def, IN_BIGINTER] THEN
   SIMP_TAC std_ss [GSPECIFICATION] THEN REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [SUBSET_DEF, sigma_sets_basic] THEN
   MATCH_MP_TAC sigma_algebra_sigma_sets THEN REWRITE_TAC [POW_DEF] THEN
   SET_TAC []]
QED

(* NOTE: removed ‘sigma_algebra M’ due to changes of ‘measurable’ *)
val in_borel_measurable_borel = store_thm
  ("in_borel_measurable_borel",
  ``!f M. f IN borel_measurable M <=>
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
     `0:real < ((1 / 2) pow n)` by METIS_TAC [POW_HALF_POS] THEN
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

Theorem borel_eq_gr_le :
    borel = sigma UNIV (IMAGE (\(a,b). {x | a < x /\ x <= b}) UNIV)
Proof
    ONCE_REWRITE_TAC [METIS [] ``{x | a < x /\ x <= b} =
                                 (\a b. {x:real | a < x /\ x <= b}) a b``]
 >> Suff `(borel = sigma univ(:real) (IMAGE (\a. {x | x <= a}) univ(:real))) /\
          (!i. (\a. {x | x <= a}) i IN
               subsets (sigma univ(:real)
                             (IMAGE (\(i,j). (\a b. {x | a < x /\ x <= b}) i j)
                                    univ(:real # real)))) /\
           !i j. (\a b. {x | a < x /\ x <= b}) i j IN subsets borel`
 >- (DISCH_THEN (MP_TAC o MATCH_MP borel_eq_sigmaI5) >> SIMP_TAC std_ss [])
 >> SIMP_TAC std_ss [borel_eq_le]
 >> Know `!a. {x | x <= a} =
              BIGUNION {{x:real | -&n < x /\ x <= a} | n IN UNIV}`
 >- (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION, IN_UNIV] \\
     reverse EQ_TAC
     >- (STRIP_TAC >> POP_ASSUM (MP_TAC o SPEC ``x:real``) \\
         ASM_REWRITE_TAC [] >> REAL_ARITH_TAC) \\
     DISCH_TAC \\
     MP_TAC (ISPEC ``x:real`` SIMP_REAL_ARCH_NEG) >> STRIP_TAC \\
     Q.EXISTS_TAC `{x | -&SUC n < x /\ x <= a}` \\
     ASM_SIMP_TAC std_ss [GSPECIFICATION] \\
     CONJ_TAC >- (MATCH_MP_TAC REAL_LTE_TRANS \\
                  Q.EXISTS_TAC ‘-&n’ >> rw []) \\
     Q.EXISTS_TAC ‘SUC n’ >> rw [])
 >> DISCH_TAC
 >> CONJ_TAC
 >- (RW_TAC std_ss [subsets_def, sigma_def, IN_BIGINTER,
                    GSPECIFICATION, SUBSET_DEF] \\
     ONCE_REWRITE_TAC [METIS [] ``{x | -&n < x /\ x <= i} =
                                  (\n. {x:real | -&n < x /\ x <= i}) n``] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UN >> EXISTS_TAC ``univ(:real)`` \\
     ASM_SIMP_TAC std_ss [COUNTABLE_NUM] \\
     RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV] >> FIRST_X_ASSUM MATCH_MP_TAC \\
     SET_TAC [])
 (* below are new steps by Chun Tian *)
 >> rpt GEN_TAC
 >> Know ‘{x | i < x /\ x <= j} = {x | x <= j} DIFF {x | x <= i}’
 >- (rw [Once EXTENSION] >> METIS_TAC [real_lt]) >> Rewr'
 >> MATCH_MP_TAC SIGMA_ALGEBRA_DIFF
 >> STRONG_CONJ_TAC
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA >> rw [subset_class_def])
 >> DISCH_TAC
 >> CONJ_TAC
 >| [ (* goal 1 (of 2) *)
      Suff ‘{x | x <= j} IN (IMAGE (\a. {x | x <= a}) univ(:real))’
      >- METIS_TAC [SUBSET_DEF, SIGMA_SUBSET_SUBSETS] \\
      rw [] >> Q.EXISTS_TAC ‘j’ >> REWRITE_TAC [],
      (* goal 2 (of 2) *)
      Suff ‘{x | x <= i} IN (IMAGE (\a. {x | x <= a}) univ(:real))’
      >- METIS_TAC [SUBSET_DEF, SIGMA_SUBSET_SUBSETS] \\
      rw [] >> Q.EXISTS_TAC ‘i’ >> REWRITE_TAC [] ]
QED

(* NOTE: removed ‘sigma_algebra s’ due to changes in ‘measurable’ *)
val in_borel_measurable = store_thm
  ("in_borel_measurable",
   ``!f s. f IN borel_measurable s <=>
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

(* NOTE: moved ‘sigma_algebra m’ to antecedents due to changes of ‘measurable’

   cf. IN_MEASURABLE_BOREL_RC in borelTheory
 *)
Theorem in_borel_measurable_le :
    !f m. sigma_algebra m ==>
         (f IN borel_measurable m <=>
          f IN (space m -> UNIV) /\
          !a. {w | w IN space m /\ f w <= a} IN subsets m)
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
            >- (RW_TAC std_ss [] >- METIS_TAC []
                >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `a - inv (& (SUC n))`
                >> RW_TAC real_ss [REAL_LT_SUB_RADD, REAL_LT_ADDR, REAL_LT_INV_EQ]
                >> METIS_TAC [])
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
            >- (RW_TAC std_ss [] >- ASM_REWRITE_TAC []
                >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `f x - inv (& (SUC n))`
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

(* NOTE: moved ‘sigma_algebra m’ to antecedents due to changes of ‘measurable’ *)
Theorem in_borel_measurable_gr :
    !f m. sigma_algebra m  ==>
         (f IN borel_measurable m <=>
          f IN (space m -> UNIV) /\
          !a. {w | w IN space m /\ a < f w} IN subsets m)
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

(* NOTE: moved ‘sigma_algebra m’ to antecedents due to changes of ‘measurable’ *)
Theorem in_borel_measurable_less :
    !f m. sigma_algebra m ==>
         (f IN borel_measurable m <=>
          f IN (space m -> UNIV) /\
          !a. {w | w IN space m /\ f w < a} IN subsets m)
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
            >- (RW_TAC std_ss [] >- ASM_REWRITE_TAC [] \\
                MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `f x - inv (&(SUC n))` \\
                RW_TAC real_ss [REAL_LT_SUB_RADD, REAL_LT_ADDR, REAL_LT_INV_EQ])
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

(* NOTE: moved ‘sigma_algebra m’ to antecedents due to changes of ‘measurable’ *)
Theorem in_borel_measurable_ge :
    !f m. sigma_algebra m ==>
         (f IN borel_measurable m <=>
          f IN (space m -> UNIV) /\
          !a. {w | w IN space m /\ a <= f w} IN subsets m)
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

(* borel_measurable_plus_borel_measurable *)
Theorem in_borel_measurable_add :
    !a f g h. sigma_algebra a /\ f IN measurable a borel /\ g IN measurable a borel /\
             (!x. x IN space a ==> (h x = f x + g x)) ==> h IN measurable a borel
Proof
    rpt STRIP_TAC
 >> RW_TAC std_ss [in_borel_measurable_less, IN_FUNSET, IN_UNIV]
 >> Know `!c. {w | w IN space a /\ h w < c} =
              BIGUNION (IMAGE (\r. {x | x IN space a /\ f x < r /\ r < c - g x}) q_set)`
 >- (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION_IMAGE, IN_UNIV, IN_INTER] \\
     EQ_TAC >- (RW_TAC std_ss [] \\
                MATCH_MP_TAC Q_DENSE_IN_REAL \\
                METIS_TAC [REAL_LT_SUB_LADD]) \\
     RW_TAC std_ss [] >- art [] \\
    ‘h x = f x + g x’ by PROVE_TAC [] >> POP_ORW \\
    ‘f x < c - g x’ by PROVE_TAC [REAL_LT_TRANS] \\
     METIS_TAC [REAL_LT_SUB_LADD])
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss []
 >> MATCH_MP_TAC BIGUNION_IMAGE_QSET
 >> RW_TAC std_ss [IN_FUNSET]
 >> rename1 ‘{x | x IN space a /\ f x < r /\ r < c - g x} IN subsets a’
 >> `{x | x IN space a /\ f x < r /\ r < c - g x} =
     {x | x IN space a /\ f x < r} INTER {x | x IN space a /\ r < c - g x}`
      by SET_TAC [] >> POP_ORW
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
 >> CONJ_TAC
 >- (MP_TAC (REWRITE_RULE [IN_FUNSET, IN_UNIV]
                          (Q.SPECL [‘f’, ‘a’] in_borel_measurable_less)) \\
     RW_TAC std_ss [])
 >> Know `!x. x IN space a ==> (r < c - g x <=> g x < c - r)`
 >- (rpt STRIP_TAC \\
     METIS_TAC [REAL_LT_SUB_LADD, REAL_ADD_COMM])
 >> DISCH_TAC
 >> `{x | x IN space a /\ r < c - g x} = {x | x IN space a /\ g x < c - r}` by ASM_SET_TAC []
 >> POP_ORW
 >> MP_TAC (REWRITE_RULE [IN_FUNSET, IN_UNIV]
                         (Q.SPECL [‘g’, ‘a’] in_borel_measurable_less))
 >> RW_TAC std_ss []
QED

Theorem in_borel_measurable_const :
    !a k f. sigma_algebra a /\ (!x. x IN space a ==> (f x = k)) ==> f IN measurable a borel
Proof
    RW_TAC std_ss [in_borel_measurable_less, IN_FUNSET, IN_UNIV]
 >> rename1 ‘{w | w IN space a /\ f w < c} IN subsets a’
 >> Cases_on `c <= k`
 >- (`{x | x IN space a /\ f x < c} = {}` by ASM_SET_TAC [real_lt] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY >> art [])
 >> `{x | x IN space a /\ f x < c} = space a` by ASM_SET_TAC [real_lt]
 >> POP_ORW
 >> MATCH_MP_TAC SIGMA_ALGEBRA_SPACE >> art []
QED

Theorem in_borel_measurable_cmul :
    !a f g z. sigma_algebra a /\ f IN measurable a borel /\
             (!x. x IN space a ==> (g x = z * f x)) ==> g IN measurable a borel
Proof
    RW_TAC std_ss []
 >> Cases_on `z = 0`
 >- METIS_TAC [in_borel_measurable_const, REAL_MUL_LZERO]
 >> Cases_on `0 < z`
 >- (RW_TAC real_ss [in_borel_measurable_less, IN_FUNSET, IN_UNIV] \\
     Know `!c. {x | x IN space a /\ g x < c} = {x | x IN space a /\ f x < c / z}`
     >- (rw [Once EXTENSION] \\
         METIS_TAC [REAL_LT_RDIV_EQ, REAL_MUL_COMM]) >> Rewr' \\
     MP_TAC (REWRITE_RULE [IN_FUNSET, IN_UNIV]
                          (Q.SPECL [‘f’, ‘a’] in_borel_measurable_less)) \\
     RW_TAC std_ss [])
 >> `z < 0` by METIS_TAC [REAL_LT_LE, GSYM real_lte]
 >> RW_TAC real_ss [in_borel_measurable_less, IN_FUNSET, IN_UNIV]
 >> Know `!c. {x | x IN space a /\ g x < c} = {x | x IN space a /\ c / z < f x}`
 >- (rw [Once EXTENSION] \\
     METIS_TAC [REAL_LT_RDIV_EQ_NEG, REAL_MUL_COMM]) >> Rewr'
 >> MP_TAC (REWRITE_RULE [IN_FUNSET, IN_UNIV]
                         (Q.SPECL [‘f’, ‘a’] in_borel_measurable_gr))
 >> RW_TAC std_ss []
QED

(* cf. borel_measurable_sub_borel_measurable (real_measureTheory) *)
Theorem in_borel_measurable_sub :
    !a f g h. sigma_algebra a /\ f IN measurable a borel /\ g IN measurable a borel /\
             (!x. x IN space a ==> (h x = f x - g x)) ==> h IN measurable a borel
Proof
    RW_TAC std_ss []
 >> MATCH_MP_TAC in_borel_measurable_add
 >> qexistsl_tac [`f`, `\x. - g x`]
 >> RW_TAC std_ss []
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC in_borel_measurable_cmul \\
      qexistsl_tac [‘g’, ‘-1’] \\
      RW_TAC real_ss [],
      (* goal 2 (of 2) *)
      REWRITE_TAC [real_sub] ]
QED

Theorem in_borel_measurable_pow2 : (* was: in_borel_measurable_sqr *)
    !a f g. sigma_algebra a /\ f IN measurable a borel /\
            (!x. x IN space a ==> (g x = (f x) pow 2)) ==> g IN measurable a borel
Proof
    rpt STRIP_TAC
 >> Know `!c. {x | f x <= c} INTER space a IN subsets a`
 >- (GEN_TAC >> rfs [in_borel_measurable_le, IN_FUNSET, IN_UNIV] \\
    ‘{x | f x <= c} INTER space a = {x | x IN space a /\ f x <= c}’ by SET_TAC [] \\
     POP_ORW >> art [])
 >> DISCH_TAC
 >> Know `!c. {x | c <= f x} INTER space a IN subsets a`
 >- (GEN_TAC >> rfs [in_borel_measurable_ge, IN_FUNSET, IN_UNIV] \\
    ‘{x | c <= f x} INTER space a = {x | x IN space a /\ c <= f x}’ by SET_TAC [] \\
     POP_ORW >> art [])
 >> DISCH_TAC
 >> simp [IN_FUNSET, in_borel_measurable_le]
 >> Q.X_GEN_TAC ‘c’
 >> ‘{w | w IN space a /\ g w <= c} = {x | g x <= c} INTER space a’ by SET_TAC []
 >> POP_ORW
 >> Cases_on `c < 0`
 >- (Know `{x | g x <= c} INTER space a = {}`
     >- (rw [Once EXTENSION, NOT_IN_EMPTY, GSYM real_lt] \\
         ONCE_REWRITE_TAC [DISJ_COMM] >> STRONG_DISJ_TAC \\
         MATCH_MP_TAC REAL_LTE_TRANS >> Q.EXISTS_TAC ‘0’ >> art [] \\
         METIS_TAC [REAL_LE_POW2]) >> Rewr' \\
     MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY >> art [])
 >> FULL_SIMP_TAC real_ss [real_lt]
 >> Suff `{x | g x <= c} INTER space a =
            ({x | f x <= sqrt c} INTER space a) INTER
            ({x | - (sqrt c) <= f x} INTER space a)`
 >- (Rewr' >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [])
 >> rw [Once EXTENSION]
 >> EQ_TAC
 >- (RW_TAC real_ss []
     >- (Cases_on `f x < 0` >- METIS_TAC [REAL_LTE_TRANS, REAL_LT_IMP_LE, SQRT_POS_LE] \\
         FULL_SIMP_TAC real_ss [real_lt] \\
         Know ‘sqrt (g x) <= sqrt c’
         >- (MATCH_MP_TAC SQRT_MONO_LE >> art [] \\
             METIS_TAC [REAL_LE_POW2]) >> DISCH_TAC \\
         Suff ‘sqrt (g x) = f x’ >- PROVE_TAC [] \\
         MATCH_MP_TAC SQRT_POS_UNIQ >> METIS_TAC [REAL_LE_POW2]) \\
     SPOSE_NOT_THEN ASSUME_TAC \\
     FULL_SIMP_TAC real_ss [GSYM real_lt] \\
    `sqrt c < -(f x)` by METIS_TAC [REAL_LT_NEG, REAL_NEG_NEG] \\
     Know `(sqrt c) pow 2 < (- (f x)) pow 2`
     >- (MATCH_MP_TAC REAL_POW_LT2 >> rw [SQRT_POS_LE]) >> DISCH_TAC \\
    `(sqrt c) pow 2 = c` by METIS_TAC [SQRT_POW2] \\
    `(-1) pow 2 = (1 :real)` by METIS_TAC [POW_MINUS1, MULT_RIGHT_1] \\
    `(- (f x)) pow 2 = (f x) pow 2`
       by RW_TAC std_ss [Once REAL_NEG_MINUS1, POW_MUL, REAL_MUL_LID] \\
     METIS_TAC [real_lt])
 >> RW_TAC std_ss []
 >> Cases_on `0 <= f x` >- METIS_TAC [POW_LE, SQRT_POW2]
 >> FULL_SIMP_TAC real_ss [GSYM real_lt]
 >> `- (f x) <= sqrt c` by METIS_TAC [REAL_LE_NEG, REAL_NEG_NEG]
 >> `(- (f x)) pow 2 <= (sqrt c) pow 2`
      by METIS_TAC [POW_LE, SQRT_POS_LE, REAL_LT_NEG, REAL_NEG_NEG, REAL_NEG_0, REAL_LT_IMP_LE]
 >> `(sqrt c) pow 2 = c` by METIS_TAC [SQRT_POW2]
 >> `(-1) pow 2 = (1 :real)` by METIS_TAC [POW_MINUS1, MULT_RIGHT_1]
 >> `(- (f x)) pow 2 = (f x) pow 2`
       by RW_TAC std_ss [Once REAL_NEG_MINUS1, POW_MUL, REAL_MUL_LID]
 >> METIS_TAC []
QED

Theorem in_borel_measurable_mul :
    !a f g h. sigma_algebra a /\ f IN measurable a borel /\ g IN measurable a borel /\
             (!x. x IN space a ==> (h x = f x * g x)) ==> h IN measurable a borel
Proof
    RW_TAC std_ss []
 >> Know `!x. x IN space a ==>
             (f x * g x = 1 / 2 * ((f x + g x) pow 2 - f x pow 2 - g x pow 2))`
 >- (rpt STRIP_TAC \\
     (MP_TAC o Q.SPECL [`f x`, `g x`]) ADD_POW_2 >> Rewr' \\
     simp [] >> REAL_ARITH_TAC)
 >> DISCH_TAC
 >> MATCH_MP_TAC in_borel_measurable_cmul
 >> Q.EXISTS_TAC `(\x. (f x + g x) pow 2 - f x pow 2 - g x pow 2)`
 >> Q.EXISTS_TAC `1 / 2`
 >> RW_TAC real_ss []
 >> MATCH_MP_TAC in_borel_measurable_sub
 >> Q.EXISTS_TAC `(\x. (f x + g x) pow 2 - f x pow 2)`
 >> Q.EXISTS_TAC `(\x. g x pow 2)`
 >> RW_TAC std_ss []
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC in_borel_measurable_sub \\
      Q.EXISTS_TAC `(\x. (f x + g x) pow 2)` \\
      Q.EXISTS_TAC `(\x. f x pow 2)` \\
      RW_TAC std_ss [] >| (* 2 subgoals *)
      [ (* goal 1.1 (of 2) *)
        MATCH_MP_TAC in_borel_measurable_pow2 \\
        Q.EXISTS_TAC `(\x. f x + g x)` \\
        RW_TAC std_ss [] \\
        MATCH_MP_TAC in_borel_measurable_add \\
        qexistsl_tac [`f`, `g`] \\
        RW_TAC std_ss [],
        (* goal 1.2 (of 2) *)
        MATCH_MP_TAC in_borel_measurable_pow2 >> METIS_TAC [] ],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC in_borel_measurable_pow2 >> METIS_TAC [] ]
QED

(* NOTE: added ‘sigma_algebra a’ due to changes in ‘measurable’

   cf. borelTheory.IN_MEASURABLE_BOREL_MAX
 *)
Theorem in_borel_measurable_max :
    !a f g. sigma_algebra a /\ f IN measurable a borel /\ g IN measurable a borel
        ==> (\x. max (f x) (g x)) IN measurable a borel
Proof
    RW_TAC std_ss [in_borel_measurable_less, max_def, IN_FUNSET, IN_UNIV]
 >> rfs [in_borel_measurable_less]
 >> `!c. {x | x IN space a /\ (if f x <= g x then g x else f x) < c} =
         {x | x IN space a /\ f x < c} INTER
         {x | x IN space a /\ g x < c}`
        by (rw [Once EXTENSION] \\
            EQ_TAC >> rw [] >- METIS_TAC [REAL_LET_TRANS] \\
            METIS_TAC [real_lte, REAL_LT_TRANS])
 >> POP_ORW
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
QED

(* NOTE: added ‘sigma_algebra a’ due to changes in ‘measurable’

   cf. borelTheory.IN_MEASURABLE_BOREL_MIN
 *)
Theorem in_borel_measurable_min :
    !a f g. sigma_algebra a /\ f IN measurable a borel /\ g IN measurable a borel
        ==> (\x. min (f x) (g x)) IN measurable a borel
Proof
    RW_TAC std_ss [in_borel_measurable_less, min_def, IN_FUNSET, IN_UNIV]
 >> rfs [in_borel_measurable_less]
 >> `!c. {x | x IN space a /\ (if f x <= g x then f x else g x) < c} =
         {x | x IN space a /\ f x < c} UNION
         {x | x IN space a /\ g x < c}`
        by (rw [Once EXTENSION] \\
            EQ_TAC >> rw [] >> rw [] >- METIS_TAC [REAL_LET_TRANS] \\
            METIS_TAC [real_lte, REAL_LT_TRANS])
 >> POP_ORW
 >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art []
QED

(* NOTE: added ‘sigma_algebra a’ due to changes in ‘measurable’

   cf. borelTheory.IN_MEASURABLE_BOREL_LT
 *)
Theorem in_borel_measurable_lt2 :
    !a f g. sigma_algebra a /\ f IN measurable a borel /\ g IN measurable a borel ==>
            {x | x IN space a /\ f x < g x} IN subsets a
Proof
    RW_TAC std_ss []
 >> `{x | x IN space a /\ f x < g x} =
      BIGUNION (IMAGE (\r. {x | f x < r /\ r < g x} INTER space a) q_set)`
        by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION_IMAGE, IN_INTER] \\
            EQ_TAC >- RW_TAC std_ss [Q_DENSE_IN_REAL] \\
            METIS_TAC [REAL_LT_TRANS])
 >> POP_ORW
 >> MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION >> art []
 >> CONJ_TAC >- (MATCH_MP_TAC image_countable \\
                 REWRITE_TAC [QSET_COUNTABLE])
 >> rw [SUBSET_DEF]
 >> `{x | f x < r /\ r < g x} INTER space a =
     {x | x IN space a /\ f x < r} INTER {x | x IN space a /\ r < g x}` by SET_TAC []
 >> POP_ORW
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
 >> CONJ_TAC
 >| [ (* goal 1 (of 2) *)
      Q.PAT_X_ASSUM ‘f IN borel_measurable a’ MP_TAC \\
      rw [in_borel_measurable_less, IN_FUNSET],
      (* goal 2 (of 2) *)
      Q.PAT_X_ASSUM ‘g IN borel_measurable a’ MP_TAC \\
      rw [in_borel_measurable_gr, IN_FUNSET] ]
QED

(* NOTE: added ‘sigma_algebra a’ due to changes in ‘measurable’

   cf. borelTheory.IN_MEASURABLE_BOREL_LE
 *)
Theorem in_borel_measurable_le2 :
    !a f g. sigma_algebra a /\ f IN measurable a borel /\ g IN measurable a borel ==>
            {x | x IN space a /\ f x <= g x} IN subsets a
Proof
    RW_TAC std_ss []
 >> `{x | x IN space a /\ f x <= g x} = space a DIFF {x | x IN space a /\ g x < f x}`
      by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_DIFF] \\
          METIS_TAC [real_lte])
 >> POP_ORW
 >> MATCH_MP_TAC SIGMA_ALGEBRA_COMPL
 >> rw [in_borel_measurable_lt2]
 >> fs [in_borel_measurable]
QED

(* NOTE: added ‘sigma_algebra a’ due to changes in ‘measurable’

   cf. borelTheory.IN_MEASURABLE_BOREL_MUL_INDICATOR
 *)
Theorem in_borel_measurable_mul_indicator :
    !a f s. sigma_algebra a /\ f IN measurable a borel /\ s IN subsets a ==>
            (\x. f x * indicator_fn s x) IN measurable a borel
Proof
    rpt STRIP_TAC
 >> rfs [in_borel_measurable_le, IN_FUNSET]
 >> Q.X_GEN_TAC ‘c’
 >> Cases_on `0 <= c`
 >- (`{x | x IN space a /\ f x * indicator_fn s x <= c} =
      ({x | x IN space a /\ f x <= c} INTER s) UNION (space a DIFF s)`
         by (RW_TAC std_ss [indicator_fn_def, EXTENSION, GSPECIFICATION, IN_INTER,
                            IN_UNION, IN_DIFF] \\
             Cases_on `x IN s` >> RW_TAC real_ss []) >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [] \\
     reverse CONJ_TAC >- (MATCH_MP_TAC SIGMA_ALGEBRA_COMPL >> art []) \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [])
 >> `{x | x IN space a /\ f x * indicator_fn s x <= c} =
     {x | x IN space a /\ f x <= c} INTER s`
         by (RW_TAC std_ss [indicator_fn_def, EXTENSION, GSPECIFICATION, IN_INTER] \\
             Cases_on `x IN s` >> RW_TAC real_ss []) >> POP_ORW
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
QED

(* cf. borelTheory.in_measurable_sigma_pow for measure_space version *)
Theorem in_measurable_sigma_pow' :
    !a sp N f. sigma_algebra a /\
               N SUBSET POW sp /\ f IN (space a -> sp) /\
              (!y. y IN N ==> (PREIMAGE f y) INTER space a IN subsets a) ==>
               f IN measurable a (sigma sp N)
Proof
    RW_TAC std_ss []
 >> MATCH_MP_TAC MEASURABLE_SIGMA
 >> rw [subset_class_def]
 >> fs [SUBSET_DEF, IN_POW]
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

(* cf. borelTheory.in_borel_measurable_imp' for measure_space version

   NOTE: theorem renamed due to name conflicts with HVG's work.
 *)
Theorem in_borel_measurable_open_imp : (* was: in_borel_measurable_open *)
    !a f. sigma_algebra a /\
         (!s. open s ==> (PREIMAGE f s) INTER space a IN subsets a) ==>
          f IN measurable a borel
Proof
    RW_TAC std_ss [borel]
 >> MATCH_MP_TAC in_measurable_sigma_pow'
 >> ASM_SIMP_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> CONJ_TAC >- SET_TAC [POW_DEF]
 >> ASM_SET_TAC []
QED

Theorem in_borel_measurable_continuous_on : (* was: borel_measurable_continuous_on1 *)
    !f. f continuous_on UNIV ==> f IN measurable borel borel
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC in_borel_measurable_open_imp
 >> rw [sigma_algebra_borel]
 >> Know `open {x | x IN UNIV /\ f x IN s}`
 >- (MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE (* key lemma *) \\
     ASM_SIMP_TAC std_ss [OPEN_UNIV])
 >> DISCH_TAC
 >> SIMP_TAC std_ss [PREIMAGE_def, space_borel, INTER_UNIV]
 >> MATCH_MP_TAC borel_open >> fs []
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

(* cf. integrationTheory.INTERVAL_UPPERBOUND for open/closed intervals *)
Theorem right_open_interval_upperbound :
    !a b. a < b ==> interval_upperbound (right_open_interval a b) = b
Proof
    RW_TAC std_ss [interval_upperbound]
 >- (fs [EXTENSION, GSPECIFICATION, in_right_open_interval] \\
     METIS_TAC [REAL_LE_REFL])
 >> RW_TAC std_ss [right_open_interval, GSPECIFICATION,
                   GSYM REAL_LE_ANTISYM]
 >- (MATCH_MP_TAC REAL_IMP_SUP_LE >> rw []
     >- (Q.EXISTS_TAC `a` >> rw [REAL_LE_REFL]) \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art [])
 >> MATCH_MP_TAC REAL_LE_EPSILON
 >> rpt STRIP_TAC
 >> Q.ABBREV_TAC `y = sup {x | a <= x /\ x < b}`
 >> `b <= y + e <=> b - e <= y` by REAL_ARITH_TAC >> POP_ORW
 >> Q.UNABBREV_TAC `y`
 >> MATCH_MP_TAC REAL_IMP_LE_SUP >> rw []
 >- (Q.EXISTS_TAC `b` >> rw [] \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art [])
 >> Cases_on `a <= b - e`
 >- (Q.EXISTS_TAC `b - e` >> rw [REAL_LE_TRANS] \\
     Q.PAT_X_ASSUM `0 < e` MP_TAC >> REAL_ARITH_TAC)
 >> Q.EXISTS_TAC `a` >> rw [REAL_LE_REFL]
 >> MATCH_MP_TAC REAL_LT_IMP_LE >> fs [real_lte]
QED

Theorem right_open_interval_lowerbound :
    !a b. a < b ==> interval_lowerbound (right_open_interval a b) = a
Proof
    RW_TAC std_ss [interval_lowerbound]
 >- (fs [EXTENSION, GSPECIFICATION, in_right_open_interval] \\
     METIS_TAC [REAL_LE_REFL])
 >> RW_TAC std_ss [right_open_interval, GSPECIFICATION]
 >> MATCH_MP_TAC REAL_INF_MIN >> rw []
QED

Theorem right_open_interval_two_bounds :
    !a b. interval_lowerbound (right_open_interval a b) <=
          interval_upperbound (right_open_interval a b)
Proof
    rpt GEN_TAC
 >> Cases_on `a < b`
 >- (rw [right_open_interval_upperbound, right_open_interval_lowerbound] \\
     IMP_RES_TAC REAL_LT_IMP_LE)
 >> fs [GSYM right_open_interval_empty]
 >> rw [interval_lowerbound, interval_upperbound]
QED

Theorem right_open_interval_between_bounds :
    !x a b. x IN right_open_interval a b <=>
            interval_lowerbound (right_open_interval a b) <= x /\
            x < interval_upperbound (right_open_interval a b)
Proof
    rpt GEN_TAC
 >> reverse (Cases_on `a < b`)
 >- (FULL_SIMP_TAC std_ss [GSYM right_open_interval_empty] \\
     rw [NOT_IN_EMPTY, INTERVAL_BOUNDS_EMPTY] \\
     REAL_ARITH_TAC)
 >> rw [in_right_open_interval]
 >> EQ_TAC >> rpt STRIP_TAC (* 4 subgoals *)
 >| [ (* goal 1 (of 4) *)
      fs [right_open_interval_lowerbound],
      (* goal 2 (of 4) *)
      fs [right_open_interval_upperbound],
      (* goal 3 (of 4) *)
      rfs [right_open_interval_lowerbound, right_open_interval_upperbound],
      (* goal 4 (of 4) *)
      rfs [right_open_interval_lowerbound, right_open_interval_upperbound] ]
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

(* ------------------------------------------------------------------------- *)
(*  Two-dimensional Borel sigma-algebra (real version), author: Chun Tian    *)
(* ------------------------------------------------------------------------- *)

(* Theorem 3.8 [1,p.19]: borel_2d can be also generated by open rectangles
   having rational endpoints.

   see open_UNION_rational_box for one-dimension case.
 *)
Theorem borel_2d_lemma1[local] :
    !U. open_in (mtop mr2) U ==>
        U = BIGUNION {J | ?a b c d. a IN q_set /\ b IN q_set /\ c IN q_set /\ d IN q_set /\
                                    J = OPEN_interval (a,b) CROSS OPEN_interval (c,d) /\
                                    J SUBSET U}
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC SUBSET_ANTISYM
 >> reverse CONJ_TAC
 >- (rw [SUBSET_DEF, IN_BIGUNION] \\
     POP_ASSUM MATCH_MP_TAC >> art [])
 (* now the hard part, fix ‘x IN U’ *)
 >> rw [Once SUBSET_DEF]
 >> fs [MTOP_OPEN]
 >> Q.PAT_X_ASSUM ‘!x. U x ==> _’ (MP_TAC o (Q.SPEC ‘x’))
 >> POP_ASSUM (MP_TAC o (REWRITE_RULE [IN_APP]))
 >> RW_TAC std_ss []
 >> Cases_on ‘x’ >> rename1 ‘U (x1,x2)’
 >> MP_TAC (Q.SPECL [‘x2’, ‘e / 2’] rational_boxes)
 >> MP_TAC (Q.SPECL [‘x1’, ‘e / 2’] rational_boxes)
 >> Know ‘0 < e / 2’
 >- (MATCH_MP_TAC REAL_LT_DIV >> rw [])
 >> RW_TAC std_ss []
 >> rename1 ‘x2 IN box c d’
 >> fs [box_alt, ball, dist]
 >> Q.EXISTS_TAC ‘OPEN_interval (a,b) CROSS OPEN_interval (c,d)’
 >> rw [IN_CROSS]
 >> qexistsl_tac [‘a’, ‘b’, ‘c’, ‘d’]
 >> rw [SUBSET_DEF, IN_CROSS]
 >> REWRITE_TAC [IN_APP]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Cases_on ‘x’ >> fs []
 (* stage work *)
 >> MATCH_MP_TAC REAL_LET_TRANS
 >> Q.EXISTS_TAC ‘dist mr2 ((x1,x2),(q,x2)) + dist mr2 ((q,x2),(q,r))’
 >> REWRITE_TAC [METRIC_TRIANGLE]
 >> rw [MR2_DEF]
 >> Know ‘(x1 - q) pow 2 = (abs (x1 - q)) pow 2’
 >- (rw [POW_ABS, ABS_POW2]) >> Rewr'
 >> Know ‘(x2 - r) pow 2 = (abs (x2 - r)) pow 2’
 >- (rw [POW_ABS, ABS_POW2]) >> Rewr'
 >> Know ‘sqrt (abs (x1 - q) pow 2) = abs (x1 - q)’
 >- (MATCH_MP_TAC POW_2_SQRT \\
     REWRITE_TAC [ABS_POS]) >> Rewr'
 >> Know ‘sqrt (abs (x2 - r) pow 2) = abs (x2 - r)’
 >- (MATCH_MP_TAC POW_2_SQRT \\
     REWRITE_TAC [ABS_POS]) >> Rewr'
 >> ‘e = e / 2 + e / 2’ by REWRITE_TAC [REAL_HALF_DOUBLE] >> POP_ORW
 >> MATCH_MP_TAC REAL_LT_ADD2
 >> CONJ_TAC (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      Q.PAT_X_ASSUM ‘interval (a,b) SUBSET _’ MP_TAC \\
      Q.PAT_X_ASSUM ‘q IN interval (a,b)’ MP_TAC,
      (* goal 2 (of 2) *)
      Q.PAT_X_ASSUM ‘interval (c,d) SUBSET _’ MP_TAC \\
      Q.PAT_X_ASSUM ‘r IN interval (c,d)’ MP_TAC ]
 >> rw [SUBSET_DEF, IN_INTERVAL]
QED

Theorem IMAGE_FST_CROSS_INTERVAL :
    !a b c d. c < d ==> IMAGE FST (interval (a,b) CROSS interval (c,d)) = interval (a,b)
Proof
    rw [Once EXTENSION, IN_INTERVAL]
 >> EQ_TAC >> rw [] >> art []
 >> MP_TAC (Q.SPECL [‘c’, ‘d’] REAL_MEAN)
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC ‘(x,z)’
 >> RW_TAC std_ss []
QED

Theorem IMAGE_SND_CROSS_INTERVAL :
    !a b c d. a < b ==> IMAGE SND (interval (a,b) CROSS interval (c,d)) = interval (c,d)
Proof
    rw [Once EXTENSION, IN_INTERVAL]
 >> EQ_TAC >> rw [] >> art []
 >> MP_TAC (Q.SPECL [‘a’, ‘b’] REAL_MEAN)
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC ‘(z,x)’
 >> RW_TAC std_ss []
QED

(* This proof needs advanced results from cardinalTheory *)
Theorem borel_2d_lemma2[local] :
    !U. COUNTABLE {J | ?a b c d. a IN q_set /\ b IN q_set /\ c IN q_set /\ d IN q_set /\
                                 J = OPEN_interval (a,b) CROSS OPEN_interval (c,d) /\
                                 J SUBSET U}
Proof
    GEN_TAC
 >> MATCH_MP_TAC (INST_TYPE [“:'b” |-> “:real # real # real # real”]
                            CARD_LE_COUNTABLE)
 >> Q.EXISTS_TAC ‘q_set CROSS (q_set CROSS (q_set CROSS q_set))’
 >> CONJ_TAC >- PROVE_TAC [COUNTABLE_CROSS, QSET_COUNTABLE]
 >> rw [cardleq_def]
 >> Q.EXISTS_TAC ‘\s. if s = {} then (0,0,0,0)
                      else (interval_lowerbound (IMAGE FST s),
                            interval_upperbound (IMAGE FST s),
                            interval_lowerbound (IMAGE SND s),
                            interval_upperbound (IMAGE SND s))’
 >> rw [INJ_DEF] (* 5 subgoals *)
 >| [ (* goal 1 (of 5) *)
      reverse (Cases_on ‘a < b’)
      >- (fs [GSYM real_lte, INTERVAL_EQ_EMPTY] \\
          rw [real_of_num, NUM_IN_QSET]) \\
      reverse (Cases_on ‘c < d’)
      >- (fs [GSYM real_lte, INTERVAL_EQ_EMPTY] \\
          rw [real_of_num, NUM_IN_QSET]) \\
     ‘interval (a,b) <> {} /\ interval (c,d) <> {}’
        by PROVE_TAC [GSYM real_lte, INTERVAL_EQ_EMPTY] \\
      Know ‘interval (a,b) CROSS interval (c,d) <> {}’
      >- (CCONTR_TAC >> rfs [CROSS_EMPTY_EQN]) \\
      RW_TAC std_ss [] \\
      Know ‘IMAGE FST (interval (a,b) CROSS interval (c,d)) = interval (a,b)’
      >- (MATCH_MP_TAC IMAGE_FST_CROSS_INTERVAL >> art []) >> Rewr' \\
      Suff ‘interval_lowerbound (interval (a,b)) = a’ >- rw [] \\
      MATCH_MP_TAC OPEN_INTERVAL_LOWERBOUND >> art [],
      (* goal 2 (of 5) *)
      reverse (Cases_on ‘a < b’)
      >- (fs [GSYM real_lte, INTERVAL_EQ_EMPTY] \\
          rw [real_of_num, NUM_IN_QSET]) \\
      reverse (Cases_on ‘c < d’)
      >- (fs [GSYM real_lte, INTERVAL_EQ_EMPTY] \\
          rw [real_of_num, NUM_IN_QSET]) \\
     ‘interval (a,b) <> {} /\ interval (c,d) <> {}’
        by PROVE_TAC [GSYM real_lte, INTERVAL_EQ_EMPTY] \\
      Know ‘interval (a,b) CROSS interval (c,d) <> {}’
      >- (CCONTR_TAC >> rfs [CROSS_EMPTY_EQN]) \\
      RW_TAC std_ss [] \\
      Know ‘IMAGE FST (interval (a,b) CROSS interval (c,d)) = interval (a,b)’
      >- (MATCH_MP_TAC IMAGE_FST_CROSS_INTERVAL >> art []) >> Rewr' \\
      Suff ‘interval_upperbound (interval (a,b)) = b’ >- rw [] \\
      MATCH_MP_TAC OPEN_INTERVAL_UPPERBOUND >> art [],
      (* goal 3 (of 5) *)
      reverse (Cases_on ‘a < b’)
      >- (fs [GSYM real_lte, INTERVAL_EQ_EMPTY] \\
          rw [real_of_num, NUM_IN_QSET]) \\
      reverse (Cases_on ‘c < d’)
      >- (fs [GSYM real_lte, INTERVAL_EQ_EMPTY] \\
          rw [real_of_num, NUM_IN_QSET]) \\
     ‘interval (a,b) <> {} /\ interval (c,d) <> {}’
        by PROVE_TAC [GSYM real_lte, INTERVAL_EQ_EMPTY] \\
      Know ‘interval (a,b) CROSS interval (c,d) <> {}’
      >- (CCONTR_TAC >> rfs [CROSS_EMPTY_EQN]) \\
      RW_TAC std_ss [] \\
      Know ‘IMAGE SND (interval (a,b) CROSS interval (c,d)) = interval (c,d)’
      >- (MATCH_MP_TAC IMAGE_SND_CROSS_INTERVAL >> art []) >> Rewr' \\
      Suff ‘interval_lowerbound (interval (c,d)) = c’ >- rw [] \\
      MATCH_MP_TAC OPEN_INTERVAL_LOWERBOUND >> art [],
      (* goal 4 (of 5) *)
      reverse (Cases_on ‘a < b’)
      >- (fs [GSYM real_lte, INTERVAL_EQ_EMPTY] \\
          rw [real_of_num, NUM_IN_QSET]) \\
      reverse (Cases_on ‘c < d’)
      >- (fs [GSYM real_lte, INTERVAL_EQ_EMPTY] \\
          rw [real_of_num, NUM_IN_QSET]) \\
     ‘interval (a,b) <> {} /\ interval (c,d) <> {}’
        by PROVE_TAC [GSYM real_lte, INTERVAL_EQ_EMPTY] \\
      Know ‘interval (a,b) CROSS interval (c,d) <> {}’
      >- (CCONTR_TAC >> rfs [CROSS_EMPTY_EQN]) \\
      RW_TAC std_ss [] \\
      Know ‘IMAGE SND (interval (a,b) CROSS interval (c,d)) = interval (c,d)’
      >- (MATCH_MP_TAC IMAGE_SND_CROSS_INTERVAL >> art []) >> Rewr' \\
      Suff ‘interval_upperbound (interval (c,d)) = d’ >- rw [] \\
      MATCH_MP_TAC OPEN_INTERVAL_UPPERBOUND >> art [],
      (* goal 5 (of 5) *)
      reverse (Cases_on ‘a < b’)
      >- (fs [GSYM real_lte, INTERVAL_EQ_EMPTY] \\
          reverse (Cases_on ‘a' < b'’)
          >- (fs [GSYM real_lte, INTERVAL_EQ_EMPTY]) \\
          reverse (Cases_on ‘c' < d'’)
          >- (fs [GSYM real_lte, INTERVAL_EQ_EMPTY]) \\
         ‘interval (a',b') <> {} /\ interval (c',d') <> {}’
            by PROVE_TAC [GSYM real_lte, INTERVAL_EQ_EMPTY] \\
          Know ‘interval (a',b') CROSS interval (c',d') <> {}’
          >- (CCONTR_TAC >> rfs [CROSS_EMPTY_EQN]) \\
          DISCH_THEN (fs o wrap) \\
          Know ‘IMAGE FST (interval (a',b') CROSS interval (c',d')) = interval (a',b')’
          >- (MATCH_MP_TAC IMAGE_FST_CROSS_INTERVAL >> art []) \\
          DISCH_THEN (fs o wrap) \\
          Know ‘IMAGE SND (interval (a',b') CROSS interval (c',d')) = interval (c',d')’
          >- (MATCH_MP_TAC IMAGE_SND_CROSS_INTERVAL >> art []) \\
          DISCH_THEN (fs o wrap) \\
          Know ‘interval_lowerbound (interval (a',b')) = a'’
          >- (MATCH_MP_TAC OPEN_INTERVAL_LOWERBOUND >> art []) \\
          DISCH_THEN (fs o wrap) \\
          Know ‘interval_upperbound (interval (a',b')) = b'’
          >- (MATCH_MP_TAC OPEN_INTERVAL_UPPERBOUND >> art []) \\
          DISCH_THEN (fs o wrap) \\
          rfs [REAL_LT_REFL]) \\
      reverse (Cases_on ‘c < d’)
      >- (fs [GSYM real_lte] \\
         ‘interval (c,d) = {}’ by PROVE_TAC [INTERVAL_EQ_EMPTY] >> fs [] \\
          reverse (Cases_on ‘a' < b'’)
          >- (fs [GSYM real_lte, INTERVAL_EQ_EMPTY]) \\
          reverse (Cases_on ‘c' < d'’)
          >- (fs [GSYM real_lte, INTERVAL_EQ_EMPTY]) \\
         ‘interval (a',b') <> {} /\ interval (c',d') <> {}’
            by PROVE_TAC [GSYM real_lte, INTERVAL_EQ_EMPTY] \\
          Know ‘interval (a',b') CROSS interval (c',d') <> {}’
          >- (CCONTR_TAC >> rfs [CROSS_EMPTY_EQN]) \\
          DISCH_THEN (fs o wrap) \\
          Know ‘IMAGE FST (interval (a',b') CROSS interval (c',d')) = interval (a',b')’
          >- (MATCH_MP_TAC IMAGE_FST_CROSS_INTERVAL >> art []) \\
          DISCH_THEN (fs o wrap) \\
          Know ‘IMAGE SND (interval (a',b') CROSS interval (c',d')) = interval (c',d')’
          >- (MATCH_MP_TAC IMAGE_SND_CROSS_INTERVAL >> art []) \\
          DISCH_THEN (fs o wrap) \\
          Know ‘interval_lowerbound (interval (a',b')) = a'’
          >- (MATCH_MP_TAC OPEN_INTERVAL_LOWERBOUND >> art []) \\
          DISCH_THEN (fs o wrap) \\
          Know ‘interval_upperbound (interval (a',b')) = b'’
          >- (MATCH_MP_TAC OPEN_INTERVAL_UPPERBOUND >> art []) \\
          DISCH_THEN (fs o wrap) \\
          rfs [REAL_LT_REFL]) \\
     ‘interval (a,b) <> {} /\ interval (c,d) <> {}’
        by PROVE_TAC [GSYM real_lte, INTERVAL_EQ_EMPTY] \\
      Know ‘interval (a,b) CROSS interval (c,d) <> {}’
      >- (CCONTR_TAC >> rfs [CROSS_EMPTY_EQN]) \\
      DISCH_THEN (fs o wrap) \\
      reverse (Cases_on ‘a' < b'’)
      >- (fs [GSYM real_lte] \\
         ‘interval (a',b') = {}’ by PROVE_TAC [INTERVAL_EQ_EMPTY] >> fs [] \\
          Know ‘IMAGE FST (interval (a,b) CROSS interval (c,d)) = interval (a,b)’
          >- (MATCH_MP_TAC IMAGE_FST_CROSS_INTERVAL >> art []) \\
          DISCH_THEN (fs o wrap) \\
          Know ‘IMAGE SND (interval (a,b) CROSS interval (c,d)) = interval (c,d)’
          >- (MATCH_MP_TAC IMAGE_SND_CROSS_INTERVAL >> art []) \\
          DISCH_THEN (fs o wrap) \\
          Know ‘interval_lowerbound (interval (a,b)) = a’
          >- (MATCH_MP_TAC OPEN_INTERVAL_LOWERBOUND >> art []) \\
          DISCH_THEN (fs o wrap) \\
          Know ‘interval_upperbound (interval (a,b)) = b’
          >- (MATCH_MP_TAC OPEN_INTERVAL_UPPERBOUND >> art []) \\
          DISCH_THEN (fs o wrap) \\
          rfs [REAL_LT_REFL]) \\
      reverse (Cases_on ‘c' < d'’)
      >- (fs [GSYM real_lte] \\
         ‘interval (c',d') = {}’ by PROVE_TAC [INTERVAL_EQ_EMPTY] >> fs [] \\
          Know ‘IMAGE FST (interval (a,b) CROSS interval (c,d)) = interval (a,b)’
          >- (MATCH_MP_TAC IMAGE_FST_CROSS_INTERVAL >> art []) \\
          DISCH_THEN (fs o wrap) \\
          Know ‘IMAGE SND (interval (a,b) CROSS interval (c,d)) = interval (c,d)’
          >- (MATCH_MP_TAC IMAGE_SND_CROSS_INTERVAL >> art []) \\
          DISCH_THEN (fs o wrap) \\
          Know ‘interval_lowerbound (interval (a,b)) = a’
          >- (MATCH_MP_TAC OPEN_INTERVAL_LOWERBOUND >> art []) \\
          DISCH_THEN (fs o wrap) \\
          Know ‘interval_upperbound (interval (a,b)) = b’
          >- (MATCH_MP_TAC OPEN_INTERVAL_UPPERBOUND >> art []) \\
          DISCH_THEN (fs o wrap) \\
          rfs [REAL_LT_REFL]) \\
     ‘interval (a',b') <> {} /\ interval (c',d') <> {}’
        by PROVE_TAC [GSYM real_lte, INTERVAL_EQ_EMPTY] \\
      Know ‘interval (a',b') CROSS interval (c',d') <> {}’
      >- (CCONTR_TAC >> rfs [CROSS_EMPTY_EQN]) \\
      DISCH_THEN (fs o wrap) \\
      Know ‘IMAGE FST (interval (a,b) CROSS interval (c,d)) = interval (a,b)’
      >- (MATCH_MP_TAC IMAGE_FST_CROSS_INTERVAL >> art []) \\
      DISCH_THEN (fs o wrap) \\
      Know ‘IMAGE SND (interval (a,b) CROSS interval (c,d)) = interval (c,d)’
      >- (MATCH_MP_TAC IMAGE_SND_CROSS_INTERVAL >> art []) \\
      DISCH_THEN (fs o wrap) \\
      Know ‘IMAGE FST (interval (a',b') CROSS interval (c',d')) = interval (a',b')’
      >- (MATCH_MP_TAC IMAGE_FST_CROSS_INTERVAL >> art []) \\
      DISCH_THEN (fs o wrap) \\
      Know ‘IMAGE SND (interval (a',b') CROSS interval (c',d')) = interval (c',d')’
      >- (MATCH_MP_TAC IMAGE_SND_CROSS_INTERVAL >> art []) \\
      DISCH_THEN (fs o wrap) \\
      Know ‘interval_lowerbound (interval (a,b)) = a’
      >- (MATCH_MP_TAC OPEN_INTERVAL_LOWERBOUND >> art []) \\
      DISCH_THEN (fs o wrap) \\
      Know ‘interval_upperbound (interval (a,b)) = b’
      >- (MATCH_MP_TAC OPEN_INTERVAL_UPPERBOUND >> art []) \\
      DISCH_THEN (fs o wrap) \\
      Know ‘interval_lowerbound (interval (a',b')) = a'’
      >- (MATCH_MP_TAC OPEN_INTERVAL_LOWERBOUND >> art []) \\
      DISCH_THEN (fs o wrap) \\
      Know ‘interval_upperbound (interval (a',b')) = b'’
      >- (MATCH_MP_TAC OPEN_INTERVAL_UPPERBOUND >> art []) \\
      DISCH_THEN (fs o wrap) \\
      Know ‘interval_lowerbound (interval (c,d)) = c’
      >- (MATCH_MP_TAC OPEN_INTERVAL_LOWERBOUND >> art []) \\
      DISCH_THEN (fs o wrap) \\
      Know ‘interval_upperbound (interval (c,d)) = d’
      >- (MATCH_MP_TAC OPEN_INTERVAL_UPPERBOUND >> art []) \\
      DISCH_THEN (fs o wrap) \\
      Know ‘interval_lowerbound (interval (c',d')) = c'’
      >- (MATCH_MP_TAC OPEN_INTERVAL_LOWERBOUND >> art []) \\
      DISCH_THEN (fs o wrap) \\
      Know ‘interval_upperbound (interval (c',d')) = d'’
      >- (MATCH_MP_TAC OPEN_INTERVAL_UPPERBOUND >> art []) \\
      DISCH_THEN (fs o wrap) ]
QED

Theorem POW_2_SUB[local] :
    !x y. (x - y) pow 2 = (y - x) pow 2
Proof
    rpt GEN_TAC
 >> ‘(x - y) pow 2 = (abs (x - y)) pow 2’ by PROVE_TAC [REAL_POW2_ABS] >> POP_ORW
 >> ‘(y - x) pow 2 = (abs (y - x)) pow 2’ by PROVE_TAC [REAL_POW2_ABS] >> POP_ORW
 >> REWRITE_TAC [Once ABS_SUB]
QED

Theorem box_open_in_mr2 :
    !a b c d. open_in (mtop mr2) (interval (a,b) CROSS interval (c,d))
Proof
    rw [MTOP_OPEN]
 >> Cases_on ‘x’ >> fs []
 (* open_in (mtop mr2) (interval (a,b) CROSS interval (c,d)) *)
 >> reverse (Cases_on ‘a < b’)
 >- (‘interval (a,b) = {}’ by METIS_TAC [real_lte, INTERVAL_EQ_EMPTY] \\
     FULL_SIMP_TAC std_ss [NOT_IN_EMPTY])
 >> reverse (Cases_on ‘c < d’)
 >- (‘interval (c,d) = {}’ by METIS_TAC [real_lte, INTERVAL_EQ_EMPTY] \\
     FULL_SIMP_TAC std_ss [NOT_IN_EMPTY])
 (* stage work *)
 >> Q.ABBREV_TAC ‘dx = min (q - a) (b - q)’
 >> Q.ABBREV_TAC ‘dy = min (r - c) (d - r)’
 >> Q.EXISTS_TAC ‘min dx dy’
 >> STRONG_CONJ_TAC
 >- (rw [Abbr ‘dx’, Abbr ‘dy’, REAL_LT_MIN, REAL_SUB_LT] \\
     fs [IN_INTERVAL])
 >> DISCH_TAC
 >> GEN_TAC
 >> Cases_on ‘y’
 >> rw [REAL_LT_MIN, IN_INTERVAL] (* 4 subgoals *)
 >> rename1 ‘dist mr2 ((x0,y0),(x1,y1)) < dx’
 >| [ (* goal 1 (of 4) *)
      CCONTR_TAC >> fs [GSYM real_lte] \\
      Know ‘dist mr2 ((x0,y0),(x1,y0)) <= dist mr2 ((x0,y0),(x1,y1))’
      >- (rw [MR2_DEF] \\
          MATCH_MP_TAC SQRT_MONO_LE >> rw [REAL_LE_POW2]) >> DISCH_TAC \\
      Know ‘dist mr2 ((x0,y0),(x1,y0)) < dx’
      >- (MATCH_MP_TAC REAL_LET_TRANS \\
          Q.EXISTS_TAC ‘dist mr2 ((x0,y0),(x1,y1))’ >> art []) \\
      rw [Abbr ‘dx’, REAL_LT_MIN, MR2_DEF] \\
      DISJ1_TAC >> rw [GSYM real_lte] \\
      Cases_on ‘0 <= x0 - x1’
      >- (Know ‘sqrt ((x0 - x1) pow 2) = x0 - x1’
          >- (MATCH_MP_TAC POW_2_SQRT >> art []) >> Rewr' \\
          Q.PAT_X_ASSUM ‘x1 <= a’ MP_TAC \\
          REAL_ARITH_TAC) \\
      POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [real_lte])) \\
      Know ‘x0 < 0 + x1’
      >- (rw [GSYM REAL_LT_SUB_RADD]) >> rw [] \\
      Know ‘x0 < a’
      >- (MATCH_MP_TAC REAL_LTE_TRANS \\
          Q.EXISTS_TAC ‘x1’ >> art []) >> DISCH_TAC \\
      Q.PAT_X_ASSUM ‘x0 IN interval (a,b)’
        (STRIP_ASSUME_TAC o (REWRITE_RULE [IN_INTERVAL])) \\
      PROVE_TAC [REAL_LT_ANTISYM],
      (* goal 2 (of 4) *)
      CCONTR_TAC >> fs [GSYM real_lte] \\
      Know ‘dist mr2 ((x0,y0),(x1,y0)) <= dist mr2 ((x0,y0),(x1,y1))’
      >- (rw [MR2_DEF] \\
          MATCH_MP_TAC SQRT_MONO_LE >> rw [REAL_LE_POW2]) >> DISCH_TAC \\
      Know ‘dist mr2 ((x0,y0),(x1,y0)) < dx’
      >- (MATCH_MP_TAC REAL_LET_TRANS \\
          Q.EXISTS_TAC ‘dist mr2 ((x0,y0),(x1,y1))’ >> art []) \\
      rw [Abbr ‘dx’, REAL_LT_MIN, MR2_DEF] \\
      DISJ2_TAC >> rw [GSYM real_lte] \\
      ONCE_REWRITE_TAC [POW_2_SUB] \\
      Cases_on ‘0 <= x1 - x0’
      >- (Know ‘sqrt ((x1 - x0) pow 2) = x1 - x0’
          >- (MATCH_MP_TAC POW_2_SQRT >> art []) >> Rewr' \\
          ASM_REWRITE_TAC [REAL_LE_SUB_CANCEL2]) \\
      POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [real_lte])) \\
      Know ‘x1 < 0 + x0’
      >- (rw [GSYM REAL_LT_SUB_RADD]) >> rw [] \\
      Know ‘b < x0’
      >- (MATCH_MP_TAC REAL_LET_TRANS \\
          Q.EXISTS_TAC ‘x1’ >> art []) >> DISCH_TAC \\
      Q.PAT_X_ASSUM ‘x0 IN interval (a,b)’
        (STRIP_ASSUME_TAC o (REWRITE_RULE [IN_INTERVAL])) \\
      PROVE_TAC [REAL_LT_ANTISYM],
      (* goal 3 (of 4) *)
      CCONTR_TAC >> fs [GSYM real_lte] \\
      Know ‘dist mr2 ((x0,y0),(x0,y1)) <= dist mr2 ((x0,y0),(x1,y1))’
      >- (rw [MR2_DEF] \\
          MATCH_MP_TAC SQRT_MONO_LE >> rw [REAL_LE_POW2]) >> DISCH_TAC \\
      Know ‘dist mr2 ((x0,y0),(x0,y1)) < dy’
      >- (MATCH_MP_TAC REAL_LET_TRANS \\
          Q.EXISTS_TAC ‘dist mr2 ((x0,y0),(x1,y1))’ >> art []) \\
      rw [Abbr ‘dy’, REAL_LT_MIN, MR2_DEF] \\
      DISJ1_TAC >> rw [GSYM real_lte] \\
      Cases_on ‘0 <= y0 - y1’
      >- (Know ‘sqrt ((y0 - y1) pow 2) = y0 - y1’
          >- (MATCH_MP_TAC POW_2_SQRT >> art []) >> Rewr' \\
          Q.PAT_X_ASSUM ‘y1 <= c’ MP_TAC \\
          REAL_ARITH_TAC) \\
      POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [real_lte])) \\
      Know ‘y0 < 0 + y1’
      >- (rw [GSYM REAL_LT_SUB_RADD]) >> rw [] \\
      Know ‘y0 < c’
      >- (MATCH_MP_TAC REAL_LTE_TRANS \\
          Q.EXISTS_TAC ‘y1’ >> art []) >> DISCH_TAC \\
      Q.PAT_X_ASSUM ‘y0 IN interval (c,d)’
        (STRIP_ASSUME_TAC o (REWRITE_RULE [IN_INTERVAL])) \\
      PROVE_TAC [REAL_LT_ANTISYM],
      (* goal 4 (of 4) *)
      CCONTR_TAC >> fs [GSYM real_lte] \\
      Know ‘dist mr2 ((x0,y0),(x0,y1)) <= dist mr2 ((x0,y0),(x1,y1))’
      >- (rw [MR2_DEF] \\
          MATCH_MP_TAC SQRT_MONO_LE >> rw [REAL_LE_POW2]) >> DISCH_TAC \\
      Know ‘dist mr2 ((x0,y0),(x0,y1)) < dy’
      >- (MATCH_MP_TAC REAL_LET_TRANS \\
          Q.EXISTS_TAC ‘dist mr2 ((x0,y0),(x1,y1))’ >> art []) \\
      rw [Abbr ‘dy’, REAL_LT_MIN, MR2_DEF] \\
      DISJ2_TAC >> rw [GSYM real_lte] \\
      ONCE_REWRITE_TAC [POW_2_SUB] \\
      Cases_on ‘0 <= y1 - y0’
      >- (Know ‘sqrt ((y1 - y0) pow 2) = y1 - y0’
          >- (MATCH_MP_TAC POW_2_SQRT >> art []) >> Rewr' \\
          ASM_REWRITE_TAC [REAL_LE_SUB_CANCEL2]) \\
      POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [real_lte])) \\
      Know ‘y1 < 0 + y0’
      >- (rw [GSYM REAL_LT_SUB_RADD]) >> rw [] \\
      Know ‘d < y0’
      >- (MATCH_MP_TAC REAL_LET_TRANS \\
          Q.EXISTS_TAC ‘y1’ >> art []) >> DISCH_TAC \\
      Q.PAT_X_ASSUM ‘y0 IN interval (c,d)’
        (STRIP_ASSUME_TAC o (REWRITE_RULE [IN_INTERVAL])) \\
      PROVE_TAC [REAL_LT_ANTISYM] ]
QED

Theorem borel_2d_lemma3[local] :
    sigma UNIV {s | open_in (mtop mr2) s} =
    sigma UNIV {J | ?a b c d. a IN q_set /\ b IN q_set /\ c IN q_set /\ d IN q_set /\
                              J = OPEN_interval (a,b) CROSS OPEN_interval (c,d)}
Proof
    Q.ABBREV_TAC ‘S1 = sigma UNIV {s | open_in (mtop mr2) s}’
 >> Q.ABBREV_TAC
     ‘S3 = sigma UNIV {J | ?a b c d. a IN q_set /\ b IN q_set /\ c IN q_set /\ d IN q_set /\
                                     J = OPEN_interval (a,b) CROSS OPEN_interval (c,d)}’
 >> Suff ‘subsets S1 = subsets S3’ >- METIS_TAC [SIGMA_CONG]
 >> MATCH_MP_TAC SUBSET_ANTISYM
 >> reverse CONJ_TAC
 >- (qunabbrevl_tac [‘S1’, ‘S3’] \\
     MATCH_MP_TAC SIGMA_MONOTONE \\
     rw [Once SUBSET_DEF] \\
     REWRITE_TAC [box_open_in_mr2])
 (* subsets S1 SUBSET subsets S3 *)
 >> Q.UNABBREV_TAC ‘S1’
 >> ‘univ(:real # real) = space S3’ by METIS_TAC [SPACE_SIGMA] >> POP_ORW
 >> MATCH_MP_TAC SIGMA_SUBSET
 >> Know ‘sigma_algebra S3’
 >- (Q.UNABBREV_TAC ‘S3’ \\
     MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA >> rw [subset_class_def])
 >> rw [SUBSET_DEF]
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o (MATCH_MP borel_2d_lemma1))
 >> MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION >> art [borel_2d_lemma2]
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘{J | ?a b c d. a IN q_set /\ b IN q_set /\ c IN q_set /\ d IN q_set /\
                                 J = OPEN_interval (a,b) CROSS OPEN_interval (c,d)}’
 >> reverse CONJ_TAC >- rw [Abbr ‘S3’, SIGMA_SUBSET_SUBSETS]
 >> rw [SUBSET_DEF]
 >> qexistsl_tac [‘a’, ‘b’, ‘c’, ‘d’] >> rw []
QED

(* now rationals are all removed *)
Theorem borel_2d_lemma4[local] :
    sigma UNIV {s | open_in (mtop mr2) s} =
    sigma UNIV {J | ?a b c d. J = OPEN_interval (a,b) CROSS OPEN_interval (c,d)}
Proof
    Q.ABBREV_TAC ‘S1 = sigma UNIV {s | open_in (mtop mr2) s}’
 >> Q.ABBREV_TAC
     ‘S2 = sigma UNIV {J | ?a b c d. J = OPEN_interval (a,b) CROSS OPEN_interval (c,d)}’
 >> Q.ABBREV_TAC
     ‘S3 = sigma UNIV {J | ?a b c d. a IN q_set /\ b IN q_set /\ c IN q_set /\ d IN q_set /\
                                     J = OPEN_interval (a,b) CROSS OPEN_interval (c,d)}’
 >> Suff ‘subsets S1 = subsets S2’ >- METIS_TAC [SIGMA_CONG]
 >> MATCH_MP_TAC SUBSET_ANTISYM
 >> reverse CONJ_TAC
 >- (qunabbrevl_tac [‘S1’, ‘S2’] \\
     MATCH_MP_TAC SIGMA_MONOTONE \\
     rw [Once SUBSET_DEF] \\
     REWRITE_TAC [box_open_in_mr2])
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘subsets S3’
 >> reverse CONJ_TAC
 >- (qunabbrevl_tac [‘S2’, ‘S3’] \\
     MATCH_MP_TAC SIGMA_MONOTONE \\
     rw [Once SUBSET_DEF] \\
     qexistsl_tac [‘a’, ‘b’, ‘c’, ‘d’] >> REWRITE_TAC [])
 >> ‘S1 = S3’ by METIS_TAC [borel_2d_lemma3] >> POP_ORW
 >> qunabbrevl_tac [‘S2’, ‘S3’]
 >> MATCH_MP_TAC SIGMA_MONOTONE
 >> rw [Once SUBSET_DEF]
 >> qexistsl_tac [‘a’, ‘b’, ‘c’, ‘d’] >> REWRITE_TAC []
QED

Theorem sigma_algebra_borel_2d :
    sigma_algebra (borel CROSS borel)
Proof
    MATCH_MP_TAC SIGMA_ALGEBRA_PROD_SIGMA
 >> rw [subset_class_def, space_borel]
QED

(* 2D borel sets can be also generated by open sets in MR2 *)
Theorem borel_2d :
    borel CROSS borel = sigma UNIV {s | open_in (mtop mr2) s}
Proof
    Suff ‘subsets (borel CROSS borel) =
          subsets (sigma UNIV {s | open_in (mtop mr2) s})’
 >- (rw [prod_sigma_def, SPACE_SIGMA, GSYM CROSS_UNIV, space_borel] \\
     MATCH_MP_TAC SIGMA_CONG >> art [])
 >> MATCH_MP_TAC SUBSET_ANTISYM
 >> reverse CONJ_TAC
 >- (rw [borel_2d_lemma4] \\
     Know ‘univ(:real # real) = space (borel CROSS borel)’
     >- (rw [SPACE_PROD_SIGMA, CROSS_UNIV, space_borel]) >> Rewr' \\
     MATCH_MP_TAC SIGMA_SUBSET \\
     REWRITE_TAC [sigma_algebra_borel_2d, prod_sigma_def] \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘prod_sets (subsets borel) (subsets borel)’ \\
     REWRITE_TAC [SIGMA_SUBSET_SUBSETS] \\
     rw [SUBSET_DEF, IN_PROD_SETS] \\
     qexistsl_tac [‘interval (a,b)’, ‘interval (c,d)’] \\
     rw [OPEN_interval, borel_measurable_sets_gr_less])
 (* applying prod_sigma_alt_sigma_functions *)
 >> Know ‘borel CROSS borel =
          sigma (space borel CROSS space borel) (binary borel borel) (binary FST SND) {0; 1}’
 >- (MATCH_MP_TAC prod_sigma_alt_sigma_functions \\
     REWRITE_TAC [sigma_algebra_borel])
 >> Rewr'
 >> rw [sigma_functions_def, binary_def, space_borel, GSYM CROSS_UNIV]
 >> Q.ABBREV_TAC ‘B = sigma univ(:real # real) {s | open_in (mtop mr2) s}’
 >> ‘univ(:real # real) = space B’ by PROVE_TAC [SPACE_SIGMA] >> POP_ORW
 >> MATCH_MP_TAC SIGMA_SUBSET
 >> Q.UNABBREV_TAC ‘B’
 >> CONJ_TAC
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
     rw [subset_class_def])
 >> rw [SUBSET_DEF] >> rename1 ‘s IN subsets borel’
 >| [ (* goal 1 (of 2) *)
      Suff ‘IMAGE (\s. PREIMAGE FST s) (subsets borel) SUBSET
            subsets (sigma univ(:real # real) {s | open_in (mtop mr2) s})’
      >- (rw [SUBSET_DEF] >> POP_ASSUM MATCH_MP_TAC \\
          Q.EXISTS_TAC ‘s’ >> art []) \\
      KILL_TAC \\
      REWRITE_TAC [borel_eq_gr_less] \\
      Q.ABBREV_TAC ‘sts = IMAGE (\(a,b). {x | a < x /\ x < b}) univ(:real # real)’ \\
      Q.ABBREV_TAC ‘Z = univ(:real # real)’ \\
      Know ‘IMAGE (\s. PREIMAGE FST s INTER Z) (subsets (sigma UNIV sts)) =
            subsets (sigma Z (IMAGE (\s. PREIMAGE FST s INTER Z) sts))’
      >- (MATCH_MP_TAC PREIMAGE_SIGMA >> rw [subset_class_def, IN_FUNSET]) \\
      simp [Abbr ‘Z’] >> Rewr' \\
      Q.ABBREV_TAC ‘B = sigma univ(:real # real) {s | open_in (mtop mr2) s}’ \\
     ‘univ(:real # real) = space B’ by PROVE_TAC [SPACE_SIGMA] >> POP_ORW \\
      MATCH_MP_TAC SIGMA_SUBSET \\
      Q.UNABBREV_TAC ‘B’ \\
      CONJ_TAC >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA >> rw [subset_class_def]) \\
      MATCH_MP_TAC SUBSET_TRANS \\
      Q.EXISTS_TAC ‘{s | open_in (mtop mr2) s}’ >> rw [SIGMA_SUBSET_SUBSETS] \\
      simp [Abbr ‘sts’, SUBSET_DEF] \\
      Q.X_GEN_TAC ‘y’ >> rw [] \\
      Cases_on ‘x’ >> simp [] \\
      Know ‘PREIMAGE FST {x | q < x /\ x < r} = {x | q < x /\ x < r} CROSS univ(:real)’
      >- (rw [Once EXTENSION, IN_PREIMAGE, IN_CROSS]) >> Rewr' \\
      rw [MTOP_OPEN] \\
      Cases_on ‘x’ >> rename1 ‘q < FST (x,y)’ >> fs [] \\
      Q.ABBREV_TAC ‘dx = min (x - q) (r - x)’ \\
      Q.EXISTS_TAC ‘dx’ \\
      CONJ_TAC >- (rw [Abbr ‘dx’, REAL_LT_MIN, REAL_SUB_LT]) \\
      Q.X_GEN_TAC ‘z’ >> Cases_on ‘z’ >> simp [] \\
      DISCH_TAC >> rename1 ‘dist mr2 ((x0,y0),(x1,y1)) < dx’ \\
      Know ‘dist mr2 ((x0,y0),(x1,y0)) <= dist mr2 ((x0,y0),(x1,y1))’
      >- (rw [MR2_DEF] \\
          MATCH_MP_TAC SQRT_MONO_LE >> rw [REAL_LE_POW2]) >> DISCH_TAC \\
      Know ‘dist mr2 ((x0,y0),(x1,y0)) < dx’
      >- (MATCH_MP_TAC REAL_LET_TRANS \\
          Q.EXISTS_TAC ‘dist mr2 ((x0,y0),(x1,y1))’ >> art []) \\
      rw [Abbr ‘dx’, REAL_LT_MIN, MR2_DEF] >| (* 2 subgoals *)
      [ (* goal 1.1 (of 2) *)
        Cases_on ‘0 <= x0 - x1’
        >- (Know ‘sqrt ((x0 - x1) pow 2) = x0 - x1’
            >- (MATCH_MP_TAC POW_2_SQRT >> art []) >> DISCH_THEN (fs o wrap) \\
            Q.PAT_X_ASSUM ‘x0 - x1 < x0 - q’ MP_TAC \\
            REAL_ARITH_TAC) \\
        POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [real_lte])) \\
        Know ‘x0 < 0 + x1’
        >- (rw [GSYM REAL_LT_SUB_RADD]) >> rw [] \\
        MATCH_MP_TAC REAL_LT_TRANS \\
        Q.EXISTS_TAC ‘x0’ >> art [],
        (* goal 1.2 (of 2) *)
       ‘sqrt ((x1 - x0) pow 2) < r - x0’ by PROVE_TAC [POW_2_SUB] \\
        Cases_on ‘0 <= x1 - x0’
        >- (Know ‘sqrt ((x1 - x0) pow 2) = x1 - x0’
            >- (MATCH_MP_TAC POW_2_SQRT >> art []) >> DISCH_THEN (fs o wrap) \\
            Q.PAT_X_ASSUM ‘x1 - x0 < r - x0’ MP_TAC \\
            REAL_ARITH_TAC) \\
        POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [real_lte])) \\
        Know ‘x1 < 0 + x0’
        >- (rw [GSYM REAL_LT_SUB_RADD]) >> rw [] \\
        MATCH_MP_TAC REAL_LT_TRANS \\
        Q.EXISTS_TAC ‘x0’ >> art [] ],
      (* goal 2 (of 2) *)
      Suff ‘IMAGE (\s. PREIMAGE SND s) (subsets borel) SUBSET
            subsets (sigma univ(:real # real) {s | open_in (mtop mr2) s})’
      >- (rw [SUBSET_DEF] >> POP_ASSUM MATCH_MP_TAC \\
          Q.EXISTS_TAC ‘s’ >> art []) \\
      KILL_TAC \\
      REWRITE_TAC [borel_eq_gr_less] \\
      Q.ABBREV_TAC ‘sts = IMAGE (\(a,b). {x | a < x /\ x < b}) univ(:real # real)’ \\
      Q.ABBREV_TAC ‘Z = univ(:real # real)’ \\
      Know ‘IMAGE (\s. PREIMAGE SND s INTER Z) (subsets (sigma UNIV sts)) =
            subsets (sigma Z (IMAGE (\s. PREIMAGE SND s INTER Z) sts))’
      >- (MATCH_MP_TAC PREIMAGE_SIGMA >> rw [subset_class_def, IN_FUNSET]) \\
      simp [Abbr ‘Z’] >> Rewr' \\
      Q.ABBREV_TAC ‘B = sigma univ(:real # real) {s | open_in (mtop mr2) s}’ \\
     ‘univ(:real # real) = space B’ by PROVE_TAC [SPACE_SIGMA] >> POP_ORW \\
      MATCH_MP_TAC SIGMA_SUBSET \\
      Q.UNABBREV_TAC ‘B’ \\
      CONJ_TAC >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA >> rw [subset_class_def]) \\
      MATCH_MP_TAC SUBSET_TRANS \\
      Q.EXISTS_TAC ‘{s | open_in (mtop mr2) s}’ >> rw [SIGMA_SUBSET_SUBSETS] \\
      simp [Abbr ‘sts’, SUBSET_DEF] \\
      Q.X_GEN_TAC ‘y’ >> rw [] \\
      Cases_on ‘x’ >> simp [] \\
      Know ‘PREIMAGE SND {x | q < x /\ x < r} = univ(:real) CROSS {x | q < x /\ x < r}’
      >- (rw [Once EXTENSION, IN_PREIMAGE, IN_CROSS]) >> Rewr' \\
      rw [MTOP_OPEN] \\
      Cases_on ‘x’ >> rename1 ‘q < SND (x,y)’ >> fs [] \\
      Q.ABBREV_TAC ‘dy = min (y - q) (r - y)’ \\
      Q.EXISTS_TAC ‘dy’ \\
      CONJ_TAC >- (rw [Abbr ‘dy’, REAL_LT_MIN, REAL_SUB_LT]) \\
      Q.X_GEN_TAC ‘z’ >> Cases_on ‘z’ >> simp [] \\
      DISCH_TAC >> rename1 ‘dist mr2 ((x0,y0),(x1,y1)) < dy’ \\
      Know ‘dist mr2 ((x0,y0),(x0,y1)) <= dist mr2 ((x0,y0),(x1,y1))’
      >- (rw [MR2_DEF] \\
          MATCH_MP_TAC SQRT_MONO_LE >> rw [REAL_LE_POW2]) >> DISCH_TAC \\
      Know ‘dist mr2 ((x0,y0),(x0,y1)) < dy’
      >- (MATCH_MP_TAC REAL_LET_TRANS \\
          Q.EXISTS_TAC ‘dist mr2 ((x0,y0),(x1,y1))’ >> art []) \\
      rw [Abbr ‘dy’, REAL_LT_MIN, MR2_DEF] >| (* 2 subgoals *)
      [ (* goal 2.1 (of 2) *)
        Cases_on ‘0 <= y0 - y1’
        >- (Know ‘sqrt ((y0 - y1) pow 2) = y0 - y1’
            >- (MATCH_MP_TAC POW_2_SQRT >> art []) >> DISCH_THEN (fs o wrap) \\
            Q.PAT_X_ASSUM ‘y0 - y1 < y0 - q’ MP_TAC \\
            REAL_ARITH_TAC) \\
        POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [real_lte])) \\
        Know ‘y0 < 0 + y1’
        >- (rw [GSYM REAL_LT_SUB_RADD]) >> rw [] \\
        MATCH_MP_TAC REAL_LT_TRANS \\
        Q.EXISTS_TAC ‘y0’ >> art [],
        (* goal 2.2 (of 2) *)
       ‘sqrt ((y1 - y0) pow 2) < r - y0’ by PROVE_TAC [POW_2_SUB] \\
        Cases_on ‘0 <= y1 - y0’
        >- (Know ‘sqrt ((y1 - y0) pow 2) = y1 - y0’
            >- (MATCH_MP_TAC POW_2_SQRT >> art []) >> DISCH_THEN (fs o wrap) \\
            Q.PAT_X_ASSUM ‘y1 - y0 < r - y0’ MP_TAC \\
            REAL_ARITH_TAC) \\
        POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [real_lte])) \\
        Know ‘y1 < 0 + y0’
        >- (rw [GSYM REAL_LT_SUB_RADD]) >> rw [] \\
        MATCH_MP_TAC REAL_LT_TRANS \\
        Q.EXISTS_TAC ‘y0’ >> art [] ] ]
QED

Theorem borel_2d_alt_box :
    borel CROSS borel = sigma UNIV {(box a b) CROSS (box c d) | T}
Proof
    REWRITE_TAC [borel_2d, borel_2d_lemma4]
 >> Suff ‘{J | (?a b c d. J = interval (a,b) CROSS interval (c,d))} =
          {box a b CROSS box c d | T}’ >- Rewr
 >> rw [Once EXTENSION, box_alt]
QED

Theorem space_borel_2d :
    space (borel CROSS borel) = UNIV
Proof
    REWRITE_TAC [borel_2d_alt_box, SPACE_SIGMA]
QED

(* Hyperbola area is a open set, needed by IN_MEASURABLE_BOREL_2D_MUL *)
Theorem hyperbola_lemma1[local] :
    !q r. 0 < q /\ 0 < r ==>
          ?e. 0 < e /\
              !y. dist mr2 ((q,r),y) < e ==>
                  ?x. (y,T) = (\(x,y). ((x,y),0 < x * y)) x
Proof
    rpt STRIP_TAC
 >> Q.EXISTS_TAC ‘min q r’
 >> simp [REAL_LT_MIN]
 >> Q.X_GEN_TAC ‘y’ >> Cases_on ‘y’ >> rw [MR2_DEF]
 >> Q.EXISTS_TAC ‘(q',r')’ >> simp []
 >> MATCH_MP_TAC REAL_LT_MUL
 >> CCONTR_TAC >> fs [GSYM real_lte] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      Know ‘q <= q - q'’
      >- (REWRITE_TAC [REAL_LE_SUB_LADD] \\
          GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM REAL_ADD_RID] \\
          ASM_REWRITE_TAC [REAL_LE_LADD]) >> DISCH_TAC \\
      Know ‘q pow 2 <= (q - q') pow 2’
      >- (MATCH_MP_TAC POW_LE >> art [] \\
          MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> DISCH_TAC \\
      Know ‘q pow 2 <= (q - q') pow 2 + (r - r') pow 2’
      >- (MATCH_MP_TAC REAL_LE_TRANS \\
          Q.EXISTS_TAC ‘(q - q') pow 2’ >> rw [REAL_LE_POW2]) >> DISCH_TAC \\
      Know ‘sqrt (q pow 2) <= sqrt ((q - q') pow 2 + (r - r') pow 2)’
      >- (MATCH_MP_TAC SQRT_MONO_LE >> rw [REAL_LE_POW2]) \\
      Know ‘sqrt (q pow 2) = q’
      >- (MATCH_MP_TAC POW_2_SQRT \\
          MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
      DISCH_THEN (PURE_ASM_REWRITE_TAC o wrap) >> DISCH_TAC \\
      METIS_TAC [REAL_LTE_ANTISYM],
      (* goal 2 (of 2) *)
      Know ‘r <= r - r'’
      >- (REWRITE_TAC [REAL_LE_SUB_LADD] \\
          GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM REAL_ADD_RID] \\
          ASM_REWRITE_TAC [REAL_LE_LADD]) >> DISCH_TAC \\
      Know ‘r pow 2 <= (r - r') pow 2’
      >- (MATCH_MP_TAC POW_LE >> art [] \\
          MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> DISCH_TAC \\
      Know ‘r pow 2 <= (q - q') pow 2 + (r - r') pow 2’
      >- (MATCH_MP_TAC REAL_LE_TRANS \\
          Q.EXISTS_TAC ‘(r - r') pow 2’ >> rw [REAL_LE_POW2]) >> DISCH_TAC \\
      Know ‘sqrt (r pow 2) <= sqrt ((q - q') pow 2 + (r - r') pow 2)’
      >- (MATCH_MP_TAC SQRT_MONO_LE >> rw [REAL_LE_POW2]) \\
      Know ‘sqrt (r pow 2) = r’
      >- (MATCH_MP_TAC POW_2_SQRT \\
          MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
      DISCH_THEN (PURE_ASM_REWRITE_TAC o wrap) >> DISCH_TAC \\
      METIS_TAC [REAL_LTE_ANTISYM] ]
QED

Theorem hyperbola_lemma2[local] :
    !q r. q < 0 /\ r < 0 ==>
          ?e. 0 < e /\
              !y. dist mr2 ((q,r),y) < e ==>
                  ?x. (y,T) = (\(x,y). ((x,y),0 < x * y)) x
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘-q’, ‘-r’] hyperbola_lemma1)
 >> ‘0 < -q /\ 0 < -r’ by METIS_TAC [GSYM REAL_NEG_LT0, REAL_NEG_NEG]
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC ‘e’ >> art []
 >> Q.X_GEN_TAC ‘y’ >> Cases_on ‘y’
 >> STRIP_TAC
 >> rename1 ‘dist mr2 ((x0,y0),(x1,y1)) < e’
 >> Q.PAT_X_ASSUM ‘!y. P ==> Q’ (MP_TAC o (Q.SPEC ‘(-x1,-y1)’))
 >> rw [MR2_MIRROR]
 >> Cases_on ‘x’ >> fs []
 >> Q.EXISTS_TAC ‘(x1,y1)’ >> rw []
 >> fs [REAL_NEG_MUL2]
QED

Theorem hyperbola_lemma3[local] :
    !a q r. a < q * r /\ 0 < a /\ 0 < q /\ 0 < r ==>
            ?e. 0 < e /\
                !y. dist mr2 ((q,r),y) < e ==>
                    ?x. (y,T) = (\(x,y). ((x,y),a < x * y)) x
Proof
    qx_genl_tac [‘R’, ‘X’, ‘Y’] >> STRIP_TAC
 >> ‘R <> 0 /\ X <> 0 /\ Y <> 0’ by PROVE_TAC [REAL_LT_IMP_NE]
 >> Q.ABBREV_TAC ‘A = X - R / Y’ (* horizontal distance to the curve *)
 >> Q.ABBREV_TAC ‘B = Y - R / X’ (*   vertical distance to the curve *)
 >> ‘0 < A /\ 0 < B’ by rw [REAL_LT_SUB_LADD, Abbr ‘A’, Abbr ‘B’]
 (* applying jensen_pos_convex_SIGMA and pos_convex_inv *)
 >> MP_TAC (ISPEC “{(0 :num);1}” jensen_pos_convex_SIGMA)
 >> rw [FINITE_TWO]
 >> POP_ASSUM (MP_TAC o (Q.SPECL [‘inv’,
                                  ‘binary (1 / 2) (1 / 2)’,
                                  ‘binary X (R / Y)’]))
 >> simp [binary_def, pos_convex_inv]
 >> ‘{1:num} DELETE 0 = {1}’ by rw [GSYM DELETE_NON_ELEMENT]
 >> DISCH_TAC
 >> Know ‘inv (SIGMA (\(x :num). 1 / 2 * if x = 0 then X else R / Y) {0; 1}) <=
          SIGMA (\(x :num). 1 / 2 * inv (if x = 0 then X else R / Y)) {0; 1}’
 >- (POP_ASSUM MATCH_MP_TAC \\
     rw [REAL_SUM_IMAGE_THM])
 >> POP_ASSUM K_TAC
 >> rw [REAL_SUM_IMAGE_THM]
 >> Q.PAT_X_ASSUM ‘{1} DELETE 0 = {1}’ K_TAC
 (* stage work *)
 >> Q.ABBREV_TAC ‘cx = 1 / 2 * X + 1 / 2 * (R * inv Y)’
 >> Q.ABBREV_TAC ‘cy = 1 / 2 * Y + 1 / 2 * (R * inv X)’
 >> Know ‘0 < cx /\ 0 < cy’
 >- (CONJ_TAC >> qunabbrevl_tac [‘cx’, ‘cy’] \\
     MATCH_MP_TAC REAL_LT_ADD \\
     CONJ_TAC >> MATCH_MP_TAC REAL_LT_MUL >> rw [])
 >> STRIP_TAC
 >> Know ‘R <= cx * cy’
 >- (Know ‘R <= cx * cy <=> R / cx <= cy’
     >- (REWRITE_TAC [Once REAL_MUL_COMM, Once EQ_SYM_EQ] \\
         MATCH_MP_TAC REAL_LE_LDIV_EQ >> art []) >> Rewr' \\
     REWRITE_TAC [real_div] \\
     Know ‘R * inv cx <= R * (1 / 2 * inv X + 1 / 2 * inv (R / Y))’
     >- (MATCH_MP_TAC REAL_LE_LMUL_IMP >> art [] \\
         MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> DISCH_TAC \\
     Suff ‘cy = R * (1 / 2 * inv X + 1 / 2 * inv (R / Y))’
     >- (Rewr' >> art []) \\
     Q.UNABBREV_TAC ‘cy’ \\
     REWRITE_TAC [real_div, REAL_ADD_LDISTRIB, REAL_MUL_LID] \\
     rw [REAL_INV_MUL, REAL_INV_INV, Once REAL_ADD_COMM])
 >> DISCH_TAC
 (* now estimate e *)
 >> Q.EXISTS_TAC ‘min (A / 2) (B / 2)’
 >> CONJ_TAC >- rw [Abbr ‘A’, Abbr ‘B’, REAL_LT_MIN, REAL_SUB_LT]
 >> Q.X_GEN_TAC ‘y’ >> Cases_on ‘y’
 >> RW_TAC std_ss [REAL_LT_MIN, MR2_DEF]
 >> Q.EXISTS_TAC ‘(q,r)’ >> rw []
 >> Know ‘X - A / 2 < q’
 >- (REWRITE_TAC [REAL_LT_SUB_RADD, Once REAL_ADD_COMM] \\
     REWRITE_TAC [GSYM REAL_LT_SUB_RADD] \\
     Cases_on ‘X - q <= 0’ >- (MATCH_MP_TAC REAL_LET_TRANS \\
                               Q.EXISTS_TAC ‘0’ >> rw []) \\
     FULL_SIMP_TAC std_ss [GSYM real_lt] \\
     CCONTR_TAC >> FULL_SIMP_TAC std_ss [GSYM real_lte] \\
     Suff ‘A / 2 <= sqrt ((X - q) pow 2 + (Y - r) pow 2)’
     >- METIS_TAC [REAL_LET_ANTISYM] \\
     MATCH_MP_TAC REAL_LE_TRANS \\
     Q.EXISTS_TAC ‘sqrt ((X - q) pow 2)’ \\
     CONJ_TAC >- (Suff ‘sqrt ((X - q) pow 2) = X - q’ >- (Rewr' >> art []) \\
                  MATCH_MP_TAC POW_2_SQRT \\
                  MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
     MATCH_MP_TAC SQRT_MONO_LE >> rw [REAL_LE_POW2])
 >> DISCH_TAC
 >> Know ‘X - A / 2 < q’
 >- (REWRITE_TAC [REAL_LT_SUB_RADD, Once REAL_ADD_COMM] \\
     REWRITE_TAC [GSYM REAL_LT_SUB_RADD] \\
     Cases_on ‘X - q <= 0’ >- (MATCH_MP_TAC REAL_LET_TRANS \\
                               Q.EXISTS_TAC ‘0’ >> rw []) \\
     FULL_SIMP_TAC std_ss [GSYM real_lt] \\
     CCONTR_TAC >> FULL_SIMP_TAC std_ss [GSYM real_lte] \\
     Suff ‘A / 2 <= sqrt ((X - q) pow 2 + (Y - r) pow 2)’
     >- METIS_TAC [REAL_LET_ANTISYM] \\
     MATCH_MP_TAC REAL_LE_TRANS \\
     Q.EXISTS_TAC ‘sqrt ((X - q) pow 2)’ \\
     CONJ_TAC >- (Suff ‘sqrt ((X - q) pow 2) = X - q’ >- (Rewr' >> art []) \\
                  MATCH_MP_TAC POW_2_SQRT \\
                  MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
     MATCH_MP_TAC SQRT_MONO_LE >> rw [REAL_LE_POW2])
 >> DISCH_TAC
 >> Know ‘Y - B / 2 < r’
 >- (REWRITE_TAC [REAL_LT_SUB_RADD, Once REAL_ADD_COMM] \\
     REWRITE_TAC [GSYM REAL_LT_SUB_RADD] \\
     Cases_on ‘Y - r <= 0’ >- (MATCH_MP_TAC REAL_LET_TRANS \\
                               Q.EXISTS_TAC ‘0’ >> rw []) \\
     FULL_SIMP_TAC std_ss [GSYM real_lt] \\
     CCONTR_TAC >> FULL_SIMP_TAC std_ss [GSYM real_lte] \\
     Suff ‘B / 2 <= sqrt ((X - q) pow 2 + (Y - r) pow 2)’
     >- METIS_TAC [REAL_LET_ANTISYM] \\
     MATCH_MP_TAC REAL_LE_TRANS \\
     Q.EXISTS_TAC ‘sqrt ((Y - r) pow 2)’ \\
     CONJ_TAC >- (Suff ‘sqrt ((Y - r) pow 2) = Y - r’ >- (Rewr' >> art []) \\
                  MATCH_MP_TAC POW_2_SQRT \\
                  MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
     MATCH_MP_TAC SQRT_MONO_LE >> rw [REAL_LE_POW2])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘sqrt _ < A / 2’ K_TAC
 >> Q.PAT_X_ASSUM ‘sqrt _ < B / 2’ K_TAC
 (* stage work *)
 >> Know ‘X - A / 2 = cx’
 >- (qunabbrevl_tac [‘cx’, ‘A’] \\
     SIMP_TAC real_ss [real_div, REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB, REAL_MUL_LID,
                       REAL_ARITH “x - (y - z) = x - y + z”] \\
     Q.ABBREV_TAC ‘c = R * inv Y’ \\
     rw [REAL_SUB_LDISTRIB] >> REAL_ARITH_TAC)
 >> DISCH_THEN ((FULL_SIMP_TAC std_ss) o wrap)
 >> Know ‘Y - B / 2 = cy’
 >- (qunabbrevl_tac [‘cy’, ‘B’] \\
     SIMP_TAC real_ss [real_div, REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB, REAL_MUL_LID,
                       REAL_ARITH “x - (y - z) = x - y + z”] \\
     Q.ABBREV_TAC ‘c = R * inv X’ \\
     rw [REAL_SUB_LDISTRIB] >> REAL_ARITH_TAC)
 >> DISCH_THEN ((FULL_SIMP_TAC std_ss) o wrap)
 >> MATCH_MP_TAC REAL_LET_TRANS
 >> Q.EXISTS_TAC ‘cx * cy’ >> art []
 >> MATCH_MP_TAC REAL_LT_MUL2 >> art []
 >> CONJ_TAC >> MATCH_MP_TAC REAL_LT_IMP_LE >> art []
QED

Theorem hyperbola_lemma4[local] :
    !a q r. a < q * r /\ 0 < a /\ q < 0 /\ r < 0 ==>
            ?e. 0 < e /\
                !y. dist mr2 ((q,r),y) < e ==>
                    ?x. (y,T) = (\(x,y). ((x,y),a < x * y)) x
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘a’, ‘-q’, ‘-r’] hyperbola_lemma3)
 >> ‘0 < -q /\ 0 < -r’ by METIS_TAC [GSYM REAL_NEG_LT0, REAL_NEG_NEG]
 >> RW_TAC std_ss [REAL_NEG_MUL2]
 >> Q.EXISTS_TAC ‘e’ >> art []
 >> Q.X_GEN_TAC ‘y’ >> Cases_on ‘y’
 >> STRIP_TAC
 >> rename1 ‘dist mr2 ((x0,y0),(x1,y1)) < e’
 >> Q.PAT_X_ASSUM ‘!y. P ==> Q’ (MP_TAC o (Q.SPEC ‘(-x1,-y1)’))
 >> rw [MR2_MIRROR]
 >> Cases_on ‘x’ >> fs []
 >> Q.EXISTS_TAC ‘(x1,y1)’ >> rw []
 >> fs [REAL_NEG_MUL2]
QED

Theorem hyperbola_lemma5[local] :
    !a. a < 0 ==> ?e. 0 < e /\
                      !y. dist mr2 ((0,0),y) < e ==>
                          ?x. (y,T) = (\(x,y). ((x,y),a < x * y)) x
Proof
    rpt STRIP_TAC
 >> Q.EXISTS_TAC ‘sqrt (-(2 * a))’
 >> STRONG_CONJ_TAC
 >- (MATCH_MP_TAC SQRT_POS_LT >> art [GSYM REAL_NEG_LT0, REAL_NEG_NEG] \\
    ‘0 = 2 * 0’ by PROVE_TAC [REAL_MUL_RZERO] >> POP_ORW \\
     MATCH_MP_TAC REAL_LT_LMUL_IMP >> rw [])
 >> DISCH_TAC
 >> Q.X_GEN_TAC ‘y’ >> Cases_on ‘y’
 >> rename1 ‘dist mr2 ((0,0),(x,y)) < sqrt (-(2 * a))’
 >> rw [MR2_DEF]
 >> Q.EXISTS_TAC ‘(x,y)’ >> rw []
 >> Know ‘sqrt (x pow 2 + y pow 2) pow 2 < sqrt (-(2 * a)) pow 2’
 >- (MATCH_MP_TAC REAL_POW_LT2 >> rw [] \\
     MATCH_MP_TAC SQRT_POS_LE \\
     MATCH_MP_TAC REAL_LE_ADD >> rw [REAL_LE_POW2])
 >> Know ‘sqrt (x pow 2 + y pow 2) pow 2 = x pow 2 + y pow 2’
 >- (MATCH_MP_TAC SQRT_POW_2 \\
     MATCH_MP_TAC REAL_LE_ADD >> rw [REAL_LE_POW2]) >> Rewr'
 >> Know ‘sqrt (-(2 * a)) pow 2 = -(2 * a)’
 >- (MATCH_MP_TAC SQRT_POW_2 >> rw [REAL_NEG_GE0] \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> Rewr'
 >> DISCH_TAC
 >> Know ‘0 <= (x + y) pow 2’ >- REWRITE_TAC [REAL_LE_POW2]
 >> REWRITE_TAC [ADD_POW_2, REAL_SUB_LZERO, Once (GSYM REAL_LE_SUB_RADD)]
 >> DISCH_TAC
 >> Know ‘-(2 * x * y) < -(2 * a)’ >- PROVE_TAC [REAL_LET_TRANS]
 >> rw []
QED

Theorem REAL_LE_SUBR[local] :
    !x y. x <= x - y <=> y <= 0
Proof
    rw [REWRITE_RULE [GSYM real_sub] (Q.SPECL [‘r’, ‘-y1’] REAL_LE_ADDR)]
QED

Theorem hyperbola_lemma6[local] :
    !a r. a < 0 /\ 0 < r (* q = 0 *) ==>
          ?e. 0 < e /\ !y. dist mr2 ((0,r),y) < e ==>
                           ?x. (y,T) = (\(x,y). ((x,y),a < x * y)) x
Proof
    rpt STRIP_TAC
 >> ‘r <> 0’ by PROVE_TAC [REAL_LT_IMP_NE]
 >> ‘0 < -a’ by METIS_TAC [GSYM REAL_NEG_LT0, REAL_NEG_NEG]
 >> Q.EXISTS_TAC ‘min ((1 / 2) * (-a / r)) r’
 >> CONJ_TAC >- rw [REAL_LT_MIN]
 >> Q.X_GEN_TAC ‘y’ >> Cases_on ‘y’
 >> rw [REAL_LT_MIN, MR2_DEF]
 >> rename1 ‘sqrt (x1 pow 2 + (r - y1) pow 2) < r’
 >> Q.EXISTS_TAC ‘(x1,y1)’ >> rw []
 >> STRIP_ASSUME_TAC (Q.SPECL [‘x1’, ‘0’] REAL_LT_TOTAL) (* 3 subgoals *)
 >| [ (* goal 1 (of 3): trivial *)
      rw [],
      (* goal 2 (of 3): hard *)
      Know ‘0 < y1’
      >- (CCONTR_TAC >> fs [GSYM real_lte] \\
         ‘r <= r - y1’ by PROVE_TAC [REAL_LE_SUBR] \\
          Know ‘r pow 2 <= x1 pow 2 + (r - y1) pow 2’
          >- (MATCH_MP_TAC REAL_LE_TRANS \\
              Q.EXISTS_TAC ‘(r - y1) pow 2’ \\
              reverse CONJ_TAC >- rw [] \\
              MATCH_MP_TAC POW_LE >> rw [REAL_LE_SUBR] \\
              MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> DISCH_TAC \\
          Know ‘sqrt (r pow 2) <= sqrt (x1 pow 2 + (r - y1) pow 2)’
          >- (MATCH_MP_TAC SQRT_MONO_LE >> rw [REAL_LE_POW2]) \\
          Know ‘sqrt (r pow 2) = r’
          >- (MATCH_MP_TAC POW_2_SQRT \\
              MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
          DISCH_THEN (PURE_ONCE_REWRITE_TAC o wrap) \\
          DISCH_TAC >> PROVE_TAC [REAL_LET_ANTISYM]) >> DISCH_TAC \\
      Suff ‘(1 / 2) * (a / r) < x1 /\ y1 < 2 * r’
      >- (STRIP_TAC \\
         ‘a < x1 * y1 <=> (~x1) * y1 < -a’ by rw [GSYM REAL_NEG_LMUL] >> POP_ORW \\
         ‘~a = (1 / 2 * (~a / r)) * (2 * r)’ by rw [] >> POP_ORW \\
          MATCH_MP_TAC REAL_LT_MUL2 >> rw [] >| (* 3 subgoals *)
          [ MATCH_MP_TAC REAL_LT_IMP_LE >> art [],
            MATCH_MP_TAC REAL_LT_IMP_LE >> art [],
            fs [GSYM REAL_NEG_LMUL] \\
            Know ‘a < 2 * (r * x1) <=> a * inv r < 2 * (r * x1) * inv r’
            >- (MATCH_MP_TAC (GSYM REAL_LT_RMUL) \\
                rw [REAL_LT_INV_EQ]) >> Rewr' \\
            Know ‘2 * (r * x1) * inv r = 2 * x1’ >- rw [] \\
            Rewr' >> art [] ]) \\
      CCONTR_TAC >> fs [GSYM real_lte] >| (* 2 subgoals *)
      [ (* goal 1 (of 2) *)
        Know ‘2 * r * ~x1 < -a’
        >- (MATCH_MP_TAC REAL_LET_TRANS \\
            Q.EXISTS_TAC ‘2 * (r * sqrt (x1 pow 2 + (r - y1) pow 2))’ >> rw [] \\
            Know ‘-x1 = sqrt (-x1 pow 2)’
            >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
                MATCH_MP_TAC POW_2_SQRT \\
                REWRITE_TAC [GSYM REAL_NEG_LE0, REAL_NEG_NEG] \\
                MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> Rewr' \\
            MATCH_MP_TAC SQRT_MONO_LE >> rw [REAL_LE_POW2]) \\
        PURE_REWRITE_TAC [GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL, REAL_LT_NEG] \\
        Know ‘a < 2 * r * x1 <=> a * inv r < 2 * r * x1 * inv r’
        >- (MATCH_MP_TAC (GSYM REAL_LT_RMUL) \\
            rw [REAL_LT_INV_EQ]) \\
        DISCH_THEN (PURE_REWRITE_TAC o wrap) \\
       ‘2 * r * x1 * inv r = 2 * x1’ by rw [] >> POP_ASSUM (PURE_REWRITE_TAC o wrap) \\
        DISCH_TAC >> PROVE_TAC [REAL_LET_ANTISYM],
        (* goal 2 (of 2) *)
       ‘r <= y1 - r’ by rw [REAL_LE_SUB_LADD, REAL_DOUBLE] \\
        Know ‘r pow 2 <= (y1 - r) pow 2’
        >- (MATCH_MP_TAC POW_LE >> art [] \\
            MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
        Know ‘(y1 - r) pow 2 = (r - y1) pow 2’
        >- (‘y1 - r = -(r - y1)’ by REAL_ARITH_TAC >> POP_ORW \\
            rw []) \\
        DISCH_THEN (PURE_REWRITE_TAC o wrap) >> DISCH_TAC \\
        Know ‘r pow 2 <= x1 pow 2 + (r - y1) pow 2’
        >- (MATCH_MP_TAC REAL_LE_TRANS \\
            Q.EXISTS_TAC ‘(r - y1) pow 2’ >> art [] \\
            rw [REAL_LE_ADDL, REAL_LE_POW2]) >> DISCH_TAC \\
        Know ‘sqrt (r pow 2) <= sqrt (x1 pow 2 + (r - y1) pow 2)’
        >- (MATCH_MP_TAC SQRT_MONO_LE >> rw [REAL_LE_POW2]) \\
        Know ‘sqrt (r pow 2) = r’
        >- (MATCH_MP_TAC POW_2_SQRT \\
            MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
        DISCH_THEN (PURE_ONCE_REWRITE_TAC o wrap) \\
        DISCH_TAC >> PROVE_TAC [REAL_LET_ANTISYM] ],
      (* goal 2 (of 3): easy *)
      Know ‘0 < y1’
      >- (CCONTR_TAC >> fs [GSYM real_lte] \\
         ‘r <= r - y1’ by PROVE_TAC [REAL_LE_SUBR] \\
          Know ‘r pow 2 <= x1 pow 2 + (r - y1) pow 2’
          >- (MATCH_MP_TAC REAL_LE_TRANS \\
              Q.EXISTS_TAC ‘(r - y1) pow 2’ \\
              reverse CONJ_TAC >- rw [] \\
              MATCH_MP_TAC POW_LE >> rw [REAL_LE_SUBR] \\
              MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> DISCH_TAC \\
          Know ‘sqrt (r pow 2) <= sqrt (x1 pow 2 + (r - y1) pow 2)’
          >- (MATCH_MP_TAC SQRT_MONO_LE >> rw [REAL_LE_POW2]) \\
          Know ‘sqrt (r pow 2) = r’
          >- (MATCH_MP_TAC POW_2_SQRT \\
              MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
          DISCH_THEN (PURE_ONCE_REWRITE_TAC o wrap) \\
          DISCH_TAC >> PROVE_TAC [REAL_LET_ANTISYM]) >> DISCH_TAC \\
       MATCH_MP_TAC REAL_LT_TRANS \\
       Q.EXISTS_TAC ‘0’ >> art [] \\
       MATCH_MP_TAC REAL_LT_MUL >> art [] ]
QED

Theorem hyperbola_lemma7[local] :
    !a q. a < 0 /\ 0 < q (* r = 0 *) ==>
          ?e. 0 < e /\ !y. dist mr2 ((q,0),y) < e ==>
                           ?x. (y,T) = (\(x,y). ((x,y),a < x * y)) x
Proof
    rpt STRIP_TAC
 >> ‘q <> 0’ by PROVE_TAC [REAL_LT_IMP_NE]
 >> ‘0 < -a’ by METIS_TAC [GSYM REAL_NEG_LT0, REAL_NEG_NEG]
 >> Q.EXISTS_TAC ‘min ((1 / 2) * (-a / q)) q’
 >> CONJ_TAC >- rw [REAL_LT_MIN]
 >> Q.X_GEN_TAC ‘y’ >> Cases_on ‘y’
 >> rw [REAL_LT_MIN, MR2_DEF]
 >> rename1 ‘sqrt ((q - x1) pow 2 + y1 pow 2) < q’
 >> Q.EXISTS_TAC ‘(x1,y1)’ >> rw []
 >> STRIP_ASSUME_TAC (Q.SPECL [‘y1’, ‘0’] REAL_LT_TOTAL) (* 3 subgoals *)
 >| [ (* goal 1 (of 3): trivial *)
      rw [],
      (* goal 2 (of 3): hard *)
      Know ‘0 < x1’
      >- (CCONTR_TAC >> fs [GSYM real_lte] \\
         ‘q <= q - x1’ by PROVE_TAC [REAL_LE_SUBR] \\
          Know ‘q pow 2 <= (q - x1) pow 2 + y1 pow 2’
          >- (MATCH_MP_TAC REAL_LE_TRANS \\
              Q.EXISTS_TAC ‘(q - x1) pow 2’ \\
              reverse CONJ_TAC >- rw [] \\
              MATCH_MP_TAC POW_LE >> rw [REAL_LE_SUBR] \\
              MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> DISCH_TAC \\
          Know ‘sqrt (q pow 2) <= sqrt ((q - x1) pow 2 + y1 pow 2)’
          >- (MATCH_MP_TAC SQRT_MONO_LE >> rw [REAL_LE_POW2]) \\
          Know ‘sqrt (q pow 2) = q’
          >- (MATCH_MP_TAC POW_2_SQRT \\
              MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
          DISCH_THEN (PURE_ONCE_REWRITE_TAC o wrap) \\
          DISCH_TAC >> PROVE_TAC [REAL_LET_ANTISYM]) >> DISCH_TAC \\
      Suff ‘(1 / 2) * (a / q) < y1 /\ x1 < 2 * q’
      >- (STRIP_TAC \\
         ‘a < x1 * y1 <=> x1 * ~y1 < -a’ by rw [GSYM REAL_NEG_LMUL] >> POP_ORW \\
         ‘~a = (2 * q) * (1 / 2 * (~a / q))’ by rw [] >> POP_ORW \\
          MATCH_MP_TAC REAL_LT_MUL2 >> rw [] >| (* 3 subgoals *)
          [ MATCH_MP_TAC REAL_LT_IMP_LE >> art [],
            MATCH_MP_TAC REAL_LT_IMP_LE >> art [],
            fs [GSYM REAL_NEG_LMUL, REAL_LT_NEG] \\
            Know ‘a < 2 * (q * y1) <=> a * inv q < 2 * (q * y1) * inv q’
            >- (MATCH_MP_TAC (GSYM REAL_LT_RMUL) \\
                rw [REAL_LT_INV_EQ]) >> Rewr' \\
            Know ‘2 * (q * y1) * inv q = 2 * y1’ >- rw [] \\
            Rewr' >> art [] ]) \\
      CCONTR_TAC >> fs [GSYM real_lte] >| (* 2 subgoals *)
      [ (* goal 1 (of 2) *)
        Know ‘2 * q * ~y1 < -a’
        >- (MATCH_MP_TAC REAL_LET_TRANS \\
            Q.EXISTS_TAC ‘2 * (q * sqrt ((q - x1) pow 2 + y1 pow 2))’ >> rw [] \\
            Know ‘-y1 = sqrt (-y1 pow 2)’
            >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
                MATCH_MP_TAC POW_2_SQRT \\
                REWRITE_TAC [GSYM REAL_NEG_LE0, REAL_NEG_NEG] \\
                MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> Rewr' \\
            MATCH_MP_TAC SQRT_MONO_LE >> rw [REAL_LE_POW2]) \\
        PURE_REWRITE_TAC [GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL, REAL_LT_NEG] \\
        Know ‘a < 2 * q * y1 <=> a * inv q < 2 * q * y1 * inv q’
        >- (MATCH_MP_TAC (GSYM REAL_LT_RMUL) \\
            rw [REAL_LT_INV_EQ]) \\
        DISCH_THEN (PURE_REWRITE_TAC o wrap) \\
       ‘2 * q * y1 * inv q = 2 * y1’ by rw [] >> POP_ASSUM (PURE_REWRITE_TAC o wrap) \\
        DISCH_TAC >> PROVE_TAC [REAL_LET_ANTISYM],
        (* goal 2 (of 2) *)
       ‘q <= x1 - q’ by rw [REAL_LE_SUB_LADD, REAL_DOUBLE] \\
        Know ‘q pow 2 <= (x1 - q) pow 2’
        >- (MATCH_MP_TAC POW_LE >> art [] \\
            MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
        Know ‘(x1 - q) pow 2 = (q - x1) pow 2’
        >- (‘x1 - q = -(q - x1)’ by REAL_ARITH_TAC >> POP_ORW \\
            rw []) \\
        DISCH_THEN (PURE_REWRITE_TAC o wrap) >> DISCH_TAC \\
        Know ‘q pow 2 <= (q - x1) pow 2 + y1 pow 2’
        >- (MATCH_MP_TAC REAL_LE_TRANS \\
            Q.EXISTS_TAC ‘(q - x1) pow 2’ >> art [] \\
            rw [REAL_LE_ADDR, REAL_LE_POW2]) >> DISCH_TAC \\
        Know ‘sqrt (q pow 2) <= sqrt ((q - x1) pow 2 + y1 pow 2)’
        >- (MATCH_MP_TAC SQRT_MONO_LE >> rw [REAL_LE_POW2]) \\
        Know ‘sqrt (q pow 2) = q’
        >- (MATCH_MP_TAC POW_2_SQRT \\
            MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
        DISCH_THEN (PURE_ONCE_REWRITE_TAC o wrap) \\
        DISCH_TAC >> PROVE_TAC [REAL_LET_ANTISYM] ],
      (* goal 2 (of 3): easy *)
      Know ‘0 < x1’
      >- (CCONTR_TAC >> fs [GSYM real_lte] \\
         ‘q <= q - x1’ by PROVE_TAC [REAL_LE_SUBR] \\
          Know ‘q pow 2 <= (q - x1) pow 2 + y1 pow 2’
          >- (MATCH_MP_TAC REAL_LE_TRANS \\
              Q.EXISTS_TAC ‘(q - x1) pow 2’ \\
              reverse CONJ_TAC >- rw [] \\
              MATCH_MP_TAC POW_LE >> rw [REAL_LE_SUBR] \\
              MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> DISCH_TAC \\
          Know ‘sqrt (q pow 2) <= sqrt ((q - x1) pow 2 + y1 pow 2)’
          >- (MATCH_MP_TAC SQRT_MONO_LE >> rw [REAL_LE_POW2]) \\
          Know ‘sqrt (q pow 2) = q’
          >- (MATCH_MP_TAC POW_2_SQRT \\
              MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
          DISCH_THEN (PURE_ONCE_REWRITE_TAC o wrap) \\
          DISCH_TAC >> PROVE_TAC [REAL_LET_ANTISYM]) >> DISCH_TAC \\
       MATCH_MP_TAC REAL_LT_TRANS \\
       Q.EXISTS_TAC ‘0’ >> art [] \\
       MATCH_MP_TAC REAL_LT_MUL >> art [] ]
QED

Theorem hyperbola_lemma8[local] :
    !a q r. a < 0 /\ a < q * r /\ q < 0 /\ 0 < r ==>
            ?e. 0 < e /\
                !y. dist mr2 ((q,r),y) < e ==>
                    ?x. (y,T) = (\(x,y). ((x,y),a < x * y)) x
Proof
    rpt STRIP_TAC
 >> ‘q <> 0 /\ r <> 0’ by PROVE_TAC [REAL_LT_IMP_NE]
 >> ‘0 < -a’ by METIS_TAC [GSYM REAL_NEG_LT0, REAL_NEG_NEG]
 >> Know ‘a / r < q’
 >- (Know ‘a / r < q <=> a / r * r < q * r’
     >- (MATCH_MP_TAC (GSYM REAL_LT_RMUL) >> art []) >> Rewr' \\
     Suff ‘a / r * r = a’ >- rw [] \\
     MATCH_MP_TAC REAL_DIV_RMUL >> art [])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘a / r’, ‘q’] REAL_MEAN)
 >> RW_TAC std_ss []
 >> ‘z < 0’ by PROVE_TAC [REAL_LT_TRANS]
 >> ‘z <> 0’ by PROVE_TAC [REAL_LT_IMP_NE]
 >> Q.EXISTS_TAC ‘min (min (q - z) (a / z - r)) (min (-q) r)’
 >> simp [REAL_LT_MIN, REAL_SUB_LT]
 >> STRONG_CONJ_TAC (* a < r * z *)
 >- (Know ‘a / r * r < z * r’
     >- (MATCH_MP_TAC REAL_LT_RMUL_IMP >> art []) \\
     Know ‘a / r * r = a’ >- (MATCH_MP_TAC REAL_DIV_RMUL >> art []) \\
     Rewr' >> DISCH_TAC >> art [Once REAL_MUL_COMM])
 >> DISCH_TAC
 >> Q.X_GEN_TAC ‘y’ >> Cases_on ‘y’ >> rw [MR2_DEF]
 >> rename1 ‘sqrt ((q - x) pow 2 + (r - y) pow 2) < q - z’
 >> Q.EXISTS_TAC ‘(x,y)’ >> rw []
 >> Know ‘x < 0’
 >- (CCONTR_TAC >> fs [GSYM real_lte] \\
    ‘-q <= -q + x’ by PROVE_TAC [REAL_LE_ADDR] \\
     Know ‘(-q) pow 2 <= (-q + x) pow 2 + (r - y) pow 2’
     >- (MATCH_MP_TAC REAL_LE_TRANS \\
         Q.EXISTS_TAC ‘(-q + x) pow 2’ >> rw [REAL_LE_ADDR, REAL_LE_POW2] \\
        ‘q pow 2 = (-q) pow 2’ by rw [] >> POP_ORW \\
         MATCH_MP_TAC POW_LE >> rw [REAL_LE_ADDR, GSYM REAL_NEG_LE0, REAL_NEG_NEG] \\
         MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
    ‘-q + x = -(q - x)’ by REAL_ARITH_TAC \\
     POP_ASSUM (PURE_ONCE_REWRITE_TAC o wrap) \\
    ‘-(q - x) pow 2 = (q - x) pow 2’ by PROVE_TAC [NEGATED_POW] \\
     POP_ASSUM (PURE_ONCE_REWRITE_TAC o wrap) \\
     DISCH_TAC \\
     Know ‘sqrt (-q pow 2) <= sqrt ((q - x) pow 2 + (r - y) pow 2)’
     >- (MATCH_MP_TAC SQRT_MONO_LE >> rw [REAL_LE_ADDR]) \\
     Know ‘sqrt (-q pow 2) = -q’
     >- (MATCH_MP_TAC POW_2_SQRT >> rw [GSYM REAL_NEG_LE0, REAL_NEG_NEG] \\
         MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
     DISCH_THEN (PURE_ONCE_REWRITE_TAC o wrap) \\
     DISCH_TAC >> PROVE_TAC [REAL_LET_ANTISYM]) >> DISCH_TAC
 >> Know ‘0 < y’
 >- (CCONTR_TAC >> fs [GSYM real_lte] \\
    ‘r <= r - y’ by rw [REAL_LE_SUBR] \\
     Know ‘r pow 2 <= (q - x) pow 2 + (r - y) pow 2’
     >- (MATCH_MP_TAC REAL_LE_TRANS \\
         Q.EXISTS_TAC ‘(r - y) pow 2’ >> rw [REAL_LE_ADDL, REAL_LE_POW2] \\
         MATCH_MP_TAC POW_LE >> rw [REAL_LE_SUBR] \\
         MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> DISCH_TAC \\
     Know ‘sqrt (r pow 2) <= sqrt ((q - x) pow 2 + (r - y) pow 2)’
     >- (MATCH_MP_TAC SQRT_MONO_LE >> rw [REAL_LE_POW2]) \\
     Know ‘sqrt (r pow 2) = r’
     >- (MATCH_MP_TAC POW_2_SQRT \\
         MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
     DISCH_THEN (PURE_ONCE_REWRITE_TAC o wrap) \\
     DISCH_TAC >> PROVE_TAC [REAL_LET_ANTISYM]) >> DISCH_TAC
 >> Suff ‘z < x /\ y < a / z’
 >- (STRIP_TAC \\
    ‘a < x * y <=> ~x * y < -a’ by rw [GSYM REAL_NEG_LMUL] >> POP_ORW \\
    ‘~a = -z * (a / z)’ by rw [] >> POP_ORW \\
     MATCH_MP_TAC REAL_LT_MUL2 >> rw [] \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art [])
 (* stage work *)
 >> CCONTR_TAC
 >> fs [GSYM real_lte]
 >| [ (* goal 1 (of 2) *)
     ‘q - z <= q - x’ by rw [REAL_LE_SUB_CANCEL1] \\
      Know ‘(q - z) pow 2 <= (q - x) pow 2 + (r - y) pow 2’
      >- (MATCH_MP_TAC REAL_LE_TRANS \\
          Q.EXISTS_TAC ‘(q - x) pow 2’ >> rw [REAL_LE_ADDR] \\
          MATCH_MP_TAC POW_LE >> rw [REAL_SUB_LE] \\
          MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> DISCH_TAC \\
      Know ‘sqrt ((q - z) pow 2) <= sqrt ((q - x) pow 2 + (r - y) pow 2)’
      >- (MATCH_MP_TAC SQRT_MONO_LE >> rw []) \\
      Know ‘sqrt ((q - z) pow 2) = q - z’
      >- (MATCH_MP_TAC POW_2_SQRT >> rw [REAL_SUB_LE] \\
          MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
      DISCH_THEN (PURE_ONCE_REWRITE_TAC o wrap) \\
      DISCH_TAC >> PROVE_TAC [REAL_LET_ANTISYM],
      (* goal 2 (of 2) *)
     ‘a / z - r <= y - r’ by rw [REAL_LE_SUB_CANCEL2] \\
      Know ‘(a / z - r) pow 2 <= (q - x) pow 2 + (y - r) pow 2’
      >- (MATCH_MP_TAC REAL_LE_TRANS \\
          Q.EXISTS_TAC ‘(y - r) pow 2’ >> rw [] \\
          MATCH_MP_TAC POW_LE >> rw [REAL_SUB_LE] \\
          MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> DISCH_TAC \\
      Know ‘sqrt ((a / z - r) pow 2) <= sqrt ((q - x) pow 2 + (y - r) pow 2)’
      >- (MATCH_MP_TAC SQRT_MONO_LE >> rw []) \\
      Know ‘sqrt ((a / z - r) pow 2) = a / z - r’
      >- (MATCH_MP_TAC POW_2_SQRT >> rw [REAL_SUB_LE] \\
          MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
      DISCH_THEN (PURE_ONCE_REWRITE_TAC o wrap) \\
     ‘y - r = -(r - y)’ by REAL_ARITH_TAC \\
      POP_ASSUM (PURE_ONCE_REWRITE_TAC o wrap) \\
      PURE_ONCE_REWRITE_TAC [NEGATED_POW] \\
      DISCH_TAC >> PROVE_TAC [REAL_LET_ANTISYM] ]
QED

Theorem hyperbola_open_in_mr2 :
    !a. {(x,y) | a < x * y} IN {s | open_in (mtop mr2) s}
Proof
    rw [MTOP_OPEN]
 >> rename1 ‘(x,T) = (\(x,y). ((x,y),a < x * y)) z’
 >> Cases_on ‘z’ >> fs []
 >> Q.PAT_X_ASSUM ‘x = (q,r)’ K_TAC (* cleanup *)
 >> STRIP_ASSUME_TAC (Q.SPECL [‘a’, ‘0’] REAL_LT_TOTAL) (* 3 subgoals *)
 >| [ (* goal 1 (of 3): a = 0 *)
      POP_ASSUM (fs o wrap) \\
      Know ‘(0 < q /\ 0 < r) \/ (q < 0 /\ r < 0)’
      >- (Cases_on ‘0 < q’ >- (DISJ1_TAC >> art [] \\
                               PROVE_TAC [REAL_LT_LMUL_0]) \\
          reverse (fs [GSYM real_lte, REAL_LE_LT]) >- fs [] \\
          DISJ2_TAC >> CCONTR_TAC \\
          reverse (fs [GSYM real_lte, REAL_LE_LT]) >- fs [] \\
          METIS_TAC [REAL_MUL_COMM, REAL_LT_LMUL_0, REAL_LT_ANTISYM]) \\
      Q.PAT_X_ASSUM ‘0 < q * r’ K_TAC \\
      STRIP_TAC >| (* 2 subgoals *)
      [ MATCH_MP_TAC hyperbola_lemma1 >> art [],
        MATCH_MP_TAC hyperbola_lemma2 >> art [] ],
      (* goal 2 (of 3): a < 0 *)
      Cases_on ‘0 < q /\ 0 < r’
      >- (MP_TAC (Q.SPECL [‘q’, ‘r’] hyperbola_lemma1) \\
          RW_TAC std_ss [] \\
          Q.EXISTS_TAC ‘e’ >> RW_TAC std_ss [] \\
          Q.PAT_X_ASSUM ‘!y. dist mr2 ((q,r),y) < e ==> P’ (MP_TAC o (Q.SPEC ‘y’)) \\
          Cases_on ‘y’ >> RW_TAC std_ss [] \\
          Cases_on ‘x’ >> rfs [] >> rename1 ‘0 < x * y’ \\
          Q.EXISTS_TAC ‘(x,y)’ >> rw [] \\
          MATCH_MP_TAC REAL_LT_TRANS >> Q.EXISTS_TAC ‘0’ >> art []) \\
      Cases_on ‘q < 0 /\ r < 0’
      >- (MP_TAC (Q.SPECL [‘q’, ‘r’] hyperbola_lemma2) \\
          RW_TAC std_ss [] \\
          Q.EXISTS_TAC ‘e’ >> RW_TAC std_ss [] \\
          Q.PAT_X_ASSUM ‘!y. dist mr2 ((q,r),y) < e ==> P’ (MP_TAC o (Q.SPEC ‘y’)) \\
          Cases_on ‘y’ >> RW_TAC std_ss [] \\
          Cases_on ‘x’ >> rfs [] >> rename1 ‘0 < x * y’ \\
          Q.EXISTS_TAC ‘(x,y)’ >> rw [] \\
          MATCH_MP_TAC REAL_LT_TRANS >> Q.EXISTS_TAC ‘0’ >> art []) \\
      fs [GSYM real_lte] >| (* 4 subgoals *)
      [ (* goal 2.1 (of 4) *)
       ‘q = 0’ by PROVE_TAC [REAL_LE_ANTISYM] >> fs [] \\
        STRIP_ASSUME_TAC (Q.SPECL [‘r’, ‘0’] REAL_LT_TOTAL) >| (* 3 subgoals *)
        [ (* goal 2.1.1 (of 3) *)
          Q.PAT_X_ASSUM ‘r = 0’ (REWRITE_TAC o wrap) \\
          MATCH_MP_TAC hyperbola_lemma5 >> art [],
          (* goal 2.1.2 (of 3) *)
          MP_TAC (Q.SPECL [‘a’, ‘-r’] hyperbola_lemma6) \\
         ‘0 < -r’ by PROVE_TAC [GSYM REAL_NEG_LT0, REAL_NEG_NEG] >> rw [] \\
          Q.EXISTS_TAC ‘e’ >> art [] \\
          Q.X_GEN_TAC ‘y’ >> Cases_on ‘y’ >> DISCH_TAC \\
          rename1 ‘dist mr2 ((0,r),(x0,y0)) < e’ \\
          Q.EXISTS_TAC ‘(x0,y0)’ >> rw [] \\
          Q.PAT_X_ASSUM ‘!y. dist mr2 ((0,-r),y) < e ==> P’ (MP_TAC o (Q.SPEC ‘(-x0,-y0)’)) \\
         ‘0 = -0’ by PROVE_TAC [REAL_NEG_0] >> POP_ORW \\
          RW_TAC std_ss [MR2_MIRROR] \\
          Cases_on ‘x’ >> fs [] \\
          rename1 ‘-x0 = x1’ >> rename1 ‘-y0 = y1’ \\
          Q.PAT_X_ASSUM ‘-x0 = x1’ (fs o wrap o SYM) \\
          Q.PAT_X_ASSUM ‘-y0 = y1’ (fs o wrap o SYM),
          (* goal 2.1.3 (of 3) *)
          MATCH_MP_TAC hyperbola_lemma6 >> art [] ],
        (* goal 2.2 (of 4) *)
        fs [REAL_LE_LT] >| (* 4 subgoals *)
        [ (* goal 2.2.1 (of 4) *)
          MATCH_MP_TAC hyperbola_lemma8 >> art [],
          (* goal 2.2.2 (of 4) *)
          MP_TAC (Q.SPECL [‘a’, ‘-q’] hyperbola_lemma7) \\
         ‘0 < -q’ by PROVE_TAC [GSYM REAL_NEG_LT0, REAL_NEG_NEG] >> rw [] \\
          Q.EXISTS_TAC ‘e’ >> art [] \\
          Q.X_GEN_TAC ‘y’ >> Cases_on ‘y’ >> DISCH_TAC \\
          rename1 ‘dist mr2 ((q,0),(x0,y0)) < e’ \\
          Q.EXISTS_TAC ‘(x0,y0)’ >> rw [] \\
          Q.PAT_X_ASSUM ‘!y. dist mr2 ((-q,0),y) < e ==> P’ (MP_TAC o (Q.SPEC ‘(-x0,-y0)’)) \\
         ‘0 = -0’ by PROVE_TAC [REAL_NEG_0] >> POP_ORW \\
          RW_TAC std_ss [MR2_MIRROR] \\
          Cases_on ‘x’ >> fs [] \\
          rename1 ‘-x0 = x1’ >> rename1 ‘-y0 = y1’ \\
          Q.PAT_X_ASSUM ‘-x0 = x1’ (fs o wrap o SYM) \\
          Q.PAT_X_ASSUM ‘-y0 = y1’ (fs o wrap o SYM),
          (* goal 2.2.3 (of 4) *)
          MATCH_MP_TAC hyperbola_lemma6 >> art [],
          (* goal 2.2.4 (of 4) *)
          MATCH_MP_TAC hyperbola_lemma5 >> art [] ],
        (* goal 2.3 (of 4) *)
        fs [REAL_LE_LT] >| (* 4 subgoals *)
        [ (* goal 2.3.1 (of 4) *)
          MP_TAC (Q.SPECL [‘a’, ‘-q’, ‘-r’] hyperbola_lemma8) \\
          rw [REAL_NEG_MUL2, REAL_NEG_LE0] \\
          Q.EXISTS_TAC ‘e’ >> art [] \\
          Q.X_GEN_TAC ‘y’ >> Cases_on ‘y’ >> DISCH_TAC \\
          rename1 ‘dist mr2 ((x0,y0),(x1,y1)) < e’ \\
          Q.EXISTS_TAC ‘(x1,y1)’ >> rw [] \\
          Q.PAT_X_ASSUM ‘!y. dist mr2 ((-x0,-y0),y) < e ==> P’ (MP_TAC o (Q.SPEC ‘(-x1,-y1)’)) \\
          rw [MR2_MIRROR] \\
          Cases_on ‘x’ >> fs [] \\
          Q.PAT_X_ASSUM ‘-x1 = x2’ (fs o wrap o SYM) \\
          Q.PAT_X_ASSUM ‘-y1 = y2’ (fs o wrap o SYM),
          (* goal 2.3.2 (of 4) *)
          MP_TAC (Q.SPECL [‘a’, ‘-r’] hyperbola_lemma6) \\
         ‘0 < -r’ by PROVE_TAC [GSYM REAL_NEG_LT0, REAL_NEG_NEG] >> rw [] \\
          Q.EXISTS_TAC ‘e’ >> art [] \\
          Q.X_GEN_TAC ‘y’ >> Cases_on ‘y’ >> DISCH_TAC \\
          rename1 ‘dist mr2 ((0,r),(x0,y0)) < e’ \\
          Q.EXISTS_TAC ‘(x0,y0)’ >> rw [] \\
          Q.PAT_X_ASSUM ‘!y. dist mr2 ((0,-r),y) < e ==> P’ (MP_TAC o (Q.SPEC ‘(-x0,-y0)’)) \\
         ‘0 = -0’ by PROVE_TAC [REAL_NEG_0] >> POP_ORW \\
          RW_TAC std_ss [MR2_MIRROR] \\
          Cases_on ‘x’ >> fs [] \\
          rename1 ‘-x0 = x1’ >> rename1 ‘-y0 = y1’ \\
          Q.PAT_X_ASSUM ‘-x0 = x1’ (fs o wrap o SYM) \\
          Q.PAT_X_ASSUM ‘-y0 = y1’ (fs o wrap o SYM),
          (* goal 2.3.3 (of 4) *)
          MATCH_MP_TAC hyperbola_lemma7 >> art [],
          (* goal 2.3.4 (of 4) *)
          MATCH_MP_TAC hyperbola_lemma5 >> art [] ],
        (* goal 2.4 (of 4) *)
       ‘r = 0’ by PROVE_TAC [REAL_LE_ANTISYM] >> fs [] \\
        STRIP_ASSUME_TAC (Q.SPECL [‘q’, ‘0’] REAL_LT_TOTAL) >| (* 3 subgoals *)
        [ (* goal 2.1.1 (of 3) *)
          Q.PAT_X_ASSUM ‘q = 0’ (REWRITE_TAC o wrap) \\
          MATCH_MP_TAC hyperbola_lemma5 >> art [],
          (* goal 2.1.2 (of 3) *)
          MP_TAC (Q.SPECL [‘a’, ‘-q’] hyperbola_lemma7) \\
         ‘0 < -q’ by PROVE_TAC [GSYM REAL_NEG_LT0, REAL_NEG_NEG] >> rw [] \\
          Q.EXISTS_TAC ‘e’ >> art [] \\
          Q.X_GEN_TAC ‘y’ >> Cases_on ‘y’ >> DISCH_TAC \\
          rename1 ‘dist mr2 ((q,0),(x0,y0)) < e’ \\
          Q.EXISTS_TAC ‘(x0,y0)’ >> rw [] \\
          Q.PAT_X_ASSUM ‘!y. dist mr2 ((-q,0),y) < e ==> P’ (MP_TAC o (Q.SPEC ‘(-x0,-y0)’)) \\
         ‘0 = -0’ by PROVE_TAC [REAL_NEG_0] >> POP_ORW \\
          RW_TAC std_ss [MR2_MIRROR] \\
          Cases_on ‘x’ >> fs [] \\
          rename1 ‘-x0 = x1’ >> rename1 ‘-y0 = y1’ \\
          Q.PAT_X_ASSUM ‘-x0 = x1’ (fs o wrap o SYM) \\
          Q.PAT_X_ASSUM ‘-y0 = y1’ (fs o wrap o SYM),
          (* goal 2.1.3 (of 3) *)
          MATCH_MP_TAC hyperbola_lemma7 >> art [] ] ],
      (* goal 3 (of 3): 0 < a *)
     ‘0 < q * r’ by PROVE_TAC [REAL_LT_TRANS] \\
      Know ‘(0 < q /\ 0 < r) \/ (q < 0 /\ r < 0)’
      >- (Cases_on ‘0 < q’ >- (DISJ1_TAC >> art [] \\
                               PROVE_TAC [REAL_LT_LMUL_0]) \\
          reverse (fs [GSYM real_lte, REAL_LE_LT]) >- fs [] \\
          DISJ2_TAC >> CCONTR_TAC \\
          reverse (fs [GSYM real_lte, REAL_LE_LT]) >- fs [] \\
          METIS_TAC [REAL_MUL_COMM, REAL_LT_LMUL_0, REAL_LT_ANTISYM]) \\
      Q.PAT_X_ASSUM ‘0 < q * r’ K_TAC \\
      STRIP_TAC >| (* 2 subgoals *)
      [ MATCH_MP_TAC hyperbola_lemma3 >> art [],
        MATCH_MP_TAC hyperbola_lemma4 >> art [] ] ]
QED

val _ = export_theory ();

(* References:

  [1] Schilling, R.L.: Measures, Integrals and Martingales (Second Edition).
      Cambridge University Press (2017).
 *)
