open HolKernel Parse boolLib bossLib;

open arithmeticTheory pred_setTheory listTheory rich_listTheory pairTheory
     combinTheory numSyntax extra_pred_setTools
     extra_listTheory hurdUtils realTheory extra_realTheory realLib
     extra_numTheory seqTheory simpLib;

open util_probTheory sigma_algebraTheory real_measureTheory real_probabilityTheory;
open subtypeTheory extra_pred_setTheory;
open sequenceTheory sequenceTools;
open prob_canonTheory prob_canonTools;

(* interactive mode
quietdec := false;
*)

val _ = new_theory "prob_algebra";
val _ = ParseExtras.temp_loose_equality()

val std_ss' = std_ss ++ boolSimps.ETA_ss;

(* ------------------------------------------------------------------------- *)
(* Definition of the embedding function from boolean list lists to boolean   *)
(* sequences.                                                                *)
(* ------------------------------------------------------------------------- *)

val halfspace_def = Define `halfspace (b : bool) = (\x. shd x = b)`;

val mirror_def = Define `mirror (x :num -> bool) = scons (~shd x) (stl x)`;

val prefix_set_def = Define
  `(prefix_set [] = UNIV) /\
   (prefix_set (h :: t) = halfspace h INTER (prefix_set t o stl))`;

val prefix_seq_def = Define `prefix_seq (h :: t) = scons h (prefix_seq t)`;

val prob_embed_def = Define `prob_embed l = UNIONL (MAP prefix_set l)`;

val prob_algebra_def = Define
   `prob_algebra = (univ(:num -> bool), {s | ?b. s = prob_embed b})`;

val prob_premeasure_def = Define
  `(prob_premeasure ([] : bool list list) = (0 :real)) /\
   (prob_premeasure (l :: rest) =
    (1 / 2) pow (LENGTH l) + prob_premeasure rest)`;

val prob_measure_def = Define
   `prob_measure s =
        inf {r | ?c. (s = prob_embed c) /\ (prob_premeasure c = r)}`;

(* NOTE: in sigma_algebraTheory, the definition of ‘measurable’ has been
   modified by removing all sigma-algebra requirements. The following
   definition of ‘premeasurable’ is not changed accordingly, as it's only
   used in the ‘miller’ example, but some related theorems may have to
   add sigma_algebra antecedents.  -- Chun Tian, 24/10/2022
 *)
val premeasurable_def = Define
   `premeasurable a b = {f | algebra a /\ algebra b /\
                             f IN (space a -> space b) /\
                             !s. s IN subsets b ==> ((PREIMAGE f s)INTER(space a)) IN subsets a}`;

val IN_PREMEASURABLE = store_thm
  ("IN_PREMEASURABLE",
   ``!a b f. f IN premeasurable a b =
                algebra a /\ algebra b /\
                f IN (space a -> space b) /\
                (!s. s IN subsets b ==> (PREIMAGE f s) INTER (space a) IN subsets a)``,
   RW_TAC std_ss [premeasurable_def, GSPECIFICATION]);

(* NOTE: added ‘sigma_algebra a /\ sigma_algebra b’ into antecedents,
         due to changes of ‘measurable’
 *)
Theorem MEASURABLE_IMP_PREMEASURABLE :
    !f a b. sigma_algebra a /\ sigma_algebra b /\ f IN measurable a b ==>
            f IN premeasurable a b
Proof
   rpt GEN_TAC
   >> RW_TAC std_ss [measurable_def, premeasurable_def, GSPECIFICATION,
                     SIGMA_ALGEBRA_ALGEBRA]
QED

val MEASURABLE_IS_PREMEASURABLE = store_thm
  ("MEASURABLE_IS_PREMEASURABLE",
  ``!a b. sigma_algebra a /\ sigma_algebra b ==> (measurable a b = premeasurable a b)``,
   rpt STRIP_TAC
   >> RW_TAC std_ss [EXTENSION, measurable_def, premeasurable_def, GSPECIFICATION]
   >> IMP_RES_TAC SIGMA_ALGEBRA_ALGEBRA
   >> METIS_TAC []);

Theorem PREMEASURABLE_SIGMA :
    !f a b sp.
       sigma_algebra a /\ subset_class sp b /\ f IN (space a -> sp) /\
       (!s. s IN b ==> (PREIMAGE f s) INTER (space a) IN subsets a) ==>
       f IN premeasurable a (sigma sp b)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC MEASURABLE_IMP_PREMEASURABLE
 >> RW_TAC std_ss [SIGMA_ALGEBRA_SIGMA]
 >> MATCH_MP_TAC MEASURABLE_SIGMA >> art []
QED

val PREMEASURABLE_SUBSET = store_thm
  ("PREMEASURABLE_SUBSET",
   ``!a b. sigma_algebra a ==>
        premeasurable a b SUBSET premeasurable a (sigma (space b) (subsets b))``,
   RW_TAC std_ss [SUBSET_DEF]
   >> MATCH_MP_TAC PREMEASURABLE_SIGMA
   >> PROVE_TAC [IN_PREMEASURABLE, algebra_def]);

val PREMEASURABLE_LIFT = store_thm
  ("PREMEASURABLE_LIFT",
   ``!f a b.
       sigma_algebra a /\ f IN premeasurable a b ==>
       f IN premeasurable a (sigma (space b) (subsets b))``,
   PROVE_TAC [PREMEASURABLE_SUBSET, SUBSET_DEF]);

val PREMEASURABLE_I = store_thm
  ("PREMEASURABLE_I",
   ``!a. algebra a ==> I IN premeasurable a a``,
   RW_TAC std_ss [IN_PREMEASURABLE, I_THM, PREIMAGE_I, IN_FUNSET,
                  GSPEC_ID, SPACE, SUBSET_REFL]
   >> Know `s INTER space a = s`
   >- (FULL_SIMP_TAC std_ss [Once EXTENSION, algebra_def, IN_INTER,
                             subset_class_def, SUBSET_DEF]
       >> METIS_TAC [])
   >> RW_TAC std_ss []);

val PREMEASURABLE_COMP = store_thm
  ("PREMEASURABLE_COMP",
   ``!f g a b c.
       f IN premeasurable a b /\ g IN premeasurable b c ==>
       (g o f) IN premeasurable a c``,
   RW_TAC std_ss [IN_PREMEASURABLE, GSYM PREIMAGE_COMP, IN_FUNSET,
                  algebra_def, space_def, subsets_def, GSPECIFICATION]
   >> `PREIMAGE f (PREIMAGE g s) INTER space a =
       PREIMAGE f (PREIMAGE g s INTER space b) INTER space a`
        by (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_PREIMAGE] >> METIS_TAC [])
   >> METIS_TAC []);

(* NOTE: there's also prob_preserving_def in real_probabilityTheory *)
val prob_preserving_def = Define
   `prob_preserving m1 m2 =
   {f |
    f IN premeasurable (m_space m1, measurable_sets m1) (m_space m2, measurable_sets m2) /\
    !s.
      s IN measurable_sets m2 ==>
           (measure m1 ((PREIMAGE f s)INTER(m_space m1)) = measure m2 s)}`;

val PROB_PRESERVING = store_thm (
   "PROB_PRESERVING",
  ``!p1 p2.
       prob_preserving p1 p2 =
       {f |
        f IN premeasurable (p_space p1, events p1) (p_space p2, events p2) /\
        !s. s IN events p2 ==> (prob p1 ((PREIMAGE f s) INTER (p_space p1)) = prob p2 s)}``,
   REPEAT GEN_TAC
   >> REWRITE_TAC [EXTENSION]
   >> GEN_TAC
   >> REWRITE_TAC [GSPECIFICATION]
   >> BETA_TAC
   >> REWRITE_TAC [PAIR_EQ]
   >> RW_TAC std_ss [prob_preserving_def, events_def, prob_def, p_space_def, GSPECIFICATION]);

val IN_PROB_PRESERVING = store_thm
  ("IN_PROB_PRESERVING",
   ``!p1 p2 f.
       f IN prob_preserving p1 p2 =
       f IN premeasurable (p_space p1, events p1) (p_space p2, events p2) /\
       !s. s IN events p2 ==> (prob p1 ((PREIMAGE f s) INTER (p_space p1)) = prob p2 s)``,
   RW_TAC std_ss [PROB_PRESERVING, GSPECIFICATION]);

val PROB_SPACE_REDUCE = store_thm
  ("PROB_SPACE_REDUCE", ``!p. (p_space p, events p, prob p) = p``,
   Cases
   >> Q.SPEC_TAC (`r`, `r`)
   >> Cases
   >> RW_TAC std_ss [p_space_def, events_def, prob_def,
                     m_space_def, measurable_sets_def, measure_def]);

val ALGEBRA_REDUCE = store_thm
  ("ALGEBRA_REDUCE", ``!a. algebra a ==> ((space a, subsets a) = a)``,
    Cases >> RW_TAC std_ss [space_def, subsets_def]);

val PROB_PRESERVING_LIFT = store_thm (
   "PROB_PRESERVING_LIFT",
  ``!p1 p2 a f.
       prob_space p1 /\ prob_space p2 /\
       (events p2 = subsets (sigma (p_space p2) a)) /\
       f IN prob_preserving p1 (p_space p2, a, prob p2) ==>
       f IN prob_preserving p1 p2``,
   RW_TAC std_ss []
   >> reverse (Cases_on `algebra (p_space p2, a)`)
   >- ( Q.PAT_X_ASSUM `f IN P`
          (ASSUME_TAC o (REWRITE_RULE [IN_PROB_PRESERVING, events_def, p_space_def, m_space_def,
                                       measurable_sets_def, prob_def, measure_def])) \\
        POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [IN_PREMEASURABLE])) \\
        FULL_SIMP_TAC std_ss [p_space_def] )
   >> Suff `f IN prob_preserving p1 (p_space p2, events p2, prob p2)`
   >- RW_TAC std_ss [PROB_SPACE_REDUCE]
   >> ASM_REWRITE_TAC []
   >> Q.PAT_X_ASSUM `f IN X` MP_TAC
   >> REWRITE_TAC [IN_PROB_PRESERVING, measurable_sets_def, measure_def, m_space_def,
                   p_space_def, events_def, prob_def]
   >> STRIP_TAC
   >> STRONG_CONJ_TAC
   >- (REWRITE_TAC [SIGMA_REDUCE]
       >> POP_ASSUM K_TAC
       >> Know `(sigma (m_space p2) a) = sigma (space (m_space p2, a)) (subsets (m_space p2, a))`
       >- RW_TAC std_ss [space_def, subsets_def]
       >> STRIP_TAC >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
       >> MATCH_MP_TAC PREMEASURABLE_LIFT
       >> ASM_REWRITE_TAC []
       >> FULL_SIMP_TAC std_ss [prob_space_def, measure_space_def])
   >> Q.PAT_X_ASSUM `f IN X` K_TAC
   >> REWRITE_TAC [IN_PREMEASURABLE, space_def, subsets_def]
   >> STRIP_TAC
   >> Suff `subsets (sigma (m_space p2) a) SUBSET
                 {s | measure p1 ((PREIMAGE f s) INTER (m_space p1)) = measure p2 s}`
   >- RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION]
   >> MATCH_MP_TAC SIGMA_PROPERTY_DISJOINT
   >> FULL_SIMP_TAC std_ss [p_space_def, prob_space_def, events_def]
   >> RW_TAC std_ss [GSPECIFICATION, SUBSET_DEF, IN_INTER, IN_FUNSET,
                     IN_UNIV, PREIMAGE_COMPL, PREIMAGE_BIGUNION, IMAGE_IMAGE] >| (* 3 sub-goals here *)
   [(* goal 1 (of 3) *)
    Q.PAT_X_ASSUM `mersurable_sets p2 = subsets (sigma (m_space p2) a)`
        (fn thm => FULL_SIMP_TAC std_ss [SYM thm])
    >> RW_TAC std_ss [MEASURE_COMPL]
    >> Q.PAT_X_ASSUM `measure p1 (PREIMAGE f s INTER m_space p1) = measure p2 s`
        (fn thm => ONCE_REWRITE_TAC [GSYM thm])
    >> Know `m_space p2 IN a` >- PROVE_TAC [ALGEBRA_SPACE, subsets_def, space_def]
    >> STRIP_TAC
    >> Q.PAT_X_ASSUM `measure p2 (m_space p2) = 1` K_TAC
    >> Q.PAT_X_ASSUM `measure p1 (m_space p1) = 1` (REWRITE_TAC o wrap o SYM)
    >> Know `PREIMAGE f (m_space p2) INTER m_space p1 = m_space p1`
    >- (FULL_SIMP_TAC std_ss [Once EXTENSION, IN_INTER, IN_PREIMAGE, IN_FUNSET] >> METIS_TAC [])
    >> RW_TAC std_ss [PREIMAGE_DIFF]
    >> `((PREIMAGE f (m_space p2) DIFF PREIMAGE f s) INTER m_space p1) =
        ((PREIMAGE f (m_space p2) INTER m_space p1) DIFF (PREIMAGE f s INTER m_space p1))`
        by (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_DIFF, IN_PREIMAGE] >> DECIDE_TAC)
    >> RW_TAC std_ss [MEASURE_COMPL],
    (* goal 2 (of 3) *)
    `BIGUNION (IMAGE (PREIMAGE f o f') UNIV) INTER m_space p1 =
     BIGUNION (IMAGE (\x:num. (PREIMAGE f o f') x INTER m_space p1) UNIV)`
        by (RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, IN_INTER, IN_IMAGE, IN_UNIV]
            >> FULL_SIMP_TAC std_ss [IN_FUNSET]
            >> EQ_TAC
            >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `PREIMAGE f (f' x') INTER m_space p1`
                >> ASM_REWRITE_TAC [IN_INTER] >> Q.EXISTS_TAC `x'` >> RW_TAC std_ss [])
            >> RW_TAC std_ss [] >> METIS_TAC [IN_PREIMAGE, IN_INTER])
    >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
    >> Suff
    `(measure p2 o f') --> measure p2 (BIGUNION (IMAGE f' UNIV)) /\
     (measure p2 o f') -->
     measure p1 (BIGUNION (IMAGE (\x. (PREIMAGE f o f') x INTER m_space p1) UNIV))`
    >- PROVE_TAC [SEQ_UNIQ]
    >> CONJ_TAC
    >- (MATCH_MP_TAC MEASURE_COUNTABLE_INCREASING
        >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, SUBSET_DEF])
    >> Know `measure p2 o f' = measure p1 o (\x. (PREIMAGE f o f') x INTER m_space p1)`
    >- (RW_TAC std_ss [FUN_EQ_THM]
        >> RW_TAC std_ss [o_THM])
    >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    >> MATCH_MP_TAC MEASURE_COUNTABLE_INCREASING
    >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, o_THM, PREIMAGE_EMPTY, INTER_EMPTY]
    >> Suff `PREIMAGE f (f' n) SUBSET PREIMAGE f (f' (SUC n))`
    >- RW_TAC std_ss [SUBSET_DEF, IN_INTER]
    >> MATCH_MP_TAC PREIMAGE_SUBSET
    >> RW_TAC std_ss [SUBSET_DEF],
    (* goal 3 (of 3) *)
    `BIGUNION (IMAGE (PREIMAGE f o f') UNIV) INTER m_space p1 =
     BIGUNION (IMAGE (\x:num. (PREIMAGE f o f') x INTER m_space p1) UNIV)`
        by (RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, IN_INTER, IN_IMAGE, IN_UNIV]
            >> FULL_SIMP_TAC std_ss [IN_FUNSET]
            >> EQ_TAC
            >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `PREIMAGE f (f' x') INTER m_space p1`
                >> ASM_REWRITE_TAC [IN_INTER] >> Q.EXISTS_TAC `x'` >> RW_TAC std_ss [])
            >> RW_TAC std_ss [] >> METIS_TAC [IN_PREIMAGE, IN_INTER])
    >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
    >> Suff
    `(measure p2 o f') sums measure p2 (BIGUNION (IMAGE f' UNIV)) /\
     (measure p2 o f') sums
     measure p1 (BIGUNION (IMAGE (\x. (PREIMAGE f o f') x INTER m_space p1) UNIV))`
    >- PROVE_TAC [SUM_UNIQ]
    >> CONJ_TAC
    >- (MATCH_MP_TAC MEASURE_COUNTABLY_ADDITIVE
        >> RW_TAC std_ss [IN_FUNSET, IN_UNIV])
    >> Know `measure p2 o f' = measure p1 o (\x. (PREIMAGE f o f') x INTER m_space p1)`
    >- (RW_TAC std_ss [FUN_EQ_THM]
        >> RW_TAC std_ss [o_THM])
    >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    >> MATCH_MP_TAC MEASURE_COUNTABLY_ADDITIVE
    >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, o_THM, IN_DISJOINT, PREIMAGE_DISJOINT, IN_INTER]
    >> METIS_TAC [IN_DISJOINT, PREIMAGE_DISJOINT]]);

val PROB_PRESERVING_SUBSET = store_thm (
   "PROB_PRESERVING_SUBSET",
  ``!p1 p2 a.
       prob_space p1 /\ prob_space p2 /\
       (events p2 = subsets (sigma (p_space p2) a)) ==>
       prob_preserving p1 (p_space p2, a, prob p2) SUBSET
       prob_preserving p1 p2``,
   RW_TAC std_ss [SUBSET_DEF]
   >> MATCH_MP_TAC PROB_PRESERVING_LIFT
   >> PROVE_TAC []);

val PREMEASURABLE_UP_LIFT = store_thm
  ("PREMEASURABLE_UP_LIFT",
   ``!sp a b c f. f IN premeasurable (sp, a) c /\
               algebra (sp, b) /\ a SUBSET b ==> f IN premeasurable (sp, b) c``,
   RW_TAC std_ss [IN_PREMEASURABLE, GSPECIFICATION, SUBSET_DEF, IN_FUNSET, space_def, subsets_def]);

val PREMEASURABLE_UP_SUBSET = store_thm
  ("PREMEASURABLE_UP_SUBSET",
   ``!sp a b c. a SUBSET b /\ algebra (sp, b)
        ==> premeasurable (sp, a) c SUBSET premeasurable (sp, b) c``,
   RW_TAC std_ss [PREMEASURABLE_UP_LIFT, SUBSET_DEF]
   >> MATCH_MP_TAC PREMEASURABLE_UP_LIFT
   >> Q.EXISTS_TAC `a`
   >> ASM_REWRITE_TAC [SUBSET_DEF]);

val PREMEASURABLE_UP_SIGMA = store_thm
  ("PREMEASURABLE_UP_SIGMA",
   ``!a b. premeasurable a b SUBSET premeasurable (sigma (space a) (subsets a)) b``,
   RW_TAC std_ss [SUBSET_DEF, IN_PREMEASURABLE, space_def, subsets_def, SPACE_SIGMA]
   >- ( MATCH_MP_TAC SIGMA_ALGEBRA_ALGEBRA \\
        MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA >> FULL_SIMP_TAC std_ss [algebra_def])
   >> PROVE_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF]);

val PROB_PRESERVING_UP_LIFT = store_thm (
   "PROB_PRESERVING_UP_LIFT",
  ``!p1 p2 f a.
       f IN prob_preserving (p_space p1, a, prob p1) p2 /\
       algebra (p_space p1, events p1) /\
       a SUBSET events p1 ==>
       f IN prob_preserving p1 p2``,
   RW_TAC std_ss [prob_preserving_def, GSPECIFICATION, SUBSET_DEF, events_def, p_space_def,
                  measure_def, measurable_sets_def, m_space_def, SPACE, prob_def]
   >> MATCH_MP_TAC PREMEASURABLE_UP_LIFT
   >> Q.EXISTS_TAC `a`
   >> RW_TAC std_ss [SUBSET_DEF]);

val PROB_PRESERVING_UP_SUBSET = store_thm (
   "PROB_PRESERVING_UP_SUBSET",
  ``!p1 p2 a.
       prob_space p1 /\
       a SUBSET events p1 /\
       algebra (p_space p1, events p1) ==>
       prob_preserving (p_space p1, a, prob p1) p2 SUBSET prob_preserving p1 p2``,
    RW_TAC std_ss [PROB_PRESERVING_UP_LIFT, SUBSET_DEF]
 >> MATCH_MP_TAC PROB_PRESERVING_UP_LIFT
 >> PROVE_TAC [SUBSET_DEF]);

val PROB_PRESERVING_UP_SIGMA = store_thm (
   "PROB_PRESERVING_UP_SIGMA",
  ``!p1 p2 a.
       prob_space p1 /\
       (events p1 = subsets (sigma (p_space p1) a)) ==>
       prob_preserving (p_space p1, a, prob p1) p2 SUBSET prob_preserving p1 p2``,
   RW_TAC std_ss [PROB_PRESERVING_UP_LIFT, SUBSET_DEF]
   >> MATCH_MP_TAC PROB_PRESERVING_UP_LIFT
   >> ASM_REWRITE_TAC [SIGMA_SUBSET_SUBSETS, SIGMA_REDUCE]
   >> FULL_SIMP_TAC std_ss [IN_PROB_PRESERVING, IN_PREMEASURABLE, p_space_def,
                            measurable_sets_def, space_def, subsets_def, prob_def,
                            events_def, measure_def, m_space_def]
   >> Q.EXISTS_TAC `a` >> ASM_REWRITE_TAC []
   >> CONJ_TAC
   >- ( MATCH_MP_TAC SIGMA_ALGEBRA_ALGEBRA \\
        MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
        Q.PAT_X_ASSUM `algebra (m_space p2, measurable_sets p2)` K_TAC \\
        Q.PAT_X_ASSUM `algebra (m_space p1, a)` MP_TAC \\
        RW_TAC std_ss [algebra_def, space_def, subsets_def] )
   >> KILL_TAC
   >> REWRITE_TAC [SUBSET_DEF, IN_SIGMA]);

(* ------------------------------------------------------------------------- *)
(* Theorems leading to:                                                      *)
(* 1.  prob_embed (prob_canon b) = prob_embed b                              *)
(* 2.  (prob_canon b = prob_canon c) = (prob_embed b = prob_embed c)         *)
(* 3.  algebra prob_algebra                                                  *)
(* 4.  (a o stl) IN prob_algebra = a IN prob_algebra                         *)
(* 5.  (a o sdrop n) IN prob_algebra = a IN prob_algebra                     *)
(* 6.  prob_premeasure (prob_canon b) <= prob_premeasure b                   *)
(* 7.  prob_measure (prob_embed b) = prob_premeasure (prob_canon b)          *)
(* 8.  positive (prob_algebra, prob_measure)                                 *)
(* 9.  additive (prob_algebra, prob_measure)                                 *)
(* 10. countably_additive (prob_algebra, prob_measure)                       *)
(* 11. a IN prob_algebra ==> prob_measure (a o stl) = prob_measure a         *)
(* 12. a IN prob_algebra ==> prob_measure (a o sdrop n) = prob_measure a     *)
(* ------------------------------------------------------------------------- *)

val IN_HALFSPACE = store_thm
  ("IN_HALFSPACE",
   ``!x b. x IN halfspace b = (shd x = b)``,
   RW_TAC std_ss [halfspace_def, SPECIFICATION]);

val COMPL_HALFSPACE = store_thm
  ("COMPL_HALFSPACE",
   ``!b. COMPL (halfspace b) = halfspace (~b)``,
   PSET_TAC [IN_HALFSPACE, EXTENSION]
   >> Cases_on `b`
   >> PROVE_TAC []);

val HALFSPACE_INTER = store_thm
  ("HALFSPACE_INTER",
   ``!b. halfspace T INTER halfspace F = {}``,
   PSET_TAC [IN_HALFSPACE, EXTENSION]);

val HALFSPACE_UNION = store_thm
  ("HALFSPACE_UNION",
   ``!b. halfspace T UNION halfspace F = UNIV``,
   PSET_TAC [IN_HALFSPACE, EXTENSION]);

val PREFIX_SET_BASIC = store_thm
  ("PREFIX_SET_BASIC",
   ``(prefix_set [] = UNIV) /\ (prefix_set [h] = halfspace h)``,
   PSET_TAC [prefix_set_def, IN_HALFSPACE, EXTENSION]);

val PREFIX_SET_SCONS = store_thm
  ("PREFIX_SET_SCONS",
   ``!h t x xs.
       scons h t IN prefix_set (x :: xs) = (h = x) /\ t IN prefix_set xs``,
   PSET_TAC [prefix_set_def, IN_HALFSPACE, SHD_SCONS, STL_SCONS, EXTENSION]);

val PREFIX_SET_NIL = store_thm
  ("PREFIX_SET_NIL",
   ``!l. (prefix_set l = UNIV) = (l = [])``,
   Cases >- RW_TAC std_ss [prefix_set_def]
   >> RW_TAC std_ss [EXTENSION, IN_UNIV]
   >> Q.EXISTS_TAC `sconst (~h)`
   >> RW_TAC std_ss [prefix_set_def]
   >> Cases_on `h`
   >> RW_TAC std_ss [IN_HALFSPACE, IN_INTER, SHD_SCONST]);

val PREFIX_SET_NONEMPTY = store_thm
  ("PREFIX_SET_NONEMPTY",
   ``!b. ~(prefix_set b = {})``,
   Induct >- PSET_TAC [prefix_set_def, EXTENSION]
   >> PSET_TAC [prefix_set_def, EXTENSION]
   >> Q.EXISTS_TAC `scons h x`
   >> PSET_TAC [IN_HALFSPACE, SHD_SCONS, IN_o, STL_SCONS]);

val PREFIX_SET_POPULATED = store_thm
  ("PREFIX_SET_POPULATED",
   ``!b. ?x. x IN prefix_set b``,
   STRIP_TAC
   >> MP_TAC (Q.SPEC `b` PREFIX_SET_NONEMPTY)
   >> PSET_TAC [EXTENSION]);

val PREFIX_SET_PREFIX_SUBSET = store_thm
  ("PREFIX_SET_PREFIX_SUBSET",
   ``!b c. prefix_set b SUBSET prefix_set c = IS_PREFIX b c``,
   Induct
   >- PSET_TAC [prefix_set_def, IS_PREFIX_NIL, GSYM PREFIX_SET_NIL, EXTENSION]
   >> Cases_on `c`
   >- PSET_TAC [prefix_set_def, IS_PREFIX_NIL, GSYM PREFIX_SET_NIL, EXTENSION]
   >> PSET_TAC [prefix_set_def, IS_PREFIX, IN_HALFSPACE, EXTENSION]
   >> Q.PAT_X_ASSUM `!c. P c = Q c` (fn th => REWRITE_TAC [SYM (Q.SPEC `t` th)])
   >> reverse EQ_TAC >- RW_TAC std_ss []
   >> STRIP_TAC
   >> reverse STRONG_CONJ_TAC
   >- (RW_TAC std_ss []
       >> Q.PAT_X_ASSUM `!x. P x ==> Q x` (MP_TAC o Q.SPEC `scons h x`)
       >> RW_TAC std_ss [SHD_SCONS, STL_SCONS])
   >> Suff `?x. (shd x = h') /\ stl x IN prefix_set b`
   >- PROVE_TAC []
   >> KILL_TAC
   >> MP_TAC (Q.SPEC `b` PREFIX_SET_NONEMPTY)
   >> PSET_TAC [EXTENSION]
   >> Q.EXISTS_TAC `scons h' x`
   >> RW_TAC std_ss [SHD_SCONS, STL_SCONS]);

val PREFIX_SET_SUBSET = store_thm
  ("PREFIX_SET_SUBSET",
   ``!b c.
       DISJOINT (prefix_set b) (prefix_set c) \/
       (prefix_set b) SUBSET (prefix_set c) \/
       (prefix_set c) SUBSET (prefix_set b)``,
   REWRITE_TAC [PREFIX_SET_PREFIX_SUBSET]
   >> Induct >- PSET_TAC [IS_PREFIX, EXTENSION]
   >> Cases_on `c` >- PSET_TAC [IS_PREFIX, EXTENSION]
   >> PSET_TAC [IS_PREFIX, prefix_set_def, IN_HALFSPACE, EXTENSION]
   >> POP_ASSUM (MP_TAC o Q.SPEC `t`)
   >> CONV_TAC (REDEPTH_CONV (LEFT_OR_FORALL_CONV ORELSEC RIGHT_OR_FORALL_CONV))
   >> Cases_on `h`
   >> Cases_on `h'`
   >> RW_TAC std_ss [OR_CLAUSES, GSYM DISJ_ASSOC]
   >> POP_ASSUM (MP_TAC o Q.SPEC `stl x`)
   >> PROVE_TAC []);

val PREFIX_SET_TWINS = store_thm
  ("PREFIX_SET_TWINS",
   ``!l. prefix_set (SNOC T l) UNION prefix_set (SNOC F l) = prefix_set l``,
   Induct >- PSET_TAC [SNOC, prefix_set_def, IN_HALFSPACE, EXTENSION]
   >> PSET_TAC [SNOC, prefix_set_def, IN_HALFSPACE, EXTENSION]
   >> PROVE_TAC []);

val PREFIX_SEQ = store_thm
  ("PREFIX_SEQ",
   ``!l. prefix_seq l IN prefix_set l``,
   Induct >- RW_TAC std_ss [prefix_set_def, IN_UNIV]
   >> RW_TAC std_ss [prefix_set_def, prefix_seq_def, IN_INTER, IN_HALFSPACE,
                     SHD_SCONS, GSYM PREIMAGE_ALT, IN_PREIMAGE, STL_SCONS]);

val IN_PROB_EMBED = store_thm
  ("IN_PROB_EMBED",
   ``!b. x IN prob_embed b = (?l. MEM l b /\ x IN prefix_set l)``,
   RW_TAC std_ss [prob_embed_def, IN_UNIONL, MEM_MAP]
   >> PROVE_TAC []);

val PROB_EMBED_BASIC = store_thm
  ("PROB_EMBED_BASIC",
   ``(prob_embed [] = {}) /\ (prob_embed [[]] = UNIV) /\
     (!b. prob_embed [[b]] = halfspace b)``,
   PSET_TAC [prob_embed_def, prefix_set_def, IN_PROB_EMBED, MEM, EXTENSION]);

val PROB_EMBED_NIL = store_thm
  ("PROB_EMBED_NIL",
   ``prob_embed [] = {}``,
   PSET_TAC [prob_embed_def, MEM_MAP, MEM, EXTENSION]);

val PROB_EMBED_CONS = store_thm
  ("PROB_EMBED_CONS",
   ``!x xs. prob_embed (x :: xs) = prefix_set x UNION prob_embed xs``,
   PSET_TAC [prob_embed_def, MEM_MAP, MEM, EXTENSION]
   >> PROVE_TAC []);

val PROB_EMBED_TRANSPOSE = store_thm
  ("PROB_EMBED_TRANSPOSE",
   ``!x y z. prob_embed (x :: y :: z) = prob_embed (y :: x :: z)``,
   PSET_TAC [PROB_EMBED_CONS, EXTENSION]
   >> PROVE_TAC []);

val PROB_EMBED_APPEND = store_thm
  ("PROB_EMBED_APPEND",
   ``!l1 l2.
       prob_embed (APPEND l1 l2) = prob_embed l1 UNION prob_embed l2``,
   PSET_TAC [IN_PROB_EMBED, EXTENSION, MEM_APPEND]
   >> PROVE_TAC []);

val PROB_EMBED_TLS = store_thm
  ("PROB_EMBED_TLS",
   ``!l b.
       (scons h t) IN prob_embed (MAP (CONS b) l) =
       (h = b) /\ t IN prob_embed l``,
   PSET_TAC [IN_PROB_EMBED, MEM_MAP, EXTENSION]
   >> EQ_TAC
   >- (PSET_TAC [PREFIX_SET_SCONS, EXTENSION]
       >> PROVE_TAC [])
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `b :: l'`
   >> PSET_TAC [PREFIX_SET_SCONS, EXTENSION]);

val PROB_CANON_PREFS_EMBED = store_thm
  ("PROB_CANON_PREFS_EMBED",
   ``!l b. prob_embed (prob_canon_prefs l b) = prob_embed (l :: b)``,
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [prob_canon_prefs_def]
   >> RW_TAC list_ss [prob_canon_prefs_def]
   >> PSET_TAC [prob_embed_def, MEM_MAP, MEM, GSYM PREFIX_SET_PREFIX_SUBSET,
                EXTENSION]
   >> Q.PAT_X_ASSUM `!x. P x = Q x` K_TAC
   >> EQ_TAC >- PROVE_TAC []
   >> RW_TAC std_ss []
   >> PROVE_TAC []);

val PROB_CANON_FIND_EMBED = store_thm
  ("PROB_CANON_FIND_EMBED",
   ``!l b. prob_embed (prob_canon_find l b) = prob_embed (l :: b)``,
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [prob_canon_find_def]
   >> PSET_TAC [prob_canon_find_def, GSYM PREFIX_SET_PREFIX_SUBSET,
                EXTENSION] >|
   [Q.PAT_X_ASSUM `!x. P x = Q x` K_TAC
    >> PSET_TAC [PROB_EMBED_CONS, EXTENSION]
    >> PROVE_TAC [],
    ONCE_REWRITE_TAC [PROB_EMBED_TRANSPOSE]
    >> ONCE_REWRITE_TAC [PROB_EMBED_CONS]
    >> PSET_TAC [EXTENSION],
    PSET_TAC [PROB_CANON_PREFS_EMBED, EXTENSION]]);

val PROB_CANON1_EMBED = store_thm
  ("PROB_CANON1_EMBED",
   ``!l. prob_embed (prob_canon1 l) = prob_embed l``,
   REWRITE_TAC [prob_canon1_def]
   >> Induct >- RW_TAC list_ss []
   >> STRIP_TAC
   >> POP_ASSUM MP_TAC
   >> MP_TAC PROB_CANON_FIND_EMBED
   >> RW_TAC list_ss [PROB_EMBED_CONS]);

val PROB_CANON_MERGE_EMBED = store_thm
  ("PROB_CANON_MERGE_EMBED",
   ``!l b. prob_embed (prob_canon_merge l b) = prob_embed (l :: b)``,
   Induct_on `b` >- RW_TAC std_ss [prob_canon_merge_def]
   >> RW_TAC list_ss [prob_canon_merge_def, prob_twin_def]
   >> POP_ASSUM (K ALL_TAC)
   >> RW_TAC std_ss [BUTLAST, PROB_EMBED_CONS]
   >> MP_TAC (Q.SPEC `l'` PREFIX_SET_TWINS)
   >> PSET_TAC [EXTENSION]
   >> PROVE_TAC []);

val PROB_CANON2_EMBED = store_thm
  ("PROB_CANON2_EMBED",
   ``!l. prob_embed (prob_canon2 l) = prob_embed l``,
   REWRITE_TAC [prob_canon2_def]
   >> Induct >- RW_TAC list_ss []
   >> STRIP_TAC
   >> POP_ASSUM MP_TAC
   >> MP_TAC PROB_CANON_MERGE_EMBED
   >> RW_TAC list_ss [PROB_EMBED_CONS]);

val PROB_CANON_EMBED = store_thm
  ("PROB_CANON_EMBED",
   ``!l. prob_embed (prob_canon l) = prob_embed l``,
   RW_TAC std_ss [prob_canon_def, PROB_CANON1_EMBED, PROB_CANON2_EMBED]);

val PROB_CANONICAL_UNIV = store_thm
  ("PROB_CANONICAL_UNIV",
   ``!l. prob_canonical l /\ (prob_embed l = UNIV) ==> (l = [[]])``,
   Suff `!l. prob_canonical l ==> (prob_embed l = UNIV) ==> (l = [[]])`
   >- PROVE_TAC []
   >> HO_MATCH_MP_TAC PROB_CANONICAL_INDUCT
   >> PSET_TAC [PROB_EMBED_BASIC, EXTENSION]
   >> Suff `F` >- PROVE_TAC []
   >> Q.PAT_X_ASSUM `prob_canonical x` MP_TAC
   >> Suff `(l = [[]]) /\ (l' = [[]])`
   >- RW_TAC prob_canon_ss [prob_canonical_def]
   >> CONJ_TAC >|
   [Q.PAT_X_ASSUM `x ==> (l = y)` MATCH_MP_TAC
    >> PSET_TAC [EXTENSION]
    >> POP_ASSUM (MP_TAC o Q.SPEC `scons T x`)
    >> PSET_TAC [PROB_EMBED_TLS, PROB_EMBED_APPEND, EXTENSION],
    Q.PAT_X_ASSUM `x ==> (l' = y)` MATCH_MP_TAC
    >> PSET_TAC [EXTENSION]
    >> POP_ASSUM (MP_TAC o Q.SPEC `scons F x`)
    >> PSET_TAC [PROB_EMBED_TLS, PROB_EMBED_APPEND, EXTENSION]]);

val PROB_CANON_REP = store_thm
  ("PROB_CANON_REP",
   ``!b c.
       (prob_canon b = prob_canon c) = (prob_embed b = prob_embed c)``,
   REPEAT STRIP_TAC
   >> EQ_TAC >- PROVE_TAC [PROB_CANON_EMBED]
   >> Suff `!b. prob_canonical b ==> (!c. prob_canonical c ==>
                  (prob_embed b = prob_embed c) ==> (b = c))`
   >- (DISCH_THEN (MP_TAC o Q.SPEC `prob_canon b`)
       >> RW_TAC std_ss [prob_canonical_def, PROB_CANON_IDEMPOT]
       >> Q.PAT_X_ASSUM `!c. P c` (MP_TAC o Q.SPEC `prob_canon c`)
       >> RW_TAC std_ss [PROB_CANON_IDEMPOT, PROB_CANON_EMBED])
   >> HO_MATCH_MP_TAC PROB_CANONICAL_INDUCT
   >> CONJ_TAC
   >- (Cases >- RW_TAC std_ss []
       >> PSET_TAC [PROB_EMBED_NIL, PROB_EMBED_CONS, FOLDR, EXTENSION]
       >> PROVE_TAC [PREFIX_SET_POPULATED])
   >> CONJ_TAC >- PROVE_TAC [PROB_EMBED_BASIC, PROB_CANONICAL_UNIV]
   >> RW_TAC std_ss []
   >> NTAC 2 (POP_ASSUM MP_TAC)
   >> Q.SPEC_TAC (`c`, `c`)
   >> HO_MATCH_MP_TAC PROB_CANONICAL_CASES
   >> CONJ_TAC
   >- (PSET_TAC [PROB_EMBED_NIL, PROB_EMBED_CONS, FOLDR, EXTENSION]
       >> reverse (Cases_on `b`)
       >- (PSET_TAC [PROB_EMBED_NIL, FOLDR, APPEND, MAP, PROB_EMBED_CONS,
                     EXTENSION]
           >> PROVE_TAC [PREFIX_SET_POPULATED])
       >> reverse (Cases_on `b'`)
       >- (PSET_TAC [PROB_EMBED_NIL, FOLDR, APPEND, MAP, PROB_EMBED_CONS,
                     EXTENSION]
           >> PROVE_TAC [PREFIX_SET_POPULATED])
       >> RW_TAC list_ss [MAP])
   >> CONJ_TAC >- PROVE_TAC [PROB_EMBED_BASIC, PROB_CANONICAL_UNIV]
   >> RW_TAC std_ss []
   >> Suff `(b = l1) /\ (b' = l2)` >- RW_TAC std_ss []
   >> CONJ_TAC >|
   [Suff `prob_embed b = prob_embed l1` >- PROVE_TAC []
    >> POP_ASSUM MP_TAC
    >> KILL_TAC
    >> PSET_TAC [PROB_EMBED_APPEND, EXTENSION]
    >> POP_ASSUM (MP_TAC o Q.SPEC `scons T x`)
    >> RW_TAC std_ss [PROB_EMBED_TLS],
    Suff `prob_embed b' = prob_embed l2` >- PROVE_TAC []
    >> POP_ASSUM MP_TAC
    >> KILL_TAC
    >> PSET_TAC [PROB_EMBED_APPEND, EXTENSION]
    >> POP_ASSUM (MP_TAC o Q.SPEC `scons F x`)
    >> RW_TAC std_ss [PROB_EMBED_TLS]]);

val PROB_CANONICAL_EMBED_EMPTY = store_thm
  ("PROB_CANONICAL_EMBED_EMPTY",
   ``!l. prob_canonical l ==> ((prob_embed l = {}) = (l = []))``,
   RW_TAC std_ss []
   >> reverse EQ_TAC >- PSET_TAC [PROB_EMBED_BASIC, EXTENSION]
   >> RW_TAC std_ss []
   >> Suff `prob_canon l = prob_canon []`
   >- PROVE_TAC [prob_canonical_def, PROB_CANON_BASIC]
   >> PSET_TAC [PROB_CANON_REP, PROB_EMBED_BASIC, EXTENSION]);

val PROB_CANONICAL_EMBED_UNIV = store_thm
  ("PROB_CANONICAL_EMBED_UNIV",
   ``!l. prob_canonical l ==> ((prob_embed l = UNIV) = (l = [[]]))``,
   RW_TAC std_ss []
   >> reverse EQ_TAC >- PSET_TAC [PROB_EMBED_BASIC, EXTENSION]
   >> RW_TAC std_ss []
   >> Suff `prob_canon l = prob_canon [[]]`
   >- PROVE_TAC [prob_canonical_def, PROB_CANON_BASIC]
   >> PSET_TAC [PROB_CANON_REP, PROB_EMBED_BASIC, EXTENSION]);

val IN_PROB_ALGEBRA = store_thm
  ("IN_PROB_ALGEBRA",
   ``!x. x IN (subsets prob_algebra) = (?b. x = prob_embed b)``,
   RW_TAC std_ss [prob_algebra_def, subsets_def, GSPECIFICATION]);

val PROB_EMBED_ALGEBRA = store_thm
  ("PROB_EMBED_ALGEBRA",
   ``!b. (prob_embed b) IN (subsets prob_algebra)``,
   PROVE_TAC [IN_PROB_ALGEBRA, subsets_def]);

val SPACE_PROB_ALGEBRA = store_thm
  ("SPACE_PROB_ALGEBRA", ``space prob_algebra = UNIV``,
    PROVE_TAC [prob_algebra_def, space_def]);

val SPACE_SUBSETS_PROB_ALGEBRA = store_thm
  ("SPACE_SUBSETS_PROB_ALGEBRA",
  ``(space prob_algebra, subsets prob_algebra) = prob_algebra``,
    REWRITE_TAC [prob_algebra_def, space_def, subsets_def]);

val PROB_ALGEBRA_EMPTY = store_thm
  ("PROB_ALGEBRA_EMPTY",
   ``{} IN (subsets prob_algebra)``,
   PROVE_TAC [IN_PROB_ALGEBRA, PROB_EMBED_BASIC, subsets_def]);

val PROB_ALGEBRA_UNION = store_thm
  ("PROB_ALGEBRA_UNION",
   ``!s t. s IN (subsets prob_algebra) /\ t IN (subsets prob_algebra)
        ==> (s UNION t) IN (subsets prob_algebra)``,
    PSET_TAC [IN_PROB_ALGEBRA, EXTENSION, subsets_def]
 >> Q.EXISTS_TAC `APPEND b b'`
 >> PSET_TAC [PROB_EMBED_APPEND, EXTENSION]);

val PROB_ALGEBRA_COMPL = store_thm
  ("PROB_ALGEBRA_COMPL",
  ``!s. s IN (subsets prob_algebra) ==> COMPL s IN (subsets prob_algebra)``,
      PSET_TAC [IN_PROB_ALGEBRA, EXTENSION, subsets_def]
   >> POP_ASSUM MP_TAC
   >> Suff `!l. prob_canonical l ==>
                  (?l'. COMPL (prob_embed l) = prob_embed l')`
   >- (DISCH_THEN (MP_TAC o Q.SPEC `prob_canon b`)
       >> PSET_TAC [prob_canonical_def, PROB_CANON_EMBED, PROB_CANON_IDEMPOT,
                    EXTENSION])
   >> HO_MATCH_MP_TAC PROB_CANONICAL_INDUCT
   >> CONJ_TAC
   >- (Q.EXISTS_TAC `[[]]`
       >> PSET_TAC [PROB_EMBED_BASIC, EXTENSION])
   >> CONJ_TAC
   >- (Q.EXISTS_TAC `[]`
       >> PSET_TAC [PROB_EMBED_BASIC, EXTENSION])
   >> PSET_TAC [EXTENSION]
   >> Q.EXISTS_TAC `APPEND (MAP (CONS T) l'') (MAP (CONS F) l''')`
   >> STRIP_TAC
   >> SEQ_CASES_TAC `x`
   >> PSET_TAC [PROB_EMBED_APPEND, PROB_EMBED_TLS, EXTENSION]
   >> PROVE_TAC []);

val PROB_ALGEBRA_ALGEBRA = store_thm
  ("PROB_ALGEBRA_ALGEBRA", ``algebra prob_algebra``,
    RW_TAC std_ss [algebra_def, subset_class_def, prob_algebra_def, space_def, subsets_def,
                   PROB_ALGEBRA_EMPTY, PROB_ALGEBRA_UNION, IN_UNIV, SUBSET_UNIV]
 >> REWRITE_TAC [GSYM COMPL_DEF]
 >> POP_ASSUM MP_TAC
 >> REWRITE_TAC [GSYM (REWRITE_CONV [subsets_def, prob_algebra_def] ``subsets prob_algebra``)]
 >> REWRITE_TAC [PROB_ALGEBRA_COMPL]);

val PROB_ALGEBRA_UNIV = store_thm
  ("PROB_ALGEBRA_UNIV", ``UNIV IN (subsets prob_algebra)``,
    `UNIV = space prob_algebra` by PROVE_TAC [prob_algebra_def, space_def]
 >> PROVE_TAC [PROB_ALGEBRA_ALGEBRA, ALGEBRA_SPACE]);

val PROB_ALGEBRA_INTER = store_thm
  ("PROB_ALGEBRA_INTER",
  ``!s t. s IN (subsets prob_algebra) /\ t IN (subsets prob_algebra)
        ==> (s INTER t) IN (subsets prob_algebra)``,
    ASSUME_TAC PROB_ALGEBRA_ALGEBRA
 >> ASSUME_TAC (ISPEC ``prob_algebra`` ALGEBRA_INTER)
 >> FULL_SIMP_TAC std_ss [subsets_def]);

val PROB_ALGEBRA_HALFSPACE = store_thm
  ("PROB_ALGEBRA_HALFSPACE",
   ``!b. halfspace b IN (subsets prob_algebra)``,
   PSET_TAC [IN_PROB_ALGEBRA, EXTENSION]
   >> Q.EXISTS_TAC `[[b]]`
   >> PSET_TAC [IN_PROB_EMBED, IN_HALFSPACE, MEM_MAP, MEM, prefix_set_def,
                EXTENSION]);

val PROB_ALGEBRA_BASIC = store_thm
  ("PROB_ALGEBRA_BASIC",
   ``{} IN (subsets prob_algebra) /\
     UNIV IN (subsets prob_algebra) /\
     (!b. halfspace b IN (subsets prob_algebra))``,
   PROVE_TAC [PROB_ALGEBRA_EMPTY, PROB_ALGEBRA_UNIV, PROB_ALGEBRA_HALFSPACE]);

val PROB_ALGEBRA_STL = store_thm
  ("PROB_ALGEBRA_STL",
   ``!p. (p o stl) IN (subsets prob_algebra) = p IN (subsets prob_algebra)``,
   RW_TAC std_ss [IN_PROB_ALGEBRA]
   >> reverse EQ_TAC
   >- (PSET_TAC [o_DEF, EXTENSION]
       >> Q.EXISTS_TAC `APPEND (MAP (CONS T) b) (MAP (CONS F) b)`
       >> PSET_TAC [PROB_EMBED_APPEND, EXTENSION]
       >> SEQ_CASES_TAC `x`
       >> RW_TAC std_ss [STL_SCONS, PROB_EMBED_TLS]
       >> PROVE_TAC [])
   >> STRIP_TAC
   >> POP_ASSUM MP_TAC
   >> Suff
      `!b.
         prob_canonical b ==>
         (p o stl = prob_embed b) ==> ?b'. (p = prob_embed b')`
   >- (DISCH_THEN (MP_TAC o Q.SPEC `prob_canon b`)
       >> RW_TAC std_ss [prob_canonical_def, PROB_CANON_IDEMPOT,
                         PROB_CANON_EMBED])
   >> HO_MATCH_MP_TAC PROB_CANONICAL_CASES
   >> CONJ_TAC
   >- (PSET_TAC [PROB_EMBED_BASIC, EXTENSION]
       >> Q.EXISTS_TAC `[]`
       >> PSET_TAC [PROB_EMBED_BASIC, EXTENSION]
       >> POP_ASSUM (MP_TAC o Q.SPEC `scons T x`)
       >> RW_TAC std_ss [STL_SCONS])
   >> CONJ_TAC
   >- (PSET_TAC [PROB_EMBED_BASIC, EXTENSION]
       >> Q.EXISTS_TAC `[[]]`
       >> PSET_TAC [PROB_EMBED_BASIC, EXTENSION]
       >> POP_ASSUM (MP_TAC o Q.SPEC `scons T x`)
       >> RW_TAC std_ss [STL_SCONS])
   >> PSET_TAC [EXTENSION]
   >> Q.EXISTS_TAC `l1`
   >> STRIP_TAC
   >> POP_ASSUM (MP_TAC o Q.SPEC `scons T x`)
   >> PSET_TAC [PROB_EMBED_APPEND, STL_SCONS, PROB_EMBED_TLS, EXTENSION]);

val PROB_ALGEBRA_SDROP = store_thm
  ("PROB_ALGEBRA_SDROP",
   ``!n p. (p o sdrop n) IN (subsets prob_algebra) = p IN (subsets prob_algebra)``,
   Induct >- RW_TAC std_ss' [sdrop_def, o_DEF, I_THM]
   >> RW_TAC bool_ss [sdrop_def, o_ASSOC, PROB_ALGEBRA_STL]);

val PROB_ALGEBRA_INTER_HALVES = store_thm
  ("PROB_ALGEBRA_INTER_HALVES",
   ``!p.
       (halfspace T INTER p) IN (subsets prob_algebra) /\
       (halfspace F INTER p) IN (subsets prob_algebra) =
       p IN (subsets prob_algebra)``,
   STRIP_TAC
   >> reverse EQ_TAC >- PROVE_TAC [PROB_ALGEBRA_INTER, PROB_ALGEBRA_HALFSPACE]
   >> REPEAT STRIP_TAC
   >> Suff `(halfspace T INTER p) UNION (halfspace F INTER p) = p`
   >- PROVE_TAC [PROB_ALGEBRA_UNION]
   >> KILL_TAC
   >> PSET_TAC [IN_HALFSPACE, EXTENSION]
   >> PROVE_TAC []);

val PROB_ALGEBRA_HALVES = store_thm
  ("PROB_ALGEBRA_HALVES",
   ``!p q.
       (halfspace T INTER p) UNION (halfspace F INTER q) IN (subsets prob_algebra) =
       (halfspace T INTER p) IN (subsets prob_algebra) /\
       (halfspace F INTER q) IN (subsets prob_algebra)``,
   REPEAT STRIP_TAC
   >> reverse EQ_TAC >- PROVE_TAC [PROB_ALGEBRA_UNION]
   >> REPEAT STRIP_TAC >|
   [Suff
    `halfspace T INTER p =
     halfspace T INTER (halfspace T INTER p UNION halfspace F INTER q)`
    >- PROVE_TAC [PROB_ALGEBRA_HALFSPACE, PROB_ALGEBRA_INTER]
    >> KILL_TAC
    >> PSET_TAC [IN_HALFSPACE, EXTENSION]
    >> PROVE_TAC [],
    Suff
    `halfspace F INTER q =
     halfspace F INTER (halfspace T INTER p UNION halfspace F INTER q)`
    >- PROVE_TAC [PROB_ALGEBRA_HALFSPACE, PROB_ALGEBRA_INTER]
    >> KILL_TAC
    >> PSET_TAC [IN_HALFSPACE, EXTENSION]
    >> PROVE_TAC []]);

val PROB_ALGEBRA_INTER_SHD = store_thm
  ("PROB_ALGEBRA_INTER_SHD",
   ``!b p. (halfspace b INTER p o stl) IN (subsets prob_algebra) = p IN (subsets prob_algebra)``,
   RW_TAC std_ss []
   >> reverse EQ_TAC
   >- PROVE_TAC [PROB_ALGEBRA_STL, PROB_ALGEBRA_HALFSPACE, PROB_ALGEBRA_INTER]
   >> PSET_TAC [IN_PROB_ALGEBRA, IN_HALFSPACE, EXTENSION]
   >> POP_ASSUM MP_TAC
   >> Suff
      `!c.
         prob_canonical c ==>
         (!v. (shd v = b) /\ stl v IN p = v IN prob_embed c) ==>
         ?d. !v. v IN p = v IN prob_embed d`
   >- (DISCH_THEN (MP_TAC o Q.SPEC `prob_canon b'`)
       >> RW_TAC std_ss [PROB_CANON_EMBED, PROB_CANON_IDEMPOT, prob_canonical_def])
   >> HO_MATCH_MP_TAC PROB_CANONICAL_CASES
   >> CONJ_TAC
   >- (PSET_TAC [PROB_EMBED_BASIC, EXTENSION]
       >> Q.EXISTS_TAC `[]`
       >> STRIP_TAC
       >> POP_ASSUM (MP_TAC o Q.SPEC `scons b v`)
       >> PSET_TAC [PROB_EMBED_BASIC, SHD_SCONS, STL_SCONS, EXTENSION])
   >> CONJ_TAC
   >- (PSET_TAC [PROB_EMBED_BASIC, EXTENSION]
       >> Q.EXISTS_TAC `[[]]`
       >> STRIP_TAC
       >> POP_ASSUM (MP_TAC o Q.SPEC `scons b v`)
       >> PSET_TAC [PROB_EMBED_BASIC, SHD_SCONS, STL_SCONS, EXTENSION])
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `if b then l1 else l2`
   >> STRIP_TAC
   >> POP_ASSUM (MP_TAC o Q.SPEC `scons b v`)
   >> PSET_TAC [PROB_EMBED_APPEND, PROB_EMBED_TLS, SHD_SCONS,
                STL_SCONS, EXTENSION]);

val PROB_TWINS_MEASURE = store_thm
  ("PROB_TWINS_MEASURE",
  ``!l.
       (1 / 2):real pow LENGTH (SNOC T l) + (1 / 2) pow LENGTH (SNOC F l) =
       (1 / 2) pow LENGTH l``,
    RW_TAC std_ss [LENGTH_SNOC]
 >> REWRITE_TAC [Q.SPEC `LENGTH (l :bool list)` POW_HALF_TWICE]
 >> REAL_ARITH_TAC);

val PROB_PREMEASURE_BASIC = store_thm
  ("PROB_PREMEASURE_BASIC",
   ``(prob_premeasure [] = 0) /\ (prob_premeasure [[]] = 1) /\
     (!b. prob_premeasure [[b]] = 1 / 2)``,
   RW_TAC real_ss [prob_premeasure_def, LENGTH, pow]);

val PROB_PREMEASURE_POS = store_thm
  ("PROB_PREMEASURE_POS",
   ``!l. 0 <= prob_premeasure l``,
   Induct >- PROVE_TAC [prob_premeasure_def, REAL_ARITH ``(0:real) <= 0``]
   >> RW_TAC list_ss [prob_premeasure_def]
   >> PROVE_TAC [REAL_ARITH ``(0:real) < a /\ 0 <= b ==> 0 <= a + b``,
                 POW_HALF_POS]);

val PROB_PREMEASURE_APPEND = store_thm
  ("PROB_PREMEASURE_APPEND",
   ``!l1 l2. prob_premeasure (APPEND l1 l2) = prob_premeasure l1 + prob_premeasure l2``,
   NTAC 2 STRIP_TAC
   >> Induct_on `l1`
   >- (RW_TAC list_ss [prob_premeasure_def, APPEND] >> REAL_ARITH_TAC)
   >> RW_TAC list_ss [prob_premeasure_def, APPEND]
   >> REAL_ARITH_TAC);

val PROB_PREMEASURE_TLS = store_thm
  ("PROB_PREMEASURE_TLS",
   ``!l b. 2 * prob_premeasure (MAP (CONS b) l) = prob_premeasure l``,
   Induct >- (RW_TAC list_ss [prob_premeasure_def] >> REAL_ARITH_TAC)
   >> RW_TAC list_ss [prob_premeasure_def, MAP, pow]
   >> REWRITE_TAC [REAL_ADD_LDISTRIB, REAL_MUL_ASSOC, HALF_CANCEL,
                   REAL_MUL_LID]
   >> PROVE_TAC []);

val PROB_CANON_PREFS_MONO = store_thm
  ("PROB_CANON_PREFS_MONO",
   ``!l b. prob_premeasure (prob_canon_prefs l b) <= prob_premeasure (l :: b)``,
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [prob_canon_prefs_def, REAL_LE_REFL]
   >> reverse (RW_TAC list_ss [prob_canon_prefs_def])
   >- PROVE_TAC [REAL_LE_REFL]
   >> Suff `prob_premeasure (l::b) <= prob_premeasure (l::h::b)`
   >- PROVE_TAC [REAL_LE_TRANS]
   >> KILL_TAC
   >> RW_TAC list_ss [prob_premeasure_def]
   >> ASSUME_TAC (SPEC ``LENGTH (h:bool list)`` POW_HALF_POS)
   >> PROVE_TAC [REAL_ARITH ``0 < (x:real) ==> a + b <= a + (x + b)``]);

val PROB_CANON_FIND_MONO = store_thm
  ("PROB_CANON_FIND_MONO",
   ``!l b. prob_premeasure (prob_canon_find l b) <= prob_premeasure (l :: b)``,
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [prob_canon_find_def, REAL_LE_REFL]
   >> RW_TAC list_ss [prob_canon_find_def] >|
   [KILL_TAC
    >> REWRITE_TAC [prob_premeasure_def]
    >> ASSUME_TAC (SPEC ``LENGTH (l:bool list)`` POW_HALF_POS)
    >> PROVE_TAC [REAL_ARITH ``0 < (x:real) ==> a <= x + a``],
    NTAC 2 (POP_ASSUM (K ALL_TAC))
    >> POP_ASSUM MP_TAC
    >> REWRITE_TAC [prob_premeasure_def]
    >> REAL_ARITH_TAC,
    PROVE_TAC [PROB_CANON_PREFS_MONO]]);

val PROB_CANON1_MONO = store_thm
  ("PROB_CANON1_MONO",
   ``!l. prob_premeasure (prob_canon1 l) <= prob_premeasure l``,
   REWRITE_TAC [prob_canon1_def]
   >> Induct >- RW_TAC list_ss [REAL_LE_REFL, FOLDR]
   >> RW_TAC list_ss [FOLDR]
   >> Suff `prob_premeasure (h::FOLDR prob_canon_find [] l)
                   <= prob_premeasure (h::l)`
   >- PROVE_TAC [PROB_CANON_FIND_MONO, REAL_LE_TRANS]
   >> PROVE_TAC [prob_premeasure_def, REAL_LE_LADD]);

val PROB_CANON_MERGE_MONO = store_thm
  ("PROB_CANON_MERGE_MONO",
   ``!l b. prob_premeasure (prob_canon_merge l b) <= prob_premeasure (l::b)``,
   Induct_on `b` >- RW_TAC real_ss [prob_canon_merge_def, REAL_LE_REFL]
   >> RW_TAC real_ss [prob_canon_merge_def, prob_twin_def]
   >> RW_TAC std_ss [BUTLAST]
   >> Suff `prob_premeasure (l'::b) <= prob_premeasure (SNOC T l'::SNOC F l'::b)`
   >- PROVE_TAC [REAL_LE_TRANS]
   >> KILL_TAC
   >> RW_TAC std_ss [prob_premeasure_def, REAL_ADD_ASSOC, PROB_TWINS_MEASURE,
                     REAL_LE_REFL]);

val PROB_CANON2_MONO = store_thm
  ("PROB_CANON2_MONO",
   ``!l. prob_premeasure (prob_canon2 l) <= prob_premeasure l``,
   REWRITE_TAC [prob_canon2_def]
   >> Induct >- RW_TAC list_ss [REAL_LE_REFL, FOLDR]
   >> RW_TAC list_ss [FOLDR]
   >> Suff `prob_premeasure (h::FOLDR prob_canon_merge [] l)
                   <= prob_premeasure (h::l)`
   >- PROVE_TAC [PROB_CANON_MERGE_MONO, REAL_LE_TRANS]
   >> PROVE_TAC [prob_premeasure_def, REAL_LE_LADD]);

val PROB_CANON_MONO = store_thm
  ("PROB_CANON_MONO",
   ``!l. prob_premeasure (prob_canon l) <= prob_premeasure l``,
   RW_TAC std_ss [prob_canon_def]
   >> PROVE_TAC [PROB_CANON1_MONO, PROB_CANON2_MONO, REAL_LE_TRANS]);

val PROB_MEASURE_ALT = store_thm
  ("PROB_MEASURE_ALT",
   ``!l. prob_measure (prob_embed l) = prob_premeasure (prob_canon l)``,
   RW_TAC std_ss [prob_measure_def]
   >> HO_MATCH_MP_TAC REAL_INF_MIN
   >> RW_TAC std_ss [GSPECIFICATION]
   >- PROVE_TAC [PROB_CANON_REP, PROB_CANON_IDEMPOT]
   >> Suff `prob_premeasure (prob_canon c) <= prob_premeasure c`
   >- PROVE_TAC [PROB_CANON_REP]
   >> PROVE_TAC [PROB_CANON_MONO]);

val PROB_MEASURE_BASIC = store_thm
  ("PROB_MEASURE_BASIC",
   ``(prob_measure {} = 0) /\ (prob_measure UNIV = 1) /\
     (!b. prob_measure (halfspace b) = 1 / 2)``,
   RW_TAC std_ss [GSYM PROB_EMBED_BASIC, PROB_MEASURE_ALT,
                  PROB_CANON_BASIC, PROB_PREMEASURE_BASIC]);

val PROB_CANONICAL_MEASURE_MAX = store_thm
  ("PROB_CANONICAL_MEASURE_MAX",
   ``!l. prob_canonical l ==> prob_premeasure l <= 1``,
   HO_MATCH_MP_TAC PROB_CANONICAL_INDUCT
   >> CONJ_TAC >- (RW_TAC list_ss [prob_premeasure_def] >> REAL_ARITH_TAC)
   >> CONJ_TAC >- (RW_TAC list_ss [prob_premeasure_def, pow] >> REAL_ARITH_TAC)
   >> RW_TAC list_ss [PROB_PREMEASURE_APPEND]
   >> Suff `(2 * prob_premeasure (MAP (CONS T) l) = prob_premeasure l) /\
            (2 * prob_premeasure (MAP (CONS F) l') = prob_premeasure l')`
   >- PROVE_TAC [REAL_ARITH ``(2 * a = b) /\ (2 * c = d) /\ b <= 1 /\ d <= 1
                              ==> a + c <= (1:real)``]
   >> PROVE_TAC [PROB_PREMEASURE_TLS]);

val PROB_MEASURE_MAX = store_thm
  ("PROB_MEASURE_MAX",
   ``!l. l IN (subsets prob_algebra) ==> prob_measure l <= 1``,
   RW_TAC std_ss [IN_PROB_ALGEBRA]
   >> RW_TAC std_ss [PROB_MEASURE_ALT]
   >> MP_TAC (Q.SPEC `prob_canon b` PROB_CANONICAL_MEASURE_MAX)
   >> RW_TAC std_ss [prob_canonical_def, PROB_CANON_IDEMPOT]);

val PROB_PREMEASURE_COMPL = store_thm
  ("PROB_PREMEASURE_COMPL",
   ``!b.
       prob_canonical b ==>
       !c.
         prob_canonical c ==>
         (COMPL (prob_embed b) = prob_embed c) ==>
         (prob_premeasure b + prob_premeasure c = 1)``,
   HO_MATCH_MP_TAC PROB_CANONICAL_INDUCT
   >> CONJ_TAC
   >- (PSET_TAC [PROB_PREMEASURE_BASIC, PROB_EMBED_BASIC, EXTENSION]
       >> Know `prob_canon c = prob_canon [[]]`
       >- PSET_TAC [PROB_CANON_REP, PROB_EMBED_BASIC, EXTENSION]
       >> PSET_TAC [PROB_CANON_BASIC, prob_canonical_def, PROB_EMBED_BASIC,
                    PROB_PREMEASURE_BASIC, REAL_ADD_LID, EXTENSION])
   >> CONJ_TAC
   >- (PSET_TAC [PROB_PREMEASURE_BASIC, PROB_EMBED_BASIC, EXTENSION]
       >> Know `prob_canon c = prob_canon []`
       >- PSET_TAC [PROB_CANON_REP, PROB_EMBED_BASIC, EXTENSION]
       >> PSET_TAC [PROB_CANON_BASIC, prob_canonical_def, PROB_EMBED_BASIC,
                    PROB_PREMEASURE_BASIC, REAL_ADD_RID, EXTENSION])
   >> PSET_TAC [PROB_PREMEASURE_BASIC, PROB_EMBED_BASIC, EXTENSION]
   >> NTAC 2 (POP_ASSUM MP_TAC)
   >> Q.SPEC_TAC (`c`, `c`)
   >> HO_MATCH_MP_TAC PROB_CANONICAL_CASES
   >> CONJ_TAC
   >- (PSET_TAC [PROB_EMBED_BASIC, PROB_PREMEASURE_BASIC, EXTENSION]
       >> Suff `APPEND (MAP (CONS T) b) (MAP (CONS F) b') = [[]]`
       >- PROVE_TAC [MEM_NIL_STEP, MEM]
       >> PSET_TAC [GSYM PROB_CANONICAL_EMBED_UNIV, EXTENSION])
   >> CONJ_TAC
   >- (PSET_TAC [PROB_EMBED_BASIC, PROB_PREMEASURE_BASIC, EXTENSION]
       >> Know `APPEND (MAP (CONS T) b) (MAP (CONS F) b') = []`
       >- PSET_TAC [GSYM PROB_CANONICAL_EMBED_EMPTY, EXTENSION]
       >> RW_TAC std_ss [PROB_PREMEASURE_BASIC, REAL_ADD_LID])
   >> RW_TAC std_ss []
   >> Know `!a b : real. (2 * a + 2 * b = 1 + 1) ==> (a + b = 1)`
   >- REAL_ARITH_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> PSET_TAC [PROB_EMBED_APPEND, PROB_PREMEASURE_APPEND, PROB_PREMEASURE_TLS,
                REAL_ADD_LDISTRIB, EXTENSION]
   >> Suff
      `(prob_premeasure b + prob_premeasure l1 = 1) /\
       (prob_premeasure b' + prob_premeasure l2 = 1)`
   >- REAL_ARITH_TAC
   >> CONJ_TAC >|
   [Suff `!v. ~(v IN prob_embed b) = v IN prob_embed l1`
    >- PROVE_TAC []
    >> STRIP_TAC
    >> POP_ASSUM (MP_TAC o Q.SPEC `scons T v`)
    >> RW_TAC std_ss [PROB_EMBED_TLS, SHD_SCONS, STL_SCONS],
    Suff `!v. ~(v IN prob_embed b') = v IN prob_embed l2`
    >- PROVE_TAC []
    >> STRIP_TAC
    >> POP_ASSUM (MP_TAC o Q.SPEC `scons F v`)
    >> RW_TAC std_ss [PROB_EMBED_TLS, SHD_SCONS, STL_SCONS]]);

val PROB_PREMEASURE_ADDITIVE = store_thm
  ("PROB_PREMEASURE_ADDITIVE",
   ``!b.
       prob_canonical b ==>
       !c.
         prob_canonical c ==>
         !d.
           prob_canonical d ==>
           (prob_embed c INTER prob_embed d = {}) /\
           (prob_embed b = prob_embed c UNION prob_embed d) ==>
           (prob_premeasure b = prob_premeasure c + prob_premeasure d)``,
   HO_MATCH_MP_TAC PROB_CANONICAL_INDUCT
   >> CONJ_TAC
   >- (PSET_TAC [PROB_PREMEASURE_BASIC, PROB_EMBED_BASIC, EXTENSION]
       >> Know `c = []` >- PSET_TAC [GSYM PROB_CANONICAL_EMBED_EMPTY, EXTENSION]
       >> Know `d = []` >- PSET_TAC [GSYM PROB_CANONICAL_EMBED_EMPTY, EXTENSION]
       >> RW_TAC real_ss [PROB_PREMEASURE_BASIC])
   >> CONJ_TAC
   >- (PSET_TAC [PROB_PREMEASURE_BASIC, PROB_EMBED_BASIC, EXTENSION]
       >> MP_TAC (Q.SPEC `c` PROB_PREMEASURE_COMPL)
       >> ASM_REWRITE_TAC []
       >> DISCH_THEN (MP_TAC o Q.SPEC `d`)
       >> PSET_TAC [EXTENSION]
       >> PROVE_TAC [])
   >> RW_TAC std_ss []
   >> NTAC 4 (POP_ASSUM MP_TAC)
   >> Q.SPEC_TAC (`c`, `c`)
   >> HO_MATCH_MP_TAC PROB_CANONICAL_CASES
   >> CONJ_TAC
   >- (PSET_TAC [PROB_PREMEASURE_BASIC, PROB_EMBED_BASIC, EXTENSION]
       >> Suff `d = APPEND (MAP (CONS T) b) (MAP (CONS F) b')`
       >- RW_TAC real_ss []
       >> Suff
          `prob_canon d = prob_canon (APPEND (MAP (CONS T) b) (MAP (CONS F) b'))`
       >- PROVE_TAC [prob_canonical_def]
       >> PSET_TAC [PROB_CANON_REP, EXTENSION])
   >> CONJ_TAC
   >- (PSET_TAC [PROB_PREMEASURE_BASIC, PROB_EMBED_BASIC, EXTENSION]
       >> Suff `APPEND (MAP (CONS T) b) (MAP (CONS F) b') = [[]]`
       >- PROVE_TAC [MEM_NIL_STEP, MEM]
       >> PSET_TAC [GSYM PROB_CANONICAL_EMBED_UNIV, EXTENSION])
   >> RW_TAC std_ss []
   >> NTAC 3 (POP_ASSUM MP_TAC)
   >> Q.SPEC_TAC (`d`, `d`)
   >> HO_MATCH_MP_TAC PROB_CANONICAL_CASES
   >> CONJ_TAC
   >- (PSET_TAC [PROB_PREMEASURE_BASIC, PROB_EMBED_BASIC, EXTENSION]
       >> Suff
          `APPEND (MAP (CONS T) b) (MAP (CONS F) b') =
           APPEND (MAP (CONS T) l1) (MAP (CONS F) l2)`
       >- RW_TAC real_ss []
       >> Suff
          `prob_canon (APPEND (MAP (CONS T) b) (MAP (CONS F) b')) =
           prob_canon (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))`
       >- PSET_TAC [prob_canonical_def, EXTENSION]
       >> PSET_TAC [PROB_CANON_REP, EXTENSION])
   >> CONJ_TAC
   >- (PSET_TAC [PROB_PREMEASURE_BASIC, PROB_EMBED_BASIC, EXTENSION]
       >> Suff `APPEND (MAP (CONS T) b) (MAP (CONS F) b') = [[]]`
       >- PROVE_TAC [MEM_NIL_STEP, MEM]
       >> PSET_TAC [GSYM PROB_CANONICAL_EMBED_UNIV, EXTENSION])
   >> RW_TAC std_ss []
   >> Know `!a b : real. (2 * a = 2 * b) ==> (a = b)`
   >- REAL_ARITH_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> RW_TAC std_ss [REAL_ADD_LDISTRIB, PROB_PREMEASURE_APPEND, PROB_PREMEASURE_TLS,
                     PROB_EMBED_APPEND]
   >> Suff
      `(prob_premeasure b = prob_premeasure l1 + prob_premeasure l1') /\
       (prob_premeasure b' = prob_premeasure l2 + prob_premeasure l2')`
   >- (RW_TAC real_ss [] >> METIS_TAC [REAL_ADD_COMM, REAL_ADD_ASSOC])
   >> CONJ_TAC >|
   [Suff
    `(prob_embed l1 INTER prob_embed l1' = {}) /\
     (prob_embed b = prob_embed l1 UNION prob_embed l1')`
    >- (Q.PAT_X_ASSUM
        `!c.
           prob_canonical c ==>
           !d.
             prob_canonical d ==>
             (prob_embed c INTER prob_embed d = {}) /\
             (prob_embed b = prob_embed c UNION prob_embed d) ==>
             (prob_premeasure b = prob_premeasure c + prob_premeasure d)`
        (MP_TAC o Q.SPEC `l1`)
        >> RW_TAC std_ss [])
    >> CONJ_TAC >|
    [POP_ASSUM K_TAC
     >> POP_ASSUM MP_TAC
     >> RW_TAC std_ss [EXTENSION, IN_INTER, NOT_IN_EMPTY]
     >> POP_ASSUM (MP_TAC o Q.SPEC `scons T x`)
     >> RW_TAC std_ss [PROB_EMBED_TLS, STL_SCONS, SHD_SCONS,
                       PROB_EMBED_APPEND, IN_UNION],
     POP_ASSUM MP_TAC
     >> POP_ASSUM K_TAC
     >> RW_TAC std_ss [EXTENSION, IN_UNION]
     >> POP_ASSUM (MP_TAC o Q.SPEC `scons T x`)
     >> RW_TAC std_ss [PROB_EMBED_TLS, STL_SCONS, SHD_SCONS,
                       PROB_EMBED_APPEND, IN_UNION]],
    Suff
    `(prob_embed l2 INTER prob_embed l2' = {}) /\
     (prob_embed b' = prob_embed l2 UNION prob_embed l2')`
    >- (Q.PAT_X_ASSUM
        `!c.
           prob_canonical c ==>
           !d.
             prob_canonical d ==>
             (prob_embed c INTER prob_embed d = {}) /\
             (prob_embed b' = prob_embed c UNION prob_embed d) ==>
             (prob_premeasure b' = prob_premeasure c + prob_premeasure d)`
        (MP_TAC o Q.SPEC `l2`)
        >> RW_TAC std_ss [])
    >> CONJ_TAC >|
    [POP_ASSUM K_TAC
     >> POP_ASSUM MP_TAC
     >> RW_TAC std_ss [EXTENSION, IN_INTER, NOT_IN_EMPTY]
     >> POP_ASSUM (MP_TAC o Q.SPEC `scons F x`)
     >> RW_TAC std_ss [PROB_EMBED_TLS, STL_SCONS, SHD_SCONS,
                       PROB_EMBED_APPEND, IN_UNION],
     POP_ASSUM MP_TAC
     >> POP_ASSUM K_TAC
     >> RW_TAC std_ss [EXTENSION, IN_UNION]
     >> POP_ASSUM (MP_TAC o Q.SPEC `scons F x`)
     >> RW_TAC std_ss [PROB_EMBED_TLS, STL_SCONS, SHD_SCONS,
                       PROB_EMBED_APPEND, IN_UNION]]]);

val PROB_MEASURE_ADDITIVE = store_thm
  ("PROB_MEASURE_ADDITIVE",
  ``additive (space prob_algebra, subsets prob_algebra, prob_measure)``,
    RW_TAC std_ss [additive_def, IN_PROB_ALGEBRA, DISJOINT_DEF,
                   measure_def, measurable_sets_def]
 >> Know `(prob_embed b UNION prob_embed b') IN (subsets prob_algebra)`
 >- PROVE_TAC [PROB_ALGEBRA_UNION, IN_PROB_ALGEBRA]
 >> RW_TAC std_ss [IN_PROB_ALGEBRA]
 >> RW_TAC std_ss [PROB_MEASURE_ALT]
 >> ASSUME_TAC PROB_PREMEASURE_ADDITIVE
 >> POP_ASSUM (MP_TAC o Q.SPEC `prob_canon b''`)
 >> RW_TAC std_ss [prob_canonical_def, PROB_CANON_IDEMPOT]
 >> POP_ASSUM (MP_TAC o Q.SPEC `prob_canon b`)
 >> RW_TAC std_ss [prob_canonical_def, PROB_CANON_IDEMPOT]
 >> POP_ASSUM (MP_TAC o Q.SPEC `prob_canon b'`)
 >> RW_TAC std_ss [prob_canonical_def, PROB_CANON_IDEMPOT]
 >> POP_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [PROB_CANON_EMBED]);

val PROB_MEASURE_POS = store_thm
  ("PROB_MEASURE_POS",
   ``!l. 0 <= prob_measure (prob_embed l)``,
   RW_TAC std_ss [PROB_MEASURE_ALT, PROB_PREMEASURE_POS]);

val PROB_MEASURE_POSITIVE = store_thm
  ("PROB_MEASURE_POSITIVE",
   ``positive (space prob_algebra, subsets prob_algebra, prob_measure)``,
   RW_TAC std_ss [positive_def, PROB_MEASURE_BASIC, IN_PROB_ALGEBRA,
                  measure_def, measurable_sets_def]
   >> RW_TAC std_ss [PROB_MEASURE_POS]);

val INFINITE_TLS = store_thm
  ("INFINITE_TLS",
   ``?sel. !s.
       INFINITE s ==> INFINITE {TL x | x IN s /\ (HD x : bool = sel s)}``,
   Suff
   `!s. ?sel.
      INFINITE s ==> INFINITE {TL x | x IN s /\ (HD x : bool = sel)}`
   >- DISCH_THEN (ACCEPT_TAC o CONV_RULE SKOLEM_CONV)
   >> RW_TAC std_ss []
   >> CCONTR_TAC
   >> POP_ASSUM MP_TAC
   >> DISCH_THEN (MP_TAC o CONV_RULE NOT_EXISTS_CONV)
   >> DISCH_THEN (fn th => MP_TAC (Q.SPEC `T` th) >> MP_TAC (Q.SPEC `F` th))
   >> RW_TAC std_ss []
   >> STRIP_TAC
   >> Q.PAT_X_ASSUM `~FINITE s` MP_TAC
   >> RW_TAC std_ss []
   >> ONCE_REWRITE_TAC [GSYM FINITE_TL]
   >> Suff `{TL x | x IN s /\ HD x} UNION {TL x | x IN s /\ ~HD x} = IMAGE TL s`
   >- PROVE_TAC [FINITE_UNION]
   >> PSET_TAC [EXTENSION]
   >> PROVE_TAC []);

val PREFIX_SET_UNION_UNIV = store_thm
  ("PREFIX_SET_UNION_UNIV",
   ``!s : bool list -> bool.
       (!a b. a IN s /\ b IN s /\ ~(a = b) ==> ~(IS_PREFIX a b)) /\
       (BIGUNION (IMAGE prefix_set s) = UNIV) ==>
       FINITE s``,
   MP_TAC INFINITE_TLS
   >> RW_TAC std_ss []
   >> CCONTR_TAC
   >> POP_ASSUM MP_TAC
   >> PURE_REWRITE_TAC []
   >> STRIP_TAC
   >> Q.PAT_X_ASSUM `x = UNIV` MP_TAC
   >> PSET_TAC [EXTENSION]
   >> Suff `?x. !l. l IN s ==> ~(x IN prefix_set l)` >- PROVE_TAC []
   >> Q.EXISTS_TAC
      `\n. sel (FUNPOW (\t. {TL x | x IN t /\ (HD x = sel t)}) n s)`
   >> RW_TAC std_ss []
   >> NTAC 3 (POP_ASSUM MP_TAC)
   >> Q.SPEC_TAC (`s`, `s`)
   >> Induct_on `l`
   >- (RW_TAC std_ss []
       >> Know `?a. a IN (s DELETE [])`
       >- PROVE_TAC [INFINITE_INHAB, INFINITE_DELETE]
       >> PSET_TAC [EXTENSION]
       >> PROVE_TAC [IS_PREFIX_NIL])
   >> RW_TAC std_ss [prefix_set_def, IN_INTER, IN_o, STL_PARTIAL]
   >> RW_TAC std_ss [o_DEF, FUNPOW, IN_HALFSPACE, shd_def]
   >> REWRITE_TAC [GSYM IMP_DISJ_THM]
   >> RW_TAC std_ss []
   >> Q.PAT_X_ASSUM `!s. P s ==> Q s`
      (MATCH_MP_TAC o REWRITE_RULE [AND_IMP_INTRO])
   >> REWRITE_TAC [GSYM CONJ_ASSOC]
   >> reverse (PSET_TAC [EXTENSION])
   >- (Q.EXISTS_TAC `sel s :: l`
       >> RW_TAC std_ss [TL, HD])
   >> Know `~([] IN s)`
   >- (STRIP_TAC
       >> Q.PAT_X_ASSUM `!a b. P a b`
          (MP_TAC o Q.SPECL [`sel (s : bool list -> bool) :: l`, `[]`])
       >> RW_TAC std_ss [IS_PREFIX_NIL])
   >> STRIP_TAC
   >> Cases_on `x` >- PROVE_TAC []
   >> Cases_on `x'` >- PROVE_TAC []
   >> REPEAT (POP_ASSUM MP_TAC)
   >> RW_TAC std_ss [HD, TL]
   >> Q.PAT_X_ASSUM `!a b. P a b`
      (MP_TAC o Q.SPECL [`sel (s : bool list -> bool) :: t`,
                         `sel (s : bool list -> bool) :: t'`])
   >> RW_TAC std_ss [IS_PREFIX]);

val IN_PROB_ALGEBRA_CANONICAL = store_thm
  ("IN_PROB_ALGEBRA_CANONICAL",
   ``!x. x IN (subsets prob_algebra) = ?b. prob_canonical b /\ (x = prob_embed b)``,
   RW_TAC std_ss [IN_PROB_ALGEBRA]
   >> reverse EQ_TAC >- PROVE_TAC []
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `prob_canon b`
   >> RW_TAC std_ss [prob_canonical_def, PROB_CANON_IDEMPOT, PROB_CANON_EMBED]);

val ALGEBRA_COUNTABLE_UNION_UNIV = store_thm
  ("ALGEBRA_COUNTABLE_UNION_UNIV",
   ``!f : num -> (num -> bool) -> bool.
       f IN (UNIV -> subsets prob_algebra) /\
       (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
       (BIGUNION (IMAGE f UNIV) = UNIV) ==>
       ?N. !n. N <= n ==> (f n = {})``,
   RW_TAC std_ss [IN_FUNSET, IN_UNIV, IN_PROB_ALGEBRA_CANONICAL]
   >> Q.PAT_X_ASSUM `!x. ?b. P x b`
      (MP_TAC o CONV_RULE (SKOLEM_CONV THENC DEPTH_CONV FORALL_AND_CONV))
   >> RW_TAC std_ss []
   >> Suff `FINITE {n | ~(f n = {})}`
   >- (RW_TAC std_ss [FINITE_SUBSET_COUNT, SUBSET_DEF, IN_COUNT,
                      GSPECIFICATION]
       >> Q.EXISTS_TAC `n`
       >> PROVE_TAC [NOT_LESS])
   >> Suff `FINITE {l | ?n : num. MEM l (b n)}`
   >- (STRIP_TAC
       >> MATCH_MP_TAC (INST_TYPE [beta |-> ``:bool list``] FINITE_INJ)
       >> Q.EXISTS_TAC `(HD o b)`
       >> Q.EXISTS_TAC `{l | ?n. IS_EL l (b n)}`
       >> RW_TAC std_ss []
       >> PSET_TAC [INJ_DEF, o_THM, EXTENSION]
       >- (POP_ASSUM MP_TAC
           >> Cases_on `b x`
           >- RW_TAC std_ss [PROB_EMBED_BASIC, NOT_IN_EMPTY]
           >> PROVE_TAC [HD, MEM])
       >> Cases_on `b x` >- PROVE_TAC [PROB_EMBED_BASIC, NOT_IN_EMPTY]
       >> Cases_on `b y` >- PROVE_TAC [PROB_EMBED_BASIC, NOT_IN_EMPTY]
       >> NTAC 3 (POP_ASSUM MP_TAC)
       >> RW_TAC std_ss [HD]
       >> Suff `?z. z IN f x /\ z IN f y` >- PROVE_TAC []
       >> RW_TAC std_ss [PROB_EMBED_CONS, IN_UNION]
       >> PROVE_TAC [PREFIX_SET_POPULATED])
   >> MATCH_MP_TAC PREFIX_SET_UNION_UNIV
   >> reverse CONJ_TAC
   >- (Q.PAT_X_ASSUM `x = UNIV` (ONCE_REWRITE_TAC o wrap o GSYM)
       >> POP_ASSUM MP_TAC
       >> KILL_TAC
       >> RW_TAC std_ss [EXTENSION, IN_BIGUNION, IN_PROB_EMBED]
       >> (EQ_TAC >> STRIP_TAC) >|
       [POP_ASSUM (MP_TAC o REWRITE_RULE [IN_IMAGE])
        >> RW_TAC std_ss [GSPECIFICATION]
        >> Q.EXISTS_TAC `f n`
        >> RW_TAC std_ss [IN_IMAGE, IN_UNIV]
        >> PROVE_TAC [],
        PSET_TAC [EXTENSION]
        >> PROVE_TAC []])
   >> RW_TAC std_ss [GSPECIFICATION, GSYM PREFIX_SET_PREFIX_SUBSET, SUBSET_DEF]
   >> MP_TAC (Q.SPEC `a` PREFIX_SET_POPULATED)
   >> STRIP_TAC
   >> Q.EXISTS_TAC `x`
   >> RW_TAC std_ss []
   >> STRIP_TAC
   >> Know `x IN f n`
   >- (RW_TAC std_ss [prob_embed_def, IN_UNIONL, MEM_MAP]
       >> PROVE_TAC [])
   >> Know `x IN f n'`
   >- (RW_TAC std_ss [prob_embed_def, IN_UNIONL, MEM_MAP]
       >> PROVE_TAC [])
   >> REPEAT STRIP_TAC
   >> Q.PAT_X_ASSUM `!m n. P m n` (MP_TAC o Q.SPECL [`n`, `n'`])
   >> reverse (RW_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER])
   >- PROVE_TAC []
   >> STRIP_TAC
   >> RW_TAC std_ss []
   >> MP_TAC (Q.SPECL [`a`, `b'`] PREFIX_SET_SUBSET)
   >> RW_TAC std_ss [PREFIX_SET_PREFIX_SUBSET, DISJOINT_DEF, EXTENSION,
                     NOT_IN_EMPTY, IN_INTER] >|
   [PROVE_TAC [],
    PROVE_TAC [PROB_CANONICAL_PREFIXFREE],
    PROVE_TAC [PROB_CANONICAL_PREFIXFREE]]);

val PROB_EMBED_TLS_EMPTY = store_thm
  ("PROB_EMBED_TLS_EMPTY",
   ``!l b. (prob_embed (MAP (CONS b) l) = {}) = (prob_embed l = {})``,
   PSET_TAC [EXTENSION]
   >> EQ_TAC >|
   [RW_TAC std_ss []
    >> POP_ASSUM (MP_TAC o Q.SPEC `scons b x`)
    >> RW_TAC std_ss [PROB_EMBED_TLS],
    RW_TAC std_ss []
    >> MP_TAC (Q.ISPEC `x : num -> bool` SCONS_SURJ)
    >> STRIP_TAC
    >> RW_TAC std_ss []
    >> RW_TAC std_ss [PROB_EMBED_TLS]]);

val ALGEBRA_COUNTABLE_UNION = store_thm
  ("ALGEBRA_COUNTABLE_UNION",
   ``!f : num -> (num -> bool) -> bool.
       f IN (UNIV -> subsets prob_algebra) /\
       (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
       (BIGUNION (IMAGE f UNIV) IN (subsets prob_algebra)) ==>
       ?N. !n. N <= n ==> (f n = {})``,
   RW_TAC std_ss [IN_PROB_ALGEBRA]
   >> REPEAT (POP_ASSUM MP_TAC)
   >> ONCE_REWRITE_TAC [GSYM PROB_CANON_EMBED]
   >> Q.SPEC_TAC (`f`, `f`)
   >> Know `prob_canonical (prob_canon b)`
   >- PROVE_TAC [prob_canonical_def, PROB_CANON_IDEMPOT]
   >> Q.SPEC_TAC (`prob_canon b`, `b`)
   >> HO_MATCH_MP_TAC PROB_CANONICAL_INDUCT
   >> CONJ_TAC
   >- (RW_TAC std_ss [PROB_EMBED_BASIC, BIGUNION_EQ_EMPTY, IN_IMAGE, IN_UNIV]
       >> Q.EXISTS_TAC `0`
       >> RW_TAC arith_ss []
       >> PROVE_TAC [])
   >> CONJ_TAC
   >- (RW_TAC std_ss [PROB_EMBED_BASIC]
       >> PROVE_TAC [ALGEBRA_COUNTABLE_UNION_UNIV])
   >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
   >> Q.PAT_X_ASSUM `!x. f x IN (subsets prob_algebra)` MP_TAC
   >> RW_TAC std_ss [IN_PROB_ALGEBRA_CANONICAL]
   >> Q.PAT_X_ASSUM `!x. ?b. P x b`
      (MP_TAC o CONV_RULE (SKOLEM_CONV THENC DEPTH_CONV FORALL_AND_CONV))
   >> RW_TAC std_ss []
   >> Know
      `?b1 b2. !x. b'' x = APPEND (MAP (CONS T) (b1 x)) (MAP (CONS F) (b2 x))`
   >- (Suff
       `!x. ?b1 b2. b'' x = APPEND (MAP (CONS T) b1) (MAP (CONS F) b2)`
       >- DISCH_THEN
          (ACCEPT_TAC o CONV_RULE (REDEPTH_CONV (CHANGED_CONV SKOLEM_CONV)))
       >> RW_TAC std_ss []
       >> Q.PAT_X_ASSUM `!x. f x = prob_embed (b'' x)` (MP_TAC o Q.SPEC `x`)
       >> Q.PAT_X_ASSUM `BIGUNION p = q` MP_TAC
       >> Q.PAT_X_ASSUM `prob_canonical p` MP_TAC
       >> Q.PAT_X_ASSUM `!x. prob_canonical (b'' x)` (MP_TAC o Q.SPEC `x`)
       >> Q.SPEC_TAC (`b'' x`, `B''`)
       >> KILL_TAC
       >> HO_MATCH_MP_TAC PROB_CANONICAL_CASES
       >> CONJ_TAC
       >- (RW_TAC std_ss []
           >> Q.EXISTS_TAC `[]`
           >> Q.EXISTS_TAC `[]`
           >> RW_TAC prob_canon_ss [])
       >> reverse CONJ_TAC
       >- (RW_TAC std_ss []
           >> PROVE_TAC [])
       >> RW_TAC std_ss [PROB_EMBED_BASIC]
       >> Q.EXISTS_TAC `b`
       >> Q.EXISTS_TAC `b'`
       >> MATCH_MP_TAC EQ_SYM
       >> MATCH_MP_TAC PROB_CANONICAL_UNIV
       >> Q.PAT_X_ASSUM `BIGUNION p = q` (ASM_REWRITE_TAC o wrap o GSYM)
       >> PSET_TAC [EXTENSION]
       >> PROVE_TAC [])
   >> RW_TAC std_ss []
   >> RW_TAC std_ss [PROB_EMBED_APPEND, EMPTY_UNION, PROB_EMBED_TLS_EMPTY]
   >> Suff
      `(?N. !n. N <= n ==> (prob_embed (b1 n) = {})) /\
       (?N. !n. N <= n ==> (prob_embed (b2 n) = {}))`
   >- (KILL_TAC
       >> RW_TAC std_ss []
       >> Q.EXISTS_TAC `MAX N N'`
       >> RW_TAC std_ss [MAX_LE_X])
   >> CONJ_TAC >|
   [Q.PAT_X_ASSUM `!f. P f ==> Q f` K_TAC
    >> Q.PAT_X_ASSUM `!f. P f ==> Q f` (MP_TAC o Q.SPEC `prob_embed o b1`)
    >> RW_TAC std_ss [o_THM, IN_PROB_ALGEBRA, AND_IMP_INTRO, GSYM CONJ_ASSOC]
    >> POP_ASSUM MATCH_MP_TAC
    >> CONJ_TAC >- PROVE_TAC []
    >> CONJ_TAC
    >- (REPEAT STRIP_TAC
        >> Q.PAT_X_ASSUM `!m n. P m n` (MP_TAC o Q.SPECL [`m`, `n`])
        >> RW_TAC std_ss [DISJOINT_DEF, PROB_EMBED_APPEND,
                          EXTENSION, NOT_IN_EMPTY, IN_UNION, IN_INTER]
        >> POP_ASSUM (MP_TAC o Q.SPEC `scons T x`)
        >> RW_TAC std_ss [PROB_EMBED_TLS])
    >> Q.PAT_X_ASSUM `BIGUNION p = q` MP_TAC
    >> ONCE_REWRITE_TAC [EXTENSION]
    >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_UNIV, o_THM]
    >> POP_ASSUM (MP_TAC o Q.SPEC `scons T x`)
    >> RW_TAC std_ss [PROB_EMBED_TLS, PROB_EMBED_APPEND, IN_UNION],
    Q.PAT_X_ASSUM `!f. P f ==> Q f` (MP_TAC o Q.SPEC `prob_embed o b2`)
    >> Q.PAT_X_ASSUM `!f. P f ==> Q f` K_TAC
    >> RW_TAC std_ss [o_THM, IN_PROB_ALGEBRA, AND_IMP_INTRO, GSYM CONJ_ASSOC]
    >> POP_ASSUM MATCH_MP_TAC
    >> CONJ_TAC >- PROVE_TAC []
    >> CONJ_TAC
    >- (REPEAT STRIP_TAC
        >> Q.PAT_X_ASSUM `!m n. P m n` (MP_TAC o Q.SPECL [`m`, `n`])
        >> RW_TAC std_ss [DISJOINT_DEF, PROB_EMBED_APPEND,
                          EXTENSION, NOT_IN_EMPTY, IN_UNION, IN_INTER]
        >> POP_ASSUM (MP_TAC o Q.SPEC `scons F x`)
        >> RW_TAC std_ss [PROB_EMBED_TLS])
    >> Q.PAT_X_ASSUM `BIGUNION p = q` MP_TAC
    >> ONCE_REWRITE_TAC [EXTENSION]
    >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_UNIV, o_THM]
    >> POP_ASSUM (MP_TAC o Q.SPEC `scons F x`)
    >> RW_TAC std_ss [PROB_EMBED_TLS, PROB_EMBED_APPEND, IN_UNION]]);

val PROB_MEASURE_COUNTABLY_ADDITIVE = store_thm
  ("PROB_MEASURE_COUNTABLY_ADDITIVE",
  ``countably_additive (space prob_algebra, subsets prob_algebra, prob_measure)``,
    RW_TAC std_ss [countably_additive_def, measure_def, measurable_sets_def]
 >> MP_TAC (Q.SPEC `f` ALGEBRA_COUNTABLE_UNION)
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM `BIGUNION p IN q` MP_TAC
 >> Know `BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE f (count N))`
 >- ( PSET_TAC [EXTENSION] >> PROVE_TAC [NOT_LESS] )
 >> DISCH_THEN (REWRITE_TAC o wrap)
 >> STRIP_TAC
 >> (MP_TAC o Q.SPECL [`f`, `N`])
       (ISPEC ``(space prob_algebra, subsets prob_algebra, prob_measure)`` ADDITIVE_SUM)
 >> ASSUME_TAC SPACE_SUBSETS_PROB_ALGEBRA
 >> RW_TAC std_ss [PROB_ALGEBRA_ALGEBRA, PROB_MEASURE_POSITIVE,
                   PROB_MEASURE_ADDITIVE, measure_def, measurable_sets_def, m_space_def]
 >> POP_ASSUM (REWRITE_TAC o wrap o GSYM)
 >> MATCH_MP_TAC SER_0
 >> RW_TAC std_ss [o_THM, PROB_MEASURE_BASIC]);

val PROB_EMBED_PREFIX_SET = store_thm
  ("PROB_EMBED_PREFIX_SET",
   ``!l. prob_embed [l] = prefix_set l``,
   PSET_TAC [PROB_EMBED_CONS, PROB_EMBED_NIL, EXTENSION]);

val PROB_ALGEBRA_PREFIX_SET = store_thm
  ("PROB_ALGEBRA_PREFIX_SET",
   ``!l. prefix_set l IN (subsets prob_algebra)``,
   RW_TAC std_ss [IN_PROB_ALGEBRA, GSYM PROB_EMBED_PREFIX_SET]
   >> PROVE_TAC []);

val PROB_MEASURE_PREFIX_SET = store_thm
  ("PROB_MEASURE_PREFIX_SET",
   ``!l. prob_measure (prefix_set l) = (1 / 2) pow (LENGTH l)``,
   RW_TAC prob_canon_ss [GSYM PROB_EMBED_PREFIX_SET, PROB_MEASURE_ALT,
                         prob_premeasure_def, REAL_ADD_RID]);

val PREMEASURABLE_PROB_ALGEBRA_STL = store_thm
  ("PREMEASURABLE_PROB_ALGEBRA_STL",
  ``stl IN premeasurable prob_algebra prob_algebra``,
    RW_TAC std_ss [IN_PREMEASURABLE, PROB_ALGEBRA_ALGEBRA, PREIMAGE_def,
                   SPACE_PROB_ALGEBRA, space_def, subsets_def, IN_FUNSET, IN_UNIV]
 >> Suff `{x | stl x IN s} = (s o stl)`
 >- PROVE_TAC [PROB_ALGEBRA_STL, PROB_ALGEBRA_UNIV, INTER_COMM, INTER_UNIV]
 >> ONCE_REWRITE_TAC [EXTENSION]
 >> RW_TAC std_ss [GSPECIFICATION, IN_o]);

val PREMEASURABLE_PROB_ALGEBRA_SDROP = store_thm
  ("PREMEASURABLE_PROB_ALGEBRA_SDROP",
  ``!n. sdrop n IN premeasurable prob_algebra prob_algebra``,
    Induct >- RW_TAC std_ss [PROB_ALGEBRA_ALGEBRA, PREMEASURABLE_I, sdrop_def]
 >> RW_TAC std_ss [sdrop_def]
 >> MATCH_MP_TAC PREMEASURABLE_COMP
 >> Q.EXISTS_TAC `prob_algebra`
 >> RW_TAC std_ss [PREMEASURABLE_PROB_ALGEBRA_STL]);

val PROB_ALGEBRA_SCONS = store_thm
  ("PROB_ALGEBRA_SCONS",
   ``!p. (!b. (p o scons b) IN (subsets prob_algebra)) = p IN (subsets prob_algebra)``,
   RW_TAC std_ss [IN_PROB_ALGEBRA]
   >> EQ_TAC
   >- (ONCE_REWRITE_TAC [EXTENSION]
       >> DISCH_THEN
          (fn th => (MP_TAC (Q.SPEC `T` th) >> MP_TAC (Q.SPEC `F` th)))
       >> RW_TAC std_ss [IN_o]
       >> Q.EXISTS_TAC `APPEND (MAP (CONS T) b'') (MAP (CONS F) b')`
       >> RW_TAC std_ss []
       >> MP_TAC (Q.ISPEC `x : num -> bool` SCONS_SURJ)
       >> RW_TAC std_ss []
       >> RW_TAC std_ss [PROB_EMBED_TLS, PROB_EMBED_APPEND, IN_UNION]
       >> Cases_on `h`
       >> PROVE_TAC [])
   >> RW_TAC std_ss []
   >> ONCE_REWRITE_TAC [GSYM PROB_CANON_EMBED]
   >> Know `prob_canonical (prob_canon b)`
   >- PROVE_TAC [prob_canonical_def, PROB_CANON_IDEMPOT]
   >> Q.SPEC_TAC (`prob_canon b`, `l`)
   >> REWRITE_TAC [PROB_CANON_EMBED]
   >> HO_MATCH_MP_TAC PROB_CANONICAL_CASES
   >> CONJ_TAC
   >- (Q.EXISTS_TAC `[]`
       >> PSET_TAC [PROB_EMBED_BASIC, EXTENSION])
   >> CONJ_TAC
   >- (Q.EXISTS_TAC `[[]]`
       >> PSET_TAC [PROB_EMBED_BASIC, EXTENSION])
   >> PSET_TAC [PROB_EMBED_APPEND, PROB_EMBED_TLS, EXTENSION]
   >> Cases_on `b'`
   >> PROVE_TAC []);

val PREMEASURABLE_PROB_ALGEBRA_SCONS = store_thm
  ("PREMEASURABLE_PROB_ALGEBRA_SCONS",
  ``!b. scons b IN premeasurable prob_algebra prob_algebra``,
    ASSUME_TAC SPACE_PROB_ALGEBRA
 >> RW_TAC std_ss [IN_PREMEASURABLE, PROB_ALGEBRA_ALGEBRA, PREIMAGE_def, IN_FUNSET, IN_UNIV]
 >> Suff `{x | scons b x IN s} = s o scons b`
 >- PROVE_TAC [PROB_ALGEBRA_SCONS, INTER_UNIV]
 >> ONCE_REWRITE_TAC [EXTENSION]
 >> RW_TAC std_ss [GSPECIFICATION, IN_o]);

val PROB_MEASURE_STL = store_thm
  ("PROB_MEASURE_STL",
   ``!a. a IN (subsets prob_algebra) ==> (prob_measure (a o stl) = prob_measure a)``,
   RW_TAC std_ss []
   >> Know `(a o stl) IN (subsets prob_algebra)` >- RW_TAC std_ss [PROB_ALGEBRA_STL]
   >> RW_TAC std_ss [GSYM PREIMAGE_ALT]
   >> REPEAT (POP_ASSUM MP_TAC)
   >> RW_TAC std_ss [IN_PROB_ALGEBRA]
   >> RW_TAC std_ss [PROB_MEASURE_ALT]
   >> REPEAT (POP_ASSUM MP_TAC)
   >> Suff
      `!c.
         prob_canonical c ==>
         !b.
           prob_canonical b ==>
           (PREIMAGE stl (prob_embed b) = prob_embed c) ==>
           (prob_premeasure b = prob_premeasure c)`
   >- (DISCH_THEN (MP_TAC o Q.SPEC `prob_canon b'`)
       >> RW_TAC std_ss [prob_canonical_def, PROB_CANON_EMBED,
                         PROB_CANON_IDEMPOT])
   >> HO_MATCH_MP_TAC PROB_CANONICAL_CASES
   >> RW_TAC std_ss [PROB_EMBED_BASIC, PROB_PREMEASURE_BASIC, o_DEF] >|
   [Suff `b = []` >- RW_TAC std_ss [PROB_PREMEASURE_BASIC]
    >> Suff `prob_embed b = {}` >- RW_TAC std_ss [PROB_CANONICAL_EMBED_EMPTY]
    >> POP_ASSUM MP_TAC
    >> RW_TAC std_ss [EXTENSION, NOT_IN_EMPTY]
    >> POP_ASSUM (MP_TAC o Q.SPEC `scons T x`)
    >> RW_TAC std_ss [STL_SCONS, IN_PREIMAGE],
    Suff `b = [[]]` >- RW_TAC std_ss [PROB_PREMEASURE_BASIC]
    >> Suff `prob_embed b = UNIV` >- RW_TAC std_ss [PROB_CANONICAL_EMBED_UNIV]
    >> POP_ASSUM MP_TAC
    >> RW_TAC std_ss [EXTENSION, IN_UNIV]
    >> POP_ASSUM (MP_TAC o Q.SPEC `scons T x`)
    >> RW_TAC std_ss [STL_SCONS, IN_PREIMAGE],
    Know `l1 = l2`
    >- (Suff `prob_canon l1 = prob_canon l2` >- PROVE_TAC [prob_canonical_def]
        >> PSET_TAC [PROB_CANON_REP, EXTENSION]
        >> POP_ASSUM (fn th => MP_TAC (Q.SPEC `scons T x` th)
                      >> MP_TAC (Q.SPEC `scons F x` th))
        >> PSET_TAC [SHD_SCONS, STL_SCONS, PROB_EMBED_APPEND,
                     PROB_EMBED_TLS, EXTENSION])
    >> RW_TAC std_ss []
    >> Know `b = l1`
    >- (Suff `prob_canon b = prob_canon l1` >- PROVE_TAC [prob_canonical_def]
        >> PSET_TAC [PROB_CANON_REP, EXTENSION]
        >> POP_ASSUM (MP_TAC o Q.SPEC `scons T x`)
        >> PSET_TAC [SHD_SCONS, STL_SCONS, PROB_EMBED_APPEND,
                     PROB_EMBED_TLS, EXTENSION])
    >> RW_TAC std_ss []
    >> Know `!a b : real. (2 * a = 2 * b) ==> (a = b)` >- REAL_ARITH_TAC
    >> DISCH_THEN MATCH_MP_TAC
    >> RW_TAC std_ss [PROB_PREMEASURE_APPEND, PROB_PREMEASURE_TLS,
                      REAL_ADD_LDISTRIB]
    >> REAL_ARITH_TAC]);

val PROB_MEASURE_SDROP = store_thm
  ("PROB_MEASURE_SDROP",
   ``!n a.
       a IN (subsets prob_algebra) ==> (prob_measure (a o sdrop n) = prob_measure a)``,
   Induct >- RW_TAC std_ss' [sdrop_def, o_DEF, I_THM]
   >> RW_TAC bool_ss [sdrop_def, o_ASSOC, PROB_MEASURE_STL, PROB_ALGEBRA_SDROP]);

val PROB_PRESERVING_PROB_ALGEBRA_STL = store_thm
  ("PROB_PRESERVING_PROB_ALGEBRA_STL",
  ``stl IN prob_preserving (space prob_algebra, subsets prob_algebra, prob_measure)
                           (space prob_algebra, subsets prob_algebra, prob_measure)``,
    ASSUME_TAC SPACE_SUBSETS_PROB_ALGEBRA
 >> RW_TAC std_ss [PROB_PRESERVING, GSPECIFICATION, EVENTS, PROB,
                   PREMEASURABLE_PROB_ALGEBRA_STL, PREIMAGE_ALT,
                   p_space_def, m_space_def]
 >> ASSUME_TAC SPACE_PROB_ALGEBRA
 >> POP_ORW
 >> RW_TAC std_ss [PROB_MEASURE_STL, INTER_UNIV]);

val PROB_PRESERVING_PROB_ALGEBRA_SDROP = store_thm
  ("PROB_PRESERVING_PROB_ALGEBRA_SDROP",
  ``!n. sdrop n IN
       prob_preserving (space prob_algebra, subsets prob_algebra, prob_measure)
                       (space prob_algebra, subsets prob_algebra, prob_measure)``,
    ASSUME_TAC SPACE_SUBSETS_PROB_ALGEBRA
 >> RW_TAC std_ss [PROB_PRESERVING, GSPECIFICATION, EVENTS, PROB,
                   PREMEASURABLE_PROB_ALGEBRA_SDROP, PREIMAGE_ALT,
                   p_space_def, m_space_def]
 >> ASSUME_TAC SPACE_PROB_ALGEBRA
 >> POP_ORW
 >> RW_TAC std_ss [PROB_MEASURE_SDROP, INTER_UNIV]);

val MIRROR_MIRROR = store_thm
  ("MIRROR_MIRROR",
   ``!x. mirror (mirror x) = x``,
   RW_TAC std_ss [mirror_def, SHD_SCONS, STL_SCONS, SCONS_SHD_STL]);

val MIRROR_o_MIRROR = store_thm
  ("MIRROR_o_MIRROR",
   ``mirror o mirror = I``,
   FUN_EQ_TAC
   >> RW_TAC std_ss [o_THM, I_THM, MIRROR_MIRROR]);

val MIRROR_SCONS = store_thm
  ("MIRROR_SCONS",
   ``!b x. mirror (scons b x) = scons (~b) x``,
   RW_TAC std_ss [mirror_def, SHD_SCONS, STL_SCONS]);

val PREIMAGE_MIRROR_TLS = store_thm
  ("PREIMAGE_MIRROR_TLS",
   ``!l1 l2.
       PREIMAGE mirror (prob_embed (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2)))
       =
       prob_embed (APPEND (MAP (CONS T) l2) (MAP (CONS F) l1))``,
   PSET_TAC [EXTENSION]
   >> MP_TAC (Q.ISPEC `x : num -> bool` SCONS_SURJ)
   >> RW_TAC std_ss []
   >> RW_TAC std_ss [MIRROR_SCONS, PROB_EMBED_APPEND, IN_UNION, PROB_EMBED_TLS]
   >> PROVE_TAC []);

val PREMEASURABLE_PROB_ALGEBRA_MIRROR = store_thm
  ("PREMEASURABLE_PROB_ALGEBRA_MIRROR",
  ``mirror IN premeasurable prob_algebra prob_algebra``,
    RW_TAC std_ss [IN_PREMEASURABLE, IN_PROB_ALGEBRA, PROB_ALGEBRA_ALGEBRA,
                   IN_FUNSET, IN_UNIV, INTER_UNIV, SPACE_PROB_ALGEBRA]
 >> Suff
      `!b.
         prob_canonical b ==>
         ?c. PREIMAGE mirror (prob_embed b) = prob_embed c`
 >- ( DISCH_THEN (MP_TAC o Q.SPEC `prob_canon b`) \\
      RW_TAC std_ss [prob_canonical_def, PROB_CANON_IDEMPOT, PROB_CANON_EMBED] )
 >> HO_MATCH_MP_TAC PROB_CANONICAL_CASES
 >> CONJ_TAC
 >- ( Q.EXISTS_TAC `[]` \\
      RW_TAC std_ss [PREIMAGE_EMPTY, PROB_EMBED_BASIC] )
 >> CONJ_TAC
 >- ( Q.EXISTS_TAC `[[]]` \\
      RW_TAC std_ss [PREIMAGE_UNIV, PROB_EMBED_BASIC] )
 >> RW_TAC std_ss [PREIMAGE_MIRROR_TLS]
 >> PROVE_TAC []);

val PROB_ALGEBRA_MIRROR = store_thm
  ("PROB_ALGEBRA_MIRROR",
  ``!p. p o mirror IN (subsets prob_algebra) = p IN (subsets prob_algebra)``,
    MP_TAC PREMEASURABLE_PROB_ALGEBRA_MIRROR
 >> RW_TAC std_ss [IN_PREMEASURABLE, PREIMAGE_ALT, INTER_UNIV, SPACE_PROB_ALGEBRA]
 >> reverse EQ_TAC >- PROVE_TAC []
 >> POP_ASSUM (MP_TAC o Q.SPEC `p o mirror`)
 >> RW_TAC std_ss [GSYM o_ASSOC, MIRROR_o_MIRROR, I_o_ID]);

val PROB_MEASURE_MIRROR = store_thm
  ("PROB_MEASURE_MIRROR",
   ``!a. a IN (subsets prob_algebra) ==> (prob_measure (a o mirror) = prob_measure a)``,
   RW_TAC std_ss [IN_PROB_ALGEBRA_CANONICAL, GSYM PREIMAGE_ALT]
   >> POP_ASSUM MP_TAC
   >> Q.SPEC_TAC (`b`, `b`)
   >> HO_MATCH_MP_TAC PROB_CANONICAL_CASES
   >> CONJ_TAC >- RW_TAC std_ss [PROB_EMBED_BASIC, PREIMAGE_EMPTY]
   >> CONJ_TAC >- RW_TAC std_ss [PROB_EMBED_BASIC, PREIMAGE_UNIV]
   >> RW_TAC std_ss [PREIMAGE_MIRROR_TLS, PROB_MEASURE_ALT]
   >> Know `prob_canonical (APPEND (MAP (CONS T) l2) (MAP (CONS F) l1))`
   >- (MP_TAC (Q.SPECL [`l2`, `l1`] PROB_CANONICAL_STEP)
       >> Know `~((l2 = [[]]) /\ (l1 = [[]]))`
       >- (STRIP_TAC
           >> Q.PAT_X_ASSUM `prob_canonical x` MP_TAC
           >> RW_TAC prob_canon_ss [prob_canonical_def])
       >> RW_TAC std_ss [])
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [prob_canonical_def]
   >> RW_TAC std_ss [PROB_PREMEASURE_APPEND]
   >> KILL_TAC
   >> Know `!a b : real. (2 * a = 2 * b) ==> (a = b)` >- REAL_ARITH_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> RW_TAC std_ss [REAL_ADD_LDISTRIB, PROB_PREMEASURE_TLS]
   >> REAL_ARITH_TAC);

val PROB_PRESERVING_PROB_ALGEBRA_MIRROR = store_thm
  ("PROB_PRESERVING_PROB_ALGEBRA_MIRROR",
   ``mirror IN
     prob_preserving (space prob_algebra, subsets prob_algebra, prob_measure)
                     (space prob_algebra, subsets prob_algebra, prob_measure)``,
    ASSUME_TAC SPACE_SUBSETS_PROB_ALGEBRA
 >> RW_TAC std_ss [PROB_PRESERVING, GSPECIFICATION, EVENTS, PROB,
                   PREMEASURABLE_PROB_ALGEBRA_MIRROR, PREIMAGE_ALT,
                   p_space_def, m_space_def]
 >> ASSUME_TAC SPACE_PROB_ALGEBRA
 >> POP_ORW
 >> RW_TAC std_ss [PROB_MEASURE_MIRROR, INTER_UNIV]);

val PREIMAGE_SHD_SING = store_thm
  ("PREIMAGE_SHD_SING",
   ``!b. PREIMAGE shd {b} = halfspace b``,
   RW_TAC std_ss [EXTENSION, IN_HALFSPACE, IN_PREIMAGE, IN_SING]);

val PREIMAGE_SHD_CASES = store_thm
  ("PREIMAGE_SHD_CASES",
   ``!x.
       (PREIMAGE shd x = {}) \/ (PREIMAGE shd x = UNIV) \/
       (?b. PREIMAGE shd x = halfspace b)``,
   HO_MATCH_MP_TAC BOOL_SET_CASES
   >> RW_TAC std_ss [PREIMAGE_EMPTY, PREIMAGE_UNIV, PREIMAGE_SHD_SING]
   >> PROVE_TAC []);

val PROB_ALGEBRA_SHD = store_thm
  ("PROB_ALGEBRA_SHD",
   ``!x. (x o shd) IN (subsets prob_algebra)``,
   STRIP_TAC
   >> MP_TAC (Q.SPEC `x` PREIMAGE_SHD_CASES)
   >> RW_TAC std_ss [PREIMAGE_ALT]
   >> RW_TAC std_ss [PROB_ALGEBRA_BASIC]);

val HALFSPACE_T_UNION_F = store_thm
  ("HALFSPACE_T_UNION_F",
   ``halfspace T UNION halfspace F = UNIV``,
   RW_TAC std_ss [EXTENSION, IN_UNION, IN_UNIV, IN_HALFSPACE]);

val EXIST_LONG_PREFIX_SETS = store_thm
  ("EXIST_LONG_PREFIX_SETS",
   ``!x n. ?l. (LENGTH l = n) /\ x IN prefix_set l``,
   REPEAT GEN_TAC
   >> Q.SPEC_TAC (`x`, `x`)
   >> Induct_on `n`
   >- (RW_TAC std_ss []
       >> Q.EXISTS_TAC `[]`
       >> RW_TAC std_ss [LENGTH, prefix_set_def, IN_UNIV])
   >> RW_TAC std_ss []
   >> SEQ_CASES_TAC `x`
   >> POP_ASSUM (MP_TAC o Q.SPEC `t`)
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `h :: l`
   >> RW_TAC std_ss [LENGTH, prefix_set_def, IN_INTER, IN_o, IN_HALFSPACE,
                     SHD_SCONS, STL_SCONS]);

val PREFIX_SET_APPEND = store_thm
  ("PREFIX_SET_APPEND",
   ``!s l1 l2. s IN prefix_set (APPEND l1 l2) ==> s IN prefix_set l1``,
   Induct_on `l1` >- RW_TAC std_ss [prefix_set_def, IN_UNIV]
   >> RW_TAC std_ss [APPEND]
   >> SEQ_CASES_TAC `s`
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [PREFIX_SET_SCONS]
   >> PROVE_TAC []);

val IS_PREFIX_APPEND1 = store_thm
  ("IS_PREFIX_APPEND1",
   ``!a b c. IS_PREFIX c (APPEND a b) ==> IS_PREFIX c a``,
   Induct >- RW_TAC std_ss [IS_PREFIX]
   >> RW_TAC std_ss []
   >> Cases_on `c`
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [IS_PREFIX, APPEND]
   >> PROVE_TAC []);

val IS_PREFIX_APPEND2 = store_thm
  ("IS_PREFIX_APPEND2",
   ``!a b c. IS_PREFIX (APPEND b c) a ==> IS_PREFIX b a \/ IS_PREFIX a b``,
   Induct >- RW_TAC std_ss [IS_PREFIX]
   >> RW_TAC std_ss []
   >> Cases_on `b` >- RW_TAC std_ss [IS_PREFIX]
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [IS_PREFIX, APPEND]
   >> PROVE_TAC []);

val IS_PREFIX_APPENDS = store_thm
  ("IS_PREFIX_APPENDS",
   ``!a b c. IS_PREFIX (APPEND a c) (APPEND a b) = IS_PREFIX c b``,
   Induct >- RW_TAC std_ss [APPEND]
   >> RW_TAC std_ss [APPEND, IS_PREFIX]);

val PREFIX_SET_UNFIXED_SDROP = store_thm
  ("PREFIX_SET_UNFIXED_SDROP",
   ``!l n. ?s. s IN prefix_set l /\ ~(sdrop (SUC n) s = s)``,
   REPEAT GEN_TAC
   >> Induct_on `l`
   >- (Q.EXISTS_TAC `FUNPOW (scons T) (SUC n) (scons F s)`
       >> RW_TAC std_ss [prefix_set_def, IN_UNIV]
       >> ONCE_REWRITE_TAC [FUNPOW_SUC, sdrop_def]
       >> RW_TAC std_ss [o_THM, I_THM, STL_SCONS]
       >> Suff `!t. ~(sdrop n (FUNPOW (scons T) n (scons F s)) = scons T t)`
       >- PROVE_TAC []
       >> GEN_TAC
       >> Induct_on `n` >- RW_TAC std_ss [sdrop_def, FUNPOW, I_THM, SCONS_EQ]
       >> RW_TAC std_ss [sdrop_def, o_THM, FUNPOW_SUC, STL_SCONS])
   >> POP_ASSUM MP_TAC
   >> REPEAT STRIP_TAC
   >> Q.EXISTS_TAC `scons h s`
   >> RW_TAC bool_ss [prefix_set_def, IN_INTER, IN_HALFSPACE, IN_o, SHD_SCONS,
                     STL_SCONS]
   >> STRIP_TAC
   >> Q.PAT_X_ASSUM `~(X = Y)` MP_TAC
   >> Know `(stl o sdrop (SUC n)) (scons h s) = stl (scons h s)`
   >- RW_TAC std_ss [o_THM]
   >> RW_TAC bool_ss [STL_o_SDROP]
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [sdrop_def, STL_SCONS, o_THM]);

val PREFIX_SET_UNFIXED_STL = store_thm
  ("PREFIX_SET_UNFIXED_STL",
   ``!l. ?s. s IN prefix_set l /\ ~(stl s = s)``,
   GEN_TAC
   >> MP_TAC (Q.SPECL [`l`, `0`] PREFIX_SET_UNFIXED_SDROP)
   >> RW_TAC bool_ss [sdrop_def, I_o_ID]);

val SDROP_APPEND = store_thm
  ("SDROP_APPEND",
   ``!s x y.
       s IN prefix_set (APPEND x y) =
       s IN prefix_set x /\ sdrop (LENGTH x) s IN prefix_set y``,
   Induct_on `x`
   >- RW_TAC list_ss [sdrop_def, I_THM, APPEND, LENGTH, prefix_set_def, IN_UNIV]
   >> RW_TAC list_ss [sdrop_def, o_THM]
   >> SEQ_CASES_TAC `s`
   >> FULL_SIMP_TAC std_ss [PREFIX_SET_SCONS, STL_SCONS]
   >> PROVE_TAC []);

val SDROP_PREFIX_SEQ_APPEND = store_thm
  ("SDROP_PREFIX_SEQ_APPEND",
   ``!s x y. sdrop (LENGTH x) (prefix_seq (APPEND x y)) = prefix_seq y``,
   Induct_on `x` >- RW_TAC list_ss [sdrop_def, I_THM]
   >> RW_TAC list_ss [sdrop_def, o_THM, APPEND, prefix_seq_def]
   >> FULL_SIMP_TAC std_ss [PREFIX_SET_SCONS, STL_SCONS]);

val PREFIX_SET_INJ = store_thm
  ("PREFIX_SET_INJ",
   ``!a b. (prefix_set a = prefix_set b) = (a = b)``,
   Induct
   >- (RW_TAC std_ss [PREFIX_SET_BASIC]
       >> PROVE_TAC [PREFIX_SET_NIL])
   >> Cases_on `b` >- RW_TAC std_ss [PREFIX_SET_BASIC, PREFIX_SET_NIL]
   >> RW_TAC std_ss []
   >> Cases_on `h = h'`
   >- (RW_TAC std_ss []
       >> reverse EQ_TAC >- RW_TAC std_ss []
       >> SET_EQ_TAC
       >> RW_TAC std_ss []
       >> Q.PAT_X_ASSUM `!b. (P b = Q b) = R b` (REWRITE_TAC o wrap o GSYM)
       >> SET_EQ_TAC
       >> GEN_TAC
       >> POP_ASSUM (MP_TAC o Q.SPEC `scons h x`)
       >> RW_TAC std_ss [PREFIX_SET_SCONS])
   >> RW_TAC std_ss []
   >> SET_EQ_TAC
   >> STRIP_TAC
   >> POP_ASSUM (MP_TAC o Q.SPEC `scons h (prefix_seq t)`)
   >> RW_TAC std_ss [PREFIX_SET_SCONS, PREFIX_SEQ]);

val STL_MIRROR = store_thm
  ("STL_MIRROR",
   ``!x. stl (mirror x) = stl x``,
   GEN_TAC
   >> SEQ_CASES_TAC `x`
   >> RW_TAC std_ss [STL_SCONS, MIRROR_SCONS]);

val MIRROR_NEQ = store_thm
  ("MIRROR_NEQ",
   ``!x. ~(mirror x = x)``,
   GEN_TAC
   >> SEQ_CASES_TAC `x`
   >> RW_TAC std_ss [MIRROR_SCONS, SCONS_EQ]
   >> Cases_on `h`
   >> PROVE_TAC []);

val PREFIX_SET_ALT = store_thm
  ("PREFIX_SET_ALT",
   ``!l. prefix_set l = {s | stake (LENGTH l) s = l}``,
   Induct
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [GSPECIFICATION, prefix_set_def, IN_UNIV, LENGTH,
                         stake_def])
   >> SET_EQ_TAC
   >> RW_TAC std_ss [GSPECIFICATION, prefix_set_def, IN_INTER, LENGTH,
                     stake_def, IN_HALFSPACE, IN_o]);

val IMAGE_MIRROR = store_thm
  ("IMAGE_MIRROR",
   ``IMAGE mirror = PREIMAGE mirror``,
   FUN_EQ_TAC
   >> SET_EQ_TAC
   >> PSET_TAC []
   >> PROVE_TAC [MIRROR_MIRROR]);

val _ = export_theory ();
