(* ------------------------------------------------------------------------- *)
(* Probability Theory                                                        *)
(* Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar                         *)
(* HVG Group, Concordia University, Montreal                                 *)
(*                                                                           *)
(* Further enriched by Chun Tian (2019-2020)                                 *)
(* ------------------------------------------------------------------------- *)
(* Based on the work of Joe Hurd [7] and Aaron Coble [8]                     *)
(* Cambridge University.                                                     *)
(* ========================================================================= *)
(* Convergence Concepts and The Laws of Large Numbers                        *)
(*                                                                           *)
(* Author: Chun Tian <binghe.lisp@gmail.com> (2020)                          *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ========================================================================= *)
(*                 Probability Density Function (PDF) [11]                   *)
(*                                                                           *)
(*        (c) Copyright 2015,                                                *)
(*                       Muhammad Qasim,                                     *)
(*                       Osman Hasan,                                        *)
(*                       Hardware Verification Group,                        *)
(*                       Concordia University                                *)
(*                                                                           *)
(*            Contact:  <m_qasi@ece.concordia.ca>                            *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open pairTheory combinTheory optionTheory prim_recTheory arithmeticTheory
     res_quanTheory res_quanTools pred_setTheory pred_setLib realTheory realLib
     seqTheory transcTheory real_sigmaTheory real_topologyTheory mesonLib
     RealArith logrootTheory;

open hurdUtils util_probTheory extrealTheory sigma_algebraTheory measureTheory
     real_borelTheory borelTheory lebesgueTheory martingaleTheory;

val _ = new_theory "probability";

(* "... This task would have been a rather hopeless one before the
    introduction of Lebesgue's theories of measure and integration. ...
    But if probability theory was to be based on the above analogies, it
    still was necessary to make the theories of measure and integration
    independent of the geometric elements which were in the foreground
    with Lebesgue. ...

    I wish to call attention to those points of the present exposition
    which are outside the above-mentioned range of ideas familiar to
    the specialist. They are the following: Probability distributions
    in infinite-dimensional spaces (Chapter III, 4); differentiation
    and integration of mathematical expectations with respect to a
    parameter (Chapter IV, 5); and especially the theory of conditional
    probabilities and conditional expectations (Chapter V). ..."

  -- A. N. Kolmogorov, "Foundations of the Theory of Probability." [1] *)

val set_ss = std_ss ++ PRED_SET_ss;

val _ = hide "S";
val _ = hide "W";

(* ------------------------------------------------------------------------- *)
(* Basic probability theory definitions.                                     *)
(* ------------------------------------------------------------------------- *)

val _ = type_abbrev ("p_space", ``:'a m_space``);
val _ = type_abbrev ("events",  ``:'a set set``);

val p_space_def = Define `p_space = m_space`;

val events_def = Define `events = measurable_sets`;

val prob_def = Define `prob = measure`;

val prob_space_def = Define
   `prob_space p <=> measure_space p /\ (measure p (m_space p) = 1)`;

val probably_def = Define
   `probably p e <=> e IN events p /\ (prob p e = 1)`;

val possibly_def = Define
   `possibly p e <=> e IN events p /\ prob p e <> 0`;

(* this is an abstract random variable *)
val random_variable_def = Define
   `random_variable X p s <=> X IN measurable (p_space p, events p) s`;

(* NOTE: use `real_random_variable` iff `!x. X x <> NegInf /\ X x <> PosInf`,
   otherwise use `random_variable X p Borel` instead. *)
val real_random_variable_def = Define
   `real_random_variable X p <=>
         random_variable X p Borel /\ (!x. X x <> NegInf /\ X x <> PosInf)`;

(* A (probability) distribution is a probability measure on `(p_space p,events p)`,

   cf. lebesgueTheory.distr_def, of type ``:'a m_space``
 *)
val distribution_def = Define (* was: pmf in [10] *)
   `distribution (p :'a p_space) X = (\s. prob p ((PREIMAGE X s) INTER p_space p))`;

(* c.f. [2, p.36], [4, p.206], [6, p.256], etc. *)
val distribution_function_def = Define
   `distribution_function p X = (\x. prob p ({w | X w <= x} INTER p_space p))`;

Definition identical_distribution_def :
    identical_distribution p X E (J :'index set) =
      !i j s. s IN subsets E /\ i IN J /\ i IN J ==>
             (distribution p (X i) s = distribution p (X j) s)
End

(* alternative definition *)
Theorem distribution_function :
    !p X t. distribution_function p X t = distribution p X {x | x <= t}
Proof
    RW_TAC std_ss [distribution_function_def, distribution_def,
                   PREIMAGE_def, GSPECIFICATION]
QED

val joint_distribution_def = Define
   `joint_distribution (p :'a p_space) X Y =
      (\a. prob p (PREIMAGE (\x. (X x, Y x)) a INTER p_space p))`;

val joint_distribution3_def = Define
   `joint_distribution3 (p :'a p_space) X Y Z =
      (\a. prob p (PREIMAGE (\x. (X x,Y x,Z x)) a INTER p_space p))`;

(* from [10], not used
Definition joint_distributions_def : (* was: joint_pmf_sequence *)
    joint_distributions p X s =
      (\V. prob p (BIGINTER (IMAGE (\i. PREIMAGE (X i) (V i)) s)) INTER p_space p)
End
 *)

val conditional_distribution_def = Define
   `conditional_distribution (p :'a p_space) X Y a b =
      joint_distribution p X Y (a CROSS b) / distribution p Y b`;

(* `expectation` is just (Lebesgue) `integral` *)
val expectation_def = Define
   `expectation = integral`;

(* not used *)
val conditional_expectation_def = Define
   `conditional_expectation p X s =
        @f. real_random_variable f p /\
            !g. g IN s ==>
               (expectation p (\x. f x * indicator_fn g x) =
                expectation p (\x. X x * indicator_fn g x))`;

(* not used *)
val conditional_prob_def = Define
   `conditional_prob p e1 e2 =
    conditional_expectation p (indicator_fn e1) e2`;

val cond_prob_def = Define
   `cond_prob p e1 e2 = (prob p (e1 INTER e2)) / (prob p e2)`;

(* not used *)
val rv_conditional_expectation_def = Define
   `rv_conditional_expectation (p :'a p_space) s X Y =
       conditional_expectation p X (IMAGE (\a. (PREIMAGE Y a) INTER p_space p) (subsets s))`;

(* this only works in discrete probability spaces *)
val uniform_distribution_def = Define
   `uniform_distribution (s :'a algebra) =
      (\(a :'a set). (&CARD a / &CARD (space s)) :extreal)`;

(* Probability Density Function [11] *)
val PDF_def = Define `PDF p X = RN_deriv (distribution p X) lborel`;

(* ------------------------------------------------------------------------- *)
(*  Basic probability theorems                                               *)
(* ------------------------------------------------------------------------- *)

val POSITIVE_PROB = store_thm
  ("POSITIVE_PROB",
  ``!p. positive p <=> (prob p {} = 0) /\ !s. s IN events p ==> 0 <= prob p s``,
    RW_TAC std_ss [positive_def, prob_def, events_def]);

val INCREASING_PROB = store_thm
  ("INCREASING_PROB",
  ``!p. increasing p <=> !s t. s IN events p /\ t IN events p /\ s SUBSET t ==>
        prob p s <= prob p t``,
    RW_TAC std_ss [increasing_def, prob_def, events_def]);

val ADDITIVE_PROB = store_thm
  ("ADDITIVE_PROB",
  ``!p. additive p <=>
        !s t. s IN events p /\ t IN events p /\ DISJOINT s t /\ s UNION t IN events p ==>
              (prob p (s UNION t) = prob p s + prob p t)``,
    RW_TAC std_ss [additive_def, prob_def, events_def]);

val COUNTABLY_ADDITIVE_PROB = store_thm
  ("COUNTABLY_ADDITIVE_PROB",
  ``!p. countably_additive p <=>
        !f. f IN (UNIV -> events p) /\ (!m n. m <> n ==> DISJOINT (f m) (f n)) /\
            BIGUNION (IMAGE f UNIV) IN events p ==>
           (prob p (BIGUNION (IMAGE f UNIV)) = suminf (prob p o f))``,
    RW_TAC std_ss [countably_additive_def, prob_def, events_def]);

val PROB_SPACE = store_thm
  ("PROB_SPACE",
  ``!p. prob_space p <=> sigma_algebra (p_space p, events p) /\ positive p /\
                         countably_additive p /\ (prob p (p_space p) = 1)``,
    RW_TAC std_ss [prob_space_def, prob_def, events_def, measure_space_def, p_space_def]
 >> PROVE_TAC []);

val EVENTS_SIGMA_ALGEBRA = store_thm
  ("EVENTS_SIGMA_ALGEBRA", ``!p. prob_space p ==> sigma_algebra (p_space p, events p)``,
    RW_TAC std_ss [PROB_SPACE]);

val EVENTS_ALGEBRA = store_thm
  ("EVENTS_ALGEBRA", ``!p. prob_space p ==> algebra (p_space p, events p)``,
    PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, EVENTS_SIGMA_ALGEBRA]);

val PROB_EMPTY = store_thm
  ("PROB_EMPTY", ``!p. prob_space p ==> (prob p {} = 0)``,
    PROVE_TAC [PROB_SPACE, POSITIVE_PROB]);

val PROB_UNIV = store_thm
  ("PROB_UNIV", ``!p. prob_space p ==> (prob p (p_space p) = 1)``,
    RW_TAC std_ss [PROB_SPACE]);

val PROB_SPACE_POSITIVE = store_thm
  ("PROB_SPACE_POSITIVE", ``!p. prob_space p ==> positive p``,
    RW_TAC std_ss [PROB_SPACE]);

val PROB_SPACE_COUNTABLY_ADDITIVE = store_thm
  ("PROB_SPACE_COUNTABLY_ADDITIVE", ``!p. prob_space p ==> countably_additive p``,
    RW_TAC std_ss [PROB_SPACE]);

val PROB_SPACE_ADDITIVE = store_thm
  ("PROB_SPACE_ADDITIVE", ``!p. prob_space p ==> additive p``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC (REWRITE_RULE [premeasure_def] ALGEBRA_PREMEASURE_ADDITIVE)
 >> IMP_RES_TAC EVENTS_ALGEBRA
 >> fs [events_def, p_space_def]
 >> PROVE_TAC [PROB_SPACE_COUNTABLY_ADDITIVE, PROB_SPACE_POSITIVE]);

val PROB_SPACE_INCREASING = store_thm
  ("PROB_SPACE_INCREASING",
  ``!p. prob_space p ==> increasing p``,
    PROVE_TAC [ADDITIVE_INCREASING, EVENTS_ALGEBRA, PROB_SPACE_ADDITIVE,
               PROB_SPACE_POSITIVE, events_def, p_space_def]);

val PROB_POSITIVE = store_thm
  ("PROB_POSITIVE",
  ``!p s. prob_space p /\ s IN events p ==> 0 <= prob p s``,
    PROVE_TAC [POSITIVE_PROB, PROB_SPACE_POSITIVE]);

val PROB_SPACE_SUBSET_PSPACE = store_thm
  ("PROB_SPACE_SUBSET_PSPACE",
  ``!p s. prob_space p /\ s IN events p ==> s SUBSET p_space p``,
    RW_TAC std_ss [prob_space_def, events_def, p_space_def, MEASURE_SPACE_SUBSET_MSPACE]);

Theorem PROB_SPACE_IN_PSPACE :
    !p E. prob_space p /\ E IN events p ==> !x. x IN E ==> x IN p_space p
Proof
    RW_TAC std_ss [prob_space_def, events_def, p_space_def]
 >> irule MEASURE_SPACE_IN_MSPACE >> art []
 >> Q.EXISTS_TAC `E` >> art []
QED

(* Thus TONELLI and FUBINI theorems are applicable *)
Theorem PROB_SPACE_SIGMA_FINITE :
    !p. prob_space p ==> sigma_finite p
Proof
    RW_TAC std_ss [prob_space_def]
 >> MATCH_MP_TAC FINITE_IMP_SIGMA_FINITE
 >> rw [extreal_of_num_def, extreal_not_infty]
QED

val PROB_UNDER_UNIV = store_thm
  ("PROB_UNDER_UNIV",
  ``!p s. prob_space p /\ s IN events p ==> (prob p (s INTER p_space p) = prob p s)``,
    RW_TAC std_ss [prob_space_def, prob_def, events_def, p_space_def]
 >> `s SUBSET m_space p` by PROVE_TAC [MEASURE_SPACE_SUBSET_MSPACE]
 >> `s INTER m_space p = s` by PROVE_TAC [INTER_SUBSET_EQN] >> art []);

val PROB_INCREASING = store_thm
  ("PROB_INCREASING",
  ``!p s t. prob_space p /\ s IN events p /\ t IN events p /\ s SUBSET t ==>
            prob p s <= prob p t``,
    PROVE_TAC [INCREASING_PROB, PROB_SPACE_INCREASING]);

val PROB_ADDITIVE = store_thm
  ("PROB_ADDITIVE",
  ``!p s t u. prob_space p /\ s IN events p /\ t IN events p /\
              DISJOINT s t /\ (u = s UNION t) ==>
             (prob p u = prob p s + prob p t)``,
    rpt STRIP_TAC
 >> IMP_RES_TAC PROB_SPACE_ADDITIVE >> art []
 >> POP_ASSUM (MATCH_MP_TAC o (REWRITE_RULE [ADDITIVE_PROB]))
 >> art []
 >> IMP_RES_TAC EVENTS_ALGEBRA
 >> PROVE_TAC [ALGEBRA_UNION, subsets_def]);

val PROB_COUNTABLY_ADDITIVE = store_thm
  ("PROB_COUNTABLY_ADDITIVE",
  ``!p s f. prob_space p /\ f IN (UNIV -> events p) /\
           (!m n. m <> n ==> DISJOINT (f m) (f n)) /\ (s = BIGUNION (IMAGE f UNIV)) ==>
           (prob p s = suminf (prob p o f))``,
    RW_TAC std_ss []
 >> Suff `BIGUNION (IMAGE f UNIV) IN events p`
 >- PROVE_TAC [COUNTABLY_ADDITIVE_PROB, PROB_SPACE_COUNTABLY_ADDITIVE]
 >> (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
     Q.SPECL [`(p_space p, events p)`,`f`]) SIGMA_ALGEBRA_ENUM
 >> PROVE_TAC [EVENTS_SIGMA_ALGEBRA]);

val PROB_FINITE = store_thm
  ("PROB_FINITE",
  ``!p s. prob_space p /\ s IN events p ==> (prob p s <> NegInf /\ prob p s <> PosInf)``,
    RW_TAC std_ss [prob_space_def, prob_def, events_def, positive_not_infty, MEASURE_SPACE_POSITIVE]
 >> RW_TAC std_ss [GSYM le_infty,GSYM extreal_lt_def]
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC `measure p (m_space p)`
 >> reverse (RW_TAC std_ss [])
 >- METIS_TAC [num_not_infty,lt_infty]
 >> METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE, INCREASING, MEASURE_SPACE_INCREASING,
               MEASURE_SPACE_MSPACE_MEASURABLE]);

val PROB_LT_POSINF = store_thm
  ("PROB_LT_POSINF",
  ``!p s. prob_space p /\ s IN events p ==> prob p s < PosInf``,
    rpt GEN_TAC
 >> DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP PROB_FINITE))
 >> art [GSYM lt_infty]);

val PROB_COMPL = store_thm
  ("PROB_COMPL",
  ``!p s. prob_space p /\ s IN events p ==> (prob p (p_space p DIFF s) = 1 - prob p s)``,
    METIS_TAC [MEASURE_SPACE_FINITE_DIFF, PROB_FINITE,
               prob_space_def, events_def, prob_def, p_space_def]);

val PROB_DIFF_SUBSET = store_thm
  ("PROB_DIFF_SUBSET",
  ``!p s t.
       prob_space p /\ s IN events p /\ t IN events p /\ (t SUBSET s) ==>
       (prob p (s DIFF t) = prob p s - prob p t)``,
    rpt STRIP_TAC
 >> `prob p t < PosInf` by PROVE_TAC [PROB_LT_POSINF]
 >> fs [prob_space_def, prob_def, events_def]
 >> MATCH_MP_TAC MEASURE_DIFF_SUBSET >> art []);

val PSPACE = store_thm
  ("PSPACE", ``!a b c. p_space (a, b, c) = a``,
    RW_TAC std_ss [p_space_def, m_space_def]);

val EVENTS = store_thm
  ("EVENTS", ``!a b c. events (a, b, c) = b``,
    RW_TAC std_ss [events_def, measurable_sets_def]);

val PROB = store_thm
  ("PROB", ``!a b c. prob (a, b, c) = c``,
    RW_TAC std_ss [prob_def, measure_def]);

val EVENTS_INTER = store_thm
  ("EVENTS_INTER",
  ``!p s t. prob_space p /\ s IN events p /\ t IN events p ==> s INTER t IN events p``,
  RW_TAC std_ss []
  >> (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
      Q.SPEC `(p_space p, events p)`) ALGEBRA_INTER
  >> PROVE_TAC [PROB_SPACE, SIGMA_ALGEBRA_ALGEBRA]);

val EVENTS_EMPTY = store_thm
  ("EVENTS_EMPTY", ``!p. prob_space p ==> {} IN events p``,
  RW_TAC std_ss []
  >> (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
      Q.SPEC `(p_space p, events p)`) ALGEBRA_EMPTY
  >> PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, PROB_SPACE]);

val EVENTS_SPACE = store_thm
  ("EVENTS_SPACE", ``!p. prob_space p ==> (p_space p) IN events p``,
    RW_TAC std_ss []
 >> (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
     Q.SPEC `(p_space p, events p)`) ALGEBRA_SPACE
 >> PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, PROB_SPACE]);

val EVENTS_UNION = store_thm
  ("EVENTS_UNION",
  ``!p s t. prob_space p /\ s IN events p /\ t IN events p ==> s UNION t IN events p``,
    RW_TAC std_ss []
 >> (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
     Q.SPEC `(p_space p, events p)`) ALGEBRA_UNION
 >> PROVE_TAC [PROB_SPACE, SIGMA_ALGEBRA_ALGEBRA]);

val INTER_PSPACE = store_thm
  ("INTER_PSPACE", ``!p s. prob_space p /\ s IN events p ==> (p_space p INTER s = s)``,
    RW_TAC std_ss [PROB_SPACE, SIGMA_ALGEBRA, space_def, subsets_def, subset_class_def,
                   SUBSET_DEF]
 >> RW_TAC std_ss [Once EXTENSION, IN_INTER]
 >> PROVE_TAC []);

(* `P` is usually a higher order term, `s` is a simple events, e.g. `p_space p` *)
val PROB_GSPEC = store_thm (* new *)
  ("PROB_GSPEC",
  ``!P p s. prob p {x | x IN s /\ P x} = prob p ({x | P x} INTER s)``,
    RW_TAC std_ss []
 >> Suff `{x | x IN s /\ P x} = {x | P x} INTER s` >- METIS_TAC []
 >> RW_TAC std_ss [Once EXTENSION, GSPECIFICATION, IN_INTER]
 >> METIS_TAC []);

val EVENTS_DIFF = store_thm
  ("EVENTS_DIFF",
  ``!p s t. prob_space p /\ s IN events p /\ t IN events p ==> s DIFF t IN events p``,
    RW_TAC std_ss []
 >> (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
     Q.SPEC `(p_space p, events p)`) ALGEBRA_DIFF
 >> PROVE_TAC [PROB_SPACE, SIGMA_ALGEBRA_ALGEBRA]);

val EVENTS_COMPL = store_thm
  ("EVENTS_COMPL", ``!p s. prob_space p /\ s IN events p ==> (p_space p) DIFF s IN events p``,
    RW_TAC std_ss []
 >> (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
     Q.SPEC `(p_space p, events p)`) ALGEBRA_COMPL
 >> PROVE_TAC [PROB_SPACE, SIGMA_ALGEBRA_ALGEBRA]);

Theorem EVENTS_BIGUNION :
    !p f n. prob_space p /\ (f IN ((count n) -> events p)) ==>
            BIGUNION (IMAGE f (count n)) IN events p
Proof
    RW_TAC std_ss [IN_FUNSET, IN_COUNT]
 >> `BIGUNION (IMAGE f (count n)) = BIGUNION (IMAGE (\m. (if m < n then f m else {})) UNIV)`
     by (RW_TAC std_ss [EXTENSION,IN_BIGUNION_IMAGE, IN_COUNT, IN_UNIV] >> METIS_TAC [NOT_IN_EMPTY])
 >> POP_ORW
 >> (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
        Q.SPECL [`(p_space p, events p)`,`(\m. if m < n then A m else {})`]) SIGMA_ALGEBRA_ENUM
 >> RW_TAC std_ss [EVENTS_SIGMA_ALGEBRA] >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, DISJOINT_EMPTY]
 >> METIS_TAC [EVENTS_EMPTY]
QED

val EVENTS_COUNTABLE_UNION = store_thm
  ("EVENTS_COUNTABLE_UNION",
  ``!p c. prob_space p /\ c SUBSET events p /\ countable c ==> BIGUNION c IN events p``,
    RW_TAC std_ss []
 >> (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
     Q.SPEC `(p_space p, events p)`) SIGMA_ALGEBRA_COUNTABLE_UNION
 >> RW_TAC std_ss [EVENTS_SIGMA_ALGEBRA]);

val PROB_ZERO_UNION = store_thm
  ("PROB_ZERO_UNION",
  ``!p s t. prob_space p /\ s IN events p /\ t IN events p /\ (prob p t = 0) ==>
           (prob p (s UNION t) = prob p s)``,
    RW_TAC std_ss []
 >> Know `t DIFF s IN events p`
 >- (MATCH_MP_TAC EVENTS_DIFF >> RW_TAC std_ss [])
 >> STRIP_TAC
 >> Know `prob p (t DIFF s) = 0`
 >- (ONCE_REWRITE_TAC [GSYM le_antisym]
     >> reverse CONJ_TAC >- PROVE_TAC [PROB_POSITIVE]
     >> Q.PAT_X_ASSUM `prob p t = 0` (ONCE_REWRITE_TAC o wrap o SYM)
     >> MATCH_MP_TAC PROB_INCREASING
     >> RW_TAC std_ss [DIFF_SUBSET])
 >> STRIP_TAC
 >> Suff `prob p (s UNION t) = prob p s + prob p (t DIFF s)`
 >- RW_TAC real_ss [add_rzero]
 >> MATCH_MP_TAC PROB_ADDITIVE
 >> RW_TAC std_ss [DISJOINT_DEF, DIFF_DEF, EXTENSION, IN_UNION, IN_DIFF, NOT_IN_EMPTY, IN_INTER]
 >> PROVE_TAC []);

Theorem PROB_INTER_ZERO :
    !p A B. prob_space p /\ A IN events p /\ B IN events p /\ (prob p B = 0) ==>
           (prob p (A INTER B) = 0)
Proof
    RW_TAC std_ss []
 >> `(A INTER B) SUBSET B` by RW_TAC std_ss [INTER_SUBSET]
 >> `prob p (A INTER B) <= prob p B` by FULL_SIMP_TAC std_ss [PROB_INCREASING, EVENTS_INTER]
 >> `0 <= prob p (A INTER B)` by FULL_SIMP_TAC std_ss [PROB_POSITIVE, EVENTS_INTER]
 >> METIS_TAC [le_antisym]
QED

Theorem PROB_ZERO_INTER :
    !p A B. prob_space p /\ A IN events p /\ B IN events p /\ (prob p A = 0) ==>
           (prob p (A INTER B) = 0)
Proof
    RW_TAC std_ss [] >> (MP_TAC o Q.SPECL [`p`, `B`, `A`]) PROB_INTER_ZERO
 >> RW_TAC std_ss [INTER_COMM]
QED

val PROB_EQ_COMPL = store_thm
  ("PROB_EQ_COMPL",
  ``!p s t. prob_space p /\ s IN events p /\ t IN events p /\
           (prob p (p_space p DIFF s) = prob p (p_space p DIFF t)) ==> (prob p s = prob p t)``,
    RW_TAC std_ss []
 >> Know `1 - prob p s = 1 - prob p t`
 >- (POP_ASSUM MP_TAC >> RW_TAC std_ss [PROB_COMPL])
 >> `?r1 r2. (prob p t = Normal r1) /\ (prob p s = Normal r2)`
     by METIS_TAC [extreal_cases,PROB_FINITE]
 >> FULL_SIMP_TAC std_ss [extreal_of_num_def,extreal_sub_def,extreal_11]
 >> REAL_ARITH_TAC);

val PROB_ONE_INTER = store_thm
  ("PROB_ONE_INTER",
  ``!p s t. prob_space p /\ s IN events p /\ t IN events p /\ (prob p t = 1) ==>
           (prob p (s INTER t) = prob p s)``,
    RW_TAC std_ss []
 >> MATCH_MP_TAC PROB_EQ_COMPL
 >> RW_TAC std_ss [EVENTS_INTER]
 >> Know `p_space p DIFF s INTER t = (p_space p DIFF s) UNION (p_space p DIFF t)`
 >- (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_UNION, IN_DIFF]
     >> DECIDE_TAC)
 >> RW_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
 >> MATCH_MP_TAC PROB_ZERO_UNION
 >> RW_TAC std_ss [PROB_COMPL, EVENTS_COMPL]
 >> RW_TAC real_ss [extreal_of_num_def,extreal_sub_def]);

val EVENTS_COUNTABLE_INTER = store_thm
  ("EVENTS_COUNTABLE_INTER",
  ``!p c. prob_space p /\ c SUBSET events p /\ countable c /\ c <> {} ==>
          BIGINTER c IN events p``,
    RW_TAC std_ss []
 >> Know `BIGINTER c = p_space p DIFF (p_space p DIFF (BIGINTER c))`
 >- (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_DIFF, LEFT_AND_OVER_OR, IN_BIGINTER]
     >> FULL_SIMP_TAC std_ss [PROB_SPACE, SIGMA_ALGEBRA, subset_class_def,
                              subsets_def, space_def, SUBSET_DEF]
     >> EQ_TAC
     >- (Know `(c = {}) \/ ?x t. (c = x INSERT t) /\ ~(x IN t)` >- PROVE_TAC [SET_CASES]
         >> RW_TAC std_ss []
         >> PROVE_TAC [IN_INSERT])
     >> PROVE_TAC [])
 >> Rewr'
 >> MATCH_MP_TAC EVENTS_COMPL
 >> Know `p_space p DIFF BIGINTER c = BIGUNION (IMAGE (\s. p_space p DIFF s) c)`
 >- (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_DIFF, IN_BIGUNION, IN_IMAGE, IN_BIGINTER]
     >> EQ_TAC
     >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `p_space p DIFF P`
         >> RW_TAC std_ss [IN_DIFF] >> Q.EXISTS_TAC `P`
         >> RW_TAC std_ss [])
     >> RW_TAC std_ss []
     >- FULL_SIMP_TAC std_ss [IN_DIFF]
     >> Q.EXISTS_TAC `s'`
     >> FULL_SIMP_TAC std_ss [IN_DIFF])
 >> RW_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
 >> MATCH_MP_TAC EVENTS_COUNTABLE_UNION
 >> Q.PAT_X_ASSUM `c SUBSET events p` MP_TAC
 >> RW_TAC std_ss [image_countable, SUBSET_DEF, IN_IMAGE]
 >> PROVE_TAC [EVENTS_COMPL]);

val EVENTS_BIGINTER_FN = store_thm
  ("EVENTS_BIGINTER_FN",
  ``!p A J. prob_space p /\ (IMAGE A J) SUBSET events p /\ countable J /\ J <> {} ==>
            BIGINTER (IMAGE A J) IN events p``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC EVENTS_COUNTABLE_INTER >> art []
 >> CONJ_TAC
 >- (MATCH_MP_TAC image_countable >> art [])
 >> RW_TAC std_ss [Once EXTENSION, IN_IMAGE, NOT_IN_EMPTY]
 >> fs [GSYM MEMBER_NOT_EMPTY]
 >> Q.EXISTS_TAC `x` >> art []);

val ABS_PROB = store_thm
  ("ABS_PROB", ``!p s. prob_space p /\ s IN events p ==> (abs (prob p s) = prob p s)``,
    RW_TAC std_ss [extreal_abs_def]
 >> PROVE_TAC [PROB_POSITIVE,abs_refl]);

val PROB_COMPL_LE1 = store_thm
  ("PROB_COMPL_LE1",
  ``!p s r. prob_space p /\ s IN events p ==>
           (prob p (p_space p DIFF s) <= r <=> 1 - r <= prob p s)``,
    RW_TAC std_ss [PROB_COMPL]
 >> METIS_TAC [sub_le_switch2,PROB_FINITE,num_not_infty]);

val PROB_LE_1 = store_thm
  ("PROB_LE_1", ``!p s. prob_space p /\ s IN events p ==> prob p s <= 1``,
    RW_TAC std_ss []
 >> Suff `0 <= 1 - prob p s` >- METIS_TAC [sub_zero_le,PROB_FINITE]
 >> RW_TAC std_ss [GSYM PROB_COMPL]
 >> RW_TAC std_ss [EVENTS_COMPL, PROB_POSITIVE]);

Theorem PROB_EQ_BIGUNION_IMAGE :
    !p f g. prob_space p /\ f IN (UNIV -> events p) /\ g IN (UNIV -> events p) /\
           (!m n. m <> n ==> DISJOINT (f m) (f n)) /\
           (!m n. m <> n ==> DISJOINT (g m) (g n)) /\
           (!n :num. prob p (f n) = prob p (g n)) ==>
       (prob p (BIGUNION (IMAGE f UNIV)) = prob p (BIGUNION (IMAGE g UNIV)))
Proof
    RW_TAC std_ss []
 >> Know `prob p (BIGUNION (IMAGE f UNIV)) = suminf (prob p o f)`
 >- PROVE_TAC [PROB_COUNTABLY_ADDITIVE]
 >> Know `prob p (BIGUNION (IMAGE g UNIV)) = suminf (prob p o g)`
 >- PROVE_TAC [PROB_COUNTABLY_ADDITIVE]
 >> METIS_TAC [o_DEF]
QED

val ABS_1_MINUS_PROB = store_thm
  ("ABS_1_MINUS_PROB",
 ``!p s. prob_space p /\ s IN events p /\ ~(prob p s = 0) ==> abs (1 - prob p s) < 1``,
   RW_TAC std_ss []
 >> Know `0 <= prob p s` >- PROVE_TAC [PROB_POSITIVE]
 >> Know `prob p s <= 1` >- PROVE_TAC [PROB_LE_1]
 >> `?r. prob p s = Normal r` by METIS_TAC [PROB_FINITE,extreal_cases]
 >> FULL_SIMP_TAC std_ss [extreal_of_num_def,extreal_sub_def,extreal_abs_def,
                          extreal_lt_eq,extreal_le_def,extreal_11]
 >> RW_TAC std_ss [abs]
 >> rpt (POP_ASSUM MP_TAC)
 >> REAL_ARITH_TAC);

val PROB_INCREASING_UNION = store_thm
  ("PROB_INCREASING_UNION",
  ``!p f. prob_space p /\ f IN (UNIV -> events p) /\ (!n. f n SUBSET f (SUC n)) ==>
         (sup (IMAGE (prob p o f) UNIV) = prob p (BIGUNION (IMAGE f UNIV)))``,
    RW_TAC std_ss [prob_space_def, events_def, prob_def, MONOTONE_CONVERGENCE]);

val PROB_SUBADDITIVE = store_thm
  ("PROB_SUBADDITIVE",
  ``!p t u. prob_space p /\ t IN events p /\ u IN events p ==>
            prob p (t UNION u) <= prob p t + prob p u``,
   RW_TAC std_ss []
   >> Know `t UNION u = t UNION (u DIFF t)`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [IN_UNION, IN_DIFF]
       >> PROVE_TAC [])
   >> Rewr
   >> Know `u DIFF t IN events p`
   >- PROVE_TAC [EVENTS_DIFF]
   >> STRIP_TAC
   >> Know `prob p (t UNION (u DIFF t)) = prob p t + prob p (u DIFF t)`
   >- (MATCH_MP_TAC PROB_ADDITIVE
       >> RW_TAC std_ss [DISJOINT_ALT, IN_DIFF])
   >> Rewr
   >> MATCH_MP_TAC le_ladd_imp
   >> MATCH_MP_TAC PROB_INCREASING
   >> RW_TAC std_ss [DIFF_DEF, SUBSET_DEF, GSPECIFICATION]);

Theorem PROB_COUNTABLY_SUBADDITIVE :
    !p f. prob_space p /\ (IMAGE f UNIV) SUBSET events p ==>
          prob p (BIGUNION (IMAGE f UNIV)) <= suminf (prob p o f)
Proof
    RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV]
 >> Know `!n. 0 <= (prob p o f) n`
 >- (RW_TAC std_ss [o_DEF] \\
     POP_ASSUM (ASSUME_TAC o (Q.SPEC `(f :num -> 'a -> bool) n`)) \\
     MATCH_MP_TAC PROB_POSITIVE >> art [] \\
     POP_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC `n` >> art [])
 >> DISCH_THEN (MP_TAC o (MATCH_MP ext_suminf_def)) >> Rewr'
 >> Suff `prob p (BIGUNION (IMAGE f UNIV)) =
                  sup (IMAGE (prob p o (\n. BIGUNION (IMAGE f (count n)))) UNIV)`
 >- (RW_TAC std_ss []
      >> MATCH_MP_TAC sup_mono
      >> RW_TAC std_ss [o_DEF]
      >> Induct_on `n`
      >- RW_TAC std_ss [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY, PROB_EMPTY,
                        EXTREAL_SUM_IMAGE_EMPTY, le_refl]
      >> RW_TAC std_ss [COUNT_SUC, IMAGE_INSERT, BIGUNION_INSERT]
      >> (MP_TAC o Q.SPEC `n` o REWRITE_RULE [FINITE_COUNT,o_DEF] o
          Q.SPECL [`prob p o f`,`count n`] o INST_TYPE [alpha |-> ``:num``])
             EXTREAL_SUM_IMAGE_PROPERTY
      >> `(!x. x IN n INSERT count n ==> prob p (f x) <> NegInf)` by METIS_TAC [PROB_FINITE]
      >> RW_TAC std_ss [COUNT_SUC]
      >> `~(n < n)` by RW_TAC real_ss []
      >> `count n DELETE n = count n` by METIS_TAC [DELETE_NON_ELEMENT,IN_COUNT]
      >> RW_TAC std_ss []
      >> `prob p (f n UNION BIGUNION (IMAGE f (count n))) <=
          prob p (f n) + prob p (BIGUNION (IMAGE f (count n)))`
          by (MATCH_MP_TAC PROB_SUBADDITIVE
              >> RW_TAC std_ss []
              >- METIS_TAC []
              >> MATCH_MP_TAC EVENTS_COUNTABLE_UNION
              >> RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT, image_countable,
                     COUNTABLE_COUNT]
              >> METIS_TAC [])
      >> METIS_TAC [le_ladd_imp, le_trans])
 >> (MP_TAC o Q.SPECL [`p`,`(\n. BIGUNION (IMAGE f (count n)))`]) PROB_INCREASING_UNION
 >> RW_TAC std_ss []
 >> `BIGUNION (IMAGE (\n. BIGUNION (IMAGE f (count n))) UNIV) = BIGUNION (IMAGE f UNIV)`
       by (RW_TAC std_ss [EXTENSION,IN_BIGUNION_IMAGE,IN_UNIV,IN_COUNT]
           >> METIS_TAC [DECIDE ``x < SUC x``])
 >> FULL_SIMP_TAC std_ss []
 >> POP_ASSUM (K ALL_TAC)
 >> POP_ASSUM (MATCH_MP_TAC o GSYM)
 >> RW_TAC std_ss [IN_FUNSET,IN_UNIV]
 >- (MATCH_MP_TAC EVENTS_COUNTABLE_UNION
     >> RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT, image_countable, COUNTABLE_COUNT]
     >> METIS_TAC [])
 >> RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_COUNT]
 >> METIS_TAC [DECIDE ``n < SUC n``, LESS_TRANS]
QED

Theorem PROB_COUNTABLY_ZERO :
    !p c. prob_space p /\ countable c /\ c SUBSET events p /\
          (!x. x IN c ==> (prob p x = 0)) ==> (prob p (BIGUNION c) = 0)
Proof
    RW_TAC std_ss [COUNTABLE_ENUM]
 >- RW_TAC std_ss [BIGUNION_EMPTY, PROB_EMPTY]
 >> Know `(!n. prob p (f n) = 0) /\ (!n. f n IN events p)`
 >- (FULL_SIMP_TAC std_ss [IN_IMAGE, IN_UNIV, SUBSET_DEF] \\
     PROVE_TAC [])
 >> NTAC 2 (POP_ASSUM K_TAC)
 >> STRIP_TAC
 >> ONCE_REWRITE_TAC [GSYM le_antisym]
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC PROB_POSITIVE \\
     RW_TAC std_ss [] \\
     MATCH_MP_TAC EVENTS_COUNTABLE_UNION \\
     RW_TAC std_ss [COUNTABLE_IMAGE_NUM, SUBSET_DEF, IN_IMAGE, IN_UNIV] \\
     RW_TAC std_ss [])
 >> Know `!n. 0 <= (prob p o f) n`
 >- RW_TAC std_ss [o_DEF, le_refl] >> DISCH_TAC
 >> Know `suminf (prob p o f) = 0`
 >- RW_TAC std_ss [ext_suminf_def, o_DEF, EXTREAL_SUM_IMAGE_ZERO, FINITE_COUNT,
                   sup_const_over_set, UNIV_NOT_EMPTY]
 >> RW_TAC std_ss []
 >> POP_ASSUM (REWRITE_TAC o wrap o SYM)
 >> MATCH_MP_TAC PROB_COUNTABLY_SUBADDITIVE
 >> RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV]
 >> RW_TAC std_ss []
QED

(* This theorem is more general than measureTheory.FINITE_ADDITIVE:

  `f :'b -> 'a -> bool` has an finite index set of type ('b set)
 *)
Theorem PROB_FINITE_ADDITIVE :
    !p s f t. prob_space p /\ FINITE s /\ (!x. x IN s ==> f x IN events p) /\
             (!a b. (a :'b) IN s /\ b IN s /\ a <> b ==> DISJOINT (f a) (f b)) /\
             (t = BIGUNION (IMAGE f s)) ==> (prob p t = SIGMA (prob p o f) s)
Proof
    Suff `!s. FINITE (s:'b -> bool) ==>
        ((\s. !p f t. prob_space p  /\ (!x. x IN s ==> f x IN events p) /\
        (!a b. a IN s /\ b IN s /\ a <> b ==> DISJOINT (f a) (f b)) /\
        (t = BIGUNION (IMAGE f s)) ==> (prob p t = SIGMA (prob p o f) s)) s)`
 >- rw []
 >> MATCH_MP_TAC FINITE_INDUCT >> RW_TAC std_ss [IMAGE_EMPTY]
 >- RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, BIGUNION_EMPTY, PROB_EMPTY]
 >> Know `SIGMA (prob p o f) ((e:'b) INSERT s) =
                (prob p o f) e + SIGMA (prob p o f) (s DELETE e)`
 >- (irule EXTREAL_SUM_IMAGE_PROPERTY >> art [] \\
     DISJ1_TAC >> GEN_TAC >> DISCH_TAC \\
     SIMP_TAC std_ss [o_DEF] >> METIS_TAC [PROB_FINITE])
 >> `s DELETE (e:'b) = s` by FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
 >> RW_TAC std_ss [IMAGE_INSERT, BIGUNION_INSERT]
 >> Know `DISJOINT (f e) (BIGUNION (IMAGE f s))`
 >- (RW_TAC set_ss [DISJOINT_BIGUNION, IN_IMAGE] \\
    `e IN e INSERT s` by PROVE_TAC [IN_INSERT] \\
    `x IN e INSERT s` by PROVE_TAC [IN_INSERT] \\
    `e <> x` by METIS_TAC [] \\
     FULL_SIMP_TAC std_ss []) >> DISCH_TAC
 >> `(f e) IN events p` by PROVE_TAC [IN_INSERT]
 >> `BIGUNION (IMAGE f s) IN events p`
        by (MATCH_MP_TAC EVENTS_COUNTABLE_UNION >> RW_TAC std_ss []
           >- (RW_TAC std_ss [SUBSET_DEF,IN_IMAGE] >> METIS_TAC [IN_INSERT])
           >> MATCH_MP_TAC image_countable >> RW_TAC std_ss [finite_countable])
 >> `(prob p (f e UNION BIGUNION (IMAGE f s))) = prob p (f e) + prob p (BIGUNION (IMAGE f s))`
        by (MATCH_MP_TAC PROB_ADDITIVE >> FULL_SIMP_TAC std_ss [])
 >> POP_ORW
 >> Suff `prob p (BIGUNION (IMAGE f s)) = SIGMA (prob p o f) s` >- rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> rw [IN_INSERT]
QED

val PROB_EXTREAL_SUM_IMAGE = store_thm
  ("PROB_EXTREAL_SUM_IMAGE",
  ``!p s. prob_space p /\ s IN events p /\ (!x. x IN s ==> {x} IN events p) /\ FINITE s ==>
         (prob p s = SIGMA (\x. prob p {x}) s)``,
  Suff `!s. FINITE s ==>
        (\s. !p. prob_space p /\ s IN events p /\ (!x. x IN s ==> {x} IN events p) ==>
             (prob p s = SIGMA (\x. prob p {x}) s)) s`
  >- METIS_TAC []
  >> MATCH_MP_TAC FINITE_INDUCT
  >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY,PROB_EMPTY,IN_INSERT]
  >> (MP_TAC o Q.SPEC `e` o UNDISCH o Q.SPECL [`(\x. prob p {x})`,`s`]) EXTREAL_SUM_IMAGE_PROPERTY
  >> `!x. x IN e INSERT s ==> (\x. prob p {x}) x <> NegInf` by METIS_TAC [PROB_FINITE,IN_INSERT]
  >> RW_TAC std_ss []
  >> Q.PAT_X_ASSUM `!p. prob_space p /\ s IN events p /\
            (!x. x IN s ==> {x} IN events p) ==>
            (prob p s = SIGMA (\x. prob p {x}) s)` (MP_TAC o GSYM o Q.SPEC `p`)
  >> RW_TAC std_ss []
  >> `s IN events p`
      by (`s = (e INSERT s) DIFF {e}`
             by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DIFF, IN_SING] \\
                 METIS_TAC [GSYM DELETE_NON_ELEMENT])
          >> POP_ORW
          >> FULL_SIMP_TAC std_ss [prob_space_def, measure_space_def, sigma_algebra_def, events_def]
          >> METIS_TAC [space_def, subsets_def, ALGEBRA_DIFF])
  >> FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
  >> MATCH_MP_TAC PROB_ADDITIVE
  >> RW_TAC std_ss [IN_DISJOINT, IN_SING, Once INSERT_SING_UNION]
  >> FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]);

val PROB_EQUIPROBABLE_FINITE_UNIONS = store_thm
  ("PROB_EQUIPROBABLE_FINITE_UNIONS",
  ``!p s. prob_space p /\ FINITE s /\ s IN events p /\ (!x. x IN s ==> {x} IN events p) /\
         (!x y. x IN s /\ y IN s ==> (prob p {x} = prob p {y})) ==>
         (prob p s = & (CARD s) * prob p {CHOICE s})``,
   RW_TAC std_ss []
   >> Cases_on `s = {}`
   >- RW_TAC real_ss [PROB_EMPTY, CARD_EMPTY,mul_lzero]
   >> `prob p s = SIGMA (\x. prob p {x}) s`
        by METIS_TAC [PROB_EXTREAL_SUM_IMAGE]
   >> POP_ORW
   >> `prob p {CHOICE s} = (\x. prob p {x}) (CHOICE s)` by RW_TAC std_ss []
   >> POP_ORW
   >> (MATCH_MP_TAC o UNDISCH o Q.SPEC `s`) EXTREAL_SUM_IMAGE_FINITE_SAME
   >> RW_TAC std_ss [CHOICE_DEF]
   >> METIS_TAC [PROB_FINITE]);

val PROB_EXTREAL_SUM_IMAGE_FN = store_thm
  ("PROB_EXTREAL_SUM_IMAGE_FN",
  ``!p f e s. prob_space p /\ e IN events p /\
             (!x. x IN s ==> e INTER f x IN events p) /\ FINITE s /\
             (!x y. x IN s /\ y IN s /\ (~(x=y)) ==> DISJOINT (f x) (f y)) /\
             (BIGUNION (IMAGE f s) INTER p_space p = p_space p) ==>
             (prob p e = SIGMA (\x. prob p (e INTER f x)) s)``,
   Suff `!(s :'b -> bool). FINITE s ==>
        (\s. !(p :('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> extreal))
       (f :'b -> 'a -> bool) (e :'a -> bool). prob_space p /\ e IN events p /\
                (!x. x IN s ==> e INTER f x IN events p) /\
                (!x y. x IN s /\ y IN s /\ (~(x=y)) ==> DISJOINT (f x) (f y)) /\
                (BIGUNION (IMAGE f s) INTER p_space p = p_space p) ==>
                (prob p e = SIGMA (\x. prob p (e INTER f x)) s)) s`
   >- METIS_TAC []
   >> MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, PROB_EMPTY, DELETE_NON_ELEMENT, IN_INSERT,
                     IMAGE_EMPTY, BIGUNION_EMPTY, INTER_EMPTY]
   >- METIS_TAC [PROB_UNIV, PROB_EMPTY, REAL_10,extreal_of_num_def,extreal_11]
   >> (MP_TAC o Q.SPEC `e` o UNDISCH o Q.SPECL [`(\x. prob p (e' INTER f x))`,`s`] o
       INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY
   >> `!x. x IN e INSERT s ==> (\x. prob p (e' INTER f x)) x <> NegInf`
      by METIS_TAC [PROB_FINITE,IN_INSERT]
   >> RW_TAC std_ss []
   >> `prob p e' =
        prob p (e' INTER f e) +
        prob p (e' DIFF f e)`
        by (MATCH_MP_TAC PROB_ADDITIVE
            >> RW_TAC std_ss []
            >| [`e' DIFF f e = e' DIFF (e' INTER f e)`
                by (RW_TAC std_ss [EXTENSION, IN_DIFF, IN_INTER] >> DECIDE_TAC)
                >> POP_ORW
                >> METIS_TAC [EVENTS_DIFF],
                FULL_SIMP_TAC std_ss [IN_DISJOINT, IN_INTER, IN_DIFF] >> METIS_TAC [],
                RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_UNION, IN_DIFF] >> DECIDE_TAC])
   >> POP_ORW
   >> RW_TAC std_ss [EXTREAL_EQ_LADD,PROB_FINITE]
   >> (MP_TAC o Q.ISPEC `(s :'b -> bool)`) SET_CASES
   >> RW_TAC std_ss []
   >- (RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY]
       >> `IMAGE f {e} = {f e}`
                by RW_TAC std_ss [EXTENSION, IN_IMAGE, IN_SING]
       >> FULL_SIMP_TAC std_ss [BIGUNION_SING, DIFF_UNIV, PROB_EMPTY]
       >> `e' DIFF f e = {}`
                by (RW_TAC std_ss [Once EXTENSION, NOT_IN_EMPTY, IN_DIFF]
                    >> METIS_TAC [SUBSET_DEF, MEASURABLE_SETS_SUBSET_SPACE, prob_space_def,
                                  events_def, p_space_def, IN_INTER])
       >> RW_TAC std_ss [PROB_EMPTY])
   >> Q.PAT_X_ASSUM `!p f e.
            prob_space p /\ e IN events p /\
            (!x. x IN s ==> e INTER f x IN events p) /\
            (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y)) /\
            (BIGUNION (IMAGE f s) INTER p_space p = p_space p) ==>
            (prob p e = SIGMA (\x. prob p (e INTER f x)) s)`
        (MP_TAC o Q.SPECL [`p`,`(\y. if y = x then f x UNION f e else f y)`,`e' DIFF f e`])
   >> ASM_SIMP_TAC std_ss []
   >> `e' DIFF f e IN events p`
        by (`e' DIFF f e = e' DIFF (e' INTER f e)`
                by (RW_TAC std_ss [EXTENSION, IN_DIFF, IN_INTER] >> DECIDE_TAC)
                >> POP_ORW
                >> METIS_TAC [EVENTS_DIFF])
   >> ASM_SIMP_TAC std_ss []
   >> `(!x'.
        x' IN x INSERT t ==>
        (e' DIFF f e) INTER (if x' = x then f x UNION f e else f x') IN
        events p)`
        by (RW_TAC std_ss []
            >- (`(e' DIFF f e) INTER (f x UNION f e) =
                 e' INTER f x`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_DIFF, IN_UNION]
                    >> FULL_SIMP_TAC std_ss [IN_DISJOINT, GSYM DELETE_NON_ELEMENT]
                    >> METIS_TAC [])
                >> RW_TAC std_ss [])
            >> `(e' DIFF f e) INTER f x' =
                (e' INTER f x') DIFF (e' INTER f e)`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_DIFF]
                    >> FULL_SIMP_TAC std_ss [IN_DISJOINT, GSYM DELETE_NON_ELEMENT]
                    >> METIS_TAC [])
            >> METIS_TAC [EVENTS_DIFF])
   >> ASM_SIMP_TAC std_ss []
   >> `(!x' y.
        x' IN x INSERT t /\ y IN x INSERT t /\ ~(x' = y) ==>
        DISJOINT (if x' = x then f x UNION f e else f x')
          (if y = x then f x UNION f e else f y))`
        by (RW_TAC std_ss [IN_DISJOINT, IN_UNION]
            >> FULL_SIMP_TAC std_ss [IN_DISJOINT, GSYM DELETE_NON_ELEMENT]
            >> METIS_TAC [])
   >> ASM_SIMP_TAC std_ss []
   >> `(BIGUNION
        (IMAGE (\y. (if y = x then f x UNION f e else f y)) (x INSERT t)) INTER p_space p = p_space p)`
        by (FULL_SIMP_TAC std_ss [IMAGE_INSERT, BIGUNION_INSERT]
            >> `IMAGE (\y. (if y = x then f x UNION f e else f y)) t =
                IMAGE f t`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_IMAGE]
                    >> EQ_TAC
                    >- (RW_TAC std_ss [] >> METIS_TAC [])
                    >> RW_TAC std_ss [] >> METIS_TAC [])
            >> POP_ORW
            >> METIS_TAC [UNION_COMM, UNION_ASSOC])
   >> ASM_SIMP_TAC std_ss []
   >> STRIP_TAC >> POP_ASSUM (K ALL_TAC)
   >> FULL_SIMP_TAC std_ss [FINITE_INSERT]
   >> (MP_TAC o Q.SPEC `x` o UNDISCH o Q.SPECL [`(\x. prob p (e' INTER f x))`,`t`] o
       INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY
   >> `!x'. x' IN x INSERT t ==> (\x. prob p (e' INTER f x)) x' <> NegInf`
        by METIS_TAC [PROB_FINITE,IN_INSERT]
   >> RW_TAC std_ss []
   >> (MP_TAC o Q.SPEC `x` o UNDISCH o
       Q.SPECL [`(\x'. prob p ((e' DIFF f e) INTER if x' = x then f x UNION f e else f x'))`,`t`] o
       INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY
   >> `!x'. x' IN x INSERT t ==>
            (\x'. prob p ((e' DIFF f e) INTER
                          if x' = x then f x UNION f e else f x')) x' <> NegInf`
        by METIS_TAC [PROB_FINITE,IN_INSERT]
   >> RW_TAC std_ss []
   >> FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
   >> FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]
   >> `(e' DIFF f e) INTER (f x UNION f e) = e' INTER f x`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, IN_DIFF, IN_UNION]
            >> FULL_SIMP_TAC std_ss [IN_DISJOINT, GSYM DELETE_NON_ELEMENT, IN_INSERT]
            >> METIS_TAC [])
   >> FULL_SIMP_TAC std_ss [EXTREAL_EQ_LADD,PROB_FINITE,IN_INSERT]
   >> (MP_TAC o Q.SPEC `(\x. prob p (e' INTER f x))` o
       UNDISCH o Q.ISPEC `(t :'b -> bool)`) EXTREAL_SUM_IMAGE_IN_IF
   >> (MP_TAC o Q.SPEC `(\x'. prob p ((e' DIFF f e) INTER
                                      if x' = x then f x UNION f e else f x'))` o
       UNDISCH o Q.ISPEC `(t :'b -> bool)`) EXTREAL_SUM_IMAGE_IN_IF
   >> RW_TAC std_ss []
   >> Suff `(\x'.
         (if x' IN t then
            (\x'.
               prob p
                 ((e' DIFF f e) INTER
                  (if x' = x then f x UNION f e else f x'))) x'
          else
            0)) =
        (\x. (if x IN t then (\x. prob p (e' INTER f x)) x else 0))`
   >- RW_TAC std_ss []
   >> RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC std_ss []
   >> Suff `(e' DIFF f e) INTER f x' = e' INTER f x'`
   >- RW_TAC std_ss []
   >> RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_DIFF]
   >> FULL_SIMP_TAC std_ss [IN_DISJOINT, IN_INSERT]
   >> METIS_TAC []);

val PROB_EXTREAL_SUM_IMAGE_SPACE = store_thm
  ("PROB_EXTREAL_SUM_IMAGE_SPACE",
  ``!p. prob_space p /\ FINITE (p_space p) /\ (!x. x IN p_space p ==> {x} IN events p) ==>
       (SIGMA (\x. prob p {x}) (p_space p) = 1)``,
    RW_TAC std_ss []
 >> (MP_TAC o GSYM o Q.SPECL [`p`,`p_space p`]) PROB_EXTREAL_SUM_IMAGE
 >> RW_TAC std_ss [EVENTS_SPACE,PROB_UNIV]);

val PROB_DISCRETE_EVENTS = store_thm
  ("PROB_DISCRETE_EVENTS",
  ``!p. prob_space p /\ FINITE (p_space p) /\ (!x. x IN p_space p ==> {x} IN events p) ==>
        !s. s SUBSET p_space p ==> s IN events p``,
  RW_TAC std_ss []
  >> `s = BIGUNION ({{x} | x IN s})`
      by (RW_TAC std_ss [EXTENSION,IN_BIGUNION,GSPECIFICATION,IN_SING]
          >> METIS_TAC [IN_SING])
  >> POP_ORW
  >> `{{x} | x IN s} SUBSET events p`
        by (RW_TAC std_ss  [SUBSET_DEF,GSPECIFICATION] >> METIS_TAC [SUBSET_DEF])
  >> `FINITE {{x} | x IN s}`
      by (Suff `{{x} | x IN s} = IMAGE (\x. {x}) s` >- METIS_TAC [IMAGE_FINITE,SUBSET_FINITE]
          >> RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_IMAGE])
  >> METIS_TAC [EVENTS_COUNTABLE_UNION,finite_countable]);

val PROB_DISCRETE_EVENTS_COUNTABLE = store_thm
  ("PROB_DISCRETE_EVENTS_COUNTABLE",
  ``!p. prob_space p /\ countable (p_space p) /\ (!x. x IN p_space p ==> {x} IN events p) ==>
        !s. s SUBSET p_space p ==> s IN events p``,
  RW_TAC std_ss []
  >> `s = BIGUNION ({{x} | x IN s})`
      by (RW_TAC std_ss [EXTENSION,IN_BIGUNION,GSPECIFICATION,IN_SING]
          >> METIS_TAC [IN_SING])
  >> POP_ORW
  >> `{{x} | x IN s} SUBSET events p`
      by (RW_TAC std_ss [SUBSET_DEF,GSPECIFICATION] >> METIS_TAC [SUBSET_DEF])
  >> `countable {{x} | x IN s}`
      by (Suff `{{x} | x IN s} = IMAGE (\x. {x}) s`
          >- METIS_TAC [image_countable, COUNTABLE_SUBSET]
          >> RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_IMAGE])
  >> METIS_TAC [EVENTS_COUNTABLE_UNION]);

(* ************************************************************************* *)

Theorem distribution_distr :
    distribution = distr
Proof
    rpt FUN_EQ_TAC >> qx_genl_tac [`p`, `X`, `s`]
 >> RW_TAC std_ss [distribution_def, distr_def, prob_def, p_space_def]
QED

(* ************************************************************************* *)

Theorem marginal_joint_zero :
    !p X Y s t. prob_space p /\ (events p = POW (p_space p)) /\
                ((distribution p X s = 0) \/ (distribution p Y t = 0))
            ==> (joint_distribution p X Y (s CROSS t) = 0)
Proof
    RW_TAC std_ss [joint_distribution_def, distribution_def]
 >- (`PREIMAGE (\x. (X x,Y x)) (s CROSS t) INTER p_space p
        SUBSET (PREIMAGE X s INTER p_space p)`
           by RW_TAC std_ss [SUBSET_DEF, IN_PREIMAGE, IN_INTER, IN_CROSS] \\
     `prob p (PREIMAGE (\x. (X x,Y x)) (s CROSS t) INTER p_space p) <=
      prob p (PREIMAGE X s INTER p_space p)`
           by METIS_TAC [PROB_INCREASING, INTER_SUBSET, IN_POW] \\
     METIS_TAC [PROB_POSITIVE, INTER_SUBSET, IN_POW, le_antisym])
 >> `(PREIMAGE (\x. (X x,Y x)) (s CROSS t) INTER p_space p)
        SUBSET (PREIMAGE Y t INTER p_space p)`
      by RW_TAC std_ss [SUBSET_DEF, IN_PREIMAGE, IN_INTER, IN_CROSS]
 >> `prob p (PREIMAGE (\x. (X x,Y x)) (s CROSS t) INTER p_space p) <=
     prob p (PREIMAGE Y t INTER p_space p)`
       by METIS_TAC [PROB_INCREASING, INTER_SUBSET, IN_POW]
 >> METIS_TAC [PROB_POSITIVE, INTER_SUBSET, IN_POW, le_antisym]
QED

Theorem marginal_joint_zero3 :
    !p X Y Z s t u. prob_space p /\ (events p = POW (p_space p)) /\
                   ((distribution p X s = 0) \/
                    (distribution p Y t = 0) \/
                    (distribution p Z u = 0))
               ==> (joint_distribution3 p X Y Z (s CROSS (t CROSS u)) = 0)
Proof
    RW_TAC std_ss [joint_distribution3_def, distribution_def]
 >| [ (* goal 1 (of 3) *)
     `PREIMAGE (\x. (X x,Y x,Z x)) (s CROSS (t CROSS u)) INTER p_space p
        SUBSET (PREIMAGE X s INTER p_space p)`
           by RW_TAC std_ss [SUBSET_DEF, IN_PREIMAGE, IN_INTER, IN_CROSS] \\
     `prob p (PREIMAGE (\x. (X x,Y x,Z x)) (s CROSS (t CROSS u)) INTER p_space p) <=
      prob p (PREIMAGE X s INTER p_space p)`
           by METIS_TAC [PROB_INCREASING, INTER_SUBSET, IN_POW] \\
      METIS_TAC [PROB_POSITIVE, INTER_SUBSET, IN_POW, le_antisym],
      (* goal 2 (of 3) *)
     `PREIMAGE (\x. (X x,Y x,Z x)) (s CROSS (t CROSS u)) INTER p_space p
        SUBSET (PREIMAGE Y t INTER p_space p)`
           by RW_TAC std_ss [SUBSET_DEF, IN_PREIMAGE, IN_INTER, IN_CROSS] \\
     `prob p (PREIMAGE (\x. (X x,Y x, Z x)) (s CROSS (t CROSS u)) INTER p_space p) <=
      prob p (PREIMAGE Y t INTER p_space p)`
           by METIS_TAC [PROB_INCREASING, INTER_SUBSET, IN_POW] \\
      METIS_TAC [PROB_POSITIVE, INTER_SUBSET, IN_POW, le_antisym],
      (* goal 3 (of 3) *)
     `PREIMAGE (\x. (X x,Y x,Z x)) (s CROSS (t CROSS u)) INTER p_space p
        SUBSET (PREIMAGE Z u INTER p_space p)`
           by RW_TAC std_ss [SUBSET_DEF, IN_PREIMAGE, IN_INTER, IN_CROSS] \\
     `prob p (PREIMAGE (\x. (X x,Y x, Z x)) (s CROSS (t CROSS u)) INTER p_space p) <=
      prob p (PREIMAGE Z u INTER p_space p)`
           by METIS_TAC [PROB_INCREASING, INTER_SUBSET, IN_POW] \\
      METIS_TAC [PROB_POSITIVE, INTER_SUBSET, IN_POW, le_antisym] ]
QED

val distribution_pos = store_thm
  ("distribution_pos",
  ``!p X a. prob_space p /\ (events p = POW (p_space p)) ==>
            0 <= distribution p X a``,
    RW_TAC std_ss [distribution_def]
 >> MATCH_MP_TAC PROB_POSITIVE
 >> RW_TAC std_ss [IN_POW, INTER_SUBSET]);

val distribution_le_1 = store_thm
  ("distribution_le_1",
  ``!p X a. prob_space p /\ (events p = POW (p_space p)) ==>
            distribution p X a <= 1``,
    RW_TAC std_ss [distribution_def]
 >> MATCH_MP_TAC PROB_LE_1
 >> RW_TAC std_ss [IN_POW, INTER_SUBSET]);

(* Theorem 3.1.3 [2, p.36], cf. measure_space_distr *)
val distribution_prob_space = store_thm (* was: prob_space_distr *)
  ("distribution_prob_space",
  ``!p X s. prob_space p /\ random_variable X p s ==>
            prob_space (space s, subsets s, distribution p X)``,
    RW_TAC std_ss [random_variable_def, distribution_def, prob_space_def, measure_def, PSPACE,
                   measure_space_def, m_space_def, measurable_sets_def, IN_MEASURABLE,
                   SPACE, positive_def, PREIMAGE_EMPTY, INTER_EMPTY, PROB_EMPTY,
                   PROB_POSITIVE, space_def, subsets_def, countably_additive_def]
 >- (Q.PAT_X_ASSUM
       `!f. f IN (UNIV -> measurable_sets p) /\
            (!m n. m <> n ==> DISJOINT (f m) (f n)) /\
            BIGUNION (IMAGE f UNIV) IN measurable_sets p ==>
            (measure p (BIGUNION (IMAGE f univ(:num))) = suminf (measure p o f))`
       (MP_TAC o Q.SPEC `(\x. PREIMAGE X x INTER p_space p) o f`) \\
     RW_TAC std_ss [prob_def, o_DEF, PREIMAGE_BIGUNION, IMAGE_IMAGE] \\
    `(BIGUNION (IMAGE (\x. PREIMAGE X (f x)) UNIV) INTER p_space p) =
     (BIGUNION (IMAGE (\x. PREIMAGE X (f x) INTER p_space p) UNIV))`
        by (RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, IN_INTER, IN_IMAGE, IN_UNIV] \\
            METIS_TAC [IN_INTER]) \\
     POP_ORW \\
     POP_ASSUM MATCH_MP_TAC \\
     FULL_SIMP_TAC std_ss [o_DEF, IN_FUNSET, IN_UNIV, events_def] \\
     CONJ_TAC
     >- (rpt STRIP_TAC \\
         Suff `DISJOINT (PREIMAGE X (f i)) (PREIMAGE X (f j))`
         >- (RW_TAC std_ss [IN_DISJOINT, IN_INTER] >> METIS_TAC []) \\
         RW_TAC std_ss [PREIMAGE_DISJOINT]) \\
     Suff `BIGUNION (IMAGE (\x. PREIMAGE X (f x) INTER p_space p) UNIV) =
           PREIMAGE X (BIGUNION (IMAGE f UNIV)) INTER p_space p`
     >- RW_TAC std_ss [] \\
     RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_BIGUNION, IN_IMAGE, IN_UNIV,
                    IN_PREIMAGE, IN_BIGUNION] \\
     METIS_TAC [IN_INTER, IN_PREIMAGE])
 >> Suff `PREIMAGE X (space s) INTER p_space p = p_space p`
 >- RW_TAC std_ss [prob_def, p_space_def]
 >> FULL_SIMP_TAC std_ss [IN_FUNSET, EXTENSION, IN_PREIMAGE, IN_INTER]
 >> METIS_TAC []);

(* `prob_space p` is added since it's not provided by random_variable_def *)
Theorem uniform_distribution_prob_space :
    !X p s. prob_space p /\ FINITE (p_space p) /\
            FINITE (space s) /\ random_variable X p s ==>
            prob_space (space s, subsets s, uniform_distribution s)
Proof
    RW_TAC std_ss []
 >> `p_space p <> {}`
      by METIS_TAC [MEASURE_EMPTY, EVAL ``0 <> 1:extreal``, prob_space_def, p_space_def]
 >> `space s <> {}`
      by (FULL_SIMP_TAC std_ss [random_variable_def, IN_FUNSET,
                                IN_MEASURABLE, space_def] \\
          METIS_TAC [CHOICE_DEF, NOT_IN_EMPTY])
 >> `CARD (space s) <> 0` by METIS_TAC [CARD_EQ_0]
 >> Know `&CARD (space s) <> 0:extreal`
 >- (REWRITE_TAC [extreal_of_num_def] \\
     CCONTR_TAC >> fs [extreal_11]) >> DISCH_TAC
 >> `&CARD (space s) <> PosInf /\ &CARD (space s) <> NegInf`
      by METIS_TAC [extreal_of_num_def, extreal_not_infty]
 >> reverse (RW_TAC std_ss [prob_space_def, measure_def, m_space_def, PSPACE])
 >- RW_TAC std_ss [uniform_distribution_def, div_refl]
 >> MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces
 >> CONJ_TAC >- FULL_SIMP_TAC std_ss [random_variable_def, IN_MEASURABLE]
 >> CONJ_TAC >- RW_TAC std_ss []
 >> CONJ_TAC
 >- (RW_TAC real_ss [positive_def, measure_def, uniform_distribution_def, PREIMAGE_EMPTY,
                     CARD_EMPTY, INTER_EMPTY, measurable_sets_def, zero_div] \\
    `&CARD s' <> PosInf /\ &CARD s' <> NegInf`
       by METIS_TAC [extreal_of_num_def, extreal_not_infty] \\
    `0 <= CARD s' /\ 0 <= CARD (space s)` by RW_TAC std_ss [] \\
    `?a. &CARD s' = Normal a` by PROVE_TAC [extreal_cases] \\
    `?b. &CARD (space s) = Normal b` by PROVE_TAC [extreal_cases] \\
    `b <> 0` by PROVE_TAC [extreal_of_num_def, extreal_11] \\
    `0 <= a /\ 0 <= b` by PROVE_TAC [extreal_of_num_def, extreal_le_eq, REAL_LE] \\
     ASM_SIMP_TAC real_ss [extreal_div_eq, extreal_of_num_def, extreal_le_eq] \\
     RW_TAC real_ss [REAL_LE_MUL, REAL_LE_INV, real_div])
 >> RW_TAC std_ss [additive_def, measure_def, uniform_distribution_def, measurable_sets_def]
 >> FULL_SIMP_TAC std_ss [random_variable_def, IN_MEASURABLE, IN_FUNSET, space_def, subsets_def]
 >> `s' SUBSET space s /\ t SUBSET space s`
      by METIS_TAC [sigma_algebra_def, algebra_def, subset_class_def]
 >> `CARD (s' INTER t) = 0` by METIS_TAC [DISJOINT_DEF, CARD_EMPTY]
 >> `CARD (s' UNION t) = CARD s' + CARD t`  by METIS_TAC [CARD_UNION, ADD_0, SUBSET_FINITE]
 >> RW_TAC std_ss [GSYM REAL_ADD, extreal_of_num_def]
 >> ASM_SIMP_TAC real_ss [extreal_div_eq, extreal_add_def]
QED

val distribution_partition = store_thm
  ("distribution_partition",
  ``!p X. prob_space p /\ (!x. x IN p_space p ==> {x} IN events p) /\
          FINITE (p_space p) /\ random_variable X p Borel ==>
         (SIGMA (\x. distribution p X {x}) (IMAGE X (p_space p)) = 1)``,
    RW_TAC std_ss []
 >> `random_variable X p (IMAGE X (p_space p), POW (IMAGE X (p_space p)))`
      by (RW_TAC std_ss [random_variable_def]
          >> RW_TAC std_ss [IN_MEASURABLE, IN_FUNSET, space_def, subsets_def,
                            IN_IMAGE,POW_SIGMA_ALGEBRA]
          >| [METIS_TAC [IN_MEASURABLE, random_variable_def],
              METIS_TAC [],
              METIS_TAC [PROB_DISCRETE_EVENTS, INTER_SUBSET]])
 >> `prob_space (space (IMAGE X (p_space p), POW (IMAGE X (p_space p))),
                 subsets (IMAGE X (p_space p), POW (IMAGE X (p_space p))),
                 distribution p X)`
     by METIS_TAC [distribution_prob_space]
 >> (MP_TAC o Q.ISPEC `(space (IMAGE (X :'a->extreal) (p_space p), POW (IMAGE X (p_space p))),
                        subsets (IMAGE X (p_space p),POW (IMAGE X (p_space p))),
                        distribution p X)`) PROB_EXTREAL_SUM_IMAGE_SPACE
 >> RW_TAC std_ss []
 >> FULL_SIMP_TAC std_ss [space_def, subsets_def, p_space_def, events_def, m_space_def,
                          measurable_sets_def, prob_def, measure_def]
 >> `FINITE (IMAGE X (m_space p))` by METIS_TAC [IMAGE_FINITE]
 >> `(!x. x IN IMAGE X (m_space p) ==> {x} IN POW (IMAGE X (m_space p)))`
     by RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_IMAGE, IN_SING]
 >> METIS_TAC []);

val distribution_lebesgue_thm1 = store_thm
  ("distribution_lebesgue_thm1",
 ``!X p s A. prob_space p /\ random_variable X p s /\ A IN subsets s ==>
      (distribution p X A = integral p (indicator_fn (PREIMAGE X A INTER p_space p)))``,
   RW_TAC std_ss [random_variable_def, prob_space_def, distribution_def, events_def,
                  IN_MEASURABLE, p_space_def, prob_def, subsets_def, space_def,
                  GSYM integral_indicator]);

val distribution_lebesgue_thm2 = store_thm
  ("distribution_lebesgue_thm2",
  ``!X p s A. prob_space p /\ random_variable X p s /\ A IN subsets s ==>
      (distribution p X A = integral (space s, subsets s, distribution p X) (indicator_fn A))``,
    rpt STRIP_TAC
 >> `prob_space (space s,subsets s,distribution p X)`
     by RW_TAC std_ss [distribution_prob_space]
 >> Q.PAT_X_ASSUM `random_variable X p s` MP_TAC
 >> RW_TAC std_ss [random_variable_def, prob_space_def, distribution_def, events_def,
                   IN_MEASURABLE, p_space_def, prob_def, subsets_def, space_def]
 >> `measure p (PREIMAGE X A INTER m_space p) =
     measure (space s,subsets s,(\A. measure p (PREIMAGE X A INTER m_space p))) A`
     by RW_TAC std_ss [measure_def]
 >> POP_ORW
 >> (MP_TAC o Q.SPECL [`(space s,subsets s,\A. measure p (PREIMAGE X A INTER m_space p))`,`A`]
     o INST_TYPE [``:'a``|->``:'b``]) integral_indicator
 >> FULL_SIMP_TAC std_ss [measurable_sets_def, prob_space_def, distribution_def,
                          prob_def, p_space_def]);

(* ************************************************************************* *)

(* |- !X p.
         real_random_variable X p <=>
         prob_space p /\ X IN measurable (p_space p,events p) Borel /\
         !x. X x <> NegInf /\ X x <> PosInf *)
val real_random_variable = save_thm
  ("real_random_variable",
    REWRITE_RULE [random_variable_def] real_random_variable_def);

(* added `integrable p X`, otherwise `expectation p X` is not defined *)
val finite_expectation1 = store_thm
  ("finite_expectation1",
  ``!p X. prob_space p /\ FINITE (p_space p) /\
          real_random_variable X p /\ integrable p X ==>
         (expectation p X =
          SIGMA (\r. r * prob p (PREIMAGE X {r} INTER p_space p)) (IMAGE X (p_space p)))``,
    RW_TAC std_ss [expectation_def, p_space_def, prob_def, prob_space_def,
                   real_random_variable, events_def]
 >> (MATCH_MP_TAC o REWRITE_RULE [finite_space_integral_def]) finite_space_integral_reduce
 >> RW_TAC std_ss [num_lt_infty]);

(* added `integrable p X`, otherwise `expectation p X` is not defined *)
val finite_expectation2 = store_thm
  ("finite_expectation2",
  ``!p X. prob_space p /\ FINITE (IMAGE X (p_space p)) /\
          real_random_variable X p /\ integrable p X ==>
         (expectation p X =
          SIGMA (\r. r * prob p (PREIMAGE X {r} INTER p_space p)) (IMAGE X (p_space p)))``,
    RW_TAC std_ss [expectation_def, p_space_def, prob_def, prob_space_def,
                   real_random_variable, events_def]
 >> (MATCH_MP_TAC o REWRITE_RULE [finite_space_integral_def]) finite_support_integral_reduce
 >> RW_TAC std_ss [num_lt_infty]);

(* added `integrable p X`, otherwise `expectation p X` is not defined *)
val finite_expectation = store_thm
  ("finite_expectation",
  ``!p X. prob_space p /\ FINITE (p_space p) /\
          real_random_variable X p /\ integrable p X ==>
         (expectation p X = SIGMA (\r. r * distribution p X {r}) (IMAGE X (p_space p)))``,
    RW_TAC std_ss [distribution_def]
 >> METIS_TAC [finite_expectation1]);

(* added `integrable p X`, otherwise `expectation p X` is not defined *)
val finite_support_expectation = store_thm
  ("finite_support_expectation",
  ``!p X. prob_space p /\ FINITE (IMAGE X (p_space p)) /\
          real_random_variable X p /\ integrable p X ==>
         (expectation p X = SIGMA (\r. r * distribution p X {r}) (IMAGE X (p_space p)))``,
    RW_TAC std_ss [distribution_def]
 >> METIS_TAC [finite_expectation2]);

(* ************************************************************************* *)

val finite_marginal_product_space_POW = store_thm
  ("finite_marginal_product_space_POW",
  ``!p X Y. prob_space p /\ FINITE (p_space p) /\ (POW (p_space p) = events p) /\
            random_variable X p (IMAGE X (p_space p), POW (IMAGE X (p_space p))) /\
            random_variable Y p (IMAGE Y (p_space p), POW (IMAGE Y (p_space p)))
        ==> measure_space (((IMAGE X (p_space p)) CROSS (IMAGE Y (p_space p))),
                           POW ((IMAGE X (p_space p)) CROSS (IMAGE Y (p_space p))),
                           (\a. prob p (PREIMAGE (\x. (X x,Y x)) a INTER p_space p)))``,
     rpt STRIP_TAC
 >> `(IMAGE X (p_space p) CROSS IMAGE Y (p_space p),
      POW (IMAGE X (p_space p) CROSS IMAGE Y (p_space p)),
      (\a. prob p (PREIMAGE (\x. (X x,Y x)) a INTER p_space p))) =
     (space (IMAGE X (p_space p) CROSS IMAGE Y (p_space p),
             POW (IMAGE X (p_space p) CROSS IMAGE Y (p_space p))),
      subsets (IMAGE X (p_space p) CROSS IMAGE Y (p_space p),
               POW (IMAGE X (p_space p) CROSS IMAGE Y (p_space p))),
      (\a. prob p (PREIMAGE (\x. (X x,Y x)) a INTER p_space p)))`
        by RW_TAC std_ss [space_def, subsets_def]
 >> POP_ORW
 >> MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces
 >> RW_TAC std_ss [POW_SIGMA_ALGEBRA, space_def, FINITE_CROSS, subsets_def, IMAGE_FINITE]
 >- (RW_TAC std_ss [positive_def, measure_def, measurable_sets_def, PREIMAGE_EMPTY, INTER_EMPTY]
     >- FULL_SIMP_TAC std_ss [random_variable_def, PROB_EMPTY] \\
     METIS_TAC [PROB_POSITIVE, SUBSET_DEF, IN_POW, IN_INTER, random_variable_def])
 >> RW_TAC std_ss [additive_def, measure_def, measurable_sets_def]
 >> MATCH_MP_TAC PROB_ADDITIVE
 >> Q.PAT_X_ASSUM `POW (p_space p) = events p` (MP_TAC o GSYM)
 >> FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_PREIMAGE, IN_CROSS, IN_DISJOINT,
                          random_variable_def, IN_INTER]
 >> RW_TAC std_ss [] >- METIS_TAC [SND]
 >> RW_TAC std_ss [Once EXTENSION, IN_UNION, IN_PREIMAGE, IN_INTER]
 >> METIS_TAC []);

val finite_marginal_product_space_POW2 = store_thm
  ("finite_marginal_product_space_POW2",
  ``!p s1 s2 X Y. prob_space p /\ FINITE (p_space p) /\ (POW (p_space p) = events p) /\
                  random_variable X p (s1, POW s1) /\
                  random_variable Y p (s2, POW s2) /\ FINITE s1 /\ FINITE s2
              ==> measure_space (s1 CROSS s2,POW (s1 CROSS s2),joint_distribution p X Y)``,
 (* proof *)
    rpt STRIP_TAC
 >> `(s1 CROSS s2, POW (s1 CROSS s2), joint_distribution p X Y) =
     (space (s1 CROSS s2, POW (s1 CROSS s2)),
      subsets (s1 CROSS s2, POW (s1 CROSS s2)),
      joint_distribution p X Y)`
        by RW_TAC std_ss [space_def, subsets_def]
 >> POP_ORW
 >> MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces
 >> RW_TAC std_ss [POW_SIGMA_ALGEBRA, space_def, FINITE_CROSS, subsets_def]
 >- (RW_TAC std_ss [positive_def, measure_def, measurable_sets_def, PREIMAGE_EMPTY, INTER_EMPTY,
                    joint_distribution_def]
     >- FULL_SIMP_TAC std_ss [random_variable_def, PROB_EMPTY] \\
     METIS_TAC [PROB_POSITIVE, SUBSET_DEF, IN_POW, IN_INTER, random_variable_def])
 >> RW_TAC std_ss [additive_def, measure_def, measurable_sets_def, joint_distribution_def]
 >> MATCH_MP_TAC PROB_ADDITIVE
 >> Q.PAT_X_ASSUM `POW (p_space p) = events p` (MP_TAC o GSYM)
 >> FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_PREIMAGE, IN_CROSS, IN_DISJOINT,
                          random_variable_def, IN_INTER]
 >> RW_TAC std_ss [] >- METIS_TAC [SND]
 >> RW_TAC std_ss [Once EXTENSION, IN_UNION, IN_PREIMAGE, IN_INTER]
 >> METIS_TAC []);

Theorem finite_marginal_product_space_POW3 :
    !p s1 s2 s3 X Y Z.
       prob_space p /\ FINITE (p_space p) /\ (POW (p_space p) = events p) /\
       random_variable X p (s1, POW s1) /\
       random_variable Y p (s2, POW s2) /\
       random_variable Z p (s3, POW s3) /\
       FINITE s1 /\ FINITE s2 /\ FINITE s3 ==>
       measure_space (s1 CROSS (s2 CROSS s3), POW (s1 CROSS (s2 CROSS s3)),
                      joint_distribution3 p X Y Z)
Proof
    rpt STRIP_TAC
 >> `(s1 CROSS (s2 CROSS s3), POW (s1 CROSS (s2 CROSS s3)), joint_distribution3 p X Y Z) =
     (space (s1 CROSS (s2 CROSS s3), POW (s1 CROSS (s2 CROSS s3))),
      subsets (s1 CROSS (s2 CROSS s3), POW (s1 CROSS (s2 CROSS s3))),
      joint_distribution3 p X Y Z)`
        by RW_TAC std_ss [space_def, subsets_def]
 >> POP_ORW
 >> MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces
 >> RW_TAC std_ss [POW_SIGMA_ALGEBRA, space_def, FINITE_CROSS, subsets_def]
 >- (RW_TAC std_ss [positive_def, measure_def, measurable_sets_def, PREIMAGE_EMPTY,
                    INTER_EMPTY, joint_distribution3_def]
     >- FULL_SIMP_TAC std_ss [random_variable_def, PROB_EMPTY] \\
     METIS_TAC [PROB_POSITIVE, SUBSET_DEF, IN_POW, IN_INTER, random_variable_def])
 >> RW_TAC std_ss [additive_def, measure_def, measurable_sets_def, joint_distribution3_def]
 >> MATCH_MP_TAC PROB_ADDITIVE
 >> Q.PAT_X_ASSUM `POW (p_space p) = events p` (MP_TAC o GSYM)
 >> FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_PREIMAGE, IN_CROSS, IN_DISJOINT,
                          random_variable_def, IN_INTER]
 >> RW_TAC std_ss [] >- METIS_TAC [SND]
 >> RW_TAC std_ss [Once EXTENSION, IN_UNION, IN_PREIMAGE, IN_INTER]
 >> METIS_TAC []
QED

val prob_x_eq_1_imp_prob_y_eq_0 = store_thm
  ("prob_x_eq_1_imp_prob_y_eq_0",
  ``!p x. prob_space p /\ {x} IN events p /\ (prob p {x} = 1) ==>
          !y. {y} IN events p /\ y <> x ==> (prob p {y} = 0)``,
    rpt STRIP_TAC
 >> (MP_TAC o Q.SPECL [`p`, `{y}`, `{x}`]) PROB_ONE_INTER
 >> RW_TAC std_ss []
 >> Know `{y} INTER {x} = {}`
 >- RW_TAC std_ss [Once EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_SING]
 >> METIS_TAC [PROB_EMPTY]);

(* this is the last theorem in HVG's "probability_hvgScript.sml" *)
val distribution_x_eq_1_imp_distribution_y_eq_0 = store_thm
  ("distribution_x_eq_1_imp_distribution_y_eq_0",
  ``!X p x. prob_space p /\
            random_variable X p (IMAGE X (p_space p),POW (IMAGE X (p_space p))) /\
           (distribution p X {x} = 1)
        ==> !y. y <> x ==> (distribution p X {y} = 0)``,
    rpt STRIP_TAC
 >> (MP_TAC o Q.SPECL [`p`, `X`, `(IMAGE X (p_space p),POW (IMAGE X (p_space p)))`])
        distribution_prob_space
 >> RW_TAC std_ss [space_def, subsets_def]
 >> (MP_TAC o Q.ISPECL [`(IMAGE (X :'a -> 'b) (p_space (p :'a p_space)),
                                POW (IMAGE X (p_space p)),distribution p X)`, `x:'b`])
        prob_x_eq_1_imp_prob_y_eq_0
 >> SIMP_TAC std_ss [EVENTS, IN_POW, SUBSET_DEF, IN_SING, PROB]
 >> `x IN IMAGE X (p_space p)`
       by (FULL_SIMP_TAC std_ss [distribution_def, IN_IMAGE] \\
           SPOSE_NOT_THEN STRIP_ASSUME_TAC \\
          `PREIMAGE X {x} INTER p_space p = {}`
             by (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_SING, IN_PREIMAGE, NOT_IN_EMPTY] \\
                 METIS_TAC []) \\
           METIS_TAC [random_variable_def, PROB_EMPTY, ne_01])
 >> POP_ORW
 >> RW_TAC std_ss []
 >> Cases_on `y IN IMAGE X (p_space p)` >- ASM_SIMP_TAC std_ss []
 >> FULL_SIMP_TAC std_ss [distribution_def, IN_IMAGE]
 >> `PREIMAGE X {y} INTER p_space p = {}`
     by (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_SING, IN_PREIMAGE, NOT_IN_EMPTY]
         >> METIS_TAC [])
 >> POP_ORW
 >> MATCH_MP_TAC PROB_EMPTY
 >> FULL_SIMP_TAC std_ss [random_variable_def]);

val joint_distribution_sym = store_thm
  ("joint_distribution_sym",
  ``!p X Y a b. prob_space p ==>
               (joint_distribution p X Y (a CROSS b) = joint_distribution p Y X (b CROSS a))``,
    RW_TAC std_ss [joint_distribution_def]
 >> Suff `PREIMAGE (\x. (X x,Y x)) (a CROSS b) INTER p_space p =
          PREIMAGE (\x. (Y x,X x)) (b CROSS a) INTER p_space p`
 >- METIS_TAC []
 >> RW_TAC std_ss [EXTENSION, IN_INTER, IN_PREIMAGE, IN_CROSS]
 >> METIS_TAC []);

val joint_distribution_pos = store_thm
  ("joint_distribution_pos",
  ``!p X Y a. prob_space p /\ (events p = POW (p_space p)) ==>
              0 <= joint_distribution p X Y a``,
    RW_TAC std_ss [joint_distribution_def]
 >> MATCH_MP_TAC PROB_POSITIVE
 >> RW_TAC std_ss [IN_POW, INTER_SUBSET]);

val joint_distribution_le_1 = store_thm
  ("joint_distribution_le_1",
  ``!p X Y a. prob_space p /\ (events p = POW (p_space p)) ==>
             (joint_distribution p X Y a <= 1)``,
    RW_TAC std_ss [joint_distribution_def]
 >> MATCH_MP_TAC PROB_LE_1
 >> RW_TAC std_ss [IN_POW, INTER_SUBSET]);

Theorem joint_distribution_not_infty :
    !p X Y a. prob_space p /\ (events p = POW (p_space p)) ==>
              joint_distribution p X Y a <> NegInf /\
              joint_distribution p X Y a <> PosInf
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> `0 <= joint_distribution p X Y a` by PROVE_TAC [joint_distribution_pos]
 >> `joint_distribution p X Y a <= 1` by PROVE_TAC [joint_distribution_le_1]
 >> CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf >> art [])
 >> REWRITE_TAC [lt_infty]
 >> MATCH_MP_TAC let_trans >> Q.EXISTS_TAC `1` >> art []
 >> REWRITE_TAC [extreal_of_num_def, lt_infty]
QED

val joint_distribution_le = store_thm
  ("joint_distribution_le",
  ``!p X Y a b. prob_space p /\ (events p = POW (p_space p)) ==>
                joint_distribution p X Y (a CROSS b) <= distribution p X a``,
    RW_TAC std_ss [joint_distribution_def,distribution_def]
 >> MATCH_MP_TAC PROB_INCREASING
 >> RW_TAC std_ss [IN_POW,INTER_SUBSET]
 >> RW_TAC std_ss [SUBSET_DEF,IN_PREIMAGE,IN_CROSS,IN_INTER]);

val joint_distribution_le2 = store_thm
  ("joint_distribution_le2",
  ``!p X Y a b. prob_space p /\ (events p = POW (p_space p)) ==>
                joint_distribution p X Y (a CROSS b) <= distribution p Y b``,
    RW_TAC std_ss [joint_distribution_def,distribution_def]
 >> MATCH_MP_TAC PROB_INCREASING
 >> RW_TAC std_ss [IN_POW, INTER_SUBSET]
 >> RW_TAC std_ss [SUBSET_DEF, IN_PREIMAGE, IN_CROSS,IN_INTER]);

Theorem distribution_not_infty :
    !p X a. prob_space p /\ (events p = POW (p_space p)) ==>
            distribution p X a <> NegInf /\
            distribution p X a <> PosInf
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> `0 <= distribution p X a` by PROVE_TAC [distribution_pos]
 >> `distribution p X a <= 1` by PROVE_TAC [distribution_le_1]
 >> CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf >> art [])
 >> REWRITE_TAC [lt_infty]
 >> MATCH_MP_TAC let_trans >> Q.EXISTS_TAC `1` >> art []
 >> REWRITE_TAC [extreal_of_num_def, lt_infty]
QED

Theorem joint_conditional :
    !p X Y a b. prob_space p /\ (events p = POW (p_space p)) ==>
               (joint_distribution p X Y (a CROSS b) =
                conditional_distribution p Y X b a * distribution p X a)
Proof
    RW_TAC std_ss [conditional_distribution_def, Once joint_distribution_sym]
 >> Cases_on `distribution p X a = 0`
 >- METIS_TAC [le_antisym, joint_distribution_pos, joint_distribution_le,
               joint_distribution_sym, mul_rzero]
 >> `distribution p X a <> NegInf /\ distribution p X a <> PosInf`
      by PROVE_TAC [distribution_not_infty]
 >> `?r. distribution p X a = Normal r` by PROVE_TAC [extreal_cases]
 >> fs []
 >> `r <> 0` by METIS_TAC [extreal_of_num_def, extreal_11]
 >> ASM_SIMP_TAC std_ss [div_mul_refl]
QED

(* add `distribution p Y b <> 0` as divide-by-zero is not
   supported by (new) extreals *)
Theorem conditional_distribution_pos :
    !p X Y a b. prob_space p /\ (events p = POW (p_space p)) /\
                distribution p Y b <> 0 ==>
                0 <= conditional_distribution p X Y a b
Proof
    RW_TAC std_ss [conditional_distribution_def, distribution_pos,
                   joint_distribution_pos]
 >> `0 <= distribution p Y b` by PROVE_TAC [distribution_pos]
 >> `distribution p Y b <> NegInf /\ distribution p Y b <> PosInf`
      by PROVE_TAC [distribution_not_infty]
 >> `?r. distribution p Y b = Normal r` by PROVE_TAC [extreal_cases]
 >> `0 <= joint_distribution p X Y (a CROSS b)`
      by PROVE_TAC [joint_distribution_pos]
 >> `joint_distribution p X Y (a CROSS b) <> NegInf /\
     joint_distribution p X Y (a CROSS b) <> PosInf`
      by PROVE_TAC [joint_distribution_not_infty]
 >> `?c. joint_distribution p X Y (a CROSS b) = Normal c`
      by PROVE_TAC [extreal_cases]
 >> fs []
 >> `r <> 0` by PROVE_TAC [extreal_of_num_def, extreal_11]
 >> `0 <= r /\ 0 <= c` by PROVE_TAC [extreal_of_num_def, extreal_le_eq]
 >> rw [extreal_div_eq, extreal_of_num_def, extreal_le_eq]
 >> RW_TAC real_ss [real_div, REAL_LE_MUL, REAL_LE_INV]
QED

(* add `distribution p Y b <> 0` as divide-by-zero is not
   supported by (new) extreals *)
Theorem conditional_distribution_le_1 :
    !p X Y a b. prob_space p /\ (events p = POW (p_space p)) /\
                distribution p Y b <> 0 ==>
                conditional_distribution p X Y a b <= 1
Proof
    RW_TAC std_ss [conditional_distribution_def]
 >> `joint_distribution p X Y (a CROSS b) <= distribution p Y b`
      by PROVE_TAC [joint_distribution_le2]
 >> `0 <= distribution p Y b` by PROVE_TAC [distribution_pos]
 >> `distribution p Y b <> NegInf /\ distribution p Y b <> PosInf`
      by PROVE_TAC [distribution_not_infty]
 >> `?r. distribution p Y b = Normal r` by PROVE_TAC [extreal_cases]
 >> `0 <= joint_distribution p X Y (a CROSS b)`
      by PROVE_TAC [joint_distribution_pos]
 >> `joint_distribution p X Y (a CROSS b) <> NegInf /\
     joint_distribution p X Y (a CROSS b) <> PosInf`
      by PROVE_TAC [joint_distribution_not_infty]
 >> `?c. joint_distribution p X Y (a CROSS b) = Normal c`
      by PROVE_TAC [extreal_cases]
 >> fs []
 >> `r <> 0` by PROVE_TAC [extreal_of_num_def, extreal_11]
 >> `0 <= r /\ 0 <= c` by PROVE_TAC [extreal_of_num_def, extreal_le_eq]
 >> rw [extreal_div_eq, extreal_of_num_def, extreal_le_eq]
 >> `0 < r` by PROVE_TAC [REAL_LT_LE]
 >> RW_TAC real_ss [REAL_LE_LDIV_EQ]
 >> fs [extreal_le_eq]
QED

Theorem marginal_distribution1 :
    !p X Y a. prob_space p /\ FINITE (p_space p) /\ (events p = POW (p_space p)) ==>
             (distribution p X a =
              SIGMA (\x. joint_distribution p X Y (a CROSS {x})) (IMAGE Y (p_space p)))
Proof
    RW_TAC std_ss [joint_distribution_def, distribution_def]
 >> `FINITE (IMAGE Y (p_space p))` by METIS_TAC [IMAGE_FINITE]
 >> RW_TAC std_ss [PREIMAGE_def, IN_CROSS, IN_SING]
 >> `(prob p ({x | X x IN a} INTER p_space p) =
       SIGMA (\x. prob p ({x | X x IN a} INTER p_space p INTER (\x. {x' | Y x' = x}) x))
                  (IMAGE Y (p_space p)))`
        by (MATCH_MP_TAC  PROB_EXTREAL_SUM_IMAGE_FN
            >> RW_TAC std_ss [IN_POW, INTER_SUBSET]
            >|[RW_TAC std_ss [SUBSET_DEF, IN_INTER, GSPECIFICATION],
               RW_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION, IN_INTER]
               >> METIS_TAC [],
               RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_INTER, GSPECIFICATION]
               >> METIS_TAC [IN_IMAGE]])
 >> RW_TAC std_ss []
 >> irule EXTREAL_SUM_IMAGE_EQ
 >> RW_TAC std_ss []
 >- (Suff `{x | X x IN a} INTER p_space p INTER {x' | Y x' = x} =
           {x' | X x' IN a /\ (Y x' = x)} INTER p_space p`
     >- RW_TAC std_ss [] \\
     RW_TAC std_ss [EXTENSION, IN_INTER, GSPECIFICATION] >> METIS_TAC [])
 >> DISJ1_TAC
 >> RW_TAC std_ss [IN_IMAGE] (* 2 subgoals, same tactics *)
 >> MATCH_MP_TAC pos_not_neginf
 >> MATCH_MP_TAC PROB_POSITIVE >> art [IN_POW]
 >> SET_TAC []
QED

Theorem marginal_distribution2 :
    !p X Y b. prob_space p /\ FINITE (p_space p) /\ (events p = POW (p_space p)) ==>
             (distribution p Y b =
              SIGMA (\x. joint_distribution p X Y ({x} CROSS b)) (IMAGE X (p_space p)))
Proof
    RW_TAC std_ss [joint_distribution_def, distribution_def]
 >> `FINITE (IMAGE X (p_space p))` by METIS_TAC [IMAGE_FINITE]
 >> RW_TAC std_ss [PREIMAGE_def, IN_CROSS, IN_SING]
 >> `prob p ({x | Y x IN b} INTER p_space p) =
      SIGMA (\x. prob p ({x | Y x IN b} INTER p_space p INTER (\x. {x' | X x' = x}) x))
            (IMAGE X (p_space p))`
        by (MATCH_MP_TAC  PROB_EXTREAL_SUM_IMAGE_FN
            >> RW_TAC std_ss [IN_POW, INTER_SUBSET]
            >|[RW_TAC std_ss [SUBSET_DEF, IN_INTER, GSPECIFICATION],
               RW_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION, IN_INTER]
               >> METIS_TAC [],
               RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_INTER, GSPECIFICATION]
               >> METIS_TAC [IN_IMAGE]])
 >> RW_TAC std_ss []
 >> irule EXTREAL_SUM_IMAGE_EQ
 >> RW_TAC std_ss []
 >- (Suff `{x | Y x IN b} INTER p_space p INTER {x' | X x' = x} =
           {x' | (X x' = x) /\ Y x' IN b} INTER p_space p`
     >- RW_TAC std_ss [] \\
     RW_TAC std_ss [EXTENSION, IN_INTER, GSPECIFICATION] >> METIS_TAC [])
 >> DISJ1_TAC
 >> RW_TAC std_ss [IN_IMAGE] (* 2 subgoals, same tactics *)
 >> MATCH_MP_TAC pos_not_neginf
 >> MATCH_MP_TAC PROB_POSITIVE >> art [IN_POW]
 >> SET_TAC []
QED

Theorem joint_distribution_sums_1 :
  !p X Y. prob_space p /\ FINITE (p_space p) /\ (events p = POW (p_space p)) ==>
         (SIGMA (\(x,y). joint_distribution p X Y {(x,y)})
                ((IMAGE X (p_space p)) CROSS (IMAGE Y (p_space p))) = 1)
Proof
    RW_TAC std_ss []
 >> `(\(x,y). joint_distribution p X Y {(x,y)}) =
      (\x. (\a b. joint_distribution p X Y ({a} CROSS {b})) (FST x) (SND x))`
       by (RW_TAC std_ss [FUN_EQ_THM]
           >> Cases_on `x`
           >> RW_TAC std_ss [FST,SND]
           >> METIS_TAC [CROSS_SINGS])
 >> POP_ORW
 >> Know `SIGMA (\x. (\a b. joint_distribution p X Y ({a} CROSS {b})) (FST x) (SND x))
                (IMAGE X (p_space p) CROSS IMAGE Y (p_space p)) =
          SIGMA (\x. SIGMA ((\a b. joint_distribution p X Y ({a} CROSS {b})) x)
                           (IMAGE Y (p_space p))) (IMAGE X (p_space p))`
 >- (MATCH_MP_TAC EQ_SYM \\
     irule EXTREAL_SUM_IMAGE_SUM_IMAGE \\
     RW_TAC std_ss [IMAGE_FINITE] \\
     DISJ1_TAC >> RW_TAC std_ss [IN_IMAGE] \\
     MATCH_MP_TAC pos_not_neginf \\
     rw [joint_distribution_pos]) >> Rewr'
 >> BETA_TAC
 >> rw [GSYM marginal_distribution1]
 >> `random_variable X p (IMAGE X (p_space p), POW (IMAGE X (p_space p)))`
      by (RW_TAC std_ss [random_variable_def, IN_MEASURABLE, IN_FUNSET, POW_SIGMA_ALGEBRA,
                         space_def, subsets_def, IN_POW, INTER_SUBSET, IN_IMAGE]
          >> METIS_TAC [IN_IMAGE])
 >> Q.ABBREV_TAC `p1 = (IMAGE X (p_space p), POW (IMAGE X (p_space p)), distribution p X)`
 >> `prob_space p1` by METIS_TAC [distribution_prob_space, space_def, subsets_def]
 >> (MP_TAC o Q.SPEC `p1` o INST_TYPE [``:'a`` |-> ``:'b``]) PROB_EXTREAL_SUM_IMAGE_SPACE
 >> `FINITE (p_space p1)` by METIS_TAC [PSPACE, IMAGE_FINITE]
 >> `!x. x IN p_space p1 ==> {x} IN events p1`
      by METIS_TAC [EVENTS, IN_POW, SUBSET_DEF, IN_SING, PSPACE]
 >> RW_TAC std_ss []
 >> METIS_TAC [PROB, PSPACE]
QED

(* added `!x. f x <> PosInf /\ f x <> NegInf` into antecedents *)
Theorem joint_distribution_sum_mul1 :
    !p X Y f. prob_space p /\ FINITE (p_space p) /\
              (events p = POW (p_space p)) /\
              (!x. f x <> PosInf /\ f x <> NegInf)  ==>
        (SIGMA (\(x,y). joint_distribution p X Y {(x,y)} * (f x))
               (IMAGE X (p_space p) CROSS IMAGE Y (p_space p)) =
         SIGMA (\x. distribution p X {x} * (f x)) (IMAGE X (p_space p)))
Proof
    RW_TAC std_ss []
 >> Q.ABBREV_TAC `s1 = IMAGE X (p_space p)`
 >> Q.ABBREV_TAC `s2 = IMAGE Y (p_space p)`
 >> `FINITE s1 /\ FINITE s2` by METIS_TAC [IMAGE_FINITE]
 >> `(\(x,y). joint_distribution p X Y {(x,y)} * (f x)) =
     (\x. (\a b. joint_distribution p X Y {(a,b)} * (f a) ) (FST x) (SND x))`
        by (RW_TAC std_ss [FUN_EQ_THM] \\
            Cases_on `x` >> RW_TAC std_ss [])
 >> POP_ORW
 >> (MP_TAC o GSYM o Q.SPECL [`s1`,`s2`,`(\a b. joint_distribution p X Y {(a,b)} * (f a))`] o
     INST_TYPE [``:'a`` |-> ``:'b``, ``:'b`` |-> ``:'c``]) EXTREAL_SUM_IMAGE_SUM_IMAGE
 >> RW_TAC std_ss []
 >> Know `(!x.
             x IN s1 CROSS s2 ==>
             NegInf <> joint_distribution p X Y {x} * f (FST x)) \/
          (!x.
             x IN s1 CROSS s2 ==>
             PosInf <> joint_distribution p X Y {x} * f (FST x))`
 >- (DISJ2_TAC >> RW_TAC std_ss [] \\
     Suff `joint_distribution p X Y {x} * f (FST x) <> PosInf` >- rw [] \\
    `joint_distribution p X Y {x} <> NegInf /\
     joint_distribution p X Y {x} <> PosInf`
       by PROVE_TAC [joint_distribution_not_infty] \\
    `?r. joint_distribution p X Y {x} = Normal r` by PROVE_TAC [extreal_cases] \\
    `?c. f (FST x) = Normal c` by PROVE_TAC [extreal_cases] \\
     fs [extreal_mul_def, extreal_not_infty])
 >> DISCH_TAC
 >> `SIGMA (\x. joint_distribution p X Y {x} * f (FST x)) (s1 CROSS s2) =
     SIGMA (\x. SIGMA (\b. joint_distribution p X Y {(x,b)} * f x) s2) s1`
      by PROVE_TAC [] >> POP_ORW
 >> NTAC 2 (POP_ASSUM K_TAC)
 >> `!x. (\b. joint_distribution p X Y {(x,b)} * (f x)) =
         (\b. (f x) * (\b. joint_distribution p X Y {(x,b)}) b)`
        by RW_TAC std_ss [FUN_EQ_THM, mul_comm] >> POP_ORW
 >> Know `!x. SIGMA (\b. f x * (\b. joint_distribution p X Y {(x,b)}) b) s2 =
              f x * SIGMA (\b. joint_distribution p X Y {(x,b)}) s2`
 >- (GEN_TAC \\
    `?c. f x = Normal c` by PROVE_TAC [extreal_cases] >> POP_ORW \\
     irule EXTREAL_SUM_IMAGE_CMUL >> art [] \\
     DISJ1_TAC >> Q.X_GEN_TAC `y` >> RW_TAC std_ss [] \\
     MATCH_MP_TAC pos_not_neginf \\
     rw [joint_distribution_pos]) >> Rewr'
 >> `!x:'b b:'c. {(x,b)} = {x} CROSS {b}` by METIS_TAC [CROSS_SINGS]
 >> Q.UNABBREV_TAC `s1`
 >> Q.UNABBREV_TAC `s2`
 >> RW_TAC std_ss [GSYM marginal_distribution1]
 >> Suff `(\x. (f x) * distribution p X {x}) = (\x. distribution p X {x} * (f x))`
 >- RW_TAC std_ss []
 >> RW_TAC std_ss [FUN_EQ_THM, mul_comm]
QED

(******************************************************************************)
(*  Moments and variance [2, p.49]                                            *)
(******************************************************************************)

val absolute_moment_def = Define
   `absolute_moment p X a r = expectation p (\x. (abs (X x - a)) pow r)`;

val moment_def = Define
   `moment p X a r = expectation p (\x. (X x - a) pow r)`;

val central_moment_def = Define
   `central_moment p X r = moment p X (expectation p X) r`;

(* `variance` = central second moment, this is the most used one. *)
val variance_def = Define
   `variance p X = central_moment p X 2`;

val standard_deviation_def = Define
   `standard_deviation p X = sqrt (variance p X)`;

val second_moment_def = Define
   `second_moment p X a = moment p X a 2`;

val second_moment_alt = store_thm
  ("second_moment_alt",
  ``!p X. second_moment p X 0 = expectation p (\x. (X x) pow 2)``,
    RW_TAC std_ss [second_moment_def, moment_def, sub_rzero]);

val integrable_imp_finite_expectation = store_thm
  ("integrable_imp_finite_expectation",
  ``!p X. prob_space p /\ integrable p X ==>
          expectation p X <> PosInf /\ expectation p X <> NegInf``,
    rpt GEN_TAC >> SIMP_TAC std_ss [prob_space_def, expectation_def]
 >> STRIP_TAC
 >> MATCH_MP_TAC integrable_finite_integral >> art []);

val integrable_from_square = store_thm
  ("integrable_from_square",
  ``!p X. prob_space p /\ real_random_variable X p /\
          integrable p (\x. X x pow 2) ==> integrable p X``,
    RW_TAC std_ss [prob_space_def, p_space_def]
 >> Know `integrable p (\x. 1)`
 >- (REWRITE_TAC [extreal_of_num_def] \\
     MATCH_MP_TAC integrable_const >> art [extreal_of_num_def, lt_infty])
 >> DISCH_TAC
 >> Know `integrable p (\x. (\x. (X x) pow 2) x + (\x. 1) x)`
 >- (MATCH_MP_TAC integrable_add_pos >> ASM_SIMP_TAC std_ss [le_01, le_pow2])
 >> BETA_TAC >> DISCH_TAC
 >> MATCH_MP_TAC integrable_bounded
 >> Q.EXISTS_TAC `\x. (X x) pow 2 + 1`
 >> ASM_SIMP_TAC std_ss [abs_le_square_plus1]
 >> `(\x. (X x) pow 2) IN measurable (m_space p,measurable_sets p) Borel`
      by PROVE_TAC [integrable_def]
 >> fs [real_random_variable, p_space_def, events_def]);

(* In general, if X has a finite absolute moment of order k, then it has finite absolute
   moments of orders 1,2,...k-1 as well. [6, p.274] *)
val integrable_absolute_moments = store_thm
  ("integrable_absolute_moments",
  ``!p X n. prob_space p /\ real_random_variable X p /\
            integrable p (\x. (abs (X x)) pow n) ==>
            !m. m <= n ==> integrable p (\x. (abs (X x)) pow m)``,
    RW_TAC std_ss [prob_space_def, p_space_def]
 >> Know `integrable p (\x. 1)`
 >- (REWRITE_TAC [extreal_of_num_def] \\
     MATCH_MP_TAC integrable_const >> art [extreal_of_num_def, lt_infty])
 >> DISCH_TAC
 >> Know `integrable p (\x. (\x. 1) x + (\x. (abs (X x)) pow n) x)`
 >- (MATCH_MP_TAC integrable_add_pos >> RW_TAC std_ss [le_01] \\
     MATCH_MP_TAC pow_pos_le >> REWRITE_TAC [abs_pos])
 >> BETA_TAC >> DISCH_TAC
 >> MATCH_MP_TAC integrable_bounded
 >> Q.EXISTS_TAC `\x. 1 + (abs (X x)) pow n`
 >> fs [real_random_variable, p_space_def, events_def]
 >> RW_TAC std_ss []
 >- (`!x. abs (X x) pow m = ((abs o X) x) pow m` by METIS_TAC [o_DEF] >> POP_ORW \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_POW >> fs [measure_space_def, space_def, o_DEF] \\
     CONJ_TAC
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS >> Q.EXISTS_TAC `X` \\
         ASM_SIMP_TAC std_ss []) \\
     PROVE_TAC [abs_not_infty])
 >> Know `abs (abs (X x) pow m) = abs (X x) pow m`
 >- (REWRITE_TAC [abs_refl] \\
     MATCH_MP_TAC pow_pos_le >> REWRITE_TAC [abs_pos]) >> Rewr'
 >> MATCH_MP_TAC abs_pow_le_mono >> art []);

val variance_alt = store_thm
  ("variance_alt",
  ``!p X. variance p X = expectation p (\x. (X x - expectation p X) pow 2)``,
    RW_TAC std_ss [variance_def, central_moment_def, moment_def]);

Theorem variance_pos :
    !p X. prob_space p ==> 0 <= variance p X
Proof
    RW_TAC std_ss [variance_alt, expectation_def, prob_space_def]
 >> MATCH_MP_TAC integral_pos
 >> RW_TAC std_ss [le_pow2]
QED

Theorem second_moment_pos :
    !p X a. prob_space p ==> 0 <= second_moment p X a
Proof
    RW_TAC std_ss [second_moment_def, moment_def, expectation_def, prob_space_def]
 >> MATCH_MP_TAC integral_pos
 >> RW_TAC std_ss [le_pow2]
QED

(* This is the most famous formula in Elementary Probability:

       Var(X) = E[X^2] - E[X]^2

   `integrable p X` is not needed due to "integrable_from_square"
 *)
Theorem variance_eq :
    !p X. prob_space p /\ real_random_variable X p /\ integrable p (\x. X x pow 2) ==>
         (variance p X = expectation p (\x. X x pow 2) - expectation p X pow 2)
Proof
    rpt STRIP_TAC
 >> IMP_RES_TAC integrable_from_square
 >> REWRITE_TAC [variance_def, central_moment_def, moment_def, expectation_def]
 >> Q.ABBREV_TAC `EX = integral p X`
 >> fs [prob_space_def, real_random_variable_def, p_space_def]
 >> `?r. EX = Normal r` by PROVE_TAC [integrable_normal_integral]
 >> Know `!x. (X x - EX) = (X x + (-EX))`
 >- (GEN_TAC >> MATCH_MP_TAC extreal_sub_add >> DISJ1_TAC \\
     PROVE_TAC [extreal_not_infty]) >> DISCH_TAC
 >> Know `!x. (X x - EX) pow 2 = (X x + (-EX)) pow 2`
 >- (GEN_TAC >> POP_ORW >> REWRITE_TAC []) >> Rewr'
 >> Know `!x. (X x + -EX) pow 2 = (X x) pow 2 + (-EX) pow 2 + 2 * (X x) * (-EX)`
 >- (GEN_TAC >> MATCH_MP_TAC add_pow2 >> art [] \\
     REWRITE_TAC [extreal_ainv_def, extreal_not_infty]) >> Rewr'
 >> Know `(-EX) pow 2 = EX pow 2`
 >- (REWRITE_TAC [pow_2, neg_mul2]) >> Rewr'
 >> Know `!x. 2 * X x * -EX = 2 * -EX * X x`
 >- (METIS_TAC [mul_assoc, mul_comm]) >> Rewr'
 >> Know `2 * -EX = Normal (2 * -r)`
 >- (art [extreal_of_num_def, extreal_ainv_def, extreal_mul_def]) >> Rewr'
 >> Know `EX pow 2 <> PosInf`
 >- (art [pow_2, extreal_mul_def, extreal_not_infty]) >> DISCH_TAC
 (* preparing for applying "integral_add" *)
 >> Know `integral p (\x. (\x. (X x) pow 2 + EX pow 2) x + (\x. Normal (2 * -r) * X x) x) =
          integral p (\x. (X x) pow 2 + EX pow 2) + integral p (\x. Normal (2 * -r) * X x)`
 >- (MATCH_MP_TAC integral_add >> simp [] \\
     CONJ_TAC
     >- (Suff `integrable p (\x. (\x. (X x) pow 2) x + (\x. (Normal r) pow 2) x)`
         >- METIS_TAC [] \\
         MATCH_MP_TAC integrable_add_pos >> ASM_SIMP_TAC std_ss [le_pow2] \\
         REWRITE_TAC [pow_2, extreal_mul_def] \\
         MATCH_MP_TAC integrable_const >> art [extreal_of_num_def, lt_infty]) \\
     CONJ_TAC >- (MATCH_MP_TAC integrable_cmul >> art []) \\
     GEN_TAC >> DISCH_TAC >> DISJ1_TAC \\
     RW_TAC std_ss [pow_2, extreal_mul_def] >| (* 2 subgoals *)
     [ `?c. X x = Normal c` by PROVE_TAC [extreal_cases] >> POP_ORW \\
       REWRITE_TAC [extreal_mul_def, extreal_add_def, extreal_not_infty],
       `?c. X x = Normal c` by PROVE_TAC [extreal_cases] >> POP_ORW \\
       REWRITE_TAC [extreal_mul_def, extreal_not_infty] ])
 >> BETA_TAC >> Rewr'
 >> Know `integral p (\x. (\x. (X x) pow 2) x + (\x. EX pow 2) x) =
          integral p (\x. (X x) pow 2) + integral p (\x. EX pow 2)`
 >- (MATCH_MP_TAC integral_add >> simp [pow_2, extreal_mul_def, extreal_not_infty] \\
     CONJ_TAC >- (MATCH_MP_TAC integrable_const >> art [extreal_of_num_def, lt_infty]) \\
     GEN_TAC >> DISCH_TAC >> DISJ1_TAC \\
    `?c. X x = Normal c` by PROVE_TAC [extreal_cases] >> POP_ORW \\
     REWRITE_TAC [extreal_mul_def, extreal_not_infty])
 >> BETA_TAC >> Rewr'
 >> Know `integral p (\x. EX pow 2) = EX pow 2 * measure p (m_space p)`
 >- (Q.PAT_X_ASSUM `EX = Normal r` (REWRITE_TAC o wrap) \\
     REWRITE_TAC [pow_2, extreal_mul_def] \\
     MATCH_MP_TAC integral_const >> art [extreal_of_num_def, lt_infty])
 >> Rewr'
 >> Know `integral p (\x. Normal (2 * -r) * X x) = Normal (2 * -r) * EX`
 >- (Q.PAT_X_ASSUM `EX = Normal r` K_TAC >> Q.UNABBREV_TAC `EX` \\
     MATCH_MP_TAC integral_cmul >> art []) >> Rewr'
 >> Know `Normal (2 * -r) = -2 * EX`
 >- (art [extreal_of_num_def, extreal_mul_def, extreal_ainv_def, extreal_11] \\
     RW_TAC real_ss []) >> Rewr'
 >> Q.PAT_X_ASSUM `EX = Normal r` K_TAC >> art [mul_rone, GSYM pow_2, GSYM mul_assoc]
 >> Know `integral p (\x. (X x) pow 2) + EX pow 2 + -2 * EX pow 2 =
          integral p (\x. (X x) pow 2) + (EX pow 2 + -2 * EX pow 2)`
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC add_assoc \\
    `?r. integral p (\x. (X x) pow 2) = Normal r` by PROVE_TAC [integrable_normal_integral] \\
    `?c. EX = Normal c` by PROVE_TAC [integrable_normal_integral] \\
     art [extreal_not_infty, pow_2, extreal_of_num_def, extreal_ainv_def, extreal_mul_def])
 >> Rewr'
 >> Know `1 * EX pow 2 + -2 * EX pow 2 = (1 + -2) * EX pow 2`
 >- (MATCH_MP_TAC EQ_SYM \\
     `?c. EX = Normal c` by PROVE_TAC [integrable_normal_integral] \\
     art [pow_2, extreal_mul_def] \\
     MATCH_MP_TAC add_rdistrib_normal \\
     REWRITE_TAC [extreal_of_num_def, extreal_ainv_def, extreal_not_infty])
 >> REWRITE_TAC [mul_lone] >> Rewr'
 >> Know `(1:extreal) + -2 = -1`
 >- (RW_TAC real_ss [extreal_of_num_def, extreal_ainv_def, extreal_11, extreal_add_def])
 >> Rewr' >> REWRITE_TAC [GSYM neg_minus1]
 >> MATCH_MP_TAC EQ_SYM
 >> MATCH_MP_TAC extreal_sub_add
 >> DISJ1_TAC >> art []
 >> `?r. integral p (\x. (X x) pow 2) = Normal r` by PROVE_TAC [integrable_normal_integral]
 >> POP_ORW >> REWRITE_TAC [extreal_not_infty]
QED

(* A corollary: Var(X) is always less or equal than E[X^2] *)
val variance_le = store_thm
  ("variance_le",
  ``!p X. prob_space p /\ real_random_variable X p /\ integrable p (\x. X x pow 2) ==>
          variance p X <= expectation p (\x. X x pow 2)``,
    rpt STRIP_TAC
 >> Know `variance p X = expectation p (\x. X x pow 2) - expectation p X pow 2`
 >- (MATCH_MP_TAC variance_eq >> art []) >> Rewr'
 >> IMP_RES_TAC integrable_from_square
 >> Q.ABBREV_TAC `EX = integral p X`
 >> fs [prob_space_def, real_random_variable_def, p_space_def, expectation_def]
 >> `?r. EX = Normal r` by PROVE_TAC [integrable_normal_integral]
 >> Know `EX pow 2 <> PosInf`
 >- (art [pow_2, extreal_mul_def, extreal_not_infty]) >> DISCH_TAC
 >> Know `EX pow 2 <> NegInf`
 >- (MATCH_MP_TAC pos_not_neginf >> REWRITE_TAC [le_pow2]) >> DISCH_TAC
 >> Know `integral p (\x. (X x) pow 2) - EX pow 2 <= integral p (\x. (X x) pow 2) <=>
          integral p (\x. (X x) pow 2) <= integral p (\x. (X x) pow 2) + EX pow 2`
 >- (MATCH_MP_TAC sub_le_eq >> art []) >> Rewr'
 >> MATCH_MP_TAC le_addr_imp
 >> REWRITE_TAC [le_pow2]);

(* NOTE: this definition is new, later we shall prove that it's equivalence with
         finite variance or finite second moment at `a = 0` *)
val finite_second_moments_def = Define
   `finite_second_moments p X = ?a. second_moment p X a < PosInf`;

val finite_variance_imp_finite_second_moments = Q.prove (
   `!p X. variance p X < PosInf ==> finite_second_moments p X`,
    RW_TAC std_ss [finite_second_moments_def, variance_def, central_moment_def,
                   second_moment_def]
 >> Q.EXISTS_TAC `expectation p X` >> art []);

val expectation_const = store_thm
  ("expectation_const",
  ``!p c. prob_space p ==> (expectation p (\x. Normal c) = Normal c)``,
    rpt GEN_TAC
 >> MP_TAC (Q.SPECL [`p`, `c`] integral_const)
 >> `1 < PosInf` by PROVE_TAC [lt_infty, extreal_of_num_def]
 >> RW_TAC std_ss [prob_space_def, p_space_def, expectation_def, mul_rone]);

val expectation_posinf = store_thm
  ("expectation_posinf",
  ``!p. prob_space p ==> (expectation p (\x. PosInf) = PosInf)``,
    RW_TAC std_ss [prob_space_def, p_space_def, expectation_def]
 >> MATCH_MP_TAC integral_posinf >> art [lt_01]);

(* a deep lemma: all second moments are finite iff one of them is finite *)
Theorem finite_second_moments_all :
    !p X. prob_space p /\ real_random_variable X p ==>
         (finite_second_moments p X <=> !r. second_moment p X (Normal r) < PosInf)
Proof
    RW_TAC std_ss [finite_second_moments_def, second_moment_def, moment_def]
 >> reverse EQ_TAC >> rpt STRIP_TAC
 >- (POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPEC `0`)) \\
     Q.EXISTS_TAC `Normal 0` >> art [])
 >> fs [real_random_variable]
 >> Cases_on `(a = PosInf) \/ (a = NegInf)`
 >- (Suff `!x. (X x - a) pow 2 = PosInf`
     >- (DISCH_THEN (fs o wrap) >> METIS_TAC [expectation_posinf, lt_infty]) \\
     GEN_TAC \\
    `?r. X x = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
    `EVEN 2` by RW_TAC arith_ss [] \\
     Q.PAT_X_ASSUM `(a = PosInf) \/ (a = NegInf)` STRIP_ASSUME_TAC \\
     ASM_SIMP_TAC std_ss [extreal_sub_def, extreal_pow_def])
 >> `?c. a = Normal c` by PROVE_TAC [extreal_cases]
 >> POP_ASSUM (fs o wrap)
 >> fs [expectation_def, p_space_def, events_def, prob_space_def]
 >> Know `integrable p (\x. (\x. X x - Normal c) x pow 2)`
 >- (RW_TAC pure_ss [integrable_def] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       MATCH_MP_TAC IN_MEASURABLE_BOREL_POW >> fs [measure_space_def, space_def] \\
       reverse CONJ_TAC
       >- (GEN_TAC >> DISCH_TAC \\
           `?r. X x = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
           REWRITE_TAC [extreal_sub_def, extreal_not_infty]) \\
       MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
       qexistsl_tac [`X`, `\x. Normal c`] \\
       ASM_SIMP_TAC std_ss [extreal_not_infty] \\
       MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST >> Q.EXISTS_TAC `Normal c` \\
       ASM_SIMP_TAC std_ss [],
       (* goal 2 (of 3) *)
       BETA_TAC \\
      `!x. 0 <= (X x - Normal c) pow 2` by REWRITE_TAC [le_pow2] \\
       Know `fn_plus (\x. (X x - Normal c) pow 2) = (\x. (X x - Normal c) pow 2)`
       >- (MATCH_MP_TAC FN_PLUS_POS_ID >> BETA_TAC >> art []) >> Rewr' \\
       REWRITE_TAC [lt_infty] \\
       Know `pos_fn_integral p (\x. (X x - Normal c) pow 2) =
                    integral p (\x. (X x - Normal c) pow 2)`
       >- (MATCH_MP_TAC EQ_SYM \\
           MATCH_MP_TAC integral_pos_fn >> ASM_SIMP_TAC std_ss []) >> Rewr' >> art [],
       (* goal 3 (of 3) *)
       BETA_TAC \\
      `!x. 0 <= (X x - Normal c) pow 2` by REWRITE_TAC [le_pow2] \\
       Know `fn_minus (\x. (X x - Normal c) pow 2) = (\x. 0)`
       >- (MATCH_MP_TAC FN_MINUS_POS_ZERO >> BETA_TAC >> art []) >> Rewr' \\
       ASM_SIMP_TAC std_ss [pos_fn_integral_zero, extreal_of_num_def, extreal_not_infty] ])
 >> DISCH_TAC
 >> Know `integrable p (\x. X x - Normal c)`
 >- (MATCH_MP_TAC integrable_from_square \\
     fs [prob_space_def, real_random_variable,
         p_space_def, events_def, prob_space_def, measure_space_def] \\
     reverse CONJ_TAC
     >- (GEN_TAC \\
         `?r. X x = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
         REWRITE_TAC [extreal_sub_def, extreal_not_infty]) \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
     Q.EXISTS_TAC `X` >> Q.EXISTS_TAC `\x. Normal c` \\
     ASM_SIMP_TAC std_ss [extreal_not_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST >> Q.EXISTS_TAC `Normal c` \\
     ASM_SIMP_TAC std_ss [])
 >> DISCH_TAC
 >> Know `integrable p X`
 >- (Know `X = \x. X x - Normal c + Normal c`
     >- (FUN_EQ_TAC >> GEN_TAC >> BETA_TAC \\
         MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC sub_add >> REWRITE_TAC [extreal_not_infty]) >> Rewr' \\
    `(\x. X x - Normal c + Normal c) = (\x. (\x. X x - Normal c) x + (\x. Normal c) x)`
       by METIS_TAC [] >> POP_ORW \\
     MATCH_MP_TAC integrable_add >> art [] \\
     CONJ_TAC >- (MATCH_MP_TAC integrable_const >> art [extreal_of_num_def, lt_infty]) \\
     GEN_TAC >> DISCH_TAC >> DISJ1_TAC \\
     RW_TAC std_ss [extreal_not_infty] \\
    `?r. X x = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
     REWRITE_TAC [extreal_sub_def, extreal_not_infty])
 >> DISCH_TAC
 >> Suff `integrable p (\x. (X x - Normal r) pow 2)`
 >- METIS_TAC [integrable_finite_integral, lt_infty]
 >> Know `!x. (X x - Normal r) pow 2 =
              (\x. (X x - Normal c) pow 2) x +
              (\x. Normal (2 * (c - r)) * (X x) + Normal (r pow 2 - c pow 2)) x`
 >- (GEN_TAC >> BETA_TAC \\
    `?y. X x = Normal y` by PROVE_TAC [extreal_cases] >> POP_ORW \\
     SIMP_TAC real_ss [sub_pow2, extreal_not_infty, pow_2] \\
     SIMP_TAC real_ss [extreal_mul_def, extreal_add_def, extreal_sub_def, extreal_11,
                       extreal_of_num_def] \\
     RW_TAC real_ss [REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB, REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB,
                     REAL_ADD_ASSOC, POW_2, GSYM REAL_DOUBLE] \\
     REAL_ARITH_TAC) >> Rewr'
 >> MATCH_MP_TAC integrable_add >> fs []
 >> reverse CONJ_TAC
 >- (GEN_TAC >> DISCH_TAC >> DISJ1_TAC \\
     RW_TAC std_ss [pow_2] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
      `?y. X x = Normal y` by PROVE_TAC [extreal_cases] >> POP_ORW \\
       REWRITE_TAC [extreal_sub_def, extreal_mul_def, extreal_not_infty],
       (* goal 2 (of 2) *)
      `?y. X x = Normal y` by PROVE_TAC [extreal_cases] >> POP_ORW \\
       REWRITE_TAC [extreal_add_def, extreal_mul_def, extreal_not_infty] ])
 >> `(\x. Normal (2 * (c - r)) * X x + Normal (r pow 2 - c pow 2)) =
     (\x. (\x. Normal (2 * (c - r)) * X x) x + (\x. Normal (r pow 2 - c pow 2)) x)`
      by METIS_TAC [] >> POP_ORW
 >> MATCH_MP_TAC integrable_add >> RW_TAC std_ss [] (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      MATCH_MP_TAC integrable_cmul >> art [],
      (* goal 2 (of 3) *)
      MATCH_MP_TAC integrable_const >> art [extreal_of_num_def, lt_infty],
      (* goal 3 (of 3) *)
      DISJ1_TAC \\
     `?y. X x = Normal y` by PROVE_TAC [extreal_cases] >> POP_ORW \\
      REWRITE_TAC [extreal_mul_def, extreal_not_infty] ]
QED

val finite_second_moments_eq_finite_variance = store_thm
  ("finite_second_moments_eq_finite_variance",
  ``!p X. prob_space p /\ real_random_variable X p ==>
         (finite_second_moments p X <=> variance p X < PosInf)``,
    rpt STRIP_TAC
 >> reverse EQ_TAC >> DISCH_TAC
 >- (MATCH_MP_TAC finite_variance_imp_finite_second_moments >> art [])
 >> fs [variance_def, central_moment_def, second_moment_def]
 >> `!r. second_moment p X (Normal r) < PosInf` by PROVE_TAC [finite_second_moments_all]
 >> fs [second_moment_def, moment_def]
 >> Q.PAT_ASSUM `!r. expectation p _ < PosInf` (MP_TAC o (Q.SPEC `0`))
 >> REWRITE_TAC [GSYM extreal_of_num_def, sub_rzero]
 >> DISCH_TAC
 >> Know `integrable p (\x. (X x) pow 2)`
 >- (RW_TAC std_ss [integrable_def] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       MATCH_MP_TAC IN_MEASURABLE_BOREL_POW \\
       fs [prob_space_def, measure_space_def, real_random_variable_def,
           random_variable_def, space_def, p_space_def, events_def],
       (* goal 2 (of 3) *)
       Know `fn_plus (\x. (X x) pow 2) = (\x. (X x) pow 2)`
       >- (MATCH_MP_TAC FN_PLUS_POS_ID >> RW_TAC std_ss [le_pow2]) >> Rewr' \\
       Know `pos_fn_integral p (\x. (X x) pow 2) = integral p (\x. (X x) pow 2)`
       >- (MATCH_MP_TAC EQ_SYM \\
           MATCH_MP_TAC integral_pos_fn >> fs [prob_space_def, le_pow2]) \\
       Rewr' >> fs [expectation_def, lt_infty],
       (* goal 3 (of 3) *)
       Know `fn_minus (\x. (X x) pow 2) = (\x. 0)`
       >- (MATCH_MP_TAC FN_MINUS_POS_ZERO >> RW_TAC std_ss [le_pow2]) >> Rewr' \\
       Know `pos_fn_integral p (\x. 0) = 0`
       >- (MATCH_MP_TAC pos_fn_integral_zero >> fs [prob_space_def]) >> Rewr' \\
       REWRITE_TAC [extreal_of_num_def, extreal_not_infty] ])
 >> DISCH_TAC
 >> Know `integrable p X`
 >- (MATCH_MP_TAC integrable_from_square >> art []) >> DISCH_TAC
 >> `expectation p X <> PosInf /\ expectation p X <> NegInf`
     by METIS_TAC [integrable_imp_finite_expectation]
 >> `?c. expectation p X = Normal c` by PROVE_TAC [extreal_cases] >> art []);

val lemma = Q.prove (
   `!p X. prob_space p /\ real_random_variable X p ==>
         (variance p X < PosInf <=> second_moment p X 0 < PosInf)`,
    rpt STRIP_TAC
 >> Know `variance p X < PosInf <=> finite_second_moments p X`
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC finite_second_moments_eq_finite_variance >> art []) >> Rewr'
 >> EQ_TAC >> STRIP_TAC
 >- (Know `finite_second_moments p X <=> !r. second_moment p X (Normal r) < PosInf`
     >- (MATCH_MP_TAC finite_second_moments_all >> art []) \\
     DISCH_THEN (fs o wrap) \\
     POP_ASSUM (REWRITE_TAC o wrap o (REWRITE_RULE [GSYM extreal_of_num_def]) o (Q.SPEC `0`)))
 >> REWRITE_TAC [finite_second_moments_def]
 >> Q.EXISTS_TAC `0` >> art []);

(* alternative definition of `finite_second_moments` for easier verification *)
val finite_second_moments_alt = store_thm
  ("finite_second_moments_alt",
  ``!p X. prob_space p /\ real_random_variable X p ==>
         (finite_second_moments p X <=> second_moment p X 0 < PosInf)``,
    rpt STRIP_TAC
 >> METIS_TAC [finite_second_moments_eq_finite_variance, lemma]);

(* |- !p X.
         prob_space p /\ real_random_variable X p ==>
         (finite_second_moments p X <=> expectation p (\x. (X x) pow 2) < PosInf)
 *)
Theorem finite_second_moments_literally =
    REWRITE_RULE [second_moment_def, moment_def, sub_rzero]
                 finite_second_moments_alt;

val finite_second_moments_eq_integrable_square = store_thm
  ("finite_second_moments_eq_integrable_square",
  ``!p X. prob_space p /\ real_random_variable X p ==>
         (finite_second_moments p X <=> integrable p (\x. X x pow 2))``,
    rpt STRIP_TAC
 >> EQ_TAC >> STRIP_TAC
 >| [ (* goal 1 (of 2) *)
      RW_TAC std_ss [integrable_def] >| (* 3 subgoals *)
      [ (* goal 1.1 (of 3) *)
        MATCH_MP_TAC IN_MEASURABLE_BOREL_POW \\
        fs [prob_space_def, measure_space_def, real_random_variable_def,
            random_variable_def, space_def, p_space_def, events_def],
        (* goal 1.2 (of 3) *)
        Know `fn_plus (\x. (X x) pow 2) = (\x. (X x) pow 2)`
        >- (MATCH_MP_TAC FN_PLUS_POS_ID >> RW_TAC std_ss [le_pow2]) >> Rewr' \\
        Know `pos_fn_integral p (\x. (X x) pow 2) = integral p (\x. (X x) pow 2)`
        >- (MATCH_MP_TAC EQ_SYM \\
            MATCH_MP_TAC integral_pos_fn >> fs [prob_space_def, le_pow2]) \\
        Rewr' >> REWRITE_TAC [lt_infty] \\
        Know `finite_second_moments p X <=> second_moment p X 0 < PosInf`
        >- (MATCH_MP_TAC finite_second_moments_alt >> art []) \\
        REWRITE_TAC [second_moment_def, moment_def, sub_rzero, expectation_def] \\
        DISCH_THEN (fs o wrap),
        (* goal 1.3 (of 3) *)
        Know `fn_minus (\x. (X x) pow 2) = (\x. 0)`
        >- (MATCH_MP_TAC FN_MINUS_POS_ZERO >> RW_TAC std_ss [le_pow2]) >> Rewr' \\
        Know `pos_fn_integral p (\x. 0) = 0`
        >- (MATCH_MP_TAC pos_fn_integral_zero >> fs [prob_space_def]) >> Rewr' \\
        REWRITE_TAC [extreal_of_num_def, extreal_not_infty] ],
      (* goal 2 (of 2) *)
      IMP_RES_TAC integrable_imp_finite_expectation \\
      Know `finite_second_moments p X <=> second_moment p X 0 < PosInf`
      >- (MATCH_MP_TAC finite_second_moments_alt >> art []) \\
      REWRITE_TAC [second_moment_def, moment_def, sub_rzero] \\
      Rewr' >> art [GSYM lt_infty] ]);

(* a more general version *)
val finite_second_moments_eq_integrable_squares = store_thm
  ("finite_second_moments_eq_integrable_squares",
  ``!p X. prob_space p /\ real_random_variable X p ==>
         (finite_second_moments p X <=> !c. integrable p (\x. (X x - Normal c) pow 2))``,
    rpt STRIP_TAC
 >> EQ_TAC >> STRIP_TAC
 >| [ (* goal 1 (of 2) *)
      RW_TAC std_ss [integrable_def] >| (* 3 subgoals *)
      [ (* goal 1.1 (of 3) *)
        `!x. (X x - Normal c) pow 2 = ((\x. X x - Normal c) x) pow 2` by METIS_TAC [] \\
         POP_ORW >> MATCH_MP_TAC IN_MEASURABLE_BOREL_POW \\
         fs [prob_space_def, measure_space_def, real_random_variable_def,
             random_variable_def, space_def, p_space_def, events_def] \\
         reverse CONJ_TAC
         >- (GEN_TAC >> DISCH_TAC \\
            `?r. X x = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
             REWRITE_TAC [extreal_sub_def, extreal_not_infty]) \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
         qexistsl_tac [`X`, `\x. Normal c`] >> RW_TAC std_ss [] \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST >> Q.EXISTS_TAC `Normal c` \\
         RW_TAC std_ss [space_def],
         (* goal 1.2 (of 3) *)
         Know `fn_plus (\x. (X x - Normal c) pow 2) = (\x. (X x - Normal c) pow 2)`
         >- (MATCH_MP_TAC FN_PLUS_POS_ID >> RW_TAC std_ss [le_pow2]) >> Rewr' \\
         Know `pos_fn_integral p (\x. (X x - Normal c) pow 2) =
                      integral p (\x. (X x - Normal c) pow 2)`
         >- (MATCH_MP_TAC EQ_SYM \\
             MATCH_MP_TAC integral_pos_fn >> fs [prob_space_def, le_pow2]) \\
         Rewr' >> REWRITE_TAC [lt_infty] \\
         IMP_RES_TAC finite_second_moments_all \\
         fs [second_moment_def, moment_def, expectation_def],
         (* goal 1.3 (of 3) *)
         Know `fn_minus (\x. (X x - Normal c) pow 2) = (\x. 0)`
         >- (MATCH_MP_TAC FN_MINUS_POS_ZERO >> RW_TAC std_ss [le_pow2]) >> Rewr' \\
         Know `pos_fn_integral p (\x. 0) = 0`
         >- (MATCH_MP_TAC pos_fn_integral_zero >> fs [prob_space_def]) >> Rewr' \\
         REWRITE_TAC [extreal_of_num_def, extreal_not_infty] ],
      (* goal 2 (of 2) *)
      Know `finite_second_moments p X <=> second_moment p X (Normal c) < PosInf`
      >- (EQ_TAC >> DISCH_TAC >| (* 2 subgoals *)
          [ (* goal 2.1 (of 2) *)
            IMP_RES_TAC finite_second_moments_all >> art [],
            (* goal 2.2 (of 2) *)
            REWRITE_TAC [finite_second_moments_def] \\
            Q.EXISTS_TAC `Normal c` >> art [] ]) >> Rewr' \\
      REWRITE_TAC [GSYM lt_infty, second_moment_def, moment_def] \\
      METIS_TAC [integrable_imp_finite_expectation] ]);

val finite_second_moments_imp_integrable = store_thm
  ("finite_second_moments_imp_integrable",
  ``!p X. prob_space p /\ real_random_variable X p /\ finite_second_moments p X ==>
          integrable p X``,
    rpt GEN_TAC >> STRIP_TAC
 >> MATCH_MP_TAC integrable_from_square >> art []
 >> IMP_RES_TAC finite_second_moments_eq_integrable_square);

val finite_second_moments_imp_finite_expectation = store_thm
  ("finite_second_moments_imp_finite_expectation",
  ``!p X. prob_space p /\ real_random_variable X p /\ finite_second_moments p X ==>
          expectation p X <> PosInf /\ expectation p X <> NegInf``,
    rpt GEN_TAC >> STRIP_TAC
 >> MATCH_MP_TAC integrable_imp_finite_expectation >> art []
 >> MATCH_MP_TAC finite_second_moments_imp_integrable >> art []);

Theorem expectation_real_affine :
    !p X c. prob_space p /\ real_random_variable X p /\ integrable p X /\
            c <> PosInf /\ c <> NegInf ==>
           (expectation p (\x. X x + c) = expectation p X + c)
Proof
    RW_TAC std_ss [real_random_variable_def, prob_space_def, p_space_def,
                   events_def, expectation_def]
 >> `?r. c = Normal r` by METIS_TAC [extreal_cases] >> POP_ORW
 >> Know `integral p (\x. X x + (\x. Normal r) x) =
          integral p X + integral p (\x. Normal r)`
 >- (MATCH_MP_TAC integral_add >> rw [integral_const] \\
     MATCH_MP_TAC integrable_const >> rw [lt_infty])
 >> BETA_TAC >> Rewr'
 >> rw [integral_const, extreal_add_def, extreal_sub_def]
QED

Theorem expectation_normal :
    !p X. prob_space p /\ integrable p X ==> ?r. expectation p X = Normal r
Proof
    fs [prob_space_def, expectation_def, integrable_normal_integral]
QED

Theorem expectation_finite :
    !p X. prob_space p /\ integrable p X ==>
          expectation p X <> PosInf /\ expectation p X <> NegInf
Proof
    METIS_TAC [expectation_normal, extreal_not_infty]
QED

Theorem variance_real_affine :
    !p X c. prob_space p /\ real_random_variable X p /\ integrable p X /\
            c <> PosInf /\ c <> NegInf ==> (variance p (\x. X x + c) = variance p X)
Proof
    RW_TAC std_ss [variance_alt]
 >> Suff `!x. X x + c - expectation p (\x. X x + c) = X x - expectation p X`
 >- rw []
 >> GEN_TAC
 >> ASM_SIMP_TAC std_ss [expectation_real_affine]
 >> `?r. c = Normal r` by METIS_TAC [extreal_cases] >> POP_ORW
 >> `?e. expectation p X = Normal e` by METIS_TAC [expectation_normal]
 >> fs [real_random_variable_def]
 >> `?z. X x = Normal z` by METIS_TAC [extreal_cases]
 >> rw [extreal_add_def, extreal_sub_def]
 >> REAL_ARITH_TAC
QED

Theorem variance_real_affine' :
    !p X c. prob_space p /\ real_random_variable X p /\ integrable p X /\
            c <> PosInf /\ c <> NegInf ==> (variance p (\x. X x - c) = variance p X)
Proof
    rpt STRIP_TAC
 >> Know `!x. X x - c = X x + -c`
 >- (GEN_TAC >> MATCH_MP_TAC extreal_sub_add \\
     fs [real_random_variable_def]) >> Rewr'
 >> MATCH_MP_TAC variance_real_affine >> art []
 >> `?r. c = Normal r` by METIS_TAC [extreal_cases]
 >> rw [extreal_ainv_def, extreal_not_infty]
QED

(* Markov's inequality for Probability (general version) *)
Theorem prob_markov_inequality :
    !p X a c. prob_space p /\ integrable p X /\ 0 < c /\ a IN events p ==>
              prob p ({x | c <= abs (X x)} INTER a) <=
                inv c * (expectation p (\x. abs (X x) * indicator_fn a x))
Proof
    RW_TAC std_ss [prob_space_def, prob_def, events_def, expectation_def]
 >> MATCH_MP_TAC markov_inequality >> art []
QED

(* The special version with `a = p_space p`, c.f. PROB_GSPEC for moving `a` outside *)
Theorem prob_markov_ineq :
    !p X c. prob_space p /\ integrable p X /\ 0 < c ==>
            prob p ({x | c <= abs (X x)} INTER p_space p) <= inv c * expectation p (abs o X)
Proof
    RW_TAC std_ss [prob_space_def, p_space_def, prob_def, events_def, expectation_def]
 >> MATCH_MP_TAC markov_ineq >> art []
QED

(* Chebyshev's inequality (general version) *)
Theorem chebyshev_inequality :
    !p X a t c. prob_space p /\ real_random_variable X p /\
                finite_second_moments p X /\ 0 < t /\ a IN events p ==>
       prob p ({x | t <= abs (X x - Normal c)} INTER a) <=
         inv (t pow 2) * (expectation p (\x. (X x - Normal c) pow 2 * indicator_fn a x))
Proof
    rpt STRIP_TAC
 >> Know `!x. t <= abs (X x - Normal c) <=> t pow 2 <= (X x - Normal c) pow 2`
 >- (GEN_TAC \\
     Know `0 <= t /\ 0 <= abs (X x - Normal c)` >- PROVE_TAC [lt_imp_le, abs_pos] \\
     DISCH_THEN (REWRITE_TAC o wrap o (MATCH_MP pow2_le_eq)) \\
     REWRITE_TAC [abs_pow2]) >> Rewr'
 >> Q.ABBREV_TAC `Y = \x. (X x - Normal c) pow 2`
 >> Know `!x. (X x - Normal c) pow 2 = abs (Y x)`
 >- (GEN_TAC >> Q.UNABBREV_TAC `Y` >> BETA_TAC \\
    `0 <= (X x - Normal c) pow 2` by PROVE_TAC [le_pow2] >> fs [GSYM abs_refl]) >> Rewr'
 >> MATCH_MP_TAC prob_markov_inequality >> art []
 >> reverse CONJ_TAC >- (MATCH_MP_TAC pow_pos_lt >> art [])
 >> Q.UNABBREV_TAC `Y`
 >> METIS_TAC [finite_second_moments_eq_integrable_squares]
QED

(* The special version with `a = p_space p` *)
Theorem chebyshev_ineq :
    !p X t c. prob_space p /\ real_random_variable X p /\
              finite_second_moments p X /\ 0 < t ==>
         prob p ({x | t <= abs (X x - Normal c)} INTER p_space p) <=
           inv (t pow 2) * (expectation p (\x. (X x - Normal c) pow 2))
Proof
    rpt STRIP_TAC
 >> Know `expectation p (\x. (X x - Normal c) pow 2) =
          expectation p (\x. (\x. (X x - Normal c) pow 2) x * indicator_fn (p_space p) x)`
 >- (FULL_SIMP_TAC pure_ss [prob_space_def, p_space_def, events_def, expectation_def] \\
     MATCH_MP_TAC integral_mspace >> art [])
 >> BETA_TAC >> Rewr'
 >> MATCH_MP_TAC chebyshev_inequality >> art []
 >> MATCH_MP_TAC EVENTS_SPACE >> art []
QED

(* The special version with `a = p_space p` and `m = expectation p X` *)
Theorem chebyshev_ineq_variance :
    !p X t. prob_space p /\ real_random_variable X p /\
            finite_second_moments p X /\ 0 < t ==>
         prob p ({x | t <= abs (X x - expectation p X)} INTER p_space p) <=
           inv (t pow 2) * variance p X
Proof
    RW_TAC std_ss [variance_alt]
 >> IMP_RES_TAC finite_second_moments_imp_finite_expectation
 >> `?c. expectation p X = Normal c` by PROVE_TAC [extreal_cases] >> POP_ORW
 >> MATCH_MP_TAC chebyshev_ineq >> art []
QED

(******************************************************************************)
(*  Independent families [3, p.31-33] - 9 definitions                         *)
(******************************************************************************)

(* "The concept of mutual independence of two or more experiments holds,
    in a certain sense, a central position in the theory of probability....
    Historically, the independence of experiments and random variables represents
    the very mathematical concept that has given the theory of probability its
    peculiar stamp."

  -- A. N. Kolmogorov, "Foundations of the Theory of Probability." [1] *)

(* 1. independence of two events: (DO NOT CHANGE) *)
Definition indep_def :
    indep p a b = (a IN events p /\ b IN events p /\
                   (prob p (a INTER b) = prob p a * prob p b))
End

(* 2. extension of `indep`: a sequence of pairwise independent events

   new definition based on real_topologyTheory.pairwise, users may use
  `pairwise (indep p) E` if possible (for any two different events in E).
 *)
Definition pairwise_indep_events :
    pairwise_indep_events p E (J :'index set) =
      pairwise (\i j. indep p (E i) (E j)) J
End

Theorem pairwise_indep_events_def :
    !p E (J :'index set).
       pairwise_indep_events p E J <=>
       !i j. i IN J /\ j IN J /\ i <> j ==> indep p (E i) (E j)
Proof
    RW_TAC std_ss [pairwise_indep_events, pairwise]
QED

(* 3. extension of `indep`: a sequence of total independent events *)
Definition indep_events_def :
    indep_events p E (J :'index set) =
      !N. N SUBSET J /\ N <> {} /\ FINITE N ==>
         (prob p (BIGINTER (IMAGE E N)) = PI (prob p o E) N)
End

(* 4. independence of two sets/collections of events: (DO NOT CHANGE) *)
Definition indep_families_def :
    indep_families p q r = !s t. s IN q /\ t IN r ==> indep p s t
End

(* 5. extension of `indep_families`: pairwise independent sets/collections of events *)
Definition pairwise_indep_sets :
    pairwise_indep_sets p A (J :'index set) =
      pairwise (\i j. indep_families p (A i) (A j)) J
End

Theorem pairwise_indep_sets_def :
    !p A J. pairwise_indep_sets p A J <=>
            !i j. i IN J /\ j IN J /\ i <> j ==> indep_families p (A i) (A j)
Proof
    RW_TAC std_ss [pairwise_indep_sets, pairwise]
QED

(* 6. extension of `indep_families`: total independent sets/collections of events *)
Definition indep_sets_def :
    indep_sets p A (J :'index set) =
      !N. N SUBSET J /\ N <> {} /\ FINITE N ==>
         !E. E IN (N --> A) ==> (prob p (BIGINTER (IMAGE E N)) = PI (prob p o E) N)
End

(* 7. independence of two r.v.'s, added `INTER p_space p` after taking the PREIMAGE *)
Definition indep_rv_def :
    indep_rv (p :'a p_space) (X :'a -> 'b) (Y :'a -> 'b) s t =
      !a b. (a IN subsets s) /\ (b IN subsets t) ==>
            indep p ((PREIMAGE X a) INTER p_space p)
                    ((PREIMAGE Y b) INTER p_space p)
End

(* 8. extension of `indep_rv`: pairwise independent random variables *)
Definition pairwise_indep_vars :
    pairwise_indep_vars p X A (J :'index set) =
      pairwise (\i j. indep_rv p (X i) (X j) (A i) (A j)) J
End

Theorem pairwise_indep_vars_def :
    !p X A (J :'index set).
       pairwise_indep_vars p X A J <=>
       !i j. i IN J /\ j IN J /\ i <> j ==> indep_rv p (X i) (X j) (A i) (A j)
Proof
    RW_TAC std_ss [pairwise_indep_vars, pairwise]
QED

(* 9. extension of `indep-rv`: total independent random variables. *)
val indep_vars_def = Define
   `indep_vars p X A (J :'index set) <=>
      !E. E IN (J --> (subsets o A)) ==>
          indep_events p (\n. (PREIMAGE (X n) (E n)) INTER p_space p) J`;

val indep_function_def = Define
   `indep_function p =
   {f | indep_families p (IMAGE (PREIMAGE (FST o f)) UNIV)
                         (IMAGE (PREIMAGE (SND o f)) (events p))}`;

val PROB_INDEP = store_thm
  ("PROB_INDEP",
  ``!p s t u. indep p s t /\ (u = s INTER t) ==> (prob p u = prob p s * prob p t)``,
    RW_TAC std_ss [indep_def]);

val INDEP_EMPTY = store_thm
  ("INDEP_EMPTY", ``!p s. prob_space p /\ s IN events p ==> indep p {} s``,
    RW_TAC std_ss [indep_def, EVENTS_EMPTY, PROB_EMPTY, INTER_EMPTY, mul_lzero]);

val INDEP_SPACE = store_thm
  ("INDEP_SPACE", ``!p s. prob_space p /\ s IN events p ==> indep p (p_space p) s``,
    RW_TAC std_ss [indep_def, EVENTS_SPACE, PROB_UNIV, INTER_PSPACE,mul_lone]);

(* `prob_space p` is not needed here *)
val INDEP_SYM = store_thm
  ("INDEP_SYM", ``!p a b. indep p a b ==> indep p b a``,
    RW_TAC std_ss [indep_def]
 >> PROVE_TAC [mul_comm, INTER_COMM]);

val INDEP_SYM_EQ = store_thm
  ("INDEP_SYM_EQ", ``!p a b. indep p a b <=> indep p b a``,
    rpt GEN_TAC >> EQ_TAC >> rpt STRIP_TAC
 >> MATCH_MP_TAC INDEP_SYM >> art []);

val INDEP_FAMILIES_SYM = store_thm
  ("INDEP_FAMILIES_SYM", ``!p q r. indep_families p q r ==> indep_families p r q``,
    RW_TAC std_ss [indep_families_def]
 >> MATCH_MP_TAC INDEP_SYM
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []);

val INDEP_RV_SYM = store_thm
  ("INDEP_RV_SYM", ``!p X Y s t. indep_rv p X Y s t ==> indep_rv p Y X t s``,
    RW_TAC std_ss [indep_rv_def]
 >> MATCH_MP_TAC INDEP_SYM
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []);

val INDEP_REFL = store_thm (* the simplest "0-1 law" *)
  ("INDEP_REFL",
  ``!p a. prob_space p /\ a IN events p ==>
         (indep p a a = (prob p a = 0) \/ (prob p a = 1))``,
    RW_TAC std_ss [indep_def, INTER_IDEMPOT]
 >> `?r. prob p a = Normal r` by METIS_TAC [PROB_FINITE, extreal_cases]
 >> RW_TAC std_ss [extreal_mul_def, extreal_of_num_def, extreal_11]
 >> METIS_TAC [REAL_MUL_IDEMPOT]);

val INDEP_COMPL = store_thm
  ("INDEP_COMPL",
  ``!p s t. prob_space p /\ indep p s t ==> indep p s (p_space p DIFF t)``,
    RW_TAC std_ss [indep_def, EVENTS_COMPL, PROB_COMPL]
 >> `s SUBSET (p_space p) /\ t SUBSET (p_space p)` by PROVE_TAC [PROB_SPACE_SUBSET_PSPACE]
 >> `s INTER (p_space p DIFF t) = s DIFF (s INTER t)` by ASM_SET_TAC []
 >> POP_ORW
 >> `(s INTER t) SUBSET s` by PROVE_TAC [INTER_SUBSET]
 >> `s INTER t IN events p` by PROVE_TAC [EVENTS_INTER]
 >> Know `prob p (s DIFF (s INTER t)) = prob p s - prob p (s INTER t)`
 >- (MATCH_MP_TAC PROB_DIFF_SUBSET >> art [])
 >> Rewr' >> art []
 >> Know `prob p s * (1 - prob p t) = prob p s * 1 - prob p s * prob p t`
 >- (MATCH_MP_TAC sub_ldistrib \\
     REWRITE_TAC [extreal_of_num_def, extreal_not_infty] \\
     PROVE_TAC [PROB_FINITE])
 >> Rewr' >> REWRITE_TAC [mul_rone]);

val INDEP_COMPL2 = store_thm
  ("INDEP_COMPL2",
  ``!p s t. prob_space p /\ indep p s t ==> indep p (p_space p DIFF s) (p_space p DIFF t)``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC INDEP_COMPL >> art []
 >> Suff `indep p t (p_space p DIFF s)`
 >- (DISCH_TAC >> MATCH_MP_TAC INDEP_SYM >> art [])
 >> MATCH_MP_TAC INDEP_COMPL >> art []
 >> MATCH_MP_TAC INDEP_SYM >> art []);

(* total ==> pairwise independence (of events) *)
Theorem total_imp_pairwise_indep_events :
    !p E (J :'index set).
           (!n. n IN J ==> (E n) IN events p) /\ indep_events p E J ==>
            pairwise_indep_events p E J
Proof
    RW_TAC std_ss [indep_events_def, pairwise_indep_events_def, indep_def]
 >> Q.PAT_X_ASSUM `!N. N SUBSET J /\ N <> {} /\ FINITE N ==> X`
      (MP_TAC o (Q.SPEC `{i; j}`))
 >> Know `{i; j} SUBSET J` >- ASM_SET_TAC []
 >> Know `{i; j} <> {}` >- SET_TAC []
 >> Know `FINITE {i; j}` >- PROVE_TAC [FINITE_INSERT, FINITE_SING]
 >> Know `BIGINTER (IMAGE E {i; j}) = E i INTER E j`
 >- (RW_TAC std_ss [Once EXTENSION, IN_BIGINTER_IMAGE, IN_SING, IN_INSERT, IN_INTER] \\
     METIS_TAC [])
 >> RW_TAC std_ss []
 >> `!i. prob p (E i) = (prob p o E) i` by PROVE_TAC [o_DEF] >> POP_ORW
 >> MATCH_MP_TAC EXTREAL_PROD_IMAGE_PAIR >> art []
QED

(* total ==> pairwise independence (of sets of events) *)
Theorem total_imp_pairwise_indep_sets :
    !p A (J :'index set).
      (!n. n IN J ==> (A n) SUBSET events p) /\ indep_sets p A J ==>
       pairwise_indep_sets p A J
Proof
    RW_TAC std_ss [indep_sets_def, pairwise_indep_sets_def, indep_families_def,
                   indep_def, IN_DFUNSET]
 >- PROVE_TAC [SUBSET_DEF]
 >- PROVE_TAC [SUBSET_DEF]
 >> Q.PAT_X_ASSUM `!N. N SUBSET J /\ N <> {} /\ FINITE N ==> X`
      (MP_TAC o (Q.SPEC `{i; j}`))
 >> Know `{i; j} SUBSET J` >- ASM_SET_TAC []
 >> Know `{i; j} <> {}` >- SET_TAC []
 >> Know `FINITE {i; j}` >- PROVE_TAC [FINITE_INSERT, FINITE_SING]
 >> Know `!E. BIGINTER (IMAGE E {i; j}) = E i INTER E j`
 >- (RW_TAC std_ss [Once EXTENSION, IN_BIGINTER_IMAGE, IN_SING, IN_INSERT, IN_INTER] \\
     METIS_TAC [])
 >> Know `!E. PI (prob p o E) {i; j} = prob p (E i) * prob p (E j)`
 >- (GEN_TAC \\
     `!i. prob p (E i) = (prob p o E) i` by PROVE_TAC [o_DEF] >> POP_ORW \\
     MATCH_MP_TAC EXTREAL_PROD_IMAGE_PAIR >> art [])
 >> RW_TAC std_ss []
 >> fs [IN_INSERT, IN_SING]
 >> Q.ABBREV_TAC `E = \x. if x = i then s else if x = j then t else {}`
 >> Q.PAT_X_ASSUM `!E. X ==> Y` (MP_TAC o (Q.SPEC `E`))
 >> Know `!x. (x = i) \/ (x = j) ==> E x IN A x`
 >- (Q.UNABBREV_TAC `E` >> RW_TAC std_ss [])
 >> Know `E i = s` >- (Q.UNABBREV_TAC `E` >> RW_TAC std_ss [])
 >> Know `E j = t` >- (Q.UNABBREV_TAC `E` >> RW_TAC std_ss [])
 >> RW_TAC std_ss []
 >> POP_ASSUM MATCH_MP_TAC >> art []
QED

(* total ==> pairwise independence (of random variables) *)
Theorem total_imp_pairwise_indep_vars :
    !p X A (J :'index set).
       (!i. i IN J ==> random_variable (X i) p (A i)) /\ indep_vars p X A J ==>
       pairwise_indep_vars p X A J
Proof
    RW_TAC std_ss [indep_vars_def, pairwise_indep_vars_def, indep_rv_def,
                   indep_events_def, random_variable_def]
 >> REWRITE_TAC [indep_def]
 >> STRONG_CONJ_TAC
 >- (`X i IN measurable (p_space p,events p) (A i)` by PROVE_TAC [] \\
     POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [IN_MEASURABLE, space_def, subsets_def])) \\
     POP_ASSUM MATCH_MP_TAC >> art []) >> DISCH_TAC
 >> STRONG_CONJ_TAC
 >- (`X j IN measurable (p_space p,events p) (A j)` by PROVE_TAC [] \\
     POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [IN_MEASURABLE, space_def, subsets_def])) \\
     POP_ASSUM MATCH_MP_TAC >> art []) >> DISCH_TAC
 >> Q.ABBREV_TAC `E = \x. if x = i then a else if x = j then b else {}`
 >> Q.PAT_X_ASSUM `!E. E IN (J --> subsets o A) => P` (MP_TAC o (Q.SPEC `E`))
 >> SIMP_TAC std_ss [IN_DFUNSET, o_DEF]
 >> Know `!x. x IN J ==> E x IN subsets (A x)`
 >- (Q.UNABBREV_TAC `E` >> RW_TAC std_ss [] \\
     `X x IN measurable (p_space p,events p) (A x)` by PROVE_TAC [] \\
     POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [IN_MEASURABLE, space_def, subsets_def])) \\
     MATCH_MP_TAC ALGEBRA_EMPTY \\
     fs [sigma_algebra_def])
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM `!N. N SUBSET J /\ N <> {} /\ FINITE N ==> P`
      (MP_TAC o (Q.SPEC `{i; j}`))
 >> Know `{i; j} SUBSET J` >- ASM_SET_TAC []
 >> Know `{i; j} <> {}` >- SET_TAC []
 >> Know `FINITE {i; j}` >- PROVE_TAC [FINITE_INSERT, FINITE_SING]
 >> Know `BIGINTER (IMAGE (\n. PREIMAGE (X n) (E n) INTER p_space p) {i; j}) =
           (\n. PREIMAGE (X n) (E n) INTER p_space p) i INTER
           (\n. PREIMAGE (X n) (E n) INTER p_space p) j`
 >- (RW_TAC std_ss [Once EXTENSION, IN_BIGINTER_IMAGE, IN_SING, IN_INSERT, IN_INTER] \\
     METIS_TAC [])
 >> Know `PI (\n. prob p (PREIMAGE (X n) (E n) INTER p_space p)) {i; j} =
             (\n. prob p (PREIMAGE (X n) (E n) INTER p_space p)) i *
             (\n. prob p (PREIMAGE (X n) (E n) INTER p_space p)) j`
 >- (MATCH_MP_TAC EXTREAL_PROD_IMAGE_PAIR >> art [])
 >> Know `E i = a` >- (Q.UNABBREV_TAC `E` >> RW_TAC std_ss [])
 >> Know `E j = b` >- (Q.UNABBREV_TAC `E` >> RW_TAC std_ss [])
 >> RW_TAC std_ss []
QED

(******************************************************************************)
(*  Kolmogorov's 0-1 Law (for independent events)                             *)
(******************************************************************************)

(* Probability version of SIGMA_SUBSET_MEASURABLE_SETS *)
Theorem SIGMA_SUBSET_EVENTS[local] :
    !a p. prob_space p /\ a SUBSET events p ==>
          subsets (sigma (p_space p) a) SUBSET events p
Proof
    RW_TAC std_ss [prob_space_def, p_space_def, events_def]
 >> MATCH_MP_TAC SIGMA_SUBSET_MEASURABLE_SETS >> art []
QED

(* Lemma 3.5.2 [3, p.37], with simplifications from the Solution Manual of [9]
   (Problem 5.11)
 *)
Theorem INDEP_FAMILIES_SIGMA_lemma[local] :
    !p B n (J :'index set).
              prob_space p /\ (IMAGE B (n INSERT J)) SUBSET events p /\
              indep_events p B (n INSERT J) /\ n NOTIN J
          ==> indep_families p {B n} (subsets (sigma (p_space p) (IMAGE B J)))
Proof
    RW_TAC std_ss [indep_families_def, IN_SING]
 >> REWRITE_TAC [indep_def]
 >> Know `B n IN events p /\ (IMAGE B J) SUBSET events p`
 >- fs [SUBSET_DEF, IN_IMAGE, IN_INSERT] >> STRIP_TAC >> art []
 >> STRONG_CONJ_TAC
 >- (Suff `subsets (sigma (p_space p) (IMAGE B J)) SUBSET events p`
     >- (DISCH_TAC >> PROVE_TAC [SUBSET_DEF]) \\
     MATCH_MP_TAC SIGMA_SUBSET_EVENTS >> art []) >> DISCH_TAC
 >> Q.ABBREV_TAC `G = (p_space p) INSERT
                      {BIGINTER (IMAGE B N) | N SUBSET J /\ FINITE N /\ N <> {}}`
 >> Q.ABBREV_TAC `u = \x. prob p (B n INTER x)`
 >> Q.ABBREV_TAC `v = \x. prob p (B n) * prob p x`
 >> Suff `u t = v t` >- METIS_TAC []
 >> irule UNIQUENESS_OF_MEASURE_FINITE
 >> qexistsl_tac [`p_space p`, `G`]
 (* !s t. s IN G /\ t IN G ==> s INTER t IN G *)
 >> CONJ_TAC
 >- (Q.UNABBREV_TAC `G` >> RW_TAC std_ss [GSPECIFICATION, IN_INSERT] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       DISJ1_TAC >> REWRITE_TAC [INTER_IDEMPOT],
       (* goal 2 (of 4) *)
       DISJ2_TAC >> Q.EXISTS_TAC `N` >> art [] \\
       Suff `BIGINTER (IMAGE B N) SUBSET p_space p` >- PROVE_TAC [INTER_SUBSET_EQN] \\
       MATCH_MP_TAC BIGINTER_SUBSET \\
       reverse CONJ_TAC
       >- (RW_TAC std_ss [Once EXTENSION, NOT_IN_EMPTY, IN_IMAGE] \\
           fs [GSYM MEMBER_NOT_EMPTY] >> Q.EXISTS_TAC `x` >> art []) \\
       RW_TAC std_ss [IN_IMAGE] \\
      `!i. i IN J ==> B i IN events p` by PROVE_TAC [SUBSET_DEF, IN_INSERT, IN_IMAGE] \\
      `B x IN events p` by PROVE_TAC [SUBSET_DEF] \\
       MATCH_MP_TAC PROB_SPACE_SUBSET_PSPACE >> art [],
       (* goal 3 (of 4) *)
       DISJ2_TAC >> Q.EXISTS_TAC `N` >> art [] \\
       Suff `BIGINTER (IMAGE B N) SUBSET p_space p` >- PROVE_TAC [INTER_SUBSET_EQN] \\
       MATCH_MP_TAC BIGINTER_SUBSET \\
       reverse CONJ_TAC
       >- (RW_TAC std_ss [Once EXTENSION, NOT_IN_EMPTY, IN_IMAGE] \\
           fs [GSYM MEMBER_NOT_EMPTY] >> Q.EXISTS_TAC `x` >> art []) \\
       RW_TAC std_ss [IN_IMAGE] \\
      `!i. i IN J ==> B i IN events p` by PROVE_TAC [SUBSET_DEF, IN_UNION, IN_IMAGE] \\
      `B x IN events p` by PROVE_TAC [SUBSET_DEF] \\
       MATCH_MP_TAC PROB_SPACE_SUBSET_PSPACE >> art [],
       (* goal 4 (of 4) *)
       DISJ2_TAC >> Q.EXISTS_TAC `N UNION N'` \\
       CONJ_TAC >- REWRITE_TAC [BIGINTER_UNION, IMAGE_UNION] \\
       art [FINITE_UNION] \\
       CONJ_TAC >- (RW_TAC std_ss [IN_UNION, SUBSET_DEF] >> fs [SUBSET_DEF]) \\
       RW_TAC std_ss [Once EXTENSION, IN_UNION, NOT_IN_EMPTY] \\
       fs [GSYM MEMBER_NOT_EMPTY] >> Q.EXISTS_TAC `x` >> DISJ1_TAC >> art [] ])
 (* !s. s IN G ==> (u s = v s) *)
 >> CONJ_TAC
 >- (Q.UNABBREV_TAC `G` >> RW_TAC std_ss [GSPECIFICATION, IN_INSERT] (* 2 subgoals *)
     >- (Q.UNABBREV_TAC `u` >> Q.UNABBREV_TAC `v` >> BETA_TAC \\
         RW_TAC std_ss [PROB_UNIV, mul_rone, PROB_UNDER_UNIV]) \\
     Q.UNABBREV_TAC `u` >> Q.UNABBREV_TAC `v` >> BETA_TAC \\
     Know `B n INTER BIGINTER (IMAGE B N) = BIGINTER (IMAGE B (n INSERT N))`
     >- REWRITE_TAC [IMAGE_INSERT, BIGINTER_INSERT] >> Rewr' \\
     FULL_SIMP_TAC bool_ss [indep_events_def] \\
    `(n INSERT N) SUBSET (n INSERT J) /\ N SUBSET (n INSERT J)` by ASM_SET_TAC [] \\
    `FINITE (n INSERT N)` by PROVE_TAC [FINITE_INSERT] \\
     Know `prob p (BIGINTER (IMAGE B (n INSERT N))) = PI (prob p o B) (n INSERT N)`
     >- (FIRST_X_ASSUM MATCH_MP_TAC >> art [] \\
         RW_TAC std_ss [Once EXTENSION, IN_INSERT, NOT_IN_EMPTY] \\
         Q.EXISTS_TAC `n` >> DISJ1_TAC >> REWRITE_TAC []) >> Rewr' \\
     Know `prob p (BIGINTER (IMAGE B N)) = PI (prob p o B) N`
     >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> Rewr' \\
     Know `PI (prob p o B) (n INSERT N) = (prob p o B) n * PI (prob p o B) (N DELETE n)`
     >- (MATCH_MP_TAC EXTREAL_PROD_IMAGE_PROPERTY >> art []) >> Rewr' \\
    `N DELETE n = N` by ASM_SET_TAC [] >> POP_ORW \\
     SIMP_TAC std_ss [o_DEF])
 >> Know `subsets (sigma (p_space p) G) SUBSET events p`
 >- (MATCH_MP_TAC SIGMA_SUBSET_EVENTS >> art [] \\
     Q.UNABBREV_TAC `G` >> RW_TAC std_ss [GSPECIFICATION, IN_INSERT, SUBSET_DEF]
     >- (MATCH_MP_TAC EVENTS_SPACE >> art []) \\
     MATCH_MP_TAC EVENTS_COUNTABLE_INTER >> art [] \\
     CONJ_TAC >- (MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC `IMAGE B J` >> art [] \\
                  MATCH_MP_TAC IMAGE_SUBSET >> PROVE_TAC [SUBSET_DEF]) \\
     CONJ_TAC >- (MATCH_MP_TAC finite_countable \\
                  MATCH_MP_TAC IMAGE_FINITE >> art []) \\
     RW_TAC std_ss [Once EXTENSION, IN_IMAGE, NOT_IN_EMPTY] \\
     fs [GSYM MEMBER_NOT_EMPTY] >> Q.EXISTS_TAC `x` >> art [])
 >> DISCH_TAC
 >> Know `sigma_algebra (p_space p,subsets (sigma (p_space p) G))`
 >- (REWRITE_TAC [SIGMA_REDUCE] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
     Q.UNABBREV_TAC `G` >> RW_TAC std_ss [subset_class_def, GSPECIFICATION, IN_INSERT]
     >- REWRITE_TAC [SUBSET_REFL] \\
     MATCH_MP_TAC PROB_SPACE_SUBSET_PSPACE >> art [] \\
     MATCH_MP_TAC EVENTS_COUNTABLE_INTER >> art [] \\
     CONJ_TAC >- (MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC `IMAGE B J` >> art [] \\
                  MATCH_MP_TAC IMAGE_SUBSET >> PROVE_TAC [SUBSET_DEF]) \\
     CONJ_TAC >- (MATCH_MP_TAC finite_countable \\
                  MATCH_MP_TAC IMAGE_FINITE >> art []) \\
     RW_TAC std_ss [Once EXTENSION, IN_IMAGE, NOT_IN_EMPTY] \\
     fs [GSYM MEMBER_NOT_EMPTY] >> Q.EXISTS_TAC `x` >> art [])
 >> DISCH_TAC
 (* measure_space (p_space p,subsets (sigma (p_space p) G),u) *)
 >> CONJ_TAC
 >- (Suff `measure_space (p_space p,events p,u)`
     >- (DISCH_TAC >> MATCH_MP_TAC MEASURE_SPACE_RESTRICTION \\
         Q.EXISTS_TAC `events p` >> art []) \\
     Q.UNABBREV_TAC `u` \\
     fs [p_space_def, events_def, prob_def, prob_space_def] \\
     MATCH_MP_TAC MEASURE_SPACE_RESTRICTED_MEASURE >> art [])
 (* measure_space (p_space p,subsets (sigma (p_space p) G),v) *)
 >> CONJ_TAC
 >- (Suff `measure_space (p_space p,events p,v)`
     >- (DISCH_TAC >> MATCH_MP_TAC MEASURE_SPACE_RESTRICTION \\
         Q.EXISTS_TAC `events p` >> art []) \\
     Q.UNABBREV_TAC `v` \\
    `prob p (B n) <> NegInf /\ prob p (B n) <> PosInf` by PROVE_TAC [PROB_FINITE] \\
    `0 <= prob p (B n)` by PROVE_TAC [PROB_POSITIVE] \\
    `?c. prob p (B n) = Normal c` by PROVE_TAC [extreal_cases] \\
    `0 <= c` by PROVE_TAC [extreal_of_num_def, extreal_le_eq] \\
     fs [p_space_def, events_def, prob_def, prob_space_def] \\
     MATCH_MP_TAC MEASURE_SPACE_CMUL >> art [])
 (* u (p_space p) = v (p_space p) *)
 >> CONJ_TAC
 >- (Q.UNABBREV_TAC `u` >> Q.UNABBREV_TAC `v` >> BETA_TAC \\
     RW_TAC std_ss [PROB_UNIV, mul_rone, PROB_UNDER_UNIV])
 (* t IN subsets (sigma (p_space p) G) *)
 >> CONJ_TAC
 >- (Suff `subsets (sigma (p_space p) (IMAGE B J)) SUBSET subsets (sigma (p_space p) G)`
     >- (DISCH_THEN (ASSUME_TAC o (REWRITE_RULE [SUBSET_DEF])) \\
         POP_ASSUM MATCH_MP_TAC >> art []) \\
     MATCH_MP_TAC SIGMA_MONOTONE \\
     Q.UNABBREV_TAC `G` \\
     RW_TAC std_ss [Once SUBSET_DEF, IN_IMAGE, GSPECIFICATION, IN_INSERT] \\
     DISJ2_TAC >> Q.EXISTS_TAC `{x'}` \\
     RW_TAC std_ss [IMAGE_SING, BIGINTER_SING, FINITE_SING, SUBSET_DEF, IN_SING] \\
     RW_TAC std_ss [Once EXTENSION, NOT_IN_EMPTY, IN_SING])
 (* u (p_space p) < PosInf *)
 >> CONJ_TAC
 >- (Q.UNABBREV_TAC `u` >> BETA_TAC \\
     RW_TAC std_ss [PROB_UNDER_UNIV, PROB_LT_POSINF])
 (* subset_class (p_space p) G *)
 >> Q.UNABBREV_TAC `G`
 >> RW_TAC std_ss [subset_class_def, IN_INSERT, GSPECIFICATION]
 >- REWRITE_TAC [SUBSET_REFL]
 >> MATCH_MP_TAC PROB_SPACE_SUBSET_PSPACE >> art []
 >> MATCH_MP_TAC EVENTS_COUNTABLE_INTER >> art []
 >> CONJ_TAC >- (MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC `IMAGE B J` >> art [] \\
                 MATCH_MP_TAC IMAGE_SUBSET >> PROVE_TAC [SUBSET_DEF])
 >> CONJ_TAC >- (MATCH_MP_TAC finite_countable \\
                 MATCH_MP_TAC IMAGE_FINITE >> art [])
 >> RW_TAC std_ss [Once EXTENSION, IN_IMAGE, NOT_IN_EMPTY]
 >> fs [GSYM MEMBER_NOT_EMPTY] >> Q.EXISTS_TAC `x` >> art []
QED

(* Lemma 3.5.2 [3, p.37], more useful form *)
Theorem INDEP_FAMILIES_SIGMA_lemma1[local] :
    !p A m (N :'index set) S2.
         prob_space p /\ IMAGE A (m INSERT N) SUBSET events p /\
         indep_events p A (m INSERT N) /\ m NOTIN N /\
         S2 IN subsets (sigma (p_space p) (IMAGE A N)) ==> indep p (A m) S2
Proof
    rpt STRIP_TAC
 >> irule (SIMP_RULE std_ss [indep_families_def, IN_SING]
                            (Q.SPEC `p` INDEP_FAMILIES_SIGMA_lemma)) >> art []
 >> Q.EXISTS_TAC `N` >> art []
QED

(* Corollary 3.5.3 of [3, p.37], Part I *)
Theorem INDEP_FAMILIES_SIGMA_lemma2[local] :
    !p A (M :'index set) N m S1.
       prob_space p /\ (IMAGE A (M UNION N)) SUBSET events p /\
       indep_events p A (M UNION N) /\ DISJOINT M N /\ m IN M /\ N <> {} /\
       S1 IN (subsets (sigma (p_space p) (IMAGE A M))) ==>
       indep_events p (\x. if x IN N then A x else S1) (m INSERT N)
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC `G = {BIGINTER (IMAGE A J) | J SUBSET N /\ FINITE J /\ J <> {}}`
 >> fs [GSYM MEMBER_NOT_EMPTY]
 >> rename1 `n IN N`
 >> Q.ABBREV_TAC `B = \a x. if x IN M then A x else a`
 >> Know `!a. a IN G ==> indep_events p (B a) (n INSERT M)`
 >- (Q.UNABBREV_TAC `B` >> BETA_TAC \\
     Q.UNABBREV_TAC `G` \\
     RW_TAC std_ss [GSPECIFICATION, indep_events_def, IN_INSERT] \\
     Cases_on `n NOTIN N'` (* easy case *)
     >- (`N' SUBSET M` by PROVE_TAC [SUBSET_INSERT] \\
         Know `IMAGE (\x. if x IN M then A x else BIGINTER (IMAGE A J)) N' = IMAGE A N'`
         >- (RW_TAC std_ss [Once EXTENSION, IN_IMAGE] \\
             EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
             [ (* goal 3.1 (of 2) *)
              `x'' IN M` by PROVE_TAC [SUBSET_DEF] >> fs [] \\
               Q.EXISTS_TAC `x''` >> art [],
               (* goal 3.2 (of 2) *)
              `x'' IN M` by PROVE_TAC [SUBSET_DEF] \\
               Q.EXISTS_TAC `x''` >> ASM_SIMP_TAC std_ss [] ]) >> Rewr' \\
         Know `PI (prob p o (\x. if x IN M then A x else BIGINTER (IMAGE A J))) N' =
               PI (prob p o A) N'`
         >- (irule EXTREAL_PROD_IMAGE_EQ >> RW_TAC std_ss [] \\
             `x' IN M` by PROVE_TAC [SUBSET_DEF]) >> Rewr' \\
         fs [indep_events_def] >> FIRST_X_ASSUM MATCH_MP_TAC >> art [] \\
         ASM_SET_TAC []) \\
     fs [] (* hard case: `n IN N'` *) \\
     Q.ABBREV_TAC `N'' = N' DELETE n` \\
    `N'' SUBSET M` by ASM_SET_TAC [] \\
    `N'' DELETE n = N''` by ASM_SET_TAC [] \\
    `N' = n INSERT N''` by ASM_SET_TAC [] >> POP_ORW \\
    `n NOTIN N''` by ASM_SET_TAC [] \\
    `n NOTIN M` by ASM_SET_TAC [DISJOINT_DEF] \\
     ASM_SIMP_TAC std_ss [IMAGE_INSERT] \\
     Know `IMAGE (\x. if x IN M then A x else BIGINTER (IMAGE A J)) N'' = IMAGE A N''`
     >- (RW_TAC std_ss [Once EXTENSION, IN_IMAGE] \\
         EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
         [ (* goal 3.1 (of 2) *)
          `x'' IN M` by PROVE_TAC [SUBSET_DEF] >> fs [] \\
           Q.EXISTS_TAC `x''` >> art [],
           (* goal 3.2 (of 2) *)
          `x'' IN M` by PROVE_TAC [SUBSET_DEF] \\
           Q.EXISTS_TAC `x''` >> ASM_SIMP_TAC std_ss [] ]) >> Rewr' \\
     REWRITE_TAC [BIGINTER_INSERT, GSYM BIGINTER_UNION, GSYM IMAGE_UNION] \\
    `N'' SUBSET N'` by ASM_SET_TAC [] \\
    `FINITE N''` by PROVE_TAC [SUBSET_FINITE_I] \\
     POP_ASSUM ((ASM_SIMP_TAC std_ss) o wrap o (MATCH_MP EXTREAL_PROD_IMAGE_PROPERTY)) \\
     Know `PI (prob p o (\x. if x IN M then A x else BIGINTER (IMAGE A J))) N'' =
           PI (prob p o A) N''`
     >- (irule EXTREAL_PROD_IMAGE_EQ \\
         RW_TAC std_ss [] >- (`x' IN M` by PROVE_TAC [SUBSET_DEF]) \\
         PROVE_TAC [SUBSET_FINITE_I]) >> Rewr' \\
     FULL_SIMP_TAC std_ss [indep_events_def] \\
     Know `prob p (BIGINTER (IMAGE A (J UNION N''))) = PI (prob p o A) (J UNION N'')`
     >- (FIRST_X_ASSUM MATCH_MP_TAC >> art [FINITE_UNION] \\
         CONJ_TAC >- ASM_SET_TAC [] \\
         CONJ_TAC >- ASM_SET_TAC [] \\
         PROVE_TAC [SUBSET_FINITE_I]) >> Rewr' \\
     Know `prob p (BIGINTER (IMAGE A J)) = PI (prob p o A) J`
     >- (FIRST_X_ASSUM MATCH_MP_TAC >> art [] \\
         CONJ_TAC >- ASM_SET_TAC [] \\
         METIS_TAC [MEMBER_NOT_EMPTY]) >> Rewr' \\
     MATCH_MP_TAC EXTREAL_PROD_IMAGE_DISJOINT_UNION >> art [] \\
     CONJ_TAC >- PROVE_TAC [SUBSET_FINITE_I] \\
     MATCH_MP_TAC SUBSET_DISJOINT \\
     qexistsl_tac [`N`, `M`] >> art [DISJOINT_SYM])
 >> DISCH_TAC
 >> Know `!s a. a IN G /\ s IN subsets (sigma (p_space p) (IMAGE (B a) M)) ==>
                indep p (B a n) s`
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC INDEP_FAMILIES_SIGMA_lemma1 \\
     Q.EXISTS_TAC `M` >> art [] \\
     Know `n NOTIN M` >- ASM_SET_TAC [DISJOINT_DEF] >> DISCH_TAC >> art [] \\
     reverse CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     RW_TAC std_ss [IMAGE_INSERT, INSERT_SUBSET] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Know `B a n = a` >- (Q.UNABBREV_TAC `B` >> ASM_SIMP_TAC std_ss []) >> Rewr' \\
       Q.PAT_X_ASSUM `a IN G` MP_TAC \\
       Q.UNABBREV_TAC `G` >> RW_TAC std_ss [GSPECIFICATION] \\
       MATCH_MP_TAC EVENTS_BIGINTER_FN >> art [GSYM MEMBER_NOT_EMPTY] \\
       CONJ_TAC
       >- (MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC `IMAGE A N` >> art [] \\
           MATCH_MP_TAC IMAGE_SUBSET >> art []) \\
       CONJ_TAC >- (MATCH_MP_TAC finite_countable >> art []) \\
       Q.EXISTS_TAC `x` >> art [],
       (* goal 2 (of 2) *)
       Suff `IMAGE (B a) M = IMAGE A M` >- METIS_TAC [] \\
       Q.UNABBREV_TAC `B` >> RW_TAC std_ss [Once EXTENSION, IN_IMAGE] \\
       EQ_TAC >> rpt STRIP_TAC >> fs [] >- (Q.EXISTS_TAC `x'` >> art []) \\
       Q.EXISTS_TAC `x'` >> ASM_SIMP_TAC std_ss [] ])
 >> Know `!a. IMAGE (B a) M = IMAGE A M`
 >- (GEN_TAC >> Q.UNABBREV_TAC `B` >> RW_TAC std_ss [Once EXTENSION, IN_IMAGE] \\
     EQ_TAC >> rpt STRIP_TAC >> fs [] >- (Q.EXISTS_TAC `x'` >> art []) \\
     Q.EXISTS_TAC `x'` >> ASM_SIMP_TAC std_ss []) >> Rewr'
 >> `n NOTIN M` by ASM_SET_TAC [DISJOINT_DEF]
 >> Know `!a. B a n = a`
 >- (GEN_TAC >> Q.UNABBREV_TAC `B` >> RW_TAC std_ss [Once EXTENSION]) >> Rewr'
 >> DISCH_THEN (MP_TAC o (ONCE_REWRITE_RULE [INDEP_SYM_EQ]) o (Q.SPEC `S1`)) >> art []
 >> DISCH_TAC (* !a. a IN G ==> indep p S1 a *)
 >> Q.ABBREV_TAC `B' = \x. if x IN N then A x else S1`
 >> Know `IMAGE B' N = IMAGE A N`
 >- (Q.UNABBREV_TAC `B'` >> RW_TAC std_ss [Once EXTENSION, IN_IMAGE] \\
     EQ_TAC >> rpt STRIP_TAC >> fs [] >- (Q.EXISTS_TAC `x'` >> art []) \\
     Q.EXISTS_TAC `x'` >> ASM_SIMP_TAC std_ss []) >> DISCH_TAC
 >> Q.UNABBREV_TAC `B'` >> BETA_TAC
 >> RW_TAC std_ss [indep_events_def, IN_INSERT]
 >> Cases_on `m NOTIN N'` (* easy case *)
 >- (`N' SUBSET N` by PROVE_TAC [SUBSET_INSERT] \\
     Know `IMAGE (\x. if x IN N then A x else S1) N' = IMAGE A N'`
     >- (RW_TAC std_ss [Once EXTENSION, IN_IMAGE] \\
         EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
         [ (* goal 3.1 (of 2) *)
          `x' IN N` by PROVE_TAC [SUBSET_DEF] >> fs [] \\
           Q.EXISTS_TAC `x'` >> art [],
           (* goal 3.2 (of 2) *)
          `x' IN N` by PROVE_TAC [SUBSET_DEF] \\
           Q.EXISTS_TAC `x'` >> ASM_SIMP_TAC std_ss [] ]) >> Rewr' \\
     Know `PI (prob p o (\x. if x IN N then A x else S1)) N' = PI (prob p o A) N'`
     >- (irule EXTREAL_PROD_IMAGE_EQ >> RW_TAC std_ss [] \\
        `x IN N` by PROVE_TAC [SUBSET_DEF]) >> Rewr' \\
     fs [indep_events_def] >> FIRST_X_ASSUM MATCH_MP_TAC >> art [] \\
     ASM_SET_TAC [])
 >> fs [] (* hard case: `m IN N'` *)
 >> Q.ABBREV_TAC `N'' = N' DELETE m`
 >> `N'' SUBSET N` by ASM_SET_TAC []
 >> `N'' DELETE m = N''` by ASM_SET_TAC []
 >> `N' = m INSERT N''` by ASM_SET_TAC [] >> POP_ORW
 >> `m NOTIN N''` by ASM_SET_TAC []
 >> `m NOTIN N` by ASM_SET_TAC [DISJOINT_DEF]
 >> ASM_SIMP_TAC std_ss [IMAGE_INSERT]
 >> Know `IMAGE (\x. if x IN N then A x else S1) N'' = IMAGE A N''`
 >- (RW_TAC std_ss [Once EXTENSION, IN_IMAGE] \\
     EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
     [ (* goal 3.1 (of 2) *)
      `x' IN N` by PROVE_TAC [SUBSET_DEF] >> fs [] \\
       Q.EXISTS_TAC `x'` >> art [],
       (* goal 3.2 (of 2) *)
      `x' IN N` by PROVE_TAC [SUBSET_DEF] \\
       Q.EXISTS_TAC `x'` >> ASM_SIMP_TAC std_ss [] ]) >> Rewr'
 >> REWRITE_TAC [BIGINTER_INSERT, GSYM BIGINTER_UNION, GSYM IMAGE_UNION]
 >> `N'' SUBSET N'` by ASM_SET_TAC []
 >> `FINITE N''` by PROVE_TAC [SUBSET_FINITE_I]
 >> POP_ASSUM ((ASM_SIMP_TAC std_ss) o wrap o (MATCH_MP EXTREAL_PROD_IMAGE_PROPERTY))
 >> Know `PI (prob p o (\x. if x IN N then A x else S1)) N'' = PI (prob p o A) N''`
 >- (irule EXTREAL_PROD_IMAGE_EQ \\
     RW_TAC std_ss [] >- (`x IN N` by PROVE_TAC [SUBSET_DEF]) \\
     PROVE_TAC [SUBSET_FINITE_I]) >> Rewr'
 >> Cases_on `N'' = {}`
 >- art [IMAGE_EMPTY, BIGINTER_EMPTY, INTER_UNIV, EXTREAL_PROD_IMAGE_EMPTY, mul_rone]
 >> Know `prob p (S1 INTER BIGINTER (IMAGE A N'')) =
          prob p S1 * prob p (BIGINTER (IMAGE A N''))`
 >- (FULL_SIMP_TAC std_ss [indep_def] \\
    `!a. a IN G ==> a IN events p` by PROVE_TAC [] \\
    `!a. a IN G ==> (prob p (S1 INTER a) = prob p S1 * prob p a)` by PROVE_TAC [] \\
     POP_ASSUM MATCH_MP_TAC \\
     Q.UNABBREV_TAC `G` >> RW_TAC std_ss [GSPECIFICATION] \\
     Q.EXISTS_TAC `N''` >> art [] \\
     CONJ_TAC >- PROVE_TAC [SUBSET_FINITE_I] \\
     fs [GSYM MEMBER_NOT_EMPTY] >> Q.EXISTS_TAC `x'` >> art []) >> Rewr'
 >> FULL_SIMP_TAC std_ss [indep_events_def]
 >> Know `prob p (BIGINTER (IMAGE A N'')) = PI (prob p o A) N''`
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> art [FINITE_UNION] \\
     CONJ_TAC >- ASM_SET_TAC [] \\
     PROVE_TAC [SUBSET_FINITE_I]) >> Rewr
QED

(* Corollary 3.5.3 of [3, p.37], Part II (futhermore, ...) *)
Theorem INDEP_FAMILIES_SIGMA :
    !p A (M :'index set) N.
       prob_space p /\ (IMAGE A (M UNION N)) SUBSET events p /\
       indep_events p A (M UNION N) /\ DISJOINT M N /\ M <> {} /\ N <> {} ==>
       indep_families p (subsets (sigma (p_space p) (IMAGE A M)))
                        (subsets (sigma (p_space p) (IMAGE A N)))
Proof
    RW_TAC std_ss [indep_families_def]
 >> rename1 `indep p S1 S2`
 >> FULL_SIMP_TAC std_ss [GSYM MEMBER_NOT_EMPTY]
 >> rename1 `m IN M` >> rename1 `n IN N`
 >> Q.ABBREV_TAC `B' = \x. if x IN N then A x else S1`
 >> Know `IMAGE B' N = IMAGE A N`
 >- (Q.UNABBREV_TAC `B'` >> RW_TAC std_ss [Once EXTENSION, IN_IMAGE] \\
     EQ_TAC >> rpt STRIP_TAC >> fs [] >- (Q.EXISTS_TAC `x'` >> art []) \\
     Q.EXISTS_TAC `x'` >> ASM_SIMP_TAC std_ss []) >> DISCH_TAC
 >> Know `indep_events p B' (m INSERT N)`
 >- (Q.UNABBREV_TAC `B'` >> BETA_TAC \\
     MATCH_MP_TAC INDEP_FAMILIES_SIGMA_lemma2 \\
     Q.EXISTS_TAC `M` >> art [] \\
     REWRITE_TAC [GSYM MEMBER_NOT_EMPTY] >> Q.EXISTS_TAC `n` >> art [])
 >> DISCH_TAC
 >> `m NOTIN N` by ASM_SET_TAC [DISJOINT_DEF]
 >> Know `S1 = B' m`
 >- (Q.UNABBREV_TAC `B'` >> ASM_SIMP_TAC std_ss []) >> Rewr'
 >> MATCH_MP_TAC INDEP_FAMILIES_SIGMA_lemma1
 >> Q.EXISTS_TAC `N` >> art []
 >> ASM_SIMP_TAC std_ss [IMAGE_INSERT, INSERT_SUBSET]
 >> Know `B' m = S1`
 >- (Q.UNABBREV_TAC `B'` >> ASM_SIMP_TAC std_ss []) >> Rewr'
 >> FULL_SIMP_TAC std_ss [IMAGE_UNION, UNION_SUBSET]
 >> Suff `subsets (sigma (p_space p) (IMAGE A M)) SUBSET events p` >- METIS_TAC [SUBSET_DEF]
 >> MATCH_MP_TAC SIGMA_SUBSET_EVENTS >> art []
QED

(* c.f. set_limsup_alt, the only difference here is the additional sigma() inside *)
val tail_algebra_def = Define
   `tail_algebra (p :'a p_space) (E :num -> 'a set) =
      (p_space p,
       BIGINTER (IMAGE (\n. subsets (sigma (p_space p) (IMAGE E (from n)))) UNIV))`;

val tail_algebra_of_rv_def = Define
   `tail_algebra_of_rv (p :'a p_space) (X :num -> 'a -> 'b) (A :num -> 'b algebra) =
      (p_space p,
       BIGINTER (IMAGE (\n. subsets (sigma_functions (p_space p) A X (from n))) UNIV))`;

val _ = overload_on ("tail_algebra", ``tail_algebra_of_rv``);

(* Theorem 3.5.1 of [3, p.37], Kolmogorov 0-1 Law (for independent events).

   NOTE: there's a more general version of "Kolmogorov 0-1 Law" for independent r.v.'s
  ([5, p.3] or [2, p.264]) under a different definition of "tail field" generated by
  `sigma_functions` (martingaleTheory).
 *)
Theorem Kolmogorov_0_1_Law :
    !p E. prob_space p /\
          (!n. (E n) IN events p) /\ indep_events p E UNIV ==>
          !e. e IN subsets (tail_algebra p E) ==> (prob p e = 0) \/ (prob p e = 1)
Proof
    RW_TAC std_ss [tail_algebra_def, subsets_def, IN_BIGINTER_IMAGE, IN_UNIV]
 >> Know `e IN events p`
 >- (fs [indep_events_def] \\
     POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [FROM_0]) o (Q.SPEC `0`)) \\
     Suff `subsets (sigma (p_space p) (IMAGE E UNIV)) SUBSET events p`
     >- METIS_TAC [SUBSET_DEF] \\
     MATCH_MP_TAC SIGMA_SUBSET_EVENTS >> art [] \\
     RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV] >> art []) >> DISCH_TAC
 >> Know `!n. indep_events p (\x. if x IN (count n) then E x else e)
                             (n INSERT count n)`
 >- (GEN_TAC >> Cases_on `n = 0`
     >- (ASM_SIMP_TAC std_ss [COUNT_ZERO, indep_events_def, IN_SING, NOT_IN_EMPTY] \\
         RW_TAC std_ss [SUBSET_DEF, IN_SING, NOT_IN_EMPTY] \\
         Know `N = {0}`
         >- (RW_TAC std_ss [GSYM UNIQUE_MEMBER_SING] \\
             fs [GSYM MEMBER_NOT_EMPTY] >> RES_TAC >> fs []) >> Rewr' \\
         SIMP_TAC std_ss [IMAGE_SING, BIGINTER_SING, EXTREAL_PROD_IMAGE_SING]) \\
    `0 < n` by RW_TAC arith_ss [] \\
     MATCH_MP_TAC INDEP_FAMILIES_SIGMA_lemma2 \\
     Q.EXISTS_TAC `from n` >> art [UNION_FROM_COUNT, DISJOINT_FROM_COUNT] \\
     CONJ_TAC >- (fs [indep_events_def] \\
                  RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV] >> art []) \\
     CONJ_TAC >- (RW_TAC arith_ss [IN_FROM]) \\
     PROVE_TAC [COUNT_NOT_EMPTY]) >> DISCH_TAC
 >> Know `indep_events p (\x. if EVEN x then E (DIV2 x) else e)
                         (1 INSERT {2 * n | T})`
 >- (  RW_TAC std_ss [indep_events_def, IN_INSERT, GSPECIFICATION] \\
       Cases_on `1 NOTIN N` (* easier case *)
       >- (`~EVEN 1` by RW_TAC arith_ss [] \\
           `N SUBSET {2 * n | T}` by ASM_SET_TAC [] \\
           Know `!x. x IN N ==> EVEN x`
           >- (POP_ASSUM MP_TAC >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION] \\
               `?n. x = 2 * n` by PROVE_TAC [] >> POP_ORW \\
               REWRITE_TAC [EVEN_DOUBLE]) >> DISCH_TAC \\
           Know `IMAGE (\x. if EVEN x then E (DIV2 x) else e) N = IMAGE (E o DIV2) N`
           >- (RW_TAC std_ss [Once EXTENSION, IN_IMAGE, o_DEF] \\
               EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
               [ (* goal 3.1 (of 2) *)
                `EVEN x'` by PROVE_TAC [] >> fs [] \\
                `?v. x' = 2 * v` by PROVE_TAC [EVEN_ODD_EXISTS] \\
                 Q.EXISTS_TAC `2 * v` >> PROVE_TAC [],
                 (* goal 3.2 (of 2) *)
                `EVEN x'` by PROVE_TAC [] \\
                 Q.EXISTS_TAC `x'` >> art [] ]) >> Rewr' \\
           Know `PI (prob p o (\x. if EVEN x then E (DIV2 x) else e)) N =
                 PI ((prob p o E) o DIV2) N`
           >- (irule EXTREAL_PROD_IMAGE_EQ >> RW_TAC std_ss [o_DEF]) >> Rewr' \\
          `IMAGE (E o DIV2) N = IMAGE E (IMAGE DIV2 N)`
             by PROVE_TAC [IMAGE_IMAGE] >> POP_ORW \\
           Know `PI ((prob p o E) o DIV2) N = PI (prob p o E) (IMAGE DIV2 N)`
           >- (MATCH_MP_TAC EQ_SYM >> irule EXTREAL_PROD_IMAGE_IMAGE >> art [] \\
               MATCH_MP_TAC INJ_IMAGE >> Q.EXISTS_TAC `IMAGE DIV2 N` \\
               RW_TAC std_ss [INJ_DEF, GSPECIFICATION, IN_IMAGE]
               >- (Q.EXISTS_TAC `x` >> art []) \\
              `(?v1. x = 2 * v1) /\ (?v2. y = 2 * v2)` by PROVE_TAC [EVEN_ODD_EXISTS] \\
               fs [DIV2_DOUBLE]) >> Rewr' \\
           fs [indep_events_def]) \\
       fs [] (* harder case: `1 IN N` *) \\
       Q.ABBREV_TAC `N' = N DELETE 1` \\
      `N' SUBSET N` by ASM_SET_TAC [] \\
      `1 NOTIN N'` by ASM_SET_TAC [] \\
      `N' DELETE 1 = N'` by PROVE_TAC [DELETE_NON_ELEMENT] \\
      `N = 1 INSERT N'` by ASM_SET_TAC [] >> POP_ORW \\
       ASM_SIMP_TAC std_ss [IMAGE_INSERT] \\
      `~EVEN 1` by RW_TAC arith_ss [] \\
      `N' SUBSET {2 * n | T}` by ASM_SET_TAC [] \\
       Know `!x. x IN N'==> EVEN x`
       >- (POP_ASSUM MP_TAC >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION] \\
           `?n. x = 2 * n` by PROVE_TAC [] >> POP_ORW \\
           REWRITE_TAC [EVEN_DOUBLE]) >> DISCH_TAC \\
       Know `IMAGE (\x. if EVEN x then E (DIV2 x) else e) N' = IMAGE (E o DIV2) N'`
       >- (RW_TAC std_ss [Once EXTENSION, IN_IMAGE, o_DEF] \\
           EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
           [ (* goal 3.1 (of 2) *)
             `EVEN x'` by PROVE_TAC [] >> fs [] \\
             `?v. x' = 2 * v` by PROVE_TAC [EVEN_ODD_EXISTS] \\
              Q.EXISTS_TAC `2 * v` >> PROVE_TAC [],
              (* goal 3.2 (of 2) *)
             `EVEN x'` by PROVE_TAC [] \\
              Q.EXISTS_TAC `x'` >> art [] ]) >> Rewr' \\
      `FINITE N'` by PROVE_TAC [SUBSET_FINITE_I] \\
       ASM_SIMP_TAC std_ss [EXTREAL_PROD_IMAGE_PROPERTY] \\
       Know `PI (prob p o (\x. if EVEN x then E (DIV2 x) else e)) N' = PI ((prob p o E) o DIV2) N'`
       >- (irule EXTREAL_PROD_IMAGE_EQ \\
           RW_TAC std_ss [o_DEF]) >> Rewr' \\
      `IMAGE (E o DIV2) N' = IMAGE E (IMAGE DIV2 N')` by PROVE_TAC [IMAGE_IMAGE] >> POP_ORW \\
       Know `PI ((prob p o E) o DIV2) N' = PI (prob p o E) (IMAGE DIV2 N')`
       >- (MATCH_MP_TAC EQ_SYM >> irule EXTREAL_PROD_IMAGE_IMAGE >> art [] \\
           MATCH_MP_TAC INJ_IMAGE >> Q.EXISTS_TAC `IMAGE DIV2 N'` \\
           RW_TAC std_ss [INJ_DEF, GSPECIFICATION, IN_IMAGE]
           >- (Q.EXISTS_TAC `x` >> art []) \\
          `(?v1. x = 2 * v1) /\ (?v2. y = 2 * v2)` by PROVE_TAC [EVEN_ODD_EXISTS] \\
           fs [DIV2_DOUBLE]) >> Rewr' \\
    (* now applying indep_events_def *)
       Q.ABBREV_TAC `n = SUC (MAX_SET N')` \\
       Q.PAT_X_ASSUM `!n. indep_events p _ (n INSERT count n)`
         (STRIP_ASSUME_TAC o (REWRITE_RULE [indep_events_def]) o (Q.SPEC `n`)) \\
       POP_ASSUM (MP_TAC o (Q.SPEC `n INSERT (IMAGE DIV2 N')`)) \\
       Know `!x. x IN N' ==> DIV2 x < n`
       >- (rpt STRIP_TAC >> Q.UNABBREV_TAC `n` \\
           MATCH_MP_TAC LESS_EQ_LESS_TRANS \\
           Q.EXISTS_TAC `MAX_SET N'` >> SIMP_TAC arith_ss [] \\
           MATCH_MP_TAC LESS_EQ_TRANS \\
           Q.EXISTS_TAC `x` >> RW_TAC std_ss [in_max_set] \\
           REWRITE_TAC [DIV2_def] >> MATCH_MP_TAC DIV_LESS_EQ >> RW_TAC arith_ss []) \\
       DISCH_TAC \\
       Know `n INSERT (IMAGE DIV2 N') SUBSET (n INSERT (count n))`
       >- (RW_TAC std_ss [SUBSET_DEF, IN_COUNT, IN_INSERT, IN_IMAGE] \\
           DISJ2_TAC >> PROVE_TAC []) \\
       Know `~(n INSERT (IMAGE DIV2 N') = {})`
       >- (RW_TAC std_ss [Once EXTENSION, IN_INSERT, NOT_IN_EMPTY] \\
           Q.EXISTS_TAC `n` >> DISJ1_TAC >> REWRITE_TAC []) \\
       Know `FINITE (n INSERT (IMAGE DIV2 N'))`
       >- (REWRITE_TAC [FINITE_INSERT] \\
           MATCH_MP_TAC IMAGE_FINITE >> art []) \\
       RW_TAC std_ss [] >> POP_ASSUM MP_TAC \\
       SIMP_TAC arith_ss [IMAGE_INSERT] \\
       Know `IMAGE (\x. if x < n then E x else e) (IMAGE DIV2 N') = IMAGE (E o DIV2) N'`
       >- (RW_TAC arith_ss [Once EXTENSION, IN_IMAGE, o_DEF] \\
           EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
           [ (* goal 3.1 (of 2) *)
            `x' < n` by PROVE_TAC [] >> fs [] \\
             Q.EXISTS_TAC `x''` >> art [],
             (* goal 3.2 (of 2) *)
            `EVEN x'` by PROVE_TAC [] \\
             Q.EXISTS_TAC `DIV2 x'` \\
             reverse CONJ_TAC >- (Q.EXISTS_TAC `x'` >> art []) \\
             Suff `DIV2 x' < n` >- ASM_SIMP_TAC std_ss [] \\
             PROVE_TAC [] ]) >> Rewr' \\
      `IMAGE (E o DIV2) N' = IMAGE E (IMAGE DIV2 N')` by PROVE_TAC [IMAGE_IMAGE] \\
       POP_ORW >> Rewr' \\
       Know `n NOTIN (IMAGE DIV2 N')`
       >- (RW_TAC std_ss [IN_IMAGE] \\
           Suff `x IN N' ==> n <> DIV2 x` >- METIS_TAC [] >> DISCH_TAC \\
           Suff `DIV2 x < n` >- SIMP_TAC arith_ss [] \\
           PROVE_TAC []) >> DISCH_TAC \\
      `(IMAGE DIV2 N') DELETE n = IMAGE DIV2 N'` by PROVE_TAC [DELETE_NON_ELEMENT] \\
      `FINITE (IMAGE DIV2 N')` by PROVE_TAC [FINITE_INSERT] \\
       RW_TAC std_ss [EXTREAL_PROD_IMAGE_PROPERTY] \\
       Suff `PI (prob p o (\x. if x < n then E x else e)) (IMAGE DIV2 N') =
             PI (prob p o E) (IMAGE DIV2 N')` >- RW_TAC std_ss [] \\
       irule EXTREAL_PROD_IMAGE_EQ >> RW_TAC std_ss [IN_IMAGE] \\
       Suff `DIV2 x' < n` >- PROVE_TAC [] \\
       PROVE_TAC [] ) >> DISCH_TAC
 (* applying INDEP_FAMILIES_SIGMA_lemma1 *)
 >> Know `!a. a IN subsets
                     (sigma (p_space p)
                            (IMAGE (\x. if EVEN x then E (DIV2 x) else e) {2 * n | T}))
          ==> indep p ((\x. if EVEN x then E (DIV2 x) else e) 1) a`
 >- (rpt STRIP_TAC >> irule INDEP_FAMILIES_SIGMA_lemma1 >> art [] \\
     Q.EXISTS_TAC `{2 * n | T}` >> art [] \\
    `ODD 1` by RW_TAC arith_ss [] \\
     CONJ_TAC >- (RW_TAC arith_ss [GSPECIFICATION]) \\
     SIMP_TAC std_ss [IMAGE_INSERT] \\
     Know `IMAGE (\x. if EVEN x then E (DIV2 x) else e) {2 * n | T} = IMAGE E UNIV`
     >- (RW_TAC arith_ss [Once EXTENSION, IN_IMAGE, IN_UNIV, GSPECIFICATION] \\
         EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
          `EVEN x'` by PROVE_TAC [EVEN_DOUBLE] >> fs [] \\
           Q.EXISTS_TAC `n` >> REWRITE_TAC [],
           (* goal 2 (of 2) *)
           POP_ORW >> Q.EXISTS_TAC `2 * x'` >> SIMP_TAC std_ss [EVEN_DOUBLE, DIV2_DOUBLE] \\
           Q.EXISTS_TAC `x'` >> REWRITE_TAC [] ]) >> Rewr' \\
    RW_TAC std_ss [SUBSET_DEF, IN_INSERT] >- art [] \\
    fs [indep_events_def, IN_IMAGE, IN_UNIV])
 >> Know `IMAGE (\x. if EVEN x then E (DIV2 x) else e) {2 * n | T} = IMAGE E UNIV`
 >- (RW_TAC arith_ss [Once EXTENSION, IN_IMAGE, IN_UNIV, GSPECIFICATION] \\
     EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
      `EVEN x'` by PROVE_TAC [EVEN_DOUBLE] >> fs [] \\
       Q.EXISTS_TAC `n` >> REWRITE_TAC [],
       (* goal 2 (of 2) *)
       POP_ORW >> Q.EXISTS_TAC `2 * x'` >> SIMP_TAC std_ss [EVEN_DOUBLE, DIV2_DOUBLE] \\
       Q.EXISTS_TAC `x'` >> REWRITE_TAC [] ]) >> Rewr'
 >> `ODD 1` by RW_TAC arith_ss []
 >> `~(EVEN 1)` by PROVE_TAC [EVEN_ODD] >> SIMP_TAC arith_ss [] >> DISCH_TAC
 >> Know `e IN subsets (sigma (p_space p) (IMAGE E univ(:num)))`
 >- (Suff `subsets (sigma (p_space p) (IMAGE E (from n))) SUBSET
           subsets (sigma (p_space p) (IMAGE E univ(:num)))` >- METIS_TAC [SUBSET_DEF] \\
     MATCH_MP_TAC SIGMA_MONOTONE \\
     MATCH_MP_TAC IMAGE_SUBSET >> REWRITE_TAC [SUBSET_UNIV]) >> DISCH_TAC
 >> `indep p e e` by PROVE_TAC []
 >> METIS_TAC [INDEP_REFL]
QED

(******************************************************************************)
(*  noncorrelation of r.v.'s [2, p.107-108]                                   *)
(******************************************************************************)

(* "The requirement of finite second moments seems unnecessary, but it does ensure the
    finiteness of E[XY] (Cauchy-Schwarz inequality!) as well as that of E[X] and E[Y]."
   [2, p.107] *)
val uncorrelated_def = Define
   `uncorrelated p X Y <=>
      finite_second_moments p X /\ finite_second_moments p Y /\
      (expectation p (\s. X s * Y s) = expectation p X * expectation p Y)`;

val uncorrelated_vars_def = Define
   `uncorrelated_vars p X J <=>
      !i j. i IN J /\ j IN J /\ i <> j ==> uncorrelated p (X i) (X j)`;

val orthogonal_def = Define
   `orthogonal p X Y <=>
      finite_second_moments p X /\ finite_second_moments p Y /\
      (expectation p (\s. X s * Y s) = 0)`;

val orthogonal_vars_def = Define
   `orthogonal_vars p X J <=>
      !i j. i IN J /\ j IN J /\ i <> j ==> orthogonal p (X i) (X j)`;

val covariance_def = Define
   `covariance p X Y =
      expectation p (\x. (X x - expectation p X) * (Y x - expectation p Y))`;

val covariance_self = store_thm
  ("covariance_self", ``!p X. covariance p X X = variance p X``,
    RW_TAC std_ss [variance_alt, covariance_def, pow_2]);

(* i.e. `covariance p X Y` is zero if X and Y are uncorelated *)
Theorem uncorrelated_thm :
    !p X Y. prob_space p /\ real_random_variable X p /\ real_random_variable Y p /\
            uncorrelated p X Y ==>
           (expectation p (\s. (X s - expectation p X) * (Y s - expectation p Y)) = 0)
Proof
    RW_TAC std_ss [uncorrelated_def] (* 2 subgoals *)
 >> `expectation p X <> PosInf /\ expectation p X <> NegInf /\
     expectation p Y <> PosInf /\ expectation p Y <> NegInf`
      by PROVE_TAC [finite_second_moments_imp_finite_expectation]
 >> `!s. X s <> PosInf /\ X s <> NegInf /\ Y s <> PosInf /\ Y s <> NegInf`
      by PROVE_TAC [real_random_variable_def]
 >> `?c. expectation p X = Normal c` by PROVE_TAC [extreal_cases]
 >> `?d. expectation p Y = Normal d` by PROVE_TAC [extreal_cases] >> art []
 >> Know `!s. (X s - Normal c) * (Y s - Normal d) =
              (\x. (X x) * (Y x)) s +
              (\x. (Normal c * Normal d - Normal c * (Y x) - Normal d * (X x))) s`
 >- (GEN_TAC >> BETA_TAC \\
    `?a. X s = Normal a` by PROVE_TAC [extreal_cases] >> POP_ORW \\
    `?b. Y s = Normal b` by PROVE_TAC [extreal_cases] >> POP_ORW \\
     art [extreal_sub_def, extreal_add_def, extreal_mul_def, extreal_11] \\
     REAL_ARITH_TAC) >> Rewr'
 >> `integrable p (\x. X x pow 2) /\ integrable p (\x. Y x pow 2)`
       by METIS_TAC [finite_second_moments_eq_integrable_square]
 >> Know `integrable p (\x. X x * Y x)`
 >- (MATCH_MP_TAC integrable_bounded \\
     Q.EXISTS_TAC `\x. Normal (1 / 2) * ((X x) pow 2 + (Y x) pow 2)` \\
     fs [prob_space_def, p_space_def, events_def, real_random_variable] \\
     rpt STRIP_TAC >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
      `(\x. Normal (1 / 2) * ((X x) pow 2 + (Y x) pow 2)) =
       (\x. Normal (1 / 2) * (\x. (X x) pow 2 + (Y x) pow 2) x)` by METIS_TAC [] >> POP_ORW \\
       MATCH_MP_TAC integrable_cmul >> art [] \\
      `(\x. (X x) pow 2 + (Y x) pow 2) = (\x. (\x. (X x) pow 2) x + (\x. (Y x) pow 2) x)`
         by METIS_TAC [] >> POP_ORW \\
       MATCH_MP_TAC integrable_add >> RW_TAC std_ss [pow_2] \\
       DISJ1_TAC >> CONJ_TAC >| (* 2 subgoals *)
       [ `?r. X x = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
         REWRITE_TAC [extreal_mul_def, extreal_not_infty],
         `?r. Y x = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
         REWRITE_TAC [extreal_mul_def, extreal_not_infty] ],
       (* goal 2 (of 3) *)
       MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL \\
       qexistsl_tac [‘X’, ‘Y’] >> fs [measure_space_def],
       (* goal 3 (of 3) *)
       REWRITE_TAC [abs_le_half_pow2] ]) >> DISCH_TAC
 >> `integrable p X /\ integrable p Y` by METIS_TAC [integrable_from_square]
 >> FULL_SIMP_TAC pure_ss [expectation_def, prob_space_def, p_space_def]
 (* applying "integral_add" *)
 >> Know `integral p (\s. (\x. X x * Y x) s +
                          (\x. Normal c * Normal d - Normal c * Y x - Normal d * X x) s) =
          integral p (\x. X x * Y x) +
          integral p (\x. Normal c * Normal d - Normal c * Y x - Normal d * X x)`
 >- (MATCH_MP_TAC integral_add \\
     RW_TAC std_ss [extreal_mul_def, extreal_not_infty] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
      `(\x. Normal (c * d) - Normal c * Y x - Normal d * X x) =
       (\x. (\x. Normal (c * d) - Normal c * Y x) x - (\x. Normal d * X x) x)`
        by METIS_TAC [] >> POP_ORW \\
       MATCH_MP_TAC integrable_sub >> RW_TAC std_ss [integrable_cmul] >| (* 3 subgoals *)
       [ (* goal 1.1 (of 3) *)
        `(\x. Normal (c * d) - Normal c * Y x) =
         (\x. (\x. Normal (c * d)) x - (\x. Normal c * Y x) x)` by METIS_TAC [] >> POP_ORW \\
         MATCH_MP_TAC integrable_sub >> RW_TAC std_ss [integrable_cmul] >| (* 2 subgoals *)
         [ (* goal 1.1.1 (of 2) *)
           MATCH_MP_TAC integrable_const >> art [extreal_of_num_def, lt_infty],
           (* goal 1.1.2 (of 2) *)
          `?r. Y x = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
           REWRITE_TAC [extreal_mul_def, extreal_not_infty] ],
         (* goal 1.2 (of 3) *)
        `?r. Y x = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
         REWRITE_TAC [extreal_mul_def, extreal_sub_def, extreal_not_infty],
         (* goal 1.3 (of 3) *)
        `?r. X x = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
         REWRITE_TAC [extreal_mul_def, extreal_not_infty] ],
       (* goal 2 (of 2) *)
       DISJ1_TAC >> CONJ_TAC >| (* 2 subgoals *)
       [ (* goal 2.1 (of 2) *)
        `?a. X x = Normal a` by PROVE_TAC [extreal_cases] >> POP_ORW \\
        `?b. Y x = Normal b` by PROVE_TAC [extreal_cases] >> POP_ORW \\
         REWRITE_TAC [extreal_mul_def, extreal_not_infty],
         (* goal 2.2 (of 2) *)
        `?a. X x = Normal a` by PROVE_TAC [extreal_cases] >> POP_ORW \\
        `?b. Y x = Normal b` by PROVE_TAC [extreal_cases] >> POP_ORW \\
         REWRITE_TAC [extreal_mul_def, extreal_sub_def, extreal_not_infty] ] ]) >> Rewr'
 >> Know `(\x. Normal c * Normal d - Normal c * Y x - Normal d * X x) =
          (\x. (\x. Normal c * Normal d) x + (\x. (- Normal c) * Y x + (- Normal d) * X x) x)`
 >- (FUN_EQ_TAC >> GEN_TAC >> BETA_TAC \\
    `?a. X x = Normal a` by PROVE_TAC [extreal_cases] >> POP_ORW \\
    `?b. Y x = Normal b` by PROVE_TAC [extreal_cases] >> POP_ORW \\
     SIMP_TAC real_ss [extreal_mul_def, extreal_ainv_def, extreal_add_def, extreal_sub_def,
                       extreal_11] \\
     REAL_ARITH_TAC) >> Rewr'
 >> Know `integral p (\x. (\x. Normal c * Normal d) x + (\x. -Normal c * Y x + -Normal d * X x) x) =
          integral p (\x. Normal c * Normal d) + integral p (\x. -Normal c * Y x + -Normal d * X x)`
 >- (MATCH_MP_TAC integral_add \\
     RW_TAC std_ss [extreal_ainv_def, extreal_mul_def, extreal_not_infty] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       MATCH_MP_TAC integrable_const >> art [extreal_of_num_def, lt_infty],
       (* goal 2 (of 3) *)
      `(\x. Normal (-c) * Y x + Normal (-d) * X x) =
       (\x. (\x. Normal (-c) * Y x) x + (\x. Normal (-d) * X x) x)`
         by METIS_TAC [] >> POP_ORW \\
       MATCH_MP_TAC integrable_add >> RW_TAC std_ss [integrable_cmul] \\
       DISJ1_TAC >> CONJ_TAC >| (* 2 subgoals *)
       [ (* goal 2.1 (of 2) *)
        `?r. Y x = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
          REWRITE_TAC [extreal_mul_def, extreal_not_infty],
         (* goal 2.2 (of 2) *)
        `?r. X x = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
          REWRITE_TAC [extreal_mul_def, extreal_not_infty] ],
       (* goal 3 (of 3) *)
       DISJ1_TAC \\
      `?a. X x = Normal a` by PROVE_TAC [extreal_cases] >> POP_ORW \\
      `?b. Y x = Normal b` by PROVE_TAC [extreal_cases] >> POP_ORW \\
       RW_TAC std_ss [extreal_add_def, extreal_mul_def, extreal_not_infty] ]) >> Rewr'
 >> Know `integral p (\x. Normal c * Normal d) = Normal c * Normal d`
 >- (REWRITE_TAC [GSYM expectation_def, extreal_mul_def] \\
     MATCH_MP_TAC expectation_const >> art [prob_space_def, p_space_def]) >> Rewr'
 >> `(\x. -Normal c * Y x + -Normal d * X x) =
     (\x. (\x. -Normal c * Y x) x + (\x. -Normal d * X x) x)` by METIS_TAC [] >> POP_ORW
 >> Know `integral p (\x. (\x. -Normal c * Y x) x + (\x. -Normal d * X x) x) =
          integral p (\x. -Normal c * Y x) + integral p (\x. -Normal d * X x)`
 >- (MATCH_MP_TAC integral_add >> art [extreal_ainv_def] \\
     RW_TAC std_ss [integrable_cmul] \\
     DISJ1_TAC >> CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
      `?r. Y x = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
       REWRITE_TAC [extreal_mul_def, extreal_not_infty],
       (* goal 2.2 (of 2) *)
      `?r. X x = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
       REWRITE_TAC [extreal_mul_def, extreal_not_infty] ]) >> Rewr'
 >> Know `integral p (\x. -Normal c * Y x) = -Normal c * integral p Y`
 >- (REWRITE_TAC [extreal_ainv_def] \\
     MATCH_MP_TAC integral_cmul >> art []) >> Rewr'
 >> Know `integral p (\x. -Normal d * X x) = -Normal d * integral p X`
 >- (REWRITE_TAC [extreal_ainv_def] \\
     MATCH_MP_TAC integral_cmul >> art []) >> Rewr'
 >> art [extreal_ainv_def, extreal_mul_def, extreal_add_def, extreal_11, extreal_of_num_def]
 >> REAL_ARITH_TAC
QED

val uncorrelated_covariance = store_thm
  ("uncorrelated_covariance",
  ``!p X Y. prob_space p /\ real_random_variable X p /\ real_random_variable Y p /\
            uncorrelated p X Y ==> (covariance p X Y = 0)``,
    RW_TAC std_ss [covariance_def]
 >> MATCH_MP_TAC uncorrelated_thm >> art []);

Theorem uncorrelated_orthogonal :
    !p X Y. prob_space p /\ real_random_variable X p /\ real_random_variable Y p /\
            (expectation p X = 0) /\ (expectation p Y = 0) ==>
            (uncorrelated p X Y <=> orthogonal p X Y)
Proof
    rw [orthogonal_def, uncorrelated_def]
QED

(* Fundamental relation of uncorrelated r.v.'s [2, p.108] *)
Theorem variance_sum :
    !p X J. prob_space p /\ FINITE J /\ (!i. i IN J ==> real_random_variable (X i) p) /\
            uncorrelated_vars p X J ==>
           (variance p (\x. SIGMA (\n. X n x) J) = SIGMA (\n. variance p (X n)) J)
Proof
    RW_TAC std_ss [uncorrelated_vars_def, variance_alt]
 >> Cases_on `J = {}`
 >- (Know `expectation p (\x. 0) = 0`
     >- (REWRITE_TAC [extreal_of_num_def] \\
         MATCH_MP_TAC expectation_const >> art []) \\
     RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, sub_rzero, pow_2, mul_rzero])
 >> Cases_on `SING J`
 >- (fs [SING_DEF] >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_SING] >> METIS_TAC [])
 (* LHS: applying integral_sum *)
 >> Know `expectation p (\x. SIGMA (\n. X n x) J) = SIGMA (\n. expectation p (X n)) J`
 >- (fs [expectation_def, prob_space_def, p_space_def, real_random_variable_def,
         random_variable_def, events_def] \\
     MATCH_MP_TAC integral_sum >> RW_TAC std_ss [] \\
     MATCH_MP_TAC finite_second_moments_imp_integrable \\
     fs [uncorrelated_def, prob_space_def, p_space_def, real_random_variable_def,
         random_variable_def, events_def] \\
    `?j. i <> j /\ j IN J` by ASM_SET_TAC [SING_DEF] >> METIS_TAC [])
 >> Rewr'
 >> Know `!n. n IN J ==> finite_second_moments p (X n)`
 >- (fs [uncorrelated_def] >> RW_TAC std_ss [] \\
    `?n'. n <> n' /\ n' IN J` by ASM_SET_TAC [SING_DEF] >> METIS_TAC [])
 >> DISCH_TAC
 >> `!n. n IN J ==> expectation p (X n) <> PosInf /\ expectation p (X n) <> NegInf`
     by METIS_TAC [finite_second_moments_imp_finite_expectation]
 >> Know `!i x. i IN J ==> X i x <> PosInf /\ X i x <> NegInf`
 >- fs [real_random_variable_def] >> DISCH_TAC
 (* LHS: applying EXTREAL_SUM_IMAGE_SUB *)
 >> Know `!x. SIGMA (\n. X n x) J - SIGMA (\n. expectation p (X n)) J =
              SIGMA (\n. (\n. X n x) n - (\n. expectation p (X n)) n) J`
 >- (GEN_TAC >> MATCH_MP_TAC EQ_SYM \\
     irule EXTREAL_SUM_IMAGE_SUB >> art [] >> DISJ1_TAC >> RW_TAC std_ss [])
 >> Rewr' >> BETA_TAC
 (* LHS: applying EXTREAL_SUM_IMAGE_POW *)
 >> Know `!x. (SIGMA (\n. X n x - expectation p (X n)) J) pow 2 =
              SIGMA (\(i,j). (\n. X n x - expectation p (X n)) i *
                             (\n. X n x - expectation p (X n)) j)
                    (J CROSS J)`
 >- (GEN_TAC \\
     irule EXTREAL_SUM_IMAGE_POW >> RW_TAC std_ss [] \\ (* 2 subgoals, same tactics *)
    `?a. X x' x = Normal a` by METIS_TAC [extreal_cases] >> POP_ORW \\
    `?b. expectation p (X x') = Normal b` by METIS_TAC [extreal_cases] >> POP_ORW \\
     REWRITE_TAC [extreal_sub_def, extreal_not_infty]) >> Rewr'
 (* LHS: applying EXTREAL_SUM_IMAGE_DISJOINT_UNION *)
 >> Q.ABBREV_TAC `A = {(i,i) | i IN J}`
 >> Q.ABBREV_TAC `B = {(i,j) | i IN J /\ j IN J /\ i <> j}`
 >> Know `J CROSS J = A UNION B`
 >- (Q.UNABBREV_TAC `A` >> Q.UNABBREV_TAC `B` \\
     RW_TAC std_ss [IN_CROSS, Once EXTENSION] >> Cases_on `x` \\
     RW_TAC std_ss [Once EXTENSION, GSPECIFICATION, IN_UNION] \\
     EQ_TAC >> rpt STRIP_TAC >| (* 5 subgoals *)
     [ (* goal 1 (of 5) *)
       Cases_on `r = q` >- (DISJ1_TAC >> art []) \\
       DISJ2_TAC >> Q.EXISTS_TAC `(q,r)` >> RW_TAC std_ss [],
       (* goal 2 (of 5) *) art [],
       (* goal 3 (of 5) *) art [],
       (* goal 4 (of 5) *) Cases_on `x` >> fs [],
       (* goal 5 (of 5) *) Cases_on `x` >> fs [] ]) >> DISCH_TAC
 >> Know `DISJOINT A B`
 >- (Q.UNABBREV_TAC `A` >> Q.UNABBREV_TAC `B` \\
     RW_TAC std_ss [DISJOINT_DEF, Once EXTENSION, NOT_IN_EMPTY, GSPECIFICATION, IN_INTER] \\
     Cases_on `x` >> Cases_on `q = r`
     >- (DISJ2_TAC >> GEN_TAC >> Cases_on `x'` >> RW_TAC std_ss [] \\
         METIS_TAC []) \\
     DISJ1_TAC >> GEN_TAC >> RW_TAC std_ss [] >> METIS_TAC []) >> DISCH_TAC
 >> Know `!x. (SIGMA (\(i,j). (\n. X n x - expectation p (X n)) i *
                              (\n. X n x - expectation p (X n)) j) (J CROSS J) =
               SIGMA (\(i,j). (\n. X n x - expectation p (X n)) i *
                              (\n. X n x - expectation p (X n)) j) A +
               SIGMA (\(i,j). (\n. X n x - expectation p (X n)) i *
                              (\n. X n x - expectation p (X n)) j) B)`
 >- (GEN_TAC >> art [] >> irule EXTREAL_SUM_IMAGE_DISJOINT_UNION \\
    `FINITE (J CROSS J)` by PROVE_TAC [FINITE_CROSS] \\
    `A SUBSET (J CROSS J) /\ B SUBSET (J CROSS J)` by ASM_SET_TAC [] \\
    `FINITE A /\ FINITE B` by PROVE_TAC [SUBSET_FINITE] \\
     Q.PAT_X_ASSUM `J CROSS J = A UNION B` (art o wrap o SYM) \\
     DISJ2_TAC >> RW_TAC std_ss [IN_CROSS] >> Cases_on `x'` \\
     FULL_SIMP_TAC std_ss [] \\
    `?a. X q x = Normal a` by PROVE_TAC [extreal_cases] >> POP_ORW \\
    `?b. X r x = Normal b` by PROVE_TAC [extreal_cases] >> POP_ORW \\
    `?c. expectation p (X q) = Normal c` by PROVE_TAC [extreal_cases] >> POP_ORW \\
    `?d. expectation p (X r) = Normal d` by PROVE_TAC [extreal_cases] >> POP_ORW \\
     REWRITE_TAC [extreal_sub_def, extreal_mul_def, extreal_not_infty]) >> Rewr'
 (* LHS: applying EXTREAL_SUM_IMAGE_IMAGE *)
 >> Know `A = IMAGE (\x. (x,x)) J`
 >- RW_TAC std_ss [Abbr ‘A’, Once EXTENSION, IN_IMAGE, GSPECIFICATION]
 >> DISCH_TAC
 >> Know `!x. (SIGMA (\(i,j). (\n. X n x - expectation p (X n)) i *
                              (\n. X n x - expectation p (X n)) j) A =
               SIGMA ((\(i,j). (\n. X n x - expectation p (X n)) i *
                               (\n. X n x - expectation p (X n)) j) o (\x. (x,x))) J)`
 >- (GEN_TAC >> art [] >> irule EXTREAL_SUM_IMAGE_IMAGE >> art [] \\
     reverse CONJ_TAC
     >- (MATCH_MP_TAC INJ_IMAGE >> Q.EXISTS_TAC `J CROSS J` \\
         Q.PAT_X_ASSUM `J CROSS J = A UNION B` K_TAC \\
         RW_TAC std_ss [INJ_DEF, IN_IMAGE, IN_CROSS]) \\
     Q.PAT_X_ASSUM `A = IMAGE (\x. (x,x)) J` (REWRITE_TAC o wrap o SYM) \\
     DISJ2_TAC >> RW_TAC std_ss [] >> Cases_on `x'` >> SIMP_TAC std_ss [] \\
    `A SUBSET (J CROSS J) /\ B SUBSET (J CROSS J)` by ASM_SET_TAC [] \\
     Know `q IN J /\ r IN J`
     >- (CONJ_TAC >> `(q,r) IN (J CROSS J)` by PROVE_TAC [SUBSET_DEF] \\
         POP_ASSUM MP_TAC >> SIMP_TAC std_ss [IN_CROSS]) >> STRIP_TAC \\
    `?a. X q x = Normal a` by PROVE_TAC [extreal_cases] >> POP_ORW \\
    `?b. X r x = Normal b` by PROVE_TAC [extreal_cases] >> POP_ORW \\
    `?c. expectation p (X q) = Normal c` by PROVE_TAC [extreal_cases] >> POP_ORW \\
    `?d. expectation p (X r) = Normal d` by PROVE_TAC [extreal_cases] >> POP_ORW \\
     REWRITE_TAC [extreal_sub_def, extreal_mul_def, extreal_not_infty]) >> Rewr'
 >> SIMP_TAC std_ss [o_DEF, GSYM pow_2]
 (* an important shared result *)
 >> Know `!q r. q IN J /\ r IN J ==>
                integrable p (\x. (X q x - expectation p (X q)) *
                                  (X r x - expectation p (X r)))`
 >- (rpt STRIP_TAC \\
     Q.ABBREV_TAC `E1 = expectation p (X q)` \\
     Q.ABBREV_TAC `E2 = expectation p (X r)` \\
  (* integrable p (\x. (X q x - E1) * (X r x - E2)) *)
     MATCH_MP_TAC integrable_bounded \\
     Q.EXISTS_TAC `\x. Normal (1 / 2) * ((X q x - E1) pow 2 + (X r x - E2) pow 2)` \\
     CONJ_TAC >- fs [prob_space_def] \\
     CONJ_TAC
     >- (`(\x. Normal (1 / 2) * ((X q x - E1) pow 2 + (X r x - E2) pow 2)) =
          (\x. Normal (1 / 2) * (\x. (X q x - E1) pow 2 + (X r x - E2) pow 2) x)`
           by METIS_TAC [] >> POP_ORW \\
         MATCH_MP_TAC integrable_cmul >> CONJ_TAC >- fs [prob_space_def] \\
        `!x. (X q x - E1) pow 2 + (X r x - E2) pow 2 =
             (\x. (X q x - E1) pow 2) x + (\x. (X r x - E2) pow 2) x`
           by METIS_TAC [] >> POP_ORW \\
         MATCH_MP_TAC integrable_add \\
         CONJ_TAC >- fs [prob_space_def] \\
        `?e1. E1 = Normal e1` by PROVE_TAC [extreal_cases] >> POP_ORW \\
        `?e2. E2 = Normal e2` by PROVE_TAC [extreal_cases] >> POP_ORW \\
         REWRITE_TAC [CONJ_ASSOC] \\
         CONJ_TAC >- METIS_TAC [finite_second_moments_eq_integrable_squares] \\
         GEN_TAC >> DISCH_TAC >> DISJ1_TAC >> BETA_TAC \\
         CONJ_TAC >> MATCH_MP_TAC pos_not_neginf >> REWRITE_TAC [le_pow2]) \\
     CONJ_TAC
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES \\
         qexistsl_tac [`\x. X q x - E1`, `\x. X r x - E2`] \\
         fs [prob_space_def, measure_space_def, space_def, p_space_def, events_def] \\
         CONJ_TAC
         >- (`!x. X q x - E1 = X q x - (\x. E1) x` by METIS_TAC [] >> POP_ORW \\
             MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
             qexistsl_tac [`X q`, `\x. E1`] \\
             fs [real_random_variable, space_def, p_space_def, events_def] \\
             reverse CONJ_TAC
             >- (GEN_TAC >> DISCH_TAC >> DISJ1_TAC \\
                 Q.UNABBREV_TAC `E1` >> METIS_TAC []) \\
             MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST >> Q.EXISTS_TAC `E1` >> fs [space_def]) \\
        `!x. X r x - E2 = X r x - (\x. E2) x` by METIS_TAC [] >> POP_ORW \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
         qexistsl_tac [`X r`, `\x. E2`] \\
         fs [real_random_variable, space_def, p_space_def, events_def] \\
         reverse CONJ_TAC >- (Q.UNABBREV_TAC `E2` >> METIS_TAC []) \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST >> Q.EXISTS_TAC `E2` >> fs [space_def]) \\
     RW_TAC std_ss [abs_le_half_pow2]) >> DISCH_TAC
 (* LHS: applying integral_add *)
 >> Know `expectation p
            (\x. (\x. SIGMA (\x'. (X x' x - expectation p (X x')) pow 2) J) x +
                 (\x. SIGMA (\(i,j). (X i x - expectation p (X i)) *
                                     (X j x - expectation p (X j))) B) x) =
          expectation p (\x. SIGMA (\x'. (X x' x - expectation p (X x')) pow 2) J) +
          expectation p (\x. SIGMA (\(i,j). (X i x - expectation p (X i)) *
                                            (X j x - expectation p (X j))) B)`
 >- (REWRITE_TAC [expectation_def] >> MATCH_MP_TAC integral_add \\
     CONJ_TAC >- fs [prob_space_def] \\
     REWRITE_TAC [CONJ_ASSOC] >> reverse CONJ_TAC (* easy goals first *)
     >- (GEN_TAC >> BETA_TAC >> DISCH_TAC >> DISJ1_TAC \\
         CONJ_TAC
         >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF >> RW_TAC std_ss [lt_infty] \\
             MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC `0` \\
             REWRITE_TAC [le_pow2] >> REWRITE_TAC [lt_infty, extreal_of_num_def]) \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
        `B SUBSET (J CROSS J)` by ASM_SET_TAC [] \\
        `FINITE (J CROSS J)` by PROVE_TAC [FINITE_CROSS] \\
        `FINITE B` by PROVE_TAC [SUBSET_FINITE] >> art [] \\
         Q.X_GEN_TAC `n` >> Cases_on `n` >> DISCH_TAC >> SIMP_TAC std_ss [] \\
         Know `q IN J /\ r IN J`
         >- (CONJ_TAC >> `(q,r) IN (J CROSS J)` by PROVE_TAC [SUBSET_DEF] \\
             POP_ASSUM MP_TAC >> SIMP_TAC std_ss [IN_CROSS]) >> STRIP_TAC \\
         REWRITE_TAC [GSYM expectation_def] \\
        `?a. X q x = Normal a` by PROVE_TAC [extreal_cases] >> POP_ORW \\
        `?b. X r x = Normal b` by PROVE_TAC [extreal_cases] >> POP_ORW \\
        `?c. expectation p (X q) = Normal c` by PROVE_TAC [extreal_cases] >> POP_ORW \\
        `?d. expectation p (X r) = Normal d` by PROVE_TAC [extreal_cases] >> POP_ORW \\
         REWRITE_TAC [extreal_sub_def, extreal_mul_def, extreal_not_infty]) \\
  (* integrable p (\x. SIGMA (\x'. (X x' x - integral p (X x')) pow 2) J) *)
     CONJ_TAC
     >- (`!x x'. (X x' x - integral p (X x')) pow 2 =
                 (\x' x. (X x' x - integral p (X x')) pow 2) x' x` by METIS_TAC [] \\
         POP_ORW >> MATCH_MP_TAC integrable_sum >> ASM_SIMP_TAC std_ss [] \\
         CONJ_TAC >- fs [prob_space_def] \\
         CONJ_TAC
         >- (RW_TAC std_ss [GSYM expectation_def] \\
            `?r. expectation p (X i) = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
             METIS_TAC [finite_second_moments_eq_integrable_squares]) \\
         rpt GEN_TAC >> SIMP_TAC std_ss [GSYM expectation_def] >> DISCH_TAC \\
        `?r. expectation p (X i) = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
        `?c. X i x = Normal c` by PROVE_TAC [extreal_cases] >> POP_ORW \\
         REWRITE_TAC [pow_2, extreal_sub_def, extreal_mul_def, extreal_not_infty]) \\
  (* applying integrable_sum *)
     Know `!x. (\(i,j). (X i x - integral p (X i)) * (X j x - integral p (X j))) =
               (\i. (\i x. (X (FST i) x - integral p (X (FST i))) *
                           (X (SND i) x - integral p (X (SND i)))) i x)`
     >- (GEN_TAC >> FUN_EQ_TAC >> Q.X_GEN_TAC `y` >> Cases_on `y` \\
         SIMP_TAC std_ss []) >> Rewr' \\
     MATCH_MP_TAC integrable_sum \\
    `B SUBSET (J CROSS J)` by ASM_SET_TAC [] \\
    `FINITE (J CROSS J)` by PROVE_TAC [FINITE_CROSS] \\
    `FINITE B` by PROVE_TAC [SUBSET_FINITE] >> art [] \\
     CONJ_TAC >- fs [prob_space_def] \\
     reverse CONJ_TAC
     >- (rpt GEN_TAC >> DISCH_TAC \\
         Cases_on `i` >> FULL_SIMP_TAC std_ss [] \\
         Know `q IN J /\ r IN J`
         >- (CONJ_TAC >> `(q,r) IN (J CROSS J)` by PROVE_TAC [SUBSET_DEF] \\
             POP_ASSUM MP_TAC >> SIMP_TAC std_ss [IN_CROSS]) >> STRIP_TAC \\
         REWRITE_TAC [GSYM expectation_def] \\
        `?a. X q x = Normal a` by PROVE_TAC [extreal_cases] >> POP_ORW \\
        `?b. X r x = Normal b` by PROVE_TAC [extreal_cases] >> POP_ORW \\
        `?c. expectation p (X q) = Normal c` by PROVE_TAC [extreal_cases] >> POP_ORW \\
        `?d. expectation p (X r) = Normal d` by PROVE_TAC [extreal_cases] >> POP_ORW \\
         REWRITE_TAC [extreal_sub_def, extreal_mul_def, extreal_not_infty]) \\
     GEN_TAC >> DISCH_TAC \\
     Cases_on `i` >> FULL_SIMP_TAC std_ss [] \\
     Know `q IN J /\ r IN J`
     >- (CONJ_TAC >> `(q,r) IN (J CROSS J)` by PROVE_TAC [SUBSET_DEF] \\
         POP_ASSUM MP_TAC >> SIMP_TAC std_ss [IN_CROSS]) >> STRIP_TAC \\
     REWRITE_TAC [GSYM expectation_def] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> BETA_TAC >> Rewr'
 (* LHS: applying integral_sum *)
 >> Know `expectation p (\x. SIGMA (\x'. (\i x. (X i x - expectation p (X i)) pow 2) x' x) J) =
          SIGMA (\n. expectation p ((\i x. (X i x - expectation p (X i)) pow 2) n)) J`
 >- (REWRITE_TAC [expectation_def] \\
     MATCH_MP_TAC integral_sum >> ASM_SIMP_TAC std_ss [] \\
     CONJ_TAC >- fs [prob_space_def] \\
     reverse CONJ_TAC
     >- (RW_TAC std_ss [GSYM expectation_def, pow_2] \\
        `?r. X i x = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
        `?c. expectation p (X i) = Normal c` by PROVE_TAC [extreal_cases] >> POP_ORW \\
         REWRITE_TAC [extreal_sub_def, extreal_mul_def, extreal_not_infty]) \\
     RW_TAC std_ss [GSYM expectation_def] \\
    `?c. expectation p (X i) = Normal c` by PROVE_TAC [extreal_cases] >> POP_ORW \\
     METIS_TAC [finite_second_moments_eq_integrable_squares]) >> BETA_TAC >> Rewr'
 >> Suff `expectation p (\x. SIGMA (\(i,j). (X i x - expectation p (X i)) *
                                            (X j x - expectation p (X j))) B) = 0`
 >- (Rewr' >> REWRITE_TAC [add_rzero])
 (* LHS: applying integral_sum again *)
 >> Know `!x. (\(i,j). (X i x - expectation p (X i)) * (X j x - expectation p (X j))) =
              (\i. (X (FST i) x - expectation p (X (FST i))) *
                   (X (SND i) x - expectation p (X (SND i))))`
 >- (GEN_TAC >> RW_TAC std_ss [FUN_EQ_THM] \\
     Cases_on `i` >> SIMP_TAC std_ss []) >> Rewr'
 >> Know `expectation p (\x. SIGMA (\i. (\i x. (X (FST i) x - expectation p (X (FST i))) *
                                               (X (SND i) x - expectation p (X (SND i)))) i x) B) =
          SIGMA (\i. expectation p ((\i x. (X (FST i) x - expectation p (X (FST i))) *
                                           (X (SND i) x - expectation p (X (SND i)))) i)) B`
 >- (REWRITE_TAC [expectation_def] >> MATCH_MP_TAC integral_sum \\
    `B SUBSET (J CROSS J)` by ASM_SET_TAC [] \\
    `FINITE (J CROSS J)` by PROVE_TAC [FINITE_CROSS] \\
    `FINITE B` by PROVE_TAC [SUBSET_FINITE] \\
     ASM_SIMP_TAC std_ss [] \\
     CONJ_TAC >- fs [prob_space_def] \\
     reverse CONJ_TAC
     >- (rpt GEN_TAC >> DISCH_TAC \\
         Cases_on `i` >> FULL_SIMP_TAC std_ss [] \\
         Know `q IN J /\ r IN J`
         >- (CONJ_TAC >> `(q,r) IN (J CROSS J)` by PROVE_TAC [SUBSET_DEF] \\
             POP_ASSUM MP_TAC >> SIMP_TAC std_ss [IN_CROSS]) >> STRIP_TAC \\
         REWRITE_TAC [GSYM expectation_def] \\
        `?a. X q x = Normal a` by PROVE_TAC [extreal_cases] >> POP_ORW \\
        `?b. X r x = Normal b` by PROVE_TAC [extreal_cases] >> POP_ORW \\
        `?c. expectation p (X q) = Normal c` by PROVE_TAC [extreal_cases] >> POP_ORW \\
        `?d. expectation p (X r) = Normal d` by PROVE_TAC [extreal_cases] >> POP_ORW \\
         REWRITE_TAC [extreal_sub_def, extreal_mul_def, extreal_not_infty]) \\
     GEN_TAC >> DISCH_TAC \\
     Cases_on `i` >> FULL_SIMP_TAC std_ss [] \\
     Know `q IN J /\ r IN J`
     >- (CONJ_TAC >> `(q,r) IN (J CROSS J)` by PROVE_TAC [SUBSET_DEF] \\
         POP_ASSUM MP_TAC >> SIMP_TAC std_ss [IN_CROSS]) >> STRIP_TAC \\
     REWRITE_TAC [GSYM expectation_def] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> BETA_TAC >> Rewr'
 >> `B SUBSET (J CROSS J)` by ASM_SET_TAC []
 >> `FINITE (J CROSS J)` by PROVE_TAC [FINITE_CROSS]
 >> `FINITE B` by PROVE_TAC [SUBSET_FINITE]
 >> Suff `SIGMA (\i. expectation p (\x. (X (FST i) x - expectation p (X (FST i))) *
                                        (X (SND i) x - expectation p (X (SND i))))) B =
          SIGMA (\i. 0) B`
 >- (Rewr' >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_ZERO >> art [])
 (* final step: applying EXTREAL_SUM_IMAGE_EQ *)
 >> irule EXTREAL_SUM_IMAGE_EQ
 >> ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_not_infty]
 >> Suff `!x. x IN B ==>
             (expectation p (\x'. (X (FST x) x' - expectation p (X (FST x))) *
                                  (X (SND x) x' - expectation p (X (SND x)))) = 0)`
 >- (RW_TAC std_ss [extreal_of_num_def, extreal_not_infty])
 >> Q.X_GEN_TAC `n` >> Cases_on `n`
 >> Q.UNABBREV_TAC `B` >> RW_TAC std_ss [GSPECIFICATION]
 >> Cases_on `x` >> FULL_SIMP_TAC std_ss []
 >> MATCH_MP_TAC uncorrelated_thm >> PROVE_TAC []
QED

(******************************************************************************)
(*  Almost sure convergence; Borel-Cantelli Lemma [2, p.75]                   *)
(******************************************************************************)

val INDICATOR_FN_REAL_RV = store_thm
  ("INDICATOR_FN_REAL_RV",
  ``!p s. prob_space p /\ s IN events p ==> real_random_variable (indicator_fn s) p``,
    RW_TAC std_ss [real_random_variable, INDICATOR_FN_NOT_INFTY]
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR
 >> Q.EXISTS_TAC `s`
 >> RW_TAC std_ss [subsets_def, space_def]
 >> fs [prob_space_def, measure_space_def, p_space_def, events_def]);

val EVENTS_LIMSUP = store_thm
  ("EVENTS_LIMSUP",
  ``!p E. prob_space p /\ (!n. E n IN events p) ==> limsup E IN events p``,
 (* proof *)
    RW_TAC std_ss [prob_space_def, measure_space_def, events_def, set_limsup_def]
 >> IMP_RES_TAC SIGMA_ALGEBRA_FN_BIGINTER
 >> fs [space_def, subsets_def, IN_FUNSET, IN_UNIV]
 >> POP_ASSUM MATCH_MP_TAC
 >> GEN_TAC >> BETA_TAC
 >> fs [sigma_algebra_def, space_def, subsets_def]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [tail_countable, SUBSET_DEF, GSPECIFICATION]
 >> ASM_REWRITE_TAC []);

val EVENTS_LIMINF = store_thm
  ("EVENTS_LIMINF",
  ``!p E. prob_space p /\ (!n. E n IN events p) ==> liminf E IN events p``,
 (* proof *)
    RW_TAC std_ss [prob_space_def, measure_space_def, events_def, set_liminf_def]
 >> STRIP_ASSUME_TAC
      (REWRITE_RULE [ASSUME ``sigma_algebra (m_space p,measurable_sets p)``, subsets_def]
                    (Q.SPEC `(m_space p,measurable_sets p)` SIGMA_ALGEBRA_ALT))
 >> POP_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> Know `{E n | m <= n} <> {}` >- METIS_TAC [tail_not_empty]
 >> Know `countable {E n | m <= n}` >- METIS_TAC [tail_countable]
 >> RW_TAC std_ss [COUNTABLE_ENUM] >> art []
 >> IMP_RES_TAC SIGMA_ALGEBRA_FN_BIGINTER
 >> fs [space_def, subsets_def, IN_FUNSET, IN_UNIV]
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.PAT_X_ASSUM `{E n | m <= n} = IMAGE f univ(:num)` (MP_TAC o (MATCH_MP EQ_SYM))
 >> RW_TAC std_ss [Once EXTENSION, IN_IMAGE, IN_UNIV, GSPECIFICATION]
 >> POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPEC `f (x :num)`))
 >> Know `?x'. f x = f x'` >- (Q.EXISTS_TAC `x` >> REWRITE_TAC [])
 >> RW_TAC std_ss []
 >> PROVE_TAC []);

val PROB_LIMSUP = store_thm
  ("PROB_LIMSUP",
  ``!p E. prob_space p /\ (!n. E n IN events p) ==>
         (prob p (limsup E) = inf (IMAGE (\m. prob p (BIGUNION {E n | m <= n})) UNIV))``,
    RW_TAC std_ss [prob_space_def, p_space_def, events_def, prob_def]
 >> MATCH_MP_TAC measure_limsup_finite >> art [extreal_of_num_def, lt_infty]);

val PROB_LIMINF = store_thm
  ("PROB_LIMINF",
  ``!p E. prob_space p /\ (!n. E n IN events p) ==>
         (prob p (liminf E) = sup (IMAGE (\m. prob p (BIGINTER {E n | m <= n})) UNIV))``,
    RW_TAC std_ss [prob_space_def, p_space_def, events_def, prob_def]
 >> MATCH_MP_TAC measure_liminf >> art []);

val expectation_indicator = store_thm
  ("expectation_indicator",
  ``!p s. prob_space p /\ s IN events p ==> (expectation p (indicator_fn s) = prob p s)``,
    RW_TAC std_ss [prob_space_def, events_def, expectation_def, prob_def]
 >> MATCH_MP_TAC integral_indicator >> art []);

(* The "easy" part of Borel-Cantelli Lemma

   The following proof is taken from Theorem 24.9 of [9, p.296], which depends on
   Beppo Levi's monotone convergence theorem, IN_limsup and a collorary from Marokv
   inequality.

   Its usual "simple" proofs [2, p.77] [3, p.35] [4, p.308] [6, p.59] all
   require Bool's inequality for p.m.'s, and the convergence (to zero) of the
   remainders of `suminf (prob p o E)`, which the latter part is not easy to
   formalize as is.
 *)
Theorem Borel_Cantelli_Lemma1 :
    !p E. prob_space p /\ (!n. E n IN events p) /\
          suminf (prob p o E) < PosInf ==> (prob p (limsup E) = 0)
Proof
    RW_TAC std_ss [o_DEF]
 >> Know `limsup E = {x | x IN m_space p /\ (suminf (\n. indicator_fn (E n) x) = PosInf)}`
 >- (MATCH_MP_TAC (((REWRITE_RULE [space_def, subsets_def]) o
                    (Q.SPECL [`(m_space p,measurable_sets p)`, `E`]))
                       limsup_suminf_indicator_space) \\
     fs [prob_space_def, measure_space_def, events_def]) >> Rewr'
 >> Q.PAT_X_ASSUM `suminf (\x. prob p (E x)) < PosInf` MP_TAC
 >> Know `!x. prob p (E x) = integral p (indicator_fn (E x))`
 >- (GEN_TAC >> MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC (REWRITE_RULE [expectation_def] expectation_indicator) >> art [])
 >> Rewr'
 >> Know `!x. integral p (indicator_fn (E x)) = pos_fn_integral p (indicator_fn (E x))`
 >- (GEN_TAC >> MATCH_MP_TAC integral_pos_fn \\
     fs [prob_space_def, INDICATOR_FN_POS]) >> Rewr'
 >> Know `!x. pos_fn_integral p (indicator_fn (E x)) =
              pos_fn_integral p ((indicator_fn o E) x)`
 >- RW_TAC std_ss [o_DEF] >> Rewr'
 >> FULL_SIMP_TAC bool_ss [prob_space_def, events_def, p_space_def, prob_def]
 >> `sigma_algebra (m_space p,measurable_sets p)` by PROVE_TAC [measure_space_def]
 (* applying "pos_fn_integral_suminf" *)
 >> Know `suminf (\x. pos_fn_integral p ((indicator_fn o E) x)) =
          pos_fn_integral p (\x. suminf (\i. (indicator_fn o E) i x))`
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC pos_fn_integral_suminf >> RW_TAC std_ss [INDICATOR_FN_POS] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR \\
     Q.EXISTS_TAC `E i` >> art [subsets_def, space_def])
 >> Rewr'
 >> RW_TAC std_ss [o_DEF]
 >> Know `integrable p (\x. suminf (\i. indicator_fn (E i) x))`
 >- (RW_TAC std_ss [integrable_def, lt_infty] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       MATCH_MP_TAC IN_MEASURABLE_BOREL_SUMINF >> BETA_TAC \\
       Q.EXISTS_TAC `indicator_fn o E` \\
       ASM_SIMP_TAC std_ss [o_DEF, space_def, INDICATOR_FN_POS] \\
       GEN_TAC >> MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR \\
       Q.EXISTS_TAC `E n` >> ASM_SIMP_TAC std_ss [subsets_def, space_def],
       (* goal 2 (of 3) *)
       Know `fn_plus (\x. suminf (\i. indicator_fn (E i) x)) =
                     (\x. suminf (\i. indicator_fn (E i) x))`
       >- (MATCH_MP_TAC FN_PLUS_POS_ID >> GEN_TAC >> BETA_TAC \\
           MATCH_MP_TAC ext_suminf_pos >> RW_TAC std_ss [INDICATOR_FN_POS]) \\
       DISCH_THEN (art o wrap),
       (* goal 3 (of 3) *)
       Know `fn_minus (\x. suminf (\i. indicator_fn (E i) x)) = (\x. 0)`
       >- (MATCH_MP_TAC FN_MINUS_POS_ZERO >> GEN_TAC >> BETA_TAC \\
           MATCH_MP_TAC ext_suminf_pos >> RW_TAC std_ss [INDICATOR_FN_POS]) \\
       Rewr' \\
      `pos_fn_integral p (\x. 0) = 0` by PROVE_TAC [pos_fn_integral_zero] >> POP_ORW \\
       REWRITE_TAC [lt_infty, extreal_of_num_def] ])
 >> DISCH_TAC
 >> Know `pos_fn_integral p (\x. suminf (\i. indicator_fn (E i) x)) =
                 integral p (\x. suminf (\i. indicator_fn (E i) x))`
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC integral_pos_fn >> RW_TAC std_ss [] \\
     MATCH_MP_TAC ext_suminf_pos >> RW_TAC std_ss [INDICATOR_FN_POS])
 >> DISCH_THEN (fs o wrap)
 >> IMP_RES_TAC integrable_infty_null >> fs [null_set_def]
QED

val finite_second_moments_indicator_fn = store_thm
  ("finite_second_moments_indicator_fn",
  ``!p s. prob_space p /\ s IN events p ==> finite_second_moments p (indicator_fn s)``,
    rpt STRIP_TAC
 >> Know `finite_second_moments p (indicator_fn s) <=>
          second_moment p (indicator_fn s) 0 < PosInf`
 >- (MATCH_MP_TAC finite_second_moments_alt >> art [] \\
     MATCH_MP_TAC INDICATOR_FN_REAL_RV >> art []) >> Rewr'
 >> fs [second_moment_def, moment_def, sub_rzero]
 >> Know `expectation p (\x. (indicator_fn s x) pow 2) = expectation p (indicator_fn s)`
 >- (fs [prob_space_def, p_space_def, expectation_def, events_def] \\
     MATCH_MP_TAC integral_indicator_pow_eq >> ASM_SIMP_TAC arith_ss []) >> Rewr'
 >> Know `expectation p (indicator_fn s) = prob p s`
 >- (MATCH_MP_TAC expectation_indicator >> art []) >> Rewr'
 >> MATCH_MP_TAC let_trans >> Q.EXISTS_TAC `1`
 >> METIS_TAC [PROB_LE_1, extreal_of_num_def, lt_infty]);

Theorem variance_eq_indicator_fn :
    !p s. prob_space p /\ s IN events p ==>
         (variance p (indicator_fn s) =
          expectation p (indicator_fn s) - (expectation p (indicator_fn s)) pow 2)
Proof
    rpt STRIP_TAC
 >> Suff `variance p (indicator_fn s) =
          expectation p (\x. (indicator_fn s x) pow 2) - (expectation p (indicator_fn s)) pow 2`
 >- (Know `expectation p (\x. (indicator_fn s x) pow 2) = expectation p (indicator_fn s)`
     >- (fs [prob_space_def, p_space_def, expectation_def, events_def] \\
         MATCH_MP_TAC integral_indicator_pow_eq >> ASM_SIMP_TAC arith_ss []) >> Rewr)
 >> MATCH_MP_TAC variance_eq >> art []
 >> STRONG_CONJ_TAC
 >- (MATCH_MP_TAC INDICATOR_FN_REAL_RV >> art []) >> DISCH_TAC
 >> Know `integrable p (\x. (indicator_fn s x) pow 2) <=> finite_second_moments p (indicator_fn s)`
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC finite_second_moments_eq_integrable_square >> art []) >> Rewr'
 >> MATCH_MP_TAC finite_second_moments_indicator_fn >> art []
QED

Theorem variance_le_indicator_fn :
    !p s. prob_space p /\ s IN events p ==>
          variance p (indicator_fn s) <= expectation p (indicator_fn s)
Proof
    rpt STRIP_TAC
 >> Suff `variance p (indicator_fn s) <= expectation p (\x. (indicator_fn s x) pow 2)`
 >- (Know `expectation p (\x. (indicator_fn s x) pow 2) = expectation p (indicator_fn s)`
     >- (fs [prob_space_def, p_space_def, expectation_def, events_def] \\
         MATCH_MP_TAC integral_indicator_pow_eq >> ASM_SIMP_TAC arith_ss []) >> Rewr)
 >> MATCH_MP_TAC variance_le >> art []
 >> STRONG_CONJ_TAC
 >- (MATCH_MP_TAC INDICATOR_FN_REAL_RV >> art []) >> DISCH_TAC
 >> Know `integrable p (\x. (indicator_fn s x) pow 2) <=> finite_second_moments p (indicator_fn s)`
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC finite_second_moments_eq_integrable_square >> art []) >> Rewr'
 >> MATCH_MP_TAC finite_second_moments_indicator_fn >> art []
QED

(* for indicator_fn r.v.'s, pairwise independence implies additive of variances *)
Theorem variance_sum_indicator_fn :
    !p E J. prob_space p /\ (!n. n IN J ==> (E n) IN events p) /\
            pairwise_indep_events p E J /\ FINITE J ==>
           (variance p (\x. SIGMA (\n. (indicator_fn o E) n x) J) =
            SIGMA (\n. variance p ((indicator_fn o E) n)) J)
Proof
    RW_TAC bool_ss [pairwise_indep_events_def]
 >> MATCH_MP_TAC variance_sum
 >> RW_TAC std_ss [o_DEF, uncorrelated_vars_def, uncorrelated_def,
                   finite_second_moments_indicator_fn, INDICATOR_FN_REAL_RV]
 >> REWRITE_TAC [GSYM INDICATOR_FN_INTER]
 >> `E i INTER E j IN events p` by PROVE_TAC [EVENTS_INTER]
 >> ASM_SIMP_TAC std_ss [expectation_indicator] >> fs [indep_def]
QED

(* The harder part of Borel-Cantelli Lemma (of pairwise independence) *)
Theorem Borel_Cantelli_Lemma2p :
    !p E. prob_space p /\ (!n. (E n) IN events p) /\
          pairwise_indep_events p E univ(:num) /\
         (suminf (prob p o E) = PosInf) ==> (prob p (limsup E) = 1)
Proof
    RW_TAC std_ss [pairwise_indep_events_def, IN_UNIV]
 >> Q.ABBREV_TAC `X = indicator_fn o E`
 >> Know `!n. real_random_variable (X n) p`
 >- (GEN_TAC >> Q.UNABBREV_TAC `X` >> SIMP_TAC std_ss [o_DEF] \\
     MATCH_MP_TAC INDICATOR_FN_REAL_RV >> art []) >> DISCH_TAC
 >> Know `!n. (prob p o E) n = expectation p (X n)`
 >- (Q.UNABBREV_TAC `X` \\
     RW_TAC std_ss [o_DEF] >> MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC expectation_indicator >> art []) >> DISCH_TAC
 (* this result can be also derived directly from independence (for any events) *)
 >> Know `!i j. i <> j ==> (expectation p (\x. (X i) x * (X j) x) =
                            expectation p (X i) * expectation p (X j))`
 >- (Q.UNABBREV_TAC `X` >> RW_TAC std_ss [o_DEF] \\
     REWRITE_TAC [GSYM INDICATOR_FN_INTER] \\
    `E i INTER E j IN events p` by PROVE_TAC [EVENTS_INTER] \\
     ASM_SIMP_TAC std_ss [expectation_indicator] >> fs [indep_def]) >> DISCH_TAC
 (* X n is uncorrelated *)
 >> Know `!i j. i <> j ==> uncorrelated p (X i) (X j)`
 >- (Q.UNABBREV_TAC `X` >> RW_TAC std_ss [uncorrelated_def] \\ (* 2 subgoals *)
     MATCH_MP_TAC finite_second_moments_indicator_fn >> art []) >> DISCH_TAC
 (* S is the partial sums of X, always finite *)
 >> Q.ABBREV_TAC `S = \n s. SIGMA (\i. X i s) (count n)`
 >> Know `!n x. S n x <> PosInf /\ S n x <> NegInf`
 >- (rpt GEN_TAC >> Q.UNABBREV_TAC `S` >> BETA_TAC \\
     Q.UNABBREV_TAC `X` >> RW_TAC std_ss [o_DEF] >| (* 2 subgoals, similar tactics *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> RW_TAC std_ss [FINITE_COUNT, IN_COUNT] \\
       PROVE_TAC [INDICATOR_FN_NOT_INFTY],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF >> RW_TAC std_ss [FINITE_COUNT, IN_COUNT] \\
       PROVE_TAC [INDICATOR_FN_NOT_INFTY] ]) >> DISCH_TAC
 (* S is Borel-measurable (needed later) *)
 >> Know `!n. S n IN measurable (p_space p,events p) Borel`
 >- (GEN_TAC >> Q.UNABBREV_TAC `S` \\
     MATCH_MP_TAC (INST_TYPE [``:'b`` |-> ``:num``] IN_MEASURABLE_BOREL_SUM) \\
     BETA_TAC >> Q.EXISTS_TAC `X` >> Q.EXISTS_TAC `count n` \\
     fs [measure_space_def, real_random_variable] \\
     RW_TAC std_ss [space_def, FINITE_COUNT, IN_COUNT] \\
     fs [prob_space_def, p_space_def, events_def, measure_space_def]) >> DISCH_TAC
 (* M is the mean of S, also always finite *)
 >> Q.ABBREV_TAC `M = \n. expectation p (S n)`
 >> Know `!n. M n = SIGMA (prob p o E) (count n)`
 >- (GEN_TAC >> Q.UNABBREV_TAC `M` >> BETA_TAC \\
     Q.UNABBREV_TAC `S` >> BETA_TAC \\
     Q.UNABBREV_TAC `X` >> BETA_TAC \\
     REWRITE_TAC [expectation_def] \\
  (* applying integral_pos_fn, pos_fn_integral_sum *)
     Know `integral p (\s. SIGMA (\i. (indicator_fn o E) i s) (count n)) =
    pos_fn_integral p (\s. SIGMA (\i. (indicator_fn o E) i s) (count n))`
     >- (MATCH_MP_TAC integral_pos_fn >> fs [o_DEF, prob_space_def] \\
         rpt STRIP_TAC >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS \\
         RW_TAC std_ss [FINITE_COUNT, INDICATOR_FN_POS]) >> Rewr' \\
     Know `(prob p o E) = \x. expectation p ((indicator_fn o E) x)`
     >- RW_TAC std_ss [o_DEF, FUN_EQ_THM] >> Rewr' \\
     Know `!x. expectation p ((indicator_fn o E) x) = pos_fn_integral p ((indicator_fn o E) x)`
     >- (RW_TAC std_ss [o_DEF, expectation_def] \\
         MATCH_MP_TAC integral_pos_fn >> fs [prob_space_def, INDICATOR_FN_POS]) >> Rewr' \\
     MATCH_MP_TAC pos_fn_integral_sum \\
     fs [o_DEF, FINITE_COUNT, prob_space_def, INDICATOR_FN_POS, IN_COUNT] \\
     rpt STRIP_TAC >> MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR \\
     Q.EXISTS_TAC `E i` >> fs [measure_space_def, subsets_def, events_def, space_def])
 >> DISCH_TAC
 >> Know `!n. M n <> PosInf /\ M n <> NegInf`
 >- (GEN_TAC >> POP_ASSUM (ONCE_REWRITE_TAC o wrap) \\
     Q.PAT_X_ASSUM `!n. (prob p o E) n = expectation p (X n)` K_TAC \\
     STRIP_TAC >| (* 2 subgoals, similar tactics *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> RW_TAC std_ss [FINITE_COUNT, IN_COUNT, o_DEF] \\
       PROVE_TAC [PROB_FINITE],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF >> RW_TAC std_ss [FINITE_COUNT, IN_COUNT, o_DEF] \\
       PROVE_TAC [PROB_FINITE] ]) >> DISCH_TAC
 >> Know `!n. 0 <= M n`
 >- (GEN_TAC >> art [] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS \\
     Q.PAT_X_ASSUM `!n. (prob p o E) n = P` K_TAC \\
     RW_TAC std_ss [o_DEF, FINITE_COUNT, IN_COUNT] \\
     MATCH_MP_TAC PROB_POSITIVE >> art []) >> DISCH_TAC
 >> Know `!m n. m <= n ==> M m <= M n`
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM `!n. M n = SIGMA (prob p o E) (count n)` (REWRITE_TAC o wrap) \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET \\
     Q.PAT_X_ASSUM `!n. (prob p o E) n = expectation p (X n)` K_TAC \\
     RW_TAC std_ss [FINITE_COUNT, COUNT_MONO, IN_COUNT, o_DEF] \\
     MATCH_MP_TAC PROB_POSITIVE >> art []) >> DISCH_TAC
 (* Step 1: variance of S is smaller than M, by noncorrelation *)
 >> Know `!n. variance p (S n) <= M n`
 >- (GEN_TAC >> Q.UNABBREV_TAC `S` >> Q.UNABBREV_TAC `X` >> BETA_TAC \\
     Know `variance p (\s. SIGMA (\i. (indicator_fn o E) i s) (count n)) =
           SIGMA (\n. variance p ((indicator_fn o E) n)) (count n)`
     >- (MATCH_MP_TAC variance_sum_indicator_fn \\
         ASM_SIMP_TAC std_ss [pairwise_indep_events_def, FINITE_COUNT]) >> Rewr' \\
     Q.PAT_X_ASSUM `!n. M n = SIGMA (prob p o E) (count n)` (REWRITE_TAC o wrap) \\
     irule EXTREAL_SUM_IMAGE_MONO >> RW_TAC bool_ss [IN_COUNT, FINITE_COUNT]
     >- (SIMP_TAC std_ss [o_DEF] \\
         MATCH_MP_TAC variance_le_indicator_fn >> art []) \\
     DISJ2_TAC >> GEN_TAC >> DISCH_TAC \\
    `x <> n` by RW_TAC arith_ss [] \\
     Q.PAT_X_ASSUM `!i j. i <> j ==> uncorrelated p ((indicator_fn o E) i) ((indicator_fn o E) j)`
       (MP_TAC o (PURE_REWRITE_RULE [uncorrelated_def]) o (Q.SPECL [`x`, `n`])) \\
     RW_TAC bool_ss [] >| (* 2 subgoals *)
     [ METIS_TAC [lt_infty, finite_second_moments_eq_finite_variance],
       METIS_TAC [finite_second_moments_imp_finite_expectation] ]) >> DISCH_TAC
 >> Know `!n. real_random_variable (S n) p`
 >- (RW_TAC std_ss [real_random_variable]) >> DISCH_TAC
 >> Know `!n. finite_second_moments p (S n)`
 >- (RW_TAC std_ss [finite_second_moments_eq_finite_variance] \\
     MATCH_MP_TAC let_trans >> Q.EXISTS_TAC `M n` >> art [GSYM lt_infty]) >> DISCH_TAC
 (* Now rewriting the goal, eliminating `limsup` *)
 >> `limsup E IN events p` by PROVE_TAC [EVENTS_LIMSUP]
 >> Know `limsup E = {x | x IN p_space p /\ (suminf (\n. X n x) = PosInf)}`
 >- (Q.UNABBREV_TAC `X` >> SIMP_TAC std_ss [o_DEF] \\
     MATCH_MP_TAC (((REWRITE_RULE [space_def, subsets_def]) o
                    (Q.SPECL [`(p_space p,events p)`, `E`])) limsup_suminf_indicator_space) \\
     fs [prob_space_def, measure_space_def, p_space_def, events_def]) >> DISCH_TAC
 >> Q.ABBREV_TAC `S' = \x. sup (IMAGE (\n. S n x) univ(:num))`
 >> Know `!n x. S n x <= S' x`
 >- (rpt GEN_TAC >> Q.UNABBREV_TAC `S'` \\
     RW_TAC std_ss [le_sup', IN_IMAGE, IN_UNIV] \\
     POP_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC `n` >> REWRITE_TAC []) >> DISCH_TAC
 >> Know `!x. suminf (\n. X n x) = S' x`
 >- (GEN_TAC >> Q.UNABBREV_TAC `S'` >> Q.UNABBREV_TAC `S` >> BETA_TAC \\
     MATCH_MP_TAC ext_suminf_def \\
     Q.UNABBREV_TAC `X` >> RW_TAC std_ss [INDICATOR_FN_POS])
 >> DISCH_TAC >> fs []
 (* S' is also Borel-measurable (needed later) *)
 >> Know `S' IN measurable (p_space p,events p) Borel`
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_SUMINF >> Q.EXISTS_TAC `X` \\
     fs [real_random_variable, space_def] \\
     CONJ_TAC >- fs [prob_space_def, measure_space_def, p_space_def, events_def] \\
     Q.UNABBREV_TAC `X` >> RW_TAC std_ss [o_DEF, INDICATOR_FN_POS]) >> DISCH_TAC
 (* prob p {x | x IN p_space p /\ S' x = PosInf} = 1 *)
 >> Q.ABBREV_TAC `s = {x | x IN p_space p /\ S' x < PosInf}`
 >> Know `limsup E = (p_space p) DIFF s`
 >- (Q.UNABBREV_TAC `s` >> art [] >> RW_TAC std_ss [Once EXTENSION, IN_DIFF, GSPECIFICATION] \\
     EQ_TAC >> RW_TAC std_ss [GSYM lt_infty]) >> DISCH_TAC
 >> Know `s IN events p`
 >- (`s = (p_space p) DIFF (limsup E)` by ASM_SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC EVENTS_COMPL >> METIS_TAC []) >> DISCH_TAC
 >> Suff `prob p s = 0`
 >- (DISCH_TAC >> `1 = 1 - prob p s` by METIS_TAC [sub_rzero] >> POP_ORW \\
    `{x | x IN p_space p /\ (S' x = PosInf)} = (p_space p) DIFF s` by METIS_TAC [] \\
     POP_ORW >> MATCH_MP_TAC PROB_COMPL >> art [])
 >> Q.UNABBREV_TAC `s`
 >> Know `sup (IMAGE (\n. M n) univ(:num)) = PosInf`
 >- (Q.PAT_X_ASSUM `!n. M n = P` (ONCE_REWRITE_TAC o wrap) \\
     Suff `suminf (prob p o E) =
           sup (IMAGE (\n. SIGMA (prob p o E) (count n)) univ(:num))` >- rw [] \\
     MATCH_MP_TAC ext_suminf_def \\
     GEN_TAC >> SIMP_TAC std_ss [o_DEF] \\
     MATCH_MP_TAC PROB_POSITIVE >> art [])
 >> REWRITE_TAC [ETA_THM] >> DISCH_TAC
 (* M n can be larger than any given positive real *)
 >> Know `!e. 0 < e /\ e <> PosInf ==> ?m. e <= M m`
 >- (Q.PAT_X_ASSUM `!n. M n = P` K_TAC >> RW_TAC std_ss [] \\
     CCONTR_TAC >> fs [GSYM extreal_lt_def] \\
     Know `sup (IMAGE M UNIV) <= e`
     >- (RW_TAC std_ss [sup_le', IN_IMAGE, IN_UNIV] \\
         MATCH_MP_TAC lt_imp_le >> art []) >> DISCH_TAC \\
     Know `sup (IMAGE M UNIV) < PosInf`
     >- (MATCH_MP_TAC let_trans >> Q.EXISTS_TAC `e` >> art [GSYM lt_infty]) \\
     RW_TAC std_ss [GSYM lt_infty]) >> DISCH_TAC
 (* Step 2: P {S' x <= (1 / 2) * M n} <= 4 * inv (M n) *)
 >> Know `!n. {x | x IN p_space p /\ S' x <= (1 / 2) * M n} IN events p`
 >- (GEN_TAC >> Q.PAT_X_ASSUM `!n. M n = P` K_TAC \\
     Know `{x | x IN p_space p /\ S' x <= (1 / 2) * M n} =
           PREIMAGE S' {x | x <= (1 / 2) * M n} INTER space (p_space p,events p)`
     >- (RW_TAC std_ss [Once EXTENSION, PREIMAGE_def, IN_INTER, space_def, GSPECIFICATION] \\
         METIS_TAC []) >> Rewr' \\
     fs [IN_MEASURABLE, space_def, subsets_def] >> FIRST_X_ASSUM irule \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_RC]) >> DISCH_TAC
 >> Know `!n. 0 < M n ==>
              prob p {x | x IN p_space p /\ S' x <= (1 / 2) * M n} <= 4 * inv (M n)`
 >- (rpt STRIP_TAC >> MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `prob p {x | x IN p_space p /\ S n x <= (1 / 2) * M n}` \\
     CONJ_TAC
     >- (MATCH_MP_TAC PROB_INCREASING >> CONJ_TAC >- art [] \\
         REWRITE_TAC [CONJ_ASSOC] >> reverse CONJ_TAC
         >- (RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION] \\
             MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `S' x` >> art []) \\
         Q.PAT_X_ASSUM `!n. M n = P` K_TAC \\
         CONJ_TAC >- art [] \\
         Know `{x | x IN p_space p /\ S n x <= (1 / 2) * M n} =
               PREIMAGE (S n) {x | x <= (1 / 2) * M n} INTER space (p_space p,events p)`
         >- (RW_TAC std_ss [Once EXTENSION, PREIMAGE_def, IN_INTER, space_def, GSPECIFICATION] \\
             METIS_TAC []) >> Rewr' \\
         fs [IN_MEASURABLE, space_def, subsets_def] \\
         Q.PAT_X_ASSUM `!n. S n IN (p_space p -> space Borel) /\ P`
             (STRIP_ASSUME_TAC o (Q.SPEC `n`)) >> POP_ASSUM MATCH_MP_TAC \\
         REWRITE_TAC [BOREL_MEASURABLE_SETS_RC]) \\
     Know `!x. S n x <= (1 / 2) * M n <=> S n x - M n <= -(1 / 2) * M n`
     >- (GEN_TAC \\
         Suff `(1 / 2) * M n = -(1 / 2) * M n + 1 * M n`
         >- (Rewr' >> MATCH_MP_TAC EQ_SYM >> REWRITE_TAC [mul_lone] \\
             MATCH_MP_TAC sub_le_eq >> art []) \\
         Suff `1 / 2 = -(1 / 2) + 1`
         >- (DISCH_THEN ((GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites) o wrap) \\
            `?r. M n = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
             MATCH_MP_TAC add_rdistrib_normal \\
             RW_TAC real_ss [extreal_of_num_def, extreal_not_infty, extreal_div_eq,
                             extreal_ainv_def]) \\
         RW_TAC real_ss [extreal_of_num_def, extreal_not_infty, extreal_div_eq, extreal_ainv_def,
                         extreal_add_def, extreal_11]) >> DISCH_TAC \\
     Q.PAT_ASSUM `!x. S n x <= (1 / 2) * M n <=> P` (ONCE_REWRITE_TAC o wrap) \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `prob p {x | x IN p_space p /\ (1 / 2) * M n <= abs (S n x - M n)}` \\
     CONJ_TAC
     >- (MATCH_MP_TAC PROB_INCREASING >> CONJ_TAC >- art [] \\
         Q.PAT_X_ASSUM `!n. M n = P` K_TAC \\
         REWRITE_TAC [CONJ_ASSOC] >> reverse CONJ_TAC
         >- (Know `0 <= (1 / 2) * M n` >- (MATCH_MP_TAC le_mul >> art [half_between]) \\
             RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION, abs_unbounds] \\
             DISJ1_TAC >> art [GSYM mul_lneg]) \\
         STRIP_TAC >| (* 2 subgoals, similar tactics *)
         [ (* goal 1 (of 2) *)
           POP_ASSUM (ONCE_REWRITE_TAC o wrap o GSYM) \\
           Know `{x | x IN p_space p /\ S n x <= (1 / 2) * M n} =
                 PREIMAGE (S n) {x | x <= (1 / 2) * M n} INTER space (p_space p,events p)`
           >- (RW_TAC std_ss [Once EXTENSION, PREIMAGE_def, IN_INTER, space_def, GSPECIFICATION] \\
               METIS_TAC []) >> Rewr' \\
           fs [IN_MEASURABLE, space_def, subsets_def] \\
           Q.PAT_X_ASSUM `!n. S n IN (p_space p -> space Borel) /\ P`
             (STRIP_ASSUME_TAC o (Q.SPEC `n`)) >> POP_ASSUM MATCH_MP_TAC \\
           REWRITE_TAC [BOREL_MEASURABLE_SETS_RC],
           (* goal 2 (of 2) *)
           Know `0 <= (1 / 2) * M n` >- (MATCH_MP_TAC le_mul >> art [half_between]) \\
           DISCH_THEN (MP_TAC o (MATCH_MP abs_unbounds)) >> Rewr' \\
           REWRITE_TAC [GSYM mul_lneg] \\
           POP_ASSUM (ONCE_REWRITE_TAC o wrap o GSYM) \\
           Know `!x. 1 / 2 * M n <= S n x - M n <=> (1 / 2 + 1) * M n <= S n x`
           >- (GEN_TAC \\
               Suff `(1 / 2 + 1) * M n = (1 / 2) * M n + 1 * M n`
               >- (Rewr' >> REWRITE_TAC [mul_lone] \\
                   MATCH_MP_TAC le_sub_eq2 >> art [] \\
                   SIMP_TAC real_ss [extreal_of_num_def, extreal_div_eq] \\
                  `0 <= 1 / 2r` by RW_TAC real_ss [] \\
                   METIS_TAC [mul_not_infty]) \\
              `?r. M n = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
               MATCH_MP_TAC add_rdistrib_normal \\
               RW_TAC real_ss [extreal_of_num_def, extreal_not_infty, extreal_div_eq,
                               extreal_ainv_def]) >> Rewr' \\
           Know `{x | x IN p_space p /\ (S n x <= 1 / 2 * M n \/ (1 / 2 + 1) * M n <= S n x)} =
                 (PREIMAGE (S n) {x | x <= (1 / 2) * M n} INTER space (p_space p,events p)) UNION
                 (PREIMAGE (S n) {x | (1 / 2 + 1) * M n <= x} INTER space (p_space p,events p))`
           >- (RW_TAC std_ss [Once EXTENSION, PREIMAGE_def, IN_UNION, IN_INTER,
                              space_def, GSPECIFICATION] \\
               METIS_TAC []) >> Rewr' \\
           MATCH_MP_TAC EVENTS_UNION \\
           fs [IN_MEASURABLE, space_def, subsets_def] \\
           Q.PAT_X_ASSUM `!n. S n IN (p_space p -> space Borel) /\ P`
             (STRIP_ASSUME_TAC o (Q.SPEC `n`)) \\
           STRIP_TAC >| (* 2 subgoals *)
           [ (* goal 2.1 (of 2) *)
             POP_ASSUM MATCH_MP_TAC >> REWRITE_TAC [BOREL_MEASURABLE_SETS_RC],
             (* goal 2.2 (of 2) *)
             POP_ASSUM MATCH_MP_TAC >> REWRITE_TAC [BOREL_MEASURABLE_SETS_CR] ] ]) \\
  (* applying chebyshev_ineq_variance *)
     Know `!x. S n x - M n = S n x - expectation p (S n)`
     >- (GEN_TAC >> Q.UNABBREV_TAC `M` >> SIMP_TAC std_ss []) >> Rewr' \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `inv ((1 / 2 * M n) pow 2) * variance p (S n)` \\
     Q.PAT_X_ASSUM `!n. M n = P` K_TAC \\
     CONJ_TAC
     >- (SIMP_TAC std_ss [PROB_GSPEC] \\
         MATCH_MP_TAC chebyshev_ineq_variance >> art [] \\
         MATCH_MP_TAC lt_mul >> art [half_between]) \\
     Suff `4 * inv (M n) = inv ((1 / 2 * M n) pow 2) * M n`
     >- (Rewr' >> MATCH_MP_TAC le_lmul_imp >> art [] \\
         MATCH_MP_TAC le_inv >> MATCH_MP_TAC pow_pos_lt \\
         MATCH_MP_TAC lt_mul >> art [half_between]) \\
    `?r. M n = Normal r` by PROVE_TAC [extreal_cases] >> art [] \\
    `0 < r` by PROVE_TAC [extreal_lt_eq, extreal_of_num_def] \\
    `r <> 0` by PROVE_TAC [REAL_LT_LE] \\
     Know `1 / 2 * r * (1 / 2 * r) <> 0` >- (CCONTR_TAC >> fs []) >> DISCH_TAC \\
     ASM_SIMP_TAC real_ss [extreal_of_num_def, extreal_inv_def, extreal_mul_def, pow_2,
                           extreal_div_eq, extreal_11] \\
     ASM_SIMP_TAC real_ss [GSYM REAL_INV_1OVER, REAL_MUL_ASSOC] \\
    `inv 2r <> 0` by RW_TAC real_ss [REAL_INV_EQ_0] \\
     Know `inv 2 * r <> 0` >- (CCONTR_TAC >> fs [] >> PROVE_TAC []) >> DISCH_TAC \\
     Know `inv 2 * r * inv 2 <> 0` >- (CCONTR_TAC >> fs [] >> PROVE_TAC []) >> DISCH_TAC \\
     ASM_SIMP_TAC real_ss [REAL_INV_MUL, REAL_INV_INV] \\
     ASM_SIMP_TAC real_ss [GSYM REAL_MUL_ASSOC, REAL_MUL_LINV] >> REAL_ARITH_TAC)
 >> DISCH_TAC
 >> Q.ABBREV_TAC `f = \n. {x | x IN p_space p /\ S' x <= 1 / 2 * M n}` >> fs []
 >> Know `!m n. m <= n ==> f m SUBSET f n`
 >- (Q.PAT_X_ASSUM `!n. M n = P` K_TAC \\
     Q.UNABBREV_TAC `f` >> RW_TAC bool_ss [SUBSET_DEF, GSPECIFICATION] \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `(1 / 2) * M m` >> art [] \\
     MATCH_MP_TAC le_lmul_imp >> ASM_SIMP_TAC arith_ss [half_between]) >> DISCH_TAC
 (* Step 3: P {S' x < PosInf} = sup (IMAGE (prob p o f) UNIV) *)
 >> Know `prob p {x | x IN p_space p /\ S' x < PosInf} = sup (IMAGE (prob p o f) univ(:num))`
 >- (REWRITE_TAC [prob_def] >> MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC MONOTONE_CONVERGENCE \\
     CONJ_TAC >- fs [prob_space_def] \\
     CONJ_TAC >- fs [events_def, IN_FUNSET, IN_UNIV] \\
     CONJ_TAC >- ASM_SIMP_TAC arith_ss [] \\
     Q.PAT_X_ASSUM `!n. M n = P` K_TAC >> Q.UNABBREV_TAC `f` \\
     RW_TAC std_ss [Once EXTENSION, GSPECIFICATION, IN_BIGUNION_IMAGE, IN_UNIV] \\
     reverse EQ_TAC >> rpt STRIP_TAC >- art [] >| (* 2 subgoals left *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC let_trans >> Q.EXISTS_TAC `(1 / 2) * M n` >> art [GSYM lt_infty] \\
      `?r. M n = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
       SIMP_TAC real_ss [extreal_div_eq, extreal_of_num_def, extreal_mul_def, extreal_not_infty],
       (* goal 2 (of 2) *)
       Know `2 * (S' x) < 2 * PosInf`
       >- (Know `0 < 2 /\ 2 <> PosInf`
           >- PROVE_TAC [lt_02, extreal_of_num_def, extreal_not_infty] \\
           DISCH_THEN (REWRITE_TAC o wrap o (MATCH_MP lt_lmul)) >> art []) \\
       Know `2 * PosInf = PosInf`
       >- (SIMP_TAC real_ss [extreal_of_num_def, extreal_mul_def]) >> Rewr' \\
       Q.PAT_X_ASSUM `sup (IMAGE M univ(:num)) = PosInf` (REWRITE_TAC o wrap o SYM) \\
       RW_TAC std_ss [GSYM sup_lt', IN_IMAGE, IN_UNIV] \\
       Q.EXISTS_TAC `x''` >> MATCH_MP_TAC lt_imp_le \\
       Suff `S' x = (1 / 2) * 2 * S' x`
       >- (Rewr' >> REWRITE_TAC [GSYM mul_assoc] \\
           Know `0 < (1 / 2) /\ (1 / 2) <> PosInf`
           >- (REWRITE_TAC [half_between] \\
               SIMP_TAC real_ss [extreal_of_num_def, extreal_div_eq, extreal_not_infty]) \\
           DISCH_THEN (REWRITE_TAC o wrap o (MATCH_MP lt_lmul)) >> art []) \\
       Know `1 / 2 = extreal_inv 2`
       >- (MATCH_MP_TAC (GSYM inv_1over) \\
           SIMP_TAC real_ss [extreal_of_num_def, extreal_11]) >> Rewr' \\
       Know `extreal_inv 2 * 2 = 1`
       >- (MATCH_MP_TAC mul_linv_pos \\
           SIMP_TAC real_ss [lt_02, extreal_of_num_def, extreal_not_infty]) >> Rewr' \\
       REWRITE_TAC [mul_lone] ]) >> Rewr'
 >> REWRITE_TAC [GSYM le_antisym]
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC le_sup_imp2 >> RW_TAC std_ss [o_DEF, IN_IMAGE, IN_UNIV] \\
     MATCH_MP_TAC PROB_POSITIVE >> art [])
 (* Step 4: sup (IMAGE (prob p o f) univ(:num)) <= 0 *)
 >> MATCH_MP_TAC le_epsilon >> RW_TAC std_ss [add_lzero]
 >> Know `!m n. m <= n ==> (prob p o f) m <= (prob p o f) n`
 >- (RW_TAC std_ss [o_DEF] >> MATCH_MP_TAC PROB_INCREASING >> art [] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> DISCH_TAC
 >> Q.PAT_X_ASSUM `!e. 0 < e /\ e <> PosInf ==> P` (MP_TAC o (Q.SPEC `4 * inv e`))
 >> Know `0 < 4 * inv e /\ 4 * inv e <> PosInf`
 >- (CONJ_TAC
     >- (MATCH_MP_TAC lt_mul \\
         CONJ_TAC >- RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq] \\
         MATCH_MP_TAC inv_pos' >> art []) \\
    `e <> NegInf` by PROVE_TAC [pos_not_neginf, lt_imp_le] \\
    `?r. e = Normal r` by PROVE_TAC [extreal_cases] >> art [] \\
    `0 < r` by PROVE_TAC [extreal_of_num_def, extreal_lt_eq] \\
    `r <> 0` by PROVE_TAC [REAL_LT_LE] \\
     ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_inv_def, extreal_mul_def, extreal_not_infty])
 >> Q.PAT_X_ASSUM `!n. M n = P` K_TAC
 >> RW_TAC std_ss []
 >> Know `0 < M m` >- (MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC `4 * inv e` >> art [])
 >> DISCH_TAC
 >> Know `(prob p o f) m <= 4 * inv (M m)`
 >- (SIMP_TAC std_ss [o_DEF] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> DISCH_TAC
 >> Know `4 * inv e * e <= M m * e`
 >- (MATCH_MP_TAC le_rmul_imp >> art [] \\
     MATCH_MP_TAC lt_imp_le >> art [])
 >> REWRITE_TAC [GSYM mul_assoc]
 >> Know `inv e * e = 1`
 >- (MATCH_MP_TAC mul_linv_pos >> art []) >> Rewr'
 >> REWRITE_TAC [mul_rone] >> DISCH_TAC
 >> Know `inv (M m) * 4 <= inv (M m) * (M m * e)`
 >- (MATCH_MP_TAC le_lmul_imp >> art [] \\
     MATCH_MP_TAC lt_imp_le >> MATCH_MP_TAC inv_pos' >> art [])
 >> REWRITE_TAC [mul_assoc]
 >> Know `inv (M m) * M m = 1`
 >- (MATCH_MP_TAC mul_linv_pos >> art []) >> Rewr'
 >> REWRITE_TAC [mul_lone, Once mul_comm] >> DISCH_TAC
 >> Know `!n. m <= n ==> (prob p o f) n <= e`
 >- (RW_TAC std_ss [] \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `4 * inv (M n)` \\
     Know `0 < M n`
     >- (MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC `M m` >> art [] \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     RW_TAC std_ss [] \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `4 * inv (M m)` >> art [] \\
     MATCH_MP_TAC le_lmul_imp \\
     CONJ_TAC >- RW_TAC real_ss [extreal_of_num_def, extreal_le_eq] \\
     METIS_TAC [inv_le_antimono]) >> DISCH_TAC
 >> Know `sup (IMAGE (prob p o f) UNIV) = sup (IMAGE (\n. (prob p o f) (n + m)) UNIV)`
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC sup_shift >> RW_TAC std_ss []) >> Rewr'
 >> RW_TAC bool_ss [sup_le', IN_IMAGE, IN_UNIV]
 >> POP_ASSUM MATCH_MP_TAC
 >> RW_TAC arith_ss []
QED

(* The hardest part of Borel-Cantelli Lemma (of full independency)

   TODO: prove it directly without using Borel_Cantelli_Lemma2p
 *)
Theorem Borel_Cantelli_Lemma2 :
    !p E. prob_space p /\ (!n. (E n) IN events p) /\
          indep_events p E univ(:num) /\
         (suminf (prob p o E) = PosInf) ==> (prob p (limsup E) = 1)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC Borel_Cantelli_Lemma2p >> art []
 >> MATCH_MP_TAC total_imp_pairwise_indep_events >> art []
QED

(* An easy corollary of Borel-Cantelli Lemma [2, p.82] *)
Theorem Borel_0_1_Law :
    !p E. prob_space p /\ (!n. (E n) IN events p) /\
          pairwise_indep_events p E univ(:num) ==>
         (prob p (limsup E) = 0) \/ (prob p (limsup E) = 1)
Proof
    rpt STRIP_TAC
 >> Cases_on `suminf (prob p o E) = PosInf`
 >| [ (* goal 1 (of 2) *)
      DISJ2_TAC >> MATCH_MP_TAC Borel_Cantelli_Lemma2p >> art [],
      (* goal 2 (of 2) *)
      DISJ1_TAC >> MATCH_MP_TAC Borel_Cantelli_Lemma1 \\
      fs [GSYM lt_infty, pairwise_indep_events_def] ]
QED

(* ========================================================================= *)
(*          Convergence Concepts and The Law(s) of Large Numbers             *)
(* ========================================================================= *)

(* convergence modes *)
val _ = Datatype `convergence_mode = almost_everywhere   ('a p_space)
                                   | in_probability      ('a p_space)
                                   | in_lebesgue extreal ('a p_space)`;

(* convergence of extreal-valued random series [1, p.68,70], only works
   for real-valued random variables (cf. real_random_variable_def)
 *)
Definition converge_def :
   (* X(n) converges to Y (a.e.) *)
   (converge (X :num->'a->extreal) (Y :'a->extreal) (almost_everywhere p) =
     AE x::p. ((\n. real (X n x)) --> real (Y x)) sequentially) /\

   (* X(n) converges to Y (in pr.) *)
   (converge (X :num->'a->extreal) (Y :'a->extreal) (in_probability p) =
     !e. 0 < e /\ e <> PosInf ==>
         ((\n. real (prob p {x | x IN p_space p /\ e < abs (X n x - Y x)})) --> 0)
           sequentially) /\

   (* X(n) converges to Y (in L^r) *)
   (converge (X :num->'a->extreal) (Y :'a->extreal) (in_lebesgue r p) <=>
     0 < r /\ r <> PosInf /\
     (!n. expectation p (\x. (abs (X n x)) powr r) <> PosInf) /\
     (expectation p (\x. (abs (Y x)) powr r) <> PosInf) /\
     ((\n. real (expectation p (\x. (abs (X n x - Y x)) powr r))) --> 0)
       sequentially)
End

val _ = overload_on ("-->", ``converge``); (* util_probTheory *)

(* AE x::p. X_n(x) --> Y(x) *)
Theorem converge_AE_def =
   (List.nth (CONJUNCTS converge_def, 0)) |> SPEC_ALL |> (Q.GENL [`p`, `X`, `Y`]);

(* !e. 0 < e ==> Prob {e < |X_n - Y|} --> 0 *)
Theorem converge_PR_def =
   (List.nth (CONJUNCTS converge_def, 1)) |> SPEC_ALL |> (Q.GENL [`p`, `X`, `Y`]);

(* X_n IN L^p /\ Y IN L^p /\ E [|X_n - Y|^p] --> 0 *)
Theorem converge_LP_def =
   (List.nth (CONJUNCTS converge_def, 2)) |> SPEC_ALL |> (Q.GENL [`p`, `X`, `Y`, `r`]);

(* alternative definition of converge_LP based on absolute moment *)
Theorem converge_LP_alt_absolute_moment :
   !p X Y k. prob_space p /\ (!n. real_random_variable (X n) p) /\
             real_random_variable Y p ==>
       ((X --> Y) (in_lebesgue (&k :extreal) p) <=>
        0 < k /\
        (!n. expectation p (\x. (abs (X n x)) pow k) <> PosInf) /\
        (expectation p (\x. (abs (Y x)) pow k) <> PosInf) /\
        ((\n. real (absolute_moment p (\x. X n x - Y x) 0 k)) --> 0) sequentially)
Proof
    RW_TAC std_ss [converge_LP_def, absolute_moment_def, sub_rzero, num_not_infty]
 >> Know `!Z. 0 < k ==> abs Z powr &k = abs Z pow k`
 >- (rpt STRIP_TAC >> MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC gen_powr >> REWRITE_TAC [abs_pos]) >> DISCH_TAC
 >> EQ_TAC >> STRIP_TAC
 >- (STRONG_CONJ_TAC
     >- (`(0 :real) < &k` by METIS_TAC [extreal_of_num_def, extreal_lt_eq] \\
         FULL_SIMP_TAC real_ss []) >> DISCH_TAC \\
     fs [] >> rfs [])
 >> fs [] >> rfs []
 >> `(0 :real) < &k` by RW_TAC real_ss []
 >> METIS_TAC [extreal_of_num_def, extreal_lt_eq]
QED

(* alternative definition of converge_LP using `pow k` explicitly *)
Theorem converge_LP_alt_pow =
        SIMP_RULE std_ss [absolute_moment_def, sub_rzero]
                  converge_LP_alt_absolute_moment;

(* Theorem 4.1.1 [1, p.69] (2) *)
Theorem converge_AE_alt_sup :
    !p X Y. prob_space p /\ (!n. real_random_variable (X n) p) /\
            real_random_variable Y p ==>
       ((X --> Y) (almost_everywhere p) <=>
        !e. 0 < e /\ e <> PosInf ==>
            (sup (IMAGE (\m. prob p {x | x IN p_space p /\
                                         !n. m <= n ==> abs (X n x - Y x) <= e})
                        univ(:num)) = 1))
Proof
    RW_TAC std_ss [real_random_variable_def]
 >> Q.ABBREV_TAC
     `A = \m e. BIGINTER
                  (IMAGE (\n. {x | x IN p_space p /\ abs (X n x - Y x) <= e}) (from m))`
 >> Q.ABBREV_TAC
     `E = \m e. {x | x IN p_space p /\ !n. m <= n ==> abs (X n x - Y x) <= e}`
 >> Know `!m e. {x | x IN p_space p /\
                     !n. m <= n ==> abs (X n x - Y x) <= e} = E m e`
 >- METIS_TAC [] >> Rewr'
 >> Know `!m e. E m e = A m e`
 >- (RW_TAC set_ss [Abbr `E`, Abbr `A`, Once EXTENSION, IN_BIGINTER_IMAGE, IN_FROM] \\
     EQ_TAC >> RW_TAC std_ss [] \\
     POP_ASSUM (STRIP_ASSUME_TAC o
                 (REWRITE_RULE [LESS_EQ_REFL]) o (Q.SPEC `m`))) >> Rewr'
 >> Know `!e n. {x | x IN p_space p /\ abs (X n x - Y x) <= e} IN events p`
 >- (RW_TAC std_ss [abs_bounds] \\
     Q.ABBREV_TAC `f = \x. X n x - Y x` \\
    `f IN measurable (m_space p,measurable_sets p) Borel`
       by (Q.UNABBREV_TAC `f` \\
           MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
           qexistsl_tac [`X n`, `Y`] \\
           fs [prob_space_def, p_space_def, events_def, space_def,
               measure_space_def, random_variable_def]) \\
     Know `{x | x IN p_space p /\ -e <= X n x - Y x /\ X n x - Y x <= e} =
           ({x | -e <= f x} INTER p_space p) INTER ({x | f x <= e} INTER p_space p)`
     >- (Q.UNABBREV_TAC `f` >> BETA_TAC >> SET_TAC []) >> Rewr' \\
     MATCH_MP_TAC EVENTS_INTER >> fs [events_def, p_space_def] \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC
 >> Know `!m e. A m e IN events p`
 >- (RW_TAC std_ss [Abbr `A`] \\
     MATCH_MP_TAC EVENTS_BIGINTER_FN >> art [COUNTABLE_FROM, FROM_NOT_EMPTY] \\
     RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_FROM] \\
     METIS_TAC []) >> DISCH_TAC
 >> Q.UNABBREV_TAC `E`
 >> Know `!e. BIGUNION (IMAGE (\m. A m e) univ(:num)) IN events p`
 >- (GEN_TAC \\
     MATCH_MP_TAC EVENTS_COUNTABLE_UNION >> art [] \\
     reverse CONJ_TAC
     >- (MATCH_MP_TAC image_countable >> REWRITE_TAC [COUNTABLE_NUM]) \\
     RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV] >> PROVE_TAC []) >> DISCH_TAC
 >> Know `!m e. A m e SUBSET A (SUC m) e`
 >- (RW_TAC set_ss [Abbr `A`, SUBSET_DEF, IN_BIGINTER_IMAGE, IN_FROM]
     >- (Q.PAT_X_ASSUM `!n. m <= n ==> P`
          (STRIP_ASSUME_TAC o (REWRITE_RULE [LESS_EQ_REFL]) o (Q.SPEC `m`))) \\
    `m <= n` by RW_TAC arith_ss [] >> METIS_TAC []) >> DISCH_TAC
 (* Part I: AE ==> (liminf = 1) *)
 >> EQ_TAC
 >- (RW_TAC std_ss [converge_AE_def, AE_THM, almost_everywhere_def, null_set_def,
                    LIM_SEQUENTIALLY, dist] \\
     Know `!x. x IN m_space p DIFF N ==> ?m. x IN (A m e)`
     >- (rpt STRIP_TAC \\
         Q.PAT_X_ASSUM `!x. x IN m_space p DIFF N ==> P` (MP_TAC o (Q.SPEC `x`)) \\
         RW_TAC std_ss [] \\
        `e <> NegInf` by METIS_TAC [pos_not_neginf, lt_imp_le] \\
        `?r. e = Normal r` by METIS_TAC [extreal_cases] \\
        `0 < r` by METIS_TAC [extreal_lt_eq, extreal_of_num_def] \\
         Q.PAT_X_ASSUM `!e. 0 < e ==> P` (MP_TAC o (Q.SPEC `r`)) \\
         RW_TAC std_ss [] \\
         Q.EXISTS_TAC `N'` \\
         RW_TAC set_ss [Abbr `A`, IN_BIGINTER_IMAGE, IN_FROM]
         >- METIS_TAC [DIFF_SUBSET, SUBSET_DEF, p_space_def] \\
         Q.PAT_X_ASSUM `!n. N' <= n ==> P` (MP_TAC o (Q.SPEC `n`)) \\
         RW_TAC std_ss [] \\
        `?a. X n x = Normal a` by METIS_TAC [extreal_cases] \\
        `?b. Y x = Normal b` by METIS_TAC [extreal_cases] \\
         MATCH_MP_TAC lt_imp_le \\
         FULL_SIMP_TAC std_ss [real_normal, extreal_sub_def, extreal_abs_def,
                               extreal_lt_eq]) >> DISCH_TAC \\
    `(m_space p DIFF N) SUBSET BIGUNION (IMAGE (\m. A m e) univ(:num))`
        by (RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_UNIV]) \\
     Know `sup (IMAGE (prob p o (\m. A m e)) univ(:num)) =
           prob p (BIGUNION (IMAGE (\m. A m e) univ(:num)))`
     >- (REWRITE_TAC [prob_def] \\
         MATCH_MP_TAC MONOTONE_CONVERGENCE \\
         CONJ_TAC >- fs [prob_space_def] \\
         RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSYM events_def]) \\
     SIMP_TAC std_ss [o_DEF] >> DISCH_THEN K_TAC \\
     REWRITE_TAC [GSYM le_antisym] \\
     CONJ_TAC >- (MATCH_MP_TAC PROB_LE_1 >> art []) \\
     fs [GSYM p_space_def, GSYM events_def, GSYM prob_def] \\
     Know `prob p (p_space p DIFF N) = 1 - prob p N`
     >- (MATCH_MP_TAC PROB_COMPL >> art []) >> art [sub_rzero] \\
     DISCH_THEN (ONCE_REWRITE_TAC o wrap o (MATCH_MP EQ_SYM)) \\
     MATCH_MP_TAC PROB_INCREASING >> art [] \\
     MATCH_MP_TAC EVENTS_COMPL >> PROVE_TAC [EVENTS_SPACE])
 (* Part II: (liminf = 1) ==> AE *)
 >> RW_TAC std_ss [converge_AE_def, AE_THM, almost_everywhere_def, null_set_def,
                   LIM_SEQUENTIALLY, dist]
 >> Q.ABBREV_TAC `B = \e. BIGUNION (IMAGE (\m. A m e) univ(:num))`
 >> Know `!e. 0 < e /\ e <> PosInf ==> (prob p (B e) = 1)`
 >- (RW_TAC std_ss [Abbr `B`] \\
     Suff `sup (IMAGE (prob p o (\m. A m e)) univ(:num)) =
           prob p (BIGUNION (IMAGE (\m. A m e) univ(:num)))` >- METIS_TAC [] \\
     REWRITE_TAC [prob_def] \\
     MATCH_MP_TAC MONOTONE_CONVERGENCE \\
     CONJ_TAC >- fs [prob_space_def] \\
     RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSYM events_def])
 >> Q.PAT_X_ASSUM `!e. 0 < e /\ e <> PosInf ==> P` K_TAC
 >> DISCH_TAC
 >> Q.ABBREV_TAC `C = BIGINTER (IMAGE (\n. B (1 / &SUC n)) univ(:num))`
 >> Know `C IN events p`
 >- (Q.UNABBREV_TAC `C` \\
     MATCH_MP_TAC EVENTS_BIGINTER_FN >> art [COUNTABLE_NUM] \\
     reverse CONJ_TAC >- (SET_TAC []) \\
     RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV] \\
     Q.UNABBREV_TAC `B` >> METIS_TAC []) >> DISCH_TAC
 >> Know `prob p C = 1`
 >- (Q.UNABBREV_TAC `C` >> REWRITE_TAC [prob_def] \\
    `measure p (BIGINTER (IMAGE (\n. B (1 / &SUC n)) univ(:num))) =
      inf (IMAGE (measure p o (\n. B (1 / &SUC n))) univ(:num))`
     by (MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC MONOTONE_CONVERGENCE_BIGINTER \\
         ASM_SIMP_TAC std_ss [] \\
         CONJ_TAC >- fs [prob_space_def] \\
         STRONG_CONJ_TAC
         >- RW_TAC std_ss [IN_FUNSET, IN_UNIV, Abbr `B`, GSYM events_def] \\
         RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSYM events_def, GSYM prob_def]
         >- METIS_TAC [PROB_FINITE] \\
         RW_TAC std_ss [Abbr `B`, SUBSET_DEF, IN_BIGUNION_IMAGE, IN_UNIV] \\
         Q.EXISTS_TAC `m` >> POP_ASSUM MP_TAC \\
         NTAC 6 (POP_ASSUM K_TAC) \\ (* up to Abbrev A *)
         RW_TAC set_ss [Abbr `A`, IN_BIGINTER_IMAGE, IN_FROM]
         >- (Q.PAT_X_ASSUM `!n'. m <= n' ==> x IN p_space p /\ _`
               (STRIP_ASSUME_TAC o (REWRITE_RULE [LESS_EQ_REFL]) o (Q.SPEC `m`))) \\
         rename1 `m <= N` \\
         Q.PAT_X_ASSUM `!n'. m <= n' ==> x IN p_space p /\ _`
           (MP_TAC o (Q.SPEC `N`)) >> RW_TAC std_ss [] \\
         fs [abs_bounds] \\
        `(&SUC n) :real <> 0` by RW_TAC real_ss [] \\
        `(&SUC (SUC n)) :real <> 0` by RW_TAC real_ss [] \\
         CONJ_TAC >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           MATCH_MP_TAC le_trans \\
           Q.EXISTS_TAC `-(1 / &SUC (SUC n))` >> art [] \\
           rw [extreal_of_num_def, extreal_div_eq, extreal_ainv_def,
               extreal_le_eq] \\
           rw [GSYM REAL_INV_1OVER],
           (* goal 2 (of 2) *)
           MATCH_MP_TAC le_trans \\
           Q.EXISTS_TAC `1 / &SUC (SUC n)` >> art [] \\
           rw [extreal_of_num_def, extreal_div_eq, extreal_ainv_def, extreal_le_eq] \\
           rw [GSYM REAL_INV_1OVER]
         ]) >> POP_ORW \\
     REWRITE_TAC [GSYM prob_def] \\
     Suff `IMAGE (prob p o (\n. B (1 / &SUC n))) univ(:num) = (\y. y = 1)`
     >- (Rewr' >> REWRITE_TAC [inf_const]) \\
     RW_TAC std_ss [Once EXTENSION, IN_IMAGE, IN_UNIV] \\
     SIMP_TAC std_ss [IN_APP] \\
     EQ_TAC >> RW_TAC std_ss []
     >- (FIRST_X_ASSUM MATCH_MP_TAC \\
        `(&SUC x') :real <> 0` by RW_TAC real_ss [] \\
         rw [extreal_of_num_def, extreal_div_eq, extreal_lt_eq, extreal_not_infty] \\
         MATCH_MP_TAC REAL_LT_DIV >> RW_TAC real_ss []) \\
     Q.EXISTS_TAC `0` (* any number is fine *) \\
     MATCH_MP_TAC EQ_SYM \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
    `(&SUC 0) :real <> 0` by RW_TAC real_ss [] \\
     rw [extreal_of_num_def, extreal_div_eq, extreal_lt_eq, extreal_not_infty])
 >> DISCH_TAC
 >> Q.EXISTS_TAC `p_space p DIFF C`
 >> REWRITE_TAC [GSYM CONJ_ASSOC, GSYM events_def, GSYM prob_def, GSYM p_space_def]
 >> STRONG_CONJ_TAC
 >- (MATCH_MP_TAC EVENTS_COMPL >> art []) >> DISCH_TAC
 >> CONJ_TAC
 >- (Know `prob p (p_space p DIFF C) = 1 - prob p C`
     >- (MATCH_MP_TAC PROB_COMPL >> art []) >> Rewr' >> art [] \\
     MATCH_MP_TAC sub_refl >> rw [extreal_of_num_def])
 >> rw [] (* p_space p DIFF (p_space p DIFF C) is simplified *)
 >> Q.PAT_X_ASSUM `x IN C` MP_TAC
 >> Q.PAT_X_ASSUM `C IN events p` K_TAC
 >> Q.PAT_X_ASSUM `prob p C = 1` K_TAC
 >> Q.PAT_X_ASSUM `p_space p DIFF C IN events p` K_TAC
 >> Q.UNABBREV_TAC `C`
 >> RW_TAC std_ss [IN_BIGINTER_IMAGE, IN_UNIV]
 >> Q.PAT_X_ASSUM `!e. 0 < e /\ e <> PosInf ==> _` K_TAC
 >> Q.UNABBREV_TAC `B` >> fs []
 >> MP_TAC (Q.SPEC `e` REAL_ARCH_INV_SUC) >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM `!n. ?s. x IN s /\ P` (STRIP_ASSUME_TAC o (Q.SPEC `n`))
 >> Q.PAT_X_ASSUM `x IN s` MP_TAC >> POP_ORW
 >> Q.PAT_X_ASSUM `!m e. A m e SUBSET A (SUC m) e` K_TAC
 >> Q.PAT_X_ASSUM `!e. BIGUNION (IMAGE (\m. A m e) UNIV) IN events p` K_TAC
 >> Q.PAT_X_ASSUM `!m e. A m e IN events p` K_TAC
 >> Q.UNABBREV_TAC `A`
 >> RW_TAC set_ss [IN_BIGINTER_IMAGE, IN_FROM]
 >> Q.EXISTS_TAC `m`
 >> RW_TAC std_ss []
 >> MATCH_MP_TAC REAL_LET_TRANS
 >> Q.EXISTS_TAC `inv (&SUC n)` >> art []
 >> rename1 `m <= N`
 >> Q.PAT_X_ASSUM `!n'. m <= n' ==> P` (MP_TAC o (Q.SPEC `N`))
 >> RW_TAC std_ss []
 >> `?a. X N x = Normal a` by METIS_TAC [extreal_cases]
 >> `?b. Y x = Normal b` by METIS_TAC [extreal_cases]
 >> `(&SUC n) :real <> 0` by RW_TAC real_ss []
 >> fs [real_normal, extreal_sub_def, extreal_abs_def, extreal_inv_eq,
        extreal_of_num_def, extreal_div_eq, extreal_le_eq, real_div]
QED

(* Theorem 4.1.1 [1, p.69] (2') *)
Theorem converge_AE_alt_inf :
    !p X Y. prob_space p /\ (!n. real_random_variable (X n) p) /\
            real_random_variable Y p ==>
       ((X --> Y) (almost_everywhere p) <=>
        !e. 0 < e /\ e <> PosInf ==>
            (inf (IMAGE (\m. prob p {x | x IN p_space p /\
                                         ?n. m <= n /\ e < abs (X n x - Y x)})
                        univ(:num)) = 0))
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [`p`, `X`, `Y`] converge_AE_alt_sup)
 >> RW_TAC std_ss [] >> POP_ASSUM K_TAC
 >> Q.ABBREV_TAC
     `E = \m e. {x | x IN p_space p /\ !n. m <= n ==> abs (X n x - Y x) <= e}`
 >> `!m e. {x | x IN p_space p /\
                     !n. m <= n ==> abs (X n x - Y x) <= e} = E m e`
      by METIS_TAC [] >> POP_ORW
 >> Know `!m e. {x | x IN p_space p /\ ?n. m <= n /\ e < abs (X n x - Y x)} =
                p_space p DIFF (E m e)`
 >- (RW_TAC set_ss [Abbr `E`, Once EXTENSION] \\
     EQ_TAC >> RW_TAC std_ss [GSYM extreal_lt_def] \\
     Q.EXISTS_TAC `n` >> art []) >> Rewr'
 >> Q.ABBREV_TAC
     `A = \m e. BIGINTER
                  (IMAGE (\n. {x | x IN p_space p /\ abs (X n x - Y x) <= e}) (from m))`
 >> Know `!m e. E m e = A m e`
 >- (RW_TAC set_ss [Abbr `E`, Abbr `A`, Once EXTENSION, IN_BIGINTER_IMAGE, IN_FROM] \\
     EQ_TAC >> RW_TAC std_ss [] \\
     POP_ASSUM (STRIP_ASSUME_TAC o
                 (REWRITE_RULE [LESS_EQ_REFL]) o (Q.SPEC `m`))) >> Rewr'
 >> fs [real_random_variable_def]
 >> Know `!e n. {x | x IN p_space p /\ abs (X n x - Y x) <= e} IN events p`
 >- (RW_TAC std_ss [abs_bounds] \\
     Q.ABBREV_TAC `f = \x. X n x - Y x` \\
    `f IN measurable (m_space p,measurable_sets p) Borel`
       by (Q.UNABBREV_TAC `f` \\
           MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
           qexistsl_tac [`X n`, `Y`] \\
           fs [prob_space_def, p_space_def, events_def, space_def,
               measure_space_def, random_variable_def]) \\
     Know `{x | x IN p_space p /\ -e <= X n x - Y x /\ X n x - Y x <= e} =
           ({x | -e <= f x} INTER p_space p) INTER ({x | f x <= e} INTER p_space p)`
     >- (Q.UNABBREV_TAC `f` >> BETA_TAC >> SET_TAC []) >> Rewr' \\
     MATCH_MP_TAC EVENTS_INTER >> fs [events_def, p_space_def] \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC
 >> Know `!m e. A m e IN events p`
 >- (RW_TAC std_ss [Abbr `A`] \\
     MATCH_MP_TAC EVENTS_BIGINTER_FN >> art [COUNTABLE_FROM, FROM_NOT_EMPTY] \\
     RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_FROM] \\
     METIS_TAC []) >> DISCH_TAC
 >> Q.UNABBREV_TAC `E`
 >> Know `!e. BIGUNION (IMAGE (\m. A m e) univ(:num)) IN events p`
 >- (GEN_TAC >> MATCH_MP_TAC EVENTS_COUNTABLE_UNION >> art [] \\
     reverse CONJ_TAC >- (MATCH_MP_TAC image_countable >> REWRITE_TAC [COUNTABLE_NUM]) \\
     RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV] >> PROVE_TAC []) >> DISCH_TAC
 >> Know `!m e. A m e SUBSET A (SUC m) e`
 >- (RW_TAC set_ss [Abbr `A`, SUBSET_DEF, IN_BIGINTER_IMAGE, IN_FROM]
     >- (Q.PAT_X_ASSUM `!n. m <= n ==> P`
          (STRIP_ASSUME_TAC o (REWRITE_RULE [LESS_EQ_REFL]) o (Q.SPEC `m`))) \\
    `m <= n` by RW_TAC arith_ss [] >> METIS_TAC []) >> DISCH_TAC
 >> Q.PAT_X_ASSUM `!e n. {x | x IN p_space p /\ P} IN events p` K_TAC
 >> Q.ABBREV_TAC `B = \m e. p_space p DIFF A m e`
 >> Know `!m e. p_space p DIFF A m e = B m e` >- METIS_TAC [] >> Rewr'
 >> `!m e. B m e IN events p` by METIS_TAC [EVENTS_COMPL]
 >> Know `!e. BIGINTER (IMAGE (\m. B m e) univ(:num)) IN events p`
 >- (GEN_TAC >> MATCH_MP_TAC EVENTS_COUNTABLE_INTER >> art [] \\
     CONJ_TAC
     >- (RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV] >> PROVE_TAC []) \\
     CONJ_TAC >- (MATCH_MP_TAC image_countable >> REWRITE_TAC [COUNTABLE_NUM]) \\
     RW_TAC std_ss [Once EXTENSION, NOT_IN_EMPTY, IN_IMAGE, IN_UNIV]) >> DISCH_TAC
 >> Know `!m e. B (SUC m) e SUBSET B m e`
 >- (RW_TAC set_ss [Abbr `B`, SUBSET_DEF, IN_BIGINTER_IMAGE, IN_FROM] \\
     ASM_SET_TAC []) >> DISCH_TAC
 >> Suff `!e. 0 < e /\ e <> PosInf ==>
            ((sup (IMAGE (\m. prob p (A m e)) univ(:num)) = 1) <=>
             (inf (IMAGE (\m. prob p (B m e)) univ(:num)) = 0))` >- METIS_TAC []
 >> rpt STRIP_TAC
 >> Know `sup (IMAGE (prob p o (\m. A m e)) univ(:num)) =
          prob p (BIGUNION (IMAGE (\m. A m e) univ(:num)))`
 >- (REWRITE_TAC [prob_def] \\
     MATCH_MP_TAC MONOTONE_CONVERGENCE \\
     CONJ_TAC >- fs [prob_space_def] \\
     RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSYM events_def])
 >> SIMP_TAC std_ss [o_DEF] >> DISCH_THEN K_TAC
 >> Know `inf (IMAGE (prob p o (\m. B m e)) univ(:num)) =
          prob p (BIGINTER (IMAGE (\m. B m e) univ(:num)))`
 >- (REWRITE_TAC [prob_def] \\
     MATCH_MP_TAC MONOTONE_CONVERGENCE_BIGINTER \\
     CONJ_TAC >- fs [prob_space_def] \\
     RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSYM events_def, GSYM prob_def] \\
     PROVE_TAC [PROB_FINITE])
 >> SIMP_TAC std_ss [o_DEF] >> DISCH_THEN K_TAC
 >> Know `BIGUNION (IMAGE (\m. A m e) univ(:num)) =
          p_space p DIFF (BIGINTER (IMAGE (\m. B m e) univ(:num)))`
 >- (RW_TAC std_ss [Once EXTENSION, Abbr `B`, IN_DIFF, IN_UNIV,
                    IN_BIGUNION_IMAGE, IN_BIGINTER_IMAGE] \\
     EQ_TAC >> RW_TAC std_ss [] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       irule PROB_SPACE_IN_PSPACE >> art [] \\
       Q.EXISTS_TAC `A m e` >> art [],
       (* goal 2 (of 3) *)
       Q.EXISTS_TAC `m` >> DISJ2_TAC >> art [],
       (* goal 3 (of 3) *)
       Q.EXISTS_TAC `m` >> art [] ]) >> Rewr'
 >> Know `prob p (p_space p DIFF BIGINTER (IMAGE (\m. B m e) univ(:num))) =
          1 - prob p (BIGINTER (IMAGE (\m. B m e) univ(:num)))`
 >- (MATCH_MP_TAC PROB_COMPL >> art []) >> Rewr'
 >> `prob p (BIGINTER (IMAGE (\m. B m e) univ(:num))) <> PosInf /\
     prob p (BIGINTER (IMAGE (\m. B m e) univ(:num))) <> NegInf`
       by METIS_TAC [PROB_FINITE]
 >> `?r. prob p (BIGINTER (IMAGE (\m. B m e) univ(:num))) = Normal r`
       by METIS_TAC [extreal_cases] >> POP_ORW
 >> rw [extreal_of_num_def, extreal_sub_def, extreal_11]
 >> REAL_ARITH_TAC
QED

(* Theorem 4.1.2 [1, p.70]: convergence a.e. implies convergence in pr. *)
Theorem converge_AE_imp_PR :
    !p X Y. prob_space p /\ (!n. real_random_variable (X n) p) /\
            real_random_variable Y p ==>
           (X --> Y) (almost_everywhere p) ==> (X --> Y) (in_probability p)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (Q.SPECL [`p`, `X`, `Y`] converge_AE_alt_inf)
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM `(X --> Y) (almost_everywhere p) <=> P` K_TAC
 >> RW_TAC real_ss [converge_PR_def, LIM_SEQUENTIALLY, dist]
 >> rename1 `0 < r`
 >> fs [real_random_variable_def]
 >> Q.ABBREV_TAC `D = \n. {x | x IN p_space p /\ e < abs (X n x - Y x)}`
 >> `!n. {x | x IN p_space p /\ e < abs (X n x - Y x)} = D n`
      by METIS_TAC [] >> POP_ORW
 >> Q.ABBREV_TAC `B = \m. {x | x IN p_space p /\ ?n. m <= n /\ e < abs (X n x - Y x)}`
 >> Q.PAT_X_ASSUM `!e. 0 < e /\ e <> PosInf ==> P` (MP_TAC o (Q.SPEC `e`))
 >> `!m. {x | x IN p_space p /\ ?n. m <= n /\ e < abs (X n x - Y x)} = B m`
      by METIS_TAC [] >> POP_ORW
 >> RW_TAC std_ss []
 >> Know `!n. D n SUBSET B n`
 >- (RW_TAC set_ss [Abbr `D`, Abbr `B`, SUBSET_DEF] \\
     Q.EXISTS_TAC `n` >> art [LESS_EQ_REFL]) >> DISCH_TAC
 >> Q.ABBREV_TAC `f = \n x. X n x - Y x`
 >> Know `!n. (f n) IN measurable (m_space p,measurable_sets p) Borel`
 >- (GEN_TAC >> Q.UNABBREV_TAC `f` >> BETA_TAC \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
     qexistsl_tac [`X n`, `Y`] \\
     fs [prob_space_def, p_space_def, events_def, space_def,
         measure_space_def, random_variable_def]) >> DISCH_TAC
 >> Know `!n. D n IN events p`
 >- (GEN_TAC >> Q.UNABBREV_TAC `D` >> BETA_TAC \\
    `{x | x IN p_space p /\ e < abs (X n x - Y x)} =
     p_space p DIFF {x | x IN p_space p /\ abs (X n x - Y x) <= e}`
        by (RW_TAC set_ss [Once EXTENSION, GSYM extreal_lt_def] \\
            METIS_TAC []) >> POP_ORW \\
     MATCH_MP_TAC EVENTS_COMPL >> art [] \\
     RW_TAC std_ss [abs_bounds] \\
    `{x | x IN p_space p /\ -e <= f n x /\ f n x <= e} =
     ({x | -e <= f n x} INTER p_space p) INTER ({x | f n x <= e} INTER p_space p)`
        by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC EVENTS_INTER >> fs [events_def, p_space_def] \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC
 >> `!n. 0 <= prob p (D n)` by METIS_TAC [PROB_POSITIVE]
 >> `!n. prob p (D n) <> PosInf /\ prob p (D n) <> NegInf` by METIS_TAC [PROB_FINITE]
 >> Know `!n. abs (real (prob p (D n))) = real (prob p (D n))`
 >- (RW_TAC std_ss [ABS_REFL] \\
     ASM_SIMP_TAC std_ss [GSYM extreal_le_eq, normal_real,
                          GSYM extreal_of_num_def]) >> Rewr'
 >> ASM_SIMP_TAC std_ss [GSYM extreal_lt_eq, normal_real]
 >> Q.ABBREV_TAC
     `E = \m. {x | x IN p_space p /\ !n. m <= n ==> abs (X n x - Y x) <= e}`
 >> Know `!m. {x | x IN p_space p /\ ?n. m <= n /\ e < abs (X n x - Y x)} =
              p_space p DIFF (E m)`
 >- (RW_TAC set_ss [Abbr `E`, Once EXTENSION] \\
     EQ_TAC >> RW_TAC std_ss [GSYM extreal_lt_def] \\
     Q.EXISTS_TAC `n` >> art [])
 >> DISCH_THEN (fs o wrap)
 >> Q.ABBREV_TAC
     `A = \m. BIGINTER
                (IMAGE (\n. {x | x IN p_space p /\ abs (X n x - Y x) <= e}) (from m))`
 >> Know `!m. E m = A m`
 >- (RW_TAC set_ss [Abbr `E`, Abbr `A`, Once EXTENSION, IN_BIGINTER_IMAGE, IN_FROM] \\
     EQ_TAC >> RW_TAC std_ss [] \\
     POP_ASSUM (STRIP_ASSUME_TAC o
                 (REWRITE_RULE [LESS_EQ_REFL]) o (Q.SPEC `m`)))
 >> DISCH_THEN (fs o wrap)
 >> Know `!m. A m SUBSET A (SUC m)`
 >- (RW_TAC set_ss [Abbr `A`, SUBSET_DEF, IN_BIGINTER_IMAGE, IN_FROM]
     >- (Q.PAT_X_ASSUM `!n. m <= n ==> P`
           (STRIP_ASSUME_TAC o (REWRITE_RULE [LESS_EQ_REFL]) o (Q.SPEC `m`))) \\
    `m <= n` by RW_TAC arith_ss [] >> METIS_TAC []) >> DISCH_TAC
 >> Know `!m. B (SUC m) SUBSET B m`
 >- (RW_TAC set_ss [Abbr `B`, SUBSET_DEF, IN_BIGINTER_IMAGE, IN_FROM] \\
     ASM_SET_TAC []) >> DISCH_TAC
 >> Know `!m n. m <= n ==> B n SUBSET B m`
 >- (GEN_TAC >> Induct_on `n`
     >- (DISCH_TAC >> `m = 0` by RW_TAC arith_ss [] >> art [SUBSET_REFL]) \\
     DISCH_TAC \\
    `m = SUC n \/ m < SUC n` by RW_TAC arith_ss [] >- art [SUBSET_REFL] \\
    `m <= n` by RW_TAC arith_ss [] \\
     MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC `B n` >> art [] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> DISCH_TAC
 >> Know `!n. B n IN events p`
 >- (GEN_TAC >> Q.UNABBREV_TAC `B` >> BETA_TAC \\
     MATCH_MP_TAC EVENTS_COMPL >> art [] \\
     Q.UNABBREV_TAC `A` >> BETA_TAC \\
     MATCH_MP_TAC EVENTS_BIGINTER_FN >> art [COUNTABLE_FROM, FROM_NOT_EMPTY] \\
     RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_FROM] \\
     rename1 `n <= m` >> REWRITE_TAC [abs_bounds] \\
    `{x | x IN p_space p /\ -e <= f m x /\ f m x <= e} =
     ({x | -e <= f m x} INTER p_space p) INTER ({x | f m x <= e} INTER p_space p)`
        by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC EVENTS_INTER >> fs [events_def, p_space_def] \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC
 >> `!n. prob p (D n) <= prob p (B n)` by METIS_TAC [PROB_INCREASING]
 >> Know `inf (IMAGE (\m. prob p (B m)) univ(:num)) < Normal r`
 >- (ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_lt_eq])
 >> RW_TAC std_ss [GSYM inf_lt', IN_IMAGE, IN_UNIV]
 >> Q.EXISTS_TAC `m` >> rpt STRIP_TAC
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC `prob p (B n)`  >> art []
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC `prob p (B m)`  >> art []
 >> MATCH_MP_TAC PROB_INCREASING >> art []
 >> FIRST_X_ASSUM MATCH_MP_TAC   >> art []
QED

(* converge_AE_alt_sup restated by liminf, cf. PROB_LIMINF *)
Theorem converge_AE_alt_liminf :
    !p X Y. prob_space p /\ (!n. real_random_variable (X n) p) /\
            real_random_variable Y p ==>
       ((X --> Y) (almost_everywhere p) <=>
        !e. 0 < e /\ e <> PosInf ==>
            prob p (liminf (\n. {x | x IN p_space p /\ abs (X n x - Y x) <= e})) = 1)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [`p`, `X`, `Y`] converge_AE_alt_sup)
 >> RW_TAC std_ss [] >> POP_ASSUM K_TAC
 >> Suff `!e. 0 < e /\ e <> PosInf ==>
            ((sup
               (IMAGE
                  (\m. prob p
                         {x |
                          x IN p_space p /\
                          !n. m <= n ==> abs (X n x - Y x) <= e}) univ(:num)) = 1) <=>
             (prob p (liminf (\n. {x | x IN p_space p /\ abs (X n x - Y x) <= e})) = 1))`
 >- METIS_TAC []
 >> rpt STRIP_TAC
 >> fs [real_random_variable_def]
 >> Q.ABBREV_TAC `f = \n x. X n x - Y x`
 >> Know `!n. (f n) IN measurable (m_space p,measurable_sets p) Borel`
 >- (GEN_TAC >> Q.UNABBREV_TAC `f` >> BETA_TAC \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
     qexistsl_tac [`X n`, `Y`] \\
     fs [prob_space_def, p_space_def, events_def, space_def,
         measure_space_def, random_variable_def]) >> DISCH_TAC
 >> Q.ABBREV_TAC `E = \n. {x | x IN p_space p /\ abs (X n x - Y x) <= e}`
 >> Know `!n. E n IN events p`
 >- (RW_TAC std_ss [Abbr `E`, abs_bounds] \\
    `{x | x IN p_space p /\ -e <= f n x /\ f n x <= e} =
     ({x | -e <= f n x} INTER p_space p) INTER ({x | f n x <= e} INTER p_space p)`
        by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC EVENTS_INTER >> fs [events_def, p_space_def] \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC
 >> ASM_SIMP_TAC std_ss [PROB_LIMINF]
 >> Suff `!m. {x | x IN p_space p /\ !n. m <= n ==> abs (f n x) <= e} =
              (BIGINTER {E n | m <= n})` >- rw []
 >> GEN_TAC
 >> `{E n | m <= n} = (IMAGE E (from m))`
      by (RW_TAC set_ss [Abbr `E`, IN_FROM, Once EXTENSION]) >> POP_ORW
 >> RW_TAC set_ss [Abbr `E`, Abbr `f`, Once EXTENSION, IN_BIGINTER_IMAGE, IN_FROM]
 >> EQ_TAC >> RW_TAC std_ss []
 >> POP_ASSUM (STRIP_ASSUME_TAC o
                 (REWRITE_RULE [LESS_EQ_REFL]) o (Q.SPEC `m`))
QED

(* converge_AE_alt_inf restated by limsup, cf. PROB_LIMSUP

   Theorem 4.2.2 [1, p.77], also see Borel_Cantelli_Lemma1.
 *)
Theorem converge_AE_alt_limsup :
    !p X Y. prob_space p /\ (!n. real_random_variable (X n) p) /\
            real_random_variable Y p ==>
       ((X --> Y) (almost_everywhere p) <=>
        !e. 0 < e /\ e <> PosInf ==>
            prob p (limsup (\n. {x | x IN p_space p /\ e < abs (X n x - Y x)})) = 0)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [`p`, `X`, `Y`] converge_AE_alt_inf)
 >> RW_TAC std_ss [] >> POP_ASSUM K_TAC
 >> Suff `!e. 0 < e /\ e <> PosInf ==>
            ((inf
               (IMAGE
                  (\m. prob p
                         {x |
                          x IN p_space p /\
                          ?n. m <= n /\ e < abs (X n x - Y x)}) univ(:num)) = 0) <=>
             (prob p (limsup (\n. {x | x IN p_space p /\ e < abs (X n x - Y x)})) = 0))`
 >- METIS_TAC []
 >> rpt STRIP_TAC
 >> fs [real_random_variable_def]
 >> Q.ABBREV_TAC `f = \n x. X n x - Y x`
 >> Know `!n. (f n) IN measurable (m_space p,measurable_sets p) Borel`
 >- (GEN_TAC >> Q.UNABBREV_TAC `f` >> BETA_TAC \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
     qexistsl_tac [`X n`, `Y`] \\
     fs [prob_space_def, p_space_def, events_def, space_def,
         measure_space_def, random_variable_def]) >> DISCH_TAC
 >> Q.ABBREV_TAC `E = \n. {x | x IN p_space p /\ e < abs (X n x - Y x)}`
 >> Know `!n. E n IN events p`
 >- (RW_TAC std_ss [Abbr `E`] \\
   `{x | x IN p_space p /\ e < abs (f n x)} =
     p_space p DIFF {x | x IN p_space p /\ abs (f n x) <= e}`
        by (RW_TAC set_ss [Once EXTENSION, GSYM extreal_lt_def] \\
            METIS_TAC []) >> POP_ORW \\
     MATCH_MP_TAC EVENTS_COMPL >> art [] \\
     REWRITE_TAC [abs_bounds] \\
    `{x | x IN p_space p /\ -e <= f n x /\ f n x <= e} =
     ({x | -e <= f n x} INTER p_space p) INTER ({x | f n x <= e} INTER p_space p)`
        by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC EVENTS_INTER >> fs [events_def, p_space_def] \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC
 >> ASM_SIMP_TAC std_ss [PROB_LIMSUP]
 >> Suff `!m. {x | x IN p_space p /\ ?n. m <= n /\ e < abs (f n x)} =
              (BIGUNION {E n | m <= n})` >- rw []
 >> GEN_TAC
 >> `{E n | m <= n} = (IMAGE E (from m))`
      by (RW_TAC set_ss [Abbr `E`, IN_FROM, Once EXTENSION]) >> POP_ORW
 >> RW_TAC set_ss [Abbr `E`, Abbr `f`, Once EXTENSION, IN_BIGUNION_IMAGE, IN_FROM]
 >> EQ_TAC >> RW_TAC std_ss [] >- art []
 >> Q.EXISTS_TAC `n` >> art []
QED

Theorem real_random_variable_zero :
    !p. prob_space p ==> real_random_variable (\x. 0) p
Proof
    RW_TAC std_ss [prob_space_def, real_random_variable_def,
                   random_variable_def, p_space_def, events_def,
                   num_not_infty]
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST'
 >> fs [measure_space_def]
QED

Theorem real_random_variable_sub :
    !p X Y. prob_space p /\ real_random_variable X p /\
            real_random_variable Y p ==> real_random_variable (\x. X x - Y x) p
Proof
    RW_TAC std_ss [prob_space_def, real_random_variable_def,
                   random_variable_def, p_space_def, events_def]
 >| [ (* goal 1 (of 3) *)
      MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
      qexistsl_tac [`X`, `Y`] >> fs [measure_space_def, space_def],
      (* goal 2 (of 3) *)
     `?a. X x = Normal a` by METIS_TAC [extreal_cases] \\
     `?b. Y x = Normal b` by METIS_TAC [extreal_cases] \\
      rw [extreal_not_infty, extreal_sub_def],
      (* goal 3 (of 3) *)
     `?a. X x = Normal a` by METIS_TAC [extreal_cases] \\
     `?b. Y x = Normal b` by METIS_TAC [extreal_cases] \\
      rw [extreal_not_infty, extreal_sub_def] ]
QED

Theorem converge_AE_to_zero :
    !p X Y. prob_space p /\ (!n. real_random_variable (X n) p) /\
            real_random_variable Y p ==>
       ((X --> Y) (almost_everywhere p) <=>
        ((\n x. X n x - Y x) --> (\x. 0)) (almost_everywhere p))
Proof
    rpt STRIP_TAC
 >> `real_random_variable (\x. 0) p` by PROVE_TAC [real_random_variable_zero]
 >> Q.ABBREV_TAC `Z = \n x. X n x - Y x`
 >> `!n. real_random_variable (Z n) p`
      by (RW_TAC std_ss [Abbr `Z`] \\
          METIS_TAC [real_random_variable_sub])
 >> RW_TAC std_ss [converge_AE_alt_limsup, sub_rzero]
QED

Theorem converge_AE_to_zero' :
    !p X Y Z. prob_space p /\ (!n. real_random_variable (X n) p) /\
              real_random_variable Y p /\ (!n x. Z n x = X n x - Y x) ==>
            ((X --> Y) (almost_everywhere p) <=> (Z --> (\x. 0)) (almost_everywhere p))
Proof
    rpt STRIP_TAC
 >> `real_random_variable (\x. 0) p` by PROVE_TAC [real_random_variable_zero]
 >> Know `!n. real_random_variable (Z n) p`
 >- (GEN_TAC >> `Z n = \x. X n x - Y x` by METIS_TAC [] >> POP_ORW \\
     METIS_TAC [real_random_variable_sub])
 >> RW_TAC std_ss [converge_AE_alt_limsup, sub_rzero]
QED

Theorem converge_PR_to_zero :
    !p X Y. prob_space p /\ (!n. real_random_variable (X n) p) /\
            real_random_variable Y p ==>
       ((X --> Y) (in_probability p) <=>
        ((\n x. X n x - Y x) --> (\x. 0)) (in_probability p))
Proof
    rpt STRIP_TAC
 >> `real_random_variable (\x. 0) p` by PROVE_TAC [real_random_variable_zero]
 >> Q.ABBREV_TAC `Z = \n x. X n x - Y x`
 >> `!n. real_random_variable (Z n) p`
      by (RW_TAC std_ss [Abbr `Z`] \\
          METIS_TAC [real_random_variable_sub])
 >> RW_TAC std_ss [converge_PR_def, sub_rzero]
QED

Theorem converge_PR_to_zero' :
    !p X Y Z. prob_space p /\ (!n. real_random_variable (X n) p) /\
              real_random_variable Y p /\ (!n x. Z n x = X n x - Y x) ==>
            ((X --> Y) (in_probability p) <=> (Z --> (\x. 0)) (in_probability p))
Proof
    rpt STRIP_TAC
 >> `real_random_variable (\x. 0) p` by PROVE_TAC [real_random_variable_zero]
 >> Know `!n. real_random_variable (Z n) p`
 >- (GEN_TAC >> `Z n = \x. X n x - Y x` by METIS_TAC [] >> POP_ORW \\
     METIS_TAC [real_random_variable_sub])
 >> RW_TAC std_ss [converge_PR_def, sub_rzero]
QED

Theorem converge_AE_imp_PR' :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) ==>
          (X --> (\x. 0)) (almost_everywhere p) ==> (X --> (\x. 0)) (in_probability p)
Proof
    rpt STRIP_TAC
 >> irule converge_AE_imp_PR
 >> rw [real_random_variable_zero]
QED

(* Theorem 4.1.4 [2, p.71], for moments (integer-valued) only. *)
Theorem converge_LP_imp_PR' :
    !p X k. prob_space p /\ (!n. real_random_variable (X n) p) ==>
            (X --> (\x. 0)) (in_lebesgue (&k :extreal) p) ==>
            (X --> (\x. 0)) (in_probability p)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> `real_random_variable (\x. 0) p` by PROVE_TAC [real_random_variable_zero]
 >> RW_TAC real_ss [converge_LP_alt_pow, converge_PR_def, LIM_SEQUENTIALLY,
                    dist, expectation_def, sub_rzero, REAL_SUB_RZERO]
 >> fs [real_random_variable_def]
 >> rename1 `0 < d` (* the last assumption *)
 >> Know `!n. {x | x IN p_space p /\ e < abs (X n x)} IN events p`
 >- (GEN_TAC \\
    `{x | x IN p_space p /\ e < abs (X n x)} =
     p_space p DIFF {x | x IN p_space p /\ abs (X n x) <= e}`
        by (RW_TAC set_ss [Once EXTENSION, GSYM extreal_lt_def] \\
            METIS_TAC []) >> POP_ORW \\
     MATCH_MP_TAC EVENTS_COMPL >> art [] \\
     REWRITE_TAC [abs_bounds] \\
    `{x | x IN p_space p /\ -e <= X n x /\ X n x <= e} =
     ({x | -e <= X n x} INTER p_space p) INTER ({x | X n x <= e} INTER p_space p)`
        by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC EVENTS_INTER >> fs [events_def, p_space_def] \\
     fs [random_variable_def, events_def, p_space_def] \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE])
 >> DISCH_TAC
 >> Know `!n. abs (real (prob p {x | x IN p_space p /\ e < abs (X n x)})) =
                   real (prob p {x | x IN p_space p /\ e < abs (X n x)})`
 >- (GEN_TAC \\
    `prob p {x | x IN p_space p /\ e < abs (X n x)} <> PosInf /\
     prob p {x | x IN p_space p /\ e < abs (X n x)} <> NegInf`
        by METIS_TAC [PROB_FINITE] \\
     ASM_SIMP_TAC std_ss [ABS_REFL, GSYM extreal_le_eq, normal_real,
                          GSYM extreal_of_num_def] \\
     MATCH_MP_TAC PROB_POSITIVE >> art []) >> Rewr'
 >> Know `!n. 0 <= integral p (\x. abs (X n x) pow k)`
 >- (GEN_TAC >> MATCH_MP_TAC integral_pos \\
     fs [prob_space_def] \\
     rpt STRIP_TAC >> MATCH_MP_TAC pow_pos_le >> REWRITE_TAC [abs_pos])
 >> DISCH_TAC
 >> `!n. integral p (\x. abs (X n x) pow k) <> NegInf`
       by METIS_TAC [pos_not_neginf]
 >> Know `!n. abs (real (integral p (\x. abs (X n x) pow k))) =
                   real (integral p (\x. abs (X n x) pow k))`
 >- (GEN_TAC \\
     ASM_SIMP_TAC std_ss [ABS_REFL, GSYM extreal_le_eq, normal_real,
                          GSYM extreal_of_num_def])
 >> DISCH_THEN (fs o wrap)
 >> Know `!n. integrable p (\x. abs (X n x) pow k)`
 >- (GEN_TAC \\
     fs [prob_space_def, random_variable_def, p_space_def, events_def] \\
     Know `measure_space p /\
           (!x. x IN m_space p ==> 0 <= (\x. abs (X n x) pow k) x)`
     >- (RW_TAC std_ss [] \\
         MATCH_MP_TAC pow_pos_le >> REWRITE_TAC [abs_pos]) \\
     DISCH_THEN (REWRITE_TAC o wrap o (MATCH_MP integrable_pos)) \\
     reverse CONJ_TAC
     >- (Suff `pos_fn_integral p (\x. abs (X n x) pow k) =
                      integral p (\x. abs (X n x) pow k)` >- rw [] \\
         MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC integral_pos_fn \\
         RW_TAC std_ss [] \\
         MATCH_MP_TAC pow_pos_le >> REWRITE_TAC [abs_pos]) \\
     ONCE_REWRITE_TAC [METIS_PROVE []
       ``(\x. abs (X n x) pow k) = (\x. (\x. abs (X n x)) x pow k)``] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_POW \\
     CONJ_TAC >- fs [measure_space_def] \\
     CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS \\
                  Q.EXISTS_TAC `X n` \\
                  fs [measure_space_def]) \\
     RW_TAC std_ss [space_def] >> METIS_TAC [abs_not_infty]) >> DISCH_TAC
 (* eliminate all `real (prob p ...)` *)
 >> `!n. real (prob p {x | x IN p_space p /\ e < abs (X n x)}) < d <=>
               prob p {x | x IN p_space p /\ e < abs (X n x)} < Normal d`
       by (METIS_TAC [PROB_FINITE, normal_real, extreal_lt_eq]) >> POP_ORW
 >> `!n. integral p (\x. abs (X n x) pow k) <> NegInf`
       by (METIS_TAC [pos_not_neginf])
 >> `!e n. real (integral p (\x. abs (X n x) pow k)) < e <=>
                 integral p (\x. abs (X n x) pow k) < Normal e`
       by (METIS_TAC [normal_real, extreal_lt_eq])
 >> POP_ASSUM (fs o wrap)
 (* prepare for prob_markov_ineq *)
 >> `e <> NegInf` by METIS_TAC [lt_imp_le, pos_not_neginf]
 >> `?E. e = Normal E` by METIS_TAC [extreal_cases]
 >> `0 < E` by METIS_TAC [extreal_of_num_def, extreal_lt_eq]
 >> Q.PAT_X_ASSUM `!e. 0 < e ==> ?N. P` (MP_TAC o (Q.SPEC `d * E pow k`))
 >> `0 < E pow k` by PROVE_TAC [REAL_POW_LT]
 >> Know `0 < d * E pow k` >- (MATCH_MP_TAC REAL_LT_MUL >> art [])
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC `N` >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM `!n. N <= n ==> P`
      (MP_TAC o (REWRITE_RULE [GSYM expectation_def]) o (Q.SPEC `n`))
 >> RW_TAC std_ss [GSYM extreal_mul_def]
 >> Know `!m x. Normal E < abs (X m x) <=>
                Normal (E pow k) < abs (X m x) pow k`
 >- (rpt GEN_TAC \\
    `?r. X m x = Normal r` by METIS_TAC [extreal_cases] >> POP_ORW \\
     SIMP_TAC std_ss [extreal_abs_def, extreal_pow_def, extreal_lt_eq] \\
    `k <> 0` by RW_TAC arith_ss [] \\
     EQ_TAC >> STRIP_TAC
     >- (MATCH_MP_TAC REAL_POW_LT2 >> art [] \\
         MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
     SPOSE_NOT_THEN (ASSUME_TAC o (REWRITE_RULE [GSYM real_lte])) \\
    `abs r pow k <= E pow k` by METIS_TAC [POW_LE, ABS_POS] \\
     METIS_TAC [REAL_LTE_ANTISYM])
 >> DISCH_THEN (fs o wrap)
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC `prob p {x | x IN p_space p /\ Normal (E pow k) <= abs (X n x) pow k}`
 >> CONJ_TAC (* from `<` to `<=` *)
 >- (MATCH_MP_TAC PROB_INCREASING >> art [] \\
     reverse CONJ_TAC
     >- (RW_TAC set_ss [SUBSET_DEF] >> MATCH_MP_TAC lt_imp_le >> art []) \\
     fs [random_variable_def, prob_space_def, events_def, p_space_def] \\
    `{x | x IN m_space p /\ Normal (E pow k) <= abs (X n x) pow k} =
     {x | Normal (E pow k) <= (\x. abs (X n x) pow k) x} INTER m_space p`
        by SET_TAC [] >> POP_ORW \\
     Suff `(\x. abs (X n x) pow k) IN measurable (m_space p,measurable_sets p) Borel`
     >- (DISCH_THEN (REWRITE_TAC o wrap o
                     (MATCH_MP IN_MEASURABLE_BOREL_ALL_MEASURE))) \\
    `!x. abs (X n x) = (\x. abs (X n x)) x` by METIS_TAC [] >> POP_ORW \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_POW \\
     CONJ_TAC >- fs [measure_space_def] \\
     RW_TAC std_ss [abs_not_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS >> Q.EXISTS_TAC `X n` \\
     CONJ_TAC >- fs [measure_space_def] \\
     RW_TAC std_ss [])
 (* applying prob_markov_ineq *)
 >> Q.ABBREV_TAC `Y = \x. abs (X n x) pow k`
 >> Know `!x. abs (X n x) pow k = abs (Y x)`
 >- (RW_TAC std_ss [Abbr `Y`, Once EQ_SYM_EQ, abs_refl] \\
     MATCH_MP_TAC pow_pos_le >> rw [abs_pos]) >> Rewr'
 >> `{x | x IN p_space p /\ Normal (E pow k) <= abs (Y x)} =
     {x | Normal (E pow k) <= abs (Y x)} INTER p_space p` by SET_TAC [] >> POP_ORW
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC `inv (Normal (E pow k)) * expectation p (abs o Y)`
 >> CONJ_TAC
 >- (MATCH_MP_TAC prob_markov_ineq \\
     RW_TAC std_ss [Abbr `Y`, extreal_of_num_def, extreal_lt_eq])
 >> Know `abs o Y = Y`
 >- (RW_TAC std_ss [o_DEF, Abbr `Y`, abs_refl, FUN_EQ_THM] \\
     MATCH_MP_TAC pow_pos_le >> rw [abs_pos]) >> Rewr'
 >> `0 < Normal (E pow k) /\ Normal (E pow k) <> PosInf`
       by (ASM_SIMP_TAC std_ss [extreal_not_infty, extreal_of_num_def, extreal_lt_eq])
 >> Know `inv (Normal (E pow k)) * expectation p Y < Normal d <=>
          Normal (E pow k) * (inv (Normal (E pow k)) * expectation p Y) <
          Normal (E pow k) * Normal d`
 >- (MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC lt_lmul >> art []) >> Rewr'
 >> ASM_SIMP_TAC std_ss [mul_assoc, mul_lone,
                         ONCE_REWRITE_RULE [mul_comm] mul_linv_pos]
 >> ASM_REWRITE_TAC [Once mul_comm]
QED

(* Theorem 5.1.1, Part I [2, p.108]: The Weak Law of Large Numbers

   (uncorrelated random sequence with a common bound of variances)
 *)
Theorem WLLN_uncorrelated_L2 :
    !p X S M. prob_space p /\ (!n. real_random_variable (X n) p) /\
       (!i j. i <> j ==> uncorrelated p (X i) (X j)) /\
       (?c. c <> PosInf /\ !n. variance p (X n) <= c) /\
       (!n x. S n x = SIGMA (\i. X i x) (count n)) /\
       (!n. M n = expectation p (S n)) ==>
       ((\n x. (S (SUC n) x - M (SUC n)) / &SUC n) --> (\x. 0)) (in_lebesgue 2 p)
Proof
    rpt STRIP_TAC
 >> `real_random_variable (\x. 0) p` by PROVE_TAC [real_random_variable_zero]
 >> Know `!n. integrable p (X n)`
 >- (GEN_TAC >> MATCH_MP_TAC finite_second_moments_imp_integrable >> art [] \\
     ASM_SIMP_TAC std_ss [finite_second_moments_eq_finite_variance] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC `c` >> rw [GSYM lt_infty]) >> DISCH_TAC
 >> Q.PAT_X_ASSUM `!n. real_random_variable (X n) p`
      (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
       (REWRITE_RULE [real_random_variable_def]))
 >> Know `!n x. S n x <> PosInf`
 >- (RW_TAC std_ss [] >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
     RW_TAC std_ss [FINITE_COUNT, IN_COUNT]) >> DISCH_TAC
 >> Know `!n x. S n x <> NegInf`
 >- (RW_TAC std_ss [] >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
     RW_TAC std_ss [FINITE_COUNT, IN_COUNT]) >> DISCH_TAC
 >> Know `!n. M n <> PosInf /\ M n <> NegInf`
 >- (GEN_TAC >> ASM_SIMP_TAC std_ss [expectation_def] \\
     MATCH_MP_TAC integrable_finite_integral \\
     CONJ_TAC >- fs [prob_space_def] \\
    `S n = \x. SIGMA (\i. X i x) (count n)` by METIS_TAC [] >> POP_ORW \\
     MATCH_MP_TAC integrable_sum \\
     RW_TAC std_ss [FINITE_COUNT, IN_COUNT] >> fs [prob_space_def])
 >> DISCH_TAC
 >> Know `!n x. S (SUC n) x - M (SUC n) <> PosInf /\
                S (SUC n) x - M (SUC n) <> NegInf`
 >- (rpt GEN_TAC \\
    `?a. S (SUC n) x = Normal a` by METIS_TAC [extreal_cases] >> POP_ORW \\
    `?b. M (SUC n) = Normal b` by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def]) >> DISCH_TAC
 >> Know `!n x. (S (SUC n) x - M (SUC n)) / &SUC n =
                inv (&SUC n) * (S (SUC n) x - M (SUC n))`
 >- (rpt GEN_TAC >> MATCH_MP_TAC div_eq_mul_linv \\
    `?a. S (SUC n) x = Normal a` by METIS_TAC [extreal_cases] >> POP_ORW \\
    `?b. M (SUC n) = Normal b` by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def] \\
     RW_TAC real_ss [extreal_lt_eq, extreal_of_num_def]) >> Rewr'
 >> Know `!n. inv (&SUC n) = Normal (inv (&SUC n))`
 >- (GEN_TAC >> `(0 :real) <> &SUC n` by RW_TAC real_ss [] \\
     ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_inv_eq]) >> Rewr'
 >> Q.ABBREV_TAC `Z = \n x. Normal (inv (&SUC n)) * (S (SUC n) x - M (SUC n))`
 >> `sigma_algebra (m_space p,measurable_sets p)`
       by METIS_TAC [prob_space_def, measure_space_def]
 >> Know `!n. real_random_variable (Z n) p`
 >- (GEN_TAC >> Q.UNABBREV_TAC `Z` \\
     SIMP_TAC std_ss [real_random_variable,
                      p_space_def, events_def] \\
     reverse CONJ_TAC
     >- (GEN_TAC \\
        `?a. S (SUC n) x = Normal a` by METIS_TAC [extreal_cases] >> POP_ORW \\
        `?b. M (SUC n) = Normal b` by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_sub_def, extreal_mul_def]) \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL \\
     qexistsl_tac [`\x. S (SUC n) x - M (SUC n)`, `inv (&SUC n)`] \\
     CONJ_TAC >- rw [] >> reverse CONJ_TAC >- rw [space_def] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
     qexistsl_tac [`S (SUC n)`, `\x. M (SUC n)`] \\
     CONJ_TAC >- rw [] >> SIMP_TAC std_ss [space_def] \\
     ONCE_REWRITE_TAC [CONJ_ASSOC] >> reverse CONJ_TAC >- rw [] \\
     reverse CONJ_TAC
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST' >> art []) \\
    `S (SUC n) = \x. SIGMA (\i. X i x) (count (SUC n))` by METIS_TAC [] >> POP_ORW \\
     MATCH_MP_TAC (INST_TYPE [``:'b`` |-> ``:num``] IN_MEASURABLE_BOREL_SUM) \\
     qexistsl_tac [`X`, `count (SUC n)`] \\
     RW_TAC std_ss [FINITE_COUNT, IN_COUNT] \\
     fs [random_variable_def, p_space_def, events_def]) >> DISCH_TAC
 >> Know `!n. real_random_variable (S n) p`
 >- (RW_TAC std_ss [real_random_variable,
                    p_space_def, events_def] \\
    `S n = \x. SIGMA (\i. X i x) (count n)` by METIS_TAC [] >> POP_ORW \\
     MATCH_MP_TAC (INST_TYPE [``:'b`` |-> ``:num``] IN_MEASURABLE_BOREL_SUM) \\
     qexistsl_tac [`X`, `count n`] \\
     RW_TAC std_ss [FINITE_COUNT, IN_COUNT] \\
     fs [random_variable_def, p_space_def, events_def]) >> DISCH_TAC
 >> ASM_SIMP_TAC std_ss [converge_LP_alt_pow, sub_rzero, abs_0, zero_pow, lt_02, abs_pow2]
 >> REWRITE_TAC [Once CONJ_SYM, GSYM CONJ_ASSOC]
 >> CONJ_TAC >- (REWRITE_TAC [extreal_of_num_def] >> rw [expectation_const])
 (* prove that (S n) has finite second moments *)
 >> Know `!n. variance p (S n) <= &n * c`
 >- (GEN_TAC \\
     Know `variance p (S n) = SIGMA (\n. variance p (X n)) (count n)`
     >- (`S n = \x. SIGMA (\i. X i x) (count n)` by METIS_TAC [] >> POP_ORW \\
         MATCH_MP_TAC variance_sum \\
         RW_TAC std_ss [uncorrelated_vars_def, real_random_variable_def,
                        FINITE_COUNT]) >> Rewr' \\
     Know `&CARD (count n) * c = SIGMA (\x. c) (count n)`
     >- (MATCH_MP_TAC EQ_SYM >> irule EXTREAL_SUM_IMAGE_FINITE_CONST \\
         RW_TAC std_ss [FINITE_COUNT]) \\
     REWRITE_TAC [CARD_COUNT] >> Rewr' \\
     irule EXTREAL_SUM_IMAGE_MONO \\
     RW_TAC std_ss [FINITE_COUNT, IN_COUNT] >> DISJ2_TAC \\
     RW_TAC std_ss [lt_infty] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC `c` >> rw [GSYM lt_infty]) >> DISCH_TAC
 >> Know `c <> NegInf`
 >- (MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `variance p (X 0)` >> art [] \\
     ASM_SIMP_TAC std_ss [variance_pos]) >> DISCH_TAC
 >> `!n. variance p (S n) <> NegInf`
       by METIS_TAC [pos_not_neginf, variance_pos]
 >> Know `!n. variance p (S n) <> PosInf`
 >- (GEN_TAC >> REWRITE_TAC [lt_infty] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC `&n * c` >> art [GSYM lt_infty] \\
    `?r. c = Normal r` by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_of_num_def, extreal_mul_def, extreal_not_infty]) >> DISCH_TAC
 >> `!n. finite_second_moments p (S n)`
       by (RW_TAC std_ss [finite_second_moments_eq_finite_variance, GSYM lt_infty])
 >> Know `!n. expectation p (\x. Z n x pow 2) =
              Normal (inv (&SUC n) pow 2) * variance p (S (SUC n))`
 >- (GEN_TAC >> SIMP_TAC std_ss [Abbr `Z`, variance_alt] \\
     Q.PAT_ASSUM `!n. M n = P` (ONCE_REWRITE_TAC o wrap o GSYM) \\
     SIMP_TAC std_ss [pow_mul, extreal_pow_def, expectation_def] \\
     HO_MATCH_MP_TAC integral_cmul \\
     CONJ_TAC >- fs [prob_space_def] \\
     Know `measure_space p /\
           (!x. x IN m_space p ==> 0 <= (\x. (S (SUC n) x - M (SUC n)) pow 2) x)`
     >- (fs [prob_space_def, le_pow2]) \\
     DISCH_THEN (ONCE_REWRITE_TAC o wrap o (MATCH_MP integrable_pos)) \\
     CONJ_TAC (* Boreal_measurable *)
     >- (HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_POW \\
         CONJ_TAC >- art [] \\
         reverse CONJ_TAC >- art [] \\
         HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
         qexistsl_tac [`S (SUC n)`, `\x. M (SUC n)`] \\
         CONJ_TAC >- art [] \\
         SIMP_TAC std_ss [space_def] \\
         ONCE_REWRITE_TAC [CONJ_ASSOC] >> reverse CONJ_TAC >- rw [] \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST' >> art []) \\
        `S (SUC n) = \x. SIGMA (\i. X i x) (count (SUC n))` by METIS_TAC [] >> POP_ORW \\
         MATCH_MP_TAC (INST_TYPE [``:'b`` |-> ``:num``] IN_MEASURABLE_BOREL_SUM) \\
         qexistsl_tac [`X`, `count (SUC n)`] \\
         RW_TAC std_ss [FINITE_COUNT, IN_COUNT] \\
         fs [random_variable_def, p_space_def, events_def]) \\
     Know `pos_fn_integral p (\x. (S (SUC n) x - M (SUC n)) pow 2) =
                  integral p (\x. (S (SUC n) x - M (SUC n)) pow 2)`
     >- (MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC integral_pos_fn >> fs [prob_space_def, le_pow2]) >> Rewr' \\
     REWRITE_TAC [GSYM expectation_def] \\
     Q.PAT_X_ASSUM `!n. M n = expectation p (S n)` (ONCE_REWRITE_TAC o wrap) \\
     ASM_REWRITE_TAC [GSYM variance_alt, GSYM lt_infty]) >> Rewr'
 >> reverse CONJ_TAC
 >- (GEN_TAC \\
    `?r. variance p (S (SUC n)) = Normal r` by METIS_TAC [extreal_cases] \\
     ASM_SIMP_TAC std_ss [extreal_mul_def, extreal_not_infty])
 (* final stage *)
 >> RW_TAC real_ss [LIM_SEQUENTIALLY, dist]
 >> `?b. c = Normal b` by METIS_TAC [extreal_cases]
 >> POP_ASSUM (fn th => fs [th, extreal_of_num_def, extreal_mul_def,
                            extreal_not_infty])
 >> STRIP_ASSUME_TAC (Q.SPEC `b / e` SIMP_REAL_ARCH)
 >> Q.EXISTS_TAC `n`
 >> Q.X_GEN_TAC `m` >> DISCH_TAC
 >> `variance p (S (SUC m)) <= Normal (b * &SUC m)`
       by PROVE_TAC [REAL_MUL_COMM] (* `b * &n` in assumption *)
 >> `?v. variance p (S (SUC m)) = Normal v` by METIS_TAC [extreal_cases]
 >> `0 <= v` by METIS_TAC [variance_pos, extreal_of_num_def, extreal_le_eq]
 >> Q.PAT_X_ASSUM `_ = Normal v`
      (fn th => fs [th, extreal_of_num_def, extreal_le_eq,
                    extreal_mul_def, real_normal])
 >> Know `abs (v * inv (&SUC m) pow 2) = v * inv (&SUC m) pow 2`
 >- (rw [] >> MATCH_MP_TAC REAL_LE_MUL >> art [] \\
     MATCH_MP_TAC POW_POS \\
     MATCH_MP_TAC REAL_LT_IMP_LE \\
     MATCH_MP_TAC REAL_INV_POS >> RW_TAC real_ss []) >> Rewr'
 >> MATCH_MP_TAC REAL_LET_TRANS
 >> Q.EXISTS_TAC `b * (&SUC m) * inv (&SUC m) pow 2`
 >> CONJ_TAC
 >- (Know `(0 :real) < inv (&SUC m) pow 2`
     >- (MATCH_MP_TAC REAL_POW_LT \\
         MATCH_MP_TAC REAL_INV_POS >> RW_TAC real_ss []) \\
     DISCH_THEN (MP_TAC o (MATCH_MP REAL_LE_RMUL)) >> Rewr' >> art [])
 >> REWRITE_TAC [POW_2]
 >> `&n <= &m :real` by (RW_TAC real_ss [])
 >> `b / e <= &m` by PROVE_TAC [REAL_LE_TRANS]
 >> `b <= e * &m` by METIS_TAC [REAL_LE_LDIV_EQ, REAL_MUL_COMM]
 >> Know `(&SUC m) * inv (&SUC m) = (1 :real)`
 >- (MATCH_MP_TAC REAL_MUL_RINV >> RW_TAC real_ss []) >> DISCH_TAC
 >> REWRITE_TAC [REAL_MUL_ASSOC]
 >> Know `b * (&SUC m) * inv (&SUC m) = b`
 >- (ASM_SIMP_TAC real_ss [GSYM REAL_MUL_ASSOC]) >> Rewr'
 >> ONCE_REWRITE_TAC [REAL_MUL_COMM]
 >> Know `inv (&SUC m) * b < e <=> (&SUC m) * inv (&SUC m) * b < (&SUC m) * e`
 >- (MATCH_MP_TAC EQ_SYM \\
     ONCE_REWRITE_TAC [GSYM REAL_MUL_ASSOC] \\
     MATCH_MP_TAC REAL_LT_LMUL >> RW_TAC real_ss []) >> Rewr'
 >> POP_ORW
 >> rw [Once REAL_MUL_COMM]
 >> MATCH_MP_TAC REAL_LET_TRANS
 >> Q.EXISTS_TAC `e * &m` >> art []
 >> rw [REAL_LT_LMUL]
QED

(* Theorem 5.1.1, Part 2 [2, p.108] (L2 ==> PR)

   This proof shares some initial steps with WLLN_uncorrelated_L2, as
   we need to show that `(S (SUC n) x - M (SUC n)) / &SUC n` is indeed
   a (real-valued) random variable.
 *)
Theorem WLLN_uncorrelated :
    !p X S M. prob_space p /\ (!n. real_random_variable (X n) p) /\
       (!i j. i <> j ==> uncorrelated p (X i) (X j)) /\
       (?c. c <> PosInf /\ !n. variance p (X n) <= c) /\
       (!n x. S n x = SIGMA (\i. X i x) (count n)) /\
       (!n. M n = expectation p (S n)) ==>
       ((\n x. (S (SUC n) x - M (SUC n)) / &SUC n) --> (\x. 0)) (in_probability p)
Proof
    rpt STRIP_TAC
 >> irule converge_LP_imp_PR'
 >> Know `!n. integrable p (X n)`
 >- (GEN_TAC >> MATCH_MP_TAC finite_second_moments_imp_integrable >> art [] \\
     ASM_SIMP_TAC std_ss [finite_second_moments_eq_finite_variance] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC `c` >> rw [GSYM lt_infty]) >> DISCH_TAC
 >> Q.PAT_X_ASSUM `!n. real_random_variable (X n) p`
      (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
       (REWRITE_RULE [real_random_variable_def]))
 >> Know `!n x. S n x <> PosInf`
 >- (RW_TAC std_ss [] >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
     RW_TAC std_ss [FINITE_COUNT, IN_COUNT]) >> DISCH_TAC
 >> Know `!n x. S n x <> NegInf`
 >- (RW_TAC std_ss [] >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
     RW_TAC std_ss [FINITE_COUNT, IN_COUNT]) >> DISCH_TAC
 >> Know `!n. M n <> PosInf /\ M n <> NegInf`
 >- (GEN_TAC >> ASM_SIMP_TAC std_ss [expectation_def] \\
     MATCH_MP_TAC integrable_finite_integral \\
     CONJ_TAC >- fs [prob_space_def] \\
    `S n = \x. SIGMA (\i. X i x) (count n)` by METIS_TAC [] >> POP_ORW \\
     MATCH_MP_TAC integrable_sum \\
     RW_TAC std_ss [FINITE_COUNT, IN_COUNT] >> fs [prob_space_def])
 >> DISCH_TAC
 >> Know `!n x. S (SUC n) x - M (SUC n) <> PosInf /\
                S (SUC n) x - M (SUC n) <> NegInf`
 >- (rpt GEN_TAC \\
    `?a. S (SUC n) x = Normal a` by METIS_TAC [extreal_cases] >> POP_ORW \\
    `?b. M (SUC n) = Normal b` by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def]) >> DISCH_TAC
 >> CONJ_TAC
 >- (GEN_TAC >> BETA_TAC \\
     Know `!x. (S (SUC n) x - M (SUC n)) / &SUC n =
                 inv (&SUC n) * (S (SUC n) x - M (SUC n))`
     >- (GEN_TAC >> MATCH_MP_TAC div_eq_mul_linv \\
        `?a. S (SUC n) x = Normal a` by METIS_TAC [extreal_cases] >> POP_ORW \\
        `?b. M (SUC n) = Normal b` by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_sub_def] \\
         RW_TAC real_ss [extreal_lt_eq, extreal_of_num_def]) >> Rewr' \\
     Know `inv (&SUC n) = Normal (inv (&SUC n))`
     >- (`(0 :real) <> &SUC n` by RW_TAC real_ss [] \\
         ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_inv_eq]) >> Rewr' \\
     SIMP_TAC std_ss [real_random_variable] \\
     reverse CONJ_TAC
     >- (GEN_TAC \\
        `?a. S (SUC n) x = Normal a` by METIS_TAC [extreal_cases] >> POP_ORW \\
        `?b. M (SUC n) = Normal b` by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_sub_def, extreal_mul_def]) \\
    `sigma_algebra (p_space p,events p)`
       by METIS_TAC [prob_space_def, measure_space_def, p_space_def, events_def] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL \\
     qexistsl_tac [`\x. S (SUC n) x - M (SUC n)`, `inv (&SUC n)`] \\
     CONJ_TAC >- rw [] >> reverse CONJ_TAC >- rw [space_def] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
     qexistsl_tac [`S (SUC n)`, `\x. M (SUC n)`] \\
     CONJ_TAC >- rw [] >> SIMP_TAC std_ss [space_def] \\
     ONCE_REWRITE_TAC [CONJ_ASSOC] >> reverse CONJ_TAC >- rw [] \\
     reverse CONJ_TAC
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST' >> art []) \\
    `S (SUC n) = \x. SIGMA (\i. X i x) (count (SUC n))` by METIS_TAC [] >> POP_ORW \\
     MATCH_MP_TAC (INST_TYPE [``:'b`` |-> ``:num``] IN_MEASURABLE_BOREL_SUM) \\
     qexistsl_tac [`X`, `count (SUC n)`] \\
     RW_TAC std_ss [FINITE_COUNT, IN_COUNT] \\
     fs [random_variable_def])
 >> CONJ_TAC >- art [] (* prob_space p *)
 >> Q.EXISTS_TAC `2`
 >> MATCH_MP_TAC WLLN_uncorrelated_L2
 >> Q.EXISTS_TAC `X` >> RW_TAC std_ss [real_random_variable_def]
 >> Q.EXISTS_TAC `c` >> RW_TAC std_ss []
QED

(* Theorem 5.1.2 [2, p.108]: The Strong Law of Large Numbers

   (uncorrelated random sequence with a common bound of variances)

   without loss of generality we may suppose that expectation (X j) = 0 for
   each j, so that the (X j)'s are orthogonal.
 *)
Theorem SLLN_uncorrelated_wlog[local] :
    !p X S M c. prob_space p /\ (!n. real_random_variable (X n) p) /\
       (!i j. i <> j ==> uncorrelated p (X i) (X j)) /\
       c <> PosInf /\ (!n. variance p (X n) <= c) /\
       (!n x. S n x = SIGMA (\i. X i x) (count n)) /\
       (!n. M n = expectation p (S n)) ==>
       ?(Y :num -> 'a -> extreal) Z.
           (!n x. Z n x = SIGMA (\i. Y i x) (count n)) /\
           (!n x. S n x - M n = Z n x) /\
           (!n. expectation p (Y n) = 0) /\
           (!n. real_random_variable (Y n) p) /\
           (!n. finite_second_moments p (Y n)) /\
           (!n. variance p (Y n) <= c) /\
           (!n. integrable p (Y n)) /\
           (!i j. i <> j ==> orthogonal p (Y i) (Y j))
Proof
    rpt STRIP_TAC
 >> Know `!n. finite_second_moments p (X n)`
 >- (RW_TAC std_ss [finite_second_moments_eq_finite_variance] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC `c` >> rw [GSYM lt_infty]) >> DISCH_TAC
 >> Know `!n. integrable p (X n)`
 >- (GEN_TAC >> MATCH_MP_TAC finite_second_moments_imp_integrable >> art [])
 >> DISCH_TAC
 (* `Y n` is centered `X n` such that `!n. expectation p (Y n) = 0` *)
 >> Q.ABBREV_TAC `Y = \n x. X n x - expectation p (X n)`
 >> Know `!n. expectation p (Y n) = 0`
 >- (RW_TAC std_ss [Abbr `Y`, expectation_def] \\
     fs [real_random_variable_def] \\
    `!x. X n x - integral p (X n) = X n x + (\x. -integral p (X n)) x`
       by METIS_TAC [prob_space_def, integrable_finite_integral,
                     extreal_sub_add] >> POP_ORW \\
     Know `integral p (\x. X n x + (\x. -integral p (X n)) x) =
           integral p (X n) + integral p (\x. -integral p (X n))`
     >- (MATCH_MP_TAC integral_add \\
         fs [prob_space_def, p_space_def, integrable_finite_integral] \\
        `?r. integral p (X n) = Normal r` by METIS_TAC [integrable_normal_integral] \\
         POP_ORW >> rw [extreal_ainv_def, extreal_not_infty] \\
         MATCH_MP_TAC integrable_const >> rw [extreal_of_num_def, lt_infty]) >> Rewr' \\
    `?r. integral p (X n) = Normal r`
       by METIS_TAC [integrable_normal_integral, prob_space_def] \\
     ASM_SIMP_TAC std_ss [extreal_ainv_def, GSYM expectation_def, expectation_const] \\
     METIS_TAC [extreal_not_infty, sub_refl, GSYM extreal_ainv_def, extreal_sub_add])
 >> DISCH_TAC
 >> Know `!n. real_random_variable (Y n) p`
 >- (GEN_TAC >> Q.UNABBREV_TAC `Y` \\
     fs [real_random_variable, p_space_def, events_def] \\
     reverse CONJ_TAC
     >- (GEN_TAC \\
        `?a. X n x = Normal a` by METIS_TAC [extreal_cases] \\
        `?b. expectation p (X n) = Normal b` by METIS_TAC [expectation_normal] \\
         rw [extreal_sub_def, extreal_not_infty]) \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
     qexistsl_tac [`X n`, `\x. expectation p (X n)`] \\
     ASM_SIMP_TAC std_ss [expectation_finite, space_def] \\
     fs [prob_space_def, measure_space_def, expectation_finite, space_def,
         IN_MEASURABLE_BOREL_CONST']) >> DISCH_TAC
 >> Know `!n. finite_second_moments p (Y n) /\ variance p (Y n) <= c`
 >- (GEN_TAC \\
     ASM_SIMP_TAC std_ss [finite_second_moments_eq_finite_variance, Abbr `Y`] \\
    `expectation p (X n) <> PosInf /\
     expectation p (X n) <> NegInf` by METIS_TAC [expectation_finite] \\
    `variance p (\x. X n x - expectation p (X n)) = variance p (X n)`
       by METIS_TAC [variance_real_affine'] >> POP_ORW >> art [] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC `c` >> rw [GSYM lt_infty])
 >> DISCH_THEN (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV))
 >> `!n. integrable p (Y n)` by PROVE_TAC [finite_second_moments_imp_integrable]
 >> Know `!i j. i <> j ==> orthogonal p (Y i) (Y j)`
 >- (RW_TAC std_ss [orthogonal_def, Abbr `Y`] \\
     MATCH_MP_TAC uncorrelated_thm >> RW_TAC std_ss []) >> DISCH_TAC
 (* `Z n` is the parial sums of `Y n` *)
 >> Q.ABBREV_TAC `Z = \n x. SIGMA (\i. Y i x) (count n)`
 >> qexistsl_tac [`Y`, `Z`]
 >> RW_TAC std_ss [Abbr `Y`, Abbr `Z`]
 >> `!i. X i x - expectation p (X i) =
        (\i. X i x) i - (\i. expectation p (X i)) i` by METIS_TAC [] >> POP_ORW
 >> Know `SIGMA (\i. (\i. X i x) i - (\i. expectation p (X i)) i) (count n) =
          SIGMA (\i. X i x) (count n) -
          SIGMA (\i. expectation p (X i)) (count n)`
 >- (irule EXTREAL_SUM_IMAGE_SUB >> art [FINITE_COUNT, IN_COUNT] \\
     DISJ1_TAC (* or DISJ2_TAC *) >> fs [real_random_variable_def] \\
     METIS_TAC [expectation_finite]) >> Rewr'
 >> Suff `expectation p (S n) =
          SIGMA (\i. expectation p (X i)) (count n)` >- rw []
 >> `S n = \x. SIGMA (\i. X i x) (count n)` by METIS_TAC [] >> POP_ORW
 >> MATCH_MP_TAC (REWRITE_RULE [GSYM expectation_def] integral_sum)
 >> fs [FINITE_COUNT, prob_space_def, real_random_variable_def]
QED

Theorem SLLN_uncorrelated :
    !p X S M. prob_space p /\ (!n. real_random_variable (X n) p) /\
       (!i j. i <> j ==> uncorrelated p (X i) (X j)) /\
       (?c. c <> PosInf /\ !n. variance p (X n) <= c) /\
       (!n x. S n x = SIGMA (\i. X i x) (count n)) /\
       (!n. M n = expectation p (S n)) ==>
       ((\n x. (S (SUC n) x - M (SUC n)) / &SUC n) --> (\x. 0)) (almost_everywhere p)
Proof
    rpt STRIP_TAC
 (* without loss of generality *)
 >> MP_TAC (Q.SPECL [`p`, `X`, `S`, `M`, `c`] SLLN_uncorrelated_wlog)
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM `!n x. _ = Z n x` (ONCE_REWRITE_TAC o wrap)
 (* clean up X and S *)
 >> Q.PAT_X_ASSUM `!n. real_random_variable (X n) p`            K_TAC
 >> Q.PAT_X_ASSUM `!i j. i <> j ==> uncorrelated p (X i) (X j)` K_TAC
 >> Q.PAT_X_ASSUM `!n. variance p (X n) <= c`                   K_TAC
 >> Q.PAT_X_ASSUM `!n x. S n x = SIGMA (\i. X i x) (count n)`   K_TAC
 >> Q.PAT_X_ASSUM `!n. M n = expectation p (S n)`               K_TAC
 >> rename1 `!n x. S n x = SIGMA (\i. X i x) (count n)`
 >> rename1 `M <> PosInf`
 (* now the actual proof *)
 >> Know `0 <= M`
 >- (MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `variance p (X 0)` \\
     ASM_SIMP_TAC std_ss [variance_pos]) >> DISCH_TAC
 >> Know `M <> NegInf`
 >- (MATCH_MP_TAC pos_not_neginf >> art []) >> DISCH_TAC
 (* properties of (S n) *)
 >> Know `!n. variance p (S n) <= &n * M`
 >- (GEN_TAC \\
    `S n = \x. SIGMA (\i. X i x) (count n)` by METIS_TAC [] >> POP_ORW \\
     Know `variance p (\x. SIGMA (\i. X i x) (count n)) =
           SIGMA (\i. variance p (X i)) (count n)`
     >- (MATCH_MP_TAC variance_sum >> rw [FINITE_COUNT] \\
         RW_TAC std_ss [uncorrelated_vars_def] \\
         METIS_TAC [uncorrelated_orthogonal]) >> Rewr' \\
     Know `SIGMA (\x. M) (count n) = &CARD (count n) * M`
     >- (irule EXTREAL_SUM_IMAGE_FINITE_CONST >> rw [FINITE_COUNT]) \\
     REWRITE_TAC [Once EQ_SYM_EQ, CARD_COUNT] >> Rewr' \\
     irule EXTREAL_SUM_IMAGE_MONO >> rw [IN_COUNT, FINITE_COUNT] \\
     DISJ2_TAC >> GEN_TAC >> DISCH_TAC \\
     REWRITE_TAC [lt_infty] \\
     MATCH_MP_TAC let_trans >> Q.EXISTS_TAC `M` >> art [GSYM lt_infty])
 >> DISCH_TAC
 >> Know `!n. expectation p (S n) = 0`
 >- (GEN_TAC \\
    `S n = \x. SIGMA (\i. X i x) (count n)` by METIS_TAC [] >> POP_ORW \\
     fs [prob_space_def, real_random_variable_def, expectation_def,
         random_variable_def, p_space_def, events_def] \\
     Know `integral p (\x. SIGMA (\i. X i x) (count n)) =
           SIGMA (\i. integral p (X i)) (count n)`
     >- (MATCH_MP_TAC integral_sum \\
         RW_TAC std_ss [IN_COUNT, FINITE_COUNT]) >> Rewr' >> rw [] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_ZERO >> REWRITE_TAC [FINITE_COUNT])
 >> DISCH_TAC
 >> Know `!n x. S n x <> PosInf`
 >- (RW_TAC std_ss [] >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
     fs [real_random_variable_def, FINITE_COUNT, IN_COUNT]) >> DISCH_TAC
 >> Know `!n x. S n x <> NegInf`
 >- (RW_TAC std_ss [] >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
     fs [real_random_variable_def, FINITE_COUNT, IN_COUNT]) >> DISCH_TAC
 >> Know `!n. real_random_variable (S n) p`
 >- (RW_TAC std_ss [real_random_variable,
                    p_space_def, events_def] \\
    `S n = \x. SIGMA (\i. X i x) (count n)` by METIS_TAC [] >> POP_ORW \\
     MATCH_MP_TAC (INST_TYPE [``:'b`` |-> ``:num``] IN_MEASURABLE_BOREL_SUM) \\
     qexistsl_tac [`X`, `count n`] \\
     fs [real_random_variable, p_space_def,
         events_def, space_def, prob_space_def, measure_space_def]) >> DISCH_TAC
 >> Know `!n. finite_second_moments p (S n)`
 >- (RW_TAC std_ss [finite_second_moments_eq_finite_variance] \\
     MATCH_MP_TAC let_trans >> Q.EXISTS_TAC `&n * M` >> art [] \\
    `?r. M = Normal r` by METIS_TAC [extreal_cases] \\
     rw [extreal_not_infty, extreal_of_num_def, extreal_mul_def, GSYM lt_infty])
 >> DISCH_TAC
 (* applying chebyshev_ineq_variance *)
 >> Know `!n e. 0 < n /\ 0 < e /\ e <> PosInf ==>
             prob p ({x | &n * e <= abs (S n x - expectation p (S n))} INTER p_space p)
             <= inv ((&n * e) pow 2) * variance p (S n)`
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC chebyshev_ineq_variance >> art [] \\
     MATCH_MP_TAC lt_mul >> fs [extreal_of_num_def, extreal_lt_eq])
 >> Q.PAT_ASSUM `!n. expectation p (S n) = 0` (ONCE_REWRITE_TAC o wrap)
 >> REWRITE_TAC [sub_rzero] >> DISCH_TAC
 >> Know `!n e. 0 < n /\ 0 < e /\ e <> PosInf ==>
             prob p ({x | &n * e <= abs (S n x)} INTER p_space p)
             <= inv ((&n * e) pow 2) * (&n * M)`
 >- (rpt STRIP_TAC >> MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `inv ((&n * e) pow 2) * variance p (S n)` \\
     CONJ_TAC >- ASM_SIMP_TAC std_ss [] \\
     MATCH_MP_TAC le_lmul_imp >> art [] \\
     MATCH_MP_TAC le_inv \\
     MATCH_MP_TAC pow_pos_lt \\
     MATCH_MP_TAC lt_mul >> fs [extreal_of_num_def, extreal_lt_eq])
 >> POP_ASSUM K_TAC >> DISCH_TAC
 >> Know `!n e. 0 < n /\ 0 < e /\ e <> PosInf ==>
             prob p ({x | &n * e <= abs (S n x)} INTER p_space p)
             <= inv (&n * e pow 2) * M`
 >- (rpt STRIP_TAC \\
     Suff `inv (&n * e pow 2) * M = inv ((&n * e) pow 2) * (&n * M)`
     >- (Rewr' >> FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
    `&n <> (0 :real)` by RW_TAC real_ss [] \\
    `e <> NegInf` by METIS_TAC [lt_le, pos_not_neginf] \\
    `?a. e = Normal a` by METIS_TAC [extreal_cases] \\
     Know `0 < &n * e pow 2`
     >- (MATCH_MP_TAC lt_mul \\
         CONJ_TAC >- (rw [extreal_of_num_def, extreal_lt_eq]) \\
         MATCH_MP_TAC pow_pos_lt >> art []) >> DISCH_TAC \\
    `&n * e pow 2 <> 0` by PROVE_TAC [lt_imp_ne] \\
    `?m. M = Normal m` by METIS_TAC [extreal_cases] \\
     ASM_SIMP_TAC std_ss [extreal_inv_eq, extreal_of_num_def, extreal_mul_def,
                          extreal_pow_def] \\
     Know `0 < (&n * a) pow 2`
     >- (MATCH_MP_TAC REAL_POW_LT \\
         MATCH_MP_TAC REAL_LT_MUL \\
         FULL_SIMP_TAC real_ss [extreal_of_num_def, extreal_lt_eq]) >> DISCH_TAC \\
    `(&n * a) pow 2 <> 0` by PROVE_TAC [REAL_LT_IMP_NE] \\
     Know `0 < a pow 2`
     >- (MATCH_MP_TAC REAL_POW_LT \\
         METIS_TAC [extreal_of_num_def, extreal_lt_eq]) >> DISCH_TAC \\
    `a pow 2 <> 0` by PROVE_TAC [REAL_LT_IMP_NE] \\
     Know `0 < &n * a pow 2`
     >- (MATCH_MP_TAC REAL_LT_MUL >> rw []) >> DISCH_TAC \\
    `&n * a pow 2 <> 0` by PROVE_TAC [REAL_LT_IMP_NE] \\
     FULL_SIMP_TAC real_ss [extreal_inv_eq, extreal_mul_def,
                           extreal_11, REAL_INV_MUL, REAL_ENTIRE, POW_2] \\
    `&n <> (0 :real)` by RW_TAC real_ss [] \\
     rw [nonzerop_def])
 >> POP_ASSUM K_TAC >> DISCH_TAC
 >> Know `!n e. 0 < n /\ 0 < e /\ e <> PosInf ==>
             prob p {x | x IN p_space p /\ &n * e < abs (S n x)}
             <= inv (&n * e pow 2) * M`
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `prob p ({x | &n * e <= abs (S n x)} INTER p_space p)` \\
     reverse CONJ_TAC
     >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     Q.ABBREV_TAC `f = \x. abs (S n x)` \\
    `!x. abs (S n x) = f x` by METIS_TAC [] >> POP_ORW \\
     Q.ABBREV_TAC `P = \x. &n * e < f x` \\
    `!x. (&n * e < f x) <=> P x` by METIS_TAC [] >> POP_ORW \\
     SIMP_TAC std_ss [PROB_GSPEC, Abbr `P`] \\
     MATCH_MP_TAC PROB_INCREASING \\
     CONJ_TAC >- art [] (* prob_space p *) \\
     Know `f IN measurable (m_space p,measurable_sets p) Borel`
     >- (Q.UNABBREV_TAC `f` \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS \\
         Q.EXISTS_TAC `S n` \\
         fs [space_def, real_random_variable,
             p_space_def, events_def, prob_space_def, measure_space_def]) \\
     DISCH_TAC \\
     ASM_SIMP_TAC std_ss [p_space_def, events_def,
                          IN_MEASURABLE_BOREL_ALL_MEASURE] \\
     rw [SUBSET_DEF, IN_INTER, GSPECIFICATION] \\
     MATCH_MP_TAC lt_imp_le >> art [])
 >> Know `!n e. {x | x IN p_space p /\ &n * e < abs (S n x)} IN events p`
 >- (rpt GEN_TAC >> Q.ABBREV_TAC `f = \x. abs (S n x)` \\
    `!x. abs (S n x) = f x` by METIS_TAC [] >> POP_ORW \\
     Know `f IN measurable (m_space p,measurable_sets p) Borel`
     >- (Q.UNABBREV_TAC `f` \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS \\
         Q.EXISTS_TAC `S n` \\
         fs [space_def, real_random_variable,
             p_space_def, events_def, prob_space_def, measure_space_def]) \\
     DISCH_TAC \\
    `{x | x IN p_space p /\ &n * e < f x} =
     {x | &n * e < f x} INTER p_space p` by SET_TAC [] >> POP_ORW \\
     ASM_SIMP_TAC std_ss [p_space_def, events_def,
                          IN_MEASURABLE_BOREL_ALL_MEASURE])
 >> POP_ASSUM K_TAC >> rpt DISCH_TAC
 (* applying Borel_Cantelli_Lemma1 *)
 >> Q.ABBREV_TAC `E = \e n. {x | x IN p_space p /\
                                 &(SUC n ** 2) * e < abs (S (SUC n ** 2) x)}`
 >> Know `!e. 0 < e /\ e <> PosInf ==> (prob p (limsup (E e)) = 0)`
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC Borel_Cantelli_Lemma1 >> art [] \\
     CONJ_TAC >- (GEN_TAC >> Q.UNABBREV_TAC `E` >> BETA_TAC >> art []) \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC `suminf (\n. inv (&(SUC n ** 2) * e pow 2) * M)` \\
     CONJ_TAC (* mono *)
     >- (MATCH_MP_TAC ext_suminf_mono \\
         Q.UNABBREV_TAC `E` >> SIMP_TAC std_ss [o_DEF] \\
         CONJ_TAC >- (GEN_TAC >> MATCH_MP_TAC PROB_POSITIVE >> art []) \\
         GEN_TAC >> FIRST_X_ASSUM MATCH_MP_TAC >> RW_TAC arith_ss []) \\
     Know `!n. inv (&(SUC n ** 2) * e pow 2) * M =
               inv (e pow 2) * M * (\n. inv (&(SUC n) pow 2)) n`
     >- (RW_TAC std_ss [] \\
         Know `&(SUC n ** 2) = &SUC n pow 2`
         >- (REWRITE_TAC [pow_2] \\
             REWRITE_TAC [EXP, ONE, TWO, MULT_ASSOC] \\
             RW_TAC real_ss [extreal_mul_def, extreal_of_num_def]) >> Rewr' \\
        `0 < e pow 2` by PROVE_TAC [pow_pos_lt] \\
         Know `0 < &SUC n pow 2`
         >- (MATCH_MP_TAC pow_pos_lt \\
             RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq]) >> DISCH_TAC \\
        `e pow 2 <> 0 /\ &SUC n pow 2 <> 0` by METIS_TAC [lt_imp_ne] \\
         ASM_SIMP_TAC real_ss [inv_mul] \\
         METIS_TAC [mul_comm, mul_assoc]) >> Rewr' \\
     Q.ABBREV_TAC `f = \n. inv (&SUC n pow 2)` \\
     Know `0 <= suminf f`
     >- (MATCH_MP_TAC ext_suminf_pos \\
         RW_TAC std_ss [Abbr `f`] \\
         MATCH_MP_TAC le_inv \\
         MATCH_MP_TAC pow_pos_lt \\
         RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq]) >> DISCH_TAC \\
     Know `suminf (\n. inv (e pow 2) * M * f n) = inv (e pow 2) * M * suminf f`
     >- (MATCH_MP_TAC ext_suminf_cmul \\
         CONJ_TAC >- (MATCH_MP_TAC le_mul >> art [] \\
                      MATCH_MP_TAC le_inv \\
                      MATCH_MP_TAC pow_pos_lt >> art []) \\
         RW_TAC std_ss [Abbr `f`] \\
         MATCH_MP_TAC le_inv \\
         MATCH_MP_TAC pow_pos_lt \\
         RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq]) >> Rewr' \\
    `suminf f <> NegInf` by METIS_TAC [pos_not_neginf] \\
     Know `suminf f <> PosInf`
     >- (Q.UNABBREV_TAC `f` >> REWRITE_TAC [lt_infty] \\
         REWRITE_TAC [harmonic_series_pow_2]) >> DISCH_TAC \\
     REWRITE_TAC [GSYM lt_infty] \\
     Know `inv (e pow 2) <> PosInf /\ inv (e pow 2) <> NegInf`
     >- (MATCH_MP_TAC inv_not_infty \\
         Suff `0 < e pow 2` >- METIS_TAC [lt_imp_ne] \\
         MATCH_MP_TAC pow_pos_lt >> art []) >> STRIP_TAC \\
    `?a. inv (e pow 2) = Normal a` by METIS_TAC [extreal_cases] \\
    `?b. M = Normal b` by METIS_TAC [extreal_cases] \\
    `?c. suminf f = Normal c` by METIS_TAC [extreal_cases] \\
     ASM_SIMP_TAC std_ss [extreal_mul_def, extreal_not_infty])
 >> Q.UNABBREV_TAC `E` >> BETA_TAC
 >> Know `!e n x. &(SUC n ** 2) * e < abs (S (SUC n ** 2) x) <=>
                  e < abs (S (SUC n ** 2) x / &(SUC n ** 2))`
 >- (rpt GEN_TAC \\
     Know `abs (S (SUC n ** 2) x / &(SUC n ** 2)) =
           abs (S (SUC n ** 2) x) / abs &(SUC n ** 2)`
     >- (MATCH_MP_TAC abs_div >> art [] \\
         RW_TAC real_ss [extreal_of_num_def, extreal_11]) >> Rewr' \\
     Know `abs (&(SUC n ** 2)) = &(SUC n ** 2)`
     >- (REWRITE_TAC [abs_refl] \\
         RW_TAC real_ss [extreal_of_num_def, extreal_le_eq]) >> Rewr' \\
    `0 < &(SUC n ** 2)` by RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq] \\
    `&(SUC n ** 2) <> PosInf` by METIS_TAC [num_not_infty] \\
     Know `e < abs (S (SUC n ** 2) x) / &(SUC n ** 2) <=>
           e * &(SUC n ** 2) <
           abs (S (SUC n ** 2) x) / &(SUC n ** 2) * &(SUC n ** 2)`
     >- (MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC lt_rmul >> art []) >> Rewr' \\
    `&(SUC n ** 2) <> 0` by METIS_TAC [lt_imp_ne] \\
    `&(SUC n ** 2) <> NegInf` by METIS_TAC [num_not_infty] \\
    `?r. &(SUC n ** 2) = Normal r` by METIS_TAC [extreal_cases] \\
    `r <> 0` by METIS_TAC [extreal_of_num_def, extreal_11] \\
     Q.PAT_X_ASSUM `_ = Normal r` (ONCE_REWRITE_TAC o wrap) \\
     Know `abs (S (SUC n ** 2) x) / Normal r * Normal r = abs (S (SUC n ** 2) x)`
     >- (MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC div_mul_refl >> art []) >> Rewr' \\
     REWRITE_TAC [Once mul_comm]) >> Rewr'
 (* applying converge_AE_alt_limsup *)
 >> Q.ABBREV_TAC `Z = \n x. S (SUC n ** 2) x / &(SUC n ** 2)`
 >> `!n x. S (SUC n ** 2) x / &(SUC n ** 2) = Z n x`
        by METIS_TAC [] >> POP_ORW
 >> Q.PAT_X_ASSUM `!n e. 0 < n /\ 0 < e /\ e <> PosInf ==> P` K_TAC
 >> DISCH_TAC
 >> Know `!n. real_random_variable (Z n) p`
 >- (GEN_TAC \\
     SIMP_TAC std_ss [real_random_variable, Abbr `Z`] \\
    `0 < &(SUC n ** 2)` by RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq] \\
    `&(SUC n ** 2) <> 0` by METIS_TAC [lt_imp_ne] \\
    `&(SUC n ** 2) <> PosInf` by METIS_TAC [num_not_infty] \\
    `&(SUC n ** 2) <> NegInf` by METIS_TAC [num_not_infty] \\
    `?r. &(SUC n ** 2) = Normal r` by METIS_TAC [extreal_cases] \\
    `r <> 0` by METIS_TAC [extreal_of_num_def, extreal_11] \\
     Q.PAT_X_ASSUM `_ = Normal r` (ONCE_REWRITE_TAC o wrap) \\
    `!z. z / Normal r = z * inv (Normal r)` by METIS_TAC [extreal_div_def] \\
     POP_ORW \\
    `inv (Normal r) = Normal (inv r)` by METIS_TAC [extreal_inv_def] >> POP_ORW \\
     reverse CONJ_TAC
     >- (GEN_TAC \\
        `?a. S (SUC n ** 2) x = Normal a` by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_mul_def, extreal_not_infty]) \\
     ONCE_REWRITE_TAC [mul_comm] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL \\
     qexistsl_tac [`S (SUC n ** 2)`, `inv r`] \\
     fs [real_random_variable, p_space_def, events_def,
         prob_space_def, measure_space_def, space_def]) >> DISCH_TAC
 >> Know `(Z --> (\x. 0)) (almost_everywhere p)`
 >- (MP_TAC (SIMP_RULE std_ss [sub_rzero]
                       (Q.SPECL [`p`, `Z`, `\x. 0`] converge_AE_alt_limsup)) \\
    `real_random_variable (\x. 0) p` by PROVE_TAC [real_random_variable_zero] \\
     RW_TAC std_ss []) >> DISCH_TAC
 >> Q.PAT_X_ASSUM `!e. 0 < e /\ e <> PosInf ==> P` K_TAC
 (* preparing for "method of subsequences" *)
 >> Q.ABBREV_TAC `N = \n. {k | n ** 2 <= k /\ k < SUC n ** 2}`
 >> Know `!n m. FINITE {k | n ** 2 <= k /\ k < m}`
 >- (rpt GEN_TAC \\
     irule SUBSET_FINITE >> Q.EXISTS_TAC `count m` \\
     rw [FINITE_COUNT, count_def, SUBSET_DEF]) >> DISCH_TAC
 >> `!n. FINITE (N n)` by (RW_TAC std_ss [Abbr `N`])
 >> Q.ABBREV_TAC `d = \n k x. abs (S k x - S (&(n ** 2)) x)`
 >> Know `!n k x. d n k x <> PosInf /\ d n k x <> NegInf`
 >- (rpt GEN_TAC >> SIMP_TAC std_ss [Abbr `d`] \\
    `?a. S k x = Normal a` by METIS_TAC [extreal_cases] \\
    `?b. S (n ** 2) x = Normal b` by METIS_TAC [extreal_cases] \\
     ASM_SIMP_TAC std_ss [extreal_sub_def, extreal_abs_def,
                          extreal_not_infty]) >> DISCH_TAC
 >> Q.ABBREV_TAC `D = \n x. sup (IMAGE (\k. d n k x) (N n))`
 (* NOTE: for different x, the maximal k may be different *)
 >> Know `!n x. ?k. n ** 2 <= k /\ k < SUC n ** 2 /\ D n x = d n k x`
 >- (rpt GEN_TAC \\
     Know `D n x IN (IMAGE (\k. d n k x) {k | n ** 2 <= k /\ k < SUC n ** 2})`
     >- (RW_TAC std_ss [Abbr `D`, Abbr `N`] \\
         MATCH_MP_TAC sup_maximal \\
         reverse CONJ_TAC
         >- (rw [Once EXTENSION, NOT_IN_EMPTY, IN_IMAGE] \\
             Q.EXISTS_TAC `n ** 2` >> rw []) \\
         MATCH_MP_TAC IMAGE_FINITE >> art []) \\
     rw [IN_IMAGE] >> Q.EXISTS_TAC `k` >> art []) >> DISCH_TAC
 (* now k becomes a function f of n and x, and from now on the original
    definition of `d` is not needed. *)
 >> POP_ASSUM (STRIP_ASSUME_TAC o (SIMP_RULE std_ss [SKOLEM_THM]))
 (* HARD: now finding the upper bound of E[D(n)^2] *)
 >> Know `!n. expectation p (\x. D n x pow 2) <=
              SIGMA (\k. expectation p (\x. (d n k x) pow 2)) (N n)`
 >- (GEN_TAC >> art [expectation_def] \\
  (* Here we have to prove:

     integral p (\x. (d n (f n x) x) pow 2) <=
       SIGMA (\k. integral p (\x. (d n k x) pow 2))
             {k | n ** 2 <= k /\ k < (SUC n) ** 2}

     The tricky part is, we cannot just pick one element from the RHS in SIGMA
     (which equals LHS) and prove the inequality by showing all other elements
     are non-negative, because the `k` (= f n x) at LHS is a function of x, i.e.
     for each point in the integration the corresponding k is jumping. The
     solution is to put SIGMA inside the integral first (by integral_sum).
   *)
     Know `!k.       integral p (\x. (d n k x) pow 2) =
              pos_fn_integral p (\x. (d n k x) pow 2)`
     >- (GEN_TAC >> MATCH_MP_TAC integral_pos_fn \\
         fs [le_pow2, prob_space_def]) >> Rewr' \\
     Know `       integral p (\x. (d n (f n x) x) pow 2) =
           pos_fn_integral p (\x. (d n (f n x) x) pow 2)`
     >- (MATCH_MP_TAC integral_pos_fn >> fs [le_pow2, prob_space_def]) >> Rewr' \\
     Know `SIGMA (\k. pos_fn_integral p ((\k x. d n k x pow 2) k)) (N n) =
           pos_fn_integral p (\x. SIGMA (\k. (\k x. d n k x pow 2) k x) (N n))`
     >- (MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC pos_fn_integral_sum \\
         fs [prob_space_def, p_space_def, le_pow2, real_random_variable_def,
             random_variable_def, events_def] \\
         RW_TAC set_ss [Abbr `N`, Abbr `d`, abs_pow2] \\
         Know `DISJOINT {k | n ** 2 <= k /\ k < i} (count (n ** 2))`
         >- (RW_TAC set_ss [DISJOINT_ALT, IN_COUNT] >> rw []) >> DISCH_TAC \\
         Know `count i = {k | n ** 2 <= k /\ k < i} UNION (count (n ** 2))`
         >- (RW_TAC set_ss [Once EXTENSION, IN_COUNT] >> rw []) >> Rewr' \\
         Know `!x. SIGMA (\i. X i x) ({k | n ** 2 <= k /\ k < i} UNION (count (n ** 2))) =
                   SIGMA (\i. X i x) {k | n ** 2 <= k /\ k < i} +
                   SIGMA (\i. X i x) (count (n ** 2))`
         >- (GEN_TAC \\
             irule EXTREAL_SUM_IMAGE_DISJOINT_UNION >> rw [FINITE_COUNT]) >> Rewr' \\
         Know `!x. SIGMA (\i. X i x) (count (n ** 2)) <> PosInf`
         >- (GEN_TAC >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
             rw [FINITE_COUNT]) >> DISCH_TAC \\
         Know `!x. SIGMA (\i. X i x) (count (n ** 2)) <> NegInf`
         >- (GEN_TAC >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
             rw [FINITE_COUNT]) >> DISCH_TAC \\
         Know `!x. SIGMA (\i. X i x) {k | n ** 2 <= k /\ k < i} +
                   SIGMA (\i. X i x) (count (n ** 2)) -
                   SIGMA (\i. X i x) (count (n ** 2)) =
                   SIGMA (\i. X i x) {k | n ** 2 <= k /\ k < i}`
         >- (GEN_TAC >> MATCH_MP_TAC add_sub >> art []) >> Rewr' \\
         HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_POW \\
         CONJ_TAC >- fs [measure_space_def] \\
         reverse CONJ_TAC
         >- (RW_TAC std_ss [space_def] >| (* 2 subgoals *)
             [ (* goal 1 (of 2) *)
               MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
               ASM_SIMP_TAC set_ss [],
               (* goal 2 (of 2) *)
               MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
               ASM_SIMP_TAC set_ss [] ]) \\
         MATCH_MP_TAC (INST_TYPE [``:'b`` |-> ``:num``] IN_MEASURABLE_BOREL_SUM) \\
         qexistsl_tac [`X`, `{k | n ** 2 <= k /\ k < i}`] \\
         fs [space_def, measure_space_def]) >> BETA_TAC >> Rewr' \\
     MATCH_MP_TAC pos_fn_integral_mono \\
     RW_TAC std_ss [le_pow2] \\
    `DISJOINT {f n x} (N n DELETE (f n x))` by SET_TAC [] \\
     Know `{f n x} UNION (N n DELETE (f n x)) = N n`
     >- (Suff `f n x IN (N n)` >- SET_TAC [] \\
         RW_TAC set_ss [Abbr `N`]) >> DISCH_TAC \\
     Know `SIGMA (\k. (d n k x) pow 2) ({f n x} UNION (N n DELETE (f n x))) =
           SIGMA (\k. (d n k x) pow 2) {f n x} +
           SIGMA (\k. (d n k x) pow 2) (N n DELETE (f n x))`
     >- (irule EXTREAL_SUM_IMAGE_DISJOINT_UNION >> fs [FINITE_SING] \\
         DISJ1_TAC >> RW_TAC std_ss [] \\ (* 2 subgoals, same tactics *)
         (MATCH_MP_TAC pos_not_neginf >> rw [le_pow2])) >> POP_ORW >> Rewr' \\
     SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_SING] \\
     MATCH_MP_TAC le_addr_imp \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> fs [le_pow2]) >> DISCH_TAC
 >> Know `!n. expectation p (\x. D n x pow 2) <=
              SIGMA (\k. expectation p (\x. (d n (SUC n ** 2) x) pow 2)) (N n)`
 >- (GEN_TAC >> MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `SIGMA (\k. expectation p (\x. (d n k x) pow 2)) (N n)` \\
     POP_ASSUM (REWRITE_TAC o wrap) \\
     irule EXTREAL_SUM_IMAGE_MONO >> art [] \\
     reverse CONJ_TAC
     >- (DISJ1_TAC >> GEN_TAC >> DISCH_TAC \\
         RW_TAC std_ss [expectation_def] \\ (* 2 subgoals, same tactics *)
         (MATCH_MP_TAC pos_not_neginf \\
          MATCH_MP_TAC integral_pos >> fs [prob_space_def, le_pow2])) \\
     RW_TAC set_ss [Abbr `N`, Abbr `d`, abs_pow2] \\
     rename1 `n ** 2 <= k` \\
     Know `count k = {j | n ** 2 <= j /\ j < k} UNION (count (n ** 2))`
     >- (RW_TAC set_ss [Once EXTENSION, IN_COUNT] >> rw []) >> Rewr' \\
     Know `DISJOINT {j | n ** 2 <= j /\ j < k} (count (n ** 2))`
     >- (RW_TAC set_ss [DISJOINT_ALT, IN_COUNT] >> rw []) >> DISCH_TAC \\
     Know `count (SUC n ** 2) = {j | n ** 2 <= j /\ j < SUC n ** 2} UNION (count (n ** 2))`
     >- (RW_TAC set_ss [Once EXTENSION, IN_COUNT] >> rw []) >> Rewr' \\
     Know `DISJOINT {j | n ** 2 <= j /\ j < SUC n ** 2} (count (n ** 2))`
     >- (RW_TAC set_ss [DISJOINT_ALT, IN_COUNT] >> rw []) >> DISCH_TAC \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
     Know `!x. SIGMA (\i. X i x) ({j | n ** 2 <= j /\ j < k} UNION (count (n ** 2))) =
               SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < k} +
               SIGMA (\i. X i x) (count (n ** 2))`
     >- (GEN_TAC >> irule EXTREAL_SUM_IMAGE_DISJOINT_UNION \\
         rw [FINITE_SING, FINITE_COUNT]) >> Rewr' \\
     Know `!x. SIGMA (\i. X i x)
                     ({j | n ** 2 <= j /\ j < SUC n ** 2} UNION (count (n ** 2))) =
               SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < SUC n ** 2} +
               SIGMA (\i. X i x) (count (n ** 2))`
     >- (GEN_TAC >> irule EXTREAL_SUM_IMAGE_DISJOINT_UNION \\
         fs [FINITE_SING, FINITE_COUNT]) >> Rewr' \\
     Know `!x. SIGMA (\i. X i x) (count (n ** 2)) <> PosInf`
     >- (GEN_TAC >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
         rw [FINITE_COUNT]) >> DISCH_TAC \\
     Know `!x. SIGMA (\i. X i x) (count (n ** 2)) <> NegInf`
     >- (GEN_TAC >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
         rw [FINITE_COUNT]) >> DISCH_TAC \\
     rw [add_sub] \\
     (* now converting LHS and RHS to variances *)
     Know `!m x. SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < m} =
                 (\x. SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < m}) x -
                 expectation p (\x. SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < m})`
     >- (rpt GEN_TAC \\
         Suff `expectation p (\x. SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < m}) = 0`
         >- rw [sub_rzero] \\
         REWRITE_TAC [expectation_def] \\
         Know `integral p (\x. SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < m}) =
               SIGMA (\i. integral p (X i)) {j | n ** 2 <= j /\ j < m}`
         >- (MATCH_MP_TAC integral_sum \\
             fs [prob_space_def, expectation_def]) >> Rewr' \\
         fs [expectation_def] \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_ZERO >> art []) >> Rewr' \\
     REWRITE_TAC [GSYM variance_alt] \\
     Know `!m. variance p (\x. SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < m}) =
               SIGMA (\i. variance p (X i)) {j | n ** 2 <= j /\ j < m}`
     >- (GEN_TAC >> MATCH_MP_TAC variance_sum \\
         rw [uncorrelated_vars_def, real_random_variable_def] \\
         METIS_TAC [REWRITE_RULE [real_random_variable_def]
                                 uncorrelated_orthogonal]) >> Rewr' \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET \\
     ASM_SIMP_TAC std_ss [variance_pos] \\
     RW_TAC set_ss [SUBSET_DEF] \\
     MATCH_MP_TAC LESS_TRANS >> Q.EXISTS_TAC `k` >> art [])
 >> POP_ASSUM K_TAC
 >> Know `!n k. expectation p (\x. (d n (SUC n ** 2) x) pow 2) =
                variance p (\x. SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < SUC n ** 2})`
 >- (RW_TAC std_ss [Abbr `d`, variance_alt, abs_pow2] \\
     Know `count (SUC n ** 2) = (N n) UNION (count (n ** 2))`
     >- (RW_TAC set_ss [Abbr `N`, Once EXTENSION, IN_COUNT] \\
         EQ_TAC >> RW_TAC arith_ss [] \\
         MATCH_MP_TAC LESS_TRANS >> Q.EXISTS_TAC `n ** 2` >> rw []) >> Rewr' \\
     Know `DISJOINT (N n) (count (n ** 2))`
     >- (RW_TAC set_ss [Abbr `N`, DISJOINT_ALT, IN_COUNT] >> rw []) >> DISCH_TAC \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
     Know `!x. SIGMA (\i. X i x) (N n UNION (count (n ** 2))) =
               SIGMA (\i. X i x) (N n) + SIGMA (\i. X i x) (count (n ** 2))`
     >- (GEN_TAC >> irule EXTREAL_SUM_IMAGE_DISJOINT_UNION \\
         fs [FINITE_SING, FINITE_COUNT]) >> Rewr' \\
     Know `!x. SIGMA (\i. X i x) (count (n ** 2)) <> PosInf`
     >- (GEN_TAC >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
         rw [FINITE_COUNT]) >> DISCH_TAC \\
     Know `!x. SIGMA (\i. X i x) (count (n ** 2)) <> NegInf`
     >- (GEN_TAC >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
         rw [FINITE_COUNT]) >> DISCH_TAC \\
     rw [add_sub] \\
     Suff `expectation p (\x. SIGMA (\i. X i x) (N n)) = 0` >- rw [sub_rzero] \\
     RW_TAC std_ss [expectation_def, Abbr `N`] \\
     Know `integral p (\x. SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < SUC n ** 2}) =
                SIGMA (\i. integral p (X i)) {j | n ** 2 <= j /\ j < SUC n ** 2}`
     >- (MATCH_MP_TAC integral_sum \\
         fs [prob_space_def, expectation_def]) >> Rewr' \\
     FULL_SIMP_TAC std_ss [expectation_def] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_ZERO >> art []) >> Rewr'
 >> Know `!n. SIGMA (\k. variance p (\x. SIGMA (\i. X i x)
                                         {j | n ** 2 <= j /\ j < SUC n ** 2})) (N n) =
              &CARD (N n) * (variance p (\x. SIGMA (\i. X i x)
                                             {j | n ** 2 <= j /\ j < SUC n ** 2}))`
 >- (GEN_TAC >> irule EXTREAL_SUM_IMAGE_FINITE_CONST \\
     ASM_SIMP_TAC std_ss [] \\
     DISJ1_TAC >> MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC variance_pos >> art []) >> Rewr'
 >> Know `!n. variance p (\x. SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < SUC n ** 2}) =
                   SIGMA (\i. variance p (X i)) (N n)`
 >- (RW_TAC std_ss [Abbr `N`] >> MATCH_MP_TAC variance_sum \\
     rw [uncorrelated_vars_def, real_random_variable_def] \\
     METIS_TAC [uncorrelated_orthogonal]) >> Rewr'
 >> DISCH_TAC
 >> Know `!n. expectation p (\x. (D n x) pow 2) <= &CARD (N n) * SIGMA (\i. M) (N n)`
 >- (GEN_TAC >> MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `&CARD (N n) * (SIGMA (\i. variance p (X i)) (N n))` >> art [] \\
     MATCH_MP_TAC le_lmul_imp \\
     CONJ_TAC >- RW_TAC real_ss [extreal_of_num_def, extreal_le_eq] \\
     irule EXTREAL_SUM_IMAGE_MONO >> ASM_SIMP_TAC std_ss [] \\
     DISJ1_TAC >> GEN_TAC >> DISCH_TAC \\
     MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC variance_pos >> art [])
 >> POP_ASSUM K_TAC
 >> Know `!n. SIGMA (\i. M) (N n) = &CARD (N n) * M`
 >- (GEN_TAC >> irule EXTREAL_SUM_IMAGE_FINITE_CONST \\
     ASM_SIMP_TAC std_ss []) >> Rewr'
 >> REWRITE_TAC [mul_assoc, GSYM pow_2]
 >> Know `!n. CARD (N n) = 2 * n + 1`
 >- (RW_TAC std_ss [Abbr `N`] \\
     Know `{k | n ** 2 <= k /\ k < SUC n ** 2} = (count (SUC n ** 2)) DIFF (count (n ** 2))`
     >- (RW_TAC set_ss [Once EXTENSION] >> rw []) >> Rewr' \\
     Know `CARD (count (SUC n ** 2) DIFF (count (n ** 2))) =
           CARD (count (SUC n ** 2)) - CARD (count (SUC n ** 2) INTER (count (n ** 2)))`
     >- (MATCH_MP_TAC CARD_DIFF_EQN >> REWRITE_TAC [FINITE_COUNT]) >> Rewr' \\
     Know `count (SUC n ** 2) INTER (count (n ** 2)) = count (n ** 2)`
     >- (RW_TAC set_ss [Once EXTENSION, IN_COUNT] \\
         EQ_TAC >> RW_TAC arith_ss [] \\
         MATCH_MP_TAC LESS_TRANS >> Q.EXISTS_TAC `n ** 2` >> rw []) >> Rewr' \\
     REWRITE_TAC [CARD_COUNT, ADD1, SUM_SQUARED] >> rw []) >> Rewr'
 >> DISCH_TAC
 (* stage work, now prove the AE convergence of D(n)/n^2 *)
 >> Q.ABBREV_TAC `W = (\n x. D (SUC n) x / &(SUC n ** 2))`
 >> Know `!n. real_random_variable (W n) p`
 >- (GEN_TAC \\
     SIMP_TAC std_ss [Abbr `W`, real_random_variable_def,
                      random_variable_def, p_space_def, events_def] \\
     reverse CONJ_TAC
     >- (GEN_TAC >> art [extreal_of_num_def] \\
        `?r. d (SUC n) (f (SUC n) x) x = Normal r` by METIS_TAC [extreal_cases] \\
         POP_ORW \\
         Suff `&(SUC n ** 2) <> (0 :real)`
         >- METIS_TAC [extreal_div_eq, extreal_not_infty] \\
         rw []) \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL \\
     qexistsl_tac [`D (SUC n)`, `inv (&(SUC n ** 2))`] \\
     fs [prob_space_def, measure_space_def, p_space_def, events_def, space_def] \\
     reverse CONJ_TAC
     >- (RW_TAC std_ss [extreal_of_num_def] \\
        `&(SUC n ** 2) <> (0 :real)` by RW_TAC real_ss [] \\
         ASM_SIMP_TAC real_ss [GSYM extreal_inv_def] \\
         MATCH_MP_TAC div_eq_mul_linv \\
         rw [extreal_of_num_def, extreal_lt_eq]) \\
     NTAC 2 (POP_ASSUM K_TAC) \\
     Q.UNABBREV_TAC `D` >> BETA_TAC \\
     irule (INST_TYPE [``:'b`` |-> ``:num``] IN_MEASURABLE_BOREL_MAXIMAL) >> art [] \\
     qexistsl_tac [`N (SUC n)`, `d (SUC n)`] \\
     ASM_SIMP_TAC std_ss [] \\
     Q.X_GEN_TAC `k` >> Q.UNABBREV_TAC `d` >> BETA_TAC \\
     POP_ASSUM K_TAC (* clean up *) \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS \\
     Q.EXISTS_TAC `\x. S k x - S (SUC n ** 2) x` \\
     CONJ_TAC >- art [] \\
     reverse CONJ_TAC >- rw [space_def] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
     qexistsl_tac [`S k`, `S (SUC n ** 2)`] \\
     fs [space_def, real_random_variable, p_space_def, events_def]) >> DISCH_TAC
 >> Know `!n. finite_second_moments p (W n)`
 >- (RW_TAC std_ss [finite_second_moments_literally, expectation_def] \\
     Q.UNABBREV_TAC `W` >> BETA_TAC \\
     Know `!x. D (SUC n) x / &(SUC n ** 2) = inv (&(SUC n ** 2)) * D (SUC n) x`
     >- (GEN_TAC \\
         MATCH_MP_TAC div_eq_mul_linv >> art [] \\
         RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq]) >> Rewr' \\
     Know `       integral p (\x. (inv (&(SUC n ** 2)) * D (SUC n) x) pow 2) =
           pos_fn_integral p (\x. (inv (&(SUC n ** 2)) * D (SUC n) x) pow 2)`
     >- (MATCH_MP_TAC integral_pos_fn \\
         FULL_SIMP_TAC std_ss [le_pow2, prob_space_def]) >> Rewr' \\
     REWRITE_TAC [pow_mul, extreal_of_num_def] \\
     Know `(inv (Normal &(SUC n ** 2))) pow 2 = Normal ((inv &(SUC n ** 2)) pow 2)`
     >- (`&(SUC n ** 2) <> (0 :real)` by RW_TAC real_ss [] \\
         ASM_SIMP_TAC std_ss [extreal_inv_eq, extreal_pow_def]) >> Rewr' \\
     Know `pos_fn_integral p
              (\x. Normal ((inv &(SUC n ** 2)) pow 2) * (\x. (D (SUC n) x) pow 2) x) =
           Normal ((inv &(SUC n ** 2)) pow 2) * pos_fn_integral p (\x. (D (SUC n) x) pow 2)`
     >- (MATCH_MP_TAC pos_fn_integral_cmul \\
         fs [prob_space_def, le_pow2]) >> BETA_TAC >> Rewr' \\
     Q.ABBREV_TAC `c = Normal ((inv &(SUC n ** 2)) pow 2)` \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC `c * (&(2 * SUC n + 1) pow 2) * M` \\
     reverse CONJ_TAC
     >- (Q.UNABBREV_TAC `c` \\
        `?r. M = Normal r` by METIS_TAC [extreal_cases] \\
         ASM_SIMP_TAC std_ss [extreal_pow_def, extreal_of_num_def,
                              lt_infty, extreal_mul_def]) \\
     ONCE_REWRITE_TAC [GSYM mul_assoc] \\
     MATCH_MP_TAC le_lmul_imp \\
     CONJ_TAC >- (Q.UNABBREV_TAC `c` \\
                  rw [extreal_of_num_def, extreal_le_eq, le_pow2]) \\
     Suff `pos_fn_integral p (\x. (D (SUC n) x) pow 2) =
               expectation p (\x. (D (SUC n) x) pow 2)`
     >- (Rewr' >> art []) \\
     REWRITE_TAC [expectation_def, Once EQ_SYM_EQ] \\
     MATCH_MP_TAC integral_pos_fn \\
     FULL_SIMP_TAC std_ss [prob_space_def, le_pow2]) >> DISCH_TAC
 >> Know `(W --> (\x. 0)) (almost_everywhere p)`
 >- (`real_random_variable (\x. 0) p` by METIS_TAC [real_random_variable_zero] \\
     RW_TAC std_ss [converge_AE_alt_limsup, sub_rzero] \\
     MATCH_MP_TAC Borel_Cantelli_Lemma1 >> BETA_TAC >> art [] \\
     STRONG_CONJ_TAC
     >- (GEN_TAC \\
        `{x | x IN p_space p /\ e < abs (W n x)} =
         {x | e < abs (W n x)} INTER p_space p` by SET_TAC [] >> POP_ORW \\
         REWRITE_TAC [lt_abs_bounds] \\
        `{x | W n x < -e \/ e < W n x} INTER p_space p =
         ({x | W n x < -e} INTER p_space p) UNION
         ({x | e < W n x} INTER p_space p)` by SET_TAC [] >> POP_ORW \\
         MATCH_MP_TAC EVENTS_UNION \\
         fs [events_def, p_space_def, real_random_variable_def,
             random_variable_def] \\
         METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC \\
     Know `!n. {x | x IN p_space p /\ e <= abs (W n x)} IN events p`
     >- (GEN_TAC \\
        `{x | x IN p_space p /\ e <= abs (W n x)} =
         {x | e <= abs (W n x)} INTER p_space p` by SET_TAC [] >> POP_ORW \\
         REWRITE_TAC [le_abs_bounds] \\
        `{x | W n x <= -e \/ e <= W n x} INTER p_space p =
         ({x | W n x <= -e} INTER p_space p) UNION
         ({x | e <= W n x} INTER p_space p)` by SET_TAC [] >> POP_ORW \\
         MATCH_MP_TAC EVENTS_UNION \\
         fs [events_def, p_space_def, real_random_variable_def,
             random_variable_def] \\
         METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC \\
     SIMP_TAC std_ss [o_DEF] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC `suminf (\n. prob p {x | x IN p_space p /\ e <= abs (W n x)})` \\
     CONJ_TAC >- (MATCH_MP_TAC ext_suminf_mono \\
                  CONJ_TAC >- METIS_TAC [PROB_POSITIVE] \\
                  RW_TAC std_ss [] \\
                  MATCH_MP_TAC PROB_INCREASING >> art [] \\
                  RW_TAC set_ss [SUBSET_DEF] \\
                  MATCH_MP_TAC lt_imp_le >> art []) \\
     Know `!n x. e <= abs (W n x) <=> e pow 2 <= abs ((\x. (W n x) pow 2) x)`
     >- (rpt GEN_TAC >> BETA_TAC \\
        `abs ((W n x) pow 2) = (abs (W n x)) pow 2`
            by METIS_TAC [abs_refl, le_pow2, abs_pow2] >> POP_ORW \\
         MATCH_MP_TAC pow_le_full >> rw [abs_pos] \\
         MATCH_MP_TAC lt_imp_le >> art []) >> DISCH_TAC \\
     (* applying prob_markov_ineq *)
    `!n. {x | x IN p_space p /\ e <= abs (W n x)} =
         {x | e <= abs (W n x)} INTER p_space p` by SET_TAC [] >> POP_ORW \\
     ASM_REWRITE_TAC [] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC `suminf (\n. inv (e pow 2) * expectation p (abs o (\x. (W n x) pow 2)))` \\
     CONJ_TAC
     >- (MATCH_MP_TAC ext_suminf_mono \\
         CONJ_TAC >- (GEN_TAC \\
                      POP_ASSUM (ONCE_REWRITE_TAC o wrap o GSYM) \\
                      BETA_TAC >> MATCH_MP_TAC PROB_POSITIVE \\
                      Suff `{x | e <= abs (W n x)} INTER p_space p =
                            {x | x IN p_space p /\ e <= abs (W n x)}` >- rw [] \\
                      SET_TAC []) \\
         GEN_TAC >> BETA_TAC \\
         HO_MATCH_MP_TAC prob_markov_ineq >> art [] \\
         reverse CONJ_TAC >- (MATCH_MP_TAC pow_pos_lt >> art []) \\
         METIS_TAC [finite_second_moments_eq_integrable_square]) \\
     SIMP_TAC std_ss [o_DEF] \\
    `!n x. abs ((W n x) pow 2) = (W n x) pow 2`
        by METIS_TAC [abs_refl, le_pow2] >> POP_ORW \\
     NTAC 3 (POP_ASSUM K_TAC) \\
     REWRITE_TAC [expectation_def] \\
     Know `!n.    integral p (\x. (W n x) pow 2) =
           pos_fn_integral p (\x. (W n x) pow 2)`
     >- (GEN_TAC >> MATCH_MP_TAC integral_pos_fn \\
         fs [prob_space_def, le_pow2]) >> Rewr' \\
     Q.UNABBREV_TAC `W` >> BETA_TAC \\
     Know `!n x. D (SUC n) x / &(SUC n ** 2) = inv (&(SUC n ** 2)) * D (SUC n) x`
     >- (rpt GEN_TAC \\
         MATCH_MP_TAC div_eq_mul_linv >> art [] \\
         RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq]) >> Rewr' \\
     REWRITE_TAC [pow_mul, extreal_of_num_def] \\
     Know `!n. (inv (Normal &(SUC n ** 2))) pow 2 = Normal ((inv &(SUC n ** 2)) pow 2)`
     >- (GEN_TAC >> `&(SUC n ** 2) <> (0 :real)` by RW_TAC real_ss [] \\
         ASM_SIMP_TAC std_ss [extreal_inv_eq, extreal_pow_def]) >> Rewr' \\
     Know `!n. pos_fn_integral p
                 (\x. Normal ((inv &(SUC n ** 2)) pow 2) * (\x. (D (SUC n) x) pow 2) x) =
               Normal ((inv &(SUC n ** 2)) pow 2) *
                 pos_fn_integral p (\x. (D (SUC n) x) pow 2)`
     >- (GEN_TAC >> MATCH_MP_TAC pos_fn_integral_cmul \\
         fs [prob_space_def, le_pow2]) >> BETA_TAC >> Rewr' \\
     ONCE_REWRITE_TAC [mul_assoc] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC `suminf (\n. inv (e pow 2) * Normal ((inv &(SUC n ** 2)) pow 2) *
                               (&(2 * SUC n + 1)) pow 2 * M)` \\
     CONJ_TAC
     >- (MATCH_MP_TAC ext_suminf_mono >> BETA_TAC \\
         Know `!n. 0 <= inv (e pow 2) * Normal ((inv &(SUC n ** 2)) pow 2)`
         >- (GEN_TAC >> MATCH_MP_TAC le_mul \\
             CONJ_TAC >- (MATCH_MP_TAC lt_imp_le \\
                          MATCH_MP_TAC inv_pos' \\
                          CONJ_TAC >- (MATCH_MP_TAC pow_pos_lt >> art []) \\
                         `e <> NegInf` by METIS_TAC [pos_not_neginf, lt_imp_le] \\
                          METIS_TAC [pow_not_infty]) \\
             RW_TAC real_ss [extreal_of_num_def, extreal_le_eq, REAL_LE_POW2]) \\
         DISCH_TAC \\
         CONJ_TAC >- (GEN_TAC >> MATCH_MP_TAC le_mul >> art [] \\
                      MATCH_MP_TAC pos_fn_integral_pos \\
                      fs [prob_space_def, le_pow2]) \\
         GEN_TAC \\
         Q.ABBREV_TAC `z = inv (e pow 2) * Normal ((inv &(SUC n ** 2)) pow 2)` \\
         ONCE_REWRITE_TAC [GSYM mul_assoc] \\
         MATCH_MP_TAC le_lmul_imp \\
         Q.UNABBREV_TAC `z` >> CONJ_TAC >- art [] \\
         Suff `pos_fn_integral p (\x. (D (SUC n) x) pow 2) =
                   expectation p (\x. (D (SUC n) x) pow 2)` >- (Rewr' >> art []) \\
         REWRITE_TAC [expectation_def, Once EQ_SYM_EQ] \\
         MATCH_MP_TAC integral_pos_fn >> fs [prob_space_def, le_pow2]) \\
  (* now the dirty (ext)real arithmetics *)
     Know `!n. Normal ((inv &(SUC n ** 2)) pow 2) = inv ((&SUC n) pow 4)`
     >- (RW_TAC std_ss [extreal_of_num_def] \\
        `&SUC n <> (0 :real)` by RW_TAC real_ss [] \\
         ASM_SIMP_TAC std_ss [extreal_inv_eq, extreal_pow_def] \\
         Know `(&SUC n) pow 4 <> (0 :real)`
         >- (Suff `(0 :real) < (&SUC n) pow 4` >- rw [] \\
             MATCH_MP_TAC REAL_POW_LT >> rw []) >> DISCH_TAC \\
         ASM_SIMP_TAC std_ss [extreal_inv_eq, extreal_11] \\
        `&(SUC n ** 2) :real = (&SUC n) pow 2` by METIS_TAC [REAL_OF_NUM_POW] >> POP_ORW \\
         ASM_SIMP_TAC real_ss [POW_INV, REAL_POW_POW]) >> Rewr' \\
     Q.ABBREV_TAC `z = \n. inv (e pow 2) * inv ((&n) pow 4)` \\
    `!n. inv (e pow 2) * inv ((&SUC n) pow 4) = z (SUC n)` by METIS_TAC [] >> POP_ORW \\
     Know `!n. 0 <= z (SUC n)`
     >- (RW_TAC std_ss [Abbr `z`] \\
         MATCH_MP_TAC le_mul \\
         CONJ_TAC >- (MATCH_MP_TAC lt_imp_le >> MATCH_MP_TAC inv_pos' \\
                      CONJ_TAC >- (MATCH_MP_TAC pow_pos_lt >> art []) \\
                     `e <> NegInf` by METIS_TAC [pos_not_neginf, lt_imp_le] \\
                      METIS_TAC [pow_not_infty]) \\
         MATCH_MP_TAC lt_imp_le >> MATCH_MP_TAC inv_pos' \\
         CONJ_TAC >- (MATCH_MP_TAC pow_pos_lt \\
                      rw [extreal_of_num_def, extreal_lt_eq]) \\
         SIMP_TAC std_ss [extreal_of_num_def, extreal_pow_def, extreal_not_infty]) \\
     DISCH_TAC \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC `suminf (\n. z (SUC n) * ((3 * &SUC n) pow 2) * M)` \\
     CONJ_TAC
     >- (MATCH_MP_TAC ext_suminf_mono >> BETA_TAC \\
         CONJ_TAC >- (GEN_TAC >> MATCH_MP_TAC le_mul >> art [] \\
                      MATCH_MP_TAC le_mul >> art [le_pow2]) \\
         GEN_TAC \\
         MATCH_MP_TAC le_rmul_imp >> art [] \\
         MATCH_MP_TAC le_lmul_imp >> art [] \\
         MATCH_MP_TAC pow_le \\
         rw [extreal_of_num_def, extreal_le_eq, extreal_mul_def]) \\
     POP_ASSUM K_TAC \\
     Q.UNABBREV_TAC `z` >> BETA_TAC \\
  (* applying harmonic_series_pow_2 *)
     Suff `!n. inv (e pow 2) * inv ((&SUC n) pow 4) * (3 * &SUC n) pow 2 * M =
               inv (e pow 2) * M * 3 pow 2 * (\n. inv ((&SUC n) pow 2)) n`
     >- (Rewr' \\
         Know `suminf (\n. inv (e pow 2) * M * 3 pow 2 * (\n. inv ((&SUC n) pow 2)) n) =
               inv (e pow 2) * M * 3 pow 2 * suminf (\n. inv ((&SUC n) pow 2))`
         >- (MATCH_MP_TAC ext_suminf_cmul >> BETA_TAC \\
             CONJ_TAC >- (MATCH_MP_TAC le_mul \\
                          reverse CONJ_TAC >- (MATCH_MP_TAC pow_pos_le \\
                                               rw [extreal_of_num_def,  extreal_le_eq]) \\
                          MATCH_MP_TAC le_mul >> art [] \\
                          MATCH_MP_TAC lt_imp_le >> MATCH_MP_TAC inv_pos' \\
                          CONJ_TAC >- (MATCH_MP_TAC pow_pos_lt >> art []) \\
                         `e <> NegInf` by METIS_TAC [pos_not_neginf, lt_imp_le] \\
                          METIS_TAC [pow_not_infty]) \\
             GEN_TAC >> MATCH_MP_TAC lt_imp_le >> MATCH_MP_TAC inv_pos' \\
             CONJ_TAC >- (MATCH_MP_TAC pow_pos_lt \\
                          rw [extreal_of_num_def, extreal_lt_eq]) \\
             METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty]) \\
         Rewr' \\
         Know `0 <= suminf (\n. inv ((&SUC n) pow 2))`
         >- (MATCH_MP_TAC ext_suminf_pos >> RW_TAC std_ss [] \\
             MATCH_MP_TAC lt_imp_le >> MATCH_MP_TAC inv_pos' \\
             CONJ_TAC >- (MATCH_MP_TAC pow_pos_lt \\
                          rw [extreal_of_num_def, extreal_lt_eq]) \\
             METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty]) \\
         DISCH_TAC \\
        `suminf (\n. inv ((&SUC n) pow 2)) <> NegInf` by METIS_TAC [pos_not_neginf] \\
        `suminf (\n. inv ((&SUC n) pow 2)) <> PosInf`
            by METIS_TAC [harmonic_series_pow_2, lt_infty] \\
        `?r. suminf (\n. inv ((&SUC n) pow 2)) = Normal r`
            by METIS_TAC [extreal_cases] >> POP_ORW \\
        `?b. M = Normal b` by METIS_TAC [extreal_cases] >> POP_ORW \\
        `e <> NegInf` by METIS_TAC [pos_not_neginf, lt_imp_le] \\
        `?a. e = Normal a` by METIS_TAC [extreal_cases] \\
         ASM_SIMP_TAC std_ss [GSYM lt_infty, extreal_of_num_def, extreal_pow_def] \\
        `0 < a` by METIS_TAC [extreal_of_num_def, extreal_lt_eq] \\
        `a pow 2 <> 0` by METIS_TAC [REAL_POW_LT, REAL_LT_IMP_NE] \\
         ASM_SIMP_TAC std_ss [extreal_inv_eq, extreal_mul_def, extreal_not_infty]) \\
     GEN_TAC >> BETA_TAC \\
     REWRITE_TAC [GSYM mul_assoc] \\
     Suff `inv ((&SUC n) pow 4) * ((3 * &SUC n) pow 2 * M) =
           M * (3 pow 2 * inv ((&SUC n) pow 2))` >- RW_TAC std_ss [] \\
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [mul_comm] \\
     REWRITE_TAC [mul_assoc] \\
     Suff `inv ((&SUC n) pow 4) * (3 * &SUC n) pow 2 =
           3 pow 2 * inv ((&SUC n) pow 2)` >- RW_TAC std_ss [] \\
     REWRITE_TAC [pow_mul] \\
     GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [mul_comm] \\
     REWRITE_TAC [GSYM mul_assoc] \\
     Suff `(&SUC n) pow 2 * inv ((&SUC n) pow 4) = inv ((&SUC n) pow 2)` >- rw [] \\
    `4 = 2 + (2 :num)` by RW_TAC arith_ss [] >> POP_ORW \\
     REWRITE_TAC [pow_add] \\
     Know `inv (&SUC n pow 2 * &SUC n pow 2) =
           inv (&SUC n pow 2) * inv (&SUC n pow 2)`
     >- (MATCH_MP_TAC inv_mul >> REWRITE_TAC [] \\
         Suff `0 < (&SUC n) pow 2` >- METIS_TAC [lt_imp_ne] \\
         MATCH_MP_TAC pow_pos_lt \\
         RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq]) >> Rewr' \\
     REWRITE_TAC [mul_assoc] \\
     Suff `(&SUC n) pow 2 * inv (&SUC n pow 2) = 1`
     >- (Rewr' >> REWRITE_TAC [mul_lone]) \\
     ONCE_REWRITE_TAC [mul_comm] \\
     MATCH_MP_TAC mul_linv_pos \\
     CONJ_TAC >- (MATCH_MP_TAC pow_pos_lt \\
                  RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq]) \\
     REWRITE_TAC [extreal_of_num_def, extreal_pow_def, extreal_not_infty])
 >> DISCH_TAC
 (* pre-final stage *)
 >> Know `!k x. abs (S (SUC k) x) / &SUC k <=
               (abs (S (&(ROOT 2 (SUC k) ** 2)) x) + abs (D (&(ROOT 2 (SUC k))) x))
                / &(ROOT 2 (SUC k) ** 2)`
 >- (rpt GEN_TAC \\
     Q.ABBREV_TAC `n = ROOT 2 (SUC k)` \\
     Know `0 < n`
     >- (Q.UNABBREV_TAC `n` \\
         MATCH_MP_TAC LESS_LESS_EQ_TRANS \\
         Q.EXISTS_TAC `1` >> RW_TAC arith_ss [] \\
        `ROOT 2 1 = 1` by EVAL_TAC \\
         POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) \\
         irule ROOT_LE_MONO >> RW_TAC arith_ss []) >> DISCH_TAC \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `abs (S (SUC k) x) / &(n ** 2)` \\
     CONJ_TAC
     >- (Know `abs (S (SUC k) x) / &SUC k = inv (&SUC k) * abs (S (SUC k) x)`
         >- (MATCH_MP_TAC div_eq_mul_linv \\
             SIMP_TAC real_ss [extreal_of_num_def, extreal_lt_eq] \\
             MATCH_MP_TAC abs_not_infty >> art []) >> Rewr' \\
         Know `abs (S (SUC k) x) / &(n ** 2) = inv (&(n ** 2)) * abs (S (SUC k) x)`
         >- (MATCH_MP_TAC div_eq_mul_linv \\
             ONCE_REWRITE_TAC [CONJ_ASSOC] \\
             CONJ_TAC >- (MATCH_MP_TAC abs_not_infty >> art []) \\
             ASM_SIMP_TAC real_ss [extreal_of_num_def, extreal_lt_eq]) >> Rewr' \\
         MATCH_MP_TAC le_rmul_imp >> REWRITE_TAC [abs_pos] \\
         Know `inv (&SUC k) <= inv (&(n ** 2)) <=> &(n ** 2) <= &SUC k`
         >- (MATCH_MP_TAC inv_le_antimono \\
             RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq]) >> Rewr' \\
         SIMP_TAC real_ss [Abbr `n`, extreal_of_num_def, extreal_le_eq] \\
         PROVE_TAC [SIMP_RULE arith_ss [] (Q.SPEC `2` ROOT)]) \\
     Know `abs (S (SUC k) x) / &(n ** 2) = inv (&(n ** 2)) * abs (S (SUC k) x)`
     >- (MATCH_MP_TAC div_eq_mul_linv \\
         SIMP_TAC real_ss [extreal_of_num_def, extreal_lt_eq] \\
         ONCE_REWRITE_TAC [CONJ_ASSOC] \\
         reverse CONJ_TAC >- art [] \\
         MATCH_MP_TAC abs_not_infty >> art []) >> Rewr' \\
     Know `(abs (S (n ** 2) x) + abs (D n x)) / &(n ** 2) =
           inv (&(n ** 2)) * (abs (S (n ** 2) x) + abs (D n x))`
     >- (MATCH_MP_TAC div_eq_mul_linv \\
         ONCE_REWRITE_TAC [CONJ_ASSOC] \\
         reverse CONJ_TAC
         >- (ASM_SIMP_TAC real_ss [extreal_of_num_def, extreal_lt_eq]) \\
        `?r. S (n ** 2) x = Normal r` by METIS_TAC [extreal_cases] \\
        `?a. D n x = Normal a` by METIS_TAC [extreal_cases] \\
         ASM_SIMP_TAC std_ss [extreal_abs_def, extreal_add_def,
                              extreal_not_infty]) >> Rewr' \\
     MATCH_MP_TAC le_lmul_imp \\
     CONJ_TAC >- (MATCH_MP_TAC lt_imp_le >> MATCH_MP_TAC inv_pos' \\
                  rw [extreal_of_num_def, extreal_lt_eq, extreal_not_infty]) \\
    `D n x = d n (f n x) x` by PROVE_TAC [] >> POP_ORW \\
    `d n (f n x) x = abs (S (f n x) x - S (n ** 2) x)` by PROVE_TAC [] >> POP_ORW \\
     REWRITE_TAC [abs_abs] \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `abs (S (n ** 2) x) + abs (S (SUC k) x - S (n ** 2) x)` \\
     CONJ_TAC
     >- (MATCH_MP_TAC abs_triangle_sub >> art []) \\
     Know `abs (S (n ** 2) x) + abs (S (SUC k) x - S (n ** 2) x) <=
           abs (S (n ** 2) x) + abs (S (f n x) x - S (n ** 2) x) <=>
           abs (S (SUC k) x - S (n ** 2) x) <= abs (S (f n x) x - S (n ** 2) x)`
     >- (MATCH_MP_TAC le_ladd \\
         ONCE_REWRITE_TAC [CONJ_SYM] \\
         MATCH_MP_TAC abs_not_infty >> art []) >> Rewr' \\
    `abs (S (SUC k) x - S (n ** 2) x) = d n (SUC k) x` by PROVE_TAC [] >> POP_ORW \\
    `abs (S (f n x) x - S (n ** 2) x) = d n (f n x) x` by PROVE_TAC [] >> POP_ORW \\
    `d n (f n x) x = sup (IMAGE (\k. d n k x) (N n))` by METIS_TAC [] >> POP_ORW \\
     MATCH_MP_TAC le_sup_imp' \\
     RW_TAC set_ss [Abbr `N`, IN_IMAGE] \\
     Q.EXISTS_TAC `SUC k` >> art [] \\
     Q.UNABBREV_TAC `n` \\
     MATCH_MP_TAC logrootTheory.ROOT (* amazing *) \\
     RW_TAC arith_ss []) >> DISCH_TAC
 (* final stage *)
 >> Q.PAT_X_ASSUM `(Z --> (\x. 0)) (almost_everywhere p)`
      (MP_TAC o (SIMP_RULE std_ss [converge_AE_def, AE_THM, almost_everywhere_def,
                                   GSYM IN_NULL_SET, LIM_SEQUENTIALLY, dist]))
 >> DISCH_THEN (Q.X_CHOOSE_THEN `N1` STRIP_ASSUME_TAC)
 >> Q.PAT_X_ASSUM `(W --> (\x. 0)) (almost_everywhere p)`
      (MP_TAC o (SIMP_RULE std_ss [converge_AE_def, AE_THM, almost_everywhere_def,
                                   GSYM IN_NULL_SET, LIM_SEQUENTIALLY, dist]))
 >> DISCH_THEN (Q.X_CHOOSE_THEN `N2` STRIP_ASSUME_TAC)
 >> SIMP_TAC std_ss [converge_AE_def, AE_THM, almost_everywhere_def,
                     GSYM IN_NULL_SET, LIM_SEQUENTIALLY, dist]
 >> Q.EXISTS_TAC `N1 UNION N2`
 >> STRONG_CONJ_TAC
 >- (MATCH_MP_TAC NULL_SET_UNION \\
     FULL_SIMP_TAC bool_ss [prob_space_def]) >> DISCH_TAC
 >> rpt STRIP_TAC
 >> `(m_space p DIFF (N1 UNION N2)) SUBSET (m_space p DIFF N1)` by SET_TAC []
 >> `(m_space p DIFF (N1 UNION N2)) SUBSET (m_space p DIFF N2)` by SET_TAC []
 (* clean up disturbing assumptions *)
 >> Q.PAT_X_ASSUM `!n x. S n x = SIGMA (\i. X i x) (count n)` K_TAC
 >> Q.PAT_X_ASSUM `!n. expectation p (X n) = 0`               K_TAC
 >> Q.PAT_X_ASSUM `!n. real_random_variable (X n) p`          K_TAC
 >> Q.PAT_X_ASSUM `!n. finite_second_moments p (X n)`         K_TAC
 >> Q.PAT_X_ASSUM `!n. variance p (X n) <= M`                 K_TAC
 >> Q.PAT_X_ASSUM `!n. integrable p (X n)`                    K_TAC
 >> Q.PAT_X_ASSUM `!i j. i <> j ==> orthogonal p (X i) (X j)` K_TAC
 (* simplify assumptions *)
 >> Q.PAT_X_ASSUM `!x. x IN m_space p DIFF N1 ==> P` (MP_TAC o Q.SPEC `x`)
 >> Know `x IN m_space p DIFF N1` >- ASM_SET_TAC []
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM `!x. x IN m_space p DIFF N2 ==> P` (MP_TAC o Q.SPEC `x`)
 >> Know `x IN m_space p DIFF N2` >- ASM_SET_TAC []
 >> RW_TAC std_ss []
 >> `real 0 = 0` by METIS_TAC [extreal_of_num_def, real_normal]
 >> POP_ASSUM (fn th => FULL_SIMP_TAC bool_ss [REAL_SUB_RZERO, th])
 >> NTAC 3 (Q.PAT_X_ASSUM `_ IN null_set p`           K_TAC)
 >> NTAC 2 (Q.PAT_X_ASSUM `_ SUBSET m_space p DIFF _` K_TAC)
 >> NTAC 3 (Q.PAT_X_ASSUM `x IN m_space p DIFF _`     K_TAC)
 >> Q.PAT_X_ASSUM `M <> PosInf` K_TAC
 >> Q.PAT_X_ASSUM `M <> NegInf` K_TAC
 >> Q.PAT_X_ASSUM `0 <= M`      K_TAC
 (* clean up Z and W *)
 >> Q.PAT_X_ASSUM `!n. real_random_variable (Z n) p`  K_TAC
 >> Q.PAT_X_ASSUM `!n. real_random_variable (W n) p`  K_TAC
 >> Q.PAT_X_ASSUM `!n. finite_second_moments p (W n)` K_TAC
 >> qunabbrevl_tac [`Z`, `W`]
 >> FULL_SIMP_TAC std_ss []
 (* translate real inequations to extreal ineq. *)
 >> Know `!n. abs (real (S (SUC n) x / &SUC n)) < e <=>
              abs (S (SUC n) x) / &SUC n < Normal e`
 >- (GEN_TAC \\
    `?r. S (SUC n) x = Normal r` by METIS_TAC [extreal_cases] >> POP_ORW \\
    `&SUC n <> (0: real)` by RW_TAC real_ss [] \\
     ASM_SIMP_TAC real_ss [extreal_of_num_def, extreal_abs_def, real_normal,
                           extreal_div_eq, extreal_lt_eq, ABS_DIV, ABS_N])
 >> Rewr'
 >> Know `!n e. abs (real (S (SUC n ** 2) x / &(SUC n ** 2))) < e <=>
                abs (S (SUC n ** 2) x) / &(SUC n ** 2) < Normal e`
 >- (rpt GEN_TAC \\
    `?r. S (SUC n ** 2) x = Normal r` by METIS_TAC [extreal_cases] >> POP_ORW \\
    `&(SUC n ** 2) <> (0: real)` by RW_TAC real_ss [] \\
     ASM_SIMP_TAC real_ss [extreal_of_num_def, extreal_abs_def, real_normal,
                           extreal_div_eq, extreal_lt_eq, ABS_DIV, ABS_N])
 >> DISCH_THEN ((FULL_SIMP_TAC bool_ss) o wrap)
 >> Know `!n e. abs (real (D (SUC n) x / &(SUC n ** 2))) < e <=>
                abs (D (SUC n) x) / &(SUC n ** 2) < Normal e`
 >- (rpt GEN_TAC \\
    `?r. D (SUC n) x = Normal r` by METIS_TAC [extreal_cases] >> POP_ORW \\
    `&(SUC n ** 2) <> (0: real)` by RW_TAC real_ss [] \\
     ASM_SIMP_TAC real_ss [extreal_of_num_def, extreal_abs_def, real_normal,
                           extreal_div_eq, extreal_lt_eq, ABS_DIV, ABS_N])
 >> DISCH_THEN ((FULL_SIMP_TAC bool_ss) o wrap)
 (* continue estimating N *)
 >> NTAC 2 (Q.PAT_X_ASSUM `!e. 0 < e ==> P` (MP_TAC o (Q.SPEC `e / 2`)))
 >> Know `0 < e / 2`
 >- (MATCH_MP_TAC REAL_LT_DIV >> RW_TAC real_ss [])
 >> `!n x. D n x <> PosInf /\ D n x <> NegInf` by METIS_TAC []
 >> Q.PAT_X_ASSUM (* to prevent `D n x` from being rewritten *)
      `!n x. n ** 2 <= f n x /\ f n x < SUC n ** 2 /\ D n x = d n (f n x) x` K_TAC
 >> RW_TAC std_ss []
 >> rename1 `!n. m1 <= n ==> abs (S (SUC n ** 2) x) / &(SUC n ** 2) < Normal (e / 2)`
 >> rename1 `!n. m2 <= n ==> abs (D (SUC n) x) / &(SUC n ** 2) < Normal (e / 2)`
 (* final-final *)
 >> Q.EXISTS_TAC `(m1 + m2 + 1) ** 2 - 1`
 >> RW_TAC std_ss []
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC `(abs (S (ROOT 2 (SUC n) ** 2) x) + abs (D (ROOT 2 (SUC n)) x)) /
                  &(ROOT 2 (SUC n) ** 2)`
 >> CONJ_TAC >- art []
 >> Q.PAT_X_ASSUM `!k x. abs (S (SUC k) x) / &SUC k <= _` K_TAC
 >> Q.ABBREV_TAC `k = ROOT 2 (SUC n)`
 >> Know `0 < k`
 >- (Q.UNABBREV_TAC `k` >> MATCH_MP_TAC LESS_LESS_EQ_TRANS \\
     Q.EXISTS_TAC `1` >> RW_TAC arith_ss [] \\
    `ROOT 2 1 = 1` by EVAL_TAC \\
     POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) \\
     irule ROOT_LE_MONO >> RW_TAC arith_ss []) >> DISCH_TAC
 >> `?m. m = k - 1` by RW_TAC arith_ss []
 >> `k = SUC m` by RW_TAC arith_ss [] >> POP_ORW
 >> Know `(abs (S (SUC m ** 2) x) + abs (D (SUC m) x)) / &(SUC m ** 2) =
           abs (S (SUC m ** 2) x) / &(SUC m ** 2) + abs (D (SUC m) x) / &(SUC m ** 2)`
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC div_add \\
     ONCE_REWRITE_TAC [CONJ_ASSOC] \\
     CONJ_TAC >- (MATCH_MP_TAC abs_not_infty >> art []) \\
     ONCE_REWRITE_TAC [CONJ_ASSOC] \\
     CONJ_TAC >- (MATCH_MP_TAC abs_not_infty >> art []) \\
     RW_TAC real_ss [extreal_of_num_def, extreal_11]) >> Rewr'
 >> `Normal e = Normal (e / 2) + Normal (e / 2)`
       by METIS_TAC [extreal_add_def, REAL_HALF_DOUBLE] >> POP_ORW
 >> MATCH_MP_TAC lt_add2
 >> CONJ_TAC (* 2 subgoals, similar tactics *)
 >| [ (* goal 1 (of 2) *)
      FIRST_X_ASSUM MATCH_MP_TAC \\
     `m1 <= m <=> m1 + 1 <= k` by RW_TAC arith_ss [] >> POP_ORW \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      Q.UNABBREV_TAC `k` \\
      Know `(m1 + 1) ** 2 <= SUC n`
      >- (MATCH_MP_TAC LESS_EQ_TRANS \\
          Q.EXISTS_TAC `(m1 + m2 + 1) ** 2` \\
          CONJ_TAC >- RW_TAC arith_ss [] \\
          PROVE_TAC [ADD_COMM, ADD1]) \\
      POP_ASSUM K_TAC >> DISCH_TAC \\
      Know `ROOT 2 ((m1 + 1) ** 2) = m1 + 1`
      >- (MATCH_MP_TAC ROOT_EXP >> RW_TAC arith_ss []) \\
      DISCH_THEN (ONCE_REWRITE_TAC o wrap o SYM) \\
      irule ROOT_LE_MONO >> RW_TAC arith_ss [],
      (* goal 2 (of 2) *)
      FIRST_X_ASSUM MATCH_MP_TAC \\
     `m2 <= m <=> m2 + 1 <= k` by RW_TAC arith_ss [] >> POP_ORW \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      Q.UNABBREV_TAC `k` \\
      Know `(m2 + 1) ** 2 <= SUC n`
      >- (MATCH_MP_TAC LESS_EQ_TRANS \\
          Q.EXISTS_TAC `(m1 + m2 + 1) ** 2` \\
          CONJ_TAC >- RW_TAC arith_ss [] \\
          PROVE_TAC [ADD_COMM, ADD1]) \\
      POP_ASSUM K_TAC >> DISCH_TAC \\
      Know `ROOT 2 ((m2 + 1) ** 2) = m2 + 1`
      >- (MATCH_MP_TAC ROOT_EXP >> RW_TAC arith_ss []) \\
      DISCH_THEN (ONCE_REWRITE_TAC o wrap o SYM) \\
      irule ROOT_LE_MONO >> RW_TAC arith_ss [] ]
QED

Theorem converge_AE_shift :
    !p X Y. ((\n. X (SUC n)) --> Y) (almost_everywhere p) ==>
            ((\n. X n)       --> Y) (almost_everywhere p)
Proof
    RW_TAC std_ss [converge_AE_def, AE_THM, almost_everywhere_def,
                   GSYM IN_NULL_SET, LIM_SEQUENTIALLY, dist]
 >> Q.EXISTS_TAC `N` >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM `!x. x IN m_space p DIFF N ==> P` (MP_TAC o (Q.SPEC `x`))
 >> RW_TAC std_ss []
 >> rename1 `zero IN null_set p`
 >> Q.PAT_X_ASSUM `!e. 0 < e ==> P` (MP_TAC o (Q.SPEC `e`))
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC `SUC N`
 >> RW_TAC std_ss []
 >> `n <> 0` by RW_TAC arith_ss []
 >> Cases_on `n` >- fs []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> rw []
QED

Theorem converge_PR_shift :
    !p X Y. ((\n. X (SUC n)) --> Y) (in_probability p) ==>
            ((\n. X n)       --> Y) (in_probability p)
Proof
    RW_TAC std_ss [converge_PR_def, LIM_SEQUENTIALLY, dist]
 >> rename1 `E <> PosInf`
 >> Q.PAT_X_ASSUM `!e. 0 < e /\ e <> PosInf ==> P` (MP_TAC o (Q.SPEC `E`))
 >> RW_TAC std_ss []
 >> rename1 `0 < e` (* this changes the last matching assumption *)
 >> Q.PAT_X_ASSUM `!e. 0 < e ==> P` (MP_TAC o (Q.SPEC `e`))
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC `SUC N`
 >> RW_TAC std_ss []
 >> `n <> 0` by RW_TAC arith_ss []
 >> Cases_on `n` >- fs []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> rw []
QED

(* more compact statements without SUC but use with cautions *)
Theorem WLLN_uncorrelated' :
    !p X S. prob_space p /\ (!n. real_random_variable (X n) p) /\
            (!i j. i <> j ==> uncorrelated p (X i) (X j)) /\
            (?c. c <> PosInf /\ !n. variance p (X n) <= c) /\
            (!n x. S n x = SIGMA (\i. X i x) (count n)) ==>
       ((\n x. (S n x - expectation p (S n)) / &n) --> (\x. 0)) (in_probability p)
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC `M = \n. expectation p (S n)`
 >> `!n. expectation p (S n) = M n` by METIS_TAC [] >> POP_ORW
 >> HO_MATCH_MP_TAC converge_PR_shift
 >> MATCH_MP_TAC WLLN_uncorrelated
 >> Q.EXISTS_TAC `X` >> art []
 >> CONJ_TAC >- (Q.EXISTS_TAC `c` >> art [])
 >> RW_TAC std_ss [Abbr `M`]
QED

(* more compact statements without SUC but use with cautions *)
Theorem SLLN_uncorrelated' :
    !p X S. prob_space p /\ (!n. real_random_variable (X n) p) /\
            (!i j. i <> j ==> uncorrelated p (X i) (X j)) /\
            (?c. c <> PosInf /\ !n. variance p (X n) <= c) /\
            (!n x. S n x = SIGMA (\i. X i x) (count n)) ==>
       ((\n x. (S n x - expectation p (S n)) / &n) --> (\x. 0)) (almost_everywhere p)
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC `M = \n. expectation p (S n)`
 >> `!n. expectation p (S n) = M n` by METIS_TAC [] >> POP_ORW
 >> HO_MATCH_MP_TAC converge_AE_shift
 >> MATCH_MP_TAC SLLN_uncorrelated
 >> Q.EXISTS_TAC `X` >> art []
 >> CONJ_TAC >- (Q.EXISTS_TAC `c` >> art [])
 >> RW_TAC std_ss [Abbr `M`]
QED

(* ------------------------------------------------------------------------- *)
(*  The Weak Law of Large Numbers for I.I.D. random sequences                *)
(* ------------------------------------------------------------------------- *)

Theorem PROB_ZERO_AE :
    !p E. prob_space p /\ E IN events p /\ (prob p E = 0) ==> AE x::p. x NOTIN E
Proof
    RW_TAC std_ss [AE_THM, almost_everywhere_def, null_set_def]
 >> Q.EXISTS_TAC `E`
 >> fs [prob_space_def, events_def, prob_def]
QED

Theorem PROB_ONE_AE :
    !p E. prob_space p /\ E IN events p /\ (prob p E = 1) ==> AE x::p. x IN E
Proof
    RW_TAC std_ss [AE_THM, almost_everywhere_def, null_set_def]
 >> Q.EXISTS_TAC `m_space p DIFF E`
 >> `E SUBSET p_space p` by PROVE_TAC [PROB_SPACE_SUBSET_PSPACE]
 >> `p_space p DIFF (p_space p DIFF E) = E` by ASM_SET_TAC []
 >> Know `prob p (p_space p DIFF E) = 1 - prob p E`
 >- (MATCH_MP_TAC PROB_COMPL >> art [])
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss [prob_space_def, events_def, prob_def, p_space_def,
                          sub_refl, extreal_not_infty, extreal_of_num_def]
 >> MATCH_MP_TAC MEASURE_SPACE_COMPL >> art []
QED

(* actually, whenever you use "fs [EXT_SKOLEM_THM]" you can also use
   "fs [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]".
 *)
Theorem EXT_SKOLEM_THM[local] :
    !P Q. (!x. x IN P ==> ?y. Q x y) <=> ?f. !x. x IN P ==> Q x (f x)
Proof
    rpt STRIP_TAC
 >> reverse EQ_TAC >> rpt STRIP_TAC
 >- (Q.EXISTS_TAC `f x` \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> fs [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
 >> Q.EXISTS_TAC `f` >> art []
QED

(* "The law of large numbers in the general case involves only the first
    moment (finite expectation), but so far we have operated with the second.
    In order to drop any assumption on the second moment, we need a new device,
    that of 'equivalent sequences', due to Khintchine (1894-1959)." [2, p.113]
 *)
val equivalent_def = Define
   `equivalent p (X :num->'a->extreal) Y =
      (suminf (\n. prob p {x | x IN p_space p /\ X n x <> Y n x}) < PosInf)`;

Theorem equivalent_lemma :
    !p X Y. prob_space p /\ equivalent p X Y /\
            (!n. real_random_variable (X n) p) /\
            (!n. real_random_variable (Y n) p) ==>
       ?N f. N IN null_set p /\
             !x. x IN p_space p DIFF N ==> !n. f x <= n ==> (X n x - Y n x = 0)
Proof
    RW_TAC std_ss [equivalent_def]
 >> Q.ABBREV_TAC `E = \n. {x | x IN p_space p /\ X n x <> Y n x}`
 >> Know `!n. (E n) IN events p`
 >- (RW_TAC std_ss [Abbr `E`, events_def, p_space_def] \\
    `{x | x IN m_space p /\ X n x <> Y n x} =
     {x | X n x <> Y n x} INTER m_space p` by SET_TAC [] >> POP_ORW \\
     Know `!n x. X n x <> Y n x <=> (\x. X n x - Y n x) x <> 0`
     >- (RW_TAC std_ss [] \\
         reverse EQ_TAC >- (DISCH_TAC >> MATCH_MP_TAC sub_0 >> art []) \\
         fs [real_random_variable_def] \\
         DISCH_TAC >> MATCH_MP_TAC sub_eq_0 >> art []) >> Rewr' \\
     Suff `(\x. X n x - Y n x) IN measurable (m_space p,measurable_sets p) Borel`
     >- (METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
     qexistsl_tac [`X n`, `Y n`] \\
     fs [prob_space_def, measure_space_def, space_def, real_random_variable_def,
         random_variable_def, p_space_def, events_def]) >> DISCH_TAC
 (* applying Borel_Cantelli_Lemma1 *)
 >> Know `(\n. prob p {x | x IN p_space p /\ X n x <> Y n x}) = prob p o E`
 >- (RW_TAC std_ss [FUN_EQ_THM, o_DEF, Abbr `E`])
 >> DISCH_THEN (fs o wrap)
 >> Know `prob p (limsup E) = 0`
 >- (MATCH_MP_TAC Borel_Cantelli_Lemma1 >> art []) >> DISCH_TAC
 >> Know `AE x::p. x NOTIN (limsup E)`
 >- (MATCH_MP_TAC PROB_ZERO_AE >> art [] \\
     MATCH_MP_TAC EVENTS_LIMSUP >> art [])
 >> RW_TAC std_ss [AE_THM, GSYM IN_NULL_SET, almost_everywhere_def,
                   IN_LIMSUP, infinitely_often_lemma]
 >> FULL_SIMP_TAC std_ss [EXT_SKOLEM_THM]
 >> qexistsl_tac [`N`, `f`]
 >> RW_TAC std_ss []
 >> Q.UNABBREV_TAC `E`
 >> fs [real_random_variable_def, p_space_def]
 >> MATCH_MP_TAC sub_eq_0 >> art []
QED

(* Theorem 5.2.1 (1) [2, p.113] *)
Theorem equivalent_thm1 :
    !p X Y Z. prob_space p /\ equivalent p X Y /\
              (!n. real_random_variable (X n) p) /\
              (!n. real_random_variable (Y n) p) /\
              (!n x. Z n x = SIGMA (\n. X n x - Y n x) (count n)) ==>
          ?W. real_random_variable W p /\ (Z --> W) (almost_everywhere p)
Proof
    rpt STRIP_TAC
 >> Know `?N f. N IN null_set p /\
               !x. x IN p_space p DIFF N ==> !n. f x <= n ==> (X n x - Y n x = 0)`
 >- (MATCH_MP_TAC equivalent_lemma >> art [])
 >> STRIP_TAC
 >> Q.EXISTS_TAC `\x. SIGMA (\n. X n x - Y n x) (count (f x)) *
                      indicator_fn (p_space p DIFF N) x`
 >> CONJ_TAC
 >- (REWRITE_TAC [real_random_variable_def] \\
     reverse CONJ_TAC
     >- (GEN_TAC >> BETA_TAC \\
         reverse (Cases_on `x IN p_space p DIFF N`)
         >- (ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rzero] \\
             REWRITE_TAC [extreal_of_num_def, extreal_not_infty]) \\
         ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rone] \\
         FULL_SIMP_TAC std_ss [real_random_variable_def] \\
         CONJ_TAC >| (* 2 subgoals, similar tactics *)
         [ MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF >> art [FINITE_COUNT] \\
           Q.X_GEN_TAC `n` >> RW_TAC std_ss [] \\
           METIS_TAC [sub_not_infty],
           MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> art [FINITE_COUNT] \\
           Q.X_GEN_TAC `n` >> RW_TAC std_ss [] \\
           METIS_TAC [sub_not_infty] ]) \\
     FULL_SIMP_TAC std_ss [prob_space_def, random_variable_def, p_space_def,
                           events_def, real_random_variable_def] \\
     (* Here is the missing part in textbook proof, that we need to prove

        (\x. SIGMA (\n. X n x - Y n x) (count (f x)) * indicator_fn s x)

        is Borel-measurable (i.e. a random variable). To remove (f x), we
        find a way to rewrite `SIGMA` by the subtraction of two `suminf`s,
        each of which is Borel-measurable, using "ext_suminf_sum".
      *)
     Know `!x. SIGMA (\n. X n x - Y n x) (count (f x)) *
                 indicator_fn (m_space p DIFF N) x =
               SIGMA (\n. indicator_fn (m_space p DIFF N) x *
                          (\n. X n x - Y n x) n) (count (f x))`
     >- (GEN_TAC >> MATCH_MP_TAC EQ_SYM \\
         STRIP_ASSUME_TAC
           (Q.SPECL [`m_space p DIFF N`, `x`] indicator_fn_normal) >> art [] \\
         GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [mul_comm] \\
         irule EXTREAL_SUM_IMAGE_CMUL >> art [FINITE_COUNT] \\
         METIS_TAC [sub_not_infty]) >> BETA_TAC >> Rewr' \\
     Q.ABBREV_TAC `g = \x n. indicator_fn (m_space p DIFF N) x * (X n x - Y n x)` \\
     Know `!x n. (\n. indicator_fn (m_space p DIFF N) x * (X n x - Y n x)) n =
                 fn_plus (g x) n - fn_minus (g x) n`
     >- (rpt GEN_TAC \\
        `(\n. indicator_fn (m_space p DIFF N) x * (X n x - Y n x)) = g x`
             by METIS_TAC [] >> POP_ORW \\
         REWRITE_TAC [GSYM FN_DECOMP]) >> BETA_TAC >> Rewr' \\
     Know `!x. SIGMA (\n. fn_plus (g x) n - fn_minus (g x) n) (count (f x)) =
               SIGMA (fn_plus  (g x)) (count (f x)) -
               SIGMA (fn_minus (g x)) (count (f x))`
     >- (GEN_TAC >> irule EXTREAL_SUM_IMAGE_SUB >> art [FINITE_COUNT] \\
         DISJ2_TAC >> Q.X_GEN_TAC `n` >> DISCH_TAC \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC pos_not_neginf >> REWRITE_TAC [FN_MINUS_POS]) \\
         MATCH_MP_TAC FN_PLUS_NOT_INFTY \\
         Q.X_GEN_TAC `i` >> Q.UNABBREV_TAC `g` >> BETA_TAC \\
         STRIP_ASSUME_TAC
           (Q.SPECL [`m_space p DIFF N`, `x`] indicator_fn_normal) >> art [] \\
         Suff `X i x - Y i x <> PosInf` >- METIS_TAC [mul_not_infty] \\
         METIS_TAC [sub_not_infty]) >> Rewr' \\
     Know `!x. SIGMA (fn_plus (g x)) (count (f x)) <> NegInf`
     >- (GEN_TAC \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF >> art [FINITE_COUNT] \\
         Q.X_GEN_TAC `n` >> DISCH_TAC \\
         MATCH_MP_TAC pos_not_neginf >> REWRITE_TAC [FN_PLUS_POS]) >> DISCH_TAC \\
     Know `!x. SIGMA (fn_plus (g x)) (count (f x)) = suminf (fn_plus (g x))`
     >- (GEN_TAC >> MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC ext_suminf_sum \\
         RW_TAC std_ss [FN_PLUS_POS, Abbr `g`] \\
         reverse (Cases_on `x IN m_space p DIFF N`)
         >- (ASM_SIMP_TAC std_ss [indicator_fn_def, mul_lzero, FN_PLUS_ZERO]) \\
         ASM_SIMP_TAC std_ss [indicator_fn_def, mul_lone, FN_PLUS_ALT, max_refl]) \\
     DISCH_THEN ((FULL_SIMP_TAC std_ss) o wrap) \\
     Know `!x. SIGMA (fn_minus (g x)) (count (f x)) <> PosInf`
     >- (GEN_TAC \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> art [FINITE_COUNT] \\
         Q.X_GEN_TAC `n` >> DISCH_TAC \\
         MATCH_MP_TAC FN_MINUS_NOT_INFTY \\
         Q.X_GEN_TAC `i` >> Q.UNABBREV_TAC `g` >> BETA_TAC \\
         STRIP_ASSUME_TAC
           (Q.SPECL [`m_space p DIFF N`, `x`] indicator_fn_normal) >> art [] \\
         Suff `X i x - Y i x <> NegInf` >- METIS_TAC [mul_not_infty] \\
         METIS_TAC [sub_not_infty]) >> DISCH_TAC \\
     Know `!x. SIGMA (fn_minus (g x)) (count (f x)) = suminf (fn_minus (g x))`
     >- (GEN_TAC >> MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC ext_suminf_sum \\
         RW_TAC std_ss [FN_MINUS_POS, Abbr `g`] \\
         reverse (Cases_on `x IN m_space p DIFF N`)
         >- (ASM_SIMP_TAC std_ss [indicator_fn_def, mul_lzero, FN_MINUS_ZERO]) \\
         ASM_SIMP_TAC std_ss [indicator_fn_def, mul_lone, FN_MINUS_ALT,
                              min_refl, neg_0]) \\
     DISCH_THEN ((FULL_SIMP_TAC std_ss) o wrap) \\
    `sigma_algebra (m_space p,measurable_sets p)` by METIS_TAC [measure_space_def] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
     qexistsl_tac [`\x. suminf (fn_plus (g x))`, `\x. suminf (fn_minus (g x))`] \\
     ASM_SIMP_TAC std_ss [space_def] \\
     CONJ_TAC >| (* 2 subgoals, similar tactics *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC IN_MEASURABLE_BOREL_SUMINF >> BETA_TAC \\
       Q.EXISTS_TAC `\n x. fn_plus (g x) n` >> BETA_TAC \\
      `!x. (\n. (fn_plus (g x)) n) = fn_plus (g x)` by METIS_TAC [] >> POP_ORW \\
       ASM_SIMP_TAC std_ss [space_def, FN_PLUS_POS] \\
       Q.PAT_X_ASSUM `!x. suminf (fn_plus  (g x)) <> NegInf` K_TAC \\
       Q.PAT_X_ASSUM `!x. suminf (fn_minus (g x)) <> PosInf` K_TAC \\
       RW_TAC std_ss [Abbr `g`, FN_PLUS_ALT] \\
       HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX >> art [] \\
       reverse CONJ_TAC
       >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST' >> art []) \\
       ONCE_REWRITE_TAC [mul_comm] \\
       HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR >> art [subsets_def] \\
       reverse CONJ_TAC
       >- (MATCH_MP_TAC MEASURE_SPACE_COMPL >> fs [IN_NULL_SET, null_set_def]) \\
       MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
       qexistsl_tac [`X n`, `Y n`] >> ASM_SIMP_TAC std_ss [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC IN_MEASURABLE_BOREL_SUMINF >> BETA_TAC \\
       Q.EXISTS_TAC `\n x. fn_minus (g x) n` >> BETA_TAC \\
      `!x. (\n. (fn_minus (g x)) n) = fn_minus (g x)` by METIS_TAC [] >> POP_ORW \\
       ASM_SIMP_TAC std_ss [space_def, FN_MINUS_POS] \\
       Q.PAT_X_ASSUM `!x. suminf (fn_plus  (g x)) <> NegInf` K_TAC \\
       Q.PAT_X_ASSUM `!x. suminf (fn_minus (g x)) <> PosInf` K_TAC \\
       RW_TAC std_ss [Abbr `g`, FN_MINUS_ALT] \\
       HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MINUS \\
       Q.EXISTS_TAC `\x. min (indicator_fn (m_space p DIFF N) x * (X n x - Y n x)) 0` \\
       ASM_SIMP_TAC std_ss [] \\
       HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MIN >> art [] \\
       reverse CONJ_TAC
       >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST' >> art []) \\
       ONCE_REWRITE_TAC [mul_comm] \\
       HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR >> art [subsets_def] \\
       reverse CONJ_TAC
       >- (MATCH_MP_TAC MEASURE_SPACE_COMPL >> fs [IN_NULL_SET, null_set_def]) \\
       MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
       qexistsl_tac [`X n`, `Y n`] >> ASM_SIMP_TAC std_ss [] ])
 >> RW_TAC std_ss [converge_AE_def, AE_THM, GSYM IN_NULL_SET, almost_everywhere_def]
 >> Q.EXISTS_TAC `N`
 >> RW_TAC std_ss [LIM_SEQUENTIALLY, dist, indicator_fn_def, mul_rone, GSYM p_space_def]
 >> Q.EXISTS_TAC `f x`
 >> RW_TAC std_ss []
 >> Know `SIGMA (\n. X n x - Y n x) (count n) =
          SIGMA (\n. X n x - Y n x) ((count n) DIFF (from (f x)))`
 >- (irule EXTREAL_SUM_IMAGE_ZERO_DIFF \\
     fs [real_random_variable_def, IN_FROM] \\
     DISJ2_TAC >> RW_TAC std_ss [sub_not_infty]) >> Rewr'
 >> Suff `count n DIFF (from (f x)) = count (f x)`
 >- (Rewr' >> rw [])
 >> RW_TAC set_ss [Once EXTENSION, IN_FROM, IN_COUNT]
 >> rw []
QED

(* Theorem 5.2.1 (2) [2, p.113] *)
Theorem equivalent_thm2 :
    !p X Y a Z. prob_space p /\ equivalent p X Y /\
                (!n. real_random_variable (X n) p) /\
                (!n. real_random_variable (Y n) p) /\
                mono_increasing a /\ (sup (IMAGE a UNIV) = PosInf) /\
                (!n x. Z n x = SIGMA (\n. X n x - Y n x) (count n) / (a n)) ==>
         (Z --> (\x. 0)) (almost_everywhere p)
Proof
    rpt STRIP_TAC
 >> Know `?N f. N IN null_set p /\
               !x. x IN p_space p DIFF N ==> !n. f x <= n ==> (X n x - Y n x = 0)`
 >- (MATCH_MP_TAC equivalent_lemma >> art [])
 >> STRIP_TAC
 >> RW_TAC std_ss [converge_AE_def, AE_THM, GSYM IN_NULL_SET, almost_everywhere_def]
 >> Q.EXISTS_TAC `N`
 >> RW_TAC std_ss [LIM_SEQUENTIALLY, dist, GSYM p_space_def]
 >> `e <> 0` by PROVE_TAC [REAL_LT_IMP_NE]
 >> FULL_SIMP_TAC std_ss [real_random_variable_def, ext_mono_increasing_def]
 >> Know `!m. SIGMA (\n. X n x - Y n x) (count m) <> PosInf`
 >- (GEN_TAC >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
     rw [sub_not_infty]) >> DISCH_TAC
 >> Know `!m. SIGMA (\n. X n x - Y n x) (count m) <> NegInf`
 >- (GEN_TAC >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
     rw [sub_not_infty]) >> DISCH_TAC
 (* 1. if (a n) ever reached PosInf, use that n directly *)
 >> reverse (Cases_on `!n. a n <> PosInf`)
 >- (FULL_SIMP_TAC std_ss [] >> Q.EXISTS_TAC `n` \\
     Q.X_GEN_TAC `m` >> DISCH_TAC \\
     Know `a n <= a m` >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     ASM_REWRITE_TAC [le_infty] >> Rewr' \\
    `?r. SIGMA (\n. X n x - Y n x) (count m) = Normal r`
         by METIS_TAC [extreal_cases] \\
     rw [extreal_div_def, real_normal, extreal_of_num_def])
 (* eliminate `real 0` first *)
 >> `real 0 = 0` by METIS_TAC [extreal_of_num_def, real_normal]
 >> POP_ASSUM (fn th => FULL_SIMP_TAC bool_ss [REAL_SUB_RZERO, th])
 >> Q.PAT_X_ASSUM `!x. x IN p_space p DIFF N ==> P` (MP_TAC o (Q.SPEC `x`))
 >> RW_TAC std_ss []
 (* now estimating N *)
 >> Know `?k. abs (SIGMA (\n. X n x - Y n x) (count (f x))) / Normal e < a k`
 >- (CCONTR_TAC >> FULL_SIMP_TAC std_ss [] \\
     Know `sup (IMAGE a UNIV) <=
           abs (SIGMA (\n. X n x - Y n x) (count (f x))) / Normal e`
     >- (RW_TAC set_ss [sup_le'] >> fs [extreal_lt_def]) >> art [] \\
    `?r. SIGMA (\n. X n x - Y n x) (count (f x)) = Normal r`
         by METIS_TAC [extreal_cases] >> art [] \\
     ASM_SIMP_TAC std_ss [extreal_abs_def, extreal_div_eq, extreal_le_def])
 >> STRIP_TAC
 >> Q.EXISTS_TAC `MAX k (f x)`
 >> RW_TAC std_ss [MAX_LE]
 >> Know `0 <= abs (SIGMA (\n. X n x - Y n x) (count (f x))) / Normal e`
 >- (MATCH_MP_TAC le_div >> art [abs_pos]) >> DISCH_TAC
 >> `0 < a k` by PROVE_TAC [let_trans]
 >> `0 < a n` by PROVE_TAC [lte_trans]
 >> Know `SIGMA (\n. X n x - Y n x) (count n) =
          SIGMA (\n. X n x - Y n x) ((count n) DIFF (from (f x)))`
 >- (irule EXTREAL_SUM_IMAGE_ZERO_DIFF >> fs [IN_FROM] \\
     DISJ2_TAC >> RW_TAC std_ss [sub_not_infty]) >> Rewr'
 >> Know `count n DIFF (from (f x)) = count (f x)`
 >- (RW_TAC set_ss [Once EXTENSION, IN_FROM, IN_COUNT] \\
     rw []) >> Rewr'
 >> Know `abs (real (SIGMA (\n. X n x - Y n x) (count (f x)) / a n)) < e <=>
          abs (SIGMA (\n. X n x - Y n x) (count (f x)) / a n) < Normal e`
 >- (`?r. SIGMA (\n. X n x - Y n x) (count (f x)) = Normal r`
         by METIS_TAC [extreal_cases] >> POP_ORW \\
     `a n <> NegInf` by PROVE_TAC [pos_not_neginf, lt_imp_le] \\
     `?b. a n = Normal b` by METIS_TAC [extreal_cases] >> art [] \\
     `a n <> 0` by PROVE_TAC [lt_imp_ne] \\
     `b <> 0` by METIS_TAC [extreal_of_num_def, extreal_11] \\
     ASM_SIMP_TAC real_ss [extreal_abs_def, real_normal, extreal_div_eq,
                           extreal_lt_eq, ABS_DIV]) >> Rewr'
 >> Know `abs (SIGMA (\n. X n x - Y n x) (count (f x)) / a n) =
          abs (SIGMA (\n. X n x - Y n x) (count (f x))) / abs (a n)`
 >- (MATCH_MP_TAC abs_div >> art [] \\
     PROVE_TAC [lt_imp_ne]) >> Rewr'
 >> Know `abs (a n) = a n`
 >- (REWRITE_TAC [abs_refl] \\
     MATCH_MP_TAC lt_imp_le >> art []) >> Rewr'
 >> `a n <> NegInf` by PROVE_TAC [pos_not_neginf, lt_imp_le]
 >> `?b. a n = Normal b` by METIS_TAC [extreal_cases] >> art []
 >> Know `abs (SIGMA (\n. X n x - Y n x) (count (f x))) / Normal b < Normal e <=>
          abs (SIGMA (\n. X n x - Y n x) (count (f x))) / Normal e < Normal b`
 >- (MATCH_MP_TAC EQ_TRANS \\
     Q.EXISTS_TAC `abs (SIGMA (\n. X n x - Y n x) (count (f x))) < Normal e * Normal b` \\
     CONJ_TAC >| (* 2 subgoals, similar tactics *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC lt_ldiv \\
       METIS_TAC [extreal_of_num_def, extreal_lt_eq],
       (* goal 2 (of 2) *)
       ONCE_REWRITE_TAC [mul_comm] \\
       MATCH_MP_TAC EQ_SYM \\
       MATCH_MP_TAC lt_ldiv >> art [] ]) >> Rewr'
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
 >> MATCH_MP_TAC lte_trans
 >> Q.EXISTS_TAC `a k` >> art []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

(* Theorem 3.2.1, Part I [2, p.45] *)
Theorem expectation_bounds :
    !p X. prob_space p /\ real_random_variable X p ==>
          suminf (\n. prob p {x | x IN p_space p /\ &SUC n <= abs (X x)}) <=
          expectation p (abs o X) /\ expectation p (abs o X) <= 1 +
          suminf (\n. prob p {x | x IN p_space p /\ &SUC n <= abs (X x)})
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Q.ABBREV_TAC ‘A = \n. {x | x IN p_space p /\ &n <= abs (X x) /\ abs (X x) < &SUC n}’
 >> Know ‘!n. A n IN events p’
 >- (GEN_TAC \\
     fs [prob_space_def, p_space_def, events_def, real_random_variable, Abbr ‘A’] \\
    ‘{x | x IN m_space p /\ &n <= abs (X x) /\ abs (X x) < &SUC n} =
       ({x | &n <= abs (X x)} INTER m_space p) INTER
       ({x | abs (X x) < &SUC n} INTER m_space p)’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC MEASURE_SPACE_INTER >> art [] \\
     RW_TAC std_ss [le_abs_bounds, abs_bounds_lt] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
      ‘{x | X x <= -&n \/ &n <= X x} INTER m_space p =
         ({x | X x <= -&n} INTER m_space p) UNION
         ({x | &n <= X x} INTER m_space p)’ by SET_TAC [] >> POP_ORW \\
       MATCH_MP_TAC MEASURE_SPACE_UNION >> art [] \\
       METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE],
       (* goal 2 (of 2) *)
      ‘{x | -&SUC n < X x /\ X x < &SUC n} INTER m_space p =
         ({x | -&SUC n < X x} INTER m_space p) INTER
         ({x | X x < &SUC n} INTER m_space p)’ by SET_TAC [] >> POP_ORW \\
       MATCH_MP_TAC MEASURE_SPACE_INTER >> art [] \\
       METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE] ]) >> DISCH_TAC
 >> Know ‘BIGUNION (IMAGE A UNIV) = p_space p’
 >- (rw [Once EXTENSION, IN_BIGUNION_IMAGE, Abbr ‘A’] \\
     EQ_TAC >> STRIP_TAC >> fs [real_random_variable_def] \\
    ‘?r. X x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     REWRITE_TAC [extreal_abs_def, extreal_of_num_def, extreal_lt_eq, extreal_le_eq] \\
     MP_TAC (Q.SPEC ‘1’ REAL_ARCH_LEAST) >> rw []) >> DISCH_TAC
 >> Know ‘!m n. m <> n ==> DISJOINT (A m) (A n)’
 >- (rw [Abbr ‘A’, DISJOINT_ALT] \\
     STRONG_DISJ_TAC >> REWRITE_TAC [extreal_lt_def] \\
     rename1 ‘&SUC n <= abs (X y)’ \\
    ‘m < n \/ n < m’ by RW_TAC arith_ss [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
      ‘SUC m <= n’ by RW_TAC arith_ss [] \\
      ‘&SUC m <= (&n) :extreal’ by rw [extreal_of_num_def, extreal_le_eq] \\
      ‘abs (X y) < &n’ by PROVE_TAC [lte_trans] \\
       METIS_TAC [let_antisym],
       (* goal 2 (of 2) *)
      ‘SUC n <= m’ by RW_TAC arith_ss [] \\
      ‘&SUC n <= (&m) :extreal’ by rw [extreal_of_num_def, extreal_le_eq] \\
       METIS_TAC [le_trans] ]) >> DISCH_TAC
 >> Know ‘expectation p (abs o X) =
          suminf (\n. pos_fn_integral p (\x. abs (X x) * indicator_fn (A n) x))’
 >- (REWRITE_TAC [expectation_def] \\
     Know ‘integral p (abs o X) = pos_fn_integral p (abs o X)’
     >- (MATCH_MP_TAC integral_pos_fn >> fs [prob_space_def, abs_pos]) >> Rewr' \\
     Know ‘pos_fn_integral p (abs o X) =
           pos_fn_integral p (\x. (abs o X) x * indicator_fn (p_space p) x)’
     >- (REWRITE_TAC [p_space_def] >> MATCH_MP_TAC pos_fn_integral_mspace \\
         fs [prob_space_def, abs_pos]) >> Rewr' \\
     SIMP_TAC std_ss [o_DEF] \\
     Q.PAT_X_ASSUM ‘_ = p_space p’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.ABBREV_TAC ‘f = \n x. abs (X x) * indicator_fn (A n) x’ \\
     Know ‘pos_fn_integral p (\x. abs (X x) * indicator_fn (BIGUNION (IMAGE A UNIV)) x) =
           pos_fn_integral p (\x. suminf (\n. f n x))’
     >- (MATCH_MP_TAC pos_fn_integral_cong >> fs [prob_space_def] \\
         CONJ_TAC >- (rpt STRIP_TAC \\
                      MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS]) \\
         CONJ_TAC >- (rpt STRIP_TAC \\
                      MATCH_MP_TAC ext_suminf_pos >> rw [Abbr ‘f’] \\
                      MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS]) \\
         rw [Abbr ‘f’] >> fs [real_random_variable_def] \\
        ‘?r. X x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         REWRITE_TAC [extreal_abs_def] \\
         Know ‘suminf (\n. Normal (abs r) * indicator_fn (A n) x) =
               Normal (abs r) * suminf (\n. indicator_fn (A n) x)’
         >- (HO_MATCH_MP_TAC ext_suminf_cmul \\
             rw [extreal_of_num_def, extreal_le_eq, INDICATOR_FN_POS]) >> Rewr' \\
         Suff ‘indicator_fn (BIGUNION (IMAGE A UNIV)) x =
               suminf (\n. indicator_fn (A n) x)’ >- rw [] \\
         MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC indicator_fn_suminf \\
         rw []) >> Rewr' \\
    ‘!n x. abs (X x) * indicator_fn (A n) x = f n x’ by METIS_TAC [] >> POP_ORW \\
    ‘!n. (\x. f n x) = f n’ by METIS_TAC [ETA_THM] >> POP_ORW \\
     MATCH_MP_TAC pos_fn_integral_suminf \\
     fs [prob_space_def, real_random_variable, Abbr ‘f’] \\
     CONJ_TAC >- (rpt STRIP_TAC \\
                  MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS]) \\
     Q.X_GEN_TAC ‘n’ \\
     HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR \\
     CONJ_TAC >- fs [measure_space_def] \\
     CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS \\
                  Q.EXISTS_TAC ‘X’ >> fs [p_space_def, events_def, measure_space_def]) \\
     FULL_SIMP_TAC std_ss [subsets_def, events_def]) >> DISCH_TAC
 >> Know ‘suminf (\n. &n * prob p (A n)) <= expectation p (abs o X)’
 >- (POP_ORW \\
     MATCH_MP_TAC ext_suminf_mono >> rw []
     >- (MATCH_MP_TAC le_mul \\
         CONJ_TAC >- rw [extreal_of_num_def, extreal_le_eq] \\
         MATCH_MP_TAC PROB_POSITIVE >> art []) \\
     Know ‘prob p (A n) = pos_fn_integral p (indicator_fn (A n))’
     >- (fs [prob_space_def, prob_def, events_def, Once EQ_SYM_EQ] \\
         MATCH_MP_TAC pos_fn_integral_indicator >> art []) >> Rewr' \\
     Know ‘&n * pos_fn_integral p (indicator_fn (A n)) =
           pos_fn_integral p (\x. &n * indicator_fn (A n) x)’
     >- (fs [prob_space_def, extreal_of_num_def, events_def, Once EQ_SYM_EQ] \\
         MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) >> Rewr' \\
     MATCH_MP_TAC pos_fn_integral_mono >> rw []
     >- (MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, extreal_of_num_def, extreal_le_eq]) \\
     reverse (Cases_on ‘x IN (A n)’)
     >- rw [indicator_fn_def, mul_rzero, le_refl] \\
     POP_ASSUM MP_TAC >> rw [Abbr ‘A’, indicator_fn_def, mul_rone]) >> DISCH_TAC
 >> Know ‘expectation p (abs o X) <= suminf (\n. &SUC n * prob p (A n))’
 >- (Q.PAT_X_ASSUM ‘expectation p (abs o X) = _’ (ONCE_REWRITE_TAC o wrap) \\
     MATCH_MP_TAC ext_suminf_mono >> rw []
     >- (MATCH_MP_TAC pos_fn_integral_pos >> fs [prob_space_def] \\
         rpt STRIP_TAC >> MATCH_MP_TAC le_mul \\
         rw [abs_pos, INDICATOR_FN_POS]) \\
     Know ‘prob p (A n) = pos_fn_integral p (indicator_fn (A n))’
     >- (fs [prob_space_def, prob_def, events_def, Once EQ_SYM_EQ] \\
         MATCH_MP_TAC pos_fn_integral_indicator >> art []) >> Rewr' \\
     Know ‘&SUC n * pos_fn_integral p (indicator_fn (A n)) =
           pos_fn_integral p (\x. &SUC n * indicator_fn (A n) x)’
     >- (fs [prob_space_def, extreal_of_num_def, events_def, Once EQ_SYM_EQ] \\
         MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) >> Rewr' \\
     MATCH_MP_TAC pos_fn_integral_mono >> rw []
     >- (MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, abs_pos]) \\
     reverse (Cases_on ‘x IN (A n)’)
     >- rw [indicator_fn_def, mul_rzero, le_refl] \\
     POP_ASSUM MP_TAC >> rw [Abbr ‘A’, indicator_fn_def, mul_rone] \\
     MATCH_MP_TAC lt_imp_le >> art []) >> DISCH_TAC
 >> Know ‘suminf (\n. &SUC n * prob p (A n)) = 1 + suminf (\n. &n * prob p (A n))’
 >- (Know ‘!n. &SUC n = (1 :extreal) + &n’
     >- (GEN_TAC >> ‘SUC n = 1 + n’ by RW_TAC arith_ss [] \\
         rw [extreal_of_num_def, extreal_add_def, extreal_11]) >> Rewr' \\
     Know ‘!n. (1 + &n) * prob p (A n) = 1 * prob p (A n) + &n * prob p (A n)’
     >- (GEN_TAC >> ONCE_REWRITE_TAC [mul_comm] \\
         MATCH_MP_TAC add_ldistrib_pos >> REWRITE_TAC [le_01] \\
         rw [extreal_of_num_def, extreal_le_eq]) >> Rewr' \\
     REWRITE_TAC [mul_lone] \\
     Know ‘suminf (\n. prob p (A n) + &n * prob p (A n)) =
           suminf (\n. prob p (A n)) + suminf (\n. &n * prob p (A n))’
     >- (HO_MATCH_MP_TAC ext_suminf_add \\
         GEN_TAC >> STRONG_CONJ_TAC >- (MATCH_MP_TAC PROB_POSITIVE >> art []) \\
         DISCH_TAC >> MATCH_MP_TAC le_mul >> art [] \\
         rw [extreal_of_num_def, extreal_le_eq]) >> Rewr' \\
     Know ‘suminf (prob p o A) = prob p (BIGUNION (IMAGE A UNIV))’
     >- (MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC PROB_COUNTABLY_ADDITIVE >> rw [IN_FUNSET, IN_UNIV]) \\
     REWRITE_TAC [o_DEF] >> Rewr' \\
     Q.PAT_X_ASSUM ‘BIGUNION (IMAGE A UNIV) = p_space p’ (ONCE_REWRITE_TAC o wrap) \\
     simp [PROB_UNIV])
 >> Q.PAT_X_ASSUM ‘expectation p (abs o X) = _’ K_TAC
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> Suff ‘suminf (\n. prob p {x | x IN p_space p /\ &SUC n <= abs (X x)}) =
          suminf (\n. &n * prob p (A n))’
 >- (Rewr' >> art [])
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 (* stage work *)
 >> Q.ABBREV_TAC ‘B = \n. {x | x IN p_space p /\ &n <= abs (X x)}’
 >> Know ‘!n. B n IN events p’
 >- (RW_TAC std_ss [Abbr ‘B’] \\
     fs [prob_space_def, p_space_def, events_def, real_random_variable, le_abs_bounds] \\
    ‘{x | x IN m_space p /\ (X x <= -&n \/ &n <= X x)} =
       ({x | X x <= -&n} INTER m_space p) UNION
       ({x | &n <= X x} INTER m_space p)’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC MEASURE_SPACE_UNION >> art [] \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC
 >> Know ‘!m n. m <= n ==> B n SUBSET B m’
 >- (rw [Abbr ‘B’, SUBSET_DEF] \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC ‘&n’ >> art [] \\
     rw [extreal_of_num_def, extreal_le_eq]) >> DISCH_TAC
 >> Q.ABBREV_TAC ‘f = \n. prob p (B n)’
 >> ‘!n. prob p {x | x IN p_space p /\ &SUC n <= abs (X x)} = f (SUC n)’ by METIS_TAC []
 >> POP_ORW
 (* new goal: suminf (\n. &n * prob p (A n)) = suminf (\n. f (SUC n)) *)
 >> Know ‘!n. 0 <= f n’
 >- (rw [Abbr ‘f’] \\
     MATCH_MP_TAC PROB_POSITIVE >> art []) >> DISCH_TAC
 >> Know ‘!n. 0 <= &n * prob p (A n)’
 >- (GEN_TAC >> MATCH_MP_TAC le_mul \\
     CONJ_TAC >- rw [extreal_of_num_def, extreal_le_eq] \\
     MATCH_MP_TAC PROB_POSITIVE >> art []) >> DISCH_TAC
 >> Know ‘!n. f n <> PosInf /\ f n <> NegInf’
 >- (GEN_TAC >> Q.UNABBREV_TAC ‘f’ \\
     METIS_TAC [PROB_FINITE]) >> DISCH_TAC
 (* stage work *)
 >> Know ‘!N. 0 < N ==> (SIGMA (\n. &n * prob p (A n)) (count N) =
                         SIGMA (\n. f (SUC n)) (count (PRE N)) - &PRE N * f N)’
 >- (rpt STRIP_TAC \\
     Know ‘!n. prob p (A n) = f n - f (SUC n)’
     >- (RW_TAC std_ss [Abbr ‘f’, Abbr ‘B’] \\
         Know ‘A n = {x | x IN p_space p /\ &n <= abs (X x)} DIFF
                     {x | x IN p_space p /\ &SUC n <= abs (X x)}’
         >- (rw [Once EXTENSION, extreal_lt_def, Abbr ‘A’] >> SET_TAC []) >> Rewr' \\
         MATCH_MP_TAC PROB_DIFF_SUBSET >> art [] \\
         fs [SUBSET_DEF, GSPECIFICATION] \\
         rpt STRIP_TAC \\
         MATCH_MP_TAC le_trans >> Q.EXISTS_TAC ‘&SUC n’ >> art [] \\
         rw [extreal_of_num_def, extreal_le_eq]) >> Rewr' \\
     Know ‘!n. &n * (f n - f (SUC n)) = &n * f n - &n * f (SUC n)’
     >- (GEN_TAC >> MATCH_MP_TAC sub_ldistrib \\
         rw [extreal_of_num_def, extreal_not_infty]) >> Rewr' \\
     Know ‘SIGMA (\n. (\n. &n * f n) n - (\n. &n * f (SUC n)) n) (count N) =
           SIGMA (\n. &n * f n) (count N) - SIGMA (\n. &n * f (SUC n)) (count N)’
     >- (irule EXTREAL_SUM_IMAGE_SUB >> rw [FINITE_COUNT] \\
         DISJ1_TAC >> NTAC 2 STRIP_TAC \\
         simp [extreal_of_num_def] \\
         Suff ‘(0 :real) <= &x’ >- METIS_TAC [mul_not_infty] >> rw []) \\
     BETA_TAC >> Rewr' \\
     Know ‘SIGMA (\n. &n * f n) (count N) = 0 + SIGMA (\n. &n * f n) (count N DELETE 0)’
     >- (Know ‘count N = 0 INSERT (count N DELETE 0)’
         >- (rw [Once EXTENSION, IN_COUNT]) \\
         DISCH_THEN (GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites o wrap) \\
         Know ‘SIGMA (\n. &n * f n) (0 INSERT (count N DELETE 0)) =
               (\n. &n * f n) 0 + SIGMA (\n. &n * f n) ((count N DELETE 0) DELETE 0)’
         >- (irule EXTREAL_SUM_IMAGE_PROPERTY >> rw [FINITE_COUNT] \\
             DISJ1_TAC >> GEN_TAC >> DISCH_TAC \\
             simp [extreal_of_num_def] \\
             Suff ‘(0 :real) <= &x’ >- METIS_TAC [mul_not_infty] >> rw []) \\
        ‘count N DELETE 0 DELETE 0 = count N DELETE 0’ by SET_TAC [] >> POP_ORW \\
         Rewr' >> rw [mul_lzero]) >> Rewr' \\
     Know ‘count N DELETE 0 = IMAGE SUC (count (PRE N))’
     >- (rw [Once EXTENSION, IN_IMAGE, IN_COUNT] \\
         EQ_TAC >> rpt STRIP_TAC >| (* 3 subgoals *)
         [ (* goal 1 (of 3) *)
           Q.EXISTS_TAC ‘PRE x’ >> rw [] \\
          ‘0 < x’ by RW_TAC arith_ss [] \\
           METIS_TAC [INV_PRE_LESS],
           (* goal 2 (of 3) *)
          ‘0 < x’ by RW_TAC arith_ss [] \\
           simp [GSYM INV_PRE_LESS],
           (* goal 3 (of 3) *)
           fs [] ]) >> Rewr' \\
     Know ‘SIGMA (\n. &n * f n) (IMAGE SUC (count (PRE N))) =
           SIGMA ((\n. &n * f n) o SUC) (count (PRE N))’
     >- (irule EXTREAL_SUM_IMAGE_IMAGE >> RW_TAC std_ss [FINITE_COUNT] >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           DISJ1_TAC >> GEN_TAC >> DISCH_TAC \\
           simp [extreal_of_num_def] \\
           Suff ‘(0 :real) <= &x’ >- METIS_TAC [mul_not_infty] >> rw [],
           (* goal 2 (of 2) *)
           MATCH_MP_TAC INJ_IMAGE \\
           Q.EXISTS_TAC ‘count N DELETE 0’ \\
           rw [INJ_DEF] ]) >> Rewr' \\
     SIMP_TAC std_ss [o_DEF] \\
    ‘count N = (PRE N) INSERT (count (PRE N))’ by rw [Once EXTENSION, IN_COUNT] \\
     POP_ASSUM (GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites o wrap) \\
     Know ‘SIGMA (\n. &n * f (SUC n)) (PRE N INSERT count (PRE N)) =
           (\n. &n * f (SUC n)) (PRE N) +
           SIGMA (\n. &n * f (SUC n)) (count (PRE N) DELETE (PRE N))’
     >- (irule EXTREAL_SUM_IMAGE_PROPERTY >> RW_TAC std_ss [FINITE_COUNT] \\
         DISJ1_TAC >> GEN_TAC >> DISCH_TAC \\
         simp [extreal_of_num_def] \\
         Suff ‘(0 :real) <= &x’ >- METIS_TAC [mul_not_infty] >> rw []) \\
     BETA_TAC >> Rewr' \\
    ‘(count (PRE N) DELETE PRE N) = count (PRE N)’
       by rw [Once EXTENSION, IN_COUNT] >> POP_ORW \\
    ‘SUC (PRE N) = N’ by METIS_TAC [SUC_PRE] >> POP_ORW \\
     Know ‘0 (* a *) + SIGMA (\x. &SUC x * f (SUC x)) (count (PRE N)) (* c *) -
           (&PRE N * f N (* b *) + SIGMA (\n. &n * f (SUC n)) (count (PRE N)) (* d *)) =
           0 (* a *) - &PRE N * f N (* b *) +
           (SIGMA (\x. &SUC x * f (SUC x)) (count (PRE N)) (* c *) -
            SIGMA (\n. &n * f (SUC n)) (count (PRE N)) (* d *))’
     >- (MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC add2_sub2 (* a - b + (c - d) = a + c - (b + d) *) \\
         rw [extreal_of_num_def, extreal_not_infty] >| (* 6 subgoals *)
         [ (* goal 1 (of 6) *)
           Suff ‘(0 :real) <= &PRE N’ >- METIS_TAC [mul_not_infty] >> rw [],
           (* goal 2 (of 6) *)
           MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> rw [FINITE_COUNT] \\
           Suff ‘(0 :real) <= &SUC x’ >- METIS_TAC [mul_not_infty] >> rw [],
           (* goal 3 (of 6) *)
           MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> rw [FINITE_COUNT] \\
           Suff ‘(0 :real) <= &x’ >- METIS_TAC [mul_not_infty] >> rw [],
           (* goal 4 (of 6) *)
           Suff ‘(0 :real) <= &PRE N’ >- METIS_TAC [mul_not_infty] >> rw [],
           (* goal 5 (of 6) *)
           MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF >> rw [FINITE_COUNT] \\
           Suff ‘(0 :real) <= &SUC x’ >- METIS_TAC [mul_not_infty] >> rw [],
           (* goal 6 (of 6) *)
           MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF >> rw [FINITE_COUNT] \\
           Suff ‘(0 :real) <= &x’ >- METIS_TAC [mul_not_infty] >> rw [] ]) >> Rewr' \\
     REWRITE_TAC [sub_lzero] \\
     Know ‘SIGMA (\x. &SUC x * f (SUC x)) (count (PRE N)) -
           SIGMA (\n. &n * f (SUC n)) (count (PRE N)) =
           SIGMA (\n. (\x. &SUC x * f (SUC x)) n - (\n. &n * f (SUC n)) n) (count (PRE N))’
     >- (MATCH_MP_TAC EQ_SYM \\
         irule EXTREAL_SUM_IMAGE_SUB >> rw [FINITE_COUNT] \\
         DISJ1_TAC >> GEN_TAC >> DISCH_TAC \\
         REWRITE_TAC [extreal_of_num_def] \\
         CONJ_TAC >| (* 2 subgoals *)
         [ Suff ‘(0 :real) <= &SUC x’ >- METIS_TAC [mul_not_infty] >> rw [],
           Suff ‘(0 :real) <= &x’ >- METIS_TAC [mul_not_infty] >> rw [] ]) \\
     BETA_TAC >> Rewr' \\
     Know ‘!n. &SUC n * f (SUC n) - &n * f (SUC n) = f (SUC n)’
     >- (GEN_TAC \\
         Know ‘&SUC n * f (SUC n) - &n * f (SUC n) = (&SUC n - &n) * f (SUC n)’
         >- (MATCH_MP_TAC EQ_SYM \\
             MATCH_MP_TAC sub_rdistrib >> rw [extreal_of_num_def, extreal_not_infty]) >> Rewr' \\
         Know ‘&SUC n - &n = 1’
         >- (REWRITE_TAC [extreal_of_num_def, extreal_sub_def, extreal_11] \\
             REWRITE_TAC [real_of_num, REAL_1] >> REAL_ARITH_TAC) >> Rewr' \\
         REWRITE_TAC [mul_lone]) >> Rewr' \\
     Know ‘-(&PRE N * f N) + SIGMA (\n. f (SUC n)) (count (PRE N)) =
           SIGMA (\n. f (SUC n)) (count (PRE N)) + -(&PRE N * f N)’
     >- (MATCH_MP_TAC add_comm >> DISJ2_TAC \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> rw [FINITE_COUNT]) \\
         Suff ‘&PRE N * f N <> NegInf’ >- METIS_TAC [extreal_ainv_def, neg_neg] \\
         REWRITE_TAC [extreal_of_num_def] \\
         Suff ‘(0 :real) <= &PRE N’ >- METIS_TAC [mul_not_infty] >> rw []) >> Rewr' \\
     MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC extreal_sub_add >> DISJ2_TAC \\
     CONJ_TAC >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> rw [FINITE_COUNT]) \\
     REWRITE_TAC [extreal_of_num_def] \\
     Suff ‘(0 :real) <= &PRE N’ >- METIS_TAC [mul_not_infty] >> rw []) >> DISCH_TAC
 >> REWRITE_TAC [GSYM le_antisym]
 >> CONJ_TAC (* easy part *)
 >- (rw [ext_suminf_def, sup_le', le_sup'] \\
     Cases_on ‘n = 0’ >- (rw [EXTREAL_SUM_IMAGE_EMPTY] \\
                          POP_ASSUM MATCH_MP_TAC \\
                          Q.EXISTS_TAC ‘0’ >> rw [EXTREAL_SUM_IMAGE_EMPTY]) \\
     Know ‘SIGMA (\n. &n * prob p (A n)) (count n) =
           SIGMA (\n. f (SUC n)) (count (PRE n)) - &PRE n * f n’
     >- (FIRST_X_ASSUM MATCH_MP_TAC >> RW_TAC arith_ss []) >> Rewr' \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC ‘SIGMA (\n. f (SUC n)) (count (PRE n))’ \\
     reverse CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC \\
                          Q.EXISTS_TAC ‘PRE n’ >> REWRITE_TAC []) \\
     MATCH_MP_TAC sub_le_imp \\
     REWRITE_TAC [extreal_of_num_def] \\
     CONJ_TAC >- (Suff ‘(0 :real) <= &PRE n’ >- METIS_TAC [mul_not_infty] >> rw []) \\
     CONJ_TAC >- (Suff ‘(0 :real) <= &PRE n’ >- METIS_TAC [mul_not_infty] >> rw []) \\
     MATCH_MP_TAC le_addr_imp \\
     MATCH_MP_TAC le_mul >> art [] \\
     rw [extreal_of_num_def, extreal_le_eq])
 (* special case *)
 >> Cases_on ‘expectation p (abs o X) = PosInf’
 >- (Know ‘suminf (\n. &n * prob p (A n)) = PosInf’
     >- (CCONTR_TAC \\
         Know ‘suminf (\n. &n * prob p (A n)) <> NegInf’
         >- (MATCH_MP_TAC pos_not_neginf \\
             MATCH_MP_TAC ext_suminf_pos >> rw []) >> DISCH_TAC \\
        ‘?r. suminf (\n. &n * prob p (A n)) = Normal r’ by METIS_TAC [extreal_cases] \\
         FULL_SIMP_TAC std_ss [le_infty, extreal_of_num_def, extreal_not_infty, extreal_add_def]) \\
     Rewr' >> REWRITE_TAC [le_infty])
 (* hard part *)
 >> Q.ABBREV_TAC ‘g = \n. pos_fn_integral p (\x. abs (X x) * indicator_fn (B n) x)’
 >> Know ‘!m n. m <= n ==> g n <= g m’
 >- (rw [Abbr ‘g’] \\
     MATCH_MP_TAC pos_fn_integral_mono >> rw []
     >- (MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS]) \\
     MATCH_MP_TAC le_lmul_imp >> REWRITE_TAC [abs_pos] \\
     MATCH_MP_TAC INDICATOR_FN_MONO \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> DISCH_TAC
 >> Know ‘!N. 0 < N ==> &PRE N * f N <= g N’
 >- (RW_TAC std_ss [Abbr ‘g’, Abbr ‘B’] \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC ‘&N * f N’ \\
     CONJ_TAC >- (ONCE_REWRITE_TAC [mul_comm] \\
                  MATCH_MP_TAC le_lmul_imp >> rw [extreal_of_num_def, extreal_le_eq]) \\
    ‘f N = prob p {x | x IN p_space p /\ &N <= abs (X x)}’ by METIS_TAC [] >> POP_ORW \\
     Know ‘prob p {x | x IN p_space p /\ &N <= abs (X x)} =
           pos_fn_integral p (indicator_fn {x | x IN p_space p /\ &N <= abs (X x)})’
     >- (REWRITE_TAC [Once EQ_SYM_EQ, prob_def, p_space_def] \\
         MATCH_MP_TAC pos_fn_integral_indicator \\
         fs [prob_space_def, p_space_def, events_def]) >> Rewr' \\
     Know ‘&N * pos_fn_integral p (indicator_fn {x | x IN p_space p /\ &N <= abs (X x)}) =
           pos_fn_integral p (\x. &N * (indicator_fn {x | x IN p_space p /\ &N <= abs (X x)} x))’
     >- (REWRITE_TAC [Once EQ_SYM_EQ, extreal_of_num_def] \\
         MATCH_MP_TAC pos_fn_integral_cmul >> fs [INDICATOR_FN_POS, prob_space_def]) >> Rewr' \\
     MATCH_MP_TAC pos_fn_integral_mono >> rw []
     >- (MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS] \\
         rw [extreal_of_num_def, extreal_le_eq]) \\
     reverse (Cases_on ‘x IN {x | x IN p_space p /\ &N <= abs (X x)}’)
     >- (ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rzero, le_refl]) \\
     ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rone] \\
     fs []) >> DISCH_TAC
 (* hard part *)
 >> rw [ext_suminf_def, sup_le', le_sup']
 >> MATCH_MP_TAC le_epsilon (* key step *)
 >> rpt STRIP_TAC
 >> Know ‘e <> NegInf’
 >- (MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC lt_imp_le >> art []) >> DISCH_TAC
 >> Know ‘SIGMA (\n. f (SUC n)) (count n) <= y' + e <=>
          SIGMA (\n. f (SUC n)) (count n) - e <= y'’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC sub_le_eq >> art []) >> Rewr'
 (* applying le_inf_epsilon_set *)
 >> Suff ‘inf (IMAGE (\n. g n) UNIV) = 0’
 >- (DISCH_TAC \\
     MP_TAC (Q.SPECL [‘IMAGE (\n. (g :num -> extreal) n) UNIV’, ‘e’]
                     le_inf_epsilon_set) \\
     Know ‘?x. x IN IMAGE (\n. g n) UNIV /\ x <> PosInf’
     >- (Q.EXISTS_TAC ‘g 0’ (* any value is fine here *) \\
         CONJ_TAC >- (rw [IN_IMAGE, IN_UNIV] \\
                      Q.EXISTS_TAC ‘0’ >> REWRITE_TAC []) \\
         rw [Abbr ‘g’, lt_infty] \\
         MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘expectation p (abs o X)’ \\
         reverse CONJ_TAC >- art [GSYM lt_infty] \\
         Know ‘expectation p (abs o X) = pos_fn_integral p (abs o X)’
         >- (REWRITE_TAC [expectation_def] \\
             MATCH_MP_TAC integral_pos_fn >> fs [prob_space_def, abs_pos]) >> Rewr' \\
         MATCH_MP_TAC pos_fn_integral_mono >> rw []
         >- (MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS]) \\
         Cases_on ‘x IN B 0’ \\ (* 2 subgoals, same tactics *)
         rw [indicator_fn_def, mul_rone, le_refl, mul_rzero, abs_pos]) \\
     Know ‘inf (IMAGE (\n. g n) univ(:num)) <> NegInf’
     >- (MATCH_MP_TAC pos_not_neginf \\
         rw [le_inf', IN_IMAGE, IN_UNIV, Abbr ‘g’] \\
         MATCH_MP_TAC pos_fn_integral_pos \\
         CONJ_TAC >- FULL_SIMP_TAC std_ss [prob_space_def] \\
         RW_TAC std_ss [] \\
         MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS]) \\
     RW_TAC std_ss [IN_IMAGE, IN_UNIV, add_lzero] \\
     Q.PAT_X_ASSUM ‘g _ <> PosInf’ K_TAC (* useless *) \\
     rename1 ‘g N <= e’ \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC ‘SIGMA (\n. &n * prob p (A n)) (count (MAX (SUC n) N))’ \\
     reverse CONJ_TAC
     >- (FIRST_X_ASSUM MATCH_MP_TAC (* !z. (?n. z = _) ==> z <= y' *) \\
         Q.EXISTS_TAC ‘MAX (SUC n) N’ >> REWRITE_TAC []) \\
    ‘0 < MAX (SUC n) N’ by RW_TAC arith_ss [] \\
     Know ‘SIGMA (\n. &n * prob p (A n)) (count (MAX (SUC n) N)) =
           SIGMA (\n. f (SUC n)) (count (PRE (MAX (SUC n) N))) -
           &PRE (MAX (SUC n) N) * f (MAX (SUC n) N)’
     >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> Rewr' \\
     Know ‘SIGMA (\n. f (SUC n)) (count n) - e <=
           SIGMA (\n. f (SUC n)) (count (PRE (MAX (SUC n) N))) -
           &PRE (MAX (SUC n) N) * f (MAX (SUC n) N) <=>
           SIGMA (\n. f (SUC n)) (count n) <=
           SIGMA (\n. f (SUC n)) (count (PRE (MAX (SUC n) N))) -
           &PRE (MAX (SUC n) N) * f (MAX (SUC n) N) + e’
     >- (MATCH_MP_TAC sub_le_eq >> art []) >> Rewr' \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC ‘SIGMA (\n. f (SUC n)) (count (PRE (MAX (SUC n) N)))’ \\
     CONJ_TAC >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET >> rw [FINITE_COUNT] \\
                  MATCH_MP_TAC COUNT_MONO \\
                  MATCH_MP_TAC LESS_EQ_TRANS >> Q.EXISTS_TAC ‘PRE (SUC n)’ \\
                  reverse CONJ_TAC
                  >- (POP_ASSUM (ONCE_REWRITE_TAC o wrap o (MATCH_MP INV_PRE_LESS_EQ)) \\
                      RW_TAC arith_ss []) \\
                  RW_TAC arith_ss []) \\
     Know ‘SIGMA (\n. f (SUC n)) (count (PRE (MAX (SUC n) N))) -
           &PRE (MAX (SUC n) N) * f (MAX (SUC n) N) =
           SIGMA (\n. f (SUC n)) (count (PRE (MAX (SUC n) N))) + -
          (&PRE (MAX (SUC n) N) * f (MAX (SUC n) N))’
     >- (MATCH_MP_TAC extreal_sub_add >> DISJ2_TAC \\
         CONJ_TAC >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> rw []) \\
         MATCH_MP_TAC pos_not_neginf \\
         MATCH_MP_TAC le_mul >> art [] \\
         rw [extreal_of_num_def, extreal_le_eq]) >> Rewr' \\
     Know ‘SIGMA (\n. f (SUC n)) (count (PRE (MAX (SUC n) N))) +
           -(&PRE (MAX (SUC n) N) * f (MAX (SUC n) N)) + e =
           SIGMA (\n. f (SUC n)) (count (PRE (MAX (SUC n) N))) +
          (-(&PRE (MAX (SUC n) N) * f (MAX (SUC n) N)) + e)’
     >- (MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC add_assoc >> DISJ1_TAC >> art [] \\
         CONJ_TAC >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF >> rw []) \\
        ‘?r. f (MAX (SUC n) N) = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_ainv_def, extreal_mul_def, extreal_of_num_def, extreal_not_infty]) >> Rewr' \\
     MATCH_MP_TAC le_addr_imp \\
     Know ‘-(&PRE (MAX (SUC n) N) * f (MAX (SUC n) N)) + e =
           e + -(&PRE (MAX (SUC n) N) * f (MAX (SUC n) N))’
     >- (MATCH_MP_TAC add_comm >> DISJ1_TAC >> art [] \\
        ‘?r. f (MAX (SUC n) N) = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_ainv_def, extreal_mul_def, extreal_of_num_def, extreal_not_infty]) >> Rewr' \\
     Know ‘e + -(&PRE (MAX (SUC n) N) * f (MAX (SUC n) N)) =
           e - &PRE (MAX (SUC n) N) * f (MAX (SUC n) N)’
     >- (MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC extreal_sub_add >> DISJ1_TAC >> art [] \\
        ‘?r. f (MAX (SUC n) N) = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_ainv_def, extreal_mul_def, extreal_of_num_def, extreal_not_infty]) >> Rewr' \\
     Know ‘0 <= e - &PRE (MAX (SUC n) N) * f (MAX (SUC n) N) <=>
           &PRE (MAX (SUC n) N) * f (MAX (SUC n) N) <= e’
     >- (MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC sub_zero_le \\
        ‘?r. f (MAX (SUC n) N) = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_ainv_def, extreal_mul_def, extreal_of_num_def, extreal_not_infty]) >> Rewr' \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC ‘g (MAX (SUC n) N)’ \\
     CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC ‘g N’ >> art [] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> RW_TAC arith_ss [])
 (* final stage: inf (IMAGE (\n. g n) univ(:num)) = 0 *)
 >> Q.PAT_X_ASSUM ‘!N. 0 < N ==> &PRE N * f N <= g N’ K_TAC
 >> Q.PAT_X_ASSUM ‘!z. (?n. z = _) ==> z <= y'’       K_TAC
 >> Q.PAT_X_ASSUM ‘!m n. m <= n ==> g n <= g m’       K_TAC
 >> NTAC 3 (POP_ASSUM K_TAC) (* all about ‘e’ *)
 >> Q.UNABBREV_TAC ‘g’ >> FULL_SIMP_TAC std_ss []
 >> Q.ABBREV_TAC ‘fi = \n x. abs (X x) * indicator_fn (B n) x’
 >> ‘!n. (\x. abs (X x) * indicator_fn (B n) x) = fi n’ by METIS_TAC [] >> POP_ORW
 (* applying lebesgue_monotone_convergence_decreasing *)
 >> Q.ABBREV_TAC ‘h = \x. inf (IMAGE (\i. fi i x) UNIV)’
 >> ‘!i x. 0 <= fi i x’
       by (rw [Abbr ‘fi’] >> MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS])
 >> Know ‘inf (IMAGE (\n. pos_fn_integral p (fi n)) UNIV) = pos_fn_integral p h’
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC lebesgue_monotone_convergence_decreasing \\
     fs [prob_space_def, p_space_def, events_def] \\
     CONJ_TAC
     >- (rw [Abbr ‘fi’] \\
         HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR \\
         fs [prob_space_def, measure_space_def, real_random_variable, p_space_def, events_def] \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS \\
         Q.EXISTS_TAC ‘X’ >> rw []) \\
     CONJ_TAC
     >- (rw [Abbr ‘fi’, GSYM lt_infty] \\
         FULL_SIMP_TAC std_ss [real_random_variable_def] \\
        ‘?r. X x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         STRIP_ASSUME_TAC (Q.SPECL [‘B (i :num)’, ‘x’] indicator_fn_normal) \\
         rw [extreal_abs_def, extreal_mul_def, extreal_not_infty]) \\
     CONJ_TAC
     >- (rw [Abbr ‘fi’, lt_infty] \\
         MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘expectation p (abs o X)’ \\
         reverse CONJ_TAC >- art [GSYM lt_infty] \\
         Know ‘expectation p (abs o X) = pos_fn_integral p (abs o X)’
         >- (REWRITE_TAC [expectation_def] \\
             MATCH_MP_TAC integral_pos_fn >> fs [prob_space_def, abs_pos]) >> Rewr' \\
         MATCH_MP_TAC pos_fn_integral_mono >> rw []
         >- (MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS]) \\
         Cases_on ‘x IN B 0’ \\ (* 2 subgoals, same tactics *)
         rw [indicator_fn_def, mul_rone, le_refl, mul_rzero, abs_pos]) \\
     rw [ext_mono_decreasing_def, Abbr ‘fi’] \\
     MATCH_MP_TAC le_lmul_imp >> REWRITE_TAC [abs_pos] \\
     MATCH_MP_TAC INDICATOR_FN_MONO \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> Rewr'
 >> Suff ‘!x. x IN p_space p ==> h x = 0’
 >- (DISCH_TAC \\
     Know ‘pos_fn_integral p (\x. 0) = 0’
     >- (MATCH_MP_TAC pos_fn_integral_zero >> fs [prob_space_def]) \\
     DISCH_THEN (ONCE_REWRITE_TAC o wrap o SYM) \\
     MATCH_MP_TAC pos_fn_integral_cong \\
     fs [prob_space_def, p_space_def, le_refl])
 >> rw [Abbr ‘h’, inf_eq'] >- art []
 >> Q.PAT_X_ASSUM ‘!i x. 0 <= fi i x’ K_TAC
 >> Q.UNABBREV_TAC ‘fi’ >> fs []
 >> POP_ASSUM MATCH_MP_TAC
 >> FULL_SIMP_TAC std_ss [real_random_variable_def]
 >> ‘?r. X x = Normal r’ by METIS_TAC [extreal_cases]
 >> STRIP_ASSUME_TAC (Q.SPEC ‘abs r’ SIMP_REAL_ARCH)
 >> Q.EXISTS_TAC ‘SUC n’
 >> Suff ‘indicator_fn (B (SUC n)) x = 0’ >- rw [mul_rzero]
 >> rw [Abbr ‘B’, indicator_fn_def, extreal_abs_def, extreal_of_num_def, extreal_le_eq]
 >> ‘&n < (&SUC n) :real’ by rw []
 >> ‘&n < abs r’ by PROVE_TAC [REAL_LTE_TRANS]
 >> METIS_TAC [REAL_LET_ANTISYM]
QED

(* Theorem 3.2.1, Part II *)
Theorem expectation_converge :
    !p X. prob_space p /\ real_random_variable X p ==>
         (expectation p (abs o X) < PosInf <=>
          suminf (\n. prob p {x | x IN p_space p /\ &SUC n <= abs (X x)}) < PosInf)
Proof
    rpt STRIP_TAC
 >> Know ‘suminf (\n. prob p {x | x IN p_space p /\ &SUC n <= abs (X x)}) <=
          expectation p (abs o X) /\ expectation p (abs o X) <= 1 +
          suminf (\n. prob p {x | x IN p_space p /\ &SUC n <= abs (X x)})’
 >- (MATCH_MP_TAC expectation_bounds >> art [])
 >> STRIP_TAC
 >> EQ_TAC >> STRIP_TAC
 >- (MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘expectation p (abs o X)’ >> art [])
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC ‘1 + suminf (\n. prob p {x | x IN p_space p /\ &SUC n <= abs (X x)})’
 >> FULL_SIMP_TAC std_ss [GSYM lt_infty]
 >> Know ‘suminf (\n. prob p {x | x IN p_space p /\ &SUC n <= abs (X x)}) <> NegInf’
 >- (MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC ext_suminf_pos >> rw [] \\
     MATCH_MP_TAC PROB_POSITIVE >> art [] \\
     fs [prob_space_def, p_space_def, events_def, real_random_variable, le_abs_bounds] \\
    ‘{x | x IN m_space p /\ (X x <= -&SUC n \/ &SUC n <= X x)} =
         ({x | X x <= -&SUC n} INTER m_space p) UNION
         ({x | &SUC n <= X x} INTER m_space p)’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC MEASURE_SPACE_UNION >> art [] \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE])
 >> DISCH_TAC
 >> ‘?r. suminf (\n. prob p {x | x IN p_space p /\ &SUC n <= abs (X x)}) = Normal r’
       by METIS_TAC [extreal_cases]
 >> POP_ORW
 >> rw [extreal_of_num_def, extreal_add_def, extreal_not_infty]
QED

(* Theorem 3.2.1, Part II' *)
Theorem expectation_converge' :
    !p X. prob_space p /\ real_random_variable X p ==>
         (expectation p (abs o X) = PosInf <=>
          suminf (\n. prob p {x | x IN p_space p /\ &SUC n <= abs (X x)}) = PosInf)
Proof
    METIS_TAC [expectation_converge, lt_infty]
QED

(* Theorem 3.2.2 [2, p.47], probability-specific version of integral_distr *)
Theorem expectation_distribution :
    !p X f. prob_space p /\ random_variable X p Borel /\ f IN measurable Borel Borel ==>
           (expectation p (f o X) =
            integral (space Borel,subsets Borel,distribution p X) f) /\
           (integrable p (f o X) <=>
            integrable (space Borel,subsets Borel,distribution p X) f)
Proof
    rpt GEN_TAC
 >> simp [prob_space_def, random_variable_def, expectation_def, p_space_def, events_def,
          distribution_distr]
 >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘Borel’, ‘X’, ‘f’] (INST_TYPE [beta |-> “:extreal”] integral_distr))
 >> rw [SIGMA_ALGEBRA_BOREL]
QED

(* r.v.'s having indentical distributions have the same integrability *)
Theorem identical_distribution_integrable :
    !p X. prob_space p /\ (!n. random_variable (X n) p Borel) /\
          identical_distribution p X Borel UNIV /\ integrable p (X 0) ==>
          !(n :num). integrable p (X n)
Proof
    RW_TAC std_ss [identical_distribution_def, IN_UNIV]
 >> ‘X n IN Borel_measurable (m_space p,measurable_sets p)’
       by fs [random_variable_def, p_space_def, events_def]
 >> Know ‘(\x. x) IN measurable Borel Borel’
 >- (rw [IN_MEASURABLE, SIGMA_ALGEBRA_BOREL, IN_FUNSET, PREIMAGE_def] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> rw [SIGMA_ALGEBRA_BOREL] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_SPACE >> rw [SIGMA_ALGEBRA_BOREL])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘X (0 :num)’, ‘\x. x’] expectation_distribution)
 >> RW_TAC std_ss [o_DEF]
 >> MP_TAC (Q.SPECL [‘p’, ‘X (n :num)’, ‘\x. x’] expectation_distribution)
 >> RW_TAC std_ss [o_DEF]
 >> Suff ‘integrable (space Borel,subsets Borel,distribution p (X 0)) (\x. x) <=>
          integrable (space Borel,subsets Borel,distribution p (X n)) (\x. x)’
 >- METIS_TAC []
 (* applying integral_cong_measure *)
 >> ‘prob_space (space Borel,subsets Borel,distribution p (X 0)) /\
     prob_space (space Borel,subsets Borel,distribution p (X n))’
       by METIS_TAC [distribution_prob_space]
 >> METIS_TAC [integral_cong_measure, prob_space_def]
QED

(* r.v.'s having indentical distributions have the same expectation *)
Theorem identical_distribution_expectation :
    !p X. prob_space p /\ (!n. random_variable (X n) p Borel) /\
          identical_distribution p X Borel UNIV ==>
          !(n :num). expectation p (X n) = expectation p (X 0)
Proof
    RW_TAC std_ss [identical_distribution_def, IN_UNIV]
 >> Know ‘(\x. x) IN measurable Borel Borel’
 >- (rw [IN_MEASURABLE, SIGMA_ALGEBRA_BOREL, IN_FUNSET, PREIMAGE_def] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> rw [SIGMA_ALGEBRA_BOREL] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_SPACE >> rw [SIGMA_ALGEBRA_BOREL])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘X (0 :num)’, ‘\x. x’] expectation_distribution)
 >> RW_TAC std_ss [o_DEF]
 >> MP_TAC (Q.SPECL [‘p’, ‘X (n :num)’, ‘\x. x’] expectation_distribution)
 >> RW_TAC std_ss [o_DEF]
 >> ‘!n. X n = (\x. X n x)’ by METIS_TAC [ETA_THM] >> POP_ORW
 >> Suff ‘integral (space Borel,subsets Borel,distribution p (X 0)) (\x. x) =
          integral (space Borel,subsets Borel,distribution p (X n)) (\x. x)’
 >- rw []
 (* applying integral_cong_measure *)
 >> ‘prob_space (space Borel,subsets Borel,distribution p (X 0)) /\
     prob_space (space Borel,subsets Borel,distribution p (X n))’
       by METIS_TAC [distribution_prob_space]
 >> METIS_TAC [integral_cong_measure, prob_space_def, expectation_def]
QED

(* ========================================================================= *)
(*                 Probability Density Function Theory [11]                  *)
(* ========================================================================= *)

Theorem PDF_LE_POS :
    !p X. prob_space p /\ random_variable X p borel /\ distribution p X << lborel
          ==> !x. 0 <= PDF p X x
Proof
    rpt STRIP_TAC
 >> `measure_space (space borel, subsets borel, distribution p X)`
       by PROVE_TAC [distribution_prob_space, prob_space_def]
 >> ASSUME_TAC sigma_finite_lborel
 >> ASSUME_TAC measure_space_lborel
 >> MP_TAC (ISPECL [(* m *) ``lborel``,
                    (* v *) ``distribution (p :'a m_space) (X :'a -> real)``]
                   Radon_Nikodym')
 >> RW_TAC std_ss [m_space_lborel, sets_lborel, space_borel, IN_UNIV]
 >> fs [PDF_def, RN_deriv_def, m_space_def, measurable_sets_def,
        m_space_lborel, sets_lborel, space_borel]
 >> SELECT_ELIM_TAC >> METIS_TAC []
QED

Theorem EXPECTATION_PDF_1 : (* was: INTEGRAL_PDF_1 *)
    !p X. prob_space p /\ random_variable X p borel /\ distribution p X << lborel
          ==> (expectation lborel (PDF p X) = 1)
Proof
    rpt STRIP_TAC
 >> `prob_space (space borel, subsets borel, distribution p X)`
       by PROVE_TAC [distribution_prob_space]
 >> NTAC 2 (POP_ASSUM MP_TAC) >> KILL_TAC
 >> RW_TAC std_ss [prob_space_def, p_space_def, m_space_def, measure_def,
                   expectation_def]
 >> ASSUME_TAC sigma_finite_lborel
 >> ASSUME_TAC measure_space_lborel
 >> MP_TAC (ISPECL [(* m *) ``lborel``,
                    (* v *) ``distribution (p :'a m_space) (X :'a -> real)``]
                   Radon_Nikodym')
 >> RW_TAC std_ss [m_space_lborel, sets_lborel, m_space_def, measure_def,
                   space_borel, IN_UNIV]
 >> fs [PDF_def, RN_deriv_def, m_space_def, measurable_sets_def,
        m_space_lborel, sets_lborel, space_borel]
 >> SELECT_ELIM_TAC
 >> CONJ_TAC >- METIS_TAC []
 >> Q.X_GEN_TAC `g`
 >> RW_TAC std_ss [density_measure_def]
 >> POP_ASSUM (MP_TAC o Q.SPEC `space borel`)
 >> Know `space borel IN subsets borel`
 >- (`sigma_algebra borel` by PROVE_TAC [sigma_algebra_borel] \\
     PROVE_TAC [sigma_algebra_def, ALGEBRA_SPACE])
 >> RW_TAC std_ss []
 >> Know `integral lborel g = pos_fn_integral lborel g`
 >- (MATCH_MP_TAC integral_pos_fn >> art []) >> Rewr'
 >> Know `pos_fn_integral lborel g =
          pos_fn_integral lborel (\x. g x * indicator_fn (space borel) x)`
 >- (MATCH_MP_TAC pos_fn_integral_cong \\
     RW_TAC std_ss [m_space_lborel, indicator_fn_def, mul_rone, mul_rzero, le_refl])
 >> Rewr'
 >> POP_ORW
 >> rw [space_borel]
QED

(* ========================================================================= *)
(*                      Condition Probability Library                        *)
(* ========================================================================= *)

Theorem COND_PROB_ZERO :
    !p A B. prob_space p /\ A IN events p /\ B IN events p /\
           (prob p A = 0) /\ prob p B <> 0 ==> (cond_prob p A B = 0)
Proof
    RW_TAC std_ss [cond_prob_def, PROB_ZERO_INTER, zero_div]
QED

Theorem COND_PROB_ZERO_INTER :
    !p A B. prob_space p /\ A IN events p /\ B IN events p /\
           (prob p (A INTER B) = 0) /\ prob p B <> 0 ==> (cond_prob p A B = 0)
Proof
    RW_TAC std_ss [cond_prob_def, zero_div]
QED

Theorem COND_PROB_INCREASING :
    !p A B C. prob_space p /\ A IN events p /\ B IN events p /\ C IN events p /\
              prob p C <> 0 ==> cond_prob p (A INTER B) C <= cond_prob p A C
Proof
    RW_TAC std_ss [cond_prob_def, real_div]
 >> `(A INTER B INTER C) SUBSET (A INTER C)` by SET_TAC []
 >> `A INTER C IN events p` by METIS_TAC [EVENTS_INTER]
 >> `A INTER B INTER C IN events p` by METIS_TAC [EVENTS_INTER]
 >> `0 < prob p C` by METIS_TAC [le_lt, PROB_POSITIVE]
 >> MATCH_MP_TAC ldiv_le_imp
 >> ASM_SIMP_TAC std_ss [PROB_FINITE]
 >> MATCH_MP_TAC PROB_INCREASING >> art []
QED

Theorem COND_PROB_POS_IMP_PROB_NZ : (* was: POS_COND_PROB_IMP_POS_PROB *)
    !A B p. prob_space p /\ A IN events p /\ B IN events p /\
            0 < cond_prob p A B /\ prob p B <> 0 ==> prob p (A INTER B) <> 0
Proof
    RW_TAC std_ss []
 >> `0 < prob p B` by METIS_TAC [lt_le, PROB_POSITIVE]
 >> FULL_SIMP_TAC std_ss [cond_prob_def]
 >> CCONTR_TAC >> fs []
 >> `0 / prob p B = 0` by METIS_TAC [zero_div]
 >> METIS_TAC [lt_refl]
QED

Theorem COND_PROB_BOUNDS :
    !p A B. prob_space p /\ A IN events p /\ B IN events p /\
            prob p B <> 0 ==> 0 <= cond_prob p A B /\ cond_prob p A B <= 1
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> `0 < prob p B` by METIS_TAC [lt_le, PROB_POSITIVE]
 >> `prob p B <> 0` by METIS_TAC [lt_le]
 >> `prob p B <> PosInf /\ prob p B <> NegInf` by METIS_TAC [PROB_FINITE]
 >> `?r. prob p B = Normal r` by METIS_TAC [extreal_cases]
 >> `0 < r` by METIS_TAC [extreal_of_num_def, extreal_lt_eq]
 >> `A INTER B IN events p` by METIS_TAC [EVENTS_INTER]
 >> `0 <= prob p (A INTER B)` by METIS_TAC [PROB_POSITIVE]
 >> REWRITE_TAC [cond_prob_def]
 >> CONJ_TAC
 >- (`(prob p (A INTER B) = 0) \/ 0 < prob p (A INTER B)` by METIS_TAC [le_lt]
     >- (POP_ORW >> Suff `0 / prob p B = 0` >- rw [le_refl] \\
         MATCH_MP_TAC zero_div >> art []) \\
     MATCH_MP_TAC lt_imp_le >> art [] \\
     MATCH_MP_TAC lt_div >> art [])
 >> ASM_SIMP_TAC std_ss [GSYM le_ldiv, mul_lone]
 >> Q.PAT_X_ASSUM `prob p B = Normal r` (ONCE_REWRITE_TAC o wrap o SYM)
 >> MATCH_MP_TAC PROB_INCREASING
 >> ASM_SIMP_TAC std_ss [INTER_SUBSET]
QED

Theorem COND_PROB_FINITE : (* new *)
    !p A B. prob_space p /\ A IN events p /\ B IN events p /\
            prob p B <> 0 ==> cond_prob p A B <> PosInf /\ cond_prob p A B <> NegInf
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> `0 <= cond_prob p A B /\ cond_prob p A B <= 1` by METIS_TAC [COND_PROB_BOUNDS]
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC pos_not_neginf >> art [])
 >> REWRITE_TAC [lt_infty]
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC `1` >> art [num_not_infty, GSYM lt_infty]
QED

Theorem COND_PROB_ITSELF :
    !p B. prob_space p /\ B IN events p /\ prob p B <> 0 ==> (cond_prob p B B = 1)
Proof
    RW_TAC real_ss [cond_prob_def, INTER_IDEMPOT]
 >> `0 < prob p B` by METIS_TAC [le_lt, PROB_POSITIVE]
 >> MATCH_MP_TAC div_refl
 >> METIS_TAC [PROB_FINITE]
QED

Theorem COND_PROB_COMPL :
    !p A B. prob_space p /\ A IN events p /\ COMPL A IN events p /\
            B IN events p /\ prob p B <> 0 ==>
           (cond_prob p (COMPL A) B = 1 - cond_prob p A B)
Proof
    RW_TAC std_ss [cond_prob_def]
 >> `prob p B <> PosInf /\ prob p B <> NegInf` by METIS_TAC [PROB_FINITE]
 >> `prob p B < PosInf` by METIS_TAC [lt_infty]
 >> `0 < prob p B` by METIS_TAC [le_lt, PROB_POSITIVE]
 >> ASM_SIMP_TAC std_ss [ldiv_eq]
 >> `A INTER B IN events p` by METIS_TAC [EVENTS_INTER]
 >> `prob p (A INTER B) <> PosInf /\
     prob p (A INTER B) <> NegInf` by METIS_TAC [PROB_FINITE]
 >> Know `prob p (A INTER B) / prob p B <> PosInf /\
          prob p (A INTER B) / prob p B <> NegInf`
 >- (`?a. prob p (A INTER B) = Normal a` by METIS_TAC [extreal_cases] \\
     `?b. prob p B = Normal b` by METIS_TAC [extreal_cases] \\
     `b <> 0` by METIS_TAC [extreal_of_num_def, extreal_11] \\
     ASM_SIMP_TAC std_ss [extreal_div_eq, extreal_not_infty])
 >> STRIP_TAC
 >> ASM_SIMP_TAC std_ss [sub_rdistrib, num_not_infty, mul_lone]
 >> Know `prob p (A INTER B) / prob p B * prob p B = prob p (A INTER B)`
 >- (MATCH_MP_TAC EQ_SYM \\
    `?b. prob p B = Normal b` by METIS_TAC [extreal_cases] \\
    `b <> 0` by METIS_TAC [extreal_of_num_def, extreal_11] >> art [] \\
     MATCH_MP_TAC div_mul_refl >> art []) >> Rewr'
 >> ASM_SIMP_TAC std_ss [eq_sub_ladd]
 >> `prob p ((COMPL A) INTER B) + prob p (A INTER B) =
     prob p (((COMPL A) INTER B) UNION (A INTER B))`
       by (ONCE_REWRITE_TAC [EQ_SYM_EQ] >> MATCH_MP_TAC PROB_ADDITIVE
          >> RW_TAC std_ss [EVENTS_INTER, DISJOINT_DEF, EXTENSION]
          >> RW_TAC std_ss [NOT_IN_EMPTY, IN_COMPL, IN_INTER] >> METIS_TAC []) >> POP_ORW
 >> `(COMPL A INTER B UNION A INTER B) = B`
        by (SET_TAC [EXTENSION, IN_INTER, IN_UNION, IN_COMPL] >> METIS_TAC [])
 >> RW_TAC std_ss []
QED

Theorem COND_PROB_DIFF :
    !p A1 A2 B. prob_space p /\ A1 IN events p /\ A2 IN events p /\
                B IN events p /\ prob p B <> 0 ==>
               (cond_prob p (A1 DIFF A2) B =
                cond_prob p A1 B - cond_prob p (A1 INTER A2) B)
Proof
    RW_TAC std_ss [cond_prob_def]
 >> `(A1 DIFF A2) INTER B IN events p` by METIS_TAC [EVENTS_INTER, EVENTS_DIFF]
 >> `A1 INTER B IN events p` by METIS_TAC [EVENTS_INTER]
 >> `A1 INTER A2 INTER B IN events p` by METIS_TAC [EVENTS_INTER]
 >> `prob p B <> PosInf /\ prob p B <> NegInf` by METIS_TAC [PROB_FINITE]
 >> `prob p B < PosInf` by METIS_TAC [lt_infty]
 >> `0 < prob p B` by METIS_TAC [le_lt, PROB_POSITIVE]
 >> ASM_SIMP_TAC std_ss [ldiv_eq]
 >> `prob p (A1 INTER B) <> PosInf /\
     prob p (A1 INTER B) <> NegInf` by METIS_TAC [PROB_FINITE]
 >> `prob p (A1 INTER A2 INTER B) <> PosInf /\
     prob p (A1 INTER A2 INTER B) <> NegInf` by METIS_TAC [PROB_FINITE]
 >> Know `prob p (A1 INTER B) / prob p B <> PosInf /\
          prob p (A1 INTER B) / prob p B <> NegInf`
 >- (`?a. prob p (A1 INTER B) = Normal a` by METIS_TAC [extreal_cases] \\
     POP_ORW >> METIS_TAC [div_not_infty]) >> STRIP_TAC
 >> Know `prob p (A1 INTER A2 INTER B) / prob p B <> PosInf /\
          prob p (A1 INTER A2 INTER B) / prob p B <> NegInf`
 >- (`?a. prob p (A1 INTER A2 INTER B) = Normal a`
          by METIS_TAC [extreal_cases] >> POP_ORW \\
     METIS_TAC [div_not_infty]) >> STRIP_TAC
 >> ASM_SIMP_TAC std_ss [sub_rdistrib]
 >> Know `prob p (A1 INTER B) / prob p B * prob p B = prob p (A1 INTER B)`
 >- (MATCH_MP_TAC EQ_SYM \\
    `?b. prob p B = Normal b` by METIS_TAC [extreal_cases] \\
    `b <> 0` by METIS_TAC [extreal_of_num_def, extreal_11] >> art [] \\
     MATCH_MP_TAC div_mul_refl >> art []) >> Rewr'
 >> Know `prob p (A1 INTER A2 INTER B) / prob p B * prob p B =
          prob p (A1 INTER A2 INTER B)`
 >- (MATCH_MP_TAC EQ_SYM \\
    `?b. prob p B = Normal b` by METIS_TAC [extreal_cases] \\
    `b <> 0` by METIS_TAC [extreal_of_num_def, extreal_11] >> art [] \\
     MATCH_MP_TAC div_mul_refl >> art []) >> Rewr'
 >> ASM_SIMP_TAC std_ss [eq_sub_ladd]
 >> `prob p ((A1 DIFF A2) INTER B) + prob p (A1 INTER A2 INTER B) =
        prob p (((A1 DIFF A2) INTER B) UNION (A1 INTER A2 INTER B))`
        by (ONCE_REWRITE_TAC [EQ_SYM_EQ] >> MATCH_MP_TAC PROB_ADDITIVE
           >> RW_TAC std_ss [EVENTS_INTER, EVENTS_DIFF, DISJOINT_DEF, EXTENSION]
           >> RW_TAC std_ss [IN_DIFF, IN_INTER, NOT_IN_EMPTY] >> PROVE_TAC [])
 >> `((A1 DIFF A2) INTER B UNION A1 INTER A2 INTER B) = (A1 INTER B)`
        by (RW_TAC std_ss [EXTENSION, IN_INTER, IN_DIFF, IN_UNION] THEN PROVE_TAC [])
 >> RW_TAC std_ss []
QED

Theorem COND_PROB_MUL_RULE :
    !p A B. prob_space p /\ A IN events p /\ B IN events p /\ prob p B <> 0 ==>
           (prob p (A INTER B) = (prob p B) * (cond_prob p A B))
Proof
    RW_TAC std_ss []
 >> `prob p B <> PosInf /\ prob p B <> NegInf` by METIS_TAC [PROB_FINITE]
 >> `prob p B < PosInf` by METIS_TAC [lt_infty]
 >> `0 < prob p B` by METIS_TAC [le_lt, PROB_POSITIVE]
 >> ASM_SIMP_TAC std_ss [cond_prob_def, ldiv_eq, Once mul_comm]
 >> `?b. prob p B = Normal b` by METIS_TAC [extreal_cases]
 >> `b <> 0` by METIS_TAC [extreal_of_num_def, extreal_11] >> art []
 >> MATCH_MP_TAC div_mul_refl >> art []
QED

Theorem COND_PROB_MUL_EQ :
    !p A B. prob_space p /\ A IN events p /\ B IN events p /\
            prob p A <> 0 /\ prob p B <> 0 ==>
           (cond_prob p A B * prob p B = cond_prob p B A * prob p A)
Proof
    RW_TAC std_ss [cond_prob_def, Once INTER_COMM]
 >> `prob p A <> PosInf /\ prob p A <> NegInf` by METIS_TAC [PROB_FINITE]
 >> `prob p A < PosInf` by METIS_TAC [lt_infty]
 >> `0 < prob p A` by METIS_TAC [le_lt, PROB_POSITIVE]
 >> `prob p B <> PosInf /\ prob p B <> NegInf` by METIS_TAC [PROB_FINITE]
 >> `prob p B < PosInf` by METIS_TAC [lt_infty]
 >> `0 < prob p B` by METIS_TAC [le_lt, PROB_POSITIVE]
 >> Know `prob p (B INTER A) / prob p A * prob p A = prob p (B INTER A)`
 >- (MATCH_MP_TAC EQ_SYM \\
    `?a. prob p A = Normal a` by METIS_TAC [extreal_cases] \\
    `a <> 0` by METIS_TAC [extreal_of_num_def, extreal_11] >> art [] \\
     MATCH_MP_TAC div_mul_refl >> art []) >> Rewr'
 >> Know `prob p (B INTER A) / prob p B * prob p B = prob p (B INTER A)`
 >- (MATCH_MP_TAC EQ_SYM \\
    `?b. prob p B = Normal b` by METIS_TAC [extreal_cases] \\
    `b <> 0` by METIS_TAC [extreal_of_num_def, extreal_11] >> art [] \\
     MATCH_MP_TAC div_mul_refl >> art []) >> Rewr
QED

Theorem COND_PROB_UNION :
    !p A1 A2 B.
       prob_space p /\ A1 IN events p /\ A2 IN events p /\ B IN events p /\
       prob p B <> 0 ==>
      (cond_prob p (A1 UNION A2) B =
       (cond_prob p A1 B) + (cond_prob p A2 B) - (cond_prob p (A1 INTER A2) B))
Proof
    RW_TAC std_ss []
 >> `cond_prob p A1 B <> PosInf /\ cond_prob p A1 B <> NegInf /\
     cond_prob p A2 B <> PosInf /\ cond_prob p A2 B <> NegInf`
      by METIS_TAC [COND_PROB_FINITE]
 >> ASM_SIMP_TAC std_ss [Once add_comm]
 >> `A1 INTER A2 IN events p` by METIS_TAC [EVENTS_INTER]
 >> `cond_prob p (A1 INTER A2) B <> PosInf /\
     cond_prob p (A1 INTER A2) B <> NegInf` by METIS_TAC [COND_PROB_FINITE]
 >> Know `cond_prob p A2 B + cond_prob p A1 B - cond_prob p (A1 INTER A2) B =
          cond_prob p A2 B + (cond_prob p A1 B - cond_prob p (A1 INTER A2) B)`
 >- (`?a. cond_prob p A2 B = Normal a` by METIS_TAC [extreal_cases] >> POP_ORW \\
     `?b. cond_prob p A1 B = Normal b` by METIS_TAC [extreal_cases] >> POP_ORW \\
     `?c. cond_prob p (A1 INTER A2) B = Normal c` by METIS_TAC [extreal_cases] \\
     POP_ORW >> SIMP_TAC real_ss [extreal_add_def, extreal_sub_def, extreal_11] \\
     REAL_ARITH_TAC) >> Rewr'
 >> `cond_prob p A1 B - cond_prob p (A1 INTER A2) B = cond_prob p (A1 DIFF A2) B`
        by PROVE_TAC [COND_PROB_DIFF] >> POP_ORW
 >> `prob p B <> PosInf /\ prob p B <> NegInf` by METIS_TAC [PROB_FINITE]
 >> `prob p B < PosInf` by METIS_TAC [lt_infty]
 >> `0 < prob p B` by METIS_TAC [le_lt, PROB_POSITIVE]
 >> ASM_SIMP_TAC std_ss [cond_prob_def, ldiv_eq]
 >> Know `(prob p (A2 INTER B) / prob p B +
           prob p ((A1 DIFF A2) INTER B) / prob p B) * prob p B =
           prob p (A2 INTER B) / prob p B * prob p B +
           prob p ((A1 DIFF A2) INTER B) / prob p B * prob p B`
 >- (`?r. prob p B = Normal r` by METIS_TAC [extreal_cases] >> art [] \\
     MATCH_MP_TAC add_rdistrib_normal >> DISJ1_TAC \\
     POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) \\
     REWRITE_TAC [GSYM cond_prob_def] >> art [] \\
    `A1 DIFF A2 IN events p` by METIS_TAC [EVENTS_DIFF] \\
     METIS_TAC [COND_PROB_FINITE]) >> Rewr'
 >> Know `prob p (A2 INTER B) / prob p B * prob p B = prob p (A2 INTER B)`
 >- (MATCH_MP_TAC EQ_SYM \\
    `?b. prob p B = Normal b` by METIS_TAC [extreal_cases] \\
    `b <> 0` by METIS_TAC [extreal_of_num_def, extreal_11] >> art [] \\
     MATCH_MP_TAC div_mul_refl >> art []) >> Rewr'
 >> Know `prob p ((A1 DIFF A2) INTER B) / prob p B * prob p B =
          prob p ((A1 DIFF A2) INTER B)`
 >- (MATCH_MP_TAC EQ_SYM \\
    `?b. prob p B = Normal b` by METIS_TAC [extreal_cases] \\
    `b <> 0` by METIS_TAC [extreal_of_num_def, extreal_11] >> art [] \\
     MATCH_MP_TAC div_mul_refl >> art []) >> Rewr'
 >> `(A1 UNION A2) INTER B IN events p` by METIS_TAC [EVENTS_UNION, EVENTS_INTER]
 >> `A2 INTER B IN events p` by METIS_TAC [EVENTS_INTER]
 >> `(A1 DIFF A2) INTER B IN events p` by METIS_TAC [EVENTS_INTER, EVENTS_DIFF]
 >> `prob p (A2 INTER B) + prob p ((A1 DIFF A2) INTER B) =
       prob p ((A2 INTER B) UNION ((A1 DIFF A2) INTER B))`
       by (ONCE_REWRITE_TAC [EQ_SYM_EQ] >> MATCH_MP_TAC PROB_ADDITIVE
          >> RW_TAC std_ss [EVENTS_INTER, EVENTS_DIFF, DISJOINT_DEF, EXTENSION]
          >> RW_TAC std_ss [IN_INTER, IN_DIFF, NOT_IN_EMPTY] >> PROVE_TAC [])
 >> `(A2 INTER B UNION (A1 DIFF A2) INTER B) = ((A1 UNION A2) INTER B)`
        by (RW_TAC std_ss [EXTENSION, IN_INTER, IN_DIFF, IN_UNION] THEN PROVE_TAC [])
 >> RW_TAC std_ss []
QED

Theorem COND_PROB_FINITE_ADDITIVE :
    !p A B n s. prob_space p /\ B IN events p /\ A IN ((count n) -> events p) /\
                (s = BIGUNION (IMAGE A (count n))) /\ prob p B <> 0 /\
                (!a b. a <> b ==> DISJOINT (A a) (A b)) ==>
                (cond_prob p s B = SIGMA (\i. cond_prob p (A i) B) (count n))
Proof
    RW_TAC std_ss [IN_FUNSET, IN_COUNT]
 >> `0 <= prob p (B:'a -> bool)` by RW_TAC std_ss [PROB_POSITIVE]
 >> `BIGUNION (IMAGE A (count n)) IN events p` by METIS_TAC [EVENTS_BIGUNION, IN_FUNSET, IN_COUNT]
 >> `prob p B <> PosInf /\ prob p B <> NegInf` by METIS_TAC [PROB_FINITE]
 >> `prob p B < PosInf` by METIS_TAC [lt_infty]
 >> `0 < prob p B` by METIS_TAC [le_lt, PROB_POSITIVE]
 >> GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [cond_prob_def]
 >> ASM_SIMP_TAC std_ss [ldiv_eq, Once mul_comm]
 >> Know `prob p B * SIGMA (\i. cond_prob p (A i) B) (count n) =
          SIGMA (\i. prob p B * (\i. cond_prob p (A i) B) i) (count n)`
 >- (`?r. prob p B = Normal r` by METIS_TAC [extreal_cases] >> POP_ORW \\
     MATCH_MP_TAC EQ_SYM >> irule EXTREAL_SUM_IMAGE_CMUL \\
     REWRITE_TAC [FINITE_COUNT] >> DISJ1_TAC \\
     RW_TAC std_ss [IN_COUNT] >> METIS_TAC [COND_PROB_FINITE])
 >> BETA_TAC >> Rewr'
 >> REWRITE_TAC [cond_prob_def, Once mul_comm]
 >> Know `!i. prob p (A i INTER B) / prob p B * prob p B = prob p (A i INTER B)`
 >- (GEN_TAC >> MATCH_MP_TAC EQ_SYM \\
    `?b. prob p B = Normal b` by METIS_TAC [extreal_cases] \\
    `b <> 0` by METIS_TAC [extreal_of_num_def, extreal_11] >> art [] \\
     MATCH_MP_TAC div_mul_refl >> art []) >> Rewr'
 >> `SIGMA (\i. prob p (A i INTER B)) (count n) = SIGMA (prob p o (\i. A i INTER B)) (count n)`
        by METIS_TAC [] >> POP_ORW
 >> Know `BIGUNION (IMAGE A (count n)) INTER B = BIGUNION (IMAGE (\i. A i INTER B) (count n))`
 >- (RW_TAC set_ss [INTER_COMM, INTER_BIGUNION, Once EXTENSION, IN_IMAGE] \\
     EQ_TAC >> rpt STRIP_TAC >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       rename1 `s = A i` >> Q.EXISTS_TAC `B INTER (A i)` \\
       reverse CONJ_TAC >- (Q.EXISTS_TAC `i` >> art []) \\
       METIS_TAC [IN_INTER],
       (* goal 2 (of 3) *)
       fs [IN_INTER] >> Q.EXISTS_TAC `A i` >> art [] \\
       Q.EXISTS_TAC `i` >> art [],
       (* goal 3 (of 3) *)
       fs [IN_INTER] ]) >> Rewr'
 >> MATCH_MP_TAC PROB_FINITE_ADDITIVE
 >> RW_TAC std_ss [IN_FUNSET, IN_COUNT, FINITE_COUNT]
 >- METIS_TAC [EVENTS_INTER]
 >> MATCH_MP_TAC DISJOINT_RESTRICT_L
 >> PROVE_TAC []
QED

Theorem BAYES_RULE :
    !p A B. prob_space p /\ A IN events p /\ B IN events p /\
            prob p A <> 0 /\ prob p B <> 0 ==>
           (cond_prob p B A = (cond_prob p A B) * (prob p B) / (prob p A))
Proof
    RW_TAC std_ss []
 >> `prob p A <> PosInf /\ prob p A <> NegInf` by METIS_TAC [PROB_FINITE]
 >> `prob p A < PosInf` by METIS_TAC [lt_infty]
 >> `0 < prob p A` by METIS_TAC [le_lt, PROB_POSITIVE]
 >> `prob p B <> PosInf /\ prob p B <> NegInf` by METIS_TAC [PROB_FINITE]
 >> `prob p B < PosInf` by METIS_TAC [lt_infty]
 >> `0 < prob p B` by METIS_TAC [le_lt, PROB_POSITIVE]
 >> GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [cond_prob_def]
 >> ASM_SIMP_TAC std_ss [ldiv_eq]
 >> Know `cond_prob p A B * prob p B / prob p A * prob p A =
          cond_prob p A B * prob p B`
 >- (MATCH_MP_TAC EQ_SYM \\
    `?a. prob p A = Normal a` by METIS_TAC [extreal_cases] \\
    `a <> 0` by METIS_TAC [extreal_of_num_def, extreal_11] >> art [] \\
     MATCH_MP_TAC div_mul_refl >> art []) >> Rewr'
 >> REWRITE_TAC [cond_prob_def]
 >> Know `prob p (A INTER B) / prob p B * prob p B = prob p (A INTER B)`
 >- (MATCH_MP_TAC EQ_SYM \\
    `?b. prob p B = Normal b` by METIS_TAC [extreal_cases] \\
    `b <> 0` by METIS_TAC [extreal_of_num_def, extreal_11] >> art [] \\
     MATCH_MP_TAC div_mul_refl >> art []) >> Rewr'
 >> REWRITE_TAC [Once INTER_COMM]
QED

Theorem TOTAL_PROB_SIGMA :
    !p A B s. prob_space p /\ A IN events p /\ FINITE s /\
             (!x. x IN s ==> B x IN events p /\ prob p (B x) <> 0) /\
             (!a b. a IN s /\ b IN s /\ ~(a = b) ==> DISJOINT (B a) (B b)) /\
             (BIGUNION (IMAGE B s) = p_space p) ==>
             (prob p A = SIGMA (\i. (prob p (B i)) * (cond_prob p A (B i))) s)
Proof
    RW_TAC std_ss []
 >> `!x. x IN s ==> prob p (B x) <> PosInf /\
                    prob p (B x) <> NegInf` by METIS_TAC [PROB_FINITE]
 >> `!x. x IN s ==> prob p (B x) < PosInf` by METIS_TAC [lt_infty]
 >> `!x. x IN s ==> 0 < prob p (B x)` by METIS_TAC [le_lt, PROB_POSITIVE]
 >> Know `SIGMA (\i. prob p (B i) * cond_prob p A (B i)) (s:'b -> bool) =
          SIGMA (\i. prob p (A INTER (B i))) s`
 >- (irule EXTREAL_SUM_IMAGE_EQ \\
     STRONG_CONJ_TAC
     >- (RW_TAC std_ss [cond_prob_def, Once mul_comm] \\
         MATCH_MP_TAC EQ_SYM \\
        `?b. prob p (B x) = Normal b` by METIS_TAC [extreal_cases] \\
        `b <> 0` by METIS_TAC [extreal_of_num_def, extreal_11] >> art [] \\
         MATCH_MP_TAC div_mul_refl >> art []) \\
     RW_TAC std_ss [] >> DISJ1_TAC >> GEN_TAC >> DISCH_TAC \\
    `A INTER B x IN events p` by METIS_TAC [EVENTS_INTER] \\
     METIS_TAC [PROB_FINITE]) >> Rewr'
 >> MATCH_MP_TAC PROB_EXTREAL_SUM_IMAGE_FN
 >> RW_TAC std_ss [EVENTS_INTER, INTER_IDEMPOT]
QED

Theorem BAYES_RULE_GENERAL_SIGMA :
    !p A B s k. prob_space p /\ A IN events p /\ prob p A <> 0 /\ FINITE s /\
        (!x . x IN s ==> B x IN events p /\ prob p (B x) <> 0) /\
         k IN s /\ (!a b. a IN s /\ b IN s /\ ~(a = b) ==> DISJOINT (B a) (B b)) /\
        (BIGUNION (IMAGE B s) = p_space p) ==>
        (cond_prob p (B k) A = ((cond_prob p A (B k)) * prob p (B k)) /
                                (SIGMA (\i. (prob p (B i)) * (cond_prob p A (B i)))) s)
Proof
    RW_TAC std_ss [GSYM TOTAL_PROB_SIGMA]
 >> MATCH_MP_TAC BAYES_RULE
 >> RW_TAC std_ss []
QED

Theorem COND_PROB_ADDITIVE :
    !p A B s. prob_space p /\ FINITE s /\ B IN events p /\
             (!x. x IN s ==> A x IN events p) /\ prob p B <> 0 /\
             (!x y. x IN s /\ y IN s /\ x <> y ==> DISJOINT (A x) (A y)) /\
             (BIGUNION (IMAGE A s) = p_space p) ==>
             (SIGMA (\i. cond_prob p (A i) B) s = 1)
Proof
    RW_TAC std_ss []
 >> `prob p B <> PosInf /\ prob p B <> NegInf` by METIS_TAC [PROB_FINITE]
 >> `prob p B < PosInf` by METIS_TAC [lt_infty]
 >> `0 < prob p B` by METIS_TAC [le_lt, PROB_POSITIVE]
 >> `(SIGMA (\i. cond_prob p (A i) B) (s:'b -> bool) = 1) <=>
          (prob p B * SIGMA (\i. cond_prob p (A i) B) s = prob p B * 1)`
     by METIS_TAC [mul_lcancel] >> POP_ORW
 >> Know `prob p B * SIGMA (\i. cond_prob p (A i) B) (s:'b -> bool) =
          SIGMA (\i. prob p B * (\i. cond_prob p (A i) B) i) s`
 >- (`?r. prob p B = Normal r` by METIS_TAC [extreal_cases] >> POP_ORW \\
     MATCH_MP_TAC EQ_SYM >> irule EXTREAL_SUM_IMAGE_CMUL \\
     RW_TAC std_ss [COND_PROB_FINITE]) >> BETA_TAC >> Rewr'
 >> RW_TAC std_ss [cond_prob_def, Once mul_comm]
 >> Know `!i. prob p (A i INTER B) / prob p B * prob p B = prob p (A i INTER B)`
 >- (GEN_TAC >> MATCH_MP_TAC EQ_SYM \\
    `?b. prob p B = Normal b` by METIS_TAC [extreal_cases] \\
    `b <> 0` by METIS_TAC [extreal_of_num_def, extreal_11] >> art [] \\
     MATCH_MP_TAC div_mul_refl >> art []) >> Rewr'
 >> REWRITE_TAC [mul_rone, Once EQ_SYM_EQ, Once INTER_COMM]
 >> MATCH_MP_TAC PROB_EXTREAL_SUM_IMAGE_FN
 >> RW_TAC std_ss [INTER_IDEMPOT, EVENTS_INTER]
QED

Theorem COND_PROB_SWAP :
    !p A B C.
       prob_space p /\ A IN events p /\ B IN events p /\ C IN events p /\
       prob p (B INTER C) <> 0 /\ prob p (A INTER C) <> 0 ==>
      (cond_prob p A (B INTER C) * cond_prob p B C =
       cond_prob p B (A INTER C) * cond_prob p A C)
Proof
    RW_TAC std_ss []
 >> `B INTER C IN events p` by METIS_TAC [EVENTS_INTER]
 >> `A INTER B IN events p` by METIS_TAC [EVENTS_INTER]
 >> `A INTER C IN events p` by METIS_TAC [EVENTS_INTER]
 >> Know `prob p C <> 0`
 >- (CCONTR_TAC >> fs [] \\
    `0 < prob p (B INTER C)` by METIS_TAC [PROB_POSITIVE, le_lt] \\
     Know `prob p (B INTER C) <= prob p C`
     >- (MATCH_MP_TAC PROB_INCREASING >> ASM_SET_TAC [EVENTS_INTER]) \\
     DISCH_TAC >> METIS_TAC [lte_trans, lt_refl]) >> DISCH_TAC
 >> RW_TAC std_ss [cond_prob_def]
 >> `A INTER (B INTER C) = B INTER (A INTER C)`
       by METIS_TAC [GSYM INTER_ASSOC, INTER_COMM] >> POP_ORW
 >> `B INTER (A INTER C) IN events p` by METIS_TAC [EVENTS_INTER]
 >> `?a. prob p (B INTER (A INTER C)) = Normal a` by METIS_TAC [PROB_FINITE, extreal_cases]
 >> `?b. prob p (B INTER C) = Normal b` by METIS_TAC [PROB_FINITE, extreal_cases]
 >> `?c. prob p (A INTER C) = Normal c` by METIS_TAC [PROB_FINITE, extreal_cases]
 >> `?d. prob p C = Normal d` by METIS_TAC [PROB_FINITE, extreal_cases]
 >> `b <> 0 /\ c <> 0 /\ d <> 0` by METIS_TAC [extreal_of_num_def, extreal_11]
 >> ASM_SIMP_TAC std_ss [extreal_mul_def, extreal_div_eq, extreal_11]
 >> `!(a:real) b c d. a * b * (c * d) = a * (b * c) * d` by METIS_TAC [REAL_MUL_ASSOC]
 >> RW_TAC std_ss [real_div, REAL_MUL_LINV, REAL_MUL_LID, REAL_MUL_RID]
QED

Theorem PROB_INTER_SPLIT :
    !p A B C.
       prob_space p /\ A IN events p /\ B IN events p /\ C IN events p /\
       prob p (B INTER C) <> 0 ==>
      (prob p (A INTER B INTER C) =
       cond_prob p A (B INTER C) * cond_prob p B C * prob p C)
Proof
    RW_TAC std_ss []
 >> `B INTER C IN events p` by METIS_TAC [EVENTS_INTER]
 >> `A INTER B IN events p` by METIS_TAC [EVENTS_INTER]
 >> Know `prob p C <> 0`
 >- (CCONTR_TAC >> fs [] \\
    `0 < prob p (B INTER C)` by METIS_TAC [PROB_POSITIVE, le_lt] \\
     Know `prob p (B INTER C) <= prob p C`
     >- (MATCH_MP_TAC PROB_INCREASING >> ASM_SET_TAC [EVENTS_INTER]) \\
     DISCH_TAC >> METIS_TAC [lte_trans, lt_refl]) >> DISCH_TAC
 >> RW_TAC std_ss [cond_prob_def]
 >> `A INTER (B INTER C) = A INTER B INTER C` by SET_TAC [] >> POP_ORW
 >> `A INTER B INTER C IN events p` by METIS_TAC [EVENTS_INTER]
 >> `?a. prob p (A INTER B INTER C) = Normal a` by METIS_TAC [PROB_FINITE, extreal_cases]
 >> `?b. prob p (B INTER C) = Normal b` by METIS_TAC [PROB_FINITE, extreal_cases]
 >> `?c. prob p C = Normal c` by METIS_TAC [PROB_FINITE, extreal_cases]
 >> `b <> 0 /\ c <> 0` by METIS_TAC [extreal_of_num_def, extreal_11]
 >> ASM_SIMP_TAC std_ss [extreal_mul_def, extreal_div_eq, extreal_11]
 >> `!(a:real) b c d e. a * b * (c * d) * e = a * (b * c) * (d * e)` by METIS_TAC [REAL_MUL_ASSOC]
 >> RW_TAC std_ss [real_div, REAL_MUL_LINV, REAL_MUL_LID, REAL_MUL_RID]
QED

Theorem COND_PROB_INTER_SPLIT :
    !p A B C.
        prob_space p /\ A IN events p /\ B IN events p /\ C IN events p /\
        prob p (B INTER C) <> 0 ==>
        (cond_prob p (A INTER B) C = cond_prob p A (B INTER C) * cond_prob p B C)
Proof
    RW_TAC std_ss []
 >> `B INTER C IN events p` by METIS_TAC [EVENTS_INTER]
 >> Know `prob p C <> 0`
 >- (CCONTR_TAC >> fs [] \\
    `0 < prob p (B INTER C)` by METIS_TAC [PROB_POSITIVE, le_lt] \\
     Know `prob p (B INTER C) <= prob p C`
     >- (MATCH_MP_TAC PROB_INCREASING >> ASM_SET_TAC [EVENTS_INTER]) \\
     DISCH_TAC >> METIS_TAC [lte_trans, lt_refl]) >> DISCH_TAC
 >> RW_TAC std_ss [cond_prob_def]
 >> `A INTER (B INTER C) = A INTER B INTER C` by SET_TAC [] >> POP_ORW
 >> `A INTER B INTER C IN events p` by METIS_TAC [EVENTS_INTER]
 >> `?a. prob p (A INTER B INTER C) = Normal a` by METIS_TAC [PROB_FINITE, extreal_cases]
 >> `?b. prob p (B INTER C) = Normal b` by METIS_TAC [PROB_FINITE, extreal_cases]
 >> `?c. prob p C = Normal c` by METIS_TAC [PROB_FINITE, extreal_cases]
 >> `b <> 0 /\ c <> 0` by METIS_TAC [extreal_of_num_def, extreal_11]
 >> ASM_SIMP_TAC std_ss [extreal_mul_def, extreal_div_eq, extreal_11]
 >> `!(x:real) y z w. x * y * (z * w) = x * (y * z) * w`
        by METIS_TAC [REAL_MUL_ASSOC, REAL_MUL_COMM]
 >> RW_TAC std_ss [real_div, REAL_MUL_LINV, REAL_MUL_RID]
QED

(* tidy up theory exports, learnt from Magnus Myreen *)
val _ = List.app Theory.delete_binding
  ["convergence_mode_TY_DEF",
   "convergence_mode_case_def",
   "convergence_mode_size_def",
   "convergence_mode_11",
   "convergence_mode_Axiom",
   "convergence_mode_case_cong",
   "convergence_mode_case_eq",
   "convergence_mode_distinct",
   "convergence_mode_induction",
   "convergence_mode_nchotomy",
   "datatype_convergence_mode",
   "converge_def"];

val _ = export_theory ();

(* References:

  [1] Kolmogorov, A.N.: Foundations of the Theory of Probability (Grundbegriffe der
      Wahrscheinlichkeitsrechnung). Chelsea Publishing Company, New York. (1950).
  [2] Chung, K.L.: A Course in Probability Theory, Third Edition. Academic Press (2001).
  [3] Rosenthal, J.S.: A First Look at Rigorous Probability Theory (Second Editoin).
      World Scientific Publishing Company (2006).
  [4] Shiryaev, A.N.: Probability-1. Springer-Verlag New York (2016).
  [5] Shiryaev, A.N.: Probability-2. Springer-Verlag New York (2019).
  [6] Billingsley, P.: Probability and Measure (Third Edition). Wiley-Interscience (1995).
  [7] Hurd, J.: Formal verification of probabilistic algorithms.
      University of Cambridge (2003). UCAM-CL-TR-566
  [8] Coble, A.R.: Anonymity, information, and machine-assisted proof.
      University of Cambridge (2010). UCAM-CL-TR-785
  [9] Schilling, R.L.: Measures, Integrals and Martingales (Second Edition).
      Cambridge University Press (2017).
  [10] Mhamdi, T., Hasan, O., Tahar, S.: Formalization of Measure Theory and Lebesgue
       Integration for Probabilistic Analysis in HOL. ACM Trans. Embedded Comput. Syst.
       12, 1-23 (2013). DOI:10.1145/2406336.2406349
  [11] Qasim, M.: Formalization of Normal Random Variables, Concordia University (2016).
 *)
