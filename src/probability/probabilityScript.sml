(* ------------------------------------------------------------------------- *)
(* Probability Theory                                                        *)
(* Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar                         *)
(* HVG Group, Concordia University, Montreal                                 *)
(*                                                                           *)
(* Further enriched by Chun Tian <binghe.lisp@gmail.com> (2019 - 2023)       *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ------------------------------------------------------------------------- *)
(* Originally based on the work of Joe Hurd [7] and Aaron Coble [8]          *)
(* Cambridge University.                                                     *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open pairTheory combinTheory optionTheory prim_recTheory arithmeticTheory
     pred_setTheory pred_setLib topologyTheory hurdUtils;

open realTheory realLib iterateTheory seqTheory transcTheory real_sigmaTheory
     real_topologyTheory metricTheory;

open util_probTheory extrealTheory sigma_algebraTheory measureTheory
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

val _ = intLib.deprecate_int ();
val _ = ratLib.deprecate_rat ();

(* ------------------------------------------------------------------------- *)
(* Basic probability theory definitions.                                     *)
(* ------------------------------------------------------------------------- *)

Type p_space = “:'a m_space”
Type events  = “:'a set set”

val p_space_def = Define `p_space = m_space`;

val events_def = Define `events = measurable_sets`;

val prob_def = Define `prob = measure`;

val prob_space_def = Define
   `prob_space p <=> measure_space p /\ (measure p (m_space p) = 1)`;

val probably_def = Define
   `probably p e <=> e IN events p /\ (prob p e = 1)`;

val possibly_def = Define
   `possibly p e <=> e IN events p /\ prob p e <> 0`;

Definition random_variable_def :
    random_variable X p s <=> X IN measurable (p_space p, events p) s
End

(* `real_random_variable` is dedicated to Borel-measurable functions

    NOTE: ‘x IN p_space p’ was wrongly removed in k14 release.
 *)
Definition real_random_variable_def :
    real_random_variable X p <=>
         random_variable X p Borel /\
         !x. x IN p_space p ==> X x <> NegInf /\ X x <> PosInf
End

(* A (probability) distribution is a probability measure on `(p_space p,events p)`,

   cf. lebesgueTheory.distr_def, of type ``:'a m_space``
 *)
val distribution_def = Define (* was: pmf in [10] *)
   `distribution (p :'a p_space) X = (\s. prob p ((PREIMAGE X s) INTER p_space p))`;

(* c.f. [2, p.36], [4, p.206], [6, p.256], etc. *)
val distribution_function_def = Define
   `distribution_function p X = (\x. prob p ({w | X w <= x} INTER p_space p))`;

(* NOTE (fixes after k14): changed ‘i IN J’ to ‘j IN J’ *)
Definition identical_distribution_def :
    identical_distribution p X E (J :'index set) =
      !i j s. s IN subsets E /\ i IN J /\ j IN J ==>
             (distribution p (X i) s = distribution p (X j) s)
End

Definition joint_distribution_def :
    joint_distribution (p :'a p_space) X Y =
      (\a. prob p (PREIMAGE (\x. (X x,Y x)) a INTER p_space p))
End

Definition joint_distribution3_def :
    joint_distribution3 (p :'a p_space) X Y Z =
      (\a. prob p (PREIMAGE (\x. (X x,Y x,Z x)) a INTER p_space p))
End

val conditional_distribution_def = Define
   `conditional_distribution (p :'a p_space) X Y a b =
      joint_distribution p X Y (a CROSS b) / distribution p Y b`;

Definition expectation_def :
    expectation = lebesgue$integral
End

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

Theorem PROB_SPACE_NOT_EMPTY :
    !p. prob_space p ==> p_space p <> {}
Proof
    METIS_TAC [PROB_EMPTY, PROB_UNIV, ne_01]
QED

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

Theorem prob_normal:
  !p. prob_space p ==>
  !x. x IN events p ==> ?r. prob p x = Normal r /\ 0 <= r /\ r <= 1
Proof
  rpt strip_tac
  \\ imp_res_tac PROB_LE_1
  \\ imp_res_tac PROB_POSITIVE
  \\ qexists_tac`real (prob p x)`
  \\ dep_rewrite.DEP_REWRITE_TAC[normal_real]
  \\ conj_asm1_tac >- (
    rpt strip_tac \\ fs[le_infty] )
  \\ Cases_on`prob p x` \\ fs[]
  \\ metis_tac[extreal_of_num_def, extreal_le_eq]
QED

Theorem prob_on_finite_set:
  !p. FINITE (m_space p) /\ measurable_sets p = POW (m_space p) ==>
  (prob_space p <=>
   positive p /\ prob p (p_space p) = 1 /\ additive p)
Proof
  ntac 2 strip_tac
  \\ simp[prob_space_def]
  \\ simp[p_space_def, prob_def]
  \\ simp[measure_space_def]
  \\ Cases_on`positive p` \\ simp[]
  \\ Cases_on`measure p (m_space p) = 1` \\ simp[]
  \\ eq_tac \\ strip_tac
  >- (
    `measure_space p` by simp[measure_space_def]
    \\ imp_res_tac MEASURE_SPACE_EMPTY_MEASURABLE
    \\ imp_res_tac COUNTABLY_ADDITIVE_FINITE_ADDITIVE
    \\ fs[finite_additive_def, additive_def]
    \\ rpt strip_tac
    \\ first_x_assum(qspecl_then[`(0n =+ s) ((1 =+ t) (K {}))`,`2`]mp_tac)
    \\ simp[count_EQN]
    \\ simp[DECIDE``n < 2n <=> (n = 0) \/ (n = 1)``]
    \\ dsimp[combinTheory.APPLY_UPDATE_THM]
    \\ fs[events_def, DISJOINT_SYM, UNION_COMM]
    \\ ‘measure p s <> PosInf /\ measure p t <> PosInf’
    by (
      conj_tac \\ irule MEASURE_SPACE_FINITE_MEASURE
      \\ simp[]
      \\ simp[measure_space_def] )
    \\ dep_rewrite.DEP_REWRITE_TAC[extrealTheory.EXTREAL_SUM_IMAGE_INSERT]
    \\ simp[combinTheory.APPLY_UPDATE_THM]
    \\ dep_rewrite.DEP_REWRITE_TAC[DELETE_NON_ELEMENT |> SPEC_ALL |> EQ_IMP_RULE |> #1]
    \\ simp[]
    \\ dep_rewrite.DEP_REWRITE_TAC[extrealTheory.EXTREAL_SUM_IMAGE_INSERT]
    \\ simp[combinTheory.APPLY_UPDATE_THM]
    \\ simp[extrealTheory.EXTREAL_SUM_IMAGE_EMPTY]
    \\ reverse conj_asm1_tac
    >- ( simp[] \\ simp[extrealTheory.add_comm] )
    \\ disj1_tac
    \\ rw[]
    \\ dep_rewrite.DEP_REWRITE_TAC[MEASURE_EMPTY]
    \\ simp[measure_space_def] )
  \\ reverse conj_asm1_tac
  >- (
    imp_res_tac finite_additivity_sufficient_for_finite_spaces2
    \\ fs[measure_space_def] )
  \\ simp[sigma_algebraTheory.SIGMA_ALGEBRA]
  \\ conj_asm1_tac >- simp[sigma_algebraTheory.subset_class_POW]
  \\ simp[IN_POW]
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ simp[IN_POW, SUBSET_DEF]
  \\ metis_tac[]
QED

(* NOTE: This is one of the rare theorems having ‘prob_space p’ at the conclusion.
         It's most common uniform distribution over discrete sample space.
 *)
Theorem prob_space_on_finite_set :
    !p. FINITE (p_space p) /\ p_space p <> {} /\ events p = POW (p_space p) /\
        (!s. s IN events p ==> prob p s = &CARD s / &CARD (p_space p)) ==>
        prob_space p
Proof
    rw [p_space_def, events_def, prob_def]
 >> ‘CARD (m_space p) <> 0’ by rw [CARD_EQ_0]
 >> rw [prob_on_finite_set]
 >| [ (* goal 1 (of 3) *)
      rw [positive_def]
      >- (MATCH_MP_TAC zero_div >> rw [extreal_of_num_def]) \\
      qabbrev_tac ‘N = CARD (m_space p)’ \\
     ‘&N = Normal (&N)’ by rw [extreal_of_num_def] >> POP_ORW \\
      MATCH_MP_TAC le_div \\
      rw [extreal_lt_eq, extreal_of_num_def],
      (* goal 2 (of 3) *)
      rw [prob_def, p_space_def] \\
     ‘m_space p IN measurable_sets p’ by rw [IN_POW] \\
      rw [] \\
      MATCH_MP_TAC div_refl >> rw [extreal_of_num_def],
      (* goal 3 (of 3) *)
      rw [additive_def] \\
      Know ‘CARD (s UNION t) = CARD s + CARD t’
      >- (MATCH_MP_TAC CARD_UNION_DISJOINT >> art [] \\
          fs [IN_POW] \\
          CONJ_TAC \\ (* 2 subgoals, same tactics *)
          MATCH_MP_TAC FINITE_SUBSET >> Q.EXISTS_TAC ‘m_space p’ >> art []) >> Rewr' \\
      Know ‘&(CARD s + CARD t) = &CARD s + (&CARD t :extreal)’
      >- rw [extreal_of_num_def, extreal_add_def] >> Rewr' \\
      ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
      MATCH_MP_TAC div_add >> rw [extreal_of_num_def] ]
QED

(* ************************************************************************* *)

Theorem distribution_distr :
    distribution = distr
Proof
    rpt FUN_EQ_TAC >> qx_genl_tac [`p`, `X`, `s`]
 >> RW_TAC std_ss [distribution_def, distr_def, prob_def, p_space_def]
QED

Theorem distribution_GSPEC :
    !s. distribution p X s = prob p {x | x IN p_space p /\ X x IN s}
Proof
    rw [distribution_def, PREIMAGE_def]
 >> simp [PROB_GSPEC]
QED

(* alternative definition of ‘distribution_function’ *)
Theorem distribution_function :
    !p X t. distribution_function p X t = distribution p X {x | x <= t}
Proof
    rw [distribution_function_def, distribution_def, PREIMAGE_def]
QED

Theorem joint_distribution_alt :
   !p X Y. joint_distribution p X Y = distribution p (\x. (X x,Y x))
Proof
   rw [joint_distribution_def, distribution_def]
QED

(* See "stochastic_processTheory.finite_dimensional_distribution_def" for the joint
   distribution of a finite sequence of random variables.
 *)
Theorem joint_distribution3_alt :
   !p X Y Z. joint_distribution3 p X Y Z = distribution p (\x. (X x,Y x,Z x))
Proof
   rw [joint_distribution3_def, distribution_def]
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

(* Theorem 3.1.3 [2, p.36], cf. measure_space_distr

   NOTE: added ‘sigma_algebra s’ due to changes in ‘measurable’
 *)
Theorem distribution_prob_space : (* was: prob_space_distr *)
    !p X s. prob_space p /\ sigma_algebra s /\ random_variable X p s ==>
            prob_space (space s, subsets s, distribution p X)
Proof
    RW_TAC std_ss [random_variable_def, distribution_def, prob_space_def, measure_def, PSPACE,
                   measure_space_def, m_space_def, measurable_sets_def, IN_MEASURABLE,
                   SPACE, positive_def, PREIMAGE_EMPTY, INTER_EMPTY, PROB_EMPTY,
                   PROB_POSITIVE, space_def, subsets_def, countably_additive_def]
 >- (Q.PAT_X_ASSUM
       `!f. _ ==> measure p (BIGUNION (IMAGE f univ(:num))) = suminf (measure p o f)`
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
 >> METIS_TAC []
QED

(* `prob_space p` is added since it's not provided by random_variable_def

   NOTE: added ‘sigma_algebra s’ due to changes in ‘measurable’
 *)
Theorem uniform_distribution_prob_space :
    !X p s. prob_space p /\ FINITE (p_space p) /\
            FINITE (space s) /\ sigma_algebra s /\ random_variable X p s ==>
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

Theorem distribution_partition :
    !p X. prob_space p /\ (!x. x IN p_space p ==> {x} IN events p) /\
          FINITE (p_space p) /\ random_variable X p Borel ==>
         (SIGMA (\x. distribution p X {x}) (IMAGE X (p_space p)) = 1)
Proof
    RW_TAC std_ss []
 >> `random_variable X p (IMAGE X (p_space p), POW (IMAGE X (p_space p)))`
      by (RW_TAC std_ss [random_variable_def] \\
          RW_TAC std_ss [IN_MEASURABLE, IN_FUNSET, space_def, subsets_def,
                         IN_IMAGE,POW_SIGMA_ALGEBRA]
          >- METIS_TAC [] \\
          METIS_TAC [PROB_DISCRETE_EVENTS, INTER_SUBSET])
 >> `prob_space (space (IMAGE X (p_space p), POW (IMAGE X (p_space p))),
                 subsets (IMAGE X (p_space p), POW (IMAGE X (p_space p))),
                 distribution p X)`
     by (MATCH_MP_TAC distribution_prob_space >> art [] \\
         REWRITE_TAC [POW_SIGMA_ALGEBRA])
 >> (MP_TAC o Q.ISPEC `(space (IMAGE (X :'a->extreal) (p_space p), POW (IMAGE X (p_space p))),
                        subsets (IMAGE X (p_space p),POW (IMAGE X (p_space p))),
                        distribution p X)`) PROB_EXTREAL_SUM_IMAGE_SPACE
 >> RW_TAC std_ss []
 >> FULL_SIMP_TAC std_ss [space_def, subsets_def, p_space_def, events_def, m_space_def,
                          measurable_sets_def, prob_def, measure_def]
 >> `FINITE (IMAGE X (m_space p))` by METIS_TAC [IMAGE_FINITE]
 >> `(!x. x IN IMAGE X (m_space p) ==> {x} IN POW (IMAGE X (m_space p)))`
     by RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_IMAGE, IN_SING]
 >> METIS_TAC []
QED

Theorem distribution_space_eq_1 : (* was: lemma1 (normal_rvScript.sml) *)
    !p X. prob_space p ==> (distribution p X (IMAGE X (p_space p)) = 1)
Proof
    RW_TAC std_ss [prob_space_def, p_space_def]
 >> SIMP_TAC std_ss [distribution_def]
 >> SIMP_TAC std_ss [IMAGE_DEF, PREIMAGE_def, INTER_DEF, GSPECIFICATION]
 >> REWRITE_TAC [prob_def, p_space_def]
 >> REWRITE_TAC [SET_RULE ``{x | (?x''. (X x = X x'') /\ x'' IN s) /\ x IN s} = s``]
 >> ASM_REWRITE_TAC []
QED

(* NOTE: added ‘sigma_algebra s’ due to changes in ‘measurable’ (‘random_variable’) *)
Theorem distribution_lebesgue_thm1 :
   !X p s A. prob_space p /\ sigma_algebra s /\
             random_variable X p s /\ A IN subsets s ==>
      (distribution p X A = integral p (indicator_fn (PREIMAGE X A INTER p_space p)))
Proof
   RW_TAC std_ss [random_variable_def, prob_space_def, distribution_def, events_def,
                  IN_MEASURABLE, p_space_def, prob_def, subsets_def, space_def,
                  GSYM integral_indicator]
QED

(* NOTE: added ‘sigma_algebra s’ due to changes in ‘measurable’ (‘random_variable’) *)
Theorem distribution_lebesgue_thm2 :
    !X p s A. prob_space p /\ sigma_algebra s /\
              random_variable X p s /\ A IN subsets s ==>
      (distribution p X A = integral (space s, subsets s, distribution p X) (indicator_fn A))
Proof
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
                          prob_def, p_space_def]
QED

(* ************************************************************************* *)

(* |- !X p.
         real_random_variable X p <=>
         prob_space p /\ X IN measurable (p_space p,events p) Borel /\
         !x. x IN p_space p ==> X x <> NegInf /\ X x <> PosInf *)
Theorem real_random_variable =
       (REWRITE_RULE [random_variable_def] real_random_variable_def)

Theorem real_random_variable_zero :
    !p. prob_space p ==> real_random_variable (\x. 0) p
Proof
    RW_TAC std_ss [prob_space_def, real_random_variable_def,
                   random_variable_def, p_space_def, events_def, num_not_infty]
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST'
 >> FULL_SIMP_TAC std_ss [measure_space_def]
QED

Theorem real_random_variable_const :
    !p m. prob_space p /\ m <> PosInf /\ m <> NegInf ==>
          real_random_variable (\x. m) p
Proof
    RW_TAC std_ss [real_random_variable, p_space_def, events_def]
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST'
 >> FULL_SIMP_TAC std_ss [prob_space_def, measure_space_def]
QED

Theorem real_random_variable_add :
    !p X Y. prob_space p /\ real_random_variable X p /\
            real_random_variable Y p ==> real_random_variable (\x. X x + Y x) p
Proof
    RW_TAC std_ss [prob_space_def, real_random_variable_def,
                   random_variable_def, p_space_def, events_def]
 >| [ (* goal 1 (of 3) *)
      MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD \\
      qexistsl_tac [`X`, `Y`] >> fs [measure_space_def, space_def],
      (* goal 2 (of 3) *)
     `?a. X x = Normal a` by METIS_TAC [extreal_cases] \\
     `?b. Y x = Normal b` by METIS_TAC [extreal_cases] \\
      rw [extreal_not_infty, extreal_add_def],
      (* goal 3 (of 3) *)
     `?a. X x = Normal a` by METIS_TAC [extreal_cases] \\
     `?b. Y x = Normal b` by METIS_TAC [extreal_cases] \\
      rw [extreal_not_infty, extreal_add_def] ]
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

Theorem real_random_variable_ainv :
    !p X. prob_space p /\ real_random_variable X p ==> real_random_variable (\x. -X x) p
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘\x. 0’, ‘X’] real_random_variable_sub)
 >> ‘real_random_variable (\x. 0) p’ by PROVE_TAC [real_random_variable_zero]
 >> RW_TAC std_ss [sub_lzero]
QED

Theorem real_random_variable_cmul :
    !p X r. prob_space p /\ real_random_variable X p ==>
            real_random_variable (\x. Normal r * X x) p
Proof
    rpt GEN_TAC
 >> simp [real_random_variable, prob_space_def, p_space_def, events_def]
 >> STRIP_TAC
 >> CONJ_TAC (* Borel_measurable *)
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL \\
     qexistsl_tac [‘X’, ‘r’] >> rw [] \\
     FULL_SIMP_TAC std_ss [measure_space_def])
 >> Q.X_GEN_TAC ‘x’
 >> DISCH_TAC
 >> ‘?z. X x = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> rw [extreal_mul_def]
QED

Theorem real_random_variable_cdiv :
    !p X c. prob_space p /\ real_random_variable X p /\ c <> 0 ==>
            real_random_variable (\x. X x / Normal c) p
Proof
    rw [extreal_div_def, extreal_inv_def, Once mul_comm]
 >> MATCH_MP_TAC real_random_variable_cmul >> art []
QED

Theorem real_random_variable_sum :
    !p X (J :'index set). prob_space p /\ FINITE J /\
         (!i. i IN J ==> real_random_variable (X i) p) ==>
          real_random_variable (\x. SIGMA (\n. X n x) J) p
Proof
    RW_TAC std_ss [real_random_variable]
 >| [ (* goal 1 (of 3) *)
      MATCH_MP_TAC (INST_TYPE [“:'b” |-> “:'index”] IN_MEASURABLE_BOREL_SUM) \\
      qexistsl_tac [‘X’, ‘J’] \\
     ‘sigma_algebra (p_space p,events p)’
        by METIS_TAC [prob_space_def, measure_space_def, p_space_def, events_def] \\
      rw [],
      (* goal 2 (of 3) *)
      MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
      RW_TAC std_ss [],
      (* goal 3 (of 3) *)
      MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
      RW_TAC std_ss [] ]
QED

(* NOTE: added ‘prob_space p’ due to changes of ‘measurable’ *)
Theorem real_random_variable_fn_plus :
    !p X. prob_space p /\ real_random_variable X p ==>
          real_random_variable (fn_plus X) p
Proof
    rpt STRIP_TAC
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
 >> fs [real_random_variable, p_space_def, events_def]
 >> CONJ_TAC
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_FN_PLUS >> art [])
 >> NTAC 3 STRIP_TAC
 >- (MATCH_MP_TAC pos_not_neginf >> rw [FN_PLUS_POS])
 >> MATCH_MP_TAC FN_PLUS_NOT_INFTY >> rw []
QED

(* NOTE: added ‘prob_space p’ due to changes of ‘measurable’ *)
Theorem real_random_variable_fn_minus :
    !p X. prob_space p /\ real_random_variable X p ==>
          real_random_variable (fn_minus X) p
Proof
    rpt STRIP_TAC
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
 >> fs [real_random_variable, p_space_def, events_def]
 >> CONJ_TAC
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_FN_MINUS >> art [])
 >> NTAC 3 STRIP_TAC
 >- (MATCH_MP_TAC pos_not_neginf >> rw [FN_MINUS_POS])
 >> MATCH_MP_TAC FN_MINUS_NOT_INFTY >> rw []
QED

Theorem real_random_variable_mul_indicator :
    !p E X. prob_space p /\ E IN events p /\ real_random_variable X p ==>
            real_random_variable (\x. X x * indicator_fn E x) p
Proof
    RW_TAC std_ss [real_random_variable]
 >- (HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR \\
     fs [prob_space_def, measure_space_def, p_space_def, events_def])
 >> ‘?r. 0 <= r /\ r <= 1 /\ indicator_fn E x = Normal r’
        by METIS_TAC [indicator_fn_normal] >> POP_ORW
 >> ONCE_REWRITE_TAC [mul_comm]
 >> METIS_TAC [mul_not_infty]
QED

Theorem random_variable_cong :
    !p X Y A. (!x. x IN p_space p ==> X x = Y x) ==>
              (random_variable X p A <=> random_variable Y p A)
Proof
    rw [random_variable_def]
 >> EQ_TAC >> rw []
 >| [ (* goal 1 (of 2) *)
      fs [p_space_def, events_def, IN_MEASURABLE, IN_FUNSET, PREIMAGE_def] \\
      CONJ_TAC >- METIS_TAC [] \\
      rpt STRIP_TAC \\
      Suff ‘{x | Y x IN s} INTER m_space p =
            {x | X x IN s} INTER m_space p’ >- METIS_TAC [] \\
      rw [Once EXTENSION] >> METIS_TAC [],
      (* goal 2 (of 2) *)
      fs [p_space_def, events_def, IN_MEASURABLE, IN_FUNSET, PREIMAGE_def] \\
      rpt STRIP_TAC \\
      Suff ‘{x | X x IN s} INTER m_space p =
            {x | Y x IN s} INTER m_space p’ >- METIS_TAC [] \\
      rw [Once EXTENSION] >> METIS_TAC [] ]
QED

Theorem real_random_variable_cong :
    !p X Y. (!x. x IN p_space p ==> X x = Y x) ==>
            (real_random_variable X p <=> real_random_variable Y p)
Proof
    rw [real_random_variable]
 >> EQ_TAC >> rw []
 >| [ (* goal 1 (of 2) *)
      fs [p_space_def, events_def] \\
      MATCH_MP_TAC IN_MEASURABLE_BOREL_EQ \\
      Q.EXISTS_TAC ‘X’ >> rw [],
      (* goal 2 (of 2) *)
      fs [p_space_def, events_def] \\
      MATCH_MP_TAC IN_MEASURABLE_BOREL_EQ \\
      Q.EXISTS_TAC ‘Y’ >> rw [] ]
QED

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

(* NOTE: this is the last theorem in HVG's "probability_hvgScript.sml" *)
Theorem distribution_x_eq_1_imp_distribution_y_eq_0 :
    !X p x. prob_space p /\
            random_variable X p (IMAGE X (p_space p),POW (IMAGE X (p_space p))) /\
           (distribution p X {x} = 1)
        ==> !y. y <> x ==> (distribution p X {y} = 0)
Proof
    rpt STRIP_TAC
 >> (MP_TAC o Q.SPECL [`p`, `X`, `(IMAGE X (p_space p),POW (IMAGE X (p_space p)))`])
        distribution_prob_space
 >> RW_TAC std_ss [space_def, subsets_def, POW_SIGMA_ALGEBRA]
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
 >> FULL_SIMP_TAC std_ss [random_variable_def]
QED

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
 >> Know `prob_space p1`
 >- (Q.UNABBREV_TAC ‘p1’ \\
     Q.ABBREV_TAC ‘s = (IMAGE X (p_space p),POW (IMAGE X (p_space p)))’ \\
    ‘(IMAGE X (p_space p),POW (IMAGE X (p_space p)),distribution p X) =
     (space s,subsets s,distribution p X)’ by rw [Abbr ‘s’] >> POP_ORW \\
     MATCH_MP_TAC distribution_prob_space \\
     rw [POW_SIGMA_ALGEBRA, Abbr ‘s’])
 >> DISCH_TAC
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
              (!x. f x <> PosInf /\ f x <> NegInf) ==>
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
 >> Know `(!x. x IN s1 CROSS s2 ==>
               NegInf <> joint_distribution p X Y {x} * f (FST x)) \/
          (!x. x IN s1 CROSS s2 ==>
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
Theorem integrable_absolute_moments :
    !p X n. prob_space p /\ real_random_variable X p /\
            integrable p (\x. (abs (X x)) pow n) ==>
            !m. m <= n ==> integrable p (\x. (abs (X x)) pow m)
Proof
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
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS >> Q.EXISTS_TAC `X` \\
     ASM_SIMP_TAC std_ss [])
 >> Know `abs (abs (X x) pow m) = abs (X x) pow m`
 >- (REWRITE_TAC [abs_refl] \\
     MATCH_MP_TAC pow_pos_le >> REWRITE_TAC [abs_pos]) >> Rewr'
 >> MATCH_MP_TAC abs_pow_le_mono >> art []
QED

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
    !p X. prob_space p /\ real_random_variable X p /\
          integrable p (\x. X x pow 2) ==>
          variance p X = expectation p (\x. X x pow 2) - (expectation p X) pow 2
Proof
    rpt STRIP_TAC
 >> IMP_RES_TAC integrable_from_square
 >> REWRITE_TAC [variance_def, central_moment_def, moment_def, expectation_def]
 >> Q.ABBREV_TAC `EX = integral p X`
 >> fs [prob_space_def, real_random_variable_def, p_space_def]
 >> `?r. EX = Normal r` by PROVE_TAC [integrable_normal_integral]
 >> Know `!x. x IN m_space p ==> (X x - EX) pow 2 = (X x + (-EX)) pow 2`
 >- (rpt STRIP_TAC \\
     Suff ‘X x - EX = X x + (-EX)’ >- rw [] \\
     MATCH_MP_TAC extreal_sub_add >> DISJ1_TAC \\
     PROVE_TAC [extreal_not_infty])
 >> DISCH_TAC
 >> Know ‘integral p (\x. (X x - EX) pow 2) =
          integral p (\x. (X x + -EX) pow 2)’
 >- (MATCH_MP_TAC integral_cong >> rw []) >> Rewr'
 >> POP_ASSUM K_TAC
 >> Know `!x. x IN m_space p ==>
             (X x + -EX) pow 2 = (X x) pow 2 + (-EX) pow 2 + 2 * (X x) * (-EX)`
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC add_pow2 >> simp [extreal_ainv_def, extreal_not_infty])
 >> DISCH_TAC
 >> Know ‘integral p (\x. (X x + -EX) pow 2) =
          integral p (\x. X x pow 2 + -EX pow 2 + 2 * X x * -EX)’
 >- (MATCH_MP_TAC integral_cong >> rw []) >> Rewr'
 >> POP_ASSUM K_TAC
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
 >- (MATCH_MP_TAC integral_add \\
     simp [pow_2, extreal_mul_def, extreal_not_infty] \\
     MATCH_MP_TAC integrable_const >> art [extreal_of_num_def, lt_infty])
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
 >> Q.PAT_X_ASSUM `EX = Normal r` K_TAC
 >> ASM_REWRITE_TAC [mul_rone, GSYM pow_2, GSYM mul_assoc]
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
 >> `?r. integral p (\x. (X x) pow 2) = Normal r`
       by PROVE_TAC [integrable_normal_integral]
 >> POP_ORW >> REWRITE_TAC [extreal_not_infty]
QED

(* A corollary: Var(X) is always less or equal than E[X^2] *)
Theorem variance_le :
    !p X. prob_space p /\ real_random_variable X p /\ integrable p (\x. X x pow 2) ==>
          variance p X <= expectation p (\x. X x pow 2)
Proof
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
 >> REWRITE_TAC [le_pow2]
QED

(* NOTE: this definition is new, later we shall prove that it's equivalence with
         finite variance or finite second moment at `a = 0` *)
val finite_second_moments_def = Define
   `finite_second_moments p X = ?a. second_moment p X a < PosInf`;

val finite_variance_imp_finite_second_moments = Q.prove (
   `!p X. variance p X < PosInf ==> finite_second_moments p X`,
    RW_TAC std_ss [finite_second_moments_def, variance_def, central_moment_def,
                   second_moment_def]
 >> Q.EXISTS_TAC `expectation p X` >> art []);

(* TODO: extend `Normal c` to all extreals (not possible for integral_cmul) *)
Theorem expectation_cmul :
    !p X c. prob_space p /\ integrable p X ==>
            expectation p (\x. Normal c * X x) = Normal c * expectation p X
Proof
    rw [prob_space_def, expectation_def]
 >> MATCH_MP_TAC integral_cmul >> art []
QED

Theorem expectation_cdiv :
    !p X c. prob_space p /\ integrable p X /\ c <> 0 ==>
            expectation p (\x. X x / Normal c) = expectation p X / Normal c
Proof
    rw [extreal_div_def, extreal_inv_def]
 >> ONCE_REWRITE_TAC [mul_comm]
 >> MATCH_MP_TAC expectation_cmul >> art []
QED

Theorem expectation_pos :
    !p X. prob_space p /\ (!x. x IN p_space p ==> 0 <= X x) ==>
          0 <= expectation p X
Proof
    rw [prob_space_def, p_space_def, expectation_def]
 >> MATCH_MP_TAC integral_pos >> rw []
QED

Theorem expectation_posinf[local] :
    !p. prob_space p ==> expectation p (\x. PosInf) = PosInf
Proof
    RW_TAC std_ss [prob_space_def, p_space_def, expectation_def]
 >> MATCH_MP_TAC integral_posinf >> art [lt_01]
QED

Theorem expectation_neginf[local] :
    !p. prob_space p ==> expectation p (\x. NegInf) = NegInf
Proof
    RW_TAC std_ss [prob_space_def, p_space_def, expectation_def]
 >> MATCH_MP_TAC integral_neginf >> art [lt_01]
QED

(* NOTE: the type of ‘c’ has changed from “:real” to “:extreal” *)
Theorem expectation_const :
    !p c. prob_space p ==> expectation p (\x. c) = c
Proof
    rpt STRIP_TAC
 >> Cases_on ‘c’
 >| [ (* goal 1 (of 3) *)
      MATCH_MP_TAC expectation_neginf >> art [],
      (* goal 2 (of 3) *)
      MATCH_MP_TAC expectation_posinf >> art [],
      (* goal 3 (of 3) *)
      MP_TAC (Q.SPECL [`p`, `r`] integral_const) \\
     `1 < PosInf` by PROVE_TAC [lt_infty, extreal_of_num_def] \\
      fs [prob_space_def, p_space_def, expectation_def, mul_rone] ]
QED

(* |- !p. prob_space p ==> expectation p (\x. 0) = 0 *)
Theorem expectation_zero =
    Q.GEN ‘p’ (Q.SPECL [‘p’, ‘0’] expectation_const)

Theorem variance_const :
    !p c. prob_space p ==> variance p (\x. Normal c) = 0
Proof
    rpt STRIP_TAC
 >> rw [variance_alt, expectation_const, extreal_sub_def]
 >> rw [extreal_pow_def, expectation_zero]
QED

Theorem expectation_sum :
    !p X J.
        FINITE J /\ prob_space p /\ (!i. i IN J ==> integrable p (X i)) /\
       (!i. i IN J ==> real_random_variable (X i) p) ==>
        expectation p (\x. SIGMA (\i. X i x) J) = SIGMA (\i. expectation p (X i)) J
Proof
    RW_TAC std_ss [expectation_def, real_random_variable_def, prob_space_def,
                   p_space_def]
 >> MATCH_MP_TAC integral_sum >> rw []
QED

(* |- !p. prob_space p ==> variance p (\x. 0) = 0 *)
Theorem variance_zero =
        variance_const |> Q.SPECL [‘p’, ‘0’]
                       |> REWRITE_RULE [GSYM extreal_of_num_def]
                       |> Q.GEN ‘p’

Theorem expectation_cong :
    !p f g. prob_space p /\ (!x. x IN p_space p ==> f x = g x) ==>
            expectation p f = expectation p g
Proof
    rw [prob_space_def, p_space_def, expectation_def]
 >> MATCH_MP_TAC integral_cong >> art []
QED

Theorem variance_cong :
    !p f g. prob_space p /\ (!x. x IN p_space p ==> f x = g x) ==>
            variance p f = variance p g
Proof
    RW_TAC std_ss [variance_alt]
 >> MATCH_MP_TAC expectation_cong
 >> RW_TAC std_ss []
 >> Suff ‘expectation p f = expectation p g’ >- rw []
 >> MATCH_MP_TAC expectation_cong
 >> RW_TAC std_ss []
QED

(* Deep lemma: all second moments are finite iff one of them is finite *)
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
 >- (Suff `!x. x IN p_space p ==> (X x - a) pow 2 = PosInf`
     >- (DISCH_TAC \\
         Q.PAT_X_ASSUM ‘expectation p (\x. (X x - a) pow 2) < PosInf’ MP_TAC \\
         Know ‘expectation p (\x. (X x - a) pow 2) =
               expectation p (\x. PosInf)’
         >- (MATCH_MP_TAC expectation_cong >> simp []) \\
         simp [expectation_const] \\
         METIS_TAC [lt_infty]) \\
     rpt STRIP_TAC \\
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
       MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB' \\
       qexistsl_tac [`X`, `\x. Normal c`] \\
       ASM_SIMP_TAC std_ss [] \\
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
     >- (GEN_TAC >> DISCH_TAC \\
        `?r. X x = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
         REWRITE_TAC [extreal_sub_def, extreal_not_infty]) \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB' \\
     Q.EXISTS_TAC `X` >> Q.EXISTS_TAC `\x. Normal c` \\
     ASM_SIMP_TAC std_ss [] \\
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
 >> Know `!x. x IN m_space p ==>
             (X x - Normal r) pow 2 = (\x. (X x - Normal c) pow 2) x +
                                      (\x. Normal (2 * (c - r)) * (X x) +
                                           Normal (r pow 2 - c pow 2)) x`
 >- (GEN_TAC >> BETA_TAC >> STRIP_TAC \\
    `?y. X x = Normal y` by PROVE_TAC [extreal_cases] >> POP_ORW \\
     SIMP_TAC real_ss [sub_pow2, extreal_not_infty, pow_2] \\
     SIMP_TAC real_ss [extreal_mul_def, extreal_add_def, extreal_sub_def, extreal_11,
                       extreal_of_num_def] \\
     RW_TAC real_ss [REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB, REAL_ADD_LDISTRIB,
                     REAL_ADD_RDISTRIB, REAL_ADD_ASSOC, POW_2, GSYM REAL_DOUBLE] \\
     REAL_ARITH_TAC)
 >> DISCH_TAC
 >> Know ‘integrable p (\x. (X x - Normal r) pow 2) <=>
          integrable p (\x. (\x. (X x - Normal c) pow 2) x +
                            (\x. Normal (2 * (c - r)) * X x + Normal (r pow 2 - c pow 2)) x)’
 >- (MATCH_MP_TAC integrable_cong >> ASM_SIMP_TAC std_ss [])
 >> Rewr'
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
 >> MATCH_MP_TAC integrable_add
 >> RW_TAC std_ss [] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC integrable_cmul >> art [],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC integrable_const >> art [extreal_of_num_def, lt_infty] ]
QED

Theorem finite_second_moments_eq_finite_variance :
    !p X. prob_space p /\ real_random_variable X p ==>
         (finite_second_moments p X <=> variance p X < PosInf)
Proof
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
 >> `?c. expectation p X = Normal c` by PROVE_TAC [extreal_cases] >> art []
QED

Theorem finite_second_moments_lemma[local] :
    !p X. prob_space p /\ real_random_variable X p ==>
         (variance p X < PosInf <=> second_moment p X 0 < PosInf)
Proof
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
 >> Q.EXISTS_TAC `0` >> art []
QED

(* alternative definition of `finite_second_moments` for easier verification *)
Theorem finite_second_moments_alt :
    !p X. prob_space p /\ real_random_variable X p ==>
         (finite_second_moments p X <=> second_moment p X 0 < PosInf)
Proof
    rpt STRIP_TAC
 >> METIS_TAC [finite_second_moments_eq_finite_variance,
               finite_second_moments_lemma]
QED

(* |- !p X.
         prob_space p /\ real_random_variable X p ==>
         (finite_second_moments p X <=> expectation p (\x. (X x) pow 2) < PosInf)
 *)
Theorem finite_second_moments_literally =
    REWRITE_RULE [second_moment_def, moment_def, sub_rzero] finite_second_moments_alt

Theorem finite_second_moments_eq_integrable_square :
    !p X. prob_space p /\ real_random_variable X p ==>
         (finite_second_moments p X <=> integrable p (\x. X x pow 2))
Proof
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
      Rewr' >> art [GSYM lt_infty] ]
QED

(* more general version *)
Theorem finite_second_moments_eq_integrable_squares :
    !p X. prob_space p /\ real_random_variable X p ==>
         (finite_second_moments p X <=> !c. integrable p (\x. (X x - Normal c) pow 2))
Proof
    rpt STRIP_TAC
 >> EQ_TAC >> STRIP_TAC
 >| [ (* goal 1 (of 2) *)
      RW_TAC std_ss [integrable_def] >| (* 3 subgoals *)
      [ (* goal 1.1 (of 3) *)
        `!x. (X x - Normal c) pow 2 = ((\x. X x - Normal c) x) pow 2` by METIS_TAC [] \\
         POP_ORW >> MATCH_MP_TAC IN_MEASURABLE_BOREL_POW \\
         fs [prob_space_def, measure_space_def, real_random_variable_def,
             random_variable_def, space_def, p_space_def, events_def] \\
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
      METIS_TAC [integrable_imp_finite_expectation] ]
QED

Theorem bounded_imp_finite_second_moments :
    !p X. prob_space p /\ random_variable X p Borel /\
         (?r. !x. x IN p_space p ==> abs (X x) <= Normal r) ==> finite_second_moments p X
Proof
    rpt STRIP_TAC
 >> Know ‘real_random_variable X p’
 >- (rw [real_random_variable_def] \\
     fs [abs_bounds, lt_infty] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC ‘Normal (-r)’ \\
       fs [lt_infty, extreal_ainv_def],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘Normal r’ \\
       rw [lt_infty] ])
 >> DISCH_TAC
 >> Know ‘finite_second_moments p X <=> integrable p (\x. X x pow 2)’
 >- (MATCH_MP_TAC finite_second_moments_eq_integrable_square >> art [])
 >> Rewr'
 >> fs [integrable_def, real_random_variable, prob_space_def, p_space_def, events_def]
 >> CONJ_TAC
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_POW \\
     fs [measure_space_def])
 >> reverse CONJ_TAC
 >- (rw [FN_MINUS_POS_ZERO, le_pow2] \\
     rw [pos_fn_integral_zero, extreal_of_num_def, extreal_not_infty])
 >> rw [FN_PLUS_POS_ID, le_pow2, lt_infty]
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC ‘pos_fn_integral p (\x. Normal (r pow 2))’
 (* applying pos_fn_integral_const *)
 >> reverse CONJ_TAC
 >- (REWRITE_TAC [GSYM lt_infty] \\
     Suff ‘pos_fn_integral p (\x. Normal (r pow 2)) =
           Normal (r pow 2) * measure p (m_space p)’ >- rw [] \\
     MATCH_MP_TAC pos_fn_integral_const \\
     rw [le_pow2, lt_infty, extreal_of_num_def, extreal_not_infty])
 >> MATCH_MP_TAC pos_fn_integral_mono
 >> rw [le_pow2, GSYM extreal_pow_def]
 (* ‘0 <= r’ is implicit *)
 >> reverse (Cases_on ‘0 <= r’)
 >- (fs [GSYM real_lt] \\
     Suff ‘abs (X x) < 0’ >- METIS_TAC [abs_pos, let_antisym] \\
     MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘Normal r’ >> rw [] \\
     rw [extreal_of_num_def, extreal_lt_eq])
 >> ‘X x pow 2 = (abs (X x)) pow 2’ by rw [abs_pow2] >> POP_ORW
 >> MATCH_MP_TAC pow_le >> rw [abs_pos]
QED

(* NOTE: ‘integrable p X’ makes sure that ‘expectation p X’ exists and is finite *)
Theorem bounded_imp_finite_second_moments' :
    !p X. prob_space p /\ random_variable X p Borel /\ integrable p X /\
         (?r. !x. x IN p_space p ==> abs (X x - expectation p X) <= Normal r) ==>
          finite_second_moments p X
Proof
    qx_genl_tac [‘p’, ‘Y’] >> rpt STRIP_TAC
 >> MATCH_MP_TAC bounded_imp_finite_second_moments >> art []
 >> Q.ABBREV_TAC ‘M = expectation p Y’
 >> ‘M <> PosInf /\ M <> NegInf’ by METIS_TAC [integrable_imp_finite_expectation]
 >> ‘r < 0 \/ 0 <= r’ by PROVE_TAC [REAL_LTE_TOTAL]
 >- (‘?x. x IN p_space p’ by METIS_TAC [PROB_SPACE_NOT_EMPTY, MEMBER_NOT_EMPTY] \\
     ‘Normal r < 0’ by METIS_TAC [extreal_of_num_def, extreal_lt_eq] \\
     ‘abs (Y x - M) < 0’ by METIS_TAC [let_trans] \\
     METIS_TAC [abs_pos, let_antisym])
 >> ‘?m. M = Normal m’ by METIS_TAC [extreal_cases] >> fs []
 >> rename1 ‘0 <= a’
 >> Know ‘!x. x IN p_space p ==> Y x <> NegInf /\ Y x <> PosInf’
 >- (NTAC 2 STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!x. x IN p_space p ==> P’ (MP_TAC o (Q.SPEC ‘x’)) \\
     RW_TAC std_ss [] >> CCONTR_TAC >> fs [extreal_abs_def, extreal_sub_def])
 >> DISCH_TAC
 >> Q.EXISTS_TAC ‘max (m + a) (abs (m - a))’
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM ‘!x. x IN p_space p ==> Y x <> NegInf /\ Y x <> PosInf’
       (MP_TAC o (Q.SPEC ‘x’))
 >> Q.PAT_X_ASSUM ‘!x. x IN p_space p ==> abs _ <= Normal a’ (MP_TAC o (Q.SPEC ‘x’))
 >> RW_TAC std_ss []
 >> ‘?y. Y x = Normal y’ by METIS_TAC [extreal_cases]
 >> gs [extreal_sub_def, extreal_abs_def]
 >> rw [REAL_LE_MAX]
 >> ‘0 <= m \/ m <= 0’ by PROVE_TAC [REAL_LE_TOTAL]
 >| [ (* goal 1 (of 2) *)
      DISJ1_TAC \\
     ‘abs m + abs (y - m) <= m + a’ by PROVE_TAC [REAL_LE_LADD, ABS_REFL] \\
      MATCH_MP_TAC REAL_LE_TRANS \\
      Q.EXISTS_TAC ‘abs m + abs (y - m)’ >> art [] \\
     ‘abs y = abs (m + (y - m))’ by REAL_ARITH_TAC >> POP_ORW \\
      REWRITE_TAC [ABS_TRIANGLE],
      (* goal 2 (of 2) *)
      DISJ2_TAC \\
      MATCH_MP_TAC REAL_LE_TRANS \\
      Q.EXISTS_TAC ‘abs m + abs (y - m)’ >> REWRITE_TAC [ABS_TRIANGLE_SUB] \\
      Suff ‘abs (m - a) = abs m + a’ >- rw [REAL_LE_LADD] \\
     ‘abs (m - a) = abs (a - m)’ by REAL_ARITH_TAC >> POP_ORW \\
      Know ‘abs (a - m) = a - m’
      >- (rw [ABS_REFL, REAL_SUB_LE] \\
          MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC ‘0’ >> art []) >> Rewr' \\
      Know ‘abs (--m) = -m’ >- art [Once ABS_NEG, ABS_REFL, REAL_NEG_GE0] \\
      REWRITE_TAC [REAL_NEG_NEG] >> Rewr' \\
      REAL_ARITH_TAC ]
QED

Theorem finite_second_moments_imp_integrable :
    !p X. prob_space p /\ real_random_variable X p /\ finite_second_moments p X ==>
          integrable p X
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MATCH_MP_TAC integrable_from_square >> art []
 >> IMP_RES_TAC finite_second_moments_eq_integrable_square
QED

(* This theorem doesn't hold for general measure spaces (cf. integrable_bounded) *)
Theorem bounded_imp_integrable :
    !p X. prob_space p /\ random_variable X p Borel /\
         (?r. !x. x IN p_space p ==> abs (X x) <= Normal r) ==> integrable p X
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC finite_second_moments_imp_integrable >> art []
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC bounded_imp_finite_second_moments >> art [] \\
     Q.EXISTS_TAC ‘r’ >> art [])
 >> FULL_SIMP_TAC std_ss [abs_bounds]
 >> RW_TAC std_ss [real_random_variable_def, lt_infty]
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC lte_trans \\
      Q.EXISTS_TAC ‘-Normal r’ >> rw [lt_infty, extreal_ainv_def],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC let_trans \\
      Q.EXISTS_TAC  ‘Normal r’ >> rw [lt_infty, extreal_ainv_def] ]
QED

Theorem finite_second_moments_imp_finite_expectation :
    !p X. prob_space p /\ real_random_variable X p /\ finite_second_moments p X ==>
          expectation p X <> PosInf /\ expectation p X <> NegInf
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MATCH_MP_TAC integrable_imp_finite_expectation >> art []
 >> MATCH_MP_TAC finite_second_moments_imp_integrable >> art []
QED

Theorem finite_second_moments_cmul :
    !p X c. prob_space p /\ real_random_variable X p /\ finite_second_moments p X ==>
            finite_second_moments p (\x. Normal c * X x)
Proof
    rpt STRIP_TAC
 >> ‘real_random_variable (\x. Normal c * X x) p’
      by METIS_TAC [real_random_variable_cmul]
 >> ‘integrable p X’ by METIS_TAC [finite_second_moments_imp_integrable]
 >> ‘integrable p (\x. X x pow 2)’
      by METIS_TAC [finite_second_moments_eq_integrable_square]
 >> Q.PAT_X_ASSUM ‘finite_second_moments p X’ MP_TAC
 >> RW_TAC std_ss [finite_second_moments_literally, GSYM lt_infty, pow_mul, extreal_pow_def]
 >> Know ‘expectation p (\x. Normal (c pow 2) * X x pow 2) =
          Normal (c pow 2) * expectation p (\x. X x pow 2)’
 >- (HO_MATCH_MP_TAC expectation_cmul >> art [])
 >> Rewr'
 >> Know ‘expectation p (\x. X x pow 2) <> NegInf’
 >- (MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC expectation_pos >> rw [le_pow2])
 >> DISCH_TAC
 >> ‘?r. expectation p (\x. X x pow 2) = Normal r’ by METIS_TAC [extreal_cases]
 >> rw [extreal_mul_def]
QED

Theorem finite_second_moments_ainv :
    !p X. prob_space p /\ real_random_variable X p /\ finite_second_moments p X ==>
          finite_second_moments p (\x. -X x)
Proof
    rpt STRIP_TAC
 >> Know ‘(\x. -X x) = (\x. Normal (-1) * X x)’
 >- RW_TAC std_ss [FUN_EQ_THM, Once neg_minus1, extreal_of_num_def, extreal_ainv_def]
 >> Rewr'
 >> MATCH_MP_TAC finite_second_moments_cmul >> art []
QED

Theorem finite_second_moments_cdiv :
    !p X c. prob_space p /\ real_random_variable X p /\
            finite_second_moments p X /\ c <> 0 ==>
            finite_second_moments p (\x. X x / Normal c)
Proof
    rw [extreal_div_def, extreal_inv_def, Once mul_comm]
 >> MATCH_MP_TAC finite_second_moments_cmul >> art []
QED

Theorem finite_second_moments_cong :
    !p X Y. prob_space p /\ (!x. x IN p_space p ==> X x = Y x) ==>
           (finite_second_moments p X <=> finite_second_moments p Y)
Proof
    RW_TAC std_ss [finite_second_moments_def, second_moment_def, moment_def]
 >> Suff ‘!a. expectation p (\x. (X x - a) pow 2) =
              expectation p (\x. (Y x - a) pow 2)’ >- rw []
 >> Q.X_GEN_TAC ‘a’
 >> MATCH_MP_TAC expectation_cong >> rw []
QED

(* An easy corollary of Minkowski_inequality *)
Theorem finite_second_moments_add :
    !p X Y. prob_space p /\
            real_random_variable X p /\ real_random_variable Y p /\
            finite_second_moments p X /\ finite_second_moments p Y ==>
            finite_second_moments p (\x. X x + Y x)
Proof
    rpt STRIP_TAC
 >> ‘real_random_variable (\x. X x + Y x) p’
       by METIS_TAC [real_random_variable_add]
 >> rfs [finite_second_moments_eq_integrable_square, prob_space_def]
 >> fs [real_random_variable, p_space_def, events_def]
 >> Suff ‘(\x. X x + Y x) IN L2_space p’
 >- rw [L2_space_alt_integrable_square]
 >> MP_TAC (Q.SPECL [‘2’, ‘p’, ‘X’, ‘Y’] Minkowski_inequality)
 >> ‘1 <= (2 :extreal)’ by rw [extreal_of_num_def, extreal_le_eq]
 >> rw [L2_space_alt_integrable_square]
QED

Theorem finite_second_moments_sum :
    !p X (J :'index set). prob_space p /\ FINITE J /\
         (!i. i IN J ==> real_random_variable (X i) p) /\
         (!i. i IN J ==> finite_second_moments p (X i)) ==>
          finite_second_moments p (\x. SIGMA (\n. X n x) J)
Proof
    rpt STRIP_TAC
 >> NTAC 3 (POP_ASSUM MP_TAC)
 >> qid_spec_tac ‘J’
 >> Induct_on ‘J’
 >> rw [EXTREAL_SUM_IMAGE_EMPTY]
 >- (IMP_RES_TAC real_random_variable_zero \\
     rw [finite_second_moments_eq_finite_variance, variance_zero])
 >> Know ‘finite_second_moments p (\x. SIGMA (\n. X n x) (e INSERT J)) <=>
          finite_second_moments p (\x. X e x + SIGMA (\n. X n x) (J DELETE e))’
 >- (MATCH_MP_TAC finite_second_moments_cong >> rw [] \\
     MATCH_MP_TAC (List.nth
                    (CONJUNCTS (BETA_RULE
                                 (Q.SPEC ‘(\n. X n x)’ EXTREAL_SUM_IMAGE_THM)),2)) \\
     simp [] >> DISJ1_TAC >> Q.X_GEN_TAC ‘i’ \\
     METIS_TAC [real_random_variable])
 >> Rewr'
 >> ‘J DELETE e = J’ by PROVE_TAC [DELETE_NON_ELEMENT]
 >> POP_ORW
 >> HO_MATCH_MP_TAC finite_second_moments_add
 >> RW_TAC std_ss []
 >| [ (* goal 1 (of 3) *)
      METIS_TAC [],
      (* goal 2 (of 3) *)
      MATCH_MP_TAC real_random_variable_sum >> RW_TAC std_ss [],
      (* goal 3 (of 3) *)
      METIS_TAC [] ]
QED

Theorem finite_second_moments_sub :
    !p X Y. prob_space p /\
            real_random_variable X p /\ real_random_variable Y p /\
            finite_second_moments p X /\ finite_second_moments p Y ==>
            finite_second_moments p (\x. X x - Y x)
Proof
    rpt STRIP_TAC
 >> Know ‘finite_second_moments p (\x. X x - Y x) <=>
          finite_second_moments p (\x. X x + -Y x)’
 >- (MATCH_MP_TAC finite_second_moments_cong >> rw [] \\
     MATCH_MP_TAC extreal_sub_add >> METIS_TAC [real_random_variable])
 >> Rewr'
 >> HO_MATCH_MP_TAC finite_second_moments_add >> rw []
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC real_random_variable_ainv >> art [],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC finite_second_moments_ainv >> art [] ]
QED

(* An easy corollary of Cauchy_Schwarz_inequality *)
Theorem finite_second_moments_imp_integrable_mul :
    !p X Y. prob_space p /\
            real_random_variable X p /\ real_random_variable Y p /\
            finite_second_moments p X /\ finite_second_moments p Y ==>
            integrable p (\x. X x * Y x)
Proof
    rpt STRIP_TAC
 >> rfs [finite_second_moments_eq_integrable_square, prob_space_def]
 >> fs [real_random_variable, p_space_def, events_def]
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘Y’] Cauchy_Schwarz_inequality)
 >> rw [L2_space_alt_integrable_square]
QED

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

Theorem expectation_finite = integrable_imp_finite_expectation

Theorem variance_real_affine :
    !p X c. prob_space p /\ real_random_variable X p /\ integrable p X /\
            c <> PosInf /\ c <> NegInf ==> (variance p (\x. X x + c) = variance p X)
Proof
    RW_TAC std_ss [variance_alt]
 >> MATCH_MP_TAC expectation_cong
 >> RW_TAC std_ss [expectation_real_affine]
 >> `?r. c = Normal r` by METIS_TAC [extreal_cases] >> POP_ORW
 >> `?e. expectation p X = Normal e` by METIS_TAC [expectation_normal]
 >> fs [real_random_variable_def]
 >> `?z. X x = Normal z` by METIS_TAC [extreal_cases]
 >> simp [extreal_add_def, extreal_sub_def]
 >> Suff ‘z + r - (e + r) = z - e’ >- rw []
 >> REAL_ARITH_TAC
QED

Theorem variance_real_affine' :
    !p X c. prob_space p /\ real_random_variable X p /\ integrable p X /\
            c <> PosInf /\ c <> NegInf ==> (variance p (\x. X x - c) = variance p X)
Proof
    rpt STRIP_TAC
 >> Know ‘variance p (\x. X x - c) = variance p (\x. X x + -c)’
 >- (MATCH_MP_TAC variance_cong >> rw [] \\
     MATCH_MP_TAC extreal_sub_add \\
     fs [real_random_variable_def]) >> Rewr'
 >> MATCH_MP_TAC variance_real_affine >> art []
 >> `?r. c = Normal r` by METIS_TAC [extreal_cases]
 >> rw [extreal_ainv_def, extreal_not_infty]
QED

Theorem variance_cmul :
    !p X c. prob_space p /\ real_random_variable X p /\
            finite_second_moments p X ==>
           (variance p (\x. Normal c * X x) = Normal (c pow 2) * variance p X)
Proof
    rw [variance_alt]
 >> ‘integrable p X’ by PROVE_TAC [finite_second_moments_imp_integrable]
 >> ASM_SIMP_TAC std_ss [expectation_cmul]
 >> Know ‘expectation p (\x. (Normal c * X x - Normal c * expectation p X) pow 2) =
          expectation p (\x. (Normal c * (X x - expectation p X)) pow 2)’
 >- (MATCH_MP_TAC expectation_cong >> rw [] \\
     Suff ‘Normal c * (X x - expectation p X) =
           Normal c * X x - Normal c * expectation p X’ >- Rewr \\
     MATCH_MP_TAC sub_ldistrib \\
     fs [real_random_variable_def, extreal_not_infty] \\
     PROVE_TAC [integrable_imp_finite_expectation])
 >> Rewr'
 >> REWRITE_TAC [pow_mul, extreal_pow_def]
 >> HO_MATCH_MP_TAC expectation_cmul >> art []
 >> ‘expectation p X <> PosInf /\ expectation p X <> NegInf’
      by PROVE_TAC [integrable_imp_finite_expectation]
 >> ‘?r. expectation p X = Normal r’ by METIS_TAC [extreal_cases]
 >> POP_ORW
 >> METIS_TAC [finite_second_moments_eq_integrable_squares]
QED

Theorem variance_cdiv :
    !p X c. prob_space p /\ real_random_variable X p /\
            finite_second_moments p X /\ c <> 0 ==>
           (variance p (\x. X x / Normal c) = variance p X / Normal (c pow 2))
Proof
    rw [extreal_div_def, extreal_inv_def, POW_INV]
 >> ONCE_REWRITE_TAC [mul_comm]
 >> MATCH_MP_TAC variance_cmul >> art []
QED

(* ------------------------------------------------------------------------- *)
(*    Markov and Chebyshev's Inequalities                                    *)
(* ------------------------------------------------------------------------- *)

(* Markov's inequality (probability version) *)
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

(* Chebyshev's inequality (probability version) *)
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

(* The special version with ‘<’ in place of ‘<=’ *)
Theorem chebyshev_ineq_variance' :
    !p X t. prob_space p /\ real_random_variable X p /\
            finite_second_moments p X /\ 0 < t ==>
         prob p ({x | t < abs (X x - expectation p X)} INTER p_space p) <=
           inv (t pow 2) * variance p X
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC ‘prob p ({x | t <= abs (X x - expectation p X)} INTER p_space p)’
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC chebyshev_ineq_variance >> art [])
 >> MATCH_MP_TAC PROB_INCREASING >> art []
 >> REWRITE_TAC [CONJ_ASSOC]
 >> reverse CONJ_TAC
 >- (rw [SUBSET_DEF, GSPECIFICATION] \\
     MATCH_MP_TAC lt_imp_le >> art [])
 >> fs [real_random_variable, prob_space_def, p_space_def, events_def]
 >> Q.ABBREV_TAC ‘Y = \x. X x - expectation p X’ >> simp []
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
 >> Know ‘Y IN measurable (m_space p,measurable_sets p) Borel’
 >- (rw [Abbr ‘Y’] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB' \\
     qexistsl_tac [‘X’, ‘\x. expectation p X’] >> simp [] \\
     fs [measure_space_def] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST' >> art [])
 >> DISCH_TAC
 >> rw [lt_abs_bounds, le_abs_bounds]
 >| [ (* goal 1 (of 2) *)
     ‘{x | Y x < -t \/ t < Y x} INTER m_space p =
        ({x | Y x < -t} INTER m_space p) UNION
        ({x | t < Y x} INTER m_space p)’ by SET_TAC [] >> POP_ORW \\
      MATCH_MP_TAC MEASURE_SPACE_UNION >> art [] \\
      METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE],
      (* goal 2 (of 2) *)
     ‘{x | Y x <= -t \/ t <= Y x} INTER m_space p =
        ({x | Y x <= -t} INTER m_space p) UNION
        ({x | t <= Y x} INTER m_space p)’ by SET_TAC [] >> POP_ORW \\
      MATCH_MP_TAC MEASURE_SPACE_UNION >> art [] \\
      METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE] ]
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

Overload indep_sets = “indep_families”

(* 5. extension of `indep_families`: pairwise independent sets/collections of events *)
Definition pairwise_indep_sets :
    pairwise_indep_sets p A (J :'index set) =
      pairwise (\i j. indep_families p (A i) (A j)) J
End

Theorem pairwise_indep_sets_def :
    !p A (J :'index set).
       pairwise_indep_sets p A J <=>
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

Overload indep_vars = “indep_rv”

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

Theorem pairwise_indep_vars_subset :
    !p X A (s :'index set) (t :'index set).
       pairwise_indep_vars p X A t /\ s SUBSET t ==>
       pairwise_indep_vars p X A s
Proof
    rw [pairwise_indep_vars_def]
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> METIS_TAC [SUBSET_DEF]
QED

(* 9. extension of `indep-rv`: totally/mutually independent r.v.'s

  See indep_vars_alt_indep_events for a weaker equivalent condition for testing
      independence.

  NOTE: ‘indep_vars’ has been modified to make sure [indep_vars_subset] holds.

  old definition:

Definition old_indep_vars_def :
    old_indep_vars p X A (J :'index set) =
      !E. E IN (J --> (subsets o A)) ==>
          indep_events p (\n. (PREIMAGE (X n) (E n)) INTER p_space p) J
End

> REWRITE_RULE [indep_events_def] old_indep_vars_def;
val it =
  |- !p X A J.
        old_indep_vars p X A J <=>
        !E. E IN J --> subsets o A ==>
            !N. N SUBSET J /\ N <> {} /\ FINITE N ==>
                prob p (BIGINTER (IMAGE (\n. PREIMAGE (X n) (E n) INTER p_space p) N)) =
                PI (prob p o (\n. PREIMAGE (X n) (E n) INTER p_space p)) N:

  new definition:
 *)
Definition indep_vars_def :
    indep_vars p X A (J :'index set) =
      !E N. N SUBSET J /\ N <> {} /\ FINITE N /\
            E IN (N --> subsets o A) ==>
            prob p (BIGINTER (IMAGE (\n. PREIMAGE (X n) (E n) INTER p_space p) N)) =
            PI (prob p o (\n. PREIMAGE (X n) (E n) INTER p_space p)) N
End

(* NOTE: If a set of r.v.'s is (totally) independent, so is any subset of them.
         With the new definition of ‘indep_vars’, this proof is very easy now.
 *)
Theorem indep_vars_subset :
    !p X A (s :'index set) (t :'index set).
       indep_vars p X A t /\ s SUBSET t ==> indep_vars p X A s
Proof
    RW_TAC std_ss [indep_vars_def, IN_DFUNSET, indep_events_def]
 >> FIRST_X_ASSUM irule >> simp []
 >> PROVE_TAC [SUBSET_TRANS]
QED

(* NOTE: the old and new definitions are actually equivalent, given ‘A n’ is indeed
   a sigma-algebra (which can be actually weakened to ‘?x. x IN subsets (A n)’), or
   ring, semiring, algebra, etc.
 *)
Theorem indep_vars_alt_indep_events :
    !p X A (J :'index set).
       (!n. n IN J ==> sigma_algebra (A n)) ==>
       (indep_vars p X A (J :'index set) <=>
        !E. E IN (J --> (subsets o A)) ==>
            indep_events p (\n. (PREIMAGE (X n) (E n)) INTER p_space p) J)
Proof
    rpt STRIP_TAC
 >> EQ_TAC
 >> RW_TAC std_ss [indep_vars_def, indep_events_def]
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> fs [IN_DFUNSET] \\
     METIS_TAC [SUBSET_DEF])
 (* The key is to choose V such that, for each indexes ‘n NOTIN N’, an arbitrary
    element ‘E n’ is choosen such that ‘E n IN subsets (A n)’ holds. Here we chose
   ‘{}’, assuming ‘sigma_algebra (A n)’.
  *)
 >> Q.ABBREV_TAC ‘V = \n. if n IN N then E n else {}’
 >> Q.PAT_X_ASSUM ‘!E. E IN J --> subsets o A ==> P’ (MP_TAC o (Q.SPEC ‘V’))
 >> Know ‘V IN J --> subsets o A’
 >- (fs [Abbr ‘V’, IN_DFUNSET] >> rw [] \\
     METIS_TAC [SIGMA_ALGEBRA_EMPTY])
 >> RW_TAC std_ss []
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘N’))
 >> RW_TAC std_ss []
 >> Suff ‘IMAGE (\n. PREIMAGE (X n) (E n) INTER p_space p) N =
          IMAGE (\n. PREIMAGE (X n) (V n) INTER p_space p) N /\
          PI (prob p o (\n. PREIMAGE (X n) (E n) INTER p_space p)) N =
          PI (prob p o (\n. PREIMAGE (X n) (V n) INTER p_space p)) N’ >- rw []
 >> CONJ_TAC
 >- (rw [Once EXTENSION] >> EQ_TAC >> rw [Abbr ‘V’] \\
     Q.EXISTS_TAC ‘n’ >> rw [])
 >> MATCH_MP_TAC EXTREAL_PROD_IMAGE_EQ
 >> Q.X_GEN_TAC ‘n’ >> rw [Abbr ‘V’]
QED

(* Alternative definition of independent r.v.'s for index set as ‘univ(:num)’

   It's sufficient that the increasing first n r.v.'s are mutually independent,
   and no need for arbitrary (non-empty) subset N of univ(:num).
 *)
Theorem indep_vars_alt_univ :
    !p X A. prob_space p /\ (!n. sigma_algebra (A n)) /\
           (!n. random_variable (X n) p (A n)) ==>
       (indep_vars p X A univ(:num) <=>
        !E n. E IN (count1 n --> subsets o A) ==>
              prob p (BIGINTER (IMAGE (\n. PREIMAGE (X n) (E n) INTER p_space p) (count1 n))) =
              PI (prob p o (\n. PREIMAGE (X n) (E n) INTER p_space p)) (count1 n))
Proof
    RW_TAC std_ss [indep_vars_def]
 >> EQ_TAC >> rw [] (* only one goal remains *)
 >> Q.ABBREV_TAC ‘V = \n. if n IN N then E n else space (A n)’
 (* find the maximal element m of N *)
 >> MP_TAC (FINITE_is_measure_maximal |> Q.GEN ‘m’
                                      |> INST_TYPE [“:'a” |-> “:num”]
                                      |> Q.SPECL [‘I’, ‘N’])
 >> rw [is_measure_maximal_def] >> rename1 ‘m IN N’
 >> Q.PAT_X_ASSUM ‘!E n. E IN count1 n --> subsets o A ==> P’
      (MP_TAC o (Q.SPECL [‘V’, ‘m’]))
 >> Know ‘V IN count1 m --> subsets o A’
 >- (rw [IN_DFUNSET, Abbr ‘V’] \\
     Cases_on ‘n IN N’ >- fs [IN_DFUNSET] \\
     simp [SIGMA_ALGEBRA_SPACE])
 >> RW_TAC std_ss []
 >> Suff ‘prob p (BIGINTER (IMAGE (\n. PREIMAGE (X n) (E n) INTER p_space p) N)) =
          prob p (BIGINTER (IMAGE (\n. PREIMAGE (X n) (V n) INTER p_space p) (count1 m))) /\
          PI (prob p o (\n. PREIMAGE (X n) (E n) INTER p_space p)) N =
          PI (prob p o (\n. PREIMAGE (X n) (V n) INTER p_space p)) (count1 m)’ >- rw []
 >> Q.ABBREV_TAC ‘D = count1 m DIFF N’
 >> ‘DISJOINT N D’ by rw [DISJOINT_ALT, Abbr ‘D’]
 >> Know ‘count1 m = N UNION D’
 >- (rw [Once EXTENSION, Abbr ‘D’] \\
     EQ_TAC >> rw [] >> rw [LT_SUC_LE]) >> Rewr'
 >> Know ‘IMAGE (\n. PREIMAGE (X n) (E n) INTER p_space p) N =
          IMAGE (\n. PREIMAGE (X n) (V n) INTER p_space p) N’
 >- (rw [Once EXTENSION, IN_IMAGE, Abbr ‘V’] \\
     EQ_TAC >> rw [] >> Q.EXISTS_TAC ‘n’ >> rw [])
 >> Rewr'
 >> Know ‘PI (prob p o (\n. PREIMAGE (X n) (E n) INTER p_space p)) N =
          PI (prob p o (\n. PREIMAGE (X n) (V n) INTER p_space p)) N’
 >- (MATCH_MP_TAC EXTREAL_PROD_IMAGE_EQ >> rw [Abbr ‘V’])
 >> Rewr'
 >> Cases_on ‘D = {}’ >- rw []
 >> Know ‘!n. n IN D ==> PREIMAGE (X n) (V n) INTER p_space p = p_space p’
 >- (rw [Abbr ‘D’, Abbr ‘V’, PREIMAGE_def] \\
     rw [Once EXTENSION] \\
     EQ_TAC >> rw [] \\
     fs [random_variable_def, measurable_def, IN_FUNSET])
 >> DISCH_TAC
 >> CONJ_TAC
 >- (rw [IMAGE_UNION, BIGINTER_UNION] \\
     Know ‘IMAGE (\n. PREIMAGE (X n) (V n) INTER p_space p) D =
           IMAGE (\n. p_space p) D’
     >- (rw [Once EXTENSION] \\
         EQ_TAC >> rw [] >> Q.EXISTS_TAC ‘n’ >> rw []) >> Rewr' \\
     Know ‘BIGINTER (IMAGE (\n. p_space p) D) = p_space p’
     >- (rw [Once EXTENSION, IN_BIGINTER_IMAGE] \\
         EQ_TAC >> rw [] \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
         METIS_TAC [MEMBER_NOT_EMPTY]) >> Rewr' \\
     ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC PROB_UNDER_UNIV >> art [] \\
     MATCH_MP_TAC EVENTS_BIGINTER_FN >> art [COUNTABLE_NUM] \\
     rw [SUBSET_DEF] \\
     fs [random_variable_def, measurable_def, IN_DFUNSET, Abbr ‘V’])
 >> Know ‘FINITE D’
 >- (irule SUBSET_FINITE >> Q.EXISTS_TAC ‘count1 m’ >> rw [Abbr ‘D’])
 >> DISCH_TAC
 >> Know ‘PI (prob p o (\n. PREIMAGE (X n) (V n) INTER p_space p)) (N UNION D) =
          PI (prob p o (\n. PREIMAGE (X n) (V n) INTER p_space p)) N *
          PI (prob p o (\n. PREIMAGE (X n) (V n) INTER p_space p)) D’
 >- (MATCH_MP_TAC EXTREAL_PROD_IMAGE_DISJOINT_UNION >> art [])
 >> Rewr'
 >> Suff ‘PI (prob p o (\n. PREIMAGE (X n) (V n) INTER p_space p)) D = 1’ >- rw []
 >> Know ‘PI (prob p o (\n. PREIMAGE (X n) (V n) INTER p_space p)) D =
          PI (prob p o (\n. p_space p)) D’
 >- (MATCH_MP_TAC EXTREAL_PROD_IMAGE_EQ >> rw [])
 >> Rewr'
 >> simp [o_DEF, PROB_UNIV, EXTREAL_PROD_IMAGE_ONE]
QED

(* not used *)
val indep_function_def = Define
   `indep_function p =
   {f | indep_families p (IMAGE (PREIMAGE (FST o f)) UNIV)
                         (IMAGE (PREIMAGE (SND o f)) (events p))}`;

val PROB_INDEP = store_thm
  ("PROB_INDEP",
  ``!p s t u. indep p s t /\ (u = s INTER t) ==> (prob p u = prob p s * prob p t)``,
    RW_TAC std_ss [indep_def]);

Theorem INDEP :
  !p a b. a IN events p /\ b IN events p /\
          prob p (a INTER b) = prob p a * prob p b ==> indep p a b
Proof
  rw [indep_def]
QED

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

(* total ==> pairwise independence (of random variables)

   NOTE: added ‘prob_space p /\ !i. i IN J ==> sigma_algebra (A i)’ due to
         changes of ‘measurable’
 *)
Theorem total_imp_pairwise_indep_vars :
    !p X A (J :'index set). prob_space p /\
        (!i. i IN J ==> random_variable (X i) p (A i)) /\
        (!i. i IN J ==> sigma_algebra (A i)) /\
        indep_vars p X A J ==> pairwise_indep_vars p X A J
Proof
    RW_TAC std_ss [indep_vars_def, pairwise_indep_vars_def, indep_rv_def,
                   indep_events_def, random_variable_def]
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
 >> REWRITE_TAC [indep_def]
 >> STRONG_CONJ_TAC
 >- (‘X i IN measurable (p_space p,events p) (A i)’ by PROVE_TAC [] \\
     POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [IN_MEASURABLE, space_def, subsets_def])) \\
     POP_ASSUM MATCH_MP_TAC >> art []) >> DISCH_TAC
 >> STRONG_CONJ_TAC
 >- (‘X j IN measurable (p_space p,events p) (A j)’ by PROVE_TAC [] \\
     POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [IN_MEASURABLE, space_def, subsets_def])) \\
     POP_ASSUM MATCH_MP_TAC >> art []) >> DISCH_TAC
 >> Q.ABBREV_TAC ‘E = \x. if x = i then a else if x = j then b else {}’
 >> Q.PAT_X_ASSUM ‘!E N. _’ (MP_TAC o (Q.SPEC ‘E’))
 >> SIMP_TAC std_ss [IN_DFUNSET, o_DEF]
 >> ‘{i; j} SUBSET J’ by rw [SUBSET_DEF]
 >> DISCH_THEN (MP_TAC o Q.SPEC ‘{i; j}’) >> simp [FINITE_TWO]
 >> Know ‘PI (\n. prob p (PREIMAGE (X n) (E n) INTER p_space p)) {i; j} =
             (\n. prob p (PREIMAGE (X n) (E n) INTER p_space p)) i *
             (\n. prob p (PREIMAGE (X n) (E n) INTER p_space p)) j’
 >- (MATCH_MP_TAC EXTREAL_PROD_IMAGE_PAIR >> art [])
 >> BETA_TAC >> Rewr'
 >> Know ‘E i = a’ >- RW_TAC std_ss [Abbr ‘E’] >> Rewr'
 >> Know ‘E j = b’ >- RW_TAC std_ss [Abbr ‘E’] >> Rewr'
 >> DISCH_THEN MATCH_MP_TAC
 >> rw [Abbr ‘E’]
QED

(* alternative definition of ‘indep_rv’ in ‘indep_vars’ *)
Theorem indep_rv_alt_indep_vars :
    !p X Y A B. random_variable (X :'a -> 'b) p A /\
                random_variable (Y :'a -> 'b) p B ==>
               (indep_rv p X Y A B <=> indep_vars p (binary X Y) (binary A B) {0; 1})
Proof
    rw [indep_vars_def, indep_rv_def, indep_events_def]
 >> reverse EQ_TAC >> rw []
 >- (Q.PAT_X_ASSUM ‘!E N. P’ (MP_TAC o (Q.SPECL [‘binary a b’, ‘{0;1}’])) \\
     Know ‘binary a b IN {0; 1} --> subsets o binary A B’
     >- (rw [IN_DFUNSET, binary_def] >> simp []) >> Rewr \\
     simp [binary_def] \\
    ‘{1} DELETE (0 :num) = {1}’ by rw [GSYM DELETE_NON_ELEMENT] \\
     rw [EXTREAL_PROD_IMAGE_THM, FINITE_TWO, indep_def] \\
     fs [random_variable_def, IN_MEASURABLE])
 >> ‘N = {0} \/ N = {1} \/ N = {0; 1}’ by METIS_TAC [SUBSET_TWO]
 >- rw [EXTREAL_PROD_IMAGE_SING]
 >- rw [EXTREAL_PROD_IMAGE_SING]
 >> POP_ASSUM (fs o wrap)
 >> ‘{1} DELETE (0 :num) = {1}’ by rw [GSYM DELETE_NON_ELEMENT]
 >> rw [EXTREAL_PROD_IMAGE_THM, FINITE_TWO, binary_def]
 >> fs [IN_DFUNSET]
 >> ‘E 0 IN subsets A’ by METIS_TAC [binary_def]
 >> Know ‘E 1 IN subsets B’
 >- (Q.PAT_X_ASSUM ‘!x. x = 0 \/ x = 1 ==> P’ (MP_TAC o (Q.SPEC ‘1’)) \\
     rw [binary_def])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘!a b. P’ (MP_TAC o (Q.SPECL [‘E (0 :num)’, ‘E (1 :num)’]))
 >> rw [indep_def]
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
       RW_TAC std_ss [IN_IMAGE, PULL_EXISTS] \\
      `!i. i IN J ==> B i IN events p` by PROVE_TAC [SUBSET_DEF, IN_INSERT, IN_IMAGE] \\
       drule_then (qx_choose_then ‘x’ strip_assume_tac)
                  (iffRL MEMBER_NOT_EMPTY) >>
      `B x IN events p` by PROVE_TAC [SUBSET_DEF] \\
       irule_at Any PROB_SPACE_SUBSET_PSPACE >> art[] >>
       first_assum (irule_at Any) >> art[],
       (* goal 3 (of 4) *)
       DISJ2_TAC >> Q.EXISTS_TAC `N` >> art [] \\
       Suff `BIGINTER (IMAGE B N) SUBSET p_space p`
       >- PROVE_TAC [INTER_SUBSET_EQN] \\
       MATCH_MP_TAC BIGINTER_SUBSET \\
       RW_TAC std_ss [IN_IMAGE, PULL_EXISTS] \\
      `!i. i IN J ==> B i IN events p` by PROVE_TAC [SUBSET_DEF, IN_INSERT, IN_IMAGE] \\
       drule_then (qx_choose_then ‘x’ strip_assume_tac)
                  (iffRL MEMBER_NOT_EMPTY) >>
      `B x IN events p` by PROVE_TAC [SUBSET_DEF] \\
       irule_at Any PROB_SPACE_SUBSET_PSPACE >> art[] >>
       first_assum (irule_at Any) >> art[],
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
     DISJ2_TAC \\
     rename1 ‘x IN J’ >> Q.EXISTS_TAC `{x}` \\
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

Overload tail_algebra = “tail_algebra_of_rv”

(* Theorem 3.5.1 of [3, p.37], Kolmogorov 0-1 Law (for independent events).

   NOTE: there's a more general version of "Kolmogorov 0-1 Law" for independent r.v.'s
  ([5, p.3] or [2, p.264]) under a different definition of "tail field" generated by
  `sigma_functions` (martingaleTheory).
 *)
Theorem Kolmogorov_0_1_Law :
    !p E. prob_space p /\ (!n. E n IN events p) /\ indep_events p E UNIV ==>
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
 >- (RW_TAC std_ss [indep_events_def, IN_INSERT, GSPECIFICATION] \\
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
         CCONTR_TAC \\
        ‘DIV2 x < DIV2 x’ by METIS_TAC [] \\
         FULL_SIMP_TAC arith_ss []) >> DISCH_TAC \\
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
(*  Uncorrelation of r.v.'s [2, p.107-108]                                    *)
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

Theorem covariance_self :
    !p X. covariance p X X = variance p X
Proof
    RW_TAC std_ss [variance_alt, covariance_def, pow_2]
QED

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
 >> `!s. s IN p_space p ==>
         X s <> PosInf /\ X s <> NegInf /\ Y s <> PosInf /\ Y s <> NegInf`
      by PROVE_TAC [real_random_variable_def]
 >> `?c. expectation p X = Normal c` by PROVE_TAC [extreal_cases]
 >> `?d. expectation p Y = Normal d` by PROVE_TAC [extreal_cases] >> art []
 >> Know `!s. s IN p_space p ==>
             (X s - Normal c) * (Y s - Normal d) =
             (\x. (X x) * (Y x)) s +
             (\x. (Normal c * Normal d - Normal c * (Y x) - Normal d * (X x))) s`
 >- (RW_TAC std_ss [] \\
    `?a. X s = Normal a` by PROVE_TAC [extreal_cases] >> POP_ORW \\
    `?b. Y s = Normal b` by PROVE_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def, extreal_add_def, extreal_mul_def, extreal_11] \\
     REAL_ARITH_TAC)
 >> DISCH_TAC
 >> Know ‘expectation p (\s. (X s - Normal c) * (Y s - Normal d)) =
          expectation p (\s. (\x. X x * Y x) s +
                             (\x. Normal c * Normal d - Normal c * Y x - Normal d * X x) s)’
 >- (MATCH_MP_TAC expectation_cong >> RW_TAC std_ss []) >> Rewr'
 >> POP_ASSUM K_TAC (* clean up useless assumption *)
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
 >> Know `integral p (\x. Normal c * Normal d - Normal c * Y x - Normal d * X x) =
          integral p (\x. (\x. Normal c * Normal d) x +
                          (\x. (- Normal c) * Y x + (- Normal d) * X x) x)`
 >- (MATCH_MP_TAC integral_cong >> RW_TAC std_ss [] \\
    `?a. X x = Normal a` by PROVE_TAC [extreal_cases] >> POP_ORW \\
    `?b. Y x = Normal b` by PROVE_TAC [extreal_cases] >> POP_ORW \\
     SIMP_TAC real_ss [extreal_mul_def, extreal_ainv_def, extreal_add_def, extreal_sub_def,
                       extreal_11] \\
     REAL_ARITH_TAC)
 >> Rewr'
 >> Know `integral p (\x. (\x. Normal c * Normal d) x +
                          (\x. -Normal c * Y x + -Normal d * X x) x) =
          integral p (\x. Normal c * Normal d) +
          integral p (\x. -Normal c * Y x + -Normal d * X x)`
 >- (MATCH_MP_TAC integral_add \\
     RW_TAC std_ss [extreal_ainv_def, extreal_mul_def, extreal_not_infty] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC integrable_const >> art [extreal_of_num_def, lt_infty],
       (* goal 2 (of 2) *)
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
          REWRITE_TAC [extreal_mul_def, extreal_not_infty] ] ]) >> Rewr'
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
 >> ASM_REWRITE_TAC [extreal_ainv_def, extreal_mul_def, extreal_add_def, extreal_11,
                     extreal_of_num_def]
 >> REAL_ARITH_TAC
QED

Theorem uncorrelated_covariance :
    !p X Y. prob_space p /\ real_random_variable X p /\ real_random_variable Y p /\
            uncorrelated p X Y ==> (covariance p X Y = 0)
Proof
    RW_TAC std_ss [covariance_def]
 >> MATCH_MP_TAC uncorrelated_thm >> art []
QED

Theorem uncorrelated_orthogonal :
    !p X Y. prob_space p /\ real_random_variable X p /\ real_random_variable Y p /\
            (expectation p X = 0) /\ (expectation p Y = 0) ==>
            (uncorrelated p X Y <=> orthogonal p X Y)
Proof
    rw [orthogonal_def, uncorrelated_def]
QED

(* Fundamental relation of uncorrelated r.v.'s [2, p.108] *)
Theorem variance_sum :
    !p X (J :'index set).
            prob_space p /\ FINITE J /\ (!i. i IN J ==> real_random_variable (X i) p) /\
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
 >- (FULL_SIMP_TAC std_ss [SING_DEF] \\
     RW_TAC std_ss [EXTREAL_SUM_IMAGE_SING] >> METIS_TAC [])
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
 >> Know `!i x. i IN J /\ x IN p_space p ==> X i x <> PosInf /\ X i x <> NegInf`
 >- fs [real_random_variable_def] >> DISCH_TAC
 (* LHS: applying EXTREAL_SUM_IMAGE_SUB *)
 >> Know `!x. x IN p_space p ==>
              SIGMA (\n. X n x) J - SIGMA (\n. expectation p (X n)) J =
              SIGMA (\n. (\n. X n x) n - (\n. expectation p (X n)) n) J`
 >- (rpt STRIP_TAC >> MATCH_MP_TAC EQ_SYM \\
     irule EXTREAL_SUM_IMAGE_SUB >> art [] >> DISJ1_TAC >> RW_TAC std_ss [])
 >> DISCH_TAC
 >> Know ‘expectation p
            (\x. (SIGMA (\n. X n x) J - SIGMA (\n. expectation p (X n)) J) pow 2) =
          expectation p
            (\x. (SIGMA (\n. (\n. X n x) n - (\n. expectation p (X n)) n) J) pow 2)’
 >- (MATCH_MP_TAC expectation_cong >> RW_TAC std_ss [])
 >> Rewr' >> BETA_TAC
 >> POP_ASSUM K_TAC
 (* LHS: applying EXTREAL_SUM_IMAGE_POW *)
 >> Know `!x. x IN p_space p ==>
              (SIGMA (\n. X n x - expectation p (X n)) J) pow 2 =
              SIGMA (\(i,j). (\n. X n x - expectation p (X n)) i *
                             (\n. X n x - expectation p (X n)) j) (J CROSS J)`
 >- (rpt STRIP_TAC \\
     irule EXTREAL_SUM_IMAGE_POW >> RW_TAC std_ss [] \\ (* 2 subgoals, same tactics *)
    `?a. X x' x = Normal a` by METIS_TAC [extreal_cases] >> POP_ORW \\
    `?b. expectation p (X x') = Normal b` by METIS_TAC [extreal_cases] >> POP_ORW \\
     REWRITE_TAC [extreal_sub_def, extreal_not_infty])
 >> DISCH_TAC
 >> Know ‘expectation p (\x. SIGMA (\n. X n x - expectation p (X n)) J pow 2) =
          expectation p (\x. SIGMA (\(i,j). (\n. X n x - expectation p (X n)) i *
                                            (\n. X n x - expectation p (X n)) j) (J CROSS J))’
 >- (MATCH_MP_TAC expectation_cong >> RW_TAC std_ss [])
 >> Rewr' >> BETA_TAC
 >> POP_ASSUM K_TAC
 (* LHS: applying EXTREAL_SUM_IMAGE_DISJOINT_UNION *)
 >> Q.ABBREV_TAC `A = {(i,i) | i IN J}`
 >> Q.ABBREV_TAC `B = {(i,j) | i IN J /\ j IN J /\ i <> j}`
 >> Know `DISJOINT A B`
 >- (Q.UNABBREV_TAC `A` >> Q.UNABBREV_TAC `B` \\
     RW_TAC std_ss [DISJOINT_DEF, Once EXTENSION, NOT_IN_EMPTY, GSPECIFICATION, IN_INTER] \\
     Cases_on `x` >> Cases_on `q = r`
     >- (DISJ2_TAC >> GEN_TAC >> Cases_on `x'` >> RW_TAC std_ss [] \\
         METIS_TAC []) \\
     DISJ1_TAC >> GEN_TAC >> RW_TAC std_ss [] >> METIS_TAC [])
 >> DISCH_TAC
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
       (* goal 5 (of 5) *) Cases_on `x` >> fs [] ])
 >> DISCH_TAC >> art []
 >> Know ‘expectation p
            (\x. SIGMA (\(i,j). (X i x - expectation p (X i)) *
                                (X j x - expectation p (X j))) (A UNION B)) =
          expectation p
            (\x. SIGMA (\(i,j). (X i x - expectation p (X i)) *
                                (X j x - expectation p (X j))) A +
                 SIGMA (\(i,j). (X i x - expectation p (X i)) *
                                (X j x - expectation p (X j))) B)’
 >- (MATCH_MP_TAC expectation_cong >> RW_TAC std_ss [] \\
     irule EXTREAL_SUM_IMAGE_DISJOINT_UNION \\

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
 >> `A = IMAGE (\x. (x,x)) J`
       by (RW_TAC std_ss [Abbr ‘A’, Once EXTENSION, IN_IMAGE, GSPECIFICATION])
 >> Know ‘!x. x IN p_space p ==>
              SIGMA (\(i,j). (X i x - expectation p (X i)) *
                             (X j x - expectation p (X j))) A =
              SIGMA ((\(i,j). (X i x - expectation p (X i)) *
                              (X j x - expectation p (X j))) o (\x. (x,x))) J’
 >- (rpt STRIP_TAC >> art [] >> irule EXTREAL_SUM_IMAGE_IMAGE >> art [] \\
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
     REWRITE_TAC [extreal_sub_def, extreal_mul_def, extreal_not_infty])
 >> SIMP_TAC std_ss [o_DEF, GSYM pow_2]
 >> DISCH_TAC
 >> Know ‘expectation p
            (\x. SIGMA (\(i,j). (X i x - expectation p (X i)) *
                                (X j x - expectation p (X j))) A +
                 SIGMA (\(i,j). (X i x - expectation p (X i)) *
                                (X j x - expectation p (X j))) B) =
          expectation p
            (\x. SIGMA (\n. (X n x - expectation p (X n)) pow 2) J +
                 SIGMA (\(i,j). (X i x - expectation p (X i)) *
                                (X j x - expectation p (X j))) B)’
 >- (MATCH_MP_TAC expectation_cong >> RW_TAC std_ss []) >> Rewr'
 >> POP_ASSUM K_TAC
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
             MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST \\
             Q.EXISTS_TAC `E1` >> fs [space_def]) \\
        `!x. X r x - E2 = X r x - (\x. E2) x` by METIS_TAC [] >> POP_ORW \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
         qexistsl_tac [`X r`, `\x. E2`] \\
         fs [real_random_variable, space_def, p_space_def, events_def] \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST \\
         Q.EXISTS_TAC `E2` >> fs [space_def]) \\
     RW_TAC std_ss [abs_le_half_pow2])
 >> DISCH_TAC
 (* LHS: applying integral_add *)
 >> Know `expectation p
            (\x. (\x. SIGMA (\n. (X n x - expectation p (X n)) pow 2) J) x +
                 (\x. SIGMA (\(i,j). (X i x - expectation p (X i)) *
                                     (X j x - expectation p (X j))) B) x) =
          expectation p (\x. SIGMA (\n. (X n x - expectation p (X n)) pow 2) J) +
          expectation p (\x. SIGMA (\(i,j). (X i x - expectation p (X i)) *
                                            (X j x - expectation p (X j))) B)`
 >- (REWRITE_TAC [expectation_def] >> MATCH_MP_TAC integral_add \\
     CONJ_TAC >- FULL_SIMP_TAC std_ss [prob_space_def] \\
     REWRITE_TAC [CONJ_ASSOC] \\
     reverse CONJ_TAC (* easy goals first *)
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
         FULL_SIMP_TAC std_ss [p_space_def] \\
        `?a. X q x = Normal a` by PROVE_TAC [extreal_cases] >> POP_ORW \\
        `?b. X r x = Normal b` by PROVE_TAC [extreal_cases] >> POP_ORW \\
        `?c. expectation p (X q) = Normal c` by PROVE_TAC [extreal_cases] >> POP_ORW \\
        `?d. expectation p (X r) = Normal d` by PROVE_TAC [extreal_cases] >> POP_ORW \\
         REWRITE_TAC [extreal_sub_def, extreal_mul_def, extreal_not_infty]) \\
  (* integrable p (\x. SIGMA (\n. (X n x - integral p (X n)) pow 2) J) *)
     CONJ_TAC
     >- (`!x n. (X n x - integral p (X n)) pow 2 =
                 (\n x. (X n x - integral p (X n)) pow 2) n x` by METIS_TAC [] \\
         POP_ORW >> MATCH_MP_TAC integrable_sum >> ASM_SIMP_TAC std_ss [] \\
         CONJ_TAC >- FULL_SIMP_TAC std_ss [prob_space_def] \\
         CONJ_TAC
         >- (RW_TAC std_ss [GSYM expectation_def] \\
            `?r. expectation p (X i) = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
             METIS_TAC [finite_second_moments_eq_integrable_squares]) \\
         rpt GEN_TAC >> SIMP_TAC std_ss [GSYM expectation_def] >> STRIP_TAC \\
        `?r. expectation p (X i) = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
         FULL_SIMP_TAC std_ss [p_space_def] \\
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
     CONJ_TAC >- FULL_SIMP_TAC std_ss [prob_space_def] \\
     reverse CONJ_TAC
     >- (rpt GEN_TAC >> STRIP_TAC \\
         Cases_on `i` >> FULL_SIMP_TAC std_ss [] \\
         Know `q IN J /\ r IN J`
         >- (CONJ_TAC >> `(q,r) IN (J CROSS J)` by PROVE_TAC [SUBSET_DEF] \\
             POP_ASSUM MP_TAC >> SIMP_TAC std_ss [IN_CROSS]) >> STRIP_TAC \\
         REWRITE_TAC [GSYM expectation_def] \\
         FULL_SIMP_TAC std_ss [p_space_def] \\
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
 >> Know `expectation p (\x. SIGMA (\n. (\i x. (X i x - expectation p (X i)) pow 2) n x) J) =
          SIGMA (\n. expectation p ((\i x. (X i x - expectation p (X i)) pow 2) n)) J`
 >- (REWRITE_TAC [expectation_def] \\
     MATCH_MP_TAC integral_sum >> ASM_SIMP_TAC std_ss [] \\
     CONJ_TAC >- FULL_SIMP_TAC std_ss [prob_space_def] \\
     reverse CONJ_TAC
     >- (RW_TAC std_ss [GSYM expectation_def, pow_2] \\
         FULL_SIMP_TAC std_ss [p_space_def] \\
        `?r. X i x = Normal r` by PROVE_TAC [extreal_cases] >> POP_ORW \\
        `?c. expectation p (X i) = Normal c` by PROVE_TAC [extreal_cases] >> POP_ORW \\
         REWRITE_TAC [extreal_sub_def, extreal_mul_def, extreal_not_infty]) \\
     RW_TAC std_ss [GSYM expectation_def] \\
    `?c. expectation p (X i) = Normal c` by PROVE_TAC [extreal_cases] >> POP_ORW \\
     METIS_TAC [finite_second_moments_eq_integrable_squares])
 >> BETA_TAC >> Rewr'
 >> Suff `expectation p (\x. SIGMA (\(i,j). (X i x - expectation p (X i)) *
                                            (X j x - expectation p (X j))) B) = 0`
 >- (Rewr' >> REWRITE_TAC [add_rzero])
 (* LHS: applying integral_sum again *)
 >> Know `!x. (\(i,j). (X i x - expectation p (X i)) * (X j x - expectation p (X j))) =
              (\i. (X (FST i) x - expectation p (X (FST i))) *
                   (X (SND i) x - expectation p (X (SND i))))`
 >- (GEN_TAC >> RW_TAC std_ss [FUN_EQ_THM] \\
     Cases_on `i` >> SIMP_TAC std_ss [])
 >> Rewr'
 >> Know `expectation p (\x. SIGMA (\i. (\i x. (X (FST i) x - expectation p (X (FST i))) *
                                               (X (SND i) x - expectation p (X (SND i)))) i x) B) =
          SIGMA (\i. expectation p ((\i x. (X (FST i) x - expectation p (X (FST i))) *
                                           (X (SND i) x - expectation p (X (SND i)))) i)) B`
 >- (REWRITE_TAC [expectation_def] >> MATCH_MP_TAC integral_sum \\
    `B SUBSET (J CROSS J)` by ASM_SET_TAC [] \\
    `FINITE (J CROSS J)` by PROVE_TAC [FINITE_CROSS] \\
    `FINITE B` by PROVE_TAC [SUBSET_FINITE] \\
     ASM_SIMP_TAC std_ss [] \\
     CONJ_TAC >- FULL_SIMP_TAC std_ss [prob_space_def] \\
     reverse CONJ_TAC
     >- (rpt GEN_TAC >> STRIP_TAC \\
         Cases_on `i` >> FULL_SIMP_TAC std_ss [] \\
         Know `q IN J /\ r IN J`
         >- (CONJ_TAC >> `(q,r) IN (J CROSS J)` by PROVE_TAC [SUBSET_DEF] \\
             POP_ASSUM MP_TAC >> SIMP_TAC std_ss [IN_CROSS]) \\
         STRIP_TAC \\
         REWRITE_TAC [GSYM expectation_def] \\
         FULL_SIMP_TAC std_ss [p_space_def] \\
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
 >> MATCH_MP_TAC uncorrelated_thm
 >> PROVE_TAC []
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
(* Convergence Concepts and The Law(s) of Large Numbers (uncorrelated_rv)    *)
(* ========================================================================= *)

(* convergence modes *)
val _ = Datatype `convergence_mode = almost_everywhere   ('a p_space)
                                   | in_probability      ('a p_space)
                                   | in_lebesgue extreal ('a p_space)
                                   | in_distribution     ('a p_space)`;

(* convergence of extreal-valued random series [1, p.68,70], only works
   for real-valued random variables (cf. real_random_variable_def)
 *)
Definition converge_def[nocompute] :
   (* X(n) converges to Y (a.e.) *)
   (converge (X :num -> 'a -> extreal) (Y :'a -> extreal) (almost_everywhere p) =
    AE x::p. ((\n. X n x) --> Y x) sequentially) /\

   (* X(n) converges to Y (in pr.) *)
   (converge (X :num -> 'a -> extreal) (Y :'a -> extreal) (in_probability p) =
    !e. 0 < e /\ e <> PosInf ==>
        ((\n. prob p {x | x IN p_space p /\ e < abs (X n x - Y x)}) --> 0)
          sequentially) /\

   (* X(n) converges to Y (in L^r), assuming ‘0 < r /\ r <> PosInf’ *)
   (converge (X :num -> 'a -> extreal) (Y :'a -> extreal) (in_lebesgue r p) <=>
    (!n. X n IN lp_space r p) /\ Y IN lp_space r p /\
    ((\n. expectation p (\x. (abs (X n x - Y x)) powr r)) --> 0) sequentially) /\

   (* X(n) converges to Y in distribution (see [4, p.425] or [2, p.96]) *)
   (converge (X :num -> 'a -> extreal) (Y :'a -> extreal) (in_distribution p) =
    !f. f bounded_on UNIV /\ (f o Normal) continuous_on UNIV ==>
        ((\n. expectation p (f o (X n))) --> expectation p (f o Y)) sequentially)
End

(* "-->" was defined in util_probTheory for IN_DFUNSET *)
Overload "-->" = “converge”

(* |- !p X Y.
        (X --> Y) (almost_everywhere p) <=>
        AE x::p. ((\n. X n x) --> Y x) sequentially
 *)
Theorem converge_AE =
   (List.nth (CONJUNCTS converge_def, 0)) |> SPEC_ALL |> (Q.GENL [`p`, `X`, `Y`])

(* The old definition based on LIM_SEQUENTIALLY *)
Theorem converge_AE_def :
    !p X Y. (!n. real_random_variable (X n) p) /\ real_random_variable Y p ==>
            ((X --> Y) (almost_everywhere p) <=>
             AE x::p. ((\n. real (X n x)) --> real (Y x)) sequentially)
Proof
    rw [converge_AE, real_random_variable_def]
 >> HO_MATCH_MP_TAC AE_cong
 >> rw [GSYM p_space_def]
 >> HO_MATCH_MP_TAC (REWRITE_RULE [o_DEF] extreal_lim_sequentially_eq)
 >> rw []
QED

(* |- !p X Y.
        (X --> Y) (in_probability p) <=>
        !e. 0 < e /\ e <> PosInf ==>
            ((\n. prob p {x | x IN p_space p /\ e < abs (X n x - Y x)}) --> 0)
              sequentially
 *)
Theorem converge_PR =
   (List.nth (CONJUNCTS converge_def, 1)) |> SPEC_ALL |> (Q.GENL [`p`, `X`, `Y`])

(* The old definition based on LIM_SEQUENTIALLY *)
Theorem converge_PR_def :
    !p X Y. prob_space p /\
           (!n. real_random_variable (X n) p) /\ real_random_variable Y p ==>
           ((X --> Y) (in_probability p) <=>
            !e. 0 < e /\ e <> PosInf ==>
                ((\n. real (prob p {x | x IN p_space p /\ e < abs (X n x - Y x)})) -->
                 0) sequentially)
Proof
    rw [converge_PR, real_random_variable_def]
 >> Q.ABBREV_TAC ‘f = \n x. X n x - Y x’
 >> Know ‘!n. (f n) IN measurable (m_space p,measurable_sets p) Borel’
 >- (rw [Abbr ‘f’] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
     qexistsl_tac [‘X n’, ‘Y’] \\
     fs [prob_space_def, p_space_def, events_def, space_def,
         measure_space_def, random_variable_def])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘A = \e n. {x | x IN p_space p /\ e < abs (f n x)}’
 >> Know ‘!e n. A e n IN events p’
 >- (RW_TAC std_ss [Abbr ‘A’] \\
    ‘{x | x IN p_space p /\ e < abs (f n x)} =
        p_space p DIFF {x | x IN p_space p /\ abs (f n x) <= e}’
        by (RW_TAC set_ss [Once EXTENSION, GSYM extreal_lt_def] >> METIS_TAC []) >> POP_ORW \\
     MATCH_MP_TAC EVENTS_COMPL >> art [] \\
     REWRITE_TAC [abs_bounds] \\
    ‘{x | x IN p_space p /\ -e <= f n x /\ f n x <= e} =
     ({x | -e <= f n x} INTER p_space p) INTER ({x | f n x <= e} INTER p_space p)’
        by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC EVENTS_INTER >> fs [events_def, p_space_def] \\
    ‘sigma_algebra (measurable_space p)’ by fs [prob_space_def, measure_space_def] \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘g = \e n. prob p (A e n)’
 >> Know ‘!e. (\n. prob p {x | x IN p_space p /\ e < abs (X n x - Y x)}) = g e’
 >- rw [Abbr ‘A’, Abbr ‘g’, FUN_EQ_THM]
 >> Rewr'
 >> Know ‘!e. (\n. real (prob p {x | x IN p_space p /\ e < abs (X n x - Y x)})) = real o (g e)’
 >- rw [Abbr ‘A’, Abbr ‘g’, FUN_EQ_THM]
 >> Rewr'
 >> EQ_TAC >> rw []
 >> Q.PAT_X_ASSUM ‘!e. 0 < e /\ e <> PosInf ==> P’ (MP_TAC o (Q.SPEC ‘e’))
 >> RW_TAC std_ss [] (* 2 subgoals, same initial & ending tactics *)
 >| [ (* goal 1 (of 2) *)
      Suff ‘(g e --> 0) sequentially <=> (real o g e --> real 0) sequentially’
      >- rw [real_0],
      (* goal 2 (of 2) *)
      Suff ‘(g e --> 0) sequentially <=> (real o g e --> real 0) sequentially’
      >- fs [real_0] ]
 >> MATCH_MP_TAC extreal_lim_sequentially_eq >> rw []
 >> Q.EXISTS_TAC ‘0’ >> GEN_TAC >> simp [Abbr ‘g’]
 >> PROVE_TAC [PROB_FINITE]
QED

(* |- !p X Y r.
        (X --> Y) (in_lebesgue r p) <=>
        (!n. X n IN lp_space r p) /\ Y IN lp_space r p /\
        ((\n. expectation p (\x. abs (X n x - Y x) powr r)) --> 0)
          sequentially
 *)
Theorem converge_LP =
   (List.nth (CONJUNCTS converge_def, 2)) |> SPEC_ALL |> (Q.GENL [`p`, `X`, `Y`, `r`])

Theorem converge_LP_def :
    !p X Y r. prob_space p /\
             (!n. real_random_variable (X n) p) /\ real_random_variable Y p /\
              0 < r /\ r <> PosInf ==>
       ((X --> Y) (in_lebesgue r p) <=>
        (!n. X n IN lp_space r p) /\ Y IN lp_space r p /\
        ((\n. real (expectation p (\x. (abs (X n x - Y x)) powr r))) --> 0)
          sequentially)
Proof
    rw [converge_LP, real_random_variable, expectation_def, prob_space_def,
        p_space_def, events_def]
 >> EQ_TAC >> rw [lp_space_alt_finite']
 (* 2 subgoals, same initial & ending tactics *)
 >> ‘(!n. X n IN lp_space r p) /\ Y IN lp_space r p’
      by METIS_TAC [lp_space_alt_finite']
 >> ‘!n. (\x. X n x - Y x) IN lp_space r p’ by METIS_TAC [lp_space_sub]
 >> ‘!n. integral p (\x. abs (X n x - Y x) powr r) <> PosInf’
      by METIS_TAC [lp_space_alt_finite']
 >> Q.ABBREV_TAC ‘f = (\n. integral p (\x. abs (X n x - Y x) powr r))’
 >> ‘(\n. real (integral p (\x. abs (X n x - Y x) powr r))) = real o f’
      by rw [Abbr ‘f’, FUN_EQ_THM] >> fs []
 >| [ Suff ‘(f --> 0) sequentially <=> (real o f --> real 0) sequentially’
      >- rw [real_0],
      Suff ‘(f --> 0) sequentially <=> (real o f --> real 0) sequentially’
      >- fs [real_0] ]
 >> MATCH_MP_TAC extreal_lim_sequentially_eq >> rw []
 >> Q.EXISTS_TAC ‘0’ >> rw []
 >> MATCH_MP_TAC pos_not_neginf
 >> simp [Abbr ‘f’]
 >> MATCH_MP_TAC integral_pos >> rw [powr_pos]
QED

(* |- !p X Y.
        (X --> Y) (in_distribution p) <=>
        !f. f bounded_on univ(:extreal) /\
            f o Normal continuous_on univ(:real) ==>
            ((\n. expectation p (f o X n)) --> expectation p (f o Y))
              sequentially
 *)
Theorem converge_in_dist =
   (List.nth (CONJUNCTS converge_def, 3)) |> SPEC_ALL |> (Q.GENL [`p`, `X`, `Y`])

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

(* alternative definition of converge_LP based on absolute moment *)
Theorem converge_LP_alt_absolute_moment :
   !p X Y k. prob_space p /\ (!n. real_random_variable (X n) p) /\
             real_random_variable Y p /\ 0 < k ==>
       ((X --> Y) (in_lebesgue (&k :extreal) p) <=>
        (!n. expectation p (\x. (abs (X n x)) pow k) <> PosInf) /\
        (expectation p (\x. (abs (Y x)) pow k) <> PosInf) /\
        ((\n. real (absolute_moment p (\x. X n x - Y x) 0 k)) --> 0) sequentially)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘0 < &k /\ &k <> PosInf’ by rw [extreal_of_num_def, extreal_lt_eq, extreal_not_infty]
 >> rw [converge_LP_def, absolute_moment_def, sub_rzero, num_not_infty]
 >> fs [prob_space_def, p_space_def, events_def, real_random_variable]
 >> rw [lp_space_alt_finite', expectation_def]
 >> Know `!Z. 0 < k ==> abs Z powr &k = abs Z pow k`
 >- (rpt STRIP_TAC >> MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC gen_powr >> REWRITE_TAC [abs_pos])
 >> DISCH_TAC
 >> EQ_TAC >> rw []
QED

(* alternative definition of converge_LP using `pow k` explicitly;
   |- !p X Y k.
        prob_space p /\ (!n. real_random_variable (X n) p) /\
        real_random_variable Y p /\ 0 < k ==>
        ((X --> Y) (in_lebesgue (&k) p) <=>
         (!n. expectation p (\x. abs (X n x) pow k) <> PosInf) /\
         expectation p (\x. abs (Y x) pow k) <> PosInf /\
         ((\n. real (expectation p (\x. abs (X n x - Y x) pow k))) --> 0)
           sequentially)
 *)
Theorem converge_LP_alt_pow =
        SIMP_RULE std_ss [absolute_moment_def, sub_rzero]
                  converge_LP_alt_absolute_moment

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
    RW_TAC std_ss [converge_AE_def]
 >> fs [real_random_variable_def]
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
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
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
 >- (RW_TAC std_ss [AE_DEF, null_set_def, LIM_SEQUENTIALLY, dist] \\
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
         FULL_SIMP_TAC std_ss [p_space_def] \\
        ‘m_space p DIFF N SUBSET m_space p’ by SET_TAC [] \\
        ‘x IN m_space p’ by METIS_TAC [SUBSET_DEF] \\
        `?a. X n x = Normal a` by METIS_TAC [extreal_cases] \\
        `?b. Y x = Normal b` by METIS_TAC [extreal_cases] \\
         MATCH_MP_TAC lt_imp_le \\
         FULL_SIMP_TAC std_ss [real_normal, extreal_sub_def, extreal_abs_def, extreal_lt_eq]) \\
     DISCH_TAC \\
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
 >> RW_TAC std_ss [AE_DEF, null_set_def, LIM_SEQUENTIALLY, dist]
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
     Q.UNABBREV_TAC `B` >> METIS_TAC [])
 >> DISCH_TAC
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
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
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
            real_random_variable Y p /\
           (X --> Y) (almost_everywhere p) ==> (X --> Y) (in_probability p)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> POP_ASSUM MP_TAC
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
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
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
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
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

   Theorem 4.2.2 [1, p.77] (extended version), also see Borel_Cantelli_Lemma1.
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
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
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
 (* applying PROB_LIMSUP *)
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

(* Theorem 4.2.2 [1, p.77] (original version) *)
Theorem converge_AE_alt_limsup' :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) ==>
         ((X --> (\x. 0)) (almost_everywhere p) <=>
          !e. 0 < e /\ e <> PosInf ==>
              prob p (limsup (\n. {x | x IN p_space p /\ e < abs (X n x)})) = 0)
Proof
    rpt STRIP_TAC
 >> ‘real_random_variable (\x. 0) p’ by METIS_TAC [real_random_variable_zero]
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘\x. 0’] converge_AE_alt_limsup)
 >> RW_TAC std_ss [sub_rzero]
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
 >> Know ‘!n. real_random_variable (Z n) p’
 >- (RW_TAC std_ss [Abbr `Z`] \\
     MATCH_MP_TAC real_random_variable_sub >> art [])
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
 >> Know ‘!n. real_random_variable (Z n) p’
 >- (RW_TAC std_ss [Abbr `Z`] \\
     MATCH_MP_TAC real_random_variable_sub >> art [])
 >> DISCH_TAC
 >> RW_TAC std_ss [converge_PR_def, sub_rzero]
QED

Theorem converge_AE_imp_PR' :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) /\
         (X --> (\x. 0)) (almost_everywhere p) ==>
         (X --> (\x. 0)) (in_probability p)
Proof
    rpt STRIP_TAC
 >> irule converge_AE_imp_PR
 >> rw [real_random_variable_zero]
QED

(* Theorem 4.1.4 [2, p.71], for moments (integer-valued) only. *)
Theorem converge_LP_imp_PR' :
    !p X k. prob_space p /\ (!n. real_random_variable (X n) p) /\ 0 < k /\
            (X --> (\x. 0)) (in_lebesgue (&k :extreal) p) ==>
            (X --> (\x. 0)) (in_probability p)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> POP_ASSUM MP_TAC
 >> `real_random_variable (\x. 0) p` by PROVE_TAC [real_random_variable_zero]
 >> RW_TAC real_ss [converge_LP_alt_pow, converge_PR_def, LIM_SEQUENTIALLY,
                    dist, expectation_def, sub_rzero, REAL_SUB_RZERO]
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
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
 >- (Q.X_GEN_TAC ‘n’ \\
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
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS \\
     Q.EXISTS_TAC `X n` >> fs [measure_space_def])
 >> DISCH_TAC
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
 >> Know `!m x. x IN p_space p ==>
               (Normal E < abs (X m x) <=> Normal (E pow k) < abs (X m x) pow k)`
 >- (rpt STRIP_TAC \\
    `?r. X m x = Normal r` by METIS_TAC [extreal_cases] >> POP_ORW \\
     SIMP_TAC std_ss [extreal_abs_def, extreal_pow_def, extreal_lt_eq] \\
    `k <> 0` by RW_TAC arith_ss [] \\
     EQ_TAC >> STRIP_TAC
     >- (MATCH_MP_TAC REAL_POW_LT2 >> art [] \\
         MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
     SPOSE_NOT_THEN (ASSUME_TAC o (REWRITE_RULE [GSYM real_lte])) \\
    `abs r pow k <= E pow k` by METIS_TAC [POW_LE, ABS_POS] \\
     METIS_TAC [REAL_LTE_ANTISYM])
 >> DISCH_TAC
 >> Know ‘!m. {x | x IN p_space p /\ Normal E < abs (X m x)} =
              {x | x IN p_space p /\ Normal (E pow k) < abs (X m x) pow k}’
 >- (rw [Once EXTENSION] \\
     METIS_TAC [])
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
     >- rw [IN_MEASURABLE_BOREL_ALL_MEASURE] \\
    `!x. abs (X n x) = (\x. abs (X n x)) x` by METIS_TAC [] >> POP_ORW \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_POW \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS >> Q.EXISTS_TAC `X n` \\
     FULL_SIMP_TAC std_ss [measure_space_def])
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

Theorem converge_AE_cong_full :
    !p X Y A B m. (!n x. m <= n /\ x IN p_space p ==> X n x = Y n x) /\
                  (!x. x IN p_space p ==> A x = B x) ==>
                  ((X --> A) (almost_everywhere p) <=> (Y --> B) (almost_everywhere p))
Proof
    rw [p_space_def, converge_AE, AE_DEF, EXTREAL_LIM_SEQUENTIALLY]
 >> EQ_TAC >> rw []
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC ‘N’ >> rw [] \\
      Q.PAT_X_ASSUM ‘!x. x IN m_space p /\ x NOTIN N ==> P’ (MP_TAC o (Q.SPEC ‘x’)) \\
      rw [] >> POP_ASSUM (MP_TAC o (Q.SPEC ‘e’)) >> rw [] \\
      Q.EXISTS_TAC ‘MAX N' m’ >> rw [MAX_LE] \\
     ‘Y n x = X n x’ by METIS_TAC [] >> POP_ORW \\
      FIRST_X_ASSUM MATCH_MP_TAC >> art [],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC ‘N’ >> rw [] \\
      Q.PAT_X_ASSUM ‘!x. x IN m_space p /\ x NOTIN N ==> P’ (MP_TAC o (Q.SPEC ‘x’)) \\
      rw [] >> POP_ASSUM (MP_TAC o (Q.SPEC ‘e’)) >> rw [] \\
      Q.EXISTS_TAC ‘MAX N' m’ >> rw [MAX_LE] ]
QED

Theorem converge_AE_cong :
    !p X Y Z m. (!n x. m <= n /\ x IN p_space p ==> X n x = Y n x) ==>
                ((X --> Z) (almost_everywhere p) <=> (Y --> Z) (almost_everywhere p))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC converge_AE_cong_full
 >> Q.EXISTS_TAC ‘m’ >> rw []
QED

Theorem converge_PR_cong_full :
    !p X Y A B m. (!n x. m <= n /\ x IN p_space p ==> X n x = Y n x) /\
                  (!x. x IN p_space p ==> A x = B x) ==>
                  ((X --> A) (in_probability p) <=> (Y --> B) (in_probability p))
Proof
    rw [converge_PR, EXTREAL_LIM_SEQUENTIALLY]
 >> EQ_TAC >> rw []
 >| [ (* goal 1 (of 2) *)
      Q.PAT_X_ASSUM ‘!e. 0 < e /\ e <> PosInf ==> P’ (MP_TAC o (Q.SPEC ‘e’)) >> rw [] \\
      rename1 ‘0 < (E :real)’ \\
      POP_ASSUM (MP_TAC o (Q.SPEC ‘E’)) >> rw [] \\
      Q.EXISTS_TAC ‘MAX N m’ >> rw [MAX_LE] \\
      Know ‘{x | x IN p_space p /\ e < abs (Y n x - B x)} =
            {x | x IN p_space p /\ e < abs (X n x - A x)}’
      >- (rw [Once EXTENSION] \\
          EQ_TAC >> rw [] >> METIS_TAC []) >> Rewr' \\
      FIRST_X_ASSUM MATCH_MP_TAC >> art [],
      (* goal 2 (of 2) *)
      Q.PAT_X_ASSUM ‘!e. 0 < e /\ e <> PosInf ==> P’ (MP_TAC o (Q.SPEC ‘e’)) >> rw [] \\
      rename1 ‘0 < (E :real)’ \\
      POP_ASSUM (MP_TAC o (Q.SPEC ‘E’)) >> rw [] \\
      Q.EXISTS_TAC ‘MAX N m’ >> rw [MAX_LE] \\
      Know ‘{x | x IN p_space p /\ e < abs (X n x - A x)} =
            {x | x IN p_space p /\ e < abs (Y n x - B x)}’
      >- (rw [Once EXTENSION] \\
          EQ_TAC >> rw [] >> METIS_TAC []) >> Rewr' \\
      FIRST_X_ASSUM MATCH_MP_TAC >> art [] ]
QED

Theorem converge_PR_cong :
    !p X Y Z m. (!n x. m <= n /\ x IN p_space p ==> X n x = Y n x) ==>
                ((X --> Z) (in_probability p) <=> (Y --> Z) (in_probability p))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC converge_PR_cong_full
 >> Q.EXISTS_TAC ‘m’ >> rw []
QED

Theorem converge_LP_cong :
    !p X Y Z r. prob_space p /\ (!n x. x IN p_space p ==> X n x = Y n x) /\
                0 < r /\ r <> PosInf ==>
               ((X --> Z) (in_lebesgue r p) <=> (Y --> Z) (in_lebesgue r p))
Proof
    rw [converge_LP, EXTREAL_LIM_SEQUENTIALLY]
 >> EQ_TAC >> RW_TAC std_ss []
 >| [ (* goal 1 (of 4) *)
      Know ‘Y n IN lp_space r p <=> X n IN lp_space r p’
      >- (MATCH_MP_TAC lp_space_cong >> fs [prob_space_def, p_space_def]) \\
      DISCH_THEN (ASM_REWRITE_TAC o wrap),
      (* goal 2 (of 4) *)
      Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘e’)) >> rw [] \\
      Q.EXISTS_TAC ‘N’ >> rw [] \\
      Know ‘expectation p (\x. abs (Y n x - Z x) powr r) =
            expectation p (\x. abs (X n x - Z x) powr r)’
      >- (MATCH_MP_TAC expectation_cong >> rw []) >> Rewr' \\
      FIRST_X_ASSUM MATCH_MP_TAC >> art [],
      (* goal 3 (of 4) *)
      Know ‘X n IN lp_space r p <=> Y n IN lp_space r p’
      >- (MATCH_MP_TAC lp_space_cong >> fs [prob_space_def, p_space_def]) \\
      DISCH_THEN (ASM_REWRITE_TAC o wrap),
      (* goal 4 (of 4) *)
      Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘e’)) >> rw [] \\
      Q.EXISTS_TAC ‘N’ >> rw [] \\
      Know ‘expectation p (\x. abs (X n x - Z x) powr r) =
            expectation p (\x. abs (Y n x - Z x) powr r)’
      >- (MATCH_MP_TAC expectation_cong >> rw []) >> Rewr' \\
      FIRST_X_ASSUM MATCH_MP_TAC >> art [] ]
QED

(*
Theorem WLLN_uncorrelated_L2 :

    has been moved to examples/probability/large_numberTheory with improved statements.
 *)

Theorem converge_AE_to_zero' :
    !p X Y Z. prob_space p /\ (!n. real_random_variable (X n) p) /\
              real_random_variable Y p /\
             (!n x. x IN p_space p ==> Z n x = X n x - Y x) ==>
             ((X --> Y) (almost_everywhere p) <=> (Z --> (\x. 0)) (almost_everywhere p))
Proof
    rw [converge_AE_to_zero]
 >> MATCH_MP_TAC converge_AE_cong
 >> Q.EXISTS_TAC ‘0’ >> rw []
QED

Theorem converge_PR_to_zero' :
    !p X Y Z. prob_space p /\ (!n. real_random_variable (X n) p) /\
              real_random_variable Y p /\
             (!n x. x IN p_space p ==> Z n x = X n x - Y x) ==>
             ((X --> Y) (in_probability p) <=> (Z --> (\x. 0)) (in_probability p))
Proof
    rw [converge_PR_to_zero]
 >> MATCH_MP_TAC converge_PR_cong
 >> Q.EXISTS_TAC ‘0’ >> rw []
QED

Theorem converge_AE_alt_shift :
    !D p X Y. (X               --> Y) (almost_everywhere p) <=>
              ((\n. X (n + D)) --> Y) (almost_everywhere p)
Proof
    RW_TAC std_ss [converge_AE, AE_DEF, GSYM IN_NULL_SET, EXTREAL_LIM_SEQUENTIALLY]
 >> EQ_TAC >> rw [] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC ‘N’ >> RW_TAC std_ss [] \\
      Q.PAT_X_ASSUM `!x. x IN m_space p /\ x NOTIN N ==> P` (MP_TAC o (Q.SPEC `x`)) \\
      RW_TAC std_ss [] \\
      rename1 `z IN null_set p` \\
      Q.PAT_X_ASSUM `!e. 0 < e ==> P` (MP_TAC o (Q.SPEC `e`)) >> RW_TAC std_ss [] \\
      Q.EXISTS_TAC ‘N’ >> RW_TAC std_ss [] \\
      Q.PAT_X_ASSUM ‘!n. N <= n ==> P’ (MP_TAC o (Q.SPEC ‘D + n’)) >> rw [],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC `N` >> RW_TAC std_ss [] \\
      Q.PAT_X_ASSUM `!x. x IN m_space p /\ x NOTIN N ==> P` (MP_TAC o (Q.SPEC `x`)) \\
      RW_TAC std_ss [] \\
      rename1 `z IN null_set p` \\
      Q.PAT_X_ASSUM `!e. 0 < e ==> P` (MP_TAC o (Q.SPEC `e`)) >> RW_TAC std_ss [] \\
      Q.EXISTS_TAC `D + N` >> rpt STRIP_TAC \\
     ‘N <= n - D’ by rw [] \\
      Q.PAT_X_ASSUM ‘!n. N <= n ==> P’ (MP_TAC o (Q.SPEC ‘n - D’)) >> rw [] ]
QED

Theorem converge_PR_alt_shift :
    !D p X Y. (X               --> Y) (in_probability p) <=>
              ((\n. X (n + D)) --> Y) (in_probability p)
Proof
    RW_TAC std_ss [converge_PR, EXTREAL_LIM_SEQUENTIALLY]
 >> EQ_TAC >> RW_TAC std_ss [] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      rename1 `E <> PosInf` \\
      Q.PAT_X_ASSUM `!e. 0 < e /\ e <> PosInf ==> P` (MP_TAC o (Q.SPEC `E`)) \\
      RW_TAC std_ss [] \\
      rename1 `0 < e` (* this changes the last matching assumption *) \\
      Q.PAT_X_ASSUM `!e. 0 < e ==> P` (MP_TAC o (Q.SPEC `e`)) \\
      RW_TAC std_ss [] \\
      Q.EXISTS_TAC ‘N’ >> RW_TAC std_ss [] \\
      Q.PAT_X_ASSUM ‘!n. N <= n ==> P’ (MP_TAC o (Q.SPEC ‘n + D’)) \\
      RW_TAC arith_ss [],
      (* goal 2 (of 2) *)
      rename1 `E <> PosInf` \\
      Q.PAT_X_ASSUM `!e. 0 < e /\ e <> PosInf ==> P` (MP_TAC o (Q.SPEC `E`)) \\
      RW_TAC std_ss [] \\
      rename1 `0 < e` (* this changes the last matching assumption *) \\
      Q.PAT_X_ASSUM `!e. 0 < e ==> P` (MP_TAC o (Q.SPEC `e`)) \\
      RW_TAC std_ss [] \\
      Q.EXISTS_TAC ‘N + D’ >> RW_TAC std_ss [] \\
      ‘N <= n - D’ by rw [] \\
      Q.PAT_X_ASSUM ‘!n. N <= n ==> P’ (MP_TAC o (Q.SPEC ‘n - D’)) \\
      RW_TAC arith_ss [] ]
QED

(* |- !p X Y. ((\n. X (SUC n)) --> Y) (almost_everywhere p) ==>
              (X               --> Y) (almost_everywhere p)
 *)
Theorem converge_AE_shift =
        converge_AE_alt_shift |> (Q.SPECL [‘1’, ‘p’, ‘X’, ‘Y’])
                              |> (snd o EQ_IMP_RULE)
                              |> (REWRITE_RULE [GSYM ADD1])
                              |> Q.GENL [‘p’, ‘X’, ‘Y’]

(* |- !p X Y. ((\n. X (SUC n)) --> Y) (in_probability p) ==>
              (X               --> Y) (in_probability p)
 *)
Theorem converge_PR_shift =
        converge_PR_alt_shift |> (Q.SPECL [‘1’, ‘p’, ‘X’, ‘Y’])
                              |> (snd o EQ_IMP_RULE)
                              |> (REWRITE_RULE [GSYM ADD1])
                              |> Q.GENL [‘p’, ‘X’, ‘Y’]

Theorem converge_AE_const :
    !p c. prob_space p ==> ((\x n. c) --> (\x. c)) (almost_everywhere p)
Proof
    rw [converge_AE, EXTREAL_LIM_SEQUENTIALLY, AE_DEF, IN_NULL_SET, METRIC_SAME]
 >> Q.EXISTS_TAC ‘{}’
 >> fs [prob_space_def, NULL_SET_EMPTY]
QED

Theorem converge_AE_const' :
    !p X m c. prob_space p /\ (!n x. m <= n /\ x IN p_space p ==> X n x = c) ==>
             (X --> (\x. c)) (almost_everywhere p)
Proof
    rpt STRIP_TAC
 >> Know ‘(X         --> (\x. c)) (almost_everywhere p) <=>
          ((\n x. c) --> (\x. c)) (almost_everywhere p)’
 >- (MATCH_MP_TAC converge_AE_cong \\
     Q.EXISTS_TAC ‘m’ >> rw [])
 >> Rewr'
 >> MATCH_MP_TAC converge_AE_const >> art []
QED

Theorem converge_PR_add_to_zero :
    !p X Y. prob_space p /\
           (!n. real_random_variable (X n) p) /\
           (!n. real_random_variable (Y n) p) /\
           (X --> (\x. 0)) (in_probability p) /\
           (Y --> (\x. 0)) (in_probability p) ==>
       ((\n x. X n x + Y n x) --> (\x. 0)) (in_probability p)
Proof
    rpt STRIP_TAC
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> ‘real_random_variable (\x. 0) p’ by PROVE_TAC [real_random_variable_zero]
 >> Know ‘!n. real_random_variable (\x. X n x + Y n x) p’
 >- (Q.X_GEN_TAC ‘n’ \\
     MP_TAC (Q.SPECL [‘p’, ‘X (n :num)’, ‘Y (n :num)’] real_random_variable_add) \\
     rw [])
 >> DISCH_TAC
 >> rw [converge_PR_def, LIM_SEQUENTIALLY, dist]
 >> rename1 ‘0 < (E :real)’ (* the last assumption with ‘e'’ is affected *)
 >> ‘e <> NegInf’ by PROVE_TAC [pos_not_neginf, lt_imp_le]
 >> Know `0 < e / 2`
 >- (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites
                     [extreal_of_num_def] \\
     MATCH_MP_TAC lt_div >> RW_TAC real_ss [])
 >> DISCH_TAC
 >> Know ‘e / 2 <> PosInf’
 >- (‘?r. e = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_of_num_def, extreal_not_infty, extreal_div_eq, GSYM ne_02])
 >> DISCH_TAC
 >> Know ‘0 < E / 2’
 >- (MATCH_MP_TAC REAL_LT_DIV >> rw [])
 >> DISCH_TAC
 >> NTAC 2 (Q.PAT_X_ASSUM ‘!e. 0 < e /\ e <> PosInf ==> P’ (MP_TAC o (Q.SPEC ‘e / 2’)))
 >> RW_TAC std_ss []
 >> NTAC 2 (Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘E / 2’)))
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC ‘MAX N N'’
 >> rw [MAX_LE]
 >> NTAC 2 (Q.PAT_X_ASSUM ‘!n. _ <= n ==> P’ (MP_TAC o (Q.SPEC ‘n’)))
 >> RW_TAC std_ss []
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
 (* stage work *)
 >> Know `!Z b. real_random_variable Z p ==>
                {x | x IN p_space p /\ b < abs (Z x)} IN events p`
 >- (rpt GEN_TAC >> DISCH_TAC \\
    `{x | x IN p_space p /\ b < abs (Z x)} =
      p_space p DIFF {x | x IN p_space p /\ abs (Z x) <= b}`
        by (RW_TAC set_ss [Once EXTENSION, GSYM extreal_lt_def] \\
            METIS_TAC []) >> POP_ORW \\
     MATCH_MP_TAC EVENTS_COMPL >> art [abs_bounds] \\
    `{x | x IN p_space p /\ -b <= Z x /\ Z x <= b} =
     ({x | -b <= Z x} INTER p_space p) INTER ({x | Z x <= b} INTER p_space p)`
        by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC EVENTS_INTER \\
     fs [real_random_variable, events_def, p_space_def] \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘A = {x | x IN p_space p /\ e / 2 < abs (X n x)}’
 >> Q.ABBREV_TAC ‘B = {x | x IN p_space p /\ e / 2 < abs (Y n x)}’
 (* simplify X-related assumptions *)
 >> Know ‘A IN events p’
 >- (Q.UNABBREV_TAC ‘A’ >> FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> DISCH_TAC
 >> Know `abs (real (prob p A)) = real (prob p A)`
 >- (‘prob p A <> PosInf /\ prob p A <> NegInf’ by METIS_TAC [PROB_FINITE] \\
     ASM_SIMP_TAC std_ss [ABS_REFL, GSYM extreal_le_eq, normal_real,
                          GSYM extreal_of_num_def] \\
     MATCH_MP_TAC PROB_POSITIVE >> rw [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> `real (prob p A) < E / 2 <=> prob p A < Normal (E / 2)`
       by (METIS_TAC [PROB_FINITE, normal_real, extreal_lt_eq])
 >> POP_ASSUM (FULL_SIMP_TAC std_ss o wrap)
 (* simplify Y-related assumptions *)
 >> Know ‘B IN events p’
 >- (Q.UNABBREV_TAC ‘B’ >> FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> DISCH_TAC
 >> Know `abs (real (prob p B)) = real (prob p B)`
 >- (‘prob p B <> PosInf /\ prob p B <> NegInf’ by METIS_TAC [PROB_FINITE] \\
     ASM_SIMP_TAC std_ss [ABS_REFL, GSYM extreal_le_eq, normal_real,
                          GSYM extreal_of_num_def] \\
     MATCH_MP_TAC PROB_POSITIVE >> rw [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> `real (prob p B) < E / 2 <=> prob p B < Normal (E / 2)`
       by (METIS_TAC [PROB_FINITE, normal_real, extreal_lt_eq])
 >> POP_ASSUM (FULL_SIMP_TAC std_ss o wrap)
 >> ‘A UNION B IN events p’ by PROVE_TAC [EVENTS_UNION]
 (* simplify goal *)
 >> Know ‘!n. real_random_variable (\x. X n x + Y n x) p’
 >- (Q.X_GEN_TAC ‘i’ \\
     MATCH_MP_TAC real_random_variable_add >> art[])
 >> DISCH_TAC
 >> Know ‘{x | x IN p_space p /\ e < abs (X n x + Y n x)} IN events p’
 >- (FIRST_X_ASSUM HO_MATCH_MP_TAC >> art [])
 >> DISCH_TAC
 >> Know ‘abs (real (prob p {x | x IN p_space p /\ e < abs (X n x + Y n x)})) =
              (real (prob p {x | x IN p_space p /\ e < abs (X n x + Y n x)}))’
 >- (‘prob p {x | x IN p_space p /\ e < abs (X n x + Y n x)} <> PosInf /\
      prob p {x | x IN p_space p /\ e < abs (X n x + Y n x)} <> NegInf’
        by METIS_TAC [PROB_FINITE] \\
     ASM_SIMP_TAC std_ss [ABS_REFL, GSYM extreal_le_eq, normal_real,
                          GSYM extreal_of_num_def] \\
     MATCH_MP_TAC PROB_POSITIVE >> rw [])
 >> Rewr'
 >> ‘real (prob p {x | x IN p_space p /\ e < abs (X n x + Y n x)}) < E <=>
           prob p {x | x IN p_space p /\ e < abs (X n x + Y n x)} < Normal E’
      by (METIS_TAC [PROB_FINITE, normal_real, extreal_lt_eq])
 >> POP_ORW
 (* final stage *)
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC ‘prob p (A UNION B)’
 >> CONJ_TAC
 >- (MATCH_MP_TAC PROB_INCREASING \\
     rw [Abbr ‘A’, Abbr ‘B’, SUBSET_DEF] \\
     SPOSE_NOT_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [extreal_lt_def])) \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
     Know ‘abs (X n x + Y n x) <= e / 2 + e / 2’
     >- (MATCH_MP_TAC le_trans \\
         Q.EXISTS_TAC ‘abs (X n x) + abs (Y n x)’ \\
         CONJ_TAC >- (MATCH_MP_TAC abs_triangle >> rw []) \\
         MATCH_MP_TAC le_add2 >> art []) \\
     Suff ‘e / 2 + e / 2 = e’ >- rw [GSYM extreal_lt_def] \\
     REWRITE_TAC [half_double])
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC ‘prob p A + prob p B’
 >> CONJ_TAC
 >- (MATCH_MP_TAC PROB_SUBADDITIVE >> art [])
 >> Suff ‘Normal E = Normal (E / 2) + Normal (E / 2)’
 >- (Rewr' >> MATCH_MP_TAC lt_add2 >> art [])
 >> rw [extreal_add_def]
 >> REWRITE_TAC [REAL_HALF_DOUBLE]
QED

Theorem converge_PR_add :
    !p X Y A B. prob_space p /\
               (!n. real_random_variable (X n) p) /\
                real_random_variable A p /\ (X --> A) (in_probability p) /\
               (!n. real_random_variable (Y n) p) /\
                real_random_variable B p /\ (Y --> B) (in_probability p) ==>
       ((\n x. X n x + Y n x) --> (\x. A x + B x)) (in_probability p)
Proof
    rpt STRIP_TAC
 >> Know ‘(X --> A) (in_probability p) <=>
          ((\n x. X n x - A x) --> (\x. 0)) (in_probability p)’
 >- (MATCH_MP_TAC converge_PR_to_zero >> art [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> Know ‘(Y --> B) (in_probability p) <=>
          ((\n x. Y n x - B x) --> (\x. 0)) (in_probability p)’
 >- (MATCH_MP_TAC converge_PR_to_zero >> art [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> Know ‘((\n x. X n x + Y n x) --> (\x. A x + B x)) (in_probability p) <=>
          ((\n x. X n x + Y n x - (A x + B x)) --> (\x. 0)) (in_probability p)’
 >- (MATCH_MP_TAC converge_PR_to_zero' >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC real_random_variable_add >> art [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC real_random_variable_add >> art [] ])
 >> Rewr'
 >> Know ‘((\n x. (X n x - A x) + (Y n x - B x)) --> (\x. 0)) (in_probability p)’
 >- (HO_MATCH_MP_TAC converge_PR_add_to_zero >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC real_random_variable_sub >> art [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC real_random_variable_sub >> art [] ])
 >> DISCH_TAC
 >> Suff ‘((\n x. X n x + Y n x - (A x + B x)) --> (\x. 0)) (in_probability p) <=>
          ((\n x. X n x - A x + (Y n x - B x)) --> (\x. 0)) (in_probability p)’
 >- DISCH_THEN (art o wrap)
 >> MATCH_MP_TAC converge_PR_cong
 >> Q.EXISTS_TAC ‘0’ >> RW_TAC arith_ss []
 >> FULL_SIMP_TAC std_ss [real_random_variable_def]
 >> ‘?a. X n x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> ‘?b. Y n x = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> ‘?c. A x = Normal c’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> ‘?d. B x = Normal d’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> rw [extreal_add_def, extreal_sub_def, extreal_11]
 >> REAL_ARITH_TAC
QED

Theorem converge_PR_ainv_to_zero :
    !p X. (X --> (\x. 0)) (in_probability p) ==>
          ((\n x. -X n x) --> (\x. 0)) (in_probability p)
Proof
    rw [converge_PR, EXTREAL_LIM_SEQUENTIALLY]
QED

Theorem converge_PR_ainv :
    !p X Y. prob_space p /\ (!n. real_random_variable (X n) p) /\
            real_random_variable Y p /\
            (X --> Y) (in_probability p) ==>
         ((\n x. -X n x) --> (\x. -Y x)) (in_probability p)
Proof
    rpt STRIP_TAC
 >> Know ‘(X --> Y) (in_probability p) <=>
          ((\n x. X n x - Y x) --> (\x. 0)) (in_probability p)’
 >- (MATCH_MP_TAC converge_PR_to_zero >> art [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> Know ‘((\n x. -X n x) --> (\x. -Y x)) (in_probability p) <=>
          ((\n x. (\n x. -X n x) n x - (\x. -Y x) x) --> (\x. 0)) (in_probability p)’
 >- (MATCH_MP_TAC converge_PR_to_zero >> rw [] >| (* 2 subgoals *)
     [ MATCH_MP_TAC real_random_variable_ainv >> art [],
       MATCH_MP_TAC real_random_variable_ainv >> art [] ])
 >> Rewr'
 >> BETA_TAC
 >> Know ‘((\n x. -X n x - -Y x) --> (\x. 0)) (in_probability p) <=>
          ((\n x. -(X n x - Y x)) --> (\x. 0)) (in_probability p)’
 >- (MATCH_MP_TAC converge_PR_cong \\
     Q.EXISTS_TAC ‘0’ >> RW_TAC arith_ss [] \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
    ‘?a. X n x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?b. Y x = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_ainv_def, extreal_sub_def] \\
     REAL_ARITH_TAC)
 >> Rewr'
 >> HO_MATCH_MP_TAC converge_PR_ainv_to_zero >> rw []
 >> MATCH_MP_TAC real_random_variable_sub >> art []
QED

Theorem converge_PR_sub :
    !p X Y A B. prob_space p /\
               (!n. real_random_variable (X n) p) /\
                real_random_variable A p /\ (X --> A) (in_probability p) /\
               (!n. real_random_variable (Y n) p) /\
                real_random_variable B p /\ (Y --> B) (in_probability p) ==>
       ((\n x. X n x - Y n x) --> (\x. A x - B x)) (in_probability p)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘\n x. -Y n x’, ‘A’, ‘\x. -B x’] converge_PR_add)
 >> BETA_TAC >> art []
 >> Know ‘((\n x. X n x + -Y n x) --> (\x. A x + -B x)) (in_probability p) <=>
          ((\n x. X n x - Y n x) --> (\x. A x - B x)) (in_probability p)’
 >- (MATCH_MP_TAC converge_PR_cong_full \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
     Q.EXISTS_TAC ‘0’ >> RW_TAC arith_ss [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
      ‘?a. X n x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
      ‘?b. Y n x = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
       rw [extreal_ainv_def, extreal_add_def, extreal_sub_def] \\
       REAL_ARITH_TAC,
       (* goal 2 (of 2) *)
      ‘?c. A x = Normal c’ by METIS_TAC [extreal_cases] >> POP_ORW \\
      ‘?d. B x = Normal d’ by METIS_TAC [extreal_cases] >> POP_ORW \\
       rw [extreal_ainv_def, extreal_add_def, extreal_sub_def] \\
       REAL_ARITH_TAC ])
 >> Rewr'
 >> Know ‘!n. real_random_variable (\x. -Y n x) p’
 >- (GEN_TAC >> MATCH_MP_TAC real_random_variable_ainv >> art [])
 >> Know ‘real_random_variable (\x. -B x) p’
 >- (MATCH_MP_TAC real_random_variable_ainv >> art [])
 >> Know ‘((\n x. -Y n x) --> (\x. -B x)) (in_probability p)’
 >- (MATCH_MP_TAC converge_PR_ainv >> art [])
 >> RW_TAC std_ss []
QED

Theorem converge_PR_to_limit :
    !p X M m. prob_space p /\ (!n. real_random_variable (X n) p) /\
              (M --> m) sequentially /\
              ((\n x. X n x - Normal (M n)) --> (\x. 0)) (in_probability p) ==>
              (X --> (\x. Normal m)) (in_probability p)
Proof
    rpt STRIP_TAC
 (* applying converge_PR_cong_full *)
 >> Know ‘(X --> (\x. Normal m)) (in_probability p) <=>
          ((\n x. X n x - Normal (M n) + Normal (M n)) --> (\x. 0 + Normal m))
           (in_probability p)’
 >- (MATCH_MP_TAC converge_PR_cong_full \\
     Q.EXISTS_TAC ‘0’ >> rw [sub_add_normal]) >> Rewr'
 >> HO_MATCH_MP_TAC converge_PR_add
 >> rw [real_random_variable_zero, real_random_variable_const]
 >- (HO_MATCH_MP_TAC real_random_variable_sub \\
     rw [real_random_variable_const] \\
    ‘(\x. X n x) = X n’ by METIS_TAC [] >> POP_ASSUM (art o wrap))
 >> Q.PAT_X_ASSUM ‘!n. real_random_variable (X n) p’ K_TAC
 >> POP_ASSUM K_TAC (* (X n x - M n) --> 0 *)
 (* stage work, now ‘X n’ disappeared, left only M and m *)
 >> POP_ASSUM MP_TAC
 >> rw [converge_PR, EXTREAL_LIM_SEQUENTIALLY, LIM_SEQUENTIALLY, dist]
 >> ‘e <> NegInf’ by PROVE_TAC [lt_imp_le, pos_not_neginf]
 >> rename1 ‘0 < (z :real)’
 >> ‘?E. e = Normal E /\ 0 < E’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq]
 >> Q.PAT_X_ASSUM ‘!e. 0 < e ==> ?N. P’ (MP_TAC o Q.SPEC ‘E’)
 >> RW_TAC std_ss [extreal_sub_def, extreal_abs_def, extreal_lt_eq]
 >> Q.EXISTS_TAC ‘N’
 >> rpt STRIP_TAC
 >> Suff ‘{x | x IN p_space p /\ E < abs (M n - m)} = {}’
 >- rw [PROB_EMPTY, METRIC_SAME]
 >> rw [Once EXTENSION, GSYM real_lte, NOT_IN_EMPTY]
 >> DISJ2_TAC
 >> MATCH_MP_TAC REAL_LT_IMP_LE
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

(* M and m are extreal-valued. This form is used by WLLN_IID directly. *)
Theorem converge_PR_to_limit' :
    !p X M m. prob_space p /\ (!n. real_random_variable (X n) p) /\
              (!n. M n <> PosInf /\ M n <> NegInf) /\ m <> PosInf /\ m <> NegInf /\
              ((real o M) --> real m) sequentially /\
              ((\n x. X n x - M n) --> (\x. 0)) (in_probability p) ==>
              (X --> (\x. m)) (in_probability p)
Proof
    rpt STRIP_TAC
 >> ‘?r. m = Normal r’ by METIS_TAC [extreal_cases] >> fs []
 >> MATCH_MP_TAC converge_PR_to_limit
 >> Q.EXISTS_TAC ‘real o M’ >> art []
 >> Suff ‘((\n x. X n x - Normal ((real o M) n)) --> (\x. 0)) (in_probability p) <=>
          ((\n x. X n x - M n) --> (\x. 0)) (in_probability p)’ >- rw []
 >> MATCH_MP_TAC converge_PR_cong
 >> Q.EXISTS_TAC ‘0’ >> rw [normal_real]
QED

Theorem converge_AE_add_to_zero :
    !p X Y. prob_space p /\
           (!n. real_random_variable (X n) p) /\
           (!n. real_random_variable (Y n) p) /\
           (X --> (\x. 0)) (almost_everywhere p) /\
           (Y --> (\x. 0)) (almost_everywhere p) ==>
       ((\n x. X n x + Y n x) --> (\x. 0)) (almost_everywhere p)
Proof
    rpt STRIP_TAC
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> ‘real_random_variable (\x. 0) p’ by PROVE_TAC [real_random_variable_zero]
 >> Know ‘!n. real_random_variable (\x. X n x + Y n x) p’
 >- (Q.X_GEN_TAC ‘n’ \\
     MP_TAC (Q.SPECL [‘p’, ‘X (n :num)’, ‘Y (n :num)’] real_random_variable_add) \\
     rw [])
 >> DISCH_TAC
 >> rw [converge_AE_def, AE_DEF, LIM_SEQUENTIALLY, dist, p_space_def]
 >> Q.EXISTS_TAC ‘N UNION N'’
 >> STRONG_CONJ_TAC
 >- (MATCH_MP_TAC (REWRITE_RULE [IN_APP] NULL_SET_UNION) \\
     FULL_SIMP_TAC std_ss [prob_space_def])
 >> rw []
 >> Q.PAT_X_ASSUM ‘!x. x IN m_space p /\ x NOTIN N ==> P’ (MP_TAC o (Q.SPEC ‘x’))
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM ‘!x. x IN m_space p /\ x NOTIN N' ==> P’ (MP_TAC o (Q.SPEC ‘x’))
 >> RW_TAC std_ss []
 >> ‘0 < e / 2’ by rw [REAL_LT_DIV]
 >> Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘e / 2’))
 >> RW_TAC std_ss []
 >> rename1 ‘!n. N1 <= n ==> abs (real (Y n x)) < e / 2’
 >> Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘e / 2’))
 >> RW_TAC std_ss []
 >> rename1 ‘!n. N2 <= n ==> abs (real (X n x)) < e / 2’
 >> Q.EXISTS_TAC ‘MAX N1 N2’
 >> rw [MAX_LE]
 >> Q.PAT_X_ASSUM ‘!n. N1 <= n ==> P’ (MP_TAC o (Q.SPEC ‘n’))
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM ‘!n. N2 <= n ==> P’ (MP_TAC o (Q.SPEC ‘n’))
 >> RW_TAC std_ss []
 >> FULL_SIMP_TAC std_ss [real_random_variable_def, p_space_def]
 >> ‘?a. X n x = Normal a’ by METIS_TAC [extreal_cases]
 >> POP_ASSUM (FULL_SIMP_TAC std_ss o wrap)
 >> ‘?b. Y n x = Normal b’ by METIS_TAC [extreal_cases]
 >> POP_ASSUM (FULL_SIMP_TAC std_ss o wrap)
 >> FULL_SIMP_TAC std_ss [extreal_add_def, real_normal]
 >> MATCH_MP_TAC REAL_LET_TRANS
 >> Q.EXISTS_TAC ‘abs a + abs b’
 >> REWRITE_TAC [ABS_TRIANGLE]
 >> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM REAL_HALF_DOUBLE]
 >> MATCH_MP_TAC REAL_LT_ADD2 >> art []
QED

Theorem converge_AE_add :
    !p X Y A B. prob_space p /\
               (!n. real_random_variable (X n) p) /\
                real_random_variable A p /\ (X --> A) (almost_everywhere p) /\
               (!n. real_random_variable (Y n) p) /\
                real_random_variable B p /\ (Y --> B) (almost_everywhere p) ==>
       ((\n x. X n x + Y n x) --> (\x. A x + B x)) (almost_everywhere p)
Proof
    rpt STRIP_TAC
 >> Know ‘(X --> A) (almost_everywhere p) <=>
          ((\n x. X n x - A x) --> (\x. 0)) (almost_everywhere p)’
 >- (MATCH_MP_TAC converge_AE_to_zero >> art [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> Know ‘(Y --> B) (almost_everywhere p) <=>
          ((\n x. Y n x - B x) --> (\x. 0)) (almost_everywhere p)’
 >- (MATCH_MP_TAC converge_AE_to_zero >> art [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> Know ‘((\n x. X n x + Y n x) --> (\x. A x + B x)) (almost_everywhere p) <=>
          ((\n x. X n x + Y n x - (A x + B x)) --> (\x. 0)) (almost_everywhere p)’
 >- (MATCH_MP_TAC converge_AE_to_zero' >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC real_random_variable_add >> art [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC real_random_variable_add >> art [] ])
 >> Rewr'
 >> Know ‘((\n x. (X n x - A x) + (Y n x - B x)) --> (\x. 0)) (almost_everywhere p)’
 >- (HO_MATCH_MP_TAC converge_AE_add_to_zero >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC real_random_variable_sub >> art [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC real_random_variable_sub >> art [] ])
 >> DISCH_TAC
 >> Suff ‘((\n x. X n x + Y n x - (A x + B x)) --> (\x. 0)) (almost_everywhere p) <=>
          ((\n x. X n x - A x + (Y n x - B x)) --> (\x. 0)) (almost_everywhere p)’
 >- DISCH_THEN (art o wrap)
 >> MATCH_MP_TAC converge_AE_cong
 >> Q.EXISTS_TAC ‘0’ >> RW_TAC arith_ss []
 >> FULL_SIMP_TAC std_ss [real_random_variable_def]
 >> ‘?a. X n x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> ‘?b. Y n x = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> ‘?c. A x = Normal c’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> ‘?d. B x = Normal d’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> rw [extreal_add_def, extreal_sub_def, extreal_11]
 >> REAL_ARITH_TAC
QED

Theorem converge_AE_ainv_to_zero :
    !p X. (!n. real_random_variable (X n) p) /\
          (X --> (\x. 0)) (almost_everywhere p) ==>
          ((\n x. -X n x) --> (\x. 0)) (almost_everywhere p)
Proof
    rw [converge_AE, AE_DEF, EXTREAL_LIM_SEQUENTIALLY,
        real_random_variable_def, p_space_def]
 >> Q.EXISTS_TAC ‘N’ >> rw []
 >> Q.PAT_X_ASSUM ‘!x. x IN m_space p /\ x NOTIN N ==> P’ (MP_TAC o (Q.SPEC ‘x’))
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘e’))
 >> RW_TAC std_ss []
 >> rename1 ‘!n. M <= n ==> dist extreal_mr1 (X n x,0) < e’
 >> Q.EXISTS_TAC ‘M’ >> rw []
 >> Q.PAT_X_ASSUM ‘!n. M <= n ==> P’ (MP_TAC o (Q.SPEC ‘n’))
 >> RW_TAC std_ss []
 >> POP_ASSUM MP_TAC (* dist extreal_mr1 (X n x,0) < e *)
 >> ‘?r. X n x = Normal r’ by METIS_TAC [extreal_cases]
 >> POP_ORW
 >> ‘0 = Normal 0’ by rw [extreal_of_num_def]
 >> POP_ORW
 >> rw [extreal_ainv_def, extreal_mr1_normal]
QED

Theorem converge_AE_ainv :
    !p X Y. prob_space p /\ (!n. real_random_variable (X n) p) /\
            real_random_variable Y p /\
            (X --> Y) (almost_everywhere p) ==>
         ((\n x. -X n x) --> (\x. -Y x)) (almost_everywhere p)
Proof
    rpt STRIP_TAC
 >> Know ‘(X --> Y) (almost_everywhere p) <=>
          ((\n x. X n x - Y x) --> (\x. 0)) (almost_everywhere p)’
 >- (MATCH_MP_TAC converge_AE_to_zero >> art [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> Know ‘((\n x. -X n x) --> (\x. -Y x)) (almost_everywhere p) <=>
          ((\n x. (\n x. -X n x) n x - (\x. -Y x) x) --> (\x. 0)) (almost_everywhere p)’
 >- (MATCH_MP_TAC converge_AE_to_zero >> rw [] >| (* 2 subgoals *)
     [ MATCH_MP_TAC real_random_variable_ainv >> art [],
       MATCH_MP_TAC real_random_variable_ainv >> art [] ])
 >> Rewr'
 >> BETA_TAC
 >> Know ‘((\n x. -X n x - -Y x) --> (\x. 0)) (almost_everywhere p) <=>
          ((\n x. -(X n x - Y x)) --> (\x. 0)) (almost_everywhere p)’
 >- (MATCH_MP_TAC converge_AE_cong \\
     Q.EXISTS_TAC ‘0’ >> RW_TAC arith_ss [] \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
    ‘?a. X n x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?b. Y x = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_ainv_def, extreal_sub_def] \\
     REAL_ARITH_TAC)
 >> Rewr'
 >> HO_MATCH_MP_TAC converge_AE_ainv_to_zero >> rw []
 >> MATCH_MP_TAC real_random_variable_sub >> art []
QED

Theorem converge_AE_sub :
    !p X Y A B. prob_space p /\
               (!n. real_random_variable (X n) p) /\
                real_random_variable A p /\ (X --> A) (almost_everywhere p) /\
               (!n. real_random_variable (Y n) p) /\
                real_random_variable B p /\ (Y --> B) (almost_everywhere p) ==>
       ((\n x. X n x - Y n x) --> (\x. A x - B x)) (almost_everywhere p)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘\n x. -Y n x’, ‘A’, ‘\x. -B x’] converge_AE_add)
 >> BETA_TAC >> art []
 >> Know ‘((\n x. X n x + -Y n x) --> (\x. A x + -B x)) (almost_everywhere p) <=>
          ((\n x. X n x - Y n x) --> (\x. A x - B x)) (almost_everywhere p)’
 >- (MATCH_MP_TAC converge_AE_cong_full \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
     Q.EXISTS_TAC ‘0’ >> RW_TAC arith_ss [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
      ‘?a. X n x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
      ‘?b. Y n x = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
       rw [extreal_ainv_def, extreal_add_def, extreal_sub_def] \\
       REAL_ARITH_TAC,
       (* goal 2 (of 2) *)
      ‘?c. A x = Normal c’ by METIS_TAC [extreal_cases] >> POP_ORW \\
      ‘?d. B x = Normal d’ by METIS_TAC [extreal_cases] >> POP_ORW \\
       rw [extreal_ainv_def, extreal_add_def, extreal_sub_def] \\
       REAL_ARITH_TAC ])
 >> Rewr'
 >> Know ‘!n. real_random_variable (\x. -Y n x) p’
 >- (GEN_TAC >> MATCH_MP_TAC real_random_variable_ainv >> art [])
 >> Know ‘real_random_variable (\x. -B x) p’
 >- (MATCH_MP_TAC real_random_variable_ainv >> art [])
 >> Know ‘((\n x. -Y n x) --> (\x. -B x)) (almost_everywhere p)’
 >- (MATCH_MP_TAC converge_AE_ainv >> art [])
 >> RW_TAC std_ss []
QED

Theorem converge_AE_to_limit :
    !p X M m. prob_space p /\ (!n. real_random_variable (X n) p) /\
              (M --> m) sequentially /\
              ((\n x. X n x - Normal (M n)) --> (\x. 0)) (almost_everywhere p) ==>
              (X --> (\x. Normal m)) (almost_everywhere p)
Proof
    rpt STRIP_TAC
 (* applying converge_PR_cong_full *)
 >> Know ‘(X --> (\x. Normal m)) (almost_everywhere p) <=>
          ((\n x. X n x - Normal (M n) + Normal (M n)) --> (\x. 0 + Normal m))
           (almost_everywhere p)’
 >- (MATCH_MP_TAC converge_AE_cong_full \\
     Q.EXISTS_TAC ‘0’ >> rw [sub_add_normal]) >> Rewr'
 >> HO_MATCH_MP_TAC converge_AE_add
 >> rw [real_random_variable_zero, real_random_variable_const]
 >- (HO_MATCH_MP_TAC real_random_variable_sub \\
     rw [real_random_variable_const] \\
    ‘(\x. X n x) = X n’ by METIS_TAC [] >> POP_ASSUM (art o wrap))
 >> Q.PAT_X_ASSUM ‘!n. real_random_variable (X n) p’ K_TAC
 >> POP_ASSUM K_TAC (* (X n x - M n) --> 0 *)
 (* stage work, now ‘X n’ disappeared, left only M and m *)
 >> POP_ASSUM MP_TAC
 >> qabbrev_tac ‘X = \n x. Normal (M n)’
 >> qabbrev_tac ‘Y = \x. Normal m’
 >> Know ‘(!n. real_random_variable (X n) p) /\ real_random_variable Y p’
 >- (rw [real_random_variable, Abbr ‘X’, Abbr ‘Y’] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST' \\
     fs [prob_space_def, measure_space_def, p_space_def, events_def])
 >> STRIP_TAC
 >> rw [converge_AE_def, AE_DEF, null_set_def, LIM_SEQUENTIALLY, dist]
 >> Q.EXISTS_TAC ‘{}’
 >> FULL_SIMP_TAC std_ss [prob_space_def]
 >> ASM_SIMP_TAC std_ss [MEASURE_SPACE_EMPTY_MEASURABLE, MEASURE_EMPTY]
 >> rw [Abbr ‘X’, Abbr ‘Y’]
QED

(* M and m are extreal-valued. This form is used by WLLN_IID directly. *)
Theorem converge_AE_to_limit' :
    !p X M m. prob_space p /\ (!n. real_random_variable (X n) p) /\
              (!n. M n <> PosInf /\ M n <> NegInf) /\ m <> PosInf /\ m <> NegInf /\
              ((real o M) --> real m) sequentially /\
              ((\n x. X n x - M n) --> (\x. 0)) (almost_everywhere p) ==>
              (X --> (\x. m)) (almost_everywhere p)
Proof
    rpt STRIP_TAC
 >> ‘?r. m = Normal r’ by METIS_TAC [extreal_cases] >> fs []
 >> MATCH_MP_TAC converge_AE_to_limit
 >> Q.EXISTS_TAC ‘real o M’ >> art []
 >> Suff ‘((\n x. X n x - Normal ((real o M) n)) --> (\x. 0)) (almost_everywhere p) <=>
          ((\n x. X n x - M n) --> (\x. 0)) (almost_everywhere p)’ >- rw []
 >> MATCH_MP_TAC converge_AE_cong
 >> Q.EXISTS_TAC ‘0’ >> rw [normal_real]
QED

(* ========================================================================= *)
(*                  Advanced estimations of expectations                     *)
(* ========================================================================= *)

Theorem PROB_ZERO_AE :
    !p E. prob_space p /\ E IN events p /\ (prob p E = 0) ==> AE x::p. x NOTIN E
Proof
    RW_TAC std_ss [AE_DEF, null_set_def]
 >> Q.EXISTS_TAC `E`
 >> fs [prob_space_def, events_def, prob_def]
QED

Theorem PROB_ZERO_AE_EQ :
    !p E. prob_space p /\ E IN events p ==> (prob p E = 0 <=> AE x::p. x NOTIN E)
Proof
    rpt STRIP_TAC
 >> EQ_TAC >- (DISCH_TAC >> MATCH_MP_TAC PROB_ZERO_AE >> art [])
 >> RW_TAC std_ss [AE_DEF, null_set_def]
 >> fs [prob_space_def, events_def, prob_def]
 >> Know ‘E SUBSET N’
 >- (rw [SUBSET_DEF] \\
    ‘x IN m_space p’ by PROVE_TAC [MEASURE_SPACE_IN_MSPACE] \\
     METIS_TAC [])
 >> DISCH_TAC
 >> reverse (rw [GSYM le_antisym])
 >- (‘positive p’ by PROVE_TAC [MEASURE_SPACE_POSITIVE] \\
     fs [positive_def])
 >> Q.PAT_X_ASSUM ‘measure p N = 0’ (ONCE_REWRITE_TAC o wrap o (MATCH_MP EQ_SYM))
 >> MATCH_MP_TAC INCREASING >> art []
 >> MATCH_MP_TAC MEASURE_SPACE_INCREASING >> art []
QED

Theorem PROB_ONE_AE :
    !p E. prob_space p /\ E IN events p /\ (prob p E = 1) ==> AE x::p. x IN E
Proof
    RW_TAC std_ss [AE_DEF, null_set_def]
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

Theorem PROB_ONE_AE_EQ :
    !p E. prob_space p /\ E IN events p ==> (prob p E = 1 <=> AE x::p. x IN E)
Proof
    rpt STRIP_TAC
 >> EQ_TAC >- (DISCH_TAC >> MATCH_MP_TAC PROB_ONE_AE >> art [])
 >> RW_TAC std_ss [AE_DEF, null_set_def]
 >> fs [prob_space_def, events_def, prob_def]
 >> Q.ABBREV_TAC ‘E' = m_space p DIFF E’
 >> ‘E' IN measurable_sets p’ by METIS_TAC [MEASURE_SPACE_COMPL]
 >> Know ‘E = m_space p DIFF E'’
 >- (rw [Once EXTENSION, Abbr ‘E'’] \\
     EQ_TAC >> rw [] \\
     PROVE_TAC [MEASURE_SPACE_IN_MSPACE])
 >> Rewr'
 >> Know ‘measure p (m_space p DIFF E') = measure p (m_space p) - measure p E'’
 >- (MATCH_MP_TAC MEASURE_COMPL >> rw [Abbr ‘E'’] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘measure p (m_space p)’ \\
     reverse CONJ_TAC >- rw [lt_infty, extreal_of_num_def] \\
     MATCH_MP_TAC INCREASING >> rw []
     >- (MATCH_MP_TAC MEASURE_SPACE_INCREASING >> art []) \\
     MATCH_MP_TAC MEASURE_SPACE_SPACE >> art [])
 >> Rewr'
 >> Suff ‘measure p E' = 0’ >- rw []
 >> reverse (rw [GSYM le_antisym])
 >- (‘positive p’ by PROVE_TAC [MEASURE_SPACE_POSITIVE] \\
     fs [positive_def])
 >> Q.PAT_X_ASSUM ‘measure p N = 0’ (ONCE_REWRITE_TAC o wrap o (MATCH_MP EQ_SYM))
 >> Know ‘E' SUBSET N’
 >- (rw [SUBSET_DEF, Abbr ‘E'’] >> METIS_TAC [])
 >> DISCH_TAC
 >> MATCH_MP_TAC INCREASING >> art []
 >> MATCH_MP_TAC MEASURE_SPACE_INCREASING >> art []
QED

(* Theorem 3.2.1, Part I [2, p.45] *)
Theorem expectation_bounds :
    !p X. prob_space p /\ real_random_variable X p ==>
          suminf (\n. prob p {x | x IN p_space p /\ &SUC n <= abs (X x)}) <=
          expectation p (abs o X) /\ expectation p (abs o X) <= 1 +
          suminf (\n. prob p {x | x IN p_space p /\ &SUC n <= abs (X x)})
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
 >> Q.ABBREV_TAC ‘A = \n. {x | x IN p_space p /\ &n <= abs (X x) /\ abs (X x) < &SUC n}’
 >> Know ‘!n. A n IN events p’
 >- (RW_TAC std_ss [Abbr ‘A’] \\
    ‘{x | x IN p_space p /\ &n <= abs (X x) /\ abs (X x) < &SUC n} =
       ({x | &n <= abs (X x)} INTER p_space p) INTER
       ({x | abs (X x) < &SUC n} INTER p_space p)’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC EVENTS_INTER >> rw [le_abs_bounds, abs_bounds_lt] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
      ‘{x | X x <= -&n \/ &n <= X x} INTER p_space p =
         ({x | X x <= -&n} INTER p_space p) UNION
         ({x | &n <= X x} INTER p_space p)’ by SET_TAC [] >> POP_ORW \\
       MATCH_MP_TAC EVENTS_UNION \\
       FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, events_def,
                             real_random_variable] \\
       METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE],
       (* goal 2 (of 2) *)
      ‘{x | -&SUC n < X x /\ X x < &SUC n} INTER p_space p =
         ({x | -&SUC n < X x} INTER p_space p) INTER
         ({x | X x < &SUC n} INTER p_space p)’ by SET_TAC [] >> POP_ORW \\
       MATCH_MP_TAC EVENTS_INTER \\
       FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, events_def,
                             real_random_variable] \\
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
     fs [real_random_variable_def, p_space_def] \\
     Know ‘pos_fn_integral p (\x. abs (X x) * indicator_fn (BIGUNION (IMAGE A UNIV)) x) =
           pos_fn_integral p (\x. suminf (\n. f n x))’
     >- (MATCH_MP_TAC pos_fn_integral_cong >> fs [prob_space_def] \\
         CONJ_TAC >- (rpt STRIP_TAC \\
                      MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS]) \\
         CONJ_TAC >- (rpt STRIP_TAC \\
                      MATCH_MP_TAC ext_suminf_pos >> rw [Abbr ‘f’] \\
                      MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS]) \\
         rw [Abbr ‘f’] \\
        ‘?r. X x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         REWRITE_TAC [extreal_abs_def] \\
         Know ‘suminf (\n. Normal (abs r) * indicator_fn (A n) x) =
               Normal (abs r) * suminf (\n. indicator_fn (A n) x)’
         >- (HO_MATCH_MP_TAC ext_suminf_cmul \\
             rw [extreal_of_num_def, extreal_le_eq, INDICATOR_FN_POS]) >> Rewr' \\
         Suff ‘indicator_fn (BIGUNION (IMAGE A UNIV)) x =
               suminf (\n. indicator_fn (A n) x)’ >- rw [] \\
         MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC indicator_fn_suminf >> rw []) >> Rewr' \\
    ‘!n x. abs (X x) * indicator_fn (A n) x = f n x’ by METIS_TAC [] >> POP_ORW \\
    ‘!n. (\x. f n x) = f n’ by METIS_TAC [ETA_THM] >> POP_ORW \\
     MATCH_MP_TAC pos_fn_integral_suminf \\
     fs [prob_space_def, Abbr ‘f’] \\
     CONJ_TAC >- (rpt STRIP_TAC \\
                  MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS]) \\
     Q.X_GEN_TAC ‘n’ \\
     HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR \\
     CONJ_TAC >- FULL_SIMP_TAC std_ss [measure_space_def] \\
     CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS \\
                  Q.EXISTS_TAC ‘X’ \\
                  fs [random_variable_def, p_space_def, events_def, measure_space_def]) \\
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
         rw [extreal_of_num_def, extreal_not_infty] >| (* 3 subgoals *)
         [ (* goal 1 (of 3) *)
           Suff ‘(0 :real) <= &PRE N’ >- METIS_TAC [mul_not_infty] >> rw [],
           (* goal 2 (of 3) *)
           MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF >> rw [FINITE_COUNT] \\
           Suff ‘(0 :real) <= &SUC x’ >- METIS_TAC [mul_not_infty] >> rw [],
           (* goal 3 (of 3) *)
           MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> rw [FINITE_COUNT] \\
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
     Suff ‘(0 :real) <= &PRE N’ >- METIS_TAC [mul_not_infty] >> rw [])
 >> DISCH_TAC
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
         FULL_SIMP_TAC std_ss [real_random_variable_def, p_space_def] \\
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

(* Theorem 3.2.1, Part II [2, p.45] *)
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
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
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

Theorem identical_distribution_alt_prob :
    !p X E J i j s. identical_distribution p X E J /\
                    s IN subsets E /\ i IN J /\ j IN J ==>
        (prob p {x | x IN p_space p /\ X i x IN s} =
         prob p {x | x IN p_space p /\ X j x IN s})
Proof
    RW_TAC std_ss [identical_distribution_def, distribution_def, PREIMAGE_def]
 >> ‘!i. {x | x IN p_space p /\ X i x IN s} =
         {x | X i x IN s} INTER p_space p’ by SET_TAC []
 >> POP_ORW
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

(* alternative definition of identical distribution, see [3, p.62, Definition 5.4.1] *)
Theorem identical_distribution_alt :
    !p X (J :'index set). prob_space p /\
         (!n. n IN J ==> random_variable (X n) p Borel) ==>
         (identical_distribution p X Borel J <=>
          (!f. f IN measurable Borel Borel ==>
               ?c. !n. n IN J ==> expectation p (f o (X n)) = c))
Proof
    RW_TAC std_ss [identical_distribution_def]
 >> EQ_TAC >> rpt STRIP_TAC
 >- (Cases_on ‘J = {}’ >- (Q.EXISTS_TAC ‘ARB’ >> rw []) \\
     Q.ABBREV_TAC ‘j = CHOICE J’ \\
    ‘j IN J’ by METIS_TAC [CHOICE_DEF] \\
     Q.EXISTS_TAC ‘expectation p (f o X j)’ \\
     Q.X_GEN_TAC ‘i’ >> STRIP_TAC \\
     Know ‘!n. n IN J ==>
               expectation p (f o X n) =
               integral (space Borel,subsets Borel,distribution p (X n)) f’
     >- (METIS_TAC [expectation_distribution]) >> rw [] \\
     MATCH_MP_TAC integral_cong_measure' >> simp [measure_space_eq_def] \\
     Suff ‘!n. n IN J ==> measure_space (space Borel,subsets Borel,distribution p (X n))’
     >- rw [] \\
     Q.X_GEN_TAC ‘n’ >> STRIP_TAC \\
     FULL_SIMP_TAC std_ss [distribution_distr, prob_space_def, random_variable_def,
                           p_space_def, events_def] \\
     MATCH_MP_TAC measure_space_distr \\
     rw [SIGMA_ALGEBRA_BOREL])
 >> Know ‘!n f. n IN J /\ f IN Borel_measurable Borel ==>
                expectation p (f o X n) =
                integral (space Borel,subsets Borel,distribution p (X n)) f’
 >- (rpt STRIP_TAC \\
     METIS_TAC [expectation_distribution])
 >> DISCH_TAC
 >> Know ‘indicator_fn s IN measurable Borel Borel’
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR \\
     Q.EXISTS_TAC ‘s’ >> rw [SIGMA_ALGEBRA_BOREL])
 >> DISCH_TAC
 >> Know ‘!n. n IN J ==>
              expectation p ((indicator_fn s) o (X n)) =
              expectation p ((indicator_fn s) o (X j))’
 >- (rpt STRIP_TAC >> METIS_TAC [])
 >> simp []
 >> Know ‘!n. n IN J ==>
              integral (space Borel,subsets Borel,distribution p (X n)) (indicator_fn s) =
              distribution p (X n) s’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC (REWRITE_RULE [measure_def, measurable_sets_def]
                    (Q.SPECL [‘(space Borel,subsets Borel,
                                distribution (p :'a m_space) (X (n :'index)))’, ‘s’]
                      (INST_TYPE [“:'a” |-> “:extreal”] integral_indicator))) \\
     simp [distribution_distr] \\
     MATCH_MP_TAC measure_space_distr \\
     fs [prob_space_def, random_variable_def, p_space_def, events_def, SIGMA_ALGEBRA_BOREL])
 >> rw []
QED

Theorem identical_distribution_alt' :
    !p (X :num -> 'a -> extreal).
          prob_space p /\ (!n. random_variable (X n) p Borel) ==>
         (identical_distribution p X Borel univ(:num) <=>
          (!f n. f IN measurable Borel Borel ==>
                 expectation p (f o (X n)) = expectation p (f o (X 0))))
Proof
    RW_TAC std_ss [identical_distribution_alt, IN_UNIV]
 >> EQ_TAC >> rw []
 >> METIS_TAC []
QED

(* Theorem 3.1.4 [2, p.37], slightly generalized *)
Theorem random_variable_comp :
    !p X A f. random_variable X p A /\ f IN measurable A A ==>
              random_variable (f o X) p A
Proof
    rw [random_variable_def]
 >> MATCH_MP_TAC MEASURABLE_COMP
 >> Q.EXISTS_TAC `A` >> art []
QED

Theorem identical_distribution_cong :
    !p X f. prob_space p /\ (!n. random_variable (X n) p Borel) /\
            identical_distribution p X Borel univ(:num) /\
            f IN measurable Borel Borel ==>
            identical_distribution p (\n. f o X n) Borel univ(:num)
Proof
    rpt STRIP_TAC
 >> Know ‘identical_distribution p X Borel univ(:num) <=>
          (!f n. f IN measurable Borel Borel ==>
                 expectation p (f o (X n)) = expectation p (f o (X 0)))’
 >- (MATCH_MP_TAC identical_distribution_alt' >> art [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> Know ‘identical_distribution p (\n. f o X n) Borel univ(:num) <=>
          (!g n. g IN measurable Borel Borel ==>
                 expectation p (g o ((\n. f o X n) n)) =
                 expectation p (g o ((\n. f o X n) 0)))’
 >- (MATCH_MP_TAC identical_distribution_alt' >> rw [] \\
     MATCH_MP_TAC random_variable_comp >> art [])
 >> Rewr'
 >> RW_TAC std_ss []
 >> REWRITE_TAC [o_ASSOC]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> MATCH_MP_TAC MEASURABLE_COMP
 >> Q.EXISTS_TAC ‘Borel’ >> art []
QED

(* r.v.'s having identical distributions have the same integrability

   NOTE: fixes after k14: changed ‘identical_distribution p X Borel UNIV’
                               to ‘identical_distribution p X Borel J’
 *)
Theorem identical_distribution_integrable_general :
    !p X (J :'index set). prob_space p /\
         (!n. n IN J ==> random_variable (X n) p Borel) /\
          identical_distribution p X Borel J /\
         (?i. i IN J /\ integrable p (X i)) ==> !n. n IN J ==> integrable p (X n)
Proof
    RW_TAC std_ss [identical_distribution_def]
 >> ‘X n IN Borel_measurable (m_space p,measurable_sets p)’
       by fs [random_variable_def, p_space_def, events_def]
 >> Know ‘(\x. x) IN measurable Borel Borel’
 >- (rw [IN_MEASURABLE, SIGMA_ALGEBRA_BOREL, IN_FUNSET, PREIMAGE_def] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> rw [SIGMA_ALGEBRA_BOREL] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_SPACE >> rw [SIGMA_ALGEBRA_BOREL])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘X (i :'index)’, ‘\x. x’] expectation_distribution)
 >> RW_TAC std_ss [o_DEF]
 >> MP_TAC (Q.SPECL [‘p’, ‘X (n :'index)’, ‘\x. x’] expectation_distribution)
 >> RW_TAC std_ss [o_DEF]
 >> Suff ‘integrable (space Borel,subsets Borel,distribution p (X i)) (\x. x) <=>
          integrable (space Borel,subsets Borel,distribution p (X n)) (\x. x)’
 >- METIS_TAC []
 (* applying integral_cong_measure *)
 >> ‘prob_space (space Borel,subsets Borel,distribution p (X i)) /\
     prob_space (space Borel,subsets Borel,distribution p (X n))’
       by METIS_TAC [distribution_prob_space, SIGMA_ALGEBRA_BOREL]
 >> MATCH_MP_TAC integrable_cong_measure
 >> fs [prob_space_def]
QED

Theorem identical_distribution_integrable :
    !p X. prob_space p /\ (!n. random_variable (X n) p Borel) /\
          identical_distribution p X Borel UNIV /\ integrable p (X 0) ==>
          !(n :num). integrable p (X n)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘UNIV’]
                    (INST_TYPE [“:'index” |-> “:num”]
                               identical_distribution_integrable_general))
 >> RW_TAC std_ss [IN_UNIV]
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘0’ >> art []
QED

(* r.v.'s having identical distributions have the same expectation

   NOTE: fixes after k14: changed ‘identical_distribution p X Borel UNIV’
                               to ‘identical_distribution p X Borel J’

         also removed unnecessary ‘J <> {}’ from antecedents.
 *)
Theorem identical_distribution_expectation_general :
    !p X (J :'index set). prob_space p /\
         (!n. n IN J ==> random_variable (X n) p Borel) /\
          identical_distribution p X Borel J ==>
          ?e. !n. n IN J ==> expectation p (X n) = e
Proof
    RW_TAC std_ss [identical_distribution_def]
 >> Know ‘(\x. x) IN measurable Borel Borel’
 >- (rw [IN_MEASURABLE, SIGMA_ALGEBRA_BOREL, IN_FUNSET, PREIMAGE_def] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> rw [SIGMA_ALGEBRA_BOREL] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_SPACE >> rw [SIGMA_ALGEBRA_BOREL])
 >> DISCH_TAC
 >> Cases_on ‘J = {}’ >- (Q.EXISTS_TAC ‘ARB’ >> rw [])
 >> Q.ABBREV_TAC ‘i = CHOICE J’
 >> ‘i IN J’ by METIS_TAC [CHOICE_DEF]
 >> MP_TAC (Q.SPECL [‘p’, ‘X (i :'index)’, ‘\x. x’] expectation_distribution)
 >> RW_TAC std_ss [o_DEF]
 >> Q.EXISTS_TAC ‘expectation p (X i)’
 >> rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘X (n :'index)’, ‘\x. x’] expectation_distribution)
 >> RW_TAC std_ss [o_DEF]
 >> ‘!n. X n = (\x. X n x)’ by METIS_TAC [ETA_THM] >> POP_ORW
 >> Suff ‘integral (space Borel,subsets Borel,distribution p (X i)) (\x. x) =
          integral (space Borel,subsets Borel,distribution p (X n)) (\x. x)’
 >- rw []
 (* applying integral_cong_measure *)
 >> ‘prob_space (space Borel,subsets Borel,distribution p (X i)) /\
     prob_space (space Borel,subsets Borel,distribution p (X n))’
       by METIS_TAC [distribution_prob_space, SIGMA_ALGEBRA_BOREL]
 >> MATCH_MP_TAC integral_cong_measure
 >> fs [prob_space_def]
QED

Theorem identical_distribution_expectation :
    !p X. prob_space p /\ (!n. random_variable (X n) p Borel) /\
          identical_distribution p X Borel UNIV ==>
          !(n :num). expectation p (X n) = expectation p (X 0)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘UNIV’]
                    (INST_TYPE [“:'index” |-> “:num”]
                               identical_distribution_expectation_general))
 >> RW_TAC std_ss [IN_UNIV] >> art []
QED

(* Theorem 3.1.5 [2, p.38] *)
Theorem fundamental_theorem_of_random_vectors :
    !p X Y f. prob_space p /\ random_variable X p Borel /\ random_variable Y p Borel /\
              f IN measurable (Borel CROSS Borel) Borel ==>
              random_variable (\x. f (X x,Y x)) p Borel
Proof
    RW_TAC std_ss [random_variable_def, prob_space_def, p_space_def, events_def]
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_2D_FUNCTION
 >> fs [measure_space_def]
QED

Theorem indep_vars_comm : (* was: INDEP_RV_SYM *)
    !p X Y s t. indep_rv p X Y s t ==> indep_rv p Y X t s
Proof
    RW_TAC std_ss [indep_rv_def]
 >> MATCH_MP_TAC INDEP_SYM
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

(* Theorem 3.3.1 [2, p.54], slightly generalized to arbitrary index set *)
Theorem indep_vars_cong :
    !p X B (J :'index set) f.
         indep_vars p (X :'index -> 'a -> 'b) B (J :'index set) /\
        (!n. n IN J ==> random_variable (X n) p (B n)) /\
        (!n. n IN J ==> f n IN measurable (B n) (B n)) ==>
         indep_vars p (\n. (f n) o (X n)) B (J :'index set)
Proof
    rw [indep_vars_def, indep_events_def, o_DEF]
 >> Q.ABBREV_TAC ‘E' = \i. PREIMAGE (f i) (E i) INTER space (B i)’
 >> Know ‘BIGINTER (IMAGE (\n. PREIMAGE (\x. f n (X n x)) (E n) INTER p_space p) N) =
          BIGINTER (IMAGE (\n. PREIMAGE (X n) (E' n) INTER p_space p) N)’
 >- (rw [Abbr ‘E'’, Once EXTENSION, IN_BIGINTER_IMAGE] \\
     EQ_TAC >> rw []
     >- (‘n IN J’ by METIS_TAC [SUBSET_DEF] \\
         Q.PAT_X_ASSUM ‘!n. n IN J ==> random_variable (X n) p (B n)’
           (STRIP_ASSUME_TAC o
            (SIMP_RULE (srw_ss()) [random_variable_def, IN_MEASURABLE, IN_FUNSET])) \\
         METIS_TAC [])
     >- (METIS_TAC [])
     >- (METIS_TAC []))
 >> Rewr'
 (* applying EXTREAL_PROD_IMAGE_EQ *)
 >> Know ‘PI (\n. prob p (PREIMAGE (\x. f n (X n x)) (E n) INTER p_space p)) N =
          PI (\n. prob p (PREIMAGE (X n) (E' n) INTER p_space p)) N’
 >- (irule EXTREAL_PROD_IMAGE_EQ >> art [] \\
     Q.X_GEN_TAC ‘n’ >> rw [] \\
     Suff ‘PREIMAGE (\x. f n (X n x)) (E n) INTER p_space p =
           PREIMAGE (X n) (E' n) INTER p_space p’ >- rw [] \\
     rw [Abbr ‘E'’, PREIMAGE_def, Once EXTENSION] >> EQ_TAC >> rw [] \\
    ‘n IN J’ by METIS_TAC [SUBSET_DEF] \\
     Q.PAT_X_ASSUM ‘!n. n IN J ==> random_variable (X n) p (B n)’
       (STRIP_ASSUME_TAC o
        (SIMP_RULE (srw_ss()) [random_variable_def, IN_MEASURABLE, IN_FUNSET])) \\
     PROVE_TAC [])
 >> Rewr'
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> fs [Abbr ‘E'’, PREIMAGE_def, IN_DFUNSET, IN_MEASURABLE]
 >> rw []
 >> Q.PAT_X_ASSUM ‘!n. n IN J ==> f n IN (space (B n) -> space (B n)) /\ _’
      (MP_TAC o (Q.SPEC ‘x’))
 >> ‘x IN J’ by PROVE_TAC [SUBSET_DEF]
 >> rw []
QED

(* A specialized version of previous theorem for only two r.v.'s *)
Theorem indep_rv_cong :
    !p X Y A B f g. indep_rv p X Y A B /\
                    random_variable X p A /\ random_variable Y p B /\
                    f IN measurable A A /\ g IN measurable B B ==>
                    indep_vars p (f o X) (g o Y) A B
Proof
    rpt STRIP_TAC
 >> ‘random_variable (f o X) p A /\
     random_variable (g o Y) p B’ by PROVE_TAC [random_variable_comp]
 >> fs [indep_rv_alt_indep_vars]
 >> MP_TAC (Q.SPECL [‘p’, ‘binary X Y’, ‘binary A B’, ‘{0; 1}’, ‘binary f g’]
                    (INST_TYPE [“:'index” |-> “:num”] indep_vars_cong))
 >> Know ‘!n. n IN {0; 1} ==> random_variable (binary X Y n) p (binary A B n)’
 >- rw [binary_def]
 >> Know ‘!n. n IN {0; 1} ==>
              binary f g n IN measurable (binary A B n) (binary A B n)’
 >- rw [binary_def]
 >> RW_TAC std_ss []
 >> Suff ‘(binary (f o X) (g o Y)) = (\n. (binary f g n) o (binary X Y n))’
 >- rw []
 >> rw [FUN_EQ_THM, binary_def]
 >> Cases_on ‘n = 0’ >> rw []
QED

(* Another version of "indep_vars_cong" for pairwise independent r.v.'s *)
Theorem pairwise_indep_vars_cong :
    !p X B (J :'index set) f.
         pairwise_indep_vars p (X :'index -> 'a -> 'b) B (J :'index set) /\
        (!n. n IN J ==> random_variable (X n) p (B n)) /\
        (!n. n IN J ==> f n IN measurable (B n) (B n)) ==>
         pairwise_indep_vars p (\n. (f n) o (X n)) B (J :'index set)
Proof
    rw [pairwise_indep_vars_def]
 >> rename1 ‘i <> j’
 >> MP_TAC (Q.SPECL [‘p’, ‘X (i :'index)’, ‘X (j :'index)’,
                     ‘B (i :'index)’, ‘B (j :'index)’,
                     ‘f (i :'index)’, ‘f (j :'index)’] indep_rv_cong)
 >> rw [o_DEF]
QED

(* Theorem 3.3.3 [2, p.54], depending on Fubini and UNIQUENESS_OF_PROD_MEASURE

   This is the last theorem in Isabelle's Independent_Family.thy but in extreals.
 *)
Theorem indep_vars_expectation :
    !p X Y. prob_space p /\ real_random_variable X p /\ real_random_variable Y p /\
            indep_rv p X Y Borel Borel /\ integrable p X /\ integrable p Y ==>
            expectation p (\x. X x * Y x) = expectation p X * expectation p Y
Proof
    rw [indep_rv_def, real_random_variable_def, prob_space_def, p_space_def, events_def,
        real_random_variable_def, random_variable_def, expectation_def]
 >> Q.ABBREV_TAC ‘f = \x. (X x,Y x)’
 >> Q.ABBREV_TAC ‘u = \(x,y). x * (y :extreal)’
 >> ‘(\x. X x * Y x) = u o f’ by rw [Abbr ‘u’, Abbr ‘f’, o_DEF] >> POP_ORW
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
 (* applying MEASURABLE_PROD_SIGMA' *)
 >> Know ‘f IN measurable (m_space p,measurable_sets p) (Borel CROSS Borel)’
 >- (MATCH_MP_TAC MEASURABLE_PROD_SIGMA' \\
     simp [Abbr ‘f’, o_DEF, ETA_AX] \\
     MP_TAC SIGMA_ALGEBRA_BOREL >> rw [sigma_algebra_def, algebra_def])
 >> DISCH_TAC
 >> Know ‘u IN measurable (Borel CROSS Borel) Borel’
 >- (Q.UNABBREV_TAC ‘u’ \\
     REWRITE_TAC [IN_MEASURABLE_BOREL_2D_MUL])
 >> DISCH_TAC
 (* applying integral_distr and SIGMA_ALGEBRA_BOREL_2D *)
 >> Know ‘integral p (u o f) =
          integral (space (Borel CROSS Borel),subsets (Borel CROSS Borel),distr p f) u’
 >- (MP_TAC (ISPECL [“p :'a m_space”,
                     “Borel CROSS Borel”,
                     “f :'a -> extreal # extreal”,
                     “u :extreal # extreal -> extreal”] integral_distr) \\
     RW_TAC std_ss [SIGMA_ALGEBRA_BOREL_2D]) >> Rewr'
 >> Q.ABBREV_TAC ‘m1 = (space Borel,subsets Borel,distr p X)’
 >> Q.ABBREV_TAC ‘m2 = (space Borel,subsets Borel,distr p Y)’
 >> ‘measure_space m1 /\ measure_space m2’
      by METIS_TAC [measure_space_distr, SIGMA_ALGEBRA_BOREL]
 (* sigma_finiteness of m1 and m2 *)
 >> Know ‘sigma_finite_measure_space m1 /\ sigma_finite_measure_space m2’
 >- (rw [sigma_finite_measure_space_def] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC FINITE_IMP_SIGMA_FINITE >> art [lt_infty] \\
      ‘m_space m1 = UNIV’ by METIS_TAC [m_space_def, SPACE_BOREL] >> POP_ORW \\
      ‘measure m1 = distr p X’ by METIS_TAC [measure_def] >> POP_ORW \\
       rw [distr_def],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC FINITE_IMP_SIGMA_FINITE >> art [lt_infty] \\
      ‘m_space m2 = UNIV’ by METIS_TAC [m_space_def, SPACE_BOREL] >> POP_ORW \\
      ‘measure m2 = distr p Y’ by METIS_TAC [measure_def] >> POP_ORW \\
       rw [distr_def] ])
 >> STRIP_TAC
 >> ‘measure_space (m1 CROSS m2)’ by PROVE_TAC [measure_space_prod_measure]
 (* applying UNIQUENESS_OF_PROD_MEASURE *)
 >> Know ‘integral (space (Borel CROSS Borel),subsets (Borel CROSS Borel),distr p f) u =
          integral (m1 CROSS m2) u’
 >- (MATCH_MP_TAC integral_cong_measure' >> simp [measure_space_eq_def] \\
     CONJ_TAC >- (MATCH_MP_TAC measure_space_distr >> rw [SIGMA_ALGEBRA_BOREL_2D]) \\
     CONJ_TAC >- rw [SPACE_PROD_SIGMA, prod_measure_space_alt, Abbr ‘m1’, Abbr ‘m2’] \\
     CONJ_TAC >- rw [prod_measure_space_alt, Abbr ‘m1’, Abbr ‘m2’] \\
     MATCH_MP_TAC UNIQUENESS_OF_PROD_MEASURE \\
     qexistsl_tac [‘space Borel’, ‘space Borel’] \\
     qexistsl_tac [‘subsets Borel’, ‘subsets Borel’] \\
     qexistsl_tac [‘distr p X’, ‘distr p Y’] \\
     Know ‘subset_class (space Borel) (subsets Borel)’
     >- (rw [subset_class_def, SPACE_BOREL]) >> Rewr \\
     Know ‘sigma (space Borel) (subsets Borel) = Borel’
     >- (MATCH_MP_TAC SIGMA_STABLE \\
         REWRITE_TAC [SIGMA_ALGEBRA_BOREL]) >> Rewr \\
     CONJ_TAC >- fs [Abbr ‘m1’, sigma_finite_measure_space_def] \\
     CONJ_TAC >- fs [Abbr ‘m2’, sigma_finite_measure_space_def] \\
     Know ‘!s t. s IN subsets Borel /\ t IN subsets Borel ==>
                 s INTER t IN subsets Borel’
     >- (rpt STRIP_TAC \\
         MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [SIGMA_ALGEBRA_BOREL]) >> Rewr \\
     CONJ_TAC >- fs [Abbr ‘m1’, sigma_finite_measure_space_def] \\
     CONJ_TAC >- fs [Abbr ‘m2’, sigma_finite_measure_space_def] \\
     Know ‘space Borel CROSS space Borel = space (Borel CROSS Borel)’
     >- (rw [prod_sigma_def, SPACE_SIGMA]) >> Rewr' \\
     CONJ_TAC >- (MATCH_MP_TAC measure_space_distr >> art [SIGMA_ALGEBRA_BOREL_2D]) \\
     CONJ_TAC
     >- (Know ‘space (Borel CROSS Borel) = m_space (m1 CROSS m2)’
         >- (rw [Abbr ‘m1’, Abbr ‘m2’, SPACE_PROD_SIGMA, prod_measure_space_alt]) >> Rewr' \\
         Know ‘subsets (Borel CROSS Borel) = measurable_sets (m1 CROSS m2)’
         >- (rw [Abbr ‘m1’, Abbr ‘m2’, prod_sigma_def, prod_measure_space_alt]) >> Rewr' \\
         art [MEASURE_SPACE_REDUCE]) \\
     CONJ_TAC
     >- (rw [distr_def, PREIMAGE_CROSS, Abbr ‘f’, o_DEF, ETA_AX] \\
        ‘PREIMAGE X s INTER PREIMAGE Y t INTER m_space p =
          (PREIMAGE X s INTER m_space p) INTER (PREIMAGE Y t INTER m_space p)’
           by SET_TAC [] >> POP_ORW \\
         METIS_TAC [indep_def, prob_def]) \\ (* independence is used here!!! *)
     rw [prod_measure_space_alt, INDICATOR_FN_CROSS] \\
     ONCE_REWRITE_TAC [mul_comm] \\
     Know ‘!y. pos_fn_integral m1 (\x. indicator_fn t y * indicator_fn s x) =
               indicator_fn t y * pos_fn_integral m1 (indicator_fn s)’
     >- (GEN_TAC \\
        ‘?r. 0 <= r /\ (indicator_fn t y = Normal r)’ by METIS_TAC [indicator_fn_normal] \\
         POP_ORW \\
         MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) >> Rewr' \\
     Know ‘pos_fn_integral m1 (indicator_fn s) = measure m1 s’
     >- (MATCH_MP_TAC pos_fn_integral_indicator >> rw [Abbr ‘m1’]) >> Rewr' \\
     ONCE_REWRITE_TAC [mul_comm] \\
     Know ‘?r. 0 <= r /\ (measure m1 s = Normal r)’
     >- (rw [Abbr ‘m1’, distr_def] \\
         Know ‘measure p (PREIMAGE X s INTER m_space p) <= measure p (m_space p)’
         >- (MATCH_MP_TAC INCREASING \\
             CONJ_TAC >- (MATCH_MP_TAC MEASURE_SPACE_INCREASING >> art []) \\
             CONJ_TAC >- REWRITE_TAC [INTER_SUBSET] \\
             reverse CONJ_TAC >- (MATCH_MP_TAC MEASURE_SPACE_MSPACE_MEASURABLE >> art []) \\
             fs [IN_MEASURABLE]) >> art [] \\
         DISCH_TAC \\
         Know ‘0 <= measure p (PREIMAGE X s INTER m_space p)’
         >- (‘positive p’ by PROVE_TAC [MEASURE_SPACE_POSITIVE] \\
             fs [positive_def] >> POP_ASSUM MATCH_MP_TAC \\
             fs [IN_MEASURABLE]) >> DISCH_TAC \\
        ‘measure p (PREIMAGE X s INTER m_space p) <> NegInf’ by PROVE_TAC [pos_not_neginf] \\
         Know ‘measure p (PREIMAGE X s INTER m_space p) <> PosInf’
         >- (REWRITE_TAC [lt_infty] \\
             MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘1’ \\
             rw [GSYM lt_infty, extreal_of_num_def, extreal_not_infty]) \\
         DISCH_TAC \\
        ‘?r. measure p (PREIMAGE X s INTER m_space p) = Normal r’ by METIS_TAC [extreal_cases] \\
         fs [extreal_of_num_def, extreal_le_eq]) \\
     STRIP_TAC \\
     Know ‘pos_fn_integral m2 (\y. measure m1 s * indicator_fn t y) =
           measure m1 s * pos_fn_integral m2 (indicator_fn t)’
     >- (POP_ORW >> MATCH_MP_TAC pos_fn_integral_cmul >> art [INDICATOR_FN_POS]) >> Rewr' \\
     Know ‘pos_fn_integral m2 (indicator_fn t) = measure m2 t’
     >- (MATCH_MP_TAC pos_fn_integral_indicator >> rw [Abbr ‘m2’]) >> Rewr' \\
     POP_ASSUM K_TAC \\
     rw [Abbr ‘m1’, Abbr ‘m2’])
 >> Rewr'
 (* clean up ‘f’ *)
 >> Q.PAT_X_ASSUM ‘f IN measurable (m_space p,measurable_sets p) (Borel CROSS Borel)’ K_TAC
 >> Q.UNABBREV_TAC ‘f’
 (* applying Fubini; finiteness / integrability is needed here. *)
 >> Know ‘integral (m1 CROSS m2) u = integral m2 (\y. integral m1 (\x. u (x,y)))’
 >- (MP_TAC (ISPECL [“m1 :extreal m_space”, “m2 :extreal m_space”,
                     “u :extreal # extreal -> extreal”] Fubini) \\
     Know ‘((m_space m1,measurable_sets m1) CROSS
            (m_space m2,measurable_sets m2)) = Borel CROSS Borel’
     >- rw [Abbr ‘m1’, Abbr ‘m2’, SPACE] >> Rewr' \\
     ASM_SIMP_TAC std_ss [o_DEF] \\
     Suff ‘pos_fn_integral m2 (\y. pos_fn_integral m1 (\x. abs (u (x,y)))) <> PosInf’
     >- METIS_TAC [] \\
     rw [Abbr ‘u’, abs_mul] \\
     Know ‘pos_fn_integral m2 (\y. pos_fn_integral m1 (\x. abs x * abs y)) =
           pos_fn_integral m2 (\y. abs y * pos_fn_integral m1 (\x. abs x))’
     >- (MATCH_MP_TAC pos_fn_integral_cong_AE >> rw [] >| (* 3 subgoals *)
         [ (* goal 1 (of 3) *)
           MATCH_MP_TAC pos_fn_integral_pos >> art [] \\
           Q.X_GEN_TAC ‘y’ >> rw [] \\
           MATCH_MP_TAC le_mul >> REWRITE_TAC [abs_pos],
           (* goal 2 (of 3) *)
           MATCH_MP_TAC le_mul >> REWRITE_TAC [abs_pos] \\
           MATCH_MP_TAC pos_fn_integral_pos >> rw [abs_pos],
           (* goal 3 (of 3) *)
           rw [AE_DEF] \\
           Q.EXISTS_TAC ‘{PosInf; NegInf}’ \\
           reverse CONJ_TAC
           >- (rw [] >> ‘?r. x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
               REWRITE_TAC [extreal_abs_def, ETA_AX] \\
               GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [mul_comm] \\
               MATCH_MP_TAC pos_fn_integral_cmul >> rw [abs_pos]) \\
           rw [null_set_def, Abbr ‘m2’, distr_def]
           >- (MATCH_MP_TAC BOREL_MEASURABLE_SETS_FINITE \\
               REWRITE_TAC [FINITE_TWO]) \\
           Know ‘PREIMAGE Y {PosInf; NegInf} INTER m_space p = {}’
           >- (rw [PREIMAGE_def, Once EXTENSION] \\
               METIS_TAC []) >> Rewr' \\
          ‘positive p’ by PROVE_TAC [MEASURE_SPACE_POSITIVE] \\
           fs [positive_def] ]) >> Rewr' \\
     ONCE_REWRITE_TAC [mul_comm] \\
     Know ‘pos_fn_integral m1 (\x. abs x) <> PosInf’
     >- (rw [Abbr ‘m1’, ETA_AX] \\
         Know ‘pos_fn_integral (space Borel,subsets Borel,distr p X) abs =
               pos_fn_integral p (abs o X)’
         >- (MATCH_MP_TAC pos_fn_integral_distr \\
             rw [SIGMA_ALGEBRA_BOREL, IN_MEASURABLE_BOREL_BOREL_ABS, abs_pos]) >> Rewr' \\
         Know ‘integrable p (abs o X)’ >- PROVE_TAC [integrable_abs] \\
         rw [integrable_def, FN_PLUS_ABS_SELF]) >> DISCH_TAC \\
     Know ‘0 <= pos_fn_integral m1 (\x. abs x)’
     >- (MATCH_MP_TAC pos_fn_integral_pos >> rw [abs_pos]) >> DISCH_TAC \\
    ‘pos_fn_integral m1 (\x. abs x) <> NegInf’ by PROVE_TAC [pos_not_neginf] \\
    ‘?r. 0 <= r /\ pos_fn_integral m1 (\x. abs x) = Normal r’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_le_eq] >> POP_ORW \\
     Know ‘pos_fn_integral m2 (\y. Normal r * abs y) =
           Normal r * pos_fn_integral m2 abs’
     >- (MATCH_MP_TAC pos_fn_integral_cmul >> rw [abs_pos]) >> Rewr' \\
     Know ‘pos_fn_integral m2 abs <> PosInf’
     >- (rw [Abbr ‘m2’] \\
         Know ‘pos_fn_integral (space Borel,subsets Borel,distr p Y) abs =
               pos_fn_integral p (abs o Y)’
         >- (MATCH_MP_TAC pos_fn_integral_distr \\
             rw [SIGMA_ALGEBRA_BOREL, IN_MEASURABLE_BOREL_BOREL_ABS, abs_pos]) >> Rewr' \\
         Know ‘integrable p (abs o Y)’ >- PROVE_TAC [integrable_abs] \\
         rw [integrable_def, FN_PLUS_ABS_SELF]) >> DISCH_TAC \\
     Know ‘pos_fn_integral m2 abs <> NegInf’
     >- (MATCH_MP_TAC pos_not_neginf \\
         MATCH_MP_TAC pos_fn_integral_pos >> rw [abs_pos]) >> DISCH_TAC \\
    ‘?z. pos_fn_integral m2 abs = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     REWRITE_TAC [extreal_mul_def, extreal_not_infty])
 >> Rewr'
 (* clean up ‘u’, now all pairs disappeared *)
 >> Q.UNABBREV_TAC ‘u’ >> simp []
 (* applying integral_cong_AE and integral_cmul, twice *)
 >> Know ‘integral m2 (\y. integral m1 (\x. x * y)) =
          integral m2 (\y. y * integral m1 (\x. x))’
 >- (GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [mul_comm] \\
     MATCH_MP_TAC integral_cong_AE >> rw [AE_DEF] \\
     Q.EXISTS_TAC ‘{PosInf; NegInf}’ \\
     CONJ_TAC
     >- (rw [null_set_def, Abbr ‘m2’, distr_def]
         >- (MATCH_MP_TAC BOREL_MEASURABLE_SETS_FINITE \\
             REWRITE_TAC [FINITE_TWO]) \\
         Know ‘PREIMAGE Y {PosInf; NegInf} INTER m_space p = {}’
         >- (rw [PREIMAGE_def, Once EXTENSION] \\
             METIS_TAC []) >> Rewr' \\
        ‘positive p’ by PROVE_TAC [MEASURE_SPACE_POSITIVE] \\
         fs [positive_def]) \\
     rw [] >> ‘?r. x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     HO_MATCH_MP_TAC integral_cmul >> art [] \\
     rw [integrable_def, Abbr ‘m1’, IN_MEASURABLE_BOREL_BOREL_I] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Know ‘pos_fn_integral (space Borel,subsets Borel,distr p X) (fn_plus (\x. x)) =
             pos_fn_integral p (fn_plus (\x. x) o X)’
       >- (MATCH_MP_TAC pos_fn_integral_distr \\
           rw [FN_PLUS_POS, SIGMA_ALGEBRA_BOREL] \\
           MATCH_MP_TAC IN_MEASURABLE_BOREL_FN_PLUS \\
           REWRITE_TAC [IN_MEASURABLE_BOREL_BOREL_I, SIGMA_ALGEBRA_BOREL]) >> Rewr' \\
      ‘(fn_plus (\x. x) o X) = fn_plus X’ by rw [fn_plus_def, o_DEF] >> POP_ORW \\
       fs [integrable_def],
       (* goal 2 (of 2) *)
       Know ‘pos_fn_integral (space Borel,subsets Borel,distr p X) (fn_minus (\x. x)) =
             pos_fn_integral p (fn_minus (\x. x) o X)’
       >- (MATCH_MP_TAC pos_fn_integral_distr \\
           rw [FN_MINUS_POS, SIGMA_ALGEBRA_BOREL] \\
           MATCH_MP_TAC IN_MEASURABLE_BOREL_FN_MINUS \\
           REWRITE_TAC [IN_MEASURABLE_BOREL_BOREL_I, SIGMA_ALGEBRA_BOREL]) >> Rewr' \\
      ‘(fn_minus (\x. x) o X) = fn_minus X’ by rw [fn_minus_def, o_DEF] >> POP_ORW \\
       fs [integrable_def] ])
 >> Rewr'
 >> Know ‘integrable m1 (\x. x)’
 >- (rw [Abbr ‘m1’] \\
     MP_TAC (Q.SPECL [‘p’, ‘Borel’, ‘X’, ‘\x. x’]
                     (INST_TYPE [“:'b” |-> “:extreal”] integral_distr)) \\
     rw [IN_MEASURABLE_BOREL_BOREL_I, SIGMA_ALGEBRA_BOREL, o_DEF, ETA_AX])
 >> DISCH_TAC
 >> Know ‘integrable m2 (\x. x)’
 >- (rw [Abbr ‘m2’] \\
     MP_TAC (Q.SPECL [‘p’, ‘Borel’, ‘Y’, ‘\x. x’]
                     (INST_TYPE [“:'b” |-> “:extreal”] integral_distr)) \\
     rw [IN_MEASURABLE_BOREL_BOREL_I, SIGMA_ALGEBRA_BOREL, o_DEF, ETA_AX])
 >> DISCH_TAC
 >> Know ‘integral m2 (\y. y * integral m1 (\x. x)) =
          integral m1 (\x. x) * integral m2 (\y. y)’
 >- (GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [mul_comm] \\
    ‘?r. integral m1 (\x. x) = Normal r’ by PROVE_TAC [integrable_normal_integral] \\
     POP_ORW \\
     HO_MATCH_MP_TAC integral_cmul >> art [])
 >> Rewr'
 >> Know ‘(\x. x) IN measurable Borel Borel’
 >- (rw [IN_MEASURABLE, SIGMA_ALGEBRA_BOREL, IN_FUNSET, PREIMAGE_def] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> rw [SIGMA_ALGEBRA_BOREL] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_SPACE >> rw [SIGMA_ALGEBRA_BOREL])
 >> DISCH_TAC
(* applying integral_distr, twice *)
 >> Know ‘integral p X = integral m1 (\x. x)’
 >- (MP_TAC (ISPECL [“p :'a m_space”, “Borel”, “X :'a -> extreal”,
                     “(\x. x) :extreal -> extreal”] integral_distr) \\
     RW_TAC std_ss [Abbr ‘m1’, SIGMA_ALGEBRA_BOREL, o_DEF, ETA_AX])
 >> Rewr'
 >> Know ‘integral p Y = integral m2 (\y. y)’
 >- (MP_TAC (ISPECL [“p :'a m_space”, “Borel”, “Y :'a -> extreal”,
                     “(\x. x) :extreal -> extreal”] integral_distr) \\
     RW_TAC std_ss [Abbr ‘m2’, SIGMA_ALGEBRA_BOREL, o_DEF, ETA_AX])
 >> Rewr
QED

(* An easy corollary of Theorem 3.3.3 *)
Theorem indep_vars_imp_uncorrelated :
    !p X Y. prob_space p /\ real_random_variable X p /\ real_random_variable Y p /\
            finite_second_moments p X /\ finite_second_moments p Y /\
            indep_rv p X Y Borel Borel ==> uncorrelated p X Y
Proof
    RW_TAC std_ss [uncorrelated_def]
 >> MATCH_MP_TAC indep_vars_expectation >> art []
 >> CONJ_TAC (* 2 subgoals, same tactics *)
 >> MATCH_MP_TAC finite_second_moments_imp_integrable >> art []
QED

Theorem pairwise_indep_vars_imp_uncorrelated :
    !p X A (J :'index set). prob_space p /\
           (!i. i IN J ==> real_random_variable (X i) p) /\
           (!i. i IN J ==> finite_second_moments p (X i)) /\
            pairwise_indep_vars p X (\n. Borel) J ==>
            uncorrelated_vars p X J
Proof
    RW_TAC std_ss [pairwise_indep_vars_def, uncorrelated_vars_def]
 >> MATCH_MP_TAC indep_vars_imp_uncorrelated
 >> ASM_SIMP_TAC std_ss []
QED

(* another version of variance_sum for pairwise independent r.v.'s *)
Theorem variance_sum' :
    !p X (J :'index set).
          prob_space p /\ FINITE J /\ pairwise_indep_vars p X (\n. Borel) J /\
         (!i. i IN J ==> real_random_variable (X i) p) /\
         (!i. i IN J ==> finite_second_moments p (X i)) ==>
         (variance p (\x. SIGMA (\n. X n x) J) = SIGMA (\n. variance p (X n)) J)
Proof
    rpt STRIP_TAC
 >> Know ‘uncorrelated_vars p X J’
 >- (rw [uncorrelated_vars_def] \\
     MATCH_MP_TAC indep_vars_imp_uncorrelated >> rw [] \\
     fs [pairwise_indep_vars_def])
 >> DISCH_TAC
 >> MATCH_MP_TAC variance_sum >> art []
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

Theorem prob_div_mul_refl :
  !p A x. prob_space p /\ A IN events p /\ prob p A <> 0 ==>
          x / prob p A * prob p A = x
Proof
  rpt STRIP_TAC
  >> `prob p A <> PosInf /\ prob p A <> NegInf` by METIS_TAC [PROB_FINITE]
  >> `?a. prob p A = Normal a` by METIS_TAC [extreal_cases]
  >> ‘a <> 0’ by METIS_TAC [extreal_of_num_def, extreal_11]
  >> Q.PAT_X_ASSUM ‘prob p A = Normal a’ (ONCE_REWRITE_TAC o wrap)
  >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
  >> MATCH_MP_TAC div_mul_refl >> art []
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
 >- simp[prob_div_mul_refl]
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
 >- simp[prob_div_mul_refl]
 >> Know `prob p (A1 INTER A2 INTER B) / prob p B * prob p B =
          prob p (A1 INTER A2 INTER B)`
 >- simp[prob_div_mul_refl]
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
 >- simp[prob_div_mul_refl]
 >> Know `prob p (B INTER A) / prob p B * prob p B = prob p (B INTER A)`
 >- simp[prob_div_mul_refl] >> rw[]
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
 >- simp[prob_div_mul_refl]
 >> Know `prob p ((A1 DIFF A2) INTER B) / prob p B * prob p B =
          prob p ((A1 DIFF A2) INTER B)`
 >- simp[prob_div_mul_refl]
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
 >- simp[prob_div_mul_refl] >> Rewr'
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
 >> ASM_SIMP_TAC bool_ss [ldiv_eq]
 >> Know `cond_prob p A B * prob p B / prob p A * prob p A =
          cond_prob p A B * prob p B`
 >- simp[ prob_div_mul_refl]
 >> Rewr'
 >> REWRITE_TAC [cond_prob_def]
 >> Know `prob p (A INTER B) / prob p B * prob p B = prob p (A INTER B)`
 >- simp[prob_div_mul_refl] >> Rewr'
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
 >- (GEN_TAC >> simp[prob_div_mul_refl]) >> Rewr'
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

(* ========================================================================= *)
(*  Additional theorems of conditional probabilities on independent events   *)
(* ========================================================================= *)

Theorem indep_alt_cond_prob :
    !p A B. prob_space p /\ A IN events p /\ B IN events p /\ prob p B <> 0 ==>
           (indep p A B <=> cond_prob p A B = prob p A)
Proof
    rw [indep_def]
 >> rw [COND_PROB_MUL_RULE, Once mul_comm]
 >> Suff ‘cond_prob p A B * prob p B = prob p A * prob p B <=>
          prob p B = 0 \/ cond_prob p A B = prob p A’ >- rw []
 >> MATCH_MP_TAC mul_rcancel >> rw [PROB_FINITE]
QED

(* ========================================================================= *)
(*   Probability Density Function                                            *)
(*  (see examples/probability/normal_rvScript.sml for the ‘lborel’ version)  *)
(* ========================================================================= *)

(* extreal version, was: pdf *)
Definition prob_density_function_def :
    prob_density_function p X = RN_deriv (distribution p X) ext_lborel
End
Overload pdf[local] = “prob_density_function”

(* local backward compatibility *)
Theorem pdf_def[local] = prob_density_function_def

Theorem pdf_le_pos :
    !p X x. prob_space p /\ random_variable X p Borel /\
            distribution p X << ext_lborel ==> 0 <= pdf p X x
Proof
    rpt STRIP_TAC
 >> `measure_space (space Borel, subsets Borel, distribution p X)`
       by PROVE_TAC [distribution_prob_space, prob_space_def, SIGMA_ALGEBRA_BOREL]
 >> ASSUME_TAC SIGMA_FINITE_LBOREL
 >> ASSUME_TAC MEASURE_SPACE_LBOREL
 >> MP_TAC (ISPECL [(* m *) ``ext_lborel``,
                    (* v *) ``distribution (p :'a m_space) (X :'a -> extreal)``]
                   Radon_Nikodym')
 >> rw [ext_lborel_def]
 >> fs [pdf_def, RN_deriv_def, ext_lborel_def, SPACE]
 >> SELECT_ELIM_TAC
 >> METIS_TAC [SPACE_BOREL, IN_UNIV]
QED

Theorem expectation_pdf_1 :
    !p X. prob_space p /\ random_variable X p Borel /\
          distribution p X << ext_lborel ==>
          expectation ext_lborel (pdf p X) = 1
Proof
    rpt STRIP_TAC
 >> `prob_space (space Borel, subsets Borel, distribution p X)`
       by PROVE_TAC [distribution_prob_space, SIGMA_ALGEBRA_BOREL]
 >> NTAC 2 (POP_ASSUM MP_TAC) >> KILL_TAC
 >> RW_TAC std_ss [prob_space_def, p_space_def, m_space_def, measure_def,
                   expectation_def]
 >> ASSUME_TAC SIGMA_FINITE_LBOREL
 >> ASSUME_TAC MEASURE_SPACE_LBOREL
 >> MP_TAC (ISPECL [(* m *) ``ext_lborel``,
                    (* v *) ``distribution (p :'a m_space) (X :'a -> extreal)``]
                   Radon_Nikodym')
 >> rw [ext_lborel_def]
 >> fs [pdf_def, RN_deriv_def, SPACE, ext_lborel_def]
 >> SELECT_ELIM_TAC
 >> CONJ_TAC >- METIS_TAC []
 >> Q.X_GEN_TAC `g`
 >> RW_TAC std_ss [density_measure_def]
 >> POP_ASSUM (MP_TAC o Q.SPEC `space Borel`)
 >> Know `space Borel IN subsets Borel`
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SPACE \\
     REWRITE_TAC [SIGMA_ALGEBRA_BOREL])
 >> RW_TAC std_ss []
 >> fs [GSYM ext_lborel_def]
 >> Know `integral ext_lborel g = pos_fn_integral ext_lborel g`
 >- (MATCH_MP_TAC integral_pos_fn >> art [] \\
     rw [ext_lborel_def]) >> Rewr'
 >> Know `pos_fn_integral ext_lborel g =
          pos_fn_integral ext_lborel (\x. g x * indicator_fn (space Borel) x)`
 >- (MATCH_MP_TAC pos_fn_integral_cong \\
     rw [indicator_fn_def, mul_rone, mul_rzero, le_refl, SPACE_BOREL])
 >> DISCH_THEN (art o wrap)
QED

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
