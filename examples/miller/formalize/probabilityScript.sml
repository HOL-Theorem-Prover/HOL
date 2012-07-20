open HolKernel Parse boolLib bossLib arithmeticTheory realTheory
     seqTheory pred_setTheory res_quanTheory listTheory
     rich_listTheory pairTheory combinTheory realLib HurdUseful
     subtypeTheory extra_pred_setTheory extra_boolTheory optionTheory
     extra_realTheory ho_proverTools extra_numTheory
     extra_pred_setTools measureTheory simpLib;

val _ = new_theory "probability";

infixr 0 ++ << || ORELSEC ## --> THENC;
infix 1 >> |->;

val !! = REPEAT;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;

(* ------------------------------------------------------------------------- *)
(* Tools.                                                                    *)
(* ------------------------------------------------------------------------- *)

val Strip = !! (POP_ASSUM MP_TAC) ++ !! STRIP_TAC;
val Simplify = RW_TAC arith_ss;
val Rewr = DISCH_THEN (REWRITE_TAC o wrap);
val Rewr' = DISCH_THEN (ONCE_REWRITE_TAC o wrap);
val Reverse = Tactical.REVERSE
val Cond =
  DISCH_THEN
  (fn mp_th =>
   let
     val cond = fst (dest_imp (concl mp_th))
   in
     KNOW_TAC cond << [ALL_TAC, DISCH_THEN (MP_TAC o MP mp_th)]
   end);

(* ------------------------------------------------------------------------- *)
(* Basic probability theory definitions.                                     *)
(* ------------------------------------------------------------------------- *)

val events_def = Define `events = measurable_sets`;

val prob_def = Define `prob = measure`;

val prob_preserving_def = Define `prob_preserving = measure_preserving`;

val prob_space_def = Define
  `prob_space p = measure_space p /\ (measure p UNIV = 1)`;

val indep_def = Define
  `indep p a b =
   a IN events p /\ b IN events p /\
   (prob p (a INTER b) = prob p a * prob p b)`;

val indep_families_def = Define
  `indep_families p q r = !s t. s IN q /\ t IN r ==> indep p s t`;

val indep_function_def = Define
  `indep_function p =
   {f |
    indep_families p (IMAGE (PREIMAGE (FST o f)) UNIV)
    (IMAGE (PREIMAGE (SND o f)) (events p))}`;

val probably_def = Define `probably p e = (e IN events p) /\ (prob p e = 1)`;

val possibly_def = Define `possibly p e = (e IN events p) /\ ~(prob p e = 0)`;

(* ------------------------------------------------------------------------- *)
(* Basic probability theorems, leading to:                                   *)
(* 1. s IN events p ==> (prob p (COMPL s) = 1 - prob p s)                    *)
(* ------------------------------------------------------------------------- *)

(* new definitions in terms of prob & events *)

val POSITIVE_PROB = store_thm
  ("POSITIVE_PROB",
   ``!p. positive p = (prob p {} = 0) /\ !s. s IN events p ==> 0 <= prob p s``,
   RW_TAC std_ss [positive_def, prob_def, events_def]);

val INCREASING_PROB = store_thm
  ("INCREASING_PROB",
   ``!p.
       increasing p =
       !s t.
         s IN events p /\ t IN events p /\ s SUBSET t ==>
         prob p s <= prob p t``,
   RW_TAC std_ss [increasing_def, prob_def, events_def]);

val ADDITIVE_PROB = store_thm
  ("ADDITIVE_PROB",
   ``!p.
       additive p =
       !s t.
         s IN events p /\ t IN events p /\ DISJOINT s t ==>
         (prob p (s UNION t) = prob p s + prob p t)``,
   RW_TAC std_ss [additive_def, prob_def, events_def]);

val COUNTABLY_ADDITIVE_PROB = store_thm
  ("COUNTABLY_ADDITIVE_PROB",
   ``!p.
       countably_additive p =
       !f.
         f IN (UNIV -> events p) /\
         (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
         BIGUNION (IMAGE f UNIV) IN events p ==>
         prob p o f sums prob p (BIGUNION (IMAGE f UNIV))``,
   RW_TAC std_ss [countably_additive_def, prob_def, events_def]);

(* properties of prob spaces *)

val PROB_SPACE = store_thm
  ("PROB_SPACE",
   ``!p.
       prob_space p =
       sigma_algebra (events p) /\ positive p /\ countably_additive p /\
       (prob p UNIV = 1)``,
   RW_TAC std_ss [prob_space_def, prob_def, events_def, measure_space_def]
   ++ PROVE_TAC []);

val EVENTS_SIGMA_ALGEBRA = store_thm
  ("EVENTS_SIGMA_ALGEBRA",
   ``!p. prob_space p ==> sigma_algebra (events p)``,
   RW_TAC std_ss [PROB_SPACE]);

val EVENTS_ALGEBRA = store_thm
  ("EVENTS_ALGEBRA",
   ``!p. prob_space p ==> algebra (events p)``,
   PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, EVENTS_SIGMA_ALGEBRA]);

val PROB_EMPTY = store_thm
  ("PROB_EMPTY",
   ``!p. prob_space p ==> (prob p {} = 0)``,
   PROVE_TAC [PROB_SPACE, POSITIVE_PROB]);

val PROB_UNIV = store_thm
  ("PROB_UNIV",
   ``!p. prob_space p ==> (prob p UNIV = 1)``,
   RW_TAC std_ss [PROB_SPACE]);

val PROB_SPACE_POSITIVE = store_thm
  ("PROB_SPACE_POSITIVE",
   ``!p. prob_space p ==> positive p``,
   RW_TAC std_ss [PROB_SPACE]);

val PROB_SPACE_COUNTABLY_ADDITIVE = store_thm
  ("PROB_SPACE_COUNTABLY_ADDITIVE",
   ``!p. prob_space p ==> countably_additive p``,
   RW_TAC std_ss [PROB_SPACE]);

val PROB_SPACE_ADDITIVE = store_thm
  ("PROB_SPACE_ADDITIVE",
   ``!p. prob_space p ==> additive p``,
   PROVE_TAC [PROB_SPACE_COUNTABLY_ADDITIVE, COUNTABLY_ADDITIVE_ADDITIVE,
              PROB_SPACE_POSITIVE, EVENTS_ALGEBRA, events_def]);

val PROB_SPACE_INCREASING = store_thm
  ("PROB_SPACE_INCREASING",
   ``!p. prob_space p ==> increasing p``,
   PROVE_TAC [ADDITIVE_INCREASING, EVENTS_ALGEBRA, PROB_SPACE_ADDITIVE,
              PROB_SPACE_POSITIVE, events_def]);

(* handy theorems for use with MATCH_MP_TAC *)

val PROB_POSITIVE = store_thm
  ("PROB_POSITIVE",
   ``!p s. prob_space p /\ s IN events p ==> 0 <= prob p s``,
   PROVE_TAC [POSITIVE_PROB, PROB_SPACE_POSITIVE]);

val PROB_INCREASING = store_thm
  ("PROB_INCREASING",
   ``!p s t.
       prob_space p /\ s IN events p /\ t IN events p /\ s SUBSET t ==>
       prob p s <= prob p t``,
   PROVE_TAC [INCREASING_PROB, PROB_SPACE_INCREASING]);

val PROB_ADDITIVE = store_thm
  ("PROB_ADDITIVE",
   ``!p s t u.
       prob_space p /\ s IN events p /\ t IN events p /\
       DISJOINT s t /\ (u = s UNION t) ==>
       (prob p u = prob p s + prob p t)``,
   PROVE_TAC [ADDITIVE_PROB, PROB_SPACE_ADDITIVE]);

val PROB_COUNTABLY_ADDITIVE = store_thm
  ("PROB_COUNTABLY_ADDITIVE",
   ``!p s f.
       prob_space p /\ f IN (UNIV -> events p) /\
       (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
       (s = BIGUNION (IMAGE f UNIV)) ==>
       prob p o f sums prob p s``,
   RW_TAC std_ss []
   ++ Suff `BIGUNION (IMAGE f UNIV) IN events p`
   >> PROVE_TAC [COUNTABLY_ADDITIVE_PROB, PROB_SPACE_COUNTABLY_ADDITIVE]
   ++ MATCH_MP_TAC SIGMA_ALGEBRA_ENUM
   ++ PROVE_TAC [EVENTS_SIGMA_ALGEBRA]);

(* more properties of prob_spaces *)

val PROB_COMPL = store_thm
  ("PROB_COMPL",
   ``!p s.
       prob_space p /\ s IN events p ==> (prob p (COMPL s) = 1 - prob p s)``,
   RW_TAC std_ss []
   ++ MP_TAC (Q.SPEC `p` PROB_UNIV)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap o GSYM)
   ++ REWRITE_TAC [prob_def]
   ++ MATCH_MP_TAC MEASURE_COMPL
   ++ PROVE_TAC [events_def, prob_space_def]);

val PROB_INDEP = store_thm
  ("PROB_INDEP",
   ``!p s t u.
       indep p s t /\ (u = s INTER t) ==> (prob p u = prob p s * prob p t)``,
   RW_TAC std_ss [indep_def]);

val PROB_PRESERVING = store_thm
  ("PROB_PRESERVING",
   ``!p1 p2.
       prob_preserving p1 p2 =
       {f |
        f IN measurable (events p1) (events p2) /\
        !s. s IN events p2 ==> (prob p1 (PREIMAGE f s) = prob p2 s)}``,
   RW_TAC std_ss [prob_preserving_def, measure_preserving_def, events_def,
                  prob_def]);

val PROB_PRESERVING_SUBSET = store_thm
  ("PROB_PRESERVING_SUBSET",
   ``!p1 p2 a.
       prob_space p1 /\ prob_space p2 /\ algebra a /\
       (events p2 = sigma a) ==>
       prob_preserving p1 (a, prob p2) SUBSET
       prob_preserving p1 p2``,
   RW_TAC std_ss [prob_space_def, prob_preserving_def, prob_def, events_def]
   ++ PROVE_TAC [MEASURE_PRESERVING_SUBSET]);

val PROB_PRESERVING_LIFT = store_thm
  ("PROB_PRESERVING_LIFT",
   ``!p1 p2 a f.
       prob_space p1 /\ prob_space p2 /\ algebra a /\
       (events p2 = sigma a) /\
       f IN prob_preserving p1 (a, prob p2) ==>
       f IN prob_preserving p1 p2``,
   RW_TAC std_ss [prob_space_def, prob_preserving_def, prob_def, events_def]
   ++ PROVE_TAC [MEASURE_PRESERVING_LIFT]);

val PROB_PRESERVING_UP_LIFT = store_thm
  ("PROB_PRESERVING_UP_LIFT",
   ``!p1 p2 f.
       f IN prob_preserving (a, prob p1) p2 /\
       a SUBSET events p1 ==>
       f IN prob_preserving p1 p2``,
   RW_TAC std_ss [prob_preserving_def, prob_def, events_def]
   ++ PROVE_TAC [MEASURE_PRESERVING_UP_LIFT]);

val PROB_PRESERVING_UP_SUBSET = store_thm
  ("PROB_PRESERVING_UP_SUBSET",
   ``!p1 p2.
       a SUBSET events p1 ==>
       prob_preserving (a, prob p1) p2 SUBSET prob_preserving p1 p2``,
   RW_TAC std_ss [prob_preserving_def, prob_def, events_def]
   ++ PROVE_TAC [MEASURE_PRESERVING_UP_SUBSET]);

val PROB_PRESERVING_UP_SIGMA = store_thm
  ("PROB_PRESERVING_UP_SIGMA",
   ``!p1 p2 a.
       (events p1 = sigma a) ==>
       prob_preserving (a, prob p1) p2 SUBSET prob_preserving p1 p2``,
   RW_TAC std_ss [prob_preserving_def, prob_def, events_def]
   ++ PROVE_TAC [MEASURE_PRESERVING_UP_SIGMA]);

val EVENTS = store_thm
  ("EVENTS",
   ``!a b. events (a, b) = a``,
   RW_TAC std_ss [events_def, measurable_sets_def]);

val PROB = store_thm
  ("PROB",
   ``!a b. prob (a, b) = b``,
   RW_TAC std_ss [prob_def, measure_def]);

val EVENTS_INTER = store_thm
  ("EVENTS_INTER",
   ``!p s t.
       prob_space p /\ s IN events p /\ t IN events p ==>
       s INTER t IN events p``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC ALGEBRA_INTER
   ++ PROVE_TAC [PROB_SPACE, SIGMA_ALGEBRA_ALGEBRA]);

val EVENTS_EMPTY = store_thm
  ("EVENTS_EMPTY",
   ``!p. prob_space p ==> {} IN events p``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC ALGEBRA_EMPTY
   ++ PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, PROB_SPACE]);

val EVENTS_UNIV = store_thm
  ("EVENTS_UNIV",
   ``!p. prob_space p ==> UNIV IN events p``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC ALGEBRA_UNIV
   ++ PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, PROB_SPACE]);

val EVENTS_UNION = store_thm
  ("EVENTS_UNION",
   ``!p s t.
       prob_space p /\ s IN events p /\ t IN events p ==>
       s UNION t IN events p``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC ALGEBRA_UNION
   ++ PROVE_TAC [PROB_SPACE, SIGMA_ALGEBRA_ALGEBRA]);

val INDEP_EMPTY = store_thm
  ("INDEP_EMPTY",
   ``!p s. prob_space p /\ s IN events p ==> indep p {} s``,
   RW_TAC std_ss [indep_def, EVENTS_EMPTY, PROB_EMPTY, INTER_EMPTY]
   ++ RW_TAC real_ss []);

val INDEP_UNIV = store_thm
  ("INDEP_UNIV",
   ``!p s. prob_space p /\ s IN events p ==> indep p UNIV s``,
   RW_TAC std_ss [indep_def, EVENTS_UNIV, PROB_UNIV, INTER_UNIV]
   ++ RW_TAC real_ss []);

val EVENTS_DIFF = store_thm
  ("EVENTS_DIFF",
   ``!p s t.
       prob_space p /\ s IN events p /\ t IN events p ==>
       s DIFF t IN events p``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC ALGEBRA_DIFF
   ++ PROVE_TAC [PROB_SPACE, SIGMA_ALGEBRA_ALGEBRA]);

val EVENTS_COMPL = store_thm
  ("EVENTS_COMPL",
   ``!p s. prob_space p /\ s IN events p ==> COMPL s IN events p``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC ALGEBRA_COMPL
   ++ PROVE_TAC [PROB_SPACE, SIGMA_ALGEBRA_ALGEBRA]);

val EVENTS_COUNTABLE_UNION = store_thm
  ("EVENTS_COUNTABLE_UNION",
   ``!p c.
       prob_space p /\ c SUBSET events p /\ countable c ==>
       BIGUNION c IN events p``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION
   ++ RW_TAC std_ss [EVENTS_SIGMA_ALGEBRA]);

val PROB_ZERO_UNION = store_thm
  ("PROB_ZERO_UNION",
   ``!p s t.
       prob_space p /\ s IN events p /\ t IN events p /\ (prob p t = 0) ==>
       (prob p (s UNION t) = prob p s)``,
   RW_TAC std_ss []
   ++ Know `t DIFF s IN events p`
   >> (MATCH_MP_TAC EVENTS_DIFF
       ++ RW_TAC std_ss [])
   ++ STRIP_TAC
   ++ Know `prob p (t DIFF s) = 0`
   >> (ONCE_REWRITE_TAC [GSYM REAL_LE_ANTISYM]
       ++ Reverse CONJ_TAC >> PROVE_TAC [PROB_POSITIVE]
       ++ Q.PAT_ASSUM `prob p t = 0` (ONCE_REWRITE_TAC o wrap o SYM)
       ++ MATCH_MP_TAC PROB_INCREASING
       ++ RW_TAC std_ss [DIFF_SUBSET])
   ++ STRIP_TAC
   ++ Suff `prob p (s UNION t) = prob p s + prob p (t DIFF s)`
   >> RW_TAC real_ss []
   ++ MATCH_MP_TAC PROB_ADDITIVE
   ++ RW_TAC std_ss []
   ++ PSET_TAC [EXTENSION]
   ++ PROVE_TAC []);

val PROB_EQ_COMPL = store_thm
  ("PROB_EQ_COMPL",
   ``!p s t.
       prob_space p /\ s IN events p /\ t IN events p /\
       (prob p (COMPL s) = prob p (COMPL t)) ==>
       (prob p s = prob p t)``,
   RW_TAC std_ss []
   ++ Suff `1 - prob p s = 1 - prob p t` >> REAL_ARITH_TAC
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [PROB_COMPL]);

val PROB_ONE_INTER = store_thm
  ("PROB_ONE_INTER",
   ``!p s t.
       prob_space p /\ s IN events p /\ t IN events p /\ (prob p t = 1) ==>
       (prob p (s INTER t) = prob p s)``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC PROB_EQ_COMPL
   ++ RW_TAC std_ss [EVENTS_INTER, COMPL_INTER]
   ++ MATCH_MP_TAC PROB_ZERO_UNION
   ++ RW_TAC std_ss [PROB_COMPL, EVENTS_COMPL]
   ++ REAL_ARITH_TAC);

val EVENTS_COUNTABLE_INTER = store_thm
  ("EVENTS_COUNTABLE_INTER",
   ``!p c.
       prob_space p /\ c SUBSET events p /\ countable c ==>
       BIGINTER c IN events p``,
   RW_TAC std_ss []
   ++ Know `BIGINTER c = COMPL (COMPL (BIGINTER c))`
   >> RW_TAC std_ss [COMPL_COMPL]
   ++ Rewr'
   ++ MATCH_MP_TAC EVENTS_COMPL
   ++ RW_TAC std_ss [COMPL_BIGINTER]
   ++ MATCH_MP_TAC EVENTS_COUNTABLE_UNION
   ++ Q.PAT_ASSUM `c SUBSET events p` MP_TAC
   ++ RW_TAC std_ss [COUNTABLE_IMAGE, SUBSET_DEF, IN_IMAGE]
   ++ PROVE_TAC [EVENTS_COMPL]);

val ABS_PROB = store_thm
  ("ABS_PROB",
   ``!p s. prob_space p /\ s IN events p ==> (abs (prob p s) = prob p s)``,
   RW_TAC std_ss [abs]
   ++ PROVE_TAC [PROB_POSITIVE]);

val PROB_COMPL_LE1 = store_thm
  ("PROB_COMPL_LE1",
   ``!p s r.
       prob_space p /\ s IN events p ==>
       (prob p (COMPL s) <= r = 1 - r <= prob p s)``,
   RW_TAC std_ss [PROB_COMPL]
   ++ REAL_ARITH_TAC);

val PROB_LE_1 = store_thm
  ("PROB_LE_1",
   ``!p s. prob_space p /\ s IN events p ==> prob p s <= 1``,
   RW_TAC std_ss []
   ++ Suff `0 <= 1 - prob p s` >> REAL_ARITH_TAC
   ++ RW_TAC std_ss [GSYM PROB_COMPL]
   ++ RW_TAC std_ss [EVENTS_COMPL, PROB_POSITIVE]);

val PROB_EQ_BIGUNION_IMAGE = store_thm
  ("PROB_EQ_BIGUNION_IMAGE",
   ``!p.
       prob_space p /\ f IN (UNIV -> events p) /\ g IN (UNIV -> events p) /\
       (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
       (!m n. ~(m = n) ==> DISJOINT (g m) (g n)) /\
       (!n : num. prob p (f n) = prob p (g n)) ==>
       (prob p (BIGUNION (IMAGE f UNIV)) = prob p (BIGUNION (IMAGE g UNIV)))``,
   RW_TAC std_ss []
   ++ Know `prob p o f sums prob p (BIGUNION (IMAGE f UNIV))`
   >> PROVE_TAC [PROB_COUNTABLY_ADDITIVE]
   ++ Know `prob p o g sums prob p (BIGUNION (IMAGE g UNIV))`
   >> PROVE_TAC [PROB_COUNTABLY_ADDITIVE]
   ++ Suff `prob p o f = prob p o g`
   >> (RW_TAC std_ss []
       ++ PROVE_TAC [SUM_UNIQ])
   ++ FUN_EQ_TAC
   ++ RW_TAC std_ss [o_THM]);

val PROB_FINITELY_ADDITIVE = store_thm
  ("PROB_FINITELY_ADDITIVE",
   ``!p s f n.
       prob_space p /\ f IN ((count n) -> events p) /\
       (!a b. a < n /\ b < n /\ ~(a = b) ==> DISJOINT (f a) (f b)) /\
       (s = BIGUNION (IMAGE f (count n))) ==>
       (sum (0, n) (prob p o f) = prob p s)``,
   RW_TAC std_ss [IN_FUNSET, IN_COUNT]
   ++ Suff
      `(prob p o (\m. if m < n then f m else {})) sums
       prob p (BIGUNION (IMAGE f (count n))) /\
       (prob p o (\m. if m < n then f m else {})) sums
       sum (0, n) (prob p o f)`
   >> PROVE_TAC [SUM_UNIQ]
   ++ Reverse CONJ_TAC
   >> (Know
       `sum (0,n) (prob p o f) =
        sum (0,n) (prob p o (\m. (if m < n then f m else {})))`
       >> (MATCH_MP_TAC SUM_EQ
           ++ RW_TAC arith_ss [o_THM])
       ++ Rewr
       ++ MATCH_MP_TAC SER_0
       ++ RW_TAC arith_ss [o_THM, PROB_EMPTY])
   ++ Know
      `BIGUNION (IMAGE f (count n)) =
       BIGUNION (IMAGE (\m. (if m < n then f m else {})) UNIV)`
   >> (SET_EQ_TAC
       ++ RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_COUNT, IN_UNIV]
       ++ PROVE_TAC [NOT_IN_EMPTY])
   ++ Rewr
   ++ MATCH_MP_TAC PROB_COUNTABLY_ADDITIVE
   ++ BasicProvers.NORM_TAC std_ss
      [IN_FUNSET, IN_UNIV, DISJOINT_EMPTY, EVENTS_EMPTY]);

val ABS_1_MINUS_PROB = store_thm
  ("ABS_1_MINUS_PROB",
   ``!p s.
       prob_space p /\ s IN events p /\ ~(prob p s = 0) ==>
       abs (1 - prob p s) < 1``,
   RW_TAC std_ss []
   ++ Know `0 <= prob p s` >> PROVE_TAC [PROB_POSITIVE]
   ++ Know `prob p s <= 1` >> PROVE_TAC [PROB_LE_1]
   ++ RW_TAC std_ss [abs]
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ REAL_ARITH_TAC);

val PROB_INCREASING_UNION = store_thm
  ("PROB_INCREASING_UNION",
   ``!p s f.
       prob_space p /\ f IN (UNIV -> events p) /\
       (!n. f n SUBSET f (SUC n)) /\ (s = BIGUNION (IMAGE f UNIV)) ==>
       prob p o f --> prob p s``,
   RW_TAC std_ss [prob_space_def, events_def, prob_def, MONOTONE_CONVERGENCE]);

val PROB_SUBADDITIVE = store_thm
  ("PROB_SUBADDITIVE",
   ``!p s t u.
       prob_space p /\ t IN events p /\ u IN events p /\ (s = t UNION u) ==>
       prob p s <= prob p t + prob p u``,
   RW_TAC std_ss []
   ++ Know `t UNION u = t UNION (u DIFF t)`
   >> (SET_EQ_TAC
       ++ PSET_TAC []
       ++ PROVE_TAC [])
   ++ Rewr
   ++ Know `u DIFF t IN events p`
   >> PROVE_TAC [EVENTS_DIFF]
   ++ STRIP_TAC
   ++ Know `prob p (t UNION (u DIFF t)) = prob p t + prob p (u DIFF t)`
   >> (MATCH_MP_TAC PROB_ADDITIVE
       ++ PSET_TAC [DISJOINT_ALT])
   ++ Rewr
   ++ MATCH_MP_TAC REAL_LE_LADD_IMP
   ++ MATCH_MP_TAC PROB_INCREASING
   ++ PSET_TAC []);

val PROB_COUNTABLY_SUBADDITIVE = store_thm
  ("PROB_COUNTABLY_SUBADDITIVE",
   ``!p f.
       prob_space p /\ (IMAGE f UNIV) SUBSET events p /\
       summable (prob p o f) ==>
       prob p (BIGUNION (IMAGE f UNIV)) <= suminf (prob p o f)``,
   RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV]
   ++ Know `(prob p o f) sums suminf (prob p o f)`
   >> PROVE_TAC [SUMMABLE_SUM]
   ++ RW_TAC std_ss [sums]
   ++ Know
      `prob p o (\n. BIGUNION (IMAGE f (count n))) -->
       prob p (BIGUNION (IMAGE f UNIV))`
   >> (MATCH_MP_TAC PROB_INCREASING_UNION
       ++ RW_TAC std_ss [IN_FUNSET, IN_UNIV] <<
       [MATCH_MP_TAC EVENTS_COUNTABLE_UNION
        ++ RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, COUNTABLE_IMAGE,
                          COUNTABLE_COUNT]
        ++ PROVE_TAC [],
        PSET_TAC []
        ++ PROVE_TAC [LT_SUC],
        SET_EQ_TAC
        ++ RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_UNIV, IN_COUNT]
        ++ Reverse EQ_TAC >> PROVE_TAC []
        ++ RW_TAC std_ss []
        ++ Q.EXISTS_TAC `SUC x'`
        ++ Q.EXISTS_TAC `x'`
        ++ RW_TAC arith_ss []])
   ++ STRIP_TAC
   ++ MATCH_MP_TAC SEQ_LE
   ++ Q.EXISTS_TAC `prob p o (\n. BIGUNION (IMAGE f (count n)))`
   ++ Q.EXISTS_TAC `(\n. sum (0,n) (prob p o f))`
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `0`
   ++ RW_TAC arith_ss [o_THM]
   ++ Induct_on `n`
   >> RW_TAC std_ss [o_THM, COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY, PROB_EMPTY,
                     sum, REAL_LE_REFL]
   ++ RW_TAC std_ss [o_THM, COUNT_SUC, IMAGE_INSERT, BIGUNION_INSERT, sum]
   ++ ONCE_REWRITE_TAC [REAL_ADD_SYM]
   ++ RW_TAC arith_ss []
   ++ Suff
      `prob p (f n UNION BIGUNION (IMAGE f (count n))) <=
       prob p (f n) + prob p (BIGUNION (IMAGE f (count n)))`
   >> (POP_ASSUM MP_TAC
       ++ REAL_ARITH_TAC)
   ++ MATCH_MP_TAC PROB_SUBADDITIVE
   ++ RW_TAC std_ss [] >> PROVE_TAC []
   ++ MATCH_MP_TAC EVENTS_COUNTABLE_UNION
   ++ RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT, COUNTABLE_IMAGE,
                     COUNTABLE_COUNT]
   ++ PROVE_TAC []);

val PROB_COUNTABLY_ZERO = store_thm
  ("PROB_COUNTABLY_ZERO",
   ``!p c.
       prob_space p /\ countable c /\ c SUBSET events p /\
       (!x. x IN c ==> (prob p x = 0)) ==>
       (prob p (BIGUNION c) = 0)``,
   RW_TAC std_ss [COUNTABLE_ENUM]
   >> RW_TAC std_ss [BIGUNION_EMPTY, PROB_EMPTY]
   ++ Know `(!n. prob p (f n) = 0) /\ (!n. f n IN events p)`
   >> (FULL_SIMP_TAC std_ss [IN_IMAGE, IN_UNIV, SUBSET_DEF]
       ++ PROVE_TAC [])
   ++ NTAC 2 (POP_ASSUM K_TAC)
   ++ STRIP_TAC
   ++ ONCE_REWRITE_TAC [GSYM REAL_LE_ANTISYM]
   ++ Reverse CONJ_TAC
   >> (MATCH_MP_TAC PROB_POSITIVE
       ++ RW_TAC std_ss []
       ++ MATCH_MP_TAC EVENTS_COUNTABLE_UNION
       ++ RW_TAC std_ss [COUNTABLE_IMAGE_NUM, SUBSET_DEF, IN_IMAGE, IN_UNIV]
       ++ RW_TAC std_ss [])
   ++ Know `(prob p o f) sums 0`
   >> (Know `0 = sum (0, 0) (prob p o f)` >> RW_TAC std_ss [sum]
       ++ Rewr'
       ++ MATCH_MP_TAC SER_0
       ++ RW_TAC std_ss [o_THM])
   ++ RW_TAC std_ss [SUMS_EQ]
   ++ POP_ASSUM (REWRITE_TAC o wrap o SYM)
   ++ MATCH_MP_TAC PROB_COUNTABLY_SUBADDITIVE
   ++ RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV]
   ++ RW_TAC std_ss []);

val INDEP_SYM = store_thm
  ("INDEP_SYM",
   ``!p a b. prob_space p /\ indep p a b ==> indep p b a``,
   RW_TAC std_ss [indep_def]
   ++ PROVE_TAC [REAL_MUL_SYM, INTER_COMM]);

val INDEP_REFL = store_thm
  ("INDEP_REFL",
   ``!p a.
       prob_space p /\ a IN events p ==>
       (indep p a a = (prob p a = 0) \/ (prob p a = 1))``,
   RW_TAC std_ss [indep_def, INTER_IDEMPOT]
   ++ PROVE_TAC [REAL_MUL_IDEMPOT]);

val _ = export_theory ();
