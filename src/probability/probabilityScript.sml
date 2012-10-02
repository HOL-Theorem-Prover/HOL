(* ------------------------------------------------------------------------- *)
(* Probability Theory                                                        *)
(* Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar                         *)
(* HVG Group, Concordia University, Montreal                                 *)
(* ------------------------------------------------------------------------- *)
(* Based on the work of Aaron Coble, Cambridge University                    *)
(* ------------------------------------------------------------------------- *)

(* interactive mode
app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
    	  "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory",
	  "transcTheory", "rich_listTheory", "pairTheory",
	  "combinTheory", "realLib", "optionTheory", "real_sigmaTheory",
	  "util_probTheory", "extrealTheory", "measureTheory", "lebesgueTheory"];
quietdec := true;
*)

open HolKernel Parse boolLib bossLib arithmeticTheory realTheory prim_recTheory
     seqTheory pred_setTheory res_quanTheory res_quanTools listTheory transcTheory
     rich_listTheory pairTheory combinTheory realLib  optionTheory
     real_sigmaTheory util_probTheory extrealTheory measureTheory lebesgueTheory;

val _ = new_theory "probability";

infixr 0 ++ << || THENC ORELSEC ORELSER ##;
infix 1 >>;

val op!! = op REPEAT;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;

val REVERSE = Tactical.REVERSE;

val S_TAC = !! (POP_ASSUM MP_TAC) ++ !! RESQ_STRIP_TAC;
val Strip = S_TAC;

fun K_TAC _ = ALL_TAC;
val KILL_TAC = POP_ASSUM_LIST K_TAC;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;
val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);

fun wrap a = [a];
val Rewr = DISCH_THEN (REWRITE_TAC o wrap);
val Rewr' = DISCH_THEN (ONCE_REWRITE_TAC o wrap);


(*
 interactive mode
quietdec := false;
*)

(* ------------------------------------------------------------------------- *)
(* Basic probability theory definitions.                                     *)
(* ------------------------------------------------------------------------- *)

val p_space_def = Define `p_space = m_space`;

val events_def = Define `events = measurable_sets`;

val prob_def = Define `prob = measure`;

val prob_space_def = Define
  `prob_space p = measure_space p /\ (measure p (p_space p) = 1)`;

val indep_def = Define
  `indep p a b =
   a IN events p /\ b IN events p /\
   (prob p (a INTER b) = prob p a * prob p b)`;

val probably_def = Define `probably p e = (e IN events p) /\ (prob p e = 1)`;

val possibly_def = Define `possibly p e = (e IN events p) /\ ~(prob p e = 0)`;

val random_variable_def = Define
   `random_variable X p s = prob_space p /\ X IN measurable (p_space p, events p) s`;

val real_random_variable_def = Define
   `real_random_variable X p = prob_space p /\
                              (!x. x IN p_space p ==> X x <> NegInf /\ X x <> PosInf) /\
                              X IN measurable (p_space p, events p) Borel`;

val distribution_def = Define
   `distribution p X = (\s. prob p ((PREIMAGE X s) INTER (p_space p)))`;

val joint_distribution_def = Define
   `joint_distribution p X Y = (\a. prob p (PREIMAGE (\x. (X x, Y x)) a INTER p_space p))`;

val joint_distribution3_def = Define
   `joint_distribution3 p X Y Z = (\a. prob p (PREIMAGE (\x. (X x,Y x, Z x)) a INTER p_space p))`;

val conditional_distribution_def = Define
   `conditional_distribution p X Y a b = joint_distribution p X Y (a CROSS b) / distribution p Y b `;

val expectation_def = Define
   `expectation = integral`;

val conditional_expectation_def = Define
   `conditional_expectation p X s =
	@f. real_random_variable f p /\
	    !g. g IN s ==>
		(integral p (\x. f x * indicator_fn g x) =
		 integral p (\x. X x * indicator_fn g x))`;

val conditional_prob_def = Define
   `conditional_prob p e1 e2 = conditional_expectation p (indicator_fn e1) e2`;

val rv_conditional_expectation_def = Define
   `rv_conditional_expectation p s X Y =
        conditional_expectation p X (IMAGE (\a. (PREIMAGE Y a) INTER p_space p) (subsets s))`;

val indep_rv_def = Define `indep_rv p X Y s t = !A B. (A IN subsets s) /\ (B IN subsets t)
    ==> indep p (PREIMAGE X A) (PREIMAGE Y B)`;

val uniform_distribution_def = Define
   `uniform_distribution p X s = (\a. (&CARD a / &CARD (space s)):real)`;

(* ------------------------------------------------------------------------- *)
(* Basic probability theorems, leading to:                                   *)
(* 1. s IN events p ==> (prob p (COMPL s) = 1 - prob p s)                    *)
(* ------------------------------------------------------------------------- *)

val POSITIVE_PROB = store_thm
  ("POSITIVE_PROB", ``!p. positive p = (prob p {} = 0) /\ !s. s IN events p
         ==> 0 <= prob p s``,
   RW_TAC std_ss [positive_def, prob_def, events_def]);

val INCREASING_PROB = store_thm
  ("INCREASING_PROB", ``!p. increasing p = !s t. s IN events p /\ t IN events p /\ s SUBSET t
         ==> prob p s <= prob p t``,
   RW_TAC std_ss [increasing_def, prob_def, events_def]);

val ADDITIVE_PROB = store_thm
  ("ADDITIVE_PROB", ``!p. additive p = !s t. s IN events p /\ t IN events p /\ DISJOINT s t
         ==> (prob p (s UNION t) = prob p s + prob p t)``,
   RW_TAC std_ss [additive_def, prob_def, events_def]);

val COUNTABLY_ADDITIVE_PROB = store_thm
  ("COUNTABLY_ADDITIVE_PROB", ``!p. countably_additive p =
       !f. f IN (UNIV -> events p) /\ (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
           BIGUNION (IMAGE f UNIV) IN events p ==>
          prob p o f sums (prob p (BIGUNION (IMAGE f UNIV)))``,
   RW_TAC std_ss [countably_additive_def, prob_def, events_def]);

val PROB_SPACE = store_thm
 ("PROB_SPACE", ``!p. prob_space p = sigma_algebra (p_space p, events p) /\ positive p /\
                 countably_additive p /\ (prob p (p_space p) = 1)``,
   RW_TAC std_ss [prob_space_def, prob_def, events_def, measure_space_def, p_space_def]
   ++ PROVE_TAC []);

val EVENTS_SIGMA_ALGEBRA = store_thm
  ("EVENTS_SIGMA_ALGEBRA",
   ``!p. prob_space p ==> sigma_algebra (p_space p, events p)``,
   RW_TAC std_ss [PROB_SPACE]);

val EVENTS_ALGEBRA = store_thm
  ("EVENTS_ALGEBRA",
   ``!p. prob_space p ==> algebra (p_space p, events p)``,
   PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, EVENTS_SIGMA_ALGEBRA]);

val PROB_EMPTY = store_thm
  ("PROB_EMPTY",
   ``!p. prob_space p ==> (prob p {} = 0)``,
   PROVE_TAC [PROB_SPACE, POSITIVE_PROB]);

val PROB_UNIV = store_thm
  ("PROB_UNIV",
   ``!p. prob_space p ==> (prob p (p_space p) = 1)``,
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
              PROB_SPACE_POSITIVE, EVENTS_ALGEBRA, events_def, p_space_def]);

val PROB_SPACE_INCREASING = store_thm
  ("PROB_SPACE_INCREASING",
   ``!p. prob_space p ==> increasing p``,
   PROVE_TAC [ADDITIVE_INCREASING, EVENTS_ALGEBRA, PROB_SPACE_ADDITIVE,
              PROB_SPACE_POSITIVE, events_def, p_space_def]);

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
       prob p o f sums (prob p s)``,
   RW_TAC std_ss []
   ++ Suff `BIGUNION (IMAGE f UNIV) IN events p`
   >> PROVE_TAC [COUNTABLY_ADDITIVE_PROB, PROB_SPACE_COUNTABLY_ADDITIVE]
   ++ (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
	Q.SPECL [`(p_space p, events p)`,`f`]) SIGMA_ALGEBRA_ENUM
   ++ PROVE_TAC [EVENTS_SIGMA_ALGEBRA]);

val PROB_COMPL = store_thm
 ("PROB_COMPL", ``!p s. prob_space p /\ s IN events p
       ==> (prob p (p_space p DIFF s) = 1 - prob p s)``,
  METIS_TAC [MEASURE_COMPL,prob_space_def,events_def,prob_def,p_space_def]);

val PROB_INDEP = store_thm
("PROB_INDEP", ``!p s t u. indep p s t /\ (u = s INTER t)
       ==> (prob p u = prob p s * prob p t)``,
  RW_TAC std_ss [indep_def]);

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
("EVENTS_INTER", ``!p s t. prob_space p /\ s IN events p /\ t IN events p
                    ==> s INTER t IN events p``,
  RW_TAC std_ss []
  ++ (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
      Q.SPEC `(p_space p, events p)`) ALGEBRA_INTER
  ++ PROVE_TAC [PROB_SPACE, SIGMA_ALGEBRA_ALGEBRA]);

val EVENTS_EMPTY = store_thm
("EVENTS_EMPTY", ``!p. prob_space p ==> {} IN events p``,
  RW_TAC std_ss []
  ++ (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
      Q.SPEC `(p_space p, events p)`) ALGEBRA_EMPTY
  ++ PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, PROB_SPACE]);

val EVENTS_SPACE = store_thm
("EVENTS_SPACE", ``!p. prob_space p ==> (p_space p) IN events p``,
  RW_TAC std_ss []
  ++ (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
      Q.SPEC `(p_space p, events p)`) ALGEBRA_SPACE
  ++ PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, PROB_SPACE]);

val EVENTS_UNION = store_thm
("EVENTS_UNION", ``!p s t. prob_space p /\ s IN events p /\ t IN events p
                    ==> s UNION t IN events p``,
  RW_TAC std_ss []
  ++ (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
      Q.SPEC `(p_space p, events p)`) ALGEBRA_UNION
  ++ PROVE_TAC [PROB_SPACE, SIGMA_ALGEBRA_ALGEBRA]);

val INDEP_EMPTY = store_thm
("INDEP_EMPTY", ``!p s. prob_space p /\ s IN events p ==> indep p {} s``,
  RW_TAC real_ss [indep_def, EVENTS_EMPTY, PROB_EMPTY, INTER_EMPTY]);

val INTER_PSPACE = store_thm
("INTER_PSPACE", ``!p s. prob_space p /\ s IN events p
                   ==> (p_space p INTER s = s)``,
  RW_TAC std_ss [PROB_SPACE, SIGMA_ALGEBRA, space_def, subsets_def, subset_class_def, SUBSET_DEF]
  ++ RW_TAC std_ss [Once EXTENSION, IN_INTER]
  ++ PROVE_TAC []);

val INDEP_SPACE = store_thm
("INDEP_SPACE", ``!p s. prob_space p /\ s IN events p ==> indep p (p_space p) s``,
  RW_TAC real_ss [indep_def, EVENTS_SPACE, PROB_UNIV, INTER_PSPACE]);

val EVENTS_DIFF = store_thm
("EVENTS_DIFF", ``!p s t. prob_space p /\ s IN events p /\ t IN events p
                    ==> s DIFF t IN events p``,
  RW_TAC std_ss []
  ++ (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
      Q.SPEC `(p_space p, events p)`) ALGEBRA_DIFF
  ++ PROVE_TAC [PROB_SPACE, SIGMA_ALGEBRA_ALGEBRA]);

val EVENTS_COMPL = store_thm
("EVENTS_COMPL", ``!p s. prob_space p /\ s IN events p
                    ==> (p_space p) DIFF s IN events p``,
  RW_TAC std_ss []
  ++ (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
      Q.SPEC `(p_space p, events p)`) ALGEBRA_COMPL
  ++ PROVE_TAC [PROB_SPACE, SIGMA_ALGEBRA_ALGEBRA]);

val EVENTS_COUNTABLE_UNION = store_thm
("EVENTS_COUNTABLE_UNION", ``!p c. prob_space p /\ c SUBSET events p /\ countable c
                              ==> BIGUNION c IN events p``,
  RW_TAC std_ss []
  ++ (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
      Q.SPEC `(p_space p, events p)`) SIGMA_ALGEBRA_COUNTABLE_UNION
  ++ RW_TAC std_ss [EVENTS_SIGMA_ALGEBRA]);

val PROB_ZERO_UNION = store_thm
("PROB_ZERO_UNION", ``!p s t. prob_space p /\ s IN events p /\ t IN events p /\ (prob p t = 0)
                       ==> (prob p (s UNION t) = prob p s)``,
  RW_TAC std_ss []
  ++ Know `t DIFF s IN events p`
  >> (MATCH_MP_TAC EVENTS_DIFF
      ++ RW_TAC std_ss [])
  ++ STRIP_TAC
  ++ Know `prob p (t DIFF s) = 0`
  >> (ONCE_REWRITE_TAC [GSYM REAL_LE_ANTISYM]
      ++ REVERSE CONJ_TAC >> PROVE_TAC [PROB_POSITIVE]
      ++ Q.PAT_ASSUM `prob p t = 0` (ONCE_REWRITE_TAC o wrap o SYM)
      ++ MATCH_MP_TAC PROB_INCREASING
      ++ RW_TAC std_ss [DIFF_SUBSET])
  ++ STRIP_TAC
  ++ Suff `prob p (s UNION t) = prob p s + prob p (t DIFF s)`
  >> RW_TAC real_ss []
  ++ MATCH_MP_TAC PROB_ADDITIVE
  ++ RW_TAC std_ss [DISJOINT_DEF, DIFF_DEF, EXTENSION, IN_UNION, IN_DIFF, NOT_IN_EMPTY, IN_INTER]
  ++ PROVE_TAC []);

val PROB_EQ_COMPL = store_thm
("PROB_EQ_COMPL", ``!p s t. prob_space p /\ s IN events p /\ t IN events p /\
                           (prob p (p_space p DIFF s) = prob p (p_space p DIFF t))
                             ==> (prob p s = prob p t)``,
  RW_TAC std_ss []
  ++ Know `1 - prob p s = 1 - prob p t`
  >> (POP_ASSUM MP_TAC
      ++ RW_TAC std_ss [PROB_COMPL])
  ++ REAL_ARITH_TAC);

val PROB_ONE_INTER = store_thm
("PROB_ONE_INTER", ``!p s t. prob_space p /\ s IN events p /\ t IN events p /\ (prob p t = 1)
                         ==> (prob p (s INTER t) = prob p s)``,
  RW_TAC std_ss []
  ++ MATCH_MP_TAC PROB_EQ_COMPL
  ++ RW_TAC std_ss [EVENTS_INTER]
  ++ Know `p_space p DIFF s INTER t = (p_space p DIFF s) UNION (p_space p DIFF t)`
  >> (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_UNION, IN_DIFF]
      ++ DECIDE_TAC)
  ++ RW_TAC std_ss [] ++ POP_ASSUM (K ALL_TAC)
  ++ MATCH_MP_TAC PROB_ZERO_UNION
  ++ RW_TAC std_ss [PROB_COMPL, EVENTS_COMPL]
  ++ RW_TAC real_ss []);

val EVENTS_COUNTABLE_INTER = store_thm
("EVENTS_COUNTABLE_INTER",
 ``!p c. prob_space p /\ c SUBSET events p /\ countable c /\ (~(c={}))
                               ==> BIGINTER c IN events p``,
  RW_TAC std_ss []
  ++ Know `BIGINTER c = p_space p DIFF (p_space p DIFF (BIGINTER c))`
  >> (ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_DIFF, LEFT_AND_OVER_OR, IN_BIGINTER]
      ++ FULL_SIMP_TAC std_ss [PROB_SPACE, SIGMA_ALGEBRA, subset_class_def,
                               subsets_def, space_def, SUBSET_DEF]
      ++ EQ_TAC
      >> (Know `(c = {}) \/ ?x t. (c = x INSERT t) /\ ~(x IN t)` >> PROVE_TAC [SET_CASES]
          ++ RW_TAC std_ss []
          ++ PROVE_TAC [IN_INSERT])
      ++ PROVE_TAC [])
  ++ Rewr'
  ++ MATCH_MP_TAC EVENTS_COMPL
  ++ Know `p_space p DIFF BIGINTER c = BIGUNION (IMAGE (\s. p_space p DIFF s) c)`
  >> (ONCE_REWRITE_TAC [EXTENSION]
      ++ RW_TAC std_ss [IN_DIFF, IN_BIGUNION, IN_IMAGE, IN_BIGINTER]
      ++ EQ_TAC
      >> (RW_TAC std_ss [] ++ Q.EXISTS_TAC `p_space p DIFF P`
          ++ RW_TAC std_ss [IN_DIFF] ++ Q.EXISTS_TAC `P`
          ++ RW_TAC std_ss [])
      ++ RW_TAC std_ss []
      >> FULL_SIMP_TAC std_ss [IN_DIFF]
      ++ Q.EXISTS_TAC `s'`
      ++ FULL_SIMP_TAC std_ss [IN_DIFF])
   ++ RW_TAC std_ss [] ++ POP_ASSUM (K ALL_TAC)
   ++ MATCH_MP_TAC EVENTS_COUNTABLE_UNION
   ++ Q.PAT_ASSUM `c SUBSET events p` MP_TAC
   ++ RW_TAC std_ss [COUNTABLE_IMAGE, SUBSET_DEF, IN_IMAGE]
   ++ PROVE_TAC [EVENTS_COMPL]);

val ABS_PROB = store_thm
("ABS_PROB", ``!p s. prob_space p /\ s IN events p
                ==> (abs (prob p s) = prob p s)``,
  RW_TAC std_ss [PROB_POSITIVE,ABS_REFL]);


val PROB_COMPL_LE1 = store_thm
("PROB_COMPL_LE1", ``!p s r. prob_space p /\ s IN events p
                      ==> (prob p (p_space p DIFF s) <= r = 1 - r <= prob p s)``,
  RW_TAC std_ss [PROB_COMPL]
  ++ REAL_ARITH_TAC);

val PROB_LE_1 = store_thm
("PROB_LE_1", ``!p s. prob_space p /\ s IN events p ==> prob p s <= 1``,
  RW_TAC std_ss []
  ++ Suff `0 <= 1 - prob p s` >> REAL_ARITH_TAC
  ++ RW_TAC std_ss [GSYM PROB_COMPL]
  ++ RW_TAC std_ss [EVENTS_COMPL, PROB_POSITIVE]);

val PROB_EQ_BIGUNION_IMAGE = store_thm
("PROB_EQ_BIGUNION_IMAGE", ``!p. prob_space p /\ f IN (UNIV -> events p) /\
                                 g IN (UNIV -> events p) /\
       (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
       (!m n. ~(m = n) ==> DISJOINT (g m) (g n)) /\
       (!n: num. prob p (f n) = prob p (g n)) ==>
       (prob p (BIGUNION (IMAGE f UNIV)) = prob p (BIGUNION (IMAGE g UNIV)))``,
  RW_TAC std_ss []
  ++ METIS_TAC [o_DEF,PROB_COUNTABLY_ADDITIVE,SEQ_UNIQ,sums]);


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
   ++ REVERSE CONJ_TAC
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
   >> (RW_TAC std_ss [EXTENSION,IN_BIGUNION_IMAGE, IN_COUNT, IN_UNIV]
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
   >> (RW_TAC std_ss [EXTENSION, IN_UNION, IN_DIFF]
       ++ PROVE_TAC [])
   ++ Rewr
   ++ Know `u DIFF t IN events p`
   >> PROVE_TAC [EVENTS_DIFF]
   ++ STRIP_TAC
   ++ Know `prob p (t UNION (u DIFF t)) = prob p t + prob p (u DIFF t)`
   >> (MATCH_MP_TAC PROB_ADDITIVE
       ++ RW_TAC std_ss [DISJOINT_ALT, IN_DIFF])
   ++ Rewr
   ++ MATCH_MP_TAC REAL_LE_LADD_IMP
   ++ MATCH_MP_TAC PROB_INCREASING
   ++ RW_TAC std_ss [DIFF_DEF, SUBSET_DEF, GSPECIFICATION]);

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
        RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE, IN_COUNT]
        ++ PROVE_TAC [LT_SUC],
        RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, IN_COUNT]
        ++ REVERSE EQ_TAC >> PROVE_TAC []
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
   ++ REVERSE CONJ_TAC
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


val PROB_REAL_SUM_IMAGE = store_thm
  ("PROB_REAL_SUM_IMAGE",
   ``!p s. prob_space p /\ s IN events p /\ (!x. x IN s ==> {x} IN events p) /\ FINITE s ==>
		(prob p s = SIGMA (\x. prob p {x}) s)``,
   Suff `!s. FINITE s ==>
	(\s. !p. prob_space p /\ s IN events p /\ (!x. x IN s ==> {x} IN events p) ==>
		(prob p s = SIGMA (\x. prob p {x}) s)) s`
   >> METIS_TAC []
   ++ MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM, PROB_EMPTY, DELETE_NON_ELEMENT, IN_INSERT]
   ++ Q.PAT_ASSUM `!p.
            prob_space p /\ s IN events p /\
            (!x. x IN s ==> {x} IN events p) ==>
            (prob p s = SIGMA (\x. prob p {x}) s)` (MP_TAC o GSYM o Q.SPEC `p`)
   ++ RW_TAC std_ss []
   ++ `s IN events p`
	by (`s = (e INSERT s) DIFF {e}`
		by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DIFF, IN_SING]
                    ++ METIS_TAC [GSYM DELETE_NON_ELEMENT])
	    ++ POP_ORW
	    ++ FULL_SIMP_TAC std_ss [prob_space_def, measure_space_def, sigma_algebra_def,
                                     events_def]
	    ++ METIS_TAC [space_def, subsets_def, ALGEBRA_DIFF])
   ++ ASM_SIMP_TAC std_ss []
   ++ MATCH_MP_TAC PROB_ADDITIVE
   ++ RW_TAC std_ss [IN_DISJOINT, IN_SING, Once INSERT_SING_UNION]
   ++ FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]);

val PROB_EQUIPROBABLE_FINITE_UNIONS = store_thm
  ("PROB_EQUIPROBABLE_FINITE_UNIONS",
   ``!p s. prob_space p /\ s IN events p /\ (!x. x IN s ==> {x} IN events p) /\ FINITE s /\
	   (!x y. x IN s /\ y IN s ==> (prob p {x} = prob p {y})) ==>
		(prob p s = & (CARD s) * prob p {CHOICE s})``,
   RW_TAC std_ss []
   ++ Cases_on `s = {}`
   >> RW_TAC real_ss [PROB_EMPTY, CARD_EMPTY]
   ++ `prob p s = SIGMA (\x. prob p {x}) s`
	by METIS_TAC [PROB_REAL_SUM_IMAGE]
   ++ POP_ORW
   ++ `prob p {CHOICE s} = (\x. prob p {x}) (CHOICE s)` by RW_TAC std_ss []
   ++ POP_ORW
   ++ (MATCH_MP_TAC o UNDISCH o Q.SPEC `s`) REAL_SUM_IMAGE_FINITE_SAME
   ++ RW_TAC std_ss [CHOICE_DEF]);


val PROB_REAL_SUM_IMAGE_FN = store_thm
  ("PROB_REAL_SUM_IMAGE_FN",
   ``!p f e s. prob_space p /\ e IN events p /\
               (!x. x IN s ==> e INTER f x IN events p) /\ FINITE s /\
		(!x y. x IN s /\ y IN s /\ (~(x=y)) ==> DISJOINT (f x) (f y)) /\
		(BIGUNION (IMAGE f s) INTER p_space p = p_space p) ==>
		(prob p e = SIGMA (\x. prob p (e INTER f x)) s)``,
   Suff `!(s :'b -> bool). FINITE s ==>
	(\s. !(p :('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real))
       (f :'b -> 'a -> bool) (e :'a -> bool). prob_space p /\ e IN events p /\
                (!x. x IN s ==> e INTER f x IN events p) /\
		(!x y. x IN s /\ y IN s /\ (~(x=y)) ==> DISJOINT (f x) (f y)) /\
		(BIGUNION (IMAGE f s) INTER p_space p = p_space p) ==>
		(prob p e = SIGMA (\x. prob p (e INTER f x)) s)) s`
   >> METIS_TAC []
   ++ MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM, PROB_EMPTY, DELETE_NON_ELEMENT, IN_INSERT,
                     IMAGE_EMPTY, BIGUNION_EMPTY, INTER_EMPTY]
   >> METIS_TAC [PROB_UNIV, PROB_EMPTY, REAL_10]
   ++ `prob p e' =
	prob p (e' INTER f e) +
	prob p (e' DIFF f e)`
	by (MATCH_MP_TAC PROB_ADDITIVE
	    ++ RW_TAC std_ss []
	    << [`e' DIFF f e = e' DIFF (e' INTER f e)`
		by (RW_TAC std_ss [EXTENSION, IN_DIFF, IN_INTER] ++ DECIDE_TAC)
	        ++ POP_ORW
		++ METIS_TAC [EVENTS_DIFF],
		FULL_SIMP_TAC std_ss [IN_DISJOINT, IN_INTER, IN_DIFF] ++ METIS_TAC [],
		RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_UNION, IN_DIFF] ++ DECIDE_TAC])
   ++ POP_ORW
   ++ RW_TAC std_ss [REAL_EQ_LADD]
   ++ (MP_TAC o Q.ISPEC `(s :'b -> bool)`) SET_CASES
   ++ RW_TAC std_ss []
   >> (RW_TAC std_ss [REAL_SUM_IMAGE_THM]
       ++ `IMAGE f {e} = {f e}`
		by RW_TAC std_ss [EXTENSION, IN_IMAGE, IN_SING]
       ++ FULL_SIMP_TAC std_ss [BIGUNION_SING, DIFF_UNIV, PROB_EMPTY]
       ++ `e' DIFF f e = {}`
		by (RW_TAC std_ss [Once EXTENSION, NOT_IN_EMPTY, IN_DIFF]
		    ++ METIS_TAC [SUBSET_DEF, MEASURABLE_SETS_SUBSET_SPACE, prob_space_def,
				  events_def, p_space_def, IN_INTER])
       ++ RW_TAC std_ss [PROB_EMPTY])
   ++ Q.PAT_ASSUM `!p f e.
            prob_space p /\ e IN events p /\
            (!x. x IN s ==> e INTER f x IN events p) /\
            (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y)) /\
            (BIGUNION (IMAGE f s) INTER p_space p = p_space p) ==>
            (prob p e = SIGMA (\x. prob p (e INTER f x)) s)`
	(MP_TAC o Q.SPECL [`p`,`(\y. if y = x then f x UNION f e else f y)`,`e' DIFF f e`])
   ++ ASM_SIMP_TAC std_ss []
   ++ `e' DIFF f e IN events p`
	by (`e' DIFF f e = e' DIFF (e' INTER f e)`
		by (RW_TAC std_ss [EXTENSION, IN_DIFF, IN_INTER] ++ DECIDE_TAC)
	        ++ POP_ORW
		++ METIS_TAC [EVENTS_DIFF])
   ++ ASM_SIMP_TAC std_ss []
   ++ `(!x'.
        x' IN x INSERT t ==>
        (e' DIFF f e) INTER (if x' = x then f x UNION f e else f x') IN
        events p)`
	by (RW_TAC std_ss []
	    >> (`(e' DIFF f e) INTER (f x UNION f e) =
		 e' INTER f x`
		by (ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_INTER, IN_DIFF, IN_UNION]
		    ++ FULL_SIMP_TAC std_ss [IN_DISJOINT, GSYM DELETE_NON_ELEMENT]
		    ++ METIS_TAC [])
	        ++ RW_TAC std_ss [])
	    ++ `(e' DIFF f e) INTER f x' =
		(e' INTER f x') DIFF (e' INTER f e)`
		by (ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_INTER, IN_DIFF]
		    ++ FULL_SIMP_TAC std_ss [IN_DISJOINT, GSYM DELETE_NON_ELEMENT]
		    ++ METIS_TAC [])
	    ++ METIS_TAC [EVENTS_DIFF])
   ++ ASM_SIMP_TAC std_ss []
   ++ `(!x' y.
        x' IN x INSERT t /\ y IN x INSERT t /\ ~(x' = y) ==>
        DISJOINT (if x' = x then f x UNION f e else f x')
          (if y = x then f x UNION f e else f y))`
	by (RW_TAC std_ss [IN_DISJOINT, IN_UNION]
	    ++ FULL_SIMP_TAC std_ss [IN_DISJOINT, GSYM DELETE_NON_ELEMENT]
	    ++ METIS_TAC [])
   ++ ASM_SIMP_TAC std_ss []
   ++ `(BIGUNION
        (IMAGE (\y. (if y = x then f x UNION f e else f y)) (x INSERT t)) INTER p_space p = p_space p)`
	by (FULL_SIMP_TAC std_ss [IMAGE_INSERT, BIGUNION_INSERT]
	    ++ `IMAGE (\y. (if y = x then f x UNION f e else f y)) t =
		IMAGE f t`
		by (ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_IMAGE]
		    ++ EQ_TAC
		    >> (RW_TAC std_ss [] ++ METIS_TAC [])
		    ++ RW_TAC std_ss [] ++ METIS_TAC [])
	    ++ POP_ORW
	    ++ METIS_TAC [UNION_COMM, UNION_ASSOC])
   ++ ASM_SIMP_TAC std_ss []
   ++ STRIP_TAC ++ POP_ASSUM (K ALL_TAC)
   ++ FULL_SIMP_TAC std_ss [FINITE_INSERT]
   ++ RW_TAC std_ss [REAL_SUM_IMAGE_THM]
   ++ FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
   ++ FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]
   ++ `(e' DIFF f e) INTER (f x UNION f e) =
	e' INTER f x`
	by (ONCE_REWRITE_TAC [EXTENSION] ++ RW_TAC std_ss [IN_INTER, IN_DIFF, IN_UNION]
	    ++ FULL_SIMP_TAC std_ss [IN_DISJOINT, GSYM DELETE_NON_ELEMENT, IN_INSERT]
	    ++ METIS_TAC [])
   ++ RW_TAC std_ss [REAL_EQ_LADD]
   ++ ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(t :'b -> bool)`) REAL_SUM_IMAGE_IN_IF]
   ++ Suff `(\x'.
         (if x' IN t then
            (\x'.
               prob p
                 ((e' DIFF f e) INTER
                  (if x' = x then f x UNION f e else f x'))) x'
          else
            0)) =
	(\x. (if x IN t then (\x. prob p (e' INTER f x)) x else 0))`
   >> RW_TAC std_ss []
   ++ RW_TAC std_ss [FUN_EQ_THM] ++ RW_TAC std_ss []
   ++ Suff `(e' DIFF f e) INTER f x' = e' INTER f x'`
   >> RW_TAC std_ss []
   ++ RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_DIFF]
   ++ FULL_SIMP_TAC std_ss [IN_DISJOINT, IN_INSERT]
   ++ METIS_TAC []);

val PROB_REAL_SUM_IMAGE_SPACE = store_thm
  ("PROB_REAL_SUM_IMAGE_SPACE",``!p. prob_space p /\ (!x. x IN (p_space p) ==> {x} IN events p) /\
                              FINITE (p_space p) ==>
		             (SIGMA (\x. prob p {x}) (p_space p) = 1)``,
 RW_TAC std_ss []
 ++ (MP_TAC o GSYM o Q.SPECL [`p`,`p_space p`]) PROB_REAL_SUM_IMAGE
 ++ RW_TAC std_ss [EVENTS_SPACE,PROB_UNIV]);

val PROB_DISCRETE_EVENTS = store_thm
("PROB_DISCRETE_EVENTS",``!p. prob_space p /\ FINITE (p_space p) /\ (!x. x IN p_space p
                              ==> {x} IN events p)
                           ==> (!s. s SUBSET p_space p ==> s IN events p)``,
  RW_TAC std_ss []
  ++ `s = BIGUNION ({{x} | x IN s})`
      by (RW_TAC std_ss [EXTENSION,IN_BIGUNION,GSPECIFICATION,IN_SING]
          ++ METIS_TAC [IN_SING])
  ++ POP_ORW
  ++ `{{x} | x IN s} SUBSET events p`
        by (RW_TAC std_ss  [SUBSET_DEF,GSPECIFICATION] ++ METIS_TAC [SUBSET_DEF])
  ++ `FINITE {{x} | x IN s}`
      by (Suff `{{x} | x IN s} = IMAGE (\x. {x}) s` >> METIS_TAC [IMAGE_FINITE,SUBSET_FINITE]
          ++ RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_IMAGE])
  ++ METIS_TAC [EVENTS_COUNTABLE_UNION,FINITE_COUNTABLE]);

val PROB_DISCRETE_EVENTS_COUNTABLE = store_thm
("PROB_DISCRETE_EVENTS_COUNTABLE",``!p. prob_space p /\ countable (p_space p) /\
                                   (!x. x IN p_space p ==> {x} IN events p) ==>
                                   (!s. s SUBSET p_space p ==> s IN events p)``,
  RW_TAC std_ss []
  ++ `s = BIGUNION ({{x} | x IN s})`
      by (RW_TAC std_ss [EXTENSION,IN_BIGUNION,GSPECIFICATION,IN_SING]
          ++ METIS_TAC [IN_SING])
  ++ POP_ORW
  ++ `{{x} | x IN s} SUBSET events p`
      by (RW_TAC std_ss [SUBSET_DEF,GSPECIFICATION] ++ METIS_TAC [SUBSET_DEF])
  ++ `countable {{x} | x IN s}`
      by (Suff `{{x} | x IN s} = IMAGE (\x. {x}) s`
  >> METIS_TAC [COUNTABLE_IMAGE,COUNTABLE_SUBSET]
          ++ RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_IMAGE])
  ++ METIS_TAC [EVENTS_COUNTABLE_UNION]);

(* ************************************************************************* *)

val marginal_joint_zero = store_thm
  ("marginal_joint_zero", ``!p X Y s t. prob_space p /\ (events p = POW (p_space p)) /\
                            ((distribution p X s = 0) \/ (distribution p Y t = 0))
                             ==> (joint_distribution p X Y (s CROSS t) = 0)``,
  RW_TAC std_ss [joint_distribution_def,distribution_def]
  >> ( `PREIMAGE (\x. (X x,Y x)) (s CROSS t) INTER p_space p SUBSET (PREIMAGE X s INTER p_space p)`
      by RW_TAC std_ss [SUBSET_DEF,IN_PREIMAGE,IN_INTER,IN_CROSS]
  ++ `prob p (PREIMAGE (\x. (X x,Y x)) (s CROSS t) INTER p_space p) <= prob p (PREIMAGE X s INTER p_space p)`
       by METIS_TAC [PROB_INCREASING,INTER_SUBSET,IN_POW]
  ++ METIS_TAC [PROB_POSITIVE,INTER_SUBSET,IN_POW,REAL_LE_ANTISYM])
  ++ `PREIMAGE (\x. (X x,Y x)) (s CROSS t) INTER p_space p SUBSET (PREIMAGE Y t INTER p_space p)`
      by RW_TAC std_ss [SUBSET_DEF,IN_PREIMAGE,IN_INTER,IN_CROSS]
  ++ `prob p (PREIMAGE (\x. (X x,Y x)) (s CROSS t) INTER p_space p) <= prob p (PREIMAGE Y t INTER p_space p)`
       by METIS_TAC [PROB_INCREASING,INTER_SUBSET,IN_POW]
  ++ METIS_TAC [PROB_POSITIVE,INTER_SUBSET,IN_POW,REAL_LE_ANTISYM]);

val marginal_joint_zero3 = store_thm
  ("marginal_joint_zero3", ``!p X Y Z s t u. prob_space p /\ (events p = POW (p_space p)) /\
  			((distribution p X s = 0) \/ (distribution p Y t = 0) \/ (distribution p Z u = 0))
		        ==> (joint_distribution3 p X Y Z (s CROSS (t CROSS u)) = 0)``,
  RW_TAC std_ss [joint_distribution3_def,distribution_def]
  << [ `PREIMAGE (\x. (X x,Y x,Z x)) (s CROSS (t CROSS u)) INTER p_space p
        SUBSET (PREIMAGE X s INTER p_space p)`
           by RW_TAC std_ss [SUBSET_DEF,IN_PREIMAGE,IN_INTER,IN_CROSS]
       ++ `prob p (PREIMAGE (\x. (X x,Y x,Z x)) (s CROSS (t CROSS u)) INTER p_space p) <=
           prob p (PREIMAGE X s INTER p_space p)`
           by METIS_TAC [PROB_INCREASING,INTER_SUBSET,IN_POW]
       ++ METIS_TAC [PROB_POSITIVE,INTER_SUBSET,IN_POW,REAL_LE_ANTISYM],
       `PREIMAGE (\x. (X x,Y x,Z x)) (s CROSS (t CROSS u)) INTER p_space p
        SUBSET (PREIMAGE Y t INTER p_space p)`
           by RW_TAC std_ss [SUBSET_DEF,IN_PREIMAGE,IN_INTER,IN_CROSS]
       ++ `prob p (PREIMAGE (\x. (X x,Y x, Z x)) (s CROSS (t CROSS u)) INTER p_space p) <=
           prob p (PREIMAGE Y t INTER p_space p)`
           by METIS_TAC [PROB_INCREASING,INTER_SUBSET,IN_POW]
       ++ METIS_TAC [PROB_POSITIVE,INTER_SUBSET,IN_POW,REAL_LE_ANTISYM],
       `PREIMAGE (\x. (X x,Y x,Z x)) (s CROSS (t CROSS u)) INTER p_space p
        SUBSET (PREIMAGE Z u INTER p_space p)`
           by RW_TAC std_ss [SUBSET_DEF,IN_PREIMAGE,IN_INTER,IN_CROSS]
       ++ `prob p (PREIMAGE (\x. (X x,Y x, Z x)) (s CROSS (t CROSS u)) INTER p_space p) <=
           prob p (PREIMAGE Z u INTER p_space p)`
           by METIS_TAC [PROB_INCREASING,INTER_SUBSET,IN_POW]
       ++ METIS_TAC [PROB_POSITIVE,INTER_SUBSET,IN_POW,REAL_LE_ANTISYM]]);

val distribution_prob_space = store_thm
  ("distribution_prob_space",
   ``!p X s. random_variable X p s ==>
		prob_space (space s, subsets s, distribution p X)``,
   RW_TAC std_ss [random_variable_def, distribution_def, prob_space_def, measure_def, PSPACE,
		  measure_space_def, m_space_def, measurable_sets_def, IN_MEASURABLE,
		  SPACE, positive_def, PREIMAGE_EMPTY, INTER_EMPTY, PROB_EMPTY,
		  PROB_POSITIVE, space_def, subsets_def, countably_additive_def]
   >> (Q.PAT_ASSUM `!f.
            f IN (UNIV -> measurable_sets p) /\
            (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
            BIGUNION (IMAGE f UNIV) IN measurable_sets p ==>
            measure p o f sums measure p (BIGUNION (IMAGE f univ(:num)))`
		(MP_TAC o Q.SPEC `(\x. PREIMAGE X x INTER p_space p) o f`)
       ++ RW_TAC std_ss [prob_def, o_DEF, PREIMAGE_BIGUNION, IMAGE_IMAGE]
       ++ `(BIGUNION (IMAGE (\x. PREIMAGE X (f x)) UNIV) INTER p_space p) =
	   (BIGUNION (IMAGE (\x. PREIMAGE X (f x) INTER p_space p) UNIV))`
	by (RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, IN_INTER, IN_IMAGE, IN_UNIV]
	    ++ METIS_TAC [IN_INTER])
       ++ POP_ORW
       ++ POP_ASSUM MATCH_MP_TAC
       ++ FULL_SIMP_TAC std_ss [o_DEF, IN_FUNSET, IN_UNIV, events_def]
       ++ CONJ_TAC
       >> (REPEAT STRIP_TAC
	    ++ Suff `DISJOINT (PREIMAGE X (f m)) (PREIMAGE X (f n))`
	    >> (RW_TAC std_ss [IN_DISJOINT, IN_INTER] ++ METIS_TAC [])
	    ++ RW_TAC std_ss [PREIMAGE_DISJOINT])
       ++ Suff `BIGUNION (IMAGE (\x. PREIMAGE X (f x) INTER p_space p) UNIV) =
		PREIMAGE X (BIGUNION (IMAGE f UNIV)) INTER p_space p`
       >> RW_TAC std_ss []
       ++ RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_BIGUNION, IN_IMAGE, IN_UNIV,
			 IN_PREIMAGE, IN_BIGUNION]
       ++ METIS_TAC [IN_INTER, IN_PREIMAGE])
   ++ Suff `PREIMAGE X (space s) INTER p_space p = p_space p`
   >> RW_TAC std_ss [prob_def]
   ++ FULL_SIMP_TAC std_ss [IN_FUNSET, EXTENSION, IN_PREIMAGE, IN_INTER]
   ++ METIS_TAC []);


val uniform_distribution_prob_space = store_thm
  ("uniform_distribution_prob_space",
   ``!X p s. FINITE (p_space p) /\ FINITE (space s) /\ random_variable X p s ==>
        prob_space (space s, subsets s, uniform_distribution p X s)``,
  RW_TAC std_ss []
  ++ `prob_space p` by FULL_SIMP_TAC std_ss [random_variable_def]
  ++ `p_space p <> {}` by METIS_TAC [MEASURE_EMPTY, EVAL ``0 <> 1:real``, prob_space_def]
  ++ `space s <> {}`
      by (FULL_SIMP_TAC std_ss [random_variable_def, IN_FUNSET, IN_MEASURABLE, space_def]
	  ++ METIS_TAC [CHOICE_DEF, NOT_IN_EMPTY])
  ++ `CARD (space s) <> 0` by METIS_TAC [CARD_EQ_0]
  ++ `&CARD (space s) <> 0:real` by RW_TAC real_ss []
  ++ REVERSE (RW_TAC std_ss [prob_space_def, measure_def, PSPACE])
  >> RW_TAC std_ss [uniform_distribution_def, REAL_DIV_REFL]
  ++ MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces
  ++ CONJ_TAC >> FULL_SIMP_TAC std_ss [random_variable_def, IN_MEASURABLE]
  ++ CONJ_TAC >> RW_TAC std_ss []
  ++ CONJ_TAC
  >> (RW_TAC real_ss [positive_def, measure_def, uniform_distribution_def, PREIMAGE_EMPTY,
     	     	      CARD_EMPTY,INTER_EMPTY]
      ++ RW_TAC real_ss [REAL_LE_MUL, REAL_LE_INV, real_div])
  ++ RW_TAC std_ss [additive_def, measure_def, uniform_distribution_def, real_div,
     	    	    measurable_sets_def]
  ++ FULL_SIMP_TAC std_ss [random_variable_def, IN_MEASURABLE, IN_FUNSET, space_def, subsets_def]
  ++ `s' SUBSET space s` by METIS_TAC [sigma_algebra_def, algebra_def, subset_class_def]
  ++ `t SUBSET space s` by METIS_TAC [sigma_algebra_def, algebra_def, subset_class_def]
  ++ `CARD (s' INTER t) = 0` by METIS_TAC [DISJOINT_DEF, CARD_EMPTY]
  ++ `CARD (s' UNION t) = CARD s' + CARD t`  by METIS_TAC [CARD_UNION, ADD_0, SUBSET_FINITE]
  ++ RW_TAC std_ss [GSYM REAL_ADD, REAL_ADD_RDISTRIB]);

val distribution_partition = store_thm
("distribution_partition",``!p X. prob_space p /\ (!x. x IN p_space p ==> {x} IN events p) /\
         FINITE (p_space p) /\ random_variable X p Borel ==>
    (SIGMA (\x. distribution p X {x}) (IMAGE X (p_space p)) = 1)``,
  RW_TAC std_ss []
  ++ `random_variable X p (IMAGE X (p_space p), POW (IMAGE X (p_space p)))`
      by (RW_TAC std_ss [random_variable_def]
	  ++ RW_TAC std_ss [IN_MEASURABLE, IN_FUNSET, space_def, subsets_def,
	     	    	    IN_IMAGE,POW_SIGMA_ALGEBRA]
	  << [METIS_TAC [IN_MEASURABLE, random_variable_def],
	      METIS_TAC [],
	      METIS_TAC [PROB_DISCRETE_EVENTS, INTER_SUBSET]])
  ++ `prob_space (space (IMAGE X (p_space p), POW (IMAGE X (p_space p))), subsets (IMAGE X (p_space p), POW (IMAGE X (p_space p))),distribution p X)` by METIS_TAC [distribution_prob_space]
  ++ (MP_TAC o Q.ISPEC `(space (IMAGE (X :'a->extreal) (p_space p), POW (IMAGE X (p_space p))),subsets (IMAGE X (p_space p), POW (IMAGE X (p_space p))),distribution p X)`) PROB_REAL_SUM_IMAGE_SPACE
  ++ RW_TAC std_ss []
  ++ FULL_SIMP_TAC std_ss [space_def, subsets_def, p_space_def, events_def, m_space_def,
     		   	   measurable_sets_def, prob_def, measure_def]
  ++ `FINITE (IMAGE X (m_space p))` by METIS_TAC [IMAGE_FINITE]
  ++ `(!x. x IN IMAGE X (m_space p) ==> {x} IN POW (IMAGE X (m_space p)))`
      by RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_IMAGE, IN_SING]
  ++ METIS_TAC []);

val distribution_lebesgue_thm1 = store_thm
  ("distribution_lebesgue_thm1",
   ``!X p s A. random_variable X p s /\ A IN subsets s ==>
	     (Normal(distribution p X A) =
	      integral p (indicator_fn (PREIMAGE X A INTER p_space p)))``,
   RW_TAC std_ss [random_variable_def, prob_space_def, distribution_def, events_def,
   	  	  IN_MEASURABLE,p_space_def, prob_def, subsets_def, space_def,
		  GSYM integral_indicator]);

val distribution_lebesgue_thm2 = store_thm
  ("distribution_lebesgue_thm2",
   ``!X p s A. random_variable X p s /\ A IN subsets s ==>
	(Normal (distribution p X A) =
	 integral (space s, subsets s, distribution p X) (indicator_fn A))``,
   REPEAT STRIP_TAC
   ++ `prob_space (space s,subsets s,distribution p X)`
	by RW_TAC std_ss [distribution_prob_space]
   ++ Q.PAT_ASSUM `random_variable X p s` MP_TAC
   ++ RW_TAC std_ss [random_variable_def,prob_space_def,distribution_def,events_def,IN_MEASURABLE,p_space_def,
      	     	     prob_def,subsets_def, space_def]
   ++ `measure p (PREIMAGE X A INTER m_space p) =
       measure (space s,subsets s,(\A. measure p (PREIMAGE X A INTER m_space p))) A`
	by RW_TAC std_ss [measure_def]
   ++ POP_ORW
   ++ (MP_TAC o Q.SPECL [`(space s,subsets s,(\A. measure p (PREIMAGE X A INTER m_space p)))`,`A`] o
       INST_TYPE [``:'a``|->``:'b``]) integral_indicator
   ++ FULL_SIMP_TAC std_ss [measurable_sets_def, prob_space_def, distribution_def, prob_def, p_space_def]);

val finite_expectation1 = store_thm
  ("finite_expectation1",
   ``!p X. FINITE (p_space p) /\ real_random_variable X p ==>
		(expectation p X =
		 SIGMA (\r. r * Normal (prob p (PREIMAGE X {r} INTER p_space p)))
		       (IMAGE X (p_space p)))``,
   RW_TAC std_ss [expectation_def, p_space_def, prob_def, prob_space_def,
   	  	  real_random_variable_def, events_def]
   ++ (MATCH_MP_TAC o REWRITE_RULE [finite_space_integral_def]) finite_space_integral_reduce
   ++ RW_TAC std_ss [num_not_infty]);

val finite_expectation = store_thm
  ("finite_expectation",
   ``!p X. FINITE (p_space p) /\ real_random_variable X p ==>
	(expectation p X = SIGMA (\r. r * Normal (distribution p X {r})) (IMAGE X (p_space p)))``,
   RW_TAC std_ss [distribution_def]
   ++ METIS_TAC [finite_expectation1]);

(* ************************************************************************* *)

val finite_marginal_product_space_POW = store_thm
  ("finite_marginal_product_space_POW",
   ``!p X Y. (POW (p_space p) = events p) /\
	     random_variable X p (IMAGE X (p_space p), POW (IMAGE X (p_space p))) /\
	     random_variable Y p (IMAGE Y (p_space p), POW (IMAGE Y (p_space p))) /\
		    FINITE (p_space p) ==>
	measure_space (((IMAGE X (p_space p)) CROSS (IMAGE Y (p_space p))),
			POW ((IMAGE X (p_space p)) CROSS (IMAGE Y (p_space p))),
			(\a. prob p (PREIMAGE (\x. (X x,Y x)) a INTER p_space p)))``,
   REPEAT STRIP_TAC
   ++ `(IMAGE X (p_space p) CROSS IMAGE Y (p_space p),
		       POW (IMAGE X (p_space p) CROSS IMAGE Y (p_space p)),
		       (\a. prob p (PREIMAGE (\x. (X x,Y x)) a INTER p_space p))) =
	(space (IMAGE X (p_space p) CROSS IMAGE Y (p_space p),
		       POW (IMAGE X (p_space p) CROSS IMAGE Y (p_space p))),
	subsets
         (IMAGE X (p_space p) CROSS IMAGE Y (p_space p),
		       POW (IMAGE X (p_space p) CROSS IMAGE Y (p_space p))),
       (\a. prob p (PREIMAGE (\x. (X x,Y x)) a INTER p_space p)))`
	by RW_TAC std_ss [space_def, subsets_def]
   ++ POP_ORW
   ++ MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces
   ++ RW_TAC std_ss [POW_SIGMA_ALGEBRA, space_def, FINITE_CROSS, subsets_def, IMAGE_FINITE]
   >> (RW_TAC std_ss [positive_def, measure_def, measurable_sets_def, PREIMAGE_EMPTY, INTER_EMPTY]
       >> FULL_SIMP_TAC std_ss [random_variable_def, PROB_EMPTY]
       ++ METIS_TAC [PROB_POSITIVE, SUBSET_DEF, IN_POW, IN_INTER, random_variable_def])
   ++ RW_TAC std_ss [additive_def, measure_def, measurable_sets_def]
   ++ MATCH_MP_TAC PROB_ADDITIVE
   ++ Q.PAT_ASSUM `POW (p_space p) = events p` (MP_TAC o GSYM)
   ++ FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_PREIMAGE, IN_CROSS, IN_DISJOINT, random_variable_def, IN_INTER]
   ++ RW_TAC std_ss [] >> METIS_TAC [SND]
   ++ RW_TAC std_ss [Once EXTENSION, IN_UNION, IN_PREIMAGE, IN_INTER]
   ++ METIS_TAC []);

val finite_marginal_product_space_POW2 = store_thm
  ("finite_marginal_product_space_POW2",
   ``!p s1 s2 X Y. (POW (p_space p) = events p) /\
	     random_variable X p (s1, POW s1) /\
	     random_variable Y p (s2, POW s2) /\
		    FINITE (p_space p) /\
		    FINITE s1 /\ FINITE s2 ==>
	measure_space (s1 CROSS s2, POW (s1 CROSS s2), joint_distribution p X Y)``,
   REPEAT STRIP_TAC
   ++ `(s1 CROSS s2, POW (s1 CROSS s2), joint_distribution p X Y) =
	(space (s1 CROSS s2, POW (s1 CROSS s2)),
	subsets
         (s1 CROSS s2, POW (s1 CROSS s2)),
       joint_distribution p X Y)`
	by RW_TAC std_ss [space_def, subsets_def]
   ++ POP_ORW
   ++ MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces
   ++ RW_TAC std_ss [POW_SIGMA_ALGEBRA, space_def, FINITE_CROSS, subsets_def]
   >> (RW_TAC std_ss [positive_def, measure_def, measurable_sets_def, PREIMAGE_EMPTY, INTER_EMPTY, joint_distribution_def]
       >> FULL_SIMP_TAC std_ss [random_variable_def, PROB_EMPTY]
       ++ METIS_TAC [PROB_POSITIVE, SUBSET_DEF, IN_POW, IN_INTER, random_variable_def])
   ++ RW_TAC std_ss [additive_def, measure_def, measurable_sets_def, joint_distribution_def]
   ++ MATCH_MP_TAC PROB_ADDITIVE
   ++ Q.PAT_ASSUM `POW (p_space p) = events p` (MP_TAC o GSYM)
   ++ FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_PREIMAGE, IN_CROSS, IN_DISJOINT, random_variable_def, IN_INTER]
   ++ RW_TAC std_ss [] >> METIS_TAC [SND]
   ++ RW_TAC std_ss [Once EXTENSION, IN_UNION, IN_PREIMAGE, IN_INTER]
   ++ METIS_TAC []);

val finite_marginal_product_space_POW3 = store_thm
  ("finite_marginal_product_space_POW3",
   ``!p s1 s2 s3 X Y Z. (POW (p_space p) = events p) /\
	     random_variable X p (s1, POW s1) /\
	     random_variable Y p (s2, POW s2) /\
	     random_variable Z p (s3, POW s3) /\
		    FINITE (p_space p) /\ FINITE s1 /\ FINITE s2 /\ FINITE s3 ==>
	measure_space (s1 CROSS (s2 CROSS s3), POW (s1 CROSS (s2 CROSS s3)), joint_distribution3 p X Y Z)``,
   REPEAT STRIP_TAC
   ++ `(s1 CROSS (s2 CROSS s3), POW (s1 CROSS (s2 CROSS s3)), joint_distribution3 p X Y Z) =
	(space (s1 CROSS (s2 CROSS s3), POW (s1 CROSS (s2 CROSS s3))),
	subsets
         (s1 CROSS (s2 CROSS s3), POW (s1 CROSS (s2 CROSS s3))),
       joint_distribution3 p X Y Z)`
	by RW_TAC std_ss [space_def, subsets_def]
   ++ POP_ORW
   ++ MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces
   ++ RW_TAC std_ss [POW_SIGMA_ALGEBRA, space_def, FINITE_CROSS, subsets_def]
   >> (RW_TAC std_ss [positive_def, measure_def, measurable_sets_def, PREIMAGE_EMPTY, INTER_EMPTY, joint_distribution3_def]
       >> FULL_SIMP_TAC std_ss [random_variable_def, PROB_EMPTY]
       ++ METIS_TAC [PROB_POSITIVE, SUBSET_DEF, IN_POW, IN_INTER, random_variable_def])
   ++ RW_TAC std_ss [additive_def, measure_def, measurable_sets_def, joint_distribution3_def]
   ++ MATCH_MP_TAC PROB_ADDITIVE
   ++ Q.PAT_ASSUM `POW (p_space p) = events p` (MP_TAC o GSYM)
   ++ FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_PREIMAGE, IN_CROSS, IN_DISJOINT, random_variable_def, IN_INTER]
   ++ RW_TAC std_ss [] >> METIS_TAC [SND]
   ++ RW_TAC std_ss [Once EXTENSION, IN_UNION, IN_PREIMAGE, IN_INTER]
   ++ METIS_TAC []);

val prob_x_eq_1_imp_prob_y_eq_0 = store_thm
  ("prob_x_eq_1_imp_prob_y_eq_0",
   ``!p x. prob_space p /\
	   {x} IN events p /\
	   (prob p {x} = 1) ==>
	   (!y. {y} IN events p /\
		(~(y = x)) ==>
		(prob p {y} = 0))``,
   REPEAT STRIP_TAC
   ++ (MP_TAC o Q.SPECL [`p`, `{y}`, `{x}`]) PROB_ONE_INTER
   ++ RW_TAC std_ss []
   ++ Know `{y} INTER {x} = {}`
   >> RW_TAC std_ss [Once EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_SING]
   ++ METIS_TAC [PROB_EMPTY]);

val distribution_x_eq_1_imp_distribution_y_eq_0 = store_thm
  ("distribution_x_eq_1_imp_distribution_y_eq_0",
   ``!X p x. random_variable X p (IMAGE X (p_space p),POW (IMAGE X (p_space p))) /\
	       (distribution p X {x} = 1) ==>
	   (!y. (~(y = x)) ==>
		(distribution p X {y} = 0))``,
   REPEAT STRIP_TAC
   ++ (MP_TAC o Q.SPECL [`p`, `X`, `(IMAGE X (p_space p),POW (IMAGE X (p_space p)))`])
      	      distribution_prob_space
   ++ RW_TAC std_ss [space_def, subsets_def]
   ++ (MP_TAC o Q.ISPECL [`(IMAGE (X :'a -> 'b)
           (p_space
              (p :
                ('a -> bool) #
                (('a -> bool) -> bool) # (('a -> bool) -> real))),
         POW (IMAGE X (p_space p)),distribution p X)`,
			`x:'b`]) prob_x_eq_1_imp_prob_y_eq_0
   ++ SIMP_TAC std_ss [EVENTS, IN_POW, SUBSET_DEF, IN_SING, PROB]
   ++ `x IN IMAGE X (p_space p)`
	by (FULL_SIMP_TAC std_ss [distribution_def, IN_IMAGE]
	    ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC
	    ++ `PREIMAGE X {x} INTER p_space p = {}`
		by (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_SING, IN_PREIMAGE, NOT_IN_EMPTY]
		    ++ METIS_TAC [])
	    ++ METIS_TAC [random_variable_def, PROB_EMPTY, EVAL ``0 <> 1:real``])
   ++ POP_ORW
   ++ RW_TAC std_ss []
   ++ Cases_on `y IN IMAGE X (p_space p)` >> ASM_SIMP_TAC std_ss []
   ++ FULL_SIMP_TAC std_ss [distribution_def, IN_IMAGE]
   ++ `PREIMAGE X {y} INTER p_space p = {}`
		by (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_SING, IN_PREIMAGE, NOT_IN_EMPTY]
		    ++ METIS_TAC [])
   ++ POP_ORW ++ MATCH_MP_TAC PROB_EMPTY ++ FULL_SIMP_TAC std_ss [random_variable_def]);

val joint_distribution_sym = store_thm
 ("joint_distribution_sym",``!p X Y a b. prob_space p  ==>
       (joint_distribution p X Y (a CROSS b) = joint_distribution p Y X (b CROSS a))``,
  RW_TAC std_ss [joint_distribution_def]
  ++ Suff `PREIMAGE (\x. (X x,Y x)) (a CROSS b) INTER p_space p =
           PREIMAGE (\x. (Y x,X x)) (b CROSS a) INTER p_space p`
  >> METIS_TAC []
  ++ RW_TAC std_ss [EXTENSION,IN_INTER,IN_PREIMAGE,IN_CROSS]
  ++ METIS_TAC []);

val joint_distribution_pos = store_thm
 ("joint_distribution_pos",``!p X Y a. prob_space p /\ (events p = POW (p_space p)) ==>
			     (0 <= joint_distribution p X Y a)``,
  RW_TAC std_ss [joint_distribution_def]
  ++ MATCH_MP_TAC PROB_POSITIVE
  ++ RW_TAC std_ss [IN_POW,INTER_SUBSET]);

val joint_distribution_le_1 = store_thm
 ("joint_distribution_le_1",``!p X Y a. prob_space p /\ (events p = POW (p_space p)) ==>
			     (joint_distribution p X Y a <= 1)``,
  RW_TAC std_ss [joint_distribution_def]
  ++ MATCH_MP_TAC PROB_LE_1
  ++ RW_TAC std_ss [IN_POW,INTER_SUBSET]);

val joint_distribution_le = store_thm
 ("joint_distribution_le",``!p X Y a b. prob_space p /\ (events p = POW (p_space p)) ==>
			     (joint_distribution p X Y (a CROSS b) <= distribution p X a)``,
  RW_TAC std_ss [joint_distribution_def,distribution_def]
  ++ MATCH_MP_TAC PROB_INCREASING
  ++ RW_TAC std_ss [IN_POW,INTER_SUBSET]
  ++ RW_TAC std_ss [SUBSET_DEF,IN_PREIMAGE,IN_CROSS,IN_INTER]);

val joint_distribution_le2 = store_thm
 ("joint_distribution_le2",``!p X Y a b. prob_space p /\ (events p = POW (p_space p)) ==>
			     (joint_distribution p X Y (a CROSS b) <= distribution p Y b)``,
  RW_TAC std_ss [joint_distribution_def,distribution_def]
  ++ MATCH_MP_TAC PROB_INCREASING
  ++ RW_TAC std_ss [IN_POW,INTER_SUBSET]
  ++ RW_TAC std_ss [SUBSET_DEF,IN_PREIMAGE,IN_CROSS,IN_INTER]);


val joint_conditional = store_thm
 ("joint_conditional",``!p X Y a b. prob_space p /\ (events p = POW (p_space p)) ==>
 			       (joint_distribution p X Y (a CROSS b) =
			        conditional_distribution p Y X b a * distribution p X a)``,
  RW_TAC std_ss [conditional_distribution_def,Once joint_distribution_sym]
  ++ Cases_on `distribution p X a = 0`
  >> METIS_TAC [REAL_LE_ANTISYM,joint_distribution_pos,joint_distribution_le,
     	        joint_distribution_sym,REAL_MUL_RZERO]
  ++ RW_TAC std_ss [REAL_DIV_RMUL]);

val distribution_pos = store_thm
 ("distribution_pos",``!p X a. prob_space p /\ (events p = POW (p_space p)) ==>
			     (0 <= distribution p X a)``,
  RW_TAC std_ss [distribution_def]
  ++ MATCH_MP_TAC PROB_POSITIVE
  ++ RW_TAC std_ss [IN_POW,INTER_SUBSET]);

val conditional_distribution_pos = store_thm
 ("conditional_distribution_pos",``!p X Y a b. prob_space p /\ (events p = POW (p_space p)) ==>
			     (0 <= conditional_distribution p X Y a b)``,
  RW_TAC std_ss [conditional_distribution_def,distribution_pos,joint_distribution_pos,real_div,
  	 	 REAL_LE_MUL,REAL_LE_INV]);

val conditional_distribution_le_1 = store_thm
 ("conditional_distribution_le_1",``!p X Y a b. prob_space p /\ (events p = POW (p_space p)) ==>
			     (conditional_distribution p X Y a b <= 1)``,
  RW_TAC std_ss [conditional_distribution_def]
  ++ Cases_on `distribution p Y b = 0`
  >> METIS_TAC [marginal_joint_zero,real_div,REAL_MUL_LZERO,REAL_LE_01]
  ++ METIS_TAC [REAL_LE_LDIV_EQ, REAL_MUL_LID, REAL_LT_LE, joint_distribution_le2,
     	        distribution_pos]);

val marginal_distribution1 = store_thm
 ("marginal_distribution1",``!p X Y a. prob_space p /\ FINITE (p_space p) /\
 				       (events p = POW (p_space p))
    ==> (distribution p X a =
    	 SIGMA (\x. joint_distribution p X Y (a CROSS {x})) (IMAGE Y (p_space p)))``,
  RW_TAC std_ss [joint_distribution_def,distribution_def]
  ++ `FINITE (IMAGE Y (p_space p))` by METIS_TAC [IMAGE_FINITE]
  ++ RW_TAC std_ss [PREIMAGE_def,IN_CROSS,IN_SING]
  ++ `(prob p ({x | X x IN a} INTER p_space p) =
       SIGMA (\x. prob p ({x | X x IN a} INTER p_space p INTER (\x. {x' | Y x' = x}) x))
       	     	  (IMAGE Y (p_space p)))`
        by (MATCH_MP_TAC  PROB_REAL_SUM_IMAGE_FN
	    ++ RW_TAC std_ss [IN_POW, INTER_SUBSET]
	    <<[RW_TAC std_ss [SUBSET_DEF, IN_INTER, GSPECIFICATION],
	       RW_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION, IN_INTER]
	       ++ METIS_TAC [],
	       RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_INTER, GSPECIFICATION]
	       ++ METIS_TAC [IN_IMAGE]])
  ++ RW_TAC std_ss []
  ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
  ++ RW_TAC std_ss []
  ++ Suff `{x | X x IN a} INTER p_space p INTER {x' | Y x' = x} =
     	   {x' | X x' IN a /\ (Y x' = x)} INTER p_space p`
  >> RW_TAC std_ss []
  ++ RW_TAC std_ss [EXTENSION, IN_INTER, GSPECIFICATION]
  ++ METIS_TAC []);

val marginal_distribution2 = store_thm
 ("marginal_distribution2",``!p X Y b. prob_space p /\ FINITE (p_space p) /\
 				       (events p = POW (p_space p))
    ==> (distribution p Y b =
    	 SIGMA (\x. joint_distribution p X Y ({x} CROSS b)) (IMAGE X (p_space p)))``,
  RW_TAC std_ss [joint_distribution_def,distribution_def]
  ++ `FINITE (IMAGE X (p_space p))` by METIS_TAC [IMAGE_FINITE]
  ++ RW_TAC std_ss [PREIMAGE_def,IN_CROSS,IN_SING]
  ++ `prob p ({x | Y x IN b} INTER p_space p) =
      SIGMA (\x. prob p ({x | Y x IN b} INTER p_space p INTER (\x. {x' | X x' = x}) x))
      	    (IMAGE X (p_space p))`
        by (MATCH_MP_TAC  PROB_REAL_SUM_IMAGE_FN
	    ++ RW_TAC std_ss [IN_POW, INTER_SUBSET]
	    <<[RW_TAC std_ss [SUBSET_DEF, IN_INTER, GSPECIFICATION],
	       RW_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION, IN_INTER]
	       ++ METIS_TAC [],
	       RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_INTER, GSPECIFICATION]
	       ++ METIS_TAC [IN_IMAGE]])
  ++ RW_TAC std_ss []
  ++ MATCH_MP_TAC REAL_SUM_IMAGE_EQ
  ++ RW_TAC std_ss []
  ++ Suff `{x | Y x IN b} INTER p_space p INTER {x' | X x' = x} =
     	   {x' | (X x' = x) /\ Y x' IN b} INTER p_space p`
  >> RW_TAC std_ss []
  ++ RW_TAC std_ss [EXTENSION, IN_INTER, GSPECIFICATION]
  ++ METIS_TAC []);

val joint_distribution_sums_1 = store_thm
 ("joint_distribution_sums_1",``!p X Y. prob_space p /\ FINITE (p_space p) /\
 				     	(events p = POW (p_space p))
    ==> (SIGMA (\(x,y). joint_distribution p X Y {(x,y)})
    	       ((IMAGE X (p_space p)) CROSS (IMAGE Y (p_space p))) = 1)``,
  RW_TAC std_ss []
  ++ `(\(x,y). joint_distribution p X Y {(x,y)}) =
      (\x. (\a b. joint_distribution p X Y ({a} CROSS {b})) (FST x) (SND x))`
       by (RW_TAC std_ss [FUN_EQ_THM]
	   ++ Cases_on `x`
	   ++ RW_TAC std_ss [FST,SND]
	   ++ METIS_TAC [CROSS_SINGS])
  ++ POP_ORW
  ++ `SIGMA (\x. (\a b. joint_distribution p X Y ({a} CROSS {b})) (FST x) (SND x))
     	    	 (IMAGE X (p_space p) CROSS IMAGE Y (p_space p)) =
      SIGMA (\x. SIGMA (\y. joint_distribution p X Y ({x} CROSS {y})) (IMAGE Y (p_space p)))
      	    	 (IMAGE X (p_space p))`
        by RW_TAC std_ss [GSYM REAL_SUM_IMAGE_REAL_SUM_IMAGE, IMAGE_FINITE]
  ++ POP_ORW
  ++ `!x. SIGMA (\y. joint_distribution p X Y ({x} CROSS {y})) (IMAGE Y (p_space p)) =
     	  distribution p X {x}`
       by METIS_TAC [marginal_distribution1]
  ++ RW_TAC std_ss [Once REAL_SUM_IMAGE_IN_IF, IMAGE_FINITE]
  ++ RW_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF, IMAGE_FINITE]
  ++ `random_variable X p (IMAGE X (p_space p), POW (IMAGE X (p_space p)))`
      by (RW_TAC std_ss [random_variable_def, IN_MEASURABLE, IN_FUNSET, POW_SIGMA_ALGEBRA,
      	 	 	 space_def, subsets_def, IN_POW, INTER_SUBSET, IN_IMAGE]
          ++ METIS_TAC [IN_IMAGE])
  ++ Q.ABBREV_TAC `p1 = (IMAGE X (p_space p), POW (IMAGE X (p_space p)), distribution p X)`
  ++ `prob_space p1` by METIS_TAC [distribution_prob_space, space_def, subsets_def]
  ++ (MP_TAC o Q.SPEC `p1` o INST_TYPE [``:'a`` |-> ``:'b``]) PROB_REAL_SUM_IMAGE_SPACE
  ++ RW_TAC std_ss []
  ++ `FINITE (p_space p1)` by METIS_TAC [PSPACE, IMAGE_FINITE]
  ++ `!x. x IN p_space p1 ==> {x} IN events p1`
      by METIS_TAC [EVENTS, IN_POW, SUBSET_DEF, IN_SING, PSPACE]
  ++ METIS_TAC [PROB,PSPACE]);

val joint_distribution_sum_mul1 = store_thm
 ("joint_distribution_sum_mul1",``!p X Y f. prob_space p /\ FINITE (p_space p) /\
 				       	    (events p = POW (p_space p))
 	 ==> (SIGMA (\(x,y). joint_distribution p X Y {(x,y)} * (f x))
	     	    (IMAGE X (p_space p) CROSS IMAGE Y (p_space p)) =
              SIGMA (\x. distribution p X {x} * (f x)) (IMAGE X (p_space p)))``,
  RW_TAC std_ss []
  ++ Q.ABBREV_TAC `s1 = IMAGE X (p_space p)`
  ++ Q.ABBREV_TAC `s2 = IMAGE Y (p_space p)`
  ++ `FINITE s1 /\ FINITE s2` by METIS_TAC [IMAGE_FINITE]
  ++ `(\(x,y). joint_distribution p X Y {(x,y)} * (f x)) =
      (\x. (\a b. joint_distribution p X Y {(a,b)} * (f a) ) (FST x) (SND x))`
        by (RW_TAC std_ss [FUN_EQ_THM]
	    ++ Cases_on `x`
	    ++ RW_TAC std_ss [])
  ++ POP_ORW
  ++ (MP_TAC o GSYM o Q.SPECL [`s1`,`s2`,`(\a b. joint_distribution p X Y {(a,b)} * (f a))`] o
      INST_TYPE [``:'a`` |-> ``:'b``, ``:'b`` |-> ``:'c``]) REAL_SUM_IMAGE_REAL_SUM_IMAGE
  ++ RW_TAC std_ss []
  ++ `!x. (\b. joint_distribution p X Y {(x,b)} * (f x)) =
          (\b. (f x) * (\b. joint_distribution p X Y {(x,b)}) b)`
        by RW_TAC std_ss [FUN_EQ_THM, REAL_MUL_COMM]
  ++ RW_TAC std_ss [REAL_SUM_IMAGE_CMUL]
  ++ `!x:'b b:'c. {(x,b)} = {x} CROSS {b}` by METIS_TAC [CROSS_SINGS]
  ++ Q.UNABBREV_TAC `s1`
  ++ Q.UNABBREV_TAC `s2`
  ++ RW_TAC std_ss [GSYM marginal_distribution1]
  ++ Suff `(\x. (f x) * distribution p X {x}) = (\x. distribution p X {x} * (f x))`
  >> RW_TAC std_ss []
  ++ RW_TAC std_ss [FUN_EQ_THM, REAL_MUL_COMM]);

val _ = export_theory ();
