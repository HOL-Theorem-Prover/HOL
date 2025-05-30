(* ========================================================================= *)
(*   Probability Density Function Theory (former normal_rvTheory) [1]        *)
(*                                                                           *)
(*        (c) Copyright 2015,                                                *)
(*                       Muhammad Qasim,                                     *)
(*                       Osman Hasan,                                        *)
(*                       Hardware Verification Group,                        *)
(*                       Concordia University                                *)
(*            Contact:  <m_qasi@ece.concordia.ca>                            *)
(*                                                                           *)
(*   Enriched by Chun Tian (Australian National University, 2024 - 2025)     *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open combinTheory arithmeticTheory numLib logrootTheory hurdUtils pred_setLib
     pred_setTheory topologyTheory pairTheory tautLib jrhUtils cardinalTheory;

open realTheory realLib seqTheory transcTheory real_sigmaTheory iterateTheory
     real_topologyTheory derivativeTheory metricTheory netsTheory;

open sigma_algebraTheory extreal_baseTheory extrealTheory real_borelTheory
     measureTheory borelTheory lebesgueTheory martingaleTheory probabilityTheory;

val _ = new_theory "distribution"; (* was: "normal_rv" *)

fun ASSERT_TAC tm = SUBGOAL_THEN tm STRIP_ASSUME_TAC;
fun METIS ths tm = prove(tm,METIS_TAC ths);
val T_TAC = rpt (Q.PAT_X_ASSUM ‘T’ K_TAC);

(* ------------------------------------------------------------------------- *)
(*  Properties of distribution_functions                                     *)
(* ------------------------------------------------------------------------- *)

(* A function is "right-continuous" if it's right-continuous at all points

   NOTE: the requirement of mono-increasing is included since this version of
  "right-continuous" definition only works on mono-increasing functions.

   NOTE: The concept of "right-continuous" at points PosInf/NegInf is tricky,
   and (may) not be true for all distribution functions, thus is excluded.
 *)
Definition right_continuous :
    right_continuous (f :extreal -> extreal) <=>
      (!x y. x <= y ==> f x <= f y) /\ !x. f right_continuous_at (Normal x)
End

(* |- !f. right_continuous f <=>
         (!x y. x <= y ==> f x <= f y) /\ !x. inf {f x' | x < x'} = f (Normal x)
 *)
Theorem right_continuous_def =
        right_continuous |> REWRITE_RULE [right_continuous_at]

(* NOTE: There's no supporting theorem for “distribution_function” in
   probabilityTheory. The present lemma seems the first one.
 *)
Theorem distribution_function_monotone :
    !p X f. prob_space p /\ random_variable X p Borel /\
            f = distribution_function p X ==> !x y. x <= y ==> f x <= f y
Proof
    rw [distribution_function_def]
 >> MATCH_MP_TAC PROB_INCREASING >> art []
 >> Know ‘!z. {w | X w <= z} INTER p_space p IN events p’
 >- (Q.X_GEN_TAC ‘z’ \\
     fs [random_variable_def, IN_MEASURABLE, PREIMAGE_def] \\
     Q.PAT_X_ASSUM ‘!s. s IN subsets Borel ==> _’ (MP_TAC o Q.SPEC ‘{x | x <= z}’) \\
     rw [BOREL_MEASURABLE_SETS])
 >> rw [SUBSET_DEF]
 >> Q_TAC (TRANS_TAC le_trans) ‘x’ >> art []
QED

Theorem distribution_function_monotone' :
    !p X f. prob_space p /\ random_variable X p borel /\
            f = distribution_function p (Normal o X) ==> !x y. x <= y ==> f x <= f y
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MATCH_MP_TAC distribution_function_monotone
 >> qexistsl_tac [‘p’, ‘Normal o X’] >> art []
 >> fs [random_variable_def]
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' >> art []
 >> MATCH_MP_TAC EVENTS_SIGMA_ALGEBRA >> art []
QED

(* NOTE: This tactic is shared by distribution_function_right_continuous and
   existence_of_random_variable.
 *)
val distribution_function_right_continuous_tac =
    (simp [right_continuous_def] \\
     Q.X_GEN_TAC ‘x0’ \\
  (* preparing for MONOTONE_CONVERGENCE_BIGINTER *)
     qabbrev_tac ‘g = \n. {x | x <= Normal x0 + 1 / &SUC n}’ \\
     qabbrev_tac ‘s = BIGINTER (IMAGE g UNIV)’ \\
     Know ‘f (Normal x0) = measure M s’
     >- (rw [Abbr ‘M’, Abbr ‘s’, Abbr ‘f’] \\
         AP_TERM_TAC \\
         rw [Once EXTENSION, IN_BIGINTER_IMAGE] \\
         EQ_TAC >> rw [Abbr ‘g’]
         >- (Q_TAC (TRANS_TAC le_trans) ‘Normal x0’ >> art [] \\
             simp [le_addr] \\
            ‘&SUC y <> 0 :extreal’ by rw [extreal_of_num_def] \\
            ‘1 / &SUC y = inv (&SUC y)’ by rw [inv_1over] >> POP_ORW \\
             MATCH_MP_TAC le_inv >> rw [extreal_of_num_def]) \\
         MATCH_MP_TAC le_epsilon >> rpt STRIP_TAC \\
         drule EXTREAL_ARCH_INV' >> STRIP_TAC \\
         Q_TAC (TRANS_TAC le_trans) ‘Normal x0 + inv (&SUC n)’ \\
        ‘&SUC n <> 0 :extreal’ by rw [extreal_of_num_def] \\
         reverse CONJ_TAC >- simp [le_ladd] \\
         simp [inv_1over]) >> Rewr' \\
     Know ‘inf {f x' | Normal x0 < x'} = inf (IMAGE (measure M o g) UNIV)’
     >- (simp [GSYM le_antisym] \\
         CONJ_TAC
         >- (rw [le_inf', inf_le'] \\
             rw [Abbr ‘M’, Abbr ‘g’] \\
             POP_ASSUM MATCH_MP_TAC \\
             Q.EXISTS_TAC ‘Normal x0 + 1 / &SUC x’ >> rw [lt_addr] \\
            ‘&SUC x <> 0 :extreal’ by rw [extreal_of_num_def] \\
            ‘1 / &SUC x = inv (&SUC x)’ by rw [inv_1over] >> POP_ORW \\
             simp [inv_pos_eq, extreal_of_num_def]) \\
         rw [le_inf'] >> rename1 ‘Normal x0 < z’ \\
         rw [inf_le', Abbr ‘g’, o_DEF] \\
         Cases_on ‘z = PosInf’
         >- (POP_ORW \\
            ‘f PosInf = measure M (m_space M)’
               by rw [Abbr ‘f’, Abbr ‘M’, SPACE_BOREL] >> POP_ORW \\
            ‘measure M (m_space M) = 1’ by fs [prob_space_def] >> POP_ORW \\
             POP_ASSUM (MP_TAC o
                        Q.SPEC ‘measure M {x' | x' <= Normal x0 + 1 / &SUC 0}’) \\
             impl_tac >- (Q.EXISTS_TAC ‘0’ >> rw []) \\
             simp [Abbr ‘M’] >> STRIP_TAC \\
             Q_TAC (TRANS_TAC le_trans) ‘f (Normal x0 + 1)’ >> art []) \\
         Know ‘z <> NegInf’
         >- (simp [lt_infty] \\
             Q_TAC (TRANS_TAC lt_trans) ‘Normal x0’ >> rw []) >> DISCH_TAC \\
        ‘?r. z = Normal r’ by METIS_TAC [extreal_cases] \\
         POP_ASSUM (fs o wrap) >> T_TAC \\
        ‘0 < r - x0’ by rw [REAL_SUB_LT] \\
         drule REAL_ARCH_INV_SUC >> STRIP_TAC \\
        ‘x0 + inv (&SUC n) < r’ by REAL_ASM_ARITH_TAC \\
         Q_TAC (TRANS_TAC le_trans) ‘f (Normal x0 + 1 / &SUC n)’ \\
         CONJ_TAC
         >- (FIRST_X_ASSUM MATCH_MP_TAC \\
             Q.EXISTS_TAC ‘n’ >> simp [Abbr ‘M’]) \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
        ‘&SUC n <> 0 :extreal’ by rw [extreal_of_num_def] \\
        ‘1 / &SUC n = inv (&SUC n)’ by rw [inv_1over] >> POP_ORW \\
         simp [extreal_inv_eq, extreal_of_num_def, extreal_add_def] \\
         MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> Rewr' \\
  (* applying MONOTONE_CONVERGENCE_BIGINTER *)
     MATCH_MP_TAC MONOTONE_CONVERGENCE_BIGINTER >> simp [IN_FUNSET] \\
     fs [prob_space_def, Abbr ‘M’] \\
     CONJ_ASM1_TAC >- rw [Abbr ‘g’, BOREL_MEASURABLE_SETS] \\
     CONJ_TAC >- (rw [lt_infty] \\
                  Q_TAC (TRANS_TAC let_trans) ‘1’ >> simp []) \\
     rw [SUBSET_DEF, Abbr ‘g’] \\
     Q_TAC (TRANS_TAC le_trans) ‘Normal x0 + 1 / &SUC (SUC n)’ >> art [] \\
     simp [le_ladd] \\
    ‘!n. &SUC n <> 0 :extreal’ by rw [extreal_of_num_def] \\
     simp [GSYM inv_1over] \\
    ‘!n. (0 :extreal) < &SUC n’ by rw [extreal_of_num_def] \\
     simp [inv_le_antimono] \\
     simp [extreal_of_num_def, extreal_le_eq]);

(* NOTE: This proof is similar with the ‘right_continuous f’ subgoal in the proof of
   existence_of_random_variable but it's hard to extract a common lemma for them.
 *)
Theorem distribution_function_right_continuous :
    !p X f. prob_space p /\ random_variable X p Borel /\
            f = distribution_function p X ==> right_continuous f
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘m = distribution p X’
 >> qabbrev_tac ‘M = (space Borel,subsets Borel,m)’
 >> Know ‘prob_space M’
 >- (qunabbrevl_tac [‘M’, ‘m’] \\
     MATCH_MP_TAC distribution_prob_space >> rw [SIGMA_ALGEBRA_BOREL])
 >> DISCH_TAC
 >> qabbrev_tac ‘f = \w. m {x | x <= w}’
 >> ‘distribution_function p X = f’
       by rw [FUN_EQ_THM, distribution_function, Abbr ‘m’]
 >> ‘!x y. x <= y ==> f x <= f y’ by PROVE_TAC [distribution_function_monotone]
 >> Know ‘!s. s IN subsets Borel ==>
              0 <= m s /\ m s <= 1 /\ m s <> NegInf /\ m s <> PosInf’
 >- (Q.X_GEN_TAC ‘s’ >> DISCH_TAC \\
    ‘m s = prob M s’ by rw [Abbr ‘M’, PROB] >> POP_ORW \\
    ‘s IN events M’ by rw [Abbr ‘M’, events_def] \\
     METIS_TAC [PROB_LE_1, PROB_POSITIVE, PROB_FINITE])
 >> DISCH_TAC
 >> Know ‘!x. 0 <= f x /\ f x <= 1 /\ f x <> NegInf /\ f x <> PosInf’
 >- (Q.X_GEN_TAC ‘x’ >> simp [Abbr ‘f’] \\
     METIS_TAC [BOREL_MEASURABLE_SETS])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘_ = f’ (REWRITE_TAC o wrap)
 >> distribution_function_right_continuous_tac
QED

(* ------------------------------------------------------------------------- *)
(*  Existence of random variables having the given distribution              *)
(* ------------------------------------------------------------------------- *)

(* NOTE: ‘m’ is the distribution to be equal to ”distribution p X“. By theorem
  [distribution_prob_space], any valid distribution must form a probability
   space, i.e. prob_space (space Borel,subsets Borel,m).

   The corresponding probability space where X is constructed, is always the
   restricted ext_lborel, i.e. restrict_space ext_lborel [0,1].

   This proof is based on idea from StackExchange [6] (answered by @Alexisz).
   See also [7, p.61] for the only textbook mentioning a similar proof.
 *)
Theorem existence_of_random_variable :
    !m p. prob_space (space Borel,subsets Borel,m) /\
          p = restrict_space ext_lborel {x | 0 <= x /\ x <= 1} ==>
          ?X. random_variable X p Borel /\
              !s. s IN subsets Borel ==> distribution p X s = m s
Proof
    RW_TAC std_ss []
 >> qabbrev_tac ‘M = (space Borel,subsets Borel,m)’
 >> Know ‘!s. s IN subsets Borel ==>
              0 <= m s /\ m s <= 1 /\ m s <> NegInf /\ m s <> PosInf’
 >- (Q.X_GEN_TAC ‘s’ >> DISCH_TAC \\
    ‘m s = prob M s’ by rw [Abbr ‘M’, PROB] >> POP_ORW \\
    ‘s IN events M’ by rw [Abbr ‘M’, events_def] \\
     METIS_TAC [PROB_LE_1, PROB_POSITIVE, PROB_FINITE])
 >> DISCH_TAC
 >> qabbrev_tac ‘sp = {(x :extreal) | 0 <= x /\ x <= 1}’
 >> ‘sp IN subsets Borel’ by rw [BOREL_MEASURABLE_SETS, Abbr ‘sp’]
 >> qabbrev_tac ‘p = restrict_space ext_lborel sp’
 >> ‘prob_space p’ by PROVE_TAC [prob_space_ext_lborel_01]
 >> qabbrev_tac ‘f = \w. m {x | x <= w}’
 >> Know ‘!x. 0 <= f x /\ f x <= 1 /\ f x <> NegInf /\ f x <> PosInf’
 >- (Q.X_GEN_TAC ‘x’ >> simp [Abbr ‘f’] \\
     METIS_TAC [BOREL_MEASURABLE_SETS])
 >> DISCH_TAC
 >> Know ‘!x y. x <= y ==> f x <= f y’
 >- (rw [Abbr ‘f’] \\
     Know ‘increasing M’ >- PROVE_TAC [MEASURE_SPACE_INCREASING, prob_space_def] \\
     rw [increasing_def, Abbr ‘M’] \\
     POP_ASSUM MATCH_MP_TAC \\
     simp [ext_lborel_def, BOREL_MEASURABLE_SETS] \\
     rw [SUBSET_DEF] >> Q_TAC (TRANS_TAC le_trans) ‘x’ >> art [])
 >> DISCH_TAC
 (* applying shared tactics *)
 >> ‘right_continuous f’ by distribution_function_right_continuous_tac
 (* now define the canonical random variable *)
 >> qabbrev_tac ‘X = \w. sup {x | f x <= w}’
 >> Know ‘!x y. x <= y ==> X x <= X y’
 >- (rw [Abbr ‘X’] \\
     MATCH_MP_TAC sup_mono_subset >> rw [SUBSET_DEF] \\
     Q_TAC (TRANS_TAC le_trans) ‘x’ >> art [])
 >> DISCH_TAC
 >> Q.EXISTS_TAC ‘X’
 >> STRONG_CONJ_TAC
 >- (rw [random_variable_def, p_space_def, events_def] \\
     simp [Abbr ‘p’, space_restrict_space, sets_restrict_space] \\
     simp [ext_lborel_def] \\
     simp [GSYM restrict_algebra_def] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_INCREASING >> rw [])
 >> DISCH_TAC
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 (* applying UNIQUENESS_OF_MEASURE_FINITE

    NOTE: The choice of [Borel_eq_le] here is to make the RHS easier, in form of
   “m {x | x <= Normal a}” which is “f (Normal a)”. The LHS is tricky no matter
    which version of ‘Borel’ alternative definition were chosen.
  *)
 >> simp [Borel_eq_le]
 >> HO_MATCH_MP_TAC UNIQUENESS_OF_MEASURE_FINITE >> simp []
 >> CONJ_TAC >- rw [subset_class_def] (* subset_class *)
 >> CONJ_TAC (* INTER-stable *)
 >- (RW_TAC std_ss [] \\
     Q.EXISTS_TAC ‘min a a'’ \\
     rw [Once EXTENSION] >> EQ_TAC >> rw [] >| (* 3 subgoals *)
     [ rw [GSYM extreal_min_eq, le_min],
       fs [GSYM extreal_min_eq, le_min],
       fs [GSYM extreal_min_eq, le_min] ])
 >> simp [GSYM Borel_eq_le, GSYM SPACE_BOREL]
 >> fs [prob_space_def, random_variable_def, p_space_def, events_def,
        distribution_distr]
 >> CONJ_TAC (* measure_space_distr *)
 >- (‘(\s. distr p X s) = distr p X’ by rw [FUN_EQ_THM] >> POP_ORW \\
     MATCH_MP_TAC measure_space_distr >> art [])
 >> simp [distr_def, SPACE_BOREL]
 >> CONJ_TAC >- fs [Abbr ‘M’, SPACE_BOREL] (* m UNIV = 1 *)
 >> RW_TAC std_ss []
 >> simp []
 (* NOTE: RHS is now ‘f (Normal a)’, which is good (Kai Phan's idea) *)
 >> ‘m_space p = sp /\ measure p = lambda o real_set’
      by rw [Abbr ‘p’, space_restrict_space, measure_restrict_space,
             ext_lborel_def, SPACE_BOREL]
 >> qabbrev_tac ‘l = \s. lambda (real_set s)’
 >> simp []
 >> qmatch_abbrev_tac ‘l (s INTER sp) = _’
 >> qabbrev_tac ‘s' = s INTER sp’
 (* This is needed at the end of this proof *)
 >> Know ‘s' IN subsets Borel’
 >- (Q.PAT_X_ASSUM ‘X IN Borel_measurable (measurable_space p)’ MP_TAC \\
     simp [Abbr ‘s'’, Abbr ‘s’, IN_MEASURABLE, IN_FUNSET, SPACE_BOREL] \\
     DISCH_TAC \\
     MP_TAC (Q.SPECL [‘ext_lborel’, ‘sp’]
                     (INST_TYPE [alpha |-> “:extreal”] restrict_space_SUBSET)) \\
     simp [measure_space_ext_lborel, ext_lborel_def] \\
     Suff ‘PREIMAGE X {x | x <= Normal a} INTER sp IN measurable_sets p’
     >- rw [SUBSET_DEF] \\
     POP_ASSUM MATCH_MP_TAC \\
     rw [BOREL_MEASURABLE_SETS])
 (* unfolding X, eliminating sup and PREIMAGE *)
 >> Q.PAT_X_ASSUM ‘!x y. x <= y ==> X x <= X y’ K_TAC
 >> Q.PAT_X_ASSUM ‘X IN Borel_measurable (measurable_space p)’ K_TAC
 >> simp [o_DEF, Abbr ‘X’, PREIMAGE_def, sup_le', Abbr ‘s'’, Abbr ‘s’]
 >> DISCH_TAC
 (* NOTE: “s INTER sp = s, i.e. s SUBSET sp” cannot be proved *)
 >> qmatch_abbrev_tac ‘l (s INTER sp) = _’
 >> qabbrev_tac ‘s' = s INTER sp’
 (* NOTE: we hope that s' is equal or (at least closer) to the following t *)
 >> qabbrev_tac ‘t = {x | 0 <= x /\ x <= f (Normal a)}’
 >> Know ‘l t = f (Normal a)’
 >- (rw [Abbr ‘l’, Abbr ‘t’, Once EXTENSION, o_DEF] \\
    ‘?r. 0 <= r /\ f (Normal a) = Normal r’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_le_eq] \\
     POP_ORW \\
     Suff ‘real_set {x | 0 <= x /\ x <= Normal r} = interval [0,r]’
     >- rw [lambda_closed_interval] \\
     rw [Once EXTENSION, real_set_def, CLOSED_interval] \\
     EQ_TAC >> rw [] (* 3 subgoals *)
     >| [ (* goal 1 (of 3) *)
         ‘?z. 0 <= z /\ x' = Normal z’
            by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_le_eq] \\
          simp [real_normal],
          (* goal 2 (of 3) *)
         ‘?z. z <= r /\ x' = Normal z’
            by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_le_eq] \\
          simp [real_normal],
          (* goal 3 (of 3) *)
          Q.EXISTS_TAC ‘Normal x’ >> rw [extreal_of_num_def, extreal_le_eq] ])
 >> DISCH_THEN (REWRITE_TAC o wrap o SYM)
 >> Know ‘s' SUBSET t’
 >- (Q.PAT_X_ASSUM ‘s' IN subsets Borel’ K_TAC \\
     rw [SUBSET_DEF, Abbr ‘s'’, Abbr ‘s’, Abbr ‘sp’, Abbr ‘t’] \\
     rename1 ‘y <= f (Normal a)’ \\
     CCONTR_TAC >> fs [GSYM extreal_lt_def] \\
     qabbrev_tac ‘x = @x. Normal a < x /\ f x <= y’ \\
     Suff ‘Normal a < x /\ f x <= y’
     >- (STRIP_TAC \\
        ‘x <= Normal a’ by rw [] \\
         METIS_TAC [let_antisym]) \\
  (* applying SELECT_ELIM_TAC, all @s must be moved to the goal *)
     qunabbrev_tac ‘x’ \\
     SELECT_ELIM_TAC >> simp [] \\
  (* applying right_continuous_at_thm *)
     MP_TAC (Q.SPECL [‘f’, ‘a’] right_continuous_at_thm) \\
     fs [right_continuous] \\
     qabbrev_tac ‘e = y - f (Normal a)’ \\
     DISCH_THEN (MP_TAC o Q.SPEC ‘e’) \\
     impl_tac (* 0 < e /\ e <> PosInf *)
     >- (‘y <> NegInf’ by rw [pos_not_neginf] \\
         Know ‘y <> PosInf’
         >- (simp [lt_infty] \\
             Q_TAC (TRANS_TAC let_trans) ‘1’ >> rw []) >> DISCH_TAC \\
         Q.PAT_X_ASSUM ‘f (Normal a) < y’ MP_TAC \\
        ‘?r. 0 <= r /\ r <= 1 /\ y = Normal r’
           by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_le_eq] \\
        ‘?z. f (Normal a) = Normal z’ by METIS_TAC [extreal_cases] \\
         simp [Abbr ‘e’, extreal_sub_def, extreal_of_num_def] \\
         rw [REAL_SUB_LT]) >> STRIP_TAC \\
     MP_TAC (Q.SPECL [‘a’, ‘a + d’] REAL_MEAN) >> rw [] \\
    ‘z - a < d’ by PROVE_TAC [REAL_LT_SUB_RADD, REAL_ADD_COMM] \\
     Q.EXISTS_TAC ‘Normal z’ >> simp [] \\
     Q.PAT_X_ASSUM ‘!x. x - a < d ==> _’ (MP_TAC o Q.SPEC ‘z’) \\
     simp [Abbr ‘e’] \\
     simp [le_rsub])
 >> DISCH_TAC
 (* Now analyzing those "extra points" in “t” but not in “s'” *)
 >> qabbrev_tac ‘N = t DIFF s'’
 >> Know ‘countable N’
 >- (Q.PAT_X_ASSUM ‘s' SUBSET t’ K_TAC \\
     Q.PAT_X_ASSUM ‘s' IN subsets Borel’ K_TAC \\
     simp [Abbr ‘N’, Abbr ‘t’, Abbr ‘s'’, Abbr ‘s’, DIFF_DEF] \\
     Q.PAT_X_ASSUM ‘m_space p = sp’ K_TAC \\
     simp [GSYM CONJ_ASSOC, GSYM extreal_lt_def, Abbr ‘sp’] \\
     simp [LEFT_AND_OVER_OR] \\
     Know ‘!x. 0 <= x /\ x <= f (Normal a) /\ 1 < x <=> F’
     >- (rw [] \\
         STRONG_DISJ_TAC >> simp [extreal_lt_def] \\
         STRONG_DISJ_TAC \\
         Q_TAC (TRANS_TAC le_trans) ‘f (Normal a)’ >> rw []) >> Rewr \\
     Know ‘!x. 0 <= x /\ x <= f (Normal a) /\ x < 0 <=> F’
     >- (rw [extreal_lt_def] >> METIS_TAC []) >> Rewr \\
     qmatch_abbrev_tac ‘countable N’ \\
     Know ‘N = {y | 0 <= y /\ y <= f (Normal a) /\ ?x. Normal a < x /\ f x = y}’
     >- (rw [Abbr ‘N’, Once EXTENSION] >> EQ_TAC >> rw [] >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           Q.EXISTS_TAC ‘y’ >> art [] \\
           rw [GSYM le_antisym] \\
           Q_TAC (TRANS_TAC le_trans) ‘f (Normal a)’ >> art [] \\
           FIRST_X_ASSUM MATCH_MP_TAC \\
           MATCH_MP_TAC lt_imp_le >> art [],
           (* goal 2 (of 2) *)
           rename1 ‘Normal a < x’ \\
           Q.EXISTS_TAC ‘x’ >> rw [] ]) >> Rewr' \\
     qunabbrev_tac ‘N’ \\
     qmatch_abbrev_tac ‘countable N’ \\
     Know ‘N = {y | y = f (Normal a) /\ ?x. Normal a < x /\ f x = y}’
     >- (rw [Abbr ‘N’, Once EXTENSION] >> EQ_TAC >> rw [] \\
         rename1 ‘Normal a < x’ \\
         simp [GSYM le_antisym] \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
         MATCH_MP_TAC lt_imp_le >> art []) >> Rewr' \\
     qunabbrev_tac ‘N’ \\
     qmatch_abbrev_tac ‘countable N’ \\
     qabbrev_tac ‘z = f (Normal a)’ \\
     Cases_on ‘?x. Normal a < x /\ f x = z’
     >- (Know ‘N = {z}’
         >- (rw [Abbr ‘N’, Once EXTENSION, Abbr ‘z’] >> METIS_TAC []) >> Rewr' \\
         rw [COUNTABLE_SING]) \\
     Know ‘N = {}’ >- (rw [Abbr ‘N’, Once EXTENSION] >> fs []) >> Rewr' \\
     REWRITE_TAC [countable_EMPTY])
 >> DISCH_TAC
 >> ‘DISJOINT s' N /\ t = s' UNION N’ by ASM_SET_TAC [] >> POP_ORW
 >> Know ‘real_set N = IMAGE real N’
 >- (rw [Once EXTENSION, real_set_def] \\
     EQ_TAC >> rw [] >> rename1 ‘y IN N’
     >- (Q.EXISTS_TAC ‘y’ >> art []) \\
     Q.EXISTS_TAC ‘y’ >> art [] \\
     POP_ASSUM MP_TAC \\
     Suff ‘!x. x IN t ==> x <> PosInf /\ x <> NegInf’ >- simp [Abbr ‘N’] \\
     Q.X_GEN_TAC ‘x’ >> simp [Abbr ‘t’] \\
     STRIP_TAC \\
     reverse CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf >> art []) \\
     simp [lt_infty] \\
     Q_TAC (TRANS_TAC let_trans) ‘f (Normal a)’ >> art [] \\
     simp [GSYM lt_infty])
 >> DISCH_THEN (ASSUME_TAC o SYM)
 >> ‘countable (real_set N)’ by PROVE_TAC [COUNTABLE_IMAGE]
 >> Know ‘l N = 0’
 >- (simp [Abbr ‘l’, o_DEF] \\
     MATCH_MP_TAC lambda_countable >> art [])
 >> DISCH_TAC
 >> Suff ‘l (s' UNION N) = l s' + l N’ >- rw []
 >> fs [Abbr ‘l’, o_DEF, real_set_UNION]
 >> Know ‘DISJOINT (real_set s') (real_set N)’
 >- (rw [DISJOINT_ALT, real_set_def] \\
     rename1 ‘real x = real y’ \\
     Cases_on ‘x = PosInf’ >> simp [] \\
     Cases_on ‘x = NegInf’ >> simp [] \\
    ‘x = y’ by METIS_TAC [real_11] >> POP_ORW \\
     Q.PAT_X_ASSUM ‘DISJOINT s' N’ MP_TAC \\
     rw [DISJOINT_ALT])
 >> DISCH_TAC
 >> qmatch_abbrev_tac ‘lambda (A UNION B) = _’
 >> Suff ‘lambda (A UNION B) = lambda A + lambda B’ >- rw []
 >> MATCH_MP_TAC ADDITIVE >> simp []
 >> ASSUME_TAC measure_space_lborel
 >> CONJ_TAC >- (MATCH_MP_TAC MEASURE_SPACE_ADDITIVE >> art [])
 >> ASSUME_TAC sigma_algebra_borel
 >> simp [sets_lborel]
 >> Suff ‘A IN subsets borel’
 >- (simp [] >> DISCH_TAC \\
     STRONG_CONJ_TAC >- (MATCH_MP_TAC countable_imp_borel_measurable >> art []) \\
     DISCH_TAC \\
     MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [])
 >> rw [Abbr ‘A’, borel_measurable_real_set]
QED

(* ------------------------------------------------------------------------- *)
(*  Various alternative definitions of distributions                         *)
(* ------------------------------------------------------------------------- *)

(* NOTE: This definition is dedicated for r.v.'s of ‘:'a -> real’ *)
Definition measurable_distr :
    measurable_distr p X =
      (\s. if s IN subsets borel then distribution p X s else 0)
End

(* |- !p X s.
        measurable_distr p X s =
        if s IN subsets borel then distribution p X s else 0
 *)
Theorem measurable_distr_def :
    !p X s. measurable_distr p X s =
            if s IN measurable_sets lborel then distribution p X s else 0
Proof
    rw [FUN_EQ_THM, sets_lborel, measurable_distr]
QED

Theorem distr_of_lborel :
    !p X. distr_of p lborel X =
            (m_space lborel, measurable_sets lborel, measurable_distr p X)
Proof
    rw [distr_of, measurable_distr, m_space_lborel, sets_lborel, FUN_EQ_THM,
        distribution_def, p_space_def, prob_def]
QED

(* NOTE: The new, shorter proof is based on pos_fn_integral_distr *)
Theorem lebesgue_real_affine :
    !c t. c <> 0 ==>
          measure_of lborel =
          measure_of
           (density
             (distr_of lborel (space borel, subsets borel, (\x. 0)) (\x. t + c * x))
             (\z. Normal (abs c)))
Proof
    RW_TAC std_ss []
 >> ASSUME_TAC sigma_algebra_borel
 >> MATCH_MP_TAC lborel_eqI
 >> qabbrev_tac ‘h = (\x :real. t + c * x)’
 >> Know ‘h IN measurable borel borel’
 >- (qunabbrev_tac ‘h’ \\
     MATCH_MP_TAC in_borel_measurable_add \\
     qexistsl_tac [‘\x. t’, ‘\x. c * x’] >> rw []
     >- (MATCH_MP_TAC in_borel_measurable_const \\
         Q.EXISTS_TAC ‘t’ >> rw []) \\
     MATCH_MP_TAC in_borel_measurable_cmul \\
     qexistsl_tac [‘\x. x’, ‘c’] >> simp [] \\
     REWRITE_TAC [in_borel_measurable_I])
 >> DISCH_TAC
 >> Know ‘measure_space (distr_of lborel (space borel,subsets borel,(\x. 0)) h)’
 >- (MATCH_MP_TAC measure_space_distr_of \\
     simp [lborel_def, measure_space_trivial'])
 >> DISCH_TAC
 >> reverse CONJ_TAC
 >- (reverse CONJ_TAC
     >- METIS_TAC [density_def, distr_of, measurable_sets_def] \\
     MATCH_MP_TAC measure_space_density >> simp [] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST \\
     Q.EXISTS_TAC `Normal (abs c)` \\
     simp [SPACE, distr_of, sigma_algebra_borel])
 >> Know ‘measure_space (space borel,subsets borel,distr lborel h)’
 >- (MATCH_MP_TAC measure_space_distr >> rw [lborel_def])
 >> DISCH_TAC
 (* stage work *)
 >> rw [distr_of_alt_distr, space_lborel, density]
 >> qmatch_abbrev_tac ‘pos_fn_integral (space borel,subsets borel,f) g = _’
 >> Know ‘!x. 0 <= g x’
 >- (rw [space_borel, Abbr ‘g’] \\
     MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS])
 >> DISCH_TAC
 >> Know ‘g IN Borel_measurable borel’
 >- (qunabbrev_tac ‘g’ \\
     HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL_INDICATOR \\
     rw [CLOSED_interval, borel_measurable_sets])
 >> DISCH_TAC
 >> Know ‘pos_fn_integral (space borel,subsets borel,f) g =
          pos_fn_integral (space borel,subsets borel,distr lborel h) g’
 >- (MATCH_MP_TAC pos_fn_integral_cong_measure >> simp [Abbr ‘f’] \\
     fs [distr_of_alt_distr])
 >> Rewr'
 >> Know ‘pos_fn_integral (space borel,subsets borel,distr lborel h) g =
          pos_fn_integral lborel (g o h)’
 >- (MATCH_MP_TAC pos_fn_integral_distr \\
     rw [lborel_def, SPACE, m_space_lborel, sets_lborel])
 >> Rewr'
 >> NTAC 2 (POP_ASSUM K_TAC)
 >> Q.PAT_X_ASSUM ‘h IN borel_measurable borel’ K_TAC
 >> rpt (Q.PAT_X_ASSUM ‘measure_space _’ K_TAC)
 >> simp [Abbr ‘g’, Abbr ‘h’, o_DEF, Abbr ‘f’]
 >> qabbrev_tac ‘s = interval [a,b]’
 >> qabbrev_tac ‘f = \x. indicator_fn s (t + c * x)’
 >> simp []
 >> Know ‘pos_fn_integral lborel (\x. Normal (abs c) * f x) =
          Normal (abs c) * pos_fn_integral lborel f’
 >- (MATCH_MP_TAC pos_fn_integral_cmul \\
     rw [abs_pos, lborel_def, Abbr ‘f’, INDICATOR_FN_POS])
 >> Rewr'
 (* applying pos_fn_integral_indicator *)
 >> Cases_on ‘0 < c’
 >- (qabbrev_tac ‘s' = interval [(a - t) / c, (b - t) / c]’ \\
     Know ‘f = indicator_fn s'’
     >- (rw [FUN_EQ_THM, Abbr ‘f’] \\
         simp [indicator_fn_def, Abbr ‘s’, Abbr ‘s'’, CLOSED_interval] \\
         simp [REAL_ARITH “a <= t + c * x <=> a - t <= c * (x :real)”,
               REAL_ARITH “t + c * x <= b <=> c * x <= b - (t :real)”]) >> Rewr' \\
     Know ‘pos_fn_integral lborel (indicator_fn s') = measure lborel s'’
     >- (MATCH_MP_TAC pos_fn_integral_indicator \\
         rw [lborel_def, Abbr ‘s'’, CLOSED_interval] \\
         Know ‘!x. a - t <= c * x <=> (a - t) / c <= x’
         >- (Q.X_GEN_TAC ‘x’ \\
             REWRITE_TAC [Once EQ_SYM_EQ, Once REAL_MUL_COMM] \\
             MATCH_MP_TAC REAL_LE_LDIV_EQ >> art []) >> Rewr' \\
         Know ‘!x. c * x <= b - t <=> x <= (b - t) / c’
         >- (Q.X_GEN_TAC ‘x’ \\
             REWRITE_TAC [Once EQ_SYM_EQ, Once REAL_MUL_COMM] \\
             MATCH_MP_TAC REAL_LE_RDIV_EQ >> art []) >> Rewr' \\
         SIMP_TAC std_ss [borel_measurable_sets, sets_lborel]) >> Rewr' \\
     simp [CONTENT_CLOSED_INTERVAL_CASES, Abbr ‘s’] \\
     qabbrev_tac ‘a' = (a - t) / c’ \\
     qabbrev_tac ‘b' = (b - t) / c’ \\
     Know ‘a <= b <=> a' <= b'’
     >- (simp [Abbr ‘a'’, Abbr ‘b'’, real_div] \\
         REAL_ARITH_TAC) >> DISCH_TAC \\
     Cases_on ‘a <= b’
     >- (fs [Abbr ‘s'’, lambda_closed_interval] \\
         simp [extreal_mul_eq, Abbr ‘b'’, Abbr ‘a'’] \\
        ‘abs c = c’ by METIS_TAC [ABS_REFL, REAL_LT_IMP_LE] >> POP_ORW \\
         simp [REAL_DIV_SUB] >> REAL_ARITH_TAC) \\
     fs [] \\
    ‘s' = {}’ by rw [Abbr ‘s'’, GSYM INTERVAL_EQ_EMPTY, real_lt] \\
     simp [lambda_empty])
 >> Know ‘c < 0’ >- (simp [REAL_LT_LE] >> fs [real_lt])
 >> POP_ASSUM K_TAC
 >> DISCH_TAC
 >> qabbrev_tac ‘s' = interval [(b - t) / c, (a - t) / c]’
 >> Know ‘f = indicator_fn s'’
 >- (rw [FUN_EQ_THM, Abbr ‘f’] \\
     simp [indicator_fn_def, Abbr ‘s’, Abbr ‘s'’, CLOSED_interval] \\
     REWRITE_TAC [Once CONJ_COMM] \\
     simp [REAL_ARITH “a <= t + c * x <=> a - t <= c * (x :real)”,
           REAL_ARITH “t + c * x <= b <=> c * x <= b - (t :real)”])
 >> Rewr'
 >> Know ‘pos_fn_integral lborel (indicator_fn s') = measure lborel s'’
 >- (MATCH_MP_TAC pos_fn_integral_indicator \\
     rw [lborel_def, Abbr ‘s'’, CLOSED_interval] \\
     Know ‘!x. a - t <= c * x <=> x <= (a - t) / c’
     >- (Q.X_GEN_TAC ‘x’ \\
         REWRITE_TAC [Once EQ_SYM_EQ, Once REAL_MUL_COMM] \\
         MATCH_MP_TAC REAL_LE_LDIV_EQ_NEG >> art []) >> Rewr' \\
     Know ‘!x. c * x <= b - t <=> (b - t) / c <= x’
     >- (Q.X_GEN_TAC ‘x’ \\
         REWRITE_TAC [Once EQ_SYM_EQ, Once REAL_MUL_COMM] \\
         MATCH_MP_TAC REAL_LE_RDIV_EQ_NEG >> art []) >> Rewr' \\
     SIMP_TAC std_ss [borel_measurable_sets, sets_lborel])
 >> Rewr'
 >> simp [CONTENT_CLOSED_INTERVAL_CASES, Abbr ‘s’]
 >> qabbrev_tac ‘a' = (a - t) / c’
 >> qabbrev_tac ‘b' = (b - t) / c’
 >> Know ‘a <= b <=> b' <= a'’
 >- (simp [Abbr ‘a'’, Abbr ‘b'’, real_div] \\
     REAL_ARITH_TAC) >> DISCH_TAC
 >> Cases_on ‘a <= b’
 >- (fs [Abbr ‘s'’, lambda_closed_interval] \\
     simp [extreal_mul_eq, Abbr ‘b'’, Abbr ‘a'’] \\
    ‘abs c = -c’ by METIS_TAC [ABS_EQ_NEG] >> POP_ORW \\
     simp [REAL_DIV_SUB] >> REAL_ARITH_TAC)
 >> fs []
 >> ‘s' = {}’ by rw [Abbr ‘s'’, GSYM INTERVAL_EQ_EMPTY, real_lt]
 >> simp [lambda_empty]
QED

(* NOTE: New proof by pos_fn_integral_density_reduce and pos_fn_integral_distr *)
Theorem lebesgue_pos_integral_real_affine :
    !f c t. c <> 0 /\ f IN measurable borel Borel ==>
           (pos_fn_integral lborel (\x. max 0 (f x)) =
            Normal (abs c) * pos_fn_integral lborel (\x. max 0 (f (t + c * x))))
Proof
    RW_TAC std_ss []
 >> ‘measure_space lborel’ by rw [lborel_def]
 >> ‘measure_space (measure_of lborel)’ by rw [measure_of_measure_space]
 >> Know ‘pos_fn_integral lborel (\x. max 0 (f x)) =
          pos_fn_integral (measure_of lborel) (\x. max 0 (f x))’
 >- (MATCH_MP_TAC pos_fn_integral_cong_measure' \\
     rw [measure_space_eq_measure_of, le_max])
 >> Rewr'
 >> MP_TAC (Q.SPECL [‘c’, ‘t’] lebesgue_real_affine) >> art []
 >> Rewr'
 >> qmatch_abbrev_tac ‘pos_fn_integral (measure_of M) g = _’
 >> qabbrev_tac ‘h = (\x :real. t + c * x)’
 >> Know ‘h IN measurable borel borel’
 >- (qunabbrev_tac ‘h’ \\
     MATCH_MP_TAC in_borel_measurable_add \\
     ASSUME_TAC sigma_algebra_borel \\
     qexistsl_tac [‘\x. t’, ‘\x. c * x’] >> rw []
     >- (MATCH_MP_TAC in_borel_measurable_const \\
         Q.EXISTS_TAC ‘t’ >> rw []) \\
     MATCH_MP_TAC in_borel_measurable_cmul \\
     qexistsl_tac [‘\x. x’, ‘c’] >> simp [] \\
     REWRITE_TAC [in_borel_measurable_I])
 >> DISCH_TAC
 >> Know ‘measure_space M’
 >- (qunabbrev_tac ‘M’ \\
     MATCH_MP_TAC measure_space_density \\
     ASSUME_TAC sigma_algebra_borel \\
     CONJ_TAC
     >- (MATCH_MP_TAC measure_space_distr_of \\
         rw [lborel_def, measure_space_trivial']) \\
     rw [distr_of] \\
     HO_MATCH_MP_TAC (REWRITE_RULE [o_DEF] IN_MEASURABLE_BOREL_IMP_BOREL') >> rw [] \\
     MATCH_MP_TAC in_borel_measurable_const \\
     Q.EXISTS_TAC ‘abs c’ >> rw [])
 >> DISCH_TAC
 >> ‘measure_space (measure_of M)’ by rw [measure_of_measure_space]
 >> Know ‘pos_fn_integral (measure_of M) g = pos_fn_integral M g’
 >- (MATCH_MP_TAC pos_fn_integral_cong_measure' \\
     rw [measure_space_eq_measure_of', le_max, Abbr ‘g’])
 >> Rewr'
 (* applying pos_fn_integral_density_reduce *)
 >> qunabbrev_tac ‘M’
 >> qmatch_abbrev_tac ‘pos_fn_integral (density N ff) _ = _’
 >> Know ‘measure_space N’
 >- (qunabbrev_tac ‘N’ \\
     MATCH_MP_TAC measure_space_distr_of \\
     rw [measure_space_trivial', lborel_def, sigma_algebra_borel])
 >> DISCH_TAC
 >> Know ‘ff IN Borel_measurable (measurable_space N)’
 >- (qunabbrev_tac ‘ff’ \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST \\
     Q.EXISTS_TAC ‘Normal (abs c)’ >> rw [Abbr ‘N’, distr_of])
 >> DISCH_TAC
 >> Know ‘g IN Borel_measurable (measurable_space N)’
 >- (‘g = fn_plus f’ by rw [FUN_EQ_THM, Abbr ‘g’, FN_PLUS_ALT, Once max_comm] \\
     POP_ORW \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_FN_PLUS \\
     rw [Abbr ‘N’, distr_of])
 >> DISCH_TAC
 >> Know ‘pos_fn_integral (density N ff) g = pos_fn_integral N (\x. ff x * g x)’
 >- (MATCH_MP_TAC pos_fn_integral_density_reduce >> art [] \\
     rw [Abbr ‘ff’, abs_pos] \\
     rw [Abbr ‘g’, le_max])
 >> Rewr'
 >> simp [Abbr ‘ff’]
 >> Know ‘pos_fn_integral N (\x. Normal (abs c) * g x) =
          Normal (abs c) * pos_fn_integral N g’
 >- (MATCH_MP_TAC pos_fn_integral_cmul >> rw [abs_pos] \\
     rw [Abbr ‘g’, le_max])
 >> Rewr'
 >> Suff ‘pos_fn_integral N g = pos_fn_integral lborel (\x. g (h x))’ >- rw []
 >> qunabbrev_tac ‘N’
 >> qmatch_abbrev_tac ‘pos_fn_integral (distr_of lborel N _) _ = _’
 >> Suff ‘pos_fn_integral (distr_of lborel N h) g =
          pos_fn_integral lborel (g o h)’ >- rw [o_DEF]
 >> MATCH_MP_TAC pos_fn_integral_distr_of
 >> simp [lborel_def, Abbr ‘N’, measure_space_trivial', sigma_algebra_borel]
 >> reverse CONJ_TAC >- rw [Abbr ‘g’, le_max]
 >> ‘g = fn_plus f’ by rw [FUN_EQ_THM, Abbr ‘g’, FN_PLUS_ALT, Once max_comm]
 >> POP_ORW
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_FN_PLUS
 >> rw [sigma_algebra_borel]
QED

(* NOTE: "modern" version without using “max” *)
Theorem lebesgue_pos_integral_real_affine' :
    !f c t. c <> 0 /\ f IN measurable borel Borel /\ (!x. 0 <= f x) ==>
            pos_fn_integral lborel f =
            Normal (abs c) * pos_fn_integral lborel (\x. f (t + c * x))
Proof
    rpt STRIP_TAC
 >> ‘f = \x. max 0 (f x)’ by rw [FUN_EQ_THM, max_0_reduce]
 >> POP_ORW
 >> simp []
 >> MATCH_MP_TAC lebesgue_pos_integral_real_affine >> art []
QED

(* See, e.g., [3, p.117] or [4, p.375]

   NOTE: In some textbooks, g is said to be in "C_B" (the class of bounded
   continuous functions).
 *)
Definition weak_converge_def :
    weak_converge (fi :num -> extreal measure) (f :extreal measure) =
    !(g :real -> real).
        bounded (IMAGE g UNIV) /\ g continuous_on UNIV ==>
        ((\n. integral (space Borel,subsets Borel,fi n) (Normal o g o real)) -->
          integral (space Borel,subsets Borel,f) (Normal o g o real)) sequentially
End

Overload "-->" = “weak_converge”

(* some shared tactics for the next two theorems *)
val converge_in_dist_tactic1 =
    qabbrev_tac ‘f = Normal o g o real’ \\
    Know ‘!n. integral (space Borel,subsets Borel,distr p (X n)) f =
              integral p (f o X n)’
    >- (Q.X_GEN_TAC ‘n’ \\
        MATCH_MP_TAC (cj 1 integral_distr) \\
        simp [SIGMA_ALGEBRA_BOREL, Abbr ‘f’] \\
        MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
        simp [SIGMA_ALGEBRA_BOREL] \\
       ‘g IN borel_measurable borel’
          by PROVE_TAC [in_borel_measurable_continuous_on] \\
        MATCH_MP_TAC MEASURABLE_COMP \\
        Q.EXISTS_TAC ‘borel’ >> rw [real_in_borel_measurable]) >> Rewr' \\
    Know ‘!n. integral (space Borel,subsets Borel,distr p Y) f = integral p (f o Y)’
    >- (MATCH_MP_TAC (cj 1 integral_distr) \\
        simp [SIGMA_ALGEBRA_BOREL, Abbr ‘f’] \\
        MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
        simp [SIGMA_ALGEBRA_BOREL] \\
       ‘g IN borel_measurable borel’
          by PROVE_TAC [in_borel_measurable_continuous_on] \\
        MATCH_MP_TAC MEASURABLE_COMP \\
        Q.EXISTS_TAC ‘borel’ >> rw [real_in_borel_measurable]) >> Rewr' \\
    simp [Abbr ‘f’];

val converge_in_dist_tactic2 =
    qabbrev_tac ‘g = Normal o f o real’ \\
   ‘!n. Normal o f o real o X n = g o X n’ by METIS_TAC [o_ASSOC] >> POP_ORW \\
   ‘Normal o f o real o Y = g o Y’ by METIS_TAC [o_ASSOC] >> POP_ORW \\
    Q.PAT_X_ASSUM ‘!g. bounded (IMAGE g UNIV) /\ _ ==> _’ (MP_TAC o Q.SPEC ‘f’) \\
    simp [] \\
    Know ‘!n. integral (space Borel,subsets Borel,distr p (X n)) g =
              integral p (g o X n)’
    >- (Q.X_GEN_TAC ‘n’ \\
        MATCH_MP_TAC (cj 1 integral_distr) \\
        simp [SIGMA_ALGEBRA_BOREL, Abbr ‘g’] \\
        MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
        simp [SIGMA_ALGEBRA_BOREL] \\
       ‘f IN borel_measurable borel’
          by PROVE_TAC [in_borel_measurable_continuous_on] \\
        MATCH_MP_TAC MEASURABLE_COMP \\
        Q.EXISTS_TAC ‘borel’ >> rw [real_in_borel_measurable]) >> Rewr' \\
    Know ‘!n. integral (space Borel,subsets Borel,distr p Y) g = integral p (g o Y)’
    >- (MATCH_MP_TAC (cj 1 integral_distr) \\
        simp [SIGMA_ALGEBRA_BOREL, Abbr ‘g’] \\
        MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
        simp [SIGMA_ALGEBRA_BOREL] \\
       ‘f IN borel_measurable borel’
          by PROVE_TAC [in_borel_measurable_continuous_on] \\
        MATCH_MP_TAC MEASURABLE_COMP \\
        Q.EXISTS_TAC ‘borel’ >> rw [real_in_borel_measurable]) >> Rewr;

(* IMPORTANT: convergence of r.v. in distribution is equivalent to weak convergence of
   their distribution functions.
 *)
Theorem converge_in_dist_alt :
    !p X Y. prob_space p /\
           (!n. real_random_variable (X n) p) /\ real_random_variable Y p ==>
           ((X --> Y) (in_distribution p) <=>
            (\n. distribution p (X n)) --> distribution p Y)
Proof
    rw [converge_in_dist_def, weak_converge_def, expectation_def, distribution_distr,
        real_random_variable, prob_space_def, p_space_def, events_def]
 >> EQ_TAC >> rw []
 >| [ (* goal 1 (of 2) *)
      converge_in_dist_tactic1,
      (* goal 2 (of 2) *)
      converge_in_dist_tactic2 ]
QED

(* Theorem 4.4.2 [2, p.93] *)
Theorem converge_in_dist_alt' :
    !p X Y. prob_space p /\
           (!n. real_random_variable (X n) p) /\ real_random_variable Y p ==>
           ((X --> Y) (in_distribution p) <=>
            !f. bounded (IMAGE f UNIV) /\ f continuous_on univ(:real) ==>
               ((\n. expectation p (Normal o f o real o (X n))) -->
                expectation p (Normal o f o real o Y)) sequentially)
Proof
    rw [converge_in_dist_alt, weak_converge_def, distribution_distr, expectation_def,
        real_random_variable, prob_space_def, p_space_def, events_def]
 >> EQ_TAC >> rw []
 >| [ (* goal 1 (of 2) *)
      converge_in_dist_tactic2,
      (* goal 2 (of 2) *)
      converge_in_dist_tactic1 ]
QED

(* ------------------------------------------------------------------------- *)
(*  PDF (for r.v.'s of type :'a -> real, aka old style r.v.'s)               *)
(* ------------------------------------------------------------------------- *)

(* This definition comes from HVG's original work (real-based)

   cf. probabilityTheory.prob_density_function_def (extreal-based)
 *)
Definition PDF_def :
    PDF p X = RN_deriv (distribution p X) lborel
End

Theorem PDF_LE_POS :
    !p X. prob_space p /\ random_variable X p borel /\
          distribution p X << lborel ==> !x. 0 <= PDF p X x
Proof
    rpt STRIP_TAC
 >> `measure_space (space borel, subsets borel, distribution p X)`
       by PROVE_TAC [distribution_prob_space, prob_space_def,
                     sigma_algebra_borel]
 >> ASSUME_TAC sigma_finite_lborel
 >> ASSUME_TAC measure_space_lborel
 >> MP_TAC (ISPECL [“lborel”, “distribution (p :'a m_space) (X :'a -> real)”]
                   Radon_Nikodym')
 >> RW_TAC std_ss [m_space_lborel, sets_lborel, space_borel, IN_UNIV]
 >> fs [PDF_def, RN_deriv_def, m_space_def, measurable_sets_def,
        m_space_lborel, sets_lborel, space_borel]
 >> SELECT_ELIM_TAC >> METIS_TAC []
QED

Theorem EXPECTATION_PDF[local] :
    !p X. prob_space p /\ random_variable X p borel /\
          distribution p X << lborel ==>
          PDF p X IN Borel_measurable borel /\
          expectation lborel (PDF p X) = 1
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> `prob_space (space borel, subsets borel, distribution p X)`
       by PROVE_TAC [distribution_prob_space, sigma_algebra_borel]
 >> NTAC 2 (POP_ASSUM MP_TAC) >> KILL_TAC
 >> simp [prob_space_def, p_space_def, m_space_def, measure_def, expectation_def]
 >> NTAC 2 STRIP_TAC
 >> ASSUME_TAC sigma_finite_lborel
 >> ASSUME_TAC measure_space_lborel
 >> MP_TAC (ISPECL [“lborel”, “distribution (p :'a m_space) (X :'a -> real)”]
                   Radon_Nikodym')
 >> simp [m_space_lborel, sets_lborel, m_space_def, measure_def]
 >> STRIP_TAC
 >> fs [PDF_def, RN_deriv_def, m_space_def, measurable_sets_def,
        m_space_lborel, sets_lborel]
 >> SELECT_ELIM_TAC
 >> CONJ_TAC >- METIS_TAC []
 >> Q.X_GEN_TAC `g`
 >> simp [density_measure_def]
 >> STRIP_TAC
 >> POP_ASSUM (MP_TAC o Q.SPEC `space borel`)
 >> impl_tac (* `space borel IN subsets borel` *)
 >- (`sigma_algebra borel` by PROVE_TAC [sigma_algebra_borel] \\
     PROVE_TAC [sigma_algebra_def, ALGEBRA_SPACE])
 >> DISCH_TAC
 >> Know `integral lborel g = pos_fn_integral lborel g`
 >- (MATCH_MP_TAC integral_pos_fn >> art [] \\
     fs [space_borel])
 >> Rewr'
 >> Suff `pos_fn_integral lborel g =
          pos_fn_integral lborel (\x. g x * indicator_fn (space borel) x)`
 >- rw []
 >> MATCH_MP_TAC pos_fn_integral_cong
 >> rw [m_space_lborel, indicator_fn_def, mul_rone, mul_rzero, le_refl]
QED

(* |- !p X.
        prob_space p /\ random_variable X p borel /\
        distribution p X << lborel ==>
        expectation lborel (PDF p X) = 1
 *)
Theorem EXPECTATION_PDF_1 = cj 2 EXPECTATION_PDF

(* |- !p X.
        prob_space p /\ random_variable X p borel /\
        distribution p X << lborel ==>
        integral lborel (PDF p X) = 1
 *)
Theorem INTEGRAL_PDF_1 = REWRITE_RULE [expectation_def] EXPECTATION_PDF_1

(* |- !p X.
        prob_space p /\ random_variable X p borel /\
        distribution p X << lborel ==>
        PDF p X IN Borel_measurable borel
 *)
Theorem PDF_IN_MEASURABLE_BOREL = cj 1 EXPECTATION_PDF

(* ------------------------------------------------------------------------- *)
(*  Normal density                                                           *)
(* ------------------------------------------------------------------------- *)

(* NOTE: ‘normal_density m s’ is a function of “:real -> real”, where m is the
   expectation, s is the standard deviation.
 *)
Definition normal_density :
    normal_density mu sig x =
      (1 / sqrt (2 * pi * sig pow 2)) * exp (-((x - mu) pow 2) / (2 * sig pow 2))
End

Overload std_normal_density = “normal_density 0 1”
Overload Normal_density = “\mu sig x. Normal (normal_density mu sig x)”

Theorem std_normal_density_def :
    !x. std_normal_density x = (1 / sqrt (2 * pi)) * exp (-(x pow 2) / 2)
Proof
    RW_TAC std_ss [normal_density]
 >> SIMP_TAC real_ss [REAL_SUB_RZERO, POW_ONE]
QED

Theorem normal_density_nonneg :
    !mu sig x. 0 <= normal_density mu sig x
Proof
  RW_TAC std_ss [normal_density] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  SIMP_TAC std_ss [EXP_POS_LE, GSYM REAL_INV_1OVER, REAL_LE_INV_EQ] THEN
  MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC real_ss [REAL_LE_LT, PI_POS],
   ALL_TAC] THEN
  SIMP_TAC real_ss [REAL_LE_POW2]
QED

Theorem normal_density_pos :
    !mu sig. 0 < sig ==> 0 < normal_density mu sig x
Proof
  RW_TAC std_ss [normal_density] THEN MATCH_MP_TAC REAL_LT_MUL THEN
  SIMP_TAC std_ss [EXP_POS_LT, GSYM REAL_INV_1OVER, REAL_LT_INV_EQ] THEN
  MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN SIMP_TAC real_ss [PI_POS], ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LT >> art []
QED

Theorem normal_density_continuous_on :
    !mu sig s. normal_density mu sig continuous_on s
Proof
    rpt GEN_TAC
 >> ‘normal_density mu sig =
       (\x. 1 / sqrt (2 * pi * sig pow 2) *
            exp (-((x - mu) pow 2) / (2 * sig pow 2)))’
       by rw [normal_density, FUN_EQ_THM]
 >> POP_ORW
 >> HO_MATCH_MP_TAC (SIMP_RULE std_ss [o_DEF] CONTINUOUS_ON_COMPOSE)
 >> reverse CONJ_TAC
 >- (‘$* (1 / sqrt (2 * pi * sig pow 2)) = \x. (1 / sqrt (2 * pi * sig pow 2)) * x’
       by rw [FUN_EQ_THM] >> POP_ORW \\
     HO_MATCH_MP_TAC CONTINUOUS_ON_CMUL >> rw [CONTINUOUS_ON_ID])
 >> HO_MATCH_MP_TAC (SIMP_RULE std_ss [o_DEF] CONTINUOUS_ON_COMPOSE)
 >> reverse CONJ_TAC
 >- rw [CONTINUOUS_ON_EXP]
 >> REWRITE_TAC [real_div, Once REAL_MUL_COMM]
 >> HO_MATCH_MP_TAC CONTINUOUS_ON_CMUL
 >> REWRITE_TAC [Once REAL_NEG_MINUS1]
 >> HO_MATCH_MP_TAC CONTINUOUS_ON_CMUL
 >> HO_MATCH_MP_TAC CONTINUOUS_ON_POW
 >> HO_MATCH_MP_TAC CONTINUOUS_ON_SUB
 >> rw [CONTINUOUS_ON_ID, CONTINUOUS_ON_CONST]
QED

Theorem in_measurable_borel_normal_density :
    !mu sig. normal_density mu sig IN borel_measurable borel
Proof
    rpt GEN_TAC
 >> MATCH_MP_TAC in_borel_measurable_continuous_on
 >> rw [normal_density_continuous_on]
QED

(* NOTE: The o-version looks nice but is not practical in use. *)
Theorem IN_MEASURABLE_BOREL_normal_density_o[local] :
    !mu sig. Normal o normal_density mu sig IN Borel_measurable borel
Proof
    rpt GEN_TAC
 >> HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL'
 >> rw [sigma_algebra_borel, in_measurable_borel_normal_density]
QED

Theorem IN_MEASURABLE_BOREL_normal_density :
    !mu sig. (\x. Normal (normal_density mu sig x)) IN
              measurable (m_space lborel, measurable_sets lborel) Borel
Proof
    rw [lborel_def, REWRITE_RULE [o_DEF] IN_MEASURABLE_BOREL_normal_density_o]
QED

(* |- !mu sig.
        (\x. Normal (normal_density mu sig x)) IN Borel_measurable borel
 *)
Theorem IN_MEASURABLE_BOREL_normal_density' =
        IN_MEASURABLE_BOREL_normal_density |> REWRITE_RULE [lborel_def]

Definition normal_pmeasure :
    normal_pmeasure mu sig =
    (\A. if A IN measurable_sets lborel then
            pos_fn_integral lborel
             (\x. Normal (normal_density mu sig x) * indicator_fn A x)
         else 0)
End

(* |- !mu sig A.
        normal_pmeasure mu sig A =
        if A IN measurable_sets lborel then
          pos_fn_integral lborel
            (\x. Normal (normal_density mu sig x) * indicator_fn A x)
        else 0
 *)
Theorem normal_pmeasure_def = SIMP_RULE std_ss [FUN_EQ_THM] normal_pmeasure

Theorem normal_pmeasure_alt_density_measure :
    !mu sig s. normal_pmeasure mu sig s =
               if s IN measurable_sets lborel then
                  density_measure lborel (Normal o normal_density mu sig) s
               else
                  0
Proof
    rw [normal_pmeasure_def, density_measure_def, o_DEF]
QED

(* NOTE: The old (bad) statements, the new proof based on pos_fn_integral_eq_0 *)
Theorem null_sets_density_iff[local] :
    !f A M. measure_space M /\ (!x. x IN m_space M ==> 0 <= f x) /\
            f IN measurable (m_space M, measurable_sets M) Borel ==>
    ((A IN measurable_sets M /\
      measure ((m_space M,measurable_sets M,
        (\A.
           if A IN measurable_sets M then
             pos_fn_integral M (\x. f x * indicator_fn A x)
           else 0))) A = 0) <=>
     (A IN measurable_sets M /\ AE x::M. x IN A ==> f x <= 0))
Proof
    RW_TAC std_ss []
 >> MATCH_MP_TAC (TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`)
 >> DISCH_TAC
 (* below are new proofs *)
 >> simp [measure_def]
 >> qmatch_abbrev_tac ‘pos_fn_integral M g = 0 <=> _’
 (* applying pos_fn_integral_eq_0 *)
 >> MP_TAC (Q.SPECL [‘M’, ‘g’] pos_fn_integral_eq_0) >> art []
 >> Know ‘!x. x IN m_space M ==> 0 <= g x’
 >- (rw [Abbr ‘g’] \\
     MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS])
 >> DISCH_TAC
 >> Know ‘g IN Borel_measurable (measurable_space M)’
 >- (fs [Abbr ‘g’] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR \\
     rw [subsets_def])
 >> DISCH_TAC
 >> simp []
 >> DISCH_THEN K_TAC
 >> qmatch_abbrev_tac ‘measure M N = 0 <=> _’
 >> Know ‘N IN measurable_sets M’
 >- (qunabbrev_tac ‘N’ \\
    ‘{x | x IN m_space M /\ g x <> 0} = {x | g x <> 0} INTER m_space M’
      by SET_TAC [] >> POP_ORW \\
     simp [IN_MEASURABLE_BOREL_ALL_MEASURE])
 >> DISCH_TAC
 >> EQ_TAC
 >- (rw [AE_ALT, null_set_def] \\
     Q.EXISTS_TAC ‘N’ >> art [] \\
     NTAC 2 (POP_ASSUM K_TAC) \\
     rw [SUBSET_DEF, Abbr ‘N’, Abbr ‘g’, GSYM extreal_lt_def]
     >- PROVE_TAC [lt_imp_ne] \\
     rw [indicator_fn_def])
 >> rw [AE_ALT, GSYM IN_NULL_SET, GSYM extreal_lt_def]
 >> POP_ASSUM MP_TAC
 >> ‘{x | x IN m_space M /\ x IN A /\ 0 < f x} =
     {x | 0 < f x} INTER m_space M INTER A’ by SET_TAC [] >> POP_ORW
 >> qmatch_abbrev_tac ‘P INTER A SUBSET N' ==> _’
 >> DISCH_TAC
 >> Know ‘P INTER A IN measurable_sets M’
 >- (MATCH_MP_TAC MEASURE_SPACE_INTER >> art [] \\
     qunabbrev_tac ‘P’ \\
     simp [IN_MEASURABLE_BOREL_ALL_MEASURE])
 >> DISCH_TAC
 (* applying NULL_SET_MONO *)
 >> Know ‘P INTER A IN null_set M’ >- PROVE_TAC [NULL_SET_MONO]
 >> rw [IN_NULL_SET, null_set_def]
 >> Suff ‘N = P INTER A’ >- rw []
 >> rw [Once EXTENSION, Abbr ‘N’, Abbr ‘P’, Abbr ‘g’, indicator_fn_def]
 >> reverse EQ_TAC >> rw [] >- PROVE_TAC [lt_imp_ne]
 >> Q.PAT_X_ASSUM ‘!x. x IN m_space M ==> 0 <= f x’ drule
 >> simp [le_lt]
QED

Theorem normal_measure_abs_continuous :
    !mu sig. measure_absolutely_continuous (normal_pmeasure mu sig) lborel
Proof
    RW_TAC std_ss []
 >> SIMP_TAC std_ss [measure_absolutely_continuous_def]
 >> RW_TAC std_ss [measurable_sets_def, measure_def]
 >> ONCE_REWRITE_TAC [normal_pmeasure]
 >> Q.ABBREV_TAC `f = (\x. Normal (normal_density mu sig x))`
 >> simp []
 >> rename1 ‘lambda A = 0’
 >> Suff `A IN measurable_sets lborel /\
   (measure (m_space lborel, measurable_sets lborel,
    (\A. if A IN measurable_sets lborel then
          pos_fn_integral lborel (\x. f x * indicator_fn A x)
         else 0)) A = 0)`
 >- (RW_TAC std_ss [measure_def])
 >> Suff `measure_space lborel /\ (!x. x IN m_space lborel ==> 0 <= f x) /\
          f IN measurable (m_space lborel,measurable_sets lborel) Borel`
 >- (DISCH_THEN (MP_TAC o MATCH_MP null_sets_density_iff) \\
     DISCH_THEN (MP_TAC o Q.SPEC `A`) >> Rewr' \\
     fs [sets_lborel] \\
     rw [AE_ALT, null_set_def, GSYM extreal_lt_def, space_lborel, sets_lborel] \\
     Q.EXISTS_TAC ‘A’ >> art [] \\
     rw [SUBSET_DEF])
 (* stage work *)
 >> simp [space_lborel]
 >> `(!x. 0 <= f x)`
     by METIS_TAC [normal_density_nonneg, extreal_of_num_def, extreal_le_def]
 >> ASM_SIMP_TAC std_ss [lborel_def]
 >> Q.UNABBREV_TAC `f`
 >> SIMP_TAC std_ss [IN_MEASURABLE_BOREL_normal_density, GSYM space_lborel]
QED

(* NOTE: This shorter new proof is based on measure_space_density *)
Theorem normal_measure_space :
    !mu sig. measure_space (space borel,subsets borel,normal_pmeasure mu sig)
Proof
    rpt GEN_TAC
 >> qabbrev_tac ‘f = Normal o normal_density mu sig’
 >> Know ‘measure_space (space borel,subsets borel,normal_pmeasure mu sig) <=>
          measure_space (density lborel f)’
 >- (simp [density_def, space_lborel, sets_lborel, space_borel] \\
     MATCH_MP_TAC measure_space_cong \\
     rw [GSYM sets_lborel, normal_pmeasure_alt_density_measure])
 >> Rewr'
 >> MATCH_MP_TAC measure_space_density
 >> simp [lborel_def, Abbr ‘f’, o_DEF, IN_MEASURABLE_BOREL_normal_density',
          space_lborel, normal_density_nonneg]
QED

(* ------------------------------------------------------------------------- *)
(*  Normal random variable                                                   *)
(* ------------------------------------------------------------------------- *)

Theorem PDF_ALT :
    !p X. PDF p X = RN_deriv (measurable_distr p X) lborel
Proof
    rw [PDF_def, RN_deriv_def]
 >> Suff ‘!f. (!s. s IN measurable_sets lborel ==>
                (f * lborel) s = distribution p X s) <=>
              (!s. s IN measurable_sets lborel ==>
                (f * lborel) s = measurable_distr p X s)’
 >- Rewr
 >> Q.X_GEN_TAC ‘f’
 >> EQ_TAC >> rw [measurable_distr_def]
QED

Theorem distribution_alt_measurable_distr :
    !p X s. s IN measurable_sets lborel ==>
            distribution p X s = measurable_distr p X s
Proof
    rw [measurable_distr_def]
QED

Theorem measurable_distr_abs_continuous_alt :
    !p X. measurable_distr p X << lborel <=> distribution p X << lborel
Proof
    rw [measurable_distr, measure_absolutely_continuous_def, sets_lborel]
QED

(* |- !p X.
        prob_space p /\ random_variable X p borel /\
        measurable_distr p X << lborel ==>
        PDF p X IN Borel_measurable borel
 *)
Theorem PDF_IN_MEASURABLE_BOREL' =
        PDF_IN_MEASURABLE_BOREL
     |> REWRITE_RULE [GSYM measurable_distr_abs_continuous_alt]

(* |- !p X.
        prob_space p /\ random_variable X p borel /\
        measurable_distr p X << lborel ==> !x. 0 <= PDF p X x
 *)
Theorem PDF_LE_POS' =
        PDF_LE_POS |> REWRITE_RULE [GSYM measurable_distr_abs_continuous_alt]

Definition normal_rv :
    normal_rv X p mu sig =
      (random_variable X p borel /\
       measurable_distr p X = normal_pmeasure mu sig)
End

Theorem normal_rv_def :
    !p X mu sig. normal_rv (X :'a -> real) p mu sig <=>
                 random_variable X p borel /\
                 !s. s IN subsets borel ==>
                     distribution p X s = normal_pmeasure mu sig s
Proof
    rw [normal_rv, measurable_distr]
 >> EQ_TAC >> rw [FUN_EQ_THM]
 >- (Q.PAT_X_ASSUM ‘!s. P’ (MP_TAC o Q.SPEC ‘s’) >> rw [])
 >> Cases_on ‘s IN subsets borel’ >> rw []
 >> rw [normal_pmeasure]
 >> fs [sets_lborel]
QED

Theorem normal_pdf_nonneg :
    !X p mu sig. prob_space p /\ normal_rv X p mu sig ==>
                 !x. 0 <= PDF p (X:'a->real) x
Proof
    RW_TAC std_ss [normal_rv]
 >> MATCH_MP_TAC PDF_LE_POS
 >> FULL_SIMP_TAC std_ss [random_variable_def, prob_space_def]
 >> REWRITE_TAC [GSYM measurable_distr_abs_continuous_alt]
 >> METIS_TAC [normal_measure_abs_continuous, normal_measure_space]
QED

Theorem normal_pdf_integral_eq_1 :
    !X p mu sig. prob_space p /\ normal_rv X p mu sig ==>
                 integral lborel (PDF p X) = 1
Proof
    RW_TAC std_ss [normal_rv]
 >> MATCH_MP_TAC INTEGRAL_PDF_1 >> art []
 >> rw [GSYM measurable_distr_abs_continuous_alt, normal_measure_abs_continuous]
QED

Theorem normal_pdf_pos_fn_integral_eq_1 :
    !X p mu sig. prob_space p /\ normal_rv X p mu sig ==>
                 pos_fn_integral lborel (PDF p X) = 1
Proof
    rpt STRIP_TAC
 >> Suff ‘pos_fn_integral lborel (PDF p X) = integral lborel (PDF p X)’
 >- (Rewr' \\
     MATCH_MP_TAC normal_pdf_integral_eq_1 >> art [] \\
     qexistsl_tac [‘mu’, ‘sig’] >> art [])
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> MATCH_MP_TAC integral_pos_fn >> rw [lborel_def, space_lborel]
 >> irule normal_pdf_nonneg >> art []
 >> qexistsl_tac [‘mu’, ‘sig’] >> art []
QED

Theorem integral_normal_pdf_eq_density :
    !X p mu sig A. normal_rv X p mu sig /\ A IN measurable_sets lborel ==>
       (pos_fn_integral lborel (\x. PDF p X x * indicator_fn A x) =
        pos_fn_integral lborel
         (\x. Normal (normal_density mu sig x) * indicator_fn A x))
Proof
    RW_TAC std_ss [normal_rv, PDF_ALT, RN_deriv_def]
 >> SELECT_ELIM_TAC
 >> RW_TAC std_ss [measure_def, normal_pmeasure, density_measure_def]
 >> Q.EXISTS_TAC `(\x. Normal (normal_density mu sig x))`
 >> rw [normal_density_nonneg, IN_MEASURABLE_BOREL_normal_density]
QED

Theorem integral_normal_pdf_eq_density' :
    !X p mu sig f. prob_space p /\ normal_rv X p mu sig /\ (!x. 0 <= f x) /\
       f IN measurable (m_space lborel, measurable_sets lborel) Borel ==>
       (pos_fn_integral lborel (\x. f x * PDF p X x) =
        pos_fn_integral lborel
         (\x. f x * Normal (normal_density mu sig x)))
Proof
    RW_TAC std_ss [normal_rv, PDF_ALT]
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> qabbrev_tac ‘g = normal_pmeasure mu sig / lborel’
 >> Know ‘!x. 0 <= g x’
 >- (rw [Abbr ‘g’] \\
     Q.PAT_ASSUM ‘_ = normal_pmeasure mu sig’ (REWRITE_TAC o wrap o SYM) \\
     irule (REWRITE_RULE [PDF_ALT] PDF_LE_POS) >> art [] \\
     REWRITE_TAC [GSYM measurable_distr_abs_continuous_alt] \\
     simp [normal_measure_abs_continuous])
 >> DISCH_TAC
 >> Know ‘g IN Borel_measurable borel’
 >- (qunabbrev_tac ‘g’ \\
     Q.PAT_ASSUM ‘_ = normal_pmeasure mu sig’ (REWRITE_TAC o wrap o SYM) \\
     MATCH_MP_TAC (REWRITE_RULE [PDF_ALT] PDF_IN_MEASURABLE_BOREL') \\
     simp [normal_measure_abs_continuous])
 >> DISCH_TAC
 >> Know ‘pos_fn_integral lborel (\x. f x *
           (RN_deriv' lborel (space borel,subsets borel,normal_pmeasure mu sig)) x) =
          pos_fn_integral (density lborel
           (RN_deriv' lborel (space borel,subsets borel,normal_pmeasure mu sig))) f’
 >- (simp [] \\
     ONCE_REWRITE_TAC [mul_comm] \\
     Know ‘g^+ IN Borel_measurable borel’
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_FN_PLUS \\
         rw [sigma_algebra_borel]) >> DISCH_TAC \\
     ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
    ‘!x. 0 <= g^+ x’ by rw [FN_PLUS_POS] \\
     Know ‘density lborel g = density lborel g^+’
     >- (MATCH_MP_TAC density_eq >> simp [lborel_def]) >> Rewr' \\
     Know ‘pos_fn_integral lborel (\x. g x * f x) =
           pos_fn_integral lborel (\x. g^+ x * f x)’
     >- (MATCH_MP_TAC pos_fn_integral_cong \\
         simp [lborel_def, space_lborel] \\
         Q.X_GEN_TAC ‘x’ >> MATCH_MP_TAC le_mul >> simp []) >> Rewr' \\
     MATCH_MP_TAC pos_fn_integral_density \\
     simp [lborel_def] \\
     MATCH_MP_TAC AE_T >> simp [lborel_def])
 >> simp []
 >> DISCH_THEN K_TAC
 >> Know ‘pos_fn_integral (density lborel g) f =
          pos_fn_integral (density_of lborel g) f’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC pos_fn_integral_density_of >> rw [lborel_def])
 >> Rewr'
 >> Q.ABBREV_TAC `N = (space borel,subsets borel,normal_pmeasure mu sig)`
 >> ‘measure_space N’ by PROVE_TAC [normal_measure_space]
 >> Q_TAC SUFF_TAC
       `pos_fn_integral lborel (\x. f x * Normal (normal_density mu sig x)) =
        pos_fn_integral N f`
 >- (Rewr' THEN
     simp [Abbr ‘g’] \\
     MP_TAC (Q.SPECL [‘lborel’, ‘N’, ‘f’]
               (INST_TYPE [alpha |-> “:real”] RN_deriv_positive_integral)) \\
     simp [sigma_finite_lborel, sigma_finite_measure_space_def, lborel_def] \\
     simp [Abbr ‘N’, normal_measure_abs_continuous, sets_lborel])
 >> fs [Abbr ‘g’]
 (* stage work *)
 >> ONCE_REWRITE_TAC [METIS [] ``Normal (normal_density mu sig x) =
                            (\x. Normal (normal_density mu sig x)) x``]
 >> Q.ABBREV_TAC `g = (\x. Normal (normal_density mu sig x))`
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ] >> ONCE_REWRITE_TAC [mul_comm]
 >> `!x. 0 <= g x`
       by (Q.UNABBREV_TAC `g` \\
           SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] \\
           METIS_TAC [normal_density_nonneg])
 >> Know ‘N = density_of lborel g’
 >- (simp [Abbr ‘N’, density_of, m_space_lborel, sets_lborel] \\
     rw [normal_pmeasure, sets_lborel, FUN_EQ_THM] \\
     Cases_on ‘A IN subsets borel’ >> rw [] \\
     qabbrev_tac ‘h = \x. g x * indicator_fn A x’ >> simp [] \\
     ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC pos_fn_integral_max_0 \\
     rw [Abbr ‘h’, lborel_def] \\
     MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS] \\
     simp [extreal_of_num_def, Abbr ‘g’])
 >> Rewr'
 >> ‘g IN Borel_measurable (measurable_space lborel)’
      by rw [Abbr ‘g’, IN_MEASURABLE_BOREL_normal_density]
 >> Know ‘pos_fn_integral (density_of lborel g) f =
          pos_fn_integral (density lborel g) f’
 >- (MATCH_MP_TAC pos_fn_integral_density_of >> rw [lborel_def])
 >> Rewr'
 >> MATCH_MP_TAC pos_fn_integral_density_reduce
 >> rw [lborel_def]
QED

Theorem integral_normal_pdf_symmetry :
    !X p mu sig. prob_space p /\ normal_rv X p mu sig ==>
      (pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | x <= mu} x) =
       pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | mu <= x} x))
Proof
    RW_TAC std_ss []
 >> `{x | x <= mu} IN measurable_sets lborel /\
     {x | mu <= x} IN measurable_sets lborel`
       by simp [borel_measurable_sets, sets_lborel]
 >> `pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | x <= mu} x) =
     pos_fn_integral lborel
       (\x. Normal (normal_density mu sig x) * indicator_fn {x | x <= mu} x)`
       by METIS_TAC [integral_normal_pdf_eq_density]
 >> `pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | mu <= x} x) =
     pos_fn_integral lborel
       (\x. Normal (normal_density mu sig x) * indicator_fn {x | mu <= x} x)`
       by METIS_TAC [integral_normal_pdf_eq_density]
 >> NTAC 2 (POP_ORW)
 >> Q.ABBREV_TAC ‘f = \x. Normal (normal_density mu sig x) *
                          indicator_fn {x | x <= mu} x’
 >> Know ‘!x. 0 <= f x’
 >- (rw [Abbr ‘f’] \\
     MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, normal_density_nonneg])
 >> DISCH_TAC
 >> Know ‘f IN Borel_measurable borel’
 >- (qunabbrev_tac ‘f’ \\
     ASSUME_TAC sigma_algebra_borel \\
     HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR \\
     rw [borel_measurable_sets] \\
     rw [IN_MEASURABLE_BOREL_normal_density'])
 >> DISCH_TAC
 >> Know ‘pos_fn_integral lborel f =
          Normal (abs (-1)) * pos_fn_integral lborel (\x. f ((2 * mu) + (-1) * x))’
 >- (MATCH_MP_TAC lebesgue_pos_integral_real_affine' >> rw [])
 >> Rewr'
 >> simp [normal_1, Abbr ‘f’]
 >> SIMP_TAC std_ss [indicator_fn_def, GSYM real_sub]
 >> SIMP_TAC real_ss [GSPECIFICATION,
                      REAL_ARITH ``2 * mu - x <= mu <=> mu <= x:real``]
 >> AP_TERM_TAC >> ABS_TAC >> AP_THM_TAC >> AP_TERM_TAC
 >> SIMP_TAC std_ss [extreal_11, normal_density]
 >> ONCE_REWRITE_TAC [REAL_ARITH ``2 * mu = mu + mu:real``]
 >> Suff `(mu + mu - x - mu) pow 2 = (x - mu) pow 2` >- METIS_TAC []
 >> SIMP_TAC std_ss [POW_2] >> REAL_ARITH_TAC
QED

Theorem integral_normal_pdf_symmetry' :
    !X p mu sig a. prob_space p /\ normal_rv X p mu sig ==>
       pos_fn_integral lborel
         (\x. PDF p X x * indicator_fn {x | mu - a <= x /\ x <= mu} x) =
       pos_fn_integral lborel
         (\x. PDF p X x * indicator_fn {x | mu <= x /\ x <= mu + a} x)
Proof
    RW_TAC std_ss []
 >> ‘{x | mu - a <= x /\ x <= mu} IN measurable_sets lborel /\
     {x | mu <= x /\ x <= mu + a} IN measurable_sets lborel’
       by rw [sets_lborel, borel_measurable_sets]
 >> ‘pos_fn_integral lborel
       (\x. PDF p X x * indicator_fn {x | mu - a <= x /\ x <= mu} x) =
     pos_fn_integral lborel
       (\x. Normal (normal_density mu sig x) *
            indicator_fn {x | mu - a <= x /\ x <= mu} x)’
       by METIS_TAC [integral_normal_pdf_eq_density]
 >> ‘pos_fn_integral lborel
       (\x. PDF p X x * indicator_fn {x | mu <= x /\ x <= mu + a} x) =
     pos_fn_integral lborel
       (\x. Normal (normal_density mu sig x) *
            indicator_fn {x | mu <= x /\ x <= mu + a} x)’
       by METIS_TAC [integral_normal_pdf_eq_density]
 >> NTAC 2 POP_ORW
 >> Q.ABBREV_TAC ‘f = (\x. Normal (normal_density mu sig x) *
                           indicator_fn {x | mu - a <= x /\ x <= mu} x)’
 >> Know ‘!x. 0 <= f x’
 >- (rw [Abbr ‘f’] \\
     MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, normal_density_nonneg])
 >> DISCH_TAC
 >> Know ‘f IN Borel_measurable borel’
 >- (qunabbrev_tac ‘f’ \\
     ASSUME_TAC sigma_algebra_borel \\
     HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR \\
     rw [borel_measurable_sets] \\
     rw [IN_MEASURABLE_BOREL_normal_density'])
 >> DISCH_TAC
 >> Know ‘pos_fn_integral lborel f =
          Normal (abs (-1)) *
          pos_fn_integral lborel (\x. f ((2 * mu) + (-1) * x))’
 >- (MATCH_MP_TAC lebesgue_pos_integral_real_affine' >> rw [])
 >> Rewr'
 >> simp [normal_1, Abbr ‘f’]
 >> SIMP_TAC std_ss [indicator_fn_def, GSYM real_sub]
 >> SIMP_TAC real_ss [GSPECIFICATION,
                      REAL_ARITH ``2 * mu - x <= mu <=> mu <= x:real``,
                      REAL_ARITH ``mu - a <= 2 * mu - x <=> x <= mu + a:real``]
 >> GEN_REWR_TAC (LAND_CONV o ONCE_DEPTH_CONV) [CONJ_COMM]
 >> AP_TERM_TAC >> ABS_TAC >> AP_THM_TAC >> AP_TERM_TAC
 >> SIMP_TAC std_ss [extreal_11, normal_density]
 >> ONCE_REWRITE_TAC [REAL_ARITH ``2 * mu = mu + mu:real``]
 >> Suff `(mu + mu - x - mu) pow 2 = (x - mu) pow 2` >- METIS_TAC []
 >> SIMP_TAC std_ss [POW_2] >> REAL_ARITH_TAC
QED

Theorem integral_normal_pdf_half1 :
    !X p mu sig A. prob_space p /\ normal_rv X p mu sig /\ A = {x | x <= mu} ==>
         pos_fn_integral lborel (\x. PDF p X x * indicator_fn A x) = 1 / 2
Proof
    RW_TAC std_ss []
 >> ‘{x | x <= mu} IN measurable_sets lborel /\
     {x | mu <= x} IN measurable_sets lborel’
       by rw [sets_lborel, borel_measurable_sets]
 >> drule_all_then STRIP_ASSUME_TAC normal_pdf_pos_fn_integral_eq_1
 >> ‘UNIV IN measurable_sets lborel’ by rw [sets_lborel, space_in_borel]
 >> ‘pos_fn_integral lborel (\x. PDF p X x * indicator_fn UNIV x) =
     pos_fn_integral lborel
       (\x. Normal (normal_density mu sig x) * indicator_fn UNIV x)’
       by METIS_TAC [integral_normal_pdf_eq_density]
 >> Know ‘UNIV = {x | x <= mu} UNION {x | mu < x}’
 >- (SIMP_TAC real_ss [EXTENSION, IN_UNIV, IN_UNION, GSPECIFICATION] \\
     REAL_ARITH_TAC)
 >> DISCH_TAC
 >> Know ‘pos_fn_integral lborel
            (\x. PDF p X x * indicator_fn univ(:real) x) = 1’
 >- (SIMP_TAC std_ss [indicator_fn_def, IN_UNIV, mul_rone] \\
     METIS_TAC [ETA_AX])
 >> Q.ABBREV_TAC ‘f = (\x. Normal (normal_density mu sig x))’ >> fs []
 >> Q.PAT_X_ASSUM ‘_ = univ(:real)’ (REWRITE_TAC o wrap o SYM)
 >> ‘!x. 0 <= f x’ by rw [Abbr ‘f’, normal_density_nonneg]
 >> ‘f IN Borel_measurable borel’
       by rw [IN_MEASURABLE_BOREL_normal_density', Abbr ‘f’]
 >> Know ‘pos_fn_integral lborel
            (\x. f x * indicator_fn ({x | x <= mu} UNION {x | mu < x}) x) =
          pos_fn_integral lborel (\x. f x * indicator_fn ({x | x <= mu}) x) +
          pos_fn_integral lborel (\x. f x * indicator_fn ({x | mu < x}) x)’
 >- (MATCH_MP_TAC pos_fn_integral_disjoint_sets \\
     rw [lborel_def, sets_lborel, borel_measurable_sets] \\
     rw [DISJOINT_ALT, real_lt])
 >> Rewr'
 >> Suff ‘pos_fn_integral lborel (\x. f x * indicator_fn {x | mu < x} x) =
          pos_fn_integral lborel (\x. f x * indicator_fn {x | mu <= x} x)’
 >- (DISCH_THEN (fn th => GEN_REWR_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) \\
     SIMP_TAC std_ss [Abbr ‘f’] \\
     drule_all integral_normal_pdf_symmetry \\
    ‘pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | x <= mu} x) =
     pos_fn_integral lborel
        (\x. Normal (normal_density mu sig x) * indicator_fn {x | x <= mu} x)’
       by METIS_TAC [integral_normal_pdf_eq_density] >> POP_ORW \\
    ‘pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | mu <= x} x) =
     pos_fn_integral lborel
        (\x. Normal (normal_density mu sig x) * indicator_fn {x | mu <= x} x)’
       by METIS_TAC [integral_normal_pdf_eq_density] >> POP_ORW \\
     Rewr' \\
     SIMP_TAC std_ss [extreal_double] >> DISCH_TAC \\
     qmatch_abbrev_tac ‘z = 1 / (2 :extreal)’ \\
     SIMP_TAC real_ss [eq_rdiv, extreal_of_num_def] \\
     SIMP_TAC std_ss [GSYM extreal_of_num_def] \\
     simp [Once mul_comm])
 >> Know ‘{x | mu <= x} = {x | mu < x} UNION {mu}’
 >- (SIMP_TAC std_ss [EXTENSION, IN_UNION, GSPECIFICATION, IN_SING] \\
     REAL_ARITH_TAC)
 >> Rewr'
 >> Know ‘pos_fn_integral lborel
             (\x. f x * indicator_fn ({x | mu < x} UNION {mu}) x) =
          pos_fn_integral lborel (\x. f x * indicator_fn ({x | mu < x}) x) +
          pos_fn_integral lborel (\x. f x * indicator_fn ({mu}) x)’
 >- (MATCH_MP_TAC pos_fn_integral_disjoint_sets \\
     rw [lborel_def, sets_lborel, borel_measurable_sets])
 >> Rewr'
 >> Suff ‘pos_fn_integral lborel (\x. f x * indicator_fn {mu} x) = 0’
 >- rw []
 >> Know ‘(\x. f x * indicator_fn {mu} x) = (\x. f mu * indicator_fn {mu} x)’
 >- (ABS_TAC >> SIMP_TAC std_ss [indicator_fn_def, IN_SING] \\
     COND_CASES_TAC >> ASM_SIMP_TAC std_ss [mul_rone, mul_rzero])
 >> Rewr'
 >> SIMP_TAC std_ss [Abbr ‘f’]
 >> Know ‘pos_fn_integral lborel
            (\x. Normal (normal_density mu sig mu) * indicator_fn {mu} x) =
          Normal (normal_density mu sig mu) * measure lborel {mu}’
 >- (MATCH_MP_TAC pos_fn_integral_cmul_indicator \\
     SIMP_TAC std_ss [normal_density_nonneg, measure_space_lborel] \\
     rw [sets_lborel, borel_measurable_sets])
 >> Rewr'
 >> rw [lambda_sing]
QED

Theorem integral_normal_pdf_split :
    !X p mu sig. prob_space p /\ normal_rv X p mu sig ==>
       pos_fn_integral lborel (PDF p X) =
       pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | x <= mu} x) +
       pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | mu <= x} x)
Proof
    RW_TAC std_ss []
 >> drule_all_then STRIP_ASSUME_TAC normal_pdf_pos_fn_integral_eq_1
 >> POP_ORW
 >> qmatch_abbrev_tac ‘1 = a + (b :extreal)’
 >> Know ‘a = b’
 >- (qunabbrevl_tac [‘a’, ‘b’] \\
     MATCH_MP_TAC integral_normal_pdf_symmetry \\
     Q.EXISTS_TAC ‘sig’ >> art [])
 >> DISCH_TAC
 >> Know ‘a = 1 / 2’
 >- (qunabbrev_tac ‘a’ \\
     MATCH_MP_TAC integral_normal_pdf_half1 \\
     qexistsl_tac [‘mu’, ‘sig’] >> art [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘a = b’ (REWRITE_TAC o wrap o SYM)
 >> POP_ORW >> simp [half_double]
QED

Theorem integral_normal_pdf_half2 :
    !X p mu sig A. prob_space p /\ normal_rv X p mu sig /\ A = {x | mu <= x} ==>
         pos_fn_integral lborel (\x. PDF p X x * indicator_fn A x) = 1 / 2
Proof
    RW_TAC std_ss []
 >> drule_all_then STRIP_ASSUME_TAC normal_pdf_pos_fn_integral_eq_1
 >> drule_all integral_normal_pdf_split
 >> `pos_fn_integral lborel (\x. PDF p X x * indicator_fn {x | x <= mu} x) = 1 / 2`
      by METIS_TAC [integral_normal_pdf_half1]
 >> ASM_REWRITE_TAC []
 >> Suff `1 = 1 / 2 + 1 / (2 :extreal)`
 >- (DISCH_THEN (fn th => GEN_REWR_TAC (LAND_CONV o LAND_CONV) [th]) \\
    `1 / 2 <> PosInf`
       by SIMP_TAC real_ss [lt_infty, extreal_of_num_def, extreal_div_eq] \\
    `1 / 2 <> NegInf`
       by SIMP_TAC real_ss [lt_infty, extreal_of_num_def, extreal_div_eq] \\
     METIS_TAC [EXTREAL_EQ_LADD])
 >> simp [half_double]
QED

Theorem normal_rv_affine :
    !X p mu sig Y b.
       prob_space p /\ normal_rv X p mu sig /\ (!x. Y x = X x + b) ==>
       normal_rv Y p (mu + b) (sig)
Proof
    RW_TAC std_ss [normal_rv]
 >- (fs [random_variable_def, p_space_def, events_def, prob_space_def] \\
    ‘sigma_algebra (measurable_space p)’
       by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA] \\
     MATCH_MP_TAC in_borel_measurable_add \\
     qexistsl_tac [‘X’, ‘\x. b’] >> simp [] \\
     MATCH_MP_TAC in_borel_measurable_const \\
     Q.EXISTS_TAC ‘b’ >> simp [])
 >> FULL_SIMP_TAC std_ss [measurable_distr, distribution_def, normal_pmeasure]
 >> FULL_SIMP_TAC std_ss [FUN_EQ_THM]
 >> GEN_TAC
 >> ‘A IN subsets borel <=> A IN measurable_sets lborel’ by rw [sets_lborel]
 >> POP_ASSUM MP_TAC >> RW_TAC std_ss []
 >> Know ‘PREIMAGE Y A = PREIMAGE X {x | x + b IN A}’
 >- (SIMP_TAC std_ss [PREIMAGE_def] >> ASM_SET_TAC [])
 >> Rewr'
 >> Know ‘{x | x + b IN A} IN subsets borel’
 >- (FULL_SIMP_TAC std_ss [measurable_sets_def] \\
    ‘{x | x + b IN A} = PREIMAGE (\x. x + b) A’ by
       (SIMP_TAC std_ss [PREIMAGE_def] >> SET_TAC []) \\
     POP_ASSUM (fn th => REWRITE_TAC [th]) \\
     Suff ‘(\x. x + b) IN borel_measurable borel’
     >- rw [IN_MEASURABLE, space_borel] \\
     ASSUME_TAC sigma_algebra_borel \\
     MATCH_MP_TAC in_borel_measurable_add \\
     qexistsl_tac [‘\x. x’, ‘\x. b’] >> simp [in_borel_measurable_I] \\
     MATCH_MP_TAC in_borel_measurable_const \\
     Q.EXISTS_TAC ‘b’ >> rw [])
 >> DISCH_TAC
 >> qabbrev_tac ‘s = {x | x + b IN A}’
 >> qabbrev_tac ‘f = (\x. Normal (normal_density mu sig x) * indicator_fn s x)’
 >> Know ‘!x. 0 <= f x’
 >- (rw [Abbr ‘f’] \\
     MATCH_MP_TAC le_mul \\
     rw [INDICATOR_FN_POS, normal_density_nonneg])
 >> DISCH_TAC
 >> Suff ‘pos_fn_integral lborel
           (\x. (\x. Normal (normal_density (mu + b) sig x) * indicator_fn A x) x) =
          Normal (abs 1) * pos_fn_integral lborel (\x. f (-b + 1 * x))’
 >- (SIMP_TAC std_ss [] >> Rewr' \\
     Suff `pos_fn_integral lborel f =
           Normal (abs 1) * pos_fn_integral lborel (\x. f (-b + 1 * x))`
     >- (DISCH_THEN (simp o wrap o SYM) \\
         qunabbrev_tac ‘f’ \\
         Q.PAT_X_ASSUM ‘!A. (if A IN subsets borel then _ else 0) = _’
           (MP_TAC o Q.SPEC ‘s’) \\
         simp [sets_lborel]) \\
     MATCH_MP_TAC lebesgue_pos_integral_real_affine' >> rw [] \\
     Q.UNABBREV_TAC `f` \\
     HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR \\
     rw [sigma_algebra_borel, IN_MEASURABLE_BOREL_normal_density'])
 >> SIMP_TAC real_ss []
 >> simp [Abbr ‘f’, normal_1]
 >> Know ‘!x. indicator_fn s (-b + x) = indicator_fn A x’
 >- rw [Abbr ‘s’, indicator_fn_def, REAL_ARITH “-b + x + b = x:real”]
 >> Rewr'
 >> Know ‘!x. Normal_density (mu + b) sig x =
              Normal_density mu sig (-b + x)’
 >- (rw [normal_density] >> DISJ2_TAC \\
     rw [REAL_ARITH “x - (mu + b) = -b + x - mu:real”])
 >> Rewr
QED

Theorem normal_rv_affine' :
    !X p mu sig Y a b.
       prob_space p /\ a <> 0 /\ 0 < sig /\
       normal_rv X p mu sig /\ (!x. Y x = b + a * X x) ==>
       normal_rv Y p (b + a * mu) (abs a * sig)
Proof
    RW_TAC std_ss [normal_rv]
 >- (fs [random_variable_def, p_space_def, events_def, prob_space_def] \\
    ‘sigma_algebra (measurable_space p)’
       by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA] \\
     MATCH_MP_TAC in_borel_measurable_add \\
     qexistsl_tac [‘\x. b’, ‘\x. a * X x’] >> simp [] \\
     CONJ_TAC >- (MATCH_MP_TAC in_borel_measurable_const \\
                  Q.EXISTS_TAC ‘b’ >> simp []) \\
     MATCH_MP_TAC in_borel_measurable_cmul \\
     qexistsl_tac [‘X’, ‘a’] >> simp [])
 >> FULL_SIMP_TAC std_ss [measurable_distr, distribution_def, PREIMAGE_def]
 >> FULL_SIMP_TAC std_ss [FUN_EQ_THM]
 >> GEN_TAC
 >> ‘{x | b + a * X x IN s} = {x | X x IN {x | b + a * x IN s}}’
      by SET_TAC []
 >> POP_ORW
 >> FIRST_X_ASSUM (MP_TAC o Q.SPEC ‘{x | b + a * x IN s:real->bool}’)
 >> SIMP_TAC std_ss [normal_pmeasure, sets_lborel]
 >> Cases_on ‘s IN subsets borel’ >> simp []
 >> qabbrev_tac ‘A = {x | b + a * x IN s}’
 >> Know ‘A IN subsets borel’
 >- (rw [Abbr ‘A’, IN_MEASURABLE] \\
     ONCE_REWRITE_TAC [SET_RULE ``{x | b + a * x IN s} =
      {x | (\x. b + a * x) x IN s:real->bool} INTER UNIV``] \\
     REWRITE_TAC [GSYM PREIMAGE_def, GSYM space_borel] \\
     Suff ‘(\x. b + a * x) IN borel_measurable borel’
     >- rw [IN_MEASURABLE, space_borel] \\
     ASSUME_TAC sigma_algebra_borel \\
     MATCH_MP_TAC in_borel_measurable_add \\
     qexistsl_tac [‘\x. b’, ‘\x. a * x’] >> simp [] \\
     CONJ_TAC >- (MATCH_MP_TAC in_borel_measurable_const \\
                  Q.EXISTS_TAC ‘b’ >> rw []) \\
     MATCH_MP_TAC in_borel_measurable_cmul \\
     qexistsl_tac [‘\x. x’, ‘a’] >> simp [in_borel_measurable_I])
 >> DISCH_TAC
 >> ASM_SIMP_TAC std_ss []
 >> DISCH_THEN K_TAC
 >> Suff ‘!x. Normal (normal_density mu sig x) * indicator_fn A x =
              Normal (abs a) *
              Normal (normal_density (b + a * mu) (abs a * sig) (b + a * x)) *
              indicator_fn s (b + a * x)’
 >- (Rewr' \\
     Know ‘pos_fn_integral lborel
             (\x. Normal (abs a) *
                 (\x. Normal (normal_density (b + a * mu) (abs a * sig) (b + a * x)) *
                      indicator_fn s (b + a * x)) x) =
           Normal (abs a) *
           pos_fn_integral lborel
             (\x. Normal (normal_density (b + a * mu) (abs a * sig) (b + a * x)) *
                  indicator_fn s (b + a * x))’
     >- (MATCH_MP_TAC pos_fn_integral_cmul \\
         rw [measure_space_lborel, space_lborel] \\
         MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS] \\
         SIMP_TAC std_ss [normal_density_nonneg]) \\
     SIMP_TAC std_ss [mul_assoc] \\
     DISCH_THEN K_TAC \\
     ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
     qmatch_abbrev_tac ‘pos_fn_integral lborel f = _’ >> simp [] \\
     Know ‘!x. 0 <= f x’
     >- (rw [Abbr ‘f’] \\
         MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS] \\
         rw [normal_density_nonneg]) >> DISCH_TAC \\
     MATCH_MP_TAC lebesgue_pos_integral_real_affine' >> art [] \\
     qunabbrev_tac ‘f’ \\
     ASSUME_TAC sigma_algebra_borel \\
     HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR >> art [] \\
     rw [IN_MEASURABLE_BOREL_normal_density'])
 (* stage work *)
 >> rw [FUN_EQ_THM, indicator_fn_def, GSPECIFICATION, Abbr ‘A’]
 >> SIMP_TAC std_ss [normal_density]
 >> ONCE_REWRITE_TAC [REAL_ARITH ``a * (b * c) = (a:real * b:real) * c:real``]
 >> Know ‘1 / sqrt (2 * pi * sig pow 2) =
          abs a * (1 / sqrt (2 * pi * (abs a * sig) pow 2))’
 >- (SIMP_TAC real_ss [real_div, REAL_MUL_ASSOC, POW_2] \\
     ONCE_REWRITE_TAC [REAL_ARITH ``2 * pi * abs a * sig * abs a * sig =
       (2:real * pi:real * sig * sig:real) * (abs a * abs a:real)``] \\
     Know `0 < 2 * pi * sig * sig`
     >- (ASSUME_TAC PI_POS \\
         MATCH_MP_TAC REAL_LT_MUL >> ASM_SIMP_TAC real_ss [] \\
         MATCH_MP_TAC REAL_LT_MUL >> ASM_SIMP_TAC real_ss [] \\
         MATCH_MP_TAC REAL_LT_MUL >> ASM_SIMP_TAC real_ss []) >> DISCH_TAC \\
     Know `0 < abs a * abs a`
     >- (MATCH_MP_TAC REAL_LT_MUL >> ASM_SIMP_TAC std_ss [GSYM ABS_NZ]) \\
     DISCH_TAC \\
    `0 <= 2 * pi * sig * sig` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE] \\
    `0 <= abs a * abs a` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE] \\
     ASM_SIMP_TAC std_ss [SQRT_MUL] \\
    `0 < sqrt (2:real * pi * sig * sig)` by METIS_TAC [SQRT_POS_LT] \\
    `0 < sqrt (abs a * abs a)` by METIS_TAC [SQRT_POS_LT] \\
    `sqrt (2:real * pi * sig * sig) <> 0` by METIS_TAC [REAL_LT_IMP_NE] \\
    `sqrt (abs a * abs a) <> 0` by METIS_TAC [REAL_LT_IMP_NE] \\
     ASM_SIMP_TAC std_ss [REAL_INV_MUL, GSYM POW_2] \\
     SIMP_TAC std_ss [POW_2_SQRT, ABS_POS] \\
     ONCE_REWRITE_TAC [REAL_ARITH ``a * (b * c) = b:real * (a:real * c:real)``] \\
    `0 < abs a` by FULL_SIMP_TAC std_ss [ABS_NZ] \\
    `abs a <> 0` by METIS_TAC [REAL_LT_IMP_NE] \\
     FULL_SIMP_TAC std_ss [REAL_MUL_RINV, REAL_MUL_RID])
 >> Rewr'
 >> simp [extreal_mul_eq]
 >> DISJ2_TAC
 >> ONCE_REWRITE_TAC [REAL_ARITH ``b + a * x - (b + a * mu) =
                                   a:real * (x:real - mu:real)``]
 >> SIMP_TAC real_ss [POW_MUL, real_div, REAL_MUL_ASSOC]
 >> ONCE_REWRITE_TAC [REAL_MUL_COMM]
 >> SIMP_TAC std_ss [REAL_MUL_ASSOC]
 >> AP_TERM_TAC >> AP_TERM_TAC
 >> ONCE_REWRITE_TAC [REAL_ARITH ``a * b * c = (a:real * b:real) * c:real``]
 >> AP_THM_TAC >> AP_TERM_TAC
 >> simp [REAL_POW2_ABS]
QED

(* NOTE: This is just normal_rv_affine' expanded with normal_rv_def *)
Theorem normal_distribution_affine :
    !X p mu sig Y a b.
       prob_space p /\ a <> 0 /\ 0 < sig /\
       random_variable X p borel /\
      (!s. s IN subsets borel ==>
           distribution p X s = normal_pmeasure mu sig s) /\
      (!x. Y x = b + a * X x) ==>
       random_variable Y p borel /\
       !s. s IN subsets borel ==>
           distribution p Y s = normal_pmeasure (b + a * mu) (abs a * sig) s
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘normal_rv X p mu sig’ by rw [normal_rv_def]
 >> Suff ‘normal_rv Y p (b + a * mu) (abs a * sig)’ >- rw [normal_rv_def]
 >> MATCH_MP_TAC normal_rv_affine'
 >> Q.EXISTS_TAC ‘X’ >> rw []
QED

(* ------------------------------------------------------------------------- *)
(*  Convolutions (see also [4, p.291] or [5, p.157])                         *)
(* ------------------------------------------------------------------------- *)

Definition convolution :
    convolution (M :real m_space) (N :real m_space) =
    distr_of (prod_measure_space M N)
             (space borel, subsets borel, (\x. 0)) (\(x,y). x + y)
End

(* |- !M N.
        convolution M N =
        (space borel,subsets borel,
         (\s.
              if s IN subsets borel then distr (M CROSS N) (\(x,y). x + y) s
              else 0))
 *)
Theorem convolution_def = convolution
     |> REWRITE_RULE [distr_of_alt_distr, m_space_def, measurable_sets_def]

(* Easy corollary of distribution_prob_space *)
Theorem prob_space_distr_of :
    !p M X. prob_space p /\ measure_space M /\
            random_variable X p (measurable_space M) ==> prob_space (distr_of p M X)
Proof
    rw [distr_of_alt_distr, GSYM distribution_distr]
 >> qmatch_abbrev_tac ‘prob_space (m_space M,measurable_sets M,m)’
 >> MATCH_MP_TAC prob_space_eq
 >> Q.EXISTS_TAC ‘(m_space M,measurable_sets M,distribution p X)’
 >> simp [p_space_def, events_def, prob_def, Abbr ‘m’]
 >> qabbrev_tac ‘A = measurable_space M’
 >> ‘m_space M = space A /\ measurable_sets M = subsets A’ by rw [Abbr ‘A’]
 >> NTAC 2 POP_ORW
 >> MATCH_MP_TAC distribution_prob_space >> art []
 >> fs [measure_space_def]
QED

Theorem prob_sigma_finite_measure_space :
    !p. prob_space p ==> sigma_finite_measure_space p
Proof
    rw [sigma_finite_measure_space_def, PROB_SPACE_SIGMA_FINITE]
 >> fs [prob_space_def]
QED

(* NOTE: This theorem gives an alternative definition of “prod_measure” targeting
   at product sets (the generator case). This proof was part of pair_measure_eqI.
 *)
(* NOTE: New proof by UNIQUENESS_OF_MEASURE *)
Theorem measure_of_prod_measure_space : (* was: pair_measure_eqI *)
    !M M1 M2. measure_space M /\
              sigma_finite_measure_space M1 /\
              sigma_finite_measure_space M2 /\
             (measurable_sets (M1 CROSS M2) = measurable_sets M) /\
             (!A B. A IN measurable_sets M1 /\ B IN measurable_sets M2 ==>
                    measure M1 A * measure M2 B = measure M (A CROSS B)) ==>
              measure_of (M1 CROSS M2) = measure_of M
Proof
    rpt STRIP_TAC
 >> ‘measure_space (M1 CROSS M2)’ by PROVE_TAC [measure_space_prod_measure]
 >> ‘m_space (M1 CROSS M2) = m_space M’ by METIS_TAC [sets_eq_imp_space_eq]
 >> rw [measure_of_def, FUN_EQ_THM]
 >> ‘sigma_sets (m_space M) (measurable_sets M) = measurable_sets M’
      by METIS_TAC [sigma_sets_eq, measure_space_def]
 >> POP_ORW
 >> Suff ‘!s. s IN measurable_sets M ==> measure (M1 CROSS M2) s = measure M s’
 >- (DISCH_TAC \\
     Cases_on ‘a IN measurable_sets M’ >> rw [] \\
     POP_ASSUM MP_TAC \\
     Suff ‘measure_space (m_space M,measurable_sets M,measure (M1 CROSS M2))’
     >- rw [] \\
     MATCH_MP_TAC measure_space_eq \\
     Q.EXISTS_TAC ‘M’ >> rw [m_space_def, measurable_sets_def, measure_def])
 (* applying UNIQUENESS_OF_MEASURE *)
 >> qabbrev_tac ‘u = measure (M1 CROSS M2)’
 >> qabbrev_tac ‘v = measure M’
 >> qabbrev_tac ‘sp = m_space M’
 >> qabbrev_tac ‘a = measurable_space M1’
 >> qabbrev_tac ‘b = measurable_space M2’
 >> fs [sigma_finite_measure_space_def]
 >> ‘sigma_algebra a /\ sigma_algebra b’ by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
 >> qabbrev_tac ‘sts = prod_sets (subsets a) (subsets b)’
 >> Know ‘measurable_sets M = subsets (sigma sp sts)’
 >- (Q.PAT_X_ASSUM ‘_ = measurable_sets M’ (REWRITE_TAC o wrap o SYM) \\
     simp [prod_measure_space_def] \\
     simp [prod_sigma_def] \\
     Suff ‘space a CROSS space b = sp’ >- rw [] \\
     simp [Abbr ‘sp’] \\
     Q.PAT_X_ASSUM ‘_ = m_space M’ (REWRITE_TAC o wrap o SYM) \\
     simp [prod_measure_space_def, Abbr ‘a’, Abbr ‘b’])
 >> Rewr'
 (* applying UNIQUENESS_OF_MEASURE *)
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> MATCH_MP_TAC UNIQUENESS_OF_MEASURE
 >> CONJ_TAC (* subset_class sp sts *)
 >- (rw [Abbr ‘sp’, Abbr ‘sts’, subset_class_def, IN_PROD_SETS] \\
     Q.PAT_X_ASSUM ‘_ = m_space M’ (REWRITE_TAC o wrap o SYM) \\
     simp [SPACE_PROD] \\
     MATCH_MP_TAC SUBSET_CROSS \\
    ‘m_space M1 = space a /\ m_space M2 = space b’ by rw [Abbr ‘a’, Abbr ‘b’] \\
     NTAC 2 POP_ORW \\
     fs [sigma_algebra_def, algebra_def, subset_class_def])
 >> CONJ_TAC (* !s t. s IN sts /\ t IN sts ==> s INTER t IN sts *)
 >- (rw [Abbr ‘sts’, IN_PROD_SETS] \\
     simp [INTER_CROSS] \\
     qexistsl_tac [‘t' INTER t''’, ‘u' INTER u''’] >> art [] \\
     CONJ_TAC \\ (* 2 subgoals, same tactics *)
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [])
 >> STRONG_CONJ_TAC (* sigma_finite (sp,sts,u) *)
 >- (NTAC 2 (Q.PAT_X_ASSUM ‘sigma_finite _’ MP_TAC) \\
     rw [sigma_finite, Abbr ‘sts’, IN_PROD_SETS, GSYM lt_infty] \\
     simp [SPACE_PROD] \\
     Q.EXISTS_TAC ‘\n. f n CROSS f' n’ \\
     CONJ_TAC
     >- (MATCH_MP_TAC exhausting_sequence_CROSS \\
        ‘m_space M1 = space a /\ m_space M2 = space b’ by rw [Abbr ‘a’, Abbr ‘b’] \\
         NTAC 2 POP_ORW \\
         simp [SPACE]) \\
     rw [] \\
     fs [exhausting_sequence_def, IN_FUNSET, Abbr ‘a’, Abbr ‘b’] \\
     Know ‘v (f n CROSS f' n) = measure M1 (f n) * measure M2 (f' n)’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> Rewr' \\
    ‘0 <= measure M1 (f n) /\ 0 <= measure M2 (f' n)’
       by PROVE_TAC [MEASURE_POSITIVE] \\
    ‘measure M1 (f n) <> NegInf /\ measure M2 (f' n) <> NegInf’
       by rw [pos_not_neginf] \\
    ‘?r1. measure M1 (f n) = Normal r1’ by METIS_TAC [extreal_cases] \\
    ‘?r2. measure M2 (f' n) = Normal r2’ by METIS_TAC [extreal_cases] \\
     NTAC 2 POP_ORW \\
     simp [extreal_mul_eq])
 >> DISCH_TAC
 >> CONJ_TAC (* measure_space (sp,subsets (sigma sp sts),v) *)
 >- (MATCH_MP_TAC measure_space_eq \\
     Q.EXISTS_TAC ‘M’ \\
     simp [m_space_def, measurable_sets_def, measure_def] \\
     Q.PAT_X_ASSUM ‘_ = measurable_sets M’ (REWRITE_TAC o wrap o SYM) \\
     simp [prod_measure_space_def, prod_sigma_def, Abbr ‘sp’] \\
     Q.PAT_X_ASSUM ‘_ = m_space M’ (REWRITE_TAC o wrap o SYM) \\
     simp [prod_measure_space_def, prod_sigma_def, m_space_def] \\
     NTAC 2 AP_TERM_TAC \\
     simp [Abbr ‘a’, Abbr ‘b’, Abbr ‘sts’])
 >> CONJ_TAC (* measure_space (sp,subsets (sigma sp sts),u) *)
 >- (MATCH_MP_TAC measure_space_eq \\
     Q.EXISTS_TAC ‘M1 CROSS M2’ \\
     simp [m_space_def, measurable_sets_def, measure_def] \\
     Q.PAT_X_ASSUM ‘_ = measurable_sets M’ (REWRITE_TAC o wrap o SYM) \\
     simp [prod_measure_space_def, prod_sigma_def, Abbr ‘sp’] \\
     Q.PAT_X_ASSUM ‘_ = m_space M’ (REWRITE_TAC o wrap o SYM) \\
     simp [prod_measure_space_def, prod_sigma_def, m_space_def] \\
     NTAC 2 AP_TERM_TAC \\
     simp [Abbr ‘a’, Abbr ‘b’, Abbr ‘sts’])
 (* stage work *)
 >> rw [Abbr ‘sts’, IN_PROD_SETS]
 >> rename1 ‘v (A CROSS B) = u (A CROSS B)’
 >> Know ‘v (A CROSS B) = measure M1 A * measure M2 B’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     fs [Abbr ‘a’, Abbr ‘b’])
 >> Rewr'
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> simp [Abbr ‘u’, prod_measure_space_def]
 >> MATCH_MP_TAC PROD_MEASURE_CROSS
 >> fs [Abbr ‘a’, Abbr ‘b’]
QED

(* NOTE: M1/M2 is usually (space Borel,subsets Borel,\x. 0) or the borel variants,
   i.e. the measure functions in M1/M2 are never used, only the measurable spaces
   (sigma_algebras) matter.
 *)
Theorem indep_var_distribution_imp :
    !p M1 X M2 Y. prob_space p /\
       sigma_finite_measure_space M1 /\
       sigma_finite_measure_space M2 /\
       random_variable X p (measurable_space M1) /\
       random_variable Y p (measurable_space M2) /\
       indep_rv p X Y (measurable_space M1) (measurable_space M2) ==>
       measure_of (distr_of p M1 X CROSS distr_of p M2 Y) =
       measure_of (distr_of p (M1 CROSS M2) (\x. (X x,Y x)))
Proof
    rpt STRIP_TAC
 >> ‘measure_space (M1 CROSS M2)’ by PROVE_TAC [measure_space_prod_measure]
 >> fs [sigma_finite_measure_space_def]
 >> Know ‘random_variable (\x. (X x, Y x)) p
           (m_space (M1 CROSS M2),measurable_sets (M1 CROSS M2))’
 >- (ASM_SIMP_TAC std_ss [random_variable_def, MEASURABLE_SPACE_PROD] \\
     SIMP_TAC std_ss [p_space_def, events_def] \\
     MATCH_MP_TAC MEASURABLE_PAIR \\
     FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, events_def,
                           random_variable_def, measure_space_def])
 >> DISCH_TAC
 >> qabbrev_tac ‘Z = \x. (X x,Y x)’
 >> qabbrev_tac ‘A1 = measurable_space M1’
 >> qabbrev_tac ‘A2 = measurable_space M2’
 >> ‘prob_space (distr_of p M1 X) /\
     prob_space (distr_of p M2 Y)’ by PROVE_TAC [prob_space_distr_of]
 (* eliminating measure_of *)
 >> MATCH_MP_TAC measure_of_prod_measure_space
 >> STRONG_CONJ_TAC
 >- (MATCH_MP_TAC measure_space_distr_of \\
     fs [prob_space_def, random_variable_def, p_space_def, events_def])
 >> DISCH_TAC
 >> CONJ_TAC
 >- (fs [prob_space_def, sigma_finite_measure_space_def] \\
     MATCH_MP_TAC FINITE_IMP_SIGMA_FINITE >> rw [lt_infty])
 >> CONJ_TAC
 >- (fs [prob_space_def, sigma_finite_measure_space_def] \\
     MATCH_MP_TAC FINITE_IMP_SIGMA_FINITE >> rw [lt_infty])
 >> simp [distr_of, prod_measure_space_def]
 >> reverse (rw [PREIMAGE_CROSS])
 >- (Q.PAT_X_ASSUM ‘A CROSS B NOTIN subsets (A1 CROSS A2)’ MP_TAC \\
     Suff ‘A CROSS B IN subsets (A1 CROSS A2)’ >- rw [] \\
     simp [prod_sigma_def] \\
     MATCH_MP_TAC IN_SIGMA >> rw [IN_PROD_SETS] \\
     qexistsl_tac [‘A’, ‘B’] >> fs [Abbr ‘A1’, Abbr ‘A2’])
 >> simp [Abbr ‘Z’, o_DEF, ETA_AX]
 (* finally, we need “indep_vars” (indep_rv) *)
 >> simp [GSYM prob_def, GSYM p_space_def]
 >> Q.PAT_X_ASSUM ‘indep_vars p X Y A1 A2’ MP_TAC
 >> simp [indep_rv_def, Abbr ‘A1’, Abbr ‘A2’, indep_def]
 >> DISCH_THEN (MP_TAC o Q.SPECL [‘A’, ‘B’])
 >> fs [random_variable_def]
 >> STRIP_TAC
 >> POP_ASSUM (REWRITE_TAC o wrap o SYM)
 >> AP_TERM_TAC >> SET_TAC []
QED

Theorem MEASURE_SPACE_SUBSET_POW :
    !N. measure_space N ==> measurable_sets N SUBSET POW (m_space N)
Proof
    NTAC 2 STRIP_TAC
 >> simp [Once SUBSET_DEF, IN_POW]
 >> qabbrev_tac ‘a = measurable_space N’
 >> ‘sigma_algebra a’ by rw [Abbr ‘a’, MEASURE_SPACE_SIGMA_ALGEBRA]
 >> ‘m_space N = space a /\ measurable_sets N = subsets a’ by rw [Abbr ‘a’]
 >> NTAC 2 POP_ORW
 >> simp [GSYM subset_class_def]
 >> POP_ASSUM MP_TAC
 >> simp [sigma_algebra_def, algebra_def]
QED

Theorem MEASURE_SPACE_SIGMA_SETS_REDUCE :
    !M. measure_space M ==>
        sigma_sets (m_space M) (measurable_sets M) = measurable_sets M
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC sigma_sets_eq
 >> MATCH_MP_TAC MEASURE_SPACE_SIGMA_ALGEBRA >> art []
QED

(* NOTE: The theorem statements (and the proof) are cleaned *)
Theorem sum_indep_random_variable :
    !p X Y. prob_space p /\
            random_variable X p borel /\
            random_variable Y p borel /\
            indep_rv p X Y borel borel ==>
        !s. s IN subsets borel ==>
            distribution p (\x. X x + Y x) s =
            measure (convolution
                      (distr_of p (space borel, subsets borel, (\x. 0)) X)
                      (distr_of p (space borel, subsets borel, (\x. 0)) Y)) s
Proof
    RW_TAC std_ss [convolution]
 >> qabbrev_tac ‘M = (space borel,subsets borel,(\x :real set. (0 :extreal)))’
 >> ‘measure_space M’
      by rw [Abbr ‘M’, measure_space_trivial', sigma_algebra_borel]
 >> Know ‘sigma_finite M’
 >- (qunabbrev_tac ‘M’ \\
     MATCH_MP_TAC FINITE_IMP_SIGMA_FINITE >> rw [])
 >> DISCH_TAC
 >> qabbrev_tac ‘N1 = distr_of p M X’
 >> qabbrev_tac ‘N2 = distr_of p M Y’
 >> ASSUME_TAC measure_space_lborel
 >> ‘random_variable X p (m_space M,measurable_sets M) /\
     random_variable Y p (m_space M,measurable_sets M) /\
     indep_vars p X Y (measurable_space M) (measurable_space M)’ by rw [Abbr ‘M’]
 >> Know ‘prob_space N1 /\ prob_space N2’
 >- (rw [Abbr ‘N1’, Abbr ‘N2’] \\
     MATCH_MP_TAC prob_space_distr_of >> art [])
 >> STRIP_TAC
 >> ‘m_space M = space borel’ by rw [Abbr ‘M’]
 >> ‘measurable_sets M = subsets borel’ by rw [Abbr ‘M’]
 >> simp [distr_of]
 (* applying indep_var_distribution_imp *)
 >> Know ‘measure_of (distr_of p M X CROSS distr_of p M Y) =
          measure_of (distr_of p (M CROSS M) (\x. (X x,Y x)))’
 >- (MATCH_MP_TAC indep_var_distribution_imp \\
     rw [sigma_finite_measure_space_def])
 >> simp [] (* rewrite “distr_of p M X”, etc. by abbreviations *)
 >> DISCH_TAC
 (* stage work *)
 >> qmatch_abbrev_tac (* this defines f *)
       ‘distribution p (\x. X x + Y x) s =
        measure (N1 CROSS N2) (PREIMAGE f s INTER m_space (N1 CROSS N2))’
 >> Know ‘measure_space (N1 CROSS N2)’
 >- (MATCH_MP_TAC measure_space_prod_measure \\
     simp [sigma_finite_measure_space_def] \\
     METIS_TAC [prob_space_def, PROB_SPACE_SIGMA_FINITE])
 >> DISCH_TAC
 >> qabbrev_tac ‘N = N1 CROSS N2’
 >> Suff ‘distribution p (\x. X x + Y x) s = measure (distr_of N M f) s’
 >- (Rewr' \\
     simp [Abbr ‘N’, prod_measure_space_def, distr_of])
 (* stage work *)
 >> Know ‘measure_space (M CROSS M)’
 >- (MATCH_MP_TAC measure_space_prod_measure \\
     simp [sigma_finite_measure_space_def])
 >> DISCH_TAC
 >> Know ‘sigma_algebra (measurable_space p)’
 >- (MATCH_MP_TAC MEASURE_SPACE_SIGMA_ALGEBRA \\
     FULL_SIMP_TAC std_ss [prob_space_def])
 >> DISCH_TAC
 >> Know ‘measure_space (distr_of p M (\x. X x + Y x))’
 >- (MATCH_MP_TAC measure_space_distr_of >> simp [SPACE] \\
     FULL_SIMP_TAC std_ss [prob_space_def] \\
     MATCH_MP_TAC in_borel_measurable_add \\
     qexistsl_tac [‘X’, ‘Y’] >> simp [] \\
     fs [random_variable_def, p_space_def, events_def])
 >> DISCH_TAC
 >> Know ‘measure_space (distr_of p (M CROSS M) (\x. (X x,Y x)))’
 >- (MATCH_MP_TAC measure_space_distr_of \\
     FULL_SIMP_TAC std_ss [prob_space_def] \\
     simp [prod_measure_space_def, GSYM SPACE_PROD_SIGMA, SPACE] \\
     MATCH_MP_TAC MEASURABLE_PAIR \\
     simp [sigma_algebra_borel] \\
     fs [random_variable_def, p_space_def, events_def])
 >> DISCH_TAC
 >> simp [distr_of, distribution_def, prob_def, p_space_def]
 >> ‘(\x. X x + Y x) = f o (\x. (X x,Y x))’ by rw [FUN_EQ_THM, o_DEF, Abbr ‘f’]
 >> POP_ORW
 >> qmatch_abbrev_tac ‘measure p (PREIMAGE (f o g) s INTER m_space p) = _’
 >> Q.PAT_X_ASSUM ‘measure_of N = _’ MP_TAC
 >> simp [measure_of_def, distr_of]
 >> simp [MEASURE_SPACE_SUBSET_POW, MEASURE_SPACE_SIGMA_SETS_REDUCE]
 >> Q.PAT_X_ASSUM ‘measure_space (distr_of p (M CROSS M) g)’ MP_TAC
 >> simp [distr_of]
 >> DISCH_THEN K_TAC
 >> STRIP_TAC
 >> POP_ASSUM (MP_TAC o (SIMP_RULE std_ss [FUN_EQ_THM]))
 >> DISCH_TAC
 >> ‘m_space (M CROSS M) = UNIV’
      by rw [Abbr ‘M’, prod_measure_space_def, space_borel, CROSS_UNIV]
 >> POP_ASSUM (fs o wrap) >> T_TAC
 >> Know ‘f IN measurable (measurable_space N) borel’
 >- (rw [IN_MEASURABLE, Abbr ‘N’, prod_measure_space_def]
     >- rw [IN_FUNSET, space_borel] \\
     Know ‘f IN borel_measurable (borel CROSS borel)’
     >- rw [Abbr ‘f’, borel_2d_measurable_add] \\
     rw [IN_MEASURABLE, IN_FUNSET, space_borel_2d])
 >> DISCH_TAC
 >> Know ‘PREIMAGE f s IN measurable_sets N’
 >- (POP_ASSUM (MP_TAC o REWRITE_RULE [IN_MEASURABLE]) \\
     simp [IN_FUNSET, Abbr ‘N’, prod_measure_space_def])
 >> DISCH_TAC
 >> simp [PREIMAGE_o]
 >> qabbrev_tac ‘h = s o f’
 >> Know ‘PREIMAGE f s = h’
 >- (rw [Abbr ‘h’, PREIMAGE_def, o_DEF] \\
     rw [IN_APP, FUN_EQ_THM])
 >> DISCH_THEN (fs o wrap)
 >> Q.PAT_X_ASSUM ‘_ = measurable_sets (M CROSS M)’ (fs o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘!a. P’ (MP_TAC o Q.SPEC ‘h’)
 >> simp []
QED

(* NOTE: This proof was extracted from the proof of convolution_density *)
Theorem measure_space_convolution :
    !M N. sigma_finite_measure_space M /\ sigma_finite_measure_space N /\
          measurable_space M = borel /\ measurable_space N = borel ==>
          measure_space (convolution M N)
Proof
    rw [convolution]
 >> MATCH_MP_TAC measure_space_distr_of
 >> rw [measure_space_prod_measure, measure_space_trivial', sigma_algebra_borel]
 >> simp [prod_measure_space_def]
 >> Know ‘m_space M = space borel’
 >- (Q.PAT_X_ASSUM ‘measurable_space M = borel’
       (REWRITE_TAC o wrap o SYM) >> rw [])
 >> Rewr'
 >> Know ‘m_space N = space borel’
 >- (Q.PAT_X_ASSUM ‘measurable_space N = borel’
       (REWRITE_TAC o wrap o SYM) >> rw [])
 >> Rewr'
 >> simp [GSYM SPACE_PROD_SIGMA, SPACE, borel_2d_measurable_add]
QED

(* NOTE: The original proof of this theorem (by HVG people) has ~1K lines. The
   present proof is a reworked version of the original proof (same idea), by
   repeatedly applying TONELLI.
 *)
Theorem convolution_density :
    !f g. f IN measurable (m_space lborel, measurable_sets lborel) Borel /\
          g IN measurable (m_space lborel, measurable_sets lborel) Borel /\
          finite_measure_space (density_of lborel f) /\
          finite_measure_space (density_of lborel g) /\
         (!x. x IN m_space lborel ==> 0 <= f x) /\
         (!x. x IN m_space lborel ==> 0 <= g x) ==>
          measure_of
            (convolution (density_of lborel f) (density_of lborel g)) =
          measure_of
            (density_of lborel (\x. pos_fn_integral lborel (\y. f (x - y) * g y)))
Proof
    rpt STRIP_TAC
 >> qmatch_abbrev_tac ‘measure_of (convolution M1 M2) = _’
 >> ASSUME_TAC measure_space_lborel
 >> Know ‘m_space M1 = UNIV /\ m_space M2 = UNIV /\
          measurable_space M1 = borel /\
          measurable_space M2 = borel’
 >- (simp [Abbr ‘M1’, Abbr ‘M2’, density_of_pos_fn, lborel_def] \\
     simp [space_lborel])
 >> STRIP_TAC
 >> MATCH_MP_TAC measure_of_eq'
 >> ‘measure_space M1 /\ measure_space M2’ by METIS_TAC [measure_space_density_of]
 >> ‘sigma_finite_measure_space M1 /\
     sigma_finite_measure_space M2’
       by fs [finite_measure_space, sigma_finite_measure_space_def]
 (* Part 1: measure_space (convolution M1 M2) *)
 >> STRONG_CONJ_TAC
 >- (MATCH_MP_TAC measure_space_convolution >> art [] \\
     simp [Abbr ‘M1’, Abbr ‘M2’, density_of, lborel_def])
 >> DISCH_TAC
 >> ‘!x y. f (x - y) * g y = (\(x,y). (f (x - y) * g y)) (x,y)’ by rw []
 >> POP_ORW
 >> qabbrev_tac ‘h = \(x,y). f (x - y) * g y’
 >> Know ‘h IN Borel_measurable (borel CROSS borel)’
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES' \\
     rw [Abbr ‘h’, sigma_algebra_borel_2d, space_borel_2d, FORALL_PROD] \\
     qexistsl_tac [‘\z. f (FST z - SND z)’, ‘g o SND’] \\
     reverse CONJ_TAC
     >- (reverse CONJ_TAC >- rw [] \\
         MATCH_MP_TAC MEASURABLE_COMP \\
         Q.EXISTS_TAC ‘measurable_space lborel’ >> art [] \\
         simp [lborel_def, MEASURABLE_SND, sigma_algebra_borel]) \\
     Know ‘(\z. f (FST z - SND z)) = f o (\(x,y). x - y)’
     >- (simp [o_DEF, FUN_EQ_THM, FORALL_PROD]) >> Rewr' \\
     MATCH_MP_TAC MEASURABLE_COMP \\
     Q.EXISTS_TAC ‘measurable_space lborel’ >> art [] \\
     simp [lborel_def, borel_2d_measurable_sub])
 >> DISCH_TAC
 >> ‘!z. 0 <= h z’ by (fs [space_lborel] >> simp [FORALL_PROD, Abbr ‘h’, le_mul])
 (* Part 2: measure_space (density_of lborel ...) *)
 >> CONJ_TAC
 >- (MATCH_MP_TAC measure_space_density_of >> art [] \\
  (* applying TONELLI *)
     MP_TAC (Q.SPECL [‘m_space lborel’, ‘m_space lborel’,
                      ‘measurable_sets lborel’, ‘measurable_sets lborel’,
                      ‘lambda’, ‘lambda’, ‘h’]
                     (INST_TYPE [alpha |-> “:real”, beta |-> “:real”] TONELLI)) \\
     simp [MEASURE_SPACE_REDUCE] \\
     simp [sigma_finite_measure_space_def, sigma_finite_lborel, lborel_def])
 (* Part 3: measurable_sets (convolution M1 M2) = _ *)
 >> STRONG_CONJ_TAC
 >- (SIMP_TAC std_ss [convolution, distr_of, density_of, measurable_sets_def] \\
     SIMP_TAC std_ss [sets_lborel])
 >> Rewr'
 (* stage work *)
 >> RW_TAC std_ss []
 >> qmatch_abbrev_tac ‘measure (convolution M1 M2) A =
                       measure (density_of lborel h2) A’
 >> Know ‘!x. x IN m_space lborel ==> 0 <= h2 x’
 >- (rw [Abbr ‘h2’] >> MATCH_MP_TAC pos_fn_integral_pos >> rw [])
 >> DISCH_TAC
 >> simp [convolution, density_of_pos_fn, distr_of]
 >> ‘A IN measurable_sets lborel’ by METIS_TAC [density_of, measurable_sets_def]
 >> ‘A IN subsets borel’ by METIS_TAC [sets_lborel]
 >> simp [prod_measure_space_def, GSYM CROSS_UNIV]
 >> ‘measure_space (M1 CROSS M2)’ by simp [measure_space_prod_measure]
 >> qmatch_abbrev_tac ‘prod_measure M1 M2 (PREIMAGE h3 A) = _’
 >> Know ‘PREIMAGE h3 A IN measurable_sets (M1 CROSS M2)’
 >- (simp [prod_measure_space_def,
           Abbr ‘M1’, Abbr ‘M2’, density_of, lborel_def, Abbr ‘h3’] \\
     MP_TAC borel_2d_measurable_add \\
     rw [IN_MEASURABLE, SPACE_PROD_SIGMA, space_borel, GSYM CROSS_UNIV])
 >> DISCH_TAC
 (* stage work *)
 >> ‘!x y. indicator_fn (PREIMAGE h3 A) (x,y) = indicator_fn A (x + y)’
       by SIMP_TAC std_ss [indicator_fn_def, IN_PREIMAGE, Abbr ‘h3’]
 >> simp [prod_measure_def]
 >> qmatch_abbrev_tac ‘pos_fn_integral M2 f0 = _’
 >> Know ‘!x. 0 <= f0 x’
 >- (rw [Abbr ‘f0’] \\
     MATCH_MP_TAC pos_fn_integral_pos >> simp [INDICATOR_FN_POS])
 >> DISCH_TAC
 (* applying pos_fn_integral_density_reduce *)
 >> qunabbrev_tac ‘M2’
 >> Know ‘pos_fn_integral (density_of lborel g) f0 =
          pos_fn_integral lborel (\x. g x * f0 x)’
 >- (MATCH_MP_TAC pos_fn_integral_density_of_reduce \\
     simp [Abbr ‘f0’] \\
  (* preparing for TONELLI *)
    ‘!x y. indicator_fn A (x + y) = (\(x,y). indicator_fn A (x + y)) (x,y)’
       by rw [] >> POP_ORW \\
     qmatch_abbrev_tac ‘(\y. pos_fn_integral M1 (\x. h4 (x,y))) IN _’ \\
    ‘h4 = indicator_fn A o h3’
       by simp [Abbr ‘h4’, Abbr ‘h3’, o_DEF, FUN_EQ_THM, FORALL_PROD] >> POP_ORW \\
     qunabbrev_tac ‘h4’ \\
     qabbrev_tac ‘h4 = indicator_fn A o h3’ \\
     Know ‘h4 IN Borel_measurable (borel CROSS borel)’
     >- (qunabbrev_tac ‘h4’ \\
         MATCH_MP_TAC MEASURABLE_COMP \\
         Q.EXISTS_TAC ‘borel’ >> rw [Abbr ‘h3’, borel_2d_measurable_add] \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR \\
         Q.EXISTS_TAC ‘A’ >> rw [sigma_algebra_borel]) >> DISCH_TAC \\
    ‘!z. 0 <= h4 z’ by rw [Abbr ‘h4’, INDICATOR_FN_POS] \\
     qabbrev_tac ‘M2 = density_of lborel g’ \\
  (* applying TONELLI *)
     MP_TAC (Q.SPECL [‘m_space M1’, ‘m_space M2’,
                      ‘measurable_sets M1’, ‘measurable_sets M2’,
                      ‘measure M1’, ‘measure M2’, ‘h4’]
                     (INST_TYPE [alpha |-> “:real”, beta |-> “:real”] TONELLI)) \\
     simp [MEASURE_SPACE_REDUCE, lborel_def])
 >> Rewr'
 >> Q.PAT_X_ASSUM ‘!x. 0 <= f0 x’ K_TAC
 >> rw [Abbr ‘f0’, Abbr ‘M1’]
 >> GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [REAL_ADD_COMM]
 >> qabbrev_tac ‘f1 = \(x,y :real). indicator_fn A (x + y)’
 >> ‘!x y. indicator_fn A (x + y) = f1 (x,y)’ by rw [Abbr ‘f1’] >> POP_ORW
 >> ‘!z. 0 <= f1 z’ by simp [Abbr ‘f1’, INDICATOR_FN_POS, FORALL_PROD]
 >> Know ‘f1 IN Borel_measurable (borel CROSS borel)’
 >- (‘f1 = indicator_fn A o h3’
        by simp [Abbr ‘f1’, Abbr ‘h3’, FORALL_PROD, FUN_EQ_THM] >> POP_ORW \\
     MATCH_MP_TAC MEASURABLE_COMP \\
     Q.EXISTS_TAC ‘borel’ >> rw [Abbr ‘h3’, borel_2d_measurable_add] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR \\
     Q.EXISTS_TAC ‘A’ >> rw [sigma_algebra_borel])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘PREIMAGE h3 A IN _’               K_TAC
 >> Q.PAT_X_ASSUM ‘!x y. _ = indicator_fn A (x + y)’ K_TAC
 >> Q.PAT_X_ASSUM ‘measure_space (_ CROSS _)’        K_TAC
 >> qabbrev_tac ‘M1 = density_of lborel f’
 (* applying pos_fn_integral_cmul_general *)
 >> Know ‘pos_fn_integral lborel (\x. g x * pos_fn_integral M1 (\y. f1 (x,y))) =
          pos_fn_integral lborel (\x. pos_fn_integral M1 (\y. g x * f1 (x,y)))’
 >- (MATCH_MP_TAC pos_fn_integral_cong \\
     simp [measure_space_lborel, space_lborel] \\
     CONJ_TAC
     >- (rpt STRIP_TAC \\
         MATCH_MP_TAC le_mul >> fs [space_lborel] \\
         MATCH_MP_TAC pos_fn_integral_pos >> simp []) \\
     CONJ_TAC
     >- (Q.X_GEN_TAC ‘x’ \\
         MATCH_MP_TAC pos_fn_integral_pos >> simp [] \\
         Q.X_GEN_TAC ‘y’ \\
         MATCH_MP_TAC le_mul >> fs [space_lborel]) \\
     Q.X_GEN_TAC ‘x’ \\
     ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
    ‘0 <= g x’ by fs [space_lborel] \\
     HO_MATCH_MP_TAC pos_fn_integral_cmul_general \\
     rw [Abbr ‘f1’, INDICATOR_FN_POS] \\
    ‘(\y. indicator_fn A (x + y)) = indicator_fn A o (\y. x + y)’ by rw [o_DEF] \\
     POP_ORW \\
     ASSUME_TAC sigma_algebra_borel \\
     MATCH_MP_TAC MEASURABLE_COMP \\
     Q.EXISTS_TAC ‘borel’ \\
     reverse CONJ_TAC
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR \\
         Q.EXISTS_TAC ‘A’ >> rw []) \\
     HO_MATCH_MP_TAC in_borel_measurable_add \\
     qexistsl_tac [‘\y. x’, ‘I’] \\
     rw [MEASURABLE_I, sigma_algebra_borel] \\
     MATCH_MP_TAC in_borel_measurable_const \\
     Q.EXISTS_TAC ‘x’ >> rw [])
 >> Rewr'
 >> qabbrev_tac ‘f2 = \(x,y). g x * f1 (x,y)’
 >> ‘!x y. g x * f1 (x,y) = f2 (x,y)’ by rw [Abbr ‘f2’] >> POP_ORW
 >> ‘!z. 0 <= f2 z’ by (fs [space_lborel] >> simp [Abbr ‘f2’, FORALL_PROD, le_mul])
 >> Know ‘f2 IN Borel_measurable (borel CROSS borel)’
 >- (qunabbrev_tac ‘f2’ \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES' \\
     qexistsl_tac [‘g o FST’, ‘f1’] \\
     simp [sigma_algebra_borel_2d, FORALL_PROD] \\
     MATCH_MP_TAC MEASURABLE_COMP \\
     Q.EXISTS_TAC ‘borel’ \\
     simp [sigma_algebra_borel, MEASURABLE_FST] \\
     fs [lborel_def])
 >> DISCH_TAC
 >> qunabbrev_tac ‘M1’
 >> Know ‘pos_fn_integral lborel
            (\x. pos_fn_integral (density_of lborel f) (\y. f2 (x,y))) =
          pos_fn_integral lborel
            (\x. pos_fn_integral lborel (\y. f y * f2 (x,y)))’
 >- (MATCH_MP_TAC pos_fn_integral_cong \\
     simp [measure_space_lborel, space_lborel] \\
     CONJ_TAC
     >- (Q.X_GEN_TAC ‘x’ \\
         MATCH_MP_TAC pos_fn_integral_pos >> rw []) \\
     CONJ_TAC
     >- (Q.X_GEN_TAC ‘x’ \\
         MATCH_MP_TAC pos_fn_integral_pos >> fs [space_lborel, le_mul]) \\
     Q.X_GEN_TAC ‘x’ \\
     HO_MATCH_MP_TAC pos_fn_integral_density_of_reduce >> simp [] \\
  (* applying TONELLI *)
     MP_TAC (Q.SPECL [‘m_space lborel’, ‘m_space lborel’,
                      ‘measurable_sets lborel’, ‘measurable_sets lborel’,
                      ‘lambda’, ‘lambda’, ‘f2’]
                     (INST_TYPE [alpha |-> “:real”, beta |-> “:real”] TONELLI)) \\
     simp [MEASURE_SPACE_REDUCE] \\
     simp [sigma_finite_measure_space_def, sigma_finite_lborel, lborel_def,
           space_lborel])
 >> Rewr'
 >> qabbrev_tac ‘f3 = \(x,y). f y * f2 (x,y)’
 >> ‘!x y. f y * f2 (x,y) = f3 (x,y)’ by rw [Abbr ‘f3’] >> POP_ORW
 >> ‘!z. 0 <= f3 z’ by (fs [space_lborel] >> simp [Abbr ‘f3’, le_mul, FORALL_PROD])
 >> Know ‘f3 IN Borel_measurable (borel CROSS borel)’
 >- (qunabbrev_tac ‘f3’ \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES' \\
     qexistsl_tac [‘f o SND’, ‘f2’] \\
     simp [sigma_algebra_borel_2d, FORALL_PROD] \\
     MATCH_MP_TAC MEASURABLE_COMP \\
     Q.EXISTS_TAC ‘borel’ \\
     simp [sigma_algebra_borel, MEASURABLE_SND] \\
     fs [lborel_def])
 >> DISCH_TAC
 (* applying lebesgue_pos_integral_real_affine' *)
 >> Know ‘pos_fn_integral lborel (\x. pos_fn_integral lborel (\y. f3 (x,y))) =
          pos_fn_integral lborel
            (\x. Normal (abs 1) *
                 pos_fn_integral lborel (\y. f3 (x,-x + 1 * y)))’
 >- (MATCH_MP_TAC pos_fn_integral_cong \\
     SIMP_TAC std_ss [lborel_def, space_lborel, IN_UNIV] \\
     CONJ_TAC
     >- (Q.X_GEN_TAC ‘x’ \\
         MATCH_MP_TAC pos_fn_integral_pos >> rw []) \\
     CONJ_TAC
     >- (Q.X_GEN_TAC ‘x’ \\
         MATCH_MP_TAC le_mul >> simp [] \\
         MATCH_MP_TAC pos_fn_integral_pos >> rw []) \\
     Q.X_GEN_TAC ‘x’ \\
     qmatch_abbrev_tac ‘pos_fn_integral lborel f4 = _’ \\
    ‘(\y. f3 (x,-x + 1 * y)) = (\y. f4 (-x + 1 * y))’
       by rw [Abbr ‘f4’, FUN_EQ_THM] >> POP_ORW \\
     MATCH_MP_TAC lebesgue_pos_integral_real_affine' \\
     simp [Abbr ‘f4’] \\
  (* applying TONELLI *)
     MP_TAC (Q.SPECL [‘m_space lborel’, ‘m_space lborel’,
                      ‘measurable_sets lborel’, ‘measurable_sets lborel’,
                      ‘lambda’, ‘lambda’, ‘f3’]
                     (INST_TYPE [alpha |-> “:real”, beta |-> “:real”] TONELLI)) \\
     simp [MEASURE_SPACE_REDUCE] \\
     simp [sigma_finite_measure_space_def, sigma_finite_lborel, lborel_def] \\
     simp [space_lborel])
 >> Rewr'
 (* stage work *)
 >> Q.PAT_X_ASSUM ‘!z. 0 <= f3 z’ K_TAC
 >> Q.PAT_X_ASSUM ‘!z. 0 <= f2 z’ K_TAC
 >> Q.PAT_X_ASSUM ‘!z. 0 <= f1 z’ K_TAC
 >> rpt (Q.PAT_X_ASSUM ‘_ IN Borel_measurable (borel CROSS borel)’ K_TAC)
 >> rw [Abbr ‘f3’, Abbr ‘f2’, Abbr ‘f1’, mul_assoc]
 >> ‘!x y:real. x + (-x + y) = y’ by REAL_ARITH_TAC >> POP_ORW
 >> simp [normal_1]
 >> ‘!x y:real. -x + y = y - x’ by REAL_ARITH_TAC >> POP_ORW
 >> qabbrev_tac ‘f4 = \(x,y). f (y - x) * g x * indicator_fn A y’
 >> ‘!x y. f (y - x) * g x * indicator_fn A y = f4 (x,y)’ by rw [Abbr ‘f4’]
 >> POP_ORW
 >> Know ‘!z. 0 <= f4 z’
 >- (simp [Abbr ‘f4’, FORALL_PROD] \\
     qx_genl_tac [‘x’, ‘y’] \\
     fs [space_lborel] \\
     MATCH_MP_TAC le_mul >> rw [le_mul, INDICATOR_FN_POS])
 >> DISCH_TAC
 >> Know ‘f4 IN Borel_measurable (borel CROSS borel)’
 >- (qunabbrev_tac ‘f4’ \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES' \\
     qexistsl_tac [‘\z. f (SND z - FST z) * g (FST z)’, ‘indicator_fn A o SND’] \\
     simp [sigma_algebra_borel_2d, FORALL_PROD] \\
     ASSUME_TAC sigma_algebra_borel \\
     reverse CONJ_TAC
     >- (MATCH_MP_TAC MEASURABLE_COMP \\
         Q.EXISTS_TAC ‘borel’ >> simp [MEASURABLE_SND] \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR \\
         Q.EXISTS_TAC ‘A’ >> simp []) \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES' \\
     qexistsl_tac [‘f o (\z. SND z - FST z)’, ‘g o FST’] \\
     ASM_SIMP_TAC std_ss [sigma_algebra_borel_2d, SPACE_PROD_SIGMA] \\
     reverse CONJ_TAC
     >- (MATCH_MP_TAC MEASURABLE_COMP \\
         Q.EXISTS_TAC ‘measurable_space lborel’ >> art [] \\
         simp [MEASURABLE_FST, lborel_def]) \\
     MATCH_MP_TAC MEASURABLE_COMP \\
     Q.EXISTS_TAC ‘measurable_space lborel’ >> art [] \\
     simp [lborel_def] \\
     MATCH_MP_TAC in_borel_measurable_sub \\
     qexistsl_tac [‘SND’, ‘FST’] \\
     simp [sigma_algebra_borel_2d, MEASURABLE_FST, MEASURABLE_SND, FORALL_PROD])
 >> DISCH_TAC
 >> Know ‘pos_fn_integral lborel (\x. pos_fn_integral lborel (\y. f4 (x,y))) =
          pos_fn_integral lborel (\y. pos_fn_integral lborel (\x. f4 (x,y)))’
 >- (MATCH_MP_TAC pos_fn_integral_exchange \\
     simp [sigma_finite_measure_space_def, sigma_finite_lborel, lborel_def])
 >> Rewr'
 >> NTAC 2 (POP_ASSUM K_TAC) (* f4-related *)
 >> simp [Abbr ‘f4’, Abbr ‘h3’]
 >> MATCH_MP_TAC pos_fn_integral_cong
 >> simp [lborel_def, space_lborel]
 >> CONJ_TAC
 >- (Q.X_GEN_TAC ‘x’ \\
     MATCH_MP_TAC pos_fn_integral_pos >> fs [lborel_def, space_lborel] \\
     Q.X_GEN_TAC ‘y’ \\
     MATCH_MP_TAC le_mul >> rw [le_mul, INDICATOR_FN_POS])
 >> CONJ_TAC
 >- (Q.X_GEN_TAC ‘x’ \\
     fs [space_lborel] \\
     MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS])
 >> Q.PAT_X_ASSUM ‘!x. x IN m_space lborel ==> 0 <= h2 x’ K_TAC
 >> Q.PAT_X_ASSUM ‘!z. 0 <= h z’ K_TAC
 >> simp [Abbr ‘h2’, Abbr ‘h’]
 >> Q.X_GEN_TAC ‘x’
 >> qabbrev_tac ‘c = indicator_fn A x’
 >> ‘0 <= c’ by rw [Abbr ‘c’, INDICATOR_FN_POS]
 >> qmatch_abbrev_tac ‘_ = pos_fn_integral lborel f5 * c’
 >> ‘(\y. f (x - y) * g y * c) = (\y. f5 y * c)’ by rw [Abbr ‘f5’, FUN_EQ_THM]
 >> POP_ORW
 >> ONCE_REWRITE_TAC [mul_comm]
 >> MATCH_MP_TAC pos_fn_integral_cmul_general
 >> fs [lborel_def, space_lborel]
 >> reverse CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> rw [Abbr ‘f5’, le_mul])
 >> qunabbrev_tac ‘f5’
 >> HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES'
 >> ASSUME_TAC sigma_algebra_borel
 >> qexistsl_tac [‘f o (\y. x - y)’, ‘g’]
 >> ASM_SIMP_TAC std_ss [space_borel, IN_UNIV]
 >> MATCH_MP_TAC MEASURABLE_COMP
 >> Q.EXISTS_TAC ‘borel’ >> art []
 >> MATCH_MP_TAC in_borel_measurable_sub
 >> qexistsl_tac [‘\y. x’, ‘I’]
 >> simp [space_borel, MEASURABLE_I]
 >> MATCH_MP_TAC in_borel_measurable_const
 >> Q.EXISTS_TAC ‘x’ >> rw []
QED

(* |- !f g.
        f IN Borel_measurable borel /\ g IN Borel_measurable borel /\
        finite_measure_space (density_of lborel f) /\
        finite_measure_space (density_of lborel g) /\ (!x. 0 <= f x) /\
        (!x. 0 <= g x) ==>
        measure_of (convolution (density_of lborel f) (density_of lborel g)) =
        measure_of
          (density_of lborel
             (\x. pos_fn_integral lborel (\y. f (x - y) * g y)))
 *)
Theorem convolution_density' =
        convolution_density |> SRULE [lborel_def, space_lborel]

Theorem measure_convolution_density :
    !f g A. f IN Borel_measurable (measurable_space lborel) /\
            g IN Borel_measurable (measurable_space lborel) /\
            finite_measure_space (density_of lborel f) /\
            finite_measure_space (density_of lborel g) /\
           (!x. x IN m_space lborel ==> 0 <= f x) /\
           (!x. x IN m_space lborel ==> 0 <= g x) /\
            A IN measurable_sets lborel ==>
            measure (convolution (density_of lborel f) (density_of lborel g)) A =
            measure (density_of lborel
                      (\x. pos_fn_integral lborel (\y. f (x - y) * g y))) A
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘f’, ‘g’] convolution_density)
 >> simp [measure_of_def]
 >> qabbrev_tac ‘h = \(x,y). f (x - y) * g y’
 >> ‘!x y. f (x - y) * g y = h (x,y)’ by rw [Abbr ‘h’, FUN_EQ_THM]
 >> POP_ORW
 >> ASSUME_TAC measure_space_lborel
 >> qabbrev_tac ‘M1 = density_of lborel f’
 >> qabbrev_tac ‘M2 = density_of lborel g’
 >> ‘measure_space M1 /\ measure_space M2’ by METIS_TAC [measure_space_density_of]
 >> ‘sigma_finite_measure_space M1 /\
     sigma_finite_measure_space M2’
       by fs [finite_measure_space, sigma_finite_measure_space_def]
 >> Know ‘measure_space (convolution M1 M2)’
 >- (MATCH_MP_TAC measure_space_convolution >> art [] \\
     simp [Abbr ‘M1’, Abbr ‘M2’, density_of_pos_fn, lborel_def])
 >> DISCH_TAC
 >> ‘!z. 0 <= h z’ by (fs [space_lborel] >> simp [Abbr ‘h’, le_mul, FORALL_PROD])
 >> Know ‘h IN Borel_measurable (borel CROSS borel)’
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES' \\
     rw [Abbr ‘h’, sigma_algebra_borel_2d, space_borel_2d, FORALL_PROD] \\
     qexistsl_tac [‘\z. f (FST z - SND z)’, ‘g o SND’] \\
     reverse CONJ_TAC
     >- (reverse CONJ_TAC >- rw [] \\
         MATCH_MP_TAC MEASURABLE_COMP \\
         Q.EXISTS_TAC ‘measurable_space lborel’ >> art [] \\
         simp [lborel_def, MEASURABLE_SND, sigma_algebra_borel]) \\
     Know ‘(\z. f (FST z - SND z)) = f o (\(x,y). x - y)’
     >- (simp [o_DEF, FUN_EQ_THM, FORALL_PROD]) >> Rewr' \\
     MATCH_MP_TAC MEASURABLE_COMP \\
     Q.EXISTS_TAC ‘measurable_space lborel’ >> art [] \\
     simp [lborel_def, borel_2d_measurable_sub])
 >> DISCH_TAC
 >> Know ‘measure_space (density_of lborel
                          (\x. pos_fn_integral lborel (\y. h (x,y))))’
 >- (MATCH_MP_TAC measure_space_density_of >> simp [lborel_def] \\
     MP_TAC (Q.SPECL [‘m_space lborel’, ‘m_space lborel’,
                      ‘measurable_sets lborel’, ‘measurable_sets lborel’,
                      ‘lambda’, ‘lambda’, ‘h’]
                     (INST_TYPE [alpha |-> “:real”, beta |-> “:real”] TONELLI)) \\
     simp [MEASURE_SPACE_REDUCE] \\
     simp [sigma_finite_measure_space_def, sigma_finite_lborel, lborel_def])
 >> DISCH_TAC
 >> qabbrev_tac ‘M = convolution M1 M2’
 >> qabbrev_tac ‘N = density_of lborel (\x. pos_fn_integral lborel (\y. h (x,y)))’
 >> qabbrev_tac ‘h2 = \x. pos_fn_integral lborel (\y. h (x,y))’
 >> Know ‘!x. x IN m_space lborel ==> 0 <= h2 x’
 >- (rw [space_lborel, Abbr ‘h2’] \\
     MATCH_MP_TAC pos_fn_integral_pos >> rw [space_lborel])
 >> DISCH_TAC
 >> Know ‘measurable_sets M = measurable_sets N’
 >- (simp [Abbr ‘M’, Abbr ‘N’, convolution, distr_of, density_of_pos_fn] \\
     SIMP_TAC std_ss [sets_lborel])
 >> DISCH_TAC
 >> STRIP_TAC >> NTAC 2 (POP_ASSUM MP_TAC)
 >> ‘measurable_sets M SUBSET POW (m_space M) /\
     measurable_sets N SUBSET POW (m_space N)’ by simp [MEASURE_SPACE_SUBSET_POW]
 >> NTAC 2 (POP_ASSUM (REWRITE_TAC o wrap))
 >> ‘sigma_sets (m_space M) (measurable_sets M) = measurable_sets M /\
     sigma_sets (m_space N) (measurable_sets N) = measurable_sets N’
       by METIS_TAC [sigma_sets_eq, MEASURE_SPACE_SIGMA_ALGEBRA]
 >> NTAC 2 (POP_ASSUM (REWRITE_TAC o wrap))
 >> STRIP_TAC
 >> REWRITE_TAC [MEASURE_SPACE_REDUCE]
 >> simp [FUN_EQ_THM]
 >> DISCH_THEN (MP_TAC o Q.SPEC ‘A’)
 >> Suff ‘measurable_sets N = measurable_sets lborel’ >- rw []
 >> simp [Abbr ‘N’, density_of_pos_fn]
QED

(* |- !f g A.
        f IN Borel_measurable borel /\ g IN Borel_measurable borel /\
        finite_measure_space (density_of lborel f) /\
        finite_measure_space (density_of lborel g) /\ (!x. 0 <= f x) /\
        (!x. 0 <= g x) /\ A IN subsets borel ==>
        measure (convolution (density_of lborel f) (density_of lborel g)) A =
        measure
          (density_of lborel
             (\x. pos_fn_integral lborel (\y. f (x - y) * g y))) A
 *)
Theorem measure_convolution_density' =
        measure_convolution_density |> SRULE [lborel_def, space_lborel, sets_lborel]

(* NOTE: The conclusion of this theorem doesn't need the random variable X,
   but to use normal_pdf_pos_fn_integral_eq_1, ‘normal_rv X p 0 sig1’ is
   necessary.
 *)
Theorem conv_normal_density_zero_mean[local] :
    !sig1 sig2 p X x. 0 < sig1 /\ 0 < sig2 /\
       prob_space p /\ normal_rv X p 0 sig1 ==>
       pos_fn_integral lborel
         (\y. Normal_density 0 sig1 (x - y) * Normal_density 0 sig2 y) =
       Normal_density 0 (sqrt (sig1 pow 2 + sig2 pow 2)) x
Proof
    RW_TAC std_ss []
 >> `0 < sig1 pow 2 /\ 0 < sig2 pow 2` by METIS_TAC [REAL_POW_LT]
 >> Know ‘pos_fn_integral lborel
            (\y. Normal_density 0 sig1 (x - y) *
                 Normal_density 0 sig2 y) =
          pos_fn_integral lborel
            (\y. Normal_density 0 (sqrt (sig1 pow 2 + sig2 pow 2)) x *
                 Normal_density
                    (sig2 pow 2 * x / (sig1 pow 2 + sig2 pow 2))
                    (sqrt (sig1 pow 2 * sig2 pow 2 / (sig1 pow 2 + sig2 pow 2))) y)’
 >- (Q.ABBREV_TAC `sig1' = sig1 pow 2` \\
     Q.ABBREV_TAC `sig2' = sig2 pow 2` \\
     Q.ABBREV_TAC `sig = sig1' * sig2' / (sig1' + sig2')` \\
    `!mu sig x. 0 <= Normal_density mu sig x` by
        METIS_TAC [extreal_of_num_def, extreal_le_def, normal_density_nonneg] \\
     MATCH_MP_TAC pos_fn_integral_cong \\
     simp [measure_space_lborel, space_lborel, le_mul] \\
     Q.X_GEN_TAC `y` \\
     RW_TAC real_ss [extreal_mul_def, extreal_11, normal_density] \\
    `0 <= sig1' + sig2'` by ASM_SIMP_TAC real_ss [REAL_LE_ADD, REAL_LT_IMP_LE] \\
     POP_ASSUM (ASSUME_TAC o MATCH_MP SQRT_POW_2) \\
     ASM_SIMP_TAC std_ss [] \\
    `0 < sig1' * sig2' / (sig1' + sig2')` by
       ASM_SIMP_TAC std_ss [REAL_LT_MUL, REAL_LT_DIV, REAL_LT_ADD] \\
    `0 <= sig` by METIS_TAC [REAL_LT_IMP_LE] \\
     POP_ASSUM (ASSUME_TAC o MATCH_MP SQRT_POW_2) \\
     ASM_SIMP_TAC std_ss [] \\
     ONCE_REWRITE_TAC [REAL_ARITH ``a * exp b * (c * exp d) =
                                   (a * c) * (exp b * exp d:real)``] \\
     MATCH_MP_TAC
       (METIS [] ``(a1 = a2) /\ (b1 = b2) ==> (a1 * b1:real = a2 * b2:real)``) \\
     CONJ_TAC (* equations about sqrt and pi *)
     >- (SIMP_TAC real_ss [real_div] \\
         ASSUME_TAC PI_POS \\
        `0 < 2 * pi * sig1'` by ASM_SIMP_TAC real_ss [REAL_LT_MUL] \\
        `0 < 2 * pi * sig2'` by ASM_SIMP_TAC real_ss [REAL_LT_MUL] \\
        `0 < 2 * pi * (sig1' + sig2')`
           by ASM_SIMP_TAC real_ss [REAL_LT_MUL, REAL_LT_ADD] \\
        `0 < sig` by METIS_TAC [] \\
        `0 < 2 * pi * sig` by ASM_SIMP_TAC real_ss [REAL_LT_MUL] \\
        `0 <> sqrt (2 * pi * sig1')`
           by (MATCH_MP_TAC REAL_LT_IMP_NE >> ASM_SIMP_TAC std_ss [SQRT_POS_LT]) \\
        `0 <> sqrt (2 * pi * sig2')`
           by (MATCH_MP_TAC REAL_LT_IMP_NE >> ASM_SIMP_TAC std_ss [SQRT_POS_LT]) \\
        `0 <> sqrt (2 * pi * (sig1' + sig2'))`
           by (MATCH_MP_TAC REAL_LT_IMP_NE >> ASM_SIMP_TAC std_ss [SQRT_POS_LT]) \\
        `0 <> sqrt (2 * pi * sig)`
           by (MATCH_MP_TAC REAL_LT_IMP_NE >> ASM_SIMP_TAC std_ss [SQRT_POS_LT]) \\
         ASM_SIMP_TAC std_ss [GSYM REAL_INV_MUL, REAL_INV_INJ] \\
         ASM_SIMP_TAC real_ss [GSYM SQRT_MUL, REAL_LT_IMP_LE] \\
         AP_TERM_TAC \\
         ONCE_REWRITE_TAC [REAL_ARITH
           ``a * b * c * (a * b * d) = (a * b * a * b) * (c * d:real)``] \\
         AP_TERM_TAC \\
         Q.UNABBREV_TAC `sig` >> ONCE_REWRITE_TAC [REAL_MUL_COMM] \\
        `sig1' + sig2' <> 0`
           by ASM_SIMP_TAC real_ss [REAL_LT_ADD, REAL_LT_IMP_NE] \\
         ASM_SIMP_TAC real_ss [REAL_DIV_RMUL] \\
         METIS_TAC [REAL_MUL_COMM]) \\
  (* equations about exp *)
     ASM_SIMP_TAC std_ss [GSYM EXP_ADD] >> AP_TERM_TAC \\
  (* exp is eliminated.. *)
     SIMP_TAC real_ss [real_div] \\
     REWRITE_TAC [REAL_ARITH ``(-a + -b = -c + -d) <=> (a + b = c + d:real)``] \\
     Q.UNABBREV_TAC `sig` \\
     SIMP_TAC std_ss [real_div, POW_2] \\
     ONCE_REWRITE_TAC [REAL_ARITH
       ``!a b. (a - b) * (a - b) = (a * a) - (2 * a * b:real) + (b * b)``] \\
     SIMP_TAC std_ss [REAL_MUL_ASSOC] \\
     Q.ABBREV_TAC `sig = sig1' + sig2'` \\
     REWRITE_TAC [REAL_ARITH ``!a b. (a + b) * c = a * c + b * c:real``] \\
     REWRITE_TAC [REAL_ARITH ``!a b. (a - b) * c = a * c - b * c:real``] \\
     Know ‘2 * y * sig2' * x * inv sig * inv (2 * sig1' * sig2' * inv sig) =
           2 * x * y * inv (2 * sig1')’
     >- (`2 <> 0:real` by REAL_ARITH_TAC \\
         `sig1' <> 0 /\ sig2' <> 0` by METIS_TAC [REAL_LT_IMP_NE, EQ_SYM_EQ] \\
         `0 < sig1' + sig2'` by ASM_SIMP_TAC std_ss [REAL_LT_ADD] \\
         `0 < inv sig` by METIS_TAC [REAL_INV_POS] \\
         `inv sig <> 0` by METIS_TAC [REAL_LT_IMP_NE, EQ_SYM_EQ] \\
         ASM_SIMP_TAC std_ss [REAL_MUL_NZ, REAL_INV_MUL, REAL_INV_INV] \\
         SIMP_TAC std_ss [REAL_MUL_ASSOC] \\
         `sig <> 0` by METIS_TAC [REAL_LT_IMP_NE] \\
         ONCE_REWRITE_TAC [REAL_ARITH
          ``2 * y * sig2' * x * inv sig * inv 2 * inv sig1' * inv sig2' * sig:real =
            2 * x * y * inv 2 * inv sig1' *
            (inv sig2' * sig2') * (inv sig * sig)``] \\
         ASM_SIMP_TAC real_ss [REAL_MUL_LINV]) >> Rewr' \\
     Q.ABBREV_TAC `DONE1 = 2 * x * y * inv (2 * sig1')` \\
    `2 <> 0:real` by REAL_ARITH_TAC \\
    `sig1' <> 0 /\ sig2' <> 0` by METIS_TAC [REAL_LT_IMP_NE, EQ_SYM_EQ] \\
    `0 < sig1' + sig2'` by ASM_SIMP_TAC std_ss [REAL_LT_ADD] \\
    `0 < inv sig` by METIS_TAC [REAL_INV_POS] \\
    `inv sig <> 0` by METIS_TAC [REAL_LT_IMP_NE, EQ_SYM_EQ] \\
     ASM_SIMP_TAC std_ss [REAL_MUL_NZ, REAL_INV_MUL, REAL_INV_INV, REAL_MUL_ASSOC] \\
     Know ‘y * y * inv 2 * inv sig1' * inv sig2' * sig =
           y * y * inv 2 * inv sig1' + y * y * inv 2 * inv sig2'’
     >- (Q.UNABBREV_TAC `sig` \\
         ONCE_REWRITE_TAC [REAL_ARITH ``!a b c. a * (b + c) = a * b + a * c:real``] \\
         REWRITE_TAC [REAL_ARITH
           ``y * y * inv 2 * inv sig1' * inv sig2' * sig1':real =
             y * y * inv 2 * inv sig2' * (sig1' * inv sig1')``] \\
         REWRITE_TAC [REAL_ARITH
           ``y * y * inv 2 * inv sig1' * inv sig2' * sig2':real =
             y * y * inv 2 * inv sig1' * (sig2' * inv sig2')``] \\
         ASM_SIMP_TAC real_ss [REAL_MUL_RINV] \\
         METIS_TAC [REAL_ADD_COMM]) >> Rewr' \\
     Q.ABBREV_TAC `DONE2 = y * y * inv 2 * inv sig1'` \\
     Q.ABBREV_TAC `DONE3 = y * y * inv 2 * inv sig2'` \\
     SIMP_TAC std_ss [REAL_ADD_ASSOC] \\
     ONCE_REWRITE_TAC [REAL_ARITH ``!a b c. a + (b) + c = a + c + b:real``] \\
     ONCE_REWRITE_TAC [REAL_ARITH ``a + b - c = -c + b + a:real``] \\
     SIMP_TAC std_ss [REAL_ADD_ASSOC, real_sub] \\
     AP_THM_TAC >> AP_TERM_TAC \\
     AP_THM_TAC >> AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC \\
    `sig <> 0` by METIS_TAC [REAL_LT_IMP_NE] \\
     ASM_SIMP_TAC std_ss [REAL_INV_MUL, REAL_MUL_ASSOC] \\
     ONCE_REWRITE_TAC [REAL_ARITH
       ``sig2' * x * inv sig * sig2' * x * inv sig * inv 2 * inv sig1' *
         inv sig2' * sig:real =
         x * x * inv 2 * (inv sig1' * (sig * inv sig) * (sig2' * inv sig2') *
         (sig2' * inv sig))``] \\
     ASM_SIMP_TAC real_ss [REAL_MUL_RINV] \\
     ONCE_REWRITE_TAC [REAL_ARITH ``x * x * inv 2 * a + x * x * inv 2 * b:real =
                                    x * x * inv 2 * (a + b:real)``] \\
     AP_TERM_TAC >> SIMP_TAC std_ss [REAL_MUL_ASSOC] \\
     ONCE_REWRITE_TAC [REAL_ARITH ``inv sig + inv sig1' * sig2' * inv sig:real =
                                    inv sig * (1 + (sig2' * inv sig1'))``] \\
     Know ‘(1 + sig2' * inv sig1') = (sig * inv sig1')’
     >- (ASM_SIMP_TAC real_ss [GSYM real_div, REAL_EQ_RDIV_EQ] \\
         ONCE_REWRITE_TAC [REAL_ARITH
           ``!a b c. (a + b) * c = a * c + b * c:real``] \\
         ASM_SIMP_TAC real_ss [real_div, GSYM REAL_MUL_ASSOC, REAL_MUL_LINV]) \\
     Rewr' \\
     ASM_SIMP_TAC real_ss [REAL_MUL_ASSOC, REAL_MUL_LINV])
 >> Rewr'
 >> Q.ABBREV_TAC `c = Normal_density 0 (sqrt (sig1 pow 2 + sig2 pow 2)) x`
 >> `!mu sig x. 0 <= Normal_density mu sig x`
       by METIS_TAC [extreal_of_num_def, extreal_le_def, normal_density_nonneg]
 >> `0 <= c` by METIS_TAC []
 >> qabbrev_tac
     ‘f = Normal_density (sig2 pow 2 * x / (sig1 pow 2 + sig2 pow 2))
                         (sqrt (sig1 pow 2 * sig2 pow 2 / (sig1 pow 2 + sig2 pow 2)))’
 >> simp []
 >> Know ‘pos_fn_integral lborel (\y. c * f y) =
          c * pos_fn_integral lborel f’
 >- (MATCH_MP_TAC pos_fn_integral_cmul_general \\
     simp [lborel_def, Abbr ‘c’, Abbr ‘f’, IN_MEASURABLE_BOREL_normal_density'])
 >> Rewr'
 >> qunabbrev_tac ‘f’
 >> `0 <= sig1 pow 2` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE]
 >> `0 < (sig1 pow 2 + sig2 pow 2)` by ASM_SIMP_TAC real_ss [REAL_LT_ADD]
 >> SIMP_TAC std_ss [real_div]
 >> ONCE_REWRITE_TAC [REAL_ARITH
      ``sig2 pow 2 * x * inv (sig1 pow 2 + sig2 pow 2):real =
        x * sig2 pow 2 * inv (sig1 pow 2 + sig2 pow 2)``]
 >> ONCE_REWRITE_TAC [GSYM REAL_MUL_ASSOC]
 >> SIMP_TAC std_ss [GSYM real_div]
 >> Q.ABBREV_TAC `b = sig2 pow 2 / (sig1 pow 2 + sig2 pow 2)`
 >> `0 < b` by METIS_TAC [REAL_LT_DIV]
 >> `0 <= b` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE]
 >> `0 <= sig1` by ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE]
 >> ASM_SIMP_TAC std_ss [SQRT_MUL, POW_2_SQRT]
 >> ONCE_REWRITE_TAC [REAL_MUL_COMM]
 >> GEN_REWR_TAC RAND_CONV [GSYM mul_rone] >> AP_TERM_TAC
 >> `0 < sqrt b` by METIS_TAC [SQRT_POS_LT]
 >> `sqrt b <> 0` by METIS_TAC [REAL_LT_IMP_NE]
 >> Q.ABBREV_TAC `a = sqrt b`
 >> Q.ABBREV_TAC `Y = (\z. (b * x) + a * X z)`
 >> `!z. Y z = (b * x) + a * X z` by METIS_TAC []
 >> `normal_rv Y p ((b * x) + a * 0) (abs a * sig1)` by METIS_TAC [normal_rv_affine']
 >> POP_ASSUM MP_TAC
 >> `abs a = a` by METIS_TAC [ABS_REFL, REAL_LT_IMP_LE]
 >> ASM_SIMP_TAC real_ss []
 >> DISCH_TAC
 >> `(\x. PDF p Y x) = PDF p Y` by METIS_TAC [ETA_AX]
 >> `integral lborel (PDF p Y) = 1` by METIS_TAC [normal_pdf_integral_eq_1]
 >> `!x. 0 <= PDF p Y x` by METIS_TAC [normal_pdf_nonneg]
 >> ASSUME_TAC measure_space_lborel
 >> `pos_fn_integral lborel (\x. PDF p Y x) = 1` by METIS_TAC [integral_pos_fn]
 >> `UNIV IN measurable_sets lborel`
      by METIS_TAC [m_space_lborel, space_borel, MEASURE_SPACE_MSPACE_MEASURABLE]
 >> `pos_fn_integral lborel (\z. PDF p Y z * indicator_fn UNIV z) =
     pos_fn_integral lborel
       (\z. Normal_density (b * x) (a * sig1) z * indicator_fn UNIV z)`
      by METIS_TAC [integral_normal_pdf_eq_density]
 >> POP_ASSUM MP_TAC
 >> SIMP_TAC std_ss [indicator_fn_def, IN_UNIV, mul_rone]
 >> METIS_TAC []
QED

Theorem sum_indep_normal :
    !p X Y mu1 mu2 sig1 sig2.
       prob_space p /\ 0 < sig1 /\ 0 < sig2 /\
       indep_rv p X Y borel borel /\
       normal_rv X p mu1 sig1 /\ normal_rv Y p mu2 sig2 ==>
       normal_rv (\x. X x + Y x) p (mu1 + mu2) (sqrt (sig1 pow 2 + sig2 pow 2))
Proof
    rpt STRIP_TAC
 (* applying indep_rv_cong *)
 >> Know ‘indep_rv p ((\x. -mu1 + x) o X) ((\x. -mu2 + x) o Y) borel borel’
 >- (MATCH_MP_TAC indep_rv_cong >> art [] \\
     fs [normal_rv] \\
     Suff ‘!c. (\x. c + x) IN borel_measurable borel’ >- rw [] \\
     Q.X_GEN_TAC ‘c’ \\
     HO_MATCH_MP_TAC in_borel_measurable_add \\
     qexistsl_tac [‘\x. c’, ‘I’] \\
     simp [sigma_algebra_borel, MEASURABLE_I] \\
     MATCH_MP_TAC in_borel_measurable_const \\
     Q.EXISTS_TAC ‘c’ >> rw [sigma_algebra_borel])
 >> simp [o_DEF]
 >> qmatch_abbrev_tac ‘indep_rv p X' Y' borel borel ==> _’
 >> DISCH_TAC
 >> Know ‘normal_rv (\x. -mu1 + 1 * X x) p (-mu1 + 1 * mu1) (abs 1 * sig1)’
 >- (MATCH_MP_TAC normal_rv_affine' \\
     Q.EXISTS_TAC ‘X’ >> ASM_SIMP_TAC real_ss [])
 >> simp [ETA_AX] >> DISCH_TAC
 >> Know ‘normal_rv (\x. -mu2 + 1 * Y x) p (-mu2 + 1 * mu2) (abs 1 * sig2)’
 >- (MATCH_MP_TAC normal_rv_affine' \\
     Q.EXISTS_TAC ‘Y’ >> ASM_SIMP_TAC real_ss [])
 >> simp [ETA_AX] >> DISCH_TAC
 >> Suff ‘normal_rv (\x. -mu1 + X x + (-mu2 + Y x)) p
                    0 (sqrt (sig1 pow 2 + sig2 pow 2))’
 >- (DISCH_TAC \\
     Know ‘normal_rv (\x. X x + Y x) p ((mu1 + mu2) + 1 * 0)
                     (abs 1 * (sqrt (sig1 pow 2 + sig2 pow 2)))’
     >- (MATCH_MP_TAC normal_rv_affine' \\
         Q.EXISTS_TAC `(\x. -mu1 + X x + (-mu2 + Y x))` \\
        `0 < sig1 pow 2 /\ 0 < sig2 pow 2` by METIS_TAC [REAL_POW_LT] \\
        `0 < (sig1 pow 2 + sig2 pow 2)` by ASM_SIMP_TAC real_ss [REAL_LT_ADD] \\
         ASM_SIMP_TAC real_ss [SQRT_POS_LT] \\
         rw [Abbr ‘X'’, Abbr ‘Y'’] \\
         REAL_ARITH_TAC) \\
     RW_TAC real_ss [])
 (* stage work *)
 >> SIMP_TAC std_ss [normal_rv]
 >> CONJ_TAC
 >- (fs [normal_rv, random_variable_def] \\
     MATCH_MP_TAC in_borel_measurable_add \\
     qexistsl_tac [‘X'’, ‘Y'’] >> rw [EVENTS_SIGMA_ALGEBRA])
 >> SIMP_TAC std_ss [normal_pmeasure, measurable_distr, FUN_EQ_THM]
 >> Q.X_GEN_TAC ‘s’
 >> `s IN subsets borel <=> s IN measurable_sets lborel`
       by METIS_TAC [sets_lborel]
 >> POP_ASSUM (REWRITE_TAC o wrap o SYM)
 >> Cases_on ‘s IN subsets borel’ >> rw []
 >> MP_TAC (Q.SPECL [‘p’, ‘X'’, ‘Y'’] sum_indep_random_variable) >> simp []
 >> impl_tac >- fs [normal_rv]
 >> DISCH_THEN (MP_TAC o Q.SPEC ‘s’) >> simp []
 >> DISCH_THEN K_TAC
 >> Know ‘distr_of p (space borel,subsets borel,(\x. 0)) X' =
          distr_of p lborel X'’
 >- (simp [distr_of, m_space_lborel, sets_lborel])
 >> Rewr'
 >> Know ‘distr_of p (space borel,subsets borel,(\x. 0)) Y' =
          distr_of p lborel Y'’
 >- (simp [distr_of, m_space_lborel, sets_lborel])
 >> Rewr'
 >> ASSUME_TAC measure_space_lborel
 >> Know ‘distr_of p lborel X' = density_of lborel (\x. Normal_density 0 sig1 x)’
 >- (qmatch_abbrev_tac ‘_ = density_of lborel f’ \\
     Know ‘!x. x IN m_space lborel ==> 0 <= f x’
     >- (rw [space_lborel, Abbr ‘f’] \\
         rw [extreal_of_num_def, extreal_le_eq, normal_density_nonneg]) \\
     DISCH_TAC \\
     simp [distr_of, density_of_pos_fn, GSYM prob_def, FUN_EQ_THM] \\
     Q.X_GEN_TAC ‘t’ \\
     simp [sets_lborel] \\
     Cases_on ‘t IN subsets borel’ >> rw [] \\
     Q.PAT_X_ASSUM ‘normal_rv X' p 0 sig1’ MP_TAC \\
     simp [normal_rv, measurable_distr, distribution_def, FUN_EQ_THM,
           normal_pmeasure, p_space_def, sets_lborel] \\
     STRIP_TAC \\
     POP_ASSUM (MP_TAC o Q.SPEC ‘t’) >> rw [])
 >> Rewr'
 >> Know ‘distr_of p lborel Y' = density_of lborel (\x. Normal_density 0 sig2 x)’
 >- (qmatch_abbrev_tac ‘_ = density_of lborel f’ \\
     Know ‘!x. x IN m_space lborel ==> 0 <= f x’
     >- (rw [space_lborel, Abbr ‘f’] \\
         rw [extreal_of_num_def, extreal_le_eq, normal_density_nonneg]) \\
     DISCH_TAC \\
     ASSUME_TAC measure_space_lborel \\
     simp [distr_of, density_of_pos_fn, GSYM prob_def, FUN_EQ_THM] \\
     Q.X_GEN_TAC ‘t’ \\
     simp [sets_lborel] \\
     Cases_on ‘t IN subsets borel’ >> rw [] \\
     Q.PAT_X_ASSUM ‘normal_rv Y' p 0 sig2’ MP_TAC \\
     simp [normal_rv, measurable_distr, distribution_def, FUN_EQ_THM,
           normal_pmeasure, p_space_def, sets_lborel] \\
     STRIP_TAC \\
     POP_ASSUM (MP_TAC o Q.SPEC ‘t’) >> rw [])
 >> Rewr'
 >> qmatch_abbrev_tac ‘measure (convolution (density_of lborel f)
                                            (density_of lborel g)) s = _’
 (* applying measure_convolution_density' *)
 >> Know ‘measure (convolution (density_of lborel f) (density_of lborel g)) s =
          measure (density_of lborel
                    (\x. pos_fn_integral lborel (\y. f (x - y) * g y))) s’
 >- (MATCH_MP_TAC measure_convolution_density' \\
     simp [Abbr ‘f’, Abbr ‘g’, IN_MEASURABLE_BOREL_normal_density',
           normal_density_nonneg] \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       simp [finite_measure_space_def] \\
       CONJ_TAC
       >- (MATCH_MP_TAC measure_space_density_of \\
           rw [lborel_def, IN_MEASURABLE_BOREL_normal_density']) \\
       qabbrev_tac ‘f = \x. Normal_density 0 sig1 x’ \\
      ‘!x. x IN m_space lborel ==> 0 <= f x’
         by rw [Abbr ‘f’, space_lborel, extreal_of_num_def, extreal_le_eq,
                normal_density_nonneg] \\
       simp [density_of_pos_fn, MEASURE_SPACE_SPACE] \\
       qabbrev_tac ‘A = m_space lborel’ \\
      ‘A IN measurable_sets lborel’ by METIS_TAC [MEASURE_SPACE_SPACE] \\
       simp [Abbr ‘f’] \\
       Know ‘pos_fn_integral lborel (\x. Normal_density 0 sig1 x * indicator_fn A x) =
             pos_fn_integral lborel (\x. PDF p X' x * indicator_fn A x)’
       >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
           MATCH_MP_TAC integral_normal_pdf_eq_density >> art []) >> Rewr' \\
       POP_ASSUM K_TAC \\
      ‘!x. 0 <= PDF p X' x’ by PROVE_TAC [normal_pdf_nonneg] \\
       Know ‘pos_fn_integral lborel (\x. PDF p X' x * indicator_fn A x) =
             pos_fn_integral lborel (PDF p X')’
       >- (MATCH_MP_TAC pos_fn_integral_cong \\
           simp [Abbr ‘A’, space_lborel] \\
           CONJ_TAC >- rw [le_mul, INDICATOR_FN_POS] \\
           rw [indicator_fn_def]) >> Rewr' \\
       Suff ‘pos_fn_integral lborel (PDF p X') = 1’ >- rw [] \\
       MATCH_MP_TAC normal_pdf_pos_fn_integral_eq_1 \\
       qexistsl_tac [‘0’, ‘sig1’] >> art [],
       (* goal 2 (of 2) *)
       simp [finite_measure_space_def] \\
       CONJ_TAC
       >- (MATCH_MP_TAC measure_space_density_of \\
           rw [lborel_def, IN_MEASURABLE_BOREL_normal_density']) \\
       qabbrev_tac ‘f = \x. Normal_density 0 sig2 x’ \\
      ‘!x. x IN m_space lborel ==> 0 <= f x’
         by rw [Abbr ‘f’, space_lborel, extreal_of_num_def, extreal_le_eq,
                normal_density_nonneg] \\
       simp [density_of_pos_fn, MEASURE_SPACE_SPACE] \\
       qabbrev_tac ‘A = m_space lborel’ \\
      ‘A IN measurable_sets lborel’ by METIS_TAC [MEASURE_SPACE_SPACE] \\
       simp [Abbr ‘f’] \\
       Know ‘pos_fn_integral lborel (\x. Normal_density 0 sig2 x * indicator_fn A x) =
             pos_fn_integral lborel (\x. PDF p Y' x * indicator_fn A x)’
       >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
           MATCH_MP_TAC integral_normal_pdf_eq_density >> art []) >> Rewr' \\
       POP_ASSUM K_TAC \\
      ‘!x. 0 <= PDF p Y' x’ by PROVE_TAC [normal_pdf_nonneg] \\
       Know ‘pos_fn_integral lborel (\x. PDF p Y' x * indicator_fn A x) =
             pos_fn_integral lborel (PDF p Y')’
       >- (MATCH_MP_TAC pos_fn_integral_cong \\
           simp [Abbr ‘A’, space_lborel] \\
           CONJ_TAC >- rw [le_mul, INDICATOR_FN_POS] \\
           rw [indicator_fn_def]) >> Rewr' \\
       Suff ‘pos_fn_integral lborel (PDF p Y') = 1’ >- rw [] \\
       MATCH_MP_TAC normal_pdf_pos_fn_integral_eq_1 \\
       qexistsl_tac [‘0’, ‘sig2’] >> art [] ])
 >> Rewr'
 >> qmatch_abbrev_tac ‘measure (density_of lborel h) s = _’
 >> Know ‘!x. x IN m_space lborel ==> 0 <= h x’
 >- (rw [space_lborel, Abbr ‘h’] \\
     MATCH_MP_TAC pos_fn_integral_pos >> simp [space_lborel] \\
     Q.X_GEN_TAC ‘y’ >> MATCH_MP_TAC le_mul \\
     simp [Abbr ‘f’, Abbr ‘g’, extreal_of_num_def, extreal_le_eq] \\
     rw [normal_density_nonneg])
 >> DISCH_TAC
 >> simp [density_of_pos_fn, sets_lborel]
 >> MATCH_MP_TAC pos_fn_integral_cong >> simp []
 >> CONJ_TAC >- rw [le_mul, INDICATOR_FN_POS]
 >> CONJ_TAC
 >- (rw [space_lborel] \\
     MATCH_MP_TAC le_mul \\
     rw [INDICATOR_FN_POS, extreal_of_num_def, extreal_le_eq] \\
     rw [normal_density_nonneg])
 >> POP_ASSUM K_TAC (* 0 <= h x *)
 >> rw [Abbr ‘f’, Abbr ‘g’, Abbr ‘h’, space_lborel]
 >> Suff ‘pos_fn_integral lborel
            (\y. Normal_density 0 sig1 (x - y) * Normal_density 0 sig2 y) =
          Normal_density 0 (sqrt (sig1 pow 2 + sig2 pow 2)) x’ >- rw []
 >> MATCH_MP_TAC conv_normal_density_zero_mean
 >> qexistsl_tac [‘p’, ‘X'’] >> art []
QED

(* Modern version of ‘convolution’ (measure function part only) *)
Definition convolution_measure_def :
    convolution_measure M N = distr (M CROSS N) (\(x,y). x + y :real)
End

Theorem m_space_convolution :
    !M N. m_space (convolution M N) = space borel
Proof
    rw [convolution_def]
QED

Theorem measurable_sets_convolution :
    !M N. measurable_sets (convolution M N) = subsets borel
Proof
    rw [convolution_def]
QED

Theorem measure_convolution :
    !M N s. s IN subsets borel ==>
            measure (convolution M N) s = convolution_measure M N s
Proof
    rw [convolution_def, convolution_measure_def]
QED

Theorem sum_indep_random_variable' :
    !(p :'a m_space) X Y.
        prob_space p /\ random_variable X p borel /\
        random_variable Y p borel /\ indep_vars p X Y borel borel ==>
        !s. s IN subsets borel ==>
            distribution p (\x. X x + Y x) s =
            convolution_measure
              (distr_of p (space borel,subsets borel,(\x. 0)) X)
              (distr_of p (space borel,subsets borel,(\x. 0)) Y) s
Proof
    rpt STRIP_TAC
 >> qmatch_abbrev_tac ‘_ = convolution_measure M N s’
 >> Suff ‘convolution_measure M N s = measure (convolution M N) s’
 >- (Rewr' \\
     qunabbrevl_tac [‘M’, ‘N’] \\
     irule sum_indep_random_variable >> art [])
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> MATCH_MP_TAC measure_convolution >> art []
QED

Definition ext_normal_rv_def :
    ext_normal_rv X p mu sig <=>
      (!x. x IN p_space p ==> X x <> PosInf /\ X x <> NegInf) /\
      normal_rv (real o X) p mu sig
End

Theorem normal_rv_and_ext_normal_rv :
    !p X mu sig. normal_rv X p mu sig <=> ext_normal_rv (Normal o X) p mu sig
Proof
    rw [ext_normal_rv_def, o_DEF, real_normal, ETA_AX]
QED

val _ = export_theory ();
val _ = html_theory "distribution";

(* References:

  [1] Qasim, M.: Formalization of Normal Random Variables,
      Concordia University (2016).
  [2] Chung, K.L.: A Course in Probability Theory, Third Edition.
      Academic Press (2001).
  [3] Rosenthal, J.S.: A First Look at Rigorous Probability Theory (Second Edition).
      World Scientific Publishing Company (2006).
  [4] Shiryaev, A.N.: Probability-1. Springer-Verlag New York (2016).
  [5] Schilling, R.L.: Measures, Integrals and Martingales (2nd Edition).
      Cambridge University Press (2017).
  [6] math.stackexchange.com:
      https://math.stackexchange.com/questions/1400327/existence-of-a-random-variable
  [7] Resnick, S.: A Probability Path. Springer (2019).
 *)
