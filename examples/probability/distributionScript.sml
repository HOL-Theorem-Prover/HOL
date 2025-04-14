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
     real_topologyTheory derivativeTheory;

open sigma_algebraTheory extreal_baseTheory extrealTheory real_borelTheory
     measureTheory borelTheory lebesgueTheory martingaleTheory probabilityTheory;

val _ = new_theory "distribution"; (* was: "normal_rv" *)

val DISC_RW_KILL = DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
                   POP_ASSUM K_TAC;

fun ASSERT_TAC tm = SUBGOAL_THEN tm STRIP_ASSUME_TAC;
fun METIS ths tm = prove(tm,METIS_TAC ths);
val T_TAC = rpt (Q.PAT_X_ASSUM ‘T’ K_TAC);

(* ------------------------------------------------------------------------- *)
(*  Properties of distribution_functions                                     *)
(* ------------------------------------------------------------------------- *)

(* NOTE: There's no supporting theorem for “distribution_function” in
   probabilityTheory. The present lemma seems the first one.
 *)
Theorem distribution_function_monotone :
    !p X f. prob_space p /\ random_variable X p Borel /\
            f = distribution_function p X ==> (!x y. x <= y ==> f x <= f y)
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

(* NOTE: This tactic is shared by existence_of_random_variable and the next
   existence_of_random_variable.
 *)
val distribution_function_right_continuous_tac =
    (simp [right_continuous_def] >> Q.X_GEN_TAC ‘x0’ \\
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
     Suff ‘PREIMAGE X {x | x <= Normal a} INTER sp IN  measurable_sets p’
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
     DISCH_THEN (MP_TAC o Q.SPEC `A`) >> DISC_RW_KILL \\
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
 >- (DISC_RW_KILL THEN
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
 >- (SIMP_TAC std_ss [] >> DISC_RW_KILL \\
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
