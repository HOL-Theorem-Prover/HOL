(* ========================================================================= *)
(*   Theory of Probability Distributions (former normal_rvTheory [1])        *)
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

Theory distribution  (* was: "normal_rv" *)
Ancestors
  combin arithmetic logroot pred_set topology pair cardinal real
  seq transc real_sigma iterate real_topology derivative metric
  nets sigma_algebra extreal_base extreal real_borel measure
  borel lebesgue lebesgue_measure martingale probability integration
  lim[qualified]
Libs
  numLib hurdUtils pred_setLib tautLib jrhUtils realLib Diff

fun METIS ths tm = prove(tm,METIS_TAC ths);
val T_TAC = rpt (Q.PAT_X_ASSUM ‘T’ K_TAC);

val _ = hide "equiv_class"; (* in pred_setTheory *)
val _ = hide "top"; (* defined in posetTheory *)

val set_ss = std_ss ++ PRED_SET_ss;

val _ = intLib.deprecate_int();
val _ = ratLib.deprecate_rat();

(* some proofs here are large with too many assumptions *)
val _ = set_trace "Goalstack.print_goal_at_top" 0;

(* ------------------------------------------------------------------------- *)
(*  Properties of distribution_functions                                     *)
(* ------------------------------------------------------------------------- *)

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
 >> ‘f = \x. max 0 (f x)’ by rw [FUN_EQ_THM, max_0_reduce] >> POP_ORW
 >> simp []
 >> MATCH_MP_TAC lebesgue_pos_integral_real_affine >> art []
QED

Theorem integral_real_affine :
    !f c t. c <> 0 /\ integrable lborel f ==>
            integrable lborel (\x. f (t + c * x)) /\
            integral lborel f =
            Normal (abs c) * integral lborel (\x. f (t + c * x))
Proof
    rpt GEN_TAC
 >> simp [integrable_def, lebesgueTheory.integral_def, lborel_def,
          GSYM CONJ_ASSOC]
 >> STRIP_TAC
 >> CONJ_ASM1_TAC
 >- (‘(\x. f (t + c * x)) = f o (\x. t + c * x)’ by rw [o_DEF, FUN_EQ_THM] \\
     POP_ORW \\
     MATCH_MP_TAC MEASURABLE_COMP \\
     Q.EXISTS_TAC ‘borel’ >> art [] \\
     MATCH_MP_TAC in_borel_measurable_add \\
     qexistsl_tac [‘\x. t’, ‘\x. c * x’] >> simp [sigma_algebra_borel] \\
     CONJ_TAC
     >- (MATCH_MP_TAC in_borel_measurable_const \\
         Q.EXISTS_TAC ‘t’ >> simp [sigma_algebra_borel]) \\
     MATCH_MP_TAC in_borel_measurable_cmul \\
     qexistsl_tac [‘\x. x’, ‘c’] \\
     simp [sigma_algebra_borel, in_borel_measurable_I])
 >> Know ‘(\x. f (t + c * x))^+ = (\x. f^+ (t + c * x))’
 >- simp [FUN_EQ_THM, FN_PLUS_ALT]
 >> Rewr'
 >> Know ‘(\x. f (t + c * x))^- = (\x. f^- (t + c * x))’
 >- simp [FUN_EQ_THM, FN_MINUS_ALT]
 >> Rewr'
 >> Know ‘f^+ IN Borel_measurable borel’
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_FN_PLUS \\
     simp [sigma_algebra_borel])
 >> DISCH_TAC
 >> Know ‘f^- IN Borel_measurable borel’
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_FN_MINUS \\
     simp [sigma_algebra_borel])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘f^+’, ‘c’, ‘t’] lebesgue_pos_integral_real_affine')
 >> simp [FN_PLUS_POS]
 >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘f^-’, ‘c’, ‘t’] lebesgue_pos_integral_real_affine')
 >> simp [FN_MINUS_POS]
 >> STRIP_TAC
 >> CONJ_ASM1_TAC
 >- (CCONTR_TAC >> fs [] \\
     Suff ‘Normal (abs c) * PosInf = PosInf’ >- PROVE_TAC [] \\
     Suff ‘0 < Normal (abs c)’ >- PROVE_TAC [mul_infty] \\
     rw [extreal_of_num_def])
 >> CONJ_ASM1_TAC
 >- (CCONTR_TAC >> fs [] \\
     Suff ‘Normal (abs c) * PosInf = PosInf’ >- PROVE_TAC [] \\
     Suff ‘0 < Normal (abs c)’ >- PROVE_TAC [mul_infty] \\
     rw [extreal_of_num_def])
 >> SYM_TAC
 >> MATCH_MP_TAC sub_ldistrib >> rw [] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC pos_not_neginf \\
      MATCH_MP_TAC pos_fn_integral_pos \\
      rw [lborel_def, space_lborel, FN_PLUS_POS],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC pos_not_neginf \\
      MATCH_MP_TAC pos_fn_integral_pos \\
      rw [lborel_def, space_lborel, FN_MINUS_POS] ]
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
    !mu sig x. 0 < sig ==> 0 < normal_density mu sig x
Proof
  RW_TAC std_ss [normal_density] THEN MATCH_MP_TAC REAL_LT_MUL THEN
  SIMP_TAC std_ss [EXP_POS_LT, GSYM REAL_INV_1OVER, REAL_LT_INV_EQ] THEN
  MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN SIMP_TAC real_ss [PI_POS], ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LT >> art []
QED

Theorem std_normal_density_decreasing :
    !x y. 0 <= x /\ x <= y ==> std_normal_density y <= std_normal_density x
Proof
    rw [std_normal_density_def]
 >> MATCH_MP_TAC REAL_LE_RMUL_IMP
 >> simp [EXP_MONO_LE]
 >> CONJ_TAC
 >- (MATCH_MP_TAC SQRT_POS_LE \\
     MATCH_MP_TAC REAL_LE_MUL >> simp [REAL_LT_IMP_LE, PI_POS])
 >> MATCH_MP_TAC POW_LE >> art []
QED

Theorem normal_density_alt_std :
    !mu sig x. 0 < sig ==>
               normal_density mu sig x =
               std_normal_density ((x - mu) / sig) / sig
Proof
    rw [normal_density]
 >> ‘0 <= pi’ by simp [REAL_LT_IMP_LE, PI_POS]
 >> Know ‘0 <= sig pow 2’
 >- (MATCH_MP_TAC POW_POS \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art [])
 >> DISCH_TAC
 >> ‘0 <= sig’ by simp [REAL_LT_IMP_LE]
 >> simp [SQRT_MUL, REAL_LE_MUL, POW_2_SQRT, REAL_INV_MUL']
 >> NTAC 3 (DISJ2_TAC)
 >> AP_TERM_TAC
 >> simp [real_div]
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

Overload std_normal_rv = “\X p. normal_rv X p 0 1”

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

Theorem integration_of_normal_rv :
    !p X mu sig g.
       prob_space p /\ normal_rv X p mu sig /\ g IN borel_measurable borel ==>
      (integrable p (Normal o g o X) <=>
       integrable lborel (\x. Normal (g x * normal_density mu sig x))) /\
      (integral p (Normal o g o X) =
       integral lborel (\x. Normal (g x * normal_density mu sig x)))
Proof
    rpt GEN_TAC
 >> simp [normal_rv_def, distribution_distr, random_variable_def,
          p_space_def, events_def, prob_def, prob_space_def]
 >> STRIP_TAC
 >> Know ‘Normal o g IN Borel_measurable borel’
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
     simp [sigma_algebra_borel])
 >> DISCH_TAC
 (* NOTE: To use “normal_rv X p mu sig” (distr p X s = normal_pmeasure mu sig s),
    we have no choice but to use integral_distr.
  *)
 >> MP_TAC (Q.SPECL [‘p’, ‘borel’, ‘X’, ‘Normal o g’]
                    (INST_TYPE [beta |-> “:real”] integral_distr))
 >> simp [sigma_algebra_borel]
 >> STRIP_TAC
 >> NTAC 2 (POP_ASSUM (REWRITE_TAC o wrap o SYM))
 >> qabbrev_tac ‘M = (space borel,subsets borel,distr p X)’
 >> Know ‘measure_space M’
 >- (qunabbrev_tac ‘M’ \\
     MATCH_MP_TAC measure_space_distr >> simp [sigma_algebra_borel])
 >> DISCH_TAC
 (* Now convert M to N, replacing “distr p X” by “normal_pmeasure mu sig” *)
 >> qabbrev_tac ‘N = (space borel,subsets borel,normal_pmeasure mu sig)’
 >> ‘measure_space N’ by PROVE_TAC [normal_measure_space]
 >> ‘measure_space_eq M N’ by rw [measure_space_eq_def, Abbr ‘M’, Abbr ‘N’]
 >> ‘integrable M (Normal o g) <=> integrable N (Normal o g)’
      by simp [integrable_cong_measure']
 >> ‘integral M (Normal o g) = integral N (Normal o g)’
      by simp [integral_cong_measure']
 >> NTAC 2 POP_ORW
 (* cleanups *)
 >> Q.PAT_X_ASSUM ‘measure_space p’              K_TAC
 >> Q.PAT_X_ASSUM ‘measure p (m_space p) = 1’    K_TAC
 >> Q.PAT_X_ASSUM ‘X IN borel_measurable _’      K_TAC
 >> Q.PAT_X_ASSUM ‘!s. s IN subsets borel ==> _’ K_TAC
 >> Q.PAT_X_ASSUM ‘measure_space M’              K_TAC
 >> Q.PAT_X_ASSUM ‘measure_space_eq M N’         K_TAC
 >> qunabbrev_tac ‘M’
 (* NOTE: now converting “normal_pmeasure” to “normal_density” *)
 >> qabbrev_tac ‘f = Normal_density mu sig’
 >> qabbrev_tac ‘M = density lborel f’
 >> Know ‘measure_space M’
 >- (qunabbrev_tac ‘M’ \\
     MATCH_MP_TAC measure_space_density >> simp [lborel_def, space_lborel] \\
     simp [Abbr ‘f’, extreal_of_num_def, normal_density_nonneg,
           IN_MEASURABLE_BOREL_normal_density'])
 >> DISCH_TAC
 >> Know ‘measure_space_eq N M’
 >- (rw [measure_space_eq_def, Abbr ‘M’, Abbr ‘N’, density_def,
         lborel_def, space_lborel, sets_lborel, space_borel] \\
     simp [normal_pmeasure_def, density_measure_def, sets_lborel])
 >> DISCH_TAC
 >> ‘integrable N (Normal o g) <=> integrable M (Normal o g)’
      by simp [integrable_cong_measure']
 >> ‘integral N (Normal o g) = integral M (Normal o g)’
      by simp [integral_cong_measure']
 >> NTAC 2 POP_ORW
 >> Q.PAT_X_ASSUM ‘measure_space M’      K_TAC
 >> Q.PAT_X_ASSUM ‘measure_space N’      K_TAC
 >> Q.PAT_X_ASSUM ‘measure_space_eq N M’ K_TAC
 >> qunabbrevl_tac [‘M’, ‘N’]
 (* applying integral_density *)
 >> MP_TAC (Q.SPECL [‘lborel’, ‘f’, ‘Normal o g’]
                    (INST_TYPE [alpha |-> “:real”] integral_density))
 >> simp [lborel_def, IN_MEASURABLE_BOREL_NORMAL, space_lborel]
 >> impl_tac
 >- simp [Abbr ‘f’, extreal_of_num_def, normal_density_nonneg,
          IN_MEASURABLE_BOREL_normal_density']
 >> Rewr'
 >> simp [Abbr ‘f’, extreal_mul_eq]
QED

(* NOTE: The the special integral of “exp (-1 / x pow 2)” is avoided here
   because it's contained in “normal_rv X p mu sig”, which actually *assumed*
   the existence of normal r.v.'s. What's really not proved (yet) and hard to
   prove, is |- ?p X. prob_space p /\ normal_rv X p mu sig
 *)
Theorem integral_normal_density :
    !p X mu sig.
       prob_space p /\ normal_rv X p mu sig ==>
       integrable lborel (\x. Normal (normal_density mu sig x)) /\
       integral lborel (\x. Normal (normal_density mu sig x)) = 1
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘mu’, ‘sig’, ‘\x. 1’] integration_of_normal_rv)
 >> simp [o_DEF]
 >> impl_tac
 >- (MATCH_MP_TAC in_borel_measurable_const \\
     Q.EXISTS_TAC ‘1’ >> simp [sigma_algebra_borel])
 >> STRIP_TAC
 >> NTAC 2 (POP_ASSUM (REWRITE_TAC o wrap o SYM))
 >> CONJ_TAC
 >- (fs [prob_space_def, FORALL_AND_THM] \\
     MATCH_MP_TAC integrable_const >> simp [GSYM lt_infty])
 >> simp [GSYM expectation_def, expectation_const]
QED

(* NOTE: The antecedents “?p X. prob_space p /\ normal_rv X p mu sig” can be
   removed only if the special integral of “exp (-1 / x pow 2)” is computed.
 *)
Theorem integral_normal_density' :
    !mu sig. (?p X. prob_space p /\ normal_rv X p mu sig) ==>
             integrable lborel (\x. Normal (normal_density mu sig x)) /\
             integral lborel (\x. Normal (normal_density mu sig x)) = 1
Proof
    METIS_TAC [integral_normal_density]
QED

(* By AXIOM/OpenAxiom/FriCAS, we have:

   (2) -> integrate(x*exp(-x^2/2),x)

               2
              x
            - --
               2
   (2)  - %e
                                         Type: Union(Expression(Integer),...)

   NOTE: Diff.HAS_VECTOR_DERIVATIVE_CONV is used here!
 *)
Theorem has_vector_derivative_x_std_normal_density :
    !x. ((\x. -std_normal_density x) has_vector_derivative
         x * std_normal_density x) (at x)
Proof
    rw [std_normal_density_def]
 >> qabbrev_tac ‘c = inv (sqrt (2 * pi))’
 >> MP_TAC (HAS_VECTOR_DERIVATIVE_CONV “\(x :real). -(exp (-(x pow 2) / 2) * c)”)
 >> simp [REAL_NEG_LMUL]
QED

Theorem HAS_INTEGRAL_MUL_INDICATOR :
    !f s l. ((\x. f x * indicator s x) has_integral l) UNIV <=>
            (f has_integral l) s
Proof
    rpt GEN_TAC
 >> ONCE_REWRITE_TAC [GSYM HAS_INTEGRAL_RESTRICT_UNIV]
 >> simp []
 >> MATCH_MP_TAC HAS_INTEGRAL_EQ_EQ >> rw [indicator]
QED

(* NOTE: FUNDAMENTAL_THEOREM_OF_CALCULUS is used here! *)
Theorem has_integral_x_std_normal_density :
    !a b. a <= b ==>
          ((\x. x * std_normal_density x) has_integral
           (std_normal_density a - std_normal_density b)) (interval [a,b])
Proof
    rpt STRIP_TAC
 >> ONCE_REWRITE_TAC [GSYM REAL_SUB_NEG2]
 >> HO_MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS
 >> rw [IN_INTERVAL]
 >> MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN
 >> REWRITE_TAC [has_vector_derivative_x_std_normal_density]
QED

Theorem integral_x_std_normal_density :
    integrable lborel (\x. Normal (x * std_normal_density x)) /\
    integral lborel (\x. Normal (x * std_normal_density x)) = 0
Proof
    qabbrev_tac ‘f = \x. x * std_normal_density x’
 >> Know ‘!x. 0 <= x ==> 0 <= f x’
 >- (rw [Abbr ‘f’] \\
     MATCH_MP_TAC REAL_LE_MUL \\
     simp [normal_density_nonneg])
 >> DISCH_TAC
 >> Know ‘f IN borel_measurable borel’
 >- (qunabbrev_tac ‘f’ \\
     MATCH_MP_TAC in_borel_measurable_mul \\
     qexistsl_tac [‘\x. x’, ‘std_normal_density’] \\
     simp [in_borel_measurable_I, space_borel, sigma_algebra_borel] \\
     REWRITE_TAC [in_measurable_borel_normal_density])
 >> DISCH_TAC
 >> simp []
 >> ‘(\x. Normal (f x)) = Normal o f’ by rw [FUN_EQ_THM, o_DEF] >> POP_ORW
 (* stage work *)
 >> simp [integrable_def, lebesgueTheory.integral_def,
          fn_plus_normal, fn_minus_normal]
 >> Know ‘Normal o f IN Borel_measurable (measurable_space lborel)’
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL \\
     simp [lborel_def])
 >> Rewr
 >> qabbrev_tac ‘g = \x. f x * indicator {y | 0 <= y} x’
 >> Know ‘g IN borel_measurable borel’
 >- (qunabbrev_tac ‘g’ \\
     MATCH_MP_TAC in_borel_measurable_mul_indicator \\
     simp [borel_measurable_sets, sigma_algebra_borel])
 >> DISCH_TAC
 >> Know ‘Normal o g IN Borel_measurable borel’
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
     simp [sigma_algebra_borel])
 >> DISCH_TAC
 >> ‘!x. 0 <= g x’ by rw [Abbr ‘g’, indicator]
 >> Know ‘f^+ = g’
 >- (rw [Abbr ‘g’, FUN_EQ_THM, real_fn_plus_def] \\
     Cases_on ‘0 <= x’ >> rw [indicator]
     >- PROVE_TAC [REAL_MAX_REDUCE] \\
     simp [Abbr ‘f’] \\
     Suff ‘x * std_normal_density x <= 0’
     >- METIS_TAC [REAL_MAX_ACI, REAL_MAX_REDUCE] \\
     simp [REAL_MUL_SIGN] \\
     fs [REAL_NOT_LE] \\
     simp [REAL_LT_IMP_LE, normal_density_pos])
 >> Rewr'
 (* applying lebesgue_pos_integral_real_affine' *)
 >> Know ‘f^- = \x. g (-x)’
 >- (rw [Abbr ‘g’, FUN_EQ_THM, real_fn_minus_def] \\
     Cases_on ‘0 <= x’ >> rw [indicator] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
      ‘x = 0’ by PROVE_TAC [REAL_LE_ANTISYM] \\
       simp [Abbr ‘f’],
       (* goal 2 (of 4) *)
       METIS_TAC [REAL_MIN_REDUCE],
       (* goal 3 (of 4) *)
       simp [Abbr ‘f’] \\
      ‘min 0 (x * std_normal_density x) = min (x * std_normal_density x) 0’
         by PROVE_TAC [REAL_MIN_ACI] >> POP_ORW \\
       Know ‘min (x * std_normal_density x) 0 = x * std_normal_density x’
       >- (Suff ‘x * std_normal_density x <= 0’
           >- PROVE_TAC [REAL_MIN_REDUCE] \\
           simp [REAL_MUL_SIGN] \\
           fs [REAL_NOT_LE] \\
           simp [REAL_LT_IMP_LE, normal_density_pos]) >> Rewr' \\
       simp [normal_density],
       (* goal 4 (of 4) *)
       fs [REAL_NOT_LE] \\
       PROVE_TAC [REAL_LT_ANTISYM] ])
 >> Rewr'
 >> Know ‘pos_fn_integral lborel (Normal o (\x. g (-x))) =
          pos_fn_integral lborel (Normal o g)’
 >- (MP_TAC (Q.SPECL [‘Normal o g’, ‘-1’, ‘0’]
                     lebesgue_pos_integral_real_affine') >> art [] \\
     simp [normal_1, o_DEF])
 >> Rewr'
 >> Suff ‘pos_fn_integral lborel (Normal o g) <> PosInf’
 >- (rw [] \\
     Know ‘pos_fn_integral lborel (Normal o g) <> NegInf’
     >- (MATCH_MP_TAC pos_not_neginf \\
         MATCH_MP_TAC pos_fn_integral_pos \\
         simp [lborel_def, space_lborel, o_DEF, extreal_of_num_def]) \\
     DISCH_TAC \\
    ‘?r. pos_fn_integral lborel (Normal o g) = Normal r’
       by METIS_TAC [extreal_cases] \\
     simp [extreal_sub_eq, extreal_of_num_def])
 (* preparing for lebesgue_monotone_convergence *)
 >> qabbrev_tac ‘h = \n x. f x * indicator (interval [0,&n]) x’
 >> Know ‘!n. h n IN borel_measurable borel’
 >- (rw [Abbr ‘h’] \\
     MATCH_MP_TAC in_borel_measurable_mul_indicator \\
     simp [interval, borel_measurable_sets, sigma_algebra_borel])
 >> DISCH_TAC
 >> Know ‘!n. Normal o h n IN Borel_measurable borel’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
     simp [sigma_algebra_borel])
 >> DISCH_TAC
 >> Know ‘!n x. 0 <= h n x’
 >- (rw [Abbr ‘h’, indicator, Abbr ‘f’, IN_INTERVAL] \\
     MATCH_MP_TAC REAL_LE_MUL \\
     simp [normal_density_nonneg])
 >> DISCH_TAC
 (* applying lebesgue_monotone_convergence *)
 >> Know ‘pos_fn_integral lborel (Normal o g) =
          sup (IMAGE (\i. pos_fn_integral lborel (Normal o h i)) UNIV)’
 >- (HO_MATCH_MP_TAC lebesgue_monotone_convergence \\
     simp [space_lborel, lborel_def] \\
     CONJ_TAC (* mono_increasing *)
     >- (Q.X_GEN_TAC ‘x’ \\
         simp [ext_mono_increasing_def] \\
         qx_genl_tac [‘i’, ‘j’] >> rw [Abbr ‘h’] \\
         reverse (Cases_on ‘0 <= x’) >- rw [indicator, IN_INTERVAL] \\
         MATCH_MP_TAC REAL_LE_LMUL_IMP \\
         CONJ_TAC >- (rw [Abbr ‘f’] \\
                      MATCH_MP_TAC REAL_LE_MUL >> art [] \\
                      simp [REAL_LT_IMP_LE, normal_density_pos]) \\
         MATCH_MP_TAC INDICATOR_MONO \\
         rw [SUBSET_DEF, IN_INTERVAL] \\
         rename1 ‘y <= &i’ \\
         Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘&i’ >> simp []) \\
     Q.X_GEN_TAC ‘x’ \\
     rw [sup_eq']
     >- (simp [Abbr ‘h’, Abbr ‘g’] \\
         reverse (Cases_on ‘0 <= x’) >- simp [indicator, IN_INTERVAL] \\
         MATCH_MP_TAC REAL_LE_LMUL_IMP >> simp [] \\
         MATCH_MP_TAC INDICATOR_MONO \\
         rw [SUBSET_DEF, IN_INTERVAL]) \\
     Know ‘!i. Normal (h i x) <= y’
     >- (Q.X_GEN_TAC ‘i’ \\
         POP_ASSUM MATCH_MP_TAC \\
         Q.EXISTS_TAC ‘i’ >> REFL_TAC) >> DISCH_TAC \\
     rw [Abbr ‘g’] \\
     reverse (Cases_on ‘0 <= x’)
     >- (Q.PAT_X_ASSUM ‘!i. Normal (h i x) <= y’ (MP_TAC o Q.SPEC ‘0’) \\
         rw [indicator, Abbr ‘h’, IN_INTERVAL]) \\
     STRIP_ASSUME_TAC (Q.SPEC ‘x’ SIMP_REAL_ARCH) \\
     Q_TAC (TRANS_TAC le_trans) ‘Normal (h n x)’ >> art [] \\
     simp [Abbr ‘h’] \\
     rw [indicator, IN_INTERVAL])
 >> Rewr'
 (* applying has_integral_x_std_normal_density *)
 >> Know ‘!n. (h n has_integral (std_normal_density 0 - std_normal_density &n))
               UNIV’
 >- (rw [Abbr ‘h’, HAS_INTEGRAL_MUL_INDICATOR] \\
     simp [Abbr ‘f’, has_integral_x_std_normal_density])
 >> rw [HAS_INTEGRAL_INTEGRABLE_INTEGRAL, FORALL_AND_THM]
 (* applying lebesgue_eq_gauge_integral_positive_alt *)
 >> Know ‘!n. pos_fn_integral lborel (Normal o h n) =
              Normal (integral univ(:real) (h n))’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC lebesgue_eq_gauge_integral_positive_alt >> art [])
 >> Rewr'
 >> POP_ORW
 >> qabbrev_tac ‘J = \n. std_normal_density 0 - std_normal_density (&n)’
 >> simp []
 >> Know ‘IMAGE (\i. Normal (J i)) UNIV = IMAGE Normal {J i | i | T}’
 >- (rw [Once EXTENSION] \\
     EQ_TAC >> rw [] >> (Q.EXISTS_TAC ‘i’ >> REFL_TAC))
 >> Rewr'
 >> qmatch_abbrev_tac ‘sup (IMAGE Normal s) <> PosInf’
 >> Know ‘sup (IMAGE Normal s) = Normal (sup s)’
 >- (MATCH_MP_TAC sup_image_normal \\
     CONJ_TAC >- simp [Abbr ‘s’, Once EXTENSION] \\
     rw [Abbr ‘s’, bounded_def] \\
     Q.EXISTS_TAC ‘std_normal_density 0’ >> rw [Abbr ‘J’] \\
     Know ‘abs (std_normal_density 0 - std_normal_density (&i)) =
                std_normal_density 0 - std_normal_density (&i)’
     >- (simp [ABS_REFL, REAL_SUB_LE] \\
         MATCH_MP_TAC std_normal_density_decreasing >> simp []) >> Rewr' \\
     Suff ‘0 <= std_normal_density (&i)’ >- REAL_ARITH_TAC \\
     simp [normal_density_nonneg])
 >> Rewr'
 (* NOTE: Here the proof finish easily, but if we want to actually calculate
    ‘sup s’ (= std_normal_density 0), just a little more work is needed.
  *)
 >> simp []
QED

Theorem expectation_of_std_normal_rv :
    !p X. prob_space p /\ std_normal_rv X p ==>
          integrable p (Normal o X) /\ expectation p (Normal o X) = 0
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘0’, ‘1’, ‘I’] integration_of_normal_rv)
 >> simp [I_EQ_IDABS, in_borel_measurable_I, expectation_def]
 >> DISCH_THEN K_TAC
 >> REWRITE_TAC [integral_x_std_normal_density]
QED

Theorem expectation_of_normal_rv :
    !p X mu sig. prob_space p /\ normal_rv X p mu sig /\ 0 < sig ==>
                 integrable p (Normal o X) /\
                 expectation p (Normal o X) = Normal mu
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘mu’, ‘sig’, ‘I’] integration_of_normal_rv)
 >> simp [I_EQ_IDABS, in_borel_measurable_I, expectation_def]
 >> DISCH_THEN K_TAC
 (* applying normal_density_alt_std *)
 >> Know ‘!x. normal_density mu sig x =
              std_normal_density ((x - mu) / sig) / sig’
 >- simp [Once normal_density_alt_std]
 >> Rewr'
 >> simp [real_div]
 >> qabbrev_tac ‘c = inv sig’
 >> Know ‘c <> 0’
 >- (qunabbrev_tac ‘c’ \\
     MATCH_MP_TAC REAL_INV_NZ \\
     PROVE_TAC [REAL_LT_IMP_NE])
 >> DISCH_TAC
 >> simp [REAL_SUB_LDISTRIB]
 >> qabbrev_tac ‘t = -(c * mu)’
 >> simp [real_sub]
 >> ONCE_REWRITE_TAC [REAL_ADD_COMM]
 >> qabbrev_tac ‘g = \x. t + c * x’
 >> simp []
 >> ‘!x. c * x = g x - t’ by simp [Abbr ‘g’, REAL_ADD_SUB]
 >> POP_ORW
 >> simp [REAL_SUB_RDISTRIB, GSYM extreal_sub_eq]
 >> Know ‘!x. t * std_normal_density (g x) =
              -mu * (std_normal_density ((x - mu) / sig) / sig)’
 >- (rw [Abbr ‘g’, Abbr ‘t’, Abbr ‘c’, real_div] \\
     DISJ2_TAC \\
     AP_TERM_TAC \\
     REAL_ARITH_TAC)
 >> Rewr'
 >> Know ‘!x. std_normal_density ((x - mu) / sig) / sig =
              normal_density mu sig x’
 >- simp [GSYM normal_density_alt_std]
 >> Rewr'
 >> qabbrev_tac ‘h = \x. g x * std_normal_density (g x)’
 >> simp []
 >> simp [GSYM extreal_mul_eq]
 >> qabbrev_tac ‘d = -mu’
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘mu’, ‘sig’] integral_normal_density)
 >> simp [] >> STRIP_TAC
 >> Know ‘integrable lborel (\x. Normal d * Normal_density mu sig x)’
 >- (HO_MATCH_MP_TAC integrable_cmul >> simp [lborel_def])
 >> DISCH_TAC
 >> Know ‘integral lborel (\x. Normal d * Normal_density mu sig x) =
          Normal d * integral lborel (\x. Normal_density mu sig x)’
 >- (HO_MATCH_MP_TAC integral_cmul >> simp [lborel_def])
 >> simp [] >> DISCH_TAC
 (* applying integral_x_std_normal_density *)
 >> STRIP_ASSUME_TAC integral_x_std_normal_density
 (* applying integral_real_affine *)
 >> MP_TAC (Q.SPECL [‘\x. Normal (x * std_normal_density x)’, ‘c’, ‘t’]
                    integral_real_affine)
 >> simp [] >> STRIP_TAC
 >> CONJ_TAC (* integrable *)
 >- (HO_MATCH_MP_TAC integrable_sub \\
     simp [extreal_mul_eq, lborel_def])
 >> Know ‘integral lborel (\x. Normal (h x) -
                               Normal d * Normal_density mu sig x) =
          integral lborel (\x. Normal (h x)) -
          integral lborel (\x. Normal d * Normal_density mu sig x)’
 >- (HO_MATCH_MP_TAC integral_sub \\
     simp [extreal_mul_eq, lborel_def])
 >> Rewr'
 >> simp [Abbr ‘d’, extreal_ainv_def]
QED

(* By AXIOM/OpenAxiom/FriCAS, we have:

   (5) -> integrate((x^2-1)*exp(-x^2/2),x)

                 2
                x
              - --
                 2
   (5)  - x %e
                                         Type: Union(Expression(Integer),...)

   NOTE: Diff.HAS_VECTOR_DERIVATIVE_CONV is used here!
 *)
Theorem has_vector_derivative_neg_x_std_normal_density :
    !x. ((\x. -x * std_normal_density x) has_vector_derivative
         (x pow 2 - 1) * std_normal_density x) (at x)
Proof
    rw [std_normal_density_def]
 >> qabbrev_tac ‘c = inv (sqrt (2 * pi))’
 >> MP_TAC (Q.SPEC ‘x’
             (HAS_VECTOR_DERIVATIVE_CONV
               “\(x :real). -x * exp (-(x pow 2) / 2) * c”))
 >> simp [REAL_NEG_LMUL]
 >> qabbrev_tac ‘z :real = exp (-(x pow 2) / 2)’
 >> qmatch_abbrev_tac ‘(f has_vector_derivative a) (at x) ==>
                       (_ has_vector_derivative b) (at x)’
 >> Suff ‘a = b’ >- rw []
 >> simp [Abbr ‘a’, Abbr ‘b’] >> REAL_ARITH_TAC
QED

(* |- !x. ((\x. -x * std_normal_density x) diffl
           ((x pow 2 - 1) * std_normal_density x)) x
 *)
Theorem diffl_neg_x_std_normal_density[local] =
        has_vector_derivative_neg_x_std_normal_density
     |> REWRITE_RULE [GSYM limTheory.diffl_has_vector_derivative]

(* Based on limTheory.DIFF_POS_MONO_LT_CU *)
Theorem neg_x_std_normal_density_increasing :
    !x y. 1 <= x /\ x <= y ==> -x * std_normal_density x <=
                               -y * std_normal_density y
Proof
    rpt STRIP_TAC
 >> ASSUME_TAC diffl_neg_x_std_normal_density
 >> qabbrev_tac ‘f = \x. -x * std_normal_density x’
 >> ASM_SIMP_TAC std_ss []
 >> ‘x = y \/ x < y’ by PROVE_TAC [REAL_LE_LT] >- simp []
 >> MATCH_MP_TAC REAL_LT_IMP_LE
 >> irule limTheory.DIFF_POS_MONO_LT_CU >> art []
 >> Q.EXISTS_TAC ‘1’ >> art []
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC limTheory.DIFF_CONT \\
     Q.EXISTS_TAC ‘(1 pow 2 - 1) * std_normal_density 1’ >> art [])
 >> rpt STRIP_TAC
 >> Q.EXISTS_TAC ‘(z pow 2 - 1) * std_normal_density z’ >> art []
 >> MATCH_MP_TAC REAL_LT_MUL
 >> simp [normal_density_pos, REAL_SUB_LT]
 >> ‘1 :real = 1 pow 2’ by simp [] >> POP_ORW
 >> ‘2 = SUC 1’ by simp [] >> POP_ORW
 >> MATCH_MP_TAC POW_LT >> simp []
QED

(* |- !x y.
        1 <= x /\ x <= y ==>
        y * std_normal_density y <= x * std_normal_density x
 *)
Theorem x_std_normal_density_decreasing =
        REWRITE_RULE [REAL_MUL_LNEG, REAL_LE_NEG2]
                     neg_x_std_normal_density_increasing

Theorem has_integral_x_x_1_std_normal_density :
    !a b. a <= b ==>
         ((\x. (x pow 2 - 1) * std_normal_density x) has_integral
          (a * std_normal_density a -
           b * std_normal_density b)) (interval [a,b])
Proof
    rpt STRIP_TAC
 >> ‘a * std_normal_density a - b * std_normal_density b =
    -b * std_normal_density b - -a * std_normal_density a’ by REAL_ARITH_TAC
 >> POP_ORW
 >> HO_MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS
 >> rw [IN_INTERVAL]
 >> MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN
 >> REWRITE_TAC [has_vector_derivative_neg_x_std_normal_density]
QED

(* NOTE: This proof is based on the new LN_LT_HALF_X (transc):

   |- ln x < x / 2 (2 <= x)
  <=> x - ln x > x - x / 2 (= x / 2)

      exp n > z * n
  <=> n > ln z + ln n
  <=> n - ln n > n / 2 > ln z
  <=> n > 2 * ln z
 *)
Theorem lim_sequentially_n_std_normal_density :
    ((\n. &n * std_normal_density (&n)) --> 0) sequentially
Proof
    rw [LIM_SEQUENTIALLY, dist]
 >> ‘e <> 0’ by PROVE_TAC [REAL_LT_IMP_NE]
 >> Know ‘!n. abs (&n * std_normal_density (&n)) =
                   &n * std_normal_density (&n)’
 >- (rw [ABS_REFL] \\
     MATCH_MP_TAC REAL_LE_MUL >> simp [normal_density_nonneg])
 >> Rewr'
 >> simp [std_normal_density_def]
 >> qabbrev_tac ‘c :real = inv (sqrt (2 * pi))’
 >> Know ‘0 < c’
 >- (simp [Abbr ‘c’] \\
     MATCH_MP_TAC SQRT_POS_LT \\
     MATCH_MP_TAC REAL_LT_MUL >> simp [PI_POS])
 >> DISCH_TAC
 >> REWRITE_TAC [GSYM neg_rat, EXP_NEG]
 >> simp [EXP_DIV, GSYM sqrt, GSYM real_div]
 >> Know ‘!n. c * &n / sqrt (exp (&n pow 2)) < e <=>
              c * &n < e * sqrt (exp (&n pow 2))’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC REAL_LT_LDIV_EQ \\
     simp [SQRT_POS_LT, EXP_POS_LT])
 >> Rewr'
 >> ONCE_REWRITE_TAC [REAL_MUL_COMM]
 >> ‘!n. &n * c < sqrt (exp (&n pow 2)) * e <=>
         &n * c / e < sqrt (exp (&n pow 2))’ by rw [] >> POP_ORW
 >> ‘!n. &n * c / e = c / e * &n’ by simp [] >> POP_ORW
 >> qabbrev_tac ‘d = c / e’
 >> ‘0 < d’ by simp [Abbr ‘d’, REAL_LT_DIV]
 >> Know ‘!n. d * &n < sqrt (exp (&n pow 2)) <=>
              (d * &n) pow 2 < sqrt (exp (&n pow 2)) pow 2’
 >- (Q.X_GEN_TAC ‘n’ \\
     qmatch_abbrev_tac ‘a < (b :real) <=> _’ \\
     SYM_TAC >> MATCH_MP_TAC REAL_POW_LT_EQ \\
     simp [Abbr ‘a’, Abbr ‘b’, SQRT_POS_LE, EXP_POS_LE] \\
     MATCH_MP_TAC REAL_LE_MUL \\
     simp [REAL_LT_IMP_LE])
 >> Rewr'
 >> simp [SQRT_POW_2, EXP_POS_LE, POW_MUL]
 >> qabbrev_tac ‘z = d pow 2’
 >> Suff ‘?N. !n. N <= n ==> z * &n < exp (&n)’
 >- (STRIP_TAC \\
     Q.EXISTS_TAC ‘SUC (SQRT N) ** 2’ \\
     STRIP_ASSUME_TAC (Q.SPEC ‘N’ SQRT_PROPERTY) \\
     rw [REAL_POW] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     MATCH_MP_TAC LT_IMP_LE \\
     Q_TAC (TRANS_TAC LTE_TRANS) ‘SUC (SQRT N) ** 2’ >> art [] \\
     Q_TAC (TRANS_TAC LE_TRANS) ‘n’ >> art [] \\
     MATCH_MP_TAC EXP_LE >> simp [])
 >> Know ‘0 < z’
 >- (qunabbrev_tac ‘z’ \\
     MATCH_MP_TAC REAL_POW_LT >> art [])
 >> DISCH_TAC
 (* stage work *)
 >> Q.EXISTS_TAC ‘MAX 2 (2 * clg (ln z))’
 >> rw [MAX_LE]
 >> Know ‘0 < n’
 >- (Q_TAC (TRANS_TAC LTE_TRANS) ‘2’ >> simp [])
 >> DISCH_TAC
 >> ASSUME_TAC (Q.SPEC ‘ln z’ LE_NUM_CEILING)
 >> irule (iffLR LN_MONO_LT)
 >> simp [EXP_POS_LT, LN_MUL, LN_EXP]
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC REAL_LT_MUL >> simp [])
 >> Suff ‘ln z < &n - ln (&n)’ >- REAL_ARITH_TAC
 >> Q_TAC (TRANS_TAC REAL_LET_TRANS) ‘&clg (ln z)’ >> art []
 >> irule (iffLR REAL_LT_LMUL)
 >> Q.EXISTS_TAC ‘2’
 >> CONJ_TAC >- simp []
 >> Q_TAC (TRANS_TAC REAL_LET_TRANS) ‘&n’ >> simp [REAL_SUB_LDISTRIB]
 >> REWRITE_TAC [GSYM REAL_OF_NUM_MUL]
 >> Suff ‘2 * ln (&n) < (&n :real)’ >- REAL_ARITH_TAC
 >> Suff ‘ln (&n) < &n / (2 :real)’ >- simp []
 >> MATCH_MP_TAC LN_LT_HALF_X >> simp []
QED

(* NOTE: This (improper) integration can be split into two equal parts: [-inf,0]
   and [0,inf], each part has integral zero. FTC from Gauge integration gives us
   the integral for [0,&n].

   Then we need to further split the interval into [0,1] and [1,&n], because the
   function is negative in [0,1] and positive in [1,&n], where only the 2nd part
   needs the (Lebesgue) monotone convergence theorem to go to infinity.
 *)
Theorem integral_x_x_1_std_normal_density :
    integrable lborel (\x. Normal ((x pow 2 - 1) * std_normal_density x)) /\
    integral lborel (\x. Normal ((x pow 2 - 1) * std_normal_density x)) = 0
Proof
    qabbrev_tac ‘f = \x. (x pow 2 - 1) * std_normal_density x’ >> simp []
 >> Know ‘f IN borel_measurable borel’
 >- (qunabbrev_tac ‘f’ \\
     MATCH_MP_TAC in_borel_measurable_mul \\
     qexistsl_tac [‘\x. x pow 2 - 1’, ‘std_normal_density’] \\
     simp [space_borel, sigma_algebra_borel, in_measurable_borel_normal_density] \\
     MATCH_MP_TAC in_borel_measurable_sub \\
     qexistsl_tac [‘\x. x pow 2’, ‘\x. 1’] \\
     simp [space_borel, sigma_algebra_borel] \\
     reverse CONJ_TAC
     >- (MATCH_MP_TAC in_borel_measurable_const \\
         Q.EXISTS_TAC ‘1’ >> simp [sigma_algebra_borel]) \\
     MATCH_MP_TAC in_borel_measurable_pow2 \\
     Q.EXISTS_TAC ‘\x. x’ \\
     simp [space_borel, sigma_algebra_borel, in_borel_measurable_I])
 >> DISCH_TAC
 >> ‘(\x. Normal (f x)) = Normal o f’ by rw [FUN_EQ_THM, o_DEF] >> POP_ORW
 >> Know ‘Normal o f IN Borel_measurable borel’
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
     simp [sigma_algebra_borel])
 >> DISCH_TAC
 >> qabbrev_tac ‘s :real set = {y | 0 <= y}’
 >> qabbrev_tac ‘t :real set = {y | y < 0}’
 (* applying integral_add and integrable_add *)
 >> Suff ‘integrable lborel (\x. Normal (f x * indicator s x)) /\
          integrable lborel (\x. Normal (f x * indicator t x)) /\
          integral lborel (\x. Normal (f x * indicator s x)) = 0 /\
          integral lborel (\x. Normal (f x * indicator t x)) = 0’
 >- (qmatch_abbrev_tac ‘integrable lborel f1 /\ integrable lborel f2 /\ _ ==> _’ \\
     STRIP_TAC \\
     Know ‘Normal o f = (\x. f1 x + f2 x)’
     >- (rw [FUN_EQ_THM, Abbr ‘f1’, Abbr ‘f2’, extreal_add_eq] \\
         simp [Abbr ‘s’, Abbr ‘t’, indicator] \\
         Cases_on ‘0 <= x’ >> fs [REAL_NOT_LE] >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           ‘~(x < 0)’ by simp [REAL_NOT_LT] >> simp [],
           (* goal 2 (of 2) *)
           ‘~(0 <= x)’ by simp [REAL_NOT_LE] >> simp [] ]) >> Rewr' \\
     CONJ_TAC
     >- (MATCH_MP_TAC integrable_add \\
         simp [measure_space_lborel, space_lborel] \\
         rw [Abbr ‘f1’, Abbr ‘f2’]) \\
     Know ‘integral lborel (\x. f1 x + f2 x) =
           integral lborel f1 + integral lborel f2’
     >- (MATCH_MP_TAC integral_add \\
         simp [measure_space_lborel, space_lborel] \\
         rw [Abbr ‘f1’, Abbr ‘f2’]) >> Rewr' \\
     simp [])
 (* stage work *)
 >> qabbrev_tac ‘u :real set = {y | y <= 0}’
 >> Know ‘(\x. Normal (f x * indicator s x)) IN Borel_measurable borel’
 >- (‘(\x. Normal (f x * indicator s x)) =
      Normal o (\x. f x * indicator s x)’ by rw [FUN_EQ_THM, o_DEF] \\
     POP_ORW \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
     simp [sigma_algebra_borel] \\
     MATCH_MP_TAC in_borel_measurable_mul_indicator \\
     simp [sigma_algebra_borel, Abbr ‘s’, borel_measurable_sets])
 >> DISCH_TAC
 >> Know ‘(\x. Normal (f x * indicator u x)) IN Borel_measurable borel’
 >- (‘(\x. Normal (f x * indicator u x)) =
      Normal o (\x. f x * indicator u x)’ by rw [FUN_EQ_THM, o_DEF] \\
     POP_ORW \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
     simp [sigma_algebra_borel] \\
     MATCH_MP_TAC in_borel_measurable_mul_indicator \\
     simp [sigma_algebra_borel, Abbr ‘u’, borel_measurable_sets])
 >> DISCH_TAC
 >> Know ‘(\x. Normal (f x * indicator t x)) IN Borel_measurable borel’
 >- (‘(\x. Normal (f x * indicator t x)) =
      Normal o (\x. f x * indicator t x)’ by rw [FUN_EQ_THM, o_DEF] \\
     POP_ORW \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
     simp [sigma_algebra_borel] \\
     MATCH_MP_TAC in_borel_measurable_mul_indicator \\
     simp [sigma_algebra_borel, Abbr ‘t’, borel_measurable_sets])
 >> DISCH_TAC
 >> Know ‘integrable lborel (\x. Normal (f x * indicator t x)) <=>
          integrable lborel (\x. Normal (f x * indicator u x))’
 >- (MATCH_MP_TAC integrable_cong_AE_alt >> simp [lborel_def] \\
     rw [AE_DEF] \\
     Q.EXISTS_TAC ‘{0}’ \\
     simp [null_set_def, lborel_def, lambda_sing, sets_lborel,
           space_lborel, borel_measurable_sets] \\
     rpt STRIP_TAC >> DISJ2_TAC \\
     rw [Abbr ‘t’, Abbr ‘u’, indicator] >> fs [REAL_NOT_LE, REAL_NOT_LT] >|
     [ PROVE_TAC [REAL_LT_ANTISYM],
       PROVE_TAC [REAL_LE_ANTISYM] ])
 >> Rewr'
 >> Know ‘integral lborel (\x. Normal (f x * indicator t x)) =
          integral lborel (\x. Normal (f x * indicator u x))’
 >- (MATCH_MP_TAC integral_cong_AE >> simp [lborel_def] \\
     rw [AE_DEF] \\
     Q.EXISTS_TAC ‘{0}’ \\
     simp [null_set_def, lborel_def, lambda_sing, sets_lborel,
           space_lborel, borel_measurable_sets] \\
     rpt STRIP_TAC >> DISJ2_TAC \\
     rw [Abbr ‘t’, Abbr ‘u’, indicator] >> fs [REAL_NOT_LE, REAL_NOT_LT] >|
     [ PROVE_TAC [REAL_LT_ANTISYM],
       PROVE_TAC [REAL_LE_ANTISYM] ])
 >> Rewr'
 >> POP_ASSUM K_TAC
 >> qunabbrev_tac ‘t’
 (* applying integral_real_affine *)
 >> qabbrev_tac ‘g = \x. Normal (f x * indicator s x)’
 >> Suff ‘integrable lborel g /\ integral lborel g = 0’
 >- (simp [] >> STRIP_TAC \\
     MP_TAC (Q.SPECL [‘g’, ‘-1’, ‘0’] integral_real_affine) \\
     simp [Abbr ‘g’] \\
     Know ‘!x. indicator s (-x) = indicator u x’
     >- (rw [Abbr ‘s’, Abbr ‘u’, indicator]) >> Rewr' \\
     Know ‘!x. f (-x) = f x’
     >- (rw [Abbr ‘f’, std_normal_density_def]) >> Rewr' \\
     simp [])
 >> Q.PAT_X_ASSUM
   ‘(\x. Normal (f x * indicator u x)) IN Borel_measurable borel’ K_TAC
 >> qunabbrevl_tac [‘g’, ‘u’]
 (* stage work *)
 >> Know ‘s = interval [0,1] UNION {y | 1 < y}’
 >- (rw [Once EXTENSION, Abbr ‘s’, IN_INTERVAL] \\
     EQ_TAC >> rw [] >- PROVE_TAC [REAL_LET_TOTAL] \\
     MATCH_MP_TAC REAL_LT_IMP_LE \\
     Q_TAC (TRANS_TAC REAL_LET_TRANS) ‘1’ >> simp [])
 >> Rewr'
 >> qabbrev_tac ‘u = interval [0,1]’
 >> qabbrev_tac ‘t :real set = {y | 1 < y}’
 >> qabbrev_tac ‘f1 = \x. f x * indicator u x’
 >> Know ‘f1 absolutely_integrable_on univ(:real)’
 >- (simp [absolutely_integrable_on] \\
     Know ‘!x. abs (f1 x) = -f1 x’
     >- (Q.X_GEN_TAC ‘x’ \\
         MATCH_MP_TAC ABS_EQ_NEG' \\
         simp [Abbr ‘f1’, Abbr ‘u’, indicator, IN_INTERVAL] \\
         Cases_on ‘0 <= x /\ x <= 1’ >> rw [] \\
         rw [Abbr ‘f’, REAL_MUL_SIGN, normal_density_nonneg] \\
         DISJ2_TAC \\
         Suff ‘x pow 2 <= 1’ >- REAL_ARITH_TAC \\
        ‘(1 :real) = 1 pow 2’ by simp [] >> POP_ORW \\
         MATCH_MP_TAC POW_LE >> art []) >> Rewr' \\
     Suff ‘f1 integrable_on univ(:real)’
     >- (rw [] \\
         MATCH_MP_TAC INTEGRABLE_NEG >> art []) \\
     rw [integrable_on, Abbr ‘f1’, HAS_INTEGRAL_MUL_INDICATOR] \\
     simp [Abbr ‘f’, Abbr ‘u’] \\
     Q.EXISTS_TAC ‘0 * std_normal_density 0 -
                   1 * std_normal_density 1’ \\
     MATCH_MP_TAC has_integral_x_x_1_std_normal_density >> simp [])
 >> DISCH_TAC
 >> Know ‘f1 IN borel_measurable borel’
 >- (qunabbrev_tac ‘f1’ \\
     MATCH_MP_TAC in_borel_measurable_mul_indicator \\
     simp [sigma_algebra_borel, Abbr ‘u’, CLOSED_interval,
           borel_measurable_sets])
 >> DISCH_TAC
 >> ‘integrable lborel (Normal o f1) /\
     integral lborel (Normal o f1) = Normal (integral univ(:real) f1)’
      by PROVE_TAC [lebesgue_eq_gauge_integral_alt]
 >> Know ‘(f1 has_integral (0 * std_normal_density 0 -
                           1 * std_normal_density 1)) UNIV’
 >- (SIMP_TAC std_ss [Abbr ‘f1’, Abbr ‘f’, Abbr ‘u’,
                      HAS_INTEGRAL_MUL_INDICATOR] \\
     MATCH_MP_TAC has_integral_x_x_1_std_normal_density >> simp [])
 >> qabbrev_tac ‘c = 1 * std_normal_density 1’
 >> simp [HAS_INTEGRAL_INTEGRABLE_INTEGRAL]
 >> STRIP_TAC
 >> POP_ASSUM (FULL_SIMP_TAC std_ss o wrap)
 (* stage work *)
 >> qabbrev_tac ‘f2 = \x. f x * indicator t x’
 >> Suff ‘integrable lborel (Normal o f2) /\
          integral lborel (Normal o f2) = Normal c’
 >- (STRIP_TAC \\
     Know ‘!x. f x * indicator (u UNION t) x = f1 x + f2 x’
     >- (rw [FUN_EQ_THM, Abbr ‘f1’, Abbr ‘f2’] \\
         simp [Abbr ‘u’, Abbr ‘t’, indicator, IN_INTERVAL] \\
         Cases_on ‘1 < x’ >> simp [] \\
        ‘~(x <= 1)’ by simp [REAL_NOT_LE] \\
         simp []) >> Rewr' \\
     simp [GSYM extreal_add_eq] \\
    ‘!x. Normal (f1 x) + Normal (f2 x) =
        (Normal o f1) x + (Normal o f2) x’ by rw [FUN_EQ_THM, o_DEF] >> POP_ORW \\
     CONJ_TAC
     >- (MATCH_MP_TAC integrable_add \\
         simp [measure_space_lborel, space_lborel]) \\
     Know ‘integral lborel (\x. (Normal o f1) x + (Normal o f2) x) =
           integral lborel (Normal o f1) + integral lborel (Normal o f2)’
     >- (MATCH_MP_TAC integral_add \\
         simp [measure_space_lborel, space_lborel]) >> Rewr' \\
     simp [extreal_add_eq, extreal_of_num_def])
 >> Q.PAT_X_ASSUM
   ‘(\x. Normal (f x * indicator s x)) IN Borel_measurable borel’ K_TAC
 >> qunabbrev_tac ‘s’
 >> qabbrev_tac ‘s :real set = {y | 1 <= y}’
 >> qabbrev_tac ‘f3 = \x. f x * indicator s x’
 >> Know ‘f3 IN borel_measurable borel’
 >- (qunabbrev_tac ‘f3’ \\
     MATCH_MP_TAC in_borel_measurable_mul_indicator \\
     simp [sigma_algebra_borel, Abbr ‘s’, borel_measurable_sets])
 >> DISCH_TAC
 >> Know ‘f2 IN borel_measurable borel’
 >- (qunabbrev_tac ‘f2’ \\
     MATCH_MP_TAC in_borel_measurable_mul_indicator \\
     simp [sigma_algebra_borel, Abbr ‘t’, borel_measurable_sets])
 >> DISCH_TAC
 >> Know ‘Normal o f2 IN Borel_measurable borel’
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
     simp [sigma_algebra_borel])
 >> DISCH_TAC
 >> Know ‘Normal o f3 IN Borel_measurable borel’
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
     simp [sigma_algebra_borel])
 >> DISCH_TAC
 >> Know ‘integrable lborel (Normal o f2) <=>
          integrable lborel (Normal o f3)’
 >- (MATCH_MP_TAC integrable_cong_AE_alt >> simp [lborel_def] \\
     rw [AE_DEF] \\
     Q.EXISTS_TAC ‘{1}’ \\
     simp [null_set_def, lborel_def, lambda_sing, sets_lborel,
           space_lborel, borel_measurable_sets] \\
     rw [Abbr ‘f2’, Abbr ‘f3’] >> DISJ2_TAC \\
     rw [Abbr ‘t’, Abbr ‘s’, indicator] >> fs [REAL_NOT_LE, REAL_NOT_LT] >|
     [ PROVE_TAC [REAL_LT_ANTISYM],
       PROVE_TAC [REAL_LE_ANTISYM] ])
 >> Rewr'
 >> Know ‘integral lborel (Normal o f2) =
          integral lborel (Normal o f3)’
 >- (MATCH_MP_TAC integral_cong_AE >> simp [lborel_def] \\
     rw [AE_DEF] \\
     Q.EXISTS_TAC ‘{1}’ \\
     simp [null_set_def, lborel_def, lambda_sing, sets_lborel,
           space_lborel, borel_measurable_sets] \\
     rw [Abbr ‘f2’, Abbr ‘f3’] >> DISJ2_TAC \\
     rw [Abbr ‘t’, Abbr ‘s’, indicator] >> fs [REAL_NOT_LE, REAL_NOT_LT] >|
     [ PROVE_TAC [REAL_LT_ANTISYM],
       PROVE_TAC [REAL_LE_ANTISYM] ])
 >> Rewr'
 (* preparing for lebesgue_monotone_convergence *)
 >> qabbrev_tac ‘h = \n x. f x * indicator (interval [1,&SUC n]) x’
 >> Know ‘!n. h n IN borel_measurable borel’
 >- (rw [Abbr ‘h’] \\
     MATCH_MP_TAC in_borel_measurable_mul_indicator \\
     simp [interval, borel_measurable_sets, sigma_algebra_borel])
 >> DISCH_TAC
 >> Know ‘!n. Normal o h n IN Borel_measurable borel’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
     simp [sigma_algebra_borel])
 >> DISCH_TAC
 >> Know ‘!n x. 0 <= h n x’
 >- (rw [Abbr ‘h’, indicator, Abbr ‘f’, IN_INTERVAL] \\
     MATCH_MP_TAC REAL_LE_MUL \\
     simp [normal_density_nonneg, REAL_SUB_LE] \\
    ‘(1 :real) = 1 pow 2’ by simp [] >> POP_ORW \\
     MATCH_MP_TAC POW_LE >> simp [])
 >> DISCH_TAC
 >> Know ‘!x. 1 <= x ==> 0 <= f x’
 >- (rw [Abbr ‘f’] \\
     MATCH_MP_TAC REAL_LE_MUL \\
     simp [normal_density_nonneg, REAL_SUB_LE] \\
    ‘(1 :real) = 1 pow 2’ by simp [] >> POP_ORW \\
     MATCH_MP_TAC POW_LE >> simp [])
 >> DISCH_TAC
 >> Know ‘!x. 0 <= f3 x’
 >- (rw [Abbr ‘f3’, Abbr ‘s’, IN_INTERVAL] \\
     Cases_on ‘1 <= x’ >> rw [indicator])
 >> DISCH_TAC
 >> Know ‘       integral lborel (Normal o f3) =
          pos_fn_integral lborel (Normal o f3)’
 >- (MATCH_MP_TAC integral_pos_fn \\
     rw [space_lborel, measure_space_lborel, extreal_of_num_def, o_DEF])
 >> Rewr'
 (* integrable is implied by finite pos_fn_integral *)
 >> Suff ‘pos_fn_integral lborel (Normal o f3) = Normal c’
 >- (RW_TAC std_ss [] \\
     MP_TAC (ISPECL [“lborel”, “Normal o (f3 :real -> real)”] integrable_pos) \\
     simp [extreal_of_num_def, lborel_def])
 (* applying lebesgue_monotone_convergence *)
 >> Know ‘pos_fn_integral lborel (Normal o f3) =
          sup (IMAGE (\i. pos_fn_integral lborel (Normal o h i)) UNIV)’
 >- (HO_MATCH_MP_TAC lebesgue_monotone_convergence \\
     simp [space_lborel, lborel_def] \\
     CONJ_TAC (* mono_increasing *)
     >- (Q.X_GEN_TAC ‘x’ \\
         simp [ext_mono_increasing_def] \\
         qx_genl_tac [‘i’, ‘j’] >> rw [Abbr ‘h’] \\
         reverse (Cases_on ‘1 <= x’) >- rw [indicator, IN_INTERVAL] \\
         MATCH_MP_TAC REAL_LE_LMUL_IMP >> simp [] \\
         MATCH_MP_TAC INDICATOR_MONO \\
         rw [SUBSET_DEF, IN_INTERVAL] >> rename1 ‘y <= &SUC i’ \\
         Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘&SUC i’ >> simp []) \\
     Q.X_GEN_TAC ‘x’ \\
     rw [sup_eq']
     >- (simp [Abbr ‘h’, Abbr ‘f3’] \\
         reverse (Cases_on ‘1 <= x’) >- simp [Abbr ‘s’, indicator, IN_INTERVAL] \\
         MATCH_MP_TAC REAL_LE_LMUL_IMP >> simp [] \\
         MATCH_MP_TAC INDICATOR_MONO \\
         rw [SUBSET_DEF, IN_INTERVAL, Abbr ‘s’]) \\
     Know ‘!i. Normal (h i x) <= y’
     >- (Q.X_GEN_TAC ‘i’ \\
         POP_ASSUM MATCH_MP_TAC \\
         Q.EXISTS_TAC ‘i’ >> REFL_TAC) >> DISCH_TAC \\
     rw [Abbr ‘f3’] \\
     reverse (Cases_on ‘1 <= x’)
     >- (Q.PAT_X_ASSUM ‘!i. Normal (h i x) <= y’ (MP_TAC o Q.SPEC ‘0’) \\
         rw [Abbr ‘s’, indicator, Abbr ‘h’, IN_INTERVAL]) \\
     STRIP_ASSUME_TAC (Q.SPEC ‘x’ SIMP_REAL_ARCH) \\
     Q_TAC (TRANS_TAC le_trans) ‘Normal (h n x)’ >> art [] \\
     simp [Abbr ‘h’] \\
     MATCH_MP_TAC REAL_LE_LMUL_IMP >> simp [] \\
     simp [Abbr ‘s’, indicator, IN_INTERVAL] \\
     Suff ‘x <= &SUC n’ >- simp [] \\
     Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘&n’ >> simp [])
 >> Rewr'
 (* applying has_integral_x_x_1_std_normal_density *)
 >> Know ‘!n. (h n has_integral (1 * std_normal_density 1 -
                                 &SUC n * std_normal_density (&SUC n))) UNIV’
 >- (RW_TAC std_ss [Abbr ‘h’, HAS_INTEGRAL_MUL_INDICATOR, Abbr ‘f’, Abbr ‘c’] \\
     MATCH_MP_TAC has_integral_x_x_1_std_normal_density \\
     simp [])
 >> rw [HAS_INTEGRAL_INTEGRABLE_INTEGRAL, FORALL_AND_THM]
 (* applying lebesgue_eq_gauge_integral_positive_alt *)
 >> Know ‘!n. pos_fn_integral lborel (Normal o h n) =
              Normal (integral univ(:real) (h n))’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC lebesgue_eq_gauge_integral_positive_alt >> art [])
 >> Rewr'
 >> POP_ORW
 >> qabbrev_tac ‘J = \n. c - &SUC n * std_normal_density (&SUC n)’
 >> simp []
 (* preparing for sup_image_normal (necessary?) *)
 >> Know ‘IMAGE (\i. Normal (J i)) UNIV = IMAGE Normal {J i | i | T}’
 >- (rw [Once EXTENSION] \\
     EQ_TAC >> rw [] >> (Q.EXISTS_TAC ‘i’ >> REFL_TAC))
 >> Rewr'
 >> qmatch_abbrev_tac ‘sup (IMAGE Normal p) = Normal c’
 >> ‘p <> {}’ by simp [Abbr ‘p’, Once EXTENSION]
 >> Know ‘bounded p’
 >- (rw [Abbr ‘p’, bounded_def] \\
     Q.EXISTS_TAC ‘c’ >> rw [Abbr ‘J’] \\
     Know ‘abs (c - &SUC i * std_normal_density (&SUC i)) =
                c - &SUC i * std_normal_density (&SUC i)’
     >- (simp [ABS_REFL, REAL_SUB_LE] \\
         qunabbrev_tac ‘c’ \\
         MATCH_MP_TAC x_std_normal_density_decreasing >> simp []) >> Rewr' \\
     Suff ‘0 <= &SUC i * std_normal_density (&SUC i)’ >- REAL_ARITH_TAC \\
     MATCH_MP_TAC REAL_LE_MUL \\
     simp [normal_density_nonneg])
 >> DISCH_TAC
 (* applying sup_image_normal *)
 >> ‘sup (IMAGE Normal p) = Normal (sup p)’ by PROVE_TAC [sup_image_normal]
 >> POP_ORW
 >> REWRITE_TAC [extreal_11]
 (* applying mono_increasing_converges_to_sup *)
 >> ‘p = IMAGE J UNIV’ by rw [Once EXTENSION, Abbr ‘p’]
 >> POP_ASSUM (fs o wrap) >> T_TAC
 >> qunabbrev_tac ‘p’
 >> Suff ‘J --> c’
 >- (DISCH_TAC \\
     SYM_TAC >> MATCH_MP_TAC mono_increasing_converges_to_sup >> art [] \\
     simp [mono_increasing_def, Abbr ‘J’] \\
     qx_genl_tac [‘i’, ‘j’] >> DISCH_TAC \\
     simp [REAL_LE_SUB_CANCEL1] \\
     MATCH_MP_TAC x_std_normal_density_decreasing >> simp [])
 >> Suff ‘(\n. &SUC n * std_normal_density (&SUC n)) --> 0’
 >- (qmatch_abbrev_tac ‘g --> 0 ==> _’ \\
     DISCH_TAC \\
     MP_TAC (Q.SPECL [‘\x. c’, ‘c’, ‘g’, ‘0’] SEQ_SUB) \\
     simp [SEQ_CONST, Abbr ‘g’, ETA_AX])
 >> simp [GSYM SEQ_SUC]
 >> simp [GSYM LIM_SEQUENTIALLY_SEQ, lim_sequentially_n_std_normal_density]
QED

Theorem integral_x_x_std_normal_density :
    !p X. prob_space p /\ std_normal_rv X p ==>
          integrable lborel (\x. Normal (x pow 2 * std_normal_density x)) /\
          integral lborel (\x. Normal (x pow 2 * std_normal_density x)) = 1
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘!(x :real). x pow 2 = x pow 2 - 1 + 1’ by simp [REAL_SUB_ADD]
 >> POP_ORW
 >> simp [REAL_ADD_RDISTRIB, GSYM extreal_add_eq]
 >> STRIP_ASSUME_TAC integral_x_x_1_std_normal_density
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘0’, ‘1’] integral_normal_density)
 >> simp [] >> STRIP_TAC
 >> Know ‘integral lborel
             (\x. Normal ((x pow 2 - 1) * std_normal_density x) +
                  Normal_density 0 1 x) =
          integral lborel (\x. Normal ((x pow 2 - 1) * std_normal_density x)) +
          integral lborel (\x. Normal_density 0 1 x)’
 >- (HO_MATCH_MP_TAC integral_add \\
     simp [lborel_def, space_lborel])
 >> Rewr'
 >> simp []
 >> HO_MATCH_MP_TAC integrable_add
 >> simp [lborel_def, space_lborel]
QED

Theorem variance_of_std_normal_rv :
    !p X. prob_space p /\ std_normal_rv X p ==>
          variance p (Normal o X) = 1
Proof
    rw [variance_alt]
 >> ‘expectation p (Normal o X) = 0’ by PROVE_TAC [expectation_of_std_normal_rv]
 >> POP_ORW
 >> simp [expectation_def, extreal_pow_eq]
 >> Know ‘(\x. x pow 2) IN borel_measurable borel’
 >- (MATCH_MP_TAC in_borel_measurable_pow2 \\
     Q.EXISTS_TAC ‘\x. x’ \\
     simp [sigma_algebra_borel, in_borel_measurable_I])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘0’, ‘1’, ‘\x. x pow 2’] integration_of_normal_rv)
 >> simp [o_DEF]
 >> DISCH_THEN K_TAC
 >> MATCH_MP_TAC (cj 2 integral_x_x_std_normal_density)
 >> qexistsl_tac [‘p’, ‘X’] >> art []
QED

(* NOTE: This proof is based on variance_cmul, variance_real_affine, etc. *)
Theorem variance_of_normal_rv :
    !p X mu sig. prob_space p /\ normal_rv X p mu sig /\ 0 < sig ==>
                 variance p (Normal o X) = Normal (sig pow 2)
Proof
    rpt STRIP_TAC
 >> ‘sig <> 0’ by PROVE_TAC [REAL_LT_IMP_NE]
 >> qabbrev_tac ‘Y = \x. -inv sig * mu + inv sig * X x’
 >> Know ‘std_normal_rv Y p’
 >- (MP_TAC (Q.SPECL [‘X’, ‘p’, ‘mu’, ‘sig’, ‘Y’,
                      ‘inv sig’ (* a *), ‘-inv sig * mu’ (* b *)]
                     normal_rv_affine') >> simp [] \\
     simp [REAL_ADD_LINV, REAL_MUL_LNEG] \\
     qabbrev_tac ‘c = inv sig’ \\
    ‘0 < c’ by simp [Abbr ‘c’, REAL_INV_POS] \\
    ‘abs c = c’ by simp [ABS_REFL, REAL_LT_IMP_LE] >> POP_ORW \\
     simp [Abbr ‘c’, REAL_MUL_LINV])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘Y’] variance_of_std_normal_rv) >> rw []
 >> ‘integrable p (Normal o Y)’ by PROVE_TAC [expectation_of_std_normal_rv]
 >> Know ‘real_random_variable (Normal o Y) p’
 >- (simp [real_random_variable_equiv] >> fs [normal_rv])
 >> DISCH_TAC
 >> qabbrev_tac ‘Z = \x. inv sig * X x’ (* b + a * X x *)
 >> Know ‘normal_rv Z p (inv sig * mu) 1’
 >- (MP_TAC (Q.SPECL [‘X’, ‘p’, ‘mu’, ‘sig’, ‘Z’,
                      ‘inv sig’ (* a *), ‘0’ (* b *)]
                     normal_rv_affine') >> simp [] \\
     qabbrev_tac ‘c = inv sig’ \\
    ‘0 < c’ by simp [Abbr ‘c’, REAL_INV_POS] \\
    ‘abs c = c’ by simp [ABS_REFL, REAL_LT_IMP_LE] >> POP_ORW \\
     simp [Abbr ‘c’, REAL_MUL_LINV])
 >> DISCH_TAC
 >> Know ‘Normal o Z = \x. (Normal o Y) x + Normal (inv sig * mu)’
 >- (rw [FUN_EQ_THM, o_DEF, Abbr ‘Z’, Abbr ‘Y’, extreal_add_eq] \\
     simp [REAL_ADD_LDISTRIB] >> REAL_ARITH_TAC)
 >> DISCH_TAC
 >> Know ‘variance p (Normal o Z) = variance p (Normal o Y)’
 >- (POP_ORW \\
     MATCH_MP_TAC variance_real_affine >> simp [])
 >> DISCH_TAC
 >> Know ‘integrable p (Normal o Z)’
 >- (MATCH_MP_TAC (cj 1 expectation_of_normal_rv) \\
     qexistsl_tac [‘inv sig * mu’, ‘1’] >> simp [])
 >> DISCH_TAC
 >> Know ‘real_random_variable (Normal o Z) p’
 >- (simp [real_random_variable_equiv] >> fs [normal_rv])
 >> DISCH_TAC
 >> Know ‘finite_second_moments p (Normal o Z)’
 >- simp [finite_second_moments_eq_finite_variance, lt_infty]
 >> DISCH_TAC
 >> Know ‘Normal o X = \x. Normal sig * (Normal o Z) x’
 >- rw [FUN_EQ_THM, o_DEF, Abbr ‘Z’, extreal_mul_eq]
 >> DISCH_TAC
 >> Know ‘variance p (Normal o X) = Normal (sig pow 2) * variance p (Normal o Z)’
 >- (POP_ORW \\
     MATCH_MP_TAC variance_cmul >> art [])
 >> Rewr'
 >> simp []
QED

(* ------------------------------------------------------------------------- *)
(*  Weak convergence and its relation with convergence in distribution       *)
(* ------------------------------------------------------------------------- *)

Overload B[local] = “general_borel”
Overload B[local] = “\E. general_borel (mtop E)”

Definition weak_convergence_condition_def :
    weak_convergence_condition (top :'a topology) X Y f <=>
    ((\n. integral (space (B top),subsets (B top),X n) (Normal o f)) -->
          integral (space (B top),subsets (B top),Y  ) (Normal o f)) sequentially
End

(* Definition 13.12 [8, p.281] *)
Definition weak_converge_in_topology_def :
    weak_converge_in_topology (top :'a topology) X Y <=>
    !f. f IN bounded_continuous top ==> weak_convergence_condition top X Y f
End

(* |- !top X Y.
        weak_converge_in_topology top X Y <=>
        !f. f IN C_b top ==>
            ((\n. integral (space (B top),subsets (B top),X n) (Normal o f)) -->
             integral (space (B top),subsets (B top),Y) (Normal o f))
              sequentially
 *)
Theorem weak_converge_in_topology = weak_converge_in_topology_def
     |> REWRITE_RULE [weak_convergence_condition_def]

Definition weak_converge :
    weak_converge X Y = weak_converge_in_topology ext_euclidean X Y
End
Overload "-->" = “weak_converge”

(* |- !X Y.
        weak_converge X Y <=>
        !f. f IN C_b ext_euclidean ==>
            ((\n. integral (space Borel,subsets Borel,X n) (Normal o f)) -->
             integral (space Borel,subsets Borel,Y) (Normal o f))
              sequentially
 *)
Theorem weak_converge_def =
        weak_converge
     |> REWRITE_RULE [weak_converge_in_topology, GSYM Borel_alt_general]

(* NOTE: "convergence of r.v. in distribution" is equivalent to "weak convergence
   of their distribution functions".
 *)
Theorem converge_in_dist_alt_weak_converge :
    !p X Y. prob_space p /\
           (!n. random_variable (X n) p Borel) /\ random_variable Y p Borel ==>
           ((X --> Y) (in_distribution p) <=>
            (\n. distribution p (X n)) --> distribution p Y)
Proof
    rw [converge_in_dist_def, weak_converge_def, expectation_def, distribution_distr,
        random_variable_def, prob_space_def, p_space_def, events_def]
 >> EQ_TAC >> rw []
 >| [ (* goal 1 (of 2) *)
      qabbrev_tac ‘g = Normal o f’ \\
      Know ‘!n. integral (space Borel,subsets Borel,distr p (X n)) g =
                integral p (g o X n)’
      >- (Q.X_GEN_TAC ‘n’ \\
          MATCH_MP_TAC (cj 1 integral_distr) \\
          simp [SIGMA_ALGEBRA_BOREL, Abbr ‘g’] \\
          MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
          simp [SIGMA_ALGEBRA_BOREL] \\
          fs [IN_bounded_continuous] \\
          simp [borel_alt_general, Borel_alt_general] \\
          MATCH_MP_TAC IN_MEASURABLE_CONTINUOUS_MAP >> art []) >> Rewr' \\
     Know ‘!n. integral (space Borel,subsets Borel,distr p Y) g = integral p (g o Y)’
     >- (MATCH_MP_TAC (cj 1 integral_distr) \\
         simp [SIGMA_ALGEBRA_BOREL, Abbr ‘g’] \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
         simp [SIGMA_ALGEBRA_BOREL] \\
         fs [IN_bounded_continuous] \\
         simp [borel_alt_general, Borel_alt_general] \\
         MATCH_MP_TAC IN_MEASURABLE_CONTINUOUS_MAP >> art []) >> Rewr' \\
     simp [Abbr ‘g’],
     (* goal 2 (of 2) *)
     qabbrev_tac ‘g = Normal o f’ \\
    ‘!n. Normal o f o X n = g o X n’ by METIS_TAC [o_ASSOC] >> POP_ORW \\
    ‘Normal o f o Y = g o Y’ by METIS_TAC [o_ASSOC] >> POP_ORW \\
     Q.PAT_X_ASSUM ‘!g. g IN C_b ext_euclidean ==> _’ (MP_TAC o Q.SPEC ‘f’) \\
     simp [] \\
     Know ‘!n. integral (space Borel,subsets Borel,distr p (X n)) g =
               integral p (g o X n)’
     >- (Q.X_GEN_TAC ‘n’ \\
         MATCH_MP_TAC (cj 1 integral_distr) \\
         simp [SIGMA_ALGEBRA_BOREL, Abbr ‘g’] \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
         simp [SIGMA_ALGEBRA_BOREL] \\
         fs [IN_bounded_continuous] \\
         simp [borel_alt_general, Borel_alt_general] \\
         MATCH_MP_TAC IN_MEASURABLE_CONTINUOUS_MAP >> art []) >> Rewr' \\
     Know ‘integral (space Borel,subsets Borel,distr p Y) g = integral p (g o Y)’
     >- (MATCH_MP_TAC (cj 1 integral_distr) \\
         simp [SIGMA_ALGEBRA_BOREL, Abbr ‘g’] \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
         simp [SIGMA_ALGEBRA_BOREL] \\
         fs [IN_bounded_continuous] \\
         simp [borel_alt_general, Borel_alt_general] \\
         MATCH_MP_TAC IN_MEASURABLE_CONTINUOUS_MAP >> art []) >> Rewr ]
QED

Theorem converge_in_dist_alt_continuous_on :
    !X Y p. prob_space p /\ (!n. real_random_variable (X n) p) /\
            real_random_variable Y p ==>
           ((X --> Y) (in_distribution p) <=>
            !f. bounded (IMAGE f UNIV) /\ f continuous_on UNIV ==>
               ((\n. expectation p (Normal o f o real o X n)) -->
                expectation p (Normal o f o real o Y)) sequentially)
Proof
    rw [real_random_variable_def, converge_in_dist_def, FORALL_AND_THM]
 >> reverse EQ_TAC >> rpt STRIP_TAC
 (* old to new *)
 >- (FULL_SIMP_TAC std_ss [IN_bounded_continuous] \\
     qabbrev_tac ‘g = f o Normal’ \\
     Know ‘!n. expectation p (Normal o f o X n) =
               expectation p (Normal o g o real o X n)’
     >- (Q.X_GEN_TAC ‘n’ \\
         MATCH_MP_TAC expectation_cong >> rw [o_DEF, Abbr ‘g’] \\
         AP_TERM_TAC >> simp [normal_real]) >> Rewr' \\
     Know ‘expectation p (Normal o f o Y) =
           expectation p (Normal o g o real o Y)’
     >- (MATCH_MP_TAC expectation_cong >> rw [o_DEF, Abbr ‘g’] \\
         AP_TERM_TAC >> simp [normal_real]) >> Rewr' \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     CONJ_TAC
     >- (fs [bounded_def, Abbr ‘g’] \\
         Q.EXISTS_TAC ‘a’ \\
         Q.X_GEN_TAC ‘z’ \\
         DISCH_THEN (Q.X_CHOOSE_THEN ‘x’ STRIP_ASSUME_TAC) \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art [] \\
         Q.EXISTS_TAC ‘Normal x’ >> simp []) \\
     simp [continuous_on_univ_alt_continuous_map, Abbr ‘g’] \\
     MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE \\
     Q.EXISTS_TAC ‘ext_euclidean’ >> simp [continuous_map_normal])
 (* new to old *)
 >> qabbrev_tac ‘g = f o real’
 >> ‘!n. Normal o f o real o X n = Normal o g o X n’
       by rw [Abbr ‘g’, GSYM o_ASSOC] >> POP_ORW
 >> ‘Normal o f o real o Y = Normal o g o Y’
       by rw [Abbr ‘g’, GSYM o_ASSOC] >> POP_ORW
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> simp [Abbr ‘g’, IN_bounded_continuous, o_DEF]
 >> reverse CONJ_TAC
 >- (fs [bounded_def] \\
     Q.EXISTS_TAC ‘a’ \\
     Q.X_GEN_TAC ‘z’ \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘x’ MP_TAC) >> rw [] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘real x’ >> REWRITE_TAC [])
 >> ‘(\x. f (real x)) = f o real’ by rw [o_DEF, FUN_EQ_THM] >> POP_ORW
 >> MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE
 >> Q.EXISTS_TAC ‘euclidean’
 >> fs [continuous_on_univ_alt_continuous_map, continuous_map_real]
QED

Definition BL_def :
    BL E = {f :'a -> real | f IN bounded_continuous (mtop E) /\
                            Lipschitz_continuous_map (E,mr1) f}
End

Theorem Lipschitz_continuous_map_rewrite[local] :
    !E f. f IN C_b (mtop E) /\ Lipschitz_continuous_map (E,mr1) f <=>
          bounded (IMAGE f UNIV) /\ Lipschitz_continuous_map (E,mr1) f
Proof
    rw [IN_APP, bounded_continuous_def, euclidean_def]
 >> METIS_TAC [Lipschitz_continuous_map_imp_continuous_map]
QED

(* NOTE: “Lipschitz_continuous_map” implies the part “continuous_map” in “C_b” *)
Theorem BL_alt :
    !E. BL E = {f | bounded (IMAGE f UNIV) /\ Lipschitz_continuous_map (E,mr1) f}
Proof
    rw [Once EXTENSION, BL_def, Lipschitz_continuous_map_rewrite]
QED

Definition subprobability_measure_def : (* aka s.p.m. *)
    subprobability_measure m <=> measure_space m /\ measure m (m_space m) <= 1
End

Theorem subprobability_measure_alt :
    !m. subprobability_measure m <=>
        measure_space m /\ !s. s IN measurable_sets m ==> measure m s <= 1
Proof
    RW_TAC std_ss [subprobability_measure_def, GSYM CONJ_ASSOC]
 >> reverse EQ_TAC >> rw []
 >- (FIRST_X_ASSUM MATCH_MP_TAC \\
     MATCH_MP_TAC MEASURE_SPACE_SPACE >> art [])
 >> Q_TAC (TRANS_TAC le_trans) ‘measure m (m_space m)’ >> art []
 >> Know ‘increasing m’ >- rw [MEASURE_SPACE_INCREASING]
 >> rw [increasing_def]
 >> POP_ASSUM MATCH_MP_TAC >> art []
 >> CONJ_TAC
 >- (MATCH_MP_TAC MEASURE_SPACE_SPACE >> art [])
 >> MATCH_MP_TAC MEASURABLE_SETS_SUBSET_SPACE >> art []
QED

Theorem subprobability_measure_imp_finite :
    !m. subprobability_measure m ==> finite_measure_space m
Proof
    rw [subprobability_measure_def, finite_measure_space_def, lt_infty]
 >> Q_TAC (TRANS_TAC let_trans) ‘1’ >> rw []
QED

Theorem prob_space_imp_subprobability_measure :
    !p. prob_space p ==> subprobability_measure p
Proof
    rw [prob_space_def, subprobability_measure_def]
QED

(* Theorem 13.16 (Portemanteau) [8, p.283]

  "In the following theorem, a whole bunch of such statements will be hung on
   a coat hanger (French: portemanteau)."
 *)
Definition Portemanteau_antecedents_def :
    Portemanteau_antecedents E X Y <=>
   (!n. subprobability_measure (space (B E),subsets (B E),X n)) /\
    subprobability_measure (space (B E),subsets (B E),Y)
End

Definition Portemanteau_i_def :
    Portemanteau_i E X Y <=> weak_converge_in_topology (mtop E) X Y
End

Definition Portemanteau_ii_def :
    Portemanteau_ii E X Y <=>
    !f. f IN BL E ==> weak_convergence_condition (mtop E) X Y f
End

(* trivial *)
Theorem Portemanteau_i_imp_ii :
    !E X Y. Portemanteau_i E X Y ==> Portemanteau_ii E X Y
Proof
    rw [Portemanteau_i_def, weak_converge_in_topology_def,
        Portemanteau_ii_def, BL_def, IN_APP]
QED

(* NOTE: This concept really belongs to real_topologyTheory *)
Definition points_of_discontinuity_def :
    points_of_discontinuity top (f :'a -> real) =
      {x | x IN topspace top /\ ~topcontinuous_at top euclidean f x}
End

Overload U[local] = “points_of_discontinuity”
val U_DEF = points_of_discontinuity_def;

(* NOTE: This proof is from https://math.stackexchange.com/questions/211511 *)
Theorem points_of_discontinuity_in_general_borel :
    !(t :'a topology) f. U t f IN subsets (B t)
Proof
    rw [U_DEF]
 >> ‘sigma_algebra (B t)’ by PROVE_TAC [sigma_algebra_general_borel]
 >> qmatch_abbrev_tac ‘s IN subsets (B t)’
 >> Know ‘s = space (B t) DIFF
              {x | x IN topspace t /\ topcontinuous_at t euclidean f x}’
 >- (rw [Abbr ‘s’, Once EXTENSION, space_general_borel] \\
     EQ_TAC >> rw [])
 >> Rewr'
 >> MATCH_MP_TAC SIGMA_ALGEBRA_COMPL >> art []
 >> simp [Abbr ‘s’, topcontinuous_at, TOPSPACE_EUCLIDEAN, CONJ_ASSOC]
 >> simp [GSYM CONJ_ASSOC, GSYM euclidean_open_def]
 >> qmatch_abbrev_tac ‘s IN subsets (B t)’
 >> Know ‘s = {x | x IN topspace t /\
                   !n. ?u. open_in t u /\ x IN u /\
                           !y z. y IN u /\ z IN u ==> dist (f y,f z) < inv (&SUC n)}’
 >- (RW_TAC set_ss [Abbr ‘s’, Once EXTENSION] \\
     EQ_TAC >> RW_TAC std_ss []
     >- (POP_ASSUM (MP_TAC o Q.SPEC ‘ball (f x,inv (&SUC n) / 2)’) \\
         RW_TAC real_ss [OPEN_BALL, IN_BALL, DIST_REFL] \\
         Q.EXISTS_TAC ‘u’ >> RW_TAC real_ss [] \\
         Q_TAC (TRANS_TAC REAL_LET_TRANS) ‘dist (f y,f x) + dist (f x,f z)’ \\
         qabbrev_tac ‘r :real = inv (&SUC n)’ \\
         REWRITE_TAC [DIST_TRIANGLE] \\
         simp [Once DIST_SYM] \\
        ‘r = r / 2 + r / 2’ by rw [REAL_HALF_DOUBLE] >> POP_ORW \\
         MATCH_MP_TAC REAL_LT_ADD2 >> simp []) \\
     FULL_SIMP_TAC std_ss [OPEN_CONTAINS_BALL] \\
     Q.PAT_X_ASSUM ‘!x. x IN v ==> _’ (MP_TAC o Q.SPEC ‘f x’) >> rw [] \\
     MP_TAC (Q.SPEC ‘e’ REAL_ARCH_INV_SUC) \\
     RW_TAC std_ss [] \\
     qabbrev_tac ‘r :real = inv (&SUC n)’ \\
     Q.PAT_X_ASSUM ‘!n. ?u. _’ (MP_TAC o Q.SPEC ‘n’) \\
     RW_TAC std_ss [] \\
     Q.EXISTS_TAC ‘u’ >> rw [] \\
     Suff ‘f y IN ball (f x,e)’ >- METIS_TAC [SUBSET_DEF] \\
     rw [IN_BALL] \\
     Q_TAC (TRANS_TAC REAL_LT_TRANS) ‘r’ >> art [] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> Rewr'
 >> qunabbrev_tac ‘s’
 (* stage work *)
 >> qmatch_abbrev_tac ‘s IN subsets (B t)’
 >> qabbrev_tac
   ‘A = \n. {x | x IN topspace t /\
                 ?u. open_in t u /\ x IN u /\
                     !y z. y IN u /\ z IN u ==> dist (f y,f z) < inv (&SUC n)}’
 >> Know ‘s = BIGINTER (IMAGE A UNIV)’
 >- (RW_TAC set_ss [Once EXTENSION, IN_BIGINTER_IMAGE, Abbr ‘s’, Abbr ‘A’] \\
     EQ_TAC >> RW_TAC std_ss [])
 >> Rewr'
 >> qunabbrev_tac ‘s’
 >> irule (cj 4 SIGMA_ALGEBRA_FN_BIGINTER)
 >> simp [IN_FUNSET]
 >> Q.X_GEN_TAC ‘n’
 >> MATCH_MP_TAC open_in_general_borel
 >> Q.PAT_X_ASSUM ‘sigma_algebra (B t)’ K_TAC
 (* stage work *)
 >> RW_TAC set_ss [Once OPEN_NEIGH', Abbr ‘A’, SUBSET_DEF]
 >> qabbrev_tac ‘r :real = inv (&SUC n)’
 (* stage work *)
 >> ‘0 < r’ by rw [Abbr ‘r’, REAL_INV_POS]
 >> Q.EXISTS_TAC ‘u’
 >> CONJ_TAC >- (MATCH_MP_TAC OPEN_OWN_NEIGH >> fs [IN_APP])
 >> Q.PAT_X_ASSUM ‘x IN topspace t’ K_TAC
 >> Q.PAT_X_ASSUM ‘x IN u’          K_TAC
 >> Q.X_GEN_TAC ‘x’
 >> rpt STRIP_TAC
 >- (Suff ‘u SUBSET topspace t’ >- METIS_TAC [SUBSET_DEF] \\
     MATCH_MP_TAC OPEN_IN_SUBSET >> art [])
 >> Q.EXISTS_TAC ‘u’ >> simp []
QED

Theorem frontier_of_in_general_borel :
    !t s. t frontier_of s IN subsets (B t)
Proof
    rw [FRONTIER_OF_CLOSURES]
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> rw [] (* 2 subgoals, same tactics *)
 >> MATCH_MP_TAC closed_in_general_borel
 >> rw [CLOSED_IN_CLOSURE_OF]
QED

Definition Portemanteau_iii_def :
    Portemanteau_iii E X Y <=>
    !f. bounded (IMAGE f UNIV) /\
        f IN borel_measurable (B (mtop E)) /\ Y (U (mtop E) f) = 0 ==>
        weak_convergence_condition (mtop E) X Y f
End

(* "trivial" *)
Theorem Portemanteau_iii_imp_i :
    !E X Y. Portemanteau_antecedents E X Y /\
            Portemanteau_iii E X Y ==> Portemanteau_i E X Y
Proof
    rw [Portemanteau_iii_def, Portemanteau_i_def,
        weak_converge_in_topology_def, Portemanteau_antecedents_def]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> CONJ_TAC >- fs [bounded_continuous_def, IN_APP]
 >> reverse CONJ_TAC
 >- (Q.PAT_X_ASSUM ‘subprobability_measure (space (B E),subsets (B E),Y)’ MP_TAC \\
     rw [subprobability_measure_alt] \\
     Suff ‘U (mtop E) f = {}’
     >- (Rewr' \\
         qabbrev_tac ‘M = (space (B E),subsets (B E),Y)’ \\
        ‘Y = measure M’ by rw [Abbr ‘M’] >> POP_ORW \\
         MATCH_MP_TAC MEASURE_EMPTY >> art []) \\
     rw [U_DEF, Once EXTENSION, TOPSPACE_MTOP] \\
     fs [CONTINUOUS_MAP_EQ_TOPCONTINUOUS_AT, TOPSPACE_MTOP,
         bounded_continuous_def, IN_APP])
 (* show that continuous function is borel measurable *)
 >> MATCH_MP_TAC in_borel_measurable_open_imp
 >> RW_TAC std_ss [sigma_algebra_general_borel, PREIMAGE_def,
                   euclidean_open_def, space_general_borel]
 >> qabbrev_tac ‘t = mtop E’ (* the underlying metric is irrelevant *)
 >> ASSUME_TAC (Q.SPEC ‘t’ OPEN_IN_TOPSPACE)
 >> qabbrev_tac ‘u = topspace t’
 >> ‘{x | f x IN s} INTER u = {x | x IN u /\ f x IN s}’ by SET_TAC []
 >> POP_ORW
 >> REWRITE_TAC [general_borel_def]
 >> MATCH_MP_TAC IN_SIGMA
 >> REWRITE_TAC [Once IN_APP]
 >> MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE_GEN
 >> Q.EXISTS_TAC ‘euclidean’
 >> fs [bounded_continuous_def, IN_APP]
QED

Definition Portemanteau_iv_def :
    Portemanteau_iv E X Y <=>
      Y (mspace E) <= liminf (\n. X n (mspace E)) /\
      !s. closed_in (mtop E) s ==> limsup (\n. X n s) <= Y s
End

Definition Portemanteau_v_def :
    Portemanteau_v E X Y <=>
      limsup (\n. X n (mspace E)) <= Y (mspace E) /\
      !s. open_in (mtop E) s ==> Y s <= liminf (\n. X n s)
End

(* NOTE: This proof doesn't work if “Y (mspace E) <= liminf (\n. X n (mspace E))”
   is removed from Portemanteau_iv_def and Portemanteau_v_def, unless the involved
   spm is just prob_space.
 *)
Theorem Portemanteau_iv_imp_v[local] :
    !E X Y. Portemanteau_antecedents E X Y /\
            Portemanteau_iv E X Y ==> Portemanteau_v E X Y
Proof
    rpt GEN_TAC
 >> simp [Portemanteau_antecedents_def, Portemanteau_iv_def, Portemanteau_v_def]
 >> STRIP_TAC
 (* limsup (\n. X n (mspace E)) <= Y (mspace E) *)
 >> CONJ_TAC
 >- (POP_ASSUM MATCH_MP_TAC \\
     REWRITE_TAC [mspace, CLOSED_IN_TOPSPACE])
 (* !s. open_in (mtop E) s ==> Y s <= liminf (\n. X n s) *)
 >> Q.X_GEN_TAC ‘s’ >> STRIP_TAC
 >> qabbrev_tac ‘sp = mspace E’
 >> qabbrev_tac ‘t = mtop E’
 >> qabbrev_tac ‘s0 = sp DIFF s’
 >> ‘s SUBSET sp’
      by FULL_SIMP_TAC std_ss [OPEN_IN_SUBSET_TOPSPACE, mspace, Abbr ‘sp’]
 >> ‘s0 SUBSET sp’ by ASM_SET_TAC []
 >> Know ‘closed_in t s0’
 >- (FULL_SIMP_TAC std_ss [closed_in, Abbr ‘s0’, Abbr ‘sp’, mspace, Abbr ‘t’] \\
     qabbrev_tac ‘sp = topspace (mtop E)’ \\
     Suff ‘sp DIFF (sp DIFF s) = s’ >- rw [] \\
     ASM_SET_TAC [])
 >> DISCH_TAC
 >> ‘s = sp DIFF s0’ by ASM_SET_TAC [] >> POP_ORW
 >> qabbrev_tac ‘b = B t’
 >> ‘sigma_algebra b’ by METIS_TAC [sigma_algebra_general_borel]
 >> Know ‘space b = sp’
 >- (rw [Abbr ‘sp’, Abbr ‘b’, space_general_borel] \\
     rw [Abbr ‘t’, mspace])
 >> DISCH_TAC
 >> Know ‘s IN subsets b’
 >- (simp [Abbr ‘b’, general_borel_def] \\
     MATCH_MP_TAC IN_SIGMA >> rw [IN_APP])
 >> DISCH_TAC
 >> Know ‘s0 IN subsets b’
 >- (qunabbrev_tac ‘s0’ \\
     Q.PAT_X_ASSUM ‘space b = sp’ (REWRITE_TAC o wrap o SYM) \\
     MATCH_MP_TAC SIGMA_ALGEBRA_COMPL >> art [])
 >> DISCH_TAC
 (* applying MEASURE_SPACE_FINITE_DIFF *)
 >> Know ‘Y (sp DIFF s0) = Y sp - Y s0’
 >- (Q.PAT_X_ASSUM ‘subprobability_measure (space b,subsets b,Y)’ MP_TAC \\
     rw [subprobability_measure_alt] \\
     qabbrev_tac ‘p = (space b,subsets b,Y)’ \\
    ‘Y = measure p’ by rw [Abbr ‘p’] >> POP_ORW \\
    ‘space b = m_space p’ by rw [Abbr ‘b’, Abbr ‘p’, space_general_borel] \\
     POP_ORW \\
     MATCH_MP_TAC MEASURE_SPACE_FINITE_DIFF >> rw [Abbr ‘p’] \\
     simp [lt_infty] \\
     Q_TAC (TRANS_TAC let_trans) ‘1’ >> rw [])
 >> Rewr'
 >> Know ‘!n. X n (sp DIFF s0) = X n sp - X n s0’
 >- (Q.X_GEN_TAC ‘n’ \\
     Q.PAT_X_ASSUM ‘!n. subprobability_measure (space b,subsets b,X n)’
       (MP_TAC o Q.SPEC ‘n’) \\
     rw [subprobability_measure_alt] \\
     qabbrev_tac ‘p = (space b,subsets b,X n)’ \\
    ‘X n = measure p’ by rw [Abbr ‘p’] >> POP_ORW \\
    ‘space b = m_space p’ by rw [Abbr ‘b’, Abbr ‘p’, space_general_borel] \\
     POP_ORW \\
     MATCH_MP_TAC MEASURE_SPACE_FINITE_DIFF >> rw [Abbr ‘p’] \\
     simp [lt_infty] \\
     Q_TAC (TRANS_TAC let_trans) ‘1’ >> rw [])
 >> Rewr'
 (* stage work *)
 >> simp [extreal_sub, ext_liminf_alt_limsup, o_DEF]
 >> ‘(!n. finite_measure_space (space b,subsets b,X n)) /\
          finite_measure_space (space b,subsets b,Y)’
      by PROVE_TAC [subprobability_measure_imp_finite]
 >> gs [subprobability_measure_alt, finite_measure_space_thm]
 >> ‘sp IN subsets b’ by METIS_TAC [SIGMA_ALGEBRA_SPACE]
 >> Know ‘!n. -(X n sp + -X n s0) = -X n sp + -(-X n s0)’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC neg_add >> simp [])
 >> Rewr'
 >> Know ‘- -Y sp + -Y s0 = -(-Y sp + Y s0)’
 >- (SYM_TAC >> MATCH_MP_TAC neg_add >> simp [])
 >> simp [] >> DISCH_THEN K_TAC
 >> simp [le_neg]
 >> Q_TAC (TRANS_TAC le_trans) ‘limsup (\n. -X n sp) + limsup (\n. X n s0)’
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC le_add2 >> simp [] \\
     rw [ext_limsup_alt_liminf, o_DEF, le_neg])
 (* applying ext_limsup_add *)
 >> HO_MATCH_MP_TAC ext_limsup_add
 >> rw [ext_bounded_alt] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC ‘1’ >> rw [normal_1] \\
      REWRITE_TAC [abs_neg_eq] \\
      simp [abs_bounds] \\
      Q_TAC (TRANS_TAC le_trans) ‘-0’ >> rw [le_neg] \\
      Q.PAT_X_ASSUM ‘!n. measure_space (space b,subsets b,X n) /\ _’
        (MP_TAC o Q.SPEC ‘n’) \\
      qmatch_abbrev_tac ‘measure_space M /\ _ ==> _’ >> STRIP_TAC \\
     ‘X n = measure M’ by rw [Abbr ‘M’] >> POP_ORW \\
      MATCH_MP_TAC MEASURE_POSITIVE >> rw [Abbr ‘M’],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC ‘1’ >> rw [normal_1] \\
      simp [abs_bounds] \\
      Q_TAC (TRANS_TAC le_trans) ‘-0’ >> rw [le_neg] \\
      Q.PAT_X_ASSUM ‘!n. measure_space (space b,subsets b,X n) /\ _’
        (MP_TAC o Q.SPEC ‘n’) \\
      qmatch_abbrev_tac ‘measure_space M /\ _ ==> _’ >> STRIP_TAC \\
     ‘X n = measure M’ by rw [Abbr ‘M’] >> POP_ORW \\
      MATCH_MP_TAC MEASURE_POSITIVE >> rw [Abbr ‘M’] ]
QED

(* "trivial", dual of the above proof *)
Theorem Portemanteau_v_imp_iv[local] :
    !E X Y. Portemanteau_antecedents E X Y /\
            Portemanteau_v E X Y ==> Portemanteau_iv E X Y
Proof
    rpt GEN_TAC
 >> simp [Portemanteau_antecedents_def, Portemanteau_iv_def, Portemanteau_v_def]
 >> STRIP_TAC
 (* Y (mspace E) <= liminf (\n. X n (mspace E)) *)
 >> CONJ_TAC
 >- (POP_ASSUM MATCH_MP_TAC \\
     REWRITE_TAC [mspace, OPEN_IN_TOPSPACE])
 >> Q.X_GEN_TAC ‘s’ >> STRIP_TAC
 >> qabbrev_tac ‘sp = mspace E’
 >> qabbrev_tac ‘t = mtop E’
 >> qabbrev_tac ‘s0 = sp DIFF s’
 >> Know ‘open_in t s0’
 >- FULL_SIMP_TAC std_ss [closed_in, Abbr ‘s0’, Abbr ‘sp’, mspace]
 >> DISCH_TAC
 >> ‘s SUBSET sp’ by FULL_SIMP_TAC std_ss [closed_in, mspace, Abbr ‘sp’]
 >> ‘s = sp DIFF s0’ by ASM_SET_TAC [] >> POP_ORW
 >> qabbrev_tac ‘b = B t’
 >> ‘sigma_algebra b’ by METIS_TAC [sigma_algebra_general_borel]
 >> Know ‘space b = sp’
 >- (rw [Abbr ‘sp’, Abbr ‘b’, space_general_borel] \\
     rw [Abbr ‘t’, mspace])
 >> DISCH_TAC
 >> Know ‘s0 IN subsets b’
 >- (simp [Abbr ‘b’, general_borel_def] \\
     MATCH_MP_TAC IN_SIGMA >> rw [IN_APP])
 >> DISCH_TAC
 >> Know ‘s IN subsets b’
 >- (‘s = sp DIFF s0’ by ASM_SET_TAC [] >> POP_ORW \\
     Q.PAT_X_ASSUM ‘space b = sp’ (REWRITE_TAC o wrap o SYM) \\
     MATCH_MP_TAC SIGMA_ALGEBRA_COMPL >> art [])
 >> DISCH_TAC
 (* applying MEASURE_SPACE_FINITE_DIFF *)
 >> Know ‘Y (sp DIFF s0) = Y sp - Y s0’
 >- (Q.PAT_X_ASSUM ‘subprobability_measure (space b,subsets b,Y)’ MP_TAC \\
     rw [subprobability_measure_alt] \\
     qabbrev_tac ‘p = (space b,subsets b,Y)’ \\
    ‘Y = measure p’ by rw [Abbr ‘p’] >> POP_ORW \\
    ‘space b = m_space p’ by rw [Abbr ‘b’, Abbr ‘p’, space_general_borel] \\
     POP_ORW \\
     MATCH_MP_TAC MEASURE_SPACE_FINITE_DIFF >> rw [Abbr ‘p’] \\
     simp [lt_infty] \\
     Q_TAC (TRANS_TAC let_trans) ‘1’ >> rw [])
 >> Rewr'
 >> Know ‘!n. X n (sp DIFF s0) = X n sp - X n s0’
 >- (Q.X_GEN_TAC ‘n’ \\
     Q.PAT_X_ASSUM ‘!n. subprobability_measure (space b,subsets b,X n)’
       (MP_TAC o Q.SPEC ‘n’) \\
     rw [subprobability_measure_alt] \\
     qabbrev_tac ‘p = (space b,subsets b,X n)’ \\
    ‘X n = measure p’ by rw [Abbr ‘p’] >> POP_ORW \\
    ‘space b = m_space p’ by rw [Abbr ‘b’, Abbr ‘p’, space_general_borel] \\
     POP_ORW \\
     MATCH_MP_TAC MEASURE_SPACE_FINITE_DIFF >> rw [Abbr ‘p’] \\
     simp [lt_infty] \\
     Q_TAC (TRANS_TAC let_trans) ‘1’ >> rw [])
 >> Rewr'
 (* stage work *)
 >> simp [extreal_sub, ext_limsup_alt_liminf, o_DEF]
 >> ‘(!n. finite_measure_space (space b,subsets b,X n)) /\
          finite_measure_space (space b,subsets b,Y)’
      by PROVE_TAC [subprobability_measure_imp_finite]
 >> gs [subprobability_measure_alt, finite_measure_space_thm]
 >> ‘sp IN subsets b’ by METIS_TAC [SIGMA_ALGEBRA_SPACE]
 >> Know ‘!n. -(X n sp + -X n s0) = -X n sp + -(-X n s0)’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC neg_add >> simp [])
 >> Rewr'
 >> Know ‘- -Y sp + -Y s0 = -(-Y sp + Y s0)’
 >- (SYM_TAC \\
     MATCH_MP_TAC neg_add >> simp [])
 >> simp []
 >> DISCH_THEN K_TAC
 >> simp [le_neg]
 (* applying ext_liminf_add *)
 >> Q_TAC (TRANS_TAC le_trans) ‘liminf (\n. -X n sp) + liminf (\n. X n s0)’
 >> CONJ_TAC
 >- (MATCH_MP_TAC le_add2 >> simp [] \\
     rw [ext_liminf_alt_limsup, o_DEF, le_neg])
 >> HO_MATCH_MP_TAC ext_liminf_add
 >> rw [ext_bounded_alt] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC ‘1’ >> rw [normal_1] \\
      REWRITE_TAC [abs_neg_eq] \\
      simp [abs_bounds] \\
      Q_TAC (TRANS_TAC le_trans) ‘-0’ >> rw [le_neg] \\
      Q.PAT_X_ASSUM ‘!n. measure_space (space b,subsets b,X n) /\ _’
        (MP_TAC o Q.SPEC ‘n’) \\
      qmatch_abbrev_tac ‘measure_space M /\ _ ==> _’ >> STRIP_TAC \\
     ‘X n = measure M’ by rw [Abbr ‘M’] >> POP_ORW \\
      MATCH_MP_TAC MEASURE_POSITIVE >> rw [Abbr ‘M’],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC ‘1’ >> rw [normal_1] \\
      simp [abs_bounds] \\
      Q_TAC (TRANS_TAC le_trans) ‘-0’ >> rw [le_neg] \\
      Q.PAT_X_ASSUM ‘!n. measure_space (space b,subsets b,X n) /\ _’
        (MP_TAC o Q.SPEC ‘n’) \\
      qmatch_abbrev_tac ‘measure_space M /\ _ ==> _’ >> STRIP_TAC \\
     ‘X n = measure M’ by rw [Abbr ‘M’] >> POP_ORW \\
      MATCH_MP_TAC MEASURE_POSITIVE >> rw [Abbr ‘M’] ]
QED

Theorem Portemanteau_iv_eq_v :
    !E X Y. Portemanteau_antecedents E X Y ==>
           (Portemanteau_iv E X Y <=> Portemanteau_v E X Y)
Proof
    METIS_TAC [Portemanteau_iv_imp_v, Portemanteau_v_imp_iv]
QED

Definition Portemanteau_vi_def :
    Portemanteau_vi E X Y <=>
      !A. A IN subsets (B (mtop E)) /\ Y ((mtop E) frontier_of A) = 0 ==>
         ((\n. X n A) --> Y A) sequentially
End

(* "trivial" *)
Theorem Portemanteau_v_imp_vi :
    !E X Y. Portemanteau_antecedents E X Y /\
            Portemanteau_v E X Y ==> Portemanteau_vi E X Y
Proof
    RW_TAC std_ss [Portemanteau_vi_def]
 >> ‘Portemanteau_iv E X Y’ by PROVE_TAC [Portemanteau_iv_eq_v]
 >> fs [Portemanteau_antecedents_def, Portemanteau_iv_def, Portemanteau_v_def]
 >> qabbrev_tac ‘t = mtop E’
 >> ‘(!n. finite_measure_space (space (B t),subsets (B t),X n)) /\
          finite_measure_space (space (B t),subsets (B t),Y)’
      by PROVE_TAC [subprobability_measure_imp_finite]
 >> fs [FORALL_AND_THM, finite_measure_space_thm]
 (* applying extreal_lim_sequentially_eq *)
 >> qmatch_abbrev_tac ‘(f --> l) sequentially’
 >> Know ‘(f --> l) sequentially <=> (real o f --> real l) sequentially’
 >- (MATCH_MP_TAC extreal_lim_sequentially_eq >> rw [Abbr ‘l’] \\
     Q.EXISTS_TAC ‘0’ >> rw [Abbr ‘f’])
 >> Rewr'
 (* applying ext_limsup_thm *)
 >> simp [Abbr ‘l’]
 >> qabbrev_tac ‘l = real (Y A)’
 >> Know ‘(real o f --> l) sequentially <=>
          limsup f = Normal l /\ liminf f = Normal l’
 >- (MATCH_MP_TAC ext_limsup_thm \\
     rw [Abbr ‘f’])
 >> Rewr'
 >> simp [Abbr ‘f’, Abbr ‘l’, normal_real]
 (* stage work *)
 >> ‘sigma_algebra (B t)’ by rw [sigma_algebra_general_borel]
 >> Know ‘A SUBSET topspace t’
 >- (REWRITE_TAC [GSYM space_general_borel] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_SUBSET_SPACE >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘b = t frontier_of A’
 >> ‘closed_in t b’ by rw [CLOSED_IN_FRONTIER_OF, Abbr ‘b’]
 >> Know ‘b IN subsets (B t)’
 >- (qunabbrev_tac ‘b’ \\
     MATCH_MP_TAC closed_in_general_borel >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘A1 = A UNION b’
 >> ‘A1 IN subsets (B t)’ by rw [SIGMA_ALGEBRA_UNION, Abbr ‘A1’]
 >> Know ‘A1 = t closure_of A’
 >- (simp [Abbr ‘A1’, Abbr ‘b’, frontier_of] \\
     qabbrev_tac ‘c = t closure_of A’ \\
    ‘A SUBSET c’ by PROVE_TAC [CLOSURE_OF_SUBSET] \\
     qabbrev_tac ‘s = t interior_of A’ \\
    ‘s SUBSET A’ by PROVE_TAC [INTERIOR_OF_SUBSET] \\
     ASM_SET_TAC [])
 >> DISCH_TAC
 >> ‘closed_in t A1’ by PROVE_TAC [CLOSED_IN_CLOSURE_OF]
 >> Q.PAT_X_ASSUM ‘_ = t closure_of A’ K_TAC
 >> qabbrev_tac ‘A0 = A DIFF b’
 >> ‘A0 IN subsets (B t)’ by rw [SIGMA_ALGEBRA_DIFF, Abbr ‘A0’]
 >> Know ‘A0 = t interior_of A’
 >- (simp [Abbr ‘A0’, Abbr ‘b’, frontier_of] \\
     qabbrev_tac ‘c = t closure_of A’ \\
    ‘A SUBSET c’ by PROVE_TAC [CLOSURE_OF_SUBSET] \\
     qabbrev_tac ‘s = t interior_of A’ \\
    ‘s SUBSET A’ by PROVE_TAC [INTERIOR_OF_SUBSET] \\
     ASM_SET_TAC [])
 >> DISCH_TAC
 >> ‘open_in t A0’ by PROVE_TAC [OPEN_IN_INTERIOR_OF]
 >> Q.PAT_X_ASSUM ‘_ = t interior_of A’ K_TAC
 >> Suff ‘limsup (\n. X n A) <= Y A /\ Y A <= liminf (\n. X n A)’
 >- (STRIP_TAC \\
    ‘liminf (\n. X n A) <= limsup (\n. X n A)’ by rw [ext_liminf_le_limsup] \\
     rw [GSYM le_antisym] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q_TAC (TRANS_TAC le_trans) ‘liminf (\n. X n A)’ >> art [],
       (* goal 2 (of 2) *)
       Q_TAC (TRANS_TAC le_trans) ‘limsup (\n. X n A)’ >> art [] ])
 >> CONJ_TAC
 >- ((* limsup (\n. X n A) <= Y A *)
     Q_TAC (TRANS_TAC le_trans) ‘limsup (\n. X n A1)’ \\
     CONJ_TAC
     >- (MATCH_MP_TAC ext_limsup_mono >> rw [Abbr ‘A1’] \\
         Q.PAT_X_ASSUM ‘!n. measure_space_space (space (B t),subsets (B t),X n)’
           (MP_TAC o Q.SPEC ‘n’) \\
         qmatch_abbrev_tac ‘measure_space M ==> _’ >> DISCH_TAC \\
        ‘X n = measure M’ by rw [Abbr ‘M’] >> POP_ORW \\
         Know ‘increasing M’ >- rw [MEASURE_SPACE_INCREASING] \\
         rw [increasing_def] \\
         POP_ASSUM MATCH_MP_TAC >> rw [Abbr ‘M’]) \\
     Q_TAC (TRANS_TAC le_trans) ‘Y A1’ >> rw [] \\
    ‘Y A = Y A + Y b’ by rw [] >> POP_ORW \\
     qabbrev_tac ‘M = (space (B t),subsets (B t),Y)’ \\
    ‘Y = measure M’ by rw [Abbr ‘M’] >> POP_ORW \\
     qunabbrev_tac ‘A1’ \\
     Know ‘subadditive M’ >- rw [MEASURE_SPACE_SUBADDITIVE] \\
     rw [subadditive_def] \\
     POP_ASSUM MATCH_MP_TAC >> rw [Abbr ‘M’])
 (* Y A <= liminf (\n. X n A) *)
 >> Q_TAC (TRANS_TAC le_trans) ‘liminf (\n. X n A0)’
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC ext_liminf_mono >> rw [Abbr ‘A0’] \\
     Q.PAT_X_ASSUM ‘!n. measure_space (space (B t),subsets (B t),X n)’
       (MP_TAC o Q.SPEC ‘n’) \\
     qmatch_abbrev_tac ‘measure_space M ==> _’ >> DISCH_TAC \\
    ‘X n = measure M’ by rw [Abbr ‘M’] >> POP_ORW \\
     Know ‘increasing M’ >- rw [MEASURE_SPACE_INCREASING] \\
     rw [increasing_def] \\
     POP_ASSUM MATCH_MP_TAC >> rw [Abbr ‘M’])
 >> Q_TAC (TRANS_TAC le_trans) ‘Y A0’ >> rw []
 >> qabbrev_tac ‘A2 = A INTER b’
 >> ‘A2 IN subsets (B t)’ by rw [SIGMA_ALGEBRA_INTER, Abbr ‘A2’]
 >> ‘A = A0 UNION A2’ by ASM_SET_TAC [] >> POP_ORW
 >> qabbrev_tac ‘M = (space (B t),subsets (B t),Y)’
 >> ‘Y = measure M’ by rw [Abbr ‘M’] >> POP_ORW
 >> Know ‘measure M (A0 UNION A2) = measure M A0 + measure M A2’
 >- (Know ‘additive M’ >- rw [MEASURE_SPACE_ADDITIVE] \\
     rw [additive_def] \\
     POP_ASSUM MATCH_MP_TAC >> rw [Abbr ‘M’, SIGMA_ALGEBRA_UNION] \\
     ASM_SET_TAC [])
 >> Rewr'
 >> Suff ‘measure M A2 = 0’ >- rw []
 >> rw [GSYM le_antisym]
 >- (‘0 = measure M b’ by rw [Abbr ‘M’] >> POP_ORW \\
     Know ‘increasing M’ >- rw [MEASURE_SPACE_INCREASING] \\
     rw [increasing_def] \\
     POP_ASSUM MATCH_MP_TAC >> rw [Abbr ‘M’, Abbr ‘A2’])
 >> Know ‘positive M’ >- rw [MEASURE_SPACE_POSITIVE]
 >> rw [positive_def]
 >> POP_ASSUM MATCH_MP_TAC >> rw [Abbr ‘M’]
QED

(* alternative antecedents using ‘prob_space’ instead of ‘subprobability_measure’ *)
Definition Portemanteau_antecedents_alt_def :
    Portemanteau_antecedents_alt E X Y <=>
   (!n. prob_space (space (B E),subsets (B E),X n)) /\
    prob_space (space (B E),subsets (B E),Y)
End

Theorem Portemanteau_antecedents_alt_imp_antecedents :
    !E X Y. Portemanteau_antecedents_alt E X Y ==>
            Portemanteau_antecedents E X Y
Proof
    rw [Portemanteau_antecedents_def, Portemanteau_antecedents_alt_def]
 >> MATCH_MP_TAC prob_space_imp_subprobability_measure >> art []
QED

(* not easy

   NOTE: Since the part “Y (mspace E) <= liminf (\n. X n (mspace E))” cannot
   be removed from Portemanteau_iv_def, this part may require a dedicated
   proof not mentioned in [8].
 *)
Theorem Portemanteau_ii_imp_iv :
    !E X Y. Portemanteau_antecedents_alt E X Y /\
            Portemanteau_ii E X Y ==> Portemanteau_iv E X Y
Proof
    rpt STRIP_TAC
 >> ‘Portemanteau_antecedents E X Y’
       by PROVE_TAC [Portemanteau_antecedents_alt_imp_antecedents]
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> SIMP_TAC set_ss [Portemanteau_antecedents_def, GSYM mspace, BL_def,
                     Portemanteau_ii_def, Portemanteau_iv_def,
                     weak_convergence_condition_def]
 >> NTAC 2 STRIP_TAC
 >> qabbrev_tac ‘sp = mspace E’
 >> qabbrev_tac ‘t = mtop E’
 >> ‘closed_in t sp’ by METIS_TAC [CLOSED_IN_TOPSPACE, mspace]
 >> qabbrev_tac ‘b = B t’
 >> ‘sigma_algebra b’ by METIS_TAC [sigma_algebra_general_borel]
 >> Know ‘space b = sp’
 >- (rw [Abbr ‘sp’, Abbr ‘b’, space_general_borel] \\
     rw [Abbr ‘t’, mspace])
 >> DISCH_TAC
 >> ‘sp IN subsets b’ by METIS_TAC [SIGMA_ALGEBRA_SPACE]
 >> ‘(!n. finite_measure_space (space b,subsets b,X n)) /\
          finite_measure_space (space b,subsets b,Y)’
      by PROVE_TAC [subprobability_measure_imp_finite]
 >> gs [subprobability_measure_alt, finite_measure_space_thm, FORALL_AND_THM]
 (* provable part *)
 >> reverse CONJ_TAC
 >- (Q.X_GEN_TAC ‘A’ >> DISCH_TAC \\
     Cases_on ‘A = {}’
     >- (rename1 ‘s = {}’ \\
         Know ‘!n. X n s = 0’
         >- (Q.X_GEN_TAC ‘n’ \\
             Q.PAT_X_ASSUM ‘!n. measure_space (sp,subsets b,X n)’
               (MP_TAC o Q.SPEC ‘n’) \\
             qmatch_abbrev_tac ‘measure_space M ==> _’ >> DISCH_TAC \\
            ‘X n = measure M’ by rw [Abbr ‘M’] >> POP_ORW \\
             rw [MEASURE_EMPTY]) >> Rewr' \\
         Know ‘Y s = 0’
         >- (qabbrev_tac ‘M = (sp,subsets b,Y)’ \\
            ‘Y = measure M’ by rw [Abbr ‘M’] >> POP_ORW \\
             rw [MEASURE_EMPTY]) >> Rewr' \\
         simp [ext_limsup_const]) \\
     qabbrev_tac ‘A' = set_mcball E A’ \\
     Know ‘!e. A' e IN subsets b’
     >- (rw [Abbr ‘A'’, Abbr ‘b’] \\
         MATCH_MP_TAC closed_in_general_borel \\
         qunabbrev_tac ‘t’ \\
         simp [closed_in_set_mcball]) \\
     DISCH_TAC \\
     qabbrev_tac ‘M' = (sp,subsets b,Y)’ \\
    ‘Y = measure M'’ by rw [Abbr ‘M'’] >> POP_ORW \\
  (* preparing for MONOTONE_CONVERGENCE_BIGINTER2 *)
     Know ‘A = BIGINTER (IMAGE (\n. A' (inv &SUC n)) UNIV)’
     >- (rw [Once EXTENSION, IN_BIGINTER_IMAGE, Abbr ‘A'’, set_mcball_def] \\
         Cases_on ‘x IN A’ >> simp [SET_DIST_SING_IN_SET] \\
         qabbrev_tac ‘d = set_dist E ({x},A)’ \\
        ‘0 <= d’ by METIS_TAC [SET_DIST_POS_LE] \\
        ‘d <> 0’ by METIS_TAC [SET_DIST_EQ_0_CLOSED] \\
        ‘0 < d’ by PROVE_TAC [REAL_LE_LT] \\
         MP_TAC (Q.SPEC ‘d’ REAL_ARCH_INV_SUC) >> rw [GSYM real_lt]) \\
     DISCH_THEN
       (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites o wrap) \\
     qmatch_abbrev_tac ‘limsup _ <= measure M' (BIGINTER (IMAGE g UNIV))’ \\
  (* applying MONOTONE_CONVERGENCE_BIGINTER2 *)
     Know ‘measure M' (BIGINTER (IMAGE g UNIV)) = inf (IMAGE (measure M' o g) UNIV)’
     >- (SYM_TAC \\
         MATCH_MP_TAC MONOTONE_CONVERGENCE_BIGINTER2 \\
         simp [IN_FUNSET, Abbr ‘M'’] \\
         CONJ_ASM1_TAC >- rw [Abbr ‘g’] \\
         CONJ_TAC >- METIS_TAC [] \\
         RW_TAC set_ss [Abbr ‘g’, Abbr ‘A'’, SUBSET_DEF, set_mcball_def] \\
         Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘inv (&SUC (SUC n))’ >> art [] \\
         MATCH_MP_TAC REAL_LE_INV2 >> simp []) >> Rewr' \\
     simp [le_inf', Abbr ‘g’] \\
     Suff ‘!e. 0 < e ==> limsup (\n. X n A) <= measure M' (A' e)’
     >- (rw [] >> POP_ASSUM MATCH_MP_TAC \\
         MATCH_MP_TAC REAL_INV_POS >> simp []) \\
     rpt STRIP_TAC \\
    ‘?f. Lipschitz_continuous_map (E,mr1) f /\
        (!x. 0 <= f x /\ f x <= 1) /\
        (!x. x IN A ==> f x = 1) /\
         !x. e <= set_dist E ({x},A) ==> f x = 0’
       by METIS_TAC [Lipschitz_continuous_map_exists] \\
     qabbrev_tac ‘M = \n. (sp,subsets b,X n)’ \\
    ‘!n. X n A = measure (M n) A’ by rw [Abbr ‘M’] >> POP_ORW \\
     Know ‘!n. measure (M n) A = integral (M n) (indicator_fn A)’
     >- (Q.X_GEN_TAC ‘n’ >> SYM_TAC \\
         MATCH_MP_TAC integral_indicator \\
         fs [Abbr ‘M’, Abbr ‘b’] \\
         MATCH_MP_TAC closed_in_general_borel >> art []) >> Rewr' \\
     Q_TAC (TRANS_TAC le_trans) ‘limsup (\n. integral (M n) (Normal o f))’ \\
     CONJ_TAC
     >- (MATCH_MP_TAC ext_limsup_mono >> RW_TAC std_ss [] \\
        ‘measure_space (M n)’ by METIS_TAC [] \\
         Know ‘       integral (M n) (indicator_fn A) =
               pos_fn_integral (M n) (indicator_fn A)’
         >- (MATCH_MP_TAC integral_pos_fn >> simp [INDICATOR_FN_POS]) >> Rewr' \\
         Know ‘       integral (M n) (Normal o f) =
               pos_fn_integral (M n) (Normal o f)’
         >- (MATCH_MP_TAC integral_pos_fn \\
             rw [o_DEF, extreal_of_num_def]) >> Rewr' \\
         MATCH_MP_TAC pos_fn_integral_mono >> rw [INDICATOR_FN_POS] \\
         Cases_on ‘x IN A’ >- rw [indicator_fn_def, normal_1] \\
         simp [indicator_fn_def, extreal_of_num_def]) \\
     Q.PAT_X_ASSUM ‘!f. f IN C_b t /\ Lipschitz_continuous_map (E,mr1) f ==> _’
       (MP_TAC o Q.SPEC ‘f’) >> simp [bounded_continuous_def, IN_APP] \\
     impl_tac (* continuous_map /\ bounded *)
     >- (CONJ_TAC
         >- (simp [euclidean_def, Abbr ‘t’] \\
             MATCH_MP_TAC Lipschitz_continuous_map_imp_continuous_map >> art []) \\
         rw [bounded_def, ABS_BOUNDS] \\
         Q.EXISTS_TAC ‘1’ >> reverse (rw []) >- simp [] \\
         Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘0’ >> simp []) \\
  (* applying extreal_lim_sequentially_eq *)
     qmatch_abbrev_tac ‘(h --> l) sequentially ==> _’ \\
     Know ‘l <> NegInf /\ l <> PosInf’
     >- (simp [Abbr ‘l’] \\
         Know ‘       integral M' (Normal o f) =
               pos_fn_integral M' (Normal o f)’
         >- (MATCH_MP_TAC integral_pos_fn \\
             rw [o_DEF, extreal_of_num_def]) >> Rewr' \\
         CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf \\
                      MATCH_MP_TAC pos_fn_integral_pos \\
                      rw [o_DEF, extreal_of_num_def]) \\
         simp [lt_infty] \\
         Q_TAC (TRANS_TAC let_trans) ‘pos_fn_integral M' (\x. Normal 1)’ \\
         CONJ_TAC
         >- (MATCH_MP_TAC pos_fn_integral_mono \\
             rw [extreal_of_num_def, o_DEF]) \\
         Know ‘pos_fn_integral M' (\x. Normal 1) =
               Normal 1 * measure M' (m_space M')’
         >- (MATCH_MP_TAC pos_fn_integral_const \\
             simp [GSYM lt_infty] >> simp [Abbr ‘M'’]) >> Rewr' \\
         simp [normal_1, GSYM lt_infty, Abbr ‘M'’]) >> STRIP_TAC \\
     Know ‘!n. h n <> NegInf /\ h n <> PosInf’
     >- (Q.X_GEN_TAC ‘n’ \\
         simp [Abbr ‘h’] \\
        ‘!n. measure_space (M n)’ by METIS_TAC [] \\
         Know ‘!n.        integral (M n) (Normal o f) =
                   pos_fn_integral (M n) (Normal o f)’
         >- (Q.X_GEN_TAC ‘n’ >> MATCH_MP_TAC integral_pos_fn \\
             rw [o_DEF, extreal_of_num_def]) >> Rewr' \\
         CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf \\
                      MATCH_MP_TAC pos_fn_integral_pos \\
                      rw [o_DEF, extreal_of_num_def]) \\
         simp [lt_infty] \\
         Q_TAC (TRANS_TAC let_trans) ‘pos_fn_integral (M n) (\x. Normal 1)’ \\
         CONJ_TAC >- (MATCH_MP_TAC pos_fn_integral_mono \\
                      rw [extreal_of_num_def, o_DEF]) \\
         Know ‘pos_fn_integral (M n) (\x. Normal 1) =
               Normal 1 * measure (M n) (m_space (M n))’
         >- (MATCH_MP_TAC pos_fn_integral_const >> simp [GSYM lt_infty] \\
             simp [Abbr ‘M’]) >> Rewr' \\
         simp [normal_1, GSYM lt_infty, Abbr ‘M’]) >> DISCH_TAC \\
     Know ‘(h --> l) sequentially <=> (real o h --> real l) sequentially’
     >- (MATCH_MP_TAC extreal_lim_sequentially_eq >> art []) >> Rewr' \\
  (* applying ext_limsup_thm *)
     qabbrev_tac ‘l' = real l’ \\
     Know ‘(real o h --> l') sequentially <=>
            limsup h = Normal l' /\ liminf h = Normal l'’
     >- (MATCH_MP_TAC ext_limsup_thm >> rw []) >> Rewr' \\
     simp [normal_real, Abbr ‘l'’, Abbr ‘l’] >> STRIP_TAC \\
     Know ‘       integral M' (Normal o f) =
           pos_fn_integral M' (Normal o f)’
     >- (MATCH_MP_TAC integral_pos_fn \\
         rw [o_DEF, extreal_of_num_def]) >> Rewr' \\
     Know ‘measure M' (A' e) = pos_fn_integral M' (indicator_fn (A' e))’
     >- (SYM_TAC \\
         MATCH_MP_TAC pos_fn_integral_indicator >> art [] \\
         rw [Abbr ‘M'’]) >> Rewr' \\
     MATCH_MP_TAC pos_fn_integral_mono \\
     rw [o_DEF, extreal_of_num_def, indicator_fn] \\
  (* final goal: f x <= indicator (A' e) x
     (1) if x IN (A' e), LHS <= 1, RHS = 1
     (2) if x NOTIN A' e, LHS = 0, RHS = 0
   *)
     Cases_on ‘x IN A' e’ >> rw [indicator] \\
     POP_ASSUM MP_TAC \\
     rw [Abbr ‘A'’, set_mcball_def, GSYM real_lt] \\
     Suff ‘f x = 0’ >- rw [] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art [])
 (* Y sp <= liminf (\n. X n sp)

    NOTE: This subgoal is trivial under ‘Portemanteau_antecedents_alt’
  *)
 >> fs [Portemanteau_antecedents_alt_def]
 (* applying PROB_UNIV *)
 >> qabbrev_tac ‘M = \n. (sp,subsets b,X n)’
 >> qabbrev_tac ‘M' = (sp,subsets b,Y)’
 >> Know ‘prob M' (p_space M') = 1’
 >- (MATCH_MP_TAC PROB_UNIV >> art [])
 >> simp [Abbr ‘M'’, p_space_def, prob_def]
 >> DISCH_TAC
 >> Know ‘!n. prob (M n) (p_space (M n)) = 1’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC PROB_UNIV >> fs [])
 >> simp [Abbr ‘M’, p_space_def, prob_def]
 >> rw [ext_liminf_const]
QED

(* NOTE: This lemma may be generated to metricTheory (or even topologyTheory) *)
Theorem frontier_of_preimage_subset :
    !E f D. mtop E frontier_of PREIMAGE f D SUBSET
            PREIMAGE f (frontier D) UNION U (mtop E) (f :'a -> real)
Proof
    rw [U_DEF, SUBSET_DEF, Once DISJ_SYM, TOPSPACE_MTOP]
 (* assuming f is continuous at x (the non-trivial case) *)
 >> STRONG_DISJ_TAC
 (* NOTE: Here we need an equivalent definition of “frontier_of”, saying a point x
    is at the frontier of D if any open set containing it must have two distinct
    points y, z such that y is inside D, and z is outside.
  *)
 >> simp [FRONTIER_STRADDLE]
 >> Q.X_GEN_TAC ‘e’
 >> DISCH_TAC
 >> fs [topcontinuous_at, TOPSPACE_EUCLIDEAN, GSYM euclidean_open_def]
 >> Q.PAT_X_ASSUM ‘!v. open v /\ f x IN v ==> _’ (MP_TAC o Q.SPEC ‘ball (f x,e)’)
 >> simp [OPEN_BALL, IN_BALL, DIST_REFL]
 >> STRIP_TAC
 (* applying FRONTIER_OF_OPEN_IN_STRADDLE_INTER *)
 >> qabbrev_tac ‘t = mtop E’
 >> qabbrev_tac ‘s = PREIMAGE f D’
 >> MP_TAC (Q.SPECL [‘t’, ‘s’, ‘u’] FRONTIER_OF_OPEN_IN_STRADDLE_INTER)
 >> simp [GSYM DISJOINT_DEF]
 >> impl_tac >- (simp [DISJOINT_ALT] >> Q.EXISTS_TAC ‘x’ >> art [])
 >> simp [DISJOINT_ALT, Abbr ‘s’, PREIMAGE_def, Once EXTENSION, IMP_CONJ]
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘y’ STRIP_ASSUME_TAC)
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘z’ STRIP_ASSUME_TAC)
 >> CONJ_TAC
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC ‘f y’ >> art [] \\
      FIRST_X_ASSUM MATCH_MP_TAC >> art [],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC ‘f z’ >> art [] \\
      FIRST_X_ASSUM MATCH_MP_TAC >> art [] ]
QED

(* hard *)
Theorem Portemanteau_vi_imp_iii :
    !E X Y. Portemanteau_antecedents E X Y /\
            Portemanteau_vi E X Y ==> Portemanteau_iii E X Y
Proof
    RW_TAC std_ss [Portemanteau_antecedents_def, Portemanteau_vi_def,
                   Portemanteau_iii_def, weak_convergence_condition_def]
 (* applying extreal_lim_sequentially_eq (and ext_limsup_thm) *)
 >> qmatch_abbrev_tac ‘(g --> l) sequentially’
 >> Know ‘(g --> l) sequentially <=> limsup g = l /\ liminf g = l’
 >- (MATCH_MP_TAC ext_limsup_thm' \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.X_GEN_TAC ‘n’ >> simp [Abbr ‘g’] \\
       qabbrev_tac ‘M = (space (B E),subsets (B E),X n)’ \\
      ‘measure_space M’ by PROVE_TAC [subprobability_measure_def] \\
       Suff ‘integrable M (Normal o f)’ >- METIS_TAC [integrable_finite_integral] \\
       MATCH_MP_TAC integrable_bounded \\
       fs [bounded_def, extreal_abs_def] \\
       Q.EXISTS_TAC ‘\x. Normal a’ >> simp [] \\
       CONJ_TAC
       >- (MATCH_MP_TAC integrable_const \\
           Know ‘finite_measure_space M’
           >- PROVE_TAC [subprobability_measure_imp_finite] \\
           rw [finite_measure_space_def, GSYM lt_infty]) \\
       CONJ_TAC
       >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
           simp [Abbr ‘M’, sigma_algebra_general_borel]) \\
       rpt STRIP_TAC \\
       FIRST_X_ASSUM MATCH_MP_TAC \\
       Q.EXISTS_TAC ‘x’ >> REWRITE_TAC [],
       (* goal 2 (of 2) *)
       qunabbrev_tac ‘l’ \\
       qabbrev_tac ‘M = (space (B E),subsets (B E),Y)’ \\
       ‘measure_space M’ by PROVE_TAC [subprobability_measure_def] \\
       Suff ‘integrable M (Normal o f)’ >- METIS_TAC [integrable_finite_integral] \\
       MATCH_MP_TAC integrable_bounded \\
       fs [bounded_def, extreal_abs_def] \\
       Q.EXISTS_TAC ‘\x. Normal a’ >> simp [] \\
       CONJ_TAC
       >- (MATCH_MP_TAC integrable_const \\
           Know ‘finite_measure_space M’
           >- PROVE_TAC [subprobability_measure_imp_finite] \\
           rw [finite_measure_space_def, GSYM lt_infty]) \\
       CONJ_TAC
       >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
           simp [Abbr ‘M’, sigma_algebra_general_borel]) \\
       rpt STRIP_TAC \\
       FIRST_X_ASSUM MATCH_MP_TAC \\
       Q.EXISTS_TAC ‘x’ >> REWRITE_TAC [] ])
 >> Rewr'
 >> Suff ‘limsup g <= l /\ l <= liminf g’
 >- (STRIP_TAC \\
    ‘liminf g <= limsup g’ by PROVE_TAC [ext_liminf_le_limsup] \\
    ‘liminf g <= l /\ l <= limsup g’ by PROVE_TAC [le_trans] \\
     METIS_TAC [le_antisym])
 >> qunabbrevl_tac [‘g’, ‘l’]
 (* stage work *)
 >> rename1 ‘f0 IN borel_measurable (B E)’
 >> Know ‘!f. bounded (IMAGE f univ(:'a)) /\
              f IN borel_measurable (B E) /\
              Y (U (mtop E) f) = 0 ==>
              limsup (\n. integral (space (B E),subsets (B E),X n) (Normal o f)) <=
              integral (space (B E),subsets (B E),Y) (Normal o f)’
 >- (Q.PAT_X_ASSUM ‘bounded (IMAGE _ univ(:'a))’ K_TAC \\
     Q.PAT_X_ASSUM ‘_ IN borel_measurable (B E)’ K_TAC \\
     Q.PAT_X_ASSUM ‘Y (U (mtop E) _) = 0’        K_TAC \\
     rpt STRIP_TAC \\
  (* define a (finite) measure by PREIMAGE of a measurable function *)
     qabbrev_tac ‘m = Y o PREIMAGE f’ \\
     Know ‘finite_measure_space (space borel,subsets borel,m)’
     >- (Know ‘finite_measure_space (space (B E),subsets (B E),Y)’
         >- PROVE_TAC [subprobability_measure_imp_finite] \\
         reverse (rw [finite_measure_space_def, space_general_borel, TOPSPACE_MTOP])
         >- rw [Abbr ‘m’, o_DEF, PREIMAGE_UNIV, space_borel] \\
         qabbrev_tac ‘M = (univ(:'a),subsets (B E),Y)’ \\
         rw [measure_space_def, SPACE, sigma_algebra_borel]
         >- (rw [positive_def, Abbr ‘m’]
             >- (‘Y {} = measure M {}’ by rw [Abbr ‘M’] >> POP_ORW \\
                 MATCH_MP_TAC MEASURE_EMPTY >> art []) \\
             Know ‘positive M’ >- PROVE_TAC [MEASURE_SPACE_POSITIVE] \\
             rw [positive_def, Abbr ‘M’] \\
             POP_ASSUM MATCH_MP_TAC \\
             Q.PAT_X_ASSUM ‘f IN borel_measurable (B E)’ MP_TAC \\
             rw [measurable_def, IN_FUNSET, space_general_borel, TOPSPACE_MTOP]) \\
         simp [countably_additive_def, IN_FUNSET, Abbr ‘m’, o_DEF] \\
         Q.X_GEN_TAC ‘g’ >> rw [PREIMAGE_BIGUNION, IMAGE_IMAGE] \\
         Know ‘countably_additive M’ >- PROVE_TAC [measure_space_def] \\
         rw [countably_additive_def, IN_FUNSET, Abbr ‘M’] \\
         qabbrev_tac ‘h = PREIMAGE f o g’ \\
        ‘(\x. Y (PREIMAGE f (g x))) = Y o h’ by rw [Abbr ‘h’, o_DEF, FUN_EQ_THM] \\
         POP_ORW >> FIRST_X_ASSUM MATCH_MP_TAC \\
         CONJ_ASM1_TAC (* !x. h x IN subsets (B E) *)
         >- (Q.X_GEN_TAC ‘n’ >> rw [Abbr ‘h’, o_DEF] \\
             Q.PAT_X_ASSUM ‘f IN borel_measurable (B E)’ MP_TAC \\
             rw [measurable_def, IN_FUNSET, space_general_borel, TOPSPACE_MTOP]) \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC SIGMA_ALGEBRA_ENUM \\
             rw [sigma_algebra_general_borel, IN_FUNSET]) \\
         POP_ASSUM K_TAC (* useless *) \\
         rw [Abbr ‘h’, o_DEF] \\
         MATCH_MP_TAC PREIMAGE_DISJOINT \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> DISCH_TAC \\
     qabbrev_tac ‘A = {y | 0 < m {y}}’ \\
  (* NOTE: This is just to make sure any interval of univ(:real) diff A has infinite
     many elements: uncountable DIFF countable = uncountable (thus INFINITE).
   *)
     Know ‘countable A’
     >- (qabbrev_tac ‘a = \n. {y | inv (&SUC n) < m {y}}’ \\
         Know ‘A = BIGUNION (IMAGE a UNIV)’
         >- (rw [Once EXTENSION, IN_BIGUNION_IMAGE, Abbr ‘A’, Abbr ‘a’] \\
             reverse EQ_TAC >> rw []
             >- (Q_TAC (TRANS_TAC lt_trans) ‘inv (&SUC n)’ >> art [] \\
                 MATCH_MP_TAC inv_pos' >> rw [extreal_of_num_def]) \\
             POP_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP EXTREAL_ARCH_INV)) \\
             Q.EXISTS_TAC ‘n’ >> art []) >> Rewr' \\
         CCONTR_TAC \\
         Know ‘?n. INFINITE (a n)’
         >- (CCONTR_TAC >> fs [] \\
             Q.PAT_X_ASSUM ‘uncountable (BIGUNION (IMAGE a UNIV))’ MP_TAC \\
             simp [] \\
             MATCH_MP_TAC bigunion_countable \\
             rw [COUNTABLE_IMAGE, COUNTABLE_NUM] \\
             MATCH_MP_TAC FINITE_IMP_COUNTABLE >> art []) >> STRIP_TAC \\
      (* applying infinite_num_inj *)
         POP_ASSUM (MP_TAC o REWRITE_RULE [infinite_num_inj]) \\
         DISCH_THEN (Q.X_CHOOSE_THEN ‘h’ MP_TAC) \\
         DISCH_THEN (STRIP_ASSUME_TAC o SRULE [INJ_DEF]) \\
      (* NOTE: The idea is to use enough (finite) number of elements from (a n) to
         go beyond (m UNIV), which is finite. *)
         qabbrev_tac ‘M = (space borel,subsets borel,m)’ \\
         qabbrev_tac ‘b = measure M (m_space M)’ \\
        ‘b <> PosInf’ by PROVE_TAC [finite_measure_space_def] \\
        ‘?N. b <= &N’ by METIS_TAC [SIMP_EXTREAL_ARCH] \\
         qabbrev_tac ‘g = \i. {h i}’ \\
         qabbrev_tac ‘k = SUC N * SUC n’ \\
        ‘0 < k’ by rw [Abbr ‘k’] \\
         Know ‘finite_additive M’
         >- PROVE_TAC [MEASURE_FINITE_ADDITIVE, finite_measure_space_def] \\
         DISCH_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [finite_additive_def]) \\
         POP_ASSUM (MP_TAC o Q.SPECL [‘g’, ‘k’]) \\
        ‘!i. i < k ==> g i IN measurable_sets M’
           by rw [Abbr ‘g’, Abbr ‘M’, borel_measurable_sets] \\
         qabbrev_tac ‘s = BIGUNION (IMAGE g (count k))’ \\
         Know ‘s IN measurable_sets M’
         >- (qunabbrev_tac ‘s’ \\
             MATCH_MP_TAC MEASURE_SPACE_FINITE_UNION >> art [] \\
             FULL_SIMP_TAC std_ss [finite_measure_space_def]) >> DISCH_TAC \\
         simp [] \\
         CONJ_TAC >- (rw [DISJOINT_ALT, Abbr ‘g’] >> METIS_TAC []) \\
         MATCH_MP_TAC lt_imp_ne \\
         Q_TAC (TRANS_TAC let_trans) ‘measure M (m_space M)’ \\
         CONJ_TAC
         >- (MATCH_MP_TAC MEASURE_INCREASING \\
              CONJ_ASM1_TAC >- FULL_SIMP_TAC std_ss [finite_measure_space_def] \\
              simp [MEASURE_SPACE_SPACE] \\
              simp [Abbr ‘M’, space_borel]) \\
          POP_ASSUM K_TAC (* now useless *) \\
          simp [Abbr ‘s’, Abbr ‘M’, o_DEF, Abbr ‘g’] \\
          Q_TAC (TRANS_TAC let_trans) ‘SIGMA (\i. inv (&SUC n)) (count k)’ \\
       (* applying EXTREAL_SUM_IMAGE_MONO_LT *)
          reverse CONJ_TAC
          >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_LT >> simp [] \\
              CONJ_TAC
              >- (DISJ1_TAC \\
                  Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
                  CONJ_TAC >> MATCH_MP_TAC pos_not_neginf
                  >- (MATCH_MP_TAC le_inv >> rw [extreal_of_num_def]) \\
                  qabbrev_tac ‘M = (space borel,subsets borel,m)’ \\
                  Know ‘positive M’
                  >- PROVE_TAC [finite_measure_space_def, MEASURE_SPACE_POSITIVE] \\
                  rw [positive_def, Abbr ‘M’] \\
                  POP_ASSUM MATCH_MP_TAC >> rw [borel_measurable_sets]) \\
              Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
              Q.PAT_X_ASSUM ‘!x. h x IN a n’ (MP_TAC o Q.SPEC ‘i’) \\
              simp [Abbr ‘a’]) \\
       (* applying EXTREAL_SUM_IMAGE_FINITE_CONST *)
          Know ‘SIGMA (\i. inv (&SUC n)) (count k) = &CARD (count k) * inv (&SUC n)’
          >- (irule EXTREAL_SUM_IMAGE_FINITE_CONST >> rw []) >> Rewr' \\
         ‘&SUC n <> (0 :real)’ by rw [] \\
          ASM_SIMP_TAC std_ss [CARD_COUNT, Abbr ‘k’, extreal_of_num_def,
                               GSYM REAL_OF_NUM_MUL, GSYM extreal_mul_eq,
                               GSYM mul_assoc, extreal_inv_eq] \\
         ‘Normal (&SUC n) * Normal (realinv (&SUC n)) = 1’
            by simp [extreal_of_num_def, extreal_mul_eq] \\
          simp [GSYM extreal_of_num_def] \\
          Q_TAC (TRANS_TAC le_trans) ‘&N’ >> art [] \\
          simp [extreal_of_num_def]) >> DISCH_TAC \\
  (* now get the (abs) bounds of f *)
     Know ‘?a. !x. abs (f x) <= a’
     >- (Q.PAT_X_ASSUM ‘bounded (IMAGE f UNIV)’ MP_TAC \\
         rw [bounded_def] \\
         Q.EXISTS_TAC ‘a’ >> METIS_TAC []) >> STRIP_TAC \\
     Know ‘0 <= a’ (* any bound must be non-negative *)
     >- (CCONTR_TAC >> fs [GSYM real_lt] \\
        ‘0 <= abs (f ARB)’ by simp [ABS_POS] \\
        ‘abs (f ARB) <= a’ by simp [] \\
        ‘0 <= a’ by PROVE_TAC [REAL_LE_TRANS] \\
         METIS_TAC [REAL_LET_ANTISYM]) >> DISCH_TAC \\
  (* NOTE: Here, for any e > 0, we want to divide (-a, a) into enough segments,
     by finding y(i) such that y(0) < -a, y(i+1) - y(i) < e, a < y(N), such that
     y(i) NOTIN A. This is possible by choose freely a point from each of the
     following open intervals: (also works when a = 0)

        y(0)    y(1)    y(2)                        y(N) ... (y is infinite)
     |--e/2--|--e/2--|--e/2--|...|--e/2--|--e/2--|--e/2--|   let e' = e/2
     b      -a <-------------- f -----------> a -|

     Note that the distance of two points from near intervals is small than e.
     The total length of these intervals is (2 * a) / (e / 2) + 2, rounded to
     the next integer (clg). Each interval misses at most countable points of A.
   *)
     Know ‘!e. 0 < e ==>
               ?N. 0 < N /\
                   ?y. y 0 < -a /\ a < y N /\
                      (!i. y i < y (SUC i) /\ y (SUC i) - y i < e) /\
                      (!i. m {y i} = 0)’
     >- (rpt STRIP_TAC \\
         qabbrev_tac ‘e' = e / 2’ \\
        ‘0 < e'’ by simp [Abbr ‘e'’, REAL_LT_DIV] \\
         qabbrev_tac ‘N :num = clg (a * 2 / e' + 2)’ \\
        ‘a * 2 / e' + 2 <= &N’ by rw [Abbr ‘N’, LE_NUM_CEILING] \\
         Q.EXISTS_TAC ‘N’ \\
        ‘0 <= a * 2 / e'’ by simp [REAL_LE_DIV, REAL_LT_IMP_LE] \\
         CONJ_ASM1_TAC (* 0 < N *)
         >- (Suff ‘(0 :real) < &N’ >- simp [] \\
             Q_TAC (TRANS_TAC REAL_LET_TRANS) ‘a * 2 / e'’ >> art [] \\
             Q_TAC (TRANS_TAC REAL_LTE_TRANS) ‘a * 2 / e' + 2’ >> art [] \\
             simp []) \\
         qabbrev_tac ‘b = -a - e'’ (* the left-most bound *) \\
         qabbrev_tac ‘g = \i. OPEN_interval (b + &i * e', b + &SUC i * e')’ \\
      (* applying UNCOUNTABLE_INTERVAL, UNCOUNTABLE_DIFF_COUNTABLE, etc. *)
         Know ‘!i. ?y. y IN g i DIFF A’
         >- (Q.X_GEN_TAC ‘i’ \\
            ‘g i <> {}’ by rw [Abbr ‘g’, INTERVAL_NE_EMPTY] \\
            ‘uncountable (g i)’ by METIS_TAC [UNCOUNTABLE_INTERVAL] \\
            ‘uncountable (g i DIFF A)’ by PROVE_TAC [UNCOUNTABLE_DIFF_COUNTABLE] \\
             Know ‘INFINITE (g i DIFF A)’ >- PROVE_TAC [FINITE_IMP_COUNTABLE] \\
             rw [INFINITE_INHAB]) \\
         Q.PAT_X_ASSUM ‘countable A’ K_TAC \\
         simp [SKOLEM_THM, Abbr ‘g’, IN_INTERVAL, Abbr ‘A’, extreal_lt_def] \\
         DISCH_THEN (Q.X_CHOOSE_THEN ‘y’
                      (STRIP_ASSUME_TAC o SIMP_RULE std_ss [FORALL_AND_THM])) \\
         Q.EXISTS_TAC ‘y’ \\
         CONJ_TAC (* y 0 < -a *)
         >- (Q.PAT_X_ASSUM ‘!i. y i < _’ (MP_TAC o Q.SPEC ‘0’) \\
             simp [Abbr ‘b’, REAL_SUB_ADD]) \\
         CONJ_TAC (* a < y N *)
         >- (Q.PAT_X_ASSUM ‘!i. _ < y i’ (STRIP_ASSUME_TAC o Q.SPEC ‘N’) \\
             Know ‘e' * (a * 2 / e' + 2) <= e' * &N’
             >- (ASM_SIMP_TAC std_ss [REAL_LE_LMUL]) \\
            ‘e' <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] \\
            ‘e' * (a * 2 / e' + 2) = 2 * a + 2 * e'’
               by simp [real_div, REAL_LDISTRIB] >> POP_ORW \\
             DISCH_TAC \\
             Q_TAC (TRANS_TAC REAL_LT_TRANS) ‘b + e' * &N’ >> art [] \\
             simp [REAL_ARITH “a < b + c <=> a - b < c:real”] \\
             Q_TAC (TRANS_TAC REAL_LTE_TRANS) ‘2 * a + 2 * e'’ >> art [] \\
             simp [Abbr ‘b’, real_sub, REAL_NEG_ADD, REAL_ADD_ASSOC, REAL_DOUBLE]) \\
         reverse CONJ_TAC (* m {y i} = 0 *)
         >- (rpt STRIP_TAC \\
             qabbrev_tac ‘M = (space borel,subsets borel,m)’ \\
             Know ‘positive M’
             >- (MATCH_MP_TAC MEASURE_SPACE_POSITIVE \\
                 FULL_SIMP_TAC std_ss [finite_measure_space_def]) \\
             rw [positive_def, Abbr ‘M’] \\
             POP_ASSUM (MP_TAC o Q.SPEC ‘{y (i :num)}’) \\
             rw [borel_measurable_sets] \\
             simp [GSYM le_antisym]) \\
         Q.X_GEN_TAC ‘i’ \\
         CONJ_ASM1_TAC (* y i < y (SUC i) *)
         >- (Q_TAC (TRANS_TAC REAL_LT_TRANS) ‘b + e' * &SUC i’ >> art []) \\
        ‘e = e' + e'’ by simp [REAL_HALF, REAL_DOUBLE, Abbr ‘e'’] >> POP_ORW \\
         simp [REAL_ARITH “a - b < e + e <=> a - e < b + (e :real)”] \\
         Q_TAC (TRANS_TAC REAL_LT_TRANS) ‘b + e' * &SUC i’ \\
         CONJ_TAC >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           simp [REAL_LT_SUB_RADD, GSYM REAL_ADD_ASSOC] \\
           Q_TAC (TRANS_TAC REAL_LTE_TRANS) ‘b + e' * &SUC (SUC i)’ >> art [] \\
           simp [REAL_LE_LADD] \\
          ‘&SUC (SUC i) = &SUC i + (1 :real)’ by simp [] >> POP_ORW \\
           simp [REAL_LDISTRIB],
           (* goal 2 (of 2) *)
          ‘&SUC i = &i + (1 :real)’ by simp [] >> POP_ORW \\
           simp [REAL_LDISTRIB, REAL_ADD_ASSOC] ]) >> DISCH_TAC \\
  (* stage work, now formally process the goal *)
     MATCH_MP_TAC le_epsilon >> rpt STRIP_TAC \\
    ‘e <> NegInf’ by PROVE_TAC [pos_not_neginf, lt_imp_le] \\
    ‘?r. 0 < r /\ e = Normal r’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] \\
     POP_ORW \\
     Q.PAT_X_ASSUM ‘!e. 0 < e ==> _’ (MP_TAC o Q.SPEC ‘r’) >> rw [] \\
     Know ‘!i j. i < j ==> y i < y j’
     >- (HO_MATCH_MP_TAC TRANSITIVE_STEPWISE_LT >> simp [] \\
         METIS_TAC [REAL_LT_TRANS]) >> DISCH_TAC \\
     qabbrev_tac ‘s = \i. right_open_interval (y i) (y (SUC i))’ \\
    ‘!i. s i IN subsets borel’
       by rw [Abbr ‘s’, right_open_interval, borel_measurable_sets] \\
     Know ‘!i. BIGUNION (IMAGE s (count1 i)) =
               right_open_interval (y 0) (y (SUC i))’
     >- (Induct_on ‘i’ >- simp [Abbr ‘s’, COUNT_ONE] \\
         rw [Once COUNT_SUC, Abbr ‘s’] \\
         rw [Once EXTENSION, in_right_open_interval] \\
         EQ_TAC >> rpt STRIP_TAC >> rw [] >| (* 3 subgoals *)
         [ (* goal 1 (of 3) *)
           Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘y (SUC i)’ >> art [] \\
           MATCH_MP_TAC REAL_LT_IMP_LE >> simp [],
           (* goal 2 (of 3) *)
           Q_TAC (TRANS_TAC REAL_LT_TRANS) ‘y (SUC i)’ >> simp [],
           (* goal 3 (of 3) *)
           METIS_TAC [REAL_LET_TOTAL] ]) >> DISCH_TAC \\
     qabbrev_tac ‘h = \i. PREIMAGE f (s i)’ \\
     Know ‘!i. h i IN subsets (B E)’
     >- (Q.PAT_X_ASSUM ‘f IN borel_measurable (B E)’ MP_TAC \\
         rw [measurable_def, Abbr ‘h’, space_general_borel, IN_FUNSET,
             TOPSPACE_MTOP, space_borel]) >> DISCH_TAC \\
     Know ‘!i n. X n (h i) <> PosInf /\ X n (h i) <> NegInf’
     >- (rpt GEN_TAC \\
         qabbrev_tac ‘M = (space (B E),subsets (B E),X n)’ \\
         Know ‘finite_measure_space M’
         >- PROVE_TAC [subprobability_measure_imp_finite] \\
         simp [Abbr ‘M’, finite_measure_space_thm]) >> DISCH_TAC \\
     Know ‘!i. Y (h i) <> PosInf /\ Y (h i) <> NegInf’
     >- (Q.X_GEN_TAC ‘i’ \\
         qabbrev_tac ‘M = (space (B E),subsets (B E),Y)’ \\
         Know ‘finite_measure_space M’
         >- PROVE_TAC [subprobability_measure_imp_finite] \\
         simp [Abbr ‘M’, finite_measure_space_thm]) >> DISCH_TAC \\
     Know ‘BIGUNION (IMAGE h (count N)) = UNIV’
     >- (rw [Once EXTENSION, IN_BIGUNION_IMAGE] \\
         simp [Abbr ‘h’, IN_PREIMAGE, in_right_open_interval] \\
         Know ‘interval [-a,a] SUBSET right_open_interval (y 0) (y N)’
         >- (rw [SUBSET_DEF, IN_INTERVAL, in_right_open_interval]
             >- (Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘-a’ \\
                 simp [REAL_LT_IMP_LE]) \\
             Q_TAC (TRANS_TAC REAL_LET_TRANS) ‘a’ >> art []) >> DISCH_TAC \\
        ‘!x. f x IN interval [-a,a]’ by fs [ABS_BOUNDS, IN_INTERVAL] \\
         Know ‘f x IN right_open_interval (y 0) (y N)’ >- METIS_TAC [SUBSET_DEF] \\
         Cases_on ‘N’ >> fs [] \\
         Q.PAT_X_ASSUM ‘!i. BIGUNION (IMAGE s (count1 i)) = _’
           (REWRITE_TAC o wrap o GSYM) \\
         simp [IN_BIGUNION_IMAGE, IN_COUNT]) >> DISCH_TAC \\
  (* applying integral_disjoint_sets_sum *)
     qabbrev_tac ‘f' = Normal o f’ \\
     Know ‘!n. integrable (space (B E),subsets (B E),X n) f'’
     >- (Q.X_GEN_TAC ‘n’ \\
         qabbrev_tac ‘M = (space (B E),subsets (B E),X n)’ \\
         MATCH_MP_TAC integrable_bounded \\
         Q.EXISTS_TAC ‘\x. Normal a’ >> simp [extreal_abs_def, Abbr ‘f'’] \\
         Know ‘finite_measure_space M’
         >- PROVE_TAC [subprobability_measure_imp_finite] \\
         simp [finite_measure_space_def, lt_infty] >> STRIP_TAC \\
         CONJ_TAC >- (MATCH_MP_TAC integrable_const >> art []) \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
         simp [Abbr ‘M’, sigma_algebra_general_borel]) >> DISCH_TAC \\
     Know ‘integrable (space (B E),subsets (B E),Y) f'’
     >- (qabbrev_tac ‘M = (space (B E),subsets (B E),Y)’ \\
         MATCH_MP_TAC integrable_bounded \\
         Q.EXISTS_TAC ‘\x. Normal a’ >> simp [extreal_abs_def, Abbr ‘f'’] \\
         Know ‘finite_measure_space M’
         >- PROVE_TAC [subprobability_measure_imp_finite] \\
         simp [finite_measure_space_def, lt_infty] >> STRIP_TAC \\
         CONJ_TAC >- (MATCH_MP_TAC integrable_const >> art []) \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
         simp [Abbr ‘M’, sigma_algebra_general_borel]) >> DISCH_TAC \\
     Know ‘!n. integral (space (B E),subsets (B E),X n) f' =
               integral (space (B E),subsets (B E),X n)
                        (\x. f' x * indicator_fn UNIV x)’
     >- rw [INDICATOR_FN_UNIV, ETA_THM] >> Rewr' \\
     Q.PAT_ASSUM ‘_ = UNIV’ (REWRITE_TAC o wrap o SYM) \\
     qabbrev_tac ‘J = count N’ \\
     Know ‘!n. integral (space (B E),subsets (B E),X n)
                        (\x. f' x * indicator_fn (BIGUNION (IMAGE h J)) x) =
               SIGMA (\i. integral (space (B E),subsets (B E),X n)
                                   (\x. f' x * indicator_fn (h i) x)) J’
     >- (Q.X_GEN_TAC ‘n’ \\
         MATCH_MP_TAC integral_disjoint_sets_sum \\
         fs [Abbr ‘J’, subprobability_measure_def] \\
         simp [disjoint_family_on_def] \\
         rw [Abbr ‘h’] >> MATCH_MP_TAC PREIMAGE_DISJOINT \\
         rw [DISJOINT_ALT, Abbr ‘s’, in_right_open_interval] \\
         simp [REAL_NOT_LE, REAL_NOT_LT] \\
        ‘i < j \/ j < i’ by simp [] >| (* 2 subgoals *)
         [ (* goal 1 (of 2): y i <= x < y (SUC i) <= y j *)
           DISJ1_TAC \\
          ‘SUC i <= j’ by simp [] \\
          ‘j = SUC i \/ SUC i < j’ by simp [] >- simp [] \\
           Q_TAC (TRANS_TAC REAL_LT_TRANS) ‘y (SUC i)’ >> simp [],
           (* goal 2 (of 2): y (SUC j) < y i <= x < y (SUC i) *)
           DISJ2_TAC \\
          ‘SUC j <= i’ by simp [] \\
          ‘SUC j = i \/ SUC j < i’ by simp [] >- simp [] \\
           Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘y i’ \\
           simp [REAL_LT_IMP_LE] ]) >> Rewr' \\
  (* applying ext_limsup_mono and EXTREAL_SUM_IMAGE_MONO *)
     Q_TAC (TRANS_TAC le_trans)
           ‘limsup (\n. SIGMA (\i. X n (h i) * Normal (y (SUC i))) J)’ \\
     CONJ_TAC
     >- (MATCH_MP_TAC ext_limsup_mono >> rw [] \\
         irule EXTREAL_SUM_IMAGE_MONO >> simp [Abbr ‘J’] \\
         reverse CONJ_TAC
         >- (DISJ2_TAC >> Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
             CONJ_TAC
             >- (qmatch_abbrev_tac ‘integral M f2 <> PosInf’ \\
                ‘measure_space M’ by PROVE_TAC [subprobability_measure_def] \\
                 Suff ‘integrable M f2’ >- METIS_TAC [integrable_finite_integral] \\
                 qunabbrev_tac ‘f2’ \\
                 MATCH_MP_TAC integrable_mul_indicator >> simp [Abbr ‘M’]) \\
            ‘?r. X n (h i) = Normal r’ by METIS_TAC [extreal_cases] \\
             simp [extreal_mul_eq]) \\
         Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
         qabbrev_tac ‘c = y (SUC i)’ \\
        ‘X n (h i) * Normal c = Normal c * X n (h i)’
           by simp [Once mul_comm] >> POP_ORW \\
         qabbrev_tac ‘M = (space (B E),subsets (B E),X n)’ \\
        ‘X n (h i) = measure M (h i)’ by simp [Abbr ‘M’] >> POP_ORW \\
         Know ‘finite_measure_space M’
         >- PROVE_TAC [subprobability_measure_imp_finite] \\
         rw [finite_measure_space_thm] \\
      (* applying integral_cmul_indicator *)
         Know ‘Normal c * measure M (h i) =
               integral M (\x. Normal c * indicator_fn (h i) x)’
         >- (SYM_TAC >> MATCH_MP_TAC integral_cmul_indicator >> art [] \\
             CONJ_ASM1_TAC >- simp [Abbr ‘M’] \\
             simp [GSYM lt_infty]) >> Rewr' \\
         MATCH_MP_TAC integral_mono >> simp [] \\
         CONJ_TAC >- (MATCH_MP_TAC integrable_mul_indicator >> simp [Abbr ‘M’]) \\
         CONJ_TAC
         >- (HO_MATCH_MP_TAC integrable_mul_indicator >> art [] \\
             CONJ_TAC >- simp [Abbr ‘M’] \\
             MATCH_MP_TAC integrable_const >> art [] \\
             REWRITE_TAC [GSYM lt_infty] \\
             Suff ‘m_space M IN measurable_sets M’ >- rw [] \\
             simp [MEASURE_SPACE_SPACE]) \\
         Q.X_GEN_TAC ‘z’ \\
         rw [Abbr ‘M’, Abbr ‘f'’, Abbr ‘h’, Abbr ‘s’, Abbr ‘c’, PREIMAGE_def,
             in_right_open_interval] \\
         qabbrev_tac ‘s = {x | y i <= f x /\ f x < y (SUC i)}’ \\
         reverse (Cases_on ‘z IN s’) >- simp [indicator_fn_def] \\
         POP_ASSUM MP_TAC >> rw [Abbr ‘s’, indicator_fn_def] \\
         MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
  (* applying frontier_of_preimage_subset *)
     Know ‘!i. Y (mtop E frontier_of (h i)) = 0’
     >- (rw [Abbr ‘h’] \\
         qmatch_abbrev_tac ‘Y s1 = 0’ \\
        ‘s1 IN subsets (B E)’ by rw [Abbr ‘s1’, frontier_of_in_general_borel] \\
         reverse (rw [GSYM le_antisym])
         >- (qabbrev_tac ‘M = (space (B E),subsets (B E),Y)’ \\
             Know ‘positive M’
             >- (MATCH_MP_TAC MEASURE_SPACE_POSITIVE \\
                 FULL_SIMP_TAC std_ss [subprobability_measure_def]) \\
             rw [positive_def, Abbr ‘M’]) \\
         MP_TAC (Q.SPECL [‘E’, ‘f’, ‘s (i :num)’] frontier_of_preimage_subset) \\
         qmatch_abbrev_tac ‘_ SUBSET s2 ==> _’ >> rw [] \\
         qabbrev_tac ‘M = (space (B E),subsets (B E),Y)’ \\
        ‘Y s1 = measure M s1’ by rw [Abbr ‘M’] >> POP_ORW \\
         Q_TAC (TRANS_TAC le_trans) ‘measure M s2’ \\
         CONJ_TAC
         >- (Know ‘increasing M’
             >- (MATCH_MP_TAC MEASURE_SPACE_INCREASING \\
                 FULL_SIMP_TAC std_ss [subprobability_measure_def]) \\
             rw [increasing_def] \\
             POP_ASSUM MATCH_MP_TAC >> simp [Abbr ‘M’, Abbr ‘s2’] \\
             MATCH_MP_TAC SIGMA_ALGEBRA_UNION \\
             simp [points_of_discontinuity_in_general_borel] \\
             Q.PAT_X_ASSUM ‘f IN borel_measurable (B E)’ MP_TAC \\
             rw [measurable_def, space_general_borel, TOPSPACE_MTOP,
                 IN_FUNSET, space_borel] \\
             POP_ASSUM MATCH_MP_TAC \\
             REWRITE_TAC [borel_frontier]) \\
         Q.PAT_X_ASSUM ‘s1 SUBSET s2’        K_TAC \\
         Q.PAT_X_ASSUM ‘s1 IN subsets (B E)’ K_TAC \\
         simp [Abbr ‘s1’, Abbr ‘s2’, Abbr ‘f'’, Abbr ‘J’] \\
         qmatch_abbrev_tac ‘measure M (s3 UNION s4) <= 0’ \\
         Q_TAC (TRANS_TAC le_trans) ‘measure M s3 + measure M s4’ \\
         CONJ_TAC
         >- (Know ‘subadditive M’
             >- (MATCH_MP_TAC MEASURE_SPACE_SUBADDITIVE \\
                 FULL_SIMP_TAC std_ss [subprobability_measure_def]) \\
             SIMP_TAC (srw_ss()) [Abbr ‘M’, subadditive_def] \\
             DISCH_THEN MATCH_MP_TAC \\
             CONJ_ASM1_TAC
             >- (Q.PAT_X_ASSUM ‘f IN borel_measurable (B E)’ MP_TAC \\
                 rw [measurable_def, space_general_borel, TOPSPACE_MTOP,
                     IN_FUNSET, space_borel, Abbr ‘s3’] \\
                 POP_ASSUM MATCH_MP_TAC \\
                 REWRITE_TAC [borel_frontier]) \\
             CONJ_ASM1_TAC
             >- simp [Abbr ‘s4’, points_of_discontinuity_in_general_borel] \\
             MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> simp []) \\
         simp [Abbr ‘M’, Abbr ‘s3’] \\
         qmatch_abbrev_tac ‘Y (PREIMAGE f s5) <= 0’ \\
        ‘Y (PREIMAGE f s5) = m s5’ by simp [Abbr ‘m’, o_DEF] >> POP_ORW \\
      (* applying right_open_interval_frontier *)
         Know ‘s5 = {y i; y (SUC i)}’
         >- (simp [Abbr ‘s5’, Abbr ‘s’] \\
             MATCH_MP_TAC right_open_interval_frontier >> simp []) >> Rewr' \\
         qunabbrevl_tac [‘s4’, ‘s5’] \\
         qabbrev_tac ‘M = (space borel,subsets borel,m)’ \\
        ‘measure_space M’ by PROVE_TAC [finite_measure_space_def] \\
         qmatch_abbrev_tac ‘m s6 <= 0’ \\
        ‘m s6 = measure M s6’ by simp [Abbr ‘M’] >> POP_ORW \\
         qunabbrev_tac ‘s6’ \\
         Q_TAC (TRANS_TAC le_trans) ‘measure M {y i} + measure M {y (SUC i)}’ \\
         CONJ_TAC
         >- (Know ‘subadditive M’
             >- (MATCH_MP_TAC MEASURE_SPACE_SUBADDITIVE >> art []) \\
             rw [subadditive_def] \\
            ‘{y i; y (SUC i)} = {y i} UNION {y (SUC i)}’ by SET_TAC [] \\
             POP_ORW \\
             FIRST_X_ASSUM MATCH_MP_TAC \\
             CONJ_ASM1_TAC >- simp [Abbr ‘M’, borel_measurable_sets] \\
             CONJ_ASM1_TAC >- simp [Abbr ‘M’, borel_measurable_sets] \\
             MATCH_MP_TAC MEASURE_SPACE_UNION >> art []) \\
         simp [Abbr ‘M’]) >> DISCH_TAC \\
  (* applying lim_sequentially_cmul and lim_sequentially_sum *)
     Know ‘!i. ((\n. X n (h i) * Normal (y (SUC i))) -->
                (Y (h i) * Normal (y (SUC i)))) sequentially’
     >- (Q.X_GEN_TAC ‘i’ \\
         ONCE_REWRITE_TAC [mul_comm] \\
         HO_MATCH_MP_TAC lim_sequentially_cmul >> simp []) \\
     qabbrev_tac ‘ff = \i n. X n (h i) * Normal (y (SUC i))’ \\
     qabbrev_tac ‘ll = \i. Y (h i) * Normal (y (SUC i))’ \\
     simp [] \\
    ‘!i. (\n. ff i n) = ff i’ by rw [FUN_EQ_THM] >> POP_ORW \\
     DISCH_TAC \\
     Know ‘((\n. SIGMA (\i. ff i n) J) --> SIGMA ll J) sequentially’
     >- (MATCH_MP_TAC lim_sequentially_sum >> simp [Abbr ‘J’] \\
         reverse CONJ_TAC
         >- (Q.X_GEN_TAC ‘i’ >> simp [Abbr ‘ll’] \\
            ‘?r. Y (h i) = Normal r’ by METIS_TAC [extreal_cases] \\
             simp [extreal_mul_eq]) \\
         rpt GEN_TAC >> DISCH_TAC \\
         simp [Abbr ‘ff’] \\
        ‘?r. X n (h i) = Normal r’ by METIS_TAC [extreal_cases] \\
         simp [extreal_mul_eq]) \\
  (* applying ext_limsup_thm' *)
     qmatch_abbrev_tac ‘(gg --> mm) sequentially ==> _’ \\
     Know ‘((gg --> mm) sequentially <=> limsup gg = mm /\ liminf gg = mm)’
     >- (MATCH_MP_TAC ext_limsup_thm' \\
         CONJ_TAC
         >- (rw [Abbr ‘gg’, Abbr ‘ff’] >| (* 2 subgoals *)
             [ (* goal 1 (of 2) *)
               MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> simp [Abbr ‘J’] \\
               Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
              ‘?r. X n (h i) = Normal r’ by METIS_TAC [extreal_cases] \\
               simp [extreal_mul_eq],
               (* goal 2 (of 2) *)
               MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF >> simp [Abbr ‘J’] \\
               Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
              ‘?r. X n (h i) = Normal r’ by METIS_TAC [extreal_cases] \\
               simp [extreal_mul_eq] ]) \\
          rw [Abbr ‘mm’, Abbr ‘ll’] >| (* 2 subgoals *)
          [ (* goal 1 (of 2) *)
             MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> simp [Abbr ‘J’] \\
             Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
            ‘?r. Y (h i) = Normal r’ by METIS_TAC [extreal_cases] \\
             simp [extreal_mul_eq],
             (* goal 2 (of 2) *)
             MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF >> simp [Abbr ‘J’] \\
             Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
            ‘?r. Y (h i) = Normal r’ by METIS_TAC [extreal_cases] \\
             simp [extreal_mul_eq] ]) >> Rewr' \\
     rw [Abbr ‘gg’, Abbr ‘mm’] \\
     NTAC 3 (POP_ASSUM K_TAC) \\
     qunabbrevl_tac [‘ll’, ‘ff’, ‘f'’] \\
  (* stage work, now rewrite RHS and only Y remains in both LHS and RHS *)
     Q.PAT_X_ASSUM ‘!n. integrable _ (Normal o f)’ K_TAC \\
     qabbrev_tac ‘M = (space (B E),subsets (B E),Y)’ \\
    ‘measure_space M’ by PROVE_TAC [subprobability_measure_def] \\
     Q_TAC (TRANS_TAC le_trans)
           ‘integral M (Normal o f) + integral M (\x. Normal r)’ \\
     reverse CONJ_TAC
     >- (MATCH_MP_TAC le_ladd_imp \\
         Know ‘integral M (\x. Normal r) = Normal r * measure M (m_space M)’
         >- (MATCH_MP_TAC integral_const \\
             Know ‘finite_measure_space M’
             >- PROVE_TAC [subprobability_measure_imp_finite] \\
             rw [finite_measure_space_def, lt_infty]) >> Rewr' \\
         GEN_REWRITE_TAC
           (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM mul_rone] \\
         MATCH_MP_TAC le_lmul_imp \\
         CONJ_TAC >- simp [extreal_of_num_def, REAL_LT_IMP_LE] \\
         fs [subprobability_measure_def]) \\
     Know ‘integral M (Normal o f) + integral M (\x. Normal r) =
           integral M (\x. (Normal o f) x + (\x. Normal r) x)’
     >- (SYM_TAC >> MATCH_MP_TAC integral_add' >> art [] \\
         MATCH_MP_TAC integrable_const \\
         Know ‘finite_measure_space M’
         >- PROVE_TAC [subprobability_measure_imp_finite] \\
         rw [finite_measure_space_def, lt_infty]) >> Rewr' \\
     qmatch_abbrev_tac ‘_ <= integral M g’ \\
     Know ‘integrable M g’
     >- (qunabbrev_tac ‘g’ \\
         MATCH_MP_TAC integrable_add' >> art [] \\
         MATCH_MP_TAC integrable_const \\
         Know ‘finite_measure_space M’
         >- PROVE_TAC [subprobability_measure_imp_finite] \\
         rw [finite_measure_space_def, lt_infty]) >> DISCH_TAC \\
  (* applying integral_disjoint_sets_sum, again *)
     Know ‘integral M g = integral M (\x. g x * indicator_fn UNIV x)’
     >- rw [INDICATOR_FN_UNIV, ETA_THM] >> Rewr' \\
     Q.PAT_X_ASSUM ‘_ = UNIV’ (REWRITE_TAC o wrap o SYM) \\
     Know ‘integral M (\x. g x * indicator_fn (BIGUNION (IMAGE h J)) x) =
           SIGMA (\i. integral M (\x. g x * indicator_fn (h i) x)) J’
     >- (MATCH_MP_TAC integral_disjoint_sets_sum \\
         simp [Abbr ‘J’, disjoint_family_on_def, Abbr ‘M’] \\
         rw [Abbr ‘h’] >> MATCH_MP_TAC PREIMAGE_DISJOINT \\
         rw [DISJOINT_ALT, Abbr ‘s’, in_right_open_interval] \\
         simp [REAL_NOT_LE, REAL_NOT_LT] \\
        ‘i < j \/ j < i’ by simp [] >| (* 2 subgoals *)
         [ (* goal 1 (of 2): y i <= x < y (SUC i) <= y j *)
           DISJ1_TAC \\
          ‘SUC i <= j’ by simp [] \\
          ‘j = SUC i \/ SUC i < j’ by simp [] >- simp [] \\
           Q_TAC (TRANS_TAC REAL_LT_TRANS) ‘y (SUC i)’ >> simp [],
           (* goal 2 (of 2): y (SUC j) < y i <= x < y (SUC i) *)
           DISJ2_TAC \\
          ‘SUC j <= i’ by simp [] \\
          ‘SUC j = i \/ SUC j < i’ by simp [] >- simp [] \\
           Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘y i’ \\
           simp [REAL_LT_IMP_LE] ]) >> Rewr' \\
  (* applying EXTREAL_SUM_IMAGE_MONO, again *)
     irule EXTREAL_SUM_IMAGE_MONO >> simp [Abbr ‘J’] \\
     reverse CONJ_TAC
     >- (DISJ2_TAC \\
         Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
        ‘?z. Y (h i) = Normal z’ by METIS_TAC [extreal_cases] \\
         simp [extreal_mul_eq] \\
         qmatch_abbrev_tac ‘integral M g' <> PosInf’ \\
         Suff ‘integrable M g'’ >- METIS_TAC [integrable_finite_integral] \\
         qunabbrev_tac ‘g'’ \\
         MATCH_MP_TAC integrable_mul_indicator >> simp [Abbr ‘M’]) \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
    ‘Y (h i) = measure M (h i)’ by simp [Abbr ‘M’] >> POP_ORW \\
     Know ‘measure M (h i) = integral M (indicator_fn (h i))’
     >- (SYM_TAC >> MATCH_MP_TAC integral_indicator \\
         simp [Abbr ‘M’]) >> Rewr' \\
     simp [Once mul_comm] \\
     qabbrev_tac ‘c = y (SUC i)’ \\
     Know ‘Normal c * integral M (indicator_fn (h i)) =
           integral M (\x. Normal c * indicator_fn (h i) x)’
     >- (SYM_TAC >> MATCH_MP_TAC integral_cmul >> art [] \\
         MATCH_MP_TAC integrable_indicator \\
         Know ‘finite_measure_space M’
         >- PROVE_TAC [subprobability_measure_imp_finite] \\
         rw [Abbr ‘M’, finite_measure_space_def, GSYM lt_infty]) >> Rewr' \\
     MATCH_MP_TAC integral_mono >> simp [] \\
     CONJ_TAC
     >- (MATCH_MP_TAC integrable_cmul >> art [] \\
         MATCH_MP_TAC integrable_indicator \\
         Know ‘finite_measure_space M’
         >- PROVE_TAC [subprobability_measure_imp_finite] \\
         rw [Abbr ‘M’, finite_measure_space_def, GSYM lt_infty]) \\
     CONJ_TAC
     >- (MATCH_MP_TAC integrable_mul_indicator >> simp [Abbr ‘M’]) \\
     Q.PAT_X_ASSUM ‘integrable M g’ K_TAC \\
     rw [Abbr ‘g’, o_DEF] \\
     Cases_on ‘x IN h i’ >> simp [indicator_fn_def, Abbr ‘c’, extreal_add_def] \\
     Q.PAT_X_ASSUM ‘x IN h i’ MP_TAC \\
     Q.PAT_X_ASSUM ‘!i. h i IN subsets (B E)’ K_TAC \\
     rw [Abbr ‘h’, IN_PREIMAGE, Abbr ‘s’, in_right_open_interval] \\
     Q.PAT_X_ASSUM ‘!i. _ /\ y (SUC i) - y i < r’ (MP_TAC o Q.SPEC ‘i’) \\
     simp [REAL_LT_SUB_RADD] >> DISCH_TAC \\
     Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘r + y i’ \\
     simp [REAL_LT_IMP_LE] \\
     Q.PAT_X_ASSUM ‘y i <= f x’ MP_TAC >> REAL_ARITH_TAC)
 (* stage work *)
 >> DISCH_TAC
 >> CONJ_TAC >- (POP_ASSUM MATCH_MP_TAC >> art [])
 >> qabbrev_tac ‘g0 = \x. -f0 x’
 >> ‘f0 = (\x. -g0 x)’ by rw [Abbr ‘g0’, FUN_EQ_THM] >> POP_ORW
 >> simp [o_DEF, GSYM extreal_ainv_def]
 >> Know ‘integral (space (B E),subsets (B E),Y) (\x. -Normal (g0 x)) =
          -integral (space (B E),subsets (B E),Y) (Normal o g0)’
 >- (simp [neg_minus1', o_DEF] \\
     HO_MATCH_MP_TAC integral_cmul \\
     qabbrev_tac ‘M = (space (B E),subsets (B E),Y)’ \\
     CONJ_ASM1_TAC >- fs [subprobability_measure_def] \\
     MATCH_MP_TAC integrable_bounded \\
     fs [bounded_def, extreal_abs_def, Abbr ‘g0’] \\
     Q.EXISTS_TAC ‘\x. Normal a’ >> simp [] \\
     CONJ_TAC
     >- (MATCH_MP_TAC integrable_const >> art [] \\
         Know ‘finite_measure_space M’
         >- PROVE_TAC [subprobability_measure_imp_finite] \\
         rw [finite_measure_space_def, lt_infty]) \\
     CONJ_TAC
     >- (HO_MATCH_MP_TAC (REWRITE_RULE [o_DEF] IN_MEASURABLE_BOREL_IMP_BOREL) \\
         MATCH_MP_TAC in_borel_measurable_ainv \\
         simp [Abbr ‘M’, sigma_algebra_general_borel]) \\
     rpt STRIP_TAC >> FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘x’ >> REWRITE_TAC [])
 >> Rewr'
 >> Know ‘!n. integral (space (B E),subsets (B E),X n) (\x. -Normal (g0 x)) =
              -integral (space (B E),subsets (B E),X n) (Normal o g0)’
 >- (Q.X_GEN_TAC ‘n’ \\
     simp [neg_minus1', o_DEF] \\
     HO_MATCH_MP_TAC integral_cmul \\
     qabbrev_tac ‘M = (space (B E),subsets (B E),X n)’ \\
     CONJ_ASM1_TAC >- fs [subprobability_measure_def, Abbr ‘M’] \\
     MATCH_MP_TAC integrable_bounded \\
     fs [bounded_def, extreal_abs_def, Abbr ‘g0’] \\
     Q.EXISTS_TAC ‘\x. Normal a’ >> simp [] \\
     CONJ_TAC
     >- (MATCH_MP_TAC integrable_const >> art [] \\
         Know ‘finite_measure_space M’
         >- PROVE_TAC [subprobability_measure_imp_finite] \\
         rw [finite_measure_space_def, lt_infty]) \\
     CONJ_TAC
     >- (HO_MATCH_MP_TAC (REWRITE_RULE [o_DEF] IN_MEASURABLE_BOREL_IMP_BOREL) \\
         MATCH_MP_TAC in_borel_measurable_ainv \\
         simp [Abbr ‘M’, sigma_algebra_general_borel]) \\
     rpt STRIP_TAC >> FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘x’ >> REWRITE_TAC [])
 >> Rewr'
 >> simp [ext_liminf_alt_limsup, o_DEF, neg_neg, le_neg]
 >> ‘(\x. Normal (g0 x)) = Normal o g0’ by rw [o_DEF, FUN_EQ_THM] >> POP_ORW
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> simp [Abbr ‘g0’]
 >> CONJ_TAC
 >- (fs [bounded_def] \\
     Q.EXISTS_TAC ‘a’ >> rw [] \\
     simp [ABS_NEG] \\
     rename1 ‘abs (f0 y) <= a’ \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘y’ >> REWRITE_TAC [])
 >> CONJ_TAC
 >- (MATCH_MP_TAC in_borel_measurable_ainv >> art [] \\
     REWRITE_TAC [sigma_algebra_general_borel])
 >> Suff ‘U (mtop E) (\x. -f0 x) = U (mtop E) f0’ >- rw []
 >> rw [U_DEF, Once EXTENSION]
 >> Suff ‘!x. topcontinuous_at (mtop E) euclidean f0 x <=>
              topcontinuous_at (mtop E) euclidean (\x. -f0 x) x’
 >- METIS_TAC []
 >> Suff ‘!f x. topcontinuous_at (mtop E) euclidean f x ==>
                topcontinuous_at (mtop E) euclidean (\x. -f x) x’
 >- (DISCH_TAC \\
     Q.X_GEN_TAC ‘x’ >> EQ_TAC >> STRIP_TAC
     >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     qabbrev_tac ‘g0 = \x. -f0 x’ \\
    ‘f0 = (\x. -g0 x)’ by rw [Abbr ‘g0’, FUN_EQ_THM] >> POP_ORW \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> KILL_TAC
 (* final goal: if f is continuous at x, so is -f *)
 >> rw [topcontinuous_at, GSYM euclidean_open_def, TOPSPACE_EUCLIDEAN]
 >> Q.PAT_X_ASSUM ‘open v’ (MP_TAC o REWRITE_RULE [open_def])
 >> qabbrev_tac ‘z = -f x’
 >> DISCH_THEN (MP_TAC o Q.SPEC ‘z’) >> rw []
 >> qabbrev_tac ‘s = IMAGE numeric_negate (ball (z,e))’
 >> Know ‘f x IN s’
 >- (rw [Abbr ‘s’, IN_BALL] \\
     Q.EXISTS_TAC ‘-f x’ >> rw [REAL_NEG_NEG, Abbr ‘z’, DIST_REFL])
 >> DISCH_TAC
 >> Know ‘open s’
 >- (Suff ‘s = ball (-z,e)’ >- rw [OPEN_BALL] \\
     rw [Abbr ‘s’, Once EXTENSION, Abbr ‘z’, IN_BALL] \\
     EQ_TAC >> rw [dist] >- (POP_ASSUM MP_TAC >> REAL_ARITH_TAC) \\
     rename1 ‘abs (f x - y) < e’ \\
     Q.EXISTS_TAC ‘-y’ >> simp [] \\
     POP_ASSUM MP_TAC >> REAL_ARITH_TAC)
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘!v. open v /\ f x IN v ==> _’ (MP_TAC o Q.SPEC ‘s’)
 >> rw []
 >> Q.EXISTS_TAC ‘u’ >> art []
 >> Q.X_GEN_TAC ‘y’ >> DISCH_TAC
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.PAT_X_ASSUM ‘!y. y IN u ==> f y IN s’ (MP_TAC o Q.SPEC ‘y’)
 >> rw [Abbr ‘s’, IN_BALL, dist]
 >> Q.PAT_X_ASSUM ‘f y = _’ (simp o wrap)
 >> POP_ASSUM MP_TAC >> REAL_ARITH_TAC
QED

(* NOTE: (2) ==> (4) <=> (5) ==> (6) ==> (3) ==> (1) ==> (2) *)
Theorem Portemanteau_i_eq_ii :
    !E X Y. Portemanteau_antecedents_alt E X Y ==>
           (Portemanteau_i E X Y <=> Portemanteau_ii E X Y)
Proof
    rpt STRIP_TAC
 >> ‘Portemanteau_antecedents E X Y’
      by PROVE_TAC [Portemanteau_antecedents_alt_imp_antecedents]
 >> EQ_TAC >> rw [Portemanteau_i_imp_ii]
 >> MATCH_MP_TAC Portemanteau_iii_imp_i  >> art []
 >> MATCH_MP_TAC Portemanteau_vi_imp_iii >> art []
 >> MATCH_MP_TAC Portemanteau_v_imp_vi   >> art []
 >> ASM_SIMP_TAC bool_ss [GSYM Portemanteau_iv_eq_v]
 >> MATCH_MP_TAC Portemanteau_ii_imp_iv  >> art []
QED

(* |- !E X Y.
        (!n. prob_space (space (B E),subsets (B E),X n)) /\
        prob_space (space (B E),subsets (B E),Y) ==>
        (weak_converge_in_topology (mtop E) X Y <=>
         !f. f IN BL E ==>
             ((\n. integral (mspace E,subsets (B E),X n) (Normal o f)) -->
              integral (mspace E,subsets (B E),Y) (Normal o f)) sequentially)
 *)
Theorem weak_converge_in_topology_alt_Lipschitz =
        Portemanteau_i_eq_ii
     |> SRULE [Portemanteau_antecedents_alt_def, GSYM mspace,
               Portemanteau_i_def, Portemanteau_ii_def,
               weak_convergence_condition_def]

(* |- !X Y.
        (!n. prob_space (space Borel,subsets Borel,X n)) /\
        prob_space (space Borel,subsets Borel,Y) ==>
        (X --> Y <=>
         !f. f IN BL extreal_mr1 ==>
             ((\n. expectation (space Borel,subsets Borel,X n) (Normal o f)) -->
              expectation (space Borel,subsets Borel,Y) (Normal o f))
               sequentially)
 *)
Theorem converge_in_dist_alt_Lipschitz_lemma[local] =
        weak_converge_in_topology_alt_Lipschitz
     |> ISPEC “extreal_mr1”
     |> REWRITE_RULE [GSYM ext_euclidean_def, GSYM Borel_alt_general]
     |> REWRITE_RULE [GSYM weak_converge, GSYM expectation_def]

Theorem converge_in_dist_alt_Lipschitz :
    !X Y p. prob_space p /\ (!n. random_variable (X n) p Borel) /\
            random_variable Y p Borel ==>
           ((X --> Y) (in_distribution p) <=>
             !f. f IN BL extreal_mr1 ==>
                ((\n. expectation p (Normal o f o X n)) -->
                 expectation p (Normal o f o Y)) sequentially)
Proof
    rw [converge_in_dist_alt_weak_converge]
 >> qabbrev_tac ‘fi = \n. distribution p (X n)’
 >> qabbrev_tac ‘f = distribution p Y’
 >> REWRITE_TAC [ext_euclidean_def]
 >> qabbrev_tac ‘E = extreal_mr1’
 >> Know ‘!n. prob_space (space Borel,subsets Borel,fi n)’
 >- (rw [Abbr ‘fi’] \\
     MATCH_MP_TAC distribution_prob_space >> simp [SIGMA_ALGEBRA_BOREL])
 >> DISCH_TAC
 >> Know ‘prob_space (space Borel,subsets Borel,f)’
 >- (rw [Abbr ‘f’] \\
     MATCH_MP_TAC distribution_prob_space >> simp [SIGMA_ALGEBRA_BOREL])
 >> DISCH_TAC
 >> simp [converge_in_dist_alt_Lipschitz_lemma, expectation_def]
 >> NTAC 2 (POP_ASSUM K_TAC)
 >> fs [Abbr ‘fi’, Abbr ‘f’, distribution_distr, random_variable_def,
        p_space_def, events_def, prob_space_def]
 >> EQ_TAC
 >| [ (* goal 1 (of 2) *)
      rpt STRIP_TAC \\
      Q.PAT_X_ASSUM ‘!f. f IN BL E ==> _’ (MP_TAC o Q.SPEC ‘f’) >> rw [] \\
      fs [BL_alt, Abbr ‘E’] \\
      Know ‘continuous_map (ext_euclidean,euclidean) f’
      >- (REWRITE_TAC [ext_euclidean_def, euclidean_def] \\
          MATCH_MP_TAC Lipschitz_continuous_map_imp_continuous_map >> art []) \\
      DISCH_TAC \\
      REWRITE_TAC [o_ASSOC] \\
      qabbrev_tac ‘g = Normal o f’ \\
      Know ‘!n. integral p (g o X n) =
                integral (space Borel,subsets Borel,distr p (X n)) g’
      >- (Q.X_GEN_TAC ‘n’ \\
          SYM_TAC >> MATCH_MP_TAC (cj 1 integral_distr) \\
          simp [SIGMA_ALGEBRA_BOREL, Abbr ‘g’] \\
          MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
          simp [SIGMA_ALGEBRA_BOREL, borel_alt_general, Borel_alt_general] \\
          MATCH_MP_TAC IN_MEASURABLE_CONTINUOUS_MAP >> art []) >> Rewr' \\
      Know ‘integral p (g o Y) = integral (space Borel,subsets Borel,distr p Y) g’
      >- (SYM_TAC >> MATCH_MP_TAC (cj 1 integral_distr) \\
          simp [SIGMA_ALGEBRA_BOREL, Abbr ‘g’] \\
          MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
          simp [SIGMA_ALGEBRA_BOREL, borel_alt_general, Borel_alt_general] \\
          MATCH_MP_TAC IN_MEASURABLE_CONTINUOUS_MAP >> art []) >> Rewr' \\
      simp [],
      (* goal 2 (of 2) *)
      DISCH_TAC \\
      Q.X_GEN_TAC ‘f’ >> DISCH_TAC \\
      Q.PAT_X_ASSUM ‘!f. f IN BL E ==> _’ (MP_TAC o Q.SPEC ‘f’) >> rw [] \\
      fs [BL_alt, Abbr ‘E’] \\
      Know ‘continuous_map (ext_euclidean,euclidean) f’
      >- (REWRITE_TAC [ext_euclidean_def, euclidean_def] \\
          MATCH_MP_TAC Lipschitz_continuous_map_imp_continuous_map >> art []) \\
      DISCH_TAC \\
      qabbrev_tac ‘g = Normal o f’ \\
      Know ‘!n. integral (space Borel,subsets Borel,distr p (X n)) g =
                integral p (g o X n)’
      >- (Q.X_GEN_TAC ‘n’ \\
          MATCH_MP_TAC (cj 1 integral_distr) \\
          simp [SIGMA_ALGEBRA_BOREL, Abbr ‘g’] \\
          MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
          simp [SIGMA_ALGEBRA_BOREL, borel_alt_general, Borel_alt_general] \\
          MATCH_MP_TAC IN_MEASURABLE_CONTINUOUS_MAP >> art []) >> Rewr' \\
      Know ‘integral (space Borel,subsets Borel,distr p Y) g = integral p (g o Y)’
      >- (MATCH_MP_TAC (cj 1 integral_distr) \\
          simp [SIGMA_ALGEBRA_BOREL, Abbr ‘g’] \\
          MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
          simp [SIGMA_ALGEBRA_BOREL, borel_alt_general, Borel_alt_general] \\
          MATCH_MP_TAC IN_MEASURABLE_CONTINUOUS_MAP >> art []) >> Rewr' \\
      simp [Abbr ‘g’] ]
QED

(* weak convergence of real-typed measures *)
Definition real_weak_converge :
    real_weak_converge X Y = weak_converge_in_topology euclidean X Y
End
Overload "-->" = “real_weak_converge”

(* |- !X (Y :num -> real measure).
        X --> Y <=>
        !f. f IN C_b euclidean ==>
            ((\n. integral (space borel,subsets borel,X n) (Normal o f)) -->
             integral (space borel,subsets borel,Y) (Normal o f))
              sequentially
 *)
Theorem real_weak_converge_def =
        real_weak_converge
     |> REWRITE_RULE [weak_converge_in_topology, GSYM borel_alt_general]

Theorem real_weak_converge_cong :
    !X Y X' Y'. (!n. measure_space (space borel,subsets borel,X n)) /\
                measure_space (space borel,subsets borel,Y) /\
                (!n s. s IN subsets borel ==> X n s = X' n s) /\
                (!s. s IN subsets borel ==> Y s = Y' s) ==>
                (X --> Y <=> X' --> Y')
Proof
    rw [real_weak_converge_def]
 >> Know ‘!f n. integral (space borel,subsets borel,X n) (Normal o f) =
                integral (space borel,subsets borel,X' n) (Normal o f)’
 >- (rpt GEN_TAC \\
     MATCH_MP_TAC integral_cong_measure >> art [])
 >> Rewr'
 >> Know ‘!f. integral (space borel,subsets borel,Y) (Normal o f) =
              integral (space borel,subsets borel,Y') (Normal o f)’
 >- (Q.X_GEN_TAC ‘f’ \\
     MATCH_MP_TAC integral_cong_measure >> art [])
 >> Rewr
QED

(* NOTE: When ‘X’ represent a distribution of another r.v., the antecedents
  ‘X {PosInf} = 0 /\ X {NegInf} = 0’ actually mean that the r.v. only takes
   finite values, i.e. a real_random_variable.
 *)
Theorem prob_space_normal :
    !X. prob_space (space Borel,subsets Borel,X) /\
        X {PosInf} = 0 /\ X {NegInf} = 0 ==>
        prob_space (space borel,subsets borel,X o IMAGE Normal)
Proof
    reverse (rw [prob_space_def])
 >- (Know ‘IMAGE Normal (space borel) = UNIV DIFF {PosInf; NegInf}’
     >- (rw [Once EXTENSION, space_borel] \\
         METIS_TAC [extreal_cases, extreal_not_infty]) >> Rewr' \\
         qabbrev_tac ‘M = (space Borel,subsets Borel,X)’ \\
        ‘X = measure M’ by simp [Abbr ‘M’] >> POP_ORW \\
         qmatch_abbrev_tac ‘measure M (UNIV DIFF s) = 1’ \\
         REWRITE_TAC [GSYM SPACE_BOREL] \\
        ‘space Borel = m_space M’ by simp [Abbr ‘M’] >> POP_ORW \\
         Know ‘measure M (m_space M DIFF s) =
               measure M (m_space M) - measure M s’
         >- (MATCH_MP_TAC MEASURE_DIFF_SUBSET \\
             simp [MEASURE_SPACE_SPACE] \\
             CONJ_ASM1_TAC
             >- (simp [Abbr ‘s’, Abbr ‘M’] \\
                ‘{PosInf; NegInf} = {PosInf} UNION {NegInf}’ by SET_TAC [] \\
                 POP_ORW >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION \\
                 simp [SIGMA_ALGEBRA_BOREL, BOREL_MEASURABLE_SETS]) \\
             CONJ_TAC >- simp [Abbr ‘M’, SPACE_BOREL] \\
             Q_TAC (TRANS_TAC let_trans) ‘measure M (space Borel)’ \\
             reverse CONJ_TAC >- simp [GSYM lt_infty, Abbr ‘M’] \\
             MATCH_MP_TAC INCREASING >> art [] \\
            ‘space Borel = m_space M’ by simp [Abbr ‘M’] >> POP_ORW \\
             simp [MEASURE_SPACE_SPACE, MEASURE_SPACE_INCREASING] \\
             simp [Abbr ‘M’, SPACE_BOREL]) >> Rewr' \\
     Know ‘measure M s = 0’
     >- (qunabbrev_tac ‘s’ \\
        ‘{PosInf; NegInf} = {PosInf} UNION {NegInf}’ by SET_TAC [] >> POP_ORW \\
         Know ‘measure M ({PosInf} UNION {NegInf}) =
               measure M {PosInf} + measure M {NegInf}’
         >- (MATCH_MP_TAC ADDITIVE >> simp [MEASURE_SPACE_ADDITIVE] \\
             CONJ_ASM1_TAC >- simp [Abbr ‘M’, BOREL_MEASURABLE_SETS] \\
             CONJ_ASM1_TAC >- simp [Abbr ‘M’, BOREL_MEASURABLE_SETS] \\
             MATCH_MP_TAC MEASURE_SPACE_UNION >> art []) >> Rewr' \\
         simp [Abbr ‘M’]) >> Rewr' \\
     simp [Abbr ‘M’])
 >> qabbrev_tac ‘M = (space Borel,subsets Borel,X)’
 >> rw [measure_space_def, sigma_algebra_borel]
 >- (rw [positive_def, o_DEF]
     >- (‘X = measure M’ by simp [Abbr ‘M’] >> POP_ORW \\
         MATCH_MP_TAC MEASURE_EMPTY >> art []) \\
    ‘X = measure M’ by simp [Abbr ‘M’] >> POP_ORW \\
     MATCH_MP_TAC MEASURE_POSITIVE >> art [] \\
     simp [Abbr ‘M’, BOREL_MEASURABLE_SETS_NORMAL])
 >> rw [countably_additive_def, IMAGE_BIGUNION, IMAGE_IMAGE, IN_FUNSET]
 >> qabbrev_tac ‘g = IMAGE Normal o f’
 >> ‘X = measure M’ by simp [Abbr ‘M’] >> POP_ORW
 >> SYM_TAC
 >> MATCH_MP_TAC COUNTABLY_ADDITIVE
 >> simp [MEASURE_SPACE_COUNTABLY_ADDITIVE, IN_FUNSET]
 >> CONJ_ASM1_TAC
 >- (rw [Abbr ‘g’, Abbr ‘M’] \\
     MATCH_MP_TAC BOREL_MEASURABLE_SETS_NORMAL >> art [])
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC MEASURE_SPACE_BIGUNION >> art [])
 >> rw [Abbr ‘g’, DISJOINT_ALT]
 >> rename1 ‘y NOTIN f j’
 >> Q.PAT_X_ASSUM ‘!i j. i <> j ==> _’ (MP_TAC o Q.SPECL [‘i’, ‘j’])
 >> rw [DISJOINT_ALT]
QED

Theorem prob_space_real_set[local] :
    !X. prob_space (space borel,subsets borel,X) ==>
        prob_space (space Borel,subsets Borel,X o real_set)
Proof
    reverse (rw [prob_space_def])
 >- (Know ‘real_set (space Borel) = UNIV’
     >- (rw [Once EXTENSION, SPACE_BOREL, real_set_def] \\
         Q.EXISTS_TAC ‘Normal x’ >> simp []) >> Rewr' \\
     fs [space_borel])
 >> qabbrev_tac ‘M = (space borel,subsets borel,X)’
 >> rw [measure_space_def, SIGMA_ALGEBRA_BOREL]
 >- (rw [positive_def, o_DEF]
     >- (‘X = measure M’ by simp [Abbr ‘M’] >> POP_ORW \\
         MATCH_MP_TAC MEASURE_EMPTY >> art []) \\
    ‘X = measure M’ by simp [Abbr ‘M’] >> POP_ORW \\
     MATCH_MP_TAC MEASURE_POSITIVE >> art [] \\
     simp [Abbr ‘M’, borel_measurable_real_set])
 >> rw [countably_additive_def, IMAGE_BIGUNION, IMAGE_IMAGE, IN_FUNSET]
 >> qabbrev_tac ‘g = real_set o f’
 >> ‘X = measure M’ by simp [Abbr ‘M’] >> POP_ORW
 >> SYM_TAC
 >> MATCH_MP_TAC COUNTABLY_ADDITIVE
 >> simp [MEASURE_SPACE_COUNTABLY_ADDITIVE, IN_FUNSET]
 >> CONJ_ASM1_TAC
 >- (Q.X_GEN_TAC ‘n’ \\
     rw [Abbr ‘M’, Abbr ‘g’] \\
     MATCH_MP_TAC borel_measurable_real_set >> art [])
 >> CONJ_TAC
 >- (rw [DISJOINT_ALT, Abbr ‘g’, real_set_def] \\
     rename1 ‘real y = real z’ \\
     Cases_on ‘y = PosInf’ >> simp [] \\
     Cases_on ‘y = NegInf’ >> simp [] \\
     gs [real_11] \\
     Q.PAT_X_ASSUM ‘!i j. i <> j ==> _’ (MP_TAC o Q.SPECL [‘i’, ‘j’]) \\
     rw [DISJOINT_ALT])
 >> CONJ_ASM1_TAC
 >- (rw [Once EXTENSION, real_set_def, IN_BIGUNION_IMAGE] \\
     EQ_TAC >> rw [GSPECIFICATION, Abbr ‘g’, real_set_def] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       rename1 ‘y IN f n’ \\
       qexistsl_tac [‘n’, ‘y’] >> art [],
       (* goal 2 (of 2) *)
       rename1 ‘y IN f n’ \\
       Q.EXISTS_TAC ‘y’ >> art [] \\
       Q.EXISTS_TAC ‘n’ >> art [] ])
 >> POP_ORW
 >> MATCH_MP_TAC MEASURE_SPACE_BIGUNION >> art []
QED

Theorem prob_space_real_set_eq :
    !X. prob_space (space borel,subsets borel,X) <=>
        prob_space (space Borel,subsets Borel,X o real_set)
Proof
    Q.X_GEN_TAC ‘X’
 >> EQ_TAC >- REWRITE_TAC [prob_space_real_set]
 >> DISCH_TAC
 >> qabbrev_tac ‘Y = X o real_set’
 >> Know ‘X = Y o IMAGE Normal’
 >- (rw [FUN_EQ_THM, Abbr ‘Y’, o_DEF] \\
     Suff ‘real_set (IMAGE Normal x) = x’ >- rw [] \\
     rw [Once EXTENSION, real_set_def] \\
     EQ_TAC >> rw [] >> simp [] \\
     rename1 ‘y IN s’ \\
     Q.EXISTS_TAC ‘Normal y’ >> simp [])
 >> Rewr'
 >> MATCH_MP_TAC prob_space_normal >> art []
 >> simp [Abbr ‘Y’, o_DEF]
 >> qabbrev_tac ‘p = (space Borel,subsets Borel,X o real_set)’
 >> Know ‘prob p {} = 0’ >- PROVE_TAC [PROB_EMPTY]
 >> simp [Abbr ‘p’, o_DEF, prob_def]
QED

(* NOTE: This theorem is inspired by [prob_space_normal] and is based on
   integral_distr, when "change of variables" is not yet available for
   our Lebesgue integration.
 *)
Theorem converge_in_dist_alt_real_weak_converge_lemma[local] :
    !p X Y. prob_space p /\ (!n. real_random_variable (X n) p) /\
            real_random_variable Y p ==>
           ((X --> Y) (in_distribution p) <=>
            (\n. distribution p (X n) o IMAGE Normal) -->
                 distribution p Y o IMAGE Normal)
Proof
    RW_TAC std_ss [real_random_variable_def, FORALL_AND_THM,
                   converge_in_dist_alt_weak_converge]
 >> Know ‘!n. prob_space (space Borel,subsets Borel,distribution p (X n))’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC distribution_prob_space >> rw [SIGMA_ALGEBRA_BOREL])
 >> DISCH_TAC
 >> Know ‘prob_space (space Borel,subsets Borel,distribution p Y)’
 >- (MATCH_MP_TAC distribution_prob_space >> rw [SIGMA_ALGEBRA_BOREL])
 >> DISCH_TAC
 >> rw [weak_converge_def, real_weak_converge_def, IN_bounded_continuous]
 >> qabbrev_tac ‘M = \n. space Borel,subsets Borel,distribution p (X n)’
 >> qabbrev_tac ‘N = (space Borel,subsets Borel,distribution p Y)’
 >> qabbrev_tac ‘M' = \n. (space borel,subsets borel,
                           distribution p (X n) o IMAGE Normal)’
 >> qabbrev_tac ‘N' = (space borel,subsets borel,
                       distribution p Y o IMAGE Normal)’
 >> fs []
 >> Know ‘!n. prob_space (M' n)’
 >- (rw [Abbr ‘M'’] \\
     MATCH_MP_TAC prob_space_normal >> simp [] \\
     simp [distribution_def, PREIMAGE_def] \\
     Know ‘{x | X n x = PosInf} INTER p_space p = {}’
     >- (rw [Once EXTENSION, NOT_IN_EMPTY] >> PROVE_TAC []) >> Rewr' \\
     Know ‘{x | X n x = NegInf} INTER p_space p = {}’
     >- (rw [Once EXTENSION, NOT_IN_EMPTY] >> PROVE_TAC []) >> Rewr \\
     simp [PROB_EMPTY])
 >> DISCH_TAC
 >> Know ‘prob_space N'’
 >- (qunabbrev_tac ‘N'’ \\
     MATCH_MP_TAC prob_space_normal >> simp [] \\
     simp [distribution_def, PREIMAGE_def] \\
     Know ‘{x | Y x = PosInf} INTER p_space p = {}’
     >- (rw [Once EXTENSION, NOT_IN_EMPTY] >> PROVE_TAC []) >> Rewr' \\
     Know ‘{x | Y x = NegInf} INTER p_space p = {}’
     >- (rw [Once EXTENSION, NOT_IN_EMPTY] >> PROVE_TAC []) >> Rewr \\
     simp [PROB_EMPTY])
 >> DISCH_TAC
 >> Know ‘!n s. s IN subsets borel ==>
               (distribution p (X n) o IMAGE Normal) s =
                distribution p (real o X n) s’
 >- (rw [o_DEF, distribution_def, PREIMAGE_def] \\
     Suff ‘{x | ?x'. X n x = Normal x' /\ x' IN s} INTER p_space p =
           {x | real (X n x) IN s} INTER p_space p’ >- rw [] \\
     rw [Once EXTENSION] \\
     Cases_on ‘x IN p_space p’ >> simp [] \\
    ‘?r. X n x = Normal r’ by METIS_TAC [extreal_cases] \\
     simp [])
 >> DISCH_TAC
 (* Y :'a -> extreal, “(real o Y) :'a -> real *)
 >> Know ‘!n f. integral (M' n) (Normal o f) =
                integral (space borel,subsets borel,distribution p (real o X n))
                         (Normal o f)’
 >- (rpt GEN_TAC \\
     fs [Abbr ‘M'’, prob_space_def, FORALL_AND_THM] \\
     MATCH_MP_TAC integral_cong_measure >> simp [])
 >> Rewr'
 >> Know ‘!s. s IN subsets borel ==>
             (distribution p Y o IMAGE Normal) s =
              distribution p (real o Y) s’
 >- (rw [o_DEF, distribution_def, PREIMAGE_def] \\
     Suff ‘{x | ?x'. Y x = Normal x' /\ x' IN s} INTER p_space p =
           {x | real (Y x) IN s} INTER p_space p’ >- rw [] \\
     rw [Once EXTENSION] \\
     Cases_on ‘x IN p_space p’ >> simp [] \\
    ‘?r. Y x = Normal r’ by METIS_TAC [extreal_cases] \\
     simp [])
 >> DISCH_TAC
 >> Know ‘!f. integral N' (Normal o f) =
              integral (space borel,subsets borel,distribution p (real o Y))
                       (Normal o f)’
 >- (Q.X_GEN_TAC ‘f’ \\
     fs [Abbr ‘N'’, prob_space_def, FORALL_AND_THM] \\
     MATCH_MP_TAC integral_cong_measure >> simp [])
 >> Rewr'
 (* preparing for integral_distr *)
 >> FULL_SIMP_TAC std_ss [distribution_distr]
 >> Q.PAT_X_ASSUM ‘!n. prob_space (M' n)’ K_TAC
 >> Q.PAT_X_ASSUM ‘prob_space N'’         K_TAC
 >> qunabbrevl_tac [‘M'’, ‘N'’]
 >> NTAC 2 (POP_ASSUM K_TAC)
 >> qabbrev_tac ‘X' = \n. real o X n’ >> simp []
 >> qabbrev_tac ‘Y' = real o Y’
 >> EQ_TAC >> rpt STRIP_TAC
 >- (Know ‘f IN measurable borel borel’
     >- (REWRITE_TAC [borel_alt_general] \\
         MATCH_MP_TAC IN_MEASURABLE_CONTINUOUS_MAP >> art []) >> DISCH_TAC \\
     qabbrev_tac ‘g = Normal o f’ \\
     Know ‘g IN measurable borel Borel’
     >- (qunabbrev_tac ‘g’ \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
         simp [sigma_algebra_borel]) >> DISCH_TAC \\
     Know ‘!n. integral (space borel,subsets borel,distr p (X' n)) g =
               integral p (g o X' n)’
     >- (Q.X_GEN_TAC ‘n’ \\
         MATCH_MP_TAC (cj 1 integral_distr) \\
         fs [Abbr ‘X'’, prob_space_def, FORALL_AND_THM, sigma_algebra_borel] \\
         MATCH_MP_TAC in_borel_measurable_from_Borel \\
         fs [measure_space_def, random_variable_def, p_space_def, events_def]) \\
     Rewr' \\
     Know ‘integral (space borel,subsets borel,distr p Y') g = integral p (g o Y')’
     >- (MATCH_MP_TAC (cj 1 integral_distr) \\
         fs [Abbr ‘Y'’, prob_space_def, FORALL_AND_THM, sigma_algebra_borel] \\
         MATCH_MP_TAC in_borel_measurable_from_Borel \\
         fs [measure_space_def, random_variable_def, p_space_def, events_def]) \\
     Rewr' \\
     simp [Abbr ‘X'’, Abbr ‘Y'’, Abbr ‘g’] \\
     qabbrev_tac ‘h = f o real’ \\
    ‘!n. Normal o f o real o X n = Normal o h o X n’ by METIS_TAC [o_ASSOC] \\
     POP_ORW \\
    ‘Normal o f o real o Y = Normal o h o Y’
       by METIS_TAC [o_ASSOC] >> POP_ORW \\
     Q.PAT_X_ASSUM ‘!f. continuous_map (ext_euclidean,euclidean) f /\ _ ==> _’
       (MP_TAC o Q.SPEC ‘h’) \\
     Know ‘continuous_map (ext_euclidean,euclidean) h’
     >- (qunabbrev_tac ‘h’ \\
         MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE \\
         Q.EXISTS_TAC ‘euclidean’ >> art [] \\
         REWRITE_TAC [continuous_map_real]) >> DISCH_TAC \\
     impl_tac
     >- (fs [Abbr ‘h’, o_DEF, bounded_def] \\
         Q.EXISTS_TAC ‘a’ >> Q.X_GEN_TAC ‘x’ \\
         DISCH_THEN (Q.X_CHOOSE_THEN ‘y’ STRIP_ASSUME_TAC) \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art [] \\
         Q.EXISTS_TAC ‘real y’ >> REFL_TAC) \\
     simp [Abbr ‘M’, Abbr ‘N’] \\
     qabbrev_tac ‘g = Normal o h’ \\
     Know ‘g IN Borel_measurable Borel’
     >- (qunabbrev_tac ‘g’ \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
         simp [Abbr ‘h’, SIGMA_ALGEBRA_BOREL] \\
         MATCH_MP_TAC MEASURABLE_COMP \\
         Q.EXISTS_TAC ‘borel’ >> simp [real_in_borel_measurable]) >> DISCH_TAC \\
     Know ‘!n. integral (space Borel,subsets Borel,distr p (X n)) g =
               integral p (g o X n)’
     >- (Q.X_GEN_TAC ‘n’ \\
         MATCH_MP_TAC (cj 1 integral_distr) \\
         fs [prob_space_def, FORALL_AND_THM, SIGMA_ALGEBRA_BOREL] \\
         fs [random_variable_def, p_space_def, events_def]) >> Rewr' \\
     Know ‘integral (space Borel,subsets Borel,distr p Y) g = integral p (g o Y)’
     >- (MATCH_MP_TAC (cj 1 integral_distr) \\
         fs [prob_space_def, FORALL_AND_THM, SIGMA_ALGEBRA_BOREL] \\
         fs [random_variable_def, p_space_def, events_def]) >> Rewr' \\
     simp [Abbr ‘g’])
 (* stage work (the other direction) *)
 >> Know ‘f IN measurable Borel borel’
 >- (REWRITE_TAC [Borel_alt_general, borel_alt_general] \\
     MATCH_MP_TAC IN_MEASURABLE_CONTINUOUS_MAP >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘g = Normal o f’
 >> Know ‘g IN measurable Borel Borel’
 >- (qunabbrev_tac ‘g’ \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
     simp [SIGMA_ALGEBRA_BOREL])
 >> DISCH_TAC
 >> simp [Abbr ‘M’, Abbr ‘N’]
 >> Know ‘!n. integral (space Borel,subsets Borel,distr p (X n)) g =
              integral p (g o X n)’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC (cj 1 integral_distr) \\
     fs [prob_space_def, FORALL_AND_THM, SIGMA_ALGEBRA_BOREL] \\
     fs [random_variable_def, p_space_def, events_def])
 >> Rewr'
 >> Know ‘integral (space Borel,subsets Borel,distr p Y) g = integral p (g o Y)’
 >- (MATCH_MP_TAC (cj 1 integral_distr) \\
     fs [prob_space_def, FORALL_AND_THM, SIGMA_ALGEBRA_BOREL] \\
     fs [random_variable_def, p_space_def, events_def])
 >> Rewr'
 >> qabbrev_tac ‘h = f o Normal’
 >> Q.PAT_X_ASSUM ‘!f. continuous_map (euclidean,euclidean) f /\ _ ==> _’
      (MP_TAC o Q.SPEC ‘h’)
 >> Know ‘continuous_map (euclidean,euclidean) h’
 >- (qunabbrev_tac ‘h’ \\
     MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE \\
     Q.EXISTS_TAC ‘ext_euclidean’ >> art [] \\
     REWRITE_TAC [continuous_map_normal])
 >> DISCH_TAC
 >> impl_tac
 >- (fs [Abbr ‘h’, bounded_def] \\
     Q.EXISTS_TAC ‘a’ >> Q.X_GEN_TAC ‘x’ \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘y’ STRIP_ASSUME_TAC) \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [] \\
     Q.EXISTS_TAC ‘Normal y’ >> REFL_TAC)
 >> qunabbrev_tac ‘g’
 >> qabbrev_tac ‘g = Normal o h’
 >> Know ‘g IN measurable borel Borel’
 >- (qunabbrev_tac ‘g’ \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
     simp [Abbr ‘h’, sigma_algebra_borel] \\
     MATCH_MP_TAC MEASURABLE_COMP \\
     Q.EXISTS_TAC ‘Borel’ >> art [] \\
     REWRITE_TAC [IN_MEASURABLE_BOREL_NORMAL])
 >> DISCH_TAC
 >> Know ‘!n. integral (space borel,subsets borel,distr p (X' n)) g =
              integral p (g o X' n)’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC (cj 1 integral_distr) \\
     fs [Abbr ‘X'’, prob_space_def, FORALL_AND_THM, sigma_algebra_borel] \\
     MATCH_MP_TAC in_borel_measurable_from_Borel \\
     fs [measure_space_def, random_variable_def, p_space_def, events_def])
 >> Rewr'
 >> Know ‘integral (space borel,subsets borel,distr p Y') g = integral p (g o Y')’
 >- (MATCH_MP_TAC (cj 1 integral_distr) \\
     fs [Abbr ‘Y'’, prob_space_def, FORALL_AND_THM, sigma_algebra_borel] \\
     MATCH_MP_TAC in_borel_measurable_from_Borel \\
     fs [measure_space_def, random_variable_def, p_space_def, events_def])
 >> Rewr'
 >> simp [Abbr ‘g’, Abbr ‘X'’, Abbr ‘Y'’, Abbr ‘h’]
 (* stage work *)
 >> Know ‘!n. integral p (Normal o f o Normal o real o X n) =
              integral p (Normal o f o X n)’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC integral_cong \\
     CONJ_ASM1_TAC >- fs [prob_space_def] \\
     rw [o_DEF, GSYM p_space_def] \\
     AP_TERM_TAC \\
     MATCH_MP_TAC normal_real >> simp [])
 >> Rewr'
 >> Know ‘integral p (Normal o f o Normal o real o Y) = integral p (Normal o f o Y)’
 >- (MATCH_MP_TAC integral_cong \\
     CONJ_ASM1_TAC >- fs [prob_space_def] \\
     rw [o_DEF, GSYM p_space_def] \\
     AP_TERM_TAC \\
     MATCH_MP_TAC normal_real >> simp [])
 >> Rewr
QED

Theorem converge_in_dist_alt_real_weak_converge :
    !p X Y. prob_space p /\ (!n. real_random_variable (X n) p) /\
            real_random_variable Y p ==>
           ((X --> Y) (in_distribution p) <=>
            (\n. distribution p (real o X n)) --> distribution p (real o Y))
Proof
    RW_TAC std_ss [converge_in_dist_alt_real_weak_converge_lemma]
 >> MATCH_MP_TAC real_weak_converge_cong
 >> fs [real_random_variable_def, FORALL_AND_THM]
 >> Know ‘!n. prob_space (space Borel,subsets Borel,distribution p (X n))’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC distribution_prob_space >> rw [SIGMA_ALGEBRA_BOREL])
 >> DISCH_TAC
 >> Know ‘prob_space (space Borel,subsets Borel,distribution p Y)’
 >- (MATCH_MP_TAC distribution_prob_space >> rw [SIGMA_ALGEBRA_BOREL])
 >> DISCH_TAC
 >> qabbrev_tac ‘M = \n. space Borel,subsets Borel,distribution p (X n)’
 >> qabbrev_tac ‘N = (space Borel,subsets Borel,distribution p Y)’
 >> qabbrev_tac ‘M' = \n. (space borel,subsets borel,
                           distribution p (X n) o IMAGE Normal)’
 >> qabbrev_tac ‘N' = (space borel,subsets borel,
                       distribution p Y o IMAGE Normal)’
 >> fs []
 >> Know ‘!n. prob_space (M' n)’
 >- (rw [Abbr ‘M'’] \\
     MATCH_MP_TAC prob_space_normal >> simp [] \\
     simp [distribution_def, PREIMAGE_def] \\
     Know ‘{x | X n x = PosInf} INTER p_space p = {}’
     >- (rw [Once EXTENSION, NOT_IN_EMPTY] >> PROVE_TAC []) >> Rewr' \\
     Know ‘{x | X n x = NegInf} INTER p_space p = {}’
     >- (rw [Once EXTENSION, NOT_IN_EMPTY] >> PROVE_TAC []) >> Rewr \\
     simp [PROB_EMPTY])
 >> DISCH_TAC
 >> Know ‘prob_space N'’
 >- (qunabbrev_tac ‘N'’ \\
     MATCH_MP_TAC prob_space_normal >> simp [] \\
     simp [distribution_def, PREIMAGE_def] \\
     Know ‘{x | Y x = PosInf} INTER p_space p = {}’
     >- (rw [Once EXTENSION, NOT_IN_EMPTY] >> PROVE_TAC []) >> Rewr' \\
     Know ‘{x | Y x = NegInf} INTER p_space p = {}’
     >- (rw [Once EXTENSION, NOT_IN_EMPTY] >> PROVE_TAC []) >> Rewr \\
     simp [PROB_EMPTY])
 >> DISCH_TAC
 >> CONJ_TAC >- fs [prob_space_def]
 >> CONJ_TAC >- fs [prob_space_def]
 >> CONJ_TAC
 >- (rw [o_DEF, distribution_def, PREIMAGE_def] \\
     Suff ‘{x | ?x'. X n x = Normal x' /\ x' IN s} INTER p_space p =
           {x | real (X n x) IN s} INTER p_space p’ >- rw [] \\
     rw [Once EXTENSION] \\
     Cases_on ‘x IN p_space p’ >> simp [] \\
    ‘?r. X n x = Normal r’ by METIS_TAC [extreal_cases] \\
     simp [])
 >> rw [o_DEF, distribution_def, PREIMAGE_def]
 >> Suff ‘{x | ?x'. Y x = Normal x' /\ x' IN s} INTER p_space p =
          {x | real (Y x) IN s} INTER p_space p’ >- rw []
 >> rw [Once EXTENSION]
 >> Cases_on ‘x IN p_space p’ >> simp []
 >> ‘?r. Y x = Normal r’ by METIS_TAC [extreal_cases]
 >> simp []
QED

(* |- !X Y.
        (!n. prob_space (space borel,subsets borel,X n)) /\
        prob_space (space borel,subsets borel,Y) ==>
        (X --> Y <=>
         !f. f IN BL mr1 ==>
             ((\n. integral (space borel,subsets borel,X n) (Normal o f)) -->
              integral (space borel,subsets borel,Y) (Normal o f))
               sequentially)
 *)
Theorem real_weak_converge_alt_Lipschitz_lemma[local] =
        weak_converge_in_topology_alt_Lipschitz
     |> ISPEC “mr1”
     |> REWRITE_RULE [GSYM euclidean_def, GSYM borel_alt_general]
     |> REWRITE_RULE [GSYM real_weak_converge]

(* cf. converge_in_dist_alt_continuous_on *)
Theorem converge_in_dist_alt_Lipschitz_real :
    !X Y p. prob_space p /\ (!n. real_random_variable (X n) p) /\
            real_random_variable Y p ==>
           ((X --> Y) (in_distribution p) <=>
             !f. f IN BL mr1 ==>
                ((\n. expectation p (Normal o f o real o X n)) -->
                 expectation p (Normal o f o real o Y)) sequentially)
Proof
    RW_TAC std_ss [converge_in_dist_alt_real_weak_converge]
 >> qabbrev_tac ‘X' = \n. distribution p (real o X n)’
 >> qabbrev_tac ‘Y' = distribution p (real o Y)’
 >> Know ‘!n. prob_space (space borel,subsets borel,X' n)’
 >- (rw [Abbr ‘X'’] \\
     MATCH_MP_TAC distribution_prob_space \\
     rw [random_variable_def, sigma_algebra_borel] \\
     MATCH_MP_TAC in_borel_measurable_from_Borel \\
     fs [prob_space_def, real_random_variable] \\
     fs [measure_space_def, p_space_def, events_def])
 >> DISCH_TAC
 >> Know ‘prob_space (space borel,subsets borel,Y')’
 >- (rw [Abbr ‘Y'’] \\
     MATCH_MP_TAC distribution_prob_space \\
     rw [random_variable_def, sigma_algebra_borel] \\
     MATCH_MP_TAC in_borel_measurable_from_Borel \\
     fs [prob_space_def, real_random_variable] \\
     fs [measure_space_def, p_space_def, events_def])
 >> DISCH_TAC
 >> RW_TAC std_ss [real_weak_converge_alt_Lipschitz_lemma]
 >> simp [expectation_def, Abbr ‘X'’, Abbr ‘Y'’, distribution_distr]
 >> EQ_TAC >> rw [BL_alt]
 >- (Q.PAT_X_ASSUM ‘!f. bounded (IMAGE f univ(:real)) /\ _ ==> _’
       (MP_TAC o Q.SPEC ‘f’) >> simp [] \\
     qabbrev_tac ‘g = Normal o f’ \\
     Know ‘g IN Borel_measurable borel’
     >- (qunabbrev_tac ‘g’ \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
         REWRITE_TAC [sigma_algebra_borel] \\
         REWRITE_TAC [borel_alt_general] \\
         MATCH_MP_TAC IN_MEASURABLE_CONTINUOUS_MAP \\
         REWRITE_TAC [euclidean_def] \\
         MATCH_MP_TAC Lipschitz_continuous_map_imp_continuous_map >> art []) \\
     DISCH_TAC \\
     Know ‘!n. integral (space borel,subsets borel,distr p (real o X n)) g =
               integral p (g o (real o X n))’
     >- (Q.X_GEN_TAC ‘n’ \\
         MATCH_MP_TAC (cj 1 integral_distr) \\
         fs [prob_space_def, sigma_algebra_borel] \\
         MATCH_MP_TAC in_borel_measurable_from_Borel \\
         fs [measure_space_def, real_random_variable, p_space_def, events_def,
             FORALL_AND_THM]) >> Rewr' \\
     Know ‘integral (space borel,subsets borel,distr p (real o Y)) g =
           integral p (g o (real o Y))’
     >- (MATCH_MP_TAC (cj 1 integral_distr) \\
         fs [prob_space_def, sigma_algebra_borel] \\
         MATCH_MP_TAC in_borel_measurable_from_Borel \\
         fs [measure_space_def, real_random_variable, p_space_def, events_def,
             FORALL_AND_THM]) >> Rewr' \\
     simp [Abbr ‘g’])
 (* stage work *)
 >> Q.PAT_X_ASSUM ‘!f. bounded (IMAGE f univ(:real)) /\ _ ==> _’
       (MP_TAC o Q.SPEC ‘f’) >> simp []
 >> qabbrev_tac ‘g = Normal o f’
 >> Know ‘g IN Borel_measurable borel’
 >- (qunabbrev_tac ‘g’ \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
     REWRITE_TAC [sigma_algebra_borel] \\
     REWRITE_TAC [borel_alt_general] \\
     MATCH_MP_TAC IN_MEASURABLE_CONTINUOUS_MAP \\
     REWRITE_TAC [euclidean_def] \\
     MATCH_MP_TAC Lipschitz_continuous_map_imp_continuous_map >> art [])
 >> DISCH_TAC
 >> Know ‘!n. integral (space borel,subsets borel,distr p (real o X n)) g =
              integral p (g o (real o X n))’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC (cj 1 integral_distr) \\
     fs [prob_space_def, sigma_algebra_borel] \\
     MATCH_MP_TAC in_borel_measurable_from_Borel \\
     fs [measure_space_def, real_random_variable, p_space_def, events_def,
         FORALL_AND_THM])
 >> Rewr'
 >> Know ‘integral (space borel,subsets borel,distr p (real o Y)) g =
          integral p (g o (real o Y))’
 >- (MATCH_MP_TAC (cj 1 integral_distr) \\
     fs [prob_space_def, sigma_algebra_borel] \\
     MATCH_MP_TAC in_borel_measurable_from_Borel \\
     fs [measure_space_def, real_random_variable, p_space_def, events_def,
         FORALL_AND_THM])
 >> Rewr'
 >> simp [Abbr ‘g’]
QED


(* ------------------------------------------------------------------------- *)
(*  Moment generating function                                               *)
(* ------------------------------------------------------------------------- *)

Definition mgf_def :
   mgf p X s =  expectation p (\x. exp (Normal s * X x))
End

Theorem mgf_0 :
    !p X. prob_space p ==> mgf p X 0 = 1
Proof
    RW_TAC std_ss [mgf_def, mul_lzero, exp_0, normal_0]
 >> MATCH_MP_TAC expectation_const >> art[]
QED

Theorem mgf_linear :
    ∀p X a b s. prob_space p ∧ real_random_variable X p ∧
                integrable p (λx. exp (Normal (a * s) * X x))  ⇒
                mgf p (λx.( Normal a * X x) + Normal b) s =
                (exp (Normal s * Normal b)) * mgf p X (a * s)
Proof
    rw [mgf_def, real_random_variable_def]
 >> Know ‘ expectation p (λx. exp (Normal s * ((Normal a * X x) + Normal b)))
         = expectation p (λx. exp ((Normal s * (Normal a * X x)) + Normal s * Normal b))’
 >- (MATCH_MP_TAC expectation_cong  >> rw[] >> AP_TERM_TAC
     >> ‘∃c. X x = Normal c’ by METIS_TAC [extreal_cases] >> rw[]
     >> ‘∃d. Normal a * Normal c = Normal d’ by METIS_TAC [extreal_mul_eq]
     >> rw[add_ldistrib_normal2]) >> Rewr'
 >> Know ‘expectation p
         (λx. exp (Normal s * (Normal a * X x) + Normal s * Normal b)) =
          expectation p (λx. (exp (Normal s * (Normal a * X x))) * exp (Normal s * Normal b))’
 >- (MATCH_MP_TAC expectation_cong
     >> rw[exp_add]
     >> ‘∃c. X x = Normal c’ by METIS_TAC [extreal_cases]>> rw[]
     >> ‘∃d. Normal a * Normal c = Normal d’ by METIS_TAC [extreal_mul_eq] >> rw[]
     >> ‘∃e. Normal s * Normal d = Normal e’ by METIS_TAC [extreal_mul_eq] >> rw[]
     >> ‘∃f. Normal s * Normal b = Normal f’ by METIS_TAC [extreal_mul_eq] >> rw[exp_add])
 >> Rewr'
 >> ‘∃g. exp (Normal s * Normal b) = Normal g’ by  METIS_TAC [extreal_mul_eq, normal_exp]
 >> rw[]
 >> GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [mul_comm]
 >> rw [mul_assoc, extreal_mul_eq]
 >> HO_MATCH_MP_TAC expectation_cmul
 >> ASM_REWRITE_TAC []
QED

Theorem mgf_sum :
    !p X Y s . prob_space p ∧ real_random_variable X p  ∧
               real_random_variable Y p  ∧
               indep_vars p X Y Borel Borel ∧
               mgf p (\x. X x + Y x) s ≠ PosInf ∧
               mgf p X s ≠ PosInf ∧
               mgf p Y s ≠ PosInf  ==>
               mgf p (\x. X x + Y x) s = mgf p X s * mgf p Y s
Proof
    rw [mgf_def, real_random_variable_def]
 >> Know ‘expectation p (\x. exp (Normal s * (X x + Y x))) =
          expectation p (\x. exp ((Normal s * X x) + (Normal s * Y x)))’
 >-(MATCH_MP_TAC expectation_cong >> rw[] >> AP_TERM_TAC
    >> MATCH_MP_TAC add_ldistrib_normal >> rw[])
    >> Rewr'
 >> Know ‘expectation p (λx. exp (Normal s * X x + Normal s * Y x)) =
          expectation p (λx. exp (Normal s * X x) * exp (Normal s * Y x))’
 >- (MATCH_MP_TAC expectation_cong  >> rw[] >> MATCH_MP_TAC exp_add >> DISJ2_TAC
     >> ‘∃a. X x = Normal a’ by METIS_TAC [extreal_cases]
     >> ‘∃b. Y x = Normal b’ by METIS_TAC [extreal_cases]
     >> rw[extreal_mul_eq]) >> Rewr'
 >> HO_MATCH_MP_TAC indep_vars_expectation
 >> simp[]
 >> CONJ_TAC
   (* real_random_variable (λx. exp (Normal s * X x)) p *)
 >- (MATCH_MP_TAC real_random_variable_exp_normal
     >> fs[real_random_variable, random_variable_def])
 >> CONJ_TAC
   (* real_random_variable (λx. exp (Normal s * X x)) p *)
 >- (MATCH_MP_TAC real_random_variable_exp_normal
     >> fs[real_random_variable, random_variable_def])
 >> CONJ_TAC
   (* indep_vars p (λx. exp (Normal s * X x)) (λx. exp (Normal s * Y x)) Borel Borel *)
 >- (Q.ABBREV_TAC ‘f = λx. exp (Normal s * x)’
     >> simp[]
     >> MATCH_MP_TAC (REWRITE_RULE [o_DEF] indep_rv_cong) >> csimp[]
     >> Q.UNABBREV_TAC ‘f’
     >> MATCH_MP_TAC IN_MEASURABLE_BOREL_EXP
     >> simp[] >> Q.EXISTS_TAC ‘λx. Normal s * x’ >> simp[SIGMA_ALGEBRA_BOREL]
     >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
     >> qexistsl [‘λx. x’, ‘s’]
     >> simp[SIGMA_ALGEBRA_BOREL, IN_MEASURABLE_BOREL_BOREL_I])
 >> Know ‘(λx. exp (Normal s * X x)) ∈ Borel_measurable (measurable_space p)’
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_EXP
     >> Q.EXISTS_TAC ‘λx. Normal s * X x’
     >> fs [prob_space_def, measure_space_def]
     >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
     >> qexistsl [‘X’, ‘s’] >> simp[random_variable_def]
     >> fs [random_variable_def, p_space_def, events_def])
 >> DISCH_TAC
 >> Know ‘(λx. exp (Normal s * Y x)) ∈ Borel_measurable (measurable_space p)’
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_EXP
     >> Q.EXISTS_TAC ‘λx. Normal s * Y x’
     >> fs [prob_space_def, measure_space_def]
     >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
     >> qexistsl [‘Y’, ‘s’] >> simp[random_variable_def]
     >> fs [random_variable_def, p_space_def, events_def])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘f = λx. exp (Normal s * X x)’ >> simp[]
 >> ‘∀x. x ∈ p_space p ⇒ 0 ≤  f x’ by METIS_TAC [exp_pos]
 >> Q.ABBREV_TAC ‘g = λx. exp (Normal s * Y x)’ >> simp[]
 >> ‘∀x. x ∈ p_space p ⇒ 0 ≤  g x’ by METIS_TAC [exp_pos]
 >> CONJ_TAC (* integrable p f *)
 >- (Suff ‘ pos_fn_integral p f <> PosInf’
     >- FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, integrable_pos, expectation_def]
     >> ‘∫ p f = ∫⁺ p f ’ by METIS_TAC[integral_pos_fn, prob_space_def, p_space_def]
     >> METIS_TAC [expectation_def]
     >> simp[])
 >- (Suff ‘ pos_fn_integral p g <> PosInf’
     >- FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, integrable_pos, expectation_def]
     >> ‘∫ p g = ∫⁺ p g ’ by METIS_TAC[integral_pos_fn, prob_space_def, p_space_def]
     >> METIS_TAC [expectation_def])
QED

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
  [8] Klenke, A.: Probability Theory: A Comprehensive Course. Third Edition.
      Springer Science & Business Media, London (2020).
 *)
