(* ========================================================================= *)
(* The Laws of Large Numbers (for Uncorrelated and I.I.D. Random Variables)  *)
(*                                                                           *)
(* Author: Chun Tian (binghe) <binghe.lisp@gmail.com> (2020 - 2021)          *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open combinTheory arithmeticTheory pred_setTheory pred_setLib logrootTheory
     realTheory realLib seqTheory transcTheory real_sigmaTheory iterateTheory
     real_topologyTheory;

open hurdUtils util_probTheory sigma_algebraTheory extrealTheory measureTheory
     borelTheory lebesgueTheory martingaleTheory probabilityTheory;

val _ = new_theory "large_number";

(* "In the formal construction of a course in the theory of probability, limit
    theorems appear as a kind of superstructure over elementary chapters, in
    which all problems have finite, purely arithmetical character. In reality,
    however, the epistemological value of the theory of probability is revealed
    only by limit theorems. Moreover, without limit theorems it is impossible
    to understand the real content of the primary concept of all our sciences -
    the concept of probability. ... The very concept of mathematical probability
    would be fruitless if it did not find its realization in the frequency of
    occurrence of events under large-scale repetition of uniform conditions."

  -- B.V. Gnedenko and A.N. Kolmogorov,
    "Limit distributions for sums of independent random variables." [13] *)

val set_ss = std_ss ++ PRED_SET_ss;

val _ = hide "S";
val _ = hide "W";

(* ------------------------------------------------------------------------- *)
(*  Definitions                                                              *)
(* ------------------------------------------------------------------------- *)

(* Law of Large Numbers: the universal conclusion for all LLN theorems *)
Definition LLN_def :
    LLN p X convergence_mode =
    let Z n x = SIGMA (\i. X i x) (count n)
    in
      ((\n x. (Z (SUC n) x - expectation p (Z (SUC n))) / &SUC n) --> (\x. 0))
       (convergence_mode p)
End

(*
Overload SLLN = “\p X. LLN p X almost_everywhere”
Overload WLLN = “\p X. LLN p X in_probability”
 *)

(* "The law of large numbers in the general case (IID) involves only the first
    moment (finite expectation), but so far we have operated with the second.
    In order to drop any assumption on the second moment, we need a new device,
    that of 'equivalent sequences', due to Khintchine (1894-1959)." [2, p.113]
 *)
Definition equivalent_def :
    equivalent p (X :num -> 'a -> extreal) Y =
      (suminf (\n. prob p {x | x IN p_space p /\ X n x <> Y n x}) < PosInf)
End

Definition truncated_def :
    truncated (X :num -> 'a -> extreal) =
      \n x. if &SUC n <= abs (X n x) then 0 else X n x
End

(* ------------------------------------------------------------------------- *)
(*  Theorems                                                                 *)
(* ------------------------------------------------------------------------- *)

(* alternative definition of LLN using ‘n’ instead of ‘SUC n’ (for end users) *)
Theorem LLN_alt_converge_AE_shift :
  !p X. LLN p X almost_everywhere <=>
        let Z n x = SIGMA (\i. X i x) (count n)
        in
          ((\n x. (Z n x - expectation p (Z n)) / &n) --> (\x. 0))
           (almost_everywhere p)
Proof
    rpt GEN_TAC
 >> Q.ABBREV_TAC ‘Z = \n x. SIGMA (\i. X i x) (count n)’
 >> EQ_TAC >> rw [LLN_def] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      ASSUME_TAC (SIMP_RULE std_ss [GSYM ADD1]
                            (Q.SPECL [‘1’, ‘p’,
                                      ‘\n x. (Z n x - expectation p (Z n)) / &n’,
                                      ‘\x. 0’] converge_AE_alt_shift)) \\
      POP_ASSUM (ASM_REWRITE_TAC o wrap),
      (* goal 2 (of 2) *)
      ASSUME_TAC (SIMP_RULE std_ss [GSYM ADD1, Once EQ_SYM_EQ]
                            (Q.SPECL [‘1’, ‘p’,
                                      ‘\n x. (Z n x - expectation p (Z n)) / &n’,
                                      ‘\x. 0’] converge_AE_alt_shift)) \\
      POP_ASSUM (ASM_REWRITE_TAC o wrap) ]
QED

(* alternative definition of LLN using ‘n’ instead of ‘SUC n’ (for end users) *)
Theorem LLN_alt_converge_PR_shift :
  !p X. LLN p X in_probability <=>
        let Z n x = SIGMA (\i. X i x) (count n)
        in
          ((\n x. (Z n x - expectation p (Z n)) / &n) --> (\x. 0))
           (in_probability p)
Proof
    rpt GEN_TAC
 >> Q.ABBREV_TAC ‘Z = \n x. SIGMA (\i. X i x) (count n)’
 >> EQ_TAC >> rw [LLN_def] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      ASSUME_TAC (SIMP_RULE std_ss [GSYM ADD1]
                            (Q.SPECL [‘1’, ‘p’,
                                      ‘\n x. (Z n x - expectation p (Z n)) / &n’,
                                      ‘\x. 0’] converge_PR_alt_shift)) \\
      POP_ASSUM (ASM_REWRITE_TAC o wrap),
      (* goal 2 (of 2) *)
      ASSUME_TAC (SIMP_RULE std_ss [GSYM ADD1, Once EQ_SYM_EQ]
                            (Q.SPECL [‘1’, ‘p’,
                                      ‘\n x. (Z n x - expectation p (Z n)) / &n’,
                                      ‘\x. 0’] converge_PR_alt_shift)) \\
      POP_ASSUM (ASM_REWRITE_TAC o wrap) ]
QED

Theorem real_random_variable_SIGMA :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) ==>
          !n. real_random_variable (\x. SIGMA (\i. X i x) (count n)) p
Proof
    RW_TAC std_ss [real_random_variable]
 >| [ (* goal 1 (of 3) *)
      MATCH_MP_TAC (INST_TYPE [``:'b`` |-> ``:num``] IN_MEASURABLE_BOREL_SUM) \\
      qexistsl_tac [`X`, `count n`] \\
     ‘sigma_algebra (p_space p,events p)’
        by METIS_TAC [prob_space_def, measure_space_def, p_space_def, events_def] \\
      rw  [FINITE_COUNT, IN_COUNT],
      (* goal 2 (of 3) *)
      MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
      RW_TAC std_ss [FINITE_COUNT, IN_COUNT],
      (* goal 3 (of 3) *)
      MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
      RW_TAC std_ss [FINITE_COUNT, IN_COUNT] ]
QED

Theorem real_random_variable_LLN :
    !p X Z. prob_space p /\
           (!n. real_random_variable (X n) p) /\
           (!n. integrable p (X n)) /\
           (!n x. x IN p_space p ==> Z n x = SIGMA (\i. X i x) (count n)) ==>
           (!n. real_random_variable
                  (\x. (Z (SUC n) x - expectation p (Z (SUC n))) / &SUC n) p)
Proof
    rpt STRIP_TAC
 (* redefine Z as an abbreviation *)
 >> Q.ABBREV_TAC ‘S = \n x. SIGMA (\i. X i x) (count n)’
 >> Know ‘expectation p (Z (SUC n)) = expectation p (S (SUC n))’
 >- (MATCH_MP_TAC expectation_cong >> rw [Abbr ‘S’]) >> Rewr'
 >> Q.ABBREV_TAC ‘M = \n. expectation p (S n)’
 >> ‘!n. expectation p (S (SUC n)) = M (SUC n)’ by METIS_TAC [] >> POP_ORW
 >> Know ‘real_random_variable (\x. (Z (SUC n) x - M (SUC n)) / &SUC n) p <=>
          real_random_variable (\x. (S (SUC n) x - M (SUC n)) / &SUC n) p’
 >- (MATCH_MP_TAC real_random_variable_cong >> rw [Abbr ‘S’]) >> Rewr'
 >> Q.PAT_X_ASSUM ‘!n x. x IN p_space p ==> Z n x = _’ K_TAC
 (* stage work *)
 >> Q.PAT_X_ASSUM `!n. real_random_variable (X n) p`
      (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
       (REWRITE_RULE [real_random_variable_def]))
 >> Know ‘!n x. x IN p_space p ==> S n x <> PosInf’
 >- (RW_TAC std_ss [Abbr ‘S’] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
     RW_TAC std_ss [FINITE_COUNT, IN_COUNT]) >> DISCH_TAC
 >> Know ‘!n x. x IN p_space p ==> S n x <> NegInf’
 >- (RW_TAC std_ss [Abbr ‘S’] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
     RW_TAC std_ss [FINITE_COUNT, IN_COUNT]) >> DISCH_TAC
 >> Know ‘!n. M n <> PosInf /\ M n <> NegInf’
 >- (Q.X_GEN_TAC ‘n’ >> ASM_SIMP_TAC std_ss [expectation_def, Abbr ‘M’] \\
     MATCH_MP_TAC integrable_finite_integral \\
     FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, events_def] \\
     Know ‘integrable p (S n) <=> integrable p (\x. SIGMA (\i. X i x) (count n))’
     >- (MATCH_MP_TAC integrable_cong >> rw []) >> Rewr' \\
     MATCH_MP_TAC integrable_sum >> rw [FINITE_COUNT])
 >> DISCH_TAC
 >> Know ‘!n x. x IN p_space p ==>
                S (SUC n) x - M (SUC n) <> PosInf /\
                S (SUC n) x - M (SUC n) <> NegInf’
 >- (rpt GEN_TAC >> DISCH_TAC \\
    ‘?a. S (SUC n) x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?b. M (SUC n) = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def])
 >> DISCH_TAC
 >> Know `!n x. x IN p_space p ==>
                (S (SUC n) x - M (SUC n)) / &SUC n =
                inv (&SUC n) * (S (SUC n) x - M (SUC n))`
 >- (rpt STRIP_TAC >> MATCH_MP_TAC div_eq_mul_linv \\
    ‘?a. S (SUC n) x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?b. M (SUC n) = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def] \\
     RW_TAC real_ss [extreal_lt_eq, extreal_of_num_def])
 >> DISCH_TAC
 >> Know ‘real_random_variable (\x. (S (SUC n) x - M (SUC n)) / &SUC n) p <=>
          real_random_variable (\x. inv (&SUC n) * (S (SUC n) x - M (SUC n))) p’
 >- (MATCH_MP_TAC real_random_variable_cong \\
     RW_TAC std_ss []) >> Rewr'
 >> Know ‘!n. inv (&SUC n) = Normal (inv (&SUC n))’
 >- (Q.X_GEN_TAC ‘n’ \\
    ‘(0 :real) <> &SUC n’ by RW_TAC real_ss [] \\
     ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_inv_eq])
 >> Rewr'
 >> ‘sigma_algebra (p_space p,events p)’
       by METIS_TAC [prob_space_def, measure_space_def, p_space_def, events_def]
 >> SIMP_TAC std_ss [real_random_variable]
 >> reverse CONJ_TAC
 >- (Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
    ‘?r. S (SUC n) x - M (SUC n) = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_mul_def])
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
 >> qexistsl_tac [`\x. S (SUC n) x - M (SUC n)`, `inv (&SUC n)`] >> rw []
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB
 >> qexistsl_tac [`S (SUC n)`, `\x. M (SUC n)`] >> rw []
 >| [ (* goal 1 (of 2) *)
      Q.UNABBREV_TAC ‘S’ \\
      MATCH_MP_TAC (INST_TYPE [``:'b`` |-> ``:num``] IN_MEASURABLE_BOREL_SUM) \\
      qexistsl_tac [`X`, `count (SUC n)`] >> rw [] \\
      FULL_SIMP_TAC std_ss [random_variable_def],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST' >> art [] ]
QED

(* Theorem 5.1.1, Part I [2, p.108]: The Weak Law of Large Numbers

   (uncorrelated random sequence with a common bound of variances)
 *)
Theorem WLLN_uncorrelated_L2 :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) /\
         (!i j. i <> j ==> uncorrelated p (X i) (X j)) /\
         (?c. c <> PosInf /\ !n. variance p (X n) <= c) ==>
          LLN p X (in_lebesgue 2)
Proof
    RW_TAC std_ss [LLN_def]
 >> Know `!n. integrable p (X n)`
 >- (GEN_TAC >> MATCH_MP_TAC finite_second_moments_imp_integrable >> art [] \\
     ASM_SIMP_TAC std_ss [finite_second_moments_eq_finite_variance] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC `c` >> rw [GSYM lt_infty]) >> DISCH_TAC
 >> Know ‘!n. real_random_variable (Z n) p’
 >- (rw [Abbr ‘Z’] \\
     MATCH_MP_TAC real_random_variable_SIGMA >> art [])
 >> DISCH_TAC
 >> Know ‘!n. real_random_variable
                (\x. (Z (SUC n) x - expectation p (Z (SUC n))) / &SUC n) p’
 >- (MATCH_MP_TAC real_random_variable_LLN \\
     Q.EXISTS_TAC ‘X’ >> rw [Abbr ‘Z’])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘M = \n. expectation p (Z n)’
 >> ‘!n. expectation p (Z (SUC n)) = M (SUC n)’ by METIS_TAC []
 >> POP_ASSUM (FULL_SIMP_TAC std_ss o wrap)
 (* renamed ‘Z’ to ‘S’ *)
 >> rename1 ‘((\n x. (S (SUC n) x - M (SUC n)) / &SUC n) --> (\x. 0))
               (in_lebesgue 2 p)’
 >> ‘real_random_variable (\x. 0) p’ by PROVE_TAC [real_random_variable_zero]
 >> Q.PAT_X_ASSUM `!n. real_random_variable (X n) p`
      (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
       (REWRITE_RULE [real_random_variable_def]))
 >> Know ‘!n. M n <> PosInf /\ M n <> NegInf’
 >- (Q.X_GEN_TAC ‘n’ \\
     ASM_SIMP_TAC std_ss [expectation_def, Abbr ‘M’] \\
     MATCH_MP_TAC integrable_finite_integral \\
     CONJ_TAC >- FULL_SIMP_TAC std_ss [prob_space_def] \\
    ‘S n = \x. SIGMA (\i. X i x) (count n)’ by METIS_TAC [] >> POP_ORW \\
     MATCH_MP_TAC integrable_sum \\
     FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, FINITE_COUNT, IN_COUNT])
 >> DISCH_TAC
 >> ‘!n x. x IN p_space p ==> S n x <> PosInf /\ S n x <> NegInf’
       by METIS_TAC [real_random_variable_def]
 >> Know ‘!n x. x IN p_space p ==>
                S (SUC n) x - M (SUC n) <> PosInf /\
                S (SUC n) x - M (SUC n) <> NegInf’
 >- (rpt GEN_TAC >> DISCH_TAC \\
    ‘?a. S (SUC n) x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?b. M (SUC n) = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def])
 >> DISCH_TAC
 >> Know `!n x. x IN p_space p ==>
                (S (SUC n) x - M (SUC n)) / &SUC n =
                inv (&SUC n) * (S (SUC n) x - M (SUC n))`
 >- (rpt STRIP_TAC >> MATCH_MP_TAC div_eq_mul_linv \\
    `?a. S (SUC n) x = Normal a` by METIS_TAC [extreal_cases] >> POP_ORW \\
    `?b. M (SUC n) = Normal b` by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def] \\
     RW_TAC real_ss [extreal_lt_eq, extreal_of_num_def])
 >> DISCH_TAC
 >> Know ‘((\n x. (S (SUC n) x - M (SUC n)) / &SUC n)       --> (\x. 0)) (in_lebesgue 2 p) <=>
          ((\n x. inv (&SUC n) * (S (SUC n) x - M (SUC n))) --> (\x. 0)) (in_lebesgue 2 p)’
 >- (MATCH_MP_TAC converge_LP_cong \\
     RW_TAC std_ss []) >> Rewr'
 >> Know ‘!n. real_random_variable (\x. (S (SUC n) x - M (SUC n)) / &SUC n) p <=>
              real_random_variable (\x. inv (&SUC n) * (S (SUC n) x - M (SUC n))) p’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC real_random_variable_cong \\
     RW_TAC std_ss [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> POP_ASSUM K_TAC (* !n x. x IN p_space p ==> (S (SUC n) x - M (SUC n)) / &SUC n = *)
 >> Know `!n. inv (&SUC n) = Normal (inv (&SUC n))`
 >- (GEN_TAC >> `(0 :real) <> &SUC n` by RW_TAC real_ss [] \\
     ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_inv_eq])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> ‘sigma_algebra (m_space p,measurable_sets p)’
       by METIS_TAC [prob_space_def, measure_space_def]
 >> Q.ABBREV_TAC ‘Z = \n x. Normal (inv (&SUC n)) * (S (SUC n) x - M (SUC n))’
 >> ‘!n. real_random_variable (Z n) p’ by rw [Abbr ‘Z’]
 (* stage work *)
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
    ‘!n. expectation p (S n) = M n’ by METIS_TAC [] >> POP_ORW \\
     SIMP_TAC std_ss [pow_mul, extreal_pow_def, expectation_def] \\
     HO_MATCH_MP_TAC integral_cmul \\
     STRONG_CONJ_TAC >- FULL_SIMP_TAC std_ss [prob_space_def] \\
     DISCH_TAC \\
     Know `measure_space p /\
           (!x. x IN m_space p ==> 0 <= (\x. (S (SUC n) x - M (SUC n)) pow 2) x)`
     >- (fs [le_pow2]) \\
     DISCH_THEN (ONCE_REWRITE_TAC o wrap o (MATCH_MP integrable_pos)) \\
     CONJ_TAC (* Boreal_measurable *)
     >- (HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_POW \\
         CONJ_TAC >- art [] \\
         reverse CONJ_TAC >- FULL_SIMP_TAC std_ss [space_def, p_space_def] \\
         HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
         qexistsl_tac [`S (SUC n)`, `\x. M (SUC n)`] \\
         CONJ_TAC >- art [] \\
         SIMP_TAC std_ss [space_def] \\
         ONCE_REWRITE_TAC [CONJ_ASSOC] \\
         reverse CONJ_TAC >- FULL_SIMP_TAC std_ss [p_space_def] \\
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
    `!n. M n = expectation p (S n)` by METIS_TAC [] >> POP_ORW \\
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
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) /\
         (!i j. i <> j ==> uncorrelated p (X i) (X j)) /\
         (?c. c <> PosInf /\ !n. variance p (X n) <= c) ==>
          LLN p X in_probability
Proof
    RW_TAC std_ss [LLN_def]
 >> MATCH_MP_TAC converge_LP_imp_PR'
 >> Q.EXISTS_TAC ‘2’ >> rw []
 >- (MATCH_MP_TAC real_random_variable_LLN \\
     Q.EXISTS_TAC ‘X’ >> rw [] \\
     MATCH_MP_TAC finite_second_moments_imp_integrable >> art [] \\
     ASM_SIMP_TAC std_ss [finite_second_moments_eq_finite_variance] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC `c` >> rw [GSYM lt_infty])
 >> Know ‘((\n x. (Z (SUC n) x - expectation p (Z (SUC n))) / &SUC n) -->
            (\x. 0)) (in_lebesgue 2 p) <=> LLN p X (in_lebesgue 2)’
 >- rw [LLN_def] >> Rewr'
 >> MATCH_MP_TAC WLLN_uncorrelated_L2 >> art []
 >> Q.EXISTS_TAC `c` >> RW_TAC std_ss []
QED

(* Theorem 5.1.2 [2, p.108]: The Strong Law of Large Numbers
   (for uncorrelated random sequence with a common bound of variances)

   Without loss of generality we may suppose that expectation (X j) = 0 for
   each j, so that the (X j)'s are orthogonal.
 *)
Theorem SLLN_uncorrelated_wlog[local] :
    !p X S M c. prob_space p /\ (!n. real_random_variable (X n) p) /\
       (!i j. i <> j ==> uncorrelated p (X i) (X j)) /\
       c <> PosInf /\ (!n. variance p (X n) <= c) /\
       (!n x. S n x = SIGMA (\i. X i x) (count n)) /\
       (!n. M n = expectation p (S n)) ==>
       ?(Y :num -> 'a -> extreal) W.
           (!n x. x IN p_space p ==> W n x = SIGMA (\i. Y i x) (count n)) /\
           (!n x. x IN p_space p ==> S n x - M n = W n x) /\
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
    `!x. x IN p_space p ==>
         X n x - integral p (X n) = X n x + (\x. -integral p (X n)) x`
       by (METIS_TAC [prob_space_def, integrable_finite_integral,
                      extreal_sub_add]) \\
     Know ‘integral p (\x. X n x - integral p (X n)) =
           integral p (\x. X n x + (\x. -integral p (X n)) x)’
     >- (MATCH_MP_TAC integral_cong \\
         FULL_SIMP_TAC std_ss [prob_space_def, p_space_def]) >> Rewr' \\
     POP_ASSUM K_TAC \\
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
     >- (GEN_TAC >> DISCH_TAC \\
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
 >> Know ‘expectation p (S n) =
          expectation p (\x. SIGMA (\i. X i x) (count n))’
 >- (MATCH_MP_TAC expectation_cong >> rw []) >> Rewr'
 >> MATCH_MP_TAC (REWRITE_RULE [GSYM expectation_def] integral_sum)
 >> FULL_SIMP_TAC std_ss [FINITE_COUNT, prob_space_def, real_random_variable_def,
                          p_space_def]
QED

Theorem SLLN_uncorrelated :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) /\
         (!i j. i <> j ==> uncorrelated p (X i) (X j)) /\
         (?c. c <> PosInf /\ !n. variance p (X n) <= c) ==>
          LLN p X almost_everywhere
Proof
    RW_TAC std_ss [LLN_def]
 (* without loss of generality *)
 >> MP_TAC (Q.SPECL [`p`, `X`, `Z`, `\n. expectation p (Z n)`, `c`]
                    SLLN_uncorrelated_wlog)
 >> RW_TAC std_ss []
 >> Know ‘((\n x. (Z (SUC n) x - expectation p (Z (SUC n))) /
                  &SUC n) --> (\x. 0)) (almost_everywhere p) <=>
          ((\n x. W (SUC n) x / &SUC n) --> (\x. 0)) (almost_everywhere p)’
 >- (MATCH_MP_TAC converge_AE_cong \\
     Q.EXISTS_TAC ‘0’ >> RW_TAC arith_ss []) >> Rewr'
 >> Q.PAT_X_ASSUM `!n x. x IN p_space p ==> _ = W n x` K_TAC
 (* clean up X and S *)
 >> Q.PAT_X_ASSUM `!n. real_random_variable (X n) p`            K_TAC
 >> Q.PAT_X_ASSUM `!i j. i <> j ==> uncorrelated p (X i) (X j)` K_TAC
 >> Q.PAT_X_ASSUM `!n. variance p (X n) <= c`                   K_TAC
 >> Q.UNABBREV_TAC ‘Z’
 (* rename Z to S, Y to X, c to M *)
 >> rename1 `!n x. x IN p_space p ==> S n x = SIGMA (\i. X i x) (count n)`
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
     Know ‘variance p (S n) = variance p (\x. SIGMA (\i. X i x) (count n))’
     >- (MATCH_MP_TAC variance_cong >> rw []) >> Rewr' \\
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
     Know ‘expectation p (S n) = expectation p (\x. SIGMA (\i. X i x) (count n))’
     >- (MATCH_MP_TAC expectation_cong >> rw []) >> Rewr' \\
     fs [prob_space_def, real_random_variable_def, expectation_def,
         random_variable_def, p_space_def, events_def] \\
     Know `integral p (\x. SIGMA (\i. X i x) (count n)) =
           SIGMA (\i. integral p (X i)) (count n)`
     >- (MATCH_MP_TAC integral_sum \\
         RW_TAC std_ss [IN_COUNT, FINITE_COUNT]) >> Rewr' >> rw [] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_ZERO >> REWRITE_TAC [FINITE_COUNT])
 >> DISCH_TAC
 >> Know `!n x. x IN p_space p ==> S n x <> PosInf`
 >- (RW_TAC std_ss [] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
     fs [real_random_variable_def, FINITE_COUNT, IN_COUNT]) >> DISCH_TAC
 >> Know `!n x. x IN p_space p ==> S n x <> NegInf`
 >- (RW_TAC std_ss [] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
     fs [real_random_variable_def, FINITE_COUNT, IN_COUNT]) >> DISCH_TAC
 >> Know `!n. real_random_variable (S n) p`
 >- (RW_TAC std_ss [real_random_variable, p_space_def, events_def] \\
     Know ‘S n IN measurable (m_space p,measurable_sets p) Borel <=>
           (\x. SIGMA (\i. X i x) (count n))
               IN measurable (m_space p,measurable_sets p) Borel’
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONG \\
         FULL_SIMP_TAC std_ss [p_space_def]) >> Rewr' \\
     MATCH_MP_TAC (INST_TYPE [``:'b`` |-> ``:num``] IN_MEASURABLE_BOREL_SUM) \\
     qexistsl_tac [`X`, `count n`] \\
     fs [real_random_variable, p_space_def,
         events_def, space_def, prob_space_def, measure_space_def])
 >> DISCH_TAC
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
 >> Know `!e n x. x IN p_space p ==>
                 (&(SUC n ** 2) * e < abs (S (SUC n ** 2) x) <=>
                  e < abs (S (SUC n ** 2) x / &(SUC n ** 2)))`
 >- (rpt STRIP_TAC \\
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
     REWRITE_TAC [Once mul_comm])
 >> DISCH_TAC
 >> Know ‘!e n. {x | x IN p_space p /\ &(SUC n ** 2) * e < abs (S (SUC n ** 2) x)} =
                {x | x IN p_space p /\ e < abs (S (SUC n ** 2) x / &(SUC n ** 2))}’
 >- (rw [Once EXTENSION] >> METIS_TAC []) >> Rewr'
 >> POP_ASSUM K_TAC
 (* applying converge_AE_alt_limsup *)
 >> Q.ABBREV_TAC `Z = \n x. S (SUC n ** 2) x / &(SUC n ** 2)`
 >> `!n x. S (SUC n ** 2) x / &(SUC n ** 2) = Z n x` by METIS_TAC [] >> POP_ORW
 >> Q.PAT_X_ASSUM `!n e. 0 < n /\ 0 < e /\ e <> PosInf ==> P` K_TAC
 >> DISCH_TAC
 >> Know `!n. real_random_variable (Z n) p`
 >- (Q.X_GEN_TAC ‘n’ \\
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
     >- (GEN_TAC >> DISCH_TAC \\
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
 >> Know `!n k x. x IN p_space p ==> d n k x <> PosInf /\ d n k x <> NegInf`
 >- (rpt GEN_TAC >> DISCH_TAC \\
     SIMP_TAC std_ss [Abbr `d`] \\
    `?a. S k x = Normal a` by METIS_TAC [extreal_cases] \\
    `?b. S (n ** 2) x = Normal b` by METIS_TAC [extreal_cases] \\
     ASM_SIMP_TAC std_ss [extreal_sub_def, extreal_abs_def, extreal_not_infty])
 >> DISCH_TAC
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
 >- (rw [expectation_def] \\
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
         HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_POW \\
         CONJ_TAC >- FULL_SIMP_TAC std_ss [measure_space_def] \\
         reverse CONJ_TAC
         >- (Q.PAT_X_ASSUM ‘!n x. x IN m_space p ==> S n x = _’ K_TAC \\
             Q.X_GEN_TAC ‘x’ >> simp [space_def] >> DISCH_TAC \\
            ‘?a. S i x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
            ‘?b. S (n ** 2) x = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
             rw [extreal_sub_def, extreal_not_infty]) \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
         qexistsl_tac [‘S i’, ‘S (n ** 2)’] \\
         CONJ_TAC >- FULL_SIMP_TAC std_ss [measure_space_def] \\
         rw [space_def]) >> BETA_TAC >> Rewr' \\
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
     Know ‘expectation p (\x'. (S k x' - S (n ** 2) x') pow 2) =
           expectation p (\x. (SIGMA (\i. X i x) (count k) -
                               SIGMA (\i. X i x) (count (n ** 2))) pow 2)’
     >- (MATCH_MP_TAC expectation_cong >> rw []) >> Rewr' \\
     Know ‘expectation p (\x. (S (SUC n ** 2) x - S (n ** 2) x) pow 2) =
           expectation p (\x. (SIGMA (\i. X i x) (count (SUC n ** 2)) -
                               SIGMA (\i. X i x) (count (n ** 2))) pow 2)’
     >- (MATCH_MP_TAC expectation_cong >> rw []) >> Rewr' \\
     Know `count k = {j | n ** 2 <= j /\ j < k} UNION (count (n ** 2))`
     >- (RW_TAC set_ss [Once EXTENSION, IN_COUNT] >> rw []) >> Rewr' \\
     Know `DISJOINT {j | n ** 2 <= j /\ j < k} (count (n ** 2))`
     >- (RW_TAC set_ss [DISJOINT_ALT, IN_COUNT] >> rw []) >> DISCH_TAC \\
     Know `count (SUC n ** 2) = {j | n ** 2 <= j /\ j < SUC n ** 2} UNION (count (n ** 2))`
     >- (RW_TAC set_ss [Once EXTENSION, IN_COUNT] >> rw []) >> Rewr' \\
     Know `DISJOINT {j | n ** 2 <= j /\ j < SUC n ** 2} (count (n ** 2))`
     >- (RW_TAC set_ss [DISJOINT_ALT, IN_COUNT] >> rw []) >> DISCH_TAC \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
     Know `expectation p
             (\x. (SIGMA (\i. X i x) ({j | n ** 2 <= j /\ j < k} UNION count (n ** 2)) -
                   SIGMA (\i. X i x) (count (n ** 2))) pow 2) =
           expectation p
             (\x. (SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < k} +
                   SIGMA (\i. X i x) (count (n ** 2)) -
                   SIGMA (\i. X i x) (count (n ** 2))) pow 2)`
     >- (MATCH_MP_TAC expectation_cong >> RW_TAC std_ss [] \\
         Suff ‘SIGMA (\i. X i x) ({j | n ** 2 <= j /\ j < k} UNION (count (n ** 2))) =
               SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < k} +
               SIGMA (\i. X i x) (count (n ** 2))’ >- rw [] \\
         irule EXTREAL_SUM_IMAGE_DISJOINT_UNION \\
         fs [FINITE_SING, FINITE_COUNT]) >> Rewr' \\
     Know `expectation p
             (\x. (SIGMA (\i. X i x) ({j | n ** 2 <= j /\ j < SUC n ** 2} UNION count (n ** 2)) -
                   SIGMA (\i. X i x) (count (n ** 2))) pow 2) =
           expectation p
             (\x. (SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < SUC n ** 2} +
                   SIGMA (\i. X i x) (count (n ** 2)) -
                   SIGMA (\i. X i x) (count (n ** 2))) pow 2)`
     >- (MATCH_MP_TAC expectation_cong >> RW_TAC std_ss [] \\
         Suff ‘SIGMA (\i. X i x) ({j | n ** 2 <= j /\ j < SUC n ** 2} UNION (count (n ** 2))) =
               SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < SUC n ** 2} +
               SIGMA (\i. X i x) (count (n ** 2))’ >- rw [] \\
         irule EXTREAL_SUM_IMAGE_DISJOINT_UNION \\
         fs [FINITE_SING, FINITE_COUNT]) >> Rewr' \\
     Know `!x. x IN p_space p ==> SIGMA (\i. X i x) (count (n ** 2)) <> PosInf`
     >- (GEN_TAC >> DISCH_TAC \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
         rw [FINITE_COUNT]) >> DISCH_TAC \\
     Know `!x. x IN p_space p ==> SIGMA (\i. X i x) (count (n ** 2)) <> NegInf`
     >- (GEN_TAC >> DISCH_TAC \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
         rw [FINITE_COUNT]) >> DISCH_TAC \\
     Know ‘!m. expectation p
                 (\x. (SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < m} +
                       SIGMA (\i. X i x) (count (n ** 2)) -
                       SIGMA (\i. X i x) (count (n ** 2))) pow 2) =
               expectation p
                 (\x. (SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < m}) pow 2)’
     >- (GEN_TAC >> MATCH_MP_TAC expectation_cong >> RW_TAC std_ss [] \\
         Suff ‘SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < m} +
               SIGMA (\i. X i x) (count (n ** 2)) -
               SIGMA (\i. X i x) (count (n ** 2)) =
               SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < m}’ >- rw [] \\
         rw [add_sub]) >> Rewr' \\
     (* now converting LHS and RHS to variances *)
     Know `!m x. x IN p_space p ==>
                 SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < m} =
                 (\x. SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < m}) x -
                 expectation p (\x. SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < m})`
     >- (rpt GEN_TAC >> DISCH_TAC \\
         Suff `expectation p (\x. SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < m}) = 0`
         >- rw [sub_rzero] \\
         REWRITE_TAC [expectation_def] \\
         Know `integral p (\x. SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < m}) =
               SIGMA (\i. integral p (X i)) {j | n ** 2 <= j /\ j < m}`
         >- (MATCH_MP_TAC integral_sum \\
             fs [p_space_def, prob_space_def, expectation_def]) >> Rewr' \\
         fs [expectation_def] \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_ZERO >> art []) >> DISCH_TAC \\
     Know ‘!m. expectation p
                 (\x. SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < m} pow 2) =
               expectation p
                 (\x. ((\x. SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < m}) x -
                       expectation p (\x. SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < m})) pow 2)’
     >- (GEN_TAC >> MATCH_MP_TAC expectation_cong >> RW_TAC std_ss [] \\
         Suff ‘SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < m} =
               (\x. SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < m}) x -
               expectation p
                 (\x. SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < m})’
         >- PROVE_TAC [] \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> Rewr' \\
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
     Know ‘expectation p (\x. (S (SUC n ** 2) x - S (n ** 2) x) pow 2) =
           expectation p
             (\x. (SIGMA (\i. X i x) (count (SUC n ** 2)) -
                   SIGMA (\i. X i x) (count (n ** 2))) pow 2)’
     >- (MATCH_MP_TAC expectation_cong >> RW_TAC std_ss []) >> Rewr' \\
     Know `count (SUC n ** 2) = (N n) UNION (count (n ** 2))`
     >- (RW_TAC set_ss [Abbr `N`, Once EXTENSION, IN_COUNT] \\
         EQ_TAC >> RW_TAC arith_ss [] \\
         MATCH_MP_TAC LESS_TRANS >> Q.EXISTS_TAC `n ** 2` >> rw []) >> Rewr' \\
     Know `DISJOINT (N n) (count (n ** 2))`
     >- (RW_TAC set_ss [Abbr `N`, DISJOINT_ALT, IN_COUNT] >> rw []) >> DISCH_TAC \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
     Know `expectation p
             (\x. (SIGMA (\i. X i x) (N n UNION (count (n ** 2))) -
                   SIGMA (\i. X i x) (count (n ** 2))) pow 2) =
           expectation p
             (\x. (SIGMA (\i. X i x) (N n) +
                   SIGMA (\i. X i x) (count (n ** 2)) -
                   SIGMA (\i. X i x) (count (n ** 2))) pow 2)`
     >- (MATCH_MP_TAC expectation_cong >> RW_TAC std_ss [] \\
         Suff ‘SIGMA (\i. X i x) (N n UNION count (n ** 2)) =
               SIGMA (\i. X i x) (N n) + SIGMA (\i. X i x) (count (n ** 2))’
         >- PROVE_TAC [] \\
         irule EXTREAL_SUM_IMAGE_DISJOINT_UNION \\
         fs [FINITE_SING, FINITE_COUNT]) >> Rewr' \\
     Know `!x. x IN p_space p ==> SIGMA (\i. X i x) (count (n ** 2)) <> PosInf`
     >- (GEN_TAC >> DISCH_TAC \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
         rw [FINITE_COUNT]) >> DISCH_TAC \\
     Know `!x. x IN p_space p ==> SIGMA (\i. X i x) (count (n ** 2)) <> NegInf`
     >- (GEN_TAC >> DISCH_TAC \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
         rw [FINITE_COUNT]) >> DISCH_TAC \\
     Know ‘expectation p
             (\x. (SIGMA (\i. X i x) (N n) +
                   SIGMA (\i. X i x) (count (n ** 2)) -
                   SIGMA (\i. X i x) (count (n ** 2))) pow 2) =
           expectation p (\x. SIGMA (\i. X i x) (N n) pow 2)’
     >- (MATCH_MP_TAC expectation_cong >> RW_TAC std_ss [add_sub]) >> Rewr' \\
     Suff `expectation p (\x. SIGMA (\i. X i x) (N n)) = 0` >- rw [sub_rzero] \\
     RW_TAC std_ss [expectation_def, Abbr `N`] \\
     Know `integral p (\x. SIGMA (\i. X i x) {j | n ** 2 <= j /\ j < SUC n ** 2}) =
                SIGMA (\i. integral p (X i)) {j | n ** 2 <= j /\ j < SUC n ** 2}`
     >- (MATCH_MP_TAC integral_sum \\
         fs [p_space_def, prob_space_def, expectation_def]) >> Rewr' \\
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
 >- (Q.X_GEN_TAC ‘n’ \\
     SIMP_TAC std_ss [Abbr `W`, real_random_variable_def,
                      random_variable_def, p_space_def, events_def] \\
     reverse CONJ_TAC
     >- (GEN_TAC >> DISCH_TAC >> art [extreal_of_num_def] \\
         FULL_SIMP_TAC std_ss [p_space_def] \\
        `?r. d (SUC n) (f (SUC n) x) x = Normal r` by METIS_TAC [extreal_cases] \\
         POP_ORW \\
         Suff `&(SUC n ** 2) <> (0 :real)` >- METIS_TAC [extreal_div_eq, extreal_not_infty] \\
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
     Q.EXISTS_TAC `\x. S k x - S (SUC n ** 2) x` >> art [] \\
     reverse CONJ_TAC >- rw [space_def] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
     qexistsl_tac [`S k`, `S (SUC n ** 2)`] \\
     fs [space_def, real_random_variable, p_space_def, events_def]) >> DISCH_TAC
 >> Know `!n. finite_second_moments p (W n)`
 >- (RW_TAC std_ss [finite_second_moments_literally, expectation_def] \\
     Q.UNABBREV_TAC `W` >> BETA_TAC \\
     Know `integral p (\x. (D (SUC n) x / &(SUC n ** 2)) pow 2) =
           integral p (\x. (inv (&(SUC n ** 2)) * D (SUC n) x) pow 2)`
     >- (MATCH_MP_TAC integral_cong \\
         CONJ_TAC >- FULL_SIMP_TAC std_ss [prob_space_def] \\
         RW_TAC std_ss [] \\
         Suff ‘d (SUC n) (f (SUC n) x) x / &(SUC n ** 2) =
               inv (&(SUC n ** 2)) * d (SUC n) (f (SUC n) x) x’ >- rw [] \\
         MATCH_MP_TAC div_eq_mul_linv >> art [] \\
         FULL_SIMP_TAC std_ss [p_space_def] \\
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
     Know `!n x. x IN p_space p ==>
                 D (SUC n) x / &(SUC n ** 2) = inv (&(SUC n ** 2)) * D (SUC n) x`
     >- (rpt GEN_TAC >> DISCH_TAC \\
         MATCH_MP_TAC div_eq_mul_linv >> art [] \\
         FULL_SIMP_TAC std_ss [p_space_def] \\
         RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq]) >> DISCH_TAC \\
     Know ‘!n. pos_fn_integral p (\x. (D (SUC n) x / &(SUC n ** 2)) pow 2) =
               pos_fn_integral p (\x. (inv (&(SUC n ** 2)) * D (SUC n) x) pow 2)’
     >- (Q.X_GEN_TAC ‘n’ \\
         MATCH_MP_TAC pos_fn_integral_cong \\
         CONJ_TAC >- FULL_SIMP_TAC std_ss [prob_space_def] \\
         CONJ_TAC >- rw [le_pow2] \\
         CONJ_TAC >- rw [le_pow2] \\
         FULL_SIMP_TAC std_ss [p_space_def]) >> Rewr' \\
     POP_ASSUM K_TAC \\
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
 >> Know `!k x. x IN p_space p ==>
                abs (S (SUC k) x) / &SUC k <=
               (abs (S (&(ROOT 2 (SUC k) ** 2)) x) + abs (D (&(ROOT 2 (SUC k))) x))
                / &(ROOT 2 (SUC k) ** 2)`
 >- (rpt GEN_TAC >> DISCH_TAC \\
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
             MATCH_MP_TAC abs_not_infty >> rw []) >> Rewr' \\
         Know `abs (S (SUC k) x) / &(n ** 2) = inv (&(n ** 2)) * abs (S (SUC k) x)`
         >- (MATCH_MP_TAC div_eq_mul_linv \\
             ONCE_REWRITE_TAC [CONJ_ASSOC] \\
             CONJ_TAC >- (MATCH_MP_TAC abs_not_infty >> rw []) \\
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
         ONCE_REWRITE_TAC [CONJ_ASSOC] >> art [] \\
         MATCH_MP_TAC abs_not_infty >> rw []) >> Rewr' \\
     Know `(abs (S (n ** 2) x) + abs (D n x)) / &(n ** 2) =
           inv (&(n ** 2)) * (abs (S (n ** 2) x) + abs (D n x))`
     >- (MATCH_MP_TAC div_eq_mul_linv \\
         ONCE_REWRITE_TAC [CONJ_ASSOC] \\
         reverse CONJ_TAC >- (ASM_SIMP_TAC real_ss [extreal_of_num_def, extreal_lt_eq]) \\
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
     CONJ_TAC >- (MATCH_MP_TAC abs_triangle_sub >> rw []) \\
     Know `abs (S (n ** 2) x) + abs (S (SUC k) x - S (n ** 2) x) <=
           abs (S (n ** 2) x) + abs (S (f n x) x - S (n ** 2) x) <=>
           abs (S (SUC k) x - S (n ** 2) x) <= abs (S (f n x) x - S (n ** 2) x)`
     >- (MATCH_MP_TAC le_ladd \\
         ONCE_REWRITE_TAC [CONJ_SYM] \\
         MATCH_MP_TAC abs_not_infty >> rw []) >> Rewr' \\
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
      (MP_TAC o (SIMP_RULE std_ss [converge_AE_def, AE_DEF,
                                   GSYM IN_NULL_SET, LIM_SEQUENTIALLY, dist]))
 >> DISCH_THEN (Q.X_CHOOSE_THEN `N1` STRIP_ASSUME_TAC)
 >> Q.PAT_X_ASSUM `(W --> (\x. 0)) (almost_everywhere p)`
      (MP_TAC o (SIMP_RULE std_ss [converge_AE_def, AE_DEF,
                                   GSYM IN_NULL_SET, LIM_SEQUENTIALLY, dist]))
 >> DISCH_THEN (Q.X_CHOOSE_THEN `N2` STRIP_ASSUME_TAC)
 >> SIMP_TAC std_ss [converge_AE_def, AE_DEF,
                     GSYM IN_NULL_SET, LIM_SEQUENTIALLY, dist]
 >> Q.EXISTS_TAC `N1 UNION N2`
 >> STRONG_CONJ_TAC
 >- (MATCH_MP_TAC NULL_SET_UNION \\
     FULL_SIMP_TAC bool_ss [prob_space_def]) >> DISCH_TAC
 >> rpt STRIP_TAC
 >> `(m_space p DIFF (N1 UNION N2)) SUBSET (m_space p DIFF N1)` by SET_TAC []
 >> `(m_space p DIFF (N1 UNION N2)) SUBSET (m_space p DIFF N2)` by SET_TAC []
 (* clean up disturbing assumptions *)
 >> Q.PAT_X_ASSUM `!n x. x IN p_space p ==>
                         S n x = SIGMA (\i. X i x) (count n)` K_TAC
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
 >> ‘m_space p DIFF (N1 UNION N2) SUBSET m_space p’ by SET_TAC []
 >> ‘x IN m_space p’ by METIS_TAC [SUBSET_DEF]
 >> NTAC 2 (Q.PAT_X_ASSUM `_ SUBSET m_space p DIFF _` K_TAC)
 >> NTAC 3 (Q.PAT_X_ASSUM `x IN m_space p DIFF _`     K_TAC)
 >> Q.PAT_X_ASSUM ‘m_space p DIFF (N1 UNION N2) SUBSET m_space p’ K_TAC
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
 >- (Q.X_GEN_TAC ‘n’ \\
     FULL_SIMP_TAC std_ss [p_space_def] \\
    `?r. S (SUC n) x = Normal r` by METIS_TAC [extreal_cases] >> POP_ORW \\
    `&SUC n <> (0: real)` by RW_TAC real_ss [] \\
     ASM_SIMP_TAC real_ss [extreal_of_num_def, extreal_abs_def, real_normal,
                           extreal_div_eq, extreal_lt_eq, ABS_DIV, ABS_N])
 >> Rewr'
 >> Know `!n e. abs (real (S (SUC n ** 2) x / &(SUC n ** 2))) < e <=>
                abs (S (SUC n ** 2) x) / &(SUC n ** 2) < Normal e`
 >- (rpt GEN_TAC \\
     FULL_SIMP_TAC std_ss [p_space_def] \\
    `?r. S (SUC n ** 2) x = Normal r` by METIS_TAC [extreal_cases] >> POP_ORW \\
    `&(SUC n ** 2) <> (0: real)` by RW_TAC real_ss [] \\
     ASM_SIMP_TAC real_ss [extreal_of_num_def, extreal_abs_def, real_normal,
                           extreal_div_eq, extreal_lt_eq, ABS_DIV, ABS_N])
 >> DISCH_THEN ((FULL_SIMP_TAC bool_ss) o wrap)
 >> Know `!n e. abs (real (D (SUC n) x / &(SUC n ** 2))) < e <=>
                abs (D (SUC n) x) / &(SUC n ** 2) < Normal e`
 >- (rpt GEN_TAC \\
    `?r. D (SUC n) x = Normal r` by METIS_TAC [extreal_cases, p_space_def] >> POP_ORW \\
    `&(SUC n ** 2) <> (0: real)` by RW_TAC real_ss [] \\
     ASM_SIMP_TAC real_ss [extreal_of_num_def, extreal_abs_def, real_normal,
                           extreal_div_eq, extreal_lt_eq, ABS_DIV, ABS_N])
 >> DISCH_THEN ((FULL_SIMP_TAC bool_ss) o wrap)
 (* continue estimating N *)
 >> NTAC 2 (Q.PAT_X_ASSUM `!e. 0 < e ==> P` (MP_TAC o (Q.SPEC `e / 2`)))
 >> Know `0 < e / 2`
 >- (MATCH_MP_TAC REAL_LT_DIV >> RW_TAC real_ss [])
 >> `!n x. x IN m_space p ==>
           D n x <> PosInf /\ D n x <> NegInf` by METIS_TAC [p_space_def]
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
 >> CONJ_TAC
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> art [p_space_def])
 >> Q.PAT_X_ASSUM `!k x. x IN p_space p ==> abs (S (SUC k) x) / &SUC k <= _` K_TAC
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
     FULL_SIMP_TAC std_ss [p_space_def] \\
     CONJ_TAC >- (MATCH_MP_TAC abs_not_infty >> rw []) \\
     ONCE_REWRITE_TAC [CONJ_ASSOC] \\
     CONJ_TAC >- (MATCH_MP_TAC abs_not_infty >> rw []) \\
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

Theorem equivalent_comm :
    !X Y. equivalent p (X :num -> 'a -> extreal) Y <=> equivalent p Y X
Proof
    rw [equivalent_def]
 >> Suff ‘!n. {x | x IN p_space p /\ X n x <> Y n x} =
              {x | x IN p_space p /\ Y n x <> X n x}’ >- Rewr
 >> rw [Once EXTENSION]
 >> METIS_TAC []
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

Theorem equivalent_events :
    !p X Y. prob_space p /\
            (!n. real_random_variable (X n) p) /\
            (!n. real_random_variable (Y n) p) ==>
            !n. {x | x IN p_space p /\ X n x <> Y n x} IN events p
Proof
    RW_TAC std_ss [events_def, p_space_def, prob_space_def]
 >> `{x | x IN m_space p /\ X n x <> Y n x} =
     {x | X n x <> Y n x} INTER m_space p` by SET_TAC []
 >> POP_ORW
 >> Know `!n x. x IN m_space p ==> (X n x <> Y n x <=> (\x. X n x - Y n x) x <> 0)`
 >- (RW_TAC std_ss [] \\
     reverse EQ_TAC >- (DISCH_TAC >> MATCH_MP_TAC sub_0 >> art []) \\
     fs [real_random_variable_def, p_space_def] \\
     DISCH_TAC >> MATCH_MP_TAC sub_eq_0 >> rw [])
 >> DISCH_TAC
 >> Know ‘{x | X n x <> Y n x} INTER m_space p =
          {x | (\x. X n x - Y n x) x <> 0} INTER m_space p’
 >- (rw [Once EXTENSION] \\
     EQ_TAC >> rw [] >> METIS_TAC [])
 >> Rewr'
 >> POP_ASSUM K_TAC
 >> Suff `(\x. X n x - Y n x) IN measurable (m_space p,measurable_sets p) Borel`
 >- (METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE])
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB
 >> qexistsl_tac [`X n`, `Y n`]
 >> FULL_SIMP_TAC std_ss [measure_space_def, space_def, real_random_variable_def,
                          random_variable_def, p_space_def, events_def]
QED

Theorem equivalent_lemma :
    !p X Y. prob_space p /\ equivalent p X Y /\
            (!n. real_random_variable (X n) p) /\
            (!n. real_random_variable (Y n) p) ==>
       ?N f. N IN null_set p /\
            !x. x IN p_space p DIFF N ==> !n. f x <= n ==> (X n x - Y n x = 0)
Proof
    RW_TAC std_ss [equivalent_def]
 >> Q.ABBREV_TAC `E = \n. {x | x IN p_space p /\ X n x <> Y n x}`
 >> `!n. (E n) IN events p` by METIS_TAC [equivalent_events]
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
 >> FULL_SIMP_TAC set_ss [real_random_variable_def, p_space_def]
 >> MATCH_MP_TAC sub_eq_0 >> rw []
QED

(* Theorem 5.2.1 (1) [2, p.113] (not used anywhere) *)
Theorem equivalent_thm1 :
    !p X Y. prob_space p /\ equivalent p X Y /\
           (!n. real_random_variable (X n) p) /\
           (!n. real_random_variable (Y n) p) ==>
        ?Z. real_random_variable Z p /\
           ((\n x. SIGMA (\i. X i x - Y i x) (count (SUC n))) --> Z) (almost_everywhere p)
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘Z = \n x. SIGMA (\i. X i x - Y i x) (count (SUC n))’
 >> Know `?N f. N IN null_set p /\
               !x. x IN p_space p DIFF N ==> !n. f x <= n ==> (X n x - Y n x = 0)`
 >- (MATCH_MP_TAC equivalent_lemma >> art [])
 >> STRIP_TAC
 >> Q.EXISTS_TAC `\x. SIGMA (\i. X i x - Y i x) (count (f x)) *
                      indicator_fn (p_space p DIFF N) x`
 >> CONJ_TAC
 >- (REWRITE_TAC [real_random_variable_def] \\
     reverse CONJ_TAC
     >- (GEN_TAC >> BETA_TAC >> DISCH_TAC \\
         reverse (Cases_on `x IN p_space p DIFF N`)
         >- (ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rzero] \\
             REWRITE_TAC [extreal_of_num_def, extreal_not_infty]) \\
         ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rone] \\
         FULL_SIMP_TAC std_ss [Abbr ‘Z’, real_random_variable_def] \\
         CONJ_TAC >| (* 2 subgoals, similar tactics *)
         [ (* goal 1 (of 2) *)
           MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF >> art [FINITE_COUNT] \\
           Q.X_GEN_TAC `n` >> RW_TAC std_ss [] \\
           METIS_TAC [sub_not_infty],
           (* goal 2 (of 2) *)
           MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> art [FINITE_COUNT] \\
           Q.X_GEN_TAC `n` >> RW_TAC std_ss [] \\
           METIS_TAC [sub_not_infty] ]) \\
     FULL_SIMP_TAC std_ss [prob_space_def, random_variable_def, p_space_def,
                           events_def, real_random_variable_def, Abbr ‘Z’] \\
     (* Here is the missing part in textbook proof, that we need to prove

        (\x. SIGMA (\n. X n x - Y n x) (count (f x)) * indicator_fn s x)

        is Borel-measurable (i.e. a random variable). To remove (f x), we
        find a way to rewrite `SIGMA` by the subtraction of two `suminf`s,
        each of which is Borel-measurable, using "ext_suminf_sum".
      *)
     Know `!x. x IN m_space p ==>
               SIGMA (\i. X i x - Y i x) (count (f x)) *
                 indicator_fn (m_space p DIFF N) x =
               SIGMA (\n. indicator_fn (m_space p DIFF N) x *
                          (\i. X i x - Y i x) n) (count (f x))`
     >- (GEN_TAC >> DISCH_TAC >> MATCH_MP_TAC EQ_SYM \\
         STRIP_ASSUME_TAC
           (Q.SPECL [`m_space p DIFF N`, `x`] indicator_fn_normal) >> art [] \\
         GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [mul_comm] \\
         irule EXTREAL_SUM_IMAGE_CMUL >> art [FINITE_COUNT] \\
         METIS_TAC [sub_not_infty]) >> DISCH_TAC \\
     Know ‘(\x. SIGMA (\i. X i x - Y i x) (count (f x)) *
                indicator_fn (m_space p DIFF N) x) IN
             Borel_measurable (m_space p,measurable_sets p) <=>
           (\x. SIGMA (\i. indicator_fn (m_space p DIFF N) x *
                           (\i. X i x - Y i x) i) (count (f x))) IN
             Borel_measurable (m_space p,measurable_sets p)’
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONG >> RW_TAC std_ss []) >> Rewr' \\
     BETA_TAC >> POP_ASSUM K_TAC \\
     Q.ABBREV_TAC `g = \x i. indicator_fn (m_space p DIFF N) x * (X i x - Y i x)` \\
     Know `!x i. (\i. indicator_fn (m_space p DIFF N) x * (X i x - Y i x)) i =
                 fn_plus (g x) i - fn_minus (g x) i`
     >- (rpt GEN_TAC \\
        `(\i. indicator_fn (m_space p DIFF N) x * (X i x - Y i x)) = g x` by METIS_TAC [] \\
         POP_ORW >> REWRITE_TAC [GSYM FN_DECOMP]) >> BETA_TAC >> Rewr' \\
     Know `!x. x IN m_space p ==>
               SIGMA (\i. fn_plus (g x) i - fn_minus (g x) i) (count (f x)) =
               SIGMA (fn_plus  (g x)) (count (f x)) -
               SIGMA (fn_minus (g x)) (count (f x))`
     >- (GEN_TAC >> DISCH_TAC \\
         irule EXTREAL_SUM_IMAGE_SUB >> art [FINITE_COUNT] \\
         DISJ2_TAC >> Q.X_GEN_TAC `n` >> DISCH_TAC \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC pos_not_neginf >> REWRITE_TAC [FN_MINUS_POS]) \\
         MATCH_MP_TAC FN_PLUS_NOT_INFTY \\
         Q.X_GEN_TAC `i` >> Q.UNABBREV_TAC `g` >> BETA_TAC \\
         STRIP_ASSUME_TAC
           (Q.SPECL [`m_space p DIFF N`, `x`] indicator_fn_normal) >> art [] \\
         Suff `X i x - Y i x <> PosInf` >- METIS_TAC [mul_not_infty] \\
         METIS_TAC [sub_not_infty]) >> DISCH_TAC \\
     Know ‘(\x. SIGMA (\i. fn_plus (g x) i - fn_minus (g x) i) (count (f x))) IN
             Borel_measurable (m_space p,measurable_sets p) <=>
           (\x. SIGMA (fn_plus  (g x)) (count (f x)) -
                SIGMA (fn_minus (g x)) (count (f x))) IN
             Borel_measurable (m_space p,measurable_sets p)’
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONG >> RW_TAC std_ss []) >> Rewr' \\
     POP_ASSUM K_TAC \\
     Know `!x. x IN m_space p ==> SIGMA (fn_plus (g x)) (count (f x)) = suminf (fn_plus (g x))`
     >- (GEN_TAC >> DISCH_TAC >> MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC ext_suminf_sum \\
         RW_TAC std_ss [FN_PLUS_POS, Abbr `g`] \\
         reverse (Cases_on `x IN m_space p DIFF N`)
         >- (ASM_SIMP_TAC std_ss [indicator_fn_def, mul_lzero, FN_PLUS_ZERO]) \\
         ASM_SIMP_TAC std_ss [indicator_fn_def, mul_lone, FN_PLUS_ALT,
                              max_refl]) >> DISCH_TAC \\
     Know `!x. x IN m_space p ==> SIGMA (fn_minus (g x)) (count (f x)) = suminf (fn_minus (g x))`
     >- (GEN_TAC >> DISCH_TAC >> MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC ext_suminf_sum \\
         RW_TAC std_ss [FN_MINUS_POS, Abbr `g`] \\
         reverse (Cases_on `x IN m_space p DIFF N`)
         >- (ASM_SIMP_TAC std_ss [indicator_fn_def, mul_lzero, FN_MINUS_ZERO]) \\
         ASM_SIMP_TAC std_ss [indicator_fn_def, mul_lone, FN_MINUS_ALT,
                              min_refl, neg_0]) >> DISCH_TAC \\
    `sigma_algebra (m_space p,measurable_sets p)` by METIS_TAC [measure_space_def] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB' \\
     qexistsl_tac [`\x. suminf (fn_plus (g x))`, `\x. suminf (fn_minus (g x))`] \\
     ASM_SIMP_TAC std_ss [space_def] \\
     CONJ_TAC >| (* 2 subgoals, similar tactics *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC IN_MEASURABLE_BOREL_SUMINF >> BETA_TAC \\
       Q.EXISTS_TAC `\n x. fn_plus (g x) n` >> BETA_TAC \\
      `!x. (\n. (fn_plus (g x)) n) = fn_plus (g x)` by METIS_TAC [] >> POP_ORW \\
       ASM_SIMP_TAC std_ss [space_def, FN_PLUS_POS] \\
       RW_TAC std_ss [Abbr `g`, FN_PLUS_ALT] \\
       HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX >> art [] \\
       reverse CONJ_TAC
       >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST' >> art []) \\
       ONCE_REWRITE_TAC [mul_comm] \\
       HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR >> art [subsets_def] \\
       reverse CONJ_TAC
       >- (MATCH_MP_TAC MEASURE_SPACE_COMPL >> fs [IN_NULL_SET, null_set_def]) \\
       MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
       qexistsl_tac [`X n`, `Y n`] >> ASM_SIMP_TAC std_ss [space_def],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC IN_MEASURABLE_BOREL_SUMINF >> BETA_TAC \\
       Q.EXISTS_TAC `\n x. fn_minus (g x) n` >> BETA_TAC \\
      `!x. (\n. (fn_minus (g x)) n) = fn_minus (g x)` by METIS_TAC [] >> POP_ORW \\
       ASM_SIMP_TAC std_ss [space_def, FN_MINUS_POS] \\
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
       qexistsl_tac [`X n`, `Y n`] >> ASM_SIMP_TAC std_ss [space_def] ])
 >> RW_TAC std_ss [Abbr ‘Z’, converge_AE_def, AE_THM, GSYM IN_NULL_SET, almost_everywhere_def]
 >> Q.EXISTS_TAC `N`
 >> RW_TAC std_ss [LIM_SEQUENTIALLY, dist, indicator_fn_def, mul_rone, GSYM p_space_def]
 >> Q.EXISTS_TAC `f x`
 >> RW_TAC std_ss []
 >> Know `SIGMA (\i. X i x - Y i x) (count (SUC n)) =
          SIGMA (\i. X i x - Y i x) ((count (SUC n)) DIFF (from (f x)))`
 >- (irule EXTREAL_SUM_IMAGE_ZERO_DIFF \\
     fs [real_random_variable_def, IN_FROM] \\
     DISJ2_TAC >> RW_TAC std_ss [sub_not_infty]) >> Rewr'
 >> Suff `count (SUC n) DIFF (from (f x)) = count (f x)`
 >- (Rewr' >> rw [])
 >> RW_TAC set_ss [Once EXTENSION, IN_FROM, IN_COUNT]
 >> rw []
QED

(* Theorem 5.2.1 (2) [2, p.113] *)
Theorem equivalent_thm2 :
    !a p X Y. prob_space p /\ equivalent p X Y /\
             (!n. real_random_variable (X n) p) /\
             (!n. real_random_variable (Y n) p) /\
              mono_increasing a /\ (sup (IMAGE a UNIV) = PosInf) ==>
       ((\n x. SIGMA (\i. X i x - Y i x) (count (SUC n)) / (a n)) --> (\x. 0))
          (almost_everywhere p)
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
 >> Know ‘x IN p_space p’
 >- (‘p_space p DIFF N SUBSET p_space p’ by SET_TAC [] \\
     METIS_TAC [SUBSET_DEF])
 >> DISCH_TAC
 >> Know `!n. SIGMA (\i. X i x - Y i x) (count n) <> PosInf`
 >- (GEN_TAC >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
     rw [sub_not_infty]) >> DISCH_TAC
 >> Know `!n. SIGMA (\i. X i x - Y i x) (count n) <> NegInf`
 >- (GEN_TAC >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
     rw [sub_not_infty]) >> DISCH_TAC
 (* 1. if (a n) ever reached PosInf, use that n directly *)
 >> reverse (Cases_on `!n. a n <> PosInf`)
 >- (FULL_SIMP_TAC std_ss [] >> Q.EXISTS_TAC `n` \\
     Q.X_GEN_TAC `m` >> DISCH_TAC \\
     Know `a n <= a m` >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     ASM_REWRITE_TAC [le_infty] >> Rewr' \\
    `?r. SIGMA (\i. X i x - Y i x) (count (SUC m)) = Normal r`
         by METIS_TAC [extreal_cases] \\
     rw [extreal_div_def, real_normal, extreal_of_num_def])
 (* eliminate `real 0` first *)
 >> `real 0 = 0` by METIS_TAC [extreal_of_num_def, real_normal]
 >> POP_ASSUM (fn th => FULL_SIMP_TAC bool_ss [REAL_SUB_RZERO, th])
 >> Q.PAT_X_ASSUM `!x. x IN p_space p DIFF N ==> P` (MP_TAC o (Q.SPEC `x`))
 >> RW_TAC std_ss []
 (* now estimating N *)
 >> Know `?k. abs (SIGMA (\i. X i x - Y i x) (count (f x))) / Normal e < a k`
 >- (CCONTR_TAC >> FULL_SIMP_TAC std_ss [] \\
     Know `sup (IMAGE a UNIV) <=
           abs (SIGMA (\i. X i x - Y i x) (count (f x))) / Normal e`
     >- (RW_TAC set_ss [sup_le'] >> fs [extreal_lt_def]) >> art [] \\
    `?r. SIGMA (\i. X i x - Y i x) (count (f x)) = Normal r`
         by METIS_TAC [extreal_cases] >> art [] \\
     ASM_SIMP_TAC std_ss [extreal_abs_def, extreal_div_eq, extreal_le_def])
 >> STRIP_TAC
 >> Q.EXISTS_TAC `MAX k (f x)`
 >> RW_TAC std_ss [MAX_LE]
 >> Know `0 <= abs (SIGMA (\i. X i x - Y i x) (count (f x))) / Normal e`
 >- (MATCH_MP_TAC le_div >> art [abs_pos]) >> DISCH_TAC
 >> `0 < a k` by PROVE_TAC [let_trans]
 >> `0 < a n` by PROVE_TAC [lte_trans]
 >> Know `SIGMA (\i. X i x - Y i x) (count (SUC n)) =
          SIGMA (\i. X i x - Y i x) ((count (SUC n)) DIFF (from (f x)))`
 >- (irule EXTREAL_SUM_IMAGE_ZERO_DIFF >> fs [IN_FROM] \\
     DISJ2_TAC >> RW_TAC std_ss [sub_not_infty]) >> Rewr'
 >> Know `count (SUC n) DIFF (from (f x)) = count (f x)`
 >- (RW_TAC set_ss [Once EXTENSION, IN_FROM, IN_COUNT] \\
     rw []) >> Rewr'
 >> Know `abs (real (SIGMA (\i. X i x - Y i x) (count (f x)) / a n)) < e <=>
          abs (SIGMA (\i. X i x - Y i x) (count (f x)) / a n) < Normal e`
 >- (`?r. SIGMA (\i. X i x - Y i x) (count (f x)) = Normal r`
         by METIS_TAC [extreal_cases] >> POP_ORW \\
     `a n <> NegInf` by PROVE_TAC [pos_not_neginf, lt_imp_le] \\
     `?b. a n = Normal b` by METIS_TAC [extreal_cases] >> art [] \\
     `a n <> 0` by PROVE_TAC [lt_imp_ne] \\
     `b <> 0` by METIS_TAC [extreal_of_num_def, extreal_11] \\
     ASM_SIMP_TAC real_ss [extreal_abs_def, real_normal, extreal_div_eq,
                           extreal_lt_eq, ABS_DIV]) >> Rewr'
 >> Know `abs (SIGMA (\i. X i x - Y i x) (count (f x)) / a n) =
          abs (SIGMA (\i. X i x - Y i x) (count (f x))) / abs (a n)`
 >- (MATCH_MP_TAC abs_div >> art [] \\
     PROVE_TAC [lt_imp_ne]) >> Rewr'
 >> Know `abs (a n) = a n`
 >- (REWRITE_TAC [abs_refl] \\
     MATCH_MP_TAC lt_imp_le >> art []) >> Rewr'
 >> `a n <> NegInf` by PROVE_TAC [pos_not_neginf, lt_imp_le]
 >> `?b. a n = Normal b` by METIS_TAC [extreal_cases] >> art []
 >> Know `abs (SIGMA (\i. X i x - Y i x) (count (f x))) / Normal b < Normal e <=>
          abs (SIGMA (\i. X i x - Y i x) (count (f x))) / Normal e < Normal b`
 >- (MATCH_MP_TAC EQ_TRANS \\
     Q.EXISTS_TAC `abs (SIGMA (\i. X i x - Y i x) (count (f x))) < Normal e * Normal b` \\
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

(* Corollary of Theorem 5.2.1 [2, p.113] *)
Theorem equivalent_thm3 :
    !a p X Y Z. prob_space p /\ equivalent p X Y /\
               (!n. real_random_variable (X n) p) /\
               (!n. real_random_variable (Y n) p) /\
                real_random_variable Z p /\
               (!n. 0 < a n /\ a n < PosInf) /\
                mono_increasing a /\ sup (IMAGE a UNIV) = PosInf /\
       ((\n x. SIGMA (\i. X i x) (count (SUC n)) / (a n)) --> Z) (in_probability p) ==>
       ((\n x. SIGMA (\i. Y i x) (count (SUC n)) / (a n)) --> Z) (in_probability p)
Proof
    rpt STRIP_TAC
 >> Know `!XY m x. (!n. real_random_variable (XY n) p) /\ x IN p_space p ==>
                  SIGMA (\i. XY i x) (count m) <> PosInf /\
                  SIGMA (\i. XY i x) (count m) <> NegInf`
 >- (rpt GEN_TAC >> STRIP_TAC \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
       rw [FINITE_COUNT, IN_COUNT] \\
       FULL_SIMP_TAC std_ss [real_random_variable_def],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
       rw [FINITE_COUNT, IN_COUNT] \\
       FULL_SIMP_TAC std_ss [real_random_variable_def] ])
 >> DISCH_TAC
 >> Know ‘!XY k. (!n. real_random_variable (XY n) p) ==>
                real_random_variable (\x. SIGMA (\i. XY i x) (count (SUC k)) / a k) p’
 >- (rpt GEN_TAC >> DISCH_TAC \\
     Know ‘real_random_variable (\x. SIGMA (\i. XY i x) (count (SUC k)) / a k) p <=>
           real_random_variable (\x. inv (a k) * SIGMA (\i. XY i x) (count (SUC k))) p’
     >- (MATCH_MP_TAC real_random_variable_cong >> RW_TAC std_ss [] \\
         MATCH_MP_TAC div_eq_mul_linv >> rw []) >> Rewr' \\
    ‘a k <> NegInf’ by PROVE_TAC [pos_not_neginf, lt_imp_le] \\
    ‘?r. a k = Normal r’ by METIS_TAC [extreal_cases, lt_infty] \\
    ‘0 < r’ by METIS_TAC [extreal_of_num_def, extreal_lt_eq] \\
    ‘r <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] \\
    ‘inv (a k) = Normal (inv r)’ by METIS_TAC [extreal_inv_def] >> POP_ORW \\
     rw [real_random_variable] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> BETA_TAC \\
       qexistsl_tac [‘\x. SIGMA (\i. XY i x) (count (SUC k))’, ‘inv r’] \\
       FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, events_def] \\
       CONJ_TAC >- FULL_SIMP_TAC std_ss [measure_space_def] \\
       MATCH_MP_TAC (INST_TYPE [“:'b” |-> “:num”] IN_MEASURABLE_BOREL_SUM) >> rw [] \\
       qexistsl_tac [‘XY’, ‘count (SUC k)’] >> rw [FINITE_COUNT, IN_COUNT] >|
       [ FULL_SIMP_TAC std_ss [measure_space_def],
         FULL_SIMP_TAC std_ss [real_random_variable, p_space_def, events_def],
         FULL_SIMP_TAC std_ss [real_random_variable, p_space_def, events_def] ],
       (* goal 2 (of 3) *)
      ‘?z. SIGMA (\i. XY i x) (count (SUC k)) = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
       rw [extreal_mul_def, extreal_not_infty],
       (* goal 3 (of 3) *)
      ‘?z. SIGMA (\i. XY i x) (count (SUC k)) = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
       rw [extreal_mul_def, extreal_not_infty] ])
 >> DISCH_TAC
 >> Know ‘!n x. x IN p_space p ==> SIGMA (\i. X i x - Y i x) (count (SUC n)) <> PosInf’
 >- (rpt GEN_TAC >> DISCH_TAC \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> art [FINITE_COUNT] \\
     Q.X_GEN_TAC ‘i’ >> rw [] \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
     METIS_TAC [sub_not_infty])
 >> DISCH_TAC
 >> Know ‘!n x. x IN p_space p ==> SIGMA (\i. X i x - Y i x) (count (SUC n)) <> NegInf’
 >- (rpt GEN_TAC >> DISCH_TAC \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF >> art [FINITE_COUNT] \\
     Q.X_GEN_TAC ‘i’ >> rw [] \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
     METIS_TAC [sub_not_infty])
 >> DISCH_TAC
 (* applying equivalent_thm2 *)
 >> Q.ABBREV_TAC ‘A = \n x. SIGMA (\i. X i x) (count (SUC n)) / a n’
 >> Q.ABBREV_TAC ‘B = \n x. SIGMA (\i. X i x - Y i x) (count (SUC n)) / a n’
 >> ‘!n. real_random_variable (A n) p’ by rw [Abbr ‘A’]
 >> Know ‘!n. real_random_variable (B n) p’
 >- (RW_TAC std_ss [Abbr ‘B’] \\
     Know ‘real_random_variable (\x. SIGMA (\i. X i x - Y i x) (count (SUC n)) / a n) p <=>
           real_random_variable (\x. inv (a n) * SIGMA (\i. X i x - Y i x) (count (SUC n))) p’
     >- (MATCH_MP_TAC real_random_variable_cong >> RW_TAC std_ss [] \\
         MATCH_MP_TAC div_eq_mul_linv >> rw []) >> Rewr' \\
    ‘a n <> NegInf’ by PROVE_TAC [pos_not_neginf, lt_imp_le] \\
    ‘?r. a n = Normal r’ by METIS_TAC [extreal_cases, lt_infty] \\
    ‘0 < r’ by METIS_TAC [extreal_of_num_def, extreal_lt_eq] \\
    ‘r <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] \\
    ‘inv (a n) = Normal (inv r)’ by METIS_TAC [extreal_inv_def] >> POP_ORW \\
     rw [real_random_variable] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> BETA_TAC \\
       qexistsl_tac [‘\x. SIGMA (\i. X i x - Y i x) (count (SUC n))’, ‘inv r’] \\
       FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, events_def] \\
       STRONG_CONJ_TAC >- FULL_SIMP_TAC std_ss [measure_space_def] \\
       DISCH_TAC \\
       MATCH_MP_TAC (INST_TYPE [“:'b” |-> “:num”] IN_MEASURABLE_BOREL_SUM) >> rw [] \\
       qexistsl_tac [‘\i x. X i x - Y i x’, ‘count (SUC n)’] \\
       rw [FINITE_COUNT, IN_COUNT] >| (* 2 subgoals *)
       [ (* goal 1.1 (of 2) *)
         MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
         qexistsl_tac [‘X i’, ‘Y i’] \\
         FULL_SIMP_TAC std_ss [real_random_variable, p_space_def, events_def, space_def],
         (* goal 1.2 (of 2) *)
         FULL_SIMP_TAC std_ss [real_random_variable, p_space_def, events_def] \\
         METIS_TAC [sub_not_infty] ],
       (* goal 2 (of 3) *)
      ‘?z. SIGMA (\i. X i x - Y i x) (count (SUC n)) = Normal z’
         by METIS_TAC [extreal_cases] >> POP_ORW \\
       rw [extreal_mul_def, extreal_not_infty],
       (* goal 3 (of 3) *)
      ‘?z. SIGMA (\i. X i x - Y i x) (count (SUC n)) = Normal z’
         by METIS_TAC [extreal_cases] >> POP_ORW \\
       rw [extreal_mul_def, extreal_not_infty] ])
 >> DISCH_TAC
 >> Know ‘(B --> (\x. 0)) (in_probability p)’
 >- (MATCH_MP_TAC converge_AE_imp_PR' >> art [] \\
     Q.UNABBREV_TAC ‘B’ >> MATCH_MP_TAC equivalent_thm2 >> art [])
 >> DISCH_TAC
 (* applying converge_PR_sub *)
 >> Suff ‘((\n x. SIGMA (\i. Y i x) (count (SUC n)) / a n) --> Z) (in_probability p) <=>
          ((\n x. A n x - B n x) --> (\x. Z x - (\x. 0) x)) (in_probability p)’
 >- (Rewr' \\
     MATCH_MP_TAC converge_PR_sub >> rw [real_random_variable_zero])
 (* applying converge_PR_cong_full *)
 >> MATCH_MP_TAC converge_PR_cong_full
 >> Q.EXISTS_TAC ‘0’
 >> RW_TAC arith_ss [sub_rzero]
 >> FULL_SIMP_TAC std_ss [Abbr ‘A’, Abbr ‘B’]
 >> Suff ‘SIGMA (\i. Y i x) (count (SUC n)) =
          SIGMA (\i. X i x) (count (SUC n)) -
          SIGMA (\i. X i x - Y i x) (count (SUC n))’
 >- (Rewr' >> ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC div_sub >> rw [] \\
     METIS_TAC [lt_imp_ne])
 (* applying EXTREAL_SUM_IMAGE_SUB *)
 >> Know ‘(\i. Y i x) = (\i. (\i. X i x) i - (\i. X i x - Y i x) i)’
 >- (rw [FUN_EQ_THM] \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
    ‘?c. X i x = Normal c’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?d. Y i x = Normal d’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def] >> REAL_ARITH_TAC)
 >> Rewr'
 >> irule (INST_TYPE [“:'a” |-> “:num”] EXTREAL_SUM_IMAGE_SUB)
 >> FULL_SIMP_TAC std_ss [real_random_variable_def]
 >> rw [FINITE_COUNT, IN_COUNT]
 >> DISJ1_TAC (* or DISJ2_TAC *)
 >> Q.X_GEN_TAC ‘i’ >> STRIP_TAC
 >> ‘?c. X i x = Normal c’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> ‘?d. Y i x = Normal d’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> rw [extreal_sub_def]
QED

(* Let ‘a = (\n. &SUC n)’ in equivalent_thm3 *)
Theorem equivalent_thm4 :
    !p X Y Z. prob_space p /\ equivalent p X Y /\
             (!n. real_random_variable (X n) p) /\
             (!n. real_random_variable (Y n) p) /\
              real_random_variable Z p /\
       ((\n x. SIGMA (\i. X i x) (count (SUC n)) / &SUC n) --> Z) (in_probability p) ==>
       ((\n x. SIGMA (\i. Y i x) (count (SUC n)) / &SUC n) --> Z) (in_probability p)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC (BETA_RULE (Q.SPEC ‘\n. &SUC n’ equivalent_thm3))
 >> Q.EXISTS_TAC ‘X’ >> rw []
 >| [ (* goal 1 (of 3) *)
      rw [extreal_of_num_def, extreal_lt_eq],
      (* goal 2 (of 3) *)
      rw [ext_mono_increasing_def, extreal_of_num_def, extreal_le_eq],
      (* goal 3 (of 3) *)
      rw [sup_eq', le_infty] \\
      SPOSE_NOT_THEN (STRIP_ASSUME_TAC o (MATCH_MP SIMP_EXTREAL_ARCH)) \\
     ‘n < SUC n’ by rw [] \\
     ‘(&n) :extreal < &SUC n’ by rw [extreal_of_num_def, extreal_lt_eq] \\
     ‘y < &SUC n’ by PROVE_TAC [let_trans] \\
      Q.PAT_X_ASSUM ‘!z. _ ==> z <= y’ (MP_TAC o (Q.SPEC ‘&SUC n’)) \\
      rw [GSYM extreal_lt_def] \\
      Q.EXISTS_TAC ‘n’ >> REWRITE_TAC [] ]
QED

(* This lemma will eliminate ‘LLN’ in WLLN_IID *)
Theorem LLN_alt_converge_PR_IID :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) /\
          identical_distribution p X Borel UNIV /\ integrable p (X 0) ==>
         (LLN p X in_probability <=>
          ((\n x. SIGMA (\i. X i x) (count (SUC n)) / &SUC n) --> (\x. expectation p (X 0)))
           (in_probability p))
Proof
    RW_TAC std_ss [LLN_def, converge_PR_def, sub_rzero]
 >> Suff ‘!e n. {x | x IN p_space p /\
                     e < abs ((Z (SUC n) x - expectation p (Z (SUC n))) / &SUC n)} =
                {x | x IN p_space p /\
                     e < abs (Z (SUC n) x / &SUC n - expectation p (X 0))}’ >- Rewr
 >> rpt GEN_TAC
 >> Suff ‘!x. x IN p_space p ==>
              (Z (SUC n) x - expectation p (Z (SUC n))) / &SUC n =
              Z (SUC n) x / &SUC n - expectation p (X 0)’
 >- (rw [Once EXTENSION] >> METIS_TAC [])
 >> rpt STRIP_TAC
 >> Know ‘!n. expectation p (Z n) = SIGMA (\i. expectation p (X i)) (count n)’
 >- (rw [expectation_def, Abbr ‘Z’] \\
     MATCH_MP_TAC integral_sum \\
     fs [FINITE_COUNT, prob_space_def, real_random_variable_def, p_space_def] \\
     rpt STRIP_TAC \\
     MATCH_MP_TAC identical_distribution_integrable >> rw [prob_space_def])
 >> Q.ABBREV_TAC ‘m = expectation p (X 0)’
 >> Know ‘!n. expectation p (X n) = m’
 >- (GEN_TAC >> Q.UNABBREV_TAC ‘m’ \\
     MATCH_MP_TAC identical_distribution_expectation \\
     FULL_SIMP_TAC std_ss [real_random_variable_def])
 >> RW_TAC std_ss []
 >> Know ‘SIGMA (\i. m) (count (SUC n)) = &CARD (count (SUC n)) * (\i. m) (0 :num)’
 >- (irule (INST_TYPE [“:'a” |-> “:num”] EXTREAL_SUM_IMAGE_FINITE_SAME) \\
     rw [IN_COUNT, FINITE_COUNT]) >> Rewr'
 >> rw [CARD_COUNT]
 >> Know `!n x. x IN p_space p ==> Z n x <> PosInf`
 >- (RW_TAC std_ss [Abbr ‘Z’] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
     FULL_SIMP_TAC std_ss [real_random_variable_def, FINITE_COUNT, IN_COUNT])
 >> DISCH_TAC
 >> Know `!n x. x IN p_space p ==> Z n x <> NegInf`
 >- (RW_TAC std_ss [Abbr ‘Z’] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
     FULL_SIMP_TAC std_ss [real_random_variable_def, FINITE_COUNT, IN_COUNT])
 >> DISCH_TAC
 >> Know `m <> PosInf /\ m <> NegInf`
 >- (ASM_SIMP_TAC std_ss [expectation_def, Abbr ‘m’] \\
     MATCH_MP_TAC integrable_finite_integral \\
     FULL_SIMP_TAC std_ss [prob_space_def])
 >> STRIP_TAC
 >> Know `(Z (SUC n) x - &SUC n * m) / &SUC n =
          inv (&SUC n) * (Z (SUC n) x - &SUC n * m)`
 >- (MATCH_MP_TAC div_eq_mul_linv \\
    `?a. Z (SUC n) x = Normal a` by METIS_TAC [extreal_cases] >> POP_ORW \\
    `?b. m = Normal b` by METIS_TAC [extreal_cases] >> POP_ORW \\
     RW_TAC real_ss [extreal_lt_eq, extreal_of_num_def, extreal_sub_def,
                     extreal_mul_def, extreal_not_infty])
 >> Rewr'
 >> Know ‘Z (SUC n) x / &SUC n = inv (&SUC n) * Z (SUC n) x’
 >- (MATCH_MP_TAC div_eq_mul_linv \\
    `?a. Z (SUC n) x = Normal a` by METIS_TAC [extreal_cases] >> POP_ORW \\
     RW_TAC real_ss [extreal_lt_eq, extreal_of_num_def, extreal_not_infty])
 >> Rewr'
 >> Know ‘inv (&SUC n) * (Z (SUC n) x - &SUC n * m) =
          inv (&SUC n) * Z (SUC n) x - inv (&SUC n) * (&SUC n * m)’
 >- (MATCH_MP_TAC sub_ldistrib \\
    ‘?r. m = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘&SUC n <> (0 :real)’ by rw [] \\
     RW_TAC real_ss [extreal_inv_def, extreal_of_num_def, extreal_not_infty, extreal_mul_def])
 >> Rewr'
 >> Suff ‘inv (&SUC n) * (&SUC n * m) = m’ >- Rewr
 >> REWRITE_TAC [mul_assoc]
 >> Suff ‘inv (&SUC n) * &SUC n = 1’ >- (Rewr' >> REWRITE_TAC [mul_lone])
 >> MATCH_MP_TAC mul_linv_pos
 >> rw [extreal_of_num_def, extreal_not_infty, extreal_lt_eq]
QED

Theorem LLN_alt_converge_PR_IID_shift :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) /\
          identical_distribution p X Borel UNIV /\ integrable p (X 0) ==>
         (LLN p X in_probability <=>
          ((\n x. SIGMA (\i. X i x) (count n) / &n) --> (\x. expectation p (X 0)))
           (in_probability p))
Proof
    RW_TAC std_ss [LLN_alt_converge_PR_IID]
 >> rw [REWRITE_RULE [Once EQ_SYM_EQ, GSYM ADD1]
                     (Q.SPEC ‘1’ converge_PR_alt_shift)]
QED

Theorem LLN_alt_converge_AE_IID :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) /\
          identical_distribution p X Borel UNIV /\ integrable p (X 0) ==>
         (LLN p X almost_everywhere <=>
          ((\n x. SIGMA (\i. X i x) (count (SUC n)) / &SUC n) --> (\x. expectation p (X 0)))
           (almost_everywhere p))
Proof
    RW_TAC real_ss [LLN_def, converge_AE_def, AE_DEF, LIM_SEQUENTIALLY, dist, real_0]
 >> Suff ‘!n x. x IN m_space p ==>
                real ((Z (SUC n) x - expectation p (Z (SUC n))) / &SUC n) =
                real (Z (SUC n) x / &SUC n) - real (expectation p (X 0))’
 >- (DISCH_TAC >> EQ_TAC >> rw [])
 >> rpt STRIP_TAC
 >> Know ‘!n. expectation p (Z n) = SIGMA (\i. expectation p (X i)) (count n)’
 >- (rw [expectation_def, Abbr ‘Z’] \\
     MATCH_MP_TAC integral_sum \\
     fs [FINITE_COUNT, prob_space_def, real_random_variable_def, p_space_def] \\
     rpt STRIP_TAC \\
     MATCH_MP_TAC identical_distribution_integrable >> rw [prob_space_def])
 >> Rewr'
 >> Q.ABBREV_TAC ‘m = expectation p (X 0)’
 >> Know ‘!n. expectation p (X n) = m’
 >- (GEN_TAC >> Q.UNABBREV_TAC ‘m’ \\
     MATCH_MP_TAC identical_distribution_expectation \\
     FULL_SIMP_TAC std_ss [real_random_variable_def])
 >> Rewr'
 >> Know ‘SIGMA (\i. m) (count (SUC n)) = &CARD (count (SUC n)) * (\i. m) (0 :num)’
 >- (irule (INST_TYPE [“:'a” |-> “:num”] EXTREAL_SUM_IMAGE_FINITE_SAME) \\
     rw [IN_COUNT, FINITE_COUNT]) >> Rewr'
 >> REWRITE_TAC [CARD_COUNT]
 >> Know `!n x. x IN m_space p ==> Z n x <> PosInf`
 >- (RW_TAC std_ss [Abbr ‘Z’] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
     FULL_SIMP_TAC std_ss [real_random_variable_def, p_space_def, FINITE_COUNT, IN_COUNT])
 >> DISCH_TAC
 >> Know `!n x. x IN m_space p ==> Z n x <> NegInf`
 >- (RW_TAC std_ss [Abbr ‘Z’] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
     FULL_SIMP_TAC std_ss [real_random_variable_def, p_space_def, FINITE_COUNT, IN_COUNT])
 >> DISCH_TAC
 >> Know `m <> PosInf /\ m <> NegInf`
 >- (ASM_SIMP_TAC std_ss [expectation_def, Abbr ‘m’] \\
     MATCH_MP_TAC integrable_finite_integral \\
     FULL_SIMP_TAC std_ss [prob_space_def])
 >> STRIP_TAC
 >> Know `(Z (SUC n) x - &SUC n * m) / &SUC n =
          inv (&SUC n) * (Z (SUC n) x - &SUC n * m)`
 >- (MATCH_MP_TAC div_eq_mul_linv \\
    `?a. Z (SUC n) x = Normal a` by METIS_TAC [extreal_cases] >> POP_ORW \\
    `?b. m = Normal b` by METIS_TAC [extreal_cases] >> POP_ORW \\
     RW_TAC real_ss [extreal_lt_eq, extreal_of_num_def, extreal_sub_def,
                     extreal_mul_def, extreal_not_infty])
 >> Rewr'
 >> Know ‘Z (SUC n) x / &SUC n = inv (&SUC n) * Z (SUC n) x’
 >- (MATCH_MP_TAC div_eq_mul_linv \\
    `?a. Z (SUC n) x = Normal a` by METIS_TAC [extreal_cases] >> POP_ORW \\
     RW_TAC real_ss [extreal_lt_eq, extreal_of_num_def, extreal_not_infty])
 >> Rewr'
 >> Know ‘inv (&SUC n) * (Z (SUC n) x - &SUC n * m) =
          inv (&SUC n) * Z (SUC n) x - inv (&SUC n) * (&SUC n * m)’
 >- (MATCH_MP_TAC sub_ldistrib \\
    ‘?r. m = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘&SUC n <> (0 :real)’ by rw [] \\
     RW_TAC real_ss [extreal_inv_def, extreal_of_num_def, extreal_not_infty, extreal_mul_def])
 >> Rewr'
 >> Know ‘inv (&SUC n) * (&SUC n * m) = m’
 >- (REWRITE_TAC [mul_assoc] \\
     Suff ‘inv (&SUC n) * &SUC n = 1’ >- (Rewr' >> REWRITE_TAC [mul_lone]) \\
     MATCH_MP_TAC mul_linv_pos \\
     rw [extreal_of_num_def, extreal_not_infty, extreal_lt_eq])
 >> Rewr'
 >> ‘&SUC n <> (0 :real)’ by rw []
 >> `?a. Z (SUC n) x = Normal a` by METIS_TAC [extreal_cases] >> POP_ORW
 >> `?b. m = Normal b` by METIS_TAC [extreal_cases] >> POP_ORW
 >> RW_TAC real_ss [extreal_inv_def, extreal_of_num_def, extreal_sub_def,
                    extreal_mul_def, real_normal]
QED

Theorem LLN_alt_converge_AE_IID_shift :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) /\
          identical_distribution p X Borel UNIV /\ integrable p (X 0) ==>
         (LLN p X almost_everywhere <=>
          ((\n x. SIGMA (\i. X i x) (count n) / &n) --> (\x. expectation p (X 0)))
           (almost_everywhere p))
Proof
    RW_TAC std_ss [LLN_alt_converge_AE_IID]
 >> rw [REWRITE_RULE [Once EQ_SYM_EQ, GSYM ADD1]
                     (Q.SPEC ‘1’ converge_AE_alt_shift)]
QED

Theorem IN_MEASURABLE_BOREL_BOREL_truncated :
    !c. (\x. if c <= abs x then 0 else x) IN measurable Borel Borel
Proof
    RW_TAC std_ss [IN_MEASURABLE, SIGMA_ALGEBRA_BOREL, SPACE_BOREL,
                   IN_FUNSET, IN_UNIV, INTER_UNIV, PREIMAGE_def]
 >> Cases_on ‘0 IN s’
 >| [ (* goal 1 (of 2) *)
      Know ‘{x | (if c <= abs x then 0 else x) IN s} =
              {x | c <= x} UNION {x | x <= -c} UNION
              ({x | -c < x /\ x < c} INTER s)’
      >- (rw [Once EXTENSION, le_abs_bounds] \\
          EQ_TAC >> rw [] >| (* 5 subgoals *)
          [ (* goal 1.1 (of 5) *) METIS_TAC [],
            (* goal 1.2 (of 5) *) METIS_TAC [],
            (* goal 1.3 (of 5) *) fs [GSYM extreal_lt_def],
            (* goal 1.4 (of 5) *) METIS_TAC [let_antisym, extreal_lt_def],
            (* goal 1.5 (of 5) *) METIS_TAC [let_antisym, extreal_lt_def] ]) >> Rewr' \\
      MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [SIGMA_ALGEBRA_BOREL] \\
      CONJ_TAC >- (MATCH_MP_TAC SIGMA_ALGEBRA_UNION \\
                   REWRITE_TAC [BOREL_MEASURABLE_SETS, SIGMA_ALGEBRA_BOREL]) \\
      MATCH_MP_TAC SIGMA_ALGEBRA_INTER \\
      ASM_REWRITE_TAC [BOREL_MEASURABLE_SETS, SIGMA_ALGEBRA_BOREL],
      (* goal 2 (of 2) *)
      Know ‘{x | (if c <= abs x then 0 else x) IN s} =
              ({x | -c < x /\ x < c} INTER s)’
      >- (rw [Once EXTENSION, le_abs_bounds] \\
          EQ_TAC >> rw [] >| (* 4 subgoals *)
          [ (* goal 2.1 (of 4) *) fs [GSYM extreal_lt_def],
            (* goal 2.2 (of 4) *) fs [GSYM extreal_lt_def],
            (* goal 2.3 (of 4) *) rw [extreal_lt_def],
            (* goal 2.4 (of 4) *) rw [extreal_lt_def] ]) >> Rewr' \\
      MATCH_MP_TAC SIGMA_ALGEBRA_INTER \\
      ASM_REWRITE_TAC [BOREL_MEASURABLE_SETS, SIGMA_ALGEBRA_BOREL] ]
QED

Theorem IN_MEASURABLE_BOREL_BOREL_truncated' :
    !c. (\x. if c <= abs x then x else 0) IN measurable Borel Borel
Proof
    RW_TAC std_ss [IN_MEASURABLE, SIGMA_ALGEBRA_BOREL, SPACE_BOREL,
                   IN_FUNSET, IN_UNIV, INTER_UNIV, PREIMAGE_def]
 >> Cases_on ‘0 IN s’
 >| [ (* goal 1 (of 2) *)
      Know ‘{x | (if c <= abs x then x else 0) IN s} =
              ({x | -c < x} INTER {x | x < c}) UNION
              (({x | c <= x} UNION {x | x <= -c}) INTER s)’
      >- (rw [Once EXTENSION, le_abs_bounds] \\
          EQ_TAC >> rw [] >| (* 5 subgoals *)
          [ (* goal 1.1 (of 5) *) METIS_TAC [],
            (* goal 1.2 (of 5) *) METIS_TAC [],
            (* goal 1.3 (of 5) *) fs [GSYM extreal_lt_def],
            (* goal 1.4 (of 5) *) METIS_TAC [let_antisym],
            (* goal 1.5 (of 5) *) METIS_TAC [let_antisym] ]) >> Rewr' \\
      ASSUME_TAC SIGMA_ALGEBRA_BOREL \\
      MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [] \\
      CONJ_TAC >- (MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
                   REWRITE_TAC [BOREL_MEASURABLE_SETS]) \\
      MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
      MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [] \\
      REWRITE_TAC [BOREL_MEASURABLE_SETS],
      (* goal 2 (of 2) *)
      Know ‘{x | (if c <= abs x then x else 0) IN s} =
              (({x | c <= x} UNION {x | x <= -c}) INTER s)’
      >- (rw [Once EXTENSION, le_abs_bounds] \\
          EQ_TAC >> rw [] >| (* 3 subgoals *)
          [ (* goal 2.1 (of 3) *) METIS_TAC [],
            (* goal 2.2 (of 3) *) METIS_TAC [],
            (* goal 2.3 (of 3) *) fs [GSYM extreal_lt_def] ]) >> Rewr' \\
      ASSUME_TAC SIGMA_ALGEBRA_BOREL \\
      MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
      MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [] \\
      REWRITE_TAC [BOREL_MEASURABLE_SETS] ]
QED

(* alternative definition of ‘truncated’ from [3, p.62] *)
Theorem truncated_alt :
    !p X n x. prob_space p /\ random_variable (X n) p Borel /\ x IN p_space p ==>
             (truncated X n x =
              X n x * indicator_fn {x | x IN p_space p /\ abs (X n x) < &SUC n} x)
Proof
    RW_TAC set_ss [truncated_def, indicator_fn_def, extreal_lt_def,
                   mul_rone, mul_rzero]
QED

Theorem truncated_le_abs :
    !X n x. abs (truncated X n x) <= abs (X n x)
Proof
    rw [truncated_def, abs_0, abs_pos]
QED

Theorem random_variable_truncated :
    !p X n. prob_space p /\ random_variable (X n) p Borel ==>
            random_variable (truncated X n) p Borel
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘f = \x. if &SUC n <= abs x then 0 else x’
 >> ‘f IN measurable Borel Borel’
       by (rw [Abbr ‘f’, IN_MEASURABLE_BOREL_BOREL_truncated])
 >> ‘truncated X n = f o X n’ by (rw [truncated_def, Abbr ‘f’, o_DEF])
 >> POP_ORW
 >> MATCH_MP_TAC random_variable_comp >> art []
QED

Theorem real_random_variable_truncated :
    !p X n. prob_space p /\ real_random_variable (X n) p ==>
            real_random_variable (truncated X n) p
Proof
    rpt GEN_TAC
 >> SIMP_TAC std_ss [real_random_variable_def]
 >> STRIP_TAC
 >> reverse CONJ_TAC
 >- (Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
     Know ‘truncated X n x =
           X n x * indicator_fn {x | x IN p_space p /\ abs (X n x) < &SUC n} x’
     >- (MATCH_MP_TAC truncated_alt >> art []) >> Rewr' \\
    ‘?r. X n x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?z. indicator_fn {x | x IN p_space p /\ abs (X n x) < &SUC n} x = Normal z’
       by METIS_TAC [indicator_fn_normal] >> POP_ORW \\
     rw [extreal_mul_def])
 >> MATCH_MP_TAC random_variable_truncated >> art []
QED

Theorem integrable_truncated :
    !p X n. prob_space p /\ random_variable (X n) p Borel /\ integrable p (X n) ==>
            integrable p (truncated X n)
Proof
    rpt STRIP_TAC
 >> ‘random_variable (truncated X n) p Borel’ by PROVE_TAC [random_variable_truncated]
 >> FULL_SIMP_TAC std_ss [prob_space_def, random_variable_def, p_space_def, events_def]
 >> MATCH_MP_TAC integrable_bounded
 >> Q.EXISTS_TAC ‘abs o (X n)’ >> art []
 >> reverse CONJ_TAC >- rw [o_DEF, truncated_le_abs]
 >> MATCH_MP_TAC integrable_abs >> art []
QED

(* this theorem requires lebesgue_dominated_convergence *)
Theorem truncated_vars_expectation :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) /\
          identical_distribution p X Borel UNIV /\ integrable p (X 0) ==>
         ((\n. real (expectation p (truncated X n))) -->
               real (expectation p (X 0))) sequentially
Proof
    rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!n. real_random_variable (X n) p’
      (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
       (REWRITE_RULE [real_random_variable_def]))
 >> Know ‘!n. integrable p (X n)’
 >- (MATCH_MP_TAC identical_distribution_integrable >> art [] \\
     fs [real_random_variable_def])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘integrable p (X 0)’ K_TAC
 >> Q.ABBREV_TAC ‘f = \n x. if &SUC n <= abs x then 0 else x’
 >> ‘!n. (f n) IN measurable Borel Borel’
       by (rw [Abbr ‘f’, IN_MEASURABLE_BOREL_BOREL_truncated])
 >> ‘!n. truncated X n = f n o X n’
       by (rw [truncated_def, Abbr ‘f’, o_DEF]) >> POP_ORW
 >> ‘!n. expectation p (f n o X n) = expectation p (f n o X 0)’
       by METIS_TAC [identical_distribution_alt'] >> POP_ORW
 >> FULL_SIMP_TAC std_ss [expectation_def, prob_space_def, p_space_def,
                          events_def, random_variable_def]
 >> Q.PAT_X_ASSUM ‘identical_distribution p X Borel univ(:num)’ K_TAC
 (* stage work, below is lebesgueTheory only *)
 >> HO_MATCH_MP_TAC lebesgue_dominated_convergence >> art []
 >> ‘integrable p (abs o X 0)’ by METIS_TAC [integrable_abs]
 >> Know ‘?w. integrable p w /\
              (!x. x IN m_space p ==> 0 <= w x /\ w x <> PosInf) /\
              !n x. x IN m_space p ==> abs ((f n o X 0) x) <= w x’
 >- (Q.EXISTS_TAC ‘abs o X 0’ >> rw [Abbr ‘f’, o_DEF] \\
    ‘?r. X 0 x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_abs_def])
 >> STRIP_TAC (* this asserts ‘w’ *)
 >> STRONG_CONJ_TAC (* !n. integrable p (f n o X 0) *)
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC integrable_bounded \\
     Q.EXISTS_TAC ‘abs o X 0’ >> art [] \\
     CONJ_TAC >- (MATCH_MP_TAC MEASURABLE_COMP \\
                  Q.EXISTS_TAC ‘Borel’ >> art []) \\
     rw [o_DEF, Abbr ‘f’])
 >> DISCH_TAC
 >> STRONG_CONJ_TAC
 >- (rpt GEN_TAC >> DISCH_TAC \\
     Know ‘(f n o X 0) x = X 0 x * indicator_fn {x | abs (X 0 x) < &SUC n} x’
     >- (RW_TAC set_ss [Abbr ‘f’, o_DEF, indicator_fn_def, mul_rzero, mul_rone] \\
         METIS_TAC [extreal_lt_def]) >> Rewr' \\
    ‘?a. X 0 x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?b. indicator_fn {x | abs (X 0 x) < &SUC n} x = Normal b’
         by METIS_TAC [indicator_fn_normal] >> POP_ORW \\
     rw [extreal_mul_def])
 >> DISCH_TAC
 >> CONJ_TAC >- rw [] (* X 0 x <> PosInf /\ X 0 x <> NegInf) *)
 >> reverse CONJ_TAC >- (Q.EXISTS_TAC ‘w’ >> art [])
 >> RW_TAC std_ss [LIM_SEQUENTIALLY, dist]
 (* key idea: ‘f n’ vanishes when ‘n >= abs (X 0 x)’ *)
 >> MP_TAC (Q.SPEC ‘abs ((X :num -> 'a -> extreal) 0 x)’ SIMP_EXTREAL_ARCH)
 >> Know ‘abs (X 0 x) <> PosInf’
 >- (‘?r. X 0 x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_abs_def])
 >> RW_TAC std_ss [] (* this asserts the needed ‘n’ *)
 >> Know ‘abs (X 0 x) < &SUC n’
 >- (MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘&n’ >> art [] \\
     rw [extreal_of_num_def, extreal_lt_eq])
 >> DISCH_TAC
 >> Q.EXISTS_TAC ‘n’
 >> Q.X_GEN_TAC ‘m’ >> DISCH_TAC
 >> Suff ‘f m (X 0 x) = X 0 x’ >- rw []
 >> rw [Abbr ‘f’]
 >> ‘&SUC n <= (&SUC m) :extreal’ by rw [extreal_of_num_def, extreal_le_eq]
 >> ‘abs (X 0 x) < &SUC m’ by PROVE_TAC [lte_trans]
 >> PROVE_TAC [let_antisym]
QED

(* The limit of the arithmetic means of the first n partial sums is called
  "Cesaro summation". cf. https://en.wikipedia.org/wiki/Cesaro_summation

   This proof uses iterateTheory (numseg).
 *)
Theorem LIM_SEQUENTIALLY_CESARO :
    !f l. ((\n. f n) --> l) sequentially ==>
          ((\n. SIGMA f (count (SUC n)) / &SUC n) --> l) sequentially
Proof
    RW_TAC std_ss [LIM_SEQUENTIALLY, dist]
 >> Q.ABBREV_TAC ‘g = \n. f n - l’
 >> Know ‘!n. SIGMA f (count (SUC n)) / &SUC n - l =
              SIGMA g (count (SUC n)) / &SUC n’
 >- (rw [Abbr ‘g’] \\
     Know ‘SIGMA (\n. f n - l) (count (SUC n)) =
           SIGMA f (count (SUC n)) - SIGMA (\x. l) (count (SUC n))’
     >- (HO_MATCH_MP_TAC REAL_SUM_IMAGE_SUB >> rw []) >> Rewr' \\
    ‘FINITE (count (SUC n))’ by rw [] \\
     rw [REAL_SUM_IMAGE_FINITE_CONST3, CARD_COUNT, real_div, REAL_SUB_LDISTRIB])
 >> Rewr'
 >> Q.PAT_X_ASSUM ‘!e. 0 < e ==> _’ MP_TAC
 >> ‘!n. f n - l = g n’ by METIS_TAC [] >> POP_ORW
 >> DISCH_THEN (MP_TAC o (Q.SPEC ‘(1 / 2) * e’))
 >> ‘0 < 1 / 2 * e’ by rw []
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM ‘Abbrev (g = (\n. f n - l))’ K_TAC
 (* special case: N = 0 *)
 >> Cases_on ‘N = 0’
 >- (fs [] >> Q.EXISTS_TAC ‘0’ >> rw [real_div] \\
    ‘abs (inv (&SUC n) * SIGMA g (count (SUC n))) =
     abs (inv (&SUC n)) * abs (SIGMA g (count (SUC n)))’
       by rw [REAL_ABS_MUL] >> POP_ORW \\
    ‘abs (inv (&SUC n)) = inv (&SUC n) :real’ by rw [] >> POP_ORW \\
     MATCH_MP_TAC REAL_LET_TRANS \\
     Q.EXISTS_TAC ‘inv (&SUC n) * SIGMA (abs o g) (count (SUC n))’ \\
     CONJ_TAC >- (MATCH_MP_TAC REAL_LE_LMUL_IMP >> rw [] \\
                  MATCH_MP_TAC REAL_SUM_IMAGE_ABS_TRIANGLE >> rw []) \\
     MATCH_MP_TAC REAL_LET_TRANS \\
     Q.EXISTS_TAC ‘inv (&SUC n) * SIGMA (\i. 1 / 2 * e) (count (SUC n))’ \\
     CONJ_TAC >- (MATCH_MP_TAC REAL_LE_LMUL_IMP >> rw [] \\
                  irule REAL_SUM_IMAGE_MONO >> rw [o_DEF] \\
                  MATCH_MP_TAC REAL_LT_IMP_LE >> rw []) \\
     rw [REAL_SUM_IMAGE_FINITE_CONST3])
 (* stage work, now ‘0 < N’ *)
 >> ‘0 < N’ by RW_TAC arith_ss []
 >> Q.ABBREV_TAC ‘M = abs (SIGMA g (count N))’
 >> Q.EXISTS_TAC ‘MAX N (2 * clg (M * inv e))’
 >> RW_TAC std_ss [MAX_LE]
 (* applying LE_NUM_CEILING *)
 >> ‘M * realinv e <= &clg (M * realinv e)’ by PROVE_TAC [LE_NUM_CEILING]
 >> Know ‘2 * &clg (M * realinv e) <= (&n :real)’
 >- (REWRITE_TAC [GSYM REAL_DOUBLE] \\
    ‘!n. &n + (&n :real) = &(n + n)’ by rw [] >> POP_ORW \\
     REWRITE_TAC [GSYM TIMES2] >> rw [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘2 * clg (M * realinv e) <= n’ K_TAC
 >> Know ‘2 * (M * realinv e) <= &n’
 >- (MATCH_MP_TAC REAL_LE_TRANS \\
     Q.EXISTS_TAC ‘2 * &clg (M * realinv e)’ >> art [] \\
     MATCH_MP_TAC REAL_LE_LMUL_IMP >> rw [])
 >> NTAC 2 (POP_ASSUM K_TAC) (* clg is gone *)
 >> DISCH_TAC
 >> ‘count (SUC n) = (count N) UNION (N .. n)’
      by (rw [Once EXTENSION, numseg, IN_COUNT]) >> POP_ORW
 >> ‘DISJOINT (count N) (N .. n)’
      by (rw [DISJOINT_ALT, IN_COUNT, IN_NUMSEG])
 >> Know ‘SIGMA g ((count N) UNION (N .. n)) = SIGMA g (count N) + SIGMA g (N .. n)’
 >- (MATCH_MP_TAC REAL_SUM_IMAGE_DISJOINT_UNION \\
     rw [FINITE_COUNT, FINITE_NUMSEG]) >> Rewr'
 >> REWRITE_TAC [real_div, REAL_ADD_RDISTRIB]
 (* applying ABS_TRIANGLE *)
 >> MATCH_MP_TAC REAL_LET_TRANS
 >> Q.EXISTS_TAC ‘abs (SIGMA g (count N) * inv (&SUC n)) +
                  abs (SIGMA g (N .. n)  * inv (&SUC n))’
 >> REWRITE_TAC [ABS_TRIANGLE]
 >> Suff ‘abs (SIGMA g (count N) * inv (&SUC n)) < 1 / 2 * e /\
          abs (SIGMA g (N .. n) * inv (&SUC n)) < 1 / 2 * e’
 >- (DISCH_TAC \\
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM X_HALF_HALF] \\
     MATCH_MP_TAC REAL_LT_ADD2 >> art [])
 (* applying REAL_SUM_IMAGE_ABS_TRIANGLE *)
 >> reverse CONJ_TAC
 >- (Know ‘abs (SIGMA g (N .. n) * inv (&SUC n)) =
           abs (SIGMA g (N .. n)) * abs (inv (&SUC n))’
     >- (rw [REAL_ABS_MUL]) >> Rewr' \\
    ‘abs (inv (&SUC n)) = inv (&SUC n) :real’ by rw [] >> POP_ORW \\
     MATCH_MP_TAC REAL_LET_TRANS \\
     Q.EXISTS_TAC ‘SIGMA (abs o g) (N .. n) * inv (&SUC n)’ \\
     CONJ_TAC >- (MATCH_MP_TAC REAL_LE_RMUL_IMP >> rw [] \\
                  MATCH_MP_TAC REAL_SUM_IMAGE_ABS_TRIANGLE \\
                  REWRITE_TAC [FINITE_NUMSEG]) \\
     MATCH_MP_TAC REAL_LET_TRANS \\
     Q.EXISTS_TAC ‘SIGMA (\i. 1 / 2 * e) (N .. n) * inv (&SUC n)’ \\
     CONJ_TAC >- (MATCH_MP_TAC REAL_LE_RMUL_IMP >> rw [] \\
                  irule REAL_SUM_IMAGE_MONO >> rw [FINITE_NUMSEG, IN_NUMSEG, o_DEF] \\
                  MATCH_MP_TAC REAL_LT_IMP_LE >> fs []) \\
    ‘FINITE (N .. n)’ by PROVE_TAC [FINITE_NUMSEG] \\
     rw [REAL_SUM_IMAGE_FINITE_CONST3, CARD_NUMSEG, GSYM ADD1])
 (* final part *)
 >> Know ‘abs (SIGMA g (count N) * inv (&SUC n)) = M * abs (inv (&SUC n))’
 >- (rw [Abbr ‘M’, REAL_ABS_MUL]) >> Rewr'
 >> ‘abs (inv (&SUC n)) = inv (&SUC n) :real’ by rw [] >> POP_ORW
 >> Q.PAT_X_ASSUM ‘2 * (M * realinv e) <= &n’
      (MP_TAC o (ONCE_REWRITE_RULE [REAL_MUL_ASSOC]))
 >> ‘e <> (0 :real)’ by PROVE_TAC [REAL_LT_IMP_NE] >> rw []
 >> MATCH_MP_TAC REAL_LET_TRANS
 >> Q.EXISTS_TAC ‘e * &n’ >> rw []
QED

Theorem truncated_vars_expectation' :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) /\
          identical_distribution p X Borel UNIV /\ integrable p (X 0) ==>
         ((\n. real (expectation p
                      (\x. SIGMA (\i. truncated X i x) (count (SUC n))) / &SUC n)) -->
               real (expectation p (X 0))) sequentially
Proof
    rpt STRIP_TAC
 >> ‘!n. real_random_variable (truncated X n) p’
       by PROVE_TAC [real_random_variable_truncated]
 >> Know ‘((\n. real (expectation p (truncated X n))) -->
                real (expectation p (X 0))) sequentially’
 >- (MATCH_MP_TAC truncated_vars_expectation >> art [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘!n. real_random_variable (X n) p’
      (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
       (REWRITE_RULE [real_random_variable_def]))
 >> Q.PAT_X_ASSUM ‘!n. real_random_variable (truncated X n) p’
      (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
       (REWRITE_RULE [real_random_variable_def]))
 >> Know ‘!n. integrable p (X n)’
 >- (MATCH_MP_TAC identical_distribution_integrable >> art [])
 >> DISCH_TAC
 >> ‘!n. integrable p (truncated X n)’ by PROVE_TAC [integrable_truncated]
 (* applying integral_sum *)
 >> Know ‘!n. expectation p
                (\x. SIGMA (\i. truncated X i x) (count (SUC n))) =
              SIGMA (\i. expectation p (truncated X i)) (count (SUC n))’
 >- (RW_TAC std_ss [expectation_def] \\
     HO_MATCH_MP_TAC integral_sum \\
     FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, FINITE_COUNT])
 >> Rewr'
 >> Q.ABBREV_TAC ‘f = \n. expectation p (truncated X n)’
 >> Q.ABBREV_TAC ‘m = expectation p (X 0)’
 >> Q.PAT_X_ASSUM ‘((\n. real (expectation p (truncated X n))) --> real m)
                     sequentially’ MP_TAC
 >> ‘!n. expectation p (truncated X n) = f n’ by METIS_TAC []
 >> POP_ORW
 >> ‘!n. f n <> PosInf /\ f n <> NegInf’ by METIS_TAC [expectation_finite]
 >> ‘m <> PosInf /\ m <> NegInf’ by METIS_TAC [expectation_finite]
 >> Q.ABBREV_TAC ‘g = real o f’
 >> Know ‘f = Normal o g’
 >- (FUN_EQ_TAC >> Q.X_GEN_TAC ‘n’ \\
     rw [o_DEF, Abbr ‘g’, Once EQ_SYM_EQ] \\
     MATCH_MP_TAC normal_real >> art []) >> Rewr'
 >> simp [o_DEF]
 >> Know ‘!n. SIGMA (\x. Normal (g x)) (count (SUC n)) =
              Normal (SIGMA g (count (SUC n)))’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NORMAL >> rw []) >> Rewr'
 >> ‘!n. &SUC n <> (0 :real)’ by rw []
 >> simp [extreal_div_eq, extreal_of_num_def]
 >> REWRITE_TAC [LIM_SEQUENTIALLY_CESARO]
QED

(* The Weak Law of Large Numbers for I.I.D. Random Variables

   Theorem 5.2.2 [2, p.114]. This law of large numbers is due to Khintchine.

   Key (non-trivial) lemmas used in the main proof (~1200 lines):

 - expectation_converge (expectation_bounds)                 [probabilityTheory]
 - equivalent_thm4 (equivalent_thm3, equivalent_thm2)
 - indep_vars_imp_uncorrelated (indep_vars_expectation)      [probabilityTheory]
 - lebesgue_monotone_convergence_decreasing                  [lebesgueTheory]
 - converge_LP_imp_PR'                                       [probabilityTheory]
 - converge_PR_to_limit' (converge_PR_to_limit)              [probabilityTheory]
 - truncated_vars_expectation' (truncated_vars_expectation,
       which depends on lebesgue_dominated_convergence)      [martingaleTheory]
 *)
Theorem WLLN_IID :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) /\
          pairwise_indep_vars p X (\n. Borel) UNIV /\
          identical_distribution p X Borel UNIV /\ integrable p (X 0)
      ==> LLN p X in_probability
Proof
    RW_TAC std_ss [LLN_alt_converge_PR_IID]
 >> Q.ABBREV_TAC ‘m = expectation p (X 0)’
 >> Know ‘!n. integrable p (X n)’
 >- (MATCH_MP_TAC identical_distribution_integrable >> art [] \\
     fs [real_random_variable_def])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘integrable p (X 0)’ K_TAC
 >> Q.ABBREV_TAC ‘f = \n x. if &SUC n <= abs x then 0 else x’
 >> ‘!n. f n IN measurable Borel Borel’
       by (rw [Abbr ‘f’, IN_MEASURABLE_BOREL_BOREL_truncated])
 (* define Y and prove it's equivalent to X *)
 >> Q.ABBREV_TAC ‘Y = truncated X’
 >> ‘!n. real_random_variable (Y n) p’
       by (rw [Abbr ‘Y’, real_random_variable_truncated])
 (* alternative definition of Y *)
 >> Know ‘!n x. x IN p_space p ==>
                Y n x = X n x *
                        indicator_fn {x | x IN p_space p /\ abs (X n x) < &SUC n} x’
 >- (Q.PAT_X_ASSUM `!n. real_random_variable (X n) p`
       (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
        (REWRITE_RULE [real_random_variable_def])) \\
     rw [Abbr ‘Y’, truncated_alt])
 >> DISCH_TAC
 >> Know ‘pairwise_indep_vars p Y (\n. Borel) UNIV’
 >- (‘Y = (\n. f n o X n)’
       by (rw [Abbr ‘Y’, Abbr ‘f’, truncated_def, o_DEF]) >> POP_ORW \\
     MATCH_MP_TAC pairwise_indep_vars_cong >> art [] \\
     FULL_SIMP_TAC std_ss [real_random_variable_def])
 >> DISCH_TAC
 (* stage work *)
 >> Know ‘!n c. {x | x IN p_space p /\ abs (X n x) < c} IN events p’
 >- (RW_TAC std_ss [abs_bounds_lt] \\
    ‘{x | x IN p_space p /\ -c < X n x /\ X n x < c} =
       ({x | -c < X n x} INTER p_space p) INTER
       ({x | X n x < c}  INTER p_space p)’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC EVENTS_INTER >> art [] \\
     FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, events_def,
                           real_random_variable] \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE])
 >> DISCH_TAC
 (* applying expectation_converge for equivalence of X and Y *)
 >> Know ‘suminf (\n. prob p {x | x IN p_space p /\ &SUC n <= abs (X n x)}) < PosInf’
 >- (Know ‘!n. prob p {x | x IN p_space p /\ &SUC n <= abs (X n x)} =
               prob p {x | x IN p_space p /\ &SUC n <= abs (X 0 x)}’
     >- (Q.X_GEN_TAC ‘n’ \\
         Know ‘!i. {x | x IN p_space p /\ &SUC n <= abs (X i x)} =
                   ((PREIMAGE (X i) {x | &SUC n <= abs x}) INTER p_space p)’
         >- (rw [PREIMAGE_def, Once EXTENSION, Once CONJ_COMM]) >> Rewr' \\
         (fs o wrap) (SIMP_RULE std_ss [distribution_def] identical_distribution_def) \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
        ‘{x | &SUC n <= abs x} = {x | &SUC n <= x} UNION {x | x <= -&SUC n}’
           by SET_TAC [le_abs_bounds] >> POP_ORW \\
         MATCH_MP_TAC SIGMA_ALGEBRA_UNION \\
         rw [BOREL_MEASURABLE_SETS, SIGMA_ALGEBRA_BOREL]) >> Rewr' \\
     Suff ‘expectation p (abs o (X 0)) < PosInf’
     >- METIS_TAC [expectation_converge] \\
    ‘integrable p (abs o (X 0))’ by METIS_TAC [prob_space_def, integrable_abs] \\
     METIS_TAC [expectation_finite, lt_infty])
 >> DISCH_TAC
 >> Know ‘equivalent p X Y’
 >- (REWRITE_TAC [equivalent_def] \\
     Suff ‘!n x. X n x <> Y n x <=> &SUC n <= abs (X n x)’ >- (Rewr' >> art []) \\
     NTAC 2 (POP_ASSUM K_TAC) \\
    ‘Y = (\n. f n o X n)’
       by (rw [Abbr ‘Y’, Abbr ‘f’, truncated_def, o_DEF]) >> POP_ORW \\
     rw [Abbr ‘f’] \\
     CCONTR_TAC >> fs [abs_0] \\
     fs [extreal_of_num_def, extreal_le_eq])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘suminf _ < PosInf’ K_TAC
 >> Know ‘!n. finite_second_moments p (Y n)’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC bounded_imp_finite_second_moments \\
     Q.EXISTS_TAC ‘&SUC n’ >> art [] \\
     CONJ_TAC >- fs [real_random_variable_def] \\
     NTAC 3 (POP_ASSUM K_TAC) \\
    ‘Y = (\n. f n o X n)’
       by (rw [Abbr ‘Y’, Abbr ‘f’, truncated_def, o_DEF]) >> POP_ORW \\
     rw [Abbr ‘f’]
     >- (rw [abs_0, extreal_of_num_def, extreal_le_eq, extreal_abs_def]) \\
     MATCH_MP_TAC lt_imp_le \\
     FULL_SIMP_TAC std_ss [GSYM extreal_lt_def, extreal_of_num_def,
                           extreal_le_eq, extreal_abs_def])
 >> DISCH_TAC
 >> Know ‘!i j. i <> j ==> uncorrelated p (Y i) (Y j)’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC indep_vars_imp_uncorrelated >> art [] \\
     fs [pairwise_indep_vars_def])
 >> DISCH_TAC
 (* applying equivalent_thm4 *)
 >> MATCH_MP_TAC equivalent_thm4
 >> Q.EXISTS_TAC ‘Y’
 >> rw [Once equivalent_comm]
 >- (MATCH_MP_TAC real_random_variable_const >> art [] \\
     Q.UNABBREV_TAC ‘m’ >> MATCH_MP_TAC expectation_finite >> art [])
 (* stage work, defining ‘Z’ as partial sums of ‘Y’ *)
 >> Q.ABBREV_TAC ‘Z = \n x. SIGMA (\i. Y i x) (count n)’
 >> ‘!n x. SIGMA (\i. Y i x) (count (SUC n)) = Z (SUC n) x’ by METIS_TAC []
 >> POP_ORW
 (* estimate the variance of ‘Z’ *)
 >> Know ‘!n. variance p (Z n) <=
              SIGMA (\i. expectation p (\x. (Y i x) pow 2)) (count n)’
 >- (RW_TAC std_ss [Abbr ‘Z’] \\
     Know ‘variance p (\x. SIGMA (\i. Y i x) (count n)) =
           SIGMA (\i. variance p (Y i)) (count n)’
     >- (MATCH_MP_TAC (INST_TYPE [“:'index” |-> “:num”] variance_sum) \\
         rw [uncorrelated_vars_def]) >> Rewr' \\
     irule EXTREAL_SUM_IMAGE_MONO \\
     CONJ_TAC >- (Q.X_GEN_TAC ‘i’ >> rw [] \\
                  MATCH_MP_TAC variance_le >> art [] \\
                  METIS_TAC [finite_second_moments_eq_integrable_square]) \\
     REWRITE_TAC [FINITE_COUNT] >> DISJ1_TAC (* easy choice *) \\
     Q.X_GEN_TAC ‘i’ >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC pos_not_neginf \\
       MATCH_MP_TAC variance_pos >> art [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC pos_not_neginf \\
       MATCH_MP_TAC expectation_pos >> rw [le_pow2] ])
 >> DISCH_TAC
 >> Know ‘!n. expectation p (\x. Y n x pow 2) <> PosInf /\
              expectation p (\x. Y n x pow 2) <> NegInf’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC expectation_finite >> art [] \\
     METIS_TAC [finite_second_moments_eq_integrable_square])
 >> DISCH_TAC
 (* stage work (further estimate the variance of ‘Z’)

    The antecedent ‘!i. 0 < a i /\ a i < &i’ in the original proof can be weaken
    to ‘!i. 0 <= a i /\ a i <= &i’ (thus ‘a i < &SUC i’) for easier applications
    later, e.g. when ‘a = \n. sqrt &n’.                             -- Chun Tian
  *)
 >> Know ‘!a. (!i. 0 <= a i /\ a i <= &i) ==>
              !n. SIGMA (\i. expectation p (\x. (Y i x) pow 2)) (count n) <=
                  &n * (a n) * expectation p (abs o (X 0)) +
                  &n pow 2 *
                  expectation p (\x. abs (X 0 x) *
                                     indicator_fn {x | x IN p_space p /\
                                                       a n <= abs (X 0 x)} x)’
 >- (rpt STRIP_TAC \\
     Know ‘!n. a n <> NegInf /\ a n <> PosInf’
     >- (Q.X_GEN_TAC ‘n’ \\
         CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf >> art []) \\
         REWRITE_TAC [lt_infty] \\
         MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘&n’ >> art [] \\
         rw [extreal_of_num_def, GSYM lt_infty, extreal_not_infty]) >> DISCH_TAC \\
     Q.ABBREV_TAC ‘b = real o a’ \\
     Know ‘!i. 0 <= b i /\ b i <= &i’
     >- (Q.X_GEN_TAC ‘i’ \\
        ‘?r. a i = Normal r’ by METIS_TAC [extreal_cases] \\
        ‘0 <= r /\ r <= &i’ by METIS_TAC [extreal_of_num_def, extreal_le_eq] \\
         rw [Abbr ‘b’, real_normal]) >> DISCH_TAC \\
     Q.ABBREV_TAC ‘k = flr (b n)’ \\
     Know ‘&k <= a n’
     >- (Know ‘!i. a i = Normal (b i)’
         >- (rw [Abbr ‘b’, normal_real]) >> Rewr' \\
         rw [extreal_of_num_def, extreal_le_eq, Abbr ‘k’] \\
         MATCH_MP_TAC NUM_FLOOR_LE >> art []) >> DISCH_TAC \\
     Know ‘k <= n’
     >- (Suff ‘(&k :extreal) <= &n’ >- rw [extreal_of_num_def, extreal_le_eq] \\
         MATCH_MP_TAC le_trans >> Q.EXISTS_TAC ‘a n’ >> art []) >> DISCH_TAC \\
    ‘count n = (count k) UNION {m | k <= m /\ m < n}’
       by (rw [Once EXTENSION, IN_COUNT]) >> POP_ORW \\
    ‘DISJOINT (count k) {m | k <= m /\ m < n}’ by (rw [DISJOINT_ALT]) \\
     Know ‘FINITE {m | k <= m /\ m < n}’
     >- (irule SUBSET_FINITE >> Q.EXISTS_TAC ‘count n’ \\
         rw [FINITE_COUNT, SUBSET_DEF]) >> DISCH_TAC \\
     Know ‘SIGMA (\i. expectation p (\x. Y i x pow 2))
                 (count k UNION {m | k <= m /\ m < n}) =
           SIGMA (\i. expectation p (\x. Y i x pow 2)) (count k) +
           SIGMA (\i. expectation p (\x. Y i x pow 2)) {m | k <= m /\ m < n}’
     >- (irule EXTREAL_SUM_IMAGE_DISJOINT_UNION >> rw [] \\
         irule SUBSET_FINITE >> Q.EXISTS_TAC ‘count n’ >> rw [count_def] \\
         SET_TAC []) >> Rewr' \\
    ‘!i c. prob p {x | x IN p_space p /\ abs (X i x) < c} < PosInf’
        by METIS_TAC [PROB_FINITE, lt_infty] \\
     Know ‘!i. integrable p
                 (\x. abs (X i x) *
                      indicator_fn {x | x IN p_space p /\ abs (X i x) < a n} x)’
     >- (Q.X_GEN_TAC ‘i’ \\
         FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, events_def,
                               prob_def, real_random_variable_def] \\
         HO_MATCH_MP_TAC integrable_mul_indicator >> art [] \\
         CONJ_TAC >- METIS_TAC [abs_not_infty] \\
         MATCH_MP_TAC (REWRITE_RULE [o_DEF] integrable_abs) >> art []) >> DISCH_TAC \\
     Know ‘!i. i < k ==>
               expectation p (\x. Y i x pow 2) <= a n *
               expectation p
                 (\x. abs (X i x) *
                      indicator_fn {x | x IN p_space p /\ abs (X i x) < a n} x)’
     >- (rpt STRIP_TAC \\
         Know ‘a n * expectation p
                      (\x. abs (X i x) *
                           indicator_fn {x | x IN p_space p /\ abs (X i x) < a n} x) =
               expectation p
                 (\x. a n *
                     (abs (X i x) *
                      indicator_fn {x | x IN p_space p /\ abs (X i x) < a n} x))’
         >- (‘?r. a n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
             ONCE_REWRITE_TAC [Once EQ_SYM_EQ] \\
             HO_MATCH_MP_TAC expectation_cmul >> art [] \\
             HO_MATCH_MP_TAC integrable_mul_indicator \\
             FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, events_def,
                                   prob_def, real_random_variable_def] \\
             CONJ_TAC >- METIS_TAC [abs_not_infty] \\
             MATCH_MP_TAC (REWRITE_RULE [o_DEF] integrable_abs) >> art []) >> Rewr' \\
         MATCH_MP_TAC (REWRITE_RULE [GSYM expectation_def] integral_mono) >> simp [] \\
         STRONG_CONJ_TAC >- FULL_SIMP_TAC std_ss [prob_space_def] \\
         DISCH_TAC (* measure_space p *) \\
         CONJ_TAC >- METIS_TAC [finite_second_moments_eq_integrable_square] \\
         CONJ_TAC (* integrable *)
         >- (‘?r. a n = Normal r’ by METIS_TAC [extreal_cases] \\
             POP_ASSUM (FULL_SIMP_TAC std_ss o wrap) \\
             FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, events_def,
                                   prob_def, real_random_variable_def] \\
             HO_MATCH_MP_TAC integrable_cmul >> art []) \\
         FULL_SIMP_TAC std_ss [p_space_def] \\
         RW_TAC set_ss [pow_2_abs, indicator_fn_def, mul_rone, mul_rzero,
                        abs_0, le_refl] >| (* 3 subgoals *)
         [ (* goal 1 (of 3) *)
           MATCH_MP_TAC le_rmul_imp >> REWRITE_TAC [abs_pos] \\
           MATCH_MP_TAC lt_imp_le >> art [],
           (* goal 2 (of 3) *)
           Suff ‘abs (X i x) < a n’ >- rw [] \\
           Q.PAT_X_ASSUM ‘~(abs (X i x) < a n)’ K_TAC \\
           MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC ‘&SUC i’ >> art [] \\
           MATCH_MP_TAC le_trans >> Q.EXISTS_TAC ‘&k’ >> art [] \\
           rw [extreal_of_num_def, extreal_le_eq],
           (* goal 3 (of 3) *)
           MATCH_MP_TAC le_mul >> art [abs_pos] ]) >> DISCH_TAC \\
  (* LHS: reduce the goal *)
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC ‘SIGMA (\i. a n *
                              expectation p
                                (\x. abs (X i x) *
                                     indicator_fn {x | x IN p_space p /\ abs (X i x) < a n} x))
                         (count k) +
                   SIGMA (\i. expectation p (\x. Y i x pow 2)) {m | k <= m /\ m < n}’ \\
     CONJ_TAC >- (MATCH_MP_TAC le_radd_imp \\
                  irule EXTREAL_SUM_IMAGE_MONO \\
                  ASM_SIMP_TAC std_ss [IN_COUNT, FINITE_COUNT] >> DISJ1_TAC \\
                  Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
                  MATCH_MP_TAC pos_not_neginf \\
                  MATCH_MP_TAC le_mul >> art [] \\
                  MATCH_MP_TAC expectation_pos >> art [] \\
                  Q.X_GEN_TAC ‘x’ >> rw [] \\
                  MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS]) \\
  (* stage work *)
     Know ‘!i. integrable p
                 (\x. abs (X i x) * indicator_fn {x | x IN p_space p /\ a n <= abs (X i x) /\
                                                      abs (X i x) < &SUC n} x)’
     >- (Q.X_GEN_TAC ‘i’ \\
         HO_MATCH_MP_TAC integrable_mul_indicator \\
         FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, events_def,
                               prob_def, real_random_variable_def] \\
        ‘&SUC n = Normal (&SUC n)’ by rw [extreal_of_num_def] >> POP_ORW \\
         Q.ABBREV_TAC ‘(r :real) = &SUC n’ \\
         STRONG_CONJ_TAC
         >- (‘{x | x IN m_space p /\ a n <= abs (X i x) /\ abs (X i x) < Normal r} =
              {x | x IN m_space p /\ a n <= abs (X i x)} INTER
              {x | x IN m_space p /\ abs (X i x) < Normal r}’ by SET_TAC [] >> POP_ORW \\
             MATCH_MP_TAC MEASURE_SPACE_INTER >> art [] \\
             REWRITE_TAC [le_abs_bounds] \\
            ‘{x | x IN m_space p /\ (X i x <= -a n \/ a n <= X i x)} =
               ({x | X i x <= -a n} INTER m_space p) UNION
               ({x | a n <= X i x} INTER m_space p)’ by SET_TAC [] >> POP_ORW \\
             MATCH_MP_TAC MEASURE_SPACE_UNION >> art [] \\
             FULL_SIMP_TAC std_ss [random_variable_def, p_space_def, events_def] \\
             METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC \\
         CONJ_TAC (* measure < PosInf *)
         >- (MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘measure p (m_space p)’ \\
             reverse CONJ_TAC >- rw [GSYM lt_infty, extreal_of_num_def] \\
             MATCH_MP_TAC INCREASING >> art [] \\
             CONJ_TAC >- (MATCH_MP_TAC MEASURE_SPACE_INCREASING >> art []) \\
             reverse CONJ_TAC >- (MATCH_MP_TAC MEASURE_SPACE_SPACE >> art []) \\
             rw [SUBSET_DEF]) \\
         CONJ_TAC >- METIS_TAC [abs_not_infty] \\
         MATCH_MP_TAC (REWRITE_RULE [o_DEF] integrable_abs) >> art []) \\
     DISCH_TAC \\
     Know ‘!i. k <= i /\ i < n ==>
               expectation p (\x. Y i x pow 2) <=
               a n * expectation p (\x. abs (X i x) *
                                        indicator_fn {x | x IN p_space p /\ abs (X i x) < a n} x) +
               &n * expectation p (\x. abs (X i x) *
                                        indicator_fn {x | x IN p_space p /\ a n <= abs (X i x) /\
                                                          abs (X i x) < &SUC n} x)’
     >- (rpt STRIP_TAC \\
         Know ‘a n * expectation p
                       (\x. abs (X i x) *
                            indicator_fn {x | x IN p_space p /\ abs (X i x) < a n} x) =
               expectation p
                 (\x. a n *
                     (abs (X i x) *
                      indicator_fn {x | x IN p_space p /\ abs (X i x) < a n} x))’
         >- (‘?r. a n = Normal r’ by METIS_TAC [extreal_cases] \\
             POP_ASSUM (FULL_SIMP_TAC std_ss o wrap) \\
             ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
             HO_MATCH_MP_TAC expectation_cmul >> art []) >> Rewr' \\
         Know ‘&n * expectation p
                      (\x. abs (X i x) *
                           indicator_fn {x | x IN p_space p /\ a n <= abs (X i x) /\
                                             abs (X i x) < &SUC n} x) =
               expectation p
                 (\x. &n * (abs (X i x) *
                            indicator_fn {x | x IN p_space p /\ a n <= abs (X i x) /\
                                              abs (X i x) < &SUC n} x))’
         >- (‘&n = Normal (&n)’ by rw [extreal_of_num_def] \\
             POP_ASSUM (FULL_SIMP_TAC std_ss o wrap) \\
             ONCE_REWRITE_TAC [Once EQ_SYM_EQ] \\
             HO_MATCH_MP_TAC expectation_cmul >> art []) >> Rewr' \\
         Know ‘expectation p
                 (\x. a n *
                     (abs (X i x) *
                      indicator_fn {x | x IN p_space p /\ abs (X i x) < a n} x)) +
               expectation p
                 (\x. &n *
                     (abs (X i x) *
                      indicator_fn
                        {x | x IN p_space p /\ a n <= abs (X i x) /\
                             abs (X i x) < &SUC n} x)) =
               expectation p
                 (\x. (\x. a n *
                          (abs (X i x) *
                           indicator_fn {x | x IN p_space p /\ abs (X i x) < a n} x)) x +
                      (\x. &n *
                          (abs (X i x) *
                           indicator_fn
                             {x | x IN p_space p /\ a n <= abs (X i x) /\
                                  abs (X i x) < &SUC n} x)) x)’
         >- (REWRITE_TAC [Once EQ_SYM_EQ, expectation_def] \\
             MATCH_MP_TAC integral_add >> BETA_TAC \\
             FULL_SIMP_TAC std_ss [prob_space_def] \\
             rpt STRIP_TAC >| (* 3 subgoals *)
             [ (* goal 1 (of 3) *)
              ‘?r. a n = Normal r’ by METIS_TAC [extreal_cases] \\
               POP_ASSUM (FULL_SIMP_TAC std_ss o wrap) \\
               HO_MATCH_MP_TAC integrable_cmul >> art [],
               (* goal 2 (of 3) *)
              ‘&n = Normal (&n)’ by rw [extreal_of_num_def] \\
               POP_ASSUM (FULL_SIMP_TAC std_ss o wrap) \\
               HO_MATCH_MP_TAC integrable_cmul >> art [],
               (* goal 3 (of 3) *)
               DISJ1_TAC >> STRIP_TAC >| (* 2 subgoals *)
               [ (* goal 3.1 (of 2) *)
                 MATCH_MP_TAC pos_not_neginf \\
                 MATCH_MP_TAC le_mul >> art [] \\
                 MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS],
                 (* goal 3.2 (of 2) *)
                 MATCH_MP_TAC pos_not_neginf \\
                 MATCH_MP_TAC le_mul \\
                 CONJ_TAC >- (rw [extreal_of_num_def, extreal_le_eq]) \\
                 MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS] ] ]) >> Rewr' \\
         REWRITE_TAC [expectation_def] \\
         MATCH_MP_TAC integral_mono \\
        ‘integrable p (\x. Y i x pow 2)’
           by METIS_TAC [finite_second_moments_eq_integrable_square] \\
         FULL_SIMP_TAC std_ss [prob_space_def] \\
         CONJ_TAC (* integrable *)
         >- (HO_MATCH_MP_TAC integrable_add >> RW_TAC std_ss [] >| (* 3 subgoals *)
             [ (* goal 1 (of 3) *)
              ‘?r. a n = Normal r’ by METIS_TAC [extreal_cases] \\
               POP_ASSUM (FULL_SIMP_TAC std_ss o wrap) \\
               HO_MATCH_MP_TAC integrable_cmul >> art [],
               (* goal 2 (of 3) *)
              ‘&n = Normal (&n)’ by rw [extreal_of_num_def] \\
               POP_ASSUM (FULL_SIMP_TAC std_ss o wrap) \\
               HO_MATCH_MP_TAC integrable_cmul >> art [],
               (* goal 3 (of 3) *)
               DISJ1_TAC >> STRIP_TAC >| (* 2 subgoals *)
               [ (* goal 3.1 (of 2) *)
                 MATCH_MP_TAC pos_not_neginf \\
                 MATCH_MP_TAC le_mul >> art [] \\
                 MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS],
                 (* goal 3.2 (of 2) *)
                 MATCH_MP_TAC pos_not_neginf \\
                 MATCH_MP_TAC le_mul \\
                 CONJ_TAC >- (rw [extreal_of_num_def, extreal_le_eq]) \\
                 MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS] ] ]) \\
      (* clean up useless assumptions *)
         Q.PAT_X_ASSUM ‘!i. i < k ==> _’           K_TAC \\
         Q.PAT_X_ASSUM ‘!n. variance p (Z n) <= _’ K_TAC \\
         Q.PAT_X_ASSUM ‘!i c. prob p _ < PosInf’   K_TAC \\
         Q.PAT_X_ASSUM ‘!i c. _ IN events p’       K_TAC \\
         rpt (Q.PAT_X_ASSUM ‘!i. integrable p _’   K_TAC) \\
      (* stage work *)
         Q.X_GEN_TAC ‘y’ >> RW_TAC std_ss [p_space_def] \\
      (* case 1 (of 3) *)
         reverse (Cases_on ‘abs (X i y) < &SUC i’)
         >- (‘indicator_fn {x | x IN m_space p /\ abs (X i x) < &SUC i} y = 0’
                by rw [indicator_fn_def] >> POP_ORW \\
             SIMP_TAC std_ss [pow_2, mul_rzero] \\
             MATCH_MP_TAC le_add >> STRIP_TAC >| (* 2 subgoals *)
             [ (* goal 1 (of 2) *)
               MATCH_MP_TAC le_mul >> art [] \\
               MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS],
               (* goal 2 (of 2) *)
               MATCH_MP_TAC le_mul \\
               CONJ_TAC >- (rw [extreal_of_num_def, extreal_le_eq]) \\
               MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS] ]) \\
         Know ‘abs (X i y) < &SUC n’
         >- (MATCH_MP_TAC lt_trans >> Q.EXISTS_TAC ‘&SUC i’ >> art [] \\
             rw [extreal_of_num_def, extreal_lt_eq]) >> DISCH_TAC \\
        ‘indicator_fn {x | x IN m_space p /\ abs (X i x) < &SUC i} y = 1’
           by rw [indicator_fn_def] >> POP_ORW \\
         REWRITE_TAC [mul_rone, pow_2_abs] \\
      (* case 2 (of 3) *)
        ‘abs (X i y) < a n \/ a n <= abs (X i y)’ by METIS_TAC [let_total]
         >- (‘indicator_fn {x | x IN m_space p /\ abs (X i x) < a n} y = 1’
                by rw [indicator_fn_def] >> POP_ORW \\
             REWRITE_TAC [mul_rone] \\
             Know ‘indicator_fn
                     {x | x IN m_space p /\ a n <= abs (X i x) /\ abs (X i x) < &SUC n} y = 0’
             >- (rw [indicator_fn_def] \\
                 METIS_TAC [let_antisym]) >> Rewr' \\
             REWRITE_TAC [mul_rzero, add_rzero] \\
             MATCH_MP_TAC le_rmul_imp >> art [abs_pos] \\
             MATCH_MP_TAC lt_imp_le >> art []) \\
      (* case 3 (of 3) *)
         Know ‘indicator_fn {x | x IN m_space p /\ abs (X i x) < a n} y = 0’
         >- (rw [indicator_fn_def] \\
             METIS_TAC [let_antisym]) >> Rewr' \\
         REWRITE_TAC [mul_rzero, add_lzero] \\
        ‘indicator_fn {x | x IN m_space p /\ a n <= abs (X i x) /\ abs (X i x) < &SUC n} y = 1’
           by rw [indicator_fn_def] >> POP_ORW \\
         REWRITE_TAC [mul_rone] \\
         MATCH_MP_TAC le_rmul_imp >> art [abs_pos] \\
         MATCH_MP_TAC le_trans >> Q.EXISTS_TAC ‘&SUC i’ \\
         CONJ_TAC >- (MATCH_MP_TAC lt_imp_le >> art []) \\
         rw [extreal_of_num_def, extreal_le_eq]) >> DISCH_TAC \\
  (* LHS: reduce the goal *)
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC
      ‘SIGMA (\i. a n *
                  expectation p
                    (\x. abs (X i x) *
                         indicator_fn {x | x IN p_space p /\ abs (X i x) < a n} x))
             (count k) +
       SIGMA (\i. a n *
                  expectation p
                    (\x. abs (X i x) *
                         indicator_fn {x | x IN p_space p /\ abs (X i x) < a n} x) +
                  &n *
                  expectation p
                    (\x. abs (X i x) *
                         indicator_fn
                           {x | x IN p_space p /\ a n <= abs (X i x) /\ abs (X i x) < &SUC n} x))
             {m | k <= m /\ m < n}’ \\
     CONJ_TAC
     >- (MATCH_MP_TAC le_ladd_imp \\
         irule EXTREAL_SUM_IMAGE_MONO >> RW_TAC set_ss [] \\
         DISJ1_TAC >> Q.X_GEN_TAC ‘i’ >> STRIP_TAC \\
         MATCH_MP_TAC pos_not_neginf \\
         MATCH_MP_TAC le_add >> STRIP_TAC >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           MATCH_MP_TAC le_mul >> art [] \\
           MATCH_MP_TAC expectation_pos >> rw [] \\
           MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS],
           (* goal 2 (of 2) *)
           MATCH_MP_TAC le_mul \\
           CONJ_TAC >- (rw [extreal_of_num_def, extreal_le_eq]) \\
           MATCH_MP_TAC expectation_pos >> rw [] \\
           MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS] ]) \\
     Know ‘SIGMA
             (\i. (\i. a n *
                       expectation p
                         (\x. abs (X i x) *
                              indicator_fn {x | x IN p_space p /\ abs (X i x) < a n} x)) i +
                  (\i. &n *
                       expectation p
                         (\x. abs (X i x) *
                              indicator_fn
                                {x | x IN p_space p /\ a n <= abs (X i x) /\
                                     abs (X i x) < &SUC n} x)) i) {m | k <= m /\ m < n} =
           SIGMA (\i. a n *
                      expectation p
                        (\x. abs (X i x) *
                             indicator_fn {x | x IN p_space p /\ abs (X i x) < a n} x))
                 {m | k <= m /\ m < n} +
           SIGMA (\i. &n *
                      expectation p
                        (\x. abs (X i x) *
                             indicator_fn
                               {x | x IN p_space p /\ a n <= abs (X i x) /\
                                    abs (X i x) < &SUC n} x)) {m | k <= m /\ m < n}’
     >- (irule EXTREAL_SUM_IMAGE_ADD >> art [] \\
         DISJ1_TAC >> RW_TAC set_ss [] >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           MATCH_MP_TAC pos_not_neginf \\
           MATCH_MP_TAC le_mul >> art [] \\
           MATCH_MP_TAC expectation_pos >> rw [] \\
           MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS],
           (* goal 2 (of 2) *)
           MATCH_MP_TAC pos_not_neginf \\
           MATCH_MP_TAC le_mul \\
           CONJ_TAC >- (rw [extreal_of_num_def, extreal_le_eq]) \\
           MATCH_MP_TAC expectation_pos >> rw [] \\
           MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS] ]) \\
     DISCH_THEN (ONCE_REWRITE_TAC o wrap o BETA_RULE) \\
  (* applying add_assoc *)
     Know ‘SIGMA (\i. a n *
                      expectation p
                        (\x. abs (X i x) *
                             indicator_fn {x | x IN p_space p /\ abs (X i x) < a n} x))
                 (count k) +
          (SIGMA (\i. a n *
                      expectation p
                        (\x. abs (X i x) *
                             indicator_fn {x | x IN p_space p /\ abs (X i x) < a n} x))
                 {m | k <= m /\ m < n} +
           SIGMA (\i. &n *
                      expectation p
                        (\x. abs (X i x) *
                             indicator_fn
                               {x | x IN p_space p /\ a n <= abs (X i x) /\
                                    abs (X i x) < &SUC n} x)) {m | k <= m /\ m < n}) =
           SIGMA (\i. a n *
                      expectation p
                        (\x. abs (X i x) *
                             indicator_fn {x | x IN p_space p /\ abs (X i x) < a n} x))
                 (count k) +
           SIGMA (\i. a n *
                      expectation p
                        (\x. abs (X i x) *
                             indicator_fn {x | x IN p_space p /\ abs (X i x) < a n} x))
                 {m | k <= m /\ m < n} +
           SIGMA (\i. &n *
                      expectation p
                        (\x. abs (X i x) *
                             indicator_fn
                               {x | x IN p_space p /\ a n <= abs (X i x) /\
                                    abs (X i x) < &SUC n} x)) {m | k <= m /\ m < n}’
     >- (MATCH_MP_TAC add_assoc >> DISJ1_TAC \\
         RW_TAC std_ss [] >> MATCH_MP_TAC pos_not_neginf >| (* 3 subgoals *)
         [ (* goal 1 (of 3) *)
           MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> simp [FINITE_COUNT] \\
           Q.X_GEN_TAC ‘i’ >> STRIP_TAC \\
           MATCH_MP_TAC le_mul >> art [] \\
           MATCH_MP_TAC expectation_pos >> rw [] \\
           MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS],
           (* goal 2 (of 3) *)
           MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> art [] \\
           Q.X_GEN_TAC ‘i’ >> RW_TAC set_ss [] \\
           MATCH_MP_TAC le_mul >> art [] \\
           MATCH_MP_TAC expectation_pos >> rw [] \\
           MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS],
           (* goal 3 (of 3) *)
           MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> art [] \\
           Q.X_GEN_TAC ‘i’ >> RW_TAC set_ss [] \\
           MATCH_MP_TAC le_mul \\
           CONJ_TAC >- (rw [extreal_of_num_def, extreal_le_eq]) \\
           MATCH_MP_TAC expectation_pos >> rw [] \\
           MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS] ]) >> Rewr' \\
     Know ‘SIGMA (\i. a n *
                      expectation p
                        (\x. abs (X i x) *
                             indicator_fn {x | x IN p_space p /\ abs (X i x) < a n} x)) (count k) +
           SIGMA (\i. a n *
                      expectation p
                        (\x. abs (X i x) *
                             indicator_fn {x | x IN p_space p /\ abs (X i x) < a n} x))
                 {m | k <= m /\ m < n} =
           SIGMA (\i. a n *
                      expectation p
                        (\x. abs (X i x) *
                             indicator_fn {x | x IN p_space p /\ abs (X i x) < a n} x)) (count n)’
     >- (‘count n = (count k) UNION {m | k <= m /\ m < n}’
            by (rw [Once EXTENSION, IN_COUNT]) >> POP_ORW \\
         ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         irule EXTREAL_SUM_IMAGE_DISJOINT_UNION >> rw [FINITE_COUNT] \\
         DISJ1_TAC \\
         Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
         MATCH_MP_TAC pos_not_neginf \\
         MATCH_MP_TAC le_mul >> art [] \\
         MATCH_MP_TAC expectation_pos >> simp [] \\
         Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
         MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS]) >> Rewr' \\
     POP_ASSUM K_TAC (* clean up ‘!i. k <= i /\ i < n ==> P’ *) \\
  (* LHS: reduce the goal *)
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC
      ‘SIGMA (\i. a n * expectation p (abs o X i)) (count n) +
       SIGMA (\i. &n *
                  expectation p
                    (\x. abs (X i x) *
                         indicator_fn
                           {x | x IN p_space p /\ a n <= abs (X i x) /\
                                abs (X i x) < &SUC n} x)) {m | k <= m /\ m < n}’ \\
     CONJ_TAC
     >- (MATCH_MP_TAC le_radd_imp \\
         irule EXTREAL_SUM_IMAGE_MONO >> simp [] \\
         reverse CONJ_TAC
         >- (DISJ1_TAC >> Q.X_GEN_TAC ‘i’ >> STRIP_TAC \\
             CONJ_TAC >> MATCH_MP_TAC pos_not_neginf >| (* 2 subgoals *)
             [ (* goal 1 (of 2) *)
               MATCH_MP_TAC le_mul >> art [] \\
               MATCH_MP_TAC expectation_pos >> rw [] \\
               MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS],
               (* goal 2 (of 2) *)
               MATCH_MP_TAC le_mul >> art [] \\
               MATCH_MP_TAC expectation_pos >> rw [abs_pos, o_DEF] ]) \\
         Q.X_GEN_TAC ‘i’ >> STRIP_TAC \\
         MATCH_MP_TAC le_lmul_imp >> art [] \\
         FULL_SIMP_TAC std_ss [expectation_def, prob_space_def, p_space_def] \\
         MATCH_MP_TAC integral_mono >> art [] \\
         CONJ_TAC >- (MATCH_MP_TAC integrable_abs >> art []) \\
         rw [o_DEF] \\
         GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM mul_rone] \\
         MATCH_MP_TAC le_lmul_imp >> rw [abs_pos, INDICATOR_FN_LE_1]) \\
     Know ‘!i. expectation p (abs o X i) = expectation p (abs o X 0)’
     >- (FULL_SIMP_TAC std_ss [real_random_variable_def] \\
         ASSUME_TAC IN_MEASURABLE_BOREL_BOREL_ABS \\
         METIS_TAC [identical_distribution_alt']) >> Rewr' \\
     Know ‘SIGMA (\i. a n * expectation p (abs o X 0)) (count n) =
           &CARD (count n) * (a n * expectation p (abs o X 0))’
     >- (irule EXTREAL_SUM_IMAGE_FINITE_CONST >> rw []) >> Rewr' \\
     REWRITE_TAC [CARD_COUNT, mul_assoc] \\
     MATCH_MP_TAC le_ladd_imp \\
  (* LHS: reduce the goal *)
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC
      ‘SIGMA (\i. &n *
                  expectation p
                    (\x. abs (X i x) *
                         indicator_fn
                           {x | x IN p_space p /\ a n <= abs (X i x) /\
                                abs (X i x) < &SUC n} x)) (count n)’ \\
     CONJ_TAC
     >- (irule EXTREAL_SUM_IMAGE_MONO_SET >> simp [] \\
         reverse CONJ_TAC >- SET_TAC [IN_COUNT] \\
         Q.X_GEN_TAC ‘i’ >> rw [] \\
         MATCH_MP_TAC le_mul \\
         CONJ_TAC >- (rw [extreal_of_num_def, extreal_le_eq]) \\
         MATCH_MP_TAC expectation_pos >> rw [] \\
         MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS]) \\
  (* LHS: reduce the goal *)
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC
      ‘SIGMA (\i. &n *
                  expectation p
                    (\x. abs (X i x) *
                         indicator_fn
                           {x | x IN p_space p /\ a n <= abs (X i x)} x)) (count n)’ \\
     CONJ_TAC
     >- (irule EXTREAL_SUM_IMAGE_MONO >> simp [] \\
         reverse CONJ_TAC
         >- (DISJ1_TAC >> Q.X_GEN_TAC ‘i’ >> STRIP_TAC \\
             CONJ_TAC >> MATCH_MP_TAC pos_not_neginf >| (* 2 subgoals *)
             [ (* goal 1 (of 2) *)
               MATCH_MP_TAC le_mul \\
               CONJ_TAC >- (rw [extreal_of_num_def, extreal_le_eq]) \\
               MATCH_MP_TAC expectation_pos >> rw [] \\
               MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS],
               (* goal 2 (of 2) *)
               MATCH_MP_TAC le_mul \\
               CONJ_TAC >- (rw [extreal_of_num_def, extreal_le_eq]) \\
               MATCH_MP_TAC expectation_pos >> rw [] \\
               MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS] ]) \\
         Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
         MATCH_MP_TAC le_lmul_imp \\
         CONJ_TAC >- (rw [extreal_of_num_def, extreal_le_eq]) \\
         FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, expectation_def] \\
         MATCH_MP_TAC integral_mono >> rw []
         >- (HO_MATCH_MP_TAC integrable_mul_indicator >> simp [] \\
             STRONG_CONJ_TAC (* IN measurable_sets p *)
             >- (REWRITE_TAC [le_abs_bounds] \\
                ‘{x' | x' IN m_space p /\ (X i x' <= -a n \/ a n <= X i x')} =
                   ({x | X i x <= -a n} INTER m_space p) UNION
                   ({x | a n <= X i x}  INTER m_space p)’ by SET_TAC [] >> POP_ORW \\
                 MATCH_MP_TAC MEASURE_SPACE_UNION >> art [] \\
                 FULL_SIMP_TAC std_ss [real_random_variable, p_space_def, events_def] \\
                 METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC \\
             CONJ_TAC
             >- (MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘measure p (m_space p)’ \\
                 reverse CONJ_TAC >- (rw [GSYM lt_infty, extreal_of_num_def]) \\
                 MATCH_MP_TAC INCREASING >> simp [MEASURE_SPACE_SPACE] \\
                 CONJ_TAC >- (MATCH_MP_TAC MEASURE_SPACE_INCREASING >> art []) \\
                 rw [SUBSET_DEF]) \\
             FULL_SIMP_TAC std_ss [real_random_variable_def, p_space_def] \\
             CONJ_TAC >- METIS_TAC [abs_not_infty] \\
             MATCH_MP_TAC (REWRITE_RULE [o_DEF] integrable_abs) >> art []) \\
         MATCH_MP_TAC le_lmul_imp >> art [abs_pos] \\
         MATCH_MP_TAC INDICATOR_FN_MONO >> rw [SUBSET_DEF]) \\
     Q.ABBREV_TAC ‘g = \x. if a n <= abs x then x else 0’ \\
     Know ‘!i x. x IN p_space p ==>
                 abs (X i x) *
                 indicator_fn {x | x IN p_space p /\ a n <= abs (X i x)} x = abs (g (X i x))’
     >- (rw [indicator_fn_def, Abbr ‘g’, abs_0]) >> DISCH_TAC \\
     Know ‘!i. expectation p
                 (\x. abs (X i x) *
                      indicator_fn {x | x IN p_space p /\ a n <= abs (X i x)} x) =
               expectation p (abs o g o X i)’
     >- (Q.X_GEN_TAC ‘i’ \\
         MATCH_MP_TAC expectation_cong >> rw [o_DEF]) >> Rewr' \\
     POP_ASSUM K_TAC \\
    ‘g IN measurable Borel Borel’ by (rw [Abbr ‘g’, IN_MEASURABLE_BOREL_BOREL_truncated']) \\
     Know ‘!i. expectation p (abs o g o X i) = expectation p (abs o g o X 0)’
     >- (FULL_SIMP_TAC std_ss [real_random_variable_def] \\
         ASSUME_TAC IN_MEASURABLE_BOREL_BOREL_ABS \\
         REWRITE_TAC [o_ASSOC] \\
         Know ‘abs o g IN measurable Borel Borel’
         >- (MATCH_MP_TAC MEASURABLE_COMP \\
             Q.EXISTS_TAC ‘Borel’ >> art []) >> DISCH_TAC \\
         METIS_TAC [identical_distribution_alt']) >> Rewr' \\
     Know ‘SIGMA (\i. &n * expectation p (abs o g o X 0)) (count n) =
           &CARD (count n) * (&n * expectation p (abs o g o X 0))’
     >- (irule EXTREAL_SUM_IMAGE_FINITE_CONST >> rw []) >> Rewr' \\
     rw [mul_assoc, CARD_COUNT] \\
     MATCH_MP_TAC le_rmul_imp \\
     CONJ_TAC >- (MATCH_MP_TAC expectation_pos >> rw [o_DEF, abs_pos]) \\
     rw [extreal_of_num_def, extreal_mul_def, extreal_le_eq, pow_2])
(* now choose ‘a’ such that: (but no need to prove all explicitly)

   - !i. 0 <= a i /\ a i <= &i
   - mono_increasing a
   - sup (IMAGE a univ(:num)) = PosInf
   - ((\n. (real o a) (SUC n) / &SUC n) --> 0) sequentially
 *)
 >> DISCH_THEN (MP_TAC o BETA_RULE o (Q.SPEC ‘\n. sqrt &n’))
 >> Know ‘!i. 0 <= sqrt (&i) /\ sqrt (&i) <= &i’
 >- (Q.X_GEN_TAC ‘n’ >> REWRITE_TAC [sqrt_le_n] \\
     MATCH_MP_TAC sqrt_pos_le \\
     rw [extreal_of_num_def, extreal_le_eq])
 >> RW_TAC std_ss []
 >> Know ‘!n x. x IN p_space p ==> Z n x <> PosInf /\ Z n x <> NegInf’
 >- (RW_TAC std_ss [] \\
    ‘Z n x = SIGMA (\i. Y i x) (count n)’ by METIS_TAC [] >> POP_ORW >|
     [ MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF,
       MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF ] \\
     Q.PAT_X_ASSUM ‘!n. real_random_variable (Y n) p’
       (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
        (REWRITE_RULE [real_random_variable_def])) \\
     Q.PAT_X_ASSUM ‘!n x. x IN p_space p ==> Y n x = _’ K_TAC \\
     ASM_SIMP_TAC std_ss [FINITE_COUNT, IN_COUNT])
 >> DISCH_TAC
 >> Know ‘!n. real_random_variable (Z n) p’
 >- (rw [Abbr ‘Z’] >> MATCH_MP_TAC real_random_variable_SIGMA >> art [])
 >> DISCH_TAC
 >> Know ‘!n. finite_second_moments p (Z n)’
 >- (Q.X_GEN_TAC ‘n’ \\
    ‘finite_second_moments p (Z n) <=> variance p (Z n) < PosInf’
       by METIS_TAC [finite_second_moments_eq_finite_variance] >> POP_ORW \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘SIGMA (\i. expectation p (\x. Y i x pow 2)) (count n)’ >> art [] \\
     REWRITE_TAC [GSYM lt_infty] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> rw [FINITE_COUNT])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘M = \n. expectation p (Z n)’
 >> Know ‘!n. M n <> PosInf /\ M n <> NegInf’
 >- (Q.X_GEN_TAC ‘n’ >> SIMP_TAC std_ss [Abbr ‘M’] \\
     MATCH_MP_TAC expectation_finite >> art [] \\
     MATCH_MP_TAC finite_second_moments_imp_integrable >> art [])
 >> DISCH_TAC
 >> Know ‘!n x. x IN p_space p ==> Z n x - M n <> PosInf /\ Z n x - M n <> NegInf’
 >- (rpt GEN_TAC >> DISCH_TAC \\
    ‘?a. Z n x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?b. M n   = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def])
 >> DISCH_TAC
 (* stage work *)
 >> Know ‘((\n x. (Z (SUC n) x - M (SUC n)) / &SUC n) --> (\x. 0)) (in_probability p)’
 >- (HO_MATCH_MP_TAC converge_LP_imp_PR' >> Q.EXISTS_TAC ‘2’ >> simp [] \\
     STRONG_CONJ_TAC (* real_random_variable *)
     >- (rw [Abbr ‘M’] \\
         MATCH_MP_TAC real_random_variable_LLN \\
         Q.EXISTS_TAC ‘Y’ >> rw [] \\
         MATCH_MP_TAC finite_second_moments_imp_integrable >> art []) \\
     DISCH_TAC \\
    ‘real_random_variable (\x. 0) p’ by PROVE_TAC [real_random_variable_zero] \\
     ASM_SIMP_TAC std_ss [converge_LP_alt_pow, sub_rzero, abs_0, zero_pow, lt_02, abs_pow2] \\
     Know ‘expectation p (\x. 0) <> PosInf’
     >- (rw [extreal_of_num_def, expectation_const]) >> Rewr \\
     Know ‘!n. expectation p (\x. ((Z (SUC n) x - M (SUC n)) / &SUC n) pow 2) =
               expectation p (\x. (inv (&SUC n) * (Z (SUC n) x - M (SUC n))) pow 2)’
     >- (Q.X_GEN_TAC ‘n’ \\
         MATCH_MP_TAC expectation_cong >> rw [] \\
         Suff ‘(Z (SUC n) x - M (SUC n)) / &SUC n =
               inv (&SUC n) * (Z (SUC n) x - M (SUC n))’ >- rw [] \\
         MATCH_MP_TAC div_eq_mul_linv >> rw [] \\
         rw [extreal_of_num_def, extreal_lt_eq]) >> Rewr' \\
    ‘!n. &SUC n <> (0 :real)’ by rw [] \\
     ASM_SIMP_TAC std_ss [pow_mul, extreal_of_num_def, extreal_inv_def,
                          extreal_pow_def] \\
     Know ‘!n. expectation p
                 (\x. Normal (inv (&SUC n) pow 2) * (Z (SUC n) x - M (SUC n)) pow 2) =
               Normal (inv (&SUC n) pow 2) *
               expectation p (\x. (Z (SUC n) x - M (SUC n)) pow 2)’
     >- (Q.X_GEN_TAC ‘n’ \\
         HO_MATCH_MP_TAC expectation_cmul >> art [] \\
        ‘?r. M (SUC n) = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         METIS_TAC [finite_second_moments_eq_integrable_squares]) >> Rewr' \\
     CONJ_TAC
     >- (Q.X_GEN_TAC ‘n’ \\
         Know ‘expectation p (\x. (Z (SUC n) x - M (SUC n)) pow 2) <> NegInf’
         >- (MATCH_MP_TAC pos_not_neginf \\
             MATCH_MP_TAC expectation_pos >> rw [le_pow2]) >> DISCH_TAC \\
         Suff ‘expectation p (\x. (Z (SUC n) x - M (SUC n)) pow 2) <> PosInf’
         >- (DISCH_TAC \\
            ‘?r. expectation p (\x. (Z (SUC n) x - M (SUC n)) pow 2) = Normal r’
               by METIS_TAC [extreal_cases] >> POP_ORW \\
             rw [extreal_mul_def]) \\
         rw [Abbr ‘M’, GSYM variance_alt, lt_infty] \\
         METIS_TAC [finite_second_moments_eq_finite_variance]) \\
     Q.PAT_X_ASSUM ‘!n. M n <> PosInf /\ M n <> NegInf’ K_TAC \\
     Q.PAT_X_ASSUM ‘!n x. x IN p_space p ==>
                          Z n x - M n <> PosInf /\ Z n x - M n <> NegInf’ K_TAC \\
     Q.PAT_X_ASSUM ‘!n. real_random_variable
                          (\x. (Z (SUC n) x - M (SUC n)) / &SUC n) p’ K_TAC \\
     SIMP_TAC std_ss [Abbr ‘M’, GSYM variance_alt] \\
  (* stage work *)
     RW_TAC real_ss [LIM_SEQUENTIALLY, dist] \\
     Know ‘!n. abs (real (Normal (realinv (&SUC n) pow 2) * variance p (Z (SUC n)))) =
                    real (Normal (realinv (&SUC n) pow 2) * variance p (Z (SUC n)))’
     >- (rw [ABS_REFL] \\
        ‘0 <= variance p (Z (SUC n))’ by PROVE_TAC [variance_pos] \\
        ‘variance p (Z (SUC n)) <> NegInf’ by PROVE_TAC [pos_not_neginf] \\
        ‘variance p (Z (SUC n)) <> PosInf’
           by METIS_TAC [finite_second_moments_eq_finite_variance, lt_infty] \\
        ‘?r. variance p (Z (SUC n)) = Normal r’ by METIS_TAC [extreal_cases] \\
        ‘0 <= r’ by METIS_TAC [extreal_of_num_def, extreal_le_eq] \\
         rw [extreal_mul_def, real_normal]) >> Rewr' \\
     ONCE_REWRITE_TAC [GSYM extreal_lt_eq] \\
     Know ‘!n. Normal (real (Normal (realinv (&SUC n) pow 2) * variance p (Z (SUC n)))) =
                             Normal (realinv (&SUC n) pow 2) * variance p (Z (SUC n))’
     >- (Q.X_GEN_TAC ‘n’ >> MATCH_MP_TAC normal_real \\
        ‘variance p (Z (SUC n)) <> NegInf’ by METIS_TAC [variance_pos, pos_not_neginf] \\
        ‘variance p (Z (SUC n)) <> PosInf’
           by METIS_TAC [finite_second_moments_eq_finite_variance, lt_infty] \\
        ‘?r. variance p (Z (SUC n)) = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_mul_def]) >> Rewr' \\
     Know ‘!n. Normal (inv (&SUC n) pow 2) = inv (&(SUC n) pow 2)’
     >- (Q.X_GEN_TAC ‘n’ \\
        ‘&(SUC n) <> (0 :real)’ by rw [] \\
        ‘&SUC n * &SUC n <> 0 :real’ by rw [] \\
         ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_inv_def, POW_2, extreal_11,
                              extreal_mul_def, pow_2, REAL_INV_MUL]) >> Rewr' \\
     Know ‘!n. inv (&SUC n pow 2) * variance p (Z (SUC n)) <=
               inv (&SUC n pow 2) *
              (&SUC n * sqrt (&SUC n) * expectation p (abs o X 0) +
               &(SUC n) pow 2 *
               expectation p
                 (\x. abs (X 0 x) *
                      indicator_fn {x | x IN p_space p /\ sqrt (&SUC n) <= abs (X 0 x)} x))’
     >- (Q.X_GEN_TAC ‘n’ \\
         MATCH_MP_TAC le_lmul_imp \\
         CONJ_TAC >- (MATCH_MP_TAC le_inv >> MATCH_MP_TAC pow_pos_lt \\
                      rw [extreal_of_num_def, extreal_lt_eq]) \\
         MATCH_MP_TAC le_trans \\
         Q.EXISTS_TAC ‘SIGMA (\i. expectation p (\x. Y i x pow 2)) (count (SUC n))’ >> art []) \\
  (* applying add_ldistrib_pos *)
     Know ‘!n. inv (&SUC n pow 2) *
              (&SUC n * sqrt (&SUC n) * expectation p (abs o X 0) +
               &SUC n pow 2 *
               expectation p
                 (\x. abs (X 0 x) *
                      indicator_fn {x | x IN p_space p /\ sqrt (&SUC n) <= abs (X 0 x)} x)) =
               inv (&SUC n pow 2) * (&SUC n * sqrt (&SUC n) * expectation p (abs o X 0)) +
               inv (&SUC n pow 2) *
              (&SUC n pow 2 *
               expectation p
                 (\x. abs (X 0 x) *
                      indicator_fn {x | x IN p_space p /\ sqrt (&SUC n) <= abs (X 0 x)} x))’
     >- (Q.X_GEN_TAC ‘n’ \\
         MATCH_MP_TAC add_ldistrib_pos \\
         CONJ_TAC >- (MATCH_MP_TAC le_mul \\
                      reverse CONJ_TAC >- (MATCH_MP_TAC expectation_pos >> rw [abs_pos]) \\
                      MATCH_MP_TAC le_mul \\
                      CONJ_TAC >- (rw [extreal_of_num_def, extreal_le_eq]) \\
                      MATCH_MP_TAC sqrt_pos_le \\
                      rw [extreal_of_num_def, extreal_le_eq]) \\
         MATCH_MP_TAC le_mul >> art [le_pow2] \\
         MATCH_MP_TAC expectation_pos >> rw [] \\
         MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS]) >> Rewr' \\
     REWRITE_TAC [mul_assoc] \\
     Know ‘!n. inv (&SUC n pow 2) * &SUC n pow 2 = 1’
     >- (Q.X_GEN_TAC ‘n’ >> MATCH_MP_TAC mul_linv_pos \\
         CONJ_TAC >- (MATCH_MP_TAC pow_pos_lt \\
                      rw [extreal_of_num_def, extreal_lt_eq]) \\
         rw [pow_2, extreal_of_num_def, extreal_mul_def]) >> Rewr' \\
     REWRITE_TAC [mul_lone] \\
     Know ‘!n. inv (&SUC n pow 2) * &SUC n * sqrt (&SUC n) = inv (sqrt (&SUC n))’
     >- (Q.X_GEN_TAC ‘n’ \\
         Know ‘(inv (&SUC n pow 2) * &SUC n * sqrt (&SUC n) = inv (sqrt (&SUC n))) <=>
               ((inv (&SUC n pow 2) * &SUC n * sqrt (&SUC n)) pow 2 =
                (inv (sqrt (&SUC n))) pow 2)’
         >- (MATCH_MP_TAC pow_eq >> rw [GSYM ne_02] >| (* 2 subgoals *)
             [ (* goal 1 (of 2) *)
               MATCH_MP_TAC le_mul \\
               reverse CONJ_TAC >- (MATCH_MP_TAC sqrt_pos_le \\
                                    rw [extreal_of_num_def, extreal_le_eq]) \\
               MATCH_MP_TAC le_mul \\
               reverse CONJ_TAC >- (rw [extreal_of_num_def, extreal_le_eq]) \\
               MATCH_MP_TAC le_inv >> MATCH_MP_TAC pow_pos_lt \\
               rw [extreal_of_num_def, extreal_lt_eq],
               (* goal 2 (of 2) *)
               MATCH_MP_TAC le_inv >> MATCH_MP_TAC sqrt_pos_lt \\
               rw [extreal_of_num_def, extreal_lt_eq] ]) >> Rewr' \\
         Know ‘inv (sqrt (&SUC n)) pow 2 = inv (sqrt (&SUC n) pow 2)’
         >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
             MATCH_MP_TAC pow_inv \\
             MATCH_MP_TAC sqrt_pos_ne \\
             rw [extreal_of_num_def, extreal_lt_eq]) >> Rewr' \\
        ‘sqrt (&SUC n) pow 2 = &SUC n’
           by (rw [sqrt_pow2, extreal_of_num_def, extreal_le_eq]) >> POP_ORW \\
         Know ‘inv (&SUC n pow 2) = inv (&SUC n) * inv (&SUC n)’
         >- (REWRITE_TAC [pow_2] \\
             MATCH_MP_TAC inv_mul >> rw [extreal_of_num_def]) >> Rewr' \\
        ‘inv (&SUC n) * inv (&SUC n) * &SUC n * sqrt (&SUC n) =
         inv (&SUC n) * (inv (&SUC n) * &SUC n) * sqrt (&SUC n)’
           by METIS_TAC [mul_assoc] >> POP_ORW \\
         Know ‘inv (&SUC n) * &SUC n = 1’
         >- (MATCH_MP_TAC mul_linv_pos \\
             rw [extreal_of_num_def, extreal_lt_eq]) >> Rewr' \\
         REWRITE_TAC [mul_rone] \\
         REWRITE_TAC [pow_mul] (* cannot merge to previous tactic *) \\
        ‘sqrt (&SUC n) pow 2 = &SUC n’
           by (rw [sqrt_pow2, extreal_of_num_def, extreal_le_eq]) >> POP_ORW \\
         REWRITE_TAC [pow_2, GSYM mul_assoc] \\
         Know ‘inv (&SUC n) * &SUC n = 1’
         >- (MATCH_MP_TAC mul_linv_pos \\
             rw [extreal_of_num_def, extreal_lt_eq]) >> Rewr' \\
         REWRITE_TAC [mul_rone]) >> Rewr' >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘!n. variance p (Z n) <= _’ K_TAC \\
     Q.PAT_X_ASSUM ‘!n. SIGMA (\i. expectation p (\x. Y i x pow 2)) (count n) <= _’ K_TAC \\
     Know ‘expectation p (abs o X 0) <> PosInf /\
           expectation p (abs o X 0) <> NegInf’
     >- (REWRITE_TAC [expectation_def] \\
         MATCH_MP_TAC integrable_finite_integral \\
         FULL_SIMP_TAC std_ss [prob_space_def] \\
         MATCH_MP_TAC integrable_abs >> art []) >> DISCH_TAC \\
     Q.ABBREV_TAC ‘E = Normal e’ \\
     Know ‘?N. !n. N <= n ==> realinv (sqrt (&SUC n)) * expectation p (abs o X 0) < E / 2’
     >- (‘?r. expectation p (abs o X 0) = Normal r’ by METIS_TAC [extreal_cases] \\
         Know ‘0 <= r’
         >- (REWRITE_TAC [GSYM extreal_le_eq, GSYM extreal_of_num_def] \\
             POP_ASSUM (ONCE_REWRITE_TAC o wrap o (MATCH_MP EQ_SYM)) \\
             MATCH_MP_TAC expectation_pos >> rw [abs_pos, o_DEF]) >> DISCH_TAC \\
         Know ‘E / 2 = Normal (1 / 2 * e)’
         >- (rw [Abbr ‘E’, ne_02, extreal_div_eq, extreal_of_num_def]) >> Rewr' \\
         Q.EXISTS_TAC ‘clg ((inv (1 / 2 * e) * r) pow 2)’ >> RW_TAC std_ss [] \\
         Know ‘(realinv (1 / 2 * e) * r) pow 2 < &SUC n’
         >- (MATCH_MP_TAC REAL_LET_TRANS \\
             Q.EXISTS_TAC ‘&n’ >> reverse CONJ_TAC >- rw [] \\
             MATCH_MP_TAC REAL_LE_TRANS \\
             Q.EXISTS_TAC ‘&clg ((realinv (1 / 2 * e) * r) pow 2)’ \\
             rw [LE_NUM_CEILING]) >> DISCH_TAC \\
         Know ‘sqrt (&SUC n) <> (0 :real)’
         >- (MATCH_MP_TAC SQRT_POS_NE >> rw []) >> DISCH_TAC \\
         Q.PAT_X_ASSUM ‘(inv (1 / 2 * e) * r) pow 2 < &SUC n’ MP_TAC \\
         rw [extreal_of_num_def, extreal_sqrt_def, extreal_inv_eq,
             extreal_mul_def, extreal_lt_eq] \\
         Q.PAT_X_ASSUM ‘clg ((inv (1 / 2 * e) * r) pow 2) <= n’ K_TAC \\
         Know ‘sqrt ((2 * (inv e * r)) pow 2) < sqrt (&SUC n)’
         >- (MATCH_MP_TAC SQRT_MONO_LT >> rw []) \\
        ‘e <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] \\
         Know ‘sqrt ((2 * (inv e * r)) pow 2) = 2 * (inv e * r)’
         >- (MATCH_MP_TAC POW_2_SQRT >> rw []) >> Rewr' >> DISCH_TAC \\
         Q.PAT_X_ASSUM ‘(2 * (inv e * r)) pow 2 < &SUC n’ K_TAC \\
         Q.ABBREV_TAC ‘(z :real) = sqrt (&SUC n)’ \\
         Cases_on ‘r = 0’ >- rw [] \\
        ‘0 < r’ by METIS_TAC [REAL_LE_LT] \\
         Know ‘2 * (r * inv z) < e <=> inv e < inv (2 * (r * inv z))’
         >- (MATCH_MP_TAC (GSYM REAL_INV_LT_ANTIMONO) >> rw [] \\
             MATCH_MP_TAC REAL_LT_MUL >> art [] \\
             MATCH_MP_TAC REAL_INV_POS >> Q.UNABBREV_TAC ‘z’ \\
             MATCH_MP_TAC SQRT_POS_LT >> rw []) >> Rewr' \\
         Q.ABBREV_TAC ‘e' = inv e’ \\
         rw [REAL_INV_INV, REAL_INV_MUL]) >> STRIP_TAC \\
  (* applying lebesgue_monotone_convergence_decreasing *)
     Know ‘inf (IMAGE (\n. expectation p
                             (\x. abs (X 0 x) *
                                  indicator_fn
                                    {x | x IN p_space p /\ sqrt (&SUC n) <= abs (X 0 x)} x))
                      univ(:num)) = pos_fn_integral p (\x. 0)’
     >- (REWRITE_TAC [Once EQ_SYM_EQ, expectation_def] \\
         FULL_SIMP_TAC std_ss [prob_space_def] \\
         Know ‘!n. integral p
                     (\x. abs (X 0 x) *
                          indicator_fn
                            {x | x IN p_space p /\ sqrt (&SUC n) <= abs (X 0 x)} x) =
                   pos_fn_integral p
                     (\x. abs (X 0 x) *
                          indicator_fn
                            {x | x IN p_space p /\ sqrt (&SUC n) <= abs (X 0 x)} x)’
         >- (Q.X_GEN_TAC ‘n’ \\
             MATCH_MP_TAC integral_pos_fn >> RW_TAC std_ss [] \\
             MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS]) >> Rewr' \\
         Q.PAT_X_ASSUM ‘!n. real_random_variable (X n) p’
           (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
            (REWRITE_RULE [real_random_variable, p_space_def, events_def])) \\
        ‘sigma_algebra (m_space p,measurable_sets p)’ by METIS_TAC [measure_space_def] \\
         HO_MATCH_MP_TAC lebesgue_monotone_convergence_decreasing \\
         ASM_SIMP_TAC std_ss [p_space_def] \\
         CONJ_TAC (* Borel_measurable *)
         >- (Q.X_GEN_TAC ‘n’ \\
             HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR >> art [subsets_def] \\
             STRONG_CONJ_TAC
             >- (MATCH_MP_TAC (REWRITE_RULE [o_DEF] IN_MEASURABLE_BOREL_ABS') >> art []) \\
             DISCH_TAC \\
            ‘{x | x IN m_space p /\ sqrt (&SUC n) <= abs (X 0 x)} =
             {x | sqrt (&SUC n) <= abs (X 0 x)} INTER m_space p’ by SET_TAC [] \\
             METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) \\
         CONJ_TAC (* 0 <= ... <= PosInf *)
         >- (rpt GEN_TAC >> DISCH_TAC >> CONJ_TAC
             >- (MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS]) \\
            ‘?r. X 0 x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
            ‘?z. indicator_fn {x' | x' IN m_space p /\ sqrt (&SUC n) <= abs (X 0 x')} x = Normal z’
                by METIS_TAC [extreal_cases, INDICATOR_FN_NOT_INFTY] >> POP_ORW \\
             rw [GSYM lt_infty, extreal_abs_def, extreal_mul_def]) \\
         CONJ_TAC (* pos_fn_integral p <> PosInf *)
         >- (rw [lt_infty] >> MATCH_MP_TAC let_trans \\
             Q.EXISTS_TAC ‘pos_fn_integral p (abs o X 0)’ \\
             CONJ_TAC
             >- (MATCH_MP_TAC pos_fn_integral_mono \\
                 rw [o_DEF] >- (MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS]) \\
                 GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM mul_rone] \\
                 MATCH_MP_TAC le_lmul_imp >> rw [abs_pos, INDICATOR_FN_LE_1]) \\
             Know ‘pos_fn_integral p (abs o X 0) = integral p (abs o X 0)’
             >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
                 MATCH_MP_TAC integral_pos_fn >> rw [abs_pos]) >> Rewr' \\
             rw [GSYM expectation_def, GSYM lt_infty]) \\
         CONJ_TAC (* mono_decreasing *)
         >- (rw [ext_mono_decreasing_def] \\
             MATCH_MP_TAC le_lmul_imp >> rw [abs_pos] \\
             MATCH_MP_TAC INDICATOR_FN_MONO >> simp [SUBSET_DEF] \\
             Q.X_GEN_TAC ‘y’ >> rw [] \\
             MATCH_MP_TAC le_trans >> Q.EXISTS_TAC ‘sqrt (&SUC n')’ >> art [] \\
             MATCH_MP_TAC sqrt_mono_le >> rw [extreal_of_num_def, extreal_le_eq]) \\
      (* applying inf_eq' *)
         rw [inf_eq'] >- (MATCH_MP_TAC le_mul >> rw [abs_pos, INDICATOR_FN_POS]) \\
         Q.PAT_X_ASSUM ‘!n. N <= n ==> _’ K_TAC \\
         Q.PAT_X_ASSUM ‘0 < e’            K_TAC \\
         Q.UNABBREV_TAC ‘E’ \\
         Q.PAT_X_ASSUM ‘!n. inv (&SUC n pow 2) * variance p (Z (SUC n)) <= _’ K_TAC \\
         POP_ASSUM MATCH_MP_TAC \\
      (* now estimate ‘n’ such that ‘abs (X 0 x) < sqrt (&SUC n)’ *)
         MP_TAC (Q.SPEC ‘(abs ((X :num -> 'a -> extreal) 0 x)) pow 2’ SIMP_EXTREAL_ARCH) \\
         Know ‘abs (X 0 x) pow 2 <> PosInf’
         >- (‘?r. X 0 x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
             rw [extreal_abs_def, extreal_pow_def]) \\
         RW_TAC std_ss [] \\
         Q.EXISTS_TAC ‘n’ >> rw [indicator_fn_def] \\
         Know ‘sqrt (&SUC n) pow 2 <= abs (X 0 x) pow 2’
         >- (MATCH_MP_TAC pow_le >> art []) \\
         Know ‘sqrt (&SUC n) pow 2 = &SUC n’
         >- (rw [sqrt_pow2, extreal_of_num_def, extreal_le_eq]) >> Rewr' >> DISCH_TAC \\
         Know ‘&SUC n <= &n’ >- METIS_TAC [le_trans] \\
         rw [extreal_of_num_def, extreal_le_eq]) \\
     Know ‘pos_fn_integral p (\x. 0) = 0’
     >- (MATCH_MP_TAC pos_fn_integral_zero \\
         FULL_SIMP_TAC std_ss [prob_space_def]) >> Rewr' \\
     DISCH_TAC \\
  (* applying lt_inf_epsilon' *)
     MP_TAC (Q.SPECL [‘IMAGE
                         (\n. expectation p
                                (\x. abs ((X :num -> 'a -> extreal) 0 x) *
                                     indicator_fn
                                       {x | x IN p_space p /\ sqrt (&SUC n) <= abs (X 0 x)} x))
                       univ(:num)’, ‘E / 2’] lt_inf_epsilon') >> POP_ORW \\
    ‘0 < E / 2’ by (rw [Abbr ‘E’, ne_02, extreal_div_eq, extreal_of_num_def, extreal_lt_eq]) \\
     POP_ASSUM (REWRITE_TAC o wrap) \\
    ‘0 <> NegInf’ by (rw [extreal_of_num_def]) \\
     POP_ASSUM (REWRITE_TAC o wrap) \\
     Know ‘?x. x IN IMAGE (\n. expectation p
                                 (\x. abs (X 0 x) *
                                      indicator_fn
                                        {x | x IN p_space p /\ sqrt (&SUC n) <= abs (X 0 x)} x))
                    univ(:num) /\ x <> PosInf’
     >- (rw [lt_infty] \\
         Q.EXISTS_TAC ‘expectation p
                         (\x. abs (X 0 x) *
                              indicator_fn
                                {x | x IN p_space p /\ sqrt (&SUC 0) <= abs (X 0 x)} x)’ \\
         CONJ_TAC >- (Q.EXISTS_TAC ‘0’ >> REWRITE_TAC []) \\
         MATCH_MP_TAC let_trans \\
         Q.EXISTS_TAC ‘expectation p (abs o X 0)’ >> art [] \\
         rw [expectation_def, o_DEF, p_space_def] \\
         MATCH_MP_TAC integral_mono \\
         FULL_SIMP_TAC std_ss [prob_space_def] \\
         Q.PAT_X_ASSUM ‘!n. real_random_variable (X n) p’
           (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
            (REWRITE_RULE [real_random_variable, p_space_def, events_def])) \\
         CONJ_TAC (* integrable *)
         >- (HO_MATCH_MP_TAC integrable_mul_indicator >> art [] \\
             STRONG_CONJ_TAC
             >- (REWRITE_TAC [le_abs_bounds] \\
                ‘{x | x IN m_space p /\ (X 0 x <= -sqrt 1 \/ sqrt 1 <= X 0 x)} =
                   ({x | X 0 x <= -sqrt 1} INTER m_space p) UNION
                   ({x | sqrt 1 <= X 0 x} INTER m_space p)’ by SET_TAC [] >> POP_ORW \\
                 MATCH_MP_TAC MEASURE_SPACE_UNION >> art [] \\
                 METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC \\
             CONJ_TAC (* measure < PosInf *)
             >- (MATCH_MP_TAC let_trans \\
                 Q.EXISTS_TAC ‘measure p (m_space p)’ \\
                 reverse CONJ_TAC >- (rw [GSYM lt_infty, extreal_of_num_def]) \\
                 MATCH_MP_TAC INCREASING >> rw [MEASURE_SPACE_SPACE]
                 >- (MATCH_MP_TAC MEASURE_SPACE_INCREASING >> art []) \\
                 rw [SUBSET_DEF]) \\
             CONJ_TAC (* abs <> PosInf /\ abs <> NegInf *)
             >- (NTAC 2 STRIP_TAC >> METIS_TAC [abs_not_infty]) \\
             MATCH_MP_TAC (REWRITE_RULE [o_DEF] integrable_abs) >> art []) \\
         CONJ_TAC >- (MATCH_MP_TAC (REWRITE_RULE [o_DEF] integrable_abs) >> art []) \\
         rpt STRIP_TAC \\
         GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM mul_rone] \\
         MATCH_MP_TAC le_lmul_imp >> rw [abs_pos, INDICATOR_FN_LE_1]) \\
     RW_TAC std_ss [add_lzero] >> rename1 ‘y < E / 2’ \\
     Q.PAT_X_ASSUM ‘y IN
                      IMAGE (\n. expectation p
                                   (\x. abs (X 0 x) *
                                        indicator_fn
                                          {x | x IN p_space p /\ sqrt (&SUC n) <= abs (X 0 x)} x))
                            univ(:num)’ MP_TAC \\
     Q.PAT_X_ASSUM ‘x IN
                      IMAGE (\n. expectation p
                                   (\x. abs (X 0 x) *
                                        indicator_fn
                                          {x | x IN p_space p /\ sqrt (&SUC n) <= abs (X 0 x)} x))
                            univ(:num)’ K_TAC \\
     Q.PAT_X_ASSUM ‘x <> PosInf’ K_TAC \\
     rw [IN_IMAGE] (* this asserts ‘n’ *) \\
  (* stage work *)
     Q.EXISTS_TAC ‘MAX N n’ \\
     Q.X_GEN_TAC ‘M’ >> RW_TAC std_ss [MAX_LE] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘inv (sqrt (&SUC M)) * expectation p (abs o X 0) +
                   expectation p
                     (\x. abs (X 0 x) *
                          indicator_fn
                            {x | x IN p_space p /\ sqrt (&SUC M) <= abs (X 0 x)} x)’ >> art [] \\
     Suff ‘inv (sqrt (&SUC M)) * expectation p (abs o X 0) < E / 2 /\
           expectation p
             (\x. abs (X 0 x) *
                  indicator_fn
                    {x | x IN p_space p /\ sqrt (&SUC M) <= abs (X 0 x)} x) < E / 2’
     >- (STRIP_TAC \\
        ‘E = E / 2 + E / 2’ by REWRITE_TAC [half_double] >> POP_ORW \\
         MATCH_MP_TAC lt_add2 >> art []) \\
     CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘expectation p
                     (\x. abs (X 0 x) *
                          indicator_fn
                            {x | x IN p_space p /\ sqrt (&SUC n) <= abs (X 0 x)} x)’ >> art [] \\
     FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, expectation_def] \\
     MATCH_MP_TAC integral_mono >> art [] \\
     Q.PAT_X_ASSUM ‘!n. real_random_variable (X n) p’
       (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
        (REWRITE_RULE [real_random_variable, p_space_def, events_def])) \\
     Know ‘!n. integrable p
                 (\x. abs (X 0 x) *
                      indicator_fn {x | x IN m_space p /\ sqrt (&SUC n) <= abs (X 0 x)} x)’
     >- (Q.X_GEN_TAC ‘i’ \\
         HO_MATCH_MP_TAC integrable_mul_indicator >> art [] \\
         STRONG_CONJ_TAC
         >- (REWRITE_TAC [le_abs_bounds] \\
            ‘{x | x IN m_space p /\ (X 0 x <= -sqrt (&SUC i) \/ sqrt (&SUC i) <= X 0 x)} =
               ({x | X 0 x <= -sqrt (&SUC i)} INTER m_space p) UNION
               ({x | sqrt (&SUC i) <= X 0 x} INTER m_space p)’ by SET_TAC [] >> POP_ORW \\
             MATCH_MP_TAC MEASURE_SPACE_UNION >> art [] \\
             METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC \\
         CONJ_TAC (* measure < PosInf *)
         >- (MATCH_MP_TAC let_trans \\
             Q.EXISTS_TAC ‘measure p (m_space p)’ \\
             reverse CONJ_TAC >- (rw [GSYM lt_infty, extreal_of_num_def]) \\
             MATCH_MP_TAC INCREASING >> rw [MEASURE_SPACE_SPACE]
             >- (MATCH_MP_TAC MEASURE_SPACE_INCREASING >> art []) \\
             rw [SUBSET_DEF]) \\
         CONJ_TAC (* abs <> PosInf /\ abs <> NegInf *)
         >- (NTAC 2 STRIP_TAC >> METIS_TAC [abs_not_infty]) \\
         MATCH_MP_TAC (REWRITE_RULE [o_DEF] integrable_abs) >> art []) >> Rewr \\
     RW_TAC std_ss [] \\
     MATCH_MP_TAC le_lmul_imp >> REWRITE_TAC [abs_pos] \\
     MATCH_MP_TAC INDICATOR_FN_MONO \\
     simp [SUBSET_DEF] >> Q.X_GEN_TAC ‘y’ >> STRIP_TAC \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC ‘sqrt (&SUC M)’ >> art [] \\
     MATCH_MP_TAC sqrt_mono_le >> rw [extreal_of_num_def, extreal_le_eq])
 (* cleanup used assumptions (22 left) *)
 >> Q.PAT_X_ASSUM ‘!n c. _ IN events p’                   K_TAC
 >> Q.PAT_X_ASSUM ‘!n. variance p (Z n) <= _’             K_TAC
 >> Q.PAT_X_ASSUM ‘!i. 0 <= sqrt (&i) /\ sqrt (&i) <= &i’ K_TAC
 >> Q.PAT_X_ASSUM ‘!n. SIGMA (\i. expectation p (\x. Y i x pow 2)) (count n) <= _’ K_TAC
 >> Know ‘((\n x. (Z (SUC n) x - M (SUC n)) / &SUC n) --> (\x. 0))
           (in_probability p) <=>
          ((\n x. (Z (SUC n) x / &SUC n - M (SUC n) / &SUC n)) --> (\x. 0))
           (in_probability p)’
 >- (MATCH_MP_TAC converge_PR_cong \\
     Q.EXISTS_TAC ‘0’ >> rw [Once EQ_SYM_EQ] \\
     MATCH_MP_TAC div_sub >> rw [extreal_of_num_def]) >> Rewr'
 >> DISCH_TAC
 (* applying converge_PR_to_limit *)
 >> ‘m <> PosInf /\ m <> NegInf’ by METIS_TAC [expectation_finite]
 >> MATCH_MP_TAC converge_PR_to_limit'
 >> Q.EXISTS_TAC ‘\n. M (SUC n) / &SUC n’ >> simp [o_DEF]
 >> CONJ_TAC (* real_random_variable *)
 >- (rw [extreal_of_num_def] \\
     Know ‘real_random_variable (\x. Z (SUC n) x / Normal (&SUC n)) p <=>
           real_random_variable (\x. inv (Normal (&SUC n)) * Z (SUC n) x) p’
     >- (MATCH_MP_TAC real_random_variable_cong >> rw [] \\
         MATCH_MP_TAC div_eq_mul_linv \\
         rw [extreal_of_num_def, extreal_lt_eq]) >> Rewr' \\
    ‘&SUC n <> (0 :real)’ by rw [] >> rw [extreal_inv_eq] \\
     MATCH_MP_TAC real_random_variable_cmul >> art [])
 >> CONJ_TAC (* M <> PosInf /\ M <> NegInf *)
 >- (Q.X_GEN_TAC ‘n’ \\
    ‘?r. M (SUC n) = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘&SUC n <> (0 :extreal)’ by rw [extreal_of_num_def] \\
     rw [div_not_infty])
 (* final: applying truncated_vars_expectation' *)
 >> SIMP_TAC std_ss [Abbr ‘M’, Abbr ‘Z’, Abbr ‘Y’, Abbr ‘m’]
 >> MATCH_MP_TAC truncated_vars_expectation' >> art []
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
  [9] Schilling, R.L.: Measures, Integrals and Martingales (Second Edition).
      Cambridge University Press (2017).
 [12] Etemadi, N.: An elementary proof of the strong law of large numbers.
      Z. Wahrsch. Verw. Gebiete. 55, 119-122 (1981).
 [13] Gnedenko, B.V., Kolmogorov, A.N.: Limit distributions for sums of independent random
      variables. Addison-Wesley Publishing Company, Inc., Cambridge, MA (1954).
 [14] Levy, P.: Theorie de L'addition des Variables Aleatoires. Gauthier-Villars, Paris (1937).
 [15] Nagaev, S.V.: On Necessary and Sufficient Conditions for the Strong Law of Large Numbers.
      Theory Probab. Appl. 17 (4), 573-581 (1973).
 *)
