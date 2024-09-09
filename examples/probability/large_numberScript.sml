(* ========================================================================= *)
(* The Laws of Large Numbers (for Uncorrelated and I.I.D. Random Variables)  *)
(*                                                                           *)
(* Author: Chun Tian (binghe) <binghe.lisp@gmail.com> (2020 - 2023)          *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open combinTheory arithmeticTheory pred_setTheory pred_setLib logrootTheory
     numLib hurdUtils topologyTheory;

open realTheory realLib seqTheory transcTheory real_sigmaTheory iterateTheory
     real_topologyTheory metricTheory;

open util_probTheory sigma_algebraTheory extrealTheory measureTheory
     borelTheory lebesgueTheory martingaleTheory probabilityTheory;

val _ = new_theory "large_number";

(* An unintended overload/abbreviation from pred_setTheory *)
val _ = temp_clear_overloads_on "equiv_class";

(* "In the formal construction of a course in the theory of probability, limit
    theorems appear as a kind of superstructure over elementary chapters, in
    which all problems have finite, purely arithmetical character. In reality,
    however, the epistemological value of the theory of probability is revealed
    only by limit theorems. Moreover, without limit theorems it is impossible
    to understand the real content of the primary concept of all our sciences -
    the concept of probability... The very concept of mathematical probability
    would be fruitless if it did not find its realization in the frequency of
    occurrence of events under large-scale repetition of uniform conditions."

  -- B.V. Gnedenko and A.N. Kolmogorov,
    "Limit distributions for sums of independent random variables." [13] *)

val PRINT_TAC = goalStack.print_tac;
val set_ss = std_ss ++ PRED_SET_ss;

val _ = hide "S";
val _ = hide "W";

val _ = intLib.deprecate_int ();
val _ = ratLib.deprecate_rat ();

(* Prefer NUM_FLOOR and NUM_CEILING (over INT_FLOOR/INT_CEILING) by redefining
   their overloads.
 *)
Overload flr = “realax$NUM_FLOOR”
Overload clg = “realax$NUM_CEILING”

(* ------------------------------------------------------------------------- *)
(*  Definitions                                                              *)
(* ------------------------------------------------------------------------- *)

(* Law of Large Numbers: the universal conclusion for all LLN theorems

   NOTE: changed ‘Z’ such that Z(0) = X(0), Z(1) = X(0) + X(1), ...
 *)
Definition LLN_def :
    LLN p X convergence_mode =
    let Z n x = SIGMA (\i. X i x) (count1 n) in
      ((\n x. (Z n x - expectation p (Z n)) / &SUC n) --> (\x. 0))
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

Definition pow_seq_def :
    pow_seq a n = flr (a pow n)
End

(* ------------------------------------------------------------------------- *)
(*  Theorems                                                                 *)
(* ------------------------------------------------------------------------- *)

Theorem real_random_variable_LLN_general :
    !p X Z b. prob_space p /\
             (!n. real_random_variable (X n) p) /\ (!n. integrable p (X n)) /\
             (!n x. x IN p_space p ==> Z n x = SIGMA (\i. X i x) (count n)) /\
             (!n :num. 0 < b n)
          ==> !n. real_random_variable
                    (\x. (Z (b n) x - expectation p (Z (b n))) / &(b n)) p
Proof
    rpt STRIP_TAC
 (* redefine Z as an abbreviation *)
 >> Q.ABBREV_TAC ‘S = \n x. SIGMA (\i. X i x) (count n)’
 >> Know ‘expectation p (Z (b n)) = expectation p (S (b n))’
 >- (MATCH_MP_TAC expectation_cong >> rw [Abbr ‘S’]) >> Rewr'
 >> Q.ABBREV_TAC ‘M = \n. expectation p (S n)’ >> simp []
 >> Know ‘real_random_variable (\x. (Z (b n) x - M (b n)) / &(b n)) p <=>
          real_random_variable (\x. (S (b n) x - M (b n)) / &(b n)) p’
 >- (MATCH_MP_TAC real_random_variable_cong >> rw [Abbr ‘S’]) >> Rewr'
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
                S (b n) x - M (b n) <> PosInf /\ S (b n) x - M (b n) <> NegInf’
 >- (rpt GEN_TAC >> DISCH_TAC \\
    ‘?r. S (b n) x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?z. M (b n) = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def])
 >> DISCH_TAC
 >> Know ‘!n x. x IN p_space p ==>
               (S (b n) x - M (b n)) / &(b n) = inv (&b n) * (S (b n) x - M (b n))’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC div_eq_mul_linv \\
    ‘?r. S (b n) x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?z. M (b n) = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def, extreal_lt_eq, extreal_of_num_def])
 >> DISCH_TAC
 >> Know ‘real_random_variable (\x. (S (b n) x - M (b n)) / &(b n)) p <=>
          real_random_variable (\x. inv (&b n) * (S (b n) x - M (b n))) p’
 >- (MATCH_MP_TAC real_random_variable_cong \\
     RW_TAC std_ss []) >> Rewr'
 >> Know ‘inv (&b n) = Normal (inv &(b n))’
 >- (‘(0 :real) < &b n’ by RW_TAC real_ss [] \\
     ‘&b n <> (0 :real)’ by PROVE_TAC [REAL_LT_IMP_NE] \\
     rw [extreal_of_num_def, extreal_inv_eq])
 >> Rewr'
 >> ‘sigma_algebra (p_space p,events p)’
       by METIS_TAC [prob_space_def, measure_space_def, p_space_def, events_def]
 >> SIMP_TAC std_ss [real_random_variable]
 >> reverse CONJ_TAC
 >- (Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
    ‘?r. S (b n) x - M (b n) = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_mul_def])
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
 >> qexistsl_tac [`\x. S (b n) x - M (b n)`, `inv &(b n)`] >> rw []
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB
 >> qexistsl_tac [`S (b n)`, `\x. M (b n)`] >> rw []
 >| [ (* goal 1 (of 2) *)
      Q.UNABBREV_TAC ‘S’ \\
      MATCH_MP_TAC (INST_TYPE [``:'b`` |-> ``:num``] IN_MEASURABLE_BOREL_SUM) \\
      qexistsl_tac [`X`, `count (b n)`] >> rw [] \\
      FULL_SIMP_TAC std_ss [random_variable_def],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST' >> art [] ]
QED

Theorem real_random_variable_LLN :
    !p X Z. prob_space p /\
           (!n. real_random_variable (X n) p) /\
           (!n. integrable p (X n)) /\
           (!n x. x IN p_space p ==> Z n x = SIGMA (\i. X i x) (count1 n)) ==>
           (!n. real_random_variable
                  (\x. (Z n x - expectation p (Z n)) / &SUC n) p)
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘Y = \n x. SIGMA (\i. X i x) (count n)’
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘Y’, ‘SUC’] real_random_variable_LLN_general)
 >> simp [Abbr ‘Y’]
 >> DISCH_THEN (ASSUME_TAC o (Q.SPEC ‘n’))
 >> Suff ‘real_random_variable (\x. (Z n x - expectation p (Z n)) / &SUC n) p <=>
          real_random_variable
            (\x. (SIGMA (\i. X i x) (count1 n) - expectation p (\x. SIGMA (\i. X i x) (count1 n))) /
                 &SUC n) p’ >- rw []
 >> MATCH_MP_TAC real_random_variable_cong >> rw []
 >> Suff ‘expectation p (Z n) = expectation p (\x. SIGMA (\i. X i x) (count1 n))’ >- rw []
 >> MATCH_MP_TAC expectation_cong >> rw []
QED

(* NOTE: removed the unnecessary antecedent ‘!n. integrable p (X n)’ *)
Theorem real_random_variable_LLN_general' :
    !p X b. prob_space p /\ (!n. real_random_variable (X n) p) /\ (!n :num. 0 < b n)
        ==> !n. real_random_variable (\x. SIGMA (\i. X i x) (count (b n)) / &(b n)) p
Proof
    rpt STRIP_TAC
 (* redefine Z as an abbreviation *)
 >> Q.ABBREV_TAC ‘S = \n x. SIGMA (\i. X i x) (count n)’
 >> simp []
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
 >> Know ‘!n x. x IN p_space p ==>
                S (b n) x / &(b n) = inv (&b n) * S (b n) x’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC div_eq_mul_linv \\
    ‘?r. S (b n) x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def, extreal_lt_eq, extreal_of_num_def])
 >> DISCH_TAC
 >> Know ‘real_random_variable (\x. S (b n) x / &(b n)) p <=>
          real_random_variable (\x. inv (&b n) * S (b n) x) p’
 >- (MATCH_MP_TAC real_random_variable_cong \\
     RW_TAC std_ss []) >> Rewr'
 >> Know ‘inv (&b n) = Normal (inv &(b n))’
 >- (‘(0 :real) < &b n’ by RW_TAC real_ss [] \\
     ‘&b n <> (0 :real)’ by PROVE_TAC [REAL_LT_IMP_NE] \\
     rw [extreal_of_num_def, extreal_inv_eq])
 >> Rewr'
 >> ‘sigma_algebra (p_space p,events p)’
       by METIS_TAC [prob_space_def, measure_space_def, p_space_def, events_def]
 >> SIMP_TAC std_ss [real_random_variable]
 >> reverse CONJ_TAC
 >- (Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
    ‘?r. S (b n) x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_mul_def])
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
 >> qexistsl_tac [`S (b n)`, `inv &(b n)`] >> rw []
 >> Q.UNABBREV_TAC ‘S’
 >> MATCH_MP_TAC (INST_TYPE [``:'b`` |-> ``:num``] IN_MEASURABLE_BOREL_SUM)
 >> qexistsl_tac [`X`, `count (b n)`] >> rw []
 >> FULL_SIMP_TAC std_ss [random_variable_def]
QED

(* A lite version of the previous lemma (needed by SLLN_IID),
   NOTE: removed the unnecessary antecedent ‘!n. integrable p (X n)’
 *)
Theorem real_random_variable_LLN' :
    !p X. prob_space p /\
         (!n. real_random_variable (X n) p) ==>
         (!n. real_random_variable (\x. SIGMA (\i. X i x) (count1 n) / &SUC n) p)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘SUC’] real_random_variable_LLN_general')
 >> rw []
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
 >> Know ‘!n. integrable p (X n)’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC finite_second_moments_imp_integrable >> art [] \\
     ASM_SIMP_TAC std_ss [finite_second_moments_eq_finite_variance] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘c’ >> rw [GSYM lt_infty]) >> DISCH_TAC
 >> Know ‘!n. real_random_variable (Z n) p’
 >- (rw [Abbr ‘Z’] \\
     MATCH_MP_TAC real_random_variable_sum >> rw [])
 >> DISCH_TAC
 >> Know ‘!n. real_random_variable (\x. (Z n x - expectation p (Z n)) / &SUC n) p’
 >- (MATCH_MP_TAC real_random_variable_LLN \\
     Q.EXISTS_TAC ‘X’ >> rw [Abbr ‘Z’])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘M = \n. expectation p (Z n)’
 >> FULL_SIMP_TAC std_ss []
 (* renamed ‘Z’ to ‘S’ *)
 >> rename1 ‘((\n x. (S n x - M n) / &SUC n) --> (\x. 0)) (in_lebesgue 2 p)’
 >> ‘real_random_variable (\x. 0) p’ by PROVE_TAC [real_random_variable_zero]
 >> Q.PAT_X_ASSUM ‘!n. real_random_variable (X n) p’
      (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
       (REWRITE_RULE [real_random_variable_def]))
 >> ‘measure_space p’ by FULL_SIMP_TAC std_ss [prob_space_def]
 >> Know ‘!n. M n <> PosInf /\ M n <> NegInf’
 >- (Q.X_GEN_TAC ‘n’ \\
     ASM_SIMP_TAC std_ss [expectation_def, Abbr ‘M’] \\
     MATCH_MP_TAC integrable_finite_integral >> art [] \\
    ‘S n = \x. SIGMA (\i. X i x) (count1 n)’ by METIS_TAC [] >> POP_ORW \\
     MATCH_MP_TAC integrable_sum \\
     FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, FINITE_COUNT, IN_COUNT])
 >> DISCH_TAC
 >> ‘!n x. x IN p_space p ==> S n x <> PosInf /\ S n x <> NegInf’
       by METIS_TAC [real_random_variable_def]
 >> Know ‘!n x. x IN p_space p ==> S n x - M n <> PosInf /\ S n x - M n <> NegInf’
 >- (qx_genl_tac [‘n’, ‘x’] >> DISCH_TAC \\
    ‘?a. S n x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?b. M n = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def])
 >> DISCH_TAC
 >> Know ‘!n x. x IN p_space p ==> (S n x - M n) / &SUC n = inv (&SUC n) * (S n x - M n)’
 >- (qx_genl_tac [‘n’, ‘x’] >> DISCH_TAC \\
     MATCH_MP_TAC div_eq_mul_linv \\
    `?a. S n x = Normal a` by METIS_TAC [extreal_cases] >> POP_ORW \\
    `?b. M n = Normal b` by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def] \\
     RW_TAC real_ss [extreal_lt_eq, extreal_of_num_def])
 >> DISCH_TAC
 >> Know ‘((\n x. (S n x - M n) / &SUC n)       --> (\x. 0)) (in_lebesgue 2 p) <=>
          ((\n x. inv (&SUC n) * (S n x - M n)) --> (\x. 0)) (in_lebesgue 2 p)’
 >- (MATCH_MP_TAC converge_LP_cong >> rw [])
 >> Rewr'
 >> Know ‘!n. real_random_variable (\x. (S n x - M n) / &SUC n) p <=>
              real_random_variable (\x. inv (&SUC n) * (S n x - M n)) p’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC real_random_variable_cong >> RW_TAC std_ss [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> POP_ASSUM K_TAC (* !n x. x IN p_space p ==> (S (SUC n) x - M (SUC n)) / &SUC n = *)
 >> Know ‘!n. inv (&SUC n) = Normal (inv (&SUC n))’
 >- (Q.X_GEN_TAC ‘n’ \\
    ‘(0 :real) <> &SUC n’ by RW_TAC real_ss [] \\
     ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_inv_eq])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> ‘sigma_algebra (m_space p,measurable_sets p)’
       by METIS_TAC [prob_space_def, measure_space_def]
 >> Q.ABBREV_TAC ‘Z = \n x. Normal (inv (&SUC n)) * (S n x - M n)’
 >> ‘!n. real_random_variable (Z n) p’ by rw [Abbr ‘Z’]
 (* now rewrite the goal *)
 >> ASM_SIMP_TAC std_ss [converge_LP_alt_pow, sub_rzero, abs_0, zero_pow, lt_02, abs_pow2]
 >> REWRITE_TAC [Once CONJ_SYM, GSYM CONJ_ASSOC]
 >> CONJ_TAC >- (REWRITE_TAC [extreal_of_num_def] >> rw [expectation_const])
 (* prove that (S n) has finite second moments *)
 >> Know ‘!n. variance p (S n) <= &SUC n * c’
 >- (Q.X_GEN_TAC ‘n’ \\
     Know ‘variance p (S n) = SIGMA (\n. variance p (X n)) (count1 n)’
     >- (‘S n = \x. SIGMA (\i. X i x) (count1 n)’ by METIS_TAC [] >> POP_ORW \\
         MATCH_MP_TAC variance_sum \\
         RW_TAC std_ss [uncorrelated_vars_def, real_random_variable_def,
                        FINITE_COUNT]) >> Rewr' \\
     Know ‘&CARD (count1 n) * c = SIGMA (\x. c) (count1 n)’
     >- (MATCH_MP_TAC EQ_SYM >> irule EXTREAL_SUM_IMAGE_FINITE_CONST \\
         RW_TAC std_ss [FINITE_COUNT]) \\
     REWRITE_TAC [CARD_COUNT] >> Rewr' \\
     irule EXTREAL_SUM_IMAGE_MONO \\
     RW_TAC std_ss [FINITE_COUNT, IN_COUNT] >> DISJ2_TAC \\
     RW_TAC std_ss [lt_infty] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘c’ >> rw [GSYM lt_infty]) >> DISCH_TAC
 >> Know ‘c <> NegInf’
 >- (MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC ‘variance p (X 0)’ >> art [] \\
     ASM_SIMP_TAC std_ss [variance_pos]) >> DISCH_TAC
 >> ‘!n. variance p (S n) <> NegInf’
       by METIS_TAC [pos_not_neginf, variance_pos]
 >> Know ‘!n. variance p (S n) <> PosInf’
 >- (Q.X_GEN_TAC ‘n’ >> REWRITE_TAC [lt_infty] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘&SUC n * c’ >> art [GSYM lt_infty] \\
    ‘?r. c = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_of_num_def, extreal_mul_def, extreal_not_infty]) >> DISCH_TAC
 >> ‘!n. finite_second_moments p (S n)’
       by (RW_TAC std_ss [finite_second_moments_eq_finite_variance, GSYM lt_infty])
 >> Know ‘!n. expectation p (\x. Z n x pow 2) =
              Normal (inv (&SUC n) pow 2) * variance p (S n)’
 >- (Q.X_GEN_TAC ‘n’ >> SIMP_TAC std_ss [Abbr `Z`, variance_alt] \\
    ‘!n. expectation p (S n) = M n’ by METIS_TAC [] >> POP_ORW \\
     SIMP_TAC std_ss [pow_mul, extreal_pow_def, expectation_def] \\
     HO_MATCH_MP_TAC integral_cmul \\
     CONJ_TAC >- FULL_SIMP_TAC std_ss [prob_space_def] \\
     Know ‘measure_space p /\
           (!x. x IN m_space p ==> 0 <= (\x. (S n x - M n) pow 2) x)’
     >- (fs [le_pow2]) \\
     DISCH_THEN (ONCE_REWRITE_TAC o wrap o (MATCH_MP integrable_pos)) \\
     CONJ_TAC (* Boreal_measurable *)
     >- (HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_POW \\
         HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB' \\
         qexistsl_tac [‘S n’, ‘\x. M n’] \\
         ASM_SIMP_TAC std_ss [space_def] \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST' >> art []) \\
        ‘S n = \x. SIGMA (\i. X i x) (count1 n)’ by METIS_TAC [] >> POP_ORW \\
         MATCH_MP_TAC (INST_TYPE [“:'b” |-> “:num”] IN_MEASURABLE_BOREL_SUM) \\
         qexistsl_tac [‘X’, ‘count1 n’] \\
         RW_TAC std_ss [FINITE_COUNT, IN_COUNT] \\
         fs [random_variable_def, p_space_def, events_def]) \\
     Know ‘pos_fn_integral p (\x. (S n x - M n) pow 2) =
                  integral p (\x. (S n x - M n) pow 2)’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC integral_pos_fn >> fs [prob_space_def, le_pow2]) >> Rewr' \\
     REWRITE_TAC [GSYM expectation_def] \\
    ‘!n. M n = expectation p (S n)’ by METIS_TAC [] >> POP_ORW \\
     ASM_REWRITE_TAC [GSYM variance_alt, GSYM lt_infty]) >> Rewr'
 >> reverse CONJ_TAC
 >- (Q.X_GEN_TAC ‘n’ \\
    ‘?r. variance p (S n) = Normal r’ by METIS_TAC [extreal_cases] \\
     ASM_SIMP_TAC std_ss [extreal_mul_def, extreal_not_infty])
 (* final stage *)
 >> RW_TAC real_ss [LIM_SEQUENTIALLY, dist]
 >> ‘?b. c = Normal b’ by METIS_TAC [extreal_cases]
 >> POP_ASSUM (fn th => fs [th, extreal_of_num_def, extreal_mul_def,
                            extreal_not_infty])
 >> STRIP_ASSUME_TAC (Q.SPEC ‘b / e’ SIMP_REAL_ARCH)
 >> Q.EXISTS_TAC ‘n’
 >> Q.X_GEN_TAC ‘m’ >> DISCH_TAC (* n <= m *)
 >> ‘variance p (S m) <= Normal (b * &SUC m)’ by PROVE_TAC [REAL_MUL_COMM]
 >> ‘?v. variance p (S m) = Normal v’ by METIS_TAC [extreal_cases]
 >> ‘0 <= v’ by METIS_TAC [variance_pos, extreal_of_num_def, extreal_le_eq]
 >> Q.PAT_X_ASSUM ‘_ = Normal v’
      (fn th => fs [th, extreal_of_num_def, extreal_le_eq,
                    extreal_mul_def, real_normal])
 >> Know ‘abs (v * inv (&SUC m) pow 2) = v * inv (&SUC m) pow 2’
 >- (rw [] >> MATCH_MP_TAC REAL_LE_MUL >> art [] \\
     MATCH_MP_TAC POW_POS \\
     MATCH_MP_TAC REAL_LT_IMP_LE \\
     MATCH_MP_TAC REAL_INV_POS >> RW_TAC real_ss []) >> Rewr'
 >> MATCH_MP_TAC REAL_LET_TRANS
 >> Q.EXISTS_TAC ‘b * (&SUC m) * inv (&SUC m) pow 2’
 >> CONJ_TAC
 >- (Know ‘(0 :real) < inv (&SUC m) pow 2’
     >- (MATCH_MP_TAC REAL_POW_LT \\
         MATCH_MP_TAC REAL_INV_POS >> RW_TAC real_ss []) \\
     DISCH_THEN (MP_TAC o (MATCH_MP REAL_LE_RMUL)) >> Rewr' >> art [])
 >> REWRITE_TAC [POW_2]
 >> ‘&n <= &m :real’ by RW_TAC real_ss []
 >> ‘b / e <= &m’ by PROVE_TAC [REAL_LE_TRANS]
 >> ‘b <= e * &m’ by METIS_TAC [REAL_LE_LDIV_EQ, REAL_MUL_COMM]
 >> Know ‘(&SUC m) * inv (&SUC m) = (1 :real)’
 >- (MATCH_MP_TAC REAL_MUL_RINV >> RW_TAC real_ss []) >> DISCH_TAC
 >> REWRITE_TAC [REAL_MUL_ASSOC]
 >> Know ‘b * (&SUC m) * inv (&SUC m) = b’
 >- (ASM_SIMP_TAC real_ss [GSYM REAL_MUL_ASSOC]) >> Rewr'
 >> ONCE_REWRITE_TAC [REAL_MUL_COMM]
 >> Know ‘inv (&SUC m) * b < e <=> (&SUC m) * inv (&SUC m) * b < (&SUC m) * e’
 >- (MATCH_MP_TAC EQ_SYM \\
     ONCE_REWRITE_TAC [GSYM REAL_MUL_ASSOC] \\
     MATCH_MP_TAC REAL_LT_LMUL >> RW_TAC real_ss []) >> Rewr'
 >> POP_ORW
 >> rw [Once REAL_MUL_COMM]
 >> MATCH_MP_TAC REAL_LET_TRANS
 >> Q.EXISTS_TAC ‘e * &m’ >> art []
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
     Q.EXISTS_TAC ‘c’ >> rw [GSYM lt_infty])
 >> Know ‘((\n x. (Z n x - expectation p (Z n)) / &SUC n) -->
            (\x. 0)) (in_lebesgue 2 p) <=> LLN p X (in_lebesgue 2)’
 >- rw [LLN_def] >> Rewr'
 >> MATCH_MP_TAC WLLN_uncorrelated_L2 >> art []
 >> Q.EXISTS_TAC ‘c’ >> RW_TAC std_ss []
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
       (!n x. S n x = SIGMA (\i. X i x) (count1 n)) /\
       (!n. M n = expectation p (S n)) ==>
       ?(Y :num -> 'a -> extreal) W.
           (!n x. x IN p_space p ==> W n x = SIGMA (\i. Y i x) (count1 n)) /\
           (!n x. x IN p_space p ==> S n x - M n = W n x) /\
           (!n. expectation p (Y n) = 0) /\
           (!n. real_random_variable (Y n) p) /\
           (!n. finite_second_moments p (Y n)) /\
           (!n. variance p (Y n) <= c) /\
           (!n. integrable p (Y n)) /\
           (!i j. i <> j ==> orthogonal p (Y i) (Y j))
Proof
    rpt STRIP_TAC
 >> Know ‘!n. finite_second_moments p (X n)’
 >- (RW_TAC std_ss [finite_second_moments_eq_finite_variance] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘c’ >> rw [GSYM lt_infty]) >> DISCH_TAC
 >> Know ‘!n. integrable p (X n)’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC finite_second_moments_imp_integrable >> art [])
 >> DISCH_TAC
 (* ‘Y n’ is centered version of ‘X n’ *)
 >> Q.ABBREV_TAC ‘Y = \n x. X n x - expectation p (X n)’
 >> Know ‘!n. expectation p (Y n) = 0’
 >- (RW_TAC std_ss [Abbr ‘Y’, expectation_def] \\
     fs [real_random_variable_def] \\
    ‘!x. x IN p_space p ==>
         X n x - integral p (X n) = X n x + (\x. -integral p (X n)) x’
       by METIS_TAC [prob_space_def, integrable_finite_integral, extreal_sub_add] \\
     Know ‘integral p (\x. X n x - integral p (X n)) =
           integral p (\x. X n x + (\x. -integral p (X n)) x)’
     >- (MATCH_MP_TAC integral_cong \\
         FULL_SIMP_TAC std_ss [prob_space_def, p_space_def]) >> Rewr' \\
     POP_ASSUM K_TAC \\ (* !x. x IN p_space p ==> X n x - integral p (X n) =  ... *)
     Know ‘integral p (\x. X n x + (\x. -integral p (X n)) x) =
           integral p (X n) + integral p (\x. -integral p (X n))’
     >- (MATCH_MP_TAC integral_add \\
         fs [prob_space_def, p_space_def, integrable_finite_integral] \\
        ‘?r. integral p (X n) = Normal r’ by METIS_TAC [integrable_normal_integral] \\
         POP_ORW >> rw [extreal_ainv_def, extreal_not_infty] \\
         MATCH_MP_TAC integrable_const >> rw [extreal_of_num_def, lt_infty]) >> Rewr' \\
    ‘?r. integral p (X n) = Normal r’
       by METIS_TAC [integrable_normal_integral, prob_space_def] \\
     ASM_SIMP_TAC std_ss [extreal_ainv_def, GSYM expectation_def, expectation_const] \\
     METIS_TAC [extreal_not_infty, sub_refl, GSYM extreal_ainv_def, extreal_sub_add])
 >> DISCH_TAC
 >> Know ‘!n. real_random_variable (Y n) p’
 >- (Q.X_GEN_TAC ‘n’ >> Q.UNABBREV_TAC ‘Y’ \\
     fs [real_random_variable, p_space_def, events_def] \\
     reverse CONJ_TAC
     >- (GEN_TAC >> DISCH_TAC \\
        ‘?a. X n x = Normal a’ by METIS_TAC [extreal_cases] \\
        ‘?b. expectation p (X n) = Normal b’ by METIS_TAC [expectation_normal] \\
         rw [extreal_sub_def, extreal_not_infty]) \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
     qexistsl_tac [‘X n’, ‘\x. expectation p (X n)’] \\
     ASM_SIMP_TAC std_ss [expectation_finite, space_def] \\
     fs [prob_space_def, measure_space_def, expectation_finite, space_def,
         IN_MEASURABLE_BOREL_CONST']) >> DISCH_TAC
 >> Know ‘!n. finite_second_moments p (Y n) /\ variance p (Y n) <= c’
 >- (Q.X_GEN_TAC ‘n’ \\
     ASM_SIMP_TAC std_ss [finite_second_moments_eq_finite_variance, Abbr `Y`] \\
    ‘expectation p (X n) <> PosInf /\
     expectation p (X n) <> NegInf’ by METIS_TAC [expectation_finite] \\
    ‘variance p (\x. X n x - expectation p (X n)) = variance p (X n)’
       by METIS_TAC [variance_real_affine'] >> POP_ORW >> art [] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘c’ >> rw [GSYM lt_infty])
 >> DISCH_THEN (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV))
 >> ‘!n. integrable p (Y n)’ by PROVE_TAC [finite_second_moments_imp_integrable]
 >> Know ‘!i j. i <> j ==> orthogonal p (Y i) (Y j)’
 >- (RW_TAC std_ss [orthogonal_def, Abbr ‘Y’] \\
     MATCH_MP_TAC uncorrelated_thm >> RW_TAC std_ss []) >> DISCH_TAC
 (* ‘Z n’ is the parial sums of ‘Y n’ *)
 >> Q.ABBREV_TAC ‘Z = \n x. SIGMA (\i. Y i x) (count1 n)’
 >> qexistsl_tac [‘Y’, ‘Z’]
 >> RW_TAC std_ss [Abbr ‘Y’, Abbr ‘Z’]
 >> ‘!i. X i x - expectation p (X i) =
        (\i. X i x) i - (\i. expectation p (X i)) i’ by METIS_TAC [] >> POP_ORW
 >> Know ‘SIGMA (\i. (\i. X i x) i - (\i. expectation p (X i)) i) (count1 n) =
          SIGMA (\i. X i x) (count1 n) -
          SIGMA (\i. expectation p (X i)) (count1 n)’
 >- (irule EXTREAL_SUM_IMAGE_SUB >> art [FINITE_COUNT, IN_COUNT] \\
     DISJ1_TAC (* or DISJ2_TAC *) >> fs [real_random_variable_def] \\
     METIS_TAC [expectation_finite]) >> Rewr'
 >> Suff ‘expectation p (S n) =
          SIGMA (\i. expectation p (X i)) (count1 n)’ >- rw []
 >> Know ‘expectation p (S n) =
          expectation p (\x. SIGMA (\i. X i x) (count1 n))’
 >- (MATCH_MP_TAC expectation_cong >> rw []) >> Rewr'
 >> MATCH_MP_TAC (REWRITE_RULE [GSYM expectation_def] integral_sum)
 >> FULL_SIMP_TAC std_ss [prob_space_def, real_random_variable_def, p_space_def,
                          FINITE_COUNT]
QED

Theorem SLLN_uncorrelated :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) /\
         (!i j. i <> j ==> uncorrelated p (X i) (X j)) /\
         (?c. c <> PosInf /\ !n. variance p (X n) <= c) ==>
          LLN p X almost_everywhere
Proof
    PRINT_TAC "proving Strong Law of Large Numbers for uncorrelated r.v.'s ..."
 >> RW_TAC std_ss [LLN_def]
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
 (* without loss of generality *)
 >> MP_TAC (Q.SPECL [‘p’, ‘X’, ‘Z’, ‘\n. expectation p (Z n)’, ‘c’]
                    SLLN_uncorrelated_wlog)
 >> RW_TAC std_ss []
 >> Know ‘((\n x. (Z n x - expectation p (Z n)) /
                  &SUC n) --> (\x. 0)) (almost_everywhere p) <=>
          ((\n x. W n x / &SUC n) --> (\x. 0)) (almost_everywhere p)’
 >- (MATCH_MP_TAC converge_AE_cong \\
     Q.EXISTS_TAC ‘0’ >> RW_TAC arith_ss []) >> Rewr'
 >> Q.PAT_X_ASSUM ‘!n x. x IN p_space p ==> _ = W n x’ K_TAC
 (* clean up X and S *)
 >> Q.PAT_X_ASSUM ‘!n. real_random_variable (X n) p’            K_TAC
 >> Q.PAT_X_ASSUM ‘!i j. i <> j ==> uncorrelated p (X i) (X j)’ K_TAC
 >> Q.PAT_X_ASSUM ‘!n. variance p (X n) <= c’                   K_TAC
 >> Q.UNABBREV_TAC ‘Z’
 (* rename Z to S, Y to X, c to M *)
 >> rename1 ‘!n x. x IN p_space p ==> S n x = SIGMA (\i. X i x) (count1 n)’
 >> rename1 ‘M <> PosInf’
 (* now the actual proof *)
 >> Know ‘0 <= M’
 >- (MATCH_MP_TAC le_trans >> Q.EXISTS_TAC ‘variance p (X 0)’ \\
     ASM_SIMP_TAC std_ss [variance_pos]) >> DISCH_TAC
 >> ‘M <> NegInf’ by PROVE_TAC [pos_not_neginf]
 (* properties of (S n) *)
 >> Know ‘!n. variance p (S n) <= &SUC n * M’
 >- (Q.X_GEN_TAC ‘n’ \\
     Know ‘variance p (S n) = variance p (\x. SIGMA (\i. X i x) (count1 n))’
     >- (MATCH_MP_TAC variance_cong >> rw []) >> Rewr' \\
     Know ‘variance p (\x. SIGMA (\i. X i x) (count1 n)) =
           SIGMA (\i. variance p (X i)) (count1 n)’
     >- (MATCH_MP_TAC variance_sum >> rw [FINITE_COUNT] \\
         RW_TAC std_ss [uncorrelated_vars_def] \\
         METIS_TAC [uncorrelated_orthogonal]) >> Rewr' \\
     Know ‘SIGMA (\x. M) (count1 n) = &CARD (count1 n) * M’
     >- (irule EXTREAL_SUM_IMAGE_FINITE_CONST >> rw [FINITE_COUNT]) \\
     REWRITE_TAC [Once EQ_SYM_EQ, CARD_COUNT] >> Rewr' \\
     irule EXTREAL_SUM_IMAGE_MONO >> rw [IN_COUNT, FINITE_COUNT] \\
     DISJ2_TAC >> GEN_TAC >> DISCH_TAC \\
     REWRITE_TAC [lt_infty] \\
     MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘M’ >> art [GSYM lt_infty])
 >> DISCH_TAC
 >> Know ‘!n. expectation p (S n) = 0’
 >- (Q.X_GEN_TAC ‘n’ \\
     Know ‘expectation p (S n) = expectation p (\x. SIGMA (\i. X i x) (count1 n))’
     >- (MATCH_MP_TAC expectation_cong >> rw []) >> Rewr' \\
     fs [prob_space_def, real_random_variable_def, expectation_def,
         random_variable_def, p_space_def, events_def] \\
     Know ‘integral p (\x. SIGMA (\i. X i x) (count1 n)) =
           SIGMA (\i. integral p (X i)) (count1 n)’
     >- (MATCH_MP_TAC integral_sum \\
         RW_TAC std_ss [IN_COUNT, FINITE_COUNT]) >> Rewr' >> rw [] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_ZERO >> REWRITE_TAC [FINITE_COUNT])
 >> DISCH_TAC
 >> Know ‘!n x. x IN p_space p ==> S n x <> PosInf /\ S n x <> NegInf’
 >- (qx_genl_tac [‘n’, ‘x’] >> NTAC 2 STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!n x. x IN p_space p ==> S n x = _’
       (fn th => ONCE_REWRITE_TAC [MATCH_MP th (ASSUME “x IN p_space p”)]) >|
     [ MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
       fs [real_random_variable_def, FINITE_COUNT, IN_COUNT],
       MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
       fs [real_random_variable_def, FINITE_COUNT, IN_COUNT] ])
 >> DISCH_TAC
 >> Know ‘!n. real_random_variable (S n) p’
 >- (RW_TAC std_ss [real_random_variable, p_space_def, events_def] \\
     Know ‘S n IN measurable (m_space p,measurable_sets p) Borel <=>
           (\x. SIGMA (\i. X i x) (count1 n))
               IN measurable (m_space p,measurable_sets p) Borel’
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONG \\
         FULL_SIMP_TAC std_ss [p_space_def]) >> Rewr' \\
     MATCH_MP_TAC (INST_TYPE [“:'b” |-> “:num”] IN_MEASURABLE_BOREL_SUM) \\
     qexistsl_tac [‘X’, ‘count1 n’] \\
     fs [real_random_variable, p_space_def,
         events_def, space_def, prob_space_def, measure_space_def])
 >> DISCH_TAC
 >> Know ‘!n. finite_second_moments p (S n)’
 >- (RW_TAC std_ss [finite_second_moments_eq_finite_variance] \\
     MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘&SUC n * M’ >> art [] \\
    ‘?r. M = Normal r’ by METIS_TAC [extreal_cases] \\
     rw [extreal_not_infty, extreal_of_num_def, extreal_mul_def, GSYM lt_infty])
 >> DISCH_TAC
 (* applying chebyshev_ineq_variance *)
 >> Know ‘!n e. 0 < e /\ e <> PosInf ==>
                prob p ({x | &SUC n * e <= abs (S n x - expectation p (S n))}
                        INTER p_space p)
             <= inv ((&SUC n * e) pow 2) * variance p (S n)’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC chebyshev_ineq_variance >> art [] \\
     MATCH_MP_TAC lt_mul >> fs [extreal_of_num_def, extreal_lt_eq])
 >> Q.PAT_ASSUM ‘!n. expectation p (S n) = 0’ (ONCE_REWRITE_TAC o wrap)
 >> REWRITE_TAC [sub_rzero] >> DISCH_TAC
 >> Know ‘!n e. 0 < e /\ e <> PosInf ==>
                prob p ({x | &SUC n * e <= abs (S n x)} INTER p_space p)
             <= inv ((&SUC n * e) pow 2) * (&SUC n * M)’
 >- (rpt STRIP_TAC >> MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC ‘inv ((&SUC n * e) pow 2) * variance p (S n)’ \\
     CONJ_TAC >- ASM_SIMP_TAC std_ss [] \\
     MATCH_MP_TAC le_lmul_imp >> art [] \\
     MATCH_MP_TAC le_inv \\
     MATCH_MP_TAC pow_pos_lt \\
     MATCH_MP_TAC lt_mul >> fs [extreal_of_num_def, extreal_lt_eq])
 >> POP_ASSUM K_TAC >> DISCH_TAC
 >> Know ‘!n e. 0 < e /\ e <> PosInf ==>
                prob p ({x | &SUC n * e <= abs (S n x)} INTER p_space p)
             <= inv (&SUC n * e pow 2) * M’
 >- (rpt STRIP_TAC \\
     Suff ‘inv (&SUC n * e pow 2) * M = inv ((&SUC n * e) pow 2) * (&SUC n * M)’
     >- (Rewr' >> FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
    ‘e <> NegInf’ by METIS_TAC [lt_le, pos_not_neginf] \\
    ‘?a. e = Normal a’ by METIS_TAC [extreal_cases] \\
     Know ‘0 < &SUC n * e pow 2’
     >- (MATCH_MP_TAC lt_mul \\
         CONJ_TAC >- (rw [extreal_of_num_def, extreal_lt_eq]) \\
         MATCH_MP_TAC pow_pos_lt >> art []) >> DISCH_TAC \\
    ‘&SUC n * e pow 2 <> 0’ by PROVE_TAC [lt_imp_ne] \\
    ‘?m. M = Normal m’ by METIS_TAC [extreal_cases] \\
     ASM_SIMP_TAC std_ss [extreal_inv_eq, extreal_of_num_def, extreal_mul_def,
                          extreal_pow_def] \\
     Know ‘0 < (&SUC n * a) pow 2’
     >- (MATCH_MP_TAC REAL_POW_LT \\
         MATCH_MP_TAC REAL_LT_MUL \\
         FULL_SIMP_TAC real_ss [extreal_of_num_def, extreal_lt_eq]) >> DISCH_TAC \\
    ‘(&SUC n * a) pow 2 <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] \\
     Know ‘0 < a pow 2’
     >- (MATCH_MP_TAC REAL_POW_LT \\
         METIS_TAC [extreal_of_num_def, extreal_lt_eq]) >> DISCH_TAC \\
    ‘a pow 2 <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] \\
     Know ‘0 < &SUC n * a pow 2’
     >- (MATCH_MP_TAC REAL_LT_MUL >> rw []) >> DISCH_TAC \\
    ‘&SUC n * a pow 2 <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] \\
     FULL_SIMP_TAC real_ss [extreal_inv_eq, extreal_mul_def,
                            extreal_11, REAL_INV_MUL, REAL_ENTIRE, POW_2] \\
     rw [])
 >> POP_ASSUM K_TAC >> DISCH_TAC
 >> Know ‘!n e. 0 < e /\ e <> PosInf ==>
                prob p {x | x IN p_space p /\ &SUC n * e < abs (S n x)}
             <= inv (&SUC n * e pow 2) * M’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC ‘prob p ({x | &SUC n * e <= abs (S n x)} INTER p_space p)’ \\
     reverse CONJ_TAC
     >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     Q.ABBREV_TAC ‘f = \x. abs (S n x)’ \\
    ‘!x. abs (S n x) = f x’ by METIS_TAC [] >> POP_ORW \\
     Q.ABBREV_TAC ‘P = \x. &SUC n * e < f x’ \\
    ‘!x. (&SUC n * e < f x) <=> P x’ by METIS_TAC [] >> POP_ORW \\
     SIMP_TAC std_ss [PROB_GSPEC, Abbr ‘P’] \\
     MATCH_MP_TAC PROB_INCREASING >> art [] \\
     Know ‘f IN measurable (m_space p,measurable_sets p) Borel’
     >- (Q.UNABBREV_TAC ‘f’ \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS \\
         Q.EXISTS_TAC ‘S n’ \\
         fs [space_def, real_random_variable,
             p_space_def, events_def, prob_space_def, measure_space_def]) \\
     DISCH_TAC \\
     ASM_SIMP_TAC std_ss [p_space_def, events_def,
                          IN_MEASURABLE_BOREL_ALL_MEASURE] \\
     rw [SUBSET_DEF, IN_INTER, GSPECIFICATION] \\
     MATCH_MP_TAC lt_imp_le >> art [])
 >> Know ‘!n e. {x | x IN p_space p /\ &SUC n * e < abs (S n x)} IN events p’
 >- (qx_genl_tac [‘n’, ‘e’] \\
     Q.ABBREV_TAC ‘f = \x. abs (S n x)’ \\
    ‘!x. abs (S n x) = f x’ by METIS_TAC [] >> POP_ORW \\
     Know ‘f IN measurable (m_space p,measurable_sets p) Borel’
     >- (Q.UNABBREV_TAC ‘f’ \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS \\
         Q.EXISTS_TAC ‘S n’ \\
         fs [space_def, real_random_variable,
             p_space_def, events_def, prob_space_def, measure_space_def]) \\
     DISCH_TAC \\
    ‘{x | x IN p_space p /\ &SUC n * e < f x} =
     {x | &SUC n * e < f x} INTER p_space p’ by SET_TAC [] >> POP_ORW \\
     ASM_SIMP_TAC std_ss [p_space_def, events_def,
                          IN_MEASURABLE_BOREL_ALL_MEASURE])
 >> POP_ASSUM K_TAC >> rpt DISCH_TAC
 (* applying Borel_Cantelli_Lemma1 *)
 >> Q.ABBREV_TAC ‘f = \n e x. &SUC n * e < abs (S n x)’
 >> Q.ABBREV_TAC ‘g = \n e. inv (&SUC n * e pow 2) * M’ >> fs []
 >> Q.ABBREV_TAC ‘E = \e n. {x | x IN p_space p /\ f (n ** 2) e x}’
 >> Know ‘!e. 0 < e /\ e <> PosInf ==> (prob p (limsup (E e)) = 0)’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC Borel_Cantelli_Lemma1 >> art [] \\
     CONJ_ASM1_TAC >- rw [Abbr ‘E’] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘suminf (\n. g (n ** 2) e)’ \\
     CONJ_TAC (* mono *)
     >- (MATCH_MP_TAC ext_suminf_mono \\
         SIMP_TAC std_ss [o_DEF, Abbr ‘E’] \\
         CONJ_TAC >- (GEN_TAC >> MATCH_MP_TAC PROB_POSITIVE >> art []) \\
         GEN_TAC >> FIRST_X_ASSUM MATCH_MP_TAC >> RW_TAC arith_ss []) \\
     SIMP_TAC std_ss [Abbr ‘g’] \\
  (* preparing for harmonic_series_pow_2 *)
     Know ‘!n. inv (&SUC (n ** 2) * e pow 2) * M =
               inv (e pow 2) * M * inv (&SUC (n ** 2))’
     >- (Q.X_GEN_TAC ‘n’ \\
        ‘0 < e pow 2’ by PROVE_TAC [pow_pos_lt] \\
        ‘0 < &SUC (n ** 2)’ by rw [extreal_lt_eq, extreal_of_num_def] \\
        ‘e pow 2 <> 0 /\ &SUC (n ** 2) <> 0’ by METIS_TAC [lt_imp_ne] \\
         ASM_SIMP_TAC real_ss [inv_mul] \\
         METIS_TAC [mul_comm, mul_assoc]) >> Rewr' \\
     Q.ABBREV_TAC ‘h = \n. inv (&SUC (n ** 2))’ >> simp [] \\
     Know ‘!n. 0 <= h n’
     >- (rw [Abbr ‘h’] \\
         MATCH_MP_TAC le_inv >> rw [extreal_of_num_def, extreal_lt_eq]) \\
     DISCH_TAC \\
     Know ‘0 <= suminf h’
     >- (MATCH_MP_TAC ext_suminf_pos >> rw [Abbr ‘h’]) \\
     DISCH_TAC \\
     Know ‘suminf (\n. inv (e pow 2) * M * h n) = inv (e pow 2) * M * suminf h’
     >- (MATCH_MP_TAC ext_suminf_cmul >> art [] \\
         MATCH_MP_TAC le_mul >> art [] \\
         MATCH_MP_TAC le_inv \\
         MATCH_MP_TAC pow_pos_lt >> art []) >> Rewr' \\
     Suff ‘suminf h <> PosInf’
     >- (DISCH_TAC \\
        ‘suminf h <> NegInf’ by METIS_TAC [pos_not_neginf] \\
         Know ‘inv (e pow 2) <> PosInf /\ inv (e pow 2) <> NegInf’
         >- (MATCH_MP_TAC inv_not_infty \\
             Suff ‘0 < e pow 2’ >- METIS_TAC [lt_imp_ne] \\
             MATCH_MP_TAC pow_pos_lt >> art []) >> STRIP_TAC \\
         REWRITE_TAC [GSYM lt_infty] \\
        ‘?a. inv (e pow 2) = Normal a’ by METIS_TAC [extreal_cases] \\
        ‘?b. M = Normal b’ by METIS_TAC [extreal_cases] \\
        ‘?c. suminf h = Normal c’ by METIS_TAC [extreal_cases] \\
         rw [extreal_mul_def, extreal_not_infty]) \\
  (* applying ext_suminf_offset *)
     Know ‘suminf h = SIGMA h (count 1) + suminf (\i. h (i + 1))’
     >- (MATCH_MP_TAC ext_suminf_offset >> art []) >> Rewr' \\
  (* applying harmonic_series_pow_2 *)
     rw [Abbr ‘h’, lt_infty] \\
     Suff ‘suminf (\i. inv (&SUC ((i + 1) ** 2))) < PosInf’
     >- (rw [GSYM lt_infty] \\
         Know ‘suminf (\i. inv (&SUC ((i + 1) ** 2))) <> NegInf’
         >- (MATCH_MP_TAC pos_not_neginf \\
             MATCH_MP_TAC ext_suminf_pos >> rw [] \\
             MATCH_MP_TAC le_inv >> rw [extreal_of_num_def, extreal_lt_eq]) \\
         DISCH_TAC \\
        ‘?r. suminf (\i. inv (&SUC ((i + 1) ** 2))) = Normal r’
           by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_of_num_def, extreal_add_def]) \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘suminf (\n. inv (&(SUC n) pow 2))’ \\
     reverse CONJ_TAC >- REWRITE_TAC [GSYM lt_infty, harmonic_series_pow_2] \\
     MATCH_MP_TAC ext_suminf_mono >> rw []
     >- (MATCH_MP_TAC le_inv >> rw [extreal_of_num_def, extreal_lt_eq]) \\
     Know ‘inv (&SUC ((n + 1) ** 2)) <= inv (&SUC n pow 2) <=>
           &SUC n pow 2 <= &SUC ((n + 1) ** 2)’
     >- (MATCH_MP_TAC inv_le_antimono \\
         rw [pow_pos_lt, extreal_of_num_def, extreal_lt_eq]) >> Rewr' \\
     Know ‘&SUC n pow 2 = &(SUC n ** 2)’
     >- (REWRITE_TAC [pow_2] \\
         REWRITE_TAC [EXP, ONE, TWO, MULT_ASSOC] \\
         RW_TAC real_ss [extreal_mul_def, extreal_of_num_def]) >> Rewr' \\
     rw [extreal_of_num_def, extreal_le_eq, ADD1])
 >> qunabbrevl_tac [‘E’, ‘f’, ‘g’] >> fs []
 >> Know ‘!e n x. x IN p_space p ==>
                 (&SUC (n ** 2) * e < abs (S (n ** 2) x) <=>
                  e < abs (S (n ** 2) x / &SUC (n ** 2)))’
 >- (rpt STRIP_TAC \\
     Know ‘abs (S (n ** 2) x / &SUC (n ** 2)) =
           abs (S (n ** 2) x) / abs &SUC (n ** 2)’
     >- (MATCH_MP_TAC abs_div >> art [] \\
         RW_TAC real_ss [extreal_of_num_def, extreal_11]) >> Rewr' \\
     Know ‘abs (&SUC (n ** 2)) = &SUC (n ** 2)’
     >- (REWRITE_TAC [abs_refl] \\
         RW_TAC real_ss [extreal_of_num_def, extreal_le_eq]) >> Rewr' \\
    ‘0 < &SUC (n ** 2)’ by rw [extreal_of_num_def, extreal_lt_eq] \\
    ‘&SUC (n ** 2) <> PosInf’ by METIS_TAC [num_not_infty] \\
     Know ‘e < abs (S (n ** 2) x) / &SUC (n ** 2) <=>
           e * &SUC (n ** 2) <
           abs (S (n ** 2) x) / &SUC (n ** 2) * &SUC (n ** 2)’
     >- (MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC lt_rmul >> art []) >> Rewr' \\
    ‘&SUC (n ** 2) <> 0’ by METIS_TAC [lt_imp_ne] \\
    ‘&SUC (n ** 2) <> NegInf’ by METIS_TAC [num_not_infty] \\
    ‘?r. r <> 0 /\ &SUC (n ** 2) = Normal r’
        by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_11] >> POP_ORW \\
     Know ‘abs (S (n ** 2) x) / Normal r * Normal r = abs (S (n ** 2) x)’
     >- (MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC div_mul_refl >> art []) >> Rewr' \\
     REWRITE_TAC [Once mul_comm])
 >> DISCH_TAC
 >> Know ‘!e n. {x | x IN p_space p /\ &SUC (n ** 2) * e < abs (S (n ** 2) x)} =
                {x | x IN p_space p /\ e < abs (S (n ** 2) x / &SUC (n ** 2))}’
 >- (rw [Once EXTENSION] >> METIS_TAC []) >> Rewr'
 >> POP_ASSUM K_TAC
 (* applying converge_AE_alt_limsup *)
 >> Q.ABBREV_TAC ‘Z = \n x. S (n ** 2) x / &SUC (n ** 2)’ >> simp []
 >> Q.PAT_X_ASSUM ‘!n e. 0 < e /\ e <> PosInf ==> P’ K_TAC
 >> DISCH_TAC
 (* stage work *)
 >> Know ‘!n. real_random_variable (Z n) p’
 >- (rw [Abbr ‘Z’] \\
     Know ‘real_random_variable (\x. S (n ** 2) x / &SUC (n ** 2)) p <=>
           real_random_variable
             (\x. SIGMA (\i. X i x) (count (SUC (n ** 2))) / &SUC (n ** 2)) p’
     >- (MATCH_MP_TAC real_random_variable_cong >> rw []) >> Rewr' \\
     MATCH_MP_TAC real_random_variable_LLN' >> art [])
 >> DISCH_TAC
 >> Know ‘(Z --> (\x. 0)) (almost_everywhere p)’
 >- (MP_TAC (SIMP_RULE std_ss [sub_rzero]
                       (Q.SPECL [‘p’, ‘Z’, ‘\x. 0’] converge_AE_alt_limsup)) \\
    ‘real_random_variable (\x. 0) p’ by PROVE_TAC [real_random_variable_zero] \\
     RW_TAC std_ss [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘!e. 0 < e /\ e <> PosInf ==> P’ K_TAC
 (* preparing for "method of subsequences" *)
 >> Q.ABBREV_TAC ‘N = \n. {k | n ** 2 <= k /\ k < SUC n ** 2}’
 >> Know ‘!n m. FINITE {k | n ** 2 <= k /\ k < m}’
 >- (rpt GEN_TAC \\
     irule SUBSET_FINITE >> Q.EXISTS_TAC ‘count m’ >> rw [SUBSET_DEF])
 >> DISCH_TAC
 >> ‘!n. FINITE (N n)’ by rw [Abbr ‘N’]
 >> Q.ABBREV_TAC ‘d = \n k x. abs (S k x - S (n ** 2) x)’
 >> Know ‘!n k x. x IN p_space p ==> d n k x <> PosInf /\ d n k x <> NegInf’
 >- (rpt GEN_TAC >> DISCH_TAC >> SIMP_TAC std_ss [Abbr ‘d’] \\
    ‘?a. S k x = Normal a’ by METIS_TAC [extreal_cases] \\
    ‘?b. S (n ** 2) x = Normal b’ by METIS_TAC [extreal_cases] \\
     ASM_SIMP_TAC std_ss [extreal_sub_def, extreal_abs_def, extreal_not_infty])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘D = \n x. sup (IMAGE (\k. d n k x) (N n))’
 (* NOTE: for different x, the maximal k may be different *)
 >> Know ‘!n x. ?k. n ** 2 <= k /\ k < SUC n ** 2 /\ D n x = d n k x’
 >- (rpt GEN_TAC \\
     Know ‘D n x IN (IMAGE (\k. d n k x) {k | n ** 2 <= k /\ k < SUC n ** 2})’
     >- (RW_TAC std_ss [Abbr ‘D’, Abbr ‘N’] \\
         MATCH_MP_TAC sup_maximal \\
         CONJ_TAC >- (MATCH_MP_TAC IMAGE_FINITE >> fs []) \\
         rw [Once EXTENSION, NOT_IN_EMPTY, IN_IMAGE] \\
         Q.EXISTS_TAC ‘n ** 2’ >> rw []) \\
     rw [IN_IMAGE] >> Q.EXISTS_TAC ‘k’ >> art [])
 (* now k becomes a function f of n and x, and from now on the original
    definition of `d` is not needed. *)
 >> DISCH_THEN (STRIP_ASSUME_TAC o (SIMP_RULE std_ss [SKOLEM_THM]))
 (* HARD: now finding the upper bound of E[D(n)^2] *)
 >> Know ‘!n. expectation p (\x. D n x pow 2) <=
              SIGMA (\k. expectation p (\x. (d n k x) pow 2)) (N n)’
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
     Know ‘!k.       integral p (\x. (d n k x) pow 2) =
              pos_fn_integral p (\x. (d n k x) pow 2)’
     >- (GEN_TAC >> MATCH_MP_TAC integral_pos_fn \\
         fs [le_pow2, prob_space_def]) >> Rewr' \\
     Know ‘       integral p (\x. (d n (f n x) x) pow 2) =
           pos_fn_integral p (\x. (d n (f n x) x) pow 2)’
     >- (MATCH_MP_TAC integral_pos_fn >> fs [le_pow2, prob_space_def]) >> Rewr' \\
     Know ‘SIGMA (\k. pos_fn_integral p ((\k x. d n k x pow 2) k)) (N n) =
           pos_fn_integral p (\x. SIGMA (\k. (\k x. d n k x pow 2) k x) (N n))’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC pos_fn_integral_sum \\
         fs [prob_space_def, p_space_def, le_pow2, real_random_variable_def,
             random_variable_def, events_def] \\
         RW_TAC set_ss [Abbr ‘N’, Abbr ‘d’, abs_pow2] \\
         HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_POW \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB' \\
         qexistsl_tac [‘S i’, ‘S (n ** 2)’] \\
         FULL_SIMP_TAC std_ss [measure_space_def]) \\
     DISCH_THEN (ONCE_REWRITE_TAC o wrap o BETA_RULE) \\
     MATCH_MP_TAC pos_fn_integral_mono \\
     RW_TAC std_ss [le_pow2] \\
    ‘DISJOINT {f n x} (N n DELETE (f n x))’ by SET_TAC [] \\
     Know ‘{f n x} UNION (N n DELETE (f n x)) = N n’
     >- (Suff ‘f n x IN (N n)’ >- SET_TAC [] \\
         RW_TAC set_ss [Abbr ‘N’]) >> DISCH_TAC \\
     Know ‘SIGMA (\k. (d n k x) pow 2) ({f n x} UNION (N n DELETE (f n x))) =
           SIGMA (\k. (d n k x) pow 2) {f n x} +
           SIGMA (\k. (d n k x) pow 2) (N n DELETE (f n x))’
     >- (irule EXTREAL_SUM_IMAGE_DISJOINT_UNION >> fs [FINITE_SING] \\
         DISJ1_TAC >> RW_TAC std_ss [] \\ (* 2 subgoals, same tactics *)
         (MATCH_MP_TAC pos_not_neginf >> rw [le_pow2])) >> POP_ORW >> Rewr' \\
     SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_SING] \\
     MATCH_MP_TAC le_addr_imp \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> fs [le_pow2])
 >> DISCH_TAC
 >> Know ‘!n. expectation p (\x. D n x pow 2) <=
              SIGMA (\k. expectation p (\x. (d n (SUC n ** 2) x) pow 2)) (N n)’
 >- (Q.X_GEN_TAC ‘n’ >> MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC ‘SIGMA (\k. expectation p (\x. (d n k x) pow 2)) (N n)’ \\
     POP_ASSUM (REWRITE_TAC o wrap) \\
     irule EXTREAL_SUM_IMAGE_MONO >> simp [] \\
     reverse CONJ_TAC
     >- (DISJ1_TAC >> GEN_TAC >> DISCH_TAC \\
         RW_TAC std_ss [expectation_def] \\ (* 2 subgoals, same tactics *)
         (MATCH_MP_TAC pos_not_neginf \\
          MATCH_MP_TAC integral_pos >> fs [prob_space_def, le_pow2])) \\
     Q.X_GEN_TAC ‘k’ \\
     RW_TAC set_ss [Abbr ‘N’, Abbr ‘d’, abs_pow2] \\
     Know ‘expectation p (\x. (S k x - S (n ** 2) x) pow 2) =
           expectation p (\x. (SIGMA (\i. X i x) (count1 k) -
                               SIGMA (\i. X i x) (count1 (n ** 2))) pow 2)’
     >- (MATCH_MP_TAC expectation_cong >> rw []) >> Rewr' \\
     Know ‘expectation p (\x. (S (SUC n ** 2) x - S (n ** 2) x) pow 2) =
           expectation p (\x. (SIGMA (\i. X i x) (count1 (SUC n ** 2)) -
                               SIGMA (\i. X i x) (count1 (n ** 2))) pow 2)’
     >- (MATCH_MP_TAC expectation_cong >> rw []) >> Rewr' \\
     Know ‘count1 k = {j | n ** 2 < j /\ j <= k} UNION (count1 (n ** 2))’
     >- (RW_TAC set_ss [Once EXTENSION, IN_COUNT] >> rw []) >> Rewr' \\
     Know ‘DISJOINT {j | n ** 2 < j /\ j <= k} (count1 (n ** 2))’
     >- (RW_TAC set_ss [DISJOINT_ALT, IN_COUNT] >> rw []) >> DISCH_TAC \\
     Know ‘count1 (SUC n ** 2) = {j | n ** 2 < j /\ j <= SUC n ** 2} UNION (count1 (n ** 2))’
     >- (RW_TAC set_ss [Once EXTENSION, IN_COUNT] >> rw []) >> Rewr' \\
     Know ‘DISJOINT {j | n ** 2 < j /\ j <= SUC n ** 2} (count1 (n ** 2))’
     >- (RW_TAC set_ss [DISJOINT_ALT, IN_COUNT] >> rw []) >> DISCH_TAC \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
     Know ‘!m. FINITE {j | n ** 2 < j /\ j <= m}’
     >- (Q.X_GEN_TAC ‘m’ \\
         MATCH_MP_TAC FINITE_SUBSET \\
         Q.EXISTS_TAC ‘count1 m’ >> rw [SUBSET_DEF]) >> DISCH_TAC \\
     Know ‘expectation p
             (\x. (SIGMA (\i. X i x) ({j | n ** 2 < j /\ j <= k} UNION count1 (n ** 2)) -
                   SIGMA (\i. X i x) (count1 (n ** 2))) pow 2) =
           expectation p
             (\x. (SIGMA (\i. X i x) {j | n ** 2 < j /\ j <= k} +
                   SIGMA (\i. X i x) (count1 (n ** 2)) -
                   SIGMA (\i. X i x) (count1 (n ** 2))) pow 2)’
     >- (MATCH_MP_TAC expectation_cong >> RW_TAC std_ss [] \\
         Suff ‘SIGMA (\i. X i x) ({j | n ** 2 < j /\ j <= k} UNION (count1 (n ** 2))) =
               SIGMA (\i. X i x) {j | n ** 2 < j /\ j <= k} +
               SIGMA (\i. X i x) (count1 (n ** 2))’ >- rw [] \\
         irule EXTREAL_SUM_IMAGE_DISJOINT_UNION \\
         fs [FINITE_SING, FINITE_COUNT]) >> Rewr' \\
     Know ‘expectation p
             (\x. (SIGMA (\i. X i x) ({j | n ** 2 < j /\ j <= SUC n ** 2} UNION count1 (n ** 2)) -
                   SIGMA (\i. X i x) (count1 (n ** 2))) pow 2) =
           expectation p
             (\x. (SIGMA (\i. X i x) {j | n ** 2 < j /\ j <= SUC n ** 2} +
                   SIGMA (\i. X i x) (count1 (n ** 2)) -
                   SIGMA (\i. X i x) (count1 (n ** 2))) pow 2)’
     >- (MATCH_MP_TAC expectation_cong >> RW_TAC std_ss [] \\
         Suff ‘SIGMA (\i. X i x) ({j | n ** 2 < j /\ j <= SUC n ** 2} UNION (count1 (n ** 2))) =
               SIGMA (\i. X i x) {j | n ** 2 < j /\ j <= SUC n ** 2} +
               SIGMA (\i. X i x) (count1 (n ** 2))’ >- rw [] \\
         irule EXTREAL_SUM_IMAGE_DISJOINT_UNION \\
         fs [FINITE_SING, FINITE_COUNT]) >> Rewr' \\
     Know ‘!x. x IN p_space p ==> SIGMA (\i. X i x) (count1 (n ** 2)) <> PosInf’
     >- (GEN_TAC >> DISCH_TAC \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
         rw [FINITE_COUNT]) >> DISCH_TAC \\
     Know ‘!x. x IN p_space p ==> SIGMA (\i. X i x) (count1 (n ** 2)) <> NegInf’
     >- (GEN_TAC >> DISCH_TAC \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
         rw [FINITE_COUNT]) >> DISCH_TAC \\
     Know ‘!m. expectation p
                 (\x. (SIGMA (\i. X i x) {j | n ** 2 < j /\ j <= m} +
                       SIGMA (\i. X i x) (count1 (n ** 2)) -
                       SIGMA (\i. X i x) (count1 (n ** 2))) pow 2) =
               expectation p
                 (\x. (SIGMA (\i. X i x) {j | n ** 2 < j /\ j <= m}) pow 2)’
     >- (GEN_TAC >> MATCH_MP_TAC expectation_cong >> RW_TAC std_ss [] \\
         Suff ‘SIGMA (\i. X i x) {j | n ** 2 < j /\ j <= m} +
               SIGMA (\i. X i x) (count1 (n ** 2)) -
               SIGMA (\i. X i x) (count1 (n ** 2)) =
               SIGMA (\i. X i x) {j | n ** 2 < j /\ j <= m}’ >- rw [] \\
         rw [add_sub]) >> Rewr' \\
  (* now converting LHS and RHS to variances *)
     Know ‘!m x. x IN p_space p ==>
                 SIGMA (\i. X i x) {j | n ** 2 < j /\ j <= m} =
                 (\x. SIGMA (\i. X i x) {j | n ** 2 < j /\ j <= m}) x -
                 expectation p (\x. SIGMA (\i. X i x) {j | n ** 2 < j /\ j <= m})’
     >- (rpt GEN_TAC >> DISCH_TAC \\
         Suff ‘expectation p (\x. SIGMA (\i. X i x) {j | n ** 2 < j /\ j <= m}) = 0’
         >- rw [sub_rzero] \\
         REWRITE_TAC [expectation_def] \\
         Know ‘integral p (\x. SIGMA (\i. X i x) {j | n ** 2 < j /\ j <= m}) =
               SIGMA (\i. integral p (X i)) {j | n ** 2 < j /\ j <= m}’
         >- (MATCH_MP_TAC integral_sum \\
             fs [p_space_def, prob_space_def, expectation_def]) >> Rewr' \\
         fs [expectation_def] \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_ZERO >> art []) >> DISCH_TAC \\
     Know ‘!m. expectation p
                 (\x. SIGMA (\i. X i x) {j | n ** 2 < j /\ j <= m} pow 2) =
               expectation p
                 (\x. ((\x. SIGMA (\i. X i x) {j | n ** 2 < j /\ j <= m}) x -
                       expectation p (\x. SIGMA (\i. X i x) {j | n ** 2 < j /\ j <= m})) pow 2)’
     >- (Q.X_GEN_TAC ‘m’ \\
         MATCH_MP_TAC expectation_cong >> RW_TAC std_ss [] \\
         Suff ‘SIGMA (\i. X i x) {j | n ** 2 < j /\ j <= m} =
               (\x. SIGMA (\i. X i x) {j | n ** 2 < j /\ j <= m}) x -
               expectation p
                 (\x. SIGMA (\i. X i x) {j | n ** 2 < j /\ j <= m})’ >- PROVE_TAC [] \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> Rewr' \\
     REWRITE_TAC [GSYM variance_alt] \\
     Know ‘!m. variance p (\x. SIGMA (\i. X i x) {j | n ** 2 < j /\ j <= m}) =
               SIGMA (\i. variance p (X i)) {j | n ** 2 < j /\ j <= m}’
     >- (Q.X_GEN_TAC ‘m’ >> MATCH_MP_TAC variance_sum \\
         rw [uncorrelated_vars_def, real_random_variable_def] \\
         METIS_TAC [REWRITE_RULE [real_random_variable_def]
                                 uncorrelated_orthogonal]) >> Rewr' \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET \\
     ASM_SIMP_TAC std_ss [variance_pos] \\
     RW_TAC set_ss [SUBSET_DEF] \\
     MATCH_MP_TAC LESS_EQ_TRANS >> Q.EXISTS_TAC ‘k’ >> art [] \\
     MATCH_MP_TAC LESS_IMP_LESS_OR_EQ >> art [])
 >> POP_ASSUM K_TAC
 (* ‘J’ is slight different with ‘N’ but the cardinality is the same *)
 >> Q.ABBREV_TAC ‘J = \n. {j | n ** 2 < j /\ j <= SUC n ** 2}’
 >> Know ‘!n. FINITE (J n)’
 >- (Q.X_GEN_TAC ‘n’ >> MATCH_MP_TAC FINITE_SUBSET \\
     Q.EXISTS_TAC ‘count1 (SUC n ** 2)’ >> rw [Abbr ‘J’, SUBSET_DEF])
 >> DISCH_TAC
 >> Know ‘!n. CARD (N n) = 2 * n + 1’
 >- (RW_TAC std_ss [Abbr ‘N’] \\
     Know ‘{k | n ** 2 <= k /\ k < SUC n ** 2} = (count (SUC n ** 2)) DIFF (count (n ** 2))’
     >- (RW_TAC set_ss [Once EXTENSION] >> rw []) >> Rewr' \\
     Know ‘CARD (count (SUC n ** 2) DIFF (count (n ** 2))) =
           CARD (count (SUC n ** 2)) - CARD (count (SUC n ** 2) INTER (count (n ** 2)))’
     >- (MATCH_MP_TAC CARD_DIFF_EQN >> REWRITE_TAC [FINITE_COUNT]) >> Rewr' \\
     Know ‘count (SUC n ** 2) INTER (count (n ** 2)) = count (n ** 2)’
     >- (RW_TAC set_ss [Once EXTENSION, IN_COUNT] \\
         EQ_TAC >> RW_TAC arith_ss [] \\
         MATCH_MP_TAC LESS_TRANS >> Q.EXISTS_TAC ‘n ** 2’ >> rw []) >> Rewr' \\
     REWRITE_TAC [CARD_COUNT, ADD1, SUM_SQUARED] >> rw [])
 >> DISCH_TAC
 >> Know ‘!n. CARD (J n) = 2 * n + 1’
 >- (RW_TAC std_ss [Abbr ‘J’] \\
     Know ‘{k | n ** 2 < k /\ k <= SUC n ** 2} = (count1 (SUC n ** 2)) DIFF (count1 (n ** 2))’
     >- (RW_TAC set_ss [Once EXTENSION] >> rw []) >> Rewr' \\
     Know ‘CARD (count1 (SUC n ** 2) DIFF (count1 (n ** 2))) =
           CARD (count1 (SUC n ** 2)) - CARD (count1 (SUC n ** 2) INTER (count1 (n ** 2)))’
     >- (MATCH_MP_TAC CARD_DIFF_EQN >> REWRITE_TAC [FINITE_COUNT]) >> Rewr' \\
     Know ‘count1 (SUC n ** 2) INTER (count1 (n ** 2)) = count1 (n ** 2)’
     >- (RW_TAC set_ss [Once EXTENSION, IN_COUNT] \\
         EQ_TAC >> RW_TAC arith_ss [] \\
         MATCH_MP_TAC LESS_TRANS >> Q.EXISTS_TAC ‘SUC (n ** 2)’ >> rw []) >> Rewr' \\
     REWRITE_TAC [CARD_COUNT, ADD1, SUM_SQUARED] >> rw [])
 >> DISCH_TAC
 >> Know ‘!n k. expectation p (\x. (d n (SUC n ** 2) x) pow 2) =
                variance p (\x. SIGMA (\i. X i x) (J n))’
 >- (RW_TAC std_ss [Abbr ‘d’, variance_alt, abs_pow2] \\
     Know ‘expectation p (\x. (S (SUC n ** 2) x - S (n ** 2) x) pow 2) =
           expectation p
             (\x. (SIGMA (\i. X i x) (count1 (SUC n ** 2)) -
                   SIGMA (\i. X i x) (count1 (n ** 2))) pow 2)’
     >- (MATCH_MP_TAC expectation_cong >> RW_TAC std_ss []) >> Rewr' \\
     Know ‘count1 (SUC n ** 2) = (J n) UNION (count1 (n ** 2))’
     >- (RW_TAC set_ss [Abbr ‘J’, Once EXTENSION, IN_COUNT] \\
         EQ_TAC >> RW_TAC arith_ss [LT_SUC_LE] \\
         MATCH_MP_TAC LESS_EQ_TRANS \\
         Q.EXISTS_TAC ‘n ** 2’ >> rw []) >> Rewr' \\
     Know ‘DISJOINT (J n) (count1 (n ** 2))’
     >- (RW_TAC set_ss [Abbr ‘J’, DISJOINT_ALT, IN_COUNT] >> rw []) >> DISCH_TAC \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
     Know ‘expectation p
             (\x. (SIGMA (\i. X i x) (J n UNION count1 (n ** 2)) -
                   SIGMA (\i. X i x) (count1 (n ** 2))) pow 2) =
           expectation p
             (\x. (SIGMA (\i. X i x) (J n) +
                   SIGMA (\i. X i x) (count1 (n ** 2)) -
                   SIGMA (\i. X i x) (count1 (n ** 2))) pow 2)’
     >- (MATCH_MP_TAC expectation_cong >> RW_TAC std_ss [] \\
         Suff ‘SIGMA (\i. X i x) (J n UNION count1 (n ** 2)) =
               SIGMA (\i. X i x) (J n) + SIGMA (\i. X i x) (count1 (n ** 2))’
         >- PROVE_TAC [] \\
         irule EXTREAL_SUM_IMAGE_DISJOINT_UNION >> rw []) >> Rewr' \\
     Know ‘!x. x IN p_space p ==> SIGMA (\i. X i x) (count1 (n ** 2)) <> PosInf’
     >- (GEN_TAC >> DISCH_TAC \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
         rw [FINITE_COUNT]) >> DISCH_TAC \\
     Know ‘!x. x IN p_space p ==> SIGMA (\i. X i x) (count1 (n ** 2)) <> NegInf’
     >- (GEN_TAC >> DISCH_TAC \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
         rw [FINITE_COUNT]) >> DISCH_TAC \\
     Know ‘expectation p
             (\x. (SIGMA (\i. X i x) (J n) +
                   SIGMA (\i. X i x) (count1 (n ** 2)) -
                   SIGMA (\i. X i x) (count1 (n ** 2))) pow 2) =
           expectation p (\x. (SIGMA (\i. X i x) (J n)) pow 2)’
     >- (MATCH_MP_TAC expectation_cong >> RW_TAC std_ss [add_sub]) >> Rewr' \\
     Suff ‘expectation p (\x. SIGMA (\i. X i x) (J n)) = 0’ >- rw [sub_rzero] \\
     RW_TAC std_ss [expectation_def] \\
     Know ‘integral p (\x. SIGMA (\i. X i x) (J n)) = SIGMA (\i. integral p (X i)) (J n)’
     >- (MATCH_MP_TAC integral_sum \\
         fs [p_space_def, prob_space_def, expectation_def]) >> Rewr' \\
     FULL_SIMP_TAC std_ss [expectation_def] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_ZERO >> art []) >> Rewr'
 >> Know ‘!n. SIGMA (\k. variance p (\x. SIGMA (\i. X i x) (J n))) (N n) =
              &CARD (N n) * (variance p (\x. SIGMA (\i. X i x) (J n)))’
 >- (GEN_TAC >> irule EXTREAL_SUM_IMAGE_FINITE_CONST \\
     ASM_SIMP_TAC std_ss [] \\
     DISJ1_TAC >> MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC variance_pos >> art []) >> Rewr'
 >> Know ‘!n. variance p (\x. SIGMA (\i. X i x) (J n)) =
                   SIGMA (\i. variance p (X i)) (J n)’
 >- (RW_TAC std_ss [] >> MATCH_MP_TAC variance_sum \\
     rw [uncorrelated_vars_def, real_random_variable_def] \\
     METIS_TAC [uncorrelated_orthogonal]) >> Rewr'
 >> DISCH_TAC
 >> Know ‘!n. expectation p (\x. (D n x) pow 2) <= &CARD (N n) * SIGMA (\i. M) (J n)’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC ‘&CARD (N n) * SIGMA (\i. variance p (X i)) (J n)’ >> art [] \\
     MATCH_MP_TAC le_lmul_imp \\
     CONJ_TAC >- RW_TAC real_ss [extreal_of_num_def, extreal_le_eq] \\
     irule EXTREAL_SUM_IMAGE_MONO >> ASM_SIMP_TAC std_ss [] \\
     DISJ1_TAC >> GEN_TAC >> DISCH_TAC \\
     MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC variance_pos >> art [])
 >> POP_ASSUM K_TAC
 >> Know ‘!n. SIGMA (\i. M) (J n) = &CARD (N n) * M’
 >- (Q.X_GEN_TAC ‘n’ \\
    ‘CARD (N n) = CARD (J n)’ by METIS_TAC [] >> POP_ORW \\
     irule EXTREAL_SUM_IMAGE_FINITE_CONST >> simp []) >> Rewr'
 >> REWRITE_TAC [mul_assoc, GSYM pow_2]
 (* ‘J’ is no more needed *)
 >> Q.PAT_X_ASSUM ‘!n. CARD (J n) = _’ K_TAC
 >> Q.PAT_X_ASSUM ‘!n. FINITE (J n)’   K_TAC
 >> Q.UNABBREV_TAC ‘J’
 >> DISCH_TAC
 (* stage work, now prove the AE convergence of D(n)/n^2 *)
 >> Q.ABBREV_TAC ‘W = (\n x. D n x / &SUC (n ** 2))’
 >> Know ‘!n. real_random_variable (W n) p’
 >- (Q.X_GEN_TAC ‘n’ \\
     SIMP_TAC std_ss [Abbr ‘W’, real_random_variable_def,
                      random_variable_def, p_space_def, events_def] \\
     reverse CONJ_TAC
     >- (GEN_TAC >> DISCH_TAC >> art [extreal_of_num_def] \\
         FULL_SIMP_TAC std_ss [p_space_def] \\
        ‘?r. d n (f n x) x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         Suff ‘&SUC (n ** 2) <> (0 :real)’ >- METIS_TAC [extreal_div_eq, extreal_not_infty] \\
         rw []) \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL \\
     qexistsl_tac [‘D n’, ‘inv &SUC (n ** 2)’] \\
     fs [prob_space_def, measure_space_def, p_space_def, events_def, space_def] \\
     reverse CONJ_TAC
     >- (RW_TAC std_ss [extreal_of_num_def] \\
        ‘&SUC (n ** 2) <> (0 :real)’ by RW_TAC real_ss [] \\
         ASM_SIMP_TAC real_ss [GSYM extreal_inv_def] \\
         MATCH_MP_TAC div_eq_mul_linv \\
         rw [extreal_of_num_def, extreal_lt_eq]) \\
     NTAC 2 (POP_ASSUM K_TAC) \\
     Q.UNABBREV_TAC ‘D’ >> BETA_TAC \\
     irule (INST_TYPE [“:'b” |-> “:num”] IN_MEASURABLE_BOREL_MAXIMAL) >> art [] \\
     qexistsl_tac [‘N n’, ‘d n’] >> ASM_SIMP_TAC std_ss [] \\
     Q.X_GEN_TAC ‘k’ >> Q.UNABBREV_TAC ‘d’ >> BETA_TAC \\
     POP_ASSUM K_TAC (* clean up *) \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS \\
     Q.EXISTS_TAC ‘\x. S k x - S (n ** 2) x’ >> art [] \\
     reverse CONJ_TAC >- rw [space_def] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
     qexistsl_tac [‘S k’, ‘S (n ** 2)’] \\
     fs [space_def, real_random_variable, p_space_def, events_def]) >> DISCH_TAC
 >> Know ‘!n. finite_second_moments p (W n)’
 >- (RW_TAC std_ss [finite_second_moments_literally, expectation_def] \\
     Q.UNABBREV_TAC ‘W’ >> BETA_TAC \\
     Know ‘integral p (\x. (D n x / &SUC (n ** 2)) pow 2) =
           integral p (\x. (inv &SUC (n ** 2) * D n x) pow 2)’
     >- (MATCH_MP_TAC integral_cong \\
         CONJ_TAC >- FULL_SIMP_TAC std_ss [prob_space_def] \\
         RW_TAC std_ss [] \\
         Suff ‘d n (f n x) x / &SUC (n ** 2) =
               inv &SUC (n ** 2) * d n (f n x) x’ >- rw [] \\
         MATCH_MP_TAC div_eq_mul_linv >> art [] \\
         FULL_SIMP_TAC std_ss [p_space_def] \\
         RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq]) >> Rewr' \\
     Know ‘       integral p (\x. (inv &SUC (n ** 2) * D n x) pow 2) =
           pos_fn_integral p (\x. (inv &SUC (n ** 2) * D n x) pow 2)’
     >- (MATCH_MP_TAC integral_pos_fn \\
         FULL_SIMP_TAC std_ss [le_pow2, prob_space_def]) >> Rewr' \\
     REWRITE_TAC [pow_mul, extreal_of_num_def] \\
     Know ‘(inv (Normal &SUC (n ** 2))) pow 2 = Normal ((inv &SUC (n ** 2)) pow 2)’
     >- (‘&SUC (n ** 2) <> (0 :real)’ by RW_TAC real_ss [] \\
         ASM_SIMP_TAC std_ss [extreal_inv_eq, extreal_pow_def]) >> Rewr' \\
     Know ‘pos_fn_integral p
              (\x. Normal ((inv &SUC (n ** 2)) pow 2) * (\x. (D n x) pow 2) x) =
           Normal ((inv &SUC (n ** 2)) pow 2) * pos_fn_integral p (\x. (D n x) pow 2)’
     >- (MATCH_MP_TAC pos_fn_integral_cmul \\
         fs [prob_space_def, le_pow2]) \\
     DISCH_THEN (ONCE_REWRITE_TAC o wrap o BETA_RULE) \\
     Q.ABBREV_TAC ‘c = Normal ((inv &SUC (n ** 2)) pow 2)’ \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘c * &CARD (N n) pow 2 * M’ \\
     reverse CONJ_TAC
     >- (Q.UNABBREV_TAC ‘c’ \\
        ‘?r. M = Normal r’ by METIS_TAC [extreal_cases] \\
         ASM_SIMP_TAC std_ss [extreal_pow_def, extreal_of_num_def,
                              lt_infty, extreal_mul_def]) \\
     ONCE_REWRITE_TAC [GSYM mul_assoc] \\
     MATCH_MP_TAC le_lmul_imp \\
     CONJ_TAC >- rw [Abbr ‘c’, extreal_of_num_def, extreal_le_eq, le_pow2] \\
     Suff ‘pos_fn_integral p (\x. (D n x) pow 2) =
               expectation p (\x. (D n x) pow 2)’ >- (Rewr' >> art []) \\
     REWRITE_TAC [expectation_def, Once EQ_SYM_EQ] \\
     MATCH_MP_TAC integral_pos_fn \\
     FULL_SIMP_TAC std_ss [prob_space_def, le_pow2]) >> DISCH_TAC
 (* stage work *)
 >> Know ‘(W --> (\x. 0)) (almost_everywhere p)’
 >- (‘real_random_variable (\x. 0) p’ by METIS_TAC [real_random_variable_zero] \\
     RW_TAC std_ss [converge_AE_alt_limsup, sub_rzero] \\
     MATCH_MP_TAC Borel_Cantelli_Lemma1 >> BETA_TAC >> art [] \\
     STRONG_CONJ_TAC
     >- (Q.X_GEN_TAC ‘n’ \\
        ‘{x | x IN p_space p /\ e < abs (W n x)} =
         {x | e < abs (W n x)} INTER p_space p’ by SET_TAC [] >> POP_ORW \\
         REWRITE_TAC [lt_abs_bounds] \\
        ‘{x | W n x < -e \/ e < W n x} INTER p_space p =
         ({x | W n x < -e} INTER p_space p) UNION
         ({x | e < W n x} INTER p_space p)’ by SET_TAC [] >> POP_ORW \\
         MATCH_MP_TAC EVENTS_UNION \\
         fs [events_def, p_space_def, real_random_variable_def,
             random_variable_def] \\
         METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC \\
     Know ‘!n. {x | x IN p_space p /\ e <= abs (W n x)} IN events p’
     >- (Q.X_GEN_TAC ‘n’ \\
        ‘{x | x IN p_space p /\ e <= abs (W n x)} =
         {x | e <= abs (W n x)} INTER p_space p’ by SET_TAC [] >> POP_ORW \\
         REWRITE_TAC [le_abs_bounds] \\
        ‘{x | W n x <= -e \/ e <= W n x} INTER p_space p =
         ({x | W n x <= -e} INTER p_space p) UNION
         ({x | e <= W n x} INTER p_space p)’ by SET_TAC [] >> POP_ORW \\
         MATCH_MP_TAC EVENTS_UNION \\
         fs [events_def, p_space_def, real_random_variable_def,
             random_variable_def] \\
         METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC \\
     SIMP_TAC std_ss [o_DEF] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘suminf (\n. prob p {x | x IN p_space p /\ e <= abs (W n x)})’ \\
     CONJ_TAC >- (MATCH_MP_TAC ext_suminf_mono \\
                  CONJ_TAC >- METIS_TAC [PROB_POSITIVE] \\
                  RW_TAC std_ss [] \\
                  MATCH_MP_TAC PROB_INCREASING >> art [] \\
                  RW_TAC set_ss [SUBSET_DEF] \\
                  MATCH_MP_TAC lt_imp_le >> art []) \\
  (* preparing for prob_markov_ineq *)
    ‘!n. {x | x IN p_space p /\ e <= abs (W n x)} =
         {x | e <= abs (W n x)} INTER p_space p’ by SET_TAC [] >> POP_ORW \\
     Know ‘!n x. e <= abs (W n x) <=> e pow 2 <= abs ((\x. (W n x) pow 2) x)’
     >- (rpt GEN_TAC >> BETA_TAC \\
        ‘abs ((W n x) pow 2) = (abs (W n x)) pow 2’
            by METIS_TAC [abs_refl, le_pow2, abs_pow2] >> POP_ORW \\
         MATCH_MP_TAC pow_le_full >> rw [abs_pos] \\
         MATCH_MP_TAC lt_imp_le >> art []) >> DISCH_TAC \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘suminf (\n. inv (e pow 2) * expectation p (abs o (\x. (W n x) pow 2)))’ \\
     CONJ_TAC
     >- (MATCH_MP_TAC ext_suminf_mono >> art [] \\
         CONJ_TAC >- (Q.X_GEN_TAC ‘n’ \\
                      POP_ASSUM (ONCE_REWRITE_TAC o wrap o GSYM) \\
                      BETA_TAC >> MATCH_MP_TAC PROB_POSITIVE \\
                      Suff ‘{x | e <= abs (W n x)} INTER p_space p =
                            {x | x IN p_space p /\ e <= abs (W n x)}’ >- rw [] \\
                      SET_TAC []) \\
         Q.X_GEN_TAC ‘n’ >> BETA_TAC \\
      (* applying prob_markov_ineq *)
         HO_MATCH_MP_TAC prob_markov_ineq >> art [] \\
         reverse CONJ_TAC >- (MATCH_MP_TAC pow_pos_lt >> art []) \\
         METIS_TAC [finite_second_moments_eq_integrable_square]) \\
     SIMP_TAC std_ss [o_DEF] \\
    ‘!n x. abs ((W n x) pow 2) = (W n x) pow 2’ by METIS_TAC [abs_refl, le_pow2] >> POP_ORW \\
     NTAC 3 (POP_ASSUM K_TAC) \\
     REWRITE_TAC [expectation_def] \\
     Know ‘!n. integral p (\x. (W n x) pow 2) = pos_fn_integral p (\x. (W n x) pow 2)’
     >- (GEN_TAC >> MATCH_MP_TAC integral_pos_fn \\
         fs [prob_space_def, le_pow2]) >> Rewr' \\
     Q.UNABBREV_TAC ‘W’ >> BETA_TAC \\
     Know ‘!n x. x IN p_space p ==> D n x / &SUC (n ** 2) = inv &SUC (n ** 2) * D n x’
     >- (rpt GEN_TAC >> DISCH_TAC \\
         MATCH_MP_TAC div_eq_mul_linv >> art [] \\
         FULL_SIMP_TAC std_ss [p_space_def] \\
         RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq]) >> DISCH_TAC \\
     Know ‘!n. pos_fn_integral p (\x. (D n x / &SUC (n ** 2)) pow 2) =
               pos_fn_integral p (\x. (inv &SUC (n ** 2) * D n x) pow 2)’
     >- (Q.X_GEN_TAC ‘n’ \\
         MATCH_MP_TAC pos_fn_integral_cong \\
         CONJ_TAC >- FULL_SIMP_TAC std_ss [prob_space_def] \\
         CONJ_TAC >- rw [le_pow2] \\
         CONJ_TAC >- rw [le_pow2] \\
         FULL_SIMP_TAC std_ss [p_space_def]) >> Rewr' \\
     POP_ASSUM K_TAC \\
     REWRITE_TAC [pow_mul, extreal_of_num_def] \\
     Know ‘!n. (inv (Normal &SUC (n ** 2))) pow 2 = Normal ((inv &SUC (n ** 2)) pow 2)’
     >- (GEN_TAC >> ‘&SUC (n ** 2) <> (0 :real)’ by RW_TAC real_ss [] \\
         ASM_SIMP_TAC std_ss [extreal_inv_eq, extreal_pow_def]) >> Rewr' \\
     Know ‘!n. pos_fn_integral p
                 (\x. Normal ((inv &SUC (n ** 2)) pow 2) * (\x. (D n x) pow 2) x) =
               Normal ((inv &SUC (n ** 2)) pow 2) * pos_fn_integral p (\x. (D n x) pow 2)’
     >- (GEN_TAC >> MATCH_MP_TAC pos_fn_integral_cmul \\
         fs [prob_space_def, le_pow2]) \\
     DISCH_THEN (ONCE_REWRITE_TAC o wrap o BETA_RULE) \\
     ONCE_REWRITE_TAC [mul_assoc] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘suminf (\n. inv (e pow 2) * Normal ((inv &SUC (n ** 2)) pow 2) *
                               &CARD (N n) pow 2 * M)’ \\
     CONJ_TAC
     >- (MATCH_MP_TAC ext_suminf_mono >> BETA_TAC \\
         Know ‘!n. 0 <= inv (e pow 2) * Normal ((inv &SUC (n ** 2)) pow 2)’
         >- (Q.X_GEN_TAC ‘n’ >> MATCH_MP_TAC le_mul \\
             CONJ_TAC >- (MATCH_MP_TAC lt_imp_le \\
                          MATCH_MP_TAC inv_pos' \\
                          CONJ_TAC >- (MATCH_MP_TAC pow_pos_lt >> art []) \\
                         ‘e <> NegInf’ by METIS_TAC [pos_not_neginf, lt_imp_le] \\
                          METIS_TAC [pow_not_infty]) \\
             RW_TAC real_ss [extreal_of_num_def, extreal_le_eq, REAL_LE_POW2]) \\
         DISCH_TAC \\
         CONJ_TAC >- (GEN_TAC >> MATCH_MP_TAC le_mul >> art [] \\
                      MATCH_MP_TAC pos_fn_integral_pos \\
                      fs [prob_space_def, le_pow2]) \\
         Q.X_GEN_TAC ‘n’ \\
         Q.ABBREV_TAC ‘z = inv (e pow 2) * Normal ((inv &SUC (n ** 2)) pow 2)’ \\
         ONCE_REWRITE_TAC [GSYM mul_assoc] \\
         MATCH_MP_TAC le_lmul_imp \\
         Q.UNABBREV_TAC ‘z’ >> CONJ_TAC >- art [] \\
         Suff ‘pos_fn_integral p (\x. (D n x) pow 2) =
                   expectation p (\x. (D n x) pow 2)’ >- (Rewr' >> art []) \\
         REWRITE_TAC [expectation_def, Once EQ_SYM_EQ] \\
         MATCH_MP_TAC integral_pos_fn >> fs [prob_space_def, le_pow2]) \\
  (* Now some dirty (ext)real arithmetics, eliminating ‘Normal’ first *)
     Know ‘!n. Normal ((inv &SUC (n ** 2)) pow 2) = inv ((&n pow 2 + 1)) pow 2’
     >- (Q.X_GEN_TAC ‘n’ \\
         REWRITE_TAC [GSYM extreal_pow_def] \\
         Suff ‘Normal (inv (&SUC (n ** 2))) = inv (&n pow 2 + 1)’ >- rw [] \\
        ‘&SUC (n ** 2) <> (0 :real)’ by RW_TAC real_ss [] \\
         ASM_SIMP_TAC std_ss [GSYM extreal_inv_eq] \\
         Suff ‘Normal (&SUC (n ** 2)) = &n pow 2 + 1’ >- rw [] \\
         rw [ADD1, extreal_of_num_def, extreal_pow_def, extreal_add_def] \\
         rw [REAL_OF_NUM_POW]) >> Rewr' \\
     Q.PAT_X_ASSUM ‘!n. CARD (N n) = _’ (ONCE_REWRITE_TAC o wrap) \\
  (* applying ext_suminf_offset *)
     Q.ABBREV_TAC ‘z = \n. inv (e pow 2) * inv (&n pow 2 + 1) pow 2 * &(2 * n + 1) pow 2 * M’ \\
     Know ‘suminf z = SIGMA z (count 1) + suminf (\i. z (i + 1))’
     >- (MATCH_MP_TAC ext_suminf_offset \\
         RW_TAC std_ss [Abbr ‘z’] \\
         MATCH_MP_TAC le_mul >> art [] \\
         MATCH_MP_TAC le_mul >> reverse CONJ_TAC >- rw [le_pow2] \\
         MATCH_MP_TAC le_mul >> reverse CONJ_TAC >- rw [le_pow2] \\
         MATCH_MP_TAC le_inv >> MATCH_MP_TAC pow_pos_lt >> art []) >> Rewr' \\
     rw [Abbr ‘z’, zero_pow] \\
     Suff ‘suminf (\i. inv (e pow 2) * inv (&(i + 1) pow 2 + 1) pow 2 *
                       &(2 * (i + 1) + 1) pow 2 * M) < PosInf’
     >- (rw [GSYM lt_infty] \\
         Know ‘suminf (\i. inv (e pow 2) * inv (&(i + 1) pow 2 + 1) pow 2 *
                           &(2 * (i + 1) + 1) pow 2 * M) <> NegInf’
         >- (MATCH_MP_TAC pos_not_neginf \\
             MATCH_MP_TAC ext_suminf_pos >> rw [] \\
             MATCH_MP_TAC le_mul >> art [] \\
             MATCH_MP_TAC le_mul >> reverse CONJ_TAC >- rw [le_pow2] \\
             MATCH_MP_TAC le_mul >> reverse CONJ_TAC >- rw [le_pow2] \\
             MATCH_MP_TAC le_inv >> MATCH_MP_TAC pow_pos_lt >> art []) \\
         DISCH_TAC \\
        ‘?r. suminf (\i. inv (e pow 2) * inv (&(i + 1) pow 2 + 1) pow 2 *
                         &(2 * (i + 1) + 1) pow 2 * M) = Normal r’
           by METIS_TAC [extreal_cases] >> POP_ORW \\
         Suff ‘inv (e pow 2) * M <> PosInf’
         >- (DISCH_TAC \\
             Know ‘inv (e pow 2) * M <> NegInf’
             >- (MATCH_MP_TAC pos_not_neginf \\
                 MATCH_MP_TAC le_mul >> art [] \\
                 MATCH_MP_TAC le_inv >> MATCH_MP_TAC pow_pos_lt >> art []) \\
             DISCH_TAC \\
            ‘?z. inv (e pow 2) * M = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
             rw [extreal_add_def, extreal_not_infty]) \\
        ‘e <> NegInf’ by PROVE_TAC [lt_imp_le, pos_not_neginf] \\
        ‘?E. 0 < E /\ e = Normal E’
           by METIS_TAC [extreal_cases, extreal_lt_eq, extreal_of_num_def] >> POP_ORW \\
        ‘0 < E pow 2’ by PROVE_TAC [REAL_POW_LT] \\
        ‘E pow 2 <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] \\
         rw [extreal_pow_def, extreal_inv_eq] \\
         Suff ‘0 <= inv (E pow 2)’ >- METIS_TAC [mul_not_infty] \\
         MATCH_MP_TAC REAL_LE_INV \\
         MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
    ‘!(i :num). 2 * (i + 1) + 1 = 2 * i + 3’ by ARITH_TAC >> POP_ORW \\
    ‘!i. inv (e pow 2) * inv (&(i + 1) pow 2 + 1) pow 2 * &(2 * i + 3) pow 2 * M =
         inv (e pow 2) * M * (inv (&(i + 1) pow 2 + 1) pow 2 * &(2 * i + 3) pow 2)’
        by METIS_TAC [mul_comm, mul_assoc] >> POP_ORW \\
     Know ‘suminf
             (\i. inv (e pow 2) * M * (inv (&(i + 1) pow 2 + 1) pow 2 * &(2 * i + 3) pow 2)) =
           inv (e pow 2) * M * suminf (\i. inv (&(i + 1) pow 2 + 1) pow 2 * &(2 * i + 3) pow 2)’
     >- (HO_MATCH_MP_TAC ext_suminf_cmul \\
         CONJ_TAC >- (MATCH_MP_TAC le_mul >> art [] \\
                      MATCH_MP_TAC le_inv >> MATCH_MP_TAC pow_pos_lt >> art []) \\
         Q.X_GEN_TAC ‘n’ \\
         MATCH_MP_TAC le_mul >> rw [le_pow2]) >> Rewr' \\
    ‘e <> NegInf’ by PROVE_TAC [lt_imp_le, pos_not_neginf] \\
    ‘?E. 0 < E /\ e = Normal E’
       by METIS_TAC [extreal_cases, extreal_lt_eq, extreal_of_num_def] >> POP_ORW \\
    ‘0 < E pow 2’ by PROVE_TAC [REAL_POW_LT] \\
    ‘E pow 2 <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] \\
     rw [extreal_pow_def, extreal_inv_eq] \\
     Suff ‘suminf (\i. inv (&(i + 1) pow 2 + 1) pow 2 * &(2 * i + 3) pow 2) < PosInf’
     >- (rw [GSYM lt_infty] \\
         Know ‘suminf (\i. inv (&(i + 1) pow 2 + 1) pow 2 * &(2 * i + 3) pow 2) <> NegInf’
         >- (MATCH_MP_TAC pos_not_neginf \\
             MATCH_MP_TAC ext_suminf_pos >> rw [] \\
             MATCH_MP_TAC le_mul >> rw [le_pow2]) >> DISCH_TAC \\
        ‘?r. suminf (\i. inv (&(i + 1) pow 2 + 1) pow 2 * &(2 * i + 3) pow 2) = Normal r’
           by METIS_TAC [extreal_cases] >> POP_ORW \\
        ‘?b. M = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_mul_def, extreal_not_infty]) \\
  (* Idea: (2*n+3)^2 / (1+(n+1)^2)^2 <= (3*(n+1))^2 / (n+1)^4 = 9 / (n+1)^2 *)
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘suminf (\i. inv (&SUC i pow 2) pow 2 * (3 * &SUC i) pow 2)’ \\
     CONJ_TAC
     >- (MATCH_MP_TAC ext_suminf_mono >> rw []
         >- (MATCH_MP_TAC le_mul >> rw [le_pow2]) \\
         MATCH_MP_TAC le_mul2 \\
         CONJ_TAC >- rw [le_pow2] \\
         CONJ_TAC >- rw [le_pow2] \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC pow_le >> rw [extreal_of_num_def, extreal_mul_def]) \\
         MATCH_MP_TAC pow_le \\
         CONJ_TAC >- (MATCH_MP_TAC le_inv >> MATCH_MP_TAC lt_add >> rw [] \\
                      MATCH_MP_TAC pow_pos_lt >> rw [extreal_of_num_def]) \\
         MATCH_MP_TAC inv_le_antimono_imp \\
         CONJ_TAC >- (MATCH_MP_TAC pow_pos_lt >> rw [extreal_of_num_def]) \\
         REWRITE_TAC [ADD1] \\
         MATCH_MP_TAC le_addr_imp >> rw []) \\
    ‘!i. &SUC i <> 0’ by rw [extreal_of_num_def] \\
     rw [GSYM pow_mul] \\
     Know ‘!i. inv (&SUC i pow 2) * (3 * &SUC i) = inv (&SUC i) * &SUC i * 3 * inv (&SUC i)’
     >- (rw [pow_2] \\
        ‘&SUC i <> (0 :extreal)’ by rw [extreal_of_num_def] \\
         rw [inv_mul] >> METIS_TAC [mul_comm, mul_assoc]) >> Rewr' \\
     Know ‘!i. inv (&SUC i) * &SUC i = 1’
     >- (GEN_TAC >> MATCH_MP_TAC mul_linv_pos >> rw [extreal_of_num_def]) >> Rewr' \\
     rw [pow_mul, GSYM pow_inv] \\
    ‘(3 :extreal) pow 2 = 9’ by rw [pow_2, extreal_of_num_def, extreal_mul_def] >> POP_ORW \\
     Know ‘suminf (\i. 9 * inv (&SUC i pow 2)) = 9 * suminf (\i. inv (&SUC i pow 2))’
     >- (HO_MATCH_MP_TAC ext_suminf_cmul \\
         CONJ_TAC >- rw [extreal_of_num_def] \\
         rw [pow_inv, le_pow2]) >> Rewr' \\
    ‘suminf (\i. realinv (&SUC i pow 2)) <> PosInf’
       by METIS_TAC [harmonic_series_pow_2, lt_infty] \\
     Know ‘suminf (\i. realinv (&SUC i pow 2)) <> NegInf’
     >- (MATCH_MP_TAC pos_not_neginf \\
         MATCH_MP_TAC ext_suminf_pos >> rw [pow_inv, le_pow2]) >> DISCH_TAC \\
    ‘?r. suminf (\i. realinv (&SUC i pow 2)) = Normal r’
       by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [GSYM lt_infty, extreal_of_num_def, extreal_mul_def])
 >> DISCH_TAC
 (* pre-final stage, ‘ROOT 2 n’ is the maximal k such that n^2 < k <= (n+1)^2 *)
 >> Q.ABBREV_TAC ‘g = ROOT 2’
 >> Know ‘!k x. x IN p_space p ==>
                abs (S k x) / &SUC k <=
                (abs (S (g k ** 2) x) + abs (D (g k) x)) / &SUC (g k ** 2)’
 >- (rpt GEN_TAC >> DISCH_TAC \\
     Q.UNABBREV_TAC ‘g’ \\
     Q.ABBREV_TAC ‘n = ROOT 2 k’ \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC ‘abs (S k x) / &SUC (n ** 2)’ \\
     CONJ_TAC
     >- (Know ‘abs (S k x) / &SUC k = inv (&SUC k) * abs (S k x)’
         >- (MATCH_MP_TAC div_eq_mul_linv \\
             SIMP_TAC real_ss [extreal_of_num_def, extreal_lt_eq] \\
             MATCH_MP_TAC abs_not_infty >> rw []) >> Rewr' \\
         Know ‘abs (S k x) / &SUC (n ** 2) = inv (&SUC (n ** 2)) * abs (S k x)’
         >- (MATCH_MP_TAC div_eq_mul_linv \\
             ONCE_REWRITE_TAC [CONJ_ASSOC] \\
             CONJ_TAC >- (MATCH_MP_TAC abs_not_infty >> rw []) \\
             ASM_SIMP_TAC real_ss [extreal_of_num_def, extreal_lt_eq]) >> Rewr' \\
         MATCH_MP_TAC le_rmul_imp >> REWRITE_TAC [abs_pos] \\
         Know ‘inv (&SUC k) <= inv (&SUC (n ** 2)) <=> &SUC (n ** 2) <= &SUC k’
         >- (MATCH_MP_TAC inv_le_antimono \\
             RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq]) >> Rewr' \\
         SIMP_TAC real_ss [Abbr ‘n’, extreal_of_num_def, extreal_le_eq] \\
         PROVE_TAC [SIMP_RULE arith_ss [] (Q.SPEC ‘2’ ROOT)]) \\
     Know ‘abs (S k x) / &SUC (n ** 2) = inv (&SUC (n ** 2)) * abs (S k x)’
     >- (MATCH_MP_TAC div_eq_mul_linv \\
         SIMP_TAC real_ss [extreal_of_num_def, extreal_lt_eq] \\
         ONCE_REWRITE_TAC [CONJ_ASSOC] >> art [] \\
         MATCH_MP_TAC abs_not_infty >> rw []) >> Rewr' \\
     Know ‘(abs (S (n ** 2) x) + abs (D n x)) / &SUC (n ** 2) =
           inv (&SUC (n ** 2)) * (abs (S (n ** 2) x) + abs (D n x))’
     >- (MATCH_MP_TAC div_eq_mul_linv \\
         ONCE_REWRITE_TAC [CONJ_ASSOC] \\
         reverse CONJ_TAC >- (ASM_SIMP_TAC real_ss [extreal_of_num_def, extreal_lt_eq]) \\
        ‘?r. S (n ** 2) x = Normal r’ by METIS_TAC [extreal_cases] \\
        ‘?a. D n x = Normal a’ by METIS_TAC [extreal_cases] \\
         ASM_SIMP_TAC std_ss [extreal_abs_def, extreal_add_def,
                              extreal_not_infty]) >> Rewr' \\
     MATCH_MP_TAC le_lmul_imp \\
     CONJ_TAC >- (MATCH_MP_TAC lt_imp_le >> MATCH_MP_TAC inv_pos' \\
                  rw [extreal_of_num_def, extreal_lt_eq, extreal_not_infty]) \\
    ‘D n x = d n (f n x) x’ by PROVE_TAC [] >> POP_ORW \\
    ‘d n (f n x) x = abs (S (f n x) x - S (n ** 2) x)’ by PROVE_TAC [] >> POP_ORW \\
     REWRITE_TAC [abs_abs] \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC ‘abs (S (n ** 2) x) + abs (S k x - S (n ** 2) x)’ \\
     CONJ_TAC >- (MATCH_MP_TAC abs_triangle_sub >> rw []) \\
     Know ‘abs (S (n ** 2) x) + abs (S k x - S (n ** 2) x) <=
           abs (S (n ** 2) x) + abs (S (f n x) x - S (n ** 2) x) <=>
           abs (S k x - S (n ** 2) x) <= abs (S (f n x) x - S (n ** 2) x)’
     >- (MATCH_MP_TAC le_ladd \\
         ONCE_REWRITE_TAC [CONJ_SYM] \\
         MATCH_MP_TAC abs_not_infty >> rw []) >> Rewr' \\
    ‘abs (S k x - S (n ** 2) x) = d n k x’ by PROVE_TAC [] >> POP_ORW \\
    ‘abs (S (f n x) x - S (n ** 2) x) = d n (f n x) x’ by PROVE_TAC [] >> POP_ORW \\
    ‘d n (f n x) x = sup (IMAGE (\k. d n k x) (N n))’ by METIS_TAC [] >> POP_ORW \\
     MATCH_MP_TAC le_sup_imp' \\
     RW_TAC set_ss [Abbr ‘N’, IN_IMAGE] \\
     Q.EXISTS_TAC ‘k’ >> art [] \\
     Q.UNABBREV_TAC ‘n’ \\
     MATCH_MP_TAC logrootTheory.ROOT (* amazing *) \\
     RW_TAC arith_ss []) >> DISCH_TAC
 (* final stage *)
 >> ‘real_random_variable (\x. 0) p’ by PROVE_TAC [real_random_variable_zero]
 >> Q.PAT_X_ASSUM ‘(Z --> (\x. 0)) (almost_everywhere p)’ MP_TAC
 >> ASM_SIMP_TAC std_ss [converge_AE_def, AE_DEF, GSYM IN_NULL_SET, LIM_SEQUENTIALLY, dist]
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘N1’ STRIP_ASSUME_TAC)
 >> Q.PAT_X_ASSUM ‘(W --> (\x. 0)) (almost_everywhere p)’ MP_TAC
 >> ASM_SIMP_TAC std_ss [converge_AE_def, AE_DEF, GSYM IN_NULL_SET, LIM_SEQUENTIALLY, dist]
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘N2’ STRIP_ASSUME_TAC)
 >> qabbrev_tac ‘Y = \n x. S n x / &SUC n’
 >> Know ‘!n. real_random_variable (Y n) p’
 >- (rw [Abbr ‘Y’] \\
     Know ‘real_random_variable (\x. S n x / &SUC n) p <=>
           real_random_variable (\x. SIGMA (\i. X i x) (count1 n) / &SUC n) p’
     >- (MATCH_MP_TAC real_random_variable_cong >> rw []) >> Rewr' \\
     MATCH_MP_TAC real_random_variable_LLN' >> art [])
 >> DISCH_TAC
 >> ASM_SIMP_TAC std_ss [converge_AE_def, AE_DEF,
                         GSYM IN_NULL_SET, LIM_SEQUENTIALLY, dist]
 >> POP_ASSUM K_TAC
 >> ASM_SIMP_TAC std_ss [Abbr ‘Y’]
 >> Q.EXISTS_TAC ‘N1 UNION N2’
 >> STRONG_CONJ_TAC
 >- (MATCH_MP_TAC NULL_SET_UNION \\
     FULL_SIMP_TAC bool_ss [prob_space_def]) >> DISCH_TAC
 >> rpt STRIP_TAC
 >> ‘(m_space p DIFF (N1 UNION N2)) SUBSET (m_space p DIFF N1)’ by SET_TAC []
 >> ‘(m_space p DIFF (N1 UNION N2)) SUBSET (m_space p DIFF N2)’ by SET_TAC []
 (* clean up disturbing assumptions *)
 >> Q.PAT_X_ASSUM ‘!n x. x IN p_space p ==>
                         S n x = SIGMA (\i. X i x) (count1 n)’ K_TAC
 >> Q.PAT_X_ASSUM ‘!n. expectation p (X n) = 0’                K_TAC
 >> Q.PAT_X_ASSUM ‘!n. real_random_variable (X n) p’           K_TAC
 >> Q.PAT_X_ASSUM ‘!n. finite_second_moments p (X n)’          K_TAC
 >> Q.PAT_X_ASSUM ‘!n. variance p (X n) <= M’                  K_TAC
 >> Q.PAT_X_ASSUM ‘!n. integrable p (X n)’                     K_TAC
 >> Q.PAT_X_ASSUM ‘!i j. i <> j ==> orthogonal p (X i) (X j)’  K_TAC
 (* simplify assumptions *)
 >> Q.PAT_X_ASSUM ‘!x. x IN m_space p DIFF N1 ==> P’ (MP_TAC o Q.SPEC ‘x’)
 >> Know ‘x IN m_space p DIFF N1’ >- ASM_SET_TAC []
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM ‘!x. x IN m_space p DIFF N2 ==> P’ (MP_TAC o Q.SPEC ‘x’)
 >> Know ‘x IN m_space p DIFF N2’ >- ASM_SET_TAC []
 >> RW_TAC std_ss []
 >> FULL_SIMP_TAC bool_ss [REAL_SUB_RZERO, real_0]
 >> NTAC 3 (Q.PAT_X_ASSUM ‘_ IN null_set p’           K_TAC)
 >> ‘m_space p DIFF (N1 UNION N2) SUBSET m_space p’ by SET_TAC []
 >> ‘x IN m_space p’ by METIS_TAC [SUBSET_DEF]
 >> NTAC 2 (Q.PAT_X_ASSUM ‘_ SUBSET m_space p DIFF _’ K_TAC)
 >> NTAC 3 (Q.PAT_X_ASSUM ‘x IN m_space p DIFF _’     K_TAC)
 >> Q.PAT_X_ASSUM ‘m_space p DIFF (N1 UNION N2) SUBSET m_space p’ K_TAC
 >> Q.PAT_X_ASSUM ‘M <> PosInf’ K_TAC
 >> Q.PAT_X_ASSUM ‘M <> NegInf’ K_TAC
 >> Q.PAT_X_ASSUM ‘0 <= M’      K_TAC
 (* clean up Z and W *)
 >> Q.PAT_X_ASSUM ‘!n. real_random_variable (Z n) p’  K_TAC
 >> Q.PAT_X_ASSUM ‘!n. real_random_variable (W n) p’  K_TAC
 >> Q.PAT_X_ASSUM ‘!n. finite_second_moments p (W n)’ K_TAC
 >> qunabbrevl_tac [‘Z’, ‘W’]
 >> FULL_SIMP_TAC std_ss []
 (* translating real inequalities to extreal ones *)
 >> Know ‘!n. abs (real (S n x / &SUC n)) < e <=> abs (S n x) / &SUC n < Normal e’
 >- (Q.X_GEN_TAC ‘n’ \\
     FULL_SIMP_TAC std_ss [p_space_def] \\
    ‘?r. S n x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘&SUC n <> (0: real)’ by RW_TAC real_ss [] \\
     ASM_SIMP_TAC real_ss [extreal_of_num_def, extreal_abs_def, real_normal,
                           extreal_div_eq, extreal_lt_eq, ABS_DIV, ABS_N])
 >> Rewr'
 >> Know ‘!n e. abs (real (S (n ** 2) x / &SUC (n ** 2))) < e <=>
                abs (S (n ** 2) x) / &SUC (n ** 2) < Normal e’
 >- (rpt GEN_TAC \\
     FULL_SIMP_TAC std_ss [p_space_def] \\
    ‘?r. S (n ** 2) x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘&SUC (n ** 2) <> (0: real)’ by RW_TAC real_ss [] \\
     ASM_SIMP_TAC real_ss [extreal_of_num_def, extreal_abs_def, real_normal,
                           extreal_div_eq, extreal_lt_eq, ABS_DIV, ABS_N])
 >> DISCH_THEN ((FULL_SIMP_TAC bool_ss) o wrap)
 >> Know ‘!n e. abs (real (D n x / &SUC (n ** 2))) < e <=>
                abs (D n x) / &SUC (n ** 2) < Normal e’
 >- (rpt GEN_TAC \\
    ‘?r. D n x = Normal r’ by METIS_TAC [extreal_cases, p_space_def] >> POP_ORW \\
    ‘&SUC (n ** 2) <> (0: real)’ by RW_TAC real_ss [] \\
     ASM_SIMP_TAC real_ss [extreal_of_num_def, extreal_abs_def, real_normal,
                           extreal_div_eq, extreal_lt_eq, ABS_DIV, ABS_N])
 >> DISCH_THEN ((FULL_SIMP_TAC bool_ss) o wrap)
 (* continue estimating N *)
 >> NTAC 2 (Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘e / 2’)))
 >> Know ‘0 < e / 2’
 >- (MATCH_MP_TAC REAL_LT_DIV >> RW_TAC real_ss [])
 >> ‘!n x. x IN m_space p ==>
           D n x <> PosInf /\ D n x <> NegInf’ by METIS_TAC [p_space_def]
 >> Q.PAT_X_ASSUM (* to prevent `D n x` from being rewritten *)
      ‘!n x. n ** 2 <= f n x /\ f n x < SUC n ** 2 /\ D n x = d n (f n x) x’ K_TAC
 >> RW_TAC std_ss []
 >> rename1 ‘!n. m1 <= n ==> abs (S (n ** 2) x) / &SUC (n ** 2) < Normal (e / 2)’
 >> rename1 ‘!n. m2 <= n ==> abs (D n x) / &SUC (n ** 2) < Normal (e / 2)’
 (* final-final *)
 >> Q.EXISTS_TAC ‘(m1 + m2) ** 2’
 >> RW_TAC std_ss []
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC ‘(abs (S (g n ** 2) x) + abs (D (g n) x)) / &SUC (g n ** 2)’
 >> CONJ_TAC
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> art [p_space_def])
 >> Q.PAT_X_ASSUM ‘!k x. x IN p_space p ==> abs (S k x) / &SUC k <= _’ K_TAC
 >> Q.ABBREV_TAC ‘k = g n’
 >> Know ‘(abs (S (k ** 2) x) + abs (D k x)) / &SUC (k ** 2) =
           abs (S (k ** 2) x) / &SUC (k ** 2) + abs (D k x) / &SUC (k ** 2)’
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC div_add \\
     ONCE_REWRITE_TAC [CONJ_ASSOC] \\
     FULL_SIMP_TAC std_ss [p_space_def] \\
     CONJ_TAC >- (MATCH_MP_TAC abs_not_infty >> rw []) \\
     ONCE_REWRITE_TAC [CONJ_ASSOC] \\
     CONJ_TAC >- (MATCH_MP_TAC abs_not_infty >> rw []) \\
     RW_TAC real_ss [extreal_of_num_def, extreal_11]) >> Rewr'
 >> ‘Normal e = Normal (e / 2) + Normal (e / 2)’
       by METIS_TAC [extreal_add_def, REAL_HALF_DOUBLE] >> POP_ORW
 >> MATCH_MP_TAC lt_add2
 >> qunabbrevl_tac [‘k’, ‘g’]
 >> CONJ_TAC >> FIRST_X_ASSUM MATCH_MP_TAC (* 2 subgoals, similar tactics *)
 >| [ (* goal 1 (of 2) *)
      Know ‘m1 = ROOT 2 (m1 ** 2)’
      >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
          MATCH_MP_TAC ROOT_EXP >> RW_TAC arith_ss []) >> Rewr' \\
      irule ROOT_LE_MONO >> RW_TAC arith_ss [] \\
      MATCH_MP_TAC LESS_EQ_TRANS \\
      Q.EXISTS_TAC ‘(m1 + m2) ** 2’ >> rw [],
      (* goal 2 (of 2) *)
      Know ‘m2 = ROOT 2 (m2 ** 2)’
      >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
          MATCH_MP_TAC ROOT_EXP >> RW_TAC arith_ss []) >> Rewr' \\
      irule ROOT_LE_MONO >> RW_TAC arith_ss [] \\
      MATCH_MP_TAC LESS_EQ_TRANS \\
      Q.EXISTS_TAC ‘(m1 + m2) ** 2’ >> rw [] ]
QED

(* ------------------------------------------------------------------------- *)
(*  The Weak Law of Large Numbers for IID random variables                   *)
(* ------------------------------------------------------------------------- *)

Theorem equivalent_comm :
    !X Y. equivalent p (X :num -> 'a -> extreal) Y <=> equivalent p Y X
Proof
    rw [equivalent_def]
 >> Suff ‘!n. {x | x IN p_space p /\ X n x <> Y n x} =
              {x | x IN p_space p /\ Y n x <> X n x}’ >- Rewr
 >> rw [Once EXTENSION]
 >> METIS_TAC []
QED

Theorem equivalent_events :
    !p X Y. prob_space p /\
            (!n. real_random_variable (X n) p) /\
            (!n. real_random_variable (Y n) p) ==>
            !n. {x | x IN p_space p /\ X n x <> Y n x} IN events p
Proof
    RW_TAC std_ss [events_def, p_space_def, prob_space_def]
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
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
           ((\n x. SIGMA (\i. X i x - Y i x) (count1 n)) --> Z) (almost_everywhere p)
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘Z = \n x. SIGMA (\i. X i x - Y i x) (count1 n)’
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
         POP_ORW >> REWRITE_TAC [GSYM FN_DECOMP]) \\
     DISCH_THEN (ONCE_REWRITE_TAC o wrap o BETA_RULE) \\
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
         Q.UNABBREV_TAC `g` >> BETA_TAC \\
         STRIP_ASSUME_TAC
           (Q.SPECL [`m_space p DIFF N`, `x`] indicator_fn_normal) >> art [] \\
         Suff `X n x - Y n x <> PosInf` >- METIS_TAC [mul_not_infty] \\
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
 (* stage work *)
 >> RW_TAC std_ss [Abbr ‘Z’, converge_AE, AE_THM, GSYM IN_NULL_SET, almost_everywhere_def]
 >> Q.EXISTS_TAC `N`
 >> RW_TAC std_ss [EXTREAL_LIM_SEQUENTIALLY, indicator_fn_def, mul_rone, GSYM p_space_def]
 >> Q.EXISTS_TAC `f x`
 >> RW_TAC std_ss []
 >> Know `SIGMA (\i. X i x - Y i x) (count1 n) =
          SIGMA (\i. X i x - Y i x) ((count1 n) DIFF (from (f x)))`
 >- (irule EXTREAL_SUM_IMAGE_ZERO_DIFF \\
     fs [real_random_variable_def, IN_FROM] \\
     DISJ2_TAC >> RW_TAC std_ss [sub_not_infty]) >> Rewr'
 >> Suff `count1 n DIFF (from (f x)) = count (f x)`
 >- (Rewr' >> rw [METRIC_SAME])
 >> RW_TAC set_ss [Once EXTENSION, IN_FROM, IN_COUNT]
 >> rw []
QED

Theorem mono_increasing_passing_zero :
   !a. mono_increasing a /\ sup (IMAGE a UNIV) = PosInf ==> ?n. 0 < a n
Proof
    rw [ext_mono_increasing_def]
 >> CCONTR_TAC
 >> fs [extreal_lt_def]
 >> Know ‘sup (IMAGE a UNIV) <= 0’
 >- (rw [sup_le'] >> art [])
 >> rw []
QED

(* Theorem 5.2.1 (2) [2, p.113], more generalized for SLLN_IID *)
Theorem equivalent_thm2' :
    !b a p X Y. prob_space p /\ equivalent p X Y /\
               (!n. real_random_variable (X n) p) /\
               (!n. real_random_variable (Y n) p) /\
                mono_increasing a /\ (sup (IMAGE a UNIV) = PosInf) /\
               (!m n. m <= n ==> b m <= b n) /\ (!n. ?i. n <= b i) ==>
          ((\n x. SIGMA (\i. X i x - Y i x) (count (b n)) / a n) --> (\x. 0))
           (almost_everywhere p)
Proof
    rpt STRIP_TAC
 (* applying equivalent_lemma *)
 >> Know `?N f. N IN null_set p /\
               !x. x IN p_space p DIFF N ==> !n. f x <= n ==> (X n x - Y n x = 0)`
 >- (MATCH_MP_TAC equivalent_lemma >> art [])
 >> STRIP_TAC
 >> ‘real_random_variable (\x. 0) p’ by PROVE_TAC [real_random_variable_zero]
 >> Know `!n x. x IN p_space p ==>
                SIGMA (\i. X i x - Y i x) (count n) <> PosInf /\
                SIGMA (\i. X i x - Y i x) (count n) <> NegInf`
 >- (rpt GEN_TAC >> DISCH_TAC \\
     CONJ_TAC >| [ MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF,
                   MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF ] \\
     fs [real_random_variable_def] \\
     rw [sub_not_infty])
 >> DISCH_TAC
 >> qabbrev_tac ‘Z = \n x. SIGMA (\i. X i x - Y i x) (count (b n)) / a n’
 (* 1. if (a n) ever reached PosInf, use that n directly *)
 >> reverse (Cases_on `!n. a n <> PosInf`)
 >- (FULL_SIMP_TAC std_ss [] \\
     Know ‘(Z         --> (\x. 0)) (almost_everywhere p) <=>
           ((\x n. 0) --> (\x. 0)) (almost_everywhere p)’
     >- (MATCH_MP_TAC converge_AE_cong \\
         Q.EXISTS_TAC `n` \\
         qx_genl_tac [‘m’, ‘x’] >> STRIP_TAC \\
         rw [Abbr ‘Z’] \\
         Know `a n <= a m` >- fs [ext_mono_increasing_def] \\
         ASM_REWRITE_TAC [le_infty] >> Rewr' \\
        `?r. SIGMA (\i. X i x - Y i x) (count (b m)) = Normal r`
           by METIS_TAC [extreal_cases] \\
         rw [extreal_div_def, real_normal, extreal_of_num_def]) >> Rewr' \\
     MATCH_MP_TAC converge_AE_const >> art [])
 >> ‘?n0. 0 < a n0’ by METIS_TAC [mono_increasing_passing_zero]
 >> RW_TAC std_ss [converge_AE, AE_THM, GSYM IN_NULL_SET, almost_everywhere_def,
                   GSYM p_space_def]
 >> Q.EXISTS_TAC `N` >> art []
 >> rpt STRIP_TAC
 >> FULL_SIMP_TAC std_ss [real_random_variable_def, ext_mono_increasing_def]
 >> Know ‘x IN p_space p’
 >- (‘p_space p DIFF N SUBSET p_space p’ by SET_TAC [] \\
     METIS_TAC [SUBSET_DEF])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM `!x. x IN p_space p DIFF N ==> P` (MP_TAC o (Q.SPEC `x`))
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM ‘!n. ?i. n <= b i’ (STRIP_ASSUME_TAC o (Q.SPEC ‘f x’))
 (* NOTE: Now starting from ‘b i’, ‘X n x - Y n x = 0’. Even the SIGMA contains some
    non-zero items, eventually it can be arbitrarily small. And ‘a i <> PosInf’, thus
    with indexes larger than ‘z’, ‘a i’ is positive infinite, making ‘/ a n’ specified.
  *)
 >> Know ‘((\n. Z n x)        -->      0) sequentially <=>
          (real o (\n. Z n x) --> real 0) sequentially’
 >- (MATCH_MP_TAC extreal_lim_sequentially_eq >> simp [] \\
     Q.EXISTS_TAC ‘n0’ >> Q.X_GEN_TAC ‘n’ >> DISCH_TAC \\
     simp [Abbr ‘Z’] \\
     Know ‘0 < a n’
     >- (MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC ‘a n0’ >> art [] \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> DISCH_TAC \\
    ‘a n <> 0’ by PROVE_TAC [lt_imp_ne] \\
     Know ‘a n <> NegInf’
     >- (MATCH_MP_TAC pos_not_neginf \\
         MATCH_MP_TAC lt_imp_le >> art []) >> DISCH_TAC \\
    ‘?r. r <> 0 /\ a n = Normal r’ by METIS_TAC [extreal_cases, extreal_of_num_def] \\
     POP_ORW \\
     Know ‘SIGMA (\i. X i x - Y i x) (count (b n)) <> PosInf’
     >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> rw [] \\
         rename1 ‘X k x - Y k x <> PosInf’ \\
         METIS_TAC [sub_not_infty]) >> DISCH_TAC \\
     Know ‘SIGMA (\i. X i x - Y i x) (count (b n)) <> NegInf’
     >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF >> rw [] \\
         rename1 ‘X k x - Y k x <> NegInf’ \\
         METIS_TAC [sub_not_infty]) >> DISCH_TAC \\
    ‘?z. SIGMA (\i. X i x - Y i x) (count (b n)) = Normal z’ by METIS_TAC [extreal_cases] \\
     simp [extreal_div_eq])
 >> Rewr'
 >> RW_TAC std_ss [LIM_SEQUENTIALLY, dist, Abbr ‘Z’, real_0, REAL_SUB_RZERO]
 >> `e <> 0` by PROVE_TAC [REAL_LT_IMP_NE]
 (* now estimating N *)
 >> Know `?k. abs (SIGMA (\i. X i x - Y i x) (count (b i))) / Normal e < a k`
 >- (CCONTR_TAC >> FULL_SIMP_TAC std_ss [] \\
     Know `sup (IMAGE a UNIV) <=
           abs (SIGMA (\i. X i x - Y i x) (count (b i))) / Normal e`
     >- (RW_TAC set_ss [sup_le'] >> fs [extreal_lt_def]) >> art [] \\
    `?r. SIGMA (\i. X i x - Y i x) (count (b i)) = Normal r`
        by METIS_TAC [extreal_cases] >> art [] \\
     ASM_SIMP_TAC std_ss [extreal_abs_def, extreal_div_eq, extreal_le_def])
 >> STRIP_TAC
 >> Q.EXISTS_TAC `MAX k i`
 >> RW_TAC std_ss [MAX_LE]
 >> Know `0 <= abs (SIGMA (\i. X i x - Y i x) (count (b i))) / Normal e`
 >- (MATCH_MP_TAC le_div >> art [abs_pos]) >> DISCH_TAC
 >> `0 < a k` by PROVE_TAC [let_trans]
 >> `0 < a n` by PROVE_TAC [lte_trans]
 (* reduce ‘count (b n)’ to ‘count (f x)’ *)
 >> Know `SIGMA (\i. X i x - Y i x) (count (b n)) =
          SIGMA (\i. X i x - Y i x) ((count (b n)) DIFF (from (f x)))`
 >- (irule EXTREAL_SUM_IMAGE_ZERO_DIFF >> fs [IN_FROM] \\
     DISJ2_TAC >> RW_TAC std_ss [sub_not_infty]) >> Rewr'
 >> Know `count (b n) DIFF (from (f x)) = count (f x)`
 >- (RW_TAC set_ss [Once EXTENSION, IN_FROM, IN_COUNT] \\
     EQ_TAC >> rw [] \\
     MATCH_MP_TAC LESS_LESS_EQ_TRANS \\
     Q.EXISTS_TAC ‘f x’ >> art [] \\
     MATCH_MP_TAC LESS_EQ_TRANS \\
     Q.EXISTS_TAC ‘b i’ >> art [] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> Rewr'
 >> Know `abs (real (SIGMA (\i. X i x - Y i x) (count (f x)) / a n)) < e <=>
          abs (SIGMA (\i. X i x - Y i x) (count (f x)) / a n) < Normal e`
 >- (`?r. SIGMA (\i. X i x - Y i x) (count (f x)) = Normal r`
         by METIS_TAC [extreal_cases] >> POP_ORW \\
     `a n <> NegInf` by PROVE_TAC [pos_not_neginf, lt_imp_le] \\
     `?z. a n = Normal z` by METIS_TAC [extreal_cases] >> art [] \\
     `a n <> 0` by PROVE_TAC [lt_imp_ne] \\
     `z <> 0` by METIS_TAC [extreal_of_num_def, extreal_11] \\
     ASM_SIMP_TAC real_ss [extreal_abs_def, real_normal, extreal_div_eq,
                           extreal_lt_eq, ABS_DIV])
 >> Rewr'
 >> Know `abs (SIGMA (\i. X i x - Y i x) (count (f x)) / a n) =
          abs (SIGMA (\i. X i x - Y i x) (count (f x))) / abs (a n)`
 >- (MATCH_MP_TAC abs_div >> simp [] \\
     PROVE_TAC [lt_imp_ne]) >> Rewr'
 >> Know `abs (a n) = a n`
 >- (REWRITE_TAC [abs_refl] \\
     MATCH_MP_TAC lt_imp_le >> art []) >> Rewr'
 >> `a n <> NegInf` by PROVE_TAC [pos_not_neginf, lt_imp_le]
 >> `?z. a n = Normal z` by METIS_TAC [extreal_cases] >> art []
 >> Know `abs (SIGMA (\i. X i x - Y i x) (count (f x))) / Normal z < Normal e <=>
          abs (SIGMA (\i. X i x - Y i x) (count (f x))) / Normal e < Normal z`
 >- (MATCH_MP_TAC EQ_TRANS \\
     Q.EXISTS_TAC `abs (SIGMA (\i. X i x - Y i x) (count (f x))) < Normal e * Normal z` \\
     CONJ_TAC >| (* 2 subgoals, similar tactics *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC lt_ldiv \\
       METIS_TAC [extreal_of_num_def, extreal_lt_eq],
       (* goal 2 (of 2) *)
       ONCE_REWRITE_TAC [mul_comm] \\
       MATCH_MP_TAC EQ_SYM \\
       MATCH_MP_TAC lt_ldiv >> art [] ]) >> Rewr'
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
 (* reduce also ‘count (b i)’ to ‘count (f x)’ *)
 >> Know `SIGMA (\i. X i x - Y i x) (count (b i)) =
          SIGMA (\i. X i x - Y i x) ((count (b i)) DIFF (from (f x)))`
 >- (irule EXTREAL_SUM_IMAGE_ZERO_DIFF >> fs [IN_FROM] \\
     DISJ2_TAC >> RW_TAC std_ss [sub_not_infty])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> Know `count (b i) DIFF (from (f x)) = count (f x)`
 >- (RW_TAC set_ss [Once EXTENSION, IN_FROM, IN_COUNT] \\
     EQ_TAC >> rw [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> MATCH_MP_TAC lte_trans
 >> Q.EXISTS_TAC `a k` >> art []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

(* Theorem 5.2.1 (2) [2, p.113], the original version *)
Theorem equivalent_thm2 :
    !a p X Y. prob_space p /\ equivalent p X Y /\
             (!n. real_random_variable (X n) p) /\
             (!n. real_random_variable (Y n) p) /\
              mono_increasing a /\ (sup (IMAGE a UNIV) = PosInf) ==>
       ((\n x. SIGMA (\i. X i x - Y i x) (count1 n) / (a n)) --> (\x. 0))
          (almost_everywhere p)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘SUC’, ‘a’, ‘p’, ‘X’, ‘Y’] equivalent_thm2')
 >> Suff ‘(!m n. m <= n ==> SUC m <= SUC n) /\ (!n. ?i. n <= SUC i)’ >- rw []
 >> rw []
 >> Q.EXISTS_TAC ‘n’ >> rw []
QED

(* Corollary of Theorem 5.2.1 [2, p.113] *)
Theorem equivalent_thm3 :
    !a p X Y Z. prob_space p /\ equivalent p X Y /\
               (!n. real_random_variable (X n) p) /\
               (!n. real_random_variable (Y n) p) /\
                real_random_variable Z p /\
               (!n. 0 < a n /\ a n < PosInf) /\
                mono_increasing a /\ sup (IMAGE a UNIV) = PosInf /\
       ((\n x. SIGMA (\i. X i x) (count1 n) / a n) --> Z) (in_probability p) ==>
       ((\n x. SIGMA (\i. Y i x) (count1 n) / a n) --> Z) (in_probability p)
Proof
    rpt STRIP_TAC
 >> Know `!W m x. (!n. real_random_variable (W n) p) /\ x IN p_space p ==>
                  SIGMA (\i. W i x) (count m) <> PosInf /\
                  SIGMA (\i. W i x) (count m) <> NegInf`
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
 >> Know ‘!W k. (!n. real_random_variable (W n) p) ==>
                real_random_variable (\x. SIGMA (\i. W i x) (count (SUC k)) / a k) p’
 >- (rpt GEN_TAC >> DISCH_TAC \\
     Know ‘real_random_variable (\x. SIGMA (\i. W i x) (count (SUC k)) / a k) p <=>
           real_random_variable (\x. inv (a k) * SIGMA (\i. W i x) (count (SUC k))) p’
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
       qexistsl_tac [‘\x. SIGMA (\i. W i x) (count (SUC k))’, ‘inv r’] \\
       FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, events_def] >> simp [] \\
       MATCH_MP_TAC (INST_TYPE [“:'b” |-> “:num”] IN_MEASURABLE_BOREL_SUM) >> rw [] \\
       qexistsl_tac [‘W’, ‘count (SUC k)’] >> rw [FINITE_COUNT, IN_COUNT] \\
       FULL_SIMP_TAC std_ss [real_random_variable, p_space_def, events_def],
       (* goal 2 (of 3) *)
      ‘?z. SIGMA (\i. W i x) (count (SUC k)) = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
       rw [extreal_mul_def, extreal_not_infty],
       (* goal 3 (of 3) *)
      ‘?z. SIGMA (\i. W i x) (count (SUC k)) = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
       rw [extreal_mul_def, extreal_not_infty] ])
 >> DISCH_TAC
 >> Know ‘!n x. x IN p_space p ==> SIGMA (\i. X i x - Y i x) (count1 n) <> PosInf’
 >- (rpt GEN_TAC >> DISCH_TAC \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> art [FINITE_COUNT] \\
     Q.X_GEN_TAC ‘i’ >> rw [] \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
     METIS_TAC [sub_not_infty])
 >> DISCH_TAC
 >> Know ‘!n x. x IN p_space p ==> SIGMA (\i. X i x - Y i x) (count1 n) <> NegInf’
 >- (rpt GEN_TAC >> DISCH_TAC \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF >> art [FINITE_COUNT] \\
     Q.X_GEN_TAC ‘i’ >> rw [] \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
     METIS_TAC [sub_not_infty])
 >> DISCH_TAC
 (* applying equivalent_thm2 *)
 >> Q.ABBREV_TAC ‘A = \n x. SIGMA (\i. X i x) (count1 n) / a n’
 >> Q.ABBREV_TAC ‘B = \n x. SIGMA (\i. X i x - Y i x) (count1 n) / a n’
 >> ‘!n. real_random_variable (A n) p’ by rw [Abbr ‘A’]
 >> Know ‘!n. real_random_variable (B n) p’
 >- (RW_TAC std_ss [Abbr ‘B’] \\
     Know ‘real_random_variable (\x. SIGMA (\i. X i x - Y i x) (count1 n) / a n) p <=>
           real_random_variable (\x. inv (a n) * SIGMA (\i. X i x - Y i x) (count1 n)) p’
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
       qexistsl_tac [‘\x. SIGMA (\i. X i x - Y i x) (count1 n)’, ‘inv r’] \\
       FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, events_def] \\
       STRONG_CONJ_TAC >- FULL_SIMP_TAC std_ss [measure_space_def] \\
       DISCH_TAC \\
       MATCH_MP_TAC (INST_TYPE [“:'b” |-> “:num”] IN_MEASURABLE_BOREL_SUM) >> rw [] \\
       qexistsl_tac [‘\i x. X i x - Y i x’, ‘count1 n’] \\
       rw [FINITE_COUNT, IN_COUNT] >| (* 2 subgoals *)
       [ (* goal 1.1 (of 2) *)
         MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
         qexistsl_tac [‘X i’, ‘Y i’] \\
         FULL_SIMP_TAC std_ss [real_random_variable, p_space_def, events_def, space_def],
         (* goal 1.2 (of 2) *)
         FULL_SIMP_TAC std_ss [real_random_variable, p_space_def, events_def] \\
         METIS_TAC [sub_not_infty] ],
       (* goal 2 (of 3) *)
      ‘?z. SIGMA (\i. X i x - Y i x) (count1 n) = Normal z’
         by METIS_TAC [extreal_cases] >> POP_ORW \\
       rw [extreal_mul_def, extreal_not_infty],
       (* goal 3 (of 3) *)
      ‘?z. SIGMA (\i. X i x - Y i x) (count1 n) = Normal z’
         by METIS_TAC [extreal_cases] >> POP_ORW \\
       rw [extreal_mul_def, extreal_not_infty] ])
 >> DISCH_TAC
 >> Know ‘(B --> (\x. 0)) (in_probability p)’
 >- (MATCH_MP_TAC converge_AE_imp_PR' >> art [] \\
     Q.UNABBREV_TAC ‘B’ >> MATCH_MP_TAC equivalent_thm2 >> art [])
 >> DISCH_TAC
 (* applying converge_PR_sub *)
 >> Suff ‘((\n x. SIGMA (\i. Y i x) (count1 n) / a n) --> Z) (in_probability p) <=>
          ((\n x. A n x - B n x) --> (\x. Z x - (\x. 0) x)) (in_probability p)’
 >- (Rewr' \\
     MATCH_MP_TAC converge_PR_sub >> rw [real_random_variable_zero])
 (* applying converge_PR_cong_full *)
 >> MATCH_MP_TAC converge_PR_cong_full
 >> Q.EXISTS_TAC ‘0’
 >> RW_TAC arith_ss [sub_rzero]
 >> FULL_SIMP_TAC std_ss [Abbr ‘A’, Abbr ‘B’]
 >> Suff ‘SIGMA (\i. Y i x) (count1 n) =
          SIGMA (\i. X i x) (count1 n) -
          SIGMA (\i. X i x - Y i x) (count1 n)’
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
Theorem equivalent_thm3' :
    !p X Y Z. prob_space p /\ equivalent p X Y /\
             (!n. real_random_variable (X n) p) /\
             (!n. real_random_variable (Y n) p) /\
              real_random_variable Z p /\
       ((\n x. SIGMA (\i. X i x) (count1 n) / &SUC n) --> Z) (in_probability p) ==>
       ((\n x. SIGMA (\i. Y i x) (count1 n) / &SUC n) --> Z) (in_probability p)
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

Theorem equivalent_thm4 :
    !p X Y Z a b. prob_space p /\ equivalent p X Y /\
                 (!n. real_random_variable (X n) p) /\
                 (!n. real_random_variable (Y n) p) /\
                  real_random_variable Z p /\
                 (!n. 0 < a n /\ a n < PosInf) /\
                 mono_increasing a /\ sup (IMAGE a UNIV) = PosInf /\
                 (!m n. m <= n ==> b m <= b n) /\ (!n. ?i. n <= b i) /\
       ((\n x. SIGMA (\i. X i x) (count (b n)) / a n) --> Z) (almost_everywhere p) ==>
       ((\n x. SIGMA (\i. Y i x) (count (b n)) / a n) --> Z) (almost_everywhere p)
Proof
    rpt STRIP_TAC
 >> Know `!W m x. (!n. real_random_variable (W n) p) /\ x IN p_space p ==>
                  SIGMA (\i. W i x) (count m) <> PosInf /\
                  SIGMA (\i. W i x) (count m) <> NegInf`
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
 >> Know ‘!W n k. (!n. real_random_variable (W n) p) ==>
                  real_random_variable (\x. SIGMA (\i. W i x) (count n) / a k) p’
 >- (rpt GEN_TAC >> DISCH_TAC \\
     Know ‘real_random_variable (\x. SIGMA (\i. W i x) (count n) / a k) p <=>
           real_random_variable (\x. inv (a k) * SIGMA (\i. W i x) (count n)) p’
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
       qexistsl_tac [‘\x. SIGMA (\i. W i x) (count n)’, ‘inv r’] \\
       FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, events_def] \\
       CONJ_TAC >- FULL_SIMP_TAC std_ss [measure_space_def] \\
       MATCH_MP_TAC (INST_TYPE [“:'b” |-> “:num”] IN_MEASURABLE_BOREL_SUM) >> rw [] \\
       qexistsl_tac [‘W’, ‘count n’] >> rw [FINITE_COUNT, IN_COUNT] \\
       FULL_SIMP_TAC std_ss [real_random_variable, p_space_def, events_def],
       (* goal 2 (of 3) *)
      ‘?z. SIGMA (\i. W i x) (count n) = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
       rw [extreal_mul_def, extreal_not_infty],
       (* goal 3 (of 3) *)
      ‘?z. SIGMA (\i. W i x) (count n) = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
       rw [extreal_mul_def, extreal_not_infty] ])
 >> DISCH_TAC
 >> Know ‘!n x. x IN p_space p ==> SIGMA (\i. X i x - Y i x) (count n) <> PosInf’
 >- (rpt GEN_TAC >> DISCH_TAC \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> art [FINITE_COUNT] \\
     Q.X_GEN_TAC ‘i’ >> rw [] \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
     METIS_TAC [sub_not_infty])
 >> DISCH_TAC
 >> Know ‘!n x. x IN p_space p ==> SIGMA (\i. X i x - Y i x) (count n) <> NegInf’
 >- (rpt GEN_TAC >> DISCH_TAC \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF >> art [FINITE_COUNT] \\
     Q.X_GEN_TAC ‘i’ >> rw [] \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
     METIS_TAC [sub_not_infty])
 >> DISCH_TAC
 (* applying equivalent_thm2' *)
 >> Q.ABBREV_TAC ‘A = \n x. SIGMA (\i. X i x) (count (b n)) / a n’
 >> Q.ABBREV_TAC ‘B = \n x. SIGMA (\i. X i x - Y i x) (count (b n)) / a n’
 >> ‘!n. real_random_variable (A n) p’ by rw [Abbr ‘A’]
 >> Know ‘!n. real_random_variable (B n) p’
 >- (RW_TAC std_ss [Abbr ‘B’] \\
     Know ‘real_random_variable (\x. SIGMA (\i. X i x - Y i x) (count (b n)) / a n) p <=>
           real_random_variable (\x. inv (a n) * SIGMA (\i. X i x - Y i x) (count (b n))) p’
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
       qexistsl_tac [‘\x. SIGMA (\i. X i x - Y i x) (count (b n))’, ‘inv r’] \\
       FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, events_def] \\
       STRONG_CONJ_TAC >- FULL_SIMP_TAC std_ss [measure_space_def] \\
       DISCH_TAC \\
       MATCH_MP_TAC (INST_TYPE [“:'b” |-> “:num”] IN_MEASURABLE_BOREL_SUM) >> rw [] \\
       qexistsl_tac [‘\i x. X i x - Y i x’, ‘count (b n)’] \\
       rw [FINITE_COUNT, IN_COUNT] >| (* 2 subgoals *)
       [ (* goal 1.1 (of 2) *)
         MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
         qexistsl_tac [‘X i’, ‘Y i’] \\
         FULL_SIMP_TAC std_ss [real_random_variable, p_space_def, events_def, space_def],
         (* goal 1.2 (of 2) *)
         FULL_SIMP_TAC std_ss [real_random_variable, p_space_def, events_def] \\
         METIS_TAC [sub_not_infty] ],
       (* goal 2 (of 3) *)
      ‘?z. SIGMA (\i. X i x - Y i x) (count (b n)) = Normal z’
         by METIS_TAC [extreal_cases] >> POP_ORW \\
       rw [extreal_mul_def, extreal_not_infty],
       (* goal 3 (of 3) *)
      ‘?z. SIGMA (\i. X i x - Y i x) (count (b n)) = Normal z’
         by METIS_TAC [extreal_cases] >> POP_ORW \\
       rw [extreal_mul_def, extreal_not_infty] ])
 >> DISCH_TAC
 >> Know ‘(B --> (\x. 0)) (almost_everywhere p)’
 >- (Q.UNABBREV_TAC ‘B’ \\
     MATCH_MP_TAC equivalent_thm2' >> art [])
 >> DISCH_TAC
 (* applying converge_PR_sub *)
 >> Suff ‘((\n x. SIGMA (\i. Y i x) (count (b n)) / a n) --> Z) (almost_everywhere p) <=>
          ((\n x. A n x - B n x) --> (\x. Z x - (\x. 0) x)) (almost_everywhere p)’
 >- (Rewr' \\
     MATCH_MP_TAC converge_AE_sub >> rw [real_random_variable_zero])
 (* applying converge_PR_cong_full *)
 >> MATCH_MP_TAC converge_AE_cong_full
 >> Q.EXISTS_TAC ‘0’
 >> RW_TAC arith_ss [sub_rzero]
 >> FULL_SIMP_TAC std_ss [Abbr ‘A’, Abbr ‘B’]
 >> Suff ‘SIGMA (\i. Y i x) (count (b n)) =
          SIGMA (\i. X i x) (count (b n)) -
          SIGMA (\i. X i x - Y i x) (count (b n))’
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

(* This lemma will eliminate ‘LLN’ in WLLN_IID *)
Theorem LLN_alt_converge_PR_IID :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) /\
          identical_distribution p X Borel UNIV /\ integrable p (X 0) ==>
         (LLN p X in_probability <=>
          ((\n x. SIGMA (\i. X i x) (count1 n) / &SUC n) --> (\x. expectation p (X 0)))
           (in_probability p))
Proof
    rw [LLN_def]
 >> ‘real_random_variable (\x. 0) p’ by PROVE_TAC [real_random_variable_zero]
 >> qabbrev_tac ‘Z = \n x. SIGMA (\i. X i x) (count1 n)’
 >> simp []
 >> ‘!n. (\x. Z n x) = Z n’ by rw [FUN_EQ_THM] >> POP_ORW
 >> qabbrev_tac ‘W = \n x. (Z n x - expectation p (Z n)) / &SUC n’
 >> Know ‘!n. integrable p (X n)’
 >- (MATCH_MP_TAC identical_distribution_integrable >> fs [real_random_variable_def])
 >> DISCH_TAC
 >> Know ‘!n. real_random_variable (W n) p’
 >- (rw [Abbr ‘W’] \\
     MATCH_MP_TAC real_random_variable_LLN \\
     Q.EXISTS_TAC ‘X’ >> rw [])
 >> DISCH_TAC
 >> qabbrev_tac ‘Y = \n x. Z n x / &SUC n’
 >> Know ‘!n. real_random_variable (Y n) p’
 >- (rw [Abbr ‘Y’, Abbr ‘Z’] \\
     MATCH_MP_TAC real_random_variable_LLN' >> art [])
 >> DISCH_TAC
 >> Know ‘real_random_variable (\x. expectation p (X 0)) p’
 >- (MATCH_MP_TAC real_random_variable_const >> art [] \\
     MATCH_MP_TAC integrable_imp_finite_expectation >> art [])
 >> DISCH_TAC
 >> RW_TAC std_ss [converge_PR_def, sub_rzero]
 >> simp [Abbr ‘W’, Abbr ‘Y’]
 >> Suff ‘!e n. {x | x IN p_space p /\
                     e < abs ((Z n x - expectation p (Z n)) / &SUC n)} =
                {x | x IN p_space p /\
                     e < abs (Z n x / &SUC n - expectation p (X 0))}’ >- Rewr
 >> rpt GEN_TAC
 >> Suff ‘!x. x IN p_space p ==>
              (Z n x - expectation p (Z n)) / &SUC n =
              Z n x / &SUC n - expectation p (X 0)’
 >- (rw [Once EXTENSION] >> METIS_TAC [])
 >> rpt STRIP_TAC
 >> Know ‘!n. expectation p (Z n) = SIGMA (\i. expectation p (X i)) (count1 n)’
 >- (rw [expectation_def, Abbr ‘Z’] \\
     MATCH_MP_TAC integral_sum \\
     fs [FINITE_COUNT, prob_space_def, real_random_variable_def, p_space_def] \\
     rpt STRIP_TAC \\
     MATCH_MP_TAC identical_distribution_integrable >> rw [prob_space_def])
 >> Q.ABBREV_TAC ‘M = expectation p (X 0)’
 >> Know ‘!n. expectation p (X n) = M’
 >- (GEN_TAC >> Q.UNABBREV_TAC ‘M’ \\
     MATCH_MP_TAC identical_distribution_expectation \\
     FULL_SIMP_TAC std_ss [real_random_variable_def])
 >> RW_TAC std_ss []
 >> Know ‘SIGMA (\i. M) (count1 n) = &CARD (count1 n) * (\i. M) (0 :num)’
 >- (irule (INST_TYPE [“:'a” |-> “:num”] EXTREAL_SUM_IMAGE_FINITE_SAME) \\
     rw [IN_COUNT, FINITE_COUNT]) >> Rewr'
 >> rw [CARD_COUNT]
 >> Know ‘!n x. x IN p_space p ==> Z n x <> PosInf’
 >- (RW_TAC std_ss [Abbr ‘Z’] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
     FULL_SIMP_TAC std_ss [real_random_variable_def, FINITE_COUNT, IN_COUNT])
 >> DISCH_TAC
 >> Know ‘!n x. x IN p_space p ==> Z n x <> NegInf’
 >- (RW_TAC std_ss [Abbr ‘Z’] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
     FULL_SIMP_TAC std_ss [real_random_variable_def, FINITE_COUNT, IN_COUNT])
 >> DISCH_TAC
 >> Know ‘M <> PosInf /\ M <> NegInf’
 >- (ASM_SIMP_TAC std_ss [expectation_def, Abbr ‘M’] \\
     MATCH_MP_TAC integrable_finite_integral \\
     FULL_SIMP_TAC std_ss [prob_space_def])
 >> STRIP_TAC
 >> Know ‘(Z n x - &SUC n * M) / &SUC n = inv (&SUC n) * (Z n x - &SUC n * M)’
 >- (MATCH_MP_TAC div_eq_mul_linv \\
    ‘?a. Z n x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?b. M = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     RW_TAC real_ss [extreal_lt_eq, extreal_of_num_def, extreal_sub_def,
                     extreal_mul_def, extreal_not_infty])
 >> Rewr'
 >> Know ‘Z n x / &SUC n = inv (&SUC n) * Z n x’
 >- (MATCH_MP_TAC div_eq_mul_linv \\
    ‘?a. Z n x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     RW_TAC real_ss [extreal_lt_eq, extreal_of_num_def, extreal_not_infty])
 >> Rewr'
 >> Know ‘inv (&SUC n) * (Z n x - &SUC n * M) =
          inv (&SUC n) * Z n x - inv (&SUC n) * (&SUC n * M)’
 >- (MATCH_MP_TAC sub_ldistrib \\
    ‘?r. M = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘&SUC n <> (0 :real)’ by rw [] \\
     RW_TAC real_ss [extreal_inv_def, extreal_of_num_def,
                     extreal_not_infty, extreal_mul_def])
 >> Rewr'
 >> Suff ‘inv (&SUC n) * (&SUC n * M) = M’ >- Rewr
 >> REWRITE_TAC [mul_assoc]
 >> Suff ‘inv (&SUC n) * &SUC n = 1’ >- (Rewr' >> REWRITE_TAC [mul_lone])
 >> MATCH_MP_TAC mul_linv_pos
 >> rw [extreal_of_num_def, extreal_not_infty, extreal_lt_eq]
QED

Theorem LLN_alt_converge_AE_IID :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) /\
          identical_distribution p X Borel UNIV /\ integrable p (X 0) ==>
         (LLN p X almost_everywhere <=>
          ((\n x. SIGMA (\i. X i x) (count1 n) / &SUC n) --> (\x. expectation p (X 0)))
           (almost_everywhere p))
Proof
    rw [LLN_def]
 >> ‘real_random_variable (\x. 0) p’ by PROVE_TAC [real_random_variable_zero]
 >> qabbrev_tac ‘Z = \n x. SIGMA (\i. X i x) (count1 n)’
 >> simp []
 >> ‘!n. (\x. Z n x) = Z n’ by rw [FUN_EQ_THM] >> POP_ORW
 >> qabbrev_tac ‘W = \n x. (Z n x - expectation p (Z n)) / &SUC n’
 >> Know ‘!n. integrable p (X n)’
 >- (MATCH_MP_TAC identical_distribution_integrable >> fs [real_random_variable_def])
 >> DISCH_TAC
 >> Know ‘!n. real_random_variable (W n) p’
 >- (rw [Abbr ‘W’] \\
     MATCH_MP_TAC real_random_variable_LLN \\
     Q.EXISTS_TAC ‘X’ >> rw [])
 >> DISCH_TAC
 >> qabbrev_tac ‘Y = \n x. Z n x / &SUC n’
 >> Know ‘!n. real_random_variable (Y n) p’
 >- (rw [Abbr ‘Y’, Abbr ‘Z’] \\
     MATCH_MP_TAC real_random_variable_LLN' >> art [])
 >> DISCH_TAC
 >> Know ‘real_random_variable (\x. expectation p (X 0)) p’
 >- (MATCH_MP_TAC real_random_variable_const >> art [] \\
     MATCH_MP_TAC integrable_imp_finite_expectation >> art [])
 >> DISCH_TAC
 >> RW_TAC real_ss [converge_AE_def, AE_DEF, LIM_SEQUENTIALLY, dist, real_0]
 >> simp [Abbr ‘W’, Abbr ‘Y’]
 >> Suff ‘!n x. x IN m_space p ==>
                real ((Z n x - expectation p (Z n)) / &SUC n) =
                real (Z n x / &SUC n) - real (expectation p (X 0))’
 >- (DISCH_TAC >> EQ_TAC >> rw [])
 >> rpt STRIP_TAC
 >> Know ‘!n. expectation p (Z n) = SIGMA (\i. expectation p (X i)) (count1 n)’
 >- (rw [expectation_def, Abbr ‘Z’] \\
     MATCH_MP_TAC integral_sum \\
     fs [FINITE_COUNT, prob_space_def, real_random_variable_def, p_space_def] \\
     rpt STRIP_TAC \\
     MATCH_MP_TAC identical_distribution_integrable >> rw [prob_space_def])
 >> Rewr'
 >> Q.ABBREV_TAC ‘M = expectation p (X 0)’
 >> Know ‘!n. expectation p (X n) = M’
 >- (GEN_TAC >> Q.UNABBREV_TAC ‘M’ \\
     MATCH_MP_TAC identical_distribution_expectation \\
     FULL_SIMP_TAC std_ss [real_random_variable_def])
 >> Rewr'
 >> Know ‘SIGMA (\i. M) (count1 n) = &CARD (count1 n) * (\i. M) (0 :num)’
 >- (irule (INST_TYPE [“:'a” |-> “:num”] EXTREAL_SUM_IMAGE_FINITE_SAME) \\
     rw [IN_COUNT, FINITE_COUNT]) >> Rewr'
 >> REWRITE_TAC [CARD_COUNT]
 >> Know ‘!n x. x IN m_space p ==> Z n x <> PosInf’
 >- (RW_TAC std_ss [Abbr ‘Z’] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
     FULL_SIMP_TAC std_ss [real_random_variable_def, p_space_def, FINITE_COUNT, IN_COUNT])
 >> DISCH_TAC
 >> Know ‘!n x. x IN m_space p ==> Z n x <> NegInf’
 >- (RW_TAC std_ss [Abbr ‘Z’] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
     FULL_SIMP_TAC std_ss [real_random_variable_def, p_space_def, FINITE_COUNT, IN_COUNT])
 >> DISCH_TAC
 >> Know ‘M <> PosInf /\ M <> NegInf’
 >- (ASM_SIMP_TAC std_ss [expectation_def, Abbr ‘M’] \\
     MATCH_MP_TAC integrable_finite_integral \\
     FULL_SIMP_TAC std_ss [prob_space_def])
 >> STRIP_TAC
 >> Know ‘(Z n x - &SUC n * M) / &SUC n = inv (&SUC n) * (Z n x - &SUC n * M)’
 >- (MATCH_MP_TAC div_eq_mul_linv \\
    ‘?a. Z n x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?b. M = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     RW_TAC real_ss [extreal_lt_eq, extreal_of_num_def, extreal_sub_def,
                     extreal_mul_def, extreal_not_infty])
 >> Rewr'
 >> Know ‘Z n x / &SUC n = inv (&SUC n) * Z n x’
 >- (MATCH_MP_TAC div_eq_mul_linv \\
    ‘?a. Z n x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     RW_TAC real_ss [extreal_lt_eq, extreal_of_num_def, extreal_not_infty])
 >> Rewr'
 >> Know ‘inv (&SUC n) * (Z n x - &SUC n * M) =
          inv (&SUC n) * Z n x - inv (&SUC n) * (&SUC n * M)’
 >- (MATCH_MP_TAC sub_ldistrib \\
    ‘?r. M = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘&SUC n <> (0 :real)’ by rw [] \\
     RW_TAC real_ss [extreal_inv_def, extreal_of_num_def, extreal_not_infty, extreal_mul_def])
 >> Rewr'
 >> Know ‘inv (&SUC n) * (&SUC n * M) = M’
 >- (REWRITE_TAC [mul_assoc] \\
     Suff ‘inv (&SUC n) * &SUC n = 1’ >- (Rewr' >> REWRITE_TAC [mul_lone]) \\
     MATCH_MP_TAC mul_linv_pos \\
     rw [extreal_of_num_def, extreal_not_infty, extreal_lt_eq])
 >> Rewr'
 >> ‘&SUC n <> (0 :real)’ by rw []
 >> ‘?a. Z n x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> ‘?b. M = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> RW_TAC real_ss [extreal_inv_def, extreal_of_num_def, extreal_sub_def,
                    extreal_mul_def, real_normal]
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

(* This lemma depends on LIM_SEQUENTIALLY_CESARO (moved to real_topologyTheory) *)
Theorem truncated_vars_expectation' :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) /\
          identical_distribution p X Borel UNIV /\ integrable p (X 0) ==>
         ((\n. real (expectation p
                      (\x. SIGMA (\i. truncated X i x) (count1 n)) / &SUC n)) -->
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
                (\x. SIGMA (\i. truncated X i x) (count1 n)) =
              SIGMA (\i. expectation p (truncated X i)) (count1 n)’
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
 >> Know ‘!n. SIGMA (\x. Normal (g x)) (count1 n) =
              Normal (SIGMA g (count1 n))’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NORMAL >> rw []) >> Rewr'
 >> ‘!n. &SUC n <> (0 :real)’ by rw []
 >> simp [extreal_div_eq, extreal_of_num_def]
 >> REWRITE_TAC [LIM_SEQUENTIALLY_CESARO]
QED

(* ------------------------------------------------------------------------- *)
(*  The Weak Law of Large Numbers for IID random variables                   *)
(* ------------------------------------------------------------------------- *)

(* This shared tactic is used by both WLLN_IID and SLLN_IID. It sets up a truncated
   sequence of r.v.'s, Y, according to the most comfortable way (but slightly
   different with textbook proofs) of proving X and Y are equivalent, while Y
   now has finite second moments and is uncorrelated.

   Furthermore (part 2), it sets up Z as the partial sum of Y, and prove that Z
   is a real_random_variable with finite second moments, etc.
 *)
val LLN_IID_shared_tactics =
 (* Part 1 (of 2) *)
    Q.ABBREV_TAC ‘m = expectation p (X 0)’
 >> ‘m <> PosInf /\ m <> NegInf’ by METIS_TAC [expectation_finite]
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
     Suff ‘expectation p (abs o (X 0)) < PosInf’ >- METIS_TAC [expectation_converge] \\
    ‘integrable p (abs o (X 0))’ by METIS_TAC [prob_space_def, integrable_abs] \\
     METIS_TAC [expectation_finite, lt_infty])
 >> DISCH_TAC
 >> Know ‘equivalent p X Y’
 >- (REWRITE_TAC [equivalent_def] \\
     Suff ‘!n x. X n x <> Y n x <=> &SUC n <= abs (X n x)’ >- DISCH_THEN (art o wrap) \\
     NTAC 2 (POP_ASSUM K_TAC) \\
    ‘Y = (\n. f n o X n)’
       by (rw [Abbr ‘Y’, Abbr ‘f’, truncated_def, o_DEF]) >> POP_ORW \\
     rw [Abbr ‘f’] \\
     CCONTR_TAC >> FULL_SIMP_TAC std_ss [abs_0] \\
     FULL_SIMP_TAC real_ss [extreal_of_num_def, extreal_le_eq])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘suminf _ < PosInf’ K_TAC
 >> Know ‘!n. finite_second_moments p (Y n)’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC bounded_imp_finite_second_moments >> art [] \\
     CONJ_TAC >- FULL_SIMP_TAC std_ss [real_random_variable_def] \\
     Q.EXISTS_TAC ‘&SUC n’ \\
     NTAC 3 (POP_ASSUM K_TAC) (* useless assumptions *) \\
    ‘Y = (\n. f n o X n)’
       by (rw [Abbr ‘Y’, Abbr ‘f’, truncated_def, o_DEF]) >> POP_ORW \\
     rw [Abbr ‘f’] \\
     MATCH_MP_TAC lt_imp_le \\
     FULL_SIMP_TAC std_ss [GSYM extreal_lt_def, extreal_of_num_def,
                           extreal_le_eq, extreal_abs_def])
 >> DISCH_TAC
 >> Know ‘!i j. i <> j ==> uncorrelated p (Y i) (Y j)’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC indep_vars_imp_uncorrelated >> art [] \\
     fs [pairwise_indep_vars_def])
 >> DISCH_TAC
 >> Know ‘!n. integrable p (Y n)’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC finite_second_moments_imp_integrable >> art [])
 >> DISCH_TAC
 (* Part 2 (of 2) *)
 >> Q.ABBREV_TAC ‘Z = \n x. SIGMA (\i. Y i x) (count n)’
 >> Know ‘!n. real_random_variable (Z n) p’
 >- (rw [Abbr ‘Z’] \\
     MATCH_MP_TAC real_random_variable_sum >> rw [])
 >> DISCH_TAC
 >> Know ‘!n. integrable p (Z n)’
 >- (rw [Abbr ‘Z’] \\
     MATCH_MP_TAC integrable_sum \\
     Q.PAT_X_ASSUM ‘!n. real_random_variable (Y n) p’
       (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
        (REWRITE_RULE [real_random_variable, p_space_def, events_def])) \\
     rw [FINITE_COUNT] >> fs [prob_space_def])
 >> DISCH_TAC
 >> Know ‘!n. finite_second_moments p (Z n)’
 >- (rw [Abbr ‘Z’, finite_second_moments_eq_finite_variance, GSYM lt_infty] \\
     Know ‘variance p (\x. SIGMA (\i. Y i x) (count n)) =
           SIGMA (\i. variance p (Y i)) (count n)’
     >- (MATCH_MP_TAC variance_sum' >> rw [FINITE_COUNT] \\
         MATCH_MP_TAC pairwise_indep_vars_subset \\
         Q.EXISTS_TAC ‘univ(:num)’ >> rw [SUBSET_DEF]) >> Rewr' \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> rw [lt_infty, FINITE_COUNT] \\
     PROVE_TAC [finite_second_moments_eq_finite_variance])
 >> DISCH_TAC
 (* estimate the variance of ‘Z’ *)
 >> Know ‘!n. variance p (Z n) <= SIGMA (\i. expectation p (\x. (Y i x) pow 2)) (count n)’
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
 >> DISCH_TAC;
 (* end of LLN_IID_shared_tactics *)

(* Theorem 5.2.2 [2, p.114]. This law of large numbers is due to Khintchine.

   Key (non-trivial) lemmas used in the main proof (~1200 lines):

 - expectation_converge (expectation_bounds)                 [probabilityTheory]
 - equivalent_thm3' (equivalent_thm3, equivalent_thm2)
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
    PRINT_TAC "proving WLLN_IID (Weak Law of Large Numbers for I.I.D. r.v.'s) ..."
 >> RW_TAC std_ss [LLN_alt_converge_PR_IID]
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
 (* define Y = truncated X, Z = SIGMA Y and prove their properties *)
 >> LLN_IID_shared_tactics
 (* stage work *)
 >> MATCH_MP_TAC equivalent_thm3'
 >> Q.EXISTS_TAC ‘Y’
 >> rw [Once equivalent_comm]
 >- (MATCH_MP_TAC real_random_variable_const >> art [] \\
     Q.UNABBREV_TAC ‘m’ >> MATCH_MP_TAC expectation_finite >> art [])
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
     Q.ABBREV_TAC ‘k :num = flr (b n)’ \\
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
             MATCH_MP_TAC integral_add' >> BETA_TAC \\
             FULL_SIMP_TAC std_ss [prob_space_def] \\
             rpt STRIP_TAC >| (* 2 subgoals *)
             [ (* goal 1 (of 2) *)
              ‘?r. a n = Normal r’ by METIS_TAC [extreal_cases] \\
               POP_ASSUM (FULL_SIMP_TAC std_ss o wrap) \\
               HO_MATCH_MP_TAC integrable_cmul >> art [],
               (* goal 2 (of 2) *)
              ‘&n = Normal (&n)’ by rw [extreal_of_num_def] \\
               POP_ASSUM (FULL_SIMP_TAC std_ss o wrap) \\
               HO_MATCH_MP_TAC integrable_cmul >> art [] ]) >> Rewr' \\
         REWRITE_TAC [expectation_def] \\
         MATCH_MP_TAC integral_mono \\
        ‘integrable p (\x. Y i x pow 2)’
           by METIS_TAC [finite_second_moments_eq_integrable_square] \\
         FULL_SIMP_TAC std_ss [prob_space_def] \\
         CONJ_TAC (* integrable *)
         >- (HO_MATCH_MP_TAC integrable_add' >> RW_TAC std_ss [] >| (* 2 subgoals *)
             [ (* goal 1 (of 3) *)
              ‘?r. a n = Normal r’ by METIS_TAC [extreal_cases] \\
               POP_ASSUM (FULL_SIMP_TAC std_ss o wrap) \\
               HO_MATCH_MP_TAC integrable_cmul >> art [],
               (* goal 2 (of 3) *)
              ‘&n = Normal (&n)’ by rw [extreal_of_num_def] \\
               POP_ASSUM (FULL_SIMP_TAC std_ss o wrap) \\
               HO_MATCH_MP_TAC integrable_cmul >> art [] ]) \\
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
             FULL_SIMP_TAC std_ss [real_random_variable_def, p_space_def] \\
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
 >- (rw [Abbr ‘Z’] >> MATCH_MP_TAC real_random_variable_sum >> rw [])
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
         MP_TAC (Q.SPECL [‘p’, ‘Y’, ‘\n. Z (SUC n)’] real_random_variable_LLN) \\
         simp []) >> DISCH_TAC \\
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
         Q.EXISTS_TAC ‘SIGMA (\i. expectation p (\x. Y i x pow 2)) (count1 n)’ >> art []) \\
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

(* |- !p X.
        prob_space p /\ (!n. real_random_variable (X n) p) /\
        pairwise_indep_vars p X (\n. Borel) univ(:num) /\
        identical_distribution p X Borel univ(:num) /\ integrable p (X 0) ==>
        ((\n x. SIGMA (\i. X i x) (count1 n) / &SUC n) -->
         (\x. expectation p (X 0))) (in_probability p)
 *)
Theorem WLLN_IID_applied = SIMP_RULE std_ss [LLN_alt_converge_PR_IID] WLLN_IID

(* ------------------------------------------------------------------------- *)
(*  The Strong Law of Large Numbers for IID random variables                 *)
(* ------------------------------------------------------------------------- *)

Theorem pow_seq_pos_lt :
    !a n. 1 < a ==> 0 < pow_seq a n
Proof
    RW_TAC std_ss [pow_seq_def]
 >> MATCH_MP_TAC LESS_LESS_EQ_TRANS
 >> Q.EXISTS_TAC ‘1’ >> rw []
 >> Know ‘0 <= a pow n’
 >- (rw [] >> DISJ1_TAC >> MATCH_MP_TAC REAL_LT_IMP_LE \\
     MATCH_MP_TAC REAL_LT_TRANS \\
     Q.EXISTS_TAC ‘1’ >> rw [REAL_LT_01])
 >> DISCH_THEN (ONCE_REWRITE_TAC o wrap o (MATCH_MP NUM_FLOOR_LE2))
 >> MATCH_MP_TAC REAL_POW_LE_1
 >> MATCH_MP_TAC REAL_LT_IMP_LE >> art []
QED

Theorem pow_seq_lower_bound :
    !a n. 1 < a ==> a pow n / 2 < &pow_seq a n
Proof
    RW_TAC std_ss [pow_seq_def]
 >> MATCH_MP_TAC NUM_FLOOR_lower_bound
 >> MATCH_MP_TAC REAL_POW_LE_1
 >> MATCH_MP_TAC REAL_LT_IMP_LE >> art []
QED

Theorem pow_seq_unbounded :
    !a (x :real). 1 < a ==> ?n. x < &pow_seq a (SUC n)
Proof
    rpt STRIP_TAC
 >> ‘1 <= a’ by PROVE_TAC [REAL_LT_IMP_LE]
 >> ‘0 <  a’ by PROVE_TAC [REAL_LT_01, REAL_LT_TRANS]
 >> ‘0 <= a’ by PROVE_TAC [REAL_LT_IMP_LE]
 >> Q.ABBREV_TAC ‘u = \(a :real) n. flr (a pow n)’
 >> FULL_SIMP_TAC std_ss [pow_seq_def]
 >> Cases_on ‘x < 1’
 >- (Q.EXISTS_TAC ‘0’ (* any value is fine here *) \\
     MATCH_MP_TAC REAL_LTE_TRANS \\
     Q.EXISTS_TAC ‘1’ >> rw [Abbr ‘u’] \\
     rw [NUM_FLOOR_LE2])
 >> POP_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [real_lt])
 >> Suff ‘?n. x < &u a n’
 >- (STRIP_TAC \\
     Cases_on ‘n’ >- (fs [Abbr ‘u’] >> PROVE_TAC [REAL_LTE_ANTISYM]) \\
     rename1 ‘x < &u a (SUC n)’ \\
     Q.EXISTS_TAC ‘n’ >> art [])
 >> RW_TAC std_ss [Abbr ‘u’]
 >> STRIP_ASSUME_TAC
      (Q.SPEC ‘2 * x’ (MATCH_MP REAL_ARCH_POW (ASSUME “1 < (a :real)”)))
 >> Q.EXISTS_TAC ‘n’
 >> MATCH_MP_TAC REAL_LT_TRANS
 >> Q.EXISTS_TAC ‘a pow n / 2’
 >> CONJ_TAC >- rw [REAL_LT_RDIV_EQ]
 >> MATCH_MP_TAC NUM_FLOOR_lower_bound
 >> MATCH_MP_TAC REAL_POW_LE_1 >> art []
QED

Theorem pow_seq_monotone :
    !a i j. 1 < a /\ i <= j ==> pow_seq a i <= pow_seq a j
Proof
    RW_TAC std_ss [pow_seq_def]
 >> MATCH_MP_TAC NUM_FLOOR_MONO
 >> ‘0 <= a’ by PROVE_TAC [REAL_LT_01, REAL_LT_IMP_LE, REAL_LT_TRANS]
 >> ‘1 <= a’ by PROVE_TAC [REAL_LT_IMP_LE]
 >> Know ‘!n. 0 <= a pow n’
 >- PROVE_TAC [POW_POS] >> Rewr
 >> MATCH_MP_TAC REAL_POW_MONO
 >> RW_TAC arith_ss []
QED

Theorem pow_seq_complete :
    !a k. 1 < a /\ 0 < k ==> ?n. pow_seq a n <= k /\ k <= pow_seq a (SUC n)
Proof
    rpt STRIP_TAC
 >> ASSUME_TAC (MATCH_MP pow_seq_unbounded (ASSUME “1 < (a :real)”))
 >> Q.ABBREV_TAC ‘u = \(a :real) n. flr (a pow n)’
 >> FULL_SIMP_TAC std_ss [pow_seq_def]
 >> Q.EXISTS_TAC ‘LEAST n. &k < &u a (SUC n) :real’
 >> numLib.LEAST_ELIM_TAC >> rw []
 >> CCONTR_TAC >> fs [GSYM NOT_LESS]
 >> Cases_on ‘n = 0’
 >- (POP_ASSUM (FULL_SIMP_TAC arith_ss o wrap) \\
     Know ‘u a 0 = 1’ >- (rw [Abbr ‘u’, pow0]) \\
     DISCH_THEN (FULL_SIMP_TAC arith_ss o wrap))
 >> Q.PAT_X_ASSUM ‘!m. m < n ==> ~(k < u a (SUC m))’
      (MP_TAC o (Q.SPEC ‘PRE n’)) >> rw []
 >> ‘0 < n’ by DECIDE_TAC >> fs [SUC_PRE]
QED

Theorem pow_seq_limit :
    !a. 1 < a ==> ((\n. &pow_seq a (SUC n) / &pow_seq a n) --> a) sequentially
Proof
    rpt STRIP_TAC
 >> ‘0 < a’ by PROVE_TAC [REAL_LT_01, REAL_LT_TRANS]
 >> ‘0 <= a’ by PROVE_TAC [REAL_LT_IMP_LE]
 >> ASSUME_TAC (MATCH_MP pow_seq_pos_lt (ASSUME “1 < (a :real)”))
 >> Q.ABBREV_TAC ‘u = \(a :real) n. flr (a pow n)’
 >> FULL_SIMP_TAC std_ss [pow_seq_def]
 >> ‘!n. (0 :real) < &u a n’ by rw []
 >> ‘!n. &u a n <> (0 :real)’ by PROVE_TAC [REAL_LT_IMP_NE]
 >> FULL_SIMP_TAC std_ss [Abbr ‘u’]
 >> RW_TAC std_ss [LIM_SEQUENTIALLY, dist,
                   ABS_BOUNDS_LT, REAL_LT_SUB_RADD, REAL_LT_SUB_LADD]
 >> Know ‘!n. 0 < n ==> &flr (a pow SUC n) / &flr (a pow n) <= a pow (SUC n) / (a pow n - 1)’
 >- (Q.X_GEN_TAC ‘n’ >> DISCH_TAC \\
     MATCH_MP_TAC REAL_LE_TRANS \\
     Q.EXISTS_TAC ‘a pow (SUC n) / &flr (a pow n)’ \\
     CONJ_TAC >- (rw [REAL_LE_RDIV_CANCEL] \\
                  MATCH_MP_TAC NUM_FLOOR_LE \\
                  MATCH_MP_TAC REAL_LT_IMP_LE \\
                  MATCH_MP_TAC POW_POS_LT >> art []) \\
     Know ‘a pow SUC n / &flr (a pow n) <= a pow SUC n / (a pow n - 1) <=>
           a pow n - 1 <= &flr (a pow n)’
     >- (MATCH_MP_TAC REAL_LE_LDIV_CANCEL >> rw [REAL_SUB_LT] >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
          ‘1 = a pow 0’ by PROVE_TAC [pow0] >> POP_ORW \\
           MATCH_MP_TAC REAL_POW_MONO_LT >> art [],
           (* goal 2 (of 2) *)
           MATCH_MP_TAC POW_POS_LT >> art [] ]) >> Rewr' \\
     MATCH_MP_TAC REAL_LT_IMP_LE \\
     REWRITE_TAC [NUM_FLOOR_LT])
 >> DISCH_TAC
 >> Know ‘!n. 0 < n ==> &flr (a pow SUC n) / &flr (a pow n) <= a / (a pow n - 1) + a’
 >- (Q.X_GEN_TAC ‘n’ >> DISCH_TAC \\
     ONCE_REWRITE_TAC [REAL_ADD_COMM] \\
     Suff ‘a + a / (a pow n - 1) = a pow SUC n / (a pow n − 1)’
     >- (Rewr' >> FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     REWRITE_TAC [pow] \\
    ‘a * a pow n = a * (a pow n - 1) + a’
       by PROVE_TAC [REAL_SUB_ADD, REAL_SUB_LDISTRIB, REAL_MUL_RID] >> POP_ORW \\
     REWRITE_TAC [GSYM REAL_DIV_ADD] \\
     Suff ‘a * (a pow n − 1) / (a pow n − 1) = a’ >- Rewr \\
     REWRITE_TAC [real_div, GSYM REAL_MUL_ASSOC] \\
     Suff ‘(a pow n - 1) * inv (a pow n - 1) = 1’ >- (Rewr' >> REWRITE_TAC [REAL_MUL_RID]) \\
     MATCH_MP_TAC REAL_MUL_RINV \\
     Suff ‘1 < a pow n’ >- REAL_ARITH_TAC \\
    ‘1 = a pow 0’ by PROVE_TAC [pow0] >> POP_ORW \\
     MATCH_MP_TAC REAL_POW_MONO_LT >> art [])
 >> POP_ASSUM K_TAC >> DISCH_TAC
 >> Know ‘!n. 0 < n ==> (a pow (SUC n) - 1) / a pow n <= &flr (a pow SUC n) / &flr (a pow n)’
 >- (Q.X_GEN_TAC ‘n’ >> DISCH_TAC \\
     MATCH_MP_TAC REAL_LE_TRANS \\
     Q.EXISTS_TAC ‘&flr (a pow (SUC n)) / a pow n’ \\
     Know ‘0 < a pow n’ >- (Cases_on ‘n’ >> rw [] \\
                            MATCH_MP_TAC POW_POS_LT >> art []) >> DISCH_TAC \\
     CONJ_TAC >- (rw [REAL_LE_RDIV_CANCEL] \\
                  MATCH_MP_TAC REAL_LT_IMP_LE \\
                  REWRITE_TAC [NUM_FLOOR_LT]) \\
     Know ‘&flr (a pow SUC n) / a pow n <= &flr (a pow SUC n) / &flr (a pow n) <=>
           &flr (a pow n) <= a pow n’
     >- (MATCH_MP_TAC REAL_LE_LDIV_CANCEL >> rw []) >> Rewr' \\
     MATCH_MP_TAC NUM_FLOOR_LE \\
     MATCH_MP_TAC POW_POS >> art [])
 >> DISCH_TAC
 >> Know ‘!n. 0 < n ==> -(1 / a pow n) + a <= &flr (a pow SUC n) / &flr (a pow n)’
 >- (Q.X_GEN_TAC ‘n’ >> DISCH_TAC \\
     REWRITE_TAC [GSYM real_sub, Once REAL_ADD_COMM] \\
     Suff ‘a - 1 / a pow n = (a pow SUC n - 1) / a pow n’
     >- (Rewr' >> FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     REWRITE_TAC [pow, GSYM REAL_DIV_SUB] \\
     Suff ‘a * a pow n / a pow n = a’ >- Rewr \\
     REWRITE_TAC [real_div, GSYM REAL_MUL_ASSOC] \\
     Suff ‘a pow n * inv (a pow n) = 1’ >- (Rewr' >> REWRITE_TAC [REAL_MUL_RID]) \\
     MATCH_MP_TAC REAL_MUL_RINV \\
     Suff ‘0 < a pow n’ >- PROVE_TAC [REAL_LT_IMP_NE] \\
     Cases_on ‘n’ >> rw [] >> MATCH_MP_TAC POW_POS_LT >> art [])
 >> POP_ASSUM K_TAC >> DISCH_TAC
 (* now estimating N for each sides *)
 >> MP_TAC (REWRITE_RULE [REAL_LT_ADDL] (Q.SPECL [‘a’, ‘a / e + 1’] REAL_ARCH_POW))
 >> RW_TAC std_ss [] >> rename1 ‘a / e + 1 < a pow N1’
 >> MP_TAC (REWRITE_RULE [REAL_LT_ADDL] (Q.SPECL [‘a’, ‘1 / e’] REAL_ARCH_POW))
 >> RW_TAC std_ss [] >> rename1 ‘1 / e < a pow N2’
 >> Q.EXISTS_TAC ‘SUC (MAX N1 N2)’
 >> RW_TAC arith_ss [GSYM LESS_EQ, MAX_LT] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC REAL_LTE_TRANS \\
      Q.EXISTS_TAC ‘-(1 / a pow n) + a’ \\
      reverse CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw []) \\
     ‘a <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] >> rw [] \\
      Know ‘1 < e * a pow n <=> 1 / e < a pow n’
      >- (REWRITE_TAC [Once EQ_SYM_EQ, Once REAL_MUL_COMM] \\
          MATCH_MP_TAC REAL_LT_LDIV_EQ >> art []) >> Rewr' \\
      MATCH_MP_TAC REAL_LT_TRANS \\
      Q.EXISTS_TAC ‘a pow N2’ >> art [] \\
      MATCH_MP_TAC REAL_POW_MONO_LT >> art [],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC REAL_LET_TRANS \\
      Q.EXISTS_TAC ‘a / (a pow n - 1) + a’ >> rw [] \\
      Know ‘a / (a pow n - 1) < e <=> a < e * (a pow n - 1)’
      >- (MATCH_MP_TAC REAL_LT_LDIV_EQ \\
          REWRITE_TAC [REAL_SUB_LT] \\
         ‘1 = a pow 0’ by PROVE_TAC [pow0] >> POP_ORW \\
          MATCH_MP_TAC REAL_POW_MONO_LT >> rw []) >> Rewr' \\
      Know ‘a < e * (a pow n - 1) <=> a / e < a pow n - 1’
      >- (REWRITE_TAC [Once EQ_SYM_EQ, Once REAL_MUL_COMM] \\
          MATCH_MP_TAC REAL_LT_LDIV_EQ >> art []) >> Rewr' \\
      REWRITE_TAC [REAL_LT_SUB_LADD] \\
      MATCH_MP_TAC REAL_LT_TRANS \\
      Q.EXISTS_TAC ‘a pow N1’ >> art [] \\
      MATCH_MP_TAC REAL_POW_MONO_LT >> art [] ]
QED

Theorem pow_seq_limit' :
    !a. 1 < a ==> ((\n. &pow_seq a n / &pow_seq a (SUC n)) --> inv a) sequentially
Proof
    rpt STRIP_TAC
 >> ‘0 < a’ by PROVE_TAC [REAL_LT_01, REAL_LT_TRANS]
 >> ‘a <> 0’ by PROVE_TAC [REAL_LT_IMP_NE]
 >> ASSUME_TAC (MATCH_MP pow_seq_pos_lt (ASSUME “1 < (a :real)”))
 >> ASSUME_TAC (MATCH_MP pow_seq_limit (ASSUME “1 < (a :real)”))
 >> Q.ABBREV_TAC ‘u = \(a :real) n. flr (a pow n)’
 >> FULL_SIMP_TAC std_ss [pow_seq_def]
 >> Q.ABBREV_TAC ‘f = \n. &u a (SUC n) / (&u a n :real)’ >> rw []
 >> ‘!n. (0 :real) < &u a n’ by rw []
 >> ‘!n. &u a n <> (0 :real)’ by PROVE_TAC [REAL_LT_IMP_NE]
 >> Know ‘(\n. &u a n / &u a (SUC n)) = inv o f’
 >- (rw [FUN_EQ_THM, o_DEF, Abbr ‘f’, REAL_INV_DIV])
 >> Rewr'
 >> MATCH_MP_TAC LIM_INV >> art []
QED

(* This lemma corresponds to the part of textbook proofs that can be formalized directly,
   while after this part a non-trivial fix is done by Chun Tian at mathematical levels.
   (see SLLN_IID_wlog for more details.)
 *)
Theorem SLLN_IID_lemma :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) /\
          pairwise_indep_vars p X (\n. Borel) UNIV /\
          identical_distribution p X Borel UNIV /\ integrable p (X 0) ==>
          !a. 1 < a ==>
             ((\n x. SIGMA (\i. X i x) (count (pow_seq a (SUC n))) /
                     &pow_seq a (SUC n)) --> (\x. expectation p (X 0))) (almost_everywhere p)
Proof
    PRINT_TAC "proving SLLN_IID (Strong Law of Large Numbers for I.I.D. r.v.'s) ..."
 >> rpt GEN_TAC >> STRIP_TAC
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
 (* define Y = truncated X, Z = SIGMA Y and prove their properties *)
 >> LLN_IID_shared_tactics
 (* additional properties of Z (n = 0 is included as a trivial case) *)
 >> Know ‘!n. variance p (Z n) <=
              &CARD (count n) *
              expectation p (\x. (X 0 x) pow 2 *
                                 indicator_fn {x | x IN p_space p /\ abs (X 0 x) < &n} x)’
 >- (Q.X_GEN_TAC ‘N’ \\
     Cases_on ‘N’ >- rw [CARD_COUNT, Abbr ‘Z’, EXTREAL_SUM_IMAGE_EMPTY, variance_zero] \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC ‘SIGMA (\i. expectation p (\x. Y i x pow 2)) (count1 n)’ >> art [] \\
  (* applying EXTREAL_SUM_IMAGE_FINITE_SAME *)
     Q.ABBREV_TAC ‘g = \i. expectation p
                             (\x. X i x pow 2 *
                                  indicator_fn {x | x IN p_space p /\ abs (X i x) < &SUC n} x)’ \\
     ASM_SIMP_TAC std_ss [] \\
    ‘FINITE (count1 n)’ by PROVE_TAC [FINITE_COUNT] \\
     Know ‘&CARD (count1 n) * g 0 = SIGMA (\i. g 0) (count1 n)’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         HO_MATCH_MP_TAC (MATCH_MP EXTREAL_SUM_IMAGE_FINITE_SAME
                                   (ASSUME “FINITE (count1 n)”)) >> rw []) >> Rewr' \\
     Q.UNABBREV_TAC ‘g’ >> BETA_TAC \\
  (* LHS rewriting: Y -> X *)
     Know ‘!i. expectation p (\x. Y i x pow 2) =
               expectation p (\x. X i x pow 2 *
                                  indicator_fn {x | x IN p_space p /\ abs (X i x) < &SUC i} x)’
     >- (Q.X_GEN_TAC ‘i’ \\
         MATCH_MP_TAC expectation_cong >> rw [Abbr ‘Y’] \\
         Cases_on ‘abs (X i x) < &SUC i’ \\
         RW_TAC real_ss [indicator_fn_def, mul_rone, mul_rzero, zero_pow, lt_02]) \\
     Rewr' \\
  (* RHS rewriting: 0 -> i (I.I.D.) *)
     Know ‘!i. expectation p
                 (\x. X 0 x pow 2 *
                      indicator_fn {x | x IN p_space p /\ abs (X 0 x) < &SUC n} x) =
               expectation p
                 (\x. X i x pow 2 *
                      indicator_fn {x | x IN p_space p /\ abs (X i x) < &SUC n} x)’
     >- (RW_TAC std_ss [Once EQ_SYM_EQ] \\
         Q.ABBREV_TAC ‘W = \i x. X i x pow 2 *
                                 indicator_fn {x | x IN p_space p /\ abs (X i x) < &SUC n} x’ \\
         ASM_SIMP_TAC std_ss [] \\
        ‘!i. (\x. W i x) = W i’ by METIS_TAC [] >> POP_ORW \\
         MATCH_MP_TAC identical_distribution_expectation >> art [] \\
         Know ‘!i x. x IN p_space p ==> W i x = (((\x. x pow 2) o (f n)) o (X i)) x’
         >- (RW_TAC std_ss [Abbr ‘W’, Abbr ‘f’, o_DEF, extreal_lt_def,
                            indicator_fn_def, GSPECIFICATION, mul_rzero, mul_rone,
                            zero_pow, lt_02] \\
             PROVE_TAC []) >> DISCH_TAC \\
         Q.PAT_X_ASSUM `!n. real_random_variable (X n) p`
           (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
            (REWRITE_RULE [real_random_variable_def])) \\
         Know ‘!i. random_variable ((\x. x pow 2) o (f n) o (X i)) p Borel’
         >- (Q.X_GEN_TAC ‘i’ \\
             MATCH_MP_TAC random_variable_comp >> art [IN_MEASURABLE_BOREL_BOREL_POW] \\
             MATCH_MP_TAC random_variable_comp >> art []) >> DISCH_TAC \\
         STRONG_CONJ_TAC (* random_variable (W n) *)
         >- (Q.X_GEN_TAC ‘i’ \\
             Know ‘random_variable (W i) p Borel <=>
                   random_variable ((\x. x pow 2) o (f n) o (X i)) p Borel’
             >- (MATCH_MP_TAC random_variable_cong >> rw []) \\
             DISCH_THEN (art o wrap)) >> DISCH_TAC \\
         Know ‘identical_distribution p W Borel UNIV <=>
               identical_distribution p (\i. ((\x. x pow 2) o (f n)) o (X i)) Borel UNIV’
         >- (REWRITE_TAC [GSYM o_ASSOC] \\
             simp [identical_distribution_alt] \\
             Suff ‘!g. g IN measurable Borel Borel ==>
                       !i. expectation p (g o W i) = expectation p (g o (\x. x pow 2) o f n o X i)’
             >- (rpt STRIP_TAC >> EQ_TAC >> rw []) \\
             rpt STRIP_TAC \\
             MATCH_MP_TAC expectation_cong >> rw []) >> Rewr' \\
         MATCH_MP_TAC identical_distribution_cong >> art [] \\
         MATCH_MP_TAC MEASURABLE_COMP \\
         Q.EXISTS_TAC ‘Borel’ >> art [IN_MEASURABLE_BOREL_BOREL_POW]) >> Rewr' \\
     irule EXTREAL_SUM_IMAGE_MONO >> ASM_SIMP_TAC std_ss [] \\
     reverse CONJ_TAC
     >- (DISJ1_TAC >> Q.X_GEN_TAC ‘i’ >> NTAC 2 STRIP_TAC \\ (* 2 subgoals, same tactics *)
         MATCH_MP_TAC pos_not_neginf \\
         MATCH_MP_TAC expectation_pos >> rw [] \\
         MATCH_MP_TAC le_mul >> rw [le_pow2, INDICATOR_FN_POS]) \\
     Q.X_GEN_TAC ‘i’ >> RW_TAC std_ss [IN_COUNT] \\
     Know ‘expectation p (\x. X i x pow 2 *
                              indicator_fn {y | y IN p_space p /\ abs (X i y) < &SUC i} x) =
       pos_fn_integral p (\x. X i x pow 2 *
                              indicator_fn {y | y IN p_space p /\ abs (X i y) < &SUC i} x)’
     >- (REWRITE_TAC [expectation_def] \\
         MATCH_MP_TAC integral_pos_fn \\
         CONJ_TAC >- FULL_SIMP_TAC std_ss [prob_space_def] \\
         RW_TAC std_ss [] \\
         MATCH_MP_TAC le_mul >> rw [le_pow2, INDICATOR_FN_POS]) >> Rewr' \\
     Know ‘expectation p (\x. X i x pow 2 *
                              indicator_fn {x | x IN p_space p /\ abs (X i x) < &SUC n} x) =
       pos_fn_integral p (\x. X i x pow 2 *
                              indicator_fn {x | x IN p_space p /\ abs (X i x) < &SUC n} x)’
     >- (REWRITE_TAC [expectation_def] \\
         MATCH_MP_TAC integral_pos_fn \\
         CONJ_TAC >- FULL_SIMP_TAC std_ss [prob_space_def] \\
         RW_TAC std_ss [] \\
         MATCH_MP_TAC le_mul >> rw [le_pow2, INDICATOR_FN_POS]) >> Rewr' \\
     MATCH_MP_TAC pos_fn_integral_mono >> BETA_TAC \\
     CONJ_TAC >- (rpt STRIP_TAC \\
                  MATCH_MP_TAC le_mul >> rw [le_pow2, INDICATOR_FN_POS]) \\
    ‘SUC i <= SUC n’ by RW_TAC arith_ss [] \\
     rpt STRIP_TAC \\
     MATCH_MP_TAC le_lmul_imp >> art [le_pow2] \\
     MATCH_MP_TAC INDICATOR_FN_MONO >> simp [SUBSET_DEF] \\
     Q.X_GEN_TAC ‘y’ >> STRIP_TAC \\
     MATCH_MP_TAC lte_trans \\
     Q.EXISTS_TAC ‘&SUC i’ >> rw [extreal_of_num_def, extreal_le_eq])
 >> REWRITE_TAC [CARD_COUNT]
 >> DISCH_TAC
 (* sub-sequence ‘u n’ and its properties *)
 >> Q.ABBREV_TAC ‘u = \(a :real) n. flr (a pow n)’
 >> ‘!a n. 1 < a ==> 0 < u a n’
      by (rw [Abbr ‘u’, GSYM pow_seq_def, pow_seq_pos_lt])
 >> Know ‘!a n. 1 < a ==> a pow n / 2 <= &u a n’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC REAL_LT_IMP_LE \\
     RW_TAC std_ss [Abbr ‘u’, GSYM pow_seq_def, pow_seq_lower_bound])
 >> DISCH_TAC
 >> ‘!a (x :real). 1 < a ==> ?n. x < &u a (SUC n)’
      by (rw [Abbr ‘u’, GSYM pow_seq_def, pow_seq_unbounded])
 >> ‘!a i j. 1 < a /\ i <= j ==> u a i <= u a j’
      by (rw [Abbr ‘u’, GSYM pow_seq_def, pow_seq_monotone])
(* stage work *)
 >> Q.ABBREV_TAC ‘A = \n x. (Z n x - expectation p (Z n)) / &n’
 >> Q.ABBREV_TAC ‘W = \a n x. A (u a (SUC n)) x’
 >> Know ‘!a. 1 < a ==> (W a --> (\x. 0)) (almost_everywhere p)’
 >- (rpt STRIP_TAC \\
    ‘1 <= a’ by PROVE_TAC [REAL_LT_IMP_LE] \\
    ‘0 <  a’ by PROVE_TAC [REAL_LT_01, REAL_LT_TRANS] \\
    ‘0 <= a’ by PROVE_TAC [REAL_LT_IMP_LE] \\
    ‘a <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] \\
     Q.PAT_X_ASSUM ‘!a n. 1 < a ==> 0 < u a n’
       (ASSUME_TAC o (fn th => MATCH_MP th (ASSUME “1 < (a :real)”))) \\
    ‘!n. (0 :real) < &u a n’ by rw [] \\
    ‘!n. &u a n <> (0 :real)’ by PROVE_TAC [REAL_LT_IMP_NE] \\
    ‘!n. &u a n pow 2 <> (0 :real)’ by PROVE_TAC [POW_NZ] \\
  (* applying converge_AE_alt_limsup' *)
     Know ‘!n. real_random_variable (W a n) p’
     >- (MP_TAC (Q.SPECL [‘p’, ‘Y’, ‘Z’, ‘\n. (u :real -> num -> num) a (SUC n)’]
                         real_random_variable_LLN_general) \\
         RW_TAC std_ss [Abbr ‘W’, Abbr ‘A’]) >> DISCH_TAC \\
     rw [converge_AE_alt_limsup'] \\
     Q.PAT_X_ASSUM ‘!n x. x IN p_space p ==> Y n x = _’ K_TAC \\
  (* applying Borel-Cantelli Lemma *)
     MATCH_MP_TAC Borel_Cantelli_Lemma1 >> simp [o_DEF] \\
     STRONG_CONJ_TAC (* IN events p *)
     >- (rw [lt_abs_bounds, events_def, p_space_def] \\
        ‘{x | x IN m_space p /\ (W a n x < -e \/ e < W a n x)} =
         ({x | W a n x < -e} INTER m_space p) UNION
         ({x | e < W a n x} INTER m_space p)’ by SET_TAC [] >> POP_ORW \\
         MATCH_MP_TAC MEASURE_SPACE_UNION \\
         CONJ_TAC >- FULL_SIMP_TAC std_ss [prob_space_def] \\
         Q.PAT_X_ASSUM ‘!n. real_random_variable (W a n) p’
           (STRIP_ASSUME_TAC o
            (REWRITE_RULE [real_random_variable, p_space_def, events_def])) \\
         METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘!n. real_random_variable (W a n) p’ K_TAC \\
  (* preparing for chebyshev_ineq_variance' *)
     Q.ABBREV_TAC ‘S = \n x. Z (u a (SUC n)) x / &u a (SUC n)’ \\
     Know ‘!n. real_random_variable (S n) p’
     >- (rw [Abbr ‘S’, extreal_of_num_def] \\
         MATCH_MP_TAC real_random_variable_cdiv >> art []) >> DISCH_TAC \\
     Know ‘!n. finite_second_moments p (S n)’
     >- (rw [Abbr ‘S’, extreal_of_num_def] \\
         MATCH_MP_TAC finite_second_moments_cdiv >> art []) >> DISCH_TAC \\
  (* stage work *)
     Know ‘!n. {x | x IN p_space p /\ e < abs (W a n x)} =
               {x | e < abs (S n x - expectation p (S n))} INTER p_space p’
     >- (rw [Once EXTENSION] \\
         Suff ‘x IN p_space p ==> W a n x = S n x - expectation p (S n)’ >- METIS_TAC [] \\
         RW_TAC std_ss [Abbr ‘W’, Abbr ‘A’, Abbr ‘S’, Once EQ_SYM_EQ] \\
         Suff ‘expectation p (\x. Z (u a (SUC n)) x / &u a (SUC n)) =
               expectation p (Z (u a (SUC n))) / &u a (SUC n)’
         >- (Rewr' >> MATCH_MP_TAC div_sub \\
             SIMP_TAC std_ss [extreal_of_num_def, extreal_11] \\
             Know ‘Z (u a (SUC n)) x <> PosInf /\ Z (u a (SUC n)) x <> NegInf’
             >- (FULL_SIMP_TAC std_ss [real_random_variable]) >> Rewr \\
             Know ‘expectation p (Z (u a (SUC n))) <> PosInf /\
                   expectation p (Z (u a (SUC n))) <> NegInf’
             >- (MATCH_MP_TAC expectation_finite >> art []) >> Rewr \\
             rw []) \\
         REWRITE_TAC [extreal_of_num_def] \\
         MATCH_MP_TAC expectation_cdiv >> art []) \\
     DISCH_THEN (FULL_SIMP_TAC std_ss o wrap) \\
     qunabbrevl_tac [‘W’, ‘A’] \\
  (* applying chebyshev_ineq_variance' *)
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘suminf (\n. inv (e pow 2) * variance p (S n))’ \\
     CONJ_TAC (* suminf <= suminf *)
     >- (MATCH_MP_TAC ext_suminf_mono \\
         rw [] >- (MATCH_MP_TAC PROB_POSITIVE >> art []) \\
         MATCH_MP_TAC chebyshev_ineq_variance' >> art []) \\
  (* cleanup S-assumptions *)
     Q.PAT_X_ASSUM ‘!n. _ INTER p_space p IN events p’ K_TAC \\
     Q.PAT_X_ASSUM ‘!n. real_random_variable (S n) p’  K_TAC \\
     Q.PAT_X_ASSUM ‘!n. finite_second_moments p (S n)’ K_TAC \\
     SIMP_TAC std_ss [Abbr ‘S’, extreal_of_num_def] \\
     Know ‘!n. variance p (\x. Z (u a (SUC n)) x / Normal (&u a (SUC n))) =
               variance p (Z (u a (SUC n))) / Normal ((&u a (SUC n)) pow 2)’
     >- (Q.X_GEN_TAC ‘n’ \\
         MATCH_MP_TAC variance_cdiv >> art []) >> Rewr' \\
     ASM_SIMP_TAC std_ss [Once mul_comm, extreal_div_def, GSYM mul_assoc] \\
     ONCE_REWRITE_TAC [mul_comm] \\
  (* now use the estimates of variance p (Z n) in assumptions *)
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC
      ‘suminf (\n. inv (Normal (&u a (SUC n) pow 2)) * inv (e pow 2) *
                   (\n. &n * expectation p
                               (\x. X 0 x pow 2 *
                                    indicator_fn {x | x IN p_space p /\ abs (X 0 x) < &n} x))
                   (u a (SUC n)))’ >> BETA_TAC \\
     CONJ_TAC
     >- (MATCH_MP_TAC ext_suminf_mono >> BETA_TAC \\
         Know ‘!n. 0 <= inv (Normal (&u a (SUC n) pow 2)) * inv (e pow 2)’
         >- (Q.X_GEN_TAC ‘n’ \\
             MATCH_MP_TAC le_mul \\
             CONJ_TAC >> MATCH_MP_TAC le_inv >| (* 2 subgoals *)
             [ RW_TAC arith_ss [extreal_of_num_def, extreal_lt_eq, ZERO_LT_POW],
               MATCH_MP_TAC pow_pos_lt >> art [] ]) >> DISCH_TAC \\
         CONJ_TAC >> Q.X_GEN_TAC ‘n’ >| (* 2 subgoals *)
         [ MATCH_MP_TAC le_mul >> rw [variance_pos],
           MATCH_MP_TAC le_lmul_imp >> art [] ]) \\
     NTAC 2 (Q.PAT_X_ASSUM ‘!n. variance p (Z n) <= _’ K_TAC) \\
     Q.PAT_X_ASSUM ‘!n. real_random_variable (Z n) p’  K_TAC \\
     Q.PAT_X_ASSUM ‘!n. integrable p (Z n)’            K_TAC \\
     Q.PAT_X_ASSUM ‘!n. finite_second_moments p (Z n)’ K_TAC \\
     Q.UNABBREV_TAC ‘Z’ \\
  (* combined multiple occurrences of ‘&u a (SUC n)’ *)
     REWRITE_TAC [mul_assoc] \\
     Know ‘!n. inv (Normal (&u a (SUC n) pow 2)) * inv (e pow 2) * &u a (SUC n) =
               inv (Normal (&u a (SUC n) pow 2)) * Normal (&u a (SUC n)) * inv (e pow 2)’
     >- (METIS_TAC [extreal_of_num_def, mul_assoc, mul_comm]) >> Rewr' \\
     Know ‘!n. realinv (Normal (&u a (SUC n) pow 2)) * Normal (&u a (SUC n)) =
               Normal (inv (&u a (SUC n)))’
     >- (rw [extreal_inv_eq, extreal_mul_def, extreal_pow_def]) >> Rewr' \\
  (* stage work *)
    ‘e <> NegInf’ by PROVE_TAC [pos_not_neginf, lt_imp_le] \\
    ‘?E. 0 < E /\ e = Normal E’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] >> POP_ORW \\
     Q.PAT_X_ASSUM ‘0 < e’         K_TAC \\
     Q.PAT_X_ASSUM ‘e <> PosInf’   K_TAC \\
     Q.PAT_X_ASSUM ‘e <> NegInf’   K_TAC \\
    ‘E pow 2 <> 0’ by METIS_TAC [POW_NZ, REAL_LT_IMP_NE] \\
     ASM_SIMP_TAC real_ss [extreal_pow_def, extreal_inv_def, extreal_mul_def] \\
     Know ‘!n. Normal (inv (&u a (SUC n)) * inv (E pow 2)) *
               expectation p
                 (\x. X 0 x pow 2 *
                      indicator_fn
                        {x | x IN p_space p /\ abs (X 0 x) < &u a (SUC n)} x) =
               expectation p
                 (\x. Normal (inv (&u a (SUC n)) * inv (E pow 2)) *
                      (\x. X 0 x pow 2 *
                           indicator_fn
                             {x | x IN p_space p /\ abs (X 0 x) < &u a (SUC n)} x) x)’
     >- (Q.X_GEN_TAC ‘n’ \\
         ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC expectation_cmul >> art [] \\
         MATCH_MP_TAC bounded_imp_integrable \\
         ASM_SIMP_TAC std_ss [] \\
         CONJ_TAC (* random_variable *)
         >- (Q.ABBREV_TAC ‘N = PRE (u a (SUC n))’ \\
             Know ‘random_variable
                     (\x. X 0 x pow 2 *
                          indicator_fn
                            {x | x IN p_space p /\ abs (X 0 x) < &u a (SUC n)} x) p Borel <=>
                   random_variable ((\x. x pow 2) o (f N) o (X 0)) p Borel’
             >- (MATCH_MP_TAC random_variable_cong \\
                 rpt STRIP_TAC \\
                 RW_TAC real_ss [Abbr ‘f’, Abbr ‘N’, o_DEF, extreal_lt_def,
                                 indicator_fn_def, GSPECIFICATION, mul_rzero, mul_rone,
                                 zero_pow, lt_02, fst (EQ_IMP_RULE SUC_PRE)] \\
                 PROVE_TAC []) >> Rewr' \\
             MATCH_MP_TAC random_variable_comp >> rw [IN_MEASURABLE_BOREL_BOREL_POW] \\
             Q.PAT_X_ASSUM `!n. real_random_variable (X n) p`
               (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
                (REWRITE_RULE [real_random_variable_def])) \\
             MATCH_MP_TAC random_variable_comp >> art []) \\
         Q.EXISTS_TAC ‘(&u a (SUC n)) pow 2’ \\
         RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, abs_0, GSPECIFICATION] >|
         [ (* goal 1 (of 2) *)
          ‘abs (X 0 x pow 2) = (abs (X 0 x)) pow 2’
             by RW_TAC std_ss [pow_2, abs_mul] >> POP_ORW \\
          ‘Normal (&u a (SUC n) pow 2) = (&u a (SUC n)) pow 2’
             by RW_TAC std_ss [POW_2, pow_2, extreal_of_num_def, extreal_mul_def] >> POP_ORW \\
           MATCH_MP_TAC pow_le >> REWRITE_TAC [abs_pos] \\
           MATCH_MP_TAC lt_imp_le >> art [],
           (* goal 2 (of 2) *)
           rw [extreal_of_num_def, extreal_le_eq] ]) \\
     DISCH_THEN (ONCE_REWRITE_TAC o wrap o BETA_RULE) \\
  (* preparing for swapping ‘suminf’ and ‘expectation’ *)
     FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, events_def] \\
     Know ‘!n. expectation p
                 (\x. Normal (inv (&u a (SUC n)) * inv (E pow 2)) *
                      (X 0 x pow 2 *
                       indicator_fn
                         {x | x IN m_space p /\ abs (X 0 x) < &u a (SUC n)} x)) =
               pos_fn_integral p
                 (\x. Normal (inv (&u a (SUC n)) * inv (E pow 2)) *
                      (X 0 x pow 2 *
                       indicator_fn
                         {x | x IN m_space p /\ abs (X 0 x) < &u a (SUC n)} x))’
     >- (RW_TAC std_ss [expectation_def] \\
         MATCH_MP_TAC integral_pos_fn \\
         RW_TAC std_ss [] \\
         MATCH_MP_TAC le_mul \\
         CONJ_TAC >- rw [extreal_of_num_def, extreal_le_eq] \\
         MATCH_MP_TAC le_mul >> rw [le_pow2, INDICATOR_FN_POS]) >> Rewr' \\
  (* applying pos_fn_integral_suminf *)
     Q.ABBREV_TAC ‘g = \n x. Normal (inv (&u a (SUC n)) * inv (E pow 2)) *
                            (X 0 x pow 2 *
                             indicator_fn
                               {x | x IN m_space p /\ abs (X 0 x) < &u a (SUC n)} x)’ \\
     ASM_SIMP_TAC std_ss [] \\
     Know ‘suminf (\n. pos_fn_integral p (g n)) =
           pos_fn_integral p (\x. suminf (\n. g n x))’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC pos_fn_integral_suminf >> ASM_SIMP_TAC std_ss [Abbr ‘g’] \\
         CONJ_TAC >- (rpt STRIP_TAC \\
                      MATCH_MP_TAC le_mul \\
                      CONJ_TAC >- rw [extreal_of_num_def, extreal_le_eq] \\
                      MATCH_MP_TAC le_mul >> rw [le_pow2, INDICATOR_FN_POS]) \\
         Q.X_GEN_TAC ‘n’ \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL \\
        ‘sigma_algebra (m_space p,measurable_sets p)’ by PROVE_TAC [measure_space_def] \\
         qexistsl_tac [‘\x. X 0 x pow 2 *
                            indicator_fn
                              {x | x IN m_space p /\ abs (X 0 x) < &u a (SUC n)} x’,
                       ‘inv (&u a (SUC n)) * inv (E pow 2)’] >> rw [] \\
         HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR >> rw [] \\
         Q.PAT_X_ASSUM `!n. real_random_variable (X n) p`
           (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
            (REWRITE_RULE [real_random_variable, p_space_def, events_def])) \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_POW >> art []) \\
     Q.UNABBREV_TAC ‘g’ >> BETA_TAC >> Rewr' \\
  (* now let's move out ‘inv (E pow 2)’ *)
     REWRITE_TAC [Once (GSYM extreal_mul_def)] \\
    ‘!n. Normal (inv (&u a (SUC n))) * Normal (inv (E pow 2)) =
         Normal (inv (E pow 2)) * Normal (inv (&u a (SUC n)))’
       by PROVE_TAC [mul_comm] >> POP_ORW \\
     REWRITE_TAC [GSYM mul_assoc] \\
     Q.ABBREV_TAC ‘c = Normal (inv (E pow 2))’ \\
     Q.ABBREV_TAC ‘g = \x n. Normal (inv (&u a (SUC n))) *
                            (X 0 x pow 2 *
                             indicator_fn
                               {x | x IN m_space p /\ abs (X 0 x) < &u a (SUC n)} x)’ \\
     ASM_SIMP_TAC std_ss [] \\
     Know ‘!x n. 0 <= g x n’
     >- (rw [Abbr ‘g’] >> MATCH_MP_TAC le_mul \\
         CONJ_TAC >- rw [extreal_of_num_def, extreal_le_eq] \\
         MATCH_MP_TAC le_mul >> rw [le_pow2, INDICATOR_FN_POS]) >> DISCH_TAC \\
     Know ‘!x. suminf (\n. c * g x n) = c * suminf (g x)’
     >- (Q.X_GEN_TAC ‘y’ >> MATCH_MP_TAC ext_suminf_cmul \\
         rw [Abbr ‘c’, extreal_of_num_def, extreal_le_eq]) >> Rewr' \\
     qunabbrevl_tac [‘c’] \\
     Know ‘pos_fn_integral p (\x. Normal (inv (E pow 2)) * (suminf o g) x) =
           Normal (inv (E pow 2)) * pos_fn_integral p (suminf o g)’
     >- (MATCH_MP_TAC pos_fn_integral_cmul >> art [] \\
         reverse CONJ_TAC >- (MATCH_MP_TAC REAL_LE_INV >> REWRITE_TAC [REAL_LE_POW2]) \\
         rw [o_DEF] >> MATCH_MP_TAC ext_suminf_pos >> art []) \\
     DISCH_THEN (ONCE_REWRITE_TAC o wrap o (SIMP_RULE std_ss [o_DEF])) \\
  (* now eliminate ‘E’ *)
     Suff ‘pos_fn_integral p (\x. suminf (g x)) < PosInf’
     >- (RW_TAC std_ss [GSYM lt_infty] \\
         Know ‘pos_fn_integral p (\x. suminf (g x)) <> NegInf’
         >- (MATCH_MP_TAC pos_not_neginf \\
             MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
             MATCH_MP_TAC ext_suminf_pos >> art []) >> DISCH_TAC \\
        ‘?r. pos_fn_integral p (\x. suminf (g x)) = Normal r’ by METIS_TAC [extreal_cases] \\
         rw [extreal_mul_def]) \\
     Q.PAT_X_ASSUM ‘0 < E’            K_TAC \\
     Q.PAT_X_ASSUM ‘E pow 2 <> 0’     K_TAC \\
     Q.PAT_X_ASSUM ‘!x n. 0 <= g x n’ K_TAC \\
     SIMP_TAC std_ss [Abbr ‘g’] \\
  (* now move out ‘X 0 x pow 2’ from ‘suminf’ *)
     REWRITE_TAC [mul_assoc] \\
    ‘!n x. Normal (inv (&u a (SUC n))) * X 0 x pow 2 =
           X 0 x pow 2 * Normal (inv (&u a (SUC n)))’
        by PROVE_TAC [mul_comm] >> POP_ORW \\
     REWRITE_TAC [GSYM mul_assoc] \\
     Q.ABBREV_TAC ‘g = \x n. Normal (inv (&u a (SUC n))) *
                             indicator_fn
                               {x | x IN m_space p /\ abs (X 0 x) < &u a (SUC n)} x’ \\
     ASM_SIMP_TAC std_ss [] \\
     Know ‘!x. suminf (\n. X 0 x pow 2 * g x n) = X 0 x pow 2 * suminf (g x)’
     >- (Q.X_GEN_TAC ‘y’ >> MATCH_MP_TAC ext_suminf_cmul \\
         rw [le_pow2, Abbr ‘g’] \\
         MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS] \\
         rw [extreal_of_num_def, extreal_le_eq]) >> Rewr' \\
     SIMP_TAC std_ss [Abbr ‘g’] \\
    ‘!n. Normal (inv (&u a (SUC n))) = inv (&u a (SUC n))’
       by (rw [extreal_inv_def, extreal_of_num_def]) >> POP_ORW \\
  (* stage work *)
     Q.ABBREV_TAC ‘N = \(x :extreal). LEAST n. x < &u a (SUC n)’ \\
  (* prove existence of ‘N’ *)
     Know ‘!(x :real). ?n. x < &u a (SUC n)’
     >- (Q.X_GEN_TAC ‘x’ \\
         Q.PAT_X_ASSUM ‘!a x. 1 < a ==> ?n. x < &u a (SUC n)’
           (fn th => STRIP_ASSUME_TAC
                       (Q.SPEC ‘x’ (MATCH_MP th (ASSUME “1 < (a :real)”)))) \\
         Q.EXISTS_TAC ‘n’ >> art []) >> DISCH_TAC \\
  (* eliminate ‘indicator_fn’ *)
     Know ‘pos_fn_integral p
             (\x. X 0 x pow 2 *
                  suminf
                    (\n. inv (&u a (SUC n)) *
                         indicator_fn {x | x IN m_space p /\ abs (X 0 x) < &u a (SUC n)} x)) =
           pos_fn_integral p
             (\x. X 0 x pow 2 *
                  suminf (\n. inv (&u a (SUC (n + N (abs (X 0 x)))))))’
     >- (MATCH_MP_TAC pos_fn_integral_cong >> ASM_SIMP_TAC std_ss [] \\
         CONJ_TAC
         >- (rpt STRIP_TAC \\
             MATCH_MP_TAC le_mul >> rw [le_pow2] \\
             MATCH_MP_TAC ext_suminf_pos >> rw [] \\
             MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS] \\
             MATCH_MP_TAC le_inv >> rw [extreal_of_num_def, extreal_lt_eq]) \\
         CONJ_TAC
         >- (rpt STRIP_TAC \\
             MATCH_MP_TAC le_mul >> rw [le_pow2] \\
             MATCH_MP_TAC ext_suminf_pos >> rw [] \\
             MATCH_MP_TAC le_inv >> rw [extreal_of_num_def, extreal_lt_eq]) \\
         rpt STRIP_TAC \\
         Suff ‘suminf
                 (\n. inv (&u a (SUC n)) *
                      indicator_fn {x | x IN m_space p /\ abs (X 0 x) < &u a (SUC n)} x) =
               suminf (\n. realinv (&u a (SUC (n + N (abs (X 0 x))))))’ >- Rewr \\
         ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC ext_suminf_eq_shift \\
         Q.ABBREV_TAC ‘e = abs (X 0 x)’ \\
        ‘0 <= e’ by METIS_TAC [abs_pos] \\
         Know ‘e <> PosInf /\ e <> NegInf’
         >- (Q.UNABBREV_TAC ‘e’ \\
             Suff ‘X 0 x <> PosInf /\ X 0 x <> NegInf’ >- PROVE_TAC [abs_not_infty] \\
             FULL_SIMP_TAC std_ss [real_random_variable_def, p_space_def]) \\
         STRIP_TAC \\
         Q.EXISTS_TAC ‘N e’ >> rw [] >| (* 3 subgoals *)
         [ (* goal 1 (of 3) *)
           DISJ2_TAC >> simp [indicator_fn_def] \\
           Suff ‘~(e < &u a (SUC n))’ >- rw [] \\
           POP_ASSUM MP_TAC >> simp [Abbr ‘N’, extreal_of_num_def, extreal_lt_eq, real_lt] \\
           numLib.LEAST_ELIM_TAC \\
           reverse CONJ_TAC >- (Q.X_GEN_TAC ‘i’ >> rw []) \\
          ‘?E. e = Normal E’ by METIS_TAC [extreal_cases] >> POP_ORW \\
           simp [extreal_lt_eq, GSYM real_lt],
           (* goal 2 (of 3) *)
           MATCH_MP_TAC le_inv >> rw [extreal_of_num_def, extreal_lt_eq],
           (* goal 3 (of 3) *)
           Suff ‘e < &u a (SUC (n + N e))’ >- rw [indicator_fn_def] \\
          ‘?E. e = Normal E’ by METIS_TAC [extreal_cases] >> POP_ORW \\
           simp [Abbr ‘N’, extreal_of_num_def, extreal_lt_eq] \\
           numLib.LEAST_ELIM_TAC >> simp [] \\
           Q.X_GEN_TAC ‘i’ >> rw [] \\
           MATCH_MP_TAC REAL_LTE_TRANS \\
           Q.EXISTS_TAC ‘&u a (SUC i)’ >> rw [] ]) >> Rewr' \\
     Q.PAT_X_ASSUM ‘!n. &u a n pow 2 <> 0’ K_TAC \\
  (* eliminate NUM_FLOOR (flr), left only ‘N’ in the goal *)
     FULL_SIMP_TAC std_ss [Abbr ‘u’] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘pos_fn_integral p
                     (\x. X 0 x pow 2 *
                          suminf (\n. inv (Normal ((a :real) pow
                                                   SUC (n + N (abs (X 0 x))) / 2))))’ \\
     CONJ_TAC
     >- (MATCH_MP_TAC pos_fn_integral_mono \\
         CONJ_TAC >- (RW_TAC std_ss [] \\
                      MATCH_MP_TAC le_mul >> rw [le_pow2] \\
                      MATCH_MP_TAC ext_suminf_pos >> rw [] \\
                      MATCH_MP_TAC le_inv >> rw [extreal_of_num_def, extreal_lt_eq]) \\
         RW_TAC std_ss [] \\
         MATCH_MP_TAC le_lmul_imp >> rw [le_pow2] \\
         MATCH_MP_TAC ext_suminf_mono \\
         rw [] >- (MATCH_MP_TAC le_inv >> rw [extreal_of_num_def, extreal_lt_eq]) \\
         Know ‘inv (&flr (a pow SUC (n + N (abs (X 0 x))))) <=
               inv (Normal (a pow SUC (n + N (abs (X 0 x))) / 2)) <=>
               Normal (a pow SUC (n + N (abs (X 0 x))) / 2) <=
               &flr (a pow SUC (n + N (abs (X 0 x))))’
         >- (MATCH_MP_TAC inv_le_antimono >> rw [extreal_of_num_def, extreal_lt_eq] \\
             MATCH_MP_TAC POW_POS_LT >> art []) >> Rewr' \\
         RW_TAC std_ss [extreal_of_num_def, extreal_le_eq]) \\
     Q.PAT_X_ASSUM ‘!b n. 1 < b ==> b pow n / 2 <= &flr (b pow n)’ K_TAC \\
     Know ‘!x n. inv (Normal (a pow SUC (n + N (abs (X 0 x))) / 2)) =
                 Normal (inv (a pow SUC (n + N (abs (X 0 x))) / 2))’
     >- (rpt STRIP_TAC \\
         Suff ‘a pow SUC (n + N (abs (X 0 x))) / 2 <> 0’ >- rw [extreal_inv_eq] \\
         Suff ‘0 < a pow SUC (n + N (abs (X 0 x))) / 2’ >- PROVE_TAC [REAL_LT_IMP_NE] \\
         MATCH_MP_TAC REAL_LT_DIV \\
         reverse CONJ_TAC >- rw [] (* 0 < 2 *) \\
         MATCH_MP_TAC POW_POS_LT >> art []) >> Rewr' \\
     Know ‘!x n. inv (a pow SUC (n + N (abs (X 0 x))) / 2) =
                 2 * inv (a pow SUC (n + N (abs (X 0 x))))’
     >- (qx_genl_tac [‘x’, ‘n’] \\
         MATCH_MP_TAC REAL_INV_DIV >> rw []) >> Rewr' \\
    ‘!x n. SUC (n + N (abs (X 0 x))) = n + SUC (N (abs (X 0 x)))’ by rw [] >> POP_ORW \\
     REWRITE_TAC [REAL_POW_ADD] \\
     Know ‘!x n. inv (a pow n * a pow SUC (N (abs (X 0 x)))) =
                 inv (a pow SUC (N (abs (X 0 x)))) * inv (a pow n)’
     >- (qx_genl_tac [‘x’, ‘n’] \\
         GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [REAL_MUL_COMM] \\
         MATCH_MP_TAC REAL_INV_MUL \\
         CONJ_TAC >> MATCH_MP_TAC POW_NZ >> art []) >> Rewr' \\
     REWRITE_TAC [mul_assoc, GSYM extreal_mul_eq] \\
     Know ‘!x n. suminf (\n. Normal 2 *
                             Normal (inv (a pow SUC (N (abs (X 0 x))))) *
                             Normal (inv (a pow n))) =
                 Normal 2 * Normal (inv (a pow SUC (N (abs (X 0 x))))) *
                 suminf (\n. Normal (inv (a pow n)))’
     >- (qx_genl_tac [‘x’, ‘n’] \\
         HO_MATCH_MP_TAC ext_suminf_cmul \\
         rw [extreal_of_num_def, extreal_le_eq, extreal_mul_eq]) >> Rewr' \\
     REWRITE_TAC [mul_assoc, GSYM extreal_of_num_def] \\
  (* applying geometric_series_pow *)
     Know ‘!n. Normal (inv (a pow n)) = (inv (Normal a)) pow n’
     >- (Q.X_GEN_TAC ‘n’ \\
        ‘a pow n <> 0’ by PROVE_TAC [POW_NZ] \\
         rw [extreal_pow_def, extreal_inv_eq, REAL_POW_INV]) >> Rewr' \\
     Q.ABBREV_TAC ‘b = inv (Normal a)’ \\
     Know ‘suminf (\n. b pow n) = inv (1 - b)’
     >- (MATCH_MP_TAC geometric_series_pow \\
         rw [Abbr ‘b’] >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           rw [extreal_inv_def, extreal_of_num_def, extreal_lt_eq],
           (* goal 2 (of 2) *)
           rw [extreal_inv_def, extreal_of_num_def, extreal_lt_eq] ]) >> Rewr' \\
     Q.UNABBREV_TAC ‘b’ \\
     Q.ABBREV_TAC ‘c = inv (1 - inv (Normal a))’ \\
     Know ‘0 <= c’
     >- (Q.UNABBREV_TAC ‘c’ \\
         MATCH_MP_TAC le_inv \\
         rw [extreal_of_num_def, extreal_inv_eq, extreal_sub_def,
             extreal_lt_eq, REAL_SUB_LT]) >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘!n. 0 < flr (a pow n)’   K_TAC \\
     Q.PAT_X_ASSUM ‘!n. 0 < &flr (a pow n)’  K_TAC \\
     Q.PAT_X_ASSUM ‘!n. &flr (a pow n) <> 0’ K_TAC \\
  (* collect all constants so far *)
    ‘!x. X 0 x pow 2 * 2 * inv (Normal a) pow SUC (N (abs (X 0 x))) * c =
         2 * c * X 0 x pow 2 * inv (Normal a) pow SUC (N (abs (X 0 x)))’
       by METIS_TAC [mul_comm, mul_assoc] >> POP_ORW \\
  (* key property of ‘N’ due to LEAST *)
     Know ‘!x. x <> PosInf /\ x <> NegInf ==> x <= Normal (a pow (SUC (N x)))’
     >- (rw [Abbr ‘N’] \\
        ‘?r. x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         numLib.LEAST_ELIM_TAC \\
         rw [extreal_le_eq, extreal_lt_eq, extreal_of_num_def] \\
         MATCH_MP_TAC REAL_LE_TRANS \\
         Q.EXISTS_TAC ‘&flr (a pow SUC n)’ \\
         CONJ_TAC >- (MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
         MATCH_MP_TAC NUM_FLOOR_LE \\
         MATCH_MP_TAC POW_POS >> art []) >> DISCH_TAC \\
     Know ‘!x. inv (Normal a) pow SUC (N (abs (X 0 x))) =
               inv (Normal (a pow SUC (N (abs (X 0 x)))))’
     >- (rw [GSYM extreal_pow_def, Once EQ_SYM_EQ] \\
         MATCH_MP_TAC pow_inv >> rw [extreal_of_num_def]) >> Rewr' \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘pos_fn_integral p (\x. 2 * c * X 0 x pow 2 * inv (abs (X 0 x)))’ \\
     CONJ_TAC
     >- (MATCH_MP_TAC pos_fn_integral_mono >> rw [] >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           MATCH_MP_TAC le_mul \\
           CONJ_TAC >- (MATCH_MP_TAC le_mul >> rw [le_pow2] \\
                        MATCH_MP_TAC le_mul >> rw []) \\
           MATCH_MP_TAC le_inv >> rw [extreal_of_num_def, extreal_lt_eq] \\
           MATCH_MP_TAC POW_POS_LT >> art [],
           (* goal 2 (of 2) *)
           REWRITE_TAC [pow_2_abs, mul_assoc] \\
           Cases_on ‘abs (X 0 x) = 0’ >- rw [] \\
           MATCH_MP_TAC le_lmul_imp \\
           CONJ_TAC >- (MATCH_MP_TAC le_mul >> rw [le_abs] \\
                        MATCH_MP_TAC le_mul >> rw [le_abs] \\
                        MATCH_MP_TAC le_mul >> rw []) \\
           Know ‘inv (Normal (a pow SUC (N (abs (X 0 x))))) <= inv (abs (X 0 x)) <=>
                 abs (X 0 x) <= Normal (a pow SUC (N (abs (X 0 x))))’
           >- (MATCH_MP_TAC inv_le_antimono \\
               CONJ_TAC >- (rw [extreal_of_num_def, extreal_lt_eq] \\
                            MATCH_MP_TAC POW_POS_LT >> art []) \\
               rw [] >> CCONTR_TAC >> FULL_SIMP_TAC std_ss [abs_0]) >> Rewr' \\
           FIRST_X_ASSUM MATCH_MP_TAC \\
           MATCH_MP_TAC abs_not_infty \\
           FULL_SIMP_TAC std_ss [real_random_variable_def, p_space_def] ]) \\
     Know ‘1 - inv a <> 0’
     >- (rw [] \\
        ‘inv a = 1 <=> inv (inv a) = inv 1’ by PROVE_TAC [REAL_INV_INJ] >> POP_ORW \\
         ASM_SIMP_TAC std_ss [REAL_INVINV, REAL_INV1] \\
         PROVE_TAC [REAL_LT_IMP_NE]) >> DISCH_TAC \\
     Know ‘2 * c = Normal (2 * inv (1 - inv a))’
     >- (rw [Abbr ‘c’, extreal_of_num_def, extreal_inv_def, extreal_sub_def,
             extreal_mul_def]) >> Rewr' \\
     Q.PAT_X_ASSUM ‘0 <= c’ K_TAC \\
     Q.UNABBREV_TAC ‘c’ \\
  (* re-collect all constant factors *)
     Q.ABBREV_TAC ‘c = 2 * inv (1 - inv a)’ \\
     Know ‘0 <= c’
     >- (Q.UNABBREV_TAC ‘c’ \\
         MATCH_MP_TAC REAL_LE_MUL >> rw [REAL_SUB_LE]) >> DISCH_TAC \\
     Know ‘pos_fn_integral p (\x. Normal c * (\x. X 0 x pow 2 * inv (abs (X 0 x))) x) =
           Normal c * pos_fn_integral p (\x. X 0 x pow 2 * inv (abs (X 0 x)))’
     >- (MATCH_MP_TAC pos_fn_integral_cmul >> rw [] \\
         Cases_on ‘X 0 x = 0’ >- rw [zero_pow] \\
         MATCH_MP_TAC le_mul >> rw [le_pow2] \\
         MATCH_MP_TAC le_inv >> rw []) \\
     BETA_TAC >> REWRITE_TAC [mul_assoc] >> Rewr' \\
     Know ‘pos_fn_integral p (\x. X 0 x pow 2 * inv (abs (X 0 x))) =
           pos_fn_integral p (abs o (X 0))’
     >- (rw [o_DEF] \\
         MATCH_MP_TAC pos_fn_integral_cong >> rw []
         >- (Cases_on ‘X 0 x = 0’ >- rw [zero_pow] \\
             MATCH_MP_TAC le_mul >> rw [le_pow2] \\
             MATCH_MP_TAC le_inv >> rw []) \\
         REWRITE_TAC [pow_2_abs, GSYM mul_assoc] \\
         Cases_on ‘X 0 x = 0’ >- rw [] \\
         Suff ‘abs (X 0 x) * inv (abs (X 0 x)) = 1’ >- rw [] \\
         ONCE_REWRITE_TAC [mul_comm] \\
         MATCH_MP_TAC mul_linv_pos >> rw [] \\
         Suff ‘X 0 x <> PosInf /\ X 0 x <> NegInf’ >- PROVE_TAC [abs_not_infty] \\
         FULL_SIMP_TAC std_ss [real_random_variable_def, p_space_def]) >> Rewr' \\
     Suff ‘pos_fn_integral p (abs o X 0) <> PosInf’
     >- (DISCH_TAC \\
         Know ‘pos_fn_integral p (abs o X 0) <> NegInf’
         >- (MATCH_MP_TAC pos_not_neginf \\
             MATCH_MP_TAC pos_fn_integral_pos >> rw [o_DEF, abs_pos]) >> DISCH_TAC \\
        ‘?r. pos_fn_integral p (abs o X 0) = Normal r’ by METIS_TAC [extreal_cases] \\
         rw [GSYM lt_infty, extreal_mul_def]) \\
     Know ‘pos_fn_integral p (abs o X 0) = integral p (abs o X 0)’
     >- (rw [integral_abs_pos_fn, Once EQ_SYM_EQ]) >> Rewr' \\
    ‘integrable p (abs o X 0)’ by PROVE_TAC [integrable_abs] \\
     METIS_TAC [integrable_finite_integral])
 >> DISCH_TAC
 >> NTAC 2 (Q.PAT_X_ASSUM ‘!n. variance p (Z n) <= _’ K_TAC)
 >> FULL_SIMP_TAC std_ss [Abbr ‘A’, Abbr ‘W’]
 (* stage work *)
 >> Know ‘!a. 1 < a ==>
              ((\n x. (Z (u a (SUC n)) x / &u a (SUC n) -
                       expectation p (Z (u a (SUC n))) / &u a (SUC n))) -->
               (\x. 0)) (almost_everywhere p)’
 >- (rpt STRIP_TAC \\
     Suff ‘((\n x. (Z (u a (SUC n)) x / &u a (SUC n) -
                   expectation p (Z (u a (SUC n))) / &u a (SUC n))) -->
            (\x. 0)) (almost_everywhere p) <=>
           ((\n x. (Z (u a (SUC n)) x - expectation p (Z (u a (SUC n)))) /
                   &u a (SUC n)) --> (\x. 0)) (almost_everywhere p)’
     >- (Rewr' \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     MATCH_MP_TAC converge_AE_cong \\
     Q.EXISTS_TAC ‘0’ >> RW_TAC arith_ss [] \\
     MATCH_MP_TAC div_sub \\
     Know ‘Z (u a (SUC n)) x <> PosInf /\ Z (u a (SUC n)) x <> NegInf’
     >- (FULL_SIMP_TAC std_ss [real_random_variable]) >> Rewr \\
     Know ‘expectation p (Z (u a (SUC n))) <> PosInf /\
           expectation p (Z (u a (SUC n))) <> NegInf’
     >- (MATCH_MP_TAC expectation_finite >> art []) >> Rewr \\
     rw [extreal_of_num_def] \\
     Suff ‘0 < u a (SUC n)’ >- ARITH_TAC \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> POP_ASSUM K_TAC >> DISCH_TAC
 (* applying converge_AE_to_limit' *)
 >> Know ‘!a. 1 < a ==> ((\n x. Z (u a (SUC n)) x / &u a (SUC n)) --> (\x. m))
                         (almost_everywhere p)’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC converge_AE_to_limit' \\
     Q.EXISTS_TAC ‘\n. expectation p (Z (u a (SUC n))) / &u a (SUC n)’ >> simp [] \\
     CONJ_TAC (* real_random_variable *)
     >- (rw [Abbr ‘Z’] \\
         MATCH_MP_TAC real_random_variable_LLN_general' >> rw []) \\
     CONJ_TAC (* expectation <> PosInf | NegInf *)
     >- (Q.X_GEN_TAC ‘n’ \\
         Know ‘expectation p (Z (u a (SUC n))) <> PosInf /\
               expectation p (Z (u a (SUC n))) <> NegInf’
         >- (MATCH_MP_TAC expectation_finite >> art []) >> DISCH_TAC \\
        ‘?r. expectation p (Z (u a (SUC n))) = Normal r’
           by METIS_TAC [extreal_cases] >> POP_ORW \\
         Suff ‘&u a (SUC n) <> (0 :real)’ >- rw [extreal_div_eq, extreal_of_num_def] \\
         rw [extreal_of_num_def] \\
         Suff ‘0 < u a (SUC n)’ >- ARITH_TAC \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     SIMP_TAC std_ss [o_DEF] \\
  (* applying LIM_SUBSEQUENCE_WEAK *)
     Q.ABBREV_TAC ‘s = \n. real (expectation p (Z (SUC n)) / &SUC n)’ \\
     Q.ABBREV_TAC ‘r = \n. PRE (u a (SUC n))’ \\
     Know ‘(\n. real (expectation p (Z (u a (SUC n))) / &u a (SUC n))) = s o r’
     >- (rw [FUN_EQ_THM, Abbr ‘s’, Abbr ‘r’, o_DEF] \\
         Suff ‘SUC (PRE (u a (SUC n))) = u a (SUC n)’ >- rw [] \\
         rw [GSYM SUC_PRE]) >> Rewr' \\
     MATCH_MP_TAC LIM_SUBSEQUENCE_WEAK \\
     CONJ_TAC (* monotone *)
     >- (qx_genl_tac [‘i’, ‘j’] >> rw [Abbr ‘r’] \\
        ‘0 < u a (SUC i)’ by PROVE_TAC [] \\
         rw [INV_PRE_LESS_EQ]) \\
     CONJ_TAC (* infinity *)
     >- (Q.X_GEN_TAC ‘N’ >> rw [Abbr ‘r’] \\
         Q.PAT_X_ASSUM ‘!a x. 1 < a ==> ?n. x < &u a (SUC n)’
           (fn th => MP_TAC (Q.SPEC ‘&N’ (MATCH_MP th (ASSUME “1 < (a :real)”)))) \\
         RW_TAC real_ss [] \\
         Q.EXISTS_TAC ‘n’ \\
         POP_ASSUM MP_TAC >> ARITH_TAC) \\
     SIMP_TAC std_ss [Abbr ‘s’, Abbr ‘r’, Abbr ‘Z’, Abbr ‘Y’, Abbr ‘m’] \\
     MATCH_MP_TAC truncated_vars_expectation' >> art [])
 >> POP_ASSUM K_TAC >> DISCH_TAC
 (* stage work, applying equivalent_thm4 *)
 >> RW_TAC std_ss [pow_seq_def]
 >> FULL_SIMP_TAC std_ss [Abbr ‘Z’]
 >> HO_MATCH_MP_TAC equivalent_thm4
 >> Q.EXISTS_TAC ‘Y’ >> rw [] (* 6 subgoals *)
 >| [ (* goal 1 (of 6): equivalent *)
      ASM_REWRITE_TAC [Once equivalent_comm],
      (* goal 2 (of 6): real_random_variable *)
      MATCH_MP_TAC real_random_variable_const >> art [] \\
      PROVE_TAC [expectation_finite],
      (* goal 3 (of 6): ‘0 < &u a (SUC n)’ *)
      rw [extreal_of_num_def, extreal_lt_eq],
      (* goal 4 (of 6): mono_increasing *)
      simp [ext_mono_increasing_def] \\
      qx_genl_tac [‘i’, ‘j’] >> rw [extreal_of_num_def, extreal_le_eq],
      (* goal 5 (of 6): sup = PosInf *)
      rw [sup_eq', le_infty] \\
      CCONTR_TAC >> FULL_SIMP_TAC std_ss [lt_infty] \\
      Cases_on ‘0 <= y’ >| (* 2 subgoals *)
      [ (* goal 5.1 (of 2): not easy *)
       ‘y <> PosInf’ by PROVE_TAC [lt_infty] \\
       ‘y <> NegInf’ by PROVE_TAC [pos_not_neginf] \\
       ‘?r. y = Normal r /\ 0 <= r’
          by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_le_eq] \\
        FULL_SIMP_TAC std_ss [] \\
        Q.PAT_X_ASSUM ‘!a x. 1 < a ==> ?n. x < &u a (SUC n)’
          (fn th => STRIP_ASSUME_TAC
                     (Q.SPEC ‘r’ (MATCH_MP th (ASSUME “1 < (a :real)”)))) \\
        Q.PAT_X_ASSUM ‘!z. P ==> z <= Normal r’
          (MP_TAC o (Q.SPEC ‘&(u :real -> num -> num) a (SUC n)’)) \\
        rw [extreal_of_num_def, extreal_le_eq] >- (Q.EXISTS_TAC ‘n’ >> art []) \\
        rw [GSYM real_lt],
        (* goal 5.2 (of 2): easy *)
        FULL_SIMP_TAC std_ss [GSYM extreal_lt_def] \\
        Q.PAT_X_ASSUM ‘!z. P ==> z <= y’
          (MP_TAC o (Q.SPEC ‘&(u :real -> num -> num) a (SUC 0)’)) \\
        RW_TAC bool_ss [] >- (Q.EXISTS_TAC ‘0’ >> art []) \\
        CCONTR_TAC >> FULL_SIMP_TAC std_ss [] \\
        Know ‘&u a 1 < (0 :extreal)’ >- PROVE_TAC [let_trans] \\
        rw [extreal_of_num_def, extreal_lt_eq] ],
      (* goal 6 (of 6): u is unbounded *)
      rename1 ‘?n. N <= u a (SUC n)’ \\
      Q.PAT_X_ASSUM ‘!a x. 1 < a ==> ?n. x < &u a (SUC n)’
        (fn th => MP_TAC (Q.SPEC ‘&N’ (MATCH_MP th (ASSUME “1 < (a :real)”)))) \\
      rw [extreal_of_num_def, extreal_lt_eq] \\
      Q.EXISTS_TAC ‘n’ >> rw [] ]
QED

(* This lemma is part of the fix of N. Etemadi's original proof [12] by Chun Tian.

   NOTE: having ‘!n x. x IN p_space p ==> 0 <= X n x’ and ‘expectation p (X n) = 0’
   doesn't mean that ‘!x. x IN p_space p ==> X n x = 0’. Instead, ‘X n x = 0’ only
   holds except for a null set, for each n. Fortunately, a countable union of null
   sets is still a null set, thus we can construct a (bigger) null set for the entire
   random sequence and finish the proof.               -- Chun Tian, July 25, 2021.
 *)
Theorem SLLN_IID_zero[local] :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) /\
          pairwise_indep_vars p X (\n. Borel) UNIV /\
          identical_distribution p X Borel UNIV /\
          integrable p (X 0) /\ expectation p (X 0) = 0 /\
         (!n x. x IN p_space p ==> 0 <= X n x)
      ==> LLN p X almost_everywhere
Proof
    rw [LLN_alt_converge_AE_IID]
 >> ‘real_random_variable (\x. 0) p’ by PROVE_TAC [real_random_variable_zero]
 >> qabbrev_tac ‘W = \n x. SIGMA (\i. X i x) (count1 n) / &SUC n’
 >> Know ‘!n. real_random_variable (W n) p’
 >- (rw [Abbr ‘W’] \\
     MATCH_MP_TAC real_random_variable_LLN' >> art [])
 >> DISCH_TAC
 >> rw [converge_AE_def, AE_DEF]
 >> simp [Abbr ‘W’]
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
 >> Know ‘!n. expectation p (X n) = 0’
 >- (Q.PAT_X_ASSUM ‘expectation p (X 0) = 0’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     MATCH_MP_TAC identical_distribution_expectation >> rw [] \\
     FULL_SIMP_TAC std_ss [real_random_variable_def])
 >> Q.PAT_X_ASSUM ‘expectation p (X 0) = 0’ K_TAC
 >> DISCH_TAC
 >> fs [prob_space_def, real_random_variable, p_space_def, events_def]
 (* applying integral_eq_0 *)
 >> Know ‘!n. AE x::p. X n x = 0’
 >- (Q.X_GEN_TAC ‘n’ \\
     Know ‘(AE x::p. X n x = 0) <=> measure p {x | x IN m_space p /\ X n x <> 0} = 0’
     >- (MATCH_MP_TAC (BETA_RULE
                       (Q.SPECL [‘{x | x IN m_space p /\ (X :num -> 'a -> extreal) n x <> 0}’,
                                 ‘p’, ‘\x. (X :num -> 'a -> extreal) n x = 0’]
                                AE_iff_measurable)) \\
        ‘{x | x IN m_space p /\ X n x <> 0} = {x | X n x <> 0} INTER m_space p’
           by SET_TAC [] >> POP_ORW \\
         METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> Rewr' \\
     Suff ‘measure p {x | x IN m_space p /\ X n x <> 0} = 0 <=> expectation p (X n) = 0’
     >- rw [] \\
     REWRITE_TAC [Once EQ_SYM_EQ, expectation_def] \\
     MATCH_MP_TAC integral_eq_0 \\
     rw [AE_DEF] >> Q.EXISTS_TAC ‘{}’ \\
     MATCH_MP_TAC NULL_SET_EMPTY >> art [])
 >> DISCH_TAC
 >> Know ‘!n. ?N. N IN null_set p /\ !x. x IN m_space p DIFF N ==> X n x = 0’
 >- (POP_ASSUM MP_TAC \\
     rw [AE_DEF, IN_NULL_SET])
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss [SKOLEM_THM] (* this asserts ‘f’ *)
 >> Q.ABBREV_TAC ‘N = BIGUNION (IMAGE f UNIV)’
 >> Know ‘N IN null_set p’
 >- (Q.UNABBREV_TAC ‘N’ \\
     MATCH_MP_TAC NULL_SET_BIGUNION >> rw [])
 >> DISCH_TAC
 >> Q.EXISTS_TAC ‘N’ >> rw [GSYM IN_NULL_SET]
 >> Know ‘!n. X n x = 0’
 >- (Suff ‘!n. x IN m_space p DIFF f n’ >- METIS_TAC [] \\
     rw [] (* x NOTIN f n *) \\
     POP_ASSUM MP_TAC (* ‘x NOTIN N’ *) \\
     rw [Abbr ‘N’] >> METIS_TAC [])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘S = \n x. SIGMA (\i. X i x) (count n)’ >> simp []
 >> ‘!n. S n x = 0’ by (rw [Abbr ‘S’, EXTREAL_SUM_IMAGE_ZERO])
 >> ‘!n. &SUC n <> (0 :real)’ by rw []
 >> ‘!n. &SUC n <> (0 :extreal)’ by rw [extreal_of_num_def]
 >> rw [GSYM extreal_of_num_def, zero_div, abs_0, LIM_CONST]
QED

(* SLLN_IID for nonnegative r.v.'s, i.e. ‘!n x. x IN p_space p ==> 0 <= X n x’

   The proof follows Theorem 5.4.4 [3, p.62], Theorem 22.1 [6, p.282] and Theorem 1 of [12].
 *)
Theorem SLLN_IID_wlog[local] :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) /\
          pairwise_indep_vars p X (\n. Borel) UNIV /\
          identical_distribution p X Borel UNIV /\
          integrable p (X 0) /\
          (!n x. x IN p_space p ==> 0 <= X n x)
      ==> LLN p X almost_everywhere
Proof
    rpt STRIP_TAC
 (* applying SLLN_IID_zero to eliminate this annoying special case *)
 >> Cases_on ‘expectation p (X 0) = 0’
 >- (MATCH_MP_TAC SLLN_IID_zero >> art [])
 >> RW_TAC std_ss [LLN_alt_converge_AE_IID]
 >> Know ‘!a. 1 < a ==> ((\n x. SIGMA (\i. X i x) (count (pow_seq a (SUC n))) /
                                &pow_seq a (SUC n)) --> (\x. expectation p (X 0)))
                          (almost_everywhere p)’
 >- (MATCH_MP_TAC SLLN_IID_lemma >> art [])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘S = \n x. SIGMA (\i. X i x) (count n)’
 >> Q.ABBREV_TAC ‘u = \(a :real) n. flr (a pow n)’
 >> FULL_SIMP_TAC std_ss [pow_seq_def]
 (* further properties of ‘S’, ‘0 <= X n x’ is FINALLY used here *)
 >> Know ‘!n x. x IN p_space p ==> 0 <= S n x’
 >- (rw [Abbr ‘S’] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> rw [])
 >> DISCH_TAC
 >> Know ‘!i j x. x IN p_space p /\ i <= j ==> S i x <= S j x’
 >- (rw [Abbr ‘S’] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET >> rw [] \\
     MATCH_MP_TAC COUNT_MONO >> art [])
 >> DISCH_TAC
 (* NOTE: this subgoal is part of the proof of Lemma 1.7 [7, p.95], which may be used
          to simplify also the final part of (the proof of) SLLN_uncorrelated. *)
 >> Know ‘!a x k. 1 < a /\ x IN p_space p ==>
                  ?n. u a n <= SUC k /\ SUC k <= u a (SUC n) /\
                     (&u a n / &u a (SUC n)) * (S (u a n) x / &u a n) <= S (SUC k) x / &SUC k /\
                      S (SUC k) x / &SUC k <=
                     (&u a (SUC n) / &u a n) * (S (u a (SUC n)) x / &u a (SUC n))’
 >- (rpt STRIP_TAC \\
     Know ‘?n. pow_seq a n <= SUC k /\ SUC k <= pow_seq a (SUC n)’
     >- (MATCH_MP_TAC pow_seq_complete >> rw []) \\
     rw [pow_seq_def] (* this asserts ‘n’ *) \\
     Q.EXISTS_TAC ‘n’ >> art [] \\
     Know ‘!i. 0 < pow_seq a i’
     >- (Q.X_GEN_TAC ‘n’ >> MATCH_MP_TAC pow_seq_pos_lt >> art []) \\
     simp [pow_seq_def] >> DISCH_TAC \\
    ‘!n. (0 :real) < &u a n’ by rw [] \\
    ‘!n. &u a n <> (0 :real)’ by PROVE_TAC [REAL_LT_IMP_NE] \\
    ‘(0 :real) < &SUC k’ by rw [] \\
    ‘&SUC k <> (0 :real)’ by PROVE_TAC [REAL_LT_IMP_NE] \\
     ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_div_def] \\
     RW_TAC std_ss [mul_assoc] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
      ‘Normal (&u a n) * inv (Normal (&u a (SUC n))) * S (u a n) x * inv (Normal (&u a n)) =
       inv (Normal (&u a n)) * Normal (&u a n) * inv (Normal (&u a (SUC n))) * S (u a n) x’
         by METIS_TAC [mul_comm, mul_assoc] >> POP_ORW \\
       Know ‘inv (Normal (&u a n)) * Normal (&u a n) = 1’
       >- (rw [extreal_of_num_def, extreal_mul_def, extreal_inv_eq, REAL_MUL_LINV]) >> Rewr' \\
       REWRITE_TAC [mul_lone] \\
       ASM_SIMP_TAC std_ss [GSYM extreal_div_def] \\
       Know ‘inv (Normal (&u a (SUC n))) * S (u a n) x <= S (SUC k) x / Normal (&SUC k) <=>
             inv (Normal (&u a (SUC n))) * S (u a n) x * Normal (&SUC k) <= S (SUC k) x’
       >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
           MATCH_MP_TAC le_rdiv >> art []) >> Rewr' \\
       REWRITE_TAC [GSYM mul_assoc] \\
       ONCE_REWRITE_TAC [mul_comm] \\
       ASM_SIMP_TAC std_ss [GSYM extreal_div_def] \\
       Know ‘S (u a n) x * Normal (&SUC k) / Normal (&u a (SUC n)) <= S (SUC k) x <=>
             S (u a n) x * Normal (&SUC k) <= S (SUC k) x * Normal (&u a (SUC n))’
       >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
           MATCH_MP_TAC le_ldiv >> art []) >> Rewr' \\
       MATCH_MP_TAC le_mul2 >> rw [extreal_of_num_def, extreal_le_eq],
       (* goal 2 (of 2) *)
      ‘Normal (&u a (SUC n)) * inv (Normal (&u a n)) * S (u a (SUC n)) x * inv (Normal (&u a (SUC n))) =
       inv (Normal (&u a (SUC n))) * Normal (&u a (SUC n)) * inv (Normal (&u a n)) * S (u a (SUC n)) x’
         by METIS_TAC [mul_comm, mul_assoc] >> POP_ORW \\
       Know ‘inv (Normal (&u a (SUC n))) * Normal (&u a (SUC n)) = 1’
       >- (rw [extreal_of_num_def, extreal_mul_def, extreal_inv_eq, REAL_MUL_LINV]) >> Rewr' \\
       REWRITE_TAC [mul_lone] \\
       ASM_SIMP_TAC std_ss [GSYM extreal_div_def] \\
       Know ‘S (SUC k) x / Normal (&SUC k) <= inv (Normal (&u a n)) * S (u a (SUC n)) x <=>
             S (SUC k) x <= inv (Normal (&u a n)) * S (u a (SUC n)) x * Normal (&SUC k)’
       >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
           MATCH_MP_TAC le_ldiv >> art []) >> Rewr' \\
       REWRITE_TAC [GSYM mul_assoc] \\
       ONCE_REWRITE_TAC [mul_comm] \\
       ASM_SIMP_TAC std_ss [GSYM extreal_div_def] \\
       Know ‘S (SUC k) x <= S (u a (SUC n)) x * Normal (&SUC k) / Normal (&u a n) <=>
             S (SUC k) x * Normal (&u a n) <= S (u a (SUC n)) x * Normal (&SUC k)’
       >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
           MATCH_MP_TAC le_rdiv >> art []) >> Rewr' \\
       MATCH_MP_TAC le_mul2 >> rw [extreal_of_num_def, extreal_le_eq] ])
 >> DISCH_TAC
 (* now touching the goal *)
 >> Know ‘!n. integrable p (X n)’
 >- (MATCH_MP_TAC identical_distribution_integrable \\
     fs [real_random_variable_def])
 >> DISCH_TAC
 >> Know ‘real_random_variable (\x. expectation p (X 0)) p’
 >- (MATCH_MP_TAC real_random_variable_const >> art [] \\
     MATCH_MP_TAC integrable_imp_finite_expectation >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘W = \n x. S (SUC n) x / &SUC n’
 >> Know ‘!n. real_random_variable (W n) p’
 >- (rw [Abbr ‘W’, Abbr ‘S’] \\
     MATCH_MP_TAC real_random_variable_LLN' >> art [])
 >> DISCH_TAC
 >> rw [converge_AE_def, AE_DEF]
 >> simp [Abbr ‘W’]
 >> Q.ABBREV_TAC ‘m = expectation p (X 0)’
 >> Know `m <> PosInf /\ m <> NegInf`
 >- (ASM_SIMP_TAC std_ss [expectation_def, Abbr ‘m’] \\
     MATCH_MP_TAC integrable_finite_integral \\
     FULL_SIMP_TAC std_ss [prob_space_def])
 >> STRIP_TAC
 (* applying EXT_SKOLEM_THM' *)
 >> Q.ABBREV_TAC ‘P = \a. 1 < (a :real)’
 >> Q.ABBREV_TAC ‘Q = \a (N :'a -> bool). null_set p N /\
                         !x. x IN m_space p /\ x NOTIN N ==>
                            ((\n. real (S (u a (SUC n)) x / &u a (SUC n))) --> real m) sequentially’
 >> Know ‘!a. P a ==> ?N. Q a N’
 >- (rw [Abbr ‘P’, Abbr ‘Q’] \\
     Q.PAT_X_ASSUM ‘!a. 1 < a ==> (_ --> (\x. m)) (almost_everywhere p)’
        (fn th => MP_TAC (MATCH_MP th (ASSUME “1 < (a :real)”))) \\
     qabbrev_tac ‘Z = \n x. S (u a (SUC n)) x / &u a (SUC n)’ \\
     Know ‘!n. real_random_variable (Z n) p’
     >- (rw [Abbr ‘Z’, Abbr ‘S’] \\
         MATCH_MP_TAC real_random_variable_LLN_general' \\
         rw [Abbr ‘u’] (* goal: 0 < flr (a pow n) *) \\
         rw [NUM_FLOOR_POS] \\
        ‘(1 :real) = 1 pow n’ by rw [] >> POP_ORW \\
         MATCH_MP_TAC POW_LE >> rw [REAL_LT_IMP_LE]) >> DISCH_TAC \\
     rw [converge_AE_def, AE_DEF])
 >> rw [EXT_SKOLEM_THM', Abbr ‘P’, Abbr ‘Q’] (* this assert ‘f’ *)
 >> Q.PAT_X_ASSUM ‘!a. 1 < a ==> (_ --> (\x. m)) (almost_everywhere p)’ K_TAC
 (* NOTE: now this formal proof is beyond the (incorrect) textbook proofs *)
 >> Q.ABBREV_TAC ‘N = BIGUNION (IMAGE (\n. f (1 + inv (&SUC n))) UNIV)’
 >> ‘!n. (1 :real) < 1 + inv (&SUC n)’ by rw [REAL_LT_ADDR]
 >> Q.EXISTS_TAC ‘N’
 >> CONJ_TAC (* null_set p N *)
 >- (Q.UNABBREV_TAC ‘N’ \\
     MATCH_MP_TAC (REWRITE_RULE [IN_NULL_SET] NULL_SET_BIGUNION) \\
     rw [] >> fs [prob_space_def])
 >> rpt STRIP_TAC (* this asserts ‘x’ *)
 >> Know ‘((\n. real (S (SUC n) x / &SUC n)) --> real m) sequentially <=>
           limsup (\n. S (SUC n) x / &SUC n) = m /\
           liminf (\n. S (SUC n) x / &SUC n) = m’
 >- (‘?M. m = Normal M’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     REWRITE_TAC [real_normal] \\
     HO_MATCH_MP_TAC (REWRITE_RULE [o_DEF] ext_limsup_thm) \\
     simp [Abbr ‘S’] \\
     Q.X_GEN_TAC ‘n’ \\
     Know ‘SIGMA (\i. X i x) (count1 n) <> PosInf’
     >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> simp [] \\
         Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
         Q.PAT_X_ASSUM `!n. real_random_variable (X n) p`
           (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
            (REWRITE_RULE [real_random_variable_def, p_space_def])) \\
         METIS_TAC []) >> DISCH_TAC \\
     Know ‘SIGMA (\i. X i x) (count1 n) <> NegInf’
     >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF >> simp [] \\
         Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
         Q.PAT_X_ASSUM `!n. real_random_variable (X n) p`
           (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
            (REWRITE_RULE [real_random_variable_def, p_space_def])) \\
         METIS_TAC []) >> DISCH_TAC \\
    ‘?r. SIGMA (\i. X i x) (count1 n) = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_of_num_def, extreal_div_eq]) >> Rewr'
 >> ‘0 <= m’ by (Q.UNABBREV_TAC ‘m’ >> MATCH_MP_TAC expectation_pos >> rw [])
 (* stage work, the rest is a pure (extreal) limit problem *)
 >> Q.ABBREV_TAC ‘g = \n. S (SUC n) x / &SUC n’
 >> Suff ‘limsup g <= m /\ m <= liminf g’
 >- (STRIP_TAC \\
    ‘liminf g <= limsup g’ by PROVE_TAC [ext_liminf_le_limsup] \\
    ‘m <= limsup g’ by PROVE_TAC [le_trans] \\
    ‘liminf g <= m’ by PROVE_TAC [le_trans] \\
     rw [GSYM le_antisym])
 (* here each ‘1 + inv (&SUC n)’ is a possible ‘a’ such that ‘null_set p (f a)’ holds *)
 >> Suff ‘!n. limsup g <= (1 + inv (&SUC n)) * m /\
              inv (1 + inv (&SUC n)) * m <= liminf g’
 >- (rpt STRIP_TAC >| (* 2 subgoals with the same ending tactics *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC le_mul_epsilon >> rpt STRIP_TAC \\
       Cases_on ‘z = 0’ >- rw [] \\
       ONCE_REWRITE_TAC [mul_comm] \\
      ‘z <> NegInf’ by PROVE_TAC [pos_not_neginf] \\
       Know ‘z <> PosInf’
       >- (REWRITE_TAC [lt_infty] \\
           MATCH_MP_TAC lt_trans >> Q.EXISTS_TAC ‘1’ >> rw []) >> DISCH_TAC \\
      ‘0 < z’ by PROVE_TAC [lt_le] \\
       Know ‘limsup g * z <= m <=> limsup g <= m / z’
       >- (‘?r. 0 < r /\ z = Normal r’
             by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] >> POP_ORW \\
           MATCH_MP_TAC le_rdiv >> art []) >> Rewr' \\
       Know ‘m / z = inv z * m’
       >- (ONCE_REWRITE_TAC [mul_comm] \\
           ‘?r. r <> 0 /\ z = Normal r’
             by METIS_TAC [extreal_cases, extreal_of_num_def] >> POP_ORW \\
           rw [extreal_div_def]) >> Rewr' \\
       Know ‘inv z - 1 <> 0’
       >- (Suff ‘0 < inv z - 1’ >- rw [lt_imp_ne] \\
           MATCH_MP_TAC sub_zero_lt \\
          ‘1 = inv (1 :extreal)’ by rw [inv_one] >> POP_ORW \\
           Suff ‘inv 1 < inv z <=> z < 1’ >- rw [] \\
           MATCH_MP_TAC inv_lt_antimono >> rw []) >> DISCH_TAC \\
       Know ‘?n. inv (inv z - 1) <= &n’
       >- (MATCH_MP_TAC SIMP_EXTREAL_ARCH \\
           METIS_TAC [inv_not_infty]) >> STRIP_TAC (* this asserts ‘n’ *) \\
       MATCH_MP_TAC le_trans \\
       Q.EXISTS_TAC ‘(1 + inv (&SUC n)) * m’ >> art [] \\
       MATCH_MP_TAC le_rmul_imp >> art [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC le_mul_epsilon >> rpt STRIP_TAC \\
       Cases_on ‘z = 0’ >- (rw [] >> MATCH_MP_TAC ext_liminf_pos >> rw [Abbr ‘g’] \\
                           ‘&SUC n = Normal (&SUC n)’ by rw [extreal_of_num_def] >> POP_ORW \\
                            MATCH_MP_TAC le_div >> rw [Abbr ‘S’] \\
                            MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> simp [] \\
                            Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
                            FIRST_X_ASSUM MATCH_MP_TAC >> rw [p_space_def]) \\
      ‘z <> NegInf’ by PROVE_TAC [pos_not_neginf] \\
       Know ‘z <> PosInf’
       >- (REWRITE_TAC [lt_infty] \\
           MATCH_MP_TAC lt_trans >> Q.EXISTS_TAC ‘1’ >> rw []) >> DISCH_TAC \\
      ‘0 < z’ by PROVE_TAC [lt_le] \\
       Know ‘inv z - 1 <> 0’
       >- (Suff ‘0 < inv z - 1’ >- rw [lt_imp_ne] \\
           MATCH_MP_TAC sub_zero_lt \\
          ‘1 = inv (1 :extreal)’ by rw [inv_one] >> POP_ORW \\
           Suff ‘inv 1 < inv z <=> z < 1’ >- rw [] \\
           MATCH_MP_TAC inv_lt_antimono >> rw []) >> DISCH_TAC \\
       Know ‘?n. inv (inv z - 1) <= &n’
       >- (MATCH_MP_TAC SIMP_EXTREAL_ARCH \\
           METIS_TAC [inv_not_infty]) >> STRIP_TAC (* this asserts ‘n’ *) \\
       MATCH_MP_TAC le_trans \\
       Q.EXISTS_TAC ‘inv (1 + inv (&SUC n)) * m’ >> art [] \\
       MATCH_MP_TAC le_rmul_imp >> art [] \\
      ‘z = inv (inv z)’ by PROVE_TAC [inv_inv] >> POP_ORW \\
       Know ‘inv (inv z) <= inv (1 + inv (&SUC n)) <=> 1 + inv (&SUC n) <= inv z’
       >- (MATCH_MP_TAC inv_le_antimono \\
           CONJ_TAC >- (MATCH_MP_TAC inv_pos' >> art []) \\
           MATCH_MP_TAC lt_add >> rw [] \\
           MATCH_MP_TAC inv_pos' >> rw [extreal_of_num_def, extreal_lt_eq]) >> Rewr' ] \\
    (* below are shared tactics *)
      (Know ‘1 + inv (&SUC n) = inv (&SUC n) + 1’
       >- (rw [extreal_of_num_def, add_comm_normal]) >> Rewr' \\
       Know ‘inv (&SUC n) + 1 <= inv z <=> inv (&SUC n) <= inv z - 1’
       >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
           MATCH_MP_TAC le_sub_eq >> rw []) >> Rewr' \\
       Know ‘inv z - 1 = inv (inv (inv z - 1))’
       >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
           MATCH_MP_TAC inv_inv >> art [] \\
           METIS_TAC [sub_not_infty, inv_not_infty,
                      extreal_of_num_def, extreal_not_infty]) >> Rewr' \\
       Know ‘inv (&SUC n) <= inv (inv (inv z - 1)) <=> inv (inv z - 1) <= &SUC n’
       >- (MATCH_MP_TAC inv_le_antimono \\
           CONJ_TAC >- rw [extreal_of_num_def, extreal_lt_eq] \\
           MATCH_MP_TAC inv_pos' \\
           CONJ_TAC >- (MATCH_MP_TAC sub_zero_lt \\
                       ‘1 = inv (1 :extreal)’ by rw [inv_one] >> POP_ORW \\
                        Suff ‘inv 1 < inv z <=> z < 1’ >- rw [] \\
                        MATCH_MP_TAC inv_lt_antimono >> rw []) \\
          ‘?r. r <> 0 /\ z = Normal r’
             by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_11] >> POP_ORW \\
           rw [extreal_of_num_def, extreal_inv_eq, extreal_sub_def]) >> Rewr' \\
       MATCH_MP_TAC lt_imp_le \\
       MATCH_MP_TAC let_trans \\
       Q.EXISTS_TAC ‘&n’ >> rw [extreal_of_num_def, extreal_lt_eq]) )
 (* final stage, now ‘a = 1 + inv (&SUC i)’ is a fixed value *)
 >> Q.X_GEN_TAC ‘i’
 >> Know ‘1 + inv (&SUC i) = Normal (1 + inv (&SUC i))’
 >- (‘&SUC i <> (0 :real)’ by rw [] \\
     rw [extreal_of_num_def, extreal_inv_eq, extreal_add_def]) >> Rewr'
 >> Q.PAT_X_ASSUM ‘!n. 1 < 1 + inv (&SUC n)’ (MP_TAC o (Q.SPEC ‘i’))
 >> Q.ABBREV_TAC ‘a = (1 :real) + inv (&SUC i)’
 >> DISCH_TAC (* 1 < a *)
 >> ASSUME_TAC (REWRITE_RULE [pow_seq_def] (MATCH_MP pow_seq_limit  (ASSUME “1 < (a :real)”)))
 >> ASSUME_TAC (REWRITE_RULE [pow_seq_def] (MATCH_MP pow_seq_limit' (ASSUME “1 < (a :real)”)))
 >> ASSUME_TAC (REWRITE_RULE [pow_seq_def] (MATCH_MP pow_seq_pos_lt (ASSUME “1 < (a :real)”)))
 >> ASSUME_TAC (REWRITE_RULE [pow_seq_def] (Q.SPEC ‘a’ pow_seq_monotone))
 >> REV_FULL_SIMP_TAC std_ss [Abbr ‘g’]
 >> Q.PAT_X_ASSUM ‘!a x k. 1 < a /\ x IN p_space p ==> P’
      (ASSUME_TAC o (REWRITE_RULE [ASSUME “1 < (a :real)”, p_space_def,
                                   ASSUME “x IN m_space p”]) o (Q.SPECL [‘a’, ‘x’]))
 >> Q.PAT_X_ASSUM ‘!a. 1 < a ==> null_set p (f a) /\ P’
     (fn th => (STRIP_ASSUME_TAC (MATCH_MP th (ASSUME “1 < (a :real)”))))
 >> POP_ASSUM (MP_TAC o (REWRITE_RULE [ASSUME “x IN m_space p”]) o
               (Q.SPEC ‘x’)) (* !x. x IN m_space p /\ x NOTIN f a ==> P *)
 >> Know ‘x NOTIN f a’
 >- (Q.PAT_X_ASSUM ‘x NOTIN N’ MP_TAC \\
     rw [Abbr ‘N’, Abbr ‘a’] >> METIS_TAC []) >> Rewr
 >> Q.ABBREV_TAC ‘h = \n. S n x / &n’
 >> FULL_SIMP_TAC std_ss []
 >> Know ‘!n. 0 < n ==> 0 <= h n’
 >- (rw [Abbr ‘h’] \\
    ‘&n = Normal (&n)’ by rw [extreal_of_num_def] >> POP_ORW \\
     MATCH_MP_TAC le_div \\
     reverse CONJ_TAC >- (rw [extreal_of_num_def, extreal_lt_eq]) \\
     FIRST_X_ASSUM MATCH_MP_TAC >> rw [p_space_def])
 >> DISCH_TAC
 >> Know ‘!n. 0 < n ==> h n <> PosInf /\ h n <> NegInf’
 >- (Q.X_GEN_TAC ‘n’ >> DISCH_TAC \\
     simp [Abbr ‘h’, Abbr ‘S’] \\
    ‘n <> 0’ by DECIDE_TAC \\
    ‘&n <> (0 :real)’ by rw [] \\
     Suff ‘SIGMA (\i. X i x) (count n) <> PosInf /\
           SIGMA (\i. X i x) (count n) <> NegInf’
     >- (STRIP_TAC \\
        ‘?z. SIGMA (\i. X i x) (count n) = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_of_num_def, extreal_div_eq]) \\
     Q.PAT_X_ASSUM ‘!n. real_random_variable (X n) p’
       (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
        (REWRITE_RULE [real_random_variable_def, p_space_def])) \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> simp [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF >> simp [] ])
 >> DISCH_TAC
 (* clean up *)
 >> Q.PAT_X_ASSUM ‘prob_space p’                                        K_TAC
 >> Q.PAT_X_ASSUM ‘!n. real_random_variable (X n) p’                    K_TAC
 >> Q.PAT_X_ASSUM ‘!n x. x IN p_space p ==> 0 <= X n x’                 K_TAC
 >> Q.PAT_X_ASSUM ‘pairwise_indep_vars p X (\n. Borel) UNIV’            K_TAC
 >> Q.PAT_X_ASSUM ‘identical_distribution p X Borel UNIV’               K_TAC
 >> Q.PAT_X_ASSUM ‘null_set p (f a)’                                    K_TAC
 >> Q.PAT_X_ASSUM ‘x IN m_space p’                                      K_TAC
 >> Q.PAT_X_ASSUM ‘x NOTIN N’                                           K_TAC
 >> Q.PAT_X_ASSUM ‘!n x. x IN p_space p ==> 0 <= S n x’                 K_TAC
 >> Q.PAT_X_ASSUM ‘!i j x. x IN p_space p /\ i <= j ==> S i x <= S j x’ K_TAC
 >> FULL_SIMP_TAC std_ss [Abbr ‘N’, Abbr ‘S’]
 >> ‘?M. 0 <= M /\ M <> 0 /\ m = Normal M’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_le_eq]
 >> Q.PAT_X_ASSUM ‘m <> PosInf’                                         K_TAC
 >> Q.PAT_X_ASSUM ‘m <> NegInf’                                         K_TAC
 >> Q.PAT_X_ASSUM ‘m <> 0’                                              K_TAC
 >> Q.PAT_X_ASSUM ‘0 <= m’                                              K_TAC
 >> POP_ORW (* m = Normal M *)
 >> Q.UNABBREV_TAC ‘m’
 (* applying SKOLEM_THM *)
 >> FULL_SIMP_TAC std_ss [SKOLEM_THM, real_normal] (* this assert ‘f’ *)
 (* f is monotone *)
 >> Know ‘!m n. m <= n ==> f m <= f n’
 >- (rpt STRIP_TAC \\
     Cases_on ‘m = n’ >- rw [] \\
    ‘m < n’ by rw [] \\
     CCONTR_TAC >> FULL_SIMP_TAC std_ss [NOT_LESS_EQUAL] \\
    ‘SUC (f n) <= f m’ by rw [] \\
    ‘u a (f n) <= SUC n /\ SUC n <= u a (SUC (f n))’ by METIS_TAC [] \\
    ‘u a (f m) <= SUC m /\ SUC m <= u a (SUC (f m))’ by METIS_TAC [] \\
    ‘SUC m < SUC n’ by rw [] \\
    ‘u a (f m) < SUC n’ by rw [] \\
    ‘u a (f m) < u a (SUC (f n))’ by rw [] \\
    ‘u a (SUC (f n)) <= u a (f m)’ by rw [] \\
     METIS_TAC [LESS_EQ_ANTISYM])
 (* f is unbounded *)
 >> Know ‘!n. ?N. n <= f N’
 >- (Q.X_GEN_TAC ‘n’ \\
     CCONTR_TAC >> FULL_SIMP_TAC std_ss [NOT_LESS_EQUAL] \\
    ‘!N. SUC (f N) <= n’ by rw [GSYM LESS_EQ] \\
    ‘!N. u a (SUC (f N)) <= u a n’ by rw [] \\
    ‘!N. SUC N <= u a (SUC (f N))’ by rw [] \\
    ‘!N. SUC N <= u a n’ by METIS_TAC [LESS_EQ_TRANS] \\
    ‘!N. SUC N < u a n’ by rw [LESS_EQ] \\
    ‘SUC (u a n) < u a n’ by rw [] \\
    ‘u a n < SUC (u a n)’ by rw [] \\
     METIS_TAC [LESS_ANTISYM])
 (* final stage, a pure goal about real numbers *)
 >> rpt STRIP_TAC
 >| [ (*** goal 1 (of 2), first inf_le' then sup_le' ***)
      rw [ext_limsup_def, inf_le'] \\ (* goal: ‘y <= Normal a * Normal M’ *)

   (* NOTE: using "le_mul_epsilon" is much easier than using "le_epsilon" here. However,
            le_mul_epsilon doesn't work if ‘a’ or ‘M’ is zero!

      Fortunately, the case ‘M = 0’ (expectation p (X 0) = 0) can be easily eliminated
      by SLLN_IID_zero, when ‘0 <= X n x’ also holds. -- Chun Tian, Jul 25, 2021
    *)
      MATCH_MP_TAC le_mul_epsilon >> rpt STRIP_TAC \\
      Cases_on ‘z = 0’ >- (rw [] >> MATCH_MP_TAC le_mul \\
                          ‘0 < a’ by PROVE_TAC [REAL_LT_01, REAL_LT_TRANS] \\
                          ‘0 <= a’ by PROVE_TAC [REAL_LT_IMP_LE] \\
                           rw [extreal_of_num_def, extreal_le_eq]) \\
     ‘z <> NegInf’ by PROVE_TAC [pos_not_neginf] \\
      Know ‘z <> PosInf’
      >- (REWRITE_TAC [lt_infty] \\
          MATCH_MP_TAC lt_trans >> Q.EXISTS_TAC ‘1’ >> rw []) >> DISCH_TAC \\
     ‘0 < z’ by PROVE_TAC [lt_le] \\
     ‘?r. r <> 0 /\ 0 < r /\ r < 1 /\ z = Normal r’
        by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] >> POP_ORW \\
      Q.PAT_X_ASSUM ‘0 <= z’      K_TAC \\
      Q.PAT_X_ASSUM ‘z < 1’       K_TAC \\
      Q.PAT_X_ASSUM ‘z <> 0’      K_TAC \\
      Q.PAT_X_ASSUM ‘z <> PosInf’ K_TAC \\
      Q.PAT_X_ASSUM ‘z <> NegInf’ K_TAC \\
      Q.PAT_X_ASSUM ‘0 < z’       K_TAC \\
      GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [mul_comm] \\
      Know ‘y * Normal r <= Normal a * Normal M <=> y <= Normal a * Normal M / Normal r’
      >- (MATCH_MP_TAC le_rdiv >> art []) >> Rewr' \\
      Know ‘Normal a * Normal M / Normal r = Normal (a / sqrt r) * Normal (M / sqrt r)’
      >- (rw [extreal_mul_eq, extreal_div_eq] \\
          DISJ2_TAC \\
         ‘sqrt r <> 0’ by PROVE_TAC [SQRT_POS_NE] \\
          rw [GSYM POW_INV, Once EQ_SYM_EQ] \\
          MATCH_MP_TAC SQRT_POW_2 \\
          MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> Rewr' \\

      Q.PAT_X_ASSUM ‘((\n. &u a n / &u a (SUC n)) --> inv a) sequentially’ K_TAC \\
      Know ‘?N. !n. N <= n ==> &u a (SUC n) / &u a n <= Normal (a / sqrt r)’
      >- (‘!n. (0 :real) < &u a n’ by rw [] \\
          ‘!n. &u a n <> (0 :real)’ by METIS_TAC [REAL_LT_IMP_NE] \\
          ‘!n. &u a (SUC n) / &u a n = Normal (&u a (SUC n) / &u a n)’
             by (rw [extreal_of_num_def, extreal_div_eq]) >> POP_ORW \\
          SIMP_TAC std_ss [extreal_le_eq] \\
          Q.PAT_X_ASSUM ‘((\n. &u a (SUC n) / &u a n) --> a) sequentially’ MP_TAC \\
          Q.ABBREV_TAC ‘g :num -> real = \n. &u a (SUC n) / &u a n’ \\
         ‘!n. &u a (SUC n) / &u a n = g n’ by METIS_TAC [] >> POP_ORW \\
          rw [real_div, LIM_SEQUENTIALLY, dist, ABS_BOUNDS_LT] \\
          Q.ABBREV_TAC ‘b = inv (sqrt r)’ \\
          Know ‘1 < b’ >- (Q.UNABBREV_TAC ‘b’ \\
                          ‘1 = inv (1 :real)’ by PROVE_TAC [REAL_INV1] >> POP_ORW \\
                           Know ‘inv 1 < inv (sqrt r) <=> sqrt r < 1’
                           >- (MATCH_MP_TAC REAL_INV_LT_ANTIMONO >> rw [] \\
                               MATCH_MP_TAC SQRT_POS_LT >> art []) >> Rewr' \\
                          ‘1 = sqrt (1 :real)’ by PROVE_TAC [SQRT_1] >> POP_ORW \\
                           MATCH_MP_TAC SQRT_MONO_LT >> art [] \\
                           MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> DISCH_TAC \\
          Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘a * b - a’)) \\
          Know ‘0 < a * b - a’
          >- (rw [REAL_SUB_LT] \\
              Know ‘a < a * b <=> a * 1 < a * b’
              >- PROVE_TAC [REAL_MUL_RID] >> Rewr' \\
              MATCH_MP_TAC REAL_LT_LMUL_IMP >> art [] \\
              PROVE_TAC [REAL_LT_01, REAL_LT_TRANS]) \\
          RW_TAC std_ss [] \\
          Q.EXISTS_TAC ‘N’ >> rpt STRIP_TAC \\
          Q.PAT_X_ASSUM ‘!n. N <= n ==> P’ (MP_TAC o (Q.SPEC ‘n’)) \\
          RW_TAC std_ss [] \\
          POP_ASSUM MP_TAC >> REAL_ARITH_TAC) \\
      Q.PAT_X_ASSUM ‘((\n. &u a (SUC n) / &u a n) --> a) sequentially’ K_TAC \\
      DISCH_THEN (Q.X_CHOOSE_THEN ‘N1’ STRIP_ASSUME_TAC) \\

      Know ‘?N. !n. N <= n ==> h (u a (SUC n)) <= Normal (M / sqrt r)’
      >- (Q.PAT_X_ASSUM ‘((\n. real (h (u a (SUC n)))) --> M) sequentially’ MP_TAC \\
          Know ‘((\n. real (h (u a (SUC n)))) --> M) sequentially <=>
                !e. 0 < e ==> ?N. !n. N <= n ==> abs (h (u a (SUC n)) - Normal M) < Normal e’
          >- (HO_MATCH_MP_TAC (REWRITE_RULE [o_DEF] LIM_SEQUENTIALLY_real_normal) \\
              Q.X_GEN_TAC ‘n’ \\
              FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> Rewr' \\
          RW_TAC std_ss [abs_bounds_lt] \\
         ‘sqrt r <> 0’ by PROVE_TAC [SQRT_POS_NE] \\
          rw [real_div, GSYM extreal_mul_eq] \\
          Q.ABBREV_TAC ‘b = inv (sqrt r)’ \\
          Know ‘1 < b’ >- (Q.UNABBREV_TAC ‘b’ \\
                          ‘1 = inv (1 :real)’ by PROVE_TAC [REAL_INV1] >> POP_ORW \\
                           Know ‘inv 1 < inv (sqrt r) <=> sqrt r < 1’
                           >- (MATCH_MP_TAC REAL_INV_LT_ANTIMONO >> rw [] \\
                               MATCH_MP_TAC SQRT_POS_LT >> art []) >> Rewr' \\
                          ‘1 = sqrt (1 :real)’ by PROVE_TAC [SQRT_1] >> POP_ORW \\
                           MATCH_MP_TAC SQRT_MONO_LT >> art [] \\
                           MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> DISCH_TAC \\
          Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘M * b - M’)) \\

         ‘0 < M’ by PROVE_TAC [REAL_LT_LE] \\
       (* IMPORTANT: here it is why the case ‘M = 0’ must be eliminated: *)
          Know ‘0 < M * b - M’ >- rw [REAL_SUB_LT] \\
          RW_TAC std_ss [] \\
          Q.EXISTS_TAC ‘N’ >> rpt STRIP_TAC \\
          Q.PAT_X_ASSUM ‘!n. N <= n ==> P’ (MP_TAC o (Q.SPEC ‘n’)) \\
          RW_TAC std_ss [GSYM extreal_sub_eq] \\
          POP_ASSUM MP_TAC \\
         ‘0 < SUC n’ by rw [] \\
         ‘?z. h (u a (SUC n)) = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
          simp [extreal_sub_eq, extreal_mul_eq, extreal_le_eq, extreal_lt_eq] \\
          REAL_ARITH_TAC) \\
      Q.PAT_X_ASSUM ‘((\n. real (h (u a (SUC n)))) --> M) sequentially’ K_TAC \\
      DISCH_THEN (Q.X_CHOOSE_THEN ‘N2’ STRIP_ASSUME_TAC) \\

   (* now choose Z such that MAX N1 N2 <= f Z *)
      Q.ABBREV_TAC ‘Z = LEAST n. MAX N1 N2 <= f n’ \\
      MATCH_MP_TAC le_trans \\
      Q.EXISTS_TAC ‘sup {h (SUC n) | Z <= n}’ \\
      CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘Z’ >> rw []) \\

      rw [sup_le'] (* this asserts ‘n’ *) \\
      Know ‘MAX N1 N2 <= f n’
      >- (POP_ASSUM MP_TAC \\
          Q.UNABBREV_TAC ‘Z’ >> numLib.LEAST_ELIM_TAC \\
          reverse CONJ_TAC
          >- (Q.X_GEN_TAC ‘j’ >> rpt STRIP_TAC \\
              MATCH_MP_TAC LESS_EQ_TRANS \\
              Q.EXISTS_TAC ‘f j’ >> rw []) \\
          Q.PAT_X_ASSUM ‘!n. ?N. n <= f N’ (STRIP_ASSUME_TAC o (Q.SPEC ‘MAX N1 N2’)) \\
          Q.EXISTS_TAC ‘N’ >> art []) >> rw [] \\
      Q.PAT_X_ASSUM ‘!k. u a (f k) <= SUC k /\ P’ (STRIP_ASSUME_TAC o (Q.SPEC ‘n’)) \\
      MATCH_MP_TAC le_trans \\
      Q.EXISTS_TAC ‘&u a (SUC (f n)) / &u a (f n) * h (u a (SUC (f n)))’ >> art [] \\
      MATCH_MP_TAC le_mul2 >> simp [] \\
     ‘&u a (f n) = Normal (&u a (f n))’ by rw [extreal_of_num_def] >> POP_ORW \\
      MATCH_MP_TAC le_div >> rw [extreal_of_num_def, extreal_le_eq],

      (* goal 2 (of 2): easier *)
      rw [ext_liminf_def, le_sup'] \\
      MATCH_MP_TAC le_mul_epsilon >> rpt STRIP_TAC \\
      Cases_on ‘z = 0’
      >- (rw [] >> MATCH_MP_TAC le_trans \\
          Q.EXISTS_TAC ‘inf {h (SUC n) | 0 <= n}’ \\
          reverse CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC \\
                               Q.EXISTS_TAC ‘0’ >> rw []) \\
          rw [le_inf'] \\
          FIRST_X_ASSUM MATCH_MP_TAC >> rw []) \\
     ‘z <> NegInf’ by PROVE_TAC [pos_not_neginf] \\
      Know ‘z <> PosInf’
      >- (REWRITE_TAC [lt_infty] \\
          MATCH_MP_TAC lt_trans >> Q.EXISTS_TAC ‘1’ >> rw []) >> DISCH_TAC \\
     ‘0 < z’ by PROVE_TAC [lt_le] \\
     ‘?r. r <> 0 /\ 0 < r /\ r < 1 /\ z = Normal r’
        by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] >> POP_ORW \\
      Q.PAT_X_ASSUM ‘0 <= z’      K_TAC \\
      Q.PAT_X_ASSUM ‘z < 1’       K_TAC \\
      Q.PAT_X_ASSUM ‘z <> 0’      K_TAC \\
      Q.PAT_X_ASSUM ‘z <> PosInf’ K_TAC \\
      Q.PAT_X_ASSUM ‘z <> NegInf’ K_TAC \\
      Q.PAT_X_ASSUM ‘0 < z’       K_TAC \\
     ‘0 < a’ by PROVE_TAC [REAL_LT_01, REAL_LT_TRANS] \\
     ‘a <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] \\
      Know ‘Normal r * (inv (Normal a) * Normal M) =
            Normal (inv a * sqrt r) * Normal (M * sqrt r)’
      >- (rw [extreal_mul_eq, extreal_div_eq, extreal_inv_eq] \\
         ‘sqrt r <> 0’ by PROVE_TAC [SQRT_POS_NE] \\
          rw [GSYM POW_INV, Once EQ_SYM_EQ] \\
          MATCH_MP_TAC SQRT_POW_2 \\
          MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> Rewr' \\

      Q.PAT_X_ASSUM ‘((\n. &u a (SUC n) / &u a n) --> a) sequentially’ K_TAC \\
      Know ‘?N. !n. N <= n ==> Normal (inv a * sqrt r) <= &u a n / &u a (SUC n)’
      >- (‘!n. (0 :real) < &u a n’ by rw [] \\
          ‘!n. &u a n <> (0 :real)’ by METIS_TAC [REAL_LT_IMP_NE] \\
          ‘!n. &u a n / &u a (SUC n) = Normal (&u a n / &u a (SUC n))’
             by (rw [extreal_of_num_def, extreal_div_eq]) >> POP_ORW \\
          SIMP_TAC std_ss [extreal_le_eq] \\
          Q.PAT_X_ASSUM ‘((\n. &u a n / &u a (SUC n)) --> inv a) sequentially’ MP_TAC \\
          Q.ABBREV_TAC ‘g :num -> real = \n. &u a n / &u a (SUC n)’ \\
         ‘!n. &u a n / &u a (SUC n) = g n’ by METIS_TAC [] >> POP_ORW \\
          rw [LIM_SEQUENTIALLY, dist, ABS_BOUNDS_LT] \\

          ONCE_REWRITE_TAC [REAL_MUL_COMM] \\
          Know ‘!n. sqrt r <= g n * a <=> sqrt r / a <= g n’
          >- (Q.X_GEN_TAC ‘n’ \\
              ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
              MATCH_MP_TAC REAL_LE_LDIV_EQ >> art []) >> Rewr' \\

          Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘(1 - sqrt r) / a’)) \\
          Know ‘0 < (1 - sqrt r) / a’
          >- (MATCH_MP_TAC REAL_LT_DIV >> art [] \\
              rw [REAL_SUB_LT] \\
             ‘1 = sqrt (1 :real)’ by PROVE_TAC [SQRT_1] >> POP_ORW \\
              MATCH_MP_TAC SQRT_MONO_LT >> art [] \\
              MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
          RW_TAC std_ss [] \\
          Q.EXISTS_TAC ‘N’ >> rpt STRIP_TAC \\
          Q.PAT_X_ASSUM ‘!n. N <= n ==> P’ (MP_TAC o (Q.SPEC ‘n’)) \\
          RW_TAC std_ss [] \\
          Q.PAT_X_ASSUM ‘-((1 - sqrt r) / a) < g n - realinv a’ MP_TAC \\
          simp [real_div, REAL_NEG_SUB, REAL_SUB_LDISTRIB] \\
          REAL_ARITH_TAC) \\
      Q.PAT_X_ASSUM ‘((\n. &u a n / &u a (SUC n)) --> inv a) sequentially’ K_TAC \\
      DISCH_THEN (Q.X_CHOOSE_THEN ‘N1’ STRIP_ASSUME_TAC) \\

      Know ‘?N. !n. N <= n ==> Normal (M * sqrt r) <= h (u a n)’
      >- (Q.PAT_X_ASSUM ‘((\n. real (h (u a (SUC n)))) --> M) sequentially’ MP_TAC \\
          Know ‘((\n. real (h (u a (SUC n)))) --> M) sequentially <=>
                !e. 0 < e ==> ?N. !n. N <= n ==> abs (h (u a (SUC n)) - Normal M) < Normal e’
          >- (HO_MATCH_MP_TAC (REWRITE_RULE [o_DEF] LIM_SEQUENTIALLY_real_normal) \\
              Q.X_GEN_TAC ‘n’ \\
              FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> Rewr' \\
          RW_TAC std_ss [abs_bounds_lt] \\
         ‘sqrt r <> 0’ by PROVE_TAC [SQRT_POS_NE] \\
          rw [GSYM extreal_mul_eq] \\

          Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘M - M * sqrt r’)) \\

         ‘0 < M’ by PROVE_TAC [REAL_LT_LE] \\
          Know ‘0 < M - M * sqrt r’
          >- (rw [REAL_SUB_LT] \\
             ‘1 = sqrt (1 :real)’ by PROVE_TAC [SQRT_1] >> POP_ORW \\
              MATCH_MP_TAC SQRT_MONO_LT >> art [] \\
              MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
          RW_TAC std_ss [] \\
          Q.EXISTS_TAC ‘SUC N’ >> rpt STRIP_TAC \\
          Cases_on ‘n’ >- fs [] \\
          rename1 ‘SUC N <= SUC n’ \\
         ‘N <= n’ by rw [] \\
          Q.PAT_X_ASSUM ‘!n. N <= n ==> P’ (MP_TAC o (Q.SPEC ‘n’)) \\
          RW_TAC std_ss [GSYM extreal_sub_eq, extreal_mul_eq] \\
          Know ‘-(Normal M - Normal (M * sqrt r)) = Normal (M * sqrt r) - Normal M’
          >- (rw [extreal_sub_eq, extreal_ainv_def, REAL_NEG_SUB]) \\
          DISCH_THEN (FULL_SIMP_TAC std_ss o wrap) \\
          Q.PAT_X_ASSUM ‘Normal (M * sqrt r) - Normal M < h (u a (SUC n)) - Normal M’ MP_TAC \\
         ‘?z. h (u a (SUC n)) = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
          simp [extreal_sub_eq, extreal_lt_eq, extreal_le_eq] \\
          REAL_ARITH_TAC) \\
      Q.PAT_X_ASSUM ‘((\n. real (h (u a (SUC n)))) --> M) sequentially’ K_TAC \\
      DISCH_THEN (Q.X_CHOOSE_THEN ‘N2’ STRIP_ASSUME_TAC) \\

   (* now choose Z such that MAX N1 N2 <= f Z *)
      Q.ABBREV_TAC ‘Z = LEAST n. MAX N1 N2 <= f n’ \\
      MATCH_MP_TAC le_trans \\
      Q.EXISTS_TAC ‘inf {h (SUC n) | Z <= n}’ \\
      reverse CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘Z’ >> rw []) \\
      rw [le_inf'] (* this asserts ‘n’ *) \\
      Know ‘MAX N1 N2 <= f n’
      >- (POP_ASSUM MP_TAC \\
          Q.UNABBREV_TAC ‘Z’ >> numLib.LEAST_ELIM_TAC \\
          reverse CONJ_TAC
          >- (Q.X_GEN_TAC ‘j’ >> rpt STRIP_TAC \\
              MATCH_MP_TAC LESS_EQ_TRANS \\
              Q.EXISTS_TAC ‘f j’ >> rw []) \\
          Q.PAT_X_ASSUM ‘!n. ?N. n <= f N’ (STRIP_ASSUME_TAC o (Q.SPEC ‘MAX N1 N2’)) \\
          Q.EXISTS_TAC ‘N’ >> art []) >> rw [] \\
      Q.PAT_X_ASSUM ‘!k. u a (f k) <= SUC k /\ P’ (STRIP_ASSUME_TAC o (Q.SPEC ‘n’)) \\
      MATCH_MP_TAC le_trans \\
      Q.EXISTS_TAC ‘&u a (f n) / &u a (SUC (f n)) * h (u a (f n))’ >> art [] \\
      MATCH_MP_TAC le_mul2 >> simp [] \\
      simp [extreal_of_num_def, extreal_le_eq] \\
      STRONG_CONJ_TAC >- (MATCH_MP_TAC SQRT_POS_LE \\
                          MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
      DISCH_TAC \\
      MATCH_MP_TAC REAL_LE_MUL >> art [] ]
QED

(* |- !p X.
        prob_space p /\ (!n. real_random_variable (X n) p) /\
        (!n x. x IN p_space p ==> 0 <= X n x) /\
        pairwise_indep_vars p X (\n. Borel) univ(:num) /\
        identical_distribution p X Borel univ(:num) /\ integrable p (X 0) ==>
        ((\n x. SIGMA (\i. X i x) (count1 n) / &SUC n) -->
         (\x. expectation p (X 0))) (almost_everywhere p)
 *)
Theorem SLLN_IID_wlog'[local] =
    SIMP_RULE std_ss [LLN_alt_converge_AE_IID] SLLN_IID_wlog

(* The Strong Law of Large Numbers for I.I.D. Random Variables - The Convergence Part

   The proof depends on SLLN_IID_wlog and follows the first sentence of the proof of
   Theorem 22.1 [6, p.282]: "If the theorem holds for nonnegative random variables, ..."
 *)
Theorem SLLN_IID :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) /\
          pairwise_indep_vars p X (\n. Borel) UNIV /\
          identical_distribution p X Borel UNIV /\ integrable p (X 0)
      ==> LLN p X almost_everywhere
Proof
    qx_genl_tac [‘p’, ‘X’]
 >> Q.ABBREV_TAC ‘Y = \i. fn_plus (X i)’
 >> Q.ABBREV_TAC ‘Z = \i. fn_minus (X i)’
 >> rw [LLN_alt_converge_AE_IID, expectation_def, integral_def]
 >> ‘!x i. X i x = Y i x - Z i x’ by METIS_TAC [FN_DECOMP]
 >> POP_ORW
 >> Know ‘((\n x. SIGMA (\i. Y i x - Z i x) (count1 n) / &SUC n) -->
           (\x. pos_fn_integral p (Y 0) - pos_fn_integral p (Z 0)))
          (almost_everywhere p) <=>
          ((\n x. SIGMA (\i. Y i x) (count1 n) / &SUC n -
                  SIGMA (\i. Z i x) (count1 n) / &SUC n) -->
           (\x. pos_fn_integral p (Y 0) - pos_fn_integral p (Z 0)))
          (almost_everywhere p)’
 >- (MATCH_MP_TAC converge_AE_cong_full \\
     Q.EXISTS_TAC ‘0’ >> rw [] \\
    ‘FINITE (count1 n)’ by METIS_TAC [FINITE_COUNT] \\
     Know ‘SIGMA (\i. Y i x - Z i x) (count1 n) =
           SIGMA (\i. Y i x) (count1 n) - SIGMA (\i. Z i x) (count1 n)’
     >- (MATCH_MP_TAC
          (BETA_RULE (Q.SPECL [‘\ (i :num). Y i x’, ‘\ (i :num). Z i x’]
                              (MATCH_MP EXTREAL_SUM_IMAGE_SUB
                                        (ASSUME “FINITE (count1 n)”)))) \\
         DISJ1_TAC (* or DISJ2_TAC *) \\
         Q.X_GEN_TAC ‘i’ \\
         rw [Abbr ‘Y’, Abbr ‘Z’] >- (MATCH_MP_TAC pos_not_neginf >> rw [FN_PLUS_POS]) \\
         MATCH_MP_TAC FN_MINUS_NOT_INFTY \\
         FULL_SIMP_TAC std_ss [real_random_variable_def]) >> Rewr' \\
     ONCE_REWRITE_TAC [EQ_SYM_EQ] >> MATCH_MP_TAC div_sub \\
    ‘&SUC n <> (0 :extreal)’ by rw [extreal_of_num_def, extreal_11] \\
     FULL_SIMP_TAC std_ss [real_random_variable_def] \\
     rw [] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> art [] \\
       Q.X_GEN_TAC ‘i’ >> rw [Abbr ‘Y’] \\
       MATCH_MP_TAC FN_PLUS_NOT_INFTY >> rw [],
       (* goal 2 (of 4) *)
       MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF >> art [] \\
       Q.X_GEN_TAC ‘i’ >> rw [Abbr ‘Y’] \\
       MATCH_MP_TAC pos_not_neginf >> rw [FN_PLUS_POS],
       (* goal 3 (of 4) *)
       MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> art [] \\
       Q.X_GEN_TAC ‘i’ >> rw [Abbr ‘Z’] \\
       MATCH_MP_TAC FN_MINUS_NOT_INFTY >> rw [],
       (* goal 4 (of 4) *)
       MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF >> art [] \\
       Q.X_GEN_TAC ‘i’ >> rw [Abbr ‘Z’] \\
       MATCH_MP_TAC pos_not_neginf >> rw [FN_MINUS_POS] ])
 >> Rewr'
 >> HO_MATCH_MP_TAC converge_AE_sub >> rw [] (* 6 subgoals *)
 >| [ (* goal 1 (of 6) *)
      MATCH_MP_TAC real_random_variable_LLN' >> rw [Abbr ‘Y’] \\
      MATCH_MP_TAC real_random_variable_fn_plus >> art [],
      (* goal 2 (of 6) *)
      MATCH_MP_TAC real_random_variable_const \\
      fs [integrable_def, Abbr ‘Y’, prob_space_def] \\
      MATCH_MP_TAC pos_not_neginf \\
      MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_PLUS_POS],
      (* goal 3 (of 6) *)
      Know ‘pos_fn_integral p (Y 0) = expectation p (Y 0)’
      >- (REWRITE_TAC [expectation_def, Once EQ_SYM_EQ] \\
          MATCH_MP_TAC integral_pos_fn \\
          fs [Abbr ‘Y’, FN_PLUS_POS, prob_space_def]) >> Rewr' \\
      MATCH_MP_TAC SLLN_IID_wlog' (* here *) \\
      simp [Abbr ‘Y’, FN_PLUS_POS] \\
      STRONG_CONJ_TAC (* real_random_variable *)
      >- (Q.X_GEN_TAC ‘n’ >> MATCH_MP_TAC real_random_variable_fn_plus >> art []) \\
      DISCH_TAC \\
      Know ‘integrable p (fn_plus (X 0))’
      >- (MATCH_MP_TAC integrable_fn_plus >> fs [prob_space_def]) >> Rewr' \\
      Q.ABBREV_TAC ‘f = \(n :num) (x :extreal). max x 0’ \\
      Know ‘!(i :num). fn_plus (X i) = (f i) o (X i)’
      >- (rw [Abbr ‘f’, o_DEF, FN_PLUS_ALT]) >> Rewr \\
      Q.PAT_X_ASSUM `!n. real_random_variable (X n) p`
        (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
         (REWRITE_RULE [real_random_variable_def])) \\
      CONJ_TAC (* pairwise_indep_vars *)
      >- (MATCH_MP_TAC pairwise_indep_vars_cong >> rw [Abbr ‘f’] \\
          REWRITE_TAC [IN_MEASURABLE_BOREL_BOREL_MAX]) \\
      Q.ABBREV_TAC ‘g = \x. max x 0’ \\
      Q.UNABBREV_TAC ‘f’ >> simp [] \\
      MATCH_MP_TAC identical_distribution_cong \\
      rw [Abbr ‘g’, IN_MEASURABLE_BOREL_BOREL_MAX],
      (* goal 4 (of 6) *)
      MATCH_MP_TAC real_random_variable_LLN' >> rw [Abbr ‘Z’] \\
      MATCH_MP_TAC real_random_variable_fn_minus >> art [],
      (* goal 5 (of 6) *)
      MATCH_MP_TAC real_random_variable_const \\
      fs [integrable_def, Abbr ‘Z’, prob_space_def] \\
      MATCH_MP_TAC pos_not_neginf \\
      MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_MINUS_POS],
      (* goal 6 (of 6) *)
      Know ‘pos_fn_integral p (Z 0) = expectation p (Z 0)’
      >- (REWRITE_TAC [expectation_def, Once EQ_SYM_EQ] \\
          MATCH_MP_TAC integral_pos_fn \\
          fs [Abbr ‘Z’, FN_MINUS_POS, prob_space_def]) >> Rewr' \\
      MATCH_MP_TAC SLLN_IID_wlog' (* here *) \\
      simp [Abbr ‘Z’, FN_MINUS_POS] \\
      STRONG_CONJ_TAC (* real_random_variable *)
      >- (Q.X_GEN_TAC ‘n’ >> MATCH_MP_TAC real_random_variable_fn_minus >> art []) \\
      DISCH_TAC \\
      Know ‘integrable p (fn_minus (X 0))’
      >- (MATCH_MP_TAC integrable_fn_minus >> fs [prob_space_def]) >> Rewr' \\
      Q.ABBREV_TAC ‘f = \(n :num) (x :extreal). -min x 0’ \\
      Know ‘!(i :num). fn_minus (X i) = (f i) o (X i)’
      >- (rw [Abbr ‘f’, o_DEF, FN_MINUS_ALT]) >> Rewr \\
      Q.PAT_X_ASSUM `!n. real_random_variable (X n) p`
        (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
         (REWRITE_RULE [real_random_variable_def])) \\
      CONJ_TAC (* pairwise_indep_vars *)
      >- (MATCH_MP_TAC pairwise_indep_vars_cong >> rw [Abbr ‘f’] \\
         ‘(\x. -min x 0) = extreal_ainv o (\x. min x 0)’ by rw [o_DEF] >> POP_ORW \\
          MATCH_MP_TAC MEASURABLE_COMP >> Q.EXISTS_TAC ‘Borel’ \\
          REWRITE_TAC [IN_MEASURABLE_BOREL_BOREL_MIN, IN_MEASURABLE_BOREL_BOREL_AINV]) \\
      Q.ABBREV_TAC ‘g = \x. -min x 0’ \\
      Q.UNABBREV_TAC ‘f’ >> simp [] \\
      MATCH_MP_TAC identical_distribution_cong \\
      rw [Abbr ‘g’] \\
     ‘(\x. -min x 0) = extreal_ainv o (\x. min x 0)’ by rw [o_DEF] >> POP_ORW \\
      MATCH_MP_TAC MEASURABLE_COMP >> Q.EXISTS_TAC ‘Borel’ \\
      REWRITE_TAC [IN_MEASURABLE_BOREL_BOREL_MIN, IN_MEASURABLE_BOREL_BOREL_AINV] ]
QED

(* A more useful form of SLLN_IID without ‘LLN’:
   |- !p X.
        prob_space p /\ (!n. real_random_variable (X n) p) /\
        pairwise_indep_vars p X (\n. Borel) univ(:num) /\
        identical_distribution p X Borel univ(:num) /\ integrable p (X 0) ==>
        ((\n x. SIGMA (\i. X i x) (count1 n) / &SUC n) -->
         (\x. expectation p (X 0))) (almost_everywhere p)
 *)
Theorem SLLN_IID_applied = SIMP_RULE std_ss [LLN_alt_converge_AE_IID] SLLN_IID

(* The 'diverge' part of SLLN_IID

   This is Theorem 5.4.2 (Part 2) of [2, p.133], the strongest version among others.
   See also Theorem 4 (Converse to the strong law of large numbers) of [11, p.241].

   The original version requires total independence, which is, however, only used by
   Borel-Cantelli Lemma (Part 2), which also has a version for pairwise independence
  (Borel_Cantelli_Lemma2p).
 *)
Theorem SLLN_IID_diverge :
    !p X. prob_space p /\ (!n. real_random_variable (X n) p) /\
          pairwise_indep_vars p X (\n. Borel) UNIV /\
          identical_distribution p X Borel UNIV /\
          expectation p (abs o X 0) = PosInf
      ==> AE x::p. limsup (\n. abs (SIGMA (\i. X i x) (count1 n)) / &SUC n) = PosInf
Proof
    rpt STRIP_TAC
 >> ‘sigma_algebra (measurable_space p)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA, prob_space_def]
 >> Know ‘!a. 0 < a ==> expectation p (\x. abs (X 0 x) / Normal a) = PosInf’
 >- (rpt STRIP_TAC >> CCONTR_TAC \\
     Q.ABBREV_TAC ‘Y = \x. abs (X 0 x) / Normal a’ \\
     Know ‘!x. 0 <= Y x’
     >- (RW_TAC std_ss [Abbr ‘Y’] \\
         MATCH_MP_TAC le_div >> RW_TAC std_ss [abs_pos]) >> DISCH_TAC \\
     Know ‘integrable p Y’
     >- (Know ‘integrable p Y <=> Y IN measurable (m_space p,measurable_sets p) Borel /\
                                  pos_fn_integral p Y <> PosInf’
         >- (MATCH_MP_TAC integrable_pos \\
             FULL_SIMP_TAC std_ss [prob_space_def]) >> Rewr' \\
         reverse CONJ_TAC
         >- (Know ‘pos_fn_integral p Y = expectation p Y’
             >- (REWRITE_TAC [Once EQ_SYM_EQ, expectation_def] \\
                 MATCH_MP_TAC integral_pos_fn \\
                 FULL_SIMP_TAC std_ss [prob_space_def]) >> Rewr' >> art []) \\
         Q.PAT_X_ASSUM `!n. real_random_variable (X n) p`
           (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
            (REWRITE_RULE [real_random_variable, p_space_def, events_def])) \\
         FULL_SIMP_TAC std_ss [prob_space_def, Abbr ‘Y’] \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL \\
         qexistsl_tac [‘abs o (X 0)’, ‘inv a’] \\
        ‘sigma_algebra (m_space p,measurable_sets p)’ by FULL_SIMP_TAC std_ss [measure_space_def] \\
         rw [] >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS' >> art []) \\
        ‘a <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] \\
         rw [extreal_div_def, extreal_inv_eq, Once mul_comm]) >> DISCH_TAC \\
  (* applying expectation_cmul *)
     Know ‘expectation p (\x. Normal a * Y x) = Normal a * expectation p Y’
     >- (MATCH_MP_TAC expectation_cmul >> art []) \\
     Know ‘expectation p (\x. Normal a * Y x) = expectation p (abs o X 0)’
     >- (MATCH_MP_TAC expectation_cong \\
         rw [Abbr ‘Y’, Once mul_comm, Once EQ_SYM_EQ] \\
         MATCH_MP_TAC div_mul_refl >> PROVE_TAC [REAL_LT_IMP_NE]) \\
     DISCH_THEN (PURE_ONCE_REWRITE_TAC o wrap) >> rw [] \\
     Know ‘expectation p Y <> NegInf’
     >- (MATCH_MP_TAC pos_not_neginf \\
         MATCH_MP_TAC expectation_pos >> art []) >> DISCH_TAC \\
    ‘?r. expectation p Y = Normal r’ by METIS_TAC [extreal_cases] \\
     rw [extreal_mul_def])
 >> DISCH_TAC
 (* applying expectation_converge' *)
 >> Q.ABBREV_TAC ‘Z = \a x. X 0 x / Normal a’
 >> Know ‘!a. 0 < a ==>
              suminf (\n. prob p {x | x IN p_space p /\ Normal a * &SUC n <= abs (X 0 x)}) = PosInf’
 >- (rpt STRIP_TAC \\
     Know ‘!n x. Normal a * &SUC n <= abs (X 0 x) <=> &SUC n <= abs (Z a x)’
     >- (RW_TAC std_ss [Abbr ‘Z’] \\
        ‘a <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] \\
         rw [abs_div_normal] \\
        ‘abs a = a’ by PROVE_TAC [ABS_REFL, REAL_LT_IMP_LE] >> POP_ORW \\
         ONCE_REWRITE_TAC [mul_comm] \\
         MATCH_MP_TAC le_rdiv >> art []) >> Rewr' \\
     Know ‘real_random_variable (Z a) p’
     >- (rw [Abbr ‘Z’] \\
         MATCH_MP_TAC real_random_variable_cdiv >> art [] \\
         PROVE_TAC [REAL_LT_IMP_NE]) >> DISCH_TAC \\
     Know ‘suminf (\n. prob p {x | x IN p_space p /\ &SUC n <= abs (Z a x)}) = PosInf <=>
           expectation p (abs o Z a) = PosInf’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC expectation_converge' >> art []) >> Rewr' \\
    ‘a <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] \\
     rw [Abbr ‘Z’, o_DEF, abs_div_normal])
 >> DISCH_TAC
 >> Q.UNABBREV_TAC ‘Z’
 >> Q.ABBREV_TAC ‘B = \a n. {y | Normal a * &SUC n <= abs y}’
 >> Know ‘!a n. B a n IN subsets Borel’
 >- (rw [Abbr ‘B’, le_abs_bounds] \\
    ‘{y | y <= -(Normal a * &SUC n) \/ Normal a * &SUC n <= y} =
     {y | y <= -(Normal a * &SUC n)} UNION {y | Normal a * &SUC n <= y}’ by SET_TAC [] \\
     POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_UNION \\
     REWRITE_TAC [SIGMA_ALGEBRA_BOREL, BOREL_MEASURABLE_SETS])
 >> DISCH_TAC
 >> Know ‘!a. 0 < a ==>
              suminf (\n. prob p {x | x IN p_space p /\ Normal a * &SUC n <= abs (X n x)}) =
              suminf (\n. prob p {x | x IN p_space p /\ Normal a * &SUC n <= abs (X 0 x)})’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC ext_suminf_eq >> rw [] \\
     Know ‘!i. {x | x IN p_space p /\ Normal a * &SUC n <= abs (X i x)} =
               {x | x IN p_space p /\ X i x IN B a n}’
     >- (rw [Once EXTENSION, Abbr ‘B’]) >> Rewr' \\
     MATCH_MP_TAC identical_distribution_alt_prob \\
     qexistsl_tac [‘Borel’, ‘univ(:num)’] >> rw [])
 >> DISCH_TAC
 >> Know ‘!a. 0 < a ==>
              suminf (\n. prob p {x | x IN p_space p /\ Normal a * &SUC n <= abs (X n x)}) =
              PosInf’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!a. 0 < a ==> suminf _ = suminf _’
       (fn th => ONCE_REWRITE_TAC [MATCH_MP th (ASSUME “0 < (a :real)”)]) \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> POP_ASSUM K_TAC
 >> DISCH_TAC
 (* applying Borel_Cantelli_Lemma2p *)
 >> Q.ABBREV_TAC ‘E = \a n. {x | x IN p_space p /\ Normal a * &SUC n <= abs (X n x)}’
 >> Know ‘!a n. E a n IN events p’
 >- (qx_genl_tac [‘a’, ‘n’] \\
     Know ‘!a n. E a n = PREIMAGE (X n) (B a n) INTER p_space p’
     >- (rw [Abbr ‘E’, Abbr ‘B’, PREIMAGE_def, Once EXTENSION] \\
         PROVE_TAC []) >> Rewr' \\
     fs [real_random_variable, IN_MEASURABLE])
 >> DISCH_TAC
 >> Know ‘!a. 0 < a ==> suminf (prob p o (E a)) = PosInf’
 >- (rw [o_DEF, Abbr ‘E’])
 >> Q.PAT_X_ASSUM ‘!a. 0 < a ==> suminf _ = PosInf’ K_TAC
 >> DISCH_TAC
 >> Know ‘!a. 0 < a ==> prob p (limsup (E a)) = 1’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC Borel_Cantelli_Lemma2p >> rw [] \\
     Know ‘!a n. E a n = PREIMAGE (X n) (B a n) INTER p_space p’
     >- (rw [Abbr ‘E’, Abbr ‘B’, PREIMAGE_def, Once EXTENSION] \\
         PROVE_TAC []) >> DISCH_TAC \\
     fs [pairwise_indep_vars_def, indep_rv_def, pairwise_indep_events_def])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘!a n. B a n IN subsets Borel’ K_TAC
 >> Q.UNABBREV_TAC ‘B’
 (* NOTE: the following definition of partial summation S is slightly different with
          those in previous proofs: ‘SIGMA (\i. X i x) (count n)’. With the present
          form it's easier to state ‘X (SUC n) x = S (SUC n) x - S n x’ for ‘0 < n’.
  *)
 >> Q.ABBREV_TAC ‘S = \n x. SIGMA (\i. X i x) (count1 n)’
 >> ASM_SIMP_TAC std_ss []
 >> Know ‘!n. real_random_variable (S n) p’
 >- (rw [Abbr ‘S’] \\
     MATCH_MP_TAC real_random_variable_sum >> rw [])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘D = \a n. {x | x IN p_space p /\ (1 / 2) * (Normal a * &SUC n) <= abs (S n x)}’
 >> Know ‘!a n. D a n IN events p’
 >- (rw [Abbr ‘D’, le_abs_bounds] \\
    ‘{x | x IN p_space p /\ (S n x <= -(1 / 2 * (Normal a * &SUC n)) \/
                             1 / 2 * (Normal a * &SUC n) <= S n x)} =
       ({x | S n x <= -(1 / 2 * (Normal a * &SUC n))} INTER p_space p) UNION
       ({x | 1 / 2 * (Normal a * &SUC n) <= S n x} INTER p_space p)’ by SET_TAC [] \\
     POP_ORW \\
     Q.PAT_X_ASSUM `!n. real_random_variable (S n) p`
       (STRIP_ASSUME_TAC o (CONV_RULE FORALL_AND_CONV) o
        (REWRITE_RULE [real_random_variable, p_space_def, events_def])) \\
     rw [p_space_def, events_def] \\
     MATCH_MP_TAC MEASURE_SPACE_UNION \\
     CONJ_TAC >- FULL_SIMP_TAC std_ss [prob_space_def] \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE])
 >> DISCH_TAC
 (* applying LIMSUP_MONO_STRONGER *)
 >> Know ‘!a. 0 < a ==> limsup (E a) SUBSET limsup (D a)’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC LIMSUP_MONO_STRONGER \\
     Q.EXISTS_TAC ‘1’ >> rw [Abbr ‘E’, Abbr ‘D’] \\
     Cases_on ‘n’ (* base case *)
     >- (Q.EXISTS_TAC ‘0’ >> fs [Abbr ‘S’, COUNT_ONE, EXTREAL_SUM_IMAGE_SING] \\
         MATCH_MP_TAC le_trans \\
         Q.EXISTS_TAC ‘1 * Normal a’ \\
         reverse CONJ_TAC >- rw [] \\
         MATCH_MP_TAC le_rmul_imp >> rw [half_between, extreal_of_num_def, extreal_le_eq] \\
         MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
     rename1 ‘Normal a * &SUC (SUC n') <= abs (X (SUC n) y)’ \\
     Know ‘X (SUC n) y = S (SUC n) y - S n y’
     >- (rw [Abbr ‘S’] >> REWRITE_TAC [Once COUNT_SUC] \\
        ‘FINITE (count1 n)’ by METIS_TAC [FINITE_COUNT] \\
         Know ‘SIGMA (\i. X i y) (SUC n INSERT count1 n) =
               (\i. X i y) (SUC n) + SIGMA (\i. X i y) (count1 n DELETE (SUC n))’
         >- (irule EXTREAL_SUM_IMAGE_PROPERTY_POS \\
             fs [real_random_variable_def]) >> BETA_TAC \\
         Know ‘count1 n DELETE SUC n = count1 n’
         >- (rw [GSYM DELETE_NON_ELEMENT]) >> Rewr' >> Rewr' \\
         ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC add_sub \\
         FULL_SIMP_TAC std_ss [real_random_variable_def]) \\
     DISCH_THEN (FULL_SIMP_TAC std_ss o wrap) \\
     Know ‘Normal a * &SUC (SUC n) <= abs (S (SUC n) y) + abs (S n y)’
     >- (MATCH_MP_TAC le_trans \\
         Q.EXISTS_TAC ‘abs (S (SUC n) y - S n y)’ >> art [] \\
         MATCH_MP_TAC abs_triangle_neg \\
         FULL_SIMP_TAC std_ss [real_random_variable_def]) \\
     POP_ASSUM K_TAC >> DISCH_TAC \\
  (* amazing part *)
     Know ‘1 / 2 * (Normal a * &SUC (SUC n)) <= abs (S (SUC n) y) \/
           1 / 2 * (Normal a * &SUC (SUC n)) <= abs (S n y)’
     >- (SPOSE_NOT_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [GSYM extreal_lt_def]) \\
         Suff ‘abs (S (SUC n) y) + abs (S n y) < Normal a * &SUC (SUC n)’
         >- METIS_TAC [let_antisym] \\
         GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM x_half_half] \\
         MATCH_MP_TAC lt_add2 >> art []) \\
     STRIP_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC ‘SUC n’ >> rw [],
       (* goal 2 (of 2) *)
       Q.EXISTS_TAC ‘n’ >> rw [] \\
       MATCH_MP_TAC le_trans \\
       Q.EXISTS_TAC ‘1 / 2 * (Normal a * &SUC (SUC n))’ >> art [] \\
       MATCH_MP_TAC le_lmul_imp >> REWRITE_TAC [half_between] \\
       MATCH_MP_TAC le_lmul_imp >> rw [extreal_of_num_def, extreal_le_eq] \\
       MATCH_MP_TAC REAL_LT_IMP_LE >> art [] ])
 >> DISCH_TAC
 (* stage work *)
 >> Know ‘!a. 0 < a ==> prob p (limsup (D a)) = 1’
 >- (rw [GSYM le_antisym]
     >- (MATCH_MP_TAC PROB_LE_1 >> art [] \\
         MATCH_MP_TAC EVENTS_LIMSUP >> art []) \\
     Q.PAT_X_ASSUM ‘!a. 0 < a ==> prob p (limsup (E a)) = 1’
       (fn th => ONCE_REWRITE_TAC [SYM (MATCH_MP th (ASSUME “0 < (a :real)”))]) \\
     MATCH_MP_TAC PROB_INCREASING >> art [] \\
     METIS_TAC [EVENTS_LIMSUP])
 (* final cleanup *)
 >> Q.PAT_X_ASSUM ‘!a. 0 < a ==> suminf _ = PosInf’                K_TAC
 >> Q.PAT_X_ASSUM ‘!a. 0 < a ==> suminf _ = PosInf’                K_TAC
 >> Q.PAT_X_ASSUM ‘!a n. E a n IN events p’                        K_TAC
 >> Q.PAT_X_ASSUM ‘!a. 0 < a ==> prob p (limsup (E a)) = 1’        K_TAC
 >> Q.PAT_X_ASSUM ‘!a. 0 < a ==> limsup (E a) SUBSET limsup (D a)’ K_TAC
 >> Q.PAT_X_ASSUM ‘!a. 0 < a ==> expectation p _ = PosInf’         K_TAC
 >> Q.UNABBREV_TAC ‘E’
 >> DISCH_TAC
 >> Know ‘!a n x. 1 / 2 * (Normal a * &SUC n) <= abs (S n x) <=>
                  1 / 2 * (Normal a * &SUC n) * inv (&SUC n) <= abs (S n x) * inv (&SUC n)’
 >- (rpt GEN_TAC \\
     MATCH_MP_TAC (GSYM le_rmul) \\
     CONJ_TAC >- (MATCH_MP_TAC inv_pos' >> rw [extreal_of_num_def, extreal_lt_eq]) \\
    ‘&SUC n <> (0 :real)’ by rw [] \\
     rw [extreal_of_num_def, extreal_inv_eq])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> ‘!a n. 1 / 2 * (Normal a * &SUC n) * inv (&SUC n) =
           1 / 2 * Normal a * (inv (&SUC n) * &SUC n)’ by PROVE_TAC [mul_assoc, mul_comm]
 >> POP_ASSUM (FULL_SIMP_TAC std_ss o wrap)
 >> Know ‘!n. inv (&SUC n) * &SUC n = (1 :extreal)’
 >- (qx_gen_tac ‘n’ \\
     MATCH_MP_TAC mul_linv >> rw [extreal_of_num_def])
 >> DISCH_THEN (fn th => FULL_SIMP_TAC std_ss [th, mul_rone])
 >> Know ‘!n x. abs (S n x) * inv (&SUC n) = abs (S n x) / &SUC n’
 >- (rpt GEN_TAC \\
    ‘&SUC n <> (0 :real)’ by rw [] \\
     rw [extreal_of_num_def, extreal_div_def])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 (* applying PROB_LIMSUP *)
 >> Know ‘!a. 0 < a ==> AE x::p. 1 / 2 * Normal a <= limsup (\n. abs (S n x) / &SUC n)’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!a. 0 < a ==> prob p (limsup (D a)) = 1’
      (fn th => ASSUME_TAC (MATCH_MP th (ASSUME “0 < (a :real)”))) \\
     Know ‘AE x::p. x IN limsup (D a)’
     >- (MATCH_MP_TAC PROB_ONE_AE >> art [] \\
         MATCH_MP_TAC EVENTS_LIMSUP >> art []) \\
     rw [AE_DEF, IN_LIMSUP] \\
     Q.EXISTS_TAC ‘N’ >> rw [] \\
     Q.PAT_X_ASSUM ‘!x. x IN m_space p /\ x NOTIN N ==> P’
       (fn th => MP_TAC (MATCH_MP th (CONJ (ASSUME “x IN m_space p”)
                                           (ASSUME “x NOTIN N”)))) \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘Z’ STRIP_ASSUME_TAC) \\
     Q.PAT_X_ASSUM ‘!a n. D a n IN events p’   K_TAC \\
     Q.PAT_X_ASSUM ‘prob p (limsup (D a)) = 1’ K_TAC \\
     Q.UNABBREV_TAC ‘D’ >> FULL_SIMP_TAC std_ss [GSPECIFICATION] \\
  (* stage work *)
     rw [ext_limsup_def, le_inf'] \\
     rw [le_sup'] (* cannot be merged into previous tactics *) \\
  (* now pick n IN Z such that m <= n *)
     Know ‘?n. n IN Z /\ m <= n’
     >- (CCONTR_TAC >> FULL_SIMP_TAC bool_ss [GSYM NOT_LESS] \\
         Know ‘Z SUBSET (count m)’
         >- (rw [SUBSET_DEF, IN_COUNT] >> METIS_TAC []) >> DISCH_TAC \\
         Suff ‘FINITE Z’ >- METIS_TAC [] \\
         MATCH_MP_TAC SUBSET_FINITE_I \\
         Q.EXISTS_TAC ‘count m’ >> rw [FINITE_COUNT]) \\
     STRIP_TAC (* this asserts the needed ‘n’ *) \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC ‘abs (S n x) / &SUC n’ \\
     CONJ_TAC >- (Q.PAT_X_ASSUM ‘!n. n IN Z ==> P’ (MP_TAC o (Q.SPEC ‘n’)) \\
                  RW_TAC std_ss []) \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘n’ >> art [])
 (* final stage *)
 >> rw [AE_DEF]
 >> Know ‘!i. ?N. null_set p N /\
                  !x. x IN m_space p /\ x NOTIN N ==>
                      1 / 2 * Normal (&SUC i) <= limsup (\n. abs (S n x) / &SUC n)’
 >- (Q.X_GEN_TAC ‘i’ >> POP_ASSUM (MP_TAC o (Q.SPEC ‘&SUC i’)) \\
    ‘(0 :real) < &SUC i’ by rw [] \\
     RW_TAC std_ss [])
 >> DISCH_THEN (STRIP_ASSUME_TAC o (SIMP_RULE std_ss [SKOLEM_THM]))
 >> Q.EXISTS_TAC ‘BIGUNION (IMAGE f UNIV)’
 >> CONJ_TAC >- (MATCH_MP_TAC (REWRITE_RULE [IN_APP] NULL_SET_BIGUNION) >> art [] \\
                 FULL_SIMP_TAC std_ss [prob_space_def])
 >> rw [IN_BIGUNION_IMAGE]
 >> CCONTR_TAC
 >> Know ‘limsup (\n. abs (S n x) / &SUC n) <> NegInf’
 >- (MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC ext_limsup_pos >> RW_TAC std_ss [] \\
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [extreal_of_num_def] \\
     MATCH_MP_TAC le_div >> rw [abs_pos])
 >> DISCH_TAC
 >> ‘?r. limsup (\n. abs (S n x) / &SUC n) = Normal r’ by METIS_TAC [extreal_cases]
 (* now choose an enough big ‘i’ as ‘j’ *)
 >> Q.ABBREV_TAC ‘j = clg (2 * r)’
 >> Q.PAT_X_ASSUM ‘!i. null_set p (f i) /\ !x. P’ (STRIP_ASSUME_TAC o (Q.SPEC ‘j’))
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘x’))
 >> RW_TAC std_ss [GSYM extreal_lt_def]
 >> Know ‘Normal r = 1 / 2 * Normal (2 * r)’
 >- (rw [extreal_of_num_def, GSYM extreal_mul_eq, mul_assoc] \\
     rw [GSYM div_mul_refl, extreal_mul_def])
 >> Rewr'
 >> MATCH_MP_TAC lt_lmul_imp
 >> rw [half_between, extreal_lt_eq, extreal_of_num_def, extreal_div_eq]
 >> MATCH_MP_TAC REAL_LET_TRANS
 >> Q.EXISTS_TAC ‘&j’
 >> rw [Abbr ‘j’, LE_NUM_CEILING]
QED

val _ = export_theory ();
val _ = html_theory "large_number";

(* References:

  [1] Kolmogorov, A.N.: Foundations of the Theory of Probability (Grundbegriffe der
      Wahrscheinlichkeitsrechnung). Chelsea Publishing Company, New York. (1950).
  [2] Chung, K.L.: A Course in Probability Theory, Third Edition. Academic Press (2001).
  [3] Rosenthal, J.S.: A First Look at Rigorous Probability Theory (Second Editoin).
      World Scientific Publishing Company (2006).
  [4] Shiryaev, A.N.: Probability-1. Springer-Verlag New York (2016).
  [5] Shiryaev, A.N.: Probability-2. Springer-Verlag New York (2019).
  [6] Billingsley, P.: Probability and Measure (Third Edition). Wiley-Interscience (1995).
  [7] Cinlar, E.: Probability and Stochastics. Springer (2011).
  [8] Kolmogoroff, A.N.: On Sums of Independent Random Variables (English Translation).
      In "Selected Works of A. N. Kolmogorov. Volume II. Probability Theory and Mathematical
      Statistics, A.N. Shiryayev (eds.), Springer Netherlands (1992).
  [9] Schilling, R.L.: Measures, Integrals and Martingales (Second Edition).
      Cambridge University Press (2017).
 [10] Feller, W.: An Introduction to Probability Theory and Its Applications, vol 1, 3rd edition.
      John Wiley & Sons, Inc., New York, N.Y. (2004).
 [11] Feller, W.: An Introduction to Probability Theory and Its Applications, vol 2, 2rd edition.
      John Wiley & Sons, Inc., New York, N.Y. (1967).
 [12] Etemadi, N.: An elementary proof of the strong law of large numbers.
      Z. Wahrsch. Verw. Gebiete. 55, 119-122 (1981).
 [13] Gnedenko, B.V., Kolmogorov, A.N.: Limit distributions for sums of independent random
      variables. Addison-Wesley Publishing Company, Inc., Cambridge, MA (1954).
 [14] Levy, P.: Theorie de L'addition des Variables Aleatoires. Gauthier-Villars, Paris (1937).
 [15] Nagaev, S.V.: On Necessary and Sufficient Conditions for the Strong Law of Large Numbers.
      Theory Probab. Appl. 17 (4), 573-581 (1973).
 *)
