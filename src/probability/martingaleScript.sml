(* ------------------------------------------------------------------------- *)
(* The Theory of Martingales for Sigma-Finite Measure Spaces                 *)
(* (Lebesgue Integration Extras, Product Measure and Fubini-Tonelli Theorem) *)
(*                                                                           *)
(* Author: Chun Tian (binghe) <binghe.lisp@gmail.com> (2019 - 2022)          *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open pairTheory relationTheory prim_recTheory arithmeticTheory pred_setTheory
     combinTheory fcpTheory hurdUtils;

open realTheory realLib seqTheory transcTheory iterateTheory real_sigmaTheory
     topologyTheory real_topologyTheory metricTheory;

open util_probTheory extrealTheory sigma_algebraTheory measureTheory
     real_borelTheory borelTheory lebesgueTheory;

val _ = new_theory "martingale";

val _ = hide "S";

fun METIS ths tm = prove(tm, METIS_TAC ths);

val _ = intLib.deprecate_int ();
val _ = ratLib.deprecate_rat ();

(* "The theory of martingales as we know it now goes back to Doob and most of
    the material of this and the following chapter can be found in his seminal
    monograph [2] from 1953.

    We want to understand martingales as an analysis tool which will be useful
    for the study of L^p- and almost everywhere convergence and, in particular,
    for the further development of measure and integration theory. Our presentation
    differs somewhat from the standard way to introduce martingales - conditional
    expectations will be defined later in [1, Chapter 22] - but the results and
    their proofs are pretty much the usual ones."

  -- Rene L. Schilling, "Measures, Integrals and Martingales" [1]

   "Martingale theory illustrates the history of mathematical probability: the
    basic definitions are inspired by crude notions of gambling, but the theory
    has become a sophisticated tool of modern abstract mathematics, drawing from
    and contributing to other field."

  -- J. L. Doob, "What is a Martingale?" [3] *)

(* ------------------------------------------------------------------------- *)
(*  Martingale definitions ([1, Chapter 23])                                 *)
(* ------------------------------------------------------------------------- *)

Definition sub_sigma_algebra_def :
   sub_sigma_algebra a b =
      (sigma_algebra a /\ sigma_algebra b /\ (space a = space b) /\
       (subsets a) SUBSET (subsets b))
End

(* the set of all filtrations of A *)
Definition filtration_def :
   filtration A (a :num -> 'a algebra) <=>
      (!n. sub_sigma_algebra (a n) A) /\
      (!i j. i <= j ==> subsets (a i) SUBSET subsets (a j))
End

(* NOTE: This is usually denoted by (sp,sts,a,m) in textbooks *)
Definition filtered_measure_space_def :
   filtered_measure_space m a =
      (measure_space m /\ filtration (m_space m,measurable_sets m) a)
End

Definition sigma_finite_filtered_measure_space_def :
   sigma_finite_filtered_measure_space m a =
      (filtered_measure_space m a /\ sigma_finite (m_space m,subsets (a 0),measure m))
End

Definition martingale_def :
   martingale m a u =
     (sigma_finite_filtered_measure_space m a /\ (!n. integrable m (u n)) /\
      !n s. s IN (subsets (a n)) ==>
           (integral m (\x. u (SUC n) x * indicator_fn s x) =
            integral m (\x. u n x * indicator_fn s x)))
End

Definition super_martingale_def :
   super_martingale m a u =
     (sigma_finite_filtered_measure_space m a /\ (!n. integrable m (u n)) /\
      !n s. s IN (subsets (a n)) ==>
           (integral m (\x. u (SUC n) x * indicator_fn s x) <=
            integral m (\x. u n x * indicator_fn s x)))
End

Definition sub_martingale_def :
   sub_martingale m a u =
     (sigma_finite_filtered_measure_space m a /\ (!n. integrable m (u n)) /\
      !n s. s IN (subsets (a n)) ==>
           (integral m (\x. u n x * indicator_fn s x) <=
            integral m (\x. u (SUC n) x * indicator_fn s x)))
End

(* ------------------------------------------------------------------------- *)
(*   Convergence theorems and their applications [1, Chapter 9 & 12]         *)
(* ------------------------------------------------------------------------- *)

(* Another convergence theorem, usually called Fatou's lemma,
   named after Pierre Fatou (1878-1929), a French mathematician and astronomer.

   This is mainly to prove the validity of the definition of `ext_liminf`. The value
   of any of the integrals may be infinite.

   This is Theorem 9.11 of [1, p.78], a simple version (enough for now).

   cf. integrationTheory.FATOU for the version of Henstock-Kurzweil integrals.
 *)
Theorem fatou_lemma :
    !m f. measure_space m /\ (!x n. x IN m_space m ==> 0 <= f n x) /\
         (!n. f n IN measurable (m_space m,measurable_sets m) Borel) ==>
          pos_fn_integral m (\x. liminf (\n. f n x)) <=
          liminf (\n. pos_fn_integral m (f n))
Proof
    rw [ext_liminf_def]
 >> Know ‘pos_fn_integral m (\x. sup (IMAGE (\m. inf {f n x | m <= n}) UNIV)) =
          sup (IMAGE (\i. pos_fn_integral m (\x. inf {f n x | i <= n})) UNIV)’
 >- (HO_MATCH_MP_TAC lebesgue_monotone_convergence >> rw [] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       MATCH_MP_TAC IN_MEASURABLE_BOREL_INF >> simp [] \\
       qexistsl_tac [‘f’, ‘from i’] >> rw [IN_FROM] >| (* 2 subgoals *)
       [ (* goal 1 (of 2) *)
         rw [Once EXTENSION, IN_FROM] \\
         Q.EXISTS_TAC ‘i’ >> rw [],
         (* goal 1 (of 2) *)
         Suff ‘{f n x | i <= n} = (IMAGE (\n. f n x) (from i))’ >- rw [] \\
         rw [Once EXTENSION, IN_FROM] ],
       (* goal 2 (of 3) *)
       rw [le_inf'] >> METIS_TAC [],
       (* goal 3 (of 3) *)
       rw [ext_mono_increasing_def] \\
       MATCH_MP_TAC inf_mono_subset >> rw [SUBSET_DEF] \\
       Q.EXISTS_TAC ‘n’ >> rw [] ]) >> Rewr'
 >> MATCH_MP_TAC sup_mono >> rw []
 >> rw [le_inf']
 >> MATCH_MP_TAC pos_fn_integral_mono >> rw []
 >| [ (* goal 1 (of 2) *)
      rw [le_inf'] >> rw [],
      (* goal 2 (of 2) *)
      rw [inf_le'] \\
      POP_ASSUM MATCH_MP_TAC \\
      Q.EXISTS_TAC ‘n'’ >> rw [] ]
QED

(* This is also called Reverse Fatou Lemma, c.f. [1, p. 80]

   NOTE: the antecedents are just to make sure that WLLN_IID can be proved.
 *)
Theorem fatou_lemma' :
    !m f w. measure_space m /\ pos_fn_integral m w < PosInf /\
           (!x n. x IN m_space m ==> 0 <= f n x /\ f n x <= w x /\ w x < PosInf) /\
           (!n. f n IN measurable (m_space m,measurable_sets m) Borel) ==>
            limsup (\n. pos_fn_integral m (f n)) <=
            pos_fn_integral m (\x. limsup (\n. f n x))
Proof
    rw [ext_limsup_def]
 >> Know ‘pos_fn_integral m (\x. inf (IMAGE (\m. sup {f n x | m <= n}) UNIV)) =
          inf (IMAGE (\i. pos_fn_integral m (\x. sup {f n x | i <= n})) UNIV)’
 >- (HO_MATCH_MP_TAC lebesgue_monotone_convergence_decreasing >> rw [] >| (* 5 subgoals *)
     [ (* goal 1 (of 5) *)
       MATCH_MP_TAC IN_MEASURABLE_BOREL_SUP >> simp [] \\
       qexistsl_tac [‘f’, ‘from i’] >> rw [IN_FROM] >| (* 2 subgoals *)
       [ (* goal 5.1 (of 3) *)
         rw [Once EXTENSION, IN_FROM] \\
         Q.EXISTS_TAC ‘i’ >> rw [],
         (* goal 5.2 (of 3) *)
         Suff ‘{f n x | i <= n} = (IMAGE (\n. f n x) (from i))’ >- rw [] \\
         rw [Once EXTENSION, IN_FROM] ],
       (* goal 2 (of 5) *)
       rw [le_sup'] \\
       MATCH_MP_TAC le_trans >> Q.EXISTS_TAC ‘f i x’ >> rw [] \\
       POP_ASSUM MATCH_MP_TAC \\
       Q.EXISTS_TAC ‘i’ >> rw [],
       (* goal 3 (of 5): sup {f n x | i <= n} < PosInf *)
       MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘w x’ \\
       reverse CONJ_TAC >- rw [GSYM lt_infty] \\
       rw [sup_le'] >> METIS_TAC [],
       (* goal 4 (of 5): pos_fn_integral m (\x. sup {f n x | i <= n}) <> PosInf *)
       REWRITE_TAC [lt_infty] \\
       MATCH_MP_TAC let_trans \\
       Q.EXISTS_TAC ‘pos_fn_integral m w’ >> art [] \\
       MATCH_MP_TAC pos_fn_integral_mono >> rw [] >| (* 2 subgoals *)
       [ (* goal 4.1 (of 2) *)
         rw [le_sup'] \\
         MATCH_MP_TAC le_trans >> Q.EXISTS_TAC ‘f i x’ >> rw [] \\
         POP_ASSUM MATCH_MP_TAC \\
         Q.EXISTS_TAC ‘i’ >> rw [],
         (* goal 4.2 (of 2) *)
         rw [sup_le'] >> METIS_TAC [] ],
       (* goal 5 (of 5) *)
       rw [ext_mono_decreasing_def] \\
       MATCH_MP_TAC sup_mono_subset >> rw [SUBSET_DEF] \\
       Q.EXISTS_TAC ‘n’ >> rw [] ])
 >> Rewr'
 >> MATCH_MP_TAC inf_mono >> rw []
 >> rw [sup_le']
 >> MATCH_MP_TAC pos_fn_integral_mono >> rw []
 >> rw [le_sup']
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘n'’ >> rw []
QED

Theorem LIM_SEQUENTIALLY_real_normal :
    !a l. (!n. a n <> PosInf /\ a n <> NegInf) ==>
          ((real o a --> l) sequentially <=>
           !e. 0 < e ==> ?N. !n. N <= n ==> abs (a n - Normal l) < Normal e)
Proof
    rw [LIM_SEQUENTIALLY, dist, o_DEF]
 >> EQ_TAC
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!e. 0 < e ==> ?N. P’ (MP_TAC o (Q.SPEC ‘e’)) \\
     RW_TAC std_ss [] \\
     Know ‘!n. real (a n) - l = real (a n - Normal l)’
     >- (Q.X_GEN_TAC ‘n’ \\
        ‘?A. a n = Normal A’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [real_normal, extreal_sub_eq]) \\
     DISCH_THEN (FULL_SIMP_TAC std_ss o wrap) \\
     Know ‘!n. abs (real (a n - Normal l)) = real (abs (a n - Normal l))’
     >- (Q.X_GEN_TAC ‘n’ \\
         MATCH_MP_TAC abs_real \\
        ‘?A. a n = Normal A’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_sub_def]) \\
     DISCH_THEN (FULL_SIMP_TAC std_ss o wrap) \\
     POP_ASSUM MP_TAC \\
     ONCE_REWRITE_TAC [GSYM extreal_lt_eq] \\
     Know ‘!n. Normal (real (abs (a n - Normal l))) = abs (a n - Normal l)’
     >- (Q.X_GEN_TAC ‘n’ \\
         MATCH_MP_TAC normal_real \\
        ‘?A. a n = Normal A’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_sub_def, extreal_abs_def]) >> Rewr' \\
     DISCH_TAC \\
     Q.EXISTS_TAC ‘N’ >> rw [])
 >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!e. 0 < e ==> ?N. P’ (MP_TAC o (Q.SPEC ‘e’))
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC ‘N’
 >> rpt STRIP_TAC
 >> Know ‘real (a n) - l = real (a n - Normal l)’
 >- (‘?A. a n = Normal A’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [real_normal, extreal_sub_eq]) >> Rewr'
 >> Know ‘abs (real (a n - Normal l)) = real (abs (a n - Normal l))’
 >- (MATCH_MP_TAC abs_real \\
    ‘?A. a n = Normal A’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def]) >> Rewr'
 >> ONCE_REWRITE_TAC [GSYM extreal_lt_eq]
 >> Know ‘Normal (real (abs (a n - Normal l))) = abs (a n - Normal l)’
 >- (MATCH_MP_TAC normal_real \\
    ‘?A. a n = Normal A’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def, extreal_abs_def]) >> Rewr'
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

(* The limit of the arithmetic means of the first n partial sums is called
  "Cesaro summation". cf. https://en.wikipedia.org/wiki/Cesaro_summation

   This proof uses iterateTheory (numseg), added for WLLN_IID and SLLN_IID.
 *)
Theorem LIM_SEQUENTIALLY_CESARO :
    !(f :num->real) l. ((\n. f n) --> l) sequentially ==>
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
 >> ‘count (SUC n) = (count N) UNION {N .. n}’
      by (rw [Once EXTENSION, numseg, IN_COUNT]) >> POP_ORW
 >> ‘DISJOINT (count N) {N .. n}’
      by (rw [DISJOINT_ALT, IN_COUNT, IN_NUMSEG])
 >> Know ‘SIGMA g ((count N) UNION {N .. n}) = SIGMA g (count N) + SIGMA g {N .. n}’
 >- (MATCH_MP_TAC REAL_SUM_IMAGE_DISJOINT_UNION \\
     rw [FINITE_COUNT, FINITE_NUMSEG]) >> Rewr'
 >> REWRITE_TAC [real_div, REAL_ADD_RDISTRIB]
 (* applying ABS_TRIANGLE *)
 >> MATCH_MP_TAC REAL_LET_TRANS
 >> Q.EXISTS_TAC ‘abs (SIGMA g (count N) * inv (&SUC n)) +
                  abs (SIGMA g {N .. n}  * inv (&SUC n))’
 >> REWRITE_TAC [ABS_TRIANGLE]
 >> Suff ‘abs (SIGMA g (count N) * inv (&SUC n)) < 1 / 2 * e /\
          abs (SIGMA g {N .. n} * inv (&SUC n)) < 1 / 2 * e’
 >- (DISCH_TAC \\
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM X_HALF_HALF] \\
     MATCH_MP_TAC REAL_LT_ADD2 >> art [])
 (* applying REAL_SUM_IMAGE_ABS_TRIANGLE *)
 >> reverse CONJ_TAC
 >- (Know ‘abs (SIGMA g {N .. n} * inv (&SUC n)) =
           abs (SIGMA g {N .. n}) * abs (inv (&SUC n))’
     >- (rw [REAL_ABS_MUL]) >> Rewr' \\
    ‘abs (inv (&SUC n)) = inv (&SUC n) :real’ by rw [] >> POP_ORW \\
     MATCH_MP_TAC REAL_LET_TRANS \\
     Q.EXISTS_TAC ‘SIGMA (abs o g) {N .. n} * inv (&SUC n)’ \\
     CONJ_TAC >- (MATCH_MP_TAC REAL_LE_RMUL_IMP >> rw [] \\
                  MATCH_MP_TAC REAL_SUM_IMAGE_ABS_TRIANGLE \\
                  REWRITE_TAC [FINITE_NUMSEG]) \\
     MATCH_MP_TAC REAL_LET_TRANS \\
     Q.EXISTS_TAC ‘SIGMA (\i. 1 / 2 * e) {N .. n} * inv (&SUC n)’ \\
     CONJ_TAC >- (MATCH_MP_TAC REAL_LE_RMUL_IMP >> rw [] \\
                  irule REAL_SUM_IMAGE_MONO >> rw [FINITE_NUMSEG, IN_NUMSEG, o_DEF] \\
                  MATCH_MP_TAC REAL_LT_IMP_LE >> fs []) \\
    ‘FINITE {N .. n}’ by PROVE_TAC [FINITE_NUMSEG] \\
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

(* Properties A.1 (iv) [1, p.409] *)
Theorem ext_liminf_le_subseq :
    !a f l. (!n. a n <> PosInf /\ a n <> NegInf) /\
            (!m n. m < n ==> f m < f n) /\
            ((real o a o f) --> l) sequentially ==> liminf a <= Normal l
Proof
    rpt STRIP_TAC
 >> POP_ASSUM MP_TAC
 >> Know ‘((real o a o f) --> l) sequentially <=>
          !e. 0 < e ==> ?N. !n. N <= n ==> abs ((a o f) n - Normal l) < Normal e’
 >- (HO_MATCH_MP_TAC LIM_SEQUENTIALLY_real_normal >> rw [])
 >> Rewr'
 >> rw [o_DEF, abs_bounds_lt, ext_liminf_def, sup_le']
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC ‘inf {a (f n) | m <= n}’
 >> CONJ_TAC
 >- (MATCH_MP_TAC inf_mono_subset \\
     rw [SUBSET_DEF] \\
     Q.EXISTS_TAC ‘f n’ >> rw [] \\
     MATCH_MP_TAC LESS_EQ_TRANS \\
     Q.EXISTS_TAC ‘n’ >> rw [] \\
     MATCH_MP_TAC MONOTONE_BIGGER >> rw [])
 >> rw [inf_le']
 >> MATCH_MP_TAC le_epsilon
 >> rpt STRIP_TAC
 >> ‘e <> NegInf’ by METIS_TAC [lt_imp_le, pos_not_neginf]
 >> ‘?E. 0 < E /\ e = Normal E’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq]
 >> POP_ORW
 >> Q.PAT_X_ASSUM ‘e <> PosInf’ K_TAC
 >> Q.PAT_X_ASSUM ‘e <> NegInf’ K_TAC
 >> Q.PAT_X_ASSUM ‘0 < e’       K_TAC
 >> Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘E’))
 >> RW_TAC std_ss []
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘N + m’))
 >> RW_TAC arith_ss []
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC ‘a (f (N + m))’
 >> CONJ_TAC
 >- (FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘N + m’ >> rw [])
 >> MATCH_MP_TAC lt_imp_le
 >> ONCE_REWRITE_TAC [add_comm_normal]
 >> Suff ‘a (f (N + m)) < Normal E + Normal l <=>
          a (f (N + m)) - Normal l < Normal E’ >- rw []
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> MATCH_MP_TAC sub_lt_eq >> rw []
QED

(* Properties A.1 (iv) [1, p.409] (dual of previous lemma) *)
Theorem ext_limsup_le_subseq :
    !a f l. (!n. a n <> PosInf /\ a n <> NegInf) /\
            (!m n. m < n ==> f m < f n) /\
            ((real o a o f) --> l) sequentially ==> Normal l <= limsup a
Proof
    rw [ext_limsup_alt_liminf]
 >> ‘Normal l = -Normal (-l)’ by rw [extreal_ainv_def] >> POP_ORW
 >> rw [le_neg]
 >> MATCH_MP_TAC ext_liminf_le_subseq
 >> Q.EXISTS_TAC ‘f’ >> rw []
 >| [ (* goal 1 (of 3) *)
     ‘?r. a n = Normal r’ by METIS_TAC [extreal_cases] >> rw [extreal_ainv_def],
      (* goal 2 (of 3) *)
     ‘?r. a n = Normal r’ by METIS_TAC [extreal_cases] >> rw [extreal_ainv_def],
      (* goal 3 (of 3) *)
      Suff ‘real o numeric_negate o a o f = (\n. -(real o a o f) n)’
      >- (Rewr' >> MATCH_MP_TAC LIM_NEG >> art []) \\
      rw [o_DEF, FUN_EQ_THM] \\
      ‘?r. a (f n) = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
      ASM_SIMP_TAC std_ss [GSYM extreal_11, GSYM extreal_ainv_def] \\
      Know ‘Normal (real (-Normal r)) = -Normal r’
      >- (MATCH_MP_TAC normal_real \\
          SIMP_TAC std_ss [extreal_ainv_def, extreal_not_infty]) >> Rewr' \\
      Know ‘Normal (real (Normal r)) = Normal r’
      >- (MATCH_MP_TAC normal_real >> rw []) >> Rewr' \\
      rw [extreal_ainv_def] ]
QED

(* Properties A.1 (iv) [1, p.409] (construction of subsequence with liminf as the limit) *)
Theorem ext_liminf_imp_subseq :
    !a. (!n. a n <> PosInf /\ a n <> NegInf) /\
        liminf a <> PosInf /\ liminf a <> NegInf ==>
        ?f. (!m n. m < n ==> f m < f n) /\
            ((real o a o f) --> real (liminf a)) sequentially
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘L = liminf a’
 >> Know ‘!k. inf {a n | k <= n} <= L’
 >- (rw [Abbr ‘L’, ext_liminf_def] \\
     MATCH_MP_TAC le_sup_imp' >> rw [] \\
     Q.EXISTS_TAC ‘k’ >> rw [])
 >> DISCH_TAC
 >> Know ‘!k. inf {a n | k <= n} <> PosInf’
 >- (rw [lt_infty] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘L’ >> art [] \\
    ‘?r. L = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [lt_infty])
 >> DISCH_TAC
 (* it's impossible that ‘inf {a n | k <= n}’ (increasing) is always NegInf *)
 >> Cases_on ‘!Z. inf {a n | Z <= n} = NegInf’
 >- (Suff ‘L = NegInf’ >- PROVE_TAC [] \\
     SIMP_TAC std_ss [Abbr ‘L’, ext_liminf_def] >> POP_ORW \\
     Know ‘IMAGE (\m. NegInf) univ(:num) = (\y. y = NegInf)’
     >- (rw [Once EXTENSION]) >> Rewr' \\
     rw [sup_const])
 >> FULL_SIMP_TAC bool_ss [] (* this asserts ‘Z’ *)
 >> Know ‘!k. Z <= k ==> inf {a n | k <= n} <> NegInf’
 >- (rw [lt_infty] \\
     MATCH_MP_TAC lte_trans \\
     Q.EXISTS_TAC ‘inf {a n | Z <= n}’ \\
     reverse CONJ_TAC >- (MATCH_MP_TAC inf_mono_subset >> rw [SUBSET_DEF] \\
                          Q.EXISTS_TAC ‘n’ >> rw []) \\
     rw [GSYM lt_infty])
 >> DISCH_TAC
 (* applying sup_lt_epsilon' *)
 >> Know ‘!e. 0 < e ==> ?N. Z <= N /\ !k. N <= k ==> abs (L - inf {a n | k <= n}) < Normal e’
 >- (rpt STRIP_TAC \\
     Q.ABBREV_TAC ‘P = IMAGE (\m. inf {a n | m <= n}) UNIV’ \\
     Know ‘?x. x IN P /\ sup P < x + Normal e’
     >- (MATCH_MP_TAC sup_lt_epsilon' \\
        ‘sup P = L’ by METIS_TAC [ext_liminf_def] >> POP_ORW \\
         rw [extreal_of_num_def, extreal_lt_eq, Abbr ‘P’] \\
         Q.EXISTS_TAC ‘inf {a n | Z <= n}’ >> rw [] \\
         Q.EXISTS_TAC ‘Z’ >> rw []) \\
     rw [Abbr ‘P’, GSYM ext_liminf_def] (* this asserts ‘m’ *) \\
     Q.EXISTS_TAC ‘MAX m Z’ >> rw [] \\
     Know ‘abs (L - inf {a n | k <= n}) = L - inf {a n | k <= n}’
     >- (rw [abs_refl] \\
         Suff ‘0 <= L - inf {a n | k <= n} <=> inf {a n | k <= n} <= L’ >- rw [] \\
         ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC sub_zero_le >> rw []) >> Rewr' \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘L - inf {a n | m <= n}’ \\
     CONJ_TAC >- (MATCH_MP_TAC le_lsub_imp \\
                  MATCH_MP_TAC inf_mono_subset >> rw [SUBSET_DEF] \\
                  Q.EXISTS_TAC ‘n’ >> rw []) \\
     MATCH_MP_TAC sub_lt_imp2 >> rw [add_comm_normal])
 >> DISCH_TAC
 (* applying lt_inf_epsilon' *)
 >> Know ‘!e. 0 < e ==> !k. Z <= k ==> ?l. k <= l /\ abs (a l - inf {a n | k <= n}) < Normal e’
 >- (rpt STRIP_TAC \\
     Q.ABBREV_TAC ‘P = {a n | k <= n}’ \\
     Know ‘?x. x IN P /\ x < inf P + Normal e’
     >- (MATCH_MP_TAC lt_inf_epsilon' \\
         rw [Abbr ‘P’, extreal_of_num_def, extreal_lt_eq] \\
         Q.EXISTS_TAC ‘a k’ >> rw [] \\
         Q.EXISTS_TAC ‘k’ >> rw []) >> rw [Abbr ‘P’] \\
     Q.EXISTS_TAC ‘n’ >> rw [] \\
     Know ‘abs (a n - inf {a n | k <= n}) = a n - inf {a n | k <= n}’
     >- (rw [abs_refl] \\
         Know ‘0 <= a n - inf {a n | k <= n} <=> inf {a n | k <= n} <= a n’
         >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
             MATCH_MP_TAC sub_zero_le >> rw []) >> Rewr' \\
         rw [inf_le'] >> FIRST_X_ASSUM MATCH_MP_TAC \\
         Q.EXISTS_TAC ‘n’ >> rw []) >> Rewr' \\
     MATCH_MP_TAC sub_lt_imp2 >> rw [add_comm_normal])
 >> DISCH_TAC
 (* combine the previous two results, applying abs_triangle_neg

    NOTE: now we go beyond the textbook proofs, to assert a "successor" function f
    which turns a previous (a l) (l starts from 0) to the next (a l'), such that
   ‘abs (a l' - L) < Normal (inv &SUC l)’.

    The resulting subsequence is ‘g = \n. FUNPOW f n 0’.
 *)
 >> Know ‘!l. ?l'. l < l' /\ abs (a l' - L) < Normal (inv (&SUC l))’
 >- (rpt STRIP_TAC \\
     Q.ABBREV_TAC ‘(e :real) = inv (&SUC l)’ \\
     Know ‘0 < e’
     >- (Q.UNABBREV_TAC ‘e’ \\
         MATCH_MP_TAC REAL_INV_POS >> rw []) >> DISCH_TAC \\
    ‘0 < e / 2’ by rw [REAL_LT_DIV] \\
     Q.PAT_X_ASSUM ‘!e. 0 < e ==> ?N. P’ (MP_TAC o (Q.SPEC ‘e / 2’)) \\
     RW_TAC std_ss [] (* this asserts ‘N’ *) \\
     Q.PAT_X_ASSUM ‘!e. 0 < e ==> !k. P’ (MP_TAC o (Q.SPEC ‘e / 2’)) \\
     RW_TAC std_ss [] \\
     Q.PAT_X_ASSUM ‘!k. Z <= k ==> ?l. P’ (MP_TAC o (Q.SPEC ‘MAX N (SUC l)’)) \\
     RW_TAC std_ss [MAX_LE] (* this asserts ‘l'’ *) \\
     Q.EXISTS_TAC ‘l'’ >> rw [] (* l < l' *) \\

     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘abs (a l' - inf {a n | MAX N (SUC l) <= n}) +
                   abs (L    - inf {a n | MAX N (SUC l) <= n})’ \\
     reverse CONJ_TAC
     >- (‘e = e / 2 + e / 2’ by PROVE_TAC [REAL_HALF_DOUBLE] >> POP_ORW \\
         REWRITE_TAC [GSYM extreal_add_def] \\
         MATCH_MP_TAC lt_add2 >> rw []) \\
    ‘?r1. a l' = Normal r1’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?r2. L = Normal r2’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     Know ‘inf {a n | MAX N (SUC l) <= n} <> NegInf’
     >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw []) >> DISCH_TAC \\
    ‘?r3. inf {a n | MAX N (SUC l) <= n} = Normal r3’
       by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def, extreal_abs_def, extreal_add_def, extreal_le_eq] \\
     Suff ‘r1 - r2 = (r1 - r3) - (r2 - r3)’ >- rw [ABS_TRIANGLE_NEG] \\
     REAL_ARITH_TAC)
 >> DISCH_THEN (STRIP_ASSUME_TAC o
                (SIMP_RULE std_ss [SKOLEM_THM])) (* this asserts ‘f’ *)
 >> Q.ABBREV_TAC ‘g = \n. FUNPOW f n 0’
 >> Q.EXISTS_TAC ‘g’
 (* applying STRICTLY_INCREASING_TC (arithmeticTheory) *)
 >> STRONG_CONJ_TAC (* !m n. m < n ==> g m < g n *)
 >- (MATCH_MP_TAC STRICTLY_INCREASING_TC \\
     rw [Abbr ‘g’, FUNPOW_SUC])
 >> DISCH_TAC
 (* applying MONOTONE_BIGGER (real_topologyTheory) *)
 >> Know ‘!n. n <= g n’
 >- (MATCH_MP_TAC MONOTONE_BIGGER >> art [])
 >> DISCH_TAC
 (* stage work, now touching the goal *)
 >> Know ‘(real o a o g --> real L) sequentially <=>
          !e. 0 < e ==> ?N. !n. N <= n ==> abs ((a o g) n - Normal (real L)) < Normal e’
 >- (MATCH_MP_TAC LIM_SEQUENTIALLY_real_normal >> rw []) >> Rewr'
 >> rw [normal_real, o_DEF] (* this asserts ‘e’ *)
 (* find ‘N’ such that ‘&SUC N < 1 / e’ *)
 >> ‘?n. n <> 0 /\ (0 :real) < inv (&n) /\ inv (&n) < (e :real)’ by METIS_TAC [REAL_ARCH_INV]
 (* stage work, the purpose of ‘N’ is to eliminate ‘Normal e’ *)
 >> Q.EXISTS_TAC ‘n’
 >> Q.X_GEN_TAC ‘m’ >> DISCH_TAC (* this asserts ‘m’ (‘n <= m’) *)
 >> ‘m <> 0’ by rw [] >> Cases_on ‘m’ >- fs []
 >> rename1 ‘SUC N <> 0’
 >> FULL_SIMP_TAC std_ss [Abbr ‘g’, FUNPOW_SUC]
 >> MATCH_MP_TAC lt_trans
 >> Q.ABBREV_TAC ‘l = FUNPOW f N 0’
 >> Q.EXISTS_TAC ‘Normal (inv (&SUC l))’
 >> Q.PAT_X_ASSUM ‘!l. l < f l /\ P’ (MP_TAC o (Q.SPEC ‘l’))
 >> RW_TAC std_ss [Abbr ‘l’, extreal_lt_eq]
 >> MATCH_MP_TAC REAL_LET_TRANS
 >> Q.EXISTS_TAC ‘inv (&SUC N)’
 >> CONJ_TAC
 >- (Know ‘inv (&SUC (FUNPOW f N 0)) <= (inv (&SUC N) :real) <=>
           &SUC N <= (&SUC (FUNPOW f N 0)) :real’
     >- (MATCH_MP_TAC REAL_INV_LE_ANTIMONO >> rw []) >> Rewr' \\
     rw [])
 >> MATCH_MP_TAC REAL_LET_TRANS
 >> Q.EXISTS_TAC ‘inv (&n)’ >> art []
 >> Know ‘inv (&SUC N) <= (inv (&n) :real) <=> &n <= (&SUC N :real)’
 >- (MATCH_MP_TAC REAL_INV_LE_ANTIMONO >> rw [])
 >> Rewr'
 >> RW_TAC real_ss []
QED

(* Properties A.1 (iv) [1, p.409] *)
Theorem ext_limsup_imp_subseq :
    !a. (!n. a n <> PosInf /\ a n <> NegInf) /\
        limsup a <> PosInf /\ limsup a <> NegInf ==>
        ?f. (!m n. m < n ==> f m < f n) /\
            ((real o a o f) --> real (limsup a)) sequentially
Proof
    rw [ext_limsup_alt_liminf]
 >> Know ‘liminf (numeric_negate o a) <> PosInf’
 >- (CCONTR_TAC >> fs [extreal_ainv_def])
 >> DISCH_TAC
 >> Know ‘liminf (numeric_negate o a) <> NegInf’
 >- (CCONTR_TAC >> fs [extreal_ainv_def])
 >> DISCH_TAC
 >> Know ‘real (-liminf (numeric_negate o a)) = -real (liminf (numeric_negate o a))’
 >- (REWRITE_TAC [GSYM extreal_11, GSYM extreal_ainv_def] \\
     rw [normal_real])
 >> Rewr'
 >> Know ‘?f. (!m n. m < n ==> f m < f n) /\
              (real o (numeric_negate o a) o f --> real (liminf (numeric_negate o a))) sequentially’
 >- (MATCH_MP_TAC ext_liminf_imp_subseq >> rw [o_DEF] \\
    ‘?r. a n = Normal r’ by METIS_TAC [extreal_cases] >> rw [extreal_ainv_def])
 >> STRIP_TAC
 >> Q.EXISTS_TAC ‘f’ >> art []
 >> Q.ABBREV_TAC ‘l = real (liminf (numeric_negate o a))’
 >> Q.ABBREV_TAC ‘g = real o (numeric_negate o a) o f’
 >> Suff ‘real o a o f = \n. -g n’
 >- (Rewr' >> MATCH_MP_TAC LIM_NEG >> art [])
 >> rw [o_DEF, Abbr ‘g’, FUN_EQ_THM]
 >> REWRITE_TAC [GSYM extreal_11, GSYM extreal_ainv_def]
 >> Know ‘-a (f n) <> PosInf /\ -a (f n) <> NegInf’
 >- (‘?r. a (f n) = Normal r’ by METIS_TAC [extreal_cases] \\
     rw [extreal_ainv_def])
 >> STRIP_TAC
 >> rw [normal_real]
QED

(* Properties A.1 (v) [1, p.409] (full version) *)
Theorem ext_limsup_thm :
    !a l. (!n. a n <> PosInf /\ a n <> NegInf) ==>
          ((real o a --> l) sequentially <=>
           limsup a = Normal l /\ liminf a = Normal l)
Proof
    rpt STRIP_TAC
 >> EQ_TAC (* easy part first *)
 >- (DISCH_TAC \\
     MP_TAC (Q.SPECL [‘a’, ‘I’, ‘l’] ext_limsup_le_subseq) \\
     MP_TAC (Q.SPECL [‘a’, ‘I’, ‘l’] ext_liminf_le_subseq) \\
     RW_TAC arith_ss [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Know ‘limsup a <> NegInf’
       >- (fs [lt_infty] >> MATCH_MP_TAC lte_trans \\
           Q.EXISTS_TAC ‘Normal l’ >> rw [lt_infty]) >> DISCH_TAC \\
       (* ‘(real o a --> l) sequentially’ cannot hold if limsup a = PosInf *)
       Know ‘limsup a <> PosInf’
       >- (rw [ext_limsup_def] \\
           CCONTR_TAC >> fs [] \\
          ‘!e. 0 < e ==> ?N. !n. N <= n ==> abs (a n - Normal l) < Normal e’
             by METIS_TAC [LIM_SEQUENTIALLY_real_normal] \\
           Q.ABBREV_TAC ‘P = IMAGE (\m. sup {a n | m <= n}) UNIV’ \\
           Suff ‘?x. x IN P /\ x < PosInf’
           >- (DISCH_TAC >> fs [Abbr ‘P’] \\
               Know ‘inf (IMAGE (\m. sup {a n | m <= n}) UNIV) < PosInf’
               >- (rw [GSYM inf_lt'] \\
                   Q.EXISTS_TAC ‘sup {a n | m <= n}’ >> rw [] \\
                   Q.EXISTS_TAC ‘m’ >> rw []) \\
               rw [lt_infty]) \\
           rw [Abbr ‘P’] \\
           POP_ASSUM (MP_TAC o (Q.SPEC ‘1’)) >> rw [abs_bounds_lt] \\
           Q.EXISTS_TAC ‘sup {a n | N <= n}’ \\
           CONJ_TAC >- (Q.EXISTS_TAC ‘N’ >> rw []) \\
           MATCH_MP_TAC let_trans \\
           Q.EXISTS_TAC ‘Normal (1 + l)’ >> rw [lt_infty, sup_le'] \\
           rw [GSYM extreal_add_def] \\
           MATCH_MP_TAC lt_imp_le \\
           Know ‘a n < Normal 1 + Normal l <=> a n - Normal l < Normal 1’
           >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
               MATCH_MP_TAC sub_lt_eq >> rw []) >> Rewr' \\
           METIS_TAC []) >> DISCH_TAC \\
       Know ‘?f. (!m n. m < n ==> f m < f n) /\
                 (real o a o f --> real (limsup a)) sequentially’
       >- (MATCH_MP_TAC ext_limsup_imp_subseq >> art []) >> STRIP_TAC \\
       Know ‘(real o a o f --> l) sequentially’
       >- (REWRITE_TAC [o_ASSOC] \\
           MATCH_MP_TAC LIM_SUBSEQUENCE >> art []) >> DISCH_TAC \\
       Know ‘real (limsup a) = l’
       >- (METIS_TAC [LIM_UNIQUE, TRIVIAL_LIMIT_SEQUENTIALLY]) \\
       REWRITE_TAC [GSYM extreal_11] \\
       ASM_SIMP_TAC std_ss [normal_real],
       (* goal 2 (of 2) *)
       Know ‘liminf a <> PosInf’
       >- (fs [lt_infty] >> MATCH_MP_TAC let_trans \\
           Q.EXISTS_TAC ‘Normal l’ >> rw [lt_infty]) >> DISCH_TAC \\
       (* if liminf a = NegInf, ‘(real o a --> l) sequentially’ cannot hold *)
       Know ‘liminf a <> NegInf’
       >- (rw [ext_liminf_def] \\
           CCONTR_TAC >> fs [] \\
          ‘!e. 0 < e ==> ?N. !n. N <= n ==> abs (a n - Normal l) < Normal e’
             by METIS_TAC [LIM_SEQUENTIALLY_real_normal] \\
           Q.ABBREV_TAC ‘P = IMAGE (\m. inf {a n | m <= n}) UNIV’ \\
           Suff ‘?x. x IN P /\ NegInf < x’
           >- (DISCH_TAC >> fs [Abbr ‘P’] \\
               Know ‘NegInf < sup (IMAGE (\m. inf {a n | m <= n}) UNIV)’
               >- (rw [lt_sup] \\
                   Q.EXISTS_TAC ‘inf {a n | m <= n}’ >> rw [] \\
                   Q.EXISTS_TAC ‘m’ >> rw []) \\
               rw [lt_infty]) \\
           rw [Abbr ‘P’] \\
           POP_ASSUM (MP_TAC o (Q.SPEC ‘1’)) >> rw [abs_bounds_lt] \\
           Q.EXISTS_TAC ‘inf {a n | N <= n}’ \\
           CONJ_TAC >- (Q.EXISTS_TAC ‘N’ >> rw []) \\
           MATCH_MP_TAC lte_trans \\
           Q.EXISTS_TAC ‘Normal (-1 + l)’ >> rw [lt_infty, le_inf'] \\
           rw [GSYM extreal_add_def, GSYM extreal_ainv_def] \\
           MATCH_MP_TAC lt_imp_le \\
           Know ‘-Normal 1 + Normal l < a n <=> -Normal 1 < a n - Normal l’
           >- (MATCH_MP_TAC lt_sub >> rw [extreal_ainv_def]) >> Rewr' \\
           METIS_TAC []) >> DISCH_TAC \\
       Know ‘?f. (!m n. m < n ==> f m < f n) /\
                 (real o a o f --> real (liminf a)) sequentially’
       >- (MATCH_MP_TAC ext_liminf_imp_subseq >> art []) >> STRIP_TAC \\
       Know ‘(real o a o f --> l) sequentially’
       >- (REWRITE_TAC [o_ASSOC] \\
           MATCH_MP_TAC LIM_SUBSEQUENCE >> art []) >> DISCH_TAC \\
    (* applying LIM_UNIQUE *)
       Know ‘real (liminf a) = l’
       >- (METIS_TAC [LIM_UNIQUE, TRIVIAL_LIMIT_SEQUENTIALLY]) \\
       REWRITE_TAC [GSYM extreal_11] \\
       ASM_SIMP_TAC std_ss [normal_real] ])
 (* stage work, now the hard part *)
 >> STRIP_TAC
 (* eventually ‘inf {a n | k <= n}’ (increasing) is normal *)
 >> Cases_on ‘!N1. inf {a n | N1 <= n} = NegInf’
 >- (Suff ‘liminf a = NegInf’ >- fs [] \\
     SIMP_TAC std_ss [ext_liminf_def] >> POP_ORW \\
     Know ‘IMAGE (\m. NegInf) univ(:num) = (\y. y = NegInf)’
     >- (rw [Once EXTENSION]) >> Rewr' \\
     rw [sup_const])
 (* eventually ‘sup {a n | k <= n}’ (decreasing) is normal *)
 >> Cases_on ‘!N2. sup {a n | N2 <= n} = PosInf’
 >- (Suff ‘limsup a = PosInf’ >- fs [] \\
     SIMP_TAC std_ss [ext_limsup_def] >> POP_ORW \\
     Know ‘IMAGE (\m. PosInf) univ(:num) = (\y. y = PosInf)’
     >- (rw [Once EXTENSION]) >> Rewr' \\
     rw [inf_const])
 >> FULL_SIMP_TAC bool_ss [] (* this asserts N1 and N2 *)
 >> Know ‘!k. N1 <= k ==> inf {a n | k <= n} <> NegInf’
 >- (rw [lt_infty] >> MATCH_MP_TAC lte_trans \\
     Q.EXISTS_TAC ‘inf {a n | N1 <= n}’ \\
     CONJ_TAC >- rw [GSYM lt_infty] \\
     MATCH_MP_TAC inf_mono_subset >> rw [SUBSET_DEF] \\
     Q.EXISTS_TAC ‘n’ >> rw [])
 >> DISCH_TAC
 >> Know ‘!k. N2 <= k ==> sup {a n | k <= n} <> PosInf’
 >- (rw [lt_infty] >> MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘sup {a n | N2 <= n}’ \\
     reverse CONJ_TAC >- rw [GSYM lt_infty] \\
     MATCH_MP_TAC sup_mono_subset >> rw [SUBSET_DEF] \\
     Q.EXISTS_TAC ‘n’ >> rw [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘inf {a n | N1 <= n} <> NegInf’ K_TAC
 >> Q.PAT_X_ASSUM ‘sup {a n | N2 <= n} <> PosInf’ K_TAC
 (* stage work *)
 >> Know ‘!k. 0 <= a k - inf {a n | k <= n}’
 >- (Q.X_GEN_TAC ‘k’ \\
     MATCH_MP_TAC le_sub_imp2 >> rw [inf_le'] \\
     POP_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘k’ >> rw [])
 >> DISCH_TAC
 >> Know ‘!k. inf {a n | k <= n} <> PosInf’
 >- (Q.X_GEN_TAC ‘k’ \\
     SPOSE_NOT_THEN (ASSUME_TAC o (SIMP_RULE std_ss [])) \\
     Q.PAT_X_ASSUM ‘!k. 0 <= a k - inf {a n | k <= n}’ (MP_TAC o (Q.SPEC ‘k’)) \\
    ‘?r. a k = Normal r’ by METIS_TAC [extreal_cases] >> art [] \\
     simp [extreal_sub_def, GSYM extreal_lt_def, lt_infty, extreal_of_num_def])
 >> DISCH_TAC
 >> Know ‘!k. sup {a n | k <= n} <> NegInf’
 >- (rw [lt_infty] \\
     MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC ‘a k’ \\
     CONJ_TAC >- (‘?r. a k = Normal r’ by METIS_TAC [extreal_cases] \\
                  rw [GSYM lt_infty]) \\
     rw [le_sup'] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘k’ >> rw [])
 >> DISCH_TAC
 >> Know ‘!k. a k - inf {a n | k <= n} <= sup {a n | k <= n} - inf {a n | k <= n}’
 >- (Q.X_GEN_TAC ‘k’ \\
     MATCH_MP_TAC le_rsub_imp >> rw [le_sup'] \\
     POP_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘k’ >> rw [])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘P = \(k :num). sup {a n | k <= n} - inf {a n | k <= n}’
 >> Know ‘!k. 0 <= P k’
 >- (rw [Abbr ‘P’] \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC ‘a k - inf {a n | k <= n}’ >> rw [])
 >> DISCH_TAC
 (* applying lt_inf_epsilon' on liminf a *)
 >> Q.ABBREV_TAC ‘Q = IMAGE (\m. inf {a n | m <= n}) UNIV’
 >> ‘sup Q = liminf a’ by METIS_TAC [ext_liminf_def]
 >> Know ‘!z. 0 < z ==> ?x. x IN Q /\ sup Q < x + z’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC sup_lt_epsilon' >> rw [Abbr ‘Q’] \\
     Q.EXISTS_TAC ‘inf {a n | N1 <= n}’ >> rw [] \\
     Q.EXISTS_TAC ‘N1’ >> rw [])
 >> POP_ORW >> rw [Abbr ‘Q’]
 (* applying sup_lt_epsilon' on limsup a *)
 >> Q.ABBREV_TAC ‘Q = IMAGE (\m. sup {a n | m <= n}) UNIV’
 >> ‘inf Q = limsup a’ by METIS_TAC [ext_limsup_def]
 >> Know ‘!z. 0 < z ==> ?x. x IN Q /\ x < inf Q + z’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC lt_inf_epsilon' >> rw [Abbr ‘Q’] \\
     Q.EXISTS_TAC ‘sup {a n | N2 <= n}’ >> rw [] \\
     Q.EXISTS_TAC ‘N2’ >> rw [])
 >> POP_ORW >> rw [Abbr ‘Q’]
 (* This is stronger than ‘inf (IMAGE P UNIV) = 0’ *)
 >> Know ‘(real o P --> 0) sequentially’
 >- (rw [LIM_SEQUENTIALLY, o_DEF, dist] \\
    ‘0 < e / 2’ by rw [] \\
     NTAC 2 (Q.PAT_X_ASSUM ‘!z. 0 < z ==> ?x. R’ (MP_TAC o (Q.SPEC ‘Normal (e / 2)’))) \\
     rw [extreal_of_num_def, extreal_lt_eq] (* this asserts ‘m’ and ‘m'’ *) \\
     fs [Abbr ‘P’] \\
     Q.EXISTS_TAC ‘MAX m m'’ \\
     Q.X_GEN_TAC ‘i’ >> rw [] \\
     Know ‘inf {a n | m <= n} <> NegInf’
     >- (SPOSE_NOT_THEN (ASSUME_TAC o (SIMP_RULE std_ss [])) \\
         Q.PAT_X_ASSUM ‘Normal l < inf {a n | m <= n} + Normal (e / 2)’ MP_TAC \\
         ASM_REWRITE_TAC [extreal_add_def, lt_infty]) >> DISCH_TAC \\
     Know ‘inf {a n | i <= n} <> NegInf’
     >- (REWRITE_TAC [lt_infty] >> MATCH_MP_TAC lte_trans \\
         Q.EXISTS_TAC ‘inf {a n | m <= n}’ >> rw [GSYM lt_infty] \\
         MATCH_MP_TAC inf_mono_subset >> rw [SUBSET_DEF] \\
         Q.EXISTS_TAC ‘n’ >> rw []) >> DISCH_TAC \\
     Know ‘sup {a n | m' <= n} <> PosInf’
     >- (SPOSE_NOT_THEN (ASSUME_TAC o (SIMP_RULE std_ss [])) \\
         Q.PAT_X_ASSUM ‘sup {a n | m' <= n} < Normal l + Normal (e / 2)’ MP_TAC \\
         ASM_REWRITE_TAC [extreal_add_def, lt_infty]) >> DISCH_TAC \\
     Know ‘sup {a n | i <= n} <> PosInf’
     >- (REWRITE_TAC [lt_infty] >> MATCH_MP_TAC let_trans \\
         Q.EXISTS_TAC ‘sup {a n | m' <= n}’ >> rw [GSYM lt_infty] \\
         MATCH_MP_TAC sup_mono_subset >> rw [SUBSET_DEF] \\
         Q.EXISTS_TAC ‘n’ >> rw []) >> DISCH_TAC \\
     Know ‘abs (real (sup {a n | i <= n} - inf {a n | i <= n})) =
                real (sup {a n | i <= n} - inf {a n | i <= n})’
     >- (rw [abs_refl] \\
         RW_TAC std_ss [GSYM extreal_le_eq, GSYM extreal_of_num_def] \\
         Suff ‘Normal (real (sup {a n | i <= n} - inf {a n | i <= n})) =
                             sup {a n | i <= n} - inf {a n | i <= n}’
         >- RW_TAC std_ss [] \\
         MATCH_MP_TAC normal_real \\
        ‘?r. sup {a n | i <= n} = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
        ‘?z. inf {a n | i <= n} = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_sub_def]) >> Rewr' \\
     REWRITE_TAC [GSYM extreal_lt_eq] \\
     Know ‘Normal (real (sup {a n | i <= n} - inf {a n | i <= n})) =
                         sup {a n | i <= n} - inf {a n | i <= n}’
     >- (MATCH_MP_TAC normal_real \\
        ‘?r. sup {a n | i <= n} = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
        ‘?z. inf {a n | i <= n} = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_sub_def]) >> Rewr' \\
    ‘Normal e = Normal (e / 2) + Normal (e / 2)’
       by METIS_TAC [REAL_HALF_DOUBLE, extreal_add_def, extreal_11] >> POP_ORW \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘sup {a n | m' <= n} - inf {a n | i <= n}’ \\
     CONJ_TAC >- (MATCH_MP_TAC le_rsub_imp \\
                  MATCH_MP_TAC sup_mono_subset >> rw [SUBSET_DEF] \\
                  Q.EXISTS_TAC ‘n’ >> rw []) \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘sup {a n | m' <= n} - inf {a n | m <= n}’ \\
     CONJ_TAC >- (MATCH_MP_TAC le_lsub_imp \\
                  MATCH_MP_TAC inf_mono_subset >> rw [SUBSET_DEF] \\
                  Q.EXISTS_TAC ‘n’ >> rw []) \\
     MATCH_MP_TAC lt_trans \\
     Q.EXISTS_TAC ‘Normal l + Normal (e / 2) - inf {a n | m <= n}’ \\
     CONJ_TAC >- (MATCH_MP_TAC lt_rsub_imp >> rw []) \\
     MATCH_MP_TAC sub_lt_imp2 \\
     NTAC 2 (CONJ_TAC >- rw [extreal_add_def]) \\
     Q.ABBREV_TAC ‘E = e / 2’ \\
     Q.PAT_X_ASSUM ‘Normal l < inf {a n | m <= n} + Normal E’ MP_TAC \\
    ‘?r. inf {a n | m <= n} = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     simp [extreal_add_def, extreal_lt_eq] \\
     REAL_ARITH_TAC)
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘Q = \(k :num). a k - inf {a n | k <= n}’
 >> ‘!k. 0 <= Q k /\ Q k <= P k’ by METIS_TAC []
 >> Know ‘(real o Q --> 0) sequentially’
 >- (Q.PAT_X_ASSUM ‘(real o P --> 0) sequentially’ MP_TAC \\
     rw [LIM_SEQUENTIALLY, o_DEF, dist] \\
     Q.PAT_X_ASSUM ‘!e. 0 < e ==> ?N. !n. N <= n ==> abs (real (P n)) < e’
       (MP_TAC o (Q.SPEC ‘e’)) \\
     RW_TAC std_ss [] (* this asserts ‘N’ *) \\
     Q.EXISTS_TAC ‘MAX N (MAX N1 N2)’ \\
     Q.X_GEN_TAC ‘i’ >> rw [] \\
     Know ‘P i <> PosInf /\ P i <> NegInf’
     >- (simp [Abbr ‘P’] \\
        ‘?r. sup {a n | i <= n} = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
        ‘?z. inf {a n | i <= n} = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_sub_def]) >> STRIP_TAC \\
     Know ‘Q i <> PosInf /\ Q i <> NegInf’
     >- (simp [Abbr ‘Q’] \\
        ‘?r. a i = Normal r’                by METIS_TAC [extreal_cases] >> POP_ORW \\
        ‘?z. inf {a n | i <= n} = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_sub_def]) >> STRIP_TAC \\
     Know ‘abs (real (Q i)) = real (Q i)’
     >- (rw [abs_refl] \\
         RW_TAC std_ss [GSYM extreal_le_eq, GSYM extreal_of_num_def] \\
         Suff ‘Normal (real (Q i)) = Q i’ >- RW_TAC std_ss [] \\
         MATCH_MP_TAC normal_real >> rw []) >> Rewr' \\
     Q.PAT_X_ASSUM ‘!n. N <= n ==> abs (real (P n)) < e’
       (fn th => ASSUME_TAC (MATCH_MP th (ASSUME “N <= (i :num)”))) \\
     Know ‘abs (real (P i)) = real (P i)’
     >- (rw [abs_refl] \\
         RW_TAC std_ss [GSYM extreal_le_eq, GSYM extreal_of_num_def] \\
         Suff ‘Normal (real (P i)) = P i’ >- RW_TAC std_ss [] \\
         MATCH_MP_TAC normal_real >> rw []) >> DISCH_THEN (fs o wrap) \\
     MATCH_MP_TAC REAL_LET_TRANS \\
     Q.EXISTS_TAC ‘real (P i)’ >> art [] \\
     REWRITE_TAC [GSYM extreal_le_eq] \\
     RW_TAC std_ss [normal_real])
 >> DISCH_TAC
 (* final stage *)
 >> rw [LIM_SEQUENTIALLY_real_normal]
 >> ‘0 < e / 2’ by rw []
 >> Q.PAT_X_ASSUM ‘(real o Q --> 0) sequentially’ MP_TAC
 >> rw [LIM_SEQUENTIALLY, dist]
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘e / 2’))
 >> RW_TAC std_ss [] (* this asserts ‘N’ *)
 >> FULL_SIMP_TAC std_ss [Abbr ‘Q’]
 >> Q.PAT_X_ASSUM ‘!z. 0 < z ==> ?x. _ /\ Normal l < x + z’
      (MP_TAC o (Q.SPEC ‘Normal (e / 2)’))
 >> rw [extreal_of_num_def, extreal_lt_eq] (* this asserts ‘m’ *)
 >> Q.EXISTS_TAC ‘MAX (MAX N1 N) m’
 >> Q.X_GEN_TAC ‘i’ >> rw []
 >> Know ‘a i - Normal l = (a i - inf {a n | i <= n}) + (inf {a n | i <= n} - Normal l)’
 >- (‘?r. a i = Normal r’                by METIS_TAC [extreal_cases] >> POP_ORW \\
     ‘?z. inf {a n | i <= n} = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_add_def, extreal_sub_def] >> REAL_ARITH_TAC)
 >> Rewr'
 (* applying abs_triangle *)
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC ‘abs (a i - inf {a n | i <= n}) + abs (inf {a n | i <= n} - Normal l)’
 >> CONJ_TAC
 >- (MATCH_MP_TAC abs_triangle \\
    ‘?r. a i = Normal r’                by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?z. inf {a n | i <= n} = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def])
 >> ‘Normal e = Normal (e / 2) + Normal (e / 2)’
       by METIS_TAC [REAL_HALF_DOUBLE, extreal_add_def, extreal_11] >> POP_ORW
 >> MATCH_MP_TAC lt_add2
 >> CONJ_TAC
 >| [ (* goal 1 (of 2) *)
     ‘abs (a i - inf {a n | i <= n}) = a i - inf {a n | i <= n}’
        by (rw [abs_refl]) >> POP_ORW \\
      Q.PAT_X_ASSUM ‘!n. N <= n ==> _ < e / 2’ (MP_TAC o (Q.SPEC ‘i’)) \\
      RW_TAC std_ss [] \\
     ‘?r. a i = Normal r’                by METIS_TAC [extreal_cases] \\
      POP_ASSUM (FULL_SIMP_TAC std_ss o wrap) \\
     ‘?z. inf {a n | i <= n} = Normal z’ by METIS_TAC [extreal_cases] \\
      POP_ASSUM (FULL_SIMP_TAC std_ss o wrap) \\
      FULL_SIMP_TAC std_ss [extreal_sub_def, real_normal, extreal_lt_eq] \\
      FULL_SIMP_TAC std_ss [ABS_BOUNDS_LT],
      (* goal 2 (of 2) *)
      Know ‘abs (inf {a n | i <= n} - Normal l) = -(inf {a n | i <= n} - Normal l)’
      >- (MATCH_MP_TAC abs_neg' \\
          Know ‘inf {a n | i <= n} - Normal l <= 0 <=> inf {a n | i <= n} <= Normal l’
          >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
              MATCH_MP_TAC sub_le_zero >> rw []) >> Rewr' \\
          Q.PAT_X_ASSUM ‘liminf a = Normal l’ (ONCE_REWRITE_TAC o wrap o SYM) \\
          rw [ext_liminf_def, le_sup'] \\
          POP_ASSUM MATCH_MP_TAC \\
          Q.EXISTS_TAC ‘i’ >> rw []) >> Rewr' \\
      Know ‘-(inf {a n | i <= n} - Normal l) = Normal l - inf {a n | i <= n}’
      >- (MATCH_MP_TAC neg_sub \\
          DISJ2_TAC >> rw []) >> Rewr' \\
      MATCH_MP_TAC sub_lt_imp2 >> rw [] \\
      MATCH_MP_TAC lte_trans \\
      Q.EXISTS_TAC ‘inf {a n | m <= n} + Normal (e / 2)’ >> rw [add_comm_normal] \\
      MATCH_MP_TAC le_radd_imp \\
      MATCH_MP_TAC inf_mono_subset >> rw [SUBSET_DEF] \\
      Q.EXISTS_TAC ‘n’ >> rw [] ]
QED

(* Properties A.1 (v) [1, p.409] (a simple version for non-negative sequences) *)
Theorem ext_limsup_thm'[local] :
    !a. (!n. 0 <= a n /\ a n <> PosInf) ==>
        (((\n. real (a n)) --> 0) sequentially <=> limsup a = 0 /\ liminf a = 0)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC (REWRITE_RULE [o_DEF, GSYM extreal_of_num_def]
                               (Q.SPECL [‘a’, ‘0’] ext_limsup_thm))
 >> rw []
 >> MATCH_MP_TAC pos_not_neginf >> rw []
QED

(* Theorem 12.2 of [1, p.97], in slightly simplified form

   NOTE: ‘integrable m f’ can be moved to conclusions, but the current form is
          enough for WLLN_IID (directly used by truncated_vars_expectation).
 *)
Theorem lebesgue_dominated_convergence :
    !m f fi. measure_space m /\ (!i. integrable m (fi i)) /\ integrable m f /\
            (!i x. x IN m_space m ==> fi i x <> PosInf /\ fi i x <> NegInf) /\
            (!x. x IN m_space m ==> f x <> PosInf /\ f x <> NegInf) /\
            (!x. x IN m_space m ==>
                ((\i. real (fi i x)) --> real (f x)) sequentially) /\
            (?w. integrable m w /\
                (!x. x IN m_space m ==> 0 <= w x /\ w x <> PosInf) /\
                 !i x. x IN m_space m ==> abs (fi i x) <= w x)
        ==> ((\i. real (integral m (fi i))) --> real (integral m f)) sequentially
Proof
    rpt STRIP_TAC
 >> Suff ‘((\i. real (integral m (\x. abs (fi i x - f x)))) --> 0) sequentially’
 >- (rw [LIM_SEQUENTIALLY, dist] \\
     Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘e’)) \\
     RW_TAC std_ss [] \\
     Q.EXISTS_TAC ‘N’ >> rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!i. N <= i ==> P’ (MP_TAC o (Q.SPEC ‘i’)) \\
     RW_TAC std_ss [] \\
     Know ‘integrable m (\x. fi i x - f x)’
     >- (MATCH_MP_TAC integrable_sub >> rw []) >> DISCH_TAC \\
     Know ‘integrable m (\x. abs (fi i x - f x))’
     >- (HO_MATCH_MP_TAC (REWRITE_RULE [o_DEF] integrable_abs) >> art []) \\
     DISCH_TAC \\
     Know ‘abs (real (integral m (\x. abs (fi i x - f x)))) =
           real (abs (integral m (\x. abs (fi i x - f x))))’
     >- (MATCH_MP_TAC abs_real >> METIS_TAC [integrable_finite_integral]) \\
     DISCH_THEN (FULL_SIMP_TAC std_ss o wrap) \\
     Know ‘real (abs (integral m (\x. abs (fi i x - f x)))) < e <=>
           Normal (real (abs (integral m (\x. abs (fi i x - f x))))) < Normal e’
     >- rw [extreal_lt_eq] \\
     Know ‘Normal (real (abs (integral m (\x. abs (fi i x - f x))))) =
                        (abs (integral m (\x. abs (fi i x - f x))))’
     >- (MATCH_MP_TAC normal_real \\
        ‘?r. integral m (\x. abs (fi i x - f x)) = Normal r’
            by METIS_TAC [extreal_cases, integrable_finite_integral] >> POP_ORW \\
         rw [extreal_abs_def, extreal_not_infty]) >> Rewr' \\
     DISCH_THEN (FULL_SIMP_TAC std_ss o wrap) \\
     Know ‘abs (integral m (\x. abs (fi i x - f x))) =
                integral m (\x. abs (fi i x - f x))’
     >- (REWRITE_TAC [abs_refl] \\
         MATCH_MP_TAC integral_pos >> rw [abs_pos]) \\
     DISCH_THEN (FULL_SIMP_TAC std_ss o wrap) \\
     Know ‘real (integral m (fi i)) - real (integral m f) =
           real (integral m (fi i) - integral m f)’
     >- (‘?a. integral m (fi i) = Normal a’
            by METIS_TAC [extreal_cases, integrable_finite_integral] >> POP_ORW \\
         ‘?b. integral m f = Normal b’
            by METIS_TAC [extreal_cases, integrable_finite_integral] >> POP_ORW \\
         rw [extreal_sub_def, real_normal]) >> Rewr' \\
     Know ‘abs (real (integral m (fi i) - integral m f)) =
           real (abs (integral m (fi i) - integral m f))’
     >- (MATCH_MP_TAC abs_real \\
         ‘?a. integral m (fi i) = Normal a’
            by METIS_TAC [extreal_cases, integrable_finite_integral] >> POP_ORW \\
         ‘?b. integral m f = Normal b’
            by METIS_TAC [extreal_cases, integrable_finite_integral] >> POP_ORW \\
         rw [extreal_sub_def, extreal_not_infty]) >> Rewr' \\
     ONCE_REWRITE_TAC [GSYM extreal_lt_eq] \\
     Know ‘Normal (real (abs (integral m (fi i) - integral m f))) =
                         abs (integral m (fi i) - integral m f)’
     >- (MATCH_MP_TAC normal_real \\
         ‘?a. integral m (fi i) = Normal a’
            by METIS_TAC [extreal_cases, integrable_finite_integral] >> POP_ORW \\
         ‘?b. integral m f = Normal b’
            by METIS_TAC [extreal_cases, integrable_finite_integral] >> POP_ORW \\
         rw [extreal_abs_def, extreal_sub_def, extreal_not_infty]) >> Rewr' \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘integral m (\x. abs (fi i x - f x))’ >> art [] \\
     Know ‘integral m (fi i) - integral m f = integral m (\x. fi i x - f x)’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC integral_sub >> rw []) >> Rewr' \\
     HO_MATCH_MP_TAC (REWRITE_RULE [o_DEF] integral_triangle_ineq) >> art [])
 (* stage work, renamed ‘fi’ to ‘u’ *)
 >> rename1 ‘!i. integrable m (u i)’
 (* simplify ‘((\i. real (u i x)) --> real (f x)) sequentially’ *)
 >> Know ‘!x. x IN m_space m ==>
              !e. 0 < e ==> ?N. !i. N <= i ==> abs (u i x - f x) < Normal e’
 >- (RW_TAC std_ss [] \\
     Q.PAT_X_ASSUM ‘!x. x IN m_space m ==>
                        ((\i. real (u i x)) --> real (f x)) sequentially’ MP_TAC \\
     rw [LIM_SEQUENTIALLY, dist] \\
     Q.PAT_X_ASSUM ‘!x. x IN m_space m ==> !e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘x’)) \\
     RW_TAC std_ss [] \\
     Q.PAT_X_ASSUM ‘!e. 0 < e ==> ?N. P’ (MP_TAC o (Q.SPEC ‘e’)) \\
     RW_TAC std_ss [] \\
     Know ‘!i. real (u i x) - real (f x) = real (u i x - f x)’
     >- (Q.X_GEN_TAC ‘i’ \\
        ‘?a. u i x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
        ‘?b. f x   = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [real_normal, extreal_sub_eq]) \\
     DISCH_THEN (FULL_SIMP_TAC std_ss o wrap) \\
     Know ‘!i. abs (real (u i x - f x)) = real (abs (u i x - f x))’
     >- (Q.X_GEN_TAC ‘i’ \\
         MATCH_MP_TAC abs_real \\
        ‘?a. u i x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
        ‘?b. f x   = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_sub_def]) \\
     DISCH_THEN (FULL_SIMP_TAC std_ss o wrap) \\
     POP_ASSUM MP_TAC >> ONCE_REWRITE_TAC [GSYM extreal_lt_eq] \\
     Know ‘!i. Normal (real (abs (u i x - f x))) = abs (u i x - f x)’
     >- (Q.X_GEN_TAC ‘i’ \\
         MATCH_MP_TAC normal_real \\
        ‘?a. u i x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
        ‘?b. f x   = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_sub_def, extreal_abs_def]) >> Rewr' \\
     DISCH_TAC \\
     Q.EXISTS_TAC ‘N’ >> rw [])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘a = \i x. abs (u i x - f x)’
 >> Know ‘!x. x IN m_space m ==> ((\i. real (a i x)) --> 0) sequentially’
 >- (rw [Abbr ‘a’, LIM_SEQUENTIALLY, dist] \\
     Q.PAT_X_ASSUM ‘!x. x IN m_space m ==> !e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘x’)) \\
     RW_TAC std_ss [] \\
     Q.PAT_X_ASSUM ‘!e. 0 < e ==> ?N. P’ (MP_TAC o (Q.SPEC ‘e’)) \\
     RW_TAC std_ss [] \\
     Q.EXISTS_TAC ‘N’ >> rpt STRIP_TAC \\
     Know ‘abs (real (abs (u i x - f x))) =
           real (abs (abs (u i x - f x)))’
     >- (MATCH_MP_TAC abs_real \\
        ‘?a. u i x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
        ‘?b. f x   = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_sub_def, extreal_abs_def]) >> Rewr' \\
     RW_TAC std_ss [abs_abs, GSYM extreal_lt_eq] \\
     Suff ‘Normal (real (abs (u i x - f x))) = abs (u i x - f x)’ >- RW_TAC std_ss [] \\
     MATCH_MP_TAC normal_real \\
    ‘?a. u i x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?b. f x   = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_sub_def, extreal_abs_def])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘b = \i. integral m (a i)’
 >> Know ‘!n. integrable m (a n)’
 >- (rw [Abbr ‘a’] \\
     HO_MATCH_MP_TAC (REWRITE_RULE [o_DEF] integrable_abs) >> art [] \\
     MATCH_MP_TAC integrable_sub >> rw [])
 >> DISCH_TAC
 >> ‘!i. integral m (\x. abs (u i x - f x)) = b i’ by rw [Abbr ‘a’, Abbr ‘b’] >> POP_ORW
 (* applying ext_limsup_thm' *)
 >> Know ‘!n. 0 <= b n /\ b n <> PosInf’
 >- (Q.X_GEN_TAC ‘n’ >> SIMP_TAC std_ss [Abbr ‘b’] \\
     reverse CONJ_TAC >- METIS_TAC [integrable_finite_integral] \\
     MATCH_MP_TAC integral_pos >> rw [Abbr ‘a’, abs_pos])
 >> DISCH_THEN
     (ONCE_REWRITE_TAC o wrap o (MATCH_MP ext_limsup_thm'))
 >> Q.UNABBREV_TAC ‘b’
 (* applying ext_limsup_thm' again *)
 >> Know ‘!x. x IN m_space m ==>
              limsup (\i. a i x) = Normal 0 /\ liminf (\i. a i x) = Normal 0’
 >- (Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
     Know ‘((\i. real (a i x)) --> 0) sequentially’
     >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     Q.ABBREV_TAC ‘c = \i. a i x’ \\
    ‘!i. a i x = c i’ by rw [Abbr ‘c’] >> POP_ORW \\
     Know ‘!n. 0 <= c n /\ c n <> PosInf’
     >- (Q.X_GEN_TAC ‘n’ >> SIMP_TAC std_ss [Abbr ‘c’, Abbr ‘a’, abs_pos] \\
        ‘?r. u n x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
        ‘?z. f x   = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_sub_def, extreal_abs_def]) \\
     DISCH_THEN (REWRITE_TAC o wrap o (MATCH_MP ext_limsup_thm')) \\
     REWRITE_TAC [GSYM extreal_of_num_def])
 >> REWRITE_TAC [GSYM extreal_of_num_def]
 >> DISCH_TAC
 (* f is also bounded by w *)
 >> Know ‘!x. x IN m_space m ==> abs (f x) <= w x’
 >- (RW_TAC std_ss [] \\
     MATCH_MP_TAC le_epsilon >> rpt STRIP_TAC \\
    ‘0 <= e’ by PROVE_TAC [lt_imp_le] \\
    ‘e <> NegInf’ by PROVE_TAC [pos_not_neginf] \\
    ‘?E. e = Normal E /\ 0 < E’
        by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] \\
     Q.PAT_X_ASSUM ‘!x. x IN m_space m ==> !e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘x’)) \\
     RW_TAC std_ss [] \\
     Q.PAT_X_ASSUM ‘!e. 0 < e ==> ?N. P’ (MP_TAC o (Q.SPEC ‘E’)) \\
     RW_TAC std_ss [] \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC ‘abs (u N x) + Normal E’ \\
     reverse CONJ_TAC
     >- (MATCH_MP_TAC le_radd_imp >> METIS_TAC []) \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC ‘abs (u N x) + abs (u N x - f x)’ \\
     CONJ_TAC >- (MATCH_MP_TAC abs_triangle_sub' >> rw []) \\
     MATCH_MP_TAC le_ladd_imp \\
     MATCH_MP_TAC lt_imp_le \\
     Q.UNABBREV_TAC ‘a’ >> FULL_SIMP_TAC std_ss [])
 >> DISCH_TAC
 (* preparing for fatou_lemma *)
 >> Know ‘!i x. x IN m_space m ==> a i x <= 2 * w x’
 >- (RW_TAC std_ss [GSYM extreal_double, Abbr ‘a’] \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC ‘abs (u i x) + abs (f x)’ \\
     CONJ_TAC >- (MATCH_MP_TAC abs_triangle_neg >> rw []) \\
     MATCH_MP_TAC le_add2 >> rw [])
 >> DISCH_TAC
 (* applying ext_liminf_le_limsup *)
 >> Know ‘!i. 0 <= integral m (a i)’
 >- (Q.X_GEN_TAC ‘i’ \\
     MATCH_MP_TAC integral_pos >> rw [Abbr ‘a’, abs_pos])
 >> DISCH_TAC
 >> Suff ‘limsup (\i. integral m (a i)) <= 0’
 >- (DISCH_TAC \\
     STRONG_CONJ_TAC
     >- (rw [GSYM le_antisym] \\
         MATCH_MP_TAC ext_limsup_pos >> rw []) \\
     DISCH_TAC \\
     REWRITE_TAC [GSYM le_antisym] \\
     reverse CONJ_TAC >- (MATCH_MP_TAC ext_liminf_pos >> rw []) \\
     MATCH_MP_TAC le_trans \\
     POP_ASSUM K_TAC \\
     Q.EXISTS_TAC ‘limsup (\i. integral m (a i))’ >> art [] \\
     REWRITE_TAC [ext_liminf_le_limsup])
 (* stage work *)
 >> Suff ‘limsup (\n. integral m (a n)) <= integral m (\x. limsup (\n. a n x))’
 >- (DISCH_TAC \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC ‘integral m (\x. limsup (\n. a n x))’ >> art [] \\
     MATCH_MP_TAC integral_neg >> rw [])
 (* final: applying fatou_lemma' *)
 >> Know ‘!n. integral m (a n) = pos_fn_integral m (a n)’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC integral_pos_fn >> rw [Abbr ‘a’, abs_pos])
 >> Rewr'
 >> Know  ‘integral m (\x. limsup (\n. a n x)) =
    pos_fn_integral m (\x. limsup (\n. a n x))’
 >- (MATCH_MP_TAC integral_pos_fn >> rw [])
 >> Rewr'
 >> MATCH_MP_TAC fatou_lemma'
 >> Q.EXISTS_TAC ‘\x. 2 * w x’ >> simp []
 >> CONJ_TAC (* pos_fn_integral m (\x. 2 * w x) < PosInf *)
 >- (REWRITE_TAC [extreal_of_num_def] \\
     Know ‘pos_fn_integral m (\x. Normal 2 * w x) = Normal 2 * pos_fn_integral m w’
     >- (MATCH_MP_TAC pos_fn_integral_cmul >> rw [le_02]) >> Rewr' \\
     Know ‘integral m w <> PosInf /\ integral m w <> NegInf’
     >- (MATCH_MP_TAC integrable_finite_integral >> art []) \\
     Know ‘integral m w = pos_fn_integral m w’
     >- (MATCH_MP_TAC integral_pos_fn >> rw []) >> Rewr' \\
     STRIP_TAC \\
    ‘?r. pos_fn_integral m w = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [GSYM lt_infty, extreal_mul_def])
 >> reverse CONJ_TAC >- FULL_SIMP_TAC std_ss [integrable_def]
 >> rw [Abbr ‘a’, abs_pos, GSYM lt_infty]
 >> ‘w x <> NegInf’ by METIS_TAC [pos_not_neginf]
 >> ‘?r. w x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> rw [extreal_of_num_def, extreal_mul_def]
QED

(* ------------------------------------------------------------------------- *)
(*  Integrals with Respect to Image Measures [1, Chapter 15]                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem 15.1, Part I (transformation theorem, positive functions only) *)
Theorem pos_fn_integral_distr :
    !M B f u. measure_space M /\ sigma_algebra B /\
              f IN measurable (m_space M, measurable_sets M) B /\
              u IN measurable B Borel /\
             (!x. x IN space B ==> 0 <= u x) ==>
             (pos_fn_integral (space B,subsets B,distr M f) u = pos_fn_integral M (u o f))
Proof
    rpt STRIP_TAC
 >> ‘measure_space (space B,subsets B,distr M f)’ by PROVE_TAC [measure_space_distr]
 >> Know ‘u o f IN measurable (m_space M,measurable_sets M) Borel’
 >- (MATCH_MP_TAC MEASURABLE_COMP \\
     Q.EXISTS_TAC ‘B’ >> art []) >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘(space B,subsets B,distr M f)’, ‘u’]
                    (INST_TYPE [alpha |-> “:'b”] lemma_fn_seq_sup))
 >> DISCH_THEN (STRIP_ASSUME_TAC o GSYM o REWRITE_RULE [m_space_def])
 (* LHS simplification *)
 >> Know ‘pos_fn_integral (space B,subsets B,distr M f) u =
          sup (IMAGE (\n. pos_fn_integral (space B,subsets B,distr M f)
                            (fn_seq (space B,subsets B,distr M f) u n)) UNIV)’
 >- (MATCH_MP_TAC lebesgue_monotone_convergence >> simp [] \\
     CONJ_TAC
     >- (Q.X_GEN_TAC ‘n’ \\
         MP_TAC (Q.SPECL [‘(space B,subsets B,distr M f)’, ‘u’, ‘n’]
                         (INST_TYPE [alpha |-> “:'b”] lemma_fn_seq_measurable)) \\
         RW_TAC std_ss [m_space_def, measurable_sets_def, SPACE]) \\
     CONJ_TAC
     >- (rpt STRIP_TAC \\
         MP_TAC (Q.SPECL [‘(space B,subsets B,distr M f)’, ‘u’, ‘i’, ‘x’]
                         (INST_TYPE [alpha |-> “:'b”] lemma_fn_seq_positive)) \\
         RW_TAC std_ss []) \\
     rpt STRIP_TAC \\
     MP_TAC (Q.SPECL [‘(space B,subsets B,distr M f)’, ‘u’, ‘x’]
                     (INST_TYPE [alpha |-> “:'b”] lemma_fn_seq_mono_increasing)) \\
     RW_TAC std_ss []) >> Rewr'
 (* RHS simplification *)
 >> Know ‘pos_fn_integral M (u o f) =
          pos_fn_integral M (\x. sup (IMAGE (\n. fn_seq (space B,subsets B,distr M f)
                                                        u n (f x)) UNIV))’
 >- (MATCH_MP_TAC pos_fn_integral_cong >> ASM_SIMP_TAC std_ss [] \\
     CONJ_TAC >- (rpt STRIP_TAC >> FIRST_X_ASSUM MATCH_MP_TAC \\
                  Q.PAT_X_ASSUM ‘f IN measurable (m_space M,measurable_sets M) B’ MP_TAC \\
                  rw [IN_MEASURABLE, IN_FUNSET]) \\
     CONJ_TAC >- (rw [le_sup', IN_IMAGE, IN_UNIV] \\
                  MATCH_MP_TAC le_trans \\
                  Q.EXISTS_TAC ‘fn_seq (space B,subsets B,distr M f) u 0 (f x)’ \\
                  reverse CONJ_TAC >- (POP_ASSUM MATCH_MP_TAC \\
                                       Q.EXISTS_TAC ‘0’ >> REWRITE_TAC []) \\
                  MATCH_MP_TAC lemma_fn_seq_positive \\
                  FIRST_X_ASSUM MATCH_MP_TAC \\
                  Q.PAT_X_ASSUM ‘f IN measurable (m_space M,measurable_sets M) B’ MP_TAC \\
                  rw [IN_MEASURABLE, IN_FUNSET]) \\
     rpt STRIP_TAC >> FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.PAT_X_ASSUM ‘f IN measurable (m_space M,measurable_sets M) B’ MP_TAC \\
     rw [IN_MEASURABLE, IN_FUNSET]) >> Rewr'
 >> Know ‘pos_fn_integral M
            (\x. sup (IMAGE (\n. fn_seq (space B,subsets B,distr M f) u n (f x)) UNIV)) =
          sup (IMAGE (\n. pos_fn_integral M
                            ((fn_seq (space B,subsets B,distr M f) u n) o f)) UNIV)’
 >- (HO_MATCH_MP_TAC lebesgue_monotone_convergence >> simp [] \\
     CONJ_TAC
     >- (GEN_TAC \\
         MATCH_MP_TAC MEASURABLE_COMP >> Q.EXISTS_TAC ‘B’ >> art [] \\
         MP_TAC (Q.SPECL [‘(space B,subsets B,distr M f)’, ‘u’, ‘n’]
                         (INST_TYPE [alpha |-> “:'b”] lemma_fn_seq_measurable)) \\
         RW_TAC std_ss [m_space_def, measurable_sets_def, SPACE]) \\
     CONJ_TAC
     >- (rpt STRIP_TAC \\
         MP_TAC (Q.SPECL [‘(space B,subsets B,distr M f)’, ‘u’, ‘n’, ‘f x’]
                         (INST_TYPE [alpha |-> “:'b”] lemma_fn_seq_positive)) \\
         RW_TAC std_ss [] \\
         POP_ASSUM MATCH_MP_TAC \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
         Q.PAT_X_ASSUM ‘f IN measurable (m_space M,measurable_sets M) B’ MP_TAC \\
         rw [IN_MEASURABLE, IN_FUNSET]) \\
     rpt STRIP_TAC \\
     MP_TAC (Q.SPECL [‘(space B,subsets B,distr M f)’, ‘u’, ‘f x’]
                     (INST_TYPE [alpha |-> “:'b”] lemma_fn_seq_mono_increasing)) \\
     RW_TAC std_ss [] \\
     POP_ASSUM MATCH_MP_TAC \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.PAT_X_ASSUM ‘f IN measurable (m_space M,measurable_sets M) B’ MP_TAC \\
     rw [IN_MEASURABLE, IN_FUNSET]) >> Rewr'
 >> Suff ‘!n. pos_fn_integral (space B,subsets B,distr M f)
                                (fn_seq (space B,subsets B,distr M f) u n) =
              pos_fn_integral M (fn_seq (space B,subsets B,distr M f) u n o f)’ >- Rewr
 >> POP_ASSUM K_TAC (* clean up *)
 (* stage work *)
 >> Q.X_GEN_TAC ‘N’
 >> SIMP_TAC std_ss [fn_seq_def, m_space_def, o_DEF]
 >> Know ‘!i n. (0 :extreal) <= &i / 2 pow n’
 >- (rpt GEN_TAC \\
    ‘2 pow n <> PosInf /\ 2 pow n <> NegInf’
       by METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty] \\
    ‘?r. 0 < r /\ (2 pow n = Normal r)’
       by METIS_TAC [lt_02, pow_pos_lt, extreal_cases, extreal_lt_eq,
                     extreal_of_num_def] >> POP_ORW \\
     MATCH_MP_TAC le_div >> rw [extreal_of_num_def, extreal_le_eq])
 >> DISCH_TAC
 (* LHS simplification *)
 >> Know ‘pos_fn_integral (space B,subsets B,distr M f)
            (\x. SIGMA (\k. &k / 2 pow N *
                           indicator_fn
                             {x | x IN space B /\ &k / 2 pow N <= u x /\
                                  u x < (&k + 1) / 2 pow N} x) (count (4 ** N)) +
                 2 pow N * indicator_fn {x | x IN space B /\ 2 pow N <= u x} x) =
          pos_fn_integral (space B,subsets B,distr M f)
            (\x. SIGMA (\k. &k / 2 pow N *
                           indicator_fn
                             {x | x IN space B /\ &k / 2 pow N <= u x /\
                                  u x < (&k + 1) / 2 pow N} x) (count (4 ** N))) +
          pos_fn_integral (space B,subsets B,distr M f)
            (\x. 2 pow N * indicator_fn {x | x IN space B /\ 2 pow N <= u x} x)’
 >- (HO_MATCH_MP_TAC pos_fn_integral_add \\
     ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def] \\
     CONJ_TAC (* 0 <= SIGMA *)
     >- (rpt STRIP_TAC \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> SIMP_TAC std_ss [FINITE_COUNT] \\
         Q.X_GEN_TAC ‘n’ >> STRIP_TAC \\
         MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
     CONJ_TAC (* 0 <= 2 pow N * indicator_fn *)
     >- (rpt STRIP_TAC \\
         MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS] \\
         MATCH_MP_TAC pow_pos_le >> REWRITE_TAC [le_02]) \\
     reverse CONJ_TAC (* 2 pow N * indicator_fn IN Borel_measurable *)
     >- (HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR \\
         rw [SPACE] >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST >> rw [] \\
                        Q.EXISTS_TAC ‘2 pow N’ >> rw []) \\
        ‘{x | x IN space B /\ 2 pow N <= u x} = {x | 2 pow N <= u x} INTER space B’
            by SET_TAC [] >> POP_ORW \\
         METIS_TAC [IN_MEASURABLE_BOREL_ALL]) \\
  (* SIGMA IN Borel_measurable *)
     MATCH_MP_TAC (INST_TYPE [“:'b” |-> “:num”] IN_MEASURABLE_BOREL_SUM) \\
     ASM_SIMP_TAC std_ss [SPACE, space_def] \\
     qexistsl_tac [‘\k x. &k / 2 pow N *
                          indicator_fn
                            {x | x IN space B /\ &k / 2 pow N <= u x /\
                                 u x < (&k + 1) / 2 pow N} x’, ‘count (4 ** N)’] \\
     SIMP_TAC std_ss [FINITE_COUNT] \\
     reverse CONJ_TAC
     >- (rpt GEN_TAC >> STRIP_TAC \\
         MATCH_MP_TAC pos_not_neginf \\
         MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
     rpt STRIP_TAC \\
     HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR >> rw []
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST >> rw [] \\
         Q.EXISTS_TAC ‘&i / 2 pow N’ >> rw []) \\
    ‘{x | x IN space B /\ &i / 2 pow N <= u x /\ u x < (&i + 1) / 2 pow N} =
     {x | &i / 2 pow N <= u x /\ u x < (&i + 1) / 2 pow N} INTER space B’
        by SET_TAC [] >> POP_ORW \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL]) >> Rewr'
 (* RHS simplification *)
 >> Know ‘pos_fn_integral M
            (\x. SIGMA
                   (\k. &k / 2 pow N *
                        indicator_fn
                          {x | x IN space B /\ &k / 2 pow N <= u x /\
                               u x < (&k + 1) / 2 pow N} (f x)) (count (4 ** N)) +
                 2 pow N * indicator_fn {x | x IN space B /\ 2 pow N <= u x} (f x)) =
          pos_fn_integral M
            (\x. SIGMA
                   (\k. &k / 2 pow N *
                        indicator_fn
                          {x | x IN space B /\ &k / 2 pow N <= u x /\
                               u x < (&k + 1) / 2 pow N} (f x)) (count (4 ** N))) +
          pos_fn_integral M
            (\x. 2 pow N * indicator_fn {x | x IN space B /\ 2 pow N <= u x} (f x))’
 >- (HO_MATCH_MP_TAC pos_fn_integral_add >> ASM_SIMP_TAC std_ss [] \\
     CONJ_TAC (* 0 <= SIGMA *)
     >- (rpt STRIP_TAC \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> SIMP_TAC std_ss [FINITE_COUNT] \\
         Q.X_GEN_TAC ‘n’ >> STRIP_TAC \\
         MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
     CONJ_TAC (* 0 <= 2 pow N * indicator_fn *)
     >- (rpt STRIP_TAC \\
         MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS] \\
         MATCH_MP_TAC pow_pos_le >> REWRITE_TAC [le_02]) \\
     reverse CONJ_TAC (* 2 pow N * indicator_fn IN Borel_measurable *)
     >- (‘(\x. 2 pow N *
               indicator_fn {x | x IN space B /\ 2 pow N <= u x} (f x)) =
          (\x. 2 pow N *
               indicator_fn {x | x IN space B /\ 2 pow N <= u x} x) o f’ by rw [o_DEF] >> POP_ORW \\
         MATCH_MP_TAC MEASURABLE_COMP >> Q.EXISTS_TAC ‘B’ >> art [] \\
         HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR \\
         rw [] >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST >> rw [] \\
                   Q.EXISTS_TAC ‘2 pow N’ >> rw []) \\
        ‘{x | x IN space B /\ 2 pow N <= u x} = {x | 2 pow N <= u x} INTER space B’
            by SET_TAC [] >> POP_ORW \\
         METIS_TAC [IN_MEASURABLE_BOREL_ALL]) \\
  (* SIGMA IN Borel_measurable *)
     MATCH_MP_TAC (INST_TYPE [“:'b” |-> “:num”] IN_MEASURABLE_BOREL_SUM) \\
     ASM_SIMP_TAC std_ss [SPACE, space_def] \\
     qexistsl_tac [‘\k x. &k / 2 pow N *
                          indicator_fn
                            {x | x IN space B /\ &k / 2 pow N <= u x /\
                                 u x < (&k + 1) / 2 pow N} (f x)’, ‘count (4 ** N)’] \\
     SIMP_TAC std_ss [FINITE_COUNT] \\
     CONJ_TAC >- FULL_SIMP_TAC std_ss [measure_space_def] \\
     reverse CONJ_TAC
     >- (rpt GEN_TAC >> STRIP_TAC \\
         MATCH_MP_TAC pos_not_neginf \\
         MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
     rpt STRIP_TAC \\
    ‘(\x. &i / 2 pow N * indicator_fn {x | x IN space B /\ &i / 2 pow N <= u x /\
                                           u x < (&i + 1) / 2 pow N} (f x)) =
     (\x. &i / 2 pow N * indicator_fn {x | x IN space B /\ &i / 2 pow N <= u x /\
                                           u x < (&i + 1) / 2 pow N} x) o f’
        by RW_TAC std_ss [o_DEF] >> POP_ORW \\
     MATCH_MP_TAC MEASURABLE_COMP >> Q.EXISTS_TAC ‘B’ >> art [] \\
     HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR >> rw []
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST >> rw [] \\
         Q.EXISTS_TAC ‘&i / 2 pow N’ >> rw []) \\
    ‘{x | x IN space B /\ &i / 2 pow N <= u x /\ u x < (&i + 1) / 2 pow N} =
     {x | &i / 2 pow N <= u x /\ u x < (&i + 1) / 2 pow N} INTER space B’
        by SET_TAC [] >> POP_ORW \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL]) >> Rewr'
 (* LHS simplification *)
 >> Know ‘pos_fn_integral (space B,subsets B,distr M f)
           (\x. SIGMA
                  (\k. (\k x. &k / 2 pow N *
                              indicator_fn
                                {x | x IN space B /\ &k / 2 pow N <= u x /\
                                     u x < (&k + 1) / 2 pow N} x) k x) (count (4 ** N))) =
          SIGMA (\k. pos_fn_integral (space B,subsets B,distr M f)
                      ((\k x. &k / 2 pow N *
                              indicator_fn
                                {x | x IN space B /\ &k / 2 pow N <= u x /\
                                     u x < (&k + 1) / 2 pow N} x) k))
                (count (4 ** N))’
 >- (MATCH_MP_TAC (INST_TYPE [beta |-> “:num”] pos_fn_integral_sum) \\
     ASM_SIMP_TAC std_ss [FINITE_COUNT, m_space_def, measurable_sets_def, SPACE] \\
     CONJ_TAC (* 0 <= &i / 2 pow N * indicator_fn *)
     >- (rpt STRIP_TAC \\
         MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
     rpt STRIP_TAC \\
     HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR >> art [] \\
     CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST >> rw [] \\
                  Q.EXISTS_TAC ‘&i / 2 pow N’ >> rw []) \\
    ‘{x | x IN space B /\ &i / 2 pow N <= u x /\ u x < (&i + 1) / 2 pow N} =
     {x | &i / 2 pow N <= u x /\ u x < (&i + 1) / 2 pow N} INTER space B’
        by SET_TAC [] >> POP_ORW \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL])
 >> BETA_TAC >> Rewr'
 >> Know ‘pos_fn_integral M
           (\x. SIGMA
                  (\k. (\k x. &k / 2 pow N *
                              indicator_fn
                                {x | x IN space B /\ &k / 2 pow N <= u x /\
                                     u x < (&k + 1) / 2 pow N} (f x)) k x) (count (4 ** N))) =
          SIGMA (\k. pos_fn_integral M
                      ((\k x. &k / 2 pow N *
                              indicator_fn
                                {x | x IN space B /\ &k / 2 pow N <= u x /\
                                     u x < (&k + 1) / 2 pow N} (f x)) k))
                (count (4 ** N))’
 >- (MATCH_MP_TAC (INST_TYPE [beta |-> “:num”] pos_fn_integral_sum) \\
     ASM_SIMP_TAC std_ss [FINITE_COUNT] \\
     CONJ_TAC (* 0 <= &i / 2 pow N * indicator_fn *)
     >- (rpt STRIP_TAC \\
         MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
     rpt STRIP_TAC \\
    ‘(\x. &i / 2 pow N *
          indicator_fn {x | x IN space B /\ &i / 2 pow N <= u x /\
                            u x < (&i + 1) / 2 pow N} (f x)) =
     (\x. &i / 2 pow N *
          indicator_fn {x | x IN space B /\ &i / 2 pow N <= u x /\
                            u x < (&i + 1) / 2 pow N} x) o f’
        by RW_TAC std_ss [o_DEF] >> POP_ORW \\
     MATCH_MP_TAC MEASURABLE_COMP >> Q.EXISTS_TAC ‘B’ >> art [] \\
     HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR >> art [] \\
     CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST >> rw [] \\
                  Q.EXISTS_TAC ‘&i / 2 pow N’ >> rw []) \\
    ‘{x | x IN space B /\ &i / 2 pow N <= u x /\ u x < (&i + 1) / 2 pow N} =
     {x | &i / 2 pow N <= u x /\ u x < (&i + 1) / 2 pow N} INTER space B’
        by SET_TAC [] >> POP_ORW \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL])
 >> BETA_TAC >> Rewr'
 (* LHS simplification *)
 >> Know ‘pos_fn_integral (space B,subsets B,distr M f)
            (\x. 2 pow N * indicator_fn {x | x IN space B /\ 2 pow N <= u x} x) =
          2 pow N * pos_fn_integral (space B,subsets B,distr M f)
                                    (indicator_fn {x | x IN space B /\ 2 pow N <= u x})’
 >- (‘2 pow N = Normal (2 pow N)’ by METIS_TAC [extreal_of_num_def, extreal_pow_def] >> POP_ORW \\
     MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) >> Rewr'
 (* RHS simplification *)
 >> Know ‘pos_fn_integral M
            (\x. 2 pow N * indicator_fn {x | x IN space B /\ 2 pow N <= u x} (f x)) =
          2 pow N * pos_fn_integral M (\x. indicator_fn {x | x IN space B /\ 2 pow N <= u x} (f x))’
 >- (‘2 pow N = Normal (2 pow N)’ by METIS_TAC [extreal_of_num_def, extreal_pow_def] >> POP_ORW \\
     HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) >> Rewr'
 (* LHS simplification *)
 >> Know ‘!k. pos_fn_integral (space B,subsets B,distr M f)
                (\x. &k / 2 pow N *
                     indicator_fn {x | x IN space B /\ &k / 2 pow N <= u x /\
                                       u x < (&k + 1) / 2 pow N} x) =
              &k / 2 pow N * pos_fn_integral (space B,subsets B,distr M f)
                               (indicator_fn {x | x IN space B /\ &k / 2 pow N <= u x /\
                                                  u x < (&k + 1) / 2 pow N})’
 >- (GEN_TAC \\
    ‘!n. 0:real < 2 pow n’ by RW_TAC real_ss [REAL_POW_LT] \\
    ‘!n. 0:real <> 2 pow n’ by RW_TAC real_ss [REAL_LT_IMP_NE] \\
    ‘!n k. &k / 2 pow n = Normal (&k / 2 pow n)’
        by METIS_TAC [extreal_of_num_def, extreal_pow_def, extreal_div_eq] >> POP_ORW \\
     MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS] \\
     MATCH_MP_TAC REAL_LE_DIV >> rw []) >> Rewr'
 (* RHS simplification *)
 >> Know ‘!k. pos_fn_integral M
                (\x. &k / 2 pow N * indicator_fn {x | x IN space B /\ &k / 2 pow N <= u x /\
                                                      u x < (&k + 1) / 2 pow N} (f x)) =
              &k / 2 pow N * pos_fn_integral M
                               (\x. indicator_fn {x | x IN space B /\ &k / 2 pow N <= u x /\
                                                      u x < (&k + 1) / 2 pow N} (f x))’
 >- (GEN_TAC \\
    ‘!n. 0:real < 2 pow n’ by RW_TAC real_ss [REAL_POW_LT] \\
    ‘!n. 0:real <> 2 pow n’ by RW_TAC real_ss [REAL_LT_IMP_NE] \\
    ‘!n k. &k / 2 pow n = Normal (&k / 2 pow n)’
        by METIS_TAC [extreal_of_num_def, extreal_pow_def, extreal_div_eq] >> POP_ORW \\
     HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS] \\
     MATCH_MP_TAC REAL_LE_DIV >> rw []) >> Rewr'
 (* stage work *)
 >> Suff ‘!s. s IN subsets B ==>
             (pos_fn_integral (space B,subsets B,distr M f) (indicator_fn s) =
              pos_fn_integral M (\x. indicator_fn s (f x)))’
 >- (DISCH_TAC \\
    ‘!k. {x | x IN space B /\ &k / 2 pow N <= u x /\ u x < (&k + 1) / 2 pow N} =
         {x | &k / 2 pow N <= u x /\ u x < (&k + 1) / 2 pow N} INTER space B’
       by SET_TAC [] >> POP_ORW \\
    ‘{x | x IN space B /\ 2 pow N <= u x} = {x | 2 pow N <= u x} INTER space B’
       by SET_TAC [] >> POP_ORW \\
     Know ‘pos_fn_integral (space B,subsets B,distr M f)
             (indicator_fn ({x | 2 pow N <= u x} INTER space B)) =
           pos_fn_integral M
             (\x. indicator_fn ({x | 2 pow N <= u x} INTER space B) (f x))’
     >- (FIRST_X_ASSUM MATCH_MP_TAC \\
         METIS_TAC [IN_MEASURABLE_BOREL_ALL]) >> Rewr' \\
     Know ‘!k. pos_fn_integral (space B,subsets B,distr M f)
                 (indicator_fn
                    ({x | &k / 2 pow N <= u x /\ u x < (&k + 1) / 2 pow N} INTER space B)) =
               pos_fn_integral M
                 (\x. indicator_fn
                        ({x | &k / 2 pow N <= u x /\ u x < (&k + 1) / 2 pow N} INTER space B) (f x))’
     >- (GEN_TAC >> FIRST_X_ASSUM MATCH_MP_TAC \\
         METIS_TAC [IN_MEASURABLE_BOREL_ALL]) >> Rewr)
 (* core proof *)
 >> rpt STRIP_TAC
 >> Know ‘pos_fn_integral (space B,subsets B,distr M f) (indicator_fn s) =
          measure (space B,subsets B,distr M f) s’
 >- (MATCH_MP_TAC pos_fn_integral_indicator >> rw []) >> Rewr'
 >> SIMP_TAC std_ss [measure_def, distr_def]
 >> Know ‘pos_fn_integral M (\x. indicator_fn s (f x)) =
          pos_fn_integral M (indicator_fn (PREIMAGE f s INTER m_space M))’
 >- (MATCH_MP_TAC pos_fn_integral_cong >> rw [INDICATOR_FN_POS] \\
     rw [indicator_fn_def]) >> Rewr'
 >> MATCH_MP_TAC EQ_SYM
 >> MATCH_MP_TAC pos_fn_integral_indicator
 >> fs [IN_MEASURABLE]
QED

(* Theorem 15.1, Part II (transformation theorem, general form) [1, p.154] *)
Theorem integral_distr :
    !M B f u. measure_space M /\ sigma_algebra B /\
              f IN measurable (m_space M, measurable_sets M) B /\
              u IN measurable B Borel ==>
             (integral (space B,subsets B,distr M f) u = integral M (u o f)) /\
             (integrable (space B,subsets B,distr M f) u = integrable M (u o f))
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> simp [integrable_def, integral_def]
 >> Suff ‘(pos_fn_integral (space B,subsets B,distr M f) (fn_plus u) =
           pos_fn_integral M (fn_plus (u o f))) /\
          (pos_fn_integral (space B,subsets B,distr M f) (fn_minus u) =
           pos_fn_integral M (fn_minus (u o f)))’
 >- (Rewr >> EQ_TAC >> rw [] \\
     MATCH_MP_TAC MEASURABLE_COMP >> Q.EXISTS_TAC ‘B’ >> art [])
 >> Know ‘fn_plus (u o f) = fn_plus u o f’
 >- rw [FN_PLUS_ALT, o_DEF] >> DISCH_THEN (fs o wrap)
 >> Know ‘fn_minus (u o f) = fn_minus u o f’
 >- rw [FN_MINUS_ALT, o_DEF] >> DISCH_THEN (fs o wrap)
 >> CONJ_TAC
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC pos_fn_integral_distr >> rw [FN_PLUS_POS] \\
      MATCH_MP_TAC IN_MEASURABLE_BOREL_FN_PLUS >> art [],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC pos_fn_integral_distr >> rw [FN_MINUS_POS] \\
      MATCH_MP_TAC IN_MEASURABLE_BOREL_FN_MINUS >> art [] ]
QED

Theorem pos_fn_integral_cong_measure :
    !sp sts u v f.
        measure_space (sp,sts,u) /\ measure_space (sp,sts,v) /\
        (!s. s IN sts ==> (u s = v s)) /\ (!x. x IN sp ==> 0 <= f x) ==>
        (pos_fn_integral (sp,sts,u) f = pos_fn_integral (sp,sts,v) f)
Proof
    rw [pos_fn_integral_def]
 >> Suff ‘!g. psfis (sp,sts,u) g = psfis (sp,sts,v) g’ >- rw []
 >> rw [psfis_def, Once EXTENSION, IN_IMAGE]
 >> EQ_TAC >> STRIP_TAC (* 2 subgoals, same tactics *)
 >> ( fs [psfs_def, pos_simple_fn_def] \\
      rename1 ‘!i. i IN s ==> 0 <= z i’ \\
      Q.EXISTS_TAC ‘(s,a,z)’ \\
      REV_FULL_SIMP_TAC std_ss [pos_simple_fn_integral_def, measure_def] \\
      Q.PAT_X_ASSUM ‘x = _’ K_TAC \\
      Q.PAT_X_ASSUM ‘_ = (s,a,z)’ K_TAC \\
      irule EXTREAL_SUM_IMAGE_EQ >> rfs [] \\
      DISJ1_TAC >> NTAC 2 STRIP_TAC \\
      MATCH_MP_TAC pos_not_neginf \\
      MATCH_MP_TAC le_mul \\
      CONJ_TAC >- (rw [extreal_of_num_def, extreal_le_eq]) \\
      rename1 ‘y IN s’ \\
     ‘positive (sp,sts,v)’ by PROVE_TAC [MEASURE_SPACE_POSITIVE] \\
      fs [positive_def] )
QED

Theorem pos_fn_integral_cong_measure' :
    !m1 m2 f. measure_space m1 /\ measure_space m2 /\ measure_space_eq m1 m2 /\
             (!x. x IN m_space m1 ==> 0 <= f x) ==>
             (pos_fn_integral m1 f = pos_fn_integral m2 f)
Proof
    RW_TAC std_ss [measure_space_eq_def]
 >> MP_TAC (Q.SPECL [‘m_space m1’, ‘measurable_sets m1’, ‘measure m1’, ‘measure m2’, ‘f’]
                    pos_fn_integral_cong_measure)
 >> rw []
QED

Theorem integral_cong_measure_base[local] :
    !sp sts u v f.
        measure_space (sp,sts,u) /\ measure_space (sp,sts,v) /\
       (!s. s IN sts ==> (u s = v s)) ==>
       (integral (sp,sts,u) f = integral (sp,sts,v) f) /\
       (integrable (sp,sts,u) f <=> integrable (sp,sts,v) f)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> simp [integral_def, integrable_def]
 >> Suff ‘(pos_fn_integral (sp,sts,u) (fn_plus f) = pos_fn_integral (sp,sts,v) (fn_plus f)) /\
          (pos_fn_integral (sp,sts,u) (fn_minus f) = pos_fn_integral (sp,sts,v) (fn_minus f))’
 >- rw []
 >> CONJ_TAC (* 2 subgoals, same tactics *)
 >> MATCH_MP_TAC pos_fn_integral_cong_measure
 >> rw [FN_PLUS_POS, FN_MINUS_POS]
QED

Theorem integral_cong_measure :
    !sp sts u v f.
        measure_space (sp,sts,u) /\ measure_space (sp,sts,v) /\
       (!s. s IN sts ==> (u s = v s)) ==>
       (integral (sp,sts,u) f = integral (sp,sts,v) f)
Proof
    PROVE_TAC [integral_cong_measure_base]
QED

Theorem integral_cong_measure' :
    !m1 m2 f. measure_space m1 /\ measure_space m2 /\ measure_space_eq m1 m2 ==>
             (integral m1 f = integral m2 f)
Proof
    RW_TAC std_ss [measure_space_eq_def]
 >> MP_TAC (Q.SPECL [‘m_space m1’, ‘measurable_sets m1’, ‘measure m1’, ‘measure m2’, ‘f’]
                    integral_cong_measure)
 >> rw []
QED

Theorem integrable_cong_measure :
    !sp sts u v f.
        measure_space (sp,sts,u) /\ measure_space (sp,sts,v) /\
       (!s. s IN sts ==> (u s = v s)) ==>
       (integrable (sp,sts,u) f <=> integrable (sp,sts,v) f)
Proof
    PROVE_TAC [integral_cong_measure_base]
QED

(* NOTE: changed to use ‘measure_space_eq m1 m2’ *)
Theorem integrable_cong_measure' :
    !m1 m2 f. measure_space m1 /\ measure_space m2 /\ measure_space_eq m1 m2 ==>
             (integrable m1 f <=> integrable m2 f)
Proof
    RW_TAC std_ss [measure_space_eq_def]
 >> MP_TAC (Q.SPECL [‘m_space m1’, ‘measurable_sets m1’, ‘measure m1’, ‘measure m2’, ‘f’]
                    integrable_cong_measure)
 >> rw []
QED

(* ------------------------------------------------------------------------- *)
(*  Product measures and Fubini's theorem (Chapter 14 of [1])                *)
(* ------------------------------------------------------------------------- *)

(* ‘FCP_CONCAT s t’ is in place of ‘(a,b)’ (pair), thus ’fcp_pair a b’ is ‘a CROSS b’ *)
val fcp_cross_def = Define (* cf. CROSS_DEF *)
   ‘fcp_cross A B = {FCP_CONCAT a b | a IN A /\ b IN B}’;

Theorem IN_FCP_CROSS : (* cf. IN_CROSS *)
    !s a b. s IN fcp_cross a b <=> ?t u. (s = FCP_CONCAT t u) /\ t IN a /\ u IN b
Proof
    RW_TAC std_ss [fcp_cross_def, GSPECIFICATION, UNCURRY]
 >> EQ_TAC >- PROVE_TAC []
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC `(t,u)`
 >> RW_TAC std_ss []
QED

(* high dimensional space are made by lower dimensional spaces *)
Theorem fcp_cross_UNIV :
    FINITE univ(:'b) /\ FINITE univ(:'c) ==>
    fcp_cross univ(:'a['b]) univ(:'a['c]) = univ(:'a['b + 'c])
Proof
    rw [Once EXTENSION, IN_UNIV, GSPECIFICATION, IN_FCP_CROSS]
 >> Q.EXISTS_TAC ‘FCP i. x ' (i + dimindex(:'c))’
 >> Q.EXISTS_TAC ‘FCP i. x ' i’
 >> rw [FCP_CONCAT_def, CART_EQ, index_sum, FCP_BETA]
QED

val fcp_prod_def = Define (* cf. prod_sets_def *)
   ‘fcp_prod a b = {fcp_cross s t | s IN a /\ t IN b}’;

Theorem IN_FCP_PROD :
    !s A B. s IN fcp_prod A B <=> ?a b. (s = fcp_cross a b) /\ a IN A /\ b IN B
Proof
    RW_TAC std_ss [fcp_prod_def, GSPECIFICATION, UNCURRY]
 >> EQ_TAC >- PROVE_TAC []
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC `(a,b)`
 >> RW_TAC std_ss []
QED

Theorem FCP_BIGUNION_CROSS :
    !f s t. fcp_cross (BIGUNION (IMAGE f s)) t = BIGUNION (IMAGE (\n. fcp_cross (f n) t) s)
Proof
    rw [Once EXTENSION, IN_BIGUNION_IMAGE, IN_FCP_CROSS]
 >> EQ_TAC >> rpt STRIP_TAC
 >- (rename1 ‘z IN s’ >> Q.EXISTS_TAC ‘z’ >> art [] \\
     rename1 ‘x = FCP_CONCAT c u’ \\
     qexistsl_tac [‘c’,‘u’] >> art [])
 >> rename1 ‘x = FCP_CONCAT c u’
 >> qexistsl_tac [‘c’,‘u’] >> art []
 >> Q.EXISTS_TAC ‘n’ >> art []
QED

Theorem FCP_CROSS_BIGUNION :
    !f s t. fcp_cross t (BIGUNION (IMAGE f s)) = BIGUNION (IMAGE (\n. fcp_cross t (f n)) s)
Proof
    rw [Once EXTENSION, IN_BIGUNION_IMAGE, IN_FCP_CROSS]
 >> EQ_TAC >> rpt STRIP_TAC
 >- (rename1 ‘z IN s’ >> Q.EXISTS_TAC ‘z’ >> art [] \\
     rename1 ‘x = FCP_CONCAT c u’ \\
     qexistsl_tac [‘c’,‘u’] >> art [])
 >> rename1 ‘x = FCP_CONCAT c u’
 >> qexistsl_tac [‘c’,‘u’] >> art []
 >> Q.EXISTS_TAC ‘n’ >> art []
QED

Theorem FCP_CROSS_DIFF :
    !(X :'a['b] set) s (t :'a['c] set).
        FINITE univ(:'b) /\ FINITE univ(:'c) ==>
        fcp_cross (X DIFF s) t = (fcp_cross X t) DIFF (fcp_cross s t)
Proof
    rw [Once EXTENSION, IN_FCP_CROSS, IN_DIFF]
 >> EQ_TAC >> rpt STRIP_TAC (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      rename1 ‘c IN X’ >> qexistsl_tac [‘c’,‘u’] >> art [],
      (* goal 2 (of 3) *)
      rename1 ‘c IN X’ \\
      rename [‘x = FCP_CONCAT c' u'’, ‘c' NOTIN s \/ u' NOTIN t’] \\
      DISJ1_TAC \\
      CCONTR_TAC >> fs [] \\
      Q.PAT_X_ASSUM ‘x = FCP_CONCAT c' u'’ K_TAC \\
      Suff ‘c = c'’ >- METIS_TAC [] \\
      PROVE_TAC [FCP_CONCAT_11],
      (* goal 3 (of 3) *)
      rename1 ‘x = FCP_CONCAT c u’ \\
      qexistsl_tac [‘c’,‘u’] >> art [] >> PROVE_TAC [] ]
QED

Theorem FCP_CROSS_DIFF' :
    !(s :'a['b] set) (X :'a['c] set) t.
        FINITE univ(:'b) /\ FINITE univ(:'c) ==>
        fcp_cross s (X DIFF t) = (fcp_cross s X) DIFF (fcp_cross s t)
Proof
    rw [Once EXTENSION, IN_FCP_CROSS, IN_DIFF]
 >> EQ_TAC >> rpt STRIP_TAC (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      rename1 ‘c IN s’ >> qexistsl_tac [‘c’,‘u’] >> art [],
      (* goal 2 (of 3) *)
      rename1 ‘c IN s’ \\
      rename[‘x = FCP_CONCAT c' u'’,‘c' NOTIN s \/ u' NOTIN t’] \\
      DISJ2_TAC \\
      CCONTR_TAC >> fs [] \\
      Q.PAT_X_ASSUM ‘x = FCP_CONCAT c' u'’ K_TAC \\
      Suff ‘u = u'’ >- METIS_TAC [] \\
      PROVE_TAC [FCP_CONCAT_11],
      (* goal 3 (of 3) *)
      rename1 ‘x = FCP_CONCAT c u’ \\
      qexistsl_tac [‘c’,‘u’] >> art [] >> PROVE_TAC [] ]
QED

Theorem FCP_SUBSET_CROSS :
    !(a :'a['b] set) b (c :'a['c] set) d.
        a SUBSET b /\ c SUBSET d ==> (fcp_cross a c) SUBSET (fcp_cross b d)
Proof
    rpt STRIP_TAC
 >> rw [SUBSET_DEF, IN_FCP_CROSS]
 >> qexistsl_tac [‘t’, ‘u’] >> art []
 >> PROVE_TAC [SUBSET_DEF]
QED

Theorem FCP_INTER_CROSS :
    !(a :'a['b] set) (b :'a['c] set) c d.
        FINITE univ(:'b) /\ FINITE univ(:'c) ==>
       (fcp_cross a b) INTER (fcp_cross c d) = fcp_cross (a INTER c) (b INTER d)
Proof
    rw [Once EXTENSION, IN_INTER, IN_FCP_CROSS]
 >> EQ_TAC >> rpt STRIP_TAC (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      fs [] >> qexistsl_tac [‘t’, ‘u’] >> art [] \\
      PROVE_TAC [FCP_CONCAT_11],
      (* goal 2 (of 3) *)
      qexistsl_tac [‘t’, ‘u’] >> art [],
      (* goal 3 (of 3) *)
      qexistsl_tac [‘t’, ‘u’] >> art [] ]
QED

(* see also LISP ... *)
val pair_operation_def = Define
   ‘pair_operation (cons :'a -> 'b -> 'c) car cdr =
      ((!a b. (car (cons a b) = a) /\ (cdr (cons a b) = b)) /\
       (!a b c d. (cons a b = cons c d) <=> (a = c) /\ (b = d)))’;

(* two sample pair operations: comma (pairTheory) and FCP_CONCAT (fcpTheory) *)
Theorem pair_operation_pair :
    pair_operation (pair$, :'a -> 'b -> 'a # 'b)
                   (FST :'a # 'b -> 'a) (SND :'a # 'b -> 'b)
Proof
    rw [pair_operation_def]
QED

Theorem pair_operation_FCP_CONCAT :
    FINITE univ(:'b) /\ FINITE univ(:'c) ==>
    pair_operation (FCP_CONCAT :'a['b] -> 'a['c] -> 'a['b + 'c])
                   (FCP_FST :'a['b + 'c] -> 'a['b])
                   (FCP_SND :'a['b + 'c] -> 'a['c])
Proof
    DISCH_TAC
 >> ASM_SIMP_TAC std_ss [pair_operation_def]
 >> reverse CONJ_TAC >- METIS_TAC [FCP_CONCAT_11]
 >> rpt GEN_TAC
 >> PROVE_TAC [FCP_CONCAT_THM]
QED

Theorem pair_operation_CONS :
    pair_operation CONS HD TL
Proof
    rw [pair_operation_def]
QED

val general_cross_def = Define
   ‘general_cross (cons :'a -> 'b -> 'c) A B = {cons a b | a IN A /\ b IN B}’;

Theorem IN_general_cross :
    !cons s A B. s IN (general_cross cons A B) <=>
                 ?a b. s = cons a b /\ a IN A /\ b IN B
Proof
    RW_TAC std_ss [general_cross_def, GSPECIFICATION]
 >> EQ_TAC >> rpt STRIP_TAC
 >- (Cases_on ‘x’ >> fs [] >> qexistsl_tac [‘q’,‘r’] >> art [])
 >> Q.EXISTS_TAC ‘(a,b)’ >> rw []
QED

(* alternative definition of pred_set$CROSS *)
Theorem CROSS_ALT :
    !A B. A CROSS B = general_cross pair$, A B
Proof
    RW_TAC std_ss [Once EXTENSION, IN_CROSS, IN_general_cross]
 >> EQ_TAC >> rw [] >> fs []
 >> qexistsl_tac [‘FST x’,‘SND x’] >> rw [PAIR]
QED

(* alternative definition of fcp_cross *)
Theorem fcp_cross_alt :
    !A B. fcp_cross A B = general_cross FCP_CONCAT A B
Proof
    RW_TAC std_ss [Once EXTENSION, IN_FCP_CROSS, IN_general_cross]
QED

val general_prod_def = Define
   ‘general_prod (cons :'a -> 'b -> 'c) A B =
      {general_cross cons a b | a IN A /\ b IN B}’;

Theorem IN_general_prod :
    !(cons :'a -> 'b -> 'c) s A B.
        s IN general_prod cons A B <=> ?a b. (s = general_cross cons a b) /\ a IN A /\ b IN B
Proof
    RW_TAC std_ss [general_prod_def, GSPECIFICATION, UNCURRY]
 >> EQ_TAC >> rpt STRIP_TAC
 >- (qexistsl_tac [‘FST x’, ‘SND x’] >> art [])
 >> Q.EXISTS_TAC `(a,b)`
 >> RW_TAC std_ss []
QED

(* alternative definition of prod_sets *)
Theorem prod_sets_alt :
    !A B. prod_sets A B = general_prod pair$, A B
Proof
    RW_TAC std_ss [Once EXTENSION, IN_PROD_SETS, IN_general_prod, GSYM CROSS_ALT]
QED

(* alternative definition of fcp_prod *)
Theorem fcp_prod_alt :
    !A B. fcp_prod A B = general_prod FCP_CONCAT A B
Proof
    RW_TAC std_ss [Once EXTENSION, IN_FCP_PROD, IN_general_prod, GSYM fcp_cross_alt]
QED

Theorem general_BIGUNION_CROSS :
    !(cons :'a -> 'b -> 'c) f (s :'index set) t.
       (general_cross cons (BIGUNION (IMAGE f s)) t =
        BIGUNION (IMAGE (\n. general_cross cons (f n) t) s))
Proof
    rw [Once EXTENSION, IN_BIGUNION_IMAGE, IN_general_cross]
 >> EQ_TAC >> rpt STRIP_TAC
 >- (rename1 ‘z IN s’ >> Q.EXISTS_TAC ‘z’ >> art [] \\
     qexistsl_tac [‘a’,‘b’] >> art [])
 >> qexistsl_tac [‘a’,‘b’] >> art []
 >> Q.EXISTS_TAC ‘n’ >> art []
QED

Theorem general_CROSS_BIGUNION :
    !(cons :'a -> 'b -> 'c) f (s :'index set) t.
       (general_cross cons t (BIGUNION (IMAGE f s)) =
        BIGUNION (IMAGE (\n. general_cross cons t (f n)) s))
Proof
    rw [Once EXTENSION, IN_BIGUNION_IMAGE, IN_general_cross]
 >> EQ_TAC >> rpt STRIP_TAC
 >- (rename1 ‘z IN s’ >> Q.EXISTS_TAC ‘z’ >> art [] \\
     qexistsl_tac [‘a’,‘b’] >> art [])
 >> qexistsl_tac [‘a’,‘b’] >> art []
 >> Q.EXISTS_TAC ‘n’ >> art []
QED

Theorem general_CROSS_DIFF :
    !(cons :'a -> 'b -> 'c) car cdr (X :'a set) s (t :'b set).
        pair_operation cons car cdr ==>
       (general_cross cons (X DIFF s) t =
        (general_cross cons X t) DIFF (general_cross cons s t))
Proof
    rw [Once EXTENSION, IN_general_cross, IN_DIFF]
 >> EQ_TAC >> rpt STRIP_TAC (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      qexistsl_tac [‘a’,‘b’] >> art [],
      (* goal 2 (of 3) *)
      DISJ1_TAC \\
      CCONTR_TAC >> fs [] \\
      Q.PAT_X_ASSUM ‘x = cons a' b'’ K_TAC \\
      Suff ‘a = a'’ >- METIS_TAC [] \\
      METIS_TAC [pair_operation_def],
      (* goal 3 (of 3) *)
      qexistsl_tac [‘a’,‘b’] >> art [] >> PROVE_TAC [] ]
QED

Theorem general_CROSS_DIFF' :
    !(cons :'a -> 'b -> 'c) car cdr (s :'a set) (X :'b set) t.
        pair_operation cons car cdr ==>
       (general_cross cons s (X DIFF t) =
        (general_cross cons s X) DIFF (general_cross cons s t))
Proof
    rw [Once EXTENSION, IN_general_cross, IN_DIFF]
 >> EQ_TAC >> rpt STRIP_TAC (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      qexistsl_tac [‘a’,‘b’] >> art [],
      (* goal 2 (of 3) *)
      DISJ2_TAC \\
      CCONTR_TAC >> fs [] \\
      Q.PAT_X_ASSUM ‘x = cons a' b'’ K_TAC \\
      Suff ‘b = b'’ >- METIS_TAC [] \\
      METIS_TAC [pair_operation_def],
      (* goal 3 (of 3) *)
      qexistsl_tac [‘a’,‘b’] >> art [] >> PROVE_TAC [] ]
QED

Theorem general_SUBSET_CROSS :
    !(cons :'a -> 'b -> 'c) (a :'a set) b (c :'b set) d.
        a SUBSET b /\ c SUBSET d ==>
        (general_cross cons a c) SUBSET (general_cross cons b d)
Proof
    rpt STRIP_TAC
 >> rw [SUBSET_DEF, IN_general_cross]
 >> qexistsl_tac [‘a'’, ‘b'’] >> art []
 >> PROVE_TAC [SUBSET_DEF]
QED

Theorem general_INTER_CROSS :
    !(cons :'a -> 'b -> 'c) car cdr (a :'a set) (b :'b set) c d.
        pair_operation cons car cdr ==>
       ((general_cross cons a b) INTER (general_cross cons c d) =
        general_cross cons (a INTER c) (b INTER d))
Proof
    rw [Once EXTENSION, IN_INTER, IN_general_cross]
 >> EQ_TAC >> rpt STRIP_TAC (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      fs [] >> rename1 ‘x = cons s t’ \\
      qexistsl_tac [‘s’, ‘t’] >> art [] \\
      METIS_TAC [pair_operation_def],
      (* goal 2 (of 3) *)
      qexistsl_tac [‘a'’, ‘b'’] >> art [],
      (* goal 3 (of 3) *)
      qexistsl_tac [‘a'’, ‘b'’] >> art [] ]
QED

Theorem INDICATOR_FN_FCP_CROSS :
    !(s :'a['b] set) (t :'a['c] set) x y.
        FINITE univ(:'b) /\ FINITE univ(:'c) ==>
       (indicator_fn (fcp_cross s t) (FCP_CONCAT x y) =
        indicator_fn s x * indicator_fn t y)
Proof
    rpt STRIP_TAC
 >> rw [IN_FCP_CROSS, indicator_fn_def] (* 4 subgoals *)
 >> METIS_TAC [FCP_CONCAT_11]
QED

Theorem indicator_fn_general_cross :
    !(cons :'a -> 'b -> 'c) car cdr (s :'a set) (t :'b set) x y.
        pair_operation cons car cdr ==>
       (indicator_fn (general_cross cons s t) (cons x y) =
        indicator_fn s x * indicator_fn t y)
Proof
    rpt STRIP_TAC
 >> rw [IN_general_cross, indicator_fn_def] (* 4 subgoals *)
 >> METIS_TAC [pair_operation_def]
QED

(* FCP version of ‘prod_sigma’ *)
val fcp_sigma_def = Define
   ‘fcp_sigma a b =
      sigma (fcp_cross (space a) (space b)) (fcp_prod (subsets a) (subsets b))’;

(* FCP version of SIGMA_ALGEBRA_PROD_SIGMA *)
Theorem sigma_algebra_prod_sigma :
    !a b. subset_class (space a) (subsets a) /\
          subset_class (space b) (subsets b) ==> sigma_algebra (fcp_sigma a b)
Proof
    RW_TAC std_ss [fcp_sigma_def]
 >> MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA
 >> RW_TAC std_ss [subset_class_def, IN_FCP_PROD, GSPECIFICATION, IN_FCP_CROSS]
 >> fs [subset_class_def]
 >> RW_TAC std_ss [SUBSET_DEF, IN_FCP_CROSS]
 >> METIS_TAC [SUBSET_DEF]
QED

Theorem sigma_algebra_prod_sigma' =
   Q.GENL [‘X’, ‘Y’, ‘A’, ‘B’]
          (REWRITE_RULE [space_def, subsets_def]
                        (Q.SPECL [‘(X,A)’, ‘(Y,B)’] sigma_algebra_prod_sigma));

val general_sigma_def = Define
   ‘general_sigma (cons :'a -> 'b -> 'c) A B =
      sigma (general_cross cons (space A) (space B))
            (general_prod cons (subsets A) (subsets B))’;

(* alternative definition of ‘prod_sigma’ *)
Theorem prod_sigma_alt :
    !A B. prod_sigma A B = general_sigma pair$, A B
Proof
    RW_TAC std_ss [prod_sigma_def, general_sigma_def,
                   GSYM CROSS_ALT, GSYM prod_sets_alt]
QED

(* alternative definition of ‘fcp_sigma’ *)
Theorem fcp_sigma_alt :
    !A B. fcp_sigma A B = general_sigma FCP_CONCAT A B
Proof
    RW_TAC std_ss [fcp_sigma_def, general_sigma_def,
                   GSYM fcp_cross_alt, GSYM fcp_prod_alt]
QED

Theorem sigma_algebra_general_sigma :
    !(cons :'a -> 'b -> 'c) A B.
        subset_class (space A) (subsets A) /\
        subset_class (space B) (subsets B) ==> sigma_algebra (general_sigma cons A B)
Proof
    RW_TAC std_ss [general_sigma_def]
 >> MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA
 >> RW_TAC std_ss [subset_class_def, IN_general_prod, GSPECIFICATION, IN_general_cross]
 >> fs [subset_class_def]
 >> RW_TAC std_ss [SUBSET_DEF, IN_general_cross]
 >> qexistsl_tac [‘a'’, ‘b'’] >> art []
 >> METIS_TAC [SUBSET_DEF]
QED

Theorem exhausting_sequence_general_cross :
    !(cons :'a -> 'b -> 'c) X Y A B f g.
       exhausting_sequence (X,A) f /\ exhausting_sequence (Y,B) g ==>
       exhausting_sequence (general_cross cons X Y,general_prod cons A B)
                           (\n. general_cross cons (f n) (g n))
Proof
    RW_TAC std_ss [exhausting_sequence_alt, space_def, subsets_def,
                   IN_FUNSET, IN_UNIV, IN_general_prod] (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      qexistsl_tac [‘f n’, ‘g n’] >> art [],
      (* goal 2 (of 3) *)
      rw [SUBSET_DEF, IN_general_cross] \\
      qexistsl_tac [‘a’, ‘b’] >> art [] \\
      METIS_TAC [SUBSET_DEF],
      (* goal 3 (of 3) *)
      simp [Once EXTENSION, IN_BIGUNION_IMAGE, IN_general_cross, IN_UNIV] \\
      GEN_TAC >> EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
      [ (* goal 3.1 (of 2) *)
        qexistsl_tac [‘a’,‘b’] >> art [] \\
        CONJ_TAC >> Q.EXISTS_TAC ‘n’ >> art [],
        (* goal 3.2 (of 2) *)
        rename1 ‘a IN f n1’ \\
        rename1 ‘b IN g n2’ \\
        Q.EXISTS_TAC ‘MAX n1 n2’ \\
        qexistsl_tac [‘a’, ‘b’] >> art [] \\
        CONJ_TAC >| (* 2 subgoals *)
        [ Suff ‘f n1 SUBSET f (MAX n1 n2)’ >- METIS_TAC [SUBSET_DEF] \\
          FIRST_X_ASSUM MATCH_MP_TAC >> RW_TAC arith_ss [],
          Suff ‘g n2 SUBSET g (MAX n1 n2)’ >- METIS_TAC [SUBSET_DEF] \\
          FIRST_X_ASSUM MATCH_MP_TAC >> RW_TAC arith_ss [] ] ] ]
QED

Theorem exhausting_sequence_CROSS :
    !X Y A B f g.
       exhausting_sequence (X,A) f /\ exhausting_sequence (Y,B) g ==>
       exhausting_sequence (X CROSS Y,prod_sets A B) (\n. f n CROSS g n)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘pair$,’, ‘X’, ‘Y’, ‘A’, ‘B’, ‘f’, ‘g’]
                    (INST_TYPE [gamma |-> “:'a # 'b”] exhausting_sequence_general_cross))
 >> RW_TAC std_ss [GSYM CROSS_ALT, GSYM prod_sets_alt]
QED

(* FCP version of exhausting_sequence_CROSS *)
Theorem exhausting_sequence_cross :
    !X Y A B f g.
       exhausting_sequence (X,A) f /\ exhausting_sequence (Y,B) g ==>
       exhausting_sequence (fcp_cross X Y,fcp_prod A B) (\n. fcp_cross (f n) (g n))
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘FCP_CONCAT’, ‘X’, ‘Y’, ‘A’, ‘B’, ‘f’, ‘g’]
                    (((INST_TYPE [“:'temp1” |-> “:'a['b]”]) o
                      (INST_TYPE [“:'temp2” |-> “:'a['c]”]) o
                      (INST_TYPE [gamma |-> “:'a['b + 'c]”]) o
                      (INST_TYPE [alpha |-> “:'temp1”]) o
                      (INST_TYPE [beta |-> “:'temp2”]))
                         exhausting_sequence_general_cross))
 >> RW_TAC std_ss [GSYM fcp_cross_alt, GSYM fcp_prod_alt]
QED

Theorem general_sigma_of_generator :
    !(cons :'a -> 'b -> 'c) (car :'c -> 'a) (cdr :'c -> 'b) (X :'a set) (Y :'b set) E G.
        pair_operation cons car cdr /\
        subset_class X E /\ subset_class Y G /\
        has_exhausting_sequence (X,E) /\ has_exhausting_sequence (Y,G) ==>
       (general_sigma cons (X,E) (Y,G) = general_sigma cons (sigma X E) (sigma Y G))
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘A = sigma X E’
 >> Q.ABBREV_TAC ‘B = sigma Y G’
 >> ONCE_REWRITE_TAC [GSYM SPACE]
 >> ‘general_cross cons (space A) (space B) = general_cross cons X Y’
       by METIS_TAC [SPACE_SIGMA]
 >> Suff ‘subsets (general_sigma cons (X,E) (Y,G)) = subsets (general_sigma cons A B)’
 >- (Know ‘space (general_sigma cons (X,E) (Y,G)) = space (general_sigma cons A B)’
     >- (rw [general_sigma_def, SPACE_SIGMA] \\
         METIS_TAC [SPACE_SIGMA]) >> Rewr' >> Rewr)
 >> rw [SET_EQ_SUBSET] (* 2 subgoals *)
 (* Part I: easy, ‘has_exhausting_sequence’ is not used *)
 >- (rw [general_sigma_def] \\
     MATCH_MP_TAC SIGMA_MONOTONE \\
     rw [IN_general_prod, SUBSET_DEF, GSPECIFICATION] \\
     qexistsl_tac [‘a’,‘b’] >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.UNABBREV_TAC ‘A’ \\
       METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF],
       (* goal 2 (of 2) *)
       Q.UNABBREV_TAC ‘B’ \\
       METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF] ])
 >> ‘sigma_algebra A /\ sigma_algebra B’ by METIS_TAC [SIGMA_ALGEBRA_SIGMA]
 >> ‘sigma_algebra (general_sigma cons (X,E) (Y,G))’
      by (MATCH_MP_TAC sigma_algebra_general_sigma >> rw [])
 (* Part II: hard *)
 >> Q.ABBREV_TAC ‘S = {a | a IN subsets A /\
                          !g. g IN G ==> (general_cross cons a g) IN
                                            subsets (general_sigma cons (X,E) (Y,G))}’
 >> Know ‘sigma_algebra (X,S)’
 >- (simp [SIGMA_ALGEBRA_ALT_SPACE] \\
     CONJ_TAC (* subset_class *)
     >- (RW_TAC std_ss [subset_class_def, Abbr ‘S’, GSPECIFICATION] \\
        ‘X = space A’ by PROVE_TAC [SPACE_SIGMA] >> POP_ORW \\
         METIS_TAC [subset_class_def, SIGMA_ALGEBRA_ALT_SPACE]) \\
     STRONG_CONJ_TAC (* space *)
     >- (RW_TAC std_ss [Abbr ‘S’, GSPECIFICATION]
         >- (‘X = space A’ by PROVE_TAC [SPACE_SIGMA] >> POP_ORW \\
             fs [SIGMA_ALGEBRA_ALT_SPACE]) \\
        ‘?f. f IN (univ(:num) -> E) /\ (!n. f n SUBSET f (SUC n)) /\
             (BIGUNION (IMAGE f univ(:num)) = X)’
           by METIS_TAC [has_exhausting_sequence_def, space_def, subsets_def] \\
         POP_ASSUM (* rewrite only LHS *)
           ((GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites) o wrap o SYM) \\
         REWRITE_TAC [general_BIGUNION_CROSS] \\
         MATCH_MP_TAC SIGMA_ALGEBRA_ENUM >> art [] \\
         rw [general_sigma_def, IN_FUNSET, IN_UNIV] \\
         MATCH_MP_TAC IN_SIGMA \\
         RW_TAC std_ss [general_prod_def, GSPECIFICATION, IN_general_cross] \\
         Q.EXISTS_TAC ‘(f n,g)’ >> fs [IN_FUNSET]) >> DISCH_TAC \\
     CONJ_TAC (* DIFF *)
     >- (GEN_TAC >> fs [Abbr ‘S’, GSPECIFICATION] >> STRIP_TAC \\
         CONJ_TAC >- (‘X = space A’ by PROVE_TAC [SPACE_SIGMA] >> POP_ORW \\
                      fs [SIGMA_ALGEBRA_ALT_SPACE]) \\
         rpt STRIP_TAC \\
         Know ‘general_cross cons (X DIFF s) g =
                 (general_cross cons X g) DIFF (general_cross cons s g)’
         >- (MATCH_MP_TAC general_CROSS_DIFF \\
             qexistsl_tac [‘car’, ‘cdr’] >> art []) >> Rewr' \\
         MATCH_MP_TAC SIGMA_ALGEBRA_DIFF >> simp []) \\
     RW_TAC std_ss [IN_FUNSET, IN_UNIV] \\
     fs [Abbr ‘S’, GSPECIFICATION] \\
     CONJ_TAC >- (MATCH_MP_TAC SIGMA_ALGEBRA_ENUM >> rw [IN_FUNSET, IN_UNIV]) \\
     RW_TAC std_ss [general_BIGUNION_CROSS] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_ENUM >> art [] \\
     rw [general_sigma_def, IN_FUNSET, IN_UNIV]) >> DISCH_TAC
 (* showing ‘E SUBSET S SUBSET subsets A’ *)
 >> Know ‘E SUBSET S’
 >- (RW_TAC std_ss [Abbr ‘S’, SUBSET_DEF, GSPECIFICATION]
     >- (Q.UNABBREV_TAC ‘A’ >> MATCH_MP_TAC IN_SIGMA >> art []) \\
     rw [general_sigma_def] >> MATCH_MP_TAC IN_SIGMA \\
     RW_TAC std_ss [IN_general_prod] \\
     qexistsl_tac [‘x’, ‘g’] >> art []) >> DISCH_TAC
 >> ‘S SUBSET subsets A’
       by (RW_TAC std_ss [Abbr ‘S’, SUBSET_DEF, GSPECIFICATION])
 >> Know ‘S = subsets A’
 >- (Q.UNABBREV_TAC ‘A’ \\
     MATCH_MP_TAC SIGMA_SMALLEST >> art []) >> DISCH_TAC
 >> Know ‘(general_prod cons (subsets A) G) SUBSET
          (subsets (general_sigma cons (X,E) (Y,G)))’
 >- (simp [IN_general_prod, SUBSET_DEF, GSPECIFICATION] \\
     rpt STRIP_TAC >> Know ‘a IN S’ >- PROVE_TAC [] \\
     rw [Abbr ‘S’, GSPECIFICATION])
 (* clean up all assumptions about S *)
 >> NTAC 4 (POP_ASSUM K_TAC) >> Q.UNABBREV_TAC ‘S’
 >> DISCH_TAC
 (* Part III: hard *)
 >> Q.ABBREV_TAC ‘S = {b | b IN subsets B /\
                          !e. e IN E ==>
                             (general_cross cons e b) IN subsets (general_sigma cons (X,E) (Y,G))}’
 >> Know ‘sigma_algebra (Y,S)’
 >- (simp [SIGMA_ALGEBRA_ALT_SPACE] \\
     CONJ_TAC (* subset_class *)
     >- (RW_TAC std_ss [subset_class_def, Abbr ‘S’, GSPECIFICATION] \\
        ‘Y = space B’ by PROVE_TAC [SPACE_SIGMA] >> POP_ORW \\
         METIS_TAC [subset_class_def, SIGMA_ALGEBRA_ALT_SPACE]) \\
     STRONG_CONJ_TAC (* space *)
     >- (RW_TAC std_ss [Abbr ‘S’, GSPECIFICATION]
         >- (‘Y = space B’ by PROVE_TAC [SPACE_SIGMA] >> POP_ORW \\
             fs [SIGMA_ALGEBRA_ALT_SPACE]) \\
        ‘?f. f IN (univ(:num) -> G) /\ (!n. f n SUBSET f (SUC n)) /\
             (BIGUNION (IMAGE f univ(:num)) = Y)’
           by METIS_TAC [has_exhausting_sequence_def, space_def, subsets_def] \\
         POP_ASSUM (* rewrite only LHS *)
           ((GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites) o wrap o SYM) \\
         REWRITE_TAC [general_CROSS_BIGUNION] \\
         MATCH_MP_TAC SIGMA_ALGEBRA_ENUM >> art [] \\
         rw [general_sigma_def, IN_FUNSET, IN_UNIV] \\
         MATCH_MP_TAC IN_SIGMA \\
         RW_TAC std_ss [IN_general_prod] \\
         qexistsl_tac [‘e’, ‘f n’] >> art [] \\
         fs [IN_FUNSET, IN_UNIV]) >> DISCH_TAC \\
     CONJ_TAC (* DIFF *)
     >- (GEN_TAC >> fs [Abbr ‘S’, GSPECIFICATION] >> STRIP_TAC \\
         CONJ_TAC >- (‘Y = space B’ by PROVE_TAC [SPACE_SIGMA] >> POP_ORW \\
                      fs [SIGMA_ALGEBRA_ALT_SPACE]) \\
         rpt STRIP_TAC \\
         Know ‘general_cross cons e (Y DIFF s) =
                (general_cross cons e Y) DIFF (general_cross cons e s)’
         >- (MATCH_MP_TAC general_CROSS_DIFF' \\
             qexistsl_tac [‘car’, ‘cdr’] >> art []) >> Rewr' \\
         MATCH_MP_TAC SIGMA_ALGEBRA_DIFF >> rw []) \\
     RW_TAC std_ss [IN_FUNSET, IN_UNIV] \\
     fs [Abbr ‘S’, GSPECIFICATION] \\
     CONJ_TAC
     >- (MATCH_MP_TAC SIGMA_ALGEBRA_ENUM >> rw [IN_FUNSET, IN_UNIV]) \\
     RW_TAC std_ss [general_CROSS_BIGUNION] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_ENUM >> art [] \\
     rw [general_sigma_def, IN_FUNSET, IN_UNIV]) >> DISCH_TAC
 (* showing ‘E SUBSET S SUBSET subsets A’ *)
 >> Know ‘G SUBSET S’
 >- (RW_TAC std_ss [Abbr ‘S’, SUBSET_DEF, GSPECIFICATION]
     >- (Q.UNABBREV_TAC ‘B’ \\
         MATCH_MP_TAC IN_SIGMA >> art []) \\
     rw [general_sigma_def] >> MATCH_MP_TAC IN_SIGMA \\
     RW_TAC std_ss [IN_general_prod] \\
     qexistsl_tac [‘e’,‘x’] >> art []) >> DISCH_TAC
 >> ‘S SUBSET subsets B’
       by (RW_TAC std_ss [Abbr ‘S’, SUBSET_DEF, GSPECIFICATION])
 >> Know ‘S = subsets B’
 >- (Q.UNABBREV_TAC ‘B’ \\
     MATCH_MP_TAC SIGMA_SMALLEST >> art []) >> DISCH_TAC
 >> Know ‘(general_prod cons E (subsets B)) SUBSET
          (subsets (general_sigma cons (X,E) (Y,G)))’
 >- (simp [IN_general_prod, SUBSET_DEF, GSPECIFICATION] \\
     rpt STRIP_TAC >> Know ‘b IN S’ >- PROVE_TAC [] \\
     rw [Abbr ‘S’, GSPECIFICATION])
 (* clean up all assumptions about S *)
 >> NTAC 4 (POP_ASSUM K_TAC) >> Q.UNABBREV_TAC ‘S’
 >> DISCH_TAC
 (* Part IV: final stage *)
 >> GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [general_sigma_def]
 >> Q.PAT_X_ASSUM ‘general_cross cons (space A) (space B) =
                   general_cross cons X Y’ (ONCE_REWRITE_TAC o wrap)
 >> Suff ‘general_prod cons (subsets A) (subsets B) SUBSET
          subsets (general_sigma cons (X,E) (Y,G))’
 >- (DISCH_TAC \\
     ASSUME_TAC (Q.SPEC ‘general_cross cons X Y’
                        (INST_TYPE [alpha |-> gamma] SIGMA_MONOTONE)) \\
     POP_ASSUM (MP_TAC o (Q.SPEC ‘general_prod cons (subsets A) (subsets B)’)) \\
     DISCH_THEN (MP_TAC o (Q.SPEC ‘subsets (general_sigma cons (X,E) (Y,G))’)) \\
     RW_TAC std_ss [] \\
     Suff ‘sigma (general_cross cons X Y) (subsets (general_sigma cons (X,E) (Y,G))) =
           general_sigma cons (X,E) (Y,G)’
     >- (DISCH_THEN (fs o wrap)) \\
    ‘general_cross cons X Y = space (general_sigma cons (X,E) (Y,G))’
        by (rw [general_sigma_def, SPACE_SIGMA]) \\
     POP_ORW >> MATCH_MP_TAC SIGMA_STABLE >> art [])
 >> RW_TAC std_ss [IN_general_prod, GSPECIFICATION, SUBSET_DEF]
 (* final goal: a CROSS b IN subsets ((X,E) CROSS (Y,G)) *)
 >> Know ‘general_cross cons a b =
            (general_cross cons a Y) INTER (general_cross cons X b)’
 >- (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_general_cross] \\
     EQ_TAC >> RW_TAC std_ss [] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       qexistsl_tac [‘a'’,‘b'’] >> art [] \\
       Suff ‘b SUBSET Y’ >- rw [SUBSET_DEF] \\
      ‘subset_class (space B) (subsets B)’
         by METIS_TAC [sigma_algebra_def, algebra_def, subset_class_def] \\
      ‘Y = space B’ by PROVE_TAC [SPACE_SIGMA] >> POP_ORW \\
       METIS_TAC [subset_class_def],
       (* goal 2 (of 3) *)
       qexistsl_tac [‘a'’,‘b'’] >> art [] \\
       Suff ‘a SUBSET X’ >- rw [SUBSET_DEF] \\
      ‘subset_class (space A) (subsets A)’
         by METIS_TAC [sigma_algebra_def, algebra_def, subset_class_def] \\
      ‘X = space A’ by PROVE_TAC [SPACE_SIGMA] >> POP_ORW \\
       METIS_TAC [subset_class_def],
       (* goal 3 (of 3) *)
       rename1 ‘cons a1 b1 = cons a2 b2’ \\
       qexistsl_tac [‘a2’,‘b2’] >> art [] \\
       Suff ‘b1 = b2’ >- PROVE_TAC [] \\
       METIS_TAC [pair_operation_def] ]) >> Rewr'
 >> ‘?e. e IN (univ(:num) -> E) /\ (!n. e n SUBSET e (SUC n)) /\
         (BIGUNION (IMAGE e univ(:num)) = X)’
      by METIS_TAC [has_exhausting_sequence_def, space_def, subsets_def]
 >> POP_ASSUM (* rewrite only LHS *)
      ((GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites) o wrap o SYM)
 >> ‘?g. g IN (univ(:num) -> G) /\ (!n. g n SUBSET g (SUC n)) /\
         (BIGUNION (IMAGE g univ(:num)) = Y)’
      by METIS_TAC [has_exhausting_sequence_def, space_def, subsets_def]
 >> POP_ASSUM (* rewrite only LHS *)
      ((GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites) o wrap o SYM)
 >> REWRITE_TAC [general_CROSS_BIGUNION, general_BIGUNION_CROSS]
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
 >> Q.PAT_X_ASSUM ‘sigma_algebra (general_sigma cons (X,E) (Y,G))’
      (STRIP_ASSUME_TAC o
       (REWRITE_RULE [SIGMA_ALGEBRA_ALT_SPACE, IN_FUNSET, IN_UNIV]))
 >> CONJ_TAC
 >| [ (* goal 1 (of 2) *)
      POP_ASSUM MATCH_MP_TAC >> Q.X_GEN_TAC ‘n’ >> BETA_TAC \\
      Suff ‘general_cross cons a (g n) IN general_prod cons (subsets A) G’
      >- PROVE_TAC [SUBSET_DEF] \\
      RW_TAC std_ss [IN_general_prod] \\
      qexistsl_tac [‘a’, ‘g n’] >> fs [IN_FUNSET, IN_UNIV],
      (* goal 2 (of 2) *)
      POP_ASSUM MATCH_MP_TAC >> Q.X_GEN_TAC ‘n’ >> BETA_TAC \\
      Suff ‘general_cross cons (e n) b IN general_prod cons E (subsets B)’
      >- PROVE_TAC [SUBSET_DEF] \\
      RW_TAC std_ss [IN_general_prod] \\
      qexistsl_tac [‘e n’, ‘b’] >> fs [IN_FUNSET, IN_UNIV] ]
QED

(* Lemma 14.3 [1, p.138], reducing consideration of ‘prod_sigma’ to generators *)
Theorem PROD_SIGMA_OF_GENERATOR :
    !X Y E G. subset_class X E /\ subset_class Y G /\
              has_exhausting_sequence (X,E) /\
              has_exhausting_sequence (Y,G) ==>
             ((X,E) CROSS (Y,G) = (sigma X E) CROSS (sigma Y G))
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘pair$,’, ‘FST’, ‘SND’, ‘X’, ‘Y’, ‘E’, ‘G’]
                    (INST_TYPE [gamma |-> “:'a # 'b”] general_sigma_of_generator))
 >> RW_TAC std_ss [GSYM CROSS_ALT, GSYM prod_sets_alt, GSYM prod_sigma_alt,
                   pair_operation_pair]
QED

(* FCP version of PROD_SIGMA_OF_GENERATOR *)
Theorem prod_sigma_of_generator :
    !(X :'a['b] set) (Y :'a['c] set) E G.
        FINITE univ(:'b) /\ FINITE univ(:'c) /\
        subset_class X E /\ subset_class Y G /\
        has_exhausting_sequence (X,E) /\
        has_exhausting_sequence (Y,G) ==>
       (fcp_sigma (X,E) (Y,G) = fcp_sigma (sigma X E) (sigma Y G))
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘FCP_CONCAT’, ‘FCP_FST’, ‘FCP_SND’, ‘X’, ‘Y’, ‘E’, ‘G’]
                    (((INST_TYPE [“:'temp1” |-> “:'a['b]”]) o
                      (INST_TYPE [“:'temp2” |-> “:'a['c]”]) o
                      (INST_TYPE [gamma |-> “:'a['b + 'c]”]) o
                      (INST_TYPE [alpha |-> “:'temp1”]) o
                      (INST_TYPE [beta |-> “:'temp2”])) general_sigma_of_generator))
 >> RW_TAC std_ss [GSYM fcp_cross_alt, GSYM fcp_prod_alt, GSYM fcp_sigma_alt,
                   pair_operation_FCP_CONCAT]
QED

Theorem uniqueness_of_prod_measure_general :
    !(cons :'a -> 'b -> 'c) (car :'c -> 'a) (cdr :'c -> 'b)
     (X :'a set) (Y :'b set) E G A B u v m m'.
      pair_operation cons car cdr /\
      subset_class X E /\ subset_class Y G /\
      sigma_finite (X,E,u) /\ sigma_finite (Y,G,v) /\
     (!s t. s IN E /\ t IN E ==> s INTER t IN E) /\
     (!s t. s IN G /\ t IN G ==> s INTER t IN G) /\
     (A = sigma X E) /\ (B = sigma Y G) /\
      measure_space (X,subsets A,u) /\
      measure_space (Y,subsets B,v) /\
      measure_space (general_cross cons X Y,subsets (general_sigma cons A B),m) /\
      measure_space (general_cross cons X Y,subsets (general_sigma cons A B),m') /\
     (!s t. s IN E /\ t IN G ==> (m  (general_cross cons s t) = u s * v t)) /\
     (!s t. s IN E /\ t IN G ==> (m' (general_cross cons s t) = u s * v t)) ==>
      !x. x IN subsets (general_sigma cons A B) ==> (m x = m' x)
Proof
    rpt GEN_TAC >> STRIP_TAC
 (* applying PROD_SIGMA_OF_GENERATOR *)
 >> Know ‘general_sigma cons A B = general_sigma cons (X,E) (Y,G)’
 >- (simp [Once EQ_SYM_EQ] \\
     MATCH_MP_TAC general_sigma_of_generator >> art [] \\
     qexistsl_tac [‘car’, ‘cdr’] \\
     PROVE_TAC [sigma_finite_has_exhausting_sequence]) >> Rewr'
 >> REWRITE_TAC [general_sigma_def, space_def, subsets_def]
 >> MATCH_MP_TAC UNIQUENESS_OF_MEASURE
 >> ‘sigma_algebra A /\ sigma_algebra B’ by PROVE_TAC [SIGMA_ALGEBRA_SIGMA]
 >> CONJ_TAC (* subset_class *)
 >- (rw [subset_class_def, IN_general_prod, GSPECIFICATION] \\
     MATCH_MP_TAC general_SUBSET_CROSS \\
     fs [subset_class_def])
 >> CONJ_TAC (* INTER-stable *)
 >- (qx_genl_tac [‘a’, ‘b’] \\
     simp [IN_general_prod] >> STRIP_TAC \\
     rename1 ‘a = general_cross cons a1 b1’ \\
     rename1 ‘b = general_cross cons a2 b2’ \\
     qexistsl_tac [‘a1 INTER a2’, ‘b1 INTER b2’] \\
     CONJ_TAC >- (art [] >> MATCH_MP_TAC general_INTER_CROSS \\
                  qexistsl_tac [‘car’, ‘cdr’] >> art []) \\
     PROVE_TAC [])
 >> CONJ_TAC (* sigma_finite *)
 >- (fs [sigma_finite_alt_exhausting_sequence] \\
     Q.EXISTS_TAC ‘\n. general_cross cons (f n) (f' n)’ \\
     CONJ_TAC >- (MATCH_MP_TAC exhausting_sequence_general_cross >> art []) \\
     Q.X_GEN_TAC ‘n’ >> BETA_TAC >> simp [] \\
    ‘positive (X,subsets A,u) /\
     positive (Y,subsets B,v)’ by PROVE_TAC [MEASURE_SPACE_POSITIVE] \\
     fs [GSYM lt_infty] \\
    ‘E SUBSET subsets A /\ G SUBSET subsets B’ by METIS_TAC [SIGMA_SUBSET_SUBSETS] \\
     rename1 ‘!n. v (g n) <> PosInf’ \\
     fs [exhausting_sequence_def, IN_FUNSET, IN_UNIV] \\
    ‘f n IN subsets A /\ g n IN subsets B’ by METIS_TAC [SUBSET_DEF] \\
    ‘u (f n) <> NegInf /\ v (g n) <> NegInf’
       by METIS_TAC [positive_not_infty, measurable_sets_def, measure_def] \\
    ‘?r1. u (f n) = Normal r1’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?r2. v (g n) = Normal r2’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     REWRITE_TAC [extreal_mul_def, extreal_not_infty])
 (* applying PROD_SIGMA_OF_GENERATOR again *)
 >> Know ‘general_sigma cons (X,E) (Y,G) = general_sigma cons A B’
 >- (simp [] >> MATCH_MP_TAC general_sigma_of_generator >> art [] \\
     PROVE_TAC [sigma_finite_has_exhausting_sequence])
 >> DISCH_THEN (MP_TAC o
                (GEN_REWRITE_RULE (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites
                                  [general_sigma_def]))
 >> REWRITE_TAC [space_def, subsets_def] >> Rewr' >> art []
 >> RW_TAC std_ss [IN_general_prod]
 >> METIS_TAC []
QED

(* Theorem 14.4 [1, p.139], cf. UNIQUENESS_OF_MEASURE *)
Theorem UNIQUENESS_OF_PROD_MEASURE :
    !(X :'a set) (Y :'b set) E G A B u v m m'.
      subset_class X E /\ subset_class Y G /\
      sigma_finite (X,E,u) /\ sigma_finite (Y,G,v) /\
     (!s t. s IN E /\ t IN E ==> s INTER t IN E) /\
     (!s t. s IN G /\ t IN G ==> s INTER t IN G) /\
     (A = sigma X E) /\ (B = sigma Y G) /\
      measure_space (X,subsets A,u) /\
      measure_space (Y,subsets B,v) /\
      measure_space (X CROSS Y,subsets (A CROSS B),m) /\
      measure_space (X CROSS Y,subsets (A CROSS B),m') /\
     (!s t. s IN E /\ t IN G ==> (m  (s CROSS t) = u s * v t)) /\
     (!s t. s IN E /\ t IN G ==> (m' (s CROSS t) = u s * v t)) ==>
      !x. x IN subsets (A CROSS B) ==> (m x = m' x)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘pair$,’,‘FST’,‘SND’,‘X’,‘Y’,‘E’,‘G’,‘A’,‘B’,‘u’,‘v’,‘m’,‘m'’]
                    (INST_TYPE [gamma |-> “:'a # 'b”] uniqueness_of_prod_measure_general))
 >> RW_TAC std_ss [GSYM CROSS_ALT, GSYM prod_sets_alt, GSYM prod_sigma_alt,
                   pair_operation_pair]
QED

(* FCP version of UNIQUENESS_OF_PROD_MEASURE *)
Theorem uniqueness_of_prod_measure :
    !(X :'a['b] set) (Y :'a['c] set) E G A B u v m m'.
      FINITE univ(:'b) /\ FINITE univ(:'c) /\
      subset_class X E /\ subset_class Y G /\
      sigma_finite (X,E,u) /\ sigma_finite (Y,G,v) /\
     (!s t. s IN E /\ t IN E ==> s INTER t IN E) /\
     (!s t. s IN G /\ t IN G ==> s INTER t IN G) /\
     (A = sigma X E) /\ (B = sigma Y G) /\
      measure_space (X,subsets A,u) /\
      measure_space (Y,subsets B,v) /\
      measure_space (fcp_cross X Y,subsets (fcp_sigma A B),m) /\
      measure_space (fcp_cross X Y,subsets (fcp_sigma A B),m') /\
     (!s t. s IN E /\ t IN G ==> (m  (fcp_cross s t) = u s * v t)) /\
     (!s t. s IN E /\ t IN G ==> (m' (fcp_cross s t) = u s * v t)) ==>
      !x. x IN subsets (fcp_sigma A B) ==> (m x = m' x)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘FCP_CONCAT’,‘FCP_FST’,‘FCP_SND’,‘X’,‘Y’,‘E’,‘G’,‘A’,‘B’,‘u’,‘v’,‘m’,‘m'’]
                    (((INST_TYPE [“:'temp1” |-> “:'a['b]”]) o
                      (INST_TYPE [“:'temp2” |-> “:'a['c]”]) o
                      (INST_TYPE [gamma |-> “:'a['b + 'c]”]) o
                      (INST_TYPE [alpha |-> “:'temp1”]) o
                      (INST_TYPE [beta |-> “:'temp2”])) uniqueness_of_prod_measure_general))
 >> RW_TAC std_ss [GSYM fcp_cross_alt, GSYM fcp_prod_alt, GSYM fcp_sigma_alt,
                   pair_operation_FCP_CONCAT]
QED

Theorem uniqueness_of_prod_measure_general' :
    !(cons :'a -> 'b -> 'c) (car :'c -> 'a) (cdr :'c -> 'b)
     (X :'a set) (Y :'b set) A B u v m m'.
      pair_operation cons car cdr /\
      sigma_finite_measure_space (X,A,u) /\
      sigma_finite_measure_space (Y,B,v) /\
      measure_space (general_cross cons X Y,subsets (general_sigma cons (X,A) (Y,B)),m) /\
      measure_space (general_cross cons X Y,subsets (general_sigma cons (X,A) (Y,B)),m') /\
     (!s t. s IN A /\ t IN B ==> (m  (general_cross cons s t) = u s * v t)) /\
     (!s t. s IN A /\ t IN B ==> (m' (general_cross cons s t) = u s * v t)) ==>
      !x. x IN subsets (general_sigma cons (X,A) (Y,B)) ==> (m x = m' x)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘cons’,‘car’,‘cdr’,‘X’,‘Y’,‘A’,‘B’,‘(X,A)’,‘(Y,B)’,‘u’,‘v’,‘m’,‘m'’]
                    uniqueness_of_prod_measure_general)
 >> fs [sigma_finite_measure_space_def]
 >> ‘sigma_algebra (X,A) /\ sigma_algebra (Y,B)’
      by METIS_TAC [measure_space_def, m_space_def, measurable_sets_def]
 >> ‘sigma X A = (X,A) /\ sigma Y B = (Y,B)’
      by METIS_TAC [SIGMA_STABLE, space_def, subsets_def]
 >> Know ‘!s t. s IN A /\ t IN A ==> s INTER t IN A’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC (REWRITE_RULE [space_def, subsets_def]
                                (Q.SPEC ‘(X,A)’ SIGMA_ALGEBRA_INTER)) \\
     ASM_REWRITE_TAC [])
 >> Know ‘!s t. s IN B /\ t IN B ==> s INTER t IN B’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC (REWRITE_RULE [space_def, subsets_def]
                                (Q.SPEC ‘(Y,B)’ SIGMA_ALGEBRA_INTER)) \\
     ASM_REWRITE_TAC [])
 >> RW_TAC std_ss []
 >> FIRST_X_ASSUM irule
 >> fs [sigma_algebra_def, algebra_def]
QED

(* A specialized version for sigma-algebras instead of generators *)
Theorem UNIQUENESS_OF_PROD_MEASURE' :
    !(X :'a set) (Y :'b set) A B u v m m'.
      sigma_finite_measure_space (X,A,u) /\
      sigma_finite_measure_space (Y,B,v) /\
      measure_space (X CROSS Y,subsets ((X,A) CROSS (Y,B)),m) /\
      measure_space (X CROSS Y,subsets ((X,A) CROSS (Y,B)),m') /\
     (!s t. s IN A /\ t IN B ==> (m  (s CROSS t) = u s * v t)) /\
     (!s t. s IN A /\ t IN B ==> (m' (s CROSS t) = u s * v t)) ==>
      !x. x IN subsets ((X,A) CROSS (Y,B)) ==> (m x = m' x)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘pair$,’,‘FST’,‘SND’,‘X’,‘Y’,‘A’,‘B’,‘u’,‘v’,‘m’,‘m'’]
                    (INST_TYPE [gamma |-> “:'a # 'b”] uniqueness_of_prod_measure_general'))
 >> RW_TAC std_ss [GSYM CROSS_ALT, GSYM prod_sets_alt, GSYM prod_sigma_alt,
                   pair_operation_pair]
QED

(* FCP version of UNIQUENESS_OF_PROD_MEASURE' *)
Theorem uniqueness_of_prod_measure' :
    !(X :'a['b] set) (Y :'a['c] set) A B u v m m'.
      FINITE univ(:'b) /\ FINITE univ(:'c) /\
      sigma_finite_measure_space (X,A,u) /\
      sigma_finite_measure_space (Y,B,v) /\
      measure_space (fcp_cross X Y,subsets (fcp_sigma (X,A) (Y,B)),m) /\
      measure_space (fcp_cross X Y,subsets (fcp_sigma (X,A) (Y,B)),m') /\
     (!s t. s IN A /\ t IN B ==> (m  (fcp_cross s t) = u s * v t)) /\
     (!s t. s IN A /\ t IN B ==> (m' (fcp_cross s t) = u s * v t)) ==>
      !x. x IN subsets (fcp_sigma (X,A) (Y,B)) ==> (m x = m' x)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘FCP_CONCAT’,‘FCP_FST’,‘FCP_SND’,‘X’,‘Y’,‘A’,‘B’,‘u’,‘v’,‘m’,‘m'’]
                    (((INST_TYPE [“:'temp1” |-> “:'a['b]”]) o
                      (INST_TYPE [“:'temp2” |-> “:'a['c]”]) o
                      (INST_TYPE [gamma |-> “:'a['b + 'c]”]) o
                      (INST_TYPE [alpha |-> “:'temp1”]) o
                      (INST_TYPE [beta |-> “:'temp2”])) uniqueness_of_prod_measure_general'))
 >> RW_TAC std_ss [GSYM fcp_cross_alt, GSYM fcp_prod_alt, GSYM fcp_sigma_alt,
                   pair_operation_FCP_CONCAT]
QED

Theorem existence_of_prod_measure_general :
   !(cons :'a -> 'b -> 'c) car cdr (X :'a set) (Y :'b set) A B u v m0.
       pair_operation cons car cdr /\
       sigma_finite_measure_space (X,A,u) /\
       sigma_finite_measure_space (Y,B,v) /\
       (!s t. s IN A /\ t IN B ==> (m0 (general_cross cons s t) = u s * v t)) ==>
       (!s. s IN subsets (general_sigma cons (X,A) (Y,B)) ==>
           (!x. x IN X ==> (\y. indicator_fn s (cons x y)) IN measurable (Y,B) Borel) /\
           (!y. y IN Y ==> (\x. indicator_fn s (cons x y)) IN measurable (X,A) Borel) /\
           (\y. pos_fn_integral (X,A,u)
                  (\x. indicator_fn s (cons x y))) IN measurable (Y,B) Borel /\
           (\x. pos_fn_integral (Y,B,v)
                  (\y. indicator_fn s (cons x y))) IN measurable (X,A) Borel) /\
       ?m. sigma_finite_measure_space (general_cross cons X Y,
                                       subsets (general_sigma cons (X,A) (Y,B)),m) /\
           (!s. s IN (general_prod cons A B) ==> (m s = m0 s)) /\
           (!s. s IN subsets (general_sigma cons (X,A) (Y,B)) ==>
               (m s = pos_fn_integral (Y,B,v)
                        (\y. pos_fn_integral (X,A,u) (\x. indicator_fn s (cons x y)))) /\
               (m s = pos_fn_integral (X,A,u)
                        (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn s (cons x y)))))
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> fs [sigma_finite_measure_space_def, sigma_finite_alt_exhausting_sequence]
 >> ‘sigma_algebra (X,A) /\ sigma_algebra (Y,B)’
      by PROVE_TAC [measure_space_def, m_space_def, measurable_sets_def,
                    space_def, subsets_def]
 >> rename1 ‘!n. u (a n) < PosInf’
 >> rename1 ‘!n. v (b n) < PosInf’
 >> Q.ABBREV_TAC ‘E = \n. general_cross cons (a n) (b n)’
 (* (D n) is supposed to be a dynkin system *)
 >> Q.ABBREV_TAC ‘D = \n.
     {d | d SUBSET (general_cross cons X Y) /\
          (!x. x IN X ==>
               (\y. indicator_fn (d INTER (E n)) (cons x y)) IN Borel_measurable (Y,B)) /\
          (!y. y IN Y ==>
               (\x. indicator_fn (d INTER (E n)) (cons x y)) IN Borel_measurable (X,A)) /\
          (\y. pos_fn_integral (X,A,u) (\x. indicator_fn (d INTER (E n)) (cons x y)))
                 IN Borel_measurable (Y,B) /\
          (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (d INTER (E n)) (cons x y)))
                 IN Borel_measurable (X,A) /\
          (pos_fn_integral (X,A,u)
             (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (d INTER (E n)) (cons x y))) =
           pos_fn_integral (Y,B,v)
             (\y. pos_fn_integral (X,A,u) (\x. indicator_fn (d INTER (E n)) (cons x y))))}’
 >> Know ‘!n. (general_prod cons A B) SUBSET (D n)’
 >- (rw [IN_general_prod, SUBSET_DEF] \\
     rename1 ‘s IN A’ >> rename1 ‘t IN B’ \\
     Q.UNABBREV_TAC ‘D’ >> BETA_TAC >> simp [GSPECIFICATION] \\
     CONJ_TAC (* (s CROSS t) SUBSET (X CROSS Y) *)
     >- (MATCH_MP_TAC general_SUBSET_CROSS \\
        ‘subset_class X A /\ subset_class Y B’
            by PROVE_TAC [measure_space_def, SIGMA_ALGEBRA_ALT_SPACE, m_space_def,
                          measurable_sets_def, space_def, subsets_def] \\
         fs [subset_class_def]) \\
     Q.UNABBREV_TAC ‘E’ >> BETA_TAC \\
     rfs [exhausting_sequence_def, IN_FUNSET, IN_UNIV] \\
  (* key separation *)
     Know ‘!x y. indicator_fn ((general_cross cons s t) INTER
                               (general_cross cons (a n) (b n))) (cons x y) =
                 indicator_fn (s INTER a n) x * indicator_fn (t INTER b n) y’
     >- (rpt GEN_TAC \\
         Know ‘general_cross cons s t INTER general_cross cons (a n) (b n) =
               general_cross cons (s INTER a n) (t INTER b n)’
         >- (MATCH_MP_TAC general_INTER_CROSS \\
             qexistsl_tac [‘car’, ‘cdr’] >> art []) >> Rewr' \\
         MATCH_MP_TAC indicator_fn_general_cross \\
         qexistsl_tac [‘car’, ‘cdr’] >> art []) >> Rewr' \\
  (* from now on FCP is not needed any more *)
     STRONG_CONJ_TAC (* Borel_measurable #1 *)
     >- (rpt STRIP_TAC \\
        ‘?r. indicator_fn (s INTER a n) x = Normal r’
            by METIS_TAC [indicator_fn_normal] >> POP_ORW \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL_INDICATOR >> art [subsets_def] \\
         MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                    (ISPEC “(Y,B) :'b algebra” SIGMA_ALGEBRA_INTER)) \\
         rw []) >> DISCH_TAC \\
     STRONG_CONJ_TAC (* Borel_measurable #2 *)
     >- (rpt STRIP_TAC >> ONCE_REWRITE_TAC [mul_comm] \\
        ‘?r. indicator_fn (t INTER b n) y = Normal r’
            by METIS_TAC [indicator_fn_normal] >> POP_ORW \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL_INDICATOR >> art [subsets_def] \\
         MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                    (ISPEC “(X,A) :'a algebra” SIGMA_ALGEBRA_INTER)) \\
         rw []) >> DISCH_TAC \\
     STRONG_CONJ_TAC (* Borel_measurable #3 *)
     >- (Know ‘!y. pos_fn_integral (X,A,u) (\x. indicator_fn (s INTER a n) x *
                                                indicator_fn (t INTER b n) y) =
                   indicator_fn (t INTER b n) y *
                   pos_fn_integral (X,A,u) (indicator_fn (s INTER a n))’
         >- (GEN_TAC \\
            ‘?r. 0 <= r /\ (indicator_fn (t INTER b n) y = Normal r)’
                by METIS_TAC [indicator_fn_normal] >> POP_ORW \\
             GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [mul_comm] \\
             MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) >> Rewr' \\
         ONCE_REWRITE_TAC [mul_comm] \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL_INDICATOR' >> art [subsets_def] \\
         MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                    (ISPEC “(Y,B) :'b algebra” SIGMA_ALGEBRA_INTER)) \\
         rw []) >> DISCH_TAC \\
     STRONG_CONJ_TAC (* Borel_measurable #4 *)
     >- (Know ‘!x. pos_fn_integral (Y,B,v) (\y. indicator_fn (s INTER a n) x *
                                                indicator_fn (t INTER b n) y) =
                   indicator_fn (s INTER a n) x *
                   pos_fn_integral (Y,B,v) (indicator_fn (t INTER b n))’
         >- (GEN_TAC \\
            ‘?r. 0 <= r /\ (indicator_fn (s INTER a n) x = Normal r)’
                by METIS_TAC [indicator_fn_normal] >> POP_ORW \\
             MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) >> Rewr' \\
         ONCE_REWRITE_TAC [mul_comm] \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL_INDICATOR' >> art [subsets_def] \\
         MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                    (ISPEC “(X,A) :'a algebra” SIGMA_ALGEBRA_INTER)) \\
         rw []) >> DISCH_TAC \\
     Know ‘!x. pos_fn_integral (Y,B,v) (\y. indicator_fn (s INTER a n) x *
                                            indicator_fn (t INTER b n) y) =
               indicator_fn (s INTER a n) x *
               pos_fn_integral (Y,B,v) (indicator_fn (t INTER b n))’
     >- (GEN_TAC \\
        ‘?r. 0 <= r /\ (indicator_fn (s INTER a n) x = Normal r)’
            by METIS_TAC [indicator_fn_normal] >> POP_ORW \\
         MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) >> Rewr' \\
     Know ‘!y. pos_fn_integral (X,A,u) (\x. indicator_fn (s INTER a n) x *
                                            indicator_fn (t INTER b n) y) =
               indicator_fn (t INTER b n) y *
               pos_fn_integral (X,A,u) (indicator_fn (s INTER a n))’
     >- (GEN_TAC \\
        ‘?r. 0 <= r /\ (indicator_fn (t INTER b n) y = Normal r)’
            by METIS_TAC [indicator_fn_normal] >> POP_ORW \\
         GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [mul_comm] \\
         MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) >> Rewr' \\
     Know ‘pos_fn_integral (Y,B,v) (indicator_fn (t INTER b n)) =
           measure (Y,B,v) (t INTER b n)’
     >- (MATCH_MP_TAC pos_fn_integral_indicator >> art [measurable_sets_def] \\
         MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                    (ISPEC “(Y,B) :'b algebra” SIGMA_ALGEBRA_INTER)) \\
         rw []) >> Rewr' \\
     Know ‘pos_fn_integral (X,A,u) (indicator_fn (s INTER a n)) =
           measure (X,A,u) (s INTER a n)’
     >- (MATCH_MP_TAC pos_fn_integral_indicator >> art [measurable_sets_def] \\
         MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                    (ISPEC “(X,A) :'a algebra” SIGMA_ALGEBRA_INTER)) \\
         rw []) >> Rewr' \\
     ONCE_REWRITE_TAC [mul_comm] >> REWRITE_TAC [measure_def] \\
  (* reduce u() and v() to normal extreals *)
     Know ‘u (s INTER a n) <> PosInf’
     >- (REWRITE_TAC [lt_infty] \\
         MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘u (a n)’ >> art [] \\
         MATCH_MP_TAC (REWRITE_RULE [measurable_sets_def, measure_def]
                                    (Q.SPEC ‘(X,A,u)’ INCREASING)) \\
         CONJ_TAC >- (MATCH_MP_TAC MEASURE_SPACE_INCREASING >> art []) \\
         ASM_REWRITE_TAC [INTER_SUBSET] \\
         MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                    (ISPEC “(X,A) :'a algebra” SIGMA_ALGEBRA_INTER)) \\
         rw []) >> DISCH_TAC \\
     Know ‘v (t INTER b n) <> PosInf’
     >- (REWRITE_TAC [lt_infty] \\
         MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘v (b n)’ >> art [] \\
         MATCH_MP_TAC (REWRITE_RULE [measurable_sets_def, measure_def]
                                    (Q.SPEC ‘(Y,B,v)’ INCREASING)) \\
         CONJ_TAC >- (MATCH_MP_TAC MEASURE_SPACE_INCREASING >> art []) \\
         ASM_REWRITE_TAC [INTER_SUBSET] \\
         MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                    (ISPEC “(Y,B) :'a algebra” SIGMA_ALGEBRA_INTER)) \\
         rw []) >> DISCH_TAC \\
     IMP_RES_TAC MEASURE_SPACE_POSITIVE >> rfs [positive_def] \\
     Know ‘0 <= u (s INTER a n)’
     >- (FIRST_X_ASSUM MATCH_MP_TAC \\
         MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                    (ISPEC “(X,A) :'a algebra” SIGMA_ALGEBRA_INTER)) \\
         rw []) >> DISCH_TAC \\
     Know ‘0 <= v (t INTER b n)’
     >- (FIRST_X_ASSUM MATCH_MP_TAC \\
         MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                    (ISPEC “(Y,B) :'b algebra” SIGMA_ALGEBRA_INTER)) \\
         rw []) >> DISCH_TAC \\
    ‘u (s INTER a n) <> NegInf /\ v (t INTER b n) <> NegInf’
        by PROVE_TAC [pos_not_neginf] \\
    ‘?r1. u (s INTER a n) = Normal r1’ by METIS_TAC [extreal_cases] \\
    ‘?r2. v (t INTER b n) = Normal r2’ by METIS_TAC [extreal_cases] \\
    ‘0 <= r1 /\ 0 <= r2’ by METIS_TAC [extreal_of_num_def, extreal_le_eq] >> art [] \\
     Know ‘pos_fn_integral (X,A,u) (\x. Normal r2 * indicator_fn (s INTER a n) x) =
           Normal r2 * pos_fn_integral (X,A,u) (indicator_fn (s INTER a n))’
     >- (MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) >> Rewr' \\
     Know ‘pos_fn_integral (Y,B,v) (\y. Normal r1 * indicator_fn (t INTER b n) y) =
           Normal r1 * pos_fn_integral (Y,B,v) (indicator_fn (t INTER b n))’
     >- (MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) >> Rewr' \\
     Know ‘pos_fn_integral (Y,B,v) (indicator_fn (t INTER b n)) =
           measure (Y,B,v) (t INTER b n)’
     >- (MATCH_MP_TAC pos_fn_integral_indicator >> art [measurable_sets_def] \\
         MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                    (ISPEC “(Y,B) :'b algebra” SIGMA_ALGEBRA_INTER)) \\
         rw []) >> Rewr' \\
     Know ‘pos_fn_integral (X,A,u) (indicator_fn (s INTER a n)) =
           measure (X,A,u) (s INTER a n)’
     >- (MATCH_MP_TAC pos_fn_integral_indicator >> art [measurable_sets_def] \\
         MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                    (ISPEC “(X,A) :'a algebra” SIGMA_ALGEBRA_INTER)) \\
         rw []) >> Rewr' \\
     ASM_REWRITE_TAC [measure_def, Once mul_comm]) >> DISCH_TAC
 (* a basic property of D *)
 >> Know ‘!n. E n IN D n’
 >- (rw [Abbr ‘E’] \\
     Suff ‘general_cross cons (a n) (b n) IN general_prod cons A B’ >- PROVE_TAC [SUBSET_DEF] \\
     rw [IN_general_prod] >> qexistsl_tac [‘a n’, ‘b n’] >> REWRITE_TAC [] \\
     REV_FULL_SIMP_TAC std_ss [exhausting_sequence_def, IN_FUNSET, IN_UNIV, subsets_def])
 >> DISCH_TAC
 (* The following 4 D-properties are frequently needed.
    Note: the quantifiers (n,d,x,y) can be anything, in particular it's NOT
          required that ‘x IN X’ or ‘y IN y’ or ‘d IN D n’ *)
 >> ‘!n d y. pos_fn_integral (X,A,u) (\x. indicator_fn (d INTER E n) (cons x y)) <> NegInf’
      by (rpt GEN_TAC >> MATCH_MP_TAC pos_not_neginf \\
          MATCH_MP_TAC pos_fn_integral_pos >> rw [INDICATOR_FN_POS])
 >> Know ‘!n d y. pos_fn_integral (X,A,u) (\x. indicator_fn (d INTER E n) (cons x y)) <> PosInf’
 >- (rw [Abbr ‘E’, lt_infty] >> MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘pos_fn_integral (X,A,u)
                     (\x. indicator_fn (general_cross cons (a n) (b n)) (cons x y))’ \\
     CONJ_TAC >- (MATCH_MP_TAC pos_fn_integral_mono >> rw [INDICATOR_FN_POS] \\
                  MATCH_MP_TAC INDICATOR_FN_MONO >> REWRITE_TAC [INTER_SUBSET]) \\
     Know ‘!x. indicator_fn (general_cross cons (a n) (b n)) (cons x y) =
               indicator_fn (a n) x * indicator_fn (b n) y’
     >- (MATCH_MP_TAC indicator_fn_general_cross \\
         qexistsl_tac [‘car’, ‘cdr’] >> art []) >> Rewr' \\
     ONCE_REWRITE_TAC [mul_comm] \\
    ‘?r. 0 <= r /\ indicator_fn (b n) y = Normal r’
        by METIS_TAC [indicator_fn_normal] >> POP_ORW \\
     Know ‘pos_fn_integral (X,A,u) (\x. Normal r * indicator_fn (a n) x) =
           Normal r * pos_fn_integral (X,A,u) (indicator_fn (a n))’
     >- (MATCH_MP_TAC pos_fn_integral_cmul >> simp [INDICATOR_FN_POS]) >> Rewr' \\
     Know ‘pos_fn_integral (X,A,u) (indicator_fn (a n)) = measure (X,A,u) (a n)’
     >- (MATCH_MP_TAC pos_fn_integral_indicator >> art [measurable_sets_def] \\
         FULL_SIMP_TAC std_ss [exhausting_sequence_def, subsets_def, IN_FUNSET, IN_UNIV]) \\
     REWRITE_TAC [measure_def] >> Rewr' \\
     REWRITE_TAC [GSYM lt_infty] \\
     IMP_RES_TAC MEASURE_SPACE_POSITIVE \\
     REV_FULL_SIMP_TAC std_ss [positive_def, exhausting_sequence_def,
                               IN_FUNSET, IN_UNIV, space_def, subsets_def,
                               measurable_sets_def, measure_def] \\
     Know ‘u (a n) <> PosInf /\ u (a n) <> NegInf’
     >- (CONJ_TAC >- art [lt_infty] \\
         MATCH_MP_TAC pos_not_neginf \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> STRIP_TAC \\
    ‘?z. u (a n) = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     REWRITE_TAC [extreal_mul_def, extreal_not_infty]) >> DISCH_TAC
 >> ‘!n d x. pos_fn_integral (Y,B,v) (\y. indicator_fn (d INTER E n) (cons x y)) <> NegInf’
      by (rpt GEN_TAC >> MATCH_MP_TAC pos_not_neginf \\
          MATCH_MP_TAC pos_fn_integral_pos >> rw [INDICATOR_FN_POS])
 >> Know ‘!n d x. pos_fn_integral (Y,B,v) (\y. indicator_fn (d INTER E n) (cons x y)) <> PosInf’
 >- (rw [Abbr ‘E’, lt_infty] >> MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘pos_fn_integral (Y,B,v)
                     (\y. indicator_fn (general_cross cons (a n) (b n)) (cons x y))’ \\
     CONJ_TAC >- (MATCH_MP_TAC pos_fn_integral_mono >> rw [INDICATOR_FN_POS] \\
                  MATCH_MP_TAC INDICATOR_FN_MONO >> REWRITE_TAC [INTER_SUBSET]) \\
     Know ‘!y. indicator_fn (general_cross cons (a n) (b n)) (cons x y) =
               indicator_fn (a n) x * indicator_fn (b n) y’
     >- (MATCH_MP_TAC indicator_fn_general_cross \\
         qexistsl_tac [‘car’, ‘cdr’] >> art []) >> Rewr' \\
    ‘?r. 0 <= r /\ indicator_fn (a n) x = Normal r’
        by METIS_TAC [indicator_fn_normal] >> POP_ORW \\
     Know ‘pos_fn_integral (Y,B,v) (\y. Normal r * indicator_fn (b n) y) =
           Normal r * pos_fn_integral (Y,B,v) (indicator_fn (b n))’
     >- (MATCH_MP_TAC pos_fn_integral_cmul >> simp [INDICATOR_FN_POS]) >> Rewr' \\
     Know ‘pos_fn_integral (Y,B,v) (indicator_fn (b n)) = measure (Y,B,v) (b n)’
     >- (MATCH_MP_TAC pos_fn_integral_indicator >> art [measurable_sets_def] \\
         FULL_SIMP_TAC std_ss [exhausting_sequence_def, subsets_def, IN_FUNSET, IN_UNIV]) \\
     REWRITE_TAC [measure_def] >> Rewr' \\
     REWRITE_TAC [GSYM lt_infty] \\
     IMP_RES_TAC MEASURE_SPACE_POSITIVE \\
     REV_FULL_SIMP_TAC std_ss [positive_def, exhausting_sequence_def,
                               IN_FUNSET, IN_UNIV, space_def, subsets_def,
                               measurable_sets_def, measure_def] \\
     Know ‘v (b n) <> PosInf /\ v (b n) <> NegInf’
     >- (CONJ_TAC >- art [lt_infty] \\
         MATCH_MP_TAC pos_not_neginf \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> STRIP_TAC \\
    ‘?z. v (b n) = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     REWRITE_TAC [extreal_mul_def, extreal_not_infty]) >> DISCH_TAC
 (* key property: D n is a dynkin system *)
 >> Know ‘!n. dynkin_system (general_cross cons X Y,D n)’
 >- (rw [dynkin_system_def] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       rw [subset_class_def, Abbr ‘D’],
       (* goal 2 (of 4) *)
       Suff ‘general_cross cons X Y IN general_prod cons A B’ >- PROVE_TAC [SUBSET_DEF] \\
       rw [IN_general_prod] >> qexistsl_tac [‘X’, ‘Y’] >> REWRITE_TAC [] \\
       fs [SIGMA_ALGEBRA_ALT_SPACE],
       (* goal 3 (of 4): DIFF (hard) *)
       rename1 ‘(general_cross cons X Y) DIFF d IN D n’ \\
    (* expanding D without touching assumptions *)
       Suff ‘(general_cross cons X Y) DIFF d IN
             {d | d SUBSET general_cross cons X Y /\
                 (!x. x IN X ==>
                      (\y. indicator_fn (d INTER E n) (cons x y)) IN Borel_measurable (Y,B)) /\
                 (!y. y IN Y ==>
                      (\x. indicator_fn (d INTER E n) (cons x y)) IN Borel_measurable (X,A)) /\
                 (\y. pos_fn_integral (X,A,u) (\x. indicator_fn (d INTER E n) (cons x y)))
                        IN Borel_measurable (Y,B) /\
                 (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (d INTER E n) (cons x y)))
                        IN Borel_measurable (X,A) /\
                 pos_fn_integral (X,A,u)
                   (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (d INTER E n) (cons x y))) =
                 pos_fn_integral (Y,B,v)
                   (\y. pos_fn_integral (X,A,u) (\x. indicator_fn (d INTER E n) (cons x y)))}’
       >- METIS_TAC [Abbr ‘D’] >> simp [GSPECIFICATION] \\
       Know ‘indicator_fn (((general_cross cons X Y) DIFF d) INTER E n) =
               (\t. indicator_fn (E n) t - indicator_fn (d INTER E n) t)’
       >- (ONCE_REWRITE_TAC [INTER_COMM] \\
           MATCH_MP_TAC INDICATOR_FN_DIFF_SPACE \\
           rw [Abbr ‘E’]
           >- (MATCH_MP_TAC general_SUBSET_CROSS \\
               FULL_SIMP_TAC std_ss [exhausting_sequence_def, IN_FUNSET, IN_UNIV,
                                     subsets_def, space_def] \\
               METIS_TAC [sigma_algebra_def, algebra_def, subset_class_def,
                          space_def, subsets_def]) \\
           REV_FULL_SIMP_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) >> Rewr' >> BETA_TAC \\
       STRONG_CONJ_TAC (* Borel_measurable #1 *)
       >- (rpt STRIP_TAC \\
           MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB >> BETA_TAC \\
           qexistsl_tac [‘\y. indicator_fn (E n) (cons x y)’,
                         ‘\y. indicator_fn (d INTER E n) (cons x y)’] \\
           rw [INDICATOR_FN_NOT_INFTY] >|
           [ (* goal 1 (of 2) *)
            ‘E n = E n INTER E n’ by PROVE_TAC [INTER_IDEMPOT] >> POP_ORW \\
             REV_FULL_SIMP_TAC std_ss [Abbr ‘D’, GSPECIFICATION],
             (* goal 2 (of 2) *)
             FULL_SIMP_TAC std_ss [Abbr ‘D’, GSPECIFICATION] ]) >> DISCH_TAC \\
       STRONG_CONJ_TAC (* Borel_measurable #2 (symmetric with #1) *)
       >- (rpt STRIP_TAC \\
           MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB >> BETA_TAC \\
           qexistsl_tac [‘\x. indicator_fn (E n) (cons x y)’,
                         ‘\x. indicator_fn (d INTER E n) (cons x y)’] \\
           rw [INDICATOR_FN_NOT_INFTY] >|
           [ (* goal 1 (of 2) *)
            ‘E n = E n INTER E n’ by PROVE_TAC [INTER_IDEMPOT] >> POP_ORW \\
             FULL_SIMP_TAC std_ss [Abbr ‘D’, GSPECIFICATION],
             (* goal 2 (of 2) *)
             FULL_SIMP_TAC std_ss [Abbr ‘D’, GSPECIFICATION] ]) >> DISCH_TAC \\
       CONJ_TAC (* Borel_measurable #3 *)
       >- (MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                      (Q.SPEC ‘(Y,B,v)’ IN_MEASURABLE_BOREL_EQ)) \\
           Q.EXISTS_TAC ‘\y. pos_fn_integral (X,A,u) (\x. indicator_fn (E n) (cons x y)) -
                             pos_fn_integral (X,A,u) (\x. indicator_fn (d INTER E n) (cons x y))’ \\
           reverse CONJ_TAC
           >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB >> BETA_TAC >> art [space_def] \\
               qexistsl_tac [‘\y. pos_fn_integral (X,A,u) (\x. indicator_fn (E n) (cons x y))’,
                             ‘\y. pos_fn_integral (X,A,u)
                                    (\x. indicator_fn (d INTER E n) (cons x y))’] \\
               rw [] >| (* 2 subgoals *)
               [ (* goal 1 (of 2) *)
                ‘E n = E n INTER E n’ by PROVE_TAC [INTER_IDEMPOT] >> POP_ORW \\
                 Q.PAT_X_ASSUM ‘!n. E n IN D n’ (MP_TAC o (Q.SPEC ‘n’)) \\
                 RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION],
                 (* goal 2 (of 2) *)
                 Q.PAT_X_ASSUM ‘d IN D n’ MP_TAC \\
                 RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION] ]) \\
           Q.X_GEN_TAC ‘y’ >> STRIP_TAC >> BETA_TAC \\
           HO_MATCH_MP_TAC pos_fn_integral_sub \\
           simp [INDICATOR_FN_POS, INDICATOR_FN_NOT_INFTY] \\
           CONJ_TAC >- (‘E n = E n INTER E n’ by PROVE_TAC [INTER_IDEMPOT] >> POP_ORW \\
                        Q.PAT_X_ASSUM ‘!n. E n IN D n’ (MP_TAC o (Q.SPEC ‘n’)) \\
                        RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
           CONJ_TAC >- (Q.PAT_X_ASSUM ‘d IN D n’ MP_TAC \\
                        RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
           rpt STRIP_TAC \\
           MATCH_MP_TAC INDICATOR_FN_MONO >> REWRITE_TAC [INTER_SUBSET]) \\
       CONJ_TAC (* Borel_measurable #4 (symmetric with #3) *)
       >- (MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                      (Q.SPEC ‘(X,A,u)’ IN_MEASURABLE_BOREL_EQ)) \\
           Q.EXISTS_TAC ‘\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (E n) (cons x y)) -
                             pos_fn_integral (Y,B,v) (\y. indicator_fn (d INTER E n) (cons x y))’ \\
           reverse CONJ_TAC
           >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB >> BETA_TAC >> art [space_def] \\
               qexistsl_tac [‘\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (E n) (cons x y))’,
                             ‘\x. pos_fn_integral (Y,B,v)
                                    (\y. indicator_fn (d INTER E n) (cons x y))’] \\
               rw [] >| (* 2 subgoals *)
               [ (* goal 1 (of 2) *)
                ‘E n = E n INTER E n’ by PROVE_TAC [INTER_IDEMPOT] >> POP_ORW \\
                 Q.PAT_X_ASSUM ‘!n. E n IN D n’ (MP_TAC o (Q.SPEC ‘n’)) \\
                 RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION],
                 (* goal 2 (of 2) *)
                 Q.PAT_X_ASSUM ‘d IN D n’ MP_TAC \\
                 RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION] ]) \\
           Q.X_GEN_TAC ‘x’ >> STRIP_TAC >> BETA_TAC \\
           HO_MATCH_MP_TAC pos_fn_integral_sub \\
           simp [INDICATOR_FN_POS, INDICATOR_FN_NOT_INFTY] \\
           CONJ_TAC >- (‘E n = E n INTER E n’ by PROVE_TAC [INTER_IDEMPOT] >> POP_ORW \\
                        Q.PAT_X_ASSUM ‘!n. E n IN D n’ (MP_TAC o (Q.SPEC ‘n’)) \\
                        RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
           CONJ_TAC >- (Q.PAT_X_ASSUM ‘d IN D n’ MP_TAC \\
                        RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
           rpt STRIP_TAC \\
           MATCH_MP_TAC INDICATOR_FN_MONO >> REWRITE_TAC [INTER_SUBSET]) \\
       Know ‘pos_fn_integral (X,A,u)
               (\x. pos_fn_integral (Y,B,v)
                      (\y. indicator_fn (E n) (cons x y) -
                           indicator_fn (d INTER E n) (cons x y))) =
             pos_fn_integral (X,A,u)
               (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (E n) (cons x y)) -
                    pos_fn_integral (Y,B,v) (\y. indicator_fn (d INTER E n) (cons x y)))’
       >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
           CONJ_TAC >- (rpt STRIP_TAC \\
                        MATCH_MP_TAC pos_fn_integral_pos >> simp [] \\
                        Q.X_GEN_TAC ‘y’ >> STRIP_TAC \\
                        MATCH_MP_TAC le_sub_imp \\
                        simp [INDICATOR_FN_NOT_INFTY, add_lzero] \\
                        MATCH_MP_TAC INDICATOR_FN_MONO >> rw [INTER_SUBSET]) \\
           CONJ_TAC >- (rpt STRIP_TAC \\
                        MATCH_MP_TAC le_sub_imp >> simp [add_lzero] \\
                        MATCH_MP_TAC pos_fn_integral_mono >> rw [INDICATOR_FN_POS] \\
                        MATCH_MP_TAC INDICATOR_FN_MONO >> rw [INTER_SUBSET]) \\
           rpt STRIP_TAC \\
           HO_MATCH_MP_TAC pos_fn_integral_sub \\
           simp [INDICATOR_FN_POS, INDICATOR_FN_NOT_INFTY] \\
           CONJ_TAC >- (‘E n = E n INTER E n’ by PROVE_TAC [INTER_IDEMPOT] >> POP_ORW \\
                        Q.PAT_X_ASSUM ‘!n. E n IN D n’ (MP_TAC o (Q.SPEC ‘n’)) \\
                        RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
           CONJ_TAC >- (Q.PAT_X_ASSUM ‘d IN D n’ MP_TAC \\
                        RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
           rpt STRIP_TAC \\
           MATCH_MP_TAC INDICATOR_FN_MONO >> REWRITE_TAC [INTER_SUBSET]) >> Rewr' \\
       Know ‘pos_fn_integral (Y,B,v)
               (\y. pos_fn_integral (X,A,u)
                      (\x. indicator_fn (E n) (cons x y) -
                           indicator_fn (d INTER E n) (cons x y))) =
             pos_fn_integral (Y,B,v)
               (\y. pos_fn_integral (X,A,u) (\x. indicator_fn (E n) (cons x y)) -
                    pos_fn_integral (X,A,u) (\x. indicator_fn (d INTER E n) (cons x y)))’
       >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
           CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                        MATCH_MP_TAC pos_fn_integral_pos >> simp [] \\
                        Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
                        MATCH_MP_TAC le_sub_imp \\
                        simp [INDICATOR_FN_NOT_INFTY, add_lzero] \\
                        MATCH_MP_TAC INDICATOR_FN_MONO >> rw [INTER_SUBSET]) \\
           CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                        MATCH_MP_TAC le_sub_imp >> simp [add_lzero] \\
                        MATCH_MP_TAC pos_fn_integral_mono >> rw [INDICATOR_FN_POS] \\
                        MATCH_MP_TAC INDICATOR_FN_MONO >> rw [INTER_SUBSET]) \\
           Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
           HO_MATCH_MP_TAC pos_fn_integral_sub \\
           simp [INDICATOR_FN_POS, INDICATOR_FN_NOT_INFTY] \\
           CONJ_TAC >- (‘E n = E n INTER E n’ by PROVE_TAC [INTER_IDEMPOT] >> POP_ORW \\
                        Q.PAT_X_ASSUM ‘!n. E n IN D n’ (MP_TAC o (Q.SPEC ‘n’)) \\
                        RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
           CONJ_TAC >- (Q.PAT_X_ASSUM ‘d IN D n’ MP_TAC \\
                        RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
           Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
           MATCH_MP_TAC INDICATOR_FN_MONO >> REWRITE_TAC [INTER_SUBSET]) >> Rewr' \\
       Know ‘pos_fn_integral (X,A,u)
               (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (E n) (cons x y)) -
                    pos_fn_integral (Y,B,v) (\y. indicator_fn (d INTER E n) (cons x y))) =
             pos_fn_integral (X,A,u)
               (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (E n) (cons x y))) -
             pos_fn_integral (X,A,u)
               (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (d INTER E n) (cons x y)))’
       >- (HO_MATCH_MP_TAC pos_fn_integral_sub >> simp [] \\
           CONJ_TAC >- (‘E n = E n INTER E n’ by PROVE_TAC [INTER_IDEMPOT] >> POP_ORW \\
                        Q.PAT_X_ASSUM ‘!n. E n IN D n’ (MP_TAC o (Q.SPEC ‘n’)) \\
                        RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
           CONJ_TAC >- (Q.PAT_X_ASSUM ‘d IN D n’ MP_TAC \\
                        RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
           CONJ_TAC >- (rpt STRIP_TAC \\
                        MATCH_MP_TAC pos_fn_integral_pos >> simp [INDICATOR_FN_POS]) \\
           CONJ_TAC >- (rpt STRIP_TAC \\
                        MATCH_MP_TAC pos_fn_integral_mono >> simp [INDICATOR_FN_POS] \\
                        Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                        MATCH_MP_TAC INDICATOR_FN_MONO >> rw [INTER_SUBSET]) \\
           REWRITE_TAC [lt_infty] >> MATCH_MP_TAC let_trans \\
           Q.EXISTS_TAC ‘pos_fn_integral (X,A,u)
                          (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (E n) (cons x y)))’ \\
           CONJ_TAC >- (MATCH_MP_TAC pos_fn_integral_mono >> simp [INDICATOR_FN_POS] \\
                        CONJ_TAC >- (rpt STRIP_TAC \\
                                     MATCH_MP_TAC pos_fn_integral_pos \\
                                     simp [INDICATOR_FN_POS]) \\
                        rpt STRIP_TAC \\
                        MATCH_MP_TAC pos_fn_integral_mono >> simp [INDICATOR_FN_POS] \\
                        Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                        MATCH_MP_TAC INDICATOR_FN_MONO >> rw [INTER_SUBSET]) \\
           rw [Abbr ‘E’, GSYM lt_infty] \\
           Know ‘!x y. indicator_fn (general_cross cons (a n) (b n)) (cons x y) =
                       indicator_fn (a n) x * indicator_fn (b n) y’
           >- (rpt GEN_TAC >> MATCH_MP_TAC indicator_fn_general_cross \\
               qexistsl_tac [‘car’, ‘cdr’] >> art []) >> Rewr' \\
           Know ‘!x. pos_fn_integral (Y,B,v) (\y. indicator_fn (a n) x * indicator_fn (b n) y) =
                     indicator_fn (a n) x * pos_fn_integral (Y,B,v) (indicator_fn (b n))’
           >- (GEN_TAC \\
              ‘?r. 0 <= r /\ indicator_fn (a n) x = Normal r’
                 by METIS_TAC [indicator_fn_normal] >> POP_ORW \\
               Know ‘pos_fn_integral (Y,B,v) (\y. Normal r * indicator_fn (b n) y) =
                     Normal r * pos_fn_integral (Y,B,v) (indicator_fn (b n))’
               >- (MATCH_MP_TAC pos_fn_integral_cmul >> simp [INDICATOR_FN_POS]) \\
               Rewr) >> Rewr' \\
           Know ‘pos_fn_integral (Y,B,v) (indicator_fn (b n)) = measure (Y,B,v) (b n)’
           >- (MATCH_MP_TAC pos_fn_integral_indicator >> art [measurable_sets_def] \\
               FULL_SIMP_TAC std_ss [exhausting_sequence_def, subsets_def, IN_FUNSET, IN_UNIV]) \\
           REWRITE_TAC [measure_def] >> Rewr' \\
           IMP_RES_TAC MEASURE_SPACE_POSITIVE \\
           REV_FULL_SIMP_TAC std_ss [positive_def, exhausting_sequence_def,
                                     IN_FUNSET, IN_UNIV, space_def, subsets_def,
                                     measurable_sets_def, measure_def] \\
           Know ‘v (b n) <> PosInf /\ v (b n) <> NegInf’
           >- (CONJ_TAC >- art [lt_infty] \\
               MATCH_MP_TAC pos_not_neginf \\
               FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> STRIP_TAC \\
           ONCE_REWRITE_TAC [mul_comm] \\
           Know ‘pos_fn_integral (X,A,u) (\x. v (b n) * indicator_fn (a n) x) =
                 v (b n) * pos_fn_integral (X,A,u) (indicator_fn (a n))’
           >- (‘?z. 0 <= z /\ v (b n) = Normal z’
                  by METIS_TAC [extreal_of_num_def, extreal_le_eq, extreal_cases] >> POP_ORW \\
               MATCH_MP_TAC pos_fn_integral_cmul >> simp [INDICATOR_FN_POS]) >> Rewr' \\
           Know ‘pos_fn_integral (X,A,u) (indicator_fn (a n)) = measure (X,A,u) (a n)’
           >- (MATCH_MP_TAC pos_fn_integral_indicator >> art [measurable_sets_def] \\
               FULL_SIMP_TAC std_ss [exhausting_sequence_def, subsets_def, IN_FUNSET, IN_UNIV]) \\
           REWRITE_TAC [measure_def] >> Rewr' \\
           Know ‘u (a n) <> PosInf /\ u (a n) <> NegInf’
           >- (CONJ_TAC >- art [lt_infty] \\
               MATCH_MP_TAC pos_not_neginf \\
               FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> STRIP_TAC \\
          ‘?r1. u (a n) = Normal r1’ by METIS_TAC [extreal_cases] >> POP_ORW \\
          ‘?r2. v (b n) = Normal r2’ by METIS_TAC [extreal_cases] >> POP_ORW \\
           REWRITE_TAC [extreal_mul_def, extreal_not_infty]) >> Rewr' \\
       Know ‘pos_fn_integral (Y,B,v)
               (\y. pos_fn_integral (X,A,u) (\x. indicator_fn (E n) (cons x y)) -
                    pos_fn_integral (X,A,u) (\x. indicator_fn (d INTER E n) (cons x y))) =
             pos_fn_integral (Y,B,v)
               (\y. pos_fn_integral (X,A,u) (\x. indicator_fn (E n) (cons x y))) -
             pos_fn_integral (Y,B,v)
               (\y. pos_fn_integral (X,A,u) (\x. indicator_fn (d INTER E n) (cons x y)))’
       >- (HO_MATCH_MP_TAC pos_fn_integral_sub >> simp [] \\
           CONJ_TAC >- (‘E n = E n INTER E n’ by PROVE_TAC [INTER_IDEMPOT] >> POP_ORW \\
                        Q.PAT_X_ASSUM ‘!n. E n IN D n’ (MP_TAC o (Q.SPEC ‘n’)) \\
                        RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
           CONJ_TAC >- (Q.PAT_X_ASSUM ‘d IN D n’ MP_TAC \\
                        RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
           CONJ_TAC >- (rpt STRIP_TAC \\
                        MATCH_MP_TAC pos_fn_integral_pos >> simp [INDICATOR_FN_POS]) \\
           CONJ_TAC >- (rpt STRIP_TAC \\
                        MATCH_MP_TAC pos_fn_integral_mono >> simp [INDICATOR_FN_POS] \\
                        Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
                        MATCH_MP_TAC INDICATOR_FN_MONO >> rw [INTER_SUBSET]) \\
           REWRITE_TAC [lt_infty] >> MATCH_MP_TAC let_trans \\
           Q.EXISTS_TAC ‘pos_fn_integral (Y,B,v)
                          (\y. pos_fn_integral (X,A,u) (\x. indicator_fn (E n) (cons x y)))’ \\
           CONJ_TAC >- (MATCH_MP_TAC pos_fn_integral_mono >> simp [] \\
                        CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                                     MATCH_MP_TAC pos_fn_integral_pos >> simp [INDICATOR_FN_POS]) \\
                        Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                        MATCH_MP_TAC pos_fn_integral_mono >> simp [INDICATOR_FN_POS] \\
                        Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
                        MATCH_MP_TAC INDICATOR_FN_MONO >> rw [INTER_SUBSET]) \\
           rw [Abbr ‘E’, GSYM lt_infty] \\
           Know ‘!x y. indicator_fn (general_cross cons (a n) (b n)) (cons x y) =
                      indicator_fn (a n) x * indicator_fn (b n) y’
           >- (rpt GEN_TAC >> MATCH_MP_TAC indicator_fn_general_cross \\
               qexistsl_tac [‘car’, ‘cdr’] >> art []) >> Rewr' \\
           ONCE_REWRITE_TAC [mul_comm] \\
           Know ‘!y. pos_fn_integral (X,A,u) (\x. indicator_fn (b n) y * indicator_fn (a n) x) =
                     indicator_fn (b n) y * pos_fn_integral (X,A,u) (indicator_fn (a n))’
           >- (GEN_TAC \\
              ‘?r. 0 <= r /\ indicator_fn (b n) y = Normal r’
                 by METIS_TAC [indicator_fn_normal] >> POP_ORW \\
               Know ‘pos_fn_integral (X,A,u) (\x. Normal r * indicator_fn (a n) x) =
                     Normal r * pos_fn_integral (X,A,u) (indicator_fn (a n))’
               >- (MATCH_MP_TAC pos_fn_integral_cmul >> simp [INDICATOR_FN_POS]) \\
               Rewr) >> Rewr' \\
           Know ‘pos_fn_integral (X,A,u) (indicator_fn (a n)) = measure (X,A,u) (a n)’
           >- (MATCH_MP_TAC pos_fn_integral_indicator >> art [measurable_sets_def] \\
               FULL_SIMP_TAC std_ss [exhausting_sequence_def, subsets_def, IN_FUNSET, IN_UNIV]) \\
           REWRITE_TAC [measure_def] >> Rewr' \\
           IMP_RES_TAC MEASURE_SPACE_POSITIVE \\
           REV_FULL_SIMP_TAC std_ss [positive_def, exhausting_sequence_def,
                                     IN_FUNSET, IN_UNIV, space_def, subsets_def,
                                     measurable_sets_def, measure_def] \\
           Know ‘u (a n) <> PosInf /\ u (a n) <> NegInf’
           >- (CONJ_TAC >- art [lt_infty] \\
               MATCH_MP_TAC pos_not_neginf \\
               FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> STRIP_TAC \\
           ONCE_REWRITE_TAC [mul_comm] \\
           Know ‘pos_fn_integral (Y,B,v) (\y. u (a n) * indicator_fn (b n) y) =
                 u (a n) * pos_fn_integral (Y,B,v) (indicator_fn (b n))’
           >- (‘?z. 0 <= z /\ u (a n) = Normal z’
                  by METIS_TAC [extreal_of_num_def, extreal_le_eq, extreal_cases] >> POP_ORW \\
               MATCH_MP_TAC pos_fn_integral_cmul >> simp [INDICATOR_FN_POS]) >> Rewr' \\
           Know ‘pos_fn_integral (Y,B,v) (indicator_fn (b n)) = measure (Y,B,v) (b n)’
           >- (MATCH_MP_TAC pos_fn_integral_indicator >> art [measurable_sets_def] \\
               FULL_SIMP_TAC std_ss [exhausting_sequence_def, subsets_def, IN_FUNSET, IN_UNIV]) \\
           REWRITE_TAC [measure_def] >> Rewr' \\
           Know ‘v (b n) <> PosInf /\ v (b n) <> NegInf’
           >- (CONJ_TAC >- art [lt_infty] \\
               MATCH_MP_TAC pos_not_neginf \\
               FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> STRIP_TAC \\
          ‘?r1. u (a n) = Normal r1’ by METIS_TAC [extreal_cases] >> POP_ORW \\
          ‘?r2. v (b n) = Normal r2’ by METIS_TAC [extreal_cases] >> POP_ORW \\
           REWRITE_TAC [extreal_mul_def, extreal_not_infty]) >> Rewr' \\
       Know ‘pos_fn_integral (X,A,u)
               (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (E n) (cons x y))) =
             pos_fn_integral (Y,B,v)
               (\y. pos_fn_integral (X,A,u) (\x. indicator_fn (E n) (cons x y)))’
       >- (‘E n = E n INTER E n’ by PROVE_TAC [INTER_IDEMPOT] >> POP_ORW \\
           Q.PAT_X_ASSUM ‘!n. E n IN D n’ (MP_TAC o (Q.SPEC ‘n’)) \\
           RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) >> Rewr' \\
       Know ‘pos_fn_integral (X,A,u)
               (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (d INTER E n) (cons x y))) =
             pos_fn_integral (Y,B,v)
               (\y. pos_fn_integral (X,A,u) (\x. indicator_fn (d INTER E n) (cons x y)))’
       >- (Q.PAT_X_ASSUM ‘d IN D n’ MP_TAC \\
           RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) >> Rewr,
       (* goal 4 (of 4): disjoint countably additive *)
       fs [IN_FUNSET, IN_UNIV] >> rename1 ‘!x. d x IN D n’ \\
    (* expanding D without touching assumptions *)
       Suff ‘BIGUNION (IMAGE d univ(:num)) IN
            {d | d SUBSET (general_cross cons X Y) /\
                 (!x. x IN X ==>
                      (\y. indicator_fn (d INTER E n) (cons x y)) IN Borel_measurable (Y,B)) /\
                 (!y. y IN Y ==>
                      (\x. indicator_fn (d INTER E n) (cons x y)) IN Borel_measurable (X,A)) /\
                 (\y. pos_fn_integral (X,A,u) (\x. indicator_fn (d INTER E n) (cons x y)))
                        IN Borel_measurable (Y,B) /\
                 (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (d INTER E n) (cons x y)))
                        IN Borel_measurable (X,A) /\
                 pos_fn_integral (X,A,u)
                   (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (d INTER E n) (cons x y))) =
                 pos_fn_integral (Y,B,v)
                   (\y. pos_fn_integral (X,A,u) (\x. indicator_fn (d INTER E n) (cons x y)))}’
       >- METIS_TAC [Abbr ‘D’] >> simp [GSPECIFICATION] \\
       Know ‘!x. d x SUBSET (general_cross cons X Y)’
       >- (GEN_TAC >> Q.PAT_X_ASSUM ‘!x. d x IN D n’ (MP_TAC o (Q.SPEC ‘x’)) \\
           RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) >> DISCH_TAC \\
       CONJ_TAC >- (POP_ASSUM MP_TAC >> rw [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_UNIV]) \\
       REWRITE_TAC [BIGUNION_OVER_INTER_L] \\
    (* applying indicator_fn_split or indicator_fn_suminf *)
       Know ‘!x y. indicator_fn (BIGUNION (IMAGE (\i. d i INTER E n) UNIV)) (cons x y) =
                   suminf (\i. indicator_fn ((\i. d i INTER E n) i) (cons x y))’
       >- (rpt GEN_TAC >> MATCH_MP_TAC EQ_SYM \\
           MATCH_MP_TAC indicator_fn_suminf \\
           BETA_TAC >> qx_genl_tac [‘i’, ‘j’] >> DISCH_TAC \\
           MATCH_MP_TAC DISJOINT_RESTRICT_L \\
           FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> Rewr' \\
       CONJ_TAC (* Borel_measurable #1 *)
       >- (rpt STRIP_TAC \\
           MATCH_MP_TAC IN_MEASURABLE_BOREL_SUMINF >> simp [INDICATOR_FN_POS] \\
           Q.EXISTS_TAC ‘\i y. indicator_fn (d i INTER E n) (cons x y)’ \\
           simp [INDICATOR_FN_POS] \\
           Q.X_GEN_TAC ‘i’ >> Q.PAT_X_ASSUM ‘!x. d x IN D n’ (MP_TAC o (Q.SPEC ‘i’)) \\
           RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
       CONJ_TAC (* Borel_measurable #2 *)
       >- (rpt STRIP_TAC \\
           MATCH_MP_TAC IN_MEASURABLE_BOREL_SUMINF >> simp [INDICATOR_FN_POS] \\
           Q.EXISTS_TAC ‘\i x. indicator_fn (d i INTER E n) (cons x y)’ \\
           simp [INDICATOR_FN_POS] \\
           Q.X_GEN_TAC ‘i’ >> Q.PAT_X_ASSUM ‘!x. d x IN D n’ (MP_TAC o (Q.SPEC ‘i’)) \\
           RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
       CONJ_TAC (* Borel_measurable #3 *)
       >- (MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                      (Q.SPEC ‘(Y,B,v)’ IN_MEASURABLE_BOREL_EQ)) \\
           BETA_TAC \\
           Q.EXISTS_TAC ‘\y. suminf (\i. pos_fn_integral (X,A,u)
                                           (\x. indicator_fn (d i INTER E n) (cons x y)))’ \\
           reverse CONJ_TAC
           >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_SUMINF >> simp [] \\
               Q.EXISTS_TAC ‘\i y. pos_fn_integral (X,A,u)
                                     (\x. indicator_fn (d i INTER E n) (cons x y))’ >> simp [] \\
               reverse CONJ_TAC
               >- (qx_genl_tac [‘i’, ‘y’] >> DISCH_TAC \\
                   MATCH_MP_TAC pos_fn_integral_pos >> simp [INDICATOR_FN_POS]) \\
               Q.X_GEN_TAC ‘i’ >> Q.PAT_X_ASSUM ‘!x. d x IN D n’ (MP_TAC o (Q.SPEC ‘i’)) \\
               RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
           Q.X_GEN_TAC ‘y’ >> BETA_TAC >> DISCH_TAC \\
           Know ‘pos_fn_integral (X,A,u)
                   (\x. suminf (\i. (\i x. indicator_fn (d i INTER E n) (cons x y)) i x)) =
                 suminf (\i. pos_fn_integral (X,A,u)
                               ((\i x. indicator_fn (d i INTER E n) (cons x y)) i))’
           >- (MATCH_MP_TAC pos_fn_integral_suminf >> simp [INDICATOR_FN_POS] \\
               GEN_TAC >> Q.PAT_X_ASSUM ‘!x. d x IN D n’ (MP_TAC o (Q.SPEC ‘i’)) \\
               RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) >> BETA_TAC >> Rewr) \\
       CONJ_TAC (* Borel_measurable #4 *)
       >- (MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                      (Q.SPEC ‘(X,A,u)’ IN_MEASURABLE_BOREL_EQ)) \\
           BETA_TAC \\
           Q.EXISTS_TAC ‘\x. suminf (\i. pos_fn_integral (Y,B,v)
                                           (\y. indicator_fn (d i INTER E n) (cons x y)))’ \\
           reverse CONJ_TAC
           >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_SUMINF >> simp [] \\
               Q.EXISTS_TAC ‘\i x. pos_fn_integral (Y,B,v)
                                     (\y. indicator_fn (d i INTER E n) (cons x y))’ >> simp [] \\
               reverse CONJ_TAC
               >- (qx_genl_tac [‘i’, ‘x’] >> DISCH_TAC \\
                   MATCH_MP_TAC pos_fn_integral_pos >> simp [INDICATOR_FN_POS]) \\
               Q.X_GEN_TAC ‘i’ >> Q.PAT_X_ASSUM ‘!x. d x IN D n’ (MP_TAC o (Q.SPEC ‘i’)) \\
               RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
           Q.X_GEN_TAC ‘x’ >> BETA_TAC >> DISCH_TAC \\
           Know ‘pos_fn_integral (Y,B,v)
                   (\y. suminf (\i. (\i y. indicator_fn (d i INTER E n) (cons x y)) i y)) =
                 suminf (\i. pos_fn_integral (Y,B,v)
                               ((\i y. indicator_fn (d i INTER E n) (cons x y)) i))’
           >- (MATCH_MP_TAC pos_fn_integral_suminf >> simp [INDICATOR_FN_POS] \\
               GEN_TAC >> Q.PAT_X_ASSUM ‘!x. d x IN D n’ (MP_TAC o (Q.SPEC ‘i’)) \\
               RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) >> BETA_TAC >> Rewr) \\
       Know ‘pos_fn_integral (X,A,u)
               (\x. pos_fn_integral (Y,B,v)
                      (\y. suminf (\i. indicator_fn (d i INTER E n) (cons x y)))) =
             pos_fn_integral (X,A,u)
               (\x. suminf (\i. pos_fn_integral (Y,B,v)
                                  (\y. indicator_fn (d i INTER E n) (cons x y))))’
       >- (MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                      (Q.SPEC ‘(X,A,u)’ pos_fn_integral_cong)) >> simp [] \\
           CONJ_TAC >- (rpt STRIP_TAC >> MATCH_MP_TAC pos_fn_integral_pos >> simp [] \\
                        Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                        MATCH_MP_TAC ext_suminf_pos >> simp [INDICATOR_FN_POS]) \\
           CONJ_TAC >- (rpt STRIP_TAC >> MATCH_MP_TAC ext_suminf_pos >> simp [] \\
                        Q.X_GEN_TAC ‘i’ >> MATCH_MP_TAC pos_fn_integral_pos \\
                        simp [INDICATOR_FN_POS]) \\
           rpt STRIP_TAC \\
           Know ‘pos_fn_integral (Y,B,v)
                   (\y. suminf (\i. (\i y. indicator_fn (d i INTER E n) (cons x y)) i y)) =
                 suminf (\i. pos_fn_integral (Y,B,v)
                               ((\i y. indicator_fn (d i INTER E n) (cons x y)) i))’
           >- (MATCH_MP_TAC pos_fn_integral_suminf \\
               simp [INDICATOR_FN_POS] \\
               GEN_TAC >> Q.PAT_X_ASSUM ‘!x. d x IN D n’ (MP_TAC o (Q.SPEC ‘i’)) \\
               RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) >> BETA_TAC >> Rewr) \\
       BETA_TAC >> Rewr' \\
       Know ‘pos_fn_integral (Y,B,v)
               (\y. pos_fn_integral (X,A,u)
                      (\x. suminf (\i. indicator_fn (d i INTER E n) (cons x y)))) =
             pos_fn_integral (Y,B,v)
               (\y. suminf (\i. pos_fn_integral (X,A,u)
                                  (\x. indicator_fn (d i INTER E n) (cons x y))))’
       >- (MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                      (Q.SPEC ‘(Y,B,v)’ pos_fn_integral_cong)) >> simp [] \\
           CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                        MATCH_MP_TAC pos_fn_integral_pos >> simp [] \\
                        rpt STRIP_TAC >> MATCH_MP_TAC ext_suminf_pos \\
                        simp [INDICATOR_FN_POS]) \\
           CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                        MATCH_MP_TAC ext_suminf_pos >> simp [] \\
                        Q.X_GEN_TAC ‘i’ >> MATCH_MP_TAC pos_fn_integral_pos \\
                        simp [INDICATOR_FN_POS]) \\
           Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
           Know ‘pos_fn_integral (X,A,u)
                   (\x. suminf (\i. (\i x. indicator_fn (d i INTER E n) (cons x y)) i x)) =
                 suminf (\i. pos_fn_integral (X,A,u)
                               ((\i x. indicator_fn (d i INTER E n) (cons x y)) i))’
           >- (MATCH_MP_TAC pos_fn_integral_suminf \\
               simp [INDICATOR_FN_POS] \\
               GEN_TAC >> Q.PAT_X_ASSUM ‘!x. d x IN D n’ (MP_TAC o (Q.SPEC ‘i’)) \\
               RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) >> BETA_TAC >> Rewr) >> Rewr' \\
       Know ‘pos_fn_integral (X,A,u)
               (\x. suminf (\i. (\i x. pos_fn_integral (Y,B,v)
                                         (\y. indicator_fn (d i INTER E n) (cons x y))) i x)) =
             suminf (\i. pos_fn_integral (X,A,u)
                           ((\i x. pos_fn_integral (Y,B,v)
                                     (\y. indicator_fn (d i INTER E n) (cons x y))) i))’
       >- (MATCH_MP_TAC pos_fn_integral_suminf >> simp [] \\
           CONJ_TAC >- (rpt STRIP_TAC >> MATCH_MP_TAC pos_fn_integral_pos \\
                        simp [INDICATOR_FN_POS]) \\
           GEN_TAC >> Q.PAT_X_ASSUM ‘!x. d x IN D n’ (MP_TAC o (Q.SPEC ‘i’)) \\
           RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) >> BETA_TAC >> Rewr' \\
       Know ‘pos_fn_integral (Y,B,v)
               (\y. suminf (\i. (\i y. pos_fn_integral (X,A,u)
                                         (\x. indicator_fn (d i INTER E n) (cons x y))) i y)) =
             suminf (\i. pos_fn_integral (Y,B,v)
                           ((\i y. pos_fn_integral (X,A,u)
                                     (\x. indicator_fn (d i INTER E n) (cons x y))) i))’
       >- (MATCH_MP_TAC pos_fn_integral_suminf >> simp [] \\
           CONJ_TAC >- (rpt STRIP_TAC >> MATCH_MP_TAC pos_fn_integral_pos \\
                        simp [INDICATOR_FN_POS]) \\
           Q.X_GEN_TAC ‘i’ >> Q.PAT_X_ASSUM ‘!x. d x IN D n’ (MP_TAC o (Q.SPEC ‘i’)) \\
           RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) >> BETA_TAC >> Rewr' \\
       MATCH_MP_TAC ext_suminf_eq >> Q.X_GEN_TAC ‘i’ >> BETA_TAC \\
       Q.PAT_X_ASSUM ‘!x. d x IN D n’ (MP_TAC o (Q.SPEC ‘i’)) \\
       RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION] ]) >> DISCH_TAC
 (* clean up *)
 >> Q.PAT_X_ASSUM ‘!n d y. pos_fn_integral (X,A,u) f <> PosInf’ K_TAC
 >> Q.PAT_X_ASSUM ‘!n d y. pos_fn_integral (X,A,u) f <> NegInf’ K_TAC
 >> Q.PAT_X_ASSUM ‘!n d x. pos_fn_integral (Y,B,v) f <> PosInf’ K_TAC
 >> Q.PAT_X_ASSUM ‘!n d x. pos_fn_integral (Y,B,v) f <> NegInf’ K_TAC
 (* applying DYNKIN_SUBSET and DYNKIN_THM *)
 >> Know ‘!n. subsets (general_sigma cons (X,A) (Y,B)) SUBSET D n’
 >- (GEN_TAC >> rw [general_sigma_def] \\
     Suff ‘sigma (general_cross cons X Y) (general_prod cons A B) =
           dynkin (general_cross cons X Y) (general_prod cons A B)’
     >- (Rewr' \\
         MATCH_MP_TAC (REWRITE_RULE [space_def, subsets_def]
                        (Q.SPECL [‘general_prod cons A B’, ‘(general_cross cons X Y,D n)’]
                          (INST_TYPE [alpha |-> gamma] DYNKIN_SUBSET))) >> art []) \\
     MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC DYNKIN_THM \\
     CONJ_TAC >- (rw [subset_class_def, IN_general_prod] \\
                  MATCH_MP_TAC general_SUBSET_CROSS \\
                  fs [sigma_algebra_def, algebra_def, subset_class_def]) \\
     qx_genl_tac [‘x’, ‘y’] >> STRIP_TAC \\
     Q.PAT_X_ASSUM ‘x IN general_prod cons A B’
        (STRIP_ASSUME_TAC o (REWRITE_RULE [IN_general_prod])) \\
     rename1 ‘x = general_cross cons s1 t1’ \\
     Q.PAT_X_ASSUM ‘y IN general_prod cons A B’
        (STRIP_ASSUME_TAC o (REWRITE_RULE [IN_general_prod])) \\
     rename1 ‘y = general_cross cons s2 t2’ \\
     rw [IN_general_prod] \\
     qexistsl_tac [‘s1 INTER s2’, ‘t1 INTER t2’] \\
     CONJ_TAC >- (MATCH_MP_TAC general_INTER_CROSS \\
                  qexistsl_tac [‘car’, ‘cdr’] >> art []) \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                  (ISPEC “(X,A) :'a algebra” SIGMA_ALGEBRA_INTER)) \\
       ASM_REWRITE_TAC [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                  (ISPEC “(Y,B) :'b algebra” SIGMA_ALGEBRA_INTER)) \\
       ASM_REWRITE_TAC [] ]) >> DISCH_TAC
 (* stage work *)
 >> Know ‘exhausting_sequence (general_cross cons X Y,general_prod cons A B) E’
 >- (Q.UNABBREV_TAC ‘E’ >> MATCH_MP_TAC exhausting_sequence_general_cross >> art [])
 >> DISCH_THEN (STRIP_ASSUME_TAC o
                (REWRITE_RULE [space_def, subsets_def, exhausting_sequence_alt,
                               IN_FUNSET, IN_UNIV]))
 >> STRONG_CONJ_TAC (* Borel_measurable *)
 >- (GEN_TAC >> DISCH_TAC \\
    ‘!n. s IN D n’ by METIS_TAC [SUBSET_DEF] \\
    ‘s SUBSET (general_cross cons X Y)’
       by (POP_ASSUM MP_TAC >> RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
    ‘s = s INTER (general_cross cons X Y)’ by ASM_SET_TAC [] >> POP_ORW \\
     Know ‘!x y. indicator_fn (s INTER (general_cross cons X Y)) (cons x y) =
                 sup (IMAGE (\n. indicator_fn (s INTER (E n)) (cons x y)) UNIV)’
     >- (rw [Once EQ_SYM_EQ, sup_eq', IN_IMAGE, IN_UNIV] >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           MATCH_MP_TAC INDICATOR_FN_MONO >> ASM_SET_TAC [],
           (* goal 2 (of 2) *)
           rename1 ‘!z. (?n. z = indicator_fn (s INTER E n) (cons x y)) ==> z <= N’ \\
           Cases_on ‘!n. indicator_fn (s INTER E n) (cons x y) = 0’
           >- (Q.PAT_X_ASSUM ‘_ = general_cross cons X Y’ (ONCE_REWRITE_TAC o wrap o SYM) \\
               POP_ASSUM MP_TAC \\
               rw [indicator_fn_def] >> METIS_TAC [ne_01]) \\
           fs [] >> FIRST_X_ASSUM MATCH_MP_TAC \\
           rename1 ‘indicator_fn (s INTER E i) (cons x y) <> 0’ \\
           Q.EXISTS_TAC ‘i’ \\
           Q.PAT_X_ASSUM ‘_ = general_cross cons X Y’ (ONCE_REWRITE_TAC o wrap o SYM) \\
           POP_ASSUM MP_TAC >> rw [indicator_fn_def] \\
           METIS_TAC [] ]) >> Rewr' \\
     CONJ_TAC (* Borel_measurable #1 *)
     >- (rpt STRIP_TAC \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP >> simp [] \\
         Q.EXISTS_TAC ‘\n y. indicator_fn (s INTER E n) (cons x y)’ >> simp [] \\
         reverse CONJ_TAC
         >- (qx_genl_tac [‘n’, ‘y’] >> DISCH_TAC \\
             MATCH_MP_TAC INDICATOR_FN_MONO \\
             Suff ‘E n SUBSET E (SUC n)’ >- ASM_SET_TAC [] \\
             FIRST_X_ASSUM MATCH_MP_TAC >> RW_TAC arith_ss []) \\
         GEN_TAC >> Q.PAT_X_ASSUM ‘!n. s IN D n’ (MP_TAC o (Q.SPEC ‘n’)) \\
         RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
     CONJ_TAC (* Borel_measurable #2 *)
     >- (rpt STRIP_TAC \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP >> simp [] \\
         Q.EXISTS_TAC ‘\n x. indicator_fn (s INTER E n) (cons x y)’ >> simp [] \\
         reverse CONJ_TAC
         >- (qx_genl_tac [‘n’, ‘x’] >> DISCH_TAC \\
             MATCH_MP_TAC INDICATOR_FN_MONO \\
             Suff ‘E n SUBSET E (SUC n)’ >- ASM_SET_TAC [] \\
             FIRST_X_ASSUM MATCH_MP_TAC >> RW_TAC arith_ss []) \\
         GEN_TAC >> Q.PAT_X_ASSUM ‘!n. s IN D n’ (MP_TAC o (Q.SPEC ‘n’)) \\
         RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
  (* applying lebesgue_monotone_convergence (Beppo Levi) *)
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                  (Q.SPEC ‘(Y,B,v)’ IN_MEASURABLE_BOREL_EQ)) \\
       Q.EXISTS_TAC ‘\y. sup (IMAGE (\n. pos_fn_integral (X,A,u)
                                           (\x. indicator_fn (s INTER E n) (cons x y))) UNIV)’ \\
       reverse CONJ_TAC
       >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP >> simp [] \\
           Q.EXISTS_TAC ‘\n y. pos_fn_integral (X,A,u)
                                 (\x. indicator_fn (s INTER E n) (cons x y))’ >> simp [] \\
           CONJ_TAC >- (GEN_TAC >> Q.PAT_X_ASSUM ‘!n. s IN D n’ (MP_TAC o (Q.SPEC ‘n’)) \\
                        RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
           qx_genl_tac [‘n’, ‘y’] >> DISCH_TAC \\
           MATCH_MP_TAC pos_fn_integral_mono >> simp [INDICATOR_FN_POS] \\
           rpt STRIP_TAC >> MATCH_MP_TAC INDICATOR_FN_MONO \\
           Suff ‘E n SUBSET E (SUC n)’ >- ASM_SET_TAC [] \\
           FIRST_X_ASSUM MATCH_MP_TAC >> RW_TAC arith_ss []) \\
       Q.X_GEN_TAC ‘y’ >> DISCH_TAC >> BETA_TAC \\
       HO_MATCH_MP_TAC lebesgue_monotone_convergence >> simp [INDICATOR_FN_POS] \\
       CONJ_TAC >- (GEN_TAC >> Q.PAT_X_ASSUM ‘!n. s IN D n’ (MP_TAC o (Q.SPEC ‘n’)) \\
                    RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
       rw [ext_mono_increasing_def] \\
       MATCH_MP_TAC INDICATOR_FN_MONO \\
       Suff ‘E n SUBSET E (SUC n)’ >- ASM_SET_TAC [] \\
       FIRST_X_ASSUM MATCH_MP_TAC >> RW_TAC arith_ss [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                  (Q.SPEC ‘(X,A,u)’ IN_MEASURABLE_BOREL_EQ)) \\
       Q.EXISTS_TAC ‘\x. sup (IMAGE (\n. pos_fn_integral (Y,B,v)
                                           (\y. indicator_fn (s INTER E n) (cons x y))) UNIV)’ \\
       reverse CONJ_TAC
       >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP >> simp [] \\
           Q.EXISTS_TAC ‘\n x. pos_fn_integral (Y,B,v)
                                 (\y. indicator_fn (s INTER E n) (cons x y))’ >> simp [] \\
           CONJ_TAC >- (GEN_TAC >> Q.PAT_X_ASSUM ‘!n. s IN D n’ (MP_TAC o (Q.SPEC ‘n’)) \\
                        RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
           qx_genl_tac [‘n’, ‘x’] >> DISCH_TAC \\
           MATCH_MP_TAC pos_fn_integral_mono >> simp [INDICATOR_FN_POS] \\
           Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
           MATCH_MP_TAC INDICATOR_FN_MONO \\
           Suff ‘E n SUBSET E (SUC n)’ >- ASM_SET_TAC [] \\
           FIRST_X_ASSUM MATCH_MP_TAC >> RW_TAC arith_ss []) \\
       Q.X_GEN_TAC ‘x’ >> DISCH_TAC >> BETA_TAC \\
       HO_MATCH_MP_TAC lebesgue_monotone_convergence >> simp [INDICATOR_FN_POS] \\
       CONJ_TAC >- (GEN_TAC >> Q.PAT_X_ASSUM ‘!n. s IN D n’ (MP_TAC o (Q.SPEC ‘n’)) \\
                    RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
       rw [ext_mono_increasing_def] \\
       MATCH_MP_TAC INDICATOR_FN_MONO \\
       Suff ‘E n SUBSET E (SUC n)’ >- ASM_SET_TAC [] \\
       FIRST_X_ASSUM MATCH_MP_TAC >> RW_TAC arith_ss [] ]) >> DISCH_TAC
 (* final battle *)
 >> Q.EXISTS_TAC ‘\s. pos_fn_integral (X,A,u)
                        (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn s (cons x y)))’
 >> REWRITE_TAC [CONJ_ASSOC]
 >> reverse CONJ_TAC (* swap of integrals *)
 >- (RW_TAC std_ss [] \\
    ‘!n. s IN D n’ by METIS_TAC [SUBSET_DEF] \\
    ‘s SUBSET (general_cross cons X Y)’
       by (POP_ASSUM MP_TAC >> RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
    ‘s = s INTER (general_cross cons X Y)’ by ASM_SET_TAC [] >> POP_ORW \\
     Know ‘!x y. indicator_fn (s INTER (general_cross cons X Y)) (cons x y) =
                 sup (IMAGE (\n. indicator_fn (s INTER (E n)) (cons x y)) UNIV)’
     >- (rw [Once EQ_SYM_EQ, sup_eq', IN_IMAGE, IN_UNIV] >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           MATCH_MP_TAC INDICATOR_FN_MONO >> ASM_SET_TAC [],
           (* goal 2 (of 2) *)
           rename1 ‘!z. (?n. z = indicator_fn (s INTER E n) (cons x y)) ==> z <= N’ \\
           Cases_on ‘!n. indicator_fn (s INTER E n) (cons x y) = 0’
           >- (Q.PAT_X_ASSUM ‘_ = general_cross cons X Y’ (ONCE_REWRITE_TAC o wrap o SYM) \\
               POP_ASSUM MP_TAC \\
               rw [indicator_fn_def] >> METIS_TAC [ne_01]) \\
           fs [] >> FIRST_X_ASSUM MATCH_MP_TAC \\
           rename1 ‘indicator_fn (s INTER E i) (cons x y) <> 0’ \\
           Q.EXISTS_TAC ‘i’ \\
           Q.PAT_X_ASSUM ‘_ = general_cross cons X Y’ (ONCE_REWRITE_TAC o wrap o SYM) \\
           POP_ASSUM MP_TAC >> rw [indicator_fn_def] \\
           METIS_TAC [] ]) >> Rewr' \\
     Know ‘!x y. 0 <= sup (IMAGE (\n. indicator_fn (s INTER E n) (cons x y)) UNIV)’
     >- (rw [le_sup'] >> MATCH_MP_TAC le_trans \\
         Q.EXISTS_TAC ‘indicator_fn (s INTER E 0) (cons x y)’ \\
         simp [INDICATOR_FN_POS] >> POP_ASSUM MATCH_MP_TAC \\
         Q.EXISTS_TAC ‘0’ >> REWRITE_TAC []) >> DISCH_TAC \\
  (* applying pos_fn_integral_cong *)
     Know ‘pos_fn_integral (X,A,u)
             (\x. pos_fn_integral (Y,B,v)
                    (\y. sup (IMAGE (\n. indicator_fn (s INTER E n) (cons x y)) UNIV))) =
           pos_fn_integral (X,A,u)
             (\x. sup (IMAGE (\n. pos_fn_integral (Y,B,v)
                                    (\y. indicator_fn (s INTER E n) (cons x y))) UNIV))’
     >- (MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                    (Q.SPEC ‘(X,A,u)’ pos_fn_integral_cong)) >> simp [] \\
         CONJ_TAC >- (rpt STRIP_TAC >> MATCH_MP_TAC pos_fn_integral_pos >> simp []) \\
         CONJ_TAC >- (rw [le_sup'] >> MATCH_MP_TAC le_trans \\
                      Q.EXISTS_TAC ‘pos_fn_integral (Y,B,v)
                                     (\y. indicator_fn (s INTER E 0) (cons x y))’ \\
                      reverse CONJ_TAC >- (POP_ASSUM MATCH_MP_TAC \\
                                           Q.EXISTS_TAC ‘0’ >> REWRITE_TAC []) \\
                      MATCH_MP_TAC pos_fn_integral_pos >> simp [INDICATOR_FN_POS]) \\
         rpt STRIP_TAC \\
         HO_MATCH_MP_TAC lebesgue_monotone_convergence >> simp [INDICATOR_FN_POS] \\
         CONJ_TAC >- (GEN_TAC >> Q.PAT_X_ASSUM ‘!n. s IN D n’ (MP_TAC o (Q.SPEC ‘n’)) \\
                      RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
         rw [ext_mono_increasing_def] \\
         MATCH_MP_TAC INDICATOR_FN_MONO \\
         Suff ‘E n SUBSET E (SUC n)’ >- ASM_SET_TAC [] \\
         FIRST_X_ASSUM MATCH_MP_TAC >> RW_TAC arith_ss []) >> Rewr' \\
     Know ‘pos_fn_integral (Y,B,v)
             (\y. pos_fn_integral (X,A,u)
                    (\x. sup (IMAGE (\n. indicator_fn (s INTER E n) (cons x y)) UNIV))) =
           pos_fn_integral (Y,B,v)
             (\y. sup (IMAGE (\n. pos_fn_integral (X,A,u)
                                    (\x. indicator_fn (s INTER E n) (cons x y))) UNIV))’
     >- (MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                    (Q.SPEC ‘(Y,B,v)’ pos_fn_integral_cong)) >> simp [] \\
         CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                      MATCH_MP_TAC pos_fn_integral_pos >> simp []) \\
         CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> rw [le_sup'] >> MATCH_MP_TAC le_trans \\
                      Q.EXISTS_TAC ‘pos_fn_integral (X,A,u)
                                     (\x. indicator_fn (s INTER E 0) (cons x y))’ \\
                      reverse CONJ_TAC >- (POP_ASSUM MATCH_MP_TAC \\
                                           Q.EXISTS_TAC ‘0’ >> REWRITE_TAC []) \\
                      MATCH_MP_TAC pos_fn_integral_pos >> simp [INDICATOR_FN_POS]) \\
         Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
         HO_MATCH_MP_TAC lebesgue_monotone_convergence >> simp [INDICATOR_FN_POS] \\
         CONJ_TAC >- (GEN_TAC >> Q.PAT_X_ASSUM ‘!n. s IN D n’ (MP_TAC o (Q.SPEC ‘n’)) \\
                      RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
         rw [ext_mono_increasing_def] \\
         MATCH_MP_TAC INDICATOR_FN_MONO \\
         Suff ‘E n SUBSET E (SUC n)’ >- ASM_SET_TAC [] \\
         FIRST_X_ASSUM MATCH_MP_TAC >> RW_TAC arith_ss []) >> Rewr' \\
     Know ‘pos_fn_integral (X,A,u)
             (\x. sup (IMAGE (\n. pos_fn_integral (Y,B,v)
                                    (\y. indicator_fn (s INTER E n) (cons x y))) UNIV)) =
           sup (IMAGE (\n. pos_fn_integral (X,A,u)
                             (\x. pos_fn_integral (Y,B,v)
                                    (\y. indicator_fn (s INTER E n) (cons x y)))) UNIV)’
     >- (HO_MATCH_MP_TAC lebesgue_monotone_convergence >> simp [] \\
         CONJ_TAC >- (GEN_TAC >> Q.PAT_X_ASSUM ‘!n. s IN D n’ (MP_TAC o (Q.SPEC ‘n’)) \\
                      RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
         CONJ_TAC >- (rpt STRIP_TAC \\
                      MATCH_MP_TAC pos_fn_integral_pos >> simp [INDICATOR_FN_POS]) \\
         rw [ext_mono_increasing_def] \\
         MATCH_MP_TAC pos_fn_integral_mono >> simp [INDICATOR_FN_POS] \\
         Q.X_GEN_TAC ‘y’ >> DISCH_TAC >> MATCH_MP_TAC INDICATOR_FN_MONO \\
         rename1 ‘n <= m’ >> Suff ‘E n SUBSET E m’ >- ASM_SET_TAC [] \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> Rewr' \\
     Know ‘pos_fn_integral (Y,B,v)
             (\y. sup (IMAGE (\n. pos_fn_integral (X,A,u)
                                    (\x. indicator_fn (s INTER E n) (cons x y))) UNIV)) =
           sup (IMAGE (\n. pos_fn_integral (Y,B,v)
                             (\y. pos_fn_integral (X,A,u)
                                    (\x. indicator_fn (s INTER E n) (cons x y)))) UNIV)’
     >- (HO_MATCH_MP_TAC lebesgue_monotone_convergence >> simp [] \\
         CONJ_TAC >- (GEN_TAC >> Q.PAT_X_ASSUM ‘!n. s IN D n’ (MP_TAC o (Q.SPEC ‘n’)) \\
                      RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION]) \\
         CONJ_TAC >- (rpt STRIP_TAC \\
                      MATCH_MP_TAC pos_fn_integral_pos >> simp [INDICATOR_FN_POS]) \\
         rw [ext_mono_increasing_def] \\
         MATCH_MP_TAC pos_fn_integral_mono >> simp [INDICATOR_FN_POS] \\
         rpt STRIP_TAC >> MATCH_MP_TAC INDICATOR_FN_MONO \\
         rename1 ‘n <= m’ >> Suff ‘E n SUBSET E m’ >- ASM_SET_TAC [] \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> Rewr' \\
     Suff ‘!n. pos_fn_integral (X,A,u)
                 (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (s INTER E n) (cons x y))) =
               pos_fn_integral (Y,B,v)
                 (\y. pos_fn_integral (X,A,u)
                        (\x. indicator_fn (s INTER E n) (cons x y)))’ >- rw [] \\
     GEN_TAC >> Q.PAT_X_ASSUM ‘!n. s IN D n’ (MP_TAC o (Q.SPEC ‘n’)) \\
     RW_TAC std_ss [Abbr ‘D’, GSPECIFICATION])
 >> reverse CONJ_TAC (* compatibility with m0 *)
 >- (Q.X_GEN_TAC ‘d’ >> simp [IN_general_prod] \\
     DISCH_THEN (qx_choosel_then [‘s’, ‘t’] STRIP_ASSUME_TAC) \\
     Q.PAT_X_ASSUM ‘d = general_cross cons s t’ (ONCE_REWRITE_TAC o wrap) \\
     Know ‘!x y. indicator_fn (general_cross cons s t) (cons x y) =
                 indicator_fn s x * indicator_fn t y’
     >- (rpt GEN_TAC >> MATCH_MP_TAC indicator_fn_general_cross \\
         qexistsl_tac [‘car’, ‘cdr’] >> art []) >> Rewr' \\
     Know ‘!x. pos_fn_integral (Y,B,v) (\y. indicator_fn s x * indicator_fn t y) =
               indicator_fn s x * pos_fn_integral (Y,B,v) (indicator_fn t)’
     >- (GEN_TAC \\
        ‘?r. 0 <= r /\ (indicator_fn s x = Normal r)’
           by METIS_TAC [indicator_fn_normal, extreal_of_num_def, extreal_le_eq] >> POP_ORW \\
         MATCH_MP_TAC pos_fn_integral_cmul >> simp [INDICATOR_FN_POS]) >> Rewr' \\
     Know ‘pos_fn_integral (Y,B,v) (indicator_fn t) = measure (Y,B,v) t’
     >- (MATCH_MP_TAC pos_fn_integral_indicator >> rw []) >> Rewr' >> simp [] \\
     GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [mul_comm] \\
     IMP_RES_TAC MEASURE_SPACE_POSITIVE >> rfs [positive_def] \\
     Know ‘pos_fn_integral (X,A,u) (\x. v t * indicator_fn s x) =
           v t * pos_fn_integral (X,A,u) (indicator_fn s)’
     >- (Know ‘indicator_fn s = fn_plus (indicator_fn s)’
         >- (MATCH_MP_TAC EQ_SYM \\
             MATCH_MP_TAC FN_PLUS_POS_ID >> rw [INDICATOR_FN_POS]) >> Rewr' \\
         MATCH_MP_TAC pos_fn_integral_cmult >> simp [] \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR \\
         Q.EXISTS_TAC ‘s’ >> simp []) >> Rewr' \\
     Know ‘pos_fn_integral (X,A,u) (indicator_fn s) = measure (X,A,u) s’
     >- (MATCH_MP_TAC pos_fn_integral_indicator >> rw []) >> Rewr' \\
     rw [Once mul_comm])
 >> reverse CONJ_TAC (* sigma-finiteness *)
 >- (Q.EXISTS_TAC ‘E’ \\
     CONJ_TAC
     >- (rw [exhausting_sequence_def, IN_FUNSET, IN_UNIV] \\
         Suff ‘(general_prod cons A B) SUBSET subsets (general_sigma cons (X,A) (Y,B))’
         >- METIS_TAC [SUBSET_DEF] \\
         REWRITE_TAC [general_sigma_def, space_def, subsets_def] \\
         REWRITE_TAC [SIGMA_SUBSET_SUBSETS]) \\
     RW_TAC std_ss [Abbr ‘E’] \\
     Know ‘!x y. indicator_fn (general_cross cons (a n) (b n)) (cons x y) =
                 indicator_fn (a n) x * indicator_fn (b n) y’
     >- (rpt GEN_TAC >> MATCH_MP_TAC indicator_fn_general_cross \\
         qexistsl_tac [‘car’, ‘cdr’] >> art []) >> Rewr' \\
     IMP_RES_TAC MEASURE_SPACE_POSITIVE \\
     REV_FULL_SIMP_TAC std_ss [positive_def, exhausting_sequence_def,
                               IN_FUNSET, IN_UNIV, space_def, subsets_def,
                               measurable_sets_def, measure_def] \\
     Know ‘!x. pos_fn_integral (Y,B,v) (\y. indicator_fn (a n) x * indicator_fn (b n) y) =
               indicator_fn (a n) x * pos_fn_integral (Y,B,v) (indicator_fn (b n))’
     >- (GEN_TAC \\
        ‘?r. 0 <= r /\ (indicator_fn (a n) x = Normal r)’
           by METIS_TAC [indicator_fn_normal, extreal_of_num_def, extreal_le_eq] >> POP_ORW \\
         MATCH_MP_TAC pos_fn_integral_cmul >> simp [INDICATOR_FN_POS]) >> Rewr' \\
     Know ‘pos_fn_integral (Y,B,v) (indicator_fn (b n)) = measure (Y,B,v) (b n)’
     >- (MATCH_MP_TAC pos_fn_integral_indicator >> rw []) >> Rewr' >> simp [] \\
     GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [mul_comm] \\
     Know ‘v (b n) <> PosInf /\ v (b n) <> NegInf’
     >- (CONJ_TAC >- art [lt_infty] \\
         MATCH_MP_TAC pos_not_neginf >> simp []) >> STRIP_TAC \\
     Know ‘pos_fn_integral (X,A,u) (\x. v (b n) * indicator_fn (a n) x) =
           v (b n) * pos_fn_integral (X,A,u) (indicator_fn (a n))’
     >- (‘?r. 0 <= r /\ (v (b n) = Normal r)’
           by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_le_eq] >> POP_ORW \\
         MATCH_MP_TAC pos_fn_integral_cmul >> simp [INDICATOR_FN_POS]) >> Rewr' \\
     Know ‘pos_fn_integral (X,A,u) (indicator_fn (a n)) = measure (X,A,u) (a n)’
     >- (MATCH_MP_TAC pos_fn_integral_indicator >> simp []) >> Rewr' >> simp [] \\
     Know ‘u (a n) <> PosInf /\ u (a n) <> NegInf’
     >- (CONJ_TAC >- art [lt_infty] \\
         MATCH_MP_TAC pos_not_neginf >> simp []) >> STRIP_TAC \\
    ‘?r1. u (a n) = Normal r1’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?r2. v (b n) = Normal r2’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     REWRITE_TAC [extreal_mul_def, lt_infty, extreal_not_infty])
 (* last three goals *)
 >> rw [measure_space_def]
 (* 1. sigma_algebra *)
 >- (Know ‘(general_cross cons X Y,subsets (general_sigma cons (X,A) (Y,B))) =
           general_sigma cons (X,A) (Y,B)’
     >- (rw [general_sigma_def] >> METIS_TAC [SPACE, SPACE_SIGMA]) >> Rewr' \\
     MATCH_MP_TAC sigma_algebra_general_sigma >> simp [] \\
     fs [sigma_algebra_def, algebra_def])
 (* 2. positive *)
 >- (rw [positive_def] >- (simp [pos_fn_integral_zero]) \\
     MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
     MATCH_MP_TAC pos_fn_integral_pos >> rw [INDICATOR_FN_POS])
 (* 3. countably_additive *)
 >> rw [countably_additive_def, IN_FUNSET, IN_UNIV, o_DEF]
 >> Know ‘!x y. indicator_fn (BIGUNION (IMAGE f UNIV)) (cons x y) =
                suminf (\n. indicator_fn (f n) (cons x y))’
 >- (RW_TAC std_ss [Once EQ_SYM_EQ] \\
     MATCH_MP_TAC indicator_fn_suminf >> simp []) >> Rewr'
 >> Know ‘pos_fn_integral (X,A,u)
            (\x. pos_fn_integral (Y,B,v) (\y. suminf (\n. indicator_fn (f n) (cons x y)))) =
          pos_fn_integral (X,A,u)
            (\x. suminf (\n. pos_fn_integral (Y,B,v) (\y. indicator_fn (f n) (cons x y))))’
 >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
     CONJ_TAC >- (rpt STRIP_TAC >> MATCH_MP_TAC pos_fn_integral_pos >> simp [] \\
                  Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                  MATCH_MP_TAC ext_suminf_pos >> rw [INDICATOR_FN_POS]) \\
     CONJ_TAC >- (rpt STRIP_TAC >> MATCH_MP_TAC ext_suminf_pos >> rw [] \\
                  MATCH_MP_TAC pos_fn_integral_pos >> rw [INDICATOR_FN_POS]) \\
     rpt STRIP_TAC \\
  (* preparing for pos_fn_integral_suminf *)
    ‘pos_fn_integral (Y,B,v) (\y. suminf (\n. indicator_fn (f n) (cons x y))) =
     pos_fn_integral (Y,B,v) (\y. suminf (\n. (\n y. indicator_fn (f n) (cons x y)) n y))’
       by PROVE_TAC [] >> POP_ORW \\
    ‘suminf (\n. pos_fn_integral (Y,B,v) (\y. indicator_fn (f n) (cons x y))) =
     suminf (\n. pos_fn_integral (Y,B,v) ((\n y. indicator_fn (f n) (cons x y)) n))’
       by PROVE_TAC [] >> POP_ORW \\
     MATCH_MP_TAC pos_fn_integral_suminf >> simp [INDICATOR_FN_POS]) >> Rewr'
 >> Know ‘pos_fn_integral (X,A,u)
            (\x. suminf (\n. (\n x. pos_fn_integral (Y,B,v)
                                      (\y. indicator_fn (f n) (cons x y))) n x)) =
          suminf (\n. pos_fn_integral (X,A,u)
                        ((\n x. pos_fn_integral (Y,B,v) (\y. indicator_fn (f n) (cons x y))) n))’
 >- (MATCH_MP_TAC pos_fn_integral_suminf >> rw [] \\
     MATCH_MP_TAC pos_fn_integral_pos >> rw [INDICATOR_FN_POS])
 >> BETA_TAC >> Rewr
QED

(* Theorem 14.5 [1, p.139], cf. CARATHEODORY_SEMIRING *)
Theorem EXISTENCE_OF_PROD_MEASURE :
   !(X :'a set) (Y :'b set) A B u v m0.
       sigma_finite_measure_space (X,A,u) /\
       sigma_finite_measure_space (Y,B,v) /\
       (!s t. s IN A /\ t IN B ==> (m0 (s CROSS t) = u s * v t)) ==>
       (!s. s IN subsets ((X,A) CROSS (Y,B)) ==>
           (!x. x IN X ==> (\y. indicator_fn s (x,y)) IN measurable (Y,B) Borel) /\
           (!y. y IN Y ==> (\x. indicator_fn s (x,y)) IN measurable (X,A) Borel) /\
           (\y. pos_fn_integral (X,A,u) (\x. indicator_fn s (x,y))) IN measurable (Y,B) Borel /\
           (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn s (x,y))) IN measurable (X,A) Borel) /\
       ?m. sigma_finite_measure_space (X CROSS Y,subsets ((X,A) CROSS (Y,B)),m) /\
           (!s. s IN (prod_sets A B) ==> (m s = m0 s)) /\
           (!s. s IN subsets ((X,A) CROSS (Y,B)) ==>
               (m s = pos_fn_integral (Y,B,v)
                        (\y. pos_fn_integral (X,A,u) (\x. indicator_fn s (x,y)))) /\
               (m s = pos_fn_integral (X,A,u)
                        (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn s (x,y)))))
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘pair$,’,‘FST’,‘SND’,‘X’,‘Y’,‘A’,‘B’,‘u’,‘v’,‘m0’]
                    (INST_TYPE [gamma |-> “:'a # 'b”] existence_of_prod_measure_general))
 >> RW_TAC std_ss [GSYM CROSS_ALT, GSYM prod_sets_alt, GSYM prod_sigma_alt,
                   pair_operation_pair]
QED

(* A derived version of EXISTENCE_OF_PROD_MEASURE using ‘integral’ instead of
  ‘pos_fn_integral’ (NOTE: this theorem has no general and FCP versions)
 *)
Theorem EXISTENCE_OF_PROD_MEASURE' :
   !(X :'a set) (Y :'b set) A B u v m0.
       sigma_finite_measure_space (X,A,u) /\
       sigma_finite_measure_space (Y,B,v) /\
       (!s t. s IN A /\ t IN B ==> (m0 (s CROSS t) = u s * v t)) ==>
       (!s. s IN subsets ((X,A) CROSS (Y,B)) ==>
           (!x. x IN X ==> (\y. indicator_fn s (x,y)) IN measurable (Y,B) Borel) /\
           (!y. y IN Y ==> (\x. indicator_fn s (x,y)) IN measurable (X,A) Borel) /\
           (\y. integral (X,A,u) (\x. indicator_fn s (x,y))) IN measurable (Y,B) Borel /\
           (\x. integral (Y,B,v) (\y. indicator_fn s (x,y))) IN measurable (X,A) Borel) /\
       ?m. sigma_finite_measure_space (X CROSS Y,subsets ((X,A) CROSS (Y,B)),m) /\
           (!s. s IN (prod_sets A B) ==> (m s = m0 s)) /\
           (!s. s IN subsets ((X,A) CROSS (Y,B)) ==>
               (m s = integral (Y,B,v) (\y. integral (X,A,u) (\x. indicator_fn s (x,y)))) /\
               (m s = integral (X,A,u) (\x. integral (Y,B,v) (\y. indicator_fn s (x,y)))))
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘X’,‘Y’,‘A’,‘B’,‘u’,‘v’,‘m0’] EXISTENCE_OF_PROD_MEASURE)
 >> FULL_SIMP_TAC std_ss [sigma_finite_measure_space_def]
 >> RW_TAC std_ss [] (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
     ‘(\y. pos_fn_integral (X,A,u) (\x. indicator_fn s (x,y))) IN Borel_measurable (Y,B)’
        by METIS_TAC [] \\
      MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                 (Q.SPEC ‘(Y,B,v)’ IN_MEASURABLE_BOREL_EQ)) \\
      Q.EXISTS_TAC ‘\y. pos_fn_integral (X,A,u) (\x. indicator_fn s (x,y))’ >> rw [] \\
      MATCH_MP_TAC integral_pos_fn >> rw [INDICATOR_FN_POS],
      (* goal 2 (of 3) *)
     ‘(\x. pos_fn_integral (Y,B,v) (\y. indicator_fn s (x,y))) IN Borel_measurable (X,A)’
        by METIS_TAC [] \\
      MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                 (Q.SPEC ‘(X,A,u)’ IN_MEASURABLE_BOREL_EQ)) \\
      Q.EXISTS_TAC ‘\x. pos_fn_integral (Y,B,v) (\y. indicator_fn s (x,y))’ >> rw [] \\
      MATCH_MP_TAC integral_pos_fn >> rw [INDICATOR_FN_POS],
      (* goal 3 (of 3) *)
      Q.EXISTS_TAC ‘m’ >> RW_TAC std_ss [] >| (* 2 subgoals *)
      [ (* goal 3.1 (of 2) *)
        Know ‘!y. integral (X,A,u) (\x. indicator_fn s (x,y)) =
                  pos_fn_integral (X,A,u) (\x. indicator_fn s (x,y))’
        >- (GEN_TAC \\
            MATCH_MP_TAC integral_pos_fn >> rw [INDICATOR_FN_POS]) >> Rewr' \\
        MATCH_MP_TAC EQ_SYM \\
        MATCH_MP_TAC integral_pos_fn >> simp [] \\
        Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
        MATCH_MP_TAC pos_fn_integral_pos >> rw [INDICATOR_FN_POS],
        (* goal 3.2 (of 2) *)
       ‘pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. indicator_fn s (x,y))) =
        pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn s (x,y)))’
           by METIS_TAC [] >> POP_ORW \\
        MATCH_MP_TAC EQ_SYM \\
        Know ‘!x. integral (Y,B,v) (\y. indicator_fn s (x,y)) =
                  pos_fn_integral (Y,B,v) (\y. indicator_fn s (x,y))’
        >- (GEN_TAC >> MATCH_MP_TAC integral_pos_fn >> rw [INDICATOR_FN_POS]) >> Rewr' \\
        MATCH_MP_TAC integral_pos_fn >> simp [] \\
        rpt STRIP_TAC \\
        MATCH_MP_TAC pos_fn_integral_pos >> rw [INDICATOR_FN_POS] ] ]
QED

(* FCP version of EXISTENCE_OF_PROD_MEASURE *)
Theorem existence_of_prod_measure :
   !(X :'a['b] set) (Y :'a['c] set) A B u v m0.
       FINITE univ(:'b) /\ FINITE univ(:'c) /\
       sigma_finite_measure_space (X,A,u) /\
       sigma_finite_measure_space (Y,B,v) /\
       (!s t. s IN A /\ t IN B ==> (m0 (fcp_cross s t) = u s * v t)) ==>
       (!s. s IN subsets (fcp_sigma (X,A) (Y,B)) ==>
           (!x. x IN X ==> (\y. indicator_fn s (FCP_CONCAT x y)) IN measurable (Y,B) Borel) /\
           (!y. y IN Y ==> (\x. indicator_fn s (FCP_CONCAT x y)) IN measurable (X,A) Borel) /\
           (\y. pos_fn_integral (X,A,u)
                  (\x. indicator_fn s (FCP_CONCAT x y))) IN measurable (Y,B) Borel /\
           (\x. pos_fn_integral (Y,B,v)
                  (\y. indicator_fn s (FCP_CONCAT x y))) IN measurable (X,A) Borel) /\
       ?m. sigma_finite_measure_space (fcp_cross X Y,subsets (fcp_sigma (X,A) (Y,B)),m) /\
           (!s. s IN (fcp_prod A B) ==> (m s = m0 s)) /\
           (!s. s IN subsets (fcp_sigma (X,A) (Y,B)) ==>
               (m s = pos_fn_integral (Y,B,v)
                        (\y. pos_fn_integral (X,A,u) (\x. indicator_fn s (FCP_CONCAT x y)))) /\
               (m s = pos_fn_integral (X,A,u)
                        (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn s (FCP_CONCAT x y)))))
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘FCP_CONCAT’,‘FCP_FST’,‘FCP_SND’,‘X’,‘Y’,‘A’,‘B’,‘u’,‘v’,‘m0’]
                    (((INST_TYPE [“:'temp1” |-> “:'a['b]”]) o
                      (INST_TYPE [“:'temp2” |-> “:'a['c]”]) o
                      (INST_TYPE [gamma |-> “:'a['b + 'c]”]) o
                      (INST_TYPE [alpha |-> “:'temp1”]) o
                      (INST_TYPE [beta |-> “:'temp2”])) existence_of_prod_measure_general))
 >> RW_TAC std_ss [GSYM fcp_cross_alt, GSYM fcp_prod_alt, GSYM fcp_sigma_alt,
                   pair_operation_FCP_CONCAT]
QED

(* Application: 2-dimensional Borel measure space *)
local
  val thm = Q.prove (
     ‘?m. sigma_finite_measure_space m /\
         (m_space m = UNIV CROSS UNIV) /\
         (measurable_sets m = subsets ((UNIV,subsets borel) CROSS (UNIV,subsets borel))) /\
         (!s t. s IN subsets borel /\ t IN subsets borel ==>
               (measure m (s CROSS t) = lambda s * lambda t)) /\
         (!s. s IN measurable_sets m ==>
             (!x. (\y. indicator_fn s (x,y)) IN Borel_measurable borel) /\
             (!y. (\x. indicator_fn s (x,y)) IN Borel_measurable borel) /\
             (\y. pos_fn_integral lborel (\x. indicator_fn s (x,y))) IN Borel_measurable borel /\
             (\x. pos_fn_integral lborel (\y. indicator_fn s (x,y))) IN Borel_measurable borel /\
             (measure m s = pos_fn_integral lborel
                              (\y. pos_fn_integral lborel (\x. indicator_fn s (x,y)))) /\
             (measure m s = pos_fn_integral lborel
                              (\x. pos_fn_integral lborel (\y. indicator_fn s (x,y)))))’,
   (* proof *)
      MP_TAC (Q.ISPECL [‘univ(:real)’, ‘univ(:real)’, ‘subsets borel’, ‘subsets borel’,
                        ‘lambda’, ‘lambda’, ‘\s. lambda (IMAGE FST s) * lambda (IMAGE SND s)’]
                       EXISTENCE_OF_PROD_MEASURE) \\
      simp [sigma_finite_measure_space_def] \\
      Know ‘(univ(:real),subsets borel,lambda) = lborel’
      >- (REWRITE_TAC [GSYM space_lborel, GSYM sets_lborel, MEASURE_SPACE_REDUCE]) >> Rewr' \\
      REWRITE_TAC [measure_space_lborel, sigma_finite_lborel] \\
      Know ‘!s t. s IN subsets borel /\ t IN subsets borel ==>
                  lambda (IMAGE FST (s CROSS t)) * lambda (IMAGE SND (s CROSS t)) =
                  lambda s * lambda t’
      >- (rpt STRIP_TAC \\
          Cases_on ‘s = {}’ >- rw [lambda_empty] \\
          Cases_on ‘t = {}’ >- rw [lambda_empty] \\
          Know ‘IMAGE FST (s CROSS t) = s’
          >- (rw [Once EXTENSION] >> EQ_TAC >> RW_TAC std_ss [] >- art [] \\
              fs [GSYM MEMBER_NOT_EMPTY] >> rename1 ‘y IN t’ \\
              Q.EXISTS_TAC ‘(x,y)’ >> rw []) >> Rewr' \\
          Know ‘IMAGE SND (s CROSS t) = t’
          >- (rw [Once EXTENSION] >> EQ_TAC >> RW_TAC std_ss [] >- art [] \\
              fs [GSYM MEMBER_NOT_EMPTY] >> rename1 ‘y IN s’ \\
              Q.EXISTS_TAC ‘(y,x)’ >> rw []) >> Rewr) \\
      RW_TAC std_ss [] \\
      Q.EXISTS_TAC ‘(UNIV CROSS UNIV,
                     subsets ((UNIV,subsets borel) CROSS (UNIV,subsets borel)),m)’ \\
      Know ‘(univ(:real),subsets borel) = borel’ >- (REWRITE_TAC [GSYM space_borel, SPACE]) \\
      DISCH_THEN (fs o wrap) \\
      reverse CONJ_TAC >- METIS_TAC [] \\
      rpt STRIP_TAC \\
      IMP_RES_TAC MEASURE_SPACE_POSITIVE >> fs [positive_def] \\
      Cases_on ‘s = {}’ >- rw [lambda_empty] \\
      Cases_on ‘t = {}’ >- rw [lambda_empty] \\
      Q.PAT_X_ASSUM ‘!s. _ ==> (m s = lambda (IMAGE FST s) * lambda (IMAGE SND s))’
        (MP_TAC o (Q.SPEC ‘s CROSS t’)) >> RW_TAC std_ss [] \\
      POP_ASSUM MATCH_MP_TAC \\
      qexistsl_tac [‘s’, ‘t’] >> art []);
in
  val lborel_2d_def = new_specification ("lborel_2d_def", ["lborel_2d"], thm);
end;

(* NOTE: symbols are now aligned with real_measureTheory *)
Definition prod_measure_def :
    prod_measure m1 m2 =
      \s. pos_fn_integral m2 (\y. pos_fn_integral m1 (\x. indicator_fn s (x,y)))
End

Definition prod_measure_space_def : (* was: prod_measure_def or pair_measure_def *)
    prod_measure_space m1 m2 =
      (m_space m1 CROSS m_space m2,
       subsets (prod_sigma (m_space m1,measurable_sets m1)
                           (m_space m2,measurable_sets m2)),
       prod_measure m1 m2)
End

Overload CROSS = “prod_measure_space”

(* |- !m1 m2.
        m1 CROSS m2 =
        (m_space m1 CROSS m_space m2,
         subsets
           ((m_space m1,measurable_sets m1) CROSS
            (m_space m2,measurable_sets m2)),
         (\s.
              pos_fn_integral m2
                (\y. pos_fn_integral m1 (\x. indicator_fn s (x,y)))))
 *)
Theorem prod_measure_space_alt =
    REWRITE_RULE [prod_measure_def] prod_measure_space_def

Theorem measure_space_prod_measure : (* was: measure_space_pair_measure *)
    !m1 m2. sigma_finite_measure_space m1 /\
            sigma_finite_measure_space m2 ==> measure_space (m1 CROSS m2)
Proof
    rpt STRIP_TAC
 >> Cases_on ‘m1’ >> Cases_on ‘r’
 >> rename1 ‘sigma_finite_measure_space (X,A,u)’
 >> Cases_on ‘m2’ >> Cases_on ‘r’
 >> rename1 ‘sigma_finite_measure_space (Y,B,v)’
 (* applying EXISTENCE_OF_PROD_MEASURE *)
 >> MP_TAC (Q.SPECL [‘X’, ‘Y’, ‘A’, ‘B’, ‘u’, ‘v’] EXISTENCE_OF_PROD_MEASURE)
 >> DISCH_THEN (MP_TAC o (Q.SPEC ‘\x. u (IMAGE FST x) * v (IMAGE SND x)’))
 >> Know ‘!s t. s IN A /\ t IN B ==>
                (\x. u (IMAGE FST x) * v (IMAGE SND x)) (s CROSS t) = u s * v t’
 >- (rpt STRIP_TAC \\
     fs [sigma_finite_measure_space_def] \\
     Cases_on ‘s = {}’ >- (IMP_RES_TAC MEASURE_SPACE_POSITIVE >> fs [positive_def]) \\
     Cases_on ‘t = {}’ >- (IMP_RES_TAC MEASURE_SPACE_POSITIVE >> fs [positive_def]) \\
     Know ‘IMAGE FST (s CROSS t) = s’
     >- (rw [Once EXTENSION] >> EQ_TAC >> RW_TAC std_ss [] >- art [] \\
         Q.PAT_X_ASSUM ‘t <> {}’ (STRIP_ASSUME_TAC o
                                  (REWRITE_RULE [GSYM MEMBER_NOT_EMPTY])) \\
         rename1 ‘y IN t’ >> Q.EXISTS_TAC ‘(x,y)’ >> rw []) >> Rewr' \\
     Know ‘IMAGE SND (s CROSS t) = t’
     >- (rw [Once EXTENSION] >> EQ_TAC >> RW_TAC std_ss [] >- art [] \\
         Q.PAT_X_ASSUM ‘t <> {}’ K_TAC \\
         Q.PAT_X_ASSUM ‘s <> {}’ (STRIP_ASSUME_TAC o
                                  (REWRITE_RULE [GSYM MEMBER_NOT_EMPTY])) \\
         rename1 ‘y IN s’ >> Q.EXISTS_TAC ‘(y,x)’ >> rw []) >> Rewr)
 >> RW_TAC std_ss []
 >> ‘m_space ((X,A,u) CROSS (Y,B,v)) = X CROSS Y’ by rw [prod_measure_space_alt]
 >> ‘measurable_sets ((X,A,u) CROSS (Y,B,v)) =
     subsets ((X,A) CROSS (Y,B))’ by rw [prod_measure_space_alt]
 >> Know ‘space ((X,A) CROSS (Y,B)) = X CROSS Y’
 >- (rw [prod_sigma_def] >> REWRITE_TAC [SPACE_SIGMA]) >> DISCH_TAC
 >> fs [sigma_finite_measure_space_def]
 >> MATCH_MP_TAC measure_space_eq
 >> Q.EXISTS_TAC ‘(X CROSS Y,subsets ((X,A) CROSS (Y,B)),m)’
 >> rw [prod_measure_space_alt]
QED

(* ‘lborel_2d = lborel CROSS lborel’ doesn't hold *)
Theorem lborel_2d_prod_measure :
    !s. s IN measurable_sets lborel_2d ==>
        measure lborel_2d s = measure (lborel CROSS lborel) s
Proof
    RW_TAC std_ss [prod_measure_space_alt]
 >> STRIP_ASSUME_TAC lborel_2d_def
 >> rw [space_lborel, sets_lborel]
 >> METIS_TAC []
QED

(******************************************************************************)
(*     Fubini-Tonelli Theorems                                                *)
(******************************************************************************)

(* Theorem 14.8 [1, p.142] (Tonelli's theorem)

   named after Leonida Tonelli, an Italian mathematician [5].

   cf. HVG's limited version under the name "fubini":

 |- !f M1 M2. measure_space M1 /\ measure_space M2 /\
       sigma_finite_measure M1 /\ sigma_finite_measure M2 /\
       (!x. 0 <= f x) /\
       f IN measurable
        (m_space (pair_measure M1 M2), measurable_sets (pair_measure M1 M2)) Borel ==>
       (pos_fn_integral M1 (\x. pos_fn_integral M2 (\y. f (x,y))) =
        pos_fn_integral M2 (\y. pos_fn_integral M1 (\x. f (x,y)))): thm
 *)
Theorem TONELLI : (* was: fubini (HVG concordia) *)
    !(X :'a set) (Y :'b set) A B u v f.
        sigma_finite_measure_space (X,A,u) /\
        sigma_finite_measure_space (Y,B,v) /\
        f IN measurable ((X,A) CROSS (Y,B)) Borel /\
        (!s. s IN X CROSS Y ==> 0 <= f s)
       ==>
        (!y. y IN Y ==> (\x. f (x,y)) IN measurable (X,A) Borel) /\
        (!x. x IN X ==> (\y. f (x,y)) IN measurable (Y,B) Borel) /\
        (\x. pos_fn_integral (Y,B,v) (\y. f (x,y))) IN measurable (X,A) Borel /\
        (\y. pos_fn_integral (X,A,u) (\x. f (x,y))) IN measurable (Y,B) Borel /\
        (pos_fn_integral ((X,A,u) CROSS (Y,B,v)) f =
         pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. f (x,y)))) /\
        (pos_fn_integral ((X,A,u) CROSS (Y,B,v)) f =
         pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. f (x,y))))
Proof
    rpt GEN_TAC >> STRIP_TAC
 (* applying measure_space_prod_measure *)
 >> ‘measure_space ((X,A,u) CROSS (Y,B,v))’ (* only needed in goal 5 & 6 *)
      by METIS_TAC [measure_space_prod_measure]
 (* preliminaries *)
 >> Know ‘!i n. (0 :extreal) <= &i / 2 pow n’
 >- (rpt GEN_TAC \\
    ‘2 pow n <> PosInf /\ 2 pow n <> NegInf’
       by METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty] \\
    ‘?r. 0 < r /\ (2 pow n = Normal r)’
       by METIS_TAC [lt_02, pow_pos_lt, extreal_cases, extreal_lt_eq,
                     extreal_of_num_def] >> POP_ORW \\
     MATCH_MP_TAC le_div >> rw [extreal_of_num_def, extreal_le_eq])
 >> DISCH_TAC
 >> Know ‘!i n. &i / 2 pow n <> PosInf /\ &i / 2 pow n <> NegInf’
 >- (rpt GEN_TAC \\
    ‘&i = Normal (&i)’ by METIS_TAC [extreal_of_num_def] >> POP_ORW \\
     MATCH_MP_TAC div_not_infty \\
     ONCE_REWRITE_TAC [EQ_SYM_EQ] >> MATCH_MP_TAC lt_imp_ne \\
     MATCH_MP_TAC pow_pos_lt >> REWRITE_TAC [lt_02])
 >> DISCH_TAC
 (* applying EXISTENCE_OF_PROD_MEASURE *)
 >> MP_TAC (Q.SPECL [‘X’, ‘Y’, ‘A’, ‘B’, ‘u’, ‘v’] EXISTENCE_OF_PROD_MEASURE)
 >> DISCH_THEN (MP_TAC o (Q.SPEC ‘\x. u (IMAGE FST x) * v (IMAGE SND x)’))
 >> Know ‘!s t. s IN A /\ t IN B ==>
                (\x. u (IMAGE FST x) * v (IMAGE SND x)) (s CROSS t) = u s * v t’
 >- (rpt STRIP_TAC \\
     fs [sigma_finite_measure_space_def] \\
     Cases_on ‘s = {}’ >- (IMP_RES_TAC MEASURE_SPACE_POSITIVE >> fs [positive_def]) \\
     Cases_on ‘t = {}’ >- (IMP_RES_TAC MEASURE_SPACE_POSITIVE >> fs [positive_def]) \\
     Know ‘IMAGE FST (s CROSS t) = s’
     >- (rw [Once EXTENSION] >> EQ_TAC >> RW_TAC std_ss [] >- art [] \\
         Q.PAT_X_ASSUM ‘t <> {}’ (STRIP_ASSUME_TAC o
                                  (REWRITE_RULE [GSYM MEMBER_NOT_EMPTY])) \\
         rename1 ‘y IN t’ >> Q.EXISTS_TAC ‘(x,y)’ >> rw []) >> Rewr' \\
     Know ‘IMAGE SND (s CROSS t) = t’
     >- (rw [Once EXTENSION] >> EQ_TAC >> RW_TAC std_ss [] >- art [] \\
         Q.PAT_X_ASSUM ‘t <> {}’ K_TAC \\
         Q.PAT_X_ASSUM ‘s <> {}’ (STRIP_ASSUME_TAC o
                                  (REWRITE_RULE [GSYM MEMBER_NOT_EMPTY])) \\
         rename1 ‘y IN s’ >> Q.EXISTS_TAC ‘(y,x)’ >> rw []) >> Rewr)
 >> DISCH_TAC
 >> ASM_SIMP_TAC std_ss []
 >> STRIP_TAC
 (* applying lemma_fn_seq_sup *)
 >> MP_TAC (Q.SPECL [‘(X,A,u) CROSS (Y,B,v)’, ‘f’]
                    (INST_TYPE [alpha |-> “:'a # 'b”] lemma_fn_seq_sup))
 >> ‘m_space ((X,A,u) CROSS (Y,B,v)) = X CROSS Y’ by rw [prod_measure_space_alt]
 >> ASM_REWRITE_TAC [] >> DISCH_TAC
 >> ‘measurable_sets ((X,A,u) CROSS (Y,B,v)) =
       subsets ((X,A) CROSS (Y,B))’ by rw [prod_measure_space_alt]
 >> Know ‘space ((X,A) CROSS (Y,B)) = X CROSS Y’
 >- (rw [prod_sigma_def] >> REWRITE_TAC [SPACE_SIGMA]) >> DISCH_TAC
 >> fs [sigma_finite_measure_space_def]
 >> ‘sigma_algebra (X,A) /\ sigma_algebra (Y,B)’
      by METIS_TAC [measure_space_def, space_def, subsets_def, m_space_def,
                    measurable_sets_def]
 >> Know ‘sigma_algebra ((X,A) CROSS (Y,B))’
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_PROD_SIGMA \\
     fs [sigma_algebra_def, algebra_def]) >> DISCH_TAC
 (* common measurable sets inside fn_seq *)
 >> Q.ABBREV_TAC ‘s = \n k. {x | x IN X CROSS Y /\ &k / 2 pow n <= f x /\
                                 f x < (&k + 1) / 2 pow n}’
 >> Know ‘!n i. s n i IN subsets ((X,A) CROSS (Y,B))’
 >- (rpt GEN_TAC \\
     Know ‘s n i = ({x | &i / 2 pow n <= f x} INTER (X CROSS Y)) INTER
                   ({x | f x < (&i + 1) / 2 pow n} INTER (X CROSS Y))’
     >- (rw [Abbr ‘s’, Once EXTENSION, IN_INTER] \\
         EQ_TAC >> RW_TAC std_ss []) >> Rewr' \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER \\
     MP_TAC (Q.SPECL [‘f’, ‘(X,A) CROSS (Y,B)’]
                     (INST_TYPE [alpha |-> “:'a # 'b”] IN_MEASURABLE_BOREL_ALL)) >> rw [])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘t = \n. {x | x IN X CROSS Y /\ 2 pow n <= f x}’
 >> Know ‘!n. t n IN subsets ((X,A) CROSS (Y,B))’
 >- (RW_TAC std_ss [Abbr ‘t’] \\
    ‘2 pow n <> PosInf /\ 2 pow n <> NegInf’
        by METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty] \\
    ‘?r. 2 pow n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘{x | x IN X CROSS Y /\ Normal r <= f x} = {x | Normal r <= f x} INTER (X CROSS Y)’
        by SET_TAC [] >> POP_ORW \\
     MP_TAC (Q.SPECL [‘f’, ‘(X,A) CROSS (Y,B)’]
                     (INST_TYPE [alpha |-> “:'a # 'b”] IN_MEASURABLE_BOREL_ALL)) >> rw [])
 >> DISCH_TAC
 (* important properties of fn_seq *)
 >> Know ‘!n y. y IN Y /\ (!s. s IN subsets ((X,A) CROSS (Y,B)) ==>
                              (\x. indicator_fn s (x,y)) IN measurable (X,A) Borel) ==>
               (\x. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y)) IN Borel_measurable (X,A)’
 >- (rpt STRIP_TAC \\
     ASM_SIMP_TAC std_ss [fn_seq_def] \\
    ‘!k. {x | x IN X CROSS Y /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n} = s n k’
        by METIS_TAC [] >> POP_ORW \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD \\
     qexistsl_tac [‘\x. SIGMA (\k. &k / 2 pow n * indicator_fn (s n k) (x,y))
                              (count (4 ** n))’,
                   ‘\x. 2 pow n * indicator_fn (t n) (x,y)’] \\
     ASM_SIMP_TAC std_ss [space_def] \\
     CONJ_TAC (* Borel_measurable #1 *)
     >- (MATCH_MP_TAC (INST_TYPE [beta |-> “:num”] IN_MEASURABLE_BOREL_SUM) \\
         qexistsl_tac [‘\k x. &k / 2 pow n * indicator_fn (s n k) (x,y)’,
                       ‘count (4 ** n)’] \\
         ASM_SIMP_TAC std_ss [FINITE_COUNT, space_def] \\
         reverse CONJ_TAC
         >- (rpt GEN_TAC >> STRIP_TAC \\
             MATCH_MP_TAC pos_not_neginf \\
             MATCH_MP_TAC le_mul >> art [INDICATOR_FN_POS]) \\
         RW_TAC std_ss [IN_COUNT] \\
        ‘?z. &i / 2 pow n = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> rw [] \\
         qexistsl_tac [‘\x. indicator_fn (s n i) (x,y)’, ‘z’] >> rw []) \\
     reverse CONJ_TAC
     >- (GEN_TAC >> DISCH_TAC >> DISJ1_TAC \\
         CONJ_TAC >> MATCH_MP_TAC pos_not_neginf >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           irule EXTREAL_SUM_IMAGE_POS \\
           reverse CONJ_TAC >- REWRITE_TAC [FINITE_COUNT] \\
           Q.X_GEN_TAC ‘i’ >> rw [] \\
           MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS],
           (* goal 2 (of 2) *)
           MATCH_MP_TAC le_mul >> REWRITE_TAC [INDICATOR_FN_POS] \\
           MATCH_MP_TAC pow_pos_le >> REWRITE_TAC [le_02] ]) \\
    ‘2 pow n <> PosInf /\ 2 pow n <> NegInf’
        by METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty] \\
    ‘?r. 2 pow n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> rw [] \\
     qexistsl_tac [‘\x. indicator_fn (t n) (x,y)’, ‘r’] >> rw [])
 >> DISCH_TAC
 >> Know ‘!n x. x IN X /\
               (!s. s IN subsets ((X,A) CROSS (Y,B)) ==>
                     (\y. indicator_fn s (x,y)) IN measurable (Y,B) Borel) ==>
               (\y. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y)) IN Borel_measurable (Y,B)’
 >- (rpt STRIP_TAC \\
     ASM_SIMP_TAC std_ss [fn_seq_def] \\
    ‘!k. {x | x IN X CROSS Y /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n} = s n k’
        by METIS_TAC [] >> POP_ORW \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD \\
     qexistsl_tac [‘\y. SIGMA (\k. &k / 2 pow n * indicator_fn (s n k) (x,y))
                              (count (4 ** n))’,
                   ‘\y. 2 pow n * indicator_fn (t n) (x,y)’] \\
     ASM_SIMP_TAC std_ss [space_def] \\
     CONJ_TAC (* Borel_measurable #1 *)
     >- (MATCH_MP_TAC (INST_TYPE [beta |-> “:num”] IN_MEASURABLE_BOREL_SUM) \\
         qexistsl_tac [‘\k y. &k / 2 pow n * indicator_fn (s n k) (x,y)’,
                       ‘count (4 ** n)’] \\
         ASM_SIMP_TAC std_ss [FINITE_COUNT, space_def] \\
         reverse CONJ_TAC
         >- (rpt GEN_TAC >> STRIP_TAC \\
             MATCH_MP_TAC pos_not_neginf \\
             MATCH_MP_TAC le_mul >> art [INDICATOR_FN_POS]) \\
         RW_TAC std_ss [IN_COUNT] \\
        ‘?z. &i / 2 pow n = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> rw [] \\
         qexistsl_tac [‘\y. indicator_fn (s n i) (x,y)’, ‘z’] >> rw []) \\
     reverse CONJ_TAC
     >- (GEN_TAC >> DISCH_TAC >> DISJ1_TAC \\
         CONJ_TAC >> MATCH_MP_TAC pos_not_neginf >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           irule EXTREAL_SUM_IMAGE_POS \\
           reverse CONJ_TAC >- REWRITE_TAC [FINITE_COUNT] \\
           Q.X_GEN_TAC ‘i’ >> rw [] \\
           MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS],
           (* goal 2 (of 2) *)
           MATCH_MP_TAC le_mul >> REWRITE_TAC [INDICATOR_FN_POS] \\
           MATCH_MP_TAC pow_pos_le >> REWRITE_TAC [le_02] ]) \\
    ‘2 pow n <> PosInf /\ 2 pow n <> NegInf’
        by METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty] \\
    ‘?r. 2 pow n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> rw [] \\
     qexistsl_tac [‘\y. indicator_fn (t n) (x,y)’, ‘r’] >> rw [])
 >> DISCH_TAC
 (* shared property by goal 3 and 5/6 *)
 >> Know ‘!n. (\x. pos_fn_integral (Y,B,v) (\y. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y)))
              IN Borel_measurable (X,A)’
 >- (RW_TAC std_ss [fn_seq_def] \\
    ‘!k. {x | x IN X CROSS Y /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n} = s n k’
        by METIS_TAC [] >> POP_ORW \\
     MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                (Q.SPEC ‘(X,A,u)’ IN_MEASURABLE_BOREL_EQ)) >> BETA_TAC \\
     Q.EXISTS_TAC ‘\x. pos_fn_integral (Y,B,v)
                         (\y. SIGMA (\k. &k / 2 pow n * indicator_fn (s n k) (x,y))
                                    (count (4 ** n))) +
                       pos_fn_integral (Y,B,v)
                         (\y. 2 pow n *
                              indicator_fn {x | x IN X CROSS Y /\ 2 pow n <= f x} (x,y))’ \\
     ASM_SIMP_TAC std_ss [] \\
     Know ‘!x. x IN X ==> (\y. SIGMA (\k. &k / 2 pow n * indicator_fn (s n k) (x,y))
                                     (count (4 ** n))) IN measurable (Y,B) Borel’
     >- (rpt STRIP_TAC \\
         MATCH_MP_TAC ((INST_TYPE [alpha |-> beta] o
                        INST_TYPE [beta |-> “:num”]) IN_MEASURABLE_BOREL_SUM) >> simp [] \\
         qexistsl_tac [‘\k y. &k / 2 pow n * indicator_fn (s n k) (x,y)’,
                       ‘count (4 ** n)’] >> simp [] \\
         CONJ_TAC
         >- (rpt STRIP_TAC \\
            ‘?z. &i / 2 pow n = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
             MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> rw [] \\
             qexistsl_tac [‘\y. indicator_fn (s n i) (x,y)’, ‘z’] >> rw []) \\
         qx_genl_tac [‘i’, ‘y’] >> STRIP_TAC \\
         MATCH_MP_TAC pos_not_neginf \\
         MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) >> DISCH_TAC \\
     Know ‘!x. x IN X ==> (\y. 2 pow n * indicator_fn (t n) (x,y)) IN measurable (Y,B) Borel’
     >- (rpt STRIP_TAC \\
        ‘2 pow n <> PosInf /\ 2 pow n <> NegInf’
            by METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty] \\
        ‘?r. 2 pow n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL \\
         ASM_SIMP_TAC std_ss [space_def] \\
         qexistsl_tac [‘\y. indicator_fn (t n) (x,y)’, ‘r’] >> rw []) >> DISCH_TAC \\
     RW_TAC std_ss []
     >- (HO_MATCH_MP_TAC pos_fn_integral_add \\
         ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def] \\
         CONJ_TAC >- (rpt STRIP_TAC \\
                      MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> rw [IN_COUNT] \\
                      MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
         rpt STRIP_TAC \\
         MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, pow_pos_le]) \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD \\
     qexistsl_tac [‘\x. pos_fn_integral (Y,B,v)
                          (\y. SIGMA (\k. &k / 2 pow n *
                                          indicator_fn (s n k) (x,y)) (count (4 ** n)))’,
                   ‘\x. pos_fn_integral (Y,B,v)
                          (\y. 2 pow n * indicator_fn (t n) (x,y))’] \\
     ASM_SIMP_TAC std_ss [space_def] \\
     REWRITE_TAC [CONJ_ASSOC] >> reverse CONJ_TAC
     >- (GEN_TAC >> DISCH_TAC >> DISJ1_TAC \\
         CONJ_TAC >> MATCH_MP_TAC pos_not_neginf >|
         [ (* goal 1 (of 2) *)
           MATCH_MP_TAC pos_fn_integral_pos >> simp [] \\
           Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
           MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> simp [] \\
           Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
           MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS],
           (* goal 2 (of 2) *)
           MATCH_MP_TAC pos_fn_integral_pos >> simp [] \\
           Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
           MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, pow_pos_le] ]) \\
     CONJ_TAC
     >- (MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                    (Q.SPEC ‘(X,A,u)’ IN_MEASURABLE_BOREL_EQ)) >> BETA_TAC \\
         Q.EXISTS_TAC ‘\x. SIGMA (\k. pos_fn_integral (Y,B,v)
                                        (\y. &k / 2 pow n * indicator_fn (s n k) (x,y)))
                                 (count (4 ** n))’ \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC ((INST_TYPE [alpha |-> beta] o
                            INST_TYPE [beta |-> “:num”]) IN_MEASURABLE_BOREL_SUM) >> simp [] \\
             qexistsl_tac [‘\k x. pos_fn_integral (Y,B,v)
                                    (\y. &k / 2 pow n * indicator_fn (s n k) (x,y))’,
                           ‘count (4 ** n)’] >> simp [] \\
             CONJ_TAC
             >- (rpt STRIP_TAC \\
                ‘?z. 0 <= z /\ (&i / 2 pow n = Normal z)’
                     by METIS_TAC [extreal_cases, extreal_le_eq, extreal_of_num_def] >> POP_ORW \\
                 MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                            (Q.SPEC ‘(X,A,u)’ IN_MEASURABLE_BOREL_EQ)) >> BETA_TAC \\
                 Q.EXISTS_TAC ‘\x. Normal z * pos_fn_integral (Y,B,v)
                                                (\y. indicator_fn (s n i) (x,y))’ >> BETA_TAC \\
                 CONJ_TAC >- (rpt STRIP_TAC \\
                              HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) \\
                 MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> rw [] \\
                 qexistsl_tac [‘\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (s n i) (x,y))’,
                               ‘z’] >> rw []) \\
             qx_genl_tac [‘i’, ‘x’] >> STRIP_TAC \\
             MATCH_MP_TAC pos_not_neginf \\
             MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
             MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
         RW_TAC std_ss [] \\
         Q.ABBREV_TAC ‘g = \k y. &k / 2 pow n * indicator_fn (s n k) (x,y)’ \\
         MP_TAC (Q.SPECL [‘(Y,B,v)’, ‘g’, ‘count (4 ** n)’]
                         ((INST_TYPE [alpha |-> beta] o
                           INST_TYPE [beta |-> “:num”]) pos_fn_integral_sum)) \\
         simp [Abbr ‘g’] \\
         Know ‘!i. i < 4 ** n ==>
                   !y. y IN Y ==> 0 <= &i / 2 pow n * indicator_fn (s n i) (x,y)’
         >- (rpt STRIP_TAC >> MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
         Suff ‘!i. i < 4 ** n ==>
                   (\y. &i / 2 pow n * indicator_fn (s n i) (x,y)) IN Borel_measurable (Y,B)’
         >- RW_TAC std_ss [] \\
         rpt STRIP_TAC \\
        ‘?z. &i / 2 pow n = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         MATCH_MP_TAC (INST_TYPE [alpha |-> beta] IN_MEASURABLE_BOREL_CMUL) >> simp [] \\
         qexistsl_tac [‘\y. indicator_fn (s n i) (x,y)’, ‘z’] >> rw []) \\
    ‘2 pow n <> PosInf /\ 2 pow n <> NegInf’
        by METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty] \\
    ‘?r. 0 <= r /\ (2 pow n = Normal r)’
        by METIS_TAC [extreal_cases, pow_pos_le, le_02, extreal_le_eq, extreal_of_num_def] \\
     POP_ORW \\
     MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                (Q.SPEC ‘(X,A,u)’ IN_MEASURABLE_BOREL_EQ)) >> BETA_TAC \\
     Q.EXISTS_TAC ‘\x. Normal r * (pos_fn_integral (Y,B,v) (\y. indicator_fn (t n) (x,y)))’ \\
     BETA_TAC \\
     CONJ_TAC >- (rpt STRIP_TAC \\
                  HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> simp [] \\
     qexistsl_tac [‘\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (t n) (x,y))’, ‘r’] >> rw [])
 >> DISCH_TAC
 (* shared property by goal 4 and 5/6 *)
 >> Know ‘!n. (\y. pos_fn_integral (X,A,u) (\x. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y)))
              IN Borel_measurable (Y,B)’
 >- (RW_TAC std_ss [fn_seq_def] \\
    ‘!k. {x | x IN X CROSS Y /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n} = s n k’
        by METIS_TAC [] >> POP_ORW \\
     MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                (Q.SPEC ‘(Y,B,v)’ IN_MEASURABLE_BOREL_EQ)) >> BETA_TAC \\
     Q.EXISTS_TAC ‘\y. pos_fn_integral (X,A,u)
                         (\x. SIGMA (\k. &k / 2 pow n * indicator_fn (s n k) (x,y))
                                    (count (4 ** n))) +
                       pos_fn_integral (X,A,u)
                         (\x. 2 pow n * indicator_fn (t n) (x,y))’ \\
     ASM_SIMP_TAC std_ss [] \\
     Know ‘!y. y IN Y ==> (\x. SIGMA (\k. &k / 2 pow n * indicator_fn (s n k) (x,y))
                                     (count (4 ** n))) IN measurable (X,A) Borel’
     >- (rpt STRIP_TAC \\
         MATCH_MP_TAC (INST_TYPE [beta |-> “:num”] IN_MEASURABLE_BOREL_SUM) >> simp [] \\
         qexistsl_tac [‘\k x. &k / 2 pow n * indicator_fn (s n k) (x,y)’,
                       ‘count (4 ** n)’] >> simp [] \\
         CONJ_TAC
         >- (rpt STRIP_TAC \\
            ‘?z. &i / 2 pow n = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
             MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> rw [] \\
             qexistsl_tac [‘\x. indicator_fn (s n i) (x,y)’, ‘z’] >> rw []) \\
         qx_genl_tac [‘i’, ‘x’] >> STRIP_TAC \\
         MATCH_MP_TAC pos_not_neginf \\
         MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
     DISCH_TAC \\
     Know ‘!y. y IN Y ==> (\x. 2 pow n * indicator_fn (t n) (x,y)) IN measurable (X,A) Borel’
     >- (rpt STRIP_TAC \\
        ‘2 pow n <> PosInf /\ 2 pow n <> NegInf’
            by METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty] \\
        ‘?r. 2 pow n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> rw [] \\
         qexistsl_tac [‘\x. indicator_fn (t n) (x,y)’, ‘r’] >> rw []) >> DISCH_TAC \\
     RW_TAC std_ss []
     >- (HO_MATCH_MP_TAC pos_fn_integral_add \\
         ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def] \\
         CONJ_TAC >- (rpt STRIP_TAC \\
                      MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> rw [IN_COUNT] \\
                      MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
         rpt STRIP_TAC \\
         MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, pow_pos_le]) \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD \\
     qexistsl_tac [‘\y. pos_fn_integral (X,A,u)
                          (\x. SIGMA (\k. &k / 2 pow n *
                                          indicator_fn (s n k) (x,y)) (count (4 ** n)))’,
                   ‘\y. pos_fn_integral (X,A,u)
                          (\x. 2 pow n * indicator_fn (t n) (x,y))’] \\
     ASM_SIMP_TAC std_ss [space_def] \\
     REWRITE_TAC [CONJ_ASSOC] >> reverse CONJ_TAC
     >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC >> DISJ1_TAC \\
         CONJ_TAC >> MATCH_MP_TAC pos_not_neginf >|
         [ (* goal 4.1 (of 2) *)
           MATCH_MP_TAC pos_fn_integral_pos >> simp [] \\
           Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
           MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> simp [] \\
           Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
           MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS],
           (* goal 4.2 (of 2) *)
           MATCH_MP_TAC pos_fn_integral_pos >> simp [] \\
           Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
           MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, pow_pos_le] ]) \\
     CONJ_TAC
     >- (MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                    (Q.SPEC ‘(Y,B,v)’ IN_MEASURABLE_BOREL_EQ)) >> BETA_TAC \\
         Q.EXISTS_TAC ‘\y. SIGMA (\k. pos_fn_integral (X,A,u)
                                        (\x. &k / 2 pow n * indicator_fn (s n k) (x,y)))
                                 (count (4 ** n))’ \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC (INST_TYPE [beta |-> “:num”] IN_MEASURABLE_BOREL_SUM) >> simp [] \\
             qexistsl_tac [‘\k y. pos_fn_integral (X,A,u)
                                    (\x. &k / 2 pow n * indicator_fn (s n k) (x,y))’,
                           ‘count (4 ** n)’] >> simp [] \\
             CONJ_TAC
             >- (rpt STRIP_TAC \\
                ‘?z. 0 <= z /\ (&i / 2 pow n = Normal z)’
                    by METIS_TAC [extreal_cases, extreal_le_eq, extreal_of_num_def] >> POP_ORW \\
                 MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                            (Q.SPEC ‘(Y,B,v)’ IN_MEASURABLE_BOREL_EQ)) >> BETA_TAC \\
                 Q.EXISTS_TAC ‘\y. Normal z * pos_fn_integral (X,A,u)
                                                (\x. indicator_fn (s n i) (x,y))’ >> BETA_TAC \\
                 CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                              HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) \\
                 MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> rw [] \\
                 qexistsl_tac [‘\y. pos_fn_integral (X,A,u) (\x. indicator_fn (s n i) (x,y))’,
                               ‘z’] >> rw []) \\
             qx_genl_tac [‘i’, ‘y’] >> STRIP_TAC \\
             MATCH_MP_TAC pos_not_neginf \\
             MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
             MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
         Q.X_GEN_TAC ‘y’ >> STRIP_TAC \\
         Q.ABBREV_TAC ‘g = \k x. &k / 2 pow n * indicator_fn (s n k) (x,y)’ \\
         MP_TAC (Q.SPECL [‘(X,A,u)’, ‘g’, ‘count (4 ** n)’]
                         (INST_TYPE [beta |-> “:num”] pos_fn_integral_sum)) \\
         simp [Abbr ‘g’] \\
         Know ‘!i. i < 4 ** n ==>
                   !x. x IN X ==> 0 <= &i / 2 pow n * indicator_fn (s n i) (x,y)’
         >- (rpt STRIP_TAC >> MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
         Suff ‘!i. i < 4 ** n ==>
                   (\x. &i / 2 pow n * indicator_fn (s n i) (x,y)) IN Borel_measurable (X,A)’
         >- RW_TAC std_ss [] \\
         rpt STRIP_TAC \\
        ‘?z. &i / 2 pow n = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> simp [] \\
         qexistsl_tac [‘\x. indicator_fn (s n i) (x,y)’, ‘z’] >> rw []) \\
    ‘2 pow n <> PosInf /\ 2 pow n <> NegInf’
        by METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty] \\
    ‘?r. 0 <= r /\ (2 pow n = Normal r)’
        by METIS_TAC [extreal_cases, pow_pos_le, le_02, extreal_le_eq, extreal_of_num_def] \\
     POP_ORW \\
     MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                (Q.SPEC ‘(Y,B,v)’ IN_MEASURABLE_BOREL_EQ)) >> BETA_TAC \\
     Q.EXISTS_TAC ‘\y. Normal r * (pos_fn_integral (X,A,u) (\x. indicator_fn (t n) (x,y)))’ \\
     BETA_TAC \\
     CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                  HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> simp [] \\
     qexistsl_tac [‘\y. pos_fn_integral (X,A,u) (\x. indicator_fn (t n) (x,y))’, ‘r’] >> rw [])
 >> DISCH_TAC
 (* stage work *)
 >> RW_TAC std_ss [] (* 6 subgoals *)
 >| [ (* goal 1 (of 6) *)
      MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                 (Q.SPEC ‘(X,A,u)’ IN_MEASURABLE_BOREL_EQ)) \\
      Q.EXISTS_TAC ‘\x. sup (IMAGE (\n. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y))
                                   UNIV)’ >> rw [] \\
      MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP \\
      Q.EXISTS_TAC ‘\n x. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y)’ >> rw [] \\
      irule (SIMP_RULE std_ss [ext_mono_increasing_def]
                              lemma_fn_seq_mono_increasing) >> rw [],
      (* goal 2 (of 6), symmetric with goal 1 *)
      MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                 (Q.SPEC ‘(Y,B,v)’
                                         (INST_TYPE [alpha |-> beta] IN_MEASURABLE_BOREL_EQ))) \\
      Q.EXISTS_TAC ‘\y. sup (IMAGE (\n. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y))
                                   UNIV)’ >> rw [] \\
      MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP \\
      Q.EXISTS_TAC ‘\n y. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y)’ >> rw [] \\
      irule (SIMP_RULE std_ss [ext_mono_increasing_def]
                              lemma_fn_seq_mono_increasing) >> rw [],
      (* goal 3 (of 6) *)
      MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                 (Q.SPEC ‘(X,A,u)’ IN_MEASURABLE_BOREL_EQ)) >> BETA_TAC \\
      Q.EXISTS_TAC ‘\x. pos_fn_integral (Y,B,v)
                          (\y. sup (IMAGE (\n. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y))
                                          UNIV))’ >> rw []
      >- (MATCH_MP_TAC pos_fn_integral_cong >> rw []) \\
      MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                 (Q.SPEC ‘(X,A,u)’ IN_MEASURABLE_BOREL_EQ)) >> BETA_TAC \\
      Q.EXISTS_TAC ‘\x. sup (IMAGE (\n. pos_fn_integral (Y,B,v)
                                          (\y. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y)))
                             UNIV)’ >> rw []
      >- (HO_MATCH_MP_TAC lebesgue_monotone_convergence \\
          simp [lemma_fn_seq_positive, lemma_fn_seq_mono_increasing]) \\
      MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP >> simp [] \\
      Q.EXISTS_TAC ‘\n x. pos_fn_integral (Y,B,v)
                            (\y. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y))’ \\
      RW_TAC std_ss [] \\
      MATCH_MP_TAC pos_fn_integral_mono >> simp [lemma_fn_seq_positive] \\
      Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
      irule (SIMP_RULE std_ss [ext_mono_increasing_def]
                              lemma_fn_seq_mono_increasing) >> rw [],
      (* goal 4 (of 6), symmetric with goal 3 *)
      MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                 (Q.SPEC ‘(Y,B,b)’ IN_MEASURABLE_BOREL_EQ)) >> BETA_TAC \\
      Q.EXISTS_TAC ‘\y. pos_fn_integral (X,A,u)
                          (\x. sup (IMAGE (\n. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y))
                                          UNIV))’ >> rw []
      >- (MATCH_MP_TAC pos_fn_integral_cong >> rw []) \\
      MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                 (Q.SPEC ‘(Y,B,v)’ IN_MEASURABLE_BOREL_EQ)) >> BETA_TAC \\
      Q.EXISTS_TAC ‘\y. sup (IMAGE (\n. pos_fn_integral (X,A,u)
                                          (\x. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y)))
                             UNIV)’ >> rw []
      >- (HO_MATCH_MP_TAC lebesgue_monotone_convergence \\
          simp [lemma_fn_seq_positive, lemma_fn_seq_mono_increasing]) \\
      MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP >> simp [] \\
      Q.EXISTS_TAC ‘\n y. pos_fn_integral (X,A,u)
                            (\x. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y))’ \\
      ASM_SIMP_TAC std_ss [] \\
      qx_genl_tac [‘n’, ‘y’] >> DISCH_TAC \\
      MATCH_MP_TAC pos_fn_integral_mono >> simp [lemma_fn_seq_positive] \\
      Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
      irule (SIMP_RULE std_ss [ext_mono_increasing_def]
                              lemma_fn_seq_mono_increasing) >> rw [],
      (* goal 5 (of 6) *)
      Know ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) f =
            pos_fn_integral ((X,A,u) CROSS (Y,B,v))
              (\x. sup (IMAGE (\n. fn_seq ((X,A,u) CROSS (Y,B,v)) f n x) UNIV))’
      >- (MATCH_MP_TAC pos_fn_integral_cong >> simp []) >> Rewr' \\
      Know ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v))
              (\x. sup (IMAGE (\n. fn_seq ((X,A,u) CROSS (Y,B,v)) f n x) UNIV)) =
            sup (IMAGE (\n. pos_fn_integral ((X,A,u) CROSS (Y,B,v))
                              (\z. fn_seq ((X,A,u) CROSS (Y,B,v)) f n z)) UNIV)’
      >- (HO_MATCH_MP_TAC lebesgue_monotone_convergence >> simp [] \\
          REWRITE_TAC [CONJ_ASSOC] (* easier goals first *) \\
          reverse CONJ_TAC (* mono_increasing *)
          >- (rpt STRIP_TAC >> MATCH_MP_TAC lemma_fn_seq_mono_increasing \\
              FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
          reverse CONJ_TAC (* positive *)
          >- (rpt STRIP_TAC >> MATCH_MP_TAC lemma_fn_seq_positive \\
              FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
          RW_TAC std_ss [fn_seq_def] \\
         ‘(X CROSS Y,subsets ((X,A) CROSS (Y,B))) = (X,A) CROSS (Y,B)’
            by METIS_TAC [SPACE] >> POP_ORW \\
          MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD \\
          ASM_SIMP_TAC std_ss [space_def] \\
          qexistsl_tac [‘\z. SIGMA (\k. &k / 2 pow n * indicator_fn (s n k) z) (count (4 ** n))’,
                        ‘\z. 2 pow n * indicator_fn (t n) z’] \\
          ASM_SIMP_TAC std_ss [CONJ_ASSOC] \\
          reverse CONJ_TAC (* nonnegative *)
          >- (Q.X_GEN_TAC ‘z’ >> DISCH_TAC >> DISJ1_TAC \\
              CONJ_TAC >> MATCH_MP_TAC pos_not_neginf >| (* 2 subgoals *)
              [ (* goal 5.1 (of 2) *)
                MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> rw [] \\
                MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS],
                (* goal 5.2 (of 2) *)
                MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, pow_pos_le] ]) \\
          CONJ_TAC (* Borel_measurable #1 *)
          >- (MATCH_MP_TAC (INST_TYPE [beta |-> “:num”] IN_MEASURABLE_BOREL_SUM) \\
              ASM_SIMP_TAC std_ss [space_def] \\
              qexistsl_tac [‘\k z. &k / 2 pow n * indicator_fn (s n k) z’,
                            ‘count (4 ** n)’] >> simp [] \\
              reverse CONJ_TAC
              >- (qx_genl_tac [‘i’, ‘z’] >> STRIP_TAC \\
                  MATCH_MP_TAC pos_not_neginf \\
                  MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
              rpt STRIP_TAC \\
             ‘?r. &i / 2 pow n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
              MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL_INDICATOR >> rw []) \\
         ‘2 pow n <> PosInf /\ 2 pow n <> NegInf’
             by METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty] \\
         ‘?r. 2 pow n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
          MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL_INDICATOR >> rw []) >> Rewr' \\
      Know ‘pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. f (x,y))) =
            pos_fn_integral (Y,B,v)
              (\y. pos_fn_integral (X,A,u)
                     (\x. sup (IMAGE (\n. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y)) UNIV)))’
      >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw []) \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw []) \\
          Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
          MATCH_MP_TAC pos_fn_integral_cong >> simp []) >> Rewr' \\
      Know ‘pos_fn_integral (Y,B,v)
              (\y. pos_fn_integral (X,A,u)
                     (\x. sup (IMAGE (\n. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y)) UNIV))) =
            pos_fn_integral (Y,B,v)
              (\y. sup (IMAGE (\n. pos_fn_integral (X,A,u)
                                     (\x. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y))) UNIV))’
      >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw []) \\
          CONJ_TAC
          >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
              rw [le_sup', IN_IMAGE, IN_UNIV] \\
              MATCH_MP_TAC le_trans \\
              Q.EXISTS_TAC ‘pos_fn_integral (X,A,u)
                              (\x. fn_seq ((X,A,u) CROSS (Y,B,v)) f 0 (x,y))’ \\
              CONJ_TAC >- (MATCH_MP_TAC pos_fn_integral_pos >> rw [lemma_fn_seq_positive]) \\
              POP_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘0’ >> REWRITE_TAC []) \\
          Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
          HO_MATCH_MP_TAC lebesgue_monotone_convergence \\
          simp [lemma_fn_seq_positive, lemma_fn_seq_mono_increasing]) >> Rewr' \\
      Know ‘pos_fn_integral (Y,B,v)
              (\y. sup (IMAGE (\n. pos_fn_integral (X,A,u)
                                     (\x. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y))) UNIV)) =
            sup (IMAGE (\n. pos_fn_integral (Y,B,v)
                              (\y. pos_fn_integral (X,A,u)
                                     (\x. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y)))) UNIV)’
      >- (HO_MATCH_MP_TAC lebesgue_monotone_convergence >> simp [] \\
          CONJ_TAC >- (rpt STRIP_TAC >> MATCH_MP_TAC pos_fn_integral_pos \\
                       simp [lemma_fn_seq_positive]) \\
          RW_TAC std_ss [ext_mono_increasing_def] \\
          MATCH_MP_TAC pos_fn_integral_mono >> simp [lemma_fn_seq_positive] \\
          rpt STRIP_TAC \\
          irule (SIMP_RULE std_ss [ext_mono_increasing_def]
                                  lemma_fn_seq_mono_increasing) >> art [] \\
          FIRST_X_ASSUM MATCH_MP_TAC >> rw []) >> Rewr' \\
      Suff ‘!n. pos_fn_integral (Y,B,v)
                  (\y. pos_fn_integral (X,A,u) (\x. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y))) =
                pos_fn_integral ((X,A,u) CROSS (Y,B,v))
                  (\z. fn_seq ((X,A,u) CROSS (Y,B,v)) f n z)’ >- rw [] \\
   (* ‘sup’ disappeared now *)
      GEN_TAC >> ASM_SIMP_TAC std_ss [fn_seq_def] \\
     ‘!k. {x | x IN X CROSS Y /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n} = s n k’
         by METIS_TAC [] >> POP_ORW \\
   (* RHS simplification *)
      Know ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v))
              (\z. SIGMA (\k. &k / 2 pow n * indicator_fn (s n k) z) (count (4 ** n)) +
                   2 pow n * indicator_fn (t n) z) =
            pos_fn_integral ((X,A,u) CROSS (Y,B,v))
              (\z. SIGMA (\k. &k / 2 pow n * indicator_fn (s n k) z) (count (4 ** n))) +
            pos_fn_integral ((X,A,u) CROSS (Y,B,v))
              (\z. 2 pow n * indicator_fn (t n) z)’
      >- (HO_MATCH_MP_TAC pos_fn_integral_add >> simp [] \\
          CONJ_TAC >- (rpt STRIP_TAC \\
                       MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> rw [] \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          CONJ_TAC >- (rpt STRIP_TAC \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, pow_pos_le]) \\
         ‘(X CROSS Y,subsets ((X,A) CROSS (Y,B))) = (X,A) CROSS (Y,B)’
            by METIS_TAC [SPACE] >> POP_ORW \\
          reverse CONJ_TAC
          >- (‘2 pow n <> PosInf /\ 2 pow n <> NegInf’
                 by METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty] \\
              ‘?r. 2 pow n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
              MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL_INDICATOR >> rw []) \\
          MATCH_MP_TAC ((INST_TYPE [alpha |-> “:'a # 'b”] o
                         INST_TYPE [beta |-> “:num”]) IN_MEASURABLE_BOREL_SUM) >> simp [] \\
          qexistsl_tac [‘\k z. &k / 2 pow n * indicator_fn (s n k) z’,
                        ‘count (4 ** n)’] >> simp [] \\
          reverse CONJ_TAC >- (qx_genl_tac [‘i’, ‘z’] >> STRIP_TAC \\
                               MATCH_MP_TAC pos_not_neginf \\
                               MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          rpt STRIP_TAC \\
         ‘?r. &i / 2 pow n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
          MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL_INDICATOR >> rw []) >> Rewr' \\
   (* LHS simplification *)
      Know ‘pos_fn_integral (Y,B,v)
              (\y. pos_fn_integral (X,A,u)
                     (\x. SIGMA (\k. &k / 2 pow n * indicator_fn (s n k) (x,y)) (count (4 ** n)) +
                          2 pow n * indicator_fn (t n) (x,y))) =
            pos_fn_integral (Y,B,v)
              (\y. pos_fn_integral (X,A,u)
                     (\x. SIGMA (\k. &k / 2 pow n * indicator_fn (s n k) (x,y)) (count (4 ** n))) +
                   pos_fn_integral (X,A,u)
                     (\x. 2 pow n * indicator_fn (t n) (x,y)))’
      >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
                       MATCH_MP_TAC le_add \\
                       reverse CONJ_TAC
                       >- (MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, pow_pos_le]) \\
                       MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> REWRITE_TAC [FINITE_COUNT] \\
                       Q.X_GEN_TAC ‘i’ >> rw [] \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                       MATCH_MP_TAC le_add \\
                       reverse CONJ_TAC
                       >- (MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
                           MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, pow_pos_le]) \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
                       MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> REWRITE_TAC [FINITE_COUNT] \\
                       Q.X_GEN_TAC ‘i’ >> rw [] \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, pow_pos_le]) \\
          Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
          HO_MATCH_MP_TAC pos_fn_integral_add >> simp [] \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
                       MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> REWRITE_TAC [FINITE_COUNT] \\
                       Q.X_GEN_TAC ‘i’ >> rw [] \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, pow_pos_le]) \\
          reverse CONJ_TAC
          >- (‘2 pow n <> PosInf /\ 2 pow n <> NegInf’
                 by METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty] \\
              ‘?r. 2 pow n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
              MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> simp [] \\
              qexistsl_tac [‘\x. indicator_fn (t n) (x,y)’, ‘r’] >> rw []) \\
          MATCH_MP_TAC (INST_TYPE [beta |-> “:num”] IN_MEASURABLE_BOREL_SUM) >> simp [] \\
          qexistsl_tac [‘\k x. &k / 2 pow n * indicator_fn (s n k) (x,y)’,
                        ‘count (4 ** n)’] >> simp [] \\
          reverse CONJ_TAC >- (rpt GEN_TAC >> STRIP_TAC \\
                               MATCH_MP_TAC pos_not_neginf \\
                               MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          rpt STRIP_TAC \\
         ‘?r. &i / 2 pow n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
          MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> simp [] \\
          qexistsl_tac [‘\x. indicator_fn (s n i) (x,y)’, ‘r’] >> rw []) >> Rewr' \\
   (* LHS simplification *)
      Know ‘pos_fn_integral (Y,B,v)
              (\y. pos_fn_integral (X,A,u)
                     (\x. SIGMA (\k. &k / 2 pow n * indicator_fn (s n k) (x,y))
                                (count (4 ** n))) +
                   pos_fn_integral (X,A,u) (\x. 2 pow n * indicator_fn (t n) (x,y))) =
            pos_fn_integral (Y,B,v)
              (\y. pos_fn_integral (X,A,u)
                     (\x. SIGMA (\k. &k / 2 pow n * indicator_fn (s n k) (x,y))
                                (count (4 ** n)))) +
            pos_fn_integral (Y,B,v)
              (\y. pos_fn_integral (X,A,u) (\x. 2 pow n * indicator_fn (t n) (x,y)))’
      >- (HO_MATCH_MP_TAC pos_fn_integral_add >> simp [] \\
          CONJ_TAC >- (rpt STRIP_TAC \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
                       MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> REWRITE_TAC [FINITE_COUNT] \\
                       Q.X_GEN_TAC ‘i’ >> rw [] \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          CONJ_TAC >- (rpt STRIP_TAC \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, pow_pos_le]) \\
          reverse CONJ_TAC
          >- (‘2 pow n <> PosInf /\ 2 pow n <> NegInf’
                 by METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty] \\
              ‘?r. 0 <= r /\ (2 pow n = Normal r)’
                 by METIS_TAC [extreal_cases, pow_pos_le, extreal_le_eq,
                               extreal_of_num_def, le_02] >> POP_ORW \\
              MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                         (Q.SPEC ‘(Y,B,v)’ IN_MEASURABLE_BOREL_EQ)) \\
              BETA_TAC \\
              Q.EXISTS_TAC ‘\y. Normal r *
                                pos_fn_integral (X,A,u) (\x. indicator_fn (t n) (x,y))’ \\
              reverse CONJ_TAC
              >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> simp [] \\
                  qexistsl_tac [‘\y. pos_fn_integral (X,A,u) (\x. indicator_fn (t n) (x,y))’,
                                ‘r’] >> rw []) \\
              Q.X_GEN_TAC ‘y’ >> RW_TAC std_ss [] \\
              HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) \\
          MATCH_MP_TAC ((INST_TYPE [alpha |-> beta] o
                         INST_TYPE [beta |-> “:num”]) IN_MEASURABLE_BOREL_SUM) \\
          ASM_SIMP_TAC std_ss [space_def] \\
          qexistsl_tac [‘\k y. pos_fn_integral (X,A,u)
                                 (\x. &k / 2 pow n * indicator_fn (s n k) (x,y))’,
                        ‘count (4 ** n)’] >> simp [] \\
          CONJ_TAC
          >- (rpt STRIP_TAC \\
             ‘?r. 0 <= r /\ (&i / 2 pow n = Normal r)’
                 by METIS_TAC [extreal_cases, extreal_le_eq, extreal_of_num_def] >> POP_ORW \\
              MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                         (Q.SPEC ‘(Y,B,v)’ IN_MEASURABLE_BOREL_EQ)) \\
              BETA_TAC \\
              Q.EXISTS_TAC ‘\y. Normal r *
                                pos_fn_integral (X,A,u) (\x. indicator_fn (s n i) (x,y))’ \\
              simp [] \\
              reverse CONJ_TAC
              >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> simp [] \\
                  qexistsl_tac [‘\y. pos_fn_integral (X,A,u) (\x. indicator_fn (s n i) (x,y))’,
                                ‘r’] >> rw []) \\
              Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
              HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) \\
          CONJ_TAC >- (qx_genl_tac [‘i’, ‘y’] >> STRIP_TAC \\
                       MATCH_MP_TAC pos_not_neginf \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
          MATCH_MP_TAC ((BETA_RULE o
                         (Q.SPECL [‘(X,A,u)’,
                                   ‘\k x. &k / 2 pow n * indicator_fn (s n k) (x,y)’,
                                   ‘count (4 ** n)’]) o
                         (INST_TYPE [beta |-> “:num”])) pos_fn_integral_sum) >> simp [] \\
          CONJ_TAC >- (GEN_TAC >> DISCH_TAC \\
                       Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          GEN_TAC >> DISCH_TAC \\
         ‘?r. &i / 2 pow n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
          MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL \\
          ASM_SIMP_TAC std_ss [space_def] \\
          qexistsl_tac [‘\x. indicator_fn (s n i) (x,y)’, ‘r’] >> rw []) >> Rewr' \\
   (* LHS simplification *)
      Know ‘pos_fn_integral (Y,B,v)
              (\y. pos_fn_integral (X,A,u) (\x. 2 pow n * indicator_fn (t n) (x,y))) =
            pos_fn_integral (Y,B,v)
              (\y. 2 pow n * pos_fn_integral (X,A,u) (\x. indicator_fn (t n) (x,y)))’
      >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, pow_pos_le]) \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                       MATCH_MP_TAC le_mul >> rw [pow_pos_le] \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw [INDICATOR_FN_POS]) \\
          Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
         ‘2 pow n <> PosInf /\ 2 pow n <> NegInf’
             by METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty] \\
         ‘?r. 0 <= r /\ (2 pow n = Normal r)’
             by METIS_TAC [extreal_cases, pow_pos_le, extreal_le_eq,
                           extreal_of_num_def, le_02] >> POP_ORW \\
          HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) >> Rewr' \\
      Know ‘pos_fn_integral (Y,B,v)
              (\y. 2 pow n * pos_fn_integral (X,A,u) (\x. indicator_fn (t n) (x,y))) =
            2 pow n * pos_fn_integral (Y,B,v)
                        (\y. pos_fn_integral (X,A,u) (\x. indicator_fn (t n) (x,y)))’
      >- (‘2 pow n <> PosInf /\ 2 pow n <> NegInf’
             by METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty] \\
          ‘?r. 0 <= r /\ (2 pow n = Normal r)’
             by METIS_TAC [extreal_cases, pow_pos_le, extreal_le_eq,
                           extreal_of_num_def, le_02] >> POP_ORW \\
          HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [] \\
          MATCH_MP_TAC pos_fn_integral_pos >> rw [INDICATOR_FN_POS]) >> Rewr' \\
     ‘pos_fn_integral (Y,B,v)
        (\y. pos_fn_integral (X,A,u) (\x. indicator_fn (t n) (x,y))) = m (t n)’
         by METIS_TAC [] >> POP_ORW \\
      Know ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (\z. 2 pow n * indicator_fn (t n) z) =
            2 pow n * pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (indicator_fn (t n))’
      >- (‘2 pow n <> PosInf /\ 2 pow n <> NegInf’
             by METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty] \\
          ‘?r. 0 <= r /\ (2 pow n = Normal r)’
             by METIS_TAC [extreal_cases, pow_pos_le, extreal_le_eq,
                           extreal_of_num_def, le_02] >> POP_ORW \\
          HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) >> Rewr' \\
     ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (indicator_fn (t n)) =
      measure ((X,A,u) CROSS (Y,B,v)) (t n)’
         by METIS_TAC [pos_fn_integral_indicator] >> POP_ORW \\
      Know ‘measure ((X,A,u) CROSS (Y,B,v)) (t n) = m (t n)’
      >- (rw [prod_measure_space_alt]) >> Rewr' \\
   (* stage work *)
      Suff ‘pos_fn_integral (Y,B,v)
              (\y. pos_fn_integral (X,A,u)
                     (\x. SIGMA (\k. &k / 2 pow n *
                                     indicator_fn (s n k) (x,y)) (count (4 ** n)))) =
            pos_fn_integral ((X,A,u) CROSS (Y,B,v))
              (\z. SIGMA (\k. &k / 2 pow n *
                              indicator_fn (s n k) z) (count (4 ** n)))’ >- Rewr \\
   (* RHS simplification *)
      Know ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v))
              (\z. SIGMA (\k. &k / 2 pow n * indicator_fn (s n k) z) (count (4 ** n))) =
            SIGMA (\k. pos_fn_integral ((X,A,u) CROSS (Y,B,v))
                         (\z. &k / 2 pow n * indicator_fn (s n k) z)) (count (4 ** n))’
      >- (MATCH_MP_TAC ((BETA_RULE o
                         (Q.SPECL [‘(X,A,u) CROSS (Y,B,v)’,
                                   ‘\k z. &k / 2 pow n * indicator_fn (s n k) z’,
                                   ‘count (4 ** n)’]) o
                         (INST_TYPE [alpha |-> “:'a # 'b”]) o
                         (INST_TYPE [beta |-> “:num”])) pos_fn_integral_sum) >> simp [] \\
          CONJ_TAC >- (rpt STRIP_TAC \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          rpt STRIP_TAC \\
         ‘(X CROSS Y,subsets ((X,A) CROSS (Y,B))) = (X,A) CROSS (Y,B)’
            by METIS_TAC [SPACE] >> POP_ORW \\
         ‘?r. &i / 2 pow n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
          MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL_INDICATOR >> rw []) >> Rewr' \\
      Know ‘!k. pos_fn_integral ((X,A,u) CROSS (Y,B,v))
                  (\z. &k / 2 pow n * indicator_fn (s n k) z) =
                &k / 2 pow n *
                pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (indicator_fn (s n k))’
      >- (GEN_TAC \\
         ‘?r. 0 <= r /\ (&k / 2 pow n = Normal r)’
             by METIS_TAC [extreal_cases, extreal_le_eq, extreal_of_num_def] >> POP_ORW \\
          MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) >> Rewr' \\
     ‘!k. pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (indicator_fn (s n k)) =
          measure ((X,A,u) CROSS (Y,B,v)) (s n k)’
         by METIS_TAC [pos_fn_integral_indicator] >> POP_ORW \\
      Know ‘!k. measure ((X,A,u) CROSS (Y,B,v)) (s n k) = m (s n k)’
      >- (rw [prod_measure_space_alt]) >> Rewr' \\
   (* LHS simplification *)
      Know ‘pos_fn_integral (Y,B,v)
              (\y. pos_fn_integral (X,A,u)
                     (\x. SIGMA (\k. &k / 2 pow n *
                                     indicator_fn (s n k) (x,y)) (count (4 ** n)))) =
            pos_fn_integral (Y,B,v)
              (\y. SIGMA (\k. pos_fn_integral (X,A,u)
                                (\x. &k / 2 pow n * indicator_fn (s n k) (x,y)))
                         (count (4 ** n)))’
      >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
                       MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> REWRITE_TAC [FINITE_COUNT] \\
                       Q.X_GEN_TAC ‘i’ >> rw [] \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                       MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> REWRITE_TAC [FINITE_COUNT] \\
                       Q.X_GEN_TAC ‘i’ >> rw [] \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
          MATCH_MP_TAC ((BETA_RULE o
                         (Q.SPECL [‘(X,A,u)’,
                                   ‘\k x. &k / 2 pow n * indicator_fn (s n k) (x,y)’,
                                   ‘count (4 ** n)’]) o
                         (INST_TYPE [beta |-> “:num”])) pos_fn_integral_sum) >> simp [] \\
          CONJ_TAC >- (rpt STRIP_TAC \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          rpt STRIP_TAC \\
         ‘?r. &i / 2 pow n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
          MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> simp [] \\
          qexistsl_tac [‘\x. indicator_fn (s n i) (x,y)’, ‘r’] >> rw []) >> Rewr' \\
      Know ‘pos_fn_integral (Y,B,v)
              (\y. SIGMA (\k. pos_fn_integral (X,A,u)
                                (\x. &k / 2 pow n * indicator_fn (s n k) (x,y)))
                         (count (4 ** n))) =
            SIGMA (\k. pos_fn_integral (Y,B,v)
                         (\y. pos_fn_integral (X,A,u)
                                (\x. &k / 2 pow n * indicator_fn (s n k) (x,y))))
                  (count (4 ** n))’
      >- (MATCH_MP_TAC ((BETA_RULE o
                         (Q.SPECL [‘(Y,B,v)’,
                                   ‘\k y. pos_fn_integral (X,A,u)
                                            (\x. &k / 2 pow n * indicator_fn (s n k) (x,y))’,
                                   ‘count (4 ** n)’]) o
                         (INST_TYPE [alpha |-> beta]) o
                         (INST_TYPE [beta |-> “:num”])) pos_fn_integral_sum) >> simp [] \\
          CONJ_TAC >- (GEN_TAC >> DISCH_TAC \\
                       Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          rpt STRIP_TAC \\
         ‘?r. 0 <= r /\ (&i / 2 pow n = Normal r)’
             by METIS_TAC [extreal_cases, extreal_le_eq, extreal_of_num_def] >> POP_ORW \\
          MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                     (Q.SPEC ‘(Y,B,v)’ IN_MEASURABLE_BOREL_EQ)) \\
          BETA_TAC \\
          Q.EXISTS_TAC ‘\y. Normal r *
                            pos_fn_integral (X,A,u) (\x. indicator_fn (s n i) (x,y))’ \\
          reverse CONJ_TAC
          >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> simp [] \\
              qexistsl_tac [‘\y. pos_fn_integral (X,A,u) (\x. indicator_fn (s n i) (x,y))’,
                            ‘r’] >> rw []) \\
          Q.X_GEN_TAC ‘y’ >> RW_TAC std_ss [] \\
          HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) >> Rewr' \\
      Suff ‘!k. pos_fn_integral (Y,B,v)
                  (\y. pos_fn_integral (X,A,u)
                         (\x. &k / 2 pow n * indicator_fn (s n k) (x,y))) =
                &k / 2 pow n * m (s n k)’ >- Rewr \\
      GEN_TAC \\
     ‘?r. 0 <= r /\ (&k / 2 pow n = Normal r)’
             by METIS_TAC [extreal_cases, extreal_le_eq, extreal_of_num_def] >> POP_ORW \\
      Know ‘pos_fn_integral (Y,B,v)
              (\y. pos_fn_integral (X,A,u)
                     (\x. Normal r * indicator_fn (s n k) (x,y))) =
            pos_fn_integral (Y,B,v)
              (\y. Normal r * pos_fn_integral (X,A,u) (\x. indicator_fn (s n k) (x,y)))’
      >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
                       MATCH_MP_TAC le_mul \\
                       rw [INDICATOR_FN_POS, extreal_le_eq, extreal_of_num_def]) \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                       MATCH_MP_TAC le_mul \\
                       CONJ_TAC >- rw [extreal_le_eq, extreal_of_num_def] \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw [INDICATOR_FN_POS]) \\
          Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
          HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) >> Rewr' \\
      Know ‘pos_fn_integral (Y,B,v)
              (\y. Normal r * pos_fn_integral (X,A,u) (\x. indicator_fn (s n k) (x,y))) =
            Normal r * pos_fn_integral (Y,B,v)
                         (\y. pos_fn_integral (X,A,u) (\x. indicator_fn (s n k) (x,y)))’
      >- (HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [] \\
          MATCH_MP_TAC pos_fn_integral_pos >> rw [INDICATOR_FN_POS]) >> Rewr' \\
      Suff ‘pos_fn_integral (Y,B,v)
              (\y. pos_fn_integral (X,A,u) (\x. indicator_fn (s n k) (x,y))) =
            m (s n k)’ >- Rewr \\
      METIS_TAC [],
      (* goal 6 (of 6), symmetric with goal 5 *)
      Know ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) f =
            pos_fn_integral ((X,A,u) CROSS (Y,B,v))
              (\x. sup (IMAGE (\n. fn_seq ((X,A,u) CROSS (Y,B,v)) f n x) UNIV))’
      >- (MATCH_MP_TAC pos_fn_integral_cong >> simp []) >> Rewr' \\
      Know ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v))
              (\x. sup (IMAGE (\n. fn_seq ((X,A,u) CROSS (Y,B,v)) f n x) UNIV)) =
            sup (IMAGE (\n. pos_fn_integral ((X,A,u) CROSS (Y,B,v))
                              (\z. fn_seq ((X,A,u) CROSS (Y,B,v)) f n z)) UNIV)’
      >- (HO_MATCH_MP_TAC lebesgue_monotone_convergence >> simp [] \\
          REWRITE_TAC [CONJ_ASSOC] (* easier goals first *) \\
          reverse CONJ_TAC (* mono_increasing *)
          >- (rpt STRIP_TAC >> MATCH_MP_TAC lemma_fn_seq_mono_increasing \\
              FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
          reverse CONJ_TAC (* positive *)
          >- (rpt STRIP_TAC >> MATCH_MP_TAC lemma_fn_seq_positive \\
              FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
          RW_TAC std_ss [fn_seq_def] \\
         ‘(X CROSS Y,subsets ((X,A) CROSS (Y,B))) = (X,A) CROSS (Y,B)’
            by METIS_TAC [SPACE] >> POP_ORW \\
          MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD \\
          ASM_SIMP_TAC std_ss [space_def] \\
          qexistsl_tac [‘\z. SIGMA (\k. &k / 2 pow n * indicator_fn (s n k) z) (count (4 ** n))’,
                        ‘\z. 2 pow n * indicator_fn (t n) z’] \\
          ASM_SIMP_TAC std_ss [CONJ_ASSOC] \\
          reverse CONJ_TAC (* nonnegative *)
          >- (Q.X_GEN_TAC ‘z’ >> DISCH_TAC >> DISJ1_TAC \\
              CONJ_TAC >> MATCH_MP_TAC pos_not_neginf >| (* 2 subgoals *)
              [ (* goal 5.1 (of 2) *)
                MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> rw [] \\
                MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS],
                (* goal 5.2 (of 2) *)
                MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, pow_pos_le] ]) \\
          CONJ_TAC (* Borel_measurable #1 *)
          >- (MATCH_MP_TAC (INST_TYPE [beta |-> “:num”] IN_MEASURABLE_BOREL_SUM) \\
              ASM_SIMP_TAC std_ss [space_def] \\
              qexistsl_tac [‘\k z. &k / 2 pow n * indicator_fn (s n k) z’,
                            ‘count (4 ** n)’] >> simp [] \\
              reverse CONJ_TAC
              >- (qx_genl_tac [‘i’, ‘z’] >> STRIP_TAC \\
                  MATCH_MP_TAC pos_not_neginf \\
                  MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
              rpt STRIP_TAC \\
             ‘?r. &i / 2 pow n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
              MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL_INDICATOR >> rw []) \\
         ‘2 pow n <> PosInf /\ 2 pow n <> NegInf’
             by METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty] \\
         ‘?r. 2 pow n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
          MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL_INDICATOR >> rw []) >> Rewr' \\
      Know ‘pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. f (x,y))) =
            pos_fn_integral (X,A,u)
              (\x. pos_fn_integral (Y,B,v)
                     (\y. sup (IMAGE (\n. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y)) UNIV)))’
      >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw []) \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw []) \\
          Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
          MATCH_MP_TAC pos_fn_integral_cong >> simp []) >> Rewr' \\
      Know ‘pos_fn_integral (X,A,u)
              (\x. pos_fn_integral (Y,B,v)
                     (\y. sup (IMAGE (\n. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y)) UNIV))) =
            pos_fn_integral (X,A,u)
              (\x. sup (IMAGE (\n. pos_fn_integral (Y,B,v)
                                     (\y. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y))) UNIV))’
      >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw []) \\
          CONJ_TAC
          >- (Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
              rw [le_sup', IN_IMAGE, IN_UNIV] \\
              MATCH_MP_TAC le_trans \\
              Q.EXISTS_TAC ‘pos_fn_integral (Y,B,v)
                              (\y. fn_seq ((X,A,u) CROSS (Y,B,v)) f 0 (x,y))’ \\
              CONJ_TAC >- (MATCH_MP_TAC pos_fn_integral_pos >> rw [lemma_fn_seq_positive]) \\
              POP_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘0’ >> REWRITE_TAC []) \\
          Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
          HO_MATCH_MP_TAC lebesgue_monotone_convergence \\
          simp [lemma_fn_seq_positive, lemma_fn_seq_mono_increasing]) >> Rewr' \\
      Know ‘pos_fn_integral (X,A,u)
              (\x. sup (IMAGE (\n. pos_fn_integral (Y,B,v)
                                     (\y. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y))) UNIV)) =
            sup (IMAGE (\n. pos_fn_integral (X,A,u)
                              (\x. pos_fn_integral (Y,B,v)
                                     (\y. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y)))) UNIV)’
      >- (HO_MATCH_MP_TAC lebesgue_monotone_convergence >> simp [] \\
          CONJ_TAC >- (rpt STRIP_TAC >> MATCH_MP_TAC pos_fn_integral_pos \\
                       simp [lemma_fn_seq_positive]) \\
          RW_TAC std_ss [ext_mono_increasing_def] \\
          MATCH_MP_TAC pos_fn_integral_mono >> simp [lemma_fn_seq_positive] \\
          rpt STRIP_TAC \\
          irule (SIMP_RULE std_ss [ext_mono_increasing_def]
                                  lemma_fn_seq_mono_increasing) >> art [] \\
          FIRST_X_ASSUM MATCH_MP_TAC >> rw []) >> Rewr' \\
      Suff ‘!n. pos_fn_integral (X,A,u)
                  (\x. pos_fn_integral (Y,B,v) (\y. fn_seq ((X,A,u) CROSS (Y,B,v)) f n (x,y))) =
                pos_fn_integral ((X,A,u) CROSS (Y,B,v))
                  (\z. fn_seq ((X,A,u) CROSS (Y,B,v)) f n z)’ >- rw [] \\
   (* ‘sup’ disappeared now *)
      GEN_TAC >> ASM_SIMP_TAC std_ss [fn_seq_def] \\
     ‘!k. {x | x IN X CROSS Y /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n} = s n k’
         by METIS_TAC [] >> POP_ORW \\
   (* RHS simplification *)
      Know ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v))
              (\z. SIGMA (\k. &k / 2 pow n * indicator_fn (s n k) z) (count (4 ** n)) +
                   2 pow n * indicator_fn (t n) z) =
            pos_fn_integral ((X,A,u) CROSS (Y,B,v))
              (\z. SIGMA (\k. &k / 2 pow n * indicator_fn (s n k) z) (count (4 ** n))) +
            pos_fn_integral ((X,A,u) CROSS (Y,B,v))
              (\z. 2 pow n * indicator_fn (t n) z)’
      >- (HO_MATCH_MP_TAC pos_fn_integral_add >> simp [] \\
          CONJ_TAC >- (rpt STRIP_TAC \\
                       MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> rw [] \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          CONJ_TAC >- (rpt STRIP_TAC \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, pow_pos_le]) \\
         ‘(X CROSS Y,subsets ((X,A) CROSS (Y,B))) = (X,A) CROSS (Y,B)’
            by METIS_TAC [SPACE] >> POP_ORW \\
          reverse CONJ_TAC
          >- (‘2 pow n <> PosInf /\ 2 pow n <> NegInf’
                 by METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty] \\
              ‘?r. 2 pow n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
              MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL_INDICATOR >> rw []) \\
          MATCH_MP_TAC ((INST_TYPE [alpha |-> “:'a # 'b”] o
                         INST_TYPE [beta |-> “:num”]) IN_MEASURABLE_BOREL_SUM) >> simp [] \\
          qexistsl_tac [‘\k z. &k / 2 pow n * indicator_fn (s n k) z’,
                        ‘count (4 ** n)’] >> simp [] \\
          reverse CONJ_TAC >- (qx_genl_tac [‘i’, ‘z’] >> STRIP_TAC \\
                               MATCH_MP_TAC pos_not_neginf \\
                               MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          rpt STRIP_TAC \\
         ‘?r. &i / 2 pow n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
          MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL_INDICATOR >> rw []) >> Rewr' \\
   (* LHS simplification *)
      Know ‘pos_fn_integral (X,A,u)
              (\x. pos_fn_integral (Y,B,v)
                     (\y. SIGMA (\k. &k / 2 pow n * indicator_fn (s n k) (x,y)) (count (4 ** n)) +
                          2 pow n * indicator_fn (t n) (x,y))) =
            pos_fn_integral (X,A,u)
              (\x. pos_fn_integral (Y,B,v)
                     (\y. SIGMA (\k. &k / 2 pow n * indicator_fn (s n k) (x,y)) (count (4 ** n))) +
                   pos_fn_integral (Y,B,v)
                     (\y. 2 pow n * indicator_fn (t n) (x,y)))’
      >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
                       MATCH_MP_TAC le_add \\
                       reverse CONJ_TAC
                       >- (MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, pow_pos_le]) \\
                       MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> REWRITE_TAC [FINITE_COUNT] \\
                       Q.X_GEN_TAC ‘i’ >> rw [] \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
                       MATCH_MP_TAC le_add \\
                       reverse CONJ_TAC
                       >- (MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
                           MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, pow_pos_le]) \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
                       MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> REWRITE_TAC [FINITE_COUNT] \\
                       Q.X_GEN_TAC ‘i’ >> rw [] \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, pow_pos_le]) \\
          Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
          HO_MATCH_MP_TAC pos_fn_integral_add >> simp [] \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                       MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> REWRITE_TAC [FINITE_COUNT] \\
                       Q.X_GEN_TAC ‘i’ >> rw [] \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, pow_pos_le]) \\
          reverse CONJ_TAC
          >- (‘2 pow n <> PosInf /\ 2 pow n <> NegInf’
                 by METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty] \\
              ‘?r. 2 pow n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
              MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> simp [] \\
              qexistsl_tac [‘\y. indicator_fn (t n) (x,y)’, ‘r’] >> rw []) \\
          MATCH_MP_TAC (INST_TYPE [beta |-> “:num”] IN_MEASURABLE_BOREL_SUM) >> simp [] \\
          qexistsl_tac [‘\k y. &k / 2 pow n * indicator_fn (s n k) (x,y)’,
                        ‘count (4 ** n)’] >> simp [] \\
          reverse CONJ_TAC >- (rpt GEN_TAC >> STRIP_TAC \\
                               MATCH_MP_TAC pos_not_neginf \\
                               MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          rpt STRIP_TAC \\
         ‘?r. &i / 2 pow n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
          MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> simp [] \\
          qexistsl_tac [‘\y. indicator_fn (s n i) (x,y)’, ‘r’] >> rw []) >> Rewr' \\
   (* LHS simplification *)
      Know ‘pos_fn_integral (X,A,u)
              (\x. pos_fn_integral (Y,B,v)
                     (\y. SIGMA (\k. &k / 2 pow n * indicator_fn (s n k) (x,y))
                                (count (4 ** n))) +
                   pos_fn_integral (Y,B,v) (\y. 2 pow n * indicator_fn (t n) (x,y))) =
            pos_fn_integral (X,A,u)
              (\x. pos_fn_integral (Y,B,v)
                     (\y. SIGMA (\k. &k / 2 pow n * indicator_fn (s n k) (x,y))
                                (count (4 ** n)))) +
            pos_fn_integral (X,A,u)
              (\x. pos_fn_integral (Y,B,v) (\y. 2 pow n * indicator_fn (t n) (x,y)))’
      >- (HO_MATCH_MP_TAC pos_fn_integral_add >> simp [] \\
          CONJ_TAC >- (rpt STRIP_TAC \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
                       MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> REWRITE_TAC [FINITE_COUNT] \\
                       Q.X_GEN_TAC ‘i’ >> rw [] \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          CONJ_TAC >- (rpt STRIP_TAC \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, pow_pos_le]) \\
          reverse CONJ_TAC
          >- (‘2 pow n <> PosInf /\ 2 pow n <> NegInf’
                 by METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty] \\
              ‘?r. 0 <= r /\ (2 pow n = Normal r)’
                 by METIS_TAC [extreal_cases, pow_pos_le, extreal_le_eq,
                               extreal_of_num_def, le_02] >> POP_ORW \\
              MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                         (Q.SPEC ‘(X,A,u)’ IN_MEASURABLE_BOREL_EQ)) \\
              BETA_TAC \\
              Q.EXISTS_TAC ‘\x. Normal r *
                                pos_fn_integral (Y,B,v) (\y. indicator_fn (t n) (x,y))’ \\
              reverse CONJ_TAC
              >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> simp [] \\
                  qexistsl_tac [‘\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (t n) (x,y))’,
                                ‘r’] >> rw []) \\
              Q.X_GEN_TAC ‘x’ >> RW_TAC std_ss [] \\
              HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) \\
          MATCH_MP_TAC (INST_TYPE [beta |-> “:num”] IN_MEASURABLE_BOREL_SUM) \\
          ASM_SIMP_TAC std_ss [space_def] \\
          qexistsl_tac [‘\k x. pos_fn_integral (Y,B,v)
                                 (\y. &k / 2 pow n * indicator_fn (s n k) (x,y))’,
                        ‘count (4 ** n)’] >> simp [] \\
          CONJ_TAC
          >- (rpt STRIP_TAC \\
             ‘?r. 0 <= r /\ (&i / 2 pow n = Normal r)’
                 by METIS_TAC [extreal_cases, extreal_le_eq, extreal_of_num_def] >> POP_ORW \\
              MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                         (Q.SPEC ‘(X,A,u)’ IN_MEASURABLE_BOREL_EQ)) \\
              BETA_TAC \\
              Q.EXISTS_TAC ‘\x. Normal r *
                                pos_fn_integral (Y,B,v) (\y. indicator_fn (s n i) (x,y))’ \\
              simp [] \\
              reverse CONJ_TAC
              >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> simp [] \\
                  qexistsl_tac [‘\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (s n i) (x,y))’,
                                ‘r’] >> rw []) \\
              Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
              HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) \\
          CONJ_TAC >- (qx_genl_tac [‘i’, ‘x’] >> STRIP_TAC \\
                       MATCH_MP_TAC pos_not_neginf \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
          MATCH_MP_TAC ((BETA_RULE o
                         (Q.SPECL [‘(Y,B,v)’,
                                   ‘\k y. &k / 2 pow n * indicator_fn (s n k) (x,y)’,
                                   ‘count (4 ** n)’]) o
                         (INST_TYPE [alpha |-> beta]) o
                         (INST_TYPE [beta |-> “:num”])) pos_fn_integral_sum) >> simp [] \\
          CONJ_TAC >- (GEN_TAC >> DISCH_TAC \\
                       Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          GEN_TAC >> DISCH_TAC \\
         ‘?r. &i / 2 pow n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
          MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL \\
          ASM_SIMP_TAC std_ss [space_def] \\
          qexistsl_tac [‘\y. indicator_fn (s n i) (x,y)’, ‘r’] >> rw []) >> Rewr' \\
   (* LHS simplification *)
      Know ‘pos_fn_integral (X,A,u)
              (\x. pos_fn_integral (Y,B,v) (\y. 2 pow n * indicator_fn (t n) (x,y))) =
            pos_fn_integral (X,A,u)
              (\x. 2 pow n * pos_fn_integral (Y,B,v) (\y. indicator_fn (t n) (x,y)))’
      >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS, pow_pos_le]) \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
                       MATCH_MP_TAC le_mul >> rw [pow_pos_le] \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw [INDICATOR_FN_POS]) \\
          Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
         ‘2 pow n <> PosInf /\ 2 pow n <> NegInf’
             by METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty] \\
         ‘?r. 0 <= r /\ (2 pow n = Normal r)’
             by METIS_TAC [extreal_cases, pow_pos_le, extreal_le_eq,
                           extreal_of_num_def, le_02] >> POP_ORW \\
          HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) >> Rewr' \\
      Know ‘pos_fn_integral (X,A,u)
              (\x. 2 pow n * pos_fn_integral (Y,B,v) (\y. indicator_fn (t n) (x,y))) =
            2 pow n * pos_fn_integral (X,A,u)
                        (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (t n) (x,y)))’
      >- (‘2 pow n <> PosInf /\ 2 pow n <> NegInf’
             by METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty] \\
          ‘?r. 0 <= r /\ (2 pow n = Normal r)’
             by METIS_TAC [extreal_cases, pow_pos_le, extreal_le_eq,
                           extreal_of_num_def, le_02] >> POP_ORW \\
          HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [] \\
          MATCH_MP_TAC pos_fn_integral_pos >> rw [INDICATOR_FN_POS]) >> Rewr' \\
     ‘pos_fn_integral (X,A,u)
        (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (t n) (x,y))) = m (t n)’
         by METIS_TAC [] >> POP_ORW \\
      Know ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (\z. 2 pow n * indicator_fn (t n) z) =
            2 pow n * pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (indicator_fn (t n))’
      >- (‘2 pow n <> PosInf /\ 2 pow n <> NegInf’
             by METIS_TAC [pow_not_infty, extreal_of_num_def, extreal_not_infty] \\
          ‘?r. 0 <= r /\ (2 pow n = Normal r)’
             by METIS_TAC [extreal_cases, pow_pos_le, extreal_le_eq,
                           extreal_of_num_def, le_02] >> POP_ORW \\
          HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) >> Rewr' \\
     ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (indicator_fn (t n)) =
      measure ((X,A,u) CROSS (Y,B,v)) (t n)’
         by METIS_TAC [pos_fn_integral_indicator] >> POP_ORW \\
      Know ‘measure ((X,A,u) CROSS (Y,B,v)) (t n) = m (t n)’
      >- (rw [prod_measure_space_alt]) >> Rewr' \\
   (* stage work *)
      Suff ‘pos_fn_integral (X,A,u)
              (\x. pos_fn_integral (Y,B,v)
                     (\y. SIGMA (\k. &k / 2 pow n *
                                     indicator_fn (s n k) (x,y)) (count (4 ** n)))) =
            pos_fn_integral ((X,A,u) CROSS (Y,B,v))
              (\z. SIGMA (\k. &k / 2 pow n *
                              indicator_fn (s n k) z) (count (4 ** n)))’ >- Rewr \\
   (* RHS simplification *)
      Know ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v))
              (\z. SIGMA (\k. &k / 2 pow n * indicator_fn (s n k) z) (count (4 ** n))) =
            SIGMA (\k. pos_fn_integral ((X,A,u) CROSS (Y,B,v))
                         (\z. &k / 2 pow n * indicator_fn (s n k) z)) (count (4 ** n))’
      >- (MATCH_MP_TAC ((BETA_RULE o
                         (Q.SPECL [‘(X,A,u) CROSS (Y,B,v)’,
                                   ‘\k z. &k / 2 pow n * indicator_fn (s n k) z’,
                                   ‘count (4 ** n)’]) o
                         (INST_TYPE [alpha |-> “:'a # 'b”]) o
                         (INST_TYPE [beta |-> “:num”])) pos_fn_integral_sum) >> simp [] \\
          CONJ_TAC >- (rpt STRIP_TAC \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          rpt STRIP_TAC \\
         ‘(X CROSS Y,subsets ((X,A) CROSS (Y,B))) = (X,A) CROSS (Y,B)’
            by METIS_TAC [SPACE] >> POP_ORW \\
         ‘?r. &i / 2 pow n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
          MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL_INDICATOR >> rw []) >> Rewr' \\
      Know ‘!k. pos_fn_integral ((X,A,u) CROSS (Y,B,v))
                  (\z. &k / 2 pow n * indicator_fn (s n k) z) =
                &k / 2 pow n *
                pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (indicator_fn (s n k))’
      >- (GEN_TAC \\
         ‘?r. 0 <= r /\ (&k / 2 pow n = Normal r)’
             by METIS_TAC [extreal_cases, extreal_le_eq, extreal_of_num_def] >> POP_ORW \\
          MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) >> Rewr' \\
     ‘!k. pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (indicator_fn (s n k)) =
          measure ((X,A,u) CROSS (Y,B,v)) (s n k)’
         by METIS_TAC [pos_fn_integral_indicator] >> POP_ORW \\
      Know ‘!k. measure ((X,A,u) CROSS (Y,B,v)) (s n k) = m (s n k)’
      >- (rw [prod_measure_space_alt]) >> Rewr' \\
   (* LHS simplification *)
      Know ‘pos_fn_integral (X,A,u)
              (\x. pos_fn_integral (Y,B,v)
                     (\y. SIGMA (\k. &k / 2 pow n *
                                     indicator_fn (s n k) (x,y)) (count (4 ** n)))) =
            pos_fn_integral (X,A,u)
              (\x. SIGMA (\k. pos_fn_integral (Y,B,v)
                                (\y. &k / 2 pow n * indicator_fn (s n k) (x,y)))
                         (count (4 ** n)))’
      >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
                       MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> REWRITE_TAC [FINITE_COUNT] \\
                       Q.X_GEN_TAC ‘i’ >> rw [] \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
                       MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> REWRITE_TAC [FINITE_COUNT] \\
                       Q.X_GEN_TAC ‘i’ >> rw [] \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
          MATCH_MP_TAC ((BETA_RULE o
                         (Q.SPECL [‘(Y,B,v)’,
                                   ‘\k y. &k / 2 pow n * indicator_fn (s n k) (x,y)’,
                                   ‘count (4 ** n)’]) o
                         (INST_TYPE [alpha |-> beta]) o
                         (INST_TYPE [beta |-> “:num”])) pos_fn_integral_sum) >> simp [] \\
          CONJ_TAC >- (rpt STRIP_TAC \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          rpt STRIP_TAC \\
         ‘?r. &i / 2 pow n = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
          MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> simp [] \\
          qexistsl_tac [‘\y. indicator_fn (s n i) (x,y)’, ‘r’] >> rw []) >> Rewr' \\
      Know ‘pos_fn_integral (X,A,u)
              (\x. SIGMA (\k. pos_fn_integral (Y,B,v)
                                (\y. &k / 2 pow n * indicator_fn (s n k) (x,y)))
                         (count (4 ** n))) =
            SIGMA (\k. pos_fn_integral (X,A,u)
                         (\x. pos_fn_integral (Y,B,v)
                                (\y. &k / 2 pow n * indicator_fn (s n k) (x,y))))
                  (count (4 ** n))’
      >- (MATCH_MP_TAC ((BETA_RULE o
                         (Q.SPECL [‘(X,A,u)’,
                                   ‘\k x. pos_fn_integral (Y,B,v)
                                            (\y. &k / 2 pow n * indicator_fn (s n k) (x,y))’,
                                   ‘count (4 ** n)’]) o
                         (INST_TYPE [beta |-> “:num”])) pos_fn_integral_sum) >> simp [] \\
          CONJ_TAC >- (GEN_TAC >> DISCH_TAC \\
                       Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
                       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS]) \\
          rpt STRIP_TAC \\
         ‘?r. 0 <= r /\ (&i / 2 pow n = Normal r)’
             by METIS_TAC [extreal_cases, extreal_le_eq, extreal_of_num_def] >> POP_ORW \\
          MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                     (Q.SPEC ‘(X,A,u)’ IN_MEASURABLE_BOREL_EQ)) \\
          BETA_TAC \\
          Q.EXISTS_TAC ‘\x. Normal r *
                            pos_fn_integral (Y,B,v) (\y. indicator_fn (s n i) (x,y))’ \\
          reverse CONJ_TAC
          >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL >> simp [] \\
              qexistsl_tac [‘\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (s n i) (x,y))’,
                            ‘r’] >> rw []) \\
          Q.X_GEN_TAC ‘x’ >> RW_TAC std_ss [] \\
          HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) >> Rewr' \\
      Suff ‘!k. pos_fn_integral (X,A,u)
                  (\x. pos_fn_integral (Y,B,v)
                         (\y. &k / 2 pow n * indicator_fn (s n k) (x,y))) =
                &k / 2 pow n * m (s n k)’ >- Rewr \\
      GEN_TAC \\
     ‘?r. 0 <= r /\ (&k / 2 pow n = Normal r)’
             by METIS_TAC [extreal_cases, extreal_le_eq, extreal_of_num_def] >> POP_ORW \\
      Know ‘pos_fn_integral (X,A,u)
              (\x. pos_fn_integral (Y,B,v)
                     (\y. Normal r * indicator_fn (s n k) (x,y))) =
            pos_fn_integral (X,A,u)
              (\x. Normal r * pos_fn_integral (Y,B,v) (\y. indicator_fn (s n k) (x,y)))’
      >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
                       MATCH_MP_TAC pos_fn_integral_pos >> simp [] \\
                       Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                       MATCH_MP_TAC le_mul \\
                       rw [INDICATOR_FN_POS, extreal_le_eq, extreal_of_num_def]) \\
          CONJ_TAC >- (Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
                       MATCH_MP_TAC le_mul \\
                       CONJ_TAC >- rw [extreal_le_eq, extreal_of_num_def] \\
                       MATCH_MP_TAC pos_fn_integral_pos >> rw [INDICATOR_FN_POS]) \\
          Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
          HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [INDICATOR_FN_POS]) >> Rewr' \\
      Know ‘pos_fn_integral (X,A,u)
              (\x. Normal r * pos_fn_integral (Y,B,v) (\y. indicator_fn (s n k) (x,y))) =
            Normal r * pos_fn_integral (X,A,u)
                         (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (s n k) (x,y)))’
      >- (HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [] \\
          MATCH_MP_TAC pos_fn_integral_pos >> rw [INDICATOR_FN_POS]) >> Rewr' \\
      Suff ‘pos_fn_integral (X,A,u)
              (\x. pos_fn_integral (Y,B,v) (\y. indicator_fn (s n k) (x,y))) =
            m (s n k)’ >- Rewr \\
      METIS_TAC [] ]
QED

(* Corollary 14.9 (Fubini's theorem) [1, p.142]

   Named after Guido Fubini, an Italian mathematician [6].
 *)
Theorem FUBINI :
    !(X :'a set) (Y :'b set) A B u v f.
        sigma_finite_measure_space (X,A,u) /\
        sigma_finite_measure_space (Y,B,v) /\
        f IN measurable ((X,A) CROSS (Y,B)) Borel /\
     (* if at least one of the three integrals is finite (P \/ Q \/ R) *)
       (pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (abs o f) <> PosInf \/
        pos_fn_integral (Y,B,v)
          (\y. pos_fn_integral (X,A,u) (\x. (abs o f) (x,y))) <> PosInf \/
        pos_fn_integral (X,A,u)
          (\x. pos_fn_integral (Y,B,v) (\y. (abs o f) (x,y))) <> PosInf)
       ==>
     (* then all three integrals are finite (P /\ Q /\ R) *)
        pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (abs o f) <> PosInf /\
        pos_fn_integral (Y,B,v)
          (\y. pos_fn_integral (X,A,u) (\x. (abs o f) (x,y))) <> PosInf /\
        pos_fn_integral (X,A,u)
          (\x. pos_fn_integral (Y,B,v) (\y. (abs o f) (x,y))) <> PosInf /\
        integrable ((X,A,u) CROSS (Y,B,v)) f /\
       (AE y::(Y,B,v). integrable (X,A,u) (\x. f (x,y))) /\
       (AE x::(X,A,u). integrable (Y,B,v) (\y. f (x,y))) /\
        integrable (X,A,u) (\x. integral (Y,B,v) (\y. f (x,y))) /\
        integrable (Y,B,v) (\y. integral (X,A,u) (\x. f (x,y))) /\
       (integral ((X,A,u) CROSS (Y,B,v)) f =
        integral (Y,B,v) (\y. integral (X,A,u) (\x. f (x,y)))) /\
       (integral ((X,A,u) CROSS (Y,B,v)) f =
        integral (X,A,u) (\x. integral (Y,B,v) (\y. f (x,y))))
Proof
    rpt GEN_TAC
 (* prevent from separating ‘P \/ Q \/ R’ *)
 >> ONCE_REWRITE_TAC [DECIDE “(A /\ B /\ C /\ D ==> E) <=>
                              (A ==> B ==> C ==> D ==> E)”]
 >> rpt DISCH_TAC
 >> ‘measure_space ((X,A,u) CROSS (Y,B,v))’
      by PROVE_TAC [measure_space_prod_measure]
 >> ‘sigma_algebra ((X,A) CROSS (Y,B))’
      by (MATCH_MP_TAC SIGMA_ALGEBRA_PROD_SIGMA \\
          fs [sigma_algebra_def, algebra_def, sigma_finite_measure_space_def,
              measure_space_def])
 >> ‘(abs o f) IN Borel_measurable ((X,A) CROSS (Y,B))’
      by (MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS' >> art [])
 >> ‘!s. s IN X CROSS Y ==> 0 <= (abs o f) s’ by rw [o_DEF, abs_pos]
 (* applying TONELLI on ‘abs o f’ *)
 >> Know ‘(!y. y IN Y ==> (\x. (abs o f) (x,y)) IN Borel_measurable (X,A)) /\
          (!x. x IN X ==> (\y. (abs o f) (x,y)) IN Borel_measurable (Y,B)) /\
          (\x. pos_fn_integral (Y,B,v) (\y. (abs o f) (x,y))) IN Borel_measurable (X,A) /\
          (\y. pos_fn_integral (X,A,u) (\x. (abs o f) (x,y))) IN Borel_measurable (Y,B) /\
          pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (abs o f) =
          pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. (abs o f) (x,y))) /\
          pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (abs o f) =
          pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. (abs o f) (x,y)))’
 >- (MATCH_MP_TAC (Q.SPECL [‘X’, ‘Y’, ‘A’, ‘B’, ‘u’, ‘v’, ‘abs o f’] TONELLI) \\
     rw []) >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!s. s IN X CROSS Y ==> 0 <= (abs o f) s’ K_TAC
 (* group the first subgoals together *)
 >> NTAC 2 (ONCE_REWRITE_TAC [CONJ_ASSOC])
 >> STRONG_CONJ_TAC >- METIS_TAC []
 (* replace one of three finite integrals by all finite integrals *)
 >> Q.PAT_X_ASSUM ‘P \/ Q \/ R’ K_TAC
 >> STRIP_TAC (* P /\ Q /\ R *)
 >> Know ‘space ((X,A) CROSS (Y,B)) = X CROSS Y’
 >- (rw [prod_sigma_def] >> REWRITE_TAC [SPACE_SIGMA]) >> DISCH_TAC
 >> ‘m_space ((X,A,u) CROSS (Y,B,v)) = X CROSS Y’ by rw [prod_measure_space_alt]
 >> ‘measurable_sets ((X,A,u) CROSS (Y,B,v)) =
       subsets ((X,A) CROSS (Y,B))’ by rw [prod_measure_space_alt]
 >> ‘(X CROSS Y,subsets ((X,A) CROSS (Y,B))) = (X,A) CROSS (Y,B)’
       by METIS_TAC [SPACE]
 (* integrable ((X,A,u) CROSS (Y,B,v)) f *)
 >> STRONG_CONJ_TAC
 >- (MATCH_MP_TAC integrable_from_abs >> simp [integrable_def] \\
     ASM_SIMP_TAC bool_ss [FN_PLUS_ABS_SELF, FN_MINUS_ABS_ZERO, pos_fn_integral_zero] \\
     rw [] (* 0 <> PosInf *)) >> DISCH_TAC
 (* applying TONELLI again on both f^+ and f^- *)
 >> ‘(fn_plus f) IN measurable ((X,A) CROSS (Y,B)) Borel’
      by PROVE_TAC [IN_MEASURABLE_BOREL_FN_PLUS]
 >> ‘!s. s IN X CROSS Y ==> 0 <= (fn_plus f) s’ by rw [FN_PLUS_POS]
 >> Know ‘(!y. y IN Y ==> (\x. (fn_plus f) (x,y)) IN Borel_measurable (X,A)) /\
          (!x. x IN X ==> (\y. (fn_plus f) (x,y)) IN Borel_measurable (Y,B)) /\
          (\x. pos_fn_integral (Y,B,v) (\y. (fn_plus f) (x,y))) IN Borel_measurable (X,A) /\
          (\y. pos_fn_integral (X,A,u) (\x. (fn_plus f) (x,y))) IN Borel_measurable (Y,B) /\
          pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_plus f) =
          pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. (fn_plus f) (x,y))) /\
          pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_plus f) =
          pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. (fn_plus f) (x,y)))’
 >- (MATCH_MP_TAC (Q.SPECL [‘X’, ‘Y’, ‘A’, ‘B’, ‘u’, ‘v’, ‘fn_plus f’] TONELLI) \\
     rw []) >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!s. s IN X CROSS Y ==> 0 <= (fn_plus f) s’ K_TAC
 >> ‘(fn_minus f) IN measurable ((X,A) CROSS (Y,B)) Borel’
      by PROVE_TAC [IN_MEASURABLE_BOREL_FN_MINUS]
 >> ‘!s. s IN X CROSS Y ==> 0 <= (fn_minus f) s’ by rw [FN_MINUS_POS]
 >> Know ‘(!y. y IN Y ==> (\x. (fn_minus f) (x,y)) IN Borel_measurable (X,A)) /\
          (!x. x IN X ==> (\y. (fn_minus f) (x,y)) IN Borel_measurable (Y,B)) /\
          (\x. pos_fn_integral (Y,B,v) (\y. (fn_minus f) (x,y))) IN Borel_measurable (X,A) /\
          (\y. pos_fn_integral (X,A,u) (\x. (fn_minus f) (x,y))) IN Borel_measurable (Y,B) /\
          pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_minus f) =
          pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. (fn_minus f) (x,y))) /\
          pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_minus f) =
          pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. (fn_minus f) (x,y)))’
 >- (MATCH_MP_TAC (Q.SPECL [‘X’, ‘Y’, ‘A’, ‘B’, ‘u’, ‘v’, ‘fn_minus f’] TONELLI) \\
     rw []) >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!s. s IN X CROSS Y ==> 0 <= (fn_minus f) s’ K_TAC
 >> Q.PAT_X_ASSUM ‘sigma_finite_measure_space (X,A,u)’
      (STRIP_ASSUME_TAC o (REWRITE_RULE [sigma_finite_measure_space_def]))
 >> Q.PAT_X_ASSUM ‘sigma_finite_measure_space (Y,B,v)’
      (STRIP_ASSUME_TAC o (REWRITE_RULE [sigma_finite_measure_space_def]))
 (* some shared properties *)
 >> Know ‘pos_fn_integral (Y,B,v)
            (\y. pos_fn_integral (X,A,u) (\x. (fn_plus f) (x,y))) <> PosInf’
 >- (REWRITE_TAC [lt_infty] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘pos_fn_integral (Y,B,v)
                     (\y. pos_fn_integral (X,A,u) (\x. (abs o f) (x,y)))’ \\
     reverse CONJ_TAC >- PROVE_TAC [lt_infty] \\
     Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_plus f) =
                    pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. (fn_plus f) (x,y)))’
       (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (abs o f) =
                    pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. (abs o f) (x,y)))’
       (ONCE_REWRITE_TAC o wrap o SYM) \\
     MATCH_MP_TAC pos_fn_integral_mono \\
     rw [FN_PLUS_POS, FN_PLUS_LE_ABS]) >> DISCH_TAC
 >> Know ‘pos_fn_integral (X,A,u)
            (\x. pos_fn_integral (Y,B,v) (\y. (fn_plus f) (x,y))) <> PosInf’
 >- (REWRITE_TAC [lt_infty] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘pos_fn_integral (X,A,u)
                     (\x. pos_fn_integral (Y,B,v) (\y. (abs o f) (x,y)))’ \\
     reverse CONJ_TAC >- PROVE_TAC [lt_infty] \\
     Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_plus f) =
                    pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. (fn_plus f) (x,y)))’
       (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (abs o f) =
                    pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. (abs o f) (x,y)))’
       (ONCE_REWRITE_TAC o wrap o SYM) \\
     MATCH_MP_TAC pos_fn_integral_mono \\
     rw [FN_PLUS_POS, FN_PLUS_LE_ABS]) >> DISCH_TAC
 >> Know ‘pos_fn_integral (Y,B,v)
            (\y. pos_fn_integral (X,A,u) (\x. (fn_minus f) (x,y))) <> PosInf’
 >- (REWRITE_TAC [lt_infty] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘pos_fn_integral (Y,B,v)
                     (\y. pos_fn_integral (X,A,u) (\x. (abs o f) (x,y)))’ \\
     reverse CONJ_TAC >- PROVE_TAC [lt_infty] \\
     Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_minus f) =
                    pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. (fn_minus f) (x,y)))’
       (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (abs o f) =
                    pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. (abs o f) (x,y)))’
       (ONCE_REWRITE_TAC o wrap o SYM) \\
     MATCH_MP_TAC pos_fn_integral_mono \\
     rw [FN_MINUS_POS, FN_MINUS_LE_ABS]) >> DISCH_TAC
 >> Know ‘pos_fn_integral (X,A,u)
            (\x. pos_fn_integral (Y,B,v) (\y. (fn_minus f) (x,y))) <> PosInf’
 >- (REWRITE_TAC [lt_infty] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘pos_fn_integral (X,A,u)
                     (\x. pos_fn_integral (Y,B,v) (\y. (abs o f) (x,y)))’ \\
     reverse CONJ_TAC >- PROVE_TAC [lt_infty] \\
     Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_minus f) =
                    pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. (fn_minus f) (x,y)))’
       (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (abs o f) =
                    pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. (abs o f) (x,y)))’
       (ONCE_REWRITE_TAC o wrap o SYM) \\
     MATCH_MP_TAC pos_fn_integral_mono \\
     rw [FN_MINUS_POS, FN_MINUS_LE_ABS]) >> DISCH_TAC
 (* clean up useless assumptions *)
 >> Q.PAT_X_ASSUM ‘sigma_finite (X,A,u)’ K_TAC
 >> Q.PAT_X_ASSUM ‘sigma_finite (Y,B,v)’ K_TAC
 (* push ‘fn_plus/fn_minus’ inside *)
 >> ‘!y. fn_plus (\x. f (x,y)) = (\x. (fn_plus f) (x,y))’   by rw [FUN_EQ_THM, FN_PLUS_ALT]
 >> ‘!y. fn_minus (\x. f (x,y)) = (\x. (fn_minus f) (x,y))’ by rw [FUN_EQ_THM, FN_MINUS_ALT]
 >> ‘!x. fn_plus (\y. f (x,y)) = (\y. (fn_plus f) (x,y))’   by rw [FUN_EQ_THM, FN_PLUS_ALT]
 >> ‘!x. fn_minus (\y. f (x,y)) = (\y. (fn_minus f) (x,y))’ by rw [FUN_EQ_THM, FN_MINUS_ALT]
 (* goal: AE y::(Y,B,v). integrable (X,A,u) (\x. f (x,y)) *)
 >> STRONG_CONJ_TAC
 >- (rw [Once FN_DECOMP, integrable_def] \\
  (* applying pos_fn_integral_infty_null *)
     Know ‘null_set (Y,B,v) {y | y IN m_space (Y,B,v) /\
                                 ((\y. pos_fn_integral (X,A,u) (\x. (fn_plus f) (x,y))) y = PosInf)}’
     >- (MATCH_MP_TAC pos_fn_integral_infty_null >> simp [] \\
         Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
         MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_PLUS_POS]) \\
     simp [] >> DISCH_TAC \\
     Know ‘null_set (Y,B,v) {y | y IN m_space (Y,B,v) /\
                                 ((\y. pos_fn_integral (X,A,u) (\x. (fn_minus f) (x,y))) y = PosInf)}’
     >- (MATCH_MP_TAC pos_fn_integral_infty_null >> simp [] \\
         Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
         MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_MINUS_POS]) \\
     simp [] >> DISCH_TAC \\
     rw [AE_DEF] \\
     Q.EXISTS_TAC ‘{y | y IN Y /\ pos_fn_integral (X,A,u) (\x. (fn_plus f) (x,y)) = PosInf} UNION
                   {y | y IN Y /\ pos_fn_integral (X,A,u) (\x. (fn_minus f) (x,y)) = PosInf}’ \\
     CONJ_TAC >- PROVE_TAC [NULL_SET_UNION'] \\
     Q.X_GEN_TAC ‘y’ >> rw [] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
      ‘!x. (fn_plus f) (x,y) - (fn_minus f) (x,y) = f (x,y)’
          by METIS_TAC [FN_DECOMP] >> POP_ORW \\
      ‘sigma_algebra (X,A)’ by fs [measure_space_def] \\
       simp [Once IN_MEASURABLE_BOREL_PLUS_MINUS],
       (* goal 2 (of 3) *)
       CCONTR_TAC >> FULL_SIMP_TAC std_ss [],
       (* goal 3 (of 3) *)
       CCONTR_TAC >> FULL_SIMP_TAC std_ss [] ]) >> DISCH_TAC
 (* goal: AE x::(X,A,u). integrable (Y,B,v) (\y. f (x,y)) *)
 >> STRONG_CONJ_TAC
 >- (rw [Once FN_DECOMP, integrable_def] \\
  (* applying pos_fn_integral_infty_null *)
     Know ‘null_set (X,A,u) {x | x IN m_space (X,A,u) /\
                                 ((\x. pos_fn_integral (Y,B,v) (\y. (fn_plus f) (x,y))) x = PosInf)}’
     >- (MATCH_MP_TAC pos_fn_integral_infty_null >> simp [] \\
         Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
         MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_PLUS_POS]) \\
     simp [] >> DISCH_TAC \\
     Know ‘null_set (X,A,u) {x | x IN m_space (X,A,u) /\
                                 ((\x. pos_fn_integral (Y,B,v) (\y. (fn_minus f) (x,y))) x = PosInf)}’
     >- (MATCH_MP_TAC pos_fn_integral_infty_null >> simp [] \\
         Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
         MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_MINUS_POS]) \\
     simp [] >> DISCH_TAC \\
     rw [AE_DEF] \\
     Q.EXISTS_TAC ‘{x | x IN X /\ pos_fn_integral (Y,B,v) (\y. (fn_plus f) (x,y)) = PosInf} UNION
                   {x | x IN X /\ pos_fn_integral (Y,B,v) (\y. (fn_minus f) (x,y)) = PosInf}’ \\
     CONJ_TAC >- PROVE_TAC [NULL_SET_UNION'] \\
     Q.X_GEN_TAC ‘x’ >> rw [] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
      ‘!y. (fn_plus f) (x,y) - (fn_minus f) (x,y) = f (x,y)’
          by METIS_TAC [FN_DECOMP] >> POP_ORW \\
      ‘sigma_algebra (Y,B)’ by fs [measure_space_def] \\
       simp [Once IN_MEASURABLE_BOREL_PLUS_MINUS],
       (* goal 2 (of 3) *)
       CCONTR_TAC >> FULL_SIMP_TAC std_ss [],
       (* goal 3 (of 3) *)
       CCONTR_TAC >> FULL_SIMP_TAC std_ss [] ]) >> DISCH_TAC
 (* goal: integrable (X,A,u) (\x. integral (Y,B,v) (\y. f (x,y))) *)
 >> STRONG_CONJ_TAC
 >- (rw [integrable_def] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                  (Q.SPEC ‘(X,A,u)’ IN_MEASURABLE_BOREL_EQ)) \\
       Q.EXISTS_TAC ‘\x. pos_fn_integral (Y,B,v) (\y. fn_plus f (x,y)) -
                         pos_fn_integral (Y,B,v) (\y. fn_minus f (x,y))’ >> BETA_TAC \\
       CONJ_TAC >- RW_TAC std_ss [integral_def] \\
       MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB' \\
       FULL_SIMP_TAC std_ss [measure_space_def, space_def, m_space_def, measurable_sets_def] \\
       qexistsl_tac [‘\x. pos_fn_integral (Y,B,v) (\y. fn_plus f (x,y))’,
                     ‘\x. pos_fn_integral (Y,B,v) (\y. fn_minus f (x,y))’] \\
       simp [],
       (* goal 2 (of 3) *)
       REWRITE_TAC [lt_infty] >> MATCH_MP_TAC let_trans \\
       Q.EXISTS_TAC ‘pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. (abs o f) (x,y)))’ \\
       reverse CONJ_TAC >- art [GSYM lt_infty] \\
       MATCH_MP_TAC pos_fn_integral_mono_AE >> rw [FN_PLUS_POS]
       >- (MATCH_MP_TAC pos_fn_integral_pos >> rw [abs_pos]) \\
       Q.PAT_X_ASSUM ‘AE x::(X,A,u). integrable (Y,B,v) (\y. f (x,y))’ MP_TAC \\
       rw [AE_DEF] \\
       Q.EXISTS_TAC ‘N’ >> rw [] \\
       MATCH_MP_TAC le_trans \\
       Q.EXISTS_TAC ‘abs ((\x. integral (Y,B,v) (\y. f (x,y))) x)’ \\
       CONJ_TAC >- REWRITE_TAC [FN_PLUS_LE_ABS] >> BETA_TAC \\
       MP_TAC (Q.SPECL [‘(Y,B,v)’, ‘(\y. f (x,y))’]
                       (INST_TYPE [alpha |-> beta] integral_triangle_ineq')) \\
       simp [o_DEF],
       (* goal 3 (of 3) *)
       REWRITE_TAC [lt_infty] >> MATCH_MP_TAC let_trans \\
       Q.EXISTS_TAC ‘pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. (abs o f) (x,y)))’ \\
       reverse CONJ_TAC >- art [GSYM lt_infty] \\
       MATCH_MP_TAC pos_fn_integral_mono_AE >> rw [FN_MINUS_POS]
       >- (MATCH_MP_TAC pos_fn_integral_pos >> rw [abs_pos]) \\
       Q.PAT_X_ASSUM ‘AE x::(X,A,u). integrable (Y,B,v) (\y. f (x,y))’ MP_TAC \\
       rw [AE_DEF] \\
       Q.EXISTS_TAC ‘N’ >> rw [] \\
       MATCH_MP_TAC le_trans \\
       Q.EXISTS_TAC ‘abs ((\x. integral (Y,B,v) (\y. f (x,y))) x)’ \\
       CONJ_TAC >- REWRITE_TAC [FN_MINUS_LE_ABS] >> BETA_TAC \\
       MP_TAC (Q.SPECL [‘(Y,B,v)’, ‘(\y. f (x,y))’]
                       (INST_TYPE [alpha |-> beta] integral_triangle_ineq')) \\
       simp [o_DEF] ])
 >> DISCH_TAC
 (* goal: integrable (Y,B,v) (\y. integral (X,A,u) (\y. f (x,y))) *)
 >> STRONG_CONJ_TAC
 >- (rw [integrable_def] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                  (ISPEC “(Y,B,v) :'b m_space” IN_MEASURABLE_BOREL_EQ)) \\
       Q.EXISTS_TAC ‘\y. pos_fn_integral (X,A,u) (\x. fn_plus f (x,y)) -
                         pos_fn_integral (X,A,u) (\x. fn_minus f (x,y))’ >> BETA_TAC \\
       CONJ_TAC >- RW_TAC std_ss [integral_def] \\
       MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB' \\
       FULL_SIMP_TAC std_ss [measure_space_def, space_def, m_space_def, measurable_sets_def] \\
       qexistsl_tac [‘\y. pos_fn_integral (X,A,u) (\x. fn_plus f (x,y))’,
                     ‘\y. pos_fn_integral (X,A,u) (\x. fn_minus f (x,y))’] \\
       simp [],
       (* goal 2 (of 3) *)
       REWRITE_TAC [lt_infty] >> MATCH_MP_TAC let_trans \\
       Q.EXISTS_TAC ‘pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. (abs o f) (x,y)))’ \\
       reverse CONJ_TAC >- art [GSYM lt_infty] \\
       MATCH_MP_TAC pos_fn_integral_mono_AE >> rw [FN_PLUS_POS]
       >- (MATCH_MP_TAC pos_fn_integral_pos >> rw [abs_pos]) \\
       Q.PAT_X_ASSUM ‘AE y::(Y,B,v). integrable (X,A,u) (\x. f (x,y))’ MP_TAC \\
       rw [AE_DEF] \\
       Q.EXISTS_TAC ‘N’ >> rw [] >> rename1 ‘y IN Y’ \\
       MATCH_MP_TAC le_trans \\
       Q.EXISTS_TAC ‘abs ((\y. integral (X,A,u) (\x. f (x,y))) y)’ \\
       CONJ_TAC >- REWRITE_TAC [FN_PLUS_LE_ABS] >> BETA_TAC \\
       MP_TAC (Q.SPECL [‘(X,A,u)’, ‘(\x. f (x,y))’] integral_triangle_ineq') \\
       simp [o_DEF],
       (* goal 3 (of 3) *)
       REWRITE_TAC [lt_infty] >> MATCH_MP_TAC let_trans \\
       Q.EXISTS_TAC ‘pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. (abs o f) (x,y)))’ \\
       reverse CONJ_TAC >- art [GSYM lt_infty] \\
       MATCH_MP_TAC pos_fn_integral_mono_AE >> rw [FN_MINUS_POS]
       >- (MATCH_MP_TAC pos_fn_integral_pos >> rw [abs_pos]) \\
       Q.PAT_X_ASSUM ‘AE y::(Y,B,v). integrable (X,A,u) (\x. f (x,y))’ MP_TAC \\
       rw [AE_DEF] \\
       Q.EXISTS_TAC ‘N’ >> rw [] >> rename1 ‘y IN Y’ \\
       MATCH_MP_TAC le_trans \\
       Q.EXISTS_TAC ‘abs ((\y. integral (X,A,u) (\x. f (x,y))) y)’ \\
       CONJ_TAC >- REWRITE_TAC [FN_MINUS_LE_ABS] >> BETA_TAC \\
       MP_TAC (Q.SPECL [‘(X,A,u)’, ‘(\x. f (x,y))’] integral_triangle_ineq') \\
       simp [o_DEF] ])
 >> DISCH_TAC
 (* final goals *)
 >> CONJ_TAC
 >| [ (* goal 1 (of 2) *)
      GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [integral_def] \\
      Know ‘integral (Y,B,v) (\y. integral (X,A,u) (\x. f (x,y))) =
            integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. fn_plus f (x,y)) -
                                  pos_fn_integral (X,A,u) (\x. fn_minus f (x,y)))’
      >- (MATCH_MP_TAC integral_cong >> simp [] \\
          Q.X_GEN_TAC ‘y’ >> rw [integral_def]) >> Rewr' \\
      Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_plus f) =
                     pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. fn_plus f (x,y)))’
          (ONCE_REWRITE_TAC o wrap) \\
      Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_minus f) =
                     pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. fn_minus f (x,y)))’
          (ONCE_REWRITE_TAC o wrap) \\
      MATCH_MP_TAC EQ_SYM \\
      MATCH_MP_TAC integral_add_lemma' >> rw [] >| (* 5 subgoals *)
      [ (* goal 1.1 (of 5) *)
        MATCH_MP_TAC integrable_eq >> simp [] \\
        Q.EXISTS_TAC ‘\y. integral (X,A,u) (\x. f (x,y))’ >> simp [integral_def],
        (* goal 1.2 (of 5) *)
        Q.ABBREV_TAC ‘g = \y. pos_fn_integral (X,A,u) (\x. fn_plus f (x,y))’ \\
        Know ‘integrable (Y,B,v) g <=>
              g IN Borel_measurable (Y,B) /\ pos_fn_integral (Y,B,v) g <> PosInf’
        >- (MATCH_MP_TAC
              (REWRITE_RULE [m_space_def, measurable_sets_def]
                            (Q.SPEC ‘(Y,B,v)’ (INST_TYPE [alpha |-> beta] integrable_pos))) \\
            rw [Abbr ‘g’] \\
            MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_PLUS_POS]) >> Rewr' \\
        Q.UNABBREV_TAC ‘g’ >> art [],
        (* goal 1.3 (of 5) *)
        Q.ABBREV_TAC ‘g = \y. pos_fn_integral (X,A,u) (\x. fn_minus f (x,y))’ \\
        Know ‘integrable (Y,B,v) g <=>
              g IN Borel_measurable (Y,B) /\ pos_fn_integral (Y,B,v) g <> PosInf’
        >- (MATCH_MP_TAC
              (REWRITE_RULE [m_space_def, measurable_sets_def]
                            (Q.SPEC ‘(Y,B,v)’ (INST_TYPE [alpha |-> beta] integrable_pos))) \\
            rw [Abbr ‘g’] \\
            MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_MINUS_POS]) >> Rewr' \\
        Q.UNABBREV_TAC ‘g’ >> art [],
        (* goal 1.4 (of 5) *)
        MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_PLUS_POS],
        (* goal 1.5 (of 5) *)
        MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_MINUS_POS] ],
      (* goal 2 (of 2) *)
      GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [integral_def] \\
      Know ‘integral (X,A,u) (\x. integral (Y,B,v) (\y. f (x,y))) =
            integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. fn_plus f (x,y)) -
                                  pos_fn_integral (Y,B,v) (\y. fn_minus f (x,y)))’
      >- (MATCH_MP_TAC integral_cong >> simp [] \\
          Q.X_GEN_TAC ‘x’ >> rw [integral_def]) >> Rewr' \\
      Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_plus f) =
                     pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. fn_plus f (x,y)))’
          (ONCE_REWRITE_TAC o wrap) \\
      Q.PAT_X_ASSUM ‘pos_fn_integral ((X,A,u) CROSS (Y,B,v)) (fn_minus f) =
                     pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. fn_minus f (x,y)))’
          (ONCE_REWRITE_TAC o wrap) \\
      MATCH_MP_TAC EQ_SYM \\
      MATCH_MP_TAC integral_add_lemma' >> rw [] >| (* 5 subgoals *)
      [ (* goal 2.1 (of 5) *)
        MATCH_MP_TAC integrable_eq >> simp [] \\
        Q.EXISTS_TAC ‘\x. integral (Y,B,v) (\y. f (x,y))’ >> simp [integral_def],
        (* goal 2.2 (of 5) *)
        Q.ABBREV_TAC ‘g = \x. pos_fn_integral (Y,B,v) (\y. fn_plus f (x,y))’ \\
        Know ‘integrable (X,A,u) g <=>
              g IN Borel_measurable (X,A) /\ pos_fn_integral (X,A,u) g <> PosInf’
        >- (MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                       (Q.SPEC ‘(X,A,u)’ integrable_pos)) \\
            rw [Abbr ‘g’] \\
            MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_PLUS_POS]) >> Rewr' \\
        Q.UNABBREV_TAC ‘g’ >> art [],
        (* goal 2.3 (of 5) *)
        Q.ABBREV_TAC ‘g = \x. pos_fn_integral (Y,B,v) (\y. fn_minus f (x,y))’ \\
        Know ‘integrable (X,A,u) g <=>
              g IN Borel_measurable (X,A) /\ pos_fn_integral (X,A,u) g <> PosInf’
        >- (MATCH_MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def]
                                       (Q.SPEC ‘(X,A,u)’ integrable_pos)) \\
            rw [Abbr ‘g’] \\
            MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_MINUS_POS]) >> Rewr' \\
        Q.UNABBREV_TAC ‘g’ >> art [],
        (* goal 2.4 (of 5) *)
        MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_PLUS_POS],
        (* goal 2.5 (of 5) *)
        MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_MINUS_POS] ] ]
QED

(* another form without using ‘pos_fn_integral’ *)
Theorem FUBINI' :
    !(X :'a set) (Y :'b set) A B u v f.
        sigma_finite_measure_space (X,A,u) /\
        sigma_finite_measure_space (Y,B,v) /\
        f IN measurable ((X,A) CROSS (Y,B)) Borel /\
     (* if at least one of the three integrals is finite (P \/ Q \/ R) *)
       (integral ((X,A,u) CROSS (Y,B,v)) (abs o f) <> PosInf \/
        integral (Y,B,v) (\y. integral (X,A,u) (\x. (abs o f) (x,y))) <> PosInf \/
        integral (X,A,u) (\x. integral (Y,B,v) (\y. (abs o f) (x,y))) <> PosInf)
       ==>
     (* then all three integrals are finite (P /\ Q /\ R) *)
        integral ((X,A,u) CROSS (Y,B,v)) (abs o f) <> PosInf /\
        integral (Y,B,v) (\y. integral (X,A,u) (\x. (abs o f) (x,y))) <> PosInf /\
        integral (X,A,u) (\x. integral (Y,B,v) (\y. (abs o f) (x,y))) <> PosInf /\
        integrable ((X,A,u) CROSS (Y,B,v)) f /\
       (AE y::(Y,B,v). integrable (X,A,u) (\x. f (x,y))) /\
       (AE x::(X,A,u). integrable (Y,B,v) (\y. f (x,y))) /\
        integrable (X,A,u) (\x. integral (Y,B,v) (\y. f (x,y))) /\
        integrable (Y,B,v) (\y. integral (X,A,u) (\x. f (x,y))) /\
       (integral ((X,A,u) CROSS (Y,B,v)) f =
        integral (Y,B,v) (\y. integral (X,A,u) (\x. f (x,y)))) /\
       (integral ((X,A,u) CROSS (Y,B,v)) f =
        integral (X,A,u) (\x. integral (Y,B,v) (\y. f (x,y))))
Proof
    rpt GEN_TAC
 (* prevent from separating ‘P \/ Q \/ R’ *)
 >> REWRITE_TAC [DECIDE “(A /\ B /\ C /\ D ==> E) <=>
                         (A ==> B ==> C ==> D ==> E)”]
 >> rpt DISCH_TAC
 >> ASSUME_TAC (Q.SPECL [‘X’, ‘Y’, ‘A’, ‘B’, ‘u’, ‘v’, ‘f’] FUBINI)
 >> ‘measure_space ((X,A,u) CROSS (Y,B,v))’
      by METIS_TAC [measure_space_prod_measure]
 >> ‘measure_space (X,A,u) /\ measure_space (Y,B,v)’
      by METIS_TAC [sigma_finite_measure_space_def]
 >> Q.PAT_X_ASSUM ‘P \/ Q \/ R’ MP_TAC
 >> Know ‘integral ((X,A,u) CROSS (Y,B,v)) (abs o f) = pos_fn_integral
                   ((X,A,u) CROSS (Y,B,v)) (abs o f)’
 >- (MATCH_MP_TAC integral_pos_fn >> rw [abs_pos])
 >> Rewr'
 >> Know ‘integral (Y,B,v) (\y. integral (X,A,u) (\x. (abs o f) (x,y))) =
          pos_fn_integral (Y,B,v) (\y. integral (X,A,u) (\x. (abs o f) (x,y)))’
 >- (MATCH_MP_TAC integral_pos_fn >> rw [] \\
     MATCH_MP_TAC integral_pos >> rw [abs_pos])
 >> Rewr'
 >> Know ‘pos_fn_integral (Y,B,v) (\y. integral (X,A,u) (\x. (abs o f) (x,y))) =
          pos_fn_integral (Y,B,v) (\y. pos_fn_integral (X,A,u) (\x. (abs o f) (x,y)))’
 >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
     CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                  MATCH_MP_TAC integral_pos >> rw [abs_pos]) \\
     CONJ_TAC >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
                  MATCH_MP_TAC pos_fn_integral_pos >> rw [abs_pos]) \\
     Q.X_GEN_TAC ‘y’ >> DISCH_TAC \\
     MATCH_MP_TAC integral_pos_fn >> rw [abs_pos])
 >> Rewr'
 >> Know ‘integral (X,A,u) (\x. integral (Y,B,v) (\y. (abs o f) (x,y))) =
          pos_fn_integral (X,A,u) (\x. integral (Y,B,v) (\y. (abs o f) (x,y)))’
 >- (MATCH_MP_TAC integral_pos_fn >> rw [] \\
     MATCH_MP_TAC integral_pos >> rw [abs_pos])
 >> Rewr'
 >> Know ‘pos_fn_integral (X,A,u) (\x. integral (Y,B,v) (\y. (abs o f) (x,y))) =
          pos_fn_integral (X,A,u) (\x. pos_fn_integral (Y,B,v) (\y. (abs o f) (x,y)))’
 >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
     CONJ_TAC >- (Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
                  MATCH_MP_TAC integral_pos >> rw [abs_pos]) \\
     CONJ_TAC >- (Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
                  MATCH_MP_TAC pos_fn_integral_pos >> rw [abs_pos]) \\
     Q.X_GEN_TAC ‘x’ >> DISCH_TAC \\
     MATCH_MP_TAC integral_pos_fn >> rw [abs_pos])
 >> Rewr'
 >> METIS_TAC []
QED

(* More compact forms of FUBINI and FUBINI' *)
Theorem Fubini = FUBINI
 |> (Q.SPECL [‘m_space m1’, ‘m_space m2’, ‘measurable_sets m1’, ‘measurable_sets m2’,
              ‘measure m1’, ‘measure m2’])
 |> (REWRITE_RULE [MEASURE_SPACE_REDUCE])
 |> (Q.GENL [‘m1’, ‘m2’]);

Theorem Fubini' = FUBINI'
 |> (Q.SPECL [‘m_space m1’, ‘m_space m2’, ‘measurable_sets m1’, ‘measurable_sets m2’,
              ‘measure m1’, ‘measure m2’])
 |> (REWRITE_RULE [MEASURE_SPACE_REDUCE])
 |> (Q.GENL [‘m1’, ‘m2’]);

(* This theorem only needs TONELLI *)
Theorem IN_MEASURABLE_BOREL_FROM_PROD_SIGMA :
    !X Y A B f. sigma_algebra (X,A) /\ sigma_algebra (Y,B) /\
                f IN measurable ((X,A) CROSS (Y,B)) Borel ==>
               (!y. y IN Y ==> (\x. f (x,y)) IN measurable (X,A) Borel) /\
               (!x. x IN X ==> (\y. f (x,y)) IN measurable (Y,B) Borel)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘sigma_finite_measure_space (X,A,\s. 0) /\
     sigma_finite_measure_space (Y,B,\s. 0)’
      by METIS_TAC [measure_space_trivial, space_def, subsets_def]
 >> Know ‘sigma_algebra ((X,A) CROSS (Y,B))’
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_PROD_SIGMA' \\
     fs [sigma_algebra_def, algebra_def]) >> DISCH_TAC
 >> ‘(fn_plus f) IN measurable ((X,A) CROSS (Y,B)) Borel’
      by PROVE_TAC [IN_MEASURABLE_BOREL_FN_PLUS]
 >> ‘!s. s IN X CROSS Y ==> 0 <= (fn_plus f) s’ by rw [FN_PLUS_POS]
 >> Know ‘(!y. y IN Y ==> (\x. (fn_plus f) (x,y)) IN Borel_measurable (X,A)) /\
          (!x. x IN X ==> (\y. (fn_plus f) (x,y)) IN Borel_measurable (Y,B))’
 >- (MP_TAC (Q.SPECL [‘X’, ‘Y’, ‘A’, ‘B’, ‘\s. 0’, ‘\s. 0’, ‘fn_plus f’] TONELLI) \\
     RW_TAC std_ss []) >> STRIP_TAC
 >> ‘(fn_minus f) IN measurable ((X,A) CROSS (Y,B)) Borel’
      by PROVE_TAC [IN_MEASURABLE_BOREL_FN_MINUS]
 >> ‘!s. s IN X CROSS Y ==> 0 <= (fn_minus f) s’ by rw [FN_MINUS_POS]
 >> Know ‘(!y. y IN Y ==> (\x. (fn_minus f) (x,y)) IN Borel_measurable (X,A)) /\
          (!x. x IN X ==> (\y. (fn_minus f) (x,y)) IN Borel_measurable (Y,B))’
 >- (MP_TAC (Q.SPECL [‘X’, ‘Y’, ‘A’, ‘B’, ‘\s. 0’, ‘\s. 0’, ‘fn_minus f’] TONELLI) \\
     RW_TAC std_ss []) >> STRIP_TAC
 (* push ‘fn_plus/fn_minus’ inside *)
 >> ‘!y. fn_plus (\x. f (x,y)) = (\x. (fn_plus f) (x,y))’   by rw [FUN_EQ_THM, FN_PLUS_ALT]
 >> ‘!y. fn_minus (\x. f (x,y)) = (\x. (fn_minus f) (x,y))’ by rw [FUN_EQ_THM, FN_MINUS_ALT]
 >> ‘!x. fn_plus (\y. f (x,y)) = (\y. (fn_plus f) (x,y))’   by rw [FUN_EQ_THM, FN_PLUS_ALT]
 >> ‘!x. fn_minus (\y. f (x,y)) = (\y. (fn_minus f) (x,y))’ by rw [FUN_EQ_THM, FN_MINUS_ALT]
 (* final goals *)
 >> CONJ_TAC >> rpt STRIP_TAC
 >| [ ASM_SIMP_TAC std_ss
        [Once (MATCH_MP IN_MEASURABLE_BOREL_PLUS_MINUS
                        (ASSUME “sigma_algebra (X :'a set,A :'a set set)”))],
      ASM_SIMP_TAC std_ss
        [Once (MATCH_MP IN_MEASURABLE_BOREL_PLUS_MINUS
                        (ASSUME “sigma_algebra (Y :'b set,B :'b set set)”))] ]
QED

(* ------------------------------------------------------------------------- *)
(*  Filtration and basic version of martingales (Chapter 23 of [1])          *)
(* ------------------------------------------------------------------------- *)

(* ‘sub_sigma_algebra’ is a partial-order between sigma-algebra *)
val SUB_SIGMA_ALGEBRA_REFL = store_thm
  ("SUB_SIGMA_ALGEBRA_REFL",
  ``!a. sigma_algebra a ==> sub_sigma_algebra a a``,
    RW_TAC std_ss [sub_sigma_algebra_def, SUBSET_REFL]);

val SUB_SIGMA_ALGEBRA_TRANS = store_thm
  ("SUB_SIGMA_ALGEBRA_TRANS",
  ``!a b c. sub_sigma_algebra a b /\ sub_sigma_algebra b c ==> sub_sigma_algebra a c``,
    RW_TAC std_ss [sub_sigma_algebra_def]
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC `subsets b` >> art []);

val SUB_SIGMA_ALGEBRA_ANTISYM = store_thm
  ("SUB_SIGMA_ALGEBRA_ANTISYM",
  ``!a b. sub_sigma_algebra a b /\ sub_sigma_algebra b a ==> (a = b)``,
    RW_TAC std_ss [sub_sigma_algebra_def]
 >> Q.PAT_X_ASSUM `space b = space a` K_TAC
 >> ONCE_REWRITE_TAC [GSYM SPACE]
 >> ASM_REWRITE_TAC [CLOSED_PAIR_EQ]
 >> MATCH_MP_TAC SUBSET_ANTISYM >> art []);

val SUB_SIGMA_ALGEBRA_ORDER = store_thm
  ("SUB_SIGMA_ALGEBRA_ORDER", ``Order sub_sigma_algebra``,
    RW_TAC std_ss [Order, antisymmetric_def, transitive_def]
 >- (MATCH_MP_TAC SUB_SIGMA_ALGEBRA_ANTISYM >> art [])
 >> IMP_RES_TAC SUB_SIGMA_ALGEBRA_TRANS);

(* Another form of measureTheory.MEASURE_SPACE_RESTRICTION *)
val SUB_SIGMA_ALGEBRA_MEASURE_SPACE = store_thm
  ("SUB_SIGMA_ALGEBRA_MEASURE_SPACE",
  ``!m a. measure_space m /\ sub_sigma_algebra a (m_space m,measurable_sets m) ==>
          measure_space (m_space m,subsets a,measure m)``,
    RW_TAC std_ss [sub_sigma_algebra_def, space_def, subsets_def]
 >> MATCH_MP_TAC MEASURE_SPACE_RESTRICTION
 >> Q.EXISTS_TAC `measurable_sets m`
 >> simp [MEASURE_SPACE_REDUCE]
 >> METIS_TAC [SPACE]);

val FILTRATION_BOUNDED = store_thm
  ("FILTRATION_BOUNDED",
  ``!A a. filtration A a ==> !n. sub_sigma_algebra (a n) A``,
    PROVE_TAC [filtration_def]);

val FILTRATION_MONO = store_thm
  ("FILTRATION_MONO",
  ``!A a. filtration A a ==> !i j. i <= j ==> subsets (a i) SUBSET subsets (a j)``,
    PROVE_TAC [filtration_def]);

(* all sigma-algebras in `filtration A` are subset of A *)
val FILTRATION_SUBSETS = store_thm
  ("FILTRATION_SUBSETS",
  ``!A a. filtration A a ==> !n. subsets (a n) SUBSET (subsets A)``,
    RW_TAC std_ss [filtration_def, sub_sigma_algebra_def]);

val FILTRATION = store_thm
  ("FILTRATION",
  ``!A a. filtration A a <=> (!n. sub_sigma_algebra (a n) A) /\
                             (!n. subsets (a n) SUBSET (subsets A)) /\
                             (!i j. i <= j ==> subsets (a i) SUBSET subsets (a j))``,
    rpt GEN_TAC >> EQ_TAC
 >- (DISCH_TAC >> IMP_RES_TAC FILTRATION_SUBSETS >> fs [filtration_def])
 >> RW_TAC std_ss [filtration_def]);

(* all sub measure spaces of a sigma-finite fms are also sigma-finite *)
Theorem SIGMA_FINITE_FILTERED_MEASURE_SPACE :
    !m a. sigma_finite_filtered_measure_space m a ==>
          !n. sigma_finite (m_space m,subsets (a n),measure m)
Proof
    RW_TAC std_ss [sigma_finite_filtered_measure_space_def,
                   filtered_measure_space_def, filtration_def]
 >> Know ‘measure_space (m_space m,subsets (a 0),measure m) /\
          measure_space (m_space m,subsets (a n),measure m)’
 >- (CONJ_TAC \\ (* 2 subgoals, same tactics *)
     MATCH_MP_TAC (Q.SPEC ‘m’ SUB_SIGMA_ALGEBRA_MEASURE_SPACE) >> art [])
 >> STRIP_TAC
 >> POP_ASSUM (simp o wrap o (MATCH_MP SIGMA_FINITE_ALT))
 >> POP_ASSUM (fs o wrap o (MATCH_MP SIGMA_FINITE_ALT))
 >> Q.EXISTS_TAC ‘f’
 >> fs [IN_FUNSET, measurable_sets_def, m_space_def, measure_def]
 >> ‘0 <= n’ by rw []
 >> METIS_TAC [SUBSET_DEF]
QED

Theorem sigma_finite_filtered_measure_space_alt =
    REWRITE_RULE [filtered_measure_space_def]
                 sigma_finite_filtered_measure_space_def

Theorem sigma_finite_filtered_measure_space_alt_all :
    !m a. sigma_finite_filtered_measure_space m a <=>
          measure_space m /\ filtration (m_space m,measurable_sets m) a /\
          !n. sigma_finite (m_space m,subsets (a n),measure m)
Proof
    rpt GEN_TAC
 >> reverse EQ_TAC
 >- rw [sigma_finite_filtered_measure_space_alt]
 >> DISCH_TAC
 >> IMP_RES_TAC SIGMA_FINITE_FILTERED_MEASURE_SPACE
 >> fs [sigma_finite_filtered_measure_space_alt]
QED

(* the smallest sigma-algebra generated by all (a n) *)
val infty_sigma_algebra_def = Define
   `infty_sigma_algebra sp a =
      sigma sp (BIGUNION (IMAGE (\(i :num). subsets (a i)) UNIV))`;

val INFTY_SIGMA_ALGEBRA_BOUNDED = store_thm
  ("INFTY_SIGMA_ALGEBRA_BOUNDED",
  ``!A a. filtration A a ==>
          sub_sigma_algebra (infty_sigma_algebra (space A) a) A``,
    RW_TAC std_ss [sub_sigma_algebra_def, FILTRATION, infty_sigma_algebra_def]
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
     RW_TAC std_ss [subset_class_def, IN_BIGUNION_IMAGE, IN_UNIV] \\
    `x IN subsets A` by PROVE_TAC [SUBSET_DEF] \\
     METIS_TAC [sigma_algebra_def, algebra_def, subset_class_def, space_def, subsets_def])
 >- REWRITE_TAC [SPACE_SIGMA]
 >> MATCH_MP_TAC SIGMA_SUBSET >> art []
 >> RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_UNIV]
 >> PROVE_TAC [SUBSET_DEF]);

val INFTY_SIGMA_ALGEBRA_MAXIMAL = store_thm
  ("INFTY_SIGMA_ALGEBRA_MAXIMAL",
  ``!A a. filtration A a ==> !n. sub_sigma_algebra (a n) (infty_sigma_algebra (space A) a)``,
 (* proof *)
    RW_TAC std_ss [sub_sigma_algebra_def, FILTRATION, infty_sigma_algebra_def]
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
     RW_TAC std_ss [subset_class_def, IN_BIGUNION_IMAGE, IN_UNIV] \\
    `x IN subsets A` by PROVE_TAC [SUBSET_DEF] \\
     METIS_TAC [sigma_algebra_def, algebra_def, subset_class_def, space_def, subsets_def])
 >- REWRITE_TAC [SPACE_SIGMA]
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC `BIGUNION (IMAGE (\i. subsets (a i)) univ(:num))`
 >> CONJ_TAC
 >- (RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_UNIV] \\
     Q.EXISTS_TAC `n` >> art [])
 >> REWRITE_TAC [SIGMA_SUBSET_SUBSETS]);

(* A construction of sigma-filteration from only measurable functions *)
Theorem filtration_from_measurable_functions :
    !m X A. measure_space m /\
           (!n. X n IN Borel_measurable (measurable_space m)) /\
           (!n. A n = sigma (m_space m) (\n. Borel) X (count1 n)) ==>
            filtration (measurable_space m) A
Proof
    rw [filtration_def]
 >- (rw [sub_sigma_algebra_def, space_sigma_functions]
     >- (MATCH_MP_TAC sigma_algebra_sigma_functions \\
         rw [IN_FUNSET, SPACE_BOREL]) \\
     MATCH_MP_TAC (REWRITE_RULE [space_def, subsets_def]
                    (Q.ISPECL [‘measurable_space m’, ‘\n:num. Borel’]
                               sigma_functions_subset)) \\
     rw [MEASURE_SPACE_SIGMA_ALGEBRA, SIGMA_ALGEBRA_BOREL])
 (* stage work *)
 >> REWRITE_TAC [Once sigma_functions_def]
 >> Q.ABBREV_TAC ‘B = (sigma (m_space m) (\n. Borel) X (count1 j))’
 >> ‘m_space m = space B’ by METIS_TAC [space_sigma_functions]
 >> POP_ORW
 >> MATCH_MP_TAC SIGMA_SUBSET
 >> CONJ_ASM1_TAC
 >- (Q.UNABBREV_TAC ‘B’ \\
     MATCH_MP_TAC sigma_algebra_sigma_functions \\
     rw [IN_FUNSET, SPACE_BOREL])
 >> rw [SUBSET_DEF, IN_BIGUNION_IMAGE]
 >> rename1 ‘k < SUC i’
 >> rename1 ‘t IN subsets Borel’
 >> ‘k <= i’ by rw []
 >> ‘k <= j’ by rw []
 (* applying SIGMA_SIMULTANEOUSLY_MEASURABLE *)
 >> Suff ‘X k IN measurable B Borel’ >- rw [IN_MEASURABLE]
 >> MP_TAC (ISPECL [“m_space m”, “\n:num. Borel”, “X :num->'a->extreal”, “count1 j”]
                   SIGMA_SIMULTANEOUSLY_MEASURABLE)
 >> rw [SIGMA_ALGEBRA_BOREL, IN_FUNSET, SPACE_BOREL]
QED

(* ------------------------------------------------------------------------- *)
(*  Martingale alternative definitions and properties (Chapter 23 of [1])    *)
(* ------------------------------------------------------------------------- *)

(* ‘u’ is a martingale if, and only if, it is both a sub- and a super-martingale

   This is Example 23.3 (i) [1, p.277]
 *)
Theorem MARTINGALE_EQ_SUB_SUPER :
    !m a u. martingale m a u <=> sub_martingale m a u /\ super_martingale m a u
Proof
    RW_TAC std_ss [martingale_def, sub_martingale_def, super_martingale_def]
 >> EQ_TAC >> RW_TAC std_ss [le_refl]
 >> ASM_SIMP_TAC std_ss [GSYM le_antisym]
QED

(* simple alternative definitions: ‘n < SUC n’ is replaced by ‘i <= j’ *)
val martingale_shared_tactics_1 =
    reverse EQ_TAC >- RW_TAC arith_ss []
 >> RW_TAC arith_ss [sigma_finite_filtered_measure_space_alt]
 >> Q.PAT_X_ASSUM ‘i <= j’ MP_TAC
 >> Induct_on ‘j - i’
 >- (RW_TAC arith_ss [] \\
    ‘j = i’ by RW_TAC arith_ss [] >> RW_TAC arith_ss [le_refl])
 >> RW_TAC arith_ss []
 >> ‘v = PRE j - i’ by RW_TAC arith_ss []
 >> ‘i < j /\ i <= PRE j’ by RW_TAC arith_ss []
 >> ‘SUC (PRE j) = j’ by RW_TAC arith_ss []
 >> ‘s IN subsets (a (PRE j))’ by METIS_TAC [FILTRATION_MONO, SUBSET_DEF]
 >> Q.PAT_X_ASSUM ‘!n s. s IN subsets (a n) ==> P’
     (MP_TAC o (Q.SPECL [‘PRE j’, ‘s’]))
 >> RW_TAC arith_ss [];

val martingale_shared_tactics_2 =
    MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC ‘integral m (\x. u (PRE j) x * indicator_fn s x)’
 >> POP_ASSUM (REWRITE_TAC o wrap)
 >> FIRST_X_ASSUM irule
 >> RW_TAC arith_ss [];

Theorem martingale_alt :
   !m a u.
      martingale m a u <=>
      sigma_finite_filtered_measure_space m a /\ (!n. integrable m (u n)) /\
      !i j s. i <= j /\ s IN subsets (a i) ==>
             (integral m (\x. u i x * indicator_fn s x) =
              integral m (\x. u j x * indicator_fn s x))
Proof
    RW_TAC std_ss [martingale_def]
 >> martingale_shared_tactics_1
QED

Theorem super_martingale_alt :
   !m a u.
      super_martingale m a u <=>
      sigma_finite_filtered_measure_space m a /\ (!n. integrable m (u n)) /\
      !i j s. i <= j /\ s IN subsets (a i) ==>
             (integral m (\x. u j x * indicator_fn s x) <=
              integral m (\x. u i x * indicator_fn s x))
Proof
    RW_TAC std_ss [super_martingale_def]
 >> martingale_shared_tactics_1
 >> martingale_shared_tactics_2
QED

Theorem sub_martingale_alt :
   !m a u.
      sub_martingale m a u <=>
      sigma_finite_filtered_measure_space m a /\ (!n. integrable m (u n)) /\
      !i j s. i <= j /\ s IN subsets (a i) ==>
             (integral m (\x. u i x * indicator_fn s x) <=
              integral m (\x. u j x * indicator_fn s x))
Proof
    RW_TAC std_ss [sub_martingale_def]
 >> martingale_shared_tactics_1
 >> martingale_shared_tactics_2
QED

(* Remark 23.2 [1, p.276]: we can replace the sigma-algebra (a n) with any
   INTER-stable generator (g n) of (a n) containing an exhausive sequence.

   NOTE: in typical applications, it's expected to have (g n) such that
  ‘!i j. i <= j ==> g i SUBSET g j’ and thus the exhausting sequence of (g 0)
   is also the exhausting sequence of all (g n).
 *)

val martingale_alt_generator_shared_tactics_1 =
    qx_genl_tac [‘m’, ‘a’, ‘u’, ‘G’]
 >> RW_TAC std_ss [sigma_finite_filtered_measure_space_alt,
                   filtered_measure_space_def,
                   martingale_alt, sub_martingale_alt, super_martingale_alt]
 >> EQ_TAC (* easy part first *)
 >- (RW_TAC std_ss [] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> rw [] \\
     Suff ‘(G i) SUBSET subsets (sigma (m_space m) (G i))’ >- METIS_TAC [SUBSET_DEF] \\
     REWRITE_TAC [SIGMA_SUBSET_SUBSETS])
 >> rw [sigma_finite_alt_exhausting_sequence, exhausting_sequence_def, IN_FUNSET]
 >- (fs [has_exhausting_sequence_def, IN_FUNSET, IN_UNIV] \\
     Q.PAT_X_ASSUM ‘!n. ?f. P’ (MP_TAC o (Q.SPEC ‘0’)) \\
     RW_TAC std_ss [] \\
     Q.EXISTS_TAC ‘f’ >> rw []
     >- (Suff ‘(G 0) SUBSET subsets (sigma (m_space m) (G 0))’
         >- METIS_TAC [SUBSET_DEF] \\
         REWRITE_TAC [SIGMA_SUBSET_SUBSETS]) \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘0’ >> art [])
 (* stage work *)
 >> FULL_SIMP_TAC std_ss [integral_def]
 >> Know ‘!n. subsets (a n) SUBSET (measurable_sets m)’
 >- (fs [filtration_def, sub_sigma_algebra_def])
 >> DISCH_TAC
 >> ‘!n s. s IN G n ==> s IN measurable_sets m’
      by METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF]
 >> Know ‘!n s. (\x. u n x * indicator_fn s x)^+ =
                (\x. fn_plus (u n) x * indicator_fn s x)’
 >- (rpt GEN_TAC >> ONCE_REWRITE_TAC [mul_comm] \\
     MATCH_MP_TAC FN_PLUS_FMUL >> rw [INDICATOR_FN_POS])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> Know ‘!n s. (\x. u n x * indicator_fn s x)^- =
                (\x. fn_minus (u n) x * indicator_fn s x)’
 >- (rpt GEN_TAC >> ONCE_REWRITE_TAC [mul_comm] \\
     MATCH_MP_TAC FN_MINUS_FMUL >> rw [INDICATOR_FN_POS])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 (* simplifications by abbreviations *)
 >> Q.ABBREV_TAC ‘A = \n s. pos_fn_integral m (\x. (u n)^+ x * indicator_fn s x)’
 >> Q.ABBREV_TAC ‘B = \n s. pos_fn_integral m (\x. (u n)^- x * indicator_fn s x)’
 >> FULL_SIMP_TAC std_ss []
 >> Know ‘!n s. 0 <= A n s /\ 0 <= B n s’
 >- (rw [Abbr ‘A’, Abbr ‘B’] \\
     MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
     MATCH_MP_TAC le_mul \\
     rw [FN_PLUS_POS, FN_MINUS_POS, INDICATOR_FN_POS])
 >> DISCH_TAC
 >> Know ‘!n s. A n s < PosInf /\ B n s < PosInf’
 >- (rw [Abbr ‘A’, Abbr ‘B’] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC let_trans \\
       Q.EXISTS_TAC ‘pos_fn_integral m (fn_plus (u n))’ \\
       reverse CONJ_TAC >- (REWRITE_TAC [GSYM lt_infty] \\
                            METIS_TAC [integrable_def]) \\
       MATCH_MP_TAC pos_fn_integral_mono >> rw []
       >- (MATCH_MP_TAC le_mul >> rw [FN_PLUS_POS, INDICATOR_FN_POS]) \\
       GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM mul_rone] \\
       MATCH_MP_TAC le_lmul_imp >> rw [FN_PLUS_POS, INDICATOR_FN_LE_1],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC let_trans \\
       Q.EXISTS_TAC ‘pos_fn_integral m (fn_minus (u n))’ \\
       reverse CONJ_TAC >- (REWRITE_TAC [GSYM lt_infty] \\
                            METIS_TAC [integrable_def]) \\
       MATCH_MP_TAC pos_fn_integral_mono >> rw []
       >- (MATCH_MP_TAC le_mul >> rw [FN_MINUS_POS, INDICATOR_FN_POS]) \\
       GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM mul_rone] \\
       MATCH_MP_TAC le_lmul_imp >> rw [FN_MINUS_POS, INDICATOR_FN_LE_1] ])
 >> DISCH_TAC;
 (* end of martingale_alt_generator_shared_tactics_1 *)

val martingale_alt_generator_shared_tactics_2 =
    Q.ABBREV_TAC ‘f = \i j x. fn_plus (u i) x + fn_minus (u j) x’
 >> Know ‘!i j s. s IN measurable_sets m ==> A i s + B j s = (f i j * m) s’
 >- (qx_genl_tac [‘k’, ‘n’, ‘t’] \\
     RW_TAC std_ss [Abbr ‘f’, Abbr ‘A’, Abbr ‘B’, density_measure_def] \\
     Know ‘pos_fn_integral m (\x. (u k)^+ x * indicator_fn t x) +
           pos_fn_integral m (\x. (u n)^- x * indicator_fn t x) =
           pos_fn_integral m (\x. (u k)^+ x * indicator_fn t x +
                                  (u n)^- x * indicator_fn t x)’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         HO_MATCH_MP_TAC pos_fn_integral_add >> rw [] >| (* 4 subgoals *)
         [ (* goal 1 (of 4) *)
           MATCH_MP_TAC le_mul >> rw [FN_PLUS_POS, INDICATOR_FN_POS],
           (* goal 2 (of 4) *)
           MATCH_MP_TAC le_mul >> rw [FN_MINUS_POS, INDICATOR_FN_POS],
           (* goal 3 (of 4) *)
           MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR >> rw [] \\
           MATCH_MP_TAC IN_MEASURABLE_BOREL_FN_PLUS \\
           FULL_SIMP_TAC std_ss [integrable_def, measure_space_def],
           (* goal 4 (of 4) *)
           MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR >> rw [] \\
           MATCH_MP_TAC IN_MEASURABLE_BOREL_FN_MINUS \\
           FULL_SIMP_TAC std_ss [integrable_def, measure_space_def] ]) >> Rewr' \\
     MATCH_MP_TAC pos_fn_integral_cong >> rw [] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       MATCH_MP_TAC le_add >> CONJ_TAC >> MATCH_MP_TAC le_mul \\
       rw [FN_PLUS_POS, FN_MINUS_POS, INDICATOR_FN_POS],
       (* goal 2 (of 3) *)
       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS] \\
       MATCH_MP_TAC le_add >> rw [FN_PLUS_POS, FN_MINUS_POS],
       (* goal 3 (of 3) *)
       rw [indicator_fn_def] ])
 >> DISCH_TAC
 >> ‘s IN measurable_sets m’ by METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF];
 (* end of martingale_alt_generator_shared_tactics_2 *)

val martingale_alt_generator_shared_tactics_3 =
    Know ‘!i j. measure_space (m_space m,measurable_sets m,f i j * m)’
 >- (qx_genl_tac [‘M’, ‘N’] \\
     MATCH_MP_TAC (REWRITE_RULE [density_def] measure_space_density) \\
     RW_TAC std_ss [Abbr ‘f’] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD' \\
       qexistsl_tac [‘fn_plus (u M)’, ‘fn_minus (u N)’] >> simp [] \\
       FULL_SIMP_TAC std_ss [integrable_def, measure_space_def] \\
       PROVE_TAC [IN_MEASURABLE_BOREL_FN_PLUS, IN_MEASURABLE_BOREL_FN_MINUS],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC le_add >> rw [FN_PLUS_POS, FN_MINUS_POS] ])
 >> DISCH_TAC;
(* end of martingale_alt_generator_shared_tactics_3 *)

val martingale_alt_generator_shared_tactics_4 =
    Suff ‘!i j n. measure_space (m_space m,subsets (sigma (m_space m) (G n)),f i j * m)’
 >- Rewr
 >> Q.PAT_X_ASSUM ‘i <= j’ K_TAC
 >> Q.PAT_X_ASSUM ‘s IN subsets (sigma (m_space m) (G i))’ K_TAC
 >> Q.PAT_X_ASSUM ‘s IN measurable_sets m’ K_TAC
 >> rpt GEN_TAC
 >> MATCH_MP_TAC MEASURE_SPACE_RESTRICTION
 >> Q.EXISTS_TAC ‘measurable_sets m’ >> art []
 >> CONJ_TAC >- PROVE_TAC [] (* sigma (G n) SUBSET measurable_sets m *)
 >> ‘(m_space m,subsets (sigma (m_space m) (G n))) = sigma (m_space m) (G n)’
       by METIS_TAC [SPACE, SPACE_SIGMA]
 >> POP_ORW
 >> MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA >> art [];
 (* end of martingale_alt_generator_shared_tactics_4 *)

Theorem martingale_alt_generator :
   !m a u g. (!n. a n = sigma (m_space m) (g n)) /\
             (!n. has_exhausting_sequence (m_space m,g n)) /\
             (!n s. s IN (g n) ==> measure m s < PosInf) /\
             (!n s t. s IN (g n) /\ t IN (g n) ==> s INTER t IN (g n)) ==>
     (martingale m a u <=>
      filtered_measure_space m a /\ (!n. integrable m (u n)) /\
      !i j s. i <= j /\ s IN (g i) ==>
             (integral m (\x. u i x * indicator_fn s x) =
              integral m (\x. u j x * indicator_fn s x)))
Proof
 (* expectations: ‘A i s - B i s = A j s - B j s’ *)
    martingale_alt_generator_shared_tactics_1
 (* stage work on transforming the goal into equivalence of two measures *)
 >> Know ‘!i j s. (A i s - B i s = A j s - B j s <=>
                   A i s + B j s = A j s + B i s)’
 >- (qx_genl_tac [‘M’, ‘N’, ‘t’] \\
    ‘A M t <> NegInf /\ A N t <> NegInf /\ B M t <> NegInf /\ B N t <> NegInf’
       by METIS_TAC [pos_not_neginf] \\
    ‘A M t <> PosInf /\ A N t <> PosInf /\ B M t <> PosInf /\ B N t <> PosInf’
       by METIS_TAC [lt_infty] \\
    ‘?r1. A M t = Normal r1’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?r2. A N t = Normal r2’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?r3. B M t = Normal r3’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?r4. B N t = Normal r4’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_add_def, extreal_sub_def, extreal_le_eq] >> REAL_ARITH_TAC)
 >> DISCH_THEN (FULL_SIMP_TAC pure_ss o wrap)
 (* applying density_measure_def *)
 >> martingale_alt_generator_shared_tactics_2
 (* final modification of the goal *)
 >> ‘A i s + B j s = A j s + B i s <=> (f i j * m) s = (f j i * m) s’
      by METIS_TAC [] >> POP_ORW
 (* final modification of the major assumption *)
 >> Know ‘!i j s. i <= j /\ s IN G i ==> (f i j * m) s = (f j i * m) s’
 >- (qx_genl_tac [‘k’, ‘n’, ‘t’] >> rpt STRIP_TAC \\
    ‘t IN measurable_sets m’ by PROVE_TAC [] \\
     METIS_TAC [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘!i j s. i <= j /\ s IN G i ==> A i s + B j s = A j s + B i s’ K_TAC
 (* applying measure_space_density, density_def *)
 >> martingale_alt_generator_shared_tactics_3
 (* applying UNIQUENESS_OF_MEASURE *)
 >> irule UNIQUENESS_OF_MEASURE
 >> qexistsl_tac [‘m_space m’, ‘G i’] >> simp []
 >> CONJ_TAC (* f i j * m = f j i * m *)
 >- (rpt STRIP_TAC >> FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> Know ‘!n. subset_class (m_space m) (G n)’
 >- (rw [subset_class_def] \\
    ‘x IN measurable_sets m’ by METIS_TAC [SUBSET_DEF] \\
     FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,
                           subset_class_def, space_def, subsets_def])
 >> DISCH_TAC
 (* easy goals first *)
 >> ASM_REWRITE_TAC [CONJ_ASSOC]
 >> reverse CONJ_TAC (* sigma_finite of G *)
 >- (Q.PAT_X_ASSUM ‘!n. has_exhausting_sequence (m_space m,G n)’ (MP_TAC o (Q.SPEC ‘i’)) \\
     rw [sigma_finite_def, has_exhausting_sequence_def, IN_FUNSET] \\
     rename1 ‘!x. g x IN G i’ >> Q.EXISTS_TAC ‘g’ >> rw [] \\
    ‘g n IN measurable_sets m’ by METIS_TAC [SUBSET_DEF] \\
    ‘(f i j * m) (g n) = A i (g n) + B j (g n)’ by METIS_TAC [] >> POP_ORW \\
     METIS_TAC [add_not_infty, lt_infty])
 (* final: applying MEASURE_SPACE_RESTRICTION *)
 >> martingale_alt_generator_shared_tactics_4
QED

val martingale_alt_generator_shared_tactics_5 =
    Know ‘!i j s. (A i s - B i s <= A j s - B j s <=>
                   A i s + B j s <= A j s + B i s)’
 >- (qx_genl_tac [‘M’, ‘N’, ‘t’] \\
    ‘A M t <> NegInf /\ A N t <> NegInf /\ B M t <> NegInf /\ B N t <> NegInf’
       by METIS_TAC [pos_not_neginf] \\
    ‘A M t <> PosInf /\ A N t <> PosInf /\ B M t <> PosInf /\ B N t <> PosInf’
       by METIS_TAC [lt_infty] \\
    ‘?r1. A M t = Normal r1’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?r2. A N t = Normal r2’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?r3. B M t = Normal r3’ by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?r4. B N t = Normal r4’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_add_def, extreal_sub_def, extreal_le_eq] >> REAL_ARITH_TAC)
 >> DISCH_THEN (FULL_SIMP_TAC pure_ss o wrap);
 (* end of martingale_alt_generator_shared_tactics_5 *)

(* For sub- and super-martingales, we need, in addition, that (g n) is a semi-ring.

   This theorem (and the next one) relies on measureTheory.SEMIRING_SIGMA_MONOTONE
 *)
Theorem sub_martingale_alt_generator :
   !m a u g. (!n. a n = sigma (m_space m) (g n)) /\
             (!n. has_exhausting_sequence (m_space m,g n)) /\
             (!n s. s IN (g n) ==> measure m s < PosInf) /\
             (!n. semiring (m_space m,g n)) ==>
     (sub_martingale m a u <=>
      filtered_measure_space m a /\ (!n. integrable m (u n)) /\
      !i j s. i <= j /\ s IN (g i) ==>
             (integral m (\x. u i x * indicator_fn s x) <=
              integral m (\x. u j x * indicator_fn s x)))
Proof
    martingale_alt_generator_shared_tactics_1
 (* stage work on transforming the goal into equivalence of two measures *)
 >> martingale_alt_generator_shared_tactics_5
 (* applying density_measure_def *)
 >> martingale_alt_generator_shared_tactics_2
 (* final modification of the goal *)
 >> ‘A i s + B j s <= A j s + B i s <=> (f i j * m) s <= (f j i * m) s’
      by METIS_TAC [] >> POP_ORW
 (* final modification of the major assumption *)
 >> Know ‘!i j s. i <= j /\ s IN G i ==> (f i j * m) s <= (f j i * m) s’
 >- (qx_genl_tac [‘M’, ‘N’, ‘t’] >> rpt STRIP_TAC \\
    ‘t IN measurable_sets m’ by PROVE_TAC [] \\
     METIS_TAC [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘!i j s. i <= j /\ s IN G i ==> A i s + B j s <= _’ K_TAC
 (* applying measure_space_density, density_def *)
 >> martingale_alt_generator_shared_tactics_3
 (* applying SEMIRING_SIGMA_MONOTONE *)
 >> irule SEMIRING_SIGMA_MONOTONE
 >> qexistsl_tac [‘m_space m’, ‘G i’] >> simp []
 >> CONJ_TAC (* (f j i * m) s < PosInf *)
 >- (Q.X_GEN_TAC ‘t’ >> DISCH_TAC \\
    ‘t IN measurable_sets m’ by METIS_TAC [SUBSET_DEF] \\
    ‘(f j i * m) t = A j t + B i t’ by METIS_TAC [] >> POP_ORW \\
     METIS_TAC [add_not_infty, lt_infty])
 (* applying MEASURE_SPACE_RESTRICTION *)
 >> martingale_alt_generator_shared_tactics_4
 (* subset_class *)
 >> Q.PAT_X_ASSUM ‘!n. semiring (m_space m,G n)’ (MP_TAC o (Q.SPEC ‘n’))
 >> rw [semiring_def]
QED

Theorem super_martingale_alt_generator :
   !m a u g. (!n. a n = sigma (m_space m) (g n)) /\
             (!n. has_exhausting_sequence (m_space m,g n)) /\
             (!n s. s IN (g n) ==> measure m s < PosInf) /\
             (!n. semiring (m_space m,g n)) ==>
     (super_martingale m a u <=>
      filtered_measure_space m a /\ (!n. integrable m (u n)) /\
      !i j s. i <= j /\ s IN (g i) ==>
             (integral m (\x. u j x * indicator_fn s x) <=
              integral m (\x. u i x * indicator_fn s x)))
Proof
    martingale_alt_generator_shared_tactics_1
 (* stage work on transforming the goal into equivalence of two measures *)
 >> martingale_alt_generator_shared_tactics_5
 (* applying density_measure_def *)
 >> martingale_alt_generator_shared_tactics_2
 (* final modification of the goal *)
 >> ‘A j s + B i s <= A i s + B j s <=> (f j i * m) s <= (f i j * m) s’
      by METIS_TAC [] >> POP_ORW
 (* final modification of the major assumption *)
 >> Know ‘!i j s. i <= j /\ s IN G i ==> (f j i * m) s <= (f i j * m) s’
 >- (qx_genl_tac [‘M’, ‘N’, ‘t’] >> rpt STRIP_TAC \\
    ‘t IN measurable_sets m’ by PROVE_TAC [] \\
     METIS_TAC [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘!i j s. i <= j /\ s IN G i ==> A j s + B i s <= _’ K_TAC
 (* applying measure_space_density, density_def *)
 >> martingale_alt_generator_shared_tactics_3
 (* applying SEMIRING_SIGMA_MONOTONE *)
 >> irule SEMIRING_SIGMA_MONOTONE
 >> qexistsl_tac [‘m_space m’, ‘G i’] >> simp []
 >> CONJ_TAC (* (f i j * m) s < PosInf *)
 >- (Q.X_GEN_TAC ‘t’ >> DISCH_TAC \\
    ‘t IN measurable_sets m’ by METIS_TAC [SUBSET_DEF] \\
    ‘(f i j * m) t = A i t + B j t’ by METIS_TAC [] >> POP_ORW \\
     METIS_TAC [add_not_infty, lt_infty])
 (* applying MEASURE_SPACE_RESTRICTION *)
 >> martingale_alt_generator_shared_tactics_4
 (* subset_class *)
 >> Q.PAT_X_ASSUM ‘!n. semiring (m_space m,G n)’ (MP_TAC o (Q.SPEC ‘n’))
 >> rw [semiring_def]
QED

(* NOTE: general_filtration_def, general_martingale_def, etc. are moved to
        "examples/probability/stochastic_processScript.sml" *)

(* ------------------------------------------------------------------------- *)
(*  The Function Spaces L^p and Important Inequalities [1, Chapter 13]       *)
(* ------------------------------------------------------------------------- *)

(* The L^p function space (1 <= p), was: ‘function_space’

   NOTE: added `c <> PosInf` to the case `p = PosInf`.
 *)
Definition lp_space_def :
    lp_space p m =
      {f | f IN measurable (m_space m,measurable_sets m) Borel /\
           if p = PosInf then
             ?c. 0 < c /\ c <> PosInf /\
                 measure m {x | x IN m_space m /\ c <= abs (f x)} = 0
           else
             pos_fn_integral m (\x. (abs (f x)) powr p) <> PosInf}
End

(* The most common function spaces (L^1 and L^2, plus L^\infty) *)
Overload L1_space = “lp_space 1”
Overload L2_space = “lp_space 2”
Overload L_PosInf = “lp_space PosInf”

(* alternative definition of ‘lp_space’ when p is finite (was: 1 <= p) *)
Theorem lp_space_alt_finite :
    !p m f. 0 < p /\ p <> PosInf ==>
           (f IN lp_space p m <=>
            f IN measurable (m_space m,measurable_sets m) Borel /\
            pos_fn_integral m (\x. (abs (f x)) powr p) <> PosInf)
Proof
    rw [lp_space_def]
QED

Theorem lp_space_alt_finite' :
    !p m f. measure_space m /\ 0 < p /\ p <> PosInf ==>
           (f IN lp_space p m <=>
            f IN measurable (m_space m,measurable_sets m) Borel /\
            integral m (\x. (abs (f x)) powr p) <> PosInf)
Proof
    rpt STRIP_TAC
 >> Know ‘integral m (\x. abs (f x) powr p) = pos_fn_integral m (\x. abs (f x) powr p)’
 >- (MATCH_MP_TAC integral_pos_fn >> rw [powr_pos])
 >> Rewr'
 >> MATCH_MP_TAC lp_space_alt_finite >> art []
QED

(* alternative definition of ‘lp_space’ when p is infinite *)
Theorem lp_space_alt_infinite :
    !m f. measure_space m ==>
         (f IN lp_space PosInf m <=>
          f IN measurable (m_space m,measurable_sets m) Borel /\
          ?c. 0 < c /\ c <> PosInf /\ AE x::m. abs (f x) < c)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘f IN measurable (m_space m,measurable_sets m) Borel ==>
     !c. {x | x IN m_space m /\ c <= abs (f x)} IN measurable_sets m’
       by rw [IN_MEASURABLE_BOREL_ALL_MEASURE_ABS']
 >> Know ‘f IN measurable (m_space m,measurable_sets m) Borel ==>
          !c. (AE x::m. abs (f x) < c) <=>
               null_set m {x | x IN m_space m /\ ~(abs (f x) < c)}’
 >- (DISCH_TAC >> Q.X_GEN_TAC ‘c’ \\
     HO_MATCH_MP_TAC AE_iff_null \\
     rw [extreal_lt_def])
 >> RW_TAC std_ss [null_set_def, extreal_lt_def]
 >> EQ_TAC >> rw [lp_space_def, GSYM extreal_lt_def]
 >> Q.EXISTS_TAC ‘c’
 >> FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
 >> METIS_TAC []
QED

(* special case when ‘p = 1’ *)
Theorem L1_space_alt_integrable :
    !m f. measure_space m ==> (f IN L1_space m <=> integrable m f)
Proof
    rw [lp_space_alt_finite]
 >> Know ‘(\x. abs (f x) powr 1) = abs o f’
 >- (rw [FUN_EQ_THM] \\
     MATCH_MP_TAC powr_1 >> rw [])
 >> Rewr'
 >> EQ_TAC (* easy part first *)
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC integrable_from_abs >> art [] \\
     PROVE_TAC [integrable_abs_alt])
 >> DISCH_TAC
 >> ‘integrable m (abs o f)’ by PROVE_TAC [integrable_abs]
 >> CONJ_ASM1_TAC >- fs [integrable_def]
 >> PROVE_TAC [integrable_abs_alt]
QED

(* special case when ‘p = 2’ *)
Theorem L2_space_alt_integrable_square :
    !m f. measure_space m ==>
         (f IN L2_space m <=>
          f IN Borel_measurable (m_space m,measurable_sets m) /\
          integrable m (\x. (f x) pow 2))
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘g = \x. (f x) pow 2’
 >> ‘!x. x IN m_space m ==> 0 <= g x’ by rw [Abbr ‘g’, le_pow2]
 >> ASM_SIMP_TAC std_ss [integrable_pos]
 >> Know ‘f IN L2_space m <=>
          f IN measurable (m_space m,measurable_sets m) Borel /\
          pos_fn_integral m (\x. (abs (f x)) powr 2) <> PosInf’
 >- (MATCH_MP_TAC lp_space_alt_finite \\
     rw [extreal_of_num_def, extreal_le_eq])
 >> Rewr'
 >> EQ_TAC
 >> rw [GSYM gen_powr, le_02, Abbr ‘g’, IN_MEASURABLE_BOREL_POW]
QED

(* The "else" part should only be used when ‘1 <= p’ (and also ‘p <> PosInf’) *)
Definition seminorm_def :
    seminorm p m f =
    if p = PosInf then
       inf {c | 0 < c /\ measure m {x | x IN m_space m /\ c <= abs (f x)} = 0}
    else
      (pos_fn_integral m (\x. (abs (f x)) powr p)) powr (inv p)
End

(* was: 1 <= p *)
Theorem seminorm_normal :
    !p m f. 0 < p /\ p <> PosInf ==>
            seminorm p m f = (pos_fn_integral m (\x. (abs (f x)) powr p)) powr (inv p)
Proof
    rw [seminorm_def]
QED

Theorem seminorm_infty :
    !m f. seminorm PosInf m f =
          inf {c | 0 < c /\ measure m {x | x IN m_space m /\ c <= abs (f x)} = 0}
Proof
    rw [seminorm_def]
QED

Theorem seminorm_infty_alt :
    !m f. measure_space m /\ f IN measurable (m_space m,measurable_sets m) Borel ==>
          seminorm PosInf m f = inf {c | 0 < c /\ AE x::m. abs (f x) < c}
Proof
    rw [seminorm_infty]
 >> Suff ‘!c. (AE x::m. abs (f x) < c) <=>
              measure m {x | x IN m_space m /\ c <= abs (f x)} = 0’ >- rw []
 >> Q.X_GEN_TAC ‘c’
 >> HO_MATCH_MP_TAC AE_iff_measurable
 >> rw [extreal_lt_def]
 >> rw [IN_MEASURABLE_BOREL_ALL_MEASURE_ABS']
QED

(* was: 1 <= p *)
Theorem seminorm_pos :
    !p m f. 0 < p ==> 0 <= seminorm p m f
Proof
    rpt STRIP_TAC
 >> Cases_on ‘p = PosInf’
 >- (rw [seminorm_infty, le_inf'] \\
     MATCH_MP_TAC lt_imp_le >> art [])
 >> rw [seminorm_normal, powr_pos]
QED

Theorem seminorm_one :
    !m f. measure_space m ==> seminorm 1 m f = pos_fn_integral m (abs o f)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘1’, ‘m’, ‘f’] seminorm_normal)
 >> rw [powr_pos, abs_pos, powr_1, o_DEF]
 >> MATCH_MP_TAC powr_1
 >> MATCH_MP_TAC pos_fn_integral_pos
 >> rw [abs_pos]
QED

Theorem seminorm_two :
    !m f. measure_space m ==>
          seminorm 2 m f = sqrt (pos_fn_integral m (\x. (f x) pow 2))
Proof
    rpt STRIP_TAC
 >> Know ‘seminorm 2 m f = (pos_fn_integral m (\x. (abs (f x)) powr 2)) powr (inv 2)’
 >- (MATCH_MP_TAC seminorm_normal >> rw [extreal_of_num_def, extreal_le_eq])
 >> Rewr'
 >> Know ‘pos_fn_integral m (\x. abs (f x) powr 2) powr (inv 2) =
          sqrt (pos_fn_integral m (\x. abs (f x) powr 2))’
 >- (MATCH_MP_TAC (GSYM sqrt_powr) \\
     MATCH_MP_TAC pos_fn_integral_pos >> rw [powr_pos])
 >> Rewr'
 >> rw [GSYM gen_powr, abs_pow2, le_02]
QED

(* was: 1 <= p; removed ‘p <> PosInf’ *)
Theorem seminorm_not_infty :
    !p m f. measure_space m /\ 0 < p /\ f IN lp_space p m ==>
            seminorm p m f <> PosInf /\ seminorm p m f <> NegInf
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Suff ‘seminorm p m f <> PosInf’
 >- (RW_TAC std_ss [] \\
     MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC seminorm_pos >> art [])
 >> Cases_on ‘p = PosInf’
 >- (rw [seminorm_infty, lt_infty] \\
     fs [lp_space_def] \\
     rw [GSYM inf_lt'] \\
     Q.EXISTS_TAC ‘c’ >> rw [GSYM lt_infty])
 >> RW_TAC std_ss [seminorm_normal]
 >> rfs [lp_space_def]
 >> ‘0 <= p’ by METIS_TAC [lt_imp_le]
 >> ‘p <> NegInf’ by PROVE_TAC [pos_not_neginf]
 >> Know ‘0 <= pos_fn_integral m (\x. abs (f x) powr p)’
 >- (MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
     REWRITE_TAC [powr_pos])
 >> DISCH_TAC
 >> ‘pos_fn_integral m (\x. abs (f x) powr p) <> NegInf’
      by PROVE_TAC [pos_not_neginf]
 >> ‘?r. 0 <= r /\ pos_fn_integral m (\x. abs (f x) powr p) = Normal r’
      by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_le_eq]
 >> POP_ORW
 >> ‘0 < inv p’ by PROVE_TAC [inv_pos']
 >> ‘r = 0 \/ 0 < r’ by PROVE_TAC [REAL_LE_LT]
 >- (POP_ORW \\
     rw [GSYM extreal_of_num_def, zero_rpow])
 >> ‘p <> NegInf’ by PROVE_TAC [pos_not_neginf]
 >> ‘p <> 0’ by PROVE_TAC [lt_imp_ne]
 >> ‘?z. 0 < z /\ p = Normal z’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq]
 >> POP_ORW
 >> ‘z <> 0’ by PROVE_TAC [REAL_LT_IMP_NE]
 >> rw [extreal_inv_eq]
 >> ‘0 < inv z’ by PROVE_TAC [REAL_INV_POS]
 >> rw [normal_powr]
QED

(* ‘seminorm PosInf m f’ is the AE upper bound of (abs o f)

   NOTE: The key in this proof is to construct the needed null set satisfying AE
         of the goal, and to eliminate the ‘inf’ behind ‘seminorm’.
 *)
Theorem seminorm_infty_AE_bound :
    !m f. measure_space m /\ f IN Borel_measurable (m_space m,measurable_sets m)
      ==> (AE x::m. abs (f x) <= seminorm PosInf m f)
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘c = seminorm PosInf m f’
 (* This special case must be eliminated first *)
 >> Cases_on ‘c = PosInf’
 >- (rw [le_infty] \\
     MATCH_MP_TAC AE_T >> art [])
 >> Know ‘c <> NegInf’
 >- (MATCH_MP_TAC pos_not_neginf \\
     Q.UNABBREV_TAC ‘c’ \\
     MATCH_MP_TAC seminorm_pos >> rw [extreal_of_num_def, lt_infty])
 >> DISCH_TAC
 (* now start finding the null sets whose BIGUNION is the needed one *)
 >> Know ‘!n. AE x::m. abs (f x) <= c + inv (&SUC n)’
 >- (rw [AE_DEF] \\
     Know ‘0 < inv (&SUC n)’
     >- (MATCH_MP_TAC inv_pos' >> rw [extreal_of_num_def, extreal_lt_eq]) \\
     DISCH_TAC \\
     Know ‘seminorm PosInf m f < c + inv (&SUC n)’
     >- (simp [] >> MATCH_MP_TAC lt_addr_imp >> art []) \\
  (* applying inf_lt' *)
     REWRITE_TAC [seminorm_infty, GSYM inf_lt'] >> rw [] \\
     Q.EXISTS_TAC ‘{z | z IN m_space m /\ x <= abs (f z)}’ \\
     reverse CONJ_TAC
     >- (rw [GSYM extreal_lt_def] \\
         MATCH_MP_TAC lt_imp_le >> PROVE_TAC [lt_trans]) \\
     rw [null_set_def, le_abs_bounds] \\
    ‘{z | z IN m_space m /\ (f z <= -x \/ x <= f z)} =
       ({z | f z <= -x} INTER m_space m) UNION ({z | x <= f z} INTER m_space m)’
        by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC MEASURE_SPACE_UNION >> art [] \\
    ‘sigma_algebra (measurable_space m)’
       by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA] \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE])
 (* stage work, ‘seminorm’ is not used below *)
 >> rw [AE_DEF]
 >> fs [SKOLEM_THM] (* This asserts function f'(n) of null sets *)
 >> Q.EXISTS_TAC ‘BIGUNION (IMAGE f' UNIV)’
 >> CONJ_TAC
 >- (MATCH_MP_TAC NULL_SET_BIGUNION' >> rw [])
 >> rw [IN_BIGUNION_IMAGE]
 >> rename1 ‘!n. x NOTIN (g n)’ (* rename f' with g *)
 (* applying le_epsilon! *)
 >> MATCH_MP_TAC le_epsilon >> rw []
 (* now we need to find n such that ‘inv (&SUCn) <= e’ *)
 >> ‘?n. inv (&SUC n) <= e’ by METIS_TAC [EXTREAL_ARCH_INV, lt_imp_le]
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC ‘c + inv (&SUC n)’
 >> CONJ_TAC >- METIS_TAC []
 >> MATCH_MP_TAC le_ladd_imp >> art []
QED

(* was: 1 <= p *)
Theorem seminorm_powr :
    !p m f. measure_space m /\ 0 < p /\ p <> PosInf ==>
           (seminorm p m f) powr p = pos_fn_integral m (\x. (abs (f x)) powr p)
Proof
    RW_TAC std_ss [seminorm_normal]
 >> Q.ABBREV_TAC ‘a = pos_fn_integral m (\x. abs (f x) powr p)’
 >> ‘0 < inv p’ by PROVE_TAC [inv_pos']
 >> ‘inv p <> PosInf’ by METIS_TAC [inv_not_infty, lt_imp_ne]
 >> Know ‘0 <= a’
 >- (Q.UNABBREV_TAC ‘a’ \\
     MATCH_MP_TAC pos_fn_integral_pos >> rw [powr_pos])
 >> RW_TAC std_ss [powr_powr]
 >> Suff ‘inv p * p = 1’ >- rw [powr_1]
 >> MATCH_MP_TAC mul_linv_pos >> art []
QED

(* was: 1 <= p; removed ‘p <> PosInf’ *)
Theorem seminorm_eq_0 :
    !p m f. measure_space m /\ 0 < p /\ f IN Borel_measurable (measurable_space m) ==>
           (seminorm p m f = 0 <=> AE x::m. f x = 0)
Proof
    rpt STRIP_TAC
 >> Cases_on ‘p = PosInf’
 >- (POP_ORW >> rw [seminorm_infty] \\
     reverse EQ_TAC >| (* 2 subgoals, first is easier *)
     [ (* goal 1 (of 2) *)
       rw [AE_DEF] \\
       Know ‘!c. 0 < c ==> measure m {x | x IN m_space m /\ c <= abs (f x)} = 0’
       >- (rpt STRIP_TAC \\
           fs [null_set_def] \\
           Q.ABBREV_TAC ‘s = {x | x IN m_space m /\ c <= abs (f x)}’ \\
          ‘s IN measurable_sets m’ by rw [Abbr ‘s’, IN_MEASURABLE_BOREL_ALL_MEASURE_ABS'] \\
          ‘s = (s DIFF N) UNION (s INTER N)’ by SET_TAC [] >> POP_ORW \\
          ‘DISJOINT (s DIFF N) (s INTER N)’ by SET_TAC [DISJOINT_ALT] \\
           Know ‘measure m (s DIFF N UNION s INTER N) =
                 measure m (s DIFF N) + measure m (s INTER N)’
           >- (MATCH_MP_TAC MEASURE_ADDITIVE >> rw [] >|
               [ MATCH_MP_TAC MEASURE_SPACE_DIFF >> art [],
                 MATCH_MP_TAC MEASURE_SPACE_INTER >> art [] ]) >> Rewr' \\
           Know ‘measure m (s INTER N) = 0’
           >- (reverse (rw [GSYM le_antisym])
               >- (MATCH_MP_TAC MEASURE_POSITIVE >> art [] \\
                   MATCH_MP_TAC MEASURE_SPACE_INTER >> art []) \\
               Q.PAT_X_ASSUM ‘measure m N = 0’ (ONCE_REWRITE_TAC o wrap o SYM) \\
               MATCH_MP_TAC MEASURE_INCREASING >> art [] \\
               CONJ_TAC >- SET_TAC [] \\
               MATCH_MP_TAC MEASURE_SPACE_INTER >> art []) \\
           DISCH_THEN (rw o wrap) \\
           Suff ‘s DIFF N = {}’ >- (Rewr' >> PROVE_TAC [MEASURE_EMPTY]) \\
           rw [Abbr ‘s’, Once EXTENSION] \\
           CCONTR_TAC >> fs [] \\
          ‘f x = 0’ by PROVE_TAC [] >> fs [abs_0] \\
           METIS_TAC [let_antisym]) >> DISCH_TAC \\
       Know ‘{c | 0 < c /\ measure m {x | x IN m_space m /\ c <= abs (f x)} = 0} =
             {c | 0 < c}’
       >- (rw [Once EXTENSION] >> EQ_TAC >> rw []) >> Rewr' \\
       rw [inf_eq'] >- (MATCH_MP_TAC lt_imp_le >> art []) \\
       CCONTR_TAC >> fs [GSYM extreal_lt_def] \\
       Cases_on ‘y = PosInf’
       >- (Q.PAT_X_ASSUM ‘!z. 0 < z ==> y <= z’ (MP_TAC o (Q.SPEC ‘1’)) \\
           rw [le_infty]) \\
       Q.PAT_X_ASSUM ‘!z. 0 < z ==> y <= z’ (MP_TAC o (Q.SPEC ‘1 / 2 * y’)) \\
       Know ‘0 < 1 / 2 * y’
       >- (MATCH_MP_TAC lt_mul >> rw [half_between]) >> rw [GSYM extreal_lt_def] \\
       Suff ‘1 / 2 * y < 1 * y’ >- rw [] \\
       rw [lt_rmul, half_between],
       (* goal 2 (of 2) *)
       DISCH_TAC \\
       Know ‘(AE x::m. f x = 0) <=> measure m {x | x IN m_space m /\ f x <> 0} = 0’
       >- (HO_MATCH_MP_TAC AE_iff_measurable \\
           rw [IN_MEASURABLE_BOREL_ALL_MEASURE_ABS']) >> Rewr' \\
      ‘!x. f x <> 0 <=> 0 < abs (f x)’ by PROVE_TAC [abs_gt_0] >> POP_ORW \\
      ‘{x | x IN m_space m /\ 0 < abs (f x)} IN measurable_sets m’
         by rw [IN_MEASURABLE_BOREL_ALL_MEASURE_ABS'] \\
      ‘!c. {x | x IN m_space m /\ c <= abs (f x)} IN measurable_sets m’
         by rw [IN_MEASURABLE_BOREL_ALL_MEASURE_ABS'] \\
    (* The measure inside ‘inf {}’ should be monotonic *)
       Q.ABBREV_TAC ‘H = \c. measure m {x | x IN m_space m /\ c <= abs (f x)}’ \\
    (* So it's actually decreasing, with smaller c the measure is larger *)
       Know ‘!a b. a <= b ==> H b <= H a’
       >- (rw [Abbr ‘H’] \\
           MATCH_MP_TAC MEASURE_INCREASING >> art [] \\
           rw [SUBSET_DEF] \\
           MATCH_MP_TAC le_trans >> Q.EXISTS_TAC ‘b’ >> art []) >> DISCH_TAC \\
       FULL_SIMP_TAC std_ss [] (* simplify assumptions using ‘H’ *) \\
       Q.ABBREV_TAC ‘s = {x | x IN m_space m /\ 0 < abs (f x)}’ \\
    (* NOTE: below we show that, if ‘measure m s < 0’ then ‘inf {} > 0’ *)
       CCONTR_TAC \\
      ‘measure m s = 0 \/ 0 < measure m s’ by PROVE_TAC [MEASURE_POSITIVE, le_lt] \\
       Q.PAT_X_ASSUM ‘measure m s <> 0’ K_TAC \\
       POP_ASSUM MP_TAC (* 0 < measure m s *) \\
       Know ‘s = BIGUNION (IMAGE (\n. {x | x IN m_space m /\ (inv &SUC n) <= abs (f x)}) UNIV)’
       >- (rw [Abbr ‘s’, Once EXTENSION, IN_BIGUNION_IMAGE, Excl "abs_gt_0"] \\
           reverse EQ_TAC >> RW_TAC std_ss [] >> art []
           >- (MATCH_MP_TAC lte_trans \\
               Q.EXISTS_TAC ‘inv (&SUC n)’ >> art [] \\
               MATCH_MP_TAC inv_pos' >> rw [extreal_of_num_def, extreal_lt_eq]) \\
           Q.ABBREV_TAC ‘y = abs (f x)’ \\
           MATCH_MP_TAC EXTREAL_ARCH_INV' >> art []) \\
       DISCH_THEN (PURE_ONCE_REWRITE_TAC o wrap) \\
    (* applying MONOTONE_CONVERGENCE2 *)
       Q.ABBREV_TAC ‘g = \n. {x | x IN m_space m /\ realinv (&SUC n) <= abs (f x)}’ \\
       Know ‘measure m (BIGUNION (IMAGE g univ(:num))) =
             sup (IMAGE (measure m o g) univ(:num))’
       >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
           MATCH_MP_TAC MONOTONE_CONVERGENCE2 >> rw [IN_FUNSET, Abbr ‘g’] \\
           rw [SUBSET_DEF] \\
           MATCH_MP_TAC le_trans >> Q.EXISTS_TAC ‘inv (&SUC n)’ >> rw [] \\
           MATCH_MP_TAC inv_le_antimono_imp >> rw [extreal_of_num_def]) \\
       DISCH_THEN (PURE_ONCE_REWRITE_TAC o wrap) \\
       Q.UNABBREV_TAC ‘s’ (* useless *) \\
    (* applying lt_sup *)
       DISCH_THEN (STRIP_ASSUME_TAC o (SIMP_RULE (srw_ss()) [o_DEF, lt_sup])) \\
       rename1 ‘x = measure m (g n)’ \\
       Q.PAT_X_ASSUM ‘x = measure m (g n)’ (FULL_SIMP_TAC std_ss o wrap) \\
       REV_FULL_SIMP_TAC std_ss [Abbr ‘g’] (* remove ‘g’, using ‘H’ *) \\
       Q.ABBREV_TAC ‘z = inv (&SUC n)’ (* this is an important constant *) \\
       Know ‘0 < z’
       >- (Q.UNABBREV_TAC ‘z’ \\
           MATCH_MP_TAC inv_pos' >> rw [extreal_of_num_def]) >> DISCH_TAC \\
    (* now we show ‘inf {H c = 0} = 0’ is impossible since z <= inf {} *)
       Suff ‘z <= inf {c | 0 < c /\ H c = 0}’
       >- (DISCH_TAC \\
          ‘0 < inf {c | 0 < c /\ H c = 0}’ by PROVE_TAC [lte_trans] \\
           METIS_TAC [lt_le]) \\
       rw [le_inf'] \\
       SPOSE_NOT_THEN (ASSUME_TAC o (REWRITE_RULE [GSYM extreal_lt_def])) \\
      ‘y <= z’ by PROVE_TAC [lt_imp_le] \\
      ‘H z <= H y’ by PROVE_TAC [] \\
       METIS_TAC [let_antisym] ])
 >> rw [seminorm_normal]
 >> ‘0 <= p’ by PROVE_TAC [lt_imp_le]
 >> ‘p <> 0’ by PROVE_TAC [lt_imp_ne]
 >> ‘0 < inv p’ by PROVE_TAC [inv_pos']
 >> Know ‘pos_fn_integral m (\x. abs (f x) powr p) powr (inv p) = 0 <=>
          pos_fn_integral m (\x. abs (f x) powr p) = 0’
 >- (MATCH_MP_TAC powr_eq_0 >> rw [inv_not_infty] \\
     MATCH_MP_TAC pos_fn_integral_pos >> rw [powr_pos])
 >> Rewr'
 >> Q.ABBREV_TAC ‘g = \x. abs (f x) powr p’
 >> Know ‘pos_fn_integral m g = 0 <=> measure m {x | x IN m_space m /\ g x <> 0} = 0’
 >- (MATCH_MP_TAC pos_fn_integral_eq_0 >> rw [Abbr ‘g’, powr_pos] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS_POWR >> art [])
 >> Rewr'
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> HO_MATCH_MP_TAC AE_iff_measurable
 >> simp [Abbr ‘g’, powr_eq_0]
 >> rw [IN_MEASURABLE_BOREL_ALL_MEASURE_ABS']
QED

(* was: 1 <= p, removed ‘p <> PosInf’ *)
Theorem lp_space_alt_seminorm :
    !p m f. measure_space m /\ 0 < p ==>
           (f IN lp_space p m <=>
            f IN Borel_measurable (m_space m,measurable_sets m) /\
            seminorm p m f < PosInf)
Proof
    RW_TAC std_ss [GSYM lt_infty]
 >> EQ_TAC
 >- (rpt STRIP_TAC >- rfs [lp_space_def] \\
     METIS_TAC [seminorm_not_infty])
 >> Cases_on ‘p = PosInf’
 >- (POP_ASSUM (FULL_SIMP_TAC std_ss o wrap) \\
     rw [lp_space_alt_infinite] \\
    ‘0 <= seminorm PosInf m f’ by (MATCH_MP_TAC seminorm_pos >> rw []) \\
    ‘seminorm PosInf m f <> NegInf’ by PROVE_TAC [pos_not_neginf] \\
    ‘seminorm PosInf m f = 0 \/ 0 < seminorm PosInf m f’ by PROVE_TAC [le_lt]
     >- (Know ‘AE x::m. f x = 0’ >- METIS_TAC [seminorm_eq_0] \\
         rw [AE_DEF] \\
         Q.EXISTS_TAC ‘1’ >> rw [] \\
         Q.EXISTS_TAC ‘N’ >> rw []) \\
     Know ‘AE x::m. abs (f x) <= seminorm PosInf m f’
     >- (MATCH_MP_TAC seminorm_infty_AE_bound >> art []) \\
     rw [AE_DEF] \\
     Q.ABBREV_TAC ‘c = seminorm PosInf m f’ \\
     Q.EXISTS_TAC ‘c + 1’ \\
     CONJ_TAC >- rw [lt_add] \\
     CONJ_TAC >- (‘1 <> PosInf’ by rw [] >> METIS_TAC [add_not_infty]) \\
     Q.EXISTS_TAC ‘N’ >> rw [] \\
     MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘c’ \\
     reverse CONJ_TAC >- (MATCH_MP_TAC lt_addr_imp >> rw []) \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> rw [lp_space_alt_finite, seminorm_normal]
 >> CCONTR_TAC
 >> ‘0 < inv p’ by PROVE_TAC [inv_pos']
 >> gs [infty_powr]
QED

(* Theorem 13.2 (Hoelder's inequality) [1, p.117]

   NOTE: ‘p <> PosInf /\ q <> PosInf’ was there but then removed.
 *)
Theorem Hoelder_inequality_lemma[local] :
    !m u v. measure_space m /\ u IN lp_space PosInf m /\ v IN L1_space m ==>
            integrable m (\x. u x * v x) /\
            integral m (\x. abs (u x * v x)) <= seminorm PosInf m u * seminorm 1 m v
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘u IN measurable (m_space m,measurable_sets m) Borel /\
     v IN measurable (m_space m,measurable_sets m) Borel’
       by fs [lp_space_def]
 >> ‘seminorm PosInf m u <> PosInf /\ seminorm PosInf m u <> NegInf’
       by (MATCH_MP_TAC seminorm_not_infty >> rw [])
 >> ONCE_REWRITE_TAC [CONJ_SYM]
 >> CONJ_ASM1_TAC
 >- (Know ‘integral m (\x. abs (u x * v x)) = pos_fn_integral m (\x. abs (u x * v x))’
     >- (MATCH_MP_TAC integral_pos_fn >> rw [abs_pos]) >> Rewr' \\
     rw [seminorm_one] \\
     Know ‘0 <= seminorm PosInf m u’
     >- (MATCH_MP_TAC seminorm_pos >> rw []) >> DISCH_TAC \\
     Know ‘seminorm PosInf m u * pos_fn_integral m (abs o v) =
           pos_fn_integral m (\x. seminorm PosInf m u * (abs o v) x)’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
        ‘?r. 0 <= r /\ seminorm PosInf m u = Normal r’
           by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_le_eq] >> POP_ORW \\
         MATCH_MP_TAC pos_fn_integral_cmul >> rw [o_DEF, abs_pos]) >> Rewr' \\
     MATCH_MP_TAC pos_fn_integral_mono_AE >> rw [abs_pos]
     >- (MATCH_MP_TAC le_mul >> rw [abs_pos]) \\
     Know ‘AE x::m. abs (u x) <= seminorm PosInf m u’
     >- (MATCH_MP_TAC seminorm_infty_AE_bound >> art []) \\
     rw [AE_DEF] >> Q.EXISTS_TAC ‘N’ >> rw [abs_mul] \\
     MATCH_MP_TAC le_rmul_imp >> rw [abs_pos])
 (* stage work *)
 >> MATCH_MP_TAC integrable_from_abs >> art []
 >> CONJ_ASM1_TAC
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES \\
     qexistsl_tac [‘u’, ‘v’] >> rw [])
 >> rw [integrable_abs_alt, lt_infty]
 >> Know ‘pos_fn_integral m (abs o (\x. u x * v x)) = integral m (\x. abs (u x * v x))’
 >- (rw [o_DEF, Once EQ_SYM_EQ] \\
     MATCH_MP_TAC integral_pos_fn >> rw [abs_pos])
 >> Rewr'
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC ‘seminorm PosInf m u * seminorm 1 m v’ >> art []
 >> ‘seminorm 1 m v <> PosInf /\ seminorm 1 m v <> NegInf’
      by PROVE_TAC [seminorm_not_infty, lt_01]
 >> ‘?a. seminorm PosInf m u = Normal a’ by METIS_TAC [extreal_cases]
 >> ‘?b. seminorm 1 m v = Normal b’ by METIS_TAC [extreal_cases]
 >> rw [GSYM lt_infty, extreal_mul_def, extreal_not_infty]
QED

Theorem Hoelder_inequality :
    !m u v p q. measure_space m /\ 0 < p /\ 0 < q /\ inv(p) + inv(q) = 1 /\
                u IN lp_space p m /\ v IN lp_space q m
            ==> integrable m (\x. u x * v x) /\
                integral m (\x. abs (u x * v x)) <= seminorm p m u * seminorm q m v
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘p <> 0 /\ q <> 0’ by rw [lt_imp_ne]
 >> ‘1 <= p /\ 1 <= q’ by PROVE_TAC [conjugate_properties]
 >> ‘0 <= p /\ 0 <= q’ by rw [lt_imp_le]
 >> ‘p <> NegInf /\ q <> NegInf’ by PROVE_TAC [pos_not_neginf]
 >> ‘u IN measurable (m_space m,measurable_sets m) Borel /\
     v IN measurable (m_space m,measurable_sets m) Borel’
       by gs [lp_space_def]
 (* special cases *)
 >> Cases_on ‘p = PosInf’
 >- (‘q = 1’ by PROVE_TAC [conjugate_properties] >> fs [] \\
     MATCH_MP_TAC Hoelder_inequality_lemma >> art [])
 >> Cases_on ‘q = PosInf’
 >- (‘p = 1’ by PROVE_TAC [conjugate_properties] >> fs [] \\
     ONCE_REWRITE_TAC [mul_comm] \\
     MATCH_MP_TAC Hoelder_inequality_lemma >> art [])
 (* stage work *)
 >> ‘seminorm p m u <> PosInf /\ seminorm p m u <> NegInf /\
     seminorm q m v <> PosInf /\ seminorm q m v <> NegInf’
       by PROVE_TAC [seminorm_not_infty]
 >> Suff ‘integral m (\x. abs (u x * v x)) <= seminorm p m u * seminorm q m v’
 >- (RW_TAC std_ss [] \\
     MATCH_MP_TAC integrable_from_abs >> ASM_SIMP_TAC std_ss [o_DEF] \\
     STRONG_CONJ_TAC
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES \\
         qexistsl_tac [‘u’, ‘v’] >> rw []) >> DISCH_TAC \\
     Q.ABBREV_TAC ‘g = \x. abs (u x * v x)’ \\
     Know ‘integrable m g <=>
           g IN Borel_measurable (m_space m,measurable_sets m) /\
           pos_fn_integral m g <> PosInf’
     >- (MATCH_MP_TAC integrable_pos >> rw [Abbr ‘g’, abs_pos]) >> Rewr' \\
     CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS \\
                  Q.EXISTS_TAC ‘\x. u x * v x’ >> rw [Abbr ‘g’]) \\
     Know ‘pos_fn_integral m g = integral m g’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC integral_pos_fn >> rw [Abbr ‘g’, abs_pos]) >> Rewr' \\
     REWRITE_TAC [lt_infty] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘seminorm p m u * seminorm q m v’ >> art [] \\
     REWRITE_TAC [GSYM lt_infty] \\
    ‘?a. seminorm p m u = Normal a’ by METIS_TAC [extreal_cases] \\
    ‘?b. seminorm q m v = Normal b’ by METIS_TAC [extreal_cases] \\
     rw [extreal_mul_def, extreal_not_infty])
 >> Know ‘integral m (\x. abs (u x * v x)) = pos_fn_integral m (\x. abs (u x * v x))’
 >- (MATCH_MP_TAC integral_pos_fn >> rw [abs_pos])
 >> Rewr'
 (* special cases stop young_inequality from applicable (division by zero) *)
 >> Cases_on ‘seminorm p m u = 0’
 >- (rw [] \\
     Suff ‘pos_fn_integral m (\x. abs (u x * v x)) = 0’ >- rw [le_lt] \\
     POP_ASSUM MP_TAC \\
     ASM_SIMP_TAC std_ss [seminorm_normal] \\
     Know ‘pos_fn_integral m (\x. abs (u x) powr p) powr (inv p) = 0 <=>
           pos_fn_integral m (\x. abs (u x) powr p) = 0’
     >- (MATCH_MP_TAC powr_eq_0 \\
         rpt CONJ_TAC >| (* 3 subgoals *)
         [ (* goal 1 (of 3) *)
           MATCH_MP_TAC pos_fn_integral_pos >> rw [powr_pos],
           (* goal 2 (of 3) *)
           rw [inv_pos'],
           (* goal 3 (of 3) *)
           METIS_TAC [inv_not_infty] ]) >> Rewr' \\
     Q.ABBREV_TAC ‘f = \x. abs (u x) powr p’ \\
     Know ‘f IN measurable (m_space m,measurable_sets m) Borel’
     >- (Q.UNABBREV_TAC ‘f’ \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS_POWR >> art []) >> DISCH_TAC \\
     Know ‘pos_fn_integral m f = 0 <=>
           measure m {x | x IN m_space m /\ f x <> 0} = 0’
     >- (MATCH_MP_TAC pos_fn_integral_eq_0 >> rw [Abbr ‘f’, powr_pos]) >> Rewr' \\
    ‘measure m {x | x IN m_space m /\ f x <> 0} = 0 <=>
     AE x::m. (abs o f) x = 0’ by METIS_TAC [integral_abs_eq_0] >> POP_ORW \\
     POP_ASSUM K_TAC (* cleanup ‘f’ *) \\
     simp [Abbr ‘f’, powr_eq_0] >> rw [AE_ALT] \\
     Know ‘pos_fn_integral m (\x. abs (u x * v x)) = 0 <=>
           measure m {x | x IN m_space m /\ abs (u x * v x) <> 0} = 0’
     >- (HO_MATCH_MP_TAC pos_fn_integral_eq_0 >> rw [] \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS \\
         Q.EXISTS_TAC ‘\x. u x * v x’ >> rw [] \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES' \\
         qexistsl_tac [‘u’, ‘v’] >> simp []) >> Rewr' \\
     rw [abs_not_zero] \\
     Know ‘{x | x IN m_space m /\ u x <> 0} IN measurable_sets m’
     >- (‘{x | x IN m_space m /\ u x <> 0} = {x | u x <> 0} INTER m_space m’
            by SET_TAC [] >> POP_ORW \\
         rw [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC \\
     Know ‘{x | x IN m_space m /\ u x <> 0 /\ v x <> 0} IN measurable_sets m’
     >- (‘{x | x IN m_space m /\ u x <> 0 /\ v x <> 0} =
          {x | x IN m_space m /\ u x <> 0} INTER
          ({x | v x <> 0} INTER m_space m)’ by SET_TAC [] >> POP_ORW \\
         MATCH_MP_TAC MEASURE_SPACE_INTER \\
         rw [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC \\
     reverse (rw [Once (GSYM le_antisym)])
     >- (Know ‘positive m’ >- PROVE_TAC [MEASURE_SPACE_POSITIVE] \\
         rw [positive_def]) \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC ‘measure m {x | x IN m_space m /\ u x <> 0}’ \\
     CONJ_TAC >- (MATCH_MP_TAC INCREASING \\
                  rw [MEASURE_SPACE_INCREASING, SUBSET_DEF]) \\
    ‘0 = measure m N’ by PROVE_TAC [null_set_def] \\
     POP_ASSUM (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites o wrap) \\
     MATCH_MP_TAC INCREASING >> rw [MEASURE_SPACE_INCREASING] \\
     fs [null_set_def])
 >> Cases_on ‘seminorm q m v = 0’ (* symmetric with above *)
 >- (rw [] \\
     Suff ‘pos_fn_integral m (\x. abs (u x * v x)) = 0’ >- rw [le_lt] \\
     POP_ASSUM MP_TAC \\
     ASM_SIMP_TAC std_ss [seminorm_normal] \\
     Know ‘pos_fn_integral m (\x. abs (v x) powr q) powr (inv q) = 0 <=>
           pos_fn_integral m (\x. abs (v x) powr q) = 0’
     >- (MATCH_MP_TAC powr_eq_0 \\
         rpt CONJ_TAC >| (* 3 subgoals *)
         [ (* goal 1 (of 3) *)
           MATCH_MP_TAC pos_fn_integral_pos >> rw [powr_pos],
           (* goal 2 (of 3) *)
           rw [inv_pos'],
           (* goal 3 (of 3) *)
           METIS_TAC [inv_not_infty] ]) >> Rewr' \\
     Q.ABBREV_TAC ‘f = \x. abs (v x) powr q’ \\
     Know ‘f IN measurable (m_space m,measurable_sets m) Borel’
     >- (Q.UNABBREV_TAC ‘f’ \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS_POWR >> art []) >> DISCH_TAC \\
     Know ‘pos_fn_integral m f = 0 <=>
           measure m {x | x IN m_space m /\ f x <> 0} = 0’
     >- (MATCH_MP_TAC pos_fn_integral_eq_0 >> rw [Abbr ‘f’, powr_pos]) >> Rewr' \\
    ‘measure m {x | x IN m_space m /\ f x <> 0} = 0 <=>
     AE x::m. (abs o f) x = 0’ by METIS_TAC [integral_abs_eq_0] >> POP_ORW \\
     POP_ASSUM K_TAC (* cleanup ‘f’ *) \\
     simp [Abbr ‘f’, powr_eq_0] >> rw [AE_ALT] \\
     Know ‘pos_fn_integral m (\x. abs (u x * v x)) = 0 <=>
           measure m {x | x IN m_space m /\ abs (u x * v x) <> 0} = 0’
     >- (HO_MATCH_MP_TAC pos_fn_integral_eq_0 >> rw [] \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS \\
         Q.EXISTS_TAC ‘\x. u x * v x’ >> rw [] \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES' \\
         qexistsl_tac [‘u’, ‘v’] >> simp []) >> Rewr' \\
     rw [abs_not_zero] \\
     Know ‘{x | x IN m_space m /\ v x <> 0} IN measurable_sets m’
     >- (‘{x | x IN m_space m /\ v x <> 0} = {x | v x <> 0} INTER m_space m’
            by SET_TAC [] >> POP_ORW \\
         rw [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC \\
     Know ‘{x | x IN m_space m /\ u x <> 0 /\ v x <> 0} IN measurable_sets m’
     >- (‘{x | x IN m_space m /\ u x <> 0 /\ v x <> 0} =
            ({x | u x <> 0} INTER m_space m) INTER
            {x | x IN m_space m /\ v x <> 0}’ by SET_TAC [] >> POP_ORW \\
         MATCH_MP_TAC MEASURE_SPACE_INTER \\
         rw [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC \\
     reverse (rw [Once (GSYM le_antisym)])
     >- (Know ‘positive m’ >- PROVE_TAC [MEASURE_SPACE_POSITIVE] \\
         rw [positive_def]) \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC ‘measure m {x | x IN m_space m /\ v x <> 0}’ \\
     CONJ_TAC >- (MATCH_MP_TAC INCREASING \\
                  rw [MEASURE_SPACE_INCREASING, SUBSET_DEF]) \\
    ‘0 = measure m N’ by PROVE_TAC [null_set_def] \\
     POP_ASSUM (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites o wrap) \\
     MATCH_MP_TAC INCREASING >> rw [MEASURE_SPACE_INCREASING] \\
     fs [null_set_def])
 >> ‘0 <= seminorm p m u /\ 0 <= seminorm q m v’ by PROVE_TAC [seminorm_pos]
 >> ‘0 < seminorm p m u /\ 0 < seminorm q m v’ by PROVE_TAC [le_lt]
 (* stage work (for ‘p <> PosInf /\ q <> PosInf’) *)
 >> Q.ABBREV_TAC ‘A = \x. abs (u x) / seminorm p m u’
 >> Q.ABBREV_TAC ‘B = \x. abs (v x) / seminorm q m v’
 >> Know ‘!x. 0 <= A x’
 >- (rw [Abbr ‘A’] \\
    ‘?r. 0 < r /\ seminorm p m u = Normal r’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] \\
     POP_ORW \\
     MATCH_MP_TAC le_div >> rw [abs_pos])
 >> DISCH_TAC
 >> Know ‘!x. 0 <= B x’
 >- (rw [Abbr ‘B’] \\
    ‘?r. 0 < r /\ seminorm q m v = Normal r’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] \\
     POP_ORW \\
     MATCH_MP_TAC le_div >> rw [abs_pos])
 >> DISCH_TAC
 >> Know ‘!x. A x * B x <= (A x) powr p / p + (B x) powr q / q’
 >- (Q.X_GEN_TAC ‘x’ \\
     MP_TAC (Q.SPECL [‘A x’, ‘B x’, ‘p’, ‘q’] young_inequality) \\
     RW_TAC std_ss [])
 >> DISCH_TAC
 >> Know ‘pos_fn_integral m (\x. A x * B x) <=
          pos_fn_integral m (\x. A x powr p / p + B x powr q / q)’
 >- (MATCH_MP_TAC pos_fn_integral_mono >> rw [] \\
     MATCH_MP_TAC le_mul >> art [])
 >> POP_ASSUM K_TAC
 >> ‘seminorm p m u * seminorm q m v <> 0’ by METIS_TAC [entire]
 >> ‘0 <= seminorm p m u * seminorm q m v’ by PROVE_TAC [le_mul]
 >> ‘0 < seminorm p m u * seminorm q m v’ by PROVE_TAC [le_lt]
 >> ‘seminorm p m u * seminorm q m v <> NegInf’ by PROVE_TAC [pos_not_neginf]
 >> Know ‘seminorm p m u * seminorm q m v <> PosInf’
 >- (‘?a. seminorm p m u = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     ‘?b. seminorm q m v = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_mul_def])
 >> DISCH_TAC
 >> Know ‘pos_fn_integral m (\x. A x * B x) =
          pos_fn_integral m (\x. abs (u x * v x)) / (seminorm p m u * seminorm q m v)’
 >- (simp [Abbr ‘A’, Abbr ‘B’] \\
     Know ‘!x. abs (u x) / seminorm p m u * (abs (v x) / seminorm q m v) =
               abs (u x * v x) / (seminorm p m u * seminorm q m v)’
     >- (Q.X_GEN_TAC ‘x’ \\
        ‘?a. a <> 0 /\ seminorm p m u = Normal a’ by METIS_TAC [extreal_cases, extreal_of_num_def] \\
         POP_ORW \\
        ‘?b. b <> 0 /\ seminorm q m v = Normal b’ by METIS_TAC [extreal_cases, extreal_of_num_def] \\
         POP_ORW \\
        ‘a * b <> 0’ by PROVE_TAC [REAL_ENTIRE] \\
         rw [extreal_div_def, extreal_mul_def, abs_mul] \\
         Know ‘inv (Normal (a * b)) = inv (Normal a) * inv (Normal b)’
         >- (rw [extreal_inv_def, extreal_mul_def]) >> Rewr' \\
         METIS_TAC [mul_comm, mul_assoc]) >> Rewr' \\
    ‘?r. 0 < r /\ seminorm p m u * seminorm q m v = Normal r’
        by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] >> POP_ORW \\
    ‘r <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] \\
     rw [extreal_div_def, extreal_inv_def] \\
     ONCE_REWRITE_TAC [mul_comm] \\
     HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [abs_pos] \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art [])
 >> Rewr'
 >> Know ‘pos_fn_integral m (\x. A x powr p / p + B x powr q / q) =
          pos_fn_integral m (\x. A x powr p / p) +
          pos_fn_integral m (\x. B x powr q / q)’
 >- (HO_MATCH_MP_TAC pos_fn_integral_add \\
     RW_TAC bool_ss [] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
      ‘?r. 0 < r /\ p = Normal r’
         by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] >> POP_ORW \\
       MATCH_MP_TAC le_div >> art [powr_pos],
       (* goal 2 (of 4) *)
      ‘?r. 0 < r /\ q = Normal r’
         by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] >> POP_ORW \\
       MATCH_MP_TAC le_div >> art [powr_pos],
       (* goal 3 (of 4) *)
       NTAC 5 (POP_ASSUM K_TAC) (* all about ‘seminorm p m u * seminorm q m v’ *) \\
       rw [Abbr ‘A’] \\
      ‘?r. 0 < r /\ seminorm p m u = Normal r’
         by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] >> POP_ORW \\
      ‘r <> 0’ by rw [REAL_LT_IMP_NE] \\
       rw [extreal_div_def, extreal_inv_def] \\
       Know ‘!x. (abs (u x) * Normal (inv r)) powr p =
                 (abs (u x)) powr p * Normal (inv r) powr p’
       >- (Q.X_GEN_TAC ‘x’ >> MATCH_MP_TAC mul_powr \\
           rw [extreal_of_num_def, extreal_le_eq, REAL_LT_IMP_LE]) >> Rewr' \\
      ‘?P. 0 < P /\ p = Normal P’
         by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] >> POP_ORW \\
      ‘P <> 0’ by rw [REAL_LT_IMP_NE] \\
      ‘0 < inv r’ by rw [REAL_INV_POS] \\
       rw [extreal_div_def, extreal_inv_def, extreal_mul_def, normal_powr, GSYM mul_assoc] \\
       MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL \\
       qexistsl_tac [‘\x. abs (u x) powr Normal P’, ‘inv P * inv r powr P’] \\
       RW_TAC std_ss [] >| (* 3 subgoals *)
       [ (* goal 3.1 (of 3) *)
         simp [],
         (* goal 3.2 (of 3) *)
         MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS_POWR \\
        ‘0 <= P’ by rw [REAL_LT_IMP_LE] \\
         rw [extreal_of_num_def, extreal_le_eq],
         (* goal 3.3 (of 3) *)
         PROVE_TAC [mul_comm] ],
       (* goal 4 (of 4) *)
       NTAC 5 (POP_ASSUM K_TAC) (* all about ‘seminorm p m u * seminorm q m v’ *) \\
       rw [Abbr ‘B’] \\
      ‘?r. 0 < r /\ seminorm q m v = Normal r’
         by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] >> POP_ORW \\
      ‘r <> 0’ by rw [REAL_LT_IMP_NE] \\
       rw [extreal_div_def, extreal_inv_def] \\
       Know ‘!x. (abs (v x) * Normal (inv r)) powr q =
                 (abs (v x)) powr q * Normal (inv r) powr q’
       >- (Q.X_GEN_TAC ‘x’ >> MATCH_MP_TAC mul_powr \\
           rw [extreal_of_num_def, extreal_le_eq, REAL_LT_IMP_LE]) >> Rewr' \\
      ‘?Q. 0 < Q /\ q = Normal Q’
         by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] >> POP_ORW \\
      ‘Q <> 0’ by rw [REAL_LT_IMP_NE] \\
      ‘0 < inv r’ by rw [REAL_INV_POS] \\
       rw [extreal_div_def, extreal_inv_def, extreal_mul_def, normal_powr, GSYM mul_assoc] \\
       MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL \\
       qexistsl_tac [‘\x. abs (v x) powr Normal Q’, ‘inv Q * inv r powr Q’] \\
       RW_TAC std_ss [] >| (* 3 subgoals *)
       [ (* goal 4.1 (of 3) *)
         simp [],
         (* goal 4.2 (of 3) *)
         MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS_POWR \\
        ‘0 <= Q’ by rw [REAL_LT_IMP_LE] \\
         rw [extreal_of_num_def, extreal_le_eq],
         (* goal 4.3 (of 3) *)
         PROVE_TAC [mul_comm] ] ])
 >> Rewr'
 >> Suff ‘pos_fn_integral m (\x. A x powr p / p) = inv p /\
          pos_fn_integral m (\x. B x powr q / q) = inv q’
 >- (Rewr' >> art [] \\
    ‘?r. 0 < r /\ seminorm p m u * seminorm q m v = Normal r’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] >> POP_ORW \\
     Know ‘pos_fn_integral m (\x. abs (u x * v x)) / Normal r <= 1 <=>
           pos_fn_integral m (\x. abs (u x * v x)) <= 1 * Normal r’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC le_ldiv >> art []) >> Rewr' >> rw [])
 >> Know ‘pos_fn_integral m (\x. A x powr p / p) =
          inv p * pos_fn_integral m (\x. A x powr p)’
 >- (‘?r. 0 < r /\ p = Normal r’
        by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] >> POP_ORW \\
     ‘r <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] \\
     rw [extreal_div_def, extreal_inv_def, Once mul_comm] \\
     HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [powr_pos] \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art [])
 >> Rewr'
 >> Know ‘pos_fn_integral m (\x. B x powr q / q) =
          inv q * pos_fn_integral m (\x. B x powr q)’
 >- (‘?r. 0 < r /\ q = Normal r’
        by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] >> POP_ORW \\
     ‘r <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] \\
     rw [extreal_div_def, extreal_inv_def, Once mul_comm] \\
     HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [powr_pos] \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art [])
 >> Rewr'
 >> Suff ‘pos_fn_integral m (\x. A x powr p) = 1 /\
          pos_fn_integral m (\x. B x powr q) = 1’ >- rw []
 (* final stage *)
 >> FULL_SIMP_TAC std_ss [Abbr ‘A’, Abbr ‘B’]
 >> NTAC 5 (POP_ASSUM K_TAC) (* all about ‘seminorm p m u * seminorm q m v’ *)
 >> CONJ_TAC (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      Know ‘!x. abs (u x) / seminorm p m u = abs (u x) * inv (seminorm p m u)’
      >- (‘?r. 0 < r /\ seminorm p m u = Normal r’
            by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] >> POP_ORW \\
          ‘r <> 0’ by rw [REAL_LT_IMP_NE] \\
          rw [extreal_div_def]) >> Rewr' \\
      Know ‘!x. (abs (u x) * inv (seminorm p m u)) powr p =
                (abs (u x)) powr p * (inv (seminorm p m u)) powr p’
      >- (Q.X_GEN_TAC ‘x’ \\
          MATCH_MP_TAC mul_powr >> rw [le_inv]) >> Rewr' \\
      Know ‘inv (seminorm p m u) powr p = inv ((seminorm p m u) powr p)’
      >- (MATCH_MP_TAC inv_powr >> art []) >> Rewr' \\
      Know ‘seminorm p m u powr p = pos_fn_integral m (\x. abs (u x) powr p)’
      >- (MATCH_MP_TAC seminorm_powr >> art []) >> Rewr' \\
      Q.ABBREV_TAC ‘c = pos_fn_integral m (\x. abs (u x) powr p)’ \\
      Know ‘c <> 0’
      >- (SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE []) \\
          Suff ‘seminorm p m u = 0’ >- PROVE_TAC [] \\
          Q.PAT_X_ASSUM ‘seminorm p m u <> 0’ K_TAC \\
         ‘0 < inv p’ by PROVE_TAC [inv_pos'] \\
          ASM_SIMP_TAC std_ss [seminorm_normal, zero_rpow]) >> DISCH_TAC \\
      Know ‘inv c <> PosInf /\ inv c <> NegInf’
      >- (MATCH_MP_TAC inv_not_infty >> art []) >> STRIP_TAC \\
      ONCE_REWRITE_TAC [mul_comm] \\
      Know ‘0 <= c’
      >- (Q.UNABBREV_TAC ‘c’ \\
          MATCH_MP_TAC pos_fn_integral_pos >> rw [powr_pos]) >> DISCH_TAC \\
     ‘0 < c’ by PROVE_TAC [le_lt] \\
     ‘0 <= inv c’ by PROVE_TAC [le_inv] \\
      Know ‘pos_fn_integral m (\x. inv c * abs (u x) powr p) =
            inv c * pos_fn_integral m (\x. abs (u x) powr p)’
      >- (‘?r. 0 <= r /\ inv c = Normal r’
            by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_le_eq] >> POP_ORW \\
          HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [powr_pos]) >> Rewr' \\
      simp [] (* inv c * c = 1 *) \\
      MATCH_MP_TAC mul_linv_pos >> art [] \\
      Q.UNABBREV_TAC ‘c’ \\
      METIS_TAC [lp_space_alt_finite],
      (* goal 2 (of 2), symmetric with above *)
      Know ‘!x. abs (v x) / seminorm q m v = abs (v x) * inv (seminorm q m v)’
      >- (‘?r. 0 < r /\ seminorm q m v = Normal r’
            by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] >> POP_ORW \\
          ‘r <> 0’ by rw [REAL_LT_IMP_NE] \\
          rw [extreal_div_def]) >> Rewr' \\
      Know ‘!x. (abs (v x) * inv (seminorm q m v)) powr q =
                (abs (v x)) powr q * (inv (seminorm q m v)) powr q’
      >- (Q.X_GEN_TAC ‘x’ \\
          MATCH_MP_TAC mul_powr >> rw [le_inv]) >> Rewr' \\
      Know ‘inv (seminorm q m v) powr q = inv ((seminorm q m v) powr q)’
      >- (MATCH_MP_TAC inv_powr >> art []) >> Rewr' \\
      Know ‘seminorm q m v powr q = pos_fn_integral m (\x. abs (v x) powr q)’
      >- (MATCH_MP_TAC seminorm_powr >> art []) >> Rewr' \\
      Q.ABBREV_TAC ‘c = pos_fn_integral m (\x. abs (v x) powr q)’ \\
      Know ‘c <> 0’
      >- (SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE []) \\
          Suff ‘seminorm q m v = 0’ >- PROVE_TAC [] \\
          Q.PAT_X_ASSUM ‘seminorm q m v <> 0’ K_TAC \\
         ‘0 < inv q’ by PROVE_TAC [inv_pos'] \\
          ASM_SIMP_TAC std_ss [seminorm_normal, zero_rpow]) >> DISCH_TAC \\
      Know ‘inv c <> PosInf /\ inv c <> NegInf’
      >- (MATCH_MP_TAC inv_not_infty >> art []) >> STRIP_TAC \\
      ONCE_REWRITE_TAC [mul_comm] \\
      Know ‘0 <= c’
      >- (Q.UNABBREV_TAC ‘c’ \\
          MATCH_MP_TAC pos_fn_integral_pos >> rw [powr_pos]) >> DISCH_TAC \\
     ‘0 < c’ by PROVE_TAC [le_lt] \\
     ‘0 <= inv c’ by PROVE_TAC [le_inv] \\
      Know ‘pos_fn_integral m (\x. inv c * abs (v x) powr q) =
            inv c * pos_fn_integral m (\x. abs (v x) powr q)’
      >- (‘?r. 0 <= r /\ inv c = Normal r’
            by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_le_eq] >> POP_ORW \\
          HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [powr_pos]) >> Rewr' \\
      simp [] (* inv c * c = 1 *) \\
      MATCH_MP_TAC mul_linv_pos >> art [] \\
      Q.UNABBREV_TAC ‘c’ \\
      METIS_TAC [lp_space_alt_finite] ]
QED

(* A more convenient version (only the 2nd part) using ‘pos_fn_integral’ *)
Theorem Hoelder_inequality' :
    !m u v p q. measure_space m /\ 0 < p /\ 0 < q /\ inv(p) + inv(q) = 1 /\
                u IN lp_space p m /\ v IN lp_space q m
            ==> pos_fn_integral m (\x. abs (u x * v x)) <= seminorm p m u * seminorm q m v
Proof
    rpt STRIP_TAC
 >> Suff ‘pos_fn_integral m (\x. abs (u x * v x)) = integral m (\x. abs (u x * v x))’
 >- METIS_TAC [Hoelder_inequality]
 >> MATCH_MP_TAC (GSYM integral_pos_fn)
 >> rw [abs_pos]
QED

(* Cauchy-Schwarz Inequality as a corollary of Hoelder's Inequality (p = q = 2)

   see, e.g., Corollary 13.3 (Cauchy-Schwarz inequality) [1, p.118]
 *)
Theorem Cauchy_Schwarz_inequality :
    !m u v. measure_space m /\ u IN L2_space m /\ v IN L2_space m ==>
            integrable m (\x. u x * v x) /\
            integral m (\x. abs (u x * v x)) <= seminorm 2 m u * seminorm 2 m v
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MATCH_MP_TAC Hoelder_inequality
 >> simp [inv_1over, half_double, GSYM ne_02]
QED

(* A more convenient version (only the 2nd part) using ‘pos_fn_integral’, ‘pow’ and
  ‘sqrt’ instead of ‘seminorm’, also with ‘abs’ eliminated inside ‘pow 2’.
 *)
Theorem Cauchy_Schwarz_inequality' :
    !m u v. measure_space m /\ u IN L2_space m /\ v IN L2_space m
        ==> pos_fn_integral m (\x. abs (u x * v x)) <=
            sqrt (pos_fn_integral m (\x. (u x) pow 2) *
                  pos_fn_integral m (\x. (v x) pow 2))
Proof
    rpt STRIP_TAC
 >> Know ‘pos_fn_integral m (\x. abs (u x * v x)) = integral m (\x. abs (u x * v x))’
 >- (MATCH_MP_TAC (GSYM integral_pos_fn) >> rw [abs_pos])
 >> Rewr'
 >> Suff ‘sqrt (pos_fn_integral m (\x. (u x) pow 2) *
                pos_fn_integral m (\x. (v x) pow 2)) =
          seminorm 2 m u * seminorm 2 m v’
 >- METIS_TAC [Cauchy_Schwarz_inequality]
 >> ASM_SIMP_TAC std_ss [seminorm_two]
 >> Q.ABBREV_TAC ‘A = pos_fn_integral m (\x. (u x) pow 2)’
 >> Q.ABBREV_TAC ‘B = pos_fn_integral m (\x. (v x) pow 2)’
 >> Know ‘0 <= A /\ 0 <= B’
 >- (RW_TAC std_ss [Abbr ‘A’, Abbr ‘B’] \\
     MATCH_MP_TAC pos_fn_integral_pos >> rw [le_pow2])
 >> RW_TAC std_ss [sqrt_mul]
QED

(* This is the first part of Minkowski's inequality

   NOTE: ‘0 < p’ doesn't hold for Minkowski's inequality but hold for this lemma.
 *)
Theorem lp_space_add :
    !p m u v. measure_space m /\ 0 < p /\ u IN lp_space p m /\ v IN lp_space p m
          ==> (\x. u x + v x) IN lp_space p m
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘0 <= p’ by PROVE_TAC [lt_imp_le]
 >> ‘p <> NegInf’ by PROVE_TAC [pos_not_neginf]
  (* special case: p = PosInf *)
 >> Cases_on ‘p = PosInf’
 >- (Q.PAT_X_ASSUM ‘u IN lp_space p m’ MP_TAC \\
     Q.PAT_X_ASSUM ‘v IN lp_space p m’ MP_TAC \\
     rw [lp_space_alt_infinite]
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD' \\
         qexistsl_tac [‘u’, ‘v’] >> simp []) \\
     Q.PAT_X_ASSUM ‘AE x::m. abs (v x) < c’ MP_TAC \\
     rename1 ‘AE x::m. abs (u x) < d’ \\
     Q.PAT_X_ASSUM ‘AE x::m. abs (u x) < d’ MP_TAC \\
     rw [AE_DEF] \\
     Q.EXISTS_TAC ‘d + c’ \\
     CONJ_TAC >- PROVE_TAC [lt_add] \\
     CONJ_TAC >- PROVE_TAC [add_not_infty] \\
     Q.EXISTS_TAC ‘N UNION N'’ \\
     rw [NULL_SET_UNION', GSYM extreal_add_def] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘abs (u x) + abs (v x)’ \\
     rw [lt_add2, abs_triangle_full])
 (* general case: p <> PosInf *)
 >> rw [lp_space_alt_finite]
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD' (* key result *) \\
     qexistsl_tac [‘u’, ‘v’] >> simp [] \\
     gs [lp_space_alt_finite, measure_space_def])
 >> REWRITE_TAC [lt_infty]
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC ‘pos_fn_integral m
                   (\x. 2 powr p * (abs (u x) powr p + abs (v x) powr p))’
 >> reverse CONJ_TAC (* easy goal first *)
 >- (gs [lp_space_alt_finite] \\
     Know ‘?c. 0 <= c /\ 2 powr p = Normal c’
     >- (‘?r. 0 < r /\ p = Normal r’
            by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] \\
         POP_ORW \\
         rw [extreal_of_num_def, normal_powr] \\
         MATCH_MP_TAC REAL_LT_IMP_LE \\
         MATCH_MP_TAC RPOW_POS_LT >> rw []) >> STRIP_TAC >> POP_ORW \\
     Know ‘pos_fn_integral m (\x. Normal c * (abs (u x) powr p + abs (v x) powr p)) =
           Normal c * pos_fn_integral m (\x. abs (u x) powr p + abs (v x) powr p)’
     >- (HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [] \\
         MATCH_MP_TAC le_add >> rw [powr_pos]) >> Rewr' \\
     Suff ‘pos_fn_integral m (\x. abs (u x) powr p + abs (v x) powr p) <> PosInf’
     >- (DISCH_TAC \\
         Know ‘pos_fn_integral m (\x. abs (u x) powr p + abs (v x) powr p) <> NegInf’
         >- (MATCH_MP_TAC pos_not_neginf \\
             MATCH_MP_TAC pos_fn_integral_pos >> rw [le_add, powr_pos]) \\
         DISCH_TAC \\
        ‘?r. pos_fn_integral m (\x. abs (u x) powr p + abs (v x) powr p) = Normal r’
           by METIS_TAC [extreal_cases] >> POP_ORW \\
         rw [extreal_mul_def, lt_infty]) \\
     Q.PAT_X_ASSUM ‘0 <= c’ K_TAC \\
     Know ‘pos_fn_integral m (\x. abs (u x) powr p + abs (v x) powr p) =
           pos_fn_integral m (\x. abs (u x) powr p) +
           pos_fn_integral m (\x. abs (v x) powr p)’
     >- (HO_MATCH_MP_TAC pos_fn_integral_add \\
         rw [powr_pos] \\ (* 2 subgoals, same tactics *)
         MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS_POWR >> rw []) >> Rewr' \\
     Know ‘pos_fn_integral m (\x. abs (u x) powr p) <> NegInf /\
           pos_fn_integral m (\x. abs (v x) powr p) <> NegInf’
     >- (CONJ_TAC \\ (* 2 subgoals, same tactics *)
         MATCH_MP_TAC pos_not_neginf \\
         MATCH_MP_TAC pos_fn_integral_pos >> rw [powr_pos]) >> STRIP_TAC \\
    ‘?a. pos_fn_integral m (\x. abs (u x) powr p) = Normal a’
       by METIS_TAC [extreal_cases] >> POP_ORW \\
    ‘?b. pos_fn_integral m (\x. abs (v x) powr p) = Normal b’
       by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_add_def])
 (* applying pos_fn_integral_mono_AE *)
 >> MATCH_MP_TAC pos_fn_integral_mono_AE
 >> rw [powr_pos]
 >- (MATCH_MP_TAC le_mul >> art [powr_pos] \\
     MATCH_MP_TAC le_add >> art [powr_pos])
 >> gs [lp_space_alt_finite]
 >> Know ‘null_set m {x | x IN m_space m /\ abs (u x) powr p = PosInf} /\
          null_set m {x | x IN m_space m /\ abs (v x) powr p = PosInf}’
 >- (CONJ_TAC (* 2 subgoals, same tactics *) \\
     HO_MATCH_MP_TAC pos_fn_integral_infty_null >> rw [powr_pos] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS_POWR >> rw [])
 >> rw [AE_DEF]
 >> Q.EXISTS_TAC ‘{x | x IN m_space m /\ abs (u x) powr p = PosInf} UNION
                  {x | x IN m_space m /\ abs (v x) powr p = PosInf}’
 >> CONJ_TAC >- (MATCH_MP_TAC (REWRITE_RULE [IN_APP] NULL_SET_UNION) >> art [])
 >> rw [GSPECIFICATION]
 >> Know ‘u x <> PosInf /\ u x <> NegInf /\ v x <> PosInf /\ v x <> NegInf’
 >- (rpt CONJ_TAC >> CCONTR_TAC \\
     gs [extreal_abs_def, infty_powr])
 >> STRIP_TAC
 >> ‘?a. u x = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> ‘?b. v x = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> rw [extreal_add_def]
 (* special cases *)
 >> Cases_on ‘a + b = 0’
 >- (rw [GSYM extreal_of_num_def, zero_rpow] \\
     MATCH_MP_TAC le_mul >> rw [powr_pos] \\
     MATCH_MP_TAC le_add >> rw [powr_pos])
 >> Cases_on ‘a = 0’
 >- (rw [GSYM extreal_of_num_def, zero_rpow] \\
     GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM mul_lone] \\
     MATCH_MP_TAC le_rmul_imp >> rw [powr_pos] \\
     MATCH_MP_TAC powr_ge_1 >> rw [extreal_of_num_def, extreal_le_eq])
 >> Cases_on ‘b = 0’
 >- (rw [GSYM extreal_of_num_def, zero_rpow] \\
     GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM mul_lone] \\
     MATCH_MP_TAC le_rmul_imp >> rw [powr_pos] \\
     MATCH_MP_TAC powr_ge_1 >> rw [extreal_of_num_def, extreal_le_eq])
 >> ‘?r. 0 < r /\ p = Normal r’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq]
 >> POP_ORW
 >> rw [extreal_abs_def]
 >> ‘0 < abs (a + b) /\ 0 < abs a /\ 0 < abs b’ by rw []
 >> rw [normal_powr, extreal_of_num_def, extreal_add_def, extreal_mul_def, extreal_le_eq]
 >> ONCE_REWRITE_TAC [REAL_MUL_COMM]
 (* below is real-only *)
 >> MATCH_MP_TAC REAL_LE_TRANS
 >> Q.EXISTS_TAC ‘(max (abs a powr r) (abs b powr r)) * 2 powr r’
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC REAL_LE_RMUL_IMP \\
     CONJ_TAC >- (MATCH_MP_TAC REAL_LT_IMP_LE \\
                  MATCH_MP_TAC RPOW_POS_LT >> rw []) \\
     rw [REAL_MAX_LE] (* 2 subgoals, same tactics *) \\
     MATCH_MP_TAC REAL_LT_IMP_LE \\
     MATCH_MP_TAC RPOW_POS_LT >> art [])
 >> Know ‘max (abs a powr r) (abs b powr r) = (max (abs a) (abs b)) powr r’
 >- (Cases_on ‘abs a <= abs b’
     >- (‘abs a powr r <= abs b powr r’ by rw [BASE_RPOW_LE] \\
         rw [max_def]) \\
    ‘~(abs a powr r <= abs b powr r)’ by rw [BASE_RPOW_LE] \\
     rw [max_def])
 >> Rewr'
 >> ‘0 < max (abs a) (abs b)’ by rw [REAL_LT_MAX]
 >> rw [GSYM RPOW_MUL]
 >> ‘0 < 2 * max (abs a) (abs b)’ by rw [REAL_LT_MUL]
 >> rw [BASE_RPOW_LE]
 >> MATCH_MP_TAC REAL_LE_TRANS
 >> Q.EXISTS_TAC ‘abs a + abs b’
 >> rw [ABS_TRIANGLE, GSYM REAL_DOUBLE]
 >> Cases_on ‘abs a <= abs b’ >> rw [max_def]
 >> FULL_SIMP_TAC std_ss [GSYM real_lt]
 >> MATCH_MP_TAC REAL_LT_IMP_LE >> art []
QED

(* Minkowski's Inequality (or triangle inequality of seminorm)

   see, e.g., Corollary 13.4 (Minkowski's inequality) [1, p.118]

   NOTE: This inequality does NOT hold when ‘0 < p < 1’, in which case the inequality
         became ‘seminorm p m u + seminorm p m v <= seminorm p m (\x. u x + v x)’,
         namely "Reversed Minkowski's Inequality" (less useful), which can be proven
         from the present Minkowski_inequality by considering u and (\x. 1 / v x).
 *)
Theorem Minkowski_inequality :
    !p m u v. measure_space m /\ 1 <= p /\ u IN lp_space p m /\ v IN lp_space p m
          ==> (\x. u x + v x) IN lp_space p m /\
              seminorm p m (\x. u x + v x) <= seminorm p m u + seminorm p m v
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘0 < p’ by PROVE_TAC [lt_01, lte_trans]
 >> STRONG_CONJ_TAC
 >- (MATCH_MP_TAC lp_space_add >> art [])
 >> DISCH_TAC
 (* special case *)
 >> Cases_on ‘p = PosInf’
 >- (POP_ASSUM (FULL_SIMP_TAC std_ss o wrap) \\
    ‘u IN measurable (m_space m,measurable_sets m) Borel /\
     v IN measurable (m_space m,measurable_sets m) Borel’ by fs [lp_space_def] \\
    ‘(AE x::m. abs (u x) <= seminorm PosInf m u) /\
     (AE x::m. abs (v x) <= seminorm PosInf m v)’
       by METIS_TAC [seminorm_infty_AE_bound] \\
     Q.ABBREV_TAC ‘cu = seminorm PosInf m u’ \\
     Q.ABBREV_TAC ‘cv = seminorm PosInf m v’ \\
     rw [seminorm_infty, inf_le'] \\
     MATCH_MP_TAC le_epsilon >> rpt STRIP_TAC \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     CONJ_TAC >- (MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC ‘e’ >> art [] \\
                  MATCH_MP_TAC le_addl_imp \\
                  MATCH_MP_TAC le_add \\
                 ‘0 < PosInf’ by rw [] \\
                  rw [seminorm_pos, Abbr ‘cu’, Abbr ‘cv’]) \\
     Q.ABBREV_TAC ‘P = \x. abs (u x + v x) < cu + cv + e’ \\
    ‘{x | x IN m_space m /\ cu + cv + e <= abs (u x + v x)} = {x | x IN m_space m /\ ~P x}’
        by rw [Abbr ‘P’, extreal_lt_def] >> POP_ORW \\
     Know ‘measure m {x | x IN m_space m /\ ~P x} = 0 <=> (AE x::m. P x)’
     >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC AE_iff_measurable >> rw [Abbr ‘P’, extreal_lt_def] \\
         Q.ABBREV_TAC ‘f = (\x. u x + v x)’ \\
        ‘sigma_algebra (measurable_space m)’ by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA] \\
        ‘f IN Borel_measurable (measurable_space m)’ by fs [lp_space_def] \\
         rw [le_abs_bounds] \\
        ‘{x | x IN m_space m /\ (f x <= -(cu + cv + e) \/ cu + cv + e <= f x)} =
           ({x | f x <= -(cu + cv + e)} INTER m_space m) UNION
           ({x | cu + cv + e <= f x} INTER m_space m)’ by SET_TAC [] >> POP_ORW \\
         MATCH_MP_TAC MEASURE_SPACE_UNION >> art [] \\
         METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> Rewr' \\
     simp [Abbr ‘P’] \\
  (* applying abs_triangle *)
    ‘0 < PosInf’ by rw [] \\
    ‘cu <> PosInf /\ cu <> NegInf’ by METIS_TAC [seminorm_not_infty] \\
    ‘cv <> PosInf /\ cv <> NegInf’ by METIS_TAC [seminorm_not_infty] \\
     Q.PAT_X_ASSUM ‘AE x::m. abs (u x) <= cu’ MP_TAC \\
     Q.PAT_X_ASSUM ‘AE x::m. abs (v x) <= cv’ MP_TAC \\
     rw [AE_DEF] \\
     Q.EXISTS_TAC ‘N UNION N'’ \\
     CONJ_TAC >- (MATCH_MP_TAC NULL_SET_UNION' >> art []) \\
     rw [] >> MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘cu + cv’ \\
     reverse CONJ_TAC >- (MATCH_MP_TAC lt_addr_imp >> art [] \\
                          METIS_TAC [add_not_infty]) \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC ‘abs (u x) + abs (v x)’ \\
     reverse CONJ_TAC >- (MATCH_MP_TAC le_add2 >> rw []) \\
     MATCH_MP_TAC abs_triangle \\
    ‘abs (u x) <= cu /\ abs (v x) <= cv’ by PROVE_TAC [] \\
     CCONTR_TAC >> FULL_SIMP_TAC bool_ss [] \\
     fs [extreal_abs_def, le_infty])
 (* general case *)
 >> ‘p <> 0’ by PROVE_TAC [lt_imp_ne]
 >> ‘0 <= p’ by rw [lt_imp_le]
 >> ‘p <> NegInf’ by rw [pos_not_neginf]
 >> ‘0 <= p - 1’ by rw [GSYM sub_zero_le]
 >> Know ‘pos_fn_integral m (\x. abs (u x + v x) powr (1 + (p - 1))) =
          pos_fn_integral m (\x. abs (u x + v x) powr 1 * abs (u x + v x) powr (p - 1))’
 >- (MATCH_MP_TAC pos_fn_integral_cong >> rw [powr_pos]
     >- (MATCH_MP_TAC le_mul >> rw [powr_pos]) \\
     MATCH_MP_TAC powr_add >> rw [abs_pos, sub_not_infty])
 >> simp [powr_1, abs_pos, sub_add2]
 >> DISCH_TAC
 (* applying abs_triangle *)
 >> Know ‘pos_fn_integral m (\x. abs (u x + v x) powr p) <=
          pos_fn_integral m (\x. (abs (u x) + abs (v x)) * abs (u x + v x) powr (p - 1))’
 >- (POP_ORW \\
     MATCH_MP_TAC pos_fn_integral_mono_AE \\
     rw [le_mul, le_add, abs_pos, powr_pos] \\
     gs [lp_space_alt_finite] \\
     Know ‘null_set m {x | x IN m_space m /\ abs (u x) powr p = PosInf} /\
           null_set m {x | x IN m_space m /\ abs (v x) powr p = PosInf}’
     >- (CONJ_TAC (* 2 subgoals, same tactics *) \\
         HO_MATCH_MP_TAC pos_fn_integral_infty_null >> rw [powr_pos] \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS_POWR >> rw []) \\
     rw [AE_DEF] \\
     Q.EXISTS_TAC ‘{x | x IN m_space m /\ abs (u x) powr p = PosInf} UNION
                   {x | x IN m_space m /\ abs (v x) powr p = PosInf}’ \\
     CONJ_TAC >- (MATCH_MP_TAC (REWRITE_RULE [IN_APP] NULL_SET_UNION) >> art []) \\
     rw [GSPECIFICATION] \\
     MATCH_MP_TAC le_rmul_imp >> simp [powr_pos] \\
     Know ‘u x <> PosInf /\ u x <> NegInf /\ v x <> PosInf /\ v x <> NegInf’
     >- (rpt CONJ_TAC >> CCONTR_TAC \\
         gs [extreal_abs_def, infty_powr]) >> STRIP_TAC \\
     MATCH_MP_TAC abs_triangle >> art [])
 >> POP_ASSUM K_TAC
 >> Know ‘!x. (abs (u x) + abs (v x)) * abs (u x + v x) powr (p - 1) =
               abs (u x) * abs (u x + v x) powr (p - 1) +
               abs (v x) * abs (u x + v x) powr (p - 1)’
 >- (Q.X_GEN_TAC ‘x’ \\
     MATCH_MP_TAC add_rdistrib >> DISJ1_TAC >> rw [abs_pos])
 >> Rewr'
 (* applying pos_fn_integral_add *)
 >> Know ‘pos_fn_integral m
           (\x. abs (u x) * abs (u x + v x) powr (p - 1) +
                abs (v x) * abs (u x + v x) powr (p - 1)) =
          pos_fn_integral m (\x. abs (u x) * abs (u x + v x) powr (p - 1)) +
          pos_fn_integral m (\x. abs (v x) * abs (u x + v x) powr (p - 1))’
 >- (HO_MATCH_MP_TAC pos_fn_integral_add \\
     gs [lp_space_alt_finite] \\
     rw [le_mul, abs_pos, powr_pos] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES \\
       qexistsl_tac [‘\x. abs (u x)’, ‘\x. abs (u x + v x) powr (p - 1)’] \\
       rw [] >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS \\
                 Q.EXISTS_TAC ‘u’ >> fs [measure_space_def]) \\
       HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS_POWR >> rw [sub_not_infty] \\
       MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD' \\
       qexistsl_tac [‘u’, ‘v’] >> fs [measure_space_def],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES \\
       qexistsl_tac [‘\x. abs (v x)’, ‘\x. abs (u x + v x) powr (p - 1)’] \\
       rw [] >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS \\
                 Q.EXISTS_TAC ‘v’ >> fs [measure_space_def]) \\
       HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS_POWR >> rw [sub_not_infty] \\
       MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD' \\
       qexistsl_tac [‘u’, ‘v’] >> fs [measure_space_def] ])
 >> Rewr'
 (* special case *)
 >> Cases_on ‘p = 1’
 >- rw [sub_refl, abs_pos, powr_1, seminorm_one, o_DEF]
 >> ‘1 < p’ by rw [lt_le]
 >> ‘0 < p - 1’ by PROVE_TAC [sub_zero_lt]
 >> ‘p - 1 <> 0’ by PROVE_TAC [lt_imp_ne]
 >> Know ‘p - 1 <> PosInf /\ p - 1 <> NegInf’
 >- (‘?r. p = Normal r’ by METIS_TAC [extreal_cases] \\
     rw [extreal_of_num_def, extreal_sub_def])
 >> STRIP_TAC
 >> ‘0 < inv (p - 1)’ by rw [inv_pos_eq]
 >> ‘inv (p - 1) <> 0’ by PROVE_TAC [lt_imp_ne]
 (* ‘q’ and its properties *)
 >> Q.ABBREV_TAC ‘q = p / (p - 1)’
 >> Know ‘(p - 1) * q = p’
 >- (rw [Abbr ‘q’, div_eq_mul_rinv] \\
     GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [mul_comm] \\
     rw [GSYM mul_assoc, mul_linv])
 >> DISCH_TAC
 >> Know ‘inv p + inv q = 1’
 >- (rw [Abbr ‘q’, div_eq_mul_rinv, inv_mul, inv_inv] \\
     rw [sub_ldistrib, inv_not_infty, mul_linv_pos] \\
     rw [sub_add2, inv_not_infty])
 >> DISCH_TAC
 >> Know ‘1 <= q’
 >- (Q.UNABBREV_TAC ‘q’ \\
     Know ‘1 <= p / (p - 1) <=> 1 * (p - 1) <= p’
     >- (‘?r. 0 < r /\ p - 1 = Normal r’
            by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq] >> POP_ORW \\
         MATCH_MP_TAC (GSYM le_rdiv) >> art []) >> Rewr' \\
     rw [sub_le_eq, le_addr])
 >> DISCH_TAC
 >> ‘0 < q’ by PROVE_TAC [lte_trans, lt_01]
 >> ‘q <> 0’ by PROVE_TAC [lt_imp_ne]
 >> Know ‘q <> PosInf’
 >- (rw [Abbr ‘q’, div_eq_mul_rinv] \\
    ‘?r. r <> 0 /\ p - 1 = Normal r’
        by METIS_TAC [extreal_cases, extreal_of_num_def] >> POP_ORW \\
    ‘?z. p = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     rw [extreal_inv_eq, extreal_mul_def])
 >> DISCH_TAC
 (* ‘f’ and its properties *)
 >> Q.ABBREV_TAC ‘f = \x. abs (u x + v x) powr (p - 1)’
 >> ‘!x. 0 <= f x’ by rw [Abbr ‘f’, powr_pos]
 >> ‘!x. abs (f x) = f x’ by rw [abs_refl]
 >> RW_TAC std_ss []
 >> Know ‘f IN lp_space q m’
 >- (gs [lp_space_alt_finite, Abbr ‘f’] \\
     CONJ_TAC
     >- (HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS_POWR >> rw [sub_not_infty]) \\
    ‘!x. abs (abs (u x + v x) powr (p - 1)) = abs (u x + v x) powr (p - 1)’
       by rw [abs_refl] >> POP_ORW \\
     rw [powr_powr])
 >> DISCH_TAC
 (* applying Hoelder_inequality' *)
 >> Know ‘pos_fn_integral m (\x. abs (u x * f x)) <= seminorm p m u * seminorm q m f’
 >- (MATCH_MP_TAC Hoelder_inequality' >> art [])
 >> Know ‘pos_fn_integral m (\x. abs (v x * f x)) <= seminorm p m v * seminorm q m f’
 >- (MATCH_MP_TAC Hoelder_inequality' >> art [])
 >> rw [abs_mul]
 >> Know ‘pos_fn_integral m (\x. abs (u x + v x) powr p) <=
          seminorm p m u * seminorm q m f + seminorm p m v * seminorm q m f’
 >- (MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC ‘pos_fn_integral m (\x. abs (u x) * f x) +
                   pos_fn_integral m (\x. abs (v x) * f x)’ >> art [] \\
     MATCH_MP_TAC le_add2 >> art [])
 >> NTAC 2 (POP_ASSUM K_TAC)
 >> Q.PAT_X_ASSUM ‘pos_fn_integral m (\x. abs (u x + v x) powr p) <= A + B’ K_TAC
 >> DISCH_TAC
 (* applying seminorm_eq_0 *)
 >> Cases_on ‘seminorm q m f = 0’
 >- (gs [lp_space_alt_finite, seminorm_eq_0] \\
     Suff ‘seminorm p m (\x. u x + v x) = 0’
     >- (Rewr' >> MATCH_MP_TAC le_add >> rw [seminorm_pos]) \\
     Know ‘seminorm p m (\x. u x + v x) = 0 <=> AE x::m. u x + v x = 0’
     >- (HO_MATCH_MP_TAC seminorm_eq_0 >> art []) >> Rewr' \\
     POP_ASSUM MP_TAC \\
     rw [AE_DEF, Abbr ‘f’] \\
     Q.EXISTS_TAC ‘N’ >> rw [] \\
     Q.PAT_X_ASSUM ‘!x. x IN m_space m /\ x NOTIN N ==> P’ (MP_TAC o (Q.SPEC ‘x’)) \\
    ‘0 <= abs (u x + v x)’ by rw [abs_pos] \\
     RW_TAC std_ss [powr_eq_0, abs_eq_0])
 >> ‘0 <= seminorm q m f’ by rw [seminorm_pos]
 >> ‘0 < seminorm q m f’ by rw [lt_le]
 >> Know ‘seminorm p m (\x. u x + v x) <= seminorm p m u + seminorm p m v <=>
          seminorm p m (\x. u x + v x) * seminorm q m f <=
         (seminorm p m u + seminorm p m v) * seminorm q m f’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC le_rmul >> PROVE_TAC [seminorm_not_infty])
 >> Rewr'
 >> Know ‘(seminorm p m u + seminorm p m v) * seminorm q m f =
           seminorm p m u * seminorm q m f + seminorm p m v * seminorm q m f’
 >- (MATCH_MP_TAC add_rdistrib >> DISJ1_TAC >> rw [seminorm_pos])
 >> Rewr'
 >> Suff ‘seminorm p m (\x. u x + v x) * seminorm q m f =
          pos_fn_integral m (\x. abs (u x + v x) powr p)’ >- rw []
 >> Q.PAT_X_ASSUM ‘pos_fn_integral m (\x. abs (u x + v x) powr p) <= P’ K_TAC
 (* final stage *)
 >> rw [Abbr ‘f’, seminorm_normal]
 >> ‘!x. abs (abs (u x + v x) powr (p - 1)) = abs (u x + v x) powr (p - 1)’
       by rw [abs_refl, powr_pos, abs_pos] >> POP_ORW
 >> rw [powr_powr]
 >> Q.ABBREV_TAC ‘A = pos_fn_integral m (\x. abs (u x + v x) powr p)’
 >> Know ‘0 <= A’
 >- (Q.UNABBREV_TAC ‘A’ \\
     MATCH_MP_TAC pos_fn_integral_pos >> rw [powr_pos])
 >> DISCH_TAC
 >> ‘A = A powr (inv p + inv q)’ by rw [powr_1]
 >> POP_ASSUM (fn th => GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [th])
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> MATCH_MP_TAC powr_add
 >> simp [inv_not_infty]
 >> CONJ_TAC (* 2 subgoals, same tactics *)
 >> MATCH_MP_TAC lt_imp_le
 >> MATCH_MP_TAC inv_pos' >> art []
QED

Theorem Minkowski_inequality' :
    !p m u v. measure_space m /\ 1 <= p /\ u IN lp_space p m /\ v IN lp_space p m
          ==> seminorm p m (\x. u x + v x) <= seminorm p m u + seminorm p m v
Proof
    rpt STRIP_TAC
 >> drule Minkowski_inequality >> rw []
QED

(* NOTE: ‘u IN measurable (m_space m,measurable_sets m) Borel’, e.g., and
  ‘AE x::m. u x = v x’ together do NOT implies ‘v IN measurable ...’ unless
   the measure space is complete, cf. IN_MEASURABLE_BOREL_AE_EQ.
 *)
Theorem seminorm_cong_AE :
    !m u v p. measure_space m /\ 0 < p /\
              u IN measurable (m_space m,measurable_sets m) Borel /\
              v IN measurable (m_space m,measurable_sets m) Borel /\
             (AE x::m. u x = v x) ==> seminorm p m u = seminorm p m v
Proof
    rpt STRIP_TAC
 >> Cases_on ‘p = PosInf’
 >- (rw [seminorm_infty_alt] \\
     Suff ‘!c. (AE x::m. abs (u x) < c) <=> (AE x::m. abs (v x) < c)’ >- rw [] \\
     Q.PAT_X_ASSUM ‘AE x::m. u x = v x’ MP_TAC \\
     rw [AE_DEF] >> rename1 ‘null_set m N0’ \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC ‘N UNION N0’ >> rw [NULL_SET_UNION'] \\
      ‘v x = u x’ by PROVE_TAC [] >> POP_ORW \\
       FIRST_X_ASSUM MATCH_MP_TAC >> art [],
       (* goal 2 (of 2) *)
       Q.EXISTS_TAC ‘N UNION N0’ >> rw [NULL_SET_UNION'] ])
 >> rw [seminorm_normal]
 >> Suff ‘pos_fn_integral m (\x. abs (u x) powr p) =
          pos_fn_integral m (\x. abs (v x) powr p)’ >- rw []
 >> MATCH_MP_TAC pos_fn_integral_cong_AE >> rw [powr_pos]
 >> HO_MATCH_MP_TAC AE_subset
 >> Q.EXISTS_TAC ‘\x. u x = v x’ >> rw []
QED

Theorem seminorm_cong :
    !m u v p. measure_space m /\ 0 < p /\
             (u IN measurable (m_space m,measurable_sets m) Borel \/
              v IN measurable (m_space m,measurable_sets m) Borel) /\
             (!x. x IN m_space m ==> u x = v x) ==> seminorm p m u = seminorm p m v
Proof
    rpt STRIP_TAC
 >> ‘u IN measurable (m_space m,measurable_sets m) Borel /\
     v IN measurable (m_space m,measurable_sets m) Borel’
      by METIS_TAC [IN_MEASURABLE_BOREL_EQ]
 >> MATCH_MP_TAC seminorm_cong_AE
 >> rw [AE_DEF]
 >> Q.EXISTS_TAC ‘{}’ >> rw [NULL_SET_EMPTY]
QED

Theorem lp_space_cong :
    !p m u v. measure_space m /\ 0 < p /\ (!x. x IN m_space m ==> u x = v x) ==>
             (u IN lp_space p m <=> v IN lp_space p m)
Proof
    rpt STRIP_TAC
 >> rw [lp_space_alt_seminorm]
 >> EQ_TAC >> rpt STRIP_TAC
 >> ‘u IN measurable (m_space m,measurable_sets m) Borel /\
     v IN measurable (m_space m,measurable_sets m) Borel’
      by METIS_TAC [IN_MEASURABLE_BOREL_EQ]
 (* 2 subgoals, same tactics *)
 >> (Suff ‘seminorm p m u = seminorm p m v’ >- (DISCH_THEN (fs o wrap)) \\
     MATCH_MP_TAC seminorm_cong >> art [])
QED

Theorem lp_space_cong_AE :
    !p m u v. measure_space m /\ 0 < p /\
              u IN Borel_measurable (measurable_space m) /\
              v IN Borel_measurable (measurable_space m) /\
             (AE x::m. u x = v x) ==> (u IN lp_space p m <=> v IN lp_space p m)
Proof
    rpt STRIP_TAC
 >> rw [lp_space_alt_seminorm]
 >> Suff ‘seminorm p m u = seminorm p m v’ >- rw []
 >> MATCH_MP_TAC seminorm_cong_AE >> art []
QED

Theorem seminorm_zero :
    !p m. measure_space m /\ 0 < p ==> seminorm p m (\x. 0) = 0
Proof
    rpt STRIP_TAC
 >> Know ‘(\x. 0) IN measurable (measurable_space m) Borel’
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST \\
     Q.EXISTS_TAC ‘0’ >> fs [measure_space_def])
 >> DISCH_TAC
 >> Cases_on ‘p = PosInf’
 >- (rw [seminorm_infty_alt, inf_eq'] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC lt_imp_le >> art [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC le_epsilon >> rw [] \\
       FIRST_X_ASSUM MATCH_MP_TAC >> rw [AE_T] ])
 >> ‘0 < inv p’ by PROVE_TAC [inv_pos']
 >> rw [seminorm_normal, zero_rpow, pos_fn_integral_zero]
QED

Theorem seminorm_cmul :
    !p m u r. measure_space m /\ 0 < p /\
              u IN measurable (measurable_space m) Borel ==>
              seminorm p m (\x. Normal r * u x) = Normal (abs r) * seminorm p m u
Proof
    rpt STRIP_TAC
 >> Cases_on ‘r = 0’ >- rw [seminorm_zero, normal_0]
 >> Know ‘(\x. Normal r * u x) IN measurable (measurable_space m) Borel’
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL \\
     qexistsl_tac [‘u’, ‘r’] >> fs [measure_space_def])
 >> DISCH_TAC
 >> Cases_on ‘p = PosInf’
 >- (rw [seminorm_infty_alt, abs_mul, extreal_abs_def] \\
    ‘!x c. Normal (abs r) * abs (u x) = abs (u x) * Normal (abs r)’
        by PROVE_TAC [mul_comm] >> POP_ORW \\
     Know ‘!x c. abs (u x) * Normal (abs r) < c <=> abs (u x) < c / Normal (abs r)’
     >- (rpt GEN_TAC \\
         ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC lt_rdiv >> rw [abs_gt_0]) >> Rewr' \\
     Know ‘{c | 0 < c /\ AE x::m. abs (u x) < c / Normal (abs r)} =
           {d * Normal (abs r) | 0 < d /\ AE y::m. abs (u y) < d}’
     >- (rw [Once EXTENSION] >> EQ_TAC >> rw [] >| (* 3 subgoals *)
         [ (* goal 1 (of 3) *)
           Q.EXISTS_TAC ‘x / Normal (abs r)’ >> rw [] >| (* 2 subgoals *)
           [ MATCH_MP_TAC div_mul_refl >> rw [],
             MATCH_MP_TAC lt_div >> rw [abs_gt_0] ],
           (* goal 2 (of 3) *)
           MATCH_MP_TAC lt_mul >> rw [],
           (* goal 3 (of 3) *)
           Suff ‘d * Normal (abs r) / Normal (abs r) = d’ >- rw [] \\
           ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
           MATCH_MP_TAC mul_div_refl >> rw [] ]) >> Rewr' \\
     Suff ‘!P. inf {d * Normal (abs r) | 0 < d /\ P d} =
               Normal (abs r) * inf {c | 0 < c /\ P c}’ >- rw [] \\
     MATCH_MP_TAC inf_cmul >> rw [abs_gt_0])
 (* stage work *)
 >> rw [seminorm_normal, abs_mul, extreal_abs_def]
 >> Know ‘!x. (Normal (abs r) * abs (u x)) powr p =
              Normal (abs r) powr p * abs (u x) powr p’
 >- (Q.X_GEN_TAC ‘x’ >> MATCH_MP_TAC mul_powr >> rw [])
 >> Rewr'
 >> ‘p <> NegInf’ by PROVE_TAC [pos_not_neginf, lt_imp_le]
 >> ‘?z. 0 < z /\ p = Normal z’
       by METIS_TAC [extreal_cases, extreal_of_num_def, extreal_lt_eq]
 >> POP_ORW
 (* applying IN_MEASURABLE_BOREL_ABS_POWR *)
 >> Know ‘(\x. abs (u x) powr Normal z) IN Borel_measurable (measurable_space m)’
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS_POWR \\
     rw [REAL_LT_IMP_LE])
 >> DISCH_TAC
 >> Know ‘pos_fn_integral m (\x. Normal (abs r) powr Normal z * abs (u x) powr Normal z) =
          Normal (abs r) powr Normal z * pos_fn_integral m (\x. abs (u x) powr Normal z)’
 >- (Know ‘Normal (abs r) powr (Normal z) = Normal (abs r powr z)’
     >- (MATCH_MP_TAC normal_powr >> rw []) >> Rewr' \\
     HO_MATCH_MP_TAC pos_fn_integral_cmul >> rw [powr_pos] \\
     MATCH_MP_TAC REAL_LT_IMP_LE \\
     MATCH_MP_TAC RPOW_POS_LT >> rw [])
 >> Rewr'
 (* final stage *)
 >> Q.ABBREV_TAC ‘y = pos_fn_integral m (\x. abs (u x) powr Normal z)’
 >> Know ‘0 <= y’
 >- (Q.UNABBREV_TAC ‘y’ \\
     MATCH_MP_TAC pos_fn_integral_pos >> rw [powr_pos])
 >> DISCH_TAC
 >> Know ‘(Normal (abs r) powr (Normal z) * y) powr inv (Normal z) =
          (Normal (abs r) powr (Normal z)) powr inv (Normal z) * y powr inv (Normal z)’
 >- (MATCH_MP_TAC mul_powr \\
    ‘Normal z <> 0’ by rw [REAL_LT_IMP_NE] \\
     rw [inv_pos', inv_not_infty, powr_pos])
 >> Rewr'
 >> Suff ‘(Normal (abs r) powr Normal z) powr inv (Normal z) = Normal (abs r)’ >- rw []
 >> Know ‘(Normal (abs r) powr Normal z) powr inv (Normal z) =
           Normal (abs r) powr (Normal z * inv (Normal z))’
 >- (MATCH_MP_TAC powr_powr \\
    ‘Normal z <> 0’ by rw [REAL_LT_IMP_NE] \\
     rw [inv_pos', inv_not_infty, powr_pos])
 >> Rewr'
 >> Suff ‘Normal z * inv (Normal z) = 1’
 >- (Rewr' >> rw [powr_1])
 >> ONCE_REWRITE_TAC [mul_comm]
 >> MATCH_MP_TAC mul_linv_pos >> rw []
QED

Theorem lp_space_cmul :
    !p m u r. measure_space m /\ 0 < p /\ u IN lp_space p m ==>
              (\x. Normal r * u x) IN lp_space p m
Proof
    rpt STRIP_TAC
 >> ‘seminorm p m u <> PosInf /\ seminorm p m u <> NegInf’
       by PROVE_TAC [seminorm_not_infty]
 >> ‘0 <= seminorm p m u’ by PROVE_TAC [seminorm_pos]
 >> ‘u IN Borel_measurable (measurable_space m)’ by fs [lp_space_def]
 >> Q.PAT_X_ASSUM ‘u IN lp_space p m’ MP_TAC
 >> rw [lp_space_alt_seminorm, seminorm_cmul, GSYM lt_infty]
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL \\
     qexistsl_tac [‘u’, ‘r’] >> fs [measure_space_def])
 >> ‘?z. seminorm p m u = Normal z’ by METIS_TAC [extreal_cases]
 >> rw [extreal_mul_eq]
QED

Theorem lp_space_add_cmul :
    !p m u v a b. measure_space m /\ 0 < p /\ u IN lp_space p m /\ v IN lp_space p m
              ==> (\x. Normal a * u x + Normal b * v x) IN lp_space p m
Proof
    rpt STRIP_TAC
 >> HO_MATCH_MP_TAC lp_space_add
 >> rw [lp_space_cmul]
QED

(* cf. lp_space_alt_finite, lp_space_alt_infinite *)
Theorem lp_space_AE_normal :
    !p m f. measure_space m /\ 0 < p /\ f IN lp_space p m ==>
            AE x::m. f x <> PosInf /\ f x <> NegInf
Proof
    rpt STRIP_TAC
 >> Cases_on ‘p = PosInf’
 >- (‘?c. 0 < c /\ c <> PosInf /\ AE x::m. abs (f x) < c’
        by METIS_TAC [lp_space_alt_infinite] \\
     POP_ASSUM MP_TAC >> rw [AE_DEF, abs_bounds_lt, lt_infty] \\
     Q.EXISTS_TAC ‘N’ >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC lt_trans >> Q.EXISTS_TAC ‘c’ >> rw [GSYM lt_infty],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC lt_trans >> Q.EXISTS_TAC ‘-c’ >> rw [GSYM lt_infty] \\
      ‘NegInf = -PosInf’ by rw [extreal_ainv_def] >> POP_ORW \\
       rw [eq_neg] ])
 >> ‘f IN Borel_measurable (measurable_space m) /\
     pos_fn_integral m (\x. abs (f x) powr p) <> PosInf’
       by METIS_TAC [lp_space_alt_finite]
 (* applying pos_fn_integral_infty_null *)
 >> Q.ABBREV_TAC ‘g = \x. abs (f x) powr p’
 >> Know ‘null_set m {x | x IN m_space m /\ g x = PosInf}’
 >- (MATCH_MP_TAC pos_fn_integral_infty_null >> art [] \\
     CONJ_TAC >- rw [Abbr ‘g’, powr_pos] \\
     Q.UNABBREV_TAC ‘g’ \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS_POWR >> rw [lt_imp_le])
 >> DISCH_TAC
 >> rw [AE_DEF]
 >> Q.EXISTS_TAC ‘{x | x IN m_space m /\ g x = PosInf}’
 >> rw [Abbr ‘g’] >> CCONTR_TAC (* 2 subgoals, same tactics *)
 >> gs [extreal_abs_def, infty_powr]
QED

Theorem lp_space_sub :
    !p m u v. measure_space m /\ 0 < p /\ u IN lp_space p m /\ v IN lp_space p m
          ==> (\x. u x - v x) IN lp_space p m
Proof
    rw [extreal_sub]
 >> HO_MATCH_MP_TAC lp_space_add >> art []
 >> ‘(\x. -v x) = (\x. Normal (-1) * v x)’
       by (rw [FUN_EQ_THM, GSYM extreal_ainv_def, GSYM neg_minus1, normal_1])
 >> POP_ORW
 >> MATCH_MP_TAC lp_space_cmul >> art []
QED

(* END *)
val _ = export_theory ();

(* References:

  [1] Schilling, R.L.: Measures, Integrals and Martingales (Second Edition).
      Cambridge University Press (2017).
  [2] Doob, J.L.: Stochastic processes. Wiley-Interscience (1990).
  [3] Doob, J.L.: What is a Martingale? Amer. Math. Monthly. 78(5), 451-463 (1971).
  [4] Pintacuda, N.: Probabilita'. Zanichelli, Bologna (1995).
  [5] Wikipedia: https://en.wikipedia.org/wiki/Leonida_Tonelli
  [6] Wikipedia: https://en.wikipedia.org/wiki/Guido_Fubini
 *)
