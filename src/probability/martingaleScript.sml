(* ------------------------------------------------------------------------- *)
(* The theory of martingales for sigma-finite measure spaces                 *)
(*                                                                           *)
(* Author: Chun Tian (2019)                                                  *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open pairTheory relationTheory optionTheory prim_recTheory arithmeticTheory
     pred_setTheory combinTheory realTheory realLib seqTheory transcTheory
     real_sigmaTheory posetTheory;

open hurdUtils util_probTheory extrealTheory sigma_algebraTheory measureTheory
     borelTheory lebesgueTheory;

val _ = new_theory "martingale";

(* "The theory of martingales as we know it now goes back to
    Doob and most of the material of this and the following chapter can be found in
    his seminal monograph [2] from 1953.

    We want to understand martingales as an analysis tool which will be useful
    for the study of L^p- and almost everywhere convergence and, in particular,
    for the further development of measure and integration theory. Our presentation
    differs somewhat from the standard way to introduce martingales - conditional
    expectations will be defined later in Chapter 22 - but the results and their
    proofs are pretty much the usual ones."

  -- Rene L. Schilling, "Measures, Integrals and Martingales" [1]

   "Martingale theory illustrates the history of mathematical probability: the
    basic definitions are inspired by crude notions of gambling, but the theory
    has become a sophisticated tool of modern abstract mathematics, drawing from
    and contributing to other field."

  -- J. L. Doob, "What is a Martingale?" [3] *)

(* ------------------------------------------------------------------------- *)
(*  Basic version of martingales (Chapter 17 of [1])                         *)
(* ------------------------------------------------------------------------- *)

val sub_sigma_algebra_def = Define
   `sub_sigma_algebra a b <=> sigma_algebra a /\ sigma_algebra b /\
                             (space a = space b) /\ (subsets a) SUBSET (subsets b)`;

(* sub_sigma_algebra is a partial-order between sigma-algebras *)
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

val SUB_SIGMA_ALGEBRA_MEASURE_SPACE = store_thm
  ("SUB_SIGMA_ALGEBRA_MEASURE_SPACE",
  ``!m a. measure_space m /\ sub_sigma_algebra a (m_space m,measurable_sets m) ==>
          measure_space (m_space m,subsets a,measure m)``,
    RW_TAC std_ss [sub_sigma_algebra_def, space_def, subsets_def]
 >> MATCH_MP_TAC MEASURE_SPACE_RESTRICTION
 >> Q.EXISTS_TAC `measurable_sets m`
 >> simp [MEASURE_SPACE_REDUCE]
 >> METIS_TAC [SPACE]);

(* `filtration A` is the set of all filtrations of A *)
val filtration_def = Define
   `filtration A (a :num -> 'a algebra) <=>
      (!n. sub_sigma_algebra (a n) A) /\
      (!i j. i <= j ==> subsets (a i) SUBSET subsets (a j))`;

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

val filtered_measure_space_def = Define
   `filtered_measure_space (sp,sts,m) a <=>
             measure_space (sp,sts,m) /\ filtration (sp,sts) a`;

val filtered_measure_space_alt = store_thm
  ("filtered_measure_space_alt",
  ``!m a. filtered_measure_space m a <=>
          measure_space m /\ filtration (m_space m,measurable_sets m) a``,
    rpt GEN_TAC
 >> Cases_on `m` >> Cases_on `r`
 >> REWRITE_TAC [filtered_measure_space_def, m_space_def, measurable_sets_def]);

(* `sigma_finite_FMS = sigma_finite_filtered_measure_space` *)
val sigma_finite_FMS_def = Define
   `sigma_finite_FMS (sp,sts,m) a <=>
    filtered_measure_space (sp,sts,m) a /\ sigma_finite (sp,subsets (a 0),m)`;

val sigma_finite_FMS_alt = store_thm
  ("sigma_finite_FMS_alt",
  ``!m a. sigma_finite_FMS m a <=>
          filtered_measure_space m a /\ sigma_finite (m_space m,subsets (a 0),measure m)``,
    rpt GEN_TAC
 >> Cases_on `m` >> Cases_on `r`
 >> REWRITE_TAC [sigma_finite_FMS_def, m_space_def, measure_def]);

(* all sub measure spaces of a sigma-finite fms are also sigma-finite *)
val SIGMA_FINITE_FMS_IMP = store_thm
  ("SIGMA_FINITE_FMS_IMP",
  ``!sp sts a m. sigma_finite_FMS (sp,sts,m) a ==> !n. sigma_finite (sp,subsets (a n),m)``,
 (* proof *)
    RW_TAC std_ss [sigma_finite_FMS_def, filtered_measure_space_def, filtration_def]
 >> Know `measure_space (sp,subsets (a 0),m) /\
          measure_space (sp,subsets (a n),m)`
 >- (CONJ_TAC \\ (* 2 subgoals, same tactics *)
     MATCH_MP_TAC
       (REWRITE_RULE [m_space_def, measurable_sets_def, measure_def]
                     (Q.SPEC `(sp,sts,m)` SUB_SIGMA_ALGEBRA_MEASURE_SPACE)) >> art [])
 >> STRIP_TAC
 >> POP_ASSUM (simp o wrap o (MATCH_MP SIGMA_FINITE_ALT))
 >> POP_ASSUM (fs o wrap o (MATCH_MP SIGMA_FINITE_ALT))
 >> Q.EXISTS_TAC `f`
 >> fs [IN_FUNSET, IN_UNIV, measurable_sets_def, m_space_def, measure_def]
 >> `0 <= n` by RW_TAC arith_ss []
 >> METIS_TAC [SUBSET_DEF]);

(* extended definition *)
val SIGMA_FINITE_FMS = store_thm
  ("SIGMA_FINITE_FMS",
  ``!sp sts a m. sigma_finite_FMS (sp,sts,m) a <=>
                 filtered_measure_space (sp,sts,m) a /\
                 !n. sigma_finite (sp,subsets (a n),m)``,
    rpt GEN_TAC >> EQ_TAC
 >- (DISCH_TAC >> IMP_RES_TAC SIGMA_FINITE_FMS_IMP \\
     fs [sigma_finite_FMS_def])
 >> RW_TAC std_ss [sigma_finite_FMS_def]);

(* the smallest sigma-algebra generated by all (a n) *)
val infty_sigma_algebra_def = Define
   `infty_sigma_algebra sp a = sigma sp (BIGUNION (IMAGE (\(i :num). subsets (a i)) UNIV))`;

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

(* `prob_martingale` will be the probability version of `martingale` *)
val martingale_def = Define
   `martingale m a u <=>
      sigma_finite_FMS m a /\ (!n. integrable m (u n)) /\
      !n s. s IN (subsets (a n)) ==>
           (integral m (\x. u (SUC n) x * indicator_fn s x) =
            integral m (\x. u n x * indicator_fn s x))`;

(* super-martingale: changed `=` with `<=` *)
val super_martingale_def = Define
   `super_martingale m a u <=>
      sigma_finite_FMS m a /\ (!n. integrable m (u n)) /\
      !n s. s IN (subsets (a n)) ==>
           (integral m (\x. u (SUC n) x * indicator_fn s x) <=
            integral m (\x. u n x * indicator_fn s x))`;

(* sub-martingale: integral (u n) <= integral (u (SUC n)), looks more natural *)
val sub_martingale_def = Define
   `sub_martingale m a u <=>
      sigma_finite_FMS m a /\ (!n. integrable m (u n)) /\
      !n s. s IN (subsets (a n)) ==>
           (integral m (\x. u n x * indicator_fn s x) <=
            integral m (\x. u (SUC n) x * indicator_fn s x))`;

(* u is a martingale if, and only if, it is both a sub- and a supermartingale *)
val MARTINGALE_BOTH_SUB_SUPER = store_thm
  ("MARTINGALE_BOTH_SUB_SUPER",
  ``!m a u. martingale m a u <=> sub_martingale m a u /\ super_martingale m a u``,
    RW_TAC std_ss [martingale_def, sub_martingale_def, super_martingale_def]
 >> EQ_TAC >> RW_TAC std_ss [le_refl]
 >> ASM_SIMP_TAC std_ss [GSYM le_antisym]);

(* ------------------------------------------------------------------------- *)
(*  General version of martingales with poset indexes (Chapter 19 of [1])    *)
(* ------------------------------------------------------------------------- *)

val POSET_NUM_LE = store_thm
  ("POSET_NUM_LE", ``poset (univ(:num),$<=)``,
    RW_TAC std_ss [poset_def]
 >- (Q.EXISTS_TAC `0` >> REWRITE_TAC [GSYM IN_APP, IN_UNIV])
 >- (MATCH_MP_TAC LESS_EQUAL_ANTISYM >> art [])
 >> MATCH_MP_TAC LESS_EQ_TRANS
 >> Q.EXISTS_TAC `y` >> art []);

(* below J is an index set, R is a partial order on J *)
val general_filtration_def = Define
   `general_filtration A a (J,R) <=>
      poset (J,R) /\ (!n. n IN J ==> sub_sigma_algebra (a n) A) /\
      (!i j. i IN J /\ j IN J /\ R i j ==> subsets (a i) SUBSET subsets (a j))`;

val TO_GENERAL_FILTRATION = store_thm
  ("TO_GENERAL_FILTRATION",
  ``!A a. filtration A a = general_filtration A a (univ(:num),$<=)``,
    RW_TAC std_ss [filtration_def, general_filtration_def, POSET_NUM_LE, IN_UNIV]);

val general_fms_def = Define
   `general_fms (sp,sts,m) a (J,R) <=>
             measure_space (sp,sts,m) /\ general_filtration (sp,sts) a (J,R)`;

val general_fms_alt = store_thm
  ("general_fms_alt",
  ``!sp sts m a. filtered_measure_space (sp,sts,m) a <=>
                 general_fms (sp,sts,m) a (univ(:num),$<=)``,
    RW_TAC std_ss [filtered_measure_space_def, general_fms_def,
                   TO_GENERAL_FILTRATION, POSET_NUM_LE, IN_UNIV]);

val sigma_finite_general_fms_def = Define
   `sigma_finite_general_fms (sp,sts,m) a (J,R) <=>
          general_fms (sp,sts,m) a (J,R) /\
          !n. n IN J ==> sigma_finite (sp,subsets (a n),m)`;

val SIGMA_FINITE_FMS_SIGMA_FINITE_FMS_I = store_thm
  ("SIGMA_FINITE_FMS_SIGMA_FINITE_FMS_I",
  ``!sp sts m a. sigma_finite_FMS (sp,sts,m) a <=>
                 sigma_finite_general_fms (sp,sts,m) a (univ(:num),$<=)``,
    RW_TAC std_ss [SIGMA_FINITE_FMS, sigma_finite_general_fms_def,
                   general_fms_alt, IN_UNIV]);

val infty_sigma_algebra_I_def = Define
   `infty_sigma_algebra_I sp a I = sigma sp (BIGUNION (IMAGE (\i. subsets (a i)) I))`;

(* `general_martingale m a u (univ(:num),$<=) = martingale m a u` *)
val general_martingale_def = Define
   `general_martingale m a u (J,R) <=>
      sigma_finite_general_fms m a (J,R) /\ (!n. n IN J ==> integrable m (u n)) /\
      !i j s. i IN J /\ j IN J /\ R i j /\ s IN (subsets (a i)) ==>
             (integral m (\x. u i x * indicator_fn s x) =
              integral m (\x. u j x * indicator_fn s x))`;

(* or "upwards directed" *)
val upwards_filtering_def = Define
   `upwards_filtering (J,R) <=> !a b. a IN J /\ b IN J ==> ?c. c IN J /\ R a c /\ R b c`;

(* The smallest sigma-algebra on `sp` that makes `f` measurable *)
val sigma_function_def = Define
   `sigma_function sp A f = (sp,IMAGE (\s. PREIMAGE f s INTER sp) (subsets A))`;

val _ = overload_on ("sigma", ``sigma_function``);

val SIGMA_MEASURABLE = store_thm
  ("SIGMA_MEASURABLE",
  ``!sp A f. sigma_algebra A /\ f IN (sp -> space A) ==> f IN measurable (sigma sp A f) A``,
    RW_TAC std_ss [sigma_function_def, space_def, subsets_def,
                   IN_FUNSET, IN_MEASURABLE, IN_IMAGE]
 >- (MATCH_MP_TAC PREIMAGE_SIGMA_ALGEBRA >> art [IN_FUNSET])
 >> Q.EXISTS_TAC `s` >> art []);

(* Definition 7.5 of [1, p.51], The smallest sigma-algebra on `sp` that makes all `f`
   simultaneously measurable. *)
val sigma_functions_def = Define
   `sigma_functions sp A f J =
      sigma sp (BIGUNION (IMAGE (\i. IMAGE (\s. PREIMAGE (f i) s INTER sp) (subsets (A i))) J))`;

val _ = overload_on ("sigma", ``sigma_functions``);

(* Lemma 7.5 of [1, p.51] *)
val SIGMA_SIMULTANEOUSLY_MEASURABLE = store_thm
  ("SIGMA_SIMULTANEOUSLY_MEASURABLE",
  ``!sp A f J. (!i. i IN J ==> sigma_algebra (A i)) /\
               (!i. f i IN (sp -> space (A i))) ==>
                !i. i IN J ==> f i IN measurable (sigma sp A f J) (A i)``,
    RW_TAC std_ss [IN_FUNSET, SPACE_SIGMA, sigma_functions_def, IN_MEASURABLE]
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
     RW_TAC std_ss [subset_class_def, IN_BIGUNION_IMAGE, IN_IMAGE, IN_PREIMAGE, IN_INTER] \\
     REWRITE_TAC [INTER_SUBSET])
 >> Know `PREIMAGE (f i) s INTER sp IN
            (BIGUNION (IMAGE (\i. IMAGE (\s. PREIMAGE (f i) s INTER sp) (subsets (A i))) J))`
 >- (RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_IMAGE] \\
     Q.EXISTS_TAC `i` >> art [] \\
     Q.EXISTS_TAC `s` >> art []) >> DISCH_TAC
 >> ASSUME_TAC
      (Q.SPECL [`sp`, `BIGUNION (IMAGE (\i. IMAGE (\s. PREIMAGE (f i) s INTER sp)
                                                  (subsets (A i))) J)`] SIGMA_SUBSET_SUBSETS)
 >> PROVE_TAC [SUBSET_DEF]);

(* ------------------------------------------------------------------------- *)
(* Some prelimitaries of Radon-Nikodym Theorem                               *)
(* ------------------------------------------------------------------------- *)

Definition seq_sup_def :
  (seq_sup P 0       = @r. r IN P /\ sup P < r + 1) /\
  (seq_sup P (SUC n) = @r. r IN P /\ sup P < r + Normal ((1 / 2) pow (SUC n)) /\
                           (seq_sup P n) < r /\ r < sup P)
End

val EXTREAL_SUP_SEQ = store_thm
  ("EXTREAL_SUP_SEQ",
  ``!P. (?x. P x) /\ (?z. z <> PosInf /\ !x. P x ==> x <= z) ==>
        ?x. (!n. x n IN P) /\ (!n. x n <= x (SUC n)) /\ (sup (IMAGE x UNIV) = sup P)``,
  RW_TAC std_ss []
  >> Cases_on `?z. P z /\ (z = sup P)`
  >- (Q.EXISTS_TAC `(\i. sup P)`
      >> RW_TAC std_ss [le_refl,SPECIFICATION]
      >> `IMAGE (\i:num. sup P) UNIV = (\i. i = sup P)`
           by RW_TAC std_ss [EXTENSION,IN_IMAGE,IN_UNIV,IN_ABS]
      >> RW_TAC std_ss [sup_const])
  >> Cases_on `!x. P x ==> (x = NegInf)`
  >- (`sup P = NegInf` by METIS_TAC [sup_const_alt]
      >> Q.EXISTS_TAC `(\n. NegInf)`
      >> FULL_SIMP_TAC std_ss [le_refl]
      >> RW_TAC std_ss []
      >- METIS_TAC []
      >> METIS_TAC [UNIV_NOT_EMPTY,sup_const_over_set])
  >> FULL_SIMP_TAC std_ss []
  >> Q.EXISTS_TAC `seq_sup P`
  >> FULL_SIMP_TAC std_ss []
  >> `sup P <> PosInf` by METIS_TAC [sup_le,lt_infty,let_trans]
  >> `!x. P x ==> x < sup P` by METIS_TAC [lt_le,le_sup_imp]
  >> `!e. 0 < e ==> ?x. P x /\ sup P < x + e`
       by (RW_TAC std_ss [] >> MATCH_MP_TAC sup_lt_epsilon >> METIS_TAC [])
  >> `!n. 0:real < (1 / 2) pow n` by METIS_TAC [HALF_POS,REAL_POW_LT]
  >> `!n. 0 < Normal ((1 / 2) pow n)` by METIS_TAC [extreal_lt_eq,extreal_of_num_def]
  >> `!n. seq_sup P n IN P`
      by (Induct
          >- (RW_TAC std_ss [seq_sup_def]
              >> SELECT_ELIM_TAC
              >> RW_TAC std_ss []
              >> METIS_TAC [lt_01,SPECIFICATION])
          >> RW_TAC std_ss [seq_sup_def]
          >> SELECT_ELIM_TAC
          >> RW_TAC std_ss []
          >> `?x. P x /\ seq_sup P n < x` by METIS_TAC [sup_lt,SPECIFICATION]
          >> `?x. P x /\ sup P < x + Normal ((1 / 2) pow (SUC n))` by METIS_TAC []
          >> Q.EXISTS_TAC `max x'' x'''`
          >> RW_TAC std_ss [extreal_max_def,SPECIFICATION]
          >- (`x''' < x''` by FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
              >> `x''' +  Normal ((1 / 2) pow (SUC n)) <= x'' +  Normal ((1 / 2) pow (SUC n))`
                  by METIS_TAC [lt_radd,lt_le,extreal_not_infty]
              >> METIS_TAC [lte_trans])
          >> METIS_TAC [lte_trans])
  >> `!n. seq_sup P n <= seq_sup P (SUC n)`
      by (RW_TAC std_ss [seq_sup_def]
          >> SELECT_ELIM_TAC
          >> RW_TAC std_ss []
          >- (`?x. P x /\ seq_sup P n < x` by METIS_TAC [sup_lt,SPECIFICATION]
              >> `?x. P x /\ sup P < x + Normal ((1 / 2) pow (SUC n))` by METIS_TAC []
              >> Q.EXISTS_TAC `max x'' x'''`
              >> RW_TAC std_ss [extreal_max_def,SPECIFICATION]
              >- (`x''' < x''` by FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
                  >> `x''' + Normal ((1 / 2) pow (SUC n)) <= x'' + Normal ((1 / 2) pow (SUC n))`
                      by METIS_TAC [lt_radd,lt_le,extreal_not_infty]
                  >> METIS_TAC [lte_trans])
              >> METIS_TAC [lte_trans])
          >> METIS_TAC [lt_le])
  >> RW_TAC std_ss []
  >> `!n. sup P <= seq_sup P n + Normal ((1 / 2) pow n)`
      by (Induct
          >- (RW_TAC std_ss [seq_sup_def,pow,GSYM extreal_of_num_def]
              >> SELECT_ELIM_TAC
              >> RW_TAC std_ss []
              >- METIS_TAC [lt_01,SPECIFICATION]
              >> METIS_TAC [lt_le])
          >> RW_TAC std_ss [seq_sup_def]
          >> SELECT_ELIM_TAC
          >> RW_TAC std_ss []
          >- (`?x. P x /\ seq_sup P n < x` by METIS_TAC [sup_lt,SPECIFICATION]
              >> `?x. P x /\ sup P < x + Normal ((1 / 2) pow (SUC n))` by METIS_TAC []
              >> Q.EXISTS_TAC `max x'' x'''`
              >> RW_TAC std_ss [extreal_max_def,SPECIFICATION]
              >- (`x''' < x''` by FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
                  >> `x''' + Normal ((1 / 2) pow (SUC n)) <= x'' + Normal ((1 / 2) pow (SUC n))`
                      by METIS_TAC [lt_radd,lt_le,extreal_not_infty]
                  >> METIS_TAC [lte_trans])
              >> METIS_TAC [lte_trans])
          >> METIS_TAC [lt_le])
  >> RW_TAC std_ss [sup_eq]
  >- (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      >> METIS_TAC [SPECIFICATION,lt_le])
  >> MATCH_MP_TAC le_epsilon
  >> RW_TAC std_ss []
  >> `e <> NegInf` by METIS_TAC [lt_infty,extreal_of_num_def,lt_trans]
  >> `?r. e = Normal r` by METIS_TAC [extreal_cases]
  >> FULL_SIMP_TAC std_ss []
  >> `?n. Normal ((1 / 2) pow n) < Normal r` by METIS_TAC [EXTREAL_ARCH_POW_INV]
  >> MATCH_MP_TAC le_trans
  >> Q.EXISTS_TAC `seq_sup P n + Normal ((1 / 2) pow n)`
  >> RW_TAC std_ss []
  >> MATCH_MP_TAC le_add2
  >> FULL_SIMP_TAC std_ss [lt_le]
  >> Q.PAT_X_ASSUM `!z. IMAGE (seq_sup P) UNIV z ==> z <= y` MATCH_MP_TAC
  >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  >> RW_TAC std_ss [IN_UNIV,IN_IMAGE]
  >> METIS_TAC []);

val EXTREAL_SUP_FUN_SEQ_IMAGE = store_thm
  ("EXTREAL_SUP_FUN_SEQ_IMAGE",
  ``!(P:extreal->bool) (P':('a->extreal)->bool) f.
       (?x. P x) /\ (?z. z <> PosInf /\ !x. P x ==> x <= z) /\ (P = IMAGE f P')
           ==> ?g. (!n:num. g n IN P') /\
                   (sup (IMAGE (\n. f (g n)) UNIV) = sup P)``,
  rpt STRIP_TAC
  >> `?y. (!n. y n IN P) /\ (!n. y n <= y (SUC n)) /\ (sup (IMAGE y UNIV) = sup P)`
     by METIS_TAC [EXTREAL_SUP_SEQ]
  >> Q.EXISTS_TAC `(\n. @r. (r IN P') /\ (f r  = y n))`
  >> `(\n. f (@(r :'a -> extreal). r IN (P' :('a -> extreal) -> bool) /\
                                  ((f :('a -> extreal) -> extreal) r = (y :num -> extreal) n))) = y`
  by (rw [FUN_EQ_THM] >> SELECT_ELIM_TAC
      >> RW_TAC std_ss []
      >> METIS_TAC [IN_IMAGE])
  >> ASM_SIMP_TAC std_ss []
  >> RW_TAC std_ss []
  >- (SELECT_ELIM_TAC
      >> RW_TAC std_ss []
      >> METIS_TAC [IN_IMAGE]));

val max_fn_seq_def = Define `
   (max_fn_seq g 0 x  = g 0 x) /\
   (max_fn_seq g (SUC n) x = max (max_fn_seq g n x) (g (SUC n) x))`;

val max_fn_seq_mono = store_thm
  ("max_fn_seq_mono", ``!g n x. max_fn_seq g n x <= max_fn_seq g (SUC n) x``,
    RW_TAC std_ss [max_fn_seq_def,extreal_max_def,le_refl]);

val EXTREAL_SUP_FUN_SEQ_MONO_IMAGE = store_thm
  ("EXTREAL_SUP_FUN_SEQ_MONO_IMAGE",
  ``!f (P:extreal->bool) (P':('a->extreal)->bool).
                (?x. P x) /\ (?z. z <> PosInf /\ !x. P x ==> x <= z) /\ (P = IMAGE f P') /\
                (!g1 g2. (g1 IN P' /\ g2 IN P' /\ (!x. g1 x <= g2 x))  ==> f g1 <= f g2) /\
                (!g1 g2. g1 IN P' /\ g2 IN P' ==> (\x. max (g1 x) (g2 x)) IN P')
          ==> ?g. (!n. g n IN P') /\
                  (!x n. g n x <= g (SUC n) x) /\
                  (sup (IMAGE (\n. f (g n)) UNIV) = sup P)``,
  rpt STRIP_TAC
  >> `?g. (!n:num. g n IN P') /\ (sup (IMAGE (\n. f (g n)) UNIV) = sup P)`
      by METIS_TAC [EXTREAL_SUP_FUN_SEQ_IMAGE]
  >> Q.EXISTS_TAC `max_fn_seq g`
  >> `!n. max_fn_seq g n IN P'`
      by (Induct
          >- (`max_fn_seq g 0 = g 0` by RW_TAC std_ss [FUN_EQ_THM,max_fn_seq_def]
              >> METIS_TAC [])
              >> `max_fn_seq g (SUC n) = (\x. max (max_fn_seq g n x) (g (SUC n) x))`
                  by RW_TAC std_ss [FUN_EQ_THM,max_fn_seq_def]
              >> RW_TAC std_ss []
              >> METIS_TAC [])
  >> `!g n x. max_fn_seq g n x <= max_fn_seq g (SUC n) x`
      by RW_TAC real_ss [max_fn_seq_def,extreal_max_def,le_refl]
  >> CONJ_TAC >- RW_TAC std_ss []
  >> CONJ_TAC >- RW_TAC std_ss []
  >> `!n. (!x. g n x <= max_fn_seq g n x)`
      by (Induct >- RW_TAC std_ss [max_fn_seq_def,le_refl]
          >> METIS_TAC [le_max2,max_fn_seq_def])
  >> `!n. f (g n) <= f (max_fn_seq g n)` by METIS_TAC []
  >> `sup (IMAGE (\n. f (g n)) UNIV) <= sup (IMAGE (\n. f (max_fn_seq g n)) UNIV)`
      by (MATCH_MP_TAC sup_le_sup_imp
          >> RW_TAC std_ss []
          >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
          >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
          >> Q.EXISTS_TAC `f (max_fn_seq g n)`
          >> RW_TAC std_ss []
          >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
          >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
          >> METIS_TAC [])
  >> `sup (IMAGE (\n. f (max_fn_seq g n)) UNIV) <= sup P`
      by (RW_TAC std_ss [sup_le]
          >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
          >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
          >> MATCH_MP_TAC le_sup_imp
          >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
          >> RW_TAC std_ss [IN_IMAGE]
          >> METIS_TAC [])
  >> METIS_TAC [le_antisym]);

val _ = export_theory ();
val _ = html_theory "martingale";

(* References:

  [1] Schilling, R.L.: Measures, Integrals and Martingales (Second Edition).
      Cambridge University Press (2017).
  [2] Doob, J.L.: Stochastic processes. Wiley-Interscience (1990).
  [3] Doob, J.L.: What is a Martingale? Amer. Math. Monthly. 78(5), 451-463 (1971).
  [4] Pintacuda, N.: Probabilita'. Zanichelli, Bologna (1995).
 *)
