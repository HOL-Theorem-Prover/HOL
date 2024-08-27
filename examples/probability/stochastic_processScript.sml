(* ========================================================================= *)
(* stochastic_processScript.sml: Theory of General Stochastic Processes      *)
(*                                                                           *)
(* Author: Chun Tian (binghe) <binghe.lisp@gmail.com> (2021 - 2024)          *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open combinTheory arithmeticTheory pred_setTheory pred_setLib numLib hurdUtils
     posetTheory listTheory fcpTheory fcpLib topologyTheory;

open realTheory realLib iterateTheory real_sigmaTheory real_topologyTheory;

open util_probTheory sigma_algebraTheory extrealTheory real_borelTheory
     measureTheory borelTheory lebesgueTheory martingaleTheory
     probabilityTheory;

val _ = new_theory "stochastic_process";

(* "The theory of probability, as a mathematical discipline, can and should
    be developed from axioms in exactly the same way as Geometry and Algebra.
    This means that after we have defined the elements to be studied and their
    basic relations, and have stated the axioms by which these relations are
    to be governed, all further exposition must be based exclusively on these
    axioms, independent of the usual concerte meaning of these elements and
    their relations."

  -- A. N. Kolmogorov, "Foundations of the Theory of Probability" [1]. *)

val set_ss = std_ss ++ PRED_SET_ss;
val fcp_ss = std_ss ++ FCP_ss ++ PRED_SET_ss;

val _ = intLib.deprecate_int ();
val _ = ratLib.deprecate_rat ();

val _ = hide "S";

(* ------------------------------------------------------------------------- *)
(*  General filtration/martingale with poset indexes (Chapter 25 of [9])     *)
(* ------------------------------------------------------------------------- *)

(* Any non-empty set with (=) is a poset *)
Theorem poset_trivial :
    !(s :'a set). s <> {} ==> poset(s,$=)
Proof
    RW_TAC std_ss [poset_def]
 >> rw [REWRITE_RULE [IN_APP] MEMBER_NOT_EMPTY]
QED

(* Any non-empty set of numbers with (<=) is a poset *)
Theorem poset_num_sets :
    !(N :num set). N <> {} ==> poset(N,$<=)
Proof
    RW_TAC std_ss [poset_def]
 >| [ (* goal 1 (of 3) *)
      rw [REWRITE_RULE [IN_APP] MEMBER_NOT_EMPTY],
      (* goal 2 (of 3) *)
      rw [GSYM LESS_EQUAL_ANTISYM],
      (* goal 3 (of 3) *)
      MATCH_MP_TAC LESS_EQ_TRANS \\
      Q.EXISTS_TAC ‘y’ >> art [] ]
QED

Theorem poset_num[simp] :
    poset (univ(:num),$<=)
Proof
    MP_TAC (Q.SPEC ‘univ(:num)’ poset_num_sets)
 >> RW_TAC std_ss [UNIV_NOT_EMPTY]
QED

Theorem poset_nnreal[simp] :
    poset ({x | 0r <= x},$<=)
Proof
    RW_TAC real_ss [poset_def]
 >- (Q.EXISTS_TAC ‘0’ \\
     RW_TAC real_ss [Once (GSYM IN_APP), GSPECIFICATION])
 >- (RW_TAC real_ss [GSYM REAL_LE_ANTISYM])
 >> MATCH_MP_TAC REAL_LE_TRANS
 >> Q.EXISTS_TAC ‘y’ >> art []
QED

Definition gen_filtration_def :
    gen_filtration A a J <=>
      poset J /\ (!n. n IN (carrier J) ==> sub_sigma_algebra (a n) A) /\
      (!i j. i IN (carrier J) /\ j IN (carrier J) /\ (relation J) i j ==>
             subsets (a i) SUBSET subsets (a j))
End

Theorem gen_filtration_imp_sigma_algebra :
    !A a J. gen_filtration A a J ==> sigma_algebra A
Proof
    rw [gen_filtration_def]
 >> Know ‘?x. x IN carrier J’
 >- (Cases_on ‘J’ >> fs [IN_APP] \\
     MATCH_MP_TAC poset_nonempty \\
     Q.EXISTS_TAC ‘r’ >> art [])
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!n. n IN carrier J ==> P’ (MP_TAC o Q.SPEC ‘x’)
 >> rw [sub_sigma_algebra_def]
QED

Theorem filtration_alt_gen : (* was: filtration_alt *)
    !A a. filtration A a = gen_filtration A a (univ(:num),$<=)
Proof
    rw [filtration_def, gen_filtration_def, poset_num]
QED

Definition gen_filtered_measure_space_def :
    gen_filtered_measure_space m a J =
      (measure_space m /\ gen_filtration (m_space m,measurable_sets m) a J)
End

Theorem filtered_measure_space_alt_gen :
    !m a. filtered_measure_space m a <=>
          gen_filtered_measure_space m a (univ(:num),$<=)
Proof
    rw [filtered_measure_space_def, gen_filtered_measure_space_def,
        filtration_alt_gen, poset_num]
QED

Definition gen_sigma_finite_filtered_measure_space_def :
    gen_sigma_finite_filtered_measure_space m a J =
      (gen_filtered_measure_space m a J /\
       !n. n IN (carrier J) ==> sigma_finite (m_space m,subsets (a n),measure m))
End

Theorem sigma_finite_filtered_measure_space_alt_gen :
    !m a. sigma_finite_filtered_measure_space m a <=>
          gen_sigma_finite_filtered_measure_space m a (univ(:num),$<=)
Proof
    rw [sigma_finite_filtered_measure_space_alt_all, GSYM CONJ_ASSOC,
        gen_sigma_finite_filtered_measure_space_def,
        GSYM filtered_measure_space_alt_gen, filtered_measure_space_def]
QED

(* ‘gen_martingale m a u (univ(:num),$<=) = martingale m a u’ [1, p.301] *)
Definition gen_martingale_def :
   gen_martingale m a u J =
     (gen_sigma_finite_filtered_measure_space m a J /\
      (!n. n IN (carrier J) ==> integrable m (u n)) /\
      !i j s. i IN (carrier J) /\ j IN (carrier J) /\ (relation J) i j /\
              s IN (subsets (a i)) ==>
             (integral m (\x. u i x * indicator_fn s x) =
              integral m (\x. u j x * indicator_fn s x)))
End

(* or "upwards directed", see [9, p.301] *)
Definition upwards_filtering_def :
    upwards_filtering (J :'index poset) =
      !i j. i IN (carrier J) /\ j IN (carrier J) ==>
            ?k. k IN (carrier J) /\ (relation J) i k /\ (relation J) j k
End

Theorem upwards_filtering_num[simp] :
    upwards_filtering (univ(:num),$<=)
Proof
    rw [upwards_filtering_def]
 >> Q.EXISTS_TAC ‘MAX i j’ >> rw []
QED

Theorem upwards_filtering_nnreal[simp] :
    upwards_filtering ({x | 0r <= x},real_lte)
Proof
    rw [upwards_filtering_def]
 >> Q.EXISTS_TAC ‘max i j’ >> rw [REAL_LE_MAX]
QED

(* ------------------------------------------------------------------------- *)
(*  N-dimensional (gen and extreal-based) Borel spaces                       *)
(* ------------------------------------------------------------------------- *)

(* ‘fcp_rectangle’ is a generalisation of ‘fcp_prod’ *)
Definition fcp_rectangle_def :
    fcp_rectangle (h :num -> 'a set) (:'N) =
      {(v :'a['N]) | !i. i < dimindex(:'N) ==> v ' i IN h i}
End

Overload rectangle = “fcp_rectangle”

Theorem RECTANGLE_UNIV :
    rectangle (\n. univ(:'a)) (:'N) = univ(:'a['N])
Proof
    rw [fcp_rectangle_def]
QED

Theorem IN_RECTANGLE :
    !x (h :num -> 'a set). x IN rectangle h (:'N) <=>
       !i. i < dimindex(:'N) ==> x ' i IN h i
Proof
    rw [fcp_rectangle_def, GSPECIFICATION]
QED

Theorem PREIMAGE_RECTANGLE :
    !(f :'a -> 'b['N]) (h :num -> 'b set).
        PREIMAGE f (rectangle h (:'N)) =
        BIGINTER (IMAGE (\n. PREIMAGE (\x. f x ' n) (h n)) (count (dimindex(:'N))))
Proof
    rw [Once EXTENSION, IN_PREIMAGE, IN_RECTANGLE]
 >> EQ_TAC >> rw [PREIMAGE_def] >- rw []
 >> Q.PAT_X_ASSUM ‘!P. _ ==> x IN P’ (MP_TAC o (Q.SPEC ‘{x | (f :'a -> 'b['N]) x ' i IN h i}’))
 >> simp []
 >> DISCH_THEN MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘i’ >> art []
QED

(* Only slightly higher than "=" (450) *)
val _ = set_fixity "of_dimension" (Infix(NONASSOC, 470));

(* cf. Theorem 14.17 [9, p.149] for this alternative way of product algebra.

   This is the smallest sigma-algebra on n-dimensional `space B` that makes
   all N-1 projections simultaneously measurable.

   NOTE: ‘(\n v. v ' n) = flip $fcp_index’ (C $fcp_index)

   This gen definition can be used to convert any (1-dimensional) Borel
   sigma-algebra (e.g. ‘borel’ and ‘Borel’) into n-dimensional Borel spaces.
 *)
Definition sigma_of_dimension_def :
    sigma_of_dimension (B :'a algebra) (:'N) =
    sigma_functions (rectangle (\n. space B) (:'N)) (\n. B) (\n v. v ' n)
                    (count (dimindex(:'N)))
End
Overload of_dimension = “sigma_of_dimension”

(* ‘B of_dimension ['N]’ is indeed a sigma-algebra (for whatever B) *)
Theorem sigma_algebra_of_dimension :
    !(B :'a algebra). sigma_algebra (B of_dimension (:'N))
Proof
    rw [sigma_of_dimension_def, sigma_functions_def, fcp_rectangle_def]
 >> MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA
 >> rw [subset_class_def, SUBSET_DEF, IN_BIGUNION_IMAGE]
 >> rename1 ‘s IN subsets B’
 >> rename1 ‘x ' i IN space B’
 >> fs [IN_INTER, IN_PREIMAGE]
QED

Theorem space_sigma_of_dimension :
    !(B :'a algebra). space (B of_dimension (:'N)) = rectangle (\n. space B) (:'N)
Proof
    rw [sigma_of_dimension_def, sigma_functions_def, SPACE_SIGMA]
QED

(* Alternative definition of ‘B of_dimension (:'N)’ (usually more useful)

   This definition is sometimes easier to use, because it requires only the plain
   sigma-generator ‘sigma’ which has many supporting theorems available.

   The proof is a genization of (the proof of) prod_sigma_alt_sigma_functions.

   NOTE: In theory, this theorem (and sigma_of_dimension_def) can be generalised
   to support differrent (space B) at each dimensions. So far this is not needed.
 *)
Theorem sigma_of_dimension_alt :
    !(B :'a algebra).
      subset_class (space B) (subsets B) /\ space B IN subsets B ==>
      B of_dimension (:'N) =
      sigma (rectangle (\n. space B) (:'N))
            {rectangle h (:'N) | !i. i < dimindex(:'N) ==> h i IN subsets B}
Proof
    rw [sigma_of_dimension_def, sigma_functions_def]
 >> Q.ABBREV_TAC (* this is part of the goal, to be replaced by ‘sts’ *)
   ‘src = BIGUNION
            (IMAGE (\n. IMAGE (\s. PREIMAGE (\ (v :'a['N]). v ' n) s INTER
                                   rectangle (\n. space B) (:'N))
                              (subsets B))
                   (count (dimindex (:'N))))’
 >> Q.ABBREV_TAC
   ‘sts = BIGUNION (IMAGE (\n. {rectangle h (:'N) |
                                h n IN subsets B /\
                                !i. i < dimindex(:'N) /\ i <> n ==> h i = space B})
                          (count (dimindex (:'N))))’
 >> Know ‘src = sts’
 >- (rw [Abbr ‘src’, Abbr ‘sts’, Once EXTENSION, PREIMAGE_def] \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       fs [IN_IMAGE] >> rename1 ‘b IN subsets B’ \\
       Q.EXISTS_TAC ‘{rectangle h (:'N) |
                      h n IN subsets B /\
                      !i. i < dimindex (:'N) /\ i <> n ==> h i = space B}’ \\
       reverse (rw []) >- (Q.EXISTS_TAC ‘n’ >> art []) \\
       Q.EXISTS_TAC ‘\i. if i = n then b else space B’ >> rw [] \\
       rw [fcp_rectangle_def, Once EXTENSION] \\
       EQ_TAC >> rw [] >| (* 3 trivial subgoals *)
       [ (* goal 1.1 (of 3) *)
         Cases_on ‘i = n’ >> rw [],
         (* goal 1.2 (of 3) *)
         POP_ASSUM (MP_TAC o (Q.SPEC ‘n’)) >> rw [],
         (* goal 1.3 (of 3) *)
         rename1 ‘x ' i IN space B’ \\
         Q.PAT_X_ASSUM ‘!i. i < dimindex (:'N) ==> P’ (MP_TAC o (Q.SPEC ‘i’)) \\
         Cases_on ‘i = n’ >> rw [] \\
         FULL_SIMP_TAC std_ss [subset_class_def] \\
         METIS_TAC [SUBSET_DEF] ],
       (* goal 2 (of 2) *)
       fs [] \\
       Q.EXISTS_TAC ‘IMAGE (\s. {v | v ' n IN s} INTER rectangle (\n. space B) (:'N))
                           (subsets B)’ \\
       reverse (rw []) >- (Q.EXISTS_TAC ‘n’ >> art []) \\
       Q.EXISTS_TAC ‘h n’ >> rw [fcp_rectangle_def, Once EXTENSION] \\
       EQ_TAC >> rw [] >| (* 2 trivial subgoals *)
       [ (* goal 2.1 (of 2) *)
         rename1 ‘x ' i IN space B’ \\
         Cases_on ‘i = n’
         >- (Q.PAT_X_ASSUM ‘!i. i < dimindex (:'N) ==> x ' i IN h i’ (MP_TAC o (Q.SPEC ‘n’)) \\
             rw [] \\
             FULL_SIMP_TAC std_ss [subset_class_def] \\
             METIS_TAC [SUBSET_DEF]) \\
         Q.PAT_X_ASSUM ‘!i. i < dimindex (:'N) /\ i <> n ==> P’ (MP_TAC o (Q.SPEC ‘i’)) \\
         Q.PAT_X_ASSUM ‘!i. i < dimindex (:'N) ==> x ' i IN h i’ (MP_TAC o (Q.SPEC ‘i’)) \\
         rw [] >> fs [],
         (* goal 2.2 (of 2) *)
         Cases_on ‘i = n’ >> rw [] ] ])
 >> Rewr'
 >> Q.UNABBREV_TAC ‘src’ (* not needed any more *)
 (* stage work *)
 >> Know ‘sigma_algebra (sigma (rectangle (\n. space B) (:'N)) sts)’
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
     rw [Abbr ‘sts’, subset_class_def, SUBSET_DEF] \\
     gs [IN_RECTANGLE] \\
     Q.PAT_X_ASSUM ‘x = rectangle h (:'N)’ K_TAC \\
     rename1 ‘!i. i < dimindex (:'N) ==> x ' i IN h i’ \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < dimindex (:'N) ==> P’ (MP_TAC o (Q.SPEC ‘i’)) \\
     RW_TAC std_ss [] \\
     FULL_SIMP_TAC std_ss [subset_class_def] \\
     Cases_on ‘i = n’ >- (rw [] >> METIS_TAC [SUBSET_DEF]) \\
     Q.PAT_X_ASSUM ‘!i. i < dimindex (:'N) /\ i <> n ==> P’ (MP_TAC o (Q.SPEC ‘i’)) \\
     RW_TAC std_ss [] >> fs [])
 >> DISCH_TAC
 >> ‘sts SUBSET subsets (sigma (rectangle (\n. space B) (:'N)) sts)’
       by PROVE_TAC [SIGMA_SUBSET_SUBSETS]
 >> Q.ABBREV_TAC
     ‘prod = {rectangle h (:'N) | (!i. i < dimindex (:'N) ==> h i IN subsets B)}’
 >> Know ‘prod SUBSET subsets (sigma (rectangle (\n. space B) (:'N)) sts)’
 >- (rw [Abbr ‘prod’, SUBSET_DEF] \\
     Know ‘rectangle h (:'N) =
           BIGINTER (IMAGE (\n. {v | v ' n IN h n /\
                                     !i. i < dimindex (:'N) /\ i <> n ==> v ' i IN space B})
                           (count (dimindex(:'N))))’
     >- (rw [fcp_rectangle_def, Once EXTENSION, IN_BIGINTER_IMAGE] \\
         EQ_TAC >> rw [] \\
         FULL_SIMP_TAC std_ss [subset_class_def] \\
         METIS_TAC [SUBSET_DEF]) >> Rewr' \\
  (* applying SIGMA_ALGEBRA_FINITE_INTER *)
     MATCH_MP_TAC SIGMA_ALGEBRA_FINITE_INTER \\
     rw [DIMINDEX_GT_0] (* newly exported from fcpTheory *) \\
     Q.ABBREV_TAC ‘A = {(v :'a['N]) |
                         v ' i IN h i /\
                        !j. j < dimindex (:'N) /\ j <> i ==> v ' j IN space B}’ \\
     Suff ‘A IN sts’ >- PROVE_TAC [SUBSET_DEF] \\
     Q.PAT_X_ASSUM ‘sigma_algebra (sigma (rectangle (\n. space B) (:'N)) sts)’      K_TAC \\
     Q.PAT_X_ASSUM ‘sts SUBSET subsets (sigma (rectangle (\n. space B) (:'N)) sts)’ K_TAC \\
     rw [Abbr ‘A’, Abbr ‘sts’, IN_BIGUNION_IMAGE] \\
     rename1 ‘n < dimindex(:'N)’ \\
     Q.EXISTS_TAC ‘n’ >> rw [] \\
     Q.EXISTS_TAC ‘\i. if i = n then h n else space B’ >> rw [] \\
     rw [fcp_rectangle_def, Once EXTENSION] \\
     EQ_TAC >> rw [] >| (* 3 trivial subgoals *)
     [ (* goal 1.1 (of 3) *)
       Cases_on ‘i = n’ >> rw [],
       (* goal 1.2 (of 3) *)
       POP_ASSUM (MP_TAC o (Q.SPEC ‘n’)) >> rw [],
       (* goal 1.3 (of 3) *)
       rename1 ‘x ' i IN space B’ \\
       Q.PAT_X_ASSUM ‘!i. i < dimindex (:'N) ==> P’ (MP_TAC o (Q.SPEC ‘i’)) \\
       Cases_on ‘i = n’ >> rw [] ])
 >> DISCH_TAC
 >> Suff ‘subsets (sigma (rectangle (\n. space B) (:'N)) sts) =
          subsets (sigma (rectangle (\n. space B) (:'N)) prod)’
 >- METIS_TAC [SPACE, SPACE_SIGMA]
 >> MATCH_MP_TAC SIGMA_SMALLEST >> art []
 >> reverse CONJ_TAC >- METIS_TAC [SPACE, SPACE_SIGMA]
 (* stage work *)
 >> MP_TAC (ISPECL [“sts :('a['N] set) set”,
                    “sigma (rectangle (\n. space B) (:'N)) (prod :('a['N] set) set)”]
                    SIGMA_SUBSET)
 >> REWRITE_TAC [SPACE_SIGMA]
 >> DISCH_THEN MATCH_MP_TAC
 >> CONJ_TAC
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
     rw [Abbr ‘prod’, subset_class_def, IN_RECTANGLE, SUBSET_DEF] \\
     rename1 ‘x ' n IN space B’ \\
     fs [IN_RECTANGLE] \\
     FULL_SIMP_TAC std_ss [subset_class_def] \\
     METIS_TAC [SUBSET_DEF])
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘prod’
 >> REWRITE_TAC [SIGMA_SUBSET_SUBSETS]
 >> Q.PAT_X_ASSUM ‘sigma_algebra (sigma (rectangle (\n. space B) (:'N)) sts)’       K_TAC
 >> Q.PAT_X_ASSUM ‘sts SUBSET subsets (sigma (rectangle (\n. space B) (:'N)) sts)’  K_TAC
 >> Q.PAT_X_ASSUM ‘prod SUBSET subsets (sigma (rectangle (\n. space B) (:'N)) sts)’ K_TAC
 >> rw [Abbr ‘sts’, Abbr ‘prod’, SUBSET_DEF]
 >> fs [IN_RECTANGLE]
 >> Q.EXISTS_TAC ‘h’ >> rw []
 >> Cases_on ‘i = n’ >> rw []
QED

(* for easier applications in the most common case (with sigma_algebras) *)
Theorem sigma_of_dimension_alt_sigma_algebra :
    !(B :'a algebra). sigma_algebra B ==>
      B of_dimension (:'N) =
      sigma (rectangle (\n. space B) (:'N))
            {rectangle h (:'N) | !i. i < dimindex(:'N) ==> h i IN subsets B}
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC sigma_of_dimension_alt
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SPACE >> art [])
 >> FULL_SIMP_TAC std_ss [sigma_algebra_def, algebra_def]
QED

Theorem rectangle_in_sigma_of_dimension :
    !B h. sigma_algebra B /\ (!i. i < dimindex(:'N) ==> h i IN subsets B) ==>
          rectangle h (:'N) IN subsets (B of_dimension (:'N))
Proof
    RW_TAC std_ss [sigma_of_dimension_alt_sigma_algebra]
 >> MATCH_MP_TAC IN_SIGMA >> rw [] (* ‘sigma’ is eliminated here *)
 >> Q.EXISTS_TAC ‘h’ >> art []
QED

Theorem RECTANGLE_INTER_STABLE :
  !(B :'a algebra) C.
     (C = {rectangle h (:'N) | !i. i < dimindex(:'N) ==> h i IN subsets B}) /\
     (!s t. s IN subsets B /\ t IN subsets B ==> s INTER t IN subsets B) ==>
      !s t. s IN C /\ t IN C ==> s INTER t IN C
Proof
    RW_TAC set_ss []
 >> rename1 ‘!i. i < dimindex (:'N) ==> g i IN subsets B’
 >> Q.EXISTS_TAC ‘\i. (g i) INTER (h i)’
 >> rw [fcp_rectangle_def, Once EXTENSION]
 >> EQ_TAC >> rw []
QED

(* This is N-dimensional real-valued Borel space “:real['N] algebra” *)
Definition borel_space_def :
    borel_space (:'N) = borel of_dimension (:'N)
End

(* This is N-dimensional extreal-valued Borel space “:extreal['N] algebra” *)
Definition Borel_space_def :
    Borel_space (:'N) = Borel of_dimension (:'N)
End

(* |- sigma_algebra (borel_space (:'N)) *)
Theorem sigma_algebra_borel_space =
    REWRITE_RULE [GSYM borel_space_def]
                 (ISPEC “borel” sigma_algebra_of_dimension)

(* |- sigma_algebra (Borel_space (:'N)) *)
Theorem SIGMA_ALGEBRA_BOREL_SPACE =
    REWRITE_RULE [GSYM Borel_space_def]
                 (ISPEC “Borel” sigma_algebra_of_dimension)

(* alternative definition of ‘borel’ following "of_dimension_def" *)
Theorem borel_space_alt_sigma_functions :
    borel_space (:'N) =
    sigma_functions univ(:real['N]) (\n. borel) (\n v. v ' n)
                   (count (dimindex(:'N)))
Proof
    rw [space_borel, borel_space_def, sigma_of_dimension_def, RECTANGLE_UNIV]
QED

Theorem Borel_space_alt_sigma_functions :
    Borel_space (:'N) =
    sigma_functions univ(:extreal['N]) (\n. Borel) (\n v. v ' n)
                   (count (dimindex(:'N)))
Proof
    rw [SPACE_BOREL, Borel_space_def, sigma_of_dimension_def, RECTANGLE_UNIV]
QED

(* alternative definition of ‘borel’ following "of_dimension_alt" *)
Theorem borel_space_alt_sigma :
    borel_space (:'N) =
    sigma univ(:real['N])
          {rectangle h (:'N) | !i. i < dimindex(:'N) ==> h i IN subsets borel}
Proof
    rw [space_borel, sigma_algebra_borel, borel_space_def, RECTANGLE_UNIV,
        sigma_of_dimension_alt_sigma_algebra]
QED

Theorem Borel_space_alt_sigma :
    Borel_space (:'N) =
    sigma univ(:extreal['N])
          {rectangle h (:'N) | !i. i < dimindex(:'N) ==> h i IN subsets Borel}
Proof
    rw [SPACE_BOREL, SIGMA_ALGEBRA_BOREL, Borel_space_def,
        sigma_of_dimension_alt_sigma_algebra, RECTANGLE_UNIV]
QED

(* |- !h. (!i. i < dimindex (:'N) ==> h i IN subsets borel) ==>
          rectangle h (:'N) IN subsets (borel_space (:'N))
 *)
Theorem rectangle_in_borel_space =
    REWRITE_RULE [sigma_algebra_borel, GSYM borel_space_def]
                 (ISPEC “borel” rectangle_in_sigma_of_dimension)

(* |- !h. (!i. i < dimindex (:'N) ==> h i IN subsets Borel) ==>
          rectangle h (:'N) IN subsets (Borel_space (:'N))
 *)
Theorem RECTANGLE_IN_BOREL_SPACE =
    REWRITE_RULE [SIGMA_ALGEBRA_BOREL, GSYM Borel_space_def]
                 (ISPEC “Borel” rectangle_in_sigma_of_dimension)

(* (M + N)-dimensional prod space is the product sigma-algebra of M- and N-dimensional
    prod spaces. (The key of this proof is prod_sigma_of_generator.)
 *)
Theorem sigma_of_dimension_decomposition :
    !(B :'a algebra).
      subset_class (space B) (subsets B) /\ space B IN subsets B /\
      FINITE univ(:'M) /\ FINITE univ(:'N) ==>
      B of_dimension (:'M + 'N) = fcp_sigma (B of_dimension (:'M)) (B of_dimension (:'N))
Proof
    RW_TAC std_ss [sigma_of_dimension_alt]
 (* preparing for prod_sigma_of_generator *)
 >> Q.ABBREV_TAC ‘X = rectangle (\n. space B) (:'M)’
 >> Q.ABBREV_TAC ‘Y = rectangle (\n. space B) (:'N)’
 >> Q.ABBREV_TAC ‘E = {rectangle h (:'M) | !i. i < dimindex(:'M) ==> h i IN subsets B}’
 >> Q.ABBREV_TAC ‘G = {rectangle h (:'N) | !i. i < dimindex(:'N) ==> h i IN subsets B}’
 (* applying prod_sigma_of_generator *)
 >> Know ‘fcp_sigma (sigma X E) (sigma Y G) = fcp_sigma (X,E) (Y,G)’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC prod_sigma_of_generator >> rw [] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       rw [Abbr ‘X’, Abbr ‘E’, subset_class_def, SUBSET_DEF, IN_RECTANGLE] \\
       fs [subset_class_def, IN_RECTANGLE] \\
       METIS_TAC [SUBSET_DEF],
       (* goal 2 (of 4) *)
       rw [Abbr ‘Y’, Abbr ‘G’, subset_class_def, SUBSET_DEF, IN_RECTANGLE] \\
       fs [subset_class_def, IN_RECTANGLE] \\
       METIS_TAC [SUBSET_DEF],
       (* goal 3 (of 4) *)
       rw [has_exhausting_sequence_def, IN_FUNSET, Abbr ‘X’, Abbr ‘E’] \\
       qunabbrevl_tac [‘Y’, ‘G’] \\
       Q.EXISTS_TAC ‘\n. rectangle (\i. space B) (:'M)’ >> rw []
       >- (Q.EXISTS_TAC ‘\i. space B’ >> rw []) \\
       rw [Once EXTENSION, IN_BIGUNION_IMAGE, IN_RECTANGLE],
       (* goal 4 (of 4) *)
       rw [has_exhausting_sequence_def, IN_FUNSET, Abbr ‘Y’, Abbr ‘G’] \\
       qunabbrevl_tac [‘X’, ‘E’] \\
       Q.EXISTS_TAC ‘\n. rectangle (\i. space B) (:'N)’ >> rw []
       >- (Q.EXISTS_TAC ‘\i. space B’ >> rw []) \\
       rw [Once EXTENSION, IN_BIGUNION_IMAGE, IN_RECTANGLE] ])
 >> Rewr'
 (* stage work *)
 >> rw [Abbr ‘X’, Abbr ‘E’, Abbr ‘Y’, Abbr ‘G’, fcp_sigma_def]
 >> Know ‘fcp_cross (rectangle (\n. space B) (:'M)) (rectangle (\n. space B) (:'N)) =
          rectangle (\n. space B) (:'M + 'N)’
 >- (rw [Once EXTENSION, IN_FCP_CROSS] \\
     EQ_TAC >> rw [IN_RECTANGLE]
     >- (RW_TAC fcp_ss [FCP_CONCAT_def] \\
         fs [NOT_LESS] \\
         FIRST_X_ASSUM MATCH_MP_TAC >> rfs [index_sum]) \\
     qexistsl_tac [‘FCP_FST x’, ‘FCP_SND x’] \\
     rw [FCP_CONCAT_REDUCE] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       rw [FCP_FST_def] \\
      ‘n < dimindex(:'M + 'N)’ by rw [index_sum] \\
       RW_TAC fcp_ss [] \\
       FIRST_X_ASSUM MATCH_MP_TAC \\
       rw [index_sum],
       (* goal 2 (of 2) *)
       rw [FCP_SND_def] \\
      ‘n < dimindex(:'M + 'N)’ by rw [index_sum] \\
       RW_TAC fcp_ss [] ])
 >> Rewr'
 >> Suff ‘fcp_prod {rectangle h (:'M) | !i. i < dimindex (:'M) ==> h i IN subsets B}
                   {rectangle h (:'N) | !i. i < dimindex (:'N) ==> h i IN subsets B} =
         {rectangle h (:'M + 'N) | !i. i < dimindex (:'M + 'N) ==> h i IN subsets B}’
 >- Rewr
 >> rw [Once EXTENSION, IN_FCP_PROD]
 >> EQ_TAC >> rw []
 >| [ (* goal 1 (of 2) *)
      rename1 ‘!i. i < dimindex (:'N) ==> g i IN subsets B’ \\
      Q.EXISTS_TAC ‘\i. if i < dimindex(:'N) then g i else h (i - dimindex(:'N))’ \\
      reverse CONJ_TAC
      >- (rw [index_sum] >> fs [NOT_LESS] \\
          FIRST_X_ASSUM MATCH_MP_TAC >> rw []) \\
      rw [Once EXTENSION, IN_FCP_CROSS, IN_RECTANGLE] \\
      EQ_TAC >> rw [] >| (* 2 subgoals *)
      [ (* goal 1.1 (of 2) *)
        Cases_on ‘i < dimindex(:'N)’ >> RW_TAC fcp_ss [FCP_CONCAT_def] \\
        fs [NOT_LESS] \\
        FIRST_X_ASSUM MATCH_MP_TAC >> rfs [index_sum, DIMINDEX_GT_0],
        (* goal 1.2 (of 2) *)
        qexistsl_tac [‘FCP_FST x’, ‘FCP_SND x’] \\
        simp [FCP_CONCAT_REDUCE] \\
        RW_TAC fcp_ss [FCP_FST_def, FCP_SND_def] >| (* 2 subgoals *)
        [ (* goal 1.2.1 (of 2) *)
         ‘i + dimindex(:'N) < dimindex(:'M + 'N)’ by rw [index_sum] \\
          Q.PAT_X_ASSUM ‘!i. i < dimindex (:'M + 'N) ==> P’
            (MP_TAC o (Q.SPEC ‘i + dimindex(:'N)’)) >> rw [],
          (* goal 1.2.2 (of 2) *)
         ‘i < dimindex(:'M + 'N)’ by rw [index_sum] \\
          Q.PAT_X_ASSUM ‘!i. i < dimindex (:'M + 'N) ==> P’ (MP_TAC o (Q.SPEC ‘i’)) \\
          rw [] ] ],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC ‘rectangle (\i. h (i + dimindex(:'N))) (:'M)’ \\
      Q.EXISTS_TAC ‘rectangle h (:'N)’ \\
      rpt STRIP_TAC >| (* 3 subgoals *)
      [ (* goal 2.1 (of 3) *)
        rw [Once EXTENSION, IN_FCP_CROSS, IN_RECTANGLE] \\
        EQ_TAC >> rw [] >| (* 2 subgoals *)
        [ (* goal 2.1.1 (of 2) *)
           qexistsl_tac [‘FCP_FST x’, ‘FCP_SND x’] >> rw [FCP_CONCAT_REDUCE] >|
           [ (* goal 2.1.1.1 (of 2) *)
             rw [FCP_FST_def] \\
            ‘i < dimindex(:'M + 'N)’ by rw [index_sum] \\
             RW_TAC fcp_ss [] \\
             FIRST_X_ASSUM MATCH_MP_TAC >> rw [index_sum],
             (* goal 2.1.1.2 (of 2) *)
             rw [FCP_SND_def] \\
            ‘i < dimindex(:'M + 'N)’ by rw [index_sum] \\
             RW_TAC fcp_ss [] ],
          (* goal 2.1.2 (of 2) *)
          RW_TAC fcp_ss [FCP_CONCAT_def] \\
          rfs [NOT_LESS, index_sum] \\
         ‘h i = h (i - dimindex(:'N) + dimindex(:'N))’ by rw [] >> POP_ORW \\
          FIRST_X_ASSUM MATCH_MP_TAC >> rw [] ],
        (* goal 2.2 (of 3) *)
        Q.EXISTS_TAC ‘\i. h (i + dimindex(:'N))’ >> rw [] \\
        FIRST_X_ASSUM MATCH_MP_TAC >> rw [index_sum],
        (* goal 2.3 (of 3) *)
        Q.EXISTS_TAC ‘h’ >> rw [] \\
        FIRST_X_ASSUM MATCH_MP_TAC >> rw [index_sum] ] ]
QED

(* an application of ‘borel’ *)
Theorem borel_space_decomposition :
    FINITE univ(:'M) /\ FINITE univ(:'N) ==>
    borel_space (:'M + 'N) = fcp_sigma (borel_space (:'M)) (borel_space (:'N))
Proof
    RW_TAC std_ss [borel_space_def]
 >> MATCH_MP_TAC sigma_of_dimension_decomposition >> rw []
 >- rw [subset_class_def, space_borel, SUBSET_DEF]
 >> MATCH_MP_TAC SIGMA_ALGEBRA_SPACE
 >> REWRITE_TAC [sigma_algebra_borel]
QED

(* an application of ‘Borel’ *)
Theorem Borel_space_decomposition :
    FINITE univ(:'M) /\ FINITE univ(:'N) ==>
    Borel_space (:'M + 'N) = fcp_sigma (Borel_space (:'M)) (Borel_space (:'N))
Proof
    RW_TAC std_ss [Borel_space_def]
 >> MATCH_MP_TAC sigma_of_dimension_decomposition >> rw []
 >- rw [subset_class_def, SPACE_BOREL, SUBSET_DEF]
 >> MATCH_MP_TAC SIGMA_ALGEBRA_SPACE
 >> REWRITE_TAC [SIGMA_ALGEBRA_BOREL]
QED

(* |- !sp A f J.
        (!i. i IN J ==> sigma_algebra (A i)) /\
        (!i. f i IN (sp -> space (A i))) ==>
        !i. i IN J ==> f i IN measurable (sigma sp A f J) (A i)
 *)
val lemma =
    SIGMA_SIMULTANEOUSLY_MEASURABLE |> INST_TYPE [“:'b” |-> “:'temp”]
                                    |> INST_TYPE [“:'a” |-> “:'a['N]”]
                                    |> INST_TYPE [“:'index” |-> “:num”]
                                    |> INST_TYPE [“:'temp” |-> “:'a”];

Theorem fcp_simultaneously_measurable :
    !B. sigma_algebra B /\
       (!i. (\v. v ' i) IN (rectangle (\n. space B) (:'N) -> space B)) ==>
        !i. i < dimindex(:'N) ==> (\v. v ' i) IN measurable (B of_dimension(:'N)) B
Proof
    rw [sigma_of_dimension_def, C_DEF]
 >> irule (SIMP_RULE std_ss [C_DEF]
                     (Q.SPECL [‘rectangle (\n. space B) (:'N)’, ‘\n. B’,
                               ‘flip $fcp_index’] lemma))
 >> rw []
QED

(* |- !i. i < dimindex (:'N) ==>
          (\v. v ' i) IN borel_measurable (borel of_dimension (:'N))
 *)
Theorem in_borel_measurable_fcp =
    SIMP_RULE (srw_ss()) [space_borel, sigma_algebra_borel, IN_FUNSET]
              (ISPEC “borel” fcp_simultaneously_measurable)

(* |- !i. i < dimindex (:'N) ==>
          (\v. v ' i) IN Borel_measurable (Borel of_dimension (:'N))
 *)
Theorem IN_MEASURABLE_BOREL_FCP =
    SIMP_RULE (srw_ss()) [SPACE_BOREL, SIGMA_ALGEBRA_BOREL, IN_FUNSET]
              (ISPEC “Borel” fcp_simultaneously_measurable)

(* ------------------------------------------------------------------------- *)
(*  List-based n-dimensional Borel spaces                                    *)
(* ------------------------------------------------------------------------- *)

(* list (cons) version of ‘CROSS’ *)
Definition cons_cross_def :
    cons_cross A B = {CONS a b | a IN A /\ b IN B}
End

Theorem cons_cross_empty[simp] :
    cons_cross {} A = {} /\ cons_cross A {} = {}
Proof
    rw [cons_cross_def]
QED

Theorem cons_cross_alt_gen :
    !A B. cons_cross A B = general_cross CONS A B
Proof
    rw [cons_cross_def, general_cross_def]
QED

(* list (cons) version of ‘prod_sets’ *)
Definition cons_prod_def :
    cons_prod a b = {cons_cross s t | s IN a /\ t IN b}
End

Theorem cons_prod_alt_gen :
    !a b. cons_prod a b = general_prod CONS a b
Proof
    rw [cons_prod_def, general_prod_def, cons_cross_alt_gen]
QED

(* list (cons) version of ‘prod_sigma’ *)
Definition cons_sigma_def :
    cons_sigma (a :'a algebra) (b :'a list algebra) =
      sigma (cons_cross (space a) (space b)) (cons_prod (subsets a) (subsets b))
End

Theorem space_cons_sigma :
    !a b. space (cons_sigma a b) = cons_cross (space a) (space b)
Proof
    rw [cons_sigma_def, SPACE_SIGMA]
QED

Theorem cons_sigma_alt_gen :
    !a b. cons_sigma a b = general_sigma CONS a b
Proof
    rw [cons_sigma_def, cons_cross_alt_gen, cons_prod_alt_gen, general_sigma_def]
QED

val lemma = general_sigma_of_generator
         |> INST_TYPE [beta  |-> “:'a list”, gamma |-> “:'a list”]
         |> Q.SPECL [‘CONS’, ‘HD’, ‘TL’, ‘X’, ‘Y’, ‘E’, ‘G’]
         |> REWRITE_RULE [pair_operation_CONS,
                          GSYM cons_cross_alt_gen,
                          GSYM cons_prod_alt_gen,
                          GSYM cons_sigma_alt_gen];

(* |- !X E Y G.
        subset_class X E /\ subset_class Y G /\
        has_exhausting_sequence (X,E) /\ has_exhausting_sequence (Y,G) ==>
        cons_sigma (X,E) (Y,G) = cons_sigma (sigma X E) (sigma Y G)
 *)
Theorem cons_sigma_of_generator = general_sigma_of_generator
     |> INST_TYPE [beta  |-> “:'a list”, gamma |-> “:'a list”]
     |> Q.SPECL [‘CONS’, ‘HD’, ‘TL’, ‘X’, ‘Y’, ‘E’, ‘G’]
     |> REWRITE_RULE [pair_operation_CONS,
                      GSYM cons_cross_alt_gen,
                      GSYM cons_prod_alt_gen,
                      GSYM cons_sigma_alt_gen]
     |> Q.GENL [‘X’, ‘E’, ‘Y’, ‘G’]

(* NOTE: ‘0 < N’ is a reasonable assumption sometimes *)
Definition list_rectangle_def :
    list_rectangle (h :num -> 'a set) N =
      {v | LENGTH v = N /\ !i. i < N ==> EL i v IN h i}
End
Overload rectangle = “list_rectangle”

(* NOTE: (\e. [e]) is a bijection *)
Theorem list_rectangle_1 :
    !h. rectangle h 1 = IMAGE (\e. [e]) (h 0)
Proof
    rw [Once EXTENSION, list_rectangle_def]
 >> EQ_TAC >> rw []
 >- (Q.EXISTS_TAC ‘HD x’ >> rw [])
 >> rw []
QED

Theorem list_rectangle_UNIV :
    list_rectangle (\n. UNIV) N = {v | LENGTH v = N}
Proof
    rw [list_rectangle_def, Once EXTENSION]
QED

Theorem IN_list_rectangle :
    !v h N. v IN list_rectangle h N <=>
            LENGTH v = N /\ !i. i < N ==> EL i v IN h i
Proof
    rw [list_rectangle_def, Once EXTENSION]
QED

Theorem list_rectangle_SUC :
    !h n. rectangle h (SUC n) = cons_cross (h 0) (rectangle (h o SUC) n)
Proof
    rw [cons_cross_def, Once EXTENSION, IN_list_rectangle, o_DEF]
 >> EQ_TAC >> rw []
 >- (Cases_on ‘x’ >> fs [] \\
     CONJ_TAC >- (POP_ASSUM (MP_TAC o Q.SPEC ‘0’) >> rw []) \\
     rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < SUC n ==> P’ (MP_TAC o Q.SPEC ‘SUC i’) >> rw [])
 >- rw []
 >> Cases_on ‘i’ >> fs []
QED

Theorem PREIMAGE_list_rectangle :
    !(f :'a -> 'b list) (h :num -> 'b set) N.
        (!x. LENGTH (f x) = N) ==>
        PREIMAGE f (list_rectangle h N) =
        BIGINTER (IMAGE (\n. PREIMAGE (\x. EL n (f x)) (h n)) (count N))
Proof
    rw [Once EXTENSION, IN_PREIMAGE, IN_list_rectangle]
 >> EQ_TAC >> rw [PREIMAGE_def] >- rw []
 >> Q.PAT_X_ASSUM ‘!P. _ ==> x IN P’
       (MP_TAC o (Q.SPEC ‘{x | EL i ((f :'a -> 'b list) x) IN h i}’))
 >> simp []
 >> DISCH_THEN MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘i’ >> art []
QED

Definition sigma_lists_def :
    sigma_lists B N =
      sigma_functions (rectangle (\n. space B) N) (\n. B) EL (count N)
End

Theorem sigma_algebra_sigma_lists :
    !(B :'a algebra) N. sigma_algebra (sigma_lists B N)
Proof
    rw [sigma_lists_def, sigma_functions_def, list_rectangle_def]
 >> MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA
 >> rw [subset_class_def, SUBSET_DEF, IN_BIGUNION_IMAGE]
 >> fs [IN_INTER, IN_PREIMAGE]
QED

Theorem space_sigma_lists :
    !(B :'a algebra) N. space (sigma_lists B N) = rectangle (\n. space B) N
Proof
    rw [sigma_lists_def, sigma_functions_def, SPACE_SIGMA]
QED

(* cf. sigma_of_dimension_alt *)
Theorem sigma_lists_alt :
    !(B :'a algebra) N.
      subset_class (space B) (subsets B) /\ space B IN subsets B /\ 0 < N ==>
      sigma_lists B N =
      sigma (list_rectangle (\n. space B) N)
            {list_rectangle h N | h | !i. i < N ==> h i IN subsets B}
Proof
    rw [sigma_lists_def, sigma_functions_def]
 >> Q.ABBREV_TAC (* this is part of the goal, to be replaced by ‘sts’ *)
   ‘src = BIGUNION
            (IMAGE (\n. IMAGE (\s. PREIMAGE (EL n) s INTER rectangle (\n. space B) N)
                              (subsets B))
                   (count N))’
 >> Q.ABBREV_TAC
   ‘sts = BIGUNION (IMAGE (\n. {rectangle h N | h |
                                                h n IN subsets B /\
                                                !i. i < N /\ i <> n ==> h i = space B})
                          (count N))’
 >> Know ‘src = sts’
 >- (rw [Abbr ‘src’, Abbr ‘sts’, Once EXTENSION, PREIMAGE_def] \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       fs [IN_IMAGE] >> rename1 ‘b IN subsets B’ \\
       Q.EXISTS_TAC ‘{rectangle h N | h |
                      h n IN subsets B /\ !i. i < N /\ i <> n ==> h i = space B}’ \\
       reverse (rw []) >- (Q.EXISTS_TAC ‘n’ >> art []) \\
       Q.EXISTS_TAC ‘\i. if i = n then b else space B’ >> rw [] \\
       rw [list_rectangle_def, Once EXTENSION] \\
       EQ_TAC >> rw [] >| (* 3 trivial subgoals *)
       [ (* goal 1.1 (of 3) *)
         Cases_on ‘i = n’ >> rw [],
         (* goal 1.2 (of 3) *)
         POP_ASSUM (MP_TAC o (Q.SPEC ‘n’)) >> rw [],
         (* goal 1.3 (of 3) *)
         rename1 ‘EL i x IN space B’ \\
         Q.PAT_X_ASSUM ‘!i. i < LENGTH x ==> P’ (MP_TAC o (Q.SPEC ‘i’)) \\
         Cases_on ‘i = n’ >> rw [] \\
         FULL_SIMP_TAC std_ss [subset_class_def] \\
         METIS_TAC [SUBSET_DEF] ],
       (* goal 2 (of 2) *)
       fs [] \\
       Q.EXISTS_TAC ‘IMAGE (\s. {v | EL n v IN s} INTER rectangle (\n. space B) N)
                           (subsets B)’ \\
       reverse (rw []) >- (Q.EXISTS_TAC ‘n’ >> art []) \\
       Q.EXISTS_TAC ‘h n’ \\
       rw [list_rectangle_def, Once EXTENSION] \\
       EQ_TAC >> rw [] >| (* 2 trivial subgoals *)
       [ (* goal 2.1 (of 2) *)
         rename1 ‘EL i x IN space B’ \\
         Cases_on ‘i = n’
         >- (Q.PAT_X_ASSUM ‘!i. i < LENGTH x ==> EL i x IN h i’ (MP_TAC o (Q.SPEC ‘n’)) \\
             rw [] \\
             FULL_SIMP_TAC std_ss [subset_class_def] \\
             METIS_TAC [SUBSET_DEF]) \\
         Q.PAT_X_ASSUM ‘!i. i < LENGTH x /\ i <> n ==> P’ (MP_TAC o (Q.SPEC ‘i’)) \\
         Q.PAT_X_ASSUM ‘!i. i < LENGTH x ==> EL i x IN h i’ (MP_TAC o (Q.SPEC ‘i’)) \\
         rw [] >> fs [],
         (* goal 2.2 (of 2) *)
         Cases_on ‘i = n’ >> rw [] ] ])
 >> Rewr'
 >> Q.UNABBREV_TAC ‘src’ (* not needed any more *)
 (* stage work *)
 >> Know ‘sigma_algebra (sigma (rectangle (\n. space B) N) sts)’
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
     rw [Abbr ‘sts’, subset_class_def, SUBSET_DEF] \\
     gs [IN_list_rectangle] \\
     Q.PAT_X_ASSUM ‘x = rectangle h N’ K_TAC \\
     rename1 ‘!i. i < N ==> EL i x IN h i’ \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < N ==> P’ (MP_TAC o (Q.SPEC ‘i’)) \\
     RW_TAC std_ss [] \\
     FULL_SIMP_TAC std_ss [subset_class_def] \\
     Cases_on ‘i = n’ >- (rw [] >> METIS_TAC [SUBSET_DEF]) \\
     Q.PAT_X_ASSUM ‘!i. i < N /\ i <> n ==> P’ (MP_TAC o (Q.SPEC ‘i’)) \\
     RW_TAC std_ss [] >> fs [])
 >> DISCH_TAC
 >> ‘sts SUBSET subsets (sigma (rectangle (\n. space B) N) sts)’
       by PROVE_TAC [SIGMA_SUBSET_SUBSETS]
 >> Q.ABBREV_TAC ‘prod = {rectangle h N | h | !i. i < N ==> h i IN subsets B}’
 >> Know ‘prod SUBSET subsets (sigma (rectangle (\n. space B) N) sts)’
 >- (rw [Abbr ‘prod’, SUBSET_DEF] \\
     Know ‘rectangle h N =
           BIGINTER (IMAGE (\n. {v | LENGTH v = N /\ EL n v IN h n /\
                                     !i. i < N /\ i <> n ==> EL i v IN space B})
                           (count N))’
     >- (rw [list_rectangle_def, Once EXTENSION, IN_BIGINTER_IMAGE] \\
         reverse EQ_TAC >> rw []
         >- (POP_ASSUM (MP_TAC o Q.SPEC ‘0’) >> rw []) \\ (* 0 < N is used here *)
         FULL_SIMP_TAC std_ss [subset_class_def] \\
         METIS_TAC [SUBSET_DEF]) >> Rewr' \\
  (* applying SIGMA_ALGEBRA_FINITE_INTER *)
     MATCH_MP_TAC SIGMA_ALGEBRA_FINITE_INTER >> rw [] \\
     qmatch_abbrev_tac ‘A IN _’ \\
     Suff ‘A IN sts’ >- PROVE_TAC [SUBSET_DEF] \\
     Q.PAT_X_ASSUM ‘sigma_algebra _’ K_TAC \\
     Q.PAT_X_ASSUM ‘sts SUBSET _’    K_TAC \\
     rw [Abbr ‘A’, Abbr ‘sts’, IN_BIGUNION_IMAGE] \\
     Q.EXISTS_TAC ‘i’ >> rw [] \\
     rename1 ‘n < N’ \\
     Q.EXISTS_TAC ‘\i. if i = n then h n else space B’ >> rw [] \\
     rw [list_rectangle_def, Once EXTENSION] \\
     EQ_TAC >> rw [] >| (* 3 trivial subgoals *)
     [ (* goal 1.1 (of 3) *)
       Cases_on ‘i = n’ >> rw [],
       (* goal 1.2 (of 3) *)
       POP_ASSUM (MP_TAC o (Q.SPEC ‘n’)) >> rw [],
       (* goal 1.3 (of 3) *)
       rename1 ‘EL i x IN space B’ \\
       Q.PAT_X_ASSUM ‘!i. i < N ==> P’ (MP_TAC o (Q.SPEC ‘i’)) \\
       Cases_on ‘i = n’ >> rw [] ])
 >> DISCH_TAC
 >> Suff ‘subsets (sigma (rectangle (\n. space B) N) sts) =
          subsets (sigma (rectangle (\n. space B) N) prod)’
 >- METIS_TAC [SPACE, SPACE_SIGMA]
 >> MATCH_MP_TAC SIGMA_SMALLEST >> art []
 >> reverse CONJ_TAC >- METIS_TAC [SPACE, SPACE_SIGMA]
 (* stage work *)
 >> MP_TAC (ISPECL [“sts :('a list set) set”,
                    “sigma (rectangle (\n. space B) N) (prod :('a list set) set)”]
                    SIGMA_SUBSET)
 >> REWRITE_TAC [SPACE_SIGMA]
 >> DISCH_THEN MATCH_MP_TAC
 >> CONJ_TAC
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
     rw [Abbr ‘prod’, subset_class_def, IN_list_rectangle, SUBSET_DEF]
     >- (fs [IN_list_rectangle]) \\
     rename1 ‘EL n x IN space B’ \\
     fs [IN_list_rectangle] \\
     FULL_SIMP_TAC std_ss [subset_class_def] \\
     METIS_TAC [SUBSET_DEF])
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘prod’
 >> REWRITE_TAC [SIGMA_SUBSET_SUBSETS]
 >> Q.PAT_X_ASSUM ‘sigma_algebra _’ K_TAC
 >> Q.PAT_X_ASSUM ‘sts SUBSET _’    K_TAC
 >> Q.PAT_X_ASSUM ‘prod SUBSET _’   K_TAC
 >> rw [Abbr ‘sts’, Abbr ‘prod’, SUBSET_DEF]
 >> fs [IN_list_rectangle]
 >> Q.EXISTS_TAC ‘h’ >> rw []
 >> Cases_on ‘i = n’ >> rw []
QED

(* cf. sigma_of_dimension_alt_sigma_algebra *)
Theorem sigma_lists_alt_sigma_algebra :
    !(B :'a algebra) N. sigma_algebra B /\ 0 < N ==>
      sigma_lists B N =
      sigma (rectangle (\n. space B) N)
            {rectangle h N | h | !i. i < N ==> h i IN subsets B}
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC sigma_lists_alt >> art []
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SPACE >> art [])
 >> fs [sigma_algebra_def, algebra_def]
QED

(* NOTE: This is a difficult result. It gives another alternative definition of
   sigma_lists using the very 1-dimensional generator. --Chun Tian, 25 ago 2024
 *)
Theorem sigma_lists_alt_generator :
    !sp sts N.
      subset_class sp sts /\ has_exhausting_sequence (sp,sts) /\ 0 < N ==>
      sigma_lists (sigma sp sts) N =
      sigma (rectangle (\n. sp) N) {rectangle h N | h | !i. i < N ==> h i IN sts}
Proof
    rw [sigma_lists_def, sigma_functions_def, SPACE_SIGMA]
 >> Q.ABBREV_TAC (* this is part of the goal, to be replaced by ‘src'’ *)
   ‘src = BIGUNION
            (IMAGE (\n. IMAGE (\s. PREIMAGE (EL n) s INTER rectangle (\n. sp) N)
                              (subsets (sigma sp sts)))
                   (count N))’
 (* src' eliminates PREIMAGE from ‘src’ *)
 >> Q.ABBREV_TAC
   ‘src' = BIGUNION (IMAGE (\n. {rectangle h N | h |
                                 h n IN subsets (sigma sp sts) /\
                                 !i. i < N /\ i <> n ==> h i = sp})
                           (count N))’
 >> Know ‘src = src'’
 >- (rw [Abbr ‘src’, Abbr ‘src'’, Once EXTENSION, PREIMAGE_def] \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       fs [IN_IMAGE] >> rename1 ‘b IN subsets (sigma sp sts)’ \\
       Q.EXISTS_TAC ‘{rectangle h N | h | h n IN subsets (sigma sp sts) /\
                                          !i. i < N /\ i <> n ==> h i = sp}’ \\
       reverse (rw []) >- (Q.EXISTS_TAC ‘n’ >> art []) \\
       Q.EXISTS_TAC ‘\i. if i = n then b else sp’ >> rw [] \\
       rw [list_rectangle_def, Once EXTENSION] \\
       EQ_TAC >> rw [] >| (* 3 trivial subgoals *)
       [ (* goal 1.1 (of 3) *)
         Cases_on ‘i = n’ >> rw [],
         (* goal 1.2 (of 3) *)
         POP_ASSUM (MP_TAC o (Q.SPEC ‘n’)) >> rw [],
         (* goal 1.3 (of 3) *)
         rename1 ‘EL i x IN sp’ \\
         Q.PAT_X_ASSUM ‘!i. i < LENGTH x ==> P’ (MP_TAC o (Q.SPEC ‘i’)) \\
         Cases_on ‘i = n’ >> rw [] \\
         qabbrev_tac ‘a = sigma sp sts’ \\
        ‘sigma_algebra a’ by rw [Abbr ‘a’, SIGMA_ALGEBRA_SIGMA] \\
        ‘space a = sp’ by rw [Abbr ‘a’, SPACE_SIGMA] \\
         Q.PAT_X_ASSUM ‘EL i x IN b’ MP_TAC \\
         Suff ‘b SUBSET sp’ >- rw [SUBSET_DEF] \\
         fs [sigma_algebra_def, algebra_def, subset_class_def] ],
       (* goal 2 (of 2) *)
       fs [] \\
       Q.EXISTS_TAC ‘IMAGE (\s. {v | EL n v IN s} INTER rectangle (\n. sp) N)
                           (subsets (sigma sp sts))’ \\
       reverse (rw []) >- (Q.EXISTS_TAC ‘n’ >> art []) \\
       Q.EXISTS_TAC ‘h n’ \\
       rw [list_rectangle_def, Once EXTENSION] \\
       EQ_TAC >> rw [] >| (* 2 subgoals *)
       [ (* goal 2.1 (of 2) *)
         rename1 ‘EL i x IN sp’ \\
         Cases_on ‘i = n’
         >- (Q.PAT_X_ASSUM ‘!i. i < LENGTH x ==> EL i x IN h i’ (MP_TAC o (Q.SPEC ‘n’)) \\
             rw [] \\
             qabbrev_tac ‘a = sigma sp sts’ \\
            ‘sigma_algebra a’ by rw [Abbr ‘a’, SIGMA_ALGEBRA_SIGMA] \\
            ‘space a = sp’ by rw [Abbr ‘a’, SPACE_SIGMA] \\
             Q.PAT_X_ASSUM ‘EL i x IN h i’ MP_TAC \\
             Suff ‘h i SUBSET sp’ >- rw [SUBSET_DEF] \\
             fs [sigma_algebra_def, algebra_def, subset_class_def]) \\
         Q.PAT_X_ASSUM ‘!i. i < LENGTH x /\ i <> n ==> P’ (MP_TAC o (Q.SPEC ‘i’)) \\
         Q.PAT_X_ASSUM ‘!i. i < LENGTH x ==> EL i x IN h i’ (MP_TAC o (Q.SPEC ‘i’)) \\
         rw [] >> fs [],
         (* goal 2.2 (of 2) *)
         Cases_on ‘i = n’ >> rw [] ] ])
 >> Rewr'
 >> qunabbrev_tac ‘src’ (* no more needed *)
 (* stage work *)
 >> Know ‘sigma_algebra (sigma (rectangle (\n. sp) N) src')’
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
     rw [Abbr ‘src'’, subset_class_def, SUBSET_DEF] \\
     gs [IN_list_rectangle] \\
     Q.PAT_X_ASSUM ‘x = rectangle h N’ K_TAC \\
     rename1 ‘!i. i < N ==> EL i x IN h i’ \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < N ==> P’ (MP_TAC o (Q.SPEC ‘i’)) \\
     RW_TAC std_ss [] \\
     reverse (Cases_on ‘i = n’)
     >- (Q.PAT_X_ASSUM ‘!i. i < N /\ i <> n ==> P’ (MP_TAC o (Q.SPEC ‘i’)) \\
        RW_TAC std_ss [] >> fs []) \\
     POP_ASSUM (fs o wrap) \\
     qabbrev_tac ‘a = sigma sp sts’ \\
    ‘sigma_algebra a’ by rw [Abbr ‘a’, SIGMA_ALGEBRA_SIGMA] \\
    ‘space a = sp’ by rw [Abbr ‘a’, SPACE_SIGMA] \\
     Q.PAT_X_ASSUM ‘EL n x IN h n’ MP_TAC \\
     Suff ‘h n SUBSET sp’ >- rw [SUBSET_DEF] \\
     fs [sigma_algebra_def, algebra_def, subset_class_def])
 >> DISCH_TAC
 >> ‘src' SUBSET subsets (sigma (rectangle (\n. sp) N) src')’
       by PROVE_TAC [SIGMA_SUBSET_SUBSETS]
 (* ‘prod’ further eliminates ‘BIGUNION IMAGE ...’ *)
 >> Q.ABBREV_TAC ‘prod = {rectangle h N | h | !i. i < N ==> h i IN subsets (sigma sp sts)}’
 >> Know ‘prod SUBSET subsets (sigma (rectangle (\n. sp) N) src')’
 >- (rw [Abbr ‘prod’, SUBSET_DEF] \\
     Know ‘rectangle h N =
           BIGINTER (IMAGE (\n. {v | LENGTH v = N /\ EL n v IN h n /\
                                     !i. i < N /\ i <> n ==> EL i v IN sp})
                           (count N))’
     >- (rw [list_rectangle_def, Once EXTENSION, IN_BIGINTER_IMAGE] \\
         reverse EQ_TAC >> rw []
         >- (POP_ASSUM (MP_TAC o Q.SPEC ‘0’) >> rw []) \\ (* 0 < N is used here *)
         Q.PAT_X_ASSUM ‘!i. i < LENGTH x ==> EL i x IN h i’ (MP_TAC o Q.SPEC ‘i’) \\
         simp [] \\
         Suff ‘h i SUBSET sp’ >- rw [SUBSET_DEF] \\
         qabbrev_tac ‘a = sigma sp sts’ \\
        ‘sigma_algebra a’ by rw [Abbr ‘a’, SIGMA_ALGEBRA_SIGMA] \\
        ‘space a = sp’ by rw [Abbr ‘a’, SPACE_SIGMA] \\
         fs [sigma_algebra_def, algebra_def, subset_class_def]) >> Rewr' \\
  (* applying SIGMA_ALGEBRA_FINITE_INTER *)
     MATCH_MP_TAC SIGMA_ALGEBRA_FINITE_INTER >> rw [] \\
     qmatch_abbrev_tac ‘A IN _’ \\
     Suff ‘A IN src'’ >- PROVE_TAC [SUBSET_DEF] \\
     Q.PAT_X_ASSUM ‘sigma_algebra _’ K_TAC \\
     Q.PAT_X_ASSUM ‘src' SUBSET _’   K_TAC \\
     rw [Abbr ‘A’, Abbr ‘src'’, IN_BIGUNION_IMAGE] \\
     Q.EXISTS_TAC ‘i’ >> rw [] \\
     rename1 ‘n < N’ \\
     Q.EXISTS_TAC ‘\i. if i = n then h n else sp’ >> rw [] \\
     rw [list_rectangle_def, Once EXTENSION] \\
     EQ_TAC >> rw [] >| (* 3 subgoals *)
     [ (* goal 1.1 (of 3) *)
       Cases_on ‘i = n’ >> rw [],
       (* goal 1.2 (of 3) *)
       POP_ASSUM (MP_TAC o (Q.SPEC ‘n’)) >> rw [],
       (* goal 1.3 (of 3) *)
       PROVE_TAC [] ])
 >> DISCH_TAC
 >> Know ‘subsets (sigma (rectangle (\n. sp) N) src') =
          subsets (sigma (rectangle (\n. sp) N) prod)’
 >- (MATCH_MP_TAC SIGMA_SMALLEST >> art [] \\
     reverse CONJ_TAC >- METIS_TAC [SPACE, SPACE_SIGMA] \\
     MP_TAC (ISPECL [“src' :('a list set) set”,
                     “sigma (rectangle (\n. sp) N) (prod :('a list set) set)”]
                    SIGMA_SUBSET) \\
     REWRITE_TAC [SPACE_SIGMA] \\
     DISCH_THEN MATCH_MP_TAC \\
     CONJ_TAC
     >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
         rw [Abbr ‘prod’, subset_class_def, IN_list_rectangle, SUBSET_DEF]
         >- fs [IN_list_rectangle] \\
         rename1 ‘EL n x IN sp’ \\
         fs [IN_list_rectangle] \\
         qabbrev_tac ‘a = sigma sp sts’ \\
        ‘sigma_algebra a’ by rw [Abbr ‘a’, SIGMA_ALGEBRA_SIGMA] \\
        ‘space a = sp’ by rw [Abbr ‘a’, SPACE_SIGMA] \\
         fs [sigma_algebra_def, algebra_def, subset_class_def] \\
         METIS_TAC [SUBSET_DEF]) \\
     MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC ‘prod’ \\
     REWRITE_TAC [SIGMA_SUBSET_SUBSETS] \\
     Q.PAT_X_ASSUM ‘sigma_algebra _’ K_TAC \\
     Q.PAT_X_ASSUM ‘src' SUBSET _’   K_TAC \\
     Q.PAT_X_ASSUM ‘prod SUBSET _’   K_TAC \\
     rw [Abbr ‘src'’, Abbr ‘prod’, SUBSET_DEF] \\
     fs [IN_list_rectangle] \\
     Q.EXISTS_TAC ‘h’ >> rw [] \\
     Cases_on ‘i = n’ >> rw [] \\
     qabbrev_tac ‘a = sigma sp sts’ \\
    ‘sigma_algebra a’ by rw [Abbr ‘a’, SIGMA_ALGEBRA_SIGMA] \\
    ‘space a = sp’ by rw [Abbr ‘a’, SPACE_SIGMA] \\
     POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) \\
     MATCH_MP_TAC SIGMA_ALGEBRA_SPACE >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘A1 = sigma (rectangle (\n. sp) N) src'’
 >> qabbrev_tac ‘A2 = sigma (rectangle (\n. sp) N) prod’
 >> ‘space A1 = space A2’ by rw [Abbr ‘A1’, Abbr ‘A2’, SPACE_SIGMA]
 >> ‘A1 = A2’ by METIS_TAC [SPACE]
 >> POP_ORW
 (* cleanup A1 *)
 >> Q.PAT_X_ASSUM ‘sigma_algebra A1’        K_TAC
 >> Q.PAT_X_ASSUM ‘prod SUBSET subsets A1’  K_TAC
 >> Q.PAT_X_ASSUM ‘subsets A1 = subsets A2’ K_TAC
 >> Q.PAT_X_ASSUM ‘space A1 = space A2’     K_TAC
 >> Q.PAT_X_ASSUM ‘src' SUBSET subsets _’   K_TAC
 >> qunabbrevl_tac [‘A1’, ‘prod’, ‘src'’, ‘A2’]
 (* final stage *)
 >> qabbrev_tac ‘Z = rectangle (\n. sp) N’
 >> qabbrev_tac ‘sts1 = {rectangle h N | h | !i. i < N ==> h i IN sts}’
 >> qabbrev_tac ‘sts2 = {rectangle h N | h |
                         !i. i < N ==> h i IN subsets (sigma sp sts)}’
 >> Suff ‘subsets (sigma Z sts2) = subsets (sigma Z sts1)’
 >- METIS_TAC [SPACE, SPACE_SIGMA]
 >> MATCH_MP_TAC SUBSET_ANTISYM
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC SIGMA_MONOTONE \\
     rw [Abbr ‘sts1’, Abbr ‘sts2’, SUBSET_DEF] \\
     Q.EXISTS_TAC ‘h’ >> rw [] \\
     Q.PAT_X_ASSUM ‘!i. i < N ==> h i IN sts’ (MP_TAC o Q.SPEC ‘i’) \\
     simp [] \\
     Suff ‘sts SUBSET subsets (sigma sp sts)’ >- rw [SUBSET_DEF] \\
     REWRITE_TAC [SIGMA_SUBSET_SUBSETS])
 >> qabbrev_tac ‘b = sigma Z sts1’
 >> ‘Z = space b’ by rw [Abbr ‘b’, SPACE_SIGMA]
 >> POP_ORW
 >> MATCH_MP_TAC SIGMA_SUBSET
 >> CONJ_TAC
 >- (qunabbrev_tac ‘b’ \\
     MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
     rw [Abbr ‘sts1’, Abbr ‘Z’, subset_class_def, SUBSET_DEF, IN_list_rectangle] \\
     fs [IN_list_rectangle] (* two subgoals, one is left *) \\
     rename1 ‘EL n v IN sp’ \\
     Q.PAT_X_ASSUM ‘!i. i < N ==> EL i v IN h i’ (MP_TAC o Q.SPEC ‘n’) \\
     simp [] \\
     Suff ‘h n SUBSET sp’ >- rw [SUBSET_DEF] \\
     fs [subset_class_def])
 (* stage work, now induction on the dimension ‘n’ *)
 >> qunabbrevl_tac [‘b’, ‘sts1’, ‘sts2’, ‘Z’]
 >> Q.PAT_X_ASSUM ‘0 < N’ MP_TAC
 >> Cases_on ‘N’ >> rw []
 >> Q.ID_SPEC_TAC ‘n’
 >> Induct_on ‘n’
 >- (rw [list_rectangle_1] \\
     qabbrev_tac ‘f = \e. [e]’ \\
     Know ‘{IMAGE f (h (0 :num)) | h 0 IN sts} = IMAGE (IMAGE f) sts’
     >- (rw [Once EXTENSION] \\
         EQ_TAC >> rw []
         >- (Q.EXISTS_TAC ‘h 0’ >> art []) \\
         rename1 ‘y IN sts’ \\
         Q.EXISTS_TAC ‘\i. y’ >> rw []) >> Rewr' \\
     Know ‘{IMAGE f (h (0 :num)) | h 0 IN subsets (sigma sp sts)} =
           IMAGE (IMAGE f) (subsets (sigma sp sts))’
     >- (rw [Once EXTENSION] \\
         EQ_TAC >> rw []
         >- (Q.EXISTS_TAC ‘h 0’ >> art []) \\
         rename1 ‘y IN subsets (sigma sp sts)’ \\
         Q.EXISTS_TAC ‘\i. y’ >> rw []) >> Rewr' \\
     Suff ‘IMAGE (IMAGE f) (subsets (sigma sp sts)) =
           subsets (sigma (IMAGE f sp) (IMAGE (IMAGE f) sts))’ >- rw [] \\
     MATCH_MP_TAC IMAGE_SIGMA >> rw [BIJ_ALT, IN_FUNSET] \\
     rw [EXISTS_UNIQUE_THM, Abbr ‘f’])
 (* stage work *)
 >> qabbrev_tac ‘N = SUC n’
 >> qabbrev_tac ‘Z = rectangle (\n. sp) N’
 >> qabbrev_tac ‘S = {rectangle h N | h | !i. i < N ==> h i IN sts}’
 >> qabbrev_tac ‘B = {rectangle h N | h | !i. i < N ==> h i IN subsets (sigma sp sts)}’
 >> qabbrev_tac ‘a = sigma sp sts’
 >> Know ‘{rectangle h (SUC N) | h | !i. i < SUC N ==> h i IN subsets a} =
          cons_prod (subsets a) B’
 >- (rw [cons_prod_def, cons_cross_def, Once EXTENSION] \\
     EQ_TAC >> rw [list_rectangle_def, Once EXTENSION] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       qexistsl_tac [‘h 0’, ‘rectangle (h o SUC) N’] \\
       CONJ_TAC
       >- (rw [Once EXTENSION] \\
           EQ_TAC >> rw [o_DEF, IN_list_rectangle] >| (* 3 subgoals *)
           [ (* goal 1.1 (of 3) *)
             rename1 ‘LENGTH v = SUC N’ \\
             Cases_on ‘v’ >> fs [] \\
             CONJ_TAC >- (POP_ASSUM (MP_TAC o Q.SPEC ‘0’) >> simp []) \\
             rpt STRIP_TAC \\
             Q.PAT_X_ASSUM ‘!i. i < SUC N ==> EL i _ IN h i’ (MP_TAC o Q.SPEC ‘SUC i’) \\
             simp [],
             (* goal 1.2 (of 3) *)
             rw [],
             (* goal 1.3 (of 3) *)
             Cases_on ‘i’ >> rw [] ]) \\
       CONJ_TAC >- (POP_ASSUM (MP_TAC o Q.SPEC ‘0’) >> simp []) \\
       rw [Abbr ‘B’] \\
       Q.EXISTS_TAC ‘h o SUC’ >> rw [o_DEF],
       (* goal 2 (of 2) *)
       Q.EXISTS_TAC ‘\i. if i = 0 then s else IMAGE (EL (i - 1)) t’ \\
       CONJ_TAC
       >- (rw [Once EXTENSION] \\
           EQ_TAC >> rw [] >| (* 3 subgoals *)
           [ (* goal 2.1 (of 3) *)
             rw [] \\
             Q.PAT_X_ASSUM ‘t IN B’ MP_TAC \\
             rw [Abbr ‘B’] >> fs [IN_list_rectangle],
             (* goal 2.2 (of 3) *)
             Cases_on ‘i’ >> rw [],
             (* goal 2.3 (of 3) *)
             rename1 ‘LENGTH v = SUC N’ \\
             Cases_on ‘v’ >> fs [] \\
             CONJ_TAC >- (POP_ASSUM (MP_TAC o Q.SPEC ‘0’) >> rw []) \\
             Q.PAT_X_ASSUM ‘t IN B’ MP_TAC \\
             rw [Abbr ‘B’] >> rw [IN_list_rectangle] \\
             rename1 ‘EL i v IN g i’ \\
             Q.PAT_X_ASSUM ‘!i. i < SUC (LENGTH v) ==> P’ (MP_TAC o Q.SPEC ‘SUC i’) \\
             rw [] >> fs [IN_list_rectangle] ]) \\
       rw [] \\
       Q.PAT_X_ASSUM ‘t IN B’ MP_TAC \\
       rw [Abbr ‘B’, list_rectangle_def] \\
       qabbrev_tac ‘j = i - 1’ >> ‘j < N’ by rw [Abbr ‘j’] \\
       reverse (Cases_on ‘!i. i < N ==> h i <> {}’)
       >- (fs [] \\
           Know ‘{v | LENGTH v = N /\ !i. i < N ==> EL i v IN h i} = {}’
           >- (rw [Once EXTENSION, NOT_IN_EMPTY] \\
               rename1 ‘h k = {}’ \\
               Q.EXISTS_TAC ‘k’ >> rw [NOT_IN_EMPTY]) >> Rewr' \\
           simp [] \\
           MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY \\
           rw [Abbr ‘a’, SIGMA_ALGEBRA_SIGMA]) \\
       Know ‘IMAGE (EL j) {v | LENGTH v = N /\ !i. i < N ==> EL i v IN h i} = h j’
       >- (rw [Once EXTENSION] \\
           EQ_TAC >> rw [] >- (rename1 ‘j < LENGTH v’ >> rw []) \\
           rename1 ‘y IN h j’ \\
           Q.EXISTS_TAC ‘GENLIST (\i. if i = j then y else CHOICE (h i)) N’ \\
           rw [] >> rename1 ‘k <> j’ \\
           rw [CHOICE_DEF]) >> Rewr' \\
       FIRST_X_ASSUM MATCH_MP_TAC >> art [] ])
 >> Rewr'
 (* Applying IH. Note that there's no way to rewrite ‘cons_prod (subsets a) B’ to
    sigma generator of something, thus IH must be leveraged here.
  *)
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘cons_prod (subsets a) (subsets (sigma Z S))’
 >> CONJ_TAC
 >- (rw [SUBSET_DEF, cons_prod_def] \\
     qexistsl_tac [‘s’, ‘t’] >> art [] \\
     POP_ASSUM MP_TAC \\
     fs [SUBSET_DEF])
 >> Q.PAT_X_ASSUM ‘B SUBSET subsets (sigma Z S)’ K_TAC
 >> qunabbrev_tac ‘B’
 >> qabbrev_tac ‘Z' = rectangle (\n. sp) (SUC N)’
 (* Now all explicit set specs are in the language of generator (sts). This is easy
    now, because both parts of ‘cons_prod’ are sigma-algebras.
  *)
 >> Know ‘cons_prod (subsets a) (subsets (sigma Z S)) SUBSET
          subsets (sigma Z' (cons_prod sts S))’
 >- (qabbrev_tac ‘t = cons_prod (subsets a) (subsets (sigma Z S))’ \\
     Suff ‘subsets (sigma Z' (cons_prod sts S)) = subsets (sigma Z' t)’
     >- (Rewr' >> rw [SIGMA_SUBSET_SUBSETS]) \\
     qunabbrevl_tac [‘t’, ‘a’] \\
  (* preparing for cons_sigma_of_generator *)
     Know ‘Z' = cons_cross sp Z’
     >- (rw [Abbr ‘Z'’, Abbr ‘Z’, cons_cross_def, Once EXTENSION, IN_list_rectangle] \\
         EQ_TAC >> rw [] >| (* 3 subgoals *)
         [ (* goal 1 (of 3) *)
           Cases_on ‘x’ >> fs [] \\
           CONJ_TAC >- (POP_ASSUM (MP_TAC o Q.SPEC ‘0’) >> rw []) \\
           rpt STRIP_TAC >> rename1 ‘EL i t IN sp’ \\
           Q.PAT_X_ASSUM ‘!n. n < SUC N ==> P’ (MP_TAC o Q.SPEC ‘SUC i’) >> rw [],
           (* goal 2 (of 3) *)
           rw [],
           (* goal 3 (of 3) *)
           rename1 ‘EL i (a::b) IN sp’ \\
           Cases_on ‘i’ >> fs [] ]) >> Rewr' \\
     qunabbrev_tac ‘Z'’ \\
    ‘sigma (cons_cross sp Z) (cons_prod sts S) = cons_sigma (sp,sts) (Z,S)’
       by (rw [cons_sigma_def]) >> POP_ORW \\
     qabbrev_tac ‘a = sigma sp sts’ \\
     qabbrev_tac ‘b = sigma Z S’ \\
     Know ‘sigma (cons_cross sp Z) (cons_prod (subsets a) (subsets b)) =
           cons_sigma a b’
     >- (rw [cons_sigma_def, Abbr ‘a’, Abbr ‘b’, SPACE_SIGMA]) >> Rewr' \\
  (* applying for cons_sigma_of_generator *)
     qunabbrevl_tac [‘a’, ‘b’] \\
     Suff ‘cons_sigma (sp,sts) (Z,S) =
           cons_sigma (sigma sp sts) (sigma Z S)’ >- METIS_TAC [SPACE] \\
     MATCH_MP_TAC cons_sigma_of_generator >> art [] \\
     STRONG_CONJ_TAC
     >- (rw [Abbr ‘Z’, Abbr ‘S’, subset_class_def] \\
         rw [SUBSET_DEF, IN_list_rectangle] \\
         rename1 ‘EL i x IN sp’ \\
         Q.PAT_X_ASSUM ‘!i. i < LENGTH x ==> EL i x IN h i’ (MP_TAC o Q.SPEC ‘i’) \\
         simp [] \\
         Suff ‘h i SUBSET sp’ >- rw [SUBSET_DEF] \\
         fs [subset_class_def]) >> DISCH_TAC \\
  (* applying has_exhausting_sequence_alt *)
     fs [has_exhausting_sequence_alt, IN_FUNSET] \\
     Q.EXISTS_TAC ‘\n. rectangle (\i. f n) N’ >> simp [] \\
     CONJ_TAC >- (rw [Abbr ‘S’] >> Q.EXISTS_TAC ‘\i. f x’ >> rw []) \\
     CONJ_TAC >- (Q.X_GEN_TAC ‘i’ >> rw [SUBSET_DEF, IN_list_rectangle] \\
                  rename1 ‘j < LENGTH v’ \\
                  Q.PAT_X_ASSUM ‘!j. j < LENGTH v ==> P’ (MP_TAC o Q.SPEC ‘j’) \\
                  simp [] \\
                  Suff ‘f i SUBSET f (SUC i)’ >- PROVE_TAC [SUBSET_DEF] \\
                  rw []) \\
     POP_ASSUM K_TAC \\
     qunabbrev_tac ‘S’ \\
     rw [Once EXTENSION, Abbr ‘Z’, IN_BIGUNION_IMAGE] \\
     EQ_TAC >> rw [IN_list_rectangle]
     >- (rename1 ‘j < LENGTH v’ \\
         rename1 ‘!i. i < LENGTH v ==> EL i v IN f m’ \\
         Q.EXISTS_TAC ‘f m’ >> rw [] \\
         Q.EXISTS_TAC ‘m’ >> rw []) \\
     Q.PAT_X_ASSUM ‘SUC n = LENGTH x’ (fs o wrap o SYM) \\
     qabbrev_tac ‘sp = BIGUNION (IMAGE f univ(:num))’ \\
     Know ‘!i. i < SUC n ==> ?j. EL i x IN f j’
     >- (rpt STRIP_TAC \\
         Q.PAT_X_ASSUM ‘!i. i < SUC n ==> P’ (MP_TAC o Q.SPEC ‘i’) >> rw [] \\
         rename1 ‘EL i x IN f m’ \\
         Q.EXISTS_TAC ‘m’ >> art []) \\
     Q.PAT_X_ASSUM ‘!i. i < SUC n ==> P’ K_TAC \\
     DISCH_TAC \\
     fs [EXT_SKOLEM_THM'] \\
     rename1 ‘!i. i < SUC n ==> EL i x IN f (g i)’ \\
     qabbrev_tac ‘k = MAX_SET (IMAGE g (count1 n))’ \\
     Q.EXISTS_TAC ‘k’ >> rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < SUC n ==> P’ (MP_TAC o Q.SPEC ‘i’) >> simp [] \\
     Suff ‘f (g i) SUBSET f k’ >- rw [SUBSET_DEF] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     qunabbrev_tac ‘k’ \\
     irule MAX_SET_PROPERTY >> rw [FINITE_IMAGE])
 >> DISCH_TAC
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘subsets (sigma Z' (cons_prod sts S))’
 >> POP_ASSUM (REWRITE_TAC o wrap)
 >> qmatch_abbrev_tac ‘subsets (sigma Z' (cons_prod sts S)) SUBSET subsets b’
 >> ‘Z' = space b’ by rw [Abbr ‘b’, SPACE_SIGMA]
 >> POP_ORW
 >> MATCH_MP_TAC SIGMA_SUBSET
 >> CONJ_TAC
 >- (qunabbrev_tac ‘b’ \\
     MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
     rw [subset_class_def, Abbr ‘Z'’, IN_list_rectangle, SUBSET_DEF]
     >- fs [IN_list_rectangle] \\
     fs [IN_list_rectangle, subset_class_def] \\
     rename1 ‘EL i y IN sp’ \\
     Q.PAT_X_ASSUM ‘!i. i < SUC N ==> EL i y IN h i’ (MP_TAC o Q.SPEC ‘i’) \\
     simp [] \\
     METIS_TAC [SUBSET_DEF])
 (* final goal *)
 >> rw [Abbr ‘b’, SUBSET_DEF, cons_prod_def]
 >> qabbrev_tac ‘S' = {rectangle h (SUC N) | h | (!i. i < SUC N ==> h i IN sts)}’
 >> Know ‘subset_class Z' S'’
 >- (rw [subset_class_def, Abbr ‘Z'’, Abbr ‘S'’] \\
     rw [IN_list_rectangle, SUBSET_DEF] \\
     rename1 ‘i < SUC N’ \\
     Q.PAT_X_ASSUM ‘!i. i < SUC N ==> EL i x IN h i’ (MP_TAC o Q.SPEC ‘i’) \\
     simp [] \\
     Suff ‘h i SUBSET sp’ >- rw [SUBSET_DEF] \\
     fs [subset_class_def])
 >> DISCH_TAC
 >> Know ‘S' SUBSET subsets (sigma Z' S')’ >- rw [SIGMA_SUBSET_SUBSETS]
 >> Suff ‘cons_cross s t IN S'’ >- rw [SUBSET_DEF]
 >> Q.PAT_X_ASSUM ‘t IN S’ MP_TAC
 >> rw [Abbr ‘S’, Abbr ‘S'’, list_rectangle_SUC]
 >> Q.EXISTS_TAC ‘\i. if i = 0 then s else h (i - 1)’
 >> rw [o_DEF, ETA_THM]
QED

(* cf. rectangle_in_sigma_of_dimension *)
Theorem list_rectangle_in_sigma_lists :
    !B h N. sigma_algebra B /\ (!i. i < N ==> h i IN subsets B) /\ 0 < N ==>
            rectangle h N IN subsets (sigma_lists B N)
Proof
    RW_TAC std_ss [sigma_lists_alt_sigma_algebra]
 >> MATCH_MP_TAC IN_SIGMA >> rw [] (* ‘sigma’ is eliminated here *)
 >> Q.EXISTS_TAC ‘h’ >> art []
QED

(* cf. RECTANGLE_INTER_STABLE *)
Theorem list_rectangle_INTER_STABLE :
  !(B :'a algebra) N C.
     C = {rectangle h N | h | !i. i < N ==> h i IN subsets B} /\
     (!s t. s IN subsets B /\ t IN subsets B ==> s INTER t IN subsets B) ==>
      !s t. s IN C /\ t IN C ==> s INTER t IN C
Proof
    RW_TAC set_ss []
 >> rename1 ‘!i. i < N ==> g i IN subsets B’
 >> Q.EXISTS_TAC ‘\i. (g i) INTER (h i)’
 >> rw [list_rectangle_def, Once EXTENSION]
 >> EQ_TAC >> rw []
QED

(* cf. Borel_space (:'N) in stochastic_processTheory. This is the list version. *)
Definition Borel_lists_def :
   Borel_lists N = sigma_lists Borel N
End

(* |- !N. sigma_algebra (Borel_lists N) *)
Theorem sigma_algebra_Borel_lists =
    REWRITE_RULE [GSYM Borel_lists_def]
                 (ISPEC “Borel” sigma_algebra_sigma_lists)

(* |- !N. Borel_lists N = sigma {v | LENGTH v = N} (\n. Borel) EL (count N): *)
Theorem Borel_lists_alt_sigma_functions =
        Borel_lists_def
     |> REWRITE_RULE [sigma_lists_def, SPACE_BOREL, list_rectangle_UNIV]

Theorem space_Borel_lists :
    !N. space (Borel_lists N) = {v | LENGTH v = N}
Proof
    rw [SPACE_SIGMA, Borel_lists_alt_sigma_functions, sigma_functions_def]
QED

(* cf. Borel_space_alt_sigma *)
Theorem Borel_lists_alt_sigma :
    !N. 0 < N ==>
        Borel_lists N =
        sigma {v | LENGTH v = N}
              {rectangle h N | h | !i. i < N ==> h i IN subsets Borel}
Proof
    rw [SPACE_BOREL, SIGMA_ALGEBRA_BOREL, Borel_lists_def,
        sigma_lists_alt_sigma_algebra, list_rectangle_UNIV]
QED

(* The shape of generator is aligned with Borel_eq_le_ext and Borel_inf_def (below) *)
Theorem Borel_lists_alt_sigma_generator :
    !N. 0 < N ==>
        Borel_lists N =
        sigma {v | LENGTH v = N}
              {rectangle h N | h | !i. i < N ==> ?c. h i = {x | x <= c}}
Proof
    rw [Borel_lists_def, Borel_eq_le_ext]
 >> qabbrev_tac ‘sts = IMAGE (\c. {x | x <= c}) univ(:extreal)’
 >> qabbrev_tac ‘sp = univ(:extreal)’
 >> Know ‘{rectangle h N | h | !i. i < N ==> ?c. h i = {x | x <= c}} =
          {rectangle h N | h | !i. i < N ==> h i IN sts}’
 >- (rw [Once EXTENSION, Abbr ‘sts’, Abbr ‘sp’])
 >> Rewr'
 >> Know ‘{v | LENGTH v = N} = rectangle (\n. sp) N’
 >- rw [list_rectangle_UNIV, Abbr ‘sp’]
 >> Rewr'
 >> MATCH_MP_TAC sigma_lists_alt_generator >> art []
 >> CONJ_TAC
 >- rw [subset_class_def, Abbr ‘sp’]
 >> rw [has_exhausting_sequence_def, IN_FUNSET]
 >> Q.EXISTS_TAC ‘\n. sp’
 >> reverse (rw [])
 >- rw [Once EXTENSION, IN_BIGUNION_IMAGE]
 >> rw [Abbr ‘sts’, Abbr ‘sp’]
 >> Q.EXISTS_TAC ‘PosInf’ >> rw []
QED

(* |- !h N.
        (!i. i < N ==> h i IN subsets Borel) /\ 0 < N ==>
        rectangle h N IN subsets (Borel_lists N)
 *)
Theorem list_rectangle_IN_Borel_lists =
    REWRITE_RULE [SIGMA_ALGEBRA_BOREL, GSYM Borel_lists_def]
                 (ISPEC “Borel” list_rectangle_in_sigma_lists)

(* ‘SUC N’-dimensional prod space is the product sigma-algebra of 1- and N-dimensional
    prod sigmas. (The key of this proof is cons_sigma_of_generator.)
 *)
Theorem sigma_lists_decomposition :
    !(B :'a algebra) N. sigma_algebra B /\ 0 < N ==>
        sigma_lists B (SUC N) = cons_sigma B (sigma_lists B N)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘subset_class (space B) (subsets B)’ by (fs [sigma_algebra_def, algebra_def])
 >> ‘space B IN subsets B ’ by PROVE_TAC [SIGMA_ALGEBRA_SPACE]
 >> RW_TAC std_ss [sigma_lists_alt]
 (* preparing for prod_sigma_of_generator *)
 >> Q.ABBREV_TAC ‘X = rectangle (\n. space B) N’
 >> Q.ABBREV_TAC ‘E = {rectangle h N | h | !i. i < N ==> h i IN subsets B}’
 (* applying cons_sigma_of_generator *)
 >> Know ‘cons_sigma (sigma (space B) (subsets B)) (sigma X E) =
          cons_sigma (space B,subsets B) (X,E)’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC cons_sigma_of_generator >> rw [] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       rw [Abbr ‘X’, Abbr ‘E’, subset_class_def, SUBSET_DEF] \\
       fs [IN_list_rectangle, subset_class_def] \\
       rpt STRIP_TAC >> rename1 ‘LENGTH v = N’ \\
       Q.PAT_X_ASSUM ‘!i. i < N ==> EL i v IN h i’ (MP_TAC o Q.SPEC ‘n’) \\
       simp [] \\
       Suff ‘h n SUBSET space B’ >- (REWRITE_TAC [SUBSET_DEF] >> rw []) \\
       FIRST_X_ASSUM MATCH_MP_TAC >> rw [],
       (* goal 3 (of 4) *)
       rw [has_exhausting_sequence_def, IN_FUNSET] \\
       Q.EXISTS_TAC ‘\i. space B’ >> rw [] \\
       rw [Once EXTENSION, IN_BIGUNION_IMAGE],
       (* goal 3 (of 3) *)
       rw [has_exhausting_sequence_def, IN_FUNSET, Abbr ‘X’, Abbr ‘E’] \\
       Q.EXISTS_TAC ‘\n. list_rectangle (\i. space B) N’ >> rw []
       >- (Q.EXISTS_TAC ‘\i. space B’ >> rw []) \\
       rw [Once EXTENSION, IN_BIGUNION_IMAGE, IN_list_rectangle] ])
 >> simp [SIGMA_STABLE]
 >> DISCH_THEN K_TAC
 (* stage work *)
 >> rw [Abbr ‘X’, Abbr ‘E’, cons_sigma_def]
 >> Know ‘cons_cross (space B) (rectangle (\n. space B) N) =
          rectangle (\n. space B) (SUC N)’
 >- (rw [Once EXTENSION, cons_cross_def] \\
     EQ_TAC >> rw [IN_list_rectangle] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       rw [],
       (* goal 2 (of 3) *)
       Cases_on ‘n’ >> rw [],
       (* goal 3 (of 3) *)
       Cases_on ‘x’ >> fs [] \\
       CONJ_TAC >- (POP_ASSUM (MP_TAC o Q.SPEC ‘0’) >> rw []) \\
       rpt STRIP_TAC \\
       Q.PAT_X_ASSUM ‘!n. n < SUC N ==> P’ (MP_TAC o Q.SPEC ‘SUC n’) \\
       rw [] ])
 >> Rewr'
 >> Suff ‘cons_prod (subsets B)
            {rectangle h N | h | (!i. i < N ==> h i IN subsets B)} =
          {rectangle h (SUC N) | h | !i. i < SUC N ==> h i IN subsets B}’
 >- Rewr
 >> rw [Once EXTENSION, cons_prod_def]
 >> EQ_TAC >> rw []
 >| [ (* goal 1 (of 2) *)
      rename1 ‘!i. i < N ==> g i IN subsets B’ \\
      Q.EXISTS_TAC ‘\i. if i = 0 then s else g (i - 1)’ \\
      reverse CONJ_TAC >- rw [] \\
      rw [Once EXTENSION, cons_cross_def, IN_list_rectangle] \\
      EQ_TAC >> rw [] >| (* 3 subgoals *)
      [ (* goal 1.1 (of 3) *)
        rw [],
        (* goal 1.2 (of 3) *)
        Cases_on ‘i’ >> fs [],
        (* goal 1.3 (of 3) *)
        Cases_on ‘x’ >> fs [] \\
        CONJ_TAC >- (POP_ASSUM (MP_TAC o Q.SPEC ‘0’) >> rw []) \\
        rpt STRIP_TAC \\
        Q.PAT_X_ASSUM ‘!i. i < SUC N ==> P’ (MP_TAC o Q.SPEC ‘SUC i’) \\
        rw [] ],
      (* goal 2 (of 2) *)
      qexistsl_tac [‘h 0’, ‘rectangle (\n. h (SUC n)) N’] \\
      rpt STRIP_TAC >| (* 3 subgoals *)
      [ (* goal 2.1 (of 3) *)
        rw [Once EXTENSION, cons_cross_def, IN_list_rectangle] \\
        EQ_TAC >> rw [] >| (* 3 subgoals *)
        [ (* goal 2.1.1 (of 3) *)
          Cases_on ‘x’ >> fs [] \\
          CONJ_TAC >- (POP_ASSUM (MP_TAC o Q.SPEC ‘0’) >> rw []) \\
          rpt STRIP_TAC \\
          Q.PAT_X_ASSUM ‘!i. i < SUC N ==> P’ (MP_TAC o Q.SPEC ‘SUC n’) \\
          rw [],
          (* goal 2.1.2 (of 3) *)
          rw [],
          (* goal 2.1.2 (of 3) *)
          Cases_on ‘i’ >> fs [] ],
        (* goal 2.2 (of 3) *)
        FIRST_X_ASSUM MATCH_MP_TAC >> rw [],
        (* goal 2.3 (of 3) *)
        Q.EXISTS_TAC ‘\n. h (SUC n)’ >> rw [] ] ]
QED

Theorem Borel_lists_decomposition :
    !N. 0 < N ==> Borel_lists (SUC N) = cons_sigma Borel (Borel_lists N)
Proof
    RW_TAC std_ss [Borel_lists_def]
 >> MATCH_MP_TAC sigma_lists_decomposition
 >> rw [SIGMA_ALGEBRA_BOREL]
QED

(* |- !sp A f J.
        (!i. i IN J ==> sigma_algebra (A i)) /\
        (!i. f i IN (sp -> space (A i))) ==>
        !i. i IN J ==> f i IN measurable (sigma sp A f J) (A i)
 *)
val lemma =
    SIGMA_SIMULTANEOUSLY_MEASURABLE |> INST_TYPE [“:'b” |-> “:'temp”]
                                    |> INST_TYPE [“:'a” |-> “:'a list”]
                                    |> INST_TYPE [“:'index” |-> “:num”]
                                    |> INST_TYPE [“:'temp” |-> “:'a”];

Theorem sigma_lists_simultaneously_measurable :
    !B N. sigma_algebra B /\
         (!i. (EL i) IN (rectangle (\n. space B) N -> space B)) ==>
          !i. i < N ==> (EL i) IN measurable (sigma_lists B N) B
Proof
    rw [sigma_lists_def]
 >> irule (SRULE []
           (Q.SPECL [‘rectangle (\n. space B) N’, ‘\n. B’, ‘EL’, ‘count N’] lemma))
 >> rw []
QED

(* |- !N i. i < N ==> EL i IN Borel_measurable (Borel_lists N) *)
Theorem IN_MEASURABLE_BOREL_EL =
        SRULE [SPACE_BOREL, SIGMA_ALGEBRA_BOREL, IN_FUNSET, GSYM Borel_lists_def]
              (ISPEC “Borel” sigma_lists_simultaneously_measurable)

(* ------------------------------------------------------------------------- *)
(*  Infinite-dimensional Borel space [4, p.178]                              *)
(* ------------------------------------------------------------------------- *)

(* A cylinder is a set of infinite-dimensional values (represented by :num ->
   'a functions) where only the first N dimensions are specified (by h).

   NOTE: The "bottom" of this cylinder is always a rectangle, thus is not the
   general cylinder sets.

   ARB-version: (!n. n < N ==> f n IN h n) /\ !n. N <= n ==> f n = ARB
 *)
Definition cylinder_def :
    cylinder (h :num -> 'a set) N =
       {f :num -> 'a | !n. n < N ==> f n IN h n}
End

(* Converting cylinders back to rectangles by converting infinite sequences to
   finite lists (i.e., cutting off the tails).
 *)
Definition cylinder2rect_def :
    cylinder2rect (c :(num -> 'a) set) N = IMAGE (\f. GENLIST f N) c
End

Theorem cylinder2rect_empty[simp] :
    cylinder2rect {} N = {}
Proof
    rw [cylinder2rect_def]
QED

Theorem cylinder2rect_eq_empty[simp] :
    cylinder2rect c N = {} <=> c = {}
Proof
    rw [cylinder2rect_def]
QED

Theorem cylinder2rect_cylinder[simp] :
    cylinder2rect (cylinder h N) N = rectangle h N
Proof
    rw [cylinder2rect_def, cylinder_def, list_rectangle_def]
 >> rw [Once EXTENSION]
 >> EQ_TAC >> rw []
 >- rw [LENGTH_GENLIST]
 >- rw [EL_GENLIST]
 >> qabbrev_tac ‘N = LENGTH x’
 >> Q.EXISTS_TAC ‘\i. if i < N then EL i x else ARB’ >> rw []
 >> rw [LIST_EQ_REWRITE]
QED

(* NOTE: The type of ‘cylinder h N’ is ‘:(num -> 'a) set’, which just indicates
   a set of infinite space points, which may not be (general) cylinder at all.

   Thus we need a predicate to identify all cylinders in this type. And perhaps
   another predicate to identify its "dimension of bottom".

   NOTE2: The part ‘c = {}’ makes |- is_cylinder (cylinder h N) N holds when some
   h i = {} (which means ‘cylinder h N = {}’ for sure)

   NOTE3: The idea is that, for each vector in the N-rectangle converted from c,
   the original point in the cylinder with the vector as the prefix, must range
   over all possible values in the suffix. For example, if :'a is just :bool, a
   cylinder c (N = 1) of "true, ...", after cutting off the initial "true", must
   ranger over all possible infinite Boolean sequences.
 *)
Definition is_cylinder_def :
    is_cylinder (c :(num -> 'a) set) N <=>
    c = {} \/ !f. GENLIST f N IN cylinder2rect c N ==> f IN c
End

Theorem is_cylinder_empty[simp] :
    is_cylinder {} N
Proof
    rw [is_cylinder_def]
QED

Theorem cylinder_is_cylinder[simp] :
    is_cylinder (cylinder h N) N
Proof
    rw [is_cylinder_def, cylinder_def]
 >> reverse (Cases_on ‘!n. n < N ==> h n <> {}’)
 >- (fs [] >> DISJ1_TAC \\
     rw [Once EXTENSION, NOT_IN_EMPTY] \\
     Q.EXISTS_TAC ‘n’ >> rw [])
 >> DISJ2_TAC
 >> rw [Once EXTENSION]
 >> fs [IN_list_rectangle]
QED

Theorem cylinder2rect_11 :
    !s t N. is_cylinder s N /\ is_cylinder t N ==>
           (cylinder2rect s N = cylinder2rect t N <=> s = t)
Proof
    rw [is_cylinder_def] >> rw []
 >> reverse EQ_TAC >- rw []
 >> rw [cylinder2rect_def, Once EXTENSION]
 >> CCONTR_TAC
 >> ‘s <> t <=> s DIFF t <> {} \/ t DIFF s <> {}’ by SET_TAC []
 >> POP_ASSUM (FULL_SIMP_TAC pure_ss o wrap)
 >| [ (* goal 1 (of 2) *)
      fs [GSYM MEMBER_NOT_EMPTY] \\
      fs [cylinder2rect_def] \\
      Q.PAT_X_ASSUM ‘!x. P <=> Q’ (MP_TAC o Q.SPEC ‘GENLIST x N’) \\
      Know ‘?f'. GENLIST x N = GENLIST f' N /\ f' IN s’
      >- (Q.EXISTS_TAC ‘x’ >> art []) >> simp [] \\
      DISCH_THEN K_TAC \\
      Q.X_GEN_TAC ‘g’ >> rpt STRIP_TAC \\
      Q.PAT_X_ASSUM ‘!f. (?f'. GENLIST f N = GENLIST f' N /\ f' IN t) ==> f IN t’
         (MP_TAC o Q.SPEC ‘x’) \\
      impl_tac >- (Q.EXISTS_TAC ‘g’ >> art []) >> rw [],
      (* goal 2 (of 2) *)
      fs [GSYM MEMBER_NOT_EMPTY, cylinder2rect_def] \\
      Q.PAT_X_ASSUM ‘!x. P <=> Q’ (MP_TAC o SYM o Q.SPEC ‘GENLIST x N’) \\
      Know ‘?f'. GENLIST x N = GENLIST f' N /\ f' IN t’
      >- (Q.EXISTS_TAC ‘x’ >> art []) >> simp [] \\
      DISCH_THEN K_TAC \\
      Q.X_GEN_TAC ‘g’ >> rpt STRIP_TAC \\
      Q.PAT_X_ASSUM ‘!f. (?f'. GENLIST f N = GENLIST f' N /\ f' IN t) ==> f IN t’
         (MP_TAC o Q.SPEC ‘g’) \\
      impl_tac >- (Q.EXISTS_TAC ‘x’ >> art []) >> DISCH_TAC \\
      Q.PAT_X_ASSUM ‘!f. (?f'. GENLIST f N = GENLIST f' N /\ f' IN t) ==> f IN s’
         (MP_TAC o Q.SPEC ‘x’) \\
      impl_tac >- (Q.EXISTS_TAC ‘g’ >> art []) >> rw [] ]
QED

(* NOTE: The choice of this particular generator {x | x <= c} is necessary, as
   it has an exhausting sequence in univ(:extreal set).
 *)
Definition Borel_inf_def :
    Borel_inf =
      sigma UNIV {cylinder h N | 0 < N /\ !i. i < N ==> ?c. h i = {x | x <= c}}
End

Definition Borel_inf1_def :
    Borel_inf1 =
      sigma UNIV {cylinder h N | 0 < N /\ !i. i < N ==> h i IN subsets Borel}
End

(* NOTE: The extra condition ‘is_cylinder c N’ is beyond textbook [4, p.178] *)
Definition Borel_inf2_def :
    Borel_inf2 =
      sigma UNIV {c | ?N. 0 < N /\ is_cylinder c N /\
                          cylinder2rect c N IN subsets (Borel_lists N)}
End

Theorem space_Borel_inf :
    space Borel_inf = UNIV
Proof
    rw [Borel_inf_def, SPACE_SIGMA]
QED

Theorem sigma_algebra_Borel_inf :
    sigma_algebra Borel_inf
Proof
    rw [Borel_inf_def, SIGMA_ALGEBRA_SIGMA_UNIV]
QED

Theorem Borel_inf_SUBSET_inf1[local] :
    subsets Borel_inf SUBSET subsets Borel_inf1
Proof
    REWRITE_TAC [Borel_inf_def]
 >> ‘univ(:num -> extreal) = space Borel_inf1’ by rw [SPACE_SIGMA, Borel_inf1_def]
 >> POP_ORW
 >> MATCH_MP_TAC SIGMA_SUBSET
 >> rw [Borel_inf1_def, SIGMA_ALGEBRA_SIGMA_UNIV]
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘{cylinder h N | 0 < N /\ !i. i < N ==> h i IN subsets Borel}’
 >> rw [SIGMA_SUBSET_SUBSETS]
 >> rw [SUBSET_DEF]
 >> qexistsl_tac [‘h’, ‘N’] >> rw []
 >> Q.PAT_X_ASSUM ‘!i. i < N ==> P’ (MP_TAC o Q.SPEC ‘i’) >> rw []
 >> POP_ORW
 >> rw [BOREL_MEASURABLE_SETS_RC]
QED

Theorem Borel_inf1_SUBSET_inf2[local] :
    subsets Borel_inf1 SUBSET subsets Borel_inf2
Proof
    REWRITE_TAC [Borel_inf1_def]
 >> ‘univ(:num -> extreal) = space Borel_inf2’ by rw [SPACE_SIGMA, Borel_inf2_def]
 >> POP_ORW
 >> MATCH_MP_TAC SIGMA_SUBSET
 >> rw [Borel_inf2_def, SIGMA_ALGEBRA_SIGMA_UNIV]
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘{c | ?N. 0 < N /\ is_cylinder c N /\
                           cylinder2rect c N IN subsets (Borel_lists N)}’
 >> rw [SIGMA_SUBSET_SUBSETS]
 >> rw [SUBSET_DEF]
 >> Q.EXISTS_TAC ‘N’ >> rw []
 >> rw [Borel_lists_alt_sigma]
 >> qmatch_abbrev_tac ‘s IN subsets (sigma X sts)’
 >> Know ‘sts SUBSET subsets (sigma X sts)’ >- rw [SIGMA_SUBSET_SUBSETS]
 >> Suff ‘s IN sts’ >- METIS_TAC [SUBSET_DEF]
 >> rw [Abbr ‘s’, Abbr ‘sts’]
 >> Q.EXISTS_TAC ‘h’ >> art []
QED

Theorem Borel_inf_SUBSET_inf2[local] :
    subsets Borel_inf SUBSET subsets Borel_inf2
Proof
    MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘subsets Borel_inf1’
 >> REWRITE_TAC [Borel_inf_SUBSET_inf1, Borel_inf1_SUBSET_inf2]
QED

(* NOTE: The extra condition ‘is_cylinder c N’ is beyond the textbook [4, p.179] *)
Definition Borel_lists' :
    Borel_lists' N = ({v :extreal list | LENGTH v = N},
                      {cylinder2rect c N | c | c IN subsets Borel_inf /\ is_cylinder c N})
End

(* NOTE: This proof depends on the hard work of Borel_lists_alt_sigma_generator *)
Theorem Borel_lists_SUBSET_Borel_lists' :
    !N. 0 < N ==> subsets (Borel_lists N) SUBSET subsets (Borel_lists' N)
Proof
    Q.X_GEN_TAC ‘N’
 >> DISCH_TAC (* 0 < N *)
 >> qabbrev_tac ‘sp = {v :extreal list | LENGTH v = N}’
 >> simp [SUBSET_DEF]
 >> Q.X_GEN_TAC ‘B’
 >> simp [Borel_lists']
 >> DISCH_TAC
 >> Cases_on ‘B = {}’
 >- (POP_ORW >> Q.EXISTS_TAC ‘{}’ >> simp [] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY \\
     rw [sigma_algebra_Borel_inf])
 (* stage work *)
 >> Q.EXISTS_TAC ‘{f | GENLIST f N IN B}’
 >> CONJ_TAC
 >- (rw [cylinder2rect_def, Once EXTENSION] \\
     reverse EQ_TAC >> rw [] >- art [] \\
     Q.EXISTS_TAC ‘\i. EL i x’ \\
     STRONG_CONJ_TAC
     >- (Know ‘LENGTH x = N’
         >- (ASSUME_TAC (Q.SPEC ‘N’ sigma_algebra_Borel_lists) \\
            ‘space (Borel_lists N) = sp’ by rw [space_Borel_lists] \\
             gs [sigma_algebra_def, algebra_def, subset_class_def] \\
             Q.PAT_X_ASSUM ‘!x. P ==> x SUBSET sp’ (MP_TAC o Q.SPEC ‘B’) >> simp [] \\
             DISCH_TAC \\
             Know ‘x IN sp’ >- METIS_TAC [SUBSET_DEF] \\
             rw [Abbr ‘sp’]) >> DISCH_TAC \\
         fs [Abbr ‘sp’, LIST_EQ_REWRITE]) \\
     DISCH_THEN (art o wrap o SYM))
 >> reverse CONJ_TAC
 >- (rw [is_cylinder_def] >> DISJ2_TAC \\
     rw [Once EXTENSION, cylinder2rect_def] >> fs [])
 (* stage work *)
 >> rfs [Borel_lists_alt_sigma_generator]
 >> qabbrev_tac ‘sts = {B | B SUBSET sp /\ {f | GENLIST f N IN B} IN subsets Borel_inf}’
 >> Suff ‘B IN sts’ >- rw [Abbr ‘sts’, SUBSET_DEF]
 >> ASSUME_TAC sigma_algebra_Borel_inf
 >> Know ‘algebra (sp,sts)’
 >- (rw [algebra_def] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       rw [subset_class_def, Abbr ‘sts’],
       (* goal 2 (of 4) *)
       rw [Abbr ‘sts’] \\
       MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY \\
       rw [SIGMA_ALGEBRA_SIGMA_UNIV, Borel_inf_def],
       (* goal 3 (of 4) *)
       fs [Abbr ‘sts’] \\
      ‘!f. GENLIST f N IN sp’ by rw [Abbr ‘sp’] >> POP_ASSUM (REWRITE_TAC o wrap) \\
       Know ‘{f | GENLIST f N NOTIN s} =
             space Borel_inf DIFF {f | GENLIST f N IN s}’
       >- (rw [Once EXTENSION, space_Borel_inf]) >> Rewr' \\
       MATCH_MP_TAC ALGEBRA_COMPL >> art [] \\
       fs [sigma_algebra_def],
       (* goal 4 (of 4) *)
       fs [Abbr ‘sts’] \\
      ‘{f | GENLIST f N IN s \/ GENLIST f N IN t} =
       {f | GENLIST f N IN s} UNION {f | GENLIST f N IN t}’ by SET_TAC [] \\
       POP_ORW \\
       MATCH_MP_TAC ALGEBRA_UNION >> art [] \\
       fs [sigma_algebra_def] ])
 >> DISCH_TAC
 >> Know ‘sigma_algebra (sp,sts)’
 >- (rw [SIGMA_ALGEBRA_ALT] \\
     Q.PAT_X_ASSUM ‘algebra (sp,sts)’ K_TAC \\
     fs [IN_FUNSET, Abbr ‘sts’] \\
     CONJ_TAC
     >- (rw [IN_BIGUNION_IMAGE, SUBSET_DEF] \\
         rename1 ‘x IN f n’ >> POP_ASSUM MP_TAC \\
         Know ‘f n SUBSET sp’ >- rw [] \\
         SET_TAC []) \\
     Know ‘{f' | ?s. GENLIST f' N IN s /\ ?x. s = f x} =
           BIGUNION (IMAGE (\i. {g | GENLIST g N IN f i}) UNIV)’
     >- (rw [Once EXTENSION, IN_BIGUNION_IMAGE] \\
         EQ_TAC >> rw []
         >- (rename1 ‘GENLIST x N IN f i’ \\
             Q.EXISTS_TAC ‘i’ >> art []) \\
         Q.EXISTS_TAC ‘f i’ >> art [] \\
         Q.EXISTS_TAC ‘i’ >> rw []) >> Rewr' \\
     fs [SIGMA_ALGEBRA_FN] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     rw [IN_FUNSET])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘algebra (sp,sts)’ K_TAC
 >> qabbrev_tac ‘src = {rectangle h N | h | !i. i < N ==> ?c. h i = {x | x <= c}}’
 >> Q.PAT_X_ASSUM ‘B IN subsets (sigma sp src)’ MP_TAC
 >> Suff ‘subsets (sigma sp src) SUBSET sts’ >- rw [SUBSET_DEF]
 >> qabbrev_tac ‘b = (sp,sts)’
 >> ‘sp = space b /\ sts = subsets b’ by rw [Abbr ‘b’]
 >> NTAC 2 POP_ORW
 >> MATCH_MP_TAC SIGMA_SUBSET >> rw [Abbr ‘b’]
 (* stage work *)
 >> Q.PAT_X_ASSUM ‘sigma_algebra (sp,sts)’ K_TAC
 >> rw [SUBSET_DEF, Abbr ‘src’, Abbr ‘sts’]
 >- fs [IN_list_rectangle, Abbr ‘sp’]
 >> fs [Borel_inf_def]
 >> qabbrev_tac ‘sts = {cylinder h N | 0 < N /\
                                      !i. i < N ==> ?c. h i = {x | x <= c}}’
 >> Suff ‘{f | GENLIST f N IN rectangle h N} IN sts’
 >- (Suff ‘sts SUBSET subsets (sigma univ(:num -> extreal) sts)’
     >- rw [SUBSET_DEF] \\
     rw [SIGMA_SUBSET_SUBSETS])
 >> rw [Abbr ‘sts’, IN_list_rectangle, cylinder_def]
 >> qexistsl_tac [‘h’, ‘N’] >> rw []
QED

Theorem Borel_inf2_SUBSET_inf[local] :
    subsets Borel_inf2 SUBSET subsets Borel_inf
Proof
    rw [Borel_inf2_def, SYM space_Borel_inf]
 >> MATCH_MP_TAC SIGMA_SUBSET
 >> rw [sigma_algebra_Borel_inf, SUBSET_DEF]
 >> Know ‘cylinder2rect x N IN subsets (Borel_lists' N)’
 >- METIS_TAC [Borel_lists_SUBSET_Borel_lists', SUBSET_DEF]
 >> POP_ASSUM K_TAC
 >> rw [Borel_lists']
 (* stage work *)
 >> Suff ‘x = c’ >- rw []
 >> Know ‘cylinder2rect x N = cylinder2rect c N <=> x = c’
 >- (MATCH_MP_TAC cylinder2rect_11 >> art [])
 >> DISCH_THEN (fs o wrap)
QED

Theorem Borel_inf_eq_Borel_inf2 :
    Borel_inf = Borel_inf2
Proof
    ‘space Borel_inf  = UNIV’ by rw [SPACE_SIGMA, Borel_inf_def]
 >> ‘space Borel_inf2 = UNIV’ by rw [SPACE_SIGMA, Borel_inf2_def]
 >> Suff ‘subsets Borel_inf = subsets Borel_inf2’
 >- METIS_TAC [SPACE]
 >> MATCH_MP_TAC SUBSET_ANTISYM
 >> REWRITE_TAC [Borel_inf2_SUBSET_inf, Borel_inf_SUBSET_inf2]
QED

Theorem Borel_inf_eq_Borel_inf1 :
    Borel_inf = Borel_inf1
Proof
    ‘space Borel_inf  = UNIV’ by rw [SPACE_SIGMA, Borel_inf_def]
 >> ‘space Borel_inf1 = UNIV’ by rw [SPACE_SIGMA, Borel_inf1_def]
 >> Suff ‘subsets Borel_inf = subsets Borel_inf1’
 >- METIS_TAC [SPACE]
 >> MATCH_MP_TAC SUBSET_ANTISYM
 >> REWRITE_TAC [Borel_inf_SUBSET_inf1, Borel_inf1_SUBSET_inf2,
                 Borel_inf_eq_Borel_inf2]
QED

val _ = export_theory ();
val _ = html_theory "stochastic_process";

(* References:

  [1] Kolmogorov, A.N.: Foundations of the Theory of Probability (Grundbegriffe der
      Wahrscheinlichkeitsrechnung). Chelsea Publishing Company, New York. (1950).
  [2] Chung, K.L.: A Course in Probability Theory, Third Edition. Academic Press (2001).
  [3] Rosenthal, J.S.: A First Look at Rigorous Probability Theory (Second Editoin).
      World Scientific Publishing Company (2006).
  [4] Shiryaev, A.N.: Probability-1. Springer-Verlag New York (2016).
  [5] Shiryaev, A.N.: Probability-2. Springer-Verlag New York (2019).
  [6] Billingsley, P.: Probability and Measure (3rd Edition). Wiley-Interscience (1995).
  [7] Cinlar, E.: Probability and Stochastics. Springer (2011).
  [8] J.L. Doob (1953), Stochastic processes (2nd ed.). John Wiley & Sons, New York.
  [9] Schilling, R.L.: Measures, Integrals and Martingales (Second Edition).
      Cambridge University Press (2017).
  [10] Lindgren, G.: Stationary Stochastic Processes. CRC Press (2012).
  [11] Wentzell, A.D.: Theorie zufalliger Prozesse. Springer-Verlag, Basel (2014).
 *)
