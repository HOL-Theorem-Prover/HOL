(* ========================================================================= *)
(* The Theory of (General) Stochastic Processes (ongoing)                    *)
(*                                                                           *)
(* Author: Chun Tian (binghe) <binghe.lisp@gmail.com> (2021)                 *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open combinTheory arithmeticTheory pred_setTheory pred_setLib numLib hurdUtils
     posetTheory listTheory fcpTheory fcpLib;

open realTheory realLib iterateTheory real_sigmaTheory real_topologyTheory;

open util_probTheory sigma_algebraTheory extrealTheory real_borelTheory
     measureTheory borelTheory lebesgueTheory martingaleTheory
     probabilityTheory;

val _ = new_theory "stochastic_process";

val set_ss = std_ss ++ PRED_SET_ss;
val fcp_ss = std_ss ++ FCP_ss ++ PRED_SET_ss;

(* ------------------------------------------------------------------------- *)
(*  General filtration/martingale with poset indexes (Chapter 25 of [9])     *)
(*  (moved here from martingaleTheory)                                       *)
(* ------------------------------------------------------------------------- *)

Theorem poset_num[simp] :
    poset (univ(:num),$<=)
Proof
    RW_TAC std_ss [poset_def]
 >- (Q.EXISTS_TAC ‘0’ >> REWRITE_TAC [GSYM IN_APP, IN_UNIV])
 >- (MATCH_MP_TAC LESS_EQUAL_ANTISYM >> art [])
 >> MATCH_MP_TAC LESS_EQ_TRANS
 >> Q.EXISTS_TAC ‘y’ >> art []
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

(* below J is an index set, R is a partial order on J *)
Definition general_filtration_def :
   general_filtration A a J =
     (poset J /\ (!n. n IN (carrier J) ==> sub_sigma_algebra (a n) A) /\
      (!i j. i IN (carrier J) /\ j IN (carrier J) /\ (relation J) i j ==>
             subsets (a i) SUBSET subsets (a j)))
End

Theorem filtration_alt_general : (* was: filtration_alt *)
    !A a. filtration A a = general_filtration A a (univ(:num),$<=)
Proof
    rw [filtration_def, general_filtration_def, poset_num]
QED

Definition general_filtered_measure_space_def :
    general_filtered_measure_space m a J =
      (measure_space m /\ general_filtration (m_space m,measurable_sets m) a J)
End

Theorem filtered_measure_space_alt_general :
    !m a. filtered_measure_space m a <=>
          general_filtered_measure_space m a (univ(:num),$<=)
Proof
    rw [filtered_measure_space_def, general_filtered_measure_space_def,
        filtration_alt_general, poset_num]
QED

Definition general_sigma_finite_filtered_measure_space_def :
    general_sigma_finite_filtered_measure_space m a J =
      (general_filtered_measure_space m a J /\
       !n. n IN (carrier J) ==> sigma_finite (m_space m,subsets (a n),measure m))
End

Theorem sigma_finite_filtered_measure_space_alt_general :
    !m a. sigma_finite_filtered_measure_space m a <=>
          general_sigma_finite_filtered_measure_space m a (univ(:num),$<=)
Proof
    rw [sigma_finite_filtered_measure_space_alt_all, GSYM CONJ_ASSOC,
        general_sigma_finite_filtered_measure_space_def,
        GSYM filtered_measure_space_alt_general, filtered_measure_space_def]
QED

(* ‘general_martingale m a u (univ(:num),$<=) = martingale m a u’ [1, p.301] *)
Definition general_martingale_def :
   general_martingale m a u J =
     (general_sigma_finite_filtered_measure_space m a J /\
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
    upwards_filtering ({x | 0r <= x},$<=)
Proof
    rw [upwards_filtering_def]
 >> Q.EXISTS_TAC ‘max i j’ >> rw [REAL_LE_MAX]
QED

(* ------------------------------------------------------------------------- *)
(*  n-dimensional (general and extreal-based) Borel spaces                   *)
(* ------------------------------------------------------------------------- *)

(* ‘fcp_rectangle’ is a generalization of ‘fcp_prod’ *)
Definition fcp_rectangle_def :
    fcp_rectangle (h :num -> 'a set) (:'N) =
      {(v :'a['N]) | !i. i < dimindex(:'N) ==> v ' i IN h i}
End
Overload rectangle = “fcp_rectangle”
Theorem rectangle_def[local] = fcp_rectangle_def

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

   This general definition can be used to convert any (1-dimensional) Borel
   sigma-algebra (e.g. ‘borel’ and ‘Borel’) into n-dimensional Borel spaces.
 *)
Definition sigma_of_dimension_def :
    sigma_of_dimension (B :'a algebra) (:'N) =
    sigma_functions (rectangle (\n. space B) (:'N))
                    (\n. B) (\n v. v ' n)
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

   The proof is a generalization of (the proof of) prod_sigma_alt_sigma_functions.

   NOTE: in theory, this theorem (and sigma_of_dimension_def) can be further generalized
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
 >> rw [rectangle_def, Once EXTENSION]
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

(* alternative definition following of_dimension_def *)
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

(* alternative definition following of_dimension_alt *)
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

Theorem rectangle_in_borel_space :
    !h. (!i. i < dimindex(:'N) ==> h i IN subsets borel) ==>
        rectangle h (:'N) IN subsets (borel_space(:'N))
Proof
    rpt STRIP_TAC
 >> MP_TAC (ISPECL [“borel”, “h :num -> real set”] rectangle_in_sigma_of_dimension)
 >> rw [sigma_algebra_borel, GSYM borel_space_def]
QED

Theorem RECTANGLE_IN_BOREL_SPACE :
    !h. (!i. i < dimindex(:'N) ==> h i IN subsets Borel) ==>
        rectangle h (:'N) IN subsets (Borel_space(:'N))
Proof
    rpt STRIP_TAC
 >> MP_TAC (ISPECL [“Borel”, “h :num -> extreal set”] rectangle_in_sigma_of_dimension)
 >> rw [SIGMA_ALGEBRA_BOREL, GSYM Borel_space_def]
QED

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
  [6] Billingsley, P.: Probability and Measure (Third Edition). Wiley-Interscience (1995).
  [7] Cinlar, E.: Probability and Stochastics. Springer (2011).
  [8] J.L. Doob (1953), Stochastic processes (2nd ed.). John Wiley & Sons, New York.
  [9] Schilling, R.L.: Measures, Integrals and Martingales (Second Edition).
      Cambridge University Press (2017).
  [10] Lindgren, G.: Stationary Stochastic Processes. CRC Press (2012).
  [11] Wentzell, A.D.: Theorie zufalliger Prozesse. Springer-Verlag, Basel (2014).
 *)
