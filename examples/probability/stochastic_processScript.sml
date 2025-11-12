(* ========================================================================= *)
(* stochastic_processScript.sml: Theory of General Stochastic Processes      *)
(*                                                                           *)
(* Author: Chun Tian (binghe) <binghe.lisp@gmail.com> (2021 - 2025)          *)
(* ========================================================================= *)
Theory stochastic_process
Ancestors
  combin arithmetic pred_set poset list fcp topology real iterate
  real_sigma real_topology extreal_base extreal sigma_algebra
  real_borel borel measure lebesgue martingale probability
Libs
  pred_setLib numLib hurdUtils fcpLib realLib


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

Overload sum_list = “FOLDR $+ (0 :extreal)”

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
         >- (Q.PAT_X_ASSUM ‘!i. i < dimindex (:'N) ==> x ' i IN h i’
               (MP_TAC o (Q.SPEC ‘n’)) >> rw [] \\
             FULL_SIMP_TAC std_ss [subset_class_def] \\
             METIS_TAC [SUBSET_DEF]) \\
         Q.PAT_X_ASSUM ‘!i. i < dimindex (:'N) /\ i <> n ==> P’
           (MP_TAC o (Q.SPEC ‘i’)) \\
         Q.PAT_X_ASSUM ‘!i. i < dimindex (:'N) ==> x ' i IN h i’
           (MP_TAC o (Q.SPEC ‘i’)) \\
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
                                     !i. i < dimindex (:'N) /\ i <> n ==>
                                         v ' i IN space B})
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
     Q.PAT_X_ASSUM ‘sigma_algebra (sigma (rectangle (\n. space B) (:'N)) sts)’ K_TAC \\
     Q.PAT_X_ASSUM ‘sts SUBSET
                    subsets (sigma (rectangle (\n. space B) (:'N)) sts)’ K_TAC \\
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
   ‘sts = BIGUNION
            (IMAGE (\n. {rectangle h N | h | h n IN subsets B /\
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
         >- (Q.PAT_X_ASSUM ‘!i. i < LENGTH x ==> EL i x IN h i’
               (MP_TAC o (Q.SPEC ‘n’)) >> rw [] \\
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

Definition wrap_def :
    wrap e = [e]
End

Theorem IMAGE_wrap_univ :
    IMAGE wrap univ(:'a) = {v | LENGTH v = 1}
Proof
    rw [Once EXTENSION, wrap_def]
 >> EQ_TAC >> rw []
 >- simp []
 >> Cases_on ‘x’ >> fs []
QED

Theorem LENGTH_wrap[simp] :
    LENGTH (wrap e) = 1
Proof
    rw [wrap_def]
QED

Definition unwrap_def :
    unwrap = EL 0
End

Theorem unwrap_wrap[simp] :
    unwrap (wrap x) = x
Proof
    rw [wrap_def, unwrap_def]
QED

Theorem wrap_unwrap :
    !x. LENGTH x = 1 ==> wrap (unwrap x) = x
Proof
    rw [wrap_def, unwrap_def]
QED

Theorem IMAGE_unwrap_wrap[simp] :
    IMAGE unwrap (IMAGE wrap s) = s
Proof
    rw [Once EXTENSION]
 >> EQ_TAC >> rw [] >- simp []
 >> Q.EXISTS_TAC ‘wrap x’ >> simp []
 >> Q.EXISTS_TAC ‘x’ >> art []
QED

Theorem IMAGE_wrap_unwrap :
    !s. (!e. e IN s ==> LENGTH e = 1) ==> IMAGE wrap (IMAGE unwrap s) = s
Proof
    rpt STRIP_TAC
 >> rw [Once EXTENSION]
 >> EQ_TAC >> rw []
 >- (rename1 ‘wrap (unwrap y) IN s’ \\
     Suff ‘wrap (unwrap y) = y’ >- rw [] \\
     MATCH_MP_TAC wrap_unwrap >> rw [])
 >> ‘LENGTH x = 1’ by PROVE_TAC []
 >> Q.EXISTS_TAC ‘unwrap x’ >> rw [wrap_unwrap]
 >> Q.EXISTS_TAC ‘x’ >> art []
QED

Theorem BIJ_wrap :
    !sp. BIJ wrap sp (IMAGE wrap sp)
Proof
    rw [BIJ_THM, EXISTS_UNIQUE_ALT]
 >> Q.EXISTS_TAC ‘x’
 >> Q.X_GEN_TAC ‘y’
 >> reverse EQ_TAC >> rw [] >> rw []
 >> fs [wrap_def]
QED

Theorem sigma_lists_1 :
    !b. sigma_algebra b ==>
        sigma_lists b 1 = (IMAGE wrap (space b), IMAGE (IMAGE wrap) (subsets b))
Proof
    rw [sigma_lists_alt_sigma_algebra, list_rectangle_1]
 >> qmatch_abbrev_tac ‘_ = (sp,sts)’
 >> Know ‘IMAGE (\e. [e]) (space b) = sp’
 >- rw [Abbr ‘sp’, wrap_def, Once EXTENSION]
 >> Rewr'
 >> Know ‘{IMAGE (\e. [e]) (h (0 :num)) | h 0 IN subsets b} = sts’
 >- (rw [Abbr ‘sts’, wrap_def, Once EXTENSION] \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC ‘h 0’ \\
       rw [Once EXTENSION, wrap_def],
       (* goal 2 (of 2) *)
       rename1 ‘s IN subsets b’ \\
       Q.EXISTS_TAC ‘\x. s’ \\
       rw [Once EXTENSION, wrap_def] ])
 >> Rewr'
 >> MATCH_MP_TAC (SRULE [] (Q.SPEC ‘(sp,sts)’ SIGMA_STABLE))
 >> rw [Abbr ‘sp’, Abbr ‘sts’, sigma_algebra_alt_pow]
 >| [ (* goal 1 (of 4) *)
      rw [SUBSET_DEF, IN_POW] \\
      rename1 ‘s IN subsets b’ \\
      rename1 ‘s' IN IMAGE wrap s’ \\
      POP_ASSUM MP_TAC >> rw [wrap_def] \\
      fs [sigma_algebra_def, algebra_def, subset_class_def] \\
      Q.PAT_X_ASSUM ‘!x. x IN subsets b ==> x SUBSET space b’
        (MP_TAC o Q.SPEC ‘s’) >> rw [SUBSET_DEF],
      (* goal 2 (of 4) *)
      MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY >> art [],
      (* goal 3 (of 4) *)
      Q.EXISTS_TAC ‘space b DIFF x’ \\
      reverse CONJ_TAC >- (MATCH_MP_TAC SIGMA_ALGEBRA_COMPL >> art []) \\
      rw [Once EXTENSION, wrap_def] \\
      EQ_TAC >> rw [] >> art [],
      (* goal 4 (of 4) *)
      POP_ASSUM MP_TAC \\
      rw [SUBSET_DEF, wrap_def] \\
      Q.EXISTS_TAC ‘BIGUNION (IMAGE (\i. IMAGE unwrap (A i)) UNIV)’ \\
      reverse CONJ_TAC
      >- (MATCH_MP_TAC SIGMA_ALGEBRA_ENUM >> rw [IN_FUNSET] \\
          POP_ASSUM (MP_TAC o Q.SPEC ‘A (i :num)’) \\
          impl_tac >- (Q.EXISTS_TAC ‘i’ >> REWRITE_TAC []) \\
          rw [] \\
          rename1 ‘A i = IMAGE wrap s’ \\
          Q.PAT_X_ASSUM ‘A i = IMAGE wrap s’ (REWRITE_TAC o wrap) \\
          simp []) \\
      rw [Once EXTENSION, IN_BIGUNION_IMAGE] \\
      EQ_TAC >> rw []
      >- (Q.PAT_X_ASSUM ‘!x. P’ (MP_TAC o Q.SPEC ‘A (i :num)’) \\
          impl_tac >- (Q.EXISTS_TAC ‘i’ >> REWRITE_TAC []) \\
          rw [] >> rename1 ‘s IN subsets b’ \\
          Q.EXISTS_TAC ‘unwrap x’ \\
          CONJ_TAC
          >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
              MATCH_MP_TAC wrap_unwrap \\
              Q.PAT_X_ASSUM ‘A i = IMAGE wrap s’ (fs o wrap)) \\
          qexistsl_tac [‘i’, ‘x’] >> art []) \\
      rename1 ‘s IN A i’ \\
      Q.EXISTS_TAC ‘A i’ \\
      reverse CONJ_TAC >- (Q.EXISTS_TAC ‘i’ >> REWRITE_TAC []) \\
      Suff ‘wrap (unwrap s) = s’ >- rw [] \\
      MATCH_MP_TAC wrap_unwrap \\
      Q.PAT_X_ASSUM ‘!x. P’ (MP_TAC o Q.SPEC ‘A (i :num)’) \\
      impl_tac >- (Q.EXISTS_TAC ‘i’ >> REWRITE_TAC []) \\
      rw [] >> rename1 ‘t IN subsets b’ \\
      Q.PAT_X_ASSUM ‘A i = IMAGE wrap t’ (fs o wrap) ]
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
         >- (Q.PAT_X_ASSUM ‘!i. i < LENGTH x ==> EL i x IN h i’
               (MP_TAC o (Q.SPEC ‘n’)) >> rw [] \\
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
 >> Q.ABBREV_TAC ‘prod = {rectangle h N | h |
                          !i. i < N ==> h i IN subsets (sigma sp sts)}’
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
 >> qabbrev_tac ‘B = {rectangle h N | h |
                      !i. i < N ==> h i IN subsets (sigma sp sts)}’
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
             Q.PAT_X_ASSUM ‘!i. i < SUC N ==> EL i _ IN h i’
               (MP_TAC o Q.SPEC ‘SUC i’) >> simp [],
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
     >- (rw [Abbr ‘Z'’, Abbr ‘Z’, cons_cross_def, Once EXTENSION,
             IN_list_rectangle] \\
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

(* |- !h N. (!i. i < N ==> h i IN subsets Borel) /\ 0 < N ==>
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

Theorem Borel_lists_1 :
    Borel_lists 1 = (IMAGE wrap univ(:extreal),
                     IMAGE (IMAGE wrap) (subsets Borel))
Proof
    rw [Borel_lists_def, sigma_lists_1, SIGMA_ALGEBRA_BOREL, SPACE_BOREL]
QED

(* |- !sp A f J.
        (!i. i IN J ==> sigma_algebra (A i)) /\
        (!i. i IN J ==> f i IN (sp -> space (A i))) ==>
        !i. i IN J ==> f i IN measurable (sigma sp A f J) (A i)
 *)
val lemma =
    SIGMA_SIMULTANEOUSLY_MEASURABLE |> INST_TYPE [“:'b” |-> “:'temp”]
                                    |> INST_TYPE [“:'a” |-> “:'a list”]
                                    |> INST_TYPE [“:'index” |-> “:num”]
                                    |> INST_TYPE [“:'temp” |-> “:'a”];

Theorem sigma_lists_simultaneously_measurable[local] :
    !B N. sigma_algebra B /\
         (!i. i < N ==> (EL i) IN (rectangle (\n. space B) N -> space B)) ==>
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

(* cf. sigma_algebraTheory.MEASURABLE_FST and MEASURABLE_SND *)
Theorem MEASURABLE_EL :
    !B N. sigma_algebra B ==>
          !i. i < N ==> (EL i) IN measurable (sigma_lists B N) B
Proof
    NTAC 3 STRIP_TAC
 >> MATCH_MP_TAC sigma_lists_simultaneously_measurable >> art []
 >> rw [IN_FUNSET, IN_list_rectangle]
QED

(* cf. sigma_algebraTheory.MEASURABLE_FST *)
Theorem IN_MEASURABLE_BOREL_HD :
    !N. 0 < N ==> HD IN Borel_measurable (Borel_lists N)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘N’, ‘0’] IN_MEASURABLE_BOREL_EL) >> rw []
QED

(* NOTE: “(\x. MAP (\i. f i x) l)” is essentially a random vector. This theorem
   could be further generalised to “sigma_lists B n” but not necessary for now.

   cf. IN_MEASURABLE_BOREL_2D_VECTOR
 *)
Theorem IN_MEASURABLE_BOREL_LISTS :
    !a f l n. sigma_algebra a /\ LENGTH (l :'index list) = n /\ 0 < n /\
             (!i. MEM i l ==> f i IN measurable a Borel) ==>
             (\x. MAP (\i. f i x) l) IN measurable a (Borel_lists n)
Proof
    rw [IN_MEASURABLE, space_Borel_lists, IN_FUNSET, SPACE_BOREL]
 >> qabbrev_tac ‘n = LENGTH l’
 >> Q.PAT_X_ASSUM ‘s IN subsets (Borel_lists n)’ MP_TAC
 >> qabbrev_tac
      ‘P = \s. s IN subsets (Borel_lists n) /\
               PREIMAGE (\x. MAP (\i. f i x) l) s INTER space a IN subsets a’
 >> Suff ‘subsets (Borel_lists n) SUBSET P’
 >- rw [SUBSET_DEF, IN_APP, Abbr ‘P’]
 >> simp [Borel_lists_alt_sigma]
 >> qmatch_abbrev_tac ‘subsets (sigma sp sts) SUBSET P’
 >> qabbrev_tac ‘b = (sp,P)’
 >> ‘P = subsets b’ by rw [Abbr ‘b’] >> POP_ORW
 >> ‘sp = space b’  by rw [Abbr ‘b’] >> POP_ORW
 >> MATCH_MP_TAC SIGMA_SUBSET
 >> reverse CONJ_TAC
 >- (rw [Abbr ‘b’, Abbr ‘P’, Abbr ‘sts’, SUBSET_DEF, Borel_lists_alt_sigma]
     >- (MATCH_MP_TAC IN_SIGMA >> rw [] \\
         Q.EXISTS_TAC ‘h’ >> art []) \\
     qmatch_abbrev_tac ‘PREIMAGE g (rectangle h n) INTER space a IN subsets a’ \\
     MP_TAC (Q.SPECL [‘g’, ‘h’, ‘n’]
                     (INST_TYPE [beta |-> “:extreal”] PREIMAGE_list_rectangle)) \\
     simp [Abbr ‘g’, BIGINTER_OVER_INTER_L] \\
     DISCH_THEN K_TAC (* already used *) \\
     MATCH_MP_TAC SIGMA_ALGEBRA_FINITE_INTER >> rw [EL_MAP] \\
    ‘(\x. f (EL i l) x) = f (EL i l)’ by rw [FUN_EQ_THM] >> POP_ORW \\
     FIRST_X_ASSUM irule >> rw [EL_MEM])
 (* stage work *)
 >> rw [Abbr ‘b’, Abbr ‘P’, sigma_algebra_alt_pow] (* 7 subgoals *)
 >| [ (* goal 1 (of 7) *)
      rw [Abbr ‘sp’, SUBSET_DEF, IN_POW] \\
      MP_TAC (Q.SPEC ‘n’ sigma_algebra_Borel_lists) \\
      rw [sigma_algebra_def, algebra_def, subset_class_def, space_Borel_lists] \\
      Q.PAT_X_ASSUM ‘!x. x IN subsets (Borel_lists n) ==>
                         x SUBSET {v | LENGTH v = n}’ (MP_TAC o Q.SPEC ‘x’) \\
      rw [SUBSET_DEF],
      (* goal 2 (of 7) *)
      MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY \\
      REWRITE_TAC [sigma_algebra_Borel_lists],
      (* goal 3 (of 7) *)
      MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY >> art [],
      (* goal 4 (of 7) *)
      simp [Abbr ‘sp’, GSYM space_Borel_lists] \\
      MATCH_MP_TAC SIGMA_ALGEBRA_COMPL \\
      rw [sigma_algebra_Borel_lists],
      (* goal 5 (of 7) *)
      rw [PREIMAGE_DIFF] \\
      qmatch_abbrev_tac ‘(X DIFF A) INTER space a IN subsets a’ \\
     ‘(X DIFF A) INTER space a = (X INTER space a) DIFF (A INTER space a)’
        by SET_TAC [] >> POP_ORW \\
      Know ‘X INTER space a = space a’
      >- (Suff ‘space a SUBSET X’ >- SET_TAC [] \\
          rw [SUBSET_DEF, Abbr ‘X’, IN_PREIMAGE, Abbr ‘sp’]) >> Rewr' \\
      MATCH_MP_TAC SIGMA_ALGEBRA_COMPL >> art [],
      (* goal 6 (of 7) *)
     ‘BIGUNION {A i | i | T} = BIGUNION (IMAGE A UNIV)’ by rw [Once EXTENSION] \\
      POP_ORW \\
      MATCH_MP_TAC SIGMA_ALGEBRA_ENUM \\
      POP_ASSUM MP_TAC \\
      rw [sigma_algebra_Borel_lists, IN_FUNSET, SUBSET_DEF] \\
      POP_ASSUM (MP_TAC o Q.SPEC ‘A (x :num)’) \\
      impl_tac >- (Q.EXISTS_TAC ‘x’ >> art []) >> rw [],
      (* goal 7 (of 7) *)
     ‘BIGUNION {A i | i | T} = BIGUNION (IMAGE A UNIV)’ by rw [Once EXTENSION] \\
      POP_ORW \\
      simp [PREIMAGE_BIGUNION, IMAGE_IMAGE, o_DEF, BIGUNION_OVER_INTER_L] \\
      MATCH_MP_TAC SIGMA_ALGEBRA_ENUM >> simp [IN_FUNSET] \\
      Q.X_GEN_TAC ‘i’ \\
      POP_ASSUM MP_TAC \\
      rw [SUBSET_DEF] \\
      POP_ASSUM (MP_TAC o Q.SPEC ‘A (i :num)’) \\
      impl_tac >- (Q.EXISTS_TAC ‘i’ >> art []) >> rw [] ]
QED

Theorem IN_MEASURABLE_BOREL_TL :
    !N. 0 < N ==> TL IN measurable (Borel_lists (SUC N)) (Borel_lists N)
Proof
    rw [IN_MEASURABLE, IN_FUNSET, space_Borel_lists]
 >> POP_ASSUM MP_TAC
 >> qabbrev_tac ‘P = \s. s IN subsets (Borel_lists N) /\
                         PREIMAGE TL s INTER {v :extreal list | LENGTH v = SUC N} IN
                         subsets (Borel_lists (SUC N))’
 >> Suff ‘subsets (Borel_lists N) SUBSET P’
 >- simp [SUBSET_DEF, Abbr ‘P’, IN_APP]
 >> simp [Borel_lists_alt_sigma]
 >> qmatch_abbrev_tac ‘subsets (sigma sp sts) SUBSET P’
 >> qabbrev_tac ‘b = (sp,P)’
 >> ‘P = subsets b’ by rw [Abbr ‘b’] >> POP_ORW
 >> ‘sp = space b’  by rw [Abbr ‘b’] >> POP_ORW
 >> MATCH_MP_TAC SIGMA_SUBSET
 >> simp [Abbr ‘b’]
 >> reverse CONJ_TAC
 >- (rw [Abbr ‘sts’, Abbr ‘P’, SUBSET_DEF]
     >- (simp [Borel_lists_alt_sigma] \\
         MATCH_MP_TAC IN_SIGMA >> rw [] \\
         Q.EXISTS_TAC ‘h’ >> simp []) \\
     rw [Borel_lists_alt_sigma, PREIMAGE_def] \\
     MATCH_MP_TAC IN_SIGMA >> rw [] \\
     Q.EXISTS_TAC ‘\i. if i = 0 then UNIV else h (i - 1)’ \\
     CONJ_TAC
     >- (rw [Once EXTENSION] \\
         EQ_TAC >> rw [IN_list_rectangle] >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           Cases_on ‘i’ >> fs [] \\
           Cases_on ‘x’ >> fs [],
           (* goal 2 (of 2) *)
           Cases_on ‘x’ >> fs [] \\
           Q.PAT_X_ASSUM ‘!i. i < SUC N ==> P’ (MP_TAC o Q.SPEC ‘SUC i’) \\
           simp [] ]) \\
     rw [] \\
     REWRITE_TAC [GSYM SPACE_BOREL] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_SPACE \\
     rw [SIGMA_ALGEBRA_BOREL])
 (* stage work *)
 >> rw [sigma_algebra_alt_pow, Abbr ‘P’] (* 7 subgoals *)
 >| [ (* goal 1 (of 7) *)
       rw [SUBSET_DEF, IN_POW] \\
       POP_ASSUM MP_TAC \\
       Suff ‘x SUBSET sp’ >- rw [SUBSET_DEF] \\
       MP_TAC (Q.SPEC ‘N’ sigma_algebra_Borel_lists) \\
       rw [sigma_algebra_def, algebra_def, subset_class_def, space_Borel_lists],
       (* goal 2 (of 7) *)
       MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY \\
       rw [sigma_algebra_Borel_lists],
       (* goal 3 (of 7) *)
       MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY \\
       rw [sigma_algebra_Borel_lists],
       (* goal 4 (of 7) *)
       simp [Abbr ‘sp’, GSYM space_Borel_lists] \\
       MATCH_MP_TAC SIGMA_ALGEBRA_COMPL \\
       rw [sigma_algebra_Borel_lists],
       (* goal 5 (of 7) *)
       simp [PREIMAGE_DIFF] \\
       qmatch_abbrev_tac ‘(A DIFF B) INTER Z IN _’ \\
      ‘(A DIFF B) INTER Z = (A INTER Z) DIFF (B INTER Z)’ by SET_TAC [] \\
       POP_ORW \\
       Know ‘A INTER Z = space (Borel_lists (SUC N))’
       >- (simp [space_Borel_lists] \\
           Suff ‘Z SUBSET A’ >- SET_TAC [] \\
           rw [Abbr ‘Z’, Abbr ‘A’, SUBSET_DEF, IN_PREIMAGE, Abbr ‘sp’] \\
           Cases_on ‘x’ >> fs []) >> Rewr' \\
       MATCH_MP_TAC SIGMA_ALGEBRA_COMPL \\
       rw [sigma_algebra_Borel_lists],
       (* goal 6 (of 7) *)
      ‘{A i | i | T} = IMAGE A UNIV’ by rw [Once EXTENSION] >> POP_ORW \\
       MATCH_MP_TAC SIGMA_ALGEBRA_ENUM \\
       rw [sigma_algebra_Borel_lists, IN_FUNSET] \\
       POP_ASSUM MP_TAC >> rw [SUBSET_DEF] \\
       POP_ASSUM (MP_TAC o Q.SPEC ‘A (x :num)’) \\
       impl_tac >- (Q.EXISTS_TAC ‘x’ >> art []) \\
       simp [],
       (* goal 7 (of 7) *)
      ‘{A i | i | T} = IMAGE A UNIV’ by rw [Once EXTENSION] >> POP_ORW \\
       simp [PREIMAGE_BIGUNION, IMAGE_IMAGE, o_DEF, BIGUNION_OVER_INTER_L] \\
       MATCH_MP_TAC SIGMA_ALGEBRA_ENUM \\
       rw [sigma_algebra_Borel_lists, IN_FUNSET] \\
       POP_ASSUM MP_TAC >> rw [SUBSET_DEF] \\
       POP_ASSUM (MP_TAC o Q.SPEC ‘A (x :num)’) \\
       impl_tac >- (Q.EXISTS_TAC ‘x’ >> art []) \\
       simp [] ]
QED

(* cf. IN_MEASURABLE_BOREL_ADD' and IN_MEASURABLE_BOREL_2D_VECTOR, and
       IN_MEASURABLE_BOREL_LISTS.
 *)
Theorem IN_MEASURABLE_BOREL_SUM_LIST :
    !N. 0 < N ==> FOLDR $+ 0 IN measurable (Borel_lists N) Borel
Proof
    Induct_on ‘N’ >- rw []
 >> Cases_on ‘N’ >> rw []
 >- (fs [Borel_lists_1] \\
     rw [IN_MEASURABLE, IN_FUNSET, SPACE_BOREL, IMAGE_wrap_univ] \\
     Q.EXISTS_TAC ‘s’ >> art [] \\
     rw [Once EXTENSION, PREIMAGE_def, wrap_def] \\
     EQ_TAC >> rw [] >> rw [FOLDR] (* only 1 goal left *)\\
     Cases_on ‘x’ >> fs [])
 >> qabbrev_tac ‘N = SUC n’
 >> ‘0 < N’ by rw [Abbr ‘N’]
 >> Know ‘FOLDR $+ 0 = \s. if s = [] then 0
                           else HD s + FOLDR $+ 0 (TL s)’
 >- (rw [FUN_EQ_THM] \\
     Cases_on ‘s’ >> simp [])
 >> Rewr'
 >> Know ‘(\s. if s = [] then 0 else HD s + FOLDR $+ 0 (TL s)) IN
             Borel_measurable (Borel_lists (SUC N)) <=>
          (\s. HD s + FOLDR $+ 0 (TL s)) IN
             Borel_measurable (Borel_lists (SUC N))’
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_EQ_SYM \\
     rw [space_Borel_lists])
 >> Rewr'
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD'
 >> simp [sigma_algebra_Borel_lists, space_Borel_lists]
 >> qexistsl_tac [‘HD’, ‘FOLDR $+ 0 o TL’]
 >> simp [IN_MEASURABLE_BOREL_HD]
 >> MATCH_MP_TAC MEASURABLE_COMP
 >> Q.EXISTS_TAC ‘Borel_lists N’ >> simp []
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_TL >> art []
QED

Theorem IN_MEASURABLE_BOREL_SUM_LIST_LIST :
    !a f l. sigma_algebra a /\ 0 < LENGTH l /\
           (!i. MEM i l ==> f i IN measurable a Borel) ==>
           (\x. FOLDR $+ 0 (MAP (\i. f i x) l)) IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> ‘(\x. FOLDR $+ 0 (MAP (\i. f i x) l)) =
     (FOLDR $+ 0) o (\x. MAP (\i. f i x) l)’ by rw [o_DEF, FUN_EQ_THM]
 >> POP_ORW
 >> MATCH_MP_TAC MEASURABLE_COMP
 >> qabbrev_tac ‘n = LENGTH l’
 >> Q.EXISTS_TAC ‘Borel_lists n’
 >> rw [IN_MEASURABLE_BOREL_LISTS]
 >> irule IN_MEASURABLE_BOREL_SUM_LIST >> art []
QED

(* ------------------------------------------------------------------------- *)
(*  Probability space constructed by sigma_lists of (the same) prob space    *)
(* ------------------------------------------------------------------------- *)

Theorem existence_of_multidimensional_prob_space :
    !p N. prob_space p /\ 0 < N ==>
         ?pp. prob_space pp /\
              measurable_space pp = sigma_lists (measurable_space p) N /\
             !E. (?h. E = rectangle h N /\ !i. i < N ==> h i IN events p) ==>
                 E IN events pp /\
                 prob pp E = PI (\i. prob p (IMAGE (EL i) E)) (count N)
Proof
    rpt STRIP_TAC
 >> ‘sigma_algebra (p_space p,events p)’ by PROVE_TAC [EVENTS_SIGMA_ALGEBRA]
 >> qabbrev_tac ‘a = (p_space p,events p)’
 >> Q.PAT_X_ASSUM ‘0 < N’ MP_TAC
 >> Cases_on ‘N’ >> rw []
 >> Induct_on ‘n’
 >- (qabbrev_tac ‘a' = sigma_lists a 1’ \\
     qabbrev_tac ‘f = \s. prob p (IMAGE unwrap s)’ \\
     Q.EXISTS_TAC ‘(space a',subsets a',f)’ \\
     CONJ_TAC (* prob_space *)
     >- (simp [prob_space_def] \\
         reverse CONJ_TAC
         >- (rw [Abbr ‘f’, Abbr ‘a'’, sigma_lists_1, Abbr ‘a’] \\
             MATCH_MP_TAC PROB_UNIV >> art []) \\
         simp [measure_space_def, Abbr ‘f’, Abbr ‘a'’, sigma_lists_1, Abbr ‘a’] \\
         CONJ_TAC (* sigma_algebra *)
         >- (MATCH_MP_TAC IMAGE_SIGMA_ALGEBRA \\
             rw [BIJ_wrap]) \\
         CONJ_TAC (* positive *)
         >- (rw [positive_def, PROB_EMPTY] \\
             rename1 ‘e IN events p’ \\
             Suff ‘IMAGE unwrap (IMAGE wrap e) = e’ >- rw [PROB_POSITIVE] \\
             rw [IMAGE_unwrap_wrap]) \\
      (* countably_additive *)
         rw [countably_additive_def, IN_FUNSET] \\
         rename1 ‘s IN events p’ \\
         REWRITE_TAC [IMAGE_BIGUNION] \\
         simp [IMAGE_IMAGE, o_DEF] \\
         qabbrev_tac ‘g = \x. IMAGE unwrap (f x)’ \\
         Know ‘prob p (BIGUNION (IMAGE g univ(:num))) = suminf (prob p o g)’
         >- (MATCH_MP_TAC PROB_COUNTABLY_ADDITIVE >> art [] \\
             rw [IN_FUNSET, Abbr ‘g’]
             >- (Q.PAT_X_ASSUM ‘!x. ?y. f x = IAMGE wrap y /\ _’
                   (MP_TAC o Q.SPEC ‘x’) \\
                 rw [] >> simp [IMAGE_unwrap_wrap]) \\
             rw [DISJOINT_ALT] \\
             rename1 ‘unwrap y = unwrap x’ \\
             CCONTR_TAC >> fs [] \\
            ‘?a. f m = IMAGE wrap a /\ a IN events p’ by METIS_TAC [] \\
            ‘?b. f n = IMAGE wrap b /\ b IN events p’ by METIS_TAC [] \\
            ‘x NOTIN f n’ by METIS_TAC [DISJOINT_ALT] \\
             gvs []) >> Rewr' \\
         AP_TERM_TAC >> simp [o_DEF, Abbr ‘g’]) \\
     rw [count_def, prob_def, Abbr ‘f’, unwrap_def, events_def]
     >- (rw [Abbr ‘a'’, Abbr ‘a’, p_space_def, events_def]) \\
     simp [Abbr ‘a'’, sigma_lists_1, Abbr ‘a’, subsets_def] \\
     fs [GSYM events_def] \\
     Q.EXISTS_TAC ‘h 0’ >> art [] \\
     rw [Once EXTENSION, list_rectangle_def] \\
     EQ_TAC >> rw [wrap_def] >> rw [] \\
     Cases_on ‘x’ >> fs [])
 (* stage work *)
 >> POP_ASSUM (Q.X_CHOOSE_THEN ‘p1’ STRIP_ASSUME_TAC)
 >> qabbrev_tac ‘N = SUC n’
 >> qunabbrev_tac ‘a’
 (* applying existence_of_prod_measure_general *)
 >> ‘sigma_finite_measure_space p /\
     sigma_finite_measure_space p1’
       by PROVE_TAC [prob_space_def, PROB_SPACE_SIGMA_FINITE,
                     sigma_finite_measure_space_def]
 >> qabbrev_tac ‘X = p_space p’
 >> qabbrev_tac ‘A = events p’
 >> qabbrev_tac ‘u = prob p’
 >> qabbrev_tac ‘Y = p_space p1’
 >> qabbrev_tac ‘B = events p1’
 >> qabbrev_tac ‘v = prob p1’
 >> MP_TAC (Q.SPECL [‘CONS’, ‘HD’, ‘TL’, ‘X’, ‘Y’, ‘A’, ‘B’, ‘u’, ‘v’]
                    (INST_TYPE [beta |-> “:'a list”, gamma |-> “:'a list”]
                               existence_of_prod_measure_general))
 >> simp [pair_operation_CONS, PROB_SPACE_REDUCE,
          Abbr ‘X’, Abbr ‘Y’, Abbr ‘A’, Abbr ‘B’, Abbr ‘u’, Abbr ‘v’]
 >> qabbrev_tac ‘m0 = \x. prob p (IMAGE HD x) * prob p1 (IMAGE TL x)’
 >> DISCH_THEN (MP_TAC o Q.SPEC ‘m0’)
 >> Know ‘!s t.
            s IN events p /\ t IN events p1 ==>
            m0 (general_cross CONS s t) = prob p s * prob p1 t’
 >- (rw [general_cross_def, Abbr ‘m0’] \\
     Cases_on ‘s = {}’ >> rw [PROB_EMPTY] \\
     Cases_on ‘t = {}’ >> rw [PROB_EMPTY] \\
     Know ‘IMAGE HD {a::b | a IN s /\ b IN t} = s’
     >- (rw [Once EXTENSION] \\
         EQ_TAC >> rw [] >> rw [] \\
        ‘?y. y IN t’ by rw [MEMBER_NOT_EMPTY] \\
         Q.EXISTS_TAC ‘x::y’ >> simp []) >> Rewr' \\
     Know ‘IMAGE TL {a::b | a IN s /\ b IN t} = t’
     >- (rw [Once EXTENSION] \\
         EQ_TAC >> rw [] >> rw [] \\
        ‘?y. y IN s’ by rw [MEMBER_NOT_EMPTY] \\
         Q.EXISTS_TAC ‘y::x’ >> simp []) >> Rewr)
 >> simp []
 >> DISCH_TAC
 >> STRIP_TAC
 >> qabbrev_tac ‘Z = general_cross CONS (p_space p) (p_space p1)’
 >> qabbrev_tac
      ‘a = general_sigma CONS (p_space p,events p) (p_space p1,events p1)’
 >> qabbrev_tac ‘p2 = (Z,subsets a,m)’
 >> Q.EXISTS_TAC ‘p2’
 >> CONJ_TAC (* prob_space p2 *)
 >- (simp [prob_space_def] \\
     fs [sigma_finite_measure_space_def] \\
     simp [GSYM prob_def, GSYM p_space_def] \\
     simp [Abbr ‘p2’, prob_def, p_space_def] \\
     Know ‘m Z = m0 Z’
     >- (FIRST_X_ASSUM MATCH_MP_TAC \\
         simp [Abbr ‘Z’, IN_general_prod] \\
         qexistsl_tac [‘p_space p’, ‘p_space p1’] \\
         simp [EVENTS_SPACE]) >> Rewr' \\
     simp [Abbr ‘Z’] \\
     Know ‘m0 (general_cross CONS (p_space p) (p_space p1)) =
           prob p (p_space p) * prob p1 (p_space p1)’
     >- (FIRST_X_ASSUM MATCH_MP_TAC \\
         simp [EVENTS_SPACE]) >> Rewr' \\
     simp [PROB_UNIV])
 >> CONJ_TAC
 >- (simp [Abbr ‘p2’, Abbr ‘Z’] \\
    ‘0 < N’ by rw [Abbr ‘N’] \\
     Know ‘sigma_algebra (measurable_space p)’
     >- (MATCH_MP_TAC MEASURE_SPACE_SIGMA_ALGEBRA \\
         fs [prob_space_def]) >> DISCH_TAC \\
     simp [sigma_lists_decomposition] \\
     Q.PAT_X_ASSUM ‘_ = sigma_lists (measurable_space p) N’
       (REWRITE_TAC o wrap o SYM) \\
     Know ‘general_cross CONS (p_space p) (p_space p1) = space a’
     >- (simp [Abbr ‘a’, general_sigma_def, SPACE_SIGMA]) >> Rewr' \\
     simp [SPACE, cons_sigma_alt_gen] \\
     simp [Abbr ‘a’, p_space_def, events_def])
 (* stage work *)
 >> Q.X_GEN_TAC ‘E’ >> simp [list_rectangle_SUC]
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘E = _’ (REWRITE_TAC o wrap)
 >> qabbrev_tac ‘s2 = cons_cross (h 0) (rectangle (h o SUC) N)’
 (* applying EXTREAL_PROD_IMAGE_PROPERTY *)
 >> ‘0 IN count1 N’ by rw [Abbr ‘N’]
 >> ‘count1 N = 0 INSERT (count1 N DELETE 0)’ by ASM_SET_TAC [] >> POP_ORW
 >> POP_ASSUM K_TAC
 >> qabbrev_tac ‘J = count1 N DELETE 0’
 >> qmatch_abbrev_tac ‘s2 IN events p2 /\ prob p2 s2 = PI g (0 INSERT J)’
 >> Know ‘PI g (0 INSERT J) = g 0 * PI g (J DELETE 0)’
 >- (MATCH_MP_TAC EXTREAL_PROD_IMAGE_PROPERTY >> rw [Abbr ‘J’])
 >> Rewr'
 >> ‘J DELETE 0 = J’ by ASM_SET_TAC [] >> POP_ORW
 >> simp [Abbr ‘J’]
 >> Know ‘count1 N DELETE 0 = IMAGE SUC (count N)’
 >- (rw [Once EXTENSION] \\
     EQ_TAC >> rw [] \\
     Cases_on ‘x’ >> fs [])
 >> Rewr'
 (* EXTREAL_PROD_IMAGE_IMAGE *)
 >> Know ‘PI g (IMAGE SUC (count N)) = PI (g o SUC) (count N)’
 >- (MATCH_MP_TAC EXTREAL_PROD_IMAGE_IMAGE >> rw [INJ_DEF])
 >> Rewr'
 >> qabbrev_tac ‘s3 = IMAGE TL s2’
 >> Know ‘PI (g o SUC) (count N) = PI (\i. prob p (IMAGE (EL i) s3)) (count N)’
 >- (MATCH_MP_TAC EXTREAL_PROD_IMAGE_EQ \\
     Q.X_GEN_TAC ‘i’ >> rw [o_DEF, Abbr ‘g’] \\
     simp [Abbr ‘s3’, IMAGE_IMAGE, o_DEF] \\
     AP_TERM_TAC >> rw [Once EXTENSION] \\
     EQ_TAC >> rw [EL])
 >> Rewr'
 >> STRONG_CONJ_TAC
 >- (simp [Abbr ‘s2’, Abbr ‘p2’, events_def] \\
     simp [Abbr ‘a’, general_sigma_def] \\
     MATCH_MP_TAC IN_SIGMA \\
     rw [IN_general_prod, cons_cross_alt_gen] \\
     qexistsl_tac [‘h 0’, ‘rectangle (h o SUC) N’] >> simp [] \\
     FIRST_X_ASSUM (MATCH_MP_TAC o cj 1) \\
     Q.EXISTS_TAC ‘h o SUC’ >> rw [])
 >> DISCH_TAC
 >> Know ‘PI (\i. prob p (IMAGE (EL i) s3)) (count N) = prob p1 s3’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     FIRST_X_ASSUM (MATCH_MP_TAC o cj 2) \\
     simp [Abbr ‘s3’] \\
     Cases_on ‘h 0 = {}’
     >- (Q.EXISTS_TAC ‘\i. h 0’ >> simp [EVENTS_EMPTY] \\
         rw [Once EXTENSION, Abbr ‘s2’, cons_cross_def, IN_list_rectangle] \\
         Q.PAT_X_ASSUM ‘SUC n = LENGTH x’ (REWRITE_TAC o wrap o SYM) \\
         Q.EXISTS_TAC ‘0’ >> rw []) \\
     Q.EXISTS_TAC ‘h o SUC’ \\
     reverse CONJ_TAC >- simp [o_DEF] \\
     rw [Abbr ‘s2’, Once EXTENSION, cons_cross_def, list_rectangle_def] \\
     EQ_TAC >> rw [] >> rw [LENGTH_TL] \\
     fs [GSYM MEMBER_NOT_EMPTY] \\
     rename1 ‘y IN h 0’ \\
     Q.EXISTS_TAC ‘y::x’ >> simp [])
 >> Rewr'
 >> simp [Abbr ‘g’, Abbr ‘s3’]
 >> Suff ‘m0 s2 = m s2’ >- simp [Abbr ‘p2’, prob_def]
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> POP_ASSUM MP_TAC (* s2 IN events p2 *)
 >> rw [IN_general_prod, Abbr ‘s2’, Abbr ‘p2’, events_def]
 >> qexistsl_tac [‘h 0’, ‘rectangle (h o SUC) N’]
 >> simp [cons_cross_alt_gen, GSYM events_def]
 >> FIRST_X_ASSUM (MATCH_MP_TAC o cj 1)
 >> Q.EXISTS_TAC ‘h o SUC’ >> rw []
QED

(* Another version with both E and h as universal quantifier *)
Theorem existence_of_multidimensional_prob_space' :
    !p N. prob_space p /\ 0 < N ==>
         ?pp. prob_space pp /\
              measurable_space pp = sigma_lists (measurable_space p) N /\
             !E h. E = rectangle h N /\ (!i. i < N ==> h i IN events p) ==>
                   E IN events pp /\ prob pp E = PI (prob p o h) (count N)
Proof
    rpt STRIP_TAC
 >> drule_all_then STRIP_ASSUME_TAC existence_of_multidimensional_prob_space
 >> Q.EXISTS_TAC ‘pp’ >> art []
 >> rpt GEN_TAC
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!E. _ ==> E IN events pp /\ _’ (MP_TAC o Q.SPEC ‘E’)
 >> impl_tac
 >- (Q.EXISTS_TAC ‘h’ >> rw [])
 >> rw []
 >> Cases_on ‘!i. i < N ==> h i <> {}’
 >- (MATCH_MP_TAC EXTREAL_PROD_IMAGE_EQ \\
     Q.X_GEN_TAC ‘i’ >> rw [o_DEF] \\
     AP_TERM_TAC \\
     rw [Once EXTENSION, IN_list_rectangle] \\
     EQ_TAC >> rw [] >> rw [] \\
     Know ‘!j. j < N /\ j <> i ==> ?y. y IN h j’
     >- (rpt STRIP_TAC \\
         rw [MEMBER_NOT_EMPTY]) \\
     simp [EXT_SKOLEM_THM'] >> STRIP_TAC \\
     Q.EXISTS_TAC ‘GENLIST (\j. if j = i then x else f j) N’ \\
     simp [] \\
     Q.X_GEN_TAC ‘j’ >> rw [])
 >> fs []
 >> qabbrev_tac ‘s = count N DELETE i’
 >> ‘i IN count N’ by rw []
 >> ‘count N = i INSERT s’ by ASM_SET_TAC []
 >> POP_ORW
 >> qmatch_abbrev_tac ‘PI f (i INSERT s) = PI g (i INSERT s)’
 >> ‘s DELETE i = s’ by ASM_SET_TAC []
 >> ‘FINITE s’ by rw [Abbr ‘s’]
 >> simp [EXTREAL_PROD_IMAGE_PROPERTY]
 >> Suff ‘f i = 0 /\ g i = 0’ >- rw []
 >> simp [Abbr ‘f’, Abbr ‘g’, PROB_EMPTY]
 >> Suff ‘IMAGE (EL i) (rectangle h N) = h i’ >- rw [PROB_EMPTY]
 >> rw [Once EXTENSION, IN_list_rectangle]
 >> Q.EXISTS_TAC ‘i’ >> rw [NOT_IN_EMPTY]
QED

(* ------------------------------------------------------------------------- *)
(*  Independence of functions of independent r.v.'s                          *)
(*                                                                           *)
(*  By "functions", here we mean those who taking lists of numbers returning *)
(*  single numbers. Lengths of input lists are "dimensions" of functions.    *)
(* ------------------------------------------------------------------------- *)

(* Theorem 3.3.2 [2, p.54] (for only two group of r.v.'s)
   See also Problem 2.5.7 of [4, p.217].

   NOTE: This is a generalization of [indep_functions_of_four_vars] for two
   disjoint lists of (total) independent r.v.'s.
 *)
Theorem indep_functions_of_vars_lemma[local] :
    !p. prob_space p /\ ALL_DISTINCT (l1 ++ (l2 :'index list)) /\
       (!n. MEM n (l1 ++ l2) ==> random_variable (X n) p Borel) /\
        LENGTH l1 = n1 /\ LENGTH l2 = n2 /\ 0 < n1 /\ 0 < n2 /\
        indep_vars p X (\n. Borel) (set (l1 ++ l2)) ==>
        !A. A IN subsets (Borel_lists n1) ==>
            !B. B IN subsets (Borel_lists n2) ==>
                indep p (PREIMAGE (\x. MAP (\n. X n x) l1) A INTER p_space p)
                        (PREIMAGE (\x. MAP (\n. X n x) l2) B INTER p_space p)
Proof
    NTAC 2 STRIP_TAC
 >> qabbrev_tac
   ‘P = \A. A IN subsets (Borel_lists n1) /\
            !B. B IN subsets (Borel_lists n2) ==>
                indep p (PREIMAGE (\x. MAP (\n. X n x) l1) A INTER p_space p)
                        (PREIMAGE (\x. MAP (\n. X n x) l2) B INTER p_space p)’
 >> Suff ‘subsets (Borel_lists n1) SUBSET P’
 >- rw [SUBSET_DEF, IN_APP, Abbr ‘P’]
 >> simp [Borel_lists_alt_sigma]
 >> qmatch_abbrev_tac ‘subsets (sigma sp sts) SUBSET P’
 >> qabbrev_tac ‘b = (sp,P)’
 >> ‘P = subsets b’ by rw [Abbr ‘b’] >> POP_ORW
 >> ‘sp = space b’ by rw [Abbr ‘b’] >> POP_ORW
 >> MATCH_MP_TAC SIGMA_PROPERTY_DYNKIN
 >> CONJ_TAC (* subset_class (space b) sts *)
 >- (rw [subset_class_def, Abbr ‘b’, Abbr ‘sp’, space_Borel_lists, SPACE_BOREL] \\
     POP_ASSUM MP_TAC >> rw [SUBSET_DEF, Abbr ‘sts’] \\
     POP_ASSUM MP_TAC >> rw [IN_list_rectangle])
 >> CONJ_TAC (* !s t. s IN sts /\ t IN sts ==> s INTER t IN sts *)
 >- (rw [Abbr ‘sts’] \\
     rw [Once EXTENSION, list_rectangle_def] \\
     qabbrev_tac ‘n1 = LENGTH l1’ \\
     Q.EXISTS_TAC ‘\i. h i INTER h' i’ \\
     CONJ_TAC >- (rw [] >> EQ_TAC >> rw []) \\
     rw [] >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> rw [SIGMA_ALGEBRA_BOREL])
 >> fs [Abbr ‘b’]
 >> reverse CONJ_TAC
 >- (rw [dynkin_system_def] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       rw [Abbr ‘sp’, Abbr ‘P’, subset_class_def, SUBSET_DEF, space_Borel_lists] \\
       qabbrev_tac ‘n1 = LENGTH l1’ \\
       MP_TAC (Q.SPEC ‘n1’ sigma_algebra_Borel_lists) \\
       rw [sigma_algebra_def, algebra_def, space_Borel_lists, subset_class_def] \\
       Q.PAT_X_ASSUM ‘!x. x IN subsets (Borel_lists n1) ==>
                          x SUBSET {v | LENGTH v = n1}’ (MP_TAC o Q.SPEC ‘x’) \\
       rw [SUBSET_DEF],
       (* goal 2 (of 4): sp IN P *)
       simp [Abbr ‘sp’, Abbr ‘P’, GSYM space_Borel_lists] \\
       qabbrev_tac ‘n1 = LENGTH l1’ \\
       CONJ_TAC
       >- (MATCH_MP_TAC SIGMA_ALGEBRA_SPACE \\
           REWRITE_TAC [sigma_algebra_Borel_lists]) \\
       rw [space_Borel_lists] \\
       qabbrev_tac ‘sp = {(v :extreal list) | LENGTH v = n1}’ \\
       Know ‘PREIMAGE (\x. MAP (\n. X n x) l1) sp INTER p_space p = p_space p’
       >- (qmatch_abbrev_tac ‘s INTER p_space p = p_space p’ \\
           Suff ‘p_space p SUBSET s’ >- SET_TAC [] \\
           rw [Abbr ‘s’, IN_PREIMAGE, SUBSET_DEF, Abbr ‘sp’]) >> Rewr' \\
       MATCH_MP_TAC INDEP_SPACE >> art [] \\
       qabbrev_tac ‘n2 = LENGTH l2’ \\
    (* applying IN_MEASURABLE_BOREL_LISTS *)
       qabbrev_tac ‘a = (p_space p,events p)’ \\
      ‘sigma_algebra a’ by METIS_TAC [EVENTS_SIGMA_ALGEBRA] \\
       MP_TAC (Q.SPECL [‘a’, ‘X’, ‘l2’, ‘n2’] IN_MEASURABLE_BOREL_LISTS) \\
       simp [] \\
       impl_tac >- (rpt STRIP_TAC \\
                    fs [random_variable_def] \\
                    FIRST_X_ASSUM MATCH_MP_TAC \\
                    Q.PAT_X_ASSUM ‘set l2 SUBSET J’ MP_TAC \\
                    rw [SUBSET_DEF]) \\
       rw [IN_MEASURABLE, SPACE_BOREL, IN_FUNSET, Abbr ‘a’],
       (* goal 3 (of 4): sp DIFF s IN P *)
       POP_ASSUM MP_TAC \\
       rw [Abbr ‘sp’, Abbr ‘P’, GSYM space_Borel_lists]
       >- (MATCH_MP_TAC SIGMA_ALGEBRA_COMPL \\
           simp [sigma_algebra_Borel_lists]) \\
       qabbrev_tac ‘n1 = LENGTH l1’ \\
       qabbrev_tac ‘n2 = LENGTH l2’ \\
       simp [space_Borel_lists, PREIMAGE_DIFF] \\
       Q.PAT_X_ASSUM ‘!B. B IN subsets (Borel_lists n2) ==> _’
                     (MP_TAC o Q.SPEC ‘B’) >> rw [] \\
       qmatch_abbrev_tac ‘indep p ((Z DIFF A) INTER sp) b’ \\
      ‘(Z DIFF A) INTER sp = (Z INTER sp) DIFF (A INTER sp)’ by SET_TAC [] \\
       POP_ORW \\
       Know ‘Z INTER sp = sp’
       >- (Suff ‘sp SUBSET Z’ >- SET_TAC [] \\
           rw [Abbr ‘sp’, Abbr ‘Z’, IN_PREIMAGE, SUBSET_DEF]) >> Rewr' \\
       qunabbrev_tac ‘sp’ \\
       MATCH_MP_TAC INDEP_COMPL' >> art [],
       (* goal 4 (of 4) *)
       Q.PAT_X_ASSUM ‘f IN (UNIV -> P)’ MP_TAC \\
       rw [Abbr ‘P’, IN_FUNSET]
       >- (MATCH_MP_TAC SIGMA_ALGEBRA_ENUM \\
           rw [sigma_algebra_Borel_lists, IN_FUNSET]) \\
       simp [PREIMAGE_BIGUNION, IMAGE_IMAGE, o_DEF, BIGUNION_OVER_INTER_L] \\
       MATCH_MP_TAC INDEP_COUNTABLE_DUNION' \\
       simp [disjoint_family_def] \\
       CONJ_TAC
       >- (qabbrev_tac ‘n2 = LENGTH l2’ \\
        (* applying IN_MEASURABLE_BOREL_LISTS *)
           qabbrev_tac ‘a = (p_space p,events p)’ \\
          ‘sigma_algebra a’ by METIS_TAC [EVENTS_SIGMA_ALGEBRA] \\
           MP_TAC (Q.SPECL [‘a’, ‘X’, ‘l2’, ‘n2’] IN_MEASURABLE_BOREL_LISTS) \\
           simp [] \\
           impl_tac >- (rpt STRIP_TAC \\
                        fs [random_variable_def] \\
                        FIRST_X_ASSUM MATCH_MP_TAC \\
                        Q.PAT_X_ASSUM ‘set l2 SUBSET J’ MP_TAC \\
                        rw [SUBSET_DEF]) \\
           rw [IN_MEASURABLE, SPACE_BOREL, IN_FUNSET, Abbr ‘a’]) \\
       qx_genl_tac [‘i’, ‘j’] >> DISCH_TAC \\
       MATCH_MP_TAC DISJOINT_RESTRICT_L \\
       MATCH_MP_TAC PREIMAGE_DISJOINT \\
       FIRST_X_ASSUM MATCH_MP_TAC >> art [] ])
 (* stage work *)
 >> simp [SUBSET_DEF, Abbr ‘sts’, Abbr ‘P’]
 >> NTAC 2 STRIP_TAC
 >> Q.PAT_X_ASSUM ‘x = rectangle h n1’ (REWRITE_TAC o wrap)
 >> CONJ_TAC
 >- (simp [Borel_lists_alt_sigma] \\
     MATCH_MP_TAC IN_SIGMA >> rw [IN_list_rectangle] \\
     Q.EXISTS_TAC ‘h’ >> art [])
 (* stage work *)
 >> qabbrev_tac ‘r = rectangle h n1’
 >> qabbrev_tac
     ‘P = \B. B IN subsets (Borel_lists n2) /\
              indep p (PREIMAGE (\x. MAP (\n. X n x) l1) r INTER p_space p)
                      (PREIMAGE (\x. MAP (\n. X n x) l2) B INTER p_space p)’
 >> Suff ‘subsets (Borel_lists n2) SUBSET P’
 >- rw [SUBSET_DEF, IN_APP, Abbr ‘P’]
 >> simp [Borel_lists_alt_sigma]
 >> qunabbrev_tac ‘sp’
 >> qmatch_abbrev_tac ‘subsets (sigma sp sts) SUBSET P’
 >> qabbrev_tac ‘b = (sp,P)’
 >> ‘P = subsets b’ by rw [Abbr ‘b’] >> POP_ORW
 >> ‘sp = space b’ by rw [Abbr ‘b’] >> POP_ORW
 >> MATCH_MP_TAC SIGMA_PROPERTY_DYNKIN
 >> CONJ_TAC (* subset_class (space b) sts *)
 >- (rw [subset_class_def, Abbr ‘b’, Abbr ‘sp’, space_Borel_lists, SPACE_BOREL] \\
     POP_ASSUM MP_TAC >> rw [SUBSET_DEF, Abbr ‘sts’] \\
     POP_ASSUM MP_TAC >> rw [IN_list_rectangle])
 >> CONJ_TAC (* !s t. s IN sts /\ t IN sts ==> s INTER t IN sts *)
 >- (rw [Abbr ‘sts’] \\
     rw [Once EXTENSION, list_rectangle_def] \\
     qabbrev_tac ‘n2 = LENGTH l2’ \\
     rename1 ‘!i. i < n2 ==> h2 i IN subsets Borel’ \\
     Q.EXISTS_TAC ‘\i. h' i INTER h2 i’ \\
     CONJ_TAC >- (rw [] >> EQ_TAC >> rw []) \\
     rw [] >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> rw [SIGMA_ALGEBRA_BOREL])
 >> fs [Abbr ‘b’]
 >> reverse CONJ_TAC
 >- (rw [dynkin_system_def] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       rw [Abbr ‘sp’, Abbr ‘P’, subset_class_def, SUBSET_DEF, space_Borel_lists] \\
       qabbrev_tac ‘n2 = LENGTH l2’ \\
       MP_TAC (Q.SPEC ‘n2’ sigma_algebra_Borel_lists) \\
       rw [sigma_algebra_def, algebra_def, space_Borel_lists, subset_class_def] \\
       Q.PAT_X_ASSUM ‘!x. x IN subsets (Borel_lists n2) ==>
                          x SUBSET {v | LENGTH v = n2}’ (MP_TAC o Q.SPEC ‘x’) \\
       rw [SUBSET_DEF],
       (* goal 2 (of 4): sp IN P *)
       simp [Abbr ‘sp’, Abbr ‘P’, GSYM space_Borel_lists] \\
       qabbrev_tac ‘n2 = LENGTH l2’ \\
       CONJ_TAC
       >- (MATCH_MP_TAC SIGMA_ALGEBRA_SPACE \\
           REWRITE_TAC [sigma_algebra_Borel_lists]) \\
       rw [space_Borel_lists] \\
       qabbrev_tac ‘sp = {(v :extreal list) | LENGTH v = n2}’ \\
       Know ‘PREIMAGE (\x. MAP (\n. X n x) l2) sp INTER p_space p = p_space p’
       >- (qmatch_abbrev_tac ‘s INTER p_space p = p_space p’ \\
           Suff ‘p_space p SUBSET s’ >- SET_TAC [] \\
           rw [Abbr ‘s’, IN_PREIMAGE, SUBSET_DEF, Abbr ‘sp’]) >> Rewr' \\
       MATCH_MP_TAC INDEP_SPACE' >> art [] \\
       qabbrev_tac ‘n1 = LENGTH l1’ \\
    (* applying PREIMAGE_list_rectangle *)
       qmatch_abbrev_tac ‘PREIMAGE g r INTER p_space p IN events p’ \\
       qunabbrev_tac ‘r’ \\
       MP_TAC (Q.SPECL [‘g’, ‘h’, ‘n1’]
                       (INST_TYPE [beta |-> “:extreal”] PREIMAGE_list_rectangle)) \\
       simp [Abbr ‘g’, BIGINTER_OVER_INTER_L] \\
       DISCH_THEN K_TAC (* already used *) \\
       MATCH_MP_TAC EVENTS_BIGINTER_FN \\
       rw [SUBSET_DEF] \\
       rw [EL_MAP] \\
      ‘(\x. X (EL n l1) x) = X (EL n l1)’ by rw [FUN_EQ_THM] >> POP_ORW \\
       fs [random_variable_def, IN_MEASURABLE, IN_FUNSET, SPACE_BOREL] \\
       FIRST_X_ASSUM irule >> simp [EL_MEM],
       (* goal 3 (of 4): sp DIFF s IN P *)
       POP_ASSUM MP_TAC \\
       rw [Abbr ‘sp’, Abbr ‘P’, GSYM space_Borel_lists]
       >- (MATCH_MP_TAC SIGMA_ALGEBRA_COMPL \\
           simp [sigma_algebra_Borel_lists]) \\
       qabbrev_tac ‘n1 = LENGTH l1’ \\
       qabbrev_tac ‘n2 = LENGTH l2’ \\
       simp [space_Borel_lists, PREIMAGE_DIFF] \\
       qmatch_abbrev_tac ‘indep p b ((Z DIFF A) INTER sp)’ \\
      ‘(Z DIFF A) INTER sp = (Z INTER sp) DIFF (A INTER sp)’ by SET_TAC [] \\
       POP_ORW \\
       Know ‘Z INTER sp = sp’
       >- (Suff ‘sp SUBSET Z’ >- SET_TAC [] \\
           rw [Abbr ‘sp’, Abbr ‘Z’, IN_PREIMAGE, SUBSET_DEF]) >> Rewr' \\
       qunabbrev_tac ‘sp’ \\
       MATCH_MP_TAC INDEP_COMPL >> art [],
       (* goal 4 (of 4) *)
       Q.PAT_X_ASSUM ‘f IN (UNIV -> P)’ MP_TAC \\
       rw [Abbr ‘P’, IN_FUNSET]
       >- (MATCH_MP_TAC SIGMA_ALGEBRA_ENUM \\
           rw [sigma_algebra_Borel_lists, IN_FUNSET]) \\
       simp [PREIMAGE_BIGUNION, IMAGE_IMAGE, o_DEF, BIGUNION_OVER_INTER_L] \\
       MATCH_MP_TAC INDEP_COUNTABLE_DUNION \\
       simp [disjoint_family_def] \\
       CONJ_TAC
       >- (qabbrev_tac ‘n1 = LENGTH l1’ \\
           qmatch_abbrev_tac ‘PREIMAGE g r INTER p_space p IN events p’ \\
           qunabbrev_tac ‘r’ \\
           MP_TAC (Q.SPECL [‘g’, ‘h’, ‘n1’]
                     (INST_TYPE [beta |-> “:extreal”] PREIMAGE_list_rectangle)) \\
           simp [Abbr ‘g’, BIGINTER_OVER_INTER_L] \\
           DISCH_THEN K_TAC (* already used *) \\
           MATCH_MP_TAC EVENTS_BIGINTER_FN \\
           rw [SUBSET_DEF] \\
           rw [EL_MAP] \\
          ‘(\x. X (EL n l1) x) = X (EL n l1)’ by rw [FUN_EQ_THM] >> POP_ORW \\
           fs [random_variable_def, IN_MEASURABLE, IN_FUNSET, SPACE_BOREL] \\
           FIRST_X_ASSUM irule >> simp [EL_MEM]) \\
       qx_genl_tac [‘i’, ‘j’] >> DISCH_TAC \\
       MATCH_MP_TAC DISJOINT_RESTRICT_L \\
       MATCH_MP_TAC PREIMAGE_DISJOINT \\
       FIRST_X_ASSUM MATCH_MP_TAC >> art [] ])
 (* stage work *)
 >> simp [SUBSET_DEF, Abbr ‘sts’, Abbr ‘P’]
 >> NTAC 2 STRIP_TAC
 >> Q.PAT_X_ASSUM ‘x = rectangle h' n2’ (REWRITE_TAC o wrap)
 >> CONJ_TAC
 >- (simp [Borel_lists_alt_sigma] \\
     MATCH_MP_TAC IN_SIGMA >> rw [IN_list_rectangle] \\
     Q.EXISTS_TAC ‘h'’ >> art [])
 >> qunabbrev_tac ‘r’
 >> qmatch_abbrev_tac
     ‘indep p (PREIMAGE f (rectangle h  n1) INTER p_space p)
              (PREIMAGE g (rectangle h' n2) INTER p_space p)’
 >> MP_TAC (Q.SPECL [‘f’, ‘h’, ‘n1’]
                    (INST_TYPE [beta |-> “:extreal”] PREIMAGE_list_rectangle))
 >> simp [Abbr ‘f’, BIGINTER_OVER_INTER_L]
 >> DISCH_THEN K_TAC
 >> MP_TAC (Q.SPECL [‘g’, ‘h'’, ‘n2’]
                    (INST_TYPE [beta |-> “:extreal”] PREIMAGE_list_rectangle))
 >> simp [Abbr ‘g’, BIGINTER_OVER_INTER_L]
 >> DISCH_THEN K_TAC
 >> rw [indep_def]
 >- (MATCH_MP_TAC EVENTS_BIGINTER_FN \\
     qabbrev_tac ‘n1 = LENGTH l1’ \\
     rw [SUBSET_DEF] >> rw [EL_MAP] \\
    ‘(\x. X (EL n l1) x) = X (EL n l1)’ by rw [FUN_EQ_THM] >> POP_ORW \\
     fs [random_variable_def, IN_MEASURABLE, IN_FUNSET, SPACE_BOREL] \\
     FIRST_X_ASSUM irule >> simp [EL_MEM])
 >- (MATCH_MP_TAC EVENTS_BIGINTER_FN \\
     qabbrev_tac ‘n2 = LENGTH l2’ \\
     rw [SUBSET_DEF] >> rw [EL_MAP] \\
    ‘(\x. X (EL n l2) x) = X (EL n l2)’ by rw [FUN_EQ_THM] >> POP_ORW \\
     fs [random_variable_def, IN_MEASURABLE, IN_FUNSET, SPACE_BOREL] \\
     FIRST_X_ASSUM irule >> simp [EL_MEM])
 (* stage work *)
 >> qabbrev_tac ‘f = \n x. EL n (MAP (\n. (X :'index -> 'a -> extreal) n x) l1)’
 >> qabbrev_tac ‘g = \n x. EL n (MAP (\n. (X :'index -> 'a -> extreal) n x) l2)’
 >> simp []
 >> ‘!n. (\x. f n x) = f n’ by rw [FUN_EQ_THM] >> POP_ORW
 >> ‘!n. (\x. g n x) = g n’ by rw [FUN_EQ_THM] >> POP_ORW
 >> qabbrev_tac ‘n1 = LENGTH l1’
 >> qabbrev_tac ‘n2 = LENGTH l2’
 >> Know ‘IMAGE (\i. EL i l1) (count n1) = set l1’
 >- (rw [Once EXTENSION, MEM_EL] >> METIS_TAC [])
 >> DISCH_TAC
 >> Know ‘IMAGE (\i. EL i l2) (count n2) = set l2’
 >- (rw [Once EXTENSION, MEM_EL] >> METIS_TAC [])
 >> DISCH_TAC
 >> qabbrev_tac ‘g1 = \i. EL i l1’
 >> qabbrev_tac ‘g2 = \i. EL i l2’
 (* applying IMAGE_IMAGE *)
 >> qabbrev_tac ‘f1 = \e. {x | x IN p_space p /\ X e x IN h  (THE (INDEX_OF e l1))}’
 >> qabbrev_tac ‘f2 = \e. {x | x IN p_space p /\ X e x IN h' (THE (INDEX_OF e l2))}’
 (* applying ALL_DISTINCT_INDEX_OF_EL *)
 >> FULL_SIMP_TAC std_ss [ALL_DISTINCT_APPEND']
 >> Know ‘!i. i < n1 ==> INDEX_OF (EL i l1) l1 = SOME i’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC ALL_DISTINCT_INDEX_OF_EL >> simp [])
 >> DISCH_TAC
 >> Know ‘!i. i < n2 ==> INDEX_OF (EL i l2) l2 = SOME i’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC ALL_DISTINCT_INDEX_OF_EL >> simp [])
 >> DISCH_TAC
 >> Know ‘IMAGE (\n. PREIMAGE (f n) (h n) INTER p_space p) (count n1) =
          IMAGE (f1 o g1) (count n1)’
 >- (rw [o_DEF, Abbr ‘g1’, Abbr ‘f1’, PREIMAGE_def, Abbr ‘f’, Once EXTENSION] \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC ‘n’ >> art [] \\
       rw [Once EXTENSION] \\
       EQ_TAC >> rw [EL_MAP],
       (* goal 2 (of 2) *)
       rename1 ‘i < n1’ \\
       Q.EXISTS_TAC ‘i’ >> art [] \\
       rw [Once EXTENSION] \\
       EQ_TAC >> rw [EL_MAP] ])
 >> Rewr'
 >> Know ‘IMAGE (\n. PREIMAGE (g n) (h' n) INTER p_space p) (count n2) =
          IMAGE (f2 o g2) (count n2)’
 >- (rw [o_DEF, Abbr ‘g2’, Abbr ‘f2’, PREIMAGE_def, Abbr ‘g’, Once EXTENSION] \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC ‘n’ >> art [] \\
       rw [Once EXTENSION] \\
       EQ_TAC >> rw [EL_MAP],
       (* goal 2 (of 2) *)
       rename1 ‘i < n2’ \\
       Q.EXISTS_TAC ‘i’ >> art [] \\
       rw [Once EXTENSION] \\
       EQ_TAC >> rw [EL_MAP] ])
 >> Rewr'
 >> simp [GSYM IMAGE_IMAGE]
 (* stage work *)
 >> qabbrev_tac ‘E1 = \e. h  (THE (INDEX_OF e l1))’
 >> qabbrev_tac ‘E2 = \e. h' (THE (INDEX_OF e l2))’
 >> Know ‘IMAGE f1 (set l1) =
          IMAGE (\e. PREIMAGE (X e) (E1 e) INTER p_space p) (set l1)’
 >- (rw [Once EXTENSION, Abbr ‘f1’, PREIMAGE_def] \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC ‘e’ >> art [] \\
       rw [Once EXTENSION] >> rw [Once CONJ_SYM],
       (* goal 2 (of 2) *)
       Q.EXISTS_TAC ‘e’ >> art [] \\
       rw [Once EXTENSION] >> rw [Once CONJ_SYM] ])
 >> Rewr'
 >> Know ‘IMAGE f2 (set l2) =
          IMAGE (\e. PREIMAGE (X e) (E2 e) INTER p_space p) (set l2)’
 >- (rw [Once EXTENSION, Abbr ‘f2’, PREIMAGE_def] \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC ‘e’ >> art [] \\
       rw [Once EXTENSION] >> rw [Once CONJ_SYM],
       (* goal 2 (of 2) *)
       Q.EXISTS_TAC ‘e’ >> art [] \\
       rw [Once EXTENSION] >> rw [Once CONJ_SYM] ])
 >> Rewr'
 (* applying indep_vars_def *)
 >> fs [indep_vars_def]
 >> Know ‘prob p
            (BIGINTER (IMAGE (\n. PREIMAGE (X n) (E1 n) INTER p_space p) (set l1))) =
          PI (prob p o (\n. PREIMAGE (X n) (E1 n) INTER p_space p)) (set l1)’
 >- (FIRST_X_ASSUM MATCH_MP_TAC \\
     simp [GSYM LENGTH_NON_NIL, IN_DFUNSET] \\
     rw [MEM_EL, Abbr ‘E1’, Abbr ‘g1’] >> simp [])
 >> Rewr'
 >> Know ‘prob p
            (BIGINTER (IMAGE (\n. PREIMAGE (X n) (E2 n) INTER p_space p) (set l2))) =
          PI (prob p o (\n. PREIMAGE (X n) (E2 n) INTER p_space p)) (set l2)’
 >- (FIRST_X_ASSUM MATCH_MP_TAC \\
     simp [GSYM LENGTH_NON_NIL, IN_DFUNSET] \\
     rw [MEM_EL, Abbr ‘E2’, Abbr ‘g2’] >> simp [])
 >> Rewr'
 >> Know ‘!e. MEM e l1 ==> ~MEM e l2’
 >- (Q.PAT_X_ASSUM ‘DISJOINT (set l1) (set l2)’ MP_TAC \\
     rw [DISJOINT_ALT])
 >> DISCH_TAC
 >> Know ‘!e. MEM e l2 ==> ~MEM e l1’
 >- (Q.PAT_X_ASSUM ‘DISJOINT (set l1) (set l2)’ MP_TAC \\
     rw [DISJOINT_ALT'])
 >> DISCH_TAC
 (* stage work *)
 >> qabbrev_tac ‘E = \e. if MEM e l1 then E1 e else E2 e’
 >> Know ‘BIGINTER
            (IMAGE (\e. PREIMAGE (X e) (E1 e) INTER p_space p) (set l1)) INTER
          BIGINTER
            (IMAGE (\e. PREIMAGE (X e) (E2 e) INTER p_space p) (set l2)) =
          BIGINTER
            (IMAGE (\e. PREIMAGE (X e) (E e) INTER p_space p) (set l1 UNION set l2))’
 >- (rw [Once EXTENSION, IN_BIGINTER_IMAGE] \\
     EQ_TAC >> rw [Abbr ‘E’] >| (* 8 subgoals *)
     [ (* goal 1 (of 8) *)
       simp [],
       (* goal 2 (of 8) *)
       Q.PAT_X_ASSUM ‘!e. MEM e l1 ==> X e x IN E1 e /\ x IN p_space p’
         (MP_TAC o Q.SPEC ‘e’) >> rw [],
       (* goal 3 (of 8) *)
       simp [],
       (* goal 4 (of 8) *)
       Q.PAT_X_ASSUM ‘!e. MEM e l2 ==> X e x IN E2 e /\ x IN p_space p’
         (MP_TAC o Q.SPEC ‘e’) >> rw [],
       (* goal 5 (of 8) *)
       Q.PAT_X_ASSUM ‘!e. MEM e l1 \/ MEM e l2 ==> _’ (MP_TAC o Q.SPEC ‘e’) \\
       simp [],
       (* goal 6 (of 8) *)
       Q.PAT_X_ASSUM ‘!e. MEM e l1 \/ MEM e l2 ==> _’ (MP_TAC o Q.SPEC ‘e’) \\
       simp [],
       (* goal 7 (of 8) *)
       Q.PAT_X_ASSUM ‘!e. MEM e l1 \/ MEM e l2 ==> _’ (MP_TAC o Q.SPEC ‘e’) \\
       simp [],
       (* goal 8 (of 8) *)
       Q.PAT_X_ASSUM ‘!e. MEM e l1 \/ MEM e l2 ==> _’ (MP_TAC o Q.SPEC ‘e’) \\
       simp [] ])
 >> Rewr'
 >> Know ‘prob p (BIGINTER (IMAGE (\n. PREIMAGE (X n) (E n) INTER p_space p)
                                  (set l1 UNION set l2))) =
          PI (prob p o (\n. PREIMAGE (X n) (E n) INTER p_space p))
             (set l1 UNION set l2)’
 >- (FIRST_X_ASSUM MATCH_MP_TAC \\
     simp [GSYM LENGTH_NON_NIL, IN_DFUNSET] \\
     rw [MEM_EL, Abbr ‘E’, Abbr ‘E1’, Abbr ‘E2’, Abbr ‘g1’, Abbr ‘g2’] \\
     simp [])
 >> Rewr'
 >> Know ‘PI (prob p o (\n. PREIMAGE (X n) (E n) INTER p_space p))
             (set l1 UNION set l2) =
          PI (prob p o (\n. PREIMAGE (X n) (E n) INTER p_space p)) (set l1) *
          PI (prob p o (\n. PREIMAGE (X n) (E n) INTER p_space p)) (set l2)’
 >- (MATCH_MP_TAC EXTREAL_PROD_IMAGE_DISJOINT_UNION >> simp [])
 >> Rewr'
 >> Know ‘PI (prob p o (\n. PREIMAGE (X n) (E n) INTER p_space p)) (set l1) =
          PI (prob p o (\n. PREIMAGE (X n) (E1 n) INTER p_space p)) (set l1)’
 >- (MATCH_MP_TAC EXTREAL_PROD_IMAGE_EQ \\
     rw [Abbr ‘E’])
 >> Rewr'
 >> Know ‘PI (prob p o (\n. PREIMAGE (X n) (E n) INTER p_space p)) (set l2) =
          PI (prob p o (\n. PREIMAGE (X n) (E2 n) INTER p_space p)) (set l2)’
 >- (MATCH_MP_TAC EXTREAL_PROD_IMAGE_EQ \\
     rw [Abbr ‘E’])
 >> Rewr
QED

Theorem indep_functions_of_vars :
    !p X (l1 :'index list) l2 n1 n2 f g.
        prob_space p /\ ALL_DISTINCT (l1 ++ l2) /\
       (!n. MEM n (l1 ++ l2) ==> random_variable (X n) p Borel) /\
        LENGTH l1 = n1 /\ LENGTH l2 = n2 /\ 0 < n1 /\ 0 < n2 /\
        f IN measurable (Borel_lists n1) Borel /\
        g IN measurable (Borel_lists n2) Borel /\
        indep_vars p X (\n. Borel) (set (l1 ++ l2)) ==>
        indep_vars p (\x. f (MAP (\n. X n x) l1))
                     (\x. g (MAP (\n. X n x) l2)) Borel Borel
Proof
    rw [indep_rv_def, IN_MEASURABLE, IN_FUNSET, space_Borel_lists, SPACE_BOREL]
 >> qabbrev_tac ‘n1 = LENGTH l1’
 >> qabbrev_tac ‘n2 = LENGTH l2’
 >> ‘(\x. f (MAP (\n. X n x) l1)) = f o (\x. MAP (\n. X n x) l1)’ by rw [o_DEF]
 >> POP_ORW
 >> ‘(\x. g (MAP (\n. X n x) l2)) = g o (\x. MAP (\n. X n x) l2)’ by rw [o_DEF]
 >> POP_ORW
 >> simp [PREIMAGE_o, GSYM PREIMAGE_ALT]
 >> qabbrev_tac ‘L1 = (\x. MAP (\n. X n x) l1)’
 >> qabbrev_tac ‘L2 = (\x. MAP (\n. X n x) l2)’
 >> qabbrev_tac ‘A = PREIMAGE f a’
 >> qabbrev_tac ‘B = PREIMAGE g b’
 >> Know ‘PREIMAGE L1 A INTER p_space p =
          PREIMAGE L1 (A INTER {v | LENGTH v = n1}) INTER p_space p’
 >- (rw [Once EXTENSION, IN_PREIMAGE] \\
     simp [Abbr ‘L1’])
 >> Rewr'
 >> Know ‘PREIMAGE L2 B INTER p_space p =
          PREIMAGE L2 (B INTER {v | LENGTH v = n2}) INTER p_space p’
 >- (rw [Once EXTENSION, IN_PREIMAGE] \\
     simp [Abbr ‘L2’])
 >> Rewr'
 >> qabbrev_tac ‘A' = A INTER {v | LENGTH v = n1}’
 >> qabbrev_tac ‘B' = B INTER {v | LENGTH v = n2}’
 >> qunabbrevl_tac [‘A’, ‘B’]
 >> ‘A' IN subsets (Borel_lists n1) /\ B' IN subsets (Borel_lists n2)’
      by METIS_TAC []
 >> qunabbrevl_tac [‘L1’, ‘L2’]
 >> irule indep_functions_of_vars_lemma
 >> simp [MEM_APPEND]
 >> rpt STRIP_TAC
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

Theorem indep_sum_list_of_vars :
    !p X (l1 :'index list) l2 n1 n2 f g.
        prob_space p /\ ALL_DISTINCT (l1 ++ l2) /\
       (!n. MEM n (l1 ++ l2) ==> random_variable (X n) p Borel) /\
        LENGTH l1 = n1 /\ LENGTH l2 = n2 /\ 0 < n1 /\ 0 < n2 /\
        indep_vars p X (\n. Borel) (set (l1 ++ l2)) ==>
        indep_vars p (\x. FOLDR $+ 0 (MAP (\n. X n x) l1))
                     (\x. FOLDR $+ 0 (MAP (\n. X n x) l2)) Borel Borel
Proof
    rpt STRIP_TAC
 >> HO_MATCH_MP_TAC indep_functions_of_vars
 >> qexistsl_tac [‘n1’, ‘n2’]
 >> simp [IN_MEASURABLE_BOREL_SUM_LIST]
QED

(* ------------------------------------------------------------------------- *)
(*  Infinite-dimensional Borel space [4, p.178]                              *)
(* ------------------------------------------------------------------------- *)

(* A cylinder is a set of infinite-dimensional values (represented by :num ->
   'a functions) where only the first N dimensions are specified (by h).

   NOTE: The "bottom" of this cylinder is always a rectangle, thus is not the
   general cylinder sets.
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
 >> rpt (Q.PAT_X_ASSUM ‘!f. P’ MP_TAC)
 (* applying wlog_tac *)
 >> wlog_tac ‘s DIFF t <> {}’ [‘s’, ‘t’]
 >- (‘t DIFF s <> {}’ by ASM_SET_TAC [] \\
     Q.PAT_X_ASSUM ‘!s t N. P’ (MP_TAC o Q.SPECL [‘t’, ‘s’, ‘N’]) \\
     rw [] >> gs [] \\
     Q.EXISTS_TAC ‘x’ >> rw [])
 >> rpt STRIP_TAC
 (* stage work *)
 >> fs [GSYM MEMBER_NOT_EMPTY]
 >> fs [cylinder2rect_def]
 >> Q.PAT_X_ASSUM ‘!x. P <=> Q’ (MP_TAC o Q.SPEC ‘GENLIST x N’)
 >> Know ‘?f'. GENLIST x N = GENLIST f' N /\ f' IN s’
 >- (Q.EXISTS_TAC ‘x’ >> art [])
 >> simp []
 >> DISCH_THEN K_TAC
 >> Q.X_GEN_TAC ‘g’ >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!f. (?f'. GENLIST f N = GENLIST f' N /\ f' IN t) ==> f IN t’
       (MP_TAC o Q.SPEC ‘x’)
 >> impl_tac >- (Q.EXISTS_TAC ‘g’ >> art [])
 >> rw []
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

(* NOTE: The extra condition ‘is_cylinder c N’ is beyond the textbook [4, p.179].
   This definition is local, shouldn't be used outside of the present theory.
 *)
Definition Borel_lists' :
    Borel_lists' N =
      ({v :extreal list | LENGTH v = N},
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
 >> qabbrev_tac ‘sts = {B | B SUBSET sp /\
                            {f | GENLIST f N IN B} IN subsets Borel_inf}’
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

val _ = html_theory "stochastic_process";

(* References:

  [1] Kolmogorov, A.N.: Foundations of the Theory of Probability (Grundbegriffe der
      Wahrscheinlichkeitsrechnung). Chelsea Publishing Company, New York. (1950).
  [2] Chung, K.L.: A Course in Probability Theory, Third Edition.
      Academic Press (2001).
  [3] Rosenthal, J.S.: A First Look at Rigorous Probability Theory (Second Editoin).
      World Scientific Publishing Company (2006).
  [4] Shiryaev, A.N.: Probability-1. Springer-Verlag New York (2016).
  [5] Shiryaev, A.N.: Probability-2. Springer-Verlag New York (2019).
  [6] Billingsley, P.: Probability and Measure (3rd Edition).
      Wiley-Interscience (1995).
  [7] Cinlar, E.: Probability and Stochastics. Springer (2011).
  [8] J.L. Doob (1953), Stochastic processes (2nd ed.). John Wiley & Sons, New York.
  [9] Schilling, R.L.: Measures, Integrals and Martingales (Second Edition).
      Cambridge University Press (2017).
  [10] Lindgren, G.: Stationary Stochastic Processes. CRC Press (2012).
  [11] Wentzell, A.D.: Theorie zufalliger Prozesse. Springer-Verlag, Basel (2014).
 *)
