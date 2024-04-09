(* ========================================================================= *)
(* Create "lebesgueTheory" setting up the theory of Lebesgue Integration     *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib

open metisLib numTheory arithmeticTheory pred_setTheory listTheory combinTheory
     pairTheory jrhUtils hurdUtils simpLib whileTheory;

open realTheory realLib realSimps seqTheory real_sigmaTheory transcTheory
     limTheory iterateTheory;

open util_probTheory sigma_algebraTheory real_measureTheory real_borelTheory;

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "lebesgue"                                      *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "real_lebesgue";

val _ = intLib.deprecate_int ();
val _ = ratLib.deprecate_rat ();

Overload indicator_fn[local] = “indicator”
Theorem indicator_fn_def[local] = indicator

(* ************************************************************************* *)
(* Basic Definitions                                                         *)
(* ************************************************************************* *)

(* This defines a simple function ‘f’ in measurable space m by (s,a,x):

   s is a (finite) num index set
   a(i) (each i IN s) are mutually disjoint measurable sets in m,
   x(i) are reals indicating the "height" of each a(i).

   Then `f(t) = SIGMA (\i. x i * indicator_fn (a i) t) s` is a simple function.

   BIGUNION and DISJOINT indicate that this is a standard representation.
 *)
Definition pos_simple_fn_def :
    pos_simple_fn m f (s :num set) (a :num -> 'a set) (x :num -> real) =
       ((!t. 0 <= f t) /\
        (!t. t IN m_space m ==> (f t = SIGMA (\i. (x i) * (indicator_fn (a i) t)) s)) /\
        (!i. i IN s ==> a i IN measurable_sets m) /\
        (!i. 0 <= x i) /\
        FINITE s /\
        (!i j. i IN s /\ j IN s /\ i <> j ==> DISJOINT (a i) (a j)) /\
        (BIGUNION (IMAGE a s) = m_space m))
End

(* The integral of a positive simple function *)
Definition pos_simple_fn_integral_def :
    pos_simple_fn_integral (m :'a m_space)
                           (s :num set) (a :num -> 'a set) (x :num -> real) =
        SIGMA (\i. (x i) * (measure m (a i))) s
End

(* ‘psfs m f’ is the set of all positive simple functions equivalent to f *)
Definition psfs_def :
    psfs m f = {(s,a,x) | pos_simple_fn m f s a x}
End

val psfis_def = Define
   `psfis m f = IMAGE (\(s,a,x). pos_simple_fn_integral m s a x) (psfs m f)`;

val nonneg_def = Define
   `nonneg f = !x. 0 <= f x`;

val fn_plus_def = Define
   `fn_plus f = (\x. if 0 <= f x then f x else 0)`;

val fn_minus_def = Define
   `fn_minus f = (\x. if 0 <= f x then 0 else ~ f x)`;

val pos_fn_integral_def = Define
   `pos_fn_integral m f = sup {r:real | ?g. r IN psfis m g /\ !x. g x <= f x}`;

(* c.f. "pos_fn_integral_def" in (new) lebesgueScript.sml *)
val nnfis_def = Define
   `nnfis m f = {y | ?u x. mono_convergent u f (m_space m) /\
                           (!n. x n IN psfis m (u n)) /\ x --> y}`;

val upclose_def = Define
   `upclose f g = (\t. max (f t) (g t))`;

val mon_upclose_help_def = Define
  `(mon_upclose_help 0 u m = u m 0) /\
   (mon_upclose_help (SUC n) u m = upclose (u m (SUC n)) (mon_upclose_help n u m))`;

val mon_upclose_def = Define
   `mon_upclose u m = mon_upclose_help m u m`;

val integrable_def = Define
   `integrable m f <=> measure_space m /\
                      (?x. x IN nnfis m (fn_plus f)) /\
                      (?y. y IN nnfis m (fn_minus f))`;

val integral_def = Define
   `integral m f = (@i. i IN nnfis m (fn_plus f)) - (@j. j IN nnfis m (fn_minus f))`;

val finite_space_integral_def = Define
   `finite_space_integral m f =
        SIGMA (\r. r * measure m (PREIMAGE f {r} INTER m_space m)) (IMAGE f (m_space m))`;

val countable_space_integral_def = Define
   `countable_space_integral m f =
        let e = enumerate (IMAGE f (m_space m))
        in suminf ((\r. r * measure m (PREIMAGE f {r} INTER m_space m)) o e)`;

val prod_measure_def = Define
   `prod_measure m0 m1 =
        (\a. integral m0 (\s0. (measure m1) (PREIMAGE (\s1. (s0,s1)) a)))`;

(* cf. martingaleTheory.prod_measure_def for the extreal-based version *)
val prod_measure_space_def = Define
   `prod_measure_space m0 m1 =
        ((m_space m0) CROSS (m_space m1),
         subsets (sigma ((m_space m0) CROSS (m_space m1))
                        (prod_sets (measurable_sets m0) (measurable_sets m1))),
         prod_measure m0 m1)`;

val prod_sets3_def = Define
   `prod_sets3 (a :'a set set) (b :'b set set) (c :'c set set) =
       {s CROSS (t CROSS u) | s IN a /\ t IN b /\ u IN c}`;

val prod_measure3_def = Define
   `prod_measure3 m0 m1 m2 = prod_measure m0 (prod_measure_space m1 m2)`;

val prod_measure_space3_def = Define
   `prod_measure_space3 m0 m1 m2 =
      (m_space m0 CROSS (m_space m1 CROSS m_space m2),
       subsets (sigma (m_space m0 CROSS (m_space m1 CROSS m_space m2))
                      (prod_sets3 (measurable_sets m0) (measurable_sets m1) (measurable_sets m2))),
       prod_measure3 m0 m1 m2)`;

val RN_deriv_def = Define
   `RN_deriv m v =
        @f. measure_space m /\ measure_space (m_space m, measurable_sets m, v) /\
            f IN borel_measurable (m_space m, measurable_sets m) /\
            (!a. a IN measurable_sets m ==>
                        (integral m (\x. f x * indicator_fn a x) = v a))`;

(* ************************************************************************* *)
(* Proofs                                                                    *)
(* ************************************************************************* *)

val indicator_fn_split = store_thm
  ("indicator_fn_split",
  ``!(r:num->bool) s (b:num->('a->bool)).
        FINITE r /\
        (BIGUNION (IMAGE b r) = s) /\
             (!i j. i IN r /\ j IN r /\ (~(i=j)) ==> DISJOINT (b i) (b j)) ==>
             !a. a SUBSET s ==>
                 ((indicator_fn a) =
                  (\x. SIGMA (\i. indicator_fn (a INTER (b i)) x) r))``,
   Suff `!r. FINITE r ==>
                (\r. !s (b:num->('a->bool)).
        FINITE r /\
        (BIGUNION (IMAGE b r) = s) /\
             (!i j. i IN r /\ j IN r /\ (~(i=j)) ==> DISJOINT (b i) (b j)) ==>
             !a. a SUBSET s ==>
                 ((indicator_fn a) =
                  (\x. SIGMA (\i. indicator_fn (a INTER (b i)) x) r))) r`
   >- METIS_TAC []
   >> MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC real_ss [REAL_SUM_IMAGE_THM, IMAGE_EMPTY, BIGUNION_EMPTY, SUBSET_EMPTY,
                      indicator_fn_def, NOT_IN_EMPTY, FINITE_INSERT, IMAGE_INSERT,
                      DELETE_NON_ELEMENT, IN_INSERT, BIGUNION_INSERT]
   >> Q.PAT_X_ASSUM `!b. P ==> !a. Q ==> (x = y)`
        (MP_TAC o Q.ISPEC `(b :num -> 'a -> bool)`)
   >> RW_TAC std_ss [SUBSET_DEF]
   >> POP_ASSUM (MP_TAC o Q.ISPEC `a DIFF ((b :num -> 'a -> bool) e)`)
   >> Know `(!x. x IN a DIFF b e ==> x IN BIGUNION (IMAGE b s))`
   >- METIS_TAC [SUBSET_DEF, IN_UNION, IN_DIFF]
   >> RW_TAC std_ss [FUN_EQ_THM]
   >> Know `SIGMA (\i. (if x IN a INTER b i then 1 else 0)) s =
            SIGMA (\i. (if x IN (a DIFF b e) INTER b i then 1 else 0)) s`
   >- (ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(s :num -> bool)`) REAL_SUM_IMAGE_IN_IF]
       >> MATCH_MP_TAC (METIS_PROVE [] ``!f x y z. (x = y) ==> (f x z = f y z)``)
       >> RW_TAC std_ss [FUN_EQ_THM, IN_INTER, IN_DIFF]
       >> FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT, DISJOINT_DEF,
                                IN_INTER, NOT_IN_EMPTY,
                                EXTENSION, GSPECIFICATION]
       >> RW_TAC real_ss [] >> METIS_TAC [])
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [GSYM thm])
   >> RW_TAC real_ss [IN_DIFF, IN_INTER] >> METIS_TAC []);

val measure_split = store_thm
  ("measure_split",
  ``!(r:num->bool) (b:num->('a->bool)) m.
        measure_space m /\
        FINITE r /\
        (BIGUNION (IMAGE b r) = m_space m) /\
        (!i j. i IN r /\ j IN r /\ (~(i=j)) ==> DISJOINT (b i) (b j)) /\
        (!i. i IN r ==> b i IN measurable_sets m) ==>
             !a. a IN measurable_sets m ==>
                 ((measure m) a =
                  SIGMA (\i. (measure m) (a INTER (b i))) r)``,
   Suff `!r. FINITE r ==>
                (\r. !(b:num->('a->bool)) m.
        measure_space m /\
        (BIGUNION (IMAGE b r) = m_space m) /\
        (!i j. i IN r /\ j IN r /\ (~(i=j)) ==> DISJOINT (b i) (b j)) /\
        (!i. i IN r ==> b i IN measurable_sets m) ==>
             !a. a IN measurable_sets m ==>
                 ((measure m) a =
                  SIGMA (\i. (measure m) (a INTER (b i))) r)) r` >- METIS_TAC []
   >> MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC std_ss [REAL_SUM_IMAGE_THM, IMAGE_EMPTY, BIGUNION_EMPTY,
                     DELETE_NON_ELEMENT,
                     IN_INSERT]
   >- (`!a m. measure_space m /\
              a IN measurable_sets m ==> a SUBSET m_space m`
        by RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,
                           subset_class_def, subsets_def, space_def]
        >> METIS_TAC [SUBSET_EMPTY, MEASURE_EMPTY])
   >> `!a m. measure_space m /\
              a IN measurable_sets m ==> a SUBSET m_space m`
        by RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,
                           subset_class_def, subsets_def, space_def]
   >> POP_ASSUM (ASSUME_TAC o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
                 Q.SPECL [`a`,`m`])
   >> Cases_on `s = {}`
   >- (FULL_SIMP_TAC std_ss [REAL_SUM_IMAGE_THM, IMAGE_DEF, IN_SING, BIGUNION,
                             GSPECIFICATION, GSPEC_ID, SUBSET_DEF]
       >> Know `a INTER m_space m = a`
       >- (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER] >> METIS_TAC [])
       >> RW_TAC real_ss [])
   >> `?x s'. (s = x INSERT s') /\ ~(x IN s')` by METIS_TAC [SET_CASES]
   >> FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT, IN_INSERT]
   >> Q.PAT_X_ASSUM `!b' m'. P ==> !a'. Q ==> (f = g)`
        (MP_TAC o Q.ISPECL [`(\i:num. if i = x then b x UNION b e else b i)`,
        `(m :('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real))`])
   >> `IMAGE (\i. (if i = x then b x UNION b e else b i)) s' = IMAGE b s'`
   by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_IMAGE]
       >> EQ_TAC
       >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `i` >> METIS_TAC [])
       >> RW_TAC std_ss [] >> Q.EXISTS_TAC `x''` >> METIS_TAC [])
   >> FULL_SIMP_TAC std_ss [IMAGE_INSERT, BIGUNION_INSERT, UNION_ASSOC]
   >> POP_ASSUM (K ALL_TAC)
   >> `(b x UNION b e UNION BIGUNION (IMAGE b s') = m_space m)`
   by METIS_TAC [UNION_COMM]
   >> ASM_REWRITE_TAC [] >> POP_ASSUM (K ALL_TAC)
   >> `(!i j.
    ((i = x) \/ i IN s') /\ ((j = x) \/ j IN s') /\ i <> j ==>
    DISJOINT (if i = x then b x UNION b e else b i)
      (if j = x then b x UNION b e else b j))`
   by (FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, GSPECIFICATION, IN_INSERT,
                            IN_INTER, NOT_IN_EMPTY]
       >> METIS_TAC [IN_UNION])
   >> ASM_REWRITE_TAC [] >> POP_ASSUM (K ALL_TAC)
   >> `(!i.
    (i = x) \/ i IN s' ==>
    (if i = x then b x UNION b e else b i) IN measurable_sets m)`
        by METIS_TAC [ALGEBRA_UNION, sigma_algebra_def, measure_space_def, subsets_def]
   >> ASM_REWRITE_TAC [] >> POP_ASSUM (K ALL_TAC)
   >> STRIP_TAC
   >> POP_ASSUM ((fn thm => ONCE_REWRITE_TAC [thm]) o UNDISCH o Q.SPEC `a`)
   >> FULL_SIMP_TAC real_ss [FINITE_INSERT, REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT,
                             REAL_ADD_ASSOC]
   >> Suff `(measure m (a INTER (b x UNION b e)) =
             measure m (a INTER b e) + measure m (a INTER b x)) /\
            (SIGMA (\i. measure m (a INTER
                                   (if i = x then b x UNION b e else b i))) s' =
             SIGMA (\i. measure m (a INTER b i)) s')`
   >- RW_TAC std_ss []
   >> CONJ_TAC
   >- (`a INTER (b x UNION b e) = (a INTER b e) UNION (a INTER b x)`
        by (FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, GSPECIFICATION,
                                     NOT_IN_EMPTY, IN_INTER, IN_UNION]
            >> METIS_TAC [])
       >> POP_ORW
       >> (MATCH_MP_TAC o REWRITE_RULE [additive_def] o UNDISCH o Q.SPEC `m`)
                MEASURE_SPACE_ADDITIVE
       >> CONJ_TAC
       >- METIS_TAC [ALGEBRA_INTER, sigma_algebra_def, measure_space_def, subsets_def]
       >> CONJ_TAC
       >- METIS_TAC [ALGEBRA_INTER, sigma_algebra_def, measure_space_def, subsets_def]
       >> FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER]
       >> METIS_TAC [])
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(s' :num -> bool)`) REAL_SUM_IMAGE_IN_IF]
   >> MATCH_MP_TAC (METIS_PROVE [] ``!f x y z. (x = y) ==> (f x z = f y z)``)
   >> RW_TAC std_ss [FUN_EQ_THM]
   >> RW_TAC std_ss []
   >> FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]);

val pos_simple_fn_integral_present = store_thm
  ("pos_simple_fn_integral_present",
  ``!m f (s:num->bool) a (x:num->real)
        g (s':num->bool) b (y:num->real).
        measure_space m /\
        pos_simple_fn m f s a x /\ pos_simple_fn m g s' b y ==>
        (?(z:num->real) (z':num->real) c (k:num->bool).
                (!t. t IN m_space m ==> (f t = SIGMA (\i. (z i) * (indicator_fn (c i) t)) k)) /\
                (!t. t IN m_space m ==> (g t = SIGMA (\i. (z' i) * (indicator_fn (c i) t)) k)) /\
                (pos_simple_fn_integral m s a x = pos_simple_fn_integral m k c z) /\
                (pos_simple_fn_integral m s' b y = pos_simple_fn_integral m k c z') /\
                FINITE k /\
                (!i j. i IN k /\ j IN k /\ (~(i=j)) ==> DISJOINT (c i) (c j)) /\
                (!i. i IN k ==> c i IN measurable_sets m) /\
                (BIGUNION (IMAGE c k) = m_space m) /\
                (!i. 0 <= z i) /\ (!i. 0 <= z' i))``,
   RW_TAC std_ss []
   >> `?p n. BIJ p (count n) (s CROSS s')`
        by FULL_SIMP_TAC std_ss [GSYM FINITE_BIJ_COUNT_EQ, pos_simple_fn_def, FINITE_CROSS]
   >> `?p'. BIJ p' (s CROSS s') (count n) /\
            (!x. x IN (count n) ==> ((p' o p) x = x)) /\
            (!x. x IN (s CROSS s') ==> ((p o p') x = x))`
        by (MATCH_MP_TAC BIJ_INV >> RW_TAC std_ss [])
   >> Q.EXISTS_TAC `x o FST o p`
   >> Q.EXISTS_TAC `y o SND o p`
   >> Q.EXISTS_TAC `(\(i,j). a i INTER b j) o p`
   >> Q.EXISTS_TAC `IMAGE p' (s CROSS s')`
   >> Q.ABBREV_TAC `G = IMAGE (\i j. p' (i,j)) s'`
   >> Q.ABBREV_TAC `H = IMAGE (\j i. p' (i,j)) s`
   >> CONJ_TAC
   >- (RW_TAC std_ss [FUN_EQ_THM] >> FULL_SIMP_TAC std_ss [pos_simple_fn_def]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(s :num -> bool)`) REAL_SUM_IMAGE_IN_IF]
       >> `(\x'. (if x' IN s then (\i. x i * indicator_fn (a i) t) x' else 0)) =
           (\x'. (if x' IN s then (\i. x i *
                SIGMA (\j. indicator_fn (a i INTER b j) t) s') x' else 0))`
        by (RW_TAC std_ss [FUN_EQ_THM]
            >> RW_TAC std_ss []
            >> FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
            >> (MP_TAC o Q.ISPEC `(a :num -> 'a -> bool) (x' :num)` o
                UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
                Q.ISPECL
                [`(s' :num -> bool)`,
                 `m_space (m:('a -> bool) #
                  (('a -> bool) -> bool) # (('a -> bool) -> real))`,
                 `(b :num -> 'a -> bool)`]) indicator_fn_split
            >> Q.PAT_X_ASSUM `!i. i IN s ==> (a:num->'a->bool) i IN measurable_sets m`
                (ASSUME_TAC o UNDISCH o Q.SPEC `x'`)
            >> `!a m. measure_space m /\
              a IN measurable_sets m ==> a SUBSET m_space m`
                by RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,
                                  subset_class_def, subsets_def, space_def]
            >> POP_ASSUM (ASSUME_TAC o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
                          Q.ISPECL [`(a :num -> 'a -> bool) (x' :num)`,
                                    `(m : ('a -> bool) #
                                     (('a -> bool) -> bool) # (('a -> bool) -> real))`])
            >> ASM_SIMP_TAC std_ss [])
       >> POP_ORW
       >> `!(x':num) (i:num). x i * SIGMA (\j. indicator_fn (a i INTER b j) t) s' =
                              SIGMA (\j. x i * indicator_fn (a i INTER b j) t) s'`
        by METIS_TAC [REAL_SUM_IMAGE_CMUL]
       >> POP_ORW
       >> `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
       >> `INJ p' (s CROSS s')
           (IMAGE p' (s CROSS s'))`
        by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `p'` o UNDISCH o
           Q.ISPEC `((s:num->bool) CROSS (s':num->bool))` o
                INST_TYPE [``:'b``|->``:num``]) REAL_SUM_IMAGE_IMAGE]
       >> RW_TAC std_ss [o_DEF]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(s :num -> bool)CROSS(s' :num -> bool)`)
                                REAL_SUM_IMAGE_IN_IF]
       >> `(\x'. (if x' IN s CROSS s' then
                (\x'. x (FST (p (p' x'))) *
                        indicator_fn ((\(i,j). a i INTER b j) (p (p' x'))) t) x'
                 else 0)) =
           (\x'. (if x' IN s CROSS s' then
                (\x'. x (FST x') *
                        indicator_fn ((\(i,j). a i INTER b j) x') t) x'
                 else 0))` by METIS_TAC []
       >> POP_ORW
       >> RW_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF]
       >> `!x'. (\j. x x' * indicator_fn (a x' INTER b j) t) =
                (\x' j. x x' * indicator_fn (a x' INTER b j) t) x'`
        by METIS_TAC []
       >> POP_ORW
       >> (MP_TAC o Q.ISPECL [`s:num->bool`,`s':num->bool`]) REAL_SUM_IMAGE_REAL_SUM_IMAGE
       >> RW_TAC std_ss []
       >> Suff `(\x'. x (FST x') * indicator_fn (a (FST x') INTER b (SND x')) t) =
                (\x'. x (FST x') * indicator_fn ((\(i,j). a i INTER b j) x') t)`
       >- RW_TAC std_ss []
       >> RW_TAC std_ss [FUN_EQ_THM]
       >> (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
       >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND])
   >> CONJ_TAC
   >- (RW_TAC std_ss [FUN_EQ_THM] >> FULL_SIMP_TAC std_ss [pos_simple_fn_def]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(s' :num -> bool)`) REAL_SUM_IMAGE_IN_IF]
       >> `(\x. (if x IN s' then (\i. y i * indicator_fn (b i) t) x else 0)) =
           (\x. (if x IN s' then (\i. y i *
                SIGMA (\j. indicator_fn (a j INTER b i) t) s) x else 0))`
        by (RW_TAC std_ss [FUN_EQ_THM]
            >> RW_TAC std_ss []
            >> FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
            >> (MP_TAC o REWRITE_RULE [Once INTER_COMM] o
                Q.ISPEC `(b :num -> 'a -> bool) (x' :num)` o
                UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
                Q.ISPECL
                [`(s :num -> bool)`,
                 `m_space (m:('a -> bool) #
                  (('a -> bool) -> bool) # (('a -> bool) -> real))`,
                 `(a :num -> 'a -> bool)`]) indicator_fn_split
            >> Q.PAT_X_ASSUM `!i. i IN s' ==> (b:num->'a->bool) i IN measurable_sets m`
                (ASSUME_TAC o UNDISCH o Q.SPEC `x'`)
            >> `!a m. measure_space m /\
              a IN measurable_sets m ==> a SUBSET m_space m`
                by RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,
                                  subset_class_def, subsets_def, space_def]
            >> POP_ASSUM (ASSUME_TAC o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
                          Q.ISPECL [`(b :num -> 'a -> bool) (x' :num)`,
                                    `(m : ('a -> bool) #
                                     (('a -> bool) -> bool) # (('a -> bool) -> real))`])
            >> ASM_SIMP_TAC std_ss [])
       >> POP_ORW
       >> `!(x:num) (i:num). y i * SIGMA (\j. indicator_fn (a j INTER b i) t) s =
                              SIGMA (\j. y i * indicator_fn (a j INTER b i) t) s`
        by METIS_TAC [REAL_SUM_IMAGE_CMUL]
       >> POP_ORW
       >> `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
       >> `INJ p' (s CROSS s')
           (IMAGE p' (s CROSS s'))`
        by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `p'` o UNDISCH o
           Q.ISPEC `((s:num->bool) CROSS (s':num->bool))` o
                INST_TYPE [``:'b``|->``:num``]) REAL_SUM_IMAGE_IMAGE]
       >> RW_TAC std_ss [o_DEF]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(s :num -> bool)CROSS(s' :num -> bool)`)
                                REAL_SUM_IMAGE_IN_IF]
       >> `(\x. (if x IN s CROSS s' then
                (\x. y (SND (p (p' x))) *
                indicator_fn ((\(i,j). a i INTER b j) (p (p' x))) t) x else 0)) =
           (\x. (if x IN s CROSS s' then
                (\x. y (SND x) *
                indicator_fn ((\(i,j). a i INTER b j) x) t) x else 0))` by METIS_TAC []
       >> POP_ORW
       >> RW_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF]
       >> `!x. (\j. y x * indicator_fn (a j INTER b x) t) =
                (\x j. y x * indicator_fn (a j INTER b x) t) x`
        by METIS_TAC []
       >> POP_ORW
       >> (MP_TAC o Q.ISPECL [`s':num->bool`,`s:num->bool`]) REAL_SUM_IMAGE_REAL_SUM_IMAGE
       >> RW_TAC std_ss []
       >> `(s' CROSS s) = IMAGE (\x. (SND x, FST x)) (s CROSS s')`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_CROSS, IN_IMAGE]
            >> (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
            >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND]
            >> EQ_TAC
            >- (STRIP_TAC >> Q.EXISTS_TAC `(r,q)` >> RW_TAC std_ss [FST,SND])
            >> RW_TAC std_ss [] >> RW_TAC std_ss [])
       >> POP_ORW
       >> `INJ (\x. (SND x,FST x)) (s CROSS s')
                (IMAGE (\x. (SND x,FST x)) (s CROSS s'))`
        by (RW_TAC std_ss [INJ_DEF, IN_CROSS, IN_IMAGE]
            >- METIS_TAC []
            >> (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
            >> (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
            >> RW_TAC std_ss []
            >> FULL_SIMP_TAC std_ss [FST,SND])
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `(\x. (SND x, FST x))` o UNDISCH o
           Q.ISPEC `((s:num->bool) CROSS (s':num->bool))` o
                INST_TYPE [``:'b``|->``:num#num``]) REAL_SUM_IMAGE_IMAGE]
       >> RW_TAC std_ss [o_DEF]
       >> Suff `(\x. y (SND x) * indicator_fn (a (FST x) INTER b (SND x)) t) =
                (\x. y (SND x) * indicator_fn ((\(i,j). a i INTER b j) x) t)`
       >- RW_TAC std_ss []
       >> RW_TAC std_ss [FUN_EQ_THM]
       >> (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
       >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND])
   >> CONJ_TAC
   >- (RW_TAC std_ss [pos_simple_fn_integral_def] >> FULL_SIMP_TAC std_ss [pos_simple_fn_def]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(s :num -> bool)`) REAL_SUM_IMAGE_IN_IF]
       >> `(\x'. (if x' IN s then (\i. x i * measure m (a i)) x' else 0)) =
           (\x'. (if x' IN s then (\i. x i *
                SIGMA (\j. measure m (a i INTER b j)) s') x' else 0))`
        by (RW_TAC std_ss [FUN_EQ_THM]
            >> RW_TAC std_ss []
            >> FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
            >> (MP_TAC o Q.SPEC `a (x' :num)` o
                UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
                Q.SPECL
                [`s'`, `b`, `m`]) measure_split
           >> RW_TAC std_ss [])
       >> POP_ORW
       >> `!(x':num) (i:num). x i * SIGMA (\j. measure m (a i INTER b j)) s' =
                              SIGMA (\j. x i * measure m (a i INTER b j)) s'`
        by METIS_TAC [REAL_SUM_IMAGE_CMUL]
       >> POP_ORW
       >> `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
       >> `INJ p' (s CROSS s')
           (IMAGE p' (s CROSS s'))`
        by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `p'` o UNDISCH o
           Q.ISPEC `((s:num->bool) CROSS (s':num->bool))` o
                INST_TYPE [``:'b``|->``:num``]) REAL_SUM_IMAGE_IMAGE]
       >> RW_TAC std_ss [o_DEF]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(s :num -> bool)CROSS(s' :num -> bool)`)
                                REAL_SUM_IMAGE_IN_IF]
       >> `(\x'. (if x' IN s CROSS s' then
                (\x'. x (FST (p (p' x'))) *
                        measure m ((\(i,j). a i INTER b j) (p (p' x')))) x'
                 else 0)) =
           (\x'. (if x' IN s CROSS s' then
                (\x'. x (FST x') *
                        measure m ((\(i,j). a i INTER b j) x')) x'
                 else 0))` by METIS_TAC []
       >> POP_ORW
       >> RW_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF]
       >> `!x'. (\j. x x' * measure m (a x' INTER b j)) =
                (\x' j. x x' * measure m (a x' INTER b j)) x'`
        by METIS_TAC []
       >> POP_ORW
       >> (MP_TAC o Q.ISPECL [`s:num->bool`,`s':num->bool`]) REAL_SUM_IMAGE_REAL_SUM_IMAGE
       >> RW_TAC std_ss []
       >> Suff `(\x'. x (FST x') * measure m (a (FST x') INTER b (SND x'))) =
                (\x'. x (FST x') * measure m ((\(i,j). a i INTER b j) x'))`
       >- RW_TAC std_ss []
       >> RW_TAC std_ss [FUN_EQ_THM]
       >> (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
       >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND])
   >> CONJ_TAC
   >- (RW_TAC std_ss [pos_simple_fn_integral_def] >> FULL_SIMP_TAC std_ss [pos_simple_fn_def]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(s' :num -> bool)`) REAL_SUM_IMAGE_IN_IF]
       >> `(\x. (if x IN s' then (\i. y i * measure m (b i)) x else 0)) =
           (\x. (if x IN s' then (\i. y i *
                SIGMA (\j. measure m (a j INTER b i)) s) x else 0))`
        by (RW_TAC std_ss [FUN_EQ_THM]
            >> RW_TAC std_ss []
            >> FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
            >> (MP_TAC o Q.SPEC `b (x' :num)` o
                UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
                Q.SPECL
                [`s`, `a`, `m`]) measure_split
           >> RW_TAC std_ss [INTER_COMM])
       >> POP_ORW
       >> `!(x:num) (i:num). y i * SIGMA (\j. measure m (a j INTER b i)) s =
                              SIGMA (\j. y i * measure m (a j INTER b i)) s`
        by METIS_TAC [REAL_SUM_IMAGE_CMUL]
       >> POP_ORW
       >> `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
       >> `INJ p' (s CROSS s')
           (IMAGE p' (s CROSS s'))`
        by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `p'` o UNDISCH o
           Q.ISPEC `((s:num->bool) CROSS (s':num->bool))` o
                INST_TYPE [``:'b``|->``:num``]) REAL_SUM_IMAGE_IMAGE]
       >> RW_TAC std_ss [o_DEF]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(s :num -> bool)CROSS(s' :num -> bool)`)
                                REAL_SUM_IMAGE_IN_IF]
       >> `(\x. (if x IN s CROSS s' then
                (\x. y (SND (p (p' x))) *
                measure m ((\(i,j). a i INTER b j) (p (p' x)))) x else 0)) =
           (\x. (if x IN s CROSS s' then
                (\x. y (SND x) *
                measure m ((\(i,j). a i INTER b j) x)) x else 0))` by METIS_TAC []
       >> POP_ORW
       >> RW_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF]
       >> `!x. (\j. y x * measure m (a j INTER b x)) =
                (\x j. y x * measure m (a j INTER b x)) x`
        by METIS_TAC []
       >> POP_ORW
       >> (MP_TAC o Q.ISPECL [`s':num->bool`,`s:num->bool`]) REAL_SUM_IMAGE_REAL_SUM_IMAGE
       >> RW_TAC std_ss []
       >> `(s' CROSS s) = IMAGE (\x. (SND x, FST x)) (s CROSS s')`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_CROSS, IN_IMAGE]
            >> (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
            >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND]
            >> EQ_TAC
            >- (STRIP_TAC >> Q.EXISTS_TAC `(r,q)` >> RW_TAC std_ss [FST,SND])
            >> RW_TAC std_ss [] >> RW_TAC std_ss [])
       >> POP_ORW
       >> `INJ (\x. (SND x,FST x)) (s CROSS s')
                (IMAGE (\x. (SND x,FST x)) (s CROSS s'))`
        by (RW_TAC std_ss [INJ_DEF, IN_CROSS, IN_IMAGE]
            >- METIS_TAC []
            >> (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
            >> (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
            >> RW_TAC std_ss []
            >> FULL_SIMP_TAC std_ss [FST,SND])
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `(\x. (SND x, FST x))` o UNDISCH o
           Q.ISPEC `((s:num->bool) CROSS (s':num->bool))` o
                INST_TYPE [``:'b``|->``:num#num``]) REAL_SUM_IMAGE_IMAGE]
       >> RW_TAC std_ss [o_DEF]
       >> Suff `(\x. y (SND x) * measure m (a (FST x) INTER b (SND x))) =
                (\x. y (SND x) * measure m ((\(i,j). a i INTER b j) x))`
       >- RW_TAC std_ss []
       >> RW_TAC std_ss [FUN_EQ_THM]
       >> (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
       >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND])
   >> CONJ_TAC
   >- FULL_SIMP_TAC std_ss [IMAGE_FINITE, FINITE_CROSS, pos_simple_fn_def]
   >> CONJ_TAC
   >- (RW_TAC std_ss [DISJOINT_DEF, IN_IMAGE]
       >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [NOT_IN_EMPTY, IN_INTER]
       >> FULL_SIMP_TAC std_ss [o_DEF]
       >> (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
       >> (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
       >> RW_TAC std_ss []
       >> RW_TAC std_ss []
       >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
       >> FULL_SIMP_TAC std_ss [IN_INTER, IN_CROSS, FST, SND, pos_simple_fn_def,
                                DISJOINT_DEF]
       >> METIS_TAC [EXTENSION, NOT_IN_EMPTY, IN_INTER])
   >> CONJ_TAC
   >- (RW_TAC std_ss [IN_IMAGE]
       >> FULL_SIMP_TAC std_ss [o_DEF]
       >> (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
       >> RW_TAC std_ss []
       >> FULL_SIMP_TAC std_ss [IN_CROSS, FST, SND, pos_simple_fn_def]
       >> METIS_TAC [ALGEBRA_INTER, subsets_def, space_def,
                     sigma_algebra_def, measure_space_def])
   >> CONJ_TAC
   >- (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_BIGUNION, IN_IMAGE, IN_CROSS]
       >> `!s'' x. (?x'. ((x = p' x') /\ FST x' IN s /\ SND x' IN s')) =
                   (?x1 x2. ((x = p' (x1,x2)) /\ x1 IN s /\ x2 IN s'))`
        by METIS_TAC [PAIR, FST, SND]
       >> POP_ORW
       >> `!s''. (?x. (s'' = (\(i,j). a i INTER b j) (p x)) /\
                  ?x1 x2. (x = p' (x1,x2)) /\ x1 IN s /\ x2 IN s') =
                 (?x1 x2. (s'' = (\(i,j). a i INTER b j) (p (p' (x1,x2)))) /\
                          x1 IN s /\ x2 IN s')`
        by METIS_TAC []
       >> POP_ORW
       >> FULL_SIMP_TAC std_ss [o_DEF, IN_CROSS]
       >> `!s''. (?x1 x2. (s'' = (\(i,j). a i INTER b j) (p (p' (x1,x2)))) /\
                  x1 IN s /\ x2 IN s') =
                 (?x1 x2. (s'' = (\(i,j). a i INTER b j) (x1,x2)) /\
                  x1 IN s /\ x2 IN s')`
        by METIS_TAC [FST,SND]
       >> POP_ORW
       >> RW_TAC std_ss []
       >> Suff `(?x1 x2. x' IN a x1 INTER b x2 /\ x1 IN s /\ x2 IN s') <=> x' IN m_space m`
       >- METIS_TAC []
       >> RW_TAC std_ss [IN_INTER]
       >> FULL_SIMP_TAC std_ss [pos_simple_fn_def]
       >> `m_space m = (BIGUNION (IMAGE a s)) INTER (BIGUNION (IMAGE b s'))`
                by METIS_TAC [INTER_IDEMPOT]
       >> POP_ORW
       >> Q.PAT_X_ASSUM `BIGUNION (IMAGE b s') = m_space m` (K ALL_TAC)
       >> Q.PAT_X_ASSUM `BIGUNION (IMAGE a s) = m_space m` (K ALL_TAC)
       >> RW_TAC std_ss [IN_INTER, IN_BIGUNION, IN_IMAGE]
       >> METIS_TAC [])
   >> FULL_SIMP_TAC std_ss [o_DEF, pos_simple_fn_def]);

val psfis_present = store_thm
  ("psfis_present",
  ``!m f g a b.
        measure_space m /\
        a IN psfis m f /\ b IN psfis m g ==>
        (?(z:num->real) (z':num->real) c (k:num->bool).
                (!t. t IN m_space m ==> (f t = SIGMA (\i. (z i) * (indicator_fn (c i) t)) k)) /\
                (!t. t IN m_space m ==> (g t = SIGMA (\i. (z' i) * (indicator_fn (c i) t)) k)) /\
                (a = pos_simple_fn_integral m k c z) /\
                (b = pos_simple_fn_integral m k c z') /\
                FINITE k /\
                (!i j. i IN k /\ j IN k /\ i <> j ==> DISJOINT (c i) (c j)) /\
                (!i. i IN k ==> c i IN measurable_sets m) /\
                (BIGUNION (IMAGE c k) = m_space m) /\
                (!i. 0 <= z i) /\ (!i. 0 <= z' i))``,
   RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
   >> (MP_TAC o Q.ISPEC `(x' :(num -> bool) # (num -> 'a -> bool) # (num -> real))`)
        pair_CASES
   >> (MP_TAC o Q.ISPEC `(x :(num -> bool) # (num -> 'a -> bool) # (num -> real))`)
        pair_CASES
   >> (MP_TAC o Q.ISPEC `(x'' :(num -> bool) # (num -> 'a -> bool) # (num -> real))`)           pair_CASES
   >> (MP_TAC o Q.ISPEC `(x''' :(num -> bool) # (num -> 'a -> bool) # (num -> real))`)
        pair_CASES
   >> RW_TAC std_ss []
   >> (MP_TAC o Q.ISPEC `(r' :(num -> 'a -> bool) # (num -> real))`) pair_CASES
   >> (MP_TAC o Q.ISPEC `(r :(num -> 'a -> bool) # (num -> real))`) pair_CASES
   >> (MP_TAC o Q.ISPEC `(r'' :(num -> 'a -> bool) # (num -> real))`) pair_CASES
   >> (MP_TAC o Q.ISPEC `(r''' :(num -> 'a -> bool) # (num -> real))`) pair_CASES
   >> RW_TAC std_ss []
   >> FULL_SIMP_TAC std_ss [PAIR_EQ]
   >> MATCH_MP_TAC pos_simple_fn_integral_present
   >> METIS_TAC []);

val pos_simple_fn_integral_add = store_thm
  ("pos_simple_fn_integral_add",
  ``!m f (s:num->bool) a (x:num->real)
        g (s':num->bool) b (y:num->real).
        measure_space m /\
        pos_simple_fn m f s a x /\ pos_simple_fn m g s' b y ==>
        ?s'' c z. pos_simple_fn m (\x. f x + g x) s'' c z /\
                (pos_simple_fn_integral m s a x +
                 pos_simple_fn_integral m s' b y =
                 pos_simple_fn_integral m s'' c z)``,
   rpt STRIP_TAC
   >> (MP_TAC o Q.SPECL [`m`,`f`,`s`,`a`,`x`,`g`,`s'`,`b`,`y`]) pos_simple_fn_integral_present
   >> RW_TAC std_ss [] >> ASM_SIMP_TAC std_ss []
   >> Q.EXISTS_TAC `k` >> Q.EXISTS_TAC `c` >> Q.EXISTS_TAC `(\i. z i + z' i)`
   >> FULL_SIMP_TAC std_ss [pos_simple_fn_def, pos_simple_fn_integral_def]
   >> reverse CONJ_TAC
   >- (RW_TAC std_ss [GSYM REAL_SUM_IMAGE_ADD]
       >> `!i. z i * measure m (c i) + z' i * measure m (c i) =
           (z i + z' i) * measure m (c i)`
        by (STRIP_TAC >> REAL_ARITH_TAC)
       >> RW_TAC std_ss [])
   >> CONJ_TAC >- RW_TAC std_ss [REAL_LE_ADD]
   >> reverse CONJ_TAC
   >- RW_TAC std_ss [REAL_LE_ADD]
   >> rpt STRIP_TAC
   >> `SIGMA (\i. x i * indicator_fn (a i) x') s =
       SIGMA (\i. z i * indicator_fn (c i) x') k` by METIS_TAC []
   >> POP_ORW
   >> `SIGMA (\i. y i * indicator_fn (b i) x') s' =
       SIGMA (\i. z' i * indicator_fn (c i) x') k` by METIS_TAC []
   >> POP_ORW
   >> RW_TAC std_ss [GSYM REAL_SUM_IMAGE_ADD]
   >> `!i. z i * indicator_fn (c i) x' + z' i * indicator_fn (c i) x' =
            (z i + z' i) * indicator_fn (c i) x'`
        by (rpt STRIP_TAC >> REAL_ARITH_TAC)
   >> RW_TAC std_ss []);

val psfis_add = store_thm
  ("psfis_add",
  ``!m f g a b.
        measure_space m /\
        a IN psfis m f /\ b IN psfis m g ==>
        a + b IN psfis m (\x. f x + g x)``,
   RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
   >> (MP_TAC o Q.ISPEC `(x' :(num -> bool) # (num -> 'a -> bool) # (num -> real))`)
        pair_CASES
   >> (MP_TAC o Q.ISPEC `(x :(num -> bool) # (num -> 'a -> bool) # (num -> real))`)
        pair_CASES
   >> (MP_TAC o Q.ISPEC `(x'' :(num -> bool) # (num -> 'a -> bool) # (num -> real))`)           pair_CASES
   >> (MP_TAC o Q.ISPEC `(x''' :(num -> bool) # (num -> 'a -> bool) # (num -> real))`)
        pair_CASES
   >> RW_TAC std_ss []
   >> (MP_TAC o Q.ISPEC `(r' :(num -> 'a -> bool) # (num -> real))`) pair_CASES
   >> (MP_TAC o Q.ISPEC `(r :(num -> 'a -> bool) # (num -> real))`) pair_CASES
   >> (MP_TAC o Q.ISPEC `(r'' :(num -> 'a -> bool) # (num -> real))`) pair_CASES
   >> (MP_TAC o Q.ISPEC `(r''' :(num -> 'a -> bool) # (num -> real))`) pair_CASES
   >> RW_TAC std_ss []
   >> FULL_SIMP_TAC std_ss [PAIR_EQ]
   >> Suff `?s a x. (pos_simple_fn_integral m q''' q'''' r'''' +
                      pos_simple_fn_integral m q q'''''' r'''''' =
                      pos_simple_fn_integral m s a x) /\
            pos_simple_fn m (\x. f x + g x) s a x`
   >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `(s,a,x)`
       >> RW_TAC std_ss [] >> Q.EXISTS_TAC `(s,a,x)`
       >> RW_TAC std_ss [PAIR_EQ])
   >> ONCE_REWRITE_TAC [CONJ_COMM]
   >> MATCH_MP_TAC pos_simple_fn_integral_add >> RW_TAC std_ss []);

val pos_simple_fn_integral_mono = store_thm
  ("pos_simple_fn_integral_mono",
  ``!m f (s:num->bool) a (x:num->real)
        g (s':num->bool) b (y:num->real).
        measure_space m /\
        pos_simple_fn m f s a x /\ pos_simple_fn m g s' b y /\
        (!x. f x <= g x) ==>
        pos_simple_fn_integral m s a x <= pos_simple_fn_integral m s' b y``,
   rpt STRIP_TAC
   >> (MP_TAC o Q.SPECL [`m`,`f`,`s`,`a`,`x`,`g`,`s'`,`b`,`y`]) pos_simple_fn_integral_present
   >> RW_TAC std_ss [] >> ASM_SIMP_TAC std_ss []
   >> RW_TAC std_ss [pos_simple_fn_integral_def]
   >> (MATCH_MP_TAC o UNDISCH o Q.ISPEC `k:num->bool`) REAL_SUM_IMAGE_MONO
   >> RW_TAC std_ss []
   >> Cases_on `c x' = {}`
   >- RW_TAC real_ss [MEASURE_EMPTY]
   >> `!x. x IN m_space m ==>
        SIGMA (\i. z i * indicator_fn (c i) x) k <=
        SIGMA (\i. z' i * indicator_fn (c i) x) k`
        by METIS_TAC []
   >> `?t ss. (c x' = t INSERT ss) /\ ~(t IN ss)`
        by METIS_TAC [SET_CASES]
   >> Q.PAT_X_ASSUM `!x. x IN m_space m ==> SIGMA (\i. z i * indicator_fn (c i) x) k <=
                        SIGMA (\i. z' i * indicator_fn (c i) x) k`
        (MP_TAC o Q.SPEC `t`)
   >> `k = x' INSERT (k DELETE x')`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INSERT, IN_DELETE] >> METIS_TAC [])
   >> POP_ORW
   >> ASM_SIMP_TAC std_ss [REAL_SUM_IMAGE_THM, FINITE_INSERT, FINITE_DELETE, DELETE_DELETE]
   >> `FINITE (k DELETE x')` by RW_TAC std_ss [FINITE_DELETE]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(k :num -> bool)DELETE x'`)
                                REAL_SUM_IMAGE_IN_IF]
   >> `(\x. (if x IN k DELETE x' then (\i. z i * indicator_fn (c i) t) x else 0)) =
       (\x. 0)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [IN_DELETE, indicator_fn_def]
            >> Q.PAT_X_ASSUM
                `!i j. i IN k /\ j IN k /\ i <> j ==> DISJOINT (c i) (c j)`
                (MP_TAC o UNDISCH_ALL o
                REWRITE_RULE [GSYM AND_IMP_INTRO] o Q.SPECL [`x''`, `x'`])
            >> RW_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_INSERT]
            >> METIS_TAC [])
   >> POP_ORW
   >> `(\x. (if x IN k DELETE x' then (\i. z' i * indicator_fn (c i) t) x else 0)) =
       (\x. 0)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [IN_DELETE, indicator_fn_def]
            >> Q.PAT_X_ASSUM
                `!i j. i IN k /\ j IN k /\ i <> j ==> DISJOINT (c i) (c j)`
                (MP_TAC o UNDISCH_ALL o
                REWRITE_RULE [GSYM AND_IMP_INTRO] o Q.SPECL [`x''`, `x'`])
            >> RW_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_INSERT]
            >> METIS_TAC [])
   >> POP_ORW
   >> Know `t IN BIGUNION (IMAGE c k)`
   >- (RW_TAC std_ss [IN_BIGUNION, IN_IMAGE] >> METIS_TAC [IN_INSERT])
   >> (MP_TAC o Q.SPECL [`(\x.0)`,`0`] o UNDISCH o Q.ISPEC `(k :num -> bool)DELETE x'`)
        REAL_SUM_IMAGE_FINITE_CONST
   >> RW_TAC real_ss [indicator_fn_def, IN_INSERT]
   >> METIS_TAC [REAL_LE_MUL2, measure_space_def, positive_def, REAL_LE_REFL]);

val pos_simple_fn_integral_mono_on_mspace = store_thm
  ("pos_simple_fn_integral_mono_on_mspace",
  ``!m f (s:num->bool) a (x:num->real)
        g (s':num->bool) b (y:num->real).
        measure_space m /\
        pos_simple_fn m f s a x /\ pos_simple_fn m g s' b y /\
        (!x. x IN m_space m ==> f x <= g x) ==>
        pos_simple_fn_integral m s a x <= pos_simple_fn_integral m s' b y``,
   rpt STRIP_TAC
   >> (MP_TAC o Q.SPECL [`m`,`f`,`s`,`a`,`x`,`g`,`s'`,`b`,`y`]) pos_simple_fn_integral_present
   >> RW_TAC std_ss [] >> ASM_SIMP_TAC std_ss []
   >> RW_TAC std_ss [pos_simple_fn_integral_def]
   >> (MATCH_MP_TAC o UNDISCH o Q.ISPEC `k:num->bool`) REAL_SUM_IMAGE_MONO
   >> RW_TAC std_ss []
   >> Cases_on `c x' = {}`
   >- RW_TAC real_ss [MEASURE_EMPTY]
   >> `!x. x IN m_space m ==>
        SIGMA (\i. z i * indicator_fn (c i) x) k <=
        SIGMA (\i. z' i * indicator_fn (c i) x) k`
        by METIS_TAC []
   >> `?t ss. (c x' = t INSERT ss) /\ ~(t IN ss)`
        by METIS_TAC [SET_CASES]
   >> Q.PAT_X_ASSUM `!x. x IN m_space m ==> SIGMA (\i. z i * indicator_fn (c i) x) k <=
                        SIGMA (\i. z' i * indicator_fn (c i) x) k`
        (MP_TAC o Q.SPEC `t`)
   >> `k = x' INSERT (k DELETE x')`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INSERT, IN_DELETE] >> METIS_TAC [])
   >> POP_ORW
   >> ASM_SIMP_TAC std_ss [REAL_SUM_IMAGE_THM, FINITE_INSERT, FINITE_DELETE, DELETE_DELETE]
   >> `FINITE (k DELETE x')` by RW_TAC std_ss [FINITE_DELETE]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `(k :num -> bool)DELETE x'`)
                                REAL_SUM_IMAGE_IN_IF]
   >> `(\x. (if x IN k DELETE x' then (\i. z i * indicator_fn (c i) t) x else 0)) =
       (\x. 0)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [IN_DELETE, indicator_fn_def]
            >> Q.PAT_X_ASSUM
                `!i j. i IN k /\ j IN k /\ i <> j ==> DISJOINT (c i) (c j)`
                (MP_TAC o UNDISCH_ALL o
                REWRITE_RULE [GSYM AND_IMP_INTRO] o Q.SPECL [`x''`, `x'`])
            >> RW_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_INSERT]
            >> METIS_TAC [])
   >> POP_ORW
   >> `(\x. (if x IN k DELETE x' then (\i. z' i * indicator_fn (c i) t) x else 0)) =
       (\x. 0)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [IN_DELETE, indicator_fn_def]
            >> Q.PAT_X_ASSUM
                `!i j. i IN k /\ j IN k /\ i <> j ==> DISJOINT (c i) (c j)`
                (MP_TAC o UNDISCH_ALL o
                REWRITE_RULE [GSYM AND_IMP_INTRO] o Q.SPECL [`x''`, `x'`])
            >> RW_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_INSERT]
            >> METIS_TAC [])
   >> POP_ORW
   >> Know `t IN BIGUNION (IMAGE c k)`
   >- (RW_TAC std_ss [IN_BIGUNION, IN_IMAGE] >> METIS_TAC [IN_INSERT])
   >> (MP_TAC o Q.SPECL [`(\x.0)`,`0`] o UNDISCH o Q.ISPEC `(k :num -> bool)DELETE x'`)
        REAL_SUM_IMAGE_FINITE_CONST
   >> RW_TAC real_ss [indicator_fn_def, IN_INSERT]
   >> METIS_TAC [REAL_LE_MUL2, measure_space_def, positive_def, REAL_LE_REFL]);

val psfis_mono = store_thm
  ("psfis_mono",
  ``!m f g a b.
        measure_space m /\
        a IN psfis m f /\ b IN psfis m g /\
        (!x. x IN m_space m ==> f x <= g x) ==>
        a <= b``,
   RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
   >> (MP_TAC o Q.ISPEC `(x' :(num -> bool) # (num -> 'a -> bool) # (num -> real))`)
        pair_CASES
   >> (MP_TAC o Q.ISPEC `(x :(num -> bool) # (num -> 'a -> bool) # (num -> real))`)
        pair_CASES
   >> (MP_TAC o Q.ISPEC `(x'' :(num -> bool) # (num -> 'a -> bool) # (num -> real))`)           pair_CASES
   >> (MP_TAC o Q.ISPEC `(x''' :(num -> bool) # (num -> 'a -> bool) # (num -> real))`)
        pair_CASES
   >> RW_TAC std_ss []
   >> (MP_TAC o Q.ISPEC `(r' :(num -> 'a -> bool) # (num -> real))`) pair_CASES
   >> (MP_TAC o Q.ISPEC `(r :(num -> 'a -> bool) # (num -> real))`) pair_CASES
   >> (MP_TAC o Q.ISPEC `(r'' :(num -> 'a -> bool) # (num -> real))`) pair_CASES
   >> (MP_TAC o Q.ISPEC `(r''' :(num -> 'a -> bool) # (num -> real))`) pair_CASES
   >> RW_TAC std_ss []
   >> FULL_SIMP_TAC std_ss [PAIR_EQ]
   >> MATCH_MP_TAC pos_simple_fn_integral_mono_on_mspace
   >> METIS_TAC []);

val pos_simple_fn_integral_unique = store_thm
  ("pos_simple_fn_integral_unique",
  ``!m f (s:num->bool) a (x:num->real)
        (s':num->bool) b (y:num->real).
        measure_space m /\
        pos_simple_fn m f s a x /\ pos_simple_fn m f s' b y ==>
        (pos_simple_fn_integral m s a x = pos_simple_fn_integral m s' b y)``,
   METIS_TAC [REAL_LE_ANTISYM, REAL_LE_REFL, pos_simple_fn_integral_mono]);

val psfis_unique = store_thm
  ("psfis_unique",
  ``!m f a b.
        measure_space m /\
        a IN psfis m f /\ b IN psfis m f ==>
        (a = b)``,
   METIS_TAC [REAL_LE_ANTISYM, REAL_LE_REFL, psfis_mono]);

val pos_simple_fn_integral_indicator = store_thm
  ("pos_simple_fn_integral_indicator",
  ``!m A.
        measure_space m /\ A IN measurable_sets m ==>
        (?s a x. pos_simple_fn m (indicator_fn A) s a x /\
                 (pos_simple_fn_integral m s a x = measure m A))``,
   RW_TAC std_ss [pos_simple_fn_integral_def, pos_simple_fn_def]
   >> `!x. x IN A ==> x IN m_space m`
        by METIS_TAC [measure_space_def, sigma_algebra_def, algebra_def,
                      subset_class_def, subsets_def, space_def, SUBSET_DEF]
   >> `m_space m DIFF A IN measurable_sets m`
        by METIS_TAC [measure_space_def, sigma_algebra_def, ALGEBRA_COMPL,
                      subsets_def, space_def]
   >> `{1:num} DELETE 0 = {1}`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC real_ss [IN_SING, IN_DELETE])
   >> `IMAGE (\i:num. (if i = 0 then A else m_space m DIFF A)) {0; 1} =
       {A; m_space m DIFF A}`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC real_ss [IN_INSERT, IN_SING, IN_IMAGE]
            >> METIS_TAC [DECIDE ``~(1:num = 0)``])
   >> Q.EXISTS_TAC `{0;1}`
   >> Q.EXISTS_TAC `\i. if i = 0 then A else m_space m DIFF A`
   >> Q.EXISTS_TAC `\i. if i = 0 then 1 else 0`
   >> RW_TAC real_ss [REAL_SUM_IMAGE_THM, IN_DISJOINT, IN_DIFF, FINITE_INSERT, FINITE_SING,
                      IN_INSERT, IN_SING, REAL_SUM_IMAGE_SING, BIGUNION_PAIR, EXTENSION,
                      IN_UNION, IN_DIFF, indicator_fn_def]
   >> METIS_TAC []);

val psfis_indicator = store_thm
  ("psfis_indicator",
  ``!m A. measure_space m /\ A IN measurable_sets m ==>
          measure m A IN psfis m (indicator_fn A)``,
   RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
   >> (MP_TAC o Q.ISPEC `(x' :(num -> bool) # (num -> 'a -> bool) # (num -> real))`)
        pair_CASES
   >> (MP_TAC o Q.ISPEC `(x :(num -> bool) # (num -> 'a -> bool) # (num -> real))`)
        pair_CASES
   >> (MP_TAC o Q.ISPEC `(x'' :(num -> bool) # (num -> 'a -> bool) # (num -> real))`)           pair_CASES
   >> (MP_TAC o Q.ISPEC `(x''' :(num -> bool) # (num -> 'a -> bool) # (num -> real))`)
        pair_CASES
   >> RW_TAC std_ss []
   >> (MP_TAC o Q.ISPEC `(r' :(num -> 'a -> bool) # (num -> real))`) pair_CASES
   >> (MP_TAC o Q.ISPEC `(r :(num -> 'a -> bool) # (num -> real))`) pair_CASES
   >> (MP_TAC o Q.ISPEC `(r'' :(num -> 'a -> bool) # (num -> real))`) pair_CASES
   >> (MP_TAC o Q.ISPEC `(r''' :(num -> 'a -> bool) # (num -> real))`) pair_CASES
   >> RW_TAC std_ss []
   >> Suff `?s a x. pos_simple_fn m (indicator_fn A) s a x /\
                    (pos_simple_fn_integral m s a x = measure m A)`
   >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `(s,a,x)`
       >> RW_TAC std_ss [] >> Q.EXISTS_TAC `(s,a,x)`
       >> RW_TAC std_ss [PAIR_EQ])
   >> MATCH_MP_TAC pos_simple_fn_integral_indicator
   >> ASM_REWRITE_TAC []);

val pos_simple_fn_integral_mult = store_thm
  ("pos_simple_fn_integral_mult",
  ``!m f s a x.
        measure_space m /\ pos_simple_fn m f s a x ==>
        (!z. 0 <= z ==>
                ?s' b y.
                    pos_simple_fn m (\x. z * f x) s' b y /\
                    (pos_simple_fn_integral m s' b y =
                     z * pos_simple_fn_integral m s a x))``,
   RW_TAC std_ss [pos_simple_fn_integral_def, pos_simple_fn_def]
   >> Q.EXISTS_TAC `s` >> Q.EXISTS_TAC `a` >> Q.EXISTS_TAC `(\i. z * x i)`
   >> RW_TAC real_ss [GSYM REAL_SUM_IMAGE_CMUL, REAL_LE_MUL, REAL_MUL_ASSOC]);

val psfis_mult = store_thm
  ("psfis_mult",
  ``!m f a. measure_space m /\ a IN psfis m f ==>
           (!z. 0 <= z ==> z * a IN psfis m (\x. z * f x))``,
   RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
   >> (MP_TAC o Q.ISPEC `(x' :(num -> bool) # (num -> 'a -> bool) # (num -> real))`)
        pair_CASES
   >> (MP_TAC o Q.ISPEC `(x :(num -> bool) # (num -> 'a -> bool) # (num -> real))`)
        pair_CASES
   >> (MP_TAC o Q.ISPEC `(x'' :(num -> bool) # (num -> 'a -> bool) # (num -> real))`)           pair_CASES
   >> (MP_TAC o Q.ISPEC `(x''' :(num -> bool) # (num -> 'a -> bool) # (num -> real))`)
        pair_CASES
   >> RW_TAC std_ss []
   >> (MP_TAC o Q.ISPEC `(r' :(num -> 'a -> bool) # (num -> real))`) pair_CASES
   >> (MP_TAC o Q.ISPEC `(r :(num -> 'a -> bool) # (num -> real))`) pair_CASES
   >> (MP_TAC o Q.ISPEC `(r'' :(num -> 'a -> bool) # (num -> real))`) pair_CASES
   >> (MP_TAC o Q.ISPEC `(r''' :(num -> 'a -> bool) # (num -> real))`) pair_CASES
   >> RW_TAC std_ss []
   >> FULL_SIMP_TAC std_ss [PAIR_EQ]
   >> Suff `?s a x. pos_simple_fn m (\x. z * f x) s a x /\
                   (pos_simple_fn_integral m s a x =
                    z * pos_simple_fn_integral m q''' q r'''')`
   >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `(s,a,x)`
       >> RW_TAC std_ss [] >> Q.EXISTS_TAC `(s,a,x)`
       >> RW_TAC std_ss [PAIR_EQ])
   >> METIS_TAC [pos_simple_fn_integral_mult]);

val pos_simple_fn_integral_REAL_SUM_IMAGE = store_thm
  ("pos_simple_fn_integral_REAL_SUM_IMAGE",
  ``!m f s a x P.
        measure_space m /\
        (!i. i IN P ==> pos_simple_fn m (f i) (s i) (a i) (x i)) /\
        FINITE P ==>
        (?s' a' x'. pos_simple_fn m (\t. SIGMA (\i. f i t) P) s' a' x' /\
                    (pos_simple_fn_integral m s' a' x' =
                     SIGMA (\i. pos_simple_fn_integral m (s i) (a i) (x i)) P))``,
   Suff `!P:'b->bool. FINITE P ==>
        (\P:'b->bool. !(m :('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real))
              (f :'b -> 'a -> real) (s :'b -> num -> bool)
              (a :'b -> num -> 'a -> bool) (x :'b -> num -> real).
        measure_space m /\
        (!i:'b. i IN P ==> pos_simple_fn m (f i) (s i) (a i) (x i)) ==>
        (?(s' :num -> bool) (a' :num -> 'a -> bool) (x' :num -> real).
                    pos_simple_fn m (\t. SIGMA (\i. f i t) P) s' a' x' /\
                    (pos_simple_fn_integral m s' a' x' =
                     SIGMA (\i. pos_simple_fn_integral m (s i) (a i) (x i)) P))) P`
   >- METIS_TAC []
   >> MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC std_ss [NOT_IN_EMPTY, REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT, IN_INSERT]
   >- ((MP_TAC o Q.SPECL [`m`,`{}`]) pos_simple_fn_integral_indicator
       >> SIMP_TAC std_ss [MEASURE_EMPTY, indicator_fn_def, NOT_IN_EMPTY]
       >> METIS_TAC [measure_space_def, sigma_algebra_def,
                     ALGEBRA_EMPTY, subsets_def, space_def])
   >> Q.PAT_X_ASSUM `!m f s' a x. M`
        (MP_TAC o Q.SPECL [`m`,`f`,`s'`,`a`,`x`])
   >> RW_TAC std_ss []
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [GSYM thm])
   >> `!s''' a'' x''. (\t. f e t + SIGMA (\i. f i t) s) =
                      (\t. f e t + (\t. SIGMA (\i. f i t) s) t)`
        by METIS_TAC []
   >> POP_ORW
   >> MATCH_MP_TAC (GSYM pos_simple_fn_integral_add)
   >> RW_TAC std_ss []);

val psfis_REAL_SUM_IMAGE = store_thm
  ("psfis_REAL_SUM_IMAGE",
  ``!m f a P.
        measure_space m /\
        (!i. i IN P ==> a i IN psfis m (f i)) /\
        FINITE P ==>
        (SIGMA a P) IN psfis m (\t. SIGMA (\i. f i t) P)``,
   Suff `!P:'b->bool. FINITE P ==>
        (\P:'b->bool. !(m :('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real))
                       (f :'b -> 'a -> real) (a :'b -> real).
                measure_space m /\ (!(i :'b). i IN P ==> a i IN psfis m (f i)) ==>
                SIGMA a P IN
                psfis m (\(t :'a). SIGMA (\(i :'b). f i t) P)) P`
   >- RW_TAC std_ss []
   >> MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC std_ss [NOT_IN_EMPTY, REAL_SUM_IMAGE_THM, DELETE_NON_ELEMENT, IN_INSERT]
   >- ((MP_TAC o Q.SPECL [`m`,`{}`]) psfis_indicator
       >> SIMP_TAC std_ss [MEASURE_EMPTY, indicator_fn_def, NOT_IN_EMPTY]
       >> METIS_TAC [measure_space_def, sigma_algebra_def,
                     ALGEBRA_EMPTY, subsets_def, space_def])
   >> Q.PAT_X_ASSUM `!m f a. M`
        (MP_TAC o Q.SPECL [`m`,`f`,`a`])
   >> RW_TAC std_ss []
   >> `(\t. f e t + SIGMA (\i. f i t) s) =
       (\t. f e t + (\t. SIGMA (\i. f i t) s) t)`
        by METIS_TAC []
   >> POP_ORW
   >> MATCH_MP_TAC psfis_add
   >> RW_TAC std_ss []);

val psfis_intro = store_thm
  ("psfis_intro",
  ``!m a x P.
        measure_space m /\ (!i. i IN P ==> a i IN measurable_sets m) /\
        (!i. 0 <= x i) /\ FINITE P ==>
        (SIGMA (\i. x i * measure m (a i)) P) IN
        psfis m (\t. SIGMA (\i. x i * indicator_fn (a i) t) P)``,
   RW_TAC std_ss []
   >> `!t. (\i. x i * indicator_fn (a i) t) =
           (\i. (\i t. x i * indicator_fn (a i) t) i t)`
        by METIS_TAC []
   >> POP_ORW
   >> MATCH_MP_TAC psfis_REAL_SUM_IMAGE
   >> RW_TAC std_ss []
   >> METIS_TAC [psfis_mult, psfis_indicator]);

val psfis_nonneg = store_thm
  ("psfis_nonneg",
  ``!m f a. a IN psfis m f ==> nonneg f``,
   RW_TAC std_ss [nonneg_def, psfis_def, IN_IMAGE, psfs_def,
                  GSPECIFICATION]
   >> (MP_TAC o Q.ISPEC `(x' :(num -> bool) # (num -> 'a -> bool) # (num -> real))`)
        pair_CASES
   >> RW_TAC std_ss []
   >> (MP_TAC o Q.ISPEC `(r :(num -> 'a -> bool) # (num -> real))`) pair_CASES
   >> RW_TAC std_ss []
   >> FULL_SIMP_TAC std_ss [PAIR_EQ, pos_simple_fn_def]);

val IN_psfis = store_thm
  ("IN_psfis",
  ``!m r f. r IN psfis m f ==>
                ?s a x. pos_simple_fn m f s a x /\
                        (r = pos_simple_fn_integral m s a x)``,
   RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
   >> (MP_TAC o Q.ISPEC `(x' :(num -> bool) # (num -> 'a -> bool) # (num -> real))`)
                pair_CASES
   >> RW_TAC std_ss []
   >> (MP_TAC o Q.ISPEC `(x :(num -> bool) # (num -> 'a -> bool) # (num -> real))`)
                pair_CASES
   >> RW_TAC std_ss []
   >> (MP_TAC o Q.ISPEC `(r :(num -> 'a -> bool) # (num -> real))`)
                pair_CASES
   >> RW_TAC std_ss []
   >> (MP_TAC o Q.ISPEC `(r' :(num -> 'a -> bool) # (num -> real))`)
                pair_CASES
   >> RW_TAC std_ss []
   >> FULL_SIMP_TAC std_ss [PAIR_EQ]
   >> METIS_TAC []);

val pos_psfis = store_thm
  ("pos_psfis",
  ``!r m f. measure_space m /\
             r IN psfis m f ==>
                0 <= r``,
    rpt STRIP_TAC
    >> `positive m` by FULL_SIMP_TAC std_ss [measure_space_def]
    >> `?s a x. pos_simple_fn m f s a x /\
                        (r = pos_simple_fn_integral m s a x)`
        by METIS_TAC [IN_psfis]
    >> RW_TAC std_ss [pos_simple_fn_integral_def] >> MATCH_MP_TAC REAL_SUM_IMAGE_POS
    >> FULL_SIMP_TAC std_ss [pos_simple_fn_def, positive_def, REAL_LE_MUL]);

val f_plus_minus = prove
  (``!f x. f x = fn_plus f x - fn_minus f x``,
   RW_TAC real_ss [fn_plus_def, fn_minus_def]
   >> REAL_ARITH_TAC);

val f_plus_minus2 = prove
  (``!f. f = (\x. fn_plus f x - fn_minus f x)``,
   RW_TAC std_ss [GSYM f_plus_minus, ETA_THM]);

val f_abs_plus_minus = prove
  (``!f x. abs (f x) = fn_plus f x + fn_minus f x``,
   RW_TAC std_ss [abs, fn_plus_def, fn_minus_def]
   >> REAL_ARITH_TAC);

val nonneg_fn_plus_fn_minus = prove
  (``!f. nonneg f ==>
        (fn_plus f = f) /\ (fn_minus f = (\x. 0))``,
   RW_TAC std_ss [nonneg_def, fn_plus_def, fn_minus_def, ETA_THM]);

val pos_fn_plus_fn_minus_help = prove
  (``!x. 0 <= f x ==> (fn_plus f x = f x) /\ (fn_minus f x = 0)``,
   RW_TAC std_ss [fn_plus_def, fn_minus_def]);

val real_neg_fn_plus_fn_minus_help = prove
  (``!x. f x <= 0 ==> (fn_minus f x = ~ f x) /\ (fn_plus f x = 0)``,
   RW_TAC std_ss [fn_plus_def, fn_minus_def] >> METIS_TAC [REAL_LE_ANTISYM, REAL_NEG_EQ0]);

val real_neg_fn_plus_fn_minus = prove
  (``!f. (!x. f x <= 0) ==>
        (fn_minus f = (\x. ~ f x)) /\ (fn_plus f = (\x. 0))``,
   RW_TAC std_ss [real_neg_fn_plus_fn_minus_help, FUN_EQ_THM]);

val real_fn_plus_fn_minus_pos_times = prove
  (``!a. 0 <= a ==> (fn_plus (\x. a * f x) = (\x. a * fn_plus f x)) /\
                    (fn_minus (\x. a * f x) = (\x. a * fn_minus f x))``,
    RW_TAC std_ss [fn_plus_def, fn_minus_def, FUN_EQ_THM]
  >> ( reverse (RW_TAC real_ss [REAL_ENTIRE, REAL_NEG_EQ0])
    >- METIS_TAC [REAL_LE_MUL]
    >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
    >> `0 < a * f x` by METIS_TAC [REAL_LE_LT, REAL_ENTIRE]
    >> METIS_TAC [real_lt, REAL_LE_LT, REAL_LT_LMUL_0] ) );

val real_fn_plus_fn_minus_neg_times = prove
  (``!a. a <= 0 ==> (fn_plus (\x. a * f x) = (\x. ~a * fn_minus f x)) /\
                    (fn_minus (\x. a * f x) = (\x. ~a * fn_plus f x))``,
    RW_TAC std_ss [fn_plus_def, fn_minus_def, FUN_EQ_THM]
  >> ( RW_TAC real_ss [REAL_ENTIRE, REAL_NEG_EQ0]
    >- METIS_TAC [REAL_LT_RMUL_0, REAL_LT_LE, REAL_ENTIRE, real_lt, REAL_NEG_EQ0]
    >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
    >> FULL_SIMP_TAC std_ss [GSYM real_lt]
    >> FULL_SIMP_TAC std_ss [REAL_LE_LT]
    >> FULL_SIMP_TAC std_ss [GSYM REAL_NEG_GT0, GSYM REAL_MUL_RNEG]
    >> METIS_TAC [REAL_LT_ANTISYM, REAL_LT_RMUL_0, REAL_NEG_GT0] ));

val fn_plus_fn_minus_borel_measurable = store_thm
  ("fn_plus_fn_minus_borel_measurable",
  ``!f m. measure_space m /\ f IN borel_measurable (m_space m, measurable_sets m) ==>
         (fn_plus f) IN borel_measurable (m_space m, measurable_sets m) /\
         (fn_minus f) IN borel_measurable (m_space m, measurable_sets m)``,
   (rpt STRIP_TAC >> RW_TAC std_ss [borel_measurable_le_iff])
   >- (Cases_on `0 <= a`
       >- (`!w. fn_plus f w <= a <=> f w <= a`
                by (RW_TAC real_ss [fn_plus_def] >> METIS_TAC [REAL_LTE_TRANS, REAL_LT_IMP_LE, GSYM real_lt])
           >> POP_ORW >> METIS_TAC [borel_measurable_le_iff])
       >> `{w | w IN m_space m /\ fn_plus f w <= a} = {}`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [GSPECIFICATION, NOT_IN_EMPTY, fn_plus_def]
                    >> RW_TAC real_ss [] >> METIS_TAC [REAL_LE_TRANS])
       >> POP_ORW >> FULL_SIMP_TAC std_ss [measure_space_def, SIGMA_ALGEBRA, space_def, subsets_def])
   >> Cases_on `0 <= a`
   >- (`!w. fn_minus f w <= a <=> ~a <= f w`
        by (RW_TAC real_ss [fn_minus_def]
            >> METIS_TAC [REAL_NEG_GE0, REAL_LE_TRANS, REAL_LE_NEGR, REAL_NEG_NEG, REAL_LE_NEG])
       >> POP_ORW
       >> METIS_TAC [borel_measurable_ge_iff])
   >> `{w | w IN m_space m /\ fn_minus f w <= a} = {}`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [GSPECIFICATION, NOT_IN_EMPTY, fn_minus_def]
            >> RW_TAC real_ss []
            >> METIS_TAC [REAL_LET_TRANS, REAL_LTE_TRANS, REAL_LT_IMP_LE, GSYM real_lt,
                          REAL_LE_NEGR, REAL_NEG_NEG, REAL_LE_NEG, REAL_NEG_GE0])
   >> POP_ORW >> FULL_SIMP_TAC std_ss [measure_space_def, SIGMA_ALGEBRA, space_def, subsets_def]);

val fn_plus_fn_minus_borel_measurable_iff = store_thm
  ("fn_plus_fn_minus_borel_measurable_iff",
  ``!f m. measure_space m ==>
         (f IN borel_measurable (m_space m, measurable_sets m) <=>
         (fn_plus f) IN borel_measurable (m_space m, measurable_sets m) /\
         (fn_minus f) IN borel_measurable (m_space m, measurable_sets m))``,
   rpt STRIP_TAC >> EQ_TAC
   >- RW_TAC std_ss [fn_plus_fn_minus_borel_measurable]
   >> STRIP_TAC >> ONCE_REWRITE_TAC [f_plus_minus2]
   >> MATCH_MP_TAC borel_measurable_sub_borel_measurable
   >> RW_TAC std_ss []);

val psfis_borel_measurable = store_thm
  ("psfis_borel_measurable",
  ``!m f a. measure_space m /\ a IN psfis m f ==>
            f IN borel_measurable (m_space m, measurable_sets m)``,
   rpt STRIP_TAC
   >> (MP_TAC o Q.SPECL [`m`,`a`,`f`]) IN_psfis
   >> RW_TAC std_ss [pos_simple_fn_def]
   >> RW_TAC std_ss [borel_measurable_le_iff]
   >> `!w. w IN m_space m /\ f w <= a <=>
           w IN m_space m /\ (\w. SIGMA (\i. x i * indicator_fn (a' i) w) s) w <= a`
        by (RW_TAC std_ss [] >> METIS_TAC [])
   >> POP_ORW
   >> Suff `(\w. SIGMA (\i. x i * indicator_fn (a' i) w) s) IN
                borel_measurable (m_space m, measurable_sets m)`
   >- METIS_TAC [GSYM borel_measurable_le_iff]
   >> `!w i. x i * indicator_fn (a' i) w = (\i w. x i * indicator_fn (a' i) w) i w`
        by RW_TAC std_ss []
   >> POP_ORW >> MATCH_MP_TAC borel_measurable_SIGMA_borel_measurable
   >> RW_TAC std_ss []
   >> `!w. x i * indicator_fn (a' i) w =
           0 + indicator_fn (a' i) w * x i`
        by RW_TAC real_ss [REAL_MUL_COMM]
   >> POP_ORW
   >> Suff `indicator_fn (a' i) IN borel_measurable (m_space m, measurable_sets m)`
   >- METIS_TAC [affine_borel_measurable]
   >> MATCH_MP_TAC borel_measurable_indicator
   >> FULL_SIMP_TAC std_ss [measure_space_def, subsets_def]);

val real_le_mult_sustain = prove
  (``!r y. (!z. 0 < z /\ z < 1 ==> z * r <= y) ==> r <= y``,
   rpt STRIP_TAC
   >> reverse (Cases_on `0<y`)
   >- (`0<(1:real)` by RW_TAC real_ss []
       >> `?z. 0 < z /\ z < 1` by (MATCH_MP_TAC REAL_MEAN >> RW_TAC std_ss [])
       >> `z * r <= y` by RW_TAC std_ss []
       >> FULL_SIMP_TAC std_ss [REAL_NOT_LT]
       >> `z * r <= 0` by METIS_TAC [REAL_LE_TRANS]
       >> `z <= 1 /\ r <= 0`
                by (RW_TAC std_ss [REAL_LT_IMP_LE]
                    >> METIS_TAC [GSYM REAL_LE_RDIV_EQ, REAL_DIV_LZERO, REAL_MUL_COMM])
       >> MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `z * r`
       >> ASM_REWRITE_TAC []
       >> ONCE_REWRITE_TAC [GSYM REAL_LE_NEG]
       >> ONCE_REWRITE_TAC [GSYM REAL_MUL_RNEG]
       >> (MP_TAC o Q.SPECL [`~r`,`z`,`1`]) REAL_LE_RMUL_IMP
       >> RW_TAC real_ss [REAL_NEG_GE0, REAL_LT_IMP_LE])
   >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
   >> FULL_SIMP_TAC std_ss [GSYM real_lt]
   >> `?q. y < q /\ q < r` by (MATCH_MP_TAC REAL_MEAN >> RW_TAC std_ss [])
   >> `0 < r` by METIS_TAC [REAL_LT_TRANS]
   >> `q / r < 1` by (RW_TAC real_ss [REAL_LT_LDIV_EQ])
   >> `0 < q / r` by METIS_TAC [REAL_LT_DIV, REAL_LT_TRANS]
   >> Q.PAT_X_ASSUM `!z. P z` (MP_TAC o Q.SPEC `q/r`)
   >> RW_TAC std_ss [REAL_DIV_RMUL, REAL_LT_IMP_NE, GSYM real_lt]);

val mono_conv_outgrow = prove
  (``!(x:num->real) y (z:real). (!(a:num) b. a <= b ==> x a <= x b) /\ x --> y /\ z < y ==>
                (?(b:num). !a. b <= a ==> z < x a)``,
   rpt STRIP_TAC
   >> `0 < y - z` by RW_TAC real_ss [REAL_LT_SUB_LADD]
   >> `?n. !m. n <= m ==> abs (x m + ~y) < y-z`
        by FULL_SIMP_TAC std_ss [SEQ, GSYM real_sub, GREATER_EQ]
   >> `!m. x m <= y`
        by (STRIP_TAC >> MATCH_MP_TAC SEQ_MONO_LE >> RW_TAC real_ss [])
   >> `!m. abs (x m + ~y) = y - x m`
        by (RW_TAC std_ss [abs]
            >- (FULL_SIMP_TAC real_ss [GSYM real_sub, REAL_LE_SUB_LADD]
                >> METIS_TAC [REAL_SUB_REFL, REAL_LE_ANTISYM])
            >> REAL_ARITH_TAC)
   >> `!m. y - x m + z = (y + z) - x m` by (STRIP_TAC >> REAL_ARITH_TAC)
   >> FULL_SIMP_TAC std_ss [REAL_LT_SUB_LADD, REAL_LT_SUB_RADD, REAL_LT_LADD]
   >> Q.EXISTS_TAC `n` >> RW_TAC std_ss []);

val psfis_mono_conv_mono = store_thm
  ("psfis_mono_conv_mono",
  ``!m f u x y r s.
        measure_space m /\
        mono_convergent u f (m_space m) /\
        (!n. x n IN psfis m (u n)) /\
        (!m n. m <= n ==> x m <= x n) /\
        x --> y /\ r IN psfis m s /\
        (!a. a IN m_space m ==> s a <= f a) ==> r <= y``,
   rpt STRIP_TAC
   >> MATCH_MP_TAC real_le_mult_sustain
   >> rpt STRIP_TAC
   >> (MP_TAC o Q.SPECL [`m`, `r`, `s`]) (GSYM IN_psfis)
   >> RW_TAC std_ss [pos_simple_fn_integral_def]
   >> Q.ABBREV_TAC `B' = (\n:num. {w | w IN m_space m /\ z * s w <= u n w})`
   >> `!n. B' n IN measurable_sets m`
        by (Q.UNABBREV_TAC `B'` >> RW_TAC std_ss []
            >> `!w. z * s w = (\w. z * s w) w` by RW_TAC std_ss [] >> POP_ORW
            >> MATCH_MP_TAC borel_measurable_leq_borel_measurable
            >> RW_TAC std_ss []
            >- (`!w. z = (\w. z) w` by RW_TAC std_ss [] >> POP_ORW
                >> MATCH_MP_TAC borel_measurable_times_borel_measurable
                >> RW_TAC std_ss []
                >- (MATCH_MP_TAC borel_measurable_const >> FULL_SIMP_TAC std_ss [measure_space_def])
                >> MATCH_MP_TAC psfis_borel_measurable
                >> Q.EXISTS_TAC `SIGMA (\i. x' i * measure m (a i)) s'` >> RW_TAC std_ss [])
            >> MATCH_MP_TAC psfis_borel_measurable
            >> Q.EXISTS_TAC `x n` >> RW_TAC std_ss [])
   >> `!n. (z * (SIGMA (\i. x' i * measure m (a i INTER B' n)) s') <= x n) /\
           (!i. i IN s' ==> (a i INTER B' n) IN measurable_sets m)`
        by (STRIP_TAC >> ONCE_REWRITE_TAC [CONJ_SYM] >> STRONG_CONJ_TAC
            >- (rpt STRIP_TAC >> FULL_SIMP_TAC std_ss [pos_simple_fn_def]
                >> `measurable_sets m = subsets (m_space m, measurable_sets m)` by RW_TAC std_ss [subsets_def]
                >> POP_ORW
                >> MATCH_MP_TAC ALGEBRA_INTER
                >> FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def, subsets_def])
            >> STRIP_TAC >> (MP_TAC o Q.SPECL [`m`, `(x:num->real) n`, `(u :num -> 'a -> real) n`]) (GSYM IN_psfis)
            >> RW_TAC std_ss [pos_simple_fn_integral_def]
            >> Q.PAT_X_ASSUM `pos_simple_fn m s s' a x'` MP_TAC
            >> RW_TAC std_ss [pos_simple_fn_def]
            >> MATCH_MP_TAC psfis_mono
            >> Q.EXISTS_TAC `m`
            >> Q.EXISTS_TAC `(\t. z * (\t. SIGMA (\i. x' i * indicator_fn (a i INTER B' n) t) s') t)`
            >> Q.EXISTS_TAC `u n`
            >> CONJ_TAC >- ASM_REWRITE_TAC []
            >> CONJ_TAC
            >- (Suff `SIGMA (\i. x' i * measure m (a i INTER B' n)) s' IN
                      psfis m (\t. SIGMA (\i. x' i * indicator_fn (a i INTER B' n) t) s')`
                >- METIS_TAC [REAL_LT_IMP_LE, psfis_mult]
                >> `!t i. a i INTER B' n = (\i. a i INTER B' n) i` by RW_TAC std_ss []
                >> POP_ORW
                >> MATCH_MP_TAC psfis_intro
                >> RW_TAC std_ss [])
            >> RW_TAC std_ss []
            >> `!i. (x' i * indicator_fn (a i INTER B' n) x''' =
                       indicator_fn (B' n) x''' * (\i.(x' i  * indicator_fn (a i) x''')) i)`
                        by (RW_TAC real_ss [indicator_fn_def, IN_INTER] >> FULL_SIMP_TAC bool_ss [DE_MORGAN_THM])
            >> POP_ORW
            >> ASM_SIMP_TAC std_ss [REAL_SUM_IMAGE_CMUL]
            >> Cases_on `x''' IN m_space m`
            >- (`SIGMA (\i. x' i * indicator_fn (a i) x''') s' = s x'''` by METIS_TAC []
                >> POP_ORW
                >> Q.UNABBREV_TAC `B'`
                >> SIMP_TAC real_ss [indicator_fn_def, GSPECIFICATION]
                >> RW_TAC real_ss []
                >> METIS_TAC [nonneg_def, psfis_nonneg])
            >> (MP_TAC o Q.SPECL [`(\i. x' i * indicator_fn (a i) x''')`, `0`]
                o UNDISCH o Q.ISPEC `s':num->bool`) REAL_SUM_IMAGE_FINITE_CONST2
            >> RW_TAC real_ss [REAL_SUM_IMAGE_0]
            >> Suff `(!y. y IN s' ==> (x' y * indicator_fn (a y) x''' = 0))`
            >- (ASM_SIMP_TAC real_ss [] >> METIS_TAC [nonneg_def, psfis_nonneg])
            >> RW_TAC std_ss [REAL_ENTIRE, indicator_fn_def]
            >> Cases_on `x' y' = 0` >> RW_TAC real_ss []
            >> FULL_SIMP_TAC std_ss [measure_space_def, SIGMA_ALGEBRA, subset_class_def, space_def, subsets_def, SUBSET_DEF]
            >> METIS_TAC [])
   >> MATCH_MP_TAC SEQ_LE
   >> Q.EXISTS_TAC `(\n. ((\n. z) n) * (\n. SIGMA (\i. x' i * measure m (a i INTER B' n)) s') n)`
   >> Q.EXISTS_TAC `x`
   >> reverse CONJ_TAC
   >- (ASM_REWRITE_TAC [GREATER_EQ] >> Q.EXISTS_TAC `0` >> RW_TAC arith_ss [])
   >> MATCH_MP_TAC SEQ_MUL
   >> RW_TAC std_ss [SEQ_CONST]
   >> FULL_SIMP_TAC std_ss [pos_simple_fn_def]
   >> `!n. (\i. x' i * measure m (a i INTER B' n)) =
           (\n i. x' i * measure m (a i INTER B' n)) n` by RW_TAC std_ss []
   >> POP_ORW
   >> (MATCH_MP_TAC o UNDISCH o Q.ISPEC `s':num->bool`) SEQ_REAL_SUM_IMAGE
   >> RW_TAC std_ss []
   >> `(\n. x' x'' * measure m (a x'' INTER B' n)) =
        (\n. (\n. x' x'') n * (\n. measure m (a x'' INTER B' n)) n)` by RW_TAC std_ss []
   >> POP_ORW >> MATCH_MP_TAC SEQ_MUL
   >> RW_TAC std_ss [SEQ_CONST]
   >> `(\n. measure m (a x'' INTER B' n)) =
       measure m o (\n. a x'' INTER B' n)`
        by RW_TAC std_ss [o_DEF]
   >> POP_ORW
   >> MATCH_MP_TAC MONOTONE_CONVERGENCE
   >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, SUBSET_DEF, IN_INTER]
   >- (Q.PAT_X_ASSUM `!t.
         t IN m_space m ==>
         (s t = SIGMA (\i. x' i * indicator_fn (a i) t) s')` (K ALL_TAC)
       >> Q.UNABBREV_TAC `B'`
       >> FULL_SIMP_TAC std_ss [GSPECIFICATION, mono_convergent_def]
       >> MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `u n x'''`
       >> RW_TAC arith_ss [])
   >> Q.UNABBREV_TAC `B'` >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_UNIV, GSPECIFICATION, IN_INTER]
   >> Suff `x''' IN a x'' ==> x''' IN m_space m /\ (?n. z * s x''' <= u n x''')`
   >- METIS_TAC []
   >> STRIP_TAC
   >> STRONG_CONJ_TAC
   >- (FULL_SIMP_TAC std_ss [measure_space_def, SIGMA_ALGEBRA, subset_class_def, space_def, subsets_def, SUBSET_DEF]
       >> METIS_TAC [])
   >> Cases_on `s x''' = 0`
   >- (RW_TAC real_ss [] >> METIS_TAC [nonneg_def, psfis_nonneg])
   >> STRIP_TAC
   >> `0 < s x'''` by METIS_TAC [REAL_LT_LE, psfis_nonneg, nonneg_def]
   >> `z * s x''' < 1 * s x'''` by (MATCH_MP_TAC REAL_LT_RMUL_IMP >> RW_TAC real_ss [REAL_LT_IMP_LE])
   >> `z * s x''' < f x'''` by METIS_TAC [REAL_LTE_TRANS, REAL_MUL_LID]
   >> (MP_TAC o Q.SPECL [`(\n. u n x''')`, `f x'''`, `z * s x'''`]) mono_conv_outgrow
   >> FULL_SIMP_TAC std_ss [mono_convergent_def]
   >> RW_TAC std_ss []
   >> METIS_TAC [LESS_EQ_REFL, REAL_LT_IMP_LE]);

val psfis_nnfis = store_thm
  ("psfis_nnfis",
  ``!m f a. measure_space m /\ a IN psfis m f ==> a IN nnfis m f``,
   RW_TAC std_ss [nnfis_def, GSPECIFICATION]
   >> Q.EXISTS_TAC `(\n. f)` >> Q.EXISTS_TAC `(\n. a)`
   >> RW_TAC real_ss [SEQ_CONST, mono_convergent_def]);

val nnfis_times = store_thm
  ("nnfis_times",
  ``!f m a z. measure_space m /\ a IN nnfis m f /\ 0 <= z ==>
             (z * a) IN nnfis m (\w. z * f w)``,
   RW_TAC std_ss [nnfis_def, GSPECIFICATION]
   >> Q.EXISTS_TAC `(\n w. z * u n w)` >> Q.EXISTS_TAC `(\n. z * x n)`
   >> CONJ_TAC
   >- (RW_TAC std_ss [mono_convergent_def]
       >- (MATCH_MP_TAC REAL_LE_MUL2
           >> FULL_SIMP_TAC real_ss [mono_convergent_def, REAL_LT_IMP_LE]
           >> METIS_TAC [nonneg_def, psfis_nonneg])
       >> `(\n. z * u n w) = (\n. (\n. z) n * (\n. u n w) n)`
                by RW_TAC std_ss []
       >> POP_ORW
       >> MATCH_MP_TAC SEQ_MUL
       >> FULL_SIMP_TAC std_ss [SEQ_CONST, mono_convergent_def])
   >> CONJ_TAC >- METIS_TAC [psfis_mult]
   >> `(\n. z * x n) = (\n. (\n. z) n * (\n. x n) n)`
        by RW_TAC std_ss []
   >> POP_ORW
   >> MATCH_MP_TAC SEQ_MUL
   >> FULL_SIMP_TAC std_ss [SEQ_CONST, ETA_THM]);

val nnfis_add = store_thm
  ("nnfis_add",
  ``!f g m a b. measure_space m /\ a IN nnfis m f /\ b IN nnfis m g ==>
               (a + b) IN nnfis m (\w. f w + g w)``,
   RW_TAC std_ss [nnfis_def, GSPECIFICATION]
   >> Q.EXISTS_TAC `(\n w. u n w + u' n w)` >> Q.EXISTS_TAC `(\n. x n + x' n)`
   >> CONJ_TAC
   >- (RW_TAC std_ss [mono_convergent_def]
       >- (MATCH_MP_TAC REAL_LE_ADD2
           >> FULL_SIMP_TAC real_ss [mono_convergent_def])
       >> `(\n. u n w + u' n w) = (\n. (\n. u n w) n + (\n. u' n w) n)`
                by RW_TAC std_ss []
       >> POP_ORW
       >> MATCH_MP_TAC SEQ_ADD
       >> FULL_SIMP_TAC std_ss [mono_convergent_def])
   >> CONJ_TAC >- METIS_TAC [psfis_add]
   >> RW_TAC std_ss []
   >> RW_TAC std_ss [SEQ_ADD]);

val nnfis_mono = store_thm
  ("nnfis_mono",
  ``!f g m a b. measure_space m /\ a IN nnfis m f /\ b IN nnfis m g /\
               (!w. w IN m_space m ==> f w <= g w) ==> a <= b``,
   RW_TAC std_ss [nnfis_def, GSPECIFICATION]
   >> `!n x. x IN m_space m ==> u n x <= f x`
        by (rpt STRIP_TAC >> FULL_SIMP_TAC std_ss [mono_convergent_def]
            >> `u n x'' = (\n. u n x'') n` by RW_TAC std_ss []
            >> POP_ORW
            >> MATCH_MP_TAC SEQ_MONO_LE
            >> RW_TAC std_ss [DECIDE ``!(n:num). n <= n + 1``])
   >> `!n x. x IN m_space m ==> u n x <= g x`
        by METIS_TAC [REAL_LE_TRANS]
   >> `!n. x n <= b`
        by (STRIP_TAC >> MATCH_MP_TAC psfis_mono_conv_mono
            >> Q.EXISTS_TAC `m` >> Q.EXISTS_TAC `g` >> Q.EXISTS_TAC `u'`
            >> Q.EXISTS_TAC `x'` >> Q.EXISTS_TAC `u n`
            >> FULL_SIMP_TAC real_ss [mono_convergent_def]
            >> rpt STRIP_TAC >> MATCH_MP_TAC psfis_mono
            >> Q.EXISTS_TAC `m` >> Q.EXISTS_TAC `u' m'` >> Q.EXISTS_TAC `u' n`
            >> RW_TAC std_ss [])
   >> MATCH_MP_TAC SEQ_LE_IMP_LIM_LE
   >> Q.EXISTS_TAC `x` >> RW_TAC std_ss []);

val nnfis_unique = store_thm
  ("nnfis_unique",
  ``!f m a b. measure_space m /\ a IN nnfis m f /\ b IN nnfis m f ==> (a = b)``,
   rpt STRIP_TAC
   >> ONCE_REWRITE_TAC [GSYM REAL_LE_ANTISYM]
   >> CONJ_TAC >> MATCH_MP_TAC nnfis_mono
   >> Q.EXISTS_TAC `f` >> Q.EXISTS_TAC `f` >> Q.EXISTS_TAC `m`
   >> RW_TAC std_ss [REAL_LE_REFL]);

val psfis_equiv = store_thm
  ("psfis_equiv",
  ``!f g a m. measure_space m /\ a IN psfis m f /\
               (!t. 0 <= g t) /\ (!t. t IN m_space m ==> (f t = g t)) ==>
        a IN psfis m g``,
    rpt STRIP_TAC
    >> (MP_TAC o Q.SPECL [`m`, `a`, `f`]) IN_psfis
    >> RW_TAC std_ss []
    >> RW_TAC std_ss [psfis_def, IN_IMAGE]
    >> Q.EXISTS_TAC `(s, a', x)`
    >> RW_TAC std_ss [psfs_def, GSPECIFICATION]
    >> Q.EXISTS_TAC `(s, a', x)`
    >> RW_TAC std_ss []
    >> FULL_SIMP_TAC std_ss [pos_simple_fn_def]);

val upclose_psfis = store_thm
  ("upclose_psfis",
  ``!f g a b m. measure_space m /\ a IN psfis m f /\ b IN psfis m g ==>
               (?c. c IN psfis m (upclose f g))``,
   rpt STRIP_TAC
   >> (MP_TAC o Q.SPECL [`m`, `f`, `g`, `a`, `b`]) psfis_present
   >> RW_TAC std_ss [upclose_def]
   >> Q.EXISTS_TAC `REAL_SUM_IMAGE (\i.max (z i) (z' i) * measure m (c i)) k`
   >> MATCH_MP_TAC psfis_equiv
   >> Q.EXISTS_TAC `(\t. REAL_SUM_IMAGE (\i.max (z i) (z' i) * indicator_fn (c i) t) k)`
   >> RW_TAC std_ss [REAL_LE_MAX]
   >| [`!t i. max (z i) (z' i) = (\i. max (z i) (z' i)) i` by RW_TAC std_ss []
       >> POP_ORW >> MATCH_MP_TAC psfis_intro
       >> RW_TAC std_ss [REAL_LE_MAX],
       METIS_TAC [psfis_nonneg, nonneg_def],
       Cases_on `?i. i IN k /\ t IN (c i)`
       >- (FULL_SIMP_TAC std_ss []
           >> `k = i INSERT k`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INSERT] >> METIS_TAC [])
           >> POP_ORW
           >> RW_TAC std_ss [REAL_SUM_IMAGE_THM, FINITE_INSERT]
           >> `FINITE (k DELETE i)` by RW_TAC std_ss [FINITE_DELETE]
           >> (MP_TAC o REWRITE_RULE [IN_DELETE, REAL_ENTIRE]
                o Q.SPECL [`\i. max (z i) (z' i) * indicator_fn (c i) t`, `0`] o UNDISCH
                o Q.SPEC `k DELETE i` o INST_TYPE [``:'a``|->``:num``]) REAL_SUM_IMAGE_FINITE_CONST2
           >> RW_TAC real_ss []
           >> `SIGMA (\i. max (z i) (z' i) * indicator_fn (c i) t) (k DELETE i) = 0`
                by (POP_ASSUM MATCH_MP_TAC
                    >> RW_TAC real_ss [indicator_fn_def, REAL_ENTIRE]
                    >> METIS_TAC [IN_DISJOINT])
           >> POP_ORW >> POP_ASSUM (K ALL_TAC)
           >> (MP_TAC o REWRITE_RULE [IN_DELETE, REAL_ENTIRE]
                o Q.SPECL [`\i. z i * indicator_fn (c i) t`, `0`] o UNDISCH
                o Q.SPEC `k DELETE i` o INST_TYPE [``:'a``|->``:num``]) REAL_SUM_IMAGE_FINITE_CONST2
           >> RW_TAC real_ss []
           >> `SIGMA (\i. z i * indicator_fn (c i) t) (k DELETE i) = 0`
                by (POP_ASSUM MATCH_MP_TAC
                    >> RW_TAC real_ss [indicator_fn_def, REAL_ENTIRE]
                    >> METIS_TAC [IN_DISJOINT])
           >> POP_ORW >> POP_ASSUM (K ALL_TAC)
           >> (MP_TAC o REWRITE_RULE [IN_DELETE, REAL_ENTIRE]
                o Q.SPECL [`\i. z' i * indicator_fn (c i) t`, `0`] o UNDISCH
                o Q.SPEC `k DELETE i` o INST_TYPE [``:'a``|->``:num``]) REAL_SUM_IMAGE_FINITE_CONST2
           >> RW_TAC real_ss []
           >> `SIGMA (\i. z' i * indicator_fn (c i) t) (k DELETE i) = 0`
                by (POP_ASSUM MATCH_MP_TAC
                    >> RW_TAC real_ss [indicator_fn_def, REAL_ENTIRE]
                    >> METIS_TAC [IN_DISJOINT])
           >> POP_ORW >> POP_ASSUM (K ALL_TAC)
           >> RW_TAC real_ss [indicator_fn_def])
   >> FULL_SIMP_TAC std_ss []
   >> (MP_TAC o REWRITE_RULE [IN_DELETE, REAL_ENTIRE]
                o Q.SPECL [`\i. max (z i) (z' i) * indicator_fn (c i) t`, `0`] o UNDISCH
                o Q.SPEC `k` o INST_TYPE [``:'a``|->``:num``]) REAL_SUM_IMAGE_FINITE_CONST2
   >> RW_TAC real_ss []
   >> `SIGMA (\i. max (z i) (z' i) * indicator_fn (c i) t) k = 0`
        by (POP_ASSUM MATCH_MP_TAC
            >> RW_TAC real_ss [indicator_fn_def, REAL_ENTIRE]
            >> METIS_TAC [IN_DISJOINT])
   >> POP_ORW >> POP_ASSUM (K ALL_TAC)
   >> (MP_TAC o REWRITE_RULE [IN_DELETE, REAL_ENTIRE]
                o Q.SPECL [`\i. z i * indicator_fn (c i) t`, `0`] o UNDISCH
                o Q.SPEC `k` o INST_TYPE [``:'a``|->``:num``]) REAL_SUM_IMAGE_FINITE_CONST2
   >> RW_TAC real_ss []
   >> `SIGMA (\i. z i * indicator_fn (c i) t) k = 0`
        by (POP_ASSUM MATCH_MP_TAC
            >> RW_TAC real_ss [indicator_fn_def, REAL_ENTIRE]
            >> METIS_TAC [IN_DISJOINT])
   >> POP_ORW >> POP_ASSUM (K ALL_TAC)
   >> (MP_TAC o REWRITE_RULE [IN_DELETE, REAL_ENTIRE]
                o Q.SPECL [`\i. (z' i) * indicator_fn (c i) t`, `0`] o UNDISCH
                o Q.SPEC `k` o INST_TYPE [``:'a``|->``:num``]) REAL_SUM_IMAGE_FINITE_CONST2
   >> RW_TAC real_ss []
   >> `SIGMA (\i. (z' i) * indicator_fn (c i) t) k = 0`
        by (POP_ASSUM MATCH_MP_TAC
            >> RW_TAC real_ss [indicator_fn_def, REAL_ENTIRE]
            >> METIS_TAC [IN_DISJOINT])
   >> POP_ORW >> POP_ASSUM (K ALL_TAC)
   >> RW_TAC real_ss []]);

val mon_upclose_psfis = store_thm
  ("mon_upclose_psfis",
  ``!m u. measure_space m /\ (!(n:num) (n':num). ?a. a IN psfis m (u n n')) ==>
         (?c. !(n:num). (c n) IN psfis m (mon_upclose u n))``,
   rpt STRIP_TAC
   >> `!(n':num) (n:num). ?c. c IN psfis m (mon_upclose_help n u n')`
        by (STRIP_TAC >> Induct
            >> RW_TAC std_ss [mon_upclose_help_def]
            >> MATCH_MP_TAC upclose_psfis
            >> METIS_TAC [])
   >> RW_TAC std_ss [mon_upclose_def]
   >> Q.ABBREV_TAC `P = (\n c. c IN psfis m (mon_upclose_help n u n))`
   >> Q.EXISTS_TAC `(\n. @c. P n c)`
   >> RW_TAC std_ss []
   >> Suff `P n (@c. P n c)` >- METIS_TAC []
   >> Q.ABBREV_TAC `P' = P n`
   >> RW_TAC std_ss [SELECT_THM]
   >> Q.UNABBREV_TAC `P'` >> Q.UNABBREV_TAC `P`
   >> RW_TAC std_ss []);

val mon_upclose_help_lemma = prove
  (``!f u h s. (!n. mono_convergent (\m. u m n) (f n) s) /\
               (!m n x. x IN s ==> 0 <= u m n x) /\
               mono_convergent f h s ==>
                   mono_convergent (mon_upclose u) h s /\
                   (!n x. x IN s ==> mon_upclose u n x <= f n x)``,
   NTAC 5 STRIP_TAC
   >> ONCE_REWRITE_TAC [CONJ_SYM]
   >> STRONG_CONJ_TAC
   >- (RW_TAC std_ss [mon_upclose_def]
       >> Suff `!m. mon_upclose_help n u m x <= f n x`
       >- RW_TAC std_ss []
       >> Induct_on `n`
       >- (RW_TAC std_ss [mon_upclose_help_def]
           >> FULL_SIMP_TAC std_ss [mono_convergent_def]
           >> `u m 0 x = (\m. u m 0 x) m` by RW_TAC std_ss []
           >> POP_ORW >> MATCH_MP_TAC SEQ_MONO_LE
           >> RW_TAC arith_ss [])
       >> RW_TAC std_ss [mon_upclose_help_def, upclose_def, REAL_MAX_LE]
       >- (`u m (SUC n) x = (\m. u m (SUC n) x) m` by RW_TAC std_ss []
           >> POP_ORW >> MATCH_MP_TAC SEQ_MONO_LE
           >> FULL_SIMP_TAC arith_ss [mono_convergent_def])
       >> MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `f n x`
       >> FULL_SIMP_TAC arith_ss [mono_convergent_def])
   >> STRIP_TAC
   >> `!t m n n'. t IN s /\ n <= n' ==> mon_upclose_help n u m t <= mon_upclose_help n' u m t`
        by (RW_TAC std_ss [mon_upclose_help_def, upclose_def, REAL_LE_MAX, REAL_LE_REFL]
            >> Suff `!n' n. n <= n' ==> mon_upclose_help n u m t <= mon_upclose_help n' u m t`
            >- RW_TAC std_ss []
            >> Induct >- RW_TAC arith_ss [REAL_LE_REFL]
            >> RW_TAC arith_ss [DECIDE ``!(m:num) n. m <= SUC n <=> (m = SUC n) \/ m <= n``]
            >> RW_TAC real_ss []
            >> MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `mon_upclose_help n'' u m t`
            >> RW_TAC arith_ss [REAL_LE_REFL]
            >> ASM_SIMP_TAC arith_ss []
            >> RW_TAC real_ss [mon_upclose_help_def, upclose_def])
   >> `!t m m' n. t IN s /\ m <= m' ==> u m n t <= u m' n t`
        by FULL_SIMP_TAC arith_ss [mono_convergent_def]
   >> `!t n n'. t IN s /\ n <= n' ==> mon_upclose u n t <= mon_upclose u n' t`
        by (rpt STRIP_TAC
            >> `!m m'. m <= m' ==> mon_upclose_help n u m t <= mon_upclose_help n u m' t`
                by (Induct_on `n`
                    >- FULL_SIMP_TAC real_ss [mon_upclose_help_def, mono_convergent_def]
                    >> RW_TAC real_ss [mon_upclose_help_def, upclose_def]
                    >> MATCH_MP_TAC REAL_IMP_MAX_LE2 >> RW_TAC std_ss [DECIDE ``!(n:num) m. SUC n <= m ==> n <= m``])
            >> RW_TAC std_ss [mon_upclose_def] >> METIS_TAC [REAL_LE_TRANS, REAL_LE_REFL])
    >> `!t n n'. t IN s /\ n <= n' ==> mon_upclose_help n u n t <= mon_upclose_help n' u n' t`
        by METIS_TAC [mon_upclose_def]
    >> `!t n. t IN s ==>  mon_upclose u n t <= h t`
        by (rpt STRIP_TAC >> MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `f n t`
            >> RW_TAC std_ss [] >> `f n t = (\n. f n t) n` by RW_TAC std_ss []
            >> POP_ORW >> MATCH_MP_TAC SEQ_MONO_LE
            >> FULL_SIMP_TAC arith_ss [mono_convergent_def])
    >> RW_TAC std_ss [mono_convergent_def]
    >> `!n. 0 <= mon_upclose u n x`
        by (STRIP_TAC >> MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `mon_upclose u 0 x`
            >> ASM_SIMP_TAC arith_ss [] >> RW_TAC std_ss [mon_upclose_def, mon_upclose_help_def])
    >> `convergent (\i. mon_upclose u i x)`
        by (MATCH_MP_TAC SEQ_ICONV
            >> CONJ_TAC
            >- (MATCH_MP_TAC SEQ_BOUNDED_2 >> Q.EXISTS_TAC `0` >> Q.EXISTS_TAC `h x`
                >> RW_TAC std_ss [])
            >> RW_TAC std_ss [GREATER_EQ, real_ge])
    >> FULL_SIMP_TAC std_ss [convergent]
    >> `l <= h x`
        by (MATCH_MP_TAC SEQ_LE_IMP_LIM_LE >> Q.EXISTS_TAC `(\i. mon_upclose u i x)` >> RW_TAC std_ss [])
    >> Suff `h x <= l` >- METIS_TAC [REAL_LE_ANTISYM]
    >> Suff `!n. f n x <= l`
    >- (FULL_SIMP_TAC std_ss [mono_convergent_def]
        >> STRIP_TAC >> MATCH_MP_TAC SEQ_LE_IMP_LIM_LE >> Q.EXISTS_TAC `(\i. f i x)` >> RW_TAC std_ss [])
    >> STRIP_TAC >> FULL_SIMP_TAC std_ss [mono_convergent_def]
    >> MATCH_MP_TAC SEQ_LE >> Q.EXISTS_TAC `(\m. u m n x)` >> Q.EXISTS_TAC `(\i. mon_upclose u i x)`
    >> RW_TAC std_ss [real_ge, GREATER_EQ]
    >> Suff `!n m. n <= m ==> u m n x <= mon_upclose u m x`
    >- (STRIP_TAC >> Q.EXISTS_TAC `n` >> RW_TAC std_ss [])
    >> RW_TAC std_ss [mon_upclose_def]
    >> MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `mon_upclose_help n u m x`
    >> RW_TAC std_ss []
    >> Induct_on `n` >- RW_TAC real_ss [mon_upclose_help_def]
    >> RW_TAC real_ss [mon_upclose_help_def, upclose_def]);

(* Beppo-Levi monotone convergence theorem *)
val nnfis_mon_conv = store_thm
  ("nnfis_mon_conv",
  ``!f m h x y. measure_space m /\ mono_convergent f h (m_space m) /\
                (!n. x n IN nnfis m (f n)) /\ x --> y ==>
                y IN nnfis m h``,
   rpt STRIP_TAC
   >> Q.ABBREV_TAC `u = (\n. @u. mono_convergent u (f n) (m_space m) /\
                             (!n'. ?a. a IN psfis m (u n')))`
   >> Q.ABBREV_TAC `urev = (\m n. u n m)`
   >> (MP_TAC o Q.SPECL [`f`, `urev`, `h`, `m_space m`]) mon_upclose_help_lemma
   >> ASM_SIMP_TAC std_ss []
   >> Q.ABBREV_TAC `P = \n u. mono_convergent u (f n) (m_space m) /\
                              !n'. ?a. a IN psfis m (u n')`
   >> `(!n. P n (@u. P n u)) ==>
        (!n. mono_convergent (\m. urev m n) (f n) (m_space m)) /\
        (!m' n x. x IN m_space m ==> 0 <= urev m' n x) /\
        (!n n'. ?a. a IN psfis m (urev n n'))`
        by (RW_TAC std_ss []
            >| [POP_ASSUM (MP_TAC o Q.SPEC `n`)
                >> Q.UNABBREV_TAC `P`
                >> Q.UNABBREV_TAC `urev`
                >> Q.UNABBREV_TAC `u`
                >> METIS_TAC [],
                Q.PAT_X_ASSUM `!n. P n @u. P n u` (MP_TAC o Q.SPEC `n`)
                >> Q.UNABBREV_TAC `P`
                >> Q.UNABBREV_TAC `urev`
                >> Q.UNABBREV_TAC `u`
                >> METIS_TAC [psfis_nonneg, nonneg_def],
                Q.PAT_X_ASSUM `!n. P n @u. P n u` (MP_TAC o Q.SPEC `n'`)
                >> Q.UNABBREV_TAC `P`
                >> Q.UNABBREV_TAC `urev`
                >> Q.UNABBREV_TAC `u`
                >> RW_TAC std_ss []
                >> METIS_TAC []])
   >> `!n. P n @u. P n u`
        by (STRIP_TAC >> Q.ABBREV_TAC `P' = P n` >> RW_TAC std_ss [SELECT_THM]
            >> Q.UNABBREV_TAC `P'` >> Q.UNABBREV_TAC `P`
            >> RW_TAC std_ss []
            >> Q.PAT_X_ASSUM `!n. x n IN nnfis m (f n)` (MP_TAC o Q.SPEC `n`)
            >> RW_TAC std_ss [nnfis_def, GSPECIFICATION]
            >> Q.EXISTS_TAC `u'`
            >> RW_TAC std_ss []
            >> Q.EXISTS_TAC `x' n'`
            >> RW_TAC std_ss [])
   >> FULL_SIMP_TAC std_ss []
   >> POP_ASSUM (K ALL_TAC) >> Q.UNABBREV_TAC `P`
   >> STRIP_TAC
   >> (MP_TAC o Q.SPECL [`m`, `urev`]) mon_upclose_psfis
   >> ASM_SIMP_TAC std_ss []
   >> STRIP_TAC
   >> `!n'. c n' IN nnfis m (mon_upclose urev n')` by RW_TAC std_ss [psfis_nnfis]
   >> `!n'. c n' <= x n'`
        by (STRIP_TAC >> MATCH_MP_TAC nnfis_mono
            >> Q.EXISTS_TAC `(mon_upclose urev n')` >> Q.EXISTS_TAC `f n'` >> Q.EXISTS_TAC `m`
            >> RW_TAC std_ss [])
   >> `!n n'. n <= n' ==> c n <= c n'`
        by (RW_TAC std_ss [] >> MATCH_MP_TAC psfis_mono
            >> Q.EXISTS_TAC `m` >> Q.EXISTS_TAC `mon_upclose urev n` >> Q.EXISTS_TAC `mon_upclose urev n'`
            >> RW_TAC std_ss [] >> FULL_SIMP_TAC std_ss [mono_convergent_def])
   >> `!n. c n <= y`
        by (STRIP_TAC >> MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `x n`
            >> ASM_REWRITE_TAC [] >> MATCH_MP_TAC SEQ_MONO_LE
            >> RW_TAC arith_ss []
            >> MATCH_MP_TAC nnfis_mono >> Q.EXISTS_TAC `f n` >> Q.EXISTS_TAC `f (n+1)` >> Q.EXISTS_TAC `m`
            >> FULL_SIMP_TAC arith_ss [mono_convergent_def])
   >> `convergent c`
        by (MATCH_MP_TAC SEQ_ICONV
            >> CONJ_TAC
            >- (MATCH_MP_TAC SEQ_BOUNDED_2 >> Q.EXISTS_TAC `0` >> Q.EXISTS_TAC `y` \\
                METIS_TAC [pos_psfis])
            >> RW_TAC std_ss [GREATER_EQ, real_ge])
    >> FULL_SIMP_TAC std_ss [convergent]
    >> `l <= y`
        by (MATCH_MP_TAC SEQ_LE_IMP_LIM_LE >> Q.EXISTS_TAC `c` >> RW_TAC std_ss [])
    >> `l IN nnfis m h`
        by (RW_TAC std_ss [nnfis_def, GSPECIFICATION]
            >> Q.EXISTS_TAC `(mon_upclose urev)` >> Q.EXISTS_TAC `c`
            >> RW_TAC std_ss [])
    >> Suff `y <= l` >- METIS_TAC [REAL_LE_ANTISYM]
    >> Suff `!n. x n <= l`
    >- (STRIP_TAC >> MATCH_MP_TAC SEQ_LE_IMP_LIM_LE >> Q.EXISTS_TAC `x` >> RW_TAC std_ss [])

    >> STRIP_TAC >> MATCH_MP_TAC nnfis_mono
    >> Q.EXISTS_TAC `f n` >> Q.EXISTS_TAC `h` >> Q.EXISTS_TAC `m`
    >> RW_TAC std_ss []
    >> `f n w = (\n. f n w) n` by RW_TAC std_ss [] >> POP_ORW
    >> MATCH_MP_TAC SEQ_MONO_LE
    >> FULL_SIMP_TAC std_ss [mono_convergent_def]);

val nnfis_pos_on_mspace = store_thm
  ("nnfis_pos_on_mspace",
  ``!f m a. measure_space m /\ a IN nnfis m f ==> (!x. x IN m_space m ==> 0 <= f x)``,
   RW_TAC std_ss [nonneg_def, nnfis_def, GSPECIFICATION]
   >> `!n. nonneg (u n)` by METIS_TAC [psfis_nonneg]
   >> MATCH_MP_TAC LE_SEQ_IMP_LE_LIM
   >> Q.EXISTS_TAC `(\n. u n x')`
   >> FULL_SIMP_TAC std_ss [nonneg_def, mono_convergent_def]);

val nnfis_borel_measurable = store_thm
  ("nnfis_borel_measurable",
  ``!m f a. measure_space m /\ a IN nnfis m f ==>
            f IN borel_measurable (m_space m, measurable_sets m)``,
   RW_TAC std_ss [nnfis_def, GSPECIFICATION]
   >> MATCH_MP_TAC mono_convergent_borel_measurable
   >> Q.EXISTS_TAC `u` >> RW_TAC std_ss []
   >> MATCH_MP_TAC psfis_borel_measurable
   >> Q.EXISTS_TAC `x n` >> RW_TAC std_ss []);

val SEQ_OFFSET = prove
  (``!f l a. (f o (\n. n + a)) --> l ==> f --> l``,
   STRIP_TAC >> STRIP_TAC >> Induct
   >> RW_TAC arith_ss [o_DEF, ETA_THM]
   >> Q.PAT_X_ASSUM `f o (\n. n + a) --> l ==> f --> l` MATCH_MP_TAC
   >> ONCE_REWRITE_TAC [SEQ_SUC]
   >> RW_TAC arith_ss [o_DEF, ETA_THM]
   >> `!n. a + SUC n = n + SUC a` by (STRIP_TAC >> DECIDE_TAC)
   >> POP_ORW
   >> RW_TAC std_ss []);

val borel_measurable_mon_conv_psfis = store_thm
  ("borel_measurable_mon_conv_psfis",
  ``!m f. measure_space m /\ f IN borel_measurable (m_space m, measurable_sets m) /\
         (!t. t IN m_space m ==> 0 <= f t) ==>
         (?u x. mono_convergent u f (m_space m) /\ (!n. x n IN psfis m (u n)))``,
    rpt STRIP_TAC
 >> Q.ABBREV_TAC `A = (\n i. {w | w IN m_space m /\ & i / (2 pow n) <= f w} INTER
                             {w | w IN m_space m /\ f w < & (SUC i) / (2 pow n)})`
 >> Q.ABBREV_TAC `u = (\n t. REAL_SUM_IMAGE (\i. &i / (2 pow n) * (indicator_fn (A n i) t))
                                            {i:num | 0 < i /\ &i < (&n * 2 pow n)})`
 >> Q.ABBREV_TAC `x = (\n. REAL_SUM_IMAGE (\i. &i / (2 pow n) * measure m (A n i))
                                          {i:num | 0 < i /\ &i < (&n * 2 pow n)})`
 >> Q.EXISTS_TAC `u` >> Q.EXISTS_TAC `x`
 >> `!n. FINITE {i | 0 < i /\ & i < & n * 2 pow n}`
      by (STRIP_TAC \\
         `!i. & i < &n * 2 pow n <=> i < n * 2 ** n`
             by (STRIP_TAC >> `&2 = 2` by RW_TAC real_ss [] >> POP_ORW \\
                 RW_TAC std_ss [REAL_OF_NUM_POW, REAL_MUL, REAL_LT]) >> POP_ORW \\
          (MATCH_MP_TAC o REWRITE_RULE [FINITE_COUNT] o Q.ISPEC `count (n * 2 ** n)`) SUBSET_FINITE \\
          RW_TAC std_ss [SUBSET_DEF, IN_COUNT, GSPECIFICATION])
 >> ONCE_REWRITE_TAC [CONJ_SYM] >> STRONG_CONJ_TAC
 >- (STRIP_TAC
     >> Q.UNABBREV_TAC `u` >> Q.UNABBREV_TAC `x`
     >> RW_TAC std_ss [ETA_THM]
     >> `!n t i. & i / 2 pow n = (\i. & i / 2 pow n) i` by RW_TAC std_ss [] >> POP_ORW
     >> MATCH_MP_TAC psfis_intro
     >> ASM_SIMP_TAC real_ss [POW_POS, REAL_LE_DIV]
     >> Q.UNABBREV_TAC `A`
     >> RW_TAC std_ss [GSPECIFICATION]
     >> `measurable_sets m = subsets (m_space m, measurable_sets m)` by RW_TAC std_ss [subsets_def]
     >> POP_ORW
     >> MATCH_MP_TAC ALGEBRA_INTER >> CONJ_TAC >- FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def]
     >> METIS_TAC [borel_measurable_less_iff, borel_measurable_ge_iff, subsets_def])
 >> STRIP_TAC >> SIMP_TAC std_ss [mono_convergent_def]
 >> `!n t i. &i < (&n * 2 pow n) /\ t IN A n i ==> (u n t = & i / (2 pow n))`
        by (rpt STRIP_TAC
            >> `!j. i <> j ==> ~(t IN A n j)`
                by (rpt STRIP_TAC >> Cases_on `i < j`
                    >- (`f t < & (SUC i) / (2 pow n)` by (Q.UNABBREV_TAC `A` >> FULL_SIMP_TAC std_ss [GSPECIFICATION, IN_INTER])
                        >> `&(SUC i) / (2 pow n) <= &j / (2 pow n)`
                                by (FULL_SIMP_TAC std_ss [LESS_EQ, real_div] >> MATCH_MP_TAC REAL_LE_MUL2
                                    >> RW_TAC real_ss [REAL_LE_INV]
                                    >> `&2 = 2` by RW_TAC real_ss [] >> POP_ORW
                                    >> RW_TAC std_ss [REAL_OF_NUM_POW, REAL_LE_INV, REAL_LE])
                        >> Q.UNABBREV_TAC `A` >> FULL_SIMP_TAC std_ss [GSPECIFICATION, IN_INTER]
                        >> METIS_TAC [REAL_LT_TRANS, REAL_LT_ANTISYM, REAL_LTE_TRANS])
                    >> `j < i` by METIS_TAC [LESS_LESS_CASES]
                    >> `& (SUC j) / (2 pow n) <= &i / (2 pow n)`
                        by (FULL_SIMP_TAC std_ss [LESS_EQ, real_div] >> MATCH_MP_TAC REAL_LE_MUL2
                                    >> RW_TAC real_ss [REAL_LE_INV]
                                    >> `&2 = 2` by RW_TAC real_ss [] >> POP_ORW
                                    >> RW_TAC std_ss [REAL_OF_NUM_POW, REAL_LE_INV, REAL_LE])
                    >> `& i / (2 pow n) <= f t` by (Q.UNABBREV_TAC `A` >> FULL_SIMP_TAC std_ss [GSPECIFICATION, IN_INTER])
                    >> Q.UNABBREV_TAC `A` >> FULL_SIMP_TAC std_ss [GSPECIFICATION, IN_INTER, GSYM real_lt]
                    >> METIS_TAC [REAL_LT_TRANS, REAL_LT_ANTISYM, REAL_LET_TRANS])
            >> `!j. i <> j ==> (indicator_fn (A n j) t = 0)` by RW_TAC real_ss [indicator_fn_def]
            >> Q.UNABBREV_TAC `u`
            >> Cases_on `i = 0`
            >- (RW_TAC real_ss [] >> Q.PAT_X_ASSUM `!n. FINITE P` (ASSUME_TAC o Q.SPEC `n`)
                >> (MP_TAC o REWRITE_RULE [IN_DELETE, REAL_ENTIRE]
                        o Q.SPECL [`\i. & i / 2 pow n * indicator_fn (A n i) t`, `0`] o UNDISCH
                        o Q.SPEC `{i | 0 < i /\ & i < & n * 2 pow n}` o INST_TYPE [``:'a``|->``:num``]) REAL_SUM_IMAGE_FINITE_CONST2
                >> ASM_SIMP_TAC real_ss [DECIDE ``!n:num. 0 < n ==> ~(0 = n)``, GSPECIFICATION])
            >> RW_TAC std_ss []
            >> `{i | 0 < i /\ & i < & n * 2 pow n} = i INSERT {i | 0 < i /\ & i < & n * 2 pow n}`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INSERT, GSPECIFICATION]
                    >> METIS_TAC [DECIDE ``!n:num. 0 < n <=> ~(0 = n)``])
            >> POP_ORW
            >> RW_TAC std_ss [REAL_SUM_IMAGE_THM]
            >> `FINITE ({i | 0 < i /\ & i < & n * 2 pow n} DELETE i)` by RW_TAC std_ss [FINITE_DELETE]
            >> (MP_TAC o REWRITE_RULE [IN_DELETE, REAL_ENTIRE]
                        o Q.SPECL [`\i. & i / 2 pow n * indicator_fn (A n i) t`, `0`] o UNDISCH
                        o Q.SPEC `{i | 0 < i /\ & i < & n * 2 pow n} DELETE i` o INST_TYPE [``:'a``|->``:num``])
                REAL_SUM_IMAGE_FINITE_CONST2
            >> ASM_SIMP_TAC real_ss [DECIDE ``!n:num. 0 < n <=> ~(0 = n)``, GSPECIFICATION, indicator_fn_def])
   >> `!t n. t IN m_space m ==>
                u n t <= u (SUC n) t /\
                (f t < & n ==> u n t <= f t) /\
                (f t < & n ==> f t < u n t + 1 / (2 pow n))`
        by (NTAC 3 STRIP_TAC
            >> `0 <= f t * (2 pow n)`
                by (FULL_SIMP_TAC std_ss [nonneg_def] >> `&2 = 2` by RW_TAC real_ss []
                    >> POP_ORW >> RW_TAC real_ss [REAL_LE, REAL_OF_NUM_POW, REAL_LE_MUL])
            >> `(\i. f t * 2 pow n < & i) ($LEAST (\i. f t * 2 pow n < & i))`
                by (MATCH_MP_TAC LEAST_INTRO >> (MP_TAC o Q.SPEC `1`) REAL_ARCH
                    >> RW_TAC real_ss [])
            >> FULL_SIMP_TAC std_ss []
            >> `0 < ($LEAST (\i. f t * 2 pow n < & i))`
                by (ONCE_REWRITE_TAC [GSYM REAL_LT] >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `f t * 2 pow n` >> RW_TAC std_ss [])
            >> `($LEAST (\i. f t * 2 pow n < & i)) - 1 < ($LEAST (\i. f t * 2 pow n < & i))`
                by (POP_ASSUM MP_TAC >> DECIDE_TAC)
            >> `~(f t * 2 pow n < &(LEAST i. f t * 2 pow n < & i) - 1)`
                by (SPOSE_NOT_THEN STRIP_ASSUME_TAC
                    >> `~((\i. f t * 2 pow n < & i) ((LEAST i. f t * 2 pow n < & i) - 1))`
                        by (MATCH_MP_TAC LESS_LEAST >> ASM_REWRITE_TAC [])
                    >> `& ((LEAST i. f t * 2 pow n < & i) - 1) =  & (LEAST i. f t * 2 pow n < & i) - 1`
                        by (RW_TAC real_ss [REAL_SUB])
                    >> FULL_SIMP_TAC real_ss [])
            >> `0 < 2 pow n` by (`&2 = 2` by RW_TAC real_ss [] >> POP_ORW
                                    >> RW_TAC std_ss [REAL_OF_NUM_POW, REAL_LE_INV, REAL_LT])
            >> `t IN A n (($LEAST (\i. f t * (2 pow n) < & i)) - 1)`
                by (Q.UNABBREV_TAC `A` >> RW_TAC real_ss [IN_INTER, GSPECIFICATION, REAL_LE_LDIV_EQ, REAL_LT_RDIV_EQ, ADD1]
                    >> `& ((LEAST i. f t * 2 pow n < & i) - 1) =  & (LEAST i. f t * 2 pow n < & i) - 1`
                        by (RW_TAC real_ss [REAL_SUB])
                    >> FULL_SIMP_TAC std_ss [real_lt])
            >> `& ((LEAST i. f t * 2 pow n < & i) - 1) = & (LEAST i. f t * 2 pow n < & i) - 1`
                        by (RW_TAC real_ss [REAL_SUB])
            >> FULL_SIMP_TAC std_ss []
            >> Q.ABBREV_TAC `i = (LEAST i. f t * 2 pow n < & i) - 1`
            >> Cases_on `f t < & n`
            >- (`&i <= f t * (2 pow n)`
                        by (Q.UNABBREV_TAC `A` >> FULL_SIMP_TAC std_ss [IN_INTER, GSPECIFICATION, GSYM REAL_LE_LDIV_EQ])
                >> `f t * (2 pow n) < & n * (2 pow n)` by RW_TAC std_ss [REAL_LT_RMUL]
                >> `& i < & n * 2 pow n` by METIS_TAC [REAL_LET_TRANS]
                >> `i < n * 2**n`
                        by (`2 = &2` by RW_TAC real_ss []
                            >> FULL_SIMP_TAC real_ss [REAL_OF_NUM_POW])
                >> `u n t = & i / (2 pow n)` by RW_TAC std_ss []
                >> `u n t <= f t` by RW_TAC std_ss [REAL_LE_LDIV_EQ]
                >> `f t < u n t + 1 / 2 pow n`
                        by (ASM_SIMP_TAC std_ss []
                            >> FULL_SIMP_TAC std_ss [real_div]
                            >> RW_TAC std_ss [GSYM REAL_ADD_RDISTRIB]
                            >> RW_TAC std_ss [GSYM real_div, REAL_LT_RDIV_EQ]
                            >> Q.UNABBREV_TAC `i` >> RW_TAC real_ss [])
                >> reverse CONJ_TAC >- RW_TAC std_ss []
                >> Cases_on `f t < &(2*i+1)/(2 * (2 pow n))`
                >- (RW_TAC std_ss []
                    >> `t IN A (n+1) (2 * i)`
                        by (Q.UNABBREV_TAC `A` >> RW_TAC real_ss [IN_INTER, GSPECIFICATION, ADD1, POW_ADD, POW_1, REAL_MUL_COMM]
                            >> RW_TAC real_ss [real_div, REAL_INV_MUL, REAL_LT_IMP_NE]
                            >> ONCE_REWRITE_TAC [GSYM REAL_MUL]
                            >> `2 * & i * (inv 2 * inv (2 pow n)) = (& i * inv (2 pow n)) * (2 * inv 2)` by REAL_ARITH_TAC
                            >> POP_ORW >> RW_TAC real_ss [REAL_MUL_RINV] >> RW_TAC std_ss [GSYM real_div, REAL_LE_LDIV_EQ])
                    >> `&(2 * i) < & (n + 1) * 2 pow (n+1)`
                        by (RW_TAC real_ss [POW_ADD]
                            >> `& (2 * i) = 2 * &i` by RW_TAC real_ss [] >> POP_ORW
                            >> `& (n + 1) * (2 pow n * 2) = 2 * (& (n + 1) * (2 pow n))` by REAL_ARITH_TAC >> POP_ORW
                            >> RW_TAC real_ss [REAL_LT_LMUL]
                            >> MATCH_MP_TAC REAL_LTE_TRANS >> Q.EXISTS_TAC `& n * 2 pow n`
                            >> RW_TAC real_ss [REAL_LE_RMUL])
                    >> `u (n + 1) t = &(2 * i) / 2 pow (n + 1)` by METIS_TAC []
                    >> RW_TAC real_ss [ADD1, POW_ADD, POW_1]
                    >> RW_TAC real_ss [real_div, REAL_INV_MUL, REAL_LT_IMP_NE]
                    >> RW_TAC std_ss [GSYM REAL_MUL]
                    >> `2 * & i * (inv (2 pow n) * inv 2) = (2 * inv 2) * (&i * inv (2 pow n))` by REAL_ARITH_TAC
                    >> POP_ORW >> RW_TAC real_ss [REAL_MUL_RINV])
                >> `t IN A (n+1) (2*i+1)`
                        by (Q.UNABBREV_TAC `A` >> RW_TAC real_ss [IN_INTER, GSPECIFICATION, ADD1, POW_ADD, POW_1, REAL_MUL_COMM]
                            >- FULL_SIMP_TAC std_ss [IN_INTER, GSPECIFICATION, REAL_NOT_LT]
                            >> FULL_SIMP_TAC std_ss [IN_INTER, GSPECIFICATION]
                            >> `2 * i + 2 = 2 * (i + 1)` by DECIDE_TAC >> POP_ORW
                            >> RW_TAC real_ss [real_div, REAL_INV_MUL, REAL_LT_IMP_NE]
                            >> RW_TAC std_ss [GSYM REAL_MUL]
                            >> `2 * & (i + 1) * (inv 2 * inv (2 pow n)) =
                                (2 * inv 2) * (&(i+1) * inv (2 pow n))` by REAL_ARITH_TAC
                            >> POP_ORW >> RW_TAC real_ss [REAL_MUL_RINV]
                            >> RW_TAC std_ss [GSYM REAL_ADD, REAL_ADD_RDISTRIB]
                            >> FULL_SIMP_TAC std_ss [real_div] >> METIS_TAC [])
                >> `&(2*i + 1) < & (n+1) * 2 pow (n+1)`
                        by (RW_TAC std_ss [GSYM REAL_ADD, REAL_ADD_RDISTRIB]
                            >> MATCH_MP_TAC REAL_LT_ADD2
                            >> RW_TAC real_ss [POW_ADD, POW_1]
                            >- (`& n * (2 pow n * 2) = 2 * (&n * 2 pow n)` by REAL_ARITH_TAC
                                >> POP_ORW >> RW_TAC std_ss [GSYM REAL_MUL]
                                >> RW_TAC real_ss [REAL_LT_LMUL])
                            >> rpt (POP_ASSUM (K ALL_TAC))
                            >> Induct_on `n` >> RW_TAC real_ss []
                            >> MATCH_MP_TAC REAL_LT_TRANS >> Q.EXISTS_TAC `2 pow n * 2`
                            >> RW_TAC real_ss [REAL_LT_RMUL, REAL_POW_MONO_LT])
                >> `u (n+1) t = &(2*i + 1) / (2 pow (n+1))` by METIS_TAC []
                >> RW_TAC real_ss [ADD1, POW_ADD, POW_1]
                >> RW_TAC real_ss [real_div, REAL_INV_MUL, REAL_LT_IMP_NE]
                >> RW_TAC std_ss [GSYM REAL_MUL, GSYM REAL_ADD, REAL_ADD_RDISTRIB]
                >> `2 * & i * (inv (2 pow n) * inv 2) = (2 * inv 2) * (&i * inv (2 pow n))` by REAL_ARITH_TAC
                >> POP_ORW >> RW_TAC real_ss [REAL_MUL_RINV, REAL_LE_ADDR, REAL_LE_MUL, REAL_LE_INV, REAL_LT_IMP_LE])
            >> RW_TAC std_ss []
            >> `u n t = 0`
                by (Q.UNABBREV_TAC `u` >> RW_TAC std_ss []
                    >> `FINITE {i | 0 < i /\ & i < & n * 2 pow n}` by RW_TAC std_ss []
                    >> (MP_TAC o REWRITE_RULE [IN_DELETE, REAL_ENTIRE]
                        o Q.SPECL [`\i. & i / 2 pow n * indicator_fn (A n i) t`, `0`] o UNDISCH
                        o Q.SPEC `{i | 0 < i /\ & i < & n * 2 pow n}` o INST_TYPE [``:'a``|->``:num``]) REAL_SUM_IMAGE_FINITE_CONST2
                    >> RW_TAC real_ss [] >> POP_ASSUM MATCH_MP_TAC
                    >> RW_TAC std_ss [GSPECIFICATION]
                    >> Suff `~(t IN A n y)` >- RW_TAC real_ss [indicator_fn_def]
                    >> Q.UNABBREV_TAC `A` >> FULL_SIMP_TAC std_ss [IN_INTER, GSPECIFICATION]
                    >> reverse (Cases_on `& y / 2 pow n <= f t`) >> RW_TAC std_ss []
                    >> FULL_SIMP_TAC std_ss [REAL_NOT_LT]
                    >> MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `&n`
                    >> FULL_SIMP_TAC std_ss [REAL_LE_LDIV_EQ, REAL_OF_NUM_POW, REAL_MUL, REAL_LE, REAL_LT]
                    >> Q.PAT_X_ASSUM `y < n * 2 ** n` MP_TAC >> DECIDE_TAC)
            >> RW_TAC real_ss [] >> Q.UNABBREV_TAC `u` >> RW_TAC std_ss []
            >> `!n. 0 < 2 pow n`
                        by (Induct >> RW_TAC real_ss []
                            >> MATCH_MP_TAC REAL_LT_TRANS >> Q.EXISTS_TAC `2 pow n'`
                            >> RW_TAC real_ss [REAL_POW_MONO_LT])
            >> MATCH_MP_TAC REAL_SUM_IMAGE_POS
            >> RW_TAC real_ss [REAL_LE_MUL, indicator_fn_def, GSPECIFICATION, REAL_LE_DIV, REAL_LT_IMP_LE])
 >> STRONG_CONJ_TAC
 >- (rpt STRIP_TAC >> Induct_on `n` >- RW_TAC arith_ss [REAL_LE_REFL]
       >> RW_TAC arith_ss [DECIDE ``!(m:num) n. m <= SUC n <=> (m = SUC n) \/ m <= n``]
       >- RW_TAC real_ss []
       >> MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `u n x'` >> RW_TAC std_ss [])
 >> rpt STRIP_TAC
 >> `?n0. f x' < & n0`
        by ((MP_TAC o Q.SPEC `1`) REAL_ARCH >> RW_TAC real_ss [])
 >> `!n. &n0 <= &(n+n0)` by (RW_TAC real_ss [REAL_LE] >> DECIDE_TAC)
 >> `!n. f x' < & (n+n0)` by METIS_TAC [REAL_LTE_TRANS]
 >> `!n. u (n+n0) x' <= f x'` by METIS_TAC []
 >> `convergent (\n. u (n+n0) x')`
        by (MATCH_MP_TAC SEQ_ICONV
            >> CONJ_TAC
            >- (MATCH_MP_TAC SEQ_BOUNDED_2 >> Q.EXISTS_TAC `0` >> Q.EXISTS_TAC `f x'`
                >> RW_TAC std_ss [] >> MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `u n0 x'`
                >> METIS_TAC [psfis_nonneg, nonneg_def, REAL_LE])
            >> RW_TAC std_ss [GREATER_EQ, real_ge])
 >> FULL_SIMP_TAC std_ss [convergent]
 >> `l <= f x'`
        by (MATCH_MP_TAC SEQ_LE_IMP_LIM_LE >> Q.EXISTS_TAC `(\n. u (n + n0) x')` >> RW_TAC std_ss [])
 >> `(\i. u i x') --> l`
        by (MATCH_MP_TAC SEQ_OFFSET >> Q.EXISTS_TAC `n0` >> RW_TAC std_ss [o_DEF])
 >> Suff `f x' <= l` >- METIS_TAC [REAL_LE_ANTISYM]
 >> `!n. f x' <= u (n+n0) x' + 1/(2 pow (n+n0))`
        by METIS_TAC [REAL_LT_IMP_LE]
 >> MATCH_MP_TAC LE_SEQ_IMP_LE_LIM
 >> Q.EXISTS_TAC `\n. u (n + n0) x' + 1 / 2 pow (n + n0)`
 >> RW_TAC std_ss []
 >> `(\n. u (n + n0) x' + 1 / 2 pow (n + n0)) = (\n. (\n. u (n + n0) x') n + (\n. 1 / 2 pow (n+n0)) n)`
        by RW_TAC std_ss []
 >> POP_ORW
 >> `l = l + 0` by RW_TAC real_ss []
 >> POP_ORW
 >> MATCH_MP_TAC SEQ_ADD
 >> RW_TAC std_ss []
 >> `(\n. 1 / 2 pow (n + n0)) = (\n. inv ((\n. 2 pow (n+n0)) n))`
        by RW_TAC real_ss [real_div]
 >> POP_ORW >> MATCH_MP_TAC SEQ_INV0
 >> RW_TAC std_ss [GREATER_EQ, real_gt]
 >> `?n. y < &n` by ((MP_TAC o Q.SPEC `1`) REAL_ARCH >> RW_TAC real_ss [])
 >> Q.EXISTS_TAC `n`
 >> RW_TAC std_ss []
 >> MATCH_MP_TAC REAL_LT_TRANS >> Q.EXISTS_TAC `&n` >> RW_TAC std_ss []
 >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `&n'` >> RW_TAC std_ss [REAL_LE]
 >> MATCH_MP_TAC REAL_LTE_TRANS >> Q.EXISTS_TAC `2 pow n'` >> RW_TAC std_ss [POW_2_LT]
 >> Cases_on `n0 = 0`
 >- RW_TAC arith_ss [REAL_LE_REFL]
 >> MATCH_MP_TAC REAL_LT_IMP_LE
 >> MATCH_MP_TAC REAL_POW_MONO_LT
 >> RW_TAC arith_ss [] >> RW_TAC real_ss []);

val nnfis_dom_conv = store_thm
  ("nnfis_dom_conv",
  ``!m f g b. measure_space m /\
              f IN borel_measurable (m_space m, measurable_sets m) /\
              b IN nnfis m g /\ (!t. t IN m_space m ==> f t <= g t) /\
              (!t. t IN m_space m ==> 0 <= f t) ==>
                   (?a. a IN nnfis m f /\ a <= b)``,
   rpt STRIP_TAC
   >> (MP_TAC o Q.SPECL [`m`, `f`]) borel_measurable_mon_conv_psfis
   >> RW_TAC std_ss []
   >> `!n t. t IN m_space m ==> u n t <= f t`
        by (rpt STRIP_TAC >> FULL_SIMP_TAC std_ss [mono_convergent_def]
            >> `u n t = (\n. u n t) n` by RW_TAC std_ss [] >> POP_ORW
            >> MATCH_MP_TAC SEQ_MONO_LE
            >> RW_TAC std_ss [])
   >> `!n. x n IN nnfis m (u n)` by METIS_TAC [psfis_nnfis]
   >> `!n. x n <= b`
        by (STRIP_TAC >> MATCH_MP_TAC nnfis_mono
            >> Q.EXISTS_TAC `(u n)` >> Q.EXISTS_TAC `g` >> Q.EXISTS_TAC `m`
            >> RW_TAC std_ss [] >> MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `f w`
            >> RW_TAC std_ss [])
   >> `!n n'. n <= n' ==> x n <= x n'`
        by (rpt STRIP_TAC >> MATCH_MP_TAC psfis_mono
            >> Q.EXISTS_TAC `m` >> Q.EXISTS_TAC `(u n)` >> Q.EXISTS_TAC `(u n')`
            >> FULL_SIMP_TAC std_ss [mono_convergent_def])
   >> `convergent x`
        by (MATCH_MP_TAC SEQ_ICONV
            >> CONJ_TAC
            >- (MATCH_MP_TAC SEQ_BOUNDED_2 >> Q.EXISTS_TAC `0` >> Q.EXISTS_TAC `b`
                >> METIS_TAC [pos_psfis])
            >> RW_TAC std_ss [GREATER_EQ, real_ge])
    >> FULL_SIMP_TAC std_ss [convergent]
    >> Q.EXISTS_TAC `l` >> RW_TAC std_ss [nnfis_def, GSPECIFICATION]
    >- (Q.EXISTS_TAC `u` >> Q.EXISTS_TAC `x` >> RW_TAC std_ss [])
    >> MATCH_MP_TAC SEQ_LE_IMP_LIM_LE
    >> Q.EXISTS_TAC `x` >> RW_TAC std_ss []);

val nnfis_integral = store_thm
  ("nnfis_integral",
  ``!m f a. measure_space m /\ a IN nnfis m f ==>
                integrable m f /\ (integral m f = a)``,
   NTAC 4 STRIP_TAC
   >> `!t. t IN m_space m ==> 0 <= f t` by METIS_TAC [nnfis_pos_on_mspace]
   >> `a IN nnfis m (fn_plus f)`
        by (MATCH_MP_TAC nnfis_mon_conv
            >> Q.EXISTS_TAC `(\i. f )` >> Q.EXISTS_TAC `(\i. a)`
            >> RW_TAC std_ss [REAL_LE_REFL, SEQ_CONST, mono_convergent_def, fn_plus_def])
   >> `0 IN nnfis m (fn_minus f)`
        by (MATCH_MP_TAC nnfis_mon_conv
            >> Q.EXISTS_TAC `(\i x. 0)` >> Q.EXISTS_TAC `(\i. 0)`
            >> RW_TAC std_ss [REAL_LE_REFL, SEQ_CONST, mono_convergent_def, fn_minus_def]
            >> MATCH_MP_TAC psfis_nnfis
            >> ASM_REWRITE_TAC []
            >> (MP_TAC o Q.SPECL [`m`, `{}`]) psfis_indicator
            >> RW_TAC real_ss [indicator_fn_def, NOT_IN_EMPTY, MEASURE_EMPTY]
            >> POP_ASSUM MATCH_MP_TAC
            >> FULL_SIMP_TAC std_ss [measure_space_def, SIGMA_ALGEBRA, subsets_def])
   >> RW_TAC std_ss [integrable_def, integral_def]
   >| [Q.EXISTS_TAC `a` >> RW_TAC std_ss [],
       Q.EXISTS_TAC `0` >> RW_TAC std_ss [],
       Suff `((@i. i IN nnfis m (fn_plus f)) = a) /\
             ((@j. j IN nnfis m (fn_minus f)) = 0)`
       >- RW_TAC real_ss []
       >> CONJ_TAC
       >> MATCH_MP_TAC SELECT_UNIQUE
       >> METIS_TAC [nnfis_unique]]);

val nnfis_minus_nnfis_integral = store_thm
  ("nnfis_minus_nnfis_integral",
  ``!m f g a b. measure_space m /\
                a IN nnfis m f /\
                b IN nnfis m g ==>
                integrable m (\t. f t - g t) /\
                (integral m (\t. f t - g t) = a - b)``,
   NTAC 6 STRIP_TAC
   >> `(\t. f t - g t) IN borel_measurable (m_space m, measurable_sets m)`
        by (MATCH_MP_TAC borel_measurable_sub_borel_measurable
            >> METIS_TAC [nnfis_borel_measurable])
   >> `fn_plus (\t. f t - g t) IN borel_measurable (m_space m, measurable_sets m) /\
       fn_minus (\t. f t - g t) IN borel_measurable (m_space m, measurable_sets m)`
        by (MATCH_MP_TAC fn_plus_fn_minus_borel_measurable >> RW_TAC std_ss [])
   >> `nonneg (fn_plus (\t. f t - g t)) /\
       nonneg (fn_minus (\t. f t - g t))`
        by (RW_TAC real_ss [nonneg_def, fn_plus_def, fn_minus_def]
            >> RW_TAC real_ss [GSYM real_lt, REAL_LE, REAL_LE_SUB_LADD, REAL_LT_IMP_LE, REAL_LT_SUB_RADD]
            >> FULL_SIMP_TAC std_ss [GSYM real_lt, REAL_LT_IMP_LE])
   >> `a + b IN nnfis m (\t. f t + g t)` by RW_TAC std_ss [nnfis_add]
   >> `!t. t IN m_space m ==> 0 <= f t /\ 0 <= g t` by METIS_TAC [nnfis_pos_on_mspace]

   >> `!t. t IN m_space m ==> fn_plus (\t. f t - g t) t <= (\t. f t + g t) t`
        by (RW_TAC real_ss [fn_plus_def, GSYM real_lt, REAL_LE_SUB_RADD, REAL_LE_ADD]
            >> ONCE_REWRITE_TAC [GSYM REAL_ADD_ASSOC] >> RW_TAC std_ss [REAL_LE_ADDR, REAL_LE_ADD])
   >> `!t. t IN m_space m ==> fn_minus (\t. f t - g t) t <= (\t. f t + g t) t`
        by (RW_TAC real_ss [fn_minus_def, GSYM real_lt, REAL_LE_SUB_RADD, REAL_LE_ADD]
            >> FULL_SIMP_TAC std_ss [GSYM real_lt]
            >> `f t + g t + f t = g t + (f t + f t)` by REAL_ARITH_TAC >> POP_ORW
            >> RW_TAC std_ss [REAL_LE_ADDR, REAL_LE_ADD])
   >> `!t. 0 <= fn_plus (\t. f t - g t) t /\ 0 <= fn_minus (\t. f t - g t) t`
        by (RW_TAC real_ss [fn_plus_def, fn_minus_def]
            >> FULL_SIMP_TAC real_ss [REAL_LE_SUB_LADD, GSYM real_lt, REAL_LT_IMP_LE, REAL_LT_SUB_RADD])
   >> (MP_TAC o Q.SPECL [`m`, `(fn_plus (\t. f t - g t))`, `(\t. f t + g t)`, `a+b`]) nnfis_dom_conv
   >> (MP_TAC o Q.SPECL [`m`, `(fn_minus (\t. f t - g t))`, `(\t. f t + g t)`, `a+b`]) nnfis_dom_conv
   >> ASM_SIMP_TAC std_ss [nonneg_def]
   >> NTAC 2 STRIP_TAC >> CONJ_TAC
   >- (RW_TAC std_ss [integrable_def]
       >- (Q.EXISTS_TAC `a''` >> RW_TAC std_ss [])
       >> Q.EXISTS_TAC `a'` >> RW_TAC std_ss [])
   >> `a + a' IN nnfis m (\t. f t + (fn_minus (\t. f t - g t)) t)`
        by (MATCH_MP_TAC nnfis_add >> RW_TAC std_ss [])
   >> `b + a'' IN nnfis m (\t. g t + (fn_plus (\t. f t - g t)) t)`
        by (MATCH_MP_TAC nnfis_add >> RW_TAC std_ss [])
   >> `(\t. f t + fn_minus (\t. f t - g t) t) =
       (\t. g t + fn_plus (\t. f t - g t) t)`
        by (RW_TAC std_ss [Once FUN_EQ_THM, fn_minus_def, fn_plus_def]
            >> RW_TAC real_ss [])
   >> FULL_SIMP_TAC std_ss []
   >> `a + a' = b + a''`
        by (MATCH_MP_TAC nnfis_unique
            >> Q.EXISTS_TAC `(\t. g t + fn_plus (\t. f t - g t) t)`
            >> Q.EXISTS_TAC `m`
            >> RW_TAC std_ss [])
   >> `a - b = a'' - a'`
        by (RW_TAC std_ss [REAL_EQ_SUB_RADD]
            >> `a'' - a' + b = (a'' + b) - a'` by REAL_ARITH_TAC
            >> POP_ORW
            >> RW_TAC std_ss [REAL_EQ_SUB_LADD, REAL_ADD_COMM])
   >> RW_TAC std_ss [integral_def]
   >> Suff `((@i. i IN nnfis m (fn_plus (\t. f t - g t))) = a'') /\
            ((@j. j IN nnfis m (fn_minus (\t. f t - g t))) = a')`
   >- RW_TAC std_ss []
   >> CONJ_TAC
   >> MATCH_MP_TAC SELECT_UNIQUE
   >> METIS_TAC [nnfis_unique]);

val integral_borel_measurable = store_thm
  ("integral_borel_measurable",
  ``!m f. integrable m f ==> f IN borel_measurable (m_space m, measurable_sets m)``,
    RW_TAC std_ss [integrable_def]
 >> ONCE_REWRITE_TAC [(UNDISCH o Q.SPECL [`f`, `m`]) fn_plus_fn_minus_borel_measurable_iff]
 >> METIS_TAC [nnfis_borel_measurable]);

val integral_indicator_fn = store_thm
  ("integral_indicator_fn",
  ``!m a. measure_space m /\ a IN measurable_sets m ==>
                (integral m (indicator_fn a) = (measure m a)) /\
                integrable m (indicator_fn a)``,
   METIS_TAC [psfis_indicator, psfis_nnfis, nnfis_integral]);

val integral_add = store_thm
  ("integral_add",
  ``!m f g. integrable m f /\ integrable m g ==>
                integrable m (\t. f t + g t) /\
                (integral m (\t. f t + g t) = integral m f + integral m g)``,
   NTAC 4 STRIP_TAC
   >> NTAC 2 (POP_ASSUM (MP_TAC o REWRITE_RULE [integrable_def]))
   >> NTAC 2 STRIP_TAC
   >> Q.ABBREV_TAC `u = (\t. fn_plus f t + fn_plus g t)`
   >> Q.ABBREV_TAC `v = (\t. fn_minus f t + fn_minus g t)`
   >> `x + x' IN nnfis m u`
        by (Q.UNABBREV_TAC `u` >> MATCH_MP_TAC nnfis_add >> RW_TAC std_ss [])
   >> `y + y' IN nnfis m v`
        by (Q.UNABBREV_TAC `v` >> MATCH_MP_TAC nnfis_add >> RW_TAC std_ss [])
   >> `!f. (\t. fn_plus f t - fn_minus f t) = f`
        by (RW_TAC real_ss [fn_plus_def, fn_minus_def, Once FUN_EQ_THM]
            >> RW_TAC real_ss [])
   >> `integral m f = x - y`
        by ((MP_TAC o Q.SPECL [`m`, `fn_plus f`, `fn_minus f`, `x`, `y`]) nnfis_minus_nnfis_integral
            >> RW_TAC std_ss [])
   >> `integral m g = x' - y'`
        by ((MP_TAC o Q.SPECL [`m`, `fn_plus g`, `fn_minus g`, `x'`, `y'`]) nnfis_minus_nnfis_integral
            >> RW_TAC std_ss [])
   >> `(\t. f t + g t) = (\t. u t - v t)`
        by (Q.UNABBREV_TAC `u` >> Q.UNABBREV_TAC `v`
            >> RW_TAC real_ss [Once FUN_EQ_THM]
            >> `fn_plus f t + fn_plus g t - (fn_minus f t + fn_minus g t) =
                (\t. fn_plus f t - fn_minus f t) t + (\t. fn_plus g t - fn_minus g t) t`
                        by (RW_TAC std_ss [] >> REAL_ARITH_TAC)
            >> ASM_SIMP_TAC std_ss []
            >> FULL_SIMP_TAC std_ss [FUN_EQ_THM])
   >> ASM_SIMP_TAC std_ss []
   >> `x - y + (x' - y') = (x + x') - (y + y')` by REAL_ARITH_TAC
   >> POP_ORW
   >> MATCH_MP_TAC nnfis_minus_nnfis_integral
   >> RW_TAC std_ss []);

val integral_mono = store_thm
  ("integral_mono",
  ``!m f g. integrable m f /\ integrable m g /\
            (!t. t IN m_space m ==> f t <= g t) ==>
            integral m f <= integral m g``,
   RW_TAC std_ss [integrable_def]
   >> `!f. (\t. fn_plus f t - fn_minus f t) = f`
        by (RW_TAC real_ss [fn_plus_def, fn_minus_def, Once FUN_EQ_THM]
            >> RW_TAC real_ss [])
   >> `integral m f = x - y`
        by ((MP_TAC o Q.SPECL [`m`, `fn_plus f`, `fn_minus f`, `x`, `y`]) nnfis_minus_nnfis_integral
            >> RW_TAC std_ss [])
   >> `integral m g = x' - y'`
        by ((MP_TAC o Q.SPECL [`m`, `fn_plus g`, `fn_minus g`, `x'`, `y'`]) nnfis_minus_nnfis_integral
            >> RW_TAC std_ss [])
   >> ASM_REWRITE_TAC [REAL_LE_SUB_RADD]
   >> `x' - y' + y = (x' + y) - y'` by REAL_ARITH_TAC >> POP_ORW >> RW_TAC std_ss [REAL_LE_SUB_LADD]
   >> MATCH_MP_TAC REAL_LE_ADD2
   >> CONJ_TAC
   >- (MATCH_MP_TAC nnfis_mono >> Q.EXISTS_TAC `fn_plus f` >> Q.EXISTS_TAC `fn_plus g` >> Q.EXISTS_TAC `m`
       >> RW_TAC real_ss [fn_plus_def]
       >> METIS_TAC [REAL_LE_TRANS])
   >> MATCH_MP_TAC nnfis_mono >> Q.EXISTS_TAC `fn_minus g` >> Q.EXISTS_TAC `fn_minus f` >> Q.EXISTS_TAC `m`
   >> RW_TAC real_ss [fn_minus_def]
   >> METIS_TAC [REAL_LE_TRANS, REAL_LE_NEGTOTAL]);

val integral_times = store_thm
  ("integral_times",
  ``!m f a. integrable m f ==>
            integrable m (\t. a * f t) /\
           (integral m (\t. a * f t) = a * integral m f)``,
   NTAC 4 STRIP_TAC >> POP_ASSUM (MP_TAC o REWRITE_RULE [integrable_def])
   >> STRIP_TAC
   >> Cases_on `0 <= a`
   >- (`a * x IN nnfis m (fn_plus (\t. a * f t))`
        by (`fn_plus (\t. a * f t) = (\t. a * fn_plus f t)`
                by (RW_TAC real_ss [FUN_EQ_THM, fn_plus_def] >> RW_TAC real_ss []
                    >- (Cases_on `a = 0` >- RW_TAC real_ss []
                        >> METIS_TAC [GSYM REAL_LE_LDIV_EQ, REAL_LT_LE, REAL_DIV_LZERO, REAL_MUL_COMM])
                    >> METIS_TAC [REAL_LE_MUL])
            >> POP_ORW
            >> MATCH_MP_TAC nnfis_times >> RW_TAC std_ss [])
       >> `a * y IN nnfis m (fn_minus (\t. a * f t))`
        by (`fn_minus (\t. a * f t) = (\t. a * fn_minus f t)`
                by (RW_TAC real_ss [FUN_EQ_THM, fn_minus_def] >> RW_TAC real_ss []
                    >- (Cases_on `a = 0` >- RW_TAC real_ss []
                        >> METIS_TAC [GSYM REAL_LE_LDIV_EQ, REAL_LT_LE, REAL_DIV_LZERO, REAL_MUL_COMM])
                    >> METIS_TAC [REAL_LE_MUL])
            >> POP_ORW
            >> MATCH_MP_TAC nnfis_times >> RW_TAC std_ss [])
       >> ASM_SIMP_TAC std_ss [integrable_def, integral_def]
       >> CONJ_TAC >- (CONJ_TAC >- (Q.EXISTS_TAC `a * x` >> RW_TAC std_ss [])
                       >> Q.EXISTS_TAC `a * y` >> RW_TAC std_ss [])
       >> `(@i. i IN nnfis m (fn_plus (\t. a * f t))) = a * x`
                by (MATCH_MP_TAC SELECT_UNIQUE >> METIS_TAC [nnfis_unique])
       >> POP_ORW
       >> `(@j. j IN nnfis m (fn_minus (\t. a * f t))) = a * y`
                by (MATCH_MP_TAC SELECT_UNIQUE >> METIS_TAC [nnfis_unique])
       >> POP_ORW
       >> `(@i. i IN nnfis m (fn_plus f)) = x`
                by (MATCH_MP_TAC SELECT_UNIQUE >> METIS_TAC [nnfis_unique])
       >> POP_ORW
       >> `(@j. j IN nnfis m (fn_minus f)) = y`
                by (MATCH_MP_TAC SELECT_UNIQUE >> METIS_TAC [nnfis_unique])
       >> POP_ORW
       >> RW_TAC std_ss [REAL_SUB_LDISTRIB])
   >> `0 <= ~a` by METIS_TAC [REAL_LE_NEGTOTAL]
   >> `(fn_plus (\t. a * f t) = (\t. ~a * fn_minus f t)) /\
       (fn_minus (\t. a * f t) = (\t. ~a * fn_plus f t))`
        by METIS_TAC [REAL_NEG_GE0, real_fn_plus_fn_minus_neg_times]
   >> `~a * x IN nnfis m (fn_minus (\t. a * f t))`
        by (ASM_SIMP_TAC std_ss [] >> MATCH_MP_TAC nnfis_times >> RW_TAC std_ss [])
   >> `~a * y IN nnfis m (fn_plus (\t. a * f t))`
        by (ASM_SIMP_TAC std_ss [] >> MATCH_MP_TAC nnfis_times >> RW_TAC std_ss [])
   >>  ASM_SIMP_TAC std_ss [integrable_def, integral_def]
   >> Q.PAT_X_ASSUM `P = Q` (MP_TAC o GSYM)
   >> Q.PAT_X_ASSUM `P = Q` (MP_TAC o GSYM)
   >> STRIP_TAC >> STRIP_TAC
   >> CONJ_TAC >- (CONJ_TAC >- (Q.EXISTS_TAC `~a * y` >> RW_TAC std_ss [])
                   >> Q.EXISTS_TAC `~a * x` >> RW_TAC std_ss [])
   >> ASM_REWRITE_TAC []
   >> `(@j. j IN nnfis m (fn_minus (\t. a * f t))) = ~a * x`
                by (MATCH_MP_TAC SELECT_UNIQUE >> METIS_TAC [nnfis_unique])
   >> POP_ORW
   >> `(@i. i IN nnfis m (fn_plus (\t. a * f t))) = ~a * y`
                by (MATCH_MP_TAC SELECT_UNIQUE >> METIS_TAC [nnfis_unique])
   >> POP_ORW
   >> `(@i. i IN nnfis m (fn_plus f)) = x`
                by (MATCH_MP_TAC SELECT_UNIQUE >> METIS_TAC [nnfis_unique])
   >> POP_ORW
   >> `(@j. j IN nnfis m (fn_minus f)) = y`
                by (MATCH_MP_TAC SELECT_UNIQUE >> METIS_TAC [nnfis_unique])
   >> POP_ORW
   >> RW_TAC real_ss [REAL_SUB_LDISTRIB, REAL_ADD_COMM, GSYM real_sub]);

val markov_ineq = store_thm
  ("markov_ineq",
  ``!m f a n. integrable m f /\ 0 < a /\ integrable m (\x. (abs (f x)) pow n) ==>
              measure m ((PREIMAGE f {y | a <= y}) INTER m_space m) <=
               (integral m (\x. (abs (f x)) pow n)) / (a pow n)``,
   rpt STRIP_TAC
   >> `0 < a pow n` by (Cases_on `n` >> RW_TAC real_ss [POW_POS_LT])
   >> RW_TAC real_ss [REAL_LE_RDIV_EQ]
   >> ONCE_REWRITE_TAC [REAL_MUL_COMM]
   >> `f IN borel_measurable (m_space m, measurable_sets m)`
        by METIS_TAC [integral_borel_measurable]
   >> `measure_space m` by FULL_SIMP_TAC std_ss [integrable_def]
   >> `{w | w IN m_space m /\ a <= f w} IN measurable_sets m`
        by FULL_SIMP_TAC std_ss [borel_measurable_ge_iff]
   >> `(a pow n) * (measure m ((PREIMAGE f {y | a <= y}) INTER m_space m)) =
       (a pow n) * measure m {w | w IN m_space m /\ a <= f w}`
        by RW_TAC std_ss [PREIMAGE_def, GSPECIFICATION, INTER_DEF, CONJ_COMM]
   >> POP_ORW
   >> `integrable m (indicator_fn {w | w IN m_space m /\ a <= f w}) /\
        ((a pow n) * measure m {w | w IN m_space m /\ a <= f w} =
          (a pow n) * integral m (indicator_fn {w | w IN m_space m /\ a <= f w}))`
        by ((MP_TAC o Q.SPECL [`m`, `{w | w IN m_space m /\ a <= f w}`]) integral_indicator_fn
            >> ASM_SIMP_TAC std_ss [])
   >> POP_ORW
   >> `a pow n * integral m (indicator_fn {w | w IN m_space m /\ a <= f w}) =
       integral m (\t. a pow n * (indicator_fn {w | w IN m_space m /\ a <= f w}) t)`
        by METIS_TAC [integral_times]
   >> POP_ORW
   >> MATCH_MP_TAC integral_mono
   >> ASM_SIMP_TAC std_ss []
   >> CONJ_TAC
   >- METIS_TAC [integral_times]
   >> rpt STRIP_TAC
   >> reverse (Cases_on `a <= f t`)
   >- RW_TAC real_ss [indicator_fn_def, GSPECIFICATION, POW_POS, ABS_POS]
   >> `abs (f t) pow n = abs (f t) pow n * 1` by RW_TAC real_ss []
   >> POP_ORW >> MATCH_MP_TAC REAL_LE_MUL2
   >> RW_TAC real_ss [REAL_LT_IMP_LE, indicator_fn_def, GSPECIFICATION]
   >> MATCH_MP_TAC POW_LE
   >> `0 <= f t` by METIS_TAC [REAL_LE_TRANS, REAL_LT_IMP_LE]
   >> RW_TAC real_ss [abs, REAL_LT_IMP_LE]);

Theorem finite_space_integral_reduce :
    !m f. measure_space m /\
          f IN borel_measurable (m_space m, measurable_sets m) /\
          FINITE (m_space m) ==> (integral m f = finite_space_integral m f)
Proof
    rpt STRIP_TAC
 >> `?c n. BIJ c (count n) (IMAGE f (m_space m))`
       by RW_TAC std_ss [GSYM FINITE_BIJ_COUNT_EQ, IMAGE_FINITE]
 >> Know `pos_simple_fn m (fn_plus f)
        (count n) (\i. PREIMAGE f {c i} INTER m_space m) (\i. if 0 <= c i then c i else 0) /\
        pos_simple_fn m (fn_minus f)
        (count n) (\i. PREIMAGE f {c i} INTER m_space m) (\i. if c i <= 0 then ~ c i else 0)`
 >- (RW_TAC std_ss [pos_simple_fn_def, FINITE_COUNT] >| (* 12 subgoals *)
     [ (* goal 1 (of 12) *)
       RW_TAC real_ss [fn_plus_def],
       (* goal 2 (of 12) *)
       `FINITE (count n)` by RW_TAC std_ss [FINITE_COUNT]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `count n`) REAL_SUM_IMAGE_IN_IF]
       >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
       >> `?i. i IN count n /\ (f t = c i)` by METIS_TAC []
       >> `(\x. (if x IN count n then (if 0 <= c x then c x else 0) *
                        indicator_fn (PREIMAGE f {c x} INTER m_space m) t else 0)) =
                (\x. if (x = i) /\ 0 <= c i then c i else 0)`
                by (RW_TAC std_ss [FUN_EQ_THM]
                    >> RW_TAC real_ss [indicator_fn_def, IN_PREIMAGE, IN_INTER]
                    >> FULL_SIMP_TAC real_ss [IN_SING]
                    >> METIS_TAC [])
       >> POP_ORW
       >> `count n = i INSERT ((count n) DELETE i)`
                by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DELETE] >> METIS_TAC [])
       >> POP_ORW
       >> ASM_SIMP_TAC std_ss [FINITE_INSERT, FINITE_DELETE, FINITE_COUNT,
                               REAL_SUM_IMAGE_THM, DELETE_DELETE]
       >> `FINITE (count n DELETE i)` by RW_TAC std_ss [FINITE_COUNT, FINITE_DELETE]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `count n DELETE i`) REAL_SUM_IMAGE_IN_IF]
       >> SIMP_TAC std_ss [IN_DELETE]
       >> (MP_TAC o Q.SPECL [`\x.0`, `0`] o UNDISCH o Q.ISPEC `count n DELETE i`)
                REAL_SUM_IMAGE_FINITE_CONST
       >> RW_TAC real_ss [fn_plus_def],
       (* goal 3 (of 12) *)
       `PREIMAGE f {c i} INTER m_space m =
        {w | w IN m_space m /\ (f w = (\n. c i) w)}`
          by (ONCE_REWRITE_TAC [EXTENSION] \\
              RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING, GSPECIFICATION, CONJ_SYM])
        >> POP_ORW
        >> MATCH_MP_TAC borel_measurable_eq_borel_measurable
        >> METIS_TAC [borel_measurable_const, measure_space_def],
       (* goal 4 (of 12) *)
        RW_TAC real_ss [],
       (* goal 5 (of 12) *)
        RW_TAC std_ss [DISJOINT_DEF]
        >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, NOT_IN_EMPTY, IN_PREIMAGE, IN_SING]
        >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE] >> METIS_TAC [],
       (* goal 6 (of 12) *)
        ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_INTER, IN_PREIMAGE, IN_SING]
        >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
        >> METIS_TAC [],
       (* goal 7 (of 12) *)
        RW_TAC real_ss [fn_minus_def, REAL_LT_IMP_LE, REAL_LE_RNEG]
        >> FULL_SIMP_TAC std_ss [GSYM real_lt, REAL_LT_IMP_LE],
       (* goal 8 (of 12) *)
        `FINITE (count n)` by RW_TAC std_ss [FINITE_COUNT]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `count n`) REAL_SUM_IMAGE_IN_IF]
       >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
       >> `?i. i IN count n /\ (f t = c i)` by METIS_TAC []
       >> `(\x. (if x IN count n then (if c x <= 0 then ~ c x else 0) *
                        indicator_fn (PREIMAGE f {c x} INTER m_space m) t else 0)) =
                (\x. if (x = i) /\ c i <= 0 then ~ c i else 0)`
                by (RW_TAC std_ss [FUN_EQ_THM]
                    >> RW_TAC real_ss [indicator_fn_def, IN_PREIMAGE, IN_INTER]
                    >> FULL_SIMP_TAC real_ss [IN_SING]
                    >> METIS_TAC [])
       >> POP_ORW
       >> `count n = i INSERT ((count n) DELETE i)`
                by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DELETE] >> METIS_TAC [])
       >> POP_ORW
       >> ASM_SIMP_TAC std_ss [FINITE_INSERT, FINITE_DELETE, FINITE_COUNT,
                               REAL_SUM_IMAGE_THM, DELETE_DELETE]
       >> `FINITE (count n DELETE i)` by RW_TAC std_ss [FINITE_COUNT, FINITE_DELETE]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `count n DELETE i`) REAL_SUM_IMAGE_IN_IF]
       >> SIMP_TAC std_ss [IN_DELETE]
       >> (MP_TAC o Q.SPECL [`\x.0`, `0`] o UNDISCH o Q.ISPEC `count n DELETE i`)
                REAL_SUM_IMAGE_FINITE_CONST
       >> RW_TAC real_ss [fn_minus_def]
       >> METIS_TAC [real_lt, REAL_LT_ANTISYM, REAL_LE_ANTISYM, REAL_NEG_0],
       (* goal 9 (of 12) *)
       `PREIMAGE f {c i} INTER m_space m =
        {w | w IN m_space m /\ (f w = (\n. c i) w)}`
           by (ONCE_REWRITE_TAC [EXTENSION] \\
               RW_TAC std_ss [IN_INTER, IN_PREIMAGE, IN_SING, GSPECIFICATION, CONJ_SYM])
        >> POP_ORW
        >> MATCH_MP_TAC borel_measurable_eq_borel_measurable
        >> METIS_TAC [borel_measurable_const, measure_space_def],
       (* goal 10 (of 12) *)
        RW_TAC real_ss [REAL_LE_RNEG],
       (* goal 11 (of 12) *)
        RW_TAC std_ss [DISJOINT_DEF]
        >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INTER, NOT_IN_EMPTY, IN_PREIMAGE, IN_SING]
        >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE] >> METIS_TAC [],
       (* goal 12 (of 12) *)
        ONCE_REWRITE_TAC [EXTENSION]
        >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_INTER, IN_PREIMAGE, IN_SING]
        >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
        >> METIS_TAC [] ])
 >> DISCH_TAC
 >> RW_TAC std_ss [finite_space_integral_def]
 >> `pos_simple_fn_integral m (count n) (\i. PREIMAGE f {c i} INTER m_space m)
                                        (\i. (if 0 <= c i then c i else 0))
        IN nnfis m (fn_plus f)`
        by (MATCH_MP_TAC psfis_nnfis
            >> RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
            >> Q.EXISTS_TAC `((count n), (\i. PREIMAGE f {c i} INTER m_space m),
                                         (\i. (if 0 <= c i then c i else 0)))`
            >> RW_TAC std_ss []
            >> Q.EXISTS_TAC `((count n), (\i. PREIMAGE f {c i} INTER m_space m),
                                         (\i. (if 0 <= c i then c i else 0)))`
            >> RW_TAC std_ss [])
 >> `pos_simple_fn_integral m (count n) (\i. PREIMAGE f {c i} INTER m_space m)
                                        (\i. (if c i <= 0 then ~ c i else 0))
        IN nnfis m (fn_minus f)`
        by (MATCH_MP_TAC psfis_nnfis
            >> RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
            >> Q.EXISTS_TAC `((count n), (\i. PREIMAGE f {c i} INTER m_space m),
                                         (\i. (if c i <= 0 then ~ c i else 0)))`
            >> RW_TAC std_ss []
            >> Q.EXISTS_TAC `((count n), (\i. PREIMAGE f {c i} INTER m_space m),
                                         (\i. (if c i <= 0 then ~ c i else 0)))`
            >> RW_TAC std_ss [])
   >> `!f. (\t. fn_plus f t - fn_minus f t) = f`
        by (RW_TAC real_ss [fn_plus_def, fn_minus_def, Once FUN_EQ_THM]
            >> RW_TAC real_ss [])
   >> (MP_TAC o Q.SPECL [`m`, `fn_plus f`, `fn_minus f`,
        `pos_simple_fn_integral m (count n) (\i. PREIMAGE f {c i} INTER m_space m)
                                            (\i. (if 0 <= c i then c i else 0))`,
        `pos_simple_fn_integral m (count n) (\i. PREIMAGE f {c i} INTER m_space m)
                                            (\i. (if c i <= 0 then ~ c i else 0))`])
        nnfis_minus_nnfis_integral
   >> RW_TAC std_ss [pos_simple_fn_integral_def, real_sub]
   >> `!x. ~x = ~1 * x` by RW_TAC real_ss [] >> POP_ORW
   >> RW_TAC std_ss [GSYM REAL_SUM_IMAGE_CMUL, FINITE_COUNT, GSYM REAL_SUM_IMAGE_ADD]
   >> `(\i.
         (if 0 <= c i then c i else 0) * measure m (PREIMAGE f {c i} INTER m_space m) +
         ~1 *
         ((if c i <= 0 then ~c i else 0) * measure m (PREIMAGE f {c i} INTER m_space m))) =
        (\i. c i * measure m (PREIMAGE f {c i} INTER m_space m))`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss []
            >> METIS_TAC [REAL_LE_TOTAL, REAL_LE_ANTISYM, REAL_MUL_LZERO, REAL_ADD_RID])
   >> POP_ORW
   >> `FINITE (count n)` by RW_TAC std_ss [FINITE_COUNT]
   >> (MP_TAC o Q.ISPEC `c:num->real` o UNDISCH o Q.ISPEC `count n` o GSYM) REAL_SUM_IMAGE_IMAGE
   >> Know `INJ c (count n) (IMAGE c (count n))`
   >- (FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, IN_IMAGE] >> METIS_TAC [])
   >> SIMP_TAC std_ss [] >> STRIP_TAC >> STRIP_TAC
   >> POP_ASSUM (MP_TAC o Q.SPEC `(\x:real. x * measure m (PREIMAGE f {x} INTER m_space m))`)
   >> RW_TAC std_ss [o_DEF]
   >> POP_ASSUM (K ALL_TAC) >> POP_ASSUM (K ALL_TAC)
   >> `(IMAGE c (count n)) = (IMAGE f (m_space m))`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_IMAGE]
            >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
            >> METIS_TAC [])
   >> RW_TAC std_ss []
QED

val integral_cmul_indicator = store_thm
  ("integral_cmul_indicator",
  ``!m s c. measure_space m /\ s IN measurable_sets m ==>
           (integral m (\x. c * indicator_fn s x) = c * (measure m s))``,
   METIS_TAC [integral_times, integral_indicator_fn]);

val integral_zero = store_thm
  ("integral_zero",
  ``!m. measure_space m ==> (integral m (\x. 0) = 0)``,
   rpt STRIP_TAC
   >> (MP_TAC o Q.SPECL [`m`, `{}`, `0`]) integral_cmul_indicator
   >> ASM_SIMP_TAC real_ss [] >> FULL_SIMP_TAC std_ss [measure_space_def, SIGMA_ALGEBRA, subsets_def]);

val finite_integral_on_set = store_thm
  ("finite_integral_on_set",
  ``!m f a. measure_space m /\ FINITE (m_space m) /\
             f IN borel_measurable (m_space m, measurable_sets m) /\ a IN measurable_sets m  ==>
                (integral m (\x. f x * indicator_fn a x) =
                 SIGMA (\r. r * measure m (PREIMAGE f {r} INTER a)) (IMAGE f a))``,
   rpt STRIP_TAC
   >> (MP_TAC o Q.SPECL [`m`, `(\x. f x * indicator_fn a x)`]) finite_space_integral_reduce
   >> `(\x. f x * indicator_fn a x) IN borel_measurable (m_space m,measurable_sets m)`
        by (MATCH_MP_TAC borel_measurable_times_borel_measurable
            >> ASM_SIMP_TAC std_ss []
            >> MATCH_MP_TAC borel_measurable_indicator
            >> FULL_SIMP_TAC std_ss [measure_space_def, subsets_def])
   >> `a SUBSET m_space m` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE]
   >> RW_TAC std_ss [finite_space_integral_def]
   >> `FINITE a` by METIS_TAC [SUBSET_FINITE]
   >> Cases_on `0 IN (IMAGE f a)`
   >- (`(IMAGE f a) =
        0 INSERT (IMAGE f a)`
                by METIS_TAC [IN_INSERT, EXTENSION]
       >> POP_ORW
       >> RW_TAC real_ss [REAL_SUM_IMAGE_THM, FINITE_INSERT, IMAGE_FINITE]
       >> `0 IN (IMAGE (\x. f x * indicator_fn a x) (m_space m))`
                by (FULL_SIMP_TAC std_ss [IN_IMAGE] >> Q.EXISTS_TAC `x`
                    >> RW_TAC real_ss [indicator_fn_def]
                    >> `a SUBSET m_space m`
                                by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE]
                    >> FULL_SIMP_TAC std_ss [SUBSET_DEF])
       >> `(IMAGE (\x. f x * indicator_fn a x) (m_space m)) =
                0 INSERT (IMAGE (\x. f x * indicator_fn a x) (m_space m))`
                by METIS_TAC [IN_INSERT, EXTENSION]
       >> POP_ORW
       >> RW_TAC real_ss [REAL_SUM_IMAGE_THM, FINITE_INSERT, IMAGE_FINITE]
       >> `(IMAGE (\x. f x * indicator_fn a x) (m_space m) DELETE 0) =
           (IMAGE f a DELETE 0)`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC real_ss [IN_IMAGE, IN_DELETE, indicator_fn_def]
                    >> Cases_on `x = 0` >> RW_TAC real_ss []
                    >> EQ_TAC >> RW_TAC real_ss [REAL_ENTIRE]
                    >> Q.EXISTS_TAC `x'` >> Cases_on `x' IN a` >> FULL_SIMP_TAC real_ss [REAL_ENTIRE, SUBSET_DEF])
       >> POP_ORW
       >> ASM_SIMP_TAC std_ss [Once REAL_SUM_IMAGE_IN_IF, FINITE_DELETE, IMAGE_FINITE]
       >> `(\r. (if r IN IMAGE f a DELETE 0 then
                        r * measure m (PREIMAGE (\x. f x * indicator_fn a x) {r} INTER m_space m)
                else 0)) =
           (\r. if r IN IMAGE f a DELETE 0 then
                (\r. r * measure m (PREIMAGE f {r} INTER a)) r
                else 0)`
                by (RW_TAC real_ss [FUN_EQ_THM, IN_DELETE, IN_IMAGE]
                    >> RW_TAC real_ss [indicator_fn_def]
                    >> Suff `(PREIMAGE (\x. f x * (if x IN a then 1 else 0)) {f x} INTER m_space m) =
                              (PREIMAGE f {f x} INTER a)`
                    >- RW_TAC std_ss []
                    >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC real_ss [IN_INTER, IN_PREIMAGE, IN_SING]
                    >> Cases_on `x' IN a` >> RW_TAC real_ss [] >> FULL_SIMP_TAC std_ss [SUBSET_DEF])
       >> POP_ORW
       >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF, FINITE_DELETE, IMAGE_FINITE])
   >> `IMAGE f a = (IMAGE f a) DELETE 0`
        by METIS_TAC [DELETE_NON_ELEMENT]
   >> POP_ORW
   >> Cases_on `0 IN (IMAGE (\x. f x * indicator_fn a x) (m_space m))`
   >- (`(IMAGE (\x. f x * indicator_fn a x) (m_space m)) =
                0 INSERT (IMAGE (\x. f x * indicator_fn a x) (m_space m))`
                by METIS_TAC [IN_INSERT, EXTENSION]
       >> POP_ORW
       >> RW_TAC real_ss [REAL_SUM_IMAGE_THM, FINITE_INSERT, IMAGE_FINITE]
       >> `(IMAGE (\x. f x * indicator_fn a x) (m_space m) DELETE 0) =
           (IMAGE f a DELETE 0)`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC real_ss [IN_IMAGE, IN_DELETE, indicator_fn_def]
                    >> Cases_on `x = 0` >> RW_TAC real_ss []
                    >> EQ_TAC >> RW_TAC real_ss [REAL_ENTIRE]
                    >> Q.EXISTS_TAC `x'` >> Cases_on `x' IN a` >> FULL_SIMP_TAC real_ss [REAL_ENTIRE, SUBSET_DEF])
       >> POP_ORW
       >> ASM_SIMP_TAC std_ss [Once REAL_SUM_IMAGE_IN_IF, FINITE_DELETE, IMAGE_FINITE]
       >> `(\r. (if r IN IMAGE f a DELETE 0 then
                        r * measure m (PREIMAGE (\x. f x * indicator_fn a x) {r} INTER m_space m)
                else 0)) =
           (\r. if r IN IMAGE f a DELETE 0 then
                (\r. r * measure m (PREIMAGE f {r} INTER a)) r
                else 0)`
                by (RW_TAC real_ss [FUN_EQ_THM, IN_DELETE, IN_IMAGE]
                    >> RW_TAC real_ss [indicator_fn_def]
                    >> Suff `(PREIMAGE (\x. f x * (if x IN a then 1 else 0)) {f x} INTER m_space m) =
                              (PREIMAGE f {f x} INTER a)`
                    >- RW_TAC std_ss []
                    >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC real_ss [IN_INTER, IN_PREIMAGE, IN_SING]
                    >> Cases_on `x' IN a` >> RW_TAC real_ss [] >> FULL_SIMP_TAC std_ss [SUBSET_DEF])
       >> POP_ORW
       >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF, FINITE_DELETE, IMAGE_FINITE])
   >> `(IMAGE (\x. f x * indicator_fn a x) (m_space m)) =
           (IMAGE f a) DELETE 0`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC real_ss [IN_IMAGE, IN_DELETE, indicator_fn_def]
                    >> FULL_SIMP_TAC real_ss [IN_IMAGE, indicator_fn_def, REAL_ENTIRE, SUBSET_DEF]
                    >> EQ_TAC
                    >- (RW_TAC real_ss [REAL_ENTIRE]
                        >- (Q.EXISTS_TAC `x'` >> Cases_on `x' IN a` >> FULL_SIMP_TAC real_ss [REAL_ENTIRE]
                            >> METIS_TAC [REAL_ARITH ``~((1:real) = 0)``])
                        >> METIS_TAC [REAL_ARITH ``~((1:real) = 0)``, REAL_ENTIRE])
                    >> RW_TAC real_ss [REAL_ENTIRE]
                    >> Q.EXISTS_TAC `x'` >> RW_TAC real_ss [])
   >> POP_ORW
   >> ASM_SIMP_TAC std_ss [Once REAL_SUM_IMAGE_IN_IF, FINITE_DELETE, IMAGE_FINITE]
   >> `(\r. (if r IN IMAGE f a DELETE 0 then
                        r * measure m (PREIMAGE (\x. f x * indicator_fn a x) {r} INTER m_space m)
                else 0)) =
           (\r. if r IN IMAGE f a DELETE 0 then
                (\r. r * measure m (PREIMAGE f {r} INTER a)) r
                else 0)`
                by (RW_TAC real_ss [FUN_EQ_THM, IN_DELETE, IN_IMAGE]
                    >> RW_TAC real_ss [indicator_fn_def]
                    >> Suff `(PREIMAGE (\x. f x * (if x IN a then 1 else 0)) {f x} INTER m_space m) =
                              (PREIMAGE f {f x} INTER a)`
                    >- RW_TAC std_ss []
                    >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC real_ss [IN_INTER, IN_PREIMAGE, IN_SING]
                    >> Cases_on `x' IN a` >> RW_TAC real_ss [] >> FULL_SIMP_TAC std_ss [SUBSET_DEF])
   >> POP_ORW
   >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF, FINITE_DELETE, IMAGE_FINITE]);

val finite_space_POW_integral_reduce = store_thm
  ("finite_space_POW_integral_reduce",
  ``!m f. measure_space m /\
         (POW (m_space m) = measurable_sets m) /\
          FINITE (m_space m) ==>
         (integral m f = SIGMA (\x. f x * measure m {x}) (m_space m))``,
   rpt STRIP_TAC
   >> `f IN borel_measurable (m_space m, measurable_sets m)`
        by (Q.PAT_X_ASSUM `P = Q` (MP_TAC o GSYM)
            >> RW_TAC std_ss [borel_measurable_le_iff, IN_POW, SUBSET_DEF, GSPECIFICATION])
   >> `?c n. BIJ c (count n) (m_space m)` by RW_TAC std_ss [GSYM FINITE_BIJ_COUNT_EQ]
   >> `pos_simple_fn m (fn_plus f)
        (count n) (\i. {c i}) (\i. if 0 <= f(c i) then f(c i) else 0) /\
        pos_simple_fn m (fn_minus f)
        (count n) (\i. {c i}) (\i. if f(c i) <= 0 then ~ f(c i) else 0)`
    by (RW_TAC std_ss [pos_simple_fn_def, FINITE_COUNT]
   >| [RW_TAC real_ss [fn_plus_def],
       `FINITE (count n)` by RW_TAC std_ss [FINITE_COUNT]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `count n`) REAL_SUM_IMAGE_IN_IF]
       >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
       >> `?i. i IN count n /\ (t = c i)` by METIS_TAC []
       >> `(\x. (if x IN count n then (if 0 <= f(c x) then f(c x) else 0) *
                        indicator_fn {c x} t else 0)) =
                (\x. if (x = i) /\ 0 <= f (c i) then f(c i) else 0)`
                by (ONCE_REWRITE_TAC [FUN_EQ_THM] >> POP_ORW
                    >> STRIP_TAC >> SIMP_TAC real_ss [indicator_fn_def, IN_SING]
                    >> reverse (Cases_on `x IN count n`) >- METIS_TAC []
                    >> ASM_SIMP_TAC std_ss []
                    >> Cases_on `x = i`
                    >> RW_TAC real_ss []
                    >> METIS_TAC [])
       >> POP_ORW
       >> `count n = i INSERT ((count n) DELETE i)`
                by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DELETE] >> METIS_TAC [])
       >> POP_ORW
       >> ASM_SIMP_TAC std_ss [FINITE_INSERT, FINITE_DELETE, FINITE_COUNT,
                               REAL_SUM_IMAGE_THM, DELETE_DELETE]
       >> `FINITE (count n DELETE i)` by RW_TAC std_ss [FINITE_COUNT, FINITE_DELETE]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `count n DELETE i`) REAL_SUM_IMAGE_IN_IF]
       >> SIMP_TAC std_ss [IN_DELETE]
       >> (MP_TAC o Q.SPECL [`\x.0`, `0`] o UNDISCH o Q.ISPEC `count n DELETE i`)
                REAL_SUM_IMAGE_FINITE_CONST
       >> RW_TAC real_ss [fn_plus_def],
       Q.PAT_X_ASSUM `P = Q` (MP_TAC o GSYM)
       >> RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_SING]
       >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF],
       RW_TAC real_ss [],
       RW_TAC std_ss [DISJOINT_DEF, IN_SING, IN_INTER, NOT_IN_EMPTY, Once EXTENSION]
        >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF] >> METIS_TAC [],
        ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_SING]
        >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
        >> METIS_TAC [],
        RW_TAC real_ss [fn_minus_def, REAL_LT_IMP_LE, REAL_LE_RNEG]
        >> FULL_SIMP_TAC std_ss [GSYM real_lt, REAL_LT_IMP_LE],
        `FINITE (count n)` by RW_TAC std_ss [FINITE_COUNT]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `count n`) REAL_SUM_IMAGE_IN_IF]
       >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
       >> `?i. i IN count n /\ (t = c i)` by METIS_TAC []
       >> `(\x. (if x IN count n then (if f(c x) <= 0 then ~f(c x) else 0) *
                        indicator_fn {c x} t else 0)) =
                (\x. if (x = i) /\ f (c i) <= 0 then ~f(c i) else 0)`
                by (ONCE_REWRITE_TAC [FUN_EQ_THM] >> POP_ORW
                    >> STRIP_TAC >> SIMP_TAC real_ss [indicator_fn_def, IN_SING]
                    >> reverse (Cases_on `x IN count n`) >- METIS_TAC []
                    >> ASM_SIMP_TAC std_ss []
                    >> Cases_on `x = i`
                    >> RW_TAC real_ss []
                    >> METIS_TAC [])
       >> POP_ORW
       >> `count n = i INSERT ((count n) DELETE i)`
                by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DELETE] >> METIS_TAC [])
       >> POP_ORW
       >> ASM_SIMP_TAC std_ss [FINITE_INSERT, FINITE_DELETE, FINITE_COUNT,
                               REAL_SUM_IMAGE_THM, DELETE_DELETE]
       >> `FINITE (count n DELETE i)` by RW_TAC std_ss [FINITE_COUNT, FINITE_DELETE]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.ISPEC `count n DELETE i`) REAL_SUM_IMAGE_IN_IF]
       >> SIMP_TAC std_ss [IN_DELETE]
       >> (MP_TAC o Q.SPECL [`\x.0`, `0`] o UNDISCH o Q.ISPEC `count n DELETE i`)
                REAL_SUM_IMAGE_FINITE_CONST
       >> RW_TAC real_ss [fn_minus_def] >> METIS_TAC [real_lt, REAL_LT_ANTISYM, REAL_LE_ANTISYM, REAL_NEG_0],
        Q.PAT_X_ASSUM `P = Q` (MP_TAC o GSYM)
       >> RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_SING]
       >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF],
        RW_TAC real_ss [REAL_LE_RNEG],
        RW_TAC std_ss [Once EXTENSION, DISJOINT_DEF, IN_SING, IN_INTER, NOT_IN_EMPTY]
        >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF] >> METIS_TAC [],
        ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_SING]
        >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
        >> METIS_TAC []])
   >> `pos_simple_fn_integral m (count n) (\i. {c i}) (\i. (if 0 <= f(c i) then f(c i) else 0))
        IN nnfis m (fn_plus f)`
        by (MATCH_MP_TAC psfis_nnfis
            >> RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
            >> Q.EXISTS_TAC `((count n), (\i. {c i}), (\i. (if 0 <= f(c i) then f(c i) else 0)))`
            >> RW_TAC std_ss []
            >> Q.EXISTS_TAC `((count n), (\i. {c i}), (\i. (if 0 <= f(c i) then f(c i) else 0)))`
            >> RW_TAC std_ss [])
   >> `pos_simple_fn_integral m (count n) (\i. {c i}) (\i. (if f(c i) <= 0 then ~f(c i) else 0))
        IN nnfis m (fn_minus f)`
        by (MATCH_MP_TAC psfis_nnfis
            >> RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
            >> Q.EXISTS_TAC `((count n), (\i. {c i}), (\i. (if f(c i) <= 0 then ~f(c i) else 0)))`
            >> RW_TAC std_ss []
            >> Q.EXISTS_TAC `((count n), (\i. {c i}), (\i. (if f(c i) <= 0 then ~f(c i) else 0)))`
            >> RW_TAC std_ss [])
   >> `!f. (\t. fn_plus f t - fn_minus f t) = f`
        by (RW_TAC real_ss [fn_plus_def, fn_minus_def, Once FUN_EQ_THM]
            >> RW_TAC real_ss [])
   >> (MP_TAC o Q.SPECL [`m`, `fn_plus f`, `fn_minus f`,
        `pos_simple_fn_integral m (count n) (\i. {c i}) (\i. (if 0 <= f(c i) then f(c i) else 0))`,
        `pos_simple_fn_integral m (count n) (\i. {c i}) (\i. (if f(c i) <= 0 then ~f(c i) else 0))`])
        nnfis_minus_nnfis_integral
   >> RW_TAC std_ss [pos_simple_fn_integral_def, real_sub]
   >> `!x. ~x = ~1 * x` by RW_TAC real_ss [] >> POP_ORW
   >> RW_TAC std_ss [GSYM REAL_SUM_IMAGE_CMUL, FINITE_COUNT, GSYM REAL_SUM_IMAGE_ADD]
   >> `(\i.
         (if 0 <= f (c i) then f (c i) else 0) * measure m {c i} +
         ~1 * ((if f (c i) <= 0 then ~f (c i) else 0) * measure m {c i})) =
        (\i. f (c i) * measure m {c i})`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss []
            >> METIS_TAC [REAL_LE_TOTAL, REAL_LE_ANTISYM, REAL_MUL_LZERO, REAL_ADD_RID])
   >> POP_ORW
   >> `FINITE (count n)` by RW_TAC std_ss [FINITE_COUNT]
   >> (MP_TAC o Q.ISPEC `c:num->'a` o UNDISCH o Q.ISPEC `count n` o GSYM) REAL_SUM_IMAGE_IMAGE
   >> Know `INJ c (count n) (IMAGE c (count n))`
   >- (FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, IN_IMAGE] >> METIS_TAC [])
   >> SIMP_TAC std_ss [] >> STRIP_TAC >> STRIP_TAC
   >> POP_ASSUM (MP_TAC o Q.SPEC `(\x:'a. f x * measure m {x})`)
   >> RW_TAC std_ss [o_DEF]
   >> POP_ASSUM (K ALL_TAC) >> POP_ASSUM (K ALL_TAC)
   >> `(IMAGE c (count n)) = (m_space m)`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_IMAGE]
            >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
            >> METIS_TAC [])
   >> RW_TAC std_ss []);

Theorem finite_POW_RN_deriv_reduce :
    !m v. measure_space m /\
          FINITE (m_space m) /\
          measure_space (m_space m, measurable_sets m, v) /\
         (POW (m_space m) = measurable_sets m) /\
         (!x. (measure m {x} = 0) ==> (v {x} = 0)) ==>
         (!x. x IN m_space m /\ measure m {x} <> 0 ==>
             (RN_deriv m v x = v {x} / (measure m {x})))
Proof
    RW_TAC std_ss [RN_deriv_def]
 >> Suff `(\f. f x = v {x} / measure m {x})
            (@f. f IN borel_measurable (m_space m,measurable_sets m) /\
                 !a. a IN measurable_sets m ==>
                    (integral m (\x. f x * indicator_fn a x) = v a))`
 >- RW_TAC std_ss []
 >> MATCH_MP_TAC SELECT_ELIM_THM
 >> RW_TAC std_ss []
 >- (Q.EXISTS_TAC `\x. v {x} / (measure m {x})`
       >> SIMP_TAC std_ss []
       >> STRONG_CONJ_TAC
       >- (Q.PAT_X_ASSUM `P = Q` (MP_TAC o GSYM)
            >> RW_TAC std_ss [borel_measurable_le_iff]
            >> RW_TAC std_ss [IN_POW, SUBSET_DEF, GSPECIFICATION])
       >> RW_TAC std_ss []
       >> (MP_TAC o Q.ISPECL [`(m :('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> real))`,
                              `\x':'a. v {x'} / measure m {x'} * indicator_fn a x'`])
             finite_space_POW_integral_reduce
       >> RW_TAC std_ss []
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `m_space m`) REAL_SUM_IMAGE_IN_IF]
       >> `(\x.
         (if x IN m_space m then
            (\x'. v {x'} / measure m {x'} * indicator_fn a x' * measure m {x'}) x
          else
            0)) =
           (\x. if x IN m_space m then
                (\x'. (\x'. v {x'}) x' * indicator_fn a x') x else 0)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC std_ss [real_div]
            >> Cases_on `measure m {x'} = 0`
            >- RW_TAC real_ss []
            >> `v {x'} * inv (measure m {x'}) * indicator_fn a x' * measure m {x'} =
                (inv (measure m {x'}) * measure m {x'}) * v {x'} * indicator_fn a x'`
                by REAL_ARITH_TAC
            >> POP_ORW
            >> RW_TAC real_ss [REAL_MUL_LINV])
       >> POP_ORW
       >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF]
       >> `a SUBSET m_space m` by METIS_TAC [IN_POW]
       >> `m_space m = a UNION (m_space m DIFF a)`
                by (ONCE_REWRITE_TAC [EXTENSION] \\
                    RW_TAC std_ss [IN_DIFF, IN_UNION] >> METIS_TAC [SUBSET_DEF])
       >> POP_ORW
       >> `DISJOINT a (m_space m DIFF a)`
                by (RW_TAC std_ss [IN_DISJOINT, IN_DIFF] >> DECIDE_TAC)
       >> `SIGMA (\x'. v {x'} * indicator_fn a x') (a UNION (m_space m DIFF a)) =
           SIGMA (\x'. v {x'} * indicator_fn a x') a +
           SIGMA (\x'. v {x'} * indicator_fn a x') (m_space m DIFF a)`
        by (MATCH_MP_TAC REAL_SUM_IMAGE_DISJOINT_UNION >> METIS_TAC [FINITE_DIFF, SUBSET_FINITE])
       >> POP_ORW
       >> `FINITE a` by METIS_TAC [SUBSET_FINITE]
       >> `FINITE (m_space m DIFF a)` by RW_TAC std_ss [FINITE_DIFF]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `a`) REAL_SUM_IMAGE_IN_IF]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `m_space m DIFF a`) REAL_SUM_IMAGE_IN_IF]
       >> `(\x.
         (if x IN m_space m DIFF a then
            (\x'. v {x'} * indicator_fn a x') x
          else
            0)) = (\x. 0)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [IN_DIFF, indicator_fn_def])
       >> RW_TAC real_ss [REAL_SUM_IMAGE_0]
       >> `(\x'. (if x' IN a then v {x'} * indicator_fn a x' else 0)) =
           (\x'. if x' IN a then (\x'. v {x'}) x' else 0)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [indicator_fn_def])
       >> POP_ORW >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF]
       >> `!x. v = measure (m_space m,measurable_sets m,v)` by RW_TAC std_ss [measure_def]
       >> POP_ORW
       >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
       >> MATCH_MP_TAC MEASURE_REAL_SUM_IMAGE
       >> RW_TAC std_ss [measurable_sets_def]
       >> METIS_TAC [SUBSET_DEF, IN_POW, IN_SING])
   >> POP_ASSUM (MP_TAC o Q.SPEC `{x}`)
   >> `{x} IN measurable_sets m` by METIS_TAC [SUBSET_DEF, IN_POW, IN_SING]
   >> ASM_SIMP_TAC std_ss []
   >> (MP_TAC o Q.SPECL [`m`,`(\x''. x' x'' * indicator_fn {x} x'')`]) finite_space_POW_integral_reduce
   >> ASM_SIMP_TAC std_ss []
   >> STRIP_TAC >> POP_ASSUM (K ALL_TAC)
   >> `x IN m_space m` by METIS_TAC [IN_POW, SUBSET_DEF, IN_SING]
   >> `m_space m = {x} UNION (m_space m DIFF {x})`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, IN_DIFF, IN_SING] >> METIS_TAC [])
   >> POP_ORW
   >> `DISJOINT {x} (m_space m DIFF {x})`
                by (RW_TAC std_ss [IN_DISJOINT, IN_DIFF, IN_SING] >> METIS_TAC [])
   >> `SIGMA (\x''. x' x'' * indicator_fn {x} x'' * measure m {x''}) ({x} UNION (m_space m DIFF {x})) =
           SIGMA (\x''. x' x'' * indicator_fn {x} x'' * measure m {x''}) {x} +
           SIGMA (\x''. x' x'' * indicator_fn {x} x'' * measure m {x''}) (m_space m DIFF {x})`
        by (MATCH_MP_TAC REAL_SUM_IMAGE_DISJOINT_UNION >> METIS_TAC [FINITE_DIFF, FINITE_SING])
   >> POP_ORW
   >> SIMP_TAC std_ss [REAL_SUM_IMAGE_SING]
   >> `FINITE (m_space m DIFF {x})` by RW_TAC std_ss [FINITE_DIFF]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `m_space m DIFF {x}`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x''.
          (if x'' IN m_space m DIFF {x} then
             (\x''. x' x'' * indicator_fn {x} x'' * measure m {x''}) x''
           else
             0)) = (\x. 0)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [IN_DIFF, indicator_fn_def])
   >> POP_ORW
   >> ASM_SIMP_TAC real_ss [REAL_SUM_IMAGE_0]
   >> `0 < measure m {x}`
        by METIS_TAC [measure_space_def, positive_def, REAL_LE_LT]
   >> ASM_SIMP_TAC real_ss [REAL_EQ_RDIV_EQ, indicator_fn_def, IN_SING]
QED

val finite_POW_prod_measure_reduce = store_thm
  ("finite_POW_prod_measure_reduce",
  ``!m0 m1. measure_space m0 /\ measure_space m1 /\
             FINITE (m_space m0) /\ FINITE (m_space m1) /\
             (POW (m_space m0) = measurable_sets m0) /\
             (POW (m_space m1) = measurable_sets m1) ==>
        (!a0 a1. a0 IN measurable_sets m0 /\
                 a1 IN measurable_sets m1 ==>
                ((prod_measure m0 m1) (a0 CROSS a1) =
                 measure m0 a0 * measure m1 a1))``,
   RW_TAC std_ss [prod_measure_def, measure_def,
                  finite_space_POW_integral_reduce]
   >> `(m_space m0) = a0 UNION ((m_space m0) DIFF a0)`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, IN_DIFF]
            >> METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_DEF])
   >> POP_ORW
   >> `DISJOINT a0 (m_space m0 DIFF a0)`
        by (RW_TAC std_ss [IN_DISJOINT, IN_DIFF] >> DECIDE_TAC)
   >> `FINITE a0` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_FINITE]
   >> RW_TAC std_ss [REAL_SUM_IMAGE_DISJOINT_UNION, FINITE_DIFF]
   >> `FINITE (m_space m0 DIFF a0)` by RW_TAC std_ss [FINITE_DIFF]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `(m_space m0 DIFF a0)`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x.
         (if x IN m_space m0 DIFF a0 then
            (\s0.
               measure m1 (PREIMAGE (\s1. (s0,s1)) (a0 CROSS a1)) *
               measure m0 {s0}) x
          else
            0)) = (\x. 0)`
        by (RW_TAC std_ss [FUN_EQ_THM, IN_DIFF]
            >> RW_TAC std_ss []
            >> `PREIMAGE (\s1. (x,s1)) (a0 CROSS a1) = {}`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [NOT_IN_EMPTY, IN_PREIMAGE, IN_CROSS])
            >> RW_TAC real_ss [MEASURE_EMPTY])
   >> RW_TAC real_ss [REAL_SUM_IMAGE_0]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `a0`) REAL_SUM_IMAGE_IN_IF]
   >> `(\x.
         (if x IN a0 then
            (\s0.
               measure m1 (PREIMAGE (\s1. (s0,s1)) (a0 CROSS a1)) *
               measure m0 {s0}) x
          else
            0)) =
        (\x. if x IN a0 then
                (\s0. measure m1 a1 * measure m0 {s0}) x else 0)`
        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC std_ss []
            >> `PREIMAGE (\s1. (x,s1)) (a0 CROSS a1) = a1`
                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_PREIMAGE, IN_CROSS])
            >> RW_TAC std_ss [])
   >> POP_ORW >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_IN_IF]
   >> `(\x. measure m1 a1 * measure m0 {x}) =
       (\x. measure m1 a1 * (\x. measure m0 {x}) x)`
        by RW_TAC std_ss []
   >> POP_ORW >> ASM_SIMP_TAC std_ss [REAL_SUM_IMAGE_CMUL]
   >> Suff `SIGMA (\x. measure m0 {x}) a0 = measure m0 a0`
   >- RW_TAC real_ss [REAL_MUL_COMM]
   >> MATCH_MP_TAC (GSYM MEASURE_REAL_SUM_IMAGE)
   >> METIS_TAC [IN_SING, IN_POW, SUBSET_DEF]);

val measure_space_finite_prod_measure_POW1 = store_thm
  ("measure_space_finite_prod_measure_POW1",
  ``!m0 m1. measure_space m0 /\ measure_space m1 /\
             FINITE (m_space m0) /\ FINITE (m_space m1) /\
             (POW (m_space m0) = measurable_sets m0) /\
             (POW (m_space m1) = measurable_sets m1) ==>
        measure_space (prod_measure_space m0 m1)``,
   rpt STRIP_TAC
   >> RW_TAC std_ss [prod_measure_space_def]
   >> `(m_space m0 CROSS m_space m1,
       subsets
         (sigma (m_space m0 CROSS m_space m1)
            (prod_sets (measurable_sets m0) (measurable_sets m1))),
       prod_measure m0 m1) =
        (space (sigma (m_space m0 CROSS m_space m1)
            (prod_sets (measurable_sets m0) (measurable_sets m1))),
        subsets
         (sigma (m_space m0 CROSS m_space m1)
            (prod_sets (measurable_sets m0) (measurable_sets m1))),
       prod_measure m0 m1)`
        by RW_TAC std_ss [sigma_def, space_def]
   >> POP_ORW
   >> MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces
   >> RW_TAC std_ss [m_space_def, SPACE_SIGMA, FINITE_CROSS,
                     measurable_sets_def, m_space_def, SIGMA_REDUCE]
   >| [MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA
       >> RW_TAC std_ss [subset_class_def, prod_sets_def, GSPECIFICATION, IN_CROSS]
       >> (MP_TAC o Q.ISPEC `(x' :('a -> bool) # ('b -> bool))`) pair_CASES
       >> RW_TAC std_ss [] >> FULL_SIMP_TAC std_ss [PAIR_EQ]
       >> RW_TAC std_ss [SUBSET_DEF, IN_CROSS]
       >> (MP_TAC o Q.ISPEC `(x :('a # 'b))`) pair_CASES
       >> RW_TAC std_ss []
       >> FULL_SIMP_TAC std_ss [FST, SND]
       >> METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_DEF],
       RW_TAC std_ss [positive_def, measure_def, measurable_sets_def]
       >- (`{} = {} CROSS {}` by RW_TAC std_ss [CROSS_EMPTY]
           >> POP_ORW
           >> METIS_TAC [finite_POW_prod_measure_reduce,
                         measure_space_def, SIGMA_ALGEBRA, subsets_def, space_def,
                         MEASURE_EMPTY, REAL_MUL_LZERO])
       >> RW_TAC std_ss [prod_measure_def, finite_space_POW_integral_reduce]
       >> MATCH_MP_TAC REAL_SUM_IMAGE_POS
       >> RW_TAC std_ss [] >> MATCH_MP_TAC REAL_LE_MUL
       >> FULL_SIMP_TAC std_ss [measure_space_def, positive_def]
       >> `(PREIMAGE (\s1. (x,s1)) s) SUBSET m_space m1`
        by (RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
            >> FULL_SIMP_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER, GSPECIFICATION]
            >> Q.PAT_X_ASSUM `!s'. P s' ==> s IN s'`
                (MP_TAC o Q.SPEC `POW (m_space m0 CROSS m_space m1)`)
            >> SIMP_TAC std_ss [POW_SIGMA_ALGEBRA]
            >> `prod_sets (measurable_sets m0) (measurable_sets m1) SUBSET
                POW (m_space m0 CROSS m_space m1)`
                by (RW_TAC std_ss [SUBSET_DEF, IN_POW, IN_CROSS, prod_sets_def, GSPECIFICATION]
                    >> (MP_TAC o Q.ISPEC `(x''' :('a -> bool) # ('b -> bool))`) pair_CASES
                    >> RW_TAC std_ss [] >> FULL_SIMP_TAC std_ss [PAIR_EQ]
                    >> `x'''' IN q CROSS r` by RW_TAC std_ss []
                    >> FULL_SIMP_TAC std_ss [IN_CROSS]
                    >> METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_DEF, IN_POW])
            >> ASM_SIMP_TAC std_ss []
            >> RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS]
            >> METIS_TAC [SND])
       >> METIS_TAC [IN_POW, IN_SING, SUBSET_DEF],
       RW_TAC std_ss [additive_def, measure_def, measurable_sets_def]
       >> RW_TAC std_ss [prod_measure_def, finite_space_POW_integral_reduce,
                         GSYM REAL_SUM_IMAGE_ADD]
       >> ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `m_space m0`) REAL_SUM_IMAGE_IN_IF]
       >> Suff `(\x.
         (if x IN m_space m0 then
            (\s0.
               measure m1 (PREIMAGE (\s1. (s0,s1)) (s UNION t)) *
               measure m0 {s0}) x
          else
            0)) =
        (\x.
         (if x IN m_space m0 then
            (\s0.
               measure m1 (PREIMAGE (\s1. (s0,s1)) s) * measure m0 {s0} +
               measure m1 (PREIMAGE (\s1. (s0,s1)) t) * measure m0 {s0}) x
          else
            0))`
       >- RW_TAC std_ss []
       >> RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC std_ss []
       >> `measure m1 (PREIMAGE (\s1. (x,s1)) s) * measure m0 {x} +
           measure m1 (PREIMAGE (\s1. (x,s1)) t) * measure m0 {x} =
          (measure m1 (PREIMAGE (\s1. (x,s1)) s) +
           measure m1 (PREIMAGE (\s1. (x,s1)) t)) * measure m0 {x}`
                by REAL_ARITH_TAC
       >> POP_ORW
       >> RW_TAC std_ss [REAL_EQ_RMUL]
       >> DISJ2_TAC
       >> FULL_SIMP_TAC std_ss [sigma_def, subsets_def, IN_BIGINTER,
                                GSPECIFICATION]
       >> Q.PAT_X_ASSUM `!s. P s ==> t IN s`
                (MP_TAC o Q.SPEC `POW (m_space m0 CROSS m_space m1)`)
       >> Q.PAT_X_ASSUM `!ss. P ss ==> s IN s'`
                (MP_TAC o Q.SPEC `POW (m_space m0 CROSS m_space m1)`)
       >> SIMP_TAC std_ss [prod_sets_def, POW_SIGMA_ALGEBRA]
       >> `{s CROSS t | s IN measurable_sets m0 /\ t IN measurable_sets m1} SUBSET
                POW (m_space m0 CROSS m_space m1)`
        by (RW_TAC std_ss [Once SUBSET_DEF, GSPECIFICATION, IN_POW]
            >> (MP_TAC o Q.ISPEC `(x'' :('a -> bool) # ('b -> bool))`) pair_CASES
            >> RW_TAC std_ss [] >> FULL_SIMP_TAC std_ss [PAIR_EQ]
            >> RW_TAC std_ss [SUBSET_DEF, IN_CROSS]
            >> METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, SUBSET_DEF, IN_POW])
       >> ASM_SIMP_TAC std_ss []
       >> RW_TAC std_ss [IN_POW]
       >> MATCH_MP_TAC MEASURE_ADDITIVE
       >> Q.PAT_X_ASSUM `POW (m_space m1) = measurable_sets m1` (MP_TAC o GSYM)
       >> Q.PAT_X_ASSUM `POW (m_space m0) = measurable_sets m0` (MP_TAC o GSYM)
       >> FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_PREIMAGE, IN_CROSS, IN_DISJOINT]
       >> RW_TAC std_ss []
       >| [ METIS_TAC [SND],
            METIS_TAC [SND],
            ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, IN_PREIMAGE]]]);

val measure_space_finite_prod_measure_POW2 = store_thm
  ("measure_space_finite_prod_measure_POW2",
  ``!m0 m1. measure_space m0 /\ measure_space m1 /\
             FINITE (m_space m0) /\ FINITE (m_space m1) /\
             (POW (m_space m0) = measurable_sets m0) /\
             (POW (m_space m1) = measurable_sets m1) ==>
        measure_space (m_space m0 CROSS m_space m1,
                       POW (m_space m0 CROSS m_space m1),
                       prod_measure m0 m1)``,
   rpt STRIP_TAC
   >> `(m_space m0 CROSS m_space m1,
                       POW (m_space m0 CROSS m_space m1),
                       prod_measure m0 m1) =
        (space (m_space m0 CROSS m_space m1,
                       POW (m_space m0 CROSS m_space m1)),
        subsets
         (m_space m0 CROSS m_space m1,
                       POW (m_space m0 CROSS m_space m1)),
       prod_measure m0 m1)`
        by RW_TAC std_ss [space_def, subsets_def]
   >> POP_ORW
   >> MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces
   >> RW_TAC std_ss [POW_SIGMA_ALGEBRA, space_def, FINITE_CROSS, subsets_def]
   >- (RW_TAC std_ss [positive_def, measure_def, measurable_sets_def]
       >- (`{} = {} CROSS {}` by RW_TAC std_ss [CROSS_EMPTY]
           >> POP_ORW
           >> METIS_TAC [finite_POW_prod_measure_reduce,
                         measure_space_def, SIGMA_ALGEBRA, subsets_def, space_def,
                         MEASURE_EMPTY, REAL_MUL_LZERO])
       >> RW_TAC std_ss [prod_measure_def, finite_space_POW_integral_reduce]
       >> MATCH_MP_TAC REAL_SUM_IMAGE_POS
       >> RW_TAC std_ss [] >> MATCH_MP_TAC REAL_LE_MUL
       >> FULL_SIMP_TAC std_ss [measure_space_def, positive_def]
       >> `(PREIMAGE (\s1. (x,s1)) s) SUBSET m_space m1`
        by (RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
            >> FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS]
            >> METIS_TAC [SND])
       >> METIS_TAC [IN_POW, IN_SING, SUBSET_DEF])
   >> RW_TAC std_ss [additive_def, measure_def, measurable_sets_def]
   >> RW_TAC std_ss [prod_measure_def, finite_space_POW_integral_reduce,
                         GSYM REAL_SUM_IMAGE_ADD]
   >> ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `m_space m0`) REAL_SUM_IMAGE_IN_IF]
   >> Suff `(\x.
         (if x IN m_space m0 then
            (\s0.
               measure m1 (PREIMAGE (\s1. (s0,s1)) (s UNION t)) *
               measure m0 {s0}) x
          else
            0)) =
        (\x.
         (if x IN m_space m0 then
            (\s0.
               measure m1 (PREIMAGE (\s1. (s0,s1)) s) * measure m0 {s0} +
               measure m1 (PREIMAGE (\s1. (s0,s1)) t) * measure m0 {s0}) x
          else
            0))`
   >- RW_TAC std_ss []
   >> RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC std_ss []
   >> `measure m1 (PREIMAGE (\s1. (x,s1)) s) * measure m0 {x} +
           measure m1 (PREIMAGE (\s1. (x,s1)) t) * measure m0 {x} =
          (measure m1 (PREIMAGE (\s1. (x,s1)) s) +
           measure m1 (PREIMAGE (\s1. (x,s1)) t)) * measure m0 {x}`
                by REAL_ARITH_TAC
   >> POP_ORW
   >> RW_TAC std_ss [REAL_EQ_RMUL]
   >> DISJ2_TAC
   >> MATCH_MP_TAC MEASURE_ADDITIVE
   >> Q.PAT_X_ASSUM `POW (m_space m1) = measurable_sets m1` (MP_TAC o GSYM)
   >> Q.PAT_X_ASSUM `POW (m_space m0) = measurable_sets m0` (MP_TAC o GSYM)
   >> FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_PREIMAGE, IN_CROSS, IN_DISJOINT]
   >> RW_TAC std_ss []
   >| [ METIS_TAC [SND],
        METIS_TAC [SND],
        ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_UNION, IN_PREIMAGE] ]);

(* from examples/diningcryptos *)
Theorem countable_space_integral_reduce :
    !m f p n. measure_space m /\ positive m /\
              f IN borel_measurable (m_space m, measurable_sets m) /\
              countable (IMAGE f (m_space m)) /\
             ~(FINITE (IMAGE (fn_plus f) (m_space m))) /\
             ~(FINITE (IMAGE (fn_minus f) (m_space m))) /\
             (\r. r *
                  measure m (PREIMAGE (fn_minus f) {r} INTER m_space m)) o
                enumerate ((IMAGE (fn_minus f) (m_space m))) sums n /\
             (\r. r *
                  measure m (PREIMAGE (fn_plus f) {r} INTER m_space m)) o
                enumerate ((IMAGE (fn_plus f) (m_space m))) sums p ==>
             (integral m f = p - n)
Proof
    RW_TAC std_ss [integral_def]
 >> Suff `((@i. i IN nnfis m (fn_plus f)) = p) /\ ((@i. i IN nnfis m (fn_minus f)) = n)`
 >- RW_TAC std_ss []
 >> (CONJ_TAC >> MATCH_MP_TAC SELECT_UNIQUE >> RW_TAC std_ss [])
 >- (Suff `p IN nnfis m (fn_plus f)` >- METIS_TAC [nnfis_unique]
     >> MATCH_MP_TAC nnfis_mon_conv
     >> Know `BIJ (enumerate(IMAGE (fn_plus f) (m_space m))) UNIV (IMAGE (fn_plus f) (m_space m))`
     >- (`countable (IMAGE (fn_plus f) (m_space m))`
           by (MATCH_MP_TAC COUNTABLE_SUBSET
               >> Q.EXISTS_TAC `0 INSERT (IMAGE f (m_space m))`
               >> RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, fn_plus_def, countable_INSERT, IN_INSERT]
               >> METIS_TAC [])
         >> METIS_TAC [COUNTABLE_ALT_BIJ])
     >> DISCH_TAC
     >> FULL_SIMP_TAC std_ss [sums, BIJ_DEF, INJ_DEF, SURJ_DEF, IN_UNIV]
     >> Q.EXISTS_TAC `(\n t. if t IN m_space m /\
                                fn_plus f t IN IMAGE (enumerate (IMAGE (fn_plus f) (m_space m)))
                                               (count n)
                             then fn_plus f t else 0)`
     >> Q.EXISTS_TAC `(\n.
         sum (0,n)
           ((\r.
               r *
               measure m (PREIMAGE (fn_plus f) {r} INTER m_space m)) o
            enumerate (IMAGE (fn_plus f) (m_space m))))`
     >> ASM_SIMP_TAC std_ss []
     >> CONJ_TAC
     >- (RW_TAC std_ss [mono_convergent_def]
           >- (RW_TAC real_ss [IN_IMAGE, IN_COUNT, fn_plus_def] >> METIS_TAC [LESS_LESS_EQ_TRANS])
           >> RW_TAC std_ss [SEQ]
           >> `?N. enumerate (IMAGE (fn_plus f) (m_space m)) N = (fn_plus f) t`
                by METIS_TAC [IN_IMAGE]
           >> Q.EXISTS_TAC `SUC N`
           >> RW_TAC real_ss [GREATER_EQ, real_ge, IN_IMAGE, REAL_SUB_LZERO]
           >> FULL_SIMP_TAC std_ss [IN_COUNT]
           >> METIS_TAC [DECIDE ``!n:num. n < SUC n``, LESS_LESS_EQ_TRANS, fn_plus_def])
     >> STRIP_TAC >> MATCH_MP_TAC psfis_nnfis
     >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_COUNT]
     >> `(\t. (if t IN m_space m /\ fn_plus f t IN IMAGE (enumerate (IMAGE (fn_plus f) (m_space m))) (count n')
                 then fn_plus f t else  0)) =
                (\t. SIGMA (\i. (\i. enumerate (IMAGE (fn_plus f) (m_space m)) i) i *
                        indicator_fn ((\i. PREIMAGE (fn_plus f) {enumerate (IMAGE (fn_plus f) (m_space m)) i}
                                           INTER (m_space m)) i) t)
                     (count n'))`
                by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [IN_IMAGE]
                    >- (`count n' = x INSERT (count n')`
                                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INSERT] >> METIS_TAC [])
                        >> POP_ORW
                        >> RW_TAC std_ss [REAL_SUM_IMAGE_THM, FINITE_COUNT]
                        >> ONCE_REWRITE_TAC [(REWRITE_RULE [FINITE_COUNT] o
                                REWRITE_RULE [FINITE_DELETE] o Q.ISPEC `count n' DELETE x`) REAL_SUM_IMAGE_IN_IF]
                        >> RW_TAC real_ss [IN_DELETE, indicator_fn_def, IN_INTER, IN_SING, IN_PREIMAGE]
                        >> `(\x'. (if x' IN count n' /\ ~(x' = x) then
                                enumerate (IMAGE (fn_plus f) (m_space m)) x' *
                                (if enumerate (IMAGE (fn_plus f) (m_space m)) x =
                                enumerate (IMAGE (fn_plus f) (m_space m)) x'
                                then 1 else 0) else 0)) = (\x. 0)`
                                by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [] >> METIS_TAC [])
                        >> POP_ORW
                        >> RW_TAC real_ss [REAL_SUM_IMAGE_0, FINITE_COUNT, FINITE_DELETE])
                    >> FULL_SIMP_TAC real_ss [IN_IMAGE, indicator_fn_def, IN_INTER, IN_PREIMAGE, IN_SING]
                    >- RW_TAC real_ss [REAL_SUM_IMAGE_0, FINITE_COUNT, FINITE_DELETE]
                    >> ONCE_REWRITE_TAC [(REWRITE_RULE [FINITE_COUNT] o Q.ISPEC `count n'`)
                        REAL_SUM_IMAGE_IN_IF]
                    >> `(\x. (if x IN count n' then
                        (\i. enumerate (IMAGE (fn_plus f) (m_space m)) i *
                        (if (fn_plus f t = enumerate (IMAGE (fn_plus f) (m_space m)) i) /\
                         t IN m_space m then 1 else 0)) x else 0)) = (\x. 0)`
                        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [] >> METIS_TAC [])
                    >> POP_ORW
                    >> RW_TAC real_ss [REAL_SUM_IMAGE_0, FINITE_COUNT])
     >> POP_ORW
     >> `((\r. r * measure m (PREIMAGE (fn_plus f) {r} INTER m_space m)) o
                enumerate (IMAGE (fn_plus f) (m_space m))) =
                (\i. (\i. enumerate (IMAGE (fn_plus f) (m_space m)) i) i *
                        measure m ((\i.
                PREIMAGE (fn_plus f)
                  {enumerate (IMAGE (fn_plus f) (m_space m)) i} INTER
                m_space m) i))`
                by (RW_TAC std_ss [FUN_EQ_THM, o_DEF] >> RW_TAC real_ss [])
     >> POP_ORW
     >> MATCH_MP_TAC psfis_intro
     >> ASM_SIMP_TAC std_ss [FINITE_COUNT]
     >> reverse CONJ_TAC
     >- (FULL_SIMP_TAC real_ss [IN_IMAGE, fn_plus_def]
         >> METIS_TAC [REAL_LE_REFL])
     >> `(fn_plus f) IN borel_measurable (m_space m, measurable_sets m)`
                by METIS_TAC [fn_plus_fn_minus_borel_measurable]
     >> rpt STRIP_TAC
     >> `PREIMAGE (fn_plus f) {enumerate (IMAGE (fn_plus f) (m_space m)) i} INTER m_space m =
         {w | w IN m_space m /\ ((fn_plus f) w = (\w. enumerate (IMAGE (fn_plus f) (m_space m)) i) w)}`
           by (ONCE_REWRITE_TAC [EXTENSION] \\
               RW_TAC std_ss [GSPECIFICATION, IN_INTER, IN_PREIMAGE, IN_SING] \\
               DECIDE_TAC)
     >> POP_ORW
     >> MATCH_MP_TAC borel_measurable_eq_borel_measurable
     >> METIS_TAC [borel_measurable_const, measure_space_def])
 >> Suff `n IN nnfis m (fn_minus f)` >- METIS_TAC [nnfis_unique]
 >> MATCH_MP_TAC nnfis_mon_conv
 >> `BIJ (enumerate(IMAGE (fn_minus f) (m_space m))) UNIV (IMAGE (fn_minus f) (m_space m))`
      by (`countable (IMAGE (fn_minus f) (m_space m))`
            by (MATCH_MP_TAC COUNTABLE_SUBSET \\
                Q.EXISTS_TAC `0 INSERT (IMAGE abs (IMAGE f (m_space m)))` \\
                RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, abs, fn_minus_def, countable_INSERT,
                               IN_INSERT, image_countable] \\
                METIS_TAC []) \\
          METIS_TAC [COUNTABLE_ALT_BIJ])
 >> FULL_SIMP_TAC std_ss [sums, BIJ_DEF, INJ_DEF, SURJ_DEF, IN_UNIV]
 >> Q.EXISTS_TAC `(\n t. if t IN m_space m /\
                            fn_minus f t IN IMAGE (enumerate (IMAGE (fn_minus f) (m_space m))) (count n)
                         then fn_minus f t else 0)`
 >> Q.EXISTS_TAC `(\n. sum (0,n)
                        ((\r. r * measure m (PREIMAGE (fn_minus f) {r} INTER m_space m)) o
                         enumerate (IMAGE (fn_minus f) (m_space m))))`
 >> ASM_SIMP_TAC std_ss []
 >> CONJ_TAC
 >- (RW_TAC std_ss [mono_convergent_def]
           >- (RW_TAC real_ss [IN_IMAGE, IN_COUNT, fn_minus_def] >> METIS_TAC [LESS_LESS_EQ_TRANS, REAL_LE_NEGTOTAL])
           >> RW_TAC std_ss [SEQ]
           >> `?N. enumerate (IMAGE (fn_minus f) (m_space m)) N = (fn_minus f) t`
                by METIS_TAC [IN_IMAGE]
           >> Q.EXISTS_TAC `SUC N`
           >> RW_TAC real_ss [GREATER_EQ, real_ge, IN_IMAGE, REAL_SUB_LZERO]
           >> FULL_SIMP_TAC std_ss [IN_COUNT]
           >> METIS_TAC [DECIDE ``!n:num. n < SUC n``, LESS_LESS_EQ_TRANS, fn_minus_def])
 >> STRIP_TAC >> MATCH_MP_TAC psfis_nnfis
 >> ASM_SIMP_TAC std_ss [GSYM REAL_SUM_IMAGE_COUNT]
 >> `(\t. (if t IN m_space m /\ fn_minus f t IN IMAGE (enumerate (IMAGE (fn_minus f) (m_space m))) (count n')
             then fn_minus f t else  0)) =
                (\t. SIGMA (\i. (\i. enumerate (IMAGE (fn_minus f) (m_space m)) i) i *
                        indicator_fn ((\i. PREIMAGE (fn_minus f) {enumerate (IMAGE (fn_minus f) (m_space m)) i}
                                           INTER (m_space m)) i) t)
                     (count n'))`
                by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [IN_IMAGE]
                    >- (`count n' = x INSERT (count n')`
                                by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_INSERT] >> METIS_TAC [])
                        >> POP_ORW
                        >> RW_TAC std_ss [REAL_SUM_IMAGE_THM, FINITE_COUNT]
                        >> ONCE_REWRITE_TAC [(REWRITE_RULE [FINITE_COUNT] o
                                REWRITE_RULE [FINITE_DELETE] o Q.ISPEC `count n' DELETE x`) REAL_SUM_IMAGE_IN_IF]
                        >> RW_TAC real_ss [IN_DELETE, indicator_fn_def, IN_INTER, IN_SING, IN_PREIMAGE]
                        >> `(\x'. (if x' IN count n' /\ ~(x' = x) then
                                enumerate (IMAGE (fn_minus f) (m_space m)) x' *
                                (if enumerate (IMAGE (fn_minus f) (m_space m)) x =
                                enumerate (IMAGE (fn_minus f) (m_space m)) x'
                                then 1 else 0) else 0)) = (\x. 0)`
                                by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [] >> METIS_TAC [])
                        >> POP_ORW
                        >> RW_TAC real_ss [REAL_SUM_IMAGE_0, FINITE_COUNT, FINITE_DELETE])
                    >> FULL_SIMP_TAC real_ss [IN_IMAGE, indicator_fn_def, IN_INTER, IN_PREIMAGE, IN_SING]
                    >- RW_TAC real_ss [REAL_SUM_IMAGE_0, FINITE_COUNT, FINITE_DELETE]
                    >> ONCE_REWRITE_TAC [((REWRITE_RULE [FINITE_COUNT]) o
                                          (Q.ISPEC `count n'`)) REAL_SUM_IMAGE_IN_IF]
                    >> `(\x. (if x IN count n' then
                        (\i. enumerate (IMAGE (fn_minus f) (m_space m)) i *
                        (if (fn_minus f t = enumerate (IMAGE (fn_minus f) (m_space m)) i) /\
                         t IN m_space m then 1 else 0)) x else 0)) = (\x. 0)`
                        by (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC real_ss [] >> METIS_TAC [])
                    >> POP_ORW
                    >> RW_TAC real_ss [REAL_SUM_IMAGE_0, FINITE_COUNT])
 >> POP_ORW
 >> `((\r. r * measure m (PREIMAGE (fn_minus f) {r} INTER m_space m)) o
                enumerate (IMAGE (fn_minus f) (m_space m))) =
                (\i. (\i. enumerate (IMAGE (fn_minus f) (m_space m)) i) i *
                        measure m ((\i.
                PREIMAGE (fn_minus f)
                  {enumerate (IMAGE (fn_minus f) (m_space m)) i} INTER
                m_space m) i))`
                by (RW_TAC std_ss [FUN_EQ_THM, o_DEF] >> RW_TAC real_ss [])
 >> POP_ORW
 >> MATCH_MP_TAC psfis_intro
 >> ASM_SIMP_TAC std_ss [FINITE_COUNT]
 >> reverse CONJ_TAC
 >- (FULL_SIMP_TAC real_ss [IN_IMAGE, fn_minus_def]
     >> METIS_TAC [REAL_LE_REFL, REAL_LE_NEGTOTAL])
 >> `(fn_minus f) IN borel_measurable (m_space m, measurable_sets m)`
        by METIS_TAC [fn_plus_fn_minus_borel_measurable]
 >> rpt STRIP_TAC
 >> `PREIMAGE (fn_minus f) {enumerate (IMAGE (fn_minus f) (m_space m)) i} INTER m_space m =
     {w | w IN m_space m /\
          ((fn_minus f) w = (\w. enumerate (IMAGE (fn_minus f) (m_space m)) i) w)}`
     by (ONCE_REWRITE_TAC [EXTENSION] \\
         RW_TAC std_ss [GSPECIFICATION, IN_INTER, IN_PREIMAGE, IN_SING] \\
         DECIDE_TAC)
 >> POP_ORW
 >> MATCH_MP_TAC borel_measurable_eq_borel_measurable
 >> METIS_TAC [borel_measurable_const, measure_space_def]
QED

(* ************************************************************************* *)
(* Below are old theorems (including Radon-Nikodym) found in K13 and prior   *)
(* ************************************************************************* *)

Theorem finite_prod_measure_space_POW :
    !s1 s2 u v. FINITE s1 /\ FINITE s2  ==>
          (prod_measure_space (s1, POW s1, u) (s2, POW s2, v) =
          (s1 CROSS s2, POW (s1 CROSS s2), prod_measure (s1, POW s1, u) (s2, POW s2, v)))
Proof
    RW_TAC std_ss [prod_measure_space_def, m_space_def, subsets_def, EXTENSION, subsets_def,
                   sigma_def, prod_sets_def, IN_POW, IN_BIGINTER, measurable_sets_def,
                   SUBSET_DEF, IN_CROSS, GSPECIFICATION]
 >> RW_TAC std_ss [GSYM EXTENSION]
 >> EQ_TAC
 >- (RW_TAC std_ss [] >| (* 2 sub-goals here, same tacticals *)
     [ rename1 ‘FST y IN s1’ >> rename1 ‘y IN s’,
       rename1 ‘SND y IN s2’ >> rename1 ‘y IN s’] \\
     (Q.PAT_X_ASSUM `!P. _ ==> s IN P` (MP_TAC o Q.SPEC `POW (s1 CROSS s2)`) \\
      RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS, POW_SIGMA_ALGEBRA] \\
      Suff ‘(!x. (?z. (x,T) = (\(s,t). (s CROSS t,
                                        (!x. x IN s ==> x IN s1) /\ !x. x IN t ==> x IN s2)) z) ==>
             !x'. x' IN x ==> FST x' IN s1 /\ SND x' IN s2)’ >- METIS_TAC [] \\
      RW_TAC std_ss [] \\
      Cases_on ‘z’ >> FULL_SIMP_TAC std_ss [] >> METIS_TAC [IN_CROSS] ))
 >> RW_TAC std_ss []
 >> `x = BIGUNION (IMAGE (\a. {a}) x)`
     by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_SING])
 >> POP_ORW
 >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, subsets_def]
 >> POP_ASSUM MATCH_MP_TAC
 >> CONJ_TAC
 >- (MATCH_MP_TAC finite_countable >> MATCH_MP_TAC IMAGE_FINITE \\
     (MP_TAC o Q.ISPEC `(s1 :'a -> bool) CROSS (s2 :'b -> bool)`) SUBSET_FINITE \\
     RW_TAC std_ss [FINITE_CROSS] \\
     POP_ASSUM MATCH_MP_TAC \\
     METIS_TAC [SUBSET_DEF, IN_CROSS])
 >> RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_SING]
 >> Q.PAT_X_ASSUM `!x. Q ==> x IN s` MATCH_MP_TAC
 >> Q.EXISTS_TAC `({FST a}, {SND a})` >> RW_TAC std_ss [PAIR_EQ, IN_SING]
 >> ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_CROSS, IN_SING]
 >> METIS_TAC [PAIR_EQ, PAIR, FST, SND]
QED

Theorem finite_POW_prod_measure_reduce3 :
    !m0 m1 m2. measure_space m0 /\ measure_space m1 /\ measure_space m2 /\
               FINITE (m_space m0) /\ FINITE (m_space m1) /\ FINITE (m_space m2) /\
              (POW (m_space m0) = measurable_sets m0) /\
              (POW (m_space m1) = measurable_sets m1) /\
              (POW (m_space m2) = measurable_sets m2) ==>
             (!a0 a1 a2. a0 IN measurable_sets m0 /\
                         a1 IN measurable_sets m1 /\
                         a2 IN measurable_sets m2
             ==> ((prod_measure3 m0 m1 m2) (a0 CROSS (a1 CROSS a2)) =
                  measure m0 a0 * measure m1 a1 * measure m2 a2))
Proof
    RW_TAC std_ss [prod_measure3_def, measure_def]
  >> `measure_space (prod_measure_space m1 m2)`
      by METIS_TAC [measure_space_finite_prod_measure_POW1]
  >> `FINITE (m_space (prod_measure_space m1 m2))`
      by METIS_TAC [prod_measure_space_def,m_space_def,FINITE_CROSS]
  >> `m_space (prod_measure_space m1 m2) = m_space m1 CROSS (m_space m2)`
         by RW_TAC std_ss [prod_measure_space_def,m_space_def]
  >> `measurable_sets (prod_measure_space m1 m2) =
      POW (m_space m1 CROSS (m_space m2))`
        by (`m1 = (m_space m1,measurable_sets m1,measure m1)`
             by RW_TAC std_ss [MEASURE_SPACE_REDUCE]
            >> `m2 = (m_space m2, measurable_sets m2, measure m2)`
             by RW_TAC std_ss [MEASURE_SPACE_REDUCE]
            >> METIS_TAC [finite_prod_measure_space_POW, m_space_def, measurable_sets_def])
  >> `a1 CROSS a2 IN measurable_sets (prod_measure_space m1 m2)`
        by (RW_TAC std_ss [IN_POW,SUBSET_DEF,IN_CROSS]
            >> METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE,SUBSET_DEF])
  >> RW_TAC std_ss [finite_POW_prod_measure_reduce]
  >> RW_TAC std_ss [prod_measure_space_def, measure_def]
  >> METIS_TAC [finite_POW_prod_measure_reduce, REAL_MUL_ASSOC]
QED

Theorem measure_space_finite_prod_measure_POW3 :
    !m0 m1 m2. measure_space m0 /\ measure_space m1 /\ measure_space m2 /\
               FINITE (m_space m0) /\ FINITE (m_space m1) /\ FINITE (m_space m2) /\
              (POW (m_space m0) = measurable_sets m0) /\
              (POW (m_space m1) = measurable_sets m1) /\
              (POW (m_space m2) = measurable_sets m2) ==>
        measure_space (m_space m0 CROSS (m_space m1 CROSS m_space m2),
                       POW (m_space m0 CROSS (m_space m1 CROSS m_space m2)),
                       prod_measure3 m0 m1 m2)
Proof
   rpt STRIP_TAC
   >> `(m_space m0 CROSS (m_space m1 CROSS m_space m2),
        POW (m_space m0 CROSS (m_space m1 CROSS m_space m2)),
        prod_measure3 m0 m1 m2) =
        (space (m_space m0 CROSS (m_space m1 CROSS m_space m2),
         POW (m_space m0 CROSS (m_space m1 CROSS m_space m2))),
         subsets (m_space m0 CROSS (m_space m1 CROSS m_space m2),
                  POW (m_space m0 CROSS (m_space m1 CROSS m_space m2))), prod_measure3 m0 m1 m2)`
        by RW_TAC std_ss [space_def, subsets_def]
   >> POP_ORW
   >> `measure_space (prod_measure_space m1 m2)`
       by METIS_TAC [measure_space_finite_prod_measure_POW1]
   >> `prod_measure_space m1 m2 =
       (m_space m1 CROSS m_space m2, POW (m_space m1 CROSS m_space m2), prod_measure m1 m2)`
           by METIS_TAC [MEASURE_SPACE_REDUCE,finite_prod_measure_space_POW]
   >> `!x s. s IN POW (m_space m0 CROSS (m_space m1 CROSS m_space m2)) ==>
           (PREIMAGE (\s1. (x,s1)) s) SUBSET (m_space m1 CROSS (m_space m2))`
                by (RW_TAC std_ss [IN_PREIMAGE, SUBSET_DEF]
                    >> FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS]
                    >> METIS_TAC [SND])
  >> MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces
  >> RW_TAC std_ss [POW_SIGMA_ALGEBRA, space_def, FINITE_CROSS, subsets_def]
  >- (RW_TAC std_ss [positive_def, measure_def, measurable_sets_def]
      >- (`{} = {} CROSS ({} CROSS {})` by RW_TAC std_ss [CROSS_EMPTY]
          >> POP_ORW
          >> RW_TAC std_ss [finite_POW_prod_measure_reduce3, MEASURE_SPACE_EMPTY_MEASURABLE,
                            MEASURE_EMPTY, REAL_MUL_LZERO])
      >> RW_TAC real_ss [Once prod_measure_def, prod_measure3_def,
                         finite_space_POW_integral_reduce]
      >> MATCH_MP_TAC REAL_SUM_IMAGE_POS
      >> RW_TAC std_ss []
      >> MATCH_MP_TAC REAL_LE_MUL
      >> reverse CONJ_TAC
      >- METIS_TAC [IN_POW, IN_SING, SUBSET_DEF, MEASURE_SPACE_POSITIVE, positive_def]
      >> RW_TAC real_ss [measure_def,prod_measure_def, finite_space_POW_integral_reduce]
      >> MATCH_MP_TAC REAL_SUM_IMAGE_POS
      >> RW_TAC std_ss []
      >> MATCH_MP_TAC REAL_LE_MUL
      >> reverse CONJ_TAC
      >- METIS_TAC [IN_POW, IN_SING, SUBSET_DEF, MEASURE_SPACE_POSITIVE, positive_def]
      >> Suff `(PREIMAGE (\s1. (x',s1)) (PREIMAGE (\s1. (x,s1)) s)) SUBSET (m_space m2)`
      >- METIS_TAC [IN_POW, IN_SING, SUBSET_DEF, MEASURE_SPACE_POSITIVE, positive_def]
      >> RW_TAC std_ss [SUBSET_DEF,IN_PREIMAGE]
      >> METIS_TAC [IN_CROSS,IN_POW,SUBSET_DEF, FST, SND])
  >> RW_TAC std_ss [additive_def, measure_def, measurable_sets_def]
  >> RW_TAC std_ss [prod_measure3_def]
  >> ONCE_REWRITE_TAC [prod_measure_def]
  >> RW_TAC std_ss [measure_def]
  >> RW_TAC std_ss [finite_space_POW_integral_reduce, GSYM REAL_SUM_IMAGE_ADD]
  >> MATCH_MP_TAC REAL_SUM_IMAGE_EQ
  >> RW_TAC std_ss [GSYM REAL_ADD_RDISTRIB]
  >> Suff `prod_measure m1 m2 (PREIMAGE (\s1. (x,s1)) (s UNION t)) =
           (prod_measure m1 m2 (PREIMAGE (\s1. (x,s1)) s) +
            prod_measure m1 m2 (PREIMAGE (\s1. (x,s1)) t))`
  >- RW_TAC std_ss []
  >> RW_TAC std_ss [prod_measure_def, finite_space_POW_integral_reduce,
                    GSYM REAL_SUM_IMAGE_ADD]
  >> MATCH_MP_TAC REAL_SUM_IMAGE_EQ
  >> RW_TAC std_ss [GSYM REAL_ADD_RDISTRIB]
  >> Suff `measure m2 (PREIMAGE (\s1. (x',s1)) (PREIMAGE (\s1. (x,s1)) (s UNION t))) =
           measure m2 (PREIMAGE (\s1. (x',s1)) (PREIMAGE (\s1. (x,s1)) s)) +
           measure m2 (PREIMAGE (\s1. (x',s1)) (PREIMAGE (\s1. (x,s1)) t))`
  >- RW_TAC std_ss []
  >> MATCH_MP_TAC MEASURE_ADDITIVE
  >> CONJ_TAC >- RW_TAC std_ss []
  >> CONJ_TAC
  >- (Suff `PREIMAGE (\s1. (x',s1)) (PREIMAGE (\s1. (x,s1)) s) SUBSET m_space m2`
      >- METIS_TAC [IN_POW]
      >> RW_TAC std_ss [SUBSET_DEF,IN_PREIMAGE]
      >> METIS_TAC [IN_POW, IN_CROSS, SUBSET_DEF, FST, SND])
  >> CONJ_TAC
  >- (Suff `PREIMAGE (\s1. (x',s1)) (PREIMAGE (\s1. (x,s1)) t) SUBSET m_space m2`
      >- METIS_TAC [IN_POW]
      >> RW_TAC std_ss [SUBSET_DEF,IN_PREIMAGE]
      >> METIS_TAC [IN_POW, IN_CROSS, SUBSET_DEF, FST, SND])
  >> CONJ_TAC
  >- (RW_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY, IN_PREIMAGE]
      >> METIS_TAC [IN_POW, IN_CROSS, SUBSET_DEF, FST, SND, DISJOINT_DEF, EXTENSION,
                    IN_INTER,NOT_IN_EMPTY])
  >> RW_TAC std_ss [EXTENSION,IN_PREIMAGE,IN_UNION]
QED

Theorem finite_prod_measure_space_POW3 :
    !s1 s2 s3 u v w.
         FINITE s1 /\ FINITE s2 /\ FINITE s3 ==>
         (prod_measure_space3 (s1,POW s1,u) (s2,POW s2,v) (s3,POW s3,w) =
          (s1 CROSS (s2 CROSS s3),POW (s1 CROSS (s2 CROSS s3)),
           prod_measure3 (s1,POW s1,u) (s2,POW s2,v) (s3,POW s3,w)))
Proof
  RW_TAC std_ss [prod_measure_space3_def,m_space_def, subsets_def, EXTENSION, subsets_def,
                sigma_def, prod_sets3_def, IN_POW, IN_BIGINTER, measurable_sets_def, SUBSET_DEF,
                IN_CROSS, GSPECIFICATION]
  >> RW_TAC std_ss [GSYM EXTENSION]
  >> EQ_TAC
  >- (RW_TAC std_ss [] \\ (* 3 sub-goals here, same tacticals *)
      (Q.PAT_X_ASSUM `!s. P ==> x IN s` (MP_TAC o Q.SPEC `POW (s1 CROSS (s2 CROSS s3))`)
       >> RW_TAC std_ss [IN_POW, SUBSET_DEF, IN_CROSS, POW_SIGMA_ALGEBRA]
       >> Suff `(!x''. (?x'. (x'',T) =
               (\(s,t,u'). (s CROSS (t CROSS u'),
               (!x. x IN s ==> x IN s1) /\ (!x. x IN t ==> x IN s2) /\
                !x. x IN u' ==> x IN s3)) x') ==>
                !x. x IN x'' ==> FST x IN s1 /\ FST (SND x) IN s2 /\ SND (SND x) IN s3)`
       >- METIS_TAC []
       >> RW_TAC std_ss []
       >> Cases_on `x'''` >> Cases_on `r`
       >> FULL_SIMP_TAC std_ss []
       >> METIS_TAC [IN_CROSS] ))
  >> RW_TAC std_ss []
  >> `x = BIGUNION (IMAGE (\a. {a}) x)`
    by (ONCE_REWRITE_TAC [EXTENSION]
        >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_SING])
  >> POP_ORW
  >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, subsets_def]
  >> POP_ASSUM MATCH_MP_TAC
  >> CONJ_TAC
  >- (MATCH_MP_TAC finite_countable >> MATCH_MP_TAC IMAGE_FINITE
      >> (MP_TAC o
          Q.ISPEC `(s1 :'a -> bool) CROSS ((s2 :'b -> bool) CROSS (s3:'c -> bool))`)
                SUBSET_FINITE
      >> RW_TAC std_ss [FINITE_CROSS]
      >> POP_ASSUM MATCH_MP_TAC
      >> RW_TAC std_ss [SUBSET_DEF, IN_CROSS])
  >> RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_SING]
  >> Q.PAT_X_ASSUM `!x. Q ==> x IN s` MATCH_MP_TAC
  >> Q.EXISTS_TAC `({FST a}, {FST (SND a)}, {SND(SND a)})` >> RW_TAC std_ss [IN_SING]
  >> RW_TAC std_ss [IN_SING,EXTENSION,IN_CROSS,PAIR]
  >> METIS_TAC [PAIR]
QED

(* ------------------------------------------------------------------------- *)
(* The Radon-Nikodym Theorem (for real_lebesgueTheory)                       *)
(* ------------------------------------------------------------------------- *)

Definition seq_sup_def :
   (seq_sup P 0       = @r. r IN P /\ sup P < r + 1) /\
   (seq_sup P (SUC n) = @r. r IN P /\ sup P < r + (1 / 2) pow (SUC n) /\
                                      seq_sup P n < r /\ r < sup P)
End

(* This theorem is general, the antecedents only assert that ‘sup P’ exists *)
Theorem REAL_SUP_SEQ :
    !P. (?x. P x) /\ (?z. !x. P x ==> x <= z) ==>
        ?x. (!n. x n IN P) /\ (!n. x n <= x (SUC n)) /\ (sup (IMAGE x UNIV) = sup P)
Proof
    RW_TAC std_ss []
 >> Cases_on `?z. P z /\ (z = sup P)`
 >- (Q.EXISTS_TAC `(\i. sup P)` \\
     RW_TAC real_ss [REAL_LE_REFL, SPECIFICATION] \\
    `IMAGE (\i:num. sup P) UNIV = (\i. i = sup P)`
       by RW_TAC std_ss [EXTENSION, IN_IMAGE, IN_UNIV, IN_ABS] \\
     RW_TAC std_ss [REAL_SUP_CONST])
 >> FULL_SIMP_TAC std_ss []
 >> Q.EXISTS_TAC `seq_sup P`
 >> `!e. 0 < e ==> ?x. P x /\ sup P < x + e`
      by (RW_TAC std_ss [] \\
          MATCH_MP_TAC SUP_LT_EPSILON >> METIS_TAC [])
 >> `!n. 0:real < (1 / 2) pow n` by METIS_TAC [HALF_POS, REAL_POW_LT]
 >> STRONG_CONJ_TAC (* !n. seq_sup P n IN P *)
 >- (Induct >- (RW_TAC std_ss [seq_sup_def] \\
                SELECT_ELIM_TAC >> RW_TAC std_ss [] \\
                METIS_TAC [REAL_LT_01, SPECIFICATION]) \\
     RW_TAC std_ss [seq_sup_def] \\
     SELECT_ELIM_TAC >> RW_TAC std_ss [] \\
    `?y. P y /\ seq_sup P n < y`
        by (Know ‘(?y. P y /\ seq_sup P n < y) <=> seq_sup P n < sup P’
            >- (MATCH_MP_TAC REAL_SUP_LE \\
                rpt STRIP_TAC >- (Q.EXISTS_TAC ‘x’ >> art []) \\
                Q.EXISTS_TAC ‘z’ >> RW_TAC std_ss []) >> Rewr' \\
            reverse (RW_TAC std_ss [REAL_LT_LE])
            >- (CCONTR_TAC >> FULL_SIMP_TAC std_ss [IN_APP]) \\
            MATCH_MP_TAC REAL_IMP_LE_SUP \\
            RW_TAC std_ss [] >- (Q.EXISTS_TAC ‘z’ >> art []) \\
            Q.EXISTS_TAC ‘seq_sup P n’ \\
            FULL_SIMP_TAC std_ss [IN_APP, REAL_LE_REFL]) \\
    `?w. P w /\ sup P < w + (1 / 2) pow (SUC n)` by METIS_TAC [] \\
     Q.EXISTS_TAC `max y w` \\
     RW_TAC std_ss [max_def, SPECIFICATION] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
      `w < y` by FULL_SIMP_TAC std_ss [real_lte] \\
      `w + (1 / 2) pow (SUC n) < y + (1 / 2) pow (SUC n)` by METIS_TAC [REAL_LT_RADD] \\
       METIS_TAC [REAL_LT_TRANS],
       (* goal 2 (of 4) *)
       METIS_TAC [REAL_LTE_TRANS],
       (* goal 3 (of 4) *)
       MATCH_MP_TAC REAL_IMP_LT_SUP >> rw [] \\
       Q.EXISTS_TAC ‘z’ >> rw [],
       (* goal 4 (of 4) *)
       MATCH_MP_TAC REAL_IMP_LT_SUP >> rw [] \\
       Q.EXISTS_TAC ‘z’ >> rw [] ])
 >> DISCH_TAC
 >> STRONG_CONJ_TAC (* !n. seq_sup P n <= seq_sup P (SUC n) *)
 >- (RW_TAC std_ss [seq_sup_def] \\
     SELECT_ELIM_TAC \\
     reverse (RW_TAC std_ss []) >- METIS_TAC [REAL_LT_LE] \\
    `?y. P y /\ seq_sup P n < y`
        by (Know ‘(?y. P y /\ seq_sup P n < y) <=> seq_sup P n < sup P’
            >- (MATCH_MP_TAC REAL_SUP_LE \\
                rpt STRIP_TAC >- (Q.EXISTS_TAC ‘x’ >> art []) \\
                Q.EXISTS_TAC ‘z’ >> RW_TAC std_ss []) >> Rewr' \\
            reverse (RW_TAC std_ss [REAL_LT_LE])
            >- (CCONTR_TAC >> FULL_SIMP_TAC std_ss [IN_APP] >> METIS_TAC []) \\
            MATCH_MP_TAC REAL_IMP_LE_SUP \\
            RW_TAC std_ss [] >- (Q.EXISTS_TAC ‘z’ >> art []) \\
            Q.EXISTS_TAC ‘seq_sup P n’ \\
            FULL_SIMP_TAC std_ss [IN_APP, REAL_LE_REFL]) \\
    `?w. P w /\ sup P < w + (1 / 2) pow (SUC n)` by METIS_TAC [] \\
     Q.EXISTS_TAC `max y w` \\
     RW_TAC std_ss [max_def, SPECIFICATION] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
      `w < y` by FULL_SIMP_TAC std_ss [real_lte] \\
      `w + (1 / 2) pow (SUC n) < y + (1 / 2) pow (SUC n)` by METIS_TAC [REAL_LT_RADD] \\
       METIS_TAC [REAL_LT_TRANS],
       (* goal 2 (of 4) *)
       METIS_TAC [REAL_LTE_TRANS],
       (* goal 3 (of 4) *)
       MATCH_MP_TAC REAL_IMP_LT_SUP >> rw [] \\
       Q.EXISTS_TAC ‘z’ >> rw [],
       (* goal 4 (of 4) *)
       MATCH_MP_TAC REAL_IMP_LT_SUP >> rw [] \\
       Q.EXISTS_TAC ‘z’ >> rw [] ])
 >> DISCH_TAC
 (* stage work *)
 >> `!n. sup P <= seq_sup P n + (1 / 2) pow n`
       by (Induct
           >- (RW_TAC std_ss [seq_sup_def, pow] \\
               SELECT_ELIM_TAC \\
               RW_TAC std_ss [] >- METIS_TAC [REAL_LT_01, SPECIFICATION] \\
               METIS_TAC [REAL_LT_LE]) \\
           RW_TAC std_ss [seq_sup_def] \\
           SELECT_ELIM_TAC \\
           reverse (RW_TAC std_ss []) >- METIS_TAC [REAL_LT_LE] \\
          `?y. P y /\ seq_sup P n < y`
              by (Know ‘(?y. P y /\ seq_sup P n < y) <=> seq_sup P n < sup P’
                  >- (MATCH_MP_TAC REAL_SUP_LE \\
                      rpt STRIP_TAC >- (Q.EXISTS_TAC ‘x’ >> art []) \\
                      Q.EXISTS_TAC ‘z’ >> RW_TAC std_ss []) >> Rewr' \\
                  reverse (RW_TAC std_ss [REAL_LT_LE])
                  >- (CCONTR_TAC >> FULL_SIMP_TAC std_ss [IN_APP] >> METIS_TAC []) \\
                  MATCH_MP_TAC REAL_IMP_LE_SUP \\
                  RW_TAC std_ss [] >- (Q.EXISTS_TAC ‘z’ >> art []) \\
                  Q.EXISTS_TAC ‘seq_sup P n’ \\
                  FULL_SIMP_TAC std_ss [IN_APP, REAL_LE_REFL]) \\
          `?w. P w /\ sup P < w + (1 / 2) pow (SUC n)` by METIS_TAC [] \\
           Q.EXISTS_TAC `max y w` \\
           RW_TAC std_ss [max_def, SPECIFICATION] >| (* 4 subgoals *)
           [ (* goal 1 (of 4) *)
            `w < y` by FULL_SIMP_TAC std_ss [real_lte] \\
            `w + (1 / 2) pow (SUC n) < y + (1 / 2) pow (SUC n)` by METIS_TAC [REAL_LT_RADD] \\
             METIS_TAC [REAL_LT_TRANS],
             (* goal 2 (of 4) *)
             METIS_TAC [REAL_LTE_TRANS],
             (* goal 3 (of 4) *)
             MATCH_MP_TAC REAL_IMP_LT_SUP >> rw [] \\
             Q.EXISTS_TAC ‘z’ >> rw [],
             (* goal 4 (of 4) *)
             MATCH_MP_TAC REAL_IMP_LT_SUP >> rw [] \\
             Q.EXISTS_TAC ‘z’ >> rw [] ])
 >> MATCH_MP_TAC SUP_EQ
 >> RW_TAC std_ss []
 >> reverse EQ_TAC >> RW_TAC std_ss []
 >- (FIRST_X_ASSUM MATCH_MP_TAC \\
     POP_ASSUM MP_TAC \\
     rw [IN_IMAGE] >> art [])
 >> rename1 ‘y IN P’
 >> MATCH_MP_TAC REAL_LE_EPSILON
 >> RW_TAC std_ss []
 >> `?n. (1 / 2) pow n < e` by METIS_TAC [REAL_HALF_BETWEEN, REAL_ARCH_POW_INV]
 >> MATCH_MP_TAC REAL_LE_TRANS
 >> Q.EXISTS_TAC `seq_sup P n + (1 / 2) pow n`
 >> RW_TAC std_ss [] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC REAL_LE_TRANS \\
      Q.EXISTS_TAC ‘sup P’ >> art [] \\
      MATCH_MP_TAC REAL_IMP_LE_SUP \\
      CONJ_TAC >- (Q.EXISTS_TAC ‘z’ >> rw []) \\
      Q.EXISTS_TAC ‘y’ \\
      FULL_SIMP_TAC std_ss [IN_APP, REAL_LE_REFL],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC REAL_LE_ADD2 \\
      reverse CONJ_TAC >- FULL_SIMP_TAC std_ss [REAL_LT_LE] \\
      FIRST_X_ASSUM MATCH_MP_TAC \\
      rw [IN_IMAGE] \\
      Q.EXISTS_TAC ‘n’ >> REWRITE_TAC [] ]
QED

Theorem REAL_SUP_FUN_SEQ_IMAGE :
    !(P:real->bool) (P':('a->real)->bool) f.
         (?x. P x) /\ (?z. !x. P x ==> x <= z) /\ (P = IMAGE f P')
      ==> ?g. (!n:num. g n IN P') /\
              (sup (IMAGE (\n. f (g n)) UNIV) = sup P)
Proof
    rpt STRIP_TAC
 >> `?y. (!n. y n IN P) /\ (!n. y n <= y (SUC n)) /\ (sup (IMAGE y UNIV) = sup P)`
      by METIS_TAC [REAL_SUP_SEQ]
 >> Q.EXISTS_TAC `(\n. @r. (r IN P') /\ (f r  = y n))`
 >> `(\n. f (@r. r IN P' /\ (f r = y n))) = y`
        by (RW_TAC std_ss [FUN_EQ_THM] >> SELECT_ELIM_TAC
            >> RW_TAC std_ss []
            >> METIS_TAC [IN_IMAGE])
 >> ASM_SIMP_TAC std_ss []
 >> RW_TAC std_ss []
 >> SELECT_ELIM_TAC
 >> RW_TAC std_ss []
 >> METIS_TAC [IN_IMAGE]
QED

Definition max_fn_seq_def :
   (max_fn_seq g       0 x = g 0 x) /\
   (max_fn_seq g (SUC n) x = max (max_fn_seq g n x) (g (SUC n) x))
End

Theorem max_fn_seq_mono :
    !g n x. max_fn_seq g n x <= max_fn_seq g (SUC n) x
Proof
    RW_TAC std_ss [max_fn_seq_def, max_def, REAL_LE_REFL]
QED

Theorem REAL_SUP_FUN_SEQ_MONO_IMAGE :
    !(P:real->bool) (P':('a->real)->bool) f.
       (?x. P x) /\ (?z. !x. P x ==> x <= z) /\ (P = IMAGE f P') /\
       (!g1 g2. (g1 IN P' /\ g2 IN P' /\ (!x. g1 x <= g2 x))  ==> f g1 <= f g2) /\
       (!g1 g2. g1 IN P' /\ g2 IN P' ==> (\x. max (g1 x) (g2 x)) IN P')
    ==> ?g. (!n. g n IN P') /\
                (!x n. g n x <= g (SUC n) x) /\
                (sup (IMAGE (\n. f (g n)) UNIV) = sup P)
Proof
    rpt STRIP_TAC
 >> `?g. (!n:num. g n IN P') /\ (sup (IMAGE (\n. f (g n)) UNIV) = sup P)`
       by METIS_TAC [REAL_SUP_FUN_SEQ_IMAGE]
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
      by RW_TAC real_ss [max_fn_seq_def,max_def,REAL_LE_REFL]
 >> CONJ_TAC >- RW_TAC std_ss []
 >> CONJ_TAC >- RW_TAC std_ss []
 >> `!n. (!x. g n x <= max_fn_seq g n x)`
      by (Induct >- RW_TAC std_ss [max_fn_seq_def,REAL_LE_REFL]
          >> METIS_TAC [REAL_LE_MAX2, max_fn_seq_def])
 >> `!n. f (g n) <= f (max_fn_seq g n)` by METIS_TAC []
 >> `sup (IMAGE (\n. f (g n)) UNIV) <= sup (IMAGE (\n. f (max_fn_seq g n)) UNIV)`
      by (MATCH_MP_TAC SUP_MONO >> rw [] >| (* 2 subgoals *)
          [ (* goal 1 (of 2) *)
            Q.EXISTS_TAC ‘z’ >> Q.X_GEN_TAC ‘n’ \\
            FIRST_X_ASSUM MATCH_MP_TAC \\
            ONCE_REWRITE_TAC [GSYM SPECIFICATION] \\
            rw [IN_IMAGE] \\
            Q.EXISTS_TAC ‘g n’ >> art [],
            (* goal 2 (of 2) *)
            Q.EXISTS_TAC ‘z’ >> Q.X_GEN_TAC ‘n’ \\
            FIRST_X_ASSUM MATCH_MP_TAC \\
            ONCE_REWRITE_TAC [GSYM SPECIFICATION] \\
            rw [IN_IMAGE] \\
            Q.EXISTS_TAC ‘max_fn_seq g n’ >> art [] ])
 >> `sup (IMAGE (\n. f (max_fn_seq g n)) UNIV) <= sup P`
      by (Q.ABBREV_TAC ‘s = IMAGE (\n. f (max_fn_seq g n)) UNIV’ \\
          Know ‘sup s <= sup P <=> !x. x IN s ==> x <= sup P’
          >- (MATCH_MP_TAC REAL_SUP_LE_EQ \\
              rw [Abbr ‘s’, IN_IMAGE] \\
              Q.EXISTS_TAC ‘z’ >> rw [] \\
              FIRST_X_ASSUM MATCH_MP_TAC \\
              ONCE_REWRITE_TAC [GSYM SPECIFICATION] \\
              rw [IN_IMAGE] \\
              Q.EXISTS_TAC ‘max_fn_seq g n’ >> art [] ) >> Rewr' \\
          rw [Abbr ‘s’, IN_IMAGE] \\
          MATCH_MP_TAC REAL_IMP_LE_SUP \\
          CONJ_TAC >- (Q.EXISTS_TAC ‘z’ >> art []) \\
          Q.EXISTS_TAC ‘f (max_fn_seq g n)’ >> art [REAL_LE_REFL] \\
          ONCE_REWRITE_TAC [GSYM SPECIFICATION] \\
          rw [IN_IMAGE] \\
          Q.EXISTS_TAC ‘max_fn_seq g n’ >> art [])
 >> METIS_TAC [REAL_LE_ANTISYM]
QED

val _ = export_theory ();
