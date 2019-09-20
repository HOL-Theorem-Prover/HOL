(* ------------------------------------------------------------------------- *)
(* Lebesgue Integrals defined on the extended real numbers                   *)
(* Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar                         *)
(* HVG Group, Concordia University, Montreal                                 *)
(*                                                                           *)
(* Updated by Chun Tian (2019)                                               *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ------------------------------------------------------------------------- *)
(* Based on the work of Aaron Coble, Cambridge University                    *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory prim_recTheory pairTheory pred_setTheory
     optionTheory combinTheory res_quanTheory res_quanTools listTheory;

open realTheory realLib seqTheory transcTheory real_sigmaTheory jrhUtils;

open hurdUtils util_probTheory extrealTheory sigma_algebraTheory measureTheory
     borelTheory;

val _ = new_theory "lebesgue";

(* ************************************************************************* *)
(* Basic Definitions                                                         *)
(* ************************************************************************* *)

(* The simple function (g) of f in measurable space m:
   f is a normal function defined on extended reals ('a -> extreal),
   a_i (i IN s) are mutually disjoint measurable sets in m,
   x_i are (normal) reals.
  `g = \t. SIGMA (\i. Normal (x i) * (indicator_fn (a i) t)) s` is the simple function of f,
   BIGUNION and DISJOINT indicate that this is a standard representation of g.
 *)
val pos_simple_fn_def = Define
   `pos_simple_fn m f (s :num set) (a :num -> 'a set) (x :num -> real) <=>
        (!t. 0 <= f t) /\
        (!t. t IN m_space m ==> (f t = SIGMA (\i. Normal (x i) * indicator_fn (a i) t) s)) /\
        (!i. i IN s ==> a i IN measurable_sets m) /\
        FINITE s /\ (!i. i IN s ==> 0 <= x i) /\
        (!i j. i IN s /\ j IN s /\ (i <> j) ==> DISJOINT (a i) (a j)) /\
        (BIGUNION (IMAGE a s) = m_space m)`;

(* The integration of a positive simple function: s is a set of indices,
   a(n) is a sequence of sets, x(n) is a sequence of reals.

   old definition: Normal (SIGMA (\i:num. (x i) * (measure m (a i))) s)
 *)
val pos_simple_fn_integral_def = Define
   `pos_simple_fn_integral m (s :num set) (a :num -> 'a set) (x :num -> real) =
        SIGMA (\i:num. Normal (x i) * (measure m (a i))) s`;

(* `psfs m f` is the set of all positive simple functions equivalent to f *)
val psfs_def = Define
   `psfs m f = {(s,a,x) | pos_simple_fn m f s a x}`;

(* `psfis m f ` is the set of integrals of positive simple functions equivalent to f *)
val psfis_def = Define
   `psfis m f = IMAGE (\(s,a,x). pos_simple_fn_integral m s a x) (psfs m f)`;

(* the integral of arbitrary positive function is the sup of integrals of all
   positive simple functions smaller than f,

   c.f. "nnfis_def" in (old) real_lebesgueScript.sml *)
val pos_fn_integral_def = Define
   `pos_fn_integral m f = sup {r | ?g. r IN psfis m g /\ !x. g x <= f x}`;

(* the integral of arbitrary function is the integrals of positive parts minus
   negative parts *)
val integral_def = Define
   `integral m f = pos_fn_integral m (fn_plus f) - pos_fn_integral m (fn_minus f)`;

(* Lebesgue integrable = the integral is defined (i.e. no `PosInf - PosInf`) *)
val integrable_def = Define
   `integrable m f <=>
        f IN measurable (m_space m,measurable_sets m) Borel /\
        pos_fn_integral m (fn_plus f) <> PosInf /\
        pos_fn_integral m (fn_minus f) <> PosInf`;

val finite_space_integral_def = Define
   `finite_space_integral m f =
        SIGMA (\r. r * measure m (PREIMAGE f {r} INTER m_space m)) (IMAGE f (m_space m))`;

val prod_measure_def = Define
   `prod_measure m0 m1 =
        (\a. (integral m0 (\s0. measure m1 (PREIMAGE (\s1. (s0,s1)) a))))`;

val prod_measure_space_def = Define
   `prod_measure_space m0 m1 =
        ((m_space m0) CROSS (m_space m1),
         subsets (sigma ((m_space m0) CROSS (m_space m1))
                        (prod_sets (measurable_sets m0) (measurable_sets m1))),
         prod_measure m0 m1)`;

(* c.f. prod_sets_def *)
val prod_sets3_def = Define
   `prod_sets3 a b c = {s CROSS (t CROSS u) | s IN a /\ t IN b /\ u IN c}`;

val prod_measure3_def = Define
   `prod_measure3 m0 m1 m2 = prod_measure m0 (prod_measure_space m1 m2)`;

val prod_measure_space3_def = Define
   `prod_measure_space3 m0 m1 m2 =
    (m_space m0 CROSS (m_space m1 CROSS m_space m2),
     subsets (sigma (m_space m0 CROSS (m_space m1 CROSS m_space m2))
                    (prod_sets3 (measurable_sets m0) (measurable_sets m1) (measurable_sets m2))),
     prod_measure3 m0 m1 m2)`;

(* v is absolutely continuous w.r.t. m, denoted by ``v << m``
   note: the type of `v` is not a measure space but a measure, the purpose is to simplify
   the statement of Radon-Nikodym theorem as much as possible.
 *)
val measure_absolutely_continuous_def = Define
   `measure_absolutely_continuous v m =
      !s. s IN measurable_sets m /\ (measure m s = 0) ==> (v s = 0)`;

(* "<<" is already used in "src/n-bit/wordsScript.sml", same priority here *)
val _ = set_fixity "<<" (Infixl 680);
val _ = Unicode.unicode_version {u = Unicode.UChar.lsl, tmnm = "<<"};

val _ = overload_on ("<<", ``measure_absolutely_continuous``);

(* ------------------------------------------------------------------------- *)
(* Radon-Nikodym Derivative                                                  *)
(* ------------------------------------------------------------------------- *)

(* The measure with density (function) f with respect to m,
   from HVG's lebesgue_measureScript.sml, simplified.

   TODO: show `density m f` is a measure, i.e.
   |- measure_space (m_space m, measurable_sets m, density m f) [1, p.81]
 *)
val density_def = Define (* or `f * m` *)
   `density m f = \s. integral m (\x. f x * indicator_fn s x)`;

(* `v = density m f` is denoted by `v = f * m`, also see "RN_deriv_def".
   (last time the word "density" appears, always use "*" later) *)
val _ = overload_on ("*", ``\f m. density m f``);

(* Radon-Nikodym derivative, from (old) real_lebesgueScript.sml, simplified.

   This definition looks more general than "RN_deriv" in Isabelle/HOL which works only on
   positive functions. Also, we have swapped the two arguments:

  `RN_deriv v m` (HOL) = `RN_deriv m (m_space m, measurable_sets m, v)` (Isabelle/HOL)

   The existence of `RN_deriv v m` is then asserted by Radon-Nikodym theorem:

   ``!m v. measure_space m /\ sigma_finite m /\
           measure_space (m_space m,measurable_sets m,v) ==>
          (measure_absolutely_continuous v m <=>
           ?f. f IN borel_measurable (m_space m,measurable_sets m) /\
               (!x. x IN m_space m ==> 0 <= f x) /\
               !s. s IN measurable_sets m ==> ((f * m) s = v s))``

   Also the uniqueness is asserted by the following theorems:

   ``!m f f'. measure_space m /\ sigma_finite m /\
              f IN borel_measurable (m_space m,measurable_sets m) /\
              f' IN borel_measurable (m_space m,measurable_sets m) /\
              nonneg f /\ nonneg f' /\
              (!s. s IN measurable_sets m ==> ((f * m) s = (f' * m) s))
          ==> AE x::m. (f x = f' x)``

   To be proved in martingaleTheory.
 *)
val RN_deriv_def = Define (* or `dv / dm` *)
   `RN_deriv v m =
      @f. f IN measurable (m_space m,measurable_sets m) Borel /\
          (!x. x IN m_space m ==> 0 <= f x) /\
          !a. a IN measurable_sets m ==> ((f * m) a = v a)`;

(* `f = RN_deriv v m` is denoted by `f = v / m`, also see "density_def" *)
val _ = overload_on ("/", ``RN_deriv``);


(*****************************************************************************)

(* moved here from measureTheory with `pos_simple_fn_def` *)
val IN_MEASURABLE_BOREL_POS_SIMPLE_FN = store_thm
  ("IN_MEASURABLE_BOREL_POS_SIMPLE_FN",
  ``!m f. measure_space m /\ (?s a x. pos_simple_fn m f s a x)
          ==> f IN measurable (m_space m,measurable_sets m) Borel``,
  RW_TAC std_ss [pos_simple_fn_def]
  >> `!i. i IN s ==> indicator_fn (a i) IN measurable (m_space m,measurable_sets m) Borel`
        by METIS_TAC [IN_MEASURABLE_BOREL_INDICATOR, measurable_sets_def, subsets_def,
                      m_space_def, measure_space_def]
  >> `!i x. i IN s ==> (\t. Normal (x i) * indicator_fn (a i) t)
         IN measurable (m_space m, measurable_sets m) Borel`
        by (RW_TAC std_ss []
            >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
            >> Q.EXISTS_TAC `indicator_fn (a i)`
            >> Q.EXISTS_TAC `x' i`
            >> RW_TAC std_ss []
            >> FULL_SIMP_TAC std_ss [measure_space_def])
  >> MATCH_MP_TAC (INST_TYPE [beta |-> ``:num``] IN_MEASURABLE_BOREL_SUM)
  >> Q.EXISTS_TAC `(\i. (\t. Normal (x i) * indicator_fn (a i) t))`
  >> Q.EXISTS_TAC `s`
  >> RW_TAC std_ss [space_def]
  >- METIS_TAC [measure_space_def]
  >> RW_TAC real_ss [indicator_fn_def,mul_rzero,mul_rone]
  >> RW_TAC std_ss [extreal_of_num_def]);

(* z/z' c is the standard representation of f/g *)
val pos_simple_fn_integral_present = store_thm
  ("pos_simple_fn_integral_present",
  ``!m f (s :num->bool) a x
       g (s':num->bool) b y.
       measure_space m /\ pos_simple_fn m f s a x /\ pos_simple_fn m g s' b y ==>
       ?z z' c (k:num->bool).
          (!t. t IN m_space m ==> (f t = SIGMA (\i. Normal (z  i) * (indicator_fn (c i) t)) k)) /\
          (!t. t IN m_space m ==> (g t = SIGMA (\i. Normal (z' i) * (indicator_fn (c i) t)) k)) /\
          (pos_simple_fn_integral m s a x = pos_simple_fn_integral m k c z) /\
          (pos_simple_fn_integral m s' b y = pos_simple_fn_integral m k c z') /\
           FINITE k /\ (!i. i IN k ==> 0 <= z i) /\ (!i. i IN k ==> 0 <= z' i) /\
          (!i j. i IN k /\ j IN k /\ i <> j ==> DISJOINT (c i) (c j)) /\
          (!i. i IN k ==> c i IN measurable_sets m) /\
          (BIGUNION (IMAGE c k) = m_space m)``,
   RW_TAC std_ss []
   >> `?p n. BIJ p (count n) (s CROSS s')`
        by FULL_SIMP_TAC std_ss [GSYM FINITE_BIJ_COUNT, pos_simple_fn_def, FINITE_CROSS]
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
   >- (RW_TAC std_ss [FUN_EQ_THM]
       >> FULL_SIMP_TAC std_ss [pos_simple_fn_def]
       >> `!i. i IN s ==> (\i. Normal (x i) * indicator_fn (a i) t) i <> NegInf`
            by METIS_TAC [indicator_fn_def,mul_rzero,mul_rone,extreal_not_infty,extreal_of_num_def]
       >> FULL_SIMP_TAC std_ss [(Once o UNDISCH o Q.ISPEC `(s :num -> bool)`) EXTREAL_SUM_IMAGE_IN_IF]
       >> `(\x'. (if x' IN s then (\i. Normal (x i) * indicator_fn (a i) t) x' else 0)) =
           (\x'. (if x' IN s then (\i. Normal (x i) *
                SIGMA (\j. indicator_fn (a i INTER b j) t) s') x' else 0))`
        by (RW_TAC std_ss [FUN_EQ_THM]
            >> RW_TAC std_ss []
            >> FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
            >> (MP_TAC o Q.ISPEC `(a :num -> 'a set) (x' :num)` o
                UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
                Q.ISPECL [`(s' :num -> bool)`, `m_space (m: 'a m_space)`,
                          `(b :num -> 'a set)`]) indicator_fn_split
            >> Q.PAT_X_ASSUM `!i. i IN s ==> (a :num -> 'a set) i IN measurable_sets m`
                (ASSUME_TAC o UNDISCH o Q.SPEC `x'`)
            >> `!a m. measure_space m /\
              a IN measurable_sets m ==> a SUBSET m_space m`
                by RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,
                                  subset_class_def, subsets_def, space_def]
            >> POP_ASSUM (ASSUME_TAC o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
                          Q.ISPECL [`(a :num -> 'a set) (x' :num)`, `(m :'a m_space)`])
            >> ASM_SIMP_TAC std_ss [])
       >> FULL_SIMP_TAC std_ss []
       >> `!i j. j IN s' ==> (\j. indicator_fn (a i INTER b j) t) j <> NegInf`
            by METIS_TAC [extreal_of_num_def,extreal_not_infty,indicator_fn_def]
       >> `!(x':num) (i:num). Normal (x i) * SIGMA (\j. indicator_fn (a i INTER b j) t) s' =
                    SIGMA (\j. Normal (x i) * indicator_fn (a i INTER b j) t) s'`
           by (RW_TAC std_ss []
               >> (MP_TAC o UNDISCH o Q.SPEC `s'` o GSYM o INST_TYPE [alpha |-> ``:num``])
                      EXTREAL_SUM_IMAGE_CMUL
               >> FULL_SIMP_TAC std_ss [])
       >> POP_ORW
       >> `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
       >> `INJ p' (s CROSS s')
           (IMAGE p' (s CROSS s'))`
           by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF]
       >> (MP_TAC o Q.SPEC `(\i:num. Normal (x (FST (p i))) *
                                     indicator_fn ((\(i:num,j:num). a i INTER b j) (p i)) t)`
           o UNDISCH o Q.SPEC `p'` o UNDISCH o Q.SPEC `s CROSS s'`
           o INST_TYPE [alpha |-> ``:num#num``, beta |-> ``:num``]) EXTREAL_SUM_IMAGE_IMAGE
       >> `!x'. Normal (x (FST (p x'))) * indicator_fn ((\(i,j). a i INTER b j) (p x')) t <> NegInf`
            by METIS_TAC [indicator_fn_def,mul_rzero,mul_rone,extreal_not_infty,extreal_of_num_def]
       >> RW_TAC std_ss []
       >> `!x'. ((\i. Normal (x (FST (p i))) *
                      indicator_fn ((\(i,j). a i INTER b j) (p i)) t) o p') x' <> NegInf`
             by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
                 >> METIS_TAC [extreal_not_infty,extreal_of_num_def])
       >> (MP_TAC o Q.SPEC `((\i. Normal (x (FST ((p :num -> num # num) i))) *
                                  indicator_fn ((\(i,j). a i INTER b j) (p i)) t) o p')`
           o UNDISCH o Q.ISPEC `(s :num set) CROSS (s' :num set)`) EXTREAL_SUM_IMAGE_IN_IF
       >> RW_TAC std_ss []
       >> `(\x'.if x' IN s CROSS s' then
                Normal (x (FST x')) * indicator_fn ((\(i,j). a i INTER b j) x') t
               else 0) =
           (\x'. (if x' IN s CROSS s' then
                (\x'. Normal (x (FST x')) * indicator_fn ((\(i,j). a i INTER b j) x') t) x'
                 else 0))` by METIS_TAC []
       >> POP_ORW
       >> `!x'. (\x'. Normal (x (FST x')) * indicator_fn ((\(i,j). a i INTER b j) x') t) x' <> NegInf`
            by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
                >> METIS_TAC [extreal_not_infty,extreal_of_num_def])
       >> (MP_TAC o Q.SPEC `(\x'. Normal (x (FST x')) * indicator_fn ((\(i,j). a i INTER b j) x') t)`
           o UNDISCH o Q.ISPEC `(s :num set) CROSS (s' :num set)`) (GSYM EXTREAL_SUM_IMAGE_IN_IF)
       >> RW_TAC std_ss []
       >> `!x'. NegInf <> (\i:num. SIGMA (\j:num. Normal (x i) * indicator_fn (a i INTER b j) t) s') x'`
            by (RW_TAC std_ss []
                >> `!j. (\j. Normal (x x') * indicator_fn (a x' INTER b j) t) j <> NegInf`
                     by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
                         >> METIS_TAC [extreal_of_num_def,extreal_not_infty])
                >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY])
       >> (MP_TAC o Q.SPEC `(\i:num. SIGMA (\j:num. Normal (x i) * indicator_fn (a i INTER b j) t) s')`
           o UNDISCH o Q.ISPEC `(s :num -> bool)`) (GSYM EXTREAL_SUM_IMAGE_IN_IF)
       >> RW_TAC std_ss []
       >> (MP_TAC o Q.ISPECL [`s:num->bool`,`s':num->bool`]) EXTREAL_SUM_IMAGE_SUM_IMAGE
       >> RW_TAC std_ss []
       >> POP_ASSUM (MP_TAC o Q.SPEC `(\i j. Normal (x i) * indicator_fn (a i INTER b j) t)`)
       >> `!x'. Normal (x (FST x')) * indicator_fn (a (FST x') INTER b (SND x')) t <> NegInf`
             by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
                 >> METIS_TAC [extreal_of_num_def,extreal_not_infty])
       >> RW_TAC std_ss []
       >> Suff `(\i. Normal (x (FST i)) * indicator_fn (a (FST i) INTER b (SND i)) t) =
                (\x'. Normal (x (FST x')) * indicator_fn ((\(i,j). a i INTER b j) x') t)`
       >- RW_TAC std_ss []
       >> RW_TAC std_ss [FUN_EQ_THM]
       >> Cases_on `x'`
       >> RW_TAC std_ss [FST, SND])
   >> CONJ_TAC
   >- (RW_TAC std_ss [FUN_EQ_THM] >> FULL_SIMP_TAC std_ss [pos_simple_fn_def]
       >> (MP_TAC o Q.SPEC `(\i. Normal (y i) * indicator_fn (b i) t)`
           o UNDISCH o Q.ISPEC `s':num->bool`) EXTREAL_SUM_IMAGE_IN_IF
       >> `!x. x IN s' ==> (\i. Normal (y i) * indicator_fn (b i) t) x <> NegInf`
           by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
                 >> METIS_TAC [extreal_of_num_def,extreal_not_infty])
       >> RW_TAC std_ss []
       >> `(\x. if x IN s' then Normal (y x) * indicator_fn (b x) t else 0) =
           (\x. (if x IN s' then (\i. Normal (y i) * indicator_fn (b i) t) x else 0))`
             by RW_TAC std_ss []
       >> POP_ORW
       >> `(\x. (if x IN s' then (\i. Normal (y i) * indicator_fn (b i) t) x else 0)) =
           (\x. (if x IN s' then (\i. Normal (y i) *
                SIGMA (\j. indicator_fn (a j INTER b i) t) s) x else 0))`
        by (RW_TAC std_ss [FUN_EQ_THM]
            >> RW_TAC std_ss []
            >> FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
            >> (MP_TAC o REWRITE_RULE [Once INTER_COMM] o
                Q.ISPEC `(b :num -> 'a set) (x' :num)` o
                UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
                Q.ISPECL [`(s :num -> bool)`, `m_space (m :'a m_space)`,
                          `(a :num -> 'a set)`]) indicator_fn_split
            >> Q.PAT_X_ASSUM `!i. i IN s' ==> (b :num -> 'a set) i IN measurable_sets m`
                (ASSUME_TAC o UNDISCH o Q.SPEC `x'`)
            >> RW_TAC std_ss [MEASURE_SPACE_SUBSET_MSPACE])
       >> POP_ORW
       >> `!(x:num) (i:num). Normal (y i) * SIGMA (\j. indicator_fn (a j INTER b i) t) s =
                              SIGMA (\j. Normal (y i) * indicator_fn (a j INTER b i) t) s`
             by (RW_TAC std_ss []
                 >> `!j. (\j. indicator_fn (a j INTER b i) t) j <> NegInf`
                      by RW_TAC std_ss [indicator_fn_def,extreal_of_num_def,extreal_not_infty]
                 >> FULL_SIMP_TAC std_ss [GSYM EXTREAL_SUM_IMAGE_CMUL])
       >> POP_ORW
       >> `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
       >> `INJ p' (s CROSS s')
           (IMAGE p' (s CROSS s'))`
             by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF]
       >> (MP_TAC o Q.SPEC `(\i:num. Normal (y (SND (p i))) *
                                     indicator_fn ((\(i:num,j:num). a i INTER b j) (p i)) t)`
           o UNDISCH o Q.SPEC `p'` o UNDISCH o Q.SPEC `s CROSS s'`
           o INST_TYPE [alpha |-> ``:num#num``, beta |-> ``:num``]) EXTREAL_SUM_IMAGE_IMAGE
       >> `!x. (\i. Normal (y (SND (p i))) *
                    indicator_fn ((\(i,j). a i INTER b j) (p i)) t) x <> NegInf`
            by METIS_TAC [indicator_fn_def,mul_rzero,mul_rone,extreal_not_infty,extreal_of_num_def]
       >> RW_TAC std_ss []
       >> `!x'. ((\i. Normal (y (SND (p i))) *
                      indicator_fn ((\(i,j). a i INTER b j) (p i)) t) o p') x' <> NegInf`
             by (RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone]
                 >> METIS_TAC [extreal_not_infty, extreal_of_num_def])
       >> (MP_TAC o Q.SPEC `((\i. Normal (y (SND ((p :num -> num # num) i))) *
                                  indicator_fn ((\(i,j). a i INTER b j) (p i)) t) o p')`
           o UNDISCH o Q.ISPEC `(s :num set) CROSS (s' :num set)`) EXTREAL_SUM_IMAGE_IN_IF
       >> RW_TAC std_ss []
       >> `(\x'.if x' IN s CROSS s' then
                Normal (y (SND x')) * indicator_fn ((\(i,j). a i INTER b j) x') t else 0) =
           (\x'. (if x' IN s CROSS s' then
                (\x'. Normal (y (SND x')) * indicator_fn ((\(i,j). a i INTER b j) x') t) x'
                 else 0))` by METIS_TAC []
       >> POP_ORW
       >> `!x'. (\x'. Normal (y (SND x')) * indicator_fn ((\(i,j). a i INTER b j) x') t) x' <> NegInf`
            by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
                >> METIS_TAC [extreal_not_infty,extreal_of_num_def])
       >> (MP_TAC o Q.SPEC `(\x'. Normal (y (SND x')) * indicator_fn ((\(i,j). a i INTER b j) x') t)`
           o UNDISCH o Q.ISPEC `(s :num set) CROSS (s' :num set)`) (GSYM EXTREAL_SUM_IMAGE_IN_IF)
       >> RW_TAC std_ss []
       >> `!x'. NegInf <> (\x:num. SIGMA (\j:num. Normal (y x) * indicator_fn (a j INTER b x) t) s) x'`
            by (RW_TAC std_ss []
                >> `!j. (\j. Normal (y x') * indicator_fn (a j INTER b x') t) j <> NegInf`
                     by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
                         >> METIS_TAC [extreal_of_num_def,extreal_not_infty])
                >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY])
       >> (MP_TAC o Q.SPEC `(\x:num. SIGMA (\j:num. Normal (y x) * indicator_fn (a j INTER b x) t) s)`
           o UNDISCH o Q.ISPEC `(s' :num -> bool)`) (GSYM EXTREAL_SUM_IMAGE_IN_IF)
       >> RW_TAC std_ss []
       >> (MP_TAC o Q.ISPECL [`s':num->bool`,`s:num->bool`]) EXTREAL_SUM_IMAGE_SUM_IMAGE
       >> RW_TAC std_ss []
       >> POP_ASSUM (MP_TAC o Q.SPEC `(\x j. Normal (y x) * indicator_fn (a j INTER b x) t)`)
       >> `!x. Normal (y x) * indicator_fn (a j INTER b x) t <> NegInf`
             by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
                 >> METIS_TAC [extreal_of_num_def,extreal_not_infty])
       >> `!x. Normal (y (FST x)) *
              indicator_fn (a (SND x) INTER b (FST x)) t <> NegInf`
             by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
                 >> METIS_TAC [extreal_of_num_def,extreal_not_infty])
       >> RW_TAC std_ss []
       >>  `(s' CROSS s) = IMAGE (\x. (SND x, FST x)) (s CROSS s')`
        by (RW_TAC std_ss [Once EXTENSION, IN_CROSS, IN_IMAGE]
            >> (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
            >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND]
            >> EQ_TAC
            >- (STRIP_TAC >> Q.EXISTS_TAC `(r,q)` >> RW_TAC std_ss [FST, SND])
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
       >> (MP_TAC o Q.SPEC `(\x. Normal (y (FST x)) * indicator_fn (a (SND x) INTER b (FST x)) t)`
           o UNDISCH o Q.SPEC `(\x. (SND x, FST x))` o UNDISCH
           o Q.ISPEC `((s:num->bool) CROSS (s':num->bool))`
           o INST_TYPE [``:'b``|->``:num#num``]) EXTREAL_SUM_IMAGE_IMAGE
       >> `!x. (\x. Normal (y (FST x)) * indicator_fn (a (SND x) INTER b (FST x)) t) x <> NegInf`
             by (RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone]
                 >> METIS_TAC [extreal_of_num_def,extreal_not_infty])
       >> RW_TAC std_ss [o_DEF]
       >> Suff `(\x. Normal (y (SND x)) * indicator_fn (a (FST x) INTER b (SND x)) t) =
                (\x. Normal (y (SND x)) * indicator_fn ((\(i,j). a i INTER b j) x) t)`
       >- RW_TAC std_ss []
       >> RW_TAC std_ss [FUN_EQ_THM]
       >> Cases_on `x'`
       >> RW_TAC std_ss [FST, SND])
   >> CONJ_TAC
   >- (RW_TAC std_ss [pos_simple_fn_integral_def] >> FULL_SIMP_TAC std_ss [pos_simple_fn_def]
       >> (MP_TAC o Q.ISPEC `(\i:num. Normal (x i) * measure m (a i))`
           o UNDISCH o Q.ISPEC `(s :num -> bool)`) EXTREAL_SUM_IMAGE_IN_IF
       >> `!x'. x' IN s ==> (\i. Normal (x i) * measure m (a i)) x' <> NegInf`
             by (RW_TAC std_ss []
                 >> METIS_TAC [positive_not_infty,mul_not_infty,measure_space_def])
       >> RW_TAC std_ss []
       >> `(\x'. if x' IN s then Normal (x x') * measure m (a x') else 0) =
           (\x'. (if x' IN s then (\i. Normal (x i) * measure m (a i)) x' else 0))`
            by METIS_TAC []
       >> POP_ORW
       >> `(\x'. (if x' IN s then (\i. Normal (x i) * measure m (a i)) x' else 0)) =
           (\x'. (if x' IN s then (\i. Normal (x i) *
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
       >> `!i. i IN s ==> (Normal (x i) * SIGMA (\j. measure m (a i INTER b j)) s' =
                           SIGMA (\j. Normal (x i) * measure m (a i INTER b j)) s')`
              by (RW_TAC std_ss [] \\
                  `!j. j IN s' ==> (\j. measure m (a i INTER b j)) j <> NegInf`
                     by METIS_TAC [positive_not_infty, measure_space_def, MEASURE_SPACE_INTER] \\
                  FULL_SIMP_TAC std_ss [GSYM EXTREAL_SUM_IMAGE_CMUL])
       >> FULL_SIMP_TAC std_ss []
       >> `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
       >> `INJ p' (s CROSS s')
           (IMAGE p' (s CROSS s'))`
               by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF]
       >> (MP_TAC o Q.SPEC `(\i:num. Normal (x (FST (p i))) *
                                     measure m ((\(i:num, j:num). a i INTER b j) (p i)))`
           o UNDISCH o Q.SPEC `p'` o UNDISCH o Q.SPEC `s CROSS s'`
           o INST_TYPE [alpha |-> ``:num#num``, beta |-> ``:num``]) EXTREAL_SUM_IMAGE_IMAGE
       >> `!x'. x' IN IMAGE p' (s CROSS s') ==>
                Normal (x (FST (p x'))) * measure m ((\(i,j). a i INTER b j) (p x')) <> NegInf`
           by (RW_TAC std_ss []
               >> Cases_on `p x'`
               >> RW_TAC std_ss []
               >> FULL_SIMP_TAC std_ss [IN_IMAGE,IN_CROSS]
               >> `q IN s` by METIS_TAC [BIJ_DEF,FST,SND]
               >> `r IN s'` by METIS_TAC [BIJ_DEF,FST,SND]
               >> METIS_TAC [positive_not_infty,measure_space_def,mul_not_infty,MEASURE_SPACE_INTER])
       >> RW_TAC std_ss []
       >> (MP_TAC o Q.SPEC `((\i. Normal (x (FST ((p :num -> num # num) i))) *
                                  measure m ((\(i,j). a i INTER b j) (p i))) o p')`
           o UNDISCH o Q.ISPEC `(s :num set) CROSS (s' :num set)`) EXTREAL_SUM_IMAGE_IN_IF
       >> `!x'. x' IN s CROSS s' ==>
                ((\i. Normal (x (FST (p i))) *
                      measure m ((\(i,j). a i INTER b j) (p i))) o p') x' <> NegInf`
            by (RW_TAC std_ss []
                >> Cases_on `x'`
                >> FULL_SIMP_TAC std_ss [IN_CROSS]
                >> METIS_TAC [positive_not_infty, measure_space_def, mul_not_infty,
                              MEASURE_SPACE_INTER])
       >> RW_TAC std_ss []
       >> `(\x'. if x' IN s CROSS s' then
                    Normal (x (FST x')) * measure m ((\(i,j). a i INTER b j) x') else 0) =
           (\x'. (if x' IN s CROSS s' then
                     (\x'. Normal (x (FST x')) * measure m ((\(i,j). a i INTER b j) x')) x' else 0))`
           by METIS_TAC []
       >> POP_ORW
       >> (MP_TAC o Q.SPEC `(\x'. Normal (x (FST x')) * measure m ((\(i,j). a i INTER b j) x'))`
           o UNDISCH o Q.ISPEC `(s :num set) CROSS (s' :num set)`) (GSYM EXTREAL_SUM_IMAGE_IN_IF)
       >> `!x'. x' IN s CROSS s' ==>
            NegInf <> (\x'. Normal (x (FST x')) * measure m ((\(i,j). a i INTER b j) x')) x'`
             by (RW_TAC std_ss []
                 >> Cases_on `x'`
                 >> FULL_SIMP_TAC std_ss [IN_CROSS]
                 >> METIS_TAC [positive_not_infty,measure_space_def,mul_not_infty,MEASURE_SPACE_INTER])
       >> RW_TAC std_ss []
       >> `!x'. x' IN s ==>
                NegInf <> (\i:num. SIGMA (\j:num. Normal (x i) * measure m (a i INTER b j)) s') x'`
            by (RW_TAC std_ss []
                >> `!j. j IN s' ==> (\j. Normal (x x') * measure m (a x' INTER b j)) j <> NegInf`
                     by (RW_TAC std_ss []
                         >> METIS_TAC [positive_not_infty, measure_space_def, mul_not_infty,
                                       MEASURE_SPACE_INTER])
                >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY])
       >> (MP_TAC o Q.SPEC `(\i:num. SIGMA (\j:num. Normal (x i) * measure m (a i INTER b j)) s')`
           o UNDISCH o Q.ISPEC `(s :num -> bool)`) (GSYM EXTREAL_SUM_IMAGE_IN_IF)
       >> RW_TAC std_ss []
       >> (MP_TAC o Q.ISPECL [`s:num->bool`,`s':num->bool`]) EXTREAL_SUM_IMAGE_SUM_IMAGE
       >> RW_TAC std_ss []
       >> POP_ASSUM (MP_TAC o Q.SPEC `(\i j. Normal (x i) * measure m (a i INTER b j))`)
       >> `!x'. x' IN s CROSS s' ==>
                Normal (x (FST x')) * measure m (a (FST x') INTER b (SND x')) <> NegInf`
             by (RW_TAC std_ss []
                 >> Cases_on `x'`
                 >> FULL_SIMP_TAC std_ss [IN_CROSS]
                 >> METIS_TAC [positive_not_infty, measure_space_def, mul_not_infty,
                               MEASURE_SPACE_INTER])
       >> RW_TAC std_ss []
       >> Suff `(\i. Normal (x (FST i)) * measure m (a (FST i) INTER b (SND i))) =
                (\x'. Normal (x (FST x')) * measure m ((\(i,j). a i INTER b j) x'))`
       >- RW_TAC std_ss []
       >> RW_TAC std_ss [FUN_EQ_THM]
       >> Cases_on `x'`
       >> RW_TAC std_ss [FST,SND])
   >> CONJ_TAC
   >- (RW_TAC std_ss [pos_simple_fn_integral_def] >> FULL_SIMP_TAC std_ss [pos_simple_fn_def]
       >> (MP_TAC o Q.ISPEC `(\i:num. Normal (y i) * measure m (b i))`
           o UNDISCH o Q.ISPEC `(s' :num -> bool)`) EXTREAL_SUM_IMAGE_IN_IF
       >> `!x. x IN s' ==> (\i. Normal (y i) * measure m (b i)) x <> NegInf`
             by (RW_TAC std_ss []
                 >> METIS_TAC [positive_not_infty,mul_not_infty,measure_space_def])
       >> RW_TAC std_ss []
       >> `(\x'. if x' IN s' then Normal (y x') * measure m (b x') else 0) =
           (\x'. (if x' IN s' then (\i. Normal (y i) * measure m (b i)) x' else 0))`
            by METIS_TAC []
       >> POP_ORW
       >> `(\x'. (if x' IN s' then (\i. Normal (y i) * measure m (b i)) x' else 0)) =
           (\x'. (if x' IN s' then (\i. Normal (y i) *
                SIGMA (\j. measure m (b i INTER a j)) s) x' else 0))`
        by (RW_TAC std_ss [FUN_EQ_THM]
            >> RW_TAC std_ss []
            >> FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
            >> (MP_TAC o Q.SPEC `b (x' :num)` o
                UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
                Q.SPECL
                [`s`, `a`, `m`]) measure_split
           >> RW_TAC std_ss [])
       >> POP_ORW
       >> `!i. i IN s' ==> (Normal (y i) * SIGMA (\j. measure m (b i INTER a j)) s =
                           SIGMA (\j. Normal (y i) * measure m (b i INTER a j)) s)`
              by (RW_TAC std_ss []
               >> `!j. j IN s ==> (\j. measure m (b i INTER a j)) j <> NegInf`
                     by METIS_TAC [positive_not_infty,measure_space_def,MEASURE_SPACE_INTER]
               >> FULL_SIMP_TAC std_ss [GSYM EXTREAL_SUM_IMAGE_CMUL])
       >> FULL_SIMP_TAC std_ss []
       >> `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
       >> `INJ p' (s CROSS s')
           (IMAGE p' (s CROSS s'))`
               by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF]
       >> (MP_TAC o Q.SPEC `(\i:num. Normal (y (SND (p i))) * measure m ((\(i:num,j:num). a i INTER b j) (p i)))`
           o UNDISCH o Q.SPEC `p'` o UNDISCH o Q.SPEC `s CROSS s'`
           o INST_TYPE [alpha |-> ``:num#num``, beta |-> ``:num``]) EXTREAL_SUM_IMAGE_IMAGE
       >> `!x'. x' IN IMAGE p' (s CROSS s') ==> Normal (y (SND (p x'))) * measure m ((\(i,j). a i INTER b j) (p x'))  <> NegInf`
           by (RW_TAC std_ss []
               >> Cases_on `p x'`
               >> RW_TAC std_ss []
               >> FULL_SIMP_TAC std_ss [IN_IMAGE,IN_CROSS]
               >> `q IN s` by METIS_TAC [BIJ_DEF,FST,SND]
               >> `r IN s'` by METIS_TAC [BIJ_DEF,FST,SND]
               >> METIS_TAC [positive_not_infty,measure_space_def,mul_not_infty,MEASURE_SPACE_INTER])
       >> RW_TAC std_ss []
       >> (MP_TAC o Q.SPEC `((\i. Normal (y (SND ((p :num -> num # num) i))) * measure m ((\(i,j). a i INTER b j) (p i))) o p')`
           o UNDISCH o Q.ISPEC `(s :num set) CROSS (s' :num set)`) EXTREAL_SUM_IMAGE_IN_IF
       >> `!x'. x' IN s CROSS s' ==> ((\i. Normal (y (SND (p i))) * measure m ((\(i,j). a i INTER b j) (p i))) o p') x' <> NegInf`
            by (RW_TAC std_ss []
                >> Cases_on `x'`
                >> FULL_SIMP_TAC std_ss [IN_CROSS]
                >> METIS_TAC [positive_not_infty,measure_space_def,mul_not_infty,MEASURE_SPACE_INTER])
       >> RW_TAC std_ss []
       >> `(\x'. if x' IN s CROSS s' then
                Normal (y (SND x')) * measure m ((\(i,j). a i INTER b j) x') else 0) =
           (\x'. (if x' IN s CROSS s' then
                (\x'. Normal (y (SND x')) * measure m ((\(i,j). a i INTER b j) x')) x' else 0))` by METIS_TAC []
       >> POP_ORW
       >> (MP_TAC o Q.SPEC `(\x'. Normal (y (SND x')) * measure m ((\(i,j). a i INTER b j) x'))`
           o UNDISCH o Q.ISPEC `(s :num set) CROSS (s' :num set)`) (GSYM EXTREAL_SUM_IMAGE_IN_IF)
       >> `!x'. x' IN s CROSS s' ==>
            NegInf <> (\x'. Normal (y (SND x')) * measure m ((\(i,j). a i INTER b j) x')) x'`
             by (RW_TAC std_ss []
                 >> Cases_on `x'`
                 >> FULL_SIMP_TAC std_ss [IN_CROSS]
                 >> METIS_TAC [positive_not_infty,measure_space_def,mul_not_infty,MEASURE_SPACE_INTER])
       >> RW_TAC std_ss []
       >> `!x'. x' IN s' ==> NegInf <> (\i:num. SIGMA (\j:num. Normal (y i) * measure m (b i INTER a j)) s) x'`
            by (RW_TAC std_ss []
                >> `!j. j IN s ==> (\j. Normal (y x') * measure m (b x' INTER a j)) j <> NegInf`
                     by (RW_TAC std_ss []
                         >> METIS_TAC [positive_not_infty,measure_space_def,mul_not_infty,MEASURE_SPACE_INTER])
                >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY])
       >> (MP_TAC o Q.SPEC `(\i:num. SIGMA (\j:num. Normal (y i) * measure m (b i INTER a j)) s)`
           o UNDISCH o Q.ISPEC `(s' :num -> bool)`) (GSYM EXTREAL_SUM_IMAGE_IN_IF)
       >> RW_TAC std_ss []
       >> (MP_TAC o Q.ISPECL [`s':num->bool`,`s:num->bool`]) EXTREAL_SUM_IMAGE_SUM_IMAGE
       >> RW_TAC std_ss []
       >> POP_ASSUM (MP_TAC o Q.SPEC `(\i j. Normal (y i) * measure m (b i INTER a j))`)
       >> `!x'. x' IN s' CROSS s ==> Normal (y (FST x')) * measure m (b (FST x') INTER a (SND x')) <> NegInf`
             by (RW_TAC std_ss []
                 >> Cases_on `x'`
                 >> FULL_SIMP_TAC std_ss [IN_CROSS]
                 >> METIS_TAC [positive_not_infty,measure_space_def,mul_not_infty,MEASURE_SPACE_INTER])
       >> RW_TAC std_ss [o_DEF]
       >>  `(s' CROSS s) = IMAGE (\x. (SND x, FST x)) (s CROSS s')`
        by (RW_TAC std_ss [Once EXTENSION, IN_CROSS, IN_IMAGE]
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
       >> (MP_TAC o Q.SPEC `(\x. Normal (y (FST x)) * measure m (a (SND x) INTER b (FST x)))`
           o UNDISCH o Q.SPEC `(\x. (SND x, FST x))` o UNDISCH o
           Q.ISPEC `((s:num->bool) CROSS (s':num->bool))` o
                INST_TYPE [``:'b``|->``:num#num``]) EXTREAL_SUM_IMAGE_IMAGE
       >> `!x. x IN IMAGE (\x. (SND x,FST x)) (s CROSS s') ==>
              (\x. Normal (y (FST x)) * measure m (a (SND x) INTER b (FST x))) x <> NegInf`
              by (RW_TAC std_ss []
                  >> Cases_on `x'`
                  >> FULL_SIMP_TAC std_ss [IN_CROSS,IN_IMAGE]
                  >> METIS_TAC [positive_not_infty,measure_space_def,mul_not_infty,MEASURE_SPACE_INTER])
       >> RW_TAC std_ss [o_DEF,INTER_COMM]
       >> Suff `(\x. Normal (y (SND x)) * measure m (a (FST x) INTER b (SND x))) =
                (\x. Normal (y (SND x)) * measure m ((\(i,j). a i INTER b j) x))`
       >- RW_TAC std_ss []
       >> RW_TAC std_ss [FUN_EQ_THM]
       >> Cases_on `x'`
       >> RW_TAC std_ss [FST,SND])
   >> CONJ_TAC
   >- FULL_SIMP_TAC std_ss [IMAGE_FINITE, FINITE_CROSS, pos_simple_fn_def]
   >> CONJ_TAC
   >- (RW_TAC std_ss [IN_IMAGE]
       >> FULL_SIMP_TAC std_ss [o_DEF]
       >> (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
       >> (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
       >> RW_TAC std_ss []
       >> RW_TAC std_ss []
       >> METIS_TAC [IN_CROSS,pos_simple_fn_def,FST])
   >> CONJ_TAC
   >- (RW_TAC std_ss [IN_IMAGE]
       >> FULL_SIMP_TAC std_ss [o_DEF]
       >> (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
       >> (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
       >> RW_TAC std_ss []
       >> RW_TAC std_ss []
       >> METIS_TAC [IN_CROSS,pos_simple_fn_def,SND])
   >> CONJ_TAC
   >- (RW_TAC std_ss [IN_DISJOINT, IN_IMAGE,EXTENSION, NOT_IN_EMPTY, IN_INTER]
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
   >> RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, IN_IMAGE, IN_CROSS]
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
   >> Suff `(?x1 x2. x' IN a x1 INTER b x2 /\ x1 IN s /\ x2 IN s') <=>
                x' IN m_space m`
   >- METIS_TAC []
   >> RW_TAC std_ss [IN_INTER]
   >> FULL_SIMP_TAC std_ss [pos_simple_fn_def]
   >> `m_space m = (BIGUNION (IMAGE a s)) INTER (BIGUNION (IMAGE b s'))`
                by METIS_TAC [INTER_IDEMPOT]
   >> POP_ORW
   >> Q.PAT_X_ASSUM `BIGUNION (IMAGE b s') = m_space m` (K ALL_TAC)
   >> Q.PAT_X_ASSUM `BIGUNION (IMAGE a s) = m_space m` (K ALL_TAC)
   >> RW_TAC std_ss [IN_INTER, IN_BIGUNION, IN_IMAGE]
   >> METIS_TAC []);

(* z/z' c is the standard representation of f/g *)
val psfis_present = store_thm
  ("psfis_present",
   ``!m f g a b.
        measure_space m /\
        a IN psfis m f /\ b IN psfis m g ==>
        ?z z' c (k:num->bool).
                (!t. t IN m_space m ==> (f t = SIGMA (\i. Normal (z  i) * (indicator_fn (c i) t)) k)) /\
                (!t. t IN m_space m ==> (g t = SIGMA (\i. Normal (z' i) * (indicator_fn (c i) t)) k)) /\
                (a = pos_simple_fn_integral m k c z) /\
                (b = pos_simple_fn_integral m k c z') /\
                FINITE k /\ (!i. i IN k ==> 0 <= z i) /\ (!i. i IN k ==> 0 <= z' i) /\
                (!i j. i IN k /\ j IN k /\ i <> j ==> DISJOINT (c i) (c j)) /\
                (!i. i IN k ==> c i IN measurable_sets m) /\
                (BIGUNION (IMAGE c k) = m_space m)``,
   RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
   >> Cases_on `x'` >> Cases_on `x` >> Cases_on `x''` >> Cases_on `x'''`
   >> Cases_on `r'` >> Cases_on `r` >> Cases_on `r''` >> Cases_on `r'''`
   >> RW_TAC std_ss []
   >> FULL_SIMP_TAC std_ss [PAIR_EQ]
   >> MATCH_MP_TAC pos_simple_fn_integral_present
   >> METIS_TAC []);

(* ------------------------------------------------------ *)
(*        Properties of POSTIVE SIMPLE FUNCTIONS          *)
(* ------------------------------------------------------ *)

val pos_simple_fn_thm1 = store_thm
  ("pos_simple_fn_thm1",
  ``!m f s a x i y. measure_space m /\ pos_simple_fn m f s a x /\
                    i IN s /\ y IN a i ==> (f y = Normal (x i))``,
  RW_TAC std_ss [pos_simple_fn_def]
  >> `y IN m_space m` by METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE,SUBSET_DEF]
  >> `FINITE (s DELETE i)` by RW_TAC std_ss [FINITE_DELETE]
  >> (MP_TAC o Q.SPEC `i` o UNDISCH o
      Q.SPECL [`(\i. Normal (x i) * indicator_fn (a i) y)`,`s DELETE i`])
         (INST_TYPE [alpha |-> ``:num``] EXTREAL_SUM_IMAGE_PROPERTY)
  >> `!x'. (\i. Normal (x i) * indicator_fn (a i) y) x' <> NegInf`
        by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero] \\
            RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  >> RW_TAC std_ss [INSERT_DELETE,DELETE_DELETE]
  >> `!j. j IN (s DELETE i) ==> ~(y IN a j)`
            by (RW_TAC std_ss [IN_DELETE]
                >> `DISJOINT (a i) (a j)` by METIS_TAC []
                >> FULL_SIMP_TAC std_ss [DISJOINT_DEF,INTER_DEF,EXTENSION,GSPECIFICATION,NOT_IN_EMPTY]
                >> METIS_TAC [])
  >> (MP_TAC o Q.ISPEC `(\i:num. Normal (x i) * indicator_fn (a i) y)`
      o UNDISCH o Q.SPEC `s DELETE i`) EXTREAL_SUM_IMAGE_IN_IF
  >> `!x'. (\i. Normal (x i) * indicator_fn (a i) y) x' <> NegInf`
        by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero] \\
            RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  >> RW_TAC std_ss []
  >> `!j. j IN s DELETE i ==> (indicator_fn (a j) y = 0)`
     by RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
  >> RW_TAC std_ss [mul_rzero,EXTREAL_SUM_IMAGE_ZERO,add_rzero,indicator_fn_def,mul_rone]);

val pos_simple_fn_le = store_thm
  ("pos_simple_fn_le",
  ``!m f g s a x x' i. measure_space m /\
                       pos_simple_fn m f s a x /\ pos_simple_fn m g s a x' /\
                       (!x. x IN m_space m ==> g x <= f x) /\
                       i IN s /\ ~(a i = {}) ==> (Normal (x' i) <= Normal (x i))``,
  RW_TAC std_ss []
  >> `!t. t IN a i ==> (f t = Normal (x i))` by METIS_TAC [pos_simple_fn_thm1]
  >> `!t. t IN a i ==> (g t = Normal (x' i))` by METIS_TAC [pos_simple_fn_thm1]
  >> METIS_TAC [CHOICE_DEF,pos_simple_fn_def,MEASURE_SPACE_SUBSET_MSPACE,SUBSET_DEF]);

val pos_simple_fn_cmul = store_thm
  ("pos_simple_fn_cmul",
  ``!m f z. measure_space m /\ pos_simple_fn m f s a x /\ 0 <= z ==>
            ?s' a' x'. pos_simple_fn m (\t. Normal z * f t) s' a' x'``,
  RW_TAC std_ss [pos_simple_fn_def]
  >> Q.EXISTS_TAC `s` >> Q.EXISTS_TAC `a` >> Q.EXISTS_TAC `(\i. z * (x i))`
  >> RW_TAC std_ss [REAL_LE_MUL, GSYM extreal_mul_def]
  >- METIS_TAC [extreal_le_def, extreal_of_num_def, le_mul]
  >> (MP_TAC o Q.SPECL [`(\i. Normal (x i) * indicator_fn (a i) t)`,`z`] o
      UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_CMUL
  >> `!x'. (\i. Normal (x i) * indicator_fn (a i) t) x' <> NegInf`
        by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero] \\
            RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  >> FULL_SIMP_TAC std_ss [mul_assoc]);

val pos_simple_fn_cmul_alt = store_thm
  ("pos_simple_fn_cmul_alt",
  ``!m f s a x z. measure_space m /\ 0 <= z /\ pos_simple_fn m f s a x ==>
                  pos_simple_fn m (\t. Normal z * f t) s a (\i. z * x i)``,
  RW_TAC std_ss [pos_simple_fn_def, REAL_LE_MUL, GSYM extreal_mul_def]
  >- METIS_TAC [extreal_le_def, extreal_of_num_def, le_mul]
  >> (MP_TAC o Q.SPECL [`(\i. Normal (x i) * indicator_fn (a i) t)`,`z`] o
      UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_CMUL
  >> `!x'. (\i. Normal (x i) * indicator_fn (a i) t) x' <> NegInf`
        by (RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero]
            >> RW_TAC std_ss [extreal_of_num_def, extreal_not_infty])
  >> FULL_SIMP_TAC std_ss [mul_assoc]);

val pos_simple_fn_add = store_thm
  ("pos_simple_fn_add",
  ``!m f g. measure_space m /\
            pos_simple_fn m f s a x /\ pos_simple_fn m g s' a' x' ==>
            ?s'' a'' x''. pos_simple_fn m (\t. f t + g t) s'' a'' x''``,
  rpt STRIP_TAC
  >> (MP_TAC o Q.SPECL [`m`,`f`,`s`,`a`,`x`,`g`,`s'`,`a'`,`x'`]) pos_simple_fn_integral_present
  >> RW_TAC std_ss []
  >> Q.EXISTS_TAC `k`
  >> Q.EXISTS_TAC `c` >> Q.EXISTS_TAC `(\i. z i + z' i)`
  >> RW_TAC std_ss [pos_simple_fn_def, REAL_LE_ADD, GSYM extreal_add_def]
  >- METIS_TAC [le_add, pos_simple_fn_def]
  >> `!i. i IN k ==> Normal (z i) <> NegInf /\ Normal (z' i) <> NegInf /\
                     0 <= Normal (z i) /\ 0 <= Normal (z' i)`
         by METIS_TAC [extreal_not_infty,extreal_of_num_def,extreal_le_def]
  >> `!i. i IN k ==> (\i. (Normal (z i) + Normal (z' i)) * indicator_fn (c i) t) i <> NegInf`
         by METIS_TAC [extreal_add_def, indicator_fn_def, mul_rzero, mul_rone, extreal_of_num_def,
                       extreal_not_infty]
  >> (MP_TAC o Q.SPEC `(\i:num. (Normal (z i) + Normal (z' i)) *  indicator_fn (c i) t)`
      o UNDISCH o Q.ISPEC `k:num->bool`) EXTREAL_SUM_IMAGE_IN_IF
  >> RW_TAC std_ss [add_rdistrib]
  >> (MP_TAC o Q.SPEC `(\x. Normal (z x) * indicator_fn (c x) t + Normal (z' x) * indicator_fn (c x) t)`
      o UNDISCH o Q.ISPEC `k:num->bool` o GSYM) EXTREAL_SUM_IMAGE_IN_IF
  >> `!x. x IN k ==>  NegInf <>
       (\x. Normal (z x) * indicator_fn (c x) t + Normal (z' x) * indicator_fn (c x) t) x`
        by (RW_TAC std_ss [extreal_add_def,indicator_fn_def,mul_rzero,mul_rone,add_rzero]
            >> METIS_TAC [extreal_of_num_def,extreal_not_infty])
  >> RW_TAC std_ss []
  >> `(\x. Normal (z x) * indicator_fn (c x) t + Normal (z' x) * indicator_fn (c x) t) =
      (\x. (\x. Normal (z x) * indicator_fn (c x) t) x + (\x. Normal (z' x) * indicator_fn (c x) t) x)`
           by METIS_TAC []
  >> POP_ORW
  >> (MP_TAC o Q.SPECL [`(\x:num. Normal (z x) * indicator_fn (c x) t)`,
                        `(\x:num. Normal (z' x) * indicator_fn (c x) t)`]
      o UNDISCH o Q.ISPEC `k:num->bool` o GSYM) EXTREAL_SUM_IMAGE_ADD
  >> `!x:num. x IN k ==> NegInf <> (\x:num. Normal (z x) * indicator_fn (c x) t) x /\
                         NegInf <> (\x:num. Normal (z' x) * indicator_fn (c x) t) x`
        by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,add_rzero]
            >> METIS_TAC [extreal_of_num_def,extreal_not_infty])
  >> METIS_TAC []);

val pos_simple_fn_add_alt = store_thm
  ("pos_simple_fn_add_alt",
  ``!m f g s a x y. measure_space m /\
                    pos_simple_fn m f s a x /\ pos_simple_fn m g s a y
                ==> pos_simple_fn m (\t. f t + g t) s a (\i. x i + y i)``,
  RW_TAC std_ss [pos_simple_fn_def,REAL_LE_ADD,GSYM extreal_add_def,le_add]
  >> `!i. i IN s ==> Normal (x i) <> NegInf /\ Normal (y i) <> NegInf /\ 0 <= Normal (x i) /\ 0 <= Normal (y i)`
         by METIS_TAC [extreal_not_infty,extreal_of_num_def,extreal_le_def]
  >> `!i. i IN s ==> (\i. (Normal (x i) + Normal (y i)) * indicator_fn (a i) t) i <> NegInf`
         by METIS_TAC [extreal_add_def,indicator_fn_def,mul_rzero,mul_rone,extreal_of_num_def,extreal_not_infty]
  >> (MP_TAC o Q.SPEC `(\i:num. (Normal (x i) + Normal (y i)) *  indicator_fn (a i) t)`
      o UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_IN_IF
  >> RW_TAC std_ss [add_rdistrib]
  >> (MP_TAC o Q.SPEC `(\i. Normal (x i) * indicator_fn (a i) t + Normal (y i) * indicator_fn (a i) t)`
      o UNDISCH o Q.ISPEC `s:num->bool` o GSYM) EXTREAL_SUM_IMAGE_IN_IF
  >> `!i. i IN s ==>  NegInf <>
       (\i. Normal (x i) * indicator_fn (a i) t + Normal (y i) * indicator_fn (a i) t) i`
        by (RW_TAC std_ss [extreal_add_def,indicator_fn_def,mul_rzero,mul_rone,add_rzero]
            >> METIS_TAC [extreal_of_num_def,extreal_not_infty])
  >> RW_TAC std_ss []
  >> `(\i. Normal (x i) * indicator_fn (a i) t + Normal (y i) * indicator_fn (a i) t) =
      (\i. (\i. Normal (x i) * indicator_fn (a i) t) i + (\i. Normal (y i) * indicator_fn (a i) t) i)`
           by METIS_TAC []
  >> POP_ORW
  >> (MP_TAC o Q.SPECL [`(\i:num. Normal (x i) * indicator_fn (a i) t)`,
                        `(\i:num. Normal (y i) * indicator_fn (a i) t)`]
      o UNDISCH o Q.ISPEC `s:num->bool` o GSYM) EXTREAL_SUM_IMAGE_ADD
  >> `!i:num. i IN s ==> NegInf <> (\i:num. Normal (x i) * indicator_fn (a i) t) i /\
                         NegInf <> (\i:num. Normal (y i) * indicator_fn (a i) t) i`
        by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,add_rzero]
            >> METIS_TAC [extreal_of_num_def,extreal_not_infty])
  >> METIS_TAC []);

val pos_simple_fn_indicator = store_thm
  ("pos_simple_fn_indicator",
  ``!m A. measure_space m /\ A IN measurable_sets m ==>
          ?s a x. pos_simple_fn m (indicator_fn A) s a x``,
    RW_TAC std_ss []
 >> `FINITE {0:num; 1:num}` by METIS_TAC [FINITE_INSERT, FINITE_SING]
 >> Q.EXISTS_TAC `{0:num; 1:num}`
 >> Q.EXISTS_TAC `(\i. if i = 0 then (m_space m DIFF A) else A)`
 >> Q.EXISTS_TAC `(\i. if i = 0 then 0 else 1)`
 >> RW_TAC std_ss [pos_simple_fn_def, indicator_fn_def, FINITE_SING, IN_SING,
                   MEASURE_SPACE_MSPACE_MEASURABLE]
 >| [ (* goal 1 (of 6) *)
      METIS_TAC [le_01, le_refl],
      (* goal 2 (of 6) *)
     `FINITE {1:num}` by METIS_TAC [FINITE_SING] \\
      Know `{1:num} DELETE 0 = {1}`
      >- (RW_TAC std_ss [DELETE_DEF, DIFF_DEF, IN_SING] \\
          RW_TAC std_ss [EXTENSION, IN_SING] \\
          RW_TAC std_ss [GSPECIFICATION] \\
          EQ_TAC >- RW_TAC arith_ss [] \\
          RW_TAC arith_ss []) >> DISCH_TAC \\
      (MP_TAC o Q.SPEC `0` o UNDISCH o
       Q.ISPECL [`(\i:num. Normal (if i = 0 then 0 else 1) *
                           if t IN if i = 0 then m_space m DIFF A else A then 1 else 0)`, `{1:num}`])
          EXTREAL_SUM_IMAGE_PROPERTY \\
     `!x. (\i:num. Normal (if i = 0 then 0 else 1) *
                   if t IN if i = 0 then m_space m DIFF A else A then 1 else 0) x <> NegInf`
           by (RW_TAC std_ss [mul_rone,mul_rzero] \\
               RW_TAC std_ss [extreal_of_num_def,extreal_not_infty]) \\
      RW_TAC real_ss [EXTREAL_SUM_IMAGE_SING, extreal_of_num_def, extreal_mul_def, extreal_add_def],
      (* goal 3 (of 6) *)
      METIS_TAC [MEASURE_SPACE_DIFF, MEASURE_SPACE_MSPACE_MEASURABLE],
      (* goal 4 (of 6) *)
      RW_TAC real_ss [],
      (* goal 5 (of 6) *)
      FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, GSPECIFICATION, IN_INTER, IN_DIFF,
                            NOT_IN_EMPTY, IN_INSERT, IN_SING] \\
      METIS_TAC [],
      (* goal 6 (of 6) *)
      RW_TAC std_ss [IMAGE_DEF] \\
     `{if i:num = 0 then m_space m DIFF A else A | i IN {0; 1}} = {m_space m DIFF A; A}`
             by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INSERT, IN_SING] \\
                 EQ_TAC >- METIS_TAC [] \\
                 RW_TAC std_ss [] >- METIS_TAC [] \\
                 Q.EXISTS_TAC `1:num` \\
                 RW_TAC real_ss []) \\
      RW_TAC std_ss [BIGUNION_INSERT, BIGUNION_SING] \\
      METIS_TAC [UNION_DIFF, MEASURE_SPACE_SUBSET_MSPACE] ]);

val pos_simple_fn_indicator_alt = store_thm
  ("pos_simple_fn_indicator_alt",
  ``!m s. measure_space m /\ s IN measurable_sets m ==>
          pos_simple_fn m (indicator_fn s) {0:num;1:num}
                        (\i:num. if i = 0 then (m_space m DIFF s) else s)
                        (\i. if i = 0 then 0 else 1)``,
    RW_TAC std_ss []
 >> `FINITE {0:num;1:num}` by METIS_TAC [FINITE_INSERT, FINITE_SING]
 >> RW_TAC real_ss [pos_simple_fn_def, indicator_fn_def, FINITE_SING, IN_SING,
                    MEASURE_SPACE_MSPACE_MEASURABLE]
 >| [ (* goal 1 (of 6) *)
      METIS_TAC [le_01, le_refl],
      (* goal 2 (of 6) *)
     `FINITE {1:num}` by METIS_TAC [FINITE_SING] \\
      Know `{1:num} DELETE 0 = {1}`
      >- (RW_TAC std_ss [DELETE_DEF, DIFF_DEF, IN_SING] \\
          RW_TAC std_ss [EXTENSION, IN_SING] \\
          RW_TAC std_ss [GSPECIFICATION] \\
          EQ_TAC >- RW_TAC arith_ss [] \\
          RW_TAC arith_ss []) >> DISCH_TAC \\
     (MP_TAC o Q.SPEC `0` o UNDISCH o
      Q.ISPECL [`(\i:num. Normal (if i = 0 then 0 else 1) *
                     if t IN if i = 0 then m_space m DIFF s else s then 1 else 0)`, `{1:num}`])
        EXTREAL_SUM_IMAGE_PROPERTY \\
     `!x. (\i:num. Normal (if i = 0 then 0 else 1) *
              if t IN if i = 0 then m_space m DIFF s else s then 1 else 0) x <> NegInf`
           by (RW_TAC std_ss [mul_rone,mul_rzero] \\
               RW_TAC std_ss [extreal_of_num_def, extreal_not_infty]) \\
      RW_TAC real_ss [EXTREAL_SUM_IMAGE_SING, extreal_of_num_def, extreal_mul_def,
                      extreal_add_def],
      (* goal 3 (of 6) *)
      METIS_TAC [MEASURE_SPACE_DIFF, MEASURE_SPACE_MSPACE_MEASURABLE],
      (* goal 4 (of 6) *)
      RW_TAC real_ss [],
      (* goal 5 (of 6) *)
      FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, GSPECIFICATION, IN_INTER, IN_DIFF,
                            NOT_IN_EMPTY, IN_INSERT, IN_SING] \\
      METIS_TAC [],
      (* goal 6 (of 6) *)
      RW_TAC std_ss [IMAGE_DEF] \\
     `{if i:num = 0 then m_space m DIFF s else s | i IN {0; 1}} = {m_space m DIFF s; s}`
             by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INSERT, IN_SING]
                 >> EQ_TAC >- METIS_TAC []
                 >> RW_TAC std_ss [] >- METIS_TAC []
                 >> Q.EXISTS_TAC `1:num`
                 >> RW_TAC real_ss []) \\
      RW_TAC std_ss [BIGUNION_INSERT, BIGUNION_SING] \\
      METIS_TAC [UNION_DIFF, MEASURE_SPACE_SUBSET_MSPACE] ]);

val pos_simple_fn_max = store_thm
  ("pos_simple_fn_max",
  ``!m f (s:num->bool) a x g (s':num->bool) b y.
         measure_space m /\ pos_simple_fn m f s a x /\ pos_simple_fn m g s' b y ==>
         ?s'' a'' x''. pos_simple_fn m (\x. max (f x) (g x)) s'' a'' x''``,
    RW_TAC std_ss []
 >> `?p n. BIJ p (count n) (s CROSS s')`
     by FULL_SIMP_TAC std_ss [GSYM FINITE_BIJ_COUNT, pos_simple_fn_def, FINITE_CROSS]
 >> `?p'. BIJ p' (s CROSS s') (count n) /\ (!x. x IN (count n) ==> ((p' o p) x = x))
           /\ (!x. x IN (s CROSS s') ==> ((p o p') x = x))`
     by (MATCH_MP_TAC BIJ_INV >> RW_TAC std_ss [])
 >> Q.EXISTS_TAC `IMAGE p' (s CROSS s')`
 >> Q.EXISTS_TAC `(\(i,j). a i INTER b j) o p`
 >> Q.EXISTS_TAC `(\n. max ((x o FST o p) n) ((y o SND o p)n))`
 >> RW_TAC std_ss [FUN_EQ_THM]
 >> FULL_SIMP_TAC std_ss [pos_simple_fn_def,extreal_max_def]
 >> `!i j. i IN IMAGE p' (s CROSS s') /\ j IN IMAGE p' (s CROSS s') /\ i <> j ==>
           DISJOINT (((\(i,j). a i INTER b j) o p) i) (((\(i,j). a i INTER b j) o p) j)`
    by (RW_TAC std_ss [DISJOINT_DEF, IN_IMAGE]
        >> RW_TAC std_ss [Once EXTENSION, NOT_IN_EMPTY, IN_INTER]
        >> FULL_SIMP_TAC std_ss [o_DEF]
        >> (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
        >> (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
        >> RW_TAC std_ss []
        >> RW_TAC std_ss []
        >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
        >> FULL_SIMP_TAC std_ss [IN_INTER, IN_CROSS, FST, SND, pos_simple_fn_def,DISJOINT_DEF]
        >> METIS_TAC [EXTENSION, NOT_IN_EMPTY, IN_INTER])
 >> `!i. i IN IMAGE p' (s CROSS s') ==>  ((\(i,j). a i INTER b j) o p) i IN measurable_sets m`
    by (RW_TAC std_ss [IN_IMAGE]
        >> FULL_SIMP_TAC std_ss [o_DEF]
        >> (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES
               >> RW_TAC std_ss []
        >> FULL_SIMP_TAC std_ss [IN_CROSS, FST, SND, pos_simple_fn_def]
        >> METIS_TAC [ALGEBRA_INTER, subsets_def, space_def,sigma_algebra_def, measure_space_def])
 >> `BIGUNION (IMAGE ((\(i,j). a i INTER b j) o p) (IMAGE p' (s CROSS s'))) = m_space m`
    by (RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, IN_IMAGE, IN_CROSS]
        >> `!s'' x. (?x'. ((x = p' x') /\ FST x' IN s /\ SND x' IN s')) <=>
                    (?x1 x2. ((x = p' (x1,x2)) /\ x1 IN s /\ x2 IN s'))`
            by METIS_TAC [PAIR, FST, SND]
        >> POP_ORW
        >> `!s''. (?x. (s'' = (\(i,j). a i INTER b j) (p x)) /\
                                       ?x1 x2. (x = p' (x1,x2)) /\ x1 IN s /\ x2 IN s') <=>
                  (?x1 x2. (s'' = (\(i,j). a i INTER b j) (p (p' (x1,x2)))) /\  x1 IN s /\ x2 IN s')`
            by METIS_TAC []
        >> POP_ORW
        >> FULL_SIMP_TAC std_ss [o_DEF, IN_CROSS]
        >> `!s''. (?x1 x2. (s'' = (\(i,j). a i INTER b j) (p (p' (x1,x2)))) /\ x1 IN s /\ x2 IN s') <=>
                  (?x1 x2. (s'' = (\(i,j). a i INTER b j) (x1,x2)) /\ x1 IN s /\ x2 IN s')`
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
 >> `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS]
 >> `INJ p' (s CROSS s')(IMAGE p' (s CROSS s'))` by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF]
 >> `FINITE (IMAGE p' (s CROSS s'))` by RW_TAC std_ss [IMAGE_FINITE]
 >> FULL_SIMP_TAC std_ss []
 >> CONJ_TAC >- METIS_TAC []
 >> Reverse CONJ_TAC
 >- (RW_TAC std_ss [max_def] >> FULL_SIMP_TAC std_ss [IN_IMAGE,IN_CROSS])
 >> RW_TAC std_ss []
 >- ((MP_TAC o Q.SPEC `(\i. Normal (y i) * indicator_fn (b i) x')` o UNDISCH o
       Q.ISPEC `(s' :num -> bool)`) EXTREAL_SUM_IMAGE_IN_IF
     >> `!x. (\i. Normal (y i) * indicator_fn (b i) x') x <> NegInf`
           by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
               >> RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
     >> RW_TAC std_ss []
     >> POP_ASSUM (K ALL_TAC)
     >> `(\x. (if x IN s' then (\i. Normal (y i) * indicator_fn (b i) x') x else 0)) =
         (\x. (if x IN s' then (\i. Normal (y i) *
                                     SIGMA (\j. indicator_fn (a j INTER b i) x') s) x else 0))`
          by (RW_TAC std_ss [FUN_EQ_THM]
              >> RW_TAC std_ss []
              >> FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
              >> (MP_TAC o REWRITE_RULE [Once INTER_COMM] o Q.ISPEC `(b :num -> 'a set) (x'' :num)`
                  o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO]
                  o Q.ISPECL [`(s :num -> bool)`, `m_space (m: 'a m_space)`,
                              `(a :num -> 'a set)`]) indicator_fn_split
              >> Q.PAT_X_ASSUM `!i. i IN s' ==> (b:num->'a->bool) i IN measurable_sets m`
                     (ASSUME_TAC o UNDISCH o Q.SPEC `x''`)
              >> `!a m. measure_space m /\ a IN measurable_sets m ==> a SUBSET m_space m`
                  by RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,
                                    subset_class_def, subsets_def, space_def]
              >> POP_ASSUM (ASSUME_TAC o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
                            Q.ISPECL [`(b :num -> 'a set) (x'' :num)`,
                                      `(m :'a m_space)`])
              >> ASM_SIMP_TAC std_ss [])
     >> `(\x. if x IN s' then Normal (y x) * indicator_fn (b x) x' else 0) =
         (\x. if x IN s' then (\i. Normal (y i) * indicator_fn (b i) x') x else 0)`
          by METIS_TAC []
     >> POP_ORW
     >> POP_ORW
     >> `!(x:num) (i:num). Normal (y i) * SIGMA (\j. indicator_fn (a j INTER b i) x') s =
                            SIGMA (\j. Normal (y i) * indicator_fn (a j INTER b i) x') s`
           by (RW_TAC std_ss []
               >> (MP_TAC o Q.SPECL [`(\j. indicator_fn (a j INTER (b:num->'a->bool) i) x')`,`y (i:num)`]
                   o UNDISCH o Q.ISPEC `s:num->bool` o GSYM
                   o INST_TYPE [alpha |-> ``:num``, beta |-> ``:num``]) EXTREAL_SUM_IMAGE_CMUL
               >> `!x. NegInf <> (\j. indicator_fn (a j INTER b i) x') x`
                     by RW_TAC std_ss [indicator_fn_def,extreal_of_num_def,extreal_not_infty]
               >> RW_TAC std_ss [])
      >> POP_ORW
      >> (MP_TAC o Q.ISPEC `(\n':num. Normal (max (x (FST (p n'))) (y (SND (p n')))) *
                                      indicator_fn ((\(i:num,j:num). a i INTER b j) (p n')) x')`
          o UNDISCH o Q.SPEC `p'` o UNDISCH
          o (Q.ISPEC `((s:num->bool) CROSS (s':num->bool))`)
          o (INST_TYPE [``:'b``|->``:num``])) EXTREAL_SUM_IMAGE_IMAGE
      >> `!x''. (\n'. Normal (max (x (FST (p n'))) (y (SND (p n')))) *
                 indicator_fn ((\(i,j). a i INTER b j) (p n')) x') x'' <> NegInf`
                 by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
                     >> RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
      >> RW_TAC std_ss [o_DEF]
      >> POP_ASSUM (K ALL_TAC)
      >> (MP_TAC o Q.SPEC `(\x''. Normal (max (x (FST ((p :num -> num # num) (p' x''))))
                                              (y (SND (p (p' x''))))) *
                                  indicator_fn ((\(i:num,j:num). a i INTER b j) (p (p' x''))) x')`
          o UNDISCH o Q.ISPEC `(s :num set) CROSS (s' :num set)`) EXTREAL_SUM_IMAGE_IN_IF
      >> `!x''. (\x''. Normal (max (x (FST (p (p' x'')))) (y (SND (p (p' x''))))) *
                      indicator_fn ((\(i,j). a i INTER b j) (p (p' x''))) x') x'' <> NegInf`
                 by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
                     >> RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
      >> RW_TAC std_ss []
      >> NTAC 4 (POP_ASSUM (K ALL_TAC))
      >> `!x. (\j. Normal (y x) * indicator_fn (a j INTER b x) x') =
              (\x j. Normal (y x) * indicator_fn (a j INTER b x) x') x` by METIS_TAC []
      >> POP_ORW
      >> `!x. SIGMA ((\x j. Normal (y x) * indicator_fn (a j INTER b x) x') x) s <> NegInf`
            by (RW_TAC std_ss []
                >> `!j. Normal (y x'') * indicator_fn (a j INTER b x'') x' <> NegInf`
                      by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
                          >> RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
                >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY])
      >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_IF_ELIM]
      >> (MP_TAC o Q.SPEC `(\x j. Normal (y x) * indicator_fn (a j INTER b x) x')`
          o Q.ISPECL [`s':num->bool`,`s:num->bool`]) EXTREAL_SUM_IMAGE_SUM_IMAGE
      >> `!x. NegInf <> (\x j. Normal (y x) * indicator_fn (a j INTER b x) x') (FST x) (SND x)`
              by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
                  >> RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
      >> RW_TAC std_ss []
      >> `(s' CROSS s) = IMAGE (\x. (SND x, FST x)) (s CROSS s')`
              by (RW_TAC std_ss [Once EXTENSION, IN_CROSS, IN_IMAGE]
                  >> (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
                  >> RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND]
                  >> EQ_TAC
                  >- (STRIP_TAC >> Q.EXISTS_TAC `(r,q)` >> RW_TAC std_ss [FST,SND])
                  >> RW_TAC std_ss [] >> RW_TAC std_ss [])
      >> POP_ORW
      >> `INJ (\x. (SND x,FST x)) (s CROSS s') (IMAGE (\x. (SND x,FST x)) (s CROSS s'))`
              by (RW_TAC std_ss [INJ_DEF, IN_CROSS, IN_IMAGE]
                  >- METIS_TAC []
                  >> (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES
                  >> (MP_TAC o Q.ISPEC `x''':num#num`) pair_CASES
                  >> RW_TAC std_ss []
                  >> FULL_SIMP_TAC std_ss [FST,SND])
      >> (MP_TAC o Q.SPEC `(\x. Normal (y (FST x)) * indicator_fn (a (SND x) INTER b (FST x)) x')`
           o UNDISCH o Q.SPEC `(\x. (SND x, FST x))` o UNDISCH
           o Q.ISPEC `((s:num->bool) CROSS (s':num->bool))`
           o INST_TYPE [``:'b``|->``:num#num``]) EXTREAL_SUM_IMAGE_IMAGE
      >> `!x. (\x. Normal (y (FST x)) * indicator_fn (a (SND x) INTER b (FST x)) x') x <> NegInf`
              by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
                  >> RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
      >> RW_TAC std_ss [o_DEF]
      >> Suff `!x'''. x''' IN (s CROSS s') ==>
                      ((\x. Normal (y (SND x)) * indicator_fn (a (FST x) INTER b (SND x)) x') x''' =
                       (\x''. if x'' IN s CROSS s' then
                                Normal (max (x (FST x'')) (y (SND x''))) *
                                indicator_fn ((\ (i,j). a i INTER b j) x'') x'
                              else 0) x''')`
      >- (RW_TAC std_ss []
           >> (MATCH_MP_TAC o UNDISCH o Q.ISPEC `(s:num->bool) CROSS (s':num->bool)`)
                 EXTREAL_SUM_IMAGE_EQ
           >> RW_TAC std_ss []
           >> DISJ1_TAC
           >> RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
           >> RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
       >> RW_TAC std_ss [FUN_EQ_THM]
       >> Cases_on `x'''`
       >> RW_TAC real_ss [indicator_fn_def,mul_rone,mul_rzero]
       >> `q IN s` by METIS_TAC [IN_CROSS,FST,SND]
       >> `x' IN (a q)` by METIS_TAC [IN_INTER]
       >> `SIGMA (\i. Normal (x i) * indicator_fn (a i) x') s = Normal (x q)`
           by (`pos_simple_fn m f s a x` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
               >> METIS_TAC [pos_simple_fn_thm1])
       >> `r IN s'` by METIS_TAC [IN_CROSS,FST,SND]
       >> `x' IN (b r)` by METIS_TAC [IN_INTER]
       >> `SIGMA (\i. Normal (y i) * indicator_fn (b i) x') s' = Normal (y r)`
          by (`pos_simple_fn m g s' b y` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
              >> METIS_TAC [pos_simple_fn_thm1])
       >> FULL_SIMP_TAC std_ss [extreal_le_def,max_def])
  >> (MP_TAC o Q.SPEC `(\i. Normal (x i) * indicator_fn (a i) x')`
      o UNDISCH o Q.ISPEC `(s :num -> bool)`) EXTREAL_SUM_IMAGE_IN_IF
  >> `!x''. (\i. Normal (x i) * indicator_fn (a i) x') x'' <> NegInf`
         by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
             >> RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  >> RW_TAC std_ss []
  >> POP_ASSUM (K ALL_TAC)
  >> `(\x''. if x'' IN s then Normal (x x'') * indicator_fn (a x'') x' else 0) =
      (\x''. if x'' IN s then (\i. Normal (x i) * indicator_fn (a i) x') x'' else 0)`
          by METIS_TAC []
  >> POP_ORW
  >> `(\x''. (if x'' IN s then (\i. Normal (x i) * indicator_fn (a i) x') x'' else 0)) =
      (\x''. (if x'' IN s then (\i. Normal (x i) *
                                    SIGMA (\j. indicator_fn (a i INTER b j) x') s') x''
                          else 0))`
         by (RW_TAC std_ss [FUN_EQ_THM]
             >> RW_TAC std_ss []
             >> FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
             >> (MP_TAC o Q.ISPEC `(a :num -> 'a set) (x'' :num)` o UNDISCH_ALL
                 o REWRITE_RULE [GSYM AND_IMP_INTRO]
                 o Q.ISPECL [`(s':num -> bool)`, `m_space (m :'a m_space)`,
                             `(b :num -> 'a set)`]) indicator_fn_split
             >> `a x'' SUBSET m_space m` by METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE]
             >> RW_TAC std_ss [])
  >> POP_ORW
  >> `!(i:num). Normal (x i) * SIGMA (\j. indicator_fn (a i INTER b j) x') s' =
                SIGMA (\j. Normal (x i) * indicator_fn (a i INTER b j) x') s'`
         by (RW_TAC std_ss []
             >> (MP_TAC o
                 Q.SPECL [`(\j. indicator_fn ((a :num -> 'a set) i INTER b j) x')`, `x (i:num)`] o
                 UNDISCH o Q.ISPEC `s':num->bool` o GSYM o
                 INST_TYPE [alpha |-> ``:num``, beta |-> ``:num``]) EXTREAL_SUM_IMAGE_CMUL
             >> `!x. NegInf <> (\j. indicator_fn (a i INTER b j) x') x`
                    by RW_TAC std_ss [indicator_fn_def,extreal_of_num_def,extreal_not_infty]
             >> RW_TAC std_ss [])
  >> POP_ORW
  >> (MP_TAC o Q.ISPEC `(\n':num. Normal (max (x (FST (p n'))) (y (SND (p n')))) *
                         indicator_fn ((\(i:num,j:num). a i INTER b j) (p n')) x')` o
               UNDISCH o Q.SPEC `p'` o UNDISCH o
               Q.ISPEC `((s:num->bool) CROSS (s':num->bool))` o
               INST_TYPE [``:'b``|->``:num``]) EXTREAL_SUM_IMAGE_IMAGE
  >> `!x''. (\n'. Normal (max (x (FST (p n'))) (y (SND (p n')))) *
             indicator_fn ((\(i,j). a i INTER b j) (p n')) x') x'' <> NegInf`
              by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
                  >> RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  >> RW_TAC std_ss [o_DEF]
  >> POP_ASSUM (K ALL_TAC)
  >> (MP_TAC o Q.SPEC `(\x''. Normal (max (x (FST ((p :num -> num # num) (p' x''))))
                                          (y (SND (p (p' x''))))) *
                              indicator_fn ((\(i:num,j:num). a i INTER b j) (p (p' x''))) x')`
      o UNDISCH o Q.ISPEC `(s :num set) CROSS (s' :num set)`) EXTREAL_SUM_IMAGE_IN_IF
  >> `!x''. (\x''. Normal (max (x (FST (p (p' x'')))) (y (SND (p (p' x''))))) *
                   indicator_fn ((\(i,j). a i INTER b j) (p (p' x''))) x') x'' <> NegInf`
        by (RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero] \\
            RW_TAC std_ss [extreal_of_num_def, extreal_not_infty])
  >> RW_TAC std_ss []
  >> NTAC 4 (POP_ASSUM (K ALL_TAC))
  >> `!x''. (\j. Normal (x x'') * indicator_fn (a x'' INTER b j) x') =
            (\x'' j. Normal (x x'') * indicator_fn (a x'' INTER b j) x') x''` by METIS_TAC []
  >> POP_ORW
  >> `!x''. SIGMA ((\x'' j. Normal (x x'') * indicator_fn (a x'' INTER b j) x') x'') s' <> NegInf`
        by (RW_TAC std_ss []
            >> `!j. Normal (x x'') * indicator_fn (a x'' INTER b j) x' <> NegInf`
                  by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
                      >> RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
            >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY])
  >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_IF_ELIM]
  >> (MP_TAC o Q.SPEC `(\x'' j. Normal (x x'') * indicator_fn (a x'' INTER b j) x')`
      o Q.ISPECL [`s:num->bool`,`s':num->bool`]) EXTREAL_SUM_IMAGE_SUM_IMAGE
  >> `!x''. NegInf <> (\x'' j. Normal (x x'') * indicator_fn (a x'' INTER b j) x') (FST x'') (SND x'')`
            by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
                >> RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  >> RW_TAC std_ss []
  >> Suff `!x'''. x''' IN (s CROSS s') ==>
                 ((\x''. Normal (x (FST x'')) * indicator_fn (a (FST x'') INTER b (SND x'')) x') x''' =
                  (\x''. if x'' IN s CROSS s' then Normal (max (x (FST x'')) (y (SND x''))) *
                                                   indicator_fn ((\(i,j). a i INTER b j) x'') x'
                         else 0) x''')`
  >- (RW_TAC std_ss []
      >> (MATCH_MP_TAC o UNDISCH o Q.ISPEC `(s:num->bool) CROSS (s':num->bool)`) EXTREAL_SUM_IMAGE_EQ
      >> RW_TAC std_ss []
      >> DISJ1_TAC
      >> RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
      >> RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
  >> RW_TAC std_ss [FUN_EQ_THM]
  >> Cases_on `x'''`
  >> RW_TAC real_ss [indicator_fn_def,mul_rone,mul_rzero]
  >> `q IN s` by METIS_TAC [IN_CROSS,FST,SND]
  >> `x' IN (a q)` by METIS_TAC [IN_INTER]
  >> `SIGMA (\i. Normal (x i) * indicator_fn (a i) x') s = Normal (x q)`
        by (`pos_simple_fn m f s a x` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
            >> METIS_TAC [pos_simple_fn_thm1])
  >> `r IN s'` by METIS_TAC [IN_CROSS,FST,SND]
  >> `x' IN (b r)` by METIS_TAC [IN_INTER]
  >> `SIGMA (\i. Normal (y i) * indicator_fn (b i) x') s' = Normal (y r)`
        by (`pos_simple_fn m g s' b y` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
            >> METIS_TAC [pos_simple_fn_thm1])
  >> FULL_SIMP_TAC std_ss [extreal_le_def,max_def]);

val pos_simple_fn_not_infty = store_thm
  ("pos_simple_fn_not_infty",
  ``!m f s a x. pos_simple_fn m f s a x ==>
                !x. x IN m_space m ==> f x <> NegInf /\ f x <> PosInf``,
    RW_TAC std_ss [pos_simple_fn_def]
 >> `(!i. i IN s ==> (\i. Normal (x i) * indicator_fn (a i) x') i <> NegInf)`
     by (RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone] \\
         RW_TAC std_ss [extreal_of_num_def, extreal_not_infty])
 >> `(!i. i IN s ==> (\i. Normal (x i) * indicator_fn (a i) x') i <> PosInf)`
     by (RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone] \\
         RW_TAC std_ss [extreal_of_num_def, extreal_not_infty])
 >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY]);

(* ************************************************************************* *)
(* Properties of Integrals of Positive Simple Functions                      *)
(* ************************************************************************* *)

val pos_simple_fn_integral_add = store_thm
  ("pos_simple_fn_integral_add",
  ``!m f (s :num -> bool) a x
       g (s':num -> bool) b y. measure_space m /\
                               pos_simple_fn m f s a x /\
                               pos_simple_fn m g s' b y ==>
       ?s'' c z. pos_simple_fn m (\x. f x + g x) s'' c z /\
                (pos_simple_fn_integral m s a x +
                 pos_simple_fn_integral m s' b y =
                 pos_simple_fn_integral m s'' c z)``,
    rpt STRIP_TAC
 >> (MP_TAC o Q.SPECL [`m`,`f`,`s`,`a`,`x`,`g`,`s'`,`b`,`y`]) pos_simple_fn_integral_present
 >> RW_TAC std_ss [] >> ASM_SIMP_TAC std_ss []
 >> Q.EXISTS_TAC `k` >> Q.EXISTS_TAC `c` >> Q.EXISTS_TAC `(\i. z i + z' i)`
 >> FULL_SIMP_TAC std_ss [pos_simple_fn_def, pos_simple_fn_integral_def]
 >> Reverse CONJ_TAC
 >- (RW_TAC std_ss [GSYM extreal_add_def] \\
    `!i. i IN k ==> Normal (z i) <> NegInf /\ Normal (z' i) <> NegInf /\
                    0 <= Normal (z i) /\ 0 <= Normal (z' i)`
        by METIS_TAC [extreal_not_infty, extreal_of_num_def, extreal_le_def] \\
    `!i. i IN k ==> (\i. (Normal (z i) + Normal (z' i)) * measure m (c i)) i <> NegInf`
        by METIS_TAC [extreal_add_def, mul_not_infty, positive_not_infty, measure_space_def,
                      REAL_LE_ADD] \\
    (MP_TAC o Q.SPEC `(\i:num. (Normal (z i) + Normal (z' i)) * measure m (c i))`
     o UNDISCH o Q.ISPEC `k:num->bool`) EXTREAL_SUM_IMAGE_IN_IF \\
     RW_TAC std_ss [add_rdistrib] \\
    (MP_TAC o Q.SPEC `(\x. Normal (z x) * measure m (c x) + Normal (z' x) * measure m (c x))`
     o UNDISCH o Q.ISPEC `k:num->bool` o GSYM) EXTREAL_SUM_IMAGE_IN_IF \\
    `!x. x IN k ==>  NegInf <>
       (\x. Normal (z x) * measure m (c x) + Normal (z' x) * measure m (c x)) x`
        by METIS_TAC [extreal_add_def, mul_not_infty, positive_not_infty, measure_space_def,
                      REAL_LE_ADD, add_not_infty] \\
     RW_TAC std_ss [] \\
    `(\x. Normal (z x) * measure m (c x) + Normal (z' x) * measure m (c x)) =
         (\x. (\x. Normal (z x) * measure m (c x)) x + (\x. Normal (z' x) * measure m (c x)) x)`
        by METIS_TAC [] >> POP_ORW \\
    (MATCH_MP_TAC o UNDISCH o Q.ISPEC `k:num->bool` o GSYM) EXTREAL_SUM_IMAGE_ADD \\
     DISJ1_TAC \\
     METIS_TAC [mul_not_infty, positive_not_infty, measure_space_def, extreal_not_infty])
 >> RW_TAC std_ss [REAL_LE_ADD, le_add]
 >> RW_TAC std_ss [GSYM extreal_add_def]
 >> `!i. i IN k ==> Normal (z i) <> NegInf /\ Normal (z' i) <> NegInf /\
                    0 <= Normal (z i) /\ 0 <= Normal (z' i)`
       by METIS_TAC [extreal_not_infty, extreal_of_num_def, extreal_le_def]
 >> `!i. i IN k ==> (\i. (Normal (z i) + Normal (z' i)) * indicator_fn (c i) x') i <> NegInf`
       by METIS_TAC [extreal_add_def, indicator_fn_def, mul_rzero, mul_rone, extreal_of_num_def,
                     extreal_not_infty]
 >> (MP_TAC o Q.SPEC `(\i:num. (Normal (z i) + Normal (z' i)) *  indicator_fn (c i) x')`
     o UNDISCH o Q.ISPEC `k:num->bool`) EXTREAL_SUM_IMAGE_IN_IF
 >> RW_TAC std_ss [add_rdistrib]
 >> (MP_TAC o Q.SPEC `(\x. Normal (z x) * indicator_fn (c x) x' + Normal (z' x) * indicator_fn (c x) x')`
     o UNDISCH o Q.ISPEC `k:num->bool` o GSYM) EXTREAL_SUM_IMAGE_IN_IF
 >> `!x. x IN k ==>  NegInf <>
       (\x. Normal (z x) * indicator_fn (c x) x' + Normal (z' x) * indicator_fn (c x) x') x`
       by (RW_TAC std_ss [extreal_add_def, indicator_fn_def, mul_rzero, mul_rone, add_rzero] \\
           METIS_TAC [extreal_of_num_def, extreal_not_infty])
 >> RW_TAC std_ss []
 >> `(\x. Normal (z x) * indicator_fn (c x) x' + Normal (z' x) * indicator_fn (c x) x') =
     (\x. (\x. Normal (z x) * indicator_fn (c x) x') x + (\x. Normal (z' x) * indicator_fn (c x) x') x)`
       by METIS_TAC [] >> POP_ORW
 >> (MP_TAC o Q.SPECL [`(\x:num. Normal (z x) * indicator_fn (c x) x')`,
                       `(\x:num. Normal (z' x) * indicator_fn (c x) x')`]
     o UNDISCH o Q.ISPEC `k:num->bool` o GSYM) EXTREAL_SUM_IMAGE_ADD
 >> `!x:num. x IN k ==> NegInf <> (\x:num. Normal (z x) * indicator_fn (c x) x') x /\
                        NegInf <> (\x:num. Normal (z' x) * indicator_fn (c x) x') x`
       by (RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, add_rzero] \\
           METIS_TAC [extreal_of_num_def, extreal_not_infty])
 >> METIS_TAC []);

val pos_simple_fn_integral_add_alt = store_thm
  ("pos_simple_fn_integral_add_alt",
  ``!m f s a x g y. measure_space m /\
        pos_simple_fn m f s a x /\ pos_simple_fn m g s a y ==>
          (pos_simple_fn_integral m s a x +
           pos_simple_fn_integral m s a y =
           pos_simple_fn_integral m s a (\i. x i + y i))``,
    RW_TAC std_ss [pos_simple_fn_def, pos_simple_fn_integral_def,GSYM extreal_add_def]
 >> `!i. i IN s ==> Normal (x i) <> NegInf /\ Normal (y i) <> NegInf /\
                    0 <= Normal (x i) /\ 0 <= Normal (y i)`
        by METIS_TAC [extreal_not_infty,extreal_of_num_def,extreal_le_def]
 >> `!i. i IN s ==> (\i. (Normal (x i) + Normal (y i)) * measure m (a i)) i <> NegInf`
        by METIS_TAC [extreal_add_def,mul_not_infty,positive_not_infty,measure_space_def,REAL_LE_ADD]
 >> (MP_TAC o Q.SPEC `(\i:num. (Normal (x i) + Normal (y i)) * measure m (a i))`
     o UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_IN_IF
 >> RW_TAC std_ss [add_rdistrib]
 >> (MP_TAC o Q.SPEC `(\i. Normal (x i) * measure m (a i) + Normal (y i) * measure m (a i))`
     o UNDISCH o Q.ISPEC `s:num->bool` o GSYM) EXTREAL_SUM_IMAGE_IN_IF
 >> `!i. i IN s ==> NegInf <> (\i. Normal (x i) * measure m (a i) + Normal (y i) * measure m (a i)) i`
        by METIS_TAC [extreal_add_def, mul_not_infty, positive_not_infty, measure_space_def,
                      REAL_LE_ADD, add_not_infty]
 >> RW_TAC std_ss []
 >> `(\i. Normal (x i) * measure m (a i) + Normal (y i) * measure m (a i)) =
     (\i. (\i. Normal (x i) * measure m (a i)) i + (\i. Normal (y i) * measure m (a i)) i)`
        by METIS_TAC []
 >> POP_ORW
 >> (MATCH_MP_TAC o UNDISCH o Q.ISPEC `s:num->bool` o GSYM) EXTREAL_SUM_IMAGE_ADD
 >> DISJ1_TAC
 >> METIS_TAC [mul_not_infty, positive_not_infty, measure_space_def, extreal_not_infty]);

val psfis_add = store_thm
  ("psfis_add",
  ``!m f g a b. measure_space m /\ a IN psfis m f /\ b IN psfis m g ==>
                a + b IN psfis m (\x. f x + g x)``,
    RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
 >> Cases_on `x'` >> Cases_on `x` >> Cases_on `x''` >> Cases_on `x'''`
 >> Cases_on `r'` >> Cases_on `r` >> Cases_on `r''` >> Cases_on `r'''`
 >> RW_TAC std_ss []
 >> FULL_SIMP_TAC std_ss [PAIR_EQ]
 >> Suff `?s a x. (pos_simple_fn_integral m q q''''' r' +
                   pos_simple_fn_integral m q''' q''''''' r'' =
                   pos_simple_fn_integral m s a x) /\ pos_simple_fn m (\x. f x + g x) s a x`
 >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `(s,a,x)` \\
     RW_TAC std_ss [] >> Q.EXISTS_TAC `(s,a,x)` \\
     RW_TAC std_ss [PAIR_EQ])
 >> ONCE_REWRITE_TAC [CONJ_COMM]
 >> MATCH_MP_TAC pos_simple_fn_integral_add >> RW_TAC std_ss []);

val pos_simple_fn_integral_mono = store_thm
  ("pos_simple_fn_integral_mono",
  ``!m f (s :num->bool) a x
       g (s':num->bool) b y.
       measure_space m /\ pos_simple_fn m f s a x /\ pos_simple_fn m g s' b y /\
      (!x. x IN m_space m ==> f x <= g x) ==>
       pos_simple_fn_integral m s a x <= pos_simple_fn_integral m s' b y``,
    rpt STRIP_TAC
 >> (MP_TAC o Q.SPECL [`m`,`f`,`s`,`a`,`x`,`g`,`s'`,`b`,`y`]) pos_simple_fn_integral_present
 >> RW_TAC std_ss [] >> ASM_SIMP_TAC std_ss []
 >> RW_TAC std_ss [pos_simple_fn_integral_def]
 >> (MATCH_MP_TAC o UNDISCH o Q.ISPEC `k:num->bool`) EXTREAL_SUM_IMAGE_MONO
 >> RW_TAC std_ss []
 >- (DISJ1_TAC \\
     RW_TAC std_ss [] \\
    `measure m (c x') <> NegInf` by METIS_TAC [measure_space_def, positive_not_infty] \\
     Cases_on `measure m (c x')` >> RW_TAC std_ss [extreal_mul_def, extreal_not_infty] \\
     METIS_TAC [real_lte, REAL_LE_ANTISYM])
 >> Cases_on `c x' = {}`
 >- RW_TAC real_ss [MEASURE_EMPTY,mul_rzero,le_refl]
 >> `pos_simple_fn m f k c z` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
 >> `pos_simple_fn m g k c z'` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
 >> `?t. t IN c x'` by METIS_TAC [CHOICE_DEF]
 >> `f t = Normal (z x')` by METIS_TAC [pos_simple_fn_thm1]
 >> `g t = Normal (z' x')` by METIS_TAC [pos_simple_fn_thm1]
 >> `Normal (z x') <= Normal (z' x')` by METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE, SUBSET_DEF]
 >> Cases_on `measure m (c x') = 0` >- RW_TAC std_ss [mul_rzero,le_refl]
 >> MATCH_MP_TAC le_rmul_imp
 >> RW_TAC std_ss []
 >> METIS_TAC [MEASURE_SPACE_POSITIVE, positive_def, lt_le]);

val psfis_mono = store_thm
  ("psfis_mono",
  ``!m f g a b. measure_space m /\ a IN psfis m f /\ b IN psfis m g /\
               (!x. x IN m_space m ==> f x <= g x) ==> a <= b``,
    RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
 >> Cases_on `x'` >> Cases_on `x` >> Cases_on `x''` >> Cases_on `x'''`
 >> Cases_on `r'` >> Cases_on `r` >> Cases_on `r''` >> Cases_on `r'''`
 >> RW_TAC std_ss []
 >> FULL_SIMP_TAC std_ss [PAIR_EQ]
 >> MATCH_MP_TAC pos_simple_fn_integral_mono
 >> METIS_TAC []);

val pos_simple_fn_integral_unique = store_thm
  ("pos_simple_fn_integral_unique",
  ``!m f (s:num->bool) a x (s':num->bool) b y.
         measure_space m /\ pos_simple_fn m f s a x /\ pos_simple_fn m f s' b y ==>
        (pos_simple_fn_integral m s a x = pos_simple_fn_integral m s' b y)``,
    METIS_TAC [le_antisym, le_refl, pos_simple_fn_integral_mono]);

val psfis_unique = store_thm
  ("psfis_unique",
  ``!m f a b. measure_space m /\ a IN psfis m f /\ b IN psfis m f ==> (a = b)``,
    METIS_TAC [le_antisym, le_refl, psfis_mono]);

val pos_simple_fn_integral_indicator = store_thm
  ("pos_simple_fn_integral_indicator",
  ``!m A. measure_space m /\ A IN measurable_sets m ==>
          ?s a x. pos_simple_fn m (indicator_fn A) s a x /\
                 (pos_simple_fn_integral m s a x = measure m A)``,
    RW_TAC std_ss []
 >> Q.EXISTS_TAC `{0;1}`
 >> Q.EXISTS_TAC `\i. if i = 0 then m_space m DIFF A else A`
 >> Q.EXISTS_TAC `\i. if i = 0 then 0 else 1`
 >> RW_TAC std_ss [pos_simple_fn_indicator_alt, pos_simple_fn_integral_def]
 >> (MP_TAC o Q.SPEC `0:num` o REWRITE_RULE [FINITE_SING]
     o Q.ISPECL [`(\i:num. Normal (if i = 0 then 0 else 1) *
                           measure m (if i = 0 then m_space m DIFF A else A))`,`{1:num}`])
         EXTREAL_SUM_IMAGE_PROPERTY
 >> `!x:num. x IN {0; 1} ==> (\i. Normal (if i = 0 then 0 else 1) *
             measure m (if i = 0 then m_space m DIFF A else A)) x <> NegInf`
      by (RW_TAC std_ss [GSYM extreal_of_num_def, mul_lzero, mul_lone] \\
          METIS_TAC [extreal_of_num_def, extreal_not_infty, positive_not_infty,
                     MEASURE_SPACE_POSITIVE])
 >> RW_TAC std_ss [GSYM extreal_of_num_def,mul_lzero,add_lzero]
 >> `{1:num} DELETE 0 = {1}`
        by RW_TAC real_ss [Once EXTENSION, IN_SING, IN_DELETE]
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_SING, GSYM extreal_of_num_def, mul_lone]);

val psfis_indicator = store_thm
  ("psfis_indicator",
  ``!m A. measure_space m /\ A IN measurable_sets m ==>
          measure m A IN psfis m (indicator_fn A)``,
    RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
 >> Suff `?s a x. pos_simple_fn m (indicator_fn A) s a x /\
                  (pos_simple_fn_integral m s a x = measure m A)`
 >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `(s,a,x)` \\
     RW_TAC std_ss [] >> Q.EXISTS_TAC `(s,a,x)` \\
     RW_TAC std_ss [PAIR_EQ])
 >> MATCH_MP_TAC pos_simple_fn_integral_indicator
 >> ASM_REWRITE_TAC []);

val pos_simple_fn_integral_cmul = store_thm
  ("pos_simple_fn_integral_cmul",
  ``!m f s a x z.
       measure_space m /\ pos_simple_fn m f s a x /\ 0 <= z ==>
      (pos_simple_fn m (\x. Normal z * f x) s a (\i. z * x i) /\
      (pos_simple_fn_integral m s a (\i. z * x i) =
       Normal z * pos_simple_fn_integral m s a x))``,
    RW_TAC std_ss [pos_simple_fn_integral_def, pos_simple_fn_def, REAL_LE_MUL,
                   GSYM extreal_mul_def]
 >| [ (* goal 1 *)
      METIS_TAC [le_mul, extreal_le_def, extreal_of_num_def],
      (* goal 2 *)
     `(\i. Normal z * Normal (x i) * indicator_fn (a i) x') =
      (\i. Normal z * (\i. Normal (x i) * indicator_fn (a i) x') i)`
         by METIS_TAC [mul_assoc] >> POP_ORW \\
     (MATCH_MP_TAC o UNDISCH o Q.ISPEC `s:num->bool` o GSYM) EXTREAL_SUM_IMAGE_CMUL \\
      DISJ1_TAC \\
      RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero] \\
      RW_TAC std_ss [extreal_of_num_def, extreal_not_infty],
      (* goal 3 *)
     `(\i. Normal z * Normal (x i) * measure m (a i)) =
      (\i. Normal z * (\i. Normal (x i) * measure m (a i)) i)` by METIS_TAC [mul_assoc] \\
      POP_ORW \\
     (MATCH_MP_TAC o UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_CMUL \\
      DISJ1_TAC \\
      RW_TAC std_ss [] \\
      METIS_TAC [mul_not_infty, positive_not_infty, MEASURE_SPACE_POSITIVE] ]);

val psfis_cmul = store_thm
  ("psfis_cmul",
  ``!m f a z. measure_space m /\ a IN psfis m f /\ 0 <= z ==>
              Normal z * a IN psfis m (\x. Normal z * f x)``,
    RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
 >> Cases_on `x'`
 >> Cases_on `r`
 >> FULL_SIMP_TAC std_ss [PAIR_EQ]
 >> Q.EXISTS_TAC `(q,q',(\i. z * r' i))`
 >> RW_TAC std_ss []
 >- METIS_TAC [pos_simple_fn_integral_cmul]
 >> Q.EXISTS_TAC `(q,q',(\i. z * r' i))`
 >> RW_TAC std_ss []
 >> METIS_TAC [pos_simple_fn_integral_cmul]);

val pos_simple_fn_integral_cmul_alt = store_thm
  ("pos_simple_fn_integral_cmul_alt",
  ``!m f s a x z. measure_space m /\ 0 <= z /\ pos_simple_fn m f s a x ==>
       ?s' a' x'. (pos_simple_fn m (\t. Normal z * f t) s' a' x') /\
                  (pos_simple_fn_integral m s' a' x' = Normal z * pos_simple_fn_integral m s a x)``,
    RW_TAC real_ss []
 >> Q.EXISTS_TAC `s`
 >> Q.EXISTS_TAC `a`
 >> Q.EXISTS_TAC `(\i. z * x i)`
 >> RW_TAC std_ss [pos_simple_fn_cmul_alt]
 >> FULL_SIMP_TAC real_ss [pos_simple_fn_integral_def, pos_simple_fn_def, mul_assoc,
                           GSYM extreal_mul_def]
 >> `(\i. Normal z * Normal (x i) * measure m (a i)) =
     (\j. Normal z * (\i. Normal (x i) * measure m (a i)) j)`
        by RW_TAC std_ss [FUN_EQ_THM,mul_assoc]
 >> POP_ORW
 >> (MATCH_MP_TAC o UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_CMUL
 >> DISJ1_TAC
 >> METIS_TAC [mul_not_infty, extreal_not_infty, positive_not_infty, MEASURE_SPACE_POSITIVE]);

val IN_psfis = store_thm
  ("IN_psfis",
  ``!m r f. r IN psfis m f ==>
            ?s a x. pos_simple_fn m f s a x /\ (r = pos_simple_fn_integral m s a x)``,
    RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
 >> Cases_on `x'`>> Cases_on `x` >> Cases_on `r` >> Cases_on `r'`
 >> RW_TAC std_ss []
 >> FULL_SIMP_TAC std_ss [PAIR_EQ]
 >> METIS_TAC []);

val IN_psfis_eq = store_thm
  ("IN_psfis_eq",
  ``!m r f. r IN psfis m f <=>
            ?s a x. pos_simple_fn m f s a x /\ (r = pos_simple_fn_integral m s a x)``,
    RW_TAC std_ss []
 >> EQ_TAC >- RW_TAC std_ss [IN_psfis]
 >> RW_TAC std_ss [psfis_def,psfs_def,IN_IMAGE,GSPECIFICATION]
 >> Q.EXISTS_TAC `(s,a,x)`
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC `(s,a,x)`
 >> RW_TAC std_ss []);

val psfis_pos = store_thm
  ("psfis_pos",
  ``!m f a. measure_space m /\ a IN psfis m f ==> (!x. x IN m_space m ==> 0 <= f x)``,
    RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
 >> Cases_on `x'`
 >> Cases_on `r`
 >> FULL_SIMP_TAC std_ss [PAIR_EQ, pos_simple_fn_def]
 >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS
 >> RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone, le_refl]
 >> RW_TAC std_ss [extreal_of_num_def, extreal_le_def]);

val pos_simple_fn_integral_zero = store_thm
  ("pos_simple_fn_integral_zero",
  ``!m s a x. measure_space m /\ pos_simple_fn m (\t. 0) s a x ==>
             (pos_simple_fn_integral m s a x = 0)``,
    RW_TAC std_ss []
 >> `pos_simple_fn m (\t. 0) {1:num} (\i:num. if i=1 then (m_space m) else {}) (\i:num. 0) /\
    (pos_simple_fn_integral m  {1:num} (\i:num. if i=1 then (m_space m) else {}) (\i:num. 0) = 0)`
      by RW_TAC real_ss [pos_simple_fn_integral_def, pos_simple_fn_def,
                         FINITE_SING, EXTREAL_SUM_IMAGE_SING, EXTREAL_SUM_IMAGE_SING,
                         IMAGE_SING, BIGUNION_SING, IN_SING, MEASURE_SPACE_MSPACE_MEASURABLE,
                         GSYM extreal_of_num_def, mul_lzero, le_refl]
 >> METIS_TAC [pos_simple_fn_integral_unique]);

val pos_simple_fn_integral_zero_alt = store_thm
  ("pos_simple_fn_integral_zero_alt",
  ``!m s a x. measure_space m /\ pos_simple_fn m g s a x /\ (!x. x IN m_space m ==> (g x = 0))
         ==> (pos_simple_fn_integral m s a x = 0)``,
    RW_TAC std_ss [pos_simple_fn_integral_def]
 >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
 >> CONJ_TAC >- FULL_SIMP_TAC std_ss [pos_simple_fn_def]
 >> RW_TAC std_ss []
 >> Cases_on `a x' = {}` >- FULL_SIMP_TAC std_ss [MEASURE_EMPTY,mul_rzero]
 >> Suff `Normal (x x') = 0` >- FULL_SIMP_TAC std_ss [mul_lzero]
 >> `?y. y IN a x'` by METIS_TAC [CHOICE_DEF]
 >> METIS_TAC [pos_simple_fn_thm1, MEASURE_SPACE_SUBSET_MSPACE, pos_simple_fn_def, SUBSET_DEF]);

val psfis_zero = store_thm
  ("psfis_zero", ``!m a. measure_space m ==> ((a IN psfis m (\x. 0)) <=> (a = 0))``,
    RW_TAC std_ss []
 >> EQ_TAC >- METIS_TAC [IN_psfis_eq, pos_simple_fn_integral_zero]
 >> RW_TAC std_ss [IN_psfis_eq]
 >> Q.EXISTS_TAC `{1}`
 >> Q.EXISTS_TAC `(\i. m_space m)`
 >> Q.EXISTS_TAC `(\i. 0)`
 >> RW_TAC real_ss [pos_simple_fn_integral_def, pos_simple_fn_def, FINITE_SING,
                    EXTREAL_SUM_IMAGE_SING, REAL_SUM_IMAGE_SING, IMAGE_SING, BIGUNION_SING,
                    IN_SING, MEASURE_SPACE_MSPACE_MEASURABLE, mul_lzero,
                    GSYM extreal_of_num_def, le_refl]);

val pos_simple_fn_integral_not_infty = store_thm
  ("pos_simple_fn_integral_not_infty",
  ``!m f s a x. measure_space m /\ pos_simple_fn m f s a x
            ==> pos_simple_fn_integral m s a x <> NegInf``,
    RW_TAC std_ss [pos_simple_fn_integral_def,pos_simple_fn_def]
 >> Suff `!i. i IN s ==> (\i. Normal (x i) * measure m (a i)) i <> NegInf`
 >- FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY]
 >> METIS_TAC [mul_not_infty, extreal_le_def, extreal_of_num_def, positive_not_infty,
               MEASURE_SPACE_POSITIVE]);

val psfis_not_infty = store_thm
  ("psfis_not_infty", ``!m f a. measure_space m  /\ a IN psfis m f ==> a <> NegInf``,
    METIS_TAC [IN_psfis_eq, pos_simple_fn_integral_not_infty]);

val pos_simple_fn_integral_sum = store_thm
  ("pos_simple_fn_integral_sum",
  ``!m f s a x P. measure_space m /\
        (!i. i IN P ==> pos_simple_fn m (f i) s a (x i)) /\
        (!i t. i IN P ==> f i t <> NegInf) /\ FINITE P /\ P <> {} ==>
        (pos_simple_fn m (\t. SIGMA (\i. f i t) P) s a (\i. SIGMA (\j. x j i) P) /\
        (pos_simple_fn_integral m s a (\j. SIGMA (\i. x i j) P) =
           SIGMA (\i. pos_simple_fn_integral m s a (x i)) P))``,
    Suff `!P:'b->bool. FINITE P ==>
            (\P:'b->bool. !m f s a x. measure_space m /\
            (!i. i IN P ==> pos_simple_fn m (f i) s a (x i)) /\
            (!i t. i IN P ==> f i t <> NegInf) /\ P <> {} ==>
            (pos_simple_fn m (\t. SIGMA (\i. f i t) P) s a (\i. SIGMA (\j. x j i) P) /\
            (pos_simple_fn_integral m s a (\j. SIGMA (\i. x i j) P) =
               SIGMA (\i. pos_simple_fn_integral m s a (x i)) P))) P`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> CONJ_TAC
 >- RW_TAC std_ss [NOT_IN_EMPTY,EXTREAL_SUM_IMAGE_EMPTY,REAL_SUM_IMAGE_THM]
 >> RW_TAC std_ss [REAL_SUM_IMAGE_THM,DELETE_NON_ELEMENT]
 >- (`(\t. SIGMA (\i. f i t) (e INSERT s)) = (\t. f e t + (\t. SIGMA (\i. f i t) s) t)`
          by (RW_TAC std_ss [FUN_EQ_THM]
             >> (MP_TAC o UNDISCH o Q.SPECL [`(\i. f i t)`,`s`] o INST_TYPE [alpha |-> beta])
                   EXTREAL_SUM_IMAGE_PROPERTY
             >> FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]) >> POP_ORW \\
     `(\i. x e i + SIGMA (\j. x j i) s) = (\i. x e i + (\i. SIGMA (\j. x j i) s) i)`
          by METIS_TAC [] >> POP_ORW \\
     MATCH_MP_TAC pos_simple_fn_add_alt \\
     RW_TAC std_ss [] >- METIS_TAC [IN_INSERT] \\
     Q.PAT_X_ASSUM `!m f s' a x. Q` (MP_TAC o Q.SPECL [`m`,`f`,`s'`,`a`,`x`]) \\
     RW_TAC std_ss [] \\
     Cases_on `s <> {}` >- METIS_TAC [IN_INSERT] \\
     FULL_SIMP_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY, REAL_SUM_IMAGE_THM, pos_simple_fn_def,
                            IN_SING, le_refl, GSYM extreal_of_num_def, mul_lzero,
                            EXTREAL_SUM_IMAGE_0])
 >> (MP_TAC o Q.SPEC `e` o UNDISCH o Q.SPEC `s`
     o Q.SPEC `(\i. pos_simple_fn_integral m s' a (x i))`
     o INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY
 >> `!x'. x' IN e INSERT s ==> (\i. pos_simple_fn_integral m s' a (x i)) x' <> NegInf`
        by (RW_TAC std_ss [] \\
            METIS_TAC [IN_INSERT, pos_simple_fn_integral_not_infty])
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM `!n f s a z. Q` (MP_TAC o Q.SPECL [`m`,`f`,`s'`,`a`,`x`])
 >> FULL_SIMP_TAC std_ss [IN_INSERT]
 >> RW_TAC std_ss []
 >> Cases_on `s = {}`
 >- (RW_TAC real_ss [EXTREAL_SUM_IMAGE_EMPTY, REAL_SUM_IMAGE_THM, add_rzero] \\
     METIS_TAC [])
 >> FULL_SIMP_TAC std_ss []
 >> `SIGMA (\i. pos_simple_fn_integral m s' a (x i)) s =
     pos_simple_fn_integral m s' a (\j. SIGMA (\i. x i j) s)`
       by METIS_TAC [] >> POP_ORW
 >> `(\j. x e j + SIGMA (\i. x i j) s) =
     (\j. x e j + (\j. SIGMA (\i. x i j) s) j)` by METIS_TAC [] >> POP_ORW
 >> (MATCH_MP_TAC o GSYM) pos_simple_fn_integral_add_alt
 >> METIS_TAC []);

val pos_simple_fn_integral_sum_alt = store_thm
  ("pos_simple_fn_integral_sum_alt",
  ``!m f s a x P. measure_space m /\
        (!i. i IN P ==> pos_simple_fn m (f i) (s i) (a i) (x i)) /\
        (!i t. i IN P ==> f i t <> NegInf) /\ FINITE P /\ P <> {} ==>
        ?c k z. (pos_simple_fn m (\t. SIGMA (\i. f i t) P) k c z /\
                (pos_simple_fn_integral m k c z =
                 SIGMA (\i. pos_simple_fn_integral m (s i) (a i) (x i)) P))``,

    Suff `!P:'b->bool. FINITE P ==>
             (\P:'b->bool. !m f s a x. measure_space m /\
                                      (!i. i IN P ==> pos_simple_fn m (f i) (s i) (a i) (x i)) /\
                                      (!i t. i IN P ==> f i t <> NegInf) /\ P <> {} ==>
               ?c k z. (pos_simple_fn m (\t. SIGMA (\i. f i t) P) k c z /\
                        (pos_simple_fn_integral m k c z =
                         SIGMA (\i. pos_simple_fn_integral m (s i) (a i) (x i)) P))) P`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss []
 >> Cases_on `s = {}` >- (RW_TAC std_ss [EXTREAL_SUM_IMAGE_SING] >> METIS_TAC [IN_SING])
 >> `?c k z. pos_simple_fn m (\t. SIGMA (\i. f i t) s) k c z /\
            (pos_simple_fn_integral m k c z =
               SIGMA (\i. pos_simple_fn_integral m (s' i) (a i) (x i)) s)`
        by METIS_TAC [IN_INSERT]
 >> `!i. i IN e INSERT s ==> (\i. pos_simple_fn_integral m (s' i) (a i) (x i)) i <> NegInf`
        by METIS_TAC [pos_simple_fn_integral_not_infty, IN_INSERT]
 >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY]
 >> (MP_TAC o Q.SPECL [`m`,`f (e:'b)`,`s' (e:'b)`,`a (e:'b)`,`x (e:'b)`,
                       `(\t. SIGMA (\i:'b. f i t) s)`,`k`,`c`,`z`]) pos_simple_fn_integral_present
 >> FULL_SIMP_TAC std_ss [IN_INSERT, DELETE_NON_ELEMENT]
 >> RW_TAC std_ss []
 >> METIS_TAC [pos_simple_fn_integral_add]);

val psfis_sum = store_thm
  ("psfis_sum",
  ``!m f a P. measure_space m /\ (!i. i IN P ==> a i IN psfis m (f i)) /\
             (!i t. i IN P ==> f i t <> NegInf) /\ FINITE P ==>
             (SIGMA a P) IN psfis m (\t. SIGMA (\i. f i t) P)``,
    Suff `!P:'b->bool. FINITE P ==>
             (\P:'b->bool. !m f a. measure_space m /\ (!i. i IN P ==> a i IN psfis m (f i)) /\
                                  (!i t. i IN P ==> f i t <> NegInf) ==>
                                  (SIGMA a P) IN psfis m (\t. SIGMA (\i. f i t) P)) P`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, psfis_zero, DELETE_NON_ELEMENT, IN_INSERT]
 >> `!x. x IN e INSERT s ==> a x <> NegInf` by METIS_TAC [IN_INSERT, psfis_not_infty]
 >> `!x t. x IN e INSERT s ==> (\x. f x t) x <> NegInf` by METIS_TAC [IN_INSERT]
 >> `!t. (\i. f i t) = (\i. (\i. f i t) i)` by METIS_TAC [] >> POP_ORW
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY]
 >> `(\t. f e t + SIGMA (\i. f i t) s) = (\t. f e t + (\t. SIGMA (\i. f i t) s) t)`
       by METIS_TAC [] >> POP_ORW
 >> MATCH_MP_TAC psfis_add
 >> RW_TAC std_ss []);

val psfis_intro = store_thm
  ("psfis_intro",
  ``!m a x P. measure_space m /\ (!i. i IN P ==> a i IN measurable_sets m) /\
             (!i. i IN P ==> 0 <= x i) /\ FINITE P ==>
             (SIGMA (\i. Normal (x i) * measure m (a i)) P) IN
              psfis m (\t. SIGMA (\i. Normal (x i) * indicator_fn (a i) t) P)``,
    RW_TAC std_ss []
 >> `!t. (\i. Normal (x i) * indicator_fn (a i) t) =
         (\i. (\i t. Normal (x i) * indicator_fn (a i) t) i t)` by METIS_TAC [] >> POP_ORW
 >> MATCH_MP_TAC psfis_sum
 >> RW_TAC std_ss [] >- METIS_TAC [psfis_cmul, psfis_indicator]
 >> RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero]
 >> METIS_TAC [extreal_of_num_def, extreal_not_infty]);

val pos_simple_fn_integral_sub = store_thm
  ("pos_simple_fn_integral_sub",
  ``!m f s a x g s' b y.
        measure_space m /\ (measure m (m_space m) <> PosInf) /\
        (!x. g x <= f x) /\ (!x. g x <> PosInf) /\
        pos_simple_fn m f s a x /\ pos_simple_fn m g s' b y ==>
        ?s'' c z. pos_simple_fn m (\x. f x - g x) s'' c z /\
                (pos_simple_fn_integral m s a x -
                 pos_simple_fn_integral m s' b y =
                 pos_simple_fn_integral m s'' c z)``,
    rpt STRIP_TAC
 >> (MP_TAC o Q.SPECL [`m`,`f`,`s`,`a`,`x`,`g`,`s'`,`b`,`y`]) pos_simple_fn_integral_present
 >> RW_TAC std_ss [] >> ASM_SIMP_TAC std_ss []
 >> Q.EXISTS_TAC `k`
 >> Q.EXISTS_TAC `c`
 >> Q.EXISTS_TAC `(\i. if (i IN k /\ ~(c i = {})) then (z i - z' i) else 0)`
 >> FULL_SIMP_TAC std_ss [pos_simple_fn_def, pos_simple_fn_integral_def]
 >> `pos_simple_fn m f k c z` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
 >> `pos_simple_fn m g k c z'` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
 >> `!x. k x <=> x IN k` by METIS_TAC [SPECIFICATION]
 >> `!x. x IN k ==> Normal (z x - z' x) * measure m (c x) <> NegInf`
         by (RW_TAC std_ss []
             >> Cases_on `c x' = {}`
             >- METIS_TAC [MEASURE_EMPTY, mul_rzero, extreal_of_num_def, extreal_not_infty]
             >> `?y. y IN c x'` by METIS_TAC [CHOICE_DEF]
             >> `f y' = Normal (z x')` by METIS_TAC [pos_simple_fn_def, pos_simple_fn_thm1]
             >> `g y' = Normal (z' x')` by METIS_TAC [pos_simple_fn_def, pos_simple_fn_thm1]
             >> `0 <= z x' - z' x'` by METIS_TAC [extreal_le_def, REAL_SUB_LE, extreal_of_num_def]
             >> METIS_TAC [mul_not_infty,positive_not_infty, MEASURE_SPACE_POSITIVE])
 >> Reverse CONJ_TAC
 >- (`!i. (Normal (if (i IN k /\ ~(c i = {})) then z i - z' i else 0) * measure m (c i)) =
          (Normal (if i IN k then z i - z' i else 0) * measure m (c i))`
         by (RW_TAC std_ss [] >> FULL_SIMP_TAC real_ss [MEASURE_EMPTY, mul_rzero]) \\
     POP_ORW \\
    `SIGMA (\i. Normal (if i IN k then z i - z' i else 0) * measure m (c i)) k =
     SIGMA (\i. Normal (z i - z' i) * measure m (c i)) k`
         by ((MP_TAC o REWRITE_RULE [SPECIFICATION]
              o Q.SPECL [`k`,`k`,`(\i. Normal (z i - z' i) * measure m (c i))`]
              o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_IF_ELIM \\
             RW_TAC real_ss [] \\
            `(\x. if x IN k then Normal (z x - z' x) * measure m (c x) else 0) =
             (\i. Normal (if i IN k then z i - z' i else 0) * measure m (c i))`
                by (RW_TAC real_ss [FUN_EQ_THM] \\
                    Cases_on `i IN k` >- METIS_TAC [] \\
                    RW_TAC real_ss [mul_lzero, GSYM extreal_of_num_def]) \\
             FULL_SIMP_TAC real_ss []) >> POP_ORW \\
     RW_TAC std_ss [GSYM extreal_sub_def] \\
    `!i. i IN k ==> measure m (c i) <= measure m (m_space m)`
         by METIS_TAC [INCREASING, MEASURE_SPACE_INCREASING, MEASURE_SPACE_MSPACE_MEASURABLE,
                       MEASURE_SPACE_SUBSET_MSPACE] \\
    `!i. i IN k ==> measure m (c i) <> PosInf` by METIS_TAC [le_infty] \\
     (MP_TAC o Q.SPEC `(\i. (Normal (z i) - Normal (z' i)) * measure m (c i))` o UNDISCH
      o Q.ISPEC `k:num->bool`) EXTREAL_SUM_IMAGE_IN_IF \\
    `!x. x IN k ==> (\i. (Normal (z i) - Normal (z' i)) * measure m (c i)) x <> NegInf`
         by RW_TAC std_ss [extreal_sub_def] \\
     RW_TAC std_ss [] \\
    `!x. x IN k ==> ((Normal (z x) - Normal (z' x)) * measure m (c x) =
                     Normal (z x) * measure m (c x) - Normal (z' x) *  measure m (c x))`
         by (RW_TAC std_ss [] \\
            `measure m (c x') <> NegInf` by METIS_TAC [positive_not_infty, MEASURE_SPACE_POSITIVE] \\
            `?r. measure m (c x') = Normal r` by METIS_TAC [extreal_cases] \\
             RW_TAC std_ss [extreal_sub_def, extreal_mul_def, REAL_SUB_RDISTRIB]) \\
     (MP_TAC o Q.SPECL [`k:num->bool`,`k`,
                        `(\x:num. Normal (z x) * measure m (c x) - Normal (z' x) * measure m (c x))`]
      o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_IF_ELIM \\
     RW_TAC std_ss [] \\
     FULL_SIMP_TAC std_ss [] \\
    `(\x. Normal (z x) * measure m (c x) - Normal (z' x) * measure m (c x)) =
     (\x. (\x. Normal (z x) * measure m (c x)) x - (\x. Normal (z' x) * measure m (c x)) x)`
          by METIS_TAC [] >> POP_ORW \\
     (MATCH_MP_TAC o UNDISCH o Q.SPEC `k` o GSYM o INST_TYPE [alpha |-> ``:num``])
        EXTREAL_SUM_IMAGE_SUB \\
     DISJ1_TAC >> RW_TAC std_ss []
     >- METIS_TAC [mul_not_infty, positive_not_infty, MEASURE_SPACE_POSITIVE] \\
     METIS_TAC [mul_not_infty])
 >> `!x. g x <> NegInf` by METIS_TAC [lt_infty,lte_trans,extreal_not_infty,extreal_of_num_def]
 >> CONJ_TAC
 >- METIS_TAC [le_sub_imp,add_lzero]
 >> Reverse (RW_TAC real_ss [])
 >- (`?q. q IN c i` by METIS_TAC [CHOICE_DEF]
      >> METIS_TAC [pos_simple_fn_thm1,REAL_SUB_LE,extreal_le_def])
 >> `!i. (Normal (if (i IN k /\ ~(c i = {})) then z i - z' i else 0) * indicator_fn (c i) x') =
         (Normal (if i IN k then z i - z' i else 0) * indicator_fn (c i) x')`
        by (RW_TAC std_ss [] \\
            FULL_SIMP_TAC real_ss [indicator_fn_def, mul_rzero, mul_rone, NOT_IN_EMPTY])
 >> POP_ORW
 >> `SIGMA (\i. Normal (if i IN k then z i - z' i else 0) * indicator_fn (c i) x') k =
     SIGMA (\i. Normal (z i - z' i) * indicator_fn (c i) x') k`
        by ((MP_TAC o REWRITE_RULE [SPECIFICATION] o
             (Q.SPECL [`k`,`k`,`(\i. Normal (z i - z' i) * indicator_fn (c i) x')`]) o
             (INST_TYPE [alpha |-> ``:num``])) EXTREAL_SUM_IMAGE_IF_ELIM \\
            RW_TAC real_ss [] \\
           `!x. (\i. Normal (z i - z' i) * indicator_fn (c i) x') x <> NegInf`
                by (RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone] \\
                    RW_TAC std_ss [extreal_of_num_def, extreal_not_infty]) \\
            RW_TAC std_ss [] \\
           `(\x. if x IN k then Normal (z x - z' x) * indicator_fn (c x) x' else 0) =
                 (\i. Normal (if i IN k then z i - z' i else 0) * indicator_fn (c i) x')`
                   by (RW_TAC real_ss [FUN_EQ_THM, indicator_fn_def, mul_rzero, mul_rone] \\
                       Cases_on `i IN k` >- METIS_TAC [] \\
                       RW_TAC real_ss [mul_lzero, GSYM extreal_of_num_def]) \\
            FULL_SIMP_TAC real_ss []) >> POP_ORW
 >> RW_TAC std_ss [GSYM extreal_sub_def]
 >> (MP_TAC o Q.SPEC `(\i. (Normal (z i) - Normal (z' i)) * indicator_fn (c i) x')`
     o UNDISCH o Q.ISPEC `k:num->bool`) EXTREAL_SUM_IMAGE_IN_IF
 >> `!x. x IN k ==> (\i. (Normal (z i) - Normal (z' i)) * indicator_fn (c i) x') x <> NegInf`
        by (RW_TAC std_ss [extreal_sub_def, indicator_fn_def, mul_rzero, mul_rone] \\
            RW_TAC std_ss [extreal_of_num_def, extreal_not_infty])
 >> RW_TAC std_ss []
 >> `!x. x IN k ==> ((Normal (z x) - Normal (z' x)) * indicator_fn (c x) x' =
                     Normal (z x) * indicator_fn (c x) x' - Normal (z' x) * indicator_fn (c x) x')`
        by (RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, sub_rzero])
 >> RW_TAC std_ss []
 >> NTAC 3 (POP_ASSUM (K ALL_TAC))
 >> (MP_TAC o
     (Q.SPEC `(\x:num. Normal (z x) * indicator_fn (c x) x' - Normal (z' x) * indicator_fn (c x) x')`) o
     UNDISCH o (Q.SPEC `k`) o GSYM o (INST_TYPE [alpha |-> ``:num``])) EXTREAL_SUM_IMAGE_IN_IF
 >> `!x. NegInf <> (\x. Normal (z x) * indicator_fn (c x) x' - Normal (z' x) * indicator_fn (c x) x') x`
        by (RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, sub_rzero, extreal_sub_def] \\
            RW_TAC std_ss [extreal_of_num_def, extreal_not_infty])
 >> RW_TAC std_ss []
 >> FULL_SIMP_TAC std_ss []
 >> `SIGMA (\i. Normal (x i) * indicator_fn (a i) x') s =
     SIGMA (\i. Normal (z i) * indicator_fn (c i) x') k` by METIS_TAC []
 >> `SIGMA (\i. Normal (y i) * indicator_fn (b i) x') s' =
     SIGMA (\i. Normal (z' i) * indicator_fn (c i) x') k` by METIS_TAC []
 >> POP_ORW
 >> POP_ORW
 >> `(\x. Normal (z x) * indicator_fn (c x) x' - Normal (z' x) * indicator_fn (c x) x') =
     (\x. (\x. Normal (z x) * indicator_fn (c x) x') x - (\x. Normal (z' x) * indicator_fn (c x) x') x)`
          by METIS_TAC [] >> POP_ORW
 >> (MATCH_MP_TAC o UNDISCH o Q.SPEC `k` o GSYM o INST_TYPE [alpha |-> ``:num``])
       EXTREAL_SUM_IMAGE_SUB
 >> DISJ1_TAC
 >> RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone]
 >> RW_TAC std_ss [extreal_of_num_def, extreal_not_infty]);

val psfis_sub = store_thm
  ("psfis_sub",
  ``!m f g a b. measure_space m /\ measure m (m_space m) <> PosInf /\
               (!x. g x <= f x) /\ (!x. g x <> PosInf) /\
                a IN psfis m f /\ b IN psfis m g ==> (a - b) IN psfis m (\x. f x - g x)``,
    RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
 >> Cases_on `x'` >> Cases_on `x` >> Cases_on `x''` >> Cases_on `x'''`
 >> RW_TAC std_ss []
 >> Cases_on `r'` >> Cases_on `r` >> Cases_on `r''` >> Cases_on `r'''`
 >> RW_TAC std_ss []
 >> FULL_SIMP_TAC std_ss [PAIR_EQ]
 >> Suff `?s a x. (pos_simple_fn_integral m q q''''' r' -
                   pos_simple_fn_integral m q''' q''''''' r'' =
                   pos_simple_fn_integral m s a x) /\
                  pos_simple_fn m (\x. f x - g x) s a x`
 >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `(s,a,x)` \\
     RW_TAC std_ss [] >> Q.EXISTS_TAC `(s,a,x)` >> RW_TAC std_ss [PAIR_EQ])
 >> ONCE_REWRITE_TAC [CONJ_COMM]
 >> MATCH_MP_TAC pos_simple_fn_integral_sub >> RW_TAC std_ss []);

(* ---------------------------------------------------- *)
(* Properties of Integrals of Positive Functions        *)
(* ---------------------------------------------------- *)

val pos_fn_integral_pos_simple_fn = store_thm
  ("pos_fn_integral_pos_simple_fn",
  ``!m f s a x. measure_space m /\ pos_simple_fn m f s a x
           ==> (pos_fn_integral m f = pos_simple_fn_integral m s a x)``,
  RW_TAC std_ss [pos_fn_integral_def,sup_eq,IN_psfis_eq]
  >- (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      >> RW_TAC std_ss [GSPECIFICATION]
      >> METIS_TAC [pos_simple_fn_integral_mono])
  >> POP_ASSUM MATCH_MP_TAC
  >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  >> RW_TAC std_ss [GSPECIFICATION]
  >> METIS_TAC [le_refl]);

(* what if only `!x. x IN m_space m ==> 0 <= f x` ? *)
val pos_fn_integral_mspace = store_thm
  ("pos_fn_integral_mspace",
  ``!m f. measure_space m /\ (!x. 0 <= f x) ==>
         (pos_fn_integral m f = pos_fn_integral m (\x. f x * indicator_fn (m_space m) x))``,
  RW_TAC std_ss [pos_fn_integral_def,sup_eq]
  >- (RW_TAC real_ss [le_sup]
      >> POP_ASSUM MATCH_MP_TAC
      >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      >> POP_ASSUM (MP_TAC o REWRITE_RULE [Once (GSYM SPECIFICATION)])
      >> RW_TAC real_ss [GSPECIFICATION,indicator_fn_def]
      >> Q.EXISTS_TAC `(\x. g x * indicator_fn (m_space m) x)`
      >> Reverse (RW_TAC real_ss [indicator_fn_def,IN_psfis_eq,mul_rone,mul_rzero,le_refl])
      >> FULL_SIMP_TAC std_ss [IN_psfis_eq,pos_simple_fn_def]
      >> Q.EXISTS_TAC `s`
      >> Q.EXISTS_TAC `a`
      >> Q.EXISTS_TAC `x`
      >> RW_TAC real_ss [mul_rzero,le_refl,mul_rone]
      >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS
      >> RW_TAC std_ss [mul_rzero,le_refl,mul_rone,indicator_fn_def]
      >> METIS_TAC [extreal_of_num_def,extreal_le_def])
  >> RW_TAC real_ss [sup_le]
  >> POP_ASSUM (MP_TAC o REWRITE_RULE [Once (GSYM SPECIFICATION)])
  >> RW_TAC real_ss [GSPECIFICATION]
  >> Q.PAT_X_ASSUM `!z. Q z ==> z <= y` MATCH_MP_TAC
  >> RW_TAC std_ss [Once (GSYM SPECIFICATION),GSPECIFICATION]
  >> Q.EXISTS_TAC `(\x. g x * indicator_fn (m_space m) x)`
  >> RW_TAC std_ss [IN_psfis_eq]
  >- (FULL_SIMP_TAC real_ss [IN_psfis_eq,pos_simple_fn_def,indicator_fn_def]
      >> Q.EXISTS_TAC `s`
      >> Q.EXISTS_TAC `a`
      >> Q.EXISTS_TAC `x`
      >> RW_TAC real_ss [le_refl,mul_rzero,mul_rone]
      >>MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS
      >> RW_TAC std_ss [mul_rzero,le_refl,mul_rone,indicator_fn_def]
      >> METIS_TAC [extreal_of_num_def,extreal_le_def])
  >> FULL_SIMP_TAC std_ss [indicator_fn_def,le_refl,mul_rzero,mul_rone]
  >> METIS_TAC [mul_rone,mul_rzero]);

val pos_fn_integral_zero = store_thm
  ("pos_fn_integral_zero",
  ``!m. measure_space m ==> (pos_fn_integral m (\x. 0) = 0)``,
  RW_TAC std_ss [pos_fn_integral_def,sup_eq]
  >- (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      >> RW_TAC std_ss [GSPECIFICATION]
      >> MATCH_MP_TAC psfis_mono
      >> Q.EXISTS_TAC `m` >> Q.EXISTS_TAC `g` >> Q.EXISTS_TAC `(\x. 0)`
      >> RW_TAC std_ss [psfis_zero])
  >> POP_ASSUM MATCH_MP_TAC
  >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  >> RW_TAC std_ss [GSPECIFICATION]
  >> Q.EXISTS_TAC `(\x. 0)`
  >> RW_TAC std_ss [le_refl,psfis_zero]);

val pos_fn_integral_mono = store_thm
  ("pos_fn_integral_mono",
  ``!m f g. (!x. 0 <= f x /\ f x <= g x) ==>
            pos_fn_integral m f <= pos_fn_integral m g``,
  RW_TAC std_ss [pos_fn_integral_def]
  >> MATCH_MP_TAC sup_le_sup_imp
  >> RW_TAC std_ss []
  >> Q.EXISTS_TAC `x`
  >> RW_TAC std_ss [le_refl]
  >> `x IN {r | ?g. r IN psfis m g /\ !x. g x <= f x}` by METIS_TAC [IN_DEF]
  >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  >> `?g. x IN psfis m g /\ !x. g x <= f x`
     by (FULL_SIMP_TAC std_ss [GSPECIFICATION] >> METIS_TAC [])
  >> FULL_SIMP_TAC std_ss [GSPECIFICATION]
  >> METIS_TAC [le_trans]);

val pos_fn_integral_mono_mspace = store_thm
  ("pos_fn_integral_mono_mspace",
  ``!m f g. measure_space m /\ (!x. x IN m_space m ==> g x <= f x) /\
            (!x. 0 <= f x) /\ (!x. 0 <= g x) ==>
            (pos_fn_integral m g <= pos_fn_integral m f)``,
  RW_TAC std_ss [Once pos_fn_integral_mspace]
  >> `pos_fn_integral m f = pos_fn_integral m (\x. f x * indicator_fn (m_space m) x)`
      by RW_TAC std_ss [Once pos_fn_integral_mspace]
  >> POP_ORW
  >> MATCH_MP_TAC pos_fn_integral_mono
  >> RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,le_refl]);

val pos_fn_integral_pos = store_thm
  ("pos_fn_integral_pos",
  ``!m f. measure_space m /\ (!x. 0 <= f x) ==> 0 <= pos_fn_integral m f``,
  RW_TAC std_ss []
  >> `0 = pos_fn_integral m (\x. 0)` by METIS_TAC [pos_fn_integral_zero]
  >> POP_ORW
  >> MATCH_MP_TAC pos_fn_integral_mono
  >> RW_TAC std_ss [le_refl]);

val pos_fn_integral_cmul = store_thm
  ("pos_fn_integral_cmul",
  ``!m f c. measure_space m /\ (!x. x IN m_space m ==> 0 <= f x) /\ 0 <= c ==>
           (pos_fn_integral m (\x. Normal c * f x) =  Normal c * pos_fn_integral m f)``,
  RW_TAC std_ss []
  >> Cases_on `c = 0`
  >- RW_TAC std_ss [GSYM extreal_of_num_def,mul_lzero,pos_fn_integral_zero]
  >> `0 < c` by FULL_SIMP_TAC std_ss [REAL_LT_LE]
  >> RW_TAC std_ss [pos_fn_integral_def,sup_eq]
  >- (Suff `y / (Normal c) <= sup {r | ?g. r IN psfis m g /\ !x. g x <= f x}`
      >- METIS_TAC [le_ldiv,mul_comm]
      >> RW_TAC std_ss [le_sup]
      >> POP_ASSUM MATCH_MP_TAC
      >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      >> RW_TAC std_ss [GSPECIFICATION]
      >> Q.EXISTS_TAC `(\x. g x / (Normal c))`
      >> Reverse (RW_TAC std_ss [])
      >- METIS_TAC [mul_comm,le_ldiv]
      >> RW_TAC std_ss [extreal_div_def]
      >> `inv (Normal c) * y IN psfis m (\x. inv (Normal c) * g x)`
         by METIS_TAC [psfis_cmul,extreal_inv_def,REAL_LE_INV]
      >> `(\x. g x * inv (Normal c)) = (\x. inv (Normal c) * g x)`
         by RW_TAC std_ss [FUN_EQ_THM, mul_comm]
      >> RW_TAC std_ss [Once mul_comm])
  >> Suff `sup {r | ?g. r IN psfis m g /\ !x. g x <= f x} <= y / Normal c`
  >- METIS_TAC [le_rdiv,extreal_not_infty,mul_comm]
  >> RW_TAC std_ss [sup_le]
  >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
  >> RW_TAC std_ss [GSPECIFICATION]
  >> Suff `y' * Normal c <= y` >- METIS_TAC [le_rdiv,extreal_not_infty]
  >> Q.PAT_X_ASSUM `!z. {r | ?g. r IN psfis m g /\ !x. g x <= Normal c * f x} z ==> (z <= y)` MATCH_MP_TAC
  >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  >> RW_TAC std_ss [GSPECIFICATION]
  >> Q.EXISTS_TAC `(\x. Normal c * g x)`
  >> RW_TAC std_ss []
  >- METIS_TAC [psfis_cmul,mul_comm,extreal_not_infty]
  >> METIS_TAC [le_lmul_imp,extreal_of_num_def,extreal_lt_eq,lt_le]);

val pos_fn_integral_indicator = store_thm
  ("pos_fn_integral_indicator",
   ``!m s. measure_space m /\ s IN measurable_sets m ==>
           (pos_fn_integral m (indicator_fn s) = measure m s)``,
  METIS_TAC [pos_fn_integral_pos_simple_fn,pos_simple_fn_integral_indicator]);

val pos_fn_integral_cmul_indicator = store_thm
  ("pos_fn_integral_cmul_indicator",
  ``!m s c. measure_space m /\ s IN measurable_sets m /\ 0 <= c ==>
           (pos_fn_integral m (\x. Normal c * indicator_fn s x) = Normal c * measure m s)``,
  RW_TAC std_ss []
  >> `!x. 0 <= indicator_fn s x` by RW_TAC std_ss [indicator_fn_def,le_refl,le_01]
  >> RW_TAC std_ss [pos_fn_integral_cmul]
  >> METIS_TAC [pos_fn_integral_pos_simple_fn,pos_simple_fn_integral_indicator]);

val pos_fn_integral_sum_cmul_indicator = store_thm
  ("pos_fn_integral_sum_cmul_indicator",
  ``!m s a x. measure_space m /\ FINITE s /\ (!i:num. i IN s ==> 0 <= x i) /\
             (!i:num. i IN s ==> a i IN measurable_sets m) ==>
           (pos_fn_integral m (\t. SIGMA (\i:num. Normal (x i) * indicator_fn (a i) t) s) =
            SIGMA (\i. Normal (x i) * measure m (a i)) s)``,
  RW_TAC std_ss []
  >> Cases_on `s = {}` >- RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY,pos_fn_integral_zero]
  >> `!i. i IN s ==> pos_simple_fn m (indicator_fn (a i)) {0:num; 1} (\n. if n = 0 then m_space m DIFF (a i) else (a i)) (\n:num. if n = 0 then 0 else 1)` by METIS_TAC [pos_simple_fn_indicator_alt]
  >> `!i. i IN s ==> pos_simple_fn m (\t. Normal (x i) * indicator_fn (a i) t) {0:num; 1} (\n:num. if n = 0 then m_space m DIFF (a i) else (a i)) (\n:num. (x i) * (if n = 0 then 0 else 1))` by METIS_TAC [pos_simple_fn_cmul_alt]
  >> (MP_TAC o Q.SPECL [`m`,`(\i. (\t. Normal (x i) * indicator_fn (a i) t))`,`(\i. {0; 1})`,`(\i. (\n. if n = 0 then m_space m DIFF a i else a i))`,`(\i. (\n. x i * if n = 0 then 0 else 1))`,`s`] o INST_TYPE [beta |-> ``:num``]) pos_simple_fn_integral_sum_alt
  >> `!i t. i IN s ==> Normal (x i) * indicator_fn (a i) t <> NegInf`
       by RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,num_not_infty]
  >> RW_TAC std_ss []
  >> `{1:num} DELETE 0 = {1}` by METIS_TAC [DELETE_NON_ELEMENT,EVAL ``0=1:num``,EXTENSION,IN_DELETE,IN_SING,NOT_IN_EMPTY]
  >> `FINITE {1:num}` by RW_TAC std_ss [FINITE_SING]
  >> `!i:num. i IN s ==> (pos_simple_fn_integral m {0:num; 1} (\n:num. if n = 0 then m_space m DIFF a i else a i) (\n:num. x i * if n = 0 then 0 else 1) = Normal (x i) * measure m (a i))`
       by (RW_TAC real_ss [pos_simple_fn_integral_def]
           >> `!n:num. n IN {0;1} ==> (\n. Normal (x i * if n = 0 then 0 else 1) *
                         measure m (if n = 0 then m_space m DIFF a i else a i)) n <> NegInf`
                  by (RW_TAC real_ss [GSYM extreal_of_num_def,num_not_infty,mul_lzero]
                      >> METIS_TAC [mul_not_infty,positive_not_infty,MEASURE_SPACE_POSITIVE,IN_INSERT])
           >> (MP_TAC o Q.SPEC `0` o UNDISCH o Q.SPECL [`(\n. Normal (x (i:num) * if n = 0 then 0 else 1) * measure m (if n = 0 then m_space m DIFF a i else a i))`,`{1}`] o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_PROPERTY
           >> RW_TAC real_ss [mul_lzero,add_lzero,EXTREAL_SUM_IMAGE_SING,GSYM extreal_of_num_def])

  >> (MP_TAC o Q.SPEC `(\i:num. pos_simple_fn_integral m {0:num; 1} (\n:num. if n = 0 then m_space m DIFF a i else a i) (\n:num. x i * if n = 0 then 0 else 1:real))` o UNDISCH o Q.SPEC `s` o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_IN_IF
  >> `!x'. x' IN s ==> (\i. pos_simple_fn_integral m {0; 1}
             (\n. if n = 0 then m_space m DIFF a i else a i)
             (\n. x i * if n = 0 then 0 else 1)) x' <> NegInf`
         by (RW_TAC std_ss []
             >> METIS_TAC [mul_not_infty,positive_not_infty,MEASURE_SPACE_POSITIVE,IN_INSERT])
  >> RW_TAC std_ss []
  >> FULL_SIMP_TAC std_ss []
  >> (MP_TAC o Q.SPECL [`s:num->bool`,`s`,`(\i:num. Normal (x i) * measure m (a i))`] o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_IF_ELIM
  >> `!x'. x' IN s ==> Normal (x x') * measure m (a x') <> NegInf` by METIS_TAC [mul_not_infty,positive_not_infty,MEASURE_SPACE_POSITIVE,IN_INSERT]
  >> RW_TAC std_ss []
  >> FULL_SIMP_TAC std_ss [SPECIFICATION]
  >> NTAC 7 (POP_ASSUM (K ALL_TAC))
  >> POP_ASSUM (MP_TAC o GSYM)
  >> RW_TAC std_ss []
  >> RW_TAC std_ss [pos_fn_integral_def,sup_eq]
  >- (POP_ASSUM  (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      >> RW_TAC std_ss [GSPECIFICATION,IN_psfis_eq]
      >> MATCH_MP_TAC pos_simple_fn_integral_mono
      >> Q.EXISTS_TAC `g`
      >> Q.EXISTS_TAC `(\t. SIGMA (\i. Normal (x i) * indicator_fn (a i) t) s)`
      >> RW_TAC std_ss [])
  >> POP_ASSUM MATCH_MP_TAC
  >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  >> RW_TAC std_ss [GSPECIFICATION,IN_psfis_eq]
  >> Q.EXISTS_TAC `(\t. SIGMA (\i. Normal (x i) * indicator_fn (a i) t) s)`
  >> RW_TAC real_ss []
  >> METIS_TAC [le_refl]);


(***************************************************************************)
(*                       Sequences - Convergence                           *)
(***************************************************************************)

(* also named "pos_mono_conv_mono_borel" by HVG *)
val lebesgue_monotone_convergence_lemma = store_thm
  ("lebesgue_monotone_convergence_lemma",
  ``!m f fi g r'.
        measure_space m /\
        (!i. fi i IN measurable (m_space m, measurable_sets m) Borel) /\
        (!x. mono_increasing (\i. fi i x)) /\
        (!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = f x)) /\
        (r' IN psfis m g) /\ (!x. g x <= f x) /\ (!i x. 0 <= fi i x) ==>
         r' <= sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV)``,
  rpt STRIP_TAC
  >> Q.ABBREV_TAC `r = sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV)`
  >> Q.ABBREV_TAC `ri = (\i. pos_fn_integral m (fi i))`
  >> MATCH_MP_TAC le_mul_epsilon
  >> RW_TAC std_ss []
  >> (Cases_on `z` >> FULL_SIMP_TAC std_ss [le_infty,lt_infty,extreal_not_infty,extreal_of_num_def])
  >> FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq]
  >> Q.ABBREV_TAC `b = \n. {t | Normal r'' * g t <= (fi n) t}`
  >> `?s a x. pos_simple_fn m g s a x` by METIS_TAC [IN_psfis]
  >> `!i j. i <= j ==> ri i <= ri j`
      by (Q.UNABBREV_TAC `ri`
          >> RW_TAC std_ss []
          >> MATCH_MP_TAC pos_fn_integral_mono
          >> FULL_SIMP_TAC std_ss [ext_mono_increasing_def, GSYM extreal_of_num_def])
  >> `f IN measurable (m_space m, measurable_sets m) Borel`
      by (MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP
          >> Q.EXISTS_TAC `fi`
          >> RW_TAC std_ss [space_def]
          >- FULL_SIMP_TAC std_ss [measure_space_def]
          >> FULL_SIMP_TAC std_ss [ext_mono_increasing_def,ext_mono_increasing_suc])
  >> `g IN measurable (m_space m, measurable_sets m) Borel` by METIS_TAC [IN_psfis_eq,IN_MEASURABLE_BOREL_POS_SIMPLE_FN]
  >> `(\t. Normal r'' * g t) IN measurable (m_space m, measurable_sets m) Borel`
        by ( MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
             >> Q.EXISTS_TAC `g` >> Q.EXISTS_TAC `r''`
             >> RW_TAC real_ss [extreal_not_infty]
             >> METIS_TAC [measure_space_def])
  >> `!n:num. {t | Normal r'' * g t <= fi n t} INTER m_space m = {t | 0 <= (fi n t) - Normal r'' * (g t)} INTER m_space m`
        by (RW_TAC real_ss [EXTENSION,GSPECIFICATION,IN_INTER]
            >> METIS_TAC [pos_simple_fn_not_infty,mul_not_infty,add_lzero,le_sub_eq,num_not_infty])
  >> `!n. (\t. fi n t - Normal r'' * g t) IN measurable (m_space m, measurable_sets m) Borel`
        by ( RW_TAC std_ss []
                   >> MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB
             >> Q.EXISTS_TAC `fi n`
             >> Q.EXISTS_TAC `(\t. Normal r'' * g t)`
             >> RW_TAC std_ss [space_def]
             >| [FULL_SIMP_TAC std_ss [measure_space_def],
                 METIS_TAC [lt_infty,lte_trans,extreal_not_infty,extreal_of_num_def],
                 METIS_TAC [pos_simple_fn_not_infty,mul_not_infty]])
  >> `!n. {t | Normal r'' * g t <= fi n t} INTER m_space m IN measurable_sets m`
        by METIS_TAC [IN_MEASURABLE_BOREL_ALL,m_space_def,space_def,
                        subsets_def,measurable_sets_def,measure_space_def,extreal_of_num_def]
  >> `!n. b n INTER m_space m IN measurable_sets m` by ( Q.UNABBREV_TAC `b` >> METIS_TAC [])
  >> Suff `r' = sup (IMAGE (\n. pos_fn_integral m (\x. g x * indicator_fn (b n INTER m_space m) x))
                           UNIV)`
  >- (Q.UNABBREV_TAC `r`
      >> RW_TAC std_ss [le_sup]
      >> Cases_on `r'' = 0`
      >- (RW_TAC std_ss [mul_lzero,GSYM extreal_of_num_def]
          >> MATCH_MP_TAC le_trans
          >> Q.EXISTS_TAC `ri (1:num)`
          >> Reverse (RW_TAC std_ss [])
          >- (POP_ASSUM MATCH_MP_TAC
              >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
              >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
              >> METIS_TAC [])
          >> Q.UNABBREV_TAC `ri`
          >> RW_TAC std_ss []
          >> METIS_TAC [pos_fn_integral_pos,extreal_of_num_def])
      >> `0 < r''` by METIS_TAC [REAL_LT_LE]
      >> `0 < Normal r''` by METIS_TAC [extreal_lt_eq,extreal_of_num_def,REAL_LE_REFL]
      >> ONCE_REWRITE_TAC [mul_comm]
      >> RW_TAC std_ss [le_rdiv]
      >> RW_TAC std_ss [sup_le]
      >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      >> RW_TAC std_ss [GSYM le_rdiv]
      >> ONCE_REWRITE_TAC [mul_comm]
      >> `!x. 0 <= (\x. g x * indicator_fn (b n INTER m_space m) x) x`
            by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,le_refl]
                >> FULL_SIMP_TAC std_ss [pos_simple_fn_def])
      >> FULL_SIMP_TAC std_ss [GSYM pos_fn_integral_cmul]
      >> `!x. (\x. Normal r'' * (g x * indicator_fn (b n INTER m_space m) x)) x <= fi n x`
            by (Q.UNABBREV_TAC `b`
                >> RW_TAC real_ss [indicator_fn_def,GSPECIFICATION,IN_INTER,mul_rzero,mul_rone]
                >> METIS_TAC [extreal_of_num_def])
      >> MATCH_MP_TAC le_trans
      >> Q.EXISTS_TAC `pos_fn_integral m (fi n)`
      >> CONJ_TAC >- (MATCH_MP_TAC pos_fn_integral_mono >> METIS_TAC [le_mul,lt_le])
      >> RW_TAC std_ss []
      >> Q.PAT_X_ASSUM `!z. IMAGE ri UNIV z ==> z <= y'` MATCH_MP_TAC
      >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      >> Q.EXISTS_TAC `n`
      >> Q.UNABBREV_TAC `ri`
      >> RW_TAC std_ss [])
  >> `!n:num. (\x. g x * indicator_fn (b n INTER m_space m) x) =
      (\t. SIGMA (\i. Normal (x i) * indicator_fn (a i INTER (b n INTER m_space m)) t) s)`
        by (RW_TAC std_ss [] >> FUN_EQ_TAC
            >> RW_TAC std_ss []
            >> Cases_on `~(x' IN m_space m)`
            >- (RW_TAC real_ss [indicator_fn_def, IN_INTER, mul_rone, mul_rzero] \\
                METIS_TAC [pos_simple_fn_def,EXTREAL_SUM_IMAGE_ZERO])
            >> RW_TAC real_ss [indicator_fn_def,IN_INTER,mul_rone,mul_rzero]
            >- FULL_SIMP_TAC real_ss [pos_simple_fn_def,indicator_fn_def]
            >> FULL_SIMP_TAC std_ss [pos_simple_fn_def,EXTREAL_SUM_IMAGE_ZERO])
  >> RW_TAC std_ss []
  >> `!n:num i. i IN s ==> (a i INTER (b n INTER m_space m)) IN measurable_sets m`
         by METIS_TAC [MEASURE_SPACE_INTER,pos_simple_fn_def]
  >> `FINITE s` by FULL_SIMP_TAC std_ss [pos_simple_fn_def]
  >> `!n :num.
       (pos_fn_integral m (\t. SIGMA (\i. Normal (x i) *
                                          indicator_fn ((\i. a i INTER (b n INTER m_space m)) i) t) s) =
        SIGMA (\i. Normal (x i) * measure m ((\i. a i INTER (b n INTER m_space m)) i)) s)`
        by (RW_TAC std_ss [] \\
            (MP_TAC o Q.SPECL [`m`, `s:num->bool`,
                               `(\i:num. a i INTER (b (n:num) INTER m_space m))`,
                               `(x:num->real)`]) pos_fn_integral_sum_cmul_indicator \\
            FULL_SIMP_TAC std_ss [pos_simple_fn_def])
  >> FULL_SIMP_TAC std_ss []
  >> Know `!i. i IN s ==> !n.
            (\i n. Normal (x i) * measure m (a i INTER (b n INTER m_space m))) i n <=
            (\i n. Normal (x i) * measure m (a i INTER (b n INTER m_space m))) i (SUC n)`
  >- (RW_TAC std_ss []
      >> MATCH_MP_TAC le_lmul_imp
      >> RW_TAC std_ss []
      >- METIS_TAC [pos_simple_fn_def,extreal_le_def,extreal_of_num_def]
      >> MATCH_MP_TAC INCREASING
      >> RW_TAC std_ss [MEASURE_SPACE_INCREASING]
      >> RW_TAC std_ss [SUBSET_DEF,IN_INTER]
      >> Q.UNABBREV_TAC `b`
      >> FULL_SIMP_TAC std_ss [GSPECIFICATION]
      >> MATCH_MP_TAC le_trans
      >> Q.EXISTS_TAC `fi n x'`
      >> RW_TAC real_ss []
      >> FULL_SIMP_TAC real_ss [ext_mono_increasing_suc])
  >> `!i. i IN s ==> !n. 0 <= (\i n. Normal (x i) * measure m (a i INTER (b n INTER m_space m))) i n`
         by (RW_TAC std_ss [] \\
             METIS_TAC [le_mul, extreal_le_def, extreal_of_num_def, MEASURE_SPACE_POSITIVE,
                        positive_def, MEASURE_SPACE_INTER, pos_simple_fn_def])
  >> FULL_SIMP_TAC std_ss [sup_sum_mono]
  >> RW_TAC std_ss []
  >> `!i. i IN s ==>
         (sup (IMAGE (\n.  Normal (x i) * measure m (a i INTER (b n INTER m_space m))) UNIV) =
          Normal (x i) * sup (IMAGE (\n. measure m (a i INTER (b n INTER m_space m))) UNIV))`
      by METIS_TAC [sup_cmul, pos_simple_fn_def]
  >> (MP_TAC o Q.SPEC `(\i. sup (IMAGE (\n. Normal (x i) *
                                            measure m (a i INTER (b (n:num) INTER m_space m)))
                                       UNIV))` o
      UNDISCH o Q.SPEC `s` o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_IN_IF
  >> `!x':num. x' IN s ==>
              (\i:num. sup (IMAGE (\n. Normal (x i) *
                                       measure m (a i INTER (b (n:num) INTER m_space m))) UNIV)) x'
               <> NegInf`
        by (RW_TAC std_ss [lt_infty]
            >> MATCH_MP_TAC lte_trans
            >> Q.EXISTS_TAC `0`
            >> RW_TAC std_ss []
            >- METIS_TAC [lt_infty,num_not_infty]
            >> RW_TAC std_ss [le_sup]
            >> MATCH_MP_TAC le_trans
            >> Q.EXISTS_TAC `Normal (x x') * measure m ((a x') INTER ((b 1) INTER m_space m))`
            >> RW_TAC std_ss []
            >> MATCH_MP_TAC le_lmul_imp
            >> CONJ_TAC >- METIS_TAC [extreal_le_def,extreal_of_num_def,pos_simple_fn_def]
            >> RW_TAC std_ss [le_sup]
            >> POP_ASSUM MATCH_MP_TAC
            >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
            >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
            >> METIS_TAC [])
  >> RW_TAC std_ss []
  >> `!i. BIGUNION (IMAGE (\n. a i INTER (b n INTER m_space m)) UNIV) = a i INTER m_space m`
       by (RW_TAC std_ss [EXTENSION,IN_BIGUNION_IMAGE,IN_INTER,IN_UNIV]
           >> EQ_TAC >- METIS_TAC []
           >> RW_TAC std_ss []
           >> Q.UNABBREV_TAC `b`
           >> RW_TAC real_ss [GSPECIFICATION]
           >> `f x' = sup (IMAGE (\i. fi i x') UNIV)` by FULL_SIMP_TAC std_ss []
           >> Cases_on `g x' = 0` >- METIS_TAC [mul_rzero,extreal_of_num_def]
           >> `Normal r'' * g x' < f x'`
                by (Cases_on `g x' = f x'`
                    >- (`0 < f x'` by METIS_TAC [le_lt,pos_simple_fn_def]
                        >> METIS_TAC [lt_rmul, mul_lone, IN_psfis_eq, pos_simple_fn_not_infty,
                                      extreal_lt_eq, extreal_of_num_def])
                    >> `g x' < f x'` by METIS_TAC [le_lt]
                    >> METIS_TAC [lt_mul2, mul_lone, extreal_not_infty, pos_simple_fn_not_infty,
                                  extreal_lt_eq, extreal_of_num_def, extreal_le_def, psfis_pos])
           >> Suff `?n. Normal r'' * g x' <= (\n. fi n x') n` >- RW_TAC std_ss []
           >> MATCH_MP_TAC sup_le_mono
           >> CONJ_TAC >- FULL_SIMP_TAC std_ss [ext_mono_increasing_def,ext_mono_increasing_suc]
           >> METIS_TAC [])
  >> `!i. i IN s==> (a i INTER m_space m = a i)`
       by METIS_TAC [pos_simple_fn_def,SUBSET_INTER1,MEASURE_SPACE_SUBSET_MSPACE]
  >> `!i. i IN s ==> (sup (IMAGE (measure m o (\n. a i INTER (b n INTER m_space m))) UNIV) =
                      measure m (a i))`
       by (RW_TAC std_ss []
           >> MATCH_MP_TAC MONOTONE_CONVERGENCE
           >> RW_TAC std_ss [IN_FUNSET,IN_UNIV]
           >> RW_TAC std_ss [SUBSET_DEF,IN_INTER]
           >> Q.UNABBREV_TAC `b`
           >> FULL_SIMP_TAC std_ss [GSPECIFICATION]
           >> MATCH_MP_TAC le_trans
           >> Q.EXISTS_TAC `fi n x'`
           >> RW_TAC real_ss []
           >> FULL_SIMP_TAC real_ss [ext_mono_increasing_suc])
  >> FULL_SIMP_TAC std_ss [o_DEF]
  >> `r' = SIGMA (\i. Normal (x i) * measure m (a i)) s`
       by METIS_TAC [IN_psfis_eq,psfis_unique,pos_simple_fn_integral_def,pos_simple_fn_integral_unique]
  >> POP_ORW
  >> `!i. i IN s ==> (\i. Normal (x i) * measure m (a i)) i <> NegInf`
      by METIS_TAC []
  >> (MP_TAC o Q.SPEC `(\i. Normal (x i) * measure m (a i))` o
      UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_IN_IF
  >> RW_TAC std_ss []);


(************************************************************)
(* LEBESGUE MONOTONE CONVERGENCE                            *)
(************************************************************)

(* NOTE: this is actually Theorem 9.6 (Beppo Levi) [1, p.75] for positive functions,
         the full version of "Monotone convergence" theroem for arbitrary integrable
         functions (Theorem 12.1 [1, p.96]) is not formalized yet.

   TODO: use `!x i. x IN m_space m ==> 0 <= fi i x` &
             `!x. x IN m_space ==> 0 <= f x)` &
             `!x. x IN m_space ==> mono_increasing (\i. fi i x)` instead.

   This theorem is also named after Beppo Levi, an Italian mathematician [4].
 *)
val lebesgue_monotone_convergence = store_thm
  ("lebesgue_monotone_convergence",
  ``!m f fi. measure_space m /\
        (!i. fi i IN measurable (m_space m, measurable_sets m) Borel) /\
        (!i x. 0 <= fi i x) /\ (!x. 0 <= f x) /\
        (!x. mono_increasing (\i. fi i x)) /\
        (!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = f x)) ==>
        (pos_fn_integral m f = sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV))``,
  Reverse (RW_TAC std_ss [GSYM le_antisym])
  >- (RW_TAC std_ss [sup_le]
      >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
      >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      >> MATCH_MP_TAC pos_fn_integral_mono_mspace
      >> RW_TAC std_ss []
      >> Q.PAT_X_ASSUM `!x. x IN m_space m ==> P` (MP_TAC o GSYM o UNDISCH o Q.SPEC `x`)
      >> RW_TAC std_ss []
      >> FULL_SIMP_TAC std_ss [sup_le]
      >> POP_ASSUM (K ALL_TAC)
      >> POP_ASSUM MATCH_MP_TAC
      >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
      >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
      >> METIS_TAC [])
  >> Q.ABBREV_TAC `r = sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV)`
  >> RW_TAC std_ss [pos_fn_integral_def, sup_le]
  >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
  >> RW_TAC std_ss [GSPECIFICATION]
  >> METIS_TAC [lebesgue_monotone_convergence_lemma, le_antisym]);

val lebesgue_monotone_convergence_subset = store_thm
  ("lebesgue_monotone_convergence_subset",
  ``!m f fi A. measure_space m /\
        (!i. fi i IN measurable (m_space m, measurable_sets m) Borel) /\
        (!i x. 0 <= fi i x) /\ (!x. 0 <= f x) /\
        (!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = f x)) /\
        (!x. mono_increasing (\i. fi i x)) /\ (A IN measurable_sets m) ==>
        (pos_fn_integral m (\x. f x * indicator_fn A x) =
         sup (IMAGE (\i. pos_fn_integral m (\x. fi i x * indicator_fn A x)) UNIV))``,
    RW_TAC std_ss []
 >> (MP_TAC o Q.SPECL [`m`, `(\x. f x * indicator_fn A x)`,
                       `(\i. (\x. fi i x * indicator_fn A x))`]) lebesgue_monotone_convergence
 >> RW_TAC std_ss []
 >> POP_ASSUM MATCH_MP_TAC
 >> CONJ_TAC
 >- METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR, measure_space_def, subsets_def,
               measurable_sets_def]
 >> CONJ_TAC >- RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,le_refl]
 >> CONJ_TAC >- RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,le_refl]
 >> CONJ_TAC
 >- (RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, le_refl, ext_mono_increasing_def] \\
     FULL_SIMP_TAC std_ss [ext_mono_increasing_def])
 >> RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
 >> Suff `IMAGE (\i:num. 0:extreal) UNIV = (\y. y = 0)` >- RW_TAC std_ss [sup_const]
 >> RW_TAC std_ss [EXTENSION, IN_ABS, IN_IMAGE, IN_UNIV]);


(**********************************************************)
(*  Existence of Convergent sequence                      *)
(**********************************************************)

(**** Define the sequence ****)
val fn_seq_def = Define
   `fn_seq m f =
       (\n x. SIGMA
                (\k. &k / 2 pow n *
                     indicator_fn
                       {x | x IN m_space m /\ &k / 2 pow n <= f x /\
                            f x < (&k + 1) / 2 pow n} x) (count (4 ** n)) +
              2 pow n * indicator_fn {x | x IN m_space m /\ 2 pow n <= f x} x)`;

(**** Define their integrals ****)
val fn_seq_integral_def = Define
   `fn_seq_integral m f =
         (\n. SIGMA
                (\k. &k / 2 pow n *
                     measure m
                       {x | x IN m_space m /\ &k / 2 pow n <= f x /\
                            f x < (&k + 1) / 2 pow n}) (count (4 ** n)) +
              2 pow n * measure m {x | x IN m_space m /\ 2 pow n <= f x})`;

(******************************************************)
(****   f_n(x) = &k / 2 pow n in the k^th interval ****)
(******************************************************)

val lemma_fn_1 = prove (
  ``!m f n x k. x IN m_space m /\ k IN count (4 ** n) /\ &k / 2 pow n <= f x /\
                f x < (&k + 1) / 2 pow n
            ==> (fn_seq m f n x = &k / 2 pow n)``,
 (* proof *)
  RW_TAC std_ss []
  >> `0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
  >> `0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
  >> FULL_SIMP_TAC real_ss [fn_seq_def, indicator_fn_def, GSPECIFICATION, IN_COUNT,
                            mul_rone, mul_rzero, extreal_of_num_def, extreal_pow_def,
                            extreal_div_eq, extreal_add_def]
  >> `f x <> PosInf` by METIS_TAC [lt_infty,lt_trans]
  >> `f x <> NegInf` by METIS_TAC [lt_infty,lte_trans]
  >> `?r. f x = Normal r` by METIS_TAC [extreal_cases]
  >> FULL_SIMP_TAC std_ss [extreal_lt_eq,extreal_le_def]
  >> `(\k'. Normal (&k' / 2 pow n) * if &k' / 2 pow n <= r /\ r < &(k' + 1) / 2 pow n then Normal 1 else Normal 0) =
      (\k'. Normal((&k' / 2 pow n) * if &k' / 2 pow n <= r /\ r < &(k' + 1) / 2 pow n then 1 else 0))`
         by (RW_TAC std_ss [FUN_EQ_THM] >> METIS_TAC [extreal_add_def,extreal_mul_def])
  >> POP_ORW
  >> `FINITE (count (4 ** n))` by RW_TAC std_ss [FINITE_COUNT]
  >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_NORMAL,extreal_11,extreal_mul_def,extreal_add_def]
  >- (`k + 1 <= 4 ** n` by RW_TAC real_ss [LESS_EQ]
      >> `&(k + 1) <= (4:real) pow n` by RW_TAC real_ss [REAL_OF_NUM_POW]
      >> FULL_SIMP_TAC real_ss [REAL_LT_RDIV_EQ]
      >> `r * 2 pow n < 4 pow n` by METIS_TAC [REAL_LTE_TRANS]
      >> METIS_TAC [REAL_LT_RDIV_EQ,REAL_POW_DIV,EVAL ``4/2:real``,real_lte])
  >> FULL_SIMP_TAC real_ss [GSYM real_lt]
  >> (MP_TAC o UNDISCH o Q.SPECL [`k`,`count (4 ** n)`] o CONJUNCT2 o Q.SPEC `(\k'. &k' / 2 pow n *
           if &k' / 2 pow n <= r:real /\ r < &(k' + 1) / 2 pow n then 1 else 0)`) (INST_TYPE [alpha |-> ``:num``] REAL_SUM_IMAGE_THM)
  >> RW_TAC real_ss []
  >> `count (4 ** n) = k INSERT (count (4 ** n))` by RW_TAC std_ss [GSYM ABSORPTION,IN_COUNT]
  >> POP_ORW
  >> RW_TAC std_ss [REAL_SUM_IMAGE_THM]
  >> Suff `SIGMA (\k'. &k' / 2 pow n * if &k' / 2 pow n <= r /\ r < &(k' + 1) / 2 pow n then 1 else 0)
                 (count (4 ** n) DELETE k) = 0:real`
  >- RW_TAC real_ss []
  >> `FINITE (count (4 ** n) DELETE k)` by RW_TAC std_ss [FINITE_COUNT,FINITE_DELETE]
  >> ONCE_REWRITE_TAC [(UNDISCH o Q.SPEC `count (4 ** n) DELETE k` o INST_TYPE [alpha |-> ``:num``]) REAL_SUM_IMAGE_IN_IF]
  >> Suff `(\x. if x IN count (4 ** n) DELETE k then (\k'. &k' / 2 pow n *
              if &k' / 2 pow n <= r:real /\ r < &(k' + 1) / 2 pow n then
                1 else 0) x else 0) = (\x:num. 0:real)`
  >- FULL_SIMP_TAC real_ss [REAL_SUM_IMAGE_0]
  >> RW_TAC real_ss [FUN_EQ_THM,IN_COUNT,IN_DELETE]
  >> RW_TAC real_ss [COND_EXPAND]
  >> Cases_on `&x'<=((&k):real)`
  >- (`&(x'+1)<=(&k):real` by FULL_SIMP_TAC real_ss [LESS_EQ,REAL_LE_LT]
      >> `r * 2 pow n < &(x' + 1)` by METIS_TAC [REAL_LT_RDIV_EQ]
      >> `r:real * 2 pow n < &k` by METIS_TAC [REAL_LTE_TRANS]
      >> METIS_TAC [REAL_LT_RDIV_EQ,real_lte])
  >> FULL_SIMP_TAC std_ss [GSYM real_lt]
  >> `&(k+1)<=(&x'):real` by FULL_SIMP_TAC real_ss [LESS_EQ,REAL_LE_LT]
  >> `&x' <= r * 2 pow n` by METIS_TAC [REAL_LE_LDIV_EQ]
  >> `&(k+1) <= r * 2 pow n` by METIS_TAC [REAL_LE_TRANS]
  >> METIS_TAC [REAL_LE_LDIV_EQ,real_lte]);


(**********************************************)
(****   f_n(x) = 2 pow n if 2 pow n <= f x ****)
(**********************************************)

val lemma_fn_2 = prove (
  ``!m f n x. x IN m_space m /\ 2 pow n <= f x ==> (fn_seq m f n x = 2 pow n)``,
 (* proof *)
  RW_TAC real_ss [fn_seq_def,indicator_fn_def,GSPECIFICATION,mul_rone]
  >> `FINITE (count (4 ** n))` by RW_TAC std_ss [FINITE_COUNT]
  >> `0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
  >> `0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
  >> Suff `SIGMA (\k. &k / 2 pow n *  if &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n then 1 else 0) (count (4 ** n)) = 0`
  >- RW_TAC real_ss [add_lzero]
  >> (MP_TAC o Q.SPEC `(\k. &k / 2 pow n * if &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n then 1 else 0)` o UNDISCH o Q.SPEC `count (4 ** n)` o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_IN_IF
  >> `!x'. (\k. &k / 2 pow n * if &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n then 1 else 0) x' <> NegInf`
      by (RW_TAC std_ss [mul_rone,mul_rzero]
          >> RW_TAC std_ss [extreal_of_num_def,extreal_pow_def,extreal_mul_def,extreal_div_eq,extreal_not_infty])
  >> Suff `(\x'. if x' IN count (4 ** n) then &x' / 2 pow n * if &x' / 2 pow n <= f x /\ f x < (&x' + 1) / 2 pow n then 1 else 0 else 0) = (\x. 0)`
  >- RW_TAC std_ss [EXTREAL_SUM_IMAGE_ZERO]
  >> RW_TAC real_ss [FUN_EQ_THM,IN_COUNT]
  >> RW_TAC real_ss [COND_EXPAND,mul_rzero,mul_rone]
  >> `&(x' + 1):real <= 4 pow n` by RW_TAC real_ss [LESS_EQ,REAL_OF_NUM_POW]
  >> `&(x' + 1):real / 2 pow n <= 4 pow n / 2 pow n` by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_POS_NZ,REAL_DIV_RMUL]
  >> `(&x' + 1) / 2 pow n <= 4 pow n / 2 pow n` by RW_TAC real_ss [extreal_div_eq,extreal_pow_def,extreal_add_def,extreal_of_num_def,extreal_le_def]
  >> `f x < 4 pow n / 2 pow n` by METIS_TAC [lte_trans]
  >> `4 pow n / 2 pow n = 2 pow n` by RW_TAC std_ss [extreal_pow_def,extreal_div_eq,extreal_of_num_def,GSYM REAL_POW_DIV,EVAL ``4/2:real``]
  >> METIS_TAC [extreal_lt_def]);

(************************************************************************)
(*** f(x) is either larger than 2 pow n or is inside some k interval ****)
(************************************************************************)

val lemma_fn_3 = prove (
  ``!m f n x. x IN m_space m /\ 0 <= f x ==>
             (2 pow n <= f x) \/
             (?k. k IN count (4 ** n) /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n)``,
 (* proof *)
  RW_TAC real_ss [IN_COUNT]
  >> Cases_on `2 pow n <= f x`
  >- RW_TAC std_ss []
  >> `f x < 2 pow n` by FULL_SIMP_TAC std_ss [extreal_lt_def]
  >> `f x <> PosInf` by METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_not_infty,lt_infty,lt_trans]
  >> `f x <> NegInf` by METIS_TAC [lt_infty,lte_trans,extreal_of_num_def,extreal_not_infty]
  >> `?r. f x = Normal r` by METIS_TAC [extreal_cases]
  >> `0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
  >> `0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
  >> FULL_SIMP_TAC real_ss [extreal_of_num_def,extreal_pow_def,extreal_le_def,extreal_lt_eq,extreal_div_eq,extreal_add_def]
  >> Q.EXISTS_TAC `flr (2 pow n * r)`
  >> CONJ_TAC
  >- (`2 pow n * r < 2 pow n * 2 pow n` by RW_TAC real_ss [REAL_LT_LMUL]
    >> `2 pow n * 2 pow n = 4:real pow n` by RW_TAC real_ss [GSYM POW_MUL]
    >> `0 <= 2 pow n * r` by RW_TAC real_ss [REAL_LT_LE_MUL]
    >> `&(4 ** n) = 4:real pow n` by RW_TAC real_ss [GSYM REAL_OF_NUM_POW]
    >> FULL_SIMP_TAC real_ss []
    >> `&flr (2 pow n * r) <= 2 pow n * r` by RW_TAC real_ss [NUM_FLOOR_LE]
    >> `&flr (2 pow n * r) < 4:real pow n` by METIS_TAC [REAL_LET_TRANS]
    >> METIS_TAC [REAL_LT])
  >> CONJ_TAC
  >- (`0 <= 2 pow n * r` by RW_TAC real_ss [REAL_LT_LE_MUL]
     >> `&flr (2 pow n * r) <= 2 pow n * r` by RW_TAC real_ss [NUM_FLOOR_LE]
     >> `&flr (2 pow n * r) / 2 pow n <= 2 pow n * r / 2 pow n`
        by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_POS_NZ,REAL_DIV_RMUL]
     >> METIS_TAC [REAL_EQ_LDIV_EQ,REAL_MUL_COMM])
  >> `0 <= 2 pow n * r` by RW_TAC real_ss [REAL_LT_LE_MUL]
  >> `2 pow n * r < &(flr (2 pow n * r) + 1)` by METIS_TAC [NUM_FLOOR_DIV_LOWERBOUND,REAL_LT_01,REAL_OVER1,REAL_MUL_RID]
  >> `2 pow n * r / 2 pow n < &(flr (2 pow n * r) + 1) / 2 pow n`
      by RW_TAC real_ss [REAL_LT_LDIV_EQ,REAL_POS_NZ,REAL_DIV_RMUL]
  >> METIS_TAC [REAL_EQ_LDIV_EQ,REAL_MUL_COMM]);


(*********************************)
(*   fn_(x) = 0 outside m_space  *)
(*********************************)

val lemma_fn_4 = prove (
  ``!m f n x. ~(x IN m_space m) ==> (fn_seq m f n x = 0)``,
 (* proof *)
  RW_TAC real_ss [fn_seq_def,indicator_fn_def,GSPECIFICATION,mul_rzero,add_rzero]
  >> METIS_TAC [FINITE_COUNT,EXTREAL_SUM_IMAGE_ZERO]);


(*********************************)
(*       fn_(x) positive         *)
(*********************************)

val lemma_fn_5 = prove (
  ``!m f n x. 0 <= f x ==> (0 <= fn_seq m f n x)``,
 (* proof *)
  RW_TAC real_ss []
  >> `0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
  >> `0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
  >> `0 < 2 pow n` by METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_lt_eq]
  >> Cases_on `~(x IN m_space m)`
  >- RW_TAC std_ss [lemma_fn_4,le_refl]
  >> FULL_SIMP_TAC std_ss []
  >> (MP_TAC o Q.SPECL [`m`,`f`,`n`,`x`]) lemma_fn_3
  >> RW_TAC real_ss []
  >- RW_TAC real_ss [lt_imp_le,lemma_fn_2]
  >> `fn_seq m f n x = &k / 2 pow n` by RW_TAC real_ss [lemma_fn_1]
  >> ASM_SIMP_TAC std_ss []
  >> RW_TAC std_ss [extreal_of_num_def,extreal_pow_def,extreal_div_eq,extreal_le_def]
  >> MATCH_MP_TAC REAL_LE_DIV
  >> RW_TAC real_ss [REAL_POW_LT,REAL_LT_IMP_LE]);


(*******************************************************************************)
(*                        MONOTONICALLY INCREASING                             *)
(*******************************************************************************)

val lemma_fn_mono_increasing = prove (
  ``!m f x. 0 <= f x ==> mono_increasing (\n. fn_seq m f n x)``,
 (* proof *)
  RW_TAC std_ss [ext_mono_increasing_suc,ADD1]
  >> Cases_on `~(x IN m_space m)`
  >- RW_TAC real_ss [lemma_fn_4,le_refl]
  >> FULL_SIMP_TAC std_ss []
  >> `!n x k. x IN m_space m /\ (k IN count (4 ** n)) /\ (&k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n) ==> (fn_seq m f n x = &k / 2 pow n)`
      by RW_TAC std_ss [lemma_fn_1]
  >> `!n x. x IN m_space m /\ 2 pow n <= f x ==> (fn_seq m f n x = 2 pow n)`
       by RW_TAC std_ss [lemma_fn_2]
  >> `!n. 0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
  >> `!n. 0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
  >> `!n k. (k IN count (4 ** (n + 1))) /\ (&k / 2 pow (n + 1) <= f x /\ f x < (&k + 1) / 2 pow (n + 1)) ==> (fn_seq m f n x <= fn_seq m f (n + 1) x)`
       by (RW_TAC real_ss []
           >> `fn_seq m f (n + 1) x = &k / (2 pow (n + 1))` by RW_TAC real_ss []
           >> `f x <> NegInf` by METIS_TAC [lt_infty,lte_trans,extreal_of_num_def,extreal_not_infty]
           >> `f x <> PosInf` by METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_not_infty,lt_infty,lt_trans]
           >> `?r. f x = Normal r` by METIS_TAC [extreal_cases]
           >> `0:real <> 2 pow (n + 1)` by RW_TAC real_ss []
           >> FULL_SIMP_TAC std_ss [extreal_of_num_def,extreal_pow_def,extreal_div_eq,extreal_add_def,extreal_mul_def,extreal_le_def,extreal_lt_eq]
           >> `&(k + 1) / (2 pow (n + 1)):real = (&(k + 1) / 2) / (2 pow (n + 1) / 2)` by RW_TAC real_ss [REAL_DIV_DENOM_CANCEL]
           >> `2 pow (n + 1) / 2 = (2 pow n):real` by (RW_TAC std_ss [GSYM ADD1,pow] >> RW_TAC real_ss [REAL_EQ_LDIV_EQ,REAL_MUL_COMM])
           >> `&k / 2 pow (n + 1) = (&k / 2) / (2 pow (n + 1) / 2):real` by RW_TAC real_ss [REAL_DIV_DENOM_CANCEL]
           >> FULL_SIMP_TAC std_ss []
           >> STRUCT_CASES_TAC (Q.SPEC `k` EVEN_OR_ODD)
           >- (FULL_SIMP_TAC std_ss [EVEN_EXISTS]
               >> FULL_SIMP_TAC real_ss []
               >> `&k / 2:real = &m'` by RW_TAC real_ss [REAL_EQ_LDIV_EQ]
               >> `&(2 * m' + 1):real < &(2 * m' + 2)` by RW_TAC real_ss []
               >> `&(2 * m' + 1) / 2:real < &(2 * m' + 2) / 2` by RW_TAC real_ss [REAL_LT_RDIV]
               >> `&(2 * m' + 1) / 2 / (2 pow n):real < &(2 * m' + 2) / 2 / 2 pow n` by RW_TAC real_ss [REAL_LT_RDIV]
               >> `&(2 * m' + 2) / 2 = &(m'+1):real` by RW_TAC real_ss [REAL_EQ_LDIV_EQ,REAL_ADD_LDISTRIB]
               >> `r < &(m' + 1) / 2 pow n` by METIS_TAC [REAL_LT_TRANS]
               >> `&(2 * m') / 2 / 2 pow n = &m' / (2 pow n):real` by METIS_TAC []
               >> FULL_SIMP_TAC real_ss []
               >> Cases_on `m' IN count (4 ** n)`
               >- (`fn_seq m f n x = Normal (&m' / 2 pow n)` by METIS_TAC [extreal_le_def,extreal_lt_eq]
                   >> RW_TAC std_ss [le_refl])
               >> FULL_SIMP_TAC real_ss [IN_COUNT,NOT_LESS]
               >> `4:real pow n <= &m'` by RW_TAC real_ss [REAL_OF_NUM_POW]
               >> `4:real pow n / 2 pow n <= &m' / 2 pow n` by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_POS_NZ,REAL_DIV_RMUL]
               >> `2 pow n <= r` by METIS_TAC [REAL_LE_TRANS,REAL_POW_DIV,EVAL ``4/2:real``]
               >> `fn_seq m f n x = Normal (2 pow n)` by METIS_TAC [extreal_le_def,extreal_lt_eq]
               >> `(2 pow n):real <= &m' / 2 pow n` by METIS_TAC [REAL_POW_DIV,EVAL ``4/2:real``]
               >> `&(2*m')/2 = &m':real` by RW_TAC real_ss []
               >> RW_TAC std_ss [extreal_le_def])
           >> FULL_SIMP_TAC std_ss [ODD_EXISTS]
           >> `(k - 1) < k` by RW_TAC real_ss []
           >> `&(k - 1) / 2 < (&k) / 2:real` by RW_TAC real_ss [REAL_LT_LDIV_EQ,REAL_DIV_RMUL]
           >> `&(k - 1) / 2 / 2 pow n < (&k) / 2 / (2 pow n):real` by RW_TAC real_ss [REAL_LT_LDIV_EQ,REAL_DIV_RMUL,REAL_POS_NZ]
           >> `&(k - 1) / 2 / 2 pow n <= r` by METIS_TAC [REAL_LTE_TRANS,REAL_LT_IMP_LE]
           >> `&(k - 1):real = 2 * &m'` by RW_TAC real_ss []
           >> `!x. 2 * x / 2 = x:real` by RW_TAC real_ss [REAL_EQ_LDIV_EQ,REAL_MUL_COMM]
           >> `&m' / (2 pow n) <= r` by METIS_TAC [REAL_MUL]
            >> `&(k + 1):real = 2 * (&m' + 1)` by RW_TAC real_ss []
           >> FULL_SIMP_TAC real_ss []
           >> `r < &(m' + 1) / (2 pow n)` by METIS_TAC [REAL_MUL,REAL_ADD]
               >> Cases_on `m' IN count (4 ** n)`
           >- (Q.PAT_X_ASSUM `!n x k. Q` (MP_TAC o Q.SPECL [`n`,`x`, `m'`])
               >> RW_TAC std_ss [extreal_le_def,extreal_lt_eq]
               >> `&(2 * m'):real <= &SUC (2*m')` by RW_TAC real_ss []
               >> `&(2 * m') / 2:real <= &SUC (2 * m') / 2` by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_DIV_RMUL]
               >> `&(2 * m') / 2 / 2 pow n <= &SUC (2 * m') / 2 / (2 pow n):real` by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_DIV_RMUL,REAL_POS_NZ]
               >> `&(2 * m') / 2:real = &m'` by RW_TAC real_ss [REAL_EQ_LDIV_EQ]
               >> FULL_SIMP_TAC real_ss [REAL_LE_TRANS])
           >> FULL_SIMP_TAC real_ss [IN_COUNT,NOT_LESS]
           >> `4 pow n <= &m':real` by RW_TAC real_ss [REAL_OF_NUM_POW]
           >> `4:real pow n / 2 pow n <= &m' / 2 pow n` by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_POS_NZ,REAL_DIV_RMUL]
           >> `&(k - 1):real = 2 * &m'` by RW_TAC real_ss []
           >> `&m' < &k / 2:real` by METIS_TAC []
           >> `&m' / (2 pow n):real  < &k / 2 / 2 pow n` by RW_TAC real_ss [REAL_LT_LDIV_EQ,REAL_POS_NZ,REAL_DIV_RMUL]
           >> `2 pow n <= r` by METIS_TAC [REAL_POW_DIV,EVAL ``4/2:real``,REAL_LET_TRANS,REAL_LTE_TRANS,REAL_LT_IMP_LE]
           >> `fn_seq m f n x = Normal (2 pow n)` by METIS_TAC [extreal_le_def,extreal_lt_eq]
           >> `2 pow n <= &m' / (2 pow n):real` by METIS_TAC [REAL_POW_DIV,EVAL ``4/2:real``]
           >> `&(2 * m'):real <= &SUC (2 * m')` by RW_TAC real_ss []
           >> `&(2 * m') / 2:real <= &SUC (2 * m') / 2` by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_DIV_RMUL]
           >> `&(2 * m') / 2 / 2 pow n <= &SUC (2 * m') / 2 / (2 pow n):real` by RW_TAC real_ss [REAL_LE_LDIV_EQ,REAL_DIV_RMUL,REAL_POS_NZ]
           >> `&(2 * m') / 2:real = &m'` by RW_TAC real_ss [REAL_EQ_LDIV_EQ]
           >> METIS_TAC [REAL_LE_TRANS,extreal_le_def])
   >> `!n. 2 pow (n + 1) <= f x ==> (fn_seq m f n x <= fn_seq m f (n + 1) x)`
        by (RW_TAC real_ss []
            >> `2:real pow n < 2 pow (n + 1)` by RW_TAC real_ss [REAL_POW_MONO_LT]
            >> `2 pow n < 2 pow (n + 1)` by METIS_TAC [extreal_pow_def,extreal_of_num_def,extreal_lt_eq]
            >> METIS_TAC [extreal_le_def,extreal_lt_eq,lte_trans,lt_imp_le])
   >> (MP_TAC o Q.SPECL [`m`,`f`,`n + 1`,`x`]) lemma_fn_3
   >> RW_TAC std_ss []
   >- RW_TAC std_ss []
   >> METIS_TAC []);


(*******************************************************************************)
(*                            UPPER BOUNDED BY f                               *)
(*******************************************************************************)

val lemma_fn_upper_bounded = prove (
  ``!m f n x. 0 <= f x ==> (fn_seq m f n x <= f x)``,
 (* proof *)
  RW_TAC std_ss []
  >> Cases_on `~(x IN m_space m)` >- RW_TAC real_ss [lemma_fn_4]
  >> FULL_SIMP_TAC std_ss []
  >> (MP_TAC o Q.SPECL [`m`,`f`,`n`,`x`]) lemma_fn_3
  >> RW_TAC real_ss []
  >- METIS_TAC [lemma_fn_2,le_refl]
  >> `fn_seq m f n x =  &k / 2 pow n` by RW_TAC real_ss [lemma_fn_1]
  >> RW_TAC std_ss []);


(*******************************************************************************)
(*                            f Supremum of fn_seq                             *)
(*******************************************************************************)

val lemma_fn_sup = prove (
  ``!m f x. x IN m_space m /\ 0 <= f x ==>
            (sup (IMAGE (\n. fn_seq m f n x) UNIV) = f x)``,
  RW_TAC std_ss []
  >> Cases_on `f x = PosInf`
  >- (`!n:num. fn_seq m f n x = 2 pow n` by METIS_TAC [le_infty,lemma_fn_2]
      >> RW_TAC std_ss [sup_eq,le_infty]
      >> `!n. 2 pow n <= y`
            by (RW_TAC std_ss []
                >> POP_ASSUM MATCH_MP_TAC
                >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
                >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
                >> METIS_TAC [])
      >> SPOSE_NOT_THEN ASSUME_TAC
      >> METIS_TAC [EXTREAL_ARCH_POW,extreal_lt_def])
  >> `!n.  fn_seq m f n x <= f x` by METIS_TAC [lemma_fn_upper_bounded]
  >> `?r. f x = Normal r` by METIS_TAC [extreal_cases,lt_infty,lte_trans,extreal_of_num_def]
  >> `!n. fn_seq m f n x <> PosInf` by METIS_TAC [lt_infty,let_trans]
  >> `!n. fn_seq m f n x <> NegInf` by METIS_TAC [lt_infty,lte_trans,lemma_fn_5,extreal_of_num_def]
  >> `?r. !n. fn_seq m f n x = Normal (r n)`
         by (Q.EXISTS_TAC `\n. @r. fn_seq m f n x = Normal r`
             >> GEN_TAC >> RW_TAC std_ss []
             >> SELECT_ELIM_TAC
                >> RW_TAC std_ss []
             >> METIS_TAC [extreal_cases])
  >> `?N. f x < 2 pow N` by RW_TAC std_ss [EXTREAL_ARCH_POW]
  >> `!p n. p <= n ==> 2 pow p <= 2 pow n` by METIS_TAC [pow_le_mono,EVAL ``1<=2``]
  >> `!n. N <= n ==> f x < 2 pow n` by METIS_TAC [lte_trans]
  >> `!n. N <= n ==> ?k. k IN count (4 ** n) /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n` by METIS_TAC [lemma_fn_3,extreal_lt_def]
  >> `!n. 0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
  >> `!n. 0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
  >> `!n k. &k / 2 pow n = Normal (&k / 2 pow n)` by METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_div_eq]
  >> `!n z. Normal z / 2 pow n = Normal (z / 2 pow n)` by METIS_TAC [extreal_pow_def,extreal_div_eq,extreal_of_num_def]
  >> `!n. N <= n ==> (f x - 1 / 2 pow n < fn_seq m f n x)`
        by (RW_TAC real_ss []
            >> `?k. k IN count (4 ** n) /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n` by METIS_TAC []
            >> `fn_seq m f n x = &k / 2 pow n` by METIS_TAC [lemma_fn_1]
            >> `Normal (&k + 1) / Normal (2 pow n) = Normal ((&k + 1) / (2 pow n))` by METIS_TAC [extreal_div_eq]
            >> `Normal r < Normal ((&k + 1) /  (2 pow n))` by METIS_TAC [extreal_pow_def,extreal_of_num_def,extreal_add_def]
            >> FULL_SIMP_TAC std_ss [extreal_lt_eq,GSYM REAL_DIV_ADD,extreal_pow_def,extreal_sub_def,extreal_of_num_def,extreal_div_eq,extreal_lt_eq,REAL_LT_SUB_RADD]
            >> `r' n = &k / 2 pow n` by METIS_TAC [extreal_div_eq,extreal_11]
            >> FULL_SIMP_TAC std_ss [])
  >> FULL_SIMP_TAC std_ss []
  >> `!n. N <= n ==> (r - 1 / 2 pow n < r' n)`
        by (FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq,extreal_of_num_def,extreal_pow_def,extreal_div_eq,extreal_add_def]
            >> RW_TAC std_ss []
            >> METIS_TAC [extreal_sub_def,extreal_lt_eq])
  >> `mono_increasing (\n. fn_seq m f n x)` by METIS_TAC [lemma_fn_mono_increasing]
  >> `mono_increasing r'` by (FULL_SIMP_TAC std_ss [ext_mono_increasing_def,mono_increasing_def] >> METIS_TAC [extreal_le_def])
  >> FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq,extreal_of_num_def,extreal_pow_def,extreal_div_eq,extreal_add_def,extreal_sub_def,extreal_not_infty]
  >> RW_TAC std_ss [GSYM sup_seq,SEQ,GREATER_EQ]
  >> `!n. 1:real / 2 pow n = (1 / 2) pow n` by RW_TAC real_ss [POW_ONE,REAL_POW_DIV]
  >> `!n. r' n < r + 1 / 2 pow n` by METIS_TAC [POW_HALF_POS,REAL_LT_ADDR,REAL_LET_TRANS,REAL_LT_IMP_LE]
  >> `!n. N <= n ==> (abs (r' n - r) < 1 / 2 pow n)` by METIS_TAC [ABS_BETWEEN,POW_HALF_POS]
  >> `?N1. (1 / 2) pow N1 < e:real` by RW_TAC std_ss [POW_HALF_SMALL]
  >> `!n. N1 <= n ==> ((1 / 2:real) pow n <= (1 / 2) pow N1)` by RW_TAC std_ss [POW_HALF_MONO]
  >> `!n. N1 <= n ==> ((1 / 2:real) pow n < e)` by METIS_TAC [REAL_LET_TRANS]
  >> Q.EXISTS_TAC `N + N1`
  >> RW_TAC real_ss []
  >> `N <= N + N1` by RW_TAC std_ss [LESS_EQ_ADD]
  >> `N1 <= N + N1` by RW_TAC std_ss [LESS_EQ_ADD]
  >> `N <= n /\ N1 <= n` by METIS_TAC [LESS_EQ_TRANS]
  >> METIS_TAC [REAL_LT_TRANS]);


(*******************************************************************************)
(*          SEQ Positive Simple Functions and Define Integral                  *)
(*******************************************************************************)

val lemma_fn_in_psfis = prove (
  ``!m f n. (!x. 0 <= f x) /\ measure_space m /\
            f IN measurable (m_space m,measurable_sets m) Borel
        ==> (fn_seq_integral m f n IN psfis m (fn_seq m f n))``,
  RW_TAC std_ss [IN_psfis_eq,pos_simple_fn_def]
  >> Q.EXISTS_TAC `count (4 ** n + 1)`
  >> Q.EXISTS_TAC `(\k. if k IN count (4 ** n) then {x | x IN m_space m /\ &k / 2 pow n <= f x /\
                         f x < (&k + 1) / 2 pow n} else {x | x IN m_space m /\ 2 pow n <= f x} )`
  >> Q.EXISTS_TAC `(\k. if k IN count (4 ** n) then &k / 2 pow n else 2 pow n )`
  >> `FINITE (count (4 ** n))` by RW_TAC std_ss [FINITE_COUNT]
  >> `FINITE (count (4 ** n + 1))` by RW_TAC std_ss [FINITE_COUNT]
  >> `!n. 0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
  >> `!n. 0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
  >> `!n k. &k / 2 pow n = Normal (&k / 2 pow n)`
      by METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_div_eq]
  >> `!n z. Normal z / 2 pow n = Normal (z / 2 pow n)`
      by METIS_TAC [extreal_pow_def,extreal_div_eq,extreal_of_num_def]
  >> CONJ_TAC
  >- (CONJ_TAC >- RW_TAC std_ss [lemma_fn_5]
      >> CONJ_TAC
      >- (RW_TAC real_ss [fn_seq_def,IN_COUNT,GSYM ADD1,COUNT_SUC]
          >> `(\i. Normal (if i < 4 ** n then &i / 2 pow n else 2 pow n) *
                   indicator_fn (if i < 4 ** n then
                   {x | x IN m_space m /\ Normal (&i / 2 pow n) <= f x /\
                                     f x < (&i + 1) / 2 pow n}
                   else {x | x IN m_space m /\ 2 pow n <= f x}) t) =
              (\i. if i < 4 ** n then &i / 2 pow n  *
                 indicator_fn {x | x IN m_space m /\ &i / 2 pow n <= f x /\
                                     f x < (&i + 1) / 2 pow n} t
                   else 2 pow n * indicator_fn {x | x IN m_space m /\ 2 pow n <= f x} t)`
                by (RW_TAC std_ss [FUN_EQ_THM]
                    >> Cases_on `i < 4 ** n` >- RW_TAC std_ss []
                    >> RW_TAC std_ss [extreal_of_num_def,extreal_pow_def])
          >> POP_ORW
          >> (MP_TAC o Q.SPEC `4 ** n` o UNDISCH o Q.SPECL [`(\i. if i < 4 ** n then &i / 2 pow n * indicator_fn {x | x IN m_space m /\ &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n} t
               else 2 pow n * indicator_fn {x | x IN m_space m /\ 2 pow n <= f x} t)`,`count (4 ** n)`] o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_PROPERTY
          >> `!x. (\i. if i < 4 ** n then &i / 2 pow n * indicator_fn {x | x IN m_space m /\ &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n} t
                else 2 pow n * indicator_fn {x | x IN m_space m /\ 2 pow n <= f x} t) x <> NegInf`
               by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,num_not_infty]
                   >> METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_not_infty])
          >> RW_TAC std_ss []
          >> `count (4 ** n) DELETE 4 ** n = count (4 ** n)`
              by METIS_TAC [DELETE_NON_ELEMENT,IN_COUNT,LESS_EQ_REFL,NOT_LESS]
          >> RW_TAC std_ss []
          >> Q.PAT_X_ASSUM `SIGMA f s = Q` (K ALL_TAC)
          >> FULL_SIMP_TAC std_ss [GSYM IN_COUNT]
          >> `!i. Normal (&i / 2 pow n) = &i / 2 pow n` by METIS_TAC []
          >> POP_ORW
          >> Q.PAT_X_ASSUM `!n k. &k / 2 pow n = Normal (&k / 2 pow n)` (K ALL_TAC)
          >> `!i.  (\i. &i / 2 pow n * indicator_fn {x | x IN m_space m /\ &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n} t) i <> NegInf`
               by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,num_not_infty]
                   >> METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_not_infty])
          >> (MP_TAC o Q.SPECL [`count (4 ** n)`,`(\k. &k / 2 pow n * indicator_fn {x | x IN m_space m /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n} t)`,` 2 pow n * indicator_fn {x | x IN m_space m /\ 2 pow n <= f x} t`] o INST_TYPE [alpha |-> ``:num``] o GSYM) EXTREAL_SUM_IMAGE_IN_IF_ALT
          >> RW_TAC std_ss []
          >> MATCH_MP_TAC add_comm
          >> DISJ1_TAC
          >> Reverse CONJ_TAC
          >- (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,num_not_infty]
              >> METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_not_infty])
          >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY])
      >> CONJ_TAC
      >- (RW_TAC real_ss []
          >- (`{x | x IN m_space m /\ Normal (&i / 2 pow n) <= f x /\ f x < (&i + 1) / 2 pow n} =
               {x | Normal (&i / 2 pow n) <= f x /\ f x < Normal (&(i + 1) / 2 pow n)} INTER m_space m`
                 by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER,CONJ_COMM]
                     >> `(&i + 1:extreal) = &(i + 1)` by RW_TAC std_ss [extreal_add_def,extreal_of_num_def,REAL_ADD]
                     >> METIS_TAC [])
              >> METIS_TAC [IN_MEASURABLE_BOREL_ALL, measurable_sets_def,subsets_def,space_def,m_space_def])
          >> `{x | x IN m_space m /\ 2 pow n <= f x} = {x | Normal (2 pow n) <= f x} INTER m_space m`
                by RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER,CONJ_COMM,extreal_of_num_def,extreal_pow_def]
          >> METIS_TAC [IN_MEASURABLE_BOREL_ALL, measurable_sets_def,subsets_def,space_def,m_space_def])
      >> CONJ_TAC
      >- RW_TAC std_ss []
      >> CONJ_TAC
      >- RW_TAC real_ss [extreal_of_num_def,extreal_pow_def,extreal_le_def,REAL_LT_IMP_LE,POW_POS,REAL_LE_DIV]
      >> CONJ_TAC
      >- (RW_TAC real_ss [DISJOINT_DEF,IN_COUNT,IN_INTER,EXTENSION,GSPECIFICATION]
         >| [Reverse EQ_TAC
             >- RW_TAC std_ss [NOT_IN_EMPTY]
                >> RW_TAC real_ss []
             >> RW_TAC std_ss [NOT_IN_EMPTY]
             >> Cases_on `i<j`
             >- (`i + 1 <= j` by RW_TAC real_ss []
                 >> `&(i + 1) / 2:real pow n <= &j / 2 pow n` by RW_TAC real_ss [REAL_LE_RDIV_EQ,REAL_POW_LT,REAL_DIV_RMUL,REAL_POS_NZ]
                 >> `&(i + 1) / 2 pow n <= &j / 2 pow n` by RW_TAC std_ss [extreal_of_num_def,extreal_add_def,extreal_pow_def,extreal_div_eq,extreal_lt_eq,extreal_le_def]
                 >> `&j / 2 pow n <= f x` by METIS_TAC []
                 >> `(&i + 1) = &(i + 1)` by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
                 >> METIS_TAC [lte_trans,extreal_lt_def])
             >> `j < i` by RW_TAC real_ss [LESS_OR_EQ]
             >> `j + 1 <= i` by RW_TAC real_ss []
             >> `&(j + 1) / 2 pow n <= &i / 2:real pow n` by RW_TAC real_ss [REAL_LE_RDIV_EQ,REAL_POW_LT,REAL_DIV_RMUL,REAL_POS_NZ]
             >> `&(j + 1) / 2 pow n <= &i / 2 pow n` by RW_TAC std_ss [extreal_of_num_def,extreal_add_def,extreal_pow_def,extreal_div_eq,extreal_lt_eq,extreal_le_def]
             >> `(&j + 1) = &(j + 1)` by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
             >> METIS_TAC [lte_trans,extreal_lt_def],

             Reverse EQ_TAC >- RW_TAC std_ss [NOT_IN_EMPTY]
             >> RW_TAC std_ss []
             >> RW_TAC real_ss [NOT_IN_EMPTY]
             >> `&(i + 1) <= &(4 ** n):real` by RW_TAC real_ss []
             >> FULL_SIMP_TAC std_ss [GSYM REAL_OF_NUM_POW]
              >> `&(i + 1) / 2 pow n <= 4 pow n / 2:real pow n` by RW_TAC real_ss [REAL_LE_RDIV_EQ,REAL_POW_LT,REAL_DIV_RMUL,REAL_POS_NZ]
              >> `&(i + 1) / 2 pow n <= 2:real pow n` by METIS_TAC [REAL_POW_DIV,EVAL ``4/2:real``]
              >> `&(i + 1) / 2 pow n <= 2 pow n` by RW_TAC std_ss [extreal_of_num_def,extreal_add_def,extreal_pow_def,extreal_div_eq,extreal_lt_eq,extreal_le_def]
             >> `(&i + 1) = &(i + 1)` by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
             >> METIS_TAC [le_trans,extreal_lt_def],

             Reverse EQ_TAC >- RW_TAC std_ss [NOT_IN_EMPTY]
             >> RW_TAC real_ss []
             >> RW_TAC std_ss [NOT_IN_EMPTY]
             >> `&(j + 1) <= &(4 ** n):real` by RW_TAC real_ss []
             >> FULL_SIMP_TAC std_ss [GSYM REAL_OF_NUM_POW]
              >> `&(j + 1) / 2 pow n <= 4:real pow n / 2 pow n` by RW_TAC real_ss [REAL_LE_RDIV_EQ,REAL_POW_LT,REAL_DIV_RMUL,REAL_POS_NZ]
              >> `&(j + 1) / 2 pow n <= 2:real pow n` by  METIS_TAC [REAL_POW_DIV,EVAL ``4/2:real``]
              >> `&(j + 1) / 2 pow n <= 2 pow n` by RW_TAC std_ss [extreal_of_num_def,extreal_add_def,extreal_pow_def,extreal_div_eq,extreal_lt_eq,extreal_le_def]
             >> `(&j + 1) = &(j + 1)` by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
             >> METIS_TAC [lte_trans,extreal_lt_def]])
     >> RW_TAC std_ss [EXTENSION,IN_BIGUNION_IMAGE,GSPECIFICATION]
     >> EQ_TAC
     >- (RW_TAC std_ss []
         >> Cases_on `k IN count (4 ** n)`
         >- FULL_SIMP_TAC std_ss [GSPECIFICATION,lemma_fn_3]
         >> FULL_SIMP_TAC std_ss [GSPECIFICATION,lemma_fn_3])
     >> RW_TAC real_ss [IN_COUNT]
     >> `2 pow n <= f x \/ ?k. k IN count (4 ** n) /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n` by METIS_TAC [lemma_fn_3]
     >- (Q.EXISTS_TAC `4 ** n`
         >> RW_TAC real_ss [GSPECIFICATION])
     >> Q.EXISTS_TAC `k`
     >> FULL_SIMP_TAC real_ss [IN_COUNT,GSPECIFICATION]
     >> METIS_TAC [])
  >> RW_TAC real_ss [pos_simple_fn_integral_def,fn_seq_integral_def]
  >> `4 ** n + 1 = SUC (4 ** n)` by RW_TAC real_ss []
  >> ASM_SIMP_TAC std_ss []
  >> RW_TAC std_ss [COUNT_SUC,IN_COUNT]
  >> `(\i. Normal (if i < 4 ** n then &i / 2 pow n else 2 pow n) *
                   measure m (if i < 4 ** n then
                   {x | x IN m_space m /\ Normal (&i / 2 pow n) <= f x /\ f x < (&i + 1) / 2 pow n}
                   else {x | x IN m_space m /\ 2 pow n <= f x})) =
              (\i. if i < 4 ** n then &i / 2 pow n  *
                   measure m {x | x IN m_space m /\ &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n}
                   else 2 pow n * measure m {x | x IN m_space m /\ 2 pow n <= f x})`
                by (RW_TAC std_ss [FUN_EQ_THM]
                    >> Cases_on `i < 4 ** n` >- RW_TAC std_ss []
                    >> RW_TAC std_ss [extreal_of_num_def,extreal_pow_def])
  >> POP_ORW
  >> (MP_TAC o Q.SPEC `4 ** n` o UNDISCH o Q.SPECL [`(\i. if i < 4 ** n then &i / 2 pow n * measure m {x | x IN m_space m /\ &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n}
         else 2 pow n * measure m {x | x IN m_space m /\ 2 pow n <= f x})`,`count (4 ** n)`] o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_PROPERTY
  >> `!x. (\i. if i < 4 ** n then &i / 2 pow n * measure m {x | x IN m_space m /\ &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n}
           else 2 pow n * measure m {x | x IN m_space m /\ 2 pow n <= f x}) x <> NegInf`
             by (RW_TAC std_ss []
                   >- (`0 <= &x / 2:real pow n` by RW_TAC real_ss [REAL_LE_DIV,REAL_LT_IMP_LE]
                       >> Suff `measure m {x' | x' IN m_space m /\ Normal (&x / 2 pow n) <= f x' /\ f x' < (&x + 1) / 2 pow n} <> NegInf`
                       >- METIS_TAC [mul_not_infty]
                       >> Suff `{x' | x' IN m_space m /\ Normal (&x / 2 pow n) <= f x' /\ f x' < (&x + 1) / 2 pow n} IN measurable_sets m`
                       >- METIS_TAC [positive_not_infty,MEASURE_SPACE_POSITIVE]
                       >> `{x' | x' IN m_space m /\ Normal (&x / 2 pow n) <= f x' /\ f x' < (&x + 1) / 2 pow n} =
                           {x' | Normal (&x / 2 pow n) <= f x' /\ f x' < (&x + 1) / 2 pow n} INTER m_space m`
                             by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER] >> METIS_TAC [])
                       >> `!x. &x + 1 =  &(x + 1)` by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
                       >> METIS_TAC [IN_MEASURABLE_BOREL_ALL, measurable_sets_def,subsets_def,space_def,m_space_def])
                   >> RW_TAC std_ss [extreal_of_num_def,extreal_pow_def]
                   >> `0:real <= 2 pow n` by FULL_SIMP_TAC std_ss [REAL_LT_IMP_LE]
                   >> Suff `{x | x IN m_space m /\ Normal (2 pow n) <= f x} IN measurable_sets m`
                   >- METIS_TAC [mul_not_infty,positive_not_infty,MEASURE_SPACE_POSITIVE]
                   >> `{x | x IN m_space m /\ Normal (2 pow n) <= f x} = {x | Normal (2 pow n) <= f x} INTER m_space m`
                         by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER] >> METIS_TAC [])
                   >> METIS_TAC [IN_MEASURABLE_BOREL_ALL, measurable_sets_def,subsets_def,space_def,m_space_def])
  >> RW_TAC std_ss []
  >> `count (4 ** n) DELETE 4 ** n = count (4 ** n)`
             by METIS_TAC [DELETE_NON_ELEMENT,IN_COUNT,LESS_EQ_REFL,NOT_LESS]
  >> RW_TAC std_ss []
  >> Q.PAT_X_ASSUM `SIGMA f s = Q` (K ALL_TAC)
  >> FULL_SIMP_TAC std_ss [GSYM IN_COUNT]
  >> `!i. (\i. Normal (&i / 2 pow n) * measure m {x | x IN m_space m /\ Normal (&i / 2 pow n) <= f x /\ f x < (&i + 1) / 2 pow n}) i <> NegInf`
        by (RW_TAC std_ss []
            >> `0 <= &i / 2:real pow n` by RW_TAC real_ss [REAL_LE_DIV,REAL_LT_IMP_LE]
            >> Suff `{x | x IN m_space m /\ Normal (&i / 2 pow n) <= f x /\ f x < (&i + 1) / 2 pow n} IN measurable_sets m`
            >- METIS_TAC [mul_not_infty,positive_not_infty,MEASURE_SPACE_POSITIVE]
            >> `{x | x IN m_space m /\ Normal (&i / 2 pow n) <= f x /\ f x < (&i + 1) / 2 pow n} =
                {x | Normal (&i / 2 pow n) <= f x /\ f x < (&i + 1) / 2 pow n} INTER m_space m`
                    by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER] >> METIS_TAC [])
            >> `!x. &x + 1 =  &(x + 1)` by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
            >> METIS_TAC [IN_MEASURABLE_BOREL_ALL, measurable_sets_def,subsets_def,space_def,m_space_def])
  >> (MP_TAC o Q.SPECL [`count (4 ** n)`,`(\k. &k / 2 pow n * measure m {x | x IN m_space m /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n})`,` 2 pow n * measure m {x | x IN m_space m /\ 2 pow n <= f x}`] o INST_TYPE [alpha |-> ``:num``] o GSYM) EXTREAL_SUM_IMAGE_IN_IF_ALT
  >> RW_TAC std_ss []
  >> FULL_SIMP_TAC std_ss []
  >> MATCH_MP_TAC add_comm
  >> DISJ1_TAC
  >> Reverse CONJ_TAC
  >- (RW_TAC std_ss [extreal_of_num_def,extreal_pow_def]
      >> `0:real <= 2 pow n` by FULL_SIMP_TAC std_ss [REAL_LT_IMP_LE]
      >> Suff `{x | x IN m_space m /\ Normal (2 pow n) <= f x} IN measurable_sets m`
      >- METIS_TAC [mul_not_infty,positive_not_infty,MEASURE_SPACE_POSITIVE]
      >> `{x | x IN m_space m /\ Normal (2 pow n) <= f x} = {x | Normal (2 pow n) <= f x} INTER m_space m`
            by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER] >> METIS_TAC [])
      >> METIS_TAC [IN_MEASURABLE_BOREL_ALL, measurable_sets_def,subsets_def,space_def,m_space_def])
  >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY]);


(*****************************************************************)

val integral_sequence = store_thm
  ("integral_sequence",
  ``!m f.  (!x. 0 <= f x) /\ measure_space m /\
           f IN measurable (m_space m,measurable_sets m) Borel
       ==> (pos_fn_integral m f = sup (IMAGE (\i. pos_fn_integral m (fn_seq m f i)) UNIV))``,
  RW_TAC std_ss []
  >> MATCH_MP_TAC lebesgue_monotone_convergence
  >> RW_TAC std_ss [lemma_fn_sup,lemma_fn_mono_increasing,lemma_fn_upper_bounded,lemma_fn_5]
  >> METIS_TAC [lemma_fn_in_psfis,IN_MEASURABLE_BOREL_POS_SIMPLE_FN,IN_psfis_eq]);

val measurable_sequence = store_thm
  ("measurable_sequence",
  ``!m f. measure_space m /\ f IN measurable (m_space m,measurable_sets m) Borel ==>
        (?fi ri. (!x. mono_increasing (\i. fi i x)) /\
        (!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = fn_plus f x)) /\
        (!i. ri i IN psfis m (fi i)) /\
        (!i x. fi i x <= fn_plus f x) /\
        (!i x. 0 <= fi i x) /\
        (pos_fn_integral m (fn_plus f) = sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV))) /\
        (?gi vi. (!x. mono_increasing (\i. gi i x)) /\
        (!x. x IN m_space m ==> (sup (IMAGE (\i. gi i x) UNIV) = fn_minus f x)) /\
        (!i. vi i IN psfis m (gi i)) /\
        (!i x. (gi i) x <= fn_minus f x) /\
        (!i x. 0 <= gi i x) /\
        (pos_fn_integral m (fn_minus f) = sup (IMAGE (\i. pos_fn_integral m (gi i)) UNIV)))``,
  rpt STRIP_TAC
  >- (Q.EXISTS_TAC `(\n. fn_seq m (fn_plus f) n)`
      >> Q.EXISTS_TAC `(\n. fn_seq_integral m (fn_plus f) n)`
      >> CONJ_TAC
      >- RW_TAC std_ss [FN_PLUS_POS,lemma_fn_mono_increasing]
      >> CONJ_TAC
      >- RW_TAC std_ss [FN_PLUS_POS,lemma_fn_sup]
      >> CONJ_TAC
      >- FULL_SIMP_TAC std_ss [FN_PLUS_POS,lemma_fn_in_psfis,IN_MEASURABLE_BOREL_FN_PLUS]
      >> CONJ_TAC
      >- METIS_TAC [FN_PLUS_POS,lemma_fn_upper_bounded]
      >> CONJ_TAC
      >- METIS_TAC [FN_PLUS_POS,lemma_fn_5]
      >> METIS_TAC [FN_PLUS_POS,integral_sequence,IN_MEASURABLE_BOREL_FN_PLUS])
  >> Q.EXISTS_TAC `(\n. fn_seq m (fn_minus f) n)`
  >> Q.EXISTS_TAC `(\n. fn_seq_integral m (fn_minus f) n)`
  >> CONJ_TAC
  >- RW_TAC std_ss [FN_MINUS_POS,lemma_fn_mono_increasing]
  >> CONJ_TAC
  >- RW_TAC std_ss [FN_MINUS_POS,lemma_fn_sup]
  >> CONJ_TAC
  >- FULL_SIMP_TAC std_ss [FN_MINUS_POS,lemma_fn_in_psfis,IN_MEASURABLE_BOREL_FN_MINUS]
  >> CONJ_TAC
  >- METIS_TAC [FN_MINUS_POS,lemma_fn_upper_bounded]
  >> CONJ_TAC
  >- METIS_TAC [FN_MINUS_POS,lemma_fn_5]
  >> METIS_TAC [FN_MINUS_POS,integral_sequence,IN_MEASURABLE_BOREL_FN_MINUS]);

val pos_fn_integral_add = store_thm
  ("pos_fn_integral_add",
  ``!m f g. measure_space m /\ (!x. 0 <= f x /\ 0 <= g x) /\
            f IN measurable (m_space m,measurable_sets m) Borel /\
            g IN measurable (m_space m,measurable_sets m) Borel  ==>
            (pos_fn_integral m (\x. f x + g x) = pos_fn_integral m f + pos_fn_integral m g)``,
    RW_TAC std_ss []
 >> `?fi ui.
       (!x. mono_increasing (\i. fi i x)) /\
       (!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = f x)) /\
       (!i. ui i IN psfis m (fi i)) /\
       (!i x. fi i x <= f x) /\
       (!i x. 0 <= fi i x) /\
       (pos_fn_integral m f = sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV))`
            by METIS_TAC [measurable_sequence,FN_PLUS_POS_ID]
 >> `?gi vi.
       (!x. mono_increasing (\i. gi i x)) /\
       (!x. x IN m_space m ==> (sup (IMAGE (\i. gi i x) UNIV) = g x)) /\
       (!i. vi i IN psfis m (gi i)) /\
       (!i x. gi i x <= g x) /\
       (!i x. 0 <= gi i x) /\
       (pos_fn_integral m g = sup (IMAGE (\i. pos_fn_integral m (gi i)) UNIV))`
            by METIS_TAC [measurable_sequence,FN_PLUS_POS_ID]
 >> `sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV) +
     sup (IMAGE (\i. pos_fn_integral m (gi i)) UNIV) =
     sup (IMAGE (\i. (\n. pos_fn_integral m (fi n)) i + (\n. pos_fn_integral m (gi n)) i) UNIV)`
       by (MATCH_MP_TAC (GSYM sup_add_mono) \\
           FULL_SIMP_TAC std_ss [pos_fn_integral_pos, ext_mono_increasing_suc, pos_fn_integral_mono])
 >> FULL_SIMP_TAC std_ss []
 >> `!i. (\x. fi i x + gi i x) IN  measurable (m_space m,measurable_sets m) Borel`
       by METIS_TAC [IN_MEASURABLE_BOREL_POS_SIMPLE_FN, IN_psfis_eq, psfis_add]
 >> `!x. mono_increasing (\i. (\i x. fi i x + gi i x) i x)`
       by FULL_SIMP_TAC std_ss [ext_mono_increasing_def, le_add2]
 >> `!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x + gi i x) UNIV) = f x + g x)`
       by (RW_TAC std_ss []
           >> `f x = sup (IMAGE (\i. fi i x) UNIV)` by FULL_SIMP_TAC std_ss []
           >> `g x = sup (IMAGE (\i. gi i x) UNIV)` by FULL_SIMP_TAC std_ss []
           >> POP_ORW >> POP_ORW
           >> FULL_SIMP_TAC std_ss [pos_fn_integral_pos, sup_add_mono,
                                    ext_mono_increasing_suc, pos_fn_integral_mono])
 >> (MP_TAC o Q.SPECL [`m`, `\x. f x + g x`, `\i. (\x. fi i x + gi i x)`])
       lebesgue_monotone_convergence
 >> RW_TAC std_ss []
 >> Suff `(\i. pos_fn_integral m (fi i) + pos_fn_integral m (gi i)) =
          (\i. pos_fn_integral m (\x. fi i x + gi i x))`
 >- RW_TAC std_ss [le_add]
 >> RW_TAC std_ss [FUN_EQ_THM]
 >> METIS_TAC [IN_psfis_eq, psfis_add, pos_fn_integral_pos_simple_fn]);

val pos_fn_integral_sum = store_thm
  ("pos_fn_integral_sum",``!m f s. FINITE s /\ measure_space m /\
                           (!i. i IN s ==> (!x. 0 <= f i x)) /\
        (!i. i IN s ==> f i IN measurable (m_space m,measurable_sets m) Borel)
            ==> (pos_fn_integral m (\x. SIGMA (\i. (f i) x) s) =
                 SIGMA (\i. pos_fn_integral m (f i)) s)``,
    Suff `!s:'b->bool.
            FINITE s ==>
              (\s:'b->bool. !m f. measure_space m /\ (!i. i IN s ==> (!x. 0 <= f i x)) /\
                            (!i. i IN s ==> f i IN measurable (m_space m,measurable_sets m) Borel)
                        ==> (pos_fn_integral m (\x. SIGMA (\i. (f i) x) s) =
                             SIGMA (\i. pos_fn_integral m (f i)) s)) s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY,pos_fn_integral_zero]
 >> `!x. SIGMA (\i. f i x) (e INSERT s) = f e x + SIGMA (\i. f i x) s`
      by (RW_TAC std_ss [] \\
          (MP_TAC o Q.SPEC `e` o UNDISCH o Q.SPECL [`(\i. f i x)`,`s`] o
           INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY \\
         `!i. i IN e INSERT s ==> (\i. f i x) i <> NegInf`
              by (RW_TAC std_ss [] \\
                  METIS_TAC [lt_infty, extreal_of_num_def, extreal_not_infty, lte_trans]) \\
          FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT])
 >> RW_TAC std_ss []
 >> `!i. i IN e INSERT s ==> (\i. pos_fn_integral m (f i)) i <> NegInf`
      by (RW_TAC std_ss [] \\
          METIS_TAC [lt_infty, extreal_of_num_def, extreal_not_infty, lte_trans, pos_fn_integral_pos])
 >> (MP_TAC o Q.SPEC `e` o UNDISCH o Q.SPECL [`(\i. pos_fn_integral m (f i))`,`s`] o
     INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY
 >> RW_TAC std_ss []
 >> `SIGMA (\i. pos_fn_integral m (f i)) s = pos_fn_integral m (\x. SIGMA (\i. f i x) s)`
      by METIS_TAC [IN_INSERT]
 >> FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
 >> `(\x. f e x + SIGMA (\i. f i x) s) = (\x. f e x + (\x. SIGMA (\i. f i x) s) x)` by METIS_TAC []
 >> POP_ORW
 >> MATCH_MP_TAC pos_fn_integral_add
 >> FULL_SIMP_TAC std_ss [IN_INSERT]
 >> RW_TAC std_ss []
 >- FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_POS]
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_SUM
 >> Q.EXISTS_TAC `f` >> Q.EXISTS_TAC `s`
 >> METIS_TAC [measure_space_def, measurable_sets_def, subsets_def, m_space_def, space_def,
               extreal_of_num_def, extreal_not_infty, lt_infty, lte_trans]);

val pos_fn_integral_disjoint_sets = store_thm
  ("pos_fn_integral_disjoint_sets",
  ``!m f s t. measure_space m /\
              DISJOINT s t /\ s IN measurable_sets m /\ t IN measurable_sets m /\
              f IN measurable (m_space m,measurable_sets m) Borel /\ (!x. 0 <= f x)
         ==> (pos_fn_integral m (\x. f x * indicator_fn (s UNION t) x) =
              pos_fn_integral m (\x. f x * indicator_fn s x) +
              pos_fn_integral m (\x. f x * indicator_fn t x))``,
 (* proof *)
    RW_TAC std_ss []
 >> `(\x. f x * indicator_fn (s UNION t) x) =
     (\x. (\x. f x * indicator_fn s x) x + (\x. f x * indicator_fn t x) x)`
       by (RW_TAC std_ss [FUN_EQ_THM, indicator_fn_def, IN_DISJOINT, IN_UNION, mul_rone, mul_rzero]
           >> Cases_on `x IN s`
           >- (RW_TAC std_ss [mul_rone, mul_rzero, add_rzero] >> METIS_TAC [EXTENSION, IN_DISJOINT])
           >> RW_TAC std_ss [mul_rone, mul_rzero, add_lzero])
 >> POP_ORW
 >> `!s. s IN measurable_sets m ==>
        (\x. f x * indicator_fn s x) IN measurable (m_space m,measurable_sets m) Borel`
      by METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR,measure_space_def,subsets_def,space_def]
 >> MATCH_MP_TAC pos_fn_integral_add
 >> FULL_SIMP_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
 >> RW_TAC std_ss [le_refl,mul_rzero,mul_rone]);

val pos_fn_integral_disjoint_sets_sum = store_thm
  ("pos_fn_integral_disjoint_sets_sum",
  ``!m f s a. FINITE s /\ measure_space m /\
        (!i. i IN s ==> a i IN measurable_sets m) /\ (!x. 0 <= f x) /\
        (!i j. i IN s /\ j IN s /\ i <> j ==> DISJOINT (a i) (a j)) /\
        f IN measurable (m_space m,measurable_sets m) Borel
        ==> (pos_fn_integral m (\x. f x * indicator_fn (BIGUNION (IMAGE a s)) x) =
             SIGMA (\i. pos_fn_integral m (\x. f x * indicator_fn (a i) x)) s)``,
 (* proof *)
    Suff `!s:'b->bool.
            FINITE s ==>
              (\s:'b->bool. !m f a. measure_space m /\
                           (!i. i IN s ==> a i IN measurable_sets m) /\ (!x. 0 <= f x) /\
                           (!i j. i IN s /\ j IN s /\ i <> j ==> DISJOINT (a i) (a j)) /\
                            f IN measurable (m_space m,measurable_sets m) Borel
                       ==> (pos_fn_integral m (\x. f x * indicator_fn (BIGUNION (IMAGE a s)) x) =
                            SIGMA (\i. pos_fn_integral m (\x. f x * indicator_fn (a i) x)) s)) s`
 >- RW_TAC std_ss []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, IMAGE_EMPTY, BIGUNION_EMPTY, FINITE_INSERT,
                   DELETE_NON_ELEMENT, IN_INSERT, BIGUNION_INSERT, IMAGE_INSERT]
 >- RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,NOT_IN_EMPTY,pos_fn_integral_zero]
 >> (MP_TAC o Q.SPEC `e` o UNDISCH o
     Q.SPECL [`(\i. pos_fn_integral m (\x. f x * indicator_fn (a i) x))`, `s`] o
     INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY
 >> `!x. (\i. pos_fn_integral m (\x. f x * indicator_fn (a i) x)) x <> NegInf`
       by (RW_TAC std_ss []
           >> Suff `0 <= pos_fn_integral m (\x'. f x' * indicator_fn (a x) x')`
           >- METIS_TAC [lt_infty, extreal_not_infty, extreal_of_num_def, lte_trans]
           >> MATCH_MP_TAC pos_fn_integral_pos
           >> RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, le_refl])
 >> RW_TAC std_ss []
 >> `~(e IN s)` by METIS_TAC [DELETE_NON_ELEMENT]
 >> `DISJOINT (a e) (BIGUNION (IMAGE a s))`
       by (RW_TAC std_ss [DISJOINT_BIGUNION, IN_IMAGE] >> METIS_TAC [])
 >> `countable (IMAGE a s)` by METIS_TAC [image_countable, finite_countable]
 >> `(IMAGE a s) SUBSET measurable_sets m`
       by (RW_TAC std_ss [SUBSET_DEF, IMAGE_DEF, GSPECIFICATION]
           >> METIS_TAC [])
 >> `BIGUNION (IMAGE a s) IN measurable_sets m`
       by METIS_TAC [sigma_algebra_def, measure_space_def, subsets_def, measurable_sets_def]
 >> METIS_TAC [pos_fn_integral_disjoint_sets]);

val pos_fn_integral_split = store_thm
  ("pos_fn_integral_split",
  ``!m f s. measure_space m /\ s IN measurable_sets m /\
           (!x. 0 <= f x) /\ f IN measurable (m_space m,measurable_sets m) Borel ==>
           (pos_fn_integral m f = pos_fn_integral m (\x. f x * indicator_fn s x) +
                                  pos_fn_integral m (\x. f x * indicator_fn (m_space m DIFF s) x))``,
  RW_TAC std_ss []
  >> (MP_TAC o Q.SPECL [`m`,`f`,`s`,`m_space m DIFF s`]) pos_fn_integral_disjoint_sets
  >> RW_TAC std_ss [DISJOINT_DIFF,MEASURE_SPACE_DIFF,MEASURE_SPACE_MSPACE_MEASURABLE]
  >> `s UNION (m_space m DIFF s) = m_space m` by METIS_TAC [UNION_DIFF,MEASURE_SPACE_SUBSET_MSPACE]
  >> METIS_TAC [pos_fn_integral_mspace]);

val pos_fn_integral_cmul_infty = store_thm
  ("pos_fn_integral_cmul_infty",
  ``!m s. measure_space m /\ s IN measurable_sets m ==>
         (pos_fn_integral m (\x. PosInf * indicator_fn s x) = PosInf * (measure m s))``,
  RW_TAC std_ss []
  >> Q.ABBREV_TAC `fi = (\i:num x. &i)`
  >> Q.ABBREV_TAC `f = (\x. PosInf)`
  >> `!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = f x)`
       by (RW_TAC std_ss []
           >> Q.UNABBREV_TAC `fi`
           >> Q.UNABBREV_TAC `f`
           >> RW_TAC std_ss []
           >> Suff `IMAGE (\i. &i) univ(:num) = (\x. ?n. x = &n)`
           >- RW_TAC std_ss [sup_num]
           >> RW_TAC std_ss [EXTENSION,IN_IMAGE,IN_ABS,IN_UNIV])
  >> `!x. mono_increasing (\i. fi i x)`
       by (RW_TAC std_ss [ext_mono_increasing_def]
           >> Q.UNABBREV_TAC `fi`
           >> RW_TAC real_ss [extreal_of_num_def,extreal_le_def])
  >> `!i x. 0 <= fi i x` by (Q.UNABBREV_TAC `fi` \\
                             RW_TAC real_ss [extreal_of_num_def,extreal_le_def])
  >> `!x. 0 <= f x` by METIS_TAC [le_infty]
  >> `!i. fi i IN measurable (m_space m, measurable_sets m) Borel`
       by (RW_TAC std_ss []
           >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST
           >> METIS_TAC [measure_space_def])
  >> (MP_TAC o Q.SPECL [`m`,`f`,`fi`,`s`]) lebesgue_monotone_convergence_subset
  >> RW_TAC std_ss []
  >> Q.UNABBREV_TAC `f`
  >> Q.UNABBREV_TAC `fi`
  >> FULL_SIMP_TAC real_ss []
  >> RW_TAC real_ss [extreal_of_num_def,pos_fn_integral_cmul_indicator]
  >> RW_TAC std_ss [Once mul_comm]
  >> `0 <= measure m s` by METIS_TAC [MEASURE_SPACE_POSITIVE,positive_def]
  (* sup (IMAGE (\i. measure m s * Normal (&i)) UNIV (:num)) = PosInf * measure m s *)
  >> Know `!n. 0 <= Normal (&n)`
  >- (GEN_TAC >> `0 = Normal (&0)` by REWRITE_TAC [extreal_of_num_def] >> POP_ORW \\
      REWRITE_TAC [extreal_le_def] >> RW_TAC real_ss []) >> DISCH_TAC
  >> RW_TAC std_ss [sup_cmul_pos]
  >> Suff `sup (IMAGE (\i. Normal (&i)) UNIV) = PosInf`
  >- METIS_TAC [mul_comm]
  >> Suff `IMAGE (\i:num. Normal (&i)) UNIV = (\x. ?n. x = &n)`
  >- RW_TAC std_ss [sup_num]
  >> RW_TAC std_ss [EXTENSION,IN_IMAGE,IN_ABS,IN_UNIV]
  >> METIS_TAC [extreal_of_num_def]);

(* Corollary 9.9 of [1, p.77] *)
Theorem pos_fn_integral_suminf :
    !m f. measure_space m /\ (!i x. 0 <= f i x) /\
         (!i. f i IN measurable (m_space m,measurable_sets m) Borel) ==>
         (pos_fn_integral m (\x. suminf (\i. f i x)) =
          suminf (\i. pos_fn_integral m (f i)))
Proof
    rpt STRIP_TAC
 >> Know `!n. 0 <= (\i. pos_fn_integral m (f i)) n`
 >- (RW_TAC std_ss [] \\
     MATCH_MP_TAC pos_fn_integral_pos >> art [])
 >> DISCH_THEN (MP_TAC o (MATCH_MP ext_suminf_alt_pos)) >> Rewr'
 >> Know `!x. suminf (\i. f i x) =
              sup (IMAGE (\n. SIGMA (\i. f i x) (count n)) univ(:num))`
 >- (GEN_TAC >> MATCH_MP_TAC ext_suminf_alt_pos \\
     RW_TAC std_ss []) >> Rewr'
 >> Know `!n. SIGMA (\i. pos_fn_integral m (f i)) (count n) =
              pos_fn_integral m (\x. SIGMA (\i. f i x) (count n))`
 >- (GEN_TAC >> MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC pos_fn_integral_sum >> rw [FINITE_COUNT]) >> Rewr'
 >> `(\n. pos_fn_integral m (\x. SIGMA (\i. f i x) (count n))) =
     (\n. pos_fn_integral m ((\n. (\x. SIGMA (\i. f i x) (count n))) n))`
      by METIS_TAC [] >> POP_ORW
 >> MATCH_MP_TAC lebesgue_monotone_convergence
 >> CONJ_TAC >- RW_TAC std_ss []
 >> CONJ_TAC
 >- (RW_TAC std_ss [] \\
     (MATCH_MP_TAC o INST_TYPE [beta |-> ``:num``]) IN_MEASURABLE_BOREL_SUM \\
      take [`f`, `count i`] \\
      RW_TAC std_ss [FINITE_COUNT]
      >- FULL_SIMP_TAC std_ss [measure_space_def] \\
      METIS_TAC [lt_infty, lte_trans, num_not_infty])
 >> CONJ_TAC >- RW_TAC std_ss [FINITE_COUNT, EXTREAL_SUM_IMAGE_POS]
 >> CONJ_TAC
 >- (RW_TAC std_ss [FINITE_COUNT, EXTREAL_SUM_IMAGE_POS, le_sup',
                    IN_IMAGE, IN_UNIV] \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `SIGMA (\i. f i x) (count 1)` \\
     RW_TAC std_ss [FINITE_COUNT, EXTREAL_SUM_IMAGE_POS] \\
     POP_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC `1` >> REWRITE_TAC [])
 >> RW_TAC std_ss [ext_mono_increasing_def]
 >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
 >> RW_TAC std_ss [FINITE_COUNT, SUBSET_DEF, IN_COUNT]
 >> DECIDE_TAC
QED

(* ------------------------------------------------------------------------- *)
(* Integral for arbitrary functions                                          *)
(* ------------------------------------------------------------------------- *)

(* TODO: use `!x. x IN m_space m ==> 0 <= f x` *)
val integral_pos_fn = store_thm
  ("integral_pos_fn",
  ``!m f. measure_space m /\ (!x. 0 <= f x) ==> (integral m f = pos_fn_integral m f)``,
    RW_TAC std_ss [integral_def]
 >> Suff `(fn_plus f = f) /\ (fn_minus f = (\x. 0))`
 >- RW_TAC std_ss [pos_fn_integral_zero, sub_rzero]
 >> RW_TAC std_ss [FN_PLUS_POS_ID, FN_MINUS_POS_ZERO]);

(* ------------------------------------------------------------------------- *)
(* Properties of integrable functions                                        *)
(* ------------------------------------------------------------------------- *)

val integrable_eq = store_thm (* new *)
  ("integrable_eq",
  ``!m f g. measure_space m /\ integrable m f /\ (!x. x IN (m_space m) ==> (f x = g x))
        ==> integrable m g``,
    RW_TAC std_ss [integrable_def, IN_MEASURABLE, space_def, subsets_def, IN_FUNSET]
 >| [ (* goal 1 (of 4) *)
      PROVE_TAC [],
      (* goal 2 (of 4) *)
      Know `PREIMAGE g s INTER m_space m = PREIMAGE f s INTER m_space m`
      >- (RW_TAC std_ss [EXTENSION, IN_INTER, IN_PREIMAGE] \\
          EQ_TAC >> RW_TAC std_ss [] \\
          PROVE_TAC []) >> Rewr \\
      FIRST_X_ASSUM MATCH_MP_TAC >> art [],
      (* goal 3 (of 4) *)
      Know `pos_fn_integral m (fn_plus g) =
            pos_fn_integral m (\x. (fn_plus g) x * indicator_fn (m_space m) x)`
      >- (MATCH_MP_TAC pos_fn_integral_mspace >> art [] \\
          REWRITE_TAC [FN_PLUS_POS]) >> Rewr \\
      Know `(\x. fn_plus g x * indicator_fn (m_space m) x) =
            (\x. fn_plus f x * indicator_fn (m_space m) x)`
      >- (FUN_EQ_TAC >> GEN_TAC >> BETA_TAC \\
          Cases_on `x IN m_space m`
          >- (ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rone] \\
              SIMP_TAC std_ss [fn_plus_def] >> METIS_TAC []) \\
          ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rzero]) >> Rewr \\
      Know `pos_fn_integral m (\x. fn_plus f x * indicator_fn (m_space m) x) =
            pos_fn_integral m (fn_plus f)`
      >- (MATCH_MP_TAC EQ_SYM \\
          MATCH_MP_TAC pos_fn_integral_mspace >> art [] \\
          REWRITE_TAC [FN_PLUS_POS]) >> Rewr \\
      ASM_REWRITE_TAC [],
      (* goal 4 (of 4) *)
      Know `pos_fn_integral m (fn_minus g) =
            pos_fn_integral m (\x. (fn_minus g) x * indicator_fn (m_space m) x)`
      >- (MATCH_MP_TAC pos_fn_integral_mspace >> art [] \\
          REWRITE_TAC [FN_MINUS_POS]) >> Rewr \\
      Know `(\x. fn_minus g x * indicator_fn (m_space m) x) =
            (\x. fn_minus f x * indicator_fn (m_space m) x)`
      >- (FUN_EQ_TAC >> GEN_TAC >> BETA_TAC \\
          Cases_on `x IN m_space m`
          >- (ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rone] \\
              SIMP_TAC std_ss [fn_minus_def] >> METIS_TAC []) \\
          ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rzero]) >> Rewr \\
      Know `pos_fn_integral m (\x. fn_minus f x * indicator_fn (m_space m) x) =
            pos_fn_integral m (fn_minus f)`
      >- (MATCH_MP_TAC EQ_SYM \\
          MATCH_MP_TAC pos_fn_integral_mspace >> art [] \\
          REWRITE_TAC [FN_MINUS_POS]) >> Rewr \\
      ASM_REWRITE_TAC [] ]);

val integrable_pos = store_thm
  ("integrable_pos",
  ``!m f. measure_space m /\ (!x. 0 <= f x) ==>
         (integrable m f <=> f IN measurable (m_space m,measurable_sets m) Borel /\
                             pos_fn_integral m f <> PosInf)``,
    RW_TAC std_ss [integrable_def, GSYM fn_plus_def, GSYM fn_minus_def,
                   FN_PLUS_POS_ID, FN_MINUS_POS_ZERO, pos_fn_integral_zero, num_not_infty]);

val integrable_infty = store_thm
  ("integrable_infty",
  ``!m f s. measure_space m /\ integrable m f /\ s IN measurable_sets m /\
           (!x. x IN s ==> (f x = PosInf)) ==> (measure m s = 0)``,
  RW_TAC std_ss [integrable_def]
  >> (MP_TAC o Q.SPECL [`m`,`fn_plus f`,`s`]) pos_fn_integral_split
  >> RW_TAC std_ss [IN_MEASURABLE_BOREL_FN_PLUS,DISJOINT_DIFF,FN_PLUS_POS]
  >> `(\x. fn_plus f x * indicator_fn s x) = (\x. PosInf * indicator_fn s x)`
      by (RW_TAC std_ss [FUN_EQ_THM,indicator_fn_def,fn_plus_def,mul_rzero,mul_rone]
          >> METIS_TAC [lt_infty,extreal_mul_def,mul_rone,mul_rzero])
  >> `pos_fn_integral m (\x. PosInf * indicator_fn s x) = PosInf * (measure m s)`
      by METIS_TAC [pos_fn_integral_cmul_infty]
  >> FULL_SIMP_TAC std_ss []
  >> `0 <= pos_fn_integral m (\x. fn_plus f x * indicator_fn (m_space m DIFF s) x)`
      by (MATCH_MP_TAC pos_fn_integral_pos
          >> RW_TAC std_ss [fn_plus_def,indicator_fn_def,mul_rzero,mul_rone,lt_imp_le,le_refl])
  >> SPOSE_NOT_THEN ASSUME_TAC
  >> `0 < measure m s` by METIS_TAC [positive_def, MEASURE_SPACE_POSITIVE, lt_le]
  >> `pos_fn_integral m (\x. fn_plus f x * indicator_fn (m_space m DIFF s) x) <> NegInf`
      by METIS_TAC [lt_infty,lte_trans,num_not_infty]
  >> FULL_SIMP_TAC std_ss [mul_lposinf, lt_imp_ne, add_infty]);

val integrable_infty_null = store_thm
  ("integrable_infty_null",
  ``!m f. measure_space m /\ integrable m f ==>
          null_set m {x | x IN m_space m /\ (f x = PosInf)}``,
  RW_TAC std_ss []
  >> Q.ABBREV_TAC `s = {x | x IN m_space m /\ (f x = PosInf)} `
  >> Suff `s IN measurable_sets m`
  >- (RW_TAC std_ss [null_set_def]
      >> MATCH_MP_TAC integrable_infty
      >> Q.EXISTS_TAC `f`
      >> RW_TAC std_ss []
      >> Q.UNABBREV_TAC `s`
      >> FULL_SIMP_TAC std_ss [GSPECIFICATION])
  >> `f IN measurable (m_space m, measurable_sets m) Borel`
      by FULL_SIMP_TAC std_ss [integrable_def]
  >> (MP_TAC o Q.SPEC `PosInf` o UNDISCH)
      (REWRITE_RULE [subsets_def, space_def, IN_FUNSET, IN_UNIV]
                    (Q.SPECL [`f`,`(m_space m, measurable_sets m)`] IN_MEASURABLE_BOREL_ALT8))
  >> Suff `s = {x | f x = PosInf} INTER m_space m`
  >- METIS_TAC []
  >> Q.UNABBREV_TAC `s`
  >> RW_TAC std_ss [EXTENSION,IN_INTER,GSPECIFICATION]
  >> METIS_TAC []);

(* Corollary 11.6 [1, p.91] (partial)

   TODO: extend it to NegInf, so that f is almost everywhere R-valued.
 *)
val integrable_AE_normal = store_thm
  ("integrable_AE_normal",
  ``!m f. measure_space m /\ integrable m f ==> AE x::m. f x < PosInf``,
    RW_TAC std_ss [AE_ALT]
 >> Q.EXISTS_TAC `{x | x IN m_space m /\ (f x = PosInf)}`
 >> CONJ_TAC >- (MATCH_MP_TAC integrable_infty_null >> art [])
 >> REWRITE_TAC [GSYM lt_infty, SUBSET_REFL]);

val integrable_normal_integral = store_thm (* new *)
  ("integrable_normal_integral",
  ``!m f. measure_space m /\ integrable m f ==> ?r. (integral m f = Normal r)``,
    RW_TAC std_ss [integrable_def, integral_def]
 >> `0 <= pos_fn_integral m (fn_plus f)` by PROVE_TAC [pos_fn_integral_pos, FN_PLUS_POS]
 >> `0 <= pos_fn_integral m (fn_minus f)` by PROVE_TAC [pos_fn_integral_pos, FN_MINUS_POS]
 >> Q.ABBREV_TAC `a = pos_fn_integral m (fn_plus f)`
 >> Q.ABBREV_TAC `b = pos_fn_integral m (fn_minus f)`
 >> `a <> NegInf /\ b <> NegInf` by PROVE_TAC [pos_not_neginf]
 >> Know `a - b <> PosInf /\ a - b <> NegInf`
 >- (Cases_on `a` >> Cases_on `b` >> fs [extreal_sub_def])
 >> STRIP_TAC
 >> METIS_TAC [extreal_cases]);

(* Updated with ``!x. x IN m_space m ==> (abs (g x) <= f x)`` *)
val integrable_bounded = store_thm
  ("integrable_bounded",
  ``!m f g. measure_space m /\ integrable m f /\
            g IN measurable (m_space m,measurable_sets m) Borel /\
            (!x. x IN m_space m ==> (abs (g x) <= f x))
        ==> integrable m g``,
    RW_TAC std_ss [integrable_def, abs_bounds, GSYM fn_plus_def, GSYM fn_minus_def]
 >- (`!x. x IN m_space m ==> fn_plus g x <= fn_plus f x`
       by (RW_TAC real_ss [fn_plus_def, lt_imp_le, le_refl] \\
           METIS_TAC [extreal_lt_def, lte_trans]) \\
     METIS_TAC [pos_fn_integral_mono_mspace, FN_PLUS_POS, lt_infty, let_trans])
 >> `!x. x IN m_space m ==> fn_minus g x <= fn_plus f x`
        by (RW_TAC real_ss [fn_minus_def, fn_plus_def, lt_imp_le, le_refl] \\
            METIS_TAC [let_trans, lt_neg, le_neg, neg_neg, neg_0])
 >> METIS_TAC [pos_fn_integral_mono_mspace, FN_PLUS_POS, FN_MINUS_POS, lt_infty, let_trans]);

val integrable_fn_plus = store_thm
  ("integrable_fn_plus",
  ``!m f. measure_space m /\ integrable m f ==> integrable m (fn_plus f)``,
    RW_TAC std_ss [integrable_def, GSYM fn_plus_def, FN_PLUS_POS, FN_PLUS_POS_ID,
                   IN_MEASURABLE_BOREL_FN_PLUS, GSYM fn_minus_def, FN_MINUS_POS_ZERO,
                   pos_fn_integral_zero, num_not_infty]
 >> METIS_TAC []);

val integrable_fn_minus = store_thm
  ("integrable_fn_minus",
  ``!m f. measure_space m /\ integrable m f ==> integrable m (fn_minus f)``,
    RW_TAC std_ss [integrable_def, GSYM fn_minus_def, FN_MINUS_POS, FN_PLUS_POS_ID,
                   IN_MEASURABLE_BOREL_FN_MINUS, GSYM fn_plus_def, FN_MINUS_POS_ZERO,
                   pos_fn_integral_zero, num_not_infty]
 >> METIS_TAC []);

(* added `measure m (m_space m) < PosInf` into antecedents, otherwise not true *)
val integrable_const = store_thm
  ("integrable_const",
  ``!m c. measure_space m /\ measure m (m_space m) < PosInf ==> integrable m (\x. Normal c)``,
    RW_TAC std_ss []
 >> `(\x. Normal c) IN measurable (m_space m,measurable_sets m) Borel`
      by (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST >> METIS_TAC [measure_space_def])
 >> RW_TAC real_ss [integrable_def, lt_antisym, pos_fn_integral_zero, fn_plus_def,
                    fn_minus_def, num_not_infty, extreal_ainv_def]
 >| [ (* goal 1 (of 4) *)
      METIS_TAC [lt_antisym],
      (* goal 2 (of 4) *)
      METIS_TAC [lt_antisym],
      (* goal 3 (of 4) *)
     (MP_TAC o Q.SPECL [`m`,`\x. Normal c`]) pos_fn_integral_mspace \\
      RW_TAC std_ss [lt_imp_le] \\
     `0 <= c` by METIS_TAC [REAL_LT_IMP_LE, extreal_of_num_def, extreal_lt_eq] \\
      Know `pos_fn_integral m (\x. Normal c * indicator_fn (m_space m) x) =
            Normal c * measure m (m_space m)`
      >- (MATCH_MP_TAC pos_fn_integral_cmul_indicator \\
          METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE]) >> Rewr' \\
   (* Normal c * measure m (m_space m) <> PosInf *)
      PROVE_TAC [mul_not_infty, lt_infty],
      (* goal 4 (of 4), similar with previous goal *)
     (MP_TAC o Q.SPECL [`m`,`\x. Normal (-c)`]) pos_fn_integral_mspace \\
     `0 < Normal (-c)` by METIS_TAC [lt_neg,neg_0, extreal_ainv_def] \\
      RW_TAC std_ss [lt_imp_le] \\
     `0 <= -c` by METIS_TAC [REAL_LT_IMP_LE, extreal_of_num_def, extreal_lt_eq] \\
      Know `pos_fn_integral m (\x. Normal (-c) * indicator_fn (m_space m) x) =
            Normal (-c) * measure m (m_space m)`
      >- (MATCH_MP_TAC pos_fn_integral_cmul_indicator \\
          METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE]) >> Rewr' \\
   (* Normal (-c) * measure m (m_space m) <> PosInf *)
      PROVE_TAC [mul_not_infty, lt_infty] ]);

val integrable_zero = store_thm
  ("integrable_zero", ``!m c. measure_space m ==> integrable m (\x. 0)``,
    RW_TAC std_ss []
 >> `(\x. 0) IN measurable (m_space m,measurable_sets m) Borel`
      by (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST \\
          METIS_TAC [measure_space_def])
 >> RW_TAC real_ss [integrable_def, fn_plus_def, fn_minus_def, lt_refl, neg_0,
                    pos_fn_integral_zero, num_not_infty]);

(* Theorem 10.3 (i) <-> (ii) [1, p.84] *)
val integrable_plus_minus = store_thm
  ("integrable_plus_minus",
  ``!m f. measure_space m ==>
         (integrable m f <=> f IN measurable (m_space m, measurable_sets m) Borel /\
                             integrable m (fn_plus f) /\ integrable m (fn_minus f))``,
    RW_TAC std_ss [integrable_def, GSYM fn_plus_def, GSYM fn_minus_def]
 >> `fn_plus (fn_minus f) = fn_minus f` by METIS_TAC [FN_MINUS_POS, FN_PLUS_POS_ID]
 >> `fn_minus (fn_minus f) = (\x. 0)` by METIS_TAC [FN_MINUS_POS, FN_MINUS_POS_ZERO]
 >> `fn_plus (fn_plus f) = fn_plus f` by METIS_TAC [FN_PLUS_POS, FN_PLUS_POS_ID]
 >> `fn_minus (fn_plus f) = (\x. 0)` by METIS_TAC [FN_PLUS_POS, FN_MINUS_POS_ZERO]
 >> `(\x. fn_minus f x) = fn_minus f` by METIS_TAC []
 >> `(\x. fn_plus f x) = fn_plus f` by METIS_TAC []
 >> EQ_TAC
 >> RW_TAC std_ss [IN_MEASURABLE_BOREL_FN_PLUS, IN_MEASURABLE_BOREL_FN_MINUS,
                   pos_fn_integral_zero, num_not_infty]);

val integrable_add_pos = store_thm
  ("integrable_add_pos",
  ``!m f g. measure_space m /\ integrable m f /\ integrable m g /\
           (!x. 0 <= f x) /\ (!x. 0 <= g x) ==> integrable m (\x. f x + g x)``,
    RW_TAC std_ss []
 >> `!x. 0 <= (\x. f x + g x) x` by RW_TAC real_ss [le_add]
 >> `f IN measurable (m_space m,measurable_sets m) Borel` by METIS_TAC [integrable_def]
 >> `g IN measurable (m_space m,measurable_sets m) Borel` by METIS_TAC [integrable_def]
 >> Know `(\x. f x + g x) IN measurable (m_space m,measurable_sets m) Borel`
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD \\
     Q.EXISTS_TAC `f` \\
     Q.EXISTS_TAC `g` \\
     fs [measure_space_def] \\
     GEN_TAC >> DISCH_TAC \\
     CONJ_TAC >> (MATCH_MP_TAC pos_not_neginf >> art []))
 >> DISCH_TAC
 >> Suff `pos_fn_integral m (\x. f x + g x) <> PosInf`
 >- FULL_SIMP_TAC std_ss [integrable_pos]
 >> RW_TAC std_ss [pos_fn_integral_add]
 >> METIS_TAC [lt_add2, integrable_pos, lt_infty]);

(* Theorem 10.3 (i) => (iii) [1, p.84] *)
val integrable_abs = store_thm (* new *)
  ("integrable_abs", ``!m f g. measure_space m /\ integrable m f ==> integrable m (abs o f)``,
    RW_TAC std_ss [FN_ABS']
 >> MATCH_MP_TAC integrable_add_pos
 >> ASM_REWRITE_TAC [FN_PLUS_POS, FN_MINUS_POS]
 >> CONJ_TAC >- (MATCH_MP_TAC integrable_fn_plus >> art [])
 >> MATCH_MP_TAC integrable_fn_minus >> art []);

(* Theorem 10.3 (ii) => (iii) [1, p.84] *)
val integrable_abs_bound_exists = prove (
  ``!m u. measure_space m /\ integrable m (abs o u) ==>
          ?w. integrable m w /\ nonneg w /\ !x. abs (u x) <= w x``,
    rpt STRIP_TAC
 >> Q.EXISTS_TAC `abs o u` >> art [nonneg_abs]
 >> RW_TAC std_ss [o_DEF, le_refl]);

(* Theorem 10.3 (i) => (iv) [1, p.84] *)
val integrable_bound_exists = prove (
  ``!m u. measure_space m /\ integrable m u ==>
          ?w. integrable m w /\ nonneg w /\ !x. abs (u x) <= w x``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC integrable_abs_bound_exists >> art []
 >> MATCH_MP_TAC integrable_abs >> art []);

(* Theorem 10.3 (iv) => (i) [1, p.84] *)
val integrable_from_bound_exists = prove (
  ``!m u. measure_space m /\ u IN measurable (m_space m,measurable_sets m) Borel /\
          (?w. integrable m w /\ nonneg w /\ !x. abs (u x) <= w x) ==>
          integrable m u``,
    RW_TAC std_ss [integrable_def, lt_infty] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC nonneg_fn_plus >> fs [] \\
      MATCH_MP_TAC let_trans \\
      Q.EXISTS_TAC `pos_fn_integral m w` >> art [] \\
      MATCH_MP_TAC pos_fn_integral_mono \\
      GEN_TAC >> REWRITE_TAC [FN_PLUS_POS] \\
      MATCH_MP_TAC le_trans \\
      Q.EXISTS_TAC `abs (u x)` >> art [] \\
      REWRITE_TAC [FN_PLUS_LE_ABS],
      (* goal 2 (of 2) *)
      IMP_RES_TAC nonneg_fn_plus >> fs [] \\
      MATCH_MP_TAC let_trans \\
      Q.EXISTS_TAC `pos_fn_integral m w` >> art [] \\
      MATCH_MP_TAC pos_fn_integral_mono \\
      GEN_TAC >> REWRITE_TAC [FN_MINUS_POS] \\
      MATCH_MP_TAC le_trans \\
      Q.EXISTS_TAC `abs (u x)` >> art [] \\
      REWRITE_TAC [FN_MINUS_LE_ABS] ]);

(* Theorem 10.3 (iii) => (i) [1, p.84] *)
val integrable_from_abs = store_thm (* new *)
  ("integrable_from_abs",
  ``!m u. measure_space m /\ u IN measurable (m_space m,measurable_sets m) Borel /\
          integrable m (abs o u) ==> integrable m u``,
    RW_TAC std_ss []
 >> MATCH_MP_TAC integrable_from_bound_exists >> art []
 >> MATCH_MP_TAC integrable_abs_bound_exists >> art []);

val integrable_add_lemma = store_thm
  ("integrable_add_lemma",
  ``!m f g. measure_space m /\ integrable m f /\ integrable m g
        ==> (integrable m (\x. fn_plus f x + fn_plus g x) /\
             integrable m (\x. fn_minus f x + fn_minus g x))``,
    RW_TAC std_ss []
 >> METIS_TAC [integrable_add_pos, integrable_plus_minus, FN_PLUS_POS, FN_MINUS_POS]);

(* added `(!x. x IN m_space m ==> f x <> NegInf /\ g x <> NegInf)`, one way to
   make sure that f + g is defined *)
val integrable_add = store_thm
  ("integrable_add",
  ``!m f g. measure_space m /\ integrable m f /\ integrable m g /\
            (!x. x IN m_space m ==> f x <> NegInf /\ g x <> NegInf)
        ==> integrable m (\x. f x + g x)``,
    RW_TAC std_ss []
 >> Know `(\x. f x + g x) IN measurable (m_space m, measurable_sets m) Borel`
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD \\
     Q.EXISTS_TAC `f` \\
     Q.EXISTS_TAC `g` \\
     RW_TAC std_ss [space_def] \\
     METIS_TAC [measure_space_def, integrable_def])
 >> DISCH_TAC
 >> RW_TAC std_ss [Once integrable_plus_minus]
 >- (MATCH_MP_TAC integrable_bounded
      >> Q.EXISTS_TAC `(\x. fn_plus f x + fn_plus g x)`
      >> RW_TAC std_ss [IN_MEASURABLE_BOREL_FN_PLUS, integrable_add_lemma]
      >> METIS_TAC [abs_refl, FN_PLUS_POS, FN_PLUS_ADD_LE])
 >> MATCH_MP_TAC integrable_bounded
 >> Q.EXISTS_TAC `(\x. fn_minus f x + fn_minus g x)`
 >> RW_TAC std_ss [IN_MEASURABLE_BOREL_FN_MINUS, integrable_add_lemma]
 >> `abs (fn_minus (\x. f x + g x) x) = fn_minus (\x. f x + g x) x`
        by METIS_TAC [abs_refl, FN_MINUS_POS] >> POP_ORW
 >> MATCH_MP_TAC FN_MINUS_ADD_LE
 >> DISJ1_TAC >> METIS_TAC []);

val integrable_cmul = store_thm
  ("integrable_cmul",
  ``!m f c. measure_space m /\ integrable m f ==> integrable m (\x. Normal c * f x)``,
    RW_TAC std_ss []
 >> Cases_on `c = 0`
 >- RW_TAC std_ss [integrable_zero, mul_lzero, GSYM extreal_of_num_def]
 >> `(\x. Normal c * f x) IN measurable (m_space m,measurable_sets m) Borel`
      by (MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
          >> METIS_TAC [measure_space_def,integrable_def])
 >> RW_TAC std_ss [integrable_def, GSYM fn_plus_def, GSYM fn_minus_def]
 >- (Cases_on `0 <= c`
     >- (`fn_plus (\x. Normal c * f x) = (\x. Normal c * fn_plus f x)`
          by METIS_TAC [FN_PLUS_CMUL] \\
         POP_ORW \\
         FULL_SIMP_TAC std_ss [pos_fn_integral_cmul, integrable_def, FN_PLUS_POS,
                               GSYM fn_plus_def] \\
         METIS_TAC [mul_not_infty]) \\
    `c < 0` by METIS_TAC [real_lt] \\
    `fn_plus (\x. Normal c * f x) = (\x. -Normal c * fn_minus f x)`
            by METIS_TAC [FN_PLUS_CMUL, REAL_LT_IMP_LE] \\
     POP_ORW \\
     RW_TAC std_ss [extreal_ainv_def] \\
    `0 <= -c` by METIS_TAC [REAL_LT_NEG, REAL_NEG_0, REAL_LT_IMP_LE] \\
     FULL_SIMP_TAC std_ss [pos_fn_integral_cmul, integrable_def, FN_MINUS_POS,
                           GSYM fn_minus_def] \\
     METIS_TAC [mul_not_infty])
 >> Cases_on `0 <= c`
 >- (`fn_minus (\x. Normal c * f x) = (\x. Normal c * fn_minus f x)`
      by METIS_TAC [FN_MINUS_CMUL] \\
     POP_ORW \\
     FULL_SIMP_TAC std_ss [pos_fn_integral_cmul, integrable_def, FN_MINUS_POS,
                           GSYM fn_minus_def] \\
     METIS_TAC [mul_not_infty])
 >> `c < 0` by METIS_TAC [real_lt]
 >> `fn_minus (\x. Normal c * f x) = (\x. -Normal c * fn_plus f x)`
        by METIS_TAC [FN_MINUS_CMUL, REAL_LT_IMP_LE]
 >> POP_ORW
 >> RW_TAC std_ss [extreal_ainv_def]
 >> `0 <= -c` by METIS_TAC [REAL_LT_IMP_LE, REAL_LE_NEG, REAL_NEG_0]
 >> RW_TAC std_ss [pos_fn_integral_cmul, FN_PLUS_POS]
 >> METIS_TAC [mul_not_infty, integrable_def]);

(* NOTE: added `!x. x IN m_space m ==> f x <> NegInf /\ g x <> PosInf`, one way
   to make sure that `f - g` is defined (i.e. f/g cannot be the same infinites *)
val integrable_sub = store_thm
  ("integrable_sub",
  ``!m f g. measure_space m /\ integrable m f /\ integrable m g /\
            (!x. x IN m_space m ==> f x <> NegInf /\ g x <> PosInf)
        ==> integrable m (\x. f x - g x)``,
    RW_TAC std_ss []
 >> MATCH_MP_TAC integrable_eq
 >> Q.EXISTS_TAC `(\x. f x + (\x. -g x) x)`
 >> CONJ_TAC >- art []
 >> Reverse CONJ_TAC
 >- (RW_TAC std_ss [FUN_EQ_THM] \\
     MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC extreal_sub_add >> DISJ1_TAC >> METIS_TAC [])
 >> MATCH_MP_TAC integrable_add >> art []
 >> Reverse CONJ_TAC
 >- (RW_TAC std_ss [] >> CCONTR_TAC >> fs [] \\
    `g x = PosInf` by PROVE_TAC [neg_neg, extreal_ainv_def] >> RES_TAC)
 >> `(\x. -g x) = (\x. Normal (-1) * g x)`
      by METIS_TAC [FUN_EQ_THM, neg_minus1, extreal_of_num_def, extreal_ainv_def]
 >> POP_ORW
 >> METIS_TAC [integrable_cmul]);

(* added `measure m s < PosInf` *)
val integrable_indicator = store_thm
  ("integrable_indicator",
  ``!m s. measure_space m /\ s IN measurable_sets m /\ measure m s < PosInf ==>
          integrable m (indicator_fn s)``,
    RW_TAC std_ss []
 >> `!x. 0 <= indicator_fn s x` by PROVE_TAC [INDICATOR_FN_POS]
 >> RW_TAC std_ss [integrable_pos, pos_fn_integral_indicator, lt_infty]
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR
 >> METIS_TAC [measure_space_def, subsets_def, space_def]);

val integrable_indicator_pow = store_thm (* new *)
  ("integrable_indicator_pow",
  ``!m s n. measure_space m /\ s IN measurable_sets m /\ measure m s < PosInf /\
            0 < n ==> integrable m (\x. (indicator_fn s x) pow n)``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC integrable_eq
 >> Q.EXISTS_TAC `indicator_fn s`
 >> RW_TAC std_ss [integrable_indicator, indicator_fn_def, one_pow, zero_pow]);

(* this result is used to simplify the definition of `RN_deriv`,

   added `!x. x IN m_space m ==> f x <> NegInf /\ f x <> PosInf`
   *)
val integrable_mul_indicator = store_thm
  ("integrable_mul_indicator",
  ``!m s f. measure_space m /\ s IN measurable_sets m /\ measure m s < PosInf /\
            (!x. x IN m_space m ==> f x <> NegInf /\ f x <> PosInf) /\
            integrable m f ==> integrable m (\x. f x * indicator_fn s x)``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC integrable_bounded
 >> Q.EXISTS_TAC `abs o f`
 >> ASM_SIMP_TAC std_ss [o_DEF]
 >> CONJ_TAC >- (MATCH_MP_TAC (REWRITE_RULE [o_DEF] integrable_abs) >> art [])
 >> Reverse CONJ_TAC
 >- (RW_TAC std_ss [] \\
     Cases_on `x IN s` >- ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rone, le_refl] \\
     ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rzero, abs_0, abs_pos])
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL
 >> BETA_TAC
 >> Q.EXISTS_TAC `f` >> Q.EXISTS_TAC `indicator_fn s`
 >> ASM_SIMP_TAC std_ss [space_def]
 >> CONJ_TAC >- PROVE_TAC [measure_space_def]
 >> CONJ_TAC >- PROVE_TAC [integrable_def]
 >> CONJ_TAC >- PROVE_TAC [INDICATOR_FN_NOT_INFTY]
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR
 >> Q.EXISTS_TAC `s`
 >> CONJ_TAC >- PROVE_TAC [measure_space_def]
 >> fs [space_def, subsets_def]);

(* IMPORTANT: all posinf-valued points (which forms a null set) in an integrable
   function can be safely removed without changing its overall integral. *)
val integrable_not_infty = store_thm
  ("integrable_not_infty",
  ``!m f. measure_space m /\ integrable m f /\ (!x. 0 <= f x) ==>
          ?g. integrable m g /\ (!x. 0 <= g x) /\
             (!x. x IN m_space m ==> g x <> PosInf) /\
             (integral m f = integral m g)``,
    RW_TAC std_ss [integral_pos_fn, integrable_def]
 >> Q.ABBREV_TAC `g = (\x. if f x = PosInf then 0 else f x)`
 >> Q.EXISTS_TAC `g`
 >> `!x. 0 <= g x` by METIS_TAC [le_refl]
 >> `!x. g x <= f x` by METIS_TAC [le_refl,le_infty]
 >> `!x. g x <> PosInf` by METIS_TAC [num_not_infty]
 >> Know `g IN measurable (m_space m,measurable_sets m) Borel`
 >- (RW_TAC std_ss [IN_MEASURABLE_BOREL, space_def, subsets_def, IN_FUNSET, IN_UNIV]
     >- METIS_TAC [measure_space_def] \\
     Cases_on `Normal c <= 0`
     >- (`{x | g x < Normal c} = {}`
            by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY]
                >> METIS_TAC [le_trans, extreal_lt_def]) \\
         METIS_TAC [INTER_EMPTY, MEASURE_SPACE_EMPTY_MEASURABLE]) \\
    `{x | g x < Normal c} = {x | f x < Normal c} UNION {x | f x = PosInf}`
       by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_UNION]
           >> Q.UNABBREV_TAC `g`
           >> RW_TAC std_ss []
           >> METIS_TAC [extreal_lt_def]) \\
     RW_TAC std_ss [Once INTER_COMM, UNION_OVER_INTER] \\
     MATCH_MP_TAC MEASURE_SPACE_UNION \\
     RW_TAC std_ss [] \\ (* 2 subgoals *)
     METIS_TAC [(REWRITE_RULE [space_def, subsets_def] o
                 Q.SPECL [`f`,`(m_space m, measurable_sets m)`])
                    IN_MEASURABLE_BOREL_ALL, integrable_def, INTER_COMM]) >> DISCH_TAC
 >> CONJ_TAC
 >- (RW_TAC std_ss []
      >- (`!x. fn_plus g x <= fn_plus f x` by METIS_TAC [FN_PLUS_POS_ID]
          >> METIS_TAC [pos_fn_integral_mono,lt_infty,let_trans,FN_PLUS_POS])
      >> RW_TAC std_ss [FN_MINUS_POS_ZERO,pos_fn_integral_zero,num_not_infty])
 >> RW_TAC std_ss []
 >> Q.ABBREV_TAC `h = (\x. f x - g x)`
 >> `h IN measurable (m_space m,measurable_sets m) Borel`
       by (MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB
           >> METIS_TAC [space_def, lt_infty, lte_trans, measure_space_def, num_not_infty])
 >> `!x. f x <> NegInf` by METIS_TAC [lt_infty,lte_trans,num_not_infty]
 >> `f = (\x. g x + h x)`
       by (RW_TAC std_ss [FUN_EQ_THM]
           >> Cases_on `f x` >> Cases_on `g x` >> Cases_on `h x`
           >> RW_TAC std_ss [extreal_add_def,extreal_sub_def]
           >> METIS_TAC [lt_infty,num_not_infty, lte_trans, extreal_sub_def, extreal_not_infty,
                         extreal_add_def, REAL_EQ_SUB_LADD, REAL_ADD_COMM, extreal_11])
 >> `!x. 0 <= h x` by  METIS_TAC [extreal_sub_def,le_infty,le_refl,extreal_of_num_def,sub_refl]
 >> (MP_TAC o Q.SPECL [`m`,`g`,`h`]) pos_fn_integral_add
 >> RW_TAC std_ss []
 >> Suff `pos_fn_integral m h = 0`
 >- RW_TAC std_ss [add_rzero, integral_pos_fn]
 >> Q.ABBREV_TAC `f = (\x. g x + h x)`
 >> `integrable m f` by RW_TAC std_ss [integrable_def, GSYM fn_plus_def, GSYM fn_minus_def]
 >> `null_set m {x | x IN m_space m /\ (f x = PosInf)}` by METIS_TAC [integrable_infty_null]
 >> (MP_TAC o Q.SPECL [`m`,`h`,`{x | x IN m_space m /\ (f x = PosInf)}`]) pos_fn_integral_split
 >> FULL_SIMP_TAC std_ss [null_set_def]
 >> RW_TAC std_ss []
 >> `(\x. h x * indicator_fn {x | x IN m_space m /\ (f x = PosInf)} x) =
     (\x. PosInf * indicator_fn {x | x IN m_space m /\ (f x = PosInf)} x)`
       by (RW_TAC std_ss [FUN_EQ_THM,indicator_fn_def,mul_rzero,mul_rone,GSPECIFICATION]
           >> Q.UNABBREV_TAC `h`
           >> RW_TAC std_ss [mul_rzero, mul_rone]
           >> METIS_TAC [extreal_sub_def,extreal_cases])
 >> RW_TAC std_ss [pos_fn_integral_cmul_infty, mul_rzero, add_lzero]
 >> `(\x. h x * indicator_fn (m_space m DIFF {x | x IN m_space m /\ (f x = PosInf)}) x) =
      (\x. 0)`
       by (RW_TAC std_ss [FUN_EQ_THM,indicator_fn_def,mul_rzero,mul_rone,GSPECIFICATION,IN_DIFF]
           >> Q.UNABBREV_TAC `h`
           >> RW_TAC std_ss [mul_rzero, mul_rone]
           >> METIS_TAC [sub_refl])
 >> RW_TAC std_ss [pos_fn_integral_zero, GSYM extreal_of_num_def, mul_rzero, add_rzero]);

val integrable_not_infty_alt = store_thm
  ("integrable_not_infty_alt",
  ``!m f. measure_space m /\ integrable m f /\ (!x. 0 <= f x) ==>
          integrable m (\x. if f x = PosInf then 0 else f x) /\
         (integral m f = integral m (\x. if f x = PosInf then 0 else f x))``,
  NTAC 3 STRIP_TAC
  >> Q.ABBREV_TAC `g = (\x. if f x = PosInf then 0 else f x)`
  >> `!x. 0 <= g x` by METIS_TAC [le_refl]
  >> `!x. g x <= f x` by METIS_TAC [le_refl, le_infty]
  >> `!x. g x <> PosInf` by METIS_TAC [num_not_infty]
  >> `!x. g x <> NegInf` by METIS_TAC [lt_infty,lte_trans, num_not_infty]
  >> `!x. f x <> NegInf` by METIS_TAC [lt_infty,lte_trans, num_not_infty]
  >> `g IN measurable (m_space m,measurable_sets m) Borel`
      by (RW_TAC std_ss [IN_MEASURABLE_BOREL, space_def, subsets_def, IN_FUNSET, IN_UNIV]
          >- METIS_TAC [measure_space_def]
          >> Cases_on `Normal c <= 0`
          >- (`{x | g x < Normal c} = {}` by
                (RW_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY]
                 >> METIS_TAC [le_trans,extreal_lt_def])
              >> METIS_TAC [INTER_EMPTY, MEASURE_SPACE_EMPTY_MEASURABLE])
          >> `{x | g x < Normal c} = {x | f x < Normal c} UNION {x | f x = PosInf}`
                by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_UNION]
                    >> Q.UNABBREV_TAC `g`
                    >> RW_TAC std_ss []
                    >> METIS_TAC [extreal_lt_def])
          >> RW_TAC std_ss [Once INTER_COMM, UNION_OVER_INTER]
          >> MATCH_MP_TAC MEASURE_SPACE_UNION
          >> RW_TAC std_ss []
          >> METIS_TAC [(REWRITE_RULE [space_def, subsets_def] o
                        Q.SPECL [`f`,`(m_space m, measurable_sets m)`])
                            IN_MEASURABLE_BOREL_ALL, integrable_def, INTER_COMM])
  >> `integrable m g`
      by (RW_TAC std_ss [integrable_def, GSYM fn_plus_def, GSYM fn_minus_def]
          >- (`!x. fn_plus g x <= fn_plus f x` by METIS_TAC [FN_PLUS_POS_ID]
              >> FULL_SIMP_TAC std_ss [integrable_def, GSYM fn_plus_def]
              >> METIS_TAC [pos_fn_integral_mono, lt_infty, let_trans, FN_PLUS_POS])
          >> RW_TAC std_ss [FN_MINUS_POS_ZERO, pos_fn_integral_zero, num_not_infty])
  >> RW_TAC std_ss []
  >>  Q.ABBREV_TAC `h = (\x. f x - g x)`
  >> `h IN measurable (m_space m,measurable_sets m) Borel`
       by (MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB
           >> METIS_TAC [space_def, lt_infty, lte_trans, measure_space_def, num_not_infty,
                         integrable_def])
  >> RW_TAC std_ss [integral_pos_fn]
  >> `f = (\x. g x + h x)`
       by (RW_TAC std_ss [FUN_EQ_THM]
           >> Cases_on `f x` >> Cases_on `g x` >> Cases_on `h x`
           >> RW_TAC std_ss [extreal_add_def, extreal_sub_def]
           >> METIS_TAC [lt_infty, num_not_infty, lte_trans, extreal_sub_def, extreal_not_infty,
                         extreal_add_def, REAL_EQ_SUB_LADD, REAL_ADD_COMM, extreal_11])
  >> `!x. 0 <= h x`
      by METIS_TAC [extreal_sub_def, le_infty, le_refl, extreal_of_num_def, sub_refl]
  >> (MP_TAC o Q.SPECL [`m`,`g`,`h`]) pos_fn_integral_add
  >> RW_TAC std_ss []
  >> Suff `pos_fn_integral m h = 0`
  >- RW_TAC std_ss [add_rzero]
  >> Q.ABBREV_TAC `f = (\x. g x + h x)`
  >> `integrable m f` by RW_TAC std_ss [integrable_def, GSYM fn_plus_def, GSYM fn_minus_def]
  >> `null_set m {x | x IN m_space m /\ (f x = PosInf)}` by METIS_TAC [integrable_infty_null]
  >> (MP_TAC o Q.SPECL [`m`,`h`,`{x | x IN m_space m /\ (f x = PosInf)}`]) pos_fn_integral_split
  >> FULL_SIMP_TAC std_ss [null_set_def]
  >> RW_TAC std_ss []
  >> `(\x. h x * indicator_fn {x | x IN m_space m /\ (f x = PosInf)} x) =
      (\x. PosInf * indicator_fn {x | x IN m_space m /\ (f x = PosInf)} x)`
       by (RW_TAC std_ss [FUN_EQ_THM, indicator_fn_def, mul_rzero, mul_rone, GSPECIFICATION]
           >> Q.UNABBREV_TAC `h`
           >> RW_TAC std_ss [mul_rzero, mul_rone]
           >> METIS_TAC [extreal_sub_def, extreal_cases])
  >> RW_TAC std_ss [pos_fn_integral_cmul_infty, mul_rzero, add_lzero]
  >> `(\x. h x * indicator_fn (m_space m DIFF {x | x IN m_space m /\ (f x = PosInf)}) x) =
      (\x. 0)`
       by (RW_TAC std_ss [FUN_EQ_THM,indicator_fn_def, mul_rzero, mul_rone, GSPECIFICATION,
                          IN_DIFF]
           >> Q.UNABBREV_TAC `h`
           >> RW_TAC std_ss [mul_rzero, mul_rone]
           >> METIS_TAC [sub_refl])
  >> RW_TAC std_ss [pos_fn_integral_zero, GSYM extreal_of_num_def, mul_rzero, add_rzero]);

val integrable_not_infty_alt2 = store_thm
  ("integrable_not_infty_alt2",
  ``!m f. measure_space m /\ integrable m f /\ (!x. 0 <= f x) ==>
        integrable m (\x. if f x = PosInf then 0 else f x) /\
        (pos_fn_integral m f = pos_fn_integral m (\x. if f x = PosInf then 0 else f x))``,
  RW_TAC std_ss []
  >- RW_TAC std_ss [integrable_not_infty_alt]
  >> `!x. 0 <= (\x. if f x = PosInf then 0 else f x) x` by METIS_TAC [le_refl]
  >> FULL_SIMP_TAC std_ss [GSYM integral_pos_fn]
  >> METIS_TAC [integrable_not_infty_alt]);

val integrable_not_infty_alt3 = store_thm
  ("integrable_not_infty_alt3",
  ``!m f. measure_space m /\ integrable m f ==>
          integrable m (\x. if ((f x = NegInf) \/ (f x = PosInf)) then 0 else f x) /\
         (integral m f =
          integral m (\x. if ((f x = NegInf) \/ (f x = PosInf)) then 0 else f x))``,
 (* proof *)
    NTAC 3 STRIP_TAC
 >> `fn_plus (\x. if (f x = NegInf) \/ (f x = PosInf) then 0 else f x) =
      (\x. if fn_plus f x = PosInf then 0 else fn_plus f x)`
      by (RW_TAC std_ss [fn_plus_def,FUN_EQ_THM]
          >> Cases_on `f x` >> METIS_TAC [lt_infty])
 >> `fn_minus (\x. if (f x = NegInf) \/ (f x = PosInf) then 0 else f x) =
      (\x. if fn_minus f x = PosInf then 0 else fn_minus f x)`
      by (RW_TAC std_ss [fn_minus_def,FUN_EQ_THM]
          >> Cases_on `f x`
          >> METIS_TAC [lt_infty, lt_refl, extreal_ainv_def, extreal_not_infty])
 >> `integrable m (fn_plus f)` by RW_TAC std_ss [integrable_fn_plus]
 >> `integrable m (fn_minus f)` by RW_TAC std_ss [integrable_fn_minus]
 >> `integrable m (\x. if fn_plus f x = PosInf then 0 else fn_plus f x)`
       by METIS_TAC [integrable_not_infty_alt2, FN_PLUS_POS, FN_MINUS_POS, integrable_pos]
 >> `integrable m (\x. if fn_minus f x = PosInf then 0 else fn_minus f x)`
       by METIS_TAC [integrable_not_infty_alt2, FN_PLUS_POS, FN_MINUS_POS, integrable_pos]
 >> Reverse (RW_TAC std_ss [integral_def, integrable_def, GSYM fn_plus_def, GSYM fn_minus_def])
 >| [ (* goal 1 (of 4) *)
      METIS_TAC [integrable_not_infty_alt2, FN_PLUS_POS, FN_MINUS_POS],
      (* goal 2 (of 4) *)
      METIS_TAC [integrable_not_infty_alt2, FN_PLUS_POS, FN_MINUS_POS, integrable_pos],
      (* goal 3 (of 4) *)
      METIS_TAC [integrable_not_infty_alt2, FN_PLUS_POS, FN_MINUS_POS, integrable_pos],
      (* goal 4 (of 4) *)
     `(\x. if (f x = NegInf) \/ (f x = PosInf) then 0 else f x) =
       (\x. (\x. if fn_plus f x = PosInf then 0 else fn_plus f x) x -
       (\x. if fn_minus f x = PosInf then 0 else fn_minus f x) x)`
         by (RW_TAC std_ss [FUN_EQ_THM,fn_plus_def,fn_minus_def]
             >> Cases_on `f x`
             >> RW_TAC std_ss [lt_infty, extreal_sub_def, extreal_ainv_def, extreal_not_infty,
                               num_not_infty, sub_rzero]
             >> METIS_TAC [lt_infty, extreal_not_infty, num_not_infty, extreal_ainv_def,
                           lt_antisym, sub_lzero, neg_neg, extreal_lt_def, le_antisym]) \\
      POP_ORW \\
      MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
      Q.EXISTS_TAC `(\x. if fn_plus f x = PosInf then 0 else fn_plus f x)` \\
      Q.EXISTS_TAC `(\x. if fn_minus f x = PosInf then 0 else fn_minus f x)` \\
      FULL_SIMP_TAC std_ss [integrable_def, measure_space_def, space_def] \\
   (* additional steps added by Chun Tian *)
      GEN_TAC >> DISCH_TAC \\
      CONJ_TAC >- (Cases_on `fn_plus f x = PosInf`
                   >- METIS_TAC [extreal_cases, extreal_of_num_def, extreal_not_infty] \\
                   ASM_SIMP_TAC std_ss [] \\
                   METIS_TAC [FN_PLUS_POS, pos_not_neginf]) \\
      Cases_on `fn_minus f x = PosInf`
      >- METIS_TAC [extreal_cases, extreal_of_num_def, extreal_not_infty] \\
      ASM_SIMP_TAC std_ss [] ]);

(* ------------------------------------------------------------------------- *)
(* Properties of Integral                                                    *)
(* ------------------------------------------------------------------------- *)

val integral_indicator = store_thm
  ("integral_indicator",
  ``!m s. measure_space m /\ s IN measurable_sets m ==>
          (integral m (indicator_fn s) = measure m s)``,
    RW_TAC std_ss []
 >> `!x. 0 <= indicator_fn s x`
     by RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, le_refl, le_01]
 >> METIS_TAC [pos_fn_integral_indicator, integral_pos_fn]);

(* added `!x. f2 x <> PosInf` to make sure that `f1 x - f2 x` is always defined *)
val integral_add_lemma = store_thm
  ("integral_add_lemma",
  ``!m f f1 f2. measure_space m /\
                integrable m f /\ integrable m f1 /\ integrable m f2  /\
               (f = (\x. f1 x - f2 x)) /\ (!x. 0 <= f1 x) /\
               (!x. 0 <= f2 x) /\ (!x. f2 x <> PosInf) ==>
      (integral m f = pos_fn_integral m f1 - pos_fn_integral m f2)``,
    rpt STRIP_TAC
 >> REWRITE_TAC [integral_def]
 >> Q.ABBREV_TAC `h1 = (\x. fn_plus f x + f2 x)`
 >> Q.ABBREV_TAC `h2 = (\x. fn_minus f x + f1 x)`
 >> `!x. f1 x <> NegInf` by METIS_TAC [lt_infty, lte_trans, num_not_infty]
 >> `!x. f2 x <> NegInf` by METIS_TAC [lt_infty, lte_trans, num_not_infty]
 >> Know `h1 = h2`
 >- (Q.UNABBREV_TAC `h1` >> Q.UNABBREV_TAC `h2` \\
     RW_TAC real_ss [FUN_EQ_THM, fn_plus_def, fn_minus_def] \\
     Cases_on `0 < f1 x - f2 x`
     >- (RW_TAC std_ss [] \\
         Cases_on `f1 x` >> Cases_on `f2 x` \\
         FULL_SIMP_TAC std_ss [extreal_sub_def, extreal_add_def, extreal_ainv_def,
                               extreal_11, add_lzero] \\
         METIS_TAC [lt_antisym, lt_infty, REAL_SUB_ADD]) \\
     RW_TAC std_ss [add_lzero] \\
     Cases_on `f1 x` >> Cases_on `f2 x` \\
     FULL_SIMP_TAC std_ss [extreal_sub_def, extreal_add_def, extreal_ainv_def, extreal_11,
                           add_lzero] \\
     METIS_TAC [real_sub, REAL_SUB_SUB2, REAL_ADD_COMM, lt_infty, lt_antisym,
                extreal_lt_def, extreal_of_num_def, REAL_LE_ANTISYM, extreal_le_def,
                REAL_SUB_0])
 >> DISCH_TAC
 >> `pos_fn_integral m h1 = pos_fn_integral m h2` by METIS_TAC []
 >> `pos_fn_integral m h1 =
     pos_fn_integral m (fn_plus f) + pos_fn_integral m f2`
      by (Q.UNABBREV_TAC `h1`
          >> MATCH_MP_TAC pos_fn_integral_add
          >> FULL_SIMP_TAC std_ss [integrable_def]
          >> RW_TAC std_ss [le_refl, lt_le, IN_MEASURABLE_BOREL_FN_PLUS,FN_PLUS_POS])
 >> `pos_fn_integral m h2 =
     pos_fn_integral m (fn_minus f) + pos_fn_integral m f1`
      by (Q.UNABBREV_TAC `h2`
          >> MATCH_MP_TAC pos_fn_integral_add
          >> METIS_TAC [FN_MINUS_POS,IN_MEASURABLE_BOREL_FN_MINUS,integrable_def])
 >> `pos_fn_integral m f2 <> PosInf` by METIS_TAC [integrable_pos]
 >> `pos_fn_integral m (fn_minus f) <> PosInf`
      by METIS_TAC [integrable_def]
 >> `pos_fn_integral m f2 <> NegInf`
      by METIS_TAC [pos_fn_integral_pos,lt_infty,lte_trans,num_not_infty]
 >> `0 <= pos_fn_integral m (fn_minus f)`
      by METIS_TAC [pos_fn_integral_pos,FN_MINUS_POS]
 >> `pos_fn_integral m (fn_minus f) <> NegInf`
      by METIS_TAC [lt_infty, lte_trans, num_not_infty]
 >> METIS_TAC [eq_add_sub_switch]);

(* added `(!x. f x <> NegInf) /\ (!x. g x <> NegInf)`, if these assumptions
   do not hold, it should be possible to first convert them into qualified functions
   by "integrable_not_infty" et el.
 *)
val integral_add = store_thm
  ("integral_add",
  ``!m f g. measure_space m /\ integrable m f /\ integrable m g /\
           (!x. f x <> NegInf) /\ (!x. g x <> NegInf)
        ==> (integral m (\x. f x + g x) = integral m f + integral m g)``,
    RW_TAC std_ss []
 >> Know `integral m (\x. f x + g x) = pos_fn_integral m (\x. fn_plus f x + fn_plus g x) -
                                       pos_fn_integral m (\x. fn_minus f x + fn_minus g x)`
 >- (MATCH_MP_TAC integral_add_lemma \\
    `!x. 0 <= fn_minus f x + fn_minus g x` by METIS_TAC [FN_MINUS_POS, le_add] \\
    `!x. 0 <= fn_plus f x + fn_plus g x` by METIS_TAC [FN_PLUS_POS, le_add] \\
     RW_TAC std_ss [FUN_EQ_THM, add_rzero, add_lzero, lt_imp_le, le_refl, le_add,
                    integrable_add] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       MATCH_MP_TAC integrable_add >> art [] \\
       CONJ_TAC >- PROVE_TAC [integrable_fn_plus] \\
       CONJ_TAC >- PROVE_TAC [integrable_fn_plus] \\
       GEN_TAC >> DISCH_TAC \\
       CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf >> REWRITE_TAC [FN_PLUS_POS]) \\
       MATCH_MP_TAC pos_not_neginf >> REWRITE_TAC [FN_PLUS_POS],
       (* goal 2 (of 4) *)
       METIS_TAC [integrable_fn_minus,integrable_add, FN_MINUS_POS, pos_not_neginf],
       (* goal 3 (of 4) *)
      `f x + g x = fn_plus f x - fn_minus f x + (fn_plus g x - fn_minus g x)`
         by PROVE_TAC [FN_DECOMP] >> POP_ORW \\
      `fn_minus f x <> PosInf /\ fn_minus g x <> PosInf` by PROVE_TAC [FN_MINUS_NOT_INFTY] \\
      `fn_plus f x <> NegInf /\ fn_plus g x <> NegInf` by PROVE_TAC [FN_PLUS_POS, pos_not_neginf] \\
       Q.ABBREV_TAC `a = fn_plus f x` \\
       Q.ABBREV_TAC `b = fn_minus f x` \\
       Q.ABBREV_TAC `c = fn_plus g x` \\
       Q.ABBREV_TAC `d = fn_minus g x` \\
      `a - b = a + -b` by PROVE_TAC [extreal_sub_add] >> POP_ORW \\
      `c - d = c + -d` by PROVE_TAC [extreal_sub_add] >> POP_ORW \\
      `a + c <> NegInf` by PROVE_TAC [add_not_infty] \\
      `b + d <> PosInf` by PROVE_TAC [add_not_infty] \\
      `a + c - (b + d) = a + c + -(b + d)` by PROVE_TAC [extreal_sub_add] >> POP_ORW \\
      `-(b + d) = -b + -d` by PROVE_TAC [neg_add] >> POP_ORW \\
       (* TODO: optimize this *)
       METIS_TAC [add_assoc, add_comm, add_not_infty, extreal_ainv_def, neg_neg],
       (* goal 4 (of 4) *)
      `fn_minus f x <> PosInf /\ fn_minus g x <> PosInf` by PROVE_TAC [FN_MINUS_NOT_INFTY] \\
       PROVE_TAC [add_not_infty] ])
 >> Rewr
 >> `pos_fn_integral m (\x. fn_plus f x + fn_plus g x) =
     pos_fn_integral m (fn_plus f) + pos_fn_integral m (fn_plus g)`
      by METIS_TAC [pos_fn_integral_add, IN_MEASURABLE_BOREL_FN_PLUS, FN_PLUS_POS, integrable_def]
 >> `pos_fn_integral m (\x. fn_minus f x + fn_minus g x) =
     pos_fn_integral m (fn_minus f) + pos_fn_integral m (fn_minus g)`
      by METIS_TAC [pos_fn_integral_add, IN_MEASURABLE_BOREL_FN_MINUS,FN_MINUS_POS,integrable_def]
 >> RW_TAC std_ss [integral_def, GSYM fn_plus_def, GSYM fn_minus_def]
 >> NTAC 2 (POP_ASSUM K_TAC)
 >> Know `pos_fn_integral m (fn_plus f) <> NegInf`
 >- (MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC pos_fn_integral_pos >> art [FN_PLUS_POS]) >> DISCH_TAC
 >> Know `pos_fn_integral m (fn_minus f) <> NegInf`
 >- (MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC pos_fn_integral_pos >> art [FN_MINUS_POS]) >> DISCH_TAC
 >> Know `pos_fn_integral m (fn_plus g) <> NegInf`
 >- (MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC pos_fn_integral_pos >> art [FN_PLUS_POS]) >> DISCH_TAC
 >> Know `pos_fn_integral m (fn_minus g) <> NegInf`
 >- (MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC pos_fn_integral_pos >> art [FN_MINUS_POS]) >> DISCH_TAC
 >> fs [integrable_def]
 >> Q.ABBREV_TAC `a = pos_fn_integral m (fn_plus f)`
 >> Q.ABBREV_TAC `b = pos_fn_integral m (fn_minus f)`
 >> Q.ABBREV_TAC `c = pos_fn_integral m (fn_plus g)`
 >> Q.ABBREV_TAC `d = pos_fn_integral m (fn_minus g)`
 >> MATCH_MP_TAC EQ_SYM
 >> MATCH_MP_TAC add2_sub2 >> art []);

val integral_cmul = store_thm (* "integral_times" in real_lebesgueTheory *)
  ("integral_cmul",
  ``!m f c. measure_space m /\ integrable m f ==>
           (integral m (\x. Normal c * f x) = Normal c * integral m f)``,
  RW_TAC std_ss [integral_def,GSYM fn_plus_def,GSYM fn_minus_def]
  >> `(\x. fn_plus f x) = fn_plus f` by METIS_TAC []
  >> `(\x. fn_minus f x) = fn_minus f` by METIS_TAC []
  >> Cases_on `0 <= c`
  >- (RW_TAC std_ss [FN_PLUS_CMUL, FN_MINUS_CMUL, FN_PLUS_POS, FN_MINUS_POS, pos_fn_integral_cmul]
      >> MATCH_MP_TAC (GSYM sub_ldistrib)
      >> FULL_SIMP_TAC std_ss [extreal_not_infty, integrable_def, GSYM fn_plus_def,
                               GSYM fn_minus_def]
      >> METIS_TAC [pos_fn_integral_pos, FN_PLUS_POS, FN_MINUS_POS, lt_infty, lte_trans,
                    extreal_of_num_def])
  >> `c <= 0` by METIS_TAC [REAL_LT_IMP_LE,real_lt]
  >> `0 <= -c` by METIS_TAC [REAL_LE_NEG,REAL_NEG_0]
  >> RW_TAC std_ss [FN_PLUS_CMUL, FN_MINUS_CMUL, FN_PLUS_POS, FN_MINUS_POS, pos_fn_integral_cmul,
                    extreal_ainv_def]
  >> RW_TAC std_ss [Once (GSYM eq_neg), GSYM mul_lneg, extreal_ainv_def]
  >> FULL_SIMP_TAC std_ss [integrable_def, GSYM fn_plus_def, GSYM fn_minus_def]
  >> `pos_fn_integral m (fn_plus f) <> NegInf`
      by METIS_TAC [pos_fn_integral_pos, FN_PLUS_POS, lt_infty, lte_trans, extreal_of_num_def]
  >> `pos_fn_integral m (fn_minus f) <> NegInf`
      by METIS_TAC [pos_fn_integral_pos, FN_MINUS_POS, lt_infty, lte_trans, extreal_of_num_def]
  >> FULL_SIMP_TAC std_ss [GSYM sub_ldistrib, extreal_not_infty, GSYM mul_rneg]
  >> METIS_TAC [neg_sub]);

(* added `measure m s < PosInf` into antecedents, otherwise not true *)
val integral_cmul_indicator = store_thm
  ("integral_cmul_indicator",
  ``!m s c. measure_space m /\ s IN measurable_sets m /\ measure m s < PosInf ==>
           (integral m (\x. Normal c * indicator_fn s x) = Normal c * measure m s)``,
    METIS_TAC [integral_cmul, integral_indicator, integrable_indicator, extreal_mul_def]);

val integral_zero = store_thm
  ("integral_zero", ``!m. measure_space m ==> (integral m (\x. 0) = 0)``,
    RW_TAC std_ss [integral_def, lt_refl, pos_fn_integral_zero, sub_lzero, neg_0,
                   fn_plus_def, fn_minus_def]);

val integral_mspace = store_thm
  ("integral_mspace",
  ``!m f. measure_space m ==>
         (integral m f = integral m (\x. f x * indicator_fn (m_space m) x))``,
    RW_TAC std_ss [integral_def]
 >> `(fn_plus (\x. f x * indicator_fn (m_space m) x)) =
     (\x. fn_plus f x * indicator_fn (m_space m) x)`
       by (RW_TAC std_ss [indicator_fn_def, fn_plus_def, FUN_EQ_THM] \\
           METIS_TAC [mul_rone, mul_lone, mul_rzero, mul_lzero])
 >> `fn_minus (\x. f x * indicator_fn (m_space m) x) =
     (\x. fn_minus f x * indicator_fn (m_space m) x)`
       by (RW_TAC std_ss [indicator_fn_def, fn_minus_def, FUN_EQ_THM] \\
           METIS_TAC [neg_0, neg_eq0, mul_rone, mul_lone, mul_rzero, mul_lzero])
 >> RW_TAC std_ss []
 >> METIS_TAC [pos_fn_integral_mspace, FN_PLUS_POS, FN_MINUS_POS]);

val integral_const = store_thm (* new *)
  ("integral_const",
  ``!m c. measure_space m /\ measure m (m_space m) < PosInf ==>
         (integral m (\x. Normal c) = Normal c * measure m (m_space m))``,
    rpt STRIP_TAC
 >> ONCE_REWRITE_TAC [MATCH_MP integral_mspace (ASSUME ``measure_space m``)]
 >> BETA_TAC
 >> MATCH_MP_TAC integral_cmul_indicator >> art []
 >> PROVE_TAC [MEASURE_SPACE_MSPACE_MEASURABLE]);

val integral_cmul_infty = store_thm
  ("integral_cmul_infty",
  ``!m s. measure_space m /\ s IN measurable_sets m ==>
         (integral m (\x. PosInf * indicator_fn s x) = PosInf * (measure m s))``,
    rpt STRIP_TAC
 >> Know `integral m (\x. PosInf) = integral m (\x. (\x. PosInf) x * indicator_fn (m_space m) x)`
 >- (MATCH_MP_TAC integral_mspace >> art []) >> Rewr'
 >> Know `integral m (\x. PosInf * indicator_fn s x) =
   pos_fn_integral m (\x. PosInf * indicator_fn s x)`
 >- (MATCH_MP_TAC integral_pos_fn >> RW_TAC std_ss [] \\
     MATCH_MP_TAC le_mul >> REWRITE_TAC [INDICATOR_FN_POS] \\
     REWRITE_TAC [extreal_of_num_def, le_infty]) >> Rewr'
 >> MATCH_MP_TAC pos_fn_integral_cmul_infty >> art []);

val integral_posinf = store_thm
  ("integral_posinf",
  ``!m. measure_space m /\ 0 < measure m (m_space m) ==> (integral m (\x. PosInf) = PosInf)``,
    rpt STRIP_TAC
 >> Know `integral m (\x. PosInf) =
          integral m (\x. (\x. PosInf) x * indicator_fn (m_space m) x)`
 >- (MATCH_MP_TAC integral_mspace >> art [])
 >> Rewr' >> BETA_TAC
 >> Know `integral m (\x. PosInf * indicator_fn (m_space m) x) = PosInf * (measure m (m_space m))`
 >- (MATCH_MP_TAC integral_cmul_infty >> art [] \\
     MATCH_MP_TAC MEASURE_SPACE_MSPACE_MEASURABLE >> art []) >> Rewr'
 >> Cases_on `measure m (m_space m) = PosInf`
 >- (POP_ORW >> REWRITE_TAC [extreal_mul_def])
 >> METIS_TAC [mul_infty]);

val integral_eq = store_thm
  ("integral_eq",
  ``!m f g. measure_space m /\ (!x. x IN m_space m ==> (f x = g x)) ==>
           (integral m f = integral m g)``,
    rpt STRIP_TAC
 >> `(integral m f = integral m (\x. f x * indicator_fn (m_space m) x)) /\
     (integral m g = integral m (\x. g x * indicator_fn (m_space m) x))`
        by METIS_TAC [integral_mspace] >> art []
 >> Suff `(\x. f x * indicator_fn (m_space m) x) = (\x. g x * indicator_fn (m_space m) x)`
 >- RW_TAC std_ss []
 >> FUN_EQ_TAC >> RW_TAC std_ss [indicator_fn_def, GSPECIFICATION, mul_rzero]);

val integral_indicator_pow_eq = store_thm (* new *)
  ("integral_indicator_pow_eq",
  ``!m s n. measure_space m /\ s IN measurable_sets m /\ 0 < n ==>
           (integral m (\x. (indicator_fn s x) pow n) = integral m (indicator_fn s))``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC integral_eq
 >> RW_TAC std_ss [indicator_fn_def, one_pow, zero_pow]);

val integral_indicator_pow = store_thm (* new *)
  ("integral_indicator_pow",
  ``!m s n. measure_space m /\ s IN measurable_sets m /\ 0 < n ==>
           (integral m (\x. (indicator_fn s x) pow n) = measure m s)``,
    rpt STRIP_TAC
 >> Suff `integral m (\x. (indicator_fn s x) pow n) = integral m (indicator_fn s)`
 >- (Rewr' >> MATCH_MP_TAC integral_indicator >> art [])
 >> MATCH_MP_TAC integral_indicator_pow_eq >> art []);

(* added `integrable f1 /\ integrable f2` into antecedents *)
val integral_mono = store_thm
  ("integral_mono",
  ``!m f1 f2. measure_space m /\ integrable m f1 /\ integrable m f2 /\
             (!t. t IN m_space m ==> f1 t <= f2 t) ==>
             (integral m f1 <= integral m f2)``,
    RW_TAC std_ss []
 >> ONCE_REWRITE_TAC [(UNDISCH o Q.SPECL [`m`,`f`]) integral_mspace]
 >> RW_TAC std_ss [integral_def]
 >> `!x. (fn_plus (\x. f1 x * indicator_fn (m_space m) x)) x <=
         (fn_plus (\x. f2 x * indicator_fn (m_space m) x)) x`
       by (RW_TAC real_ss [fn_plus_def, lt_imp_le, le_refl, indicator_fn_def, mul_rzero, mul_rone]
           >> METIS_TAC [extreal_lt_def, mul_rone, lt_imp_le, le_trans])
 >> `!x. (fn_minus (\x. f2 x * indicator_fn (m_space m) x)) x <=
         (fn_minus (\x. f1 x * indicator_fn (m_space m) x)) x`
       by (RW_TAC real_ss [fn_minus_def, lt_imp_le, le_refl, indicator_fn_def, mul_rzero,
                           mul_rone, neg_0, neg_eq0, le_neg]
           >> METIS_TAC [mul_rone, extreal_lt_def, le_trans, lt_neg, lt_imp_le, neg_0])
 >> fs [integrable_def]
 (* preparing for applying "extreal_sub_add" *)
 >> Know `pos_fn_integral m (fn_plus (\x. f1 x * indicator_fn (m_space m) x)) <> NegInf`
 >- (MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC pos_fn_integral_pos >> art [] \\
     REWRITE_TAC [FN_PLUS_POS]) >> DISCH_TAC
 >> Know `pos_fn_integral m (fn_plus (\x. f2 x * indicator_fn (m_space m) x)) <> NegInf`
 >- (MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC pos_fn_integral_pos >> art [] \\
     REWRITE_TAC [FN_PLUS_POS]) >> DISCH_TAC
 >> Know `pos_fn_integral m (fn_minus (\x. f1 x * indicator_fn (m_space m) x)) <> PosInf`
 >- (Suff `pos_fn_integral m (fn_minus (\x. f1 x * indicator_fn (m_space m) x)) =
           pos_fn_integral m (fn_minus f1)` >- METIS_TAC [] \\
     MATCH_MP_TAC EQ_SYM \\
     Suff `fn_minus (\x. f1 x * indicator_fn (m_space m) x) =
           (\x. fn_minus f1 x * indicator_fn (m_space m) x)`
     >- (Rewr >> MATCH_MP_TAC pos_fn_integral_mspace >> art [FN_MINUS_POS]) \\
     ONCE_REWRITE_TAC [mul_comm] \\
     MATCH_MP_TAC FN_MINUS_FMUL >> REWRITE_TAC [INDICATOR_FN_POS]) >> DISCH_TAC
 >> Know `pos_fn_integral m (fn_minus (\x. f2 x * indicator_fn (m_space m) x)) <> PosInf`
 >- (Suff `pos_fn_integral m (fn_minus (\x. f2 x * indicator_fn (m_space m) x)) =
           pos_fn_integral m (fn_minus f2)` >- METIS_TAC [] \\
     MATCH_MP_TAC EQ_SYM \\
     Suff `fn_minus (\x. f2 x * indicator_fn (m_space m) x) =
           (\x. fn_minus f2 x * indicator_fn (m_space m) x)`
     >- (Rewr >> MATCH_MP_TAC pos_fn_integral_mspace >> art [FN_MINUS_POS]) \\
     ONCE_REWRITE_TAC [mul_comm] \\
     MATCH_MP_TAC FN_MINUS_FMUL >> REWRITE_TAC [INDICATOR_FN_POS]) >> DISCH_TAC
 >> `pos_fn_integral m (fn_plus (\x. f1 x * indicator_fn (m_space m) x)) -
     pos_fn_integral m (fn_minus (\x. f1 x * indicator_fn (m_space m) x)) =
     pos_fn_integral m (fn_plus (\x. f1 x * indicator_fn (m_space m) x)) +
    -pos_fn_integral m (fn_minus (\x. f1 x * indicator_fn (m_space m) x))`
     by PROVE_TAC [extreal_sub_add] >> POP_ORW
 >> `pos_fn_integral m (fn_plus (\x. f2 x * indicator_fn (m_space m) x)) -
     pos_fn_integral m (fn_minus (\x. f2 x * indicator_fn (m_space m) x)) =
     pos_fn_integral m (fn_plus (\x. f2 x * indicator_fn (m_space m) x)) +
    -pos_fn_integral m (fn_minus (\x. f2 x * indicator_fn (m_space m) x))`
     by PROVE_TAC [extreal_sub_add] >> POP_ORW
 >> MATCH_MP_TAC le_add2
 >> CONJ_TAC
 >- (MATCH_MP_TAC pos_fn_integral_mono >> GEN_TAC >> art [FN_PLUS_POS])
 >> REWRITE_TAC [le_neg]
 >> MATCH_MP_TAC pos_fn_integral_mono
 >> GEN_TAC >> art [FN_MINUS_POS]);

val integrable_finite_integral = store_thm (* new *)
  ("integrable_finite_integral",
  ``!m f. measure_space m /\ integrable m f ==>
          integral m f <> PosInf /\ integral m f <> NegInf``,
    rpt GEN_TAC
 >> SIMP_TAC std_ss [integral_def, integrable_def]
 >> STRIP_TAC
 >> Know `pos_fn_integral m (fn_plus f) <> NegInf`
 >- (MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC pos_fn_integral_pos >> art [FN_PLUS_POS]) >> DISCH_TAC
 >> Know `pos_fn_integral m (fn_minus f) <> NegInf`
 >- (MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC pos_fn_integral_pos >> art [FN_MINUS_POS]) >> DISCH_TAC
 >> `?r1. pos_fn_integral m (fn_plus f) = Normal r1` by PROVE_TAC [extreal_cases]
 >> `?r2. pos_fn_integral m (fn_minus f) = Normal r2` by PROVE_TAC [extreal_cases]
 >> ASM_REWRITE_TAC [extreal_sub_def, extreal_not_infty]);

val integrable_sum = store_thm
  ("integrable_sum",
  ``!m f s. FINITE s /\ measure_space m /\ (!i. i IN s ==> integrable m (f i)) /\
            (!x i. i IN s ==> f i x <> PosInf /\ f i x <> NegInf) ==>
            integrable m (\x. SIGMA (\i. f i x) s)``,
    Suff `!s:'b->bool.
            FINITE s ==>
              (\s:'b->bool. !m f. measure_space m /\ (!i. i IN s ==> integrable m (f i)) /\
                                  (!x i. i IN s ==> f i x <> PosInf /\ f i x <> NegInf)
                              ==> integrable m (\x. SIGMA (\i. f i x) s)) s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, integrable_zero]
 >> Know `!x. SIGMA (\i. f i x) (e INSERT s) = f e x + (\x. SIGMA (\i. f i x) s) x`
 >- (RW_TAC std_ss [] \\
     (MP_TAC o Q.SPEC `e` o UNDISCH o Q.SPECL [`(\i. f i x)`,`s`] o
      INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY \\
    `!i. i IN e INSERT s ==> (\i. f i x) i <> NegInf` by RW_TAC std_ss [] \\
     FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]) >> Rewr'
 >> MATCH_MP_TAC integrable_add >> art []
 >> CONJ_TAC >- fs [IN_INSERT]
 >> CONJ_TAC
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> fs [IN_INSERT])
 >> RW_TAC std_ss [IN_INSERT]
 >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF >> fs [IN_INSERT]);

val integral_sum = store_thm
  ("integral_sum",
  ``!m f s. FINITE s /\ measure_space m /\ (!i. i IN s ==> integrable m (f i)) /\
            (!x i. i IN s ==> f i x <> PosInf /\ f i x <> NegInf)
        ==> (integral m (\x. SIGMA (\i. (f i) x) s) = SIGMA (\i. integral m (f i)) s)``,
 (* proof *)
    Suff `!s:'b->bool.
            FINITE s ==>
              (\s:'b->bool. !m f. measure_space m /\ (!i. i IN s ==> integrable m (f i)) /\
                                 (!x i. i IN s ==> f i x <> PosInf /\ f i x <> NegInf)
                             ==> (integral m (\x. SIGMA (\i. (f i) x) s) =
                                  SIGMA (\i. integral m (f i)) s)) s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, integral_zero]
 >> Know `!x. SIGMA (\i. f i x) (e INSERT s) = f e x + SIGMA (\i. f i x) s`
 >- (RW_TAC std_ss [] \\
     (MP_TAC o Q.SPEC `e` o UNDISCH o Q.SPECL [`(\i. f i x)`,`s`] o
      INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY \\
    `!i. i IN e INSERT s ==> (\i. f i x) i <> NegInf` by RW_TAC std_ss [] \\
     FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT])
 >> RW_TAC std_ss []
 >> `integral m (\x. f e x + SIGMA (\i. f i x) s) =
     integral m (\x. f e x + (\x. SIGMA (\i. f i x) s) x)` by METIS_TAC [] >> POP_ORW
 >> Know `integral m (\x. f e x + (\x. SIGMA (\i. f i x) s) x) =
          integral m (f e) + integral m (\x. SIGMA (\i. f i x) s)`
 >- (MATCH_MP_TAC integral_add >> fs [IN_INSERT] \\
     Reverse CONJ_TAC
     >- (GEN_TAC >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF >> RW_TAC std_ss []) \\
     MATCH_MP_TAC integrable_sum >> METIS_TAC []) >> Rewr'
 >> Know `integral m (\x. SIGMA (\i. f i x) s) = SIGMA (\i. integral m (f i)) s`
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> fs [IN_INSERT]) >> Rewr'
 >> (MP_TAC o Q.SPEC `e` o UNDISCH o Q.SPECL [`(\i. integral m (f i))`,`s`] o
     INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY
 >> Know `!x. x IN e INSERT s ==> (\i. integral m (f i)) x <> NegInf`
 >- (RW_TAC std_ss [] >> METIS_TAC [integrable_finite_integral])
 >> RW_TAC std_ss []
 >> FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]);

(* general case: `(m_space m)` can be infinite but `IMAGE f (m_space)` is finite.
   e.g. m_space m = univ(:real) but f() only takes values from a finite set.

   added `integrable m f` into antecedents, otherwise `integral m f` is not defined;
   added `measure m (m_space m) < PosInf` into antecedents
 *)
val finite_support_integral_reduce = store_thm
  ("finite_support_integral_reduce",
  ``!m f. measure_space m /\ f IN measurable (m_space m,measurable_sets m) Borel /\
         (!x. x IN m_space m ==> f x <> NegInf /\ f x <> PosInf) /\
          FINITE (IMAGE f (m_space m)) /\
          integrable m f /\ measure m (m_space m) < PosInf ==>
         (integral m f = finite_space_integral m f)``,
    rpt STRIP_TAC
 >> `?c1 n. BIJ c1 (count n) (IMAGE f (m_space m))`
       by RW_TAC std_ss [GSYM FINITE_BIJ_COUNT_EQ]
 >> `?c. !i. (i IN count n ==> (c1 i = Normal (c i)))`
       by (Q.EXISTS_TAC `\i. @r. c1 i = Normal r`
           >> RW_TAC std_ss []
           >> SELECT_ELIM_TAC
           >> RW_TAC std_ss []
           >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
           >> `?t. (c1 i = f t) /\ t IN m_space m` by METIS_TAC []
           >> METIS_TAC [extreal_cases])
 >> `FINITE (count n)` by RW_TAC std_ss [FINITE_COUNT]
 >> `!i j. i <> j /\ (i IN count n) /\ (j IN count n) ==>
           DISJOINT (PREIMAGE f {Normal (c i)}) (PREIMAGE f {Normal (c j)})`
        by (RW_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_PREIMAGE, IN_INTER, NOT_IN_EMPTY,
                           IN_SING]
            >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
            >> METIS_TAC [])
 >> `!i. PREIMAGE f {Normal (c i)} INTER m_space m IN measurable_sets m`
      by (RW_TAC std_ss []
          >> `PREIMAGE f {Normal (c i)} = {x | f x = Normal (c i)}`
              by RW_TAC std_ss [EXTENSION,IN_PREIMAGE,GSPECIFICATION,IN_SING]
          >> METIS_TAC [IN_MEASURABLE_BOREL_ALL, integrable_def, space_def, m_space_def,
                        subsets_def, measurable_sets_def])
 >> Know `pos_simple_fn m (fn_plus f)
            (count n) (\i. PREIMAGE f {Normal (c i)} INTER m_space m)
            (\i. if 0 <= (c i) then c i else 0)`
 >- (RW_TAC std_ss [pos_simple_fn_def, FINITE_COUNT, FN_PLUS_POS, FN_MINUS_POS] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       Reverse (RW_TAC real_ss [fn_plus_def])
       >- (FULL_SIMP_TAC std_ss [extreal_lt_def, indicator_fn_def, IN_INTER]
           >> (MP_TAC o Q.SPEC `(\i. Normal (if 0 <= c i then c i else 0) *
                                    if t IN PREIMAGE f {Normal (c i)} then 1 else 0)` o
               UNDISCH o Q.ISPEC `count n`) EXTREAL_SUM_IMAGE_IN_IF
           >> Know `(!x. x IN count n ==>
                         (\i. Normal (if 0 <= c i then c i else 0) *
                              if t IN PREIMAGE f {Normal (c i)} then 1 else 0) x <> NegInf)`
           >- (GEN_TAC >> DISCH_TAC >> BETA_TAC \\
               MATCH_MP_TAC pos_not_neginf \\
               Cases_on `~(0 <= c x)` >- fs [GSYM extreal_of_num_def, mul_lzero, le_refl] \\
               fs [] \\
               Cases_on `t NOTIN (PREIMAGE f {Normal (c x)})` >- fs [mul_rzero, le_refl] \\
               fs [mul_rone] >> fs [extreal_le_eq, extreal_of_num_def])
           >> RW_TAC std_ss [] >> POP_ASSUM K_TAC
           >> Suff `(\x. if x IN count n then Normal (if 0 <= c x then c x else 0) *
                       if t IN PREIMAGE f {Normal (c x)} then 1 else 0 else 0) =
                    (\x. 0)`
           >- RW_TAC std_ss [EXTREAL_SUM_IMAGE_ZERO]
           >> RW_TAC std_ss [FUN_EQ_THM]
           >> Cases_on `~(x IN count n)` >- RW_TAC std_ss []
           >> Reverse (RW_TAC std_ss [mul_rone, mul_rzero])
           >- RW_TAC std_ss [extreal_of_num_def]
           >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_COUNT, IN_IMAGE,
                                    IN_PREIMAGE, IN_SING]
           >> METIS_TAC [le_antisym, extreal_le_def, extreal_of_num_def])
       >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
       >> `?i. i IN count n /\ (f t = Normal (c i))` by METIS_TAC []
       >> `count n = i INSERT ((count n) DELETE i)`
            by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DELETE] >> METIS_TAC [])
       >> POP_ORW
       >> Know `!x. x IN (i INSERT count n DELETE i) ==>
                   (\i. Normal (if 0 <= c i then c i else 0) *
                        indicator_fn (PREIMAGE f {Normal (c i)} INTER m_space m) t) x <> NegInf`
       >- (GEN_TAC >> DISCH_TAC >> BETA_TAC \\
           MATCH_MP_TAC pos_not_neginf \\
          `0 <= indicator_fn (PREIMAGE f {Normal (c x)} INTER m_space m) t`
                by PROVE_TAC [INDICATOR_FN_POS] \\
           Suff `0 <= Normal (if 0 <= c x then c x else 0)` >- PROVE_TAC [le_mul] \\
           Suff `0 <= if 0 <= c x then c x else 0`
           >- PROVE_TAC [extreal_of_num_def, extreal_le_eq] \\
           Cases_on `0 <= c x` >> RW_TAC real_ss [])
       >> Reverse (RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM, FINITE_DELETE, GSYM extreal_of_num_def,
                   mul_lzero, DELETE_DELETE, add_lzero])
       >- METIS_TAC [extreal_of_num_def, extreal_lt_eq, lt_antisym, real_lt]
       >> RW_TAC std_ss [indicator_fn_def, IN_INTER, DELETE_DELETE, mul_rzero, add_lzero,
                         IN_PREIMAGE, IN_SING, mul_rone]
       >> Suff `SIGMA (\i'. Normal (if 0 <= c i' then c i' else 0) *
                            if c i = c i' then 1 else 0) (count n DELETE i) = 0`
       >- RW_TAC std_ss [add_rzero]
       >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
       >> Reverse (RW_TAC std_ss [FINITE_DELETE, mul_rone, mul_rzero])
       >- RW_TAC std_ss [extreal_of_num_def]
       >> METIS_TAC [IN_DELETE],
       (* goal 2 (of 4) *)
       RW_TAC real_ss [],
       (* goal 3 (of 4) *)
       FULL_SIMP_TAC std_ss [DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY, IN_PREIMAGE, EXTENSION, IN_SING]
       >> METIS_TAC [],
       (* goal 4 (of 4) *)
       RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_PREIMAGE, IN_SING, IN_INTER]
       >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF]
       >> METIS_TAC [IN_IMAGE] ])
 >> DISCH_TAC
 >> Know `pos_simple_fn m (fn_minus f)
            (count n) (\i. PREIMAGE f {Normal (c i)} INTER m_space m)
            (\i. if c i <= 0 then ~(c i) else 0)`
 >- (RW_TAC std_ss [pos_simple_fn_def, FINITE_COUNT, FN_PLUS_POS, FN_MINUS_POS] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       Reverse (RW_TAC real_ss [fn_minus_def])
       >- (FULL_SIMP_TAC std_ss [extreal_lt_def, indicator_fn_def, IN_INTER]
           >> (MP_TAC o Q.SPEC `(\i. Normal (if c i <= 0 then -c i else 0) *
                                     if t IN PREIMAGE f {Normal (c i)} then 1 else 0)` o
               UNDISCH o Q.ISPEC `count n`) EXTREAL_SUM_IMAGE_IN_IF
           >> Know `(!x. x IN count n ==>
                        (\i. Normal (if c i <= 0 then (-c i) else 0) *
                             if t IN PREIMAGE f {Normal (c i)} then 1 else 0) x <> NegInf)`
           >- (GEN_TAC >> DISCH_TAC >> BETA_TAC \\
               MATCH_MP_TAC pos_not_neginf \\
               Cases_on `~(c x <= 0)` >- fs [GSYM extreal_of_num_def, mul_lzero, le_refl] \\
               fs [] \\
               Cases_on `t NOTIN (PREIMAGE f {Normal (c x)})` >- fs [mul_rzero, le_refl] \\
               fs [mul_rone] >> fs [extreal_le_eq, extreal_of_num_def])
           >> RW_TAC std_ss [] >> POP_ASSUM K_TAC
           >> Suff `(\x. if x IN count n then Normal (if c x <= 0 then -c x else 0) *
                         if t IN PREIMAGE f {Normal (c x)} then 1 else 0 else 0) = (\x. 0)`
           >- RW_TAC std_ss [EXTREAL_SUM_IMAGE_ZERO]
           >> RW_TAC std_ss [FUN_EQ_THM]
           >> Cases_on `~(x IN count n)`
           >- RW_TAC std_ss []
           >> Reverse (RW_TAC std_ss [mul_rone, mul_rzero])
           >- RW_TAC std_ss [extreal_of_num_def]
           >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_COUNT, IN_IMAGE,
                                    IN_PREIMAGE, IN_SING]
           >> METIS_TAC [REAL_LE_ANTISYM, extreal_of_num_def, REAL_NEG_0, extreal_le_def, IN_COUNT])
       >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
       >> `?i. i IN count n /\ (f t = Normal (c i))` by METIS_TAC []
       >> `count n = i INSERT ((count n) DELETE i)`
            by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DELETE] >> METIS_TAC [])
       >> POP_ORW
       >> Know `!x. x IN (i INSERT count n DELETE i) ==>
                   (\i. Normal (if c i <= 0 then (-c i) else 0) *
                        indicator_fn (PREIMAGE f {Normal (c i)} INTER m_space m) t) x <> NegInf`
       >- (GEN_TAC >> DISCH_TAC >> BETA_TAC \\
           MATCH_MP_TAC pos_not_neginf \\
          `0 <= indicator_fn (PREIMAGE f {Normal (c x)} INTER m_space m) t`
                by PROVE_TAC [INDICATOR_FN_POS] \\
           Suff `0 <= Normal (if c x <= 0 then (-c x) else 0)` >- PROVE_TAC [le_mul] \\
           Suff `0 <= if c x <= 0 then (-c x) else 0`
           >- PROVE_TAC [extreal_of_num_def, extreal_le_eq] \\
           Cases_on `c x <= 0` >> fs [] >> PROVE_TAC [])
       >> Reverse (RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM, FINITE_DELETE, GSYM extreal_of_num_def,
                                  mul_lzero, DELETE_DELETE, add_lzero])
       >- METIS_TAC [extreal_lt_eq, real_lt, extreal_of_num_def, lt_antisym]
       >> RW_TAC std_ss [indicator_fn_def, IN_INTER, DELETE_DELETE, mul_rzero,
                         add_lzero, IN_PREIMAGE, IN_SING, mul_rone]
       >> Suff `SIGMA (\i'. Normal (if c i' <= 0 then -c i' else 0) *
                            if c i = c i' then 1 else 0) (count n DELETE i) = 0`
       >- METIS_TAC [add_rzero, extreal_ainv_def]
       >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
       >> Reverse (RW_TAC std_ss [FINITE_DELETE, mul_rone, mul_rzero])
       >- RW_TAC std_ss [extreal_of_num_def]
       >> METIS_TAC [IN_DELETE],
       (* goal 2 (of 4) *)
       RW_TAC real_ss [] >> METIS_TAC [REAL_LE_NEG, REAL_NEG_0],
       (* goal 3 (of 4) *)
       FULL_SIMP_TAC std_ss [DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY, IN_PREIMAGE, EXTENSION, IN_SING]
       >> METIS_TAC [],
       (* goal 4 (of 4) *)
       RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_PREIMAGE, IN_SING, IN_INTER]
       >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF]
       >> METIS_TAC [IN_IMAGE] ])
 >> DISCH_TAC
 >> RW_TAC std_ss [finite_space_integral_def]
 >> `pos_fn_integral m (fn_plus f) =
     pos_simple_fn_integral m (count n) (\i. PREIMAGE f {Normal (c i)} INTER m_space m)
                              (\i. if 0 <= c i then c i else 0)`
            by METIS_TAC [pos_fn_integral_pos_simple_fn]
 >> `pos_fn_integral m (fn_minus f) =
     pos_simple_fn_integral m (count n) (\i. PREIMAGE f {Normal (c i)} INTER m_space m)
                              (\i. if c i <= 0 then -c i else 0)`
            by METIS_TAC [pos_fn_integral_pos_simple_fn]
 >> FULL_SIMP_TAC std_ss [integral_def, pos_simple_fn_integral_def]
 >> Know `!x. (PREIMAGE f {x}) INTER (m_space m) IN (measurable_sets m)`
 >- (fs [IN_MEASURABLE, space_def, subsets_def] \\
     GEN_TAC >> FIRST_X_ASSUM MATCH_MP_TAC \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_SING])
 >> DISCH_TAC
 >> Know `!x. measure m (PREIMAGE f {x} INTER m_space m) < PosInf`
 >- (GEN_TAC >> MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC `measure m (m_space m)` >> art [] \\
     MATCH_MP_TAC INCREASING >> art [INTER_SUBSET] \\
     PROVE_TAC [MEASURE_SPACE_MSPACE_MEASURABLE, MEASURE_SPACE_INCREASING])
 >> DISCH_TAC
 (* applying EXTREAL_SUM_IMAGE_SUB *)
 >> Know `SIGMA (\i. Normal (if 0 <= c i then c i else 0) *
                     measure m (PREIMAGE f {Normal (c i)} INTER m_space m)) (count n) -
          SIGMA (\i. Normal (if c i <= 0 then (-c i) else 0) *
                     measure m (PREIMAGE f {Normal (c i)} INTER m_space m)) (count n) =
          SIGMA (\x. (\i. Normal (if 0 <= c i then c i else 0) *
                          measure m (PREIMAGE f {Normal (c i)} INTER m_space m)) x -
                     (\i. Normal (if c i <= 0 then (-c i) else 0) *
                          measure m (PREIMAGE f {Normal (c i)} INTER m_space m)) x) (count n)`
 >- (MATCH_MP_TAC EQ_SYM \\
     irule EXTREAL_SUM_IMAGE_SUB >> art [] \\
     DISJ1_TAC \\ (* or DISJ2_TAC, doesn't matter *)
     GEN_TAC >> DISCH_TAC >> BETA_TAC \\
     CONJ_TAC
     >- (MATCH_MP_TAC pos_not_neginf \\
        `0 <= if 0 <= c x then c x else 0` by SRW_TAC [] [] \\
        `0 <= Normal (if 0 <= c x then c x else 0)`
          by PROVE_TAC [extreal_of_num_def, extreal_le_eq] \\
         Suff `0 <= measure m (PREIMAGE f {Normal (c x)} INTER m_space m)` >- METIS_TAC [le_mul] \\
         Suff `(PREIMAGE f {Normal (c x)} INTER m_space m) IN measurable_sets m`
         >- PROVE_TAC [measure_space_def, positive_def, measure_def] \\
         fs [IN_MEASURABLE]) \\
     Cases_on `0 < c x`
     >- (`~(c x <= 0)` by METIS_TAC [real_lte] \\
         fs [GSYM extreal_of_num_def, mul_lzero] \\
         fs [extreal_of_num_def, extreal_not_infty]) \\
    `c x <= 0` by METIS_TAC [real_lte] >> fs [] \\
    `0 <= -c x` by PROVE_TAC [REAL_NEG_GE0] \\
     METIS_TAC [mul_not_infty, lt_infty]) >> Rewr'
 >> BETA_TAC
 >> Know `!x. Normal (if 0 <= c x then c x else 0) *
              measure m (PREIMAGE f {Normal (c x)} INTER m_space m) -
              Normal (if c x <= 0 then (-c x) else 0) *
              measure m (PREIMAGE f {Normal (c x)} INTER m_space m) =
              Normal ((if 0 <= c x then c x else 0) - if c x <= 0 then (-c x) else 0) *
              measure m (PREIMAGE f {Normal (c x)} INTER m_space m)`
 >- (GEN_TAC >> REWRITE_TAC [GSYM extreal_sub_def] \\
     MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC sub_rdistrib \\
     REWRITE_TAC [extreal_not_infty] \\
     CONJ_TAC
     >- (MATCH_MP_TAC pos_not_neginf \\
         IMP_RES_TAC MEASURE_SPACE_POSITIVE >> PROVE_TAC [positive_def]) \\
     PROVE_TAC [lt_infty]) >> Rewr'
 >> `!x. ((if 0 <= c x then c x else 0) - if c x <= 0 then -c x else 0) = c x`
      by (RW_TAC real_ss []
          >> METIS_TAC [REAL_LE_ANTISYM, REAL_ADD_RID, real_lt, REAL_LT_ANTISYM])
 >> POP_ORW
 >> (MP_TAC o Q.ISPEC `c1:num->extreal` o UNDISCH o Q.ISPEC `count n`)
        EXTREAL_SUM_IMAGE_IMAGE
 >> Know `INJ c1 (count n) (IMAGE c1 (count n))`
 >- (FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, IN_IMAGE] >> METIS_TAC [])
 >> SIMP_TAC std_ss []
 >> NTAC 2 STRIP_TAC
 >> POP_ASSUM (MP_TAC o Q.SPEC `(\r. r * (measure m (PREIMAGE f {r} INTER m_space m)))`)
 >> SIMP_TAC std_ss [o_DEF]
 >> `(IMAGE c1 (count n)) = (IMAGE f (m_space m))`
     by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_IMAGE]
         >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
         >> METIS_TAC []) >> art []
 >> Know `!x. x IN IMAGE f (m_space m) ==>
              x * measure m (PREIMAGE f {x} INTER m_space m) <> PosInf`
 >- (RW_TAC std_ss [IN_IMAGE] \\
     `f x' <> PosInf /\ f x' <> NegInf` by PROVE_TAC [] \\
     `?r. f x' = Normal r` by PROVE_TAC [extreal_cases] >> art [] \\
     Cases_on `0 <= r` >- METIS_TAC [mul_not_infty, lt_infty] \\
     `r <= 0` by PROVE_TAC [REAL_NOT_LE, REAL_LT_IMP_LE] \\
     Suff `measure m (PREIMAGE f {Normal r} INTER m_space m) <> NegInf`
     >- METIS_TAC [mul_not_infty] \\
     MATCH_MP_TAC pos_not_neginf \\
     IMP_RES_TAC MEASURE_SPACE_POSITIVE \\
     METIS_TAC [positive_def])
 >> RW_TAC std_ss []
 >> (MATCH_MP_TAC o UNDISCH o Q.SPEC `count n` o INST_TYPE [``:'a`` |-> ``:num``])
        EXTREAL_SUM_IMAGE_EQ
 >> RW_TAC std_ss []
 >> DISJ2_TAC >> GEN_TAC >> DISCH_TAC
 >> Cases_on `0 <= c x` >- METIS_TAC [mul_not_infty, lt_infty]
 >> `c x <= 0` by PROVE_TAC [REAL_NOT_LE, REAL_LT_IMP_LE]
 >> Suff `measure m (PREIMAGE f {Normal (c x)} INTER m_space m) <> NegInf`
 >- METIS_TAC [mul_not_infty]
 >> MATCH_MP_TAC pos_not_neginf
 >> IMP_RES_TAC MEASURE_SPACE_POSITIVE
 >> METIS_TAC [positive_def]);

(* special case of "finite_support_integral_reduce": (m_space m) is finite.

   added `measure m (m_space m) < PosInf` into antecedents.
   TODO: remove `integrable m f` and prove it.
 *)
Theorem finite_space_integral_reduce :
    !m f. measure_space m /\ f IN measurable (m_space m,measurable_sets m) Borel /\
          (!x. x IN m_space m ==> f x <> NegInf /\ f x <> PosInf) /\
          FINITE (m_space m) /\ measure m (m_space m) < PosInf /\
          integrable m f
      ==> (integral m f = finite_space_integral m f)
Proof
    rpt STRIP_TAC
 >> `FINITE (IMAGE f (m_space m))` by PROVE_TAC [IMAGE_FINITE]
 >> MATCH_MP_TAC finite_support_integral_reduce >> art []
QED

(* No need to have PREIMAGE if `POW (m_space m) = measurable_sets m`.

   Added `measure m (m_space m) < PosInf` into antecedents
 *)
val finite_space_POW_integral_reduce = store_thm
  ("finite_space_POW_integral_reduce",
  ``!m f. measure_space m /\ (POW (m_space m) = measurable_sets m) /\ FINITE (m_space m) /\
          (!x. x IN m_space m ==> f x <> NegInf /\ f x <> PosInf) /\
          measure m (m_space m) < PosInf
      ==> (integral m f = SIGMA (\x. f x * (measure m {x})) (m_space m))``,
    RW_TAC std_ss []
 >> `f IN measurable (m_space m, measurable_sets m) Borel`
        by (RW_TAC std_ss [IN_MEASURABLE_BOREL,IN_FUNSET,IN_UNIV,space_def,subsets_def]
            >- FULL_SIMP_TAC std_ss [measure_space_def]
            >> METIS_TAC [INTER_SUBSET,IN_POW])
 >> `?c n. BIJ c (count n) (m_space m)` by RW_TAC std_ss [GSYM FINITE_BIJ_COUNT_EQ]
 >> `FINITE (count n)` by RW_TAC std_ss [FINITE_COUNT]
 >> `?x. !i. (i IN count n ==> (f (c i) = Normal (x i)))`
       by (Q.EXISTS_TAC `(\i. @r. f (c i) = Normal r)`
           >> RW_TAC std_ss []
           >> SELECT_ELIM_TAC
           >> RW_TAC std_ss []
           >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
           >> METIS_TAC [extreal_cases])
 >> `!i. i IN count n ==> {c i } IN measurable_sets m`
       by METIS_TAC [IN_POW, IN_SING, BIJ_DEF, SURJ_DEF, SUBSET_DEF]
 >> Know `pos_simple_fn m (fn_plus f)
            (count n) (\i. {c i}) (\i. if 0 <= x i then x i else 0)`
 >- (RW_TAC std_ss [pos_simple_fn_def, FINITE_COUNT, FN_PLUS_POS, FN_MINUS_POS] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       Reverse (RW_TAC real_ss [fn_plus_def])
       >- (FULL_SIMP_TAC std_ss [extreal_lt_def, IN_INTER]
           >> (MP_TAC o Q.SPEC `(\i. Normal (if 0 <= x i then x i else 0) *
                                     indicator_fn {c i} t)` o
               UNDISCH o Q.ISPEC `count n`) EXTREAL_SUM_IMAGE_IN_IF
           >> Know `!x'. x' IN count n ==>
                         (\i. Normal (if 0 <= x i then x i else 0) *
                              indicator_fn {c i} t) x' <> NegInf`
           >- (GEN_TAC >> DISCH_TAC >> BETA_TAC >> rename1 `i IN count n` \\
               MATCH_MP_TAC pos_not_neginf \\
               Cases_on `~(0 <= x i)` >- fs [GSYM extreal_of_num_def, mul_lzero, le_refl] \\
               fs [] \\
               MATCH_MP_TAC le_mul \\
               CONJ_TAC >- fs [extreal_le_eq, extreal_of_num_def] \\
               REWRITE_TAC [INDICATOR_FN_POS])
           >> RW_TAC std_ss [] >> POP_ASSUM K_TAC
           >> Suff `(\x'. if x' IN count n then Normal (if 0 <= x x' then x x' else 0) *
                          indicator_fn {c x'} t else 0) = (\x. 0)`
           >- RW_TAC std_ss [EXTREAL_SUM_IMAGE_ZERO]
           >> RW_TAC std_ss [FUN_EQ_THM]
           >> Cases_on `~(x' IN count n)` >- RW_TAC std_ss []
           >> Reverse (RW_TAC std_ss [mul_rone, mul_rzero])
           >- RW_TAC std_ss [GSYM extreal_of_num_def, mul_lzero]
           >> rename1 `i IN count n`
           >> Cases_on `c i <> t` >- PROVE_TAC [INDICATOR_FN_SING_0, mul_rzero]
           >> fs [INDICATOR_FN_SING_1, mul_rone]
           >> `f t = Normal (x i)` by PROVE_TAC []
           >> `0 <= f t` by PROVE_TAC [extreal_le_eq, extreal_of_num_def]
           >> `f t = 0` by PROVE_TAC [le_antisym, extreal_lt_def]
           >> METIS_TAC [])
       >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
       >> `?i. i IN count n /\ (t = c i)` by METIS_TAC []
       >> FULL_SIMP_TAC std_ss []
       >> `count n = i INSERT ((count n) DELETE i)`
            by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DELETE] >> METIS_TAC [])
       >> POP_ORW
       >> Know `!x'. x' IN (i INSERT count n DELETE i) ==>
                    (\i'. Normal (if 0 <= x i' then x i' else 0) *
                          indicator_fn {c i'} (c i)) x' <> NegInf`
       >- (GEN_TAC >> DISCH_TAC >> BETA_TAC \\
           MATCH_MP_TAC pos_not_neginf \\
           MATCH_MP_TAC le_mul >> REWRITE_TAC [INDICATOR_FN_POS] \\
           METIS_TAC [extreal_le_eq, extreal_of_num_def, le_refl])
       >> Reverse (RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM, FINITE_DELETE, GSYM extreal_of_num_def,
                                  mul_lzero, DELETE_DELETE, add_lzero])
       >- METIS_TAC [extreal_of_num_def, extreal_lt_eq, lt_antisym, real_lt]
       >> RW_TAC std_ss [indicator_fn_def, IN_INTER, DELETE_DELETE, mul_rzero, add_lzero,
                         IN_PREIMAGE, IN_SING, mul_rone]
       >> Suff `SIGMA (\i'. Normal (if 0 <= x i' then x i' else 0) *
                            if c i = c i' then 1 else 0) (count n DELETE i) = 0`
       >- RW_TAC std_ss [add_rzero]
       >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
       >> Reverse (RW_TAC std_ss [FINITE_DELETE, mul_rone, mul_rzero])
       >- RW_TAC std_ss [extreal_of_num_def]
       >> METIS_TAC [IN_DELETE],
       (* goal 2 (of 4) *)
       RW_TAC real_ss [],
       (* goal 3 (of 4) *)
       FULL_SIMP_TAC std_ss [DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY, IN_PREIMAGE, EXTENSION,
                             IN_SING, BIJ_DEF, INJ_DEF]
       >> METIS_TAC [],
       (* goal 4 (of 4) *)
       RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_PREIMAGE, IN_SING, IN_INTER]
       >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF]
       >> METIS_TAC [IN_IMAGE] ])
 >> DISCH_TAC
 >> Know `pos_simple_fn m (fn_minus f)
            (count n) (\i. {c i}) (\i. if x i <= 0 then -(x i) else 0)`
 >- (RW_TAC std_ss [pos_simple_fn_def, FINITE_COUNT, FN_MINUS_POS, FN_MINUS_POS] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       Reverse (RW_TAC real_ss [fn_minus_def])
       >- (FULL_SIMP_TAC std_ss [extreal_lt_def, IN_INTER]
           >> (MP_TAC o Q.SPEC `(\i. Normal (if x i <= 0 then -x i else 0) *
                                     indicator_fn {c i} t)` o
               UNDISCH o Q.ISPEC `count n`) EXTREAL_SUM_IMAGE_IN_IF
           >> Know `!x'. x' IN count n ==>
                         (\i. Normal (if x i <= 0 then (-x i) else 0) *
                              indicator_fn {c i} t) x' <> NegInf`
           >- (GEN_TAC >> DISCH_TAC >> BETA_TAC \\
               MATCH_MP_TAC pos_not_neginf \\
               Cases_on `~(x x' <= 0)` >- fs [GSYM extreal_of_num_def, mul_lzero, le_refl] \\
               fs [] \\
               MATCH_MP_TAC le_mul >> REWRITE_TAC [INDICATOR_FN_POS] \\
              `0 <= -(x x')` by PROVE_TAC [REAL_LE_NEG, REAL_NEG_0] \\
               fs [extreal_le_eq, extreal_of_num_def])
           >> RW_TAC std_ss [] >> POP_ASSUM K_TAC
           >> Suff `(\x'. if x' IN count n then Normal (if x x' <= 0 then -(x x') else 0) *
                          indicator_fn {c x'} t else 0) = (\x. 0)`
           >- RW_TAC std_ss [EXTREAL_SUM_IMAGE_ZERO]
           >> RW_TAC std_ss [FUN_EQ_THM]
           >> Cases_on `~(x' IN count n)` >- RW_TAC std_ss []
           >> Reverse (RW_TAC std_ss [mul_rone, mul_rzero])
           >- RW_TAC std_ss [GSYM extreal_of_num_def, mul_lzero]
           >> rename1 `i IN count n`
           >> Cases_on `c i <> t` >- PROVE_TAC [INDICATOR_FN_SING_0, mul_rzero]
           >> fs [INDICATOR_FN_SING_1, mul_rone]
           >> `f t = Normal (x i)` by PROVE_TAC []
           >> `f t <= 0` by PROVE_TAC [extreal_le_eq, extreal_of_num_def]
           >> `f t = 0` by PROVE_TAC [le_antisym]
           >> `x i = 0` by PROVE_TAC [extreal_of_num_def, extreal_11]
           >> `-x i = 0` by PROVE_TAC [REAL_NEG_0]
           >> METIS_TAC [extreal_of_num_def])
       >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
       >> `?i. i IN count n /\ (t = c i)` by METIS_TAC []
       >> FULL_SIMP_TAC std_ss []
       >> `count n = i INSERT ((count n) DELETE i)`
            by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DELETE] >> METIS_TAC [])
       >> POP_ORW
       >> Know `!x'. x' IN (i INSERT count n DELETE i) ==>
                    (\i'. Normal (if x i' <= 0 then -x i' else 0) *
                          indicator_fn {c i'} (c i)) x' <> NegInf`
       >- (GEN_TAC >> DISCH_TAC >> BETA_TAC \\
           MATCH_MP_TAC pos_not_neginf \\
           MATCH_MP_TAC le_mul >> REWRITE_TAC [INDICATOR_FN_POS] \\
           Cases_on `x x' <= 0`
           >- (ASM_SIMP_TAC std_ss [] \\
               `0 <= -x x'` by PROVE_TAC [REAL_LE_NEG, REAL_NEG_0] \\
               PROVE_TAC [extreal_of_num_def, extreal_le_eq]) \\
           ASM_SIMP_TAC std_ss [GSYM extreal_of_num_def, le_refl])
       >> Reverse (RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM, FINITE_DELETE, GSYM extreal_of_num_def,
                                  mul_lzero, DELETE_DELETE, add_lzero])
       >- METIS_TAC [extreal_of_num_def, extreal_lt_eq, lt_antisym, real_lt]
       >> RW_TAC std_ss [indicator_fn_def, IN_INTER, DELETE_DELETE, mul_rzero, add_lzero,
                         IN_PREIMAGE, IN_SING, mul_rone]
       >> Suff `SIGMA (\i'. Normal (if x i' <= 0 then -(x i') else 0) *
                      if c i = c i' then 1 else 0) (count n DELETE i) = 0`
       >- RW_TAC std_ss [add_rzero, extreal_ainv_def]
       >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
       >> Reverse (RW_TAC std_ss [FINITE_DELETE, mul_rone, mul_rzero])
       >- RW_TAC std_ss [extreal_of_num_def]
       >> METIS_TAC [IN_DELETE],
       (* goal 2 (of 4) *)
       METIS_TAC [REAL_LE_REFL, REAL_LE_NEG, REAL_NEG_0],
       (* goal 3 (of 4) *)
       FULL_SIMP_TAC std_ss [DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY, IN_PREIMAGE, EXTENSION,
                             IN_SING, BIJ_DEF, INJ_DEF]
       >> METIS_TAC [],
       (* goal 4 (of 4) *)
       RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_PREIMAGE, IN_SING, IN_INTER]
       >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF]
       >> METIS_TAC [IN_IMAGE] ])
 >> DISCH_TAC
 >> RW_TAC std_ss [integral_def]
 >> (MP_TAC o Q.SPECL [`m`,`fn_plus f`,`count n`,`(\i. {c i})`,
                       `(\i. if 0 <= x i then x i else 0)`]) pos_fn_integral_pos_simple_fn
 >> (MP_TAC o Q.SPECL [`m`,`fn_minus f`,`count n`,`(\i. {c i})`,
                       `(\i. if x i <= 0 then -(x i) else 0)`]) pos_fn_integral_pos_simple_fn
 >> RW_TAC std_ss [pos_simple_fn_integral_def, extreal_sub_def, GSYM REAL_SUM_IMAGE_SUB,
                   GSYM REAL_SUB_RDISTRIB]
 >> `!x. ((if 0 <= x i then x i else 0) - if x i <= 0:real then -(x i) else 0) = x i`
      by (RW_TAC real_ss [REAL_SUB_RNEG]
          >> METIS_TAC [REAL_LE_ANTISYM, REAL_ADD_RID, real_lt, REAL_LT_ANTISYM])
 >> RW_TAC std_ss []
 >> (MP_TAC o Q.ISPEC `c:num->'a` o UNDISCH o Q.ISPEC `count n`) EXTREAL_SUM_IMAGE_IMAGE
 >> Know `INJ c (count n) (IMAGE c (count n))`
 >- (FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, IN_IMAGE] >> METIS_TAC [])
 >> `(IMAGE c (count n)) = (m_space m)`
        by (ONCE_REWRITE_TAC [EXTENSION] >> RW_TAC std_ss [IN_IMAGE]
            >> FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, IN_IMAGE]
            >> METIS_TAC [])
 >> RW_TAC std_ss []
 >> POP_ASSUM (MP_TAC o Q.SPEC `(\x. f x * (measure m {x}))`)
 >> Know `!x. x IN m_space m ==> f x * measure m {x} <> PosInf`
 >- (Q.PAT_ASSUM `IMAGE c (count n) = m_space m` (ONCE_REWRITE_TAC o wrap o SYM) \\
     RW_TAC std_ss [IN_IMAGE] >> rename1 `j IN count n` \\
     `{c j} IN measurable_sets m` by METIS_TAC [IN_POW, SUBSET_DEF, IN_SING, IN_IMAGE] \\
     `(c j) IN m_space m` by METIS_TAC [IN_IMAGE] \\
     Know `measure m {c j} <> NegInf`
     >- (MATCH_MP_TAC pos_not_neginf >> PROVE_TAC [measure_space_def, positive_def]) \\
     Know `measure m {c j} <> PosInf`
     >- (REWRITE_TAC [lt_infty] >> MATCH_MP_TAC let_trans \\
         Q.EXISTS_TAC `measure m (m_space m)` >> art [] \\
         MATCH_MP_TAC INCREASING >> art [] \\
         CONJ_TAC >- PROVE_TAC [MEASURE_SPACE_INCREASING] \\
         CONJ_TAC >- PROVE_TAC [SUBSET_DEF, IN_SING] \\
         IMP_RES_TAC MEASURE_SPACE_MSPACE_MEASURABLE) \\
     NTAC 2 DISCH_TAC \\
     METIS_TAC [mul_not_infty2])
 >> RW_TAC std_ss [o_DEF]
 (* applying EXTREAL_SUM_IMAGE_SUB *)
 >> Know `SIGMA (\i. Normal (if 0 <= x i then x i else 0) * measure m {c i}) (count n) -
          SIGMA (\i. Normal (if x i <= 0 then (-x i) else 0) * measure m {c i}) (count n) =
          SIGMA (\j. (\i. Normal (if 0 <= x i then x i else 0) * measure m {c i}) j -
                     (\i. Normal (if x i <= 0 then (-x i) else 0) * measure m {c i}) j) (count n)`
 >- (MATCH_MP_TAC EQ_SYM \\
     irule EXTREAL_SUM_IMAGE_SUB >> art [] \\
     DISJ1_TAC \\ (* or DISJ2_TAC, doesn't matter *)
     GEN_TAC >> DISCH_TAC >> BETA_TAC >> rename1 `j IN count n` \\
     CONJ_TAC
     >- (MATCH_MP_TAC pos_not_neginf \\
        `0 <= if 0 <= x j then x j else 0` by SRW_TAC [] [] \\
        `0 <= Normal (if 0 <= x j then x j else 0)`
          by PROVE_TAC [extreal_of_num_def, extreal_le_eq] \\
         MATCH_MP_TAC le_mul >> art [] \\
         Suff `{c j} IN measurable_sets m`
         >- PROVE_TAC [measure_space_def, positive_def, measure_def] \\
         METIS_TAC [IN_POW, SUBSET_DEF, IN_SING, IN_IMAGE]) \\
     Cases_on `0 < x j`
     >- (`~(x j <= 0)` by METIS_TAC [real_lte] \\
         fs [GSYM extreal_of_num_def, mul_lzero] \\
         fs [extreal_of_num_def, extreal_not_infty]) \\
    `x j <= 0` by METIS_TAC [real_lte] >> fs [] \\
    `0 <= -x j` by PROVE_TAC [REAL_NEG_GE0] \\
     Suff `measure m {c j} <> PosInf` >- METIS_TAC [mul_not_infty] \\
     REWRITE_TAC [lt_infty] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC `measure m (m_space m)` >> art [] \\
     MATCH_MP_TAC INCREASING >> art [] \\
     CONJ_TAC >- PROVE_TAC [MEASURE_SPACE_INCREASING] \\
     `(c j) IN m_space m` by METIS_TAC [IN_IMAGE, IN_COUNT] \\
     CONJ_TAC >- PROVE_TAC [SUBSET_DEF, IN_SING] \\
     CONJ_TAC >- METIS_TAC [IN_POW, SUBSET_DEF, IN_SING, IN_IMAGE] \\
     IMP_RES_TAC MEASURE_SPACE_MSPACE_MEASURABLE) >> Rewr'
 >> BETA_TAC
 >> Know `!j. j IN count n ==>
             (Normal (if 0 <= x j then x j else 0) * measure m {c j} -
              Normal (if x j <= 0 then (-x j) else 0) * measure m {c j} =
              Normal ((if 0 <= x j then x j else 0) - if x j <= 0 then (-x j) else 0) *
              measure m {c j})`
 >- (GEN_TAC >> DISCH_TAC \\
     REWRITE_TAC [GSYM extreal_sub_def] \\
     MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC sub_rdistrib \\
     REWRITE_TAC [extreal_not_infty] \\
    `{c j} IN measurable_sets m` by METIS_TAC [IN_POW, SUBSET_DEF, IN_SING, IN_IMAGE] \\
     CONJ_TAC
     >- (MATCH_MP_TAC pos_not_neginf \\
         IMP_RES_TAC MEASURE_SPACE_POSITIVE >> PROVE_TAC [positive_def]) \\
     REWRITE_TAC [lt_infty] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC `measure m (m_space m)` >> art [] \\
     MATCH_MP_TAC INCREASING >> art [] \\
     CONJ_TAC >- PROVE_TAC [MEASURE_SPACE_INCREASING] \\
    `(c j) IN m_space m` by METIS_TAC [IN_IMAGE, IN_COUNT] \\
     CONJ_TAC >- PROVE_TAC [SUBSET_DEF, IN_SING] \\
     IMP_RES_TAC MEASURE_SPACE_MSPACE_MEASURABLE)
 >> DISCH_TAC
 >> `!j. ((if 0 <= x j then x j else 0) - if x j <= 0 then -x j else 0) = x j`
      by (RW_TAC real_ss []
          >> METIS_TAC [REAL_LE_ANTISYM, REAL_ADD_RID, real_lt, REAL_LT_ANTISYM])
 >> Know `SIGMA (\j. Normal (if 0 <= x j then x j else 0) * measure m {c j} -
                     Normal (if x j <= 0 then (-x j) else 0) * measure m {c j}) (count n) =
          SIGMA (\j. Normal ((if 0 <= x j then x j else 0) - if x j <= 0 then -x j else 0) *
                     measure m {c j}) (count n)`
 >- (irule EXTREAL_SUM_IMAGE_EQ >> BETA_TAC >> art [] \\
     DISJ2_TAC \\
     GEN_TAC >> DISCH_TAC >> rename1 `j IN count n` \\
     Q.PAT_X_ASSUM `!j. j IN count n ==> X`
       (fn th => (art [MATCH_MP th (ASSUME ``j IN count n``)])) \\
     Cases_on `0 <= x j`
     >- (Suff `measure m {c j} <> PosInf` >- METIS_TAC [mul_not_infty] \\
         REWRITE_TAC [lt_infty] \\
         MATCH_MP_TAC let_trans \\
         Q.EXISTS_TAC `measure m (m_space m)` >> art [] \\
         MATCH_MP_TAC INCREASING >> art [] \\
         CONJ_TAC >- PROVE_TAC [MEASURE_SPACE_INCREASING] \\
        `(c j) IN m_space m` by METIS_TAC [IN_IMAGE, IN_COUNT] \\
         CONJ_TAC >- PROVE_TAC [SUBSET_DEF, IN_SING] \\
         CONJ_TAC >- METIS_TAC [IN_POW, SUBSET_DEF, IN_SING, IN_IMAGE] \\
         IMP_RES_TAC MEASURE_SPACE_MSPACE_MEASURABLE) \\
    `x j <= 0` by PROVE_TAC [real_lte, REAL_LT_IMP_LE] \\
     Suff `measure m {c j} <> NegInf` >- METIS_TAC [mul_not_infty] \\
     MATCH_MP_TAC pos_not_neginf \\
    `{c j} IN measurable_sets m` by METIS_TAC [IN_POW, SUBSET_DEF, IN_SING, IN_IMAGE] \\
     IMP_RES_TAC MEASURE_SPACE_POSITIVE >> PROVE_TAC [positive_def])
 >> Rewr'
 >> ASM_REWRITE_TAC []
 >> (MATCH_MP_TAC o UNDISCH o Q.SPEC `count n` o INST_TYPE [``:'a`` |-> ``:num``])
        EXTREAL_SUM_IMAGE_EQ
 >> RW_TAC std_ss []
 >> DISJ2_TAC
 >> GEN_TAC >> DISCH_TAC >> rename1 `j IN count n`
 >> `{c j} IN measurable_sets m` by METIS_TAC [IN_POW, SUBSET_DEF, IN_SING, IN_IMAGE]
 >> `(c j) IN m_space m` by METIS_TAC [IN_IMAGE, IN_COUNT]
 >> Cases_on `0 <= x j`
 >- (Suff `measure m {c j} <> PosInf` >- METIS_TAC [mul_not_infty] \\
     REWRITE_TAC [lt_infty] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC `measure m (m_space m)` >> art [] \\
     MATCH_MP_TAC INCREASING >> art [] \\
     CONJ_TAC >- PROVE_TAC [MEASURE_SPACE_INCREASING] \\
     CONJ_TAC >- PROVE_TAC [SUBSET_DEF, IN_SING] \\
     IMP_RES_TAC MEASURE_SPACE_MSPACE_MEASURABLE)
 >> `x j <= 0` by PROVE_TAC [real_lte, REAL_LT_IMP_LE]
 >> Suff `measure m {c j} <> NegInf` >- METIS_TAC [mul_not_infty]
 >> MATCH_MP_TAC pos_not_neginf
 >> IMP_RES_TAC MEASURE_SPACE_POSITIVE
 >> PROVE_TAC [positive_def]);

(* ------------------------------------------------------------------------- *)
(*  The Function Spaces L^p and Important Inequalities [1, Chapter 13]      *)
(* ------------------------------------------------------------------------- *)

(* [1, p.116], not used so far *)
val norm_def = Define
   `norm m u p = if p < PosInf then
                     (integral m (\x. (abs (u x)) powr p)) powr (inv p)
                 else
                     inf {c | 0 < c /\ (measure m {x | c <= abs (u x)} = 0)}`;

(* Proposition 11.5 [1, p.91]

   NOTE: "markov_ineq" in real_lebesgueTheory is a variant [1, p.93] that we shall
   prove latter as a corollary (in extreals).
 *)
Theorem markov_inequality :
    !m f a c. measure_space m /\ integrable m f /\ a IN measurable_sets m /\ 0 < c ==>
              measure m ({x | c <= abs (f x)} INTER a) <=
                inv c * integral m (\x. abs (f x) * indicator_fn a x)
Proof
    rpt STRIP_TAC
 >> Know `{x | c <= abs (f x)} INTER a IN measurable_sets m`
 >- (`{x | c <= abs (f x)} = PREIMAGE (abs o f) {x | c <= x}`
        by (RW_TAC std_ss [EXTENSION, IN_PREIMAGE, o_DEF, GSPECIFICATION]) \\
     `a SUBSET m_space m`
        by (fs [measure_space_def, sigma_algebra_def, algebra_def, subset_class_def,
                space_def, subsets_def]) \\
     `a = m_space m INTER a` by PROVE_TAC [INTER_SUBSET_EQN] >> POP_ORW \\
     REWRITE_TAC [INTER_ASSOC] \\
     MATCH_MP_TAC MEASURE_SPACE_INTER >> art [] \\
     fs [integrable_def] \\
     Know `abs o f IN measurable (m_space m,measurable_sets m) Borel`
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS \\
         Q.EXISTS_TAC `f` >> RW_TAC std_ss [o_DEF, space_def] \\
         fs [measure_space_def]) \\
     DISCH_THEN (STRIP_ASSUME_TAC o
                 (SIMP_RULE std_ss [measurable_def, GSPECIFICATION, space_def, subsets_def])) \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_CR])
 >> DISCH_TAC
 >> `integrable m (abs o f)` by PROVE_TAC [integrable_abs]
 (* special case: c = PosInf *)
 >> Cases_on `c = PosInf`
 >- (fs [extreal_inv_def, GSYM extreal_of_num_def, mul_lzero, le_infty] \\
     REWRITE_TAC [le_lt] >> DISJ2_TAC \\
     irule integrable_infty >> art [] \\
     Q.EXISTS_TAC `abs o f` >> art [] \\
     RW_TAC std_ss [GSPECIFICATION, IN_INTER, o_DEF])
 (* general case *)
 >> Know `measure m ({x | c <= abs (f x)} INTER a) =
          integral m (indicator_fn ({x | c <= abs (f x)} INTER a))`
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC integral_indicator >> art []) >> Rewr'
 >> REWRITE_TAC [INDICATOR_FN_INTER]
 >> Know `integral m (\t. indicator_fn {x | c <= abs (f x)} t * indicator_fn a t) =
          integral m (\t. inv c * (c * indicator_fn {x | c <= abs (f x)} t * indicator_fn a t))`
 >- (REWRITE_TAC [mul_assoc] \\
     `inv c * c = 1` by PROVE_TAC [mul_linv_pos] >> POP_ORW \\
     REWRITE_TAC [mul_lone]) >> Rewr'
 >> `c <> NegInf` by PROVE_TAC [pos_not_neginf, lt_imp_le]
 >> Cases_on `c` >> fs [extreal_of_num_def, extreal_lt_eq]
 >> `r <> 0` by PROVE_TAC [REAL_LT_LE]
 >> `inv (Normal r) = Normal (inv r)` by ASM_SIMP_TAC std_ss [extreal_inv_def] >> POP_ORW
 (* before further moves, we must convert all `integral`s into `pos_fn_intergral`s *)
 >> `0 <= inv r` by PROVE_TAC [REAL_LT_IMP_LE, REAL_LE_INV]
 >> Know `integral m (\t. Normal (inv r) *
                         (Normal r * indicator_fn {x | Normal r <= abs (f x)} t * indicator_fn a t)) =
   pos_fn_integral m (\t. Normal (inv r) *
                         (Normal r * indicator_fn {x | Normal r <= abs (f x)} t * indicator_fn a t))`
 >- (MATCH_MP_TAC integral_pos_fn >> art [] \\
     RW_TAC std_ss [] \\
     MATCH_MP_TAC le_mul >> CONJ_TAC >- art [extreal_of_num_def, extreal_le_eq] \\
     MATCH_MP_TAC le_mul >> Reverse CONJ_TAC >- REWRITE_TAC [INDICATOR_FN_POS] \\
     MATCH_MP_TAC le_mul >> Reverse CONJ_TAC >- REWRITE_TAC [INDICATOR_FN_POS] \\
     REWRITE_TAC [extreal_of_num_def, extreal_le_eq] \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> Rewr'
 >> Know `integral m (\x. abs (f x) * indicator_fn a x) =
   pos_fn_integral m (\x. abs (f x) * indicator_fn a x)`
 >- (MATCH_MP_TAC integral_pos_fn >> art [] \\
     RW_TAC std_ss [] \\
     MATCH_MP_TAC le_mul >> Reverse CONJ_TAC >- REWRITE_TAC [INDICATOR_FN_POS] \\
     REWRITE_TAC [abs_pos]) >> Rewr'
 >> Know `pos_fn_integral m (\x. Normal (inv r) *
                                (\t. Normal r * indicator_fn {x | Normal r <= abs (f x)} t
                                     * indicator_fn a t) x) =
          Normal (inv r) * pos_fn_integral m (\t. Normal r * indicator_fn {x | Normal r <= abs (f x)} t
                                                  * indicator_fn a t)`
 >- (MATCH_MP_TAC pos_fn_integral_cmul >> art [] \\
     RW_TAC std_ss [] \\
     MATCH_MP_TAC le_mul >> Reverse CONJ_TAC >- REWRITE_TAC [INDICATOR_FN_POS] \\
     MATCH_MP_TAC le_mul >> Reverse CONJ_TAC >- REWRITE_TAC [INDICATOR_FN_POS] \\
     REWRITE_TAC [extreal_of_num_def, extreal_le_eq] \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> BETA_TAC >> Rewr'
 >> MATCH_MP_TAC le_lmul_imp
 >> CONJ_TAC >- art [extreal_of_num_def, extreal_le_eq]
 (* now the core of proof: a smart application of `le_trans` *)
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC `pos_fn_integral m
                    (\t. abs (f t) * indicator_fn {x | Normal r <= abs (f x)} t * indicator_fn a t)`
 >> CONJ_TAC
 >- (MATCH_MP_TAC pos_fn_integral_mono \\
     RW_TAC std_ss []
     >- (MATCH_MP_TAC le_mul >> Reverse CONJ_TAC >- REWRITE_TAC [INDICATOR_FN_POS] \\
         MATCH_MP_TAC le_mul >> Reverse CONJ_TAC >- REWRITE_TAC [INDICATOR_FN_POS] \\
         REWRITE_TAC [extreal_of_num_def, extreal_le_eq] \\
         MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
     Cases_on `Normal r <= abs (f x)`
     >- (REWRITE_TAC [GSYM mul_assoc] \\
         MATCH_MP_TAC le_rmul_imp >> art [] \\
         MATCH_MP_TAC le_mul >> REWRITE_TAC [INDICATOR_FN_POS]) \\
     ASM_SIMP_TAC std_ss [indicator_fn_def, GSPECIFICATION, mul_lzero, mul_rzero, le_refl])
 >> MATCH_MP_TAC pos_fn_integral_mono
 >> RW_TAC std_ss []
 >- (MATCH_MP_TAC le_mul >> Reverse CONJ_TAC >- REWRITE_TAC [INDICATOR_FN_POS] \\
     MATCH_MP_TAC le_mul >> Reverse CONJ_TAC >- REWRITE_TAC [INDICATOR_FN_POS] \\
     REWRITE_TAC [abs_pos])
 >> MATCH_MP_TAC le_rmul_imp
 >> REWRITE_TAC [INDICATOR_FN_POS]
 >> `abs (f x) = abs (f x) * 1` by PROVE_TAC [mul_rone]
 >> POP_ASSUM (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites o wrap)
 >> MATCH_MP_TAC le_lmul_imp
 >> REWRITE_TAC [abs_pos, INDICATOR_FN_LE_1]
QED

(* The special version with `a = m_space m`, the part `INTER m_space m` cannot be removed,
   because in general the PREIMAGE of f may go outside of `m_space m`, even it's integrable.
 *)
Theorem markov_ineq : (* c.f. real_lebesgueTheory.markov_ineq *)
    !m f c. measure_space m /\ integrable m f /\ 0 < c ==>
            measure m ({x | c <= abs (f x)} INTER m_space m) <= inv c * integral m (abs o f)
Proof
    RW_TAC std_ss [o_DEF]
 >> MP_TAC (Q.SPECL [`m`, `f`, `m_space m`, `c`] markov_inequality)
 >> Know `m_space m IN measurable_sets m`
 >- (MATCH_MP_TAC (REWRITE_RULE [space_def, subsets_def]
                                (Q.SPEC `(m_space m,measurable_sets m)` ALGEBRA_SPACE)) \\
     fs [measure_space_def, sigma_algebra_def])
 >> RW_TAC std_ss []
 >> Know `integral m (\x. abs (f x)) = integral m (\t. (\x. abs (f x)) t * indicator_fn (m_space m) t)`
 >- (MATCH_MP_TAC integral_mspace >> art [])
 >> BETA_TAC >> Rewr' >> art []
QED

val _ = export_theory ();

(* References:

  [1] Schilling, R.L.: Measures, Integrals and Martingales (Second Edition).
      Cambridge University Press (2017).
  [2] Hunt, G. A., Martingales et processus de Markov, Paris: Dunod, Monogr.
      Soc. Math. France t. 1, 1966.
  [3] Wikipedia: https://en.wikipedia.org/wiki/Pierre_Fatou
  [4] Wikipedia: https://en.wikipedia.org/wiki/Beppo_Levi
  [5] Wikipedia: https://en.wikipedia.org/wiki/Giuseppe_Vitali
  [6] Shiryaev, A.N.: Probability-1. Springer-Verlag New York (2016).
 *)
