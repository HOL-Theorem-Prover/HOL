(* ------------------------------------------------------------------------- *)
(* Lebesgue Integrals defined on the extended real numbers [2]               *)
(* Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar                         *)
(* HVG Group, Concordia University, Montreal                                 *)
(* ------------------------------------------------------------------------- *)
(* Based on the work of Aaron Coble [7] (2010), Cambridge University         *)
(* ------------------------------------------------------------------------- *)
(* Updated by Chun Tian (2019-2020) using some materials from:               *)
(*                                                                           *)
(*        Lebesgue Measure Theory (lebesgue_measure_hvgScript.sml)           *)
(*                                                                           *)
(*        (c) Copyright 2015,                                                *)
(*                       Muhammad Qasim,                                     *)
(*                       Osman Hasan,                                        *)
(*                       Hardware Verification Group,                        *)
(*                       Concordia University                                *)
(*                                                                           *)
(*            Contact:  <m_qasi@ece.concordia.ca>                            *)
(*                                                                           *)
(* Note: This theory is inspired by Isabelle/HOL                             *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory prim_recTheory optionTheory pairTheory combinTheory
     pred_setTheory pred_setLib numLib res_quanTheory res_quanTools listTheory;

open realTheory realLib seqTheory transcTheory real_sigmaTheory RealArith
     jrhUtils cardinalTheory;

open hurdUtils util_probTheory extrealTheory sigma_algebraTheory measureTheory
     borelTheory real_topologyTheory;

val _ = new_theory "lebesgue";

val ASM_ARITH_TAC = rpt (POP_ASSUM MP_TAC) >> ARITH_TAC; (* numLib *)
val ASM_REAL_ARITH_TAC = REAL_ASM_ARITH_TAC; (* RealArith *)
val DISC_RW_KILL = DISCH_TAC >> ONCE_ASM_REWRITE_TAC [] >> POP_ASSUM K_TAC;
fun METIS ths tm = prove (tm, METIS_TAC ths);

(* ************************************************************************* *)
(* Basic Definitions                                                         *)
(* ************************************************************************* *)

(* This defines a simple function ‘f’ in measurable space m by (s,a,x):

   s is a (finite) set of indices,
   a_i (each i IN s) are mutually disjoint measurable sets in m,
   x_i are (normal) reals indicating the "height" of each a(i).

   Then `f(t) = SIGMA (\i. Normal (x i) * indicator_fn (a i) t) s` is a simple function.

   BIGUNION and DISJOINT indicate that this is a standard representation.

   NOTE: changed from `!t. 0 <= f t` to `!t. t IN m_space m ==> 0 <= f t`
 *)
Definition pos_simple_fn_def :
    pos_simple_fn m f (s :num set) (a :num -> 'a set) (x :num -> real) =
       ((!t. t IN m_space m ==> 0 <= f t) /\ (* was: !t. 0 <= f t *)
        (!t. t IN m_space m ==>
            (f t = SIGMA (\i. Normal (x i) * indicator_fn (a i) t) s)) /\
        (!i. i IN s ==> a i IN measurable_sets m) /\
        FINITE s /\ (!i. i IN s ==> 0 <= x i) /\
        (!i j. i IN s /\ j IN s /\ (i <> j) ==> DISJOINT (a i) (a j)) /\
        (BIGUNION (IMAGE a s) = m_space m))
End

(* The integral of a positive simple function: s is a set of indices,
   a(n) is a sequence of disjoint sets, x(n) is a sequence of reals.

   old definition: Normal (SIGMA (\i:num. (x i) * (measure m (a i))) s)
 *)
Definition pos_simple_fn_integral_def :
    pos_simple_fn_integral (m :'a m_space)
                           (s :num set) (a :num -> 'a set) (x :num -> real) =
        SIGMA (\i:num. Normal (x i) * (measure m (a i))) s
End

(* ‘psfs m f’ is the set of all positive simple functions equivalent to f *)
Definition psfs_def :
    psfs m f = {(s,a,x) | pos_simple_fn m f s a x}
End

(* `psfis m f ` is the set of integrals of positive simple functions equivalent to f *)
val psfis_def = Define
   `psfis m f = IMAGE (\(s,a,x). pos_simple_fn_integral m s a x) (psfs m f)`;

(* the integral of arbitrary positive function is the sup of integrals of all
   positive simple functions smaller than f,

   cf. "nnfis_def" in (old) real_lebesgueScript.sml

   changed from `!x. g x <= fx` to `!x. x IN m_space m ==> g x <= f x`
 *)
val pos_fn_integral_def = Define
   `pos_fn_integral m f =
      sup {r | ?g. r IN psfis m g /\ !x. x IN m_space m ==> g x <= f x}`;

(* INTEGRAL^+ *)
val _ = Unicode.unicode_version {u = UTF8.chr 0x222B ^ Unicode.UChar.sup_plus,
                                 tmnm = "pos_fn_integral"};

val _ = TeX_notation {hol = UTF8.chr 0x222B ^ Unicode.UChar.sup_plus,
                      TeX = ("\\HOLTokenIntegralPlus{}", 1)};

val _ = hide "integral"; (* possibly integrationTheory.integral_def *)
Definition integral_def :
    integral m f = pos_fn_integral m (fn_plus f) - pos_fn_integral m (fn_minus f)
End

(* INTEGRAL *)
val _ = Unicode.unicode_version {u = UTF8.chr 0x222B, tmnm = "integral"};
val _ = TeX_notation {hol = UTF8.chr 0x222B, TeX = ("\\HOLTokenIntegral{}", 1)};

(* Lebesgue integrable = the integral is specified (ie. no `PosInf - PosInf`) *)
val _ = hide "integrable";

(* NOTE: all integrable functions form the set ‘L1_space m’, i.e. set of integrable
   measurable functions from arbitrary measure space ‘m’ to Borel measurable
   space generated by extended reals. (cf. martingaleTheory.lp_space_def)
 *)
Definition integrable_def :
    integrable m f =
       (f IN measurable (m_space m,measurable_sets m) Borel /\
        pos_fn_integral m (fn_plus f) <> PosInf /\
        pos_fn_integral m (fn_minus f) <> PosInf)
End

Definition finite_space_integral_def :
    finite_space_integral m f =
      SIGMA (\r. r * measure m (PREIMAGE f {r} INTER m_space m)) (IMAGE f (m_space m))
End

(* ------------------------------------------------------------------------- *)
(* Radon-Nikodym Related Definitions                                         *)
(* ------------------------------------------------------------------------- *)

(* v is absolutely continuous w.r.t. m, denoted by ``v << m``

   NOTE: the type of `v` is not `:'a m_space` but `:'a measure`, to simplify
   the statements of Radon-Nikodym theorems as much as possible.
 *)
val measure_absolutely_continuous_def = Define
   `measure_absolutely_continuous v m =
      !s. s IN measurable_sets m /\ (measure m s = 0) ==> (v s = 0)`;

(* "<<" is already used in "src/n-bit/wordsScript.sml", same priority here *)
val _ = set_fixity "<<" (Infixl 680);
val _ = Unicode.unicode_version {u = Unicode.UChar.lsl, tmnm = "<<"};

(* aligned with wordsTheory *)
val _ = TeX_notation {hol = "<<",              TeX = ("\\HOLTokenLsl{}", 2)};
val _ = TeX_notation {hol = Unicode.UChar.lsl, TeX = ("\\HOLTokenLsl{}", 2)};

val _ = overload_on ("<<", ``measure_absolutely_continuous``);

(* The measure with density (function) f with respect to m, see [1, p.86-87]
   from HVG's lebesgue_measureScript.sml, simplified.

   The use of `density`, e.g. in RN_deriv_def, should guarantee that:

   1) the involved function `f` is (AE) non-negative in measure space `m`.
   2) the resulting `f * m` is only called on `s IN measurable_sets m`.
 *)
val density_measure_def = Define (* or `f * m` *)
   `density_measure m f = \s. pos_fn_integral m (\x. f x * indicator_fn s x)`;

val density_def = Define (* was: density *)
   `density m f = (m_space m, measurable_sets m, density_measure m f)`;

(* `v = density m f` is denoted by `v = f * m` (cf. "RN_deriv_def" below)

   The idea is to syntactically have (`*` is not commutative here):

      `(f * m = v) <=> (f = v / m)`     or      `v / m * m = v`
 *)
val _ = overload_on ("*", ``\f m. density_measure m f``);

(* Theorem 7.6 [1, p.55]: let M, N be measurable spaces and f : M -> N be an
   M/N-measurable map. For every `u` on `(m_space M,measurable_sets M)`,

      u' = \A. u (PREIMAGE f A INTER m_space M)  (A IN measurable_sets N)

   defines a measure on (m_space N,measurable_sets N).

   Definition 7.7 [1, p.55]: The measure u' of Theorem 7.6 is called the
   "image measure" or "push forward" of `u` under f.

   cf. density_def, probabilityTheory.distribution_def (an application)
 *)
val distr_def = Define
   `distr m f = \s. measure m (PREIMAGE f s INTER m_space m)`;

(* unused for now:
val diff_measure_space_def = Define
   `diff_measure_space m v =
      (m_space m, measurable_sets m, (\s. measure m s - v s))`;

val _ = overload_on ("-", ``diff_measure_space``);
 *)

(*****************************************************************************)

Theorem IN_MEASURABLE_BOREL_POS_SIMPLE_FN :
    !m f. measure_space m /\ (?s a x. pos_simple_fn m f s a x) ==>
          f IN measurable (m_space m,measurable_sets m) Borel
Proof
    RW_TAC std_ss [pos_simple_fn_def]
 >> `!i. i IN s ==> indicator_fn (a i) IN measurable (m_space m,measurable_sets m) Borel`
        by METIS_TAC [IN_MEASURABLE_BOREL_INDICATOR, measurable_sets_def, subsets_def,
                      m_space_def, measure_space_def]
 >> `!i x. i IN s ==> (\t. Normal (x i) * indicator_fn (a i) t) IN
                      measurable (m_space m, measurable_sets m) Borel`
        by (qx_genl_tac [`i`, `y`] >> DISCH_TAC \\
            MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL \\
            qexistsl_tac [`indicator_fn (a i)`, `y i`] \\
            RW_TAC std_ss [] \\
            FULL_SIMP_TAC std_ss [measure_space_def])
 >> MATCH_MP_TAC (INST_TYPE [beta |-> ``:num``] IN_MEASURABLE_BOREL_SUM)
 >> qexistsl_tac [`(\i. (\t. Normal (x i) * indicator_fn (a i) t))`, `s`]
 >> RW_TAC std_ss [space_def]
 >- FULL_SIMP_TAC std_ss [measure_space_def]
 >> RW_TAC real_ss [indicator_fn_def, mul_rzero, mul_rone]
 >> RW_TAC std_ss [extreal_of_num_def]
QED

(* z/z' c is the standard representation of f/g *)
Theorem pos_simple_fn_integral_present :
    !m f (s :num->bool) a x
       g (s':num->bool) b y.
       measure_space m /\ pos_simple_fn m f s a x /\ pos_simple_fn m g s' b y ==>
       ?z z' c (k:num->bool).
          (!t. t IN m_space m ==> (f t = SIGMA (\i. Normal (z  i) * (indicator_fn (c i) t)) k)) /\
          (!t. t IN m_space m ==> (g t = SIGMA (\i. Normal (z' i) * (indicator_fn (c i) t)) k)) /\
          (pos_simple_fn_integral m s  a x = pos_simple_fn_integral m k c z) /\
          (pos_simple_fn_integral m s' b y = pos_simple_fn_integral m k c z') /\
           FINITE k /\ (!i. i IN k ==> 0 <= z i) /\ (!i. i IN k ==> 0 <= z' i) /\
          (!i j. i IN k /\ j IN k /\ i <> j ==> DISJOINT (c i) (c j)) /\
          (!i. i IN k ==> c i IN measurable_sets m) /\
          (BIGUNION (IMAGE c k) = m_space m)
Proof
    rpt STRIP_TAC
 >> `?p n. BIJ p (count n) (s CROSS s')`
        by FULL_SIMP_TAC std_ss [GSYM FINITE_BIJ_COUNT, pos_simple_fn_def, FINITE_CROSS]
 >> `?p'. BIJ p' (s CROSS s') (count n) /\
          (!x. x IN (count n) ==> ((p' o p) x = x)) /\
          (!x. x IN (s CROSS s') ==> ((p o p') x = x))`
        by (MATCH_MP_TAC BIJ_INV >> RW_TAC std_ss [])
 >> qexistsl_tac [`x o FST o p`, `y o SND o p`,
                  `(\(i,j). a i INTER b j) o p`,
                  `IMAGE p' (s CROSS s')`]
 >> Q.ABBREV_TAC `G = IMAGE (\i j. p' (i,j)) s'`
 >> Q.ABBREV_TAC `H = IMAGE (\j i. p' (i,j)) s`
 >> CONJ_TAC
 >- (RW_TAC std_ss [FUN_EQ_THM] \\
     FULL_SIMP_TAC std_ss [pos_simple_fn_def] \\
    `!i. i IN s ==> (\i. Normal (x i) * indicator_fn (a i) t) i <> NegInf`
         by METIS_TAC [indicator_fn_def, mul_rzero, mul_rone, extreal_not_infty,
                       extreal_of_num_def] \\
     FULL_SIMP_TAC std_ss [(Once o UNDISCH o Q.ISPEC `(s :num -> bool)`)
                               EXTREAL_SUM_IMAGE_IN_IF] \\
    `(\x'. (if x' IN s then (\i. Normal (x i) * indicator_fn (a i) t) x' else 0)) =
     (\x'. (if x' IN s then (\i. Normal (x i) *
                SIGMA (\j. indicator_fn (a i INTER b j) t) s') x' else 0))`
        by (RW_TAC std_ss [FUN_EQ_THM] \\
            RW_TAC std_ss [] \\
            FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO] \\
            (MP_TAC o Q.ISPEC `(a :num -> 'a set) (x' :num)` o
             UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
             Q.ISPECL [`(s' :num -> bool)`, `m_space (m: 'a m_space)`,
                       `(b :num -> 'a set)`]) indicator_fn_split \\
            Q.PAT_X_ASSUM `!i. i IN s ==> (a :num -> 'a set) i IN measurable_sets m`
               (ASSUME_TAC o UNDISCH o Q.SPEC `x'`) \\
           `!a m. measure_space m /\ a IN measurable_sets m ==> a SUBSET m_space m`
               by RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,
                                 subset_class_def, subsets_def, space_def] \\
            POP_ASSUM (ASSUME_TAC o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
                       Q.ISPECL [`(a :num -> 'a set) (x' :num)`, `(m :'a m_space)`]) \\
            ASM_SIMP_TAC std_ss []) \\
     FULL_SIMP_TAC std_ss [] \\
    `!i j. j IN s' ==> (\j. indicator_fn (a i INTER b j) t) j <> NegInf`
         by METIS_TAC [extreal_of_num_def, extreal_not_infty, indicator_fn_def] \\
    `!(x':num) (i:num). Normal (x i) * SIGMA (\j. indicator_fn (a i INTER b j) t) s' =
                        SIGMA (\j. Normal (x i) * indicator_fn (a i INTER b j) t) s'`
         by (RW_TAC std_ss [] \\
             (MP_TAC o UNDISCH o Q.SPEC `s'` o GSYM o INST_TYPE [alpha |-> ``:num``])
                EXTREAL_SUM_IMAGE_CMUL \\
             FULL_SIMP_TAC std_ss []) >> POP_ORW \\
    `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS] \\
    `INJ p' (s CROSS s') (IMAGE p' (s CROSS s'))` by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF] \\
     (MP_TAC o Q.SPEC `(\i:num. Normal (x (FST (p i))) *
                                indicator_fn ((\(i:num,j:num). a i INTER b j) (p i)) t)`
             o UNDISCH o Q.SPEC `p'` o UNDISCH o Q.SPEC `s CROSS s'`
             o INST_TYPE [alpha |-> ``:num#num``, beta |-> ``:num``]) EXTREAL_SUM_IMAGE_IMAGE \\
    `!x'. Normal (x (FST (p x'))) * indicator_fn ((\(i,j). a i INTER b j) (p x')) t <> NegInf`
          by METIS_TAC [indicator_fn_def, mul_rzero, mul_rone, extreal_not_infty,
                        extreal_of_num_def] \\
     RW_TAC std_ss [] \\
    `!x'. ((\i. Normal (x (FST (p i))) *
                indicator_fn ((\(i,j). a i INTER b j) (p i)) t) o p') x' <> NegInf`
          by (RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone] \\
              METIS_TAC [extreal_not_infty, extreal_of_num_def]) \\
     (MP_TAC o Q.SPEC `((\i. Normal (x (FST ((p :num -> num # num) i))) *
                             indicator_fn ((\(i,j). a i INTER b j) (p i)) t) o p')`
             o UNDISCH o Q.ISPEC `(s :num set) CROSS (s' :num set)`) EXTREAL_SUM_IMAGE_IN_IF \\
     RW_TAC std_ss [] \\
    `(\x'.if x' IN s CROSS s' then
             Normal (x (FST x')) * indicator_fn ((\(i,j). a i INTER b j) x') t
          else 0) =
     (\x'. (if x' IN s CROSS s' then
               (\x'. Normal (x (FST x')) * indicator_fn ((\(i,j). a i INTER b j) x') t) x'
            else 0))` by METIS_TAC [] >> POP_ORW \\
    `!x'. (\x'. Normal (x (FST x')) * indicator_fn ((\(i,j). a i INTER b j) x') t) x' <> NegInf`
          by (RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone] \\
              METIS_TAC [extreal_not_infty, extreal_of_num_def]) \\
     (MP_TAC o Q.SPEC `(\x'. Normal (x (FST x')) * indicator_fn ((\(i,j). a i INTER b j) x') t)`
             o UNDISCH o Q.ISPEC `(s :num set) CROSS (s' :num set)`)
       (GSYM EXTREAL_SUM_IMAGE_IN_IF) \\
     RW_TAC std_ss [] \\
    `!x'. NegInf <> (\i:num. SIGMA (\j:num. Normal (x i) * indicator_fn (a i INTER b j) t) s') x'`
          by (RW_TAC std_ss [] \\
             `!j. (\j. Normal (x x') * indicator_fn (a x' INTER b j) t) j <> NegInf`
                  by (RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone] \\
                      METIS_TAC [extreal_of_num_def, extreal_not_infty]) \\
              FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY]) \\
     (MP_TAC o Q.SPEC `(\i:num. SIGMA (\j:num. Normal (x i) * indicator_fn (a i INTER b j) t) s')`
             o UNDISCH o Q.ISPEC `(s :num -> bool)`) (GSYM EXTREAL_SUM_IMAGE_IN_IF) \\
     RW_TAC std_ss [] \\
     (MP_TAC o Q.ISPECL [`s:num->bool`,`s':num->bool`]) EXTREAL_SUM_IMAGE_SUM_IMAGE \\
     RW_TAC std_ss [] \\
     POP_ASSUM (MP_TAC o Q.SPEC `(\i j. Normal (x i) * indicator_fn (a i INTER b j) t)`) \\
    `!x'. Normal (x (FST x')) * indicator_fn (a (FST x') INTER b (SND x')) t <> NegInf`
          by (RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone] \\
              METIS_TAC [extreal_of_num_def, extreal_not_infty]) \\
     RW_TAC std_ss [] \\
     Suff `(\i. Normal (x (FST i)) * indicator_fn (a (FST i) INTER b (SND i)) t) =
           (\x'. Normal (x (FST x')) * indicator_fn ((\(i,j). a i INTER b j) x') t)`
     >- RW_TAC std_ss [] \\
     RW_TAC std_ss [FUN_EQ_THM] \\
     Cases_on `x'` >> RW_TAC std_ss [FST, SND])
 >> CONJ_TAC
 >- (RW_TAC std_ss [FUN_EQ_THM] \\
     FULL_SIMP_TAC std_ss [pos_simple_fn_def] \\
     (MP_TAC o Q.SPEC `(\i. Normal (y i) * indicator_fn (b i) t)`
             o UNDISCH o Q.ISPEC `s':num->bool`) EXTREAL_SUM_IMAGE_IN_IF \\
    `!x. x IN s' ==> (\i. Normal (y i) * indicator_fn (b i) t) x <> NegInf`
         by (RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone] \\
             METIS_TAC [extreal_of_num_def, extreal_not_infty]) \\
     RW_TAC std_ss [] \\
    `(\x. if x IN s' then Normal (y x) * indicator_fn (b x) t else 0) =
     (\x. (if x IN s' then (\i. Normal (y i) * indicator_fn (b i) t) x else 0))`
         by RW_TAC std_ss [] >> POP_ORW \\
    `(\x. (if x IN s' then (\i. Normal (y i) * indicator_fn (b i) t) x else 0)) =
     (\x. (if x IN s' then (\i. Normal (y i) *
                SIGMA (\j. indicator_fn (a j INTER b i) t) s) x else 0))`
         by (RW_TAC std_ss [FUN_EQ_THM] \\
             RW_TAC std_ss [] \\
             FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO] \\
             (MP_TAC o REWRITE_RULE [Once INTER_COMM] o
              Q.ISPEC `(b :num -> 'a set) (x' :num)` o
              UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
              Q.ISPECL [`(s :num -> bool)`, `m_space (m :'a m_space)`,
                        `(a :num -> 'a set)`]) indicator_fn_split \\
             Q.PAT_X_ASSUM `!i. i IN s' ==> (b :num -> 'a set) i IN measurable_sets m`
                (ASSUME_TAC o UNDISCH o Q.SPEC `x'`) \\
             RW_TAC std_ss [MEASURE_SPACE_SUBSET_MSPACE]) >> POP_ORW \\
    `!(x:num) (i:num). Normal (y i) * SIGMA (\j. indicator_fn (a j INTER b i) t) s =
                       SIGMA (\j. Normal (y i) * indicator_fn (a j INTER b i) t) s`
         by (RW_TAC std_ss [] \\
            `!j. (\j. indicator_fn (a j INTER b i) t) j <> NegInf`
                 by RW_TAC std_ss [indicator_fn_def, extreal_of_num_def, extreal_not_infty] \\
             FULL_SIMP_TAC std_ss [GSYM EXTREAL_SUM_IMAGE_CMUL]) >> POP_ORW \\
    `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS] \\
    `INJ p' (s CROSS s') (IMAGE p' (s CROSS s'))` by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF] \\
     (MP_TAC o Q.SPEC `(\i:num. Normal (y (SND (p i))) *
                                indicator_fn ((\(i:num,j:num). a i INTER b j) (p i)) t)`
             o UNDISCH o Q.SPEC `p'` o UNDISCH o Q.SPEC `s CROSS s'`
             o INST_TYPE [alpha |-> ``:num#num``, beta |-> ``:num``]) EXTREAL_SUM_IMAGE_IMAGE \\
    `!x. (\i. Normal (y (SND (p i))) *
              indicator_fn ((\(i,j). a i INTER b j) (p i)) t) x <> NegInf`
         by METIS_TAC [indicator_fn_def, mul_rzero, mul_rone, extreal_not_infty,
                       extreal_of_num_def] \\
     RW_TAC std_ss [] \\
    `!x'. ((\i. Normal (y (SND (p i))) *
                indicator_fn ((\(i,j). a i INTER b j) (p i)) t) o p') x' <> NegInf`
         by (RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone] \\
             METIS_TAC [extreal_not_infty, extreal_of_num_def]) \\
     (MP_TAC o Q.SPEC `((\i. Normal (y (SND ((p :num -> num # num) i))) *
                             indicator_fn ((\(i,j). a i INTER b j) (p i)) t) o p')`
             o UNDISCH o Q.ISPEC `(s :num set) CROSS (s' :num set)`) EXTREAL_SUM_IMAGE_IN_IF \\
     RW_TAC std_ss [] \\
    `(\x'.if x' IN s CROSS s' then
             Normal (y (SND x')) * indicator_fn ((\(i,j). a i INTER b j) x') t else 0) =
     (\x'. (if x' IN s CROSS s' then
             (\x'. Normal (y (SND x')) * indicator_fn ((\(i,j). a i INTER b j) x') t) x'
            else 0))` by METIS_TAC [] >> POP_ORW \\
    `!x'. (\x'. Normal (y (SND x')) * indicator_fn ((\(i,j). a i INTER b j) x') t) x' <> NegInf`
         by (RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone] \\
             METIS_TAC [extreal_not_infty, extreal_of_num_def]) \\
     (MP_TAC o Q.SPEC `(\x'. Normal (y (SND x')) * indicator_fn ((\(i,j). a i INTER b j) x') t)`
             o UNDISCH o Q.ISPEC `(s :num set) CROSS (s' :num set)`)
        (GSYM EXTREAL_SUM_IMAGE_IN_IF) \\
     RW_TAC std_ss [] \\
    `!x'. NegInf <> (\x:num. SIGMA (\j:num. Normal (y x) * indicator_fn (a j INTER b x) t) s) x'`
         by (RW_TAC std_ss [] \\
            `!j. (\j. Normal (y x') * indicator_fn (a j INTER b x') t) j <> NegInf`
                 by (RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone] \\
                     METIS_TAC [extreal_of_num_def, extreal_not_infty]) \\
             FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY]) \\
     (MP_TAC o Q.SPEC `(\x:num. SIGMA (\j:num. Normal (y x) * indicator_fn (a j INTER b x) t) s)`
             o UNDISCH o Q.ISPEC `(s' :num -> bool)`) (GSYM EXTREAL_SUM_IMAGE_IN_IF) \\
     RW_TAC std_ss [] \\
     (MP_TAC o Q.ISPECL [`s':num->bool`,`s:num->bool`]) EXTREAL_SUM_IMAGE_SUM_IMAGE \\
     RW_TAC std_ss [] \\
     POP_ASSUM (MP_TAC o Q.SPEC `(\x j. Normal (y x) * indicator_fn (a j INTER b x) t)`) \\
    `!x. Normal (y x) * indicator_fn (a j INTER b x) t <> NegInf`
         by (RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone] \\
             METIS_TAC [extreal_of_num_def, extreal_not_infty]) \\
    `!x. Normal (y (FST x)) * indicator_fn (a (SND x) INTER b (FST x)) t <> NegInf`
         by (RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone] \\
             METIS_TAC [extreal_of_num_def, extreal_not_infty]) \\
     RW_TAC std_ss [] \\
    `(s' CROSS s) = IMAGE (\x. (SND x, FST x)) (s CROSS s')`
         by (RW_TAC std_ss [Once EXTENSION, IN_CROSS, IN_IMAGE] \\
             (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES \\
             RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND] \\
             EQ_TAC >- (STRIP_TAC >> Q.EXISTS_TAC `(r,q)` >> RW_TAC std_ss [FST, SND]) \\
             RW_TAC std_ss [] >> RW_TAC std_ss []) >> POP_ORW \\
    `INJ (\x. (SND x,FST x)) (s CROSS s')
         (IMAGE (\x. (SND x,FST x)) (s CROSS s'))`
         by (RW_TAC std_ss [INJ_DEF, IN_CROSS, IN_IMAGE] >- METIS_TAC [] \\
             (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES \\
             (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES \\
             RW_TAC std_ss [] \\
             FULL_SIMP_TAC std_ss [FST,SND]) \\
     (MP_TAC o Q.SPEC `(\x. Normal (y (FST x)) * indicator_fn (a (SND x) INTER b (FST x)) t)`
             o UNDISCH o Q.SPEC `(\x. (SND x, FST x))` o UNDISCH
             o Q.ISPEC `((s:num->bool) CROSS (s':num->bool))`
             o INST_TYPE [``:'b``|->``:num#num``]) EXTREAL_SUM_IMAGE_IMAGE \\
    `!x. (\x. Normal (y (FST x)) * indicator_fn (a (SND x) INTER b (FST x)) t) x <> NegInf`
         by (RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone] \\
             METIS_TAC [extreal_of_num_def, extreal_not_infty]) \\
     RW_TAC std_ss [o_DEF] \\
     Suff `(\x. Normal (y (SND x)) * indicator_fn (a (FST x) INTER b (SND x)) t) =
           (\x. Normal (y (SND x)) * indicator_fn ((\(i,j). a i INTER b j) x) t)`
     >- RW_TAC std_ss [] \\
     RW_TAC std_ss [FUN_EQ_THM] \\
     Cases_on `x'` >> RW_TAC std_ss [FST, SND])
 >> CONJ_TAC
 >- (RW_TAC std_ss [pos_simple_fn_integral_def] \\
     FULL_SIMP_TAC std_ss [pos_simple_fn_def] \\
     (MP_TAC o Q.ISPEC `(\i:num. Normal (x i) * measure m (a i))`
             o UNDISCH o Q.ISPEC `(s :num -> bool)`) EXTREAL_SUM_IMAGE_IN_IF \\
    `!x'. x' IN s ==> (\i. Normal (x i) * measure m (a i)) x' <> NegInf`
         by (RW_TAC std_ss [] \\
             METIS_TAC [positive_not_infty, mul_not_infty, measure_space_def]) \\
     RW_TAC std_ss [] \\
    `(\x'. if x' IN s then Normal (x x') * measure m (a x') else 0) =
     (\x'. (if x' IN s then (\i. Normal (x i) * measure m (a i)) x' else 0))`
         by METIS_TAC [] >> POP_ORW \\
    `(\x'. (if x' IN s then (\i. Normal (x i) * measure m (a i)) x' else 0)) =
     (\x'. (if x' IN s then (\i. Normal (x i) *
                                 SIGMA (\j. measure m (a i INTER b j)) s') x' else 0))`
         by (RW_TAC std_ss [FUN_EQ_THM] \\
             RW_TAC std_ss [] \\
             FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO] \\
             (MP_TAC o Q.SPEC `a (x' :num)` o
              UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
              Q.SPECL [`s'`, `b`, `m`]) measure_split \\
             RW_TAC std_ss []) >> POP_ORW \\
    `!i. i IN s ==> (Normal (x i) * SIGMA (\j. measure m (a i INTER b j)) s' =
                     SIGMA (\j. Normal (x i) * measure m (a i INTER b j)) s')`
         by (RW_TAC std_ss [] \\
            `!j. j IN s' ==> (\j. measure m (a i INTER b j)) j <> NegInf`
                by METIS_TAC [positive_not_infty, measure_space_def, MEASURE_SPACE_INTER] \\
             FULL_SIMP_TAC std_ss [GSYM EXTREAL_SUM_IMAGE_CMUL]) \\
     FULL_SIMP_TAC std_ss [] \\
    `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS] \\
    `INJ p' (s CROSS s') (IMAGE p' (s CROSS s'))`
               by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF] \\
     (MP_TAC o Q.SPEC `(\i:num. Normal (x (FST (p i))) *
                                measure m ((\(i:num, j:num). a i INTER b j) (p i)))`
             o UNDISCH o Q.SPEC `p'` o UNDISCH o Q.SPEC `s CROSS s'`
             o INST_TYPE [alpha |-> ``:num#num``, beta |-> ``:num``])
        EXTREAL_SUM_IMAGE_IMAGE \\
    `!x'. x' IN IMAGE p' (s CROSS s') ==>
          Normal (x (FST (p x'))) * measure m ((\(i,j). a i INTER b j) (p x')) <> NegInf`
         by (RW_TAC std_ss [] \\
             Cases_on `p x'` \\
             RW_TAC std_ss [] \\
             FULL_SIMP_TAC std_ss [IN_IMAGE, IN_CROSS] \\
            `q IN s` by METIS_TAC [BIJ_DEF, FST, SND] \\
            `r IN s'` by METIS_TAC [BIJ_DEF, FST, SND] \\
             METIS_TAC [positive_not_infty, measure_space_def, mul_not_infty,
                        MEASURE_SPACE_INTER]) >> RW_TAC std_ss [] \\
     (MP_TAC o Q.SPEC `((\i. Normal (x (FST ((p :num -> num # num) i))) *
                             measure m ((\(i,j). a i INTER b j) (p i))) o p')`
             o UNDISCH o Q.ISPEC `(s :num set) CROSS (s' :num set)`) EXTREAL_SUM_IMAGE_IN_IF \\
    `!x'. x' IN s CROSS s' ==>
          ((\i. Normal (x (FST (p i))) *
                measure m ((\(i,j). a i INTER b j) (p i))) o p') x' <> NegInf`
         by (RW_TAC std_ss [] \\
             Cases_on `x'` \\
             FULL_SIMP_TAC std_ss [IN_CROSS] \\
             METIS_TAC [positive_not_infty, measure_space_def, mul_not_infty,
                        MEASURE_SPACE_INTER]) >> RW_TAC std_ss [] \\
    `(\x'. if x' IN s CROSS s' then
              Normal (x (FST x')) * measure m ((\(i,j). a i INTER b j) x') else 0) =
     (\x'. (if x' IN s CROSS s' then
               (\x'. Normal (x (FST x')) * measure m ((\(i,j). a i INTER b j) x')) x' else 0))`
         by METIS_TAC [] >> POP_ORW \\
     (MP_TAC o Q.SPEC `(\x'. Normal (x (FST x')) * measure m ((\(i,j). a i INTER b j) x'))`
             o UNDISCH o Q.ISPEC `(s :num set) CROSS (s' :num set)`)
        (GSYM EXTREAL_SUM_IMAGE_IN_IF) \\
    `!x'. x' IN s CROSS s' ==>
          NegInf <> (\x'. Normal (x (FST x')) * measure m ((\(i,j). a i INTER b j) x')) x'`
         by (RW_TAC std_ss [] \\
             Cases_on `x'` \\
             FULL_SIMP_TAC std_ss [IN_CROSS] \\
             METIS_TAC [positive_not_infty, measure_space_def, mul_not_infty,
                        MEASURE_SPACE_INTER]) >> RW_TAC std_ss [] \\
    `!x'. x' IN s ==>
          NegInf <> (\i:num. SIGMA (\j:num. Normal (x i) * measure m (a i INTER b j)) s') x'`
         by (RW_TAC std_ss [] \\
            `!j. j IN s' ==> (\j. Normal (x x') * measure m (a x' INTER b j)) j <> NegInf`
                 by (RW_TAC std_ss [] \\
                     METIS_TAC [positive_not_infty, measure_space_def, mul_not_infty,
                                MEASURE_SPACE_INTER]) \\
             FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY]) \\
     (MP_TAC o Q.SPEC `(\i:num. SIGMA (\j:num. Normal (x i) * measure m (a i INTER b j)) s')`
             o UNDISCH o Q.ISPEC `(s :num -> bool)`) (GSYM EXTREAL_SUM_IMAGE_IN_IF) \\
     RW_TAC std_ss [] \\
     (MP_TAC o Q.ISPECL [`s:num->bool`,`s':num->bool`]) EXTREAL_SUM_IMAGE_SUM_IMAGE \\
     RW_TAC std_ss [] \\
     POP_ASSUM (MP_TAC o Q.SPEC `(\i j. Normal (x i) * measure m (a i INTER b j))`) \\
    `!x'. x' IN s CROSS s' ==>
          Normal (x (FST x')) * measure m (a (FST x') INTER b (SND x')) <> NegInf`
         by (RW_TAC std_ss [] \\
             Cases_on `x'` \\
             FULL_SIMP_TAC std_ss [IN_CROSS] \\
             METIS_TAC [positive_not_infty, measure_space_def, mul_not_infty,
                        MEASURE_SPACE_INTER]) \\
     RW_TAC std_ss [] \\
     Suff `(\i. Normal (x (FST i)) * measure m (a (FST i) INTER b (SND i))) =
           (\x'. Normal (x (FST x')) * measure m ((\(i,j). a i INTER b j) x'))`
     >- RW_TAC std_ss [] \\
     RW_TAC std_ss [FUN_EQ_THM] \\
     Cases_on `x'` >> RW_TAC std_ss [FST, SND])
 >> CONJ_TAC
 >- (RW_TAC std_ss [pos_simple_fn_integral_def] \\
     FULL_SIMP_TAC std_ss [pos_simple_fn_def] \\
     (MP_TAC o Q.ISPEC `(\i:num. Normal (y i) * measure m (b i))`
             o UNDISCH o Q.ISPEC `(s' :num -> bool)`) EXTREAL_SUM_IMAGE_IN_IF \\
    `!x. x IN s' ==> (\i. Normal (y i) * measure m (b i)) x <> NegInf`
        by (RW_TAC std_ss [] \\
            METIS_TAC [positive_not_infty, mul_not_infty, measure_space_def]) \\
     RW_TAC std_ss [] \\
    `(\x'. if x' IN s' then Normal (y x') * measure m (b x') else 0) =
     (\x'. (if x' IN s' then (\i. Normal (y i) * measure m (b i)) x' else 0))`
        by METIS_TAC [] >> POP_ORW \\
    `(\x'. (if x' IN s' then (\i. Normal (y i) * measure m (b i)) x' else 0)) =
     (\x'. (if x' IN s' then (\i. Normal (y i) *
               SIGMA (\j. measure m (b i INTER a j)) s) x' else 0))`
        by (RW_TAC std_ss [FUN_EQ_THM] \\
            RW_TAC std_ss [] \\
            FULL_SIMP_TAC std_ss [GSYM AND_IMP_INTRO] \\
            (MP_TAC o Q.SPEC `b (x' :num)` o
             UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
             Q.SPECL [`s`, `a`, `m`]) measure_split \\
            RW_TAC std_ss []) >> POP_ORW \\
    `!i. i IN s' ==> (Normal (y i) * SIGMA (\j. measure m (b i INTER a j)) s =
                      SIGMA (\j. Normal (y i) * measure m (b i INTER a j)) s)`
        by (RW_TAC std_ss [] \\
           `!j. j IN s ==> (\j. measure m (b i INTER a j)) j <> NegInf`
               by METIS_TAC [positive_not_infty, measure_space_def, MEASURE_SPACE_INTER] \\
            FULL_SIMP_TAC std_ss [GSYM EXTREAL_SUM_IMAGE_CMUL]) \\
     FULL_SIMP_TAC std_ss [] \\
    `FINITE (s CROSS s')` by RW_TAC std_ss [FINITE_CROSS] \\
    `INJ p' (s CROSS s') (IMAGE p' (s CROSS s'))` by METIS_TAC [INJ_IMAGE_BIJ, BIJ_DEF] \\
     (MP_TAC o Q.SPEC `(\i:num. Normal (y (SND (p i))) *
                                measure m ((\(i:num,j:num). a i INTER b j) (p i)))`
             o UNDISCH o Q.SPEC `p'` o UNDISCH o Q.SPEC `s CROSS s'`
             o INST_TYPE [alpha |-> ``:num#num``, beta |-> ``:num``])
         EXTREAL_SUM_IMAGE_IMAGE \\
    `!x'. x' IN IMAGE p' (s CROSS s') ==>
          Normal (y (SND (p x'))) * measure m ((\(i,j). a i INTER b j) (p x')) <> NegInf`
         by (RW_TAC std_ss [] \\
             Cases_on `p x'` \\
             RW_TAC std_ss [] \\
             FULL_SIMP_TAC std_ss [IN_IMAGE,IN_CROSS] \\
            `q IN s` by METIS_TAC [BIJ_DEF, FST, SND] \\
            `r IN s'` by METIS_TAC [BIJ_DEF, FST, SND] \\
             METIS_TAC [positive_not_infty, measure_space_def, mul_not_infty,
                        MEASURE_SPACE_INTER]) >> RW_TAC std_ss [] \\
     (MP_TAC o Q.SPEC `((\i. Normal (y (SND ((p :num -> num # num) i))) *
                             measure m ((\(i,j). a i INTER b j) (p i))) o p')`
             o UNDISCH o Q.ISPEC `(s :num set) CROSS (s' :num set)`)
         EXTREAL_SUM_IMAGE_IN_IF \\
    `!x'. x' IN s CROSS s' ==>
          ((\i. Normal (y (SND (p i))) *
                measure m ((\(i,j). a i INTER b j) (p i))) o p') x' <> NegInf`
         by (RW_TAC std_ss [] \\
             Cases_on `x'` \\
             FULL_SIMP_TAC std_ss [IN_CROSS] \\
             METIS_TAC [positive_not_infty, measure_space_def, mul_not_infty,
                        MEASURE_SPACE_INTER]) >> RW_TAC std_ss [] \\
    `(\x'. if x' IN s CROSS s' then
              Normal (y (SND x')) * measure m ((\(i,j). a i INTER b j) x') else 0) =
     (\x'. (if x' IN s CROSS s' then
              (\x'. Normal (y (SND x')) * measure m ((\(i,j). a i INTER b j) x')) x' else 0))`
         by METIS_TAC [] >> POP_ORW \\
     (MP_TAC o Q.SPEC `(\x'. Normal (y (SND x')) * measure m ((\(i,j). a i INTER b j) x'))`
             o UNDISCH o Q.ISPEC `(s :num set) CROSS (s' :num set)`)
         (GSYM EXTREAL_SUM_IMAGE_IN_IF) \\
    `!x'. x' IN s CROSS s' ==>
          NegInf <> (\x'. Normal (y (SND x')) * measure m ((\(i,j). a i INTER b j) x')) x'`
         by (RW_TAC std_ss [] \\
             Cases_on `x'` \\
             FULL_SIMP_TAC std_ss [IN_CROSS] \\
             METIS_TAC [positive_not_infty, measure_space_def, mul_not_infty,
                        MEASURE_SPACE_INTER]) >> RW_TAC std_ss [] \\
    `!x'. x' IN s' ==>
          NegInf <> (\i:num. SIGMA (\j:num. Normal (y i) * measure m (b i INTER a j)) s) x'`
         by (RW_TAC std_ss [] \\
            `!j. j IN s ==> (\j. Normal (y x') * measure m (b x' INTER a j)) j <> NegInf`
                by (RW_TAC std_ss [] \\
                    METIS_TAC [positive_not_infty, measure_space_def, mul_not_infty,
                               MEASURE_SPACE_INTER]) \\
             FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY]) \\
     (MP_TAC o Q.SPEC `(\i:num. SIGMA (\j:num. Normal (y i) * measure m (b i INTER a j)) s)`
             o UNDISCH o Q.ISPEC `(s' :num -> bool)`) (GSYM EXTREAL_SUM_IMAGE_IN_IF) \\
     RW_TAC std_ss [] \\
     (MP_TAC o Q.ISPECL [`s':num->bool`,`s:num->bool`]) EXTREAL_SUM_IMAGE_SUM_IMAGE \\
     RW_TAC std_ss [] \\
     POP_ASSUM (MP_TAC o Q.SPEC `(\i j. Normal (y i) * measure m (b i INTER a j))`) \\
    `!x'. x' IN s' CROSS s ==>
          Normal (y (FST x')) * measure m (b (FST x') INTER a (SND x')) <> NegInf`
         by (RW_TAC std_ss [] \\
             Cases_on `x'` \\
             FULL_SIMP_TAC std_ss [IN_CROSS] \\
             METIS_TAC [positive_not_infty, measure_space_def, mul_not_infty,
                        MEASURE_SPACE_INTER]) \\
     RW_TAC std_ss [o_DEF] \\
    `(s' CROSS s) = IMAGE (\x. (SND x, FST x)) (s CROSS s')`
         by (RW_TAC std_ss [Once EXTENSION, IN_CROSS, IN_IMAGE] \\
             (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES \\
             RW_TAC std_ss [] >> RW_TAC std_ss [FST,SND] \\
             EQ_TAC >- (STRIP_TAC >> Q.EXISTS_TAC `(r,q)` >> RW_TAC std_ss [FST,SND]) \\
             RW_TAC std_ss [] >> RW_TAC std_ss []) >> POP_ORW \\
    `INJ (\x. (SND x,FST x)) (s CROSS s') (IMAGE (\x. (SND x,FST x)) (s CROSS s'))`
         by (RW_TAC std_ss [INJ_DEF, IN_CROSS, IN_IMAGE]
             >- METIS_TAC [] \\
             (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES \\
             (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES \\
             RW_TAC std_ss [] \\
             FULL_SIMP_TAC std_ss [FST,SND]) \\
     (MP_TAC o Q.SPEC `(\x. Normal (y (FST x)) * measure m (a (SND x) INTER b (FST x)))`
             o UNDISCH o Q.SPEC `(\x. (SND x, FST x))` o UNDISCH
             o Q.ISPEC `((s:num->bool) CROSS (s':num->bool))`
             o INST_TYPE [``:'b``|->``:num#num``]) EXTREAL_SUM_IMAGE_IMAGE \\
    `!x. x IN IMAGE (\x. (SND x,FST x)) (s CROSS s') ==>
         (\x. Normal (y (FST x)) * measure m (a (SND x) INTER b (FST x))) x <> NegInf`
         by (RW_TAC std_ss [] \\
             Cases_on `x'` \\
             FULL_SIMP_TAC std_ss [IN_CROSS,IN_IMAGE] \\
             METIS_TAC [positive_not_infty, measure_space_def, mul_not_infty,
                        MEASURE_SPACE_INTER]) \\
     RW_TAC std_ss [o_DEF, INTER_COMM] \\
     Suff `(\x. Normal (y (SND x)) * measure m (a (FST x) INTER b (SND x))) =
           (\x. Normal (y (SND x)) * measure m ((\(i,j). a i INTER b j) x))`
     >- RW_TAC std_ss [] \\
     RW_TAC std_ss [FUN_EQ_THM] \\
     Cases_on `x'` >> RW_TAC std_ss [FST, SND])
 >> CONJ_TAC
 >- FULL_SIMP_TAC std_ss [IMAGE_FINITE, FINITE_CROSS, pos_simple_fn_def]
 >> CONJ_TAC
 >- (RW_TAC std_ss [IN_IMAGE] \\
     FULL_SIMP_TAC std_ss [o_DEF] \\
     (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES \\
     (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES \\
     RW_TAC std_ss [] \\
     RW_TAC std_ss [] \\
     METIS_TAC [IN_CROSS, pos_simple_fn_def, FST])
 >> CONJ_TAC
 >- (RW_TAC std_ss [IN_IMAGE] \\
     FULL_SIMP_TAC std_ss [o_DEF] \\
     (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES \\
     (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES \\
     RW_TAC std_ss [] \\
     RW_TAC std_ss [] \\
     METIS_TAC [IN_CROSS, pos_simple_fn_def, SND])
 >> CONJ_TAC
 >- (RW_TAC std_ss [IN_DISJOINT, IN_IMAGE, EXTENSION, NOT_IN_EMPTY, IN_INTER] \\
     FULL_SIMP_TAC std_ss [o_DEF] \\
     (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES \\
     (MP_TAC o Q.ISPEC `x'':num#num`) pair_CASES \\
     RW_TAC std_ss [] \\
     RW_TAC std_ss [] \\
     SPOSE_NOT_THEN STRIP_ASSUME_TAC \\
     FULL_SIMP_TAC std_ss [IN_INTER, IN_CROSS, FST, SND, pos_simple_fn_def,
                           DISJOINT_DEF] \\
     METIS_TAC [EXTENSION, NOT_IN_EMPTY, IN_INTER])
 >> CONJ_TAC
 >- (RW_TAC std_ss [IN_IMAGE] \\
     FULL_SIMP_TAC std_ss [o_DEF] \\
     (MP_TAC o Q.ISPEC `x':num#num`) pair_CASES \\
     RW_TAC std_ss [] \\
     FULL_SIMP_TAC std_ss [IN_CROSS, FST, SND, pos_simple_fn_def] \\
     METIS_TAC [ALGEBRA_INTER, subsets_def, space_def,
                sigma_algebra_def, measure_space_def])
 >> RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, IN_IMAGE, IN_CROSS]
 >> `!s'' x. (?x'. ((x = p' x') /\ FST x' IN s /\ SND x' IN s')) =
             (?x1 x2. ((x = p' (x1,x2)) /\ x1 IN s /\ x2 IN s'))`
      by METIS_TAC [PAIR, FST, SND]
 >> POP_ORW
 >> `!s''. (?x. (s'' = (\(i,j). a i INTER b j) (p x)) /\
                ?x1 x2. (x = p' (x1,x2)) /\ x1 IN s /\ x2 IN s') <=>
           (?x1 x2. (s'' = (\(i,j). a i INTER b j) (p (p' (x1,x2)))) /\
                    x1 IN s /\ x2 IN s')`
      by METIS_TAC []
 >> POP_ORW
 >> FULL_SIMP_TAC std_ss [o_DEF, IN_CROSS]
 >> `!s''. (?x1 x2. (s'' = (\(i,j). a i INTER b j) (p (p' (x1,x2)))) /\
                    x1 IN s /\ x2 IN s') <=>
           (?x1 x2. (s'' = (\(i,j). a i INTER b j) (x1,x2)) /\
                    x1 IN s /\ x2 IN s')`
      by METIS_TAC [FST,SND]
 >> POP_ORW
 >> RW_TAC std_ss []
 >> Suff `(?x1 x2. x' IN a x1 INTER b x2 /\ x1 IN s /\ x2 IN s') <=>
          x' IN m_space m` >- METIS_TAC []
 >> RW_TAC std_ss [IN_INTER]
 >> FULL_SIMP_TAC std_ss [pos_simple_fn_def]
 >> `m_space m = (BIGUNION (IMAGE a s)) INTER (BIGUNION (IMAGE b s'))`
      by METIS_TAC [INTER_IDEMPOT]
 >> POP_ORW
 >> Q.PAT_X_ASSUM `BIGUNION (IMAGE b s') = m_space m` (K ALL_TAC)
 >> Q.PAT_X_ASSUM `BIGUNION (IMAGE a s) = m_space m` (K ALL_TAC)
 >> RW_TAC std_ss [IN_INTER, IN_BIGUNION, IN_IMAGE]
 >> METIS_TAC []
QED

(* z/z' c is the standard representation of f/g *)
Theorem psfis_present :
    !m f g a b.
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
          (BIGUNION (IMAGE c k) = m_space m)
Proof
    RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
 >> Cases_on `x'` >> Cases_on `x` >> Cases_on `x''` >> Cases_on `x'''`
 >> Cases_on `r'` >> Cases_on `r` >> Cases_on `r''` >> Cases_on `r'''`
 >> RW_TAC std_ss []
 >> FULL_SIMP_TAC std_ss [PAIR_EQ]
 >> MATCH_MP_TAC pos_simple_fn_integral_present >> art []
QED

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

Theorem pos_simple_fn_le :
    !m f g s a x x' i. measure_space m /\
                       pos_simple_fn m f s a x /\ pos_simple_fn m g s a x' /\
                       (!x. x IN m_space m ==> g x <= f x) /\
                       i IN s /\ ~(a i = {}) ==> (Normal (x' i) <= Normal (x i))
Proof
    RW_TAC std_ss []
 >> `!t. t IN a i ==> (f t = Normal (x i))` by METIS_TAC [pos_simple_fn_thm1]
 >> `!t. t IN a i ==> (g t = Normal (x' i))` by METIS_TAC [pos_simple_fn_thm1]
 >> METIS_TAC [CHOICE_DEF, pos_simple_fn_def, MEASURE_SPACE_SUBSET_MSPACE, SUBSET_DEF]
QED

(* added some missing quantifiers *)
Theorem pos_simple_fn_cmul :
    !m f z s a x. measure_space m /\ pos_simple_fn m f s a x /\ 0 <= z ==>
                  ?s' a' x'. pos_simple_fn m (\t. Normal z * f t) s' a' x'
Proof
    RW_TAC std_ss [pos_simple_fn_def]
 >> Q.EXISTS_TAC `s` >> Q.EXISTS_TAC `a` >> Q.EXISTS_TAC `(\i. z * (x i))`
 >> RW_TAC std_ss [REAL_LE_MUL, GSYM extreal_mul_def]
 >- METIS_TAC [extreal_le_def, extreal_of_num_def, le_mul]
 >> (MP_TAC o Q.SPECL [`(\i. Normal (x i) * indicator_fn (a i) t)`,`z`] o
     UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_CMUL
 >> `!x'. (\i. Normal (x i) * indicator_fn (a i) t) x' <> NegInf`
        by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero] \\
            RW_TAC std_ss [extreal_of_num_def,extreal_not_infty])
 >> FULL_SIMP_TAC std_ss [mul_assoc]
QED

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

(* added some missing quantifiers *)
Theorem pos_simple_fn_add :
    !m f g s a x s' a' x'.
       measure_space m /\ pos_simple_fn m f s a x /\ pos_simple_fn m g s' a' x' ==>
       ?s'' a'' x''. pos_simple_fn m (\t. f t + g t) s'' a'' x''
Proof
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
 >> `!x. x IN k ==> NegInf <>
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
        by (RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, add_rzero] \\
            METIS_TAC [extreal_of_num_def, extreal_not_infty])
 >> METIS_TAC []
QED

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
 >> reverse CONJ_TAC
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

Theorem pos_simple_fn_integral_add :
    !m f (s :num -> bool) a x
       g (s':num -> bool) b y. measure_space m /\
                               pos_simple_fn m f s a x /\
                               pos_simple_fn m g s' b y ==>
       ?s'' c z. pos_simple_fn m (\x. f x + g x) s'' c z /\
                (pos_simple_fn_integral m s a x +
                 pos_simple_fn_integral m s' b y =
                 pos_simple_fn_integral m s'' c z)
Proof
    rpt STRIP_TAC
 >> (MP_TAC o Q.SPECL [`m`,`f`,`s`,`a`,`x`,`g`,`s'`,`b`,`y`]) pos_simple_fn_integral_present
 >> RW_TAC std_ss [] >> ASM_SIMP_TAC std_ss []
 >> qexistsl_tac [`k`, `c`, `\i. z i + z' i`]
 >> FULL_SIMP_TAC std_ss [pos_simple_fn_def, pos_simple_fn_integral_def]
 >> reverse CONJ_TAC
 >- (RW_TAC std_ss [GSYM extreal_add_def] \\
    `!i. i IN k ==> Normal (z i) <> NegInf /\ Normal (z' i) <> NegInf /\
                    0 <= Normal (z i) /\ 0 <= Normal (z' i)`
        by METIS_TAC [extreal_not_infty, extreal_of_num_def, extreal_le_def] \\
    `!i. i IN k ==> (\i. (Normal (z i) + Normal (z' i)) * measure m (c i)) i <> NegInf`
        by METIS_TAC [extreal_add_def, mul_not_infty, positive_not_infty, measure_space_def,
                      REAL_LE_ADD] \\
    (MP_TAC o Q.SPEC `\i:num. (Normal (z i) + Normal (z' i)) * measure m (c i)`
     o UNDISCH o Q.ISPEC `k:num->bool`) EXTREAL_SUM_IMAGE_IN_IF \\
     RW_TAC std_ss [add_rdistrib] \\
    (MP_TAC o Q.SPEC `\x. Normal (z x) * measure m (c x) + Normal (z' x) * measure m (c x)`
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
 (* applying le_add *)
 >> CONJ_TAC >- (Q.X_GEN_TAC `t` >> STRIP_TAC \\
                 MATCH_MP_TAC le_add >> METIS_TAC [])
 (* applying REAL_LE_ADD *)
 >> reverse CONJ_TAC
 >- (rpt STRIP_TAC >> MATCH_MP_TAC REAL_LE_ADD >> PROVE_TAC [])
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
 >> `!x. x IN k ==> NegInf <>
       (\x. Normal (z x) * indicator_fn (c x) x' + Normal (z' x) * indicator_fn (c x) x') x`
       by (RW_TAC std_ss [extreal_add_def, indicator_fn_def, mul_rzero, mul_rone, add_rzero] \\
           METIS_TAC [extreal_of_num_def, extreal_not_infty])
 >> RW_TAC std_ss []
 >> `(\x. Normal (z x) * indicator_fn (c x) x' + Normal (z' x) * indicator_fn (c x) x') =
     (\x. (\x. Normal (z x) * indicator_fn (c x) x') x + (\x. Normal (z' x) * indicator_fn (c x) x') x)`
       by METIS_TAC [] >> POP_ORW
 >> (MP_TAC o Q.SPECL [`\x:num. Normal (z x) * indicator_fn (c x) x'`,
                       `\x:num. Normal (z' x) * indicator_fn (c x) x'`]
     o UNDISCH o Q.ISPEC `k:num->bool` o GSYM) EXTREAL_SUM_IMAGE_ADD
 >> `!x:num. x IN k ==> NegInf <> (\x:num. Normal (z x) * indicator_fn (c x) x') x /\
                        NegInf <> (\x:num. Normal (z' x) * indicator_fn (c x) x') x`
       by (RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, add_rzero] \\
           METIS_TAC [extreal_of_num_def, extreal_not_infty])
 >> METIS_TAC []
QED

Theorem pos_simple_fn_integral_add_alt :
    !m f s a x g y. measure_space m /\
           pos_simple_fn m f s a x /\ pos_simple_fn m g s a y ==>
          (pos_simple_fn_integral m s a x +
           pos_simple_fn_integral m s a y =
           pos_simple_fn_integral m s a (\i. x i + y i))
Proof
    RW_TAC std_ss [pos_simple_fn_def, pos_simple_fn_integral_def, GSYM extreal_add_def]
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
 >> METIS_TAC [mul_not_infty, positive_not_infty, measure_space_def, extreal_not_infty]
QED

Theorem psfis_add :
    !m f g a b. measure_space m /\ a IN psfis m f /\ b IN psfis m g ==>
                (a + b) IN psfis m (\x. f x + g x)
Proof
    RW_TAC std_ss [psfis_def, IN_IMAGE, psfs_def, GSPECIFICATION]
 >> rename1 `(x,T) = (\(s,a,x). ((s,a,x),pos_simple_fn m f s a x)) f1`
 >> rename1 `(y,T) = (\(s,a,x). ((s,a,x),pos_simple_fn m g s a x)) f2`
 >> Cases_on `f1` >> Cases_on `r`
 >> rename1 `(x,T) = (\(s,a,x). ((s,a,x),pos_simple_fn m f s a x)) (s0,a0,x0)`
 >> Cases_on `f2` >> Cases_on `r`
 >> rename1 `(y,T) = (\(s,a,x). ((s,a,x),pos_simple_fn m g s a x)) (s1,a1,x1)`
 >> fs []
 >> Suff `?s a x. (pos_simple_fn_integral m s0 a0 x0 +
                   pos_simple_fn_integral m s1 a1 x1 =
                   pos_simple_fn_integral m s a x) /\ pos_simple_fn m (\x. f x + g x) s a x`
 >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `(s,a,x)` \\
     RW_TAC std_ss [] >> Q.EXISTS_TAC `(s,a,x)` \\
     RW_TAC std_ss [PAIR_EQ])
 >> ONCE_REWRITE_TAC [CONJ_COMM]
 >> MATCH_MP_TAC pos_simple_fn_integral_add
 >> RW_TAC std_ss []
QED

Theorem pos_simple_fn_integral_mono :
    !m f (s :num->bool) a x
       g (s':num->bool) b y.
       measure_space m /\ pos_simple_fn m f s a x /\ pos_simple_fn m g s' b y /\
      (!x. x IN m_space m ==> f x <= g x) ==>
       pos_simple_fn_integral m s a x <= pos_simple_fn_integral m s' b y
Proof
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
 >- RW_TAC real_ss [MEASURE_EMPTY, mul_rzero, le_refl]
 >> `pos_simple_fn m f k c z`
      by (FULL_SIMP_TAC std_ss [pos_simple_fn_def] >> METIS_TAC [])
 >> `pos_simple_fn m g k c z'`
      by (FULL_SIMP_TAC std_ss [pos_simple_fn_def] >> METIS_TAC [])
 >> `?t. t IN c x'` by METIS_TAC [CHOICE_DEF]
 >> `f t = Normal (z x')` by METIS_TAC [pos_simple_fn_thm1]
 >> `g t = Normal (z' x')` by METIS_TAC [pos_simple_fn_thm1]
 >> `Normal (z x') <= Normal (z' x')` by METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE, SUBSET_DEF]
 >> Cases_on `measure m (c x') = 0` >- RW_TAC std_ss [mul_rzero,le_refl]
 >> MATCH_MP_TAC le_rmul_imp
 >> RW_TAC std_ss []
 >> METIS_TAC [MEASURE_SPACE_POSITIVE, positive_def, lt_le]
QED

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

(* added missing quantifier (g) *)
val pos_simple_fn_integral_zero_alt = store_thm
  ("pos_simple_fn_integral_zero_alt",
  ``!m g s a x. measure_space m /\ pos_simple_fn m g s a x /\ (!x. x IN m_space m ==> (g x = 0))
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

(* added `x IN m_space m` *)
Theorem pos_simple_fn_integral_sub :
    !m f s a x g s' b y.
       measure_space m /\ (measure m (m_space m) <> PosInf) /\
       (!x. x IN m_space m ==> g x <= f x) /\
       (!x. x IN m_space m ==> g x <> PosInf) /\
       pos_simple_fn m f s  a x /\
       pos_simple_fn m g s' b y ==>
       ?s'' c z. pos_simple_fn m (\x. f x - g x) s'' c z /\
                (pos_simple_fn_integral m s   a x -
                 pos_simple_fn_integral m s'  b y =
                 pos_simple_fn_integral m s'' c z)
Proof
    rpt STRIP_TAC
 >> (MP_TAC o Q.SPECL [`m`,`f`,`s`,`a`,`x`,`g`,`s'`,`b`,`y`]) pos_simple_fn_integral_present
 >> RW_TAC std_ss []
 >> ASM_SIMP_TAC std_ss []
 >> qexistsl_tac [`k`,`c`,`(\i. if (i IN k /\ ~(c i = {})) then (z i - z' i) else 0)`]
 >> REV_FULL_SIMP_TAC std_ss [pos_simple_fn_integral_def]
 (* expand `pos_simple_fn` without touching the goal *)
 >> Q.PAT_X_ASSUM `pos_simple_fn m f s a x`
      (STRIP_ASSUME_TAC o (REWRITE_RULE [pos_simple_fn_def]))
 >> Q.PAT_X_ASSUM `pos_simple_fn m g s' b y`
      (STRIP_ASSUME_TAC o (REWRITE_RULE [pos_simple_fn_def]))
 >> `pos_simple_fn m f k c z`
       by (FULL_SIMP_TAC std_ss [pos_simple_fn_def] >> METIS_TAC [])
 >> `pos_simple_fn m g k c z'`
       by (FULL_SIMP_TAC std_ss [pos_simple_fn_def] >> METIS_TAC [])
 >> `!x. k x <=> x IN k` by METIS_TAC [SPECIFICATION]
 >> Know `!x. x IN k ==> Normal (z x - z' x) * measure m (c x) <> NegInf`
 >- (RW_TAC std_ss [] \\
     Cases_on `c x' = {}`
     >- METIS_TAC [MEASURE_EMPTY, mul_rzero, extreal_of_num_def, extreal_not_infty] \\
    `?y. y IN c x'` by METIS_TAC [CHOICE_DEF] \\
    `f y' = Normal (z  x')` by METIS_TAC [pos_simple_fn_def, pos_simple_fn_thm1] \\
    `g y' = Normal (z' x')` by METIS_TAC [pos_simple_fn_def, pos_simple_fn_thm1] \\
     Suff `y' IN m_space m`
     >- (DISCH_TAC \\
        `0 <= z x' - z' x'` by METIS_TAC [extreal_le_eq, REAL_SUB_LE, extreal_of_num_def] \\
         METIS_TAC [mul_not_infty, positive_not_infty, MEASURE_SPACE_POSITIVE]) \\
    `c x' IN measurable_sets m` by PROVE_TAC [] \\
     Suff `c x' SUBSET m_space m` >- METIS_TAC [SUBSET_DEF] \\
     fs [measure_space_def, sigma_algebra_def, algebra_def] \\
     METIS_TAC [subset_class_def])
 >> DISCH_TAC
 >> reverse CONJ_TAC
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
 >> `!x. x IN m_space m ==> g x <> NegInf`
        by METIS_TAC [lt_infty, lte_trans, extreal_not_infty, extreal_of_num_def]
 >> SIMP_TAC std_ss [pos_simple_fn_def]
 >> CONJ_TAC
 >- METIS_TAC [le_sub_imp, add_lzero]
 >> reverse (RW_TAC real_ss [])
 >- (REWRITE_TAC [REAL_SUB_LE] \\
    `?q. q IN c i` by METIS_TAC [CHOICE_DEF] \\
     Suff `q IN m_space m`
     >- (METIS_TAC [pos_simple_fn_thm1, REAL_SUB_LE, extreal_le_def]) \\
    `c i IN measurable_sets m` by PROVE_TAC [] \\
     Suff `c i SUBSET m_space m` >- METIS_TAC [SUBSET_DEF] \\
     fs [measure_space_def, sigma_algebra_def, algebra_def] \\
     METIS_TAC [subset_class_def])
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
     SIGMA (\i. Normal (z i) * indicator_fn (c i) x') k` by METIS_TAC [] >> POP_ORW
 >> `SIGMA (\i. Normal (y i) * indicator_fn (b i) x') s' =
     SIGMA (\i. Normal (z' i) * indicator_fn (c i) x') k` by METIS_TAC [] >> POP_ORW
 >> `(\x. Normal (z x) * indicator_fn (c x) x' - Normal (z' x) * indicator_fn (c x) x') =
     (\x. (\x. Normal (z x) * indicator_fn (c x) x') x - (\x. Normal (z' x) * indicator_fn (c x) x') x)`
          by METIS_TAC [] >> POP_ORW
 >> (MATCH_MP_TAC o UNDISCH o Q.SPEC `k` o GSYM o INST_TYPE [alpha |-> ``:num``])
       EXTREAL_SUM_IMAGE_SUB
 >> DISJ1_TAC
 >> RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone]
 >> RW_TAC std_ss [extreal_of_num_def, extreal_not_infty]
QED

Theorem psfis_sub :
    !m f g a b. measure_space m /\ measure m (m_space m) <> PosInf /\
               (!x. x IN m_space m ==> g x <= f x) /\
               (!x. x IN m_space m ==> g x <> PosInf) /\
                a IN psfis m f /\ b IN psfis m g ==> (a - b) IN psfis m (\x. f x - g x)
Proof
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
 >> MATCH_MP_TAC pos_simple_fn_integral_sub >> RW_TAC std_ss []
QED

(* ---------------------------------------------------- *)
(* Properties of Integrals of Positive Functions        *)
(* ---------------------------------------------------- *)

Theorem pos_fn_integral_pos_simple_fn :
    !m f s a x. measure_space m /\ pos_simple_fn m f s a x ==>
               (pos_fn_integral m f = pos_simple_fn_integral m s a x)
Proof
    RW_TAC std_ss [pos_fn_integral_def, sup_eq', IN_psfis_eq,
                   GSPECIFICATION]
 >- METIS_TAC [pos_simple_fn_integral_mono]
 >> POP_ASSUM MATCH_MP_TAC
 >> METIS_TAC [le_refl]
QED

Theorem pos_fn_integral_mspace :
    !m f. measure_space m /\ (!x. x IN m_space m ==> 0 <= f x) ==>
         (pos_fn_integral m f = pos_fn_integral m (\x. f x * indicator_fn (m_space m) x))
Proof
    RW_TAC std_ss [pos_fn_integral_def,sup_eq]
 >- (RW_TAC real_ss [le_sup] \\
     POP_ASSUM MATCH_MP_TAC \\
     ONCE_REWRITE_TAC [GSYM SPECIFICATION] \\
     POP_ASSUM (MP_TAC o REWRITE_RULE [Once (GSYM SPECIFICATION)]) \\
     RW_TAC real_ss [GSPECIFICATION, indicator_fn_def] \\
     Q.EXISTS_TAC `(\x. g x * indicator_fn (m_space m) x)` \\
     reverse (RW_TAC real_ss [indicator_fn_def, IN_psfis_eq, mul_rone, mul_rzero, le_refl]) \\
     FULL_SIMP_TAC std_ss [IN_psfis_eq, pos_simple_fn_def] \\
     qexistsl_tac [`s`, `a`, `x`] \\
     RW_TAC real_ss [mul_rzero, le_refl, mul_rone] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS \\
     RW_TAC std_ss [mul_rzero,le_refl, mul_rone, indicator_fn_def] \\
     METIS_TAC [extreal_of_num_def, extreal_le_def])
 >> RW_TAC real_ss [sup_le]
 >> POP_ASSUM (MP_TAC o REWRITE_RULE [Once (GSYM SPECIFICATION)])
 >> RW_TAC real_ss [GSPECIFICATION]
 >> Q.PAT_X_ASSUM `!z. Q z ==> z <= y` MATCH_MP_TAC
 >> RW_TAC std_ss [Once (GSYM SPECIFICATION),GSPECIFICATION]
 >> Q.EXISTS_TAC `(\x. g x * indicator_fn (m_space m) x)`
 >> RW_TAC std_ss [IN_psfis_eq]
 >- (FULL_SIMP_TAC real_ss [IN_psfis_eq, pos_simple_fn_def, indicator_fn_def] \\
     qexistsl_tac [`s`, `a`, `x`] \\
     RW_TAC real_ss [le_refl, mul_rzero, mul_rone] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS \\
     RW_TAC std_ss [mul_rzero, le_refl, mul_rone, indicator_fn_def] \\
     METIS_TAC [extreal_of_num_def, extreal_le_def])
 >> FULL_SIMP_TAC std_ss [indicator_fn_def, le_refl, mul_rzero, mul_rone]
 >> METIS_TAC [mul_rone, mul_rzero]
QED

Theorem pos_fn_integral_zero :
    !m. measure_space m ==> (pos_fn_integral m (\x. 0) = 0)
Proof
    RW_TAC std_ss [pos_fn_integral_def, sup_eq']
 >- (fs [GSPECIFICATION] \\
     MATCH_MP_TAC psfis_mono \\
     qexistsl_tac [`m`, `g`, `(\x. 0)`] \\
     RW_TAC std_ss [psfis_zero])
 >> POP_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [GSPECIFICATION]
 >> Q.EXISTS_TAC `(\x. 0)`
 >> RW_TAC std_ss [le_refl, psfis_zero]
QED

Theorem pos_fn_integral_mono :
    !m f g. (!x. x IN m_space m ==> 0 <= f x) /\
            (!x. x IN m_space m ==> f x <= g x) ==>
            pos_fn_integral m f <= pos_fn_integral m g
Proof
    RW_TAC std_ss [pos_fn_integral_def]
 >> MATCH_MP_TAC sup_le_sup_imp
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC `x`
 >> RW_TAC std_ss [le_refl]
 >> `x IN {r | ?g. r IN psfis m g /\ !x. x IN m_space m ==> g x <= f x}`
       by METIS_TAC [IN_DEF]
 >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
 >> `?g. x IN psfis m g /\ !x. x IN m_space m ==> g x <= f x`
       by (FULL_SIMP_TAC std_ss [GSPECIFICATION] >> METIS_TAC [])
 >> FULL_SIMP_TAC std_ss [GSPECIFICATION]
 >> METIS_TAC [le_trans]
QED

val pos_fn_integral_mono_mspace = pos_fn_integral_mono;

(* added `x IN m_space m` *)
Theorem pos_fn_integral_pos :
    !m f. measure_space m /\ (!x. x IN m_space m ==> 0 <= f x) ==>
          0 <= pos_fn_integral m f
Proof
    RW_TAC std_ss []
 >> `0 = pos_fn_integral m (\x. 0)` by METIS_TAC [pos_fn_integral_zero]
 >> POP_ORW
 >> MATCH_MP_TAC pos_fn_integral_mono
 >> RW_TAC std_ss [le_refl]
QED

Theorem pos_fn_integral_cmul :
    !m f c. measure_space m /\ (!x. x IN m_space m ==> 0 <= f x) /\ 0 <= c ==>
           (pos_fn_integral m (\x. Normal c * f x) = Normal c * pos_fn_integral m f)
Proof
    RW_TAC std_ss []
 >> Cases_on `c = 0`
 >- RW_TAC std_ss [GSYM extreal_of_num_def,mul_lzero,pos_fn_integral_zero]
 >> `0 < c` by FULL_SIMP_TAC std_ss [REAL_LT_LE]
 >> RW_TAC std_ss [pos_fn_integral_def, sup_eq']
 >- (Suff `y / (Normal c) <= sup {r | ?g. r IN psfis m g /\ !x. x IN m_space m ==> g x <= f x}`
     >- METIS_TAC [le_ldiv, mul_comm] \\
     RW_TAC std_ss [le_sup'] \\
     POP_ASSUM MATCH_MP_TAC \\
     fs [GSPECIFICATION] \\
     Q.EXISTS_TAC `(\x. g x / (Normal c))` \\
     reverse (RW_TAC std_ss [])
     >- METIS_TAC [mul_comm, le_ldiv] \\
     RW_TAC std_ss [extreal_div_def] \\
    `inv (Normal c) * y IN psfis m (\x. inv (Normal c) * g x)`
       by METIS_TAC [psfis_cmul, extreal_inv_def, REAL_LE_INV] \\
    `(\x. g x * inv (Normal c)) = (\x. inv (Normal c) * g x)`
       by RW_TAC std_ss [FUN_EQ_THM, mul_comm] \\
     RW_TAC std_ss [Once mul_comm])
 >> Suff `sup {r | ?g. r IN psfis m g /\ !x. x IN m_space m ==> g x <= f x} <= y / Normal c`
 >- METIS_TAC [le_rdiv, extreal_not_infty, mul_comm]
 >> RW_TAC std_ss [sup_le']
 >> fs [GSPECIFICATION]
 >> Suff `y' * Normal c <= y` >- METIS_TAC [le_rdiv, extreal_not_infty]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC `(\x. Normal c * g x)`
 >> RW_TAC std_ss []
 >- METIS_TAC [psfis_cmul, mul_comm, extreal_not_infty]
 >> METIS_TAC [le_lmul_imp, extreal_of_num_def, extreal_lt_eq, lt_le]
QED

Theorem pos_fn_integral_indicator :
    !m s. measure_space m /\ s IN measurable_sets m ==>
         (pos_fn_integral m (indicator_fn s) = measure m s)
Proof
    METIS_TAC [pos_fn_integral_pos_simple_fn, pos_simple_fn_integral_indicator]
QED

Theorem pos_fn_integral_cmul_indicator :
    !m s c. measure_space m /\ s IN measurable_sets m /\ 0 <= c ==>
           (pos_fn_integral m (\x. Normal c * indicator_fn s x) = Normal c * measure m s)
Proof
    RW_TAC std_ss []
 >> `!x. 0 <= indicator_fn s x`
       by RW_TAC std_ss [indicator_fn_def, le_refl, le_01]
 >> RW_TAC std_ss [pos_fn_integral_cmul]
 >> METIS_TAC [pos_fn_integral_pos_simple_fn, pos_simple_fn_integral_indicator]
QED

Theorem pos_fn_integral_const :
    !m c. measure_space m /\ measure m (m_space m) < PosInf /\ 0 <= c ==>
         (pos_fn_integral m (\x. Normal c) = Normal c * measure m (m_space m))
Proof
    rpt STRIP_TAC
 >> Know ‘pos_fn_integral m (\x. Normal c)  =
          pos_fn_integral m (\x. (\x. Normal c) x * indicator_fn (m_space m) x)’
 >- (MATCH_MP_TAC pos_fn_integral_mspace \\
     rw [extreal_of_num_def, extreal_le_eq])
 >> BETA_TAC >> Rewr'
 >> MATCH_MP_TAC pos_fn_integral_cmul_indicator
 >> simp [MEASURE_SPACE_MSPACE_MEASURABLE]
QED

Theorem pos_fn_integral_sum_cmul_indicator :
    !m s a x. measure_space m /\ FINITE s /\ (!i:num. i IN s ==> 0 <= x i) /\
             (!i:num. i IN s ==> a i IN measurable_sets m) ==>
             (pos_fn_integral m (\t. SIGMA (\i:num. Normal (x i) * indicator_fn (a i) t) s) =
              SIGMA (\i. Normal (x i) * measure m (a i)) s)
Proof
    RW_TAC std_ss []
 >> Cases_on `s = {}`
 >- RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, pos_fn_integral_zero]
 >> `!i. i IN s ==> pos_simple_fn m (indicator_fn (a i)) {0:num; 1}
                                    (\n. if n = 0 then m_space m DIFF (a i) else (a i))
                                    (\n:num. if n = 0 then 0 else 1)`
       by METIS_TAC [pos_simple_fn_indicator_alt]
 >> `!i. i IN s ==> pos_simple_fn m (\t. Normal (x i) * indicator_fn (a i) t) {0:num; 1}
                                    (\n:num. if n = 0 then m_space m DIFF (a i) else (a i))
                                    (\n:num. (x i) * (if n = 0 then 0 else 1))`
       by METIS_TAC [pos_simple_fn_cmul_alt]
 >> (MP_TAC o Q.SPECL [`m`,`(\i. (\t. Normal (x i) * indicator_fn (a i) t))`,
                       `(\i. {0; 1})`,
                       `(\i. (\n. if n = 0 then m_space m DIFF a i else a i))`,
                       `(\i. (\n. x i * if n = 0 then 0 else 1))`,`s`] o
     INST_TYPE [beta |-> ``:num``]) pos_simple_fn_integral_sum_alt
 >> `!i t. i IN s ==> Normal (x i) * indicator_fn (a i) t <> NegInf`
       by RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone, num_not_infty]
 >> RW_TAC std_ss []
 >> `{1:num} DELETE 0 = {1}`
       by METIS_TAC [DELETE_NON_ELEMENT, EVAL ``0=1:num``, EXTENSION, IN_DELETE,
                     IN_SING, NOT_IN_EMPTY]
 >> `FINITE {1:num}` by RW_TAC std_ss [FINITE_SING]
 >> `!i:num. i IN s ==>
             (pos_simple_fn_integral m {0:num; 1}
                                       (\n:num. if n = 0 then m_space m DIFF a i else a i)
                                       (\n:num. x i * if n = 0 then 0 else 1) =
              Normal (x i) * measure m (a i))`
       by (RW_TAC real_ss [pos_simple_fn_integral_def] \\
          `!n:num. n IN {0;1} ==>
                   (\n. Normal (x i * if n = 0 then 0 else 1) *
                        measure m (if n = 0 then m_space m DIFF a i else a i)) n <> NegInf`
              by (RW_TAC real_ss [GSYM extreal_of_num_def, num_not_infty, mul_lzero] \\
                  METIS_TAC [mul_not_infty, positive_not_infty,
                             MEASURE_SPACE_POSITIVE, IN_INSERT]) \\
           (MP_TAC o Q.SPEC `0` o UNDISCH o
            Q.SPECL [`(\n. Normal (x (i:num) * if n = 0 then 0 else 1) *
                           measure m (if n = 0 then m_space m DIFF a i else a i))`,`{1}`] o
            INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_PROPERTY \\
           RW_TAC real_ss [mul_lzero, add_lzero, EXTREAL_SUM_IMAGE_SING, GSYM extreal_of_num_def])
 >> (MP_TAC o Q.SPEC `(\i:num. pos_simple_fn_integral m {0:num; 1}
                               (\n:num. if n = 0 then m_space m DIFF a i else a i)
                               (\n:num. x i * if n = 0 then 0 else 1:real))` o
     UNDISCH o Q.SPEC `s` o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_IN_IF
 >> `!x'. x' IN s ==> (\i. pos_simple_fn_integral m {0; 1}
             (\n. if n = 0 then m_space m DIFF a i else a i)
             (\n. x i * if n = 0 then 0 else 1)) x' <> NegInf`
       by (RW_TAC std_ss [] \\
           METIS_TAC [mul_not_infty, positive_not_infty, MEASURE_SPACE_POSITIVE, IN_INSERT])
 >> RW_TAC std_ss []
 >> FULL_SIMP_TAC std_ss []
 >> (MP_TAC o Q.SPECL [`s:num->bool`,`s`,`(\i:num. Normal (x i) * measure m (a i))`] o
     INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_IF_ELIM
 >> `!x'. x' IN s ==> Normal (x x') * measure m (a x') <> NegInf`
       by METIS_TAC [mul_not_infty, positive_not_infty, MEASURE_SPACE_POSITIVE, IN_INSERT]
 >> RW_TAC std_ss []
 >> FULL_SIMP_TAC std_ss [SPECIFICATION]
 >> NTAC 7 (POP_ASSUM (K ALL_TAC))
 >> POP_ASSUM (MP_TAC o GSYM)
 >> RW_TAC std_ss []
 >> RW_TAC std_ss [pos_fn_integral_def, sup_eq]
 >- (POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) \\
     RW_TAC std_ss [GSPECIFICATION, IN_psfis_eq] \\
     MATCH_MP_TAC pos_simple_fn_integral_mono \\
     Q.EXISTS_TAC `g` \\
     Q.EXISTS_TAC `(\t. SIGMA (\i. Normal (x i) * indicator_fn (a i) t) s)` \\
     RW_TAC std_ss [])
 >> POP_ASSUM MATCH_MP_TAC
 >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
 >> RW_TAC std_ss [GSPECIFICATION,IN_psfis_eq]
 >> Q.EXISTS_TAC `(\t. SIGMA (\i. Normal (x i) * indicator_fn (a i) t) s)`
 >> RW_TAC real_ss []
 >> METIS_TAC [le_refl]
QED

(***************************************************************************)
(*                       Sequences - Convergence                           *)
(***************************************************************************)

(* added `x IN m_space m` at various places *)
Theorem lebesgue_monotone_convergence_lemma[local] :
    !m f fi g r'.
        measure_space m /\
        (!i. fi i IN measurable (m_space m, measurable_sets m) Borel) /\
        (!x. x IN m_space m ==> mono_increasing (\i. fi i x)) /\
        (!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = f x)) /\
        (r' IN psfis m g) /\ (!x. x IN m_space m ==> g x <= f x) /\
        (!i x. x IN m_space m ==> 0 <= fi i x) ==>
         r' <= sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV)
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC `r = sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV)`
 >> Q.ABBREV_TAC `ri = (\i. pos_fn_integral m (fi i))`
 >> MATCH_MP_TAC le_mul_epsilon
 >> RW_TAC std_ss []
 >> (Cases_on `z` \\
     FULL_SIMP_TAC std_ss [le_infty, lt_infty, extreal_not_infty, extreal_of_num_def])
 >> FULL_SIMP_TAC std_ss [extreal_le_def, extreal_lt_eq]
 (* stage work *)
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
 >> `g IN measurable (m_space m, measurable_sets m) Borel`
      by METIS_TAC [IN_psfis_eq, IN_MEASURABLE_BOREL_POS_SIMPLE_FN]
 >> `(\t. Normal r'' * g t) IN measurable (m_space m, measurable_sets m) Borel`
      by (MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL \\
          qexistsl_tac [`g`, `r''`] \\
          RW_TAC real_ss [extreal_not_infty] \\
          METIS_TAC [measure_space_def])
 >> `!n:num. {t | Normal r'' * g t <= fi n t} INTER m_space m =
             {t | 0 <= (fi n t) - Normal r'' * (g t)} INTER m_space m`
      by (RW_TAC real_ss [EXTENSION, GSPECIFICATION, IN_INTER] \\
          METIS_TAC [pos_simple_fn_not_infty, mul_not_infty, add_lzero,
                     le_sub_eq, num_not_infty])
 >> `!n. (\t. fi n t - Normal r'' * g t) IN measurable (m_space m, measurable_sets m) Borel`
      by (RW_TAC std_ss [] \\
          MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
          Q.EXISTS_TAC `fi n` \\
          Q.EXISTS_TAC `(\t. Normal r'' * g t)` \\
          RW_TAC std_ss [space_def] >| (* 2 subgoals *)
          [ FULL_SIMP_TAC std_ss [measure_space_def],
            DISJ1_TAC \\
            CONJ_TAC >- (METIS_TAC [pos_not_neginf, GSYM extreal_of_num_def]) \\
            METIS_TAC [pos_simple_fn_not_infty, mul_not_infty] ])
 >> `!n. {t | Normal r'' * g t <= fi n t} INTER m_space m IN measurable_sets m`
      by METIS_TAC [IN_MEASURABLE_BOREL_ALL, m_space_def, space_def, subsets_def,
                    measurable_sets_def, measure_space_def, extreal_of_num_def]
 >> `!n. b n INTER m_space m IN measurable_sets m` by (Q.UNABBREV_TAC `b` >> METIS_TAC [])
 (* stage work *)
 >> Suff `r' = sup (IMAGE (\n. pos_fn_integral m
                                 (\x. g x * indicator_fn (b n INTER m_space m) x)) UNIV)`
 >- (Q.UNABBREV_TAC `r` \\
     RW_TAC std_ss [le_sup'] \\
     Cases_on `r'' = 0`
     >- (RW_TAC std_ss [mul_lzero, GSYM extreal_of_num_def] \\
         MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `ri (1:num)` \\
         reverse CONJ_TAC
         >- (POP_ASSUM MATCH_MP_TAC \\
             RW_TAC std_ss [IN_IMAGE, IN_UNIV] >> METIS_TAC []) \\
         Q.UNABBREV_TAC `ri` \\
         RW_TAC std_ss [] \\
         METIS_TAC [pos_fn_integral_pos, extreal_of_num_def]) \\
    `0 < r''` by METIS_TAC [REAL_LT_LE] \\
    `0 < Normal r''` by METIS_TAC [extreal_lt_eq, extreal_of_num_def, REAL_LE_REFL] \\
     ONCE_REWRITE_TAC [mul_comm] \\
     RW_TAC std_ss [le_rdiv] \\
     RW_TAC std_ss [sup_le'] \\
     POP_ASSUM MP_TAC >> RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
     RW_TAC std_ss [GSYM le_rdiv] \\
     ONCE_REWRITE_TAC [mul_comm] \\
    `!x. x IN m_space m ==> 0 <= (\x. g x * indicator_fn (b n INTER m_space m) x) x`
        by (RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, le_refl] \\
            FULL_SIMP_TAC std_ss [pos_simple_fn_def]) \\
     FULL_SIMP_TAC std_ss [GSYM pos_fn_integral_cmul] \\
    `!x. x IN m_space m ==> (\x. Normal r'' * (g x * indicator_fn (b n INTER m_space m) x)) x <= fi n x`
        by (Q.UNABBREV_TAC `b` \\
            RW_TAC real_ss [indicator_fn_def, GSPECIFICATION, IN_INTER, mul_rzero, mul_rone] \\
            METIS_TAC [extreal_of_num_def]) \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `pos_fn_integral m (fi n)` \\
     CONJ_TAC >- (MATCH_MP_TAC pos_fn_integral_mono >> METIS_TAC [le_mul, lt_le]) \\
     RW_TAC std_ss [] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
     Q.EXISTS_TAC `n` >> REWRITE_TAC [])
 >> `!n:num. (\x. g x * indicator_fn (b n INTER m_space m) x) =
             (\t. SIGMA (\i. Normal (x i) * indicator_fn (a i INTER (b n INTER m_space m)) t) s)`
      by (RW_TAC std_ss [] >> FUN_EQ_TAC \\
          RW_TAC std_ss [] \\
          Cases_on `~(x' IN m_space m)`
          >- (RW_TAC real_ss [indicator_fn_def, IN_INTER, mul_rone, mul_rzero] \\
              METIS_TAC [pos_simple_fn_def,EXTREAL_SUM_IMAGE_ZERO]) \\
          RW_TAC real_ss [indicator_fn_def, IN_INTER, mul_rone, mul_rzero]
          >- FULL_SIMP_TAC real_ss [pos_simple_fn_def, indicator_fn_def] \\
          FULL_SIMP_TAC std_ss [pos_simple_fn_def, EXTREAL_SUM_IMAGE_ZERO])
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
 >- (RW_TAC std_ss [] \\
     MATCH_MP_TAC le_lmul_imp \\
     RW_TAC std_ss []
     >- METIS_TAC [pos_simple_fn_def, extreal_le_def, extreal_of_num_def] \\
     MATCH_MP_TAC INCREASING \\
     RW_TAC std_ss [MEASURE_SPACE_INCREASING] \\
     RW_TAC std_ss [SUBSET_DEF,IN_INTER] \\
     Q.UNABBREV_TAC `b` \\
     FULL_SIMP_TAC std_ss [GSPECIFICATION] \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `fi n x'` \\
     RW_TAC real_ss [] \\
     FULL_SIMP_TAC real_ss [ext_mono_increasing_suc])
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
      by (RW_TAC std_ss [lt_infty] \\
          MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC `0` \\
          RW_TAC std_ss [] >- METIS_TAC [lt_infty, num_not_infty] \\
          RW_TAC std_ss [le_sup] \\
          MATCH_MP_TAC le_trans \\
          Q.EXISTS_TAC `Normal (x x') * measure m ((a x') INTER ((b 1) INTER m_space m))` \\
          RW_TAC std_ss [] \\
          MATCH_MP_TAC le_lmul_imp \\
          CONJ_TAC >- METIS_TAC [extreal_le_def, extreal_of_num_def, pos_simple_fn_def] \\
          RW_TAC std_ss [le_sup] \\
          POP_ASSUM MATCH_MP_TAC \\
          ONCE_REWRITE_TAC [GSYM SPECIFICATION] \\
          RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
          METIS_TAC [])
 >> RW_TAC std_ss []
 >> `!i. BIGUNION (IMAGE (\n. a i INTER (b n INTER m_space m)) UNIV) = a i INTER m_space m`
      by (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_INTER, IN_UNIV] \\
          EQ_TAC >- METIS_TAC [] \\
          RW_TAC std_ss [] \\
          Q.UNABBREV_TAC `b` \\
          RW_TAC real_ss [GSPECIFICATION] \\
         `f x' = sup (IMAGE (\i. fi i x') UNIV)` by FULL_SIMP_TAC std_ss [] \\
          Cases_on `g x' = 0` >- METIS_TAC [mul_rzero,extreal_of_num_def] \\
         `Normal r'' * g x' < f x'`
            by (Cases_on `g x' = f x'`
                >- (`0 < f x'` by METIS_TAC [le_lt, pos_simple_fn_def] \\
                    METIS_TAC [lt_rmul, mul_lone, IN_psfis_eq, pos_simple_fn_not_infty,
                               extreal_lt_eq, extreal_of_num_def]) \\
               `g x' < f x'` by METIS_TAC [le_lt] \\
                METIS_TAC [lt_mul2, mul_lone, extreal_not_infty, pos_simple_fn_not_infty,
                           extreal_lt_eq, extreal_of_num_def, extreal_le_def, psfis_pos]) \\
          Suff `?n. Normal r'' * g x' <= (\n. fi n x') n` >- RW_TAC std_ss [] \\
          MATCH_MP_TAC sup_le_mono \\
          CONJ_TAC >- FULL_SIMP_TAC std_ss [ext_mono_increasing_def,
                                            ext_mono_increasing_suc] \\
          METIS_TAC [])
 >> `!i. i IN s==> (a i INTER m_space m = a i)`
      by METIS_TAC [pos_simple_fn_def,SUBSET_INTER1,MEASURE_SPACE_SUBSET_MSPACE]
 >> `!i. i IN s ==> (sup (IMAGE (measure m o (\n. a i INTER (b n INTER m_space m))) UNIV) =
                     measure m (a i))`
      by (RW_TAC std_ss [] \\
          MATCH_MP_TAC MONOTONE_CONVERGENCE \\
          RW_TAC std_ss [IN_FUNSET, IN_UNIV] \\
          RW_TAC std_ss [SUBSET_DEF, IN_INTER] \\
          Q.UNABBREV_TAC `b` \\
          FULL_SIMP_TAC std_ss [GSPECIFICATION] \\
          MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `fi n x'` \\
          RW_TAC real_ss [] \\
          FULL_SIMP_TAC real_ss [ext_mono_increasing_suc])
 >> FULL_SIMP_TAC std_ss [o_DEF]
 >> `r' = SIGMA (\i. Normal (x i) * measure m (a i)) s`
      by METIS_TAC [IN_psfis_eq, psfis_unique, pos_simple_fn_integral_def,
                    pos_simple_fn_integral_unique]
 >> POP_ORW
 >> `!i. i IN s ==> (\i. Normal (x i) * measure m (a i)) i <> NegInf`
      by METIS_TAC []
 >> (MP_TAC o Q.SPEC `(\i. Normal (x i) * measure m (a i))` o
     UNDISCH o Q.ISPEC `s:num->bool`) EXTREAL_SUM_IMAGE_IN_IF
 >> RW_TAC std_ss []
QED

(************************************************************)
(*     LEBESGUE MONOTONE CONVERGENCE (Beppo Levi)           *)
(************************************************************)

(* NOTE: this is actually Theorem 9.6 (Beppo Levi) [1, p.75] for positive functions,
         the full version of "Monotone convergence" theroem for arbitrary integrable
         functions (Theorem 12.1 [1, p.96]) is not formalized yet.

   This theorem is also named after Beppo Levi, an Italian mathematician [4].

   Removed unnecessary ‘!x. x IN m_space m ==> 0 <= f x’ (Chun Tian)
 *)
Theorem lebesgue_monotone_convergence :
    !m f fi. measure_space m /\
        (!i. fi i IN measurable (m_space m, measurable_sets m) Borel) /\
        (!i x. x IN m_space m ==> 0 <= fi i x) /\
        (!x. x IN m_space m ==> mono_increasing (\i. fi i x)) /\
        (!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = f x)) ==>
        (pos_fn_integral m f = sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV))
Proof
    rpt STRIP_TAC
 >> Know ‘!x. x IN m_space m ==> 0 <= f x’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!x. x IN m_space m ==> _ = f x’ (MP_TAC o (Q.SPEC ‘x’)) \\
     RW_TAC std_ss [] \\
     POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) \\
     rw [le_sup'] \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC ‘fi 0 x’ \\
     CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     POP_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘0’ >> REWRITE_TAC [])
 >> POP_ASSUM MP_TAC
 >> reverse (RW_TAC std_ss [GSYM le_antisym])
 >- (RW_TAC std_ss [sup_le'] \\
     POP_ASSUM MP_TAC >> RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
     MATCH_MP_TAC pos_fn_integral_mono \\
     RW_TAC std_ss [] \\
     Q.PAT_X_ASSUM `!x. x IN m_space m ==> sup (IMAGE _ UNIV) <= f x /\ _`
        (MP_TAC o GSYM o UNDISCH o Q.SPEC `x`) \\
     RW_TAC std_ss [] \\
     FULL_SIMP_TAC std_ss [sup_le'] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
     Q.EXISTS_TAC `i` >> REWRITE_TAC [])
 >> Q.ABBREV_TAC `r = sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV)`
 >> RW_TAC std_ss [pos_fn_integral_def, sup_le]
 >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
 >> RW_TAC std_ss [GSPECIFICATION]
 >> METIS_TAC [lebesgue_monotone_convergence_lemma, le_antisym]
QED

(* removed unnecessary ‘!x. x IN m_space m ==> 0 <= f x’ (Chun Tian) *)
Theorem lebesgue_monotone_convergence_subset :
    !m f fi A. measure_space m /\
        (!i. fi i IN measurable (m_space m, measurable_sets m) Borel) /\
        (!i x. x IN m_space m ==> 0 <= fi i x) /\
        (!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = f x)) /\
        (!x. x IN m_space m ==> mono_increasing (\i. fi i x)) /\
         A IN measurable_sets m ==>
        (pos_fn_integral m (\x. f x * indicator_fn A x) =
         sup (IMAGE (\i. pos_fn_integral m (\x. fi i x * indicator_fn A x)) UNIV))
Proof
    RW_TAC std_ss []
 >> (MP_TAC o Q.SPECL [`m`, `(\x. f x * indicator_fn A x)`,
                       `(\i. (\x. fi i x * indicator_fn A x))`])
       lebesgue_monotone_convergence
 >> RW_TAC std_ss []
 >> POP_ASSUM MATCH_MP_TAC
 >> CONJ_TAC
 >- METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR, measure_space_def, subsets_def,
               measurable_sets_def]
 >> CONJ_TAC >- RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,le_refl]
 >> CONJ_TAC
 >- (RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, le_refl, ext_mono_increasing_def] \\
     FULL_SIMP_TAC std_ss [ext_mono_increasing_def])
 >> RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero]
 >> Suff `IMAGE (\i:num. 0:extreal) UNIV = (\y. y = 0)` >- RW_TAC std_ss [sup_const]
 >> RW_TAC std_ss [EXTENSION, IN_ABS, IN_IMAGE, IN_UNIV]
QED

(**********************************************************)
(*  Existence of convergent sequence (fn_seq)             *)
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

(* NOTE: Given the following (s,a,x) for a sequence of positive simple function:

   s = `count (4 ** n + 1)`
   a = `(\k. if k IN count (4 ** n) then
               {x | x IN m_space m /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n}
             else
               {x | x IN m_space m /\ 2 pow n <= f x})`
   x = `(\k. if k IN count (4 ** n) then &k / 2 pow n else 2 pow n)`

   We have (as part of lemma_fn_seq_in_psfis):
   |- fn_seq m f = \n t. SIGMA (\i. Normal (x i) * indicator_fn (a i) t) s)
   |- fn_seq_integral m f n = pos_simple_fn_integral m s a x
 *)

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
    RW_TAC real_ss [fn_seq_def,indicator_fn_def,GSPECIFICATION,mul_rzero,add_rzero]
 >> METIS_TAC [FINITE_COUNT,EXTREAL_SUM_IMAGE_ZERO]);

(*********************************)
(*       fn_(x) positive         *)
(*********************************)

Theorem lemma_fn_seq_positive :
    !m f n x. 0 <= f x ==> (0 <= fn_seq m f n x)
Proof
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
 >> RW_TAC real_ss [REAL_POW_LT,REAL_LT_IMP_LE]
QED

(*******************************************************************************)
(*                        MONOTONICALLY INCREASING                             *)
(*******************************************************************************)

Theorem lemma_fn_seq_mono_increasing :
    !m f x. 0 <= f x ==> mono_increasing (\n. fn_seq m f n x)
Proof
    RW_TAC std_ss [ext_mono_increasing_suc,ADD1]
 >> Cases_on `~(x IN m_space m)`
 >- RW_TAC real_ss [lemma_fn_4, le_refl]
 >> FULL_SIMP_TAC std_ss []
 >> `!n x k. x IN m_space m /\ (k IN count (4 ** n)) /\
            (&k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n) ==> (fn_seq m f n x = &k / 2 pow n)`
      by RW_TAC std_ss [lemma_fn_1]
 >> `!n x. x IN m_space m /\ 2 pow n <= f x ==> (fn_seq m f n x = 2 pow n)`
      by RW_TAC std_ss [lemma_fn_2]
 >> `!n. 0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
 >> `!n. 0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
 >> `!n k. k IN count (4 ** (n + 1)) /\
          (&k / 2 pow (n + 1) <= f x /\ f x < (&k + 1) / 2 pow (n + 1)) ==>
          (fn_seq m f n x <= fn_seq m f (n + 1) x)`
      by (RW_TAC real_ss [] \\
         `fn_seq m f (n + 1) x = &k / (2 pow (n + 1))` by RW_TAC real_ss [] \\
         `f x <> NegInf` by METIS_TAC [lt_infty, lte_trans, extreal_of_num_def, extreal_not_infty] \\
         `f x <> PosInf` by METIS_TAC [extreal_of_num_def, extreal_pow_def, extreal_not_infty,
                                       lt_infty, lt_trans] \\
         `?r. f x = Normal r` by METIS_TAC [extreal_cases] \\
         `0:real <> 2 pow (n + 1)` by RW_TAC real_ss [] \\
          FULL_SIMP_TAC std_ss [extreal_of_num_def, extreal_pow_def, extreal_div_eq, extreal_add_def,
                                extreal_mul_def, extreal_le_def, extreal_lt_eq] \\
         `&(k + 1) / (2 pow (n + 1)):real = (&(k + 1) / 2) / (2 pow (n + 1) / 2)`
             by RW_TAC real_ss [REAL_DIV_DENOM_CANCEL] \\
         `2 pow (n + 1) / 2 = (2 pow n):real`
             by (RW_TAC std_ss [GSYM ADD1, pow] \\
                 RW_TAC real_ss [REAL_EQ_LDIV_EQ, REAL_MUL_COMM]) \\
         `&k / 2 pow (n + 1) = (&k / 2) / (2 pow (n + 1) / 2):real`
             by RW_TAC real_ss [REAL_DIV_DENOM_CANCEL] \\
          FULL_SIMP_TAC std_ss [] \\
          STRUCT_CASES_TAC (Q.SPEC `k` EVEN_OR_ODD)
          >- (FULL_SIMP_TAC std_ss [EVEN_EXISTS] \\
              FULL_SIMP_TAC real_ss [] \\
             `&k / 2:real = &m'` by RW_TAC real_ss [REAL_EQ_LDIV_EQ] \\
             `&(2 * m' + 1):real < &(2 * m' + 2)` by RW_TAC real_ss [] \\
             `&(2 * m' + 1) / 2:real < &(2 * m' + 2) / 2` by RW_TAC real_ss [REAL_LT_RDIV] \\
             `&(2 * m' + 1) / 2 / (2 pow n):real < &(2 * m' + 2) / 2 / 2 pow n`
                 by RW_TAC real_ss [REAL_LT_RDIV] \\
             `&(2 * m' + 2) / 2 = &(m'+1):real`
                 by RW_TAC real_ss [REAL_EQ_LDIV_EQ, REAL_ADD_LDISTRIB] \\
             `r < &(m' + 1) / 2 pow n` by METIS_TAC [REAL_LT_TRANS] \\
             `&(2 * m') / 2 / 2 pow n = &m' / (2 pow n):real` by METIS_TAC [] \\
              FULL_SIMP_TAC real_ss [] \\
              Cases_on `m' IN count (4 ** n)`
              >- (`fn_seq m f n x = Normal (&m' / 2 pow n)`
                     by METIS_TAC [extreal_le_def, extreal_lt_eq] \\
                  RW_TAC std_ss [le_refl]) \\
              FULL_SIMP_TAC real_ss [IN_COUNT, NOT_LESS] \\
             `4:real pow n <= &m'` by RW_TAC real_ss [REAL_OF_NUM_POW] \\
             `4:real pow n / 2 pow n <= &m' / 2 pow n`
                 by RW_TAC real_ss [REAL_LE_LDIV_EQ, REAL_POS_NZ, REAL_DIV_RMUL] \\
             `2 pow n <= r` by METIS_TAC [REAL_LE_TRANS, REAL_POW_DIV, EVAL ``4/2:real``] \\
             `fn_seq m f n x = Normal (2 pow n)` by METIS_TAC [extreal_le_def, extreal_lt_eq] \\
             `(2 pow n):real <= &m' / 2 pow n` by METIS_TAC [REAL_POW_DIV,EVAL ``4/2:real``] \\
             `&(2*m')/2 = &m':real` by RW_TAC real_ss [] \\
              RW_TAC std_ss [extreal_le_def]) \\
          FULL_SIMP_TAC std_ss [ODD_EXISTS] \\
         `(k - 1) < k` by RW_TAC real_ss [] \\
         `&(k - 1) / 2 < (&k) / 2:real` by RW_TAC real_ss [REAL_LT_LDIV_EQ, REAL_DIV_RMUL] \\
         `&(k - 1) / 2 / 2 pow n < (&k) / 2 / (2 pow n):real`
             by RW_TAC real_ss [REAL_LT_LDIV_EQ, REAL_DIV_RMUL, REAL_POS_NZ] \\
         `&(k - 1) / 2 / 2 pow n <= r` by METIS_TAC [REAL_LTE_TRANS, REAL_LT_IMP_LE] \\
         `&(k - 1):real = 2 * &m'` by RW_TAC real_ss [] \\
         `!x. 2 * x / 2 = x:real` by RW_TAC real_ss [REAL_EQ_LDIV_EQ, REAL_MUL_COMM] \\
         `&m' / (2 pow n) <= r` by METIS_TAC [REAL_MUL] \\
         `&(k + 1):real = 2 * (&m' + 1)` by RW_TAC real_ss [] \\
          FULL_SIMP_TAC real_ss [] \\
         `r < &(m' + 1) / (2 pow n)` by METIS_TAC [REAL_MUL, REAL_ADD] \\
          Cases_on `m' IN count (4 ** n)`
          >- (Q.PAT_X_ASSUM `!n x k. Q` (MP_TAC o Q.SPECL [`n`,`x`, `m'`]) \\
              RW_TAC std_ss [extreal_le_def, extreal_lt_eq] \\
             `&(2 * m'):real <= &SUC (2*m')` by RW_TAC real_ss [] \\
             `&(2 * m') / 2:real <= &SUC (2 * m') / 2`
                 by RW_TAC real_ss [REAL_LE_LDIV_EQ, REAL_DIV_RMUL] \\
             `&(2 * m') / 2 / 2 pow n <= &SUC (2 * m') / 2 / (2 pow n):real`
                 by RW_TAC real_ss [REAL_LE_LDIV_EQ, REAL_DIV_RMUL, REAL_POS_NZ] \\
             `&(2 * m') / 2:real = &m'` by RW_TAC real_ss [REAL_EQ_LDIV_EQ] \\
              FULL_SIMP_TAC real_ss [REAL_LE_TRANS]) \\
          FULL_SIMP_TAC real_ss [IN_COUNT, NOT_LESS] \\
         `4 pow n <= &m':real` by RW_TAC real_ss [REAL_OF_NUM_POW] \\
         `4:real pow n / 2 pow n <= &m' / 2 pow n`
             by RW_TAC real_ss [REAL_LE_LDIV_EQ, REAL_POS_NZ, REAL_DIV_RMUL] \\
         `&(k - 1):real = 2 * &m'` by RW_TAC real_ss [] \\
         `&m' < &k / 2:real` by METIS_TAC [] \\
         `&m' / (2 pow n):real  < &k / 2 / 2 pow n`
             by RW_TAC real_ss [REAL_LT_LDIV_EQ, REAL_POS_NZ, REAL_DIV_RMUL] \\
         `2 pow n <= r`
             by METIS_TAC [REAL_POW_DIV, EVAL ``4/2:real``, REAL_LET_TRANS,
                           REAL_LTE_TRANS, REAL_LT_IMP_LE] \\
         `fn_seq m f n x = Normal (2 pow n)` by METIS_TAC [extreal_le_def, extreal_lt_eq] \\
         `2 pow n <= &m' / (2 pow n):real` by METIS_TAC [REAL_POW_DIV, EVAL ``4/2:real``] \\
         `&(2 * m'):real <= &SUC (2 * m')` by RW_TAC real_ss [] \\
         `&(2 * m') / 2:real <= &SUC (2 * m') / 2`
             by RW_TAC real_ss [REAL_LE_LDIV_EQ, REAL_DIV_RMUL] \\
         `&(2 * m') / 2 / 2 pow n <= &SUC (2 * m') / 2 / (2 pow n):real`
             by RW_TAC real_ss [REAL_LE_LDIV_EQ, REAL_DIV_RMUL, REAL_POS_NZ] \\
         `&(2 * m') / 2:real = &m'` by RW_TAC real_ss [REAL_EQ_LDIV_EQ] \\
          METIS_TAC [REAL_LE_TRANS, extreal_le_def])
 >> `!n. 2 pow (n + 1) <= f x ==> (fn_seq m f n x <= fn_seq m f (n + 1) x)`
       by (RW_TAC real_ss [] \\
          `2:real pow n < 2 pow (n + 1)` by RW_TAC real_ss [REAL_POW_MONO_LT] \\
          `2 pow n < 2 pow (n + 1)`
             by METIS_TAC [extreal_pow_def, extreal_of_num_def, extreal_lt_eq] \\
           METIS_TAC [extreal_le_def, extreal_lt_eq, lte_trans, lt_imp_le])
 >> (MP_TAC o Q.SPECL [`m`,`f`,`n + 1`,`x`]) lemma_fn_3
 >> RW_TAC std_ss []
 >- RW_TAC std_ss []
 >> METIS_TAC []
QED

(*******************************************************************************)
(*                            UPPER BOUNDED BY f                               *)
(*******************************************************************************)

Theorem lemma_fn_seq_upper_bounded[local] :
    !m f n x. 0 <= f x ==> (fn_seq m f n x <= f x)
Proof
    RW_TAC std_ss []
 >> Cases_on `~(x IN m_space m)` >- RW_TAC real_ss [lemma_fn_4]
 >> FULL_SIMP_TAC std_ss []
 >> (MP_TAC o Q.SPECL [`m`,`f`,`n`,`x`]) lemma_fn_3
 >> RW_TAC real_ss []
 >- METIS_TAC [lemma_fn_2,le_refl]
 >> `fn_seq m f n x =  &k / 2 pow n` by RW_TAC real_ss [lemma_fn_1]
 >> RW_TAC std_ss []
QED

(*******************************************************************************)
(*                            f Supremum of fn_seq                             *)
(*******************************************************************************)

Theorem lemma_fn_seq_sup :
    !m f x. x IN m_space m /\ 0 <= f x ==>
            (sup (IMAGE (\n. fn_seq m f n x) UNIV) = f x)
Proof
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
      >> METIS_TAC [EXTREAL_ARCH_POW2, extreal_lt_def])
  >> `!n.  fn_seq m f n x <= f x` by METIS_TAC [lemma_fn_seq_upper_bounded]
  >> `?r. f x = Normal r` by METIS_TAC [extreal_cases,lt_infty,lte_trans,extreal_of_num_def]
  >> `!n. fn_seq m f n x <> PosInf` by METIS_TAC [lt_infty,let_trans]
  >> `!n. fn_seq m f n x <> NegInf`
        by METIS_TAC [lt_infty,lte_trans,lemma_fn_seq_positive,extreal_of_num_def]
  >> `?r. !n. fn_seq m f n x = Normal (r n)`
         by (Q.EXISTS_TAC `\n. @r. fn_seq m f n x = Normal r`
             >> GEN_TAC >> RW_TAC std_ss []
             >> SELECT_ELIM_TAC
                >> RW_TAC std_ss []
             >> METIS_TAC [extreal_cases])
  >> `?N. f x < 2 pow N` by RW_TAC std_ss [EXTREAL_ARCH_POW2]
  >> `!p n. p <= n ==> 2 pow p <= 2 pow n` by METIS_TAC [pow_le_mono,EVAL ``1<=2``]
  >> `!n. N <= n ==> f x < 2 pow n` by METIS_TAC [lte_trans]
  >> `!n. N <= n ==> ?k. k IN count (4 ** n) /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n`
       by METIS_TAC [lemma_fn_3,extreal_lt_def]
  >> `!n. 0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
  >> `!n. 0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
  >> `!n k. &k / 2 pow n = Normal (&k / 2 pow n)`
       by METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_div_eq]
  >> `!n z. Normal z / 2 pow n = Normal (z / 2 pow n)`
       by METIS_TAC [extreal_pow_def,extreal_div_eq,extreal_of_num_def]
  >> `!n. N <= n ==> (f x - 1 / 2 pow n < fn_seq m f n x)`
       by (RW_TAC real_ss []
            >> `?k. k IN count (4 ** n) /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n` by METIS_TAC []
            >> `fn_seq m f n x = &k / 2 pow n` by METIS_TAC [lemma_fn_1]
            >> `Normal (&k + 1) / Normal (2 pow n) = Normal ((&k + 1) / (2 pow n))`
                by METIS_TAC [extreal_div_eq]
            >> `Normal r < Normal ((&k + 1) /  (2 pow n))`
                by METIS_TAC [extreal_pow_def,extreal_of_num_def,extreal_add_def]
            >> FULL_SIMP_TAC std_ss [extreal_lt_eq,GSYM REAL_DIV_ADD,extreal_pow_def,extreal_sub_def,
                                     extreal_of_num_def,extreal_div_eq,extreal_lt_eq,REAL_LT_SUB_RADD]
            >> `r' n = &k / 2 pow n` by METIS_TAC [extreal_div_eq,extreal_11]
            >> FULL_SIMP_TAC std_ss [])
  >> FULL_SIMP_TAC std_ss []
  >> `!n. N <= n ==> (r - 1 / 2 pow n < r' n)`
        by (FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq,extreal_of_num_def,extreal_pow_def,
                                  extreal_div_eq,extreal_add_def]
            >> RW_TAC std_ss []
            >> METIS_TAC [extreal_sub_def,extreal_lt_eq])
  >> `mono_increasing (\n. fn_seq m f n x)` by METIS_TAC [lemma_fn_seq_mono_increasing]
  >> `mono_increasing r'`
        by (FULL_SIMP_TAC std_ss [ext_mono_increasing_def,mono_increasing_def] \\
            METIS_TAC [extreal_le_def])
  >> FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq,extreal_of_num_def,extreal_pow_def,
                           extreal_div_eq,extreal_add_def,extreal_sub_def,extreal_not_infty]
  >> RW_TAC std_ss [GSYM sup_seq,SEQ,GREATER_EQ]
  >> `!n. 1:real / 2 pow n = (1 / 2) pow n` by RW_TAC real_ss [POW_ONE,REAL_POW_DIV]
  >> `!n. r' n < r + 1 / 2 pow n`
       by METIS_TAC [POW_HALF_POS,REAL_LT_ADDR,REAL_LET_TRANS,REAL_LT_IMP_LE]
  >> `!n. N <= n ==> (abs (r' n - r) < 1 / 2 pow n)` by METIS_TAC [ABS_BETWEEN,POW_HALF_POS]
  >> `?N1. (1 / 2) pow N1 < e:real` by RW_TAC std_ss [POW_HALF_SMALL]
  >> `!n. N1 <= n ==> ((1 / 2:real) pow n <= (1 / 2) pow N1)` by RW_TAC std_ss [POW_HALF_MONO]
  >> `!n. N1 <= n ==> ((1 / 2:real) pow n < e)` by METIS_TAC [REAL_LET_TRANS]
  >> Q.EXISTS_TAC `N + N1`
  >> RW_TAC real_ss []
  >> `N <= N + N1` by RW_TAC std_ss [LESS_EQ_ADD]
  >> `N1 <= N + N1` by RW_TAC std_ss [LESS_EQ_ADD]
  >> `N <= n /\ N1 <= n` by METIS_TAC [LESS_EQ_TRANS]
  >> METIS_TAC [REAL_LT_TRANS]
QED

(*******************************************************************************)
(*          SEQ Positive Simple Functions and Define Integral                  *)
(*******************************************************************************)

Theorem lemma_fn_seq_measurable:
    !m f n. measure_space m /\ (!x. x IN m_space m ==> 0 <= f x) /\
            f IN measurable (m_space m,measurable_sets m) Borel ==>
            fn_seq m f n IN measurable (m_space m,measurable_sets m) Borel
Proof
    RW_TAC std_ss [fn_seq_def]
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD >> simp []
 >> qexistsl_tac [‘\x. SIGMA
                  (\k. &k / 2 pow n *
                       indicator_fn
                         {x | x IN m_space m /\ &k / 2 pow n <= f x /\
                              f x < (&k + 1) / 2 pow n} x) (count (4 ** n))’,
                  ‘\x. 2 pow n *
                       indicator_fn {x | x IN m_space m /\ 2 pow n <= f x} x’]
 >> ‘sigma_algebra (m_space m,measurable_sets m)’ by FULL_SIMP_TAC std_ss [measure_space_def]
 >> ASM_SIMP_TAC std_ss []
 >> CONJ_TAC
 >- (MATCH_MP_TAC (INST_TYPE [“:'b” |-> “:num”] IN_MEASURABLE_BOREL_SUM) \\
     ASM_SIMP_TAC std_ss [space_def] \\
     qexistsl_tac [‘\k x. &k / 2 pow n *
                          indicator_fn {x | x IN m_space m /\ &k / 2 pow n <= f x /\
                                            f x < (&k + 1) / 2 pow n} x’,
                   ‘count (4 ** n)’] \\
     SIMP_TAC std_ss [FINITE_COUNT] \\
     reverse CONJ_TAC
     >- (rpt GEN_TAC >> STRIP_TAC \\
         rename1 ‘&i / 2 pow n * indicator_fn s x’ \\
        ‘?r. indicator_fn s x = Normal r’ by METIS_TAC [indicator_fn_normal] >> POP_ORW \\
        ‘!n. 0:real < 2 pow n’ by RW_TAC real_ss [REAL_POW_LT] \\
        ‘!n. 0:real <> 2 pow n’ by RW_TAC real_ss [REAL_LT_IMP_NE] \\
        ‘!n k. &k / 2 pow n = Normal (&k / 2 pow n)’
            by METIS_TAC [extreal_of_num_def, extreal_pow_def, extreal_div_eq] \\
         rw [extreal_mul_def, extreal_not_infty]) \\
     rpt STRIP_TAC \\
     HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR >> rw []
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST >> rw [] \\
         Q.EXISTS_TAC ‘&i / 2 pow n’ >> rw []) \\
    ‘{x | x IN m_space m /\ &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n} =
     {x | &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n} INTER m_space m’
        by SET_TAC [] >> POP_ORW \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE])
 >> CONJ_TAC
 >- (HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR >> rw []
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST >> rw [] \\
         Q.EXISTS_TAC ‘2 pow n’ >> rw []) \\
    ‘{x | x IN m_space m /\ 2 pow n <= f x} =
     {x | 2 pow n <= f x} INTER m_space m’ by SET_TAC [] >> POP_ORW \\
      METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE])
 >> NTAC 2 STRIP_TAC >> DISJ1_TAC (* easier *)
 >> CONJ_TAC >> MATCH_MP_TAC pos_not_neginf
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> SIMP_TAC std_ss [FINITE_COUNT] \\
      Q.X_GEN_TAC ‘i’ >> STRIP_TAC \\
      MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS] \\
     ‘2 pow n = Normal (2 pow n)’
        by METIS_TAC [extreal_pow_def, extreal_of_num_def] >> POP_ORW \\
      MATCH_MP_TAC le_div \\
      reverse CONJ_TAC >- RW_TAC real_ss [REAL_POW_LT] \\
      rw [extreal_of_num_def, extreal_le_eq],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS] \\
      MATCH_MP_TAC pow_pos_le >> REWRITE_TAC [le_02] ]
QED

Theorem lemma_fn_seq_in_psfis[local] :
    !m f n. (!x. x IN m_space m ==> 0 <= f x) /\ measure_space m /\
            f IN measurable (m_space m,measurable_sets m) Borel ==>
            (fn_seq_integral m f n IN psfis m (fn_seq m f n))
Proof
    RW_TAC std_ss [IN_psfis_eq, pos_simple_fn_def]
 >> qexistsl_tac [`count (4 ** n + 1)`,
                  `(\k. if k IN count (4 ** n) then
                          {x | x IN m_space m /\ &k / 2 pow n <= f x /\
                               f x < (&k + 1) / 2 pow n}
                        else {x | x IN m_space m /\ 2 pow n <= f x})`,
                  `(\k. if k IN count (4 ** n) then &k / 2 pow n else 2 pow n)`]
 >> `FINITE (count (4 ** n)) /\
     FINITE (count (4 ** n + 1))` by RW_TAC std_ss [FINITE_COUNT]
 >> `!n. 0:real < 2 pow n` by RW_TAC real_ss [REAL_POW_LT]
 >> `!n. 0:real <> 2 pow n` by RW_TAC real_ss [REAL_LT_IMP_NE]
 >> `!n k. &k / 2 pow n = Normal (&k / 2 pow n)`
      by METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_div_eq]
 >> `!n z. Normal z / 2 pow n = Normal (z / 2 pow n)`
      by METIS_TAC [extreal_pow_def,extreal_div_eq,extreal_of_num_def]
 >> ‘sigma_algebra (measurable_space m)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
 (* flatten all CONJ *)
 >> ASM_SIMP_TAC std_ss [GSYM CONJ_ASSOC]
 >> CONJ_TAC >- RW_TAC std_ss [lemma_fn_seq_positive]
 >> CONJ_TAC
 >- (RW_TAC real_ss [fn_seq_def, IN_COUNT, GSYM ADD1, COUNT_SUC] \\
        `(\i. Normal (if i < 4 ** n then &i / 2 pow n else 2 pow n) *
              indicator_fn (if i < 4 ** n then
                   {x | x IN m_space m /\ Normal (&i / 2 pow n) <= f x /\
                                     f x < (&i + 1) / 2 pow n}
                   else {x | x IN m_space m /\ 2 pow n <= f x}) t) =
         (\i. if i < 4 ** n then &i / 2 pow n  *
                 indicator_fn {x | x IN m_space m /\ &i / 2 pow n <= f x /\
                                     f x < (&i + 1) / 2 pow n} t
               else 2 pow n * indicator_fn {x | x IN m_space m /\ 2 pow n <= f x} t)`
            by (RW_TAC std_ss [FUN_EQ_THM] \\
                Cases_on `i < 4 ** n` >- RW_TAC std_ss [] \\
                RW_TAC std_ss [extreal_of_num_def, extreal_pow_def]) >> POP_ORW \\
         (MP_TAC o Q.SPEC `4 ** n` o UNDISCH o
          Q.SPECL [`(\i. if i < 4 ** n then &i / 2 pow n * indicator_fn
                           {x | x IN m_space m /\ &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n} t
                         else 2 pow n * indicator_fn {x | x IN m_space m /\ 2 pow n <= f x} t)`,
                   `count (4 ** n)`] o
          INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_PROPERTY \\
         `!x. (\i. if i < 4 ** n then &i / 2 pow n * indicator_fn
                     {x | x IN m_space m /\ &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n} t
                   else 2 pow n * indicator_fn {x | x IN m_space m /\ 2 pow n <= f x} t) x <> NegInf`
             by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,num_not_infty] \\
                 METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_not_infty]) \\
          RW_TAC std_ss [] \\
         `count (4 ** n) DELETE 4 ** n = count (4 ** n)`
             by METIS_TAC [DELETE_NON_ELEMENT,IN_COUNT,LESS_EQ_REFL,NOT_LESS] \\
          RW_TAC std_ss [] \\
          Q.PAT_X_ASSUM `SIGMA _ _ = _` (K ALL_TAC) \\
          FULL_SIMP_TAC std_ss [GSYM IN_COUNT] \\
         `!i. Normal (&i / 2 pow n) = &i / 2 pow n` by METIS_TAC [] \\
          POP_ORW \\
          Q.PAT_X_ASSUM `!n k. &k / 2 pow n = Normal (&k / 2 pow n)` (K ALL_TAC) \\
         `!i. (\i. &i / 2 pow n * indicator_fn
                   {x | x IN m_space m /\ &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n} t) i <> NegInf`
             by (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,num_not_infty] \\
                 METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_not_infty]) \\
          (MP_TAC o Q.SPECL [`count (4 ** n)`,
                             `(\k. &k / 2 pow n * indicator_fn
                                 {x | x IN m_space m /\ &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n} t)`,
                             `2 pow n * indicator_fn {x | x IN m_space m /\ 2 pow n <= f x} t`] o
           INST_TYPE [alpha |-> ``:num``] o GSYM) EXTREAL_SUM_IMAGE_IN_IF_ALT \\
          RW_TAC std_ss [] \\
          MATCH_MP_TAC add_comm \\
          DISJ1_TAC \\
          reverse CONJ_TAC
          >- (RW_TAC std_ss [indicator_fn_def,mul_rone,mul_rzero,num_not_infty] \\
              METIS_TAC [extreal_of_num_def,extreal_pow_def,extreal_not_infty]) \\
          FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY])
 >> CONJ_TAC
 >- (RW_TAC real_ss []
         >- (`{x | x IN m_space m /\ Normal (&i / 2 pow n) <= f x /\ f x < (&i + 1) / 2 pow n} =
              {x | Normal (&i / 2 pow n) <= f x /\ f x < Normal (&(i + 1) / 2 pow n)} INTER m_space m`
                 by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER,CONJ_COMM] \\
                    `(&i + 1:extreal) = &(i + 1)`
                       by RW_TAC std_ss [extreal_add_def,extreal_of_num_def,REAL_ADD] \\
                     METIS_TAC []) >> POP_ORW \\
             METIS_TAC [IN_MEASURABLE_BOREL_ALL, m_space_def, measurable_sets_def,
                        space_def, subsets_def]) \\
        `{x | x IN m_space m /\ 2 pow n <= f x} = {x | Normal (2 pow n) <= f x} INTER m_space m`
            by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, CONJ_COMM,
                              extreal_of_num_def, extreal_pow_def] >> POP_ORW \\
         METIS_TAC [IN_MEASURABLE_BOREL_ALL, m_space_def, measurable_sets_def,
                    space_def, subsets_def])
 >> CONJ_TAC
 >- RW_TAC real_ss [extreal_of_num_def,extreal_pow_def,extreal_le_def,
                    REAL_LT_IMP_LE,POW_POS,REAL_LE_DIV]
 >> CONJ_TAC
 >- (RW_TAC real_ss [DISJOINT_DEF,IN_COUNT,IN_INTER,EXTENSION,GSPECIFICATION] >|
         [ reverse EQ_TAC >- RW_TAC std_ss [NOT_IN_EMPTY] \\
           RW_TAC real_ss [] \\
           RW_TAC std_ss [NOT_IN_EMPTY] \\
           Cases_on `i < j`
           >- (`i + 1 <= j` by RW_TAC real_ss []
                 >> `&(i + 1) / 2:real pow n <= &j / 2 pow n`
                       by RW_TAC real_ss [REAL_LE_RDIV_EQ,REAL_POW_LT,REAL_DIV_RMUL,REAL_POS_NZ]
                 >> `&(i + 1) / 2 pow n <= &j / 2 pow n`
                       by RW_TAC std_ss [extreal_of_num_def,extreal_add_def,extreal_pow_def,
                                         extreal_div_eq,extreal_lt_eq,extreal_le_def]
                 >> `&j / 2 pow n <= f x` by METIS_TAC []
                 >> `(&i + 1) = &(i + 1)` by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
                 >> METIS_TAC [lte_trans,extreal_lt_def])
             >> `j < i` by RW_TAC real_ss [LESS_OR_EQ]
             >> `j + 1 <= i` by RW_TAC real_ss []
             >> `&(j + 1) / 2 pow n <= &i / 2:real pow n` by RW_TAC real_ss [REAL_LE_RDIV_EQ,REAL_POW_LT,REAL_DIV_RMUL,REAL_POS_NZ]
             >> `&(j + 1) / 2 pow n <= &i / 2 pow n` by RW_TAC std_ss [extreal_of_num_def,extreal_add_def,extreal_pow_def,extreal_div_eq,extreal_lt_eq,extreal_le_def]
             >> `(&j + 1) = &(j + 1)` by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
             >> METIS_TAC [lte_trans,extreal_lt_def],

             reverse EQ_TAC >- RW_TAC std_ss [NOT_IN_EMPTY]
             >> RW_TAC std_ss []
             >> RW_TAC real_ss [NOT_IN_EMPTY]
             >> `&(i + 1) <= &(4 ** n):real` by RW_TAC real_ss []
             >> FULL_SIMP_TAC std_ss [GSYM REAL_OF_NUM_POW]
              >> `&(i + 1) / 2 pow n <= 4 pow n / 2:real pow n` by RW_TAC real_ss [REAL_LE_RDIV_EQ,REAL_POW_LT,REAL_DIV_RMUL,REAL_POS_NZ]
              >> `&(i + 1) / 2 pow n <= 2:real pow n` by METIS_TAC [REAL_POW_DIV,EVAL ``4/2:real``]
              >> `&(i + 1) / 2 pow n <= 2 pow n` by RW_TAC std_ss [extreal_of_num_def,extreal_add_def,extreal_pow_def,extreal_div_eq,extreal_lt_eq,extreal_le_def]
             >> `(&i + 1) = &(i + 1)` by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
             >> METIS_TAC [le_trans,extreal_lt_def],

             reverse EQ_TAC >- RW_TAC std_ss [NOT_IN_EMPTY]
             >> RW_TAC real_ss []
             >> RW_TAC std_ss [NOT_IN_EMPTY]
             >> `&(j + 1) <= &(4 ** n):real` by RW_TAC real_ss []
             >> FULL_SIMP_TAC std_ss [GSYM REAL_OF_NUM_POW]
              >> `&(j + 1) / 2 pow n <= 4:real pow n / 2 pow n` by RW_TAC real_ss [REAL_LE_RDIV_EQ,REAL_POW_LT,REAL_DIV_RMUL,REAL_POS_NZ]
              >> `&(j + 1) / 2 pow n <= 2:real pow n` by  METIS_TAC [REAL_POW_DIV,EVAL ``4/2:real``]
              >> `&(j + 1) / 2 pow n <= 2 pow n` by RW_TAC std_ss [extreal_of_num_def,extreal_add_def,extreal_pow_def,extreal_div_eq,extreal_lt_eq,extreal_le_def]
             >> `(&j + 1) = &(j + 1)` by METIS_TAC [extreal_of_num_def,extreal_add_def,REAL_ADD]
             >> METIS_TAC [lte_trans,extreal_lt_def]])
 (* BIGUNION (IMAGE ... = m_space m *)
 >> CONJ_TAC
 >- (RW_TAC std_ss [EXTENSION,IN_BIGUNION_IMAGE,GSPECIFICATION] \\
     EQ_TAC
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
 (* fn_seq_integral m f n = pos_simple_fn_integral m (count (4 ** n + 1)) _ _ *)
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
  >> (MP_TAC o Q.SPEC `4 ** n` o UNDISCH o Q.SPECL
      [`(\i. if i < 4 ** n then
                &i / 2 pow n *
                measure m {x | x IN m_space m /\ &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n}
             else
                2 pow n * measure m {x | x IN m_space m /\ 2 pow n <= f x})`,`count (4 ** n)`]
      o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_PROPERTY
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
  >> Q.PAT_X_ASSUM `SIGMA _ _ = _` (K ALL_TAC)
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
  >> reverse CONJ_TAC
  >- (RW_TAC std_ss [extreal_of_num_def,extreal_pow_def]
      >> `0:real <= 2 pow n` by FULL_SIMP_TAC std_ss [REAL_LT_IMP_LE]
      >> Suff `{x | x IN m_space m /\ Normal (2 pow n) <= f x} IN measurable_sets m`
      >- METIS_TAC [mul_not_infty,positive_not_infty,MEASURE_SPACE_POSITIVE]
      >> `{x | x IN m_space m /\ Normal (2 pow n) <= f x} = {x | Normal (2 pow n) <= f x} INTER m_space m`
            by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER] >> METIS_TAC [])
      >> METIS_TAC [IN_MEASURABLE_BOREL_ALL, measurable_sets_def,subsets_def,space_def,m_space_def])
  >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY]
QED

(* This huge theorem (from HVG Concordia) cannot be put into borelTheory as it
   depends on several lemmas here.
 *)
Theorem BOREL_INDUCT : (* was: Induct_on_Borel_functions *)
  !f m P.
     measure_space m /\
     f IN measurable (m_space m, measurable_sets m) Borel /\ (!x. 0 <= f x) /\
     (!f g. f IN measurable (m_space m, measurable_sets m) Borel /\
            g IN measurable (m_space m, measurable_sets m) Borel /\
            (!x. x IN m_space m ==> (f x = g x)) /\ P f ==> P g) /\
     (!A. A IN measurable_sets m ==> P (indicator_fn A)) /\
     (!f c. f IN measurable (m_space m, measurable_sets m) Borel /\
            0 <= c /\ (!x. 0 <= f x) /\ P f ==> P (\x. c * f x)) /\
     (!f g. f IN measurable (m_space m, measurable_sets m) Borel /\
            g IN measurable (m_space m, measurable_sets m) Borel /\
            (!x. 0 <= f x) /\ P f /\ (!x. 0 <= g x) /\ P g ==>
            P (\x. f x + g x)) /\
     (!u. (!i:num. (u i) IN measurable (m_space m, measurable_sets m) Borel) /\
          (!i x. 0 <= u i x) /\ (!x. mono_increasing (\i. u i x)) /\
          (!i. P (u i)) ==> P (\x. sup (IMAGE (\i. u i x) UNIV))) ==> P f
Proof
    RW_TAC std_ss []
 >> ‘sigma_algebra (measurable_space m)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
 >> FIRST_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC `(\x. sup (IMAGE (\i. fn_seq m f i x) univ(:num)))`
 >> ASM_SIMP_TAC std_ss [lemma_fn_seq_sup]
 THEN
  Know `!i. (\x. SIGMA
          (\k. &k / 2 pow i *
             indicator_fn {x |
                x IN m_space m /\ &k / 2 pow i <= f x /\
                f x < (&k + 1) / 2 pow i} x) (count (4 ** i)))
          IN measurable (m_space m, measurable_sets m) Borel` THEN1
  (Q.X_GEN_TAC `i` THEN
   Q.ABBREV_TAC `s = count (4 ** i)` THEN
   Q.ABBREV_TAC `g = (\k x. &k / 2 pow i *
        indicator_fn
          {x |
           x IN m_space m /\ &k / 2 pow i <= f x /\
           f x < (&k + 1) / 2 pow i} x)` THEN

   Suff `FINITE s /\ sigma_algebra (m_space m, measurable_sets m) /\
     (!i. i IN s ==> g i IN measurable (m_space m, measurable_sets m) Borel) /\
     (!i x. i IN s /\ x IN space (m_space m, measurable_sets m) ==> g i x <> NegInf) /\
     (!x. x IN space (m_space m, measurable_sets m) ==>
      ((\x. SIGMA
     (\k. &k / 2 pow i *
        indicator_fn {x |
           x IN m_space m /\ &k / 2 pow i <= f x /\
           f x < (&k + 1) / 2 pow i} x) s) x = SIGMA (\i. g i x) s))` THEN1
   (DISCH_THEN (MP_TAC o MATCH_MP IN_MEASURABLE_BOREL_SUM) THEN
    SIMP_TAC std_ss []) THEN

   Q.UNABBREV_TAC `s` THEN Q.UNABBREV_TAC `g` THEN
   FULL_SIMP_TAC std_ss [measure_space_def, FINITE_COUNT] THEN
   SIMP_TAC std_ss [space_def, IN_UNIV] THEN

  `2 pow i <> NegInf /\ 2 pow i <> PosInf`
      by METIS_TAC [pow_not_infty, num_not_infty] THEN
   Know `real (2 pow i) <> 0`
   >- (ASM_SIMP_TAC std_ss [GSYM extreal_11, normal_real,
                            GSYM extreal_of_num_def] THEN
       Suff `(0 :extreal) < 2 pow i` >- METIS_TAC [lt_imp_ne] THEN
       METIS_TAC [lt_02, pow_pos_lt]) >> DISCH_TAC THEN

   reverse CONJ_TAC THEN1
   (Q.X_GEN_TAC `n` THEN
    RW_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
    Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
    MATCH_MP_TAC le_mul THEN REWRITE_TAC [INDICATOR_FN_POS] THEN
    `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    ASM_SIMP_TAC std_ss [extreal_div_def] THEN
    MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [le_num] THEN
    ASM_SIMP_TAC real_ss [extreal_inv_def] THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
    SIMP_TAC std_ss [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
    ASM_SIMP_TAC std_ss [normal_real, GSYM extreal_of_num_def] THEN
    METIS_TAC [le_02, pow_pos_le]) THEN

   Q.X_GEN_TAC `n` THEN
   RW_TAC std_ss [] THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL THEN
   qexistsl_tac
        [`(\x. indicator_fn
               {x | x IN m_space m /\ &n / 2 pow i <= f x /\ f x < (&n + 1) / 2 pow i} x)`,
         `real (&n / 2 pow i)`] THEN

   Know `&n / 2 pow i <> NegInf /\ &n / 2 pow i <> PosInf` THEN1
   (`2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    `&n = Normal (&n)` by PROVE_TAC [extreal_of_num_def] >> POP_ORW \\
    ASM_SIMP_TAC std_ss [extreal_div_eq, extreal_not_infty]) >> STRIP_TAC THEN

   ASM_SIMP_TAC std_ss [normal_real] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
   Q.EXISTS_TAC `{x | x IN m_space m /\ &n / 2 pow i <= f x /\ f x < (&n + 1) / 2 pow i}` THEN
   ASM_SIMP_TAC std_ss [] THEN
   Q_TAC SUFF_TAC
   `{x | x IN m_space m /\ &n / 2 pow i <= f x /\ f x < (&n + 1) / 2 pow i} =
    PREIMAGE f {x | &n / 2 pow i <= x /\ x < (&n + 1) / 2 pow i} INTER
    space (m_space m, measurable_sets m)` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [PREIMAGE_def, space_def, INTER_UNIV] THEN
    SET_TAC []] THEN
   FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN

   Suff `(&n + 1) / 2 pow i <> NegInf /\ (&n + 1) / 2 pow i <> PosInf`
   >- (STRIP_TAC THEN METIS_TAC [BOREL_MEASURABLE_SETS_CO, normal_real]) THEN

   `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    Know `&n + 1 = Normal (&n + 1)`
    >- (REWRITE_TAC [extreal_of_num_def, extreal_add_def]) >> Rewr' THEN
    ASM_SIMP_TAC std_ss [extreal_div_eq, extreal_not_infty]
  ) THEN DISCH_TAC THEN

  Know `!i. (\x. 2 pow i * indicator_fn {x | x IN m_space m /\ 2 pow i <= f x} x)
            IN measurable (m_space m, measurable_sets m) Borel` THEN1
  (GEN_TAC THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL THEN
   `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
    METIS_TAC [pow_not_infty, num_not_infty] THEN
   Q.EXISTS_TAC `(\x. indicator_fn {x | x IN m_space m /\ 2 pow i <= f x} x)` THEN
   Q.EXISTS_TAC `real (2 pow i)` THEN ASM_SIMP_TAC std_ss [normal_real] THEN
   FULL_SIMP_TAC std_ss [measure_space_def] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
   Q.EXISTS_TAC `{x | x IN m_space m /\ 2 pow i <= f x}` THEN
   ASM_SIMP_TAC std_ss [space_def, IN_UNIV] THEN
   Q_TAC SUFF_TAC `{x | x IN m_space m /\ 2 pow i <= f x} =
    PREIMAGE f {x | 2 pow i <= x} INTER space (m_space m,measurable_sets m)` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [PREIMAGE_def, space_def, INTER_UNIV] THEN
    SET_TAC []] THEN
   FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC [BOREL_MEASURABLE_SETS_CR, normal_real]
   ) THEN DISCH_TAC THEN

  Know `!i. fn_seq m f i IN measurable (m_space m,measurable_sets m) Borel` THEN1
  (SIMP_TAC std_ss [fn_seq_def] THEN GEN_TAC THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD THEN
   qexistsl_tac
        [`(\x. SIGMA
          (\k. &k / 2 pow i *
             indicator_fn {x |
                x IN m_space m /\ &k / 2 pow i <= f x /\
                f x < (&k + 1) / 2 pow i} x) (count (4 ** i)))`,
         `(\x. 2 pow i * indicator_fn {x | x IN m_space m /\ 2 pow i <= f x} x)`] THEN
   POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN FULL_SIMP_TAC std_ss [measure_space_def] THEN

   `2 pow i <> NegInf /\ 2 pow i <> PosInf`
      by METIS_TAC [pow_not_infty, num_not_infty] THEN
    Know `real (2 pow i) <> 0`
    >- (ASM_SIMP_TAC std_ss [GSYM extreal_11, normal_real,
                             GSYM extreal_of_num_def] THEN
        Suff `(0 :extreal) < 2 pow i` >- METIS_TAC [lt_imp_ne] THEN
        METIS_TAC [lt_02, pow_pos_lt]) >> DISCH_TAC THEN

   RW_TAC std_ss [] \\
   DISJ1_TAC \\
   reverse CONJ_TAC
   >- (MATCH_MP_TAC pos_not_neginf \\
       MATCH_MP_TAC le_mul >> rw [pow_pos_le, INDICATOR_FN_POS]) \\
   SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
   Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
   MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS THEN REWRITE_TAC [FINITE_COUNT] THEN
   Q.X_GEN_TAC `n` THEN RW_TAC std_ss [IN_UNIV] THEN
   MATCH_MP_TAC le_mul THEN REWRITE_TAC [INDICATOR_FN_POS] THEN
   `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
   POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
   ASM_SIMP_TAC std_ss [extreal_div_def] THEN
   MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [le_num] THEN
   ASM_SIMP_TAC real_ss [extreal_inv_def] THEN
   SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
   SIMP_TAC std_ss [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
   ASM_SIMP_TAC std_ss [normal_real, GSYM extreal_of_num_def] THEN
   METIS_TAC [le_02, pow_pos_le]) THEN DISCH_TAC THEN

  CONJ_TAC THENL
  [MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP THEN
   Q.EXISTS_TAC `fn_seq m f` THEN SIMP_TAC std_ss [] THEN
   CONJ_TAC THENL
   [METIS_TAC [measure_space_def], ALL_TAC] THEN
   CONJ_TAC THENL
   [ALL_TAC,
    GEN_TAC THEN GEN_TAC THEN
    `mono_increasing (\n. fn_seq m f n x)` by METIS_TAC [lemma_fn_seq_mono_increasing] THEN
    FULL_SIMP_TAC std_ss [ext_mono_increasing_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC] THEN ASM_SIMP_TAC std_ss [],
   ALL_TAC] THEN

  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC std_ss [lemma_fn_seq_mono_increasing, lemma_fn_seq_positive] THEN

  GEN_TAC THEN SIMP_TAC std_ss [fn_seq_def] THEN
  Suff `P (\x.
    (\x. SIGMA
      (\k. &k / 2 pow i *
         indicator_fn {x |
            x IN m_space m /\ &k / 2 pow i <= f x /\
            f x < (&k + 1) / 2 pow i} x) (count (4 ** i))) x +
    (\x. 2 pow i * indicator_fn {x | x IN m_space m /\ 2 pow i <= f x} x) x)`
  >- (SIMP_TAC std_ss []) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [IN_UNIV] THEN
  CONJ_TAC >-
  (GEN_TAC THEN
   MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS THEN REWRITE_TAC [FINITE_COUNT] THEN
   Q.X_GEN_TAC `n` THEN RW_TAC std_ss [IN_COUNT] THEN
   MATCH_MP_TAC le_mul THEN REWRITE_TAC [INDICATOR_FN_POS] THEN

   `2 pow i <> NegInf /\ 2 pow i <> PosInf`
      by METIS_TAC [pow_not_infty, num_not_infty] THEN
    Know `real (2 pow i) <> 0`
    >- (ASM_SIMP_TAC std_ss [GSYM extreal_11, normal_real,
                             GSYM extreal_of_num_def] THEN
        Suff `(0 :extreal) < 2 pow i` >- METIS_TAC [lt_imp_ne] THEN
        METIS_TAC [lt_02, pow_pos_lt]) >> DISCH_TAC THEN

   `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    ASM_SIMP_TAC std_ss [extreal_div_def] THEN
    MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [le_num] THEN
    ASM_SIMP_TAC real_ss [extreal_inv_def] THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
    SIMP_TAC std_ss [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
    ASM_SIMP_TAC std_ss [normal_real, GSYM extreal_of_num_def] THEN
    METIS_TAC [le_02, pow_pos_le]) THEN

  CONJ_TAC THEN1
  (`FINITE (count (4 ** i))` by SIMP_TAC std_ss [FINITE_COUNT] THEN
   Suff `(\s. P
    (\x. SIGMA
       (\k. &k / 2 pow i *
          indicator_fn {x | x IN m_space m /\ &k / 2 pow i <= f x /\ f x < (&k + 1) / 2 pow i} x) (s)))
         (count (4 ** i))`
   >- (SIMP_TAC std_ss []) THEN
   POP_ASSUM MP_TAC THEN
   Q.ABBREV_TAC `s = count (4 ** i)` THEN Q.SPEC_TAC (`s`,`s`) THEN
   MATCH_MP_TAC FINITE_INDUCT THEN
   Q.UNABBREV_TAC `s` THEN SIMP_TAC std_ss [FINITE_COUNT] THEN
   SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY] THEN
   CONJ_TAC THEN1
   (FIRST_ASSUM MATCH_MP_TAC THEN Q.EXISTS_TAC `indicator_fn {}` THEN
    RW_TAC std_ss [] THENL
    [MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN Q.EXISTS_TAC `{}` THEN
     FULL_SIMP_TAC std_ss [measure_space_def] THEN METIS_TAC [SIGMA_ALGEBRA],
     MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN Q.EXISTS_TAC `0` THEN
     FULL_SIMP_TAC std_ss [measure_space_def],
     SIMP_TAC std_ss [indicator_fn_def, NOT_IN_EMPTY],
     ALL_TAC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    FULL_SIMP_TAC std_ss [measure_space_def, SIGMA_ALGEBRA, subsets_def]) THEN
   RW_TAC std_ss [] THEN
   Know `!x.
     SIGMA
       (\k.
          &k / 2 pow i *
          indicator_fn
            {x | x IN m_space m /\ &k / 2 pow i <= f x /\ f x < (&k + 1) / 2 pow i} x)
       (e INSERT s) =
      (\k. &k / 2 pow i *
      indicator_fn {x | x IN m_space m /\ &k / 2 pow i <= f x /\ f x < (&k + 1) / 2 pow i} x) e +
      SIGMA
       (\k.
          &k / 2 pow i *
          indicator_fn
            {x | x IN m_space m /\ &k / 2 pow i <= f x /\ f x < (&k + 1) / 2 pow i} x)
       (s DELETE e)` THEN1
   (GEN_TAC THEN FIRST_ASSUM (MP_TAC o MATCH_MP EXTREAL_SUM_IMAGE_PROPERTY) THEN
    DISCH_THEN MATCH_MP_TAC THEN DISJ1_TAC THEN
    Q.X_GEN_TAC `n` THEN DISCH_TAC THEN
    SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
    Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
    MATCH_MP_TAC le_mul THEN REWRITE_TAC [INDICATOR_FN_POS] THEN

   `2 pow i <> NegInf /\ 2 pow i <> PosInf`
       by METIS_TAC [pow_not_infty, num_not_infty] THEN
    Know `real (2 pow i) <> 0`
    >- (ASM_SIMP_TAC std_ss [GSYM extreal_11, normal_real,
                             GSYM extreal_of_num_def] THEN
        Suff `(0 :extreal) < 2 pow i` >- METIS_TAC [lt_imp_ne] THEN
        METIS_TAC [lt_02, pow_pos_lt]) >> DISCH_TAC THEN

   `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    ASM_SIMP_TAC std_ss [extreal_div_def] THEN
    MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [le_num] THEN
    ASM_SIMP_TAC real_ss [extreal_inv_def] THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
    SIMP_TAC std_ss [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
    ASM_SIMP_TAC std_ss [normal_real, GSYM extreal_of_num_def] THEN
    METIS_TAC [le_02, pow_pos_le]) THEN DISC_RW_KILL THEN
   ASM_SIMP_TAC std_ss [SET_RULE ``e NOTIN s ==> (s DELETE e = s)``] THEN
   Suff `P (\x.
     (\x. &e / 2 pow i *
     indicator_fn {x | x IN m_space m /\ &e / 2 pow i <= f x /\ f x < (&e + 1) / 2 pow i}
       x) x +
     (\x. SIGMA
       (\k. &k / 2 pow i *
     indicator_fn {x | x IN m_space m /\ &k / 2 pow i <= f x /\ f x < (&k + 1) / 2 pow i} x) s) x)`
   >- (SIMP_TAC std_ss []) THEN
   FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [] THEN

   CONJ_TAC THEN1
   (MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL THEN
    Know `&e / 2 pow i <> NegInf /\ &e / 2 pow i <> PosInf` THEN1
    (`2 pow i <> NegInf /\ 2 pow i <> PosInf` by
     METIS_TAC [pow_not_infty, num_not_infty] THEN
     `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
     POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
     Know `real (2 pow i) <> 0`
     >- (ASM_SIMP_TAC std_ss [GSYM extreal_11, normal_real,
                              GSYM extreal_of_num_def] THEN
         Suff `(0 :extreal) < 2 pow i` >- METIS_TAC [lt_imp_ne] THEN
         METIS_TAC [lt_02, pow_pos_lt]) >> DISCH_TAC THEN
     `&e = Normal (&e)` by PROVE_TAC [extreal_of_num_def] >> POP_ORW \\
     ASM_SIMP_TAC std_ss [extreal_div_eq, extreal_not_infty]) THEN STRIP_TAC THEN

    qexistsl_tac
         [`(\x. indicator_fn
           {x | x IN m_space m /\ &e / 2 pow i <= f x /\ f x < (&e + 1) / 2 pow i} x)`,
          `real (&e / 2 pow i)`] THEN ASM_SIMP_TAC std_ss [normal_real] THEN
    FULL_SIMP_TAC std_ss [measure_space_def] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
    Q.EXISTS_TAC `{x | x IN m_space m /\ &e / 2 pow i <= f x /\ f x < (&e + 1) / 2 pow i}` THEN
    ASM_SIMP_TAC std_ss [space_def, IN_UNIV] THEN
    Q_TAC SUFF_TAC `{x | x IN m_space m /\ &e / 2 pow i <= f x /\ f x < (&e + 1) / 2 pow i} =
     PREIMAGE f {x | &e / 2 pow i <= x /\ x < (&e + 1) / 2 pow i} INTER
     space (m_space m, measurable_sets m)` THENL
    [DISC_RW_KILL,
     SIMP_TAC std_ss [PREIMAGE_def, space_def, INTER_UNIV] THEN
     SET_TAC []] THEN
    FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [BOREL_MEASURABLE_SETS_CO]) THEN

   CONJ_TAC THEN1
   (Q.ABBREV_TAC `g = (\k x.
             &k / 2 pow i *
             indicator_fn
               {x | x IN m_space m /\ &k / 2 pow i <= f x /\ f x < (&k + 1) / 2 pow i} x)` THEN

    Suff `FINITE s /\ sigma_algebra (m_space m, measurable_sets m) /\
     (!i. i IN s ==> g i IN measurable (m_space m, measurable_sets m) Borel) /\
     (!i x. i IN s /\ x IN space (m_space m, measurable_sets m) ==> g i x <> NegInf) /\
     (!x. x IN space (m_space m, measurable_sets m) ==>
      ((\x. SIGMA
     (\k.
        &k / 2 pow i *
        indicator_fn
          {x | x IN m_space m /\ &k / 2 pow i <= f x /\ f x < (&k + 1) / 2 pow i} x) s) x =
      SIGMA (\i. g i x) s))`
    >- (DISCH_THEN (MP_TAC o MATCH_MP IN_MEASURABLE_BOREL_SUM) THEN
        ASM_SIMP_TAC std_ss []) THEN
   Q.UNABBREV_TAC `g` THEN
   FULL_SIMP_TAC std_ss [measure_space_def, FINITE_COUNT] THEN
   SIMP_TAC std_ss [space_def, IN_UNIV] THEN
   reverse CONJ_TAC THEN1
   (Q.X_GEN_TAC `n` THEN
    RW_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
    Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
    MATCH_MP_TAC le_mul THEN REWRITE_TAC [INDICATOR_FN_POS] THEN

   `2 pow i <> NegInf /\ 2 pow i <> PosInf`
       by METIS_TAC [pow_not_infty, num_not_infty] THEN
    Know `real (2 pow i) <> 0`
    >- (ASM_SIMP_TAC std_ss [GSYM extreal_11, normal_real,
                             GSYM extreal_of_num_def] THEN
        Suff `(0 :extreal) < 2 pow i` >- METIS_TAC [lt_imp_ne] THEN
        METIS_TAC [lt_02, pow_pos_lt]) >> DISCH_TAC THEN

   `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    ASM_SIMP_TAC std_ss [extreal_div_def] THEN
    MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [le_num] THEN
    ASM_SIMP_TAC real_ss [extreal_inv_def] THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
    SIMP_TAC std_ss [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
    ASM_SIMP_TAC std_ss [normal_real, GSYM extreal_of_num_def] THEN
    METIS_TAC [le_02, pow_pos_le]) THEN
   Q.X_GEN_TAC `n` THEN
   RW_TAC std_ss [] THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL THEN
   qexistsl_tac
        [`(\x. indicator_fn
          {x | x IN m_space m /\ &n / 2 pow i <= f x /\ f x < (&n + 1) / 2 pow i} x)`,
         `real (&n / 2 pow i)`] THEN

   Know `&n / 2 pow i <> NegInf /\ &n / 2 pow i <> PosInf` THEN1
   ( `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
     METIS_TAC [pow_not_infty, num_not_infty] THEN
     `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
     POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
     Know `real (2 pow i) <> 0`
     >- (ASM_SIMP_TAC std_ss [GSYM extreal_11, normal_real,
                              GSYM extreal_of_num_def] THEN
         Suff `(0 :extreal) < 2 pow i` >- METIS_TAC [lt_imp_ne] THEN
         METIS_TAC [lt_02, pow_pos_lt]) >> DISCH_TAC THEN
     `&n = Normal (&n)` by PROVE_TAC [extreal_of_num_def] >> POP_ORW \\
     ASM_SIMP_TAC std_ss [extreal_div_eq, extreal_not_infty] ) THEN STRIP_TAC THEN

   ASM_SIMP_TAC std_ss [normal_real] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
   Q.EXISTS_TAC `{x | x IN m_space m /\ &n / 2 pow i <= f x /\ f x < (&n + 1) / 2 pow i}` THEN
   ASM_SIMP_TAC std_ss [] THEN
   Know
   `{x | x IN m_space m /\ &n / 2 pow i <= f x /\ f x < (&n + 1) / 2 pow i} =
    PREIMAGE f {x | &n / 2 pow i <= x /\ x < (&n + 1) / 2 pow i} INTER
    space (m_space m,measurable_sets m)`
   >- (SIMP_TAC std_ss [PREIMAGE_def, space_def, INTER_UNIV] THEN
       SET_TAC []) THEN DISC_RW_KILL THEN

   FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   REWRITE_TAC [BOREL_MEASURABLE_SETS_CO] ) THEN

   CONJ_TAC THEN1
   (Q.X_GEN_TAC `x` THEN
    MATCH_MP_TAC le_mul THEN REWRITE_TAC [INDICATOR_FN_POS] THEN

   `2 pow i <> NegInf /\ 2 pow i <> PosInf`
       by METIS_TAC [pow_not_infty, num_not_infty] THEN
    Know `real (2 pow i) <> 0`
    >- (ASM_SIMP_TAC std_ss [GSYM extreal_11, normal_real,
                             GSYM extreal_of_num_def] THEN
        Suff `(0 :extreal) < 2 pow i` >- METIS_TAC [lt_imp_ne] THEN
        METIS_TAC [lt_02, pow_pos_lt]) >> DISCH_TAC THEN

   `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    ASM_SIMP_TAC std_ss [extreal_div_def] THEN
    MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [le_num] THEN
    ASM_SIMP_TAC real_ss [extreal_inv_def] THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
    SIMP_TAC std_ss [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
    ASM_SIMP_TAC std_ss [normal_real, GSYM extreal_of_num_def] THEN
    METIS_TAC [le_02, pow_pos_le] ) THEN

   reverse CONJ_TAC THEN1
   (Q.X_GEN_TAC `x` THEN
    MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS THEN ASM_REWRITE_TAC [] THEN
    Q.X_GEN_TAC `n` >> RW_TAC std_ss [FINITE_COUNT, IN_UNIV] THEN
    MATCH_MP_TAC le_mul THEN REWRITE_TAC [INDICATOR_FN_POS] THEN

   `2 pow i <> NegInf /\ 2 pow i <> PosInf`
       by METIS_TAC [pow_not_infty, num_not_infty] THEN
    Know `real (2 pow i) <> 0`
    >- (ASM_SIMP_TAC std_ss [GSYM extreal_11, normal_real,
                             GSYM extreal_of_num_def] THEN
        Suff `(0 :extreal) < 2 pow i` >- METIS_TAC [lt_imp_ne] THEN
        METIS_TAC [lt_02, pow_pos_lt]) >> DISCH_TAC THEN

   `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    ASM_SIMP_TAC std_ss [extreal_div_def] THEN
    MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [le_num] THEN
    ASM_SIMP_TAC real_ss [extreal_inv_def] THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
    SIMP_TAC std_ss [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
    ASM_SIMP_TAC std_ss [normal_real, GSYM extreal_of_num_def] THEN
    METIS_TAC [le_02, pow_pos_le] ) THEN

   Suff `P (\x. &e / 2 pow i *
     (\x. indicator_fn {x | x IN m_space m /\ &e / 2 pow i <= f x /\ f x < (&e + 1) / 2 pow i}
       x) x)`
   >- (SIMP_TAC std_ss []) THEN
   FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [] THEN

   CONJ_TAC THEN1
   (MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
    Q.EXISTS_TAC `{x | x IN m_space m /\ &e / 2 pow i <= f x /\ f x < (&e + 1) / 2 pow i}` THEN
    ASM_SIMP_TAC std_ss [space_def, IN_UNIV] THEN
    Know `{x | x IN m_space m /\ &e / 2 pow i <= f x /\ f x < (&e + 1) / 2 pow i} =
     PREIMAGE f {x | &e / 2 pow i <= x /\ x < (&e + 1) / 2 pow i} INTER
     space (m_space m,measurable_sets m)`
    >- (SIMP_TAC std_ss [PREIMAGE_def, space_def, INTER_UNIV] THEN
        SET_TAC []) THEN DISC_RW_KILL THEN

    FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [BOREL_MEASURABLE_SETS_CO] ) THEN

   CONJ_TAC THEN1
   (`2 pow i <> NegInf /\ 2 pow i <> PosInf`
      by METIS_TAC [pow_not_infty, num_not_infty] THEN
    Know `real (2 pow i) <> 0`
    >- (ASM_SIMP_TAC std_ss [GSYM extreal_11, normal_real,
                             GSYM extreal_of_num_def] THEN
        Suff `(0 :extreal) < 2 pow i` >- METIS_TAC [lt_imp_ne] THEN
        METIS_TAC [lt_02, pow_pos_lt]) >> DISCH_TAC THEN

   `2 pow i = Normal (real (2 pow i))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    ASM_SIMP_TAC std_ss [extreal_div_def] THEN
    MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [le_num] THEN
    ASM_SIMP_TAC real_ss [extreal_inv_def] THEN
    SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
    SIMP_TAC std_ss [REAL_LE_INV_EQ] THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
    ASM_SIMP_TAC std_ss [normal_real, GSYM extreal_of_num_def] THEN
    METIS_TAC [le_02, pow_pos_le] ) THEN

   CONJ_TAC THENL
   [GEN_TAC THEN SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
    SIMP_TAC real_ss [le_refl, extreal_le_def, extreal_of_num_def],
    ALL_TAC] THEN
   Q_TAC SUFF_TAC `P
     (indicator_fn {x | x IN m_space m /\ &e / 2 pow i <= f x /\ f x < (&e + 1) / 2 pow i})` THENL
   [METIS_TAC [ETA_AX], ALL_TAC] THEN
   FIRST_ASSUM MATCH_MP_TAC THEN

   ONCE_REWRITE_TAC [METIS [subsets_def]
    ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
    Know `{x | x IN m_space m /\ &e / 2 pow i <= f x /\ f x < (&e + 1) / 2 pow i} =
     PREIMAGE f {x | &e / 2 pow i <= x /\ x < (&e + 1) / 2 pow i} INTER
     space (m_space m,measurable_sets m)`
    >- (SIMP_TAC std_ss [PREIMAGE_def, space_def, INTER_UNIV] THEN
        SET_TAC []) THEN DISC_RW_KILL THEN
    FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [BOREL_MEASURABLE_SETS_CO] ) THEN

  CONJ_TAC THEN1
  (GEN_TAC THEN MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [indicator_fn_def] THEN
   CONJ_TAC THENL
   [ALL_TAC, COND_CASES_TAC THEN
    SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]] THEN
   SIMP_TAC std_ss [extreal_of_num_def, extreal_pow_def, extreal_le_def] THEN
   MATCH_MP_TAC POW_POS THEN SIMP_TAC real_ss [] ) THEN

  Suff `P (\x. 2 pow i *
     (\x. indicator_fn {x |  x IN m_space m /\ 2 pow i <= f x} x) x)`
  >- (SIMP_TAC std_ss []) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [] THEN

  CONJ_TAC THENL
  [MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
   Q.EXISTS_TAC `{x | x IN m_space m /\ 2 pow i <= f x}` THEN
   ASM_SIMP_TAC std_ss [space_def, IN_UNIV] THEN
   Q_TAC SUFF_TAC `{x | x IN m_space m /\ 2 pow i <= f x} =
   PREIMAGE f {x | 2 pow i <= x} INTER
    space (m_space m,measurable_sets m)` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [PREIMAGE_def, space_def, INTER_UNIV] THEN
    SET_TAC []] THEN
   FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
    METIS_TAC [pow_not_infty, num_not_infty] THEN
   METIS_TAC [BOREL_MEASURABLE_SETS_CR, normal_real], ALL_TAC] THEN
  CONJ_TAC THENL
  [SIMP_TAC std_ss [extreal_of_num_def, extreal_pow_def, extreal_le_def] THEN
   MATCH_MP_TAC POW_POS THEN SIMP_TAC real_ss [], ALL_TAC] THEN
  CONJ_TAC THENL
  [GEN_TAC THEN SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
   SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def], ALL_TAC] THEN
  Q_TAC SUFF_TAC `P (indicator_fn {x | x IN m_space m /\ 2 pow i <= f x})` THENL
  [METIS_TAC [ETA_AX], ALL_TAC] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN
  ONCE_REWRITE_TAC [METIS [subsets_def]
    ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
  Q_TAC SUFF_TAC `{x | x IN m_space m /\ 2 pow i <= f x} = PREIMAGE f {x | 2 pow i <= x} INTER
     space (m_space m,measurable_sets m)` THENL
  [DISC_RW_KILL,
   SIMP_TAC std_ss [PREIMAGE_def, space_def, INTER_UNIV] THEN
   SET_TAC []] THEN
  FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  `2 pow i <> NegInf /\ 2 pow i <> PosInf` by
    METIS_TAC [pow_not_infty, num_not_infty] THEN
  METIS_TAC [BOREL_MEASURABLE_SETS_CR, normal_real]
QED

(*****************************************************************)

(* added `x IN m_space m` *)
Theorem integral_sequence :
    !m f.  (!x. x IN m_space m ==> 0 <= f x) /\ measure_space m /\
           f IN measurable (m_space m,measurable_sets m) Borel
       ==> (pos_fn_integral m f = sup (IMAGE (\i. pos_fn_integral m (fn_seq m f i)) UNIV))
Proof
    RW_TAC std_ss []
 >> MATCH_MP_TAC lebesgue_monotone_convergence
 >> RW_TAC std_ss [lemma_fn_seq_sup, lemma_fn_seq_mono_increasing,
                   lemma_fn_seq_upper_bounded, lemma_fn_seq_positive]
 >> METIS_TAC [lemma_fn_seq_in_psfis, IN_MEASURABLE_BOREL_POS_SIMPLE_FN, IN_psfis_eq]
QED

Theorem measurable_sequence :
    !m f. measure_space m /\ f IN measurable (m_space m,measurable_sets m) Borel ==>
         (?fi ri. (!x. mono_increasing (\i. fi i x)) /\
                  (!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = fn_plus f x)) /\
                  (!i. ri i IN psfis m (fi i)) /\
                  (!i x. fi i x <= fn_plus f x) /\
                  (!i x. 0 <= fi i x) /\
                  (pos_fn_integral m (fn_plus f) =
                   sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV))) /\
         (?gi vi. (!x. mono_increasing (\i. gi i x)) /\
                  (!x. x IN m_space m ==> (sup (IMAGE (\i. gi i x) UNIV) = fn_minus f x)) /\
                  (!i. vi i IN psfis m (gi i)) /\
                  (!i x. (gi i) x <= fn_minus f x) /\
                  (!i x. 0 <= gi i x) /\
                  (pos_fn_integral m (fn_minus f) =
                   sup (IMAGE (\i. pos_fn_integral m (gi i)) UNIV)))
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘sigma_algebra (measurable_space m)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
 >> CONJ_TAC
 >- (Q.EXISTS_TAC `(\n. fn_seq m (fn_plus f) n)` \\
     Q.EXISTS_TAC `(\n. fn_seq_integral m (fn_plus f) n)` \\
     CONJ_TAC >- RW_TAC std_ss [FN_PLUS_POS, lemma_fn_seq_mono_increasing] \\
     CONJ_TAC >- RW_TAC std_ss [FN_PLUS_POS, lemma_fn_seq_sup] \\
     CONJ_TAC
     >- FULL_SIMP_TAC std_ss [FN_PLUS_POS, lemma_fn_seq_in_psfis,
                              IN_MEASURABLE_BOREL_FN_PLUS] \\
     CONJ_TAC >- METIS_TAC [FN_PLUS_POS, lemma_fn_seq_upper_bounded] \\
     CONJ_TAC >- METIS_TAC [FN_PLUS_POS, lemma_fn_seq_positive] \\
     METIS_TAC [FN_PLUS_POS, integral_sequence, IN_MEASURABLE_BOREL_FN_PLUS])
 >> Q.EXISTS_TAC `(\n. fn_seq m (fn_minus f) n)`
 >> Q.EXISTS_TAC `(\n. fn_seq_integral m (fn_minus f) n)`
 >> CONJ_TAC
 >- RW_TAC std_ss [FN_MINUS_POS, lemma_fn_seq_mono_increasing]
 >> CONJ_TAC
 >- RW_TAC std_ss [FN_MINUS_POS, lemma_fn_seq_sup]
 >> CONJ_TAC
 >- FULL_SIMP_TAC std_ss [FN_MINUS_POS, lemma_fn_seq_in_psfis,
                          IN_MEASURABLE_BOREL_FN_MINUS]
 >> CONJ_TAC
 >- METIS_TAC [FN_MINUS_POS, lemma_fn_seq_upper_bounded]
 >> CONJ_TAC
 >- METIS_TAC [FN_MINUS_POS, lemma_fn_seq_positive]
 >> METIS_TAC [FN_MINUS_POS, integral_sequence, IN_MEASURABLE_BOREL_FN_MINUS]
QED

(* deep result. added `x IN m_space m` *)
Theorem pos_fn_integral_mono_AE : (* was: positive_integral_mono_AE *)
    !m u v. measure_space m /\
            (!x. x IN m_space m ==> 0 <= u x) /\
            (!x. x IN m_space m ==> 0 <= v x) /\
            (AE x::m. u x <= v x) ==>
            pos_fn_integral m u <= pos_fn_integral m v
Proof
    Q.X_GEN_TAC ‘M’
 >> RW_TAC std_ss [pos_fn_integral_def]
 >> MATCH_MP_TAC sup_le_sup_imp'
 >> RW_TAC std_ss [GSPECIFICATION]
 >> FULL_SIMP_TAC std_ss [GSPECIFICATION, IN_psfis_eq]
 >> FULL_SIMP_TAC std_ss [AE_ALT, GSPECIFICATION]
 >> `AE x::M. x NOTIN N`
      by (MATCH_MP_TAC AE_NOT_IN THEN ASM_SIMP_TAC std_ss [])
 >> Q.ABBREV_TAC `nn = (\x. g x * indicator_fn (m_space M DIFF N) x)`
 >> Know `AE x::M. g x <= nn x`
 >- (FULL_SIMP_TAC std_ss [AE_ALT, GSPECIFICATION] THEN Q.EXISTS_TAC `N'` THEN
     FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN RW_TAC std_ss [] THEN
     FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN POP_ASSUM MP_TAC THEN
     Q.UNABBREV_TAC `nn` THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
     RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone, le_refl] THEN
     ASM_SET_TAC []) >> DISCH_TAC
 >> Know `!x. x IN m_space M ==> nn x <= v x`
 >- (Q.X_GEN_TAC ‘y’ >> DISCH_TAC >> Q.UNABBREV_TAC `nn` \\
     ASM_SIMP_TAC std_ss [indicator_fn_def] \\
     COND_CASES_TAC >> ASM_SIMP_TAC std_ss [mul_rone, mul_rzero] \\
     FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_DIFF] \\
     POP_ASSUM MP_TAC >> ONCE_REWRITE_TAC [MONO_NOT_EQ] \\
     RW_TAC std_ss [] >> FIRST_ASSUM MATCH_MP_TAC \\
     FULL_SIMP_TAC std_ss [GSYM extreal_lt_def] >> METIS_TAC [lte_trans])
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss [GSYM IN_NULL_SET, null_sets, GSPECIFICATION]
 >> `?e. e NOTIN s` by METIS_TAC [num_FINITE_AVOID, pos_simple_fn_def]
 >> Know `pos_simple_fn M nn (e INSERT s)
            (\i. if i = e then N else a i DIFF N)
            (\i. if i = e then 0 else x' i)`
 >- (FULL_SIMP_TAC std_ss [pos_simple_fn_def] \\
     Q.UNABBREV_TAC `nn` >> RW_TAC real_ss [] >> TRY (ASM_SET_TAC []) >|
     [ (* goal 1 (of 5) *)
       Q.PAT_X_ASSUM ‘!t. t IN m_space M ==> g t = _’
          (fn th => (ONCE_REWRITE_TAC [SYM (MATCH_MP th (ASSUME “t IN m_space M”))])) \\
       MATCH_MP_TAC le_mul >> ASM_SIMP_TAC std_ss [INDICATOR_FN_POS],
       (* goal 2 (of 5) *)
       ALL_TAC,
       (* goal 3 (of 5) *)
       ONCE_REWRITE_TAC [METIS [subsets_def]
         ``measurable_sets M = subsets (m_space M, measurable_sets M)``] \\
       MATCH_MP_TAC SIGMA_ALGEBRA_DIFF \\
      `i IN s` by ASM_SET_TAC [] \\
       fs [measure_space_def],
       (* goal 4 (of 5) *)
       METIS_TAC [FINITE_INSERT],
       (* goal 5 (of 5) *)
       SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, IN_IMAGE, GSPECIFICATION, IN_DIFF] \\
       GEN_TAC >> EQ_TAC
       >- (RW_TAC std_ss [] THEN UNDISCH_TAC ``x IN s'`` THEN ASM_REWRITE_TAC [] THEN
          `N SUBSET m_space M`
             by (MATCH_MP_TAC MEASURABLE_SETS_SUBSET_SPACE THEN ASM_SIMP_TAC std_ss []) \\
          `!i. i IN s ==> a i SUBSET m_space M` by (RW_TAC std_ss [] THEN
           MATCH_MP_TAC MEASURABLE_SETS_SUBSET_SPACE THEN ASM_SIMP_TAC std_ss []) THEN
           ASM_SET_TAC []) \\
       DISCH_TAC >> `?i. x IN a i /\ i IN s` by ASM_SET_TAC [] \\
       ASM_CASES_TAC ``x IN N``
       >- (Q.EXISTS_TAC `N` THEN ASM_SIMP_TAC std_ss [] \\
           Q.EXISTS_TAC `e` THEN ASM_SET_TAC []) \\
       Q.EXISTS_TAC `a i DIFF N` \\
       CONJ_TAC >- ASM_SET_TAC [] \\
       Q.EXISTS_TAC `i` >> ASM_SET_TAC [] ] \\ (* end of 5 goals *)
     (* continue goal 2 (of 5) *)
     ASM_CASES_TAC ``t IN N`` >> ASM_SIMP_TAC std_ss [indicator_fn_def, IN_DIFF]
     >- (SIMP_TAC std_ss [mul_rzero] >> ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_0 >> ASM_SIMP_TAC std_ss [FINITE_INSERT] \\
         RW_TAC std_ss [IN_INSERT, GSYM extreal_of_num_def, mul_rzero, mul_lzero, mul_rone] \\
         ASM_SET_TAC []) \\
     ASM_SIMP_TAC std_ss [mul_rone] \\
     Q.ABBREV_TAC `f = (\i. Normal (if i = e then 0 else x' i) *
                            if t IN if i = e then N else a i DIFF N then 1 else 0)` \\
     ONCE_REWRITE_TAC [SET_RULE ``e INSERT s = {e} UNION s``] \\
     Know `(!x. x IN {e} UNION s ==> f x <> NegInf) \/
           (!x. x IN {e} UNION s ==> f x <> PosInf) ==>
           (SIGMA f ({e} UNION s) = SIGMA f {e} + SIGMA f s)`
     >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_DISJOINT_UNION \\
         ASM_SIMP_TAC std_ss [FINITE_SING] >> ASM_SET_TAC []) >> DISCH_TAC \\
     Know `(SIGMA f ({e} UNION s) = SIGMA f {e} + SIGMA f s)`
     >- (POP_ASSUM MATCH_MP_TAC THEN DISJ1_TAC THEN Q.UNABBREV_TAC `f` \\
         RW_TAC std_ss [IN_UNION] THENL
         [SIMP_TAC std_ss [GSYM extreal_of_num_def, mul_lzero, num_not_infty],
          SIMP_TAC std_ss [GSYM extreal_of_num_def, mul_lzero, num_not_infty],
          SIMP_TAC std_ss [mul_rone, extreal_not_infty],
          SIMP_TAC std_ss [mul_rone, extreal_not_infty],
          SIMP_TAC std_ss [mul_rzero, num_not_infty],
          SIMP_TAC std_ss [mul_rzero, num_not_infty]]) \\
     DISC_RW_KILL >> Q.UNABBREV_TAC `f` >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_SING] \\
     SIMP_TAC std_ss [mul_rzero, add_lzero] \\
     FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP EXTREAL_SUM_IMAGE_EQ) THEN RW_TAC std_ss [] >|
     [ALL_TAC, ASM_SET_TAC [], ASM_SET_TAC []] \\
     DISJ1_TAC >> RW_TAC std_ss [] >> `x <> e` by ASM_SET_TAC [] >|
     [SIMP_TAC std_ss [mul_rone, extreal_not_infty],
      SIMP_TAC std_ss [mul_rone, extreal_not_infty],
      SIMP_TAC std_ss [mul_rzero, num_not_infty],
      SIMP_TAC std_ss [mul_rzero, num_not_infty],
      SIMP_TAC std_ss [mul_rone, extreal_not_infty],
      ALL_TAC] \\
     SIMP_TAC std_ss [mul_rzero, num_not_infty]) >> DISCH_TAC
 (* stage work *)
 >> Q.EXISTS_TAC `pos_simple_fn_integral M (e INSERT s)
   (\i. if i = e then N else a i DIFF N) (\i. if i = e then 0 else x' i)` THEN
  CONJ_TAC THENL [METIS_TAC [], ALL_TAC] THEN
  SIMP_TAC std_ss [pos_simple_fn_integral_def] THEN
  Q.ABBREV_TAC `f = (\i. Normal (if i = e then 0 else x' i) *
     measure M (if i = e then N else a i DIFF N))` THEN
  ONCE_REWRITE_TAC [SET_RULE ``e INSERT s = {e} UNION s``] THEN
  Q_TAC SUFF_TAC `(!x. x IN {e} UNION s ==> f x <> NegInf) \/
                  (!x. x IN {e} UNION s ==> f x <> PosInf) ==>
                  (SIGMA f ({e} UNION s) = SIGMA f {e} + SIGMA f s)` THENL
  [ALL_TAC,
   MATCH_MP_TAC EXTREAL_SUM_IMAGE_DISJOINT_UNION THEN
   ASM_SIMP_TAC std_ss [FINITE_SING] THEN ASM_SET_TAC [pos_simple_fn_def]] THEN
  DISCH_TAC THEN Q_TAC SUFF_TAC `(SIGMA f ({e} UNION s) = SIGMA f {e} + SIGMA f s)` THENL
  [ALL_TAC,
   POP_ASSUM MATCH_MP_TAC THEN DISJ1_TAC THEN Q.UNABBREV_TAC `f` THEN
   RW_TAC std_ss [IN_UNION] THENL
   [SIMP_TAC std_ss [mul_rzero, num_not_infty], ASM_SET_TAC [],
    ALL_TAC] THEN
   SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
   Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
   MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
   FULL_SIMP_TAC std_ss [pos_simple_fn_def, measure_space_def, positive_def] THEN
   SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN FIRST_ASSUM MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets M = subsets (m_space M, measurable_sets M)``] THEN
   MATCH_MP_TAC ALGEBRA_DIFF THEN
   FULL_SIMP_TAC std_ss [subsets_def, measure_space_def, sigma_algebra_def]] THEN
  DISC_RW_KILL THEN Q.UNABBREV_TAC `f` THEN RW_TAC std_ss [EXTREAL_SUM_IMAGE_SING] THEN
  SIMP_TAC std_ss [mul_rzero, add_lzero] THEN `FINITE s` by METIS_TAC [pos_simple_fn_def] THEN
  FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP EXTREAL_SUM_IMAGE_MONO) THEN RW_TAC std_ss [] THENL
  [DISJ1_TAC THEN RW_TAC std_ss [] THENL
   [SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
    Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
    MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
    FULL_SIMP_TAC std_ss [pos_simple_fn_def, measure_space_def, positive_def] THEN
    SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC std_ss [], ALL_TAC] THEN
   SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
   Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
   MATCH_MP_TAC le_mul THEN SIMP_TAC std_ss [extreal_of_num_def, extreal_le_def] THEN
   FULL_SIMP_TAC std_ss [pos_simple_fn_def, measure_space_def, positive_def] THEN
   SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN FIRST_ASSUM MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets M = subsets (m_space M, measurable_sets M)``] THEN
   MATCH_MP_TAC ALGEBRA_DIFF THEN
   FULL_SIMP_TAC std_ss [subsets_def, measure_space_def, sigma_algebra_def],
   ALL_TAC] THEN
  ONCE_REWRITE_TAC [SET_RULE ``a DIFF b = a DIFF (a INTER b)``] THEN
  Q_TAC SUFF_TAC `measure M (a x DIFF a x INTER N) = measure M (a x) - measure M (a x INTER N)` THENL
  [ALL_TAC,
   MATCH_MP_TAC MEASURE_DIFF_SUBSET THEN FULL_SIMP_TAC std_ss [pos_simple_fn_def] THEN
   CONJ_TAC THENL
   [ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets M = subsets (m_space M, measurable_sets M)``] THEN
    MATCH_MP_TAC ALGEBRA_INTER THEN
    FULL_SIMP_TAC std_ss [subsets_def, measure_space_def, sigma_algebra_def],
    ALL_TAC] THEN
   CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
   SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC let_trans THEN
   Q.EXISTS_TAC `measure M N` THEN CONJ_TAC THENL
   [ALL_TAC, METIS_TAC [lt_infty, num_not_infty]] THEN
   MATCH_MP_TAC INCREASING THEN ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING] THEN
   CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
   ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets M = subsets (m_space M, measurable_sets M)``] THEN
   MATCH_MP_TAC ALGEBRA_INTER THEN
   FULL_SIMP_TAC std_ss [subsets_def, measure_space_def, sigma_algebra_def]] THEN
  DISC_RW_KILL THEN Q_TAC SUFF_TAC `measure M (a x INTER N) = 0` THENL
  [SIMP_TAC std_ss [le_refl, sub_rzero], ALL_TAC] THEN
  SIMP_TAC std_ss [GSYM le_antisym] THEN CONJ_TAC THENL
  [ALL_TAC,
   FULL_SIMP_TAC std_ss [measure_space_def, positive_def] THEN
   FIRST_ASSUM MATCH_MP_TAC THEN FULL_SIMP_TAC std_ss [pos_simple_fn_def] THEN
   ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets M = subsets (m_space M, measurable_sets M)``] THEN
   MATCH_MP_TAC ALGEBRA_INTER THEN
   FULL_SIMP_TAC std_ss [subsets_def, measure_space_def, sigma_algebra_def]] THEN
  `0 = measure M N` by METIS_TAC [] THEN FIRST_X_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
  MATCH_MP_TAC INCREASING THEN ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING] THEN
  CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN FULL_SIMP_TAC std_ss [pos_simple_fn_def] THEN
  ONCE_REWRITE_TAC [METIS [subsets_def]
    ``measurable_sets M = subsets (m_space M, measurable_sets M)``] THEN
  MATCH_MP_TAC ALGEBRA_INTER THEN
  FULL_SIMP_TAC std_ss [subsets_def, measure_space_def, sigma_algebra_def]
QED

(* key result. added ‘x IN m_space m’ *)
Theorem pos_fn_integral_cong_AE : (* was: positive_integral_cong_AE *)
    !m u v. measure_space m /\
           (!x. x IN m_space m ==> 0 <= u x) /\
           (!x. x IN m_space m ==> 0 <= v x) /\
           (AE x::m. u x = v x) ==>
           (pos_fn_integral m u = pos_fn_integral m v)
Proof
    RW_TAC std_ss [GSYM le_antisym] (* 2 subgoals, same tactics *)
 >> MATCH_MP_TAC pos_fn_integral_mono_AE
 >> FULL_SIMP_TAC std_ss [AE_ALT, SUBSET_DEF, GSPECIFICATION]
 >> METIS_TAC []
QED

(* common result. added ‘x IN m_space m’ *)
Theorem pos_fn_integral_cong : (* was: positive_integral_cong *)
    !m u v. measure_space m /\
           (!x. x IN m_space m ==> 0 <= u x) /\
           (!x. x IN m_space m ==> 0 <= v x) /\
           (!x. x IN m_space m ==> (u x = v x)) ==>
           (pos_fn_integral m u = pos_fn_integral m v)
Proof
    RW_TAC std_ss []
 >> MATCH_MP_TAC pos_fn_integral_cong_AE
 >> FULL_SIMP_TAC std_ss [AE_ALT, GSPECIFICATION]
 >> `{x | x IN m_space m /\ u x <> v x} = {}` by ASM_SET_TAC []
 >> Q.EXISTS_TAC `{}`
 >> ASM_SIMP_TAC std_ss [SUBSET_REFL, GSYM IN_NULL_SET, null_sets,
                         GSPECIFICATION]
 >> METIS_TAC [measure_space_def, positive_def, sigma_algebra_alt_pow]
QED

Theorem pos_fn_integral_add :
    !m f g. measure_space m /\
           (!x. x IN m_space m ==> 0 <= f x) /\
           (!x. x IN m_space m ==> 0 <= g x) /\
            f IN measurable (m_space m,measurable_sets m) Borel /\
            g IN measurable (m_space m,measurable_sets m) Borel ==>
           (pos_fn_integral m (\x. f x + g x) = pos_fn_integral m f + pos_fn_integral m g)
Proof
    rpt STRIP_TAC
 >> `?fi ui.
       (!x. mono_increasing (\i. fi i x)) /\
       (!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = (fn_plus f) x)) /\
       (!i. ui i IN psfis m (fi i)) /\
       (!i x. fi i x <= (fn_plus f) x) /\
       (!i x. 0 <= fi i x) /\
       (pos_fn_integral m (fn_plus f) = sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV))`
            by METIS_TAC [measurable_sequence]
 >> `?gi vi.
       (!x. mono_increasing (\i. gi i x)) /\
       (!x. x IN m_space m ==> (sup (IMAGE (\i. gi i x) UNIV) = (fn_plus g) x)) /\
       (!i. vi i IN psfis m (gi i)) /\
       (!i x. gi i x <= (fn_plus g) x) /\
       (!i x. 0 <= gi i x) /\
       (pos_fn_integral m (fn_plus g) = sup (IMAGE (\i. pos_fn_integral m (gi i)) UNIV))`
            by METIS_TAC [measurable_sequence]
 >> Know ‘pos_fn_integral m f = pos_fn_integral m (fn_plus f)’
 >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [FN_PLUS_POS] \\
     rpt STRIP_TAC >> rw []) >> Rewr'
 >> Know ‘pos_fn_integral m g = pos_fn_integral m (fn_plus g)’
 >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [FN_PLUS_POS] \\
     rpt STRIP_TAC >> rw []) >> Rewr'
 >> `sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV) +
     sup (IMAGE (\i. pos_fn_integral m (gi i)) UNIV) =
     sup (IMAGE (\i. (\n. pos_fn_integral m (fi n)) i + (\n. pos_fn_integral m (gi n)) i) UNIV)`
       by (MATCH_MP_TAC (GSYM sup_add_mono) \\
           FULL_SIMP_TAC std_ss [pos_fn_integral_pos, ext_mono_increasing_suc, pos_fn_integral_mono])
 >> FULL_SIMP_TAC std_ss []
 >> `!i. (\x. fi i x + gi i x) IN measurable (m_space m,measurable_sets m) Borel`
       by METIS_TAC [IN_MEASURABLE_BOREL_POS_SIMPLE_FN, IN_psfis_eq, psfis_add]
 >> `!x. mono_increasing (\i. (\i x. fi i x + gi i x) i x)`
       by FULL_SIMP_TAC std_ss [ext_mono_increasing_def, le_add2]
 >> Know `!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x + gi i x) UNIV) = f x + g x)`
 >- (rpt STRIP_TAC \\
    `f x = sup (IMAGE (\i. fi i x) UNIV)` by METIS_TAC [FN_PLUS_REDUCE] >> POP_ORW \\
    `g x = sup (IMAGE (\i. gi i x) UNIV)` by METIS_TAC [FN_PLUS_REDUCE] >> POP_ORW \\
     FULL_SIMP_TAC std_ss [pos_fn_integral_pos, sup_add_mono,
                           ext_mono_increasing_suc, pos_fn_integral_mono])
 >> DISCH_TAC
 >> (MP_TAC o Q.SPECL [`m`, `\x. f x + g x`, `\i. (\x. fi i x + gi i x)`])
       lebesgue_monotone_convergence
 >> RW_TAC std_ss []
 >> Suff `(\i. pos_fn_integral m (fi i) + pos_fn_integral m (gi i)) =
          (\i. pos_fn_integral m (\x. fi i x + gi i x))`
 >- RW_TAC std_ss [le_add]
 >> RW_TAC std_ss [FUN_EQ_THM]
 >> METIS_TAC [IN_psfis_eq, psfis_add, pos_fn_integral_pos_simple_fn]
QED

Theorem pos_fn_integral_add3 :
    !m f g h. measure_space m /\
             (!x. x IN m_space m ==> 0 <= f x) /\
             (!x. x IN m_space m ==> 0 <= g x) /\
             (!x. x IN m_space m ==> 0 <= h x) /\
              f IN measurable (m_space m,measurable_sets m) Borel /\
              g IN measurable (m_space m,measurable_sets m) Borel /\
              h IN measurable (m_space m,measurable_sets m) Borel
          ==> pos_fn_integral m (\x. f x + g x + h x) =
              pos_fn_integral m f + pos_fn_integral m g + pos_fn_integral m h
Proof
    rpt STRIP_TAC
 >> Know ‘pos_fn_integral m (\x. f x + g x + h x) =
          pos_fn_integral m (\x. f x + g x) +
          pos_fn_integral m h’
 >- (HO_MATCH_MP_TAC pos_fn_integral_add >> rw [le_add] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD' \\
     qexistsl_tac [‘f’, ‘g’] >> rw [] \\
     fs [measure_space_def])
 >> Rewr'
 >> Suff ‘pos_fn_integral m (\x. f x + g x) =
          pos_fn_integral m f + pos_fn_integral m g’ >- rw []
 >> MATCH_MP_TAC pos_fn_integral_add >> art []
QED

(* added ‘x IN m_space m’. used by martingaleTheory.EXISTENCE_OF_PROD_MEASURE *)
Theorem pos_fn_integral_sub :
    !m f g. measure_space m /\
            f IN measurable (m_space m,measurable_sets m) Borel /\
            g IN measurable (m_space m,measurable_sets m) Borel /\
           (!x. x IN m_space m ==> 0 <= g x) /\
           (!x. x IN m_space m ==> g x <= f x) /\
           (!x. x IN m_space m ==> g x <> PosInf) /\
            pos_fn_integral m g <> PosInf ==>
           (pos_fn_integral m (\x. f x - g x) = pos_fn_integral m f - pos_fn_integral m g)
Proof
    rpt STRIP_TAC
 >> Know `pos_fn_integral m g <> NegInf /\ pos_fn_integral m g <> PosInf`
 >- (art [] >> MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC pos_fn_integral_pos >> art [])
 >> DISCH_THEN (ONCE_REWRITE_TAC o wrap o (MATCH_MP eq_sub_ladd))
 >> Know `pos_fn_integral m (\x. f x - g x) + pos_fn_integral m g =
          pos_fn_integral m (\x. (\x. f x - g x) x + g x)`
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC pos_fn_integral_add >> simp [] \\
     CONJ_TAC >- (rpt STRIP_TAC >> MATCH_MP_TAC le_sub_imp >> simp [add_lzero] \\
                  MATCH_MP_TAC pos_not_neginf \\
                  FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
     qexistsl_tac [`f`, `g`] >> fs [measure_space_def] \\
     GEN_TAC >> DISCH_TAC \\
     Suff ‘f x <> NegInf’ >- PROVE_TAC [] \\
     MATCH_MP_TAC pos_not_neginf >> simp [] \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC ‘g x’ \\
     CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> Rewr'
 >> BETA_TAC
 >> Suff `!x. x IN m_space m ==> f x - g x + g x = f x`
 >- (DISCH_TAC >> MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
     rpt STRIP_TAC \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC ‘g x’ \\
     CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> rpt STRIP_TAC
 >> MATCH_MP_TAC sub_add >> art []
 >> CONJ_TAC
 >- (MATCH_MP_TAC pos_not_neginf \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

(* lebesgue_monotone_convergence for decreasing function sequences

   The case for mono-decreasing functions can be derived as an easy corollary,
   because ‘\i x. f 0 x - f i x’ is mono-increasing, while assuming additionally

   1. !i x. x IN m_space m ==> fi i x < PosInf
   2. !i. pos_fn_integral m (fi i) <> PosInf
 *)
Theorem lebesgue_monotone_convergence_decreasing :
    !m f fi. measure_space m /\
        (!i. fi i IN measurable (m_space m, measurable_sets m) Borel) /\
        (!i x. x IN m_space m ==> 0 <= fi i x /\ fi i x < PosInf) /\
        (!i. pos_fn_integral m (fi i) <> PosInf) /\
        (!x. x IN m_space m ==> mono_decreasing (\i. fi i x)) /\
        (!x. x IN m_space m ==> (inf (IMAGE (\i. fi i x) UNIV) = f x)) ==>
        (pos_fn_integral m f = inf (IMAGE (\i. pos_fn_integral m (fi i)) UNIV))
Proof
    rpt STRIP_TAC
 >> Know ‘!x. x IN m_space m ==> 0 <= f x’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!x. x IN m_space m ==> _ = f x’ (MP_TAC o (Q.SPEC ‘x’)) \\
     RW_TAC std_ss [] \\
     POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) \\
     rw [le_inf'] >> PROVE_TAC []) >> DISCH_TAC
 >> Q.ABBREV_TAC ‘gi = \i x. fi 0 x - fi i x’
 >> Know ‘!i x. x IN m_space m ==> 0 <= gi i x’
 >- (rw [Abbr ‘gi’] \\
     Know ‘0 <= fi 0 x - fi i x <=> fi i x <= fi 0 x’
     >- (MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC sub_zero_le \\
         CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf >> PROVE_TAC []) \\
         PROVE_TAC [lt_infty]) >> Rewr' \\
     fs [ext_mono_decreasing_def]) >> DISCH_TAC
 >> Know ‘!i x. x IN m_space m ==> gi i x <> PosInf’
 >- (rw [Abbr ‘gi’] \\
    ‘fi 0 x <> PosInf /\ fi i x <> PosInf’ by METIS_TAC [lt_infty] \\
    ‘fi 0 x <> NegInf /\ fi i x <> NegInf’ by METIS_TAC [pos_not_neginf] \\
    ‘?a. fi 0 x = Normal a’ by METIS_TAC [extreal_cases] \\
    ‘?b. fi i x = Normal b’ by METIS_TAC [extreal_cases] \\
     rw [extreal_sub_def, extreal_not_infty]) >> DISCH_TAC
 >> Know ‘!x. x IN m_space m ==> mono_increasing (\i. gi i x)’
 >- (rw [Abbr ‘gi’, ext_mono_increasing_def] \\
     MATCH_MP_TAC le_lsub_imp \\
     fs [ext_mono_decreasing_def]) >> DISCH_TAC
 >> Q.ABBREV_TAC ‘g = \x. sup (IMAGE (\i. gi i x) UNIV)’
 >> Know ‘!x. x IN m_space m ==> 0 <= g x’
 >- (rw [Abbr ‘g’, le_sup'] \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC ‘gi 0 x’ \\
     ASM_SIMP_TAC std_ss [] \\
     POP_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘0’ >> REWRITE_TAC []) >> DISCH_TAC
 >> Know ‘!i. gi i IN Borel_measurable (m_space m,measurable_sets m)’
 >- (rw [Abbr ‘gi’] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
     qexistsl_tac [‘fi 0’, ‘fi i’] >> fs [measure_space_def] \\
     rpt STRIP_TAC >> DISJ1_TAC \\
     reverse CONJ_TAC >- rw [lt_infty] \\
     MATCH_MP_TAC pos_not_neginf >> PROVE_TAC []) >> DISCH_TAC
 >> Know ‘!i x. x IN m_space m ==> (fi i x = fi 0 x - gi i x)’
 >- (rpt STRIP_TAC \\
     Know ‘fi i x = fi 0 x - gi i x <=> fi i x + gi i x = fi 0 x’
     >- (MATCH_MP_TAC eq_sub_ladd >> rw [] \\
         MATCH_MP_TAC pos_not_neginf >> rw []) >> Rewr' \\
     Know ‘fi i x + gi i x = gi i x + fi i x’
     >- (MATCH_MP_TAC add_comm >> DISJ2_TAC >> rw [] \\
         rw [lt_infty]) >> Rewr' \\
     rw [Abbr ‘gi’] >> MATCH_MP_TAC sub_add \\
     CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf >> PROVE_TAC []) \\
     rw [lt_infty]) >> DISCH_TAC
 >> Know ‘!i. pos_fn_integral m (gi i) =
              pos_fn_integral m (fi 0) - pos_fn_integral m (fi i)’
 >- (GEN_TAC \\
     Know ‘pos_fn_integral m (gi i) = pos_fn_integral m (\x. fi 0 x - fi i x)’
     >- (MATCH_MP_TAC pos_fn_integral_cong >> rw []) >> Rewr' \\
     MATCH_MP_TAC pos_fn_integral_sub >> art [] \\
     CONJ_TAC >- METIS_TAC [] \\
     reverse CONJ_TAC >- METIS_TAC [lt_infty] \\
     rpt STRIP_TAC >> rfs [ext_mono_decreasing_def]) >> DISCH_TAC
 >> Know ‘!i. pos_fn_integral m (fi i) <> NegInf’
 >- (GEN_TAC \\
     MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC pos_fn_integral_pos >> rw []) >> DISCH_TAC
 >> Know ‘!i. pos_fn_integral m (gi i) <> PosInf’
 >- (GEN_TAC \\
     Q.PAT_X_ASSUM ‘!i. pos_fn_integral m (gi i) = _’ (ONCE_REWRITE_TAC o wrap) \\
    ‘?a. pos_fn_integral m (fi 0) = Normal a’ by METIS_TAC [extreal_cases] \\
    ‘?b. pos_fn_integral m (fi i) = Normal b’ by METIS_TAC [extreal_cases] \\
     rw [extreal_sub_def, extreal_not_infty]) >> DISCH_TAC
 >> Know ‘!i. pos_fn_integral m (gi i) <> NegInf’
 >- (GEN_TAC \\
     MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC pos_fn_integral_pos >> rw []) >> DISCH_TAC
 >> Know ‘!i. pos_fn_integral m (fi i) =
              pos_fn_integral m (fi 0) - pos_fn_integral m (gi i)’
 >- (GEN_TAC \\
     Know ‘pos_fn_integral m (fi i) =
           pos_fn_integral m (fi 0) - pos_fn_integral m (gi i) <=>
           pos_fn_integral m (fi i) + pos_fn_integral m (gi i) = pos_fn_integral m (fi 0)’
     >- (MATCH_MP_TAC eq_sub_ladd >> art []) >> Rewr' \\
     Know ‘pos_fn_integral m (fi i) + pos_fn_integral m (gi i) =
           pos_fn_integral m (gi i) + pos_fn_integral m (fi i)’
     >- (MATCH_MP_TAC add_comm >> DISJ2_TAC \\
         POP_ASSUM (REWRITE_TAC o wrap) >> art []) >> Rewr' >> art [] \\
     MATCH_MP_TAC sub_add >> art []) >> Rewr'
 (* stage work *)
 >> REWRITE_TAC [extreal_inf_def]
 >> Know ‘IMAGE numeric_negate
            (IMAGE (\i. pos_fn_integral m (fi 0) - pos_fn_integral m (gi i)) UNIV) =
          IMAGE (\i. pos_fn_integral m (gi i) - pos_fn_integral m (fi 0)) UNIV’
 >- (rw [Once EXTENSION, IN_IMAGE, IN_UNIV] \\
     EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC ‘i’ >> rename1 ‘x = -y’ \\
       Q.PAT_X_ASSUM ‘x = -y’ (ONCE_REWRITE_TAC o wrap) >> POP_ORW \\
      ‘?a. pos_fn_integral m (fi 0) = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
      ‘?b. pos_fn_integral m (fi i) = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
       rw [extreal_sub_def, extreal_ainv_def, extreal_11] \\
       REAL_ARITH_TAC,
       (* goal 2 (of 2) *)
       Q.EXISTS_TAC ‘pos_fn_integral m (fi 0) -
                       (pos_fn_integral m (fi 0) - pos_fn_integral m (fi i))’ \\
       reverse CONJ_TAC >- (Q.EXISTS_TAC ‘i’ >> REWRITE_TAC []) \\
       POP_ORW \\
      ‘?a. pos_fn_integral m (fi 0) = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
      ‘?b. pos_fn_integral m (fi i) = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
       rw [extreal_sub_def, extreal_ainv_def, extreal_11] \\
       REAL_ARITH_TAC ]) >> Rewr'
 >> Know ‘sup (IMAGE (\i. pos_fn_integral m (gi i) - pos_fn_integral m (fi 0)) UNIV) =
          sup (IMAGE (\i. pos_fn_integral m (gi i)) UNIV) - pos_fn_integral m (fi 0)’
 >- (RW_TAC std_ss [sup_eq', IN_IMAGE, IN_UNIV] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC le_rsub_imp \\
       RW_TAC std_ss [le_sup', IN_IMAGE, IN_UNIV] \\
       POP_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘i’ >> REWRITE_TAC [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC sub_le_imp >> art [] \\
       RW_TAC std_ss [sup_le', IN_IMAGE, IN_UNIV] \\
       Know ‘pos_fn_integral m (fi 0) - pos_fn_integral m (fi i) <= y + pos_fn_integral m (fi 0) <=>
             pos_fn_integral m (fi 0) - pos_fn_integral m (fi i) - pos_fn_integral m (fi 0) <= y’
       >- (MATCH_MP_TAC EQ_SYM \\
           MATCH_MP_TAC sub_le_eq >> art []) >> Rewr' \\
       POP_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘i’ >> REWRITE_TAC [] ]) >> Rewr'
 >> Know ‘-(sup (IMAGE (\i. pos_fn_integral m (gi i)) UNIV) - pos_fn_integral m (fi 0)) =
          pos_fn_integral m (fi 0) - sup (IMAGE (\i. pos_fn_integral m (gi i)) UNIV)’
 >- (MATCH_MP_TAC neg_sub >> DISJ2_TAC >> art []) >> Rewr'
 (* applying lebesgue_monotone_convergence *)
 >> Know ‘sup (IMAGE (\i. pos_fn_integral m (gi i)) UNIV) = pos_fn_integral m g’
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC lebesgue_monotone_convergence >> art [] \\
     rpt STRIP_TAC >> METIS_TAC []) >> Rewr'
 >> Know ‘pos_fn_integral m f =
          pos_fn_integral m (\x. inf (IMAGE (\i. fi i x) UNIV))’
 >- (MATCH_MP_TAC pos_fn_integral_cong >> rw []) >> Rewr'
 >> REWRITE_TAC [extreal_inf_def]
 >> Know ‘pos_fn_integral m (\x. -sup (IMAGE numeric_negate (IMAGE (\i. fi i x) UNIV))) =
          pos_fn_integral m (\x. -sup (IMAGE (\i. gi i x - fi 0 x) UNIV))’
 >- (MATCH_MP_TAC pos_fn_integral_cong >> BETA_TAC >> art [] \\
     CONJ_TAC >- (rpt STRIP_TAC \\
                 ‘0 = --0’ by PROVE_TAC [neg_neg] >> POP_ORW \\
                  REWRITE_TAC [le_neg, neg_0] \\
                  SIMP_TAC std_ss [sup_le', IN_IMAGE, IN_UNIV] \\
                  rpt STRIP_TAC >> rename1 ‘y = -z’ \\
                  Q.PAT_X_ASSUM ‘y = -z’ (ONCE_REWRITE_TAC o wrap) \\
                 ‘0 = --0’ by PROVE_TAC [neg_neg] >> POP_ORW \\
                  REWRITE_TAC [le_neg, neg_0] \\
                  POP_ORW >> PROVE_TAC []) \\
     CONJ_TAC >- (rpt STRIP_TAC \\
                 ‘0 = --0’ by PROVE_TAC [neg_neg] >> POP_ORW \\
                  REWRITE_TAC [le_neg, neg_0] \\
                  SIMP_TAC std_ss [sup_le', IN_IMAGE, IN_UNIV] \\
                  rpt STRIP_TAC >> POP_ORW \\
                  Know ‘gi i x - fi 0 x = -(fi 0 x - gi i x)’
                  >- (MATCH_MP_TAC EQ_SYM \\
                      MATCH_MP_TAC neg_sub >> DISJ1_TAC \\
                      reverse CONJ_TAC >- rw [lt_infty] \\
                      MATCH_MP_TAC pos_not_neginf >> PROVE_TAC []) >> Rewr' \\
                 ‘0 = --0’ by PROVE_TAC [neg_neg] >> POP_ORW \\
                  REWRITE_TAC [le_neg, neg_0] \\
                  METIS_TAC []) \\
     rpt STRIP_TAC \\
     REWRITE_TAC [eq_neg] \\
     Suff ‘IMAGE numeric_negate (IMAGE (\i. fi i x) UNIV) =
           IMAGE (\i. gi i x - fi 0 x) UNIV’ >- Rewr \\
     SIMP_TAC std_ss [Once EXTENSION, IN_IMAGE, IN_UNIV] \\
     GEN_TAC >> EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       rename1 ‘y = -z’ >> Q.EXISTS_TAC ‘i’ \\
       Q.PAT_X_ASSUM ‘y = -z’ (ONCE_REWRITE_TAC o wrap) >> POP_ORW \\
       Know ‘gi i x - fi 0 x = -(fi 0 x - gi i x)’
       >- (MATCH_MP_TAC EQ_SYM \\
           MATCH_MP_TAC neg_sub >> DISJ1_TAC \\
           reverse CONJ_TAC >- rw [lt_infty] \\
           MATCH_MP_TAC pos_not_neginf >> PROVE_TAC []) >> Rewr' \\
       REWRITE_TAC [eq_neg] \\
       FIRST_X_ASSUM MATCH_MP_TAC >> art [],
       (* goal 2 (of 2) *)
       rename1 ‘y = gi i x - fi 0 x’ \\
       Q.EXISTS_TAC ‘fi 0 x - gi i x’ >> POP_ORW \\
       CONJ_TAC >- (MATCH_MP_TAC EQ_SYM \\
                    MATCH_MP_TAC neg_sub >> DISJ1_TAC \\
                    reverse CONJ_TAC >- rw [lt_infty] \\
                    MATCH_MP_TAC pos_not_neginf >> PROVE_TAC []) \\
       Q.EXISTS_TAC ‘i’ >> METIS_TAC [] ]) >> Rewr'
 >> Know ‘pos_fn_integral m (\x. -sup (IMAGE (\i. gi i x - fi 0 x) UNIV)) =
          pos_fn_integral m (\x. -(sup (IMAGE (\i. gi i x) UNIV) - fi 0 x))’
 >- (MATCH_MP_TAC pos_fn_integral_cong >> BETA_TAC >> art [] \\
     CONJ_TAC >- (rpt STRIP_TAC \\
                 ‘0 = --0’ by PROVE_TAC [neg_neg] >> POP_ORW \\
                  REWRITE_TAC [le_neg, neg_0] \\
                  SIMP_TAC std_ss [sup_le', IN_IMAGE, IN_UNIV] \\
                  rpt STRIP_TAC >> POP_ORW \\
                  Know ‘gi i x - fi 0 x = -(fi 0 x - gi i x)’
                  >- (MATCH_MP_TAC EQ_SYM \\
                      MATCH_MP_TAC neg_sub >> DISJ1_TAC \\
                      reverse CONJ_TAC >- rw [lt_infty] \\
                      MATCH_MP_TAC pos_not_neginf >> PROVE_TAC []) >> Rewr' \\
                 ‘0 = --0’ by PROVE_TAC [neg_neg] >> POP_ORW \\
                  REWRITE_TAC [le_neg, neg_0] \\
                  METIS_TAC []) \\
     CONJ_TAC >- (rpt STRIP_TAC \\
                 ‘0 = --0’ by PROVE_TAC [neg_neg] >> POP_ORW \\
                  REWRITE_TAC [le_neg, neg_0] \\
                  Know ‘sup (IMAGE (\i. gi i x) UNIV) - fi 0 x <= 0 <=>
                        sup (IMAGE (\i. gi i x) UNIV) <= fi 0 x’
                  >- (MATCH_MP_TAC EQ_SYM \\
                      MATCH_MP_TAC sub_le_zero \\
                      reverse CONJ_TAC >- rw [lt_infty] \\
                      MATCH_MP_TAC pos_not_neginf >> PROVE_TAC []) >> Rewr' \\
                  SIMP_TAC std_ss [sup_le', IN_IMAGE, IN_UNIV] \\
                  rpt STRIP_TAC >> POP_ORW \\
                  Q.UNABBREV_TAC ‘gi’ >> BETA_TAC \\
                  MATCH_MP_TAC sub_le_imp \\
                  CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf >> PROVE_TAC []) \\
                  CONJ_TAC >- rw [lt_infty] \\
                  MATCH_MP_TAC le_addr_imp >> PROVE_TAC []) \\
     rpt STRIP_TAC \\
     REWRITE_TAC [eq_neg] \\
     SIMP_TAC std_ss [sup_eq', IN_IMAGE, IN_UNIV] \\
     rpt STRIP_TAC >- (POP_ORW >> MATCH_MP_TAC le_rsub_imp \\
                       SIMP_TAC std_ss [le_sup', IN_IMAGE, IN_UNIV] \\
                       rpt STRIP_TAC >> POP_ASSUM MATCH_MP_TAC \\
                       Q.EXISTS_TAC ‘i’ >> REWRITE_TAC []) \\
     MATCH_MP_TAC sub_le_imp \\
     CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf >> PROVE_TAC []) \\
     CONJ_TAC >- rw [lt_infty] \\
     SIMP_TAC std_ss [sup_le', IN_IMAGE, IN_UNIV] \\
     rpt STRIP_TAC >> rename1 ‘z = gi i x’ \\
     Know ‘z <= y + fi 0 x <=> z - fi 0 x <= y’
     >- (MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC sub_le_eq \\
         CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf >> PROVE_TAC []) \\
         rw [lt_infty]) >> Rewr' \\
     POP_ORW >> FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘i’ >> REWRITE_TAC []) >> Rewr'
 >> Know ‘pos_fn_integral m (\x. -(sup (IMAGE (\i. gi i x) univ(:num)) - fi 0 x)) =
          pos_fn_integral m (\x. fi 0 x - sup (IMAGE (\i. gi i x) UNIV))’
 >- (MATCH_MP_TAC pos_fn_integral_cong >> BETA_TAC >> art [] \\
     CONJ_TAC >- (rpt STRIP_TAC \\
                 ‘0 = --0’ by PROVE_TAC [neg_neg] >> POP_ORW \\
                  REWRITE_TAC [le_neg, neg_0] \\
                  Know ‘sup (IMAGE (\i. gi i x) UNIV) - fi 0 x <= 0 <=>
                        sup (IMAGE (\i. gi i x) UNIV) <= fi 0 x’
                  >- (MATCH_MP_TAC EQ_SYM \\
                      MATCH_MP_TAC sub_le_zero \\
                      reverse CONJ_TAC >- rw [lt_infty] \\
                      MATCH_MP_TAC pos_not_neginf >> PROVE_TAC []) >> Rewr' \\
                  SIMP_TAC std_ss [sup_le', IN_IMAGE, IN_UNIV] \\
                  rpt STRIP_TAC >> POP_ORW \\
                  Q.UNABBREV_TAC ‘gi’ >> BETA_TAC \\
                  MATCH_MP_TAC sub_le_imp \\
                  CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf >> PROVE_TAC []) \\
                  CONJ_TAC >- rw [lt_infty] \\
                  MATCH_MP_TAC le_addr_imp >> PROVE_TAC []) \\
     CONJ_TAC >- (rpt STRIP_TAC \\
                  MATCH_MP_TAC le_sub_imp2 >> REWRITE_TAC [add_lzero] \\
                  CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf >> PROVE_TAC []) \\
                  CONJ_TAC >- rw [lt_infty] \\
                  SIMP_TAC std_ss [sup_le', IN_IMAGE, IN_UNIV] \\
                  rpt STRIP_TAC >> POP_ORW \\
                  Q.UNABBREV_TAC ‘gi’ >> BETA_TAC \\
                  MATCH_MP_TAC sub_le_imp \\
                  CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf >> PROVE_TAC []) \\
                  CONJ_TAC >- rw [lt_infty] \\
                  MATCH_MP_TAC le_addr_imp >> PROVE_TAC []) \\
     rpt STRIP_TAC \\
     MATCH_MP_TAC neg_sub >> DISJ2_TAC \\
     CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf >> PROVE_TAC []) \\
     rw [lt_infty]) >> Rewr'
 (* final stage, applying pos_fn_integral_sub *)
 >> ‘!x. sup (IMAGE (\i. gi i x) UNIV) = g x’ by METIS_TAC [] >> POP_ORW
 >> MATCH_MP_TAC pos_fn_integral_sub >> art []
 >> CONJ_TAC (* g IN Borel_measurable (m_space m,measurable_sets m) *)
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP \\
     Q.EXISTS_TAC ‘gi’ >> rfs [measure_space_def, ext_mono_increasing_def])
 >> STRONG_CONJ_TAC (* !x. x IN m_space m ==> g x <= fi 0 x *)
 >- (Q.UNABBREV_TAC ‘g’ >> BETA_TAC \\
     rpt STRIP_TAC \\
     SIMP_TAC std_ss [sup_le', IN_IMAGE, IN_UNIV] \\
     rpt STRIP_TAC >> POP_ORW \\
     Q.UNABBREV_TAC ‘gi’ >> BETA_TAC \\
     MATCH_MP_TAC sub_le_imp \\
     CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf >> PROVE_TAC []) \\
     CONJ_TAC >- rw [lt_infty] \\
     MATCH_MP_TAC le_addr_imp >> PROVE_TAC []) >> DISCH_TAC
 >> CONJ_TAC (* !x. x IN m_space m ==> g x <> PosInf *)
 >- (GEN_TAC >> DISCH_TAC >> REWRITE_TAC [lt_infty] \\
     MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘fi 0 x’ \\
     CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     PROVE_TAC [])
 >> REWRITE_TAC [lt_infty]
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC ‘pos_fn_integral m (fi 0)’
 >> reverse CONJ_TAC >- rw [GSYM lt_infty]
 >> MATCH_MP_TAC pos_fn_integral_mono >> art []
QED

(* cf. lebesgue_monotone_convergence_subset *)
Theorem lebesgue_monotone_convergence_decreasing' :
    !m f fi A. measure_space m /\
        (!i. fi i IN measurable (m_space m, measurable_sets m) Borel) /\
        (!i x. x IN m_space m ==> 0 <= fi i x /\ fi i x < PosInf) /\
        (!i. pos_fn_integral m (fi i) <> PosInf) /\
        (!x. x IN m_space m ==> mono_decreasing (\i. fi i x)) /\
        (!x. x IN m_space m ==> inf (IMAGE (\i. fi i x) UNIV) = f x) /\
         A IN measurable_sets m ==>
        (pos_fn_integral m (\x. f x * indicator_fn A x) =
         inf (IMAGE (\i. pos_fn_integral m (\x. fi i x * indicator_fn A x)) UNIV))
Proof
    RW_TAC std_ss []
 >> (MP_TAC o Q.SPECL [`m`, `(\x. f x * indicator_fn A x)`,
                       `(\i. (\x. fi i x * indicator_fn A x))`])
       lebesgue_monotone_convergence_decreasing
 >> RW_TAC std_ss []
 >> POP_ASSUM MATCH_MP_TAC
 >> CONJ_TAC
 >- METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR, measure_space_def, subsets_def,
               measurable_sets_def]
 >> CONJ_TAC
 >- (RW_TAC std_ss [GSYM lt_infty] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS],
       (* goal 2 (of 2) *)
       STRIP_ASSUME_TAC (Q.SPECL [‘A’, ‘x’] indicator_fn_normal) \\
      ‘fi i x <> PosInf’ by METIS_TAC [lt_infty] \\
      ‘fi i x <> NegInf’ by METIS_TAC [pos_not_neginf] \\
      ‘?z. fi i x = Normal z’ by METIS_TAC [extreal_cases] \\
       rw [extreal_mul_eq] ])
 >> CONJ_TAC
 >- (rw [lt_infty] >> MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘pos_fn_integral m (fi i)’ \\
     reverse CONJ_TAC >- rw [GSYM lt_infty] \\
     MATCH_MP_TAC pos_fn_integral_mono >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC le_mul >> rw [INDICATOR_FN_POS],
       (* goal 1 (of 2) *)
       GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM mul_rone] \\
       MATCH_MP_TAC le_lmul_imp >> rw [INDICATOR_FN_LE_1] ])
 >> CONJ_TAC
 >- (RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, le_refl, ext_mono_decreasing_def] \\
     FULL_SIMP_TAC std_ss [ext_mono_decreasing_def])
 >> RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero]
 >> Suff `IMAGE (\i:num. 0:extreal) UNIV = (\y. y = 0)` >- RW_TAC std_ss [inf_const]
 >> RW_TAC std_ss [EXTENSION, IN_ABS, IN_IMAGE, IN_UNIV]
QED

(* added ‘x IN m_space m’ *)
Theorem pos_fn_integral_sum :
    !m f s. FINITE s /\ measure_space m /\
           (!i. i IN s ==> !x. x IN m_space m ==> 0 <= f i x) /\
           (!i. i IN s ==> f i IN measurable (m_space m,measurable_sets m) Borel) ==>
           (pos_fn_integral m (\x. SIGMA (\i. (f i) x) s) =
            SIGMA (\i. pos_fn_integral m (f i)) s)
Proof
    Suff `!s:'b->bool.
            FINITE s ==>
              (\s:'b->bool. !m f. measure_space m /\
                            (!i. i IN s ==> !x. x IN m_space m ==> 0 <= f i x) /\
                            (!i. i IN s ==> f i IN measurable (m_space m,measurable_sets m) Borel)
                        ==> (pos_fn_integral m (\x. SIGMA (\i. (f i) x) s) =
                             SIGMA (\i. pos_fn_integral m (f i)) s)) s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, pos_fn_integral_zero]
 >> `!x. x IN m_space m ==> SIGMA (\i. f i x) (e INSERT s) = f e x + SIGMA (\i. f i x) s`
      by (RW_TAC std_ss [] \\
          (MP_TAC o Q.SPEC `e` o UNDISCH o Q.SPECL [`(\i. f i x)`,`s`] o
           INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY \\
         `!i. i IN e INSERT s ==> (\i. f i x) i <> NegInf`
              by (RW_TAC std_ss [] \\
                  METIS_TAC [lt_infty, extreal_of_num_def, extreal_not_infty, lte_trans]) \\
          FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT])
 >> Know ‘pos_fn_integral m (\x. SIGMA (\i. f i x) (e INSERT s)) =
          pos_fn_integral m (\x. f e x + SIGMA (\i. f i x) s)’
 >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
     rpt STRIP_TAC \\
     MATCH_MP_TAC le_add >> simp [] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> simp []) >> Rewr'
 >> `!i. i IN e INSERT s ==> (\i. pos_fn_integral m (f i)) i <> NegInf`
      by (RW_TAC std_ss [] \\
          METIS_TAC [lt_infty, extreal_of_num_def, extreal_not_infty, lte_trans,
                     pos_fn_integral_pos])
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
 >> qexistsl_tac [`f`, `s`]
 >> METIS_TAC [measure_space_def, measurable_sets_def, subsets_def, m_space_def, space_def,
               extreal_of_num_def, extreal_not_infty, lt_infty, lte_trans]
QED

(* added ‘x IN m_space m’ *)
Theorem pos_fn_integral_disjoint_sets :
    !m f s t. measure_space m /\
              DISJOINT s t /\ s IN measurable_sets m /\ t IN measurable_sets m /\
              f IN measurable (m_space m,measurable_sets m) Borel /\
             (!x. x IN m_space m ==> 0 <= f x) ==>
             (pos_fn_integral m (\x. f x * indicator_fn (s UNION t) x) =
              pos_fn_integral m (\x. f x * indicator_fn s x) +
              pos_fn_integral m (\x. f x * indicator_fn t x))
Proof
    RW_TAC std_ss []
 >> `(\x. f x * indicator_fn (s UNION t) x) =
     (\x. (\x. f x * indicator_fn s x) x + (\x. f x * indicator_fn t x) x)`
       by (RW_TAC std_ss [FUN_EQ_THM, indicator_fn_def, IN_DISJOINT, IN_UNION,
                          mul_rone, mul_rzero] \\
           Cases_on `x IN s`
           >- (RW_TAC std_ss [mul_rone, mul_rzero, add_rzero] \\
               METIS_TAC [EXTENSION, IN_DISJOINT]) \\
           RW_TAC std_ss [mul_rone, mul_rzero, add_lzero])
 >> POP_ORW
 >> `!s. s IN measurable_sets m ==>
        (\x. f x * indicator_fn s x) IN measurable (m_space m,measurable_sets m) Borel`
       by METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR, measure_space_def,
                     subsets_def, space_def]
 >> MATCH_MP_TAC pos_fn_integral_add
 >> FULL_SIMP_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero]
 >> RW_TAC std_ss [le_refl, mul_rzero, mul_rone]
QED

(* added ‘x IN m_space m’ *)
Theorem pos_fn_integral_disjoint_sets_sum :
    !m f s a. FINITE s /\ measure_space m /\
             (!i. i IN s ==> a i IN measurable_sets m) /\
             (!x. x IN m_space m ==> 0 <= f x) /\
             (!i j. i IN s /\ j IN s /\ i <> j ==> DISJOINT (a i) (a j)) /\
              f IN measurable (m_space m,measurable_sets m) Borel ==>
             (pos_fn_integral m (\x. f x * indicator_fn (BIGUNION (IMAGE a s)) x) =
              SIGMA (\i. pos_fn_integral m (\x. f x * indicator_fn (a i) x)) s)
Proof
    Suff `!s:'b->bool.
            FINITE s ==>
              (\s:'b->bool. !m f a. measure_space m /\
                           (!i. i IN s ==> a i IN measurable_sets m) /\
                           (!x. x IN m_space m ==> 0 <= f x) /\
                           (!i j. i IN s /\ j IN s /\ i <> j ==> DISJOINT (a i) (a j)) /\
                            f IN measurable (m_space m,measurable_sets m) Borel
                       ==> (pos_fn_integral m (\x. f x * indicator_fn (BIGUNION (IMAGE a s)) x) =
                            SIGMA (\i. pos_fn_integral m (\x. f x * indicator_fn (a i) x)) s)) s`
 >- RW_TAC std_ss []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, IMAGE_EMPTY, BIGUNION_EMPTY, FINITE_INSERT,
                   DELETE_NON_ELEMENT, IN_INSERT, BIGUNION_INSERT, IMAGE_INSERT]
 >- RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone, NOT_IN_EMPTY, pos_fn_integral_zero]
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
 >> `e NOTIN s` by METIS_TAC [DELETE_NON_ELEMENT]
 >> `DISJOINT (a e) (BIGUNION (IMAGE a s))`
       by (RW_TAC std_ss [DISJOINT_BIGUNION, IN_IMAGE] >> METIS_TAC [])
 >> `countable (IMAGE a s)` by METIS_TAC [image_countable, finite_countable]
 >> `(IMAGE a s) SUBSET measurable_sets m`
       by (RW_TAC std_ss [SUBSET_DEF, IMAGE_DEF, GSPECIFICATION] \\
           METIS_TAC [])
 >> `BIGUNION (IMAGE a s) IN measurable_sets m`
       by METIS_TAC [sigma_algebra_def, measure_space_def, subsets_def, measurable_sets_def]
 >> METIS_TAC [pos_fn_integral_disjoint_sets]
QED

(* added ‘x IN m_space m’ *)
Theorem pos_fn_integral_split :
    !m f s. measure_space m /\ s IN measurable_sets m /\
           (!x. x IN m_space m ==> 0 <= f x) /\
            f IN measurable (m_space m,measurable_sets m) Borel ==>
           (pos_fn_integral m f = pos_fn_integral m (\x. f x * indicator_fn s x) +
                                  pos_fn_integral m (\x. f x * indicator_fn (m_space m DIFF s) x))
Proof
    RW_TAC std_ss []
 >> (MP_TAC o Q.SPECL [`m`,`f`,`s`,`m_space m DIFF s`]) pos_fn_integral_disjoint_sets
 >> RW_TAC std_ss [DISJOINT_DIFF, MEASURE_SPACE_DIFF, MEASURE_SPACE_MSPACE_MEASURABLE]
 >> `s UNION (m_space m DIFF s) = m_space m`
      by METIS_TAC [UNION_DIFF, MEASURE_SPACE_SUBSET_MSPACE]
 >> METIS_TAC [pos_fn_integral_mspace]
QED

Theorem pos_fn_integral_cmul_infty :
    !m s. measure_space m /\ s IN measurable_sets m ==>
          pos_fn_integral m (\x. PosInf * indicator_fn s x) = PosInf * measure m s
Proof
    RW_TAC std_ss []
 >> Q.ABBREV_TAC `fi = (\i:num x. &i)`
 >> Q.ABBREV_TAC `f = (\x. PosInf)`
 >> `!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) UNIV) = f x)`
      by (RW_TAC std_ss [Abbr ‘fi’, Abbr ‘f’] \\
          Suff `IMAGE (\i. &i) univ(:num) = (\x. ?n. x = &n)`
          >- RW_TAC std_ss [sup_num] \\
          RW_TAC std_ss [EXTENSION, IN_IMAGE, IN_ABS, IN_UNIV])
 >> `!x. x IN m_space m ==> mono_increasing (\i. fi i x)`
      by (RW_TAC std_ss [ext_mono_increasing_def] \\
          RW_TAC real_ss [Abbr ‘fi’, extreal_of_num_def, extreal_le_def])
 >> `!i x. x IN m_space m ==> 0 <= fi i x`
      by RW_TAC real_ss [Abbr ‘fi’, extreal_of_num_def,extreal_le_def]
 >> `!x. x IN m_space m ==> 0 <= f x` by METIS_TAC [le_infty]
 >> `!i. fi i IN measurable (m_space m, measurable_sets m) Borel`
      by (RW_TAC std_ss [] \\
          MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST \\
          METIS_TAC [measure_space_def])
 >> (MP_TAC o Q.SPECL [`m`,`f`,`fi`,`s`]) lebesgue_monotone_convergence_subset
 >> RW_TAC std_ss [Abbr ‘f’, Abbr ‘fi’]
 >> FULL_SIMP_TAC real_ss []
 >> RW_TAC real_ss [extreal_of_num_def, pos_fn_integral_cmul_indicator]
 >> RW_TAC std_ss [Once mul_comm]
 >> `0 <= measure m s` by METIS_TAC [MEASURE_SPACE_POSITIVE, positive_def]
 (* sup (IMAGE (\i. measure m s * Normal (&i)) UNIV (:num)) = PosInf * measure m s *)
 >> Know `!n. 0 <= Normal (&n)`
 >- (GEN_TAC >> `0 = Normal (&0)` by REWRITE_TAC [extreal_of_num_def] >> POP_ORW \\
     REWRITE_TAC [extreal_le_def] >> RW_TAC real_ss [])
 >> DISCH_TAC
 >> RW_TAC std_ss [sup_cmult]
 >> Suff `sup (IMAGE (\i. Normal (&i)) UNIV) = PosInf`
 >- METIS_TAC [mul_comm]
 >> Suff `IMAGE (\i:num. Normal (&i)) UNIV = (\x. ?n. x = &n)`
 >- RW_TAC std_ss [sup_num]
 >> RW_TAC std_ss [EXTENSION,IN_IMAGE,IN_ABS,IN_UNIV]
 >> METIS_TAC [extreal_of_num_def]
QED

(* Corollary 9.9 of [1, p.77] *)
Theorem pos_fn_integral_suminf :
    !m f. measure_space m /\
         (!i x. x IN m_space m ==> 0 <= f i x) /\
         (!i. f i IN measurable (m_space m,measurable_sets m) Borel) ==>
         (pos_fn_integral m (\x. suminf (\i. f i x)) =
          suminf (\i. pos_fn_integral m (f i)))
Proof
    rpt STRIP_TAC
 >> Know `!n. 0 <= (\i. pos_fn_integral m (f i)) n`
 >- (RW_TAC std_ss [] \\
     MATCH_MP_TAC pos_fn_integral_pos >> art [])
 >> DISCH_THEN (MP_TAC o (MATCH_MP ext_suminf_def)) >> Rewr'
 >> Know `!x. x IN m_space m ==>
              suminf (\i. f i x) =
              sup (IMAGE (\n. SIGMA (\i. f i x) (count n)) UNIV)`
 >- (rpt STRIP_TAC >> MATCH_MP_TAC ext_suminf_def \\
     RW_TAC std_ss []) >> DISCH_TAC
 >> Know ‘pos_fn_integral m (\x. suminf (\i. f i x)) =
          pos_fn_integral m (\x. sup (IMAGE (\n. SIGMA (\i. f i x) (count n)) UNIV))’
 >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
     rpt STRIP_TAC >> RW_TAC std_ss [le_sup', IN_IMAGE, IN_UNIV] \\
     POP_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘0’ >> rw [EXTREAL_SUM_IMAGE_EMPTY]) >> Rewr'
 >> Know `!n. SIGMA (\i. pos_fn_integral m (f i)) (count n) =
              pos_fn_integral m (\x. SIGMA (\i. f i x) (count n))`
 >- (GEN_TAC >> MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC pos_fn_integral_sum >> rw [FINITE_COUNT]) >> Rewr'
 >> `(\n. pos_fn_integral m (\x. SIGMA (\i. f i x) (count n))) =
     (\n. pos_fn_integral m ((\n. (\x. SIGMA (\i. f i x) (count n))) n))`
      by METIS_TAC [] >> POP_ORW
 >> MATCH_MP_TAC lebesgue_monotone_convergence >> simp []
 >> CONJ_TAC
 >- (GEN_TAC \\
     MATCH_MP_TAC (INST_TYPE [beta |-> ``:num``] IN_MEASURABLE_BOREL_SUM) \\
     qexistsl_tac [`f`, `count i`] >> rw [FINITE_COUNT] \\
     METIS_TAC [lt_infty, lte_trans, num_not_infty])
 >> CONJ_TAC >- RW_TAC std_ss [FINITE_COUNT, EXTREAL_SUM_IMAGE_POS]
 >> RW_TAC std_ss [ext_mono_increasing_def]
 >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET
 >> RW_TAC std_ss [FINITE_COUNT, SUBSET_DEF, IN_COUNT]
 >> DECIDE_TAC
QED

(* added ‘x IN m_space m’, changed quantifiers' order *)
Theorem pos_fn_integral_null_set : (* was: positive_integral_null_set *)
    !m f N. measure_space m /\
           (!x. x IN m_space m ==> 0 <= f x) /\ N IN null_set m ==>
           (pos_fn_integral m (\x. f x * indicator_fn N x) = 0)
Proof
    RW_TAC std_ss [null_sets, GSPECIFICATION]
 >> Suff `pos_fn_integral m (\x. f x * indicator_fn N x) =
          pos_fn_integral m (\x. 0)`
 >- METIS_TAC [pos_fn_integral_zero]
 >> `!x. x IN m_space m ==> 0 <= f x * indicator_fn N x`
       by (rpt STRIP_TAC \\
           MATCH_MP_TAC le_mul >> ASM_SIMP_TAC std_ss [INDICATOR_FN_POS])
 >> SIMP_TAC std_ss [GSYM le_antisym]
 >> CONJ_TAC
 >- (MATCH_MP_TAC pos_fn_integral_mono_AE \\
     ASM_SIMP_TAC std_ss [le_refl] \\
     SIMP_TAC std_ss [AE_ALT, GSPECIFICATION] \\
     Q.EXISTS_TAC `N` \\
     ASM_SIMP_TAC std_ss [GSYM IN_NULL_SET, null_sets, GSPECIFICATION, SUBSET_DEF] \\
     GEN_TAC >> STRIP_TAC >> POP_ASSUM MP_TAC \\
     ONCE_REWRITE_TAC [MONO_NOT_EQ] >> SIMP_TAC std_ss [indicator_fn_def] \\
     SIMP_TAC std_ss [mul_rzero, le_refl])
 >> MATCH_MP_TAC pos_fn_integral_mono
 >> ASM_SIMP_TAC std_ss [le_refl]
QED

(* key result *)
Theorem lebesgue_monotone_convergence_AE :
    !m f fi. measure_space m /\
        (!i. fi i IN measurable (m_space m,measurable_sets m) Borel) /\
        (AE x::m. !i. fi i x <= fi (SUC i) x /\ 0 <= fi i x) /\
        (!x. x IN m_space m ==> (sup (IMAGE (\i. fi i x) univ(:num)) = f x)) ==>
        (pos_fn_integral m (fn_plus f) =
         sup (IMAGE (\i. pos_fn_integral m (fn_plus (fi i))) univ(:num)))
Proof
    RW_TAC std_ss [FN_PLUS_ALT']
 >> ‘sigma_algebra (measurable_space m)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
 >> FULL_SIMP_TAC std_ss [AE_ALT, GSPECIFICATION]
 >> Q.ABBREV_TAC `ff = (\i x. if x IN m_space m DIFF N then fi i x else 0)`
 >> Know `AE x::m. !i. ff i x = fi i x`
 >- (MATCH_MP_TAC
       (SIMP_RULE std_ss [AND_IMP_INTRO]
          (Q.SPECL [`N`, `m`, `\x. !i. ff i x = fi i x`] AE_I)) \\
     Q.UNABBREV_TAC `ff` \\
     ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_DIFF] \\
     GEN_TAC THEN REWRITE_TAC [GSYM AND_IMP_INTRO] >> DISCH_TAC \\
     ASM_REWRITE_TAC [] >> ASM_CASES_TAC ``x NOTIN N`` >> METIS_TAC [])
 >> DISCH_TAC
 >> Know `pos_fn_integral m (\x. max 0 (f x)) =
          pos_fn_integral m (\x. max 0 (sup (IMAGE (\i. ff i x) univ(:num))))`
 >- (MATCH_MP_TAC pos_fn_integral_cong_AE >> ASM_SIMP_TAC std_ss [le_max1] \\
     FULL_SIMP_TAC std_ss [GSPECIFICATION, AE_ALT] \\
     Q.EXISTS_TAC `N'` >> Q.UNABBREV_TAC `ff` \\
     FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] \\
     RW_TAC std_ss [] >> FIRST_X_ASSUM MATCH_MP_TAC \\
     ASM_SIMP_TAC std_ss [] >> POP_ASSUM MP_TAC \\
     ONCE_REWRITE_TAC [MONO_NOT_EQ] >> RW_TAC std_ss [])
 >> DISC_RW_KILL
 >> Know `pos_fn_integral m (\x. max 0 (sup (IMAGE (\i. ff i x) univ(:num)))) =
          sup (IMAGE (\i. pos_fn_integral m ((\i x. max 0 (ff i x)) i)) univ(:num))`
 >- (MATCH_MP_TAC lebesgue_monotone_convergence \\
     ASM_SIMP_TAC std_ss [le_max1] \\
    `(\x. 0) IN measurable (m_space m,measurable_sets m) Borel`
        by (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST \\
            METIS_TAC [measure_space_def]) \\
     CONJ_TAC
     >- (GEN_TAC \\
         ONCE_REWRITE_TAC [METIS []
           ``!x. (\x. max 0 (ff i x)) = (\x. max ((\x. 0) x) ((\x. ff i x) x))``] \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX >> Q.UNABBREV_TAC `ff` \\
         FULL_SIMP_TAC std_ss [measure_space_def] \\
         KNOW_TAC ``Borel = (m_space (space Borel, subsets Borel, (\x. 0)),
                             measurable_sets (space Borel, subsets Borel, (\x. 0)))`` >|
         [SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
          DISC_RW_KILL] \\
         Suff `(\x. if x IN m_space m DIFF N then fi i x else 0) =
               (\x. if (\x. x IN m_space m DIFF N) x then (\x. fi i x) x else (\x. 0) x)` >|
         [DISC_RW_KILL, SIMP_TAC std_ss []] \\
         MATCH_MP_TAC MEASURABLE_IF \\
         ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE, measure_space_def] \\
         CONJ_TAC >|
         [ ONCE_REWRITE_TAC [METIS [ETA_AX] ``(\x. fi i x) = fi i``] \\
           ASM_SIMP_TAC std_ss [], ALL_TAC ] \\
         ONCE_REWRITE_TAC [METIS [subsets_def]
           ``measurable_sets m = subsets (m_space m, measurable_sets m)``] \\
        `{x | x IN m_space m /\ x IN m_space m DIFF N} = m_space m DIFF N` by SET_TAC [] \\
         POP_ASSUM (fn th => REWRITE_TAC [th, SIGMA_ALGEBRA_BOREL]) \\
         MATCH_MP_TAC SIGMA_ALGEBRA_DIFF \\
         FULL_SIMP_TAC std_ss [subsets_def, GSYM IN_NULL_SET, null_sets, GSPECIFICATION] \\
         METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE, measure_space_def]) \\
     CONJ_TAC
     >- (rpt STRIP_TAC \\
         Q.UNABBREV_TAC `ff` >> SIMP_TAC std_ss [ext_mono_increasing_def] \\
         RW_TAC std_ss [] >> MATCH_MP_TAC max_le2_imp >> SIMP_TAC std_ss [le_refl] \\
         POP_ASSUM MP_TAC \\
         UNDISCH_TAC ``{x | x IN m_space m /\
                            ?i. ~(fi i x <= fi (SUC i) x) \/ ~(0 <= fi i x)} SUBSET N`` \\
         FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_DIFF] \\
         DISCH_THEN (MP_TAC o Q.SPEC `x`) >> FULL_SIMP_TAC std_ss [] \\
         DISCH_TAC >> Induct_on `i'` >> ASM_SIMP_TAC std_ss [le_refl] \\
         ASM_CASES_TAC ``i = SUC i'`` >> ASM_SIMP_TAC std_ss [le_refl] \\
         DISCH_TAC >> MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `fi i' x` \\
         ASM_SIMP_TAC std_ss [] >> FIRST_X_ASSUM MATCH_MP_TAC \\
         ASM_SIMP_TAC arith_ss []) \\
     rpt STRIP_TAC \\
     Suff `!i:num. 0 <= ff i x` >|
     [ (* goal 1 (of 2) *)
       RW_TAC std_ss [extreal_max_def] THEN
       UNDISCH_TAC ``~(0 <= sup (IMAGE (\i. ff i x) univ(:num)))`` THEN
       ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THEN
       ASM_CASES_TAC ``!i:num. ff i x = 0`` THENL
       [ASM_SIMP_TAC std_ss [IMAGE_DEF, IN_UNIV] THEN
        ONCE_REWRITE_TAC [SET_RULE ``{0 | i | T} = {0}``] THEN
        SIMP_TAC std_ss [sup_sing, le_refl],
        ALL_TAC] THEN
       SIMP_TAC std_ss [le_lt] THEN DISJ1_TAC THEN
       SIMP_TAC std_ss [GSYM sup_lt] THEN FULL_SIMP_TAC std_ss [] THEN
       Q.EXISTS_TAC `ff i x` THEN CONJ_TAC THENL [ALL_TAC, METIS_TAC [le_lt]] THEN
       ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SET_TAC [],
       (* goal 2 (of 2) *)
       Q.UNABBREV_TAC `ff` THEN SIMP_TAC std_ss [] ] \\

     GEN_TAC >> ASM_CASES_TAC ``x IN m_space m DIFF N`` \\
     ASM_SIMP_TAC std_ss [le_refl] \\
     UNDISCH_TAC ``{x | x IN m_space m /\
                        ?i. ~(fi i x <= fi (SUC i) x) \/ ~(0 <= fi i x)} SUBSET N`` \\
     ONCE_REWRITE_TAC [MONO_NOT_EQ] >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION] \\
     METIS_TAC [IN_DIFF])
 >> DISC_RW_KILL
 >> AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >> ABS_TAC
 >> SIMP_TAC std_ss []
 >> MATCH_MP_TAC pos_fn_integral_cong_AE
 >> FULL_SIMP_TAC std_ss [le_max1, AE_ALT, GSPECIFICATION]
 >> Q.EXISTS_TAC `N'` >> FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION]
 >> RW_TAC std_ss [] >> FIRST_X_ASSUM MATCH_MP_TAC
 >> METIS_TAC []
QED

(* ------------------------------------------------------------------------- *)
(* Integral for arbitrary functions                                          *)
(* ------------------------------------------------------------------------- *)

(* added ‘x IN m_space m’ *)
Theorem integral_pos_fn :
    !m f. measure_space m /\ (!x. x IN m_space m ==> 0 <= f x) ==>
          (integral m f = pos_fn_integral m f)
Proof
    RW_TAC std_ss [integral_def]
 >> Know ‘pos_fn_integral m (fn_minus f) = pos_fn_integral m (\x. 0)’
 >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [FN_MINUS_POS] \\
     RW_TAC std_ss [fn_minus_def, GSYM le_antisym, le_refl] >|
     [ Suff ‘0 <= f x’ >- METIS_TAC [le_neg, neg_0] \\
       FIRST_X_ASSUM MATCH_MP_TAC >> art [],
       Suff ‘f x <= 0’ >- METIS_TAC [le_neg, neg_0] \\
       MATCH_MP_TAC lt_imp_le >> art [] ]) >> Rewr'
 >> simp [pos_fn_integral_zero, sub_rzero]
 >> MATCH_MP_TAC pos_fn_integral_cong >> simp []
QED

(* added ‘x IN m_space m’ *)
Theorem integral_pos :
    !m f. measure_space m /\ (!x. x IN m_space m ==> 0 <= f x) ==> 0 <= integral m f
Proof
    rpt STRIP_TAC
 >> Know `integral m f = pos_fn_integral m f`
 >- (MATCH_MP_TAC integral_pos_fn >> art []) >> Rewr'
 >> MATCH_MP_TAC pos_fn_integral_pos >> art []
QED

Theorem integral_neg :
    !m f. measure_space m /\ (!x. x IN m_space m ==> f x <= 0) ==> integral m f <= 0
Proof
    rw [integral_def]
 >> Know ‘pos_fn_integral m (fn_plus f) = pos_fn_integral m (\x. 0)’
 >- (MATCH_MP_TAC pos_fn_integral_cong \\
     rw [FN_PLUS_POS] \\
     MATCH_MP_TAC FN_PLUS_REDUCE' \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> Rewr'
 >> rw [pos_fn_integral_zero]
 >> REWRITE_TAC [Once (GSYM le_neg), neg_0, neg_neg]
 >> MATCH_MP_TAC pos_fn_integral_pos >> rw [FN_MINUS_POS]
QED

Theorem integral_abs_pos_fn :
    !m f. measure_space m ==> (integral m (abs o f) = pos_fn_integral m (abs o f))
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [`m`, `abs o f`] integral_pos_fn)
 >> RW_TAC std_ss [o_DEF, abs_pos]
QED

(* added ‘x IN m_space m’ *)
Theorem integral_split :
    !m f s. measure_space m /\ s IN measurable_sets m /\
           (!x. x IN m_space m ==> 0 <= f x) /\
            f IN measurable (m_space m,measurable_sets m) Borel ==>
           (integral m f = integral m (\x. f x * indicator_fn s x) +
                           integral m (\x. f x * indicator_fn (m_space m DIFF s) x))
Proof
    rpt STRIP_TAC
 >> Know `!s x. x IN m_space m ==> 0 <= (\x. f x * indicator_fn s x) x`
 >- (RW_TAC std_ss [] \\
     MATCH_MP_TAC le_mul >> art [INDICATOR_FN_POS] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> DISCH_TAC
 >> ASM_SIMP_TAC std_ss [integral_pos_fn]
 >> Know    `integral m (\x. f x * indicator_fn s x) =
      pos_fn_integral m (\x. f x * indicator_fn s x)`
 >- (MATCH_MP_TAC integral_pos_fn >> art []) >> Rewr'
 >> Know    `integral m (\x. f x * indicator_fn (m_space m DIFF s) x) =
      pos_fn_integral m (\x. f x * indicator_fn (m_space m DIFF s) x)`
 >- (MATCH_MP_TAC integral_pos_fn >> art []) >> Rewr'
 >> MATCH_MP_TAC pos_fn_integral_split >> art []
QED

(* removed ‘!x. x IN m_space m ==> 0 <= f x’, added ‘integrable m f’ *)
Theorem integral_split' :
    !m f s. measure_space m /\ integrable m f /\ s IN measurable_sets m ==>
           (integral m f = integral m (\x. f x * indicator_fn s x) +
                           integral m (\x. f x * indicator_fn (m_space m DIFF s) x))
Proof
    RW_TAC std_ss [integrable_def, integral_def,
                   fn_plus_mul_indicator, fn_minus_mul_indicator]
 >> ‘sigma_algebra (measurable_space m)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
 >> Know ‘pos_fn_integral m (fn_plus f) =
          pos_fn_integral m (\x. fn_plus f x * indicator_fn s x) +
          pos_fn_integral m (\x. fn_plus f x * indicator_fn (m_space m DIFF s) x)’
 >- (MATCH_MP_TAC pos_fn_integral_split >> rw [FN_PLUS_POS] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_FN_PLUS >> art []) >> Rewr'
 >> Know ‘pos_fn_integral m (fn_minus f) =
          pos_fn_integral m (\x. fn_minus f x * indicator_fn s x) +
          pos_fn_integral m (\x. fn_minus f x * indicator_fn (m_space m DIFF s) x)’
 >- (MATCH_MP_TAC pos_fn_integral_split >> rw [FN_MINUS_POS] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_FN_MINUS >> art []) >> Rewr'
 >> Q.ABBREV_TAC ‘A = pos_fn_integral m (\x. fn_plus f x * indicator_fn s x)’
 >> Q.ABBREV_TAC ‘B = pos_fn_integral m (\x. fn_minus f x * indicator_fn s x)’
 >> Q.ABBREV_TAC ‘C = pos_fn_integral m (\x. fn_plus f x * indicator_fn (m_space m DIFF s) x)’
 >> Q.ABBREV_TAC ‘D = pos_fn_integral m (\x. fn_minus f x * indicator_fn (m_space m DIFF s) x)’
 >> Know ‘A <> PosInf /\ C <> PosInf’
 >- (fs [Abbr ‘A’, Abbr ‘C’, lt_infty] \\
     CONJ_TAC \\
     ( MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘pos_fn_integral m (fn_plus f)’ >> art [] \\
       MATCH_MP_TAC pos_fn_integral_mono \\
       rw [] >- (MATCH_MP_TAC le_mul >> rw [FN_PLUS_POS, INDICATOR_FN_POS]) \\
      ‘fn_plus f x = fn_plus f x * 1’ by PROVE_TAC [mul_rone] \\
       POP_ASSUM ((GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites) o wrap) \\
       MATCH_MP_TAC le_lmul_imp >> rw [FN_PLUS_POS, INDICATOR_FN_LE_1] )) >> STRIP_TAC
 >> Know ‘B <> PosInf /\ D <> PosInf’
 >- (fs [Abbr ‘B’, Abbr ‘D’, lt_infty] \\
     CONJ_TAC \\
     ( MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘pos_fn_integral m (fn_minus f)’ >> art [] \\
       MATCH_MP_TAC pos_fn_integral_mono \\
       rw [] >- (MATCH_MP_TAC le_mul >> rw [FN_MINUS_POS, INDICATOR_FN_POS]) \\
      ‘fn_minus f x = fn_minus f x * 1’ by PROVE_TAC [mul_rone] \\
       POP_ASSUM ((GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites) o wrap) \\
       MATCH_MP_TAC le_lmul_imp >> rw [FN_MINUS_POS, INDICATOR_FN_LE_1] )) >> STRIP_TAC
 >> Know ‘A <> NegInf’
 >- (MATCH_MP_TAC pos_not_neginf >> Q.UNABBREV_TAC ‘A’ \\
     MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
     MATCH_MP_TAC le_mul >> rw [FN_PLUS_POS, INDICATOR_FN_POS]) >> DISCH_TAC
 >> Know ‘C <> NegInf’
 >- (MATCH_MP_TAC pos_not_neginf >> Q.UNABBREV_TAC ‘C’ \\
     MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
     MATCH_MP_TAC le_mul >> rw [FN_PLUS_POS, INDICATOR_FN_POS]) >> DISCH_TAC
 >> Know ‘B <> NegInf’
 >- (MATCH_MP_TAC pos_not_neginf >> Q.UNABBREV_TAC ‘B’ \\
     MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
     MATCH_MP_TAC le_mul >> rw [FN_MINUS_POS, INDICATOR_FN_POS]) >> DISCH_TAC
 >> Know ‘D <> NegInf’
 >- (MATCH_MP_TAC pos_not_neginf >> Q.UNABBREV_TAC ‘D’ \\
     MATCH_MP_TAC pos_fn_integral_pos >> rw [] \\
     MATCH_MP_TAC le_mul >> rw [FN_MINUS_POS, INDICATOR_FN_POS]) >> DISCH_TAC
 >> ‘?a. A = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> ‘?b. B = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> ‘?c. C = Normal c’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> ‘?d. D = Normal d’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> REWRITE_TAC [extreal_add_def, extreal_sub_def, extreal_11]
 >> REAL_ARITH_TAC
QED

(* ------------------------------------------------------------------------- *)
(* Properties of integrable functions                                        *)
(* ------------------------------------------------------------------------- *)

Theorem integrable_eq :
    !m f g. measure_space m /\ integrable m f /\
            (!x. x IN m_space m ==> (f x = g x)) ==> integrable m g
Proof
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
      ASM_REWRITE_TAC [] ]
QED

Theorem integrable_cong :
    !m f g. measure_space m /\ (!x. x IN m_space m ==> (f x = g x)) ==>
           (integrable m f <=> integrable m g)
Proof
    rpt STRIP_TAC
 >> EQ_TAC >> STRIP_TAC
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC integrable_eq >> Q.EXISTS_TAC ‘f’ >> art [],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC integrable_eq >> Q.EXISTS_TAC ‘g’ >> rw [] ]
QED

(* added ‘x IN m_space m’ *)
Theorem integrable_pos :
    !m f. measure_space m /\ (!x. x IN m_space m ==> 0 <= f x) ==>
         (integrable m f <=> f IN measurable (m_space m,measurable_sets m) Borel /\
                             pos_fn_integral m f <> PosInf)
Proof
    RW_TAC std_ss [integrable_def, GSYM fn_plus_def, GSYM fn_minus_def,
                   pos_fn_integral_zero, num_not_infty]
 >> Know ‘pos_fn_integral m (fn_plus f) = pos_fn_integral m f’
 >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [FN_PLUS_POS] \\
     rpt STRIP_TAC >> rw []) >> Rewr'
 >> Know ‘pos_fn_integral m (fn_minus f) = pos_fn_integral m (\x. 0)’
 >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [FN_MINUS_POS] \\
     rpt STRIP_TAC >> rw []) >> Rewr'
 >> rw [pos_fn_integral_zero]
QED

val integrable_infty = store_thm
  ("integrable_infty",
  ``!m f s. measure_space m /\ integrable m f /\ s IN measurable_sets m /\
           (!x. x IN s ==> (f x = PosInf)) ==> (measure m s = 0)``,
  RW_TAC std_ss [integrable_def]
  >> ‘sigma_algebra (measurable_space m)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
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

Theorem integrable_infty_null :
    !m f. measure_space m /\ integrable m f ==>
          null_set m {x | x IN m_space m /\ (f x = PosInf)}
Proof
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
 >> MP_TAC (Q.SPECL [`f`,`(m_space m, measurable_sets m)`] IN_MEASURABLE_BOREL_ALT8)
 >> rw [MEASURE_SPACE_SIGMA_ALGEBRA]
 >> POP_ASSUM (MP_TAC o (Q.SPEC `PosInf`))
 >> Suff `s = {x | f x = PosInf} INTER m_space m`
 >- METIS_TAC []
 >> Q.UNABBREV_TAC `s`
 >> RW_TAC std_ss [EXTENSION,IN_INTER,GSPECIFICATION]
 >> METIS_TAC []
QED

Theorem pos_fn_integral_infty_null :
    !m f. measure_space m /\ (!x. x IN m_space m ==> 0 <= f x) /\
          f IN measurable (m_space m,measurable_sets m) Borel /\
          pos_fn_integral m f <> PosInf ==>
          null_set m {x | x IN m_space m /\ (f x = PosInf)}
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC integrable_infty_null
 >> simp [integrable_def]
 >> CONJ_TAC
 >- (Suff ‘pos_fn_integral m (fn_plus f) = pos_fn_integral m f’ >- rw [] \\
     MATCH_MP_TAC pos_fn_integral_cong >> rw [])
 >> Suff ‘pos_fn_integral m (fn_minus f) = pos_fn_integral m (\x. 0)’
 >- rw [pos_fn_integral_zero]
 >> MATCH_MP_TAC pos_fn_integral_cong >> rw []
QED

(* The need of complete measure space comes from IN_MEASURABLE_BOREL_AE_EQ

   NOTE: In general (unless the measure space is complete), a function g may not
   be integrable, when it is almost everywhere equal to an integrable function f.
 *)
Theorem integrable_eq_AE :
    !m f g. complete_measure_space m /\
            integrable m f /\ (AE x::m. f x = g x) ==> integrable m g
Proof
    rw [integrable_def]
 >| [ (* goal 1 (of 3) *)
      MATCH_MP_TAC IN_MEASURABLE_BOREL_AE_EQ \\
      Q.EXISTS_TAC ‘f’ >> art [],
      (* goal 2 (of 3) *)
      Suff ‘pos_fn_integral m (fn_plus f) = pos_fn_integral m (fn_plus g)’
      >- (DISCH_THEN (fs o wrap)) \\
      MATCH_MP_TAC pos_fn_integral_cong_AE \\
      fs [complete_measure_space_def, FN_PLUS_POS] \\
      fs [AE_DEF] \\
      Q.EXISTS_TAC ‘N’ >> rw [] \\
     ‘f x = g x’ by PROVE_TAC [] \\
      RW_TAC std_ss [fn_plus_def],
      (* goal 3 (of 3) *)
      Suff ‘pos_fn_integral m (fn_minus f) = pos_fn_integral m (fn_minus g)’
      >- (DISCH_THEN (fs o wrap)) \\
      MATCH_MP_TAC pos_fn_integral_cong_AE \\
      fs [complete_measure_space_def, FN_MINUS_POS] \\
      fs [AE_DEF] \\
      Q.EXISTS_TAC ‘N’ >> rw [] \\
     ‘f x = g x’ by PROVE_TAC [] \\
      RW_TAC std_ss [fn_minus_def] ]
QED

(* Corollary 11.6 [1, p.91] (partial)

   FIXME: extend it to NegInf, so that f is almost everywhere R-valued.
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

(* Updated with ‘!x. x IN m_space m ==> (abs (g x) <= f x)’ *)
Theorem integrable_bounded :
    !m f g. measure_space m /\ integrable m f /\
            g IN measurable (m_space m,measurable_sets m) Borel /\
            (!x. x IN m_space m ==> (abs (g x) <= f x))
        ==> integrable m g
Proof
    RW_TAC std_ss [integrable_def, abs_bounds, GSYM fn_plus_def, GSYM fn_minus_def]
 >- (`!x. x IN m_space m ==> fn_plus g x <= fn_plus f x`
       by (RW_TAC real_ss [fn_plus_def, lt_imp_le, le_refl] \\
           METIS_TAC [extreal_lt_def, lte_trans]) \\
     METIS_TAC [pos_fn_integral_mono, FN_PLUS_POS, lt_infty, let_trans])
 >> `!x. x IN m_space m ==> fn_minus g x <= fn_plus f x`
        by (RW_TAC real_ss [fn_minus_def, fn_plus_def, lt_imp_le, le_refl] \\
            METIS_TAC [let_trans, lt_neg, le_neg, neg_neg, neg_0])
 >> METIS_TAC [pos_fn_integral_mono, FN_PLUS_POS, FN_MINUS_POS, lt_infty, let_trans]
QED

Theorem integrable_fn_plus :
    !m f. measure_space m /\ integrable m f ==> integrable m (fn_plus f)
Proof
    rpt STRIP_TAC >> POP_ASSUM MP_TAC
 >> ‘sigma_algebra (measurable_space m)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
 >> RW_TAC std_ss [integrable_def, GSYM fn_plus_def, FN_PLUS_POS, FN_PLUS_POS_ID,
                   IN_MEASURABLE_BOREL_FN_PLUS, GSYM fn_minus_def, FN_MINUS_POS_ZERO,
                   pos_fn_integral_zero, num_not_infty]
QED

Theorem integrable_fn_minus :
    !m f. measure_space m /\ integrable m f ==> integrable m (fn_minus f)
Proof
    rpt STRIP_TAC >> POP_ASSUM MP_TAC
 >> ‘sigma_algebra (measurable_space m)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
 >> RW_TAC std_ss [integrable_def, GSYM fn_minus_def, FN_MINUS_POS, FN_PLUS_POS_ID,
                   IN_MEASURABLE_BOREL_FN_MINUS, GSYM fn_plus_def, FN_MINUS_POS_ZERO,
                   pos_fn_integral_zero, num_not_infty]
QED

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
Theorem integrable_plus_minus :
    !m f. measure_space m ==>
         (integrable m f <=> f IN measurable (m_space m, measurable_sets m) Borel /\
                             integrable m (fn_plus f) /\ integrable m (fn_minus f))
Proof
    rpt STRIP_TAC
 >> ‘sigma_algebra (measurable_space m)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
 >> RW_TAC std_ss [integrable_def, GSYM fn_plus_def, GSYM fn_minus_def]
 >> `fn_plus (fn_minus f) = fn_minus f` by METIS_TAC [FN_MINUS_POS, FN_PLUS_POS_ID]
 >> `fn_minus (fn_minus f) = (\x. 0)` by METIS_TAC [FN_MINUS_POS, FN_MINUS_POS_ZERO]
 >> `fn_plus (fn_plus f) = fn_plus f` by METIS_TAC [FN_PLUS_POS, FN_PLUS_POS_ID]
 >> `fn_minus (fn_plus f) = (\x. 0)` by METIS_TAC [FN_PLUS_POS, FN_MINUS_POS_ZERO]
 >> `(\x. fn_minus f x) = fn_minus f` by METIS_TAC []
 >> `(\x. fn_plus f x) = fn_plus f` by METIS_TAC []
 >> EQ_TAC
 >> RW_TAC std_ss [IN_MEASURABLE_BOREL_FN_PLUS, IN_MEASURABLE_BOREL_FN_MINUS,
                   pos_fn_integral_zero, num_not_infty]
QED

(* added ‘x IN m_space m’ *)
Theorem integrable_add_pos :
    !m f g. measure_space m /\ integrable m f /\ integrable m g /\
           (!x. x IN m_space m ==> 0 <= f x) /\
           (!x. x IN m_space m ==> 0 <= g x) ==> integrable m (\x. f x + g x)
Proof
    rpt STRIP_TAC
 >> ‘sigma_algebra (measurable_space m)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
 >> RW_TAC std_ss []
 >> `!x. x IN m_space m ==> 0 <= (\x. f x + g x) x` by RW_TAC real_ss [le_add]
 >> `f IN measurable (m_space m,measurable_sets m) Borel` by METIS_TAC [integrable_def]
 >> `g IN measurable (m_space m,measurable_sets m) Borel` by METIS_TAC [integrable_def]
 >> Know `(\x. f x + g x) IN measurable (m_space m,measurable_sets m) Borel`
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD \\
     qexistsl_tac [`f`, `g`] >> fs [measure_space_def] \\
     GEN_TAC >> DISCH_TAC >> DISJ1_TAC \\
     CONJ_TAC >> (MATCH_MP_TAC pos_not_neginf >> simp []))
 >> DISCH_TAC
 >> Suff `pos_fn_integral m (\x. f x + g x) <> PosInf`
 >- FULL_SIMP_TAC std_ss [integrable_pos]
 >> RW_TAC std_ss [pos_fn_integral_add]
 >> METIS_TAC [lt_add2, integrable_pos, lt_infty]
QED

(* alternative definition of ‘integrable m (abs o f)’ w/o fn_plus, fn_minus *)
Theorem integrable_abs_alt :
    !m f. measure_space m /\ f IN Borel_measurable (measurable_space m) ==>
         (integrable m (abs o f) <=> pos_fn_integral m (abs o f) <> PosInf)
Proof
    rw [integrable_def, fn_plus_abs, fn_minus_abs, pos_fn_integral_zero]
 >> EQ_TAC >> rw []
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS'
 >> rw [SIGMA_ALGEBRA_BOREL]
QED

(* Theorem 10.3 (i) => (iii) [1, p.84], cf. integrable_from_abs *)
Theorem integrable_abs :
    !m f. measure_space m /\ integrable m f ==> integrable m (abs o f)
Proof
    RW_TAC std_ss [FN_ABS']
 >> MATCH_MP_TAC integrable_add_pos
 >> ASM_REWRITE_TAC [FN_PLUS_POS, FN_MINUS_POS]
 >> CONJ_TAC >- (MATCH_MP_TAC integrable_fn_plus >> art [])
 >> MATCH_MP_TAC integrable_fn_minus >> art []
QED

(* Theorem 10.3 (ii) => (iii) [1, p.84] *)
Theorem integrable_abs_bound_exists :
    !m u. measure_space m /\ integrable m (abs o u) ==>
          ?w. integrable m w /\ (!x. x IN m_space m ==> 0 <= w x) /\
              !x. x IN m_space m ==> abs (u x) <= w x
Proof
    rpt STRIP_TAC
 >> Q.EXISTS_TAC `abs o u`
 >> RW_TAC std_ss [o_DEF, le_refl, abs_pos]
QED

(* Theorem 10.3 (i) => (iv) [1, p.84] *)
Theorem integrable_bound_exists :
    !m u. measure_space m /\ integrable m u ==>
          ?w. integrable m w /\ (!x. x IN m_space m ==> 0 <= w x) /\
              !x. x IN m_space m ==> abs (u x) <= w x
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC integrable_abs_bound_exists >> art []
 >> MATCH_MP_TAC integrable_abs >> art []
QED

(* Theorem 10.3 (iv) => (i) [1, p.84] *)
Theorem integrable_from_bound_exists :
    !m u. measure_space m /\
          u IN measurable (m_space m,measurable_sets m) Borel /\
          (?w. integrable m w /\
               (!x. x IN m_space m ==> 0 <= w x) /\
               (!x. x IN m_space m ==> abs (u x) <= w x)) ==> integrable m u
Proof
    RW_TAC std_ss [integrable_def, lt_infty] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC let_trans \\
      Q.EXISTS_TAC `pos_fn_integral m w` \\
      Suff ‘pos_fn_integral m w = pos_fn_integral m (fn_plus w)’
      >- (Rewr' >> art [] \\
          MATCH_MP_TAC pos_fn_integral_mono >> rw [FN_PLUS_POS] \\
          MATCH_MP_TAC le_trans \\
          Q.EXISTS_TAC `abs (u x)` >> simp [] \\
          REWRITE_TAC [FN_PLUS_LE_ABS]) \\
      MATCH_MP_TAC pos_fn_integral_cong >> rw [],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC let_trans \\
      Q.EXISTS_TAC `pos_fn_integral m w` \\
      Suff ‘pos_fn_integral m w = pos_fn_integral m (fn_plus w)’
      >- (Rewr' >> art [] \\
          MATCH_MP_TAC pos_fn_integral_mono >> rw [FN_MINUS_POS] \\
          MATCH_MP_TAC le_trans \\
          Q.EXISTS_TAC `abs (u x)` >> simp [] \\
          REWRITE_TAC [FN_MINUS_LE_ABS]) \\
      MATCH_MP_TAC pos_fn_integral_cong >> rw [] ]
QED

(* Theorem 10.3 (iii) => (i) [1, p.84]

   NOTE: (abs o f)-measurability doesn't imply f-measurablity in general.
 *)
Theorem integrable_from_abs :
    !m u. measure_space m /\ u IN measurable (m_space m,measurable_sets m) Borel /\
          integrable m (abs o u) ==> integrable m u
Proof
    RW_TAC std_ss []
 >> MATCH_MP_TAC integrable_from_bound_exists >> art []
 >> MATCH_MP_TAC integrable_abs_bound_exists >> art []
QED

Theorem integral_abs_imp_integrable :
    !m f. measure_space m /\ f IN measurable (m_space m,measurable_sets m) Borel /\
         (integral m (abs o f) = 0) ==> integrable m f
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC integrable_from_abs >> art []
 >> `sigma_algebra (m_space m,measurable_sets m)` by METIS_TAC [measure_space_def]
 >> `abs o f IN measurable (m_space m,measurable_sets m) Borel`
      by METIS_TAC [IN_MEASURABLE_BOREL_ABS']
 >> Q.ABBREV_TAC `g = abs o f`
 >> Know `nonneg g`
 >- (Q.UNABBREV_TAC `g` >> RW_TAC std_ss [nonneg_def, abs_pos]) >> DISCH_TAC
 >> RW_TAC std_ss [integrable_def]
 >| [ (* goal 1 (of 2) *)
      Know `integral m g = pos_fn_integral m g`
      >- (MATCH_MP_TAC integral_pos_fn >> fs [nonneg_def]) \\
      DISCH_THEN ((FULL_SIMP_TAC bool_ss) o wrap) \\
      Know `fn_plus g = g`
      >- (MATCH_MP_TAC nonneg_fn_plus >> art []) \\
      RW_TAC std_ss [extreal_of_num_def, extreal_not_infty],
      (* goal 2 (of 2) *)
      Know `fn_minus g = (\x. 0)`
      >- (MATCH_MP_TAC nonneg_fn_minus >> art []) >> Rewr' \\
      ASM_SIMP_TAC std_ss [pos_fn_integral_zero] \\
      RW_TAC std_ss [extreal_of_num_def, extreal_not_infty] ]
QED

val integrable_add_lemma = store_thm
  ("integrable_add_lemma",
  ``!m f g. measure_space m /\ integrable m f /\ integrable m g
        ==> (integrable m (\x. fn_plus f x + fn_plus g x) /\
             integrable m (\x. fn_minus f x + fn_minus g x))``,
    RW_TAC std_ss []
 >> METIS_TAC [integrable_add_pos, integrable_plus_minus, FN_PLUS_POS, FN_MINUS_POS]);

(* more general antecedents, old:

           (!x. x IN m_space m ==> (f x <> NegInf /\ g x <> NegInf))

   new:

           (!x. x IN m_space m ==> (f x <> NegInf /\ g x <> NegInf) \/
                                   (f x <> PosInf /\ g x <> PosInf))
 *)
Theorem integrable_add :
    !m f g. measure_space m /\ integrable m f /\ integrable m g /\
           (!x. x IN m_space m ==> (f x <> NegInf /\ g x <> NegInf) \/
                                   (f x <> PosInf /\ g x <> PosInf))
        ==> integrable m (\x. f x + g x)
Proof
    RW_TAC std_ss []
 >> ‘sigma_algebra (measurable_space m)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
 >> Know `(\x. f x + g x) IN measurable (m_space m, measurable_sets m) Borel`
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD \\
     qexistsl_tac [`f`, `g`] >> simp [] \\
     METIS_TAC [measure_space_def, integrable_def])
 >> DISCH_TAC
 >> RW_TAC std_ss [Once integrable_plus_minus]
 >- (MATCH_MP_TAC integrable_bounded \\
     Q.EXISTS_TAC `(\x. fn_plus f x + fn_plus g x)` \\
     RW_TAC std_ss [IN_MEASURABLE_BOREL_FN_PLUS, integrable_add_lemma] \\
     METIS_TAC [abs_refl, FN_PLUS_POS, FN_PLUS_ADD_LE])
 >> MATCH_MP_TAC integrable_bounded
 >> Q.EXISTS_TAC `(\x. fn_minus f x + fn_minus g x)`
 >> RW_TAC std_ss [IN_MEASURABLE_BOREL_FN_MINUS, integrable_add_lemma]
 >> `abs (fn_minus (\x. f x + g x) x) = fn_minus (\x. f x + g x) x`
        by METIS_TAC [abs_refl, FN_MINUS_POS] >> POP_ORW
 >> MATCH_MP_TAC FN_MINUS_ADD_LE
 >> METIS_TAC []
QED

Theorem integrable_cmul :
    !m f c. measure_space m /\ integrable m f ==> integrable m (\x. Normal c * f x)
Proof
    rpt STRIP_TAC
 >> ‘sigma_algebra (measurable_space m)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
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
 >> METIS_TAC [mul_not_infty, integrable_def]
QED

Theorem integrable_ainv :
    !m f. measure_space m /\ integrable m f ==> integrable m (\x. -f x)
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [Once neg_minus1, extreal_of_num_def, extreal_ainv_def]
 >> MATCH_MP_TAC integrable_cmul >> art []
QED

(* NOTE: added `!x. x IN m_space m ==> f x <> NegInf /\ g x <> PosInf`, one way
   to make sure that `f - g` is defined (i.e. f/g cannot be the same infinites
 *)
Theorem integrable_sub :
    !m f g. measure_space m /\ integrable m f /\ integrable m g /\
            (!x. x IN m_space m ==> f x <> NegInf /\ g x <> PosInf)
        ==> integrable m (\x. f x - g x)
Proof
    rw [extreal_sub]
 >> ‘integrable m (\x. -g x)’ by METIS_TAC [integrable_ainv]
 >> HO_MATCH_MP_TAC integrable_add >> rw []
 >> Cases_on ‘g x’ >> METIS_TAC [extreal_ainv_def, extreal_distinct]
QED

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

(* deleted ‘measure m s < PosInf’ and
   deleted ‘!x. x IN m_space m ==> f x <> NegInf /\ f x <> PosInf’
 *)
Theorem integrable_mul_indicator :
    !m s f. measure_space m /\ s IN measurable_sets m /\
            integrable m f ==> integrable m (\x. f x * indicator_fn s x)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC integrable_bounded
 >> Q.EXISTS_TAC `abs o f`
 >> ASM_SIMP_TAC std_ss [o_DEF]
 >> CONJ_TAC >- (MATCH_MP_TAC (REWRITE_RULE [o_DEF] integrable_abs) >> art [])
 >> reverse CONJ_TAC
 >- (RW_TAC std_ss [] \\
     Cases_on `x IN s` >- ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rone, le_refl] \\
     ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rzero, abs_0, abs_pos])
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR
 >> fs [measure_space_def, integrable_def]
QED

(* IMPORTANT: all posinf-valued points (which forms a null set) in an integrable
   function can be safely removed without changing its overall integral.
 *)
Theorem integrable_not_infty_lemma[local] :
    !m f. measure_space m /\ integrable m f /\
         (!x. x IN m_space m ==> 0 <= f x) ==>
          ?g. integrable m g /\
             (!x. x IN m_space m ==> 0 <= g x) /\
             (!x. x IN m_space m ==> g x <> PosInf) /\
             (integral m f = integral m g)
Proof
    RW_TAC std_ss [integral_pos_fn, integrable_def]
 >> ‘sigma_algebra (measurable_space m)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
 >> Q.ABBREV_TAC `g = (\x. if f x = PosInf then 0 else f x)`
 >> Q.EXISTS_TAC `g`
 >> `!x. x IN m_space m ==> 0 <= g x` by METIS_TAC [le_refl]
 >> `!x. x IN m_space m ==> g x <= f x` by METIS_TAC [le_refl,le_infty]
 >> `!x. x IN m_space m ==> g x <> PosInf` by METIS_TAC [num_not_infty]
 >> Know `g IN measurable (m_space m,measurable_sets m) Borel`
 >- (RW_TAC std_ss [IN_MEASURABLE_BOREL, space_def, subsets_def, IN_FUNSET, IN_UNIV] \\
     Cases_on `Normal c <= 0`
     >- (`{x | g x < Normal c} INTER m_space m = {}`
            by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY, IN_INTER] \\
                METIS_TAC [le_trans, extreal_lt_def]) \\
         METIS_TAC [MEASURE_SPACE_EMPTY_MEASURABLE]) \\
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
                    IN_MEASURABLE_BOREL_ALL, integrable_def, INTER_COMM])
 >> DISCH_TAC
 >> CONJ_TAC
 >- (RW_TAC std_ss []
     >- (FULL_SIMP_TAC std_ss [lt_infty] \\
         MATCH_MP_TAC let_trans \\
         Q.EXISTS_TAC ‘pos_fn_integral m (fn_plus f)’ >> art [] \\
         MATCH_MP_TAC pos_fn_integral_mono >> rw [FN_PLUS_POS]) \\
     Know ‘pos_fn_integral m (fn_minus g) = pos_fn_integral m (\x. 0)’
     >- (MATCH_MP_TAC pos_fn_integral_cong >> rw [FN_MINUS_POS]) >> Rewr' \\
     RW_TAC std_ss [pos_fn_integral_zero, num_not_infty])
 >> RW_TAC std_ss []
 >> Q.ABBREV_TAC `h = (\x. f x - g x)`
 >> Know `!x. x IN m_space m ==> f x <> NegInf`
 >- (GEN_TAC >> DISCH_TAC >> MATCH_MP_TAC pos_not_neginf \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> DISCH_TAC
 >> Know `h IN measurable (m_space m,measurable_sets m) Borel`
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
     qexistsl_tac [‘f’, ‘g’] >> fs [measure_space_def]) >> DISCH_TAC
 >> `!x. x IN m_space m ==> 0 <= h x`
       by METIS_TAC [extreal_sub_def,le_infty,le_refl,extreal_of_num_def,sub_refl]
 >> Know `pos_fn_integral m f = pos_fn_integral m (\x. g x + h x)`
 >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
     CONJ_TAC >- (rpt STRIP_TAC >> MATCH_MP_TAC le_add >> PROVE_TAC []) \\
     rw [Abbr ‘h’] \\
     Know ‘g x + (f x - g x) = f x - g x + g x’
     >- (MATCH_MP_TAC add_comm >> DISJ1_TAC \\
         CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf >> simp []) \\
         MATCH_MP_TAC pos_not_neginf >> fs []) >> Rewr' \\
     MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC sub_add \\
     CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf >> simp []) \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> Rewr'
 >> (MP_TAC o Q.SPECL [`m`,`g`,`h`]) pos_fn_integral_add
 >> RW_TAC std_ss []
 >> Suff `pos_fn_integral m h = 0`
 >- RW_TAC std_ss [add_rzero, integral_pos_fn]
 >> POP_ASSUM K_TAC
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
 >> RW_TAC std_ss [pos_fn_integral_zero, GSYM extreal_of_num_def, mul_rzero, add_rzero]
QED

(* moved here as integrable_not_infty' needs it *)
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

Theorem integral_cong : (* was: integral_eq *)
    !m f g. measure_space m /\ (!x. x IN m_space m ==> (f x = g x)) ==>
           (integral m f = integral m g)
Proof
    rpt STRIP_TAC
 >> `(integral m f = integral m (\x. f x * indicator_fn (m_space m) x)) /\
     (integral m g = integral m (\x. g x * indicator_fn (m_space m) x))`
        by METIS_TAC [integral_mspace] >> art []
 >> Suff `(\x. f x * indicator_fn (m_space m) x) = (\x. g x * indicator_fn (m_space m) x)`
 >- RW_TAC std_ss []
 >> FUN_EQ_TAC >> RW_TAC std_ss [indicator_fn_def, GSPECIFICATION, mul_rzero]
QED

Theorem integral_cong_AE :
    !m f g. measure_space m /\ (AE x::m. f x = g x) ==> (integral m f = integral m g)
Proof
    rw [AE_DEF, integral_def]
 >> Suff ‘(pos_fn_integral m (fn_plus f) = pos_fn_integral m (fn_plus g)) /\
          (pos_fn_integral m (fn_minus f) = pos_fn_integral m (fn_minus g))’
 >- Rewr
 >> CONJ_TAC
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC pos_fn_integral_cong_AE \\
      rw [FN_PLUS_POS, AE_DEF] \\
      Q.EXISTS_TAC ‘N’ >> rw [FN_PLUS_ALT],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC pos_fn_integral_cong_AE \\
      rw [FN_MINUS_POS, AE_DEF] \\
      Q.EXISTS_TAC ‘N’ >> rw [FN_MINUS_ALT] ]
QED

(* furthermore, ‘x IN m_space m’ can be removed from ‘g’ *)
Theorem integrable_not_infty :
    !m f. measure_space m /\ integrable m f /\
         (!x. x IN m_space m ==> 0 <= f x) ==>
          ?g. integrable m g /\ (!x. 0 <= g x) /\ (!x. g x <> PosInf) /\
             (integral m f = integral m g)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘m’, ‘f’] integrable_not_infty_lemma)
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC ‘\x. if x IN m_space m then g x else 0’
 >> CONJ_TAC
 >- (MATCH_MP_TAC integrable_eq >> Q.EXISTS_TAC ‘g’ >> simp [])
 >> rw []
 >> MATCH_MP_TAC integral_cong >> rw []
QED

(* added ‘x IN m_space m’ *)
Theorem integrable_not_infty_alt :
    !m f. measure_space m /\ integrable m f /\
         (!x. x IN m_space m ==> 0 <= f x) ==>
          integrable m (\x. if f x = PosInf then 0 else f x) /\
         (integral m f = integral m (\x. if f x = PosInf then 0 else f x))
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘sigma_algebra (measurable_space m)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
 >> Q.ABBREV_TAC `g = (\x. if f x = PosInf then 0 else f x)`
 >> `!x. x IN m_space m ==> 0 <= g x` by METIS_TAC [le_refl]
 >> `!x. x IN m_space m ==> g x <= f x` by METIS_TAC [le_refl, le_infty]
 >> `!x. x IN m_space m ==> g x <> PosInf` by METIS_TAC [num_not_infty]
 >> `!x. x IN m_space m ==> g x <> NegInf` by METIS_TAC [lt_infty, lte_trans, num_not_infty]
 >> `!x. x IN m_space m ==> f x <> NegInf` by METIS_TAC [lt_infty, lte_trans, num_not_infty]
 >> Know `g IN measurable (m_space m,measurable_sets m) Borel`
 >- (RW_TAC std_ss [IN_MEASURABLE_BOREL, space_def, subsets_def, IN_FUNSET, IN_UNIV] \\
     Cases_on `Normal c <= 0`
     >- (`{x | g x < Normal c} INTER m_space m = {}`
            by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY, IN_INTER] \\
                METIS_TAC [le_trans, extreal_lt_def]) >> POP_ORW \\
         METIS_TAC [MEASURE_SPACE_EMPTY_MEASURABLE]) \\
    `{x | g x < Normal c} = {x | f x < Normal c} UNION {x | f x = PosInf}`
        by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_UNION] \\
            Q.UNABBREV_TAC `g` >> RW_TAC std_ss [] \\
            METIS_TAC [extreal_lt_def]) \\
     RW_TAC std_ss [Once INTER_COMM, UNION_OVER_INTER] \\
     MATCH_MP_TAC MEASURE_SPACE_UNION \\
     RW_TAC std_ss [] \\
     METIS_TAC [(REWRITE_RULE [space_def, subsets_def] o
                 Q.SPECL [`f`,`(m_space m, measurable_sets m)`])
                    IN_MEASURABLE_BOREL_ALL, integrable_def, INTER_COMM])
 >> DISCH_TAC
 >> Know `integrable m g`
 >- (RW_TAC std_ss [integrable_def, GSYM fn_plus_def, GSYM fn_minus_def]
     >- (fs [lt_infty, integrable_def, GSYM fn_plus_def] \\
         MATCH_MP_TAC let_trans \\
         Q.EXISTS_TAC ‘pos_fn_integral m (fn_plus f)’ >> art [] \\
         MATCH_MP_TAC pos_fn_integral_mono >> rw [FN_PLUS_POS]) \\
     Know ‘pos_fn_integral m (fn_minus g) = pos_fn_integral m (\x. 0)’
     >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [FN_MINUS_POS]) >> Rewr' \\
     RW_TAC std_ss [pos_fn_integral_zero, num_not_infty])
 >> RW_TAC std_ss []
 >> Q.ABBREV_TAC `h = (\x. f x - g x)`
 >> Know `h IN measurable (m_space m,measurable_sets m) Borel`
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
     qexistsl_tac [‘f’, ‘g’] >> fs [measure_space_def, integrable_def])
 >> RW_TAC std_ss [integral_pos_fn]
 >> `!x. x IN m_space m ==> 0 <= h x`
       by METIS_TAC [extreal_sub_def,le_infty,le_refl,extreal_of_num_def,sub_refl]
 >> Know `pos_fn_integral m f = pos_fn_integral m (\x. g x + h x)`
 >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
     CONJ_TAC >- (rpt STRIP_TAC >> MATCH_MP_TAC le_add >> PROVE_TAC []) \\
     rw [Abbr ‘h’] \\
     Know ‘g x + (f x - g x) = f x - g x + g x’
     >- (MATCH_MP_TAC add_comm >> DISJ1_TAC \\
         CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf >> simp []) \\
         MATCH_MP_TAC pos_not_neginf >> fs []) >> Rewr' \\
     MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC sub_add \\
     CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf >> simp []) \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> Rewr'
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
 >> RW_TAC std_ss [pos_fn_integral_zero, GSYM extreal_of_num_def, mul_rzero, add_rzero]
QED

(* added ‘x IN m_space m’ *)
Theorem integrable_not_infty_alt2 :
    !m f. measure_space m /\ integrable m f /\
         (!x. x IN m_space m ==> 0 <= f x) ==>
          integrable m (\x. if f x = PosInf then 0 else f x) /\
         (pos_fn_integral m f = pos_fn_integral m (\x. if f x = PosInf then 0 else f x))
Proof
    RW_TAC std_ss []
 >- RW_TAC std_ss [integrable_not_infty_alt]
 >> `!x. x IN m_space m ==>
         0 <= (\x. if f x = PosInf then 0 else f x) x` by METIS_TAC [le_refl]
 >> FULL_SIMP_TAC std_ss [GSYM integral_pos_fn]
 >> METIS_TAC [integrable_not_infty_alt]
QED

Theorem integrable_not_infty_alt3 :
    !m f. measure_space m /\ integrable m f ==>
          integrable m (\x. if ((f x = NegInf) \/ (f x = PosInf)) then 0 else f x) /\
         (integral m f =
          integral m (\x. if ((f x = NegInf) \/ (f x = PosInf)) then 0 else f x))
Proof
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
 >> reverse (RW_TAC std_ss [integral_def, integrable_def, GSYM fn_plus_def, GSYM fn_minus_def])
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
      GEN_TAC >> DISCH_TAC >> DISJ1_TAC \\
      CONJ_TAC >- (Cases_on `fn_plus f x = PosInf`
                   >- METIS_TAC [extreal_cases, extreal_of_num_def, extreal_not_infty] \\
                   ASM_SIMP_TAC std_ss [] \\
                   METIS_TAC [FN_PLUS_POS, pos_not_neginf]) \\
      Cases_on `fn_minus f x = PosInf`
      >- METIS_TAC [extreal_cases, extreal_of_num_def, extreal_not_infty] \\
      ASM_SIMP_TAC std_ss [] ]
QED

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

(* enhanced with more general antecedents, old:

      (!x. x IN m_space m ==> f2 x <> PosInf)

   new:

      (!x. x IN m_space m ==> f1 x <> PosInf \/ f2 x <> PosInf)
 *)
Theorem integral_add_lemma :
    !m f f1 f2.
       measure_space m /\ integrable m f /\
       integrable m f1 /\ integrable m f2 /\
      (!x. x IN m_space m ==> (f x = f1 x - f2 x)) /\
      (!x. x IN m_space m ==> 0 <= f1 x) /\
      (!x. x IN m_space m ==> 0 <= f2 x) /\
      (!x. x IN m_space m ==> f1 x <> PosInf \/ f2 x <> PosInf) ==>
      (integral m f = pos_fn_integral m f1 - pos_fn_integral m f2)
Proof
    rpt STRIP_TAC
 >> ‘sigma_algebra (measurable_space m)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
 >> REWRITE_TAC [integral_def]
 >> `!x. x IN m_space m ==> f1 x <> NegInf` by METIS_TAC [pos_not_neginf]
 >> `!x. x IN m_space m ==> f2 x <> NegInf` by METIS_TAC [pos_not_neginf]
 >> Q.ABBREV_TAC `h1 = (\x. fn_plus f x + f2 x)`
 >> Q.ABBREV_TAC `h2 = (\x. fn_minus f x + f1 x)`
 >> Know `!x. x IN m_space m ==> (h1 x = h2 x)`
 >- (RW_TAC std_ss [Abbr ‘h1’, Abbr ‘h2’] \\
     Q.PAT_X_ASSUM ‘!x. x IN m_space m ==> P \/ Q’ (MP_TAC o (Q.SPEC ‘x’)) \\
     RW_TAC std_ss [] \\
     Cases_on ‘f2 x = PosInf’
     >- (‘?r. f1 x = Normal r’ by METIS_TAC [extreal_cases] \\
         ‘f x = NegInf’ by METIS_TAC [extreal_sub_def] \\
         ‘fn_minus f x = PosInf’ by METIS_TAC [FN_MINUS_ALT, min_infty, extreal_ainv_def] \\
         ‘fn_plus f x = 0’ by METIS_TAC [FN_MINUS_INFTY_IMP] \\
         rw [extreal_add_def]) \\
    ‘f1 x <> NegInf /\ f2 x <> NegInf’ by PROVE_TAC [] \\
     SIMP_TAC std_ss [fn_plus_def, fn_minus_def, add_lzero] \\
     Cases_on `f1 x` >> Cases_on `f2 x` \\
     FULL_SIMP_TAC std_ss [extreal_sub_def, extreal_add_def, extreal_ainv_def,
                           extreal_11, add_lzero, extreal_of_num_def, GSYM lt_infty,
                           extreal_lt_eq, extreal_not_infty] \\
     Cases_on ‘0 < r - r'’
     >- (‘~(r - r' < 0)’ by METIS_TAC [REAL_LT_ANTISYM] \\
         fs [extreal_add_def, extreal_sub_def, add_lzero] >> REAL_ARITH_TAC) \\
     Cases_on ‘r - r' < 0’
     >- (fs [extreal_add_def, extreal_sub_def, add_lzero] >> REAL_ARITH_TAC) \\
     fs [extreal_add_def, extreal_11] \\
    ‘r - r' = 0’ by METIS_TAC [REAL_LE_ANTISYM, real_lt] >> POP_ASSUM MP_TAC \\
     REAL_ARITH_TAC)
 >> DISCH_TAC
 >> Know `pos_fn_integral m h1 = pos_fn_integral m h2`
 >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
     RW_TAC std_ss [Abbr ‘h2’] \\
     MATCH_MP_TAC le_add >> rw [FN_MINUS_POS]) >> DISCH_TAC
 >> `pos_fn_integral m h1 =
     pos_fn_integral m (fn_plus f) + pos_fn_integral m f2`
      by (Q.UNABBREV_TAC `h1`
          >> MATCH_MP_TAC pos_fn_integral_add
          >> FULL_SIMP_TAC std_ss [integrable_def]
          >> RW_TAC std_ss [le_refl, lt_le, IN_MEASURABLE_BOREL_FN_PLUS, FN_PLUS_POS])
 >> `pos_fn_integral m h2 =
     pos_fn_integral m (fn_minus f) + pos_fn_integral m f1`
      by (Q.UNABBREV_TAC `h2`
          >> MATCH_MP_TAC pos_fn_integral_add
          >> METIS_TAC [FN_MINUS_POS, IN_MEASURABLE_BOREL_FN_MINUS, integrable_def])
 >> `pos_fn_integral m f2 <> PosInf` by METIS_TAC [integrable_pos]
 >> `pos_fn_integral m (fn_minus f) <> PosInf`
      by METIS_TAC [integrable_def]
 >> `pos_fn_integral m f2 <> NegInf`
      by METIS_TAC [pos_fn_integral_pos, lt_infty, lte_trans, num_not_infty]
 >> `0 <= pos_fn_integral m (fn_minus f)`
      by METIS_TAC [pos_fn_integral_pos, FN_MINUS_POS]
 >> `pos_fn_integral m (fn_minus f) <> NegInf`
      by METIS_TAC [lt_infty, lte_trans, num_not_infty]
 >> METIS_TAC [eq_add_sub_switch]
QED

(* an improved version without the following antecedents: (used by FUBINI)

   !x. x IN m_space m ==> f1 x <> PosInf \/ f2 x <> PosInf
 *)
Theorem integral_add_lemma' :
    !m f f1 f2.
       measure_space m /\ integrable m f /\
       integrable m f1 /\ integrable m f2 /\
      (!x. x IN m_space m ==> (f x = f1 x - f2 x)) /\
      (!x. x IN m_space m ==> 0 <= f1 x) /\
      (!x. x IN m_space m ==> 0 <= f2 x) ==>
      (integral m f = pos_fn_integral m f1 - pos_fn_integral m f2)
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘N1 = {x | x IN m_space m /\ f1 x = PosInf}’
 >> Q.ABBREV_TAC ‘N2 = {x | x IN m_space m /\ f2 x = PosInf}’
 >> ‘null_set m N1 /\ null_set m N2’ by METIS_TAC [integrable_infty_null]
 >> Q.ABBREV_TAC ‘g1 = \x. if f1 x = PosInf then 0 else f1 x’
 >> Q.ABBREV_TAC ‘g2 = \x. if f2 x = PosInf then 0 else f2 x’
 >> Know ‘integrable m g1 /\ pos_fn_integral m f1 = pos_fn_integral m g1’
 >- (Q.UNABBREV_TAC ‘g1’ \\
     MATCH_MP_TAC integrable_not_infty_alt2 >> rw [])
 >> STRIP_TAC >> POP_ORW
 >> Know ‘integrable m g2 /\ pos_fn_integral m f2 = pos_fn_integral m g2’
 >- (Q.UNABBREV_TAC ‘g2’ \\
     MATCH_MP_TAC integrable_not_infty_alt2 >> rw [])
 >> STRIP_TAC >> POP_ORW
 (* applying integral_add_lemma *)
 >> Q.ABBREV_TAC ‘g = \x. g1 x - g2 x’
 >> Know ‘integral m f = integral m g’
 >- (MATCH_MP_TAC integral_cong_AE >> art [] \\
     rw [AE_DEF] \\
     Q.EXISTS_TAC ‘N1 UNION N2’ \\
     CONJ_TAC >- METIS_TAC [NULL_SET_UNION, IN_APP] \\
     rw [Abbr ‘N1’, Abbr ‘N2’, Abbr ‘g’, Abbr ‘g1’, Abbr ‘g2’])
 >> Rewr'
 >> MATCH_MP_TAC integral_add_lemma >> simp []
 (* easy goals first *)
 >> reverse CONJ_TAC
 >- (rw [Abbr ‘g1’, Abbr ‘g2’])
 (* integrable m g *)
 >> Q.UNABBREV_TAC ‘g’
 >> MATCH_MP_TAC integrable_sub
 >> rw [Abbr ‘g1’, Abbr ‘g2’]
 >> MATCH_MP_TAC pos_not_neginf >> simp []
QED

(* enhanced with more general antecedents, old:

           (!x. x IN m_space m ==> (f x <> NegInf /\ g x <> NegInf))

   new:
           (!x. x IN m_space m ==> (f x <> NegInf /\ g x <> NegInf) \/
                                   (f x <> PosInf /\ g x <> PosInf))
 *)
Theorem integral_add :
    !m f g. measure_space m /\ integrable m f /\ integrable m g /\
           (!x. x IN m_space m ==> (f x <> NegInf /\ g x <> NegInf) \/
                                   (f x <> PosInf /\ g x <> PosInf)) ==>
           (integral m (\x. f x + g x) = integral m f + integral m g)
Proof
    RW_TAC std_ss []
 >> ‘sigma_algebra (measurable_space m)’ by fs [measure_space_def]
 >> Know `integral m (\x. f x + g x) =
          pos_fn_integral m (\x. fn_plus f x + fn_plus g x) -
          pos_fn_integral m (\x. fn_minus f x + fn_minus g x)`
 >- (MATCH_MP_TAC integral_add_lemma \\
    `!x. 0 <= fn_minus f x + fn_minus g x` by METIS_TAC [FN_MINUS_POS, le_add] \\
    `!x. 0 <= fn_plus f x + fn_plus g x` by METIS_TAC [FN_PLUS_POS, le_add] \\
     RW_TAC std_ss [FUN_EQ_THM, add_rzero, add_lzero, lt_imp_le, le_refl, le_add,
                    integrable_add] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       MATCH_MP_TAC integrable_add >> rw [integrable_fn_plus] \\
       Q.PAT_X_ASSUM ‘!x. x IN m_space m ==> P \/ Q’ (MP_TAC o (Q.SPEC ‘x’)) \\
       RW_TAC std_ss [] >| (* 2 subgoals *)
       [ (* goal 1.1 (of 2) *)
         DISJ1_TAC \\
         CONJ_TAC >> (MATCH_MP_TAC pos_not_neginf >> REWRITE_TAC [FN_PLUS_POS]),
         (* goal 1.2 (of 2) *)
         DISJ1_TAC \\
         CONJ_TAC >> (MATCH_MP_TAC pos_not_neginf >> REWRITE_TAC [FN_PLUS_POS]) ],
       (* goal 2 (of 4) *)
       METIS_TAC [integrable_fn_minus, integrable_add, FN_MINUS_POS, pos_not_neginf],
       (* goal 3 (of 4) *)
      `f x + g x = fn_plus f x - fn_minus f x + (fn_plus g x - fn_minus g x)`
         by PROVE_TAC [FN_DECOMP] >> POP_ORW \\
       Q.PAT_X_ASSUM ‘!x. x IN m_space m ==> P \/ Q’ (MP_TAC o (Q.SPEC ‘x’)) \\
       RW_TAC std_ss []
       >- (Know ‘fn_minus f x <> PosInf /\ fn_minus g x <> PosInf’
           >- (rw [fn_minus_def] >> METIS_TAC [neg_neg, extreal_ainv_def]) >> STRIP_TAC \\
          ‘fn_plus f x <> NegInf /\ fn_plus g x <> NegInf’
              by PROVE_TAC [FN_PLUS_POS, pos_not_neginf] \\
           MATCH_MP_TAC add2_sub2 >> art []) \\
       Cases_on ‘fn_minus f x = PosInf’
       >- (‘fn_plus f x = 0’ by METIS_TAC [FN_MINUS_INFTY_IMP] >> rw [extreal_ainv_def] \\
           ‘fn_plus g x <> PosInf’ by PROVE_TAC [FN_PLUS_NOT_INFTY] \\
           ‘fn_plus g x <> NegInf’ by METIS_TAC [pos_not_neginf, FN_PLUS_POS] \\
           ‘?r. fn_plus g x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
           Cases_on ‘fn_minus g x = PosInf’ >- (rw [extreal_sub_def, extreal_add_def]) \\
           ‘fn_minus g x <> NegInf’ by METIS_TAC [pos_not_neginf, FN_MINUS_POS] \\
           ‘?s. fn_minus g x = Normal s’ by METIS_TAC [extreal_cases] >> POP_ORW \\
           rw [extreal_sub_def, extreal_add_def]) \\
       Cases_on ‘fn_minus g x = PosInf’
       >- (‘fn_plus g x = 0’ by METIS_TAC [FN_MINUS_INFTY_IMP] >> rw [extreal_ainv_def] \\
           ‘fn_minus g x <> NegInf’ by METIS_TAC [pos_not_neginf, FN_MINUS_POS] \\
           ‘fn_minus f x <> NegInf’ by METIS_TAC [pos_not_neginf, FN_MINUS_POS] \\
           ‘?r. fn_minus f x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
           rw [extreal_add_def, extreal_ainv_def] \\
           ‘fn_plus f x <> PosInf’ by PROVE_TAC [FN_PLUS_NOT_INFTY] \\
           ‘fn_plus f x <> NegInf’ by METIS_TAC [pos_not_neginf, FN_PLUS_POS] \\
           ‘?s. fn_plus f x = Normal s’ by METIS_TAC [extreal_cases] >> POP_ORW \\
           rw [extreal_add_def, extreal_sub_def]) \\
      ‘fn_plus f x <> NegInf /\ fn_plus g x <> NegInf’
          by PROVE_TAC [FN_PLUS_POS, pos_not_neginf] \\
       MATCH_MP_TAC add2_sub2 >> art [],
       (* goal 4 (of 4) *)
       Q.PAT_X_ASSUM ‘!x. x IN m_space m ==> P \/ Q’ (MP_TAC o (Q.SPEC ‘x’)) \\
       RW_TAC std_ss [] >| (* 2 subgoals *)
       [ (* goal 4.1 (of 2) *)
         Know `fn_minus f x <> PosInf /\ fn_minus g x <> PosInf`
         >- (rw [fn_minus_def] >> METIS_TAC [neg_neg, extreal_ainv_def]) >> STRIP_TAC \\
         PROVE_TAC [add_not_infty],
         (* goal 4.2 (of 2) *)
         Cases_on ‘fn_minus f x = PosInf’
         >- (‘fn_plus f x = 0’ by METIS_TAC [FN_MINUS_INFTY_IMP] \\
             ‘fn_plus g x <> PosInf’ by METIS_TAC [FN_PLUS_NOT_INFTY] \\
             ‘fn_plus g x <> NegInf’ by METIS_TAC [pos_not_neginf, FN_PLUS_POS] \\
             ‘?r. fn_plus g x = Normal r’ by METIS_TAC [extreal_cases] \\
             fs [add_lzero]) \\
         Cases_on ‘fn_minus g x = PosInf’
         >- (‘fn_plus g x = 0’ by METIS_TAC [FN_MINUS_INFTY_IMP] \\
             ‘fn_plus f x <> PosInf’ by METIS_TAC [FN_PLUS_NOT_INFTY] \\
             ‘fn_plus f x <> NegInf’ by METIS_TAC [pos_not_neginf, FN_PLUS_POS] \\
             ‘?r. fn_plus f x = Normal r’ by METIS_TAC [extreal_cases] \\
             fs [add_rzero]) \\
         PROVE_TAC [add_not_infty] ] ])
 >> Rewr
 >> Know `pos_fn_integral m (\x. fn_plus f x + fn_plus g x) =
          pos_fn_integral m (fn_plus f) + pos_fn_integral m (fn_plus g)`
 >- (MATCH_MP_TAC pos_fn_integral_add \\
     FULL_SIMP_TAC std_ss [integrable_def] \\
     rw [FN_PLUS_POS, IN_MEASURABLE_BOREL_FN_PLUS])
 >> Rewr'
 >> Know `pos_fn_integral m (\x. fn_minus f x + fn_minus g x) =
          pos_fn_integral m (fn_minus f) + pos_fn_integral m (fn_minus g)`
 >- (MATCH_MP_TAC pos_fn_integral_add \\
     FULL_SIMP_TAC std_ss [integrable_def] \\
     rw [FN_MINUS_POS, IN_MEASURABLE_BOREL_FN_MINUS])
 >> Rewr'
 >> RW_TAC std_ss [integral_def]
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
 >> FULL_SIMP_TAC std_ss [integrable_def]
 >> Q.ABBREV_TAC `a = pos_fn_integral m (fn_plus f)`
 >> Q.ABBREV_TAC `b = pos_fn_integral m (fn_minus f)`
 >> Q.ABBREV_TAC `c = pos_fn_integral m (fn_plus g)`
 >> Q.ABBREV_TAC `d = pos_fn_integral m (fn_minus g)`
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> MATCH_MP_TAC add2_sub2 >> art []
QED

(* cf. real_lebesgueTheory.integral_times *)
Theorem integral_cmul :
    !m f c. measure_space m /\ integrable m f ==>
           (integral m (\x. Normal c * f x) = Normal c * integral m f)
Proof
    RW_TAC std_ss [integral_def,GSYM fn_plus_def,GSYM fn_minus_def]
 >> `(\x. fn_plus f x) = fn_plus f` by METIS_TAC []
 >> `(\x. fn_minus f x) = fn_minus f` by METIS_TAC []
 >> Cases_on `0 <= c`
 >- (RW_TAC std_ss [FN_PLUS_CMUL, FN_MINUS_CMUL, FN_PLUS_POS, FN_MINUS_POS,
                    pos_fn_integral_cmul] \\
     MATCH_MP_TAC (GSYM sub_ldistrib) \\
     FULL_SIMP_TAC std_ss [extreal_not_infty, integrable_def, GSYM fn_plus_def,
                           GSYM fn_minus_def] \\
     METIS_TAC [pos_fn_integral_pos, FN_PLUS_POS, FN_MINUS_POS, lt_infty, lte_trans,
                extreal_of_num_def])
 >> `c <= 0` by METIS_TAC [REAL_LT_IMP_LE,real_lt]
 >> `0 <= -c` by METIS_TAC [REAL_LE_NEG,REAL_NEG_0]
 >> RW_TAC std_ss [FN_PLUS_CMUL, FN_MINUS_CMUL, FN_PLUS_POS, FN_MINUS_POS,
                   pos_fn_integral_cmul, extreal_ainv_def]
 >> RW_TAC std_ss [Once (GSYM eq_neg), GSYM mul_lneg, extreal_ainv_def]
 >> FULL_SIMP_TAC std_ss [integrable_def, GSYM fn_plus_def, GSYM fn_minus_def]
 >> `pos_fn_integral m (fn_plus f) <> NegInf`
      by METIS_TAC [pos_fn_integral_pos, FN_PLUS_POS, lt_infty, lte_trans, extreal_of_num_def]
 >> `pos_fn_integral m (fn_minus f) <> NegInf`
      by METIS_TAC [pos_fn_integral_pos, FN_MINUS_POS, lt_infty, lte_trans, extreal_of_num_def]
 >> FULL_SIMP_TAC std_ss [GSYM sub_ldistrib, extreal_not_infty, GSYM mul_rneg]
 >> METIS_TAC [neg_sub]
QED

Theorem integrable_finite_integral :
    !m f. measure_space m /\ integrable m f ==>
          integral m f <> PosInf /\ integral m f <> NegInf
Proof
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
 >> ASM_REWRITE_TAC [extreal_sub_def, extreal_not_infty]
QED

Theorem integral_sub :
    !m f g. measure_space m /\ integrable m f /\ integrable m g /\
           (!x. x IN m_space m ==> (f x <> NegInf /\ g x <> PosInf) \/
                                   (f x <> PosInf /\ g x <> NegInf)) ==>
           (integral m (\x. f x - g x) = integral m f - integral m g)
Proof
    rw [extreal_sub]
 >> ‘integrable m (\x. -g x)’ by METIS_TAC [integrable_ainv]
 >> Know ‘Normal (-1) * integral m g = integral m (\x. Normal (-1) * g x)’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC integral_cmul >> art [])
 >> rw [GSYM neg_minus1, GSYM extreal_ainv_def, normal_1]
 >> HO_MATCH_MP_TAC integral_add >> rw []
 >> CCONTR_TAC
 >> Cases_on ‘g x’ >> METIS_TAC [extreal_ainv_def, extreal_distinct]
QED

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

Theorem integral_cmul_infty' :
    !m s. measure_space m /\ s IN measurable_sets m ==>
         (integral m (\x. NegInf * indicator_fn s x) = NegInf * (measure m s))
Proof
    rpt STRIP_TAC
 >> Know `integral m (\x. PosInf) = integral m (\x. (\x. PosInf) x * indicator_fn (m_space m) x)`
 >- (MATCH_MP_TAC integral_mspace >> art [])
 >> Rewr'
 >> REWRITE_TAC [integral_def]
 >> Know ‘pos_fn_integral m (\x. NegInf * indicator_fn s x)^+ = pos_fn_integral m (\x. 0)’
 >- (MATCH_MP_TAC pos_fn_integral_cong \\
     rw [FN_PLUS_ALT, le_max] \\
     rw [indicator_fn_def])
 >> Rewr'
 >> Know ‘pos_fn_integral m (\x. NegInf * indicator_fn s x)^- =
          pos_fn_integral m (\x. PosInf * indicator_fn s x)’
 >- (MATCH_MP_TAC pos_fn_integral_cong \\
     rw [fn_minus_def, GSYM mul_lneg, extreal_ainv_def] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       MATCH_MP_TAC le_mul >> rw [le_infty, INDICATOR_FN_POS],
       (* goal 2 (of 3) *)
       MATCH_MP_TAC le_mul >> rw [le_infty, INDICATOR_FN_POS],
       (* goal 3 (of 3) *)
       fs [extreal_lt_def] \\
       STRIP_ASSUME_TAC (Q.SPECL [‘s’, ‘x’] indicator_fn_normal) \\
       FULL_SIMP_TAC std_ss [extreal_mul_def, le_infty, extreal_of_num_def, extreal_11] \\
       Cases_on ‘r = 0’ >- rw [] \\
      ‘0 < r’ by PROVE_TAC [REAL_LE_LT] \\
       FULL_SIMP_TAC std_ss [le_infty, extreal_not_infty] ])
 >> Rewr'
 >> ASM_SIMP_TAC std_ss [pos_fn_integral_zero, sub_lzero]
 >> Know ‘pos_fn_integral m (\x. PosInf * indicator_fn s x) = PosInf * measure m s’
 >- (MATCH_MP_TAC pos_fn_integral_cmul_infty >> art [])
 >> Rewr'
 >> rw [GSYM mul_lneg, extreal_ainv_def]
QED

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

Theorem integral_neginf :
    !m. measure_space m /\ 0 < measure m (m_space m) ==> (integral m (\x. NegInf) = NegInf)
Proof
    rpt STRIP_TAC
 >> Know `integral m (\x. NegInf) =
          integral m (\x. (\x. NegInf) x * indicator_fn (m_space m) x)`
 >- (MATCH_MP_TAC integral_mspace >> art [])
 >> Rewr' >> BETA_TAC
 >> Know `integral m (\x. NegInf * indicator_fn (m_space m) x) = NegInf * (measure m (m_space m))`
 >- (MATCH_MP_TAC integral_cmul_infty' >> art [] \\
     MATCH_MP_TAC MEASURE_SPACE_MSPACE_MEASURABLE >> art [])
 >> Rewr'
 >> Cases_on `measure m (m_space m) = PosInf`
 >- (POP_ORW >> REWRITE_TAC [extreal_mul_def])
 >> METIS_TAC [mul_infty]
QED

val integral_indicator_pow_eq = store_thm (* new *)
  ("integral_indicator_pow_eq",
  ``!m s n. measure_space m /\ s IN measurable_sets m /\ 0 < n ==>
           (integral m (\x. (indicator_fn s x) pow n) = integral m (indicator_fn s))``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC integral_cong
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
Theorem integral_mono :
    !m f1 f2. measure_space m /\ integrable m f1 /\ integrable m f2 /\
             (!x. x IN m_space m ==> f1 x <= f2 x) ==>
              integral m f1 <= integral m f2
Proof
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
 >- (MATCH_MP_TAC pos_fn_integral_mono >> simp [FN_PLUS_POS])
 >> REWRITE_TAC [le_neg]
 >> MATCH_MP_TAC pos_fn_integral_mono
 >> simp [FN_MINUS_POS]
QED

(* added ‘x IN m_space m’ *)
Theorem integrable_sum :
    !m f s. FINITE s /\ measure_space m /\ (!i. i IN s ==> integrable m (f i)) /\
            (!i x. i IN s /\ x IN m_space m ==>
                   f i x <> PosInf /\ f i x <> NegInf) ==>
            integrable m (\x. SIGMA (\i. f i x) s)
Proof
    Suff `!s:'b->bool.
            FINITE s ==>
              (\s:'b->bool. !m f. measure_space m /\ (!i. i IN s ==> integrable m (f i)) /\
                                  (!x i. i IN s /\ x IN m_space m ==>
                                         f i x <> PosInf /\ f i x <> NegInf)
                              ==> integrable m (\x. SIGMA (\i. f i x) s)) s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, integrable_zero]
 >> Know `!x. x IN m_space m ==>
              SIGMA (\i. f i x) (e INSERT s) = f e x + (\x. SIGMA (\i. f i x) s) x`
 >- (RW_TAC std_ss [] \\
     (MP_TAC o Q.SPEC `e` o UNDISCH o Q.SPECL [`(\i. f i x)`,`s`] o
      INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY \\
    `!i x. i IN e INSERT s /\ x IN m_space m ==> (\i. f i x) i <> NegInf`
        by RW_TAC std_ss [] \\
     FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]) >> DISCH_TAC
 >> MATCH_MP_TAC integrable_eq
 >> Q.EXISTS_TAC ‘\x. f e x + (\x. SIGMA (\i. f i x) s) x’ >> art []
 >> reverse CONJ_TAC >- simp []
 >> MATCH_MP_TAC integrable_add >> art []
 >> CONJ_TAC >- fs [IN_INSERT]
 >> CONJ_TAC
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> fs [IN_INSERT])
 >> RW_TAC std_ss [IN_INSERT]
 >> DISJ1_TAC
 >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF >> fs [IN_INSERT]
QED

Theorem integral_sum :
    !m f s. FINITE s /\ measure_space m /\ (!i. i IN s ==> integrable m (f i)) /\
            (!x i. i IN s /\ x IN m_space m ==>
                   f i x <> PosInf /\ f i x <> NegInf) ==>
            (integral m (\x. SIGMA (\i. (f i) x) s) = SIGMA (\i. integral m (f i)) s)
Proof
    Suff `!s:'b->bool.
            FINITE s ==>
              (\s:'b->bool. !m f. measure_space m /\ (!i. i IN s ==> integrable m (f i)) /\
                                 (!x i. i IN s /\ x IN m_space m ==>
                                        f i x <> PosInf /\ f i x <> NegInf)
                             ==> (integral m (\x. SIGMA (\i. (f i) x) s) =
                                  SIGMA (\i. integral m (f i)) s)) s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, integral_zero]
 >> Know `!x. x IN m_space m ==>
              SIGMA (\i. f i x) (e INSERT s) = f e x + SIGMA (\i. f i x) s`
 >- (RW_TAC std_ss [] \\
     (MP_TAC o Q.SPEC `e` o UNDISCH o Q.SPECL [`(\i. f i x)`,`s`] o
      INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY \\
    `!i. i IN e INSERT s ==> (\i. f i x) i <> NegInf` by RW_TAC std_ss [] \\
     FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]) >> DISCH_TAC
 >> Know ‘integral m (\x. SIGMA (\i. f i x) (e INSERT s)) =
          integral m (\x. f e x + SIGMA (\i. f i x) s)’
 >- (MATCH_MP_TAC integral_cong >> simp []) >> Rewr'
 >> `integral m (\x. f e x + SIGMA (\i. f i x) s) =
     integral m (\x. f e x + (\x. SIGMA (\i. f i x) s) x)` by METIS_TAC [] >> POP_ORW
 >> Know `integral m (\x. f e x + (\x. SIGMA (\i. f i x) s) x) =
          integral m (f e) + integral m (\x. SIGMA (\i. f i x) s)`
 >- (MATCH_MP_TAC integral_add >> fs [IN_INSERT] \\
     MATCH_MP_TAC integrable_sum >> METIS_TAC []) >> Rewr'
 >> Know `integral m (\x. SIGMA (\i. f i x) s) = SIGMA (\i. integral m (f i)) s`
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> fs [IN_INSERT]) >> Rewr'
 >> (MP_TAC o Q.SPEC `e` o UNDISCH o Q.SPECL [`(\i. integral m (f i))`,`s`] o
     INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY
 >> Know `!x. x IN e INSERT s ==> (\i. integral m (f i)) x <> NegInf`
 >- (RW_TAC std_ss [] >> METIS_TAC [integrable_finite_integral])
 >> RW_TAC std_ss []
 >> FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]
QED

(* general case: `(m_space m)` can be infinite but `IMAGE f (m_space)` is finite.
   e.g. m_space m = univ(:real) but f() only takes values from a finite set.

   added `integrable m f` into antecedents, otherwise `integral m f` is not defined;
   added `measure m (m_space m) < PosInf` into antecedents
 *)
Theorem finite_support_integral_reduce :
    !m f. measure_space m /\ f IN measurable (m_space m,measurable_sets m) Borel /\
         (!x. x IN m_space m ==> f x <> NegInf /\ f x <> PosInf) /\
          FINITE (IMAGE f (m_space m)) /\
          integrable m f /\ measure m (m_space m) < PosInf ==>
         (integral m f = finite_space_integral m f)
Proof
    rpt STRIP_TAC
 >> ‘sigma_algebra (measurable_space m)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
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
       reverse (RW_TAC real_ss [fn_plus_def])
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
           >> reverse (RW_TAC std_ss [mul_rone, mul_rzero])
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
       >> reverse (RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM, FINITE_DELETE, GSYM extreal_of_num_def,
                   mul_lzero, DELETE_DELETE, add_lzero])
       >- METIS_TAC [extreal_of_num_def, extreal_lt_eq, lt_antisym, real_lt]
       >> RW_TAC std_ss [indicator_fn_def, IN_INTER, DELETE_DELETE, mul_rzero, add_lzero,
                         IN_PREIMAGE, IN_SING, mul_rone]
       >> Suff `SIGMA (\i'. Normal (if 0 <= c i' then c i' else 0) *
                            if c i = c i' then 1 else 0) (count n DELETE i) = 0`
       >- RW_TAC std_ss [add_rzero]
       >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
       >> reverse (RW_TAC std_ss [FINITE_DELETE, mul_rone, mul_rzero])
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
       reverse (RW_TAC real_ss [fn_minus_def])
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
           >> reverse (RW_TAC std_ss [mul_rone, mul_rzero])
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
       >> reverse (RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM, FINITE_DELETE, GSYM extreal_of_num_def,
                                  mul_lzero, DELETE_DELETE, add_lzero])
       >- METIS_TAC [extreal_lt_eq, real_lt, extreal_of_num_def, lt_antisym]
       >> RW_TAC std_ss [indicator_fn_def, IN_INTER, DELETE_DELETE, mul_rzero,
                         add_lzero, IN_PREIMAGE, IN_SING, mul_rone]
       >> Suff `SIGMA (\i'. Normal (if c i' <= 0 then -c i' else 0) *
                            if c i = c i' then 1 else 0) (count n DELETE i) = 0`
       >- METIS_TAC [add_rzero, extreal_ainv_def]
       >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
       >> reverse (RW_TAC std_ss [FINITE_DELETE, mul_rone, mul_rzero])
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
 >> METIS_TAC [positive_def]
QED

(* special case of "finite_support_integral_reduce": (m_space m) is finite.

   added `measure m (m_space m) < PosInf` into antecedents.
   FIXME: remove `integrable m f` and prove it.
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
Theorem finite_space_POW_integral_reduce :
    !m f. measure_space m /\ (POW (m_space m) = measurable_sets m) /\ FINITE (m_space m) /\
         (!x. x IN m_space m ==> f x <> NegInf /\ f x <> PosInf) /\
          measure m (m_space m) < PosInf ==>
         (integral m f = SIGMA (\x. f x * (measure m {x})) (m_space m))
Proof
    RW_TAC std_ss []
 >> ‘sigma_algebra (measurable_space m)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
 >> `f IN measurable (m_space m, measurable_sets m) Borel`
        by (RW_TAC std_ss [IN_MEASURABLE_BOREL,IN_FUNSET,IN_UNIV,space_def,subsets_def]
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
       reverse (RW_TAC real_ss [fn_plus_def])
       >- (FULL_SIMP_TAC std_ss [extreal_lt_def, IN_INTER] \\
           (MP_TAC o Q.SPEC `(\i. Normal (if 0 <= x i then x i else 0) *
                                  indicator_fn {c i} t)` o
               UNDISCH o Q.ISPEC `count n`) EXTREAL_SUM_IMAGE_IN_IF \\
           Know `!x'. x' IN count n ==>
                      (\i. Normal (if 0 <= x i then x i else 0) *
                           indicator_fn {c i} t) x' <> NegInf`
           >- (GEN_TAC >> DISCH_TAC >> BETA_TAC >> rename1 `i IN count n` \\
               MATCH_MP_TAC pos_not_neginf \\
               Cases_on `~(0 <= x i)` >- fs [GSYM extreal_of_num_def, mul_lzero, le_refl] \\
               fs [] \\
               MATCH_MP_TAC le_mul \\
               CONJ_TAC >- fs [extreal_le_eq, extreal_of_num_def] \\
               REWRITE_TAC [INDICATOR_FN_POS]) \\
           RW_TAC std_ss [] >> POP_ASSUM K_TAC \\
           Suff `(\x'. if x' IN count n then Normal (if 0 <= x x' then x x' else 0) *
                       indicator_fn {c x'} t else 0) = (\x. 0)`
           >- RW_TAC std_ss [EXTREAL_SUM_IMAGE_ZERO] \\
           RW_TAC std_ss [FUN_EQ_THM] \\
           Cases_on `~(x' IN count n)` >- RW_TAC std_ss [] \\
           reverse (RW_TAC std_ss [mul_rone, mul_rzero])
           >- RW_TAC std_ss [GSYM extreal_of_num_def, mul_lzero] \\
           rename1 `i IN count n` \\
           Cases_on `c i <> t` >- PROVE_TAC [INDICATOR_FN_SING_0, mul_rzero] \\
           fs [INDICATOR_FN_SING_1, mul_rone] \\
          `f t = Normal (x i)` by PROVE_TAC [] \\
          `0 <= f t` by PROVE_TAC [extreal_le_eq, extreal_of_num_def] \\
          `f t = 0` by PROVE_TAC [le_antisym, extreal_lt_def] \\
           fs [])
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
       >> reverse (RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM, FINITE_DELETE, GSYM extreal_of_num_def,
                                  mul_lzero, DELETE_DELETE, add_lzero])
       >- METIS_TAC [extreal_of_num_def, extreal_lt_eq, lt_antisym, real_lt]
       >> RW_TAC std_ss [indicator_fn_def, IN_INTER, DELETE_DELETE, mul_rzero, add_lzero,
                         IN_PREIMAGE, IN_SING, mul_rone]
       >> Suff `SIGMA (\i'. Normal (if 0 <= x i' then x i' else 0) *
                            if c i = c i' then 1 else 0) (count n DELETE i) = 0`
       >- RW_TAC std_ss [add_rzero]
       >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
       >> reverse (RW_TAC std_ss [FINITE_DELETE, mul_rone, mul_rzero])
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
       reverse (RW_TAC real_ss [fn_minus_def])
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
           >> reverse (RW_TAC std_ss [mul_rone, mul_rzero])
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
       >> reverse (RW_TAC std_ss [EXTREAL_SUM_IMAGE_THM, FINITE_DELETE, GSYM extreal_of_num_def,
                                  mul_lzero, DELETE_DELETE, add_lzero])
       >- METIS_TAC [extreal_of_num_def, extreal_lt_eq, lt_antisym, real_lt]
       >> RW_TAC std_ss [indicator_fn_def, IN_INTER, DELETE_DELETE, mul_rzero, add_lzero,
                         IN_PREIMAGE, IN_SING, mul_rone]
       >> Suff `SIGMA (\i'. Normal (if x i' <= 0 then -(x i') else 0) *
                      if c i = c i' then 1 else 0) (count n DELETE i) = 0`
       >- RW_TAC std_ss [add_rzero, extreal_ainv_def]
       >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
       >> reverse (RW_TAC std_ss [FINITE_DELETE, mul_rone, mul_rzero])
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
 >> PROVE_TAC [positive_def]
QED

(* added ‘x IN m_space m’ *)
Theorem measure_space_density :
    !m f. measure_space m /\ f IN measurable (m_space m,measurable_sets m) Borel /\
         (!x. x IN m_space m ==> 0 <= f x) ==> measure_space (density m f)
Proof
    Q.X_GEN_TAC ‘M’ >> rpt STRIP_TAC
 >> ‘sigma_algebra (measurable_space M)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
 >> SIMP_TAC std_ss [measure_space_def, density_measure_def, density_def,
                     m_space_def, measurable_sets_def]
 >> Q.PAT_ASSUM `measure_space M`
      (STRIP_ASSUME_TAC o (REWRITE_RULE [measure_space_def]))
 >> RW_TAC std_ss []
 >- (FULL_SIMP_TAC std_ss [positive_def, measure_def, measurable_sets_def] \\
     CONJ_TAC
     >- (SIMP_TAC std_ss [indicator_fn_def, GSPECIFICATION, NOT_IN_EMPTY] \\
         ASM_SIMP_TAC std_ss [mul_rzero, pos_fn_integral_zero]) \\
     RW_TAC std_ss [] >> MATCH_MP_TAC pos_fn_integral_pos \\
     RW_TAC std_ss [] \\
     MATCH_MP_TAC le_mul >> ASM_SIMP_TAC std_ss [INDICATOR_FN_POS])
 (* countably_additive *)
 >> RW_TAC std_ss [countably_additive_def, measure_def, measurable_sets_def,
                   IN_FUNSET, IN_UNIV]
 >> rename1 `!x. A x IN measurable_sets M`
 >> Q.PAT_ASSUM `countably_additive M`
      (ASSUME_TAC o (ONCE_REWRITE_RULE [GSYM MEASURE_SPACE_REDUCE]))
 >> FULL_SIMP_TAC std_ss [countably_additive_alt_eq]
 >> `!i. A i IN measurable_sets M` by ASM_SET_TAC []
 >> Know `!i. (\x. f x * indicator_fn (A i) x) IN measurable (m_space M,measurable_sets M) Borel`
 >- (GEN_TAC \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR \\
     ASM_SIMP_TAC std_ss [subsets_def])
 >> RW_TAC std_ss [o_DEF]
 >> Know `suminf (\x. pos_fn_integral M ((\x x'. f x' * indicator_fn (A x) x') x)) =
          pos_fn_integral M (\x'. suminf (\x. (\x x'. f x' * indicator_fn (A x) x') x x'))`
 >- (MATCH_MP_TAC (GSYM pos_fn_integral_suminf) \\
     ASM_SIMP_TAC std_ss [] \\
     rpt STRIP_TAC >> MATCH_MP_TAC le_mul \\
     ASM_SIMP_TAC std_ss [INDICATOR_FN_POS])
 >> ASM_SIMP_TAC std_ss [] >> DISC_RW_KILL
 >> Know `!y. y IN m_space M ==>
             (suminf (\x. (f y) * (\x. indicator_fn (A x) y) x) =
              (f y) * suminf (\x. indicator_fn (A x) y))`
 >- (GEN_TAC >> DISCH_TAC >> MATCH_MP_TAC ext_suminf_cmul \\
     ASM_SIMP_TAC std_ss [INDICATOR_FN_POS])
 >> SIMP_TAC std_ss [] >> DISCH_TAC
 >> Know ‘pos_fn_integral M (\x'. suminf (\x. f x' * indicator_fn (A x) x')) =
          pos_fn_integral M (\y. f y * suminf (\x. indicator_fn (A x) y))’
 >- (MATCH_MP_TAC pos_fn_integral_cong >> simp [] \\
     rpt STRIP_TAC >> MATCH_MP_TAC le_mul >> simp [] \\
     MATCH_MP_TAC ext_suminf_pos >> rw [INDICATOR_FN_POS]) >> Rewr'
 >> Know  `!y. y IN m_space M ==>
              (suminf (\x. indicator_fn (A x) y) =
               indicator_fn (BIGUNION (IMAGE A UNIV)) y)`
 >- (GEN_TAC >> DISCH_TAC \\
     MATCH_MP_TAC indicator_fn_suminf >> art []) >> DISCH_TAC
 >> MATCH_MP_TAC pos_fn_integral_cong >> simp []
 >> rpt STRIP_TAC
 >> MATCH_MP_TAC le_mul >> simp [INDICATOR_FN_POS]
QED

Theorem measure_space_density' :
    !M f. measure_space M /\ f IN measurable (m_space M,measurable_sets M) Borel
      ==> measure_space (density M (fn_plus f))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC measure_space_density >> art [FN_PLUS_POS]
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_FN_PLUS
 >> rw [MEASURE_SPACE_SIGMA_ALGEBRA]
QED

val suminf_measure = prove (
  ``!M A. measure_space M /\ IMAGE (\i:num. A i) UNIV SUBSET measurable_sets M /\
          disjoint_family A ==>
         (suminf (\i. measure M (A i)) = measure M (BIGUNION {A i | i IN UNIV}))``,
    RW_TAC std_ss [GSYM IMAGE_DEF]
 >> MATCH_MP_TAC (SIMP_RULE std_ss [o_DEF] MEASURE_COUNTABLY_ADDITIVE)
 >> FULL_SIMP_TAC std_ss [IN_FUNSET, disjoint_family_on, disjoint_family]
 >> ASM_SET_TAC []);

(* removed ‘image_measure_space’, reduced ‘N’ (measure_space) to ‘B’ (sigma_algebra) *)
Theorem measure_space_distr :
    !M B f. measure_space M /\ sigma_algebra B /\
            f IN measurable (m_space M,measurable_sets M) B ==>
            measure_space (space B, subsets B, distr M f)
Proof
    qx_genl_tac [‘M’, ‘B’, ‘t’]
 >> RW_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def, SPACE]
 >- (fs [positive_def, distr_def, measure_def, measurable_sets_def] \\
     rpt STRIP_TAC >> FIRST_X_ASSUM MATCH_MP_TAC \\
     fs [IN_MEASURABLE, space_def, subsets_def])
 >> FULL_SIMP_TAC std_ss [countably_additive_alt_eq, distr_def]
 >> RW_TAC std_ss []
 >> `!i. A i IN subsets B` by ASM_SET_TAC []
 >> `IMAGE (\i. PREIMAGE t (A i) INTER m_space M) UNIV SUBSET measurable_sets M`
      by (FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def, SUBSET_DEF] \\
          FULL_SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] >> METIS_TAC [])
 >> `BIGUNION {PREIMAGE t (A i) INTER m_space M | i IN UNIV} IN measurable_sets M`
      by (FULL_SIMP_TAC std_ss [sigma_algebra_alt])
 >> `disjoint_family (\i. PREIMAGE t (A i) INTER m_space M)`
      by (FULL_SIMP_TAC std_ss [disjoint_family, disjoint_family_on, IN_UNIV] \\
          FULL_SIMP_TAC std_ss [PREIMAGE_def] THEN ASM_SET_TAC [])
 >> SIMP_TAC std_ss [PREIMAGE_BIGUNION, o_DEF]
 >> Know `IMAGE (PREIMAGE t) {A i | i IN univ(:num)} =
          IMAGE (\i. PREIMAGE t (A i)) UNIV` >- ASM_SET_TAC []
 >> ONCE_REWRITE_TAC [METIS [ETA_AX] ``PREIMAGE t = (\s. PREIMAGE t s)``]
 >> ONCE_REWRITE_TAC [METIS [ETA_AX] ``PREIMAGE t = (\s. PREIMAGE t s)``]
 >> SIMP_TAC std_ss [] >> DISC_RW_KILL
 >> Know `BIGUNION (IMAGE (\i. PREIMAGE t (A i)) univ(:num)) INTER m_space M =
          BIGUNION (IMAGE (\i. PREIMAGE t (A i) INTER m_space M) univ(:num))`
 >- (FULL_SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_BIGUNION] \\
     RW_TAC std_ss [] >> EQ_TAC \\
     RW_TAC std_ss [IN_IMAGE, IN_UNIV, IN_INTER, IN_PREIMAGE] >|
     [ Q.EXISTS_TAC `PREIMAGE t (A i) INTER m_space M` \\
       FULL_SIMP_TAC std_ss [] >> ASM_SET_TAC [],
       FULL_SIMP_TAC std_ss [IN_INTER] >> METIS_TAC [],
       ALL_TAC ] \\
     FULL_SIMP_TAC std_ss [IN_INTER])
 >> SIMP_TAC std_ss [] >> DISC_RW_KILL
 >> Suff `measure M
           (BIGUNION (IMAGE (\i. PREIMAGE t (A i) INTER m_space M) univ(:num))) =
          suminf (\x. measure M ((\x. PREIMAGE t (A x) INTER m_space M) x))`
 >- SIMP_TAC std_ss []
 >> MATCH_MP_TAC (GSYM (REWRITE_RULE [GSYM IMAGE_DEF] suminf_measure))
 >> FULL_SIMP_TAC std_ss [measure_space_def]
 >> ONCE_REWRITE_TAC [GSYM MEASURE_SPACE_REDUCE]
 >> METIS_TAC [countably_additive_alt_eq, space_def, subsets_def]
QED

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
     MATCH_MP_TAC le_mul >> reverse CONJ_TAC >- REWRITE_TAC [INDICATOR_FN_POS] \\
     MATCH_MP_TAC le_mul >> reverse CONJ_TAC >- REWRITE_TAC [INDICATOR_FN_POS] \\
     REWRITE_TAC [extreal_of_num_def, extreal_le_eq] \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> Rewr'
 >> Know `integral m (\x. abs (f x) * indicator_fn a x) =
   pos_fn_integral m (\x. abs (f x) * indicator_fn a x)`
 >- (MATCH_MP_TAC integral_pos_fn >> art [] \\
     RW_TAC std_ss [] \\
     MATCH_MP_TAC le_mul >> reverse CONJ_TAC >- REWRITE_TAC [INDICATOR_FN_POS] \\
     REWRITE_TAC [abs_pos]) >> Rewr'
 >> Know `pos_fn_integral m (\x. Normal (inv r) *
                                (\t. Normal r * indicator_fn {x | Normal r <= abs (f x)} t
                                     * indicator_fn a t) x) =
          Normal (inv r) * pos_fn_integral m (\t. Normal r * indicator_fn {x | Normal r <= abs (f x)} t
                                                  * indicator_fn a t)`
 >- (MATCH_MP_TAC pos_fn_integral_cmul >> art [] \\
     RW_TAC std_ss [] \\
     MATCH_MP_TAC le_mul >> reverse CONJ_TAC >- REWRITE_TAC [INDICATOR_FN_POS] \\
     MATCH_MP_TAC le_mul >> reverse CONJ_TAC >- REWRITE_TAC [INDICATOR_FN_POS] \\
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
     >- (MATCH_MP_TAC le_mul >> reverse CONJ_TAC >- REWRITE_TAC [INDICATOR_FN_POS] \\
         MATCH_MP_TAC le_mul >> reverse CONJ_TAC >- REWRITE_TAC [INDICATOR_FN_POS] \\
         REWRITE_TAC [extreal_of_num_def, extreal_le_eq] \\
         MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
     Cases_on `Normal r <= abs (f x)`
     >- (REWRITE_TAC [GSYM mul_assoc] \\
         MATCH_MP_TAC le_rmul_imp >> art [] \\
         MATCH_MP_TAC le_mul >> REWRITE_TAC [INDICATOR_FN_POS]) \\
     ASM_SIMP_TAC std_ss [indicator_fn_def, GSPECIFICATION, mul_lzero, mul_rzero, le_refl])
 >> MATCH_MP_TAC pos_fn_integral_mono
 >> RW_TAC std_ss []
 >- (MATCH_MP_TAC le_mul >> reverse CONJ_TAC >- REWRITE_TAC [INDICATOR_FN_POS] \\
     MATCH_MP_TAC le_mul >> reverse CONJ_TAC >- REWRITE_TAC [INDICATOR_FN_POS] \\
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
Theorem markov_ineq : (* cf. real_lebesgueTheory.markov_ineq *)
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

(* This is not needed any more (but could be useful somewhere)
Theorem markov_inequality_AE : (* was: positive_integral_Markov_inequality *)
    !M A u c. measure_space M /\
              u IN measurable (m_space M, measurable_sets M) Borel /\
              (AE x::M. 0 <= u x) /\ A IN measurable_sets M ==>
       measure M ({x | x IN m_space M /\ 1 <= &c * u x} INTER A) <=
         &c * pos_fn_integral M (\x. u x * indicator_fn A x)
Proof
QED
*)

(* Theorem 10.4 (v) [1, p.85] (Triangle Inequality) *)
Theorem integral_triangle_ineq :
    !m f. measure_space m /\ integrable m f ==>
          abs (integral m f) <= integral m (abs o f)
Proof
    RW_TAC std_ss [abs_max, Once neg_minus1, extreal_of_num_def, extreal_ainv_def]
 >> Know `Normal (-1) * integral m f = integral m (\x. Normal (-1) * f x)`
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC integral_cmul >> art []) >> Rewr'
 >> Know `integral m (abs o f) = max (integral m (abs o f)) (integral m (abs o f))`
 >- REWRITE_TAC [max_refl] >> Rewr'
 >> MATCH_MP_TAC max_le2_imp
 >> CONJ_TAC
 >- (MATCH_MP_TAC integral_mono >> RW_TAC std_ss [le_abs] \\
     MATCH_MP_TAC integrable_abs >> art [])
 >> MATCH_MP_TAC integral_mono >> RW_TAC std_ss []
 >- (MATCH_MP_TAC integrable_cmul >> art [])
 >- (MATCH_MP_TAC integrable_abs >> art [])
 >> REWRITE_TAC [GSYM extreal_of_num_def, GSYM extreal_ainv_def, GSYM neg_minus1]
 >> REWRITE_TAC [le_abs]
QED

(* special version, RHS is for `pos_fn_integral` *)
Theorem integral_triangle_ineq' :
    !m f. measure_space m /\ integrable m f ==>
          abs (integral m f) <= pos_fn_integral m (abs o f)
Proof
    rpt STRIP_TAC
 >> Suff `pos_fn_integral m (abs o f) = integral m (abs o f)`
 >- (Rewr' >> MATCH_MP_TAC integral_triangle_ineq >> art [])
 >> MATCH_MP_TAC EQ_SYM
 >> MATCH_MP_TAC integral_pos_fn
 >> RW_TAC std_ss [o_DEF, abs_pos]
QED

(* Theorem 11.2 (ii) [1, p.89-90], cf. pos_fn_integral_null_set *)
Theorem integral_null_set :
    !m f N. measure_space m /\
            f IN measurable (m_space m, measurable_sets m) Borel /\
            N IN null_set m ==> integrable m (\x. f x * indicator_fn N x) /\
                                 (integral m (\x. f x * indicator_fn N x) = 0)
Proof
    rpt GEN_TAC
 >> SIMP_TAC std_ss [IN_NULL_SET, null_set_def] >> STRIP_TAC
 >> Q.ABBREV_TAC `fi = \i:num x. min ((abs o f) x) &i`
 >> Know `!i x. 0 <= fi i x`
 >- (rpt GEN_TAC >> Q.UNABBREV_TAC `fi` \\
     RW_TAC std_ss [le_min, abs_pos] \\
     RW_TAC real_ss [extreal_of_num_def, extreal_le_eq]) >> DISCH_TAC
 >> Know `!x. (abs o f) x = sup (IMAGE (\i. fi i x) univ(:num))`
 >- (GEN_TAC >> Q.UNABBREV_TAC `fi` \\
     SIMP_TAC std_ss [o_DEF] \\
     Cases_on `(f x = PosInf) \/ (f x = NegInf)` (* special case *)
     >- (POP_ASSUM STRIP_ASSUME_TAC \\ (* 2 subgoals, same tactics *)
         (ASM_SIMP_TAC std_ss [extreal_abs_def, min_infty] \\
          MATCH_MP_TAC EQ_SYM \\
          Suff `IMAGE (\i. &i) univ(:num) = \x. ?n. x = &n` >- rw [sup_num] \\
          RW_TAC std_ss [Once EXTENSION, IN_IMAGE, IN_UNIV, IN_APP])) >> fs [] \\
     MATCH_MP_TAC EQ_SYM >> RW_TAC std_ss [sup_eq'] \\
     POP_ASSUM (STRIP_ASSUME_TAC o BETA_RULE o
                (REWRITE_RULE [IN_IMAGE, IN_UNIV])) >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.PAT_X_ASSUM `y = min (abs (f x)) (&x')` (ONCE_REWRITE_TAC o wrap) \\
       RW_TAC std_ss [min_le, le_refl],
       (* goal 2 (of 2) *)
      `abs (f x) <> PosInf` by PROVE_TAC [abs_not_infty] \\
       POP_ASSUM (STRIP_ASSUME_TAC o
                  (MATCH_MP (Q.SPEC `abs ((f :'a -> extreal) x)` SIMP_EXTREAL_ARCH))) \\
       Cases_on `&n <= y` (* easy case *)
       >- (MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `&n` >> art []) \\
       Q.PAT_X_ASSUM `!z. P ==> z <= y` MATCH_MP_TAC \\
       Q.EXISTS_TAC `&n` >> PROVE_TAC [min_reduce] ]) >> DISCH_TAC
 >> Q.ABBREV_TAC `fi' = \i:num x. fi i x * indicator_fn N x`
 >> Know `!i x. 0 <= fi' i x`
 >- (rpt GEN_TAC >> Q.UNABBREV_TAC `fi'` >> BETA_TAC \\
     MATCH_MP_TAC le_mul >> art [INDICATOR_FN_POS]) >> DISCH_TAC
 >> Know `!x. (abs o f) x * indicator_fn N x = sup (IMAGE (\i. fi' i x) univ(:num))`
 >- (GEN_TAC >> Q.UNABBREV_TAC `fi'` >> BETA_TAC >> POP_ORW \\
    `indicator_fn N x <> PosInf /\ indicator_fn N x <> NegInf`
       by PROVE_TAC [INDICATOR_FN_NOT_INFTY] \\
    `0 <= indicator_fn N x` by PROVE_TAC [INDICATOR_FN_POS] \\
    `?r. indicator_fn N x = Normal r` by METIS_TAC [extreal_cases] \\
    `0 <= r` by METIS_TAC [extreal_of_num_def, extreal_le_eq] \\
     ONCE_REWRITE_TAC [mul_comm] \\
     Q.PAT_X_ASSUM `indicator_fn N x = Normal r` (ONCE_REWRITE_TAC o wrap) \\
     POP_ASSUM (rw o wrap o (MATCH_MP sup_cmul))) >> DISCH_TAC
 >> `sigma_algebra (m_space m,measurable_sets m)` by PROVE_TAC [measure_space_def]
 (* applying Beppo Levi *)
 >> Know `pos_fn_integral m (\x. (abs o f) x * indicator_fn N x) =
          sup (IMAGE (\i. pos_fn_integral m (fi' i)) univ(:num))`
 >- (MATCH_MP_TAC lebesgue_monotone_convergence >> art [] \\
     Q.UNABBREV_TAC `fi'` >> REV_FULL_SIMP_TAC bool_ss [] \\
     rpt STRIP_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR \\
       ASM_SIMP_TAC std_ss [subsets_def] \\
       Q.UNABBREV_TAC `fi` >> BETA_TAC \\
      `(\x. min ((abs o f) x) (&i)) = (\x. min ((abs o f) x) ((\x. &i) x))`
          by METIS_TAC [] >> POP_ORW \\
       MATCH_MP_TAC IN_MEASURABLE_BOREL_MIN >> art [] \\
       CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS' >> art []) \\
       MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST' >> art [],
       (* goal 2 (of 2) *)
       RW_TAC std_ss [ext_mono_increasing_suc] \\
       reverse (Cases_on `x IN N`)
       >- (ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rzero, le_refl]) \\
       ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rone] \\
       Q.UNABBREV_TAC `fi` >> BETA_TAC \\
      `(&i :real) < &(SUC i)` by RW_TAC real_ss [] \\
      `(&i :extreal) < &(SUC i)` by METIS_TAC [extreal_lt_eq, extreal_of_num_def] \\
       RW_TAC std_ss [o_DEF, extreal_min_def, le_refl] >| (* 3 subgoals *)
       [ (* goal 3.1 (of 3) *)
         REV_FULL_SIMP_TAC bool_ss [GSYM extreal_lt_def] \\
         METIS_TAC [let_trans, lt_antisym],
         (* goal 3.1 (of 3) *)
         REV_FULL_SIMP_TAC bool_ss [GSYM extreal_lt_def] \\
         MATCH_MP_TAC lt_imp_le >> art [],
         (* goal 3.3 (of 3) *)
         MATCH_MP_TAC lt_imp_le >> art [] ] ]) >> DISCH_TAC
 >> Know `!i. pos_fn_integral m (fi' i) <= pos_fn_integral m (\x. &i * indicator_fn N x)`
 >- (GEN_TAC >> MATCH_MP_TAC pos_fn_integral_mono \\
     RW_TAC std_ss [] >> qunabbrevl_tac [`fi'`, `fi`] >> BETA_TAC \\
     reverse (Cases_on `x IN N`)
     >- (ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rzero, le_refl]) \\
     ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rone, min_le2])
 >> Know `!i. pos_fn_integral m (\x. &i * indicator_fn N x) =
              &i * pos_fn_integral m (indicator_fn N)`
 >- (GEN_TAC >> SIMP_TAC std_ss [extreal_of_num_def] \\
     MATCH_MP_TAC pos_fn_integral_cmul \\
     RW_TAC real_ss [INDICATOR_FN_POS, extreal_of_num_def, extreal_lt_eq])
 >> ASM_SIMP_TAC std_ss [pos_fn_integral_indicator, mul_rzero]
 >> DISCH_THEN K_TAC >> DISCH_TAC
 >> Know `!i. pos_fn_integral m (fi' i) = 0`
 >- (GEN_TAC >> RW_TAC std_ss [GSYM le_antisym] \\
     MATCH_MP_TAC pos_fn_integral_pos >> art [])
 >> POP_ASSUM K_TAC >> DISCH_TAC
 >> Know `sup (IMAGE (\i. pos_fn_integral m (fi' i)) univ(:num)) = 0`
 >- (POP_ORW \\
     Suff `IMAGE (\i. (0 :extreal)) univ(:num) = (\y. y = 0)`
     >- (Rewr' >> REWRITE_TAC [sup_const]) \\
     RW_TAC std_ss [Once EXTENSION, IN_IMAGE, IN_UNIV] \\
     SIMP_TAC std_ss [IN_APP])
 >> POP_ASSUM K_TAC
 >> DISCH_THEN ((REV_FULL_SIMP_TAC bool_ss) o wrap)
 >> Know `pos_fn_integral m (\x. (abs o f) x * indicator_fn N x) = 0`
 >- (Q.PAT_X_ASSUM `!x. (abs o f) x = _` (ONCE_REWRITE_TAC o wrap) \\
     ASM_SIMP_TAC std_ss [])
 >> POP_ASSUM K_TAC >> DISCH_TAC
 >> Q.PAT_X_ASSUM `!i x. 0 <= fi' i x` K_TAC
 >> Q.UNABBREV_TAC `fi'`
 (* integrable m (\x. f x * indicator_fn N x) *)
 >> STRONG_CONJ_TAC
 >- (SIMP_TAC std_ss [integrable_def] \\
     CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR \\
                  ASM_SIMP_TAC std_ss [subsets_def]) \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Suff `pos_fn_integral m (fn_plus (\x. f x * indicator_fn N x)) <= 0`
       >- METIS_TAC [neg_not_posinf] \\
       POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) \\
       REWRITE_TAC [GSYM INDICATOR_FN_ABS_MUL] \\
       MATCH_MP_TAC pos_fn_integral_mono \\
       RW_TAC std_ss [o_DEF, FN_PLUS_LE_ABS, FN_PLUS_POS],
       (* goal 2 (of 2) *)
       Suff `pos_fn_integral m (fn_minus (\x. f x * indicator_fn N x)) <= 0`
       >- METIS_TAC [neg_not_posinf] \\
       POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) \\
       REWRITE_TAC [GSYM INDICATOR_FN_ABS_MUL] \\
       MATCH_MP_TAC pos_fn_integral_mono \\
       RW_TAC std_ss [o_DEF, FN_MINUS_LE_ABS, FN_MINUS_POS] ])
 >> DISCH_TAC
 >> REWRITE_TAC [GSYM abs_le_0]
 >> Q.PAT_X_ASSUM `_ = 0` (ONCE_REWRITE_TAC o wrap o SYM)
 >> REWRITE_TAC [GSYM INDICATOR_FN_ABS_MUL]
 >> MATCH_MP_TAC integral_triangle_ineq' >> art []
QED

(* Theorem 11.2 (i) [1, p.89] *)
Theorem integral_abs_eq_0 :
    !m f. measure_space m /\
          f IN measurable (m_space m, measurable_sets m) Borel ==>
        ((integral m (abs o f) = 0) <=> AE x::m. (abs o f) x = 0) /\
        ((AE x::m. (abs o f) x = 0) <=> (measure m {x | x IN m_space m /\ f x <> 0} = 0))
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘sigma_algebra (measurable_space m)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
 >> Know `{x | x IN m_space m /\ f x <> 0} IN measurable_sets m`
 >- (`{x | x IN m_space m /\ f x <> 0} = {x | f x <> 0} INTER m_space m` by SET_TAC [] \\
     POP_ORW >> METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]) >> DISCH_TAC
 >> ONCE_REWRITE_TAC [CONJ_SYM]
 >> STRONG_CONJ_TAC (* by definition of AE and null_set *)
 >- (reverse EQ_TAC
     >- (RW_TAC std_ss [AE_ALT, null_set_def] \\
         Q.EXISTS_TAC `{x | x IN m_space m /\ f x <> 0}` \\
         ASM_REWRITE_TAC [SUBSET_REFL, abs_eq_0]) \\
     RW_TAC std_ss [AE_ALT, null_set_def] \\
     RW_TAC std_ss [Once CONJ_SYM, Once (GSYM le_antisym)] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       IMP_RES_TAC MEASURE_SPACE_POSITIVE \\
       fs [positive_def, measure_def, measurable_sets_def],
       (* goal 2 (of 2) *)
       Q.PAT_X_ASSUM `measure m N = 0`
         ((GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites) o wrap o SYM) \\
       IMP_RES_TAC MEASURE_SPACE_INCREASING \\
       MATCH_MP_TAC INCREASING >> fs [abs_eq_0] ]) >> DISCH_TAC
 (* RHS ==> LHS, by AE and integral_null_set *)
 >> reverse EQ_TAC
 >- (SIMP_TAC bool_ss [AE_ALT, GSYM IN_NULL_SET] >> STRIP_TAC \\
     Know `(abs o f) IN measurable (m_space m, measurable_sets m) Borel`
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS' >> art []) >> DISCH_TAC \\
    `!x. 0 <= (abs o f) x` by METIS_TAC [o_DEF, abs_pos] \\
    `N IN measurable_sets m /\ (measure m N = 0)` by METIS_TAC [IN_NULL_SET, null_set_def] \\
     Know `{x | x IN m_space m /\ (abs o f) x <> 0} IN measurable_sets m`
     >- (ASM_SIMP_TAC std_ss [o_DEF, abs_eq_0]) >> DISCH_TAC \\
     MP_TAC (Q.SPECL [`m`, `abs o f`,
                      `{x | x IN m_space m /\ (abs o f) x <> 0}`] integral_split) \\
     RW_TAC bool_ss [] >> POP_ASSUM K_TAC \\
     MP_TAC (Q.SPECL [`m`, `abs o f`,
                      `{x | x IN m_space m /\ (abs o f) x <> 0}`] integral_null_set) \\
     Know `{x | x IN m_space m /\ (abs o f) x <> 0} IN null_set m`
     >- (RW_TAC bool_ss [null_set_def, IN_NULL_SET] \\
         RW_TAC bool_ss [Once CONJ_SYM, Once (GSYM le_antisym)] >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           IMP_RES_TAC MEASURE_SPACE_POSITIVE \\
           fs [positive_def, measure_def, measurable_sets_def],
           (* goal 2 (of 2) *)
           Q.PAT_X_ASSUM `measure m N = 0`
             ((GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites) o wrap o SYM) \\
           IMP_RES_TAC MEASURE_SPACE_INCREASING \\
           MATCH_MP_TAC INCREASING >> art [] ]) \\
     RW_TAC bool_ss [add_lzero] \\
     Suff `integral m
             (\x. (abs o f) x *
                  indicator_fn (m_space m DIFF {x | x IN m_space m /\ (abs o f) x <> 0}) x) =
           integral m (\x. 0)` >- (Rewr' >> MATCH_MP_TAC integral_zero >> art []) \\
     MATCH_MP_TAC integral_cong >> art [] \\
     RW_TAC bool_ss [] \\
     reverse (Cases_on `x IN (m_space m DIFF {x | x IN m_space m /\ (abs o f) x <> 0})`)
     >- (ASM_SIMP_TAC bool_ss [indicator_fn_def, mul_rzero]) \\
     POP_ASSUM MP_TAC \\
     RW_TAC bool_ss [IN_DIFF, GSPECIFICATION, mul_lzero])
 (* LHS ==> RHS, by markov_ineq *)
 >> DISCH_TAC >> Q.PAT_X_ASSUM `_ <=> (measure m _ = 0)` (ONCE_REWRITE_TAC o wrap)
 >> REWRITE_TAC [GSYM abs_gt_0]
 >> `{x | x IN m_space m /\ 0 < abs (f x)} = {x | 0 < abs (f x)} INTER m_space m`
       by SET_TAC [] >> POP_ORW
 >> Know `{x | 0 < abs (f x)} INTER m_space m =
          BIGUNION (IMAGE (\n. {x | 1 / &(SUC n) <= abs (f x)} INTER m_space m) UNIV)`
 >- (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_BIGUNION_IMAGE, IN_UNIV,
                    GSPECIFICATION] \\
     reverse EQ_TAC >> rpt STRIP_TAC >> RW_TAC std_ss []
     >- (MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC `1 / &(SUC n)` >> art [] \\
        `&(SUC n) = Normal &(SUC n)` by METIS_TAC [extreal_of_num_def] >> POP_ORW \\
         MATCH_MP_TAC lt_div >> RW_TAC real_ss [lt_01]) \\
     MP_TAC (Q.SPEC `inv (abs (f x))` SIMP_EXTREAL_ARCH) \\
    `abs (f x) <> 0` by PROVE_TAC [lt_le] \\
    `inv (abs (f x)) <> PosInf` by PROVE_TAC [inv_not_infty] \\
     RW_TAC std_ss [] \\
     Q.EXISTS_TAC `n` \\
     Cases_on `abs (f x) = PosInf` >- art [le_infty] \\
    `&(SUC n) <> (0 :real)` by RW_TAC real_ss [] \\
    `&(SUC n) <> (0 :extreal)` by METIS_TAC [extreal_of_num_def, extreal_11] \\
    `abs (f x) <> NegInf` by METIS_TAC [pos_not_neginf, lt_imp_le] \\
    `?r. abs (f x) = Normal r` by METIS_TAC [extreal_cases] \\
     FULL_SIMP_TAC std_ss [extreal_of_num_def, extreal_div_eq,
                           extreal_11, extreal_le_eq, extreal_lt_eq] \\
     rfs [extreal_inv_eq, extreal_le_eq, REAL_INV_1OVER] \\
     rfs [REAL_LE_LDIV_EQ, REAL_LT_LDIV_EQ] \\
     MATCH_MP_TAC REAL_LE_TRANS \\
     Q.EXISTS_TAC `r * &n` >> art [] \\
    `(&n :real) < &SUC n` by RW_TAC real_ss [] \\
     ASM_SIMP_TAC real_ss [REAL_LE_LMUL]) >> DISCH_TAC
 >> Know `(abs o f) IN measurable (m_space m,measurable_sets m) Borel`
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS' >> art []) >> DISCH_TAC
 >> Know `{x | 0 < (abs o f) x} INTER m_space m IN measurable_sets m`
 >- METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]
 >> ASM_SIMP_TAC std_ss [o_DEF] >> DISCH_TAC
 >> Know `!n. {x | 1 / &SUC n <= (abs o f) x} INTER m_space m IN measurable_sets m`
 >- METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE]
 >> ASM_SIMP_TAC std_ss [o_DEF] >> DISCH_TAC
 >> IMP_RES_TAC MEASURE_SPACE_COUNTABLY_SUBADDITIVE
 >> Q.ABBREV_TAC `g = \n. {x | 1 / &SUC n <= abs (f x)} INTER m_space m`
 >> RW_TAC std_ss [GSYM le_antisym, Once CONJ_SYM]
 >- (IMP_RES_TAC MEASURE_SPACE_POSITIVE \\
     fs [positive_def, measurable_sets_def, measure_def])
 >> Know `measure m (BIGUNION (IMAGE g UNIV)) <= suminf (measure m o g)`
 >- (MATCH_MP_TAC COUNTABLY_SUBADDITIVE >> art [] \\
     Q.UNABBREV_TAC `g` >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]) >> DISCH_TAC
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC `suminf (measure m o g)` >> art []
 >> Know `!n. (measure m o g) n <= inv (1 / &SUC n) * integral m (abs o f)`
 >- (GEN_TAC >> Q.UNABBREV_TAC `g` \\
     GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [o_DEF] \\
     SIMP_TAC std_ss [] \\
     MATCH_MP_TAC markov_ineq >> art [] \\
     reverse CONJ_TAC
     >- (`&(SUC n) = Normal &(SUC n)` by METIS_TAC [extreal_of_num_def] >> POP_ORW \\
         MATCH_MP_TAC lt_div >> art [lt_01] \\
         RW_TAC real_ss [extreal_of_num_def, extreal_lt_eq]) \\
     MATCH_MP_TAC integral_abs_imp_integrable >> art [])
 >> RW_TAC bool_ss [mul_rzero]
 >> Know `!n. (measure m o g) n = 0`
 >- (RW_TAC bool_ss [GSYM le_antisym, Once CONJ_SYM] \\
     IMP_RES_TAC MEASURE_SPACE_POSITIVE \\
     Q.UNABBREV_TAC `g` >> SIMP_TAC std_ss [o_DEF] \\
     fs [positive_def, measure_def, measurable_sets_def])
 >> POP_ASSUM K_TAC >> DISCH_TAC
 >> REWRITE_TAC [le_lt] >> DISJ2_TAC
 >> MATCH_MP_TAC ext_suminf_zero >> art []
QED

(* NOTE: changed ‘nonneg f’ to ‘!x. x IN m_space m ==> 0 <= f x’ *)
Theorem pos_fn_integral_eq_0 : (* was: positive_integral_0_iff *)
    !m f. measure_space m /\ (!x. x IN m_space m ==> 0 <= f x) /\
          f IN measurable (m_space m, measurable_sets m) Borel ==>
        ((pos_fn_integral m f = 0) <=> (measure m {x | x IN m_space m /\ f x <> 0} = 0))
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [`m`, `f`] integral_abs_eq_0)
 >> RW_TAC std_ss []
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
 >> Know `integral m (abs o f) = pos_fn_integral m (abs o f)`
 >- (MATCH_MP_TAC integral_pos_fn >> rw [abs_pos])
 >> Rewr'
 >> Suff ‘pos_fn_integral m f = pos_fn_integral m (abs o f)’ >- rw []
 >> MATCH_MP_TAC pos_fn_integral_cong
 >> rw [abs_pos]
 >> METIS_TAC [abs_refl]
QED

Theorem integral_eq_0 :
    !m f. f IN measurable (m_space m, measurable_sets m) Borel /\
          measure_space m /\ (AE x::m. 0 <= f x) ==>
        ((integral m f = 0) <=> (measure m {x | x IN m_space m /\ f x <> 0} = 0))
Proof
    qx_genl_tac [‘M’, ‘u’] >> STRIP_TAC
 >> MP_TAC (Q.SPECL [`M`, `u`] integral_abs_eq_0) >> RW_TAC std_ss []
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
 >> REWRITE_TAC [integral_def]
 >> `nonneg (abs o u)` by PROVE_TAC [nonneg_abs]
 >> Know `fn_minus (abs o u) = (\x. 0)`
 >- (MATCH_MP_TAC nonneg_fn_minus >> art []) >> Rewr'
 >> Know `pos_fn_integral M (fn_plus u) = pos_fn_integral M (fn_plus (abs o u))`
 >- (MATCH_MP_TAC pos_fn_integral_cong_AE \\
     RW_TAC std_ss [FN_PLUS_POS] \\
     fs [AE_ALT, GSYM IN_NULL_SET] \\
     Q.EXISTS_TAC `N` >> art [] \\
     Suff `{x | x IN m_space M /\ u^+ x <> (abs o u)^+ x} =
           {x | x IN m_space M /\ ~(0 <= u x)}` >- rw [] \\
     RW_TAC std_ss [Once EXTENSION, GSPECIFICATION, fn_plus_def] \\
     reverse EQ_TAC >> rpt STRIP_TAC >> RW_TAC std_ss []
     >- (fs [GSYM extreal_lt_def] \\
         `~(0 < u x)` by METIS_TAC [lt_antisym] >> fs [] \\
         `u x <> 0` by METIS_TAC [lt_le] \\
         `0 < abs (u x)` by METIS_TAC [abs_gt_0] \\
          METIS_TAC [lt_le]) \\
     fs [le_lt] >- (fs [] >> `u x <> 0` by METIS_TAC [lt_le] \\
                   `0 < abs (u x)` by METIS_TAC [abs_gt_0] \\
                    fs [] >> METIS_TAC [abs_refl, lt_imp_le]) \\
     `~(0 < u x)` by METIS_TAC [lt_refl] \\
     `~(0 < abs (u x))` by METIS_TAC [abs_0] >> fs []) >> Rewr'
 >> Suff `pos_fn_integral M (fn_minus u) = pos_fn_integral M (\x. 0)` >- rw []
 >> MATCH_MP_TAC pos_fn_integral_cong_AE
 >> RW_TAC std_ss [FN_MINUS_POS, le_refl]
 >> fs [AE_ALT, GSYM IN_NULL_SET]
 >> Q.EXISTS_TAC `N` >> art []
 >> Suff `{x | x IN m_space M /\ u^- x <> 0} =
          {x | x IN m_space M /\ ~(0 <= u x)}` >- rw []
 >> RW_TAC std_ss [Once EXTENSION, GSPECIFICATION, fn_minus_def]
 >> reverse EQ_TAC >> rpt STRIP_TAC >> RW_TAC std_ss []
 >- (fs [GSYM extreal_lt_def] >> rfs [] \\
     `u x <> 0` by METIS_TAC [lt_le] >> METIS_TAC [neg_eq0])
 >> `~(u x < 0)` by METIS_TAC [extreal_lt_def] >> fs []
QED

val indicator_fn_pos_le = INDICATOR_FN_POS;

Theorem pos_fn_integral_cmult' :
    !f c m. measure_space m /\ 0 <= c /\
            f IN measurable (m_space m, measurable_sets m) Borel ==>
           (pos_fn_integral m (\x. max 0 (c * f x)) =
            c * pos_fn_integral m (\x. max 0 (f x)))
Proof
    RW_TAC std_ss []
 >> Q.ABBREV_TAC `g = (\x. max 0 (f x))`
 >> Know `!x. max 0 (c * f x) = c * g x`
 >- (RW_TAC std_ss [Abbr ‘g’, extreal_max_def, mul_rzero]
     >- (UNDISCH_TAC ``0 <= c * f x`` >> ONCE_REWRITE_TAC [MONO_NOT_EQ] \\
         RW_TAC std_ss [GSYM extreal_lt_def] >> ONCE_REWRITE_TAC [GSYM lt_neg] \\
         SIMP_TAC std_ss [neg_0, GSYM mul_rneg] >> MATCH_MP_TAC lt_mul \\
         CONJ_TAC
         >- (SIMP_TAC std_ss [extreal_lt_def] >> POP_ASSUM MP_TAC \\
             ONCE_REWRITE_TAC [MONO_NOT_EQ] >> RW_TAC std_ss [] \\
            `c = 0` by METIS_TAC [le_antisym] THEN ASM_SIMP_TAC std_ss [mul_lzero]) \\
         ONCE_REWRITE_TAC [GSYM lt_neg] \\
         ASM_SIMP_TAC std_ss [neg_0, extreal_lt_def, neg_neg]) \\
     REWRITE_TAC [GSYM le_antisym] \\
     CONJ_TAC >- METIS_TAC [le_mul] \\
     METIS_TAC [le_lt, extreal_lt_def]) >> DISC_RW_KILL
 >> Know `g IN measurable (m_space m,measurable_sets m) Borel`
 >- (Q.UNABBREV_TAC `g` THEN ONCE_REWRITE_TAC [METIS []
       ``!x. (\x. max 0 (f x)) = (\x. max ((\x. 0) x) ((\x. f x) x))``] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX \\
     ONCE_REWRITE_TAC [METIS [ETA_AX]  ``(\x. f x) = f``] \\
     FULL_SIMP_TAC std_ss [measure_space_def] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST >> METIS_TAC [])
 >> DISCH_TAC
 >> `!x. 0 <= g x` by METIS_TAC [le_max1]
 >> reverse (Cases_on `c = PosInf`)
 >- (`c <> NegInf` by METIS_TAC [le_infty, le_trans, num_not_infty] THEN
     `c = Normal (real c)` by METIS_TAC [normal_real] THEN
     POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
     MATCH_MP_TAC pos_fn_integral_cmul THEN ASM_SIMP_TAC std_ss [] THEN
     ASM_SIMP_TAC std_ss [GSYM extreal_le_def, normal_real, GSYM extreal_of_num_def] THEN
     METIS_TAC [normal_real])
 (* c = PosInf *)
 >> ASM_SIMP_TAC std_ss []
 >> Know `pos_fn_integral m (\x. (\x. c * g x) x *
            indicator_fn (({x | g x = 0} INTER m_space m) UNION ({x | 0 < g x} INTER m_space m)) x) =
          pos_fn_integral m (\x. (\x. c * g x) x * indicator_fn ({x | g x = 0} INTER m_space m) x) +
          pos_fn_integral m (\x. (\x. c * g x) x * indicator_fn ({x | 0 < g x} INTER m_space m) x)`
 >- (MATCH_MP_TAC pos_fn_integral_disjoint_sets \\
     ASM_SIMP_TAC std_ss [] \\
     CONJ_TAC
     >- (SIMP_TAC std_ss [DISJOINT_DEF, IN_INTER, EXTENSION, NOT_IN_EMPTY] \\
         GEN_TAC >> SIMP_TAC std_ss [GSPECIFICATION] \\
         ASM_CASES_TAC ``g (x:'a) <> 0:extreal`` >> FULL_SIMP_TAC std_ss [lt_refl]) \\
     CONJ_TAC
     >- (`{x | g x = 0} = PREIMAGE g {x | x = 0}` by SET_TAC [PREIMAGE_def] \\
         POP_ASSUM (fn th => REWRITE_TAC [th]) >> FULL_SIMP_TAC std_ss [IN_MEASURABLE] \\
         FULL_SIMP_TAC std_ss [space_def, subsets_def] \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
         ONCE_REWRITE_TAC [SET_RULE ``{x | x = 0} = {0}``] \\
         SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_SING, extreal_of_num_def]) \\
     CONJ_TAC
     >- (`{x | 0 < g x} = PREIMAGE g {x | 0 < x}` by SET_TAC [PREIMAGE_def] \\
         POP_ASSUM (fn th => REWRITE_TAC [th]) THEN FULL_SIMP_TAC std_ss [IN_MEASURABLE] \\
         FULL_SIMP_TAC std_ss [space_def, subsets_def] \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
         SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_OR, extreal_of_num_def]) \\
     CONJ_TAC
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES >> Q.EXISTS_TAC `(\x. PosInf)` \\
         Q.EXISTS_TAC `g` >> ASM_SIMP_TAC std_ss [] \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST >> Q.EXISTS_TAC `PosInf` \\
         METIS_TAC [measure_space_def]) \\
     rpt STRIP_TAC \\
     MATCH_MP_TAC le_mul >> ASM_SIMP_TAC std_ss [le_infty])
 >> RW_TAC std_ss []
 >> Know `pos_fn_integral m (\x. PosInf * g x) =
          pos_fn_integral m (\x. PosInf * g x *
           indicator_fn
             ({x | g x = 0} INTER m_space m UNION
              {x | 0 < g x} INTER m_space m) x)`
 >- (MATCH_MP_TAC pos_fn_integral_cong \\
     ASM_SIMP_TAC std_ss [le_mul, le_infty] \\
     CONJ_TAC
     >- (rpt STRIP_TAC \\
         MATCH_MP_TAC le_mul >> ASM_SIMP_TAC std_ss [le_mul, le_infty] \\
         SIMP_TAC std_ss [indicator_fn_pos_le]) \\
     RW_TAC std_ss [UNION_DEF, IN_INTER, GSPECIFICATION] \\
     ASM_SIMP_TAC std_ss [indicator_fn_def, GSPECIFICATION] \\
     ONCE_REWRITE_TAC [DISJ_COMM] \\
     GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] \\
     ASM_SIMP_TAC std_ss [GSYM le_lt, mul_rone])
 >> DISC_RW_KILL
 >> ASM_SIMP_TAC std_ss []
 >> Know `pos_fn_integral m
            (\x. PosInf * g x * indicator_fn ({x | g x = 0} INTER m_space m) x) =
          pos_fn_integral m (\x. 0)`
 >- (MATCH_MP_TAC pos_fn_integral_cong >> ASM_SIMP_TAC std_ss [le_refl] \\
     CONJ_TAC
     >- (rpt STRIP_TAC >> MATCH_MP_TAC le_mul >> ASM_SIMP_TAC std_ss [le_infty, le_mul] \\
         SIMP_TAC std_ss [indicator_fn_pos_le]) \\
     RW_TAC std_ss [] >> ASM_SIMP_TAC std_ss [indicator_fn_def, GSPECIFICATION, IN_INTER] \\
     COND_CASES_TAC >> ASM_SIMP_TAC std_ss [mul_rone, mul_rzero])
 >> DISC_RW_KILL
 >> ASM_SIMP_TAC std_ss [pos_fn_integral_zero, add_lzero]
 >> Suff `pos_fn_integral m (\x. g x *
            indicator_fn (({x | g x = 0} INTER m_space m) UNION ({x | 0 < g x} INTER m_space m)) x) =
          pos_fn_integral m (\x. g x * indicator_fn (({x | g x = 0} INTER m_space m)) x) +
          pos_fn_integral m (\x. g x * indicator_fn (({x | 0 < g x} INTER m_space m)) x)` >|
  [ SIMP_TAC std_ss [] THEN DISCH_TAC,
    MATCH_MP_TAC pos_fn_integral_disjoint_sets THEN ASM_SIMP_TAC std_ss [] THEN
    CONJ_TAC THENL
    [SIMP_TAC std_ss [DISJOINT_DEF, IN_INTER, EXTENSION, NOT_IN_EMPTY] THEN
     GEN_TAC THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
     ASM_CASES_TAC ``g (x:'a) <> 0:extreal`` THEN FULL_SIMP_TAC std_ss [lt_refl],
     ALL_TAC] THEN
    CONJ_TAC THENL
    [`{x | g x = 0} = PREIMAGE g {x | x = 0}` by SET_TAC [PREIMAGE_def] THEN
     POP_ASSUM (fn th => REWRITE_TAC [th]) THEN FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
     FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ONCE_REWRITE_TAC [SET_RULE ``{x | x = 0} = {0}``] THEN
     SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_SING, extreal_of_num_def],
     ALL_TAC] THEN
    `{x | 0 < g x} = PREIMAGE g {x | 0 < x}` by SET_TAC [PREIMAGE_def] THEN
    POP_ASSUM (fn th => REWRITE_TAC [th]) THEN FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
    FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_OR, extreal_of_num_def] ]
 >> Suff `pos_fn_integral m g =
          pos_fn_integral m (\x. g x *
           indicator_fn
             ({x | g x = 0} INTER m_space m UNION
              {x | 0 < g x} INTER m_space m) x)` THENL
   [DISC_RW_KILL,
    MATCH_MP_TAC pos_fn_integral_cong THEN ASM_SIMP_TAC std_ss [le_mul, indicator_fn_pos_le] THEN
    RW_TAC std_ss [] THEN
    ASM_SIMP_TAC std_ss [UNION_DEF, INTER_DEF, indicator_fn_def, GSPECIFICATION] THEN
    ONCE_REWRITE_TAC [DISJ_COMM] THEN
    GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ASM_SIMP_TAC std_ss [GSYM le_lt, mul_rone]]
 >> ASM_SIMP_TAC std_ss []
 >> Suff `pos_fn_integral m
            (\x. g x * indicator_fn ({x | g x = 0} INTER m_space m) x) =
          pos_fn_integral m (\x. 0)` THENL
   [DISC_RW_KILL,
    MATCH_MP_TAC pos_fn_integral_cong THEN ASM_SIMP_TAC std_ss [le_refl] THEN
    CONJ_TAC THENL
    [rpt STRIP_TAC >> MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [le_infty, le_mul] THEN
     SIMP_TAC std_ss [indicator_fn_pos_le], ALL_TAC] THEN
    RW_TAC std_ss [] THEN ASM_SIMP_TAC std_ss [indicator_fn_def, GSPECIFICATION, IN_INTER] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [mul_rone, mul_rzero]]
 >> ASM_SIMP_TAC std_ss [pos_fn_integral_zero, add_lzero]
 >> Suff `pos_fn_integral m
            (\x. PosInf * g x * indicator_fn ({x | 0 < g x} INTER m_space m) x) =
          pos_fn_integral m (\x. PosInf * indicator_fn ({x | 0 < g x} INTER m_space m) x)` THENL
   [DISC_RW_KILL,
    MATCH_MP_TAC pos_fn_integral_cong THEN ASM_SIMP_TAC std_ss [le_infty] THEN
    ASM_SIMP_TAC std_ss [le_mul, indicator_fn_pos_le, le_infty] THEN
    RW_TAC std_ss [] THEN ASM_SIMP_TAC std_ss [indicator_fn_def, GSPECIFICATION, IN_INTER] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [mul_rone, mul_rzero] THEN
    `g x <> NegInf` by METIS_TAC [lt_infty, lte_trans, num_not_infty] THEN
    ASM_CASES_TAC ``g x = PosInf`` THEN ASM_SIMP_TAC std_ss [extreal_mul_def] THEN
    `g x = Normal (real (g x))` by ASM_SIMP_TAC std_ss [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
    SIMP_TAC std_ss [extreal_mul_def, GSYM extreal_11, GSYM extreal_lt_eq] THEN
    ASM_SIMP_TAC std_ss [GSYM extreal_of_num_def, normal_real] THEN
    `g x <> 0` by METIS_TAC [lt_imp_ne] THEN ASM_SIMP_TAC std_ss []]
 >> Suff `{x | 0 < g x} INTER m_space m IN measurable_sets m` THENL
   [DISCH_TAC,
    `{x | 0 < g x} = PREIMAGE g {x | 0 < x}` by SET_TAC [PREIMAGE_def] THEN
    POP_ASSUM (fn th => REWRITE_TAC [th]) THEN FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
    FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_OR, extreal_of_num_def]]
 >> ASM_SIMP_TAC std_ss [pos_fn_integral_cmul_infty]
 >> ASM_CASES_TAC ``measure m ({x | 0 < g x} INTER m_space m) = 0``
 >- (Suff `pos_fn_integral m
             (\x. g x * indicator_fn ({x | 0 < g x} INTER m_space m) x) = 0` THENL
     [DISC_RW_KILL,
      MATCH_MP_TAC pos_fn_integral_null_set THEN
      ASM_SIMP_TAC std_ss [null_sets, GSPECIFICATION]] THEN
     SIMP_TAC std_ss [mul_rzero])
 >> Suff `measure m ({x | 0 < g x} INTER m_space m) =
          measure m ({x | x IN m_space m /\
                        (\x. g x * indicator_fn ({x | 0 < g x} INTER m_space m) x) x <> 0})` THENL
   [DISCH_TAC,
    AP_TERM_TAC THEN SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
    GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [] THENL
    [ASM_SIMP_TAC std_ss [indicator_fn_def, GSPECIFICATION, IN_INTER] THEN
     ASM_SIMP_TAC std_ss [lt_imp_ne, mul_rone], ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THEN
    FULL_SIMP_TAC std_ss [extreal_not_lt] THEN `g x = 0` by METIS_TAC [le_antisym] THEN
    ASM_SIMP_TAC std_ss [mul_lzero]]
 >> Q.ABBREV_TAC `ff = (\x. g x * indicator_fn ({x | 0 < g x} INTER m_space m) x)`
 >> `measure m {x | x IN m_space m /\ ff x <> 0} <> 0` by METIS_TAC []
 >> Know `measure m {x | x IN m_space m /\ ff x <> 0} <> 0 <=>
          pos_fn_integral m ff <> 0`
 >- (ONCE_REWRITE_TAC [METIS [] ``(a = b:bool) = (~b = ~a)``] THEN
    SIMP_TAC std_ss [] THEN
    Know `!x. 0 <= ff x`
    >- (Q.UNABBREV_TAC `ff` >> GEN_TAC >> BETA_TAC \\
        MATCH_MP_TAC le_mul >> art [INDICATOR_FN_POS]) >> DISCH_TAC \\
    Know `pos_fn_integral m ff = integral m ff`
    >- (MATCH_MP_TAC EQ_SYM \\
        MATCH_MP_TAC integral_pos_fn >> art []) >> Rewr' \\
    MATCH_MP_TAC integral_eq_0 THEN (* was: pos_fn_integral_eq_0 *)
    Q.UNABBREV_TAC `ff` THEN ASM_SIMP_TAC std_ss [le_mul, indicator_fn_pos_le] THEN
    CONJ_TAC THENL
    [ALL_TAC,
     SIMP_TAC std_ss [AE_ALT, GSYM IN_NULL_SET, GSPECIFICATION] THEN
     SIMP_TAC std_ss [GSPEC_F, EMPTY_SUBSET, null_sets, GSPECIFICATION] THEN
     Q.EXISTS_TAC `{}` THEN METIS_TAC [measure_space_def, SIGMA_ALGEBRA, positive_def, subsets_def]] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN Q.EXISTS_TAC `g` THEN
    Q.EXISTS_TAC `indicator_fn ({x | 0 < g x} INTER m_space m)` THEN
    ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
    Q.EXISTS_TAC `{x | 0 < g x} INTER m_space m` THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    ASM_SIMP_TAC std_ss [] THEN
    `{x | 0 < g x} = PREIMAGE g {x | 0 < x}` by SET_TAC [PREIMAGE_def] THEN
    POP_ASSUM (fn th => REWRITE_TAC [th]) THEN FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
    FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_OR, extreal_of_num_def])
 >> DISCH_TAC
 >> Suff `0 <= pos_fn_integral m ff` THENL
   [DISCH_TAC,
    MATCH_MP_TAC pos_fn_integral_pos THEN Q.UNABBREV_TAC `ff` THEN
    ASM_SIMP_TAC std_ss [le_mul, indicator_fn_pos_le]]
 >> `0 < pos_fn_integral m ff` by METIS_TAC [le_lt]
 >> `pos_fn_integral m ff <> NegInf` by METIS_TAC [lt_infty, num_not_infty, lte_trans]
 >> Suff `PosInf * pos_fn_integral m ff = PosInf` THENL
   [DISC_RW_KILL,
    ASM_CASES_TAC ``pos_fn_integral m ff = PosInf`` THEN ASM_SIMP_TAC std_ss [extreal_mul_def] THEN
    `pos_fn_integral m ff = Normal (real (pos_fn_integral m ff))` by METIS_TAC [normal_real] THEN
    POP_ASSUM (fn th => ONCE_REWRITE_TAC[th]) THEN REWRITE_TAC [extreal_mul_def] THEN
    ASM_SIMP_TAC std_ss [GSYM extreal_11, GSYM extreal_lt_eq, GSYM extreal_of_num_def] THEN
    ASM_SIMP_TAC std_ss [normal_real] THEN METIS_TAC []]
 >> Suff `0 <= measure m {x | x IN m_space m /\ ff x <> 0}` THENL
   [DISCH_TAC, FULL_SIMP_TAC std_ss [measure_space_def, positive_def] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    Suff `{x | x IN m_space m /\ ff x <> 0} = PREIMAGE ff {x | x <> 0} INTER m_space m` THENL
    [DISC_RW_KILL, SIMP_TAC std_ss [PREIMAGE_def] THEN SET_TAC []] THEN
    Suff `ff IN measurable (m_space m,measurable_sets m) Borel` THENL
    [DISCH_TAC,
     Q.UNABBREV_TAC `ff` THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN Q.EXISTS_TAC `g` THEN
     Q.EXISTS_TAC `indicator_fn ({x | 0 < g x} INTER m_space m)` THEN
     ASM_SIMP_TAC std_ss [measure_space_def, positive_def] THEN
     MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
     Q.EXISTS_TAC `{x | 0 < g x} INTER m_space m` THEN
     CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
     ASM_SIMP_TAC std_ss [] THEN
     `{x | 0 < g x} = PREIMAGE g {x | 0 < x}` by SET_TAC [PREIMAGE_def] THEN
     POP_ASSUM (fn th => REWRITE_TAC [th]) THEN FULL_SIMP_TAC std_ss [IN_MEASURABLE] THEN
     FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_OR, extreal_of_num_def]] THEN
    FULL_SIMP_TAC std_ss [IN_MEASURABLE, subsets_def, space_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [SET_RULE ``{x | x <> 0} = UNIV DIFF {0}``] THEN
    MATCH_MP_TAC ALGEBRA_DIFF THEN SIMP_TAC std_ss [extreal_of_num_def, GSYM SPACE_BOREL] THEN
    ASSUME_TAC SIGMA_ALGEBRA_BOREL THEN `algebra Borel` by METIS_TAC [sigma_algebra_def] THEN
    ASM_SIMP_TAC std_ss [ALGEBRA_SPACE, BOREL_MEASURABLE_SETS_SING]]
 >> `0 < measure m {x | x IN m_space m /\ ff x <> 0}` by METIS_TAC [le_lt]
 >> Q.ABBREV_TAC `gg = {x | x IN m_space m /\ ff x <> 0}`
 >> `measure m gg <> NegInf` by METIS_TAC [lt_infty, lte_trans, num_not_infty]
 >> ASM_CASES_TAC ``measure m gg = PosInf``
 >> ASM_SIMP_TAC std_ss [extreal_mul_def]
 >> `measure m gg = Normal (real (measure m gg))` by METIS_TAC [normal_real]
 >> POP_ASSUM (fn th => ONCE_REWRITE_TAC[th])
 >> SIMP_TAC std_ss [extreal_mul_def]
 >> ASM_SIMP_TAC std_ss [GSYM extreal_11, GSYM extreal_lt_eq, GSYM extreal_of_num_def]
 >> ASM_SIMP_TAC std_ss [normal_real]
QED

Theorem pos_fn_integral_cmult :
    !f c m. measure_space m /\ 0 <= c /\
            f IN measurable (m_space m, measurable_sets m) Borel ==>
           (pos_fn_integral m (\x. c * fn_plus f x) = c * pos_fn_integral m (fn_plus f))
Proof
    rpt STRIP_TAC
 >> `(\x. c * fn_plus f x) = fn_plus (\x. c * f x)` by METIS_TAC [FN_PLUS_CMUL_full]
 >> POP_ORW >> SIMP_TAC std_ss [o_DEF, FN_PLUS_ALT']
 >> MATCH_MP_TAC pos_fn_integral_cmult' >> art []
QED

Theorem density_fn_plus :
    !M f. density M (fn_plus f) =
           (m_space M, measurable_sets M,
            (\A. pos_fn_integral M (\x. max 0 (f x * indicator_fn A x))))
Proof
    RW_TAC std_ss [density_def, density_measure_def, FUN_EQ_THM]
 >> Suff `!x. fn_plus f x * indicator_fn A x = max 0 (f x * indicator_fn A x)`
 >- rw []
 >> RW_TAC std_ss [FN_PLUS_ALT']
 >> Cases_on `x IN A`
 >> ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone, max_refl]
QED

Theorem pos_fn_integral_density' :
    !f g M. measure_space M /\
            f IN measurable (m_space M, measurable_sets M) Borel /\
            g IN measurable (m_space M, measurable_sets M) Borel /\
           (AE x::M. 0 <= f x) /\ (!x. 0 <= g x) ==>
      ((pos_fn_integral (m_space M, measurable_sets M,
                         (\A. pos_fn_integral M (\x. max 0 (f x * indicator_fn A x))))
                        (\x. max 0 (g x)) =
        pos_fn_integral M (\x. max 0 (f x * g x))))
Proof
  RW_TAC std_ss [GSYM density_fn_plus] THEN
  Suff `(\g. pos_fn_integral (density M (fn_plus f)) (\x. max 0 (g x)) =
             pos_fn_integral M (\x. max 0 (f x * g x))) g`
  >- (SIMP_TAC std_ss []) THEN
  MATCH_MP_TAC BOREL_INDUCT THEN (* induction on Borel functions *)
  Q.EXISTS_TAC `M` THEN ASM_SIMP_TAC std_ss [] THEN
  CONJ_TAC THEN1 (* Part I *)
  (RW_TAC std_ss [] THEN
   Know `pos_fn_integral (density M (fn_plus f)) (\x. max 0 (g' x)) =
         pos_fn_integral (density M (fn_plus f)) (\x. max 0 (f' x))` THEN1
   (MATCH_MP_TAC pos_fn_integral_cong THEN ASM_SIMP_TAC std_ss [le_max1] THEN
    reverse CONJ_TAC
    >- (RW_TAC std_ss [density_def, density_measure_def, m_space_def]) \\
    MATCH_MP_TAC measure_space_density' >> art []) THEN DISC_RW_KILL THEN
   ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC pos_fn_integral_cong THEN
   ASM_SIMP_TAC std_ss [le_max1]) THEN
  CONJ_TAC THEN1 (* Part II *)
  (GEN_TAC THEN ONCE_REWRITE_TAC [METIS [extreal_max_def, indicator_fn_pos_le]
    ``!x. max 0 (indicator_fn A x) = indicator_fn A x``] THEN
   ONCE_REWRITE_TAC [METIS [ETA_AX] ``(\x. indicator_fn A x) = indicator_fn A``] THEN
   DISCH_TAC THEN `A IN measurable_sets (density M (fn_plus f))` by
    ASM_SIMP_TAC std_ss [density_fn_plus, measurable_sets_def] THEN
   `measure_space (density M (fn_plus f))` by METIS_TAC [measure_space_density'] THEN
   ASM_SIMP_TAC std_ss [pos_fn_integral_indicator] THEN
   ASM_SIMP_TAC std_ss [density_fn_plus, measure_def]) THEN
  CONJ_TAC THEN1 (* Part III *)
  (RW_TAC std_ss [] THEN
   Suff `pos_fn_integral (density M (fn_plus f)) (\x. max 0 (c * f' x)) =
                   c * pos_fn_integral (density M (fn_plus f)) (\x. max 0 (f' x))` THENL
   [DISC_RW_KILL,
    MATCH_MP_TAC pos_fn_integral_cmult' THEN
    `measure_space (density M (fn_plus f))` by METIS_TAC [measure_space_density'] THEN
    ASM_SIMP_TAC std_ss [density_fn_plus, m_space_def, measurable_sets_def]] THEN
   ASM_SIMP_TAC std_ss [] THEN
   Suff `c * pos_fn_integral M (\x. max 0 ((\x. f x * f' x) x)) =
                   pos_fn_integral M (\x. max 0 (c * (\x. f x * f' x) x))` THENL
   [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
    MATCH_MP_TAC (GSYM pos_fn_integral_cmult') THEN
    ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN
    METIS_TAC []] THEN
   AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
   METIS_TAC [mul_comm, mul_assoc]) THEN
  CONJ_TAC THEN1 (* Part IV *)
  (RW_TAC std_ss [] THEN ASM_SIMP_TAC std_ss [add_ldistrib_pos] THEN
   Suff `!x. max 0 (f' x + g' x) = max 0 (f' x) + max 0 (g' x)` THENL
   [DISC_RW_KILL, METIS_TAC [extreal_max_def, le_add]] THEN
   Suff `pos_fn_integral (density M (fn_plus f)) (\x. (\x. max 0 (f' x)) x + (\x. max 0 (g' x)) x) =
                   pos_fn_integral (density M (fn_plus f)) (\x. max 0 (f' x)) +
                   pos_fn_integral (density M (fn_plus f)) (\x. max 0 (g' x))` THENL
   [SIMP_TAC std_ss [] THEN DISC_RW_KILL,
    MATCH_MP_TAC pos_fn_integral_add THEN
    `measure_space (density M (fn_plus f))` by METIS_TAC [measure_space_density'] THEN
    ASM_SIMP_TAC std_ss [le_max1] THEN ASM_SIMP_TAC std_ss [extreal_max_def] THEN
    ASM_SIMP_TAC std_ss [ETA_AX, density_fn_plus, m_space_def, measurable_sets_def]] THEN
   Suff `pos_fn_integral M (\x. max 0 (f x * f' x + f x * g' x)) =
                   pos_fn_integral M (\x. (\x. max 0 (f x * f' x)) x + (\x. max 0 (f x * g' x)) x)` THENL
   [DISC_RW_KILL,
    MATCH_MP_TAC pos_fn_integral_cong_AE THEN
    ASM_SIMP_TAC std_ss [le_max1, le_mul, le_add] THEN
    FULL_SIMP_TAC std_ss [AE_ALT, GSPECIFICATION, null_set_def] THEN
    Q.EXISTS_TAC `N` THEN ASM_SIMP_TAC std_ss [] THEN
    FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN RW_TAC std_ss [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [] THEN
    POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
    RW_TAC std_ss [extreal_max_def, add_rzero, add_lzero] THEN
    TRY (METIS_TAC [le_mul, le_add])] THEN
   MATCH_MP_TAC (GSYM pos_fn_integral_add) THEN
   ASM_SIMP_TAC std_ss [le_max1] THEN
   ONCE_REWRITE_TAC [METIS []
     ``!g. (\x. max 0 (f x * g x)) = (\x. max ((\x. 0) x) ((\x. f x * g x) x))``] THEN
   `(\x. 0) IN measurable (m_space M,measurable_sets M) Borel` by
     (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
      METIS_TAC [measure_space_def]) THEN
   CONJ_TAC THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
   FULL_SIMP_TAC std_ss [measure_space_def] THEN
   MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN METIS_TAC [measure_space_def]) THEN
  RW_TAC std_ss [] THEN (* Part V *)
  Suff `AE x::M. f x * sup (IMAGE (\i. u i x) UNIV) = sup (IMAGE (\i. f x * u i x) UNIV)` THENL
  [DISCH_TAC,
   FULL_SIMP_TAC std_ss [AE_ALT, GSPECIFICATION, null_set_def, SUBSET_DEF] THEN
   Q.EXISTS_TAC `N` THEN ASM_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THEN
   FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
   POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
   RW_TAC std_ss [] THEN
   Suff `f x * sup (IMAGE (\i. u i x) UNIV) =
     sup (IMAGE (\i. f x * (\i. u i x) i) UNIV)` THENL
   [SIMP_TAC std_ss [], ALL_TAC] THEN
   MATCH_MP_TAC (GSYM sup_cmult) THEN ASM_SIMP_TAC std_ss []] THEN
  Suff `pos_fn_integral (density M (fn_plus f))
       (\x. max 0 (sup (IMAGE (\i. u i x) univ(:num)))) =
      sup (IMAGE (\i. pos_fn_integral (density M (fn_plus f)) ((\i x. max 0 (u i x)) i)) UNIV)` THENL
  [DISC_RW_KILL,
   MATCH_MP_TAC lebesgue_monotone_convergence THEN
   ASM_SIMP_TAC std_ss [measure_space_density', le_max1] THEN
   ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, density_fn_plus] THEN
   CONJ_TAC THENL
   [GEN_TAC THEN
    Suff `!x. max 0 (u i x) = max ((\x. 0) x) ((\x. u i x) x)` THENL
    [DISC_RW_KILL, SIMP_TAC std_ss []] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX THEN
    `(\x. 0) IN measurable (m_space M,measurable_sets M) Borel` by
     (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
      METIS_TAC [measure_space_def]) THEN
    ONCE_REWRITE_TAC [METIS [ETA_AX] ``(\x. u i x) = u i``] THEN
    METIS_TAC [measure_space_def], ALL_TAC] THEN
   ASM_SIMP_TAC std_ss [extreal_max_def] THEN
   GEN_TAC THEN ASM_CASES_TAC ``!i:num. u i x = 0`` THENL
   [ASM_SIMP_TAC std_ss [IMAGE_DEF, IN_UNIV] THEN
    DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [] THEN
    POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN
    RW_TAC std_ss [le_sup] THEN POP_ASSUM (MATCH_MP_TAC) THEN
    ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN METIS_TAC [],
    ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THEN
   UNDISCH_TAC ``~(0 <= sup (IMAGE (\i. u i x) univ(:num)))`` THEN
   ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [le_lt] THEN
   SIMP_TAC std_ss [GSYM sup_lt] THEN Q.EXISTS_TAC `u i x` THEN
   CONJ_TAC THENL [ALL_TAC, METIS_TAC [le_lt]] THEN
   ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
   SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN METIS_TAC []] THEN
  ASM_SIMP_TAC std_ss [] THEN
  Suff `pos_fn_integral M (\x. max 0 (f x * sup (IMAGE (\i. u i x) univ(:num)))) =
                  pos_fn_integral M (\x. max 0 (sup (IMAGE (\i. f x * u i x) univ(:num))))` THENL
  [DISC_RW_KILL,
   MATCH_MP_TAC pos_fn_integral_cong_AE THEN ASM_SIMP_TAC std_ss [le_max1] THEN
   FULL_SIMP_TAC std_ss [AE_ALT, GSPECIFICATION, SUBSET_DEF, null_set_def] THEN
   Q.EXISTS_TAC `N'` THEN ASM_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
   POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss []] THEN
  Suff
   `sup (IMAGE (\i. pos_fn_integral M (\x. max 0 ((\i x. f x * u i x) i x))) univ(:num)) =
    pos_fn_integral M (\x. max 0 ((\x. sup (IMAGE (\i. f x * u i x) univ(:num))) x))` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  REWRITE_TAC [GSYM FN_PLUS_ALT'] THEN
  MATCH_MP_TAC (GSYM lebesgue_monotone_convergence_AE) THEN
  ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES THEN
   Q.EXISTS_TAC `f` THEN Q.EXISTS_TAC `u i` THEN ASM_SIMP_TAC std_ss [],
   ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [AE_ALT, GSYM IN_NULL_SET, GSPECIFICATION] THEN
  Q.EXISTS_TAC `N` THEN FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN
  RW_TAC std_ss [] THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
  [ASM_SIMP_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN
   ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THEN
   MATCH_MP_TAC le_lmul_imp THEN FULL_SIMP_TAC std_ss [ext_mono_increasing_def],
   ALL_TAC] THEN
  ASM_SIMP_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC [MONO_NOT_EQ] THEN RW_TAC std_ss [] THEN
  METIS_TAC [le_mul]
QED

Theorem pos_fn_integral_density :
    !m f g. measure_space m /\
            f IN measurable (m_space m, measurable_sets m) Borel /\
            g IN measurable (m_space m, measurable_sets m) Borel /\
           (AE x::m. 0 <= f x) /\ (!x. 0 <= g x)
       ==> (pos_fn_integral (density m (fn_plus f)) g =
            pos_fn_integral m (\x. (fn_plus f) x * g x))
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [`f`, `g`, `m`] pos_fn_integral_density')
 >> RW_TAC std_ss [GSYM density_fn_plus]
 >> Know `(\x. max 0 (g x)) = g`
 >- (RW_TAC std_ss [FUN_EQ_THM, GSYM fn_plus] \\
     Suff `fn_plus g = g` >- rw [] \\
     MATCH_MP_TAC nonneg_fn_plus >> rw [nonneg_def])
 >> DISCH_THEN (fs o wrap)
 >> POP_ASSUM K_TAC
 >> Suff `!x. max 0 ((\x. f x * g x) x) = (fn_plus f) x * g x` >- rw []
 >> GEN_TAC >> REWRITE_TAC [GSYM fn_plus]
 >> ONCE_REWRITE_TAC [mul_comm]
 >> ASM_SIMP_TAC std_ss [FN_PLUS_FMUL]
QED

(* ------------------------------------------------------------------------- *)
(*  Preliminary for Radon-Nikodym Theorem                                    *)
(* ------------------------------------------------------------------------- *)

Definition seq_sup_def :
   (seq_sup P 0       = @r. r IN P /\ sup P < r + 1) /\
   (seq_sup P (SUC n) = @r. r IN P /\ sup P < r + Normal ((1 / 2) pow (SUC n)) /\
                           (seq_sup P n) < r /\ r < sup P)
End

Theorem EXTREAL_SUP_SEQ :
   !P. (?x. P x) /\ (?z. z <> PosInf /\ !x. P x ==> x <= z) ==>
        ?x. (!n. x n IN P) /\ (!n. x n <= x (SUC n)) /\ (sup (IMAGE x UNIV) = sup P)
Proof
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
          >> rename1 `seq_sup P n < x2`
          >> `?x. P x /\ sup P < x + Normal ((1 / 2) pow (SUC n))` by METIS_TAC []
          >> rename1 `sup P < x3 + _`
          >> Q.EXISTS_TAC `max x2 x3`
          >> RW_TAC std_ss [extreal_max_def,SPECIFICATION]
          >- (`x3 < x2` by FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
              >> `x3 +  Normal ((1 / 2) pow (SUC n)) <= x2 +  Normal ((1 / 2) pow (SUC n))`
                  by METIS_TAC [lt_radd,lt_le,extreal_not_infty]
              >> METIS_TAC [lte_trans])
          >> METIS_TAC [lte_trans])
  >> `!n. seq_sup P n <= seq_sup P (SUC n)`
      by (RW_TAC std_ss [seq_sup_def]
          >> SELECT_ELIM_TAC
          >> RW_TAC std_ss []
          >- (`?x. P x /\ seq_sup P n < x` by METIS_TAC [sup_lt,SPECIFICATION]
              >> rename1 `sup_sup P n < x2`
              >> `?x. P x /\ sup P < x + Normal ((1 / 2) pow (SUC n))` by METIS_TAC []
              >> rename1 `sup P < x3 + _`
              >> Q.EXISTS_TAC `max x2 x3`
              >> RW_TAC std_ss [extreal_max_def,SPECIFICATION]
              >- (`x3 < x2` by FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
                  >> `x3 + Normal ((1 / 2) pow (SUC n)) <= x2 + Normal ((1 / 2) pow (SUC n))`
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
              >> rename1 `sup_sup P n < x2`
              >> `?x. P x /\ sup P < x + Normal ((1 / 2) pow (SUC n))` by METIS_TAC []
              >> rename1 `sup P < x3 + _`
              >> Q.EXISTS_TAC `max x2 x3`
              >> RW_TAC std_ss [extreal_max_def,SPECIFICATION]
              >- (`x3 < x2` by FULL_SIMP_TAC std_ss [GSYM extreal_lt_def]
                  >> `x3 + Normal ((1 / 2) pow (SUC n)) <= x2 + Normal ((1 / 2) pow (SUC n))`
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
  >> `?n. Normal ((1 / 2) pow n) < Normal r` by METIS_TAC [EXTREAL_ARCH_POW2_INV]
  >> MATCH_MP_TAC le_trans
  >> Q.EXISTS_TAC `seq_sup P n + Normal ((1 / 2) pow n)`
  >> RW_TAC std_ss []
  >> MATCH_MP_TAC le_add2
  >> FULL_SIMP_TAC std_ss [lt_le]
  >> Q.PAT_X_ASSUM `!z. IMAGE (seq_sup P) UNIV z ==> z <= y` MATCH_MP_TAC
  >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
  >> RW_TAC std_ss [IN_UNIV,IN_IMAGE]
  >> METIS_TAC []
QED

Theorem EXTREAL_SUP_FUN_SEQ_IMAGE :
    !(P:extreal->bool) (P':('a->extreal)->bool) f.
       (?x. P x) /\ (?z. z <> PosInf /\ !x. P x ==> x <= z) /\ (P = IMAGE f P')
           ==> ?g. (!n:num. g n IN P') /\
                   (sup (IMAGE (\n. f (g n)) UNIV) = sup P)
Proof
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
  >> SELECT_ELIM_TAC
  >> RW_TAC std_ss []
  >> METIS_TAC [IN_IMAGE]
QED

Theorem EXTREAL_SUP_FUN_SEQ_MONO_IMAGE :
    !f (P :extreal->bool) (P' :('a->extreal)->bool).
       (?x. P x) /\ (?z. z <> PosInf /\ !x. P x ==> x <= z) /\ (P = IMAGE f P') /\
       (!g1 g2. (g1 IN P' /\ g2 IN P' /\ (!x. g1 x <= g2 x))  ==> f g1 <= f g2) /\
       (!g1 g2. g1 IN P' /\ g2 IN P' ==> (\x. max (g1 x) (g2 x)) IN P')
      ==>
       ?g. (!n. g n IN P') /\ (!x n. g n x <= g (SUC n) x) /\
           (sup (IMAGE (\n. f (g n)) UNIV) = sup P)
Proof
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
  >> METIS_TAC [le_antisym]
QED

(**********************************************************)
(*  Radon-Nikodym Theorem                                 *)
(**********************************************************)

val RADON_F_def = Define
   `RADON_F m v =
      {f | f IN measurable (m_space m,measurable_sets m) Borel /\
           (!x. 0 <= f x) /\
           !A. A IN measurable_sets m ==>
               (pos_fn_integral m (\x. f x * indicator_fn A x) <= measure v A)}`;

val RADON_F_integrals_def = Define
   `RADON_F_integrals m v = {r | ?f. (r = pos_fn_integral m f) /\ f IN RADON_F m v}`;

Theorem lemma_radon_max_in_F[local] :
    !f g m v. measure_space m /\ measure_space v /\
              (m_space v = m_space m) /\ (measurable_sets v = measurable_sets m) /\
              f IN RADON_F m v /\ g IN RADON_F m v
          ==> (\x. max (f x) (g x)) IN RADON_F m v
Proof
    RW_TAC real_ss [RADON_F_def, GSPECIFICATION, max_le, le_max]
 >> ‘sigma_algebra (measurable_space m)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
 >- FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL_MAX, measure_space_def]
 >> Q.ABBREV_TAC `A1 = {x | x IN A /\ g x < f x}`
 >> Q.ABBREV_TAC `A2 = {x | x IN A /\ f x <= g x}`
 >> `DISJOINT A1 A2`
       by (qunabbrevl_tac [`A1`, `A2`] \\
           RW_TAC std_ss [IN_DISJOINT, GSPECIFICATION] \\
           METIS_TAC [extreal_lt_def])
 >> `A1 UNION A2 = A`
       by (qunabbrevl_tac [`A1`, `A2`] \\
           RW_TAC std_ss [IN_UNION, EXTENSION, GSPECIFICATION] \\
           METIS_TAC [extreal_lt_def])
 >> `(\x. max (f x) (g x) * indicator_fn A x) =
     (\x. (\x. max (f x) (g x) * indicator_fn A1 x) x +
          (\x. max (f x) (g x) * indicator_fn A2 x) x)`
       by (qunabbrevl_tac [`A1`, `A2`] \\
           RW_TAC std_ss [indicator_fn_def, GSPECIFICATION, FUN_EQ_THM] \\
           Cases_on `g x < f x`
           >- (RW_TAC std_ss [mul_rone,mul_rzero,add_rzero] >> METIS_TAC [extreal_lt_def])
           >> RW_TAC real_ss [mul_rone,mul_rzero,add_lzero] >> METIS_TAC [extreal_lt_def])
 >> `additive v` by METIS_TAC [MEASURE_SPACE_ADDITIVE]
 >> `A SUBSET m_space m` by RW_TAC std_ss [MEASURE_SPACE_SUBSET_MSPACE]
 >> `A1 = ({x | g x < f x} INTER m_space m) INTER A`
       by (Q.UNABBREV_TAC `A1` \\
           RW_TAC std_ss [EXTENSION, IN_INTER, GSPECIFICATION, CONJ_SYM] \\
           METIS_TAC [SUBSET_DEF])
 >> `A2 = ({x | f x <= g x} INTER m_space m) INTER A`
       by (Q.UNABBREV_TAC `A2` \\
           RW_TAC std_ss [EXTENSION, IN_INTER, GSPECIFICATION, CONJ_SYM] \\
           METIS_TAC [SUBSET_DEF])
 >> `A1 IN measurable_sets m`
       by (ASM_SIMP_TAC std_ss [] \\
           MATCH_MP_TAC MEASURE_SPACE_INTER >> RW_TAC std_ss [] \\
           METIS_TAC [IN_MEASURABLE_BOREL_LT, m_space_def, space_def, subsets_def,
                      measurable_sets_def])
 >> `A2 IN measurable_sets m`
       by (ASM_SIMP_TAC std_ss [] \\
           MATCH_MP_TAC MEASURE_SPACE_INTER >> RW_TAC std_ss [] \\
           METIS_TAC [IN_MEASURABLE_BOREL_LE, m_space_def, space_def, subsets_def,
                      measurable_sets_def])
 >> `measure v A = measure v A1 + measure v A2` by METIS_TAC [ADDITIVE]
 >> Q.PAT_X_ASSUM `A1 = M` (K ALL_TAC)
 >> Q.PAT_X_ASSUM `A2 = M` (K ALL_TAC)
 >> `!x. max (f x) (g x) * indicator_fn A1 x = f x * indicator_fn A1 x`
       by (Q.UNABBREV_TAC `A1` \\
           RW_TAC std_ss [extreal_max_def, indicator_fn_def, GSPECIFICATION,
                          mul_rone, mul_rzero] \\
           METIS_TAC [extreal_lt_def])
 >> `!x. max (f x) (g x) * indicator_fn A2 x = g x * indicator_fn A2 x`
       by (Q.UNABBREV_TAC `A2` \\
           RW_TAC std_ss [extreal_max_def, indicator_fn_def, GSPECIFICATION,
                          mul_rone, mul_rzero] \\
           METIS_TAC [extreal_lt_def])
 >> ASM_SIMP_TAC std_ss []
 >> `(\x. f x * indicator_fn A1 x) IN measurable (m_space m,measurable_sets m) Borel`
       by METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR, measure_space_def,
                     measurable_sets_def, subsets_def]
 >> `(\x. g x * indicator_fn A2 x) IN  measurable (m_space m,measurable_sets m) Borel`
       by METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR, measure_space_def,
                     measurable_sets_def, subsets_def]
 >> `!x. x IN m_space m ==> 0 <= (\x. f x * indicator_fn A1 x) x`
       by RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, le_01, le_refl]
 >> `!x. x IN m_space m ==> 0 <= (\x. g x * indicator_fn A2 x) x`
       by RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, le_01, le_refl]
 >> FULL_SIMP_TAC std_ss [le_add2, pos_fn_integral_add]
QED

val lemma_radon_seq_conv_sup = Q.prove (
   `!f m v. (measure_space m /\ measure_space v /\
            (m_space v = m_space m) /\ (measurable_sets v = measurable_sets m)) /\
            (measure v (m_space v) <> PosInf) ==>
      ?f. (!n. f n IN RADON_F m v) /\ (!x n. f n x <= f (SUC n) x) /\
          (sup (IMAGE (\n. pos_fn_integral m (f n)) UNIV) = sup (RADON_F_integrals m v))`,
    RW_TAC std_ss [RADON_F_integrals_def]
 >> MATCH_MP_TAC EXTREAL_SUP_FUN_SEQ_MONO_IMAGE
 >> CONJ_TAC
 >- (Q.EXISTS_TAC `0` \\
     ONCE_REWRITE_TAC [GSYM SPECIFICATION] \\
     RW_TAC std_ss [GSPECIFICATION] \\
     Q.EXISTS_TAC `(\x. 0)` \\
     RW_TAC real_ss [RADON_F_def, GSPECIFICATION, pos_fn_integral_zero, mul_lzero, le_refl]
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST \\
         METIS_TAC [space_def, measure_space_def]) \\
     METIS_TAC [measure_space_def, positive_def])
 >> CONJ_TAC
 >- (Q.EXISTS_TAC `measure v (m_space v)` \\
     RW_TAC std_ss [] \\
     POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) \\
     RW_TAC std_ss [GSPECIFICATION, RADON_F_def] \\
     POP_ASSUM (MP_TAC o Q.SPEC `m_space m`) \\
     RW_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE, GSYM pos_fn_integral_mspace])
 >> CONJ_TAC
 >- RW_TAC std_ss [EXTENSION,GSPECIFICATION, IN_IMAGE, RADON_F_def]
 >> CONJ_TAC
 >- RW_TAC std_ss [RADON_F_def, GSPECIFICATION, pos_fn_integral_mono]
 >> RW_TAC std_ss [lemma_radon_max_in_F]);

val RN_lemma1 = Q.prove (
   `!m v e. measure_space m /\ measure_space v /\ 0 < e /\
           (m_space v = m_space m) /\ (measurable_sets v = measurable_sets m) /\
            measure v (m_space m) <> PosInf /\
            measure m (m_space m) <> PosInf ==>
        ?A. A IN measurable_sets m /\
            measure m (m_space m) - measure v (m_space m) <= measure m A - measure v A /\
           !B. B IN measurable_sets m /\ B SUBSET A ==> -e < measure m B - measure v B`,
 (* proof *)
    RW_TAC std_ss []
 >> `!A. A IN measurable_sets m ==> measure m A <> NegInf`
       by METIS_TAC [MEASURE_SPACE_POSITIVE, positive_not_infty]
 >> `!A. A IN measurable_sets m ==> measure m A <=  measure m (m_space m)`
       by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, MEASURE_SPACE_MSPACE_MEASURABLE,
                     INCREASING, MEASURE_SPACE_INCREASING]
 >> `!A. A IN measurable_sets m ==> measure m A <> PosInf` by METIS_TAC [lt_infty, let_trans]
 >> `!A. A IN measurable_sets m ==> measure v A <> NegInf`
       by METIS_TAC [MEASURE_SPACE_POSITIVE, positive_not_infty,
                     measure_def, measurable_sets_def]
 >> `!A. A IN measurable_sets m ==> measure v A <= measure v (m_space m)`
       by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE, MEASURE_SPACE_MSPACE_MEASURABLE,
                     INCREASING, MEASURE_SPACE_INCREASING]
 >> `!A. A IN measurable_sets m ==> measure v A <> PosInf` by METIS_TAC [lt_infty, let_trans]
 >> Q.ABBREV_TAC `d = (\A. measure m A - measure v A)`
 >> `!A. A IN measurable_sets m ==> d A <> NegInf` by METIS_TAC [sub_not_infty]
 >> `!A. A IN measurable_sets m ==> d A <> PosInf` by METIS_TAC [sub_not_infty]
 >> `e <> NegInf` by METIS_TAC [lt_infty, lt_trans, num_not_infty]
 >> Cases_on `e = PosInf`
 >- (Q.EXISTS_TAC `m_space m` \\
     METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE, le_refl, lt_infty, extreal_ainv_def])
 >> Q.ABBREV_TAC
     `h = \A. if (!B. B IN measurable_sets m /\ B SUBSET (m_space m DIFF A) ==> -e < d B)
              then {}
              else @B. B IN measurable_sets m /\ B SUBSET (m_space m DIFF A) /\ d B <= -e`
 >> `!A. A IN measurable_sets m ==> h A  IN measurable_sets m`
       by (RW_TAC std_ss [] >> METIS_TAC [MEASURE_SPACE_EMPTY_MEASURABLE, extreal_lt_def])
 >> Q.ABBREV_TAC `A = SIMP_REC {} (\a. a UNION h a)`
 >> `A 0 = {}` by METIS_TAC [SIMP_REC_THM]
 >> `!n. A (SUC n) = (A n) UNION (h (A n))`
       by (Q.UNABBREV_TAC `A` >> RW_TAC std_ss [SIMP_REC_THM])
 >> `!n. A n IN measurable_sets m`
       by (Induct >- RW_TAC std_ss [MEASURE_SPACE_EMPTY_MEASURABLE] \\
           RW_TAC std_ss [MEASURE_SPACE_UNION])
 >> Know `!n. (?B. B IN measurable_sets m /\ B SUBSET (m_space m DIFF (A n)) /\ d B <= -e) ==>
              d (A (SUC n)) <= d (A n) - e`
 >- (RW_TAC std_ss [] \\
    `~(!B. B IN measurable_sets m /\ B SUBSET (m_space m DIFF (A n)) ==> -e < d B)`
           by METIS_TAC [extreal_lt_def] \\
    `h (A n) = (@B. B IN measurable_sets m /\ B SUBSET m_space m DIFF (A n) /\ d B <= -e)`
           by (Q.UNABBREV_TAC `h` >> RW_TAC std_ss []) >> POP_ORW \\
     SELECT_ELIM_TAC >> RW_TAC std_ss [] >- METIS_TAC [] \\
    `DISJOINT (A n) x`
           by (RW_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY] \\
               METIS_TAC [SUBSET_DEF, IN_DIFF]) \\
     Know `d ((A n) UNION x) = d (A n) + d x`
     >- (Q.UNABBREV_TAC `d` \\
         RW_TAC std_ss [] \\
         Know `measure m (A n UNION x) = measure m (A n) + measure m x`
         >- (MATCH_MP_TAC MEASURE_ADDITIVE >> art []) >> Rewr' \\
         Know `measure v (A n UNION x) = measure v (A n) + measure v x`
         >- (MATCH_MP_TAC MEASURE_ADDITIVE >> art []) >> Rewr' \\
        `?r1. measure v (A n) = Normal r1` by METIS_TAC [extreal_cases] \\
        `?r2. measure v x = Normal r2` by METIS_TAC [extreal_cases] \\
         RW_TAC std_ss [extreal_add_def] \\
         Cases_on `measure m (A n)` \\
         Cases_on `measure m x` \\
         RW_TAC std_ss [extreal_add_def, extreal_sub_def, REAL_ADD2_SUB2] \\
         METIS_TAC []) >> Rewr' \\
        `d (A n) - e = d (A n) + -e` by METIS_TAC [extreal_sub_add] \\
         METIS_TAC [le_ladd])
 >> DISCH_TAC
 >> `!n. d (A (SUC n)) <= d (A n)`
        by (RW_TAC std_ss [] \\
            Cases_on `(?B. B IN measurable_sets m /\ B SUBSET m_space m DIFF A n /\ d B <= -e)`
            >- (`d (A n) <= d (A n) + e` by METIS_TAC [lt_le, le_addr_imp] \\
                `d (A n) - e <= d (A n)`
                   by (Cases_on `d (A n)` >> Cases_on `e` \\
                       RW_TAC std_ss [extreal_add_def, extreal_sub_def, extreal_le_def,
                                      extreal_not_infty, lt_infty, le_infty] \\
                       METIS_TAC [extreal_add_def, extreal_le_def, REAL_LE_SUB_RADD]) \\
                METIS_TAC [le_trans]) \\
           `!B. B IN measurable_sets m /\ B SUBSET m_space m DIFF A n ==> -e < d B`
               by METIS_TAC [extreal_lt_def] \\
            METIS_TAC [UNION_EMPTY, le_refl])
 >> Cases_on `?n. !B. ((B IN measurable_sets m /\ B SUBSET (m_space m DIFF (A n))) ==> -e < d B)`
 >- (Q.PAT_X_ASSUM `!n. A (SUC n) = a UNION b` (K ALL_TAC) \\
     FULL_SIMP_TAC std_ss [] \\
    `!n. m_space m DIFF (A n) IN measurable_sets m`
        by METIS_TAC [MEASURE_SPACE_DIFF, MEASURE_SPACE_MSPACE_MEASURABLE] \\
     Suff `!n. d (m_space m) <= d (m_space m DIFF (A n))`
     >- METIS_TAC [] \\
     Induct >- RW_TAC std_ss [DIFF_EMPTY, le_refl] \\
    `measure m (m_space m DIFF A (SUC n')) = measure m (m_space m) - measure m (A (SUC n'))`
        by METIS_TAC [MEASURE_SPACE_FINITE_DIFF] \\
    `measure v (m_space m DIFF A (SUC n')) = measure v (m_space m) - measure v (A (SUC n'))`
        by METIS_TAC [MEASURE_SPACE_FINITE_DIFF, measure_def, measurable_sets_def,
                      m_space_def] \\
    `measure m (m_space m DIFF A n') = measure m (m_space m) - measure m (A n')`
        by METIS_TAC [MEASURE_SPACE_FINITE_DIFF] \\
    `measure v (m_space m DIFF A n') = measure v (m_space m) - measure v (A n')`
        by METIS_TAC [MEASURE_SPACE_FINITE_DIFF, measure_def, measurable_sets_def,
                      m_space_def] \\
    `d (m_space m DIFF A n') = d (m_space m) - d (A n')`
        by (Q.UNABBREV_TAC `d` >> FULL_SIMP_TAC std_ss [] \\
           `?r1. measure m (m_space m) = Normal r1`
               by METIS_TAC [extreal_cases, MEASURE_SPACE_MSPACE_MEASURABLE] \\
           `?r2. measure v (m_space m) = Normal r2`
               by METIS_TAC [extreal_cases, MEASURE_SPACE_MSPACE_MEASURABLE] \\
           `?r3. measure m (A n') = Normal r3` by METIS_TAC [extreal_cases] \\
           `?r4. measure v (A n') = Normal r4` by METIS_TAC [extreal_cases] \\
            FULL_SIMP_TAC std_ss [extreal_add_def, extreal_sub_def, extreal_lt_def, extreal_11] \\
            REAL_ARITH_TAC) \\
    `d (m_space m DIFF A (SUC n')) = d (m_space m) - d (A (SUC n'))`
        by (Q.UNABBREV_TAC `d` >> FULL_SIMP_TAC std_ss [] \\
           `?r1. measure m (m_space m) = Normal r1`
               by METIS_TAC [extreal_cases, MEASURE_SPACE_MSPACE_MEASURABLE] \\
           `?r2. measure v (m_space m) = Normal r2`
               by METIS_TAC [extreal_cases, MEASURE_SPACE_MSPACE_MEASURABLE] \\
           `?r3. measure m (A (SUC n')) = Normal r3` by METIS_TAC [extreal_cases] \\
           `?r4. measure v (A (SUC n')) = Normal r4` by METIS_TAC [extreal_cases] \\
            FULL_SIMP_TAC std_ss [extreal_add_def, extreal_sub_def, extreal_lt_def, extreal_11] \\
            REAL_ARITH_TAC) \\
     FULL_SIMP_TAC std_ss [] \\
    `d (m_space m) - d (A n') <= d (m_space m) - d (A (SUC n'))`
        by METIS_TAC [extreal_sub_add, MEASURE_SPACE_MSPACE_MEASURABLE, le_ladd_imp, le_neg] \\
     METIS_TAC [le_trans])
 >> `!n. ?B. B IN measurable_sets m /\ B SUBSET (m_space m DIFF (A n)) /\ d B <= -e`
       by METIS_TAC [extreal_lt_def]
 >> `!n. d (A n) <= - &n * e`
       by (Induct
           >- METIS_TAC [mul_lzero,neg_0,le_refl,MEASURE_EMPTY,measure_def,sub_rzero]
           >> `d (A (SUC n)) <= d (A n) - e` by METIS_TAC []
           >> `?r1. d (A n) = Normal r1` by METIS_TAC [extreal_cases]
           >> `?r2. d (A (SUC n)) = Normal r2` by METIS_TAC [extreal_cases]
           >> `e <> PosInf` by ( METIS_TAC [extreal_sub_def,le_infty,extreal_not_infty])
           >> `?r3. e = Normal r3` by METIS_TAC [extreal_cases]
           >> FULL_SIMP_TAC std_ss [extreal_sub_def, extreal_le_def, extreal_ainv_def,
                                    extreal_of_num_def, extreal_mul_def]
           >> RW_TAC std_ss [ADD1, GSYM REAL_ADD, REAL_NEG_ADD, REAL_ADD_RDISTRIB,
                             GSYM REAL_NEG_MINUS1]
           >> `r1 + -r3 <= -&n * r3 + -r3` by METIS_TAC [REAL_LE_ADD2,REAL_LE_REFL]
           >> METIS_TAC [real_sub,REAL_LE_TRANS])
 >> `!n. - d (A n) <= - d (A (SUC n))` by METIS_TAC [le_neg]
 >> `!n. A n SUBSET A (SUC n)` by METIS_TAC [SUBSET_UNION]
 >> `sup (IMAGE (measure m o A) UNIV) = measure m (BIGUNION (IMAGE A UNIV))`
       by METIS_TAC [MONOTONE_CONVERGENCE2,IN_FUNSET,IN_UNIV,measure_def,measurable_sets_def]
 >> `sup (IMAGE (measure v o A) UNIV) = measure v (BIGUNION (IMAGE A UNIV))`
       by METIS_TAC [MONOTONE_CONVERGENCE2,IN_FUNSET,IN_UNIV,measure_def,measurable_sets_def]
 >> FULL_SIMP_TAC std_ss [o_DEF]
 >> `?r1. !n. measure m (A n) = Normal (r1 n)`
       by (Q.EXISTS_TAC `(\n. @r. measure m (A n) = Normal r)`
           >> RW_TAC std_ss []
           >> SELECT_ELIM_TAC
           >> METIS_TAC [extreal_cases])
 >> `?r2. !n. measure v (A n) = Normal (r2 n)`
       by (Q.EXISTS_TAC `(\n. @r. measure v (A n) = Normal r)`
           >> RW_TAC std_ss []
           >> SELECT_ELIM_TAC
           >> METIS_TAC [extreal_cases])
 >> `BIGUNION (IMAGE A UNIV) IN measurable_sets m`
       by METIS_TAC [SIGMA_ALGEBRA_ENUM, measure_space_def, subsets_def,
                     measurable_sets_def, IN_FUNSET, IN_UNIV]
 >> `?l1. measure m (BIGUNION (IMAGE A UNIV)) = Normal l1` by METIS_TAC [extreal_cases]
 >> `?l2. measure v (BIGUNION (IMAGE A UNIV)) = Normal l2` by METIS_TAC [extreal_cases]
 >> FULL_SIMP_TAC std_ss []
 >> `mono_increasing r1`
       by METIS_TAC [mono_increasing_def, mono_increasing_suc, MEASURE_SPACE_INCREASING,
                     increasing_def, extreal_le_def]
 >> `mono_increasing r2`
       by METIS_TAC [mono_increasing_def, mono_increasing_suc, MEASURE_SPACE_INCREASING,
                     increasing_def, extreal_le_def, measure_def, measurable_sets_def]
 >> FULL_SIMP_TAC std_ss [GSYM sup_seq]
 >> `!n. -d (A n) = Normal (r2 n - r1 n)`
        by (Q.UNABBREV_TAC `d`
            >> RW_TAC std_ss [extreal_sub_def,extreal_ainv_def,REAL_NEG_SUB])
 >> Q.ABBREV_TAC `r = (\n. r2 n - r1 n)`
 >> `mono_increasing r` by METIS_TAC [mono_increasing_suc, extreal_le_def]
 >> `r --> (l2 - l1)` by (Q.UNABBREV_TAC `r` >> METIS_TAC [SEQ_SUB])
 >> `sup (IMAGE (\n. Normal (r n)) UNIV) = Normal (l2 - l1)` by METIS_TAC [sup_seq]
 >> `sup (IMAGE (\n. -d (A n)) UNIV) = -d (BIGUNION (IMAGE A UNIV))`
        by (`(\n. -d (A n)) = (\n. Normal (r n))` by METIS_TAC []
            >> POP_ORW
            >> Q.UNABBREV_TAC `d`
            >> RW_TAC std_ss [extreal_sub_def, extreal_ainv_def, REAL_NEG_SUB])
 >> `d (BIGUNION (IMAGE A UNIV)) <> NegInf` by METIS_TAC []
 >> `- d (BIGUNION (IMAGE A UNIV)) <> PosInf`
      by METIS_TAC [extreal_ainv_def, extreal_cases, extreal_not_infty]
 >> `?n. - d (BIGUNION (IMAGE A UNIV)) < &n * e` by METIS_TAC [EXTREAL_ARCH]
 >> `&n * e <= -d (A n)` by METIS_TAC [le_neg,neg_neg,mul_lneg]
 >> `-d (BIGUNION (IMAGE A univ(:num))) < -d (A n)` by METIS_TAC [lte_trans]
 >> `-d (A n) <= - d (BIGUNION (IMAGE A UNIV))`
       by (RW_TAC std_ss []
           >> Q.PAT_X_ASSUM `sup P = -d Q` (MP_TAC o GSYM)
           >> DISCH_THEN (fn th => REWRITE_TAC [th])
           >> MATCH_MP_TAC le_sup_imp
           >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
           >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
           >> METIS_TAC [])
 >> METIS_TAC [extreal_lt_def]);

val RN_lemma2 = Q.prove (
   `!m v. measure_space m /\ measure_space v /\
         (m_space v = m_space m) /\
         (measurable_sets v = measurable_sets m) /\
          measure v (m_space m) <> PosInf /\
          measure m (m_space m) <> PosInf ==>
      ?A. A IN measurable_sets m /\
          measure m (m_space m) - measure v (m_space m) <= measure m A - measure v A /\
         !B. B IN measurable_sets m /\ B SUBSET A ==> 0 <= measure m B - measure v B`,
 (* proof *)
    RW_TAC std_ss []
 >> Q.ABBREV_TAC `d = (\a. measure m a - measure v a)`
 >> Q.ABBREV_TAC
     `p = (\a b n. a IN measurable_sets m /\ a SUBSET b /\ d b <= d a /\
                  !c. c IN measurable_sets m /\ c SUBSET a ==> -(Normal ((1 / 2) pow n)) < d c)`
 >> Q.ABBREV_TAC `sts = (\s. IMAGE (\A. s INTER A) (measurable_sets m))`
 >> `!s t. s IN measurable_sets m /\ t IN sts s ==> t IN measurable_sets m`
        by (RW_TAC std_ss []
            >> Q.UNABBREV_TAC `sts`
            >> FULL_SIMP_TAC std_ss [IN_IMAGE, MEASURE_SPACE_INTER])
 >> `!s t. t IN sts s ==> t SUBSET s`
        by (RW_TAC std_ss []
            >> Q.UNABBREV_TAC `sts`
            >> FULL_SIMP_TAC std_ss [IN_IMAGE, INTER_SUBSET])
 >> `!s. s IN measurable_sets m ==> measure_space (s, sts s, measure m)`
        by METIS_TAC [MEASURE_SPACE_RESTRICTED]
 >> `!s. s IN measurable_sets m ==> measure_space (s, sts s, measure v)`
        by METIS_TAC [MEASURE_SPACE_RESTRICTED]
 >> `!n. 0 < Normal ((1 / 2) pow n)`
        by METIS_TAC [extreal_lt_eq, extreal_of_num_def, POW_HALF_POS]
 >> `!s. s IN measurable_sets m ==> measure m s <> PosInf`
        by METIS_TAC [MEASURE_SPACE_FINITE_MEASURE]
 >> `!s. s IN measurable_sets m ==> measure v s <> PosInf`
        by METIS_TAC [MEASURE_SPACE_FINITE_MEASURE]
 >> `!s. s IN measurable_sets m ==> measure m s <> NegInf`
        by METIS_TAC [MEASURE_SPACE_POSITIVE, positive_not_infty]
 >> `!s. s IN measurable_sets m ==> measure v s <> NegInf`
        by METIS_TAC [MEASURE_SPACE_POSITIVE, positive_not_infty]
 >> `!s n. s IN measurable_sets m ==> ?A. p A s n`
        by (RW_TAC std_ss [] \\
           `?A. A IN (sts s) /\ measure m s - measure v s <= measure m A - measure v A /\
               !B. B IN (sts s) /\ B SUBSET A ==>
                   -Normal ((1 / 2) pow n) < measure m B - measure v B`
               by (RW_TAC std_ss [] \\
                   (MP_TAC o Q.SPECL [`(s,sts s,measure m)`,
                                      `(s,sts s,measure v)`,
                                      `Normal ((1 / 2) pow n)`]) RN_lemma1 \\
                   RW_TAC std_ss [m_space_def, measure_def, measurable_sets_def]) \\
            Q.EXISTS_TAC `A` \\
            Q.UNABBREV_TAC `p` \\
            FULL_SIMP_TAC std_ss [measure_def] \\
            RW_TAC std_ss []
            >| [ (* goal 1 (of 3) *) METIS_TAC [],
                 (* goal 2 (of 3) *) METIS_TAC [],
                 (* goal 3 (of 3) *)
                 `A SUBSET s` by METIS_TAC []
                 >> Suff `c IN sts s` >- METIS_TAC []
                 >> Q.UNABBREV_TAC `sts`
                 >> FULL_SIMP_TAC std_ss [IN_IMAGE]
                 >> Q.EXISTS_TAC `c`
                 >> METIS_TAC [SUBSET_INTER2,SUBSET_TRANS] ])
 >> Q.ABBREV_TAC `A = PRIM_REC (m_space m) (\a n. @b. p b a n)`
 >> `A 0 = m_space m` by METIS_TAC [PRIM_REC_THM]
 >> `!n. A (SUC n) = @b. p b (A n) n`
        by (Q.UNABBREV_TAC `A` >> RW_TAC std_ss [PRIM_REC_THM])
 >> `!n. A n IN measurable_sets m`
       by (Induct >- METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE]
           >> RW_TAC std_ss []
           >> SELECT_ELIM_TAC
           >> FULL_SIMP_TAC std_ss []
           >> METIS_TAC [])
 >> `!n. p (A (SUC n)) (A n) n` by METIS_TAC []
 >> `!n. A (SUC n) SUBSET (A n)` by METIS_TAC []
 >> `!n. d (A n) <= d (A (SUC n))` by METIS_TAC []
 >> `!n c. c IN measurable_sets m /\ c SUBSET (A (SUC n)) ==>
           -Normal ((1 / 2) pow n) < d c` by METIS_TAC []
 >> Q.EXISTS_TAC `BIGINTER (IMAGE A UNIV)`
 >> CONJ_TAC >- METIS_TAC [SIGMA_ALGEBRA_FN_BIGINTER, IN_UNIV, IN_FUNSET,
                           subsets_def, measurable_sets_def, measure_space_def]
 >> reverse CONJ_TAC
 >- (RW_TAC std_ss [] \\
     SPOSE_NOT_THEN ASSUME_TAC \\
     FULL_SIMP_TAC std_ss [GSYM extreal_lt_def] \\
    `0 < - (measure m B - measure v B)` by METIS_TAC [lt_neg, neg_0] \\
    `?n. measure m B - measure v B < -Normal ((1 / 2) pow n)`
         by METIS_TAC [EXTREAL_ARCH_POW2_INV, lt_neg, neg_neg] \\
    `d B < -Normal ((1 / 2) pow n)` by METIS_TAC [] \\
    `!n. B SUBSET A n` by METIS_TAC [SUBSET_BIGINTER, IN_IMAGE, IN_UNIV] \\
     METIS_TAC [lt_antisym])
 >> `measure m (BIGINTER (IMAGE A UNIV)) = inf (IMAGE (measure m o A) UNIV)`
       by (MATCH_MP_TAC (GSYM MONOTONE_CONVERGENCE_BIGINTER2)
           >> RW_TAC std_ss [IN_UNIV, IN_FUNSET])
 >> `measure v (BIGINTER (IMAGE A UNIV)) = inf (IMAGE (measure v o A) UNIV)`
       by (MATCH_MP_TAC (GSYM MONOTONE_CONVERGENCE_BIGINTER2)
           >> RW_TAC std_ss [IN_UNIV, IN_FUNSET])
 >> `?r1. !n. measure m (A n) = Normal (r1 n)`
       by (Q.EXISTS_TAC `(\n. @r. measure m (A n) = Normal r)`
           >> RW_TAC std_ss []
           >> SELECT_ELIM_TAC
           >> METIS_TAC [extreal_cases])
 >> `?r2. !n. measure v (A n) = Normal (r2 n)`
       by (Q.EXISTS_TAC `(\n. @r. measure v (A n) = Normal r)`
           >> RW_TAC std_ss []
           >> SELECT_ELIM_TAC
           >> METIS_TAC [extreal_cases])
 >> `BIGINTER (IMAGE A UNIV) IN measurable_sets m` by METIS_TAC [MEASURE_SPACE_BIGINTER]
 >> `?l1. measure m (BIGINTER (IMAGE A UNIV)) = Normal l1` by METIS_TAC [extreal_cases]
 >> `?l2. measure v (BIGINTER (IMAGE A UNIV)) = Normal l2` by METIS_TAC [extreal_cases]
 >> FULL_SIMP_TAC std_ss [o_DEF]
 >> Q.PAT_X_ASSUM `Normal l1 = Q` (MP_TAC o GSYM)
 >> Q.PAT_X_ASSUM `Normal l2 = Q` (MP_TAC o GSYM)
 >> RW_TAC std_ss [extreal_sub_def]
 >> `mono_decreasing r1`
       by METIS_TAC [mono_decreasing_def, mono_decreasing_suc, MEASURE_SPACE_INCREASING,
                     increasing_def, extreal_le_def]
 >> `mono_decreasing r2`
       by METIS_TAC [mono_decreasing_def, mono_decreasing_suc, MEASURE_SPACE_INCREASING,
                     increasing_def, extreal_le_def, measure_def, measurable_sets_def]
 >> FULL_SIMP_TAC std_ss [GSYM inf_seq]
 >> `!n. -d (A n) = Normal (r2 n - r1 n)`
       by (Q.UNABBREV_TAC `d` \\
           RW_TAC std_ss [extreal_sub_def, extreal_ainv_def, REAL_NEG_SUB])
 >> Q.ABBREV_TAC `r = (\n. r2 n - r1 n)`
 >> `!n. -d (A (SUC n)) <= -d (A n)` by METIS_TAC [le_neg]
 >> `mono_decreasing r` by METIS_TAC [mono_decreasing_suc, extreal_le_def,extreal_ainv_def]
 >> `r --> (l2 - l1)` by (Q.UNABBREV_TAC `r` >> METIS_TAC [SEQ_SUB])
 >> `inf (IMAGE (\n. Normal (r n)) UNIV) = Normal (l2 - l1)` by METIS_TAC [inf_seq]
 >> `inf (IMAGE (\n. -d (A n)) UNIV) = -d (BIGINTER (IMAGE A UNIV))`
       by (`(\n. -d (A n)) = (\n. Normal (r n))` by METIS_TAC [] \\
           POP_ORW >> Q.UNABBREV_TAC `d` \\
           RW_TAC std_ss [extreal_sub_def, extreal_ainv_def, REAL_NEG_SUB])
 >> FULL_SIMP_TAC std_ss [inf_eq]
 >> `-d (BIGINTER (IMAGE A univ(:num))) <= -d (A 0)`
       by (Q.PAT_X_ASSUM `!y. Q ==> -d (BIGINTER (IMAGE A univ(:num))) <= y` MATCH_MP_TAC
           >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
           >> RW_TAC std_ss [IN_IMAGE, IN_UNIV]
           >> METIS_TAC [])
 >> METIS_TAC [le_neg]);

(* NOTE: the resulting function ‘f’ is total, i.e. ‘!x. 0 <= f x’, usually more than
         what's needed (!x. x IN m_space m ==> 0 <= f x) in RN_deriv_def
 *)
Theorem Radon_Nikodym_finite : (* was: Radon_Nikodym *)
    !M N. measure_space M /\ measure_space N /\
         (m_space M = m_space N) /\ (measurable_sets M = measurable_sets N) /\
          measure M (m_space M) <> PosInf /\
          measure N (m_space N) <> PosInf /\
          measure_absolutely_continuous (measure N) M ==>
      ?f. f IN measurable (m_space M,measurable_sets M) Borel /\
          (!x. 0 <= f x) /\
          !A. A IN measurable_sets M ==>
             (pos_fn_integral M (\x. f x * indicator_fn A x) = measure N A)
Proof
    qx_genl_tac [`m`, `v`] >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM `m_space m = m_space v` (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM `measurable_sets m = measurable_sets v` (ASSUME_TAC o SYM)
 >> `?f_n. (!n. f_n n IN RADON_F m v) /\ (!x n. f_n n x <= f_n (SUC n) x) /\
           (sup (IMAGE (\n. pos_fn_integral m (f_n n)) univ(:num)) = sup (RADON_F_integrals m v))`
       by RW_TAC std_ss [lemma_radon_seq_conv_sup]
 >> Q.ABBREV_TAC `g = (\x. sup (IMAGE (\n. f_n n x) UNIV))`
 >> Q.EXISTS_TAC `g`
 >> `g IN measurable (m_space m,measurable_sets m) Borel`
       by (MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP
           >> Q.EXISTS_TAC `f_n`
           >> FULL_SIMP_TAC std_ss [RADON_F_def, GSPECIFICATION, measure_space_def, space_def]
           >> Q.UNABBREV_TAC `g`
           >> RW_TAC std_ss [])
 >> Know `!x. 0 <= g x`
 >- (RW_TAC std_ss [Abbr ‘g’, le_sup'] \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `f_n 0 x` \\
     CONJ_TAC >- FULL_SIMP_TAC std_ss [RADON_F_def, GSPECIFICATION] \\
     POP_ASSUM MATCH_MP_TAC \\
     RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
     Q.EXISTS_TAC ‘0’ >> REWRITE_TAC []) >> DISCH_TAC
 >> RW_TAC std_ss []
 >> `!A. A IN measurable_sets m ==>
         (pos_fn_integral m (\x. g x * indicator_fn A x) =
          sup (IMAGE (\n. pos_fn_integral m (\x. f_n n x * indicator_fn A x)) UNIV))`
       by (RW_TAC std_ss []
           >> MATCH_MP_TAC lebesgue_monotone_convergence_subset
           >> FULL_SIMP_TAC std_ss [RADON_F_def, GSPECIFICATION, ext_mono_increasing_suc]
           >> RW_TAC std_ss []
           >> Q.UNABBREV_TAC `g`
           >> METIS_TAC [])
 >> `g IN RADON_F m v`
       by (FULL_SIMP_TAC std_ss [RADON_F_def,GSPECIFICATION,sup_le]
           >> RW_TAC std_ss []
           >> POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION])
           >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
           >> METIS_TAC [])
 >> `pos_fn_integral m g = sup (IMAGE (\n:num. pos_fn_integral m (f_n n)) UNIV)`
       by (MATCH_MP_TAC lebesgue_monotone_convergence
           >> FULL_SIMP_TAC std_ss [RADON_F_def, GSPECIFICATION, ext_mono_increasing_suc]
           >> Q.UNABBREV_TAC `g`
           >> METIS_TAC [])
 >> `pos_fn_integral m g = sup (RADON_F_integrals m v)` by FULL_SIMP_TAC std_ss []
 >> Q.ABBREV_TAC `nu = (\A. measure v A - pos_fn_integral m (\x. g x * indicator_fn A x))`
 >> `!A. A IN measurable_sets m ==>
         pos_fn_integral m (\x. g x * indicator_fn A x) <= measure v A`
       by FULL_SIMP_TAC std_ss [RADON_F_def, GSPECIFICATION]
 >> `!A. A IN measurable_sets m ==> measure v A <> PosInf`
       by METIS_TAC [lt_infty, INCREASING, MEASURE_SPACE_INCREASING, let_trans,
                     MEASURE_SPACE_SUBSET_MSPACE, MEASURE_SPACE_MSPACE_MEASURABLE]
 >> `!A. A IN measurable_sets m ==> measure m A <> PosInf`
       by METIS_TAC [lt_infty, INCREASING, MEASURE_SPACE_INCREASING, let_trans,
                     MEASURE_SPACE_SUBSET_MSPACE, MEASURE_SPACE_MSPACE_MEASURABLE]
 >> `!A x. 0 <= (\x. g x * indicator_fn A x) x`
       by RW_TAC std_ss [indicator_fn_def, mul_rzero, mul_rone, le_01, le_refl]
 >> `!A. A IN measurable_sets m ==> 0 <= pos_fn_integral m (\x. g x * indicator_fn A x)`
       by (REPEAT STRIP_TAC >> MATCH_MP_TAC pos_fn_integral_pos >> METIS_TAC [])
 >> `!A. A IN measurable_sets m ==>
         pos_fn_integral m (\x. g x * indicator_fn A x) <> NegInf`
       by METIS_TAC [lt_infty, extreal_of_num_def, extreal_not_infty, lte_trans]
 >> `!A. A IN measurable_sets m ==>
         pos_fn_integral m (\x. g x * indicator_fn A x) <> PosInf`
       by METIS_TAC [let_trans, lt_infty]
 >> `!A. A IN measurable_sets m ==> 0 <= nu A`
       by (RW_TAC std_ss []
           >> FULL_SIMP_TAC std_ss [RADON_F_def, GSPECIFICATION]
           >> `pos_fn_integral m (\x. g x * indicator_fn A' x) <= measure v A'`
                by FULL_SIMP_TAC std_ss []
           >> `pos_fn_integral m (\x. g x * indicator_fn A' x) <> PosInf`
                by METIS_TAC [lt_infty, INCREASING, MEASURE_SPACE_INCREASING, let_trans,
                              MEASURE_SPACE_SUBSET_MSPACE, MEASURE_SPACE_MSPACE_MEASURABLE]
           >> Q.UNABBREV_TAC `nu` >> METIS_TAC [sub_zero_le])
 >> `positive (m_space m,measurable_sets m,nu)`
       by (RW_TAC std_ss [positive_def, measure_def, measurable_sets_def] \\
           Q.UNABBREV_TAC `nu` \\
           RW_TAC std_ss [MEASURE_EMPTY, indicator_fn_def, NOT_IN_EMPTY,
                          pos_fn_integral_zero, mul_rzero, mul_rone, sub_rzero])
 >> Q.PAT_X_ASSUM `!A. A IN measurable_sets m ==>
                      (pos_fn_integral m (\x. g x * indicator_fn A x) = Q)` (K ALL_TAC)
 >> RW_TAC std_ss []
 >> `measure_space (m_space m,measurable_sets m,nu)`
       by (FULL_SIMP_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def,
                                 countably_additive_def, measure_def]
           >> Q.UNABBREV_TAC `nu`
           >> RW_TAC std_ss [o_DEF]
           >> `suminf (\x. measure v (f x)) = measure v (BIGUNION (IMAGE f univ(:num)))`
                 by METIS_TAC [o_DEF,countably_additive_def]
           >> `suminf (\x. measure v (f x)) <> PosInf` by METIS_TAC []
           >> `suminf (\x. measure v (f x) - pos_fn_integral m (\x'. g x' * indicator_fn (f x) x')) =
               suminf (\x. measure v (f x)) -
               suminf (\x. pos_fn_integral m (\x'. g x' * indicator_fn (f x) x'))`
                by  (`(\x. measure v (f x) - pos_fn_integral m (\x'. g x' * indicator_fn (f x) x')) =
                      (\x. (\x. measure v (f x)) x -
                           (\x. pos_fn_integral m (\x'. g x' * indicator_fn (f x) x')) x)`
                         by METIS_TAC []
                     >> POP_ORW
                     >> MATCH_MP_TAC ext_suminf_sub
                     >> RW_TAC std_ss []
                     >- (MATCH_MP_TAC pos_fn_integral_pos
                         >> RW_TAC std_ss [indicator_fn_def,mul_rzero,mul_rone,le_refl]
                         >> METIS_TAC [measure_space_def,countably_additive_def])
                     >> METIS_TAC [IN_FUNSET,IN_UNIV])
           >> POP_ORW
           >> Suff `pos_fn_integral m (\x. g x * indicator_fn (BIGUNION (IMAGE f univ(:num))) x) =
                    suminf (\x. pos_fn_integral m (\x'. g x' * indicator_fn (f x) x'))`
           >- RW_TAC std_ss []
           >> `measure_space m` by METIS_TAC [measure_space_def,countably_additive_def]
           >> `(!i x. 0 <= (\i x. g x * indicator_fn (f i) x) i x)`
                by RW_TAC std_ss [mul_rzero,mul_rone,indicator_fn_def,le_refl]
           >> `(!i. (\i x. g x * indicator_fn (f i) x) i IN measurable (m_space m,measurable_sets m) Borel)`
                by (RW_TAC std_ss [] \\
                    METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR, IN_FUNSET,
                               IN_UNIV, measurable_sets_def, subsets_def])
           >> (MP_TAC o Q.SPECL [`m`,`(\i:num. (\x. g x * indicator_fn (f i) x))`]) pos_fn_integral_suminf
           >> RW_TAC std_ss []
           >> POP_ASSUM (MP_TAC o GSYM)
           >> RW_TAC std_ss []
           >> Suff `(\x. g x * indicator_fn (BIGUNION (IMAGE f univ(:num))) x) =
                    (\x'. suminf (\x. g x' * indicator_fn (f x) x'))`
           >- RW_TAC std_ss []
           >> RW_TAC std_ss [FUN_EQ_THM]
           >> `suminf (\x. g x' * (\x. indicator_fn (f x) x') x) = g x' * suminf (\x. indicator_fn (f x) x')`
                by (MATCH_MP_TAC ext_suminf_cmul \\
                    RW_TAC std_ss [mul_rone,mul_rzero,le_refl,indicator_fn_def,le_01])
           >> FULL_SIMP_TAC std_ss []
           >> Suff `suminf (\i. indicator_fn (f i) x') = indicator_fn (BIGUNION (IMAGE f univ(:num))) x'`
           >- RW_TAC std_ss []
           >> FULL_SIMP_TAC std_ss [indicator_fn_suminf])
 >> `!A. A IN measurable_sets m ==> nu A <= nu (m_space m)`
       by METIS_TAC [MEASURE_SPACE_INCREASING, INCREASING, MEASURE_SPACE_SUBSET_MSPACE,
                     measure_def, measurable_sets_def, m_space_def,
                     MEASURE_SPACE_MSPACE_MEASURABLE]
 >> Cases_on `nu A = 0` >- METIS_TAC [sub_0]
 >> `0 < nu A` by METIS_TAC [lt_le, MEASURE_SPACE_POSITIVE, positive_def]
 >> `0 < nu (m_space m)` by METIS_TAC [lte_trans]
 >> `0 <> measure m (m_space m)`
       by (SPOSE_NOT_THEN ASSUME_TAC
           >> `measure v (m_space m) = 0`
                 by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE, measure_absolutely_continuous_def]
           >> `pos_fn_integral m (\x. g x * indicator_fn (m_space m) x) <= 0`
                 by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE]
           >> `pos_fn_integral m (\x. g x * indicator_fn (m_space m) x) =  0`
                 by METIS_TAC [le_antisym,MEASURE_SPACE_MSPACE_MEASURABLE]
           >> `nu (m_space m) = 0` by (Q.UNABBREV_TAC `nu` >> METIS_TAC [sub_rzero])
           >> METIS_TAC [lt_imp_ne])
 >> `0 < measure m (m_space m)`
       by METIS_TAC [lt_le, MEASURE_SPACE_POSITIVE, positive_def, MEASURE_SPACE_MSPACE_MEASURABLE]
 >> Q.ABBREV_TAC `z = nu (m_space m) / (2 * measure m (m_space m)) `
 >> `nu (m_space m) <> NegInf` by METIS_TAC [lt_trans, lt_infty, num_not_infty]
 >> `measure m (m_space m) <> NegInf` by METIS_TAC [lt_trans, lt_infty, num_not_infty]
 >> `nu (m_space m) <> PosInf`
       by (Q.UNABBREV_TAC `nu`
           >> RW_TAC std_ss []
           >> METIS_TAC [sub_not_infty, MEASURE_SPACE_MSPACE_MEASURABLE])
 >> `?e. 0 < e /\ (z = Normal e)`
       by (Q.UNABBREV_TAC `z`
           >> `?r1. nu (m_space m) = Normal r1` by METIS_TAC [extreal_cases]
           >> `?r2. measure m (m_space m) = Normal r2` by METIS_TAC [extreal_cases]
           >> RW_TAC std_ss [extreal_mul_def,extreal_of_num_def]
           >> `0 < r1` by METIS_TAC [extreal_of_num_def,extreal_lt_eq]
           >> `0 < r2` by METIS_TAC [extreal_of_num_def,extreal_lt_eq]
           >> `0 < 2 * r2` by RW_TAC real_ss [REAL_LT_MUL]
           >> FULL_SIMP_TAC std_ss [extreal_div_eq,REAL_LT_IMP_NE]
           >> `0 < r1 / (2 * r2)` by RW_TAC std_ss [REAL_LT_DIV]
           >> METIS_TAC [])
 >> Q.ABBREV_TAC `snu = (\A. nu A - Normal e * (measure m A))`
 >> `?A'. A' IN measurable_sets m /\ snu(m_space m) <= snu (A') /\
         !B. B IN measurable_sets m /\ B SUBSET A' ==> 0 <= snu (B)`
       by (Q.UNABBREV_TAC `snu` >> RW_TAC std_ss [] \\
           MP_TAC
             (Q.SPECL [`(m_space m, measurable_sets m, nu)`,
                       `(m_space m, measurable_sets m, (\A. Normal e * measure m A))`]
                      RN_lemma2) \\
           RW_TAC std_ss [m_space_def, measurable_sets_def, measure_def] \\
           METIS_TAC [MEASURE_SPACE_CMUL, REAL_LT_IMP_LE, mul_not_infty, extreal_not_infty])
 >> Q.ABBREV_TAC `g' = (\x. g x + Normal e * indicator_fn (A') x)`
 >> `!A. A IN measurable_sets m ==>
         pos_fn_integral m (\x. g' x * indicator_fn A x) =
         pos_fn_integral m (\x. g x * indicator_fn A x) +
         Normal e * measure m (A INTER A')`
   by (rpt STRIP_TAC
       >> `measure m (A'' INTER A') =
             pos_fn_integral m (indicator_fn (A'' INTER A'))`
         by METIS_TAC [pos_fn_integral_indicator,MEASURE_SPACE_INTER]
       >> POP_ORW
       >> `Normal e * pos_fn_integral m (indicator_fn (A'' INTER A')) =
             pos_fn_integral m (\x. Normal e * indicator_fn (A'' INTER A') x)`
         by ((MATCH_MP_TAC o GSYM) pos_fn_integral_cmul
             >> RW_TAC real_ss [REAL_LT_IMP_LE,indicator_fn_def,le_01,le_refl])
       >> POP_ORW
       >> Q.UNABBREV_TAC `g'`
       >> `(\x. (\x. g x + Normal e * indicator_fn A' x) x * indicator_fn A'' x)
              =
           (\x. (\x. g x * indicator_fn A'' x) x +
                (\x. Normal e * indicator_fn (A'' INTER A') x) x)`
         by (RW_TAC std_ss [FUN_EQ_THM, indicator_fn_def, IN_INTER] \\
             METIS_TAC [mul_rone, mul_rzero, add_rzero, indicator_fn_def,
                        IN_INTER])
       >> POP_ORW
       >> MATCH_MP_TAC pos_fn_integral_add
       >> FULL_SIMP_TAC std_ss []
       >> CONJ_TAC
       >- (RW_TAC std_ss [indicator_fn_def,le_01,le_refl,mul_rone,mul_rzero]
           >> FULL_SIMP_TAC std_ss [extreal_of_num_def,extreal_le_def,
                                    REAL_LT_IMP_LE])
       >> RW_TAC std_ss []
           >- METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR, measure_space_def,
                         measurable_sets_def, subsets_def]
           >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
           >> RW_TAC std_ss []
           >> Q.EXISTS_TAC `indicator_fn (A'' INTER A')`
           >> Q.EXISTS_TAC `e`
           >> RW_TAC std_ss []
           >- FULL_SIMP_TAC std_ss [measure_space_def]
           >> MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR
           >> METIS_TAC [measure_space_def, measurable_sets_def, subsets_def,
                         MEASURE_SPACE_INTER, space_def])
 >> `!A. A IN measurable_sets m ==> ((A INTER A') IN measurable_sets m /\ (A INTER A') SUBSET A')`
        by METIS_TAC [INTER_SUBSET, MEASURE_SPACE_INTER]
 >> `!A. A IN measurable_sets m ==> 0 <= nu (A INTER A') - Normal e * measure m (A INTER A')`
        by (Q.UNABBREV_TAC `snu` >> METIS_TAC [])
 >> `!A. A IN measurable_sets m ==> Normal e * measure m (A INTER A') <= nu (A INTER A')`
        by (RW_TAC std_ss [] \\
           `Normal e * measure m (A'' INTER A') <> PosInf`
               by FULL_SIMP_TAC std_ss [mul_not_infty, REAL_LT_IMP_LE, MEASURE_SPACE_INTER] \\
           `Normal e * measure m (A'' INTER A') <> NegInf`
               by METIS_TAC [mul_not_infty, REAL_LT_IMP_LE, MEASURE_SPACE_INTER,
                             MEASURE_SPACE_POSITIVE, positive_not_infty] \\
            METIS_TAC [sub_zero_le])
 >> `!A. A IN measurable_sets m ==>
         pos_fn_integral m (\x. g x * indicator_fn A x) + Normal e * measure m (A INTER A') <=
         pos_fn_integral m (\x. g x * indicator_fn A x) + nu (A INTER A')`
        by METIS_TAC [le_ladd_imp]
 >> `!A. A IN measurable_sets m ==> nu (A INTER A') <= nu A`
        by (RW_TAC std_ss [] \\
            (MATCH_MP_TAC o REWRITE_RULE [measurable_sets_def, measure_def] o
             Q.SPEC `(m_space m,measurable_sets m,nu)`) INCREASING \\
             METIS_TAC [MEASURE_SPACE_INCREASING, MEASURE_SPACE_INTER, INTER_SUBSET])
 >> `!A. A IN measurable_sets m ==>
         pos_fn_integral m (\x. g x * indicator_fn A x) + Normal e * measure m (A INTER A') <=
         pos_fn_integral m (\x. g x * indicator_fn A x) + nu (A)`
        by METIS_TAC [le_ladd_imp,le_trans]
 >> `!A. A IN measurable_sets m ==>
         pos_fn_integral m (\x. g x * indicator_fn A x) +
         Normal e * measure m (A INTER A') <= measure v A`
        by (Q.UNABBREV_TAC `nu` >> FULL_SIMP_TAC std_ss [] \\
            RW_TAC std_ss [] >> METIS_TAC [sub_add2])
 >> `!A. A IN measurable_sets m ==>
         pos_fn_integral m (\x. g' x * indicator_fn A x) <= measure v A`
        by METIS_TAC []
 >> `g' IN RADON_F m v`
        by (RW_TAC std_ss [RADON_F_def,GSPECIFICATION]
            >- (Q.UNABBREV_TAC `g'` \\
                MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD \\
                Q.EXISTS_TAC `g` \\
                Q.EXISTS_TAC `(\x. Normal e * indicator_fn A' x)` \\
                CONJ_TAC >- FULL_SIMP_TAC std_ss [measure_space_def] \\
                FULL_SIMP_TAC std_ss [] \\
                CONJ_TAC
                >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL \\
                    METIS_TAC [measure_space_def, subsets_def, measurable_sets_def,
                               IN_MEASURABLE_BOREL_INDICATOR]) \\
                RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, num_not_infty, space_def] \\
                METIS_TAC [lt_infty, lte_trans, num_not_infty]) \\
            Q.UNABBREV_TAC `g'` \\
            RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, add_rzero] \\
            METIS_TAC [le_add2, add_rzero, le_trans, lt_imp_le,
                       extreal_lt_eq, extreal_of_num_def])
 >> `pos_fn_integral m g' IN RADON_F_integrals m v`
       by (FULL_SIMP_TAC std_ss [RADON_F_integrals_def, GSPECIFICATION] \\
           METIS_TAC [])
 >> `pos_fn_integral m (\x. g' x * indicator_fn (m_space m) x) =
     pos_fn_integral m (\x. g x * indicator_fn (m_space m) x) + Normal e * measure m A'`
       by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE,
                     MEASURE_SPACE_SUBSET_MSPACE, SUBSET_INTER2]
 >> `!x. 0 <= g' x`
       by (Q.UNABBREV_TAC `g'` \\
           RW_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero, add_rzero] \\
           METIS_TAC [le_add2, add_rzero, le_trans, lt_imp_le, extreal_lt_eq, extreal_of_num_def])
 >> `pos_fn_integral m g' = pos_fn_integral m g + Normal e * measure m A'`
       by METIS_TAC [pos_fn_integral_mspace]
 >> `0 < snu (m_space m)`
       by (Q.UNABBREV_TAC `snu` \\
           RW_TAC std_ss [] \\
          `?r1. nu (m_space m) = Normal r1` by METIS_TAC [extreal_cases] \\
          `?r2. measure m (m_space m) = Normal r2` by METIS_TAC [extreal_cases] \\
          `0 < r1` by METIS_TAC [extreal_of_num_def,extreal_lt_eq] \\
          `0 < r2` by METIS_TAC [extreal_of_num_def,extreal_lt_eq] \\
          `0 < 2 * r2` by RW_TAC real_ss [REAL_LT_MUL] \\
          `Normal e = nu (m_space m) / (2 * measure m (m_space m))` by RW_TAC std_ss [] \\
           POP_ORW \\
           REWRITE_TAC [extreal_of_num_def] \\
           FULL_SIMP_TAC std_ss [extreal_mul_def, extreal_div_eq, REAL_LT_IMP_NE,
                                 extreal_sub_def, extreal_lt_eq] \\
           RW_TAC real_ss [real_div, REAL_INV_MUL, REAL_LT_IMP_NE, REAL_MUL_ASSOC] \\
          `inv 2 * inv r2 * r2 = inv 2`
             by METIS_TAC [REAL_LT_IMP_NE, REAL_MUL_LINV, REAL_MUL_ASSOC, REAL_MUL_RID] \\
          `r1 - r1 * inv 2 * inv r2 * r2 = r1 / 2`
             by METIS_TAC [REAL_NEG_HALF, real_div, REAL_MUL_ASSOC] \\
           FULL_SIMP_TAC real_ss [REAL_LT_DIV])
 >> `0 < snu A'` by METIS_TAC [lte_trans]
 >> `Normal e * measure m A' <> PosInf` by METIS_TAC [REAL_LT_IMP_LE,mul_not_infty]
 >> `Normal e * measure m A' <> NegInf`
       by METIS_TAC [REAL_LT_IMP_LE, mul_not_infty, MEASURE_SPACE_POSITIVE,
                     positive_not_infty]
 >> `Normal e * measure m A' < nu (A')` by METIS_TAC [sub_zero_lt2]
 >> `0 <= Normal e * measure m A'`
       by METIS_TAC [le_mul, REAL_LT_IMP_LE, extreal_le_def, MEASURE_SPACE_POSITIVE,
                     positive_def, extreal_of_num_def]
 >> `0 < nu A'` by METIS_TAC [let_trans]
 >> `0 <> measure m A'`
       by (SPOSE_NOT_THEN ASSUME_TAC \\
          `measure v A' = 0`
             by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE,
                           measure_absolutely_continuous_def] \\
          `pos_fn_integral m (\x. g x * indicator_fn A' x) <= 0` by METIS_TAC [] \\
          `pos_fn_integral m (\x. g x * indicator_fn A' x) =  0` by METIS_TAC [le_antisym] \\
          `nu A' = 0` by (Q.UNABBREV_TAC `nu` >> METIS_TAC [sub_rzero]) \\
           METIS_TAC [lt_imp_ne])
 >> `0 < measure m A'`
       by METIS_TAC [lt_le, MEASURE_SPACE_POSITIVE, positive_def,
                     MEASURE_SPACE_MSPACE_MEASURABLE]
 >> `0 < Normal e * measure m A'`
       by METIS_TAC [lt_mul, extreal_lt_eq, extreal_of_num_def]
 >> `pos_fn_integral m g <> NegInf`
       by METIS_TAC [pos_fn_integral_pos, lt_infty, num_not_infty, lte_trans]
 >> `pos_fn_integral m g <> PosInf`
       by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE, pos_fn_integral_mspace]
 >> `pos_fn_integral m g < pos_fn_integral m g'`
       by METIS_TAC [let_add2, le_refl, num_not_infty, add_rzero]
 >> `pos_fn_integral m g' <= pos_fn_integral m g`
       by METIS_TAC [le_sup_imp, SPECIFICATION]
 >> METIS_TAC [extreal_lt_def]
QED

(* cf. measure_density_indicator for simplified statements *)
Theorem measure_restricted :
    !m s t. measure_space m /\
            s IN measurable_sets m /\ t IN measurable_sets m ==>
         (measure (m_space m, measurable_sets m,
           (\A. pos_fn_integral m (\x. indicator_fn s x * indicator_fn A x))) t =
          measure m (s INTER t))
Proof
  Q.X_GEN_TAC `M` THEN RW_TAC std_ss [] THEN
  `algebra (m_space M, measurable_sets M)` by
    METIS_TAC [measure_space_def, sigma_algebra_def] THEN
  `s INTER t IN measurable_sets M` by METIS_TAC [ALGEBRA_INTER, subsets_def] THEN
  Q.ABBREV_TAC `m = (m_space M,measurable_sets M,
          (\A. pos_fn_integral M (\x. indicator_fn s x * indicator_fn A x)))` THEN

 Suff `measure_space m` THEN1
 ( DISCH_TAC THEN `t IN measurable_sets m` by METIS_TAC [measurable_sets_def] THEN
   ASM_SIMP_TAC std_ss [GSYM pos_fn_integral_indicator] THEN
   ONCE_REWRITE_TAC [METIS [INDICATOR_FN_MUL_INTER]
    ``indicator_fn (s INTER t) = (\x. indicator_fn s x * indicator_fn t x)``] THEN
   ASM_CASES_TAC ``m_space M = {}`` THENL
   [Suff `measurable_sets M = {{}}` THENL
    [DISCH_TAC,
     FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def] THEN
     FULL_SIMP_TAC std_ss [space_def, subsets_def, subset_class_def] THEN
     UNDISCH_TAC ``!x. x IN measurable_sets M ==> x SUBSET {}`` THEN
     SIMP_TAC std_ss [SUBSET_EMPTY, EXTENSION, IN_SING] THEN DISCH_TAC THEN
     GEN_TAC THEN EQ_TAC THEN ASM_SIMP_TAC std_ss [] THEN DISCH_TAC THEN
     `x = {}` by ASM_SET_TAC [] THEN METIS_TAC []] THEN
    FULL_SIMP_TAC std_ss [IN_SING] THEN
    SIMP_TAC std_ss [indicator_fn_def, NOT_IN_EMPTY, mul_rzero] THEN
    ASM_SIMP_TAC std_ss [pos_fn_integral_zero],
    ALL_TAC] THEN
   Q.UNABBREV_TAC `m` THEN
   Suff `pos_fn_integral
          (m_space M,measurable_sets M,
           (\A. pos_fn_integral M (\x. max 0 (indicator_fn s x * indicator_fn A x))))
          (\x. max 0 (indicator_fn t x)) =
         pos_fn_integral M (\x. max 0 (indicator_fn s x * indicator_fn t x))` THENL
   [SIMP_TAC std_ss [extreal_max_def, le_mul, indicator_fn_pos_le] THEN
    METIS_TAC [], ALL_TAC] THEN
   MATCH_MP_TAC pos_fn_integral_density' THEN
   ASM_SIMP_TAC std_ss [] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
    METIS_TAC [subsets_def, measure_space_def],
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
    METIS_TAC [subsets_def, measure_space_def],
    ALL_TAC] THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [AE_ALT, GSPECIFICATION, null_set_def] THEN
    SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN Q.EXISTS_TAC `{}` THEN
    FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_alt_pow] THEN
    FULL_SIMP_TAC std_ss [positive_def, NOT_IN_EMPTY] THEN
    GEN_TAC THEN DISJ2_TAC THEN
    SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
    SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def],
    ALL_TAC] THEN
   GEN_TAC THEN
   SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
   SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def] ) THEN
  Q.UNABBREV_TAC `m` THEN
  FULL_SIMP_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def] THEN
  CONJ_TAC THENL
  [SIMP_TAC std_ss [positive_def, measure_def, measurable_sets_def] THEN
   SIMP_TAC std_ss [indicator_fn_def, NOT_IN_EMPTY, mul_rzero] THEN
   FULL_SIMP_TAC std_ss [COND_ID, pos_fn_integral_zero, measure_space_def] THEN
   GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC pos_fn_integral_pos THEN
   FULL_SIMP_TAC std_ss [measure_space_def] THEN GEN_TAC THEN
   REPEAT COND_CASES_TAC THEN
   SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def, mul_rone, mul_rzero],
   ALL_TAC] THEN
  SIMP_TAC std_ss [countably_additive_alt_eq, INDICATOR_FN_MUL_INTER] THEN
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [o_DEF] THEN
  `!x. A x IN measurable_sets M` by ASM_SET_TAC [] THEN
  ASM_SIMP_TAC std_ss [INTER_BIGUNION, GSPECIFICATION, IN_UNIV] THEN
  REWRITE_TAC [SET_RULE ``{s INTER x | ?i'. x = A i'} = {s INTER A i' | i' IN UNIV}``] THEN
  SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
  Suff `!x. indicator_fn (BIGUNION (IMAGE (\i'. s INTER A i') univ(:num))) x =
   suminf (\j. indicator_fn ((\i'. s INTER A i') j) x)` THENL
  [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
   GEN_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC indicator_fn_suminf THEN
  FULL_SIMP_TAC std_ss [disjoint_family, disjoint_family_on, DISJOINT_DEF] THEN
  ASM_SET_TAC []] THEN ONCE_REWRITE_TAC [METIS [ETA_AX]
   ``(\x'. indicator_fn (s INTER A x) x') = (\x. indicator_fn (s INTER A x)) x``] THEN
  ONCE_REWRITE_TAC [METIS [] ``suminf (\j. indicator_fn (s INTER A j) x) =
                       suminf (\j. (\k. indicator_fn (s INTER A k)) j x)``] THEN
  MATCH_MP_TAC pos_fn_integral_suminf THEN ASM_SIMP_TAC std_ss [measure_space_def] THEN
  CONJ_TAC THENL
  [SIMP_TAC std_ss [indicator_fn_def] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
   SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def], ALL_TAC] THEN
  GEN_TAC THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
  Q.EXISTS_TAC `s INTER A i` THEN ASM_SIMP_TAC std_ss [] THEN
  MATCH_MP_TAC ALGEBRA_INTER THEN
  FULL_SIMP_TAC std_ss [sigma_algebra_def, subsets_def] THEN
  METIS_TAC []
QED

(* |- !m s t.
          measure_space m /\ s IN measurable_sets m /\ t IN measurable_sets m ==>
          measure (density m (indicator_fn s)) t = measure m (s INTER t)
 *)
val measure_density_indicator = save_thm
  ("measure_density_indicator",
    REWRITE_RULE [GSYM density_def, GSYM density_measure_def] measure_restricted);

(* NOTE: changed the universal quantifier ‘I’ to ‘J’ *)
Theorem measure_subadditive_finite :
   !J A M. measure_space M /\ FINITE J /\
           IMAGE A J SUBSET measurable_sets M ==>
           measure M (BIGUNION {A i | (i:num) IN J}) <=
           SIGMA (\i. measure M (A i)) J
Proof
  RW_TAC std_ss [] THEN NTAC 2 (POP_ASSUM MP_TAC) THEN
  qid_spec_tac ‘J’ THEN SET_INDUCT_TAC THEN1
  (SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, NOT_IN_EMPTY] THEN
   REWRITE_TAC [SET_RULE ``{A i | i | F} = {}``] THEN
   FULL_SIMP_TAC std_ss [BIGUNION_EMPTY, measure_space_def, positive_def] THEN
   SIMP_TAC std_ss [le_refl]) THEN
  REWRITE_TAC [SET_RULE ``BIGUNION {A i | i IN e INSERT s} =
                          BIGUNION {A i | i IN s} UNION A e``] THEN
  DISCH_TAC THEN MATCH_MP_TAC le_trans THEN
  Q.EXISTS_TAC `measure M (BIGUNION {A i | i IN s}) + measure M (A e)` THEN
  CONJ_TAC THEN1
  (Know `measure M (BIGUNION {A i | i IN s} UNION A e) =
         measure M (BIGUNION {A i | i IN s}) +
         measure M (A e DIFF BIGUNION {A i | i IN s})` THEN1
   (MATCH_MP_TAC ADDITIVE THEN
    ASM_SIMP_TAC std_ss [MEASURE_SPACE_ADDITIVE] THEN
    REPEAT CONJ_TAC THENL (* 5 subgoals *)
    [(* goal 1 (of 5) *)
     ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
     MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION THEN
     FULL_SIMP_TAC std_ss [measure_space_def] THEN
     CONJ_TAC >- (SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
      MATCH_MP_TAC image_countable THEN
      SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM]) THEN
     SIMP_TAC std_ss [GSYM IMAGE_DEF, SUBSET_DEF, IN_IMAGE, subsets_def, GSPECIFICATION] THEN
     GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_SET_TAC [],
     (* goal 2 (of 5) *)
     ONCE_REWRITE_TAC [METIS [subsets_def]
       ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
     MATCH_MP_TAC ALGEBRA_DIFF THEN
     FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def] THEN
     SIMP_TAC std_ss [subsets_def] THEN CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
     ONCE_REWRITE_TAC [METIS [subsets_def]
       ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
     MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION THEN
     FULL_SIMP_TAC std_ss [sigma_algebra_def] THEN
     CONJ_TAC THENL [SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
       MATCH_MP_TAC image_countable THEN
       SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM], ALL_TAC] THEN
     SIMP_TAC std_ss [GSYM IMAGE_DEF, SUBSET_DEF, IN_IMAGE, subsets_def, GSPECIFICATION] THEN
     GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_SET_TAC [],
     (* goal 3 of 5) *)
     ASM_SIMP_TAC std_ss [DISJOINT_DEF] THEN SET_TAC [],
     (* goal 4 of 5) *)
     FULL_SIMP_TAC std_ss [IMAGE_INSERT] \\
    `A e IN measurable_sets M` by ASM_SET_TAC [] \\
    `IMAGE A s SUBSET measurable_sets M` by ASM_SET_TAC [] \\
     ONCE_REWRITE_TAC [METIS [subsets_def]
       ``measurable_sets m = subsets (m_space m, measurable_sets m)``] \\
     MATCH_MP_TAC ALGEBRA_UNION \\
     FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def] \\
    `{A i | i IN s} = IMAGE A s` by SET_TAC [] >> POP_ORW \\
     reverse CONJ_TAC >- FULL_SIMP_TAC std_ss [subsets_def] \\
     MATCH_MP_TAC ALGEBRA_FINITE_UNION \\
     FULL_SIMP_TAC std_ss [IMAGE_FINITE, subsets_def],
     (* goal 5 of 5) *)
     SET_TAC [] ]) THEN DISC_RW_KILL THEN
   MATCH_MP_TAC le_ladd_imp THEN MATCH_MP_TAC INCREASING THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING] THEN
   CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
   CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN
   ONCE_REWRITE_TAC [METIS [subsets_def]
    ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
    MATCH_MP_TAC ALGEBRA_DIFF THEN
    FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def] THEN
    CONJ_TAC THENL [ASM_SET_TAC [subsets_def], ALL_TAC] THEN
    MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION THEN
    FULL_SIMP_TAC std_ss [sigma_algebra_def] THEN
    CONJ_TAC THENL [SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
     MATCH_MP_TAC image_countable THEN
     SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM], ALL_TAC] THEN
    SIMP_TAC std_ss [GSYM IMAGE_DEF, SUBSET_DEF, IN_IMAGE, subsets_def, GSPECIFICATION] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_SET_TAC [] ) THEN
   Suff `SIGMA (\i. measure M (A i)) (e INSERT s) =
    SIGMA (\i. measure M (A i)) (s DELETE e) + (\i. measure M (A i)) e` THENL
   [DISC_RW_KILL THEN SIMP_TAC std_ss [] THEN MATCH_MP_TAC le_radd_imp THEN
    ASM_SIMP_TAC std_ss [SET_RULE ``e NOTIN s ==> (s DELETE e = s)``] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SET_TAC [],
    ALL_TAC] THEN
   ASM_CASES_TAC ``!x:num. x IN e INSERT s ==> ((\i. measure M (A i)) x <> PosInf)`` THENL
   [`(\i. measure M (A i)) e <> PosInf` by (FIRST_ASSUM MATCH_MP_TAC THEN ASM_SET_TAC []) THEN
    `SIGMA (\i. measure M (A i)) (s DELETE e) <> PosInf`
     by (MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF THEN
         ASM_SIMP_TAC std_ss [SET_RULE ``e NOTIN s ==> (s DELETE e = s)``] THEN
         ASM_SET_TAC []) THEN
    `SIGMA (\i. measure M (A i)) (s DELETE e) + (\i. measure M (A i)) e =
     (\i. measure M (A i)) e + SIGMA (\i. measure M (A i)) (s DELETE e)`
      by METIS_TAC [add_comm] THEN ONCE_ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP EXTREAL_SUM_IMAGE_PROPERTY_POS) THEN
    POP_ASSUM MATCH_MP_TAC THEN FULL_SIMP_TAC std_ss [],
    ALL_TAC] THEN FULL_SIMP_TAC std_ss [] THEN
   Suff `!x. x IN s ==> (\i. measure M (A i)) x <= SIGMA (\i. measure M (A i)) s` THENL
   [DISCH_TAC,
    MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS_MEM_LE THEN RW_TAC std_ss [] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP MEASURE_SPACE_POSITIVE) THEN
    FULL_SIMP_TAC std_ss [positive_def] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SET_TAC []] THEN
   Suff `!x. x IN (e INSERT s) ==>
    (\i. measure M (A i)) x <= SIGMA (\i. measure M (A i)) (e INSERT s)` THENL
   [DISCH_TAC,
    MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS_MEM_LE THEN RW_TAC std_ss [FINITE_INSERT] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP MEASURE_SPACE_POSITIVE) THEN
    FULL_SIMP_TAC std_ss [positive_def] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SET_TAC []] THEN
   POP_ASSUM (MP_TAC o Q.SPEC `x`) THEN ASM_SIMP_TAC std_ss [le_infty] THEN
   DISCH_TAC THEN UNDISCH_TAC ``(x:num) IN e INSERT s`` THEN
   Suff `SIGMA (\i. measure M (A i)) (s DELETE e) <> NegInf` THENL
   [DISCH_TAC,
    MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF THEN
    ASM_SIMP_TAC std_ss [SET_RULE ``e NOTIN s ==> (s DELETE e = s)``] THEN
    RW_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
    Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP MEASURE_SPACE_POSITIVE) THEN
    FULL_SIMP_TAC std_ss [positive_def] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SET_TAC []] THEN
   RW_TAC std_ss [INSERT_DEF, GSPECIFICATION] THENL
   [ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC ``SIGMA (\i:num. measure M (A i)) (s DELETE e) = PosInf`` THENL
    [FULL_SIMP_TAC std_ss [extreal_add_def], ALL_TAC] THEN
    METIS_TAC [normal_real, extreal_add_def],
    ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `x`) THEN ASM_SIMP_TAC std_ss [le_infty] THEN
   ASM_SIMP_TAC std_ss [SET_RULE ``e NOTIN s ==> (s DELETE e = s)``] THEN
   DISCH_TAC THEN Suff `measure M (A e) <> NegInf` THENL
   [DISCH_TAC,
    RW_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
    Q.EXISTS_TAC `0` THEN SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP MEASURE_SPACE_POSITIVE) THEN
    FULL_SIMP_TAC std_ss [positive_def] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SET_TAC []] THEN
   ASM_CASES_TAC ``measure M (A (e:num)) = PosInf`` THENL
   [FULL_SIMP_TAC std_ss [extreal_add_def], ALL_TAC] THEN
   METIS_TAC [normal_real, extreal_add_def]
QED

(* A0 and B (all djsjoint) are in measurable_sets M, together `m_space M`.

  `measure N (B i) <> PosInf` although `measure N (m_space M) = PosInf`,
   i.e. `m_space M` is splited with all infinite measures only in A0.
 *)
Theorem split_space_into_finite_sets_and_rest[local] :
    !M N. measure_space M /\ measure_space N /\
         (m_space M = m_space N) /\ (measurable_sets M = measurable_sets N) /\
          measure M (m_space M) <> PosInf /\
          measure_absolutely_continuous (measure N) M ==>
       ?A0 B. A0 IN measurable_sets M /\ disjoint_family B /\
              IMAGE B univ(:num) SUBSET measurable_sets M /\
             (A0 = m_space M DIFF BIGUNION {B i | i IN UNIV}) /\
             (!A. A IN measurable_sets M /\ A SUBSET A0 ==>
                  (((measure M A = 0) /\ (measure N A = 0)) \/
                   (0 < measure M A /\ (measure N A = PosInf)))) /\
             (!i. measure N (B i) <> PosInf)
Proof
  RW_TAC std_ss [] THEN
  Q.ABBREV_TAC `Q = {x | x IN measurable_sets M /\ (measure N x <> PosInf)}` THEN
  Q.ABBREV_TAC `a = sup {measure M x | x IN Q}` THEN
  Know `{} IN Q`
  >- (Q.UNABBREV_TAC `Q` >> RW_TAC std_ss [GSPECIFICATION] \\
      FULL_SIMP_TAC std_ss [measure_space_def, positive_def, num_not_infty,
                            sigma_algebra_alt_pow]) >> DISCH_TAC \\
  `Q <> {}` by ASM_SET_TAC [] THEN
  Know `a <= measure M (m_space M)`
  >- (Q.UNABBREV_TAC `a` THEN REWRITE_TAC [sup_le'] THEN GEN_TAC THEN
      SIMP_TAC std_ss [GSPECIFICATION] THEN RW_TAC std_ss [] THEN
      MATCH_MP_TAC INCREASING THEN
      ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE, MEASURE_SPACE_INCREASING] THEN
      Q.UNABBREV_TAC `Q` THEN
      REV_FULL_SIMP_TAC std_ss [GSPECIFICATION, MEASURE_SPACE_SUBSET_MSPACE])
  THEN DISCH_TAC THEN
  Know `a <> PosInf`
  >- (Q.UNABBREV_TAC `a` THEN FULL_SIMP_TAC std_ss [lt_infty] THEN
      MATCH_MP_TAC let_trans THEN Q.EXISTS_TAC `measure M (m_space M)` THEN
      ASM_SIMP_TAC std_ss []) THEN DISCH_TAC THEN
  Know `?Q''. IMAGE Q'' UNIV SUBSET IMAGE (measure M) Q /\
             (a = sup {Q'' i | i IN univ(:num)})`
  >- (FIRST_ASSUM (ASSUME_TAC o MATCH_MP sup_seq_countable_seq) THEN
      POP_ASSUM (MP_TAC o Q.SPEC `(\x. measure M x)`) THEN STRIP_TAC THEN
      Q.EXISTS_TAC `f` THEN METIS_TAC []) THEN STRIP_TAC THEN
  Know `!i. ?Q'. (Q'' i = measure M Q') /\ Q' IN Q`
  >- (ASM_SET_TAC []) THEN STRIP_TAC THEN
  Know `?Q'. !i. (Q'' i = measure M (Q' i)) /\ Q' i IN Q`
  >- (METIS_TAC []) THEN STRIP_TAC THEN
  Know `a = sup {measure M (Q' i) | i IN univ(:num)}`
  >- (FULL_SIMP_TAC std_ss []) THEN DISCH_TAC THEN
  Q.ABBREV_TAC `D = (\n. BIGUNION {Q' i | i <= n:num})` THEN
  Know `sup {measure M (D i) | i IN univ(:num)} =
        measure M (BIGUNION {D i | i IN univ(:num)})` >-
  (SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
   MATCH_MP_TAC (REWRITE_RULE [o_DEF] MONOTONE_CONVERGENCE2) THEN
   ASM_REWRITE_TAC [] THEN CONJ_TAC >-
   (Q.UNABBREV_TAC `D` THEN SRW_TAC[] [IN_DEF, IN_FUNSET] THEN
    ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN RW_TAC std_ss [] THEN
    ONCE_REWRITE_TAC [SET_RULE ``{Q' i' | i' <= i} =
             IMAGE (\i':num. Q' i') {i' | i' <= i}``] THEN
    ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
    MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION THEN
    FULL_SIMP_TAC std_ss [measure_space_def] THEN
    CONJ_TAC >- (MATCH_MP_TAC image_countable THEN
                 SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM]) THEN
    SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE, subsets_def, GSPECIFICATION] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o Q.SPEC `i'`) THEN
    Q.UNABBREV_TAC `Q` THEN SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC []) THEN
   Q.UNABBREV_TAC `D` THEN
   RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION, GSPECIFICATION] THEN
   Q.EXISTS_TAC `Q' i` THEN ASM_REWRITE_TAC [] THEN
   Q.EXISTS_TAC `i` THEN ASM_SIMP_TAC arith_ss [] ) THEN DISCH_TAC THEN
  Know `!i. Q' i IN measurable_sets M`
  >- (GEN_TAC THEN FIRST_X_ASSUM (MP_TAC o Q.SPEC `i`) THEN
      Q.UNABBREV_TAC `Q` THEN
      RW_TAC std_ss [GSPECIFICATION] THEN METIS_TAC []) THEN DISCH_TAC THEN
  Know `!i. D i IN measurable_sets M`
  >- (Q.UNABBREV_TAC `D` THEN RW_TAC std_ss [] THEN
      ONCE_REWRITE_TAC [SET_RULE ``{Q' i' | i' <= i} =
                        IMAGE (\i':num. Q' i') {i' | i' <= i}``] THEN
      ONCE_REWRITE_TAC [METIS [subsets_def]
       ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
      MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION THEN
      FULL_SIMP_TAC std_ss [measure_space_def] THEN
      CONJ_TAC >- (MATCH_MP_TAC image_countable THEN
                   SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM]) THEN
      SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE, subsets_def, GSPECIFICATION] THEN
      GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN METIS_TAC []) THEN
  DISCH_TAC THEN
  Know `!i. D i IN Q`
  >- (Know `!i. IMAGE Q' {x | x <= i} SUBSET measurable_sets M`
      >- (RW_TAC std_ss [SUBSET_DEF, IN_IMAGE] THEN METIS_TAC []) THEN
      DISCH_TAC THEN
      Suff `!i. measure N (D i) <= SIGMA (\i. measure N (Q' i)) {x | x <= i}`
      >- (DISCH_TAC THEN GEN_TAC THEN qunabbrevl_tac [`D`, `Q`] THEN
          FULL_SIMP_TAC std_ss [GSPECIFICATION] THEN CONJ_TAC THENL
          [METIS_TAC [], ALL_TAC] THEN
          REWRITE_TAC [lt_infty] THEN MATCH_MP_TAC let_trans THEN
          Q.EXISTS_TAC `SIGMA (\i. measure N (Q' i)) {x | x <= i}` THEN
          ASM_REWRITE_TAC [GSYM lt_infty] THEN
          MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF THEN
          SIMP_TAC std_ss [FINITE_NUMSEG_LE, GSPECIFICATION] THEN
          GEN_TAC THEN DISCH_TAC THEN
          Q.PAT_X_ASSUM `!i. (Q'' i = measure M (Q' i)) /\ _` MP_TAC THEN
          DISCH_THEN (MP_TAC o Q.SPEC `x`) THEN SIMP_TAC std_ss []) THEN
      GEN_TAC THEN Q.UNABBREV_TAC `D` THEN BETA_TAC THEN
      ONCE_REWRITE_TAC [SET_RULE ``(BIGUNION {Q' i' | i' <= i:num}) =
                      (BIGUNION {Q' i' | i' IN {x | x <= i}})``] THEN
      MATCH_MP_TAC measure_subadditive_finite THEN
      ASM_SIMP_TAC std_ss [FINITE_NUMSEG_LE] THEN METIS_TAC []) THEN DISCH_TAC THEN
  Know `!n. D n SUBSET D (SUC n)`
  >- (Q.UNABBREV_TAC `D` THEN
      GEN_TAC THEN SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION] THEN
      GEN_TAC THEN SIMP_TAC std_ss [GSPECIFICATION] THEN STRIP_TAC THEN
      Q.EXISTS_TAC `Q' i` THEN FULL_SIMP_TAC std_ss [] THEN
      Q.EXISTS_TAC `i` THEN FULL_SIMP_TAC arith_ss []) THEN DISCH_TAC THEN
  Know `a = measure M (BIGUNION {D i | i IN univ(:num)})`
  >- (REWRITE_TAC [GSYM le_antisym] THEN CONJ_TAC >-
      (ASM_REWRITE_TAC [sup_le'] THEN GEN_TAC THEN
       SIMP_TAC std_ss [GSPECIFICATION] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
       MATCH_MP_TAC INCREASING THEN ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING] THEN
       reverse CONJ_TAC
       >- (ONCE_REWRITE_TAC [METIS [subsets_def]
            ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
           MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION THEN
           FULL_SIMP_TAC std_ss [measure_space_def, GSYM IMAGE_DEF] THEN
           CONJ_TAC THENL [MATCH_MP_TAC image_countable THEN
              SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM], ALL_TAC] THEN
           SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE, subsets_def, GSPECIFICATION] THEN
           GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN METIS_TAC []) \\
       Q.UNABBREV_TAC `D` THEN
       SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, GSPECIFICATION] THEN
       GEN_TAC THEN STRIP_TAC THEN
       Q.EXISTS_TAC `BIGUNION {Q' x | x <= i}` THEN
       CONJ_TAC THENL [ALL_TAC, METIS_TAC [IN_UNIV]] THEN
       ASM_SIMP_TAC arith_ss [IN_BIGUNION, GSPECIFICATION] THEN
       Q.EXISTS_TAC `Q' i` THEN METIS_TAC [LESS_OR_EQ]) THEN
      UNDISCH_TAC ``sup {measure M (D i) | i IN univ(:num)} =
          measure M (BIGUNION {D i | i IN univ(:num)})`` THEN
      GEN_REWR_TAC LAND_CONV [EQ_SYM_EQ] THEN SIMP_TAC std_ss [] THEN DISCH_TAC THEN
      Suff `!n. BIGUNION {Q' i | i <= n} = D n` THENL
      [DISCH_TAC, METIS_TAC []] THEN
      Suff `!n. ?x. x IN Q /\ measure M (BIGUNION {Q' i | i <= n}) <= measure M x` THENL
      [DISCH_TAC,
       GEN_TAC THEN Q.EXISTS_TAC `D n` THEN ASM_SIMP_TAC std_ss [le_refl]] THEN
      Q.UNABBREV_TAC `a` THEN SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
      MATCH_MP_TAC sup_le_sup_imp THEN GEN_TAC THEN
      GEN_REWR_TAC LAND_CONV [GSYM SPECIFICATION] THEN
      SIMP_TAC std_ss [IN_IMAGE] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o Q.SPEC `i`) THEN STRIP_TAC THEN
      Q.EXISTS_TAC `measure M x'` THEN
      Q.UNABBREV_TAC `D` THEN BETA_TAC THEN ASM_REWRITE_TAC [] THEN
      ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [IN_IMAGE] THEN
      METIS_TAC [] ) THEN DISCH_TAC THEN
  Q.ABBREV_TAC `O_o = BIGUNION {(D:num->'a->bool) i | i IN UNIV}` THEN
  Know `O_o IN measurable_sets M`
  >- (Q.UNABBREV_TAC `O_o` THEN
      ONCE_REWRITE_TAC [METIS [subsets_def]
       ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
      MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION THEN
      FULL_SIMP_TAC std_ss [measure_space_def, GSYM IMAGE_DEF] THEN
      CONJ_TAC THENL [MATCH_MP_TAC image_countable THEN
        SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM], ALL_TAC] THEN
      SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE, subsets_def, GSPECIFICATION] THEN
      GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN METIS_TAC []) THEN
  DISCH_TAC THEN
  Q.ABBREV_TAC `(QQ) = (\i. if i = 0 then (Q':num->'a->bool) 0
                         else D i DIFF (D:num->'a->bool) (i - 1))` THEN
  Know `!i. QQ i IN measurable_sets M`
  >- (GEN_TAC THEN ASM_CASES_TAC ``i = 0:num``
      >- (Q.UNABBREV_TAC `QQ` THEN ASM_SIMP_TAC std_ss [] THEN
          METIS_TAC []) THEN
      Know `?n. i = SUC n`
      >- (Q.EXISTS_TAC `PRE i` THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
          REWRITE_TAC [GSYM SUC_PRE] THEN ASM_SIMP_TAC arith_ss []) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      Q.UNABBREV_TAC `QQ` THEN ASM_SIMP_TAC arith_ss [] THEN
      ONCE_REWRITE_TAC [METIS [subsets_def]
        ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
      MATCH_MP_TAC ALGEBRA_DIFF THEN SIMP_TAC std_ss [subsets_def] THEN
      CONJ_TAC THENL [ALL_TAC, METIS_TAC []] THEN
      FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def]) THEN
  DISCH_TAC THEN
  Q.EXISTS_TAC `QQ` THEN CONJ_TAC THENL
  [ONCE_REWRITE_TAC [METIS [subsets_def]
    ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
   MATCH_MP_TAC ALGEBRA_DIFF THEN CONJ_TAC THENL
   [FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def],
    ALL_TAC] THEN CONJ_TAC THENL
   [METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE, subsets_def],
    ALL_TAC] THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION THEN
   FULL_SIMP_TAC std_ss [measure_space_def, GSYM IMAGE_DEF] THEN
   CONJ_TAC THENL [MATCH_MP_TAC image_countable THEN
    SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM], ALL_TAC] THEN
   SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE, subsets_def, GSPECIFICATION] THEN
   GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN METIS_TAC [], ALL_TAC] THEN
  CONJ_TAC THENL
  [SIMP_TAC std_ss [disjoint_family, disjoint_family_on, IN_UNIV] THEN
   REPEAT STRIP_TAC THEN Q.UNABBREV_TAC `QQ` THEN BETA_TAC THEN
   SIMP_TAC std_ss [INTER_DEF, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION] THEN
   GEN_TAC THEN REPEAT COND_CASES_TAC THENL (* 4 subgoals *)
   [(* goal 1 (of 4) *)
    FULL_SIMP_TAC arith_ss [],
    (* goal 2 (of 4) *)
    ASM_CASES_TAC ``(x:'a) NOTIN Q' (0:num)`` THEN FULL_SIMP_TAC std_ss [] THEN
    `1 <= n` by ASM_SIMP_TAC arith_ss [] THEN
    SIMP_TAC std_ss [Abbr ‘D’, IN_DIFF, IN_BIGUNION, GSPECIFICATION] \\
    Cases_on `!s. x NOTIN s \/ !i. s = Q' i ==> ~(i <= n)` >- art [] \\
    DISJ2_TAC \\
    Q.EXISTS_TAC `Q' 0` >> ASM_SIMP_TAC std_ss [] \\
    Q.EXISTS_TAC `0` >> SIMP_TAC arith_ss [],
    (* goal 3 (of 4) *)
    ASM_CASES_TAC ``(x:'a) NOTIN Q' (0:num)`` THEN FULL_SIMP_TAC std_ss [] THEN
    `1 <= m` by ASM_SIMP_TAC arith_ss [] THEN
    SIMP_TAC std_ss [Abbr ‘D’, IN_DIFF, IN_BIGUNION, GSPECIFICATION] \\
    Cases_on `!s. x NOTIN s \/ !i. s = Q' i ==> ~(i <= m)` >- art [] \\
    DISJ2_TAC \\
    Q.EXISTS_TAC `Q' 0` >> ASM_SIMP_TAC std_ss [] \\
    Q.EXISTS_TAC `0` >> SIMP_TAC arith_ss [],
    (* goal 4 (of 4) *)
    ALL_TAC] THEN
   ASM_CASES_TAC ``x NOTIN (D:num->'a->bool) m DIFF D (m - 1)`` THEN
   FULL_SIMP_TAC std_ss [IN_DIFF] THEN
   ASM_CASES_TAC ``m < n:num`` THENL
   [ASM_CASES_TAC ``x NOTIN (D:num->'a->bool) n`` THEN ASM_SIMP_TAC std_ss [] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    Q.UNABBREV_TAC `D` THEN BETA_TAC THEN
    SIMP_TAC std_ss [IN_BIGUNION, GSPECIFICATION] THEN REPEAT STRIP_TAC THEN
    Q.EXISTS_TAC `s` THEN ASM_REWRITE_TAC [] THEN Q.EXISTS_TAC `i` THEN
    ASM_SIMP_TAC arith_ss [], ALL_TAC] THEN
   ASM_CASES_TAC ``x IN (D:num->'a->bool) (n - 1)`` THEN ASM_SIMP_TAC std_ss [] THEN
   POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
   POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
   SIMP_TAC std_ss [Abbr ‘D’, IN_BIGUNION, GSPECIFICATION] \\
   rpt STRIP_TAC \\
   `n < m` by FULL_SIMP_TAC arith_ss [] \\
   NTAC 2 (POP_ASSUM MP_TAC) \\
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `s'`) THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN DISJ2_TAC THEN GEN_TAC THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `i':num`) THEN STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN STRIP_TAC \\
   FULL_SIMP_TAC arith_ss [NOT_LESS_EQUAL], ALL_TAC] THEN
  CONJ_TAC >- ASM_SET_TAC [] THEN
  reverse CONJ_TAC >-
  (GEN_TAC THEN Q.UNABBREV_TAC `QQ` THEN BETA_TAC THEN
   ASM_CASES_TAC ``i = 0:num`` THEN ASM_SIMP_TAC std_ss [] THENL
   [ASM_SET_TAC [], ALL_TAC] THEN
   SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC let_trans THEN
   Q.EXISTS_TAC `measure N (D i) - measure N (D (i - 1))` THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [le_lt] THEN DISJ2_TAC THEN
    MATCH_MP_TAC MEASURE_SPACE_FINITE_DIFF_SUBSET THEN
    ASM_SIMP_TAC std_ss [] THEN REPEAT (CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC]) THEN
    CONJ_TAC THENL [METIS_TAC [ARITH_PROVE ``i <> 0 ==> (i = SUC (i - 1))``], ALL_TAC] THEN
    ASM_SET_TAC [], ALL_TAC] THEN
   REWRITE_TAC [GSYM lt_infty] THEN MATCH_MP_TAC (METIS [sub_not_infty]
    ``x <> PosInf /\ y <> NegInf ==> x - y <> PosInf``) THEN
   CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
   `positive N` by METIS_TAC [MEASURE_SPACE_POSITIVE] THEN
   FULL_SIMP_TAC std_ss [positive_def, lt_infty] THEN
   MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `0` THEN
   SIMP_TAC std_ss [GSYM lt_infty, num_not_infty] THEN
   FIRST_ASSUM MATCH_MP_TAC THEN METIS_TAC [] ) THEN
  GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC ``0 < measure M A ==> (measure N (A:'a->bool) <> PosInf)`` THENL
  [ALL_TAC, FULL_SIMP_TAC std_ss []] THEN
  ASM_CASES_TAC ``measure M (A:'a->bool) = 0`` THENL
  [FULL_SIMP_TAC std_ss [measure_absolutely_continuous_def], ALL_TAC] THEN
  `positive M` by METIS_TAC [MEASURE_SPACE_POSITIVE] THEN
  POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [positive_def])) THEN
  POP_ASSUM (MP_TAC o Q.SPEC `A`) THEN
  ASM_REWRITE_TAC [le_lt] THEN STRIP_TAC THENL [ALL_TAC, METIS_TAC []] THEN
  ASM_REWRITE_TAC [] THEN UNDISCH_TAC ``0 < measure M A ==> measure N A <> PosInf`` THEN
  ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
  Know `measure M O_o + measure M A = measure M (O_o UNION A)` >-
  (ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC ADDITIVE THEN
   ASM_SIMP_TAC std_ss [MEASURE_SPACE_ADDITIVE, DISJOINT_DEF] THEN
   reverse CONJ_TAC
   >- (MATCH_MP_TAC MEASURE_SPACE_UNION >> rfs []) THEN
   Q.PAT_X_ASSUM  `A SUBSET m_space N DIFF BIGUNION {QQ i | i IN univ(:num)}` MP_TAC THEN
   qunabbrevl_tac [`QQ`, `O_o`] THEN BETA_TAC THEN
   Suff `BIGUNION {D i | i IN univ(:num)} =
         BIGUNION {if i = 0 then Q' 0 else D i DIFF D (i - 1) | i IN univ(:num)}`
   >- (Rewr' >> SET_TAC []) THEN
   SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, GSPECIFICATION, IN_UNIV] THEN
   GEN_TAC THEN EQ_TAC THEN STRIP_TAC
   >- (FULL_SIMP_TAC std_ss [] THEN POP_ASSUM K_TAC THEN
       ASM_CASES_TAC ``x IN (D:num->'a->bool) 0``
       >- (Q.EXISTS_TAC `D 0` THEN FULL_SIMP_TAC std_ss [] THEN
           Q.EXISTS_TAC `0` THEN
           Q.UNABBREV_TAC `D` THEN SIMP_TAC std_ss [] THEN
           SET_TAC []) THEN
       Suff `?i. i <> 0 /\ x IN D i DIFF D (i - 1)` THENL
       [STRIP_TAC THEN Q.EXISTS_TAC `D i' DIFF D (i' - 1)` THEN
        ASM_REWRITE_TAC [] THEN METIS_TAC [], ALL_TAC] THEN
       Induct_on `i` THENL [METIS_TAC [], ALL_TAC] THEN
       DISCH_TAC THEN ASM_CASES_TAC ``x IN D (SUC i) DIFF ((D:num->'a->bool) i)`` THENL
       [Q.EXISTS_TAC `SUC i` THEN ASM_SIMP_TAC arith_ss [], ALL_TAC] THEN
       ASM_SET_TAC []) THEN
   FULL_SIMP_TAC std_ss [] THEN POP_ASSUM K_TAC THEN
   ASM_CASES_TAC ``i = 0:num``
   >- (Q.EXISTS_TAC `Q' 0` THEN FULL_SIMP_TAC std_ss [] THEN
       Q.UNABBREV_TAC `D` THEN Q.EXISTS_TAC `0` THEN
       BETA_TAC THEN SET_TAC []) THEN
   FULL_SIMP_TAC std_ss [] THEN Q.EXISTS_TAC `D i` THEN CONJ_TAC THENL
   [ALL_TAC, METIS_TAC []] THEN
   ASM_SET_TAC [] ) THEN DISCH_TAC THEN
  Know `measure M (BIGUNION {D i | i IN univ(:num)} UNION A) =
             sup {measure M ((D i) UNION A) | i IN univ(:num)}` >-
  (SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
   `(\i. measure M (D i UNION A)) = measure M o (\i. (D:num->'a->bool) i UNION A)`
     by SIMP_TAC std_ss [o_DEF] THEN
   FIRST_X_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
   ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC MONOTONE_CONVERGENCE THEN
   ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
   [EVAL_TAC THEN SRW_TAC[][IN_DEF,IN_FUNSET]  THEN
    ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
    ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
    MATCH_MP_TAC ALGEBRA_UNION THEN
    FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def] THEN
    METIS_TAC [subsets_def], ALL_TAC] THEN
   CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC (SET_RULE ``a SUBSET c /\ b SUBSET d ==>
                  a UNION b SUBSET c UNION d``) THEN
    ASM_SIMP_TAC std_ss [SUBSET_REFL], ALL_TAC] THEN
   GEN_REWR_TAC (LAND_CONV o RAND_CONV) [SET_RULE ``A = BIGUNION {A}``] THEN
   REWRITE_TAC [GSYM BIGUNION_UNION] THEN
   SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, IN_IMAGE, IN_UNIV, GSPECIFICATION, IN_UNION] THEN
   GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [Q.EXISTS_TAC `D x' UNION A` THEN ASM_SET_TAC [],
    Q.EXISTS_TAC `D x' UNION A` THEN ASM_SET_TAC [],
    ASM_SET_TAC []] ) THEN DISCH_TAC THEN
  Know `sup {measure M ((D i) UNION A) | i IN univ(:num)} <= a` THEN1
  (REWRITE_TAC [sup_le'] THEN GEN_TAC THEN
   SIMP_TAC std_ss [GSPECIFICATION] THEN STRIP_TAC THEN
   Q.PAT_X_ASSUM `y = _` (ONCE_REWRITE_TAC o wrap) THEN
   Know `a = sup {measure M x | x IN Q}` >- METIS_TAC [] THEN Rewr' THEN
   Know `!i. D i UNION A IN Q` >-
   (Know `!i. D i UNION A IN measurable_sets M`
    >- (GEN_TAC THEN ONCE_REWRITE_TAC [METIS [subsets_def]
         ``measurable_sets m = subsets (m_space m, measurable_sets m)``] THEN
        MATCH_MP_TAC ALGEBRA_UNION THEN
        FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def] THEN
        METIS_TAC [subsets_def]) THEN DISCH_TAC THEN
    GEN_TAC THEN
    Know `Q = {x | x IN measurable_sets M /\ measure N x <> PosInf}`
    >- (Q.UNABBREV_TAC `Q` >> REWRITE_TAC []) >> Rewr' THEN
    ASM_SIMP_TAC std_ss [GSPECIFICATION] THEN
    CONJ_TAC THENL [METIS_TAC [], ALL_TAC] THEN
    SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC let_trans THEN
    Q.EXISTS_TAC `measure N (D i') + measure N A` THEN
    reverse CONJ_TAC
    >- (SIMP_TAC std_ss [GSYM lt_infty] THEN
        MATCH_MP_TAC (METIS [add_not_infty]
          ``x <> PosInf /\ y <> PosInf ==> x + y <> PosInf``) THEN
        ASM_SIMP_TAC std_ss [] THEN
        `D i' IN Q` by METIS_TAC [] THEN POP_ASSUM MP_TAC THEN
        Q.UNABBREV_TAC `Q` THEN SIMP_TAC std_ss [GSPECIFICATION]) THEN
    REWRITE_TAC [le_lt] THEN DISJ2_TAC THEN MATCH_MP_TAC ADDITIVE THEN
    REV_FULL_SIMP_TAC std_ss [MEASURE_SPACE_ADDITIVE] THEN
    SIMP_TAC std_ss [DISJOINT_DEF] THEN
    ASM_SIMP_TAC std_ss [EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
    GEN_TAC THEN ASM_CASES_TAC ``(x:'a) NOTIN A`` THEN
    FULL_SIMP_TAC std_ss [] THEN
    UNDISCH_TAC ``(A:'a->bool) SUBSET m_space N DIFF BIGUNION {QQ i | i IN univ(:num)}`` THEN
    Q.UNABBREV_TAC `QQ` THEN FULL_SIMP_TAC bool_ss [] THEN
    Suff `BIGUNION {D i | i IN univ(:num)} =
          BIGUNION {if i = 0 then Q' 0 else D i DIFF D (i - 1) | i IN univ(:num)}`
    >- (GEN_REWR_TAC LAND_CONV [EQ_SYM_EQ] THEN DISC_RW_KILL THEN
        SIMP_TAC std_ss [SUBSET_DEF] THEN DISCH_THEN (MP_TAC o Q.SPEC `x`) THEN
        ASM_REWRITE_TAC [] THEN ASM_SET_TAC []) THEN
    SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, GSPECIFICATION, IN_UNIV] THEN
    GEN_TAC THEN EQ_TAC THEN STRIP_TAC
    >- (FULL_SIMP_TAC std_ss [] THEN POP_ASSUM K_TAC THEN
        ASM_CASES_TAC ``x' IN (D:num->'a->bool) 0``
        >- (Q.EXISTS_TAC `D 0` THEN FULL_SIMP_TAC std_ss [] THEN
            Q.EXISTS_TAC `0` THEN
            Q.UNABBREV_TAC `D` THEN SIMP_TAC std_ss [] THEN
            SET_TAC []) THEN
        Suff `?i. i <> 0 /\ x' IN D i DIFF D (i - 1)` THENL
        [STRIP_TAC THEN Q.EXISTS_TAC `D i'' DIFF D (i'' - 1)` THEN
         ASM_REWRITE_TAC [] THEN METIS_TAC [], ALL_TAC] THEN
         Induct_on `i'` THENL [METIS_TAC [], ALL_TAC] THEN
        DISCH_TAC THEN ASM_CASES_TAC ``x' IN D (SUC i') DIFF ((D:num->'a->bool) i')`` THENL
        [Q.EXISTS_TAC `SUC i'` THEN ASM_SIMP_TAC arith_ss [], ALL_TAC] THEN
        ASM_SET_TAC []) THEN
    FULL_SIMP_TAC std_ss [] THEN POP_ASSUM K_TAC THEN
    ASM_CASES_TAC ``i' = 0:num``
    >- (Q.EXISTS_TAC `Q' 0` THEN FULL_SIMP_TAC std_ss [] THEN
        Q.UNABBREV_TAC `D` THEN BETA_TAC THEN
        Q.EXISTS_TAC `0` THEN SET_TAC []) THEN
    FULL_SIMP_TAC std_ss [] THEN Q.EXISTS_TAC `D i'` THEN CONJ_TAC THENL
    [ALL_TAC, METIS_TAC []] THEN
    ASM_SET_TAC [] ) THEN DISCH_TAC THEN
   MATCH_MP_TAC le_sup_imp' THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
   METIS_TAC [] ) THEN DISCH_TAC THEN
  POP_ASSUM MP_TAC THEN
  SIMP_TAC std_ss [GSYM extreal_lt_def] THEN
  POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) THEN
 `BIGUNION {D i | i IN univ(:num)} = O_o` by METIS_TAC [] THEN POP_ORW THEN
  POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) THEN
  Know `a = measure M O_o` >- METIS_TAC [] THEN Rewr' THEN DISCH_TAC THEN
  Know `measure M O_o <> NegInf`
  >- (MATCH_MP_TAC pos_not_neginf THEN
     `positive M` by PROVE_TAC [MEASURE_SPACE_POSITIVE] THEN
      fs [positive_def, measurable_sets_def, measure_def]) THEN DISCH_TAC THEN
 `measure M O_o <> PosInf` by PROVE_TAC [] THEN
 `measure M A <= 0`
    by PROVE_TAC [REWRITE_RULE [add_rzero]
                   (Q.SPECL [`measure M O_o`, `measure M A`, `0`] le_ladd)] THEN
  PROVE_TAC [let_antisym]
QED

(* M is finite, while N can be infinite *)
Theorem Radon_Nikodym_finite_arbitrary : (* was: Radon_Nikodym_finite_measure_infinite *)
    !M N. measure_space M /\ measure_space N /\
         (m_space M = m_space N) /\ (measurable_sets M = measurable_sets N) /\
         (measure M (m_space M) <> PosInf) /\
          measure_absolutely_continuous (measure N) M ==>
      ?f. f IN measurable (m_space M,measurable_sets M) Borel /\ (!x. 0 <= f x) /\
          !A. A IN measurable_sets M ==>
             (pos_fn_integral M (\x. f x * indicator_fn A x) = measure N A)
Proof
  rpt GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM (MP_TAC o MATCH_MP split_space_into_finite_sets_and_rest) THEN
  DISCH_THEN (X_CHOOSE_TAC ``Q0:'a->bool``) THEN POP_ASSUM MP_TAC THEN
  DISCH_THEN (X_CHOOSE_TAC ``Q:num->'a->bool``) THEN FULL_SIMP_TAC std_ss [] THEN
  Q.PAT_X_ASSUM `m_space M = m_space N` (ASSUME_TAC o (MATCH_MP EQ_SYM)) THEN
  Q.PAT_X_ASSUM `measurable_sets M = measurable_sets N`
      (ASSUME_TAC o (MATCH_MP EQ_SYM)) THEN ASM_REWRITE_TAC [] THEN
  Know `!i. Q i IN measurable_sets M` >- ASM_SET_TAC [] THEN DISCH_TAC THEN
  Q.ABBREV_TAC `NN = (\i:num. (m_space M, measurable_sets M,
    (\A. pos_fn_integral N (\x. indicator_fn (Q i) x * indicator_fn A x))))` THEN
  Q.ABBREV_TAC `MM = (\i:num. (m_space M, measurable_sets M,
    (\A. pos_fn_integral M (\x. indicator_fn (Q i) x * indicator_fn A x))))` THEN
  Know `!i. ?f. f IN measurable (m_space (MM i), measurable_sets (MM i)) Borel /\
                (!x. 0 <= f x) /\ !A. A IN measurable_sets (MM i) ==>
                (pos_fn_integral (MM i) (\x. f x * indicator_fn A x) = measure (NN i) A)` >-
  (GEN_TAC THEN MATCH_MP_TAC Radon_Nikodym_finite THEN
   Know `measure (MM i) (m_space (MM i)) <> PosInf` >-
   ( Q.UNABBREV_TAC `MM` THEN
     SIMP_TAC std_ss [measure_def, m_space_def] THEN
     ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE] THEN
     SIMP_TAC std_ss [INDICATOR_FN_MUL_INTER] THEN
    `Q i SUBSET m_space M` by METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE] THEN
     ASM_SIMP_TAC std_ss [SET_RULE ``a SUBSET b ==> (a INTER b = a)``] THEN
     REWRITE_TAC [METIS [ETA_AX] ``(\x. indicator_fn (Q i) x) = indicator_fn (Q i)``] THEN
     ASM_SIMP_TAC std_ss [pos_fn_integral_indicator] THEN
     SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC let_trans THEN
     Q.EXISTS_TAC `measure M (m_space M)` THEN ASM_REWRITE_TAC [GSYM lt_infty] THEN
     MATCH_MP_TAC INCREASING THEN ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE] THEN
     ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING] ) THEN
   DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
   Know `measure (NN i) (m_space (NN i)) <> PosInf` >-
   ( Q.UNABBREV_TAC `NN` THEN
     SIMP_TAC std_ss [measure_def, m_space_def] THEN
     ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE] THEN
     SIMP_TAC std_ss [INDICATOR_FN_MUL_INTER] THEN
     `Q i SUBSET m_space M` by METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE] THEN
     ASM_SIMP_TAC std_ss [SET_RULE ``a SUBSET b ==> (a INTER b = a)``] THEN
     REWRITE_TAC [METIS [ETA_AX] ``(\x. indicator_fn (Q i) x) = indicator_fn (Q i)``] THEN
     `pos_fn_integral N (indicator_fn (Q i)) = measure N (Q i)`
      by METIS_TAC [pos_fn_integral_indicator] THEN
     ASM_SIMP_TAC std_ss [] ) THEN
   DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
   `measurable_sets (MM i) = measurable_sets (NN i)` by METIS_TAC [measurable_sets_def] THEN
   ASM_REWRITE_TAC [] THEN
   Know `measure_absolutely_continuous (measure (NN i)) (MM i)` >-
   (FULL_SIMP_TAC std_ss [measure_absolutely_continuous_def] THEN
    qunabbrevl_tac [`MM`, `NN`] THEN
    SIMP_TAC std_ss [measure_def, measurable_sets_def] THEN
    SIMP_TAC std_ss [INDICATOR_FN_MUL_INTER] THEN
    REWRITE_TAC [METIS [ETA_AX] ``(\x. indicator_fn (Q i) x) = indicator_fn (Q i)``] THEN
    GEN_TAC THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
    FIRST_ASSUM (fn th => REWRITE_TAC [th]) THEN
    `Q i INTER s IN measurable_sets M` by
     METIS_TAC [ALGEBRA_INTER, measure_space_def, sigma_algebra_def, subsets_def] THEN
    FULL_SIMP_TAC std_ss [subsets_def, pos_fn_integral_indicator]) THEN
   DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
   Know `m_space (MM i) = m_space (NN i)`
   >- (qunabbrevl_tac [`MM`, `NN`] >> SIMP_TAC std_ss [m_space_def]) THEN
   DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
   FULL_SIMP_TAC std_ss [measure_space_def] THEN
   qunabbrevl_tac [`MM`, `NN`] THEN
   FULL_SIMP_TAC std_ss [m_space_def, measurable_sets_def, measure_def] THEN
   REWRITE_TAC [GSYM CONJ_ASSOC] THEN CONJ_TAC
   >- (SIMP_TAC std_ss [positive_def, measure_def, measurable_sets_def] THEN
      `{} IN measurable_sets N` by METIS_TAC [measure_space_def, sigma_algebra_alt_pow] THEN
       ASM_SIMP_TAC std_ss [] THEN CONJ_TAC
       >- (SIMP_TAC std_ss [indicator_fn_def, NOT_IN_EMPTY, mul_rzero] THEN
           METIS_TAC [pos_fn_integral_zero, measure_space_def]) THEN
       RW_TAC std_ss [] THEN MATCH_MP_TAC pos_fn_integral_pos THEN
       REWRITE_TAC [INDICATOR_FN_MUL_INTER] THEN ASM_SIMP_TAC std_ss [measure_space_def] THEN
       SIMP_TAC std_ss [indicator_fn_def] THEN GEN_TAC THEN COND_CASES_TAC THEN
       SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]) THEN
   CONJ_TAC (* countably_additive *)
   >- (SIMP_TAC std_ss [countably_additive_alt_eq, INDICATOR_FN_MUL_INTER] THEN
       REPEAT STRIP_TAC THEN SIMP_TAC std_ss [o_DEF] THEN
      `!x. A x IN measurable_sets M` by ASM_SET_TAC [] THEN
       ASM_SIMP_TAC std_ss [INTER_BIGUNION, GSPECIFICATION, IN_UNIV] THEN
       REWRITE_TAC [SET_RULE ``{Q i INTER x | ?i'. x = A i'} = {Q i INTER A i' | i' IN UNIV}``] THEN
       SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
       Suff `!x. indicator_fn (BIGUNION (IMAGE (\i'. Q i INTER A i') univ(:num))) x =
          suminf (\j. indicator_fn ((\i'. Q i INTER A i') j) x)` THENL
       [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
        GEN_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC indicator_fn_suminf THEN
        FULL_SIMP_TAC std_ss [disjoint_family, disjoint_family_on, DISJOINT_DEF] THEN
        ASM_SET_TAC []] THEN ONCE_REWRITE_TAC [METIS [ETA_AX]
          ``(\x'. indicator_fn (Q i INTER A x) x') = (\x. indicator_fn (Q i INTER A x)) x``] THEN
       ONCE_REWRITE_TAC [METIS [] ``suminf (\j. indicator_fn (Q i INTER A j) x) =
                         suminf (\j. (\k. indicator_fn (Q i INTER A k)) j x)``] THEN
       MATCH_MP_TAC pos_fn_integral_suminf THEN ASM_SIMP_TAC std_ss [measure_space_def] THEN
       CONJ_TAC THENL
       [SIMP_TAC std_ss [indicator_fn_def] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
        SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def], ALL_TAC] THEN
       GEN_TAC THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
       Q.EXISTS_TAC `Q i INTER A i'` THEN ASM_SIMP_TAC std_ss [] THEN
       MATCH_MP_TAC ALGEBRA_INTER THEN
       FULL_SIMP_TAC std_ss [sigma_algebra_def, subsets_def] THEN
       METIS_TAC []) THEN
   CONJ_TAC (* positive *)
   >- (SIMP_TAC std_ss [positive_def, measure_def, measurable_sets_def] THEN
      `{} IN measurable_sets M` by METIS_TAC [measure_space_def, sigma_algebra_alt_pow] THEN
       ASM_SIMP_TAC std_ss [] THEN CONJ_TAC THENL
       [SIMP_TAC std_ss [indicator_fn_def, NOT_IN_EMPTY, mul_rzero] THEN
        METIS_TAC [pos_fn_integral_zero, measure_space_def], ALL_TAC] THEN
       RW_TAC std_ss [] THEN MATCH_MP_TAC pos_fn_integral_pos THEN
       REWRITE_TAC [INDICATOR_FN_MUL_INTER] THEN ASM_SIMP_TAC std_ss [measure_space_def] THEN
       SIMP_TAC std_ss [indicator_fn_def] THEN GEN_TAC THEN COND_CASES_TAC THEN
       SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]) THEN
   (* countably_additive *)
   SIMP_TAC std_ss [countably_additive_alt_eq, INDICATOR_FN_MUL_INTER] THEN
   REPEAT STRIP_TAC THEN SIMP_TAC std_ss [o_DEF] THEN
   `!x. A x IN measurable_sets M` by ASM_SET_TAC [] THEN
   ASM_SIMP_TAC std_ss [INTER_BIGUNION, GSPECIFICATION, IN_UNIV] THEN
   REWRITE_TAC [SET_RULE ``{Q i INTER x | ?i'. x = A i'} = {Q i INTER A i' | i' IN UNIV}``] THEN
   SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
   Suff `!x. indicator_fn (BIGUNION (IMAGE (\i'. Q i INTER A i') univ(:num))) x =
           suminf (\j. indicator_fn ((\i'. Q i INTER A i') j) x)` THENL
   [DISCH_TAC THEN ASM_SIMP_TAC std_ss [],
    GEN_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC indicator_fn_suminf THEN
    FULL_SIMP_TAC std_ss [disjoint_family, disjoint_family_on, DISJOINT_DEF] THEN
    ASM_SET_TAC []] THEN ONCE_REWRITE_TAC [METIS [ETA_AX]
     ``(\x'. indicator_fn (Q i INTER A x) x') = (\x. indicator_fn (Q i INTER A x)) x``] THEN
   ONCE_REWRITE_TAC [METIS [] ``suminf (\j. indicator_fn (Q i INTER A j) x) =
                           suminf (\j. (\k. indicator_fn (Q i INTER A k)) j x)``] THEN
   MATCH_MP_TAC pos_fn_integral_suminf THEN ASM_SIMP_TAC std_ss [measure_space_def] THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [indicator_fn_def] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def], ALL_TAC] THEN
   GEN_TAC THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN
   Q.EXISTS_TAC `Q i INTER A i'` THEN ASM_SIMP_TAC std_ss [] THEN
   MATCH_MP_TAC ALGEBRA_INTER THEN
   FULL_SIMP_TAC std_ss [sigma_algebra_def, subsets_def] THEN
   METIS_TAC [] ) THEN DISCH_TAC THEN
  Suff `?f. (!i. f i IN measurable (m_space (MM i), measurable_sets (MM i)) Borel) /\
            (!i x. 0 <= f i x) /\ !i A. A IN measurable_sets (MM i) ==>
            (pos_fn_integral (MM i) (\x. (f i) x * indicator_fn A x) = measure (NN i) A)` THENL
  [STRIP_TAC, METIS_TAC []] THEN
  Q.ABBREV_TAC
     `ff = (\x. suminf (\i. f i x * indicator_fn (Q i) x) + PosInf * indicator_fn (Q0) x)` THEN
  Know `ff IN measurable (m_space M,measurable_sets M) Borel` >-
  (Know `ff = (\x. if x IN Q0 then (\x. PosInf) x
                   else (\x. suminf (\i. f i x * indicator_fn (Q i) x)) x)` >-
   (Q.UNABBREV_TAC `ff` THEN SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN
    COND_CASES_TAC THENL
    [POP_ASSUM (fn th => SIMP_TAC std_ss [indicator_fn_def, th, mul_rone]) THEN
     Suff `!x. 0 <= x ==> (x + PosInf = PosInf)`
     >- (DISCH_THEN (MATCH_MP_TAC) THEN
         Know `!n. 0 <= (\i. f i x * if x IN Q i then 1 else 0) n`
         >- (RW_TAC std_ss [mul_rone, mul_rzero, le_refl]) THEN
         DISCH_THEN (REWRITE_TAC o wrap o (MATCH_MP ext_suminf_def)) THEN
         SIMP_TAC std_ss [le_sup'] THEN
         GEN_TAC THEN DISCH_THEN (MATCH_MP_TAC) THEN
         SIMP_TAC std_ss [GSPECIFICATION, IN_IMAGE, IN_UNIV] THEN Q.EXISTS_TAC `0` THEN
         SIMP_TAC std_ss [count_def, GSPEC_F, EXTREAL_SUM_IMAGE_EMPTY]) THEN
     GEN_TAC THEN DISCH_TAC THEN
     `x <> NegInf` by METIS_TAC [lt_infty, lte_trans, num_not_infty] THEN
     ASM_CASES_TAC ``x = PosInf`` THENL [METIS_TAC [extreal_add_def], ALL_TAC] THEN
     METIS_TAC [extreal_cases, extreal_add_def], ALL_TAC] THEN
    POP_ASSUM (fn th => SIMP_TAC std_ss [indicator_fn_def, th, mul_rzero]) THEN
    SIMP_TAC std_ss [add_rzero]) THEN DISCH_TAC THEN
   ONCE_REWRITE_TAC [METIS [SPACE, m_space_def, measurable_sets_def]
    ``Borel = (m_space (space Borel, subsets Borel, (\x. 0)),
       measurable_sets (space Borel, subsets Borel, (\x. 0)))``] THEN
   FIRST_X_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [SPECIFICATION]) THEN
   POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN
   ONCE_REWRITE_TAC [METIS [] ``PosInf = (\x. PosInf) x``] THEN
   MATCH_MP_TAC MEASURABLE_IF >> rpt STRIP_TAC >| (* 5 subgoals *)
   [(* goal 1 (of 5) *)
    SIMP_TAC std_ss [SPACE, m_space_def, measurable_sets_def] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN Q.EXISTS_TAC `PosInf` THEN
    METIS_TAC [measure_space_def],
    (* goal 2 (of 5) *)
    ALL_TAC,
    (* goal 3 (of 5) *)
    ONCE_REWRITE_TAC [prove (``{x | x IN m_space M /\ Q0 x} = {x | x IN m_space M /\ x IN Q0}``,
     SIMP_TAC std_ss [SPECIFICATION])] THEN SIMP_TAC std_ss [GSYM INTER_DEF] THEN
    ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets M = subsets (m_space M, measurable_sets M)``] THEN
    MATCH_MP_TAC ALGEBRA_INTER THEN SIMP_TAC std_ss [subsets_def] THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def, sigma_algebra_def], ALL_TAC] THEN
    METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE],
    (* goal 4 (of 5) *)
    ASM_REWRITE_TAC [],
    (* goal 5 (of 5) *)
    rw [SIGMA_ALGEBRA_BOREL] ] THEN
   Know `!x. suminf (\i. f i x * indicator_fn (Q i) x) =
             sup (IMAGE (\n. SIGMA (\i. f i x * indicator_fn (Q i) x)
                             (count n)) univ(:num))`
   >- (GEN_TAC >> MATCH_MP_TAC ext_suminf_def \\
       GEN_TAC >> BETA_TAC \\
       MATCH_MP_TAC le_mul >> art [INDICATOR_FN_POS]) >> Rewr' THEN
   SIMP_TAC std_ss [SPACE, m_space_def, measurable_sets_def] THEN
   Suff `!x. (\n. SIGMA (\i. f i x * indicator_fn (Q i) x) (count n)) =
                       (\n. (\n x. SIGMA (\i. f i x * indicator_fn (Q i) x) (count n)) n x)` THENL
   [DISC_RW_KILL, METIS_TAC []] THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP THEN
   Q.EXISTS_TAC `(\n x. SIGMA (\i. f i x * indicator_fn (Q i) x) (count n))` THEN
   SIMP_TAC std_ss [space_def] THEN
   CONJ_TAC >- METIS_TAC [measure_space_def] THEN
   reverse CONJ_TAC
   >- (rpt STRIP_TAC THEN MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET THEN
       SIMP_TAC std_ss [FINITE_COUNT, count_def] THEN
       SIMP_TAC arith_ss [SUBSET_DEF, GSPECIFICATION] THEN
       rpt STRIP_TAC THEN MATCH_MP_TAC le_mul THEN art [INDICATOR_FN_POS]) THEN
   GEN_TAC THEN
   MP_TAC (ISPECL [``(m_space (M:('a->bool)#(('a->bool)->bool)#(('a->bool)->extreal)),
                      measurable_sets M)``,
                   ``(\i x. (f:num->'a->extreal) i x * indicator_fn (Q i) x)``,
                   ``(\x. SIGMA (\i. (f:num->'a->extreal) i x * indicator_fn (Q i) x) (count n))``,
                   ``count n``] IN_MEASURABLE_BOREL_SUM) THEN
   ASM_REWRITE_TAC [] THEN DISCH_THEN (MATCH_MP_TAC) THEN
   SIMP_TAC std_ss [FINITE_COUNT, space_def] THEN
   CONJ_TAC >- METIS_TAC [measure_space_def] THEN
   reverse CONJ_TAC
   >- (rpt GEN_TAC >> STRIP_TAC THEN MATCH_MP_TAC pos_not_neginf THEN
       MATCH_MP_TAC le_mul THEN art [INDICATOR_FN_POS]) THEN
   GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR THEN
   METIS_TAC [subsets_def, measure_space_def, m_space_def, measurable_sets_def] ) THEN
  DISCH_TAC THEN
  Know `!x. 0 <= ff x` THEN1
  (Q.UNABBREV_TAC `ff` >> BETA_TAC THEN GEN_TAC THEN
   ASM_CASES_TAC ``(x:'a) IN Q0`` THENL
   [POP_ASSUM (fn th => SIMP_TAC std_ss [indicator_fn_def, th, mul_rone]) THEN
    Suff `suminf (\i. f i x * if x IN Q i then 1 else 0) + PosInf = PosInf` THENL
    [METIS_TAC [le_infty], ALL_TAC] THEN
    Suff `!x. 0 <= x ==> (x + PosInf = PosInf)` THENL
    [DISCH_THEN (MATCH_MP_TAC) THEN
     Know `!n. 0 <= (\i. f i x * if x IN Q i then 1 else 0) n`
     >- (RW_TAC std_ss [mul_rone, mul_rzero, le_refl]) THEN
     DISCH_THEN (REWRITE_TAC o wrap o (MATCH_MP ext_suminf_def)) THEN
     SIMP_TAC std_ss [le_sup'] THEN
     GEN_TAC THEN DISCH_THEN (MATCH_MP_TAC) THEN
     SIMP_TAC std_ss [GSPECIFICATION, IN_IMAGE, IN_UNIV] THEN Q.EXISTS_TAC `0` THEN
     SIMP_TAC std_ss [count_def, GSPEC_F, EXTREAL_SUM_IMAGE_EMPTY],
     ALL_TAC] THEN
    GEN_TAC THEN DISCH_TAC THEN
    `x <> NegInf` by METIS_TAC [lt_infty, lte_trans, num_not_infty] THEN
    ASM_CASES_TAC ``x = PosInf`` THENL [METIS_TAC [extreal_add_def], ALL_TAC] THEN
    METIS_TAC [extreal_cases, extreal_add_def], ALL_TAC] THEN
   POP_ASSUM (fn th => SIMP_TAC std_ss [indicator_fn_def, th, mul_rzero]) THEN
   SIMP_TAC std_ss [add_rzero] THEN
   MATCH_MP_TAC ext_suminf_pos THEN
   RW_TAC std_ss [mul_rone, mul_rzero, le_refl]) THEN DISCH_TAC THEN
  Q.EXISTS_TAC `ff` THEN ASM_SIMP_TAC std_ss [] THEN
  GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC ``m_space M = {}`` THENL
  [`m_space M = m_space N` by METIS_TAC [sets_eq_imp_space_eq] THEN
   `A SUBSET m_space M` by METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE] THEN
   `positive N` by METIS_TAC [MEASURE_SPACE_POSITIVE] THEN
   `A = {}` by ASM_SET_TAC [] THEN FULL_SIMP_TAC std_ss [positive_def] THEN
   SIMP_TAC std_ss [indicator_fn_def, NOT_IN_EMPTY, mul_rzero] THEN
   METIS_TAC [pos_fn_integral_zero],
   ALL_TAC] THEN
  Suff `(!i. (\x. f i x * indicator_fn (Q i INTER A) x) IN
                     measurable (m_space M, measurable_sets M) Borel) /\
                  (!i. ?x. x IN m_space M /\ 0 <= f i x * indicator_fn (Q i INTER A) x)` THENL
  [STRIP_TAC,
   CONJ_TAC THENL
   [ALL_TAC,
    GEN_TAC THEN FULL_SIMP_TAC std_ss [GSYM MEMBER_NOT_EMPTY] THEN
    Q.EXISTS_TAC `x` THEN ASM_SIMP_TAC std_ss [] THEN
    MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [indicator_fn_def] THEN
    COND_CASES_TAC THEN SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]] THEN
   GEN_TAC THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   CONJ_TAC THENL [METIS_TAC [m_space_def, measurable_sets_def], ALL_TAC] THEN
   MATCH_MP_TAC ALGEBRA_INTER THEN CONJ_TAC THENL
   [ALL_TAC, METIS_TAC [subsets_def]] THEN
   METIS_TAC [measure_space_def, sigma_algebra_def]] THEN
  Know `pos_fn_integral M (\x. ff x * indicator_fn A x) =
        pos_fn_integral M (\x. suminf (\i. f i x * indicator_fn (Q i INTER A) x) +
        PosInf * indicator_fn (Q0 INTER A) x)` THEN1
  (Q.UNABBREV_TAC `ff` >> BETA_TAC THEN
   Know `!x. 0 <= suminf (\i. f i x * indicator_fn (Q i) x)`
   >- (GEN_TAC >> MATCH_MP_TAC ext_suminf_pos THEN
       RW_TAC std_ss [] THEN
       MATCH_MP_TAC le_mul >> art [INDICATOR_FN_POS]) THEN DISCH_TAC THEN
   Know `!x. 0 <= PosInf * indicator_fn Q0 x`
   >- (GEN_TAC >> MATCH_MP_TAC le_mul THEN
       SIMP_TAC std_ss [le_infty, INDICATOR_FN_POS]) THEN DISCH_TAC THEN

   `!x. (suminf (\i. f i x * indicator_fn (Q i) x) +
        PosInf * indicator_fn Q0 x) * indicator_fn A x =
        (suminf (\i. f i x * indicator_fn (Q i) x) * indicator_fn A x) +
        ((PosInf * indicator_fn Q0 x) * indicator_fn A x)` by METIS_TAC [add_rdistrib] THEN
   POP_ASSUM (fn th => REWRITE_TAC [th]) THEN REWRITE_TAC [GSYM mul_assoc] THEN
   ONCE_REWRITE_TAC [METIS [INDICATOR_FN_MUL_INTER]
    ``indicator_fn Q0 x * indicator_fn A x = indicator_fn (Q0 INTER A) x``] THEN
   Suff `!x. suminf (\i. f i x * indicator_fn (Q i) x) * indicator_fn A x =
                       suminf (\i. f i x * indicator_fn (Q i INTER A) x)` THENL
   [DISCH_TAC THEN ASM_SIMP_TAC std_ss [], ALL_TAC] THEN
   GEN_TAC THEN
   ONCE_REWRITE_TAC [METIS [INDICATOR_FN_MUL_INTER]
    ``indicator_fn (Q i INTER A) x = indicator_fn (Q i) x * indicator_fn A x``] THEN
   ASM_CASES_TAC ``(x:'a) IN A`` THEN
   ASM_SIMP_TAC std_ss [indicator_fn_def, mul_rone, mul_rzero] THEN
   SIMP_TAC std_ss [ext_suminf_0] ) THEN DISCH_TAC THEN
 (* stage work *)
  Know `pos_fn_integral M (\x. suminf (\i. f i x * indicator_fn (Q i INTER A) x) +
          PosInf * indicator_fn (Q0 INTER A) x) =
        pos_fn_integral M (\x. suminf (\i. f i x * indicator_fn (Q i INTER A) x)) +
          PosInf * measure M (Q0 INTER A)` >-
  ( Suff `pos_fn_integral M (\x. (\x. suminf (\i. f i x * indicator_fn (Q i INTER A) x)) x +
                            (\x. PosInf * indicator_fn (Q0 INTER A) x) x) =
          pos_fn_integral M (\x. suminf (\i. f i x * indicator_fn (Q i INTER A) x)) +
          pos_fn_integral M (\x. PosInf * indicator_fn (Q0 INTER A) x)`
    >- (SIMP_TAC std_ss [] THEN DISCH_TAC THEN
        MATCH_MP_TAC (METIS [] ``(b = c) ==> (a + b = a + c)``) THEN
        MATCH_MP_TAC pos_fn_integral_cmul_infty THEN
        CONJ_TAC >- METIS_TAC [] THEN
        ONCE_REWRITE_TAC [METIS [subsets_def]
          ``measurable_sets M = subsets (m_space M, measurable_sets M)``] THEN
        METIS_TAC [measure_space_def, sigma_algebra_def, ALGEBRA_INTER, subsets_def]) \\
    MATCH_MP_TAC pos_fn_integral_add THEN SIMP_TAC std_ss [] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
    Know `!x. 0 <= suminf (\i. f i x * indicator_fn (Q i INTER A) x)`
    >- (GEN_TAC THEN MATCH_MP_TAC ext_suminf_pos THEN
        GEN_TAC THEN BETA_TAC THEN
        MATCH_MP_TAC le_mul >> art [INDICATOR_FN_POS]) THEN DISCH_TAC THEN
    Know `!x. 0 <= PosInf * indicator_fn (Q0 INTER A) x`
    >- (GEN_TAC THEN MATCH_MP_TAC le_mul THEN
        SIMP_TAC std_ss [le_infty, INDICATOR_FN_POS]) THEN DISCH_TAC THEN
    CONJ_TAC THENL [METIS_TAC [], ALL_TAC] THEN
    CONJ_TAC >- (simp []) \\
    CONJ_TAC THENL
    [Know `!x. suminf (\i. f i x * indicator_fn (Q i INTER A) x) =
               sup (IMAGE (\n. SIGMA (\i. f i x * indicator_fn (Q i INTER A) x)
                          (count n)) univ(:num))`
     >- (GEN_TAC >> MATCH_MP_TAC ext_suminf_def \\
         GEN_TAC >> BETA_TAC >> MATCH_MP_TAC le_mul >> art [INDICATOR_FN_POS]) THEN
     Rewr' >> SIMP_TAC std_ss [] THEN
     Suff `!x. (\n. SIGMA (\i. f i x * indicator_fn (Q i INTER A) x) (count n)) =
               (\n. (\n x. SIGMA (\i. f i x * indicator_fn (Q i INTER A) x) (count n)) n x)` THENL
     [DISC_RW_KILL, METIS_TAC []] THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP THEN
     Q.EXISTS_TAC `(\n x. SIGMA (\i. f i x * indicator_fn (Q i INTER A) x) (count n))` THEN
     SIMP_TAC std_ss [] THEN
     CONJ_TAC >- METIS_TAC [measure_space_def] THEN
     reverse CONJ_TAC
     >- (rpt STRIP_TAC THEN MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET THEN
         SIMP_TAC std_ss [FINITE_COUNT] THEN
         CONJ_TAC >- (MATCH_MP_TAC COUNT_MONO >> RW_TAC arith_ss []) THEN
         SIMP_TAC arith_ss [IN_COUNT, SUBSET_DEF, GSPECIFICATION] THEN
         GEN_TAC THEN DISCH_TAC THEN
         MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [INDICATOR_FN_POS]) THEN
     GEN_TAC THEN
     MP_TAC (ISPECL [``(m_space (M:('a->bool)#(('a->bool)->bool)#(('a->bool)->extreal)),
                        measurable_sets M)``,
                     ``(\i x.  (f:num->'a->extreal) i x * indicator_fn (Q i INTER A) x)``,
                     ``(\x. SIGMA (\i. (f:num->'a->extreal) i x * indicator_fn (Q i INTER A) x) (count n))``,
                     ``count n``] IN_MEASURABLE_BOREL_SUM) THEN
     ASM_REWRITE_TAC [] THEN DISCH_THEN (MATCH_MP_TAC) THEN
     SIMP_TAC std_ss [FINITE_COUNT] THEN CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
     reverse CONJ_TAC
     >- (rpt GEN_TAC THEN STRIP_TAC THEN
         MATCH_MP_TAC pos_not_neginf THEN
         MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [INDICATOR_FN_POS]) THEN
     GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR THEN
     METIS_TAC [subsets_def, measure_space_def, m_space_def, measurable_sets_def,
                ALGEBRA_INTER, sigma_algebra_def], ALL_TAC] THEN
    ONCE_REWRITE_TAC [METIS [] ``(\x. PosInf * indicator_fn (Q0 INTER A) x) =
                                 (\x. (\x. PosInf) x * indicator_fn (Q0 INTER A) x)``] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN Q.EXISTS_TAC `PosInf` THEN
     METIS_TAC [measure_space_def], ALL_TAC] THEN
    METIS_TAC [ALGEBRA_INTER, measure_space_def, sigma_algebra_def, subsets_def] ) THEN
  DISCH_TAC THEN
  Know `!A i. A IN measurable_sets M ==>
             (pos_fn_integral M (\x. f i x * indicator_fn (Q i INTER A) x) =
              measure (m_space (MM i), measurable_sets (MM i),
               (\A. pos_fn_integral (MM i) (\x. f i x * indicator_fn A x))) A)` >-
  (rpt GEN_TAC THEN SIMP_TAC std_ss [measure_def] THEN
   DISCH_TAC THEN
   Know `pos_fn_integral (MM i) (\x. f i x * indicator_fn A' x) =
         pos_fn_integral M (\x. indicator_fn (Q i) x * (\x. f i x * indicator_fn A' x) x)` >-
   (Q.UNABBREV_TAC `MM` THEN BETA_TAC THEN
    ONCE_REWRITE_TAC [METIS [] ``(\x. indicator_fn (Q i) x * (f i x * indicator_fn A' x)) =
                             (\x. indicator_fn (Q i) x * (\x. f i x * indicator_fn A' x) x)``] THEN
    Suff `pos_fn_integral
           (m_space M,measurable_sets M,
            (\A. pos_fn_integral M (\x. max 0 (indicator_fn (Q i) x * indicator_fn A x))))
           (\x. max 0 ((\x. f i x * indicator_fn A' x) x)) =
          pos_fn_integral M
           (\x. max 0 (indicator_fn (Q i) x * (\x. f i x * indicator_fn A' x) x))` THENL
    [ASM_SIMP_TAC std_ss [extreal_max_def, indicator_fn_pos_le, le_mul], ALL_TAC] THEN
    MATCH_MP_TAC pos_fn_integral_density' THEN ASM_SIMP_TAC std_ss [] THEN
    CONJ_TAC
    >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR THEN Q.EXISTS_TAC `Q i` THEN
        ASM_SIMP_TAC std_ss [] THEN METIS_TAC [measure_space_def, subsets_def]) THEN
    CONJ_TAC
    >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR THEN
        METIS_TAC [measure_space_def, subsets_def, m_space_def, measurable_sets_def]) THEN
    CONJ_TAC (* AE *)
    >- (SIMP_TAC std_ss [AE_ALT, GSPECIFICATION, null_set_def] THEN
        SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN Q.EXISTS_TAC `{}` THEN
        FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_alt_pow] THEN
        FULL_SIMP_TAC std_ss [positive_def, NOT_IN_EMPTY] THEN
        GEN_TAC THEN DISJ2_TAC THEN
        SIMP_TAC std_ss [indicator_fn_def] THEN COND_CASES_TAC THEN
        SIMP_TAC real_ss [le_refl, extreal_of_num_def, extreal_le_def]) THEN
    GEN_TAC THEN MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [INDICATOR_FN_POS]) THEN
   DISC_RW_KILL THEN SIMP_TAC std_ss [mul_assoc] THEN
   ONCE_REWRITE_TAC [mul_comm] THEN SIMP_TAC std_ss [mul_assoc] THEN
   ONCE_REWRITE_TAC [METIS [INDICATOR_FN_MUL_INTER]
    ``indicator_fn A' x * indicator_fn (Q i) x = indicator_fn (A' INTER Q i) x``] THEN
   METIS_TAC [INTER_COMM]) THEN
  DISCH_TAC THEN
  Know `!i. measure (m_space (MM i),measurable_sets (MM i),
                     (\A. pos_fn_integral (MM i) (\x. f i x * indicator_fn A x))) A =
            measure N (Q i INTER A)`
  >- (GEN_TAC THEN
      Know `measure N (Q i INTER A) =
            measure (m_space N,measurable_sets N,
                     (\s. pos_fn_integral N (\x. indicator_fn (Q i) x * indicator_fn s x))) A`
      >- (MATCH_MP_TAC (GSYM measure_restricted) THEN METIS_TAC []) THEN
      DISC_RW_KILL THEN SIMP_TAC std_ss [measure_def] THEN
     `measurable_sets (MM i) = measurable_sets (N)` by METIS_TAC [measurable_sets_def] THEN
      Know `pos_fn_integral (MM i) (\x. f i x * indicator_fn A x) = measure (NN i) A`
      >- (FIRST_X_ASSUM MATCH_MP_TAC >> PROVE_TAC []) >> Rewr' THEN
      Q.UNABBREV_TAC `NN` THEN SIMP_TAC std_ss [measure_def] ) THEN DISCH_TAC THEN
 `!i. measure N (Q i INTER A) =
      pos_fn_integral M (\x. f i x * indicator_fn (Q i INTER A) x)` by METIS_TAC [] THEN
  Know `pos_fn_integral M (\x. suminf (\i. f i x * indicator_fn (Q i INTER A) x)) +
        PosInf * measure M (Q0 INTER A) =
        suminf (\i. measure N (Q i INTER A)) + PosInf * measure M (Q0 INTER A)`
  >- (MATCH_MP_TAC (METIS [] ``(b = c) ==> (b + a = c + a)``) THEN
      Know `pos_fn_integral M (\x. suminf (\i. (\i x. f i x * indicator_fn (Q i INTER A) x) i x)) =
            suminf (\i. pos_fn_integral M ((\i x. f i x * indicator_fn (Q i INTER A) x) i))`
      >- (MATCH_MP_TAC pos_fn_integral_suminf >> ASM_SIMP_TAC std_ss [] \\
          rpt STRIP_TAC >> MATCH_MP_TAC le_mul \\
          ASM_SIMP_TAC std_ss [INDICATOR_FN_POS]) \\
      SIMP_TAC std_ss [] THEN DISC_RW_KILL THEN REWRITE_TAC [] ) >> DISCH_TAC THEN
  Suff `suminf (\i. measure N (Q i INTER A)) =
       measure N (BIGUNION {Q i | i IN UNIV} INTER A)` THENL
  [DISCH_TAC,
   SIMP_TAC std_ss [INTER_BIGUNION, GSPECIFICATION, IN_UNIV] THEN
   ONCE_REWRITE_TAC [SET_RULE ``BIGUNION {x INTER A | ?i. x = Q i} =
                                BIGUNION {Q i INTER A | i IN UNIV}``] THEN
   ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
   `countably_additive N` by METIS_TAC [measure_space_def] THEN
   POP_ASSUM MP_TAC THEN SIMP_TAC std_ss [countably_additive_def] THEN
   SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
   DISCH_THEN (MP_TAC o Q.SPEC `(\i. Q i INTER A)`) THEN
   SIMP_TAC std_ss [o_DEF] THEN DISCH_THEN (MATCH_MP_TAC) THEN
   CONJ_TAC THENL
   [EVAL_TAC THEN ASM_SIMP_TAC std_ss [IN_DEF,IN_FUNSET] THEN SRW_TAC[][] THEN
     ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
    METIS_TAC [ALGEBRA_INTER, subsets_def, measure_space_def, sigma_algebra_def],
    ALL_TAC] THEN
   CONJ_TAC THENL
   [ASM_SET_TAC [DISJOINT_DEF, disjoint_family, disjoint_family_on], ALL_TAC] THEN
   ONCE_REWRITE_TAC [METIS [subsets_def] ``measurbale_sets M =
                       subsets (m_space M, measurbale_sets M)``] THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC image_countable THEN
    SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM], ALL_TAC] THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE] THEN GEN_TAC THEN
   METIS_TAC [ALGEBRA_INTER, measure_space_def, sigma_algebra_def, subsets_def]] THEN
  Know `PosInf * measure M (Q0 INTER A) = measure N (Q0 INTER A)` >-
  (UNDISCH_TAC ``!A.
        A IN measurable_sets M /\ A SUBSET Q0 ==>
        (measure M A = 0) /\ (measure N A = 0) \/
        0 < measure M A /\ (measure N A = PosInf)`` THEN
   DISCH_THEN (MP_TAC o Q.SPEC `Q0 INTER A`) THEN
   `Q0 INTER A SUBSET Q0` by SET_TAC [] THEN
   `Q0 INTER A IN measurable_sets M` by
    METIS_TAC [ALGEBRA_INTER, subsets_def, measure_space_def, sigma_algebra_def] THEN
   POP_ASSUM (fn th => REWRITE_TAC [th]) THEN POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
   STRIP_TAC THEN ASM_SIMP_TAC std_ss [mul_rzero] THEN
   Suff `(m_space M DIFF BIGUNION {Q i | i IN univ(:num)}) INTER A
     IN measurable_sets M` THENL
   [DISCH_TAC,
    ONCE_REWRITE_TAC [METIS [subsets_def]
     ``measurable_sets M = subsets (m_space M, measurable_sets M)``] THEN
    MATCH_MP_TAC ALGEBRA_INTER THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def, sigma_algebra_def], ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC, ASM_SIMP_TAC std_ss [subsets_def]] THEN
    MATCH_MP_TAC ALGEBRA_DIFF THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def, sigma_algebra_def], ALL_TAC] THEN
    CONJ_TAC THENL [METIS_TAC [subsets_def, MEASURE_SPACE_MSPACE_MEASURABLE], ALL_TAC] THEN
    MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION THEN
    CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
    CONJ_TAC THENL
    [SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
     MATCH_MP_TAC image_countable THEN
     SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM], ALL_TAC] THEN
    ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_UNIV] THEN GEN_TAC THEN
    METIS_TAC [subsets_def]] THEN
   `!A. A IN measurable_sets M ==> 0 <= measure M A`
     by METIS_TAC [measure_space_def, positive_def] THEN
   POP_ASSUM (MP_TAC o Q.SPEC `(m_space M DIFF BIGUNION {Q i | i IN univ(:num)}) INTER A`) THEN
   ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
   Suff `0 < measure M ((m_space M DIFF BIGUNION {Q i | i IN univ(:num)}) INTER A)` THENL
   [DISCH_TAC,
    MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `measure M (Q0 INTER A)` THEN
    ASM_SIMP_TAC std_ss [le_refl]] THEN
   `measure M ((m_space M DIFF BIGUNION {Q i | i IN univ(:num)}) INTER A) <> NegInf` by
     METIS_TAC [lte_trans, lt_infty, num_not_infty] THEN
   ASM_CASES_TAC ``measure M ((m_space M DIFF BIGUNION {Q i | i IN univ(:num)}) INTER A) = PosInf`` THENL
   [ASM_SIMP_TAC std_ss [extreal_mul_def], ALL_TAC] THEN
   `?r. measure M ((m_space M DIFF BIGUNION {Q i | i IN univ(:num)}) INTER A) = Normal r` by
     METIS_TAC [extreal_cases] THEN FULL_SIMP_TAC std_ss [] THEN
   SIMP_TAC std_ss [extreal_mul_def] THEN
   `0 < r` by METIS_TAC [extreal_lt_eq, extreal_of_num_def] THEN
   METIS_TAC [REAL_LT_IMP_NE] ) THEN DISCH_TAC THEN
  Suff `Q0 INTER A IN measurable_sets M /\
                  (BIGUNION {Q i | i IN UNIV} INTER A) IN measurable_sets M` THENL
  [DISCH_TAC,
   CONJ_TAC THENL
   [METIS_TAC [ALGEBRA_INTER, subsets_def, measure_space_def, sigma_algebra_def],
    ALL_TAC] THEN
   ONCE_REWRITE_TAC [METIS [subsets_def] ``measurbale_sets M =
                       subsets (m_space M, measurbale_sets M)``] THEN
   MATCH_MP_TAC ALGEBRA_INTER THEN CONJ_TAC THENL
   [METIS_TAC [measure_space_def, sigma_algebra_def], ALL_TAC] THEN
   CONJ_TAC THENL [ALL_TAC, METIS_TAC [subsets_def]] THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION THEN
   CONJ_TAC THENL [METIS_TAC [measure_space_def], ALL_TAC] THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
    MATCH_MP_TAC image_countable THEN
    SIMP_TAC std_ss [pred_setTheory.COUNTABLE_NUM], ALL_TAC] THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_UNIV] THEN GEN_TAC THEN
   METIS_TAC [subsets_def]] THEN
  Suff `((BIGUNION {Q i | i IN UNIV} INTER A) UNION (Q0 INTER A) = A) /\
                  ((BIGUNION {Q i | i IN UNIV} INTER A) INTER (Q0 INTER A) = {})` THENL
  [DISCH_TAC,
   CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC [disjoint_family, disjoint_family_on]] THEN
   UNDISCH_TAC ``Q0 = m_space M DIFF BIGUNION {Q i | i IN univ(:num)}`` THEN
   UNDISCH_TAC ``disjoint_family (Q:num->'a->bool)`` THEN
   SIMP_TAC std_ss [disjoint_family, disjoint_family_on, IN_UNIV] THEN
   FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_alt_pow, POW_DEF] THEN
   ASM_SET_TAC []] THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC ADDITIVE THEN
  CONJ_TAC THENL [METIS_TAC [MEASURE_SPACE_ADDITIVE], ALL_TAC] THEN
  CONJ_TAC THENL [METIS_TAC [], ALL_TAC] THEN
  CONJ_TAC THENL [METIS_TAC [], ALL_TAC] THEN ASM_SET_TAC [DISJOINT_DEF]
QED

Theorem finite_integrable_function_exists : (* was: Ex_finite_integrable_function *)
    !m. measure_space m /\ sigma_finite m ==>
        ?h. h IN measurable (m_space m, measurable_sets m) Borel /\
           (pos_fn_integral m h <> PosInf) /\
           (!x. x IN m_space m ==> 0 < h x /\ h x < PosInf) /\
           (!x. 0 <= h x)
Proof
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP sigma_finite_disjoint) THEN
  FULL_SIMP_TAC std_ss [] THEN
  Q.ABBREV_TAC `B = (\i. 2 pow (SUC i) * measure m (A i))` THEN
  Q.ABBREV_TAC `inv' = \x. if (x = 0) then PosInf else inv x` THEN
  Know `!x. 0 < inv' x <=> x <> PosInf /\ 0 <= x` (* inv_pos_eq' *)
  >- (GEN_TAC \\
      Cases_on `x = 0`
      >- (Q.UNABBREV_TAC `inv'` \\
          ASM_SIMP_TAC std_ss [le_refl, num_not_infty, lt_infty]) \\
      Q.UNABBREV_TAC `inv'` >> ASM_SIMP_TAC std_ss [] \\
      POP_ASSUM (REWRITE_TAC o wrap o (MATCH_MP inv_pos_eq))) THEN
  DISCH_TAC THEN
  Know `!i:num. ?x. 0 < x /\ x < inv' (B i)` >-
  (GEN_TAC THEN Q.UNABBREV_TAC `B` THEN BETA_TAC THEN
   Suff `0 < inv' (2 pow SUC i * measure m (A i))`
   >- (DISCH_THEN (MP_TAC o MATCH_MP Q_DENSE_IN_R) THEN METIS_TAC []) THEN
   POP_ORW THEN
   `(2 pow SUC i <> NegInf) /\ (2 pow SUC i <> PosInf)`
    by METIS_TAC [pow_not_infty, num_not_infty] THEN
   KNOW_TAC ``measure m ((A:num->'a->bool) i) <> NegInf`` THENL
   [FULL_SIMP_TAC std_ss [measure_space_def, positive_def, lt_infty] THEN
    MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `0` THEN
    SIMP_TAC std_ss [num_not_infty,  GSYM lt_infty] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SET_TAC [],
    DISCH_TAC] THEN CONJ_TAC THENL
   [`?r. measure m (A i) = Normal r` by METIS_TAC [extreal_cases] THEN
    ASM_REWRITE_TAC [] THEN KNOW_TAC ``0:real <= r`` THENL
    [REWRITE_TAC [GSYM extreal_le_def] THEN
     FIRST_X_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
     ASM_SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN
     FULL_SIMP_TAC std_ss [measure_space_def, positive_def] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SET_TAC [], DISCH_TAC] THEN
    ONCE_REWRITE_TAC [mul_comm] THEN METIS_TAC [mul_not_infty],
    ALL_TAC] THEN
   `2 pow SUC i = Normal (real (2 pow SUC i))` by METIS_TAC [normal_real] THEN
   `measure m (A i) = Normal (real (measure m (A i)))` by METIS_TAC [normal_real] THEN
   MATCH_MP_TAC le_mul THEN CONJ_TAC THENL
   [ALL_TAC,
   FULL_SIMP_TAC std_ss [measure_space_def, positive_def] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SET_TAC []] THEN
   MATCH_MP_TAC pow_pos_le THEN
   SIMP_TAC real_ss [extreal_le_def, extreal_of_num_def]) THEN DISCH_TAC THEN
  Know `?f. !x. 0 < f x /\ f x < inv' (2 pow SUC x * measure m (A x))`
  >- (METIS_TAC []) THEN STRIP_TAC THEN
  Know `!x. 0 <= f x` >- (ASM_SIMP_TAC std_ss [le_lt]) THEN DISCH_TAC THEN
  Q.ABBREV_TAC `h = (\x. suminf (\i. f i * indicator_fn (A i) x))` THEN
  Know `!i. A i IN measurable_sets m` >- ASM_SET_TAC [] THEN DISCH_TAC THEN
  Know `pos_fn_integral m h = suminf (\i. f i * measure m (A i))` >-
  (Q.UNABBREV_TAC `h` THEN
   Know `pos_fn_integral m (\x. suminf (\i. (\i x. f i * indicator_fn (A i) x) i x)) =
         suminf (\i. pos_fn_integral m ((\i x. f i * indicator_fn (A i) x) i))` >-
   (MATCH_MP_TAC pos_fn_integral_suminf THEN RW_TAC std_ss [] THENL
    [MATCH_MP_TAC le_mul THEN ASM_SIMP_TAC std_ss [indicator_fn_def] THEN
     COND_CASES_TAC THEN SIMP_TAC std_ss [le_refl] THEN
     SIMP_TAC real_ss [extreal_le_def, extreal_of_num_def], ALL_TAC] THEN
    ONCE_REWRITE_TAC [METIS [] ``(\x. f i * indicator_fn (A i) x) =
                         (\x. (\x. f i) x * indicator_fn (A i) x)``] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR THEN
    FULL_SIMP_TAC std_ss [measure_space_def, subsets_def] THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN Q.EXISTS_TAC `f i` THEN
    ASM_SIMP_TAC std_ss [] ) THEN
   RW_TAC std_ss [] THEN POP_ASSUM K_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
   Suff `(f i <> NegInf) /\ (f i <> PosInf)` THENL
   [STRIP_TAC THEN `f i = Normal (real (f i))` by METIS_TAC [GSYM normal_real] THEN
    ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC pos_fn_integral_cmul_indicator THEN
    POP_ASSUM K_TAC THEN ASM_SIMP_TAC std_ss [] THEN
    SIMP_TAC std_ss [GSYM extreal_le_def, GSYM extreal_of_num_def] THEN
    ASM_SIMP_TAC std_ss [normal_real], ALL_TAC] THEN
   CONJ_TAC THENL
   [SIMP_TAC std_ss [lt_infty] THEN MATCH_MP_TAC lte_trans THEN
    Q.EXISTS_TAC `0` THEN ASM_SIMP_TAC std_ss [num_not_infty, GSYM lt_infty],
    ALL_TAC] THEN SIMP_TAC std_ss [lt_infty] THEN
   Cases_on `measure m (A i) = 0`
   >- (POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
       POP_ASSUM (MP_TAC o Q.SPEC `i`) THEN
       qunabbrevl_tac [`inv'`, `B`] THEN RW_TAC std_ss [] THEN
       FULL_SIMP_TAC std_ss [mul_rzero]) THEN
   MATCH_MP_TAC lt_trans THEN
   Q.EXISTS_TAC `inv' (2 pow SUC i * measure m (A i))` THEN
   ASM_SIMP_TAC std_ss [] THEN
   `(2 pow SUC i <> NegInf) /\ (2 pow SUC i <> PosInf)`
       by METIS_TAC [pow_not_infty, num_not_infty] THEN
   Know `measure m ((A:num->'a->bool) i) <> NegInf`
   >- (IMP_RES_TAC MEASURE_SPACE_POSITIVE \\
       POP_ASSUM (MATCH_MP_TAC o (MATCH_MP positive_not_infty)) >> art []) THEN
   DISCH_TAC THEN
   `?r. 2 pow SUC i = Normal r` by METIS_TAC [extreal_cases] THEN
   `?a. measure m (A i) = Normal a` by METIS_TAC [extreal_cases] THEN
   qunabbrevl_tac [`inv'`, `B`] THEN BETA_TAC THEN
   ONCE_ASM_REWRITE_TAC [] THEN
   SIMP_TAC std_ss [extreal_mul_def, extreal_of_num_def, extreal_11] THEN
   `(0 :extreal) < 2 pow (SUC i)` by METIS_TAC [pow_pos_lt, lt_02] THEN
   `a <> 0` by METIS_TAC [extreal_of_num_def, extreal_11] THEN
   `0 < r` by METIS_TAC [extreal_of_num_def, extreal_lt_eq] THEN
   Know `r * a <> 0`
   >- (`r <> 0` by METIS_TAC [REAL_LT_LE] \\
       CCONTR_TAC >> METIS_TAC [REAL_ENTIRE]) THEN DISCH_TAC THEN
   ASM_SIMP_TAC std_ss [extreal_inv_eq, lt_infty] ) THEN DISCH_TAC THEN
  Know `suminf (\i. f i * measure m (A i)) <= suminf (\i. (1 / 2) pow SUC i)` >-
  (MATCH_MP_TAC ext_suminf_mono THEN RW_TAC std_ss [lt_infty]
   >- (MATCH_MP_TAC le_mul THEN
       FULL_SIMP_TAC std_ss [measure_space_def, positive_def]) THEN
   MATCH_MP_TAC le_trans THEN
   Q.EXISTS_TAC `inv' (2 pow SUC n * measure m (A n)) * measure m (A n)` THEN
   CONJ_TAC
   >- (Cases_on `measure m (A n) = 0`
       >- (ASM_SIMP_TAC std_ss [mul_rzero, le_refl]) THEN
       MATCH_MP_TAC le_rmul_imp THEN FULL_SIMP_TAC std_ss [measure_space_def, le_lt] THEN
       FULL_SIMP_TAC std_ss [positive_def, le_lt] THEN METIS_TAC []) THEN
   `(2 pow SUC n <> NegInf) /\ (2 pow SUC n <> PosInf)`
      by METIS_TAC [pow_not_infty, num_not_infty] THEN
   KNOW_TAC ``measure m ((A:num->'a->bool) n) <> NegInf`` THENL
   [FULL_SIMP_TAC std_ss [measure_space_def, positive_def, lt_infty] THEN
    MATCH_MP_TAC lte_trans THEN Q.EXISTS_TAC `0` THEN
    SIMP_TAC std_ss [num_not_infty,  GSYM lt_infty] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SET_TAC [],
    DISCH_TAC] THEN
   Cases_on `measure m (A n) = 0`
   >- (ASM_SIMP_TAC std_ss [mul_rzero] THEN MATCH_MP_TAC pow_pos_le THEN
       SIMP_TAC std_ss [half_between]) THEN
   `?r. 2 pow SUC n = Normal r` by METIS_TAC [extreal_cases] THEN
   `?a. measure m (A n) = Normal a` by METIS_TAC [extreal_cases] THEN
   ONCE_ASM_REWRITE_TAC [] THEN SIMP_TAC std_ss [extreal_mul_def] THEN
   `(0 :extreal) < 2 pow (SUC n)` by METIS_TAC [pow_pos_lt, lt_02] THEN
   `a <> 0` by METIS_TAC [extreal_of_num_def, extreal_11] THEN
   `0 < r` by METIS_TAC [extreal_of_num_def, extreal_lt_eq] THEN
   Know `r * a <> 0`
   >- (`r <> 0` by METIS_TAC [REAL_LT_LE] \\
       CCONTR_TAC >> METIS_TAC [REAL_ENTIRE]) THEN DISCH_TAC THEN
   Q.UNABBREV_TAC `inv'` >> BETA_TAC THEN
   `Normal (r * a) <> 0` by METIS_TAC [extreal_of_num_def, extreal_11] THEN
   ASM_SIMP_TAC std_ss [extreal_inv_eq] THEN
   `r <> 0` by METIS_TAC [REAL_LT_LE] THEN
   ASM_SIMP_TAC std_ss [REAL_INV_MUL, GSYM extreal_mul_def] THEN
   Know `Normal (inv a) * Normal a = 1`
   >- (SIMP_TAC std_ss [extreal_mul_def] THEN
       GEN_REWR_TAC RAND_CONV [extreal_of_num_def] THEN
       SIMP_TAC std_ss [extreal_11] THEN ASM_SIMP_TAC std_ss [REAL_MUL_LINV]) THEN
   ONCE_REWRITE_TAC [GSYM mul_assoc] THEN Rewr' THEN
   RW_TAC std_ss [mul_rone] THEN
   ASM_SIMP_TAC std_ss [normal_inv_eq] THEN
   GEN_REWR_TAC LAND_CONV [GSYM mul_lone] THEN
   ASM_SIMP_TAC std_ss [GSYM extreal_div_def] THEN
   ASM_SIMP_TAC std_ss [GSYM le_ldiv] THEN
   Q.PAT_ASSUM `_ = Normal r` (ONCE_REWRITE_TAC o wrap o SYM) THEN
   ASM_SIMP_TAC std_ss [GSYM pow_mul] THEN
   MATCH_MP_TAC le_trans THEN Q.EXISTS_TAC `(1 / 2 * 2) pow 0` THEN
   CONJ_TAC >- (SIMP_TAC std_ss [pow_0, le_lt]) THEN
   MATCH_MP_TAC pow_le_mono THEN SIMP_TAC arith_ss [] THEN
   SIMP_TAC real_ss [extreal_le_def, extreal_of_num_def, extreal_div_eq, extreal_mul_def,
                     GSYM REAL_LE_LDIV_EQ] ) THEN
  RW_TAC std_ss [pow_half_ser'] THEN
  `pos_fn_integral m h <> PosInf` by METIS_TAC [lt_infty, num_not_infty, let_trans] THEN
  Know `!x. x IN m_space m ==> ?i. x IN A i`
  >- (RULE_ASSUM_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
      FULL_SIMP_TAC std_ss [IN_BIGUNION, IN_UNIV, GSPECIFICATION] THEN
      METIS_TAC []) THEN DISCH_TAC THEN
  Know `!x i. x IN A i ==> (h x = f i)`
  >- (RW_TAC std_ss [] \\
      Q.UNABBREV_TAC `h` >> BETA_TAC \\
      MATCH_MP_TAC ext_suminf_cmult_indicator \\
      ASM_SIMP_TAC std_ss []) THEN DISCH_TAC THEN
  Know `!x. x IN m_space m ==> 0 < h x /\ h x < PosInf`
  >- (RW_TAC std_ss []
      >- (FIRST_X_ASSUM (MP_TAC o Q.SPEC `x`) THEN
          FIRST_X_ASSUM (MP_TAC o Q.SPEC `x`) THEN ASM_REWRITE_TAC [] THEN
          STRIP_TAC THEN DISCH_THEN (MP_TAC o Q.SPEC `i`) THEN
          ASM_REWRITE_TAC [] THEN RW_TAC std_ss []) THEN
      FIRST_X_ASSUM (MP_TAC o Q.SPEC `x`) THEN
      FIRST_X_ASSUM (MP_TAC o Q.SPEC `x`) THEN ASM_REWRITE_TAC [] THEN
      STRIP_TAC THEN DISCH_THEN (MP_TAC o Q.SPEC `i`) THEN
      ASM_REWRITE_TAC [] THEN RW_TAC std_ss [] THEN
      UNDISCH_TAC ``!x. 0 < f x /\ f x < inv' (2 pow SUC x * measure m (A x))`` THEN
      DISCH_THEN (MP_TAC o Q.SPEC `i`) THEN
      Cases_on `measure m (A i) = 0`
      >- (POP_ORW THEN SIMP_TAC std_ss [mul_rzero] THEN
          Q.UNABBREV_TAC `inv'` THEN METIS_TAC []) THEN
      STRIP_TAC THEN MATCH_MP_TAC lte_trans THEN
      Q.EXISTS_TAC `inv' (2 pow SUC i * measure m (A i))` THEN
      ASM_REWRITE_TAC [le_infty]) THEN DISCH_TAC THEN
  Know `!x. 0 <= h x`
  >- (GEN_TAC >> Q.UNABBREV_TAC `h` >> BETA_TAC \\
      MATCH_MP_TAC ext_suminf_pos >> RW_TAC std_ss [] \\
      MATCH_MP_TAC le_mul >> art [INDICATOR_FN_POS]) THEN DISCH_TAC THEN
  Q.EXISTS_TAC `h` THEN ASM_SIMP_TAC std_ss [] THEN
 (* h IN Borel_measurable (m_space m,measurable_sets m) *)
  Q.UNABBREV_TAC `h` \\
  MATCH_MP_TAC IN_MEASURABLE_BOREL_SUMINF \\
  Q.EXISTS_TAC `\i x. f i * indicator_fn (A i) x` \\
  STRONG_CONJ_TAC >- PROVE_TAC [measure_space_def] >> DISCH_TAC \\
  RW_TAC std_ss [space_def] >| (* 2 subgoals *)
  [ (* goal 1 (of 2) *)
    MATCH_MP_TAC
     (BETA_RULE (Q.SPECL [`(m_space m,measurable_sets m)`, `\x. f n`, `A n`]
                 IN_MEASURABLE_BOREL_MUL_INDICATOR)) \\
    RW_TAC std_ss [subsets_def] \\
    MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST' >> art [],
    (* goal 2 (of 2) *)
    MATCH_MP_TAC le_mul >> art [INDICATOR_FN_POS] ]
QED

(* The most general version (M: sigma-finite, N: arbitrary).

   cf. Radon_Nikodym_finite, Radon_Nikodym_finite_arbitrary
 *)
Theorem Radon_Nikodym_sigma_finite : (* was: RADON_NIKODYM *)
    !M N. measure_space M /\ measure_space N /\
         (m_space M = m_space N) /\ (measurable_sets M = measurable_sets N) /\
          sigma_finite M /\
          measure_absolutely_continuous (measure N) M ==>
      ?f. f IN measurable (m_space M,measurable_sets M) Borel /\ (!x. 0 <= f x) /\
          !A. A IN measurable_sets M ==>
             (pos_fn_integral M (\x. f x * indicator_fn A x) = measure N A)
Proof
    rpt STRIP_TAC
 >> ‘sigma_algebra (measurable_space M) /\ sigma_algebra (measurable_space N)’
      by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
 >> Q.PAT_X_ASSUM `m_space M = m_space N` (ASSUME_TAC o SYM)
 >> Q.PAT_X_ASSUM `measurable_sets M = measurable_sets N` (ASSUME_TAC o SYM)
 >> ASM_REWRITE_TAC []
 >> `{PosInf} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_INFINITY]
 >> `?h. h IN measurable (m_space M,measurable_sets M) Borel /\
         pos_fn_integral M h <> PosInf /\
         (!x. x IN m_space M ==> 0 < h x /\ h x < PosInf) /\ !x. 0 <= h x`
     by METIS_TAC [finite_integrable_function_exists]
 >> Q.ABBREV_TAC `t = \A. pos_fn_integral M (\x. h x * indicator_fn A x)`
 >> Q.ABBREV_TAC `mt = (m_space M, measurable_sets M,
                        (\A. pos_fn_integral M (\x. h x * indicator_fn A x)))`
 >> Know `measure mt (m_space mt) <> PosInf`
 >- (Q.UNABBREV_TAC `mt` THEN
     SIMP_TAC std_ss [measure_def, m_space_def] THEN
     ASM_SIMP_TAC std_ss [MEASURE_SPACE_MSPACE_MEASURABLE] THEN
     Suff `pos_fn_integral M (\x. h x * indicator_fn (m_space M) x) =
           pos_fn_integral M h` >- METIS_TAC [] THEN
     MATCH_MP_TAC (GSYM pos_fn_integral_mspace) THEN ASM_SIMP_TAC std_ss [])
 >> DISCH_TAC
 >> Know `measure_space mt`
 >- (Q.UNABBREV_TAC `mt` THEN
     FULL_SIMP_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def] THEN
     CONJ_TAC (* positive *)
     >- (SIMP_TAC std_ss [positive_def, measure_def, measurable_sets_def] \\
         Q.UNABBREV_TAC `t` >> BETA_TAC \\
         CONJ_TAC
         >- (SIMP_TAC std_ss [indicator_fn_def, NOT_IN_EMPTY, mul_rzero] \\
             ASM_SIMP_TAC std_ss [pos_fn_integral_zero, measure_space_def]) \\
         rpt STRIP_TAC >> MATCH_MP_TAC pos_fn_integral_pos \\
         ASM_SIMP_TAC std_ss [measure_space_def] \\
         rpt STRIP_TAC >> MATCH_MP_TAC le_mul >> art [INDICATOR_FN_POS]) \\
     SIMP_TAC std_ss [countably_additive_alt_eq] \\
     rpt STRIP_TAC >> SIMP_TAC std_ss [o_DEF] \\
    `!x. A x IN measurable_sets M` by ASM_SET_TAC [] \\
     ASM_SIMP_TAC std_ss [GSYM IMAGE_DEF] \\
     Q.UNABBREV_TAC `t` >> BETA_TAC \\
     Know `!x. indicator_fn (BIGUNION (IMAGE A univ(:num))) x =
               suminf (\j. indicator_fn (A j) x)`
     >- (GEN_TAC >> ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
         MATCH_MP_TAC indicator_fn_suminf \\
         FULL_SIMP_TAC std_ss [disjoint_family, disjoint_family_on, DISJOINT_DEF] \\
         ASM_SET_TAC []) \\
     DISCH_TAC >> ASM_SIMP_TAC std_ss [] \\
     Know `!x. h x * suminf (\j. indicator_fn (A j) x) =
               suminf (\j. h x * (\j. indicator_fn (A j) x) j)`
     >- (GEN_TAC >> MATCH_MP_TAC (GSYM ext_suminf_cmul) \\
         ASM_SIMP_TAC std_ss [INDICATOR_FN_POS]) >> DISC_RW_KILL \\
     SIMP_TAC std_ss [] \\
     ONCE_REWRITE_TAC [METIS [] ``(\x'. h x' * indicator_fn (A x) x') =
                             (\x. (\x'. h x' * indicator_fn (A x) x')) x``] \\
     ONCE_REWRITE_TAC [METIS [] ``suminf (\j. h x * indicator_fn (A j) x) =
                                  suminf (\j. (\x x'. h x' * indicator_fn (A x) x') j x)``] \\
     MATCH_MP_TAC pos_fn_integral_suminf \\
     ASM_SIMP_TAC std_ss [measure_space_def] \\
     CONJ_TAC >- (RW_TAC std_ss [] \\
                  MATCH_MP_TAC le_mul >> art [INDICATOR_FN_POS]) \\
     GEN_TAC >> MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR \\
     METIS_TAC [subsets_def, measurable_sets_def])
 >> DISCH_TAC
 >> Q.UNABBREV_TAC `t` (* not needed any more *)
 >> Cases_on `m_space M = {}`
 >- (Know `measurable_sets M = {{}}`
     >- (FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_alt_pow, POW_DEF] \\
         FULL_SIMP_TAC std_ss [SUBSET_EMPTY] \\
         UNDISCH_TAC ``measurable_sets M SUBSET {s:'a->bool | s = {}}`` \\
         SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, EXTENSION, IN_SING] \\
         SIMP_TAC std_ss [NOT_IN_EMPTY] \\
         ONCE_REWRITE_TAC [SET_RULE ``(!x'. x' NOTIN x) = (x = {})``] \\
         DISCH_TAC >> GEN_TAC >> POP_ASSUM (MP_TAC o Q.SPEC `x`) \\
         STRIP_TAC >> EQ_TAC >| [ASM_SET_TAC [], METIS_TAC []]) \\
     DISCH_TAC \\
     Q.EXISTS_TAC `(\x. 0)` >> ASM_SIMP_TAC std_ss [le_refl, IN_SING] \\
     FULL_SIMP_TAC std_ss [mul_lzero, measure_space_def, positive_def] \\
     reverse CONJ_TAC
     >- (MATCH_MP_TAC pos_fn_integral_zero \\
         METIS_TAC [measure_space_def, positive_def]) \\
     ASM_SIMP_TAC std_ss [IN_MEASURABLE_BOREL] \\
     ASM_SIMP_TAC std_ss [space_def, INTER_EMPTY, subsets_def] \\
     SRW_TAC [] [IN_DEF, IN_FUNSET])
 >> Suff `measure_absolutely_continuous (measure N) mt`
 >- (STRIP_TAC \\
     MP_TAC (Q.SPECL [`mt`, `N`] Radon_Nikodym_finite_arbitrary) \\
    `m_space mt = m_space M` by METIS_TAC [m_space_def] \\
    `measurable_sets mt = measurable_sets M` by METIS_TAC [measurable_sets_def] \\
     RW_TAC std_ss [] >> POP_ASSUM MP_TAC \\
     Know `!A. A IN measurable_sets mt ==>
              (pos_fn_integral mt (\x. f x * indicator_fn A x) =
               pos_fn_integral M (\x. h x * (\x. f x * indicator_fn A x) x))`
     >- (GEN_TAC THEN DISCH_TAC THEN
         Q.UNABBREV_TAC `mt` THEN
         ONCE_REWRITE_TAC [METIS [] ``pos_fn_integral M (\x. h x * (f x * indicator_fn A x)) =
                             pos_fn_integral M (\x. h x * (\x. f x * indicator_fn A x) x)``] \\
         Suff `pos_fn_integral
                (m_space M,measurable_sets M,
                 (\A. pos_fn_integral M (\x. max 0 (h x * indicator_fn A x))))
                (\x. max 0 ((\x. f x * indicator_fn A x) x)) =
               pos_fn_integral M (\x. max 0 (h x * (\x. f x * indicator_fn A x) x))`
         >- (ASM_SIMP_TAC std_ss [extreal_max_def, le_mul, indicator_fn_pos_le] \\
             METIS_TAC []) \\
         MATCH_MP_TAC pos_fn_integral_density' THEN ASM_SIMP_TAC std_ss [] \\
         CONJ_TAC
         >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR \\
             METIS_TAC [subsets_def, measure_space_def, measurable_sets_def, m_space_def]) \\
         CONJ_TAC
         >- (SIMP_TAC std_ss [AE_ALT, GSPECIFICATION, null_set_def, GSPEC_T] \\
             Q.EXISTS_TAC `{}` >> SIMP_TAC std_ss [IN_UNIV, GSPEC_F, SUBSET_REFL] \\
             METIS_TAC [measure_space_def, sigma_algebra_alt_pow, positive_def]) \\
         GEN_TAC >> MATCH_MP_TAC le_mul \\
         ASM_SIMP_TAC std_ss [INDICATOR_FN_POS]) \\
     NTAC 2 (DISCH_TAC) \\
     Q.EXISTS_TAC `(\x. h x * f x)` \\
     CONJ_TAC (* (\x. h x * f x) is borel-measurable *)
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES \\
         qexistsl_tac [`h`, `f`] >> ASM_SIMP_TAC std_ss []) \\
     CONJ_TAC (* 0 <= h x * f x *)
     >- (GEN_TAC >> BETA_TAC >> MATCH_MP_TAC le_mul >> art []) \\
     RW_TAC std_ss [] >> REV_FULL_SIMP_TAC std_ss [mul_assoc])
 (* below was reworked by Chun Tian without using null_sets_density_iff (nonsense) *)
 >> FULL_SIMP_TAC std_ss [measure_absolutely_continuous_def]
 >> rpt STRIP_TAC
 >> `measurable_sets mt = measurable_sets M`
       by METIS_TAC [measurable_sets_def] THEN FULL_SIMP_TAC std_ss []
 >> rename1 `measure N A = 0`
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> Q.PAT_X_ASSUM `measure mt A = 0` MP_TAC
 >> Q.UNABBREV_TAC `mt`
 >> FULL_SIMP_TAC std_ss [m_space_def, measurable_sets_def, measure_def]
 >> MP_TAC (Q.SPECL [`M`, `\x. h x * indicator_fn A x`] pos_fn_integral_eq_0)
 >> ASM_SIMP_TAC std_ss []
 >> Know ‘!x. x IN m_space M ==> 0 <= h x * indicator_fn A x’
 >- rw [le_mul, INDICATOR_FN_POS]
 >> Know `(\x. h x * indicator_fn A x) IN Borel_measurable (m_space M,measurable_sets M)`
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL_INDICATOR \\
     fs [measure_space_def, subsets_def])
 >> RW_TAC std_ss []
 >> Suff `A = {x | x IN m_space M /\ h x * indicator_fn A x <> 0}`
 >- (Rewr' >> art [])
 >> RW_TAC std_ss [Once EXTENSION, GSPECIFICATION, indicator_fn_def]
 >> Cases_on `x IN A` >> ASM_SIMP_TAC std_ss [mul_rone, mul_rzero]
 >> STRONG_CONJ_TAC >- METIS_TAC [MEASURE_SPACE_IN_MSPACE]
 >> METIS_TAC [lt_le]
QED

(* Final version: more compact using of "<<" and "*" (density_measure_def).

   Previous versions are not needed any more, cf. FINITE_IMP_SIGMA_FINITE.
 *)
Theorem Radon_Nikodym :
    !m v. measure_space m /\ sigma_finite m /\
          measure_space (m_space m,measurable_sets m,v) /\
          measure_absolutely_continuous v m ==>
      ?f. f IN measurable (m_space m,measurable_sets m) Borel /\ (!x. 0 <= f x) /\
          !s. s IN (measurable_sets m) ==> ((f * m) s = v s)
Proof
    RW_TAC std_ss [density_measure_def]
 >> MP_TAC (REWRITE_RULE [m_space_def, measurable_sets_def, measure_def]
              (Q.SPECL [`m`, `(m_space m,measurable_sets m,v)`]
                       Radon_Nikodym_sigma_finite))
 >> RW_TAC std_ss []
QED

(* A variant with ‘x IN m_space m’ added, aligned with ‘RN_deriv’. *)
Theorem Radon_Nikodym' :
    !m v. measure_space m /\ sigma_finite m /\
          measure_space (m_space m,measurable_sets m,v) /\
          measure_absolutely_continuous v m ==>
      ?f. f IN measurable (m_space m,measurable_sets m) Borel /\
         (!x. x IN m_space m ==> 0 <= f x) /\
          !s. s IN (measurable_sets m) ==> ((f * m) s = v s)
Proof
    rpt STRIP_TAC
 >> ‘?f. f IN measurable (m_space m,measurable_sets m) Borel /\ (!x. 0 <= f x) /\
         !s. s IN (measurable_sets m) ==> ((f * m) s = v s)’
      by METIS_TAC [Radon_Nikodym]
 >> Q.EXISTS_TAC ‘f’ >> rw []
QED

(* ------------------------------------------------------------------------- *)
(*   Applications of Radon_Nikodym (ported from HVG's normal_rvScript.sml)   *)
(* ------------------------------------------------------------------------- *)

(* Radon-Nikodym derivative (RN_deriv)

  `RN_deriv v m` (HOL) = `RN_deriv m (m_space m,measurable_sets m,v)` (Isabelle/HOL)

   The existence of `RN_deriv v m` is then asserted by Radon-Nikodym theorem, and
   its uniqueness is asserted by the following (unproved) theorem:

     !m f f'. measure_space m /\ sigma_finite m /\
              f IN borel_measurable (m_space m,measurable_sets m) /\
              f' IN borel_measurable (m_space m,measurable_sets m) /\
              nonneg f /\ nonneg f' /\
              (!s. s IN measurable_sets m ==> ((f * m) s = (f' * m) s))
          ==> AE x::m. (f x = f' x)

   see also density_measure_def for the overload of ‘*’ in `f * m`.
 *)
Definition RN_deriv_def : (* or `v / m` (dv/dm) *)
    RN_deriv v m =
      @f. f IN measurable (m_space m,measurable_sets m) Borel /\
          (!x. x IN m_space m ==> 0 <= f x) /\
          !s. s IN measurable_sets m ==> ((f * m) s = v s)
End

(* `f = RN_deriv v m` is denoted by `f = v / m`
   NOTE: cannot use the Overload syntax sugar here (on "/").
 *)
val _ = overload_on ("/", “RN_deriv”);

Theorem RN_deriv_thm :
    !m v. measure_space m /\
          (?f. f IN measurable (m_space m,measurable_sets m) Borel /\
              (!x. x IN m_space m ==> 0 <= f x) /\
              (!s. s IN measurable_sets m ==> (f * m) s = v s)) ==>
          !s. s IN measurable_sets m ==> (v / m * m) s = v s
Proof
    RW_TAC std_ss [RN_deriv_def]
 >> SELECT_ELIM_TAC
 >> CONJ_TAC >- (Q.EXISTS_TAC ‘f’ >> rw [])
 >> Q.X_GEN_TAC ‘g’
 >> rpt STRIP_TAC
 >> POP_ASSUM MATCH_MP_TAC >> art []
QED

(* This is ported from the following theorem (RN_derivI)

    !f M N. f IN measurable (m_space M, measurable_sets M) Borel /\
            (!x. 0 <= f x) /\ (density M f = measure_of N) /\
             measure_space M /\ measure_space N /\
            (measurable_sets M = measurable_sets N) ==>
            (density M (RN_deriv M N) = measure_of N)
 *)
Theorem RN_deriv_thm' : (* was: RN_derivI *)
    !f m v. measure_space m /\
            f IN measurable (m_space m,measurable_sets m) Borel /\
           (!x. x IN m_space m ==> 0 <= f x) /\
           (!s. s IN measurable_sets m ==> (f * m) s = v s) ==>
            measure_space_eq (density m (v / m))
                             (m_space m,measurable_sets m,v)
Proof
    rw [measure_space_eq_def, density_def]
 >> irule RN_deriv_thm >> art []
 >> Q.EXISTS_TAC ‘f’ >> rw []
QED

(***********************)
(*   Further Results   *)
(***********************)

(*  I add these results at the end
      in order to manipulate the simplifier without breaking anything
      - Jared Yeager                                                    *)

(*** integral and integrable Theorems with fewer preconditions ***)

Theorem integrable_measurable:
    !m f. integrable m f ==> f IN Borel_measurable (measurable_space m)
Proof
    simp[integrable_def]
QED

Theorem pos_fn_integrable_AE_finite:
    !m f. measure_space m /\ (!x. x IN m_space m ==> 0 <= f x) /\
        f IN Borel_measurable (measurable_space m) /\ pos_fn_integral m f <> PosInf ==>
        AE x::m. f x = (Normal o real o f) x
Proof
    rw[] >> rw[AE_ALT] >> qexists_tac ‘{x | x IN m_space m /\ f x = PosInf}’ >>
    simp[pos_fn_integral_infty_null] >> rw[SUBSET_DEF] >>
    Cases_on ‘f x’ >> fs[normal_real] >> rw[] >>
    last_x_assum (dxrule_then assume_tac) >> rfs[]
QED

Theorem integrable_AE_finite:
    !m f. measure_space m /\ integrable m f ==> AE x::m. f x = (Normal o real o f) x
Proof
    rw[] >> fs[integrable_def] >>
    map_every (fn tm => (qspecl_then [‘m’,tm] assume_tac) pos_fn_integrable_AE_finite) [‘f^+’,‘f^-’] >>
    rfs[FN_PLUS_POS,FN_MINUS_POS,IN_MEASURABLE_BOREL_FN_PLUS,IN_MEASURABLE_BOREL_FN_MINUS] >>
    fs[AE_ALT] >> qexists_tac ‘N UNION N'’ >> (drule_then assume_tac) NULL_SET_UNION >>
    rfs[IN_APP] >> pop_assum kall_tac >> fs[SUBSET_DEF] >> rw[] >>
    NTAC 2 (last_x_assum (drule_then assume_tac)) >> Cases_on ‘f x’ >> rw[] >>
    DISJ2_TAC >> first_x_assum irule >> simp[fn_minus_def,extreal_ainv_def]
QED

Theorem integrable_eq_AE_alt:
    !m f g. measure_space m /\ integrable m f /\ (AE x::m. f x = g x) /\
        g IN Borel_measurable (measurable_space m) ==> integrable m g
Proof
    simp[integrable_def] >> NTAC 4 strip_tac >>
    ‘pos_fn_integral m f^+ = pos_fn_integral m g^+ /\
        pos_fn_integral m f^- = pos_fn_integral m g^-’ suffices_by (rw[] >> fs[]) >>
    rw[] >> irule pos_fn_integral_cong_AE >> simp[FN_PLUS_POS,FN_MINUS_POS] >>
    fs[AE_ALT,SUBSET_DEF] >> qexists_tac ‘N’ >> rw[] >>
    last_x_assum (dxrule_then assume_tac) >> pop_assum irule >>
    pop_assum mp_tac >> CONV_TAC CONTRAPOS_CONV >>
    simp[fn_plus_def,fn_minus_def]
QED

Theorem integrable_cong_AE:
    !m f g. complete_measure_space m /\ (AE x::m. f x = g x) ==>
        (integrable m f <=> integrable m g)
Proof
    rw[] >> eq_tac >> rw[] >>
    dxrule_at_then (Pos $ el 1) (dxrule_at_then (Pos $ el 1) irule) integrable_eq_AE >> simp[] >>
    qspecl_then [‘m’,‘λx. g x = f x’,‘λx. f x = g x’] (irule_at Any o SIMP_RULE (srw_ss ()) []) AE_subset >>
    simp[]
QED

Theorem integrable_cong_AE_alt:
    !m f g. measure_space m /\ (AE x::m. f x = g x) /\
        f IN Borel_measurable (measurable_space m) /\ g IN Borel_measurable (measurable_space m)==>
        (integrable m f <=> integrable m g)
Proof
    rw[] >> eq_tac >> rw[] >>
    dxrule_at_then (Pos $ el 1) (dxrule_at_then (Pos $ el 1) irule) integrable_eq_AE_alt >> simp[] >>
    qspecl_then [‘m’,‘λx. g x = f x’,‘λx. f x = g x’] (irule_at Any o SIMP_RULE (srw_ss ()) []) AE_subset >>
    simp[]
QED

Theorem integral_mono_AE:
    !m f g. measure_space m /\ (AE x::m. f x <= g x) ==> integral m f <= integral m g
Proof
    rw[integral_def] >> irule sub_le_sub_imp >> NTAC 2 $ irule_at Any pos_fn_integral_mono_AE >>
    simp[FN_PLUS_POS,FN_MINUS_POS] >>
    map_every (fn tms => qspecl_then tms (irule_at Any o SIMP_RULE (srw_ss ()) []) AE_subset)
        [[‘m’,‘λx. f x <= g x’,‘λx. f^+ x <= g^+ x’],[‘m’,‘λx. f x <= g x’,‘λx. g^- x <= f^- x’]] >>
    simp[GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM] >> NTAC 2 strip_tac >>
    rw[fn_plus_def,fn_minus_def]
    >| [simp[le_neg],simp[Once le_negl],simp[Once le_negr,le_lt],simp[],simp[le_lt]] >>
    ‘F’ suffices_by simp[] >> qpat_x_assum ‘~b’ mp_tac >> simp[]
    >- (irule let_trans >> qexists_tac ‘g x’ >> simp[])
    >- (irule lte_trans >> qexists_tac ‘f x’ >> simp[])
QED

Theorem integral_add':
    !m f g. measure_space m /\ integrable m f /\ integrable m g ==>
        integral m (λx. f x + g x) = integral m f + integral m g
Proof
    rw[] >> imp_res_tac integrable_AE_finite >>
    (qspecl_then [‘m’,‘f’,‘Normal o real o f’,‘g’,‘Normal o real o g’] assume_tac)
        AE_eq_add >> rfs[] >>
    map_every (fn tms => (qspecl_then tms assume_tac) integral_cong_AE)
        [[‘m’,‘f’,‘Normal o real o f’],[‘m’,‘g’,‘Normal o real o g’],
        [‘m’,‘λx. f x + g x’,‘λx. Normal (real (f x)) + Normal (real (g x))’]] >>
    rfs[] >> NTAC 3 (pop_assum kall_tac) >>
    qspecl_then [‘m’,‘Normal o real o f’,‘Normal o real o g’] assume_tac integral_add >>
    rfs[] >> pop_assum irule >> rw[] >> irule integrable_eq_AE_alt >> fs[integrable_def] >>
    simp[IN_MEASURABLE_BOREL_NORMAL_REAL]
    >| [qexists_tac ‘f’,qexists_tac ‘g’] >> simp[]
QED

Theorem integrable_add':
    !m f g. measure_space m /\ integrable m f /\ integrable m g ==> integrable m (λx. f x + g x)
Proof
    rw[] >> imp_res_tac integrable_AE_finite >>
    (qspecl_then [‘m’,‘f’,‘Normal o real o f’,‘g’,‘Normal o real o g’] assume_tac) AE_eq_add >> rfs[] >>
    map_every (fn tms => (qspecl_then tms assume_tac) integrable_eq_AE_alt)
        [[‘m’,‘f’,‘Normal o real o f’],[‘m’,‘g’,‘Normal o real o g’],
        [‘m’,‘λx. Normal (real (f x)) + Normal (real (g x))’,‘λx. f x + g x’]] >>
    rfs[integrable_measurable,IN_MEASURABLE_BOREL_NORMAL_REAL] >> pop_assum irule >>
    simp[Once EQ_SYM_EQ] >> irule_at Any IN_MEASURABLE_BOREL_ADD' >>
    qexistsl_tac [‘g’,‘f’] >> simp[integrable_measurable] >>
    qspecl_then [‘m’,‘Normal o real o f’,‘Normal o real o g’] (irule o SIMP_RULE (srw_ss ()) []) integrable_add >>
    simp[]
QED

Theorem integral_sum':
    !m f s. FINITE s /\ measure_space m /\ (!i. i IN s ==> integrable m (f i)) ==>
        integral m (λx. SIGMA (λi. f i x) s) = SIGMA (λi. integral m (f i)) s
Proof
    rw[] >>
    resolve_then Any (resolve_then (Pos $ el 2)
        (qspecl_then [‘zzz’,‘xxx’,‘s’,‘m’,‘λi. Normal o real o f i’] irule) integral_sum) EQ_TRANS EQ_TRANS >>
    qexistsl_tac [‘f’,‘m’,‘s’] >> simp[] >>
    first_assum $ C (resolve_then Any assume_tac) integrable_AE_finite >> rfs[] >>
    qspecl_then [‘m’,‘λi x. f i x = Normal (real (f i x))’,‘s’] assume_tac AE_BIGINTER >>
    rfs[finite_countable] >> rw[]
    >- (irule integrable_eq_AE_alt >> simp[integrable_measurable,IN_MEASURABLE_BOREL_NORMAL_REAL] >>
        qexists_tac ‘f i’ >> simp[])
    >- (irule integral_cong_AE >> simp[] >>
        qspecl_then [‘m’,‘λx. !n. n IN s ==> f n x = Normal (real (f n x))’,
            ‘λx. SIGMA (λi. f i x) s = SIGMA (λi. Normal (real (f i x))) s’]
            (irule o SIMP_RULE (srw_ss ()) []) AE_subset >>
        rw[] >> irule EXTREAL_SUM_IMAGE_EQ' >> simp[])
    >- (irule EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
        rw[] >> irule integral_cong_AE >> simp[Once EQ_SYM_EQ])
QED

Theorem integrable_sum':
    !m f s. FINITE s /\ measure_space m /\ (!i. i IN s ==> integrable m (f i)) ==>
        integrable m (λx. SIGMA (λi. f i x) s)
Proof
    rw[] >> irule integrable_eq_AE_alt >> simp[] >> drule_then (irule_at Any) IN_MEASURABLE_BOREL_SUM' >>
    qexistsl_tac [‘f’,‘λx. SIGMA (λi. Normal (real (f i x))) s’] >> simp[integrable_measurable] >>
    qspecl_then [‘m’,‘λi. Normal o real o f i’,‘s’] (irule_at Any o SIMP_RULE (srw_ss ()) []) integrable_sum >>
    simp[] >> first_assum $ C (resolve_then Any assume_tac) integrable_AE_finite >> rfs[] >>
    qspecl_then [‘m’,‘λi x. f i x = Normal (real (f i x))’,‘s’] assume_tac AE_BIGINTER >>
    rfs[finite_countable] >> rw[]
    >- (irule integrable_eq_AE_alt >> simp[integrable_measurable,IN_MEASURABLE_BOREL_NORMAL_REAL] >>
        qexists_tac ‘f i’ >> simp[])
    >- (qspecl_then [‘m’,‘λx. !n. n IN s ==> f n x = Normal (real (f n x))’,
            ‘λx. SIGMA (λi. Normal (real (f i x))) s = SIGMA (λi. f i x) s’]
            (irule o SIMP_RULE (srw_ss ()) []) AE_subset >>
        rw[] >> irule EXTREAL_SUM_IMAGE_EQ' >> simp[])
QED

Theorem integral_sub':
    !m f g. measure_space m /\ integrable m f /\ integrable m g ==>
        integral m (λx. f x - g x) = integral m f - integral m g
Proof
    rw [extreal_sub]
 >> ‘integrable m (\x. -g x)’ by METIS_TAC [integrable_ainv]
 >> Know ‘Normal (-1) * integral m g = integral m (\x. Normal (-1) * g x)’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC integral_cmul >> art [])
 >> rw [GSYM neg_minus1, GSYM extreal_ainv_def, normal_1]
 >> HO_MATCH_MP_TAC integral_add' >> rw []
QED

Theorem integrable_sub':
    !m f g. measure_space m /\ integrable m f /\ integrable m g ==>
        integrable m (λx. f x - g x)
Proof
    rw [extreal_sub]
 >> ‘integrable m (\x. -g x)’ by METIS_TAC [integrable_ainv]
 >> HO_MATCH_MP_TAC integrable_add' >> rw []
QED

(* An easy corollary of the new integral_add' and integrable_add' *)
Theorem integral_add3 :
    !m f g h. measure_space m /\
              integrable m f /\ integrable m g /\ integrable m h
          ==> integral m (\x. f x + g x + h x) =
              integral m f + integral m g + integral m h
Proof
    rpt STRIP_TAC
 >> Know ‘integral m (\x. f x + g x + h x) =
          integral m (\x. f x + g x) + integral m h’
 >- (HO_MATCH_MP_TAC integral_add' >> simp [] \\
     MATCH_MP_TAC integrable_add' >> rw [])
 >> Rewr'
 >> Suff ‘integral m (\x. f x + g x) = integral m f + integral m g’ >- rw []
 >> MATCH_MP_TAC integral_add' >> rw []
QED

val _ = export_theory ();

(* References:

  [1] Schilling, R.L.: Measures, Integrals and Martingales (Second Edition).
      Cambridge University Press (2017).
  [2] Mhamdi, T., Hasan, O., Tahar, S.: Formalization of Measure Theory and Lebesgue
      Integration for Probabilistic Analysis in HOL. ACM Trans. Embedded Comput. Syst.
      12, 1-23 (2013). DOI:10.1145/2406336.2406349
  [4] Wikipedia: https://en.wikipedia.org/wiki/Beppo_Levi
  [5] Wikipedia: https://en.wikipedia.org/wiki/Giuseppe_Vitali
  [6] Shiryaev, A.N.: Probability-1. Springer-Verlag New York (2016).
  [7] Coble, A.R.: Anonymity, information, and machine-assisted proof. University of Cambridge (2010).
 *)
