(* ------------------------------------------------------------------------- *)
(* Borel measurable sets defined on reals (from "examples/diningcryptos")    *)
(* Author: Aaron Coble (2010)                                                *)
(* Cambridge University                                                      *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib metisLib arithmeticTheory pred_setTheory
     listTheory combinTheory pairTheory realTheory realLib jrhUtils realSimps
     simpLib seqTheory real_sigmaTheory transcTheory limTheory numTheory;

open hurdUtils util_probTheory sigma_algebraTheory real_measureTheory;

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "borel" (renamed to "real_borel")               *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "real_borel";

(* ************************************************************************* *)
(* Basic Definitions                                                         *)
(* ************************************************************************* *)

val borel_def = Define
   `borel = sigma univ(:real) (IMAGE (\a:real. {x:real | x <= a}) univ(:real))`;

val _ = overload_on ("borel_measurable", ``\a. measurable a borel``);

val mono_convergent_def = Define
   `mono_convergent u f s <=>
        (!x m n. m <= n /\ x IN s ==> u m x <= u n x) /\
        (!x. x IN s ==> (\i. u i x) --> f x)`;

val indicator_fn_def = Define
   `indicator_fn s = \x. if x IN s then (1:real) else (0:real)`;

(* ************************************************************************* *)
(* Proofs                                                                    *)
(* ************************************************************************* *)

val in_borel_measurable = store_thm
  ("in_borel_measurable",
   ``!f s. f IN borel_measurable s <=>
           sigma_algebra s /\
           (!s'. s' IN subsets (sigma UNIV (IMAGE (\a. {x | x <= a}) UNIV)) ==>
                 PREIMAGE f s' INTER space s IN subsets s)``,
   RW_TAC std_ss [IN_MEASURABLE, borel_def,
                  SPACE_SIGMA, IN_FUNSET, IN_UNIV]
   >> `sigma_algebra (sigma UNIV (IMAGE (\a. {x | x <= a}) UNIV))`
        by (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA
            >> RW_TAC std_ss [subset_class_def, SUBSET_DEF, IN_UNIV])
   >> ASM_REWRITE_TAC []);

val borel_measurable_const = store_thm
  ("borel_measurable_const",
  ``!s c. sigma_algebra s ==> (\x. c) IN borel_measurable s``,
   RW_TAC std_ss [in_borel_measurable]
   >> Cases_on `c IN s'`
   >- (`PREIMAGE (\x. c) s' INTER space s = space s`
        by RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_PREIMAGE]
        >> POP_ORW
        >> MATCH_MP_TAC ALGEBRA_SPACE >> MATCH_MP_TAC SIGMA_ALGEBRA_ALGEBRA
        >> ASM_REWRITE_TAC [])
   >> `PREIMAGE (\x. c) s' INTER space s = {}`
        by RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_PREIMAGE, NOT_IN_EMPTY]
   >> POP_ORW
   >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA]);

val borel_measurable_indicator = store_thm
  ("borel_measurable_indicator",
   ``!s a. sigma_algebra s /\ a IN subsets s ==>
           indicator_fn a IN borel_measurable s``,
   RW_TAC std_ss [indicator_fn_def, in_borel_measurable]
   >> Cases_on `1 IN s'`
   >- (Cases_on `0 IN s'`
       >- (`PREIMAGE (\x. (if x IN a then 1 else 0)) s' INTER space s = space s`
                by (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_PREIMAGE]
                    >> METIS_TAC [])
           >> POP_ORW
           >> MATCH_MP_TAC ALGEBRA_SPACE >> MATCH_MP_TAC SIGMA_ALGEBRA_ALGEBRA
           >> ASM_REWRITE_TAC [])
       >> `PREIMAGE (\x. (if x IN a then 1 else 0)) s' INTER space s = a`
                by (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_PREIMAGE]
                    >> METIS_TAC [SIGMA_ALGEBRA, algebra_def, subset_class_def, SUBSET_DEF])
       >> ASM_REWRITE_TAC [])
   >> Cases_on `0 IN s'`
   >- (`PREIMAGE (\x. (if x IN a then 1 else 0)) s' INTER space s = space s DIFF a`
                by (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_PREIMAGE, IN_DIFF]
                    >> METIS_TAC [SIGMA_ALGEBRA, algebra_def, subset_class_def, SUBSET_DEF])
        >> METIS_TAC [SIGMA_ALGEBRA, algebra_def])
   >> `PREIMAGE (\x. (if x IN a then 1 else 0)) s' INTER space s = {}`
        by (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_PREIMAGE, NOT_IN_EMPTY] >> METIS_TAC [])
   >> POP_ORW >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, algebra_def]);

(* c.f. IN_MEASURABLE_BOREL_RC in borelTheory *)
val borel_measurable_le_iff = store_thm
  ("borel_measurable_le_iff",
   ``!m. measure_space m ==>
         !f. f IN borel_measurable (m_space m, measurable_sets m) <=>
             !a. {w | w IN m_space m /\ f w <= a} IN measurable_sets m``,
   NTAC 3 STRIP_TAC >> EQ_TAC
   >- (RW_TAC std_ss [in_borel_measurable, subsets_def, space_def]
       >> POP_ASSUM (MP_TAC o REWRITE_RULE [PREIMAGE_def] o Q.SPEC `{b | b <= a}`)
       >> RW_TAC std_ss [GSPECIFICATION]
       >> `{x | f x <= a} INTER m_space m =
           {w | w IN m_space m /\ f w <= a}`
                by (RW_TAC std_ss [Once EXTENSION, IN_INTER, GSPECIFICATION]
                    >> DECIDE_TAC)
       >> FULL_SIMP_TAC std_ss [] >> POP_ASSUM (K ALL_TAC) >> POP_ASSUM MATCH_MP_TAC
       >> MATCH_MP_TAC IN_SIGMA
       >> RW_TAC std_ss [IN_IMAGE, IN_UNIV, Once EXTENSION, GSPECIFICATION]
       >> Q.EXISTS_TAC `a` >> SIMP_TAC std_ss [])
   >> RW_TAC std_ss [borel_def]
   >> MATCH_MP_TAC MEASURABLE_SIGMA
   >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, subset_class_def, space_def, subsets_def, SUBSET_UNIV,
                     IN_IMAGE]
   >- FULL_SIMP_TAC std_ss [measure_space_def]
   >> `PREIMAGE f {x | x <= a} INTER m_space m =
       {w | w IN m_space m /\ f w <= a}`
        by (RW_TAC std_ss [Once EXTENSION, IN_INTER, GSPECIFICATION, IN_PREIMAGE]
            >> DECIDE_TAC)
   >> RW_TAC std_ss []);

(* c.f. IN_MEASURABLE_BOREL_IMP in borelTheory *)
val sigma_le_less = store_thm
  ("sigma_le_less",
  ``!f A. sigma_algebra A /\ (!(a:real). {w | w IN space A /\ f w <= a} IN subsets A) ==>
          !a. {w | w IN space A /\ f w < a} IN subsets A``,
   rpt STRIP_TAC
   >> `BIGUNION (IMAGE (\n. {w | w IN space A /\ f w <= a - inv(&(SUC n))}) (UNIV:num->bool)) =
       {w | w IN space A /\ f w < a}`
        by (ONCE_REWRITE_TAC [EXTENSION]
            >> RW_TAC std_ss [GSPECIFICATION, IN_BIGUNION, IN_IMAGE, IN_UNIV]
            >> `(?s. x IN s /\ ?n. s = {w | w IN space A /\ f w <= a - inv (&SUC n)}) =
                (?n. x IN {w | w IN space A /\ f w <= a - inv (& (SUC n))})`
                by METIS_TAC [GSYM EXTENSION]
            >> POP_ORW
            >> RW_TAC std_ss [GSPECIFICATION]
            >> EQ_TAC
            >- (RW_TAC std_ss [] >- METIS_TAC [] >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `a - inv (& (SUC n))`
                >> RW_TAC real_ss [REAL_LT_SUB_RADD, REAL_LT_ADDR, REAL_LT_INV_EQ] >> METIS_TAC [])
            >> RW_TAC std_ss []
            >> `(\n. inv (($& o SUC) n)) --> 0`
                by (MATCH_MP_TAC SEQ_INV0
                    >> RW_TAC std_ss [o_DEF]
                    >> Q.EXISTS_TAC `clg y`
                    >> RW_TAC std_ss [GREATER_EQ, real_gt]
                    >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `&(clg y)`
                    >> RW_TAC std_ss [REAL_LT, LE_NUM_CEILING]
                    >> MATCH_MP_TAC LESS_EQ_LESS_TRANS >> Q.EXISTS_TAC `n`
                    >> RW_TAC arith_ss [])
            >> FULL_SIMP_TAC real_ss [SEQ, o_DEF]
            >> POP_ASSUM (MP_TAC o REWRITE_RULE [REAL_LT_SUB_LADD] o Q.SPEC `a - f x`)
            >> RW_TAC real_ss [ABS_INV, ABS_N, REAL_LE_SUB_LADD]
            >> Q.EXISTS_TAC `N` >> MATCH_MP_TAC REAL_LT_IMP_LE
            >> ONCE_REWRITE_TAC [REAL_ADD_COMM] >> POP_ASSUM MATCH_MP_TAC >> RW_TAC std_ss [])
   >> POP_ASSUM (MP_TAC o GSYM) >> RW_TAC std_ss []
   >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA]
   >> Q.PAT_ASSUM `!c. P c ==> BIGUNION c IN subsets A` MATCH_MP_TAC
   >> RW_TAC std_ss [COUNTABLE_NUM, image_countable, SUBSET_DEF, IN_IMAGE, IN_UNIV]
   >> METIS_TAC []);

val sigma_less_ge = store_thm
  ("sigma_less_ge",
  ``!f A. sigma_algebra A /\ (!(a:real). {w | w IN space A /\ f w < a} IN subsets A) ==>
          !a. {w | w IN space A /\ a <= f w} IN subsets A``,
   rpt STRIP_TAC
   >> `{w | w IN space A /\ a <= f w} =
       space A DIFF {w | w IN space A /\ f w < a}`
        by (RW_TAC std_ss [Once EXTENSION, IN_DIFF, GSPECIFICATION, real_lt]
            >> DECIDE_TAC)
   >> POP_ORW
   >> METIS_TAC [SIGMA_ALGEBRA]);

val sigma_ge_gr = store_thm
  ("sigma_ge_gr",
  ``!f A. sigma_algebra A /\ (!(a:real). {w | w IN space A /\ a <= f w} IN subsets A) ==>
          !a. {w | w IN space A /\ a < f w} IN subsets A``,
   rpt STRIP_TAC
   >> `BIGUNION (IMAGE (\n. {w | w IN space A /\ a <= f w - inv(&(SUC n))}) (UNIV:num->bool)) =
       {w | w IN space A /\ a < f w}`
        by (ONCE_REWRITE_TAC [EXTENSION]
            >> RW_TAC std_ss [GSPECIFICATION, IN_BIGUNION, IN_IMAGE, IN_UNIV]
            >> `(?s. x IN s /\ ?n. s = {w | w IN space A /\ a <= f w - inv (& (SUC n))}) =
                (?n. x IN {w | w IN space A /\ a <= f w - inv (& (SUC n))})`
                by METIS_TAC []
            >> POP_ORW
            >> RW_TAC std_ss [GSPECIFICATION]
            >> EQ_TAC
            >- (RW_TAC std_ss [] >- ASM_REWRITE_TAC [] >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `f x - inv (& (SUC n))`
                >> RW_TAC real_ss [REAL_LT_SUB_RADD, REAL_LT_ADDR, REAL_LT_INV_EQ])
            >> RW_TAC std_ss []
            >> `(\n. inv (($& o SUC) n)) --> 0`
                by (MATCH_MP_TAC SEQ_INV0
                    >> RW_TAC std_ss [o_DEF]
                    >> Q.EXISTS_TAC `clg y`
                    >> RW_TAC std_ss [GREATER_EQ, real_gt]
                    >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `&(clg y)`
                    >> RW_TAC std_ss [REAL_LT, LE_NUM_CEILING]
                    >> MATCH_MP_TAC LESS_EQ_LESS_TRANS >> Q.EXISTS_TAC `n`
                    >> RW_TAC arith_ss [])
            >> FULL_SIMP_TAC real_ss [SEQ, o_DEF]
            >> POP_ASSUM (MP_TAC o REWRITE_RULE [REAL_LT_SUB_LADD] o Q.SPEC `f x - a`)
            >> RW_TAC real_ss [ABS_INV, ABS_N, REAL_LE_SUB_LADD]
            >> Q.EXISTS_TAC `N` >> MATCH_MP_TAC REAL_LT_IMP_LE
            >> ONCE_REWRITE_TAC [REAL_ADD_COMM] >> POP_ASSUM MATCH_MP_TAC >> RW_TAC std_ss [])
   >> POP_ASSUM (MP_TAC o GSYM) >> RW_TAC std_ss []
   >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA]
   >> Q.PAT_ASSUM `!c. P c ==> BIGUNION c IN subsets A` MATCH_MP_TAC
   >> RW_TAC std_ss [COUNTABLE_NUM, image_countable, SUBSET_DEF, IN_IMAGE, IN_UNIV, REAL_LE_SUB_LADD]
   >> METIS_TAC []);

val sigma_gr_le = store_thm
  ("sigma_gr_le",
  ``!f A. sigma_algebra A /\ (!(a:real). {w | w IN space A /\ a < f w} IN subsets A) ==>
          !a. {w | w IN space A /\ f w <= a} IN subsets A``,
   rpt STRIP_TAC
   >> `{w | w IN space A /\ f w <= a} =
       space A DIFF {w | w IN space A /\ a < f w}`
        by (RW_TAC std_ss [Once EXTENSION, IN_DIFF, GSPECIFICATION, real_lt]
            >> DECIDE_TAC)
   >> POP_ORW
   >> METIS_TAC [SIGMA_ALGEBRA]);

val borel_measurable_gr_iff = store_thm
  ("borel_measurable_gr_iff",
  ``!m. measure_space m ==>
        !f. f IN borel_measurable (m_space m, measurable_sets m) <=>
            !a. {w | w IN m_space m /\ a < f w} IN measurable_sets m``,
   RW_TAC std_ss [measure_space_def, borel_measurable_le_iff]
   >> EQ_TAC
   >- (rpt STRIP_TAC
       >> `{w | w IN m_space m /\ a < f w} =
                m_space m DIFF {w | w IN m_space m /\ f w <= a}`
        by (ONCE_REWRITE_TAC [EXTENSION]
            >> RW_TAC std_ss [IN_DIFF, GSPECIFICATION, real_lt]
            >> DECIDE_TAC)
       >> POP_ORW
       >> METIS_TAC [SIGMA_ALGEBRA, space_def, subsets_def])
   >> METIS_TAC [sigma_gr_le, SPACE, subsets_def, space_def, measurable_sets_def, m_space_def]);

val borel_measurable_less_iff = store_thm
  ("borel_measurable_less_iff",
  ``!m. measure_space m ==>
        !f. f IN borel_measurable (m_space m, measurable_sets m) <=>
            !a. {w | w IN m_space m /\ f w < a} IN measurable_sets m``,
   RW_TAC std_ss [measure_space_def, borel_measurable_le_iff]
   >> EQ_TAC
   >- METIS_TAC [sigma_le_less, SPACE, subsets_def, space_def, measurable_sets_def, m_space_def]
   >> rpt STRIP_TAC
   >> `BIGUNION (IMAGE (\n. {w | w IN m_space m /\ a <= f w - inv(&(SUC n))}) (UNIV:num->bool)) =
       {w | w IN m_space m /\ a < f w}`
        by (ONCE_REWRITE_TAC [EXTENSION]
            >> RW_TAC std_ss [GSPECIFICATION, IN_BIGUNION, IN_IMAGE, IN_UNIV]
            >> `(?s. x IN s /\ ?n. s = {w | w IN m_space m /\ a <= f w - inv (& (SUC n))}) =
                (?n. x IN {w | w IN m_space m /\ a <= f w - inv (& (SUC n))})`
                by METIS_TAC []
            >> POP_ORW
            >> RW_TAC std_ss [GSPECIFICATION]
            >> EQ_TAC
            >- (RW_TAC std_ss [] >- ASM_REWRITE_TAC [] >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `f x - inv (& (SUC n))`
                >> RW_TAC real_ss [REAL_LT_SUB_RADD, REAL_LT_ADDR, REAL_LT_INV_EQ])
            >> RW_TAC std_ss []
            >> `(\n. inv (($& o SUC) n)) --> 0`
                by (MATCH_MP_TAC SEQ_INV0
                    >> RW_TAC std_ss [o_DEF]
                    >> Q.EXISTS_TAC `clg y`
                    >> RW_TAC std_ss [GREATER_EQ, real_gt]
                    >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `&(clg y)`
                    >> RW_TAC std_ss [REAL_LT, LE_NUM_CEILING]
                    >> MATCH_MP_TAC LESS_EQ_LESS_TRANS >> Q.EXISTS_TAC `n`
                    >> RW_TAC arith_ss [])
            >> FULL_SIMP_TAC real_ss [SEQ, o_DEF]
            >> POP_ASSUM (MP_TAC o REWRITE_RULE [REAL_LT_SUB_LADD] o Q.SPEC `f x - a`)
            >> RW_TAC real_ss [ABS_INV, ABS_N, REAL_LE_SUB_LADD]
            >> Q.EXISTS_TAC `N` >> MATCH_MP_TAC REAL_LT_IMP_LE
            >> ONCE_REWRITE_TAC [REAL_ADD_COMM] >> POP_ASSUM MATCH_MP_TAC >> RW_TAC std_ss [])
   >> `{w | w IN m_space m /\ f w <= a} =
                m_space m DIFF {w | w IN m_space m /\ a < f w}`
        by (RW_TAC std_ss [Once EXTENSION, IN_DIFF, GSPECIFICATION, real_lt]
            >> DECIDE_TAC)
   >> POP_ORW
   >> Suff `{w | w IN m_space m /\ a < f w} IN measurable_sets m`
   >- METIS_TAC [SPACE, subsets_def, space_def, measurable_sets_def, m_space_def, SIGMA_ALGEBRA]
   >> POP_ASSUM (MP_TAC o GSYM) >> RW_TAC std_ss []
   >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, subsets_def]
   >> Q.PAT_ASSUM `!c. P c ==> BIGUNION c IN (measurable_sets m)` MATCH_MP_TAC
   >> RW_TAC std_ss [COUNTABLE_NUM, image_countable, SUBSET_DEF, IN_IMAGE, IN_UNIV, REAL_LE_SUB_LADD]
   >> `{w | w IN m_space m /\ a + inv (& (SUC n)) <= f w} =
        m_space m DIFF {w | w IN m_space m /\ f w < a + inv (& (SUC n))}`
        by (RW_TAC std_ss [Once EXTENSION, IN_DIFF, GSPECIFICATION, real_lt]
            >> DECIDE_TAC)
   >> POP_ORW
   >> Suff `{w | w IN m_space m /\ f w < a + inv (& (SUC n))} IN measurable_sets m`
   >- METIS_TAC [SPACE, subsets_def, space_def, measurable_sets_def, m_space_def, SIGMA_ALGEBRA]
   >> METIS_TAC []);

val borel_measurable_ge_iff = store_thm
  ("borel_measurable_ge_iff",
   ``!m. measure_space m ==>
        !f. f IN borel_measurable (m_space m, measurable_sets m) <=>
            !a. {w | w IN m_space m /\ a <= f w} IN measurable_sets m``,
   RW_TAC std_ss [measure_space_def, borel_measurable_less_iff]
   >> EQ_TAC
   >- (rpt STRIP_TAC
       >> `{w | w IN m_space m /\ a <= f w} =
                m_space m DIFF {w | w IN m_space m /\ f w < a}`
        by (RW_TAC std_ss [Once EXTENSION, IN_DIFF, GSPECIFICATION, real_lt]
            >> DECIDE_TAC)
       >> POP_ORW
       >> METIS_TAC [SIGMA_ALGEBRA, space_def, subsets_def])
   >> METIS_TAC [sigma_ge_gr, sigma_gr_le, sigma_le_less, SPACE, subsets_def, space_def,
                 measurable_sets_def, m_space_def]);

val affine_borel_measurable = store_thm
  ("affine_borel_measurable",
   ``!m g. measure_space m /\ g IN borel_measurable (m_space m, measurable_sets m) ==>
           !(a:real) (b:real). (\x. a + (g x) * b) IN borel_measurable (m_space m, measurable_sets m)``,
   rpt STRIP_TAC
   >> Cases_on `b=0`
   >- (RW_TAC real_ss [] >> FULL_SIMP_TAC std_ss [measure_space_def, borel_measurable_const])
   >> `!x c. (a + g x * b <= c) = (g x * b <= c - a)`
        by (rpt STRIP_TAC >> REAL_ARITH_TAC)
   >> RW_TAC std_ss [borel_measurable_le_iff]
   >> POP_ASSUM (K ALL_TAC)
   >> Reverse (Cases_on `b < 0`)
   >- (`0 < b` by METIS_TAC [REAL_LT_LE, real_lt]
       >> `! x c. (g x * b <= c - a) = (g x <= (c - a) / b)`
        by (rpt STRIP_TAC
            >> MATCH_MP_TAC (GSYM REAL_LE_RDIV_EQ)
            >> ASM_REWRITE_TAC [])
       >> `!c. {w | w IN m_space m /\ a + g w * b <= c} =
               {w | w IN m_space m /\ g w <= (c - a) / b}`
                by (RW_TAC std_ss [Once EXTENSION, GSPECIFICATION]
                    >> FULL_SIMP_TAC std_ss [REAL_LE_SUB_LADD]
                    >> FULL_SIMP_TAC std_ss [Once REAL_ADD_COMM])
       >> RW_TAC std_ss [REAL_LE_SUB_LADD]
       >> METIS_TAC [borel_measurable_le_iff])
   >> RW_TAC std_ss [Once (GSYM REAL_LE_NEG), Once (GSYM REAL_MUL_RNEG)]
   >> `!x. (~(a' - a) <= g x * ~b) = ((~(a' - a))/(~b) <= g x)`
        by (STRIP_TAC >> MATCH_MP_TAC (GSYM REAL_LE_LDIV_EQ)
            >> RW_TAC std_ss [REAL_NEG_GT0])
   >> POP_ORW
   >> `{x | x IN m_space m /\ ~(a' - a) / ~b <= g x} =
        m_space m DIFF {x | x IN m_space m /\ g x < ~(a' - a) / ~b}`
        by (RW_TAC std_ss [Once EXTENSION, IN_DIFF, GSPECIFICATION, real_lt]
            >> DECIDE_TAC)
   >> POP_ORW
   >> Suff `{x | x IN m_space m /\ g x < ~(a' - a) / ~b} IN measurable_sets m`
   >- METIS_TAC [SPACE, subsets_def, space_def, measurable_sets_def, m_space_def, SIGMA_ALGEBRA, measure_space_def]
   >> METIS_TAC [borel_measurable_less_iff]);

val NON_NEG_REAL_RAT_DENSE = store_thm
  ("NON_NEG_REAL_RAT_DENSE",
  ``!(x:real)(y:real). 0 <= x /\ x < y ==> ?(m:num) (n:num). x < &m / & n /\ &m / &n < y``,
   rpt STRIP_TAC
   >> `0 < y - x` by RW_TAC real_ss [REAL_SUB_LT]
   >> (MP_TAC o Q.SPEC `y - x`) REAL_ARCH >> RW_TAC bool_ss []
   >> POP_ASSUM (MP_TAC o Q.SPEC `1`) >> RW_TAC bool_ss []
   >> Q.ABBREV_TAC `m = minimal (\a. y <= & (SUC a) / & n)`
   >> Q.EXISTS_TAC `m` >> Q.EXISTS_TAC `n`
   >> `0 < n`
        by (ONCE_REWRITE_TAC [GSYM REAL_LT]
            >> MATCH_MP_TAC REAL_LT_TRANS
            >> Q.EXISTS_TAC `1/(y-x)`
            >> CONJ_TAC >- (MATCH_MP_TAC REAL_LT_DIV >> RW_TAC real_ss [])
            >> METIS_TAC [REAL_LT_LDIV_EQ])
   >> (MP_TAC o Q.SPEC `inv (&n)`) REAL_ARCH >> ASM_SIMP_TAC real_ss [REAL_INV_POS]
   >> STRIP_TAC
   >> POP_ASSUM (MP_TAC o Q.SPEC `y`) >> STRIP_TAC
   >> `y * &n < &n'`
        by (FULL_SIMP_TAC std_ss [GSYM real_div]
            >> METIS_TAC [REAL_LT, REAL_LT_RDIV_EQ])
   >> FULL_SIMP_TAC std_ss [GSYM real_div]
   >> `minimal (\a. y <= & a / & n) = SUC m`
        by (MATCH_MP_TAC (GSYM MINIMAL_SUC_IMP)
            >> Reverse CONJ_TAC
            >- (RW_TAC real_ss [o_DEF,GSYM real_lt] >> METIS_TAC [REAL_LET_TRANS])
            >> Suff `(\a. y <= & (SUC a) / & n) m` >- RW_TAC std_ss []
            >> Q.UNABBREV_TAC `m`
            >> Q.ABBREV_TAC `P = (\a. y <= & (SUC a) / & n)`
            >> Suff `?a. P a` >- METIS_TAC [MINIMAL_EXISTS]
            >> Q.UNABBREV_TAC `P`
            >> RW_TAC std_ss []
            >> Cases_on `n' = 0`
            >- (FULL_SIMP_TAC real_ss [] >> METIS_TAC [REAL_LT_ANTISYM, REAL_LET_TRANS])
            >> METIS_TAC [num_CASES,REAL_LT_IMP_LE])
   >> `y <= & (SUC m) / & n`
        by (POP_ASSUM (MP_TAC o GSYM) >> RW_TAC std_ss []
            >> Q.ABBREV_TAC `P = (\a. y <= & a / & n)`
            >> METIS_TAC [MINIMAL_EXISTS, REAL_LT_IMP_LE])
   >> CONJ_TAC
   >- (Suff `y - (y - x) < (&(SUC m))/(&n) - inv(&n)`
       >- (SIMP_TAC bool_ss [real_div]
            >> ONCE_REWRITE_TAC [REAL_ARITH ``& m * inv (& n) - inv (& n) = (&m - 1) * inv (&n)``]
            >> SIMP_TAC real_ss [ADD1] >> ONCE_REWRITE_TAC [GSYM REAL_ADD]
            >> SIMP_TAC bool_ss [REAL_ADD_SUB_ALT])
       >> RW_TAC bool_ss [real_div]
       >> ONCE_REWRITE_TAC [REAL_ARITH ``& m * inv (& n) - inv (& n) = (&m - 1) * inv (&n)``]
       >> RW_TAC bool_ss [GSYM real_div]
       >> (MP_TAC o Q.SPECL [`y - (y - x)`,`&(SUC m) - 1`,`&n`]) REAL_LT_RDIV_EQ
       >> RW_TAC arith_ss [REAL_LT] >> ONCE_REWRITE_TAC [REAL_SUB_RDISTRIB]
       >> RW_TAC std_ss [REAL_LT_SUB_RADD]
       >> (MP_TAC o GSYM o Q.SPECL [`y`,`(&(SUC m)) - 1 + ((y-x)*(&n))`,`&n`]) REAL_LT_RDIV_EQ
       >> RW_TAC arith_ss [REAL_LT]
       >> RW_TAC bool_ss [real_div]
       >> ONCE_REWRITE_TAC [REAL_ARITH ``(& (SUC m) - 1 + (y - x) * & n) * inv (& n) =
                                         ((&(SUC m))*(inv(&n))) + ((y - x)*(&n)*inv(&n) - inv (&n))``]
       >> `(y - x) * (& n) * inv (& n) = (y - x)`
                by METIS_TAC [REAL_MUL_RINV, GSYM REAL_MUL_ASSOC, REAL_INJ,
                              DECIDE ``!(n:num). 0 < n ==> ~(n=0)``, REAL_MUL_RID]
       >> POP_ORW
       >> RW_TAC bool_ss [GSYM real_div]
       >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `& (SUC m)/(&n)`
       >> RW_TAC bool_ss [REAL_LT_ADDR, Once REAL_SUB_LT, REAL_INV_1OVER]
       >> (MP_TAC o Q.SPECL [`1`,`y - x`,`&n`]) REAL_LT_LDIV_EQ
       >> RW_TAC arith_ss [REAL_LT, REAL_MUL_COMM])
   >> RW_TAC std_ss [real_lt]
   >> Q.ABBREV_TAC `P = (\a. y <= & a / & n)`
   >> Suff `?n. P n` >- METIS_TAC [DECIDE ``m < SUC m``, MINIMAL_EXISTS]
   >> Q.UNABBREV_TAC `P`
   >> RW_TAC std_ss []
   >> Cases_on `n' = 0`
   >- (FULL_SIMP_TAC real_ss [] >> METIS_TAC [REAL_LT_ANTISYM, REAL_LET_TRANS])
   >> METIS_TAC [num_CASES,REAL_LT_IMP_LE]);

val real_rat_set_def = Define
   `real_rat_set = (IMAGE (\(a:num,b:num). (&a)/(&b)) (univ(:num) CROSS univ(:num))) UNION
                   (IMAGE (\(a:num,b:num). ~((&a)/(&b))) (univ(:num) CROSS univ(:num)))`;

val countable_real_rat_set = store_thm
  ("countable_real_rat_set", ``countable real_rat_set``,
   RW_TAC std_ss [real_rat_set_def] >> MATCH_MP_TAC union_countable
   >> Suff `countable ((UNIV:num->bool) CROSS (UNIV:num->bool))` >- RW_TAC std_ss [image_countable]
   >> RW_TAC std_ss [COUNTABLE_ALT_BIJ] >> DISJ2_TAC
   >> RW_TAC std_ss [enumerate_def]
   >> METIS_TAC [SELECT_THM, NUM_2D_BIJ_INV]);

val REAL_RAT_DENSE = store_thm
  ("REAL_RAT_DENSE",
  ``!(x:real)(y:real). x < y ==> ?i. i IN real_rat_set /\ x < i /\ i < y``,
   RW_TAC std_ss [real_rat_set_def, IN_UNION, IN_IMAGE, IN_CROSS, IN_UNIV]
   >> Suff `?(a:num)(b:num). (x < (&a)/(&b) /\ (&a)/(&b) < y) \/ (x < ~((&a)/(&b)) /\ ~((&a)/(&b)) < y)`
   >- (RW_TAC std_ss []
       >- (Q.EXISTS_TAC `&a/(&b)` >> RW_TAC std_ss []
           >> DISJ1_TAC >> Q.EXISTS_TAC `(a,b)` >> RW_TAC std_ss [])
       >> Q.EXISTS_TAC `~ (&a/(&b))` >> RW_TAC std_ss []
       >> DISJ2_TAC >> Q.EXISTS_TAC `(a,b)` >> RW_TAC std_ss [])
   >> Cases_on `0 <= x` >- METIS_TAC [NON_NEG_REAL_RAT_DENSE]
   >> FULL_SIMP_TAC std_ss [GSYM real_lt]
   >> Cases_on `0 < y`
   >- (Q.EXISTS_TAC `0` >> Q.EXISTS_TAC `1` >> RW_TAC real_ss [])
   >> POP_ASSUM (MP_TAC o REWRITE_RULE [real_lt]) >> STRIP_TAC
   >> ONCE_REWRITE_TAC [REAL_ARITH ``((x:real) = ~~x) /\ ((y:real)= ~~y)``]
   >> ONCE_REWRITE_TAC [REAL_LT_NEG]
   >> RW_TAC real_ss []
   >> `0 <= ~y` by METIS_TAC [real_lt, REAL_LE_NEG, REAL_NEG_0]
   >> `~y < ~x` by METIS_TAC [REAL_LT_NEG, REAL_LT_IMP_LE]
   >> METIS_TAC [NON_NEG_REAL_RAT_DENSE]);

val borel_measurable_less_borel_measurable = store_thm
  ("borel_measurable_less_borel_measurable",
   ``!m f g. measure_space m /\
             f IN borel_measurable (m_space m, measurable_sets m) /\
             g IN borel_measurable (m_space m, measurable_sets m) ==>
                {w | w IN m_space m /\ f w < g w} IN measurable_sets m``,
   rpt STRIP_TAC
   >> `{w | w IN m_space m /\ f w < g w} =
        BIGUNION (IMAGE (\i. {w | w IN m_space m /\ f w < i} INTER {w | w IN m_space m /\ i < g w })
                        real_rat_set)`
        by (MATCH_MP_TAC SUBSET_ANTISYM
            >> CONJ_TAC
            >- (RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_BIGUNION, IN_IMAGE, IN_INTER]
                >> Suff `?i. x IN {w | w IN m_space m /\ f w < i} INTER
                                  {w | w IN m_space m /\ i < g w} /\ i IN real_rat_set`
                >- METIS_TAC []
                >> RW_TAC std_ss [IN_INTER, GSPECIFICATION]
                >> METIS_TAC [REAL_RAT_DENSE])
            >> RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE]
            >> FULL_SIMP_TAC std_ss [IN_INTER, GSPECIFICATION]
            >> METIS_TAC [REAL_LT_TRANS])
   >> POP_ORW
   >> `sigma_algebra (m_space m,measurable_sets m)` by FULL_SIMP_TAC std_ss [measure_space_def]
   >> FULL_SIMP_TAC std_ss [sigma_algebra_def, subsets_def, space_def]
   >> Q.PAT_ASSUM `!c. P c ==> BIGUNION c IN measurable_sets m` MATCH_MP_TAC
   >> RW_TAC std_ss [image_countable, countable_real_rat_set, SUBSET_DEF, IN_IMAGE, IN_INTER]
   >> `measurable_sets m = subsets (m_space m, measurable_sets m)` by RW_TAC std_ss [subsets_def]
   >> POP_ORW >> MATCH_MP_TAC ALGEBRA_INTER
   >> RW_TAC std_ss [subsets_def]
   >> METIS_TAC [borel_measurable_less_iff, borel_measurable_gr_iff]);

val borel_measurable_leq_borel_measurable = store_thm
  ("borel_measurable_leq_borel_measurable",
   ``!m f g. measure_space m /\
             f IN borel_measurable (m_space m, measurable_sets m) /\
             g IN borel_measurable (m_space m, measurable_sets m) ==>
                {w | w IN m_space m /\ f w <= g w} IN measurable_sets m``,
   rpt STRIP_TAC
   >> `{w | w IN m_space m /\ f w <= g w} =
       m_space m DIFF {w | w IN m_space m /\ g w < f w}`
        by (RW_TAC std_ss [Once EXTENSION, IN_DIFF, GSPECIFICATION, real_lt] >> DECIDE_TAC)
   >> POP_ORW
   >> `{w | w IN m_space m /\ g w < f w} IN measurable_sets m`
        by RW_TAC std_ss [borel_measurable_less_borel_measurable]
   >> FULL_SIMP_TAC std_ss [measure_space_def, SIGMA_ALGEBRA, subsets_def, space_def]);

val borel_measurable_eq_borel_measurable = store_thm
  ("borel_measurable_eq_borel_measurable",
   ``!m f g. measure_space m /\
             f IN borel_measurable (m_space m, measurable_sets m) /\
             g IN borel_measurable (m_space m, measurable_sets m) ==>
                {w | w IN m_space m /\ (f w = g w)} IN measurable_sets m``,
   rpt STRIP_TAC
   >> `{w | w IN m_space m /\ (f w = g w)} =
       {w | w IN m_space m /\ f w <= g w} DIFF {w | w IN m_space m /\ f w < g w}`
        by (RW_TAC std_ss [Once EXTENSION, IN_DIFF, GSPECIFICATION, real_lt] >> METIS_TAC [REAL_LE_ANTISYM])
   >> POP_ORW
   >> `{w | w IN m_space m /\ f w < g w} IN measurable_sets m`
        by RW_TAC std_ss [borel_measurable_less_borel_measurable]
   >> `{w | w IN m_space m /\ f w <= g w} IN measurable_sets m`
        by RW_TAC std_ss [borel_measurable_leq_borel_measurable]

   >> FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def, subsets_def, space_def]
   >> `measurable_sets m = subsets (m_space m, measurable_sets m)` by RW_TAC std_ss [subsets_def]
   >> POP_ORW >> MATCH_MP_TAC ALGEBRA_DIFF
   >> RW_TAC std_ss [subsets_def]);

val borel_measurable_neq_borel_measurable = store_thm
  ("borel_measurable_neq_borel_measurable",
   ``!m f g. measure_space m /\
             f IN borel_measurable (m_space m, measurable_sets m) /\
             g IN borel_measurable (m_space m, measurable_sets m) ==>
                {w | w IN m_space m /\ ~(f w = g w)} IN measurable_sets m``,
   rpt STRIP_TAC
   >> `{w | w IN m_space m /\ ~(f w = g w)} =
       m_space m DIFF {w | w IN m_space m /\ (f w = g w)}`
        by (RW_TAC std_ss [Once EXTENSION, IN_DIFF, GSPECIFICATION] >> DECIDE_TAC)
   >> POP_ORW
   >> `{w | w IN m_space m /\ (f w = g w)} IN measurable_sets m`
        by RW_TAC std_ss [borel_measurable_eq_borel_measurable]
   >> FULL_SIMP_TAC std_ss [measure_space_def, SIGMA_ALGEBRA, subsets_def, space_def]);

val sigma_algebra_borel = store_thm
  ("sigma_algebra_borel", ``sigma_algebra borel``,
   RW_TAC std_ss [borel_def]
   >> MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA
   >> RW_TAC std_ss [subset_class_def, IN_UNIV, IN_IMAGE, SUBSET_DEF]);

val borel_measurable_plus_borel_measurable = store_thm
  ("borel_measurable_plus_borel_measurable",
   ``!m f g. measure_space m /\
             f IN borel_measurable (m_space m, measurable_sets m) /\
             g IN borel_measurable (m_space m, measurable_sets m) ==>
             (\x. f x + g x) IN borel_measurable (m_space m, measurable_sets m)``,
   rpt STRIP_TAC
   >> `!a. {w | w IN m_space m /\ a <= f w + g w} =
           {w | w IN m_space m /\ a + (g w) * (~1) <= f w}`
        by RW_TAC real_ss [Once EXTENSION, GSPECIFICATION, GSYM real_sub, REAL_LE_SUB_RADD]
   >> `!a. (\w. a + (g w) * (~1)) IN borel_measurable (m_space m, measurable_sets m)`
        by RW_TAC std_ss [affine_borel_measurable]
   >> `!a. {w | w IN m_space m /\ (\w. a + (g w)*(~1)) w <= f w} IN measurable_sets m`
        by RW_TAC std_ss [borel_measurable_leq_borel_measurable]
   >> `!a. {w | w IN m_space m /\ a <= f w + g w} IN measurable_sets m`
        by FULL_SIMP_TAC std_ss []
   >> RW_TAC bool_ss [borel_measurable_ge_iff]);

val borel_measurable_square = store_thm
  ("borel_measurable_square",
   ``!m f g. measure_space m /\
             f IN borel_measurable (m_space m, measurable_sets m) ==>
                (\x. (f x) pow 2) IN borel_measurable (m_space m, measurable_sets m)``,
   rpt STRIP_TAC
   >> RW_TAC std_ss [borel_measurable_le_iff]
   >> `!a. 0 <= a pow 2`
        by (STRIP_TAC
            >> Cases_on `a = 0` >- RW_TAC real_ss [POW_0]
            >> RW_TAC bool_ss [Once (GSYM REAL_POW2_ABS)]
            >> `0 < abs (a)` by METIS_TAC [REAL_LT_LE, REAL_ABS_POS, ABS_ZERO]
            >> METIS_TAC [REAL_POW_LT, REAL_LT_IMP_LE])
   >> `!a. (a pow 2 = 0) = (a = 0)`
        by (STRIP_TAC >> EQ_TAC >> RW_TAC real_ss [POW_0]
            >> POP_ASSUM MP_TAC >> RW_TAC bool_ss [Once (GSYM REAL_POW2_ABS)]
            >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
            >> `0 < abs a` by METIS_TAC [REAL_LT_LE, REAL_ABS_POS, ABS_ZERO]
            >> (MP_TAC o Q.SPECL [`2`,`0`, `abs a`]) REAL_POW_LT2
            >> RW_TAC real_ss [POW_0])
   >> Cases_on `a < 0`
   >- (`{x | x IN m_space m /\ f x pow 2 <= a} = {}`
        by (RW_TAC std_ss [Once EXTENSION, NOT_IN_EMPTY, GSPECIFICATION]
            >> Reverse (Cases_on `(x IN m_space m)`) >> RW_TAC std_ss []
            >> RW_TAC std_ss [GSYM real_lt] >> MATCH_MP_TAC REAL_LTE_TRANS >> Q.EXISTS_TAC `0`
            >> RW_TAC std_ss [])
       >> FULL_SIMP_TAC std_ss [measure_space_def, SIGMA_ALGEBRA, subsets_def])
   >> Cases_on `a = 0`
   >- (ASM_REWRITE_TAC []
       >> `{x | x IN m_space m /\ f x pow 2 <= 0} =
           {x | x IN m_space m /\ f x <= 0} INTER
           {x | x IN m_space m /\ 0 <= f x}`
        by (RW_TAC std_ss [Once EXTENSION, IN_INTER, GSPECIFICATION]
            >> METIS_TAC [REAL_LE_ANTISYM])
        >> POP_ORW
        >> `{x | x IN m_space m /\ f x <= 0} IN measurable_sets m /\
            {x | x IN m_space m /\ 0 <= f x} IN measurable_sets m`
                by METIS_TAC [borel_measurable_le_iff, borel_measurable_ge_iff]
        >> `measurable_sets m = subsets (m_space m, measurable_sets m)` by RW_TAC std_ss [subsets_def]
        >> POP_ORW >> MATCH_MP_TAC ALGEBRA_INTER
        >> FULL_SIMP_TAC std_ss [subsets_def, measure_space_def, sigma_algebra_def])
   >> `0 < a` by METIS_TAC [REAL_LT_TOTAL]
   >> `!b. 0 < b ==> ?q. 0 < q /\ (q pow 2 = b)`
        by METIS_TAC [SQRT_POS_LT, SQRT_POW_2, REAL_LT_IMP_LE]
   >> POP_ASSUM (MP_TAC o Q.SPEC `a`) >> RW_TAC std_ss []
   >> `!x. (f x pow 2 <= q pow 2) =
           (~ q <= f x /\ f x <= q)`
        by (STRIP_TAC >> RW_TAC bool_ss [Once (GSYM REAL_POW2_ABS)]
            >> ONCE_REWRITE_TAC [GSYM ABS_BOUNDS]
            >> RW_TAC std_ss [GSYM REAL_NOT_LT]
            >> Reverse EQ_TAC
            >- (STRIP_TAC >> MATCH_MP_TAC REAL_POW_LT2 >> RW_TAC real_ss [REAL_LT_IMP_LE])
            >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
            >> POP_ASSUM MP_TAC
            >> RW_TAC std_ss [REAL_LT_LE]
            >- (SIMP_TAC std_ss [GSYM REAL_NOT_LT] >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
                >> (MP_TAC o Q.SPECL [`2`, `abs (f x)`, `q`]) REAL_POW_LT2
                >> RW_TAC real_ss [REAL_ABS_POS]
                >> METIS_TAC [REAL_LT_ANTISYM])
            >> METIS_TAC [REAL_LT_ANTISYM])
   >> POP_ORW
   >> `{x | x IN m_space m /\ ~q <= f x /\ f x <= q} =
       {x | x IN m_space m /\ ~q <= f x} INTER
       {x | x IN m_space m /\ f x <= q}`
        by (RW_TAC std_ss [Once EXTENSION, IN_INTER, GSPECIFICATION]
            >> METIS_TAC [REAL_LE_ANTISYM])
   >>  POP_ORW
   >> `{x | x IN m_space m /\ ~q <= f x} IN measurable_sets m /\
       {x | x IN m_space m /\ f x <= q} IN measurable_sets m`
                by METIS_TAC [borel_measurable_le_iff, borel_measurable_ge_iff]
   >> `measurable_sets m = subsets (m_space m, measurable_sets m)` by RW_TAC std_ss [subsets_def]
   >> POP_ORW >> MATCH_MP_TAC ALGEBRA_INTER
   >> FULL_SIMP_TAC std_ss [subsets_def, measure_space_def, sigma_algebra_def]);

val pow2_binomial = prove
  (``!(f:real) g. (f+g) pow 2 = f pow 2 + 2 * (f*g) + g pow 2``,
   RW_TAC std_ss [POW_2, REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB] >> REAL_ARITH_TAC);

val times_eq_sum_squares = prove
  (``!(f:real) g. f*g = ((f+g) pow 2)/4 - ((f-g)pow 2)/4``,
   RW_TAC std_ss [real_sub, pow2_binomial, real_div, REAL_MUL_RNEG]
   >> `~g pow 2 = g pow 2` by METIS_TAC [GSYM REAL_POW2_ABS, ABS_NEG]
   >> POP_ORW
   >> Q.ABBREV_TAC `a = f * g` >> Q.ABBREV_TAC `b = f pow 2` >> Q.ABBREV_TAC `c = g pow 2`
   >> ONCE_REWRITE_TAC [GSYM REAL_MUL_LNEG]
   >> ONCE_REWRITE_TAC [GSYM REAL_ADD_RDISTRIB]
   >> ONCE_REWRITE_TAC [GSYM real_div]
   >> (MP_TAC o Q.SPECL [`a`, `(b + 2 * a + c + ~(b + ~(2 * a) + c))`, `4`]) REAL_EQ_RDIV_EQ
   >> RW_TAC real_ss [GSYM real_sub]
   >> REAL_ARITH_TAC);

val borel_measurable_times_borel_measurable = store_thm
  ("borel_measurable_times_borel_measurable",
   ``!m f g. measure_space m /\
             f IN borel_measurable (m_space m, measurable_sets m) /\
             g IN borel_measurable (m_space m, measurable_sets m) ==>
             (\x. f x * g x) IN borel_measurable (m_space m, measurable_sets m)``,
   rpt STRIP_TAC
   >> `(\x. f x * g x) = (\x. ((f x + g x) pow 2)/4 - ((f x - g x) pow 2)/4)`
        by RW_TAC std_ss [times_eq_sum_squares]
   >> POP_ORW
   >> RW_TAC bool_ss [real_div, real_sub]
   >> Suff `(\x. (f x + g x) pow 2 * inv 4) IN borel_measurable (m_space m,measurable_sets m) /\
            (\x. ~((f x + ~g x) pow 2 * inv 4)) IN borel_measurable (m_space m,measurable_sets m)`
   >- RW_TAC std_ss [borel_measurable_plus_borel_measurable]
   >> ONCE_REWRITE_TAC [GSYM REAL_ADD_LID]
   >> CONJ_TAC >- METIS_TAC [affine_borel_measurable, borel_measurable_square, borel_measurable_plus_borel_measurable]
   >> ONCE_REWRITE_TAC [GSYM REAL_MUL_RNEG]
   >> Suff `(\x. ~ g x) IN borel_measurable (m_space m,measurable_sets m)`
   >- METIS_TAC [affine_borel_measurable, borel_measurable_square, borel_measurable_plus_borel_measurable]
   >> `!x. ~ g x = 0 + (g x) * ~1` by RW_TAC real_ss []
   >> POP_ORW
   >> RW_TAC std_ss [affine_borel_measurable]);

val borel_measurable_sub_borel_measurable = store_thm
  ("borel_measurable_sub_borel_measurable",
   ``!m f g. measure_space m /\
             f IN borel_measurable (m_space m, measurable_sets m) /\
             g IN borel_measurable (m_space m, measurable_sets m) ==>
             (\x. f x - g x) IN borel_measurable (m_space m, measurable_sets m)``,
   RW_TAC bool_ss [real_sub]
   >> Suff `(\x. ~ g x) IN borel_measurable (m_space m,measurable_sets m)`
   >- METIS_TAC [borel_measurable_plus_borel_measurable]
   >> `!x. ~ g x = 0 + (g x) * ~1` by RW_TAC real_ss []
   >> POP_ORW
   >> RW_TAC std_ss [affine_borel_measurable]);

val mono_convergent_borel_measurable = store_thm
  ("mono_convergent_borel_measurable",
   ``!u m f. measure_space m /\ (!n. u n IN borel_measurable (m_space m, measurable_sets m)) /\
             mono_convergent u f (m_space m) ==>
                f IN borel_measurable (m_space m, measurable_sets m)``,
   rpt STRIP_TAC
   >> RW_TAC std_ss [borel_measurable_le_iff]
   >> `!w. w IN m_space m /\ f w <= a <=> w IN m_space m /\ !i. u i w <= a`
        by (FULL_SIMP_TAC std_ss [mono_convergent_def] >> STRIP_TAC >> EQ_TAC
            >- (RW_TAC std_ss [] >> MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `f w`
                >> ASM_REWRITE_TAC [] >> `u i w = (\i. u i w) i` by SIMP_TAC std_ss [] >> POP_ORW
                >> MATCH_MP_TAC SEQ_MONO_LE >> RW_TAC arith_ss [])
            >> RW_TAC std_ss [] >> MATCH_MP_TAC SEQ_LE_IMP_LIM_LE
            >> Q.EXISTS_TAC `(\i. u i w)` >> RW_TAC std_ss [])
   >> POP_ORW
   >> `{w: 'a | w IN m_space m /\ !i:num. (u :num -> 'a -> real) i w <= (a:real)} =
        (m_space m) DIFF
        (BIGUNION (IMAGE (\i. (m_space m) DIFF
                              {w | w IN m_space m /\ (u :num -> 'a -> real) i w <= (a:real)})
                  (UNIV:num->bool)))`
        by (RW_TAC std_ss [Once EXTENSION, GSPECIFICATION, IN_DIFF, IN_BIGUNION_IMAGE, IN_UNIV]
            >> METIS_TAC [])
   >> POP_ORW
   >> `sigma_algebra (m_space m, measurable_sets m)` by FULL_SIMP_TAC std_ss [measure_space_def]
   >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, space_def, subsets_def]
   >> Suff `(BIGUNION (IMAGE (\i. (m_space m) DIFF
                              {w | w IN m_space m /\ (u :num -> 'a -> real) i w <= (a:real)})
                  (UNIV:num->bool))) IN measurable_sets m`
   >- RW_TAC std_ss []
   >> Q.PAT_X_ASSUM `!c. P c ==> BIGUNION c IN measurable_sets m` MATCH_MP_TAC
   >> RW_TAC std_ss [image_countable, COUNTABLE_NUM, SUBSET_DEF, IN_IMAGE, IN_UNIV]
   >> POP_ASSUM MATCH_MP_TAC
   >> METIS_TAC [borel_measurable_le_iff]);

val borel_measurable_SIGMA_borel_measurable = store_thm
  ("borel_measurable_SIGMA_borel_measurable",
   ``!m f s. measure_space m /\ FINITE s /\
           (!i. i IN s ==> f i IN borel_measurable (m_space m, measurable_sets m)) ==>
           (\x. SIGMA (\i. f i x) s) IN borel_measurable (m_space m, measurable_sets m)``,
   rpt STRIP_TAC
   >> Suff `!s. FINITE s ==> (\s. !f. (!i. i IN s ==> f i IN borel_measurable (m_space m, measurable_sets m)) ==>
           (\x. SIGMA (\i. f i x) s) IN borel_measurable (m_space m, measurable_sets m)) s`
   >- METIS_TAC []
   >> MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC std_ss [REAL_SUM_IMAGE_THM, IN_INSERT, DELETE_NON_ELEMENT]
   >- FULL_SIMP_TAC std_ss [measure_space_def, borel_measurable_const]
   >> METIS_TAC [borel_measurable_plus_borel_measurable]);

val _ = export_theory ();
