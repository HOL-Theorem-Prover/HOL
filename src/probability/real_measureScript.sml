(* ------------------------------------------------------------------------- *)
(* Measure Theory defined on the positive reals [0, PosInf)                  *)
(* Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar                         *)
(* HVG Group, Concordia University, Montreal                                 *)
(* ------------------------------------------------------------------------- *)
(* Based on the work of Aaron Coble (and Joe Hurd), Cambridge University     *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib arithmeticTheory realTheory
     seqTheory pred_setTheory res_quanTheory res_quanTools listTheory transcTheory
     rich_listTheory pairTheory combinTheory realLib optionTheory
     real_sigmaTheory iterateTheory;

open hurdUtils util_probTheory sigma_algebraTheory real_borelTheory;

val _ = new_theory "real_measure";

(* ------------------------------------------------------------------------- *)
(* Basic measure theory definitions.                                         *)
(* ------------------------------------------------------------------------- *)

Type measure = “:'a set -> real”
Type m_space = “:'a set # 'a set set # 'a measure”

val m_space_def = Define
   `m_space (sp:'a->bool, sts:('a->bool)->bool, mu:('a->bool)->real) = sp`;

val measurable_sets_def = Define
   `measurable_sets (sp:'a->bool, sts:('a->bool)->bool, mu:('a->bool)->real) = sts`;

val _ = hide "measure"; (* prim_recTheory *)
val measure_def = Define
   `measure (sp:'a->bool, sts:('a->bool)->bool, mu:('a->bool)->real) = mu`;

val positive_def = Define
   `positive m <=>
    (measure m {} = 0) /\ !s. s IN measurable_sets m ==> 0 <= measure m s`;

val additive_def = Define
   `additive m <=>
    !s t. s IN measurable_sets m /\ t IN measurable_sets m /\ DISJOINT s t ==>
         (measure m (s UNION t) = measure m s + measure m t)`;

val countably_additive_def = Define
   `countably_additive m <=>
    !f : num -> ('a -> bool).
     f IN (UNIV -> measurable_sets m) /\
     (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
     BIGUNION (IMAGE f UNIV) IN measurable_sets m ==>
     (measure m o f) sums measure m (BIGUNION (IMAGE f UNIV))`;

val subadditive_def = Define
   `subadditive m <=>
    !s t.
     s IN measurable_sets m /\ t IN measurable_sets m ==>
     measure m (s UNION t) <= measure m s + measure m t`;

val countably_subadditive_def = Define
   `countably_subadditive m <=>
    !f : num -> ('a -> bool).
     f IN (UNIV -> measurable_sets m) /\
     BIGUNION (IMAGE f UNIV) IN measurable_sets m /\
     summable (measure m o f) ==>
     measure m (BIGUNION (IMAGE f UNIV)) <= suminf (measure m o f)`;

val increasing_def = Define
   `increasing m <=>
    !s t.
     s IN measurable_sets m /\ t IN measurable_sets m /\ s SUBSET t ==>
     measure m s <= measure m t`;

val measure_space_def = Define
   `measure_space m <=>
    sigma_algebra (m_space m, measurable_sets m) /\ positive m /\ countably_additive m`;

val lambda_system_def = Define
  `lambda_system gen (lam : ('a -> bool) -> real) =
   {l |
    l IN (subsets gen) /\
    !s. s IN (subsets gen) ==> (lam (l INTER s) + lam ((space gen DIFF l) INTER s) = lam s)}`;

val outer_measure_space_def = Define
   `outer_measure_space m <=> positive m /\ increasing m /\ countably_subadditive m`;

val inf_measure_def = Define
   `inf_measure m s =
    inf
    {r | ?f. f IN (UNIV -> measurable_sets m) /\
            (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
             s SUBSET BIGUNION (IMAGE f UNIV) /\ ((measure m o f) sums r)}`;

val closed_cdi_def = Define
   `closed_cdi p <=>
    subset_class (space p) (subsets p) /\
     (!s. s IN (subsets p) ==> (space p DIFF s) IN (subsets p)) /\
     (!f : num -> 'a -> bool.
        f IN (UNIV -> (subsets p)) /\ (f 0 = {}) /\ (!n. f n SUBSET f (SUC n)) ==>
        BIGUNION (IMAGE f UNIV) IN (subsets p)) /\
     (!f : num -> 'a -> bool.
        f IN (UNIV -> (subsets p)) /\ (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
        BIGUNION (IMAGE f UNIV) IN (subsets p))`;

val smallest_closed_cdi_def = Define
   `smallest_closed_cdi a =
     (space a, BIGINTER {b | (subsets a) SUBSET b /\ closed_cdi (space a, b)})`;

(* NOTE: removed `measure_space m1 /\ measure_space m2` to allow possible usage of
  `measure_preserving` on pseudo-measure spaces.

   This is also aligned with `measureTheory.measure_preserving_def`.
 *)
val measure_preserving_def = Define
   `measure_preserving m1 m2 =
    {f |
     f IN measurable (m_space m1, measurable_sets m1) (m_space m2, measurable_sets m2) /\
     !s.
      s IN measurable_sets m2 ==>
           (measure m1 ((PREIMAGE f s)INTER(m_space m1)) = measure m2 s)}`;

val mono_convergent_def = Define
   `mono_convergent u f s <=>
        (!x m n. m <= n /\ x IN s ==> u m x <= u n x) /\
        (!x. x IN s ==> (\i. u i x) --> f x)`;

(* ------------------------------------------------------------------------- *)
(* Basic measure theory theorems                                             *)
(* ------------------------------------------------------------------------- *)

val LAMBDA_SYSTEM_EMPTY = store_thm
  ("LAMBDA_SYSTEM_EMPTY",
  ``!g0 lam. algebra g0 /\ positive (space g0, subsets g0, lam) ==> {} IN lambda_system g0 lam``,
    RW_TAC real_ss [lambda_system_def, GSPECIFICATION, positive_def,
                    INTER_EMPTY, DIFF_EMPTY, ALGEBRA_INTER_SPACE, measure_def]
 >> FULL_SIMP_TAC std_ss [algebra_def]);

val LAMBDA_SYSTEM_COMPL = store_thm
  ("LAMBDA_SYSTEM_COMPL",
   ``!g0 lam l.
       algebra g0 /\ positive (space g0, subsets g0, lam) /\ l IN lambda_system g0 lam ==>
       (space g0) DIFF l IN lambda_system g0 lam``,
   RW_TAC real_ss [lambda_system_def, GSPECIFICATION, positive_def]
   >- PROVE_TAC [algebra_def, subset_class_def]
   >> Know `(space g0 DIFF (space g0 DIFF l)) = l`
   >- (RW_TAC std_ss [Once EXTENSION, IN_DIFF, LEFT_AND_OVER_OR] >> PROVE_TAC [algebra_def, subset_class_def, SUBSET_DEF])
   >> RW_TAC std_ss []
   >> PROVE_TAC [REAL_ADD_SYM]);

val LAMBDA_SYSTEM_INTER = store_thm
  ("LAMBDA_SYSTEM_INTER",
   ``!g0 lam l1 l2.
       algebra g0 /\ positive (space g0, subsets g0, lam) /\
       l1 IN lambda_system g0 lam /\ l2 IN lambda_system g0 lam ==>
       (l1 INTER l2) IN lambda_system g0 lam``,
   RW_TAC real_ss [lambda_system_def, GSPECIFICATION, positive_def]
   >- PROVE_TAC [ALGEBRA_ALT_INTER]
   >> Know
      `lam ((space g0 DIFF (l1 INTER l2)) INTER s) =
       lam (l2 INTER (space g0 DIFF l1) INTER s) + lam ((space g0 DIFF l2) INTER s)`
   >- (ONCE_REWRITE_TAC [EQ_SYM_EQ]
       >> Know
          `l2 INTER (space g0 DIFF l1) INTER s = l2 INTER ((space g0 DIFF (l1 INTER l2)) INTER s)`
       >- (RW_TAC std_ss [EXTENSION, IN_INTER, IN_DIFF]
           >> PROVE_TAC [])
       >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
       >> Know `(space g0 DIFF l2) INTER s = (space g0 DIFF l2) INTER ((space g0 DIFF (l1 INTER l2)) INTER s)`
       >- (RW_TAC std_ss [EXTENSION, IN_INTER, IN_DIFF]
           >> PROVE_TAC [])
       >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
       >> Q.PAT_X_ASSUM `!g. P g` MATCH_MP_TAC
       >> PROVE_TAC [ALGEBRA_ALT_INTER])
   >> Know `lam (l2 INTER s) + lam ((space g0 DIFF l2) INTER s) = lam s`
   >- PROVE_TAC []
   >> Know
      `lam (l1 INTER l2 INTER s) + lam (l2 INTER (space g0 DIFF l1) INTER s) =
       lam (l2 INTER s)`
   >- (Know `l2 INTER (space g0 DIFF l1) INTER s = (space g0 DIFF l1) INTER (l2 INTER s)`
       >- (RW_TAC std_ss [EXTENSION, IN_INTER, IN_DIFF]
           >> PROVE_TAC [])
       >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
       >> REWRITE_TAC [GSYM INTER_ASSOC]
       >> Q.PAT_X_ASSUM `!g. P g` K_TAC
       >> Q.PAT_X_ASSUM `!g. P g` MATCH_MP_TAC
       >> PROVE_TAC [ALGEBRA_ALT_INTER])
   >> Q.SPEC_TAC (`l1 INTER l2`, `l`)
   >> GEN_TAC
   >> Q.SPEC_TAC (`lam (l2 INTER (space g0 DIFF l1) INTER s)`, `r1`)
   >> Q.SPEC_TAC (`lam (l INTER s)`, `r2`)
   >> Q.SPEC_TAC (`lam ((space g0 DIFF l2) INTER s)`, `r3`)
   >> Q.SPEC_TAC (`lam (l2 INTER s)`, `r4`)
   >> Q.SPEC_TAC (`lam s`, `r5`)
   >> Q.SPEC_TAC (`lam ((space g0 DIFF l) INTER s)`, `r6`)
   >> KILL_TAC
   >> REAL_ARITH_TAC);

val LAMBDA_SYSTEM_ALGEBRA = store_thm
  ("LAMBDA_SYSTEM_ALGEBRA",
   ``!g0 lam.
       algebra g0 /\ positive (space g0, subsets g0, lam)
       ==> algebra (space g0, lambda_system g0 lam)``,
   RW_TAC std_ss [ALGEBRA_ALT_INTER, LAMBDA_SYSTEM_EMPTY, positive_def,
                  LAMBDA_SYSTEM_COMPL, LAMBDA_SYSTEM_INTER, space_def,
                  subsets_def, subset_class_def]
   >> FULL_SIMP_TAC std_ss [lambda_system_def, GSPECIFICATION]);

val LAMBDA_SYSTEM_STRONG_ADDITIVE = store_thm
  ("LAMBDA_SYSTEM_STRONG_ADDITIVE",
   ``!g0 lam g l1 l2.
       algebra g0 /\ positive (space g0, subsets g0, lam) /\ g IN (subsets g0) /\ DISJOINT l1 l2 /\
       l1 IN lambda_system g0 lam /\ l2 IN lambda_system g0 lam ==>
       (lam ((l1 UNION l2) INTER g) = lam (l1 INTER g) + lam (l2 INTER g))``,
   RW_TAC std_ss [positive_def]
   >> Know `l1 INTER g = l1 INTER ((l1 UNION l2) INTER g)`
   >- (RW_TAC std_ss [EXTENSION, IN_INTER, IN_UNION]
       >> PROVE_TAC [])
   >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   >> Know `l2 INTER g = (space g0 DIFF l1) INTER ((l1 UNION l2) INTER g)`
   >- (Q.PAT_X_ASSUM `DISJOINT x y` MP_TAC
       >> RW_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF, DISJOINT_DEF,
                         NOT_IN_EMPTY]
       >> PROVE_TAC [algebra_def, SUBSET_DEF, subset_class_def])
   >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   >> Know `(l1 UNION l2) INTER g IN (subsets g0)`
   >- (Suff `l1 IN (subsets g0) /\ l2 IN (subsets g0)`
       >- PROVE_TAC [algebra_def, SUBSET_DEF, ALGEBRA_ALT_INTER, subset_class_def]
       >> rpt (POP_ASSUM MP_TAC)
       >> RW_TAC std_ss [lambda_system_def, GSPECIFICATION])
   >> STRIP_TAC
   >> Q.PAT_X_ASSUM `l1 IN x` MP_TAC
   >> RW_TAC std_ss [lambda_system_def, GSPECIFICATION]);

val LAMBDA_SYSTEM_ADDITIVE = store_thm
  ("LAMBDA_SYSTEM_ADDITIVE",
   ``!g0 lam l1 l2.
       algebra g0 /\ positive (space g0, subsets g0, lam) ==>
       additive (space g0, lambda_system g0 lam, lam)``,
   RW_TAC std_ss [additive_def, measure_def, measurable_sets_def]
   >> MP_TAC (Q.SPECL [`g0`, `lam`, `space g0`, `s`, `t`]
              LAMBDA_SYSTEM_STRONG_ADDITIVE)
   >> FULL_SIMP_TAC std_ss [lambda_system_def, GSPECIFICATION, ALGEBRA_INTER_SPACE,
                            ALGEBRA_SPACE, ALGEBRA_UNION]);

val COUNTABLY_SUBADDITIVE_SUBADDITIVE = store_thm
  ("COUNTABLY_SUBADDITIVE_SUBADDITIVE",
   ``!m.
       algebra (m_space m, measurable_sets m) /\ positive m /\ countably_subadditive m ==>
       subadditive m``,
   RW_TAC std_ss [countably_subadditive_def, subadditive_def]
   >> Q.PAT_X_ASSUM `!f. P f`
      (MP_TAC o Q.SPEC `\n : num. if n = 0 then s else if n = 1 then t else {}`)
   >> Know
      `BIGUNION
       (IMAGE (\n : num. (if n = 0 then s else (if n = 1 then t else {})))
        UNIV) =
       s UNION t`
   >- (Suff
       `IMAGE (\n : num. (if n = 0 then s else (if n = 1 then t else {})))
        UNIV =
        {s; t; {}}`
       >- (RW_TAC std_ss [BIGUNION, EXTENSION, IN_INSERT, GSPECIFICATION]
           >> RW_TAC std_ss [GSYM EXTENSION]
           >> RW_TAC std_ss [NOT_IN_EMPTY, IN_UNION]
           >> PROVE_TAC [NOT_IN_EMPTY])
       >> RW_TAC arith_ss [EXTENSION, IN_IMAGE, IN_INSERT, IN_UNIV]
       >> RW_TAC std_ss [GSYM EXTENSION]
       >> RW_TAC std_ss [NOT_IN_EMPTY]
       >> KILL_TAC
       >> EQ_TAC >- PROVE_TAC []
       >> Know `~(0:num = 1) /\ ~(0:num = 2) /\ ~(1:num = 2)` >- DECIDE_TAC
       >> PROVE_TAC [])
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> Know
      `(measure m o (\n. (if n = 0 then s else (if n = 1 then t else {})))) sums
       (measure m s + measure m t)`
   >- (Know
       `measure m s + measure m t =
        sum (0,2)
        (measure m o (\n. (if n = 0 then s else (if n = 1 then t else {}))))`
       >- (ASM_SIMP_TAC bool_ss [TWO, sum, ONE, o_DEF]
           >> RW_TAC arith_ss []
           >> RW_TAC real_ss [])
       >> DISCH_THEN (REWRITE_TAC o wrap)
       >> MATCH_MP_TAC SER_0
       >> RW_TAC arith_ss [o_DEF]
       >> PROVE_TAC [positive_def])
   >> REWRITE_TAC [SUMS_EQ]
   >> DISCH_THEN (REWRITE_TAC o CONJUNCTS)
   >> DISCH_THEN MATCH_MP_TAC
   >> CONJ_TAC
   >- (Q.PAT_X_ASSUM `algebra a` MP_TAC
       >> BasicProvers.NORM_TAC std_ss [IN_FUNSET, IN_UNIV, algebra_def, subsets_def, subset_class_def])
   >> PROVE_TAC [algebra_def, subsets_def, subset_class_def]);

val SUBADDITIVE = store_thm
  ("SUBADDITIVE",
   ``!m s t u.
       subadditive m /\ s IN measurable_sets m /\ t IN measurable_sets m /\
       (u = s UNION t) ==>
       measure m u <= measure m s + measure m t``,
   RW_TAC std_ss [subadditive_def]);

val ADDITIVE = store_thm
  ("ADDITIVE",
   ``!m s t u.
       additive m /\ s IN measurable_sets m /\ t IN measurable_sets m /\
       DISJOINT s t /\ (u = s UNION t) ==>
       (measure m u = measure m s + measure m t)``,
   RW_TAC std_ss [additive_def]);

val COUNTABLY_SUBADDITIVE = store_thm
  ("COUNTABLY_SUBADDITIVE",
   ``!m f s.
       countably_subadditive m /\ f IN (UNIV -> measurable_sets m) /\
       summable (measure m o f) /\ (s = BIGUNION (IMAGE f UNIV)) /\
       (s IN measurable_sets m) ==>
       measure m s <= suminf (measure m o f)``,
   PROVE_TAC [countably_subadditive_def]);

val ADDITIVE_SUM = store_thm
  ("ADDITIVE_SUM",
   ``!m f n.
       algebra (m_space m, measurable_sets m) /\ positive m /\ additive m /\
       f IN (UNIV -> measurable_sets m) /\
       (!m n : num. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
       (sum (0, n) (measure m o f) =
        measure m (BIGUNION (IMAGE f (count n))))``,
   RW_TAC std_ss [IN_FUNSET, IN_UNIV]
   >> Induct_on `n`
   >- (RW_TAC std_ss [sum, COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY]
       >> PROVE_TAC [positive_def])
   >> RW_TAC std_ss [sum, COUNT_SUC, IMAGE_INSERT, BIGUNION_INSERT, ADD_CLAUSES,
                     o_DEF]
   >> MATCH_MP_TAC EQ_SYM
   >> ONCE_REWRITE_TAC [REAL_ADD_SYM]
   >> MATCH_MP_TAC ADDITIVE
   >> RW_TAC std_ss [DISJOINT_COUNT]
   >> MATCH_MP_TAC ((REWRITE_RULE [subsets_def] o Q.SPEC `(m_space m,measurable_sets m)`) ALGEBRA_FINITE_UNION)
   >> RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT]
   >> PROVE_TAC [FINITE_COUNT, IMAGE_FINITE]);

val INCREASING_ADDITIVE_SUMMABLE = store_thm
  ("INCREASING_ADDITIVE_SUMMABLE",
   ``!m f.
       algebra (m_space m, measurable_sets m) /\ positive m /\ increasing m /\
       additive m /\ f IN (UNIV -> measurable_sets m) /\
       (!m n : num. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
       summable (measure m o f)``,
   RW_TAC std_ss [increasing_def]
   >> MATCH_MP_TAC POS_SUMMABLE
   >> CONJ_TAC
   >- FULL_SIMP_TAC std_ss [o_DEF, IN_FUNSET, IN_UNIV, positive_def]
   >> Q.EXISTS_TAC `measure m (m_space m)`
   >> RW_TAC std_ss []
   >> MP_TAC (Q.SPECL [`m`, `f`, `n`] ADDITIVE_SUM)
   >> ASM_REWRITE_TAC []
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> Q.PAT_X_ASSUM `!(s : 'a -> bool). P s` MATCH_MP_TAC
   >> CONJ_TAC
   >- (MATCH_MP_TAC ((REWRITE_RULE [subsets_def] o Q.SPEC `(m_space m,measurable_sets m)`) ALGEBRA_FINITE_UNION)
       >> Q.PAT_X_ASSUM `f IN x` MP_TAC
       >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, SUBSET_DEF, IN_IMAGE]
       >> PROVE_TAC [IMAGE_FINITE, FINITE_COUNT])
   >> CONJ_TAC >- PROVE_TAC [ALGEBRA_SPACE, space_def, subsets_def]
   >> Q.PAT_X_ASSUM `f IN x` MP_TAC
   >> Q.PAT_X_ASSUM `algebra a` MP_TAC
   >> RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE, IN_COUNT,
                     IN_FUNSET, IN_UNIV, algebra_def, space_def, subsets_def, subset_class_def]
   >> PROVE_TAC []);

val LAMBDA_SYSTEM_POSITIVE = store_thm
  ("LAMBDA_SYSTEM_POSITIVE",
   ``!g0 lam. positive (space g0, subsets g0, lam) ==> positive (space g0, lambda_system g0 lam, lam)``,
   RW_TAC std_ss [positive_def, lambda_system_def, GSPECIFICATION,
                  measure_def, measurable_sets_def]);

val LAMBDA_SYSTEM_INCREASING = store_thm
  ("LAMBDA_SYSTEM_INCREASING",
   ``!g0 lam. increasing (space g0, subsets g0, lam) ==> increasing (space g0, lambda_system g0 lam, lam)``,
   RW_TAC std_ss [increasing_def, lambda_system_def, GSPECIFICATION,
                  measure_def, measurable_sets_def]);

val LAMBDA_SYSTEM_STRONG_SUM = store_thm
  ("LAMBDA_SYSTEM_STRONG_SUM",
   ``!g0 lam g f n.
       algebra g0 /\ positive (space g0, subsets g0, lam) /\ g IN (subsets g0) /\
       f IN (UNIV -> lambda_system g0 lam) /\
       (!m n : num. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
       (sum (0, n) (lam o (\s. s INTER g) o f) =
        lam (BIGUNION (IMAGE f (count n)) INTER g))``,
   RW_TAC std_ss [IN_FUNSET, IN_UNIV]
   >> Induct_on `n`
   >- (RW_TAC std_ss [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY, sum, INTER_EMPTY]
       >> PROVE_TAC [positive_def, measure_def])
   >> RW_TAC arith_ss [COUNT_SUC, IMAGE_INSERT, BIGUNION_INSERT, sum, o_DEF]
   >> ONCE_REWRITE_TAC [REAL_ADD_SYM]
   >> MATCH_MP_TAC EQ_SYM
   >> MATCH_MP_TAC LAMBDA_SYSTEM_STRONG_ADDITIVE
   >> Q.EXISTS_TAC `g0`
   >> RW_TAC std_ss [DISJOINT_COUNT]
   >> MATCH_MP_TAC ((REWRITE_RULE [subsets_def] o Q.SPEC `(space g0,lambda_system g0 lam)`) ALGEBRA_FINITE_UNION)
   >> RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, LAMBDA_SYSTEM_ALGEBRA]
   >> PROVE_TAC [IMAGE_FINITE, FINITE_COUNT]);

val OUTER_MEASURE_SPACE_POSITIVE = store_thm
  ("OUTER_MEASURE_SPACE_POSITIVE",
   ``!m. outer_measure_space m ==> positive m``,
   PROVE_TAC [outer_measure_space_def]);

val LAMBDA_SYSTEM_CARATHEODORY = store_thm
  ("LAMBDA_SYSTEM_CARATHEODORY",
   ``!gsig lam.
       sigma_algebra gsig /\ outer_measure_space (space gsig, subsets gsig, lam) ==>
       (!f.
          f IN (UNIV -> lambda_system gsig lam) /\
          (!m n : num. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
          BIGUNION (IMAGE f UNIV) IN lambda_system gsig lam /\
          ((lam o f) sums lam (BIGUNION (IMAGE f UNIV))))``,
   NTAC 5 STRIP_TAC
   >> Know `summable (lam o f)`
   >- (Suff `summable (measure (space gsig, lambda_system gsig lam, lam) o f)`
       >- RW_TAC std_ss [measure_def]
       >> MATCH_MP_TAC INCREASING_ADDITIVE_SUMMABLE
       >> REWRITE_TAC [measurable_sets_def, m_space_def]
       >> CONJ_TAC
       >- (MATCH_MP_TAC LAMBDA_SYSTEM_ALGEBRA
           >> CONJ_TAC >- PROVE_TAC [sigma_algebra_def]
           >> PROVE_TAC [outer_measure_space_def])
       >> CONJ_TAC
       >- PROVE_TAC [LAMBDA_SYSTEM_POSITIVE, outer_measure_space_def]
       >> CONJ_TAC
       >- PROVE_TAC [LAMBDA_SYSTEM_INCREASING, outer_measure_space_def]
       >> CONJ_TAC
       >- PROVE_TAC [LAMBDA_SYSTEM_ADDITIVE, outer_measure_space_def,
                     sigma_algebra_def]
       >> RW_TAC std_ss [])
   >> STRIP_TAC
   >> Know `BIGUNION (IMAGE f UNIV) IN subsets gsig`
   >- (Q.PAT_X_ASSUM `sigma_algebra a` MP_TAC
       >> Q.PAT_X_ASSUM `f IN s` MP_TAC
       >> RW_TAC std_ss [SIGMA_ALGEBRA_ALT, IN_FUNSET, IN_UNIV]
       >> POP_ASSUM MATCH_MP_TAC
       >> RW_TAC std_ss []
       >> Q.PAT_X_ASSUM `!x. P x` MP_TAC
       >> RW_TAC std_ss [lambda_system_def, GSPECIFICATION])
   >> STRIP_TAC
   >> Suff
      `!g l.
         g IN subsets gsig /\ (BIGUNION (IMAGE f (UNIV : num -> bool)) = l) ==>
         (lam (l INTER g) + lam ((space gsig DIFF l) INTER g) = lam g) /\
         (lam (l INTER g) = suminf (lam o (\s. s INTER g) o f))`
   >- (RW_TAC std_ss [lambda_system_def, GSPECIFICATION, SUMS_EQ]
       >> POP_ASSUM
          (MP_TAC o Q.SPEC `BIGUNION (IMAGE (f : num -> 'a -> bool) UNIV)`)
       >> RW_TAC std_ss [INTER_IDEMPOT]
       >> Suff `(\s. s INTER BIGUNION (IMAGE f UNIV)) o f = f`
       >- RW_TAC std_ss []
       >> KILL_TAC
       >> RW_TAC std_ss [FUN_EQ_THM]
       >> RW_TAC std_ss [o_DEF, EXTENSION, IN_INTER, IN_BIGUNION,
                         GSPECIFICATION, IN_IMAGE, IN_UNIV]
       >> METIS_TAC [IN_INTER,SPECIFICATION,IN_BIGUNION_IMAGE,IN_UNIV])
   >> rpt GEN_TAC
   >> STRIP_TAC
   >> Know `summable (lam o (\s. s INTER g) o f)`
   >- (MATCH_MP_TAC SER_COMPAR
       >> Q.EXISTS_TAC `lam o f`
       >> RW_TAC std_ss []
       >> Q.EXISTS_TAC `0`
       >> RW_TAC arith_ss [o_DEF]
       >> Q.PAT_X_ASSUM `outer_measure_space (space gsig,subsets gsig,lam)` MP_TAC
       >> RW_TAC std_ss [outer_measure_space_def, increasing_def, positive_def,
                         measure_def, measurable_sets_def]
       >> Know `f n IN subsets gsig`
       >- (Q.PAT_X_ASSUM `f IN x` MP_TAC
           >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, lambda_system_def,
                             GSPECIFICATION])
       >> STRIP_TAC
       >> Know `f n INTER g IN subsets gsig`
       >- PROVE_TAC [ALGEBRA_INTER, sigma_algebra_def]
       >> STRIP_TAC
       >> Know `0 <= lam (f n INTER g)` >- PROVE_TAC []
       >> RW_TAC std_ss [abs]
       >> Q.PAT_X_ASSUM `!s. P s` MATCH_MP_TAC
       >> RW_TAC std_ss [SUBSET_DEF, IN_INTER])
   >> STRIP_TAC
   >> Suff
      `lam g <= lam (l INTER g) + lam ((space gsig DIFF l) INTER g) /\
       lam (l INTER g) <= suminf (lam o (\s. s INTER g) o f) /\
       suminf (lam o (\s. s INTER g) o f) + lam ((space gsig DIFF l) INTER g) <= lam g`
   >- REAL_ARITH_TAC
   >> Strip >|
   [Know `lam = measure (space gsig,subsets gsig,lam)` >- RW_TAC std_ss [measure_def]
    >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    >> MATCH_MP_TAC SUBADDITIVE
    >> REWRITE_TAC [measurable_sets_def]
    >> CONJ_TAC
    >- (MATCH_MP_TAC COUNTABLY_SUBADDITIVE_SUBADDITIVE
        >> REWRITE_TAC [measurable_sets_def, m_space_def, SPACE]
        >> PROVE_TAC [outer_measure_space_def, sigma_algebra_def])
    >> CONJ_TAC >- PROVE_TAC [ALGEBRA_INTER, sigma_algebra_def]
    >> CONJ_TAC >- PROVE_TAC [ALGEBRA_INTER, sigma_algebra_def, ALGEBRA_COMPL]
    >> RW_TAC std_ss [EXTENSION, DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY, IN_DIFF,
                      IN_UNION]
    >> FULL_SIMP_TAC std_ss [sigma_algebra_def, algebra_def, SUBSET_DEF, subset_class_def]
    >> PROVE_TAC [],
    Q.PAT_X_ASSUM `f IN (x -> y)` MP_TAC
    >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
    >> Know `lam = measure (space gsig,subsets gsig,lam)` >- RW_TAC std_ss [measure_def]
    >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    >> MATCH_MP_TAC COUNTABLY_SUBADDITIVE
    >> REWRITE_TAC [measurable_sets_def, measure_def]
    >> CONJ_TAC >- PROVE_TAC [outer_measure_space_def]
    >> CONJ_TAC
    >- (RW_TAC std_ss [IN_FUNSET, IN_UNIV, o_DEF]
        >> POP_ASSUM (MP_TAC o Q.SPEC `x`)
        >> RW_TAC std_ss [lambda_system_def, GSPECIFICATION]
        >> PROVE_TAC [ALGEBRA_INTER, sigma_algebra_def])
    >> CONJ_TAC >- PROVE_TAC []
    >> CONJ_TAC
    >- (RW_TAC std_ss [EXTENSION, IN_INTER, IN_BIGUNION, IN_IMAGE, IN_UNIV,
                       o_DEF]
        >> reverse EQ_TAC >- PROVE_TAC []
        >> RW_TAC std_ss [GSYM EXTENSION]
        >> Q.EXISTS_TAC `f x' INTER g`
        >> RW_TAC std_ss [IN_INTER]
        >> PROVE_TAC [])
    >> PROVE_TAC [ALGEBRA_INTER, sigma_algebra_def],
    Suff `suminf (lam o (\s. s INTER g) o f) <= lam g - lam ((space gsig DIFF l) INTER g)`
    >- REAL_ARITH_TAC
    >> MATCH_MP_TAC SUMMABLE_LE
    >> CONJ_TAC >- PROVE_TAC []
    >> GEN_TAC
    >> MP_TAC (Q.SPECL [`gsig`, `lam`, `g`, `f`, `n`] LAMBDA_SYSTEM_STRONG_SUM)
    >> RW_TAC std_ss [SIGMA_ALGEBRA_ALGEBRA, OUTER_MEASURE_SPACE_POSITIVE]
    >> POP_ASSUM K_TAC
    >> Suff
       `(lam g = lam (BIGUNION (IMAGE f (count n)) INTER g) +
                 lam ((space gsig DIFF BIGUNION (IMAGE f (count n))) INTER g)) /\
        lam ((space gsig DIFF BIGUNION (IMAGE f UNIV)) INTER g) <=
        lam ((space gsig DIFF BIGUNION (IMAGE f (count n))) INTER g)`
    >- REAL_ARITH_TAC
    >> CONJ_TAC
    >- (Suff `BIGUNION (IMAGE f (count n)) IN lambda_system gsig lam`
        >- RW_TAC std_ss [lambda_system_def, GSPECIFICATION]
        >> MATCH_MP_TAC ((REWRITE_RULE [subsets_def] o Q.SPEC `(space gsig,lambda_system gsig lam)`) ALGEBRA_FINITE_UNION)
        >> Q.PAT_X_ASSUM `f IN (x -> y)` MP_TAC
        >> RW_TAC std_ss [SUBSET_DEF, IN_FUNSET, IN_UNIV, IN_IMAGE]
        >> PROVE_TAC [LAMBDA_SYSTEM_ALGEBRA, SIGMA_ALGEBRA_ALGEBRA,
                      OUTER_MEASURE_SPACE_POSITIVE, IMAGE_FINITE, FINITE_COUNT])
    >> Q.PAT_X_ASSUM `outer_measure_space (space gsig,subsets gsig,lam)` MP_TAC
    >> RW_TAC std_ss [outer_measure_space_def, increasing_def, measure_def,
                      measurable_sets_def]
    >> Q.PAT_X_ASSUM `!s. P s` MATCH_MP_TAC
    >> CONJ_TAC
    >- PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, ALGEBRA_COMPL, ALGEBRA_INTER]
    >> CONJ_TAC
    >- (Know `algebra gsig` >- PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA]
        >> STRIP_TAC
        >> MATCH_MP_TAC ALGEBRA_INTER
        >> RW_TAC std_ss []
        >> MATCH_MP_TAC ALGEBRA_COMPL
        >> RW_TAC std_ss []
        >> MATCH_MP_TAC ALGEBRA_FINITE_UNION
        >> Q.PAT_X_ASSUM `f IN x` MP_TAC
        >> RW_TAC std_ss [SUBSET_DEF, IN_FUNSET, IN_UNIV, lambda_system_def,
                          GSPECIFICATION, IN_IMAGE]
        >> PROVE_TAC [IMAGE_FINITE, FINITE_COUNT])
    >> RW_TAC std_ss [SUBSET_DEF, IN_INTER, IN_COMPL, IN_IMAGE, IN_BIGUNION,
                      IN_UNIV, IN_DIFF]
    >> PROVE_TAC []]);

val CARATHEODORY_LEMMA = store_thm
  ("CARATHEODORY_LEMMA",
   ``!gsig lam.
       sigma_algebra gsig /\ outer_measure_space (space gsig, subsets gsig, lam) ==>
       measure_space (space gsig, lambda_system gsig lam, lam)``,
   RW_TAC std_ss []
   >> MP_TAC (Q.SPECL [`gsig`, `lam`] LAMBDA_SYSTEM_CARATHEODORY)
   >> RW_TAC std_ss [measure_space_def, countably_additive_def,
                     measurable_sets_def, measure_def, m_space_def] >|
   [RW_TAC std_ss [SIGMA_ALGEBRA_ALT_DISJOINT, subsets_def]
    >> PROVE_TAC [LAMBDA_SYSTEM_ALGEBRA, SIGMA_ALGEBRA_ALGEBRA,
                  outer_measure_space_def],
    PROVE_TAC [outer_measure_space_def, LAMBDA_SYSTEM_POSITIVE]]);

val INF_MEASURE_NONEMPTY = store_thm
  ("INF_MEASURE_NONEMPTY",
   ``!m g s.
       algebra (m_space m, measurable_sets m) /\ positive m /\ s IN measurable_sets m /\
       g SUBSET s ==>
       measure m s IN
       {r |
        ?f.
          f IN (UNIV -> measurable_sets m) /\
          (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
          g SUBSET BIGUNION (IMAGE f UNIV) /\ measure m o f sums r}``,
   RW_TAC std_ss [GSPECIFICATION, SUBSET_DEF, positive_def]
   >> Q.EXISTS_TAC `\n. if n = 0 then s else {}`
   >> BasicProvers.NORM_TAC std_ss
      [SUBSET_DEF, IN_BIGUNION, DISJOINT_EMPTY,
       IN_IMAGE, IN_UNIV, o_DEF, IN_FUNSET, ALGEBRA_EMPTY]
   >| [PROVE_TAC [subsets_def, ALGEBRA_EMPTY],
       PROVE_TAC [],
      Know `measure m s = sum (0,1) (\x. measure m (if x = 0 then s else {}))`
      >- (ASM_SIMP_TAC bool_ss [sum, ONE, REAL_ADD_LID] >> RW_TAC arith_ss [])
      >> DISCH_THEN (REWRITE_TAC o wrap)
      >> MATCH_MP_TAC SER_0
      >> RW_TAC arith_ss []]);

val INF_MEASURE_POS0 = store_thm
  ("INF_MEASURE_POS0",
   ``!m g x.
       algebra (m_space m,measurable_sets m) /\ positive m /\
       x IN
       {r |
        ?f.
          f IN (UNIV -> measurable_sets m) /\
          (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
          g SUBSET BIGUNION (IMAGE f UNIV) /\ measure m o f sums r} ==>
       0 <= x``,
   RW_TAC std_ss [GSPECIFICATION, SUMS_EQ, IN_FUNSET, IN_UNIV, positive_def]
   >> MATCH_MP_TAC SER_POS
   >> RW_TAC std_ss [o_DEF]);

val INF_MEASURE_POS = store_thm
  ("INF_MEASURE_POS",
   ``!m g. algebra (m_space m, measurable_sets m) /\ positive m /\ g SUBSET m_space m ==> 0 <= inf_measure m g``,
   RW_TAC std_ss [GSPECIFICATION, inf_measure_def]
   >> MATCH_MP_TAC LE_INF
   >> CONJ_TAC
   >- (Q.EXISTS_TAC `measure m (m_space m)`
       >> MATCH_MP_TAC INF_MEASURE_NONEMPTY
       >> PROVE_TAC [ALGEBRA_SPACE, space_def, subsets_def])
   >> METIS_TAC [INF_MEASURE_POS0]);

val INCREASING = store_thm
  ("INCREASING",
   ``!m s t.
       increasing m /\ s SUBSET t /\ s IN measurable_sets m /\
       t IN measurable_sets m ==>
       measure m s <= measure m t``,
   PROVE_TAC [increasing_def]);

val ADDITIVE_INCREASING = store_thm
  ("ADDITIVE_INCREASING",
   ``!m.
       algebra (m_space m, measurable_sets m) /\ positive m /\ additive m ==>
       increasing m``,
   RW_TAC std_ss [increasing_def, positive_def]
   >> Suff
      `?u. u IN measurable_sets m /\ (measure m t = measure m s + measure m u)`
   >- (RW_TAC std_ss []
       >> Q.PAT_X_ASSUM `!s. P s` (MP_TAC o Q.SPEC `u`)
       >> RW_TAC std_ss []
       >> NTAC 2 (POP_ASSUM MP_TAC)
       >> REAL_ARITH_TAC)
   >> Q.EXISTS_TAC `t DIFF s`
   >> STRONG_CONJ_TAC >- PROVE_TAC [ALGEBRA_DIFF, subsets_def]
   >> RW_TAC std_ss []
   >> MATCH_MP_TAC ADDITIVE
   >> RW_TAC std_ss [DISJOINT_DEF, IN_DIFF, IN_UNION, EXTENSION, IN_INTER,
                     NOT_IN_EMPTY]
   >> PROVE_TAC [SUBSET_DEF]);

val COUNTABLY_ADDITIVE_ADDITIVE = store_thm
  ("COUNTABLY_ADDITIVE_ADDITIVE",
   ``!m.
       algebra (m_space m, measurable_sets m) /\ positive m /\ countably_additive m ==>
       additive m``,
   RW_TAC std_ss [additive_def, positive_def, countably_additive_def]
   >> Q.PAT_X_ASSUM `!f. P f`
      (MP_TAC o Q.SPEC `\n : num. if n = 0 then s else if n = 1 then t else {}`)
   >> Know
      `BIGUNION
       (IMAGE (\n : num. (if n = 0 then s else (if n = 1 then t else {})))
        UNIV) =
       s UNION t`
   >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION, IN_IMAGE, IN_UNIV, IN_UNION]
       >> EQ_TAC >- PROVE_TAC [NOT_IN_EMPTY]
       >> Know `~(1 = (0:num))` >- DECIDE_TAC
       >> RW_TAC std_ss [] >- PROVE_TAC []
       >> Q.EXISTS_TAC `t`
       >> RW_TAC std_ss []
       >> Q.EXISTS_TAC `1`
       >> RW_TAC std_ss []
       >> PROVE_TAC [])
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
   >> Suff
      `measure m o (\n. (if n = 0 then s else (if n = 1 then t else {}))) sums
       (measure m s + measure m t) /\
       measure m o (\n. (if n = 0 then s else (if n = 1 then t else {}))) sums
       measure m (s UNION t)`
   >- PROVE_TAC [SUM_UNIQ]
   >> CONJ_TAC
   >- (Know
       `measure m s + measure m t =
        sum (0, 2)
        (measure m o (\n. (if n = 0 then s else (if n = 1 then t else {}))))`
       >- (ASM_SIMP_TAC bool_ss [TWO, ONE, sum]
           >> RW_TAC std_ss []
           >> RW_TAC arith_ss [REAL_ADD_LID, o_THM])
       >> DISCH_THEN (REWRITE_TAC o wrap)
       >> MATCH_MP_TAC SER_0
       >> RW_TAC arith_ss [o_THM])
   >> POP_ASSUM MATCH_MP_TAC
   >> CONJ_TAC >- PROVE_TAC [ALGEBRA_EMPTY, space_def, subsets_def]
   >> RW_TAC std_ss [DISJOINT_EMPTY]
   >> PROVE_TAC [DISJOINT_SYM, ALGEBRA_UNION, subsets_def]);

val COUNTABLY_ADDITIVE = store_thm
  ("COUNTABLY_ADDITIVE",
   ``!m s f.
       countably_additive m /\ f IN (UNIV -> measurable_sets m)
       /\ (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
       (s = BIGUNION (IMAGE f UNIV)) /\ s IN measurable_sets m ==>
       measure m o f sums measure m s``,
   RW_TAC std_ss []
   >> PROVE_TAC [countably_additive_def]);

val INF_MEASURE_AGREES = store_thm
  ("INF_MEASURE_AGREES",
   ``!m s.
       algebra (m_space m, measurable_sets m) /\ positive m /\ countably_additive m /\
       s IN measurable_sets m ==>
       (inf_measure m s = measure m s)``,
   RW_TAC std_ss [inf_measure_def]
   >> ONCE_REWRITE_TAC [GSYM REAL_LE_ANTISYM]
   >> CONJ_TAC
   >- (MATCH_MP_TAC INF_LE
       >> CONJ_TAC
       >- (Q.EXISTS_TAC `0`
           >> METIS_TAC [INF_MEASURE_POS0])
       >> Q.EXISTS_TAC `measure m s`
       >> reverse CONJ_TAC >- RW_TAC std_ss [REAL_LE_REFL]
       >> MATCH_MP_TAC INF_MEASURE_NONEMPTY
       >> RW_TAC std_ss [SUBSET_REFL])
   >> MATCH_MP_TAC LE_INF
   >> CONJ_TAC
   >- (Q.EXISTS_TAC `measure m s`
       >> MATCH_MP_TAC INF_MEASURE_NONEMPTY
       >> RW_TAC std_ss [SUBSET_REFL])
   >> RW_TAC std_ss [GSPECIFICATION, SUBSET_DEF, IN_FUNSET, IN_UNIV,
                     IN_BIGUNION, IN_IMAGE, SUMS_EQ]
   >> MP_TAC (Q.SPECL [`m`] countably_additive_def)
   >> RW_TAC std_ss []
   >> POP_ASSUM (MP_TAC o Q.SPEC `(\g. g INTER s) o f`)
   >> Know `BIGUNION (IMAGE ((\g. g INTER s) o f) UNIV) = s`
   >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION, IN_IMAGE, IN_INTER, o_THM]
       >> EQ_TAC >- PROVE_TAC []
       >> RW_TAC std_ss []
       >> Q.PAT_X_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`)
       >> RW_TAC std_ss [IN_UNIV]
       >> Q.EXISTS_TAC `s INTER f x'`
       >> RW_TAC std_ss [IN_INTER]
       >> PROVE_TAC [EXTENSION])
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> RW_TAC std_ss [o_THM, IN_FUNSET, IN_UNIV, IN_INTER]
   >> Suff `measure m o (\g. g INTER s) o f sums measure m s`
   >- (RW_TAC std_ss [SUMS_EQ]
       >> POP_ASSUM (REWRITE_TAC o wrap o GSYM)
       >> MATCH_MP_TAC SER_LE
       >> RW_TAC std_ss [o_THM]
       >> MATCH_MP_TAC INCREASING
       >> RW_TAC std_ss [ALGEBRA_INTER, INTER_SUBSET]
       >- (MATCH_MP_TAC ADDITIVE_INCREASING
           >> RW_TAC std_ss []
           >> MATCH_MP_TAC COUNTABLY_ADDITIVE_ADDITIVE
           >> RW_TAC std_ss [])
       >> PROVE_TAC [ALGEBRA_INTER, subsets_def])
   >> POP_ASSUM MATCH_MP_TAC
   >> CONJ_TAC >- PROVE_TAC [ALGEBRA_INTER, subsets_def]
   >> RW_TAC std_ss []
   >> Q.PAT_X_ASSUM `!m n. P m n` (MP_TAC o Q.SPECL [`m'`, `n`])
   >> RW_TAC std_ss [DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY, EXTENSION]
   >> PROVE_TAC []);

val MEASURE_DOWN = store_thm
  ("MEASURE_DOWN",
   ``!m0 m1.
       sigma_algebra (m_space m0,measurable_sets m0) /\
       measurable_sets m0 SUBSET measurable_sets m1 /\
       (measure m0 = measure m1) /\ measure_space m1 ==>
       measure_space m0``,
   RW_TAC std_ss [measure_space_def, positive_def, SUBSET_DEF,
                  countably_additive_def, IN_FUNSET, IN_UNIV]);

val INF_MEASURE_EMPTY = store_thm
  ("INF_MEASURE_EMPTY",
   ``!m. algebra (m_space m, measurable_sets m) /\ positive m ==> (inf_measure m {} = 0)``,
   RW_TAC std_ss []
   >> ONCE_REWRITE_TAC [GSYM REAL_LE_ANTISYM]
   >> reverse CONJ_TAC >- PROVE_TAC [INF_MEASURE_POS, EMPTY_SUBSET]
   >> RW_TAC std_ss [inf_measure_def]
   >> MATCH_MP_TAC INF_LE
   >> CONJ_TAC >- METIS_TAC [INF_MEASURE_POS0, EMPTY_SUBSET]
   >> Q.EXISTS_TAC `0`
   >> RW_TAC std_ss [GSPECIFICATION, REAL_LE_REFL]
   >> Q.EXISTS_TAC `K {}`
   >> RW_TAC bool_ss [IN_FUNSET, IN_UNIV, ALGEBRA_EMPTY, DISJOINT_EMPTY, K_THM,
                      SUBSET_DEF, NOT_IN_EMPTY, IN_BIGUNION, IN_IMAGE]
   >- PROVE_TAC [subsets_def, space_def, ALGEBRA_EMPTY]
   >> Know `0 = sum (0, 0) (measure m o K {})` >- RW_TAC std_ss [sum]
   >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   >> MATCH_MP_TAC SER_0
   >> RW_TAC std_ss [K_THM, o_THM]
   >> PROVE_TAC [positive_def]);

val INF_MEASURE_POSITIVE = store_thm
  ("INF_MEASURE_POSITIVE",
   ``!m.
       algebra (m_space m, measurable_sets m) /\ positive m ==>
       positive (m_space m, POW (m_space m), inf_measure m)``,
   RW_TAC std_ss [positive_def, INF_MEASURE_EMPTY, INF_MEASURE_POS,
                  measure_def, measurable_sets_def, IN_POW]);

val INF_MEASURE_INCREASING = store_thm
  ("INF_MEASURE_INCREASING",
   ``!m.
       algebra (m_space m, measurable_sets m) /\ positive m ==>
       increasing (m_space m, POW (m_space m), inf_measure m)``,
   RW_TAC std_ss [increasing_def, inf_measure_def, measurable_sets_def, IN_POW, measure_def]
   >> MATCH_MP_TAC LE_INF
   >> CONJ_TAC
   >- (Q.EXISTS_TAC `measure m (m_space m)`
       >> MATCH_MP_TAC INF_MEASURE_NONEMPTY
       >> RW_TAC std_ss []
       >> PROVE_TAC [ALGEBRA_SPACE, subsets_def, space_def, m_space_def, measurable_sets_def])
   >> RW_TAC std_ss []
   >> MATCH_MP_TAC INF_LE
   >> CONJ_TAC
   >- (Q.EXISTS_TAC `0`
       >> METIS_TAC [INF_MEASURE_POS0])
   >> Q.EXISTS_TAC `x`
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [GSPECIFICATION, REAL_LE_REFL]
   >> PROVE_TAC [SUBSET_TRANS]);

val INF_MEASURE_LE = store_thm
  ("INF_MEASURE_LE",
   ``!m s x.
       algebra (m_space m, measurable_sets m) /\ positive m /\ increasing m /\
       x IN
       {r | ?f.
          f IN (UNIV -> measurable_sets m) /\
          s SUBSET BIGUNION (IMAGE f UNIV) /\
          measure m o f sums r} ==>
       inf_measure m s <= x``,
   RW_TAC std_ss [GSPECIFICATION, SUMS_EQ, IN_FUNSET, IN_UNIV]
   >> RW_TAC std_ss [inf_measure_def]
   >> MATCH_MP_TAC INF_LE
   >> CONJ_TAC
   >- (Q.EXISTS_TAC `0`
       >> METIS_TAC [INF_MEASURE_POS0])
   >> RW_TAC std_ss [GSPECIFICATION, SUMS_EQ]
   >> CONV_TAC (DEPTH_CONV LEFT_AND_EXISTS_CONV THENC SWAP_EXISTS_CONV)
   >> Q.EXISTS_TAC `\n. f n DIFF (BIGUNION (IMAGE f (count n)))`
   >> Q.EXISTS_TAC
      `suminf (measure m o (\n. f n DIFF (BIGUNION (IMAGE f (count n)))))`
   >> REWRITE_TAC [GSYM CONJ_ASSOC, IN_FUNSET, IN_UNIV]
   >> BETA_TAC
   >> STRONG_CONJ_TAC
   >- (STRIP_TAC
       >> MATCH_MP_TAC ((REWRITE_RULE [space_def, subsets_def] o Q.SPEC `(m_space m,measurable_sets m)`) ALGEBRA_DIFF)
       >> RW_TAC std_ss []
       >> MATCH_MP_TAC ((REWRITE_RULE [space_def, subsets_def] o Q.SPEC `(m_space m,measurable_sets m)`) ALGEBRA_FINITE_UNION)
       >> RW_TAC std_ss [SUBSET_DEF, IN_IMAGE]
       >> PROVE_TAC [IMAGE_FINITE, FINITE_COUNT])
   >> STRIP_TAC
   >> Know
      `summable (measure m o (\n. f n DIFF (BIGUNION (IMAGE f (count n))))) /\
       suminf (measure m o (\n. f n DIFF (BIGUNION (IMAGE f (count n))))) <=
       suminf (measure m o f)`
   >- (MATCH_MP_TAC SER_POS_COMPARE
       >> RW_TAC std_ss [o_THM] >- PROVE_TAC [positive_def]
       >> MATCH_MP_TAC INCREASING
       >> PROVE_TAC [DIFF_SUBSET])
   >> RW_TAC std_ss [] >|
   [RW_TAC arith_ss [DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY, EXTENSION, IN_DIFF,
                     IN_BIGUNION, IN_IMAGE, IN_COUNT]
    >> Know `m' < n \/ n < m'` >- DECIDE_TAC
    >> PROVE_TAC [],
    Q.PAT_X_ASSUM `s SUBSET g` MP_TAC
    >> RW_TAC arith_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE, IN_UNIV]
    >> Q.PAT_X_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`)
    >> RW_TAC std_ss []
    >> Know `?n. x IN f n` >- PROVE_TAC []
    >> DISCH_THEN (MP_TAC o Ho_Rewrite.REWRITE_RULE [whileTheory.LEAST_EXISTS])
    >> RW_TAC std_ss []
    >> Q.EXISTS_TAC
       `f (LEAST n. x IN f n) DIFF
        BIGUNION (IMAGE f (count (LEAST n. x IN f n)))`
    >> reverse CONJ_TAC >- PROVE_TAC []
    >> RW_TAC std_ss [IN_DIFF, IN_BIGUNION, IN_IMAGE, IN_COUNT]
    >> PROVE_TAC []]);

val INF_MEASURE_CLOSE = store_thm
  ("INF_MEASURE_CLOSE",
   ``!m s e.
       algebra (m_space m, measurable_sets m) /\ positive m /\ 0 < e /\ s SUBSET (m_space m) ==>
       ?f l.
         f IN (UNIV -> measurable_sets m) /\ s SUBSET BIGUNION (IMAGE f UNIV) /\
         (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
         (measure m o f) sums l /\ l <= inf_measure m s + e``,
   RW_TAC std_ss [inf_measure_def]
   >> Suff
      `?l.
         l IN {r | ?f.
            f IN (UNIV -> measurable_sets m) /\
            (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
            s SUBSET BIGUNION (IMAGE f UNIV) /\ measure m o f sums r} /\
         l < inf {r | ?f.
            f IN (UNIV -> measurable_sets m) /\
            (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
            s SUBSET BIGUNION (IMAGE f UNIV) /\ measure m o f sums r} + e`
   >- (RW_TAC std_ss [GSPECIFICATION]
       >> Q.EXISTS_TAC `f`
       >> Q.EXISTS_TAC `l`
       >> RW_TAC std_ss []
       >> PROVE_TAC [REAL_LT_IMP_LE])
   >> MATCH_MP_TAC INF_CLOSE
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `measure m (m_space m)`
   >> MATCH_MP_TAC INF_MEASURE_NONEMPTY
   >> RW_TAC std_ss []
   >> PROVE_TAC [ALGEBRA_SPACE, m_space_def, measurable_sets_def, subsets_def, space_def]);

val INF_MEASURE_COUNTABLY_SUBADDITIVE = store_thm
  ("INF_MEASURE_COUNTABLY_SUBADDITIVE",
   ``!m.
       algebra (m_space m, measurable_sets m) /\ positive m /\ increasing m ==>
       countably_subadditive (m_space m, POW (m_space m), inf_measure m)``,
   RW_TAC std_ss [countably_subadditive_def, IN_FUNSET, IN_UNIV]
   >> MATCH_MP_TAC REAL_LE_EPSILON
   >> RW_TAC std_ss []
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Know
      `!n. ?g l.
         g IN (UNIV -> measurable_sets m) /\
         f n SUBSET BIGUNION (IMAGE g UNIV) /\
         (!m n. ~(m = n) ==> DISJOINT (g m) (g n)) /\
         (measure m o g) sums l /\
         l <= inf_measure m (f n) + e * (1 / 2) pow (n + 1)`
   >- (STRIP_TAC
       >> MATCH_MP_TAC INF_MEASURE_CLOSE
       >> PROVE_TAC [REAL_LT_MUL, POW_HALF_POS, measurable_sets_def, IN_POW])
   >> CONV_TAC (REDEPTH_CONV (CHANGED_CONV SKOLEM_CONV))
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `suminf l`
   >> Know `!n. 0 <= l n`
   >- (RW_TAC std_ss []
       >> POP_ASSUM (MP_TAC o Q.SPEC `n`)
       >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, SUMS_EQ]
       >> Q.PAT_X_ASSUM `a = b` (REWRITE_TAC o wrap o GSYM)
       >> MATCH_MP_TAC SUMINF_POS
       >> RW_TAC std_ss [o_THM]
       >> PROVE_TAC [positive_def])
   >> STRIP_TAC
   >> Know
      `summable l /\
       suminf l <= suminf (\n. inf_measure m (f n)) + e`
   >- (Know `(\n. e * (1 / 2) pow (n + 1)) sums (e * 1)`
       >- (HO_MATCH_MP_TAC SER_CMUL
           >> RW_TAC std_ss [POW_HALF_SER])
       >> PURE_REWRITE_TAC [REAL_MUL_RID, SUMS_EQ]
       >> STRIP_TAC
       >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o GSYM)
       >> Know
          `summable (\n. inf_measure m (f n) + e * (1 / 2) pow (n + 1)) /\
           (suminf (\n. inf_measure m (f n)) +
            suminf (\n. e * (1 / 2) pow (n + 1)) =
            suminf (\n. inf_measure m (f n) + e * (1 / 2) pow (n + 1)))`
       >- (HO_MATCH_MP_TAC SUMINF_ADD
           >> Q.PAT_X_ASSUM `summable (a o b)` MP_TAC
           >> RW_TAC std_ss [o_DEF, measure_def])
       >> STRIP_TAC
       >> POP_ASSUM (ONCE_REWRITE_TAC o wrap)
       >> MATCH_MP_TAC SER_POS_COMPARE
       >> RW_TAC std_ss [])
   >> RW_TAC std_ss [o_DEF, measure_def]
   >> MATCH_MP_TAC INF_MEASURE_LE
   >> RW_TAC std_ss [GSPECIFICATION]
   >> MP_TAC NUM_2D_BIJ_INV
   >> STRIP_TAC
   >> Q.EXISTS_TAC `UNCURRY g o f'`
   >> Q.PAT_X_ASSUM `!n. P n /\ Q n` MP_TAC
   >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, o_THM, SUBSET_DEF, IN_BIGUNION,
                     IN_IMAGE] >|
   [Cases_on `f' x`
    >> RW_TAC std_ss [UNCURRY_DEF],
    Q.PAT_X_ASSUM `!n. P n` (MP_TAC o Q.SPEC `x'`)
    >> RW_TAC std_ss []
    >> Q.PAT_X_ASSUM `!n. P n` K_TAC
    >> Q.PAT_X_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`)
    >> RW_TAC std_ss []
    >> Q.EXISTS_TAC `g x' x''`
    >> RW_TAC std_ss []
    >> Q.PAT_X_ASSUM `BIJ a b c` MP_TAC
    >> RW_TAC std_ss [BIJ_DEF, SURJ_DEF, IN_UNIV, IN_CROSS]
    >> POP_ASSUM (MP_TAC o Q.SPEC `(x', x'')`)
    >> RW_TAC std_ss []
    >> Q.EXISTS_TAC `y`
    >> RW_TAC std_ss [UNCURRY_DEF],
    Know `measure m o UNCURRY g o f' = UNCURRY (\m'. measure m o g m') o f'`
    >- (RW_TAC std_ss [FUN_EQ_THM]
        >> RW_TAC std_ss [o_DEF]
        >> Cases_on `f' x`
        >> RW_TAC std_ss [UNCURRY_DEF])
    >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    >> MATCH_MP_TAC SUMINF_2D
    >> RW_TAC std_ss [o_THM]
    >> PROVE_TAC [positive_def]]);

val INF_MEASURE_OUTER = store_thm
  ("INF_MEASURE_OUTER",
   ``!m.
       algebra (m_space m, measurable_sets m) /\ positive m /\ increasing m ==>
       outer_measure_space (m_space m, POW(m_space m), inf_measure m)``,
   RW_TAC std_ss [outer_measure_space_def, INF_MEASURE_POSITIVE,
                  INF_MEASURE_INCREASING, INF_MEASURE_COUNTABLY_SUBADDITIVE]);

val ALGEBRA_SUBSET_LAMBDA_SYSTEM = store_thm
  ("ALGEBRA_SUBSET_LAMBDA_SYSTEM",
   ``!m.
       algebra (m_space m, measurable_sets m) /\ positive m /\ increasing m /\
       additive m ==>
       measurable_sets m SUBSET lambda_system (m_space m, POW (m_space m)) (inf_measure m)``,
   RW_TAC std_ss [SUBSET_DEF, lambda_system_def, GSPECIFICATION,
                           IN_UNIV, GSYM REAL_LE_ANTISYM, space_def, subsets_def, IN_POW]
   >| [FULL_SIMP_TAC std_ss [algebra_def, subset_class_def, m_space_def, measurable_sets_def,
                             space_def, subsets_def, SUBSET_DEF]
       >> PROVE_TAC [],
       MATCH_MP_TAC REAL_LE_EPSILON
   >> RW_TAC std_ss []
   >> MP_TAC (Q.SPECL [`m`, `s`, `e`] INF_MEASURE_CLOSE)
   >> Know `s SUBSET m_space m`
   >- PROVE_TAC [SUBSET_DEF, algebra_def, subset_class_def, subsets_def, space_def]
   >> RW_TAC std_ss [SUMS_EQ, IN_FUNSET, IN_UNIV]
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Q.EXISTS_TAC `suminf (measure m o f)`
   >> RW_TAC std_ss []
   >> POP_ASSUM K_TAC
   >> Know
      `!x.
         x IN measurable_sets m ==>
         summable (measure m o (\s. x INTER s) o f) /\
         inf_measure m (x INTER s) <= suminf (measure m o (\s. x INTER s) o f)`
   >- (NTAC 2 STRIP_TAC
       >> STRONG_CONJ_TAC
       >- (MATCH_MP_TAC SER_COMPAR
           >> Q.EXISTS_TAC `measure m o f`
           >> RW_TAC std_ss [GREATER_EQ]
           >> Q.EXISTS_TAC `0`
           >> reverse (RW_TAC arith_ss [o_THM, abs])
           >- PROVE_TAC [positive_def, (REWRITE_RULE [subsets_def, space_def] o
                         Q.SPEC `(m_space m,measurable_sets m)`) ALGEBRA_INTER]
           >> MATCH_MP_TAC INCREASING
           >> RW_TAC std_ss [INTER_SUBSET, (REWRITE_RULE [subsets_def, space_def] o
                                           Q.SPEC `(m_space m,measurable_sets m)`) ALGEBRA_INTER])
       >> RW_TAC std_ss [inf_measure_def]
       >> MATCH_MP_TAC INF_LE
       >> CONJ_TAC
       >- (Q.EXISTS_TAC `0`
           >> METIS_TAC [INF_MEASURE_POS0])
       >> Q.EXISTS_TAC `suminf (measure m o (\s. x' INTER s) o f)`
       >> RW_TAC std_ss [REAL_LE_REFL, GSPECIFICATION]
       >> Q.EXISTS_TAC `(\s. x' INTER s) o f`
       >> RW_TAC std_ss [IN_FUNSET, IN_UNIV,
                (REWRITE_RULE [subsets_def, space_def] o Q.SPEC `(m_space m,measurable_sets m)`) ALGEBRA_INTER, o_THM, SUMS_EQ]
       >- (Q.PAT_X_ASSUM `!n. P n` (MP_TAC o Q.SPECL [`m'`, `n`])
           >> RW_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY]
           >> PROVE_TAC [])
       >> Q.PAT_X_ASSUM `s SUBSET ss` MP_TAC
       >> RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_INTER, IN_IMAGE,
                         IN_UNIV, o_THM]
       >> Q.PAT_X_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x''`)
       >> RW_TAC std_ss []
       >> PROVE_TAC [IN_INTER])
   >> DISCH_THEN
      (fn th => MP_TAC (Q.SPEC `x` th) >> MP_TAC (Q.SPEC `m_space m DIFF x` th))
   >> RW_TAC std_ss [(REWRITE_RULE [subsets_def, space_def] o
                     Q.SPEC `(m_space m,measurable_sets m)`) ALGEBRA_COMPL]
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Q.EXISTS_TAC
      `suminf (measure m o (\s. x INTER s) o f) +
       suminf (measure m o (\s. (m_space m DIFF x) INTER s) o f)`
   >> CONJ_TAC
   >- (Q.PAT_X_ASSUM `(a:real) <= b` MP_TAC
       >> Q.PAT_X_ASSUM `(a:real) <= b` MP_TAC
       >> REAL_ARITH_TAC)
   >> RW_TAC std_ss [SUMINF_ADD, o_THM]
   >> Know `!a b : real. (a = b) ==> a <= b` >- REAL_ARITH_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> AP_TERM_TAC
   >> RW_TAC std_ss [FUN_EQ_THM]
   >> RW_TAC std_ss [o_THM]
   >> MATCH_MP_TAC EQ_SYM
   >> MATCH_MP_TAC ADDITIVE
   >> RW_TAC std_ss [(REWRITE_RULE [subsets_def, space_def] o
                      Q.SPEC `(m_space m,measurable_sets m)`) ALGEBRA_INTER,
                     (REWRITE_RULE [subsets_def, space_def] o
                      Q.SPEC `(m_space m,measurable_sets m)`) ALGEBRA_COMPL,
                     DISJOINT_DEF, IN_INTER, IN_DIFF, NOT_IN_EMPTY, EXTENSION, IN_UNION]
   >> PROVE_TAC [algebra_def, subset_class_def, SUBSET_DEF, space_def, subsets_def],
   Know `inf_measure m = measure (m_space m, POW (m_space m), inf_measure m)`
       >- RW_TAC std_ss [measure_def]
       >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
       >> MATCH_MP_TAC SUBADDITIVE
       >> RW_TAC std_ss [IN_UNIV, EXTENSION, IN_INTER, IN_DIFF, IN_UNION, IN_POW,
                         measurable_sets_def, SUBSET_DEF]
       >> PROVE_TAC [INF_MEASURE_COUNTABLY_SUBADDITIVE,
                     INF_MEASURE_POSITIVE, POW_ALGEBRA,
                     COUNTABLY_SUBADDITIVE_SUBADDITIVE,
                     measurable_sets_def, m_space_def]]);

val CARATHEODORY = store_thm
  ("CARATHEODORY",
   ``!m0.
       algebra (m_space m0, measurable_sets m0) /\ positive m0 /\ countably_additive m0 ==>
       ?m.
         (!s. s IN measurable_sets m0 ==> (measure m s = measure m0 s)) /\
         ((m_space m, measurable_sets m) =
          sigma (m_space m0) (measurable_sets m0)) /\ measure_space m``,
   RW_TAC std_ss []
   >> Q.EXISTS_TAC `(space (sigma (m_space m0) (measurable_sets m0)),
                     subsets (sigma (m_space m0) (measurable_sets m0)),
                     inf_measure m0)`
   >> CONJ_TAC >- PROVE_TAC [INF_MEASURE_AGREES, measure_def]
   >> CONJ_TAC >- RW_TAC std_ss [measurable_sets_def, subsets_def, space_def, m_space_def, SPACE]
   >> MATCH_MP_TAC MEASURE_DOWN
   >> Q.EXISTS_TAC
      `(m_space m0,
        lambda_system (m_space m0, POW (m_space m0)) (inf_measure m0),
        inf_measure m0)`
   >> REWRITE_TAC [measurable_sets_def, measure_def, space_def, m_space_def, subsets_def, SPACE]
   >> STRONG_CONJ_TAC >- FULL_SIMP_TAC std_ss [algebra_def, SIGMA_ALGEBRA_SIGMA,
                                               space_def, subsets_def]
   >> STRIP_TAC
   >> ONCE_REWRITE_TAC [CONJ_COMM]
   >> STRONG_CONJ_TAC
   >- ((MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
       Q.SPEC `(m_space m0,POW (m_space m0))`) CARATHEODORY_LEMMA
       >> CONJ_TAC >- RW_TAC std_ss [POW_SIGMA_ALGEBRA]
       >> PROVE_TAC [INF_MEASURE_OUTER, COUNTABLY_ADDITIVE_ADDITIVE,
                     ADDITIVE_INCREASING])
   >> RW_TAC std_ss []
   >> (MATCH_MP_TAC o REWRITE_RULE [space_def, subsets_def] o
        Q.SPECL [`(measurable_sets m0)`, `(m_space m0,
                                           lambda_system (m_space m0, POW (m_space m0))
                                           (inf_measure m0))`]) SIGMA_SUBSET
   >> CONJ_TAC >- FULL_SIMP_TAC std_ss [measure_space_def, measurable_sets_def, m_space_def]
   >> PROVE_TAC [ALGEBRA_SUBSET_LAMBDA_SYSTEM, COUNTABLY_ADDITIVE_ADDITIVE,
                 ADDITIVE_INCREASING]);

val MEASURE_COMPL = store_thm
  ("MEASURE_COMPL",
   ``!m s.
       measure_space m /\ s IN measurable_sets m ==>
       (measure m (m_space m DIFF s) = measure m (m_space m) - measure m s)``,
   RW_TAC std_ss []
   >> Suff `measure m (m_space m) = measure m s + measure m (m_space m DIFF s)`
   >- REAL_ARITH_TAC
   >> MATCH_MP_TAC ADDITIVE
   >> Q.PAT_X_ASSUM `measure_space m` MP_TAC
   >> RW_TAC std_ss [measure_space_def, sigma_algebra_def, DISJOINT_DEF,
                     EXTENSION, IN_DIFF, IN_UNIV, IN_UNION, IN_INTER,
                     NOT_IN_EMPTY]
   >> PROVE_TAC [COUNTABLY_ADDITIVE_ADDITIVE, ALGEBRA_COMPL, subsets_def, space_def,
                 algebra_def, subset_class_def, SUBSET_DEF]);

val MEASURE_EMPTY = store_thm
  ("MEASURE_EMPTY",
   ``!m. measure_space m ==> (measure m {} = 0)``,
   RW_TAC std_ss [measure_space_def, positive_def]);

val SIGMA_SUBSET_MEASURABLE_SETS = store_thm
  ("SIGMA_SUBSET_MEASURABLE_SETS",
   ``!a m.
       measure_space m /\ a SUBSET measurable_sets m ==>
       subsets (sigma (m_space m) a) SUBSET measurable_sets m``,
   RW_TAC std_ss [measure_space_def]
   >> MATCH_MP_TAC SIGMA_PROPERTY
   >> RW_TAC std_ss [IN_INTER, SUBSET_INTER]
   >> PROVE_TAC [SIGMA_ALGEBRA, space_def, subsets_def]);


val SPACE_SMALLEST_CLOSED_CDI = store_thm
  ("SPACE_SMALLEST_CLOSED_CDI",
   ``!a. space (smallest_closed_cdi a) = space a``,
  RW_TAC std_ss [smallest_closed_cdi_def, space_def]);

val SMALLEST_CLOSED_CDI = store_thm
  ("SMALLEST_CLOSED_CDI",
   ``!a. algebra a ==> subsets a SUBSET subsets (smallest_closed_cdi a) /\
                       closed_cdi (smallest_closed_cdi a) /\
         subset_class (space a) (subsets (smallest_closed_cdi a))``,
   Know `!a. algebra a ==> subsets a SUBSET subsets (smallest_closed_cdi a) /\
                           closed_cdi (smallest_closed_cdi a)`
   >- (RW_TAC std_ss [smallest_closed_cdi_def, GSPECIFICATION, SUBSET_DEF, INTER_DEF, BIGINTER,
                       subset_class_def, algebra_def, subsets_def]
        >> RW_TAC std_ss [closed_cdi_def, GSPECIFICATION, IN_BIGINTER, IN_FUNSET,
                          IN_UNIV, subsets_def, space_def, subset_class_def]
        >> POP_ASSUM (MP_TAC o Q.SPEC `{x | x SUBSET space a}`)
        >> RW_TAC std_ss [GSPECIFICATION]
        >> POP_ASSUM MATCH_MP_TAC
        >> RW_TAC std_ss [SUBSET_DEF]
        >> PROVE_TAC [IN_DIFF, IN_BIGUNION, IN_IMAGE, IN_UNIV])
   >> SIMP_TAC std_ss []
   >> RW_TAC std_ss [closed_cdi_def, SPACE_SMALLEST_CLOSED_CDI]);

val CLOSED_CDI_DUNION = store_thm
  ("CLOSED_CDI_DUNION",
   ``!p s t.
       {} IN subsets p /\ closed_cdi p /\ s IN subsets p /\ t IN subsets p /\ DISJOINT s t ==>
       s UNION t IN subsets p``,
   RW_TAC std_ss [closed_cdi_def]
   >> Q.PAT_X_ASSUM `!f. P f`
      (MP_TAC o Q.SPEC `\n. if n = 0 then s else if n = 1 then t else {}`)
   >> Know
      `BIGUNION
       (IMAGE (\n : num. (if n = 0 then s else (if n = 1 then t else {})))
        UNIV) =
       BIGUNION
       (IMAGE (\n : num. (if n = 0 then s else (if n = 1 then t else {})))
        (count 2))`
   >- (MATCH_MP_TAC BIGUNION_IMAGE_UNIV
       >> RW_TAC arith_ss [])
   >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   >> RW_TAC bool_ss [COUNT_SUC, IMAGE_INSERT, TWO, ONE, BIGUNION_INSERT,
                      COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY, UNION_EMPTY]
   >> ONCE_REWRITE_TAC [UNION_COMM]
   >> POP_ASSUM MATCH_MP_TAC
   >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, DISJOINT_EMPTY]
   >> PROVE_TAC [DISJOINT_SYM]);

val CLOSED_CDI_COMPL = store_thm
  ("CLOSED_CDI_COMPL",
   ``!p s. closed_cdi p /\ s IN subsets p ==> space p DIFF s IN subsets p``,
   RW_TAC std_ss [closed_cdi_def]);

val CLOSED_CDI_DISJOINT = store_thm
  ("CLOSED_CDI_DISJOINT",
   ``!p f.
       closed_cdi p /\ f IN (UNIV -> subsets p) /\
       (!m n : num. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
       BIGUNION (IMAGE f UNIV) IN subsets p``,
   RW_TAC std_ss [closed_cdi_def]);

val CLOSED_CDI_INCREASING = store_thm
  ("CLOSED_CDI_INCREASING",
   ``!p f.
       closed_cdi p /\ f IN (UNIV -> subsets p) /\ (f 0 = {}) /\
       (!n. f n SUBSET f (SUC n)) ==>
       BIGUNION (IMAGE f UNIV) IN subsets p``,
   RW_TAC std_ss [closed_cdi_def]);

val SIGMA_PROPERTY_DISJOINT_LEMMA1 = store_thm
  ("SIGMA_PROPERTY_DISJOINT_LEMMA1",
   ``!a.
       algebra a ==>
       (!s t.
          s IN subsets a /\ t IN subsets (smallest_closed_cdi a) ==>
          s INTER t IN subsets (smallest_closed_cdi a))``,
   RW_TAC std_ss [IN_BIGINTER, GSPECIFICATION, smallest_closed_cdi_def, subsets_def]
   >> Suff
      `t IN
       {b | b IN subsets (smallest_closed_cdi a) /\ s INTER b IN subsets (smallest_closed_cdi a)}`
   >- RW_TAC std_ss [GSPECIFICATION, IN_BIGINTER, smallest_closed_cdi_def, subsets_def]
   >> first_x_assum MATCH_MP_TAC
   >> STRONG_CONJ_TAC
   >- (RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_BIGINTER,
                      smallest_closed_cdi_def, subsets_def]
       >> PROVE_TAC [ALGEBRA_INTER])
   >> RW_TAC std_ss [GSPECIFICATION, SUBSET_DEF, closed_cdi_def, space_def, subsets_def] >|
   [(MP_TAC o UNDISCH o Q.SPEC `a`) SMALLEST_CLOSED_CDI
    >> RW_TAC std_ss [subset_class_def, SUBSET_DEF, GSPECIFICATION]
    >> PROVE_TAC [algebra_def, subset_class_def, SUBSET_DEF],
    PROVE_TAC [closed_cdi_def, SMALLEST_CLOSED_CDI, SPACE_SMALLEST_CLOSED_CDI],
    Know `s INTER (space a DIFF s') =
          space (smallest_closed_cdi a) DIFF
                (space (smallest_closed_cdi a) DIFF s UNION (s INTER s'))`
    >- (RW_TAC std_ss [EXTENSION, INTER_DEF, COMPL_DEF, UNION_DEF, GSPECIFICATION, IN_UNIV,
                       IN_DIFF]
        >> PROVE_TAC [SPACE_SMALLEST_CLOSED_CDI])
    >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    >> MATCH_MP_TAC CLOSED_CDI_COMPL
    >> RW_TAC std_ss [SMALLEST_CLOSED_CDI]
    >> MATCH_MP_TAC CLOSED_CDI_DUNION
    >> CONJ_TAC
    >- PROVE_TAC [ALGEBRA_EMPTY, SMALLEST_CLOSED_CDI, SUBSET_DEF]
    >> CONJ_TAC >- RW_TAC std_ss [SMALLEST_CLOSED_CDI]
    >> CONJ_TAC
    >- (MATCH_MP_TAC CLOSED_CDI_COMPL
        >> RW_TAC std_ss [SMALLEST_CLOSED_CDI])
    >> CONJ_TAC >- PROVE_TAC [SMALLEST_CLOSED_CDI, SUBSET_DEF]
    >> RW_TAC std_ss [DISJOINT_DEF, COMPL_DEF, INTER_DEF, IN_DIFF, IN_UNIV, GSPECIFICATION,
                      EXTENSION, NOT_IN_EMPTY]
    >> DECIDE_TAC,
    Q.PAT_X_ASSUM `f IN x` MP_TAC
    >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSPECIFICATION]
    >> MATCH_MP_TAC CLOSED_CDI_INCREASING
    >> RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, SUBSET_DEF],
    Know
    `s INTER BIGUNION (IMAGE f UNIV) =
     BIGUNION (IMAGE (\m. case m of 0 => {} | SUC n => s INTER f n) UNIV)`
    >- (KILL_TAC
        >> RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, GSPECIFICATION, IN_IMAGE, IN_UNIV,
                          IN_INTER]
        >> (EQ_TAC >> RW_TAC std_ss [NOT_IN_EMPTY]) >|
        [Q.EXISTS_TAC `s INTER f x'`
         >> RW_TAC std_ss [IN_INTER]
         >> Q.EXISTS_TAC `SUC x'`
         >> RW_TAC arith_ss [IN_INTER, num_case_def],
         POP_ASSUM (MP_TAC)
         >> Cases_on `m` >- RW_TAC arith_ss [num_case_def, NOT_IN_EMPTY]
         >> RW_TAC arith_ss [num_case_def, IN_INTER],
         POP_ASSUM (MP_TAC)
         >> Cases_on `m` >- RW_TAC arith_ss [num_case_def, NOT_IN_EMPTY]
         >> RW_TAC arith_ss [num_case_def, IN_INTER]
         >> Q.EXISTS_TAC `f n`
         >> RW_TAC std_ss []
         >> PROVE_TAC []])
    >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    >> MATCH_MP_TAC CLOSED_CDI_INCREASING
    >> Q.PAT_X_ASSUM `f IN X` MP_TAC
    >> RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, IN_UNIV, GSPECIFICATION]
    >- (reverse (Cases_on `m`) >- RW_TAC arith_ss []
        >> RW_TAC arith_ss []
        >> PROVE_TAC [SMALLEST_CLOSED_CDI, ALGEBRA_EMPTY, SUBSET_DEF])
    >> Cases_on `n` >- RW_TAC arith_ss [num_case_def, EMPTY_SUBSET]
    >> RW_TAC arith_ss [num_case_def, SUBSET_DEF, IN_INTER],
    Q.PAT_X_ASSUM `f IN x` MP_TAC
    >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSPECIFICATION]
    >> MATCH_MP_TAC CLOSED_CDI_DISJOINT
    >> RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, SUBSET_DEF],
    Know
    `s INTER BIGUNION (IMAGE f UNIV) =
     BIGUNION (IMAGE (\n. s INTER f n) UNIV)`
    >- (KILL_TAC
        >> RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, GSPECIFICATION, IN_IMAGE, IN_UNIV,
                          IN_INTER]
        >> (EQ_TAC >> RW_TAC std_ss []) >|
        [Q.EXISTS_TAC `s INTER f x'`
         >> RW_TAC std_ss [IN_INTER]
         >> Q.EXISTS_TAC `x'`
         >> RW_TAC arith_ss [IN_INTER],
         POP_ASSUM (MP_TAC)
         >> RW_TAC arith_ss [IN_INTER],
         POP_ASSUM (MP_TAC)
         >> RW_TAC arith_ss [IN_INTER]
         >> Q.EXISTS_TAC `f n`
         >> RW_TAC std_ss []
         >> PROVE_TAC []])
    >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    >> MATCH_MP_TAC CLOSED_CDI_DISJOINT
    >> Q.PAT_X_ASSUM `f IN X` MP_TAC
    >> RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, IN_UNIV, GSPECIFICATION]
    >> Q.PAT_X_ASSUM `!m n. PP m n` (MP_TAC o Q.SPECL [`m`, `n`])
    >> RW_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY]
    >> PROVE_TAC []]);

val SIGMA_PROPERTY_DISJOINT_LEMMA2 = store_thm
  ("SIGMA_PROPERTY_DISJOINT_LEMMA2",
   ``!a.
       algebra a ==>
       (!s t.
          s IN subsets (smallest_closed_cdi a) /\ t IN subsets (smallest_closed_cdi a) ==>
          s INTER t IN subsets (smallest_closed_cdi a))``,
   RW_TAC std_ss []
   >> POP_ASSUM MP_TAC
   >> SIMP_TAC std_ss [smallest_closed_cdi_def, IN_BIGINTER, GSPECIFICATION, subsets_def]
   >> STRIP_TAC >> Q.X_GEN_TAC `P`
   >> Suff
      `t IN
       {b | b IN subsets (smallest_closed_cdi a) /\ s INTER b IN subsets (smallest_closed_cdi a)}`
   >- RW_TAC std_ss [GSPECIFICATION, IN_BIGINTER, smallest_closed_cdi_def, subsets_def]
   >> Q.PAT_X_ASSUM `!s. P s` MATCH_MP_TAC
   >> STRONG_CONJ_TAC
   >- (RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION] >|
       [PROVE_TAC [SMALLEST_CLOSED_CDI, SUBSET_DEF],
        PROVE_TAC [SIGMA_PROPERTY_DISJOINT_LEMMA1, INTER_COMM]])
   >> SIMP_TAC std_ss [GSPECIFICATION, SUBSET_DEF, closed_cdi_def, space_def, subsets_def]
   >> STRIP_TAC >> rpt CONJ_TAC >|
   [(MP_TAC o UNDISCH o Q.SPEC `a`) SMALLEST_CLOSED_CDI
    >> RW_TAC std_ss [subset_class_def, SUBSET_DEF, GSPECIFICATION]
    >> PROVE_TAC [algebra_def, subset_class_def, SUBSET_DEF],
    Q.X_GEN_TAC `s'`
    >> rpt STRIP_TAC
    >- PROVE_TAC [closed_cdi_def, SMALLEST_CLOSED_CDI,
                  SPACE_SMALLEST_CLOSED_CDI]
    >> Know `s INTER (space a DIFF s') =
             space (smallest_closed_cdi a) DIFF
             (space (smallest_closed_cdi a) DIFF s UNION (s INTER s'))`
    >- (RW_TAC std_ss [EXTENSION, INTER_DEF, COMPL_DEF, UNION_DEF, GSPECIFICATION, IN_UNIV,
                       IN_DIFF, SPACE_SMALLEST_CLOSED_CDI]
        >> DECIDE_TAC)
    >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    >> MATCH_MP_TAC CLOSED_CDI_COMPL
    >> RW_TAC std_ss [SMALLEST_CLOSED_CDI]
    >> MATCH_MP_TAC CLOSED_CDI_DUNION
    >> CONJ_TAC
    >- PROVE_TAC [ALGEBRA_EMPTY, SMALLEST_CLOSED_CDI, SUBSET_DEF]
    >> CONJ_TAC >- RW_TAC std_ss [SMALLEST_CLOSED_CDI]
    >> CONJ_TAC
    >- (MATCH_MP_TAC CLOSED_CDI_COMPL
        >> RW_TAC std_ss [SMALLEST_CLOSED_CDI])
    >> CONJ_TAC >- PROVE_TAC [SMALLEST_CLOSED_CDI, SUBSET_DEF]
    >> RW_TAC std_ss [DISJOINT_DEF, COMPL_DEF, INTER_DEF, IN_DIFF, IN_UNIV, GSPECIFICATION,
                      EXTENSION, NOT_IN_EMPTY]
    >> DECIDE_TAC,
    Q.X_GEN_TAC `f` >> rpt STRIP_TAC
    >- (Q.PAT_X_ASSUM `f IN x` MP_TAC
        >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSPECIFICATION]
        >> MATCH_MP_TAC CLOSED_CDI_INCREASING
        >> RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, SUBSET_DEF])
    >> Know
         `s INTER BIGUNION (IMAGE f UNIV) =
          BIGUNION (IMAGE (\m. case m of 0 => {} | SUC n => s INTER f n) UNIV)`
    >- (KILL_TAC
        >> RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, GSPECIFICATION, IN_IMAGE, IN_UNIV,
                          IN_INTER]
        >> (EQ_TAC >> RW_TAC std_ss [NOT_IN_EMPTY]) >|
        [Q.EXISTS_TAC `s INTER f x'`
         >> RW_TAC std_ss [IN_INTER]
         >> Q.EXISTS_TAC `SUC x'`
         >> RW_TAC arith_ss [IN_INTER, num_case_def],
         POP_ASSUM (MP_TAC)
         >> Cases_on `m` >- RW_TAC arith_ss [num_case_def, NOT_IN_EMPTY]
         >> RW_TAC arith_ss [num_case_def, IN_INTER],
         POP_ASSUM (MP_TAC)
         >> Cases_on `m` >- RW_TAC arith_ss [num_case_def, NOT_IN_EMPTY]
         >> RW_TAC arith_ss [num_case_def, IN_INTER]
         >> Q.EXISTS_TAC `f n`
         >> RW_TAC std_ss []
         >> PROVE_TAC []])
    >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    >> MATCH_MP_TAC CLOSED_CDI_INCREASING
    >> Q.PAT_X_ASSUM `f IN X` MP_TAC
    >> RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, IN_UNIV, GSPECIFICATION]
    >- (reverse (Cases_on `m`) >- RW_TAC arith_ss []
        >> RW_TAC arith_ss []
        >> PROVE_TAC [SMALLEST_CLOSED_CDI, ALGEBRA_EMPTY, SUBSET_DEF])
    >> Cases_on `n` >- RW_TAC arith_ss [num_case_def, EMPTY_SUBSET]
    >> RW_TAC arith_ss [num_case_def, SUBSET_DEF, IN_INTER],
    Q.X_GEN_TAC `f` >> rpt STRIP_TAC
    >- (Q.PAT_X_ASSUM `f IN x` MP_TAC
        >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSPECIFICATION]
        >> MATCH_MP_TAC CLOSED_CDI_DISJOINT
        >> RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, SUBSET_DEF])
    >> Know
        `s INTER BIGUNION (IMAGE f UNIV) =
         BIGUNION (IMAGE (\n. s INTER f n) UNIV)`
    >- (KILL_TAC
        >> RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, GSPECIFICATION, IN_IMAGE, IN_UNIV,
                          IN_INTER]
        >> (EQ_TAC >> RW_TAC std_ss []) >|
        [Q.EXISTS_TAC `s INTER f x'`
         >> RW_TAC std_ss [IN_INTER]
         >> Q.EXISTS_TAC `x'`
         >> RW_TAC arith_ss [IN_INTER],
         POP_ASSUM (MP_TAC)
         >> RW_TAC arith_ss [IN_INTER],
         POP_ASSUM (MP_TAC)
         >> RW_TAC arith_ss [IN_INTER]
         >> Q.EXISTS_TAC `f n`
         >> RW_TAC std_ss []
         >> PROVE_TAC []])
    >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    >> MATCH_MP_TAC CLOSED_CDI_DISJOINT
    >> Q.PAT_X_ASSUM `f IN X` MP_TAC
    >> RW_TAC std_ss [SMALLEST_CLOSED_CDI, IN_FUNSET, IN_UNIV, GSPECIFICATION]
    >> Q.PAT_X_ASSUM `!m n. PP m n` (MP_TAC o Q.SPECL [`m`, `n`])
    >> RW_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY]
    >> PROVE_TAC []]);

val SIGMA_PROPERTY_DISJOINT_LEMMA = store_thm
  ("SIGMA_PROPERTY_DISJOINT_LEMMA",
   ``!sp a p. algebra (sp, a) /\ a SUBSET p /\ closed_cdi (sp, p)
         ==> subsets (sigma sp a) SUBSET p``,
   RW_TAC std_ss []
   >> MATCH_MP_TAC SUBSET_TRANS
   >> Q.EXISTS_TAC `subsets (smallest_closed_cdi (sp, a))`
   >> reverse CONJ_TAC
   >- (RW_TAC std_ss [SUBSET_DEF, smallest_closed_cdi_def, IN_BIGINTER,
                      GSPECIFICATION, subsets_def, space_def]
       >> PROVE_TAC [SUBSET_DEF])
   >> NTAC 2 (POP_ASSUM K_TAC)
   >> Suff `subsets (smallest_closed_cdi (sp, a)) IN {b | a SUBSET b /\ sigma_algebra (sp,b)}`
   >- (KILL_TAC
       >> RW_TAC std_ss [sigma_def, BIGINTER, SUBSET_DEF, GSPECIFICATION,subsets_def])
   >> RW_TAC std_ss [GSPECIFICATION, SIGMA_ALGEBRA_ALT_DISJOINT,
                     ALGEBRA_ALT_INTER, space_def, subsets_def] >|
   [PROVE_TAC [SMALLEST_CLOSED_CDI, subsets_def],
    PROVE_TAC [SMALLEST_CLOSED_CDI, space_def],
    PROVE_TAC [ALGEBRA_EMPTY, SUBSET_DEF, SMALLEST_CLOSED_CDI, space_def],
    PROVE_TAC [SMALLEST_CLOSED_CDI, CLOSED_CDI_COMPL, space_def, SPACE_SMALLEST_CLOSED_CDI],
    PROVE_TAC [SIGMA_PROPERTY_DISJOINT_LEMMA2],
    PROVE_TAC [SMALLEST_CLOSED_CDI, CLOSED_CDI_DISJOINT]]);

val MEASURE_COUNTABLY_ADDITIVE = store_thm
  ("MEASURE_COUNTABLY_ADDITIVE",
   ``!m s f.
       measure_space m /\ f IN (UNIV -> measurable_sets m) /\
       (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
       (s = BIGUNION (IMAGE f UNIV)) ==>
       measure m o f sums measure m s``,
   RW_TAC std_ss []
   >> MATCH_MP_TAC COUNTABLY_ADDITIVE
   >> RW_TAC std_ss []
   >- PROVE_TAC [measure_space_def]
   >> (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
         Q.SPEC `(m_space m, measurable_sets m)`) SIGMA_ALGEBRA_COUNTABLE_UNION
   >> CONJ_TAC >- PROVE_TAC [measure_space_def]
   >> Q.PAT_X_ASSUM `f IN P` MP_TAC
   >> RW_TAC std_ss [COUNTABLE_IMAGE_NUM, SUBSET_DEF, IN_IMAGE, IN_UNIV,
                     IN_FUNSET]
   >> PROVE_TAC []);

val MEASURE_SPACE_ADDITIVE = store_thm
  ("MEASURE_SPACE_ADDITIVE",
   ``!m. measure_space m ==> additive m``,
   RW_TAC std_ss []
   >> MATCH_MP_TAC COUNTABLY_ADDITIVE_ADDITIVE
   >> PROVE_TAC [measure_space_def, SIGMA_ALGEBRA_ALGEBRA]);

val MEASURE_ADDITIVE = store_thm
  ("MEASURE_ADDITIVE",
   ``!m s t u.
       measure_space m /\ s IN measurable_sets m /\ t IN measurable_sets m /\
       DISJOINT s t /\ (u = s UNION t) ==>
       (measure m u = measure m s + measure m t)``,
   RW_TAC std_ss []
   >> MATCH_MP_TAC ADDITIVE
   >> RW_TAC std_ss [MEASURE_SPACE_ADDITIVE]);

val MEASURE_COUNTABLE_INCREASING = store_thm
  ("MEASURE_COUNTABLE_INCREASING",
   ``!m s f.
       measure_space m /\ f IN (UNIV -> measurable_sets m) /\
       (f 0 = {}) /\ (!n. f n SUBSET f (SUC n)) /\
       (s = BIGUNION (IMAGE f UNIV)) ==>
       measure m o f --> measure m s``,
   RW_TAC std_ss [IN_FUNSET, IN_UNIV]
   >> Know
      `measure m o f = (\n. sum (0, n) (measure m o (\m. f (SUC m) DIFF f m)))`
   >- (RW_TAC std_ss [FUN_EQ_THM]
       >> Induct_on `n` >- RW_TAC std_ss [o_THM, sum, MEASURE_EMPTY]
       >> POP_ASSUM (MP_TAC o SYM)
       >> RW_TAC arith_ss [o_THM, sum]
       >> MATCH_MP_TAC MEASURE_ADDITIVE
       >> FULL_SIMP_TAC std_ss [EXTENSION, IN_UNION, IN_DIFF, DISJOINT_DEF, NOT_IN_EMPTY,
                                IN_INTER, SUBSET_DEF]
       >> Know `algebra (m_space m, measurable_sets m)`
       >- FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,
                                space_def, subsets_def]
       >> STRIP_TAC
       >> (MP_TAC o REWRITE_RULE [subsets_def, space_def] o
           Q.SPEC `(m_space m, measurable_sets m)`) ALGEBRA_DIFF
       >> PROVE_TAC [])
   >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   >> RW_TAC std_ss [GSYM sums]
   >> MATCH_MP_TAC COUNTABLY_ADDITIVE
   >> CONJ_TAC >- PROVE_TAC [measure_space_def]
   >> CONJ_TAC
   >- (RW_TAC std_ss [IN_FUNSET, IN_UNIV]
       >> Know `algebra (m_space m, measurable_sets m)`
       >- FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,
                                space_def, subsets_def]
       >> STRIP_TAC
       >> (MP_TAC o REWRITE_RULE [subsets_def, space_def] o
           Q.SPEC `(m_space m, measurable_sets m)`) ALGEBRA_DIFF
       >> PROVE_TAC [])
   >> CONJ_TAC
   >- (rpt STRIP_TAC
       >> MATCH_MP_TAC DISJOINT_DIFFS
       >> Q.EXISTS_TAC `f`
       >> RW_TAC std_ss [])
   >> CONJ_TAC
   >- (FULL_SIMP_TAC std_ss [EXTENSION, IN_UNION, IN_DIFF, DISJOINT_DEF, NOT_IN_EMPTY, IN_INTER,
                             SUBSET_DEF, IN_BIGUNION, IN_IMAGE, IN_UNIV, DIFF_DEF]
       >> STRIP_TAC
       >> reverse (EQ_TAC >> RW_TAC std_ss [])
       >- PROVE_TAC []
       >> Know `x IN f x'` >- PROVE_TAC []
       >> NTAC 2 (POP_ASSUM K_TAC)
       >> Induct_on `x'` >- RW_TAC std_ss []
       >> POP_ASSUM MP_TAC
       >> Cases_on `x IN f x'` >- RW_TAC std_ss []
       >> RW_TAC std_ss []
       >> Q.EXISTS_TAC `f (SUC x') DIFF f x'`
       >> RW_TAC std_ss [EXTENSION, DIFF_DEF, GSPECIFICATION]
       >> PROVE_TAC [])
   >> (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
        Q.SPEC `(m_space m, measurable_sets m)`) SIGMA_ALGEBRA_COUNTABLE_UNION
   >> CONJ_TAC >- PROVE_TAC [measure_space_def]
   >> RW_TAC std_ss [COUNTABLE_IMAGE_NUM]
   >> RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV]
   >> PROVE_TAC []);

val MEASURE_SPACE_REDUCE = store_thm
  ("MEASURE_SPACE_REDUCE",
   ``!m. (m_space m, measurable_sets m, measure m) = m``,
   Cases
   >> Q.SPEC_TAC (`r`, `r`)
   >> Cases
   >> RW_TAC std_ss [m_space_def, measurable_sets_def, measure_def]);

Theorem MONOTONE_CONVERGENCE :
    !m s f.
       measure_space m /\ f IN (UNIV -> measurable_sets m) /\
       (!n. f n SUBSET f (SUC n)) /\
       (s = BIGUNION (IMAGE f UNIV)) ==>
       measure m o f --> measure m s
Proof
    RW_TAC std_ss [measure_space_def, IN_FUNSET, IN_UNIV]
 >> (MP_TAC o
       INST_TYPE [beta |-> ``:num``] o
       Q.SPECL [`m`, `BIGUNION (IMAGE f UNIV)`, `\x. num_CASE x {} f`])
      MEASURE_COUNTABLE_INCREASING
 >> Cond
 >- (RW_TAC std_ss [IN_FUNSET, IN_UNIV, num_case_def, measure_space_def] >|
     [ (* goal 1 *)
       Cases_on `x` >|
       [ RW_TAC std_ss [num_case_def] \\
         PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, ALGEBRA_EMPTY, subsets_def],
         RW_TAC std_ss [num_case_def] ],
       (* goal 2 *)
       Cases_on `n` \\
       RW_TAC std_ss [num_case_def, EMPTY_SUBSET],
       (* goal 3 *)
       RW_TAC std_ss [EXTENSION, GSPECIFICATION] \\
       RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_UNIV] \\
       EQ_TAC >| (* 2 subgoals *)
       [ (* goal 1 (of 2) *)
         RW_TAC std_ss [] \\
         Q.EXISTS_TAC `SUC x'` \\
         RW_TAC std_ss [num_case_def],
         (* goal 2 (of 2) *)
         RW_TAC std_ss [] \\
         POP_ASSUM MP_TAC \\
         Cases_on `x'` >- RW_TAC std_ss [NOT_IN_EMPTY, num_case_def] \\
         RW_TAC std_ss [num_case_def] \\
         PROVE_TAC [] ] ])
 >> RW_TAC std_ss []
 >> Know `measure m o f = (\n. (measure m o (\x. num_CASE x {} f)) (SUC n))`
 >- (RW_TAC std_ss [FUN_EQ_THM] \\
     RW_TAC std_ss [num_case_def, o_THM])
 >> Rewr
 >> Ho_Rewrite.REWRITE_TAC [GSYM SEQ_SUC]
 >> RW_TAC (std_ss ++ boolSimps.ETA_ss) []
QED

val MEASURABLE_SETS_SUBSET_SPACE = store_thm
  ("MEASURABLE_SETS_SUBSET_SPACE",
   ``!m s. measure_space m /\ s IN measurable_sets m ==>
                s SUBSET m_space m``,
   RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def, subsets_def, space_def,
                  subset_class_def]);

(* NOTE: removed `measure_space m1 /\ measure_space m2` due to changes of
   `measurable` and `measure_preserving`.
 *)
val IN_MEASURE_PRESERVING = store_thm
  ("IN_MEASURE_PRESERVING",
   ``!m1 m2 f.
       f IN measure_preserving m1 m2 <=>
       f IN measurable (m_space m1, measurable_sets m1) (m_space m2, measurable_sets m2) /\
       !s.
         s IN measurable_sets m2 ==>
         (measure m1 ((PREIMAGE f s)INTER(m_space m1)) = measure m2 s)``,
   RW_TAC std_ss [measure_preserving_def, GSPECIFICATION]);

(* NOTE: added `measure_space (m_space m2,a,measure m2)` due to changes of `measurable` *)
val MEASURE_PRESERVING_LIFT = store_thm
  ("MEASURE_PRESERVING_LIFT",
   ``!m1 m2 a f.
       measure_space m1 /\ measure_space m2 /\
       measure_space (m_space m2,a,measure m2) /\
       (measurable_sets m2 = subsets (sigma (m_space m2) a)) /\
       f IN measure_preserving m1 (m_space m2, a, measure m2) ==>
       f IN measure_preserving m1 m2``,
   RW_TAC std_ss []
   >> `algebra (m_space m2,a)`
        by fs [measure_space_def, sigma_algebra_def, m_space_def, measurable_sets_def]
   >> Suff `f IN measure_preserving m1 (m_space m2, measurable_sets m2, measure m2)`
   >- RW_TAC std_ss [MEASURE_SPACE_REDUCE]
   >> ASM_REWRITE_TAC []
   >> Q.PAT_X_ASSUM `f IN X` MP_TAC
   >> REWRITE_TAC [IN_MEASURE_PRESERVING, measurable_sets_def, measure_def, m_space_def]
   >> STRIP_TAC
   >> STRONG_CONJ_TAC
   >- (Know `(m_space m2,subsets (sigma (m_space m2) a)) = sigma (m_space m2) a`
       >- (Q.ABBREV_TAC `Q = (m_space m2,subsets (sigma (m_space m2) a))`
           >> Know `sigma (m_space m2) a = (space (sigma (m_space m2) a),
                                            subsets (sigma (m_space m2) a))`
           >- RW_TAC std_ss [SPACE]
           >> STRIP_TAC >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
           >> Q.UNABBREV_TAC `Q`
           >> RW_TAC std_ss [PAIR_EQ, sigma_def, space_def])
       >> RW_TAC std_ss []
       >> POP_ASSUM (K ALL_TAC)
       >> Know `(sigma (m_space m2) a) = sigma (space (m_space m2, a)) (subsets (m_space m2, a))`
       >- RW_TAC std_ss [space_def, subsets_def]
       >> STRIP_TAC >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
       >> MATCH_MP_TAC MEASURABLE_LIFT
       >> fs [measure_space_def, algebra_def])
   >> Q.PAT_X_ASSUM `f IN X` K_TAC
   >> REWRITE_TAC [IN_MEASURABLE, space_def, subsets_def]
   >> STRIP_TAC
   >> ASM_REWRITE_TAC []
   >> Suff `subsets (sigma (m_space m2) a) SUBSET
                 {s | measure m1 ((PREIMAGE f s) INTER (m_space m1)) = measure m2 s}`
   >- RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION]
   >> MATCH_MP_TAC SIGMA_PROPERTY_DISJOINT
   >> RW_TAC std_ss [GSPECIFICATION, SUBSET_DEF, IN_INTER, IN_FUNSET,
                     IN_UNIV, PREIMAGE_COMPL, PREIMAGE_BIGUNION, IMAGE_IMAGE,
                     MEASURE_COMPL] >| (* 3 subgoals *)
   [ (* goal 1 (of 3) *)
     Q.PAT_X_ASSUM `measure m1 (PREIMAGE f s INTER m_space m1) = measure m2 s`
                (fn thm => ONCE_REWRITE_TAC [GSYM thm])
    >> Know `m_space m2 IN a` >- PROVE_TAC [ALGEBRA_SPACE, subsets_def, space_def]
    >> STRIP_TAC
    >> Q.PAT_X_ASSUM `!s. s IN a ==> (measure m1 (PREIMAGE f s INTER m_space m1) = measure m2 s)`
        ((fn thm => ONCE_REWRITE_TAC [GSYM thm]) o UNDISCH o Q.SPEC `m_space m2`)
    >> Know `PREIMAGE f (m_space m2) INTER m_space m1 = m_space m1`
    >- (FULL_SIMP_TAC std_ss [Once EXTENSION, IN_INTER, IN_PREIMAGE, IN_FUNSET] >> METIS_TAC [])
    >> RW_TAC std_ss [PREIMAGE_DIFF]
    >> `((PREIMAGE f (m_space m2) DIFF PREIMAGE f s) INTER m_space m1) =
        ((PREIMAGE f (m_space m2) INTER m_space m1) DIFF (PREIMAGE f s INTER m_space m1))`
        by (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_DIFF, IN_PREIMAGE] >> DECIDE_TAC)
    >> RW_TAC std_ss [MEASURE_COMPL],
     (* goal 2 (of 3) *)
    `BIGUNION (IMAGE (PREIMAGE f o f') UNIV) INTER m_space m1 =
     BIGUNION (IMAGE (\x:num. (PREIMAGE f o f') x INTER m_space m1) UNIV)`
        by (RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, IN_INTER, IN_IMAGE, IN_UNIV]
            >> FULL_SIMP_TAC std_ss [IN_FUNSET]
            >> EQ_TAC
            >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `PREIMAGE f (f' x') INTER m_space m1`
                >> ASM_REWRITE_TAC [IN_INTER] >> Q.EXISTS_TAC `x'` >> RW_TAC std_ss [])
            >> RW_TAC std_ss [] >> METIS_TAC [IN_PREIMAGE, IN_INTER])
    >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
    >> Suff
    `(measure m2 o f') --> measure m2 (BIGUNION (IMAGE f' UNIV)) /\
     (measure m2 o f') -->
     measure m1 (BIGUNION (IMAGE (\x. (PREIMAGE f o f') x INTER m_space m1) UNIV))`
    >- PROVE_TAC [SEQ_UNIQ]
    >> CONJ_TAC
    >- (MATCH_MP_TAC MEASURE_COUNTABLE_INCREASING
        >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, SUBSET_DEF])
    >> Know `measure m2 o f' = measure m1 o (\x. (PREIMAGE f o f') x INTER m_space m1)`
    >- (RW_TAC std_ss [FUN_EQ_THM]
        >> RW_TAC std_ss [o_THM])
    >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    >> MATCH_MP_TAC MEASURE_COUNTABLE_INCREASING
    >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, o_THM, PREIMAGE_EMPTY, INTER_EMPTY]
    >> Suff `PREIMAGE f (f' n) SUBSET PREIMAGE f (f' (SUC n))`
    >- RW_TAC std_ss [SUBSET_DEF, IN_INTER]
    >> MATCH_MP_TAC PREIMAGE_SUBSET
    >> RW_TAC std_ss [SUBSET_DEF],
     (* goal 3 (of 3) *)
    `BIGUNION (IMAGE (PREIMAGE f o f') UNIV) INTER m_space m1 =
     BIGUNION (IMAGE (\x:num. (PREIMAGE f o f') x INTER m_space m1) UNIV)`
        by (RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, IN_INTER, IN_IMAGE, IN_UNIV]
            >> FULL_SIMP_TAC std_ss [IN_FUNSET]
            >> EQ_TAC
            >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `PREIMAGE f (f' x') INTER m_space m1`
                >> ASM_REWRITE_TAC [IN_INTER] >> Q.EXISTS_TAC `x'` >> RW_TAC std_ss [])
            >> RW_TAC std_ss [] >> METIS_TAC [IN_PREIMAGE, IN_INTER])
    >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
    >> Suff
    `(measure m2 o f') sums measure m2 (BIGUNION (IMAGE f' UNIV)) /\
     (measure m2 o f') sums
     measure m1 (BIGUNION (IMAGE (\x. (PREIMAGE f o f') x INTER m_space m1) UNIV))`
    >- PROVE_TAC [SUM_UNIQ]
    >> CONJ_TAC
    >- (MATCH_MP_TAC MEASURE_COUNTABLY_ADDITIVE
        >> RW_TAC std_ss [IN_FUNSET, IN_UNIV])
    >> Know `measure m2 o f' = measure m1 o (\x. (PREIMAGE f o f') x INTER m_space m1)`
    >- (RW_TAC std_ss [FUN_EQ_THM]
        >> RW_TAC std_ss [o_THM])
    >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    >> MATCH_MP_TAC MEASURE_COUNTABLY_ADDITIVE
    >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, o_THM, IN_DISJOINT, PREIMAGE_DISJOINT, IN_INTER]
    >> METIS_TAC [IN_DISJOINT, PREIMAGE_DISJOINT]
  ]);

(* NOTE: added `measure_space (m_space m2,a,measure m2)` due to changes of `measurable` *)
val MEASURE_PRESERVING_SUBSET = store_thm
  ("MEASURE_PRESERVING_SUBSET",
   ``!m1 m2 a.
       measure_space m1 /\ measure_space m2 /\
       measure_space (m_space m2,a,measure m2) /\
       (measurable_sets m2 = subsets (sigma (m_space m2) a)) ==>
       measure_preserving m1 (m_space m2, a, measure m2) SUBSET
       measure_preserving m1 m2``,
   RW_TAC std_ss [SUBSET_DEF]
   >> MATCH_MP_TAC MEASURE_PRESERVING_LIFT
   >> PROVE_TAC []);

(* NOTE: removed unused antecedent `measure_space m1` *)
val MEASURE_PRESERVING_UP_LIFT = store_thm
  ("MEASURE_PRESERVING_UP_LIFT",
   ``!m1 m2 f a.
       f IN measure_preserving (m_space m1, a, measure m1) m2 /\
       sigma_algebra (m_space m1, measurable_sets m1) /\
       a SUBSET measurable_sets m1 ==>
       f IN measure_preserving m1 m2``,
   RW_TAC std_ss [measure_preserving_def, GSPECIFICATION, SUBSET_DEF,
                  measure_def, measurable_sets_def, m_space_def, SPACE]
   >> MATCH_MP_TAC MEASURABLE_UP_LIFT
   >> Q.EXISTS_TAC `a`
   >> RW_TAC std_ss [SUBSET_DEF]);

(* NOTE: removed unused antecedent `measure_space m1` *)
val MEASURE_PRESERVING_UP_SUBSET = store_thm
  ("MEASURE_PRESERVING_UP_SUBSET",
   ``!m1 m2 a.
       a SUBSET measurable_sets m1 /\
       sigma_algebra (m_space m1, measurable_sets m1) ==>
       measure_preserving (m_space m1, a, measure m1) m2 SUBSET measure_preserving m1 m2``,
   RW_TAC std_ss [MEASURE_PRESERVING_UP_LIFT, SUBSET_DEF]
   >> MATCH_MP_TAC MEASURE_PRESERVING_UP_LIFT
   >> PROVE_TAC [SUBSET_DEF]);

(* NOTE: removed unused antecedent `measure_space m1`
         added `subset_class (m_space m1) a` due to changes of `measurable`.
 *)
val MEASURE_PRESERVING_UP_SIGMA = store_thm
  ("MEASURE_PRESERVING_UP_SIGMA",
   ``!m1 m2 a. subset_class (m_space m1) a /\
       (measurable_sets m1 = subsets (sigma (m_space m1) a)) ==>
       measure_preserving (m_space m1, a, measure m1) m2 SUBSET measure_preserving m1 m2``,
   RW_TAC std_ss [MEASURE_PRESERVING_UP_LIFT, SUBSET_DEF]
   >> MATCH_MP_TAC MEASURE_PRESERVING_UP_LIFT
   >> Q.EXISTS_TAC `a`
   >> ASM_REWRITE_TAC [SIGMA_SUBSET_SUBSETS, SIGMA_REDUCE]
   >> MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA >> art []);

(* ****************** *)

val MEASURABLE_RANGE_REDUCE = store_thm
  ("MEASURABLE_RANGE_REDUCE",
   ``!m f s. measure_space m /\
           f IN measurable (m_space m, measurable_sets m) (s, POW s) /\
             (~(s = {})) ==>
                f IN measurable (m_space m, measurable_sets m)
        (s INTER (IMAGE f (m_space m)), POW (s INTER (IMAGE f (m_space m))))``,
   RW_TAC std_ss [IN_MEASURABLE, POW_SIGMA_ALGEBRA, subsets_def, space_def, IN_FUNSET,
                  IN_INTER, IN_IMAGE, IN_POW, SUBSET_INTER,
                  MEASURABLE_SETS_SUBSET_SPACE, INTER_SUBSET]
   >> METIS_TAC []);

val MEASURABLE_POW_TO_POW = store_thm
  ("MEASURABLE_POW_TO_POW",
   ``!m f.
        measure_space m /\
        (measurable_sets m = POW (m_space m)) ==>
        f IN measurable (m_space m, measurable_sets m) (UNIV, POW(UNIV))``,
   RW_TAC std_ss [IN_MEASURABLE, IN_POW, IN_UNIV, POW_SIGMA_ALGEBRA, subsets_def, space_def,
                  IN_FUNSET, PREIMAGE_UNIV, SUBSET_UNIV, measure_space_def, SUBSET_DEF,
                  IN_INTER]);

val MEASURABLE_POW_TO_POW_IMAGE = store_thm
  ("MEASURABLE_POW_TO_POW_IMAGE",
   ``!m f.
        measure_space m /\
        (measurable_sets m = POW (m_space m)) ==>
        f IN measurable (m_space m, measurable_sets m)
                        (IMAGE f (m_space m), POW(IMAGE f (m_space m)))``,
   rpt STRIP_TAC
   >> (MP_TAC o Q.SPECL [`m`,`f`,`UNIV`]) MEASURABLE_RANGE_REDUCE
   >> ASM_SIMP_TAC std_ss [UNIV_NOT_EMPTY, INTER_UNIV, MEASURABLE_POW_TO_POW]);

val MEASURE_SPACE_SUBSET = store_thm
  ("MEASURE_SPACE_SUBSET",
   ``!s s' m. s' SUBSET s /\ measure_space (s,POW s, m) ==>
                measure_space (s',POW s', m)``,
   RW_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def, POW_SIGMA_ALGEBRA,
                  positive_def, measure_def, IN_POW, countably_additive_def, IN_FUNSET, IN_POW]
   >> METIS_TAC [SUBSET_TRANS, SUBSET_REFL]);

val STRONG_MEASURE_SPACE_SUBSET = store_thm
  ("STRONG_MEASURE_SPACE_SUBSET",
   ``!s s'. s' SUBSET m_space s /\ measure_space s /\ POW s' SUBSET measurable_sets s ==>
                measure_space (s',POW s', measure s)``,
   rpt STRIP_TAC >> MATCH_MP_TAC MEASURE_DOWN
   >> Q.EXISTS_TAC `s`
   >> RW_TAC std_ss [measure_def, m_space_def, measurable_sets_def, POW_SIGMA_ALGEBRA]);

val MEASURE_REAL_SUM_IMAGE = store_thm
  ("MEASURE_REAL_SUM_IMAGE",
   ``!m s. measure_space m /\ s IN measurable_sets m /\
                (!x. x IN s ==> {x} IN measurable_sets m) /\ FINITE s ==>
                (measure m s = SIGMA (\x. measure m {x}) s)``,
   Suff `!s. FINITE s ==>
        (\s. !m. measure_space m /\ s IN measurable_sets m /\
             (!x. x IN s ==> {x} IN measurable_sets m) ==>
                (measure m s = SIGMA (\x. measure m {x}) s)) s`
   >- METIS_TAC []
   >> MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC std_ss [REAL_SUM_IMAGE_THM, MEASURE_EMPTY, DELETE_NON_ELEMENT, IN_INSERT]
   >> Q.PAT_X_ASSUM `!p.
            measure_space m /\ s IN measurable_set m /\
            (!x. x IN s ==> {x} IN measurable_sets m) ==>
            (measure m s = SIGMA (\x. measure m {x}) s)` (MP_TAC o GSYM o Q.SPEC `m`)
   >> RW_TAC std_ss []
   >> `s IN measurable_sets m`
        by (`s = (e INSERT s) DIFF {e}`
                by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DIFF, IN_SING]
                    >> METIS_TAC [GSYM DELETE_NON_ELEMENT])
            >> POP_ORW
            >> FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def]
            >> METIS_TAC [space_def, subsets_def, ALGEBRA_DIFF])
   >> ASM_SIMP_TAC std_ss []
   >> MATCH_MP_TAC MEASURE_ADDITIVE
   >> RW_TAC std_ss [IN_DISJOINT, IN_SING, Once INSERT_SING_UNION]
   >> FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]);

val finite_additivity_sufficient_for_finite_spaces = store_thm
  ("finite_additivity_sufficient_for_finite_spaces",
   ``!s m. sigma_algebra s /\ FINITE (space s) /\
           positive (space s, subsets s, m) /\
           additive (space s, subsets s, m) ==>
                measure_space (space s, subsets s, m)``,
   RW_TAC std_ss [countably_additive_def, additive_def, measurable_sets_def, measure_def,
                  IN_FUNSET, IN_UNIV, measure_space_def, m_space_def, SPACE]
   >> `FINITE (subsets s)`
        by (Suff `subsets s SUBSET (POW (space s))`
            >- METIS_TAC [SUBSET_FINITE, FINITE_POW]
            >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, subset_class_def, SUBSET_DEF, IN_POW]
            >> METIS_TAC [])
   >> `?N. !n. n >= N ==> (f n = {})`
        by METIS_TAC [finite_enumeration_of_sets_has_max_non_empty]
   >> FULL_SIMP_TAC std_ss [GREATER_EQ]
   >> `BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE f (count N))`
        by METIS_TAC [BIGUNION_IMAGE_UNIV]
   >> RW_TAC std_ss [sums, SEQ]
   >> Q.EXISTS_TAC `N`
   >> RW_TAC std_ss [GREATER_EQ]
   >> Suff `!n. N <= n ==> (sum (0,n) (m o f) = m(BIGUNION (IMAGE f (count N))))`
   >- RW_TAC real_ss [LESS_EQ_REFL]
   >> Induct
   >- (RW_TAC std_ss [sum] >> `count 0 = {}` by RW_TAC real_ss [EXTENSION, IN_COUNT, NOT_IN_EMPTY]
       >> FULL_SIMP_TAC std_ss [IMAGE_EMPTY, BIGUNION_EMPTY, positive_def, measure_def])
   >> STRIP_TAC
   >> Cases_on `SUC n' = N`
   >- (POP_ORW
       >> `m = measure (space s, subsets s,m)` by RW_TAC std_ss [measure_def]
       >> POP_ORW
       >> MATCH_MP_TAC ADDITIVE_SUM
       >> RW_TAC std_ss [m_space_def, measurable_sets_def, IN_FUNSET, IN_UNIV, additive_def,
                         measure_def, SIGMA_ALGEBRA_ALGEBRA, SPACE])
   >> `N <= n'`
        by (NTAC 2 (POP_ASSUM MP_TAC) >> DECIDE_TAC)
   >> FULL_SIMP_TAC std_ss []
   >> RW_TAC std_ss [sum]
   >> FULL_SIMP_TAC real_ss [positive_def, measure_def]);

val finite_additivity_sufficient_for_finite_spaces2 = store_thm
  ("finite_additivity_sufficient_for_finite_spaces2",
  ``!m. sigma_algebra (m_space m, measurable_sets m) /\ FINITE (m_space m) /\
        positive m /\ additive m ==> measure_space m``,
   rpt STRIP_TAC
   >> Suff `measure_space (space (m_space m, measurable_sets m),
                           subsets (m_space m, measurable_sets m), measure m)`
   >- RW_TAC std_ss [space_def, subsets_def, MEASURE_SPACE_REDUCE]
   >> MATCH_MP_TAC finite_additivity_sufficient_for_finite_spaces
   >> RW_TAC std_ss [space_def, subsets_def, MEASURE_SPACE_REDUCE]);

val MEASURE_SPACE_INCREASING = store_thm
  ("MEASURE_SPACE_INCREASING",``!m. measure_space m ==> increasing m``,
  RW_TAC real_ss [] >> `additive m` by RW_TAC real_ss [MEASURE_SPACE_ADDITIVE]
  >> FULL_SIMP_TAC real_ss [measure_space_def,sigma_algebra_def,ADDITIVE_INCREASING]);

val MEASURE_SPACE_POSITIVE = store_thm
  ("MEASURE_SPACE_POSITIVE",``!m. measure_space m ==> positive m``,
  PROVE_TAC [measure_space_def]);

val MEASURE_SPACE_INTER = store_thm
  ("MEASURE_SPACE_INTER",``!m s t. (measure_space m) /\ (s IN measurable_sets m) /\
                        (t IN measurable_sets m) ==> (s INTER t IN measurable_sets m)``,
  METIS_TAC [measure_space_def,sigma_algebra_def,subsets_def,
            (REWRITE_RULE [subsets_def] (Q.SPEC `(m_space m,measurable_sets m)` ALGEBRA_INTER))]);

val MEASURE_SPACE_UNION = store_thm
  ("MEASURE_SPACE_UNION",``!m s t. (measure_space m) /\ (s IN measurable_sets m) /\
                              (t IN measurable_sets m) ==> (s UNION t IN measurable_sets m)``,
  METIS_TAC [measure_space_def,sigma_algebra_def,subsets_def,
              (REWRITE_RULE [subsets_def] (Q.SPEC `(m_space m,measurable_sets m)`
              ALGEBRA_UNION))]);

val MEASURE_SPACE_DIFF = store_thm
  ("MEASURE_SPACE_DIFF",``!m s t. (measure_space m) /\ (s IN measurable_sets m) /\
                    (t IN measurable_sets m) ==> (s DIFF t IN measurable_sets m)``,
   METIS_TAC [measure_space_def,sigma_algebra_def,subsets_def,
       (REWRITE_RULE [subsets_def] (Q.SPEC `(m_space m,measurable_sets m)` ALGEBRA_DIFF))]);

val MEASURE_COMPL_SUBSET = store_thm
  ("MEASURE_COMPL_SUBSET",
   ``!m s t.
       measure_space m /\ s IN measurable_sets m /\ t IN measurable_sets m /\ (t SUBSET s) ==>
       (measure m (s DIFF t) = measure m s - measure m t)``,
   RW_TAC std_ss []
   >> Suff `measure m s = measure m t + measure m (s DIFF t)`
   >- REAL_ARITH_TAC
   >> MATCH_MP_TAC ADDITIVE
   >> Q.PAT_X_ASSUM `measure_space m` MP_TAC
   >> RW_TAC std_ss [measure_space_def, sigma_algebra_def, DISJOINT_DEF,
                            EXTENSION, IN_DIFF, IN_UNIV, IN_UNION, IN_INTER,
                            NOT_IN_EMPTY]
   >> METIS_TAC [COUNTABLY_ADDITIVE_ADDITIVE,MEASURE_SPACE_DIFF,measure_space_def,
                 sigma_algebra_def,SUBSET_DEF]);

val MEASURE_SPACE_BIGUNION = store_thm
  ("MEASURE_SPACE_BIGUNION",``!m s. measure_space m /\ (!n:num. s n IN measurable_sets m)
              ==> (BIGUNION (IMAGE s UNIV) IN measurable_sets m)``,
  RW_TAC std_ss []
  >> (MP_TAC o REWRITE_RULE [subsets_def,space_def,IN_UNIV,IN_FUNSET] o
               Q.SPEC `(m_space m,measurable_sets m)`) SIGMA_ALGEBRA_FN
  >> METIS_TAC [measure_space_def]);

val MEASURE_SPACE_IN_MSPACE = store_thm
  ("MEASURE_SPACE_IN_MSPACE",``!m A. measure_space m /\ A IN measurable_sets m
             ==> (!x. x IN A ==> x IN m_space m)``,
   METIS_TAC [measure_space_def,sigma_algebra_def,algebra_def,measurable_sets_def,space_def,
              subset_class_def,subsets_def,SUBSET_DEF]);

val MEASURE_SPACE_SUBSET_MSPACE = store_thm
  ("MEASURE_SPACE_SUBSET_MSPACE", ``!A m. measure_space m /\ A IN measurable_sets m
                  ==> A SUBSET m_space m``,
   RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,subset_class_def,
                  subsets_def, space_def]);

val MEASURE_SPACE_EMPTY_MEASURABLE = store_thm
  ("MEASURE_SPACE_EMPTY_MEASURABLE",``!m. measure_space m
                              ==> {} IN measurable_sets m``,
   RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,subsets_def, space_def]);

val MEASURE_SPACE_MSPACE_MEASURABLE = store_thm
  ("MEASURE_SPACE_MSPACE_MEASURABLE",``!m. measure_space m ==> (m_space m) IN measurable_sets m``,
   RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def, subsets_def, space_def]
   >> METIS_TAC [DIFF_EMPTY]);

val MEASURE_SPACE_BIGINTER = store_thm
  ("MEASURE_SPACE_BIGINTER",``!m s. measure_space m /\ (!n:num. s n IN measurable_sets m)
                  ==> (BIGINTER (IMAGE s UNIV) IN measurable_sets m)``,
  RW_TAC std_ss []
  >> (MP_TAC o REWRITE_RULE [subsets_def,space_def,IN_UNIV,IN_FUNSET] o
               Q.SPEC `(m_space m,measurable_sets m)`) SIGMA_ALGEBRA_FN_BIGINTER
  >> METIS_TAC [measure_space_def]);

val MONOTONE_CONVERGENCE2 = store_thm
  ("MONOTONE_CONVERGENCE2", ``!m f. measure_space m /\
       f IN (UNIV -> measurable_sets m) /\ (!n. f n SUBSET f (SUC n)) ==>
       (measure m o f --> measure m (BIGUNION (IMAGE f UNIV)))``,
  METIS_TAC [MONOTONE_CONVERGENCE]);

val MONOTONE_CONVERGENCE_BIGINTER = store_thm
  ("MONOTONE_CONVERGENCE_BIGINTER",
   ``!m s f.
       measure_space m /\ f IN (UNIV -> measurable_sets m) /\
       (!n. f (SUC n) SUBSET f n) /\ (s = BIGINTER (IMAGE f UNIV)) ==>
       measure m o f --> measure m s``,
  RW_TAC std_ss [IN_FUNSET, IN_UNIV]
  >> `BIGINTER (IMAGE f UNIV) IN measurable_sets m` by METIS_TAC [MEASURE_SPACE_BIGINTER]
  >> `!n. f n SUBSET f 0`
       by (Induct_on `n` >- RW_TAC std_ss [SUBSET_REFL]
             >> METIS_TAC [SUBSET_TRANS])
  >> `BIGINTER (IMAGE f UNIV) SUBSET (f 0)`
       by (MATCH_MP_TAC BIGINTER_SUBSET
           >> METIS_TAC [IMAGE_EQ_EMPTY,UNIV_NOT_EMPTY,IN_IMAGE,IN_UNIV])
  >> Q.ABBREV_TAC `g = (\n. (f 0) DIFF (f n))`
  >> FULL_SIMP_TAC std_ss [o_DEF]
  >> `!n. measure m (f 0) - measure m (f n) = measure m (g n)` by METIS_TAC [MEASURE_COMPL_SUBSET]
  >> `(\x. measure m (f x)) = (\x. (\x. measure m (f 0)) x - (\x. measure m (g x)) x)`
       by (RW_TAC std_ss [FUN_EQ_THM]
           >> METIS_TAC [REAL_EQ_SUB_LADD,REAL_EQ_SUB_RADD,real_sub,REAL_ADD_COMM])
  >> POP_ORW
  >> `BIGINTER (IMAGE f UNIV) = (f 0) DIFF BIGUNION (IMAGE (\u. (f 0) DIFF u) (IMAGE f UNIV))`
      by (MATCH_MP_TAC DIFF_BIGINTER
          >> METIS_TAC [IN_IMAGE,IN_UNIV,IMAGE_EQ_EMPTY,UNIV_NOT_EMPTY])
  >> POP_ORW
  >> `BIGUNION (IMAGE (\u. f 0 DIFF u) (IMAGE f UNIV)) = BIGUNION (IMAGE (\n. f 0 DIFF f n) UNIV)`
        by (RW_TAC std_ss [EXTENSION,IN_BIGUNION_IMAGE,IN_UNIV,IN_IMAGE]
            >> METIS_TAC [SUBSET_DEF,IN_DIFF])
  >> POP_ORW
  >> RW_TAC std_ss []
  >> `(\n. measure m (g n)) --> measure m (BIGUNION (IMAGE g UNIV))`
       by ((MATCH_MP_TAC o REWRITE_RULE [o_DEF]) MONOTONE_CONVERGENCE2
           >> RW_TAC std_ss [IN_FUNSET,IN_UNIV]
           >- METIS_TAC [MEASURE_SPACE_DIFF]
           >> Q.UNABBREV_TAC `g`
           >> RW_TAC std_ss [SUBSET_DEF,IN_DIFF,GSPECIFICATION]
           >> METIS_TAC [SUBSET_DEF])
  >> Suff `measure m (f 0 DIFF BIGUNION (IMAGE (\n. f 0 DIFF f n) UNIV)) =
           measure m (f 0) - measure m (BIGUNION (IMAGE (\n. f 0 DIFF f n) UNIV))`
  >- (RW_TAC std_ss []
      >> `(\x. measure m (f 0) - measure m (g x)) =
          (\x. (\x. measure m (f 0)) x - (\x. measure m (g x)) x)`
            by RW_TAC std_ss [FUN_EQ_THM]
      >> POP_ORW
      >> MATCH_MP_TAC SEQ_SUB
      >> METIS_TAC [SEQ_CONST])
  >> MATCH_MP_TAC MEASURE_COMPL_SUBSET
  >> RW_TAC std_ss []
  >- (MATCH_MP_TAC MEASURE_SPACE_BIGUNION
      >> METIS_TAC [MEASURE_SPACE_DIFF])
  >> RW_TAC std_ss [BIGUNION_SUBSET,IN_IMAGE,IN_UNIV]
  >> METIS_TAC [DIFF_SUBSET]);

val MONOTONE_CONVERGENCE_BIGINTER2 = store_thm
  ("MONOTONE_CONVERGENCE_BIGINTER2",
   ``!m f. measure_space m /\ f IN (UNIV -> measurable_sets m) /\
       (!n. f (SUC n) SUBSET f n) ==>
       measure m o f --> measure m (BIGINTER (IMAGE f UNIV))``,
  METIS_TAC [MONOTONE_CONVERGENCE_BIGINTER]);

val MEASURE_SPACE_RESTRICTED = store_thm
  ("MEASURE_SPACE_RESTRICTED",
  ``!m s. measure_space m /\ s IN measurable_sets m ==>
          measure_space (s, IMAGE (\t. s INTER t) (measurable_sets m), measure m)``,
  RW_TAC std_ss []
  >> `positive (s,IMAGE (\t. s INTER t) (measurable_sets m),measure m)`
        by (RW_TAC std_ss [positive_def,measure_def,measurable_sets_def,IN_IMAGE]
            >> METIS_TAC [MEASURE_SPACE_POSITIVE,MEASURE_SPACE_INTER,positive_def])
  >> `countably_additive (s,IMAGE (\t. s INTER t) (measurable_sets m),measure m)`
        by (RW_TAC std_ss [countably_additive_def,measure_def,measurable_sets_def,
                           IN_IMAGE,IN_FUNSET,IN_UNIV]
            >> `!x. f x IN measurable_sets m` by METIS_TAC [MEASURE_SPACE_INTER]
            >> `BIGUNION (IMAGE f univ(:num)) IN measurable_sets m`
                 by METIS_TAC [MEASURE_SPACE_INTER]
            >> `countably_additive m` by METIS_TAC [measure_space_def]
            >> FULL_SIMP_TAC std_ss [countably_additive_def,IN_FUNSET,IN_UNIV])
  >> RW_TAC std_ss [measure_space_def,sigma_algebra_def,measurable_sets_def,subsets_def,
                    m_space_def,IN_IMAGE]
  >- (RW_TAC std_ss [algebra_def,space_def,subsets_def,subset_class_def,IN_IMAGE]
      >| [RW_TAC std_ss [INTER_SUBSET],
          METIS_TAC [INTER_EMPTY,MEASURE_SPACE_EMPTY_MEASURABLE],
          Q.EXISTS_TAC `m_space m DIFF t`
          >> RW_TAC std_ss [MEASURE_SPACE_DIFF,MEASURE_SPACE_MSPACE_MEASURABLE,EXTENSION,
                            IN_DIFF,IN_INTER]
          >> METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE,SUBSET_DEF],
          Q.EXISTS_TAC `t' UNION t''`
          >> RW_TAC std_ss [MEASURE_SPACE_UNION,UNION_OVER_INTER]])
  >> `BIGUNION c SUBSET s`
       by (RW_TAC std_ss [SUBSET_DEF,IN_BIGUNION]
           >> FULL_SIMP_TAC std_ss [SUBSET_DEF,IN_IMAGE]
           >> `?t. (s' = s INTER t) /\ t IN measurable_sets m` by METIS_TAC []
           >> METIS_TAC [IN_INTER])
  >> Q.EXISTS_TAC `BIGUNION c`
  >> RW_TAC std_ss [SUBSET_INTER2]
  >> Suff `BIGUNION c IN subsets (m_space m, measurable_sets m)`
  >- RW_TAC std_ss [subsets_def]
  >> MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION
  >> RW_TAC std_ss [subsets_def]
  >- FULL_SIMP_TAC std_ss [measure_space_def]
  >> FULL_SIMP_TAC std_ss [SUBSET_DEF,IN_IMAGE]
  >> METIS_TAC [MEASURE_SPACE_INTER]);

val MEASURE_SPACE_CMUL = store_thm
  ("MEASURE_SPACE_CMUL", ``!m c. measure_space m /\ 0 <= c ==>
                   measure_space (m_space m, measurable_sets m, (\a. c * measure m a))``,
  RW_TAC real_ss [measure_space_def,m_space_def,measurable_sets_def,measure_def,positive_def]
  >- METIS_TAC [REAL_LE_MUL]
  >> RW_TAC std_ss [countably_additive_def,measure_def,measurable_sets_def,o_DEF]
  >> METIS_TAC [SER_CMUL,countably_additive_def]);

Theorem borel_measurable_le_iff :
    !m. measure_space m ==>
        !f. f IN borel_measurable (m_space m, measurable_sets m) <=>
            !a. {w | w IN m_space m /\ f w <= a} IN measurable_sets m
Proof
    RW_TAC std_ss [measure_space_def, in_borel_measurable_le,
                   space_def, subsets_def, IN_FUNSET, IN_UNIV]
QED

Theorem borel_measurable_gr_iff :
    !m. measure_space m ==>
        !f. f IN borel_measurable (m_space m, measurable_sets m) <=>
            !a. {w | w IN m_space m /\ a < f w} IN measurable_sets m
Proof
    RW_TAC std_ss [measure_space_def, in_borel_measurable_gr,
                   space_def, subsets_def, IN_FUNSET, IN_UNIV]
QED

Theorem borel_measurable_less_iff :
    !m. measure_space m ==>
        !f. f IN borel_measurable (m_space m, measurable_sets m) <=>
            !a. {w | w IN m_space m /\ f w < a} IN measurable_sets m
Proof
    RW_TAC std_ss [measure_space_def, in_borel_measurable_less,
                   space_def, subsets_def, IN_FUNSET, IN_UNIV]
QED

Theorem borel_measurable_ge_iff :
    !m. measure_space m ==>
        !f. f IN borel_measurable (m_space m, measurable_sets m) <=>
            !a. {w | w IN m_space m /\ a <= f w} IN measurable_sets m
Proof
    RW_TAC std_ss [measure_space_def, in_borel_measurable_ge,
                   space_def, subsets_def, IN_FUNSET, IN_UNIV]
QED

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
   >> reverse (Cases_on `b < 0`)
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
            >> reverse (Cases_on `(x IN m_space m)`) >> RW_TAC std_ss []
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
            >> reverse EQ_TAC
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
