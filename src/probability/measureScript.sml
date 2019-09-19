(* ------------------------------------------------------------------------- *)
(* Measure Theory defined on the extended reals                              *)
(* Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar (2013, 2015) [2]        *)
(* HVG Group, Concordia University, Montreal                                 *)
(*                                                                           *)
(* Measures are now in the range [0, +infinity] (type: 'a set -> extreal)    *)
(* ------------------------------------------------------------------------- *)
(* Based on the work of Joe Hurd [4] (2001) and Aaron Coble [7] (2010)       *)
(* Cambridge University.                                                     *)
(* ------------------------------------------------------------------------- *)
(* The Uniqueness and Existence of Measure                                   *)
(*                                                                           *)
(* Author: Chun Tian (2018, 2019)                                            *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(*                                                                           *)
(* Caratheodory's extension theorem (real_measureTheory.CARATHEODORY) was    *)
(* originally proved by Joe Hurd [4] under algebra and [0, +inf) measure.    *)
(* The theorem is now reproved under semiring and [0, +inf] measure.         *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open prim_recTheory arithmeticTheory optionTheory pairTheory
     numpairTheory combinTheory pred_setTheory;

open realTheory realLib seqTheory transcTheory real_sigmaTheory;

open hurdUtils util_probTheory extrealTheory sigma_algebraTheory;

val _ = new_theory "measure";

val SET_SPEC_TAC = SIMP_TAC (std_ss ++ SET_SPEC_ss);

(* from cardinalTheory *)
fun PRINT_TAC s gl = (print ("** " ^ s ^ "\n"); ALL_TAC gl);

val _ = hide "S"; (* TODO: remove all uses of `S` *)

(* ------------------------------------------------------------------------- *)
(*  Basic measure theory definitions.                                        *)
(* ------------------------------------------------------------------------- *)

val _ = type_abbrev_pp ("measure", ``:'a set -> extreal``);
val _ = type_abbrev_pp ("m_space", ``:'a set # 'a set set # 'a measure``);

(* These're accessors of the triple of measure space *)
val m_space_def = Define
   `m_space         (sp :'a set, sts :('a set) set, mu :('a set) -> extreal) = sp`;

val measurable_sets_def = Define
   `measurable_sets (sp :'a set, sts :('a set) set, mu :('a set) -> extreal) = sts`;

val measure_def = Define
   `measure         (sp :'a set, sts :('a set) set, mu :('a set) -> extreal) = mu`;

(* NOTE: `{} IN measurable_sets m` is not assumed, instead it must be provided by
   definition of the system of sets. *)
val positive_def = Define
   `positive m <=>
    (measure m {} = 0) /\ !s. s IN measurable_sets m ==> 0 <= measure m s`;

(* NOTE: add ``s UNION t IN measurable_sets m`` into antecedents, like in the
   case of "countably_additive_def", because otherwise this definition only works
   with system of sets stable under (finite) union. *)
val additive_def = Define
   `additive m =
    !s t. s IN measurable_sets m /\ t IN measurable_sets m /\ DISJOINT s t /\
          s UNION t IN measurable_sets m
      ==> (measure m (s UNION t) = measure m s + measure m t)`;

(* to derive finite additivity from countable additivity for all systems *)
val finite_additive_def = Define (* new *)
   `finite_additive m =
    !f :num -> ('a -> bool) n.
     (!i. i < n ==> f i IN measurable_sets m) /\
     (!i j. i < n /\ j < n /\ i <> j ==> DISJOINT (f i) (f j)) /\
     BIGUNION (IMAGE f (count n)) IN measurable_sets m ==>
     (measure m (BIGUNION (IMAGE f (count n))) = SIGMA (measure m o f) (count n))`;

(* NOTE: ``summable (measure m o f)`` was removed from the antecedents *)
val countably_additive_def = Define
   `countably_additive m =
    !f :num -> ('a -> bool).
     f IN (UNIV -> measurable_sets m) /\
     (!i j. i <> j ==> DISJOINT (f i) (f j)) /\
     BIGUNION (IMAGE f UNIV) IN measurable_sets m ==>
     (measure m (BIGUNION (IMAGE f UNIV)) = suminf (measure m o f))`;

(* NOTE: added ``s UNION t IN measurable_sets m`` into antecedents *)
val subadditive_def = Define
   `subadditive m =
    !s t. s IN measurable_sets m /\ t IN measurable_sets m /\
          s UNION t IN measurable_sets m
      ==> measure m (s UNION t) <= measure m s + measure m t`;

val finite_subadditive_def = Define (* new *)
   `finite_subadditive m =
    !f :num -> ('a set) n.
     (!i. i < n ==> f i IN measurable_sets m) /\
     BIGUNION (IMAGE f (count n)) IN measurable_sets m  ==>
     measure m (BIGUNION (IMAGE f (count n))) <= SIGMA (measure m o f) (count n)`;

val countably_subadditive_def = Define
   `countably_subadditive m =
    !f :num -> ('a set).
     f IN (UNIV -> measurable_sets m) /\
     BIGUNION (IMAGE f UNIV) IN measurable_sets m  ==>
     measure m (BIGUNION (IMAGE f UNIV)) <= suminf (measure m o f)`;

val increasing_def = Define
   `increasing m =
    !s t.
     s IN measurable_sets m /\ t IN measurable_sets m /\ s SUBSET t ==>
     measure m s <= measure m t`;

val measure_space_def = Define
   `measure_space m <=>
      sigma_algebra (m_space m, measurable_sets m) /\ positive m /\ countably_additive m`;

(* The set of measurable mappings, each (f :'a -> 'b) is called A/B-measurable *)
val measurable_def = Define
   `measurable a b = {f | sigma_algebra a /\ sigma_algebra b /\
                          f IN (space a -> space b) /\
                          !s. s IN subsets b ==> ((PREIMAGE f s) INTER (space a)) IN subsets a}`;

(* The set of measure-preserving measurable mappings.
   NOTE: ``measure_space m1 /\ measure_space m2`` was removed. *)
val measure_preserving_def = Define
   `measure_preserving m1 m2 =
    {f |
     f IN measurable (m_space m1, measurable_sets m1) (m_space m2, measurable_sets m2) /\
     !s.
      s IN measurable_sets m2 ==>
           (measure m1 ((PREIMAGE f s) INTER (m_space m1)) = measure m2 s)}`;


(* ------------------------------------------------------------------------- *)
(*  Basic measure theory theorems                                            *)
(* ------------------------------------------------------------------------- *)

val positive_not_infty = store_thm
  ("positive_not_infty",
  ``!m. positive m ==>
         (!s. s IN measurable_sets m ==> measure m s <> NegInf)``,
    RW_TAC std_ss [positive_def]
 >> METIS_TAC [lt_infty, extreal_of_num_def, extreal_not_infty, lte_trans]);

(* added `u IN measurable_sets m` into antecedents *)
val SUBADDITIVE = store_thm
  ("SUBADDITIVE",
   ``!m s t u.
       subadditive m /\ s IN measurable_sets m /\ t IN measurable_sets m /\
       u IN measurable_sets m /\ (u = s UNION t) ==>
       measure m u <= measure m s + measure m t``,
    RW_TAC std_ss [subadditive_def]
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []);

(* added `u IN measurable_sets m` into antecedents *)
val ADDITIVE = store_thm
  ("ADDITIVE",
   ``!m s t u.
       additive m /\ s IN measurable_sets m /\ t IN measurable_sets m /\
       DISJOINT s t /\ u IN measurable_sets m /\ (u = s UNION t) ==>
       (measure m u = measure m s + measure m t)``,
    RW_TAC std_ss [additive_def]
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []);

(* removed `summable (measure m o f)` *)
val COUNTABLY_SUBADDITIVE = store_thm
  ("COUNTABLY_SUBADDITIVE",
   ``!m f s.
       countably_subadditive m /\ f IN (UNIV -> measurable_sets m) /\
       (s = BIGUNION (IMAGE f UNIV)) /\
       (s IN measurable_sets m) ==>
       (measure m s <= suminf (measure m o f))``,
   PROVE_TAC [countably_subadditive_def]);

val ADDITIVE_SUM = store_thm
  ("ADDITIVE_SUM",
   ``!m f n.
       algebra (m_space m, measurable_sets m) /\ positive m /\ additive m /\
       f IN (UNIV -> measurable_sets m) /\
       (!m n : num. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
       (SIGMA (measure m o f) (count n) =
        measure m (BIGUNION (IMAGE f (count n))))``,
   RW_TAC std_ss [IN_FUNSET, IN_UNIV]
   >> Induct_on `n`
   >- (RW_TAC std_ss [COUNT_ZERO,EXTREAL_SUM_IMAGE_EMPTY,IMAGE_EMPTY,BIGUNION_EMPTY]
       >> PROVE_TAC [positive_def])
   >> `FINITE (count n)` by PROVE_TAC [FINITE_COUNT]
   >> `!x. (measure m o f) x <> NegInf` by METIS_TAC [positive_not_infty,o_DEF]
   >> RW_TAC std_ss [COUNT_SUC, IMAGE_INSERT, BIGUNION_INSERT,EXTREAL_SUM_IMAGE_PROPERTY]
   >> `(IMAGE f (count n)) SUBSET measurable_sets m` by METIS_TAC [SUBSET_DEF,IN_IMAGE]
   >> `measurable_sets m = subsets (m_space m,measurable_sets m)`
        by (METIS_TAC [subsets_def,measurable_sets_def])
   >> `BIGUNION (IMAGE f (count n)) IN measurable_sets m`
          by (RW_TAC std_ss []
              >> METIS_TAC [ALGEBRA_FINITE_UNION,IMAGE_FINITE])
   >> `DISJOINT (f n) (BIGUNION (IMAGE f (count n)))`
       by (RW_TAC std_ss [DISJOINT_BIGUNION,IN_IMAGE,IN_COUNT]
           >> `x <> n` by RW_TAC real_ss []
           >> METIS_TAC [])
   >> `(count n) DELETE n = count n` by RW_TAC real_ss [EXTENSION,IN_DELETE,IN_COUNT]
   >> POP_ORW >> art []
   >> MATCH_MP_TAC (GSYM ADDITIVE)
   >> METIS_TAC [ALGEBRA_UNION]);

val INCREASING = store_thm
  ("INCREASING",
   ``!m s t.
       increasing m /\ s SUBSET t /\ s IN measurable_sets m /\
       t IN measurable_sets m ==>
       measure m s <= measure m t``,
   PROVE_TAC [increasing_def]);

(* This result holds as long as m is a ring, c.f. RING_ADDITIVE_INCREASING *)
val ADDITIVE_INCREASING = store_thm (* merged *)
  ("ADDITIVE_INCREASING",
   ``!m. algebra (m_space m, measurable_sets m) /\ positive m /\ additive m ==>
         increasing m``,
   RW_TAC std_ss [increasing_def, positive_def]
   >> Suff
      `?u. u IN measurable_sets m /\ (measure m t = measure m s + measure m u)`
   >- METIS_TAC [le_addr_imp]
   >> Q.EXISTS_TAC `t DIFF s`
   >> STRONG_CONJ_TAC >- PROVE_TAC [ALGEBRA_DIFF, subsets_def]
   >> RW_TAC std_ss []
   >> MATCH_MP_TAC ADDITIVE
   >> RW_TAC std_ss [DISJOINT_DEF,IN_DIFF,IN_UNION,EXTENSION,IN_INTER,NOT_IN_EMPTY]
   >> PROVE_TAC [SUBSET_DEF]);

val FINITE_ADDITIVE = store_thm
  ("FINITE_ADDITIVE",
  ``!m s f n.
       finite_additive m /\ (!i. i < n ==> f i IN measurable_sets m)
       /\ (!i j. i < n /\ j < n /\ i <> j ==> DISJOINT (f i) (f j)) /\
       (s = BIGUNION (IMAGE f (count n))) /\ s IN measurable_sets m ==>
       (SIGMA (measure m o f) (count n) = measure m s)``,
    RW_TAC std_ss [finite_additive_def]
 >> MATCH_MP_TAC EQ_SYM
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []);

val FINITE_ADDITIVE_ALT = store_thm
  ("FINITE_ADDITIVE_ALT",
  ``!m s c.
       positive m /\ finite_additive m /\ c SUBSET measurable_sets m /\
       FINITE c /\ disjoint c /\ BIGUNION c IN measurable_sets m ==>
       (SIGMA (measure m) c = measure m (BIGUNION c))``,
    RW_TAC std_ss [finite_additive_def]
 >> STRIP_ASSUME_TAC (MATCH_MP finite_disjoint_decomposition
                               (CONJ (ASSUME ``FINITE (c :'a set set)``)
                                     (ASSUME ``disjoint (c :'a set set)``)))
 >> ASM_REWRITE_TAC []
 >> Know `measure m (BIGUNION (IMAGE f (count n))) = SIGMA (measure m o f) (count n)`
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> art [] \\
     CONJ_TAC >- PROVE_TAC [SUBSET_DEF] \\
     PROVE_TAC [])
 >> Rewr'
 >> irule EXTREAL_SUM_IMAGE_IMAGE
 >> REWRITE_TAC [FINITE_COUNT, IN_COUNT, IN_IMAGE]
 >> CONJ_TAC
 >- (DISJ1_TAC >> GEN_TAC >> STRIP_TAC >> MATCH_MP_TAC pos_not_neginf >> art [] \\
    `f x' IN measurable_sets m` by PROVE_TAC [SUBSET_DEF] \\
     fs [positive_def])
 >> MATCH_MP_TAC INJ_IMAGE
 >> Q.EXISTS_TAC `c`
 >> RW_TAC std_ss [INJ_DEF, IN_COUNT]
 >> METIS_TAC []);

val FINITE_SUBADDITIVE = store_thm
  ("FINITE_SUBADDITIVE",
  ``!m s f n.
       finite_subadditive m /\ (!i. i < n ==> f i IN measurable_sets m) /\
       (s = BIGUNION (IMAGE f (count n))) /\ s IN measurable_sets m ==>
       measure m s <= SIGMA (measure m o f) (count n)``,
    RW_TAC std_ss [finite_subadditive_def]
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []);

val FINITE_SUBADDITIVE_ALT = store_thm
  ("FINITE_SUBADDITIVE_ALT",
  ``!m c.
       positive m /\ finite_subadditive m /\ c SUBSET measurable_sets m /\
       FINITE c /\ disjoint c /\ BIGUNION c IN measurable_sets m ==>
       measure m (BIGUNION c) <= SIGMA (measure m) c``,
    RW_TAC std_ss [finite_subadditive_def]
 >> STRIP_ASSUME_TAC (MATCH_MP finite_disjoint_decomposition
                               (CONJ (ASSUME ``FINITE (c :'a set set)``)
                                     (ASSUME ``disjoint (c :'a set set)``)))
 >> ASM_REWRITE_TAC []
 >> Know `measure m (BIGUNION (IMAGE f (count n))) <= SIGMA (measure m o f) (count n)`
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> art [] \\
     CONJ_TAC >- PROVE_TAC [SUBSET_DEF] \\
     PROVE_TAC [])
 >> DISCH_TAC
 >> Suff `SIGMA (measure m) (IMAGE f (count n)) = SIGMA (measure m o f) (count n)`
 >- METIS_TAC []
 >> irule EXTREAL_SUM_IMAGE_IMAGE
 >> REWRITE_TAC [FINITE_COUNT, IN_COUNT, IN_IMAGE]
 >> CONJ_TAC
 >- (DISJ1_TAC >> GEN_TAC >> STRIP_TAC >> MATCH_MP_TAC pos_not_neginf >> art [] \\
    `f x' IN measurable_sets m` by PROVE_TAC [SUBSET_DEF] \\
     fs [positive_def])
 >> MATCH_MP_TAC INJ_IMAGE
 >> Q.EXISTS_TAC `c`
 >> RW_TAC std_ss [INJ_DEF, IN_COUNT]
 >> METIS_TAC []);

val COUNTABLY_ADDITIVE = store_thm
  ("COUNTABLY_ADDITIVE",
   ``!m s f.
       countably_additive m /\ f IN (UNIV -> measurable_sets m)
       /\ (!i j. i <> j ==> DISJOINT (f i) (f j)) /\
       (s = BIGUNION (IMAGE f UNIV)) /\ s IN measurable_sets m ==>
       (suminf (measure m o f) =  measure m s)``,
   RW_TAC std_ss []
   >> PROVE_TAC [countably_additive_def]);

val COUNTABLY_ADDITIVE_ADDITIVE_lemma = Q.prove (
   `!m s t. {} IN measurable_sets m /\ (measure m {} = 0) /\
        (!s. s IN measurable_sets m ==> 0 <= measure m s) /\
         s IN measurable_sets m /\ t IN measurable_sets m ==>
        (suminf (measure m o (\n. if n = 0 then s else if n = 1 then t else {})) =
         measure m s + measure m t)`,
    rpt STRIP_TAC
 >> `FINITE (count 2)` by RW_TAC std_ss [FINITE_COUNT]
 >> `!n. FINITE ((count n) DIFF (count 2))` by METIS_TAC [FINITE_COUNT, FINITE_DIFF]
 >> `!n:num. (2 <= n) ==>
         (SIGMA (\n. measure m (if n = 0 then s else if n = 1 then t else {})) (count n) =
          SIGMA (\n. measure m (if n = 0 then s else if n = 1 then t else {})) (count 2))`
           by (Q.ABBREV_TAC `f = (\n:num. measure m (if n = 0 then s else if n = 1 then t else {}))`
               >> RW_TAC std_ss []
               >> `count 2 SUBSET (count n)` by RW_TAC real_ss [SUBSET_DEF,IN_COUNT]
               >> `(count n) = (count 2) UNION ((count n) DIFF (count 2))`
                   by RW_TAC std_ss [UNION_DIFF]
               >> `DISJOINT (count 2) ((count n) DIFF (count 2))`
                    by RW_TAC real_ss [EXTENSION,IN_DISJOINT, IN_COUNT,IN_DIFF]
               >> `!n. f n <> NegInf`
                   by (Q.UNABBREV_TAC `f`
                       >> RW_TAC std_ss []
                       >> METIS_TAC [positive_def,positive_not_infty,extreal_of_num_def,
                                     extreal_not_infty])
               >> (MP_TAC o (Q.SPECL [`count 2`,`count n DIFF count 2`]) o
                   (INST_TYPE [alpha |-> ``:num``])) EXTREAL_SUM_IMAGE_DISJOINT_UNION
               >> FULL_SIMP_TAC std_ss []
               >> Suff `SIGMA f (count n DIFF count 2) = 0` >- METIS_TAC [add_rzero]
               >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
               >> RW_TAC std_ss [IN_COUNT,IN_DIFF,NOT_LESS]
               >> Q.UNABBREV_TAC `f`
               >> RW_TAC real_ss [])
 >> `SIGMA (\n. measure m (if n = 0 then s else if n = 1 then t else {})) (count 2) =
       measure m s + measure m t`
         by (`count 2 = (1:num) INSERT {0}`
                by METIS_TAC [TWO,ONE,COUNT_SUC,EXTENSION, IN_INSERT,COUNT_ZERO]
           >> `~(0=1:num)` by RW_TAC real_ss []
           >> `{0:num} DELETE 1 = {0}` by METIS_TAC [DELETE_NON_ELEMENT,IN_SING]
           >> (MP_TAC o (Q.SPEC `1:num` o REWRITE_RULE [FINITE_SING]) o
               (Q.SPECL [`(measure m o (\n. if n = 0 then s else if n = 1 then t else {}))`,
                         `{0:num}`]))
                  (INST_TYPE [``:'a`` |-> ``:num`` ] EXTREAL_SUM_IMAGE_PROPERTY)
           >> RW_TAC real_ss [EXTREAL_SUM_IMAGE_SING,o_DEF]
           >> `measure m s + measure m t = measure m t + measure m s`
                by METIS_TAC [positive_def,positive_not_infty,add_comm]
           >> POP_ORW
           >> POP_ASSUM MATCH_MP_TAC
           >> DISJ1_TAC
           >> RW_TAC real_ss [] >> METIS_TAC [positive_def,positive_not_infty,
                                              add_comm,extreal_of_num_def,extreal_not_infty])
 (* stage work *)
 >> Know `!i:num. 0 <= (measure m o (\n. if n = 0 then s else if n = 1
                                         then t else {})) i`
 >- RW_TAC std_ss [o_DEF]
 >> DISCH_THEN (MP_TAC o (MATCH_MP ext_suminf_alt_pos)) >> Rewr'
 >> RW_TAC std_ss [sup_eq', o_DEF, IN_IMAGE, IN_UNIV]
 >- (Cases_on `2 <= n` >- METIS_TAC [le_refl] \\
    `(n = 0) \/ (n = 1)` by RW_TAC real_ss []
     >- RW_TAC real_ss [COUNT_ZERO, EXTREAL_SUM_IMAGE_EMPTY, le_add] \\
    `count 1 = {0}` by RW_TAC real_ss [EXTENSION, IN_COUNT, IN_SING] \\
     FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_SING, le_addr_imp])
 >> Suff `(measure m s + measure m t) IN
            IMAGE (\n. SIGMA (\n. measure m (if n = 0 then s else if n = 1 then t else {}))
                             (count n)) univ(:num)`
 >- METIS_TAC [IN_DEF]
 >> RW_TAC std_ss [IN_IMAGE, IN_UNIV]
 >> Q.EXISTS_TAC `2`
 >> METIS_TAC []);

(* removed `algebra (m_space m, measurable_sets m)` from antecedents,
   added `{} IN measurable_sets m` into antecedents. *)
val COUNTABLY_ADDITIVE_ADDITIVE = store_thm
  ("COUNTABLY_ADDITIVE_ADDITIVE",
  ``!m. {} IN measurable_sets m /\ positive m /\ countably_additive m ==> additive m``,
(* proof *)
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
   >> Rewr
   >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
   >> `!n:num. (if n = 0 then s else if n = 1 then t else {}) IN measurable_sets m`
       by METIS_TAC []
   >> `!m n:num. m <> n ==> DISJOINT (if m = 0 then s else if m = 1 then t else {})
               (if n = 0 then s else if n = 1 then t else {})`
               by RW_TAC real_ss [DISJOINT_EMPTY, DISJOINT_SYM]
   >> FULL_SIMP_TAC std_ss []
   >> NTAC 5 (POP_ASSUM K_TAC)
   (* now use the lemma instead *)
   >> MATCH_MP_TAC COUNTABLY_ADDITIVE_ADDITIVE_lemma >> art []);

Theorem COUNTABLY_SUBADDITIVE_SUBADDITIVE :
    !m. {} IN measurable_sets m /\ positive m /\ countably_subadditive m ==>
        subadditive m
Proof
    RW_TAC std_ss [subadditive_def, positive_def, countably_subadditive_def]
 >> Q.PAT_X_ASSUM `!f. P f`
      (MP_TAC o Q.SPEC `\n : num. if n = 0 then s else if n = 1 then t else {}`)
 >> Know
    `BIGUNION
       (IMAGE (\n : num. (if n = 0 then s else (if n = 1 then t else {}))) UNIV) =
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
 >> Rewr
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `!n:num. (if n = 0 then s else if n = 1 then t else {}) IN measurable_sets m`
       by METIS_TAC []
 >> fs []
 >> POP_ASSUM K_TAC
 >> Suff `suminf (measure m o (\n. if n = 0 then s else if n = 1 then t else {})) =
          measure m s + measure m t` >- METIS_TAC []
 >> NTAC 2 (POP_ASSUM K_TAC)
 (* now use the lemma instead *)
 >> MATCH_MP_TAC COUNTABLY_ADDITIVE_ADDITIVE_lemma >> art []
QED

val COUNTABLY_ADDITIVE_FINITE_ADDITIVE_lemma = Q.prove (
   `!m f n. {} IN measurable_sets m /\ (measure m {} = 0) /\
        (!s. s IN measurable_sets m ==> 0 <= measure m s) /\
        (!i. i < n ==> f i IN measurable_sets m) ==>
        (suminf (measure m o (\i. if i < n then f i else {})) = SIGMA (measure m o f) (count n))`,
    rpt STRIP_TAC
 >> Know `!j. 0 <= (measure m o (\i. if i < n then f i else {})) j`
 >- RW_TAC std_ss [o_DEF, le_refl]
 >> DISCH_THEN (MP_TAC o (MATCH_MP ext_suminf_alt_pos)) >> Rewr
 >> RW_TAC std_ss [sup_eq, o_DEF, IN_IMAGE, IN_UNIV]
 >- (`y IN IMAGE (\n'. SIGMA (\i. measure m (if i < n then f i else {})) (count n')) univ(:num)`
        by METIS_TAC [IN_DEF] \\
     FULL_SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] \\
     Cases_on `n <= n'`
     >- (Know `SIGMA (\i. measure m (if i < n then f i else {})) (count n') =
               SIGMA (\i. measure m (if i < n then f i else {})) (count n)`
         >- (Q.ABBREV_TAC `g = (\i:num. measure m (if i < n then f i else {}))` \\
             `count n SUBSET count n'` by RW_TAC arith_ss [SUBSET_DEF, IN_COUNT] \\
             `count n UNION (count n' DIFF count n) = count n'` by RW_TAC std_ss [UNION_DIFF] \\
             (MP_TAC o (Q.SPECL [`count n`,`count n' DIFF count n`]) o
                   (INST_TYPE [alpha |-> ``:num``])) EXTREAL_SUM_IMAGE_DISJOINT_UNION \\
             `DISJOINT (count n) (count n' DIFF count n)`
                   by RW_TAC real_ss [EXTENSION, IN_DISJOINT, IN_COUNT, IN_DIFF] \\
             `FINITE (count n)` by PROVE_TAC [FINITE_COUNT] \\
             `FINITE (count n' DIFF count n)` by PROVE_TAC [FINITE_COUNT, FINITE_DIFF] \\
             `!n. g n <> NegInf`
                   by (Q.UNABBREV_TAC `g` >> RW_TAC std_ss [] \\
                       METIS_TAC [positive_def, positive_not_infty, extreal_of_num_def,
                                  extreal_not_infty]) \\
             FULL_SIMP_TAC std_ss [] \\
             rpt STRIP_TAC \\
             Suff `SIGMA g (count n' DIFF count n) = 0` >- METIS_TAC [add_rzero] \\
             MATCH_MP_TAC EXTREAL_SUM_IMAGE_0 \\
             RW_TAC std_ss [IN_COUNT, IN_DIFF, NOT_LESS] \\
             Q.UNABBREV_TAC `g` >> RW_TAC arith_ss []) \\
         Rewr \\
         irule EXTREAL_SUM_IMAGE_MONO \\
         RW_TAC std_ss [le_refl, IN_COUNT, FINITE_COUNT] \\
         DISJ1_TAC \\
         RW_TAC arith_ss [IN_COUNT] >> PROVE_TAC [le_not_infty]) \\
     Know `SIGMA (\x. measure m (f x)) (count n) =
           SIGMA (\x. if x IN count n then (\x. measure m (f x)) x else 0) (count n)`
     >- (irule EXTREAL_SUM_IMAGE_IN_IF \\
         REWRITE_TAC [FINITE_COUNT] >> DISJ1_TAC >> PROVE_TAC [IN_COUNT, le_not_infty]) \\
     Rewr >> SIMP_TAC std_ss [IN_COUNT] \\
     `(\i. measure m (if i < n then f i else {})) = (\x. if x < n then measure m (f x) else 0)`
        by METIS_TAC [] >> POP_ORW \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET >> REWRITE_TAC [FINITE_COUNT] \\
     CONJ_TAC >- RW_TAC arith_ss [SUBSET_DEF, IN_COUNT] \\
     RW_TAC std_ss [IN_COUNT])
 (* SIGMA (\x. measure m (f x)) (count n) <= y *)
 >> Know `SIGMA (\x. measure m (f x)) (count n) =
          SIGMA (\i. measure m (if i < n then f i else {})) (count n)`
 >- (Know `SIGMA (\x. measure m (f x)) (count n) =
           SIGMA (\x. if x IN count n then (\x. measure m (f x)) x else 0) (count n)`
     >- (irule EXTREAL_SUM_IMAGE_IN_IF \\
         REWRITE_TAC [FINITE_COUNT] >> DISJ1_TAC >> PROVE_TAC [IN_COUNT, le_not_infty]) \\
     Rewr >> SIMP_TAC std_ss [IN_COUNT] \\
     `(\x. if x < n then measure m (f x) else 0) = (\i. measure m (if i < n then (f i) else {}))`
        by METIS_TAC [] >> POP_ORW \\
     REWRITE_TAC [])
 >> Rewr
 >> POP_ASSUM MATCH_MP_TAC
 >> Suff `(SIGMA (\i. measure m (if i < n then f i else {})) (count n)) IN
          (IMAGE (\n'. SIGMA (\i. measure m (if i < n then f i else {})) (count n')) univ(:num))`
 >- METIS_TAC [IN_APP]
 >> SIMP_TAC std_ss [IN_IMAGE, IN_UNIV]
 >> Q.EXISTS_TAC `n`
 >> METIS_TAC []);

Theorem COUNTABLY_ADDITIVE_FINITE_ADDITIVE :
    !m. {} IN measurable_sets m /\ positive m /\ countably_additive m ==>
        finite_additive m
Proof
    RW_TAC std_ss [positive_def, countably_additive_def, finite_additive_def,
                   IN_FUNSET, IN_UNIV]
 >> Q.PAT_X_ASSUM `!f. P f` (MP_TAC o Q.SPEC `\i :num. if i < n then (f i) else {}`)
 >> Know
      `BIGUNION (IMAGE (\i :num. if i < n then (f i) else {}) UNIV) =
       BIGUNION (IMAGE f (count n))`
 >- (RW_TAC arith_ss [EXTENSION, IN_BIGUNION, IN_IMAGE, IN_UNIV, IN_UNION, IN_COUNT] \\
     EQ_TAC >> rpt STRIP_TAC >|
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC `s` \\
       CONJ_TAC >- (POP_ASSUM K_TAC >> art []) \\
       Q.EXISTS_TAC `i` >> PROVE_TAC [NOT_IN_EMPTY],
       (* goal 2 (of 2) *)
       Q.EXISTS_TAC `s` \\
       CONJ_TAC >- (NTAC 2 (POP_ASSUM K_TAC) >> art []) \\
       Q.EXISTS_TAC `x'` >> PROVE_TAC [NOT_IN_EMPTY] ]) >> Rewr
 >> RW_TAC std_ss []
 (* `{} IN measurable_sets m` is used here *)
 >> `!i:num. (if i < n then (f i) else {}) IN measurable_sets m` by METIS_TAC []
 >> `!i j:num. i <> j ==> DISJOINT (if i < n then (f i) else {})
                                   (if j < n then (f j) else {})`
               by RW_TAC real_ss [DISJOINT_EMPTY,DISJOINT_SYM]
 >> FULL_SIMP_TAC std_ss []
 >> NTAC 5 (POP_ASSUM K_TAC)
 (* now use the lemma instead *)
 >> MATCH_MP_TAC COUNTABLY_ADDITIVE_FINITE_ADDITIVE_lemma >> art []
QED

Theorem COUNTABLY_SUBADDITIVE_FINITE_SUBADDITIVE :
    !m. {} IN measurable_sets m /\ positive m /\ countably_subadditive m ==>
        finite_subadditive m
Proof
    RW_TAC std_ss [positive_def, countably_subadditive_def, finite_subadditive_def,
                   IN_FUNSET, IN_UNIV]
 >> Q.PAT_X_ASSUM `!f. P f` (MP_TAC o Q.SPEC `\i :num. if i < n then (f i) else {}`)
 >> Know
      `BIGUNION (IMAGE (\i :num. if i < n then (f i) else {}) UNIV) =
       BIGUNION (IMAGE f (count n))`
 >- (RW_TAC arith_ss [EXTENSION, IN_BIGUNION, IN_IMAGE, IN_UNIV, IN_UNION, IN_COUNT] \\
     EQ_TAC >> rpt STRIP_TAC >|
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC `s` \\
       CONJ_TAC >- (POP_ASSUM K_TAC >> art []) \\
       Q.EXISTS_TAC `i` >> PROVE_TAC [NOT_IN_EMPTY],
       (* goal 2 (of 2) *)
       Q.EXISTS_TAC `s` \\
       CONJ_TAC >- (NTAC 2 (POP_ASSUM K_TAC) >> art []) \\
       Q.EXISTS_TAC `x'` >> PROVE_TAC [NOT_IN_EMPTY] ]) >> Rewr
 >> RW_TAC std_ss []
 (* `{} IN measurable_sets m` is used here *)
 >> `!x:num. (if x < n then (f x) else {}) IN measurable_sets m` by METIS_TAC []
 >> FULL_SIMP_TAC std_ss []
 >> POP_ASSUM K_TAC
 >> Suff `suminf (measure m o (\i. if i < n then f i else {})) = SIGMA (measure m o f) (count n)`
 >- METIS_TAC []
 >> NTAC 2 (POP_ASSUM K_TAC)
 (* now use the lemma instead *)
 >> MATCH_MP_TAC COUNTABLY_ADDITIVE_FINITE_ADDITIVE_lemma >> art []
QED

val MEASURE_DOWN = store_thm
  ("MEASURE_DOWN",
   ``!m0 m1.
       sigma_algebra (m_space m0,measurable_sets m0) /\
       measurable_sets m0 SUBSET measurable_sets m1 /\
       (measure m0 = measure m1) /\ measure_space m1 ==>
       measure_space m0``,
   RW_TAC std_ss [measure_space_def, positive_def, SUBSET_DEF,
                  countably_additive_def, IN_FUNSET, IN_UNIV]);

(* added ``measure m s < PosInf`` into antecedents, c.f. MEASURE_SPACE_FINITE_DIFF *)
val MEASURE_COMPL = store_thm
  ("MEASURE_COMPL",
  ``!m s.
       measure_space m /\ s IN measurable_sets m /\
       measure m s < PosInf ==>
       (measure m (m_space m DIFF s) = measure m (m_space m) - measure m s)``,
    RW_TAC std_ss []
 >> Know `(measure m (m_space m DIFF s) = measure m (m_space m) - measure m s) <=>
          (measure m (m_space m DIFF s) + measure m s = measure m (m_space m))`
 >- (MATCH_MP_TAC eq_sub_ladd \\
     `positive m` by PROVE_TAC [measure_space_def] \\
     PROVE_TAC [positive_not_infty, lt_infty])
 >> DISCH_THEN (REWRITE_TAC o wrap)
 >> MATCH_MP_TAC EQ_SYM
 >> MATCH_MP_TAC ADDITIVE
 >> Q.PAT_X_ASSUM `measure_space m` MP_TAC
 >> RW_TAC std_ss [measure_space_def, sigma_algebra_def, DISJOINT_DEF,
                   EXTENSION, IN_DIFF, IN_UNIV, IN_UNION, IN_INTER,
                   NOT_IN_EMPTY]
 >> PROVE_TAC [COUNTABLY_ADDITIVE_ADDITIVE, ALGEBRA_COMPL, subsets_def, space_def,
               algebra_def, subset_class_def, SUBSET_DEF, ALGEBRA_SPACE, positive_def]);

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

val MEASURE_COUNTABLY_ADDITIVE = store_thm (* merged *)
  ("MEASURE_COUNTABLY_ADDITIVE",
   ``!m s f.
       measure_space m /\ f IN (UNIV -> measurable_sets m) /\
       (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) /\
       (s = BIGUNION (IMAGE f UNIV)) ==>
       (suminf (measure m o f) = measure m s)``,
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
   >> PROVE_TAC [measure_space_def, SIGMA_ALGEBRA_ALGEBRA, ALGEBRA_EMPTY, subsets_def]);

val MEASURE_ADDITIVE = store_thm
  ("MEASURE_ADDITIVE",
   ``!m s t u.
       measure_space m /\ s IN measurable_sets m /\ t IN measurable_sets m /\
       DISJOINT s t /\ (u = s UNION t) ==>
       (measure m u = measure m s + measure m t)``,
   RW_TAC std_ss []
   >> MATCH_MP_TAC ADDITIVE
   >> RW_TAC std_ss [MEASURE_SPACE_ADDITIVE]
   >> PROVE_TAC [measure_space_def, SIGMA_ALGEBRA_ALGEBRA, ALGEBRA_UNION, subsets_def]);

(* The following theorems were merged from measure_hvgScript.sml *)
val MEASURE_SPACE_INCREASING = store_thm
  ("MEASURE_SPACE_INCREASING", ``!m. measure_space m ==> increasing m``,
    RW_TAC real_ss []
 >> `additive m` by RW_TAC real_ss [MEASURE_SPACE_ADDITIVE]
 >> FULL_SIMP_TAC real_ss [measure_space_def,sigma_algebra_def,ADDITIVE_INCREASING]);

val MEASURE_SPACE_POSITIVE = store_thm
  ("MEASURE_SPACE_POSITIVE",``!m. measure_space m ==> positive m``,
   PROVE_TAC [measure_space_def]);

val MEASURE_SPACE_INTER = store_thm
  ("MEASURE_SPACE_INTER",
  ``!m s t. (measure_space m) /\ (s IN measurable_sets m) /\ (t IN measurable_sets m) ==>
            (s INTER t IN measurable_sets m)``,
   METIS_TAC [measure_space_def,sigma_algebra_def,subsets_def,
              (REWRITE_RULE [subsets_def] (Q.SPEC `(m_space m,measurable_sets m)` ALGEBRA_INTER))]);

val MEASURE_SPACE_UNION = store_thm
  ("MEASURE_SPACE_UNION",
  ``!m s t. (measure_space m) /\ (s IN measurable_sets m) /\ (t IN measurable_sets m) ==>
            (s UNION t IN measurable_sets m)``,
   METIS_TAC [measure_space_def,sigma_algebra_def,subsets_def,
              (REWRITE_RULE [subsets_def] (Q.SPEC `(m_space m,measurable_sets m)` ALGEBRA_UNION))]);

val MEASURE_SPACE_DIFF = store_thm
  ("MEASURE_SPACE_DIFF",
  ``!m s t. (measure_space m) /\ (s IN measurable_sets m) /\ (t IN measurable_sets m) ==>
            (s DIFF t IN measurable_sets m)``,
   METIS_TAC [measure_space_def,sigma_algebra_def,subsets_def,
              (REWRITE_RULE [subsets_def] (Q.SPEC `(m_space m,measurable_sets m)` ALGEBRA_DIFF))]);

val MEASURE_SPACE_BIGUNION = store_thm
  ("MEASURE_SPACE_BIGUNION",
  ``!m s. measure_space m /\ (!n:num. s n IN measurable_sets m) ==>
          (BIGUNION (IMAGE s UNIV) IN measurable_sets m)``,
    RW_TAC std_ss []
 >> (MP_TAC o REWRITE_RULE [subsets_def,space_def,IN_UNIV,IN_FUNSET] o
     (Q.SPEC `(m_space m,measurable_sets m)`)) SIGMA_ALGEBRA_FN
 >> METIS_TAC [measure_space_def]);

val MEASURE_SPACE_IN_MSPACE = store_thm
  ("MEASURE_SPACE_IN_MSPACE",
  ``!m A. measure_space m /\ A IN measurable_sets m ==> (!x. x IN A ==> x IN m_space m)``,
   METIS_TAC [measure_space_def,sigma_algebra_def,algebra_def,measurable_sets_def,
              space_def,subset_class_def,subsets_def,SUBSET_DEF]);

val MEASURE_SPACE_SUBSET_MSPACE = store_thm
  ("MEASURE_SPACE_SUBSET_MSPACE",
  ``!A m. measure_space m /\ A IN measurable_sets m ==> A SUBSET m_space m``,
  RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,subset_class_def,
                 subsets_def, space_def]);

val MEASURE_SPACE_EMPTY_MEASURABLE = store_thm
  ("MEASURE_SPACE_EMPTY_MEASURABLE",``!m. measure_space m ==> {} IN measurable_sets m``,
   RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,subsets_def, space_def]);

val MEASURE_SPACE_MSPACE_MEASURABLE = store_thm
  ("MEASURE_SPACE_MSPACE_MEASURABLE",``!m. measure_space m ==> (m_space m) IN measurable_sets m``,
    RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def, subsets_def, space_def]
 >> METIS_TAC [DIFF_EMPTY]);

val MEASURE_SPACE_BIGINTER = store_thm
  ("MEASURE_SPACE_BIGINTER",
  ``!m s. measure_space m /\ (!n:num. s n IN measurable_sets m) ==>
         (BIGINTER (IMAGE s UNIV) IN measurable_sets m)``,
  RW_TAC std_ss []
  >> (MP_TAC o REWRITE_RULE [subsets_def,space_def,IN_UNIV,IN_FUNSET] o
      (Q.SPEC `(m_space m,measurable_sets m)`)) SIGMA_ALGEBRA_FN_BIGINTER
  >> METIS_TAC [measure_space_def]);

(* use MONOTONE_CONVERGENCE when `f 0 = {}` doesn't hold *)
Theorem MEASURE_COUNTABLE_INCREASING :
    !m s f.
       measure_space m /\ f IN (UNIV -> measurable_sets m) /\
       (f 0 = {}) /\ (!n. f n SUBSET f (SUC n)) /\
       (s = BIGUNION (IMAGE f UNIV)) ==>
       (sup (IMAGE (measure m o f) UNIV) = measure m s)
Proof
    RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> Know `measure m o f = (\n. SIGMA (measure m o (\m. f (SUC m) DIFF f m)) (count n))`
 >- (FUN_EQ_TAC
       >> Induct >- RW_TAC std_ss [o_THM, MEASURE_EMPTY,COUNT_ZERO,EXTREAL_SUM_IMAGE_EMPTY]
       >> POP_ASSUM (MP_TAC o SYM)
       >> RW_TAC arith_ss [o_THM, COUNT_SUC]
       >> Know `!n. (measure m o (\m. f (SUC m) DIFF f m)) n <> NegInf`
       >- ( RW_TAC std_ss []
            >> `f (SUC n) DIFF f n IN measurable_sets m`
                   by METIS_TAC [measure_space_def, sigma_algebra_def, algebra_def, ALGEBRA_DIFF,
                                 subsets_def]
            >> METIS_TAC [measure_space_def,positive_not_infty,o_DEF] )
       >> DISCH_TAC
       >> `FINITE (count x)` by RW_TAC std_ss [FINITE_COUNT]
       >> `count x DELETE x = count x`
                by METIS_TAC [IN_COUNT, DELETE_NON_ELEMENT, LESS_REFL]
       >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY]
       >> MATCH_MP_TAC MEASURE_ADDITIVE
       >> FULL_SIMP_TAC std_ss [EXTENSION, IN_UNION, IN_DIFF, DISJOINT_DEF, NOT_IN_EMPTY,
                                IN_INTER, SUBSET_DEF]
       >> Know `algebra (m_space m, measurable_sets m)`
       >- FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def,
                                space_def, subsets_def]
       >> DISCH_TAC
       >> (MP_TAC o REWRITE_RULE [subsets_def, space_def] o
           (Q.SPEC `(m_space m, measurable_sets m)`)) ALGEBRA_DIFF
       >> PROVE_TAC [])
 >> Rewr
 >> Know `!n. 0 <= (measure m o (\m. f (SUC m) DIFF f m)) n`
 >- (RW_TAC std_ss [o_DEF] \\
     IMP_RES_TAC MEASURE_SPACE_POSITIVE \\
     fs [positive_def] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     MATCH_MP_TAC MEASURE_SPACE_DIFF >> art [])
 >> DISCH_THEN (MP_TAC o SYM o (MATCH_MP ext_suminf_alt_pos)) >> Rewr'
 >> MATCH_MP_TAC COUNTABLY_ADDITIVE
 >> CONJ_TAC >- FULL_SIMP_TAC std_ss [measure_space_def]
 >> CONJ_TAC
 >- (RW_TAC std_ss [IN_UNIV,IN_FUNSET]
       >> (((MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
             (Q.SPEC `(m_space m, measurable_sets m)`)) ALGEBRA_DIFF
       >> FULL_SIMP_TAC std_ss [measure_space_def,sigma_algebra_def])))
 >> CONJ_TAC
 >- (rpt STRIP_TAC
       >> MATCH_MP_TAC DISJOINT_DIFFS
       >> Q.EXISTS_TAC `f`
       >> RW_TAC std_ss [])
 >> CONJ_TAC
 >- (RW_TAC std_ss [IN_BIGUNION_IMAGE,IN_DIFF,IN_UNIV,EXTENSION]
       >> Reverse (EQ_TAC >> RW_TAC std_ss [])
       >- METIS_TAC []
       >> Induct_on `x'` >- RW_TAC std_ss [NOT_IN_EMPTY]
       >> METIS_TAC [])
 >> (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
     (Q.SPEC `(m_space m, measurable_sets m)`)) SIGMA_ALGEBRA_COUNTABLE_UNION
 >> CONJ_TAC >- PROVE_TAC [measure_space_def]
 >> RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV,COUNTABLE_IMAGE_NUM]
 >> PROVE_TAC []
QED

(* c.f. MEASURE_COMPL *)
val MEASURE_SPACE_FINITE_DIFF = store_thm
  ("MEASURE_SPACE_FINITE_DIFF",
  ``!m s. measure_space m /\ s IN measurable_sets m /\ measure m s <> PosInf ==>
         (measure  m (m_space m DIFF s) = measure m (m_space m) - measure m s)``,
  RW_TAC std_ss []
  >> `(m_space m) IN measurable_sets m` by METIS_TAC [MEASURE_SPACE_MSPACE_MEASURABLE]
  >> `(m_space m DIFF s) IN measurable_sets m` by METIS_TAC [MEASURE_SPACE_DIFF]
  >> `!s. s IN measurable_sets m ==> measure m s <> NegInf`
       by METIS_TAC [MEASURE_SPACE_POSITIVE,positive_not_infty]
  >> `measure m (m_space m DIFF s) <= measure m (m_space m)`
       by METIS_TAC [MEASURE_SPACE_INCREASING,INCREASING,MEASURE_SPACE_SUBSET_MSPACE]
  >> `measure m (m_space m) = measure m (m_space m DIFF s) + measure m s`
       by METIS_TAC [MEASURE_SPACE_ADDITIVE,UNION_DIFF,DISJOINT_DIFF,MEASURE_SPACE_SUBSET_MSPACE,ADDITIVE]
  >> Cases_on `measure m (m_space m DIFF s)`
  >> Cases_on `measure m (m_space m)`
  >> Cases_on `measure m s`
  >> RW_TAC std_ss [extreal_sub_def,extreal_not_infty,extreal_add_def]
  >> FULL_SIMP_TAC std_ss [extreal_add_def,REAL_EQ_SUB_LADD,REAL_ADD_COMM,EQ_SYM,extreal_11]
  >> METIS_TAC [lt_infty,extreal_not_infty,let_trans,extreal_add_def]);

(* c.f. MEASURE_DIFF_SUBSET *)
val MEASURE_SPACE_FINITE_DIFF_SUBSET = store_thm
  ("MEASURE_SPACE_FINITE_DIFF_SUBSET",
   ``!m s t. measure_space m /\ s IN measurable_sets m /\ t IN measurable_sets m /\
             t SUBSET s /\ measure m s <> PosInf ==>
        (measure  m (s DIFF t) = measure m s - measure m t)``,
  RW_TAC std_ss []
  >> `!s. s IN measurable_sets m ==> measure m s <> NegInf`
       by METIS_TAC [MEASURE_SPACE_POSITIVE,positive_not_infty]
  >> `measure m s = measure m (s DIFF t) + measure m t`
       by (MATCH_MP_TAC ADDITIVE
           >> METIS_TAC [MEASURE_SPACE_ADDITIVE,UNION_DIFF,DISJOINT_DIFF,ADDITIVE,MEASURE_SPACE_DIFF])
  >> `s DIFF t IN measurable_sets m ` by METIS_TAC [MEASURE_SPACE_DIFF]
  >> `measure m (s DIFF t) <= measure m s` by METIS_TAC [MEASURE_SPACE_INCREASING,INCREASING,DIFF_SUBSET]
  >> `measure m (s DIFF t) <> PosInf` by METIS_TAC [lt_infty,let_trans]
  >> `measure m t <> PosInf` by METIS_TAC [lt_infty,let_trans,MEASURE_SPACE_INCREASING,INCREASING]
  >> Cases_on `measure m (s DIFF t)`
  >> Cases_on `measure m s`
  >> Cases_on `measure m t`
  >> RW_TAC std_ss [extreal_sub_def,extreal_not_infty,extreal_add_def]
  >> FULL_SIMP_TAC real_ss [extreal_add_def,extreal_11]
  >> METIS_TAC []);

val MEASURE_SPACE_FINITE_MEASURE = store_thm
  ("MEASURE_SPACE_FINITE_MEASURE",
   ``!m s. measure_space m /\ s IN measurable_sets m /\ measure m (m_space m) <> PosInf ==>
           measure m s <> PosInf``,
   METIS_TAC [MEASURE_SPACE_INCREASING,INCREASING,MEASURE_SPACE_MSPACE_MEASURABLE,
              lt_infty,let_trans,MEASURE_SPACE_SUBSET_MSPACE]);

val MEASURE_SPACE_REDUCE = store_thm
  ("MEASURE_SPACE_REDUCE", ``!m. (m_space m, measurable_sets m, measure m) = m``,
    Cases >> Q.SPEC_TAC (`r`, `r`)
 >> Cases >> RW_TAC std_ss [m_space_def, measurable_sets_def, measure_def]);

val MONOTONE_CONVERGENCE = store_thm
  ("MONOTONE_CONVERGENCE",
   ``!m s f.
       measure_space m /\ f IN (UNIV -> measurable_sets m) /\
       (!n. f n SUBSET f (SUC n)) /\
       (s = BIGUNION (IMAGE f UNIV)) ==>
       (sup (IMAGE (measure m o f) univ(:num)) = measure m s)``,
   RW_TAC std_ss [measure_space_def, IN_FUNSET, IN_UNIV]
   >> (MP_TAC o
       INST_TYPE [beta |-> ``:num``] o
       Q.SPECL [`m`, `BIGUNION (IMAGE f UNIV)`, `\x. num_CASE x {} f`])
      MEASURE_COUNTABLE_INCREASING
   >> Cond
   >- (RW_TAC std_ss [IN_FUNSET, IN_UNIV, num_case_def, measure_space_def] >|
       [Cases_on `x` >|
        [RW_TAC std_ss [num_case_def]
         >> PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, ALGEBRA_EMPTY, subsets_def],
         RW_TAC std_ss [num_case_def]],
        Cases_on `n`
        >> RW_TAC std_ss [num_case_def, EMPTY_SUBSET],
        SET_EQ_TAC
        >> RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_UNIV]
        >> EQ_TAC >|
        [RW_TAC std_ss []
         >> Q.EXISTS_TAC `SUC x'`
         >> RW_TAC std_ss [num_case_def],
         RW_TAC std_ss []
         >> POP_ASSUM MP_TAC
         >> Cases_on `x'` >- RW_TAC std_ss [NOT_IN_EMPTY, num_case_def]
         >> RW_TAC std_ss [num_case_def]
         >> PROVE_TAC []]])
   >> RW_TAC std_ss []
   >> Know `measure m o f = (\n. (measure m o (\x. num_CASE x {} f)) (SUC n))`
   >- (FUN_EQ_TAC
       >> RW_TAC std_ss [num_case_def, o_THM])
   >> Rewr
   >> `sup (IMAGE (\n. (measure m o (\x. num_CASE x {} f)) (SUC n)) UNIV) =
       sup (IMAGE (measure m o (\x. num_CASE x {} f)) UNIV)`
           by (MATCH_MP_TAC sup_suc
               >> RW_TAC std_ss [o_DEF]
               >> MATCH_MP_TAC INCREASING
               >> CONJ_TAC >- METIS_TAC [measure_space_def,MEASURE_SPACE_INCREASING]
               >> CONJ_TAC
               >- (Cases_on `n` >- FULL_SIMP_TAC std_ss [LE,EMPTY_SUBSET,num_case_def]
                   >> Cases_on `m'` >- FULL_SIMP_TAC std_ss [EMPTY_SUBSET,num_case_def]
                   >> `!n m:num. m <= n ==> f m SUBSET f n`
                       by (RW_TAC std_ss []
                           >> Know `?d:num. n'' = m' + d` >- PROVE_TAC [LESS_EQ_EXISTS]
                           >> RW_TAC std_ss []
                           >> Induct_on `d` >- RW_TAC std_ss [add_rzero,SUBSET_REFL]
                           >> RW_TAC std_ss []
                           >> Q.PAT_ASSUM `!n. f n SUBSET f (SUC n)` (MP_TAC o Q.SPEC `m' + d`)
                           >> METIS_TAC [SUBSET_TRANS,ADD_CLAUSES,LESS_EQ_ADD])
                   >> FULL_SIMP_TAC std_ss [num_case_def,LESS_EQ_MONO])
               >> CONJ_TAC
               >- (Cases_on `m'`
                   >- METIS_TAC [measure_space_def,MEASURE_SPACE_EMPTY_MEASURABLE,num_case_def]
                   >> RW_TAC std_ss [num_case_def])
               >> Cases_on `n`
               >- METIS_TAC [measure_space_def,MEASURE_SPACE_EMPTY_MEASURABLE,num_case_def]
               >> RW_TAC std_ss [num_case_def])
    >> METIS_TAC []);

val MONOTONE_CONVERGENCE2 = store_thm
  ("MONOTONE_CONVERGENCE2",
  ``!m f. measure_space m /\ f IN (UNIV -> measurable_sets m) /\
         (!n. f n SUBSET f (SUC n)) ==>
         (sup (IMAGE (measure m o f) univ(:num)) = measure m (BIGUNION (IMAGE f UNIV)))``,
    METIS_TAC [MONOTONE_CONVERGENCE]);

val MONOTONE_CONVERGENCE_BIGINTER = store_thm
  ("MONOTONE_CONVERGENCE_BIGINTER",
   ``!m s f.
       measure_space m /\ f IN (UNIV -> measurable_sets m) /\
       (!n. measure m (f n) <> PosInf) /\
       (!n. f (SUC n) SUBSET f n) /\
       (s = BIGINTER (IMAGE f UNIV)) ==>
       (inf (IMAGE (measure m o f) univ(:num)) = measure m s)``,
  RW_TAC std_ss [IN_FUNSET, IN_UNIV]
  >> `BIGINTER (IMAGE f UNIV) IN measurable_sets m` by METIS_TAC [MEASURE_SPACE_BIGINTER]
  >> `!n. f n SUBSET f 0`
         by (Induct_on `n` >- RW_TAC std_ss [SUBSET_REFL]
             >> METIS_TAC [SUBSET_TRANS])
    >> `BIGINTER (IMAGE f UNIV) SUBSET (f 0)`
        by (MATCH_MP_TAC BIGINTER_SUBSET
            >> METIS_TAC [IMAGE_EQ_EMPTY,UNIV_NOT_EMPTY,IN_IMAGE,IN_UNIV])
  >> `measure m (BIGINTER (IMAGE f UNIV)) <> PosInf`
        by METIS_TAC [MEASURE_SPACE_INCREASING,INCREASING,let_trans,lt_infty]
  >> `inf (IMAGE (measure m o f) UNIV) <= measure m (f 0)`
        by (MATCH_MP_TAC inf_le_imp
            >> ONCE_REWRITE_TAC [GSYM SPECIFICATION]
            >> RW_TAC std_ss [IN_UNIV,IN_IMAGE,o_DEF]
            >> METIS_TAC [])
  >> `!n. measure m (f n) <> NegInf` by METIS_TAC [MEASURE_SPACE_POSITIVE,positive_not_infty]
  >> `?r. measure m (f 0) = Normal r` by METIS_TAC [extreal_cases]
  >> `measure m (f 0) - inf (IMAGE (measure m o f) UNIV) =
      sup (IMAGE (\n. measure m (f 0) - measure m (f n)) UNIV)`
        by RW_TAC std_ss [inf_cminus]
  >> Q.ABBREV_TAC `g = (\n. (f 0) DIFF (f n))`
  >> `!n. measure m (f 0) - measure m (f n) = measure m (g n)`
       by METIS_TAC [MEASURE_SPACE_FINITE_DIFF_SUBSET]
  >> FULL_SIMP_TAC std_ss []
  >> `sup (IMAGE (\n. measure m (g n)) UNIV) = measure m (BIGUNION (IMAGE g UNIV))`
       by ((MATCH_MP_TAC o REWRITE_RULE [o_DEF]) MONOTONE_CONVERGENCE2
           >> RW_TAC std_ss [IN_FUNSET,IN_UNIV]
           >- METIS_TAC [MEASURE_SPACE_DIFF]
           >> Q.UNABBREV_TAC `g`
           >> RW_TAC std_ss [SUBSET_DEF,IN_DIFF,GSPECIFICATION]
           >> METIS_TAC [SUBSET_DEF])
  >> Q.UNABBREV_TAC `g`
  >> `BIGINTER (IMAGE f UNIV) = (f 0) DIFF BIGUNION (IMAGE (\u. (f 0) DIFF u) (IMAGE f UNIV))`
      by (MATCH_MP_TAC DIFF_BIGINTER
          >> METIS_TAC [IN_IMAGE,IN_UNIV,IMAGE_EQ_EMPTY,UNIV_NOT_EMPTY])
  >> POP_ORW
  >> `BIGUNION (IMAGE (\u. f 0 DIFF u) (IMAGE f UNIV)) = BIGUNION (IMAGE (\n. f 0 DIFF f n) UNIV)`
        by (RW_TAC std_ss [EXTENSION,IN_BIGUNION_IMAGE,IN_UNIV,IN_IMAGE]
            >> METIS_TAC [SUBSET_DEF,IN_DIFF])
  >> POP_ORW
  >> Suff `measure m (f 0 DIFF BIGUNION (IMAGE (\n. f 0 DIFF f n) UNIV)) =
           measure m (f 0) - measure m (BIGUNION (IMAGE (\n. f 0 DIFF f n) UNIV))`
  >- METIS_TAC [eq_sub_switch]
  >> MATCH_MP_TAC MEASURE_SPACE_FINITE_DIFF_SUBSET
  >> RW_TAC std_ss []
  >- (MATCH_MP_TAC MEASURE_SPACE_BIGUNION
      >> METIS_TAC [MEASURE_SPACE_DIFF])
  >> RW_TAC std_ss [BIGUNION_SUBSET,IN_IMAGE,IN_UNIV]
  >> METIS_TAC [DIFF_SUBSET]);

val MONOTONE_CONVERGENCE_BIGINTER2 = store_thm
  ("MONOTONE_CONVERGENCE_BIGINTER2",
  ``!m f. measure_space m /\ f IN (UNIV -> measurable_sets m) /\
         (!n. measure m (f n) <> PosInf) /\
         (!n. f (SUC n) SUBSET f n) ==>
         (inf (IMAGE (measure m o f) univ(:num)) = measure m (BIGINTER (IMAGE f UNIV)))``,
    METIS_TAC [MONOTONE_CONVERGENCE_BIGINTER]);

val MEASURABLE_SETS_SUBSET_SPACE = store_thm
  ("MEASURABLE_SETS_SUBSET_SPACE",
  ``!m s. measure_space m /\ s IN measurable_sets m ==> s SUBSET m_space m``,
    RW_TAC std_ss [measure_space_def, sigma_algebra_def, algebra_def, subsets_def, space_def,
                   subset_class_def]);

val MEASURABLE_DIFF_PROPERTY = store_thm
  ("MEASURABLE_DIFF_PROPERTY",
   ``!a b f. sigma_algebra a /\ sigma_algebra b /\
             f IN (space a -> space b) /\
             (!s. s IN subsets b ==> PREIMAGE f s IN subsets a) ==>
        (!s. s IN subsets b ==>
                (PREIMAGE f (space b DIFF s) = space a DIFF PREIMAGE f s))``,
   RW_TAC std_ss [SIGMA_ALGEBRA, IN_FUNSET, subsets_def, space_def, GSPECIFICATION,
                  PREIMAGE_DIFF, IN_IMAGE]
   >> MATCH_MP_TAC SUBSET_ANTISYM
   >> RW_TAC std_ss [SUBSET_DEF, IN_DIFF, IN_PREIMAGE]
   >> Q.PAT_X_ASSUM `!s. s IN subsets b ==> PREIMAGE f s IN subsets a`
        (MP_TAC o Q.SPEC `space b DIFF s`)
   >> Know `x IN PREIMAGE f (space b DIFF s)`
   >- RW_TAC std_ss [IN_PREIMAGE, IN_DIFF]
   >> PROVE_TAC [subset_class_def, SUBSET_DEF]);

val MEASURABLE_BIGUNION_PROPERTY = store_thm
  ("MEASURABLE_BIGUNION_PROPERTY",
   ``!a b f. sigma_algebra a /\ sigma_algebra b /\
             f IN (space a -> space b) /\
             (!s. s IN subsets b ==> PREIMAGE f s IN subsets a) ==>
        (!c. c SUBSET subsets b ==>
                (PREIMAGE f (BIGUNION c) = BIGUNION (IMAGE (PREIMAGE f) c)))``,
   RW_TAC std_ss [SIGMA_ALGEBRA, IN_FUNSET, subsets_def, space_def, GSPECIFICATION,
                  PREIMAGE_BIGUNION, IN_IMAGE]);

val MEASUBABLE_BIGUNION_LEMMA = store_thm
  ("MEASUBABLE_BIGUNION_LEMMA",
   ``!a b f. sigma_algebra a /\ sigma_algebra b /\
             f IN (space a -> space b) /\
             (!s. s IN subsets b ==> PREIMAGE f s IN subsets a) ==>
        (!c. countable c /\ c SUBSET (IMAGE (PREIMAGE f) (subsets b)) ==>
                BIGUNION c IN IMAGE (PREIMAGE f) (subsets b))``,
   RW_TAC std_ss [SIGMA_ALGEBRA, IN_FUNSET, IN_IMAGE]
   >> Q.EXISTS_TAC `BIGUNION (IMAGE (\x. @x'. x' IN subsets b /\ (PREIMAGE f x' = x)) c)`
   >> Reverse CONJ_TAC
   >- (Q.PAT_X_ASSUM `!c. countable c /\ c SUBSET subsets b ==> BIGUNION c IN subsets b`
           MATCH_MP_TAC
       >> RW_TAC std_ss [image_countable, SUBSET_DEF, IN_IMAGE]
       >> Suff `(\x''. x'' IN subsets b) (@x''. x'' IN subsets b /\ (PREIMAGE f x'' = x'))`
       >- RW_TAC std_ss []
       >> MATCH_MP_TAC SELECT_ELIM_THM
       >> FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE]
       >> PROVE_TAC [])
   >> RW_TAC std_ss [PREIMAGE_BIGUNION, IMAGE_IMAGE]
   >> RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, IN_IMAGE]
   >> FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE]
   >> EQ_TAC
   >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `s` >> ASM_REWRITE_TAC []
       >> Q.PAT_X_ASSUM `!x. x IN c ==> ?x'. (x = PREIMAGE f x') /\ x' IN subsets b`
             (MP_TAC o Q.SPEC `s`)
       >> RW_TAC std_ss []
       >> Q.EXISTS_TAC `PREIMAGE f x'` >> ASM_REWRITE_TAC []
       >> Suff `(\x''. PREIMAGE f x' = PREIMAGE f x'')
                (@x''. x'' IN subsets b /\ (PREIMAGE f x'' = PREIMAGE f x'))`
       >- METIS_TAC []
       >> MATCH_MP_TAC SELECT_ELIM_THM
       >> PROVE_TAC [])
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `x'`
   >> ASM_REWRITE_TAC []
   >> Know `(\x''. x IN PREIMAGE f x'' ==> x IN x')
                   (@x''. x'' IN subsets b /\ (PREIMAGE f x'' = x'))`
   >- (MATCH_MP_TAC SELECT_ELIM_THM
       >> RW_TAC std_ss []
       >> PROVE_TAC [])
   >> RW_TAC std_ss []);

val MEASURABLE_SIGMA_PREIMAGES = store_thm
  ("MEASURABLE_SIGMA_PREIMAGES",
   ``!a b f. sigma_algebra a /\ sigma_algebra b /\
             f IN (space a -> space b) /\
             (!s. s IN subsets b ==> PREIMAGE f s IN subsets a) ==>
             sigma_algebra (space a, IMAGE (PREIMAGE f) (subsets b))``,
   RW_TAC std_ss [SIGMA_ALGEBRA, IN_FUNSET, subsets_def, space_def]
   >| [FULL_SIMP_TAC std_ss [subset_class_def, GSPECIFICATION, IN_IMAGE]
       >> PROVE_TAC [],
       RW_TAC std_ss [IN_IMAGE]
       >> Q.EXISTS_TAC `{}`
       >> RW_TAC std_ss [PREIMAGE_EMPTY],
       RW_TAC std_ss [IN_IMAGE, PREIMAGE_DIFF]
       >> FULL_SIMP_TAC std_ss [IN_IMAGE]
       >> Q.EXISTS_TAC `space b DIFF x`
       >> RW_TAC std_ss [PREIMAGE_DIFF]
       >> MATCH_MP_TAC SUBSET_ANTISYM
       >> RW_TAC std_ss [SUBSET_DEF, IN_DIFF, IN_PREIMAGE]
       >> Q.PAT_X_ASSUM `!s. s IN subsets b ==> PREIMAGE f s IN subsets a`
             (MP_TAC o Q.SPEC `space b DIFF x`)
       >> Know `x' IN PREIMAGE f (space b DIFF x)`
       >- RW_TAC std_ss [IN_PREIMAGE, IN_DIFF]
       >> PROVE_TAC [subset_class_def, SUBSET_DEF],
       (MP_TAC o REWRITE_RULE [IN_FUNSET, SIGMA_ALGEBRA] o Q.SPECL [`a`, `b`, `f`])
               MEASUBABLE_BIGUNION_LEMMA
       >> RW_TAC std_ss []]);

val IN_MEASURABLE = store_thm
  ("IN_MEASURABLE",
  ``!a b f. f IN measurable a b <=>
            sigma_algebra a /\ sigma_algebra b /\ f IN (space a -> space b) /\
            (!s. s IN subsets b ==> ((PREIMAGE f s)INTER(space a)) IN subsets a)``,
    RW_TAC std_ss [measurable_def, GSPECIFICATION]);

val MEASURABLE_SIGMA = store_thm
  ("MEASURABLE_SIGMA",
  ``!f a b sp. sigma_algebra a /\ subset_class sp b /\ f IN (space a -> sp) /\
              (!s. s IN b ==> ((PREIMAGE f s)INTER(space a)) IN subsets a)
           ==> f IN measurable a (sigma sp b)``,
   RW_TAC std_ss []
   >> REWRITE_TAC [IN_MEASURABLE]
   >> CONJ_TAC >- FULL_SIMP_TAC std_ss [sigma_def, space_def]
   >> RW_TAC std_ss [SIGMA_ALGEBRA_SIGMA, SPACE_SIGMA, subsets_def, GSPECIFICATION]
   >> Know `subsets (sigma sp b) SUBSET {x' | ((PREIMAGE f x')INTER(space a)) IN subsets a /\
                                         x' SUBSET sp}`
   >- (MATCH_MP_TAC SIGMA_PROPERTY
       >> RW_TAC std_ss [subset_class_def, GSPECIFICATION, IN_INTER, EMPTY_SUBSET,
                         PREIMAGE_EMPTY, PREIMAGE_DIFF, SUBSET_INTER, SIGMA_ALGEBRA,
                         DIFF_SUBSET, SUBSET_DEF, NOT_IN_EMPTY, IN_DIFF,
                         PREIMAGE_BIGUNION, IN_BIGUNION]
       >| [FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, INTER_EMPTY],
           PROVE_TAC [subset_class_def, SUBSET_DEF],
           Know `(PREIMAGE f sp DIFF PREIMAGE f s') INTER space a =
                 (PREIMAGE f sp INTER space a) DIFF (PREIMAGE f s' INTER space a)`
           >- (RW_TAC std_ss [Once EXTENSION, IN_DIFF, IN_INTER, IN_PREIMAGE] >> DECIDE_TAC)
           >> RW_TAC std_ss []
           >> Know `PREIMAGE f sp INTER space a = space a`
           >- (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_PREIMAGE] >> METIS_TAC [IN_FUNSET])
           >> FULL_SIMP_TAC std_ss [sigma_algebra_def, ALGEBRA_COMPL],
           FULL_SIMP_TAC std_ss [sigma_algebra_def]
           >> `BIGUNION (IMAGE (PREIMAGE f) c) INTER space a =
               BIGUNION (IMAGE (\x. (PREIMAGE f x) INTER (space a)) c)`
                by (RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, IN_INTER, IN_IMAGE]
                    >> FULL_SIMP_TAC std_ss [IN_FUNSET]
                    >> EQ_TAC
                    >- (RW_TAC std_ss []
                        >> Q.EXISTS_TAC `PREIMAGE f x' INTER space a`
                        >> ASM_REWRITE_TAC [IN_INTER]
                        >> Q.EXISTS_TAC `x'` >> RW_TAC std_ss [])
                    >> RW_TAC std_ss [] >> METIS_TAC [IN_INTER, IN_PREIMAGE])
           >> RW_TAC std_ss []
           >> Q.PAT_X_ASSUM `!c. countable c /\ c SUBSET subsets a ==>
                 BIGUNION c IN subsets a` MATCH_MP_TAC
           >> RW_TAC std_ss [image_countable, SUBSET_DEF, IN_IMAGE]
           >> PROVE_TAC [],
           PROVE_TAC []])
   >> RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION]);

val MEASURABLE_SUBSET = store_thm
  ("MEASURABLE_SUBSET",
   ``!a b. measurable a b SUBSET measurable a (sigma (space b) (subsets b))``,
   RW_TAC std_ss [SUBSET_DEF]
   >> MATCH_MP_TAC MEASURABLE_SIGMA
   >> FULL_SIMP_TAC std_ss [IN_MEASURABLE, SIGMA_ALGEBRA, space_def, subsets_def]);

val MEASURABLE_LIFT = store_thm
  ("MEASURABLE_LIFT",
   ``!f a b.
       f IN measurable a b ==> f IN measurable a (sigma (space b) (subsets b))``,
   PROVE_TAC [MEASURABLE_SUBSET, SUBSET_DEF]);

val IN_MEASURE_PRESERVING = store_thm
  ("IN_MEASURE_PRESERVING",
   ``!m1 m2 f.
       f IN measure_preserving m1 m2 <=>
       f IN measurable (m_space m1, measurable_sets m1) (m_space m2, measurable_sets m2) /\
       !s.
         s IN measurable_sets m2 ==>
         (measure m1 ((PREIMAGE f s)INTER(m_space m1)) = measure m2 s)``,
   RW_TAC std_ss [measure_preserving_def, GSPECIFICATION]);

(* The old definition of `measure_preserving m1 m2` requires that both
  `m1` and `m2` must be measure_space. Now they're removed, and we must add
  `measure_space (m_space m2,a,measure m2)` into the antecedents, which cannot
   be derived from other conditions, since we don't know if `a` (for sure
   smaller than `measurable_sets m2`, as a generator) is countably_additive.

   Furthermore, due to the changes to [0,+inf]-measure, now the theorem requires
   that both m1 and m2 are finite measure spaces.
 *)
Theorem MEASURE_PRESERVING_LIFT :
    !m1 m2 a f.
       measure_space m1 /\ measure_space m2 /\
       measure_space (m_space m2,a,measure m2) /\
       measure m1 (m_space m1) <> PosInf /\
       measure m2 (m_space m2) <> PosInf /\
      (measurable_sets m2 = subsets (sigma (m_space m2) a)) /\
       f IN measure_preserving m1 (m_space m2,a,measure m2) ==>
       f IN measure_preserving m1 m2
Proof
    RW_TAC std_ss []
 >> Reverse (Cases_on `algebra (m_space m2,a)`)
 >- FULL_SIMP_TAC std_ss [IN_MEASURE_PRESERVING, IN_MEASURABLE, m_space_def,
                          measurable_sets_def, sigma_algebra_def]
 >> Suff `f IN measure_preserving m1 (m_space m2,measurable_sets m2,measure m2)`
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
     >> ASM_REWRITE_TAC [])
 >> Q.PAT_X_ASSUM `f IN X` K_TAC
 >> REWRITE_TAC [IN_MEASURABLE, space_def, subsets_def]
 >> STRIP_TAC
 >> ASM_REWRITE_TAC []
 (* stage work *)
 >> Suff `subsets (sigma (m_space m2) a) SUBSET
                 {s | measure m1 ((PREIMAGE f s) INTER (m_space m1)) = measure m2 s}`
 >- RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION]
 >> MATCH_MP_TAC SIGMA_PROPERTY_DISJOINT
 >> Know `!s. s IN subsets (sigma (m_space m2) a) ==> measure m2 s <> PosInf`
 >- (NTAC 2 STRIP_TAC \\
    `s IN measurable_sets m2` by PROVE_TAC [] \\
     MATCH_MP_TAC MEASURE_SPACE_FINITE_MEASURE >> art [])
 >> RW_TAC std_ss [GSPECIFICATION, SUBSET_DEF, IN_INTER, IN_FUNSET,
                   IN_UNIV, PREIMAGE_COMPL, PREIMAGE_BIGUNION, IMAGE_IMAGE,
                   MEASURE_SPACE_FINITE_DIFF] (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      Q.PAT_X_ASSUM `measure m1 (PREIMAGE f s INTER m_space m1) = measure m2 s`
                    (fn thm => ONCE_REWRITE_TAC [GSYM thm]) \\
      Know `m_space m2 IN a` >- PROVE_TAC [ALGEBRA_SPACE, subsets_def, space_def] \\
      STRIP_TAC \\
      Q.PAT_X_ASSUM `!s. s IN a ==> (measure m1 (PREIMAGE f s INTER m_space m1) = measure m2 s)`
        ((fn thm => ONCE_REWRITE_TAC [GSYM thm]) o UNDISCH o Q.SPEC `m_space m2`) \\
      Know `PREIMAGE f (m_space m2) INTER m_space m1 = m_space m1`
      >- (FULL_SIMP_TAC std_ss [Once EXTENSION, IN_INTER, IN_PREIMAGE, IN_FUNSET] \\
          METIS_TAC []) \\
      RW_TAC std_ss [PREIMAGE_DIFF] \\
     `(PREIMAGE f (m_space m2) DIFF PREIMAGE f s) INTER m_space m1 =
      (PREIMAGE f (m_space m2) INTER m_space m1) DIFF (PREIMAGE f s INTER m_space m1)`
         by (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_DIFF, IN_PREIMAGE] \\
             DECIDE_TAC) >> POP_ORW \\
      POP_ORW \\
     `measure m1 (PREIMAGE f s INTER m_space m1) <> PosInf`
        by METIS_TAC [MEASURE_SPACE_FINITE_MEASURE] \\
      RW_TAC std_ss [MEASURE_SPACE_FINITE_DIFF],
      (* goal 2 (of 3) *)
     `BIGUNION (IMAGE (PREIMAGE f o f') UNIV) INTER m_space m1 =
      BIGUNION (IMAGE (\x:num. (PREIMAGE f o f') x INTER m_space m1) UNIV)`
        by (RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, IN_INTER, IN_IMAGE, IN_UNIV] \\
            FULL_SIMP_TAC std_ss [IN_FUNSET] \\
            EQ_TAC
            >- (RW_TAC std_ss [] \\
                Q.EXISTS_TAC `PREIMAGE f (f' x') INTER m_space m1` \\
                ASM_REWRITE_TAC [IN_INTER] \\
                Q.EXISTS_TAC `x'` >>  RW_TAC std_ss []) \\
            RW_TAC std_ss [] >> METIS_TAC [IN_PREIMAGE, IN_INTER]) \\
      POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]) \\
      Suff
       `sup (IMAGE (measure m2 o f') univ(:num)) = measure m2 (BIGUNION (IMAGE f' UNIV)) /\
        sup (IMAGE (measure m2 o f') univ(:num)) =
            measure m1 (BIGUNION (IMAGE (\x. (PREIMAGE f o f') x INTER m_space m1) UNIV))`
      >- PROVE_TAC [] \\
      CONJ_TAC >- (MATCH_MP_TAC MEASURE_COUNTABLE_INCREASING \\
                   RW_TAC std_ss [IN_FUNSET, IN_UNIV, SUBSET_DEF]) \\
      Know `measure m2 o f' = measure m1 o (\x. (PREIMAGE f o f') x INTER m_space m1)`
      >- (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC std_ss [o_THM]) \\
      DISCH_THEN (ONCE_REWRITE_TAC o wrap) \\
      MATCH_MP_TAC MEASURE_COUNTABLE_INCREASING \\
      RW_TAC std_ss [IN_FUNSET, IN_UNIV, o_THM, PREIMAGE_EMPTY, INTER_EMPTY] \\
      Suff `PREIMAGE f (f' n) SUBSET PREIMAGE f (f' (SUC n))`
      >- RW_TAC std_ss [SUBSET_DEF, IN_INTER] \\
      MATCH_MP_TAC PREIMAGE_SUBSET \\
      RW_TAC std_ss [SUBSET_DEF],
      (* goal 3 of 3 *)
     `BIGUNION (IMAGE (PREIMAGE f o f') UNIV) INTER m_space m1 =
      BIGUNION (IMAGE (\x:num. (PREIMAGE f o f') x INTER m_space m1) UNIV)`
        by (RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, IN_INTER, IN_IMAGE, IN_UNIV]
            >> FULL_SIMP_TAC std_ss [IN_FUNSET]
            >> EQ_TAC
            >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `PREIMAGE f (f' x') INTER m_space m1`
                >> ASM_REWRITE_TAC [IN_INTER] >> Q.EXISTS_TAC `x'` >> RW_TAC std_ss [])
            >> RW_TAC std_ss [] >> METIS_TAC [IN_PREIMAGE, IN_INTER]) \\
      POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]) \\
      Suff
       `suminf (measure m2 o f') = measure m2 (BIGUNION (IMAGE f' UNIV)) /\
        suminf (measure m2 o f') =
          measure m1 (BIGUNION (IMAGE (\x. (PREIMAGE f o f') x INTER m_space m1) UNIV))`
      >- PROVE_TAC [] \\
      CONJ_TAC >- (MATCH_MP_TAC MEASURE_COUNTABLY_ADDITIVE \\
                   RW_TAC std_ss [IN_FUNSET, IN_UNIV]) \\
      Know `measure m2 o f' = measure m1 o (\x. (PREIMAGE f o f') x INTER m_space m1)`
      >- (RW_TAC std_ss [FUN_EQ_THM] >> RW_TAC std_ss [o_THM]) \\
      DISCH_THEN (ONCE_REWRITE_TAC o wrap) \\
      MATCH_MP_TAC MEASURE_COUNTABLY_ADDITIVE \\
      RW_TAC std_ss [IN_FUNSET, IN_UNIV, o_THM, IN_DISJOINT, PREIMAGE_DISJOINT, IN_INTER] \\
      METIS_TAC [IN_DISJOINT, PREIMAGE_DISJOINT] ]
QED

(* added the same more requirements as for MEASURE_PRESERVING_LIFT *)
val MEASURE_PRESERVING_SUBSET = store_thm
  ("MEASURE_PRESERVING_SUBSET",
   ``!m1 m2 a.
       measure_space m1 /\ measure_space m2 /\
       measure_space (m_space m2,a,measure m2) /\
       measure m1 (m_space m1) <> PosInf /\
       measure m2 (m_space m2) <> PosInf /\
       (measurable_sets m2 = subsets (sigma (m_space m2) a)) ==>
       measure_preserving m1 (m_space m2, a, measure m2) SUBSET
       measure_preserving m1 m2``,
   RW_TAC std_ss [SUBSET_DEF]
   >> MATCH_MP_TAC MEASURE_PRESERVING_LIFT
   >> PROVE_TAC []);

val MEASURABLE_I = store_thm
  ("MEASURABLE_I",
   ``!a. sigma_algebra a ==> I IN measurable a a``,
   RW_TAC std_ss [IN_MEASURABLE, I_THM, PREIMAGE_I, IN_FUNSET, GSPEC_ID, SPACE, SUBSET_REFL]
   >> Know `s INTER space a = s`
   >- (FULL_SIMP_TAC std_ss [Once EXTENSION, sigma_algebra_def, algebra_def, IN_INTER,
                             subset_class_def, SUBSET_DEF]
       >> METIS_TAC [])
   >> RW_TAC std_ss []);

val MEASURABLE_COMP = store_thm
  ("MEASURABLE_COMP",
   ``!f g a b c.
       f IN measurable a b /\ g IN measurable b c ==>
       (g o f) IN measurable a c``,
   RW_TAC std_ss [IN_MEASURABLE, GSYM PREIMAGE_COMP, IN_FUNSET, SIGMA_ALGEBRA, space_def,
                  subsets_def, GSPECIFICATION]
   >> `PREIMAGE f (PREIMAGE g s) INTER space a =
       PREIMAGE f (PREIMAGE g s INTER space b) INTER space a`
        by (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_PREIMAGE] >> METIS_TAC [])
   >> METIS_TAC []);

val MEASURABLE_COMP_STRONG = store_thm
  ("MEASURABLE_COMP_STRONG",
   ``!f g a b c.
       f IN measurable a b /\
       sigma_algebra c /\
       g IN (space b -> space c) /\
       (!x. x IN (subsets c) ==> PREIMAGE g x INTER (IMAGE f (space a)) IN subsets b) ==>
       (g o f) IN measurable a c``,
   RW_TAC bool_ss [IN_MEASURABLE]
   >| [FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, IN_FUNSET] >> PROVE_TAC [],
       RW_TAC std_ss [PREIMAGE_ALT]
       >> ONCE_REWRITE_TAC [o_ASSOC]
       >> ONCE_REWRITE_TAC [GSYM PREIMAGE_ALT]
       >> Know `PREIMAGE f (s o g) INTER space a =
                PREIMAGE f (s o g INTER (IMAGE f (space a))) INTER space a`
       >- (RW_TAC std_ss [GSYM PREIMAGE_ALT]
           >> RW_TAC std_ss [Once EXTENSION, IN_PREIMAGE, IN_INTER, IN_IMAGE]
           >> EQ_TAC
           >> RW_TAC std_ss []
           >> FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_PREIMAGE]
           >> Q.EXISTS_TAC `x`
           >> Know `g (f x) IN space c`
           >- (FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, subset_class_def, SUBSET_DEF] >> PROVE_TAC [])
           >> PROVE_TAC [])
       >> STRIP_TAC >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
       >> FULL_SIMP_TAC std_ss [PREIMAGE_ALT]]);

val MEASURABLE_COMP_STRONGER = store_thm
  ("MEASURABLE_COMP_STRONGER",
  ``!f g a b c t.
       f IN measurable a b /\
       sigma_algebra c /\
       g IN (space b -> space c) /\
       (IMAGE f (space a)) SUBSET t /\
       (!s. s IN subsets c ==> (PREIMAGE g s INTER t) IN subsets b) ==>
       (g o f) IN measurable a c``,
   RW_TAC bool_ss [IN_MEASURABLE]
   >| [FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, IN_FUNSET] >> PROVE_TAC [],
       RW_TAC std_ss [PREIMAGE_ALT]
       >> ONCE_REWRITE_TAC [o_ASSOC]
       >> ONCE_REWRITE_TAC [GSYM PREIMAGE_ALT]
       >> Know `(PREIMAGE (f:'a->'b) (((s : 'c -> bool) o (g :'b -> 'c)) INTER
                (t :'b -> bool)) INTER space a = PREIMAGE f (s o g) INTER space a)`
       >- (RW_TAC std_ss [GSYM PREIMAGE_ALT]
           >> RW_TAC std_ss [Once EXTENSION, IN_PREIMAGE, IN_INTER, IN_IMAGE]
           >> EQ_TAC
           >> RW_TAC std_ss []
            >> Know `g (f x) IN space c`
           >- (FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, subset_class_def, SUBSET_DEF] >> PROVE_TAC [])
           >> STRIP_TAC
           >> Know `(f x) IN space b`
           >- FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_PREIMAGE, IN_FUNSET]
           >> STRIP_TAC
           >> Know `x IN space a`
           >- FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_PREIMAGE]
           >> STRIP_TAC
           >> FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE]
           >> Q.PAT_X_ASSUM `!x. (?x'. (x = f x') /\ x' IN space a) ==> x IN t` MATCH_MP_TAC
           >> Q.EXISTS_TAC `x`
           >> ASM_REWRITE_TAC [])
       >> DISCH_THEN (ONCE_REWRITE_TAC o wrap o GSYM)
       >> RW_TAC std_ss [PREIMAGE_ALT]
       >> RW_TAC std_ss [GSYM PREIMAGE_ALT, GSYM PREIMAGE_COMP]]);

val MEASURABLE_UP_LIFT = store_thm
  ("MEASURABLE_UP_LIFT",
  ``!sp a b c f. f IN measurable (sp, a) c /\
                 sigma_algebra (sp, b) /\ a SUBSET b ==> f IN measurable (sp,b) c``,
    RW_TAC std_ss [IN_MEASURABLE, GSPECIFICATION, SUBSET_DEF, IN_FUNSET, space_def, subsets_def]);

val MEASURABLE_UP_SUBSET = store_thm
  ("MEASURABLE_UP_SUBSET",
   ``!sp a b c. a SUBSET b /\ sigma_algebra (sp, b)
        ==> measurable (sp, a) c SUBSET measurable (sp, b) c``,
   RW_TAC std_ss [MEASURABLE_UP_LIFT, SUBSET_DEF]
   >> MATCH_MP_TAC MEASURABLE_UP_LIFT
   >> Q.EXISTS_TAC `a`
   >> ASM_REWRITE_TAC [SUBSET_DEF]);

val MEASURABLE_UP_SIGMA = store_thm
  ("MEASURABLE_UP_SIGMA",
   ``!a b. measurable a b SUBSET measurable (sigma (space a) (subsets a)) b``,
   RW_TAC std_ss [SUBSET_DEF, IN_MEASURABLE, space_def, subsets_def, SPACE_SIGMA]
   >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA])
   >> PROVE_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF]);

(* fewer antecedents *)
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

(* fewer antecedents *)
val MEASURE_PRESERVING_UP_SUBSET = store_thm
  ("MEASURE_PRESERVING_UP_SUBSET",
   ``!m1 m2 a.
       a SUBSET measurable_sets m1 /\
       sigma_algebra (m_space m1, measurable_sets m1) ==>
       measure_preserving (m_space m1, a, measure m1) m2 SUBSET measure_preserving m1 m2``,
   RW_TAC std_ss [MEASURE_PRESERVING_UP_LIFT, SUBSET_DEF]
   >> MATCH_MP_TAC MEASURE_PRESERVING_UP_LIFT
   >> PROVE_TAC [SUBSET_DEF]);

val MEASURE_PRESERVING_UP_SIGMA = store_thm
  ("MEASURE_PRESERVING_UP_SIGMA",
   ``!m1 m2 a.
       (measurable_sets m1 = subsets (sigma (m_space m1) a)) ==>
       measure_preserving (m_space m1, a, measure m1) m2 SUBSET measure_preserving m1 m2``,
   RW_TAC std_ss [MEASURE_PRESERVING_UP_LIFT, SUBSET_DEF]
   >> MATCH_MP_TAC MEASURE_PRESERVING_UP_LIFT
   >> Q.EXISTS_TAC `a`
   >> ASM_REWRITE_TAC [SIGMA_SUBSET_SUBSETS, SIGMA_REDUCE]
   >> FULL_SIMP_TAC std_ss [IN_MEASURE_PRESERVING, IN_MEASURABLE, m_space_def, measurable_sets_def]
   >> MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA
   >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, space_def, subsets_def]);

(* ****************** *)

val MEASURABLE_PROD_SIGMA = store_thm
  ("MEASURABLE_PROD_SIGMA",
   ``!a a1 a2 f.
       sigma_algebra a /\
       (FST o f) IN measurable a a1 /\
       (SND o f) IN measurable a a2 ==>
       f IN measurable a (sigma ((space a1) CROSS (space a2))
                                (prod_sets (subsets a1) (subsets a2)))``,
   rpt STRIP_TAC
   >> MATCH_MP_TAC MEASURABLE_SIGMA
   >> FULL_SIMP_TAC std_ss [IN_MEASURABLE]
   >> CONJ_TAC
   >- (RW_TAC std_ss [subset_class_def, subsets_def, space_def, IN_PROD_SETS]
      >> PROVE_TAC [SIGMA_ALGEBRA, CROSS_SUBSET, SUBSET_DEF, subset_class_def, subsets_def,
                    space_def])
   >> CONJ_TAC
   >- (RW_TAC std_ss [IN_FUNSET, SPACE_SIGMA, IN_CROSS]
       >> FULL_SIMP_TAC std_ss [IN_FUNSET, o_DEF])
   >> RW_TAC std_ss [IN_PROD_SETS]
   >> RW_TAC std_ss [PREIMAGE_CROSS]
   >> `PREIMAGE (FST o f) t INTER PREIMAGE (SND o f) u INTER space a =
       (PREIMAGE (FST o f) t INTER space a) INTER (PREIMAGE (SND o f) u INTER space a)`
        by (RW_TAC std_ss [Once EXTENSION, IN_INTER] >> DECIDE_TAC)
   >> PROVE_TAC [sigma_algebra_def, ALGEBRA_INTER]);

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

val MEASURE_EXTREAL_SUM_IMAGE = store_thm
  ("MEASURE_EXTREAL_SUM_IMAGE",
   ``!m s. measure_space m /\ s IN measurable_sets m /\
           (!x. x IN s ==> {x} IN measurable_sets m) /\ FINITE s ==>
                (measure m s = SIGMA (\x. measure m {x}) s)``,
   Suff `!s. FINITE s ==>
        (\s. !m. measure_space m /\ s IN measurable_sets m /\
                 (!x. x IN s ==> {x} IN measurable_sets m) ==>
                (measure m s = SIGMA (\x. measure m {x}) s)) s`
   >- METIS_TAC []
   >> MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, MEASURE_EMPTY, DELETE_NON_ELEMENT, IN_INSERT]
   >> `!x. x IN e INSERT s ==> (\x. measure m {x}) x <> NegInf`
        by METIS_TAC [IN_INSERT,measure_space_def,positive_not_infty]
   >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY, DELETE_NON_ELEMENT]
   >> Q.PAT_X_ASSUM `!m. a /\ b /\ c ==> d` (MP_TAC o GSYM o Q.SPEC `m`)
   >>  `s IN measurable_sets m`
        by (`s = (e INSERT s) DIFF {e}`
                by (RW_TAC std_ss [EXTENSION, IN_INSERT, IN_DIFF, IN_SING]
                    >> METIS_TAC [GSYM DELETE_NON_ELEMENT])
            >> POP_ORW
            >> FULL_SIMP_TAC std_ss [measure_space_def, sigma_algebra_def]
            >> METIS_TAC [space_def, subsets_def, ALGEBRA_DIFF])
   >> RW_TAC std_ss []
   >> MATCH_MP_TAC MEASURE_ADDITIVE
   >> RW_TAC std_ss [IN_DISJOINT, IN_SING, Once INSERT_SING_UNION]
   >> FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]);

Theorem finite_additivity_sufficient_for_finite_spaces :
    !s m. sigma_algebra s /\ FINITE (space s) /\
          positive (space s, subsets s, m) /\
          additive (space s, subsets s, m) ==>
          measure_space (space s, subsets s, m)
Proof
    RW_TAC std_ss [countably_additive_def, additive_def, measurable_sets_def,
                   measure_def, IN_FUNSET, IN_UNIV, measure_space_def, m_space_def, SPACE]
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
 (* stage work *)
 >> Know `!n. 0 <= (m o f) n`
 >- fs [positive_def, measure_def, measurable_sets_def]
 >> DISCH_THEN (MP_TAC o (MATCH_MP ext_suminf_alt_pos)) >> Rewr'
 >> RW_TAC std_ss [sup_eq', IN_IMAGE, IN_UNIV]
 >- (Cases_on `N <= n`
     >- (`count n = (count N) UNION (count n DIFF count N)`
             by METIS_TAC [UNION_DIFF,SUBSET_DEF,IN_COUNT,SUBSET_DEF,IN_COUNT,LESS_EQ_TRANS,LESS_EQ]
           >> POP_ORW
           >> `FINITE (count N) /\ FINITE (count n DIFF count N)`
                 by RW_TAC std_ss [FINITE_COUNT,FINITE_DIFF]
           >> `DISJOINT (count N) (count n DIFF count N)`
                 by METIS_TAC [EXTENSION,IN_DISJOINT,IN_COUNT,IN_DIFF,IN_INTER,NOT_IN_EMPTY]
           >> `!x. (m o f) x <> NegInf`
                 by METIS_TAC [positive_not_infty,measurable_sets_def,subsets_def,measure_def,o_DEF]
           >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_DISJOINT_UNION]
           >> (MP_TAC o Q.SPEC `(m :('a -> bool) -> extreal) o f` o UNDISCH o
               (Q.SPEC `count n DIFF count N`) o INST_TYPE [alpha |-> ``:num``]) EXTREAL_SUM_IMAGE_IN_IF
           >> RW_TAC std_ss []
           >> `(\x. if x IN count n DIFF count N then m (f x) else 0) = (\x. 0)`
                by (FUN_EQ_TAC
                    >> RW_TAC std_ss [IN_COUNT,IN_DIFF,NOT_LESS]
                    >> FULL_SIMP_TAC std_ss [positive_def,measure_def])
           >> POP_ORW
           >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_ZERO,add_rzero]
           >> Suff `SIGMA (m o f) (count N) = m (BIGUNION (IMAGE f (count N)))`
           >- RW_TAC std_ss [le_refl]
           >> (MATCH_MP_TAC o REWRITE_RULE [m_space_def,measurable_sets_def,measure_def] o
               Q.SPECL [`(space s,subsets s, m)`,`f`,`N`]) ADDITIVE_SUM
           >> FULL_SIMP_TAC std_ss [IN_FUNSET,IN_UNIV,SPACE,sigma_algebra_def]
           >> METIS_TAC [additive_def,measure_def,measurable_sets_def,m_space_def])
     >> FULL_SIMP_TAC std_ss [NOT_LESS_EQUAL]
     >> `SIGMA (m o f) (count n) = m (BIGUNION (IMAGE f (count n)))`
            by ((MATCH_MP_TAC o REWRITE_RULE [m_space_def,measurable_sets_def,measure_def] o
                 Q.SPECL [`(space s,subsets s, m)`,`f`,`n`]) ADDITIVE_SUM
                >> RW_TAC std_ss [IN_FUNSET,IN_UNIV]
                >- FULL_SIMP_TAC std_ss [sigma_algebra_def,SPACE]
                >> METIS_TAC [additive_def,measure_def,measurable_sets_def,m_space_def])
     >> POP_ORW
     >> (MATCH_MP_TAC o REWRITE_RULE [measurable_sets_def,subsets_def,measure_def] o
         Q.SPECL [`(space s,subsets s,m)`,
                  `BIGUNION (IMAGE f (count n))`,
                  `BIGUNION (IMAGE f (count N))`]) INCREASING
     >> CONJ_TAC
     >- (MATCH_MP_TAC ADDITIVE_INCREASING
           >> FULL_SIMP_TAC std_ss [m_space_def,measurable_sets_def,sigma_algebra_def,SPACE]
           >> METIS_TAC [additive_def,measure_def,m_space_def,measurable_sets_def])
     >> RW_TAC std_ss [SUBSET_DEF,IN_BIGUNION_IMAGE,IN_COUNT]
     >- METIS_TAC [LESS_TRANS]
     >> FULL_SIMP_TAC std_ss [sigma_algebra_def]
     >> Q.PAT_X_ASSUM ` !c. P c /\ Q c ==> BIGUNION c IN subsets s` MATCH_MP_TAC
     >> RW_TAC std_ss [COUNTABLE_IMAGE_NUM,SUBSET_DEF,IN_IMAGE,IN_COUNT]
     >> METIS_TAC [])
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC `N`
 >> (MATCH_MP_TAC o GSYM o REWRITE_RULE [m_space_def,measurable_sets_def,measure_def] o
     Q.SPECL [`(space s,subsets s, m)`,`f`,`N`]) ADDITIVE_SUM
 >> RW_TAC std_ss [IN_FUNSET,IN_UNIV]
 >- FULL_SIMP_TAC std_ss [sigma_algebra_def,SPACE]
 >> METIS_TAC [additive_def,measure_def,measurable_sets_def,m_space_def]
QED

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

(* added ``measure m t < PosInf`` into antecedents, c.f. MEASURE_SPACE_FINITE_DIFF_SUBSET *)
val MEASURE_DIFF_SUBSET = store_thm
  ("MEASURE_DIFF_SUBSET",
  ``!m s t.
       measure_space m /\ s IN measurable_sets m /\ t IN measurable_sets m /\
      (t SUBSET s) /\ measure m t < PosInf ==>
       (measure m (s DIFF t) = measure m s - measure m t)``,
    RW_TAC std_ss []
 >> Know `(measure m (s DIFF t) = measure m s - measure m t) <=>
          (measure m (s DIFF t) + measure m t = measure m s)`
 >- (MATCH_MP_TAC eq_sub_ladd \\
     `positive m` by PROVE_TAC [measure_space_def] \\
     PROVE_TAC [positive_not_infty, lt_infty])
 >> DISCH_THEN (REWRITE_TAC o wrap)
 >> MATCH_MP_TAC EQ_SYM
 >> MATCH_MP_TAC ADDITIVE
 >> Q.PAT_X_ASSUM `measure_space m` MP_TAC
 >> RW_TAC std_ss [measure_space_def, sigma_algebra_def, DISJOINT_DEF,
                   EXTENSION, IN_DIFF, IN_UNIV, IN_UNION, IN_INTER,
                   NOT_IN_EMPTY]
 >> METIS_TAC [COUNTABLY_ADDITIVE_ADDITIVE, MEASURE_SPACE_DIFF, measure_space_def,
               sigma_algebra_def, SUBSET_DEF, ALGEBRA_EMPTY, subsets_def, positive_def]);

val MEASURE_COMPL_SUBSET = save_thm (* old name for compatibility purposes *)
  ("MEASURE_COMPL_SUBSET", MEASURE_DIFF_SUBSET);

(* c.f. MEASURE_SPACE_RESTRICTION *)
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

(* Another way to restrict a measure space *)
val MEASURE_SPACE_RESTRICTED_MEASURE = store_thm
  ("MEASURE_SPACE_RESTRICTED_MEASURE",
  ``!m s. measure_space m /\ s IN measurable_sets m ==>
          measure_space (m_space m,measurable_sets m,(\a. measure m (s INTER a)))``,
 (* proof *)
    RW_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def, measure_def, positive_def,
                   INTER_EMPTY]
 >- (FIRST_ASSUM MATCH_MP_TAC \\
     MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                (Q.SPEC `(m_space m,measurable_sets m)` ALGEBRA_INTER)) \\
     fs [sigma_algebra_def])
 >> fs [countably_additive_def, measurable_sets_def, measure_def, m_space_def, IN_FUNSET, IN_UNIV]
 >> RW_TAC std_ss [o_DEF]
 >> Know `(\x. measure m (s INTER f x)) = measure m o (\x. s INTER f x)`
 >- (FUN_EQ_TAC >> SIMP_TAC std_ss [o_DEF]) >> Rewr'
 >> REWRITE_TAC [BIGUNION_OVER_INTER_R]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [o_DEF, GSYM BIGUNION_OVER_INTER_R] (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                 (Q.SPEC `(m_space m,measurable_sets m)` ALGEBRA_INTER)) \\
      fs [sigma_algebra_def],
      (* goal 2 (of 3) *)
      MATCH_MP_TAC DISJOINT_RESTRICT_R \\
      FIRST_X_ASSUM MATCH_MP_TAC >> art [],
      (* goal 3 (of 3) *)
      MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                 (Q.SPEC `(m_space m,measurable_sets m)` ALGEBRA_INTER)) \\
      fs [sigma_algebra_def] ]);

val MEASURE_SPACE_CMUL = store_thm
  ("MEASURE_SPACE_CMUL",
  ``!m c. measure_space m /\ 0 <= c ==>
          measure_space (m_space m, measurable_sets m, (\a. Normal c * measure m a))``,
  RW_TAC std_ss [measure_space_def,m_space_def,measurable_sets_def,measure_def,
                 positive_def,mul_rzero]
  >- METIS_TAC [extreal_le_def,le_mul,extreal_of_num_def]
  >> RW_TAC std_ss [countably_additive_def,measure_def,measurable_sets_def,o_DEF]
  >> `measure m (BIGUNION (IMAGE f univ(:num))) = suminf (measure m o f)`
        by METIS_TAC [countably_additive_def]
  >> `suminf (\x. Normal c * measure m (f x)) = suminf (\x. Normal c * (\x. measure m (f x)) x)`
        by METIS_TAC []
  >> POP_ORW
  >> Suff `suminf (\x. Normal c * (\x. measure m (f x)) x) = Normal c * suminf (\x. measure m (f x))`
  >- METIS_TAC []
  >> MATCH_MP_TAC ext_suminf_cmul
  >> METIS_TAC [IN_UNIV,IN_FUNSET,extreal_le_def,extreal_of_num_def]);

val BIGUNION_IMAGE_Q = store_thm
  ("BIGUNION_IMAGE_Q",
   ``!a f: extreal -> 'a -> bool. sigma_algebra a /\ f IN (Q_set -> subsets a)
            ==> BIGUNION (IMAGE f Q_set) IN subsets a``,
   RW_TAC std_ss [SIGMA_ALGEBRA, IN_FUNSET, IN_UNIV, SUBSET_DEF]
   >> Q.PAT_X_ASSUM `!c. countable c /\ P c ==> Q c` MATCH_MP_TAC
   >> RW_TAC std_ss [image_countable, IN_IMAGE, Q_COUNTABLE]
   >> METIS_TAC []);

val measure_split = store_thm
  ("measure_split",
  ``!(r :num -> bool) (b :num -> ('a -> bool)) m.
        measure_space m /\ FINITE r /\
        (BIGUNION (IMAGE b r) = m_space m) /\
        (!i j. i IN r /\ j IN r /\ (~(i = j)) ==> DISJOINT (b i) (b j)) /\
        (!i. i IN r ==> b i IN measurable_sets m) ==>
             !a. a IN measurable_sets m ==>
                 ((measure m) a = SIGMA (\i. (measure m) (a INTER (b i))) r)``,
(* proof *)
   Suff `!r. FINITE r ==>
             (\r. !(b :num -> ('a -> bool)) m.
                   measure_space m /\
                   (BIGUNION (IMAGE b r) = m_space m) /\
                   (!i j. i IN r /\ j IN r /\ (~(i=j)) ==> DISJOINT (b i) (b j)) /\
                   (!i. i IN r ==> b i IN measurable_sets m) ==>
                   !a. a IN measurable_sets m ==>
                       ((measure m) a = SIGMA (\i. (measure m) (a INTER (b i))) r)) r`
   >- RW_TAC std_ss []
   >> MATCH_MP_TAC FINITE_INDUCT
   >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, IMAGE_EMPTY, BIGUNION_EMPTY, DELETE_NON_ELEMENT,
                     IN_INSERT, NOT_IN_EMPTY]
   >- METIS_TAC [MEASURE_SPACE_SUBSET_MSPACE,SUBSET_EMPTY,MEASURE_EMPTY]
   >> `!i. i IN e INSERT s ==> (\i. measure m (a INTER b i)) i <> NegInf`
        by METIS_TAC [measure_space_def,positive_not_infty,MEASURE_SPACE_INTER,IN_INSERT]
   >> Cases_on `s = {}`
   >- (FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY, IMAGE_DEF, IN_SING, BIGUNION,
                             GSPECIFICATION, GSPEC_ID, SUBSET_DEF, add_rzero,
                             EXTREAL_SUM_IMAGE_SING]
       >> METIS_TAC [SUBSET_INTER1,MEASURE_SPACE_SUBSET_MSPACE])
   >> `?x s'. (s = x INSERT s') /\ ~(x IN s')` by METIS_TAC [SET_CASES]
   >> FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT, IN_INSERT]
   >> Q.PAT_X_ASSUM `!b' m'. P ==> !a'. Q ==> (f = g)`
        (MP_TAC o Q.ISPECL [`(\i:num. if i = x then b x UNION b e else b i)`,
        `(m :('a -> bool) # (('a -> bool) -> bool) # (('a -> bool) -> extreal))`])
   >> `IMAGE (\i. (if i = x then b x UNION b e else b i)) s' = IMAGE b s'`
        by (RW_TAC std_ss [Once EXTENSION, IN_IMAGE]
            >> EQ_TAC
            >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `i` >> METIS_TAC [])
            >> RW_TAC std_ss [] >> Q.EXISTS_TAC `x''` >> METIS_TAC [])
   >> FULL_SIMP_TAC std_ss [IMAGE_INSERT, BIGUNION_INSERT, UNION_ASSOC]
   >> POP_ASSUM (K ALL_TAC)
   >> `(b x UNION (b e UNION BIGUNION (IMAGE b s')) = m_space m)`
       by METIS_TAC [UNION_COMM,UNION_ASSOC]
   >> ASM_REWRITE_TAC []
   >> `(!i j. ((i = x) \/ i IN s') /\ ((j = x) \/ j IN s') /\ ~(i = j) ==>
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
   >> FULL_SIMP_TAC std_ss [UNION_ASSOC]
   >> POP_ASSUM MP_TAC >> ASM_REWRITE_TAC []
   >> DISCH_THEN (MP_TAC o Q.SPEC `a`) >> ASM_REWRITE_TAC []
   >> DISCH_TAC
   >> `!i. i IN x INSERT s' ==>
           (\i. measure m (a INTER if i = x then b x UNION b e else b i)) i <> NegInf`
        by (RW_TAC std_ss []
            >- (`a INTER (b i UNION b e) IN measurable_sets m`
                  by METIS_TAC [MEASURE_SPACE_INTER,MEASURE_SPACE_UNION]
                >> METIS_TAC [measure_space_def,positive_not_infty])
            >> METIS_TAC [IN_INSERT])
   >> `!i. i IN (e INSERT x INSERT s') ==> (\i. measure m (a INTER b i)) i <> NegInf`
        by METIS_TAC [IN_INSERT]
   >> `!i. i IN (x INSERT s') ==> (\i. measure m (a INTER b i)) i <> NegInf`
        by METIS_TAC [IN_INSERT]
   >> `(x INSERT s') DELETE e = x INSERT s'` by METIS_TAC [EXTENSION,IN_DELETE,IN_INSERT]
   >> FULL_SIMP_TAC real_ss [FINITE_INSERT, EXTREAL_SUM_IMAGE_PROPERTY, DELETE_NON_ELEMENT]
   >> Suff `(measure m (a INTER (b x UNION b e)) =
             measure m (a INTER b e) + measure m (a INTER b x)) /\
            (SIGMA (\i. measure m (a INTER
                                   (if i = x then b x UNION b e else b i))) s' =
             SIGMA (\i. measure m (a INTER b i)) s')`
   >- (`measure m (a INTER (b x UNION b e)) <> NegInf`
          by METIS_TAC [MEASURE_SPACE_POSITIVE,positive_not_infty,MEASURE_SPACE_INTER,
                        MEASURE_SPACE_UNION]
       >> `SIGMA (\i. measure m (a INTER if i = x then b x UNION b e else b i)) s' <> NegInf`
          by FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_NOT_INFTY,IN_INSERT]
       >> METIS_TAC [add_assoc,IN_INSERT,EXTREAL_SUM_IMAGE_NOT_INFTY,add_not_infty,
                     MEASURE_SPACE_POSITIVE,positive_not_infty,MEASURE_SPACE_INTER,
                     MEASURE_SPACE_UNION])
   >> CONJ_TAC
   >- (`a INTER (b x UNION b e) = (a INTER b e) UNION (a INTER b x)`
        by (FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, GSPECIFICATION,
                                     NOT_IN_EMPTY, IN_INTER, IN_UNION]
            >> METIS_TAC [])
       >> POP_ORW
       >> (MATCH_MP_TAC o REWRITE_RULE [additive_def] o UNDISCH o Q.SPEC `m`)
                MEASURE_SPACE_ADDITIVE
       >> STRONG_CONJ_TAC
       >- METIS_TAC [ALGEBRA_INTER, sigma_algebra_def, measure_space_def, subsets_def]
       >> DISCH_TAC
       >> STRONG_CONJ_TAC
       >- METIS_TAC [ALGEBRA_INTER, sigma_algebra_def, measure_space_def, subsets_def]
       >> DISCH_TAC
       >> CONJ_TAC
       >- (FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] \\
           METIS_TAC [])
       >> METIS_TAC [ALGEBRA_UNION, sigma_algebra_def, measure_space_def, subsets_def])
   >> FULL_SIMP_TAC std_ss [(Once o UNDISCH o Q.ISPEC `(s' :num -> bool)`)
                                EXTREAL_SUM_IMAGE_IN_IF, IN_INSERT]
   >> (MP_TAC o Q.SPEC `(\i. measure m (a INTER b i))` o UNDISCH o
       Q.ISPEC `(s' :num -> bool)`) EXTREAL_SUM_IMAGE_IN_IF
   >> RW_TAC std_ss []
   >> MATCH_MP_TAC (METIS_PROVE [] ``!f x y z. (x = y) ==> (f x z = f y z)``)
   >> RW_TAC std_ss [FUN_EQ_THM]
   >> RW_TAC std_ss []
   >> FULL_SIMP_TAC std_ss [GSYM DELETE_NON_ELEMENT]);

(* ------------------------------------------------------------------------- *)
(*  Uniqueness of Measure - Dynkin system [3]                                *)
(* ------------------------------------------------------------------------- *)

(* `sigma-finite` is a property of measure space but sigma algebra *)
val sigma_finite_def = Define
   `sigma_finite m =
    ?f :num -> 'a set.
     f IN (UNIV -> measurable_sets m) /\
     (!n. f n SUBSET f (SUC n)) /\
     (BIGUNION (IMAGE f UNIV) = m_space m) /\
     (!n. measure m (f n) < PosInf)`;

(* NOTE: this definition should always be used together with a system of sets,
   e.g. algebra, ring, semiring, ... because by itself `m` is not meaningful. *)
val premeasure_def = Define `
    premeasure m <=> positive m /\ countably_additive m`;

(*****************************************************************************)
(*            Premeasure properties of various systems of sets               *)
(* ========================================================================= *)
(* Property name          SEMIRING   DYNKIN   RING     ALGEBRA     MEASURE   *)
(* ========================================================================= *)
(* INCREASING (MONOTONE)  YES*       YES      YES        YES           YES   *)
(* ADDITIVE               YES        YES      YES        YES           YES   *)
(* FINITE_ADDITIVE        YES*       YES      YES        YES           YES   *)
(* STRONG_ADDITIVE        NO         ?        YES        YES           YES   *)
(* SUBADDITIVE            NO         ?        YES+       YES           YES   *)
(* FINITE_SUBADDIIVE      NO         ?        YES+       YES           YES   *)
(* COUNTABLY_SUBADDITIVE  NO         ?        YES*       YES           YES   *)
(* COUNTABLE_INCREASING   NO         ?        YES+       YES           YES   *)
(* COMPL_SUBSET           NO         YES?     YES        YES           YES   *)
(* COMPL                  NO         YES?     NO         YES           YES   *)
(* ========================================================================= *)
(*  [*]   directly used in the proof of CARATHEODORY_SEMIRING                *)
(*  [+] indirectly used in the proof of CARATHEODORY_SEMIRING                *)
(*****************************************************************************)

val ALGEBRA_PREMEASURE_ADDITIVE = store_thm
  ("ALGEBRA_PREMEASURE_ADDITIVE",
  ``!m. algebra (m_space m, measurable_sets m) /\ premeasure m ==> additive m``,
    RW_TAC std_ss [premeasure_def]
 >> MATCH_MP_TAC COUNTABLY_ADDITIVE_ADDITIVE
 >> PROVE_TAC [ALGEBRA_EMPTY, subsets_def]);

(* |- !m. algebra (m_space m,measurable_sets m) /\ positive m /\
         countably_additive m ==> additive m
  old name: COUNTABLY_ADDITIVE_ADDITIVE *)
val ALGEBRA_COUNTABLY_ADDITIVE_ADDITIVE = save_thm
  ("ALGEBRA_COUNTABLY_ADDITIVE_ADDITIVE",
    REWRITE_RULE [premeasure_def] ALGEBRA_PREMEASURE_ADDITIVE);

val ALGEBRA_PREMEASURE_FINITE_ADDITIVE = store_thm
  ("ALGEBRA_PREMEASURE_FINITE_ADDITIVE",
  ``!m. algebra (m_space m, measurable_sets m) /\ premeasure m ==> finite_additive m``,
    RW_TAC std_ss [premeasure_def]
 >> MATCH_MP_TAC COUNTABLY_ADDITIVE_FINITE_ADDITIVE
 >> PROVE_TAC [ALGEBRA_EMPTY, subsets_def]);

val MEASURE_FINITE_ADDITIVE = store_thm
  ("MEASURE_FINITE_ADDITIVE",
  ``!m. measure_space m ==> finite_additive m``,
    RW_TAC std_ss [measure_space_def]
 >> MATCH_MP_TAC ALGEBRA_PREMEASURE_FINITE_ADDITIVE >> art []
 >> PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, premeasure_def]);

(*****************************************************************************)

val DYNKIN_SYSTEM_PREMEASURE_ADDITIVE = store_thm
  ("DYNKIN_SYSTEM_PREMEASURE_ADDITIVE",
  ``!m. dynkin_system (m_space m, measurable_sets m) /\ premeasure m ==> additive m``,
    RW_TAC std_ss [premeasure_def]
 >> MATCH_MP_TAC COUNTABLY_ADDITIVE_ADDITIVE
 >> PROVE_TAC [DYNKIN_SYSTEM_EMPTY, subsets_def]);

val DYNKIN_SYSTEM_PREMEASURE_FINITE_ADDITIVE = store_thm
  ("DYNKIN_SYSTEM_PREMEASURE_FINITE_ADDITIVE",
  ``!m. dynkin_system (m_space m, measurable_sets m) /\ premeasure m ==> finite_additive m``,
    RW_TAC std_ss [premeasure_def]
 >> MATCH_MP_TAC COUNTABLY_ADDITIVE_FINITE_ADDITIVE
 >> PROVE_TAC [DYNKIN_SYSTEM_EMPTY, subsets_def]);

(*****************************************************************************)


(* Assume that (sp, A) is a measurable space and that (A = sigma sp sts) is generated by
   a family `sts` such that

   - `sts` is stable under finite intersections: G,H IN sts ==> G INTER H IN sts;
   - there exists an exhausting sequence (f n) SUBSET g with (f n) --> X.

   Any two measures u, v that coincide on sts and are finite for all members of the
   exhausting sequence u(f n) = v(f n) < Inf, are equal on sts, i.e. u(s) = v(s) for
   all s IN A.
 *)
val UNIQUENESS_OF_MEASURE = store_thm
  ("UNIQUENESS_OF_MEASURE",
  ``!sp sts u v.
      subset_class sp sts /\
      (!s t. s IN sts /\ t IN sts ==> s INTER t IN sts) /\
      sigma_finite (sp,sts,u) /\
      measure_space (sp,subsets (sigma sp sts),u) /\
      measure_space (sp,subsets (sigma sp sts),v) /\
      (!s. s IN sts ==> (u s = v s))
     ==>
      (!s. s IN subsets (sigma sp sts) ==> (u s = v s))``,
 (* proof: expand `sigma_finite` first *)
    REWRITE_TAC [sigma_finite_def, space_def, subsets_def, m_space_def,
                 measurable_sets_def, measure_def]
 >> rpt STRIP_TAC
 >> IMP_RES_TAC SIGMA_ALGEBRA_SIGMA
 >> Q.ABBREV_TAC `A = subsets (sigma sp sts)`
 >> Q.ABBREV_TAC `D = \j. (sp, {q | q IN A /\ (u (f j INTER q) = v (f j INTER q))})`
 >> `!j. space (D j) = sp` by METIS_TAC [space_def]
 >> IMP_RES_TAC DYNKIN_THM
 >> Know `!j. sts SUBSET subsets (D j)`
 >- (GEN_TAC >> REWRITE_TAC [SUBSET_DEF] >> rpt STRIP_TAC \\
     Q.UNABBREV_TAC `D` >> BETA_TAC \\
     SIMP_TAC std_ss [subsets_def, GSPECIFICATION] \\
     CONJ_TAC >- PROVE_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF] \\
     fs [IN_FUNSET, IN_UNIV])
 >> DISCH_TAC
 (* Part 1: u (f j INTER a) < PosInf *)
 >> Know `!n. v (f n) < PosInf`
 >- (GEN_TAC >> `f n IN sts` by PROVE_TAC [IN_UNIV, IN_FUNSET] \\
     PROVE_TAC [])
 >> DISCH_TAC
 >> Know `!j a. a IN A ==> u (f j INTER a) < PosInf`
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC `u (f j)` >> ASM_REWRITE_TAC [] \\
     `u = measure (sp,A,u)` by PROVE_TAC [measure_def] \\
     POP_ASSUM (ONCE_REWRITE_TAC o wrap) \\
     MATCH_MP_TAC INCREASING \\
     CONJ_TAC >- IMP_RES_TAC MEASURE_SPACE_INCREASING \\
     CONJ_TAC >- REWRITE_TAC [INTER_SUBSET] \\
     REWRITE_TAC [measurable_sets_def, Once CONJ_COMM] \\
     ASSUME_TAC (Q.SPECL [`sp`, `sts`] SIGMA_SUBSET_SUBSETS) \\
     STRONG_CONJ_TAC >- PROVE_TAC [IN_UNIV, IN_FUNSET, SUBSET_DEF] \\
     DISCH_TAC \\
     Q.UNABBREV_TAC `A` >> MATCH_MP_TAC ALGEBRA_INTER \\
     fs [sigma_algebra_def])
 >> DISCH_TAC
 >> Know `!j a. a IN A ==> v (f j INTER a) < PosInf`
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC `v (f j)` >> ASM_REWRITE_TAC [] \\
     `v = measure (sp,A,v)` by PROVE_TAC [measure_def] \\
     POP_ASSUM (ONCE_REWRITE_TAC o wrap) \\
     MATCH_MP_TAC INCREASING \\
     CONJ_TAC >- IMP_RES_TAC MEASURE_SPACE_INCREASING \\
     CONJ_TAC >- REWRITE_TAC [INTER_SUBSET] \\
     REWRITE_TAC [measurable_sets_def, Once CONJ_COMM] \\
     ASSUME_TAC (Q.SPECL [`sp`, `sts`] SIGMA_SUBSET_SUBSETS) \\
     STRONG_CONJ_TAC >- PROVE_TAC [IN_UNIV, IN_FUNSET, SUBSET_DEF] \\
     DISCH_TAC \\
     Q.UNABBREV_TAC `A` >> MATCH_MP_TAC ALGEBRA_INTER \\
     fs [sigma_algebra_def])
 >> DISCH_TAC
 (* Part 2: (D j) is dynkin system *)
 >> Know `!j. dynkin_system (D j)`
 >- (GEN_TAC >> REWRITE_TAC [dynkin_system_def] \\
     CONJ_TAC (* subset_class (space (D j)) (subsets (D j)) *)
     >- (Q.PAT_X_ASSUM `!j. space (D j) = sp` (REWRITE_TAC o wrap) \\
         REWRITE_TAC [subset_class_def] >> GEN_TAC \\
         Q.UNABBREV_TAC `D` >> BETA_TAC \\
         SIMP_TAC std_ss [subsets_def, GSPECIFICATION] \\
         `subset_class sp A` by PROVE_TAC [SPACE_SIGMA, sigma_algebra_def, algebra_def] \\
         STRIP_TAC >> PROVE_TAC [subset_class_def]) \\
     CONJ_TAC (* space (D j) IN subsets (D j) *)
     >- (ASM_REWRITE_TAC [] \\
         Q.UNABBREV_TAC `D` >> BETA_TAC \\
         `!n. f n SUBSET sp` by PROVE_TAC [IN_UNIV, IN_FUNSET, subset_class_def] \\
         SIMP_TAC std_ss [subsets_def, GSPECIFICATION] \\
         CONJ_TAC (* sp IN A *)
         >- (Q.UNABBREV_TAC `A` \\
             Suff `space (sigma sp sts) IN subsets (sigma sp sts)` >- PROVE_TAC [SPACE_SIGMA] \\
             MATCH_MP_TAC (Q.SPEC `sigma sp sts` ALGEBRA_SPACE) \\
             PROVE_TAC [sigma_algebra_def]) \\
      (* u (f j INTER sp) = v (f j INTER sp) *)
         `f j INTER sp = f j` by PROVE_TAC [INTER_SUBSET_EQN] \\
         POP_ASSUM (REWRITE_TAC o wrap) \\
         PROVE_TAC [IN_FUNSET, IN_UNIV]) \\
     CONJ_TAC (* under COMPL *)
     >- (Q.X_GEN_TAC `a` >> ONCE_ASM_REWRITE_TAC [] \\
         Q.UNABBREV_TAC `D` >> BETA_TAC >> SIMP_TAC std_ss [subsets_def, GSPECIFICATION] \\
         STRIP_TAC >> CONJ_TAC
         >- (Q.UNABBREV_TAC `A` \\
             `sp DIFF a = space (sigma sp sts) DIFF a` by PROVE_TAC [SPACE_SIGMA] \\
             POP_ASSUM (REWRITE_TAC o wrap) \\
             MATCH_MP_TAC ALGEBRA_COMPL \\
             PROVE_TAC [sigma_algebra_def]) \\
         `!n. f n SUBSET sp` by PROVE_TAC [IN_UNIV, IN_FUNSET, subset_class_def] \\
         `f j INTER (sp DIFF a) = f j DIFF (f j INTER a)` by ASM_SET_TAC [] \\
         POP_ASSUM (REWRITE_TAC o wrap) \\
         `(f j INTER a) SUBSET f j` by ASM_SET_TAC [] \\
         Know `u (f j DIFF (f j INTER a)) = u (f j) - u (f j INTER a)`
         >- (`u = measure (sp,A,u)` by PROVE_TAC [measure_def] \\
             POP_ASSUM (ONCE_REWRITE_TAC o wrap) \\
             MATCH_MP_TAC MEASURE_DIFF_SUBSET \\
             ASM_REWRITE_TAC [measurable_sets_def, measure_def] \\
             STRONG_CONJ_TAC (* f j IN A *)
             >- (Q.UNABBREV_TAC `A` \\
                 ASSUME_TAC (Q.SPECL [`sp`, `sts`] SIGMA_SUBSET_SUBSETS) \\
                 PROVE_TAC [SUBSET_DEF, IN_FUNSET, IN_UNIV]) \\
             DISCH_TAC >> CONJ_TAC
             >- (Q.UNABBREV_TAC `A` \\
                 MATCH_MP_TAC ALGEBRA_INTER >> PROVE_TAC [sigma_algebra_def]) \\
             PROVE_TAC []) \\
         DISCH_TAC \\
         Know `v (f j DIFF (f j INTER a)) = v (f j) - v (f j INTER a)`
         >- (`v = measure (sp,A,v)` by PROVE_TAC [measure_def] \\
             POP_ASSUM (ONCE_REWRITE_TAC o wrap) \\
             MATCH_MP_TAC MEASURE_DIFF_SUBSET \\
             ASM_REWRITE_TAC [measurable_sets_def, measure_def] \\
             STRONG_CONJ_TAC (* f j IN A *)
             >- (Q.UNABBREV_TAC `A` \\
                 ASSUME_TAC (Q.SPECL [`sp`, `sts`] SIGMA_SUBSET_SUBSETS) \\
                 PROVE_TAC [SUBSET_DEF, IN_FUNSET, IN_UNIV]) \\
             DISCH_TAC >> CONJ_TAC
             >- (Q.UNABBREV_TAC `A` \\
                 MATCH_MP_TAC ALGEBRA_INTER >> PROVE_TAC [sigma_algebra_def]) \\
             PROVE_TAC []) \\
         DISCH_TAC \\
         NTAC 2 (POP_ASSUM (ONCE_REWRITE_TAC o wrap)) \\
         fs [IN_UNIV, IN_FUNSET]) \\
     (* 4. under COUNTABLE DIJOINT UNION *)
     Q.X_GEN_TAC `g` >> rpt STRIP_TAC \\
     Q.UNABBREV_TAC `D` >> BETA_TAC \\
     Q.PAT_X_ASSUM `g IN X` MP_TAC \\
     SIMP_TAC std_ss [subsets_def, GSPECIFICATION, IN_UNIV, IN_FUNSET] \\
     STRIP_TAC \\
     CONJ_TAC (* BIGUNION (IMAGE g univ(:num)) IN A *)
     >- (Q.UNABBREV_TAC `A` \\
         STRIP_ASSUME_TAC (REWRITE_RULE [SIGMA_ALGEBRA_ALT]
                                        (ASSUME ``sigma_algebra (sigma sp sts)``)) \\
         POP_ASSUM MATCH_MP_TAC \\
         fs [IN_FUNSET, IN_UNIV]) \\
     REWRITE_TAC [ONCE_REWRITE_RULE [INTER_COMM] BIGUNION_OVER_INTER_L] \\
     Know `u (BIGUNION (IMAGE (\i. f j INTER g i) univ(:num))) = suminf (u o (\i. f j INTER g i))`
     >- (`countably_additive (sp,A,u)` by PROVE_TAC [measure_space_def] \\
         POP_ASSUM (MATCH_MP_TAC o
                    (REWRITE_RULE [countably_additive_def, measurable_sets_def, measure_def])) \\
         CONJ_TAC
         >- (REWRITE_TAC [IN_UNIV, IN_FUNSET] >> GEN_TAC >> BETA_TAC \\
             Q.UNABBREV_TAC `A` >> MATCH_MP_TAC ALGEBRA_INTER \\
             CONJ_TAC >- PROVE_TAC [sigma_algebra_def] \\
             ASSUME_TAC (Q.SPECL [`sp`, `sts`] SIGMA_SUBSET_SUBSETS) \\
             CONJ_TAC >- PROVE_TAC [subset_class_def, IN_FUNSET, IN_UNIV, SUBSET_DEF] \\
             METIS_TAC []) \\
         CONJ_TAC (* disjoint *)
         >- (Q.X_GEN_TAC `k` >> Q.X_GEN_TAC `l` >> DISCH_TAC \\
             BETA_TAC >> ASM_SET_TAC []) \\
         STRIP_ASSUME_TAC (REWRITE_RULE [SIGMA_ALGEBRA_ALT]
                                        (ASSUME ``sigma_algebra (sigma sp sts)``)) \\
         Q.UNABBREV_TAC `A` >> POP_ASSUM MATCH_MP_TAC \\
         SIMP_TAC std_ss [IN_UNIV, IN_FUNSET] \\
         GEN_TAC >> MATCH_MP_TAC ALGEBRA_INTER \\
         CONJ_TAC >- ASM_REWRITE_TAC [] \\
         ASSUME_TAC (Q.SPECL [`sp`, `sts`] SIGMA_SUBSET_SUBSETS) \\
         CONJ_TAC >- PROVE_TAC [subset_class_def, IN_FUNSET, IN_UNIV, SUBSET_DEF] \\
         METIS_TAC []) \\
     DISCH_THEN (REWRITE_TAC o wrap) \\
     Know `v (BIGUNION (IMAGE (\i. f j INTER g i) univ(:num))) = suminf (v o (\i. f j INTER g i))`
     >- (`countably_additive (sp,A,v)` by PROVE_TAC [measure_space_def] \\
         POP_ASSUM (MATCH_MP_TAC o
                    (REWRITE_RULE [countably_additive_def, measurable_sets_def, measure_def])) \\
         CONJ_TAC
         >- (REWRITE_TAC [IN_UNIV, IN_FUNSET] >> GEN_TAC >> BETA_TAC \\
             Q.UNABBREV_TAC `A` >> MATCH_MP_TAC ALGEBRA_INTER \\
             CONJ_TAC >- PROVE_TAC [sigma_algebra_def] \\
             ASSUME_TAC (Q.SPECL [`sp`, `sts`] SIGMA_SUBSET_SUBSETS) \\
             CONJ_TAC >- PROVE_TAC [subset_class_def, IN_FUNSET, IN_UNIV, SUBSET_DEF] \\
             METIS_TAC []) \\
         CONJ_TAC (* disjoint *)
         >- (Q.X_GEN_TAC `k` >> Q.X_GEN_TAC `l` >> DISCH_TAC \\
             BETA_TAC >> ASM_SET_TAC []) \\
         STRIP_ASSUME_TAC (REWRITE_RULE [SIGMA_ALGEBRA_ALT]
                                        (ASSUME ``sigma_algebra (sigma sp sts)``)) \\
         Q.UNABBREV_TAC `A` >> POP_ASSUM MATCH_MP_TAC \\
         SIMP_TAC std_ss [IN_UNIV, IN_FUNSET] \\
         GEN_TAC >> MATCH_MP_TAC ALGEBRA_INTER \\
         CONJ_TAC >- ASM_REWRITE_TAC [] \\
         ASSUME_TAC (Q.SPECL [`sp`, `sts`] SIGMA_SUBSET_SUBSETS) \\
         CONJ_TAC >- PROVE_TAC [subset_class_def, IN_FUNSET, IN_UNIV, SUBSET_DEF] \\
         METIS_TAC []) \\
     DISCH_THEN (REWRITE_TAC o wrap) \\
     `u o (\i. f j INTER g i) = \i. u (f j INTER g i)` by METIS_TAC [o_DEF] \\
     POP_ASSUM (REWRITE_TAC o wrap) \\
     `v o (\i. f j INTER g i) = \i. v (f j INTER g i)` by METIS_TAC [o_DEF] \\
     POP_ASSUM (REWRITE_TAC o wrap) \\
     Know `(\i. u (f j INTER g i)) = (\i. v (f j INTER g i))`
     >- (FUN_EQ_TAC >> GEN_TAC >> BETA_TAC >> METIS_TAC []) \\
     DISCH_THEN (ONCE_REWRITE_TAC o wrap) \\
     KILL_TAC >> METIS_TAC [])
 >> DISCH_TAC
  (* Part 3: the main proof *)
 >> Know `!j. subsets (sigma sp sts) SUBSET subsets (D j)`
 >- (Q.PAT_ASSUM `dynkin sp sts = sigma sp sts` (ONCE_REWRITE_TAC o wrap o SYM) \\
     GEN_TAC >> `sts SUBSET subsets (D j)` by PROVE_TAC [] \\
     POP_ASSUM (MP_TAC o (MATCH_MP (Q.SPECL [`sp`, `sts`, `subsets (D j)`] DYNKIN_MONOTONE))) \\
     METIS_TAC [(Q.SPEC `D j` DYNKIN_OF_DYNKIN_SYSTEM)])
 >> DISCH_TAC
 >> Know `!j. A = subsets (D j)`
 >- (GEN_TAC >> REWRITE_TAC [GSYM SUBSET_SUBSET_EQ] \\
     CONJ_TAC >- PROVE_TAC [] \\
     REWRITE_TAC [SUBSET_DEF] \\
     Q.UNABBREV_TAC `D` >> BETA_TAC \\
     SIMP_TAC std_ss [subsets_def, GSPECIFICATION])
 >> DISCH_TAC
 >> Know `!j a. a IN A ==> (u (f j INTER a) = v (f j INTER a))`
 >- (ASM_REWRITE_TAC [] >> rpt GEN_TAC \\
     Q.UNABBREV_TAC `D` >> KILL_TAC >> BETA_TAC \\
     SIMP_TAC std_ss [subsets_def, GSPECIFICATION])
 >> DISCH_TAC
 >> Know `!a. a IN A ==> (u a = sup (IMAGE (u o (\i. (f i) INTER a)) UNIV))`
 >- (rpt STRIP_TAC \\
     Q.ABBREV_TAC `g = \i. f i INTER a` \\
     MATCH_MP_TAC EQ_SYM \\
     `u = measure (sp,A,u)` by PROVE_TAC [measure_def] \\
     POP_ASSUM (ONCE_REWRITE_TAC o wrap) \\
     MATCH_MP_TAC MONOTONE_CONVERGENCE \\ (* the "sup" is removed here! *)
     REWRITE_TAC [measurable_sets_def] \\
     CONJ_TAC >- ASM_REWRITE_TAC [] \\
     CONJ_TAC
     >- (REWRITE_TAC [IN_UNIV, IN_FUNSET] \\
         GEN_TAC >> Q.UNABBREV_TAC `g` >> BETA_TAC \\
         Q.UNABBREV_TAC `A` >> MATCH_MP_TAC ALGEBRA_INTER \\
         CONJ_TAC >- PROVE_TAC [sigma_algebra_def] \\
         ASSUME_TAC (Q.SPECL [`sp`, `sts`] SIGMA_SUBSET_SUBSETS) \\
         CONJ_TAC >- PROVE_TAC [subset_class_def, IN_FUNSET, IN_UNIV, SUBSET_DEF] \\
         ASM_REWRITE_TAC []) \\
     CONJ_TAC (* !n. g n SUBSET g (SUC n) *)
     >- (Q.UNABBREV_TAC `g` >> BETA_TAC \\
         GEN_TAC >> ASM_SET_TAC []) \\
  (* a = BIGUNION (IMAGE g univ(:num)) *)
     Q.UNABBREV_TAC `g` >> BETA_TAC \\
     REWRITE_TAC [GSYM BIGUNION_OVER_INTER_L] \\
     Suff `a SUBSET sp` >- PROVE_TAC [INTER_SUBSET_EQN] \\
     Q.UNABBREV_TAC `A` \\
     `subset_class sp (subsets (sigma sp sts))`
                by PROVE_TAC [sigma_algebra_def, algebra_def, SPACE_SIGMA] \\
     PROVE_TAC [subset_class_def])
 >> DISCH_TAC
 >> Know `!a. a IN subsets (sigma sp sts) ==>
              (v a = sup (IMAGE (v o (\i. (f i) INTER a)) UNIV))`
 >- (rpt STRIP_TAC \\
     Q.ABBREV_TAC `g = \i. f i INTER a` \\
     MATCH_MP_TAC EQ_SYM \\
     `v = measure (sp,A,v)` by PROVE_TAC [measure_def] \\
     POP_ASSUM (ONCE_REWRITE_TAC o wrap) \\
     MATCH_MP_TAC MONOTONE_CONVERGENCE \\ (* the "sup" is removed here! *)
     REWRITE_TAC [measurable_sets_def] \\
     CONJ_TAC >- ASM_REWRITE_TAC [] \\
     CONJ_TAC
     >- (REWRITE_TAC [IN_UNIV, IN_FUNSET] \\
         GEN_TAC >> Q.UNABBREV_TAC `g` >> BETA_TAC \\
         Q.UNABBREV_TAC `A` >> MATCH_MP_TAC ALGEBRA_INTER \\
         CONJ_TAC >- PROVE_TAC [sigma_algebra_def] \\
         ASSUME_TAC (Q.SPECL [`sp`, `sts`] SIGMA_SUBSET_SUBSETS) \\
         CONJ_TAC >- PROVE_TAC [subset_class_def, IN_FUNSET, IN_UNIV, SUBSET_DEF] \\
         ASM_REWRITE_TAC []) \\
     CONJ_TAC (* !n. g n SUBSET g (SUC n) *)
     >- (Q.UNABBREV_TAC `g` >> BETA_TAC \\
         GEN_TAC >> ASM_SET_TAC []) \\
  (* a = BIGUNION (IMAGE g univ(:num)) *)
     Q.UNABBREV_TAC `g` >> BETA_TAC \\
     REWRITE_TAC [GSYM BIGUNION_OVER_INTER_L] \\
     Suff `a SUBSET sp` >- PROVE_TAC [INTER_SUBSET_EQN] \\
     Q.UNABBREV_TAC `A` \\
     `subset_class sp (subsets (sigma sp sts))`
                by PROVE_TAC [sigma_algebra_def, algebra_def, SPACE_SIGMA] \\
     PROVE_TAC [subset_class_def])
 >> DISCH_TAC >> RES_TAC >> fs [o_DEF]);

(* In this version, added assums: `(u sp = v sp) /\ (u sp < PosInf)`
                  removed assums: everything about `f`
   c.f. https://en.wikipedia.org/wiki/Pi-system
 *)
val UNIQUENESS_OF_MEASURE_FINITE = store_thm
  ("UNIQUENESS_OF_MEASURE_FINITE",
  ``!sp sts u v.
      subset_class sp sts /\
      (!s t. s IN sts /\ t IN sts ==> s INTER t IN sts) /\
      measure_space (sp,subsets (sigma sp sts),u) /\
      measure_space (sp,subsets (sigma sp sts),v) /\
      (u sp = v sp) /\ (u sp < PosInf) /\ (!s. s IN sts ==> (u s = v s))
     ==>
      (!s. s IN subsets (sigma sp sts) ==> (u s = v s))``,
    rpt STRIP_TAC
 (* Part 1: some common facts *)
 >> IMP_RES_TAC SIGMA_ALGEBRA_SIGMA
 >> Q.ABBREV_TAC `A = subsets (sigma sp sts)`
 >> Q.ABBREV_TAC `D = (sp, {q | q IN A /\ (u q = v q)})`
 >> `space D = sp` by METIS_TAC [space_def]
 >> IMP_RES_TAC DYNKIN_THM
 >> Know `sts SUBSET subsets D`
 >- (REWRITE_TAC [SUBSET_DEF] >> rpt STRIP_TAC \\
     Q.UNABBREV_TAC `D` >> BETA_TAC \\
     SIMP_TAC std_ss [subsets_def, GSPECIFICATION] \\
     CONJ_TAC >- PROVE_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF] >> fs [])
 >> DISCH_TAC
 (* Part 2: D is dynkin system *)
 >> Know `dynkin_system D`
 >- (REWRITE_TAC [dynkin_system_def] \\
     CONJ_TAC (* subset_class (space D) (subsets D) *)
     >- (Q.PAT_X_ASSUM `space D = sp` (REWRITE_TAC o wrap) \\
         REWRITE_TAC [subset_class_def] >> GEN_TAC \\
         Q.UNABBREV_TAC `D` >> BETA_TAC \\
         SIMP_TAC std_ss [subsets_def, GSPECIFICATION] \\
         `subset_class sp A` by PROVE_TAC [SPACE_SIGMA, sigma_algebra_def, algebra_def] \\
         STRIP_TAC >> PROVE_TAC [subset_class_def]) \\
     CONJ_TAC (* space D IN subsets D *)
     >- (ASM_REWRITE_TAC [] \\
         Q.UNABBREV_TAC `D` >> BETA_TAC \\
         SIMP_TAC std_ss [subsets_def, GSPECIFICATION] \\
         CONJ_TAC (* sp IN A *)
         >- (Q.UNABBREV_TAC `A` \\
             Suff `space (sigma sp sts) IN subsets (sigma sp sts)` >- PROVE_TAC [SPACE_SIGMA] \\
             MATCH_MP_TAC (Q.SPEC `sigma sp sts` ALGEBRA_SPACE) \\
             PROVE_TAC [sigma_algebra_def]) \\
         ASM_REWRITE_TAC []) \\
     CONJ_TAC (* under COMPL *)
     >- (Q.X_GEN_TAC `a` >> ONCE_ASM_REWRITE_TAC [] \\
         Q.UNABBREV_TAC `D` >> BETA_TAC >> SIMP_TAC std_ss [subsets_def, GSPECIFICATION] \\
         STRIP_TAC >> CONJ_TAC (* sp DIFF a IN A *)
         >- (Q.UNABBREV_TAC `A` \\
             `sp DIFF a = space (sigma sp sts) DIFF a` by PROVE_TAC [SPACE_SIGMA] \\
             POP_ASSUM (REWRITE_TAC o wrap) \\
             MATCH_MP_TAC ALGEBRA_COMPL \\
             PROVE_TAC [sigma_algebra_def]) \\
         Know `u (sp DIFF a) = u sp - u a`
         >- (`u = measure (sp,A,u)` by PROVE_TAC [measure_def] \\
             POP_ASSUM (ONCE_REWRITE_TAC o wrap) \\
             MATCH_MP_TAC MEASURE_DIFF_SUBSET \\
             REWRITE_TAC [measurable_sets_def, measure_def] \\
             CONJ_TAC >- ASM_REWRITE_TAC [] \\
             STRONG_CONJ_TAC >- PROVE_TAC [sigma_algebra_def, ALGEBRA_SPACE, SPACE_SIGMA] \\
             DISCH_TAC \\
             CONJ_TAC >- ASM_REWRITE_TAC [] \\
             STRONG_CONJ_TAC (* a SUBSET sp *)
             >- (`subset_class sp A` by PROVE_TAC [sigma_algebra_def, algebra_def, SPACE_SIGMA] \\
                 PROVE_TAC [subset_class_def]) \\
             DISCH_TAC \\
             MATCH_MP_TAC let_trans \\
             Q.EXISTS_TAC `u sp` \\
             Reverse CONJ_TAC >- ASM_REWRITE_TAC [] \\
          (* u a <= u sp *)
             `u = measure (sp,A,u)` by PROVE_TAC [measure_def] \\
             POP_ASSUM (ONCE_REWRITE_TAC o wrap) \\
             MATCH_MP_TAC INCREASING \\
             CONJ_TAC >- PROVE_TAC [MEASURE_SPACE_INCREASING] \\
             ASM_REWRITE_TAC [measurable_sets_def]) \\
         DISCH_THEN (ONCE_REWRITE_TAC o wrap) \\
         Know `v (sp DIFF a) = v sp - v a`
         >- (`v = measure (sp,A,v)` by PROVE_TAC [measure_def] \\
             POP_ASSUM (ONCE_REWRITE_TAC o wrap) \\
             MATCH_MP_TAC MEASURE_DIFF_SUBSET \\
             REWRITE_TAC [measurable_sets_def, measure_def] \\
             CONJ_TAC >- ASM_REWRITE_TAC [] \\
             STRONG_CONJ_TAC >- PROVE_TAC [sigma_algebra_def, ALGEBRA_SPACE, SPACE_SIGMA] \\
             DISCH_TAC \\
             CONJ_TAC >- ASM_REWRITE_TAC [] \\
             STRONG_CONJ_TAC (* a SUBSET sp *)
             >- (`subset_class sp A` by PROVE_TAC [sigma_algebra_def, algebra_def, SPACE_SIGMA] \\
                 PROVE_TAC [subset_class_def]) \\
             DISCH_TAC \\
             MATCH_MP_TAC let_trans \\
             Q.EXISTS_TAC `v sp` \\
             Reverse CONJ_TAC >- PROVE_TAC [] \\
          (* v a <= v sp *)
             `v = measure (sp,A,v)` by PROVE_TAC [measure_def] \\
             POP_ASSUM (ONCE_REWRITE_TAC o wrap) \\
             MATCH_MP_TAC INCREASING \\
             CONJ_TAC >- PROVE_TAC [MEASURE_SPACE_INCREASING] \\
             ASM_REWRITE_TAC [measurable_sets_def]) \\
         DISCH_THEN (ONCE_REWRITE_TAC o wrap) >> fs []) \\
  (* under COUNTABLE UNION *)
     Q.X_GEN_TAC `g` >> rpt STRIP_TAC \\
     Q.UNABBREV_TAC `D` >> BETA_TAC \\
     Q.PAT_X_ASSUM `g IN X` MP_TAC \\
     SIMP_TAC std_ss [subsets_def, GSPECIFICATION, IN_UNIV, IN_FUNSET] \\
     STRIP_TAC >> CONJ_TAC
  (* BIGUNION (IMAGE g univ(:num)) IN A *)
     >- (Q.UNABBREV_TAC `A` \\
         STRIP_ASSUME_TAC (REWRITE_RULE [SIGMA_ALGEBRA_ALT]
                                        (ASSUME ``sigma_algebra (sigma sp sts)``)) \\
         POP_ASSUM MATCH_MP_TAC \\
         fs [IN_FUNSET, IN_UNIV]) \\
  (* u (BIGUNION (IMAGE g univ(:num))) = v (BIGUNION (IMAGE g univ(:num))) *)
     Know `u (BIGUNION (IMAGE g univ(:num))) = suminf (u o g)`
     >- (`countably_additive (sp,A,u)` by PROVE_TAC [measure_space_def] \\
         POP_ASSUM (MATCH_MP_TAC o
                    (REWRITE_RULE [countably_additive_def, measurable_sets_def, measure_def])) \\
         CONJ_TAC
         >- (REWRITE_TAC [IN_UNIV, IN_FUNSET] >> GEN_TAC >> METIS_TAC []) \\
         CONJ_TAC (* disjoint *)
         >- (Q.X_GEN_TAC `k` >> Q.X_GEN_TAC `l` >> DISCH_TAC >> METIS_TAC []) \\
         STRIP_ASSUME_TAC (REWRITE_RULE [SIGMA_ALGEBRA_ALT]
                                        (ASSUME ``sigma_algebra (sigma sp sts)``)) \\
         Q.UNABBREV_TAC `A` >> POP_ASSUM MATCH_MP_TAC \\
         SIMP_TAC std_ss [IN_UNIV, IN_FUNSET] >> METIS_TAC []) \\
     DISCH_THEN (REWRITE_TAC o wrap) \\
     Know `v (BIGUNION (IMAGE g univ(:num))) = suminf (v o g)`
     >- (`countably_additive (sp,A,v)` by PROVE_TAC [measure_space_def] \\
         POP_ASSUM (MATCH_MP_TAC o
                    (REWRITE_RULE [countably_additive_def, measurable_sets_def, measure_def])) \\
         CONJ_TAC
         >- (REWRITE_TAC [IN_UNIV, IN_FUNSET] >> GEN_TAC >> METIS_TAC []) \\
         CONJ_TAC (* disjoint *)
         >- (Q.X_GEN_TAC `k` >> Q.X_GEN_TAC `l` >> DISCH_TAC >> METIS_TAC []) \\
         STRIP_ASSUME_TAC (REWRITE_RULE [SIGMA_ALGEBRA_ALT]
                                        (ASSUME ``sigma_algebra (sigma sp sts)``)) \\
         Q.UNABBREV_TAC `A` >> POP_ASSUM MATCH_MP_TAC \\
         SIMP_TAC std_ss [IN_UNIV, IN_FUNSET] >> METIS_TAC []) \\
     DISCH_THEN (REWRITE_TAC o wrap) \\
     `u o g = \i. u (g i)` by METIS_TAC [o_DEF] \\
     POP_ASSUM (REWRITE_TAC o wrap) \\
     `v o g = \i. v (g i)` by METIS_TAC [o_DEF] \\
     POP_ASSUM (REWRITE_TAC o wrap) \\
     Know `(\i. u (g i)) = (\i. v (g i))`
     >- (FUN_EQ_TAC >> GEN_TAC >> BETA_TAC >> METIS_TAC []) \\
     DISCH_THEN (ONCE_REWRITE_TAC o wrap) \\
     KILL_TAC >> METIS_TAC [])
 >> DISCH_TAC
 (* Part 3: the main proof, much easier than those in UNIQUENESS_OF_MEASURE *)
 >> Know `subsets (sigma sp sts) SUBSET subsets D`
 >- (Q.PAT_ASSUM `dynkin sp sts = sigma sp sts` (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.PAT_ASSUM `sts SUBSET subsets D`
        (MP_TAC o (MATCH_MP (Q.SPECL [`sp`, `sts`, `subsets D`] DYNKIN_MONOTONE))) \\
     METIS_TAC [Q.SPEC `D` DYNKIN_OF_DYNKIN_SYSTEM])
 >> DISCH_TAC
 >> Know `A = subsets D`
 >- (REWRITE_TAC [GSYM SUBSET_SUBSET_EQ] \\
     CONJ_TAC >- PROVE_TAC [] \\
     REWRITE_TAC [SUBSET_DEF] \\
     Q.UNABBREV_TAC `D` >> BETA_TAC \\
     SIMP_TAC std_ss [subsets_def, GSPECIFICATION])
 >> DISCH_TAC
 >> Know `!a. a IN A ==> (u a = v a)`
 >- (ASM_REWRITE_TAC [] >> rpt GEN_TAC \\
     Q.UNABBREV_TAC `D` >> KILL_TAC >> BETA_TAC \\
     SIMP_TAC std_ss [subsets_def, GSPECIFICATION])
 >> DISCH_TAC >> RES_TAC);

(* Dynkin system is closed under subset diff, a little surprised *)
val DYNKIN_SYSTEM_DIFF_SUBSET = store_thm
  ("DYNKIN_SYSTEM_DIFF_SUBSET",
  ``!d s t. dynkin_system d /\ s IN subsets d /\ t IN subsets d /\ s SUBSET t ==>
            t DIFF s IN subsets d``,
    rpt STRIP_TAC
 >> `subset_class (space d) (subsets d)` by PROVE_TAC [dynkin_system_def]
 >> `t DIFF s = space d DIFF ((space d DIFF t) UNION s)` by ASM_SET_TAC [subset_class_def]
 >> POP_ORW
 >> MATCH_MP_TAC DYNKIN_SYSTEM_COMPL >> art []
 >> `DISJOINT (space d DIFF t) s` by ASM_SET_TAC [DISJOINT_DEF, subset_class_def]
 >> MATCH_MP_TAC DYNKIN_SYSTEM_DUNION >> art []
 >> MATCH_MP_TAC DYNKIN_SYSTEM_COMPL >> art []);

val DYNKIN_SYSTEM_PREMEASURE_INCREASING = store_thm
  ("DYNKIN_SYSTEM_PREMEASURE_INCREASING",
  ``!m. dynkin_system (m_space m, measurable_sets m) /\ premeasure m ==> increasing m``,
    rpt STRIP_TAC
 >> `additive m` by PROVE_TAC [DYNKIN_SYSTEM_PREMEASURE_ADDITIVE]
 >> fs [premeasure_def, increasing_def, positive_def]
 >> rpt STRIP_TAC
 >> `t = s UNION (t DIFF s)` by PROVE_TAC [UNION_DIFF] >> POP_ORW
 >> `DISJOINT s (t DIFF s)` by SET_TAC [DISJOINT_DEF]
 >> `t DIFF s IN measurable_sets m` by PROVE_TAC [DYNKIN_SYSTEM_DIFF_SUBSET, subsets_def]
 >> Know `measure m (s UNION (t DIFF s)) = measure m s + measure m (t DIFF s)`
 >- (MATCH_MP_TAC ADDITIVE >> art [] \\
     MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                        (Q.SPEC `(m_space m,measurable_sets m)` DYNKIN_SYSTEM_DUNION)) \\
     ASM_REWRITE_TAC []) >> Rewr'
 >> MATCH_MP_TAC le_addr_imp >> PROVE_TAC []);

(* ------------------------------------------------------------------------- *)
(*  Existence of Measure - Caratheodory's celebrated extension theorem       *)
(* ------------------------------------------------------------------------- *)

(* (measure m) is an outer measure in (m_space m, measurable_sets m), which may
   not even be an algebra but at least `{} IN measurable_sets m` should hold. *)
val outer_measure_space_def = Define `
    outer_measure_space m <=>
     subset_class (m_space m) (measurable_sets m) /\
     {} IN (measurable_sets m) /\
     positive m /\ increasing m /\ countably_subadditive m`;

(* Defition 18.1 of [1]: the family of countable S-covers

   Notice that `BIGUNION (IMAGE f UNIV)` needs not be disjoint or in `sts`
 *)
val countable_covers_def = Define
   `countable_covers (sts :'a set set) =
      \a. {f | f IN (univ(:num) -> sts) /\ a SUBSET (BIGUNION (IMAGE f UNIV))}`;

(* Defition 18.1 of [1]: outer measure of the set-function m for C (covering),
   which could be `coutable_covers sts`. *)
val outer_measure_def = Define
   `outer_measure (m :'a measure) (C :('a set) -> (num -> 'a set) set) =
      \a. inf {r | ?f. f IN (C a) /\ (suminf (m o f) = r)}`;

(* Defition 18.1 of [1]: m-measurable sets (caratheodory sets) of m *)
val caratheodory_sets_def = Define
   `caratheodory_sets (sp :'a set) (m :'a measure) =
      {a | a SUBSET sp /\ !q. q SUBSET sp ==> (m q = m (q INTER a) + m (q DIFF a))}`;

(* pre_measure_sapce ==> countably_additive ==> additive *)
val SEMIRING_PREMEASURE_ADDITIVE = store_thm
  ("SEMIRING_PREMEASURE_ADDITIVE",
  ``!m. semiring (m_space m, measurable_sets m) /\ premeasure m ==> additive m``,
    RW_TAC std_ss [premeasure_def]
 >> MATCH_MP_TAC COUNTABLY_ADDITIVE_ADDITIVE
 >> PROVE_TAC [SEMIRING_EMPTY, subsets_def]);

(* premeasure ==> countably_additive ==> finite_additive *)
val SEMIRING_PREMEASURE_FINITE_ADDITIVE = store_thm
  ("SEMIRING_PREMEASURE_FINITE_ADDITIVE",
  ``!m. semiring (m_space m, measurable_sets m) /\ premeasure m ==>
        finite_additive m``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC COUNTABLY_ADDITIVE_FINITE_ADDITIVE
 >> PROVE_TAC [SEMIRING_EMPTY, subsets_def, premeasure_def]);

(* This non-trivial result is needed by CARATHEODORY_SEMIRING *)
val SEMIRING_PREMEASURE_INCREASING = store_thm (* c.f. ADDITIVE_INCREASING *)
  ("SEMIRING_PREMEASURE_INCREASING",
  ``!m. semiring (m_space m, measurable_sets m) /\ premeasure m ==> increasing m``,
    rpt STRIP_TAC
 >> IMP_RES_TAC SEMIRING_PREMEASURE_FINITE_ADDITIVE
 >> fs [increasing_def, positive_def, premeasure_def]
 >> rpt STRIP_TAC
 >> `t = s UNION (t DIFF s)` by PROVE_TAC [UNION_DIFF] >> POP_ORW
 >> `DISJOINT s (t DIFF s)` by SET_TAC [DISJOINT_DEF]
 >> fs [semiring_def, space_def, subsets_def]
 >> `?c. c SUBSET measurable_sets m /\ FINITE c /\ disjoint c /\ (t DIFF s = BIGUNION c)`
        by PROVE_TAC [] >> art []
 >> REWRITE_TAC [GSYM BIGUNION_INSERT]
 >> Know `FINITE (s INSERT c) /\ disjoint (s INSERT c)`
 >- (CONJ_TAC >- PROVE_TAC [FINITE_INSERT] \\
     ONCE_REWRITE_TAC [INSERT_SING_UNION] \\
     MATCH_MP_TAC disjoint_union >> art [disjoint_sing, BIGUNION_SING] \\
     PROVE_TAC [DISJOINT_DEF])
 >> STRIP_TAC
 >> STRIP_ASSUME_TAC (MATCH_MP finite_disjoint_decomposition
                               (CONJ (ASSUME ``FINITE (s INSERT (c :'a set set))``)
                                     (ASSUME ``disjoint (s INSERT (c :'a set set))``)))
 >> ASM_REWRITE_TAC []
 >> Know `measure m (BIGUNION (IMAGE f (count n))) = SIGMA (measure m o f) (count n)`
 >- (fs [finite_additive_def] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     RW_TAC std_ss [] >- PROVE_TAC [SUBSET_DEF] \\
     Q.PAT_X_ASSUM `s INSERT c = IMAGE f (count n)` (REWRITE_TAC o wrap o (MATCH_MP EQ_SYM)) \\
     REWRITE_TAC [BIGUNION_INSERT] \\
     Q.PAT_X_ASSUM `t DIFF s = BIGUNION c` (REWRITE_TAC o wrap o (MATCH_MP EQ_SYM)) \\
    `s UNION (t DIFF s) = t` by PROVE_TAC [UNION_DIFF] \\
     POP_ASSUM (ASM_REWRITE_TAC o wrap))
 >> Rewr
 >> Know `SIGMA (measure m o f) (count n) = SIGMA (measure m) (IMAGE f (count n))`
 >- (MATCH_MP_TAC EQ_SYM >> irule EXTREAL_SUM_IMAGE_IMAGE \\
     REWRITE_TAC [FINITE_COUNT, IN_IMAGE, IN_COUNT] \\
     CONJ_TAC >- (DISJ1_TAC >> GEN_TAC >> STRIP_TAC \\
                  MATCH_MP_TAC pos_not_neginf >> art [] \\
                  fs [IN_INSERT] >> METIS_TAC [SUBSET_DEF]) \\
     MATCH_MP_TAC INJ_IMAGE \\
     Q.EXISTS_TAC `s INSERT c` \\
     RW_TAC std_ss [INJ_DEF, IN_COUNT] >> METIS_TAC [])
 >> Rewr'
 >> Q.PAT_X_ASSUM `s INSERT c = IMAGE f (count n)` (REWRITE_TAC o wrap o (MATCH_MP EQ_SYM))
 >> Know `SIGMA (measure m) (s INSERT c) = measure m s + SIGMA (measure m) (c DELETE s)`
 >- (STRIP_ASSUME_TAC (Q.ISPEC `measure m` EXTREAL_SUM_IMAGE_THM) \\
     POP_ASSUM MATCH_MP_TAC >> art [] \\
     DISJ2_TAC >> GEN_TAC >> DISCH_TAC >> MATCH_MP_TAC pos_not_neginf \\
     FIRST_X_ASSUM MATCH_MP_TAC >> fs [IN_INSERT] >> PROVE_TAC [SUBSET_DEF])
 >> Rewr
 >> MATCH_MP_TAC le_addr_imp
 >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS
 >> RW_TAC std_ss [FINITE_DELETE, IN_DELETE]
 >> PROVE_TAC [SUBSET_DEF]);

val RING_PREMEASURE_INCREASING = store_thm (* c.f. ADDITIVE_INCREASING *)
  ("RING_PREMEASURE_INCREASING",
  ``!m. ring (m_space m, measurable_sets m) /\ premeasure m ==> increasing m``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC SEMIRING_PREMEASURE_INCREASING >> art []
 >> IMP_RES_TAC RING_IMP_SEMIRING);

val ALGEBRA_PREMEASURE_INCREASING = store_thm (* c.f. ADDITIVE_INCREASING *)
  ("ALGEBRA_PREMEASURE_INCREASING",
  ``!m. algebra (m_space m, measurable_sets m) /\ premeasure m ==> increasing m``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC RING_PREMEASURE_INCREASING >> art []
 >> IMP_RES_TAC ALGEBRA_IMP_RING);

val RING_PREMEASURE_ADDITIVE = store_thm
  ("RING_PREMEASURE_ADDITIVE",
  ``!m. ring (m_space m, measurable_sets m) /\ premeasure m ==> additive m``,
    RW_TAC std_ss [premeasure_def]
 >> MATCH_MP_TAC COUNTABLY_ADDITIVE_ADDITIVE
 >> PROVE_TAC [RING_EMPTY, subsets_def]);

val RING_PREMEASURE_FINITE_ADDITIVE = store_thm
  ("RING_PREMEASURE_FINITE_ADDITIVE",
  ``!m. ring (m_space m, measurable_sets m) /\ premeasure m ==> finite_additive m``,
    RW_TAC std_ss [premeasure_def]
 >> MATCH_MP_TAC COUNTABLY_ADDITIVE_FINITE_ADDITIVE
 >> PROVE_TAC [RING_EMPTY, subsets_def]);

val RING_PREMEASURE_DIFF_SUBSET = store_thm
  ("RING_PREMEASURE_DIFF_SUBSET",
  ``!m s t. ring (m_space m, measurable_sets m) /\ premeasure m /\
        s IN measurable_sets m /\ t IN measurable_sets m /\ s SUBSET t /\
        measure m s < PosInf ==> (measure m (t DIFF s) = measure m t - measure m s)``,
    rpt STRIP_TAC
 >> `additive m` by PROVE_TAC [RING_PREMEASURE_ADDITIVE]
 >> Know `measure m s <> NegInf /\ measure m s <> PosInf`
 >- (CONJ_TAC >- PROVE_TAC [positive_not_infty, premeasure_def] \\
     art [lt_infty])
 >> DISCH_TAC
 >> Suff `measure m (t DIFF s) + measure m s = measure m t - measure m s + measure m s`
 >- (POP_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP EXTREAL_EQ_RADD)) \\
     PROVE_TAC [])
 >> POP_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP sub_add)) >> POP_ORW
 >> MATCH_MP_TAC EQ_SYM
 >> MATCH_MP_TAC ADDITIVE >> art []
 >> CONJ_TAC >- (MATCH_MP_TAC (((REWRITE_RULE [subsets_def]) o
                                (Q.SPEC `(m_space m, measurable_sets m)`)) RING_DIFF) \\
                 ASM_REWRITE_TAC [])
 >> ASM_SET_TAC [DISJOINT_DEF]);

val ALGEBRA_PREMEASURE_DIFF_SUBSET = store_thm
  ("ALGEBRA_PREMEASURE_DIFF_SUBSET",
  ``!m s t. algebra (m_space m, measurable_sets m) /\ premeasure m /\
        s IN measurable_sets m /\ t IN measurable_sets m /\ s SUBSET t /\
        measure m s < PosInf ==> (measure m (t DIFF s) = measure m t - measure m s)``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC RING_PREMEASURE_DIFF_SUBSET >> art []
 >> MATCH_MP_TAC ALGEBRA_IMP_RING >> art []);

val ALGEBRA_PREMEASURE_COMPL = store_thm
  ("ALGEBRA_PREMEASURE_COMPL",
  ``!m s. algebra (m_space m, measurable_sets m) /\ premeasure m /\
        s IN measurable_sets m /\ measure m s < PosInf ==>
        (measure m (m_space m DIFF s) = measure m (m_space m) - measure m s)``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC ALGEBRA_PREMEASURE_DIFF_SUBSET >> art []
 >> CONJ_TAC >- PROVE_TAC [ALGEBRA_SPACE, space_def, subsets_def]
 >> fs [algebra_def, subset_class_def, space_def, subsets_def]);

val RING_PREMEASURE_STRONG_ADDITIVE = store_thm
  ("RING_PREMEASURE_STRONG_ADDITIVE",
  ``!m s t. ring (m_space m, measurable_sets m) /\ premeasure m /\
        s IN measurable_sets m /\ t IN measurable_sets m ==>
        (measure m (s UNION t) + measure m (s INTER t) = measure m s + measure m t)``,
    rpt STRIP_TAC
 >> `additive m` by PROVE_TAC [RING_PREMEASURE_ADDITIVE]
 >> `s UNION t = s UNION (t DIFF s)` by SET_TAC [] >> POP_ORW
 >> `s INTER t IN measurable_sets m` by PROVE_TAC [RING_INTER, subsets_def]
 >> `t DIFF s IN measurable_sets m` by PROVE_TAC [RING_DIFF, subsets_def]
 >> Know `measure m (s UNION (t DIFF s)) = measure m s + measure m (t DIFF s)`
 >- (MATCH_MP_TAC ADDITIVE >> art [] \\
     CONJ_TAC >- SET_TAC [DISJOINT_DEF] \\
     PROVE_TAC [RING_UNION, subsets_def])
 >> Rewr'
 >> Know `measure m s + measure m (t DIFF s) + measure m (s INTER t) =
          measure m s + (measure m (t DIFF s) + measure m (s INTER t))`
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC add_assoc >> DISJ1_TAC \\
     RW_TAC std_ss [] \\ (* 3 subgoals, same tactics *)
     MATCH_MP_TAC pos_not_neginf >> PROVE_TAC [premeasure_def, positive_def])
 >> Rewr'
 >> Know `measure m (t DIFF s) + measure m (s INTER t) = measure m t`
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC ADDITIVE >> art [] \\
     SET_TAC [DISJOINT_DEF])
 >> Rewr);

val ALGEBRA_PREMEASURE_STRONG_ADDITIVE = store_thm
  ("ALGEBRA_PREMEASURE_STRONG_ADDITIVE",
  ``!m s t. algebra (m_space m, measurable_sets m) /\ premeasure m /\
        s IN measurable_sets m /\ t IN measurable_sets m ==>
        (measure m (s UNION t) + measure m (s INTER t) = measure m s + measure m t)``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC RING_PREMEASURE_STRONG_ADDITIVE >> art []
 >> MATCH_MP_TAC ALGEBRA_IMP_RING >> art []);

val MEASURE_SPACE_STRONG_ADDITIVE = store_thm
  ("MEASURE_SPACE_STRONG_ADDITIVE",
  ``!m s t. measure_space m /\
        s IN measurable_sets m /\ t IN measurable_sets m ==>
        (measure m (s UNION t) + measure m (s INTER t) = measure m s + measure m t)``,
    RW_TAC std_ss [measure_space_def]
 >> MATCH_MP_TAC ALGEBRA_PREMEASURE_STRONG_ADDITIVE >> art []
 >> PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, premeasure_def]);

(* This is a more general version of MEASURE_COUNTABLE_INCREASING,
   `s IN measurable_sets m` must be added into antecedents. *)
Theorem RING_PREMEASURE_COUNTABLE_INCREASING :
    !m s f.
       ring (m_space m, measurable_sets m) /\ premeasure m /\
       f IN (UNIV -> measurable_sets m) /\
       (f 0 = {}) /\ (!n. f n SUBSET f (SUC n)) /\
       (s = BIGUNION (IMAGE f UNIV)) /\ s IN measurable_sets m ==>
       (sup (IMAGE (measure m o f) UNIV) = measure m s)
Proof
    RW_TAC std_ss [IN_FUNSET, IN_UNIV, premeasure_def]
 >> Know `measure m o f = (\n. SIGMA (measure m o (\m. f (SUC m) DIFF f m)) (count n))`
 >- (FUN_EQ_TAC \\
     Induct >- (RW_TAC std_ss [o_THM, RING_EMPTY, subsets_def, COUNT_ZERO,
                               EXTREAL_SUM_IMAGE_EMPTY] >> PROVE_TAC [positive_def]) \\
     POP_ASSUM (MP_TAC o SYM) \\
     RW_TAC arith_ss [o_THM, COUNT_SUC] \\
     Know `!n. (measure m o (\m. f (SUC m) DIFF f m)) n <> NegInf`
     >- (RW_TAC std_ss [] \\
        `f (SUC n) DIFF f n IN measurable_sets m` by METIS_TAC [RING_DIFF, subsets_def] \\
         METIS_TAC [positive_def, positive_not_infty, o_DEF]) >> DISCH_TAC \\
    `FINITE (count x)` by RW_TAC std_ss [FINITE_COUNT] \\
    `count x DELETE x = count x`
       by METIS_TAC [IN_COUNT, DELETE_NON_ELEMENT, LESS_REFL] \\
     RW_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY] \\
    `additive m` by PROVE_TAC [RING_PREMEASURE_ADDITIVE, premeasure_def] \\
     MATCH_MP_TAC ADDITIVE \\
     FULL_SIMP_TAC arith_ss [EXTENSION, IN_UNION, IN_DIFF, DISJOINT_DEF, NOT_IN_EMPTY,
                             IN_INTER, SUBSET_DEF, IN_COUNT, IN_DELETE] \\
     (MP_TAC o REWRITE_RULE [subsets_def, space_def] o
      (Q.SPEC `(m_space m, measurable_sets m)`)) RING_DIFF >> PROVE_TAC [])
 >> Rewr'
 >> Know `!n. 0 <= (measure m o (\m. f (SUC m) DIFF f m)) n`
 >- (RW_TAC std_ss [o_DEF] \\
     fs [positive_def] >> FIRST_X_ASSUM MATCH_MP_TAC \\
     MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                    (Q.SPEC `(m_space m,measurable_sets m)` RING_DIFF)) >> art [])
 >> DISCH_THEN (MP_TAC o SYM o (MATCH_MP ext_suminf_alt_pos)) >> Rewr'
 >> MATCH_MP_TAC COUNTABLY_ADDITIVE >> art []
 >> CONJ_TAC
 >- (RW_TAC std_ss [IN_UNIV, IN_FUNSET] \\
     (MATCH_MP_TAC o REWRITE_RULE [subsets_def, space_def] o
      (Q.SPEC `(m_space m, measurable_sets m)`)) RING_DIFF \\
     FULL_SIMP_TAC std_ss [])
 >> CONJ_TAC
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC DISJOINT_DIFFS \\
     Q.EXISTS_TAC `f` >> RW_TAC std_ss [])
 >> RW_TAC std_ss [IN_BIGUNION_IMAGE,IN_DIFF,IN_UNIV,EXTENSION]
 >> Reverse EQ_TAC >> RW_TAC std_ss [] >- METIS_TAC []
 >> Induct_on `x'` >- RW_TAC std_ss [NOT_IN_EMPTY]
 >> METIS_TAC []
QED

val ALGEBRA_PREMEASURE_COUNTABLE_INCREASING = store_thm
  ("ALGEBRA_PREMEASURE_COUNTABLE_INCREASING",
  ``!m s f.
       algebra (m_space m, measurable_sets m) /\ premeasure m /\
       f IN (UNIV -> measurable_sets m) /\
       (f 0 = {}) /\ (!n. f n SUBSET f (SUC n)) /\
       (s = BIGUNION (IMAGE f UNIV)) /\ s IN measurable_sets m ==>
       (sup (IMAGE (measure m o f) UNIV) = measure m s)``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC RING_PREMEASURE_COUNTABLE_INCREASING >> art []
 >> MATCH_MP_TAC ALGEBRA_IMP_RING >> art []);

val RING_PREMEASURE_SUBADDITIVE = store_thm
  ("RING_PREMEASURE_SUBADDITIVE",
  ``!m. ring (m_space m, measurable_sets m) /\ premeasure m ==> subadditive m``,
    RW_TAC std_ss [subadditive_def]
 >> `measure m s + measure m t = measure m (s UNION t) + measure m (s INTER t)`
        by PROVE_TAC [RING_PREMEASURE_STRONG_ADDITIVE]
 >> POP_ORW
 >> MATCH_MP_TAC le_addr_imp
 >> `s INTER t IN measurable_sets m` by PROVE_TAC [RING_INTER, subsets_def]
 >> PROVE_TAC [premeasure_def, positive_def]);

val ALGEBRA_PREMEASURE_SUBADDITIVE = store_thm
  ("ALGEBRA_PREMEASURE_SUBADDITIVE",
  ``!m. algebra (m_space m, measurable_sets m) /\ premeasure m ==> subadditive m``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC RING_PREMEASURE_SUBADDITIVE >> art []
 >> MATCH_MP_TAC ALGEBRA_IMP_RING >> art []);

val MEASURE_SPACE_SUBADDITIVE = store_thm
  ("MEASURE_SPACE_SUBADDITIVE",
  ``!m. measure_space m ==> subadditive m``,
    RW_TAC std_ss [measure_space_def]
 >> MATCH_MP_TAC ALGEBRA_PREMEASURE_SUBADDITIVE >> art []
 >> PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, premeasure_def]);

val RING_PREMEASURE_FINITE_SUBADDITIVE = store_thm
  ("RING_PREMEASURE_FINITE_SUBADDITIVE",
  ``!m. ring (m_space m, measurable_sets m) /\ premeasure m ==> finite_subadditive m``,
    rpt STRIP_TAC
 >> `subadditive m` by PROVE_TAC [RING_PREMEASURE_SUBADDITIVE]
 >> fs [premeasure_def, finite_subadditive_def]
 >> GEN_TAC >> Induct_on `n`
 >- (RW_TAC arith_ss [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY, EXTREAL_SUM_IMAGE_EMPTY] \\
     PROVE_TAC [le_refl, positive_def])
 >> RW_TAC arith_ss [COUNT_SUC, IMAGE_INSERT, BIGUNION_INSERT]
 >> `!i. i < n ==> f i IN measurable_sets m` by RW_TAC arith_ss []
 >> Know `BIGUNION (IMAGE f (count n)) IN measurable_sets m`
 >- (MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                        (Q.SPEC `(m_space m,measurable_sets m)` RING_FINITE_UNION_ALT)) \\
     ASM_REWRITE_TAC [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM `X ==> measure m (BIGUNION (IMAGE f (count n))) <=
         SIGMA (measure m o f) (count n)` MP_TAC
 >> RW_TAC std_ss []
 >> Know `SIGMA (measure m o f) (n INSERT count n) =
                (measure m o f) n + SIGMA (measure m o f) ((count n) DELETE n)`
 >- (irule EXTREAL_SUM_IMAGE_PROPERTY \\
     SIMP_TAC std_ss [FINITE_COUNT, IN_INSERT, IN_COUNT] \\
     DISJ1_TAC >> GEN_TAC >> DISCH_TAC \\
     MATCH_MP_TAC pos_not_neginf \\
     METIS_TAC [positive_def, LESS_SUC_REFL]) >> Rewr'
 >> Know `count n DELETE n = count n`
 >- (REWRITE_TAC [EXTENSION] \\
     GEN_TAC >> REWRITE_TAC [IN_DELETE, IN_COUNT] \\
     RW_TAC arith_ss []) >> Rewr'
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC `measure m (f n) + measure m (BIGUNION (IMAGE f (count n)))`
 >> CONJ_TAC
 >- (MATCH_MP_TAC SUBADDITIVE >> art [] \\
     PROVE_TAC [positive_def, LESS_SUC_REFL])
 >> fs [o_DEF] >> MATCH_MP_TAC le_ladd_imp >> art []);

val ALGEBRA_PREMEASURE_FINITE_SUBADDITIVE = store_thm
  ("ALGEBRA_PREMEASURE_FINITE_SUBADDITIVE",
  ``!m. algebra (m_space m, measurable_sets m) /\ premeasure m ==> finite_subadditive m``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC RING_PREMEASURE_FINITE_SUBADDITIVE >> art []
 >> MATCH_MP_TAC ALGEBRA_IMP_RING >> art []);

val MEASURE_SPACE_FINITE_SUBADDITIVE = store_thm
  ("MEASURE_SPACE_FINITE_SUBADDITIVE",
  ``!m. measure_space m ==> finite_subadditive m``,
    RW_TAC std_ss [measure_space_def]
 >> MATCH_MP_TAC ALGEBRA_PREMEASURE_FINITE_SUBADDITIVE >> art []
 >> PROVE_TAC [SIGMA_ALGEBRA_ALGEBRA, premeasure_def]);

(* This non-trivial result is needed by CARATHEODORY_SEMIRING *)
Theorem RING_PREMEASURE_COUNTABLY_SUBADDITIVE :
    !m. ring (m_space m, measurable_sets m) /\ premeasure m ==>
        countably_subadditive m
Proof
    RW_TAC std_ss [countably_subadditive_def, premeasure_def]
 >> STRIP_ASSUME_TAC (Q.SPEC `f` SETS_TO_INCREASING_SETS') >> art []
 >> Know `g IN (univ(:num) -> measurable_sets m)`
 >- (REWRITE_TAC [IN_FUNSET, IN_UNIV] \\
     GEN_TAC >> art [] \\
     MATCH_MP_TAC (((REWRITE_RULE [subsets_def]) o
                    (Q.SPEC `(m_space m,measurable_sets m)`)) RING_FINITE_UNION_ALT) \\
     RW_TAC std_ss [] >> PROVE_TAC [IN_FUNSET, IN_UNIV])
 >> DISCH_TAC
 >> Know `measure m (BIGUNION (IMAGE g univ(:num))) = sup (IMAGE (measure m o g) UNIV)`
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC RING_PREMEASURE_COUNTABLE_INCREASING >> art [premeasure_def] \\
     PROVE_TAC []) >> Rewr'
 (* stage work *)
 >> Know `!n. 0 <= (measure m o f) n`
 >- (RW_TAC std_ss [o_DEF] \\
     fs [positive_def] >> FIRST_X_ASSUM MATCH_MP_TAC \\
     fs [IN_FUNSET, IN_UNIV])
 >> DISCH_THEN (MP_TAC o (MATCH_MP ext_suminf_alt_pos)) >> Rewr'
 >> MATCH_MP_TAC sup_mono
 >> GEN_TAC
 >> GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [o_DEF]
 >> BETA_TAC >> art []
 >> MATCH_MP_TAC FINITE_SUBADDITIVE >> art []
 >> fs [IN_FUNSET, IN_UNIV]
 >> CONJ_TAC
 >- (MATCH_MP_TAC RING_PREMEASURE_FINITE_SUBADDITIVE >> art [premeasure_def])
 >> MATCH_MP_TAC (((REWRITE_RULE [subsets_def]) o
                   (Q.SPEC `(m_space m,measurable_sets m)`)) RING_FINITE_UNION_ALT)
 >> ASM_REWRITE_TAC []
QED

val ALGEBRA_PREMEASURE_COUNTABLY_SUBADDITIVE = store_thm
  ("ALGEBRA_PREMEASURE_COUNTABLY_SUBADDITIVE",
  ``!m. algebra (m_space m, measurable_sets m) /\ premeasure m ==>
        countably_subadditive m``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC RING_PREMEASURE_COUNTABLY_SUBADDITIVE >> art []
 >> MATCH_MP_TAC ALGEBRA_IMP_RING >> art []);

(* Proposition 4.3 (viii) [1] *)
val MEASURE_SPACE_COUNTABLY_SUBADDITIVE = store_thm
  ("MEASURE_SPACE_COUNTABLY_SUBADDITIVE",
  ``!m. measure_space m ==> countably_subadditive m``,
    RW_TAC std_ss [measure_space_def, sigma_algebra_def]
 >> MATCH_MP_TAC RING_PREMEASURE_COUNTABLY_SUBADDITIVE
 >> ASM_REWRITE_TAC [premeasure_def]
 >> MATCH_MP_TAC ALGEBRA_IMP_RING >> art []);

val RING_ADDITIVE_INCREASING = store_thm (* c.f. ADDITIVE_INCREASING *)
  ("RING_ADDITIVE_INCREASING",
  ``!m. ring (m_space m, measurable_sets m) /\ positive m /\ additive m ==>
        increasing m``,
    RW_TAC std_ss [increasing_def, positive_def]
 >> Suff
      `?u. u IN measurable_sets m /\ (measure m t = measure m s + measure m u)`
 >- METIS_TAC [le_addr_imp]
 >> Q.EXISTS_TAC `t DIFF s`
 >> STRONG_CONJ_TAC >- PROVE_TAC [RING_DIFF, subsets_def]
 >> RW_TAC std_ss []
 >> MATCH_MP_TAC ADDITIVE
 >> RW_TAC std_ss [DISJOINT_DEF,IN_DIFF,IN_UNION,EXTENSION,IN_INTER,NOT_IN_EMPTY]
 >> PROVE_TAC [SUBSET_DEF]);

val OUTER_MEASURE_SPACE_POSITIVE = store_thm
  ("OUTER_MEASURE_SPACE_POSITIVE",
  ``!m. outer_measure_space m ==> positive m``,
    PROVE_TAC [outer_measure_space_def]);

val OUTER_MEASURE_SPACE_SUBADDITIVE = store_thm
  ("OUTER_MEASURE_SPACE_SUBADDITIVE",
  ``!m. outer_measure_space m ==> subadditive m``,
    RW_TAC std_ss [outer_measure_space_def]
 >> MATCH_MP_TAC COUNTABLY_SUBADDITIVE_SUBADDITIVE
 >> ASM_REWRITE_TAC []);

val OUTER_MEASURE_SPACE_FINITE_SUBADDITIVE = store_thm
  ("OUTER_MEASURE_SPACE_FINITE_SUBADDITIVE",
  ``!m. outer_measure_space m ==> finite_subadditive m``,
    RW_TAC std_ss [outer_measure_space_def]
 >> MATCH_MP_TAC COUNTABLY_SUBADDITIVE_FINITE_SUBADDITIVE
 >> ASM_REWRITE_TAC []);

(* c.f. MEASURE_SPACE_RESTRICTED *)
val MEASURE_SPACE_RESTRICTION = store_thm
  ("MEASURE_SPACE_RESTRICTION",
  ``!sp sts m sub. measure_space (sp,sts,m) /\ sub SUBSET sts /\ sigma_algebra (sp,sub) ==>
                   measure_space (sp,sub,m)``,
    RW_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def]
 >- (REWRITE_TAC [positive_def, measure_def, measurable_sets_def] \\
     CONJ_TAC >- PROVE_TAC [positive_def, measure_def, measurable_sets_def] \\
     rpt STRIP_TAC >> fs [positive_def, measure_def, measurable_sets_def] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> PROVE_TAC [SUBSET_DEF])
 >> fs [countably_additive_def, IN_FUNSET, IN_UNIV, measurable_sets_def, measure_def]
 >> RW_TAC std_ss []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> PROVE_TAC [SUBSET_DEF]);

(* Theorem 18.2 of [1]. Given (sp,sts,m) and u = outer_measure m (countable_covers sts):

   (*1*) u is an outer measure such that u(x) <= m(x) for all x IN sts;
   (*2*) A (caratheodory_sets sp u) is a sigma-algebra and u|A is a measure;
   (*3*) u is maximal: if v is another outer measure such that v(x) <= mu(x)
         for all x IN sts, then v(x) <= m(x) for all x SUBSET sp.

   NOTE: there's no structual requirements on `sts` and `mu` (except for `{} IN sts`);
         and (*3*) is not needed by CARATHEODORY_SEMIRING.
 *)
Theorem OUTER_MEASURE_CONSTRUCTION :
  !sp sts m u. subset_class sp sts /\ {} IN sts /\ positive (sp,sts,m) /\
               (u = outer_measure m (countable_covers sts)) ==>
   (*1*) outer_measure_space (sp,POW sp,u) /\ (!x. x IN sts ==> u x <= m x) /\
   (*2*) measure_space (sp,caratheodory_sets sp u,u) /\
   (*3*) !v. outer_measure_space (sp,POW sp,v) /\ (!x. x IN sts ==> v x <= m x)
             ==> !x. x SUBSET sp ==> v x <= u x
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> rename1 `positive (sp,sts,mu)` >> rename1 `m = _` (* m -> mu, u -> m *)
 >> Q.ABBREV_TAC `C = countable_covers sts`
 >> Q.ABBREV_TAC `A = caratheodory_sets sp m`
 >> STRONG_CONJ_TAC
 >- (REWRITE_TAC [outer_measure_space_def, m_space_def, measurable_sets_def,
                  subset_class_POW, EMPTY_IN_POW] \\
     fs [countable_covers_def, outer_measure_def] \\
     Q.PAT_ASSUM `m = _` (REWRITE_TAC o wrap o (MATCH_MP EQ_SYM)) \\ (* recover `m` *)
  (* C is anti-monotone (or antitone) *)
     Know `!a b. a SUBSET b ==> (C b) SUBSET (C a)`
     >- (rpt STRIP_TAC \\
         Q.UNABBREV_TAC `C` >> BETA_TAC \\
         ONCE_REWRITE_TAC [SUBSET_DEF] \\
         SET_SPEC_TAC [IN_FUNSET, IN_UNIV] \\
         RW_TAC std_ss [] >> PROVE_TAC [SUBSET_TRANS]) >> DISCH_TAC \\
  (* m is positive *)
     Know `!s. s SUBSET sp ==> 0 <= m s`
     >- (Q.PAT_X_ASSUM `m = _` ((SIMP_TAC std_ss) o wrap) \\
         rpt STRIP_TAC >> REWRITE_TAC [le_inf'] \\
         GEN_TAC >> RW_TAC std_ss [GSPECIFICATION] \\
         MATCH_MP_TAC ext_suminf_pos \\
         GEN_TAC >> SIMP_TAC std_ss [o_DEF] \\
         fs [positive_def, measure_def, measurable_sets_def] \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
         POP_ASSUM MP_TAC \\
         Q.UNABBREV_TAC `C` >> BETA_TAC \\
         RW_TAC std_ss [GSPECIFICATION, IN_FUNSET, IN_UNIV]) >> DISCH_TAC \\
  (* joint-property I of C and m *)
     Know `!a. m a < PosInf ==> (C a) <> EMPTY`
     >- (GEN_TAC >> REWRITE_TAC [GSYM lt_infty] \\
         MATCH_MP_TAC MONO_NOT \\
         Q.UNABBREV_TAC `C` >> BETA_TAC \\
         Q.PAT_X_ASSUM `m = _` (fs o wrap) \\
         SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY] >> DISCH_TAC \\
         Know `!r. (?f. f IN (univ(:num) -> sts) /\ a SUBSET BIGUNION (IMAGE f univ(:num)) /\
                        (suminf (mu o f) = r)) = F`
         >- (GEN_TAC >> MATCH_MP_TAC NOT_F >> SIMP_TAC bool_ss [] \\
             GEN_TAC >> POP_ASSUM MP_TAC \\
             SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY] \\
             METIS_TAC []) >> DISCH_TAC \\
         Know `{r | ?f. (f IN (univ(:num) -> sts) /\ a SUBSET BIGUNION (IMAGE f univ(:num))) /\
                        (suminf (mu o f) = r)} = EMPTY`
         >- ASM_SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY] \\
         DISCH_THEN (ONCE_REWRITE_TAC o wrap) >> KILL_TAC \\
         ACCEPT_TAC inf_empty) >> DISCH_TAC \\
  (* joint-property II of C and m *)
     Know `!a. m a < PosInf ==> ?f. f IN (C a) /\ suminf (mu o f) <> PosInf`
     >- (GEN_TAC \\
         Q.PAT_X_ASSUM `m = _` (fs o wrap) \\
         REWRITE_TAC [Q.SPECL [`{r | ?f. f IN (C :('a set)->(num->'a set)->bool) (a :'a set) /\
                                         (suminf (mu o f) = r)}`, `PosInf`] (GSYM inf_lt')] \\
         RW_TAC std_ss [GSPECIFICATION] \\
         Q.EXISTS_TAC `f` >> PROVE_TAC [lt_infty]) >> DISCH_TAC \\
  (* joint-property III of C and m *)
     Know `!a e. a SUBSET sp /\ 0 < e /\ m a < PosInf ==>
                 ?f. f IN (C a) /\ suminf (mu o f) <= m a + e`
     >- (rpt STRIP_TAC \\
         MP_TAC (Q.SPEC `{r | ?f. f IN ((C :('a->bool)->(num->'a->bool)->bool) (a :'a->bool)) /\
                                  (suminf (mu o f) = r)}` le_inf_epsilon_set) \\
        `inf {r | ?f. f IN (C a) /\ (suminf (mu o f) = r)} = m a` by METIS_TAC [] \\
         POP_ASSUM (REWRITE_TAC o wrap) \\
         SIMP_TAC std_ss [GSPECIFICATION] \\
         DISCH_THEN (MP_TAC o (Q.SPEC `e`)) \\
        `(?x. (?f. f IN C a /\ (suminf (mu o f) = x)) /\ x <= m a + e) =
         (?f. f IN C a /\ suminf (mu o f) <= m a + e)` by METIS_TAC [] \\
         POP_ASSUM (REWRITE_TAC o wrap) \\
        `(?x. (?f. f IN C a /\ (suminf (mu o f) = x)) /\ x <> PosInf) =
         (?f. f IN C a /\ (suminf (mu o f) <> PosInf))` by METIS_TAC [] \\
         POP_ASSUM (REWRITE_TAC o wrap) \\
         DISCH_THEN MATCH_MP_TAC \\
         ASM_REWRITE_TAC [] \\
         CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> ASM_REWRITE_TAC []) \\
         METIS_TAC [lt_infty, extreal_of_num_def, extreal_not_infty, lte_trans]) >> DISCH_TAC \\
  (* joint-property IV of C and m *)
     Know `!a f. f IN (univ(:num) -> sts) /\ a SUBSET BIGUNION (IMAGE f univ(:num)) ==>
                 m a <= suminf (mu o f)`
     >- (rpt STRIP_TAC \\
         Q.PAT_X_ASSUM `m = _` (fs o wrap) \\
         MATCH_MP_TAC inf_le_imp' >> SET_SPEC_TAC [] \\
         Q.EXISTS_TAC `f` >> REWRITE_TAC [] \\
         Q.UNABBREV_TAC `C` >> BETA_TAC \\
         ASM_SIMP_TAC std_ss [GSPECIFICATION]) >> DISCH_TAC \\
  (* OM1. positive (sp, POW sp, m) *)
     STRONG_CONJ_TAC
     >- (REWRITE_TAC [positive_def, measure_def, measurable_sets_def, IN_POW] \\
         Reverse CONJ_TAC >- art [] \\
         Q.PAT_X_ASSUM `m = _` (fs o wrap) \\
         ONCE_REWRITE_TAC [GSYM le_antisym] \\
         Reverse CONJ_TAC
         >- (REWRITE_TAC [le_inf'] \\
             RW_TAC std_ss [GSPECIFICATION] \\
             Know `!n. 0 <= (mu o f) n`
             >- (Q.UNABBREV_TAC `C` \\
                 FULL_SIMP_TAC std_ss [positive_def, measure_def,
                                       GSPECIFICATION, IN_FUNSET,
                                       IN_UNIV, measurable_sets_def]) \\
             DISCH_THEN (MP_TAC o (MATCH_MP ext_suminf_alt_pos)) >> Rewr' \\
             MATCH_MP_TAC le_sup_imp' \\
             REWRITE_TAC [IN_IMAGE, IN_UNIV] \\
             Q.EXISTS_TAC `0` >> BETA_TAC \\
             REWRITE_TAC [COUNT_ZERO, EXTREAL_SUM_IMAGE_EMPTY]) \\
         MATCH_MP_TAC inf_le_imp' \\
         RW_TAC std_ss [GSPECIFICATION] \\
         Q.EXISTS_TAC `\n. EMPTY` \\
         REWRITE_TAC [o_DEF] \\
         Reverse CONJ_TAC >- (MATCH_MP_TAC ext_suminf_zero >> GEN_TAC >> BETA_TAC \\
                              PROVE_TAC [positive_def, measure_def]) \\
         Q.UNABBREV_TAC `C` >> BETA_TAC \\
         RW_TAC std_ss [EMPTY_SUBSET, GSPECIFICATION, IN_FUNSET, IN_UNIV]) >> DISCH_TAC \\
  (* OM2. increasing (sp, POW sp, m) *)
     STRONG_CONJ_TAC
     >- (RW_TAC std_ss [increasing_def, measurable_sets_def, measure_def, IN_POW] \\
         (* equivalent definition of `m` in IMAGE, use when needed *)
         Know `!S. {r | ?f. f IN S /\ (suminf (mu o f) = r)} = IMAGE (\f. (suminf (mu o f))) S`
         >- (GEN_TAC >> RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_IMAGE, o_DEF] \\
             METIS_TAC []) \\
         DISCH_THEN (REWRITE_TAC o wrap) \\
         MATCH_MP_TAC inf_mono_subset \\
         PROVE_TAC [IMAGE_SUBSET]) >> DISCH_TAC \\
  (* OM3. countably_subadditive (sp, POW sp, m) *)
     SIMP_TAC std_ss [countably_subadditive_def, measure_def, measurable_sets_def,
                      IN_FUNSET, IN_UNIV, IN_POW] \\
     rpt STRIP_TAC \\
  (* assume wlog: !x. m (f x) < PosInf *)
     Reverse (Cases_on `!x. m (f x) < PosInf`)
     >- (REWRITE_TAC [o_DEF] \\
         POP_ASSUM (STRIP_ASSUME_TAC o (SIMP_RULE std_ss [GSYM lt_infty])) \\
         Suff `suminf (\x. m (f x)) = PosInf`
         >- (DISCH_THEN (ONCE_REWRITE_TAC o wrap) >> REWRITE_TAC [le_infty]) \\
         MATCH_MP_TAC ext_suminf_posinf >> BETA_TAC \\
         CONJ_TAC >- PROVE_TAC [positive_def, measurable_sets_def, measure_def, IN_POW] \\
         Q.EXISTS_TAC `x` >> art []) \\
  (* assume wlog: suminf (m o f) < PosInf *)
     Reverse (Cases_on `suminf (m o f) < PosInf`)
     >- (fs [GSYM lt_infty] >> REWRITE_TAC [le_infty]) \\
  (* m (BIGUNION (IMAGE f univ(:num))) <= suminf (m o f) *)
     MATCH_MP_TAC le_epsilon >> rpt STRIP_TAC \\
     IMP_RES_TAC pow_half_ser_by_e \\
     Q.PAT_ASSUM `e = _` (ONCE_REWRITE_TAC o wrap) \\
  (* m (BIGUNION (IMAGE f univ(:num))) <= suminf (m o f) + suminf (\n. e * (1 / 2) pow (n + 1)) *)
     MATCH_MP_TAC le_trans \\
     Q.PAT_X_ASSUM `!a e. X ==> ?f. P`
        (STRIP_ASSUME_TAC o (Q.GEN `n`) o
         (Q.SPECL [`(f :num->'a->bool) n`, `e * (1 / 2) pow (n + 1)`])) \\
    `!n. 0 < e * (1 / 2) pow (n + 1)` by PROVE_TAC [lt_mul, pow_half_pos_lt] \\
    `!n. ?g. g IN C (f n) /\ suminf (mu o g) <= (m o f) n + e * (1 / 2) pow (n + 1)`
         by METIS_TAC [o_DEF] \\
     Q.PAT_X_ASSUM `!n. X => ?f'. Y` K_TAC (* cleanup *) \\
     POP_ASSUM (STRIP_ASSUME_TAC o (SIMP_RULE bool_ss [SKOLEM_THM])) \\ (* f' is a cover for each f *)
     Q.EXISTS_TAC `suminf (\n. suminf (mu o f' n))` \\
     ONCE_REWRITE_TAC [CONJ_COMM] \\
     STRONG_CONJ_TAC
     >- (Know `suminf (m o f) + suminf (\n. e * (1 / 2) pow (n + 1)) =
               suminf (\n. (m o f) n + (\n. e * (1 / 2) pow (n + 1)) n)`
         >- (MATCH_MP_TAC EQ_SYM \\
             MATCH_MP_TAC ext_suminf_add >> BETA_TAC \\
             GEN_TAC >> Reverse CONJ_TAC >- PROVE_TAC [le_mul, lt_le, pow_half_pos_le] \\
             METIS_TAC [o_DEF]) >> Rewr' \\
         MATCH_MP_TAC ext_suminf_mono >> BETA_TAC \\
         GEN_TAC >> Reverse CONJ_TAC >- METIS_TAC [] \\
         Suff `0 <= suminf (mu o f' n)`
         >- PROVE_TAC [lt_infty,extreal_of_num_def,extreal_not_infty,lte_trans] \\
         MATCH_MP_TAC ext_suminf_pos \\
         GEN_TAC >> REWRITE_TAC [o_DEF] >> BETA_TAC \\
         Suff `f' n n' IN sts` >- PROVE_TAC [positive_def, measurable_sets_def, measure_def] \\
        `f' n IN C (f n)` by METIS_TAC [] >> POP_ASSUM MP_TAC \\
         Q.ABBREV_TAC `g = f' n` \\
         Q.UNABBREV_TAC `C` >> BETA_TAC \\
         SIMP_TAC std_ss [GSPECIFICATION, IN_FUNSET, IN_UNIV]) \\
     Q.PAT_X_ASSUM `e = _` (REWRITE_TAC o wrap o (MATCH_MP EQ_SYM)) \\
     DISCH_TAC \\
     Know `suminf (\n. suminf (mu o f' n)) < PosInf`
     >- (MATCH_MP_TAC let_trans >> Q.EXISTS_TAC `suminf (m o f) + e` \\
         PROVE_TAC [lt_infty, add_not_infty]) >> DISCH_TAC \\
     `!n. f' n IN C (f n)` by METIS_TAC [] \\
     rename1 `!n. g n IN C (f n)` \\
     Q.PAT_X_ASSUM `!n. g n IN C (f n) /\ X` K_TAC \\ (* cleanup *)
  (* m (BIGUNION (IMAGE f univ(:num))) <= suminf (\n. suminf (mu o g n)) *)
     Know `!n. (g n) IN (univ(:num) -> sts) /\ (f n) SUBSET BIGUNION (IMAGE (g n) univ(:num))`
     >- (GEN_TAC >> POP_ASSUM (MP_TAC o (Q.SPEC `n`)) \\
         Q.UNABBREV_TAC `C` >> SET_SPEC_TAC []) >> DISCH_TAC \\
  (* `!n. m (f n) <= suminf (mu o g n)` by METIS_TAC [] \\ *)
     Know `BIGUNION (IMAGE f univ(:num)) SUBSET
           BIGUNION (IMAGE (\n. BIGUNION (IMAGE (g n) univ(:num))) univ(:num))`
     >- (RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE, IN_UNIV] \\
         rename1 `x IN f n` \\
         Q.EXISTS_TAC `BIGUNION (IMAGE (g n) univ(:num))` \\
         Reverse CONJ_TAC >- (Q.EXISTS_TAC `n` >> REWRITE_TAC []) \\
         PROVE_TAC [SUBSET_DEF]) >> DISCH_TAC \\
  (* merge two nesting BIGUNIONs into one BIGUNION *)
    `!i j. g i j IN sts` by PROVE_TAC [IN_FUNSET, IN_UNIV] \\
     Q.ABBREV_TAC `ff = \n. g (nfst n) (nsnd n)` \\
    `ff IN (univ(:num) -> sts)` by PROVE_TAC [IN_FUNSET, IN_UNIV] \\
     Know `BIGUNION (IMAGE (\n. BIGUNION (IMAGE (g n) univ(:num))) univ(:num)) =
           BIGUNION (IMAGE ff (univ(:num)))`
     >- (RW_TAC std_ss [GSYM SUBSET_SUBSET_EQ, SUBSET_DEF, IN_BIGUNION_IMAGE, IN_UNIV] >|
         [ (* goal 1 (of 2) *)
           Q.EXISTS_TAC `npair n x'` \\ (* numpairTheory is used here! *)
           Q.UNABBREV_TAC `ff` >> BETA_TAC >> PROVE_TAC [nfst_npair, nsnd_npair],
           (* goal 2 (of 2) *)
           Q.EXISTS_TAC `nfst x'` \\
           Q.EXISTS_TAC `nsnd x'` \\
           POP_ASSUM MP_TAC >> Q.UNABBREV_TAC `ff` >> BETA_TAC \\
           REWRITE_TAC [] ]) \\
     DISCH_TAC \\
     Q.PAT_X_ASSUM `BIGUNION (IMAGE f UNIV) SUBSET X` MP_TAC \\
     POP_ORW >> DISCH_TAC \\
     Suff `suminf (\n. suminf (mu o g n)) = suminf (mu o ff)`
     >- (DISCH_THEN (ONCE_REWRITE_TAC o wrap) \\
         FIRST_X_ASSUM MATCH_MP_TAC >> ASM_REWRITE_TAC []) \\
     Q.UNABBREV_TAC `ff` \\
  (* prepare for applying "ext_suminf_2d" *)
     MATCH_MP_TAC EQ_SYM \\
     Q.ABBREV_TAC `h = \n. (nfst n, nsnd n)` \\
     Q.ABBREV_TAC `ff = \m n. mu (g m n)` \\
     Know `(mu o (\n. g (nfst n) (nsnd n))) = UNCURRY ff o h`
     >- (SIMP_TAC std_ss [o_DEF, FUN_EQ_THM, UNCURRY] \\
         Q.UNABBREV_TAC `h` >> Q.UNABBREV_TAC `ff` \\
         ASM_SIMP_TAC std_ss []) >> Rewr \\
  (* finally, apply "ext_suminf_2d", cleaning up easy goals *)
     MATCH_MP_TAC ext_suminf_2d \\
     `!n. suminf (ff n) = (\n. suminf (mu o g n)) n` by METIS_TAC [o_DEF] \\
     POP_ASSUM ((ASM_SIMP_TAC std_ss) o wrap) \\
     Know `BIJ h univ(:num) (univ(:num) CROSS univ(:num))`
     >- (Q.UNABBREV_TAC `h` >> REWRITE_TAC [NUM_2D_BIJ_nfst_nsnd]) >> Rewr \\
  (* !m n. 0 <= ff m n *)
     Q.UNABBREV_TAC `ff` >> BETA_TAC \\
     PROVE_TAC [positive_def, measure_def, measurable_sets_def])
 (* Part II *)
 >> DISCH_TAC >> STRONG_CONJ_TAC
 >- (rpt STRIP_TAC >> fs [countable_covers_def, outer_measure_def] \\
     MATCH_MP_TAC inf_le_imp \\
     SIMP_TAC std_ss [GSPECIFICATION, Once (GSYM IN_APP)] \\
     Q.EXISTS_TAC `\n. if n = 0 then x else EMPTY` \\
     Know `mu o (\n :num. if n = 0 then x else EMPTY) = (\n. if n = 0 then mu x else 0)`
     >- (RW_TAC arith_ss [o_DEF, FUN_EQ_THM] \\
         Cases_on `n = 0` >- METIS_TAC [] \\
         PROVE_TAC [positive_def, measure_def]) >> Rewr' \\
    `0 <= mu x` by PROVE_TAC [positive_def, measure_def, measurable_sets_def] \\
     POP_ASSUM (fn th => REWRITE_TAC [MATCH_MP ext_suminf_sing th]) \\
     Q.UNABBREV_TAC `C` >> BETA_TAC \\
     SIMP_TAC std_ss [GSPECIFICATION] \\
     CONJ_TAC >- (SIMP_TAC std_ss [IN_FUNSET, IN_UNIV] \\
                  GEN_TAC >> Cases_on `n = 0` >- METIS_TAC [] \\
                  METIS_TAC [semiring_def, subsets_def]) \\
     SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_UNIV] \\
     rpt STRIP_TAC >> Q.EXISTS_TAC `0` >> METIS_TAC [])
 >> DISCH_TAC >> STRONG_CONJ_TAC
 (* Part III: measure_space (sp,A,m) *)
 >- (fs [countable_covers_def, outer_measure_def, caratheodory_sets_def] \\
     Q.PAT_ASSUM `m = _` (REWRITE_TAC o wrap o (MATCH_MP EQ_SYM)) \\ (* recover `m` *)
     REWRITE_TAC [measure_space_def, m_space_def, measurable_sets_def, measure_def] \\
    `increasing (sp,POW sp,m)` by PROVE_TAC [outer_measure_space_def] \\
    `subset_class sp sts` by PROVE_TAC [semiring_def, space_def, subsets_def] \\
    `positive (sp,POW sp,m)` by PROVE_TAC [outer_measure_space_def] \\
    `!s. s SUBSET sp ==> 0 <= m s`
        by PROVE_TAC [positive_def, measure_def, measurable_sets_def, IN_POW] \\
     Know `positive (sp,A,m)`
     >- (REWRITE_TAC [positive_def, measure_def, measurable_sets_def] \\
         CONJ_TAC >- PROVE_TAC [positive_def, measure_def] \\
         GEN_TAC >> Q.UNABBREV_TAC `A` >> SET_SPEC_TAC [] \\
         METIS_TAC []) >> DISCH_TAC \\
     ONCE_REWRITE_TAC [DECIDE ``A /\ B /\ C <=> B /\ (A /\ C)``] \\
     CONJ_TAC >- art [] \\
  (* Dynkin's lemma is used here *)
     REWRITE_TAC [GSYM DYNKIN_LEMMA, subsets_def] \\
     REWRITE_TAC [dynkin_system_def, space_def, subsets_def, GSYM CONJ_ASSOC] \\
     STRONG_CONJ_TAC
     >- (REWRITE_TAC [subset_class_def] \\
         GEN_TAC >> Q.UNABBREV_TAC `A` >> SET_SPEC_TAC []) >> DISCH_TAC \\
     MATCH_MP_TAC (prove (``!a b c. b /\ a /\ c ==> a /\ b /\ c``, PROVE_TAC [])) \\
     STRONG_CONJ_TAC
     >- (GEN_TAC >> Q.UNABBREV_TAC `A` >> SET_SPEC_TAC [] \\
         rpt STRIP_TAC >- (MATCH_MP_TAC SUBSET_DIFF_SUBSET >> REWRITE_TAC [SUBSET_REFL]) \\
        `q INTER (sp DIFF s) = q DIFF s` by ASM_SET_TAC [] >> POP_ORW \\
        `q DIFF (sp DIFF s) = q INTER s` by ASM_SET_TAC [] >> POP_ORW \\
         MATCH_MP_TAC add_comm >> DISJ1_TAC \\
         CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf \\
                      FIRST_X_ASSUM MATCH_MP_TAC >> ASM_SET_TAC []) \\
         MATCH_MP_TAC pos_not_neginf \\
         FIRST_X_ASSUM MATCH_MP_TAC >> ASM_SET_TAC []) >> DISCH_TAC \\
     Know `{} IN A`
     >- (Q.UNABBREV_TAC `A` >> SET_SPEC_TAC [] \\
         REWRITE_TAC [EMPTY_SUBSET, INTER_EMPTY, DIFF_EMPTY] >> rpt STRIP_TAC \\
        `m {} = 0` by PROVE_TAC [positive_def, measure_def, measurable_sets_def] \\
         POP_ORW >> REWRITE_TAC [add_lzero]) >> DISCH_TAC \\
     STRONG_CONJ_TAC >- METIS_TAC [DIFF_EMPTY] >> DISCH_TAC \\
     SIMP_TAC std_ss [IN_FUNSET, IN_UNIV] \\
    `subadditive (sp,POW sp,m)` by PROVE_TAC [OUTER_MEASURE_SPACE_SUBADDITIVE] \\
     Know `!a q. a IN A /\ q SUBSET sp ==> (m q = m (q INTER a) + m (q DIFF a))`
     >- (rpt GEN_TAC >> Q.UNABBREV_TAC `A` >> SET_SPEC_TAC [] \\
         rpt STRIP_TAC >> PROVE_TAC []) >> DISCH_TAC \\
  (* A is stable under union *)
     Know `!s t. s IN A /\ t IN A ==> s UNION t IN A`
     >- (rpt STRIP_TAC \\
         Suff `s UNION t IN {a | a SUBSET sp /\
                                 !q. q SUBSET sp ==> (m q = m (q INTER a) + m (q DIFF a))}`
         >- METIS_TAC [] \\
         SET_SPEC_TAC [] \\
         CONJ_TAC >- PROVE_TAC [UNION_SUBSET, subset_class_def] \\
         rpt STRIP_TAC >> rename1 `p SUBSET sp` \\
         REWRITE_TAC [GSYM le_antisym] \\
         CONJ_TAC >- (MATCH_MP_TAC (REWRITE_RULE [measure_def, measurable_sets_def]
                                                 (Q.SPEC `(sp,POW sp,m)` SUBADDITIVE)) \\
                      ASM_SET_TAC [IN_POW]) \\
        `p INTER (s UNION t) = p INTER (s UNION (t DIFF s))` by SET_TAC [] >> POP_ORW \\
         REWRITE_TAC [UNION_OVER_INTER] \\
         MATCH_MP_TAC le_trans \\
         Q.EXISTS_TAC `m (p INTER s) + m (p INTER (t DIFF s)) + m (p DIFF (s UNION t))` \\
         CONJ_TAC >- (MATCH_MP_TAC le_radd_imp \\
                      MATCH_MP_TAC (REWRITE_RULE [measure_def, measurable_sets_def]
                                                 (Q.SPEC `(sp,POW sp,m)` SUBADDITIVE)) \\
                      ASM_SET_TAC [IN_POW]) \\
        `p INTER (t DIFF s) = (p DIFF s) INTER t` by SET_TAC [] >> POP_ORW \\
        `p DIFF (s UNION t) = (p DIFF s) DIFF t`  by SET_TAC [] >> POP_ORW \\
         Know `m (p INTER s) + m ((p DIFF s) INTER t) + m (p DIFF s DIFF t) =
               m (p INTER s) + (m ((p DIFF s) INTER t) + m (p DIFF s DIFF t))`
         >- (MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC add_assoc \\
             DISJ1_TAC \\
             CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf >> FIRST_X_ASSUM MATCH_MP_TAC \\
                          ASM_SET_TAC []) \\
             CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf >> FIRST_X_ASSUM MATCH_MP_TAC \\
                          ASM_SET_TAC []) \\
             MATCH_MP_TAC pos_not_neginf \\
             FIRST_X_ASSUM MATCH_MP_TAC >> ASM_SET_TAC []) >> Rewr' \\
         Know `m ((p DIFF s) INTER t) + m (p DIFF s DIFF t) = m (p DIFF s)`
         >- (MATCH_MP_TAC EQ_SYM \\
             FIRST_X_ASSUM MATCH_MP_TAC >> art [] \\
             MATCH_MP_TAC SUBSET_DIFF_SUBSET >> art []) >> Rewr' \\
         Know `m (p INTER s) + m (p DIFF s) = m p`
         >- (MATCH_MP_TAC EQ_SYM >> FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> Rewr' \\
         REWRITE_TAC [le_refl]) >> DISCH_TAC \\
  (* A is stable under finite union *)
     Know `!f n. (!i. i < n ==> f i IN A) ==> BIGUNION (IMAGE f (count n)) IN A`
     >- (GEN_TAC >> Induct_on `n`
         >- ASM_SIMP_TAC arith_ss [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY] \\
         RW_TAC arith_ss [COUNT_SUC, IMAGE_INSERT, BIGUNION_INSERT]) >> DISCH_TAC \\
     Know `!q s t. q SUBSET sp /\ s IN A /\ t IN A /\ DISJOINT s t ==>
                  (m (q INTER (s UNION t)) = m (q INTER s) + m (q INTER t))`
     >- (rpt STRIP_TAC \\
        `q INTER s = (q INTER (s UNION t)) INTER s` by SET_TAC [] >> POP_ORW \\
        `q INTER t = (q INTER (s UNION t)) DIFF s`
                by ASM_SET_TAC [DISJOINT_DEF] >> POP_ORW \\
         FIRST_X_ASSUM MATCH_MP_TAC >> ASM_SET_TAC []) >> DISCH_TAC \\
     Know `!q f. q SUBSET sp ==>
                 !n. (!i. i < n ==> f i IN A) /\
                     (!i j. i < n /\ j < n /\ i <> j ==> DISJOINT (f i) (f j)) ==>
                     (m (q INTER (BIGUNION (IMAGE f (count n)))) =
                      SIGMA (\i. m (q INTER f i)) (count n))`
     >- (rpt GEN_TAC >> DISCH_TAC \\
         Induct_on `n` >- (SIMP_TAC arith_ss [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY,
                                              EXTREAL_SUM_IMAGE_EMPTY, INTER_EMPTY] \\
                           PROVE_TAC [positive_def, measure_def, measurable_sets_def]) \\
         SIMP_TAC arith_ss [COUNT_SUC, IMAGE_INSERT, BIGUNION_INSERT] \\
         STRIP_TAC \\
         Know `DISJOINT (f n) (BIGUNION (IMAGE f (count n)))`
         >- (REWRITE_TAC [DISJOINT_BIGUNION] \\
             RW_TAC std_ss [IN_IMAGE, IN_COUNT] \\
             FIRST_X_ASSUM MATCH_MP_TAC >> RW_TAC arith_ss []) >> DISCH_TAC \\
         Know `m (q INTER (f n UNION BIGUNION (IMAGE f (count n)))) =
               m (q INTER f n) + m (q INTER BIGUNION (IMAGE f (count n)))`
         >- (FIRST_X_ASSUM MATCH_MP_TAC >> art [] \\
             CONJ_TAC >- PROVE_TAC [LESS_SUC_REFL] \\
             FIRST_X_ASSUM MATCH_MP_TAC \\
             rpt STRIP_TAC >> PROVE_TAC [LESS_SUC]) >> Rewr' \\
         Know `SIGMA (\i. m (q INTER f i)) (n INSERT count n) =
               (\i. m (q INTER f i)) n + SIGMA (\i. m (q INTER f i)) (count n DELETE n)`
         >- (irule EXTREAL_SUM_IMAGE_PROPERTY \\
             REWRITE_TAC [FINITE_COUNT, IN_INSERT, IN_COUNT] \\
             DISJ1_TAC >> GEN_TAC >> DISCH_TAC >> BETA_TAC \\
             MATCH_MP_TAC pos_not_neginf \\
             FIRST_X_ASSUM MATCH_MP_TAC \\
             MATCH_MP_TAC SUBSET_INTER_SUBSET_L >> art []) >> Rewr' \\
        `count n DELETE n = count n` by REWRITE_TAC [COUNT_DELETE] >> POP_ORW \\
         BETA_TAC \\
      (* m (q INTER f n) + m (q INTER BIGUNION (IMAGE f (count n))) =
         m (q INTER f n) + SIGMA (\i. m (q INTER f i)) (count n) *)
         Cases_on `m (q INTER f n) = PosInf` >- fs [positive_def] \\
         Know `m (q INTER f n) <> NegInf /\ m (q INTER f n) <> PosInf`
         >- (POP_ASSUM (REWRITE_TAC o wrap) \\
             MATCH_MP_TAC pos_not_neginf \\
             FIRST_X_ASSUM MATCH_MP_TAC \\
             MATCH_MP_TAC SUBSET_INTER_SUBSET_L >> art []) \\
         DISCH_THEN (REWRITE_TAC o wrap o (MATCH_MP EXTREAL_EQ_LADD)) \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
         RW_TAC arith_ss []) >> DISCH_TAC \\
  (* now prove that A is stable under countably disjoint unions *)
     STRONG_CONJ_TAC
     >- (rpt STRIP_TAC \\ (* goal: BIGUNION (IMAGE f univ(:num)) IN A *)
         Know `!a. a IN A <=> (a SUBSET sp /\
                               !q. q SUBSET sp ==> (m q = m (q INTER a) + m (q DIFF a)))`
         >- (GEN_TAC >> Q.UNABBREV_TAC `A` >> SET_SPEC_TAC []) >> Rewr' \\
         STRONG_CONJ_TAC >- (RW_TAC std_ss [BIGUNION_SUBSET, IN_IMAGE, IN_UNIV] \\
                             PROVE_TAC [subset_class_def]) >> DISCH_TAC \\
         rpt STRIP_TAC >> REWRITE_TAC [GSYM le_antisym] \\
         CONJ_TAC >- (MATCH_MP_TAC (REWRITE_RULE [measure_def, measurable_sets_def, IN_POW]
                                                 (Q.SPEC `(sp,POW sp,m)` SUBADDITIVE)) \\
                      art [] >> ASM_SET_TAC []) \\
         REWRITE_TAC [BIGUNION_OVER_INTER_R] \\
         MATCH_MP_TAC le_trans \\
         Q.EXISTS_TAC `suminf (m o (\i. q INTER f i)) + m (q DIFF BIGUNION (IMAGE f univ(:num)))` \\
         CONJ_TAC >- (MATCH_MP_TAC le_radd_imp \\
                      MATCH_MP_TAC (REWRITE_RULE [measure_def, measurable_sets_def, IN_POW]
                                                 (Q.SPEC `(sp,POW sp,m)` COUNTABLY_SUBADDITIVE)) \\
                      REWRITE_TAC [] \\
                      CONJ_TAC >- PROVE_TAC [outer_measure_space_def] \\
                      SIMP_TAC std_ss [IN_FUNSET, IN_UNIV, IN_POW] \\
                      CONJ_TAC >- (GEN_TAC >> MATCH_MP_TAC SUBSET_INTER_SUBSET_L >> art []) \\
                      RW_TAC std_ss [BIGUNION_SUBSET, IN_IMAGE, IN_UNIV] \\
                      MATCH_MP_TAC SUBSET_INTER_SUBSET_L >> art []) \\
      (* preparing for applying le_sub_eq2 *)
         Cases_on `m q = PosInf` >- METIS_TAC [le_infty] \\
         Know `m q <> NegInf`
         >- (MATCH_MP_TAC pos_not_neginf \\
             FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> DISCH_TAC \\
         Know `suminf (m o (\i. q INTER f i)) <> NegInf`
         >- (MATCH_MP_TAC pos_not_neginf \\
             MATCH_MP_TAC ext_suminf_pos >> SIMP_TAC std_ss [o_DEF] \\
             GEN_TAC >> FIRST_X_ASSUM MATCH_MP_TAC \\
             MATCH_MP_TAC SUBSET_INTER_SUBSET_L >> art []) >> DISCH_TAC \\
         Know `m (q DIFF BIGUNION (IMAGE f univ(:num))) <> NegInf`
         >- (MATCH_MP_TAC pos_not_neginf \\
             FIRST_X_ASSUM MATCH_MP_TAC \\
             MATCH_MP_TAC SUBSET_DIFF_SUBSET >> art []) >> DISCH_TAC \\
         Know `(* z *) m q <> NegInf /\ m q <> PosInf /\
               (* x *) m (q DIFF BIGUNION (IMAGE f univ(:num))) <> NegInf /\
               (* y *) suminf (m o (\i. q INTER f i)) <> NegInf` >- art [] \\
         DISCH_THEN (REWRITE_TAC o wrap o (MATCH_MP EQ_SYM) o (MATCH_MP le_sub_eq2)) \\
      (* suminf (m o (\i. q INTER f i)) <= m q - m (q DIFF BIGUNION (IMAGE f univ(:num))) *)
         Know `!n. 0 <= (m o (\i. q INTER f i)) n`
         >- (GEN_TAC >> SIMP_TAC std_ss [o_DEF] \\
             FIRST_X_ASSUM MATCH_MP_TAC \\
             ASM_SET_TAC []) \\
         DISCH_THEN (MP_TAC o (MATCH_MP ext_suminf_alt_pos)) >> Rewr' \\
         REWRITE_TAC [sup_le'] >> GEN_TAC \\
         SIMP_TAC std_ss [IN_IMAGE, IN_UNIV, IN_COUNT] >> STRIP_TAC \\
         POP_ASSUM (ONCE_REWRITE_TAC o wrap) \\
      (* preparing for applying le_sub_eq2 again *)
         Know `SIGMA (m o (\i. q INTER f i)) (count n) <> NegInf`
         >- (MATCH_MP_TAC pos_not_neginf \\
             irule EXTREAL_SUM_IMAGE_POS \\
             SIMP_TAC std_ss [o_DEF, IN_COUNT, FINITE_COUNT] >> rpt STRIP_TAC \\
             FIRST_X_ASSUM MATCH_MP_TAC \\
             MATCH_MP_TAC SUBSET_INTER_SUBSET_L >> art []) >> DISCH_TAC \\
         Know `(* z *) m q <> NegInf /\ m q <> PosInf /\
               (* x *) m (q DIFF BIGUNION (IMAGE f univ(:num))) <> NegInf /\
               (* y *) SIGMA (m o (\i. q INTER f i)) (count n) <> NegInf` >- art [] \\
         DISCH_THEN (REWRITE_TAC o wrap o (MATCH_MP le_sub_eq2)) \\
         SIMP_TAC std_ss [o_DEF] \\
      (* SIGMA (\i. m (q INTER f i)) (count n) + m (q DIFF BIGUNION (IMAGE f univ(:num))) <= m q *)
         Know `SIGMA (\i. m (q INTER f i)) (count n) = m (q INTER BIGUNION (IMAGE f (count n)))`
         >- (MATCH_MP_TAC EQ_SYM >> FIRST_X_ASSUM irule >> PROVE_TAC []) >> Rewr' \\
         Know `m q = m (q INTER BIGUNION (IMAGE f (count n))) +
                     m (q DIFF BIGUNION (IMAGE f (count n)))`
         >- (FIRST_X_ASSUM MATCH_MP_TAC >> art [] \\
             FIRST_X_ASSUM MATCH_MP_TAC >> RW_TAC std_ss []) >> Rewr' \\
         MATCH_MP_TAC le_ladd_imp \\
         MATCH_MP_TAC (REWRITE_RULE [measure_def, measurable_sets_def, IN_POW]
                                    (Q.SPEC `(sp,POW sp,m)` INCREASING)) \\
         ASM_REWRITE_TAC [] \\
         MATCH_MP_TAC (prove (``!a b c. b /\ c /\ a ==> a /\ b /\ c``, PROVE_TAC [])) \\
         CONJ_TAC >- (MATCH_MP_TAC SUBSET_DIFF_SUBSET >> art []) \\
         CONJ_TAC >- (MATCH_MP_TAC SUBSET_DIFF_SUBSET >> art []) \\
      (* q DIFF BIGUNION (IMAGE f univ(:num)) SUBSET q DIFF BIGUNION (IMAGE f (count n)) *)
         MATCH_MP_TAC SUBSET_RESTRICT_DIFF \\
         RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_COUNT, IN_UNIV] \\
         Q.EXISTS_TAC `x'` >> art []) >> DISCH_TAC \\
  (* !s t. s IN A /\ t IN A ==> s INTER t IN A *)
     STRONG_CONJ_TAC
     >- (rpt STRIP_TAC \\
        `s INTER t = sp DIFF ((sp DIFF s) UNION (sp DIFF t))` by ASM_SET_TAC [] >> POP_ORW \\
         FIRST_ASSUM MATCH_MP_TAC \\ (* removed one (sp DIFF ...) *)
         FIRST_ASSUM MATCH_MP_TAC \\ (* removed one (... UNION ...) *)
         CONJ_TAC >- (FIRST_ASSUM MATCH_MP_TAC >> art []) \\
         FIRST_ASSUM MATCH_MP_TAC >> art []) >> DISCH_TAC \\
  (* countably_additive (sp,A,m) *)
     SIMP_TAC std_ss [countably_additive_def, measurable_sets_def, measure_def,
                      IN_FUNSET, IN_UNIV] \\
     rpt STRIP_TAC \\
     REWRITE_TAC [GSYM le_antisym] \\
     CONJ_TAC >- (MATCH_MP_TAC (REWRITE_RULE [measure_def, measurable_sets_def, IN_POW]
                                             (Q.SPEC `(sp,POW sp,m)` COUNTABLY_SUBADDITIVE)) \\
                  REWRITE_TAC [IN_FUNSET, IN_UNIV, IN_POW] \\
                  CONJ_TAC >- PROVE_TAC [outer_measure_space_def] \\
                  CONJ_TAC >- PROVE_TAC [subset_class_def] \\
                  RW_TAC std_ss [BIGUNION_SUBSET, IN_IMAGE, IN_UNIV] \\
                  PROVE_TAC [subset_class_def]) \\
     Know `!n. 0 <= (m o f) n`
     >- (GEN_TAC >> SIMP_TAC std_ss [o_DEF] \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
         FULL_SIMP_TAC std_ss [subset_class_def]) \\
     DISCH_THEN (MP_TAC o (MATCH_MP ext_suminf_alt_pos)) >> Rewr' \\
     REWRITE_TAC [sup_le'] >> GEN_TAC \\
     SIMP_TAC std_ss [IN_IMAGE, IN_UNIV, IN_COUNT] \\
     STRIP_TAC >> POP_ASSUM (ONCE_REWRITE_TAC o wrap) \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `m (BIGUNION (IMAGE f (count n)))` \\
     Reverse CONJ_TAC
     >- (MATCH_MP_TAC (REWRITE_RULE [measure_def, measurable_sets_def, IN_POW]
                                    (Q.SPEC `(sp,POW sp,m)` INCREASING)) \\
         CONJ_TAC >- art [] \\
         MATCH_MP_TAC (prove (``!a b c. b /\ c /\ a ==> a /\ b /\ c``, PROVE_TAC [])) \\
         CONJ_TAC >- (RW_TAC std_ss [BIGUNION_SUBSET, IN_IMAGE, IN_COUNT] \\
                      PROVE_TAC [subset_class_def]) \\
         CONJ_TAC >- (RW_TAC std_ss [BIGUNION_SUBSET, IN_IMAGE, IN_UNIV] \\
                      PROVE_TAC [subset_class_def]) \\
         RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_COUNT, IN_UNIV] \\
         Q.EXISTS_TAC `x'` >> art []) \\
    `BIGUNION (IMAGE f univ(:num)) SUBSET sp` by PROVE_TAC [subset_class_def] \\
     Q.PAT_X_ASSUM `!q f. q SUBSET sp ==> X`
        (fn th => MP_TAC (Q.SPECL [`f`, `n`]
                            (MATCH_MP th (ASSUME ``BIGUNION (IMAGE f univ(:num)) SUBSET sp``)))) \\
     Know `BIGUNION (IMAGE f univ(:num)) INTER BIGUNION (IMAGE f (count n)) =
           BIGUNION (IMAGE f (count n))`
     >- (MATCH_MP_TAC SUBSET_INTER2 \\
         RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_COUNT, IN_UNIV] \\
         Q.EXISTS_TAC `x'` >> art []) >> Rewr' \\
     Know `(\i. m (BIGUNION (IMAGE f univ(:num)) INTER f i)) = (m o f)`
     >- (REWRITE_TAC [o_DEF] >> FUN_EQ_TAC >> GEN_TAC >> BETA_TAC \\
         Suff `BIGUNION (IMAGE f univ(:num)) INTER f x = f x` >- PROVE_TAC [] \\
         MATCH_MP_TAC SUBSET_INTER2 \\
         MATCH_MP_TAC SUBSET_BIGUNION_I \\
         RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
         Q.EXISTS_TAC `x` >> REWRITE_TAC []) >> Rewr \\
     METIS_TAC [le_refl]) >> rpt STRIP_TAC
 >> fs [outer_measure_def]
 >> RW_TAC std_ss [le_inf', GSPECIFICATION]
 >> Know `!x. f x IN sts`
 >- (GEN_TAC \\
     Q.UNABBREV_TAC `C` >> fs [countable_covers_def, IN_FUNSET, IN_UNIV]) >> DISCH_TAC
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC `suminf (v o f)`
 >> Reverse CONJ_TAC
 >- (MATCH_MP_TAC ext_suminf_mono \\
     RW_TAC std_ss [o_DEF] \\
     MATCH_MP_TAC pos_not_neginf \\
    `positive (sp,POW sp,v)` by PROVE_TAC [outer_measure_space_def] \\
     METIS_TAC [positive_def, measurable_sets_def, measure_def, subset_class_def, IN_POW])
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC `v (BIGUNION (IMAGE f univ(:num)))`
 >> Reverse CONJ_TAC
 >- (`countably_subadditive (sp,POW sp,v)` by PROVE_TAC [outer_measure_space_def] \\
     MATCH_MP_TAC (REWRITE_RULE [measurable_sets_def, measure_def]
                                (Q.SPEC `(sp,POW sp,v)` COUNTABLY_SUBADDITIVE)) \\
     RW_TAC std_ss [IN_POW, IN_FUNSET, IN_UNIV, BIGUNION_SUBSET, IN_IMAGE] \\
     METIS_TAC [subset_class_def])
 >> Know `x SUBSET (BIGUNION (IMAGE f univ(:num)))`
 >- (Q.UNABBREV_TAC `C` >> fs [countable_covers_def, IN_FUNSET, IN_UNIV]) >> DISCH_TAC
 >> `increasing (sp,POW sp,v)` by PROVE_TAC [outer_measure_space_def]
 >> MATCH_MP_TAC (REWRITE_RULE [measurable_sets_def, measure_def]
                               (Q.SPEC `(sp,POW sp,v)` INCREASING))
 >> RW_TAC std_ss [IN_POW, BIGUNION_SUBSET, IN_IMAGE]
 >> METIS_TAC [subset_class_def]
QED

(* The "semiring" version of Caratheodory's Extension Theorem
   (Theorem 6.1 of [1, p.38-45])

   named after Constantin Caratheodory, a Greek mathematician who spent most
   of his professional career in Germany. [9]
 *)
Theorem CARATHEODORY_SEMIRING :
    !m0.
       semiring (m_space m0, measurable_sets m0) /\ premeasure m0 ==>
       ?m. (!s. s IN measurable_sets m0 ==> (measure m s = measure m0 s)) /\
           ((m_space m, measurable_sets m) =
            sigma (m_space m0) (measurable_sets m0)) /\ measure_space m
Proof
    PRINT_TAC "Beginning Caratheodory's extension theorem"
 >> rpt STRIP_TAC >> Cases_on `m0` >> Cases_on `r`
 >> fs [m_space_def, measurable_sets_def, measure_def, premeasure_def]
 >> rename1 `positive (sp,sts,mu)` (* m0 now disappeared *)
(******************************************************************************)
 >> PRINT_TAC "Step 1: m is an outer measure, which will eventually extend mu"
(******************************************************************************)
 >> Q.ABBREV_TAC `C = countable_covers sts`
 >> Q.ABBREV_TAC `m = outer_measure mu C`
 >> Q.ABBREV_TAC `A' = caratheodory_sets sp m`
 >> fs [countable_covers_def, outer_measure_def, caratheodory_sets_def]
 >> Know `outer_measure_space (sp, POW sp, m) /\ (!x. x IN sts ==> m x <= mu x) /\
          measure_space (sp,A',m)`
 >- (`subset_class sp sts /\ {} IN sts`
       by PROVE_TAC [semiring_def, space_def, subsets_def] \\
     METIS_TAC [OUTER_MEASURE_CONSTRUCTION,
                outer_measure_def, countable_covers_def, caratheodory_sets_def])
 >> STRIP_TAC
(******************************************************************************)
 >> PRINT_TAC "Step 2a. Extend the measure from semi-ring (mu) to ring (m')"
(******************************************************************************)
 >> Know `!x. x IN sts ==> (m x = mu x)`
 >- (rpt STRIP_TAC >> REWRITE_TAC [GSYM le_antisym] \\
     CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
  (* now `mu x <= m x`, S is the set of finite unions of disjoint sets from sts. *)
     Q.ABBREV_TAC `S = {BIGUNION c | c SUBSET sts /\ FINITE c /\ disjoint c}` \\
     Know `{} IN S`
     >- (Q.UNABBREV_TAC `S` >> RW_TAC std_ss [GSPECIFICATION] \\
         Q.EXISTS_TAC `EMPTY` \\
         REWRITE_TAC [BIGUNION_EMPTY, EMPTY_SUBSET, FINITE_EMPTY, disjoint_empty]) \\
     DISCH_TAC \\
     Know `sts SUBSET S`
     >- (RW_TAC std_ss [SUBSET_DEF] \\
         Q.UNABBREV_TAC `S` >> SIMP_TAC std_ss [GSPECIFICATION] \\
         Q.EXISTS_TAC `{x'}` \\
         REWRITE_TAC [BIGUNION_SING, FINITE_SING, disjoint_sing] \\
         ASM_SET_TAC []) >> DISCH_TAC \\
  (* S is stable under disjoint unions *)
     Know `!s t. s IN S /\ t IN S /\ DISJOINT s t ==> s UNION t IN S`
     >- (Q.UNABBREV_TAC `S` >> RW_TAC std_ss [GSPECIFICATION] \\
         Q.EXISTS_TAC `c UNION c'` >> REWRITE_TAC [BIGUNION_UNION] \\
         CONJ_TAC >- PROVE_TAC [UNION_SUBSET] \\
         CONJ_TAC >- PROVE_TAC [FINITE_UNION] \\
         MATCH_MP_TAC disjoint_union >> art [] \\
         METIS_TAC [DISJOINT_DEF]) >> DISCH_TAC \\
  (* S is stable under finite disjoint unions (not that easy!) *)
     Know `!c. c SUBSET S /\ FINITE c /\ disjoint c ==> BIGUNION c IN S`
     >- (Suff `!c. FINITE c ==> c SUBSET S /\ disjoint c ==> BIGUNION c IN S`
         >- METIS_TAC [] \\
         HO_MATCH_MP_TAC FINITE_INDUCT \\
         CONJ_TAC >- (RW_TAC std_ss [] >> ASM_REWRITE_TAC [BIGUNION_EMPTY]) \\
         rpt STRIP_TAC \\
      (* BIGUNION (e INSERT c) IN S *)
         REWRITE_TAC [BIGUNION_INSERT] \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
         CONJ_TAC >- PROVE_TAC [INSERT_SUBSET] \\
         CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC \\
                      CONJ_TAC >- PROVE_TAC [INSERT_SUBSET] \\
                      PROVE_TAC [disjoint_insert_imp]) \\
      (* DISJOINT e (BIGUNION c) *)
        `?f n. (!x. x < n  ==> f x IN c) /\ (c = IMAGE f (count n))`
             by PROVE_TAC [finite_decomposition] \\
         ASM_REWRITE_TAC [DISJOINT_DEF] \\
         REWRITE_TAC [BIGUNION_IMAGE_OVER_INTER_R] \\
         REWRITE_TAC [BIGUNION_EQ_EMPTY] \\
         Cases_on `n = 0` >- (DISJ1_TAC >> PROVE_TAC [COUNT_ZERO, IMAGE_EMPTY]) \\
         DISJ2_TAC >> REWRITE_TAC [EXTENSION] \\
         GEN_TAC >> EQ_TAC >| (* 2 subgoals *)
         [ (* goal (1 of 2) *)
           RW_TAC std_ss [IN_IMAGE, IN_COUNT, IN_SING] \\
           METIS_TAC [disjoint_insert_notin, DISJOINT_DEF],
           (* goal (2 of 2) *)
           RW_TAC std_ss [IN_IMAGE, IN_COUNT, IN_SING] \\
           Q.EXISTS_TAC `0` >> RW_TAC arith_ss [] \\
          `f 0 IN IMAGE f (count n)` by (FIRST_X_ASSUM MATCH_MP_TAC >> RW_TAC arith_ss []) \\
           METIS_TAC [disjoint_insert_notin, DISJOINT_DEF] ]) >> DISCH_TAC \\
  (* S is stable under finite intersection *)
     Know `!s t. s IN S /\ t IN S ==> s INTER t IN S`
     >- (rpt STRIP_TAC \\
         Know `?A. A SUBSET sts /\ FINITE A /\ disjoint A /\ (s = BIGUNION A)`
         >- (Q.PAT_X_ASSUM `s IN S` MP_TAC \\
             Q.UNABBREV_TAC `S` >> RW_TAC std_ss [GSPECIFICATION] \\
             Q.EXISTS_TAC `c` >> art []) >> STRIP_TAC \\
         Know `?B. B SUBSET sts /\ FINITE B /\ disjoint B /\ (t = BIGUNION B)`
         >- (Q.PAT_X_ASSUM `t IN S` MP_TAC \\
             Q.UNABBREV_TAC `S` >> RW_TAC std_ss [GSPECIFICATION] \\
             Q.EXISTS_TAC `c` >> art []) >> STRIP_TAC \\
         ASM_REWRITE_TAC [] \\
         Q.PAT_X_ASSUM `FINITE A` (STRIP_ASSUME_TAC o (MATCH_MP finite_decomposition)) \\
         Q.PAT_X_ASSUM `FINITE B` (STRIP_ASSUME_TAC o (MATCH_MP finite_decomposition)) \\
         ASM_REWRITE_TAC [BIGUNION_IMAGE_OVER_INTER_L] \\
         REWRITE_TAC [BIGUNION_IMAGE_OVER_INTER_R] \\
         FIRST_ASSUM MATCH_MP_TAC \\
         Reverse CONJ_TAC (* some easy goals *)
         >- (CONJ_TAC >- (MATCH_MP_TAC IMAGE_FINITE >> REWRITE_TAC [FINITE_COUNT]) \\
             MATCH_MP_TAC disjointI \\
             NTAC 2 GEN_TAC >> SIMP_TAC std_ss [IN_IMAGE, IN_COUNT] \\
             rpt STRIP_TAC \\
             Cases_on `i = i'` >- (`a = b` by METIS_TAC []) \\
             ASM_REWRITE_TAC [DISJOINT_ALT] \\
             GEN_TAC >> SIMP_TAC std_ss [IN_BIGUNION_IMAGE, IN_COUNT, IN_INTER] \\
             rpt STRIP_TAC \\
             DISJ2_TAC >> DISJ1_TAC >> CCONTR_TAC >> fs [] \\
            `x' IN f i INTER f i'` by METIS_TAC [IN_INTER] \\
            `~DISJOINT (f i) (f i')` by ASM_SET_TAC [DISJOINT_DEF] \\
             Q.PAT_X_ASSUM `disjoint (IMAGE f (count n))` MP_TAC \\
             RW_TAC std_ss [disjoint_def, IN_IMAGE, IN_COUNT] \\
             Q.EXISTS_TAC `f i` >> Q.EXISTS_TAC `f i'` >> art [] \\
             METIS_TAC []) \\
      (* IMAGE (\i. BIGUNION (IMAGE (\i'. f i INTER f' i') (count n'))) (count n) SUBSET S *)
         RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT] \\
         FIRST_ASSUM MATCH_MP_TAC \\
         Reverse CONJ_TAC (* some easy goals *)
         >- (CONJ_TAC >- (MATCH_MP_TAC IMAGE_FINITE >> REWRITE_TAC [FINITE_COUNT]) \\
             MATCH_MP_TAC disjointI \\
             NTAC 2 GEN_TAC >> SIMP_TAC std_ss [IN_IMAGE, IN_COUNT] \\
             rpt STRIP_TAC \\
             Cases_on `i' = i''` >- (`a = b` by METIS_TAC []) \\
             ASM_REWRITE_TAC [DISJOINT_ALT] \\
             RW_TAC std_ss [IN_INTER] \\
             CCONTR_TAC >> fs [] \\
            `x' IN f' i' INTER f' i''` by PROVE_TAC [IN_INTER] \\
            `~DISJOINT (f' i') (f' i'')` by ASM_SET_TAC [DISJOINT_DEF] \\
             Q.PAT_X_ASSUM `disjoint (IMAGE f' (count n'))` MP_TAC \\
             RW_TAC std_ss [disjoint_def, IN_IMAGE, IN_COUNT] \\
             Q.EXISTS_TAC `f' i'` >> Q.EXISTS_TAC `f' i''` >> art [] \\
             METIS_TAC []) \\
         RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT] \\
      (* f i INTER f' i' IN S *)
         Know `(IMAGE f (count n)) SUBSET sts`
         >- (Q.PAT_X_ASSUM `BIGUNION (IMAGE f (count n)) IN S` MP_TAC \\
             Q.UNABBREV_TAC `S` >> SIMP_TAC std_ss [GSPECIFICATION] >> METIS_TAC []) \\
         DISCH_TAC \\
         Know `(IMAGE f' (count n')) SUBSET sts`
         >- (Q.PAT_X_ASSUM `BIGUNION (IMAGE f' (count n')) IN S` MP_TAC \\
             Q.UNABBREV_TAC `S` >> SIMP_TAC std_ss [GSPECIFICATION] >> METIS_TAC []) \\
         DISCH_TAC \\
        `f i IN sts /\ f' i' IN sts` by PROVE_TAC [SUBSET_DEF, IN_IMAGE, IN_COUNT] \\
         fs [semiring_def, space_def, subsets_def] \\
        `f i INTER f' i' IN sts` by PROVE_TAC [] \\
         METIS_TAC [SUBSET_DEF]) >> DISCH_TAC \\
  (* S is stable under (more) finite intersection *)
     Know `!f n. 0 < n ==> (!i. i < n ==> f i IN S) ==> BIGINTER (IMAGE f (count n)) IN S`
     >- (GEN_TAC >> Induct_on `n` >- RW_TAC arith_ss [] \\
         RW_TAC arith_ss [] \\
         Cases_on `n = 0` >- fs [COUNT_SUC, COUNT_ZERO, IMAGE_INSERT, IMAGE_EMPTY,
                                 BIGINTER_INSERT] \\
        `0 < n` by RW_TAC arith_ss [] \\
         REWRITE_TAC [COUNT_SUC, IMAGE_INSERT, BIGINTER_INSERT] \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
         STRONG_CONJ_TAC
         >- (Q.PAT_X_ASSUM `!i. i < SUC n ==> f i IN S` (MP_TAC o (Q.SPEC `n`)) \\
             RW_TAC arith_ss []) >> DISCH_TAC \\
         FIRST_X_ASSUM irule >> art [] \\
         rpt STRIP_TAC >> FIRST_X_ASSUM MATCH_MP_TAC \\
         RW_TAC arith_ss []) >> DISCH_TAC \\
  (* DIFF of sts is in S *)
     Know `!s t. s IN sts /\ t IN sts ==> s DIFF t IN S`
     >- (rpt STRIP_TAC \\
         fs [semiring_def, subset_class_def, space_def, subsets_def] \\
        `?c. c SUBSET sts /\ FINITE c /\ disjoint c /\ (s DIFF t = BIGUNION c)` by PROVE_TAC [] \\
         Q.UNABBREV_TAC `S` >> SIMP_TAC std_ss [GSPECIFICATION] \\
         Q.EXISTS_TAC `c` >> art []) >> DISCH_TAC \\
  (* S is stable under diff *)
     Know `!s t. s IN S /\ t IN S ==> s DIFF t IN S`
     >- (rpt STRIP_TAC \\
      (* assert two finite disjoint sets from s and t *)
         Know `?A. A SUBSET sts /\ FINITE A /\ disjoint A /\ (s = BIGUNION A)`
         >- (Q.PAT_X_ASSUM `s IN S` MP_TAC \\
             Q.UNABBREV_TAC `S` >> RW_TAC std_ss [GSPECIFICATION] \\
             Q.EXISTS_TAC `c` >> art []) >> STRIP_TAC \\
         Know `?B. B SUBSET sts /\ FINITE B /\ disjoint B /\ (t = BIGUNION B)`
         >- (Q.PAT_X_ASSUM `t IN S` MP_TAC \\
             Q.UNABBREV_TAC `S` >> RW_TAC std_ss [GSPECIFICATION] \\
             Q.EXISTS_TAC `c` >> art []) >> STRIP_TAC \\
         ASM_REWRITE_TAC [] \\
      (* decomposite the two sets into two sequences of sets *)
         STRIP_ASSUME_TAC (MATCH_MP finite_disjoint_decomposition
                                    (CONJ (ASSUME ``FINITE (A :'a set set)``)
                                          (ASSUME ``disjoint (A :'a set set)``))) \\
         STRIP_ASSUME_TAC (MATCH_MP finite_disjoint_decomposition
                                    (CONJ (ASSUME ``FINITE (B :'a set set)``)
                                          (ASSUME ``disjoint (B :'a set set)``))) \\
         ASM_REWRITE_TAC [] \\
         Know `BIGUNION (IMAGE f (count n)) SUBSET sp`
         >- (RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_COUNT] \\
             Suff `f x'' SUBSET sp` >- PROVE_TAC [SUBSET_DEF] \\
             fs [semiring_def, subset_class_def, space_def, subsets_def] \\
            `f x'' IN sts` by PROVE_TAC [SUBSET_DEF, IN_IMAGE, IN_COUNT] \\
             METIS_TAC []) >> DISCH_TAC \\
         Know `BIGUNION (IMAGE f' (count n')) SUBSET sp`
         >- (RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_COUNT] \\
             Suff `f' x'' SUBSET sp` >- PROVE_TAC [SUBSET_DEF] \\
             fs [semiring_def, subset_class_def, space_def, subsets_def] \\
            `f' x'' IN sts` by PROVE_TAC [SUBSET_DEF, IN_IMAGE, IN_COUNT] \\
             METIS_TAC []) >> DISCH_TAC \\
         Cases_on `n = 0` (* TODO: optimize the METIS_TAC *)
         >- (METIS_TAC [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY, EMPTY_DIFF]) \\
         Cases_on `n' = 0`
         >- (ASM_REWRITE_TAC [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY, DIFF_EMPTY] \\
             METIS_TAC []) \\
        `0 < n /\ 0 < n'` by RW_TAC arith_ss [] \\
         REWRITE_TAC [MATCH_MP GEN_DIFF_INTER
                               (CONJ (ASSUME ``BIGUNION (IMAGE f (count n)) SUBSET sp``)
                                     (ASSUME ``BIGUNION (IMAGE f' (count n')) SUBSET sp``))] \\
         REWRITE_TAC [MATCH_MP GEN_COMPL_FINITE_UNION (ASSUME ``0:num < n'``)] \\
         REWRITE_TAC [BIGUNION_IMAGE_OVER_INTER_L] \\
         REWRITE_TAC [MATCH_MP BIGINTER_IMAGE_OVER_INTER_R (ASSUME ``0:num < n'``)] \\
         BETA_TAC >> FIRST_ASSUM MATCH_MP_TAC \\
         Reverse CONJ_TAC (* some easy goals *)
         >- (CONJ_TAC >- (MATCH_MP_TAC IMAGE_FINITE >> REWRITE_TAC [FINITE_COUNT]) \\
             MATCH_MP_TAC disjointI \\
             NTAC 2 GEN_TAC >> SIMP_TAC std_ss [IN_IMAGE, IN_COUNT] \\
             rpt STRIP_TAC \\
             Cases_on `i = i'` >- (`a = b` by METIS_TAC []) \\
             ASM_REWRITE_TAC [DISJOINT_ALT] \\
             GEN_TAC >> SIMP_TAC std_ss [IN_BIGINTER_IMAGE, IN_COUNT] \\
             rpt STRIP_TAC \\
             POP_ASSUM (STRIP_ASSUME_TAC o (fn th => MATCH_MP th (ASSUME ``0:num < n'``))) \\
             Q.EXISTS_TAC `0` >> art [] \\
             SIMP_TAC std_ss [IN_INTER] \\
             DISJ1_TAC >> CCONTR_TAC \\
             fs [IN_INTER] \\
            `x' IN f i INTER f i'` by PROVE_TAC [IN_INTER] \\
             ASM_SET_TAC [DISJOINT_DEF]) \\ (* TODO: optimize this last step *)
         RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT] \\
      (* BIGINTER (IMAGE (\i'. f i INTER (sp DIFF f' i')) (count n')) IN S *)
         FIRST_X_ASSUM irule >> art [] \\
         rpt STRIP_TAC >> BETA_TAC \\
        `f i IN sts /\ f' i' IN sts` by PROVE_TAC [SUBSET_DEF, IN_IMAGE, IN_COUNT] \\
         Know `f i INTER (sp DIFF f' i') = f i DIFF f' i'`
         >- (MATCH_MP_TAC EQ_SYM \\
             MATCH_MP_TAC GEN_DIFF_INTER \\
             fs [semiring_def, subset_class_def, space_def, subsets_def]) \\
         Rewr >> FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> DISCH_TAC \\
  (* S is stable under finite union (but is still NOT an algebra) *)
     Know `!s t. s IN S /\ t IN S ==> s UNION t IN S`
     >- (rpt STRIP_TAC \\
         STRIP_ASSUME_TAC (Q.SPECL [`s`, `t`] UNION_TO_3_DISJOINT_UNIONS) >> art [] \\
         FIRST_ASSUM MATCH_MP_TAC \\
         CONJ_TAC >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           FIRST_ASSUM MATCH_MP_TAC \\
           CONJ_TAC >- PROVE_TAC [] \\
           CONJ_TAC >- PROVE_TAC [] \\
           ASM_SET_TAC [disjoint_def, DISJOINT_DEF],
           (* goal 2 (of 2) *)
           CONJ_TAC >- PROVE_TAC [] \\
           ASM_SET_TAC [disjoint_def, DISJOINT_DEF] ]) >> DISCH_TAC \\
  (* S is a ring (but is NOT an algebra or sigma-algebra) since sp NOTIN S *)
     Know `ring (sp,S)`
     >- (RW_TAC std_ss [ring_def, subset_class_def, space_def, subsets_def] \\
         POP_ASSUM MP_TAC >> Q.UNABBREV_TAC `S` \\
         RW_TAC std_ss [GSPECIFICATION] \\
         RW_TAC std_ss [BIGUNION_SUBSET] \\
        `Y IN sts` by METIS_TAC [SUBSET_DEF] \\
         METIS_TAC [semiring_def, subset_class_def, space_def, subsets_def]) \\
     DISCH_TAC \\
  (* clean up duplicated assumptions (use ``ring (sp,S)`` from now on) *)
     Q.PAT_X_ASSUM `{} IN S`                                      K_TAC \\
     Q.PAT_X_ASSUM `!s t. s IN S /\ t IN S ==> s INTER t IN S`    K_TAC \\
     Q.PAT_X_ASSUM `!s t. s IN S /\ t IN S ==> s DIFF t IN S`     K_TAC \\
     Q.PAT_X_ASSUM `!s t. s IN sts /\ t IN sts ==> s DIFF t IN S` K_TAC \\
     Q.PAT_X_ASSUM `!s t. s IN S /\ t IN S /\ DISJOINT s t ==>
                          s UNION t IN S`                         K_TAC \\
     Q.PAT_X_ASSUM `!s t. s IN S /\ t IN S ==> s UNION t IN S`    K_TAC \\
     Q.PAT_X_ASSUM `!c. c SUBSET S /\ FINITE c /\ disjoint c ==>
                        BIGUNION c IN S`                          K_TAC \\
     Q.PAT_X_ASSUM `!f n. 0 < n ==> X`                            K_TAC \\
  (****************************************************************************)
     PRINT_TAC "Step 2b. Claim: m extends mu, i.e. m(x) = mu(x), !x IN sts" \\
  (****************************************************************************)
  (* M is a set of "measure" on S extended from mu *)
     Q.ABBREV_TAC `M = \a. {r | ?c. c SUBSET sts /\ FINITE c /\ disjoint c /\
                                    (a = BIGUNION c) /\ (r = SIGMA mu c)}` \\
    `finite_additive (sp,sts,mu)`
        by PROVE_TAC [SEMIRING_PREMEASURE_FINITE_ADDITIVE, premeasure_def,
                      m_space_def, measurable_sets_def] \\
     Know `!a s t. s IN (M a) /\ t IN (M a) ==> (s = t)`
     >- (rpt GEN_TAC >> Q.UNABBREV_TAC `M` >> RW_TAC std_ss [GSPECIFICATION] \\
         STRIP_ASSUME_TAC (MATCH_MP finite_disjoint_decomposition
                                    (CONJ (ASSUME ``FINITE (c :'a set set)``)
                                          (ASSUME ``disjoint (c :'a set set)``))) \\
         STRIP_ASSUME_TAC (MATCH_MP finite_disjoint_decomposition
                                    (CONJ (ASSUME ``FINITE (c' :'a set set)``)
                                          (ASSUME ``disjoint (c' :'a set set)``))) \\
         Q.PAT_X_ASSUM `BIGUNION c' = BIGUNION c` MP_TAC >> art [] \\
         DISCH_TAC \\
         Know `!i. i < n ==> (f i = f i INTER BIGUNION (IMAGE f' (count n')))`
         >- (POP_ORW >> rpt STRIP_TAC \\
             MATCH_MP_TAC EQ_SYM >> REWRITE_TAC [INTER_SUBSET_EQN] \\
             MATCH_MP_TAC SUBSET_BIGUNION_I \\
             PROVE_TAC [IN_IMAGE, IN_COUNT]) >> DISCH_TAC \\
         Know `IMAGE f (count n) =
               IMAGE (\i. f i INTER BIGUNION (IMAGE f' (count n'))) (count n)`
         >- (MATCH_MP_TAC SUBSET_ANTISYM \\
             SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT] \\
             rpt STRIP_TAC >- (Q.EXISTS_TAC `x''` >> METIS_TAC []) \\
             Q.EXISTS_TAC `i` >> METIS_TAC []) >> Rewr \\
         Know `!i. i < n' ==> (f' i = f' i INTER BIGUNION (IMAGE f (count n)))`
         >- (Q.PAT_X_ASSUM `BIGUNION (IMAGE f' (count n')) = BIGUNION (IMAGE f (count n))`
                (ONCE_REWRITE_TAC o wrap o (MATCH_MP EQ_SYM)) >> rpt STRIP_TAC \\
             MATCH_MP_TAC EQ_SYM >> REWRITE_TAC [INTER_SUBSET_EQN] \\
             MATCH_MP_TAC SUBSET_BIGUNION_I \\
             PROVE_TAC [IN_IMAGE, IN_COUNT]) >> DISCH_TAC \\
         Know `IMAGE f' (count n') =
               IMAGE (\i. f' i INTER BIGUNION (IMAGE f (count n))) (count n')`
         >- (MATCH_MP_TAC SUBSET_ANTISYM \\
             SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT] \\
             rpt STRIP_TAC >- (Q.EXISTS_TAC `x''` >> METIS_TAC []) \\
             Q.EXISTS_TAC `i` >> METIS_TAC []) \\
         DISCH_THEN
           ((GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites) o wrap) \\
         Know `SIGMA mu (IMAGE (\i. f i INTER BIGUNION (IMAGE f' (count n'))) (count n)) =
               SIGMA (mu o (\i. f i INTER BIGUNION (IMAGE f' (count n')))) (count n)`
         >- (irule EXTREAL_SUM_IMAGE_IMAGE \\
             REWRITE_TAC [FINITE_COUNT] >> CONJ_TAC
             >- (DISJ1_TAC >> GEN_TAC >> RW_TAC std_ss [IN_IMAGE, IN_COUNT] \\
                 Suff `0 <= mu (f i)` >- METIS_TAC [le_not_infty] \\
                 METIS_TAC [SUBSET_DEF, positive_def, measure_def, measurable_sets_def]) \\
             MATCH_MP_TAC INJ_IMAGE \\
             Q.EXISTS_TAC `c` >> REWRITE_TAC [INJ_DEF, IN_COUNT] >> BETA_TAC \\
             METIS_TAC []) >> Rewr' \\
         Know `SIGMA mu (IMAGE (\i. f' i INTER BIGUNION (IMAGE f (count n))) (count n')) =
               SIGMA (mu o (\i. f' i INTER BIGUNION (IMAGE f (count n)))) (count n')`
         >- (irule EXTREAL_SUM_IMAGE_IMAGE \\
             REWRITE_TAC [FINITE_COUNT] >> CONJ_TAC
             >- (DISJ1_TAC >> GEN_TAC >> RW_TAC std_ss [IN_IMAGE, IN_COUNT] \\
                 Suff `0 <= mu (f' i)` >- METIS_TAC [le_not_infty] \\
                 METIS_TAC [SUBSET_DEF, positive_def, measure_def, measurable_sets_def]) \\
             MATCH_MP_TAC INJ_IMAGE \\
             Q.EXISTS_TAC `c'` >> REWRITE_TAC [INJ_DEF, IN_COUNT] >> BETA_TAC \\
             METIS_TAC []) >> Rewr' \\
         SIMP_TAC std_ss [BIGUNION_IMAGE_OVER_INTER_R, o_DEF] \\
      (* applying FINITE_ADDITIVE and EXTREAL_SUM_IMAGE_EQ *)
         Know `SIGMA (\i. mu (BIGUNION (IMAGE (\i'. f i INTER f' i') (count n')))) (count n) =
               SIGMA (\i. SIGMA (mu o (\i'. f i INTER f' i')) (count n')) (count n)`
         >- (irule EXTREAL_SUM_IMAGE_EQ \\
             SIMP_TAC std_ss [o_DEF, FINITE_COUNT, IN_COUNT] \\
             MATCH_MP_TAC (prove (``!a b c. b /\ a ==> a /\ (b \/ c)``, PROVE_TAC [])) \\
             STRONG_CONJ_TAC
             >- (GEN_TAC >> DISCH_TAC >> CONJ_TAC
              (* mu (BIGUNION (IMAGE (\i'. f x' INTER f' i') (count n'))) <> NegInf *)
                 >- (MATCH_MP_TAC pos_not_neginf \\
                     fs [positive_def, measure_def, measurable_sets_def] \\
                     Q.PAT_ASSUM `!s. s IN sts ==> 0 <= mu s` MATCH_MP_TAC \\
                     REWRITE_TAC [GSYM BIGUNION_IMAGE_OVER_INTER_R] \\
                    `f x' INTER BIGUNION (IMAGE f' (count n')) = f x'` by PROVE_TAC [] \\
                     POP_ORW >> METIS_TAC [SUBSET_DEF, IN_IMAGE, IN_COUNT]) \\
              (* SIGMA (\i'. mu (f x' INTER f' i')) (count n') <> NegInf *)
                 MATCH_MP_TAC pos_not_neginf \\
                 irule EXTREAL_SUM_IMAGE_POS >> RW_TAC std_ss [IN_COUNT, FINITE_COUNT] \\
                 fs [positive_def, measure_def, measurable_sets_def] \\
                 Q.PAT_ASSUM `!s. s IN sts ==> 0 <= mu s` MATCH_MP_TAC \\
                 MATCH_MP_TAC
                   (REWRITE_RULE [subsets_def] (Q.SPEC `(sp,sts)` SEMIRING_INTER)) \\
                 PROVE_TAC [SUBSET_DEF, IN_COUNT, IN_IMAGE]) \\
             rpt STRIP_TAC \\
          (* applying FINITE_ADDITIVE on (sp,sts,mu) *)
             Suff `SIGMA (mu o (\i'. f x' INTER f' i')) (count n') =
                   mu (BIGUNION (IMAGE (\i'. f x' INTER f' i') (count n')))` >- METIS_TAC [o_DEF] \\
             MATCH_MP_TAC (REWRITE_RULE [measure_def, measurable_sets_def]
                                        (Q.SPEC `(sp,sts,mu)` FINITE_ADDITIVE)) \\
             ASM_SIMP_TAC std_ss [] \\
             CONJ_TAC >- (rpt STRIP_TAC \\
                          MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                                     (Q.SPEC `(sp,sts)` SEMIRING_INTER)) \\
                          PROVE_TAC [SUBSET_DEF, IN_COUNT, IN_IMAGE]) \\
             CONJ_TAC >- (rpt STRIP_TAC \\
                          MATCH_MP_TAC DISJOINT_RESTRICT_R >> PROVE_TAC []) \\
          (* `BIGUNION (IMAGE (\i'. f x' INTER f' i') (count n')) IN sts` *)
             REWRITE_TAC [GSYM BIGUNION_IMAGE_OVER_INTER_R] \\
            `f x' INTER BIGUNION (IMAGE f' (count n')) = f x'` by PROVE_TAC [] \\
             POP_ORW >> METIS_TAC [SUBSET_DEF, IN_IMAGE, IN_COUNT]) >> Rewr' \\
      (* symmetric with previous known *)
         Know `SIGMA (\i. mu (BIGUNION (IMAGE (\i'. f' i INTER f i') (count n)))) (count n') =
               SIGMA (\i. SIGMA (mu o (\i'. f' i INTER f i')) (count n)) (count n')`
         >- (irule EXTREAL_SUM_IMAGE_EQ \\
             SIMP_TAC std_ss [o_DEF, FINITE_COUNT, IN_COUNT] \\
             MATCH_MP_TAC (prove (``!a b c. b /\ a ==> a /\ (b \/ c)``, PROVE_TAC [])) \\
             STRONG_CONJ_TAC
             >- (GEN_TAC >> DISCH_TAC >> CONJ_TAC
              (* mu (BIGUNION (IMAGE (\i'. f' x' INTER f i') (count n))) <> NegInf *)
                 >- (MATCH_MP_TAC pos_not_neginf \\
                     fs [positive_def, measure_def, measurable_sets_def] \\
                     Q.PAT_ASSUM `!s. s IN sts ==> 0 <= mu s` MATCH_MP_TAC \\
                  (* BIGUNION (IMAGE (\i'. f' x' INTER f i') (count n)) IN sts *)
                     REWRITE_TAC [GSYM BIGUNION_IMAGE_OVER_INTER_R] \\
                    `f' x' INTER BIGUNION (IMAGE f (count n)) = f' x'` by PROVE_TAC [] \\
                     POP_ORW >> METIS_TAC [SUBSET_DEF, IN_IMAGE, IN_COUNT]) \\
              (* SIGMA (\i'. mu (f' x' INTER f i')) (count n) <> NegInf *)
                 MATCH_MP_TAC pos_not_neginf \\
                 irule EXTREAL_SUM_IMAGE_POS >> RW_TAC std_ss [IN_COUNT, FINITE_COUNT] \\
                 fs [positive_def, measure_def, measurable_sets_def] \\
                 Q.PAT_ASSUM `!s. s IN sts ==> 0 <= mu s` MATCH_MP_TAC \\
                 MATCH_MP_TAC
                   (REWRITE_RULE [subsets_def] (Q.SPEC `(sp,sts)` SEMIRING_INTER)) \\
                 PROVE_TAC [SUBSET_DEF, IN_COUNT, IN_IMAGE]) \\
             rpt STRIP_TAC \\
          (* applying FINITE_ADDITIVE on (sp,sts,mu) *)
             Suff `SIGMA (mu o (\i'. f' x' INTER f i')) (count n) =
                   mu (BIGUNION (IMAGE (\i'. f' x' INTER f i') (count n)))` >- METIS_TAC [o_DEF] \\
             MATCH_MP_TAC (REWRITE_RULE [measure_def, measurable_sets_def]
                                        (Q.SPEC `(sp,sts,mu)` FINITE_ADDITIVE)) \\
             ASM_SIMP_TAC std_ss [] \\
             CONJ_TAC >- (rpt STRIP_TAC \\
                          MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                                     (Q.SPEC `(sp,sts)` SEMIRING_INTER)) \\
                          PROVE_TAC [SUBSET_DEF, IN_COUNT, IN_IMAGE]) \\
             CONJ_TAC >- (rpt STRIP_TAC \\
                          MATCH_MP_TAC DISJOINT_RESTRICT_R >> PROVE_TAC []) \\
          (* `BIGUNION (IMAGE (\i'. f' x' INTER f i') (count n)) IN sts` *)
             REWRITE_TAC [GSYM BIGUNION_IMAGE_OVER_INTER_R] \\
            `f' x' INTER BIGUNION (IMAGE f (count n)) = f' x'` by PROVE_TAC [] \\
             POP_ORW >> METIS_TAC [SUBSET_DEF, IN_IMAGE, IN_COUNT]) >> Rewr' \\
         SIMP_TAC std_ss [o_DEF] \\
      (* applying NESTED_EXTREAL_SUM_IMAGE_REVERSE, swapping the two SIGMAs *)
         Know `!i. (\i'. mu (f i INTER f' i')) = (\i i'. mu (f i INTER f' i')) i`
         >- PROVE_TAC [] >> Rewr' \\
         Know `!i. (\i'. mu (f' i INTER f i')) = (\i i'. mu (f' i INTER f i')) i`
         >- PROVE_TAC [] >> Rewr' \\
         Know `SIGMA (\i. SIGMA ((\i i'. mu (f' i INTER f i')) i) (count n)) (count n') =
               SIGMA (\i. SIGMA (\y. (\i i'. mu (f' i INTER f i')) y i) (count n')) (count n)`
         >- (MATCH_MP_TAC NESTED_EXTREAL_SUM_IMAGE_REVERSE \\
             RW_TAC std_ss [FINITE_COUNT, IN_COUNT] \\
             MATCH_MP_TAC pos_not_neginf \\
             fs [positive_def, measure_def, measurable_sets_def] \\
             Q.PAT_X_ASSUM `!s. s IN sts ==> 0 <= mu s` MATCH_MP_TAC \\
             MATCH_MP_TAC
                (REWRITE_RULE [subsets_def] (Q.SPEC `(sp,sts)` SEMIRING_INTER)) \\
             METIS_TAC [SUBSET_DEF, IN_COUNT, IN_IMAGE]) >> Rewr' \\
      (* reduce one level of SIGMA *)
         irule EXTREAL_SUM_IMAGE_EQ \\
         SIMP_TAC std_ss [IN_COUNT, FINITE_COUNT] \\
         MATCH_MP_TAC (prove (``!a b c. b /\ a ==> a /\ (b \/ c)``, PROVE_TAC [])) \\
         STRONG_CONJ_TAC
         >- (GEN_TAC >> DISCH_TAC >> CONJ_TAC \\ (* 2 subgoals, same tactics *)
             MATCH_MP_TAC pos_not_neginf \\
             irule EXTREAL_SUM_IMAGE_POS >> RW_TAC std_ss [IN_COUNT, FINITE_COUNT] \\
             fs [positive_def, measure_def, measurable_sets_def] \\
             Q.PAT_ASSUM `!s. s IN sts ==> 0 <= mu s` MATCH_MP_TAC \\
             MATCH_MP_TAC
                (REWRITE_RULE [subsets_def] (Q.SPEC `(sp,sts)` SEMIRING_INTER)) \\
             PROVE_TAC [SUBSET_DEF, IN_COUNT, IN_IMAGE]) \\
         rpt STRIP_TAC \\
      (* reduce another level of SIGMA *)
         irule EXTREAL_SUM_IMAGE_EQ \\
         SIMP_TAC std_ss [IN_COUNT, FINITE_COUNT] \\
         MATCH_MP_TAC (prove (``!a b c. b /\ a ==> a /\ (b \/ c)``, PROVE_TAC [])) \\
         STRONG_CONJ_TAC
         >- (GEN_TAC >> DISCH_TAC >> CONJ_TAC \\ (* 2 subgoals, same tactics *)
             MATCH_MP_TAC pos_not_neginf \\
             fs [positive_def, measure_def, measurable_sets_def] \\
             Q.PAT_ASSUM `!s. s IN sts ==> 0 <= mu s` MATCH_MP_TAC \\
             MATCH_MP_TAC
                (REWRITE_RULE [subsets_def] (Q.SPEC `(sp,sts)` SEMIRING_INTER)) \\
             PROVE_TAC [SUBSET_DEF, IN_COUNT, IN_IMAGE]) \\
         rpt STRIP_TAC \\
         PROVE_TAC [INTER_COMM]) >> DISCH_TAC \\
  (* m' is the inf (or sup) of M, which is either empty or a singleton *)
     Q.ABBREV_TAC `(m' :'a measure) = inf o M` \\
  (* we prove that the "inf" can be eliminated given one element in (M a) *)
     Know `!a r. r IN (M a) ==> (m' a = r)`
     >- (rpt STRIP_TAC \\
         Q.UNABBREV_TAC `m'` >> SIMP_TAC std_ss [GSPECIFICATION] \\
         MATCH_MP_TAC inf_const_alt \\
         CONJ_TAC >- (Q.EXISTS_TAC `r` >> PROVE_TAC [IN_APP]) \\
         METIS_TAC [IN_APP]) >> DISCH_TAC \\
  (* now we can prove (6.3) as a property of m', easily. *)
     Know `!c. c SUBSET sts /\ FINITE c /\ disjoint c ==> (m' (BIGUNION c) = SIGMA mu c)`
     >- (rpt STRIP_TAC >> FIRST_X_ASSUM MATCH_MP_TAC \\
         Q.UNABBREV_TAC `M` >> SIMP_TAC std_ss [GSPECIFICATION] \\
         Q.EXISTS_TAC `c` >> art []) >> DISCH_TAC \\
  (* m' extends mu on sts *)
     Know `!s. s IN sts ==> (m' s = mu s)`
     >- (rpt STRIP_TAC \\
        `m' s = m' (BIGUNION {s})` by PROVE_TAC [BIGUNION_SING] >> POP_ORW \\
         Know `m' (BIGUNION {s}) = SIGMA mu {s}`
         >- (FIRST_X_ASSUM MATCH_MP_TAC >> REWRITE_TAC [FINITE_SING, disjoint_sing] \\
             PROVE_TAC [SUBSET_DEF, IN_SING]) >> Rewr' \\
         REWRITE_TAC [EXTREAL_SUM_IMAGE_SING]) >> DISCH_TAC \\
  (* Let us show that m' is sigma-additive on S, i.e. a pre-measure. *)
     Know `premeasure (sp,S,m')`
     >- (SIMP_TAC std_ss [premeasure_def, m_space_def, measurable_sets_def] \\
         STRONG_CONJ_TAC (* positive (sp,S,m') *)
         >- (SIMP_TAC std_ss [positive_def, measure_def] \\
             rpt STRIP_TAC >| (* 2 subgoals *)
             [ (* goal 1 (of 2): m' {} = 0 *)
               FIRST_X_ASSUM MATCH_MP_TAC \\
               Q.UNABBREV_TAC `M` >> SIMP_TAC std_ss [GSPECIFICATION] \\
               Q.EXISTS_TAC `{}` \\
               REWRITE_TAC [EMPTY_SUBSET, FINITE_EMPTY, disjoint_empty, BIGUNION_EMPTY,
                            EXTREAL_SUM_IMAGE_EMPTY],
               (* goal 2 (of 2): 0 <= m' s *)
               Q.UNABBREV_TAC `m'` >> SIMP_TAC std_ss [GSPECIFICATION] \\
               REWRITE_TAC [le_inf] >> GEN_TAC \\
               Suff `y IN (M s) ==> 0 <= y` >- PROVE_TAC [IN_APP] \\
               Q.UNABBREV_TAC `M` >> SIMP_TAC std_ss [GSPECIFICATION] \\
               rpt STRIP_TAC >> POP_ORW \\
            (* 0 <= SIGMA mu c *)
               MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> art [] \\
               rpt STRIP_TAC \\
               fs [positive_def, measure_def, measurable_sets_def] \\
               Q.PAT_X_ASSUM `!s. s IN sts ==> 0 <= mu s` MATCH_MP_TAC \\
               PROVE_TAC [SUBSET_DEF] ]) >> DISCH_TAC \\
      (************************************************************************)
         PRINT_TAC "Step 2c. Claim: m' is countably-additive (hard)" \\
      (************************************************************************)
      (* countably_additive (sp,S,m') *)
         RW_TAC std_ss [countably_additive_def, measure_def, measurable_sets_def,
                        IN_FUNSET, IN_UNIV] \\
         Know `!x. ?c. (f x = BIGUNION c) /\ c SUBSET sts /\ FINITE c /\ disjoint c`
         >- (GEN_TAC >> Q.PAT_X_ASSUM `!x. f x IN S` (MP_TAC o (Q.SPEC `x'`)) \\
             Q.UNABBREV_TAC `S` >> SIMP_TAC std_ss [GSPECIFICATION]) \\
         SIMP_TAC std_ss [SKOLEM_THM] >> STRIP_TAC \\ (* skolemization here *)
      (* g is a finite disjoint union of (f n) *)
        `!n. f n = BIGUNION (f' n)`
             by PROVE_TAC [] >> rename1 `!n. f n = BIGUNION (g n)` \\
        `!n. g n SUBSET sts` by PROVE_TAC [] \\
        `!n. FINITE (g n)`   by PROVE_TAC [] \\
        `!n. disjoint (g n)` by PROVE_TAC [] \\
         Q.PAT_X_ASSUM `!x. (f x = BIGUNION (g x)) /\ P` K_TAC \\
      (* applying countable_disjoint_decomposition *)
         Know `!x. ?h n. (!i. i < n ==> h i IN (g x)) /\ (!i. n <= i ==> (h i = {})) /\
                         (g x = IMAGE h (count n)) /\
                         (BIGUNION (g x) = BIGUNION (IMAGE h univ(:num))) /\
                         (!i j. i < n /\ j < n /\ i <> j ==> h i <> h j) /\
                         (!i j. i < n /\ j < n /\ i <> j ==> DISJOINT (h i) (h j))`
         >- (Q.X_GEN_TAC `n` \\
             Know `FINITE (g n) /\ disjoint (g n)` >- PROVE_TAC [] \\
             DISCH_THEN (STRIP_ASSUME_TAC o (MATCH_MP countable_disjoint_decomposition)) \\
             Q.EXISTS_TAC `f'` >> Q.EXISTS_TAC `n'` >> art []) \\
         SIMP_TAC std_ss [SKOLEM_THM] >> STRIP_TAC \\ (* skolemization here *)
        `!n i. i < f'' n ==> f' n i IN g n` by PROVE_TAC [] \\
         rename1 `!n i. i < p n ==> s n i IN g n` \\
        `!n i. p n <= i ==> (s n i = {})`                         by PROVE_TAC [] \\
        `!n. g n = IMAGE (s n) (count (p n))`                     by PROVE_TAC [] \\
        `!n. BIGUNION (g n) = BIGUNION (IMAGE (s n) univ(:num))`  by PROVE_TAC [] \\
        `!n i j. i < p n /\ j < p n /\ i <> j ==> s n i <> s n j` by PROVE_TAC [] \\
        `!n i j. i < p n /\ j < p n /\ i <> j ==>
                 DISJOINT (s n i) (s n j)`                        by PROVE_TAC [] \\
         Q.PAT_X_ASSUM `!x. (!i. i < p x ==> s x i IN g x) /\ X`  K_TAC \\
      (* properties of 2-dimension sets s(n,i), p(n) is the length of each f(n) *)
         Know `!n i. s n i IN sts`
         >- (rpt GEN_TAC >> Cases_on `p n <= i` (* easy case *)
             >- (`s n i = {}` by PROVE_TAC [] >> art [] \\
                 PROVE_TAC [semiring_def, subsets_def]) \\
             POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [GSYM NOT_LESS])) \\
            `s n i IN g n` by PROVE_TAC [] \\
             PROVE_TAC [SUBSET_DEF]) >> DISCH_TAC \\
         STRIP_ASSUME_TAC NUM_2D_BIJ_INV \\
         rename1 `BIJ h univ(:num) (univ(:num) CROSS univ(:num))` \\
         Know `BIGUNION (IMAGE f univ(:num)) =
               BIGUNION (IMAGE (\n. BIGUNION (IMAGE (s n) univ(:num))) univ(:num))`
         >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV]) >> DISCH_TAC \\
         STRIP_ASSUME_TAC (Q.SPEC `s` BIGUNION_IMAGE_BIGUNION_IMAGE_UNIV) \\
         STRIP_ASSUME_TAC (MATCH_MP (Q.SPEC `s` BIGUNION_IMAGE_UNIV_CROSS_UNIV)
                                    (ASSUME ``BIJ h univ(:num) (univ(:num) CROSS univ(:num))``)) \\
         Know `BIGUNION (IMAGE f univ(:num)) = BIGUNION (IMAGE (UNCURRY s o h) univ(:num))`
         >- METIS_TAC [] >> NTAC 3 (POP_ASSUM K_TAC) >> DISCH_TAC >> art [] \\
      (* now we show that `z` is a countable disjoint union of sets in sts, constructed by
         compressing f and g together. Once the properties of z were established, we don't
         need to uncompress it back any more, nor needed properties of f and g. *)
         Q.ABBREV_TAC `z = UNCURRY s o h` \\
         Know `!n. (z n) IN sts`
         >- (Q.UNABBREV_TAC `z` >> RW_TAC std_ss [UNCURRY, o_DEF]) >> DISCH_TAC \\
         Know `BIGUNION (IMAGE z univ(:num)) IN S`
         >- (Q.UNABBREV_TAC `z` >> METIS_TAC []) >> DISCH_TAC \\
      (* disjointness of z *)
         Know `!i j k l. i <> j ==> DISJOINT (s i k) (s j l)`
         >- (rpt STRIP_TAC \\
             Cases_on `p i <= k` >- METIS_TAC [DISJOINT_EMPTY] \\
             Cases_on `p j <= l` >- METIS_TAC [DISJOINT_EMPTY] \\
            `DISJOINT (BIGUNION (g i)) (BIGUNION (g j))` by PROVE_TAC [] \\
             POP_ASSUM (irule o (REWRITE_RULE [DISJOINT_BIGUNION])) \\
             fs [NOT_LESS_EQUAL]) >> DISCH_TAC \\
         Know `!i j. i <> j ==> DISJOINT (z i) (z j)`
         >- (rpt STRIP_TAC \\
             Q.UNABBREV_TAC `z` >> SIMP_TAC std_ss [o_DEF, UNCURRY] \\
             Cases_on `FST (h i) = FST (h j)`
             >- (Cases_on `p (FST (h i)) <= SND (h i)` >- METIS_TAC [DISJOINT_EMPTY] \\
                 Cases_on `p (FST (h j)) <= SND (h j)` >- METIS_TAC [DISJOINT_EMPTY] \\
                 fs [NOT_LESS_EQUAL] \\
                 LAST_X_ASSUM MATCH_MP_TAC >> rfs [] \\
                 CCONTR_TAC >> fs [] \\
                `h i = h j` by PROVE_TAC [PAIR_FST_SND_EQ] \\
                 METIS_TAC [BIJ_DEF, INJ_DEF, IN_UNIV, IN_CROSS]) \\
             FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> DISCH_TAC \\
      (* construct another finite disjoint union such that BIGUNION c = Z *)
         Q.ABBREV_TAC `Z = BIGUNION (IMAGE z univ(:num))` \\
         Know `?c. (Z = BIGUNION c) /\ c SUBSET sts /\ FINITE c /\ disjoint c`
         >- (Q.PAT_X_ASSUM `Z IN S` MP_TAC \\
             Q.UNABBREV_TAC `S` >> SET_SPEC_TAC [] >> STRIP_TAC \\
             Q.EXISTS_TAC `c` >> art []) >> STRIP_TAC \\
         PURE_ASM_REWRITE_TAC [] \\
         Know `m' (BIGUNION c) = SIGMA mu c`
         >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> Rewr' \\
      (* convert c into a disjoint sequence f' of sets *)
         STRIP_ASSUME_TAC (MATCH_MP finite_disjoint_decomposition
                                    (CONJ (ASSUME ``FINITE (c :'a set set)``)
                                          (ASSUME ``disjoint (c :'a set set)``))) \\
         PURE_ASM_REWRITE_TAC [] \\
      (* SIGMA mu (IMAGE f' (count n)) = suminf (m' o f) *)
         Know `!i. i < n ==> (f' i = (f' i) INTER BIGUNION (IMAGE z univ(:num)))`
         >- (rpt STRIP_TAC \\
             MATCH_MP_TAC EQ_SYM >> REWRITE_TAC [INTER_SUBSET_EQN] \\
             `BIGUNION (IMAGE z univ(:num)) = BIGUNION (IMAGE f' (count n))` by PROVE_TAC [] \\
             POP_ORW >> MATCH_MP_TAC SUBSET_BIGUNION_I \\
             RW_TAC std_ss [IN_IMAGE, IN_COUNT]) >> DISCH_TAC \\
      (* LHS reductions *)
         Know `SIGMA mu (IMAGE f' (count n)) = SIGMA (mu o f') (count n)`
         >- (irule EXTREAL_SUM_IMAGE_IMAGE \\
             RW_TAC std_ss [FINITE_COUNT, IN_IMAGE, IN_COUNT] >| (* 2 subgoals *)
             [ (* goal 1 (of 2) *)
               DISJ1_TAC >> GEN_TAC >> STRIP_TAC >> art [] \\
               MATCH_MP_TAC pos_not_neginf \\
              `f' x'' IN sts` by PROVE_TAC [SUBSET_DEF, IN_IMAGE, IN_COUNT] \\
               METIS_TAC [positive_def, measure_def, measurable_sets_def],
               (* goal 2 (of 2) *)
               MATCH_MP_TAC INJ_IMAGE >> Q.EXISTS_TAC `sts` \\
               RW_TAC std_ss [INJ_DEF, IN_COUNT] >- PROVE_TAC [SUBSET_DEF, IN_IMAGE, IN_COUNT] \\
               CCONTR_TAC >> PROVE_TAC [] ]) >> Rewr' \\
         Know `SIGMA (mu o f') (count n) =
               SIGMA (mu o (\i. (f' i) INTER BIGUNION (IMAGE z univ(:num)))) (count n)`
         >- (irule EXTREAL_SUM_IMAGE_EQ \\
             SIMP_TAC std_ss [FINITE_COUNT, IN_COUNT, o_DEF] \\
             CONJ_TAC >- (rpt STRIP_TAC >> METIS_TAC []) \\
             DISJ1_TAC >> GEN_TAC >> STRIP_TAC \\
             CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf \\
                          `f' x' IN sts` by PROVE_TAC [SUBSET_DEF, IN_IMAGE, IN_COUNT] \\
                          METIS_TAC [positive_def, measure_def, measurable_sets_def]) \\
            `f' x' INTER BIGUNION (IMAGE z univ(:num)) = f' x'` by METIS_TAC [] >> POP_ORW \\
             MATCH_MP_TAC pos_not_neginf \\
            `f' x' IN sts` by PROVE_TAC [SUBSET_DEF, IN_IMAGE, IN_COUNT] \\
             METIS_TAC [positive_def, measure_def, measurable_sets_def]) >> Rewr' \\
        `!i. f' i INTER BIGUNION (IMAGE z univ(:num)) = BIGUNION (IMAGE (\n. f' i INTER z n) univ(:num))`
                by REWRITE_TAC [BIGUNION_OVER_INTER_R] >> art [] \\
         Know `!i. i < n ==> BIGUNION (IMAGE (\n. f' i INTER z n) univ(:num)) IN sts`
         >- (rpt STRIP_TAC \\
             FIRST_X_ASSUM (ONCE_REWRITE_TAC o wrap o (MATCH_MP EQ_SYM) o (Q.SPEC `i`)) \\
             Q.PAT_X_ASSUM `!i. i < n ==> X`
                (ONCE_REWRITE_TAC o wrap o (MATCH_MP EQ_SYM) o
                 (fn th => (MATCH_MP th (ASSUME ``(i :num) < n``)))) \\
             PROVE_TAC [SUBSET_DEF, IN_IMAGE, IN_COUNT]) >> DISCH_TAC \\
         Know `!i j. i < n ==> (f' i INTER z j) IN sts`
         >- (rpt STRIP_TAC \\
             MATCH_MP_TAC (REWRITE_RULE [subsets_def] (Q.SPEC `(sp,sts)` SEMIRING_INTER)) \\
             art [] >> PROVE_TAC [SUBSET_DEF, IN_COUNT, IN_IMAGE]) >> DISCH_TAC \\
         Know `!i. i < n ==> (mu (BIGUNION (IMAGE (\n. f' i INTER z n) univ(:num))) =
                              suminf (mu o (\n. f' i INTER z n)))`
         >- (rpt STRIP_TAC >> MATCH_MP_TAC EQ_SYM \\
             MATCH_MP_TAC (REWRITE_RULE [measure_def, measurable_sets_def]
                                        (Q.SPEC `(sp,sts,mu)` COUNTABLY_ADDITIVE)) \\
             ASM_SIMP_TAC std_ss [IN_FUNSET, IN_UNIV] \\
             Q.X_GEN_TAC `a` >> Q.X_GEN_TAC `b` >> DISCH_TAC \\
             MATCH_MP_TAC DISJOINT_RESTRICT_R \\
             FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> DISCH_TAC \\
      (* only rewrite LHS *)
         GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [o_DEF] \\
         BETA_TAC \\
         Know `SIGMA (\i. mu (BIGUNION (IMAGE (\n. f' i INTER z n) univ(:num)))) (count n) =
               SIGMA (\i. suminf (mu o (\n. f' i INTER z n))) (count n)`
         >- (irule EXTREAL_SUM_IMAGE_EQ \\
             SIMP_TAC std_ss [FINITE_COUNT, IN_COUNT] \\
             CONJ_TAC >- (rpt STRIP_TAC >> FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
             DISJ1_TAC >> GEN_TAC >> STRIP_TAC \\
             CONJ_TAC >- (MATCH_MP_TAC pos_not_neginf \\
                          METIS_TAC [positive_def, measure_def, measurable_sets_def]) \\
             MATCH_MP_TAC pos_not_neginf \\
             MATCH_MP_TAC ext_suminf_pos >> RW_TAC std_ss [o_DEF] \\
             Know `(f' x' INTER z n') IN sts`
             >- (MATCH_MP_TAC (REWRITE_RULE [subsets_def] (Q.SPEC `(sp,sts)` SEMIRING_INTER)) \\
                 art [] >> PROVE_TAC [SUBSET_DEF, IN_IMAGE, IN_COUNT]) >> DISCH_TAC \\
             METIS_TAC [positive_def, measure_def, measurable_sets_def]) >> Rewr' \\
      (* only rewrite LHS *)
         GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [o_DEF] \\
         BETA_TAC \\
      (* clean up useless assums *)
         POP_ASSUM K_TAC \\
         Q.PAT_X_ASSUM `!i. f' i INTER BIGUNION (IMAGE z univ(:num)) = X` K_TAC \\
         Q.PAT_X_ASSUM `!i. i < n ==> (f' i = f' i INTER BIGUNION (IMAGE z univ(:num)))` K_TAC \\
         Q.PAT_X_ASSUM `!i. i < n ==> BIGUNION (IMAGE (\n. f' i INTER z n) univ(:num)) IN sts` K_TAC \\
      (* stage: SIGMA (\i. suminf (\x. mu (f' i INTER z x))) (count n) = suminf (m' o f) *)
         Know `(\i. suminf (\x. mu (f' i INTER z x))) = (suminf o (\i x. mu (f' i INTER z x)))`
         >- (FUN_EQ_TAC >> Q.X_GEN_TAC `i` >> REWRITE_TAC [o_DEF] \\
             BETA_TAC >> REWRITE_TAC []) >> Rewr' \\
         Know `SIGMA (suminf o (\i x. mu (f' i INTER z x))) (count n) =
               suminf (\x. SIGMA (\i. (\i x. mu (f' i INTER z x)) i x) (count n))`
         >- (MATCH_MP_TAC ext_suminf_sigma >> BETA_TAC >> rpt STRIP_TAC \\
             Know `f' i INTER z x' IN sts`
             >- (MATCH_MP_TAC (REWRITE_RULE [subsets_def] (Q.SPEC `(sp,sts)` SEMIRING_INTER)) \\
                 art [] >> PROVE_TAC [SUBSET_DEF]) >> DISCH_TAC \\
             METIS_TAC [positive_def, measure_def, measurable_sets_def]) >> Rewr' \\
         BETA_TAC \\
      (* suminf (\x. SIGMA (\i. mu (f' i INTER z x)) (count n)) = suminf (m' o f) *)
         Know `!x. (\i. mu (f' i INTER z x)) = mu o (\i. f' i INTER z x)`
         >- (REWRITE_TAC [o_DEF] >> BETA_TAC >> GEN_TAC >> FUN_EQ_TAC \\
             BETA_TAC >> GEN_TAC >> REWRITE_TAC []) >> Rewr' \\
         Know `!x. SIGMA (mu o (\i. f' i INTER z x)) (count n) =
                   SIGMA mu (IMAGE (\i. f' i INTER z x) (count n))`
         >- (Q.X_GEN_TAC `j` \\
             NTAC 3 (POP_ASSUM MP_TAC) \\
             POP_ASSUM K_TAC \\ (* c = IMAGE f' (count n) *)
             POP_ASSUM MP_TAC \\
             Q.SPEC_TAC (`n`, `n`) \\
             Induct_on `n` >- (RW_TAC arith_ss [] \\
                               art [COUNT_ZERO, EXTREAL_SUM_IMAGE_EMPTY, IMAGE_EMPTY]) \\
             rpt STRIP_TAC \\
            `mu {} = 0` by PROVE_TAC [positive_def, measure_def, measurable_sets_def] \\
             REWRITE_TAC [COUNT_SUC, IMAGE_INSERT] \\
             Know `SIGMA (mu o (\i. f' i INTER z j)) (n INSERT count n) =
                   (mu o (\i. f' i INTER z j)) n + SIGMA (mu o (\i. f' i INTER z j)) (count n DELETE n)`
             >- (irule EXTREAL_SUM_IMAGE_PROPERTY >> art [FINITE_COUNT] \\
                 DISJ1_TAC >> SIMP_TAC std_ss [IN_INSERT, IN_COUNT, o_DEF] \\
                 GEN_TAC >> DISCH_TAC >> MATCH_MP_TAC pos_not_neginf \\
                `x' < SUC n` by RW_TAC arith_ss [] \\
                `f' x' INTER z j IN sts` by PROVE_TAC [] \\
                 METIS_TAC [positive_def, measure_def, measurable_sets_def]) >> Rewr' \\
             SIMP_TAC std_ss [COUNT_DELETE] \\
             Know `SIGMA mu (f' n INTER z j INSERT IMAGE (\i. f' i INTER z j) (count n)) =
                   mu (f' n INTER z j) +
                   SIGMA mu ((IMAGE (\i. f' i INTER z j) (count n)) DELETE (f' n INTER z j))`
             >- (irule EXTREAL_SUM_IMAGE_PROPERTY \\
                 CONJ_TAC >- (MATCH_MP_TAC IMAGE_FINITE >> REWRITE_TAC [FINITE_COUNT]) \\
                 DISJ1_TAC >> GEN_TAC >> SIMP_TAC std_ss [IN_INSERT, IN_IMAGE, IN_COUNT] \\
                 STRIP_TAC
                 >- (art [] >> MATCH_MP_TAC pos_not_neginf \\
                     `f' n INTER z j IN sts` by RW_TAC std_ss [] \\
                     METIS_TAC [positive_def, measure_def, measurable_sets_def]) \\
                 art [] >> MATCH_MP_TAC pos_not_neginf \\
                 `f' i INTER z j IN sts` by RW_TAC arith_ss [] \\
                 METIS_TAC [positive_def, measure_def, measurable_sets_def]) >> Rewr' \\
             Know `SIGMA mu (IMAGE (\i. f' i INTER z j) (count n) DELETE f' n INTER z j) =
                   SIGMA mu (IMAGE (\i. f' i INTER z j) (count n))`
             >- (Cases_on `(f' n INTER z j) NOTIN (IMAGE (\i. f' i INTER z j) (count n))`
                 >- METIS_TAC [DELETE_NON_ELEMENT] \\
                 POP_ASSUM MP_TAC >> SIMP_TAC arith_ss [IN_IMAGE, IN_COUNT] \\
              (* ?i. (f' n INTER z j = f' i INTER z j) /\ i < n *)
                 STRIP_TAC \\
                `n < SUC n /\ i < SUC n /\ n <> i` by RW_TAC arith_ss [] \\
                `DISJOINT (f' n INTER z j) (f' i INTER z j)` by PROVE_TAC [DISJOINT_RESTRICT_L] \\
                `(f' n INTER z j = {}) /\ (f' i INTER z j = {})` by PROVE_TAC [DISJOINT_EMPTY_REFL] \\
                 art [DELETE_DEF] >> MATCH_MP_TAC EQ_SYM \\
                 irule EXTREAL_SUM_IMAGE_ZERO_DIFF \\
                 ASM_SIMP_TAC std_ss [IN_SING, IN_IMAGE, IN_COUNT] \\
                 CONJ_TAC >- (MATCH_MP_TAC IMAGE_FINITE >> REWRITE_TAC [FINITE_COUNT]) \\
                 DISJ1_TAC >> GEN_TAC >> STRIP_TAC >> art [] \\
                 MATCH_MP_TAC pos_not_neginf \\
                `f' i' INTER z j IN sts` by RW_TAC arith_ss [] \\
                 METIS_TAC [positive_def, measure_def, measurable_sets_def]) >> Rewr' \\
            `!i. i < n ==> f' i IN c` by RW_TAC arith_ss [] \\
            `!i j. i < n /\ j < n /\ i <> j ==> f' i <> f' j` by RW_TAC arith_ss [] \\
            `!i j. i < n /\ j < n /\ i <> j ==> DISJOINT (f' i) (f' j)` by RW_TAC arith_ss [] \\
            `!i j. i < n ==> f' i INTER z j IN sts` by RW_TAC arith_ss [] \\
            `SIGMA (mu o (\i. f' i INTER z j)) (count n) =
             SIGMA mu (IMAGE (\i. f' i INTER z j) (count n))` by PROVE_TAC [] \\
             Q.PAT_X_ASSUM `(!i. i < n ==> f' i IN c) ==> X` K_TAC \\
             ASM_REWRITE_TAC []) >> Rewr' \\
      (* suminf (\x. SIGMA mu (IMAGE (\i. f' i INTER z x) (count n))) = suminf (m' o f) *)
         Know `!x. SIGMA mu (IMAGE (\i. f' i INTER z x) (count n)) =
                   m' (BIGUNION (IMAGE (\i. f' i INTER z x) (count n)))`
         >- (Q.X_GEN_TAC `y` >> MATCH_MP_TAC EQ_SYM \\
             FIRST_X_ASSUM MATCH_MP_TAC \\
             CONJ_TAC >- (RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT] >> PROVE_TAC []) \\
             CONJ_TAC >- (MATCH_MP_TAC IMAGE_FINITE >> REWRITE_TAC [FINITE_COUNT]) \\
             RW_TAC std_ss [disjoint_def, IN_IMAGE, IN_COUNT] \\
             Cases_on `i = i'` >- METIS_TAC [] \\
             MATCH_MP_TAC DISJOINT_RESTRICT_L >> PROVE_TAC []) >> Rewr' \\
         REWRITE_TAC [GSYM BIGUNION_IMAGE_OVER_INTER_L] \\
        `BIGUNION (IMAGE f' (count n)) = BIGUNION (IMAGE z univ(:num))` by PROVE_TAC [] \\
         POP_ORW \\
         Know `!x. BIGUNION (IMAGE z univ(:num)) INTER z x = z x`
         >- (GEN_TAC >> REWRITE_TAC [INTER_SUBSET_EQN] \\
             RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_UNIV] \\
             Q.EXISTS_TAC `x'` >> art []) >> Rewr' \\
      (* RHS reductions: *)
        `f = \n. BIGUNION (IMAGE (s n) (count (p n)))` by METIS_TAC [] >> POP_ORW \\
         SIMP_TAC std_ss [o_DEF] \\
         Know `!n. m' (BIGUNION (IMAGE (s n) (count (p n)))) =
                   SIGMA mu (IMAGE (s n) (count (p n)))`
         >- (GEN_TAC >> FIRST_X_ASSUM MATCH_MP_TAC \\
             CONJ_TAC >- METIS_TAC [SUBSET_DEF, IN_IMAGE, IN_COUNT] \\
             CONJ_TAC >- (MATCH_MP_TAC IMAGE_FINITE >> REWRITE_TAC [FINITE_COUNT]) \\
             RW_TAC std_ss [disjoint_def, IN_IMAGE, IN_COUNT] \\
             LAST_X_ASSUM MATCH_MP_TAC >> art [] >> PROVE_TAC []) >> Rewr' \\
         Know `!n. SIGMA mu (IMAGE (s n) (count (p n))) = SIGMA (mu o (s n)) (count (p n))`
         >- (GEN_TAC >> irule EXTREAL_SUM_IMAGE_IMAGE \\
             art [FINITE_COUNT, IN_IMAGE, IN_COUNT] >> CONJ_TAC
             >- (DISJ1_TAC >> GEN_TAC >> STRIP_TAC \\
                 MATCH_MP_TAC pos_not_neginf >> art [] \\
                 PROVE_TAC [positive_def, measure_def, measurable_sets_def]) \\
             MATCH_MP_TAC INJ_IMAGE >> Q.EXISTS_TAC `sts` \\
             RW_TAC std_ss [INJ_DEF, IN_COUNT] >> PROVE_TAC []) >> Rewr' \\
         Know `!n. SIGMA (mu o s n) (count (p n)) = suminf (mu o s n)`
         >- (GEN_TAC >> MATCH_MP_TAC EQ_SYM \\
             MATCH_MP_TAC ext_suminf_sum >> SIMP_TAC std_ss [o_DEF] \\
             CONJ_TAC >- (GEN_TAC >> PROVE_TAC [positive_def, measure_def, measurable_sets_def]) \\
             RW_TAC std_ss [] \\
             PROVE_TAC [positive_def, measure_def, measurable_sets_def]) >> Rewr' \\
         Know `!x. m' (z x) = mu (z x)` >- METIS_TAC [] >> Rewr' \\
      (* suminf (\x. mu (z x)) = suminf (\n. suminf (mu o s n)) *)
         Q.UNABBREV_TAC `z` >> SIMP_TAC std_ss [o_DEF, UNCURRY] \\
      (* preparing for applying ext_suminf_2d *)
         Q.ABBREV_TAC `ms = \x y. mu (s x y)` \\
        `!x. mu (s (FST (h x)) (SND (h x))) = ms (FST (h x)) (SND (h x))`
             by METIS_TAC [] >> POP_ORW \\
        `!n x. mu (s n x) = ms n x` by METIS_TAC [] >> POP_ORW \\
        `(\x. ms (FST (h x)) (SND (h x))) = UNCURRY ms o h`
             by METIS_TAC [o_DEF, UNCURRY] >> POP_ORW \\
      (* suminf (UNCURRY ms o h) = suminf (\n. suminf (\x. ms n x)) *)
         MATCH_MP_TAC ext_suminf_2d_full \\
         Q.UNABBREV_TAC `ms` >> ASM_SIMP_TAC std_ss [] \\
         rpt GEN_TAC >> PROVE_TAC [positive_def, measure_def, measurable_sets_def]) \\
     DISCH_TAC \\
  (* mu x <= m x *)
    `mu x = m' x` by PROVE_TAC [] >> POP_ORW \\
     Q.PAT_X_ASSUM `outer_measure_space (sp,POW sp,m)` K_TAC \\
  (* m' x <= m x *)
     Q.UNABBREV_TAC `m` >> SIMP_TAC std_ss [GSPECIFICATION] \\
     REWRITE_TAC [le_inf'] >> GEN_TAC \\
     SIMP_TAC std_ss [GSPECIFICATION] >> rpt STRIP_TAC \\
     POP_ASSUM (ONCE_REWRITE_TAC o wrap o (MATCH_MP EQ_SYM)) \\
  (* m' x <= suminf (mu o f) *)
     POP_ASSUM MP_TAC (* f IN C x *) \\
     Q.UNABBREV_TAC `C` >> SIMP_TAC std_ss [GSPECIFICATION, IN_FUNSET, IN_UNIV] \\
     rpt STRIP_TAC \\
    `m' x = m' (BIGUNION (IMAGE f univ(:num)) INTER x)`
        by PROVE_TAC [SUBSET_INTER2] >> POP_ORW \\
     REWRITE_TAC [BIGUNION_OVER_INTER_L] \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `suminf (m' o (\i. f i INTER x))` \\
  (* applying countably_subadditive_def of premeasure (sp,S,m') *)
    `countably_subadditive (sp,S,m')`
        by PROVE_TAC [RING_PREMEASURE_COUNTABLY_SUBADDITIVE, premeasure_def,
                      m_space_def, measurable_sets_def] \\
     CONJ_TAC
     >- (fs [countably_subadditive_def, measure_def, measurable_sets_def, IN_FUNSET, IN_UNIV] \\
         POP_ASSUM MATCH_MP_TAC >> BETA_TAC \\
         STRONG_CONJ_TAC (* !x'. f x' INTER x IN S *)
         >- (GEN_TAC >> MATCH_MP_TAC (REWRITE_RULE [subsets_def] (Q.SPEC `(sp,S)` RING_INTER)) \\
             PROVE_TAC [SUBSET_DEF]) >> DISCH_TAC \\
      (* BIGUNION (IMAGE (\i. f i INTER x) univ(:num)) IN S *)
         REWRITE_TAC [GSYM BIGUNION_OVER_INTER_L] \\
         PROVE_TAC [SUBSET_INTER2, SUBSET_DEF]) \\
     Know `m' o (\i. f i INTER x) = mu o (\i. f i INTER x)`
     >- (SIMP_TAC std_ss [o_DEF] >> FUN_EQ_TAC >> GEN_TAC >> BETA_TAC \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
         MATCH_MP_TAC (REWRITE_RULE [subsets_def] (Q.SPEC `(sp,sts)` SEMIRING_INTER)) \\
         art []) >> Rewr' \\
  (* suminf (mu o (\i. f i INTER x)) <= suminf (mu o f) *)
     MATCH_MP_TAC ext_suminf_mono >> GEN_TAC >> SIMP_TAC std_ss [o_DEF] \\
     STRONG_CONJ_TAC
     >- (MATCH_MP_TAC pos_not_neginf \\
         fs [positive_def, measure_def, measurable_sets_def] \\
         Q.PAT_X_ASSUM `!s. s IN sts ==> 0 <= mu s` MATCH_MP_TAC \\
         MATCH_MP_TAC (REWRITE_RULE [subsets_def] (Q.SPEC `(sp,sts)` SEMIRING_INTER)) \\
         METIS_TAC [SUBSET_DEF]) >> DISCH_TAC \\
    `increasing (sp,sts,mu)`
        by PROVE_TAC [SEMIRING_PREMEASURE_INCREASING, premeasure_def,
                      m_space_def, measurable_sets_def] \\
     fs [increasing_def, measure_def, measurable_sets_def] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [INTER_SUBSET] \\
     MATCH_MP_TAC (REWRITE_RULE [subsets_def] (Q.SPEC `(sp,sts)` SEMIRING_INTER)) \\
     PROVE_TAC [SUBSET_DEF])
 >> DISCH_TAC
(******************************************************************************)
 >> PRINT_TAC "Step 3. Claim: sts SUBSET A, where A is m-measurable sets"
(******************************************************************************)
 >> Know `!s t. s IN sts /\ t IN sts ==> m (s INTER t) + m (s DIFF t) <= m s`
 >- (rpt STRIP_TAC \\
     `s INTER t IN sts` by PROVE_TAC [SEMIRING_INTER, subsets_def] \\
  (* special case *)
     Cases_on `s INTER t = {}`
     >- (`s DIFF t = s` by ASM_SET_TAC [] \\
         `mu {} = 0` by PROVE_TAC [positive_def, semiring_def, measure_def, subsets_def,
                                   measurable_sets_def] \\
         `{} IN sts` by PROVE_TAC [semiring_def, subsets_def] \\
         `m {} = 0` by PROVE_TAC [] \\
         art [add_lzero, le_refl]) \\
  (* general case *)
     MP_TAC (REWRITE_RULE [subsets_def]
                          (Q.SPECL [`(sp,sts)`, `s`, `t`] SEMIRING_DIFF)) \\
     RW_TAC std_ss [] \\
     STRIP_ASSUME_TAC (MATCH_MP finite_disjoint_decomposition
                                (CONJ (ASSUME ``FINITE (c :'a set set)``)
                                      (ASSUME ``disjoint (c :'a set set)``))) \\
    `((s INTER t) UNION (s DIFF t) = s) /\
      DISJOINT (s INTER t) (s DIFF t)` by SET_TAC [DISJOINT_DEF] \\
    `mu ((s INTER t) UNION (s DIFF t)) = mu s` by PROVE_TAC [] \\
  (* IMPORTANT: (s INTER t) is disjoint with all (f i), i < n *)
     Know `!i. i < n ==> DISJOINT (s INTER t) (f i)`
     >- (rpt STRIP_TAC \\
         `DISJOINT (s INTER t) (BIGUNION (IMAGE f (count n)))` by PROVE_TAC [] \\
         POP_ASSUM MP_TAC \\
         REWRITE_TAC [DISJOINT_ALT, IN_BIGUNION_IMAGE, IN_COUNT] \\
         METIS_TAC []) >> DISCH_TAC \\
     Know `mu ((s INTER t) UNION (BIGUNION c)) = mu s` >- PROVE_TAC [] \\
     REWRITE_TAC [GSYM BIGUNION_INSERT] >> DISCH_TAC \\
     Know `disjoint ((s INTER t) INSERT c)`
     >- (`(s INTER t) INSERT c =
          {s INTER t} UNION c` by SET_TAC [] >> POP_ORW \\
         MATCH_MP_TAC disjoint_union >> art [disjoint_sing] \\
         ASM_SET_TAC [BIGUNION_SING, disjoint_def, IN_BIGUNION_IMAGE, IN_COUNT]) \\
     DISCH_TAC \\
     Know `mu (BIGUNION (s INTER t INSERT c)) = SIGMA mu (s INTER t INSERT c)`
     >- (MATCH_MP_TAC EQ_SYM \\
         MATCH_MP_TAC (REWRITE_RULE [measure_def, measurable_sets_def]
                                    (Q.SPEC `(sp,sts,mu)` FINITE_ADDITIVE_ALT)) \\
        `finite_additive (sp,sts,mu)`
                by PROVE_TAC [SEMIRING_PREMEASURE_FINITE_ADDITIVE, premeasure_def,
                              m_space_def, measurable_sets_def] \\
         Know `BIGUNION ((s INTER t) INSERT c) = s`
         >- (REWRITE_TAC [BIGUNION_INSERT] \\
             Q.PAT_X_ASSUM `s DIFF t = BIGUNION c` (ONCE_REWRITE_TAC o wrap o (MATCH_MP EQ_SYM)) \\
             SET_TAC []) \\
         Rewr' >> art [FINITE_INSERT, INSERT_SUBSET]) >> DISCH_TAC \\
     `(s INTER t) INSERT c = {s INTER t} UNION c` by SET_TAC [] \\
     Know `c DELETE (s INTER t) = c`
     >- (MATCH_MP_TAC DELETE_NON_ELEMENT_RWT \\
         CCONTR_TAC >> rfs [] \\
        `DISJOINT (s INTER t) (f x)` by PROVE_TAC [] \\
         PROVE_TAC [DISJOINT_EMPTY_REFL_RWT]) >> DISCH_TAC \\
     Know `SIGMA mu (s INTER t INSERT c) = mu (s INTER t) + SIGMA mu (c DELETE s INTER t)`
     >- (irule EXTREAL_SUM_IMAGE_PROPERTY >> art [] \\
         DISJ1_TAC \\
         RW_TAC std_ss [IN_UNION, IN_IMAGE, IN_COUNT, IN_SING] >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           MATCH_MP_TAC pos_not_neginf \\
           PROVE_TAC [positive_def, measure_def, measurable_sets_def],
           (* goal 2 (of 2) *)
           MATCH_MP_TAC pos_not_neginf \\
          `f x' IN sts` by PROVE_TAC [SUBSET_DEF] \\
           PROVE_TAC [positive_def, measure_def, measurable_sets_def] ]) >> DISCH_TAC \\
     Know `m (BIGUNION c) <= SIGMA m c`
     >- (MATCH_MP_TAC (REWRITE_RULE [measure_def, measurable_sets_def]
                                    (Q.SPECL [`(sp,POW sp,m)`, `c`] FINITE_SUBADDITIVE_ALT)) \\
        `finite_subadditive (sp,POW sp,m)`
             by PROVE_TAC [OUTER_MEASURE_SPACE_FINITE_SUBADDITIVE] \\
         fs [outer_measure_space_def] \\
        `subset_class sp sts` by PROVE_TAC [semiring_def, space_def, subsets_def] \\
         RW_TAC std_ss [SUBSET_DEF, IN_POW, IN_BIGUNION] \\ (* 2 subgoals, same tactics *)
         ASM_SET_TAC [subset_class_def]) >> DISCH_TAC \\
     Know `SIGMA mu c = SIGMA m c`
     >- (irule EXTREAL_SUM_IMAGE_EQ >> art [] \\
         CONJ_TAC >- (rpt STRIP_TAC >> PROVE_TAC [SUBSET_DEF]) \\
         DISJ1_TAC >> RW_TAC std_ss [IN_IMAGE, IN_COUNT] >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           MATCH_MP_TAC pos_not_neginf \\
          `f x' IN sts` by PROVE_TAC [SUBSET_DEF] \\
           PROVE_TAC [positive_def, measure_def, measurable_sets_def],
           (* goal 2 (of 2) *)
           MATCH_MP_TAC pos_not_neginf \\
          `f x' IN sts` by PROVE_TAC [SUBSET_DEF] \\
           PROVE_TAC [positive_def, measure_def, measurable_sets_def] ]) >> DISCH_TAC \\
     Know `mu s = m (s INTER t) + SIGMA m c` >- PROVE_TAC [] >> Rewr' \\
     Know `m (s DIFF t) = m (BIGUNION c)` >- PROVE_TAC [] >> Rewr' \\
     Know `mu (s INTER t) = m (s INTER t)` >- PROVE_TAC [] >> Rewr' \\
     MATCH_MP_TAC le_ladd_imp >> art [])
 >> DISCH_TAC
 >> Know `!b s f. s IN sts /\ b SUBSET sp /\ f IN (C b) ==>
                  m (b INTER s) + m (b DIFF s) <= suminf (mu o f)`
 >- (rpt GEN_TAC \\
     Q.PAT_X_ASSUM `Abbrev (m = X)` K_TAC \\ (* useless here *)
     Q.UNABBREV_TAC `C` >> SET_SPEC_TAC [IN_FUNSET, IN_UNIV] >> STRIP_TAC \\
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `m (BIGUNION (IMAGE f univ(:num)) INTER s) + m (BIGUNION (IMAGE f univ(:num)) DIFF s)` \\
    `increasing (sp,POW sp,m)` by PROVE_TAC [outer_measure_space_def] \\
    `subset_class sp sts` by PROVE_TAC [semiring_def, space_def, subsets_def] \\
    `positive (sp,POW sp,m)` by PROVE_TAC [outer_measure_space_def] \\
    `!s. s SUBSET sp ==> 0 <= m s`
        by PROVE_TAC [positive_def, measure_def, measurable_sets_def, IN_POW] \\
    `countably_subadditive (sp,POW sp,m)` by PROVE_TAC [outer_measure_space_def] \\
    `subadditive (sp,POW sp,m)` by PROVE_TAC [OUTER_MEASURE_SPACE_SUBADDITIVE] \\
     CONJ_TAC (* m (b INTER s) + m (b DIFF s) <= ... *)
     >- (MATCH_MP_TAC le_add2 >> STRIP_TAC >|
         [ (* goal 1 (of 2) *)
           MATCH_MP_TAC (REWRITE_RULE [measure_def, measurable_sets_def]
                                      (Q.SPEC `(sp,POW sp,m)` INCREASING)) >> art [IN_POW] \\
           CONJ_TAC >- (MATCH_MP_TAC SUBSET_RESTRICT_L >> art []) \\
           CONJ_TAC >- (MATCH_MP_TAC SUBSET_INTER_SUBSET_L >> art []) \\
           MATCH_MP_TAC SUBSET_INTER_SUBSET_L \\
           RW_TAC std_ss [BIGUNION_SUBSET, IN_IMAGE, IN_UNIV] \\
           PROVE_TAC [subset_class_def],
           (* goal 2 (of 2) *)
           MATCH_MP_TAC (REWRITE_RULE [measure_def, measurable_sets_def]
                                      (Q.SPEC `(sp,POW sp,m)` INCREASING)) >> art [IN_POW] \\
           CONJ_TAC >- (MATCH_MP_TAC SUBSET_MONO_DIFF >> art []) \\
           CONJ_TAC >- (MATCH_MP_TAC SUBSET_DIFF_SUBSET >> art []) \\
           MATCH_MP_TAC SUBSET_DIFF_SUBSET \\
           RW_TAC std_ss [BIGUNION_SUBSET, IN_IMAGE, IN_UNIV] \\
           PROVE_TAC [subset_class_def] ]) \\
     Know `suminf (mu o f) = suminf (m o f)`
     >- (MATCH_MP_TAC ext_suminf_eq >> SIMP_TAC std_ss [o_DEF] \\
         CONJ_TAC >- (DISJ1_TAC >> GEN_TAC >> MATCH_MP_TAC pos_not_neginf \\
                      PROVE_TAC [positive_def, measure_def, measurable_sets_def]) \\
         GEN_TAC >> METIS_TAC []) >> Rewr' \\
     REWRITE_TAC [BIGUNION_OVER_INTER_L, BIGUNION_OVER_DIFF] \\
  (* m (BIGUNION (IMAGE (\i. f i INTER s) univ(:num))) + ... <= suminf (m o f) *)
     MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `suminf (m o (\i. f i INTER s)) + suminf (m o (\i. f i DIFF s))` \\
     CONJ_TAC
     >- (MATCH_MP_TAC le_add2 >> STRIP_TAC >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           MATCH_MP_TAC (REWRITE_RULE [measure_def, measurable_sets_def]
                                      (Q.SPECL [`(sp,POW sp,m)`, `c`] COUNTABLY_SUBADDITIVE)) \\
           art [IN_POW, IN_FUNSET, IN_UNIV] >> BETA_TAC \\
           CONJ_TAC >- (GEN_TAC >> MATCH_MP_TAC SUBSET_INTER_SUBSET_R \\
                        PROVE_TAC [subset_class_def]) \\
           RW_TAC std_ss [BIGUNION_SUBSET, IN_IMAGE, IN_UNIV] \\
           MATCH_MP_TAC SUBSET_INTER_SUBSET_R >> PROVE_TAC [subset_class_def],
           (* goal 2 (of 2) *)
           MATCH_MP_TAC (REWRITE_RULE [measure_def, measurable_sets_def]
                                      (Q.SPECL [`(sp,POW sp,m)`, `c`] COUNTABLY_SUBADDITIVE)) \\
           art [IN_POW, IN_FUNSET, IN_UNIV] >> BETA_TAC \\
           CONJ_TAC >- (GEN_TAC >> MATCH_MP_TAC SUBSET_DIFF_SUBSET \\
                        PROVE_TAC [subset_class_def]) \\
           RW_TAC std_ss [BIGUNION_SUBSET, IN_IMAGE, IN_UNIV] \\
           MATCH_MP_TAC SUBSET_DIFF_SUBSET >> PROVE_TAC [subset_class_def] ]) \\
  (* suminf (m o (\i. f i INTER s)) + suminf (m o (\i. f i DIFF s)) <= suminf (m o f) *)
     Know `suminf (m o (\i. f i INTER s)) + suminf (m o (\i. f i DIFF s)) =
           suminf (\n. (m o (\i. f i INTER s)) n + (m o (\i. f i DIFF s)) n)`
     >- (MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC ext_suminf_add \\
         GEN_TAC >> SIMP_TAC std_ss [o_DEF] \\
         CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC \\
                      MATCH_MP_TAC SUBSET_INTER_SUBSET_R >> PROVE_TAC [subset_class_def]) \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
         MATCH_MP_TAC SUBSET_DIFF_SUBSET >> PROVE_TAC [subset_class_def]) >> Rewr' \\
  (* suminf (\n. (m o (\i. f i INTER s)) n + (m o (\i. f i DIFF s)) n) <= suminf (m o f) *)
     MATCH_MP_TAC ext_suminf_mono \\
     GEN_TAC >> SIMP_TAC std_ss [o_DEF] \\
     Reverse CONJ_TAC >- PROVE_TAC [] \\
     MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC le_add \\
     CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC \\
                  MATCH_MP_TAC SUBSET_INTER_SUBSET_R >> PROVE_TAC [subset_class_def]) \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     MATCH_MP_TAC SUBSET_DIFF_SUBSET >> PROVE_TAC [subset_class_def])
 >> DISCH_TAC
 (* core definition: m-measurable sets *)
 >> Know `sts SUBSET A'` (* this doesn't hold is `sts` is not semiring *)
 >- (REWRITE_TAC [SUBSET_DEF] >> rpt STRIP_TAC \\
     rename1 `s IN A'` \\
     Q.UNABBREV_TAC `A'` >> SET_SPEC_TAC [] \\
     CONJ_TAC >- PROVE_TAC [semiring_def, subset_class_def, space_def, subsets_def] \\
     Q.X_GEN_TAC `b` >> DISCH_TAC \\
    `subadditive (sp,POW sp,m)` by PROVE_TAC [OUTER_MEASURE_SPACE_SUBADDITIVE] \\
  (* m b = m (b INTER s) + m (b DIFF s) *)
     REWRITE_TAC [GSYM le_antisym] >> CONJ_TAC
     >- (MATCH_MP_TAC (REWRITE_RULE [measure_def, measurable_sets_def]
                                    (Q.SPEC `(sp,POW sp,m)` SUBADDITIVE)) \\
         ASM_SIMP_TAC std_ss [IN_POW] >> ASM_SET_TAC []) \\
  (* m (b INTER s) + m (b DIFF s) <= m b *)
    `m b = inf {r | (?f. f IN C b /\ (suminf (mu o f) = r))}` by METIS_TAC [] \\
     POP_ORW >> REWRITE_TAC [le_inf'] >> GEN_TAC \\
     SET_SPEC_TAC [] >> STRIP_TAC >> PROVE_TAC []) >> DISCH_TAC
 >> Q.PAT_X_ASSUM `!s t. s IN sts /\ t IN sts ==> X`                  K_TAC
 >> Q.PAT_X_ASSUM `!b s f. s IN sts /\ b SUBSET sp /\ f IN C b ==> X` K_TAC
(******************************************************************************)
 >> PRINT_TAC "Step 4. Claim: A' is sigma-algebra and m is measure on (sp,A')"
(******************************************************************************)
 >> `sigma_algebra (sp,A')`
     by PROVE_TAC [measure_space_def, m_space_def, measurable_sets_def]
(******************************************************************************)
 >> PRINT_TAC "Step 5. Claim: m is mseaure on (sigma sp sts) which extends mu"
(******************************************************************************)
 >> Q.EXISTS_TAC `(sp,subsets (sigma sp sts),m)`
 >> art [m_space_def, measurable_sets_def, measure_def]
 (* measure_space (sp,subsets (sigma sp sts),m) *)
 >> Reverse CONJ_TAC
 >- (`(subsets (sigma sp sts)) SUBSET (subsets (sigma sp A'))`
        by PROVE_TAC [SIGMA_MONOTONE] \\
     `sigma sp A' = (sp,A')` by PROVE_TAC [SIGMA_OF_SIGMA_ALGEBRA_LEMMA] \\
     `sigma_algebra (sigma sp sts)`
        by PROVE_TAC [SIGMA_ALGEBRA_SIGMA, semiring_def, space_def, subsets_def] \\
     `(subsets (sigma sp sts)) SUBSET A'` by PROVE_TAC [subsets_def] \\
     MATCH_MP_TAC MEASURE_SPACE_RESTRICTION \\
     Q.EXISTS_TAC `A'` >> art [] \\
     `(sp,subsets (sigma sp sts)) = sigma sp sts`
        by METIS_TAC [SPACE_SIGMA, SPACE, space_def, subsets_def] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
     PROVE_TAC [semiring_def, space_def, subsets_def])
 >> METIS_TAC [SPACE_SIGMA, SPACE, space_def, subsets_def]
QED

(* The original Caratheodory theorem proved by Joe Hurd now becomes an easy corollary *)
val CARATHEODORY = store_thm
  ("CARATHEODORY",
  ``!m0.
       algebra (m_space m0, measurable_sets m0) /\
       positive m0 /\ countably_additive m0 ==>
       ?m.
         (!s. s IN measurable_sets m0 ==> (measure m s = measure m0 s)) /\
         ((m_space m, measurable_sets m) =
          sigma (m_space m0) (measurable_sets m0)) /\ measure_space m``,
    GEN_TAC >> STRIP_TAC
 >> MATCH_MP_TAC CARATHEODORY_SEMIRING
 >> IMP_RES_TAC ALGEBRA_IMP_SEMIRING >> art [premeasure_def]
 >> fs [algebra_def, space_def, subsets_def]);

(* The original "ring" version of Caratheodory theorem *)
val CARATHEODORY_RING = store_thm
  ("CARATHEODORY_RING",
  ``!m0.
       ring (m_space m0, measurable_sets m0) /\
       positive m0 /\ countably_additive m0 ==>
       ?m.
         (!s. s IN measurable_sets m0 ==> (measure m s = measure m0 s)) /\
         ((m_space m, measurable_sets m) =
          sigma (m_space m0) (measurable_sets m0)) /\ measure_space m``,
    GEN_TAC >> STRIP_TAC
 >> MATCH_MP_TAC CARATHEODORY_SEMIRING
 >> IMP_RES_TAC RING_IMP_SEMIRING >> art [premeasure_def]
 >> fs [algebra_def, space_def, subsets_def]);

(* ------------------------------------------------------------------------- *)
(*  Completeness of Measure - Null sets                                      *)
(* ------------------------------------------------------------------------- *)

(* s is a null set on measure sapce m, c.f. [1] (p.29) *)
val null_set_def = Define
   `null_set m s <=> s IN measurable_sets m /\ (measure m s = 0)`;

(* MATHEMATICAL SCRIPT CAPITAL N, this is too much, disabled:
val _ = Unicode.unicode_version {u = UTF8.chr 0x1D4A9, tmnm = "null_set"};
 *)

(* a measure space m which is not yet complete can be completed *)
val complete_of_def = Define
   `complete_of m =
      (m_space m, {s UNION n | s IN measurable_sets m /\ ?t. n SUBSET t /\ null_set m t},
       measure m)`;

(* the measure space m is called complete iff any subset of a null set is again
   in `subsets m` (thus also a null set) c.f. [1] (p.29], [5] (p.382) *)
val complete_measure_space_def = Define
   `complete_measure_space m <=>
     measure_space m /\
     !s. null_set m s ==> !t. t SUBSET s ==> t IN measurable_sets m`;

val IN_NULL_SET = store_thm
  ("IN_NULL_SET", ``!m s. s IN null_set m <=> null_set m s``,
    GEN_TAC >> SIMP_TAC std_ss [IN_APP]);

val NULL_SET_EMPTY = store_thm
  ("NULL_SET_EMPTY", ``!m. measure_space m ==> null_set m {}``,
    RW_TAC std_ss [measure_space_def, positive_def, null_set_def]
 >> PROVE_TAC [sigma_algebra_def, ALGEBRA_EMPTY, space_def, subsets_def]);

(* properties of the set of m-null sets, c.f. [1] (p.29, Problem 4.10) *)
val NULL_SET_THM = store_thm
  ("NULL_SET_THM",
  ``!m s t. measure_space m ==>
      {} IN null_set m /\
      (t IN null_set m /\ s IN measurable_sets m /\ s SUBSET t ==> s IN null_set m) /\
      !f. f IN (univ(:num) -> null_set m) ==>
          BIGUNION (IMAGE f univ(:num)) IN null_set m``,
    rpt GEN_TAC >> DISCH_TAC
 >> SIMP_TAC std_ss [IN_NULL_SET, null_set_def]
 >> CONJ_TAC >- (PROVE_TAC [MEASURE_SPACE_EMPTY_MEASURABLE, MEASURE_EMPTY])
 >> CONJ_TAC >- (rpt STRIP_TAC \\
                 Suff `measure m s <= measure m t`
                 >- (DISCH_TAC >> REWRITE_TAC [GSYM le_antisym] \\
                     CONJ_TAC >- PROVE_TAC [] \\
                     fs [measure_space_def, positive_def]) \\
                 MATCH_MP_TAC INCREASING >> art [] \\
                 IMP_RES_TAC MEASURE_SPACE_INCREASING)
 >> GEN_TAC >> REWRITE_TAC [IN_FUNSET, IN_UNIV, IN_NULL_SET, null_set_def]
 >> STRIP_TAC >> STRONG_CONJ_TAC
 >- (fs [measure_space_def, sigma_algebra_def, subsets_def] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     REWRITE_TAC [COUNTABLE_IMAGE_NUM] \\
     fs [SUBSET_DEF, IN_FUNSET, IN_UNIV, IN_NULL_SET, null_set_def] \\
     PROVE_TAC []) >> DISCH_TAC
 >> IMP_RES_TAC MEASURE_SPACE_COUNTABLY_SUBADDITIVE
 >> fs [countably_subadditive_def]
 >> Know `measure m (BIGUNION (IMAGE f univ(:num))) <= suminf (measure m o f)`
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> PROVE_TAC [IN_FUNSET, IN_UNIV]) >> DISCH_TAC
 >> Suff `suminf (measure m o f) = 0`
 >- (DISCH_TAC >> fs [] >> REWRITE_TAC [GSYM le_antisym] >> art [] \\
     fs [measure_space_def, positive_def])
 >> MATCH_MP_TAC ext_suminf_zero >> METIS_TAC [o_DEF]);

(* in complete measure space, the subset of a null set is still a null set. *)
val COMPLETE_MEASURE_THM = store_thm
  ("COMPLETE_MEASURE_THM",
  ``!m s t. complete_measure_space m /\ t IN null_set m /\ s SUBSET t ==> s IN null_set m``,
    RW_TAC std_ss [complete_measure_space_def]
 >> PROVE_TAC [NULL_SET_THM, IN_NULL_SET]);

(* ------------------------------------------------------------------------- *)
(*  Alternative definitions of `sigma_finite`                                *)
(* ------------------------------------------------------------------------- *)

(* The increasing sequence in "sigma_finite_def" is not required *)
val SIGMA_FINITE_ALT = store_thm
  ("SIGMA_FINITE_ALT",
  ``!m. measure_space m ==>
       (sigma_finite m <=> ?f :num -> 'a set.
                           f IN (UNIV -> measurable_sets m) /\
                           (BIGUNION (IMAGE f UNIV) = m_space m) /\
                           (!n. measure m (f n) < PosInf))``,
    GEN_TAC >> DISCH_TAC
 >> REWRITE_TAC [sigma_finite_def]
 >> EQ_TAC >> rpt STRIP_TAC
 >- (Q.EXISTS_TAC `f` >> art [])
 >> STRIP_ASSUME_TAC (Q.SPEC `f` SETS_TO_INCREASING_SETS)
 >> Q.EXISTS_TAC `g`
 >> fs [IN_FUNSET, IN_UNIV, measure_space_def]
 >> CONJ_TAC
 >- (GEN_TAC \\
     MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                (Q.SPEC `(m_space m,measurable_sets m)` ALGEBRA_FINITE_UNION)) \\
     CONJ_TAC >- fs [sigma_algebra_def] \\
     CONJ_TAC >- (MATCH_MP_TAC IMAGE_FINITE >> REWRITE_TAC [FINITE_COUNT]) \\
     RW_TAC arith_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT] >> art [])
 >> GEN_TAC
 >> MATCH_MP_TAC let_trans
 >> Q.EXISTS_TAC `SIGMA (measure m o f) (count (SUC n))`
 >> CONJ_TAC
 >- (MATCH_MP_TAC FINITE_SUBADDITIVE >> art [] \\
     CONJ_TAC >- (MATCH_MP_TAC ALGEBRA_PREMEASURE_FINITE_SUBADDITIVE \\
                  fs [sigma_algebra_def, premeasure_def]) \\
     MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                (Q.SPEC `(m_space m,measurable_sets m)` ALGEBRA_FINITE_UNION)) \\
     CONJ_TAC >- fs [sigma_algebra_def] \\
     CONJ_TAC >- (MATCH_MP_TAC IMAGE_FINITE >> REWRITE_TAC [FINITE_COUNT]) \\
     RW_TAC arith_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT] >> art [])
 >> REWRITE_TAC [GSYM lt_infty]
 >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF
 >> CONJ_TAC >- REWRITE_TAC [FINITE_COUNT]
 >> RW_TAC std_ss [o_DEF, lt_infty]);

(* this is the definition used by HVG's "lebesgue_measureTheory" *)
val SIGMA_FINITE_ALT2 = store_thm
  ("SIGMA_FINITE_ALT2",
  ``!m. measure_space m ==>
       (sigma_finite m <=> ?A. countable A /\ A SUBSET measurable_sets m /\
                              (BIGUNION A = m_space m) /\
                              (!a. a IN A ==> measure m a <> PosInf))``,
    GEN_TAC >> DISCH_TAC
 >> EQ_TAC >> rpt STRIP_TAC
 >- (fs [sigma_finite_def] \\
     Q.EXISTS_TAC `IMAGE f univ(:num)` >> art [] \\
     CONJ_TAC >- REWRITE_TAC [countable_image_nats] \\
     CONJ_TAC >- (RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV] \\
                  fs [IN_FUNSET, IN_UNIV]) \\
     RW_TAC std_ss [IN_IMAGE, lt_infty] >> art [])
 >> fs [COUNTABLE_ENUM]
 >| [ (* goal 1 (of 2) *)
      REWRITE_TAC [sigma_finite_def] \\
      Q.EXISTS_TAC `\n. {}` \\
      CONJ_TAC >- (RW_TAC std_ss [IN_FUNSET, IN_UNIV] \\
                   METIS_TAC [measure_space_def, sigma_algebra_def, ALGEBRA_EMPTY, ALGEBRA_SPACE,
                              space_def, subsets_def]) \\
      CONJ_TAC >- RW_TAC std_ss [SUBSET_REFL] \\
      CONJ_TAC >- (Suff `BIGUNION (IMAGE (\n. {}) univ(:num)) = BIGUNION {}` >- METIS_TAC [] \\
                   RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_BIGUNION, IN_UNIV,
                                  NOT_IN_EMPTY]) \\
      GEN_TAC >> BETA_TAC \\
      fs [measure_space_def, positive_def] \\
      REWRITE_TAC [extreal_of_num_def, lt_infty],
      (* goal 2 (of 2) *)
      RW_TAC std_ss [SIGMA_FINITE_ALT] \\
      Q.EXISTS_TAC `f` >> art [] \\
      CONJ_TAC >- (fs [IN_FUNSET, IN_UNIV, SUBSET_DEF, IN_IMAGE] \\
                   GEN_TAC >> FIRST_X_ASSUM MATCH_MP_TAC \\
                   Q.EXISTS_TAC `x` >> REWRITE_TAC []) \\
      GEN_TAC >> REWRITE_TAC [GSYM lt_infty] \\
      FIRST_X_ASSUM MATCH_MP_TAC \\
      REWRITE_TAC [IN_IMAGE, IN_UNIV] \\
      Q.EXISTS_TAC `n` >> REWRITE_TAC [] ]);

val _ = export_theory ();
val _ = html_theory "measure";

(* References:

  [1] Schilling, R.L.: Measures, Integrals and Martingales (Second Edition).
      Cambridge University Press (2017).
  [2] Mhamdi, T., Hasan, O., Tahar, S.: Formalization of Measure Theory and Lebesgue Integration
      for Probabilistic Analysis in HOL. ACM Trans. Embedded Comput. Syst. 12, 1--23 (2013).
  [4] Hurd, J.: Formal verification of probabilistic algorithms. University of Cambridge (2001).
  [5] Chung, K.L.: A Course in Probability Theory, Third Edition. Academic Press (2001).
  [6] Munroe, Marshall Evans: Introduction to measure and integration. Reading, Mass.: Addison-Wesley (1953).
  [7] Coble, A.R.: Anonymity, information, and machine-assisted proof. University of Cambridge (2010).
  [9] Wikipedia: https://en.wikipedia.org/wiki/Constantin_Carath%C3%A9odory
 *)
