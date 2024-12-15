(* ------------------------------------------------------------------------- *)
(* Useful Theorems, some are taken from various theories by Hurd and Coble   *)
(* Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar                         *)
(* HVG Group, Concordia University, Montreal                                 *)
(*                                                                           *)
(* Extended by Chun Tian (2019-2020)                                         *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open metisLib pairTheory combinTheory pred_setTheory pred_setLib jrhUtils
     arithmeticTheory numLib hurdUtils topologyTheory;

open realTheory realLib real_sigmaTheory iterateTheory;

val _ = new_theory "util_prob";

fun METIS ths tm = prove(tm, METIS_TAC ths);

(* ------------------------------------------------------------------------- *)

val _ = set_fixity "->" (Infixr 250);
val _ = overload_on ("->",
      ``FUNSET  :'a set -> 'b set -> ('a -> 'b) set``);

val _ = overload_on ("-->", (* "Pi" in Isabelle's FuncSet.thy *)
      ``DFUNSET :'a set -> ('a -> 'b set) -> ('a -> 'b) set``);

(* RIGHTWARDS ARROW *)
val _ = Unicode.unicode_version {u = UTF8.chr 0x2192, tmnm = "->"};

(* LONG RIGHTWARDS ARROW *)
val _ = Unicode.unicode_version {u = UTF8.chr 0x27F6, tmnm = "-->"};

val _ = TeX_notation {hol = "->",            TeX = ("\\HOLTokenMap{}", 1)};
val _ = TeX_notation {hol = UTF8.chr 0x2192, TeX = ("\\HOLTokenMap{}", 1)};
val _ = TeX_notation {hol = "-->",           TeX = ("\\HOLTokenLongmap{}", 1)};
val _ = TeX_notation {hol = UTF8.chr 0x27F6, TeX = ("\\HOLTokenLongmap{}", 1)};

Definition prod_sets_def :
    prod_sets a b = {s CROSS t | s IN a /\ t IN b}
End

Theorem IN_PROD_SETS[simp] :
    !s a b. s IN prod_sets a b <=> ?t u. (s = t CROSS u) /\ t IN a /\ u IN b
Proof
    RW_TAC std_ss [prod_sets_def, GSPECIFICATION, UNCURRY]
 >> EQ_TAC >- PROVE_TAC []
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC `(t,u)`
 >> RW_TAC std_ss []
QED

(********************************************************************************************)

Theorem finite_enumeration_of_sets_has_max_non_empty :
    !f s. FINITE s /\ (!x. f x IN s) /\
            (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
            ?N. !n:num. n >= N ==> (f n = {})
Proof
   `!s. FINITE s ==>
        (\s. !f. (!x. f x IN {} INSERT s) /\
                 (~({} IN s)) /\
                 (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
                 ?N. !n:num. n >= N ==> (f n = {})) s`
        by (MATCH_MP_TAC FINITE_INDUCT
            >> RW_TAC std_ss [NOT_IN_EMPTY, IN_INSERT]
            >> Q.PAT_X_ASSUM `!f. (!x. (f x = {}) \/ f x IN s) /\ ~({} IN s) /\
                                (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
                                ?N:num. !n. n >= N ==> (f n = {})`
                (MP_TAC o Q.SPEC `(\x. if f x = e then {} else f x)`)
            >> `(!x. ((\x. (if f x = e then {} else f x)) x = {}) \/
                     (\x. (if f x = e then {} else f x)) x IN s) /\ ~({} IN s)`
                by METIS_TAC []
            >> ASM_SIMP_TAC std_ss []
            >> `(!m n. ~(m = n) ==> DISJOINT (if f m = e then {} else f m)
                        (if f n = e then {} else f n))`
                by (RW_TAC std_ss [IN_DISJOINT, NOT_IN_EMPTY]
                            >> METIS_TAC [IN_DISJOINT])
            >> ASM_SIMP_TAC std_ss []
            >> RW_TAC std_ss []
            >> Cases_on `?n. f n = e`
            >- (FULL_SIMP_TAC std_ss []
                >> Cases_on `n < N`
                >- (Q.EXISTS_TAC `N`
                    >> RW_TAC std_ss [GREATER_EQ]
                    >> `~(n' = n)`
                        by METIS_TAC [LESS_LESS_EQ_TRANS,
                                      DECIDE ``!m (n:num). m < n ==> ~(m=n)``]
                    >> Cases_on `f n' = f n`
                    >- (`DISJOINT (f n') (f n)` by METIS_TAC []
                        >> FULL_SIMP_TAC std_ss [IN_DISJOINT, EXTENSION, NOT_IN_EMPTY]
                        >> METIS_TAC [])
                    >> Q.PAT_X_ASSUM
                                `!n'. n' >= N ==> ((if f n' = f n then {} else f n') = {})`
                                (MP_TAC o Q.SPEC `n'`)
                    >> ASM_SIMP_TAC std_ss [GREATER_EQ])
                >> Q.EXISTS_TAC `SUC n`
                >> RW_TAC std_ss [GREATER_EQ]
                >> FULL_SIMP_TAC std_ss [NOT_LESS]
                >> `~(n' = n)`
                        by METIS_TAC [LESS_LESS_EQ_TRANS,
                                      DECIDE ``!n:num. n < SUC n``,
                                      DECIDE ``!m (n:num). m < n ==> ~(m=n)``]
                >> Cases_on `f n' = f n`
                >- (`DISJOINT (f n') (f n)` by METIS_TAC []
                    >> FULL_SIMP_TAC std_ss [IN_DISJOINT, EXTENSION, NOT_IN_EMPTY]
                    >> METIS_TAC [])
                >> `N <= n'` by METIS_TAC [LESS_EQ_IMP_LESS_SUC,
                                           LESS_LESS_EQ_TRANS,
                                           LESS_IMP_LESS_OR_EQ]
                >> Q.PAT_X_ASSUM
                                `!n'. n' >= N ==> ((if f n' = f n then {} else f n') = {})`
                                (MP_TAC o Q.SPEC `n'`)
                >> ASM_SIMP_TAC std_ss [GREATER_EQ])
        >> METIS_TAC [])
   >> REPEAT STRIP_TAC
   >> Cases_on `{} IN s`
   >- (Q.PAT_X_ASSUM `!s. FINITE s ==> P` (MP_TAC o Q.SPEC `s DELETE {}`)
       >> RW_TAC std_ss [FINITE_DELETE, IN_INSERT, IN_DELETE])
   >> METIS_TAC [IN_INSERT]
QED

val PREIMAGE_REAL_COMPL1 = store_thm
  ("PREIMAGE_REAL_COMPL1", ``!c:real. COMPL {x | c < x} = {x | x <= c}``,
  RW_TAC real_ss [COMPL_DEF,UNIV_DEF,DIFF_DEF,EXTENSION]
  >> RW_TAC real_ss [GSPECIFICATION,GSYM real_lte,SPECIFICATION]);

val PREIMAGE_REAL_COMPL2 = store_thm
  ("PREIMAGE_REAL_COMPL2", ``!c:real. COMPL {x | c <= x} = {x | x < c}``,
  RW_TAC real_ss [COMPL_DEF,UNIV_DEF,DIFF_DEF,EXTENSION]
  >> RW_TAC real_ss [GSPECIFICATION,GSYM real_lt,SPECIFICATION]);

val PREIMAGE_REAL_COMPL3 = store_thm
  ("PREIMAGE_REAL_COMPL3", ``!c:real. COMPL {x | x <= c} = {x | c < x}``,
  RW_TAC real_ss [COMPL_DEF,UNIV_DEF,DIFF_DEF,EXTENSION]
  >> RW_TAC real_ss [GSPECIFICATION,GSYM real_lt,SPECIFICATION]);

val PREIMAGE_REAL_COMPL4 = store_thm
  ("PREIMAGE_REAL_COMPL4", ``!c:real. COMPL {x | x < c} = {x | c <= x}``,
  RW_TAC real_ss [COMPL_DEF,UNIV_DEF,DIFF_DEF,EXTENSION]
  >> RW_TAC real_ss [GSPECIFICATION,GSYM real_lte,SPECIFICATION]);

val GBIGUNION_IMAGE = store_thm
  ("GBIGUNION_IMAGE",
   ``!s p n. {s | ?n. p s n} = BIGUNION (IMAGE (\n. {s | p s n}) UNIV)``,
   RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION_IMAGE, IN_UNIV]);

Theorem DISJOINT_RESTRICT_L :
  !s t c. DISJOINT s t ==> DISJOINT (s INTER c) (t INTER c)
Proof SET_TAC []
QED

Theorem DISJOINT_RESTRICT_R :
  !s t c. DISJOINT s t ==> DISJOINT (c INTER s) (c INTER t)
Proof SET_TAC []
QED

Theorem DISJOINT_CROSS_L :
    !s t c. DISJOINT s t ==> DISJOINT (s CROSS c) (t CROSS c)
Proof
    RW_TAC std_ss [DISJOINT_ALT, CROSS_DEF, Once EXTENSION, IN_INTER,
                   NOT_IN_EMPTY, GSPECIFICATION]
QED

Theorem DISJOINT_CROSS_R :
    !s t c. DISJOINT s t ==> DISJOINT (c CROSS s) (c CROSS t)
Proof
    RW_TAC std_ss [DISJOINT_ALT, CROSS_DEF, Once EXTENSION, IN_INTER,
                   NOT_IN_EMPTY, GSPECIFICATION]
QED

Theorem SUBSET_RESTRICT_L :
  !r s t. s SUBSET t ==> (s INTER r) SUBSET (t INTER r)
Proof SET_TAC []
QED

Theorem SUBSET_RESTRICT_R :
  !r s t. s SUBSET t ==> (r INTER s) SUBSET (r INTER t)
Proof SET_TAC []
QED

Theorem SUBSET_RESTRICT_DIFF :
  !r s t. s SUBSET t ==> (r DIFF t) SUBSET (r DIFF s)
Proof SET_TAC []
QED

Theorem SUBSET_INTER_SUBSET_L :
  !r s t. s SUBSET t ==> (s INTER r) SUBSET t
Proof SET_TAC []
QED

Theorem SUBSET_INTER_SUBSET_R :
  !r s t. s SUBSET t ==> (r INTER s) SUBSET t
Proof SET_TAC []
QED

Theorem SUBSET_MONO_DIFF :
  !r s t. s SUBSET t ==> (s DIFF r) SUBSET (t DIFF r)
Proof SET_TAC []
QED

Theorem SUBSET_DIFF_SUBSET :
  !r s t. s SUBSET t ==> (s DIFF r) SUBSET t
Proof SET_TAC []
QED

Theorem SUBSET_DIFF_DISJOINT :
  !s1 s2 s3. (s1 SUBSET (s2 DIFF s3)) ==> DISJOINT s1 s3
Proof
    PROVE_TAC [SUBSET_DIFF]
QED

(* ------------------------------------------------------------------------- *)
(* Binary Unions                                                             *)
(* ------------------------------------------------------------------------- *)

Definition binary_def :
    binary a b = (\x:num. if x = 0 then a else b)
End

Theorem BINARY_RANGE : (* was: range_binary_eq *)
    !a b. IMAGE (binary a b) UNIV = {a;b}
Proof
  RW_TAC std_ss [IMAGE_DEF, binary_def] THEN
  SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, SET_RULE
   ``x IN {a;b} <=> (x = a) \/ (x = b)``] THEN
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
  [METIS_TAC [], METIS_TAC [IN_UNIV],
   EXISTS_TAC ``1:num`` THEN ASM_SIMP_TAC arith_ss [IN_UNIV]]
QED

Theorem UNION_BINARY : (* was: Un_range_binary *)
    !a b. a UNION b = BIGUNION {binary a b i | i IN UNIV}
Proof
  SIMP_TAC arith_ss [GSYM IMAGE_DEF] THEN
  REWRITE_TAC [METIS [ETA_AX] ``(\i. binary a b i) = binary a b``] THEN
  SIMP_TAC std_ss [BINARY_RANGE] THEN SET_TAC []
QED

Theorem INTER_BINARY : (* was: Int_range_binary *)
    !a b. a INTER b = BIGINTER {binary a b i | i IN UNIV}
Proof
  SIMP_TAC arith_ss [GSYM IMAGE_DEF] THEN
  REWRITE_TAC [METIS [ETA_AX] ``(\i. binary a b i) = binary a b``] THEN
  SIMP_TAC std_ss [BINARY_RANGE] THEN SET_TAC []
QED

Theorem FINITE_TWO :
    !s t. FINITE {s; t}
Proof
    PROVE_TAC [FINITE_INSERT, FINITE_SING]
QED

Theorem SUBSET_TWO :
    !N s t. N SUBSET {s; t} /\ N <> {} ==> N = {s} \/ N = {t} \/ N = {s; t}
Proof
    rpt GEN_TAC
 >> SET_TAC []
QED

(* ------------------------------------------------------------------------- *)
(*  Some lemmas needed by CARATHEODORY in measureTheory (author: Chun Tian)  *)
(* ------------------------------------------------------------------------- *)

val DINTER_IMP_FINITE_INTER = store_thm
  ("DINTER_IMP_FINITE_INTER",
  ``!sts f. (!s t. s IN sts /\ t IN sts ==> s INTER t IN sts) /\
            f IN (UNIV -> sts)
        ==> !n. 0 < n ==> BIGINTER (IMAGE f (count n)) IN sts``,
    rpt GEN_TAC
 >> STRIP_TAC
 >> Induct_on `n`
 >> RW_TAC arith_ss []
 >> fs [IN_FUNSET, IN_UNIV]
 >> STRIP_ASSUME_TAC (Q.SPEC `n` LESS_0_CASES)
 >- RW_TAC std_ss [COUNT_SUC, COUNT_ZERO, IMAGE_INSERT, IMAGE_EMPTY,
                   BIGINTER_INSERT, IMAGE_EMPTY, BIGINTER_EMPTY, INTER_UNIV]
 >> fs [COUNT_SUC]);

(* Dual lemma of above, used in "ring_and_semiring" *)
val DUNION_IMP_FINITE_UNION = store_thm
  ("DUNION_IMP_FINITE_UNION",
  ``!sts f. (!s t. s IN sts /\ t IN sts ==> s UNION t IN sts) ==>
            !n. 0 < n /\ (!i. i < n ==> f i IN sts) ==>
                BIGUNION (IMAGE f (count n)) IN sts``,
    rpt GEN_TAC
 >> STRIP_TAC
 >> Induct_on `n`
 >> RW_TAC arith_ss []
 >> fs [IN_FUNSET, IN_UNIV]
 >> STRIP_ASSUME_TAC (Q.SPEC `n` LESS_0_CASES)
 >- RW_TAC std_ss [COUNT_SUC, COUNT_ZERO, IMAGE_INSERT, IMAGE_EMPTY,
                   BIGUNION_INSERT, IMAGE_EMPTY, BIGUNION_EMPTY, UNION_EMPTY]
 >> fs [COUNT_SUC]);

val GEN_DIFF_INTER = store_thm
  ("GEN_DIFF_INTER",
  ``!sp s t. s SUBSET sp /\ t SUBSET sp ==> (s DIFF t = s INTER (sp DIFF t))``,
    rpt STRIP_TAC
 >> ASM_SET_TAC []);

val GEN_COMPL_UNION = store_thm
  ("GEN_COMPL_UNION",
  ``!sp s t. s SUBSET sp /\ t SUBSET sp ==>
             (sp DIFF (s UNION t) = (sp DIFF s) INTER (sp DIFF t))``,
    rpt STRIP_TAC
 >> ASM_SET_TAC [])

val GEN_COMPL_INTER = store_thm
  ("GEN_COMPL_INTER",
  ``!sp s t. s SUBSET sp /\ t SUBSET sp ==>
             (sp DIFF (s INTER t) = (sp DIFF s) UNION (sp DIFF t))``,
    rpt STRIP_TAC
 >> ASM_SET_TAC [])

val COMPL_BIGINTER_IMAGE = store_thm
  ("COMPL_BIGINTER_IMAGE",
  ``!f. COMPL (BIGINTER (IMAGE f univ(:num))) = BIGUNION (IMAGE (COMPL o f) univ(:num))``,
    RW_TAC std_ss [EXTENSION, IN_COMPL, IN_BIGINTER_IMAGE, IN_BIGUNION_IMAGE, IN_UNIV]);

val COMPL_BIGUNION_IMAGE = store_thm
  ("COMPL_BIGUNION_IMAGE",
  ``!f. COMPL (BIGUNION (IMAGE f univ(:num))) = BIGINTER (IMAGE (COMPL o f) univ(:num))``,
    RW_TAC std_ss [EXTENSION, IN_COMPL, IN_BIGINTER_IMAGE, IN_BIGUNION_IMAGE, IN_UNIV]);

val GEN_COMPL_BIGINTER_IMAGE = store_thm
  ("GEN_COMPL_BIGINTER_IMAGE",
  ``!sp f. (!n. f n SUBSET sp) ==>
           (sp DIFF (BIGINTER (IMAGE f univ(:num))) =
            BIGUNION (IMAGE (\n. sp DIFF (f n)) univ(:num)))``,
    RW_TAC std_ss [EXTENSION, IN_DIFF, IN_BIGINTER_IMAGE, IN_BIGUNION_IMAGE, IN_UNIV]
 >> EQ_TAC >> rpt STRIP_TAC >> art []
 >- (Q.EXISTS_TAC `y` >> art [])
 >> Q.EXISTS_TAC `n` >> art []);

val GEN_COMPL_BIGUNION_IMAGE = store_thm
  ("GEN_COMPL_BIGUNION_IMAGE",
  ``!sp f. (!n. f n SUBSET sp) ==>
           (sp DIFF (BIGUNION (IMAGE f univ(:num))) =
            BIGINTER (IMAGE (\n. sp DIFF (f n)) univ(:num)))``,
    RW_TAC std_ss [EXTENSION, IN_DIFF, IN_BIGINTER_IMAGE, IN_BIGUNION_IMAGE, IN_UNIV]
 >> EQ_TAC >> rpt STRIP_TAC >> art []
 >> METIS_TAC []);

val COMPL_BIGINTER = store_thm
  ("COMPL_BIGINTER",
  ``!c. COMPL (BIGINTER c) = BIGUNION (IMAGE COMPL c)``,
    RW_TAC std_ss [EXTENSION, IN_COMPL, IN_BIGINTER, IN_BIGUNION_IMAGE]);

val COMPL_BIGUNION = store_thm
  ("COMPL_BIGUNION",
  ``!c. c <> {} ==> (COMPL (BIGUNION c) = BIGINTER (IMAGE COMPL c))``,
    RW_TAC std_ss [NOT_IN_EMPTY, EXTENSION, IN_COMPL, IN_BIGUNION, IN_BIGINTER_IMAGE]
 >> EQ_TAC >> rpt STRIP_TAC
 >> PROVE_TAC []);

val GEN_COMPL_BIGINTER = store_thm
  ("GEN_COMPL_BIGINTER",
  ``!sp c. (!x. x IN c ==> x SUBSET sp) ==>
           (sp DIFF (BIGINTER c) = BIGUNION (IMAGE (\x. sp DIFF x) c))``,
    RW_TAC std_ss [EXTENSION, IN_DIFF, IN_BIGINTER, IN_BIGUNION_IMAGE]
 >> EQ_TAC >> rpt STRIP_TAC >> art []
 >- (Q.EXISTS_TAC `P` >> art [])
 >> Q.EXISTS_TAC `x'` >> art []);

val GEN_COMPL_BIGUNION = store_thm
  ("GEN_COMPL_BIGUNION",
  ``!sp c. c <> {} /\ (!x. x IN c ==> x SUBSET sp) ==>
           (sp DIFF (BIGUNION c) = BIGINTER (IMAGE (\x. sp DIFF x) c))``,
    RW_TAC std_ss [EXTENSION, IN_DIFF, IN_BIGINTER, IN_BIGUNION, IN_BIGINTER_IMAGE,
                   NOT_IN_EMPTY]
 >> EQ_TAC >> rpt STRIP_TAC >> art []
 >> METIS_TAC []);

val GEN_COMPL_FINITE_UNION = store_thm
  ("GEN_COMPL_FINITE_UNION",
  ``!sp f n. 0 < n ==> (sp DIFF BIGUNION (IMAGE f (count n)) =
                        BIGINTER (IMAGE (\i. sp DIFF f i) (count n)))``,
    NTAC 2 GEN_TAC
 >> Induct_on `n`
 >> RW_TAC arith_ss []
 >> STRIP_ASSUME_TAC (Q.SPEC `n` LESS_0_CASES)
 >- RW_TAC std_ss [COUNT_SUC, COUNT_ZERO, IMAGE_INSERT, IMAGE_EMPTY, BIGINTER_SING,
                   BIGUNION_INSERT, IMAGE_EMPTY, BIGUNION_EMPTY, UNION_EMPTY]
 >> fs [COUNT_SUC]
 >> ONCE_REWRITE_TAC [UNION_COMM]
 >> ASM_REWRITE_TAC [DIFF_UNION]
 >> REWRITE_TAC [DIFF_INTER]
 >> Suff `(BIGINTER (IMAGE (\i. sp DIFF f i) (count n)) DIFF f n) SUBSET sp`
 >- (KILL_TAC >> DISCH_THEN (ASSUME_TAC o (MATCH_MP SUBSET_INTER2)) >> ASM_SET_TAC [])
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC `BIGINTER (IMAGE (\i. sp DIFF f i) (count n))`
 >> REWRITE_TAC [DIFF_SUBSET]
 >> REWRITE_TAC [SUBSET_DEF, IN_BIGINTER_IMAGE, IN_COUNT] >> BETA_TAC
 >> RW_TAC std_ss [IN_DIFF]
 >> RES_TAC);

val BIGINTER_PAIR = store_thm
  ("BIGINTER_PAIR",
  ``!s t. BIGINTER {s; t} = s INTER t``,
    RW_TAC std_ss [EXTENSION, IN_BIGINTER, IN_INTER, IN_INSERT, NOT_IN_EMPTY]
 >> PROVE_TAC []);

val DIFF_INTER_PAIR = store_thm
  ("DIFF_INTER_PAIR",
  ``!sp x y. sp DIFF (x INTER y) = (sp DIFF x) UNION (sp DIFF y)``,
    rpt GEN_TAC
 >> REWRITE_TAC [REWRITE_RULE [BIGINTER_PAIR] (Q.SPECL [`sp`, `{x; y}`] DIFF_BIGINTER1)]
 >> REWRITE_TAC [EXTENSION, IN_UNION, IN_BIGUNION_IMAGE]
 >> BETA_TAC
 >> GEN_TAC >> EQ_TAC >> rpt STRIP_TAC
 >| [ fs [IN_INSERT] >> PROVE_TAC [],
      Q.EXISTS_TAC `x` >> ASM_REWRITE_TAC [IN_INSERT],
      Q.EXISTS_TAC `y` >> ASM_REWRITE_TAC [IN_INSERT] ]);

val GEN_COMPL_FINITE_INTER = store_thm
  ("GEN_COMPL_FINITE_INTER",
  ``!sp f n. 0 < n ==> (sp DIFF BIGINTER (IMAGE f (count n)) =
                        BIGUNION (IMAGE (\i. sp DIFF f i) (count n)))``,
    NTAC 2 GEN_TAC
 >> Induct_on `n`
 >> RW_TAC arith_ss []
 >> STRIP_ASSUME_TAC (Q.SPEC `n` LESS_0_CASES)
 >- RW_TAC std_ss [COUNT_SUC, COUNT_ZERO, IMAGE_INSERT, IMAGE_EMPTY, BIGINTER_SING,
                   BIGUNION_INSERT, IMAGE_EMPTY, BIGUNION_EMPTY, UNION_EMPTY]
 >> fs [COUNT_SUC]
 >> ASM_REWRITE_TAC [DIFF_INTER_PAIR]);

(* This proof is provided by Thomas Tuerk, needed by SETS_TO_DISJOINT_SETS *)
val BIGUNION_IMAGE_COUNT_IMP_UNIV = store_thm
  ("BIGUNION_IMAGE_COUNT_IMP_UNIV",
  ``!f g. (!n. BIGUNION (IMAGE g (count n)) = BIGUNION (IMAGE f (count n))) ==>
          (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE g UNIV))``,
 (* proof *)
   `!f g. (!n. BIGUNION (IMAGE g (count n)) = BIGUNION (IMAGE f (count n))) ==>
          (BIGUNION (IMAGE f UNIV) SUBSET BIGUNION (IMAGE g UNIV))`
       suffices_by PROVE_TAC [SUBSET_ANTISYM]
 >> REWRITE_TAC [SUBSET_DEF]
 >> REPEAT STRIP_TAC
 >> rename1 `e IN BIGUNION _`
 >> Know `?n. e IN BIGUNION (IMAGE f (count n))`
 >- (FULL_SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE, PULL_EXISTS, IN_COUNT] \\
     rename1 `e IN f n'` \\
     Q.EXISTS_TAC `SUC n'` \\
     Q.EXISTS_TAC `n'` \\
     ASM_SIMP_TAC arith_ss [])
 >> STRIP_TAC
 >> `e IN BIGUNION (IMAGE g (count n))` by PROVE_TAC []
 >> FULL_SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE, PULL_EXISTS, IN_UNIV]
 >> METIS_TAC []);

Theorem BIGUNION_OVER_INTER_L :
    !f s d. BIGUNION (IMAGE f s) INTER d = BIGUNION (IMAGE (\i. f i INTER d) s)
Proof
    rw [Once EXTENSION]
 >> EQ_TAC >> rw []
 >| [ (* goal 1 (of 3) *)
      rename1 ‘y IN s’ \\
      Q.EXISTS_TAC ‘f y INTER d’ >> rw [] \\
      Q.EXISTS_TAC ‘y’ >> rw [],
      (* goal 2 (of 3) *)
      fs [] \\
      Q.EXISTS_TAC ‘f i’ >> rw [] \\
      Q.EXISTS_TAC ‘i’ >> rw [],
      (* goal 3 (of 3) *)
      fs [] ]
QED

(* |- !f s d. d INTER BIGUNION (IMAGE f s) = BIGUNION (IMAGE (\i. d INTER f i) s) *)
Theorem BIGUNION_OVER_INTER_R = ONCE_REWRITE_RULE [INTER_COMM] BIGUNION_OVER_INTER_L

Theorem BIGUNION_OVER_DIFF :
    !f s d. BIGUNION (IMAGE f s) DIFF d = BIGUNION (IMAGE (\i. f i DIFF d) s)
Proof
    rw [Once EXTENSION]
 >> EQ_TAC >> rw []
 >| [ (* goal 1 (of 3) *)
      rename1 ‘y IN s’ \\
      Q.EXISTS_TAC ‘f y DIFF d’ >> rw [] \\
      Q.EXISTS_TAC ‘y’ >> rw [],
      (* goal 2 (of 3) *)
      fs [] \\
      Q.EXISTS_TAC ‘f i’ >> art [] \\
      Q.EXISTS_TAC ‘i’ >> art [],
      (* goal 3 (of 3) *)
      fs [] ]
QED

Theorem BIGINTER_OVER_INTER_L :
    !f s d. s <> {} ==> (BIGINTER (IMAGE f s) INTER d =
                         BIGINTER (IMAGE (\i. f i INTER d) s))
Proof
    rpt STRIP_TAC
 >> rw [Once EXTENSION]
 >> EQ_TAC >> rw []
 >| [ (* goal 1 (of 3) *)
      rw [] >> FIRST_X_ASSUM MATCH_MP_TAC \\
      Q.EXISTS_TAC ‘i’ >> rw [],
      (* goal 2 (of 3) *)
      rename1 ‘y IN s’ \\
      Suff ‘x IN (f y INTER d)’ >- rw [] \\
      FIRST_X_ASSUM MATCH_MP_TAC \\
      Q.EXISTS_TAC ‘y’ >> rw [],
      (* goal 3 (of 3) *)
      fs [GSYM MEMBER_NOT_EMPTY] \\
      rename1 ‘i IN s’ \\
      Suff ‘x IN f i INTER d’ >- rw [] \\
      FIRST_X_ASSUM MATCH_MP_TAC \\
      Q.EXISTS_TAC ‘i’ >> rw [] ]
QED

(* |- !f s d. s <> {} ==>
              d INTER BIGINTER (IMAGE f s) = BIGINTER (IMAGE (\i. d INTER f i) s)
 *)
Theorem BIGINTER_OVER_INTER_R = ONCE_REWRITE_RULE [INTER_COMM] BIGINTER_OVER_INTER_L

(* any finite set can be decomposed into a finite sequence of sets *)
val finite_decomposition_simple = store_thm (* new *)
  ("finite_decomposition_simple",
  ``!c. FINITE c ==> ?f n. (!x. x < n ==> f x IN c) /\ (c = IMAGE f (count n))``,
    GEN_TAC
 >> REWRITE_TAC [FINITE_BIJ_COUNT_EQ]
 >> rpt STRIP_TAC
 >> rename1 `BIJ f (count n) c`
 >> Q.EXISTS_TAC `f`
 >> Q.EXISTS_TAC `n`
 >> CONJ_TAC >- (rpt STRIP_TAC >> PROVE_TAC [BIJ_DEF, INJ_DEF, IN_COUNT])
 >> PROVE_TAC [BIJ_IMAGE]);

(* any finite set can be decomposed into a finite (non-repeated) sequence of sets *)
Theorem finite_decomposition :
    !c. FINITE c ==>
        ?f n. (!x. x < n ==> f x IN c) /\ (c = IMAGE f (count n)) /\
              (!i j. i < n /\ j < n /\ i <> j ==> f i <> f j)
Proof
    GEN_TAC
 >> REWRITE_TAC [FINITE_BIJ_COUNT_EQ]
 >> rpt STRIP_TAC
 >> rename1 `BIJ f (count n) c`
 >> Q.EXISTS_TAC `f`
 >> Q.EXISTS_TAC `n`
 >> CONJ_TAC >- (rpt STRIP_TAC >> PROVE_TAC [BIJ_DEF, INJ_DEF, IN_COUNT])
 >> CONJ_TAC >- PROVE_TAC [BIJ_IMAGE]
 >> rpt STRIP_TAC
 >> fs [BIJ_ALT, IN_FUNSET, IN_COUNT]
 >> METIS_TAC []
QED

(* any finite disjoint set can be decomposed into a finite pair-wise
   disjoint sequence of sets *)
Theorem finite_disjoint_decomposition :
    !c. FINITE c /\ disjoint c ==>
        ?f n. (!i. i < n ==> f i IN c) /\ (c = IMAGE f (count n)) /\
              (!i j. i < n /\ j < n /\ i <> j ==> f i <> f j) /\
              (!i j. i < n /\ j < n /\ i <> j ==> DISJOINT (f i) (f j))
Proof
    GEN_TAC
 >> REWRITE_TAC [FINITE_BIJ_COUNT_EQ]
 >> rpt STRIP_TAC
 >> rename1 `BIJ f (count n) c`
 >> Q.EXISTS_TAC `f`
 >> Q.EXISTS_TAC `n`
 >> STRONG_CONJ_TAC
 >- (rpt STRIP_TAC >> PROVE_TAC [BIJ_DEF, INJ_DEF, IN_COUNT])
 >> DISCH_TAC
 >> CONJ_TAC >- PROVE_TAC [BIJ_IMAGE]
 >> STRONG_CONJ_TAC
 >- (rpt STRIP_TAC \\
     fs [BIJ_ALT, IN_FUNSET, IN_COUNT] >> METIS_TAC [])
 >> rpt STRIP_TAC
 >> fs [disjoint_def]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> METIS_TAC []
QED

(* cf. cardinalTheory. disjoint_countable_decomposition *)
Theorem finite_disjoint_decomposition' :
    !c. FINITE c /\ disjoint c ==>
        ?f n. (!i. i < n ==> f i IN c) /\ (!i. n <= i ==> (f i = {})) /\
              (c = IMAGE f (count n)) /\
              (BIGUNION c = BIGUNION (IMAGE f univ(:num))) /\
              (!i j. i < n /\ j < n /\ i <> j ==> f i <> f j) /\
              (!i j. i < n /\ j < n /\ i <> j ==> DISJOINT (f i) (f j))
Proof
    rpt STRIP_TAC
 >> STRIP_ASSUME_TAC
        (MATCH_MP finite_disjoint_decomposition
                  (CONJ (ASSUME ``FINITE (c :'a set set)``)
                        (ASSUME ``disjoint (c :'a set set)``)))
 >> Q.EXISTS_TAC `\i. if i < n then f i else {}`
 >> Q.EXISTS_TAC `n`
 >> BETA_TAC
 >> CONJ_TAC >- METIS_TAC []
 >> CONJ_TAC >- METIS_TAC [NOT_LESS]
 >> CONJ_TAC
 >- (art [] >> MATCH_MP_TAC IMAGE_CONG >> RW_TAC std_ss [IN_COUNT])
 >> reverse CONJ_TAC >- METIS_TAC []
 >> art [] >> KILL_TAC
 >> SIMP_TAC std_ss [Once EXTENSION, IN_BIGUNION_IMAGE, IN_COUNT, IN_UNIV]
 >> GEN_TAC >> EQ_TAC >> rpt STRIP_TAC
 >| [ Q.EXISTS_TAC `x'` >> METIS_TAC [],
      Cases_on `i < n` >- (Q.EXISTS_TAC `i` >> METIS_TAC []) \\
      fs [NOT_IN_EMPTY] ]
QED

(* any union of two sets can be decomposed into 3 disjoint unions *)
val UNION_TO_3_DISJOINT_UNIONS = store_thm (* new *)
  ("UNION_TO_3_DISJOINT_UNIONS",
  ``!s t. (s UNION t = (s DIFF t) UNION (s INTER t) UNION (t DIFF s)) /\
          disjoint {(s DIFF t); (s INTER t); (t DIFF s)}``,
    NTAC 2 GEN_TAC
 >> CONJ_TAC >- SET_TAC []
 >> REWRITE_TAC [disjoint_def, DISJOINT_DEF]
 >> RW_TAC std_ss [IN_INSERT]
 >> ASM_SET_TAC []);

val BIGUNION_IMAGE_BIGUNION_IMAGE_UNIV = store_thm
  ("BIGUNION_IMAGE_BIGUNION_IMAGE_UNIV",
  ``!f. BIGUNION (IMAGE (\n. BIGUNION (IMAGE (f n) univ(:num))) univ(:num)) =
        BIGUNION (IMAGE (UNCURRY f) univ(:num # num))``,
    GEN_TAC
 >> RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, IN_CROSS, UNCURRY]
 >> EQ_TAC >> STRIP_TAC
 >- (Q.EXISTS_TAC `(n, x')` >> art [FST, SND])
 >> Q.EXISTS_TAC `FST x'`
 >> Q.EXISTS_TAC `SND x'` >> art []);

val BIGUNION_IMAGE_UNIV_CROSS_UNIV = store_thm
  ("BIGUNION_IMAGE_UNIV_CROSS_UNIV",
  ``!f (h :num -> num # num). BIJ h UNIV (UNIV CROSS UNIV) ==>
       (BIGUNION (IMAGE (UNCURRY f) univ(:num # num)) =
        BIGUNION (IMAGE (UNCURRY f o h) univ(:num)))``,
    rpt STRIP_TAC
 >> RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, IN_CROSS, UNCURRY, o_DEF]
 >> fs [BIJ_ALT, IN_FUNSET, IN_UNIV]
 >> EQ_TAC >> STRIP_TAC
 >- (Q.PAT_X_ASSUM `!y. ?!x. y = h x` (MP_TAC o (Q.SPEC `x'`)) >> METIS_TAC [])
 >> Q.EXISTS_TAC `h x'` >> art []);

(* ------------------------------------------------------------------------- *)
(*  Three series of lemmas on bigunion-equivalent sequences of sets          *)
(* ------------------------------------------------------------------------- *)

(* 1. for any sequence of sets, there is an increasing sequence of the same bigunion. *)
val SETS_TO_INCREASING_SETS = store_thm
  ("SETS_TO_INCREASING_SETS",
  ``!f :num->'a set.
       ?g. (g 0 = f 0) /\ (!n. g n = BIGUNION (IMAGE f (count (SUC n)))) /\
           (!n. g n SUBSET g (SUC n)) /\
           (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE g UNIV))``,
    rpt STRIP_TAC
 >> Q.EXISTS_TAC `\n. BIGUNION (IMAGE f (count (SUC n)))`
 >> BETA_TAC
 >> RW_TAC bool_ss []
 >| [ (* goal 1 (of 3) *)
      REWRITE_TAC [COUNT_SUC, COUNT_ZERO, IMAGE_SING, BIGUNION_SING],
      (* goal 2 (of 3) *)
     `count (SUC (SUC n)) = (SUC n) INSERT (count (SUC n))`
          by PROVE_TAC [COUNT_SUC] >> POP_ORW \\
      REWRITE_TAC [IMAGE_INSERT, BIGUNION_INSERT] \\
      REWRITE_TAC [SUBSET_UNION],
      (* goal 3 (of 3) *)
      MATCH_MP_TAC BIGUNION_IMAGE_COUNT_IMP_UNIV \\
      Induct_on `n` >- REWRITE_TAC [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY] \\
     `count (SUC n) = n INSERT (count n)` by PROVE_TAC [COUNT_SUC] \\
      POP_ORW >> REWRITE_TAC [IMAGE_INSERT, BIGUNION_INSERT] \\
      POP_ASSUM (REWRITE_TAC o wrap) \\
      BETA_TAC \\
      Cases_on `n = 0` >> fs [COUNT_SUC, COUNT_ZERO, IMAGE_SING, BIGUNION_SING] \\
      REWRITE_TAC [GSYM UNION_ASSOC, UNION_IDEMPOT] ]);

(* another version with `g 0 = {}` *)
val SETS_TO_INCREASING_SETS' = store_thm
  ("SETS_TO_INCREASING_SETS'",
  ``!f :num -> 'a set.
       ?g. (g 0 = {}) /\ (!n. g n = BIGUNION (IMAGE f (count n))) /\
           (!n. g n SUBSET g (SUC n)) /\
           (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE g UNIV))``,
    rpt STRIP_TAC
 >> Q.EXISTS_TAC `\n. BIGUNION (IMAGE f (count n))`
 >> BETA_TAC
 >> RW_TAC bool_ss []
 >| [ (* goal 1 (of 3) *)
      REWRITE_TAC [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY],
      (* goal 2 (of 3) *)
     `count (SUC n) = n INSERT (count n)` by PROVE_TAC [COUNT_SUC] \\
      POP_ORW >> REWRITE_TAC [IMAGE_INSERT, BIGUNION_INSERT] \\
      REWRITE_TAC [SUBSET_UNION],
      (* goal 3 (of 3) *)
      REWRITE_TAC [EXTENSION] \\
      GEN_TAC >> SIMP_TAC std_ss [IN_BIGUNION_IMAGE, IN_UNIV, IN_COUNT] \\
      EQ_TAC >> RW_TAC std_ss [] >|
      [ Q.EXISTS_TAC `SUC x'` \\
        Q.EXISTS_TAC `x'` >> ASM_SIMP_TAC arith_ss [],
        Q.EXISTS_TAC `x'` >> art [] ] ]);

(* 2. (hard) for any sequence of sets in a space, there is a disjoint family with
      the same bigunion. This lemma is needed by DYNKIN_LEMMA *)
val SETS_TO_DISJOINT_SETS = store_thm
  ("SETS_TO_DISJOINT_SETS",
  ``!sp sts f. (!s. s IN sts ==> s SUBSET sp) /\ (!n. f n IN sts) ==>
       ?g. (g 0 = f 0) /\
           (!n. 0 < n ==> (g n = f n INTER (BIGINTER (IMAGE (\i. sp DIFF f i) (count n))))) /\
           (!i j :num. i <> j ==> DISJOINT (g i) (g j)) /\
           (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE g UNIV))``,
    rpt STRIP_TAC
 >> Q.EXISTS_TAC `\n. if n = 0:num then f n
                      else f n INTER (BIGINTER (IMAGE (\i. sp DIFF f i) (count n)))`
 >> BETA_TAC >> SIMP_TAC arith_ss []
 >> CONJ_TAC >> RW_TAC arith_ss []
 >| [ (* goal 1 (of 4)
        `DISJOINT (f 0) (f j INTER BIGINTER (IMAGE (\i. sp DIFF f i) (count j)))` *)
      `0 IN (count j)` by PROVE_TAC [NOT_ZERO_LT_ZERO, IN_COUNT] \\
      POP_ASSUM (MP_TAC o SYM o (MATCH_MP INSERT_DELETE)) \\
      DISCH_THEN (ONCE_REWRITE_TAC o wrap) \\
      REWRITE_TAC [IMAGE_INSERT, BIGINTER_INSERT] >> BETA_TAC \\
      REWRITE_TAC [INTER_ASSOC] \\
      `f j INTER (sp DIFF f 0) = (sp DIFF f 0) INTER f j` by PROVE_TAC [INTER_COMM] \\
      POP_ASSUM (ONCE_REWRITE_TAC o wrap) \\
      REWRITE_TAC [DIFF_INTER, DISJOINT_DIFF],
      (* goal 2 (of 4),
        `DISJOINT (f i INTER BIGINTER (IMAGE (\i. sp DIFF f i) (count i))) (f 0)` *)
     `0 IN (count i)` by PROVE_TAC [NOT_ZERO_LT_ZERO, IN_COUNT] \\
      POP_ASSUM (MP_TAC o SYM o (MATCH_MP INSERT_DELETE)) \\
      DISCH_THEN (ONCE_REWRITE_TAC o wrap) \\
      REWRITE_TAC [IMAGE_INSERT, BIGINTER_INSERT] >> BETA_TAC \\
      REWRITE_TAC [INTER_ASSOC] \\
     `f i INTER (sp DIFF f 0) = (sp DIFF f 0) INTER f i` by PROVE_TAC [INTER_COMM] \\
      POP_ASSUM (ONCE_REWRITE_TAC o wrap) \\
      REWRITE_TAC [DIFF_INTER, DISJOINT_DIFF],
      (* goal 3 (of 4),
        `DISJOINT (f i INTER BIGINTER (IMAGE (\i. sp DIFF f i) (count i)))
                  (f j INTER BIGINTER (IMAGE (\i. sp DIFF f i) (count j)))` *)
      STRIP_ASSUME_TAC (Q.SPECL [`i`, `j`] LESS_LESS_CASES) >| (* 2 subgoals *)
      [ (* goal 3.1 (of 2) *)
        ONCE_REWRITE_TAC [DISJOINT_SYM] \\
        MATCH_MP_TAC DISJOINT_SUBSET \\
        Q.EXISTS_TAC `f i` >> REWRITE_TAC [INTER_SUBSET] \\
       `i IN (count j)` by PROVE_TAC [IN_COUNT] \\
        POP_ASSUM (MP_TAC o SYM o (MATCH_MP INSERT_DELETE)) \\
        DISCH_THEN (ONCE_REWRITE_TAC o wrap) \\
        REWRITE_TAC [IMAGE_INSERT, BIGINTER_INSERT] >> BETA_TAC \\
        REWRITE_TAC [INTER_ASSOC] \\
       `f j INTER (sp DIFF f i) = (sp DIFF f i) INTER f j` by PROVE_TAC [INTER_COMM] \\
        POP_ASSUM (ONCE_REWRITE_TAC o wrap) \\
        REWRITE_TAC [DIFF_INTER, DISJOINT_DIFF],
        (* goal 3.2 (of 2) *)
        MATCH_MP_TAC DISJOINT_SUBSET \\
        Q.EXISTS_TAC `f j` >> REWRITE_TAC [INTER_SUBSET] \\
       `j IN (count i)` by PROVE_TAC [IN_COUNT] \\
        POP_ASSUM (MP_TAC o SYM o (MATCH_MP INSERT_DELETE)) \\
        DISCH_THEN (ONCE_REWRITE_TAC o wrap) \\
        REWRITE_TAC [IMAGE_INSERT, BIGINTER_INSERT] >> BETA_TAC \\
        REWRITE_TAC [INTER_ASSOC] \\
       `f i INTER (sp DIFF f j) = (sp DIFF f j) INTER f i` by PROVE_TAC [INTER_COMM] \\
        POP_ASSUM (ONCE_REWRITE_TAC o wrap) \\
        REWRITE_TAC [DIFF_INTER, DISJOINT_DIFF] ],
      (* goal 4 (of 4) *)
      MATCH_MP_TAC BIGUNION_IMAGE_COUNT_IMP_UNIV \\
      Induct_on `n` >- REWRITE_TAC [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY] \\
      REWRITE_TAC [COUNT_SUC, IMAGE_INSERT, BIGUNION_INSERT] \\
      POP_ASSUM (REWRITE_TAC o wrap) >> BETA_TAC \\
      Cases_on `n = 0` >> fs [] (* now ``n <> 0`` *) \\
      REWRITE_TAC [Once UNION_COMM, INTER_OVER_UNION] \\
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [UNION_COMM] \\
      Suff `BIGUNION (IMAGE f (count n)) UNION (BIGINTER (IMAGE (\i. sp DIFF f i) (count n))) = sp`
      >- (DISCH_THEN (REWRITE_TAC o wrap) \\
          REWRITE_TAC [INTER_SUBSET_EQN, UNION_SUBSET] \\
          reverse CONJ_TAC >- PROVE_TAC [] \\
          REWRITE_TAC [BIGUNION_SUBSET, IN_IMAGE] >> PROVE_TAC []) \\
      (* BIGUNION (IMAGE f (count n)) UNION BIGINTER (IMAGE (\i. sp DIFF f i) (count n)) = sp *)
     `0 < n` by PROVE_TAC [NOT_ZERO_LT_ZERO] \\
      POP_ASSUM (REWRITE_TAC o wrap o GSYM o (MATCH_MP GEN_COMPL_FINITE_UNION)) \\
      Suff `BIGUNION (IMAGE f (count n)) SUBSET sp` >- ASM_SET_TAC [] \\
      REWRITE_TAC [BIGUNION_SUBSET, IN_IMAGE] >> PROVE_TAC [] ]);

(* A specific version without sts and sp *)
val SETS_TO_DISJOINT_SETS' = store_thm
  ("SETS_TO_DISJOINT_SETS'",
  ``!f. ?g. (g 0 = f 0) /\
            (!n. 0 < n ==> (g n = f n INTER (BIGINTER (IMAGE (COMPL o f) (count n))))) /\
            (!i j :num. i <> j ==> DISJOINT (g i) (g j)) /\
            (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE g UNIV))``,
    GEN_TAC
 >> STRIP_ASSUME_TAC (Q.SPECL [`UNIV`, `UNIV`, `f`] SETS_TO_DISJOINT_SETS)
 >> fs [SUBSET_UNIV, o_DEF, COMPL_DEF]
 >> Q.EXISTS_TAC `g` >> art []);

(* 3. (hard) for any sequence of (straightly) increasing sets, there is a disjoint
      family with the same bigunion. *)
val INCREASING_TO_DISJOINT_SETS = store_thm
  ("INCREASING_TO_DISJOINT_SETS",
  ``!f :num -> 'a set. (!n. f n SUBSET f (SUC n)) ==>
       ?g. (g 0 = f 0) /\ (!n. 0 < n ==> (g n = f n DIFF f (PRE n))) /\
           (!i j :num. i <> j ==> DISJOINT (g i) (g j)) /\
           (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE g UNIV))``,
    rpt STRIP_TAC
 >> Q.EXISTS_TAC `\n. if n = (0 :num) then f n else f n DIFF f (PRE n)`
 >> BETA_TAC
 (* preliminaries *)
 >> Know `!n. 0 < n ==> f 0 SUBSET (f n)`
 >- (Induct_on `n` >- RW_TAC arith_ss [] \\
     RW_TAC arith_ss [] \\
     Cases_on `n = 0` >- art [] \\
     IMP_RES_TAC NOT_ZERO_LT_ZERO >> RES_TAC \\
     MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC `f n` >> art [])
 >> DISCH_TAC
 >> Know `!n. 0 < n ==> f 0 SUBSET (f (PRE n))`
 >- (Induct_on `n` >- RW_TAC arith_ss [] \\
     RW_TAC arith_ss [] \\
     Cases_on `n = 0` >- art [SUBSET_REFL] \\
     IMP_RES_TAC NOT_ZERO_LT_ZERO >> RES_TAC)
 >> DISCH_TAC
 >> Know `!i j. i < j ==> f (SUC i) SUBSET (f j)`
 >- (GEN_TAC >> Induct_on `j` >- RW_TAC arith_ss [] \\
     STRIP_TAC \\
     fs [GSYM LESS_EQ_IFF_LESS_SUC, LESS_OR_EQ] \\
     MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC `f j` \\
     CONJ_TAC >- RES_TAC >> art [])
 >> DISCH_TAC
 >> Know `!n. 0 < n ==> f (PRE n) SUBSET f n`
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM `!n. f n SUBSET f (SUC n)` (STRIP_ASSUME_TAC o (Q.SPEC `PRE n`)) \\
     PROVE_TAC [SUC_PRE])
 >> DISCH_TAC
 >> Know `!i j. i < j ==> f i SUBSET f (PRE j)`
 >- (GEN_TAC >> Induct_on `j` >- RW_TAC arith_ss [] \\
     STRIP_TAC \\
     fs [GSYM LESS_EQ_IFF_LESS_SUC, LESS_OR_EQ] \\
     MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC `f (PRE j)` \\
     CONJ_TAC >- RES_TAC \\
     Cases_on `j = 0` >- (RW_TAC arith_ss [SUBSET_REFL]) \\
     IMP_RES_TAC NOT_ZERO_LT_ZERO >> RES_TAC)
 >> DISCH_TAC
 >> RW_TAC arith_ss []
 >| [ (* goal 1 (of 4): DISJOINT (f 0) (f (SUC j) DIFF f j) *)
      MATCH_MP_TAC SUBSET_DIFF_DISJOINT \\
      Q.EXISTS_TAC `f j` \\
      IMP_RES_TAC NOT_ZERO_LT_ZERO \\
     `f j DIFF (f j DIFF f (PRE j)) = f (PRE j)`
          by PROVE_TAC [DIFF_DIFF_SUBSET] >> POP_ORW >> RES_TAC,
      (* goal 2 (of 4): DISJOINT (f (SUC i) DIFF f i) (f 0) *)
      ONCE_REWRITE_TAC [DISJOINT_SYM] \\
      MATCH_MP_TAC SUBSET_DIFF_DISJOINT \\
      Q.EXISTS_TAC `f i` \\
      IMP_RES_TAC NOT_ZERO_LT_ZERO \\
     `f i DIFF (f i DIFF f (PRE i)) = f (PRE i)`
          by PROVE_TAC [DIFF_DIFF_SUBSET] >> POP_ORW \\
      IMP_RES_TAC NOT_ZERO_LT_ZERO >> RES_TAC,
      (* goal 3 (of 4): DISJOINT (f (SUC i) DIFF f i) (f (SUC j) DIFF f j) *)
      STRIP_ASSUME_TAC (Q.SPECL [`i`, `j`] LESS_LESS_CASES) >| (* 2 subgoals *)
      [ (* goal 3.1 (of 2) *)
        ONCE_REWRITE_TAC [DISJOINT_SYM] \\
        MATCH_MP_TAC DISJOINT_SUBSET \\
        Q.EXISTS_TAC `f i` >> REWRITE_TAC [DIFF_SUBSET] \\
        ONCE_REWRITE_TAC [DISJOINT_SYM] \\
        MATCH_MP_TAC SUBSET_DIFF_DISJOINT \\
        Q.EXISTS_TAC `f j` \\
        IMP_RES_TAC NOT_ZERO_LT_ZERO \\
       `f j DIFF (f j DIFF f (PRE j)) = f (PRE j)`
          by PROVE_TAC [DIFF_DIFF_SUBSET] >> POP_ORW >> RES_TAC,
        (* goal 3.2 (of 2) *)
        MATCH_MP_TAC DISJOINT_SUBSET \\
        Q.EXISTS_TAC `f j` >> REWRITE_TAC [DIFF_SUBSET] \\
        ONCE_REWRITE_TAC [DISJOINT_SYM] \\
        MATCH_MP_TAC SUBSET_DIFF_DISJOINT \\
        Q.EXISTS_TAC `f i` \\
        IMP_RES_TAC NOT_ZERO_LT_ZERO \\
       `f i DIFF (f i DIFF f (PRE i)) = f (PRE i)`
          by PROVE_TAC [DIFF_DIFF_SUBSET] >> POP_ORW >> RES_TAC ],
      (* goal 4 (of 4): BIGUNION (IMAGE f univ(:num)) = ... *)
      MATCH_MP_TAC BIGUNION_IMAGE_COUNT_IMP_UNIV \\
      Induct_on `n` >- REWRITE_TAC [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY] \\
      REWRITE_TAC [COUNT_SUC, IMAGE_INSERT, BIGUNION_INSERT] \\
      POP_ASSUM (REWRITE_TAC o wrap) >> BETA_TAC \\
      Cases_on `n = 0` >> fs [] (* now ``n <> 0`` *) \\
      RW_TAC arith_ss [EXTENSION, IN_UNION, IN_BIGUNION_IMAGE, IN_COUNT, IN_DIFF] \\
      EQ_TAC >> rpt STRIP_TAC >| (* 4 subgoals *)
      [ DISJ1_TAC >> art [],
        DISJ2_TAC >> Q.EXISTS_TAC `x'` >> art [],
        Cases_on `x IN f (PRE n)` >- (DISJ2_TAC >> Q.EXISTS_TAC `PRE n` \\
                                      ASM_SIMP_TAC arith_ss []) \\
        DISJ1_TAC >> art [],
        DISJ2_TAC >> Q.EXISTS_TAC `x'` >> art [] ] ]);

(* Surprisingly, this variant of INCREASING_TO_DISJOINT_SETS cannot be
   easily proved without using the non-trivial SETS_TO_DISJOINT_SETS *)
val INCREASING_TO_DISJOINT_SETS' = store_thm
  ("INCREASING_TO_DISJOINT_SETS'",
  ``!f :num -> 'a set. (f 0 = {}) /\ (!n. f n SUBSET f (SUC n)) ==>
       ?g. (!n. g n = f (SUC n) DIFF f n) /\
           (!i j :num. i <> j ==> DISJOINT (g i) (g j)) /\
           (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE g UNIV))``,
    rpt STRIP_TAC
 >> Q.EXISTS_TAC `\n. f (SUC n) DIFF f n`
 >> BETA_TAC
 (* preliminaries *)
 >> Know `!i j. i < j ==> f i SUBSET f j`
 >- (GEN_TAC >> Induct_on `j` >- RW_TAC arith_ss [] \\
     STRIP_TAC \\
     MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC `f j` >> art [] \\
     fs [GSYM LESS_EQ_IFF_LESS_SUC, LESS_OR_EQ])
 >> DISCH_TAC
 >> Know `!i j. i < j ==> f (SUC i) SUBSET f j`
 >- (GEN_TAC >> Induct_on `j` >- RW_TAC arith_ss [] \\
     STRIP_TAC \\
     Cases_on `i = j` >- PROVE_TAC [SUBSET_REFL] \\
     MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC `f j` >> art [] \\
     fs [GSYM LESS_EQ_IFF_LESS_SUC, LESS_OR_EQ])
 >> DISCH_TAC
 >> RW_TAC arith_ss [] (* 2 subgoals *)
 >| [ (* goal 1 (of 2): DISJOINT (f (SUC i) DIFF f i) (f (SUC j) DIFF f j) *)
      STRIP_ASSUME_TAC (Q.SPECL [`i`, `j`] LESS_LESS_CASES) >| (* 2 subgoals *)
      [ (* goal 1.1 (of 2) *)
        ONCE_REWRITE_TAC [DISJOINT_SYM] \\
        MATCH_MP_TAC DISJOINT_SUBSET \\
        Q.EXISTS_TAC `f (SUC i)` >> REWRITE_TAC [DIFF_SUBSET] \\
        ONCE_REWRITE_TAC [DISJOINT_SYM] \\
        MATCH_MP_TAC SUBSET_DIFF_DISJOINT \\
        Q.EXISTS_TAC `f (SUC j)` \\
        `f (SUC j) DIFF (f (SUC j) DIFF f j) = f j`
          by PROVE_TAC [DIFF_DIFF_SUBSET] >> POP_ORW >> RES_TAC,
        (* goal 1.2 (of 2) *)
        MATCH_MP_TAC DISJOINT_SUBSET \\
        Q.EXISTS_TAC `f (SUC j)` >> REWRITE_TAC [DIFF_SUBSET] \\
        ONCE_REWRITE_TAC [DISJOINT_SYM] \\
        MATCH_MP_TAC SUBSET_DIFF_DISJOINT \\
        Q.EXISTS_TAC `f (SUC i)` \\
       `f (SUC i) DIFF (f (SUC i) DIFF f i) = f i`
          by PROVE_TAC [DIFF_DIFF_SUBSET] >> POP_ORW >> RES_TAC ],
      (* goal 2 (of 2): BIGUNION (IMAGE f univ(:num)) = ... *)
      STRIP_ASSUME_TAC (Q.SPEC `f` SETS_TO_DISJOINT_SETS') >> art [] \\
      RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, IN_DIFF] \\
      EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
      [ (* goal 2.1 (of 2) *)
        Cases_on `x' = 0` >- PROVE_TAC [NOT_IN_EMPTY] \\
        IMP_RES_TAC NOT_ZERO_LT_ZERO \\
        Q.EXISTS_TAC `PRE x'` \\
       `SUC (PRE x') = x'` by PROVE_TAC [SUC_PRE] >> POP_ORW \\
        Q.PAT_X_ASSUM `x IN g x'` MP_TAC \\
        Q.PAT_X_ASSUM `!n. 0 < n ==> X`
            (fn th => REWRITE_TAC [MATCH_MP th (ASSUME ``0:num < x'``)]) \\
        RW_TAC std_ss [IN_INTER, IN_BIGINTER_IMAGE, IN_COUNT, o_DEF, IN_COMPL] \\
        FIRST_X_ASSUM MATCH_MP_TAC >> RW_TAC arith_ss [],
        (* goal 2.2 (of 2) *)
        Q.EXISTS_TAC `SUC n` \\
       `0 < SUC n` by REWRITE_TAC [prim_recTheory.LESS_0] \\
        Q.PAT_X_ASSUM `!n. 0 < n ==> X`
            (fn th => REWRITE_TAC [MATCH_MP th (ASSUME ``0:num < SUC n``)]) \\
        RW_TAC std_ss [IN_INTER, IN_BIGINTER_IMAGE, IN_COUNT, o_DEF, IN_COMPL] \\
        fs [GSYM LESS_EQ_IFF_LESS_SUC, LESS_OR_EQ] \\
        CCONTR_TAC >> fs [] \\
       `x IN f n` by PROVE_TAC [SUBSET_DEF] ] ]);

(* ------------------------------------------------------------------------- *)
(* Other types of disjointness definitions (from Concordia HVG)              *)
(* ------------------------------------------------------------------------- *)

(* This is not more general than disjoint_def *)
Definition disjoint_family_on :
    disjoint_family_on a s =
      (!m n. m IN s /\ n IN s /\ (m <> n) ==> (a m INTER a n = {}))
End

(* A new, equivalent definition based on DISJOINT *)
Theorem disjoint_family_on_def :
    !A J. disjoint_family_on A (J :'index set) <=>
         (!i j. i IN J /\ j IN J /\ (i <> j) ==> DISJOINT (A i) (A j))
Proof
    rw [DISJOINT_DEF, disjoint_family_on]
QED

Overload disjoint_family = “\A. disjoint_family_on A UNIV”

(* A new, equivalent definition based on DISJOINT *)
Theorem disjoint_family_def :
    !A. disjoint_family (A :'index -> 'a set) <=>
        !i j. i <> j ==> DISJOINT (A i) (A j)
Proof
    rw [disjoint_family_on_def]
QED

(* This is the way to convert a family of sets into a disjoint family
   of sets, cf. SETS_TO_DISJOINT_SETS -- Chun Tian
 *)
Definition disjointed :
    disjointed A n = A n DIFF BIGUNION {A i | i IN {x:num | 0 <= x /\ x < n}}
End

val disjointed_subset = store_thm ("disjointed_subset",
  ``!A n. disjointed A n SUBSET A n``,
  RW_TAC std_ss [disjointed] THEN ASM_SET_TAC []);

Theorem disjoint_family_disjoint :
    !A. disjoint_family (disjointed A)
Proof
  SIMP_TAC std_ss [disjoint_family_on, IN_UNIV] THEN
  RW_TAC std_ss [disjointed, EXTENSION, GSPECIFICATION, IN_INTER] THEN
  SIMP_TAC std_ss [NOT_IN_EMPTY, IN_DIFF, IN_BIGUNION] THEN
  ASM_CASES_TAC ``(x NOTIN A (m:num) \/ ?s. x IN s /\ s IN {A i | i < m})`` THEN
  ASM_REWRITE_TAC [] THEN RW_TAC std_ss [] THEN
  ASM_CASES_TAC ``x NOTIN A (n:num)`` THEN FULL_SIMP_TAC std_ss [] THEN
  FULL_SIMP_TAC std_ss [GSPECIFICATION] THEN
  ASM_CASES_TAC ``m < n:num`` THENL [METIS_TAC [], ALL_TAC] THEN
  `n < m:num` by ASM_SIMP_TAC arith_ss [] THEN METIS_TAC []
QED

val finite_UN_disjointed_eq = prove (
  ``!A n. BIGUNION {disjointed A i | i IN {x | 0 <= x /\ x < n}} =
          BIGUNION {A i | i IN {x | 0 <= x /\ x < n}}``,
  GEN_TAC THEN INDUCT_TAC THENL
  [FULL_SIMP_TAC real_ss [GSPECIFICATION] THEN SET_TAC [], ALL_TAC] THEN
  FULL_SIMP_TAC real_ss [GSPECIFICATION] THEN
  GEN_REWR_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [ARITH_PROVE ``i < SUC n <=> i < n \/ (i = n)``] THEN
  REWRITE_TAC [SET_RULE ``BIGUNION {(A:num->'a->bool) i | i < n \/ (i = n)} =
                          BIGUNION {A i | i < n} UNION A n``] THEN
  ASM_REWRITE_TAC [disjointed] THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
  SIMP_TAC std_ss [UNION_DEF] THEN
  REWRITE_TAC [ARITH_PROVE ``i < SUC n <=> i < n \/ (i = n)``] THEN
  REWRITE_TAC [SET_RULE ``BIGUNION {(A:num->'a->bool) i | i < n \/ (i = n)} =
                          BIGUNION {A i | i < n} UNION A n``] THEN
  SET_TAC []);

val atLeast0LessThan = prove (
  ``{x:num | 0 <= x /\ x < n} = {x | x < n}``,
  SIMP_TAC arith_ss [EXTENSION, GSPECIFICATION]);

val UN_UN_finite_eq = prove (
  ``!A.
     BIGUNION {BIGUNION {A i | i IN {x | 0 <= x /\ x < n}} | n IN univ(:num)} =
     BIGUNION {A n | n IN UNIV}``,
  SIMP_TAC std_ss [atLeast0LessThan] THEN
  RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION, IN_UNIV] THEN
  EQ_TAC THEN RW_TAC std_ss [] THENL
  [POP_ASSUM (MP_TAC o Q.SPEC `x`) THEN ASM_REWRITE_TAC [] THEN
   RW_TAC std_ss [] THEN METIS_TAC [], ALL_TAC] THEN
  Q.EXISTS_TAC `BIGUNION {A i | i IN {x | 0 <= x /\ x < SUC n}}` THEN
  RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION, IN_UNIV] THENL
  [ALL_TAC, METIS_TAC []] THEN Q.EXISTS_TAC `A n` THEN
  FULL_SIMP_TAC std_ss [] THEN Q.EXISTS_TAC `n` THEN
  SIMP_TAC arith_ss []);

val UN_finite_subset = prove (
  ``!A C. (!n. BIGUNION {A i | i IN {x | 0 <= x /\ x < n}} SUBSET C) ==>
               BIGUNION {A n | n IN univ(:num)} SUBSET C``,
  RW_TAC std_ss [] THEN ONCE_REWRITE_TAC [GSYM UN_UN_finite_eq] THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF] THEN RW_TAC std_ss [] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FULL_SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION, IN_UNIV] THEN
  POP_ASSUM (MP_TAC o Q.SPEC `x`) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
  Q.EXISTS_TAC `n` THEN Q.EXISTS_TAC `s'` THEN METIS_TAC []);

val UN_finite2_subset = prove (
  ``!A B n k.
    (!n. BIGUNION {A i | i IN {x | 0 <= x /\ x < n}} SUBSET
         BIGUNION {B i | i IN {x | 0 <= x /\ x < n + k}}) ==>
         BIGUNION {A n | n IN univ(:num)} SUBSET BIGUNION {B n | n IN univ(:num)}``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC UN_finite_subset THEN
  ONCE_REWRITE_TAC [GSYM UN_UN_finite_eq] THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, GSPECIFICATION, IN_UNIV] THEN
  RW_TAC std_ss [] THEN FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`x`]) THEN
  Q_TAC SUFF_TAC `(?s. x IN s /\ ?i. (s = A i) /\ i < n)` THENL
  [ALL_TAC, METIS_TAC []] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN Q.EXISTS_TAC `BIGUNION {B i | i < n + k}` THEN
  CONJ_TAC THENL [ALL_TAC, METIS_TAC []] THEN
  SIMP_TAC std_ss [IN_BIGUNION, GSPECIFICATION] THEN METIS_TAC []);

val UN_finite2_eq = prove (
  ``!A B k.
    (!n. BIGUNION {A i | i IN {x | 0 <= x /\ x < n}} =
         BIGUNION {B i | i IN {x | 0 <= x /\ x < n + k}}) ==>
    (BIGUNION {A n | n IN univ(:num)} = BIGUNION {B n | n IN univ(:num)})``,
  RW_TAC std_ss [] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
  [MATCH_MP_TAC  UN_finite2_subset THEN REWRITE_TAC [atLeast0LessThan] THEN
   METIS_TAC [SUBSET_REFL], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_UNIV, GSPECIFICATION] THEN
  RW_TAC std_ss [] THEN FIRST_X_ASSUM (MP_TAC o Q.SPEC `SUC n`) THEN
  GEN_REWR_TAC LAND_CONV [EXTENSION] THEN
  DISCH_THEN (MP_TAC o Q.SPEC `x`) THEN
  SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_UNIV, GSPECIFICATION] THEN
  Q_TAC SUFF_TAC `?s. x IN s /\ ?i. (s = B i) /\ i < SUC n + k` THENL
  [ALL_TAC,
   Q.EXISTS_TAC `B n` THEN ASM_REWRITE_TAC [] THEN
   Q.EXISTS_TAC `n` THEN SIMP_TAC arith_ss []] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC [] THEN RW_TAC std_ss [] THEN
  METIS_TAC []);

Theorem BIGUNION_disjointed : (* was: UN_disjointed_eq *)
    !A. BIGUNION {disjointed A i | i IN UNIV} = BIGUNION {A i | i IN UNIV}
Proof
  GEN_TAC THEN MATCH_MP_TAC UN_finite2_eq THEN
  Q.EXISTS_TAC `0` THEN RW_TAC arith_ss [GSPECIFICATION] THEN
  ASSUME_TAC finite_UN_disjointed_eq THEN
  FULL_SIMP_TAC arith_ss [GSPECIFICATION]
QED

(******************************************************************************)
(*  liminf and limsup [1, p.74] [2, p.76] - the set-theoretic version         *)
(******************************************************************************)

val set_ss' = arith_ss ++ PRED_SET_ss;

(* This lemma is provided by Konrad Slind *)
val lemma = Q.prove
  (`!P. ~(?N. INFINITE N /\ !n. N n ==> P n) <=> !N. N SUBSET P ==> FINITE N`,
  rw_tac set_ss' [EQ_IMP_THM, SUBSET_DEF, IN_DEF]
  >- (`FINITE P \/ ?n. P n /\ ~P n` by metis_tac []
       >> imp_res_tac SUBSET_FINITE
       >> full_simp_tac std_ss [SUBSET_DEF, IN_DEF])
  >- metis_tac[]);

(* "From this and the original assumption, you should be able to get that P is finite,
    so has a maximum element." -- Konrad Slind, Feb 17, 2019.
 *)
Theorem infinitely_often_lemma :
    !P. ~(?N. INFINITE N /\ !n:num. n IN N ==> P n) <=> ?m. !n. m <= n ==> ~(P n)
Proof
    Q.X_GEN_TAC ‘P’
 >> `!N. (!n. n IN N ==> P n) <=> !n. N n ==> P n` by PROVE_TAC [SUBSET_DEF, IN_APP]
 >> POP_ORW
 >> REWRITE_TAC [lemma]
 >> reverse EQ_TAC >> rpt STRIP_TAC
 >| [ (* goal 1 (of 2) *)
      Suff ‘FINITE P’ >- PROVE_TAC [SUBSET_FINITE_I] \\
      Know ‘P SUBSET (count m)’
      >- (REWRITE_TAC [count_def, GSYM NOT_LESS_EQUAL] \\
          ASM_SET_TAC []) \\
      DISCH_TAC \\
      MATCH_MP_TAC SUBSET_FINITE_I \\
      Q.EXISTS_TAC ‘count m’ >> art [FINITE_COUNT],
      (* goal 2 (of 2) *)
      POP_ASSUM (MP_TAC o (Q.SPEC `P`)) \\
      RW_TAC std_ss [SUBSET_REFL] \\
      Cases_on ‘P = {}’ >- rw [] \\
      MP_TAC (FINITE_is_measure_maximal |> INST_TYPE [“:'a” |-> “:num”]
                                        |> Q.SPECL [‘I’, ‘P’]) \\
      rw [is_measure_maximal_def, IN_APP] \\
      Q.EXISTS_TAC ‘SUC x’ >> rw [] \\
      CCONTR_TAC >> fs [] \\
     ‘x < n’ by rw [] \\
     ‘n <= x’ by PROVE_TAC [] \\
      METIS_TAC [LESS_EQ_ANTISYM] ]
QED

(* This proof is provided by Konrad Slind. *)
Theorem infinity_bound_lemma :
    !N m. INFINITE N ==> ?n:num. m <= n /\ n IN N
Proof
    spose_not_then strip_assume_tac
 >> `FINITE (count m)` by metis_tac [FINITE_COUNT]
 >> `N SUBSET (count m)`
      by (rw_tac set_ss' [SUBSET_DEF]
           >> `~(m <= x)` by metis_tac []
           >> decide_tac)
 >> metis_tac [SUBSET_FINITE]
QED

(* TODO: restate this lemma by real_topologyTheory.from *)
val tail_not_empty = store_thm
  ("tail_not_empty", ``!A m:num. {A n | m <= n} <> {}``,
    RW_TAC std_ss [Once EXTENSION, NOT_IN_EMPTY, GSPECIFICATION]
 >> Q.EXISTS_TAC `(SUC m)` >> RW_TAC arith_ss []);

val tail_countable = store_thm
  ("tail_countable", ``!A m:num. countable {A n | m <= n}``,
    rpt GEN_TAC
 >> Suff `{A n | m <= n} = IMAGE A {n | m <= n}`
 >- PROVE_TAC [COUNTABLE_IMAGE_NUM]
 >> RW_TAC std_ss [EXTENSION, IN_IMAGE, GSPECIFICATION]);

val set_limsup_def = Define (* "infinitely often" *)
   `set_limsup (E :num -> 'a set) =
      BIGINTER (IMAGE (\m. BIGUNION {E n | m <= n}) UNIV)`;

val set_liminf_def = Define (* "almost always" *)
   `set_liminf (E :num -> 'a set) =
      BIGUNION (IMAGE (\m. BIGINTER {E n | m <= n}) UNIV)`;

val _ = overload_on ("limsup", ``set_limsup``);
val _ = overload_on ("liminf", ``set_liminf``);

(* alternative definition of `limsup` using `from` *)
val set_limsup_alt = store_thm
  ("set_limsup_alt",
  ``!E. set_limsup E = BIGINTER (IMAGE (\n. BIGUNION (IMAGE E (from n))) UNIV)``,
    GEN_TAC >> REWRITE_TAC [set_limsup_def]
 >> Suff `!m. BIGUNION (IMAGE E (from m)) = BIGUNION {E n | m <= n}`
 >- (Rewr' >> REWRITE_TAC [])
 >> RW_TAC std_ss [Once EXTENSION, IN_BIGUNION_IMAGE, IN_BIGUNION, GSPECIFICATION, from_def]
 >> EQ_TAC >> rpt STRIP_TAC
 >- (Q.EXISTS_TAC `E x'` >> art [] \\
     Q.EXISTS_TAC `x'` >> art [])
 >> Q.EXISTS_TAC `n` >> PROVE_TAC []);

Theorem LIMSUP_COMPL : (* was: liminf_limsup *)
    !(E :num -> 'a set). COMPL (liminf E) = limsup (COMPL o E)
Proof
    RW_TAC std_ss [set_limsup_def, set_liminf_def]
 >> SIMP_TAC std_ss [COMPL_BIGUNION_IMAGE, o_DEF]
 >> Suff `!m. COMPL (BIGINTER {E n | m <= n}) = BIGUNION {COMPL (E n) | m <= n}` >- Rewr
 >> GEN_TAC >> REWRITE_TAC [COMPL_BIGINTER]
 >> Suff `IMAGE COMPL {E n | m <= n} = {COMPL (E n) | m <= n}` >- Rewr
 >> SIMP_TAC std_ss [IMAGE_DEF, IN_COMPL, Once GSPECIFICATION]
 >> RW_TAC std_ss [Once EXTENSION, GSPECIFICATION, IN_COMPL]
 >> EQ_TAC >> rpt STRIP_TAC
 >- (fs [COMPL_COMPL] >> Q.EXISTS_TAC `n` >> art [])
 >> fs []
 >> Q.EXISTS_TAC `E n` >> art []
 >> Q.EXISTS_TAC `n` >> art []
QED

Theorem LIMSUP_DIFF : (* was: liminf_limsup_sp *)
    !sp E. (!n. E n SUBSET sp) ==> (sp DIFF (liminf E) = limsup (\n. sp DIFF (E n)))
Proof
    RW_TAC std_ss [set_limsup_def, set_liminf_def]
 >> Q.ABBREV_TAC `f = (\m. BIGINTER {E n | m <= n})`
 >> Know `!m. f m SUBSET sp`
 >- (GEN_TAC >> Q.UNABBREV_TAC `f` >> BETA_TAC \\
     RW_TAC std_ss [SUBSET_DEF, IN_BIGINTER, GSPECIFICATION] \\
     fs [SUBSET_DEF] >> LAST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC `SUC m` \\
     POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPEC `E (SUC m)`)) \\
     POP_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC `SUC m` >> RW_TAC arith_ss [])
 >> DISCH_THEN (REWRITE_TAC o wrap o (MATCH_MP GEN_COMPL_BIGUNION_IMAGE))
 >> Suff `!m. sp DIFF f m = BIGUNION {sp DIFF E n | m <= n}` >- Rewr
 >> GEN_TAC >> Q.UNABBREV_TAC `f` >> BETA_TAC
 >> Know `!x. x IN {E n | m <= n} ==> x SUBSET sp`
 >- (RW_TAC std_ss [GSPECIFICATION] >> art [])
 >> DISCH_THEN (REWRITE_TAC o wrap o (MATCH_MP GEN_COMPL_BIGINTER))
 >> Suff `(IMAGE (\x. sp DIFF x) {E n | m <= n}) = {sp DIFF E n | m <= n}` >- Rewr
 >> RW_TAC std_ss [Once EXTENSION, IMAGE_DEF, IN_DIFF, GSPECIFICATION]
 >> EQ_TAC >> rpt STRIP_TAC
 >- (Q.EXISTS_TAC `n` >> METIS_TAC [])
 >> Q.EXISTS_TAC `E n` >> art []
 >> Q.EXISTS_TAC `n` >> art []
QED

(* A point belongs to `limsup E` if and only if it belongs to infinitely
   many terms of the sequence E. [2, p.76]
 *)
Theorem IN_LIMSUP :
    !A x. x IN limsup A <=> ?N. INFINITE N /\ !n. n IN N ==> x IN (A n)
Proof
    rpt GEN_TAC >> EQ_TAC
 >> RW_TAC std_ss [set_limsup_def, IN_BIGINTER_IMAGE, IN_UNIV]
 >| [ (* goal 1 (of 2) *)
      Q.ABBREV_TAC `P = \n. x IN (A n)` \\
     `!n. x IN (A n) <=> P n` by PROVE_TAC [] >> POP_ORW \\
      CCONTR_TAC \\
     `?m. !n. m <= n ==> ~(P n)` by PROVE_TAC [infinitely_often_lemma] \\
      Q.UNABBREV_TAC `P` >> FULL_SIMP_TAC bool_ss [] \\
      Know `x NOTIN BIGUNION {A n | m <= n}`
      >- (SIMP_TAC std_ss [IN_BIGUNION, GSPECIFICATION] \\
          CCONTR_TAC >> FULL_SIMP_TAC bool_ss [] >> METIS_TAC []) \\
      DISCH_TAC >> METIS_TAC [],
      (* goal 2 (of 2) *)
      SIMP_TAC std_ss [IN_BIGUNION, GSPECIFICATION] \\
      IMP_RES_TAC infinity_bound_lemma \\
      POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPEC `m`)) \\
      Q.EXISTS_TAC `A n` >> CONJ_TAC >- PROVE_TAC [] \\
      Q.EXISTS_TAC `n` >> art [] ]
QED

(* A point belongs to `liminf E` if and only if it belongs to all terms
   of the sequence from a certain term on. [2, p.76]
 *)
Theorem IN_LIMINF :
    !A x. x IN liminf A <=> ?m. !n. m <= n ==> x IN (A n)
Proof
    rpt GEN_TAC
 >> ASSUME_TAC (SIMP_RULE std_ss [GSYM LIMSUP_COMPL, IN_COMPL, o_DEF]
                                 (Q.SPECL [`COMPL o A`, `x`] IN_LIMSUP))
 >> `x IN liminf A <=> ~(?N. INFINITE N /\ !n. n IN N ==> x NOTIN A n)` by PROVE_TAC []
 >> fs [infinitely_often_lemma]
QED

(* This version of LIMSUP_MONO is used in large_numberTheory.SLLN_IID_diverge *)
Theorem LIMSUP_MONO_STRONGER :
    !A B. (?d. !y n. y IN A n ==> ?m. n - d <= m /\ y IN B m) ==> limsup A SUBSET limsup B
Proof
    RW_TAC std_ss [set_limsup_alt]
 >> RW_TAC std_ss [IN_BIGINTER_IMAGE, IN_BIGUNION_IMAGE, SUBSET_DEF, IN_UNIV, IN_FROM]
 >> POP_ASSUM ((Q.X_CHOOSE_THEN ‘N’ STRIP_ASSUME_TAC) o (Q.SPEC ‘d + n’))
 >> Q.PAT_X_ASSUM ‘!y n. y IN A n ==> _’ (MP_TAC o (Q.SPECL [‘x’, ‘N’]))
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC ‘m’
 >> FULL_SIMP_TAC arith_ss []
QED

Theorem LIMSUP_MONO_STRONG :
    !A B. (!y n. y IN A n ==> ?m. n <= m /\ y IN B m) ==> limsup A SUBSET limsup B
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC LIMSUP_MONO_STRONGER
 >> Q.EXISTS_TAC ‘0’ >> rw []
QED

Theorem LIMSUP_MONO_WEAK :
    !A B. (!n. A n SUBSET B n) ==> limsup A SUBSET limsup B
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC LIMSUP_MONO_STRONG
 >> qx_genl_tac [‘x’, ‘n’]
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss [SUBSET_DEF]
 >> Q.EXISTS_TAC ‘n’ >> fs []
QED

(* ‘count1 n’ (inclusive ‘count’) returns the set of integers from 0 to n *)
Overload count1 = “\n. count (SUC n)”;

(* A fake definition in case a user wants to check its definition by guess *)
Theorem count1_def :
    !n. count1 n = {m | m <= n}
Proof
    rw [Once EXTENSION, LT_SUC_LE]
QED

(* ‘count n’ re-expressed by numseg *)
Theorem count1_numseg :
    !n. count1 n = {0..n}
Proof
    rw [Once EXTENSION]
QED

val _ = export_theory ();

(* References:

  [1] Schilling, R.L.: Measures, Integrals and Martingales. Cambridge University Press (2005).
  [2] Chung, K.L.: A Course in Probability Theory, Third Edition. Academic Press (2001).

 *)
