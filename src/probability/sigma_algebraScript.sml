(* ------------------------------------------------------------------------- *)
(* The (shared) theory of sigma-algebra and other systems of sets (ring,     *)
(* semiring, and dynkin system) used in measureTheory/real_measureTheory     *)
(*                                                                           *)
(* Author: Chun Tian (2018 - 2025)                                           *)
(* ------------------------------------------------------------------------- *)
(* Based on the work of Tarek Mhamdi, Osman Hasan, Sofiene Tahar [3]         *)
(* HVG Group, Concordia University, Montreal (2013, 2015)                    *)
(*                                                                           *)
(* With some further additions by M. Qasim & W. Ahmed (2019)                 *)
(* ------------------------------------------------------------------------- *)
(* Based on the work of Joe Hurd [1] (2001) and Aaron Coble [2] (2010)       *)
(* Cambridge University.                                                     *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory optionTheory pairTheory combinTheory pred_setTheory
     pred_setLib numLib topologyTheory hurdUtils jrhUtils res_quanTools
     iterateTheory prim_recTheory;

val _ = new_theory "sigma_algebra";

val DISC_RW_KILL = DISCH_TAC >> ONCE_ASM_REWRITE_TAC [] >> POP_ASSUM K_TAC;
fun METIS ths tm = prove(tm, METIS_TAC ths);
val set_ss = std_ss ++ PRED_SET_ss;
val std_ss' = std_ss ++ boolSimps.ETA_ss;
val S_TAC = rpt (POP_ASSUM MP_TAC) >> rpt RESQ_STRIP_TAC;
val Strip = S_TAC;

val _ = hide "S";

(* ------------------------------------------------------------------------- *)

val _ = set_fixity "->" (Infixr 250);
Overload "->"  = “FUNSET :'a set -> 'b set -> ('a -> 'b) set”

(* NOTE: this is "Pi" in Isabelle's FuncSet.thy *)
Overload "-->" = “DFUNSET :'a set -> ('a -> 'b set) -> ('a -> 'b) set”

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

Theorem finite_enumeration_of_sets_has_max_non_empty :
    !f s. FINITE s /\ (!x. f x IN s) /\
         (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
          ?N. !(n :num). n >= N ==> (f n = {})
Proof
    Suff
    `!s. FINITE s ==>
        (\s. !f. (!x. f x IN {} INSERT s) /\
                 (~({} IN s)) /\
                 (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
                 ?N. !n:num. n >= N ==> (f n = {})) s`
 >- (rpt STRIP_TAC \\
     Cases_on `{} IN s`
     >- (Q.PAT_X_ASSUM `!s. FINITE s ==> P` (MP_TAC o Q.SPEC `s DELETE {}`) \\
         RW_TAC std_ss [FINITE_DELETE, IN_INSERT, IN_DELETE]) \\
     METIS_TAC [IN_INSERT])
 >> MATCH_MP_TAC FINITE_INDUCT
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
       by (RW_TAC std_ss [IN_DISJOINT, NOT_IN_EMPTY] \\
           METIS_TAC [IN_DISJOINT])
 >> ASM_SIMP_TAC std_ss []
 >> RW_TAC std_ss []
 >> Cases_on `?n. f n = e`
 >- (FULL_SIMP_TAC std_ss [] \\
     Cases_on `n < N`
     >- (Q.EXISTS_TAC `N` \\
         RW_TAC std_ss [GREATER_EQ] \\
        `~(n' = n)` by METIS_TAC [LESS_LESS_EQ_TRANS,
                                  DECIDE ``!m (n:num). m < n ==> ~(m=n)``] \\
         Cases_on `f n' = f n`
         >- (`DISJOINT (f n') (f n)` by METIS_TAC [] \\
             FULL_SIMP_TAC std_ss [IN_DISJOINT, EXTENSION, NOT_IN_EMPTY] \\
             METIS_TAC []) \\
         Q.PAT_X_ASSUM `!n'. n' >= N ==> ((if f n' = f n then {} else f n') = {})`
                       (MP_TAC o Q.SPEC `n'`) \\
         ASM_SIMP_TAC std_ss [GREATER_EQ]) \\
     Q.EXISTS_TAC `SUC n` \\
     RW_TAC std_ss [GREATER_EQ] \\
     FULL_SIMP_TAC std_ss [NOT_LESS] \\
    `~(n' = n)` by METIS_TAC [LESS_LESS_EQ_TRANS, DECIDE ``!n:num. n < SUC n``,
                              DECIDE ``!m (n:num). m < n ==> ~(m=n)``] \\
     Cases_on `f n' = f n`
     >- (`DISJOINT (f n') (f n)` by METIS_TAC [] \\
         FULL_SIMP_TAC std_ss [IN_DISJOINT, EXTENSION, NOT_IN_EMPTY] \\
         METIS_TAC []) \\
    `N <= n'` by METIS_TAC [LESS_EQ_IMP_LESS_SUC, LESS_LESS_EQ_TRANS,
                            LESS_IMP_LESS_OR_EQ] \\
     Q.PAT_X_ASSUM `!n'. n' >= N ==> ((if f n' = f n then {} else f n') = {})`
       (MP_TAC o Q.SPEC `n'`) \\
     ASM_SIMP_TAC std_ss [GREATER_EQ])
 >> METIS_TAC []
QED

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
    rpt GEN_TAC >> SET_TAC []
QED

(* ------------------------------------------------------------------------- *)
(*  Some lemmas needed by CARATHEODORY in measureTheory                      *)
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

Theorem COMPL_BIGINTER_IMAGE :
    !f. COMPL (BIGINTER (IMAGE f univ(:num))) =
        BIGUNION (IMAGE (COMPL o f) univ(:num))
Proof
    RW_TAC std_ss [EXTENSION, IN_COMPL, IN_BIGINTER_IMAGE,
                   IN_BIGUNION_IMAGE, IN_UNIV]
QED

Theorem COMPL_BIGUNION_IMAGE :
    !f. COMPL (BIGUNION (IMAGE f univ(:num))) =
        BIGINTER (IMAGE (COMPL o f) univ(:num))
Proof
    RW_TAC std_ss [EXTENSION, IN_COMPL, IN_BIGINTER_IMAGE,
                   IN_BIGUNION_IMAGE, IN_UNIV]
QED

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

Theorem GEN_COMPL_FINITE_UNION :
    !sp f n. 0 < n ==> sp DIFF BIGUNION (IMAGE f (count n)) =
                       BIGINTER (IMAGE (\i. sp DIFF f i) (count n))
Proof
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
 >- (KILL_TAC \\
     DISCH_THEN (ASSUME_TAC o (MATCH_MP SUBSET_INTER2)) >> ASM_SET_TAC [])
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC `BIGINTER (IMAGE (\i. sp DIFF f i) (count n))`
 >> REWRITE_TAC [DIFF_SUBSET]
 >> REWRITE_TAC [SUBSET_DEF, IN_BIGINTER_IMAGE, IN_COUNT] >> BETA_TAC
 >> RW_TAC std_ss [IN_DIFF]
 >> PROVE_TAC []
QED

val BIGINTER_PAIR = store_thm
  ("BIGINTER_PAIR",
  ``!s t. BIGINTER {s; t} = s INTER t``,
    RW_TAC std_ss [EXTENSION, IN_BIGINTER, IN_INTER, IN_INSERT, NOT_IN_EMPTY]
 >> PROVE_TAC []);

Theorem DIFF_INTER_PAIR :
    !sp x y. sp DIFF (x INTER y) = (sp DIFF x) UNION (sp DIFF y)
Proof
    rpt GEN_TAC
 >> REWRITE_TAC [REWRITE_RULE [BIGINTER_PAIR]
                              (Q.SPECL [`sp`, `{x; y}`] DIFF_BIGINTER1)]
 >> REWRITE_TAC [EXTENSION, IN_UNION, IN_BIGUNION_IMAGE]
 >> BETA_TAC
 >> GEN_TAC >> EQ_TAC >> rpt STRIP_TAC
 >| [ fs [IN_INSERT] >> PROVE_TAC [],
      Q.EXISTS_TAC `x` >> ASM_REWRITE_TAC [IN_INSERT],
      Q.EXISTS_TAC `y` >> ASM_REWRITE_TAC [IN_INSERT] ]
QED

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
Theorem BIGUNION_IMAGE_COUNT_IMP_UNIV :
    !f g. (!n. BIGUNION (IMAGE g (count n)) = BIGUNION (IMAGE f (count n))) ==>
          (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE g UNIV))
Proof
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
 >> METIS_TAC []
QED

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

(* 1. for any set sequence there's increasing sequence of the same bigunion. *)
Theorem SETS_TO_INCREASING_SETS :
    !f :num->'a set.
       ?g. (g 0 = f 0) /\ (!n. g n = BIGUNION (IMAGE f (count (SUC n)))) /\
           (!n. g n SUBSET g (SUC n)) /\
           (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE g UNIV))
Proof
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
      REWRITE_TAC [GSYM UNION_ASSOC, UNION_IDEMPOT] ]
QED

(* another version with `g 0 = {}` *)
Theorem SETS_TO_INCREASING_SETS' :
    !f :num -> 'a set.
       ?g. (g 0 = {}) /\ (!n. g n = BIGUNION (IMAGE f (count n))) /\
           (!n. g n SUBSET g (SUC n)) /\
           (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE g UNIV))
Proof
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
        Q.EXISTS_TAC `x'` >> art [] ] ]
QED

(* 2. (hard) for any sequence of sets in a space, there is a disjoint family with
      the same bigunion. This lemma is needed by DYNKIN_LEMMA.
 *)
Theorem SETS_TO_DISJOINT_SETS :
    !sp sts f. (!s. s IN sts ==> s SUBSET sp) /\ (!n. f n IN sts) ==>
       ?g. (g 0 = f 0) /\
           (!n. 0 < n ==>
                g n = f n INTER (BIGINTER (IMAGE (\i. sp DIFF f i) (count n)))) /\
           (!i j :num. i <> j ==> DISJOINT (g i) (g j)) /\
           (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE g UNIV))
Proof
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
      Suff `BIGUNION (IMAGE f (count n)) UNION
              (BIGINTER (IMAGE (\i. sp DIFF f i) (count n))) = sp`
      >- (DISCH_THEN (REWRITE_TAC o wrap) \\
          REWRITE_TAC [INTER_SUBSET_EQN, UNION_SUBSET] \\
          reverse CONJ_TAC >- PROVE_TAC [] \\
          REWRITE_TAC [BIGUNION_SUBSET, IN_IMAGE] >> PROVE_TAC []) \\
   (* BIGUNION (IMAGE f (count n)) UNION
      BIGINTER (IMAGE (\i. sp DIFF f i) (count n)) = sp *)
     `0 < n` by PROVE_TAC [NOT_ZERO_LT_ZERO] \\
      POP_ASSUM (REWRITE_TAC o wrap o GSYM o (MATCH_MP GEN_COMPL_FINITE_UNION)) \\
      Suff `BIGUNION (IMAGE f (count n)) SUBSET sp` >- ASM_SET_TAC [] \\
      REWRITE_TAC [BIGUNION_SUBSET, IN_IMAGE] >> PROVE_TAC [] ]
QED

(* A specific version without sts and sp *)
Theorem SETS_TO_DISJOINT_SETS' :
    !f. ?g. (g 0 = f 0) /\
            (!n. 0 < n ==>
                 g n = f n INTER (BIGINTER (IMAGE (COMPL o f) (count n)))) /\
            (!i j :num. i <> j ==> DISJOINT (g i) (g j)) /\
            (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE g UNIV))
Proof
    GEN_TAC
 >> STRIP_ASSUME_TAC (Q.SPECL [`UNIV`, `UNIV`, `f`] SETS_TO_DISJOINT_SETS)
 >> fs [SUBSET_UNIV, o_DEF, COMPL_DEF]
 >> Q.EXISTS_TAC `g` >> art []
QED

(* 3. (hard) for any sequence of (straightly) increasing sets, there is a disjoint
      family with the same bigunion.
 *)
Theorem INCREASING_TO_DISJOINT_SETS :
    !f :num -> 'a set. (!n. f n SUBSET f (SUC n)) ==>
       ?g. (g 0 = f 0) /\ (!n. 0 < n ==> (g n = f n DIFF f (PRE n))) /\
           (!i j :num. i <> j ==> DISJOINT (g i) (g j)) /\
           (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE g UNIV))
Proof
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
        DISJ2_TAC >> Q.EXISTS_TAC `x'` >> art [] ] ]
QED

(* Surprisingly, this variant of INCREASING_TO_DISJOINT_SETS cannot be
   easily proved without using the non-trivial SETS_TO_DISJOINT_SETS
 *)
Theorem INCREASING_TO_DISJOINT_SETS' :
    !f :num -> 'a set. (f 0 = {}) /\ (!n. f n SUBSET f (SUC n)) ==>
       ?g. (!n. g n = f (SUC n) DIFF f n) /\
           (!i j :num. i <> j ==> DISJOINT (g i) (g j)) /\
           (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE g UNIV))
Proof
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
       `0 < SUC n` by REWRITE_TAC [LESS_0] \\
        Q.PAT_X_ASSUM `!n. 0 < n ==> X`
            (fn th => REWRITE_TAC [MATCH_MP th (ASSUME ``0:num < SUC n``)]) \\
        RW_TAC std_ss [IN_INTER, IN_BIGINTER_IMAGE, IN_COUNT, o_DEF, IN_COMPL] \\
        fs [GSYM LESS_EQ_IFF_LESS_SUC, LESS_OR_EQ] \\
        CCONTR_TAC >> fs [] \\
       `x IN f n` by PROVE_TAC [SUBSET_DEF] ] ]
QED

(* ------------------------------------------------------------------------- *)
(* Other types of disjointness definitions (from Concordia HVG)              *)
(* ------------------------------------------------------------------------- *)

Definition disjoint_family_on :
    disjoint_family_on a s =
      (!m n. m IN s /\ n IN s /\ (m <> n) ==> (a m INTER a n = {}))
End

Theorem disjoint_family_on_imp_disjoint :
    !a s. disjoint_family_on a s ==> disjoint (IMAGE a s)
Proof
    rw [disjoint_family_on, disjoint_def, DISJOINT_DEF]
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> CCONTR_TAC >> fs []
QED

Theorem disjoint_family_on_iff_disjoint :
    !a s. INJ a s (IMAGE a s) ==>
         (disjoint_family_on a s <=> disjoint (IMAGE a s))
Proof
    rpt STRIP_TAC
 >> EQ_TAC >- REWRITE_TAC [disjoint_family_on_imp_disjoint]
 >> rw [disjoint_family_on, disjoint_def, DISJOINT_DEF]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> CONJ_TAC >- (Q.EXISTS_TAC ‘m’ >> art [])
 >> CONJ_TAC >- (Q.EXISTS_TAC ‘n’ >> art [])
 >> fs [INJ_DEF]
 >> METIS_TAC []
QED

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
  [FULL_SIMP_TAC std_ss [GSPECIFICATION] THEN SET_TAC [], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [GSPECIFICATION] THEN
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
 >> RW_TAC std_ss [Once EXTENSION, IN_BIGUNION_IMAGE, IN_BIGUNION,
                   GSPECIFICATION, from_def]
 >> EQ_TAC >> rpt STRIP_TAC
 >- (Q.EXISTS_TAC `E x'` >> art [] \\
     Q.EXISTS_TAC `x'` >> art [])
 >> Q.EXISTS_TAC `n` >> PROVE_TAC []);

Theorem LIMSUP_COMPL : (* was: liminf_limsup *)
    !(E :num -> 'a set). COMPL (liminf E) = limsup (COMPL o E)
Proof
    RW_TAC std_ss [set_limsup_def, set_liminf_def]
 >> SIMP_TAC std_ss [COMPL_BIGUNION_IMAGE, o_DEF]
 >> Suff `!m. COMPL (BIGINTER {E n | m <= n}) =
              BIGUNION {COMPL (E n) | m <= n}` >- Rewr
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
 >> `x IN liminf A <=> ~(?N. INFINITE N /\ !n. n IN N ==> x NOTIN A n)`
       by PROVE_TAC []
 >> fs [infinitely_often_lemma]
QED

(* This version of LIMSUP_MONO is used in large_numberTheory.SLLN_IID_diverge *)
Theorem LIMSUP_MONO_STRONGER :
    !A B. (?d. !y n. y IN A n ==> ?m. n - d <= m /\ y IN B m) ==>
          limsup A SUBSET limsup B
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

(* ------------------------------------------------------------------------- *)
(*  Basic definitions.                                                       *)
(* ------------------------------------------------------------------------- *)

val _ = type_abbrev_pp ("algebra", ``:('a set) # ('a set set)``);

val space_def = Define
   `space   (x :'a set, y :('a set) set) = x`;

val subsets_def = Define
   `subsets (x :'a set, y :('a set) set) = y`;

val _ = export_rewrites ["space_def", "subsets_def"];

val subset_class_def = Define
   `subset_class sp sts = !x. x IN sts ==> x SUBSET sp`;

Definition algebra_def :
  algebra a =
    (subset_class (space a) (subsets a) /\
     {} IN subsets a /\
     (!s. s IN subsets a ==> space a DIFF s IN subsets a) /\
     (!s t. s IN subsets a /\ t IN subsets a ==> s UNION t IN subsets a))
End

Definition sigma_algebra_def :
  sigma_algebra a =
    (algebra a /\
     !c. countable c /\ c SUBSET (subsets a) ==> BIGUNION c IN (subsets a))
End

(* The set of measurable mappings, each (f :'a -> 'b) is called A/B-measurable

   NOTE: The requirement ‘sigma_algebra a /\ sigma_algebra b’ has been removed
         so that ‘measurable’ can be used in other system of sets.
        (cf. MEASURABLE_LIFT for a major related results.)
 *)
val measurable_def = Define
   `measurable a b = {f | f IN (space a -> space b) /\
                          !s. s IN subsets b ==>
                              ((PREIMAGE f s) INTER space a) IN subsets a}`;

(* the smallest sigma algebra generated from a set of sets *)
val sigma_def = Define
   `sigma sp sts = (sp, BIGINTER {s | sts SUBSET s /\ sigma_algebra (sp, s)})`;

Definition semiring_def : (* [7, p.39] *)
  semiring r =
    (subset_class (space r) (subsets r) /\
     {} IN (subsets r) /\
     (!s t. s IN (subsets r) /\ t IN (subsets r) ==> s INTER t IN (subsets r)) /\
     (!s t. s IN (subsets r) /\ t IN (subsets r) ==>
            ?c. c SUBSET (subsets r) /\ FINITE c /\ disjoint c /\
               (s DIFF t = BIGUNION c)))
End

Definition ring_def : (* see [4] *)
  ring r =
    (subset_class (space r) (subsets r) /\
     {} IN (subsets r) /\
     (!s t. s IN (subsets r) /\ t IN (subsets r) ==> s UNION t IN (subsets r)) /\
     (!s t. s IN (subsets r) /\ t IN (subsets r) ==> s DIFF t IN (subsets r)))
End

(* The smallest ring generated from a set of sets (usually a semiring) *)
val smallest_ring_def = Define
   `smallest_ring sp sts = (sp, BIGINTER {s | sts SUBSET s /\ ring (sp, s)})`;

(* After Eugene B. Dynkin (1924-2014), a Soviet and American mathematician [5] *)
Definition dynkin_system_def :
  dynkin_system d =
    (subset_class (space d) (subsets d) /\
     (space d) IN (subsets d) /\
     (!s. s IN (subsets d) ==> (space d DIFF s) IN (subsets d)) /\
     (!f :num -> 'a set.
        f IN (UNIV -> (subsets d)) /\ (!i j. i <> j ==> DISJOINT (f i) (f j))
        ==> BIGUNION (IMAGE f UNIV) IN (subsets d)))
End

(* The smallest dynkin system generated from a set of sets, cf. "sigma_def" *)
val dynkin_def = Define
   `dynkin sp sts = (sp, BIGINTER {d | sts SUBSET d /\ dynkin_system (sp, d)})`;

(* ------------------------------------------------------------------------- *)
(*  Basic theorems                                                           *)
(* ------------------------------------------------------------------------- *)

Theorem SPACE[simp] :
    !a. (space a, subsets a) = a
Proof
    GEN_TAC >> Cases_on ‘a’ >> rw []
QED

val ALGEBRA_ALT_INTER = store_thm
  ("ALGEBRA_ALT_INTER",
   ``!a.
       algebra a <=>
       subset_class (space a) (subsets a) /\
       {} IN (subsets a) /\ (!s. s IN (subsets a) ==> (space a DIFF s) IN (subsets a)) /\
       !s t. s IN (subsets a) /\ t IN (subsets a) ==> s INTER t IN (subsets a)``,
   RW_TAC std_ss [algebra_def, subset_class_def]
   >> EQ_TAC >|
   [RW_TAC std_ss []
    >> Know `s INTER t = space a DIFF ((space a DIFF s) UNION (space a DIFF t))`
    >- (RW_TAC std_ss [EXTENSION, IN_INTER, IN_DIFF, IN_UNION]
        >> EQ_TAC
        >- (RW_TAC std_ss [] >> FULL_SIMP_TAC std_ss [SUBSET_DEF] >> PROVE_TAC [])
        >> RW_TAC std_ss [] >> ASM_REWRITE_TAC [])
    >> RW_TAC std_ss [],
    RW_TAC std_ss []
    >> Know `s UNION t = space a DIFF ((space a DIFF s) INTER (space a DIFF t))`
    >- (RW_TAC std_ss [EXTENSION, IN_INTER, IN_DIFF, IN_UNION]
        >> EQ_TAC
        >- (RW_TAC std_ss [] >> FULL_SIMP_TAC std_ss [SUBSET_DEF] >> PROVE_TAC [])
        >> RW_TAC std_ss [] >> ASM_REWRITE_TAC [])
    >> RW_TAC std_ss []]);

val ALGEBRA_EMPTY = store_thm
  ("ALGEBRA_EMPTY",
   ``!a. algebra a ==> {} IN (subsets a)``,
   RW_TAC std_ss [algebra_def]);

val ALGEBRA_SPACE = store_thm
  ("ALGEBRA_SPACE",
   ``!a. algebra a ==> (space a) IN (subsets a)``,
   RW_TAC std_ss [algebra_def]
   >> PROVE_TAC [DIFF_EMPTY]);

val ALGEBRA_COMPL = store_thm
  ("ALGEBRA_COMPL",
   ``!a s. algebra a /\ s IN (subsets a) ==> (space a DIFF s) IN (subsets a)``,
   RW_TAC std_ss [algebra_def]);

Theorem ALGEBRA_UNION :
    !a s t. algebra a /\ s IN (subsets a) /\ t IN (subsets a) ==>
            s UNION t IN (subsets a)
Proof
    RW_TAC std_ss [algebra_def]
QED

Theorem ALGEBRA_INTER :
    !a s t. algebra a /\ s IN (subsets a) /\ t IN (subsets a) ==>
            s INTER t IN (subsets a)
Proof
    RW_TAC std_ss [ALGEBRA_ALT_INTER]
QED

Theorem ALGEBRA_DIFF :
    !a s t. algebra a /\ s IN (subsets a) /\ t IN (subsets a) ==>
            s DIFF t IN (subsets a)
Proof
    rpt STRIP_TAC
 >> Know `s DIFF t = s INTER (space a DIFF t)`
 >- (RW_TAC std_ss [EXTENSION, IN_DIFF, IN_INTER] \\
     FULL_SIMP_TAC std_ss [algebra_def, SUBSET_DEF, subset_class_def] \\
     PROVE_TAC [])
 >> RW_TAC std_ss [ALGEBRA_INTER, ALGEBRA_COMPL]
QED

Theorem ALGEBRA_FINITE_UNION :
    !a c. algebra a /\ FINITE c /\ c SUBSET (subsets a) ==>
          BIGUNION c IN (subsets a)
Proof
    RW_TAC std_ss [algebra_def]
 >> NTAC 2 (POP_ASSUM MP_TAC)
 >> Q.SPEC_TAC (`c`, `c`)
 >> HO_MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [BIGUNION_EMPTY, BIGUNION_INSERT, INSERT_SUBSET]
QED

(* prove "*_FINITE_INTER" from "*_INTER" *)
fun prove_finite_inter tm thm =
    Q.X_GEN_TAC `r`
 >> Suff `^tm r ==>
           !f n. 0 < n ==> (!i. i < n ==> f i IN (subsets r)) ==>
                 BIGINTER (IMAGE f (count n)) IN (subsets r)`
 >- METIS_TAC []
 >> DISCH_TAC
 >> Q.X_GEN_TAC ‘f’
 >> Induct_on `n` >- RW_TAC arith_ss []
 >> RW_TAC arith_ss []
 >> Cases_on `n = 0` >- fs [COUNT_SUC, COUNT_ZERO, IMAGE_INSERT, IMAGE_EMPTY,
                            BIGINTER_INSERT]
 >> `0 < n` by RW_TAC arith_ss []
 >> REWRITE_TAC [COUNT_SUC, IMAGE_INSERT, BIGINTER_INSERT]
 >> `!s t. s IN (subsets r) /\ t IN (subsets r) ==> s INTER t IN (subsets r)`
        by PROVE_TAC [thm] (* thm is used here *)
 >> POP_ASSUM MATCH_MP_TAC
 >> STRONG_CONJ_TAC
 >- (Q.PAT_X_ASSUM `!i. i < SUC n ==> f i IN X` (MP_TAC o (Q.SPEC `n`)) \\
     RW_TAC arith_ss [])
 >> DISCH_TAC
 >> FIRST_X_ASSUM irule >> art []
 >> rpt STRIP_TAC >> FIRST_X_ASSUM MATCH_MP_TAC
 >> RW_TAC arith_ss [];

(* This version is more applicable than ALGEBRA_FINITE_INTER' *)
Theorem ALGEBRA_FINITE_INTER :
    !a f n. algebra a /\ 0 < n /\ (!i. i < n ==> f i IN (subsets a)) ==>
            BIGINTER (IMAGE f (count n)) IN (subsets a)
Proof
    prove_finite_inter “algebra” ALGEBRA_INTER
QED

(* prove "*_FINITE_INTER'" from "*_INTER" *)
fun prove_finite_inter' thm =
    rpt STRIP_TAC
 >> NTAC 3 (POP_ASSUM MP_TAC)
 >> Q.SPEC_TAC (`c`, `c`)
 >> HO_MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [BIGINTER_EMPTY, BIGINTER_INSERT, INSERT_SUBSET]
 >> Cases_on ‘c = {}’ >- rw []
 >> MATCH_MP_TAC thm (* used here *) >> art []
 >> FIRST_X_ASSUM irule >> art [];

(* ‘c <> {}’ is necessary, otherwise ‘UNIV IN subset a’ does not hold. *)
Theorem ALGEBRA_FINITE_INTER' :
    !a c. algebra a /\ FINITE c /\ c SUBSET (subsets a) /\ c <> {} ==>
          BIGINTER c IN (subsets a)
Proof
    prove_finite_inter' ALGEBRA_INTER
QED

Theorem ALGEBRA_INTER_SPACE :
    !a s. algebra a /\ s IN subsets a ==> space a INTER s = s /\ s INTER space a = s
Proof
    RW_TAC std_ss [algebra_def, SUBSET_DEF, IN_INTER, EXTENSION, subset_class_def]
 >> PROVE_TAC []
QED

fun shared_tactics tm =
    rpt STRIP_TAC >> MATCH_MP_TAC tm >> fs [sigma_algebra_def];

Theorem SIGMA_ALGEBRA_EMPTY :
    !a. sigma_algebra a ==> {} IN (subsets a)
Proof
    shared_tactics ALGEBRA_EMPTY
QED

Theorem SIGMA_ALGEBRA_SPACE :
    !a. sigma_algebra a ==> (space a) IN (subsets a)
Proof
    shared_tactics ALGEBRA_SPACE
QED

Theorem SIGMA_ALGEBRA_COMPL :
    !a s. sigma_algebra a /\ s IN (subsets a) ==> (space a DIFF s) IN (subsets a)
Proof
    shared_tactics ALGEBRA_COMPL
QED

Theorem SIGMA_ALGEBRA_UNION :
    !a s t. sigma_algebra a /\ s IN (subsets a) /\ t IN (subsets a) ==>
            s UNION t IN (subsets a)
Proof
    shared_tactics ALGEBRA_UNION
QED

Theorem SIGMA_ALGEBRA_INTER :
    !a s t. sigma_algebra a /\ s IN (subsets a) /\ t IN (subsets a) ==>
            s INTER t IN (subsets a)
Proof
    shared_tactics ALGEBRA_INTER
QED

Theorem SIGMA_ALGEBRA_DIFF :
   !a s t. sigma_algebra a /\ s IN (subsets a) /\ t IN (subsets a) ==>
           s DIFF t IN (subsets a)
Proof
    shared_tactics ALGEBRA_DIFF
QED

Theorem SIGMA_ALGEBRA_FINITE_UNION :
    !a c. sigma_algebra a /\ FINITE c /\ c SUBSET (subsets a) ==>
          BIGUNION c IN (subsets a)
Proof
    shared_tactics ALGEBRA_FINITE_UNION
QED

Theorem SIGMA_ALGEBRA_FINITE_INTER :
    !a f n. sigma_algebra a /\ 0 < n /\ (!i. i < n ==> f i IN (subsets a)) ==>
            BIGINTER (IMAGE f (count n)) IN (subsets a)
Proof
    shared_tactics ALGEBRA_FINITE_INTER
QED

Theorem SIGMA_ALGEBRA_FINITE_INTER' :
    !a c. sigma_algebra a /\ FINITE c /\ c SUBSET (subsets a) /\ c <> {} ==>
          BIGINTER c IN (subsets a)
Proof
    shared_tactics ALGEBRA_FINITE_INTER'
QED

val SIGMA_ALGEBRA_ALT = store_thm
  ("SIGMA_ALGEBRA_ALT",
   ``!a.
       sigma_algebra a <=>
       algebra a /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> (subsets a)) ==> BIGUNION (IMAGE f UNIV) IN (subsets a))``,
   RW_TAC std_ss [sigma_algebra_def]
   >> EQ_TAC
   >- (RW_TAC std_ss [COUNTABLE_ALT, IN_FUNSET, IN_UNIV]
       >> Q.PAT_X_ASSUM `!c. P c ==> Q c` MATCH_MP_TAC
       >> reverse (RW_TAC std_ss [IN_IMAGE, SUBSET_DEF, IN_UNIV])
       >- PROVE_TAC []
       >> Q.EXISTS_TAC `f`
       >> RW_TAC std_ss []
       >> PROVE_TAC [])
   >> RW_TAC std_ss [COUNTABLE_ALT_BIJ]
   >- PROVE_TAC [ALGEBRA_FINITE_UNION]
   >> Q.PAT_X_ASSUM `!f. P f` (MP_TAC o Q.SPEC `\n. enumerate c n`)
   >> RW_TAC std_ss' [IN_UNIV, IN_FUNSET]
   >> Know `BIGUNION c = BIGUNION (IMAGE (enumerate c) UNIV)`
   >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION, IN_IMAGE, IN_UNIV]
       >> Suff `!s. s IN c <=> ?n. (enumerate c n = s)` >- PROVE_TAC []
       >> Q.PAT_X_ASSUM `BIJ x y z` MP_TAC
       >> RW_TAC std_ss [BIJ_DEF, SURJ_DEF, IN_UNIV]
       >> PROVE_TAC [])
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> POP_ASSUM MATCH_MP_TAC
   >> Strip
   >> Suff `enumerate c n IN c` >- PROVE_TAC [SUBSET_DEF]
   >> Q.PAT_X_ASSUM `BIJ i j k` MP_TAC
   >> RW_TAC std_ss [BIJ_DEF, SURJ_DEF, IN_UNIV]);

val SIGMA_ALGEBRA_ALT_MONO = store_thm
  ("SIGMA_ALGEBRA_ALT_MONO",
   ``!a.
       sigma_algebra a <=>
       algebra a /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> (subsets a)) /\ (f 0 = {}) /\ (!n. f n SUBSET f (SUC n)) ==>
          BIGUNION (IMAGE f UNIV) IN (subsets a))``,
   RW_TAC std_ss [SIGMA_ALGEBRA_ALT]
   >> EQ_TAC >- PROVE_TAC []
   >> RW_TAC std_ss []
   >> Q.PAT_X_ASSUM `!f. P f`
      (MP_TAC o Q.SPEC `\n. BIGUNION (IMAGE f (count n))`)
   >> RW_TAC std_ss [IN_UNIV, IN_FUNSET]
   >> Know `BIGUNION (IMAGE f UNIV) =
            BIGUNION (IMAGE (\n. BIGUNION (IMAGE f (count n))) UNIV)`
   >- (KILL_TAC
       >> ONCE_REWRITE_TAC [EXTENSION]
       >> RW_TAC std_ss [IN_BIGUNION, IN_IMAGE, IN_UNIV]
       >> EQ_TAC
       >- (RW_TAC std_ss []
           >> Q.EXISTS_TAC `BIGUNION (IMAGE f (count (SUC x')))`
           >> RW_TAC std_ss [IN_BIGUNION, IN_IMAGE, IN_COUNT]
           >> PROVE_TAC [LESS_SUC_REFL])
       >> RW_TAC std_ss []
       >> POP_ASSUM MP_TAC
       >> RW_TAC std_ss [IN_BIGUNION, IN_IMAGE, IN_COUNT]
       >> PROVE_TAC [])
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> POP_ASSUM MATCH_MP_TAC
   >> reverse (RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_COUNT, IN_IMAGE,
                              COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY])
   >- (Q.EXISTS_TAC `f x'`
       >> RW_TAC std_ss []
       >> Q.EXISTS_TAC `x'`
       >> DECIDE_TAC)
   >> MATCH_MP_TAC ALGEBRA_FINITE_UNION
   >> POP_ASSUM MP_TAC
   >> reverse (RW_TAC std_ss [IN_FUNSET, IN_UNIV, SUBSET_DEF, IN_IMAGE])
   >- PROVE_TAC []
   >> MATCH_MP_TAC IMAGE_FINITE
   >> RW_TAC std_ss [FINITE_COUNT]);

val SIGMA_ALGEBRA_ALT_DISJOINT = store_thm
  ("SIGMA_ALGEBRA_ALT_DISJOINT",
   ``!a.
       sigma_algebra a <=>
       algebra a /\
       (!f.
          f IN (UNIV -> (subsets a)) /\
          (!m n : num. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
          BIGUNION (IMAGE f UNIV) IN (subsets a))``,
   Strip
   >> EQ_TAC >- RW_TAC std_ss [SIGMA_ALGEBRA_ALT]
   >> RW_TAC std_ss [SIGMA_ALGEBRA_ALT_MONO, IN_FUNSET, IN_UNIV]
   >> Q.PAT_X_ASSUM `!f. P f ==> Q f` (MP_TAC o Q.SPEC `\n. f (SUC n) DIFF f n`)
   >> RW_TAC std_ss []
   >> Know
      `BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE (\n. f (SUC n) DIFF f n) UNIV)`
   >- (POP_ASSUM K_TAC
       >> ONCE_REWRITE_TAC [EXTENSION]
       >> RW_TAC std_ss [IN_BIGUNION, IN_IMAGE, IN_UNIV, IN_DIFF]
       >> reverse EQ_TAC
       >- (RW_TAC std_ss []
           >> POP_ASSUM MP_TAC
           >> RW_TAC std_ss [IN_DIFF]
           >> PROVE_TAC [])
       >> RW_TAC std_ss []
       >> Induct_on `x'` >- RW_TAC std_ss [NOT_IN_EMPTY]
       >> RW_TAC std_ss []
       >> Cases_on `x IN f x'` >- PROVE_TAC []
       >> Q.EXISTS_TAC `f (SUC x') DIFF f x'`
       >> RW_TAC std_ss [EXTENSION, IN_DIFF]
       >> PROVE_TAC [])
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> POP_ASSUM MATCH_MP_TAC
   >> CONJ_TAC >- RW_TAC std_ss [ALGEBRA_DIFF]
   >> HO_MATCH_MP_TAC TRANSFORM_2D_NUM
   >> CONJ_TAC >- PROVE_TAC [DISJOINT_SYM]
   >> RW_TAC arith_ss []
   >> Suff `f (SUC m) SUBSET f (m + n)`
   >- (RW_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY,
                      IN_INTER, IN_DIFF, SUBSET_DEF]
       >> PROVE_TAC [])
   >> Cases_on `n` >- PROVE_TAC [ADD_CLAUSES]
   >> POP_ASSUM K_TAC
   >> Know `m + SUC n' = SUC m + n'` >- DECIDE_TAC
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> Induct_on `n'` >- RW_TAC arith_ss [SUBSET_REFL]
   >> MATCH_MP_TAC SUBSET_TRANS
   >> Q.EXISTS_TAC `f (SUC m + n')`
   >> PROVE_TAC [ADD_CLAUSES]);

(* Definition 3.1 of [7, p.16] *)
Theorem SIGMA_ALGEBRA_ALT_SPACE :
    !a. sigma_algebra a <=>
        subset_class (space a) (subsets a) /\
        space a IN subsets a /\
        (!s. s IN subsets a ==> space a DIFF s IN subsets a) /\
        (!f :num -> 'a -> bool.
          f IN (UNIV -> (subsets a)) ==> BIGUNION (IMAGE f UNIV) IN (subsets a))
Proof
    RW_TAC std_ss [SIGMA_ALGEBRA_ALT]
 >> EQ_TAC >> RW_TAC std_ss [] (* 4 subgoals *)
 >- fs [algebra_def]
 >- (MATCH_MP_TAC ALGEBRA_SPACE >> art [])
 >- (MATCH_MP_TAC ALGEBRA_DIFF >> art [] \\
     MATCH_MP_TAC ALGEBRA_SPACE >> art [])
 >> RW_TAC std_ss [algebra_def]
 >- (‘{} = space a DIFF space a’ by SET_TAC [] >> POP_ORW \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> Q.PAT_X_ASSUM ‘!f. P ==> BIGUNION (IMAGE f univ(:num)) IN subsets a’
      (MP_TAC o (Q.SPEC ‘\n. if n = 0 then s else if n = 1 then t else {}’))
 >> simp [IN_FUNSET, IN_UNIV]
 >> Know ‘!n :num. (if n = 0 then s else if n = 1 then t else {}) IN subsets a’
 >- (GEN_TAC \\
     Cases_on ‘n = 0’ >- rw [] \\
     Cases_on ‘n = 1’ >- rw [] \\
     rw [] >> ‘{} = space a DIFF space a’ by SET_TAC [] >> POP_ORW \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> RW_TAC std_ss []
 >> Suff ‘s UNION t =
          BIGUNION (IMAGE (\n. if n = 0 then s else if n = 1 then t else {})
                          univ(:num))’ >- rw []
 >> RW_TAC std_ss [Once EXTENSION, IN_UNION, IN_BIGUNION_IMAGE, IN_UNIV]
 >> EQ_TAC >> RW_TAC std_ss [NOT_IN_EMPTY] (* 3 subgoals *)
 >- (Q.EXISTS_TAC ‘0’ >> rw [])
 >- (Q.EXISTS_TAC ‘1’ >> rw [])
 >> Cases_on ‘n = 0’ >- (DISJ1_TAC >> fs [])
 >> Cases_on ‘n = 1’ >- (DISJ2_TAC >> fs [])
 >> fs [NOT_IN_EMPTY]
QED

val SIGMA_ALGEBRA_ALGEBRA = store_thm
  ("SIGMA_ALGEBRA_ALGEBRA",
   ``!a. sigma_algebra a ==> algebra a``,
   PROVE_TAC [sigma_algebra_def]);

val SIGMA_ALGEBRA_SIGMA = store_thm
  ("SIGMA_ALGEBRA_SIGMA",
   ``!sp sts. subset_class sp sts ==> sigma_algebra (sigma sp sts)``,
   SIMP_TAC std_ss [subset_class_def]
   >> NTAC 3 STRIP_TAC
   >> RW_TAC std_ss [sigma_def, sigma_algebra_def, algebra_def,
                     subsets_def, space_def, IN_BIGINTER,
                     GSPECIFICATION, subset_class_def]
   >- (POP_ASSUM (MATCH_MP_TAC o
                  REWRITE_RULE [IN_POW, DIFF_SUBSET, UNION_SUBSET, EMPTY_SUBSET] o
       Q.ISPEC `POW (sp :'a -> bool)`)
       >> RW_TAC std_ss [SUBSET_DEF, IN_POW, IN_BIGUNION]
       >> PROVE_TAC [])
   >> POP_ASSUM (fn th => MATCH_MP_TAC th >> ASSUME_TAC th)
   >> RW_TAC std_ss [SUBSET_DEF]
   >> Q.PAT_X_ASSUM `c SUBSET PP` MP_TAC
   >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss()) [SUBSET_DEF]))
   >> DISCH_THEN (MP_TAC o Q.SPEC `x`)
   >> ASM_REWRITE_TAC []
   >> DISCH_THEN MATCH_MP_TAC
   >> RW_TAC std_ss []
   >> PROVE_TAC [SUBSET_DEF]);

Theorem SIGMA_ALGEBRA_SIGMA_UNIV :
    !sts. sigma_algebra (sigma UNIV sts)
Proof
    Q.X_GEN_TAC ‘sts’
 >> MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA
 >> rw [subset_class_def]
QED

(* power set of any space gives the largest possible algebra and sigma-algebra *)
val POW_ALGEBRA = store_thm
  ("POW_ALGEBRA", ``!sp. algebra (sp, POW sp)``,
    RW_TAC std_ss [algebra_def, IN_POW, space_def, subsets_def, subset_class_def,
                   EMPTY_SUBSET, DIFF_SUBSET, UNION_SUBSET]);

val POW_SIGMA_ALGEBRA = store_thm
  ("POW_SIGMA_ALGEBRA", ``!sp. sigma_algebra (sp, POW sp)``,
    RW_TAC std_ss [sigma_algebra_def, IN_POW, space_def, subsets_def,
                   POW_ALGEBRA, SUBSET_DEF, IN_BIGUNION]
 >> PROVE_TAC []);

val SIGMA_POW = store_thm
  ("SIGMA_POW",
   ``!s. sigma s (POW s) = (s,POW s)``,
   RW_TAC std_ss [sigma_def, PAIR_EQ, EXTENSION, IN_BIGINTER, IN_POW, GSPECIFICATION]
   >> EQ_TAC
   >- (RW_TAC std_ss [] >> POP_ASSUM (MP_TAC o Q.SPEC `POW s`)
       >> METIS_TAC [IN_POW, POW_SIGMA_ALGEBRA, SUBSET_REFL])
   >> RW_TAC std_ss [SUBSET_DEF, IN_POW] >> METIS_TAC []);

val UNIV_SIGMA_ALGEBRA = store_thm
  ("UNIV_SIGMA_ALGEBRA",
   ``sigma_algebra ((UNIV :'a -> bool),(UNIV :('a -> bool) -> bool))``,
    Know `(UNIV :('a -> bool) -> bool) = POW (UNIV :'a -> bool)`
    >- RW_TAC std_ss [EXTENSION, IN_POW, IN_UNIV, SUBSET_UNIV]
    >> RW_TAC std_ss [POW_SIGMA_ALGEBRA]);

Theorem SIGMA_SUBSET :
    !a b. sigma_algebra b /\ a SUBSET (subsets b) ==>
          subsets (sigma (space b) a) SUBSET (subsets b)
Proof
    RW_TAC std_ss [sigma_def, SUBSET_DEF, IN_BIGINTER, GSPECIFICATION, subsets_def]
 >> POP_ASSUM (MATCH_MP_TAC o Q.SPEC `subsets b`)
 >> RW_TAC std_ss [SPACE]
QED

val SIGMA_SUBSET_SUBSETS = store_thm
  ("SIGMA_SUBSET_SUBSETS", ``!sp a. a SUBSET subsets (sigma sp a)``,
   RW_TAC std_ss [sigma_def, IN_BIGINTER, SUBSET_DEF, GSPECIFICATION, subsets_def]);

val IN_SIGMA = store_thm
  ("IN_SIGMA", ``!sp a x. x IN a ==> x IN subsets (sigma sp a)``,
   MP_TAC SIGMA_SUBSET_SUBSETS
   >> RW_TAC std_ss [SUBSET_DEF]);

(* the proof is fully syntactical, `subset_class sp a` (or b) is not needed *)
val SIGMA_MONOTONE = store_thm
  ("SIGMA_MONOTONE",
  ``!sp a b. a SUBSET b ==> (subsets (sigma sp a)) SUBSET (subsets (sigma sp b))``,
    RW_TAC std_ss [sigma_def, SUBSET_DEF, IN_BIGINTER, GSPECIFICATION, subsets_def]);

(* the sigma of sigma-algebra is itself (stable) *)
val SIGMA_STABLE_LEMMA = store_thm
  ("SIGMA_STABLE_LEMMA",
   ``!sp sts. sigma_algebra (sp,sts) ==> (sigma sp sts = (sp,sts))``,
    RW_TAC std_ss [sigma_def, GSPECIFICATION, space_def, subsets_def]
 >> ASM_SET_TAC []);

(* |- !a. sigma_algebra a ==> (sigma (space a) (subsets a) = a) *)
val SIGMA_STABLE = save_thm
  ("SIGMA_STABLE",
    GEN_ALL (REWRITE_RULE [SPACE]
                (Q.SPECL [`space a`, `subsets a`] SIGMA_STABLE_LEMMA)));

(* This is why ‘sigma sp sts’ is "smallest": any sigma-algebra in the middle
   coincides with it. *)
Theorem SIGMA_SMALLEST :
    !sp sts A. sts SUBSET A /\ A SUBSET subsets (sigma sp sts) /\
               sigma_algebra (sp,A) ==> (A = subsets (sigma sp sts))
Proof
    RW_TAC std_ss [SET_EQ_SUBSET]
 >> IMP_RES_TAC SIGMA_STABLE_LEMMA
 >> ‘A = subsets (sigma sp A)’ by PROVE_TAC [subsets_def]
 >> POP_ORW
 >> MATCH_MP_TAC SIGMA_MONOTONE >> art []
QED

Theorem SIGMA_ALGEBRA :
    !p. sigma_algebra p <=>
        subset_class (space p) (subsets p) /\
        {} IN subsets p /\ (!s. s IN subsets p ==> (space p DIFF s) IN subsets p) /\
        !c. countable c /\ c SUBSET subsets p ==> BIGUNION c IN subsets p
Proof
    RW_TAC std_ss [sigma_algebra_def, algebra_def]
 >> EQ_TAC >- PROVE_TAC []
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM `!c. P c` (MP_TAC o Q.SPEC `{s; t}`)
 >> RW_TAC std_ss [COUNTABLE_ALT_BIJ, FINITE_INSERT, FINITE_EMPTY, SUBSET_DEF,
                   BIGUNION_PAIR, IN_INSERT, NOT_IN_EMPTY]
 >> PROVE_TAC []
QED

val SIGMA_ALGEBRA_COUNTABLE_UNION = store_thm
  ("SIGMA_ALGEBRA_COUNTABLE_UNION",
   ``!a c. sigma_algebra a /\ countable c /\ c SUBSET subsets a ==>
           BIGUNION c IN subsets a``,
   PROVE_TAC [sigma_algebra_def]);

Theorem SIGMA_ALGEBRA_ENUM :
    !a (f : num -> ('a -> bool)).
        sigma_algebra a /\ f IN (UNIV -> subsets a) ==>
        BIGUNION (IMAGE f UNIV) IN subsets a
Proof
    RW_TAC std_ss [SIGMA_ALGEBRA_ALT]
QED

Theorem SIGMA_PROPERTY :
    !sp p a.
       subset_class sp p /\ {} IN p /\ a SUBSET p /\
       (!s. s IN (p INTER subsets (sigma sp a)) ==> (sp DIFF s) IN p) /\
       (!c. countable c /\ c SUBSET (p INTER subsets (sigma sp a)) ==>
            BIGUNION c IN p) ==> subsets (sigma sp a) SUBSET p
Proof
    RW_TAC std_ss []
 >> Suff `subsets (sigma sp a) SUBSET p INTER subsets (sigma sp a)`
 >- SIMP_TAC std_ss [SUBSET_INTER]
 >> Suff `p INTER subsets (sigma sp a) IN {b | a SUBSET b /\ sigma_algebra (sp,b)}`
 >- (KILL_TAC \\
     RW_TAC std_ss [sigma_def, GSPECIFICATION, SUBSET_DEF, INTER_DEF, BIGINTER,
                    subsets_def])
 >> RW_TAC std_ss [GSPECIFICATION]
 >- PROVE_TAC [SUBSET_DEF, IN_INTER, IN_SIGMA]
 >> Know `subset_class sp a` >- PROVE_TAC [subset_class_def, SUBSET_DEF]
 >> STRIP_TAC
 >> Know `sigma_algebra (sigma sp a)`
 >- PROVE_TAC [subset_class_def, SUBSET_DEF, SIGMA_ALGEBRA_SIGMA]
 >> STRIP_TAC
 >> RW_TAC std_ss [SIGMA_ALGEBRA, IN_INTER, space_def, subsets_def,
                   SIGMA_ALGEBRA_ALGEBRA, ALGEBRA_EMPTY]
 >| [ (* goal 1 (of 3) *)
      PROVE_TAC [subset_class_def, IN_INTER, SUBSET_DEF],
      (* goal 2 (of 3) *)
     (MATCH_MP_TAC o REWRITE_RULE [space_def, subsets_def] o
        Q.SPEC `(sp, subsets (sigma sp a))`) ALGEBRA_COMPL \\
      FULL_SIMP_TAC std_ss [sigma_def, sigma_algebra_def, subsets_def],
      (* goal 3 (of 3 *)
      FULL_SIMP_TAC std_ss [sigma_algebra_def] \\
      Q.PAT_X_ASSUM `!c. P c ==> BIGUNION c IN subsets (sigma sp a)` MATCH_MP_TAC \\
      FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_INTER] ]
QED

val SIGMA_ALGEBRA_FN = store_thm
  ("SIGMA_ALGEBRA_FN",
   ``!a.
       sigma_algebra a <=>
       subset_class (space a) (subsets a) /\
       {} IN subsets a /\ (!s. s IN subsets a ==> (space a DIFF s) IN subsets a) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> subsets a) ==> BIGUNION (IMAGE f UNIV) IN subsets a)``,
   RW_TAC std_ss [SIGMA_ALGEBRA, IN_FUNSET, IN_UNIV, SUBSET_DEF]
   >> EQ_TAC
   >- (RW_TAC std_ss []
       >> Q.PAT_X_ASSUM `!c. P c ==> Q c` MATCH_MP_TAC
       >> RW_TAC std_ss [COUNTABLE_IMAGE_NUM, IN_IMAGE]
       >> PROVE_TAC [])
   >> RW_TAC std_ss [COUNTABLE_ENUM]
   >- RW_TAC std_ss [BIGUNION_EMPTY]
   >> Q.PAT_X_ASSUM `!f. (!x. P x f) ==> Q f` MATCH_MP_TAC
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [IN_IMAGE, IN_UNIV]
   >> PROVE_TAC []);

Theorem SIGMA_ALGEBRA_FN_BIGINTER :
    !a. sigma_algebra a ==>
        subset_class (space a) (subsets a) /\
        {} IN subsets a /\
        (!s. s IN subsets a ==> (space a DIFF s) IN subsets a) /\
        (!f :num -> 'a -> bool. f IN (UNIV -> subsets a) ==>
            BIGINTER (IMAGE f UNIV) IN subsets a)
Proof
    RW_TAC std_ss [SIGMA_ALGEBRA, IN_FUNSET, IN_UNIV, SUBSET_DEF]
 >> ASSUME_TAC (Q.SPECL [`space a`,`(IMAGE (f:num -> 'a -> bool) UNIV)`]
                        DIFF_BIGINTER)
 >> `!t. t IN IMAGE f UNIV ==> t SUBSET space a`
       by (FULL_SIMP_TAC std_ss [IN_IMAGE,sigma_algebra_def,algebra_def,subsets_def,
                                 space_def,subset_class_def,IN_UNIV] \\
           RW_TAC std_ss [] >> METIS_TAC [])
 >> `IMAGE f UNIV <> {}` by RW_TAC std_ss [IMAGE_EQ_EMPTY,UNIV_NOT_EMPTY]
 >> FULL_SIMP_TAC std_ss []
 >> `BIGUNION (IMAGE (\u. space a DIFF u) (IMAGE f UNIV)) IN subsets a`
       by (Q.PAT_ASSUM `!c. M ==> BIGUNION c IN subsets a` (MATCH_MP_TAC) \\
           RW_TAC std_ss []
           >- (MATCH_MP_TAC image_countable \\
               RW_TAC std_ss [COUNTABLE_ENUM] \\
               Q.EXISTS_TAC `f` >> RW_TAC std_ss [])
               >> FULL_SIMP_TAC std_ss [IN_IMAGE])
 >> METIS_TAC []
QED

val SIGMA_ALGEBRA_FN_DISJOINT = store_thm
  ("SIGMA_ALGEBRA_FN_DISJOINT",
   ``!a.
       sigma_algebra a <=>
       subset_class (space a) (subsets a) /\
       {} IN subsets a /\ (!s. s IN subsets a ==> (space a DIFF s) IN subsets a) /\
       (!s t. s IN subsets a /\ t IN subsets a ==> s UNION t IN subsets a) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> subsets a) /\ (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
          BIGUNION (IMAGE f UNIV) IN subsets a)``,
   RW_TAC std_ss [SIGMA_ALGEBRA_ALT_DISJOINT, algebra_def]
   >> EQ_TAC
   >> RW_TAC std_ss []);

(* [7, p.16] or Theorem 3.1.1 [8, p.35], f is not necessary measurable *)
Theorem PREIMAGE_SIGMA_ALGEBRA :
    !sp A f. sigma_algebra A /\ f IN (sp -> space A) ==>
             sigma_algebra (sp,IMAGE (\s. PREIMAGE f s INTER sp) (subsets A))
Proof
    rpt STRIP_TAC
 >> RW_TAC std_ss [SIGMA_ALGEBRA_ALT, space_def, subsets_def, algebra_def,
                   subset_class_def]
 >| [ (* goal 1 (of 5) *)
      fs [IN_IMAGE, IN_FUNSET],
      (* goal 2 (of 5) *)
      fs [IN_IMAGE, IN_FUNSET] \\
      Q.EXISTS_TAC `{}` >> REWRITE_TAC [PREIMAGE_EMPTY, INTER_EMPTY] \\
      fs [sigma_algebra_def, ALGEBRA_EMPTY],
      (* goal 3 (of 5) *)
      fs [IN_IMAGE, IN_FUNSET] \\
      Q.EXISTS_TAC `space A DIFF s'` \\
      reverse CONJ_TAC
      >- (MATCH_MP_TAC ALGEBRA_COMPL >> fs [sigma_algebra_def]) \\
      RW_TAC std_ss [EXTENSION, IN_PREIMAGE, IN_DIFF, IN_INTER] \\
      EQ_TAC >> RW_TAC std_ss [],
      (* goal 4 (of 5) *)
      fs [IN_IMAGE, IN_FUNSET] \\
      rename1 ‘t = PREIMAGE f t' INTER sp’ \\
      Q.EXISTS_TAC `s' UNION t'` \\
      reverse CONJ_TAC
      >- (MATCH_MP_TAC ALGEBRA_UNION >> fs [sigma_algebra_def]) \\
      RW_TAC std_ss [EXTENSION, IN_PREIMAGE, IN_UNION, IN_INTER] \\
      EQ_TAC >> RW_TAC std_ss [] >> art [],
      (* goal 5 (of 5) *)
      fs [IN_IMAGE, IN_FUNSET, IN_UNIV, SKOLEM_THM] \\
      rename1 ‘!x. f' x = PREIMAGE f (g x) INTER sp /\ g x IN subsets A’ \\
     `f' = \x. PREIMAGE f (g x) INTER sp` by PROVE_TAC [] >> POP_ORW \\
     `!x. g x IN subsets A` by PROVE_TAC [] \\
      Q.EXISTS_TAC `BIGUNION (IMAGE g UNIV)` \\
      reverse CONJ_TAC
      >- (fs [SIGMA_ALGEBRA_FN] \\
          FIRST_X_ASSUM MATCH_MP_TAC >> art [IN_FUNSET, IN_UNIV]) \\
      RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_PREIMAGE, IN_UNIV, IN_INTER] \\
      EQ_TAC >> RW_TAC std_ss [] >> art [] \\
      rename1 ‘f x IN g n’ \\
      Q.EXISTS_TAC `n` >> art [] ]
QED

Theorem SIGMA_PROPERTY_ALT :
    !sp p a.
       subset_class sp p /\
       {} IN p /\ a SUBSET p /\
       (!s. s IN (p INTER subsets (sigma sp a)) ==> sp DIFF s IN p) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> p INTER subsets (sigma sp a)) ==>
          BIGUNION (IMAGE f UNIV) IN p) ==>
       subsets (sigma sp a) SUBSET p
Proof
    RW_TAC std_ss []
 >> Suff `subsets (sigma sp a) SUBSET p INTER subsets (sigma sp a)`
 >- SIMP_TAC std_ss [SUBSET_INTER]
 >> Suff `p INTER subsets (sigma sp a) IN {b | a SUBSET b /\ sigma_algebra (sp, b)}`
 >- (KILL_TAC \\
     RW_TAC std_ss [sigma_def, GSPECIFICATION, SUBSET_DEF, INTER_DEF,
                    BIGINTER, subsets_def])
 >> RW_TAC std_ss [GSPECIFICATION]
 >- PROVE_TAC [SUBSET_DEF, IN_INTER, IN_SIGMA]
 >> POP_ASSUM MP_TAC
 >> Know `sigma_algebra (sigma sp a)`
 >- PROVE_TAC [subset_class_def, SUBSET_DEF, SIGMA_ALGEBRA_SIGMA]
 >> STRIP_TAC
 >> RW_TAC std_ss [SIGMA_ALGEBRA_FN, IN_INTER, FUNSET_INTER, subsets_def, space_def,
                   SIGMA_ALGEBRA_ALGEBRA, ALGEBRA_EMPTY]
 >| [ (* goal 1 (of 3) *)
      PROVE_TAC [subset_class_def, IN_INTER, SUBSET_DEF],
      (* goal 2 (of 3) *)
     (MATCH_MP_TAC o REWRITE_RULE [space_def, subsets_def] o
       Q.SPEC `(sp, subsets (sigma sp a))`) ALGEBRA_COMPL \\
      FULL_SIMP_TAC std_ss [sigma_def, sigma_algebra_def, subsets_def],
      (* goal 3 (of 3) *)
      FULL_SIMP_TAC std_ss [(Q.SPEC `(sigma sp a)`) SIGMA_ALGEBRA_FN] ]
QED

(* see SIGMA_PROPERTY_DISJOINT_WEAK_ALT for another version *)
val SIGMA_PROPERTY_DISJOINT_WEAK = store_thm
  ("SIGMA_PROPERTY_DISJOINT_WEAK",
   ``!sp p a.
       subset_class sp p /\
       {} IN p /\ a SUBSET p /\
       (!s. s IN (p INTER subsets (sigma sp a)) ==> (sp DIFF s) IN p) /\
       (!s t. s IN p /\ t IN p ==> s UNION t IN p) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> p INTER subsets (sigma sp a)) /\
          (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
          BIGUNION (IMAGE f UNIV) IN p) ==>
       subsets (sigma sp a) SUBSET p``,
   RW_TAC std_ss []
   >> Suff `subsets (sigma sp a) SUBSET p INTER subsets (sigma sp a)`
   >- SIMP_TAC std_ss [SUBSET_INTER]
   >> Suff `p INTER subsets (sigma sp a) IN {b | a SUBSET b /\ sigma_algebra (sp, b)}`
   >- (KILL_TAC
       >> RW_TAC std_ss [sigma_def, GSPECIFICATION, SUBSET_DEF, INTER_DEF, BIGINTER, subsets_def, space_def])
   >> RW_TAC std_ss [GSPECIFICATION]
   >- PROVE_TAC [SUBSET_DEF, IN_INTER, IN_SIGMA]
   >> POP_ASSUM MP_TAC
   >> Know `sigma_algebra (sigma sp a)` >- PROVE_TAC [subset_class_def, SUBSET_DEF,
                                                      SIGMA_ALGEBRA_SIGMA]
   >> STRIP_TAC
   >> RW_TAC std_ss [SIGMA_ALGEBRA_FN_DISJOINT, IN_INTER, FUNSET_INTER, subsets_def, space_def,
                     SIGMA_ALGEBRA_ALGEBRA, ALGEBRA_EMPTY]
   >| [PROVE_TAC [subset_class_def, IN_INTER, SUBSET_DEF],
       (MATCH_MP_TAC o REWRITE_RULE [space_def, subsets_def] o
        Q.SPEC `(sp, subsets (sigma sp a))`) ALGEBRA_COMPL
       >> FULL_SIMP_TAC std_ss [sigma_def, sigma_algebra_def, subsets_def],
       (MATCH_MP_TAC o REWRITE_RULE [space_def, subsets_def] o
        Q.SPEC `(sp, subsets (sigma sp a))`) ALGEBRA_UNION
       >> FULL_SIMP_TAC std_ss [sigma_def, sigma_algebra_def, subsets_def],
       FULL_SIMP_TAC std_ss [(Q.SPEC `(sigma sp a)`) SIGMA_ALGEBRA_FN_DISJOINT]]);

val SPACE_SIGMA = store_thm
  ("SPACE_SIGMA", ``!sp a. space (sigma sp a) = sp``,
    RW_TAC std_ss [sigma_def, space_def]);

val SIGMA_REDUCE = store_thm
  ("SIGMA_REDUCE", ``!sp a. (sp, subsets (sigma sp a)) = sigma sp a``,
    PROVE_TAC [SPACE_SIGMA, SPACE]);

Theorem SIGMA_CONG :
    !sp a b. (subsets (sigma sp a) = subsets (sigma sp b)) ==>
             (sigma sp a = sigma sp b)
Proof
    METIS_TAC [SPACE_SIGMA, SPACE]
QED

(* note: SEMIRING_SPACE doesn't hold *)
val SEMIRING_EMPTY = store_thm
  ("SEMIRING_EMPTY", ``!r. semiring r ==> {} IN (subsets r)``,
    RW_TAC std_ss [semiring_def]);

val SEMIRING_INTER = store_thm
  ("SEMIRING_INTER",
  ``!r s t. semiring r /\ s IN (subsets r) /\ t IN (subsets r) ==>
            s INTER t IN (subsets r)``,
    RW_TAC std_ss [semiring_def]);

val SEMIRING_DIFF = store_thm
  ("SEMIRING_DIFF",
  ``!r s t. semiring r /\ s IN (subsets r) /\ t IN (subsets r) ==>
         ?c. c SUBSET (subsets r) /\ FINITE c /\ disjoint c /\
            (s DIFF t = BIGUNION c)``,
    RW_TAC std_ss [semiring_def]);

val SEMIRING_DIFF_ALT = store_thm
  ("SEMIRING_DIFF_ALT",
  ``!r s t. semiring r /\ s IN (subsets r) /\ t IN (subsets r) ==>
         ?f n. (!i. i < n ==> f i IN subsets r) /\
               (!i j. i < n /\ j < n /\ i <> j ==> DISJOINT (f i) (f j)) /\
               (s DIFF t = BIGUNION (IMAGE f (count n)))``,
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [`r`, `s`, `t`] SEMIRING_DIFF)
 >> RW_TAC std_ss []
 >> STRIP_ASSUME_TAC (MATCH_MP finite_disjoint_decomposition
                               (CONJ (ASSUME ``FINITE (c :'a set set)``)
                                     (ASSUME ``disjoint (c :'a set set)``)))
 >> qexistsl_tac [`f`, `n`]
 >> RW_TAC std_ss []
 >> PROVE_TAC [SUBSET_DEF]);

Theorem SEMIRING_FINITE_INTER :
    !r f n. semiring r /\ 0 < n /\ (!i. i < n ==> f i IN (subsets r)) ==>
            BIGINTER (IMAGE f (count n)) IN (subsets r)
Proof
    prove_finite_inter “semiring” SEMIRING_INTER
QED

(* ‘c <> {}’ is necessary, otherwise ‘UNIV IN subset a’ does not hold. *)
Theorem SEMIRING_FINITE_INTER' :
    !r c. semiring r /\ FINITE c /\ c SUBSET (subsets r) /\ c <> {} ==>
          BIGINTER c IN (subsets r)
Proof
    prove_finite_inter' SEMIRING_INTER
QED

val RING_EMPTY = store_thm
  ("RING_EMPTY", ``!r. ring r ==> {} IN (subsets r)``,
    RW_TAC std_ss [ring_def]);

val RING_UNION = store_thm
  ("RING_UNION",
  ``!r s t. ring r /\ s IN (subsets r) /\ t IN (subsets r) ==>
            s UNION t IN (subsets r)``,
    RW_TAC std_ss [ring_def]);

val RING_FINITE_UNION = store_thm
  ("RING_FINITE_UNION",
  ``!r c. ring r /\ c SUBSET (subsets r) /\ FINITE c ==> BIGUNION c IN (subsets r)``,
    GEN_TAC
 >> Suff `ring r ==>
           !c. FINITE c ==> c SUBSET (subsets r) /\ FINITE c ==>
               BIGUNION c IN (subsets r)`
 >- METIS_TAC []
 >> DISCH_TAC
 >> HO_MATCH_MP_TAC FINITE_INDUCT
 >> CONJ_TAC
 >- (RW_TAC std_ss [] >> PROVE_TAC [BIGUNION_EMPTY, RING_EMPTY])
 >> rpt STRIP_TAC
 >> REWRITE_TAC [BIGUNION_INSERT]
 >> fs [ring_def]);

val RING_FINITE_UNION_ALT = store_thm
  ("RING_FINITE_UNION_ALT",
  ``!r f n. ring r /\ (!i. i < n ==> f i IN subsets r) ==>
            BIGUNION (IMAGE f (count n)) IN (subsets r)``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC RING_FINITE_UNION
 >> ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT]
 >> CONJ_TAC >- METIS_TAC []
 >> MATCH_MP_TAC IMAGE_FINITE
 >> REWRITE_TAC [FINITE_COUNT]);

(* NOTE: RING_COMPL doesn't hold because RING_SPACE doesn't hold *)
val RING_DIFF = store_thm
  ("RING_DIFF",
  ``!r s t. ring r /\ s IN (subsets r) /\ t IN (subsets r) ==>
            s DIFF t IN (subsets r)``,
    RW_TAC std_ss [ring_def]);

val RING_INTER = store_thm
  ("RING_INTER",
  ``!r s t. ring r /\ s IN (subsets r) /\ t IN (subsets r) ==>
            s INTER t IN (subsets r)``,
    RW_TAC std_ss [ring_def]
 >> `s INTER t = s DIFF (s DIFF t)` by SET_TAC [] >> POP_ORW
 >> Q.PAT_ASSUM `!s t. X ==> s DIFF t IN subsets r` MATCH_MP_TAC >> art []
 >> Q.PAT_ASSUM `!s t. X ==> s DIFF t IN subsets r` MATCH_MP_TAC >> art []);

Theorem RING_FINITE_INTER :
    !r f n. ring r /\ 0 < n /\ (!i. i < n ==> f i IN (subsets r)) ==>
            BIGINTER (IMAGE f (count n)) IN (subsets r)
Proof
    prove_finite_inter “ring” RING_INTER
QED

(* ‘c <> {}’ is necessary, otherwise ‘UNIV IN subset a’ does not hold. *)
Theorem RING_FINITE_INTER' :
    !r c. ring r /\ FINITE c /\ c SUBSET (subsets r) /\ c <> {} ==>
          BIGINTER c IN (subsets r)
Proof
    prove_finite_inter' RING_INTER
QED

(* a ring is also a semiring (but not vice versa) *)
val RING_IMP_SEMIRING = store_thm
  ("RING_IMP_SEMIRING", ``!r. ring r ==> semiring r``,
    RW_TAC std_ss [semiring_def]
 >- PROVE_TAC [ring_def]
 >- (MATCH_MP_TAC RING_EMPTY >> art [])
 >- (MATCH_MP_TAC RING_INTER >> art [])
 >> Q.EXISTS_TAC `{s DIFF t}`
 >> `s DIFF t IN subsets r` by PROVE_TAC [RING_DIFF]
 >> SIMP_TAC std_ss [disjoint_sing, BIGUNION_SING, FINITE_SING]
 >> ASM_SET_TAC []);

(* thus: algebra ==> ring ==> semiring *)
val ALGEBRA_IMP_RING = store_thm
  ("ALGEBRA_IMP_RING", ``!a. algebra a ==> ring a``,
    RW_TAC std_ss [ring_def]
 >- PROVE_TAC [algebra_def]
 >- (MATCH_MP_TAC ALGEBRA_EMPTY >> art [])
 >- (MATCH_MP_TAC ALGEBRA_UNION >> art [])
 >> MATCH_MP_TAC ALGEBRA_DIFF >> art []);

(* an algebra is also a semiring (but not vice versa) *)
val ALGEBRA_IMP_SEMIRING = store_thm
  ("ALGEBRA_IMP_SEMIRING", ``!a. algebra a ==> semiring a``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC RING_IMP_SEMIRING
 >> MATCH_MP_TAC ALGEBRA_IMP_RING
 >> ASM_REWRITE_TAC []);

(* if the whole space is in the ring, the ring becomes algebra (thus also semiring) *)
val RING_SPACE_IMP_ALGEBRA = store_thm
  ("RING_SPACE_IMP_ALGEBRA",
  ``!r. ring r /\ (space r) IN (subsets r) ==> algebra r``,
    RW_TAC std_ss [algebra_def, ring_def, subset_class_def]);

(* thus (smallest_ring sp sts) is really a ring, as `POW sp` is a ring. *)
val SMALLEST_RING = store_thm
  ("SMALLEST_RING",
  ``!sp sts. subset_class sp sts ==> ring (smallest_ring sp sts)``,
    SIMP_TAC std_ss [subset_class_def]
 >> rpt STRIP_TAC
 >> RW_TAC std_ss [smallest_ring_def, ring_def, subsets_def, space_def, IN_BIGINTER,
                   GSPECIFICATION, subset_class_def]
 >> POP_ASSUM (MATCH_MP_TAC o
               REWRITE_RULE [IN_POW, DIFF_SUBSET, UNION_SUBSET, EMPTY_SUBSET] o
               (Q.ISPEC `POW (sp :'a -> bool)`))
 >> RW_TAC std_ss [SUBSET_DEF, IN_POW, IN_BIGUNION, IN_DIFF, IN_INTER]);

Theorem SPACE_SMALLEST_RING :
    !sp sts. space (smallest_ring sp sts) = sp
Proof
    RW_TAC std_ss [smallest_ring_def, space_def]
QED

Theorem SMALLEST_RING_SUBSET_SUBSETS :
    !sp a. a SUBSET subsets (smallest_ring sp a)
Proof
    RW_TAC std_ss [smallest_ring_def, subsets_def,
                   IN_BIGINTER, SUBSET_DEF, GSPECIFICATION]
QED

(* extracted from CARATHEODORY_SEMIRING for `lborel` construction *)
Theorem SMALLEST_RING_OF_SEMIRING :
    !sp sts. semiring (sp,sts) ==>
             subsets (smallest_ring sp sts) =
               {BIGUNION c | c SUBSET sts /\ FINITE c /\ disjoint c}
Proof
    RW_TAC std_ss [smallest_ring_def, subsets_def]
 >> RW_TAC std_ss [Once EXTENSION, GSPECIFICATION, IN_BIGINTER]
 >> reverse EQ_TAC >> RW_TAC std_ss []
 >- (MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                (Q.SPEC `(sp,P)` RING_FINITE_UNION)) >> art [] \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC `sts` >> art [])
 >> POP_ASSUM (MP_TAC o
               (Q.SPEC `{BIGUNION c | c SUBSET sts /\ FINITE c /\ disjoint c}`))
 >> Know `sts SUBSET {BIGUNION c | c SUBSET sts /\ FINITE c /\ disjoint c}`
 >- (RW_TAC set_ss [SUBSET_DEF] \\
     Q.EXISTS_TAC `{x}` >> rw [disjoint_sing])
 >> Suff `ring (sp,{BIGUNION c | c SUBSET sts /\ FINITE c /\ disjoint c})` >- rw []
 >> Q.ABBREV_TAC `S = {BIGUNION c | c SUBSET sts /\ FINITE c /\ disjoint c}`
 >> Know `{} IN S`
 >- (Q.UNABBREV_TAC `S` >> RW_TAC std_ss [GSPECIFICATION] \\
     Q.EXISTS_TAC `EMPTY` \\
     REWRITE_TAC [BIGUNION_EMPTY, EMPTY_SUBSET, FINITE_EMPTY, disjoint_empty])
 >> DISCH_TAC
 >> Know `sts SUBSET S`
 >- (RW_TAC std_ss [SUBSET_DEF] \\
     Q.UNABBREV_TAC `S` >> SIMP_TAC std_ss [GSPECIFICATION] \\
     Q.EXISTS_TAC `{x}` \\
     REWRITE_TAC [BIGUNION_SING, FINITE_SING, disjoint_sing] \\
     ASM_SET_TAC [])
 >> DISCH_TAC
 (* S is stable under disjoint unions *)
 >> Know `!s t. s IN S /\ t IN S /\ DISJOINT s t ==> s UNION t IN S`
 >- (Q.UNABBREV_TAC `S` >> RW_TAC std_ss [GSPECIFICATION] \\
     Q.EXISTS_TAC `c UNION c'` >> REWRITE_TAC [BIGUNION_UNION] \\
     CONJ_TAC >- PROVE_TAC [UNION_SUBSET] \\
     CONJ_TAC >- PROVE_TAC [FINITE_UNION] \\
     MATCH_MP_TAC disjoint_union >> art [] \\
     METIS_TAC [DISJOINT_DEF])
 >> DISCH_TAC
 (* S is stable under finite disjoint unions (not that easy!) *)
 >> Know `!c. c SUBSET S /\ FINITE c /\ disjoint c ==> BIGUNION c IN S`
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
     REWRITE_TAC [BIGUNION_OVER_INTER_R] \\
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
      `f 0 IN IMAGE f (count n)`
         by (FIRST_X_ASSUM MATCH_MP_TAC >> RW_TAC arith_ss []) \\
       METIS_TAC [disjoint_insert_notin, DISJOINT_DEF] ])
 >> DISCH_TAC
 (* S is stable under finite intersection (semiring is used) *)
 >> Know `!s t. s IN S /\ t IN S ==> s INTER t IN S`
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
     ASM_REWRITE_TAC [BIGUNION_OVER_INTER_L] \\
     REWRITE_TAC [BIGUNION_OVER_INTER_R] \\
     FIRST_ASSUM MATCH_MP_TAC \\
     reverse CONJ_TAC (* some easy goals *)
     >- (CONJ_TAC >- (MATCH_MP_TAC IMAGE_FINITE >> REWRITE_TAC [FINITE_COUNT]) \\
         MATCH_MP_TAC disjointI \\
         NTAC 2 GEN_TAC >> SIMP_TAC std_ss [IN_IMAGE, IN_COUNT] \\
         rpt STRIP_TAC \\
         Cases_on `i = i'` >- (`a = b` by METIS_TAC []) \\
         ASM_REWRITE_TAC [DISJOINT_ALT] \\
         GEN_TAC >> SIMP_TAC std_ss [IN_BIGUNION_IMAGE, IN_COUNT, IN_INTER] \\
         rpt STRIP_TAC \\
         DISJ2_TAC >> DISJ1_TAC >> CCONTR_TAC >> fs [] \\
        `x IN f i INTER f i'` by METIS_TAC [IN_INTER] \\
        `~DISJOINT (f i) (f i')` by ASM_SET_TAC [DISJOINT_DEF] \\
         Q.PAT_X_ASSUM `disjoint (IMAGE f (count n))` MP_TAC \\
         RW_TAC std_ss [disjoint_def, IN_IMAGE, IN_COUNT] \\
         Q.EXISTS_TAC `f i` >> Q.EXISTS_TAC `f i'` >> art [] \\
         METIS_TAC []) \\
  (* IMAGE (\i. BIGUNION (IMAGE (\i'. f i INTER f' i') (count n'))) (count n)
     SUBSET S *)
     RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT] \\
     FIRST_ASSUM MATCH_MP_TAC \\
     reverse CONJ_TAC (* some easy goals *)
     >- (CONJ_TAC >- (MATCH_MP_TAC IMAGE_FINITE >> REWRITE_TAC [FINITE_COUNT]) \\
         MATCH_MP_TAC disjointI \\
         NTAC 2 GEN_TAC >> SIMP_TAC std_ss [IN_IMAGE, IN_COUNT] \\
         rpt STRIP_TAC \\
         Cases_on `i' = i''` >- (`a = b` by METIS_TAC []) \\
         ASM_REWRITE_TAC [DISJOINT_ALT] \\
         RW_TAC std_ss [IN_INTER] \\
         CCONTR_TAC >> fs [] \\
        `x IN f' i' INTER f' i''` by PROVE_TAC [IN_INTER] \\
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
     METIS_TAC [SUBSET_DEF])
 >> DISCH_TAC
 (* S is stable under (more) finite intersection *)
 >> Know `!f n. 0 < n ==> (!i. i < n ==> f i IN S) ==>
                BIGINTER (IMAGE f (count n)) IN S`
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
     RW_TAC arith_ss [])
 >> DISCH_TAC
 (* DIFF of sts is in S (semiring is used) *)
 >> Know `!s t. s IN sts /\ t IN sts ==> s DIFF t IN S`
 >- (rpt STRIP_TAC \\
     fs [semiring_def, subset_class_def, space_def, subsets_def] \\
    `?c. c SUBSET sts /\ FINITE c /\ disjoint c /\ (s DIFF t = BIGUNION c)`
       by PROVE_TAC [] \\
     Q.UNABBREV_TAC `S` >> SIMP_TAC std_ss [GSPECIFICATION] \\
     Q.EXISTS_TAC `c` >> art [])
 >> DISCH_TAC
 (* S is stable under diff (semiring is used) *)
 >> Know `!s t. s IN S /\ t IN S ==> s DIFF t IN S`
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
         Suff `f x' SUBSET sp` >- PROVE_TAC [SUBSET_DEF] \\
         fs [semiring_def, subset_class_def, space_def, subsets_def] \\
        `f x' IN sts` by PROVE_TAC [SUBSET_DEF, IN_IMAGE, IN_COUNT] \\
         METIS_TAC []) >> DISCH_TAC \\
     Know `BIGUNION (IMAGE f' (count n')) SUBSET sp`
     >- (RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_COUNT] \\
         Suff `f' x' SUBSET sp` >- PROVE_TAC [SUBSET_DEF] \\
         fs [semiring_def, subset_class_def, space_def, subsets_def] \\
        `f' x' IN sts` by PROVE_TAC [SUBSET_DEF, IN_IMAGE, IN_COUNT] \\
         METIS_TAC []) >> DISCH_TAC \\
     Cases_on `n = 0`
     >- (METIS_TAC [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY, EMPTY_DIFF]) \\
     Cases_on `n' = 0`
     >- (ASM_REWRITE_TAC [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY, DIFF_EMPTY] \\
         METIS_TAC []) \\
    `0 < n /\ 0 < n'` by RW_TAC arith_ss [] \\
     REWRITE_TAC
       [MATCH_MP GEN_DIFF_INTER
                (CONJ (ASSUME ``BIGUNION (IMAGE f (count n)) SUBSET sp``)
                      (ASSUME ``BIGUNION (IMAGE f' (count n')) SUBSET sp``))] \\
     REWRITE_TAC [MATCH_MP GEN_COMPL_FINITE_UNION (ASSUME ``0:num < n'``)] \\
     REWRITE_TAC [BIGUNION_OVER_INTER_L] \\
    ‘count n' <> {}’ by PROVE_TAC [COUNT_NOT_EMPTY] \\
     REWRITE_TAC [MATCH_MP BIGINTER_OVER_INTER_R (ASSUME ``count n' <> {}``)] \\
     BETA_TAC >> FIRST_ASSUM MATCH_MP_TAC \\
     reverse CONJ_TAC (* some easy goals *)
     >- (CONJ_TAC >- (MATCH_MP_TAC IMAGE_FINITE >> REWRITE_TAC [FINITE_COUNT]) \\
         MATCH_MP_TAC disjointI \\
         NTAC 2 GEN_TAC >> SIMP_TAC std_ss [IN_IMAGE, IN_COUNT] \\
         rpt STRIP_TAC \\
         Cases_on `i = i'` >- (`a = b` by METIS_TAC []) \\
         ASM_REWRITE_TAC [DISJOINT_ALT] \\
         GEN_TAC >> SIMP_TAC std_ss [IN_BIGINTER_IMAGE, IN_COUNT] \\
         rpt STRIP_TAC \\
         POP_ASSUM (STRIP_ASSUME_TAC o
                    (fn th => MATCH_MP th (ASSUME ``0:num < n'``))) \\
         Q.EXISTS_TAC `0` >> art [] \\
         SIMP_TAC std_ss [IN_INTER] \\
         DISJ1_TAC >> CCONTR_TAC \\
         fs [IN_INTER] \\
        `x IN f i INTER f i'` by PROVE_TAC [IN_INTER] \\
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
     Rewr >> FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> DISCH_TAC
  (* S is stable under finite union (but is still NOT an algebra) *)
 >> Know `!s t. s IN S /\ t IN S ==> s UNION t IN S`
 >- (rpt STRIP_TAC \\
     STRIP_ASSUME_TAC (Q.SPECL [`s`, `t`] UNION_TO_3_DISJOINT_UNIONS) >> art [] \\
     FIRST_ASSUM MATCH_MP_TAC \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       FIRST_X_ASSUM MATCH_MP_TAC \\
       CONJ_TAC >- PROVE_TAC [] \\
       CONJ_TAC >- PROVE_TAC [] \\
       ASM_SET_TAC [disjoint_def, DISJOINT_DEF],
       (* goal 2 (of 2) *)
       CONJ_TAC >- PROVE_TAC [] \\
       ASM_SET_TAC [disjoint_def, DISJOINT_DEF] ])
 >> DISCH_TAC
 >> RW_TAC std_ss [ring_def, subset_class_def, space_def, subsets_def]
 >> POP_ASSUM MP_TAC >> Q.UNABBREV_TAC `S`
 >> RW_TAC std_ss [GSPECIFICATION]
 >> RW_TAC std_ss [BIGUNION_SUBSET]
 >> `Y IN sts` by METIS_TAC [SUBSET_DEF]
 >> METIS_TAC [semiring_def, subset_class_def, space_def, subsets_def]
QED

val subset_class_POW = store_thm
  ("subset_class_POW", ``!sp. subset_class sp (POW sp)``,
    RW_TAC std_ss [subset_class_def, IN_POW]);

val DYNKIN_SYSTEM_COMPL = store_thm
  ("DYNKIN_SYSTEM_COMPL",
  ``!d s. dynkin_system d /\ s IN subsets d ==> space d DIFF s IN subsets d``,
    RW_TAC std_ss [dynkin_system_def]);

val DYNKIN_SYSTEM_SPACE = store_thm
  ("DYNKIN_SYSTEM_SPACE",
  ``!d. dynkin_system d ==> (space d) IN subsets d``,
    PROVE_TAC [dynkin_system_def]);

val DYNKIN_SYSTEM_EMPTY = store_thm
  ("DYNKIN_SYSTEM_EMPTY",
  ``!d. dynkin_system d ==> {} IN subsets d``,
    rpt STRIP_TAC
 >> REWRITE_TAC [SYM (Q.SPEC `space d` DIFF_EQ_EMPTY)]
 >> MATCH_MP_TAC DYNKIN_SYSTEM_COMPL >> art []
 >> PROVE_TAC [dynkin_system_def]);

val DYNKIN_SYSTEM_DUNION = store_thm
  ("DYNKIN_SYSTEM_DUNION",
  ``!d s t. dynkin_system d /\ s IN subsets d /\ t IN subsets d /\ DISJOINT s t
        ==> s UNION t IN subsets d``,
    rpt STRIP_TAC
 >> IMP_RES_TAC DYNKIN_SYSTEM_EMPTY
 >> fs [dynkin_system_def]
 >> Q.PAT_X_ASSUM `!f. P f`
      (MP_TAC o Q.SPEC `\n. if n = 0 then s else if n = 1 then t else {}`)
 >> Know
      `BIGUNION
       (IMAGE (\n : num. (if n = 0 then s else (if n = 1 then t else {})))
        UNIV) =
       BIGUNION
       (IMAGE (\n : num. (if n = 0 then s else (if n = 1 then t else {})))
        (count 2))`
 >- (MATCH_MP_TAC BIGUNION_IMAGE_UNIV >> RW_TAC arith_ss [])
 >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
 >> RW_TAC bool_ss [COUNT_SUC, IMAGE_INSERT, TWO, ONE, BIGUNION_INSERT,
                    COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY, UNION_EMPTY]
 >> ONCE_REWRITE_TAC [UNION_COMM]
 >> POP_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, DISJOINT_EMPTY]
 >- (rpt COND_CASES_TAC >> art [])
 >> ASM_REWRITE_TAC [DISJOINT_SYM]);

val DYNKIN_SYSTEM_COUNTABLY_DUNION = store_thm
  ("DYNKIN_SYSTEM_COUNTABLY_DUNION",
   ``!d f.
       dynkin_system d /\ f IN (UNIV -> subsets d) /\
       (!i j :num. i <> j ==> DISJOINT (f i) (f j)) ==>
       BIGUNION (IMAGE f UNIV) IN subsets d``,
   RW_TAC std_ss [dynkin_system_def]);

(* Alternative definition of Dynkin system [6], this equivalence proof is not easy *)
val DYNKIN_SYSTEM_ALT_MONO = store_thm
  ("DYNKIN_SYSTEM_ALT_MONO",
  ``!d. dynkin_system d <=>
        subset_class (space d) (subsets d) /\
        (space d) IN (subsets d) /\
        (!s t. s IN (subsets d) /\ t IN (subsets d) /\ s SUBSET t ==> (t DIFF s) IN (subsets d)) /\
        (!f :num -> 'a set.
          f IN (UNIV -> subsets d) /\ (f 0 = {}) /\ (!n. f n SUBSET f (SUC n)) ==>
          BIGUNION (IMAGE f UNIV) IN (subsets d))``,
    RW_TAC std_ss [dynkin_system_def]
 >> EQ_TAC (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      RW_TAC std_ss [IN_FUNSET, IN_UNIV] >|
      [ (* goal 1.1 (of 2), `t DIFF s IN subsets d` *)
       `DISJOINT s (space d DIFF t)` by ASM_SET_TAC [] \\
        Q.PAT_X_ASSUM `!f. P f`
          (MP_TAC o Q.SPEC `\n. if n = 0 then s else
                                if n = 1 then (space d DIFF t) else {}`) \\
        Know `BIGUNION
                (IMAGE (\n :num. if n = 0 then s else
                                 if n = 1 then (space d DIFF t) else {}) UNIV) =
              BIGUNION
                (IMAGE (\n :num. if n = 0 then s else
                                 if n = 1 then (space d DIFF t) else {}) (count 2))`
        >- (MATCH_MP_TAC BIGUNION_IMAGE_UNIV >> RW_TAC arith_ss [])
        >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
        >> RW_TAC bool_ss [COUNT_SUC, IMAGE_INSERT, TWO, ONE, BIGUNION_INSERT,
                           COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY, UNION_EMPTY] \\
        Know `t DIFF s = (space d) DIFF ((space d DIFF t) UNION s)`
        >- (`s SUBSET space d /\ t SUBSET space d` by PROVE_TAC [subset_class_def]
            >> ASM_SET_TAC [])
        >> DISCH_THEN (ONCE_REWRITE_TAC o wrap) \\
        Q.PAT_ASSUM `!s. s IN subsets d ==> P` MATCH_MP_TAC \\
        POP_ASSUM MATCH_MP_TAC \\
        CONJ_TAC >> rpt STRIP_TAC
        >- (rpt COND_CASES_TAC >> PROVE_TAC [DIFF_EQ_EMPTY])
        >> rpt COND_CASES_TAC >> fs [DISJOINT_SYM],
        (* goal 1.2 (of 2), `BIGUNION (IMAGE f univ(:num)) IN subsets d` *)
        Q.PAT_ASSUM `!f. P f ==> Q f` (MP_TAC o Q.SPEC `\n. f (SUC n) DIFF f n`) \\
        BETA_TAC >> STRIP_TAC \\
        Know `BIGUNION (IMAGE f UNIV) =
              BIGUNION (IMAGE (\n. f (SUC n) DIFF f n) UNIV)`
        >- (POP_ASSUM K_TAC
            >> ONCE_REWRITE_TAC [EXTENSION]
            >> RW_TAC std_ss [IN_BIGUNION, IN_IMAGE, IN_UNIV, IN_DIFF]
            >> reverse EQ_TAC
            >- (RW_TAC std_ss []
                >> POP_ASSUM MP_TAC
                >> RW_TAC std_ss [IN_DIFF]
                >> PROVE_TAC [])
            >> RW_TAC std_ss []
            >> Induct_on `x'` >- RW_TAC std_ss [NOT_IN_EMPTY]
            >> RW_TAC std_ss []
            >> Cases_on `x IN f x'` >- PROVE_TAC []
            >> Q.EXISTS_TAC `f (SUC x') DIFF f x'`
            >> RW_TAC std_ss [EXTENSION, IN_DIFF]
            >> PROVE_TAC [])
        >> DISCH_THEN (REWRITE_TAC o wrap) \\
        POP_ASSUM MATCH_MP_TAC \\
        CONJ_TAC >| (* 2 subgoals *)
        [ (* goal 1.2.1 (of 2) *)
          GEN_TAC \\
          Know `f (SUC x) DIFF f x =
                (space d) DIFF ((space d DIFF f (SUC x)) UNION f x)`
          >- (`f x SUBSET space d /\ f (SUC x) SUBSET space d`
                 by PROVE_TAC [subset_class_def] \\
              ASM_SET_TAC [])
          >> DISCH_THEN (ONCE_REWRITE_TAC o wrap) \\
          Q.PAT_ASSUM `!s. s IN subsets d ==> P` MATCH_MP_TAC \\
          `space d DIFF f (SUC x) IN subsets d` by PROVE_TAC [] \\
          `DISJOINT (space d DIFF f (SUC x)) (f x)` by ASM_SET_TAC [] \\
          Q.PAT_X_ASSUM `!f. P f`
            (MP_TAC o
             Q.SPEC `\n. if n = 0 then (f x) else
                         if n = 1 then (space d DIFF f (SUC x)) else {}`) \\
          Know `BIGUNION
                 (IMAGE (\n:num. if n = 0 then (f x) else
                                 if n = 1 then (space d DIFF f (SUC x)) else {})
                        UNIV) =
                BIGUNION
                 (IMAGE (\n:num. if n = 0 then (f x) else
                                 if n = 1 then (space d DIFF f (SUC x)) else {})
                        (count 2))`
          >- (MATCH_MP_TAC BIGUNION_IMAGE_UNIV >> RW_TAC arith_ss [])
          >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
          >> RW_TAC bool_ss [COUNT_SUC, IMAGE_INSERT, TWO, ONE, BIGUNION_INSERT,
                             COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY, UNION_EMPTY] \\
          POP_ASSUM MATCH_MP_TAC \\
          CONJ_TAC >- PROVE_TAC [] \\
          rpt GEN_TAC >> PROVE_TAC [DISJOINT_SYM, DISJOINT_EMPTY],
          (* goal 1.2.2 (of 2) *)
          HO_MATCH_MP_TAC TRANSFORM_2D_NUM \\
          CONJ_TAC >- PROVE_TAC [DISJOINT_SYM] \\
          RW_TAC arith_ss [] \\
          Suff `f (SUC i) SUBSET f (i + j)`
          >- (RW_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY,
                             IN_INTER, IN_DIFF, SUBSET_DEF]
              >> PROVE_TAC [])
          >> Cases_on `j` >- PROVE_TAC [ADD_CLAUSES]
          >> POP_ASSUM K_TAC
          >> Know `i + SUC n = SUC i + n` >- DECIDE_TAC
          >> DISCH_THEN (REWRITE_TAC o wrap)
          >> Induct_on `n` >- RW_TAC arith_ss [SUBSET_REFL]
          >> MATCH_MP_TAC SUBSET_TRANS
          >> Q.EXISTS_TAC `f (SUC i + n)`
          >> PROVE_TAC [ADD_CLAUSES] ] ],
      (* goal 2 (of 2) *)
      RW_TAC std_ss [IN_UNIV, IN_FUNSET] >- PROVE_TAC [subset_class_def] \\
      Q.PAT_X_ASSUM `!f. P f`
        (MP_TAC o Q.SPEC `\n. BIGUNION (IMAGE f (count n))`) \\
      BETA_TAC >> STRIP_TAC \\
      Know `BIGUNION (IMAGE f UNIV) =
            BIGUNION (IMAGE (\n. BIGUNION (IMAGE f (count n))) UNIV)`
      >- ( KILL_TAC
        >> ONCE_REWRITE_TAC [EXTENSION]
        >> RW_TAC std_ss [IN_BIGUNION, IN_IMAGE, IN_UNIV]
        >> EQ_TAC
        >- (RW_TAC std_ss []
            >> Q.EXISTS_TAC `BIGUNION (IMAGE f (count (SUC x')))`
            >> RW_TAC std_ss [IN_BIGUNION, IN_IMAGE, IN_COUNT]
            >> PROVE_TAC [LESS_SUC_REFL])
        >> RW_TAC std_ss []
        >> POP_ASSUM MP_TAC
        >> RW_TAC std_ss [IN_BIGUNION, IN_IMAGE, IN_COUNT]
        >> PROVE_TAC [] )
      >> DISCH_THEN (REWRITE_TAC o wrap) \\
      POP_ASSUM MATCH_MP_TAC \\
      SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_COUNT, IN_IMAGE,
                       COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY] \\
      reverse CONJ_TAC
      >- (RW_TAC std_ss [] \\
          Q.EXISTS_TAC `f x'` >> RW_TAC std_ss [] \\
          Q.EXISTS_TAC `x'` >> DECIDE_TAC) \\
      (* !x. BIGUNION (IMAGE f (count x)) IN subsets d *)
      Induct_on `x`
      >- (RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_COUNT, IN_IMAGE,
                         COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY] \\
          REWRITE_TAC [Q.SPEC `space d` (GSYM DIFF_EQ_EMPTY)] \\
          Q.PAT_X_ASSUM `!s t. X ==> t DIFF s IN subsets d` MATCH_MP_TAC \\
          ASM_REWRITE_TAC [SUBSET_REFL]) \\
      (* BIGUNION (IMAGE f (count (SUC x))) IN subsets d *)
      REWRITE_TAC [COUNT_SUC, IMAGE_INSERT, BIGUNION_INSERT] \\
      `f x SUBSET space d` by PROVE_TAC [subset_class_def] \\
      Know `BIGUNION (IMAGE f (count x)) SUBSET space d`
      >- (REWRITE_TAC [BIGUNION_SUBSET] >> GEN_TAC \\
          RW_TAC std_ss [IN_IMAGE] >> PROVE_TAC [subset_class_def]) \\
      DISCH_TAC \\
      `f x UNION (BIGUNION (IMAGE f (count x))) SUBSET space d`
         by PROVE_TAC [UNION_SUBSET] \\
      POP_ASSUM (MP_TAC o SYM o (MATCH_MP DIFF_DIFF_SUBSET)) \\
      ONCE_REWRITE_TAC [DIFF_UNION] \\
      DISCH_THEN (ONCE_REWRITE_TAC o wrap) \\
      Q.PAT_ASSUM `!s t. X ==> t DIFF s IN subsets d` MATCH_MP_TAC \\
      ASM_REWRITE_TAC [DIFF_SUBSET] \\
      reverse CONJ_TAC >- ASM_SET_TAC [] \\
      Q.PAT_ASSUM `!s t. X ==> t DIFF s IN subsets d` MATCH_MP_TAC >> art [] \\
      CONJ_TAC (* 2 subgoals *)
      >- (Q.PAT_ASSUM `!s t. X ==> t DIFF s IN subsets d` MATCH_MP_TAC >> art []) \\
      REWRITE_TAC [SUBSET_DIFF] >> art [] \\
      REWRITE_TAC [DISJOINT_BIGUNION] >> RW_TAC std_ss [IN_IMAGE] \\
      fs [IN_COUNT] ]);

val DYNKIN_SYSTEM_INCREASING = store_thm
  ("DYNKIN_SYSTEM_INCREASING",
   ``!p f.
       dynkin_system p /\ f IN (UNIV -> subsets p) /\ (f 0 = {}) /\
       (!n. f n SUBSET f (SUC n)) ==>
       BIGUNION (IMAGE f UNIV) IN subsets p``,
   RW_TAC std_ss [DYNKIN_SYSTEM_ALT_MONO]);

(* The original definition of `closed_cdi`, plus `(space d) IN (subsets d)` *)
val DYNKIN_SYSTEM_ALT = store_thm
  ("DYNKIN_SYSTEM_ALT",
  ``!d. dynkin_system d <=>
        subset_class (space d) (subsets d) /\
        (space d) IN (subsets d) /\
        (!s. s IN (subsets d) ==> (space d DIFF s) IN (subsets d)) /\
        (!f :num -> 'a set.
          f IN (UNIV -> subsets d) /\ (f 0 = {}) /\ (!n. f n SUBSET f (SUC n)) ==>
          BIGUNION (IMAGE f UNIV) IN (subsets d)) /\
        (!f :num -> 'a set.
          f IN (UNIV -> (subsets d)) /\ (!i j. i <> j ==> DISJOINT (f i) (f j)) ==>
          BIGUNION (IMAGE f UNIV) IN (subsets d))``,
    GEN_TAC >> EQ_TAC
 >> REWRITE_TAC [dynkin_system_def] >> RW_TAC std_ss [IN_UNIV, IN_FUNSET]
 >> Q.PAT_ASSUM `!f. P f ==> Q f` (MP_TAC o Q.SPEC `\n. f (SUC n) DIFF f n`)
 >> BETA_TAC >> STRIP_TAC
 >> Know `BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE (\n. f (SUC n) DIFF f n) UNIV)`
        >- (POP_ASSUM K_TAC
            >> ONCE_REWRITE_TAC [EXTENSION]
            >> RW_TAC std_ss [IN_BIGUNION, IN_IMAGE, IN_UNIV, IN_DIFF]
            >> reverse EQ_TAC
            >- (RW_TAC std_ss []
                >> POP_ASSUM MP_TAC
                >> RW_TAC std_ss [IN_DIFF]
                >> PROVE_TAC [])
            >> RW_TAC std_ss []
            >> Induct_on `x'` >- RW_TAC std_ss [NOT_IN_EMPTY]
            >> RW_TAC std_ss []
            >> Cases_on `x IN f x'` >- PROVE_TAC []
            >> Q.EXISTS_TAC `f (SUC x') DIFF f x'`
            >> RW_TAC std_ss [EXTENSION, IN_DIFF]
            >> PROVE_TAC [])
 >> DISCH_THEN (REWRITE_TAC o wrap)
 >> POP_ASSUM MATCH_MP_TAC
 >> CONJ_TAC (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      GEN_TAC \\
      Know `f (SUC x) DIFF f x = (space d) DIFF ((space d DIFF f (SUC x)) UNION f x)`
      >- (`f x SUBSET space d /\ f (SUC x) SUBSET space d`
             by PROVE_TAC [subset_class_def] \\
          ASM_SET_TAC []) \\
      DISCH_THEN (ONCE_REWRITE_TAC o wrap) \\
      Q.PAT_ASSUM `!s. s IN subsets d ==> P` MATCH_MP_TAC \\
      `space d DIFF f (SUC x) IN subsets d` by PROVE_TAC [] \\
      `DISJOINT (space d DIFF f (SUC x)) (f x)` by ASM_SET_TAC [] \\
      Q.PAT_X_ASSUM `!f. P f`
            (MP_TAC o
             Q.SPEC `\n. if n = 0 then (f x) else
                         if n = 1 then (space d DIFF f (SUC x)) else {}`) \\
      Know `BIGUNION (IMAGE (\n:num. if n = 0 then (f x) else
                                 if n = 1 then (space d DIFF f (SUC x)) else {})
                            UNIV) =
            BIGUNION (IMAGE (\n:num. if n = 0 then (f x) else
                                 if n = 1 then (space d DIFF f (SUC x)) else {})
                            (count 2))`
      >- (MATCH_MP_TAC BIGUNION_IMAGE_UNIV >> RW_TAC arith_ss []) \\
      DISCH_THEN (ONCE_REWRITE_TAC o wrap) \\
      RW_TAC bool_ss [COUNT_SUC, IMAGE_INSERT, TWO, ONE, BIGUNION_INSERT,
                      COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY, UNION_EMPTY] \\
      POP_ASSUM MATCH_MP_TAC \\
      CONJ_TAC >- PROVE_TAC [] \\
      rpt GEN_TAC >> PROVE_TAC [DISJOINT_SYM, DISJOINT_EMPTY],
      (* goal 2 (of 2) *)
      HO_MATCH_MP_TAC TRANSFORM_2D_NUM \\
      CONJ_TAC >- PROVE_TAC [DISJOINT_SYM] \\
      RW_TAC arith_ss [] \\
      Suff `f (SUC i) SUBSET f (i + j)`
      >- (RW_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY,
                         IN_INTER, IN_DIFF, SUBSET_DEF]
          >> PROVE_TAC []) \\
      Cases_on `j` >- PROVE_TAC [ADD_CLAUSES] \\
      POP_ASSUM K_TAC \\
      Know `i + SUC n = SUC i + n` >- DECIDE_TAC \\
      DISCH_THEN (REWRITE_TAC o wrap) \\
      Induct_on `n` >- RW_TAC arith_ss [SUBSET_REFL] \\
      MATCH_MP_TAC SUBSET_TRANS \\
      Q.EXISTS_TAC `f (SUC i + n)` \\
      PROVE_TAC [ADD_CLAUSES] ]);

val SPACE_DYNKIN = store_thm
  ("SPACE_DYNKIN", ``!sp sts. space (dynkin sp sts) = sp``,
    RW_TAC std_ss [dynkin_def, space_def]);

val DYNKIN_SUBSET = store_thm
  ("DYNKIN_SUBSET",
   ``!a b. dynkin_system b /\ a SUBSET (subsets b) ==>
           subsets (dynkin (space b) a) SUBSET (subsets b)``,
   RW_TAC std_ss [dynkin_def, SUBSET_DEF, IN_BIGINTER, GSPECIFICATION, subsets_def]
   >> POP_ASSUM (MATCH_MP_TAC o Q.SPEC `subsets b`)
   >> RW_TAC std_ss [SPACE]);

val DYNKIN_SUBSET_SUBSETS = store_thm
  ("DYNKIN_SUBSET_SUBSETS",
   ``!sp a. a SUBSET subsets (dynkin sp a)``,
   RW_TAC std_ss [dynkin_def, IN_BIGINTER, SUBSET_DEF, GSPECIFICATION, subsets_def]);

val IN_DYNKIN = store_thm
  ("IN_DYNKIN",
   ``!sp a x. x IN a ==> x IN subsets (dynkin sp a)``,
   MP_TAC DYNKIN_SUBSET_SUBSETS
   >> RW_TAC std_ss [SUBSET_DEF]);

val DYNKIN_MONOTONE = store_thm
  ("DYNKIN_MONOTONE",
  ``!sp a b. a SUBSET b ==> (subsets (dynkin sp a)) SUBSET (subsets (dynkin sp b))``,
    RW_TAC std_ss [dynkin_def, SUBSET_DEF, IN_BIGINTER, GSPECIFICATION, subsets_def]);

Theorem DYNKIN_STABLE_LEMMA :
    !sp sts. dynkin_system (sp,sts) ==> (dynkin sp sts = (sp,sts))
Proof
    RW_TAC std_ss [dynkin_def, GSPECIFICATION, space_def, subsets_def]
 >> ASM_SET_TAC []
QED

(* |- !d. dynkin_system d ==> (dynkin (space d) (subsets d) = d) *)
Theorem DYNKIN_STABLE =
    GEN_ALL (REWRITE_RULE [SPACE]
                          (Q.SPECL [`space d`, `subsets d`] DYNKIN_STABLE_LEMMA));

Theorem DYNKIN_SMALLEST :
    !sp sts D. sts SUBSET D /\ D SUBSET subsets (dynkin sp sts) /\
               dynkin_system (sp,D) ==> (D = subsets (dynkin sp sts))
Proof
    RW_TAC std_ss [SET_EQ_SUBSET]
 >> IMP_RES_TAC DYNKIN_STABLE_LEMMA
 >> ‘D = subsets (dynkin sp D)’ by PROVE_TAC [subsets_def]
 >> POP_ORW
 >> MATCH_MP_TAC DYNKIN_MONOTONE >> art []
QED

val DYNKIN = store_thm
  ("DYNKIN",
  ``!sp sts. subset_class sp sts ==>
             sts SUBSET subsets (dynkin sp sts) /\
             dynkin_system (dynkin sp sts) /\
             subset_class sp (subsets (dynkin sp sts))``,
    rpt GEN_TAC
 >> Know `!sp sts. subset_class sp sts ==> sts SUBSET subsets (dynkin sp sts) /\
                                           dynkin_system (dynkin sp sts)`
 >- ( RW_TAC std_ss [dynkin_def, GSPECIFICATION, SUBSET_DEF, INTER_DEF, BIGINTER,
                     subset_class_def, subsets_def, space_def] \\
      RW_TAC std_ss [dynkin_system_def, GSPECIFICATION, IN_BIGINTER, IN_FUNSET,
                     IN_UNIV, subsets_def, space_def, subset_class_def] \\
      POP_ASSUM (MP_TAC o Q.SPEC `{x | x SUBSET sp}`) \\
      RW_TAC std_ss [GSPECIFICATION] \\
      POP_ASSUM MATCH_MP_TAC \\
      RW_TAC std_ss [SUBSET_DEF] \\
      PROVE_TAC [IN_DIFF, IN_BIGUNION, IN_IMAGE, IN_UNIV] )
 >> SIMP_TAC std_ss []
 >> RW_TAC std_ss [dynkin_system_def, SPACE_DYNKIN]);

val SIGMA_PROPERTY_DISJOINT_LEMMA1 = store_thm
  ("SIGMA_PROPERTY_DISJOINT_LEMMA1",
  ``!sp sts.
       algebra (sp,sts) ==>
       (!s t.
          s IN sts /\ t IN subsets (dynkin sp sts) ==>
          s INTER t IN subsets (dynkin sp sts))``,
    RW_TAC std_ss [IN_BIGINTER, GSPECIFICATION, dynkin_def, subsets_def]
 >> Suff
      `t IN
       {b | b IN subsets (dynkin sp sts) /\ s INTER b IN subsets (dynkin sp sts)}`
 >- RW_TAC std_ss [GSPECIFICATION, IN_BIGINTER, dynkin_def, subsets_def]
 >> first_x_assum MATCH_MP_TAC
 >> STRONG_CONJ_TAC
 >- (RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_BIGINTER,
                    dynkin_def, subsets_def] \\
     first_x_assum MATCH_MP_TAC \\
     PROVE_TAC [subsets_def, ALGEBRA_INTER])
 >> `subset_class sp sts` by PROVE_TAC [algebra_def, space_def, subsets_def]
 >> RW_TAC std_ss [GSPECIFICATION, SUBSET_DEF, dynkin_system_def, space_def,
                   subsets_def]
 >| (* 7 subgoals *)
  [ (* goal 1 (of 7) *)
    MP_TAC (UNDISCH (Q.SPECL [`sp`, `sts`] DYNKIN))
    >> RW_TAC std_ss [subset_class_def, SUBSET_DEF, GSPECIFICATION]
    >> PROVE_TAC [algebra_def, subset_class_def, SUBSET_DEF],
    (* goal 2 (of 7) *)
    PROVE_TAC [dynkin_system_def, DYNKIN, SPACE_DYNKIN],
    (* goal 3 (of 7) *)
    `sp IN sts` by PROVE_TAC [ALGEBRA_SPACE, space_def, subsets_def] >> RES_TAC,
    (* goal 4 (of 7) *)
    Know `(sp DIFF s') = space (dynkin sp sts) DIFF s'`
    >- (RW_TAC std_ss [EXTENSION, INTER_DEF, COMPL_DEF, UNION_DEF, GSPECIFICATION,
                       IN_UNIV, IN_DIFF] \\
        PROVE_TAC [SPACE_DYNKIN])
    >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    >> MATCH_MP_TAC DYNKIN_SYSTEM_COMPL
    >> RW_TAC std_ss [DYNKIN],
    (* goal 5 (of 7) *)
    Know `s INTER (sp DIFF s') =
          space (dynkin sp sts) DIFF
                (space (dynkin sp sts) DIFF s UNION (s INTER s'))`
    >- (RW_TAC std_ss [EXTENSION, INTER_DEF, COMPL_DEF, UNION_DEF, GSPECIFICATION,
                       IN_UNIV, IN_DIFF] \\
        PROVE_TAC [SPACE_DYNKIN])
    >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    >> MATCH_MP_TAC DYNKIN_SYSTEM_COMPL
    >> FULL_SIMP_TAC bool_ss [algebra_def, space_def, subsets_def]
    >> RW_TAC std_ss [DYNKIN]
    >> MATCH_MP_TAC DYNKIN_SYSTEM_DUNION
    >> CONJ_TAC
    >- PROVE_TAC [ALGEBRA_EMPTY, DYNKIN, SUBSET_DEF]
    >> CONJ_TAC
    >- (MATCH_MP_TAC DYNKIN_SYSTEM_COMPL
        >> RW_TAC std_ss [DYNKIN])
    >> ASM_REWRITE_TAC []
    >> RW_TAC std_ss [DISJOINT_DEF, COMPL_DEF, INTER_DEF, IN_DIFF, IN_UNIV,
                      GSPECIFICATION, EXTENSION, NOT_IN_EMPTY]
    >> DECIDE_TAC,
    (* goal 6 (of 7) *)
    Q.PAT_X_ASSUM `f IN x` MP_TAC
    >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSPECIFICATION]
    >> MATCH_MP_TAC DYNKIN_SYSTEM_COUNTABLY_DUNION
    >> RW_TAC std_ss [DYNKIN, IN_FUNSET, SUBSET_DEF],
    (* goal 7 (of 7) *)
    Know `s INTER BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE (\n. s INTER f n) UNIV)`
    >- (KILL_TAC \\
        RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, GSPECIFICATION, IN_IMAGE, IN_UNIV,
                       IN_INTER] \\
        EQ_TAC >> RW_TAC std_ss [] >|
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
    >> MATCH_MP_TAC DYNKIN_SYSTEM_COUNTABLY_DUNION
    >> Q.PAT_X_ASSUM `f IN X` MP_TAC
    >> RW_TAC std_ss [DYNKIN, IN_FUNSET, IN_UNIV, GSPECIFICATION]
    >> Q.PAT_X_ASSUM `!i j. X i j` (MP_TAC o Q.SPECL [`i`, `j`])
    >> RW_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY]
    >> PROVE_TAC [] ]);

(* The smallest dynkin system generated from an algebra is stable under finite
   intersection. *)
val SIGMA_PROPERTY_DISJOINT_LEMMA2 = store_thm
  ("SIGMA_PROPERTY_DISJOINT_LEMMA2",
  ``!sp sts.
       algebra (sp,sts) ==>
       (!s t.
          s IN subsets (dynkin sp sts) /\ t IN subsets (dynkin sp sts) ==>
          s INTER t IN subsets (dynkin sp sts))``,
    RW_TAC std_ss []
 >> POP_ASSUM MP_TAC
 >> SIMP_TAC std_ss [dynkin_def, IN_BIGINTER, GSPECIFICATION, subsets_def]
 >> STRIP_TAC >> Q.X_GEN_TAC `P`
 >> Suff
      `t IN
       {b | b IN subsets (dynkin sp sts) /\ s INTER b IN subsets (dynkin sp sts)}`
 >- RW_TAC std_ss [GSPECIFICATION, IN_BIGINTER, dynkin_def, subsets_def]
 >> `subset_class sp sts` by PROVE_TAC [algebra_def, space_def, subsets_def]
 >> Q.PAT_X_ASSUM `!s. P s` MATCH_MP_TAC
 >> STRONG_CONJ_TAC
 >- (RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION] >|
     [PROVE_TAC [DYNKIN, SUBSET_DEF],
      PROVE_TAC [SIGMA_PROPERTY_DISJOINT_LEMMA1, INTER_COMM]])
 >> SIMP_TAC std_ss [GSPECIFICATION, SUBSET_DEF, dynkin_system_def, space_def,
                     subsets_def]
 >> STRIP_TAC >> rpt CONJ_TAC
 >| (* 5 subgoals *)
  [ (* goal 1 (of 5) *)
    (MP_TAC o UNDISCH o Q.SPECL [`sp`, `sts`]) DYNKIN
    >> RW_TAC std_ss [subset_class_def, SUBSET_DEF, GSPECIFICATION]
    >> PROVE_TAC [algebra_def, subset_class_def, SUBSET_DEF],
    (* goal 2 (of 5) *)
    PROVE_TAC [dynkin_system_def, DYNKIN, SPACE_DYNKIN],
    (* goal 3 (of 5) *)
    `sp IN sts` by PROVE_TAC [ALGEBRA_SPACE, space_def, subsets_def] >> RES_TAC,
    (* goal 4 (of 5) *)
    Q.X_GEN_TAC `s'`
    >> rpt STRIP_TAC
    >- PROVE_TAC [dynkin_system_def, DYNKIN, SPACE_DYNKIN]
    >> Know `s INTER (sp DIFF s') =
             space (dynkin sp sts) DIFF
             (space (dynkin sp sts) DIFF s UNION (s INTER s'))`
    >- (RW_TAC std_ss [EXTENSION, INTER_DEF, COMPL_DEF, UNION_DEF, GSPECIFICATION,
                       IN_UNIV, IN_DIFF, SPACE_DYNKIN] \\
        DECIDE_TAC)
    >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    >> MATCH_MP_TAC DYNKIN_SYSTEM_COMPL
    >> RW_TAC std_ss [DYNKIN]
    >> MATCH_MP_TAC DYNKIN_SYSTEM_DUNION
    >> CONJ_TAC
    >- PROVE_TAC [ALGEBRA_EMPTY, DYNKIN, SUBSET_DEF]
    >> CONJ_TAC
    >- (MATCH_MP_TAC DYNKIN_SYSTEM_COMPL
        >> RW_TAC std_ss [DYNKIN])
    >> ASM_REWRITE_TAC []
    >> RW_TAC std_ss [DISJOINT_DEF, COMPL_DEF, INTER_DEF, IN_DIFF, IN_UNIV,
                      GSPECIFICATION, EXTENSION, NOT_IN_EMPTY]
    >> DECIDE_TAC,
    (* goal 5 (of 5) *)
    Q.X_GEN_TAC `f` >> rpt STRIP_TAC
    >- (Q.PAT_X_ASSUM `f IN x` MP_TAC
        >> RW_TAC std_ss [IN_FUNSET, IN_UNIV, GSPECIFICATION]
        >> MATCH_MP_TAC DYNKIN_SYSTEM_COUNTABLY_DUNION
        >> RW_TAC std_ss [DYNKIN, IN_FUNSET, SUBSET_DEF])
    >> Know
        `s INTER BIGUNION (IMAGE f UNIV) =
         BIGUNION (IMAGE (\n. s INTER f n) UNIV)`
    >- (KILL_TAC \\
        RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, GSPECIFICATION, IN_IMAGE, IN_UNIV,
                       IN_INTER] \\
        EQ_TAC >> RW_TAC std_ss [] >|
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
    >> MATCH_MP_TAC DYNKIN_SYSTEM_COUNTABLY_DUNION
    >> Q.PAT_X_ASSUM `f IN X` MP_TAC
    >> RW_TAC std_ss [DYNKIN, IN_FUNSET, IN_UNIV, GSPECIFICATION]
    >> Q.PAT_X_ASSUM `!i j. X i j` (MP_TAC o Q.SPECL [`i`, `j`])
    >> RW_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY]
    >> PROVE_TAC [] ]);

(* If an algebra is contained in a dynkin system, then the smallest sigma-algebra
   generated from it is also contained in the dynkin system.
 *)
val SIGMA_PROPERTY_DISJOINT_LEMMA = store_thm
  ("SIGMA_PROPERTY_DISJOINT_LEMMA",
   ``!sp a d. algebra (sp,a) /\ a SUBSET d /\ dynkin_system (sp,d)
          ==> subsets (sigma sp a) SUBSET d``,
   RW_TAC std_ss []
   >> MATCH_MP_TAC SUBSET_TRANS
   >> Q.EXISTS_TAC `subsets (dynkin sp a)`
   >> reverse CONJ_TAC
   >- (RW_TAC std_ss [SUBSET_DEF, dynkin_def, IN_BIGINTER,
                      GSPECIFICATION, subsets_def, space_def]
       >> PROVE_TAC [SUBSET_DEF])
   >> NTAC 2 (POP_ASSUM K_TAC)
   >> Suff `subsets (dynkin sp a) IN {b | a SUBSET b /\ sigma_algebra (sp,b)}`
   >- (KILL_TAC \\
       RW_TAC std_ss [sigma_def, BIGINTER, SUBSET_DEF, GSPECIFICATION, subsets_def])
   >> `subset_class sp a` by PROVE_TAC [algebra_def, space_def, subsets_def]
   >> RW_TAC std_ss [GSPECIFICATION, SIGMA_ALGEBRA_ALT_DISJOINT,
                     ALGEBRA_ALT_INTER, space_def, subsets_def] >|
   [PROVE_TAC [DYNKIN, subsets_def],
    PROVE_TAC [DYNKIN, space_def],
    PROVE_TAC [ALGEBRA_EMPTY, SUBSET_DEF, DYNKIN, space_def, subsets_def],
    PROVE_TAC [DYNKIN, DYNKIN_SYSTEM_COMPL, space_def, SPACE_DYNKIN],
    PROVE_TAC [SIGMA_PROPERTY_DISJOINT_LEMMA2],
    PROVE_TAC [DYNKIN, DYNKIN_SYSTEM_COUNTABLY_DUNION]]);

val SIGMA_PROPERTY_DISJOINT_WEAK_ALT = store_thm (* renamed *)
  ("SIGMA_PROPERTY_DISJOINT_WEAK_ALT",
   ``!sp p a.
       algebra (sp, a) /\ a SUBSET p /\
       subset_class sp p /\
       (!s. s IN p ==> sp DIFF s IN p) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> p) /\ (f 0 = {}) /\ (!n. f n SUBSET f (SUC n)) ==>
          BIGUNION (IMAGE f UNIV) IN p) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> p) /\ (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
          BIGUNION (IMAGE f UNIV) IN p) ==>
       subsets (sigma sp a) SUBSET p``,
   RW_TAC std_ss []
   >> MATCH_MP_TAC (Q.SPECL [`sp`, `a`, `p`] SIGMA_PROPERTY_DISJOINT_LEMMA)
   >> RW_TAC std_ss [dynkin_system_def, space_def, subsets_def]
   >> `sp IN a` by PROVE_TAC [ALGEBRA_SPACE, space_def, subsets_def]
   >> PROVE_TAC [SUBSET_DEF]);

val SIGMA_PROPERTY_DISJOINT = store_thm
  ("SIGMA_PROPERTY_DISJOINT",
  ``!sp p a.
       algebra (sp,a) /\ a SUBSET p /\
       (!s. s IN (p INTER subsets (sigma sp a)) ==> sp DIFF s IN p) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> p INTER subsets (sigma sp a)) /\ (f 0 = {}) /\
          (!n. f n SUBSET f (SUC n)) ==>
          BIGUNION (IMAGE f UNIV) IN p) /\
       (!f : num -> 'a -> bool.
          f IN (UNIV -> p INTER subsets (sigma sp a)) /\
          (!i j. i <> j ==> DISJOINT (f i) (f j)) ==>
          BIGUNION (IMAGE f UNIV) IN p) ==>
       subsets (sigma sp a) SUBSET p``,
    RW_TAC std_ss [IN_FUNSET, IN_UNIV, IN_INTER]
 >> Suff `subsets (sigma sp a) SUBSET p INTER subsets (sigma sp a)`
 >- (KILL_TAC
     >> SIMP_TAC std_ss [SUBSET_INTER])
 >> MATCH_MP_TAC
      (Q.SPECL [`sp`, `p INTER subsets (sigma sp a)`, `a`]
               SIGMA_PROPERTY_DISJOINT_WEAK_ALT)
 >> RW_TAC std_ss [SUBSET_INTER, IN_INTER, IN_FUNSET, IN_UNIV]
 >| (* 5 subgoals *)
  [ (* goal 1 (of 5) *)
    REWRITE_TAC [SIGMA_SUBSET_SUBSETS],
    (* goal 2 (of 5) *)
    REWRITE_TAC [subset_class_def] \\
    RW_TAC std_ss [IN_INTER] \\
    `subset_class sp a` by PROVE_TAC [algebra_def, space_def, subsets_def] \\
    POP_ASSUM (MP_TAC o (MATCH_MP SIGMA_ALGEBRA_SIGMA)) \\
    RW_TAC std_ss [sigma_algebra_def, algebra_def, space_def, subsets_def,
                   SPACE_SIGMA] \\
    fs [subset_class_def],
    (* goal (3 of 5) *)
    (MP_TAC o Q.SPECL [`sp`,`a`]) SIGMA_ALGEBRA_SIGMA
    >> Q.PAT_X_ASSUM `algebra (sp,a)` MP_TAC
    >> RW_TAC std_ss [algebra_def, space_def, subsets_def]
    >> POP_ASSUM MP_TAC
    >> NTAC 3 (POP_ASSUM (K ALL_TAC))
    >> Know `space (sigma sp a) = sp` >- RW_TAC std_ss [sigma_def, space_def]
    >> RW_TAC std_ss [SIGMA_ALGEBRA, algebra_def, subsets_def, space_def],
    (* goal 4 (of 5) *)
    MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION
    >> Q.PAT_X_ASSUM `algebra (sp,a)` MP_TAC
    >> RW_TAC std_ss [SIGMA_ALGEBRA_SIGMA, COUNTABLE_IMAGE_NUM, SUBSET_DEF,
                      IN_IMAGE, IN_UNIV, algebra_def, subsets_def, space_def]
    >> PROVE_TAC [],
    (* goal 5 (of 5) *)
    MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UNION
    >> Q.PAT_X_ASSUM `algebra (sp,a)` MP_TAC
    >> RW_TAC std_ss [SIGMA_ALGEBRA_SIGMA, COUNTABLE_IMAGE_NUM, SUBSET_DEF,
                      IN_IMAGE, IN_UNIV, algebra_def, subsets_def, space_def]
    >> PROVE_TAC [] ]);

(* Every sigma-algebra is a Dynkin system *)
val SIGMA_ALGEBRA_IMP_DYNKIN_SYSTEM = store_thm
  ("SIGMA_ALGEBRA_IMP_DYNKIN_SYSTEM", ``!a. sigma_algebra a ==> dynkin_system a``,
    rpt STRIP_TAC
 >> REWRITE_TAC [dynkin_system_def]
 >> CONJ_TAC >- PROVE_TAC [SIGMA_ALGEBRA]
 >> CONJ_TAC >- PROVE_TAC [sigma_algebra_def, ALGEBRA_SPACE]
 >> CONJ_TAC >- PROVE_TAC [SIGMA_ALGEBRA]
 >> PROVE_TAC [SIGMA_ALGEBRA_ALT]);

(* A Dynkin system d is a sigma-algebra iff it is stable under finite intersections *)
val DYNKIN_LEMMA = store_thm
  ("DYNKIN_LEMMA",
  ``!d. dynkin_system d /\
       (!s t. s IN subsets d /\ t IN subsets d ==> s INTER t IN subsets d)
        <=> sigma_algebra d``,
    GEN_TAC >> reverse EQ_TAC
 >- (rpt STRIP_TAC >- IMP_RES_TAC SIGMA_ALGEBRA_IMP_DYNKIN_SYSTEM \\
     MATCH_MP_TAC ALGEBRA_INTER >> PROVE_TAC [sigma_algebra_def])
 >> rpt STRIP_TAC
 (* it remains to show that a INTER-stable Dynkin system is sigma-algebra *)
 >> REWRITE_TAC [SIGMA_ALGEBRA_ALT, ALGEBRA_ALT_INTER]
 >> rpt CONJ_TAC >- PROVE_TAC [dynkin_system_def]
 >- PROVE_TAC [DYNKIN_SYSTEM_EMPTY]
 >- PROVE_TAC [dynkin_system_def]
 >- ASM_REWRITE_TAC []
 (* now the last hard part *)
 >> rpt STRIP_TAC
 >> `subset_class (space d) (subsets d)` by PROVE_TAC [dynkin_system_def]
 >> fs [subset_class_def, IN_FUNSET, IN_UNIV]
 >> MP_TAC (Q.SPECL [`space d`, `subsets d`, `f`] SETS_TO_DISJOINT_SETS)
 >> RW_TAC std_ss []
 >> POP_ASSUM (REWRITE_TAC o wrap)
 >> MATCH_MP_TAC DYNKIN_SYSTEM_COUNTABLY_DUNION
 >> fs [IN_FUNSET, IN_UNIV]
(* !x. g x IN subsets d *)
 >> MP_TAC (Q.SPECL [`subsets d`, `\i. space d DIFF f i`] DINTER_IMP_FINITE_INTER)
 >> Know `(\i. space d DIFF f i) IN (UNIV -> subsets d)`
 >- (SIMP_TAC std_ss [IN_FUNSET, IN_UNIV] \\
     GEN_TAC >> MATCH_MP_TAC DYNKIN_SYSTEM_COMPL >> art [])
 >> RW_TAC std_ss []
 >> STRIP_ASSUME_TAC (Q.SPEC `x` LESS_0_CASES) >- fs []
 >> Q.PAT_X_ASSUM `!n. 0 < n ==> (g n = X)`
        (fn th => MP_TAC (MATCH_MP th (ASSUME ``0 < x:num``)))
 >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
 >> PROVE_TAC []);

val DYNKIN_SUBSET_SIGMA = store_thm
  ("DYNKIN_SUBSET_SIGMA",
  ``!sp sts. subset_class sp sts ==>
             subsets (dynkin sp sts) SUBSET subsets (sigma sp sts)``,
    rpt STRIP_TAC
 >> ASSUME_TAC
      (Q.SPEC `sp` (MATCH_MP DYNKIN_MONOTONE
                            (Q.SPECL [`sp`, `sts`] SIGMA_SUBSET_SUBSETS)))
 >> Suff `subsets (dynkin sp (subsets (sigma sp sts))) = subsets (sigma sp sts)`
 >- PROVE_TAC []
 >> IMP_RES_TAC SIGMA_ALGEBRA_SIGMA
 >> IMP_RES_TAC SIGMA_ALGEBRA_IMP_DYNKIN_SYSTEM
 >> POP_ASSUM (MP_TAC o (MATCH_MP DYNKIN_STABLE))
 >> REWRITE_TAC [SPACE_SIGMA]
 >> DISCH_THEN (ASM_REWRITE_TAC o wrap));

(* if generator is stable under finite intersections, then dynkin(g) = sigma(g) *)
val DYNKIN_THM = store_thm
  ("DYNKIN_THM",
  ``!sp sts. subset_class sp sts /\ (!s t. s IN sts /\ t IN sts ==> s INTER t IN sts)
         ==> (dynkin sp sts = sigma sp sts)``,
    rpt STRIP_TAC
 >> ONCE_REWRITE_TAC [SYM (Q.SPEC `dynkin sp sts` SPACE),
                      SYM (Q.SPEC `sigma sp sts` SPACE)]
 >> REWRITE_TAC [SPACE_DYNKIN, SPACE_SIGMA]
 >> SIMP_TAC std_ss []
 >> REWRITE_TAC [SET_EQ_SUBSET]
 >> CONJ_TAC >- IMP_RES_TAC DYNKIN_SUBSET_SIGMA
 (* goal: subsets (sigma sp sts) SUBSET subsets (dynkin sp sts) *)
 >> Suff `sigma_algebra (dynkin sp sts)`
 >- (DISCH_TAC \\
     ASSUME_TAC (Q.SPECL [`sp`, `sts`] DYNKIN_SUBSET_SUBSETS) \\
     POP_ASSUM (ASSUME_TAC o (Q.SPEC `sp`) o (MATCH_MP SIGMA_MONOTONE)) \\
     IMP_RES_TAC SIGMA_STABLE \\
     fs [SPACE_DYNKIN])
 (* goal: sigma_algebra (dynkin sp sts) *)
 >> REWRITE_TAC [GSYM DYNKIN_LEMMA]
 >> CONJ_TAC >- PROVE_TAC [DYNKIN]
 (* goal: (dynkin sp sts) is INTER-stable *)
 >> Q.ABBREV_TAC
     `D = \d. (sp, {q | q SUBSET sp /\ q INTER d IN (subsets (dynkin sp sts))})`
 >> Suff `!d. d IN subsets (dynkin sp sts) ==> dynkin_system (D d)`
 >- (DISCH_TAC \\
     ASSUME_TAC (Q.SPECL [`sp`, `sts`] DYNKIN_SUBSET_SUBSETS) \\
     Know `!g. g IN sts ==> sts SUBSET (subsets (D g))`
     >- (REWRITE_TAC [SUBSET_DEF] >> rpt STRIP_TAC \\
         `x INTER g IN sts` by PROVE_TAC [] \\
         Q.UNABBREV_TAC `D` >> BETA_TAC \\
         RW_TAC std_ss [subsets_def, GSPECIFICATION]
         >- PROVE_TAC [subset_class_def] \\
         PROVE_TAC [DYNKIN_SUBSET_SUBSETS, SUBSET_DEF]) >> DISCH_TAC \\
     Know `!g. g IN sts ==> subsets (dynkin sp sts) SUBSET subsets (D g)`
     >- (rpt STRIP_TAC \\
         `sts SUBSET subsets (D g)` by PROVE_TAC [] \\
         POP_ASSUM (MP_TAC o (Q.SPEC `sp`) o (MATCH_MP DYNKIN_MONOTONE)) \\
         `dynkin_system (D g)` by PROVE_TAC [SUBSET_DEF] \\
         POP_ASSUM (MP_TAC o (MATCH_MP DYNKIN_STABLE)) \\
         `space (D g) = sp` by METIS_TAC [space_def] \\
         POP_ASSUM (REWRITE_TAC o wrap) \\
         DISCH_THEN (ASM_REWRITE_TAC o wrap)) >> DISCH_TAC \\
     Know `!g d. g IN sts /\ d IN subsets (dynkin sp sts) ==>
                 d INTER g IN subsets (dynkin sp sts)`
     >- (rpt STRIP_TAC \\
         `d IN subsets (D g)` by PROVE_TAC [SUBSET_DEF] \\
         POP_ASSUM MP_TAC \\
         Q.UNABBREV_TAC `D` >> BETA_TAC \\
         RW_TAC std_ss [subsets_def, GSPECIFICATION]) >> DISCH_TAC \\
     Know `!d. d IN subsets (dynkin sp sts) ==> sts SUBSET subsets (D d)`
     >- (rpt STRIP_TAC \\
         REWRITE_TAC [SUBSET_DEF] >> rpt STRIP_TAC \\
         Q.UNABBREV_TAC `D` >> BETA_TAC \\
         RW_TAC std_ss [subsets_def, GSPECIFICATION]
         >- PROVE_TAC [subset_class_def] \\
         ONCE_REWRITE_TAC [INTER_COMM] \\
         PROVE_TAC []) >> DISCH_TAC \\
     Know `!d. d IN subsets (dynkin sp sts) ==>
               subsets (dynkin sp sts) SUBSET subsets (D d)`
     >- (rpt STRIP_TAC \\
         `sts SUBSET subsets (D d)` by PROVE_TAC [] \\
         POP_ASSUM (MP_TAC o (Q.SPEC `sp`) o (MATCH_MP DYNKIN_MONOTONE)) \\
         `dynkin_system (D d)` by PROVE_TAC [SUBSET_DEF] \\
         POP_ASSUM (MP_TAC o (MATCH_MP DYNKIN_STABLE)) \\
         `space (D d) = sp` by METIS_TAC [space_def] \\
         POP_ASSUM (REWRITE_TAC o wrap) \\
         DISCH_THEN (ASM_REWRITE_TAC o wrap)) >> DISCH_TAC \\
     rpt STRIP_TAC \\
     `subsets (dynkin sp sts) SUBSET subsets (D t)` by PROVE_TAC [] \\
     POP_ASSUM MP_TAC \\
     REWRITE_TAC [SUBSET_DEF] >> rpt STRIP_TAC \\
     `s IN subsets (D t)` by PROVE_TAC [] \\
     POP_ASSUM MP_TAC \\
     Q.UNABBREV_TAC `D` >> BETA_TAC \\
     RW_TAC std_ss [subsets_def, GSPECIFICATION])
 (* !d. d IN subsets (dynkin sp sts) ==> dynkin_system (D d) *)
 >> rpt STRIP_TAC
 >> REWRITE_TAC [dynkin_system_def]
 >> STRONG_CONJ_TAC
 >- (FULL_SIMP_TAC std_ss [subset_class_def] \\
     GEN_TAC >> Q.UNABBREV_TAC `D` >> BETA_TAC \\
     RW_TAC std_ss [subsets_def, GSPECIFICATION, space_def])
 >> DISCH_TAC
 >> STRONG_CONJ_TAC
 >- (Q.UNABBREV_TAC `D` >> BETA_TAC \\
     RW_TAC std_ss [GSPECIFICATION, space_def, subsets_def, SUBSET_REFL] \\
     fs [space_def, subsets_def] \\
     STRIP_ASSUME_TAC (MATCH_MP DYNKIN (ASSUME ``subset_class sp sts``)) \\
     `d SUBSET sp` by PROVE_TAC [subset_class_def] \\
     `sp INTER d = d` by PROVE_TAC [INTER_SUBSET_EQN] \\
     POP_ASSUM (ASM_REWRITE_TAC o wrap))
 >> DISCH_TAC
 >> STRONG_CONJ_TAC
 >- ((* !s. s IN subsets (D d) ==> space (D d) DIFF s IN subsets (D d) *)
     `space (D d) = sp` by METIS_TAC [space_def]\\
     POP_ASSUM (fs o wrap) \\
     rpt STRIP_TAC \\
     Q.UNABBREV_TAC `D` >> fs [subsets_def] \\
     Know `(sp DIFF s) INTER d = sp DIFF ((s INTER d) UNION (sp DIFF d))`
     >- ASM_SET_TAC [] \\
     DISCH_THEN (REWRITE_TAC o wrap) \\
     `dynkin_system (dynkin sp sts)` by PROVE_TAC [DYNKIN] \\
     MATCH_MP_TAC (REWRITE_RULE [SPACE_DYNKIN]
                     (Q.SPEC `dynkin sp sts` DYNKIN_SYSTEM_COMPL)) \\
     ASM_REWRITE_TAC [] \\
     `DISJOINT (s INTER d) (sp DIFF d)` by ASM_SET_TAC [] \\
     MATCH_MP_TAC (Q.SPEC `dynkin sp sts` DYNKIN_SYSTEM_DUNION) \\
     ASM_REWRITE_TAC [] \\
     MATCH_MP_TAC (REWRITE_RULE [SPACE_DYNKIN]
                     (Q.SPEC `dynkin sp sts` DYNKIN_SYSTEM_COMPL)) \\
     ASM_REWRITE_TAC [])
 >> DISCH_TAC
 (* final goal *)
 >> rpt STRIP_TAC
 >> `!i j. i <> i ==> DISJOINT (f i INTER d) (f j INTER d)` by ASM_SET_TAC []
 >> Q.UNABBREV_TAC `D` >> BETA_TAC
 >> REWRITE_TAC [subsets_def]
 >> RW_TAC std_ss [GSPECIFICATION]
 >- (REWRITE_TAC [BIGUNION_SUBSET, IN_IMAGE] \\
     rpt STRIP_TAC >> fs [subsets_def, IN_FUNSET, IN_UNIV])
 >> fs [subsets_def, IN_FUNSET, IN_UNIV]
 >> REWRITE_TAC [BIGUNION_OVER_INTER_L]
 >> fs [space_def]
 >> MATCH_MP_TAC DYNKIN_SYSTEM_COUNTABLY_DUNION
 >> CONJ_TAC >- PROVE_TAC [DYNKIN]
 >> CONJ_TAC >- (REWRITE_TAC [IN_FUNSET, IN_UNIV] >> PROVE_TAC [])
 >> rpt STRIP_TAC
 >> `DISJOINT (f i) (f j)` by PROVE_TAC []
 >> BETA_TAC >> ASM_SET_TAC []);

(* This theorem is a stronger version of SIGMA_PROPERTY_DISJOINT_LEMMA, requiring
   only closure of (finite) intersections instead of a full algebra.
 *)
Theorem SIGMA_PROPERTY_DYNKIN :
    !sp sts d.
          subset_class sp sts /\
         (!s t. s IN sts /\ t IN sts ==> s INTER t IN sts) /\
          sts SUBSET d /\ dynkin_system (sp,d) ==>
          subsets (sigma sp sts) SUBSET d
Proof
    rpt STRIP_TAC
 (* applying DYNKIN_THM *)
 >> Know ‘sigma sp sts = dynkin sp sts’
 >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     MATCH_MP_TAC DYNKIN_THM >> art [])
 >> Rewr'
 (* applying DYNKIN_SUBSET *)
 >> qabbrev_tac ‘b = (sp,d)’
 >> ‘d = subsets b’ by rw [Abbr ‘b’] >> POP_ORW
 >> ‘sp = space b’ by rw [Abbr ‘b’] >> POP_ORW
 >> MATCH_MP_TAC DYNKIN_SUBSET
 >> simp [Abbr ‘b’]
QED

(* ------------------------------------------------------------------------- *)
(*  Some further additions by Concordia HVG (M. Qasim & W. Ahmed)            *)
(* ------------------------------------------------------------------------- *)

(* |- !sp sts.
        semiring (sp,sts) <=>
        subset_class sp sts /\ {} IN sts /\
        (!s t. s IN sts /\ t IN sts ==> s INTER t IN sts) /\
        !s t.
          s IN sts /\ t IN sts ==>
          ?c. c SUBSET sts /\ FINITE c /\ disjoint c /\ s DIFF t = BIGUNION c
 *)
Theorem semiring_alt = semiring_def |> (Q.SPEC ‘(sp,sts)’)
                                    |> REWRITE_RULE [space_def, subsets_def]
                                    |> Q.GENL [‘sp’, ‘sts’]

Theorem INTER_SPACE_EQ1 : (* was: Int_space_eq1 *)
    !sp sts . subset_class sp sts ==> !x. x IN sts ==> (sp INTER x = x)
Proof
    rpt GEN_TAC THEN SET_TAC [subset_class_def]
QED

Theorem INTER_SPACE_REDUCE : (* was: Int_space_eq2 *)
    !sp sts. subset_class sp sts ==> !x. x IN sts ==> (x INTER sp = x)
Proof
    rpt GEN_TAC THEN SET_TAC [subset_class_def]
QED

Theorem SEMIRING_SETS_COLLECT : (* was: sets_Collect_conj *)
    !sp sts P Q. semiring (sp, sts) /\
                {x | x IN sp /\ P x} IN sts /\
                {x | x IN sp /\ Q x} IN sts ==>
                {x | x IN sp /\ P x /\ Q x} IN sts
Proof
    rpt GEN_TAC
 >> SIMP_TAC std_ss [semiring_def, space_def, subsets_def]
 >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!s t. s IN sts /\ t IN sts ==> ?c. _’ K_TAC
 >> FIRST_X_ASSUM (MP_TAC o Q.SPECL [‘{x | x IN sp /\ P x}’, ‘{x | x IN sp /\ Q x}’])
 >> ASM_SIMP_TAC std_ss [GSPECIFICATION, INTER_DEF]
 >> REWRITE_TAC [SET_RULE “(A /\ B) /\ A /\ C <=> A /\ B /\ C”]
QED

(* |- !sp sts.
        ring (sp,sts) <=>
        subset_class sp sts /\ {} IN sts /\
        (!s t. s IN sts /\ t IN sts ==> s UNION t IN sts) /\
        !s t. s IN sts /\ t IN sts ==> s DIFF t IN sts
 *)
Theorem ring_alt = ring_def |> Q.SPEC ‘(sp,sts)’
                            |> REWRITE_RULE [space_def, subsets_def]
                            |> Q.GENL [‘sp’, ‘sts’]

(* A semiring becomes a ring if it's stable under finite union *)
val ring_and_semiring = store_thm
  ("ring_and_semiring",
  ``!r. ring r <=>
        semiring r /\
        !s t. s IN (subsets r) /\ t IN (subsets r) ==> s UNION t IN (subsets r)``,
    GEN_TAC >> EQ_TAC >> RW_TAC std_ss []
 >- (MATCH_MP_TAC RING_IMP_SEMIRING >> art [])
 >- (MATCH_MP_TAC RING_UNION >> art [])
 >> RW_TAC std_ss [ring_def] >> fs [semiring_def]
 >> Q.PAT_X_ASSUM `!s t. s IN subsets r /\ t IN subsets r ==> ?c. X`
      (MP_TAC o (Q.SPECL [`s`, `t`]))
 >> RW_TAC std_ss []
 >> POP_ORW
 >> IMP_RES_TAC finite_decomposition_simple
 >> Cases_on `n = 0`
 >- (fs [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY])
 >> `0 < n` by RW_TAC arith_ss []
 >> fs [SUBSET_DEF, IN_IMAGE, IN_COUNT]
 >> irule DUNION_IMP_FINITE_UNION >> art []
 >> RW_TAC std_ss []);

Theorem RING_FINITE_BIGUNION1 : (* was: finite_Union *)
    !X sp sts. ring (sp, sts) /\ FINITE X ==> X SUBSET sts ==> BIGUNION X IN sts
Proof
  rpt GEN_TAC THEN
  REWRITE_TAC [ring_def,subsets_def] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC (``X:('a->bool)->bool``,``X:('a->bool)->bool``) THEN
  SET_INDUCT_TAC THENL
  [FULL_SIMP_TAC std_ss [semiring_def, BIGUNION_EMPTY], ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC [BIGUNION_INSERT] THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_SET_TAC []
QED

Theorem RING_FINITE_BIGUNION2 : (* was: finite_UN *)
    !A N sp sts. ring (sp, sts) /\ FINITE N /\ (!i. i IN N ==> A i IN sts) ==>
                 BIGUNION {A i | i IN N} IN sts
Proof
  rpt GEN_TAC THEN
  REWRITE_TAC [ring_def,subsets_def] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC (``N:'a->bool``,``N:'a->bool``) THEN
  SET_INDUCT_TAC THENL
  [REWRITE_TAC [SET_RULE ``{A i | i IN {}} = {}``, BIGUNION_EMPTY] THEN
   FULL_SIMP_TAC std_ss [semiring_def], ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC [IN_INSERT] THEN
  REWRITE_TAC [SET_RULE ``BIGUNION {A i | (i = e) \/ i IN s} =
               BIGUNION {A e} UNION BIGUNION {A i | i IN s}``] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [BIGUNION_SING] THEN
  ASM_SET_TAC []
QED

Theorem RING_DIFF_ALT : (* was: Diff *)
    !a b sp sts. ring (sp, sts) /\ a IN sts /\ b IN sts ==> a DIFF b IN sts
Proof
  rpt GEN_TAC THEN REWRITE_TAC [ring_def,subsets_def, semiring_def] THEN
  STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  FIRST_ASSUM (MP_TAC o SPECL [``a:'a->bool``,``b:'a->bool``]) THEN
  rpt STRIP_TAC THEN FULL_SIMP_TAC std_ss [] THEN
  UNDISCH_TAC ``c SUBSET sts:('a->bool)->bool`` THEN
  MATCH_MP_TAC RING_FINITE_BIGUNION1 THEN
  EXISTS_TAC ``sp:'a->bool`` THEN
  FULL_SIMP_TAC std_ss [ring_def, subsets_def, semiring_def]
QED

Theorem ring_alt_pow_imp : (* was: ring_of_setsI *)
    !sp sts. sts SUBSET POW sp /\ {} IN sts /\
            (!a b. a IN sts /\ b IN sts ==> a UNION b IN sts) /\
            (!a b. a IN sts /\ b IN sts ==> a DIFF b IN sts) ==> ring (sp, sts)
Proof
  REWRITE_TAC [ring_def, subsets_def, semiring_def, subset_class_def, POW_DEF] THEN
  REWRITE_TAC [SET_RULE ``sts SUBSET {s | s SUBSET sp} <=>
                !x. x IN sts ==> x SUBSET sp``] THEN
  rpt STRIP_TAC THEN ASM_SIMP_TAC std_ss [space_def] THENL
  [REWRITE_TAC [SET_RULE ``s INTER t = s DIFF (s DIFF t)``] THEN
   ASM_SET_TAC [], ALL_TAC] THEN
  REWRITE_TAC [disjoint] THEN EXISTS_TAC ``{(s:'a->bool) DIFF t}`` THEN
  SIMP_TAC std_ss [BIGUNION_SING, FINITE_SING, IN_SING, SUBSET_DEF] THEN
  ASM_SET_TAC []
QED

Theorem ring_alt_pow : (* was: ring_of_sets_iff *)
    !sp sts. ring (sp, sts) <=>
             sts SUBSET POW sp /\ {} IN sts /\
             (!s t. s IN sts /\ t IN sts ==> s UNION t IN sts) /\
             (!s t. s IN sts /\ t IN sts ==> s DIFF t IN sts)
Proof
    rpt GEN_TAC
 >> reverse EQ_TAC >- METIS_TAC [ring_alt_pow_imp]
 >> REWRITE_TAC [ring_def, subsets_def, space_def, semiring_def, subset_class_def,
                 POW_DEF]
 >> REWRITE_TAC [SET_RULE ``sts SUBSET {s | s SUBSET sp} <=>
                            !x. x IN sts ==> x SUBSET sp``]
 >> rpt STRIP_TAC
 >> ASM_SIMP_TAC std_ss []
 >> MATCH_MP_TAC RING_DIFF_ALT
 >> EXISTS_TAC ``sp:'a->bool``
 >> ASM_SIMP_TAC std_ss [ring_def, space_def, subsets_def, semiring_def,
                         subset_class_def]
QED

Theorem RING_BIGUNION : (* was: UNION_in_sets *)
    !sp sts (A:num->'a->bool) n.
        ring (sp,sts) /\ IMAGE A UNIV SUBSET sts ==>
        BIGUNION {A i | i < n} IN sts
Proof
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [SIMP_TAC std_ss [GSPECIFICATION] THEN
   REWRITE_TAC [SET_RULE ``{A i | i | F} = {}``] THEN
   SIMP_TAC std_ss [BIGUNION_EMPTY, ring_alt, semiring_alt],
   ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [GSPECIFICATION] THEN
  RW_TAC std_ss [ARITH_PROVE ``i < SUC n <=> i < n \/ (i = n)``] THEN
  REWRITE_TAC [SET_RULE ``BIGUNION {(A:num->'a->bool) i | i < n \/ (i = n)} =
                          BIGUNION {A i | i < n} UNION A n``] THEN
  FULL_SIMP_TAC std_ss [ring_alt_pow] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN FULL_SIMP_TAC std_ss [SUBSET_DEF] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN SET_TAC []
QED

Theorem ring_disjointed_sets : (* was: range_disjointed_sets *)
    !sp sts A. ring (sp,sts) /\ IMAGE A UNIV SUBSET sts ==>
               IMAGE (\n. disjointed A n) UNIV SUBSET sts
Proof
  RW_TAC std_ss [disjointed] THEN
  SIMP_TAC std_ss [IN_IMAGE, SUBSET_DEF, IN_UNIV] THEN
  FULL_SIMP_TAC std_ss [GSPECIFICATION, ring_alt_pow] THEN
  RW_TAC std_ss [] THEN FIRST_ASSUM MATCH_MP_TAC THEN
  KNOW_TAC
  ``BIGUNION {(A:num->'a->bool) i | i IN {x | 0 <= x /\ x < n}} IN sts`` THENL
  [SIMP_TAC std_ss [GSPECIFICATION] THEN
   MATCH_MP_TAC RING_BIGUNION THEN SIMP_TAC std_ss [ring_alt_pow] THEN
   METIS_TAC [], DISCH_TAC] THEN
  FULL_SIMP_TAC std_ss [GSPECIFICATION, SUBSET_DEF] THEN ASM_SET_TAC []
QED

Theorem RING_INSERT : (* was: insert_in_sets *)
    !x A sp sts. ring (sp,sts) /\ {x} IN sts /\ A IN sts ==> x INSERT A IN sts
Proof
  REWRITE_TAC [ring_def, subsets_def, space_def] THEN rpt STRIP_TAC THEN
  ONCE_REWRITE_TAC [SET_RULE ``x INSERT A = {x} UNION A``] THEN
  ASM_SET_TAC []
QED

Theorem RING_SETS_COLLECT_FINITE : (* was: sets_collect_finite_Ex *)
    !sp sts s P. ring (sp, sts) /\
                 (!i. i IN s ==> {x | x IN sp /\ P i x} IN sts) /\ FINITE s
             ==> {x | x IN sp /\ (?i. i IN s /\ P i x)} IN sts
Proof
  rpt GEN_TAC THEN SIMP_TAC std_ss [ring_def, subsets_def, space_def] THEN
  rpt STRIP_TAC THEN
  KNOW_TAC ``{x | x IN sp /\ (?i. i IN s /\ P i x)} =
              BIGUNION {{x | x IN sp /\ P i x} | i IN s}`` THENL
  [SIMP_TAC std_ss [EXTENSION, BIGUNION, GSPECIFICATION] THEN
   GEN_TAC THEN EQ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN
   STRIP_TAC THEN EXISTS_TAC ``{x | x IN sp /\ P i x}`` THEN
   CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN EXISTS_TAC ``i:'b`` THEN
   ASM_SIMP_TAC std_ss [GSPECIFICATION], ALL_TAC] THEN
  DISC_RW_KILL THEN
  KNOW_TAC ``{{x | x IN sp /\ P i x} | i IN s} SUBSET sts`` THENL
  [SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN GEN_TAC THEN
   STRIP_TAC THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [], MATCH_MP_TAC RING_FINITE_BIGUNION1] THEN
  EXISTS_TAC ``sp:'a->bool`` THEN CONJ_TAC THENL
  [FULL_SIMP_TAC std_ss [ring_def, space_def, subsets_def], ALL_TAC] THEN
  ONCE_REWRITE_TAC [METIS [] ``{x | x IN sp /\ P i x} =
                          (\i. {x | x IN sp /\ P i x}) i``] THEN
  ONCE_REWRITE_TAC [GSYM IMAGE_DEF] THEN METIS_TAC [IMAGE_FINITE]
QED

Theorem algebra_alt : (* was: algebra_alt_eq *)
    !sp sts. algebra (sp, sts) <=> ring (sp, sts) /\ sp IN sts
Proof
    rw [] >> EQ_TAC
 >- (rw [] >> imp_res_tac ALGEBRA_SPACE \\
     fs [algebra_def,ring_def,space_def,subsets_def] >> rw [] \\
     FULL_SIMP_TAC std_ss [BIGUNION_SING, subset_class_def] \\
     KNOW_TAC ``s SUBSET sp /\ t SUBSET sp ==>
               (s DIFF t = sp DIFF ((sp DIFF s) UNION t))``
     >- SET_TAC [] \\
     FULL_SIMP_TAC std_ss [])
 >> metis_tac [RING_SPACE_IMP_ALGEBRA, space_def, subsets_def]
QED

Theorem ALGEBRA_COMPL_SETS : (* was: compl_sets *)
    !sp sts a. algebra (sp,sts) /\ a IN sts ==> sp DIFF a IN sts
Proof
  REWRITE_TAC [algebra_alt, ring_def, subsets_def,space_def] THEN
  rpt STRIP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  POP_ASSUM MP_TAC THEN
  FIRST_ASSUM (MP_TAC o SPECL [``sp:'a->bool``,``a:'a->bool``]) THEN
  rpt STRIP_TAC THEN FULL_SIMP_TAC std_ss [] THEN
  UNDISCH_TAC ``c SUBSET (sts:('a->bool)->bool)`` THEN
  MATCH_MP_TAC RING_FINITE_BIGUNION1 THEN
  EXISTS_TAC ``sp:'a->bool`` THEN
  FULL_SIMP_TAC std_ss [ring_def, space_def, subsets_def]
QED

Theorem algebra_alt_union : (* was: algebra_iff_Un *)
    !sp sts. algebra (sp,sts) <=>
             sts SUBSET (POW sp) /\ {} IN sts /\
             (!a. a IN sts ==> sp DIFF a IN sts) /\
             (!a b. a IN sts /\ b IN sts ==> a UNION b IN sts)
Proof
  rpt STRIP_TAC THEN REWRITE_TAC [algebra_def, subsets_def, space_def] THEN
  REWRITE_TAC [subset_class_def, POW_DEF] THEN
  REWRITE_TAC [SET_RULE ``sts SUBSET {s | s SUBSET sp} <=>
                          (!x. x IN sts ==> x SUBSET sp)``]
QED

Theorem algebra_alt_inter : (* was: algebra_iff_Int *)
    !sp sts. algebra (sp,sts) <=> sts SUBSET POW sp /\ {} IN sts /\
             (!a. a IN sts ==> sp DIFF a IN sts) /\
             (!a b. a IN sts /\  b IN sts ==> a INTER b IN sts)
Proof
  rpt STRIP_TAC THEN REWRITE_TAC [algebra_def, subsets_def, space_def] THEN
  REWRITE_TAC [subset_class_def, POW_DEF] THEN
  REWRITE_TAC [SET_RULE ``sts SUBSET {s | s SUBSET sp} <=>
                          (!x. x IN sts ==> x SUBSET sp)``] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
  [rpt STRIP_TAC THEN KNOW_TAC ``a SUBSET sp /\ b SUBSET sp ==>
    (a INTER b = sp DIFF ((sp DIFF a) UNION (sp DIFF b)))`` THENL
   [SET_TAC [], ALL_TAC]
   THEN FULL_SIMP_TAC std_ss [], ALL_TAC] THEN
  rpt STRIP_TAC THEN KNOW_TAC ``s SUBSET sp /\ t SUBSET sp ==>
   (s UNION t = sp DIFF ((sp DIFF s) INTER (sp DIFF t)))`` THENL
  [SET_TAC [], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss []
QED

Theorem ALGEBRA_SETS_COLLECT_NEG : (* was: sets_Collect_neg *)
    !sp sts P. algebra (sp,sts) /\ {x | x IN sp /\ P x} IN sts ==>
              {x | x IN sp /\ ~P x} IN sts
Proof
  rpt GEN_TAC THEN REWRITE_TAC [algebra_def, space_def, subsets_def] THEN
  RW_TAC std_ss [subset_class_def] THEN
  KNOW_TAC ``{x | x IN sp /\ ~P x} = sp DIFF {x | x IN sp /\ P x}`` THENL
  [ALL_TAC, DISC_RW_KILL THEN FULL_SIMP_TAC std_ss []] THEN SET_TAC []
QED

Theorem ALGEBRA_SETS_COLLECT_IMP : (* was: sets_Collect_imp *)
    !sp sts P Q. algebra (sp,sts) /\ {x | x IN sp /\ P x} IN sts ==>
                 {x | x IN sp /\ Q x} IN sts ==>
                 {x | x IN sp /\ (Q x ==> P x)} IN sts
Proof
  rpt GEN_TAC THEN REWRITE_TAC [algebra_alt, ring_def, space_def, subsets_def] THEN
  rpt STRIP_TAC THEN REWRITE_TAC [IMP_DISJ_THM] THEN
  REWRITE_TAC [SET_RULE ``{x | x IN sp /\ (~Q x \/ P x)} =
                          {x | x IN sp /\ ~Q x} UNION {x | x IN sp /\ P x}``] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss [] THEN
  MATCH_MP_TAC ALGEBRA_SETS_COLLECT_NEG THEN
  FULL_SIMP_TAC std_ss [algebra_alt, ring_def, space_def, subsets_def]
QED

Theorem ALGEBRA_SETS_COLLECT_CONST : (* was: sets_Collect_const *)
    !sp sts P. algebra (sp,sts) ==> {x | x IN sp /\ P} IN sts
Proof
  REWRITE_TAC [algebra_alt] THEN rpt STRIP_TAC THEN
  Cases_on `P` THENL
  [REWRITE_TAC [SET_RULE ``{x | x IN sp /\ T} = sp``] THEN ASM_REWRITE_TAC [],
   FULL_SIMP_TAC std_ss [GSPEC_F, ring_def, subsets_def, space_def]]
QED

Theorem ALGEBRA_SINGLE_SET : (* was: algebra_single_set *)
    !X S. X SUBSET S ==> algebra (S, {{}; X; S DIFF X; S})
Proof
  RW_TAC std_ss [algebra_def, subsets_def, space_def, subset_class_def] THEN
  FULL_SIMP_TAC std_ss [SET_RULE ``x IN {a;b;c;d} <=>
        (x = a) \/ (x = b) \/ (x = c) \/ (x = d)``] THEN TRY (ASM_SET_TAC [])
QED

(* ------------------------------------------------------------------------- *)
(* Retricted Algebras                                                        *)
(* ------------------------------------------------------------------------- *)

(* NOTE: ‘a IN sts’ is weakened to ‘a SUBSET sp’ *)
Theorem ALGEBRA_RESTRICT' : (* was: restricted_algebra *)
    !sp sts a. algebra (sp,sts) /\ a SUBSET sp ==>
               algebra (a,IMAGE (\s. s INTER a) sts)
Proof
    rw [algebra_alt, ring_def, space_def, subsets_def, subset_class_def]
 >| [ (* goal 1 (of 5) *)
      REWRITE_TAC [INTER_SUBSET],
      (* goal 2 (of 5) *)
      Q.EXISTS_TAC ‘{}’ >> ASM_SIMP_TAC std_ss [INTER_EMPTY],
      (* goal 3 (of 5) *)
      rename1 ‘?s. s1 INTER a UNION s2 INTER a = s INTER a /\ s IN sts’ \\
      Q.EXISTS_TAC ‘s1 UNION s2’ \\
      CONJ_TAC >- SET_TAC [] \\
      FULL_SIMP_TAC std_ss [],
      (* goal 4 (of 5) *)
      rename1 ‘?s. s1 INTER a DIFF s2 INTER a = s INTER a /\ s IN sts’ \\
      Q.EXISTS_TAC ‘s1 DIFF s2’ \\
      CONJ_TAC >- SET_TAC [] \\
      FULL_SIMP_TAC std_ss [],
      (* goal 5 (of 5) *)
      Q.EXISTS_TAC ‘sp’ >> ASM_SET_TAC [] ]
QED

Theorem ALGEBRA_RESTRICT : (* was: restricted_algebra *)
    !sp sts a. algebra (sp,sts) /\ a IN sts ==>
               algebra (a,IMAGE (\s. s INTER a) sts)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC ALGEBRA_RESTRICT'
 >> Q.EXISTS_TAC ‘sp’ >> art []
 >> fs [algebra_def, subset_class_def]
QED

(* NOTE: ‘a IN sts’ is weakened to ‘a SUBSET sp’ *)
Theorem SIGMA_ALGEBRA_RESTRICT' :
    !sp sts a. sigma_algebra (sp,sts) /\ a SUBSET sp ==>
               sigma_algebra (a,IMAGE (\s. s INTER a) sts)
Proof
    rpt STRIP_TAC
 >> rw [SIGMA_ALGEBRA_ALT, algebra_def, subset_class_def, IN_FUNSET]
 >| [ (* goal 1 (of 5) *)
      REWRITE_TAC [INTER_SUBSET],
      (* goal 2 (of 5) *)
      Q.EXISTS_TAC ‘{}’ >> REWRITE_TAC [INTER_EMPTY] \\
      MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                 (Q.SPEC ‘(sp,sts)’ SIGMA_ALGEBRA_EMPTY)) >> art [],
      (* goal 3 (of 5) *)
      rename1 ‘s IN sts’ >> Q.EXISTS_TAC ‘sp DIFF s’ \\
      CONJ_TAC
      >- (fs [SIGMA_ALGEBRA_ALT, algebra_def, subset_class_def] \\
          ASM_SET_TAC []) \\
      MATCH_MP_TAC (REWRITE_RULE [space_def, subsets_def]
                                 (Q.SPEC ‘(sp,sts)’ SIGMA_ALGEBRA_COMPL)) >> art [],
      (* goal 4 (of 5) *)
      rename1 ‘?s. s1 INTER a UNION s2 INTER a = s INTER a /\ s IN sts’ \\
      Q.EXISTS_TAC ‘s1 UNION s2’ \\
      CONJ_TAC >- SET_TAC [] \\
      MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                 (Q.SPEC ‘(sp,sts)’ SIGMA_ALGEBRA_UNION)) >> art [],
      (* goal 5 (of 5) *)
      fs [SKOLEM_THM] \\
      rename1 ‘!x. f x = g x INTER a /\ g x IN sts’ \\
      Q.EXISTS_TAC ‘BIGUNION (IMAGE g UNIV)’ \\
      CONJ_TAC >- ASM_SET_TAC [] \\
      fs [SIGMA_ALGEBRA_FN, IN_FUNSET] ]
QED

Theorem SIGMA_ALGEBRA_RESTRICT :
    !sp sts a. sigma_algebra (sp,sts) /\ a IN sts ==>
               sigma_algebra (a,IMAGE (\s. s INTER a) sts)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC SIGMA_ALGEBRA_RESTRICT'
 >> Q.EXISTS_TAC ‘sp’ >> art []
 >> fs [sigma_algebra_def, algebra_def, subset_class_def]
QED

Definition restrict_algebra_def :
    restrict_algebra A sp = (sp INTER space A,IMAGE (\a. a INTER sp) (subsets A))
End

Theorem restrict_algebra_reduce :
    !A. subset_class (space A) (subsets A) ==> restrict_algebra A (space A) = A
Proof
    rw [restrict_algebra_def, subset_class_def]
 >> qabbrev_tac ‘sp = space A’
 >> qabbrev_tac ‘sts = subsets A’
 >> ASSUME_TAC (SYM (Q.SPEC ‘A’ SPACE))
 >> POP_ORW
 >> simp []
 >> rw [Once EXTENSION]
 >> EQ_TAC >> rw []
 >- (Suff ‘a INTER sp = a’ >- rw [] \\
     Suff ‘a SUBSET sp’ >- SET_TAC [] \\
     rw [])
 >> Q.EXISTS_TAC ‘x’ >> art []
 >> Suff ‘x SUBSET sp’ >- SET_TAC []
 >> rw []
QED

Theorem restrict_algebra_reduce' :
    !A. sigma_algebra A ==> restrict_algebra A (space A) = A
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC restrict_algebra_reduce
 >> fs [sigma_algebra_def, algebra_def]
QED

Theorem sigma_algebra_restrict_algebra :
    !A sp. sigma_algebra A /\ sp IN subsets A ==>
           sigma_algebra (restrict_algebra A sp)
Proof
    rw [restrict_algebra_def]
 >> qabbrev_tac ‘Z = space A’
 >> qabbrev_tac ‘sts = subsets A’
 >> Know ‘sp INTER Z = sp’
 >- (Suff ‘sp SUBSET Z’ >- SET_TAC [] \\
     fs [sigma_algebra_def, algebra_def, subset_class_def])
 >> Rewr'
 >> MATCH_MP_TAC SIGMA_ALGEBRA_RESTRICT >> art []
 >> Q.EXISTS_TAC ‘Z’
 >> rw [SPACE, Abbr ‘Z’, Abbr ‘sts’]
QED

(* NOTE: this theorem doesn't hold if ‘a IN sts’ is weakened to ‘a SUBSET sp’ *)
Theorem SIGMA_ALGEBRA_RESTRICT_SUBSET :
    !sp sts a. sigma_algebra (sp,sts) /\ a IN sts ==>
              (IMAGE (\s. s INTER a) sts) SUBSET sts
Proof
    rw [SUBSET_DEF]
 >> MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                               (Q.SPEC ‘(sp,sts)’ SIGMA_ALGEBRA_INTER)) >> art []
QED

Theorem restrict_algebra_SUBSET :
    !A sp. sigma_algebra A /\ sp IN subsets A ==>
           subsets (restrict_algebra A sp) SUBSET subsets A
Proof
    rw [restrict_algebra_def]
 >> MATCH_MP_TAC SIGMA_ALGEBRA_RESTRICT_SUBSET
 >> Q.EXISTS_TAC ‘space A’ >> rw [SPACE]
QED

Theorem sigma_algebra_alt_eq :
    !sp sts. sigma_algebra (sp,sts) <=>
             algebra (sp,sts) /\
             !A. IMAGE A UNIV SUBSET sts ==> BIGUNION {A i | i IN univ(:num)} IN sts
Proof
  rpt GEN_TAC THEN REWRITE_TAC [SIGMA_ALGEBRA_ALT] THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC ``A:num->'a->bool`` THEN
  POP_ASSUM (MP_TAC o SPEC ``A:num->'a->bool``) THEN
  SIMP_TAC std_ss [IMAGE_DEF, subsets_def] THEN rpt STRIP_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THEN POP_ASSUM MP_TAC THEN EVAL_TAC THEN
  SRW_TAC[] [IN_UNIV,SUBSET_DEF,IN_FUNSET] THEN METIS_TAC[]
QED

Definition sigma_algebra_alt :
    sigma_algebra_alt sp sts <=>
     algebra (sp,sts) /\
     !A. IMAGE A UNIV SUBSET sts ==> BIGUNION {A i | i IN univ(:num)} IN sts
End

Theorem sigma_algebra_eq_alt :
    !sp sts. sigma_algebra (sp,sts) <=> sigma_algebra_alt sp sts
Proof
    REWRITE_TAC [sigma_algebra_alt, sigma_algebra_alt_eq]
QED

Theorem sigma_algebra_alt_pow :
    !sp sts. sigma_algebra (sp,sts) <=>
             sts SUBSET POW sp /\ {} IN sts /\
            (!s. s IN sts ==> sp DIFF s IN sts) /\
            (!A. IMAGE A UNIV SUBSET sts ==>
                 BIGUNION {(A :num->'a->bool) i | i IN UNIV} IN sts)
Proof
  SIMP_TAC std_ss [sigma_algebra_alt_eq, algebra_def, space_def, subsets_def] THEN
  rpt GEN_TAC THEN SIMP_TAC std_ss [subset_class_def, POW_DEF] THEN
  EQ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
  rpt STRIP_TAC THENL [ASM_SET_TAC [], ASM_SET_TAC [], ASM_SET_TAC [],
   ALL_TAC, ASM_SET_TAC []] THEN
  SIMP_TAC std_ss [UNION_BINARY] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SIMP_TAC std_ss [BINARY_RANGE] THEN ASM_SET_TAC []
QED
Theorem sigma_algebra_iff2 = sigma_algebra_alt_pow

val lemma = prove ((* was: countable_Union *)
  ``!sp sts c. sigma_algebra (sp,sts) /\ countable c /\ c SUBSET sts ==>
               BIGUNION c IN sts``,
    FULL_SIMP_TAC std_ss [sigma_algebra_def, subsets_def]);

Theorem SIGMA_ALGEBRA_COUNTABLE_UN : (* was: countable_UN *)
    !sp sts A X. sigma_algebra (sp,sts) /\ IMAGE (A:num->'a->bool) X SUBSET sts ==>
                 BIGUNION {A x | x IN X} IN sts
Proof
  REPEAT STRIP_TAC THEN
  KNOW_TAC
  ``(IMAGE (\i. if i IN X then (A:num->'a->bool) i else {}) UNIV) SUBSET sts``
  THENL [POP_ASSUM MP_TAC THEN
   SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE] THEN REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [] THEN COND_CASES_TAC THENL [METIS_TAC [], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [sigma_algebra_alt_eq, algebra_def, ring_alt, semiring_alt,
    subsets_def], ALL_TAC] THEN DISCH_TAC THEN KNOW_TAC
    ``BIGUNION {(\i. if i IN X then (A:num->'a->bool) i else {}) x | x IN UNIV}
       IN sts``
  THENL [SIMP_TAC std_ss [] THEN MATCH_MP_TAC lemma THEN
   EXISTS_TAC ``sp:'a->bool`` THEN FULL_SIMP_TAC std_ss [] THEN
   CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC []] THEN
   SIMP_TAC arith_ss [GSYM IMAGE_DEF] THEN
   METIS_TAC [COUNTABLE_IMAGE_NUM], DISCH_TAC] THEN KNOW_TAC ``
  BIGUNION {(\i. if i IN X then (A:num->'a->bool) i else {}) x | x IN univ(:num)} =
  BIGUNION {A x | x IN X}`` THENL [ALL_TAC, METIS_TAC []] THEN
  SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, GSPECIFICATION] THEN GEN_TAC THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
  [EXISTS_TAC ``s:'a->bool`` THEN FULL_SIMP_TAC std_ss [] THEN
   POP_ASSUM K_TAC THEN POP_ASSUM K_TAC THEN POP_ASSUM MP_TAC THEN
   COND_CASES_TAC THEN ASM_SET_TAC [], ALL_TAC] THEN
  EXISTS_TAC ``s:'a->bool`` THEN FULL_SIMP_TAC std_ss [IN_UNIV] THEN
  EXISTS_TAC ``x':num`` THEN ASM_SET_TAC []
QED

Theorem SIGMA_ALGEBRA_COUNTABLE_UN' : (* was: countable_UN' *)
    !sp sts A X. sigma_algebra (sp,sts) /\ IMAGE A X SUBSET sts /\
                 countable X ==> BIGUNION {A x | x IN X} IN sts
Proof
  RW_TAC std_ss [] THEN
  KNOW_TAC ``(IMAGE (\i. if i IN X then (A:'b->'a->bool) i else {}) UNIV)
              SUBSET sts`` THENL
  [SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV] THEN RW_TAC std_ss [] THEN
   COND_CASES_TAC THENL
    [ASM_SET_TAC [], FULL_SIMP_TAC std_ss [sigma_algebra_alt_pow]],
   DISCH_TAC] THEN
  KNOW_TAC ``BIGUNION {(\i. if i IN X then A i else {}) x | x IN UNIV}
             IN sts`` THENL
  [ALL_TAC, DISCH_TAC THEN
   KNOW_TAC ``
    BIGUNION {(\i. if i IN X then (A:'b->'a->bool) i else {}) x | x IN univ(:'b)} =
    BIGUNION {A x | x IN X}`` THENL [ALL_TAC, METIS_TAC []] THEN
   SIMP_TAC std_ss [EXTENSION, IN_BIGUNION, GSPECIFICATION] THEN GEN_TAC THEN
   EQ_TAC THEN rpt STRIP_TAC THENL
   [EXISTS_TAC ``s:'a->bool`` THEN FULL_SIMP_TAC std_ss [] THEN
    POP_ASSUM K_TAC THEN POP_ASSUM K_TAC THEN POP_ASSUM MP_TAC THEN
    COND_CASES_TAC THEN ASM_SET_TAC [], ALL_TAC] THEN
   EXISTS_TAC ``s:'a->bool`` THEN FULL_SIMP_TAC std_ss [IN_UNIV] THEN
   EXISTS_TAC ``x':'b`` THEN FULL_SIMP_TAC std_ss []] THEN
  RULE_ASSUM_TAC (SIMP_RULE std_ss [SIGMA_ALGEBRA]) THEN
  rpt (POP_ASSUM MP_TAC) THEN REWRITE_TAC [subsets_def] THEN
  rpt STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC std_ss [GSYM IMAGE_DEF] THEN
  KNOW_TAC ``countable (IMAGE (A:'b->'a->bool) X)`` THENL
  [rw[image_countable], DISCH_TAC] THEN
  ONCE_REWRITE_TAC [SET_RULE ``IMAGE (\x. if x IN X then A x else {}) univ(:'b) =
                    (IMAGE A X) UNION IMAGE (\x. {}) (UNIV DIFF X)``] THEN
  MATCH_MP_TAC union_countable THEN CONJ_TAC THENL
  [FULL_SIMP_TAC std_ss [COUNTABLE_ALT] THEN
   METIS_TAC [], ALL_TAC] THEN
  SIMP_TAC std_ss [COUNTABLE_ALT] THEN Q.EXISTS_TAC `(\n. {}):num->'a->bool` THEN
  SIMP_TAC std_ss [IN_IMAGE] THEN METIS_TAC []
QED

Theorem SIGMA_ALGEBRA_COUNTABLE_INT : (* was: countable_INT *)
    !sp sts A X. sigma_algebra (sp,sts) /\
                 IMAGE (A :num->'a->bool) X SUBSET sts /\ X <> {} ==>
                 BIGINTER {(A :num->'a->bool) x | x IN X} IN sts
Proof
  REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [GSYM MEMBER_NOT_EMPTY] THEN
  KNOW_TAC ``!x. x IN X ==> (A:num->'a->bool) x IN sts`` THENL
  [ASM_SET_TAC [], DISCH_TAC] THEN
  KNOW_TAC ``sp DIFF BIGUNION {sp DIFF (A:num->'a->bool) x | x IN X} IN sts`` THENL
  [MATCH_MP_TAC RING_DIFF_ALT THEN EXISTS_TAC ``sp:'a->bool`` THEN
   FULL_SIMP_TAC std_ss [sigma_algebra_alt_eq, algebra_alt] THEN
   ONCE_REWRITE_TAC [METIS [] ``sp DIFF A x = (\x. sp DIFF A x) x``] THEN

   MATCH_MP_TAC SIGMA_ALGEBRA_COUNTABLE_UN THEN EXISTS_TAC ``sp:'a->bool`` THEN
   FULL_SIMP_TAC std_ss [sigma_algebra_alt_eq, algebra_alt] THEN
   SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_DIFF_ALT THEN
   EXISTS_TAC ``sp:'a->bool`` THEN
   ASM_SET_TAC [], DISCH_TAC] THEN
  KNOW_TAC ``BIGINTER {(A:num->'a->bool) x | x IN X} =
             sp DIFF BIGUNION {sp DIFF A x | x IN X}`` THENL
  [ALL_TAC, METIS_TAC []] THEN SIMP_TAC std_ss [EXTENSION] THEN GEN_TAC THEN
  KNOW_TAC ``sts SUBSET POW sp`` THENL
  [FULL_SIMP_TAC std_ss [sigma_algebra_alt_eq, algebra_alt, ring_alt, semiring_alt,
    subset_class_def] THEN ASM_SET_TAC [POW_DEF], RW_TAC std_ss [POW_DEF]] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
  [SIMP_TAC std_ss [IN_DIFF] THEN CONJ_TAC THENL [ASM_SET_TAC [], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [BIGINTER, BIGUNION, GSPECIFICATION] THEN GEN_TAC THEN
   ASM_CASES_TAC ``x' NOTIN (s:'a->bool)`` THEN ASM_REWRITE_TAC [] THEN
   GEN_TAC THEN ASM_CASES_TAC ``x'' NOTIN (X:num->bool)`` THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN
   SIMP_TAC std_ss [DIFF_DEF, EXTENSION, GSPECIFICATION] THEN
   EXISTS_TAC ``x':'a`` THEN FULL_SIMP_TAC std_ss [] THEN
   ASM_CASES_TAC ``x' NOTIN (sp:'a->bool)`` THEN FULL_SIMP_TAC std_ss [] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SET_TAC [], ALL_TAC] THEN
  SIMP_TAC std_ss [BIGINTER, GSPECIFICATION] THEN GEN_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC [] THEN POP_ASSUM MP_TAC THEN
  POP_ASSUM K_TAC THEN FULL_SIMP_TAC std_ss [IN_DIFF, BIGUNION, GSPECIFICATION] THEN
  STRIP_TAC THEN CCONTR_TAC THEN
  UNDISCH_TAC
   “!s. (!x. s = sp DIFF (A:num->'a->bool) x ==> x NOTIN X) \/ x' NOTIN s” THEN
  SIMP_TAC std_ss [] THEN EXISTS_TAC ``sp DIFF (A:num->'a->bool) x''`` THEN
  CONJ_TAC THENL [METIS_TAC [], ALL_TAC] THEN
  ASM_SIMP_TAC std_ss [IN_DIFF]
QED

Theorem SIGMA_ALGEBRA_COUNTABLE_INT' : (* was: countable_INT' *)
    !sp sts A X. sigma_algebra (sp,sts) /\ countable X /\ (X <> {}) /\
                 IMAGE (A:num->'a->bool) X SUBSET sts ==>
                 BIGINTER {(A:num->'a->bool) x | x IN X} IN sts
Proof
    METIS_TAC [SIGMA_ALGEBRA_COUNTABLE_INT]
QED

(* ------------------------------------------------------------------------- *)
(*  Initial Sigma Algebra (conributed by HVG concordia)                      *)
(* ------------------------------------------------------------------------- *)

Inductive sigma_sets :
    (sigma_sets sp st {}) /\
    (!a. st a ==> sigma_sets sp st a) /\
    (!a. sigma_sets sp st a ==> sigma_sets sp st (sp DIFF a)) /\
    (!A. (!i. sigma_sets sp st ((A :num->'a->bool) i)) ==>
              sigma_sets sp st (BIGUNION {A i | i IN UNIV}))
End

val sigma_sets_basic = store_thm ("sigma_sets_basic",
 ``!sp st a. a IN st ==> a IN sigma_sets sp st``,
  SIMP_TAC std_ss [SPECIFICATION, sigma_sets_rules]);

val sigma_sets_empty = store_thm ("sigma_sets_empty",
 ``!sp st. {} IN sigma_sets sp st``,
  SIMP_TAC std_ss [SPECIFICATION, sigma_sets_rules]);

val sigma_sets_compl = store_thm ("sigma_sets_compl",
  ``!sp st a. a IN sigma_sets sp st ==> sp DIFF a IN sigma_sets sp st``,
  SIMP_TAC std_ss [SPECIFICATION, sigma_sets_rules]);

Theorem sigma_sets_BIGUNION : (* was: sigma_sets_union *)
    !sp st A. (!i. (A:num->'a->bool) i IN sigma_sets sp st) ==>
              BIGUNION {A i | i IN UNIV} IN sigma_sets sp st
Proof
    SIMP_TAC std_ss [SPECIFICATION, sigma_sets_rules]
QED

Theorem sigma_sets_subset :
    !sp sts st. sigma_algebra (sp,sts) /\ st SUBSET sts ==>
                sigma_sets sp st SUBSET sts
Proof
  rpt STRIP_TAC THEN SIMP_TAC std_ss [SPECIFICATION, SUBSET_DEF] THEN
  HO_MATCH_MP_TAC sigma_sets_ind THEN
  FULL_SIMP_TAC std_ss [sigma_algebra_alt_eq,
    algebra_alt, ring_def, space_def, subsets_def, subset_class_def] THEN
  rpt STRIP_TAC THENL
  [ASM_SET_TAC [],
   ASM_SET_TAC [],
   ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN MATCH_MP_TAC RING_DIFF_ALT THEN
   FULL_SIMP_TAC std_ss [ring_def, subsets_def, space_def, subset_class_def] THEN
   ASM_SET_TAC [],
   ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   rpt STRIP_TAC THEN ASM_SET_TAC []]
QED

val sigma_sets_into_sp = store_thm ("sigma_sets_into_sp",
 ``!sp st. st SUBSET POW sp ==> !x. x IN sigma_sets sp st ==> x SUBSET sp``,
  rpt GEN_TAC THEN DISCH_TAC THEN SIMP_TAC std_ss [SPECIFICATION] THEN
  HO_MATCH_MP_TAC sigma_sets_ind THEN FULL_SIMP_TAC std_ss [POW_DEF] THEN
  rpt STRIP_TAC THEN ASM_SET_TAC []);

Theorem sigma_algebra_sigma_sets :
    !sp st. st SUBSET POW sp ==> sigma_algebra (sp, sigma_sets sp st)
Proof
  RW_TAC std_ss [sigma_algebra_alt_pow] THENL
  [SIMP_TAC std_ss [SUBSET_DEF] THEN
   SIMP_TAC std_ss [POW_DEF, GSPECIFICATION] THEN
   METIS_TAC [sigma_sets_into_sp],
   METIS_TAC [sigma_sets_empty],
   METIS_TAC [sigma_sets_compl],
   MATCH_MP_TAC sigma_sets_BIGUNION THEN ASM_SET_TAC []]
QED

(* NOTE: this indicates that `sigma_sets = sigma`, see next theorem *)
Theorem sigma_sets_least_sigma_algebra :
    !sp A. A SUBSET POW sp ==>
          (sigma_sets sp A =
           BIGINTER {B | A SUBSET B /\ sigma_algebra (sp,B)})
Proof
  rpt STRIP_TAC THEN
  KNOW_TAC ``!B X. A SUBSET B /\ sigma_algebra (sp,B) /\
                   X IN sigma_sets sp A ==> X IN B`` THENL
  [rpt STRIP_TAC THEN UNDISCH_TAC ``A SUBSET (B:('a->bool)->bool)`` THEN
   UNDISCH_TAC ``sigma_algebra (sp, B)`` THEN REWRITE_TAC [AND_IMP_INTRO] THEN
   DISCH_THEN (MP_TAC o MATCH_MP sigma_sets_subset) THEN ASM_SET_TAC [],
   DISCH_TAC] THEN
  KNOW_TAC
   ``!X. X IN BIGINTER {B | A SUBSET B /\ sigma_algebra (sp,B)} ==>
         !B. A SUBSET B ==> sigma_algebra (sp,B) ==> X IN B`` THENL
  [STRIP_TAC THEN ASM_SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION],
   DISCH_TAC] THEN
  SIMP_TAC std_ss [EXTENSION] THEN GEN_TAC THEN EQ_TAC THENL
  [DISCH_TAC THEN SIMP_TAC std_ss [IN_BIGINTER, GSPECIFICATION] THEN
   rpt STRIP_TAC THEN FULL_SIMP_TAC std_ss [SUBSET_DEF], ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC ``x:'a->bool``) THEN
  ASM_REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  rpt CONJ_TAC THENL
  [ASM_SIMP_TAC std_ss [SUBSET_DEF, sigma_sets_basic],
   ASM_SIMP_TAC std_ss [sigma_algebra_sigma_sets],
   ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [AND_IMP_INTRO] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC std_ss [sigma_algebra_sigma_sets] THEN
  ASM_SIMP_TAC std_ss [SUBSET_DEF, sigma_sets_basic]
QED

Theorem sigma_sets_sigma :
    !sp A. A SUBSET POW sp ==> sigma_sets sp A = subsets (sigma sp A)
Proof
    rw [sigma_sets_least_sigma_algebra, sigma_def]
QED

val sigma_sets_top = store_thm ("sigma_sets_top",
 ``!sp A. sp IN sigma_sets sp A``,
 METIS_TAC [sigma_sets_compl, sigma_sets_empty, DIFF_EMPTY]);

Theorem sigma_sets_union : (* was: sigma_sets_Un *)
    !sp st a b. a IN sigma_sets sp st /\ b IN sigma_sets sp st ==>
                a UNION b IN sigma_sets sp st
Proof
  rpt STRIP_TAC THEN REWRITE_TAC [UNION_BINARY] THEN
  MATCH_MP_TAC sigma_sets_BIGUNION THEN GEN_TAC THEN
  RW_TAC std_ss [binary_def]
QED

Theorem sigma_sets_BIGINTER : (* was: sigma_sets_Inter *)
    !sp st A. st SUBSET POW sp ==>
             (!i. (A :num->'a->bool) i IN sigma_sets sp st) ==>
              BIGINTER {A i | i IN UNIV} IN sigma_sets sp st
Proof
  rpt STRIP_TAC THEN
  KNOW_TAC ``(!i:num. A i IN sigma_sets sp st) ==>
             (!i:num. sp DIFF A i IN sigma_sets sp st)`` THENL
  [METIS_TAC [sigma_sets_compl], DISCH_TAC] THEN
  KNOW_TAC ``BIGUNION {sp DIFF A i | (i:num) IN UNIV} IN sigma_sets sp st`` THENL
  [ONCE_REWRITE_TAC [METIS [] ``sp DIFF A i = (\i. sp DIFF A i) i``] THEN
   MATCH_MP_TAC sigma_sets_BIGUNION THEN METIS_TAC [], DISCH_TAC] THEN
  KNOW_TAC
   ``sp DIFF BIGUNION {sp DIFF A i | (i:num) IN UNIV} IN sigma_sets sp st`` THENL
  [MATCH_MP_TAC sigma_sets_compl THEN METIS_TAC [], DISCH_TAC] THEN
  KNOW_TAC ``sp DIFF BIGUNION {sp DIFF A i | i IN UNIV} =
             BIGINTER {A i | (i:num) IN UNIV}`` THENL
  [ALL_TAC, METIS_TAC[]] THEN
  SIMP_TAC std_ss [EXTENSION] THEN GEN_TAC THEN EQ_TAC THENL
  [SIMP_TAC std_ss [IN_DIFF, IN_BIGUNION, IN_BIGINTER, GSPECIFICATION] THEN
   RW_TAC std_ss [] THEN POP_ASSUM K_TAC THEN
   POP_ASSUM (MP_TAC o SPEC ``sp DIFF (A:num->'a->bool) i``) THEN
   ASM_SET_TAC [], ALL_TAC] THEN
  SIMP_TAC std_ss [IN_BIGINTER, IN_DIFF, IN_BIGUNION, GSPECIFICATION] THEN
  RW_TAC std_ss [IN_UNIV] THENL
  [FIRST_X_ASSUM (MP_TAC o SPEC ``(A:num->'a->bool) i``) THEN
   KNOW_TAC ``(?i'. A i = (A:num->'a->bool) i')`` THENL
   [METIS_TAC [], DISCH_TAC THEN ASM_REWRITE_TAC []] THEN
   SPEC_TAC (``x``,``x``) THEN REWRITE_TAC [GSYM SUBSET_DEF] THEN
   UNDISCH_TAC ``st SUBSET POW (sp:'a->bool)`` THEN
   DISCH_THEN (MP_TAC o MATCH_MP sigma_sets_into_sp) THEN
   METIS_TAC [], ALL_TAC] THEN
  ASM_CASES_TAC ``x NOTIN s`` THEN FULL_SIMP_TAC std_ss [] THEN
  RW_TAC std_ss [EXTENSION] THEN EXISTS_TAC ``x`` THEN
  ASM_SIMP_TAC std_ss [IN_DIFF] THEN DISJ2_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC []
QED

Theorem sigma_sets_BIGINTER2 : (* was: sigma_sets_INTER *)
    !sp st A N. st SUBSET POW sp /\
               (!i:num. i IN N ==> A i IN sigma_sets sp st) /\ N <> {} ==>
                BIGINTER {A i | i IN N} IN sigma_sets sp st
Proof
  rpt STRIP_TAC THEN
  KNOW_TAC ``!i:num. (if i IN N then A i else sp) IN sigma_sets sp st`` THENL
  [GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [] THEN
   SIMP_TAC std_ss [sigma_sets_top], DISCH_TAC] THEN
  KNOW_TAC ``BIGINTER {(if i IN N then (A:num->'a->bool) i else sp) | i IN UNIV} IN
             sigma_sets sp st`` THENL
  [ASM_SIMP_TAC std_ss [sigma_sets_BIGINTER], DISCH_TAC] THEN
  KNOW_TAC ``BIGINTER {(if i IN N then (A:num->'a->bool) i else sp) | i IN UNIV} =
             BIGINTER {A i | i IN N}`` THENL
  [ALL_TAC, METIS_TAC []] THEN
  UNDISCH_TAC ``st SUBSET POW (sp:'a->bool)``  THEN
  DISCH_THEN (MP_TAC o MATCH_MP sigma_sets_into_sp) THEN DISCH_TAC THEN
  ASM_SET_TAC []
QED

Theorem sigma_sets_fixpoint :
    !sp sts. sigma_algebra (sp,sts) ==> (sigma_sets sp sts = sts)
Proof
  rpt STRIP_TAC THEN EVAL_TAC THEN CONJ_TAC THENL
  [MATCH_MP_TAC sigma_sets_subset THEN ASM_SIMP_TAC std_ss [SUBSET_REFL],
   SIMP_TAC std_ss [SUBSET_DEF, sigma_sets_basic]]
QED
Theorem sigma_sets_eq = sigma_sets_fixpoint

Theorem sigma_sets_superset_generator :
    !X A. A SUBSET sigma_sets X A
Proof
  SIMP_TAC std_ss [SUBSET_DEF, sigma_sets_basic]
QED

(* NOTE: ‘sigma_algebra a /\ sigma_algebra b’ has been removed due to changes
         in measurable_def.
 *)
Theorem IN_MEASURABLE :
    !a b f. f IN measurable a b <=>
            f IN (space a -> space b) /\
            (!s. s IN subsets b ==> ((PREIMAGE f s)INTER(space a)) IN subsets a)
Proof
    RW_TAC std_ss [measurable_def, GSPECIFICATION]
QED

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
   >> reverse CONJ_TAC
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

val MEASURABLE_SIGMA = store_thm
  ("MEASURABLE_SIGMA",
  ``!f a b sp.
       sigma_algebra a /\
       subset_class sp b /\
       f IN (space a -> sp) /\
       (!s. s IN b ==> ((PREIMAGE f s)INTER(space a)) IN subsets a)
      ==>
       f IN measurable a (sigma sp b)``,
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

(* This is Lemma 2.4.1 of [9, p.207], re-expressing the above MEASURABLE_SIGMA as a
   necessary ad sufficient condition.
 *)
Theorem MEASURABLE_LEMMA :
    !f a b sp sts.
       sigma_algebra a /\ subset_class sp sts /\
       f IN (space a -> sp) /\ b = (sigma sp sts)
     ==>
      ((!s. s IN subsets b ==> ((PREIMAGE f s) INTER (space a)) IN subsets a)
       <=>
       (!s. s IN sts       ==> ((PREIMAGE f s) INTER (space a)) IN subsets a))
Proof
    RW_TAC std_ss []
 >> EQ_TAC
 >- (rpt STRIP_TAC \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Suff ‘sts SUBSET subsets (sigma sp sts)’ >- METIS_TAC [SUBSET_DEF] \\
     REWRITE_TAC [SIGMA_SUBSET_SUBSETS])
 >> DISCH_TAC
 >> Know ‘f IN measurable a (sigma sp sts)’
 >- (MATCH_MP_TAC MEASURABLE_SIGMA >> art [])
 >> rw [measurable_def]
QED

(* NOTE: more antecedents are added due to changes of ‘measurable’ *)
Theorem MEASURABLE_SUBSET :
    !a b. sigma_algebra a /\ subset_class (space b) (subsets b) ==>
          measurable a b SUBSET measurable a (sigma (space b) (subsets b))
Proof
   RW_TAC std_ss [SUBSET_DEF]
   >> MATCH_MP_TAC MEASURABLE_SIGMA
   >> FULL_SIMP_TAC std_ss [IN_MEASURABLE, SIGMA_ALGEBRA, space_def, subsets_def]
QED

(* NOTE: more antecedents are added due to changes of ‘measurable’ *)
Theorem MEASURABLE_LIFT :
    !f a b. sigma_algebra a /\ subset_class (space b) (subsets b) /\
            f IN measurable a b ==> f IN measurable a (sigma (space b) (subsets b))
Proof
   PROVE_TAC [MEASURABLE_SUBSET, SUBSET_DEF]
QED

val MEASURABLE_I = store_thm
  ("MEASURABLE_I",
   ``!a. sigma_algebra a ==> I IN measurable a a``,
   RW_TAC std_ss [IN_MEASURABLE, I_THM, PREIMAGE_I, IN_FUNSET, GSPEC_ID, SPACE, SUBSET_REFL]
   >> Know `s INTER space a = s`
   >- (FULL_SIMP_TAC std_ss [Once EXTENSION, sigma_algebra_def, algebra_def, IN_INTER,
                             subset_class_def, SUBSET_DEF]
       >> METIS_TAC [])
   >> RW_TAC std_ss []);

(* Theorem 7.4 [7, p.54] *)
val MEASURABLE_COMP = store_thm
  ("MEASURABLE_COMP",
   ``!f g a b c.
       f IN measurable a b /\ g IN measurable b c ==>
       (g o f) IN measurable a c``,
   RW_TAC std_ss [IN_MEASURABLE, GSYM PREIMAGE_COMP, IN_FUNSET, SIGMA_ALGEBRA,
                  space_def, subsets_def, GSPECIFICATION]
   >> `PREIMAGE f (PREIMAGE g s) INTER space a =
       PREIMAGE f (PREIMAGE g s INTER space b) INTER space a`
        by (RW_TAC std_ss [Once EXTENSION, IN_INTER, IN_PREIMAGE] >> METIS_TAC [])
   >> METIS_TAC []);

Theorem MEASURABLE_COMP_STRONG :
    !f g a b c.
       f IN measurable a b /\ sigma_algebra c /\ g IN (space b -> space c) /\
      (!x. x IN (subsets c) ==>
           PREIMAGE g x INTER (IMAGE f (space a)) IN subsets b) ==>
      (g o f) IN measurable a c
Proof
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
           >- (FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, subset_class_def, SUBSET_DEF] \\
               PROVE_TAC [])
           >> PROVE_TAC [])
       >> STRIP_TAC >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
       >> FULL_SIMP_TAC std_ss [PREIMAGE_ALT]]
QED

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
           >- (FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, subset_class_def, SUBSET_DEF] \\
               PROVE_TAC [])
           >> STRIP_TAC
           >> Know `(f x) IN space b`
           >- FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_PREIMAGE, IN_FUNSET]
           >> STRIP_TAC
           >> Know `x IN space a`
           >- FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_PREIMAGE]
           >> STRIP_TAC
           >> FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE]
           >> Q.PAT_X_ASSUM `!x. (?x'. (x = f x') /\ x' IN space a) ==> x IN t`
                MATCH_MP_TAC
           >> Q.EXISTS_TAC `x`
           >> ASM_REWRITE_TAC [])
       >> DISCH_THEN (ONCE_REWRITE_TAC o wrap o GSYM)
       >> RW_TAC std_ss [PREIMAGE_ALT]
       >> RW_TAC std_ss [GSYM PREIMAGE_ALT, GSYM PREIMAGE_COMP]]);

val MEASURABLE_UP_LIFT = store_thm
  ("MEASURABLE_UP_LIFT",
   ``!sp a b c f. f IN measurable (sp, a) c /\
               sigma_algebra (sp, b) /\ a SUBSET b ==> f IN measurable (sp,b) c``,
   RW_TAC std_ss [IN_MEASURABLE, GSPECIFICATION, SUBSET_DEF, IN_FUNSET,
                  space_def, subsets_def]);

val MEASURABLE_UP_SUBSET = store_thm
  ("MEASURABLE_UP_SUBSET",
   ``!sp a b c. a SUBSET b /\ sigma_algebra (sp, b)
            ==> measurable (sp, a) c SUBSET measurable (sp, b) c``,
   RW_TAC std_ss [MEASURABLE_UP_LIFT, SUBSET_DEF]
   >> MATCH_MP_TAC MEASURABLE_UP_LIFT
   >> Q.EXISTS_TAC `a`
   >> ASM_REWRITE_TAC [SUBSET_DEF]);

(* NOTE: more antecedents are added due to changes of ‘measurable’ *)
Theorem MEASURABLE_UP_SIGMA :
    !a b. subset_class (space a) (subsets a) /\ sigma_algebra b ==>
          measurable a b SUBSET measurable (sigma (space a) (subsets a)) b
Proof
    RW_TAC std_ss [SUBSET_DEF, IN_MEASURABLE, space_def, subsets_def, SPACE_SIGMA]
 >> PROVE_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF]
QED

(* Definition 14.2 of [1, p.137] *)
val prod_sigma_def = Define
   ‘prod_sigma a b =
      sigma (space a CROSS space b) (prod_sets (subsets a) (subsets b))’;

val _ = overload_on ("CROSS", “prod_sigma”);

(* NOTE: the following easy satifsiable antecedents are added, due to changes
         in ‘measurable’ which previously requires that a1 and a2 are
         sigma-algebras:

   subset_class (space a1) (subsets a1)
   subset_class (space a2) (subsets a2)
 *)
Theorem MEASURABLE_PROD_SIGMA' :
    !a a1 a2 f. sigma_algebra a /\
                subset_class (space a1) (subsets a1) /\
                subset_class (space a2) (subsets a2) /\
               (FST o f) IN measurable a a1 /\
               (SND o f) IN measurable a a2 ==> f IN measurable a (a1 CROSS a2)
Proof
    RW_TAC std_ss [prod_sigma_def]
 >> MATCH_MP_TAC MEASURABLE_SIGMA
 >> FULL_SIMP_TAC std_ss [IN_MEASURABLE]
 >> CONJ_TAC
 >- (RW_TAC std_ss [subset_class_def, subsets_def, space_def, IN_PROD_SETS] \\
     rw [CROSS_SUBSET] \\
     fs [subset_class_def])
 >> CONJ_TAC
 >- (RW_TAC std_ss [IN_FUNSET, SPACE_SIGMA, IN_CROSS] \\
     FULL_SIMP_TAC std_ss [IN_FUNSET, o_DEF])
 >> RW_TAC std_ss [IN_PROD_SETS]
 >> RW_TAC std_ss [PREIMAGE_CROSS]
 >> `PREIMAGE (FST o f) t INTER PREIMAGE (SND o f) u INTER space a =
      (PREIMAGE (FST o f) t INTER space a) INTER
      (PREIMAGE (SND o f) u INTER space a)`
       by (RW_TAC std_ss [Once EXTENSION, IN_INTER] >> DECIDE_TAC)
 >> PROVE_TAC [sigma_algebra_def, ALGEBRA_INTER]
QED

(* |- !a a1 a2 f.
        sigma_algebra a /\ subset_class (space a1) (subsets a1) /\
        subset_class (space a2) (subsets a2) /\ FST o f IN measurable a a1 /\
        SND o f IN measurable a a2 ==>
        f IN measurable a (sigma (space a1 CROSS space a2)
                                 (prod_sets (subsets a1) (subsets a2)))
 *)
Theorem MEASURABLE_PROD_SIGMA =
    REWRITE_RULE [prod_sigma_def] MEASURABLE_PROD_SIGMA'

(* prod_sigma is indeed a sigma-algebra *)
Theorem SIGMA_ALGEBRA_PROD_SIGMA :
    !a b. subset_class (space a) (subsets a) /\
          subset_class (space b) (subsets b) ==> sigma_algebra (prod_sigma a b)
Proof
    RW_TAC std_ss [prod_sigma_def]
 >> MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA
 >> RW_TAC std_ss [subset_class_def, IN_PROD_SETS, GSPECIFICATION, IN_CROSS]
 >> fs [subset_class_def]
 >> RW_TAC std_ss [SUBSET_DEF, IN_CROSS]
 >> METIS_TAC [SUBSET_DEF]
QED

(* |- !X Y A B.
          subset_class X A /\ subset_class Y B ==>
          sigma_algebra ((X,A) CROSS (Y,B))
 *)
Theorem SIGMA_ALGEBRA_PROD_SIGMA' =
   Q.GENL [‘X’, ‘Y’, ‘A’, ‘B’]
          (REWRITE_RULE [space_def, subsets_def]
                        (Q.SPECL [‘(X,A)’, ‘(Y,B)’] SIGMA_ALGEBRA_PROD_SIGMA));

Theorem SPACE_PROD_SIGMA :
    !a b. space (prod_sigma a b) = space a CROSS space b
Proof
    rw [SPACE_SIGMA, prod_sigma_def]
QED

(* ------------------------------------------------------------------------- *)
(*  sigma-algebra of functions [7, p.55]                                     *)
(* ------------------------------------------------------------------------- *)

(* The smallest sigma-algebra on `sp` that makes `f` measurable *)
Definition sigma_function_def :
    sigma_function sp A f = (sp,IMAGE (\s. PREIMAGE f s INTER sp) (subsets A))
End

Overload sigma = “sigma_function”

Theorem space_sigma_function :
    !sp A f. space (sigma_function sp A f) = sp
Proof
    rw [sigma_function_def]
QED

(* For ‘sigma_function sp A f’ to be a sigma_algebra, A must be sigma_algebra *)
Theorem sigma_algebra_sigma_function :
    !sp A f. sigma_algebra A /\ f IN (sp -> space A) ==>
             sigma_algebra (sigma_function sp A f)
Proof
    rw [sigma_function_def]
 >> MATCH_MP_TAC PREIMAGE_SIGMA_ALGEBRA >> art []
QED

Theorem sigma_function_subset :
   !A B f. sigma_algebra A /\ f IN measurable A B ==>
           subsets (sigma (space A) B f) SUBSET subsets A
Proof
    rw [sigma_function_def]
 >> rw [SUBSET_DEF]
 >> rename1 ‘t IN subsets B’
 >> FULL_SIMP_TAC std_ss [IN_MEASURABLE]
QED

Theorem SIGMA_MEASURABLE :
    !sp A f. sigma_algebra A /\ f IN (sp -> space A) ==>
             f IN measurable (sigma sp A f) A
Proof
    RW_TAC std_ss [sigma_function_def, space_def, subsets_def,
                   IN_FUNSET, IN_MEASURABLE, IN_IMAGE]
 >> Q.EXISTS_TAC `s` >> art []
QED

(* Definition 7.5 of [7, p.51], The smallest sigma-algebra on `sp` that makes all `f`
   simultaneously measurable.
 *)
Definition sigma_functions_def :
    sigma_functions sp A f (J :'index set) =
      sigma sp (BIGUNION (IMAGE (\i. IMAGE (\s. PREIMAGE (f i) s INTER sp)
                                           (subsets (A i))) J))
End

Overload sigma = “sigma_functions”

Theorem space_sigma_functions :
    !sp A f (J :'index set). space (sigma_functions sp A f J) = sp
Proof
    rw [sigma_functions_def, SPACE_SIGMA]
QED

Theorem sigma_algebra_sigma_functions :
    !sp A f (J :'index set).
            (!i. f i IN (sp -> space (A i))) ==>
            sigma_algebra (sigma_functions sp A f J)
Proof
    rw [sigma_functions_def, IN_FUNSET]
 >> MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA
 >> rw [subset_class_def, IN_BIGUNION_IMAGE]
 >> rw [PREIMAGE_def]
QED

(* The sigma algebra generated from A/B-measurable functions does not exceed A *)
Theorem sigma_functions_subset :
    !A B f (J :'index set). sigma_algebra A /\
            (!i. i IN J ==> sigma_algebra (B i)) /\
            (!i. i IN J ==> f i IN measurable A (B i)) ==>
            subsets (sigma (space A) B f J) SUBSET subsets A
Proof
    rw [sigma_functions_def]
 >> MATCH_MP_TAC SIGMA_SUBSET >> art []
 >> rw [SUBSET_DEF, IN_BIGUNION_IMAGE]
 >> rename1 ‘t IN subsets (B i)’
 >> Q.PAT_X_ASSUM ‘!i. i IN J ==> f i IN measurable A (B n)’ (MP_TAC o (Q.SPEC ‘i’))
 >> rw [IN_MEASURABLE]
QED

(* ‘sigma_functions’ reduce to ‘sigma_function’ when there's only one function *)
Theorem sigma_functions_1 :
    !sp A f. sigma_algebra A /\ f 0 IN (sp -> space A) ==>
             sigma sp (\n. A) f (count 1) = sigma sp A (f 0)
Proof
    rw [sigma_functions_def]
 >> Know ‘BIGUNION
            (IMAGE (\n. IMAGE (\s. PREIMAGE (f n) s INTER sp) (subsets A)) (count 1))
          = IMAGE (\s. PREIMAGE (f 0) s INTER sp) (subsets A)’
 >- rw [Once EXTENSION, IN_BIGUNION_IMAGE]
 >> Rewr'
 >> Know ‘IMAGE (\s. PREIMAGE (f 0) s INTER sp) (subsets A) =
          subsets (sigma sp A (f 0))’
 >- rw [sigma_function_def]
 >> Rewr'
 >> Q.ABBREV_TAC ‘B = sigma sp A (f 0)’
 >> ‘sp = space B’ by METIS_TAC [space_sigma_function] >> POP_ORW
 >> MATCH_MP_TAC SIGMA_STABLE
 >> Q.UNABBREV_TAC ‘B’
 >> MATCH_MP_TAC sigma_algebra_sigma_function >> art []
QED

Theorem sigma_function_alt_sigma_functions :
    !sp A X. sigma_algebra A /\ X IN (sp -> space A) ==>
             sigma sp A X = sigma sp (\n. A) (\n x. X x) (count 1)
Proof
    rpt STRIP_TAC
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> Q.ABBREV_TAC ‘f = \n:num x. X x’
 >> ‘X = f 0’ by METIS_TAC [] >> POP_ORW
 >> MATCH_MP_TAC sigma_functions_1
 >> rw [Abbr ‘f’, ETA_THM]
QED

(* Lemma 7.5 of [7, p.51] *)
Theorem SIGMA_SIMULTANEOUSLY_MEASURABLE :
    !sp A f (J :'index set).
            (!i. i IN J ==> sigma_algebra (A i)) /\
            (!i. i IN J ==> f i IN (sp -> space (A i))) ==>
             !i. i IN J ==> f i IN measurable (sigma sp A f J) (A i)
Proof
    RW_TAC std_ss [IN_FUNSET, SPACE_SIGMA, sigma_functions_def, IN_MEASURABLE]
 >> Know `PREIMAGE (f i) s INTER sp IN
            (BIGUNION (IMAGE (\i. IMAGE (\s. PREIMAGE (f i) s INTER sp)
                                        (subsets (A i))) J))`
 >- (RW_TAC std_ss [IN_BIGUNION_IMAGE, IN_IMAGE] \\
     Q.EXISTS_TAC `i` >> art [] \\
     Q.EXISTS_TAC `s` >> art [])
 >> DISCH_TAC
 >> ASSUME_TAC
      (Q.SPECL [`sp`,
                `BIGUNION (IMAGE (\i. IMAGE (\s. PREIMAGE (f i) s INTER sp)
                                            (subsets (A i)))
                                 (J :'index set))`] SIGMA_SUBSET_SUBSETS)
 >> PROVE_TAC [SUBSET_DEF]
QED

(* Theorem 14.17 (i): alternative definition of product sigma-algebra [7, p.149]

   NOTE: previous antecedents ‘sigma_algebra A /\ sigma_algebra B’ has been weakened.
 *)
Theorem prod_sigma_alt_sigma_functions' :
    !A B. algebra A /\ algebra B ==>
          prod_sigma A B =
          sigma_functions (space A CROSS space B)
                          (binary A B) (binary FST SND) {0; 1 :num}
Proof
    rw [sigma_functions_def, binary_def]
 >> Q.ABBREV_TAC ‘sts = {a CROSS space B | a IN subsets A} UNION
                        {space A CROSS b | b IN subsets B}’
 >> Know ‘(IMAGE (\s. PREIMAGE FST s INTER (space A CROSS space B)) (subsets A) UNION
           IMAGE (\s. PREIMAGE SND s INTER (space A CROSS space B)) (subsets B)) =
           sts’
 >- (rw [Abbr ‘sts’, Once EXTENSION, PREIMAGE_def] \\
     EQ_TAC >> rw [] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       rename1 ‘s IN subsets A’ \\
       DISJ1_TAC >> Q.EXISTS_TAC ‘s’ >> art [] \\
       rw [Once EXTENSION, IN_CROSS] \\
       EQ_TAC >> rw [] \\
       Suff ‘s SUBSET space A’ >- METIS_TAC [SUBSET_DEF] \\
       FULL_SIMP_TAC std_ss [algebra_def, subset_class_def],
       (* goal 2 (of 4) *)
       rename1 ‘s IN subsets B’ \\
       DISJ2_TAC >> Q.EXISTS_TAC ‘s’ >> art [] \\
       rw [Once EXTENSION, IN_CROSS] \\
       EQ_TAC >> rw [] \\
       Suff ‘s SUBSET space B’ >- METIS_TAC [SUBSET_DEF] \\
       FULL_SIMP_TAC std_ss [algebra_def, subset_class_def],
       (* goal 3 (of 4) *)
       DISJ1_TAC >> Q.EXISTS_TAC ‘a’ >> art [] \\
       rw [Once EXTENSION, IN_CROSS] \\
       EQ_TAC >> rw [] \\
       Suff ‘a SUBSET space A’ >- METIS_TAC [SUBSET_DEF] \\
       FULL_SIMP_TAC std_ss [algebra_def, subset_class_def],
       (* goal 4 (of 4) *)
       DISJ2_TAC >> Q.EXISTS_TAC ‘b’ >> art [] \\
       rw [Once EXTENSION, IN_CROSS] \\
       EQ_TAC >> rw [] \\
       Suff ‘b SUBSET space B’ >- METIS_TAC [SUBSET_DEF] \\
       FULL_SIMP_TAC std_ss [algebra_def, subset_class_def] ])
 >> Rewr'
 >> ‘sts SUBSET subsets (sigma (space A CROSS space B) sts)’
       by PROVE_TAC [SIGMA_SUBSET_SUBSETS]
 >> Know ‘sigma_algebra (sigma (space A CROSS space B) sts)’
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
     rw [Abbr ‘sts’, subset_class_def, SUBSET_DEF] \\
     fs [IN_CROSS] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       rename1 ‘FST y IN a’ \\
       Suff ‘a SUBSET space A’ >- METIS_TAC [SUBSET_DEF] \\
       FULL_SIMP_TAC std_ss [algebra_def, subset_class_def],
       (* goal 2 (of 2) *)
       rename1 ‘SND y IN b’ \\
       Suff ‘b SUBSET space B’ >- METIS_TAC [SUBSET_DEF] \\
       FULL_SIMP_TAC std_ss [algebra_def, subset_class_def] ])
 >> DISCH_TAC
 >> Know ‘prod_sets (subsets A) (subsets B) SUBSET
          subsets (sigma (space A CROSS space B) sts)’
 >- (rw [SUBSET_DEF, IN_PROD_SETS] \\
     Know ‘t CROSS u = (t CROSS space B) INTER (space A CROSS u)’
     >- (rw [Once EXTENSION, IN_CROSS] \\
         EQ_TAC >> rw [] >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           Suff ‘u SUBSET space B’ >- METIS_TAC [SUBSET_DEF] \\
           FULL_SIMP_TAC std_ss [algebra_def, subset_class_def],
           (* goal 2 (of 2) *)
           Suff ‘t SUBSET space A’ >- METIS_TAC [SUBSET_DEF] \\
           FULL_SIMP_TAC std_ss [algebra_def, subset_class_def] ]) \\
     Rewr' \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER \\
     RW_TAC std_ss [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Suff ‘t CROSS space B IN sts’ >- METIS_TAC [SUBSET_DEF] \\
       Q.UNABBREV_TAC ‘sts’ >> rw [] \\
       DISJ1_TAC >> Q.EXISTS_TAC ‘t’ >> art [],
       (* goal 2 (of 2) *)
       Suff ‘space A CROSS u IN sts’ >- METIS_TAC [SUBSET_DEF] \\
       Q.UNABBREV_TAC ‘sts’ >> rw [] \\
       DISJ2_TAC >> Q.EXISTS_TAC ‘u’ >> art [] ])
 >> DISCH_TAC
 >> REWRITE_TAC [prod_sigma_def, Once EQ_SYM_EQ]
 >> Suff ‘subsets (sigma (space A CROSS space B) sts) =
          subsets (sigma (space A CROSS space B)
                         (prod_sets (subsets A) (subsets B)))’
 >- METIS_TAC [SPACE, SPACE_SIGMA]
 >> MATCH_MP_TAC SIGMA_SMALLEST >> art []
 >> reverse CONJ_TAC
 >- METIS_TAC [SPACE, SPACE_SIGMA]
 >> MP_TAC (Q.SPECL [‘sts’, ‘(sigma (space A CROSS space B)
                                    (prod_sets (subsets A) (subsets B)))’]
                    (INST_TYPE [“:'a” |-> “:'a # 'a”] SIGMA_SUBSET))
 >> REWRITE_TAC [SPACE_SIGMA]
 >> DISCH_THEN MATCH_MP_TAC
 >> CONJ_TAC
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
     rw [subset_class_def, IN_PROD_SETS] \\
     MATCH_MP_TAC SUBSET_CROSS \\
     FULL_SIMP_TAC std_ss [algebra_def, subset_class_def])
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC ‘prod_sets (subsets A) (subsets B)’
 >> REWRITE_TAC [SIGMA_SUBSET_SUBSETS]
 >> rw [Abbr ‘sts’, SUBSET_DEF, IN_PROD_SETS]
 >| [ (* goal 1 (of 2) *)
      qexistsl_tac [‘a’, ‘space B’] >> art [] \\
      MATCH_MP_TAC ALGEBRA_SPACE >> art [],
      (* goal 2 (of 2) *)
      qexistsl_tac [‘space A’, ‘b’] >> art [] \\
      MATCH_MP_TAC ALGEBRA_SPACE >> art [] ]
QED

(* for compatibility purposes (and sometimes more applicable) *)
Theorem prod_sigma_alt_sigma_functions :
    !A B. sigma_algebra A /\ sigma_algebra B ==>
          prod_sigma A B =
          sigma_functions (space A CROSS space B)
                          (binary A B) (binary FST SND) {0; 1 :num}
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC prod_sigma_alt_sigma_functions'
 >> CONJ_TAC (* 2 subgoals, same tactics *)
 >> MATCH_MP_TAC SIGMA_ALGEBRA_ALGEBRA >> art []
QED

(* ------------------------------------------------------------------------- *)
(*   Pre-images (and images) of sigma generator                              *)
(* ------------------------------------------------------------------------- *)

(* The proof is learnt from https://math.stackexchange.com/questions/1496875 *)
Theorem PREIMAGE_SIGMA_SUBSET[local] :
    !Z sp sts f. subset_class sp sts /\ f IN (Z -> sp) ==>
                 IMAGE (\s. PREIMAGE f s INTER Z) (subsets (sigma sp sts)) SUBSET
                 subsets (sigma Z (IMAGE (\s. PREIMAGE f s INTER Z) sts))
Proof
    rpt STRIP_TAC
 (* applying PREIMAGE_SIGMA_ALGEBRA *)
 >> Know ‘sigma_algebra (Z,IMAGE (\s. PREIMAGE f s INTER Z) (subsets (sigma sp sts)))’
 >- (MATCH_MP_TAC PREIMAGE_SIGMA_ALGEBRA >> rw [SPACE_SIGMA] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA >> art [])
 >> DISCH_TAC
 (* stage work *)
 >> rw [SUBSET_DEF]
 >> rename1 ‘u IN subsets (sigma sp sts)’
 >> Q.ABBREV_TAC ‘D = {G | G SUBSET sp /\
                           PREIMAGE f G INTER Z IN
                           subsets (sigma Z (IMAGE (\s. PREIMAGE f s INTER Z) sts))}’
 >> Suff ‘sts SUBSET D /\ sigma_algebra (sp,D)’
 >- (STRIP_TAC \\
     Know ‘subsets (sigma (space (sp,D)) sts) SUBSET subsets (sp,D)’
     >- (MATCH_MP_TAC SIGMA_SUBSET >> art [subsets_def]) \\
     REWRITE_TAC [space_def, subsets_def] \\
     DISCH_TAC \\
     Know ‘u IN D’ >- METIS_TAC [SUBSET_DEF] \\
     rw [Abbr ‘D’, GSPECIFICATION])
 >> CONJ_TAC (* sts SUBSET D *)
 >- (Know ‘(IMAGE (\s. PREIMAGE f s INTER Z) sts) SUBSET
             subsets (sigma Z (IMAGE (\s. PREIMAGE f s INTER Z) sts))’
     >- (rw [SIGMA_SUBSET_SUBSETS]) \\
     rw [SUBSET_DEF, Abbr ‘D’]
     >- (rename [‘s IN sts’, ‘x IN s’] \\
         METIS_TAC [subset_class_def, SUBSET_DEF]) \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘x’ >> art [])
 (* final stage *)
 >> Know ‘sigma_algebra (sigma Z (IMAGE (\s. PREIMAGE f s INTER Z) sts))’
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA \\
     rw [subset_class_def] \\
     REWRITE_TAC [INTER_SUBSET])
 >> DISCH_TAC
 >> rw [sigma_algebra_alt_pow] (* 4 subgoals *)
 >| [ (* goal 1 (of 4) *)
      rw [SUBSET_DEF, IN_POW, Abbr ‘D’],
      (* goal 2 (of 4) *)
      rw [Abbr ‘D’] \\
      MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY >> art [],
      (* goal 3 (of 4) *)
      fs [Abbr ‘D’] \\
      Know ‘PREIMAGE f (sp DIFF s) INTER Z =
              (space (sigma Z (IMAGE (\s. PREIMAGE f s INTER Z) sts)))
              DIFF (PREIMAGE f s INTER Z)’
      >- (REWRITE_TAC [SPACE_SIGMA] \\
          rw [Once EXTENSION, GSPECIFICATION] \\
          METIS_TAC [IN_FUNSET]) >> Rewr' \\
      MATCH_MP_TAC SIGMA_ALGEBRA_COMPL >> art [],
      (* goal 4 (of 4) *)
      POP_ASSUM MP_TAC \\
      rw [Abbr ‘D’, SUBSET_DEF] >- METIS_TAC [] \\
      Know ‘PREIMAGE f (BIGUNION {A i | i | T}) INTER Z =
            BIGUNION (IMAGE (\i. PREIMAGE f (A i) INTER Z) UNIV)’
      >- (rw [Once EXTENSION, IN_PREIMAGE, IN_BIGUNION_IMAGE] \\
          METIS_TAC []) >> Rewr' \\
      Q.PAT_X_ASSUM ‘sigma_algebra (sigma Z (IMAGE (\s. PREIMAGE f s INTER Z) sts))’
        (MP_TAC o REWRITE_RULE [SIGMA_ALGEBRA_ALT]) \\
      rw [IN_FUNSET] \\
      POP_ASSUM MATCH_MP_TAC >> rw [] \\
      METIS_TAC [] ]
QED

Theorem PREIMAGE_SIGMA :
    !Z sp sts f. subset_class sp sts /\ f IN (Z -> sp) ==>
                 IMAGE (\s. PREIMAGE f s INTER Z) (subsets (sigma sp sts)) =
                 subsets (sigma Z (IMAGE (\s. PREIMAGE f s INTER Z) sts))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC SUBSET_ANTISYM
 >> CONJ_TAC
 >- (MATCH_MP_TAC PREIMAGE_SIGMA_SUBSET >> art [])
 >> fs [IN_FUNSET]
 >> ‘sigma_algebra (sigma sp sts)’ by PROVE_TAC [SIGMA_ALGEBRA_SIGMA]
 >> MATCH_MP_TAC SIGMA_PROPERTY_ALT
 >> rw [IN_FUNSET] (* 5 subgoals *)
 >| [ (* goal 1 (of 5) *)
      rw [subset_class_def] >> REWRITE_TAC [INTER_SUBSET],
      (* goal 2 (of 5) *)
      Q.EXISTS_TAC ‘{}’ >> rw [PREIMAGE_EMPTY] \\
      MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY >> art [],
      (* goal 3 (of 5) *)
      rw [SUBSET_DEF] >> rename1 ‘s IN sts’ \\
      Q.EXISTS_TAC ‘s’ >> REWRITE_TAC [] \\
      METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF],
      (* goal 4 (of 5) *)
      rename1 ‘s IN subsets (sigma sp sts)’ \\
      Q.EXISTS_TAC ‘(space (sigma sp sts)) DIFF s’ \\
      reverse CONJ_TAC
      >- (MATCH_MP_TAC SIGMA_ALGEBRA_COMPL >> art []) \\
      rw [Once EXTENSION, SPACE_SIGMA] >> METIS_TAC [],
      (* goal 5 (of 5) *)
      Know ‘(!x. f' x IN subsets (sigma Z (IMAGE (\s. PREIMAGE f s INTER Z) sts))) /\
            (!x. (?s. f' x = PREIMAGE f s INTER Z /\ s IN subsets (sigma sp sts)))’
      >- METIS_TAC [] \\
      POP_ASSUM K_TAC >> STRIP_TAC \\
      fs [SKOLEM_THM] \\
      Know ‘(!x. f' x = PREIMAGE f (f'' x) INTER Z) /\
            (!x. f'' x IN subsets (sigma sp sts))’ >- METIS_TAC [] \\
      POP_ASSUM K_TAC >> STRIP_TAC \\
      rename1 ‘!x. g x = PREIMAGE f (h x) INTER Z’ \\
      Q.EXISTS_TAC ‘BIGUNION (IMAGE h UNIV)’ \\
      reverse CONJ_TAC
      >- (Q.PAT_X_ASSUM ‘sigma_algebra (sigma sp sts)’
            (MP_TAC o REWRITE_RULE [SIGMA_ALGEBRA_ALT]) \\
          rw [IN_FUNSET]) \\
      rw [Once EXTENSION, IN_PREIMAGE, IN_BIGUNION_IMAGE] >> METIS_TAC [] ]
QED

(* A good corollary of PREIMAGE_SIGMA *)
Theorem IMAGE_SIGMA :
    !sp sts f. subset_class sp sts /\ BIJ f sp (IMAGE f sp) ==>
               IMAGE (IMAGE f) (subsets (sigma sp sts)) =
               subsets (sigma (IMAGE f sp) (IMAGE (IMAGE f) sts))
Proof
    rpt STRIP_TAC
 >> MP_TAC (MATCH_MP BIJ_INV
                     (ASSUME “BIJ (f :'a -> 'b) (sp :'a -> bool) (IMAGE f sp)”))
 >> rw []
 >> qabbrev_tac ‘Z = IMAGE f sp’
 >> qabbrev_tac ‘H = \s. PREIMAGE g s INTER Z’
 >> Know ‘IMAGE (IMAGE f) sts = IMAGE H sts’
 >- (rw [Abbr ‘H’, FUN_EQ_THM, Once EXTENSION, PREIMAGE_def] \\
     EQ_TAC >> rw [Abbr ‘Z’]
     >- (rename1 ‘s IN sts’ >> Q.EXISTS_TAC ‘s’ >> rw [] \\
         EQ_TAC >> rw [] >| (* 3 subgoals *)
         [ (* goal 1 (of 3) *)
           rename1 ‘g (f y) IN s’ \\
           Suff ‘g (f y) = y’ >- rw [] \\
           FIRST_X_ASSUM MATCH_MP_TAC \\
           POP_ASSUM MP_TAC \\
           Suff ‘s SUBSET sp’ >- rw [SUBSET_DEF] \\
           fs [subset_class_def],
           (* goal 2 (of 3) *)
           rename1 ‘y IN s’ >> Q.EXISTS_TAC ‘y’ >> rw [] \\
           POP_ASSUM MP_TAC \\
           Suff ‘s SUBSET sp’ >- rw [SUBSET_DEF] \\
           fs [subset_class_def],
           (* goal 3 (of 3) *)
           rename1 ‘y IN sp’ >> Q.EXISTS_TAC ‘y’ >> rw [] \\
           Suff ‘g (f y) = y’ >- PROVE_TAC [] \\
           FIRST_X_ASSUM MATCH_MP_TAC \\
           POP_ASSUM MP_TAC \\
           Suff ‘s SUBSET sp’ >- rw [SUBSET_DEF] \\
           fs [subset_class_def] ]) \\
    rename1 ‘s IN sts’ \\
    Q.EXISTS_TAC ‘s’ >> rw [] \\
    EQ_TAC >> rw [] >| (* 3 subgoals *)
    [ (* goal 1 (of 3) *)
      rename1 ‘y IN sp’ >> Q.EXISTS_TAC ‘y’ >> rw [] \\
      Suff ‘g (f y) = y’ >- PROVE_TAC [] \\
      FIRST_X_ASSUM MATCH_MP_TAC \\
      POP_ASSUM MP_TAC \\
      Suff ‘s SUBSET sp’ >- rw [SUBSET_DEF] \\
      fs [subset_class_def],
      (* goal 2 (of 3) *)
      rename1 ‘g (f y) IN s’ \\
      Suff ‘g (f y) = y’ >- PROVE_TAC [] \\
      FIRST_X_ASSUM MATCH_MP_TAC \\
      POP_ASSUM MP_TAC \\
      Suff ‘s SUBSET sp’ >- rw [SUBSET_DEF] \\
      fs [subset_class_def],
      (* goal 3 (of 3) *)
      rename1 ‘y IN s’ >> Q.EXISTS_TAC ‘y’ >> rw [] \\
      POP_ASSUM MP_TAC \\
      Suff ‘s SUBSET sp’ >- rw [SUBSET_DEF] \\
      fs [subset_class_def] ])
 >> Rewr'
 >> qabbrev_tac ‘a = sigma sp sts’
 >> ‘sigma_algebra a’ by rw [Abbr ‘a’, SIGMA_ALGEBRA_SIGMA]
 >> Know ‘IMAGE (IMAGE f) (subsets a) = IMAGE H (subsets a)’
 >- (rw [Abbr ‘H’, Once EXTENSION, PREIMAGE_def] \\
     EQ_TAC >> rw [Abbr ‘Z’]
     >- (rename1 ‘s IN subsets a’ \\
         Q.EXISTS_TAC ‘s’ >> art [] \\
         rw [Once EXTENSION] \\
         EQ_TAC >> rw [] >| (* 3 subgoals *)
         [ (* goal 1 (of 3) *)
           rename1 ‘g (f y) IN s’ \\
           Suff ‘g (f y) = y’ >- rw [] \\
           FIRST_X_ASSUM MATCH_MP_TAC \\
           POP_ASSUM MP_TAC \\
           Suff ‘s SUBSET sp’ >- rw [SUBSET_DEF] \\
          ‘space a = sp’ by rw [Abbr ‘a’, SPACE_SIGMA] \\
           fs [sigma_algebra_def, algebra_def, subset_class_def],
           (* goal 2 (of 3) *)
           rename1 ‘y IN s’ >> Q.EXISTS_TAC ‘y’ >> rw [] \\
           POP_ASSUM MP_TAC \\
           Suff ‘s SUBSET sp’ >- rw [SUBSET_DEF] \\
          ‘space a = sp’ by rw [Abbr ‘a’, SPACE_SIGMA] \\
           fs [sigma_algebra_def, algebra_def, subset_class_def],
           (* goal 3 (of 3) *)
           rename1 ‘y IN sp’ >> Q.EXISTS_TAC ‘y’ >> rw [] \\
           Suff ‘g (f y) = y’ >- PROVE_TAC [] \\
           FIRST_X_ASSUM MATCH_MP_TAC >> art [] ]) \\
     rename1 ‘s IN subsets a’ \\
     Q.EXISTS_TAC ‘s’ >> art [] \\
     rw [Once EXTENSION] \\
     EQ_TAC >> rw []
     >- (rename1 ‘y IN sp’ >> Q.EXISTS_TAC ‘y’ >> art [] \\
         Suff ‘g (f y) = y’ >- PROVE_TAC [] \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art [])
     >- (rename1 ‘g (f y) IN s’ \\
         Suff ‘g (f y) = y’ >- rw [] \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
         POP_ASSUM MP_TAC \\
         Suff ‘s SUBSET sp’ >- rw [SUBSET_DEF] \\
        ‘space a = sp’ by rw [Abbr ‘a’, SPACE_SIGMA] \\
         fs [sigma_algebra_def, algebra_def, subset_class_def]) \\
     rename1 ‘y IN s’ >> Q.EXISTS_TAC ‘y’ >> art [] \\
     POP_ASSUM MP_TAC \\
     Suff ‘s SUBSET sp’ >- rw [SUBSET_DEF] \\
    ‘space a = sp’ by rw [Abbr ‘a’, SPACE_SIGMA] \\
     fs [sigma_algebra_def, algebra_def, subset_class_def])
 >> Rewr'
 >> qunabbrevl_tac [‘H’, ‘a’]
 >> MATCH_MP_TAC PREIMAGE_SIGMA
 >> rw [Abbr ‘Z’, IN_FUNSET]
 >> rename1 ‘g (f y) IN sp’
 >> Suff ‘g (f y) = y’ >- rw []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

Theorem IMAGE_SIGMA_ALGEBRA :
    !sp sts f. sigma_algebra (sp,sts) /\ BIJ f sp (IMAGE f sp) ==>
               sigma_algebra (IMAGE f sp,IMAGE (IMAGE f) sts)
Proof
    rw [sigma_algebra_alt_pow]
 >| [ (* goal 1 (of 3) *)
      rw [SUBSET_DEF, IN_POW] \\
      rename1 ‘y IN IMAGE f s’ >> fs [IN_IMAGE] \\
      Q.EXISTS_TAC ‘x’ >> art [] \\
      Q.PAT_X_ASSUM ‘sts SUBSET POW sp’ MP_TAC \\
      rw [SUBSET_DEF, IN_POW] \\
      POP_ASSUM irule \\
      Q.EXISTS_TAC ‘s’ >> art [],
      (* goal 2 (of 3) *)
      rename1 ‘s IN sts’ \\
      Q.EXISTS_TAC ‘sp DIFF s’ \\
      reverse CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
      rw [Once EXTENSION] \\
      EQ_TAC >> rw [] >| (* 3 subgoals *)
      [ (* goal 2.1 (of 3) *)
        rename1 ‘y IN sp’ \\
        Q.EXISTS_TAC ‘y’ >> art [] \\
        POP_ASSUM MATCH_MP_TAC >> art [],
        (* goal 2.2 (of 3) *)
        rename1 ‘y IN sp’ \\
        Q.EXISTS_TAC ‘y’ >> art [],
        (* goal 2.3 (of 3) *)
        rename1 ‘f x = f y’ \\
        Q.PAT_X_ASSUM ‘BIJ f sp _’ MP_TAC \\
        simp [BIJ_ALT, IN_FUNSET, EXISTS_UNIQUE_ALT] \\
        DISCH_THEN (MP_TAC o Q.SPEC ‘f x’) \\
        impl_tac >- (Q.EXISTS_TAC ‘y’ >> art []) \\
        DISCH_THEN (Q.X_CHOOSE_THEN ‘z’ STRIP_ASSUME_TAC) \\
        CCONTR_TAC >> fs [] \\
        Suff ‘x IN sp’ >- METIS_TAC [] \\
        Q.PAT_X_ASSUM ‘sts SUBSET POW sp’ MP_TAC \\
        rw [SUBSET_DEF, IN_POW] \\
        POP_ASSUM irule \\
        Q.EXISTS_TAC ‘s’ >> art [] ],
      (* goal 3 (of 3) *)
      Know ‘BIGUNION {A i | i | T} = BIGUNION (IMAGE A UNIV)’
      >- (rw [Once EXTENSION, IN_BIGUNION_IMAGE] \\
          EQ_TAC >> rw [] >- (Q.EXISTS_TAC ‘i’ >> art []) \\
          rename1 ‘x IN A i’ \\
          Q.EXISTS_TAC ‘A i’ >> art [] \\
          Q.EXISTS_TAC ‘i’ >> art []) >> Rewr' \\
      POP_ASSUM MP_TAC >> rw [SUBSET_DEF] \\
      IMP_RES_TAC BIJ_INV \\
      Q.EXISTS_TAC ‘BIGUNION (IMAGE (IMAGE g o A) UNIV)’ \\
      simp [IMAGE_BIGUNION, IMAGE_IMAGE] \\
      CONJ_TAC
      >- (AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC \\
          rw [Once EXTENSION, o_DEF, FUN_EQ_THM] \\
          reverse EQ_TAC >> rw []
          >- (rename1 ‘f (g y) IN A i’ \\
              fs [o_DEF] \\
              Suff ‘f (g y) = y’ >- rw [] \\
              FIRST_ASSUM MATCH_MP_TAC \\
              Q.PAT_X_ASSUM ‘!x. _ ==> ?x. _’ (MP_TAC o Q.SPEC ‘A (i :num)’) \\
              impl_tac >- (Q.EXISTS_TAC ‘i’ >> art []) \\
              DISCH_THEN (Q.X_CHOOSE_THEN ‘j’ STRIP_ASSUME_TAC) \\
              Q.PAT_X_ASSUM ‘A i = IMAGE f j’ (fs o wrap) \\
              Q.EXISTS_TAC ‘x’ >> art [] \\
              Q.PAT_X_ASSUM ‘sts SUBSET POW sp’ MP_TAC \\
              rw [SUBSET_DEF, IN_POW] \\
              POP_ASSUM irule \\
              Q.EXISTS_TAC ‘j’ >> art []) \\
          rename1 ‘y IN A i’ \\
          fs [o_DEF] \\
          Q.EXISTS_TAC ‘g y’ \\
          reverse CONJ_TAC >- (Q.EXISTS_TAC ‘y’ >> art []) \\
          ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
          FIRST_ASSUM MATCH_MP_TAC \\
          Q.PAT_X_ASSUM ‘!x. _ ==> ?x. _’ (MP_TAC o Q.SPEC ‘A (i :num)’) \\
          impl_tac >- (Q.EXISTS_TAC ‘i’ >> art []) \\
          DISCH_THEN (Q.X_CHOOSE_THEN ‘j’ STRIP_ASSUME_TAC) \\
          Q.PAT_X_ASSUM ‘A i = IMAGE f j’ (fs o wrap) \\
          Q.EXISTS_TAC ‘x’ >> art [] \\
          Q.PAT_X_ASSUM ‘sts SUBSET POW sp’ MP_TAC \\
          rw [SUBSET_DEF, IN_POW] \\
          POP_ASSUM irule \\
          Q.EXISTS_TAC ‘j’ >> art []) \\
      qabbrev_tac ‘B = IMAGE g o A’ \\
      Know ‘BIGUNION {B i | i | T} = BIGUNION (IMAGE B UNIV)’
      >- (rw [Once EXTENSION, IN_BIGUNION_IMAGE] \\
          EQ_TAC >> rw [] >- (Q.EXISTS_TAC ‘i’ >> art []) \\
          rename1 ‘x IN B i’ \\
          Q.EXISTS_TAC ‘B i’ >> art [] \\
          Q.EXISTS_TAC ‘i’ >> art []) \\
      DISCH_THEN (REWRITE_TAC o wrap o SYM) \\
      FIRST_X_ASSUM MATCH_MP_TAC \\
      rw [Abbr ‘B’, SUBSET_DEF] \\
      rename1 ‘IMAGE g (A i) IN sts’ \\
      Q.PAT_X_ASSUM ‘!x. _ ==> ?x. _’ (MP_TAC o Q.SPEC ‘A (i :num)’) \\
      impl_tac >- (Q.EXISTS_TAC ‘i’ >> art []) \\
      DISCH_THEN (Q.X_CHOOSE_THEN ‘s’ STRIP_ASSUME_TAC) \\
      Q.PAT_X_ASSUM ‘A i = IMAGE f s’ (fs o wrap) \\
      Suff ‘IMAGE g (IMAGE f s) = s’ >- rw [] \\
      rw [Once EXTENSION] \\
      reverse EQ_TAC >> rw []
      >- (Q.EXISTS_TAC ‘f x’ \\
          reverse CONJ_TAC >- (Q.EXISTS_TAC ‘x’ >> art []) \\
          ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
          FIRST_X_ASSUM MATCH_MP_TAC \\
          Q.PAT_X_ASSUM ‘sts SUBSET POW sp’ MP_TAC \\
          rw [SUBSET_DEF, IN_POW] \\
          POP_ASSUM irule \\
          Q.EXISTS_TAC ‘s’ >> art []) \\
      rename1 ‘g (f y) IN s’ \\
      Suff ‘g (f y) = y’ >- rw [] \\
      FIRST_X_ASSUM MATCH_MP_TAC \\
      Q.PAT_X_ASSUM ‘sts SUBSET POW sp’ MP_TAC \\
      rw [SUBSET_DEF, IN_POW] \\
      POP_ASSUM irule \\
      Q.EXISTS_TAC ‘s’ >> art [] ]
QED

(* Lemma 2.2.5 of [9, p.177] (moving INTER outside of the sigma generator) *)
Theorem SIGMA_RESTRICT :
    !sp sts B. subset_class sp sts /\ B SUBSET sp ==>
               sigma_algebra (B,IMAGE (\s. s INTER B) (subsets (sigma sp sts))) /\
               subsets (sigma B (IMAGE (\s. s INTER B) sts)) =
               IMAGE (\s. s INTER B) (subsets (sigma sp sts))
Proof
    rpt STRIP_TAC
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_RESTRICT' \\
     Q.EXISTS_TAC ‘sp’ \\
     rw [SIGMA_REDUCE, SIGMA_ALGEBRA_SIGMA])
 >> MP_TAC (Q.SPECL [‘B’, ‘sp’, ‘sts’, ‘I’]
                    (INST_TYPE [“:'b” |-> “:'a”] PREIMAGE_SIGMA))
 >> FULL_SIMP_TAC std_ss [SUBSET_DEF]
 >> rw [IN_FUNSET]
QED

(* Example 3.3 (vi) [7, p.17] (another form of SIGMA_ALGEBRA_RESTRICT') *)
Theorem TRACE_SIGMA_ALGEBRA :
    !a E. sigma_algebra a /\ E SUBSET (space a) ==>
          sigma_algebra (E,{A INTER E | A IN subsets a})
Proof
    rpt STRIP_TAC
 >> Know ‘{A INTER E | A IN subsets a} = IMAGE (\s. s INTER E) (subsets a)’
 >- rw [Once EXTENSION, IN_IMAGE]
 >> Rewr'
 >> MATCH_MP_TAC SIGMA_ALGEBRA_RESTRICT'
 >> Q.EXISTS_TAC ‘space a’ >> rw [SPACE]
QED

(* Lemma 14.1 of [7, p.137] (not used anywhere) *)
Theorem SEMIRING_PROD_SETS :
    !a b. semiring a /\ semiring b ==>
          semiring ((space a CROSS space b),prod_sets (subsets a) (subsets b))
Proof
    rpt STRIP_TAC
 >> RW_TAC std_ss [semiring_def, space_def, subsets_def]
 (* subset_class *)
 >- (RW_TAC std_ss [subset_class_def, IN_PROD_SETS, GSPECIFICATION] \\
     RW_TAC std_ss [SUBSET_DEF, IN_CROSS] >| (* 2 subgoals, same ending *)
     [ Suff ‘t SUBSET space a’ >- rw [SUBSET_DEF],
       Suff ‘u SUBSET space b’ >- rw [SUBSET_DEF] ] \\
     PROVE_TAC [subset_class_def, semiring_def])
 (* EMPTY *)
 >- (RW_TAC std_ss [IN_CROSS, IN_PROD_SETS, GSPECIFICATION, Once EXTENSION,
                    NOT_IN_EMPTY] \\
     qexistsl_tac [‘{}’, ‘{}’] >> fs [semiring_def])
 (* INTER *)
 >- (fs [IN_PROD_SETS] \\
     rename1 ‘s = t1 CROSS u1’ \\
     rename1 ‘t = t2 CROSS u2’ \\
     qexistsl_tac [`t1 INTER t2`, `u1 INTER u2`] \\
     reverse CONJ_TAC >- METIS_TAC [SEMIRING_INTER] \\
     RW_TAC std_ss [Once EXTENSION, IN_CROSS, IN_INTER] >> PROVE_TAC [])
 (* DIFF (hard) *)
 >> fs [prod_sets_def]
 >> rename1 `s = A CROSS B`
 >> rename1 `t = A' CROSS B'`
 >> REWRITE_TAC [DIFF_INTER_COMPL]
 >> Know `COMPL (A' CROSS B') =
          (COMPL A' CROSS B') UNION (A' CROSS COMPL B') UNION
          (COMPL A' CROSS COMPL B')`
 >- (RW_TAC std_ss [Once EXTENSION, IN_CROSS, IN_COMPL, IN_UNION] \\
     PROVE_TAC []) >> Rewr'
 >> REWRITE_TAC [UNION_OVER_INTER]
 >> REWRITE_TAC [INTER_CROSS, GSYM DIFF_INTER_COMPL]
 >> `?c1. c1 SUBSET subsets a /\ FINITE c1 /\ disjoint c1 /\
          (A DIFF A' = BIGUNION c1)` by METIS_TAC [semiring_def] >> art []
 >> `?c2. c2 SUBSET subsets b /\ FINITE c2 /\ disjoint c2 /\
          (B DIFF B' = BIGUNION c2)` by METIS_TAC [semiring_def] >> art []
 (* applying finite_disjoint_decomposition *)
 >> Know `FINITE c1 /\ disjoint c1` >- art []
 >> DISCH_THEN (MP_TAC o (MATCH_MP finite_disjoint_decomposition))
 >> DISCH_THEN (qx_choosel_then [`f1`, `n1`] STRIP_ASSUME_TAC)
 >> Know `FINITE c2 /\ disjoint c2` >- art []
 >> DISCH_THEN (MP_TAC o (MATCH_MP finite_disjoint_decomposition))
 >> DISCH_THEN (qx_choosel_then [`f2`, `n2`] STRIP_ASSUME_TAC)
 >> ASM_REWRITE_TAC [] (* rewrite c1 and c2 in the goal *)
 >> Know `BIGUNION (IMAGE f1 (count n1)) CROSS (B INTER B') =
          BIGUNION (IMAGE (\n. f1 n CROSS (B INTER B')) (count n1))`
 >- (RW_TAC std_ss [Once EXTENSION, IN_BIGUNION_IMAGE, IN_CROSS,
                    IN_COUNT] >> PROVE_TAC []) >> Rewr'
 >> Know `(A INTER A') CROSS BIGUNION (IMAGE f2 (count n2)) =
          BIGUNION (IMAGE (\n. (A INTER A') CROSS f2 n) (count n2))`
 >- (RW_TAC std_ss [Once EXTENSION, IN_BIGUNION_IMAGE, IN_CROSS,
                    IN_COUNT] >> PROVE_TAC []) >> Rewr'
 >> Know `BIGUNION (IMAGE f1 (count n1)) CROSS
          BIGUNION (IMAGE f2 (count n2)) =
          BIGUNION (IMAGE (\(i,j). f1 i CROSS f2 j) (count n1 CROSS count n2))`
 >- (RW_TAC std_ss [Once EXTENSION, IN_BIGUNION_IMAGE, IN_CROSS, IN_COUNT] \\
     EQ_TAC >> rpt STRIP_TAC >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       rename1 `y < n1` >> rename1 `z < n2` \\
       Q.EXISTS_TAC `(y,z)` >> fs [],
       (* goal 2 (of 3) *)
       rename1 `FST z < n1` \\
       Q.EXISTS_TAC `FST z` >> art [] \\
       Cases_on `z` >> fs [],
       (* goal 3 (of 3) *)
       rename1 `SND z < n2` \\
       Q.EXISTS_TAC `SND z` >> art [] \\
       Cases_on `z` >> fs [] ]) >> Rewr'
 >> Q.EXISTS_TAC `(IMAGE (\n. f1 n CROSS (B INTER B')) (count n1)) UNION
                  (IMAGE (\n. (A INTER A') CROSS f2 n) (count n2)) UNION
                  (IMAGE (\(i,j). f1 i CROSS f2 j) (count n1 CROSS count n2))`
 >> rw [BIGUNION_UNION] (* 4 subgoals, first 3 are easy *)
 >- (RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, GSPECIFICATION] \\
     Q.EXISTS_TAC `(f1 n,B INTER B')` >> rw []
     >- fs [SUBSET_DEF, IN_IMAGE, IN_COUNT] \\
     fs [semiring_def])
 >- (RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, GSPECIFICATION] \\
     Q.EXISTS_TAC `(A INTER A',f2 n)` >> rw []
     >- fs [semiring_def] \\
     fs [SUBSET_DEF, IN_IMAGE, IN_COUNT])
 >- (RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, GSPECIFICATION] \\
     rename1 `y IN count n1 CROSS count n2` \\
     Cases_on `y` >> fs [IN_CROSS, IN_COUNT] \\
     Q.EXISTS_TAC `(f1 q,f2 r)` >> fs [SUBSET_DEF, IN_IMAGE, IN_COUNT] \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       FIRST_X_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC `q` >> art [],
       (* goal 2 (of 2) *)
       FIRST_X_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC `r` >> art [] ])
 >> RW_TAC std_ss [disjoint_def, IN_IMAGE, IN_COUNT, IN_CROSS, IN_UNION]
 (* 9 (3 * 3) subgoals *)
 >| [ (* goal 1 (of 9) *)
      MATCH_MP_TAC DISJOINT_CROSS_L \\
      FIRST_X_ASSUM MATCH_MP_TAC >> art [] >> METIS_TAC [],
      (* goal 2 (of 9) *)
      RW_TAC std_ss [DISJOINT_ALT, IN_CROSS] >> ASM_SET_TAC [],
      (* goal 3 (of 9) *)
      Cases_on `x` >> fs [] \\
      RW_TAC std_ss [DISJOINT_ALT, IN_CROSS] \\
      DISJ2_TAC \\
      Know `SND x NOTIN (B DIFF B')` >- ASM_SET_TAC [] \\
      Q.PAT_X_ASSUM `B DIFF B' = BIGUNION (IMAGE f2 (count n2))`
        (ONCE_REWRITE_TAC o wrap) \\
      rw [IN_BIGUNION_IMAGE, IN_COUNT] >> METIS_TAC [],
      (* goal 4 (of 9) *)
      RW_TAC std_ss [DISJOINT_ALT, IN_CROSS] >> ASM_SET_TAC [],
      (* goal 5 (of 9) *)
      MATCH_MP_TAC DISJOINT_CROSS_R \\
      FIRST_X_ASSUM MATCH_MP_TAC >> art [] >> METIS_TAC [],
      (* goal 6 (of 9) *)
      Cases_on `x` >> fs [] \\
      RW_TAC std_ss [DISJOINT_ALT, IN_CROSS] \\
      DISJ1_TAC \\
      Know `FST x NOTIN (A DIFF A')` >- ASM_SET_TAC [] \\
      Q.PAT_X_ASSUM `A DIFF A' = BIGUNION (IMAGE f1 (count n1))`
        (ONCE_REWRITE_TAC o wrap) \\
      rw [IN_BIGUNION_IMAGE, IN_COUNT] >> METIS_TAC [],
      (* goal 7 (of 9) *)
      Cases_on `x` >> fs [] \\
      RW_TAC std_ss [DISJOINT_ALT, IN_CROSS] \\
      DISJ2_TAC \\
      Suff `SND x IN B DIFF B'` >- ASM_SET_TAC [] \\
      Q.PAT_X_ASSUM `B DIFF B' = BIGUNION (IMAGE f2 (count n2))`
        (ONCE_REWRITE_TAC o wrap) \\
      rw [IN_BIGUNION_IMAGE, IN_COUNT] \\
      Q.EXISTS_TAC `r` >> art [],
      (* goal 8 (of 9) *)
      Cases_on `x` >> fs [] \\
      RW_TAC std_ss [DISJOINT_ALT, IN_CROSS] \\
      DISJ1_TAC \\
      Suff `FST x IN A DIFF A'` >- ASM_SET_TAC [] \\
      Q.PAT_X_ASSUM `A DIFF A' = BIGUNION (IMAGE f1 (count n1))`
        (ONCE_REWRITE_TAC o wrap) \\
      rw [IN_BIGUNION_IMAGE, IN_COUNT] \\
      Q.EXISTS_TAC `q` >> art [],
      (* goal 9 (of 9) *)
      Cases_on `x` >> Cases_on `x'` >> fs [] \\
      RW_TAC std_ss [DISJOINT_ALT, IN_CROSS] \\
      reverse (Cases_on `q = q'`)
      >- (DISJ1_TAC >> ASM_SET_TAC []) \\
      reverse (Cases_on `r = r'`)
      >- (DISJ2_TAC >> ASM_SET_TAC []) \\
      METIS_TAC [] ]
QED

(* a sigma_algebra is also a semiring *)
Theorem SEMIRING_PROD_SETS' :
    !a b. sigma_algebra a /\ sigma_algebra b ==>
          semiring ((space a CROSS space b),prod_sets (subsets a) (subsets b))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC SEMIRING_PROD_SETS
 >> CONJ_TAC
 >> MATCH_MP_TAC ALGEBRA_IMP_SEMIRING
 >> MATCH_MP_TAC SIGMA_ALGEBRA_ALGEBRA >> art []
QED

(***********************)
(*   Further Results   *)
(***********************)

(*  These do not require addition simplifier manipulations. It would
      probably be more appropriate to add these in the proper places above.
      - Jared Yeager                                                                   *)

Theorem SIGMA_ALGEBRA_SUBSET_SPACE:
    !a s. sigma_algebra a /\ s IN subsets a ==> s SUBSET space a
Proof
    rw[sigma_algebra_def,algebra_def,subset_class_def]
QED

Theorem SIGMA_ALGEBRA_PROD_SIGMA_WEAK:
    !a b. sigma_algebra a /\ sigma_algebra b ==> sigma_algebra (a CROSS b)
Proof
    rw[] >> irule SIGMA_ALGEBRA_PROD_SIGMA >> fs[sigma_algebra_def,algebra_def]
QED

Theorem IN_SPACE_PROD_SIGMA:
    !a b z. z IN space (a CROSS b) <=> FST z IN space a /\ SND z IN space b
Proof
    simp[prod_sigma_def,SPACE_SIGMA]
QED

Theorem MEASURABLE_FST:
    !a b. sigma_algebra a /\ sigma_algebra b ==> FST IN measurable (a CROSS b) a
Proof
    rw[]
 >> simp[IN_MEASURABLE,SIGMA_ALGEBRA_PROD_SIGMA_WEAK,FUNSET,IN_SPACE_PROD_SIGMA]
 >> rw[]
 >> ‘PREIMAGE FST s INTER space (a CROSS b) = s CROSS (space b)’
      by (simp[EXTENSION,IN_SPACE_PROD_SIGMA] \\
          rw[] >> eq_tac >> rw[] \\
          dxrule_all_then mp_tac SIGMA_ALGEBRA_SUBSET_SPACE >> simp[SUBSET_DEF])
 >> pop_assum SUBST1_TAC >> simp[prod_sigma_def] >> irule IN_SIGMA
 >> simp[prod_sets_def]
 >> qexistsl_tac [‘s’,‘space b’] >> simp[SIGMA_ALGEBRA_SPACE]
QED

Theorem MEASURABLE_SND:
    !a b. sigma_algebra a /\ sigma_algebra b ==> SND IN measurable (a CROSS b) b
Proof
    rw[]
 >> simp[IN_MEASURABLE,SIGMA_ALGEBRA_PROD_SIGMA_WEAK,FUNSET,IN_SPACE_PROD_SIGMA]
 >> rw[]
 >> ‘PREIMAGE SND s INTER space (a CROSS b) = (space a) CROSS s’
      by (simp[EXTENSION,IN_SPACE_PROD_SIGMA] \\
          rw[] >> eq_tac >> rw[] \\
          dxrule_all_then mp_tac SIGMA_ALGEBRA_SUBSET_SPACE >> simp[SUBSET_DEF])
 >> pop_assum SUBST1_TAC >> simp[prod_sigma_def] >> irule IN_SIGMA
 >> simp[prod_sets_def]
 >> qexistsl_tac [‘space a’,‘s’] >> simp[SIGMA_ALGEBRA_SPACE]
QED

Theorem IN_MEASURABLE_EQ:
    !a b f g. f IN measurable a b /\ (!x. x IN space a ==> g x = f x) ==>
              g IN measurable a b
Proof
    rw[measurable_def] >- fs[FUNSET] >> first_x_assum $ dxrule_then mp_tac >>
    `PREIMAGE g s INTER space a = PREIMAGE f s INTER space a` suffices_by simp[] >>
    rw[EXTENSION] >> Cases_on `x IN space a` >> fs[]
QED

Theorem IN_MEASURABLE_CONG:
    !a b c d f g. a = c /\ b = d /\ (!x. x IN space c ==> f x = g x) ==>
                 (f IN measurable a b <=> g IN measurable c d)
Proof
    rw[] >> eq_tac >> rw[]
 >> dxrule_at_then (Pos $ el 1) irule IN_MEASURABLE_EQ >> simp[]
QED

(* for use with irule, often not super useful in prectice due to need to address 'b *)
Theorem IN_MEASURABLE_COMP:
    !f g h a b c. f IN measurable a b /\ g IN measurable b c /\
                 (!x. x IN space a ==> h x = g (f x)) ==>
                  h IN measurable a c
Proof
    rw[] >> irule IN_MEASURABLE_EQ
 >> qexists_tac `g o f` >> simp[MEASURABLE_COMP,SF SFY_ss]
QED

(* NOTE: more antecendents are added due to changes in ‘measurable’ *)
Theorem IN_MEASURABLE_PROD_SIGMA:
    !a bx by fx fy f.
        sigma_algebra a /\
        subset_class (space bx) (subsets bx) /\
        subset_class (space by) (subsets by) /\
        fx IN measurable a bx /\ fy IN measurable a by /\
        (!z. z IN space a ==> f z = (fx z,fy z)) ==> f IN measurable a (bx CROSS by)
Proof
    rw[] >> irule IN_MEASURABLE_EQ >> qexists_tac `λz. (fx z,fy z)` >> simp[] >>
    irule MEASURABLE_PROD_SIGMA' >> simp[o_DEF,ETA_AX]
QED

(* NOTE: This version is inspired by HVG's "measurable_Pair". *)
Theorem MEASURABLE_PAIR :
    !a b1 b2 X Y.
       sigma_algebra a /\ sigma_algebra b1 /\ sigma_algebra b2 /\
       X IN measurable a b1 /\ Y IN measurable a b2 ==>
      (\x. (X x,Y x)) IN measurable a (b1 CROSS b2)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC IN_MEASURABLE_PROD_SIGMA
 >> qexistsl_tac [‘X’, ‘Y’] >> simp []
 >> fs [sigma_algebra_def, algebra_def]
QED

Theorem algebra_finite_subsets_imp_sigma_algebra :
    !a. algebra a /\ FINITE (subsets a) ==> sigma_algebra a
Proof
    rw [sigma_algebra_def]
 >> ‘FINITE c’ by PROVE_TAC [SUBSET_FINITE_I]
 >> MP_TAC (Q.ISPEC ‘c :('a set) set’ finite_decomposition_simple) >> rw []
 >> MATCH_MP_TAC ALGEBRA_FINITE_UNION >> art []
QED

Theorem algebra_finite_space_imp_sigma_algebra :
    !a. algebra a /\ FINITE (space a) ==> sigma_algebra a
Proof
    rw [sigma_algebra_def]
 >> Know ‘subsets a SUBSET (POW (space a))’
 >- (rw [Once SUBSET_DEF, IN_POW] \\
     fs [algebra_def, subset_class_def])
 >> DISCH_TAC
 >> ‘FINITE (POW (space a))’ by PROVE_TAC [FINITE_POW]
 >> ‘c SUBSET (POW (space a))’ by PROVE_TAC [SUBSET_TRANS]
 >> ‘FINITE c’ by PROVE_TAC [SUBSET_FINITE_I]
 >> MP_TAC (Q.ISPEC ‘c :('a set) set’ finite_decomposition_simple) >> rw []
 >> MATCH_MP_TAC ALGEBRA_FINITE_UNION >> art []
QED

(* NOTE: The trivial algebras below are also sigma-algebra by above lemmas *)
Theorem trivial_algebra_of_space :
    !sp. algebra (sp, {{}; sp})
Proof
    rw [algebra_def, subset_class_def]
 >> SET_TAC []
QED

Theorem trivial_algebra_of_two_sets :
    !sp s. s SUBSET sp ==> algebra (sp, {{}; s; sp DIFF s; sp})
Proof
    rw [algebra_def, subset_class_def]
 >> ASM_SET_TAC []
QED

(* NOTE: This is head (h) and tail (t) of one-time coin tossing *)
Theorem trivial_algebra_of_two_points :
    !h t. algebra ({h; t}, {{}; {h}; {t}; {h; t}})
Proof
    rw [algebra_def, subset_class_def]
 >> ASM_SET_TAC []
QED

val _ = export_theory ();

(* References:

  [1] Hurd, J.: Formal verification of probabilistic algorithms. University of
      Cambridge (2001).
  [2] Coble, A.R.: Anonymity, information, and machine-assisted proof.
      University of Cambridge (2010).
  [3] Mhamdi, T., Hasan, O., Tahar, S.: Formalization of Measure Theory and
      Lebesgue Integration for Probabilistic Analysis in HOL. ACM Trans.
      Embedded Comput. Syst. 12, 1--23 (2013).
  [4] Wikipedia: https://en.wikipedia.org/wiki/Ring_of_sets
  [5] Wikipedia: https://en.wikipedia.org/wiki/Eugene_Dynkin
  [6] Wikipedia: https://en.wikipedia.org/wiki/Dynkin_system
  [7] Schilling, R.L.: Measures, Integrals and Martingales (Second Edition).
      Cambridge University Press (2017).
  [8] Chung, K.L.: A Course in Probability Theory, Third Edition.
      Academic Press (2001).
  [9] Shiryaev, A.N.: Probability-1. Springer-Verlag New York (2016).

 *)
