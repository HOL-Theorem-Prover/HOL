open HolKernel Parse boolLib bossLib;

open binderLib
open relationTheory nomsetTheory termTheory chap2Theory

val _ = new_theory "horeduction";

Inductive compat_closure:
[~R:]
  !x y. R x y ==> compat_closure R x y
[~APPR:]
  !x y z. compat_closure R x y ==> compat_closure R (z @@ x) (z @@ y)
[~APPL:]
  !x y z. compat_closure R x y ==> compat_closure R (x @@ z) (y @@ z)
[~LAM:]
  !x y v. compat_closure R x y ==> compat_closure R (LAM v x) (LAM v y)
End

(* Barendregt definition 3.1.14 *)
Definition substitutive_def:
  substitutive R = !M M'. R M M' ==> !N v. R ([N/v]M) ([N/v]M')
End

Definition permutative_def:
  permutative R = !M M'. R M M' ==> !p. R (tpm p M) (tpm p M')
End

Theorem cc_gen_ind:
  !R fv. (!M N p. R M N ==> R (tpm p M) (tpm p N)) /\
         (!M N x. R M N ==> P M N x) /\
         (!M M' N x. (!y. P M M' y) ==> P (M @@ N) (M' @@ N) x) /\
         (!M N N' x. (!y. P N N' y) ==> P (M @@ N) (M @@ N') x) /\
         (!v M M' x. ~(v IN fv x) /\ (!y. P M M' y) ==>
                     P (LAM v M) (LAM v M') x) /\
         (!x. FINITE (fv x)) ==>
         !M N. compat_closure R M N ==> !x. P M N x
Proof
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!M N. compat_closure R M N ==>
                        !x p. P (tpm p M) (tpm p N) x`
        THEN1 METIS_TAC [pmact_nil] THEN
  HO_MATCH_MP_TAC compat_closure_ind THEN SRW_TAC [][] THEN
  Q_TAC (NEW_TAC "z") `fv x UNION {lswapstr p v} UNION FV (tpm p M) UNION
                       FV (tpm p N)` THEN
  `LAM (lswapstr p v) (tpm p M) = LAM z (tpm ([(z,lswapstr p v)] ++ p) M)`
     by SRW_TAC [][tpm_ALPHA, pmact_decompose] THEN
  `LAM (lswapstr p v) (tpm p N) = LAM z (tpm ([(z,lswapstr p v)] ++ p) N)`
     by SRW_TAC [][tpm_ALPHA, pmact_decompose] THEN
  SRW_TAC [][]
QED

Theorem cc_ind =
  (Q.GEN ‘P’ o Q.GEN ‘X’ o Q.GEN ‘R’ o
   Q.INST [‘P'’ |-> ‘P’] o
   SIMP_RULE (srw_ss()) [] o
   Q.INST [‘P’ |-> ‘\M N x. P' M N’, ‘fv’ |-> ‘\x. X’] o
   SPEC_ALL) cc_gen_ind

Theorem compat_closure_permutative:
  permutative R ==> permutative (compat_closure R)
Proof
  STRIP_TAC THEN ASM_SIMP_TAC (srw_ss()) [permutative_def] THEN
  HO_MATCH_MP_TAC compat_closure_ind THEN SRW_TAC [][] THEN
  METIS_TAC [permutative_def, compat_closure_rules]
QED

Theorem permutative_compat_closure_eqn[simp]:
  permutative R ==>
  compat_closure R (tpm p M) (tpm p N) = compat_closure R M N
Proof
  STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    `permutative (compat_closure R)`
       by METIS_TAC [compat_closure_permutative] THEN
    `compat_closure R (tpm (REVERSE p) (tpm p M))
                      (tpm (REVERSE p) (tpm p N))`
       by METIS_TAC [permutative_def] THEN
    FULL_SIMP_TAC (srw_ss()) [],
    METIS_TAC [permutative_def, compat_closure_permutative]
  ]
QED

Definition compatible_def:
  compatible R = !x y c. R x y /\ one_hole_context c ==>
                         R (c x) (c y)
End

Definition congruence_def:
  congruence R <=> equivalence R /\ compatible R
End

Definition is_reduction_def:
  is_reduction R <=> compatible R /\ transitive R /\ reflexive R
End

Theorem substitutive_implies_permutative:
  substitutive R ==> permutative R
Proof
  SRW_TAC [][substitutive_def, permutative_def] THEN
  Induct_on `p` THEN SRW_TAC [][] THEN
  `?x y. h = (x,y)` by METIS_TAC [pairTheory.pair_CASES] THEN
  SRW_TAC [][] THEN
  Q_TAC (NEW_TAC "z") `{x; y} UNION FV (tpm p M) UNION FV (tpm p M')` THEN
  `(tpm ((x,y)::p) M = [VAR y/z] ([VAR x/y] ([VAR z/x] (tpm p M)))) /\
   (tpm ((x,y)::p) M'= [VAR y/z] ([VAR x/y] ([VAR z/x] (tpm p M'))))`
      by (ONCE_REWRITE_TAC [tpm_CONS] THEN
          SRW_TAC [][swap_eq_3substs]) THEN
  ASM_SIMP_TAC (srw_ss()) []
QED

Theorem compat_closure_substitutive:
  substitutive R ==> substitutive (compat_closure R)
Proof
  STRIP_TAC THEN SIMP_TAC (srw_ss()) [substitutive_def] THEN
  REPEAT STRIP_TAC THEN
  Q.UNDISCH_THEN `compat_closure R M M'` MP_TAC THEN
  MAP_EVERY Q.ID_SPEC_TAC [`M'`, `M`] THEN
  HO_MATCH_MP_TAC cc_ind THEN Q.EXISTS_TAC `v INSERT FV N` THEN
  SRW_TAC [][SUB_THM] THENL [
    PROVE_TAC [substitutive_implies_permutative, permutative_def],
    PROVE_TAC [compat_closure_rules, substitutive_def],
    SRW_TAC [][compat_closure_rules],
    SRW_TAC [][compat_closure_rules],
    SRW_TAC [][compat_closure_rules]
  ]
QED

Overload equiv_closure = ``relation$EQC``
Overload EQC = ``relation$EQC`` (* prefer older, existing name *)
Theorem equiv_closure_rules = LIST_CONJ [EQC_R, EQC_REFL, EQC_SYM, EQC_TRANS]
Theorem equiv_closure_ind = EQC_INDUCTION

Theorem equiv_closure_substitutive:
  substitutive R ==> substitutive (equiv_closure R)
Proof
  STRIP_TAC THEN SIMP_TAC (srw_ss()) [substitutive_def] THEN
  HO_MATCH_MP_TAC equiv_closure_ind THEN SRW_TAC [][] THEN
  METIS_TAC [substitutive_def, equiv_closure_rules]
QED

Overload conversion = “λR. equiv_closure (compat_closure R)”

Theorem conversion_substitutive:
  substitutive R ==> substitutive (conversion R)
Proof
  METIS_TAC [compat_closure_substitutive, equiv_closure_substitutive]
QED

Theorem RTC_substitutive:
  substitutive R ==> substitutive (RTC R)
Proof
  STRIP_TAC THEN SIMP_TAC (srw_ss()) [substitutive_def] THEN
  HO_MATCH_MP_TAC RTC_INDUCT THEN
  METIS_TAC [RTC_RULES, substitutive_def]
QED

Overload reduction = “λR. RTC (compat_closure R)”

Theorem reduction_substitutive:
  substitutive R ==> substitutive (reduction R)
Proof
  METIS_TAC [compat_closure_substitutive, RTC_substitutive]
QED

Theorem conversion_rules:
  !R. (!x. conversion R x x) /\
      (!x y. conversion R x y ==> conversion R y x) /\
      (!x y z. conversion R x y /\ conversion R y z ==> conversion R x z) /\
      (!x y. R x y ==> conversion R x y) /\
      (!x y. reduction R x y ==> conversion R x y) /\
      (!x y. compat_closure R x y ==> conversion R x y)
Proof
  SRW_TAC [][equiv_closure_rules] THENL [
    PROVE_TAC [equiv_closure_rules],
    PROVE_TAC [equiv_closure_rules, compat_closure_rules],
    POP_ASSUM MP_TAC THEN SIMP_TAC (srw_ss()) [] THEN
    MAP_EVERY Q.ID_SPEC_TAC [`y`,`x`] THEN
    HO_MATCH_MP_TAC RTC_INDUCT THEN
    PROVE_TAC [equiv_closure_rules]
  ]
QED

(* |- !R x y z. conversion R x y /\ conversion R y z ==> conversion R x z *)
Theorem conversion_TRANS = cj 3 conversion_rules

Theorem compat_closure_compatible:
  !R. compatible (compat_closure R)
Proof
  GEN_TAC THEN
  Q_TAC SUFF_TAC `!c. one_hole_context c ==>
                      !x y. compat_closure R x y ==>
                            compat_closure R (c x) (c y)` THEN1
     SRW_TAC [][compatible_def] THEN
  HO_MATCH_MP_TAC one_hole_context_ind THEN SRW_TAC [][] THEN
  PROVE_TAC [compat_closure_rules]
QED

val reduction_compatible = store_thm(
  "reduction_compatible",
  ``!R. compatible (reduction R)``,
  GEN_TAC THEN
  Q_TAC SUFF_TAC `!x y. RTC (compat_closure R) x y ==>
                        !c. one_hole_context c ==>
                            RTC (compat_closure R) (c x) (c y)` THEN1
    SRW_TAC [][compatible_def] THEN
  HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [][] THEN
  PROVE_TAC [compatible_def, compat_closure_compatible,
             RTC_RULES]);

val reduction_rules = store_thm(
  "reduction_rules",
  ``(!x. reduction R x x) /\
    (!x y. R x y ==> reduction R x y) /\
    (!x y. compat_closure R x y ==> reduction R x y) /\
    (!x y z. reduction R x y /\ reduction R y z ==>
             reduction R x z) /\
    (!x y z. reduction R x y ==> reduction R (z @@ x) (z @@ y)) /\
    (!x y z. reduction R x y ==> reduction R (x @@ z) (y @@ z)) /\
    (!x y v. reduction R x y ==> reduction R (LAM v x) (LAM v y))``,
  REPEAT STRIP_TAC THENL [
    PROVE_TAC [RTC_RULES],
    PROVE_TAC [RTC_RULES, compat_closure_rules],
    PROVE_TAC [RTC_RULES],
    PROVE_TAC [RTC_RTC],
    PROVE_TAC [leftctxt, compatible_def, reduction_compatible],
    PROVE_TAC [rightctxt_thm, rightctxt, compatible_def, reduction_compatible],
    PROVE_TAC [absctxt, compatible_def, reduction_compatible]
  ]);

val conversion_compatible = store_thm(
  "conversion_compatible",
  ``!R. compatible (conversion R)``,
  GEN_TAC THEN
  Q_TAC SUFF_TAC `!x y. equiv_closure (compat_closure R) x y ==>
                        !c. one_hole_context c ==>
                            equiv_closure (compat_closure R) (c x) (c y)` THEN1
    SRW_TAC [][compatible_def] THEN
  HO_MATCH_MP_TAC equiv_closure_ind THEN SRW_TAC [][] THEN
  PROVE_TAC [compatible_def, equiv_closure_rules, compat_closure_compatible]);

Theorem conversion_monotone :
    !r1 r2. r1 RSUBSET r2 ==> (conversion r1) RSUBSET (conversion r2)
Proof
    rpt STRIP_TAC
 >> simp [relationTheory.RSUBSET]
 >> HO_MATCH_MP_TAC relationTheory.EQC_INDUCTION
 >> reverse (rw [conversion_rules])
 >- (MATCH_MP_TAC EQC_TRANS \\
     rename1 ‘conversion r2 z y’ \\
     Q.EXISTS_TAC ‘z’ >> ASM_REWRITE_TAC [])
 >> POP_ASSUM MP_TAC
 >> Q.ID_SPEC_TAC ‘y’
 >> Q.ID_SPEC_TAC ‘x’
 >> HO_MATCH_MP_TAC compat_closure_ind
 >> RW_TAC std_ss []
 >| [ (* goal 1 (of 4) *)
      Q_TAC SUFF_TAC ‘r2 x y’ >- rw [conversion_rules] \\
      Q.PAT_X_ASSUM ‘r1 RSUBSET r2’ MP_TAC \\
      rw [relationTheory.RSUBSET],
      (* goal 2 (of 4) *)
      PROVE_TAC [conversion_compatible, compatible_def, leftctxt],
      (* goal 3 (of 4) *)
      PROVE_TAC [conversion_compatible, compatible_def, rightctxt, rightctxt_thm],
      (* goal 7 (of 7) *)
      PROVE_TAC [conversion_compatible, compatible_def, absctxt] ]
QED

(* "Follows from an induction on the structure of M, and the
    compatibility of reduction R" *)
val lemma3_8 = store_thm(
  "lemma3_8",
  ``!M. reduction R N N' ==> reduction R ([N/x] M) ([N'/x] M)``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN
  Q.EXISTS_TAC `x INSERT FV N UNION FV N'` THEN
  SRW_TAC [][SUB_THM, SUB_VAR] THEN PROVE_TAC [reduction_rules]);

val redex_def = Define`redex (R:'a -> 'a -> bool) t = ?u. R t u`;

val (can_reduce_rules, can_reduce_ind, can_reduce_cases) =
  Hol_reln`(!t. redex R t ==> can_reduce R t) /\
           (!M N. can_reduce R M ==> can_reduce R (M @@ N)) /\
           (!M N. can_reduce R M ==> can_reduce R (N @@ M)) /\
           (!v M. can_reduce R M ==> can_reduce R (LAM v M))`

val can_reduce_reduces = store_thm(
  "can_reduce_reduces",
  ``!R t. can_reduce R t ==> ?u. compat_closure R t u``,
  GEN_TAC THEN HO_MATCH_MP_TAC can_reduce_ind THEN SRW_TAC [][redex_def] THEN
  PROVE_TAC [compat_closure_rules]);

val normal_form_def = Define`normal_form R t = ~can_reduce R t`;

val _ = export_theory();
