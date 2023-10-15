open HolKernel Parse boolLib bossLib BasicProvers;

open metisLib boolSimps relationTheory listTheory llistTheory pathTheory
     pred_setTheory finite_mapTheory hurdUtils;

open nomsetTheory binderLib
open finite_developmentsTheory
open labelledTermsTheory
open termTheory chap2Theory chap3Theory appFOLDLTheory
open term_posnsTheory
open chap11_1Theory
open head_reductionTheory

local open containerTheory in end

val _ = new_theory "standardisation"
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]


structure NewQ = Q
structure Q = struct open Q open OldAbbrevTactics end

val _ = ParseExtras.temp_loose_equality()


val RUNION_def = relationTheory.RUNION
val ADD1 = arithmeticTheory.ADD1

(* Section 11.4 of Barendregt *)

val standard_reduction_def = Define`
  standard_reduction s =
    okpath (labelled_redn beta) s /\
    !i j. j < i /\ (i + 1) IN PL s ==>
          !p. p < nth_label j s ==>
              ~(nth_label i s IN residuals (seg j i s) {p})
`;

val better_standard_reduction = store_thm(
  "better_standard_reduction",
  ``standard_reduction s =
       okpath (labelled_redn beta) s /\
       !i j. j < i /\ i + 1 IN PL s ==>
             !p. p IN redex_posns (el j s) /\ p < nth_label j s ==>
                 ~(nth_label i s IN residuals (seg j i s) {p})``,
  SRW_TAC [][standard_reduction_def] THEN EQ_TAC THEN SRW_TAC [][] THEN
  Cases_on `p IN redex_posns (el j s)` THENL [
    METIS_TAC [],
    `i IN PL s` by METIS_TAC [PL_downward_closed, DECIDE ``i < i + 1``] THEN
    `okpath (labelled_redn beta) (seg j i s)`
       by SRW_TAC [numSimps.ARITH_ss][okpath_seg] THEN
    `first (seg j i s) = el j s` by SRW_TAC [numSimps.ARITH_ss][first_seg] THEN
    `{p} INTER redex_posns (el j s) = {}` by SRW_TAC [][EXTENSION] THEN
    `finite (seg j i s)` by SRW_TAC [numSimps.ARITH_ss][] THEN
    `residuals (seg j i s) {p} = {}`
        by METIS_TAC [residuals_can_ignore, residuals_EMPTY] THEN
    SRW_TAC [][]
  ]);

val _ = add_infix("is_internal_redex", 760, NONASSOC)
(* definition 11.4.2 (i) *)
val is_internal_redex_def = Define`
  p is_internal_redex t = ~(p is_head_redex t) /\ p IN redex_posns t
`;

Theorem NIL_never_internal_redex[simp] :
    !t. ~([] is_internal_redex t)
Proof
  GEN_TAC THEN
  Q.SPEC_THEN `t` STRUCT_CASES_TAC term_CASES THEN
  SRW_TAC [][is_internal_redex_def, is_head_redex_thm, redex_posns_thm]
QED

val _ = add_infix("i_reduces", 760, NONASSOC)
(* definition 11.4.2 (ii) *)
val i_reduces_def = Define`
  M i_reduces N = ?s. okpath (labelled_redn beta) s /\ (first s = M) /\
                      finite s /\ (last s = N) /\
                      !i. i + 1 IN PL s ==>
                          (nth_label i s) is_internal_redex (el i s)
`;

(* single step version of the same *)
val _ = add_infix("i_reduce1", 760, NONASSOC)
val i_reduce1_def = Define`
  M i_reduce1 N = ?r. labelled_redn beta M r N /\ r is_internal_redex M
`;

val i_reduces_RTC_i_reduce1 = store_thm(
  "i_reduces_RTC_i_reduce1",
  ``(i_reduces) = RTC (i_reduce1)``,
  SIMP_TAC (srw_ss()) [FUN_EQ_THM, EQ_IMP_THM, i_reduces_def, i_reduce1_def,
                       FORALL_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
  CONJ_TAC THENL [
    Q_TAC SUFF_TAC
          `!s. okpath (labelled_redn beta) s /\ finite s ==>
               (!i. i + 1 IN PL s ==>
                    nth_label i s is_internal_redex el i s) ==>
               RTC (i_reduce1) (first s) (last s)` THEN1 PROVE_TAC [] THEN
    HO_MATCH_MP_TAC pathTheory.finite_okpath_ind THEN
    SIMP_TAC (srw_ss())
             [relationTheory.RTC_RULES, GSYM ADD1] THEN
    MAP_EVERY Q.X_GEN_TAC [`x`,`r`,`p`] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (CONJUNCT2 (SPEC_ALL relationTheory.RTC_RULES)) THEN
    Q.EXISTS_TAC `first p` THEN
    POP_ASSUM (fn th =>
                  MAP_EVERY (MP_TAC o GEN_ALL o C SPEC th)
                            [``0``, ``SUC i``]) THEN
    SRW_TAC [][i_reduce1_def] THEN PROVE_TAC [],

    HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
    SRW_TAC [][i_reduce1_def] THENL [
      Q.EXISTS_TAC `stopped_at x` THEN SRW_TAC [][],
      Q.EXISTS_TAC `pcons x r s` THEN
      SRW_TAC [][GSYM ADD1] THEN
      Cases_on `i` THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [ADD1]
    ]
  ]);


val _ = add_infix("i1_reduces", 760, NONASSOC)
(* definition 11.4.3 (iii) *)
val i1_reduces_def = Define`
  M i1_reduces N = ?s. okpath (labelled_redn beta) s /\ (first s = M) /\
                       finite s /\ (last s = N) /\
                       (!i. i + 1 IN PL s ==>
                            (nth_label i s) is_internal_redex (el i s)) /\
                       ?FS. s IN complete_development M FS
`;

(* NOTE: the antecedent ‘delta is_internal_redex M’ is unnecessary *)
val lemma11_4_3i = store_thm(
  "lemma11_4_3i",
  ``!M delta N.
        labelled_redn beta M delta N /\ delta is_internal_redex M ==>
        ((?p. p is_head_redex N) ==> (?p. p is_head_redex M))``,
  METIS_TAC [labelled_redn_cc, hnf_no_head_redex, hnf_ccbeta_preserved]);

val residual1_equal_singletons = store_thm(
  "residual1_equal_singletons",
  ``!M N pos. labelled_redn beta M pos N ==> (residual1 M pos N {pos} = {})``,
  SRW_TAC [][residual1_def] THEN
  Q.ABBREV_TAC `M' = nlabel 0 M {pos}` THEN
  `lrcc (beta0 RUNION beta1) M' pos (lift_redn M' pos N) /\
   (N = strip_label (lift_redn M' pos N))`
      by PROVE_TAC [strip_label_nlabel, lift_redn_def] THEN
  Q.ABBREV_TAC `N' = lift_redn M' pos N` THEN
  `pos IN redex_posns M`
      by PROVE_TAC [IN_term_IN_redex_posns, is_redex_occurrence_def] THEN
  `pos IN n_posns 0 M'` by SRW_TAC [][n_posns_nlabel] THEN
  IMP_RES_TAC pick_a_beta THENL [
    PROVE_TAC [beta0_reduce_at_single_label],
    PROVE_TAC []
  ])

val nlabel_eq = store_thm(
  "nlabel_eq",
  ``!t. ((VAR s = nlabel n t ps) = (t = VAR s)) /\
        ((M' @@ N' = nlabel n t ps) =
            ?M N. (t = M @@ N) /\ (~is_abs M \/ ~([] IN ps)) /\
                  (M' = nlabel n M { p | Lt::p IN ps}) /\
                  (N' = nlabel n N { p | Rt::p IN ps})) /\
        ((LAM v M' = nlabel n t ps) =
            ?M. (t = LAM v M) /\ (M' = nlabel n M {p| In::p IN ps})) /\
        ((LAMi m v M' N' = nlabel n t ps) =
            ?M N. (t = LAM v M @@ N) /\ [] IN ps /\ (m = n) /\
                  (M' = nlabel n M { p | Lt::In::p IN ps}) /\
                  (N' = nlabel n N { p | Rt::p IN ps}))``,
  GEN_TAC THEN
  Q.SPEC_THEN `t` STRUCT_CASES_TAC term_CASES THEN
  SRW_TAC [][nlabel_thm] THENL [
    PROVE_TAC [],
    Q.SPEC_THEN `t1` STRUCT_CASES_TAC term_CASES THEN
    SRW_TAC [][nlabel_thm],
    Q.SPEC_THEN `t1` STRUCT_CASES_TAC term_CASES THEN
    SRW_TAC [][nlabel_thm],
    Q.SPEC_THEN `t1` STRUCT_CASES_TAC term_CASES THEN
    SRW_TAC [][nlabel_thm],
    Q.SPEC_THEN `t1` STRUCT_CASES_TAC term_CASES THEN
    SRW_TAC [][nlabel_thm] THEN
    SRW_TAC [][lLAMi_eq_thm, lLAM_eq_thm, EQ_IMP_THM, LAM_eq_thm] THENL [
      SRW_TAC [][tpm_eqr, nlabel_def, pmact_flip_args],
      SRW_TAC [][nlabel_def, pmact_flip_args]
    ],
    SRW_TAC [][LAM_eq_thm, lLAM_eq_thm, EQ_IMP_THM] THENL [
      SRW_TAC [][tpm_eqr, nlabel_def, pmact_flip_args],
      SRW_TAC [][nlabel_def, pmact_flip_args]
    ]
  ]);

val IMAGE_EQ_SING = prove(
  ``!f s x. (!x y. (f x = f y) = (x = y)) ==>
            ((IMAGE f s = {f x}) = (s = {x}))``,
  REPEAT STRIP_TAC THEN SRW_TAC [][EXTENSION, EQ_IMP_THM] THEN
  PROVE_TAC []);

val _ = augment_srw_ss [rewrites [IMAGE_EQ_SING]]



val residual1_different_singletons = store_thm(
  "residual1_different_singletons",
  ``!M N p1 p2.
        labelled_redn beta M p1 N /\ p2 IN redex_posns M /\ p2 < p1 ==>
        (residual1 M p1 N {p2} = {p2})``,
  SRW_TAC [][residual1_def] THEN
  Q.ABBREV_TAC `M' = nlabel 0 M {p2}` THEN
  Q.ABBREV_TAC `N' = lift_redn M' p1 N` THEN
  `lrcc (beta0 RUNION beta1) M' p1 N' /\ (N = strip_label N')` by
     METIS_TAC [lift_redn_def, strip_label_nlabel] THEN
  Q_TAC SUFF_TAC
        `!M' p1 N'. lrcc (beta0 RUNION beta1) M' p1 N' ==>
                    !p2 M. (M' = nlabel 0 M {p2}) /\ p2 < p1 /\
                           p2 IN redex_posns M ==>
                           (n_posns 0 N' = {p2})` THEN1 METIS_TAC [] THEN
  POP_ASSUM_LIST (K ALL_TAC) THEN
  HO_MATCH_MP_TAC strong_lrcc_ind THEN
  SRW_TAC [][n_posns_def, nlabel_eq] THENL [
    FULL_SIMP_TAC (srw_ss()) [n_posns_nlabel, redex_posns_thm] THEN
    FULL_SIMP_TAC (srw_ss() ++ COND_elim_ss) [] THEN PROVE_TAC [],

    FULL_SIMP_TAC (srw_ss()) [n_posns_nlabel, redex_posns_thm] THEN
    FULL_SIMP_TAC (srw_ss() ++ COND_elim_ss) [] THEN
    SRW_TAC [][] THEN TRY (RES_TAC THEN NO_TAC) THEN PROVE_TAC [],

    FULL_SIMP_TAC (srw_ss()) [n_posns_nlabel, redex_posns_thm] THEN
    FULL_SIMP_TAC (srw_ss() ++ COND_elim_ss) [] THENL [
      `n_posns 0 (nlabel 0 N {}) = {}` by SRW_TAC [][n_posns_nlabel] THEN
      `n_posns 0 N' = {}` by PROVE_TAC [lrcc_new_labels] THEN
      SRW_TAC [][EXTENSION],
      PROVE_TAC []
    ],

    FULL_SIMP_TAC (srw_ss()) [n_posns_nlabel, redex_posns_thm] THEN
    FULL_SIMP_TAC (srw_ss() ++ COND_elim_ss) [] THEN
    SRW_TAC [][] THEN TRY (RES_TAC THEN NO_TAC) THENL [
      `n_posns 0 (nlabel 0 N {}) = {}` by SRW_TAC [][n_posns_nlabel] THEN
      `n_posns 0 N' = {}` by PROVE_TAC [lrcc_new_labels] THEN
      SRW_TAC [][EXTENSION],
      PROVE_TAC []
    ],

    FULL_SIMP_TAC (srw_ss()) [n_posns_nlabel, redex_posns_thm] THEN
    FULL_SIMP_TAC (srw_ss() ++ COND_elim_ss) [] THEN PROVE_TAC [],

    FULL_SIMP_TAC (srw_ss()) [n_posns_nlabel, redex_posns_thm] THEN
    `n_posns 0 (nlabel 0 N {}) = {}` by SRW_TAC [][n_posns_nlabel] THEN
    `n_posns 0 N' = {}` by PROVE_TAC [lrcc_new_labels] THEN
    SRW_TAC [][EXTENSION],

    FULL_SIMP_TAC (srw_ss()) [n_posns_nlabel, redex_posns_thm] THEN
    `n_posns 0 (nlabel 0 M'' {}) = {}` by SRW_TAC [][n_posns_nlabel] THEN
    `n_posns 0 N' = {}` by PROVE_TAC [lrcc_new_labels] THEN
    SRW_TAC [][EXTENSION]
  ]);

val lr_beta_preserves_lefter_redexes = store_thm(
  "lr_beta_preserves_lefter_redexes",
  ``!x y r r0. r0 IN redex_posns x /\ r0 < r /\
               labelled_redn beta x r y ==> (r0 IN redex_posns y)``,
  REPEAT STRIP_TAC THEN
  `residual1 x r y {r0} = {r0}`
     by SRW_TAC [][residual1_different_singletons] THEN
  `r0 IN redex_posns y`
     by (Q_TAC SUFF_TAC `{r0} SUBSET redex_posns y` THEN1
         SRW_TAC [][] THEN METIS_TAC [residual1_SUBSET]));

val residuals_different_singletons = store_thm(
  "residuals_different_singletons",
  ``!p. okpath (labelled_redn beta) p /\ finite p ==>
        !r. r IN redex_posns (first p) /\
            (!n. SUC n IN PL p ==> r < nth_label n p) ==>
            (residuals p {r} = {r})``,
  HO_MATCH_MP_TAC finite_okpath_ind THEN
  SRW_TAC [][residuals_stopped_at, residuals_pcons] THENL [
    SRW_TAC [][EXTENSION] THEN METIS_TAC [],
    FIRST_X_ASSUM
      (fn th => Q.SPEC_THEN `0` MP_TAC th THEN
                Q.SPEC_THEN `SUC n` (ASSUME_TAC o SIMP_RULE (srw_ss()) [] o
                                     Q.GEN `n`) th) THEN
    SRW_TAC [][residual1_different_singletons] THEN
    METIS_TAC [lr_beta_preserves_lefter_redexes]
  ]);

val standard_coind = store_thm(
  "standard_coind",
  ``∀Q. (∀x r p. Q (pcons x r p) ⇒
                  labelled_redn beta x r (first p) ∧
                  (∀n r₀. r₀ ∈ redex_posns x ∧ r₀ < r ∧ n + 1 ∈ PL p ⇒
                          r₀ < nth_label n p) ∧
                  Q p)
       ⇒
         ∀p. Q p ⇒ standard_reduction p``,
  SRW_TAC [][] THEN
  `okpath (labelled_redn beta) p`
     by (Q.UNDISCH_THEN `Q p` MP_TAC THEN Q.ID_SPEC_TAC `p` THEN
         HO_MATCH_MP_TAC okpath_co_ind THEN METIS_TAC []) THEN
  SRW_TAC [][better_standard_reduction] THEN
  `∀n pth. Q pth ∧ n ∈ PL pth ⇒ Q (drop n pth)`
     by (Induct THEN SRW_TAC [][] THEN
         Q.ISPEC_THEN `pth` FULL_STRUCT_CASES_TAC path_cases THEN
         FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []) THEN
  `j < i + 1` by DECIDE_TAC THEN
  `j ∈ PL p` by METIS_TAC [PL_downward_closed] THEN
  `okpath (labelled_redn beta) (drop j p)`
    by METIS_TAC [okpath_drop] THEN
  `Q (drop j p)` by METIS_TAC [] THEN
  SRW_TAC [][seg_def] THEN
  `el j p = first (drop j p)` by SRW_TAC [][first_drop] THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  `nth_label j p = first_label (drop j p)`
     by SRW_TAC [][first_label_drop] THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  `nth_label i p = nth_label (i - j) (drop j p)`
     by SRW_TAC [ARITH_ss]
                [nth_label_drop, ADD1] THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  qabbrev_tac `pp = drop j p` THEN
  qabbrev_tac `ii = i - j`  THEN
  `ii + 1 ∈ PL pp` by SRW_TAC [ARITH_ss][IN_PL_drop, Abbr`ii`, Abbr`pp`] THEN
  `∀n. n + 1 ∈ PL pp ⇒ p' < nth_label n pp`
     by (Q.ISPEC_THEN `pp` FULL_STRUCT_CASES_TAC path_cases THEN
         FULL_SIMP_TAC (srw_ss()) [ADD1] THEN Cases THEN SRW_TAC [][] THEN
         SRW_TAC [][] THEN METIS_TAC [ADD1]) THEN
  `ii ∈ PL pp` by METIS_TAC [PL_downward_closed, DECIDE ``x < x + 1``] THEN
  `residuals (take ii pp) {p'} = {p'}`
     by (MATCH_MP_TAC (SIMP_RULE (srw_ss() ++ DNF_ss) [AND_IMP_INTRO]
                                 residuals_different_singletons) THEN
         SRW_TAC [ARITH_ss][okpath_take,nth_label_take,ADD1] THEN
         `n + 1 ∈ PL pp` by METIS_TAC [PL_downward_closed,
                                       arithmeticTheory.LESS_OR_EQ] THEN
         SRW_TAC [][]) THEN
  SRW_TAC [][] THEN
  METIS_TAC [posn_lt_irrefl]);

val cant_create_redexes_to_left1 = store_thm(
  "cant_create_redexes_to_left1",
  ``!x r y. labelled_redn beta x r y ==>
            !r0 r1. r1 IN redex_posns x /\ r0 IN redex_posns y /\
                    r1 < r /\ r0 < r1 ==> r0 IN redex_posns x``,
  HO_MATCH_MP_TAC strong_labelled_redn_ind THEN
  SRW_TAC [][redex_posns_thm] THEN
  FULL_SIMP_TAC (srw_ss()) [posn_lt_def] THEN TRY (PROVE_TAC []) THEN
  RULE_ASSUM_TAC (ONCE_REWRITE_RULE [labelled_redn_cases]) THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN REPEAT VAR_EQ_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [is_abs_thm, posn_lt_nil]);

val cant_create_redexes_to_left = store_thm(
  "cant_create_redexes_to_left",
  ``!p. okpath (labelled_redn beta) p /\ finite p ==>
        !r. r IN redex_posns (first p) /\
            (!n. SUC n IN PL p ==> r < nth_label n p) ==>
            !r' M. labelled_redn beta (last p) r' M /\ r' < r ==>
                   r' IN redex_posns (first p)``,
  HO_MATCH_MP_TAC finite_okpath_ind THEN SRW_TAC [][] THENL [
    METIS_TAC [labelled_redn_beta_redex_posn],
    FIRST_X_ASSUM
      (fn th => Q.SPEC_THEN `0` MP_TAC th THEN
                Q.SPEC_THEN `SUC n` (ASSUME_TAC o SIMP_RULE (srw_ss()) [] o
                                     Q.GEN `n`) th) THEN
    SRW_TAC [][] THEN
    `r' IN redex_posns (first p)`
      by METIS_TAC [lr_beta_preserves_lefter_redexes] THEN
    `r'' IN redex_posns (first p)` by METIS_TAC [] THEN
    `r'' < r` by METIS_TAC [posn_lt_trans] THEN
    METIS_TAC [cant_create_redexes_to_left1]
  ]);

val lemma11_4_3ii = store_thm(
  "lemma11_4_3ii",
  ``!M delta N.
       labelled_redn beta M delta N /\ delta is_internal_redex M ==>
       (!delta_h. delta_h is_head_redex M ==>
                  ?p. (residual1 M delta N {delta_h} = {p}) /\
                      p is_head_redex N)``,
  REPEAT STRIP_TAC THEN
  `~(delta = delta_h) /\ delta IN redex_posns M`
       by PROVE_TAC [is_internal_redex_def] THEN
  `delta_h < delta` by PROVE_TAC [head_redex_leftmost] THEN
  `delta_h IN redex_posns M` by PROVE_TAC [head_redex_is_redex] THEN
  PROVE_TAC [residual1_different_singletons, head_redex_preserved]);

val nil_posn_le = store_thm(
  "nil_posn_le",
  ``!p : posn. ([] = p) \/ [] < p``,
  Induct THEN SRW_TAC [][]);

val lrcc_new_labels' = prove(
  ``~(lrcc (beta0 RUNION beta1) (nlabel 0 x {}) r y /\ p IN n_posns 0 y)``,
  PROVE_TAC [NOT_IN_EMPTY, n_posns_nlabel, INTER_EMPTY, lrcc_new_labels]);

val residuals_to_right_of_reduction = store_thm(
  "residuals_to_right_of_reduction",
  ``!M p1 N. labelled_redn beta M p1 N ==>
             !p2. p2 IN redex_posns M /\ p1 < p2 ==>
                  !p. p IN residual1 M p1 N {p2} ==> (p1 = p) \/ (p1 < p)``,
  SRW_TAC [][residual1_def] THEN
  Q.ABBREV_TAC `M' = nlabel 0 M {p2}` THEN
  Q.ABBREV_TAC `N' = lift_redn M' p1 N` THEN
  `lrcc (beta0 RUNION beta1) M' p1 N' /\ (N = strip_label N')`
      by METIS_TAC [lift_redn_def, strip_label_nlabel] THEN
  Q_TAC SUFF_TAC
        `!M' p1 N'. lrcc (beta0 RUNION beta1) M' p1 N' ==>
                    !p2 M. p1 < p2 /\ p2 IN redex_posns M /\
                           (M' = nlabel 0 M {p2}) ==>
                           !p. p IN n_posns 0 N' ==>
                               (p1 = p) \/ p1 < p` THEN1 METIS_TAC [] THEN
  POP_ASSUM_LIST (K ALL_TAC) THEN
  HO_MATCH_MP_TAC strong_lrcc_ind THEN
  SRW_TAC [][beta0_def, beta1_def, RUNION_def, nlabel_eq, n_posns_def,
             n_posns_nlabel, nil_posn_le] THEN
  FULL_SIMP_TAC (srw_ss()) [redex_posns_thm] THEN
  FULL_SIMP_TAC (srw_ss() ++ COND_elim_ss) [] THENL [
    PROVE_TAC [],
    PROVE_TAC [lrcc_new_labels'],
    PROVE_TAC [],
    PROVE_TAC [lrcc_new_labels'],
    PROVE_TAC [],
    FULL_SIMP_TAC (srw_ss()) [n_posns_nlabel] THEN SRW_TAC [][],
    PROVE_TAC [],
    FULL_SIMP_TAC (srw_ss()) [n_posns_nlabel] THEN SRW_TAC [][],
    FULL_SIMP_TAC (srw_ss()) [n_posns_nlabel] THEN SRW_TAC [][],
    PROVE_TAC [],
    PROVE_TAC [],
    PROVE_TAC []
  ]);


val lemma11_4_3iii = store_thm(
  "lemma11_4_3iii",
  ``!M delta N.
       labelled_redn beta M delta N /\ delta is_internal_redex M ==>
       !delta_i. delta_i is_internal_redex M ==>
                 !p. p IN residual1 M delta N {delta_i} ==>
                     p is_internal_redex N``,
  SRW_TAC [][] THEN
  `delta IN valid_posns M /\ delta_i IN valid_posns M`
      by PROVE_TAC [is_internal_redex_def, redex_posns_are_valid] THEN
  Q.SPECL_THEN [`M`, `delta`, `delta_i`]
               MP_TAC all_valid_posns_comparable THEN
  SRW_TAC [][] THENL [
    `delta_i IN redex_posns M` by PROVE_TAC [is_internal_redex_def] THEN
    `p IN redex_posns N` by PROVE_TAC [residual1_SUBSET, SUBSET_DEF] THEN
    Cases_on `?h. h is_head_redex N` THENL [
      POP_ASSUM STRIP_ASSUME_TAC THEN
      Q_TAC SUFF_TAC `~(p = h)` THEN1
            METIS_TAC [is_internal_redex_def, is_head_redex_unique] THEN
      DISCH_THEN ASSUME_TAC THEN
      `delta IN redex_posns M` by PROVE_TAC [is_internal_redex_def] THEN
      `(delta = p) \/ delta < p`
          by PROVE_TAC [residuals_to_right_of_reduction] THEN
      `?h0. h0 is_head_redex M` by PROVE_TAC [lemma11_4_3i] THEN
      `~(h0 = delta)` by PROVE_TAC [is_internal_redex_def] THEN
      `h0 = h`
         by PROVE_TAC [head_redex_preserved, is_head_redex_unique] THEN
      PROVE_TAC [head_redex_leftmost, posn_lt_antisym, posn_lt_irrefl],
      PROVE_TAC [is_internal_redex_def]
    ],
    PROVE_TAC [residual1_equal_singletons, NOT_IN_EMPTY],
    `p = delta_i`
       by PROVE_TAC [residual1_different_singletons, NOT_IN_EMPTY,
                     IN_INSERT, is_internal_redex_def] THEN
    SRW_TAC [][] THEN
    `delta_i IN redex_posns N`
       by PROVE_TAC [residual1_SUBSET, SUBSET_DEF] THEN
    Cases_on `?h. h is_head_redex N` THENL [
      POP_ASSUM STRIP_ASSUME_TAC THEN
      Q_TAC SUFF_TAC `~(delta_i = h)` THEN1
            PROVE_TAC [is_internal_redex_def, is_head_redex_unique] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      `?h0. h0 is_head_redex M` by PROVE_TAC [lemma11_4_3i] THEN
      `~(h0 = delta)` by PROVE_TAC [is_internal_redex_def] THEN
      `h0 = h` by PROVE_TAC [head_redex_preserved, is_head_redex_unique] THEN
      PROVE_TAC [is_internal_redex_def],
      PROVE_TAC [is_internal_redex_def]
    ]
  ]);

val beta0_induction =
    REWRITE_RULE [relationTheory.inv_DEF]
                 (MATCH_MP relationTheory.WF_INDUCTION_THM prop11_2_20)

val last_strip_path_label = store_thm(
  "last_strip_path_label",
  ``!s. finite s ==> (last (strip_path_label s) = strip_label (last s))``,
  HO_MATCH_MP_TAC pathTheory.finite_path_ind THEN
  SRW_TAC [][strip_path_label_thm]);


val okpath_monotone = prove(
  ``!R1 R2 s. (!x r y. R1 x r y ==> R2 x r y) /\ okpath R1 s ==>
              okpath R2 s``,
  Q_TAC SUFF_TAC
        `!R1 R2. (!x r y. R1 x r y ==> R2 x r y) ==>
                 !s. okpath R1 s ==> okpath R2 s` THEN1 PROVE_TAC [] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  HO_MATCH_MP_TAC pathTheory.okpath_co_ind THEN SRW_TAC [][]);

val lrcc_monotone = store_thm(
  "lrcc_monotone",
  ``!R1 R2 x r y. (!x y. R1 x y ==> R2 x y) /\
                  lrcc R1 x r y ==> lrcc R2 x r y``,
  Q_TAC SUFF_TAC
        `!R1 R2. (!x y. R1 x y ==> R2 x y) ==>
                 !x r y. lrcc R1 x r y ==> lrcc R2 x r y` THEN1
                 PROVE_TAC [] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  HO_MATCH_MP_TAC lrcc_ind THEN PROVE_TAC [lrcc_rules]);

Theorem length_lift_path[simp] :
    !M p. length (lift_path M p) = length p
Proof
  REPEAT GEN_TAC THEN
  Cases_on `finite p` THENL [
    Q.ID_SPEC_TAC `M` THEN POP_ASSUM MP_TAC THEN
    Q.ID_SPEC_TAC `p` THEN
    HO_MATCH_MP_TAC pathTheory.finite_path_ind THEN
    SRW_TAC [][lift_path_def, pathTheory.length_thm, finite_lift_path],
    SRW_TAC [][pathTheory.length_def, finite_lift_path]
  ]
QED

val PL_lift_path = store_thm(
  "PL_lift_path",
  ``!p. PL (lift_path M p) = PL p``,
  SRW_TAC [][pathTheory.PL_def, finite_lift_path]);
val _ = export_rewrites ["PL_lift_path"]

val n_posns_are_redex_posns = store_thm(
  "n_posns_are_redex_posns",
  ``!p n t. p IN n_posns n t ==> p IN redex_posns (strip_label t)``,
  SRW_TAC [][] THEN
  `?u. lrcc beta0 t p u` by PROVE_TAC [n_posns_beta0] THEN
  `lrcc (beta0 RUNION beta1) t p u` by PROVE_TAC [pick_a_beta] THEN
  `labelled_redn beta (strip_label t) p (strip_label u)`
     by PROVE_TAC [lrcc_labelled_redn] THEN
  PROVE_TAC [is_redex_occurrence_def, IN_term_IN_redex_posns]);

val zero_def = Define`
  zero n M = nlabel 0 (strip_label M) (n_posns n M)
`;

val zero_thm = store_thm(
  "zero_thm",
  ``(zero n (VAR s) = VAR s) /\
    (zero n (M @@ N) = zero n M @@ zero n N) /\
    (zero n (LAM v t) = LAM v (zero n t)) /\
    (zero n (LAMi m v t u) =
          if m = n then LAMi 0 v (zero n t) (zero n u)
          else LAM v (zero n t) @@ zero n u)``,
  ASM_SIMP_TAC (srw_ss())[zero_def, nlabel_thm, n_posns_def, strip_label_thm,
                          nlabel_app_no_nil] THEN
  Cases_on `n = m` THEN SRW_TAC [][]);

val n_posns_zero = store_thm(
  "n_posns_zero",
  ``!M n. n_posns 0 (zero n M) = n_posns n M``,
  HO_MATCH_MP_TAC simple_lterm_induction THEN
  SRW_TAC [][n_posns_def, zero_thm] THEN
  Cases_on `n = y` THEN SRW_TAC [][n_posns_def] THEN
  SRW_TAC [][EXTENSION, EQ_IMP_THM]);

val zero_vsubst = store_thm(
  "zero_vsubst",
  ``zero n ([VAR u/v] t) = [VAR u/v] (zero n t)``,
  SRW_TAC [][zero_def, GSYM nlabel_vsubst_commutes, n_posns_vsubst_invariant,
             strip_label_vsubst_commutes]);

Theorem FV_zero[simp] :
    FV (zero n t) = FV t
Proof
  SRW_TAC [][zero_def, FV_nlabel, FV_strip_label]
QED

val zero_subst = store_thm(
  "zero_subst",
  ``!t. zero n ([u/v] t) = [zero n u/v] (zero n t)``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN
  Q.EXISTS_TAC `v INSERT FV u` THEN SRW_TAC [][zero_thm, lSUB_VAR]);

val lrcc_zero = store_thm(
  "lrcc_zero",
  ``!M r N. lrcc (beta0 RUNION beta1) M r N ==>
            lrcc (beta0 RUNION beta1) (zero n M) r (zero n N)``,
  HO_MATCH_MP_TAC lrcc_ind THEN
  SRW_TAC [][zero_thm, RUNION_def, beta0_def, beta1_def] THENL [
    SRW_TAC [][zero_thm, zero_subst] THENL [
      PROVE_TAC [lrcc_rules, beta0_def, RUNION_def],
      PROVE_TAC [lrcc_rules, beta1_def, RUNION_def]
    ],
    SRW_TAC [][zero_thm, zero_subst] THEN
    PROVE_TAC [lrcc_rules, beta1_def, RUNION_def],
    PROVE_TAC [lrcc_rules],
    PROVE_TAC [lrcc_rules],
    PROVE_TAC [lrcc_rules],
    PROVE_TAC [lrcc_rules],
    PROVE_TAC [lrcc_rules],
    PROVE_TAC [lrcc_rules],
    PROVE_TAC [lrcc_rules]
  ]);

val residuals_have_precursors0 = prove(
  ``!M' r N'.
       lrcc (beta0 RUNION beta1) M' r N' ==>
       !p. p IN n_posns n N' ==>
           p IN residual1 (strip_label M') r (strip_label N') (n_posns n M')``,
  SRW_TAC [][residual1_def] THEN
  `labelled_redn beta (strip_label M') r (strip_label N')`
     by PROVE_TAC [lrcc_labelled_redn] THEN
  Q.ABBREV_TAC `M = strip_label M'` THEN
  Q.ABBREV_TAC `N = strip_label N'` THEN
  Q.ABBREV_TAC `M'' = nlabel 0 M (n_posns n M')` THEN
  Q.ABBREV_TAC `N'' = lift_redn M'' r N` THEN
  `M = strip_label M''` by PROVE_TAC [strip_label_nlabel] THEN
  `lrcc (beta0 RUNION beta1) M'' r N'' /\ (N = strip_label N'')`
     by PROVE_TAC [lift_redn_def] THEN
  `M'' = zero n M'` by PROVE_TAC [zero_def] THEN
  `N'' = zero n N'` by PROVE_TAC [lrcc_det, lrcc_zero] THEN
  SRW_TAC [][n_posns_zero])

val linear_set_fn_lemma = prove(
  ``(!X Y. f (X UNION Y) = f X UNION f Y) /\ (f {} = {}) ==>
    !X. FINITE X ==>
        !x. x IN f X ==> ?y. y IN X /\ x IN f {y}``,
  STRIP_TAC THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  ONCE_REWRITE_TAC [INSERT_SING_UNION] THEN
  SRW_TAC [][] THEN PROVE_TAC []);

val residual1_empty = store_thm(
  "residual1_empty",
  ``labelled_redn beta M r N ==> (residual1 M r N {} = {})``,
  STRIP_TAC THEN
  Q.ABBREV_TAC `s = pcons M r (stopped_at N)` THEN
  `okpath (labelled_redn beta) s`
     by SRW_TAC [][pathTheory.okpath_thm] THEN
  `residuals s {} = {}` by SRW_TAC [][residuals_EMPTY] THEN
  POP_ASSUM MP_TAC THEN SRW_TAC [][residuals_pcons, residuals_stopped_at] THEN
  PROVE_TAC [residual1_SUBSET, SUBSET_INTER_ABSORPTION]);

val residuals_have_precursors = store_thm(
  "residuals_have_precursors",
  ``lrcc (beta0 RUNION beta1) M' r N' ==>
    p IN n_posns n N' ==>
    ?p0. p IN residual1 (strip_label M') r (strip_label N') {p0} /\
         p0 IN n_posns n M'``,
  REPEAT STRIP_TAC THEN
  `p IN residual1 (strip_label M') r (strip_label N') (n_posns n M')`
     by PROVE_TAC [residuals_have_precursors0] THEN
  `labelled_redn beta (strip_label M') r (strip_label N')`
     by PROVE_TAC [lrcc_labelled_redn] THEN
  MAP_EVERY IMP_RES_TAC [residual1_pointwise_union, residual1_empty] THEN
  POP_ASSUM
  (fn th2 => (POP_ASSUM
              (fn th1 => ASSUME_TAC
                           (MATCH_MP linear_set_fn_lemma
                                     (CONJ (CONV_RULE SWAP_VARS_CONV th1)
                                           th2))))) THEN
  `FINITE (n_posns n M')` by METIS_TAC [n_posns_are_redex_posns,
                                        redex_posns_FINITE, SUBSET_DEF,
                                        SUBSET_FINITE] THEN
  METIS_TAC []);

val lemma11_4_4 = store_thm(
  "lemma11_4_4",
  ``!M N. fd_grandbeta M N ==> ?M'. M head_reduces M' /\ M' i1_reduces N``,
  SRW_TAC [][fd_grandbeta_def] THEN
  `!M'. ?s. okpath (lrcc beta0) s /\ (first s = M') /\ finite s /\
            is_head_reduction (strip_path_label s) /\
            !p n. p IN n_posns n (last s) ==>
                  ~(p is_head_redex (strip_label (last s)))`
     by (POP_ASSUM (K ALL_TAC) THEN
         HO_MATCH_MP_TAC beta0_induction THEN
         REPEAT STRIP_TAC THEN
         Cases_on `?p n. p is_head_redex (strip_label M') /\
                         p IN n_posns n M'` THENL [
           POP_ASSUM STRIP_ASSUME_TAC THEN
           `p IN redex_posns (strip_label M')`
              by PROVE_TAC [head_redex_is_redex] THEN
           `?N. labelled_redn beta (strip_label M') p N`
              by PROVE_TAC [IN_term_IN_redex_posns,
                            is_redex_occurrence_def] THEN
           Q.ABBREV_TAC `N' = lift_redn M' p N`  THEN
           `lrcc (beta0 RUNION beta1) M' p N' /\ (N = strip_label N')`
              by PROVE_TAC [lift_redn_def] THEN
           `lrcc beta0 M' p N'` by PROVE_TAC [pick_a_beta] THEN
           `lcompat_closure beta0 M' N'` by PROVE_TAC [lrcc_lcc] THEN
           `?s0. okpath (lrcc beta0) s0 /\ (first s0 = N') /\
                 finite s0 /\ is_head_reduction (strip_path_label s0) /\
                 !p n. p IN n_posns n (last s0) ==>
                       ~(p is_head_redex strip_label (last s0))`
                by METIS_TAC [] THEN
           Q.EXISTS_TAC `pcons M' p s0` THEN
           SRW_TAC [] [strip_path_label_thm, first_strip_path_label,
                       development_thm, strip_label_nlabel] THEN
           PROVE_TAC [],
           POP_ASSUM (STRIP_ASSUME_TAC o SIMP_RULE bool_ss []) THEN
           Q.EXISTS_TAC `stopped_at M'` THEN
           SRW_TAC [][strip_path_label_thm] THEN PROVE_TAC []
         ]) THEN
  POP_ASSUM (Q.SPEC_THEN `nlabel 0 M FS`
                         (Q.X_CHOOSE_THEN `s'` STRIP_ASSUME_TAC)) THEN
  Q.EXISTS_TAC `strip_label (last s')` THEN
  Q.ABBREV_TAC `s = strip_path_label s'` THEN
  ASM_SIMP_TAC (srw_ss()) [head_reduces_def] THEN CONJ_TAC THENL [
    Q.EXISTS_TAC `s` THEN
    SRW_TAC [][finite_strip_path_label, first_strip_path_label,
               strip_label_nlabel, last_strip_path_label],
    ALL_TAC
  ] THEN
  `okpath (lrcc (beta0 RUNION beta1)) s'`
     by (MATCH_MP_TAC okpath_monotone THEN
         Q.EXISTS_TAC `lrcc beta0` THEN SRW_TAC [][] THEN
         MATCH_MP_TAC lrcc_monotone THEN Q.EXISTS_TAC `beta0` THEN
         SRW_TAC [][RUNION_def]) THEN
  `lift_path (first s') (strip_path_label s') = s'`
     by (MATCH_MP_TAC lift_path_strip_path_label THEN SRW_TAC [][]) THEN
  `okpath (labelled_redn beta) s`
     by PROVE_TAC [lemma11_2_1] THEN
  `first s = M` by SRW_TAC [][first_strip_path_label, strip_label_nlabel] THEN
  `s IN development M FS` by PROVE_TAC [lemma11_2_12] THEN
  ASM_SIMP_TAC (srw_ss()) [i1_reduces_def] THEN
  `finite s` by SRW_TAC [][finite_strip_path_label] THEN
  `(last s' = nlabel 0 (last s) (residuals s FS)) /\
   residuals s FS SUBSET redex_posns (last s)`
     by PROVE_TAC [residuals_def] THEN
  `residuals s FS SUBSET (last s)` by PROVE_TAC [redex_occurrences_SUBSET] THEN
  `n_posns 0 (nlabel 0 (last s) (residuals s FS)) = n_posns 0 (last s')`
     by SRW_TAC [][] THEN
  `residuals s FS = n_posns 0 (last s')`
     by PROVE_TAC [n_posns_nlabel, SUBSET_INTER_ABSORPTION] THEN
  `?s2. s2 IN complete_development (last s) (residuals s FS)`
     by PROVE_TAC [complete_developments_always_exist] THEN
  Q.EXISTS_TAC `s2` THEN
  `s2 IN development (last s) (residuals s FS)`
     by PROVE_TAC [complete_development_thm] THEN
  `first s2 = strip_label (last s')` by
     PROVE_TAC [last_strip_path_label, wf_development] THEN
  `okpath (labelled_redn beta) s2` by PROVE_TAC [lemma11_2_12] THEN
  `finite s2 /\ (residuals s2 (residuals s FS) = {})`
     by PROVE_TAC [complete_development_thm] THEN
  `plink s s2 IN development M FS` by PROVE_TAC [linking_developments] THEN
  `last s = first s2` by PROVE_TAC [last_strip_path_label] THEN
  `residuals (plink s s2) FS = {}` by METIS_TAC [lemma11_2_6] THEN
  `finite (plink s s2)` by PROVE_TAC [pathTheory.finite_plink] THEN
  `plink s s2 IN complete_development M FS`
     by PROVE_TAC [complete_development_thm] THEN
  `last (plink s s2) = Cpl(M, FS)`
     by PROVE_TAC [Cpl_complete_development] THEN
  `last s2 = Cpl(M, FS)` by PROVE_TAC [pathTheory.last_plink] THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THENL [
    `okpath (lrcc beta0) (lift_path (last s') s2)`
       by METIS_TAC [lemma11_2_12] THEN
    Q.PAT_X_ASSUM `last u = nlabel x y z` (K ALL_TAC) THEN
    Q_TAC SUFF_TAC
          `!s.  okpath (lrcc beta0) s /\ finite s ==>
               (!p n. p IN n_posns n (first s) ==>
                      ~(p is_head_redex strip_label (first s))) ==>
               !i. i + 1 IN PL s ==>
                   nth_label i (strip_path_label s) is_internal_redex
                   el i (strip_path_label s)` THEN1
          (DISCH_THEN (Q.SPEC_THEN `lift_path (last s') s2` MP_TAC) THEN
           ASM_SIMP_TAC (srw_ss())
                        [finite_lift_path, first_lift_path,
                         strip_path_label_lift_path] THEN
           DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC) THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN
    HO_MATCH_MP_TAC pathTheory.finite_okpath_ind THEN
    SIMP_TAC (srw_ss())[pathTheory.okpath_thm, strip_path_label_thm,
                        GSYM ADD1] THEN
    MAP_EVERY Q.X_GEN_TAC [`x`,`r`,`p`] THEN REPEAT STRIP_TAC THEN
    `?m. r IN n_posns m x` by PROVE_TAC [beta0_n_posns] THEN
    `r IN redex_posns (strip_label x)`
       by PROVE_TAC [n_posns_are_redex_posns] THEN
    `r is_internal_redex (strip_label x)`
        by (SRW_TAC [][is_internal_redex_def] THEN PROVE_TAC []) THEN
    Cases_on `i` THEN SRW_TAC [][] THEN
    Q_TAC SUFF_TAC `!p' n. p' IN n_posns n (first p) ==>
                           ~(p' is_head_redex strip_label (first p))` THEN1
          PROVE_TAC [] THEN
    REPEAT STRIP_TAC THEN
    `labelled_redn beta (strip_label x) r (strip_label (first p))`
       by PROVE_TAC [pick_a_beta, lrcc_labelled_redn] THEN
    `lrcc (beta0 RUNION beta1) x r (first p)`
       by PROVE_TAC [pick_a_beta] THEN
    `?p0. p' IN residual1 (strip_label x) r (strip_label (first p)) {p0} /\
          p0 IN n_posns n' x`
       by PROVE_TAC [residuals_have_precursors] THEN
    `p0 is_internal_redex strip_label x`
       by PROVE_TAC [is_internal_redex_def, n_posns_are_redex_posns] THEN
    `p' is_internal_redex strip_label (first p)`
       by PROVE_TAC [lemma11_4_3iii] THEN
    PROVE_TAC [is_internal_redex_def],

    PROVE_TAC []
  ]);

val i_reduce1_i1_reduces = prove(
  ``M i_reduce1 N ==> M i1_reduces N``,
  SRW_TAC [][i_reduce1_def, i1_reduces_def] THEN
  Q.EXISTS_TAC `pcons M r (stopped_at N)` THEN
  SRW_TAC [][complete_development_thm, development_thm, residuals_pcons,
             residuals_stopped_at, redex_occurrences_SUBSET,
             residual1_SUBSET] THEN
  Q.EXISTS_TAC `{r}` THEN
  SRW_TAC [][residual1_equal_singletons, SUBSET_DEF] THEN
  PROVE_TAC [is_redex_occurrence_def, IN_term_IN_redex_posns]);

val i1_reduces_i_reduces = prove(
  ``M i1_reduces N ==> M i_reduces N``,
  SRW_TAC [][i1_reduces_def, i_reduces_def] THEN PROVE_TAC []);

val _ = augment_srw_ss [rewrites [REWRITE_CONV [EMPTY_SUBSET,
                                                redex_occurrences_SUBSET]
                                  ``{} SUBSET (M:term)``]]

val lemma11_4_5 = store_thm(
  "lemma11_4_5",
  ``!M M' N'. M i_reduce1 M' /\ M' head_reduces N' ==>
              ?N. M head_reduces N /\ N i_reduces N'``,
  Q_TAC SUFF_TAC
        `!M M' N'. M i1_reduces M' /\ M' -h-> N' ==>
                   ?N. M head_reduces N /\ N i1_reduces N'` THEN1
        (STRIP_TAC THEN
         Q_TAC SUFF_TAC
               `!M' N'. M' -h->* N' ==>
                        !M. M i1_reduces M' ==>
                            ?N. M head_reduces N /\ N i1_reduces N'`
            THEN1 METIS_TAC [head_reduces_RTC_hreduce1,
                             i_reduce1_i1_reduces, i1_reduces_i_reduces] THEN
         HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN CONJ_TAC THENL [
           MAP_EVERY Q.X_GEN_TAC [`M'`,`M`] THEN STRIP_TAC THEN
           Q.EXISTS_TAC `M` THEN
           SRW_TAC [][relationTheory.RTC_RULES, head_reduces_RTC_hreduce1],
           METIS_TAC [head_reduces_TRANS]
         ]) THEN
  SIMP_TAC (srw_ss()) [SimpL ``(==>)``, i1_reduces_def, head_reduce1_def] THEN
  REPEAT STRIP_TAC THEN
  `?r0. r0 is_head_redex M`
      by (Q_TAC SUFF_TAC
                `!s. okpath (labelled_redn beta) s /\ finite s ==>
                     (!i. i + 1 IN PL s ==>
                          nth_label i s is_internal_redex el i s) ==>
                     !r. r is_head_redex (last s) ==>
                         ?r0. r0 is_head_redex (first s)`
            THEN1 PROVE_TAC [] THEN
          POP_ASSUM_LIST (K ALL_TAC) THEN
          HO_MATCH_MP_TAC pathTheory.finite_okpath_ind THEN
          SRW_TAC [][GSYM ADD1] THENL [
            PROVE_TAC [],
            FIRST_X_ASSUM (fn th =>
                           MAP_EVERY (MP_TAC o GEN_ALL o C SPEC th)
                                     [``0``, ``SUC i``]) THEN
            SRW_TAC [][] THEN PROVE_TAC [lemma11_4_3i]
          ]) THEN
  `(residuals s (FS UNION {r0}) = {r}) /\ (r0 = r)`
     by (`residuals s FS = {}` by PROVE_TAC [complete_development_thm] THEN
         ASM_SIMP_TAC (srw_ss()) [residuals_pointwise_union] THEN
         Q_TAC SUFF_TAC
               `!s. okpath (labelled_redn beta) s /\ finite s ==>
                    (!i. i + 1 IN PL s ==>
                         nth_label i s is_internal_redex el i s) ==>
                    !r r0.
                       r0 is_head_redex (first s) /\
                       r is_head_redex (last s) ==>
                       (residuals s {r0} = {r}) /\ (r0 = r)`
            THEN1 METIS_TAC [] THEN
         POP_ASSUM_LIST (K ALL_TAC) THEN
         HO_MATCH_MP_TAC pathTheory.finite_okpath_ind THEN
         ASM_SIMP_TAC (srw_ss())
                      [GSYM ADD1, residuals_pcons,
                       residuals_stopped_at] THEN CONJ_TAC
         THENL [
           REPEAT STRIP_TAC THEN
           `r0 = r` by PROVE_TAC [is_head_redex_unique] THEN
           SRW_TAC [][GSYM SUBSET_INTER_ABSORPTION, head_redex_is_redex],
           MAP_EVERY Q.X_GEN_TAC [`x`,`r`,`p`] THEN STRIP_TAC THEN
           DISCH_THEN (fn th =>
                          MAP_EVERY (MP_TAC o GEN_ALL o C SPEC th)
                                    [``0``, ``SUC i``]) THEN
           ASM_SIMP_TAC (srw_ss()) [] THEN NTAC 2 STRIP_TAC THEN
           REPEAT GEN_TAC THEN STRIP_TAC THEN
           `?hr. (residual1 x r (first p) {r0} = {hr})/\
                 hr is_head_redex (first p)` by PROVE_TAC [lemma11_4_3ii] THEN
           `r0 is_head_redex (first p)`
                 by PROVE_TAC [is_internal_redex_def,
                               head_redex_preserved] THEN
           `r0 = hr` by PROVE_TAC [is_head_redex_unique] THEN
           ASM_SIMP_TAC (srw_ss()) []
         ]) THEN
  VAR_EQ_TAC THEN
  `FS SUBSET M` by PROVE_TAC [complete_development_thm, wf_development] THEN
  `{r} SUBSET M /\ {r} SUBSET M'`
       by SRW_TAC [][redexes_all_occur_def, IN_term_IN_redex_posns,
                     head_redex_is_redex] THEN
  `FS UNION {r} SUBSET M`
     by PROVE_TAC [redex_occurrences_SUBSET, UNION_SUBSET] THEN
  `plink s (pcons M' r (stopped_at N')) IN
     complete_development M (FS UNION {r})`
    by (ASM_SIMP_TAC (srw_ss()) [complete_development_thm,
                                 lemma11_2_6, residuals_pcons,
                                 residuals_stopped_at,
                                 residual1_equal_singletons] THEN
        MATCH_MP_TAC linking_developments THEN
        SRW_TAC [][development_thm, residual1_equal_singletons] THEN
        MATCH_MP_TAC development_SUBSET THEN
        Q.EXISTS_TAC `FS` THEN
        FULL_SIMP_TAC (srw_ss()) [complete_development_thm]) THEN
  `?M1. labelled_redn beta M r M1`
      by PROVE_TAC [is_redex_occurrence_def, head_redex_is_redex,
                    IN_term_IN_redex_posns] THEN
  Q.ABBREV_TAC `FS' = residual1 M r M1 FS` THEN
  `?s'. s' IN complete_development M1 FS'`
      by PROVE_TAC [complete_developments_always_exist,
                    residual1_SUBSET, redex_occurrences_SUBSET] THEN
  `finite s'` by PROVE_TAC [complete_development_thm, FD] THEN
  `first s' = M1` by PROVE_TAC [complete_development_thm, wf_development] THEN
  `okpath (labelled_redn beta) s' /\ s' IN development (first s') FS' /\
   (residuals s' FS' = {})`
      by PROVE_TAC [complete_development_thm, lemma11_2_12] THEN
  `pcons M r s' IN complete_development M (FS UNION {r})`
      by (SRW_TAC [][complete_development_thm, development_thm,
                     residual1_pointwise_union, residual1_equal_singletons,
                     residuals_pcons]) THEN
  `last s' = N'`
      by (`last (pcons M r s') = last (plink s (pcons M' r (stopped_at N')))`
              by PROVE_TAC [FDbang] THEN
          POP_ASSUM MP_TAC THEN SRW_TAC [][]) THEN
  `FS' SUBSET M1` by PROVE_TAC [complete_development_thm, wf_development] THEN
  `fd_grandbeta M1 N'` by PROVE_TAC [fd_grandbeta_def,
                                     Cpl_complete_development] THEN
  `?P. M1 head_reduces P /\ P i1_reduces N'` by PROVE_TAC [lemma11_4_4] THEN
  Q.EXISTS_TAC `P` THEN SRW_TAC [][] THEN
  METIS_TAC [head_reduces_RTC_hreduce1, head_reduce1_def,
             relationTheory.RTC_RULES]);

val lemma11_4_6 = store_thm(
  "lemma11_4_6",
  ``!M N. reduction beta M N ==>
          ?M'. M head_reduces M' /\ M' i_reduces N``,
  SIMP_TAC (srw_ss()) [] THEN
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN CONJ_TAC THENL [
    PROVE_TAC [head_reduces_RTC_hreduce1, i_reduces_RTC_i_reduce1,
               relationTheory.RTC_RULES],
    MAP_EVERY Q.X_GEN_TAC [`M`,`N`,`P`] THEN
    SIMP_TAC (srw_ss()) [GSYM LEFT_FORALL_IMP_THM,
                         GSYM RIGHT_EXISTS_AND_THM] THEN
    Q.X_GEN_TAC `M'` THEN STRIP_TAC THEN
    `?r. labelled_redn beta M r N` by PROVE_TAC [cc_labelled_redn] THEN
    `r IN redex_posns M` by PROVE_TAC [is_redex_occurrence_def,
                                       IN_term_IN_redex_posns] THEN
    Cases_on `r is_head_redex M` THENL [
      Q.EXISTS_TAC `M'` THEN SRW_TAC [][] THEN
      METIS_TAC [relationTheory.RTC_RULES, head_reduces_RTC_hreduce1,
                 head_reduce1_def],
      `r is_internal_redex M` by PROVE_TAC [is_internal_redex_def] THEN
      `M i_reduce1 N` by PROVE_TAC [i_reduce1_def] THEN
      `?Q. M head_reduces Q /\ Q i_reduces M'` by PROVE_TAC [lemma11_4_5] THEN
      Q.EXISTS_TAC `Q` THEN SRW_TAC [][] THEN
      METIS_TAC [relationTheory.RTC_RTC, i_reduces_RTC_i_reduce1]
    ]
  ]);

val cant_ireduce_to_atom = prove(
  ``!M N. (size N = 1) ==> ~(M i_reduce1 N)``,
  Q_TAC SUFF_TAC `!M r N. labelled_redn beta M r N ==>
                          (size N = 1) ==> ~(r is_internal_redex M)`
        THEN1 PROVE_TAC [i_reduce1_def] THEN
  HO_MATCH_MP_TAC labelled_redn_ind THEN
  SRW_TAC [] [is_internal_redex_def, redex_posns_thm, size_thm, size_nz,
              beta_def] THEN
  SRW_TAC [][redex_posns_thm, is_head_redex_thm]);

val i_reduce_to_LAM_underneath = prove(
  ``!M N v. ~(v IN FV M) ==>
            (M i_reduce1 (LAM v N) = ?M0. (M = LAM v M0) /\ M0 i_reduce1 N)``,
  SRW_TAC [][i_reduce1_def, EQ_IMP_THM, is_internal_redex_def,
             redex_posns_thm, is_head_redex_thm]
  THENL [
    Cases_on `r` THENL [
      Q.SPEC_THEN `M` (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC) term_CASES THEN
      FULL_SIMP_TAC (srw_ss() ++ COND_elim_ss)
                    [redex_posns_thm, is_head_redex_thm],
      RULE_ASSUM_TAC (ONCE_REWRITE_RULE [labelled_redn_cases]) THEN
      FULL_SIMP_TAC (srw_ss()) [LAM_eq_thm] THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [redex_posns_thm, is_head_redex_thm] THENL [
        PROVE_TAC [],
        SRW_TAC [][tpm_eqr, labelled_redn_beta_tpm_eqn, pmact_flip_args] THEN
        PROVE_TAC []
      ]
    ],
    Q.EXISTS_TAC `In :: r` THEN
    ASM_SIMP_TAC (srw_ss()) [is_head_redex_thm, redex_posns_thm] THEN
    PROVE_TAC [labelled_redn_rules]
  ]);

val FRESH_lists = store_thm(
  "FRESH_lists",
  ``!n s : string set.
       FINITE s ==> ?l'. ALL_DISTINCT l' /\ DISJOINT (LIST_TO_SET l') s /\
                         (LENGTH l' = n)``,
  Induct THEN SRW_TAC [][] THENL [
    RES_TAC THEN
    Q_TAC (NEW_TAC "z") `LIST_TO_SET l' UNION s` THEN
    Q.EXISTS_TAC `z::l'` THEN
    FULL_SIMP_TAC (srw_ss()) []
  ]);

val _ = augment_srw_ss [rewrites [RENAMING_REVERSE, RENAMING_ZIP_MAP_VAR]]

val head_reduction_standard = store_thm(
  "head_reduction_standard",
  ``!s. is_head_reduction s ==> standard_reduction s``,
  HO_MATCH_MP_TAC standard_coind THEN SRW_TAC [][is_head_reduction_thm] THEN
  METIS_TAC [head_redex_leftmost, posn_lt_antisym, posn_lt_irrefl]);

val i_reduce1_under_lam = prove(
  ``M i_reduce1 N ==> LAM v M i_reduce1 LAM v N``,
  SRW_TAC [][i_reduce1_def, is_internal_redex_def,
             redex_posns_thm, is_head_redex_thm] THEN
  Q.EXISTS_TAC `In::r` THEN SRW_TAC [][] THEN
  PROVE_TAC [labelled_redn_rules]);

val i_reduce1_under_LAMl = prove(
  ``!vs. M i_reduce1 N ==> LAMl vs M i_reduce1 LAMl vs N``,
  Induct THEN SRW_TAC [][i_reduce1_under_lam]);


val i1_reduce_to_LAMl = prove(
  ``!vs M N. DISJOINT (LIST_TO_SET vs) (FV M) /\ ALL_DISTINCT vs ==>
             (M i_reduce1 LAMl vs N =
              ?M0. (M = LAMl vs M0) /\ M0 i_reduce1 N)``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, IMP_CONJ_THM, FORALL_AND_THM] THEN
  CONJ_TAC THENL [
    Induct THEN
    SRW_TAC [][i_reduce_to_LAM_underneath] THEN
    `DISJOINT (LIST_TO_SET vs) (FV M0)`
        by (FULL_SIMP_TAC (srw_ss()) [] THEN
            Q.PAT_X_ASSUM `DISJOINT X Y` MP_TAC THEN
            SRW_TAC [][DISJOINT_DEF, EXTENSION] THEN PROVE_TAC []) THEN
    `?M00. (M0 = LAMl vs M00) /\ M00 i_reduce1 N` by PROVE_TAC [] THEN
    PROVE_TAC [],

    Q_TAC SUFF_TAC
       `!vs M N. M i_reduce1 N ==> LAMl vs M i_reduce1 LAMl vs N` THEN1
       PROVE_TAC [] THEN
    Induct THEN SRW_TAC [][] THEN
    PROVE_TAC [i_reduce1_under_lam]
  ]);

(* NOTE: renamed due to conflicts with pred_setTheory.SUBSET_DISJOINT *)
Theorem SUBSET_DISJOINT_L[local] :
    !X Y Z. X SUBSET Y /\ DISJOINT Y Z ==> DISJOINT X Z
Proof
  SRW_TAC [][SUBSET_DEF, DISJOINT_DEF, EXTENSION] THEN PROVE_TAC []
QED

val i_reduces_to_LAMl = prove(
  ``!vs M N. DISJOINT (LIST_TO_SET vs) (FV M) /\ ALL_DISTINCT vs ==>
             (M i_reduces LAMl vs N =
              ?M0. (M = LAMl vs M0) /\ M0 i_reduces N)``,
  SIMP_TAC (srw_ss()) [i_reduces_RTC_i_reduce1, EQ_IMP_THM,
                       FORALL_AND_THM, IMP_CONJ_THM] THEN CONJ_TAC
  THENL [
    Q_TAC SUFF_TAC
      `!M N1.
          RTC (i_reduce1) M N1 ==>
          !vs N. (N1 = LAMl vs N) /\ DISJOINT (LIST_TO_SET vs) (FV M) /\
                 ALL_DISTINCT vs ==>
                 ?M0.
                    (M = LAMl vs M0) /\ RTC $i_reduce1 M0 N`
      THEN1 PROVE_TAC [] THEN
    HO_MATCH_MP_TAC relationTheory.RTC_STRONG_INDUCT_RIGHT1 THEN
    SRW_TAC [][] THEN
    `DISJOINT (LIST_TO_SET vs) (FV N1)`
        by (Q_TAC SUFF_TAC `FV N1 SUBSET FV M` THEN1
                  PROVE_TAC [DISJOINT_SYM, SUBSET_DISJOINT_L] THEN
            Q_TAC SUFF_TAC
                  `!M N. RTC (i_reduce1) M N ==> FV N SUBSET FV M` THEN1
                  PROVE_TAC [] THEN
            HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
            SRW_TAC [][] THEN
            PROVE_TAC [cc_beta_FV_SUBSET, SUBSET_TRANS, labelled_redn_cc,
                       i_reduce1_def]) THEN
    `?N10. (N1 = LAMl vs N10) /\ N10 i_reduce1 N`
        by PROVE_TAC [i1_reduce_to_LAMl] THEN
    `?M0. (M = LAMl vs M0) /\ RTC (i_reduce1) M0 N10`
        by METIS_TAC [] THEN
    Q.EXISTS_TAC `M0` THEN
    PROVE_TAC [relationTheory.RTC_CASES2],

    Q_TAC SUFF_TAC `!M N. RTC $i_reduce1 M N ==>
                          !vs. RTC (i_reduce1) (LAMl vs M) (LAMl vs N)`
      THEN1 PROVE_TAC [] THEN
    HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
    SRW_TAC [][relationTheory.RTC_RULES] THEN
    PROVE_TAC [relationTheory.RTC_RULES, i_reduce1_under_LAMl]
  ]);

val _ = augment_srw_ss [rewrites [size_vsubst, size_ISUB]]

val cant_ireduce_to_lam_atom = prove(
  ``!vs M N. (size N = 1) ==> ~(M i_reduce1 LAMl vs N)``,
  REPEAT GEN_TAC THEN
  Q.SPECL_THEN [`LENGTH vs`, `LIST_TO_SET vs UNION FV M UNION FV N`]
               MP_TAC FRESH_lists THEN
  SIMP_TAC (srw_ss()) [FINITE_FV] THEN
  DISCH_THEN (Q.X_CHOOSE_THEN `vs'` STRIP_ASSUME_TAC) THEN
  `LAMl vs N = LAMl vs' (N ISUB REVERSE (ZIP (MAP VAR vs', vs)))`
     by SRW_TAC [][LAMl_ALPHA] THEN
  FULL_SIMP_TAC (srw_ss()) [DISJOINT_SYM] THEN
  SRW_TAC [][i1_reduce_to_LAMl, cant_ireduce_to_atom]);

val noncomb_nonabs_doesnt_reduce = store_thm(
  "noncomb_nonabs_doesnt_reduce",
  ``~is_comb t /\ ~is_abs t ==> ~(labelled_redn beta t r u)``,
  Q.SPEC_THEN `t` STRUCT_CASES_TAC term_CASES THEN
  SRW_TAC [][is_comb_thm, is_abs_thm] THEN
  ONCE_REWRITE_TAC [labelled_redn_cases] THEN
  SRW_TAC [][beta_def]);

val i_reduce1_to_app = store_thm(
  "i_reduce1_to_app",
  ``M i_reduce1 (N @@ P) =
      (?N0 r. (M = N0 @@ P) /\ ~is_comb N0 /\ labelled_redn beta N0 r N) \/
      (?N0. (M = N0 @@ P) /\ is_comb N0 /\ N0 i_reduce1 N) \/
      (?P0 r. (M = N @@ P0) /\ labelled_redn beta P0 r P)``,
  SRW_TAC [][i_reduce1_def, EQ_IMP_THM] THENL [
    RULE_ASSUM_TAC (ONCE_REWRITE_RULE [labelled_redn_cases]) THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss() ++ SatisfySimps.SATISFY_ss)
                  [is_internal_redex_def, is_head_redex_thm,
                   redex_posns_thm, beta_def]
    THENL [
      PROVE_TAC [],
      FULL_SIMP_TAC (srw_ss()) [COND_RATOR, COND_RAND]
    ],
    Q.EXISTS_TAC `Lt::r` THEN
    SRW_TAC [][labelled_redn_rules, is_internal_redex_def,
               redex_posns_thm, is_head_redex_thm] THEN
    PROVE_TAC [labelled_redn_beta_redex_posn],
    Q.EXISTS_TAC `Lt::r` THEN
    FULL_SIMP_TAC (srw_ss())[labelled_redn_rules, is_internal_redex_def,
                             redex_posns_thm, is_head_redex_thm],
    Q.EXISTS_TAC `Rt::r` THEN
    SRW_TAC [][labelled_redn_rules, is_internal_redex_def,
               redex_posns_thm, is_head_redex_thm] THEN
    PROVE_TAC [labelled_redn_beta_redex_posn]
  ]);

val i_reduce1_to_fold_app = store_thm(
  "i_reduce1_to_fold_app",
  ``!args t M.
      M i_reduce1 FOLDL APP t args  =
        (?t0 r. (M = FOLDL APP t0 args) /\ labelled_redn beta t0 r t /\
                ~is_comb t0 /\ ~(args = [])) \/
        (?t0. (M = FOLDL APP t0 args) /\ t0 i_reduce1 t) \/
        (?pfx a0 a sfx r.
                (M = FOLDL APP t (APPEND pfx (a0 :: sfx))) /\
                (args = (APPEND pfx (a :: sfx))) /\
                labelled_redn beta a0 r a)``,
  Induct THEN SRW_TAC [][] THEN
  POP_ASSUM (K ALL_TAC) THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
    `is_abs t0` by PROVE_TAC [noncomb_nonabs_doesnt_reduce] THEN
    POP_ASSUM MP_TAC THEN
    RULE_ASSUM_TAC (ONCE_REWRITE_RULE [labelled_redn_cases]) THEN
    FULL_SIMP_TAC (srw_ss()) [beta_def],
    FULL_SIMP_TAC (srw_ss()) [i_reduce1_to_app] THENL [
      PROVE_TAC [],
      PROVE_TAC [],
      DISJ2_TAC THEN DISJ2_TAC THEN
      MAP_EVERY Q.EXISTS_TAC [`[]`,`P0`,`h`,`args`,`r`] THEN SRW_TAC [][]
    ],
    REPEAT DISJ2_TAC THEN
    MAP_EVERY Q.EXISTS_TAC [`h::pfx`,`a0`,`a`, `sfx`,`r`] THEN SRW_TAC [][],
    DISJ2_TAC THEN DISJ1_TAC THEN Q.EXISTS_TAC `t0 @@ h` THEN
    SRW_TAC [][] THEN
    `is_abs t0` by PROVE_TAC [noncomb_nonabs_doesnt_reduce] THEN
    SRW_TAC [][i_reduce1_def] THEN
    Q.EXISTS_TAC `Lt::r` THEN
    SRW_TAC [][is_internal_redex_def, is_head_redex_thm, redex_posns_thm,
               labelled_redn_rules] THEN
    PROVE_TAC [labelled_redn_beta_redex_posn],
    DISJ2_TAC THEN DISJ1_TAC THEN
    Q.EXISTS_TAC `t0 @@ h` THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [i_reduce1_def, is_head_redex_thm,
                              is_internal_redex_def, redex_posns_thm] THEN
    Q.EXISTS_TAC `Lt::r` THEN SRW_TAC [][labelled_redn_rules] THEN
    PROVE_TAC [],
    Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
      DISJ2_TAC THEN DISJ1_TAC THEN Q.EXISTS_TAC `t @@ a0` THEN
      SRW_TAC [][i_reduce1_def, is_internal_redex_def] THEN
      Q.EXISTS_TAC `Rt::r` THEN
      SRW_TAC [][labelled_redn_rules, is_head_redex_thm, redex_posns_thm] THEN
      PROVE_TAC [labelled_redn_beta_redex_posn],
      REPEAT DISJ2_TAC THEN
      MAP_EVERY Q.EXISTS_TAC [`t'`, `a0`, `a`, `sfx`, `r`] THEN
      SRW_TAC [][]
    ]
  ]);

val EL_APPEND1 = prove(
  ``!l1 l2 n. n < LENGTH l1 ==> (EL n (APPEND l1 l2) = EL n l1)``,
  Induct THEN SRW_TAC [][] THEN
  Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) []);

val EL_APPEND2 = prove(
  ``!l1 l2 n. LENGTH l1 <= n /\ n < LENGTH l1 + LENGTH l2 ==>
              (EL n (APPEND l1 l2) = EL (n - LENGTH l1) l2)``,
  Induct THEN SRW_TAC [][] THEN
  Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.ADD_CLAUSES]);

val ireduces_to_fold_app = store_thm(
  "ireduces_to_fold_app",
  ``M i_reduces FOLDL APP t args ⇒
    ∃t0 args0.
        (M = FOLDL APP t0 args0) ∧ (LENGTH args0 = LENGTH args) ∧
        reduction beta t0 t ∧
        EVERY (λp. reduction beta (FST p) (SND p)) (ZIP (args0, args))``,
  SIMP_TAC (srw_ss()) [i_reduces_RTC_i_reduce1] THEN
  Q_TAC SUFF_TAC
     `∀M N. RTC (i_reduce1) M N ⇒
            ∀t args. (N = FOLDL APP t args) ⇒
                     ∃t0 args0.
                        (M = FOLDL APP t0 args0) ∧
                        (LENGTH args0 = LENGTH args) ∧
                        reduction beta t0 t ∧
                        EVERY (λp. reduction beta (FST p) (SND p))
                              (ZIP (args0, args))`
      THEN1 PROVE_TAC [] THEN
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT_RIGHT1 THEN
  SRW_TAC [][] THENL [
    MAP_EVERY Q.EXISTS_TAC [`t`, `args`] THEN
    SIMP_TAC (srw_ss()) [reduction_rules, listTheory.MEM_ZIP,
                         listTheory.EVERY_MEM, GSYM LEFT_FORALL_IMP_THM],
    FULL_SIMP_TAC (srw_ss()) [i_reduce1_to_fold_app] THENL [
      RES_TAC THEN
      MAP_EVERY Q.EXISTS_TAC [`t0'`, `args0`] THEN
      SRW_TAC [][] THEN
      PROVE_TAC [reduction_rules, labelled_redn_cc],
      RES_TAC THEN
      MAP_EVERY Q.EXISTS_TAC [`t0'`, `args0`] THEN
      SRW_TAC [][] THEN
      PROVE_TAC [reduction_rules, labelled_redn_cc, i_reduce1_def],
      RES_TAC THEN
      MAP_EVERY Q.EXISTS_TAC [`t0`, `args0`] THEN SRW_TAC [ARITH_ss][] THEN
      Q.PAT_X_ASSUM `EVERY f l` MP_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss)
                   [listTheory.EVERY_MEM, listTheory.MEM_ZIP,
                    GSYM LEFT_FORALL_IMP_THM] THEN
      STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
      Cases_on `n < LENGTH pfx` THENL [
        FIRST_X_ASSUM (Q.SPEC_THEN `n` MP_TAC) THEN
        SRW_TAC [numSimps.ARITH_ss][EL_APPEND1],
        `LENGTH pfx <= n` by DECIDE_TAC THEN
        FIRST_X_ASSUM (Q.SPEC_THEN `n` MP_TAC) THEN
        Cases_on `n = LENGTH pfx` THEN
        SRW_TAC [numSimps.ARITH_ss][EL_APPEND2, EL_APPEND1] THENL [
          PROVE_TAC [reduction_rules, labelled_redn_cc],
          `n − LENGTH pfx = SUC (n - (LENGTH pfx +1))` by DECIDE_TAC THEN
          FULL_SIMP_TAC (srw_ss()) []
        ]
      ]
    ]
  ]);

val standard_reductions_ok = store_thm(
  "standard_reductions_ok",
  ``!s. standard_reduction s ==> okpath (labelled_redn beta) s``,
  PROVE_TAC [standard_reduction_def]);

val valid_posns_relate = store_thm(
  "valid_posns_relate",
  ``!t r1 r2. r1 IN valid_posns t /\ r2 IN valid_posns t ==>
              r1 < r2 \/ (r1 = r2) \/ r2 < r1``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][valid_posns_thm]);

val lefty_relates_to_first_nonless = store_thm(
  "lefty_relates_to_first_nonless",
  ``!p. okpath (labelled_redn beta) p /\ finite p ==>
        !r0 r M. r0 IN redex_posns (first p) /\
                 (!n. SUC n IN PL p ==> r0 < nth_label n p) /\
                 labelled_redn beta (last p) r M ==>
                 r0 < r \/ (r0 = r) \/ r < r0``,
  HO_MATCH_MP_TAC finite_okpath_ind THEN SRW_TAC [][] THENL [
    `r IN redex_posns x` by METIS_TAC [labelled_redn_beta_redex_posn] THEN
    METIS_TAC [valid_posns_relate, redex_posns_are_valid],
    FIRST_X_ASSUM MATCH_MP_TAC THEN Q.EXISTS_TAC `M` THEN
    SRW_TAC [][] THENL [
      FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN SRW_TAC [][] THEN
      METIS_TAC [lr_beta_preserves_lefter_redexes],
      FIRST_X_ASSUM (Q.SPEC_THEN `SUC n` MP_TAC) THEN SRW_TAC [][]
    ]
  ]);

val okpath_every_el_relates = store_thm(
  "okpath_every_el_relates",
  ``!R p. okpath R p =
          !i. SUC i IN PL p ==> R (el i p) (nth_label i p) (el (SUC i) p)``,
  GEN_TAC THEN SIMP_TAC (srw_ss()) [EQ_IMP_THM, FORALL_AND_THM] THEN
  CONJ_TAC THENL [
    SIMP_TAC (srw_ss()) [GSYM RIGHT_FORALL_IMP_THM] THEN
    Induct_on `i`,
    HO_MATCH_MP_TAC okpath_co_ind
  ] THEN REPEAT GEN_TAC THENL [
    Q.SPEC_THEN `p` STRUCT_CASES_TAC path_cases,
    Q.SPEC_THEN `p` STRUCT_CASES_TAC path_cases,
    ALL_TAC
  ] THEN SRW_TAC [][] THENL [
    POP_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN SRW_TAC [][],
    RES_THEN MP_TAC THEN SIMP_TAC (srw_ss()) []
  ]);

val seg_SUC_pcons = store_thm(
  "seg_SUC_pcons",
  ``!i j p x r. i < j /\ j IN PL p ==>
                (seg (SUC i) j (pcons x r p) = seg i (j - 1) p)``,
  SRW_TAC [][seg_def] THEN
  Q_TAC SUFF_TAC `j - SUC i = j - 1 - i` THEN1 SRW_TAC [][] THEN
  DECIDE_TAC);

val standard_reduction_thm = store_thm(
  "standard_reduction_thm",
  ``(standard_reduction (stopped_at x) = T) /\
    (standard_reduction (pcons x r p) =
       labelled_redn beta x r (first p) /\
       (!n r0. r0 IN redex_posns x /\ r0 < r /\ n + 1 IN PL p ==>
               r0 < nth_label n p) /\
       standard_reduction p)``,
  CONJ_TAC THENL [
    SRW_TAC [][standard_reduction_def],
    SIMP_TAC (srw_ss()) [EQ_IMP_THM,
                         GSYM RIGHT_FORALL_IMP_THM, IMP_CONJ_THM] THEN
    REPEAT CONJ_TAC THENL [
      SRW_TAC [][standard_reduction_def],
      SIMP_TAC (srw_ss())[better_standard_reduction,
                          GSYM ADD1] THEN
      completeInduct_on `n` THEN REPEAT STRIP_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n`, `0`] MP_TAC) THEN
      `n IN PL p` by METIS_TAC [PL_downward_closed, DECIDE ``n < SUC n``] THEN
      ASM_SIMP_TAC (srw_ss()) [seg_def, residuals_pcons,
                               residual1_different_singletons] THEN
      `!m. SUC m IN PL (take n p) ==> r0 < nth_label m (take n p)`
           by (SRW_TAC [][PL_take] THEN
               `m < n` by DECIDE_TAC THEN
               SRW_TAC [][nth_label_take] THEN
               `SUC m IN PL p`
                   by METIS_TAC [PL_downward_closed,
                                 DECIDE ``m < n = SUC m < SUC n``] THEN
               METIS_TAC []) THEN
      `labelled_redn beta (el n p) (nth_label n p) (el (SUC n) p)`
           by METIS_TAC [okpath_every_el_relates] THEN
      `last (take n p) = el n p` by SRW_TAC [][last_take] THEN
      `okpath (labelled_redn beta) (take n p)` by METIS_TAC [okpath_take] THEN
      `first (take n p) = first p` by SRW_TAC [][first_take] THEN
      `r0 IN redex_posns (first p)`
         by METIS_TAC [lr_beta_preserves_lefter_redexes] THEN
      `finite (take n p)` by SRW_TAC [][finite_take] THEN
      `r0 < nth_label n p \/ (r0 = nth_label n p) \/ nth_label n p < r0`
         by METIS_TAC [lefty_relates_to_first_nonless]
      THENL [
        SRW_TAC [][],
        DISCH_THEN (Q.SPEC_THEN `r0` MP_TAC) THEN SRW_TAC [][] THEN
        SRW_TAC [][residuals_different_singletons],
        Q.ABBREV_TAC `r00 = nth_label n p` THEN
        `r00 IN redex_posns (first p)`
            by METIS_TAC [cant_create_redexes_to_left] THEN
        `r00 IN redex_posns x`
            by METIS_TAC [cant_create_redexes_to_left1] THEN
        DISCH_THEN (Q.SPEC_THEN `r00` MP_TAC) THEN
        `r00 < r` by METIS_TAC [posn_lt_trans] THEN
        `!m. SUC m IN PL (take n p) ==> r00 < nth_label m (take n p)`
            by (SRW_TAC [][PL_take] THEN
                `m < n` by DECIDE_TAC THEN
                SRW_TAC [][nth_label_take] THEN
                `SUC m IN PL p`
                   by METIS_TAC [PL_downward_closed,
                                 DECIDE ``m < n = SUC m < SUC n``] THEN
                METIS_TAC []) THEN
        SRW_TAC [][residuals_different_singletons]
      ],

      SRW_TAC [][better_standard_reduction, GSYM ADD1] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`SUC i`, `SUC j`] MP_TAC) THEN
      SRW_TAC [][seg_def],

      SRW_TAC [][better_standard_reduction, GSYM ADD1] THEN
      Cases_on `j` THENL [
        FULL_SIMP_TAC (srw_ss()) [seg_def] THEN
        `?n. i = SUC n` by METIS_TAC [TypeBase.nchotomy_of ``:num``,
                                      DECIDE ``0 < n = ~(n = 0)``] THEN
        FULL_SIMP_TAC (srw_ss()) [] THEN
        `n IN PL p` by METIS_TAC [PL_downward_closed,
                                  DECIDE ``n < SUC n``] THEN
        `okpath (labelled_redn beta) (take n p)`
           by SRW_TAC [][okpath_take] THEN
        `finite (take n p)` by SRW_TAC [][finite_take] THEN
        `first (take n p) = first p` by SRW_TAC [][first_take] THEN
        SRW_TAC [][residuals_pcons, residual1_different_singletons] THEN
        `p' IN redex_posns (first p)`
           by METIS_TAC [lr_beta_preserves_lefter_redexes] THEN
        `!m. SUC m IN PL (take n p) ==> p' < nth_label m (take n p)`
           by (SRW_TAC [][PL_take] THEN
               `m < n` by DECIDE_TAC THEN
               SRW_TAC [][nth_label_take] THEN
               FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [][] THEN
               METIS_TAC [PL_downward_closed,
                          arithmeticTheory.LESS_MONO_EQ]) THEN
        SRW_TAC [][residuals_different_singletons] THEN
        METIS_TAC [posn_lt_irrefl],

        FULL_SIMP_TAC (srw_ss()) [] THEN
        `?m. i = SUC m` by METIS_TAC [TypeBase.nchotomy_of ``:num``,
                                      DECIDE ``~(SUC n < 0)``] THEN
        FULL_SIMP_TAC (srw_ss()) [] THEN
        `n < SUC m` by DECIDE_TAC THEN
        SRW_TAC [][seg_SUC_pcons]
      ]
    ]
  ]);


val PL_plink = prove(
  ``!p1. finite p1 ==>
         !x p2. x IN PL (plink p1 p2) =
                x IN PL p1 \/
                ?n. 0 < n /\ n IN PL p2 /\ (x = n + THE (length p1) - 1)``,
  HO_MATCH_MP_TAC pathTheory.finite_path_ind THEN
  SRW_TAC [][pathTheory.length_thm] THENL [
    PROVE_TAC [pathTheory.PL_0, DECIDE ``(x = 0) \/ 0 < x``],
    SRW_TAC [numSimps.ARITH_ss][LEFT_AND_OVER_OR, EXISTS_OR_THM,
                                GSYM RIGHT_EXISTS_AND_THM] THEN
    `0 < THE (length p1)`
       by (`?m. length p1 = SOME m`
              by PROVE_TAC [pathTheory.finite_length] THEN
           SRW_TAC [][] THEN
           Q_TAC SUFF_TAC `~(m = 0)` THEN1 DECIDE_TAC THEN STRIP_TAC THEN
           PROVE_TAC [pathTheory.length_never_zero]) THEN
    SRW_TAC [numSimps.ARITH_ss][ADD1] THEN PROVE_TAC []
  ]);

val el_plink_left = store_thm(
  "el_plink_left",
  ``!i p1. i IN PL p1 /\ (last p1 = first p2) ==>
           (el i (plink p1 p2) = el i p1)``,
  Induct THENL [
    SRW_TAC [][first_plink],
    GEN_TAC THEN
    Q.SPEC_THEN `p1` STRUCT_CASES_TAC path_cases THEN
    SRW_TAC [][]
  ]);

val drop_plink_left = store_thm(
  "drop_plink_left",
  ``!i p1. i IN PL p1 /\ (last p1 = first p2) ==>
           (drop i (plink p1 p2) = plink (drop i p1) p2)``,
  Induct THEN SRW_TAC [][] THEN
  Q.SPEC_THEN `p1` (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC) path_cases THEN
  FULL_SIMP_TAC (srw_ss()) []);

val take_plink_left = store_thm(
  "take_plink_left",
  ``!i p1. i IN PL p1 /\ (last p1 = first p2) ==>
           (take i (plink p1 p2) = take i p1)``,
  Induct THENL [
    SRW_TAC [][],
    GEN_TAC THEN
    Q.SPEC_THEN `p1` STRUCT_CASES_TAC path_cases THEN
    SRW_TAC [][]
  ]);

val IN_PL_tail = store_thm(
  "IN_PL_tail",
  ``!x p1. x + 1 IN PL p1 ==> x IN PL (tail p1)``,
  Induct THENL [
    SRW_TAC [][],
    GEN_TAC THEN
    Q.SPEC_THEN `p1` STRUCT_CASES_TAC path_cases THEN
    SRW_TAC [][arithmeticTheory.ADD_CLAUSES, GSYM ADD1]
  ]);

val last_drop = store_thm(
  "last_drop",
  ``!i p. i IN PL p ==> (last (drop i p) = last p)``,
  Induct THENL [
    SRW_TAC [][],
    GEN_TAC THEN Q.SPEC_THEN `p` STRUCT_CASES_TAC path_cases THEN
    SRW_TAC [][]
  ]);

val seg_plink_left = store_thm(
  "seg_plink_left",
  ``!i j. i <= j /\ j IN PL p1 /\ (last p1 = first p2) ==>
          (seg i j (plink p1 p2) = seg i j p1)``,
  SRW_TAC [][seg_def] THEN
  `i IN PL p1` by METIS_TAC [arithmeticTheory.LESS_OR_EQ,
                             PL_downward_closed] THEN
  SRW_TAC [][drop_plink_left] THEN
  `j - i IN PL (drop i p1)` by SRW_TAC [numSimps.ARITH_ss][IN_PL_drop] THEN
  SRW_TAC [][take_plink_left, last_drop]);

val nth_label_plink_left = store_thm(
  "nth_label_plink_left",
  ``!i p1. i + 1 IN PL p1 ==> (nth_label i (plink p1 p2) = nth_label i p1)``,
  Induct THEN GEN_TAC THEN
  Q.SPEC_THEN `p1` STRUCT_CASES_TAC path_cases THEN
  SRW_TAC [][arithmeticTheory.ADD_CLAUSES, GSYM ADD1]);

val nth_label_plink_right = store_thm(
  "nth_label_plink_right",
  ``!i p1 p2. finite p1 /\ THE (length p1) <= SUC i /\ (last p1 = first p2) ==>
              (nth_label i (plink p1 p2) =
               nth_label (SUC i - THE (length p1)) p2)``,
  Induct THEN
  GEN_TAC THEN Q.SPEC_THEN `p1` STRUCT_CASES_TAC path_cases THEN
  SRW_TAC [][length_thm, DECIDE ``y + x <= x = (y = 0)``] THENL [
    FULL_SIMP_TAC (srw_ss()) [finite_length] THEN
    Q.PAT_X_ASSUM `length x = SOME y` MP_TAC THEN
    DISCH_THEN (fn th => SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN VAR_EQ_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [length_never_zero],
    `THE (length q) <= SUC i` by DECIDE_TAC  THEN
    SRW_TAC [][GSYM ADD1]
  ]);

val standard_reductions_join_over_comb = prove(
  ``!s1 s2.
      standard_reduction s1 /\ standard_reduction s2 /\
      finite s1 /\ finite s2 ==>
      standard_reduction (plink (pmap (\t. t @@ first s2) (CONS Lt) s1)
                                (pmap (APP (last s1)) (CONS Rt) s2))``,
  Q_TAC SUFF_TAC
    `!s1.
        okpath (labelled_redn beta) s1 /\ finite s1 ==>
        standard_reduction s1 ==>
        !s2. standard_reduction s2 /\ finite s2 ==>
             standard_reduction (plink (pmap (\t. t @@ first s2) (CONS Lt) s1)
                                       (pmap (APP (last s1)) (CONS Rt) s2))`
     THEN1 METIS_TAC [standard_reductions_ok] THEN
  HO_MATCH_MP_TAC finite_okpath_ind THEN
  SIMP_TAC (srw_ss()) [standard_reduction_thm] THEN CONJ_TAC THENL [
    Q_TAC SUFF_TAC
          `!s. okpath (labelled_redn beta) s /\ finite s ==>
               !x. standard_reduction s ==>
                   standard_reduction (pmap (APP x) (CONS Rt) s)` THEN1
          METIS_TAC [standard_reductions_ok] THEN
    HO_MATCH_MP_TAC finite_okpath_ind THEN
    SRW_TAC [][standard_reduction_thm, labelled_redn_rules] THEN
    FULL_SIMP_TAC (srw_ss()) [GSYM ADD1, nth_label_pmap] THEN
    FULL_SIMP_TAC (srw_ss()) [redex_posns_thm] THENL [
      REPEAT VAR_EQ_TAC THEN FULL_SIMP_TAC (srw_ss()) [],
      FULL_SIMP_TAC (srw_ss() ++ COND_elim_ss) [] THEN RES_TAC
    ],
    MAP_EVERY Q.X_GEN_TAC [`x`,`r`,`p`] THEN REPEAT STRIP_TAC THEN
    Q.ABBREV_TAC `p' = pmap (\t. t @@ first s2) (CONS Lt) p` THEN
    Q.ABBREV_TAC `s2' = pmap (APP (last p)) (CONS Rt) s2` THEN
    `last p' = first s2'` by SRW_TAC [][] THENL [
       SRW_TAC [][first_plink, labelled_redn_rules],

      `finite p'` by SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [PL_plink] THENL [
        SRW_TAC [][] THEN
        FULL_SIMP_TAC (srw_ss()) [nth_label_plink_left, nth_label_pmap,
                                  GSYM ADD1] THEN
        FULL_SIMP_TAC (srw_ss()) [redex_posns_thm] THEN
        SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
        FULL_SIMP_TAC (srw_ss() ++ COND_elim_ss) [] THEN RES_TAC,

        `THE (length p') <= SUC n` by DECIDE_TAC THEN
        ASM_SIMP_TAC (srw_ss())[nth_label_plink_right] THEN
        `SUC n - THE (length p') = n' - 1` by DECIDE_TAC THEN
        `SUC (n' - 1) = n'` by DECIDE_TAC THEN
        SRW_TAC [][] THEN
        FULL_SIMP_TAC (srw_ss()) [nth_label_pmap] THEN
        MATCH_MP_TAC posn_lt_trans THEN Q.EXISTS_TAC `Lt::r` THEN
        SRW_TAC [][]
      ]
    ]
  ]);

val standard_reductions_join_over_comb = store_thm(
  "standard_reductions_join_over_comb",
  ``!s1 s2. standard_reduction s1 /\ finite s1 /\
            standard_reduction s2 /\ finite s2 ==>
            ?s.
                standard_reduction s /\ finite s /\
                (first s = first s1 @@ first s2) /\
                (last s = last s1 @@ last s2)``,
  REPEAT STRIP_TAC THEN
  Q.ABBREV_TAC `s1' = pmap (\t. t @@ first s2) (CONS Lt) s1` THEN
  Q.ABBREV_TAC `s2' = pmap (APP (last s1)) (CONS Rt) s2` THEN
  Q.EXISTS_TAC `plink s1' s2'` THEN
  `last s1' = first s2'` by SRW_TAC [][] THEN
  SRW_TAC [][] THEN
  METIS_TAC [standard_reductions_join_over_comb]);

val head_standard_is_standard = store_thm(
  "head_standard_is_standard",
  ``!s1 s2.
       is_head_reduction s1 /\ finite s1 /\ (last s1 = first s2) /\
       standard_reduction s2 ==>
       standard_reduction (plink s1 s2)``,
  Q_TAC SUFF_TAC
        `!s1. okpath (labelled_redn beta) s1 /\ finite s1 ==>
              is_head_reduction s1 ==>
              !s2. standard_reduction s2 /\ (last s1 = first s2) ==>
                   standard_reduction (plink s1 s2)` THEN1
        METIS_TAC [is_head_reduction_def] THEN
  HO_MATCH_MP_TAC finite_okpath_ind THEN
  SRW_TAC [][standard_reduction_thm, is_head_reduction_thm] THEN
  METIS_TAC [head_redex_leftmost, posn_lt_irrefl, posn_lt_antisym]);

val collect_standard_reductions = prove(
  ``!args0 args s.
       (LENGTH args = LENGTH args0) /\
       standard_reduction s /\ finite s /\
       EVERY (\p. ?arg_s. (first arg_s = FST p) /\
                          finite arg_s /\
                          (last arg_s = SND p) /\
                          standard_reduction arg_s) (ZIP (args0, args)) ==>
       ?s'. standard_reduction s' /\ finite s' /\
            (first s' = FOLDL APP (first s) args0) /\
            (last s' = FOLDL APP (last s) args)``,
  Induct THEN SRW_TAC [][] THENL [
    FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [],
    FULL_SIMP_TAC (srw_ss()) [listTheory.LENGTH_CONS] THEN VAR_EQ_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    `?s0. standard_reduction s0 /\ finite s0 /\
          (first s @@ h = first s0) /\ (last s @@ h' = last s0)`
       by (ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN REPEAT VAR_EQ_TAC THEN
           MATCH_MP_TAC standard_reductions_join_over_comb THEN
           SRW_TAC [][]) THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []
  ]);

val standard_reduction_under_LAM = prove(
  ``!s. standard_reduction s /\ finite s ==>
        standard_reduction (pmap (LAM v) (CONS In) s)``,
  Q_TAC SUFF_TAC
        `!s. okpath (labelled_redn beta) s /\ finite s ==>
             standard_reduction s ==>
             standard_reduction (pmap (LAM v) (CONS In) s)` THEN1
        METIS_TAC [standard_reductions_ok] THEN
  HO_MATCH_MP_TAC finite_okpath_ind THEN
  SRW_TAC [][standard_reduction_thm, labelled_redn_rules,
             nth_label_pmap, GSYM ADD1, redex_posns_thm] THEN
  FULL_SIMP_TAC (srw_ss()) []);

val standard_reduction_under_LAMl = prove(
  ``!vs s. finite s /\ standard_reduction s ==>
           ?s'. (first s' = LAMl vs (first s)) /\
                (last s' = LAMl vs (last s)) /\ finite s' /\
                standard_reduction s'``,
  Induct THEN SRW_TAC [][] THENL [
    METIS_TAC [],
    `?s0. (first s0 = LAMl vs (first s)) /\
          (last s0 = LAMl vs (last s)) /\ finite s0 /\ standard_reduction s0`
      by METIS_TAC [] THEN
    Q.EXISTS_TAC `pmap (LAM h) (CONS In) s0` THEN SRW_TAC [][] THEN
    METIS_TAC [standard_reduction_under_LAM]
  ]);

val standardisation_theorem = store_thm(
  "standardisation_theorem",
  ``!M N. reduction beta M N ==>
          ?s. (first s = M) /\ finite s /\ (last s = N) /\
              standard_reduction s``,
  CONV_TAC SWAP_VARS_CONV THEN GEN_TAC THEN completeInduct_on `size N` THEN
  FULL_SIMP_TAC (srw_ss()) [GSYM RIGHT_FORALL_IMP_THM] THEN
  SRW_TAC [][] THEN
  `?Z. M head_reduces Z /\ Z i_reduces N` by PROVE_TAC [lemma11_4_6] THEN
  Q.SPEC_THEN `N` STRIP_ASSUME_TAC strange_cases THENL [
    `Z = N` by
       (FULL_SIMP_TAC (srw_ss()) [i_reduces_RTC_i_reduce1] THEN
        RULE_ASSUM_TAC (ONCE_REWRITE_RULE [relationTheory.RTC_CASES2]) THEN
        FULL_SIMP_TAC (srw_ss()) [] THEN
        PROVE_TAC [cant_ireduce_to_lam_atom]) THEN
    PROVE_TAC [head_reduces_def, head_reduction_standard],
    Q.SPECL_THEN [`LENGTH vs`,
                   `LIST_TO_SET vs UNION FV (FOLDL APP t args) UNION FV Z`]
                 MP_TAC FRESH_lists THEN
    SIMP_TAC (srw_ss()) [FINITE_FV] THEN
    DISCH_THEN (Q.X_CHOOSE_THEN `vs'` STRIP_ASSUME_TAC) THEN
    Q.ABBREV_TAC `sub = REVERSE (ZIP (MAP VAR vs' : term list, vs))` THEN
    `LAMl vs (FOLDL APP t args) = LAMl vs' (FOLDL APP t args ISUB sub)`
       by SRW_TAC [][LAMl_ALPHA] THEN
    Q.ABBREV_TAC `N0 = FOLDL APP t args ISUB sub` THEN
    `?Z0. (Z = LAMl vs' Z0) /\ Z0 i_reduces N0`
       by METIS_TAC [i_reduces_to_LAMl, DISJOINT_SYM] THEN
    `N0 = FOLDL APP (t ISUB sub) (MAP (\t. t ISUB sub) args)`
       by SRW_TAC [][FOLDL_APP_ISUB] THEN
    Q.ABBREV_TAC `args' = MAP (\t. t ISUB sub) args` THEN
    `?t0 args0.
        (Z0 = FOLDL APP t0 args0) /\ (LENGTH args0 = LENGTH args') /\
        reduction beta t0 (t ISUB sub) /\
        EVERY (\p. reduction beta (FST p) (SND p)) (ZIP (args0, args'))`
       by METIS_TAC [ireduces_to_fold_app] THEN
    `!t. size (t ISUB sub) = size t`
       by SRW_TAC [][RENAMING_REVERSE, RENAMING_ZIP] THEN
    `size (t ISUB sub) < size N`
       by (SRW_TAC [][size_foldl_app] THEN
           Cases_on `args` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
           `size t + size h + 1 <=
             FOLDL (\n t. n + size t + 1) (size t + size h + 1) t'` by
                METIS_TAC [size_foldl_app_lt] THEN
           DECIDE_TAC) THEN
    `?ts. (first ts = t0) /\ finite ts /\ (last ts = t ISUB sub) /\
          standard_reduction ts` by METIS_TAC[] THEN
    `EVERY (\p. ?arg_s. (first arg_s = FST p) /\ finite arg_s /\
                        (last arg_s = SND p) /\ standard_reduction arg_s)
           (ZIP (args0, args'))`
       by (FULL_SIMP_TAC (srw_ss())[listTheory.EVERY_MEM, listTheory.MEM_ZIP,
                                    GSYM LEFT_FORALL_IMP_THM] THEN
           REPEAT STRIP_TAC THEN
           FULL_SIMP_TAC (srw_ss()) [AND_IMP_INTRO] THEN
           FIRST_X_ASSUM MATCH_MP_TAC THEN
           ASM_SIMP_TAC (srw_ss()) [size_args_foldl_app] THEN
           Q.PAT_X_ASSUM `LENGTH x = LENGTH y` ASSUME_TAC THEN
           FULL_SIMP_TAC (srw_ss()) [listTheory.MEM_ZIP,
                                     GSYM LEFT_FORALL_IMP_THM]) THEN
    `?sr. standard_reduction sr /\ finite sr /\
          (first sr = FOLDL APP (first ts) args0) /\
          (last sr = FOLDL APP (last ts) args')`
       by (MATCH_MP_TAC collect_standard_reductions THEN
           ASM_REWRITE_TAC []) THEN
    `?hr. is_head_reduction hr /\ finite hr /\ (first hr = M) /\
          (last hr = Z)`
       by METIS_TAC [head_reduces_def] THEN
    `?sr2. (first sr2 = LAMl vs' (first sr)) /\
           (last sr2 = LAMl vs' (last sr)) /\
           finite sr2 /\ standard_reduction sr2`
       by (MATCH_MP_TAC standard_reduction_under_LAMl THEN
           ASM_REWRITE_TAC []) THEN
    Q.EXISTS_TAC `plink hr sr2` THEN
    SRW_TAC [][head_standard_is_standard]
  ]);

val hnf_preserved = store_thm(
  "hnf_preserved",
  ``!M N. reduction beta M N ==> hnf M ==> hnf N``,
  SIMP_TAC (srw_ss())[] THEN
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
  SRW_TAC [][hnf_no_head_redex] THEN
  Q_TAC SUFF_TAC `!p. ~(p is_head_redex N)` THEN1 PROVE_TAC [] THEN
  `?r. labelled_redn beta M r M'` by METIS_TAC [cc_labelled_redn] THEN
  `r is_internal_redex M` by METIS_TAC [is_internal_redex_def,
                                        labelled_redn_beta_redex_posn] THEN
  METIS_TAC [lemma11_4_3i]);

val hnf_reflected_over_ireduction = store_thm(
  "hnf_reflected_over_ireduction",
  ``!M N. M i_reduces N ==> hnf N ==> hnf M``,
  SIMP_TAC (srw_ss()) [i_reduces_RTC_i_reduce1] THEN
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
  SRW_TAC [][hnf_no_head_redex, i_reduce1_def] THEN
  METIS_TAC [lemma11_4_3ii]);

(* NOTE: This is also Theorem 8.3.11 [1, p.174] *)
val corollary11_4_8 = store_thm(
  "corollary11_4_8",
  ``!M. has_hnf M = finite (head_reduction_path M)``,
  GEN_TAC THEN EQ_TAC THENL [
    SRW_TAC [][has_hnf_def] THEN
    `?Z. reduction beta M Z /\ reduction beta N Z`
        by METIS_TAC [lameq_betaconversion, theorem3_13, beta_CR] THEN
    `hnf Z` by METIS_TAC [hnf_preserved] THEN
    `?Z0. M head_reduces Z0 /\ Z0 i_reduces Z` by METIS_TAC [lemma11_4_6] THEN
    `hnf Z0` by METIS_TAC [hnf_reflected_over_ireduction] THEN
    `?p. finite p /\ (first p = M) /\ (last p = Z0) /\
         is_head_reduction p` by METIS_TAC [head_reduces_def] THEN
    METIS_TAC [head_reduction_path_unique],
    SRW_TAC [][has_hnf_def, lameq_betaconversion] THEN
    `(first (head_reduction_path M) = M) /\
     hnf (last (head_reduction_path M)) /\
     is_head_reduction (head_reduction_path M)`
        by METIS_TAC [head_reduction_path_def] THEN
    Q.EXISTS_TAC `last (head_reduction_path M)` THEN
    METIS_TAC [head_reduces_reduction_beta, conversion_rules,
               head_reduces_def]
  ]);

(* named by analogy with has_bnf_thm in chap3Theory *)
val has_hnf_thm = store_thm(
  "has_hnf_thm",
  ``has_hnf M ⇔ ∃N. M -h->* N ∧ hnf N``,
  SRW_TAC [][corollary11_4_8, EQ_IMP_THM] THENL [
    Q.EXISTS_TAC `last (head_reduction_path M)` THEN
    METIS_TAC [head_reduction_path_def, head_reduces_def,
               head_reduces_RTC_hreduce1],

    `M head_reduces N` by METIS_TAC [head_reduces_RTC_hreduce1] THEN
    `∃p. finite p ∧ (first p = M) ∧ (last p = N) ∧ is_head_reduction p`
       by METIS_TAC [head_reduces_def] THEN
    METIS_TAC [head_reduction_path_unique]
  ]);

val has_hnf_whnf = store_thm(
  "has_hnf_whnf",
  ``has_hnf M ⇒ has_whnf M``,
  METIS_TAC [has_hnf_thm, head_reductions_have_weak_prefixes,
             has_whnf_def]);

val has_bnf_whnf = store_thm(
  "has_bnf_whnf",
  ``has_bnf M ⇒ has_whnf M``,
  METIS_TAC [has_bnf_hnf, has_hnf_whnf]);

(* Proposition 8.3.13 (i) [1, p.174] *)
Theorem has_hnf_LAM_E[simp] :
    !x M. has_hnf (LAM x M) <=> has_hnf M
Proof
    RW_TAC std_ss [has_hnf_def]
 >> reverse EQ_TAC (* easy goal first *)
 >> rpt STRIP_TAC
 >- (Q.EXISTS_TAC ‘LAM x N’ \\
     CONJ_TAC >- PROVE_TAC [lameq_rules] \\
     rw [hnf_cases])
 (* stage work *)
 >> ‘?Z. LAM x M -b->* Z /\ N -b->* Z’ by METIS_TAC [lameq_CR]
 >> ‘?N'. (Z = LAM x N') /\ M -b->* N'’ by rw [GSYM abs_betastar]
 >> Q.EXISTS_TAC ‘N'’
 >> ‘hnf Z’ by PROVE_TAC [hnf_preserved]
 >> gs [hnf_thm]
 >> MATCH_MP_TAC betastar_lameq >> art []
QED

(* Proposition 8.3.13 (ii) [1, p.174] *)
Theorem has_hnf_SUB_E :
    !M N z. has_hnf ([N/z] M) ==> has_hnf M
Proof
    rpt STRIP_TAC
 >> simp [corollary11_4_8, Once MONO_NOT_EQ]
 >> CCONTR_TAC
 >> Suff ‘infinite (head_reduction_path ([N/z] M))’
 >- (DISCH_TAC >> fs [corollary11_4_8])
 >> Q.PAT_X_ASSUM ‘has_hnf _’ K_TAC
 (* stage work *)
 >> ‘?l. ~LFINITE l /\ (LNTH 0 l = SOME M) /\
         !i. THE (LNTH i l) -h-> THE (LNTH (SUC i) l)’
      by METIS_TAC [infinite_head_reduction_path_to_llist]
 >> qabbrev_tac ‘ll = LMAP [N/z] l’
 >> rw [infinite_head_reduction_path_to_llist]
 >> Q.EXISTS_TAC ‘ll’
 >> rw [Abbr ‘ll’]
 >> Know ‘!i. THE (OPTION_MAP [N/z] (LNTH i l)) = [N/z] (THE (LNTH i l))’
 >- (Q.X_GEN_TAC ‘n’ \\
     Q.PAT_X_ASSUM ‘~LFINITE l’
       (STRIP_ASSUME_TAC o (Q.SPEC ‘n’) o (REWRITE_RULE [infinite_lnth_some])) \\
     rw [])
 >> Rewr
 >> MATCH_MP_TAC hreduce1_substitutive >> art []
QED

(* additionally, each list element has hnf: ‘EVERY has_hnf l’ *)
Theorem finite_head_reduction_path_to_list_every_has_hnf :
    !M. finite (head_reduction_path M) <=>
        ?l. l <> [] /\ (HD l = M) /\ hnf (LAST l) /\ EVERY has_hnf l /\
            !i. SUC i < LENGTH l ==> EL i l -h-> EL (SUC i) l
Proof
    rw [finite_head_reduction_path_to_list]
 >> reverse EQ_TAC >> rw []
 >> Q.EXISTS_TAC ‘l’ >> rw []
 >> rfs [LAST_EL]
 >> rw [EVERY_EL, corollary11_4_8, finite_head_reduction_path_to_list]
 >> Q.EXISTS_TAC ‘DROP n l’ >> rw [HD_DROP, LAST_EL, EL_DROP]
 >- (Know ‘n + PRE (LENGTH l - n) = PRE (LENGTH l)’
     >- (POP_ASSUM MP_TAC \\
         numLib.ARITH_TAC) >> DISCH_THEN (art o wrap))
 >> ‘n + SUC i = SUC (i + n)’ by rw [] >> POP_ORW
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> POP_ASSUM MP_TAC >> numLib.ARITH_TAC
QED

(* alternatively, the list is incomplete but the last element has hnf *)
Theorem finite_head_reduction_path_to_list_last_has_hnf :
    !M. finite (head_reduction_path M) <=>
        ?l. l <> [] /\ (HD l = M) /\ has_hnf (LAST l) /\
            !i. SUC i < LENGTH l ==> EL i l -h-> EL (SUC i) l
Proof
    Q.X_GEN_TAC ‘M’
 >> EQ_TAC
 >- (rw [finite_head_reduction_path_to_list_every_has_hnf] \\
    ‘0 < LENGTH l’ by rw [GSYM NOT_NIL_EQ_LENGTH_NOT_0] \\
     Q.EXISTS_TAC ‘l’ >> rw [LAST_EL] \\
     Q.PAT_X_ASSUM ‘EVERY has_hnf l’ MP_TAC >> rw [EVERY_EL])
 >> rw [finite_head_reduction_path_to_list]
 >> qabbrev_tac ‘M0 = LAST l’
 >> fs [corollary11_4_8, finite_head_reduction_path_to_list]
 >> ‘0 < LENGTH l /\ 0 < LENGTH l'’ by rw [GSYM NOT_NIL_EQ_LENGTH_NOT_0]
 >> ‘(LENGTH l' = 1) \/ 1 < LENGTH l'’ by rw []
 >- (‘LAST l' = HD l'’ by RW_TAC std_ss [GSYM EL, LAST_EL] \\
     Q.EXISTS_TAC ‘l’ >> rw [Abbr ‘M0’] >> PROVE_TAC [])
 (* stage work *)
 >> Q.EXISTS_TAC ‘l ++ TL l'’ >> rw []
 >| [ (* goal 1 (of 3) *)
      RW_TAC std_ss [GSYM EL, EL_APPEND_EQN],
      (* goal 2 (of 3) *)
      Suff ‘LAST (l ++ TL l') = LAST l'’ >- rw [] \\
     ‘l ++ TL l' <> []’ by rw [] \\
      Know ‘TL l' <> []’
      >- (CCONTR_TAC \\
         ‘LENGTH (TL l') = LENGTH ([] :term list)’ by PROVE_TAC [] \\
          REV_FULL_SIMP_TAC std_ss [LENGTH_TL] >> fs []) \\
      DISCH_TAC \\
      Know ‘LAST (l ++ TL l') = LAST (TL l')’
      >- (qabbrev_tac ‘l0 = TL l'’ \\
          Cases_on ‘l0’ >> rw [LAST_APPEND_CONS]) >> Rewr' \\
      rw [LAST_EL, LENGTH_TL] \\
      Cases_on ‘l'’ >> fs [] \\
      Induct_on ‘t’ >> fs [],
      (* goal 3 (of 3) *)
      Cases_on ‘SUC i < LENGTH l’ >> rw [EL_APPEND_EQN]
      >- (‘SUC i = LENGTH l’ by rw [] \\
          Know ‘EL i l = LAST l’
          >- (Q.PAT_X_ASSUM ‘LAST l = HD l'’ K_TAC \\
              rw [LAST_EL] \\
              Suff ‘PRE (LENGTH l) = i’ >- Rewr \\
              rw []) >> Rewr' \\
          rw [] \\
          REWRITE_TAC [GSYM EL] \\
          FIRST_X_ASSUM MATCH_MP_TAC >> rw []) \\
      REWRITE_TAC [GSYM EL] \\
     ‘SUC (SUC i - LENGTH l) = SUC (SUC (i - LENGTH l))’ by rw [] >> POP_ORW \\
      FIRST_X_ASSUM MATCH_MP_TAC >> gs [LENGTH_TL] ]
QED

(* Proposition 8.3.13 (iii) [1, p.174], cf. has_whnf_APP_E *)
Theorem has_hnf_APP_E :
    has_hnf (M @@ N) ==> has_hnf M
Proof
    rpt STRIP_TAC
 >> ‘finite (head_reduction_path (M @@ N))’ by rw [GSYM corollary11_4_8]
 (* this asserts a list ‘l’ *)
 >> FULL_SIMP_TAC std_ss [finite_head_reduction_path_to_list_every_has_hnf]
 (* Case 1: all APPs *)
 >> Cases_on ‘EVERY is_comb l’
 >- ((* Case 1.1: all non-LAM: M @@ N -h-> M1 @@ N -h-> M2 @@ N -h->* hnf @@ N *)
     Cases_on ‘EVERY (\e. ~is_abs (rator e)) l’
     >- (NTAC 2 (POP_ASSUM MP_TAC) >> rw [EVERY_MEM] \\
        ‘0 < LENGTH l’ by rw [GSYM NOT_NIL_EQ_LENGTH_NOT_0] \\
         Know ‘!i. SUC i < LENGTH l ==> rator (EL i l) -h-> rator (EL (SUC i) l)’
         >- (rpt STRIP_TAC \\
            ‘i < LENGTH l’ by rw [] \\
             qabbrev_tac ‘a = EL i l’ >> qabbrev_tac ‘b = EL (SUC i) l’ \\
             Know ‘a -h-> b’ >- PROVE_TAC [] \\
            ‘MEM a l /\ MEM b l’ by METIS_TAC [MEM_EL] \\
            ‘is_comb a /\ ~is_abs (rator a) /\ is_comb b’ by PROVE_TAC [] \\
            ‘?a1 a2 v. a = a1 @@ a2’ by METIS_TAC [is_comb_APP_EXISTS] \\
            ‘?b1 b2. b = b1 @@ b2’ by METIS_TAC [is_comb_APP_EXISTS] \\
             FULL_SIMP_TAC std_ss [rator_def] \\
             simp [Once hreduce1_cases] >> rw [] \\
             FULL_SIMP_TAC std_ss [is_abs_thm]) \\
         DISCH_TAC \\
      (* constructing a new head reduction list *)
         rw [corollary11_4_8, finite_head_reduction_path_to_list] \\
         qabbrev_tac ‘l0 = MAP rator l’ \\
        ‘(LENGTH l0 = LENGTH l) /\ l0 <> []’ by rw [Abbr ‘l0’] \\
         Q.EXISTS_TAC ‘l0’ >> RW_TAC std_ss [] >| (* 3 subgoals *)
         [ (* goal 1 (of 3) *)
           ASM_SIMP_TAC arith_ss [GSYM EL, EL_MAP, Abbr ‘l0’] >> rw [],
           (* goal 2 (of 3) *)
           rw [LAST_MAP, Abbr ‘l0’] \\
           Know ‘MEM (LAST l) l’
           >- (rw [LAST_EL, MEM_EL] \\
               Q.EXISTS_TAC ‘PRE (LENGTH l)’ >> rw []) >> DISCH_TAC \\
           qabbrev_tac ‘e = LAST l’ \\
          ‘is_comb e /\ ~is_abs (rator e)’ by PROVE_TAC [] \\
          ‘?u v. e = u @@ v’ by METIS_TAC [is_comb_APP_EXISTS] \\
           fs [], (* NOTE: ‘hnf (LAST l)’ is only used here *)
           (* goal 3 (of 3) *)
          ‘i < LENGTH l’ by rw [] \\
           rw [Abbr ‘l0’, EL_MAP] ]) \\
     (* Case 1.2: all APP, some LAM:

        M @@ N -h-> M1 @@ N -h->* (M2 = LAM v M') @@ N [EL n l] -h-> [N/v] M2' -h->* hnf
      *)
     FULL_SIMP_TAC std_ss [NOT_EVERY_EXISTS_FIRST] \\
     Q.PAT_X_ASSUM ‘EVERY is_comb l’ (STRIP_ASSUME_TAC o (REWRITE_RULE [EVERY_EL])) \\
    ‘?M2 N2. EL i l = M2 @@ N2’ by METIS_TAC [is_comb_APP_EXISTS] \\
     FULL_SIMP_TAC std_ss [rator_def] \\
     rename1 ‘EL n l = M2 @@ N2’ \\
     Know ‘!i. i < n ==> rator (EL i l) -h-> rator (EL (SUC i) l)’
     >- (rpt STRIP_TAC \\
        ‘SUC i < LENGTH l’ by rw [] \\
         qabbrev_tac ‘a = EL i l’ >> qabbrev_tac ‘b = EL (SUC i) l’ \\
         Know ‘a -h-> b’ >- PROVE_TAC [] \\
        ‘i < LENGTH l’ by rw [] \\
        ‘MEM a l /\ MEM b l’ by METIS_TAC [MEM_EL] \\
        ‘is_comb a /\ ~is_abs (rator a) /\ is_comb b’ by PROVE_TAC [] \\
        ‘?a1 a2. a = a1 @@ a2’ by METIS_TAC [is_comb_APP_EXISTS] \\
        ‘?b1 b2. b = b1 @@ b2’ by METIS_TAC [is_comb_APP_EXISTS] \\
         FULL_SIMP_TAC std_ss [rator_def] \\
         simp [Once hreduce1_cases] >> rw [] \\
         FULL_SIMP_TAC std_ss [is_abs_thm]) \\
     DISCH_TAC \\
     (* Case 1.2.1: first LAM is last element in the list *)
    ‘(n = PRE (LENGTH l)) \/ n < PRE (LENGTH l)’ by rw [] (* cf. LAST_EL *)
     >- (‘LAST l = EL n l’ by rw [LAST_EL] \\
         ‘hnf (M2 @@ N2)’ by PROVE_TAC [] \\
         ‘hnf M2’ by PROVE_TAC [hnf_thm] \\
      (* constructing a new head reduction list *)
         rw [corollary11_4_8, finite_head_reduction_path_to_list] \\
         qabbrev_tac ‘l0 = MAP rator l’ \\
        ‘(LENGTH l0 = LENGTH l) /\ l0 <> []’ by rw [Abbr ‘l0’] \\
         Q.EXISTS_TAC ‘l0’ >> RW_TAC std_ss [] >| (* 3 subgoals *)
         [ (* goal 1 (of 3) *)
           ASM_SIMP_TAC arith_ss [GSYM EL, EL_MAP, Abbr ‘l0’] >> rw [],
           (* goal 2 (of 3) *)
           rw [LAST_MAP, Abbr ‘l0’],
           (* goal 3 (of 3) *)
          ‘i < LENGTH l’ by rw [] \\
           rw [Abbr ‘l0’, EL_MAP] ]) \\
    ‘SUC n < LENGTH l’ by rw [] \\
     qabbrev_tac ‘a = EL n l’ >> qabbrev_tac ‘b = EL (SUC n) l’ \\
     Know ‘a -h-> b’ >- PROVE_TAC [] \\
     DISCH_THEN (MP_TAC o (ONCE_REWRITE_RULE [hreduce1_cases])) >> rw [] \\
     Know ‘has_hnf ([N2/v] M')’
     >- (POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM) \\
         Q.PAT_X_ASSUM ‘EVERY has_hnf l’ MP_TAC \\
         rw [EVERY_EL]) >> DISCH_TAC \\
    ‘has_hnf M'’ by PROVE_TAC [has_hnf_SUB_E] \\
     qabbrev_tac ‘M2 = LAM v M'’ \\
    ‘has_hnf M2’ by METIS_TAC [has_hnf_LAM_E] \\
     Cases_on ‘n = 0’ >- gs [] \\
  (* constructing a new head reduction list *)
     rw [Once corollary11_4_8, Once finite_head_reduction_path_to_list_last_has_hnf] \\
     qabbrev_tac ‘l0 = MAP rator l’ \\
    ‘(LENGTH l0 = LENGTH l) /\ l0 <> []’ by rw [Abbr ‘l0’] \\
    ‘0 < LENGTH l /\ 0 < LENGTH l0’ by rw [GSYM NOT_NIL_EQ_LENGTH_NOT_0] \\
     Q.EXISTS_TAC ‘TAKE (SUC n) l0’ \\
     Know ‘LENGTH (TAKE (SUC n) l0) = SUC n’
     >- (MATCH_MP_TAC LENGTH_TAKE >> rw []) >> DISCH_TAC \\
    ‘0 < LENGTH (TAKE (SUC n) l0)’ by rw [] \\
     rw [NOT_NIL_EQ_LENGTH_NOT_0] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       RW_TAC arith_ss [GSYM EL, EL_TAKE, Abbr ‘l0’, EL_MAP] \\
       fs [EL],
       (* goal 2 (of 3) *)
       rw [LAST_EL, EL_TAKE, Abbr ‘l0’, EL_MAP],
       (* goal 3 (of 3) *)
       rw [EL_TAKE, Abbr ‘l0’, EL_MAP] ])
 (* case 2: some non-APP (LAM or VAR)

    NOTE: 1) the first one (M @@ N) is always APP; 2) All but the last one can
    be VAR (because any VAR is already hnf).

    1. M @@ N -h-> M1 @@ N1 -h->* M2 @@ N2 -h-> VAR (is hnf, the last element)
    2. M @@ N -h-> M1 @@ N1 -h->* M2 @@ N2 -h-> LAM v P -h->* hnf

    Now there must be at last one LAM in M, M1, M2, ... before reaching VAR/LAM.
  *)
 >> FULL_SIMP_TAC std_ss [NOT_EVERY_EXISTS_FIRST]
 >> rename1 ‘n < LENGTH l’
 >> ‘(n = 0) \/ 0 < n’ by rw [] >- gs [EL] (* NOTE: ‘TAKE 0 n = []’ *)
 (* impossible case *)
 >> Cases_on ‘EVERY (\e. ~is_abs (rator e)) (TAKE n l)’
 >- (POP_ASSUM MP_TAC >> rw [EVERY_EL, EL_TAKE] \\
    ‘0 < LENGTH l’ by rw [GSYM NOT_NIL_EQ_LENGTH_NOT_0] \\
    ‘n - 1 < LENGTH l’ by rw [] \\
     qabbrev_tac ‘a = EL (n - 1) l’ \\
     qabbrev_tac ‘b = EL n l’ \\
     Know ‘a -h-> b’
     >- (rw [Abbr ‘a’, Abbr ‘b’] \\
         qabbrev_tac ‘j = n - 1’ >> ‘n = SUC j’ by rw [Abbr ‘j’] >> POP_ORW \\
         FIRST_X_ASSUM MATCH_MP_TAC >> rw [Abbr ‘j’]) \\
    ‘is_comb a’ by rw [Abbr ‘a’] \\
    ‘n - 1 < n’ by rw [] \\
    ‘~is_abs (rator a)’ by PROVE_TAC [] \\
    ‘?a1 a2. a = a1 @@ a2’ by METIS_TAC [is_comb_APP_EXISTS] \\
     FULL_SIMP_TAC std_ss [rator_def] \\
     simp [Once hreduce1_cases] >> rw [] >> fs [])
 (* stage work *)
 >> ‘LENGTH (TAKE n l) = n’ by rw [LENGTH_TAKE]
 >> gs [NOT_EVERY_EXISTS_FIRST, EL_TAKE]
 >> Know ‘!j. j < i ==> rator (EL j l) -h-> rator (EL (SUC j) l)’
 >- (rpt STRIP_TAC \\
    ‘SUC j < LENGTH l’ by rw [] \\
     qabbrev_tac ‘a = EL j l’ >> qabbrev_tac ‘b = EL (SUC j) l’ \\
     Know ‘a -h-> b’ >- PROVE_TAC [] \\
    ‘j < LENGTH l’ by rw [] \\
    ‘j < n /\ SUC j < n’ by rw [] \\
    ‘is_comb a /\ ~is_abs (rator a) /\ is_comb b’ by PROVE_TAC [] \\
    ‘?a1 a2. a = a1 @@ a2’ by METIS_TAC [is_comb_APP_EXISTS] \\
    ‘?b1 b2. b = b1 @@ b2’ by METIS_TAC [is_comb_APP_EXISTS] \\
     FULL_SIMP_TAC std_ss [rator_def] \\
     simp [Once hreduce1_cases] >> rw [] \\
     FULL_SIMP_TAC std_ss [is_abs_thm])
 >> DISCH_TAC
 >> ‘SUC i < LENGTH l’ by rw []
 >> qabbrev_tac ‘a = EL i l’ >> qabbrev_tac ‘b = EL (SUC i) l’
 >> Know ‘a -h-> b’ >- PROVE_TAC []
 >> ‘is_comb a’ by METIS_TAC []
 >> ‘?a1 a2. a = a1 @@ a2’ by METIS_TAC [is_comb_APP_EXISTS]
 >> FULL_SIMP_TAC std_ss [rator_def]
 >> simp [Once hreduce1_cases] >> rw []
 >> rename1 ‘EL (SUC i) l = [N2/v] M'’
 >> Know ‘has_hnf ([N2/v] M')’
 >- (Q.PAT_X_ASSUM ‘_ = [N2/v] M'’ (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM ‘EVERY has_hnf l’ MP_TAC \\
     rw [EVERY_EL])
 >> DISCH_TAC
 >> ‘has_hnf M'’ by PROVE_TAC [has_hnf_SUB_E]
 >> qabbrev_tac ‘M2 = LAM v M'’
 >> ‘has_hnf M2’ by METIS_TAC [has_hnf_LAM_E]
 >> Cases_on ‘i = 0’ >- gs []
 (* constructing a new head reduction list *)
 >> rw [Once corollary11_4_8, Once finite_head_reduction_path_to_list_last_has_hnf]
 >> qabbrev_tac ‘l0 = MAP rator l’
 >> ‘(LENGTH l0 = LENGTH l) /\ l0 <> []’ by rw [Abbr ‘l0’]
 >> ‘0 < LENGTH l /\ 0 < LENGTH l0’ by rw [GSYM NOT_NIL_EQ_LENGTH_NOT_0]
 >> Q.EXISTS_TAC ‘TAKE (SUC i) l0’
 >> Know ‘LENGTH (TAKE (SUC i) l0) = SUC i’
 >- (MATCH_MP_TAC LENGTH_TAKE >> rw [])
 >> DISCH_TAC
 >> ‘0 < LENGTH (TAKE (SUC i) l0)’ by rw []
 >> rw [NOT_NIL_EQ_LENGTH_NOT_0] (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      RW_TAC arith_ss [GSYM EL, EL_TAKE, Abbr ‘l0’, EL_MAP] >> fs [EL],
      (* goal 2 (of 3) *)
      rw [LAST_EL, EL_TAKE, Abbr ‘l0’, EL_MAP],
      (* goal 3 (of 3) *)
      rw [EL_TAKE, Abbr ‘l0’, EL_MAP] ]
QED

val _ = export_theory()
val _ = html_theory "standardisation";

(* References:

   [1] Barendregt, H.P.: The Lambda Calculus, Its Syntax and Semantics.
       College Publications, London (1984).
 *)
