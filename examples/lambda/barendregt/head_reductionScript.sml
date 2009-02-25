open HolKernel Parse boolLib bossLib

open chap3Theory pred_setTheory termTheory boolSimps

val _ = new_theory "head_reduction"

val _ = set_trace "Unicode" 1

val (hreduce1_rules, hreduce1_ind, hreduce1_cases) = Hol_reln`
  (∀v M N. hreduce1 (LAM v M @@ N) ([N/v]M)) ∧
  (∀v M1 M2. hreduce1 M1 M2 ⇒ hreduce1 (LAM v M1) (LAM v M2)) ∧ 
  (∀M1 M2 N. hreduce1 M1 M2 ∧ ¬is_abs M1 ⇒ hreduce1 (M1 @@ N) (M2 @@ N))
`;

val _ = set_fixity "-h->" (Infix(NONASSOC, 450))
val _ = overload_on ("-h->", ``hreduce1``)

val _ = set_fixity "-h->*" (Infix(NONASSOC, 450))
val _ = overload_on ("-h->*", ``hreduce1^*``)

val hreduce_ccbeta = store_thm(
  "hreduce_ccbeta",
  ``∀M N. M -h-> N ⇒ compat_closure beta M N``,
  HO_MATCH_MP_TAC hreduce1_ind THEN SRW_TAC [][cc_beta_thm] THEN 
  METIS_TAC []);

val hreduce1_FV = store_thm(
  "hreduce1_FV",
  ``∀M N. M -h-> N ⇒ ∀v. v ∈ FV N ⇒ v ∈ FV M``,
  METIS_TAC [SUBSET_DEF, hreduce_ccbeta, cc_beta_FV_SUBSET]);


val _ = temp_add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT,2)),
                       fixity = Infix(NONASSOC, 950),
                       paren_style = OnlyIfNecessary,
                       pp_elements = [TOK "·", BreakSpace(0,0)],
                       term_name = "apply_perm"}
val _ = temp_overload_on ("apply_perm", ``λp M. tpm [p] M``)
val _ = temp_overload_on ("apply_perm", ``tpm``)
val _ = temp_overload_on ("#", ``λv t. v ∉ FV t``)
val _ = temp_set_fixity "#" (Infix(NONASSOC, 450))

val tpm_hreduce_I = store_thm(
  "tpm_hreduce_I",
  ``∀M N. M -h-> N ⇒ ∀π. π·M -h-> π·N``,
  HO_MATCH_MP_TAC hreduce1_ind THEN SRW_TAC [][tpm_subst, hreduce1_rules]);

val tpm_hreduce = store_thm(
  "tpm_hreduce",
  ``∀M N π. π·M -h-> π·N ⇔ M -h-> N``,
  METIS_TAC [tpm_inverse, tpm_hreduce_I]);

val hreduce1_rwts = store_thm(
  "hreduce1_rwts",
  ``(VAR s -h-> M ⇔ F) ∧
    (¬is_abs M ⇒ (M @@ N -h-> P ⇔ ∃M'. (P = M' @@ N) ∧ M -h-> M')) ∧
    (LAM v M -h-> N ⇔ ∃M'. (N = LAM v M') ∧ M -h-> M') ∧
    (LAM v M @@ N -h-> P ⇔ (P = [N/v]M))``,
  REPEAT STRIP_TAC THENL [
    SRW_TAC [][Once hreduce1_cases],
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [hreduce1_cases])) THEN 
    SRW_TAC [][] THEN 
    Q_TAC SUFF_TAC `∀v N. M ≠ LAM v N` THEN1 METIS_TAC [] THEN 
    SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN 
    FULL_SIMP_TAC (srw_ss()) [],
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [hreduce1_cases])) THEN 
    SRW_TAC [DNF_ss][LAM_eq_thm, tpm_eqr] THEN EQ_TAC THEN 
    SRW_TAC [][] THEN1 SRW_TAC [][] THEN
    Q.EXISTS_TAC `(v,v')·M2` THEN 
    SRW_TAC [][] THENL [
      `v # (v,v')·M` by SRW_TAC [][] THEN 
      `v # M2` by METIS_TAC [hreduce1_FV] THEN 
      SRW_TAC [][GSYM tpm_ALPHA],

      METIS_TAC [tpm_sing_inv, tpm_hreduce_I]
    ],

    SRW_TAC [DNF_ss][Once hreduce1_cases, LAM_eq_thm] THEN 
    SRW_TAC [][EQ_IMP_THM, tpm_eqr] THEN 
    METIS_TAC [lemma15a, tpm_flip_args, fresh_tpm_subst]
  ]);

val hnf_def = Define`hnf M = ∀N. ¬(M -h-> N)`;
val hnf_thm = store_thm(
  "hnf_thm",
  ``(hnf (VAR s) ⇔ T) ∧
    (hnf (M @@ N) ⇔ hnf M ∧ ¬is_abs M) ∧
    (hnf (LAM v M) ⇔ hnf M)``,
  SRW_TAC [][hnf_def, hreduce1_rwts] THEN 
  Cases_on `is_abs M` THEN SRW_TAC [][hreduce1_rwts] THEN 
  Q.SPEC_THEN `M` FULL_STRUCT_CASES_TAC term_CASES THEN 
  FULL_SIMP_TAC (srw_ss()) [hreduce1_rwts]);
val _ = export_rewrites ["hnf_thm"]

val hnf_tpm = store_thm(
  "hnf_tpm",
  ``∀M π. hnf (π·M) = hnf M``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][]);
val _ = export_rewrites ["hnf_tpm"]


val _ = set_trace "Unicode" 0

val _ = export_theory()
