open HolKernel Parse boolLib bossLib;
open binderLib

open pred_setTheory
open termTheory chap2Theory chap3Theory
val _ = new_theory "chap4";

val _ = hide "B"

(* definition 4.1.1(i) is already in chap2, given name asmlam *)

Definition lambdathy_def:
  lambdathy A ⇔ consistent (asmlam A) ∧ UNCURRY (asmlam A) = A
End

Definition church1_def:
  church1 = LAM "x" (LAM "y" (VAR "x" @@ VAR "y"))
End

Overload "𝟙" = “church1”


Overload "TC" = “asmlam”

Overload "eta_extend" = “λA. asmlam (UNCURRY eta ∪ A)”
val _ = set_mapped_fixity {tok = UTF8.chr 0x1D73C, fixity = Suffix 2100,
                           term_name = "eta_extend"}


Theorem lameta_subset_eta_extend:
  ∀M N. lameta M N ⇒ 𝒯 𝜼 M N
Proof
  Induct_on ‘lameta’ >>
  rw[asmlam_refl, asmlam_beta, asmlam_lcong, asmlam_rcong, asmlam_abscong] >~
  [‘_ 𝜼 M N’, ‘_ 𝜼 N M’] >- metis_tac[asmlam_sym] >~
  [‘_ 𝜼 (LAM v (M @@ VAR v)) M’]
  >- (irule asmlam_eqn >> simp[eta_def] >> metis_tac[]) >>
  metis_tac[asmlam_trans]
QED

Theorem asmlam_equality:
  asmlam A = asmlam B ⇔
    (∀a1 a2. (a1,a2) ∈ A ⇒ asmlam B a1 a2) ∧
    (∀b1 b2. (b1,b2) ∈ B ⇒ asmlam A b1 b2)
Proof
  iff_tac
  >- (simp[] >> rw[] >~
      [‘A⁺ = B⁺’, ‘(a1,a2) ∈ A’]
      >- (‘A⁺ a1 a2’ suffices_by simp[] >> simp[asmlam_eqn]) >>
      simp[asmlam_eqn]) >>
  strip_tac >> simp[FUN_EQ_THM, EQ_IMP_THM, FORALL_AND_THM] >> conj_tac >>
  Induct_on ‘asmlam’ >>
  rw[asmlam_beta, asmlam_refl, asmlam_lcong, asmlam_rcong, asmlam_abscong] >>
  metis_tac[asmlam_sym, asmlam_trans]
QED

Theorem eta_alt:
  FINITE X ⇒ (η M N ⇔ ∃v. v ∉ X ∧ v # N ∧ M = LAM v (N @@ VAR v))
Proof
  simp[EQ_IMP_THM, eta_def] >> rw[]
  >- (simp[LAM_eq_thm, SF DNF_ss, SF CONJ_ss, tpm_fresh] >>
      Q_TAC (NEW_TAC "z") ‘{v} ∪ FV N ∪ X’ >> metis_tac[]) >>
  simp[LAM_eq_thm, SF CONJ_ss, tpm_fresh, SF SFY_ss]
QED

Theorem lemma4_1_5:
  ((I,𝟙) INSERT 𝒯)⁺ = 𝒯 𝜼
Proof
  simp[asmlam_equality] >> rw[]
  >- (irule lameta_subset_eta_extend >>
      simp[church1_def, I_def] >> irule lameta_SYM >>
      irule lameta_ABS >> irule lameta_ETA >> simp[]) >>
  simp[asmlam_eqn] >>
  ‘FINITE {"x"; "y"}’ by simp[] >>
  dxrule_then assume_tac eta_alt >> gvs[] >>
  rename [‘_⁺ (LAM v (M @@ VAR v)) M’] >>
  qmatch_abbrev_tac ‘A⁺ _ _’ >>
  ‘A⁺ (LAM v (M @@ VAR v)) (𝟙 @@ M)’
    by (‘A⁺ (𝟙 @@ M) ([M/"x"] (LAM "y" (VAR "x" @@ VAR "y")))’
          by simp[asmlam_beta, church1_def] >>
        Q_TAC (NEW_TAC "z") ‘FV M ∪ {"x"; "y"}’ >>
        ‘LAM "y" (VAR "x" @@ VAR "y") = LAM z ([VAR z/"y"](VAR "x" @@ VAR "y"))’
          by simp[SIMPLE_ALPHA] >>
        gs[SUB_THM] >>
        ‘LAM z (M @@ VAR z) = LAM v (M @@ VAR v)’
          suffices_by metis_tac[asmlam_sym] >>
        simp[LAM_eq_thm, SF CONJ_ss, tpm_fresh]) >>
  ‘A⁺ (𝟙 @@ M) (I @@ M)’
    by (irule asmlam_lcong  >> simp[Abbr‘A’] >>
        metis_tac[asmlam_sym, asmlam_eqn, IN_INSERT]) >>
  dxrule_all_then assume_tac asmlam_trans >>
  ‘A⁺ (I @@ M) M’ suffices_by metis_tac[asmlam_trans] >>
  simp[lameq_asmlam, lameq_I]
QED

(* Barendregt def'n 4.1.6(i) *)
Definition K0_def:
  K0 = { (M,N) | unsolvable M ∧ unsolvable N ∧ closed M ∧ closed N }
End

Overload "𝒦₀" = “K0”

Definition Kthy_def:
  Kthy = { (M,N) | asmlam K0 M N }
End
Overload "𝒦" = “Kthy”

(* Barendregt def'n 4.1.7(ii) *)
Definition sensible_def:
  sensible 𝒯 ⇔ lambdathy 𝒯 ∧ 𝒦 ⊆ 𝒯
End

(* Barendregt def'n 4.1.7(iii) *)
Definition semisensible_def:
  semisensible 𝒯 ⇔ ∀M N. 𝒯⁺ M N ⇒ ¬(unsolvable M ∧ solvable N)
End

val Kfp_def =
  new_specification ("Kfp_def", ["Kfp"], SPEC “K:term” fixed_point_thm);

Overload "K∞" = “Kfp”

Theorem FV_Kfp[simp]:
  FV Kfp = {}
Proof
  simp[Kfp_def]
QED

Theorem Kfp_thm:
  Kfp @@ x == Kfp
Proof
  strip_assume_tac Kfp_def >>
  dxrule_then (qspec_then ‘x’ assume_tac) lameq_APPL >>
  dxrule_then assume_tac lameq_SYM >> irule lameq_TRANS >>
  first_x_assum $ irule_at Any >> simp[lameq_K]
QED

Theorem KfpI:
  𝒯⁺ I Kfp ⇒ inconsistent 𝒯⁺
Proof
  strip_tac >> simp[inconsistent_def] >>
  qx_genl_tac [‘M’, ‘N’] >>
  qmatch_abbrev_tac ‘A M N’ >>
  ‘∀P. A P Kfp’
    suffices_by (strip_tac >> simp[Abbr‘A’] >>
                 metis_tac[asmlam_trans, asmlam_sym]) >>
  qx_gen_tac ‘P’ >>
  ‘A P (I @@ P)’
    by (simp[Abbr‘A’] >> metis_tac[asmlam_sym, lameq_asmlam, lameq_I]) >>
  ‘A (I @@ P) (Kfp @@ P)’
    by (simp[Abbr‘A’] >> metis_tac[asmlam_lcong, IN_INSERT, asmlam_eqn]) >>
  ‘∀x y z. A x y ∧ A y z ⇒ A x z’ by metis_tac[asmlam_trans] >>
  first_assum $ dxrule_all_then assume_tac >>
  first_x_assum irule >> pop_assum $ irule_at Any >>
  simp[Abbr‘A’, lameq_asmlam, Kfp_thm]
QED

Theorem asmlam_EMPTY:
  asmlam {} = $==
Proof
  simp[FUN_EQ_THM, EQ_IMP_THM, lameq_asmlam] >>
  Induct_on ‘asmlam’ >> metis_tac[lameq_rules, NOT_IN_EMPTY]
QED

Theorem Kfp_unsolvable[simp]:
  unsolvable Kfp
Proof
  simp[solvable_alt_closed, closed_def] >>
  Induct >> simp[]
  >- (strip_tac >> gvs[GSYM asmlam_EMPTY] >>
      dxrule_then assume_tac asmlam_sym >> drule KfpI >>
      simp[asmlam_EMPTY, lameq_consistent]) >>
  rpt strip_tac >>
  resolve_then Any assume_tac Kfp_thm lameq_appstar_cong >>
  metis_tac[lameq_SYM, lameq_TRANS]
QED

Theorem lemma4_1_8i:
  I # Kfp
Proof
  simp[incompatible_def, KfpI, asmlam_eqn]
QED

(* argument seems to rely on solvable (LAM v t) ⇔ solvable t, which is proved
   in chapter 8, suggesting all of this stuff should move to a mechanisation of
   chapter 16
Theorem corollary4_1_19:
  sensible 𝒯 ⇒ semisensible 𝒯
Proof
  simp[sensible_def, semisensible_def] >> CCONTR_TAC >> gvs[] >>
  rename [‘solvable M’, ‘unsolvable N’, ‘𝒯⁺ N M’] >>
  wlog_tac ‘closed M ∧ closed N’ [‘M’,‘N’]
  >- (gvs[]
      >- (first_x_assum $ qspecl_then [‘closure M’, ‘closure N’] mp_tac >>
          simp[]
  qpat_x_assum ‘solvable M’ mp_tac >> simp[solvable_def] >>
  qx_genl_tac [‘M'’, ‘Ps’] >> Cases_on ‘M' ·· Ps == I’ >> simp[] >>
  simp[closures_def] >> qx_gen_tac ‘vs’ >> rpt strip_tac >>
QED
*)



val _ = export_theory();
