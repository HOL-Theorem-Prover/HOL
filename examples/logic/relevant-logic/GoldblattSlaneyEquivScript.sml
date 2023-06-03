open HolKernel Parse boolLib bossLib stringTheory;

open SlaneyRLTheory GoldblattRLTheory;

val _ = new_theory "GoldblattSlaneyEquiv";

Definition sg_translation_def:
  (sg_translation (s_VAR A) = g_VAR A) ∧
  (sg_translation (A -->ₛ B) = sg_translation A -->ₐ sg_translation B) ∧
  (sg_translation (A &ₛ B) = sg_translation A &ₐ sg_translation B) ∧
  (sg_translation (A Vₛ B) = sg_translation A Vₐ sg_translation B) ∧
  (sg_translation (A ioₛ B) = sg_translation A ioₐ sg_translation B) ∧
  (sg_translation (~ₛ A) = ~ₐ (sg_translation A)) ∧
  (sg_translation τₛ = τₐ)
End

Definition gs_translation_def:
  (gs_translation (g_VAR A) = s_VAR A) ∧
  (gs_translation (A -->ₐ B) = gs_translation A -->ₛ gs_translation B) ∧
  (gs_translation (A &ₐ B) = gs_translation A &ₛ gs_translation B) ∧
  (gs_translation (~ₐ A) = ~ₛ (gs_translation A)) ∧
  (gs_translation τₐ = τₛ)
End

val _ = overload_on ("sg", “sg_translation”);
val _ = overload_on ("gs", “gs_translation”);

Theorem gs_sg_equiv:
  ∀A. slaney_provable (A <->ₛ (gs $ sg A))
Proof
  Induct >> rpt strip_tac
  >- gs[gs_translation_def, sg_translation_def, s_equiv_identity]
  >- gs[gs_translation_def, sg_translation_def, s_double_dimp_equiv]
  >- gs[gs_translation_def, sg_translation_def, s_double_dimp_equiv]
  >- (gs[gs_translation_def, sg_translation_def, g_OR_def] >>
      rename[‘slaney_provable ((A Vₛ B) <->ₛ _)’] >>
      assume_tac s_OR_definable >>
      last_x_assum $ qspecl_then [‘gs $ sg A’, ‘gs $ sg B’] strip_assume_tac >>
      ‘slaney_provable ((A Vₛ B) <->ₛ (gs $ sg A) Vₛ (gs $ sg B))’ suffices_by
        metis_tac[s_equiv_symmetry, s_equiv_transitivity] >>
      gs[s_double_dimp_equiv])
  >- (gs[gs_translation_def, sg_translation_def, g_ICONJ_def] >>
      rename[‘slaney_provable ((A ioₛ B) <->ₛ _)’] >>
      assume_tac s_IO_definable >>
      last_x_assum $ qspecl_then [‘gs $ sg A’, ‘gs $ sg B’] strip_assume_tac >>
      ‘slaney_provable ((A ioₛ B) <->ₛ (gs $ sg A) ioₛ (gs $ sg B))’ suffices_by
        metis_tac[s_equiv_symmetry, s_equiv_transitivity] >>
      gs[s_double_dimp_equiv])
  >- (gs[gs_translation_def, sg_translation_def] >> metis_tac[s_equiv_replacement, s_DIMP_def, slaney_provable_rules])
  >- simp[s_equiv_identity, gs_translation_def, sg_translation_def]
QED

Theorem sg_gs_EQ:
  ∀A. sg $ gs A = A
Proof
  Induct_on ‘A’ >> simp[gs_translation_def, sg_translation_def]
QED


Theorem g_trans_invarient:
  ∀A. goldblatt_provable $ sg $ gs A ⇔ goldblatt_provable A
Proof
  simp[sg_gs_EQ]
QED

Theorem s_trans_invarient:
  ∀A. slaney_provable $ gs $ sg A ⇔ slaney_provable A
Proof
  metis_tac[s_equiv_replacement, gs_sg_equiv]
QED

Theorem goldblatt_implies_slaney:
  ∀A. goldblatt_provable A ⇒ slaney_provable $ gs A
Proof
  Induct_on ‘goldblatt_provable’ >> rpt strip_tac >> gs[gs_translation_def, g_OR_def, slaney_provable_rules, s_assertion, s_disjunction_OR_def]
  >- metis_tac[slaney_provable_rules]
  >- metis_tac[slaney_provable_rules, s_assertion, s_OR_definable, s_equiv_replacement, s_disjunction_OR_def]
  >- metis_tac[s_equiv_replacement, s_OR_definable, s_disjunction_elim]
  >- metis_tac[slaney_provable_rules]
QED

Theorem slaney_implies_goldblatt:
  ∀A. slaney_provable A ⇒ goldblatt_provable $ sg A
Proof
  Induct_on ‘slaney_provable ’ >> rpt strip_tac >> gs [sg_translation_def] >>
  metis_tac[goldblatt_provable_rules, g_permutation, g_io_rule]
QED

Theorem goldblatt_slaney_equiv:
  ∃ s g. ∀A B. (goldblatt_provable A ⇒ slaney_provable $ s A) ∧
               (slaney_provable B ⇒ goldblatt_provable $ g B) ∧
               (goldblatt_provable $ g $ s A ⇔ goldblatt_provable A) ∧
               (slaney_provable $ s $ g B ⇔ slaney_provable B)
Proof
  qexistsl_tac [‘gs’, ‘sg’] >>
  metis_tac[slaney_implies_goldblatt,
            goldblatt_implies_slaney,
            s_trans_invarient,
            g_trans_invarient]
QED

val _ = export_theory();
