Theory IntuitionisticHilbert
(* Inspired by Sonia Marin's presentation of this material at the
   ANU Logic Summer School, December 2025
*)

Ancestors
  hol string pred_set finite_map ipropSyntax

val _ = set_mapped_fixity {
  term_name = "ded", tok = "⊢ⁱ", fixity = Infix(NONASSOC,450)
}

Inductive ded:
[PLK:]
  Γ ⊢ⁱ a ⇒ⁱ (b ⇒ⁱ a)
[PLS:]
  Γ ⊢ⁱ (a ⇒ⁱ (b ⇒ⁱ c)) ⇒ⁱ ((a ⇒ⁱ b) ⇒ⁱ (a ⇒ⁱ c))
[conjE1:]
  Γ ⊢ⁱ a ∧ⁱ b ⇒ⁱ a
[conjE2:]
  Γ ⊢ⁱ a ∧ⁱ b ⇒ⁱ b
[conjI:]
  Γ ⊢ⁱ a ⇒ⁱ b ⇒ⁱ a ∧ⁱ b
[disjI1:]
  Γ ⊢ⁱ (a ⇒ⁱ (a ∨ⁱ b))
[disjI2:]
  Γ ⊢ⁱ (b ⇒ⁱ (a ∨ⁱ b))
[disjE:]
  Γ ⊢ⁱ (a ⇒ⁱ c) ⇒ⁱ ((b ⇒ⁱ c) ⇒ⁱ (a ∨ⁱ b ⇒ⁱ c))
[exFalso:]
  Γ ⊢ⁱ ⊥ⁱ ⇒ⁱ a
[~hyp:]
  a ∈ Γ ⇒ Γ ⊢ⁱ a
[~mp:]
  Γ ⊢ⁱ a ⇒ⁱ b ∧ Γ ⊢ⁱ a ⇒ Γ ⊢ⁱ b
End

Theorem id:
  Γ ⊢ⁱ a ⇒ⁱ a
Proof
  metis_tac[ded_rules]
QED

Theorem deductionRL:
  (a INSERT Γ) ⊢ⁱ b ⇒ Γ ⊢ⁱ a ⇒ⁱ b
Proof
  Induct_on ‘ded’ >> rw[] >> simp[id] >~
  [‘ded Γ _ (* a *)’, ‘ded (a INSERT Γ) _ (* a *)’]
  >- (resolve_then (Pos hd) mp_tac PLS ded_mp >>
      disch_then $ dxrule_then assume_tac >>
      metis_tac[ded_mp]) >>
  irule ded_mp >> irule_at (Pat ‘ded _ (_ ⇒ⁱ _)’) PLK >>
  simp[ded_rules]
QED

Theorem weakening:
  Γ ⊢ⁱ ϕ ∧ Γ ⊆ Δ ⇒ Δ ⊢ⁱ ϕ
Proof
  Induct_on ‘ded’ >> rpt strip_tac >> gvs[ded_rules] >>
  metis_tac[ded_mp, SUBSET_DEF, ded_hyp]
QED

Theorem deductionLR:
  Γ ⊢ⁱ a ⇒ⁱ b ⇒ (a INSERT Γ) ⊢ⁱ b
Proof
  strip_tac >> irule ded_mp >>
  drule_then (irule_at (Pat ‘ded _ (_ ⇒ⁱ _)’)) weakening >>
  simp[ded_hyp, SUBSET_DEF]
QED

Theorem deduction_iff:
  Γ ⊢ⁱ (a ⇒ⁱ b) ⇔ (a INSERT Γ) ⊢ⁱ b
Proof
  metis_tac[deductionLR, deductionRL]
QED

Theorem instantiation:
  ∀ϕ. Γ ⊢ⁱ ϕ ⇒ ∀σ. IMAGE (subst σ) Γ ⊢ⁱ subst σ ϕ
Proof
  Induct_on ‘ded’ >> rw[] >> simp[ded_rules] >>
  metis_tac[ded_rules]
QED



(* lift axioms into inference rules; also provide MP with weakening *)
Theorem ded_MP:
  Γ₁ ⊢ⁱ p ⇒ⁱ q ∧ Γ₂ ⊢ⁱ p ⇒ Γ₁ ∪ Γ₂ ⊢ⁱ q
Proof
  strip_tac >> irule ded_mp >>
  irule_at (Pat ‘_ ⊢ⁱ _ ⇒ⁱ _’) weakening >>
  first_assum $ irule_at (Pat ‘_ ⊢ⁱ _ ⇒ⁱ _’) >> simp[] >>
  irule weakening >> first_assum $ irule_at Any >> simp[]
QED

Theorem disj1_I:
  Γ ⊢ⁱ p ⇒ Γ ⊢ⁱ p ∨ⁱ q
Proof
  strip_tac >> irule ded_mp >> first_assum $ irule_at Any >>
  simp[disjI1]
QED

Theorem disj2_I:
  Γ ⊢ⁱ q ⇒ Γ ⊢ⁱ p ∨ⁱ q
Proof
  strip_tac >> irule ded_mp >> first_assum $ irule_at Any >>
  simp[disjI2]
QED

Theorem disj_E:
  Γ ⊢ⁱ p ∨ⁱ q ∧ p INSERT Γ ⊢ⁱ r ∧ q INSERT Γ ⊢ⁱ r ⇒ Γ ⊢ⁱ r
Proof
  strip_tac >>
  resolve_then (Pos hd) mp_tac disjE ded_mp >>
  disch_then (fn th => resolve_then (Pos hd) mp_tac th ded_mp) >>
  disch_then (fn th => resolve_then (Pos hd) mp_tac th ded_mp) >>
  simp[deduction_iff] >> disch_then dxrule_all >> simp[]
QED

Theorem conj_I:
  Γ ⊢ⁱ p ∧ Γ ⊢ⁱ q ⇒ Γ ⊢ⁱ p ∧ⁱ q
Proof
  strip_tac >> resolve_then (Pos hd) mp_tac conjI ded_mp >>
  disch_then $ C (resolve_then (Pos hd) mp_tac) ded_mp >>
  simp[]
QED

Theorem example2:
  Γ ⊢ⁱ p ∨ⁱ ⊤
Proof
  simp[deduction_iff, ded_hyp, disj2_I]
QED

(* from classical to intuitionistic; needs linking to a classical
   presentation
Definition negtrans_def:
  negtrans (CVar p) = ineg (ineg p) ∧
  negtrans (CConj a b) = Conj (negtrans a) (negtrans b) ∧
  negtrans (CDisj a b) = ineg (Conj (ineg (negtrans a)) (ineg (negtrans b))) ∧
  negtrans (CImpl a b) = Impl (negtrans a) (negtrans b) ∧
  negtrans CBottom = Bottom
End

Theorem negtrans_correct:
  cvalid ϕ ⇔ valid (negtrans ϕ)
Proof
QED
*)


