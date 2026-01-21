Theory absConseq

Ancestors
  hol pred_set

Definition lift_def:
  lift (R:'a set -> 'a -> bool) Γ Δ ⇔ (Δ ⊆ { d | R Γ d })
End

Overload "⊩"[local] = “λ(A:'a set) (a:'a). R A a:bool”
Overload "⊩ₛ"[local] = “λ(A:'a set) (B:'a set). lift R A B:bool”
val _ = temp_set_fixity "⊩" (Infix(NONASSOC, 450))
val _ = temp_set_fixity "⊩ₛ" (Infix(NONASSOC, 450))

Definition isConsequence_def:
  isConsequence (R : 'a set -> 'a -> bool) ⇔
    (∀a. R {a} a) ∧
    (∀Γ Δ a. R Γ a ∧ Γ ⊆ Δ ⇒ R Δ a) ∧
    (∀Γ Δ Σ ϕ. Γ ⊩ₛ Δ ∧ Δ ∪ Σ ⊩ ϕ ⇒ Γ ∪ Σ ⊩ ϕ)
End

Theorem isConsequence_monotone:
  isConsequence R ∧ Γ ⊆ Δ ⇒ R Γ ⊆ R Δ
Proof
  rpt strip_tac >> drule_then strip_assume_tac (iffLR isConsequence_def) >>
  simp[SUBSET_DEF, IN_DEF] >>
  metis_tac[]
QED

Theorem isConsequence_subset:
  isConsequence R ⇒ Γ ⊆ R Γ
Proof
  strip_tac >> drule_then strip_assume_tac (iffLR isConsequence_def) >>
  simp[SUBSET_DEF] >> rpt strip_tac >> simp[IN_DEF] >>
  rename [‘R Γ a (* g *)’] >>
  ‘{a} ⊆ Γ’ by simp[] >>
  first_x_assum (pop_assum o mp_then Any mp_tac) >> metis_tac[]
QED

Theorem isConsequence_assum:
  isConsequence R ∧ a ∈ Γ ⇒ R Γ a
Proof
  metis_tac[isConsequence_subset, SUBSET_DEF, IN_DEF]
QED

Theorem isConsequence_idem0:
  isConsequence R ⇒ R (R Γ) ⊆ R Γ
Proof
  strip_tac >> drule_then strip_assume_tac (iffLR isConsequence_def) >>
  simp[SUBSET_DEF, IN_DEF] >> rpt strip_tac >>
  ‘lift R Γ (R Γ)’
    by simp[lift_def, SUBSET_DEF, IN_DEF] >>
  metis_tac[UNION_EMPTY]
QED

Theorem isConsequence_idem:
  isConsequence R ⇒ R (R Γ) = R Γ
Proof
  strip_tac >> drule_then strip_assume_tac (iffLR isConsequence_def) >>
  irule SUBSET_ANTISYM >> simp[isConsequence_idem0] >>
  simp[SUBSET_DEF] >> simp[IN_DEF] >>
  metis_tac[isConsequence_subset]
QED

Definition finitary_consequence_def:
  finitary_consequence R ⇔
    isConsequence R ∧
    ∀A. R A = BIGUNION { R A₀ | FINITE A₀ ∧ A₀ ⊆ A }
End
