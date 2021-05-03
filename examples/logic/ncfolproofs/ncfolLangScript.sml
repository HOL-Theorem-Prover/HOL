open HolKernel Parse boolLib bossLib;

local open stringTheory in end
open pred_setTheory listTheory

val _ = new_theory "ncfolLang";

Datatype:
  term = Var string | Fn string (term list)
End

val term_size_def = DB.fetch "-" "term_size_def"
val _ = export_rewrites ["term_size_def"]

Theorem term_size_lemma[simp]:
  ∀x l a. MEM a l ⇒ term_size a < 1 + (x + term1_size l)
Proof
  rpt gen_tac >> Induct_on ‘l’ >> simp[] >> rpt strip_tac >> simp[] >>
  res_tac >> simp[]
QED

Theorem term_induct:
  ∀P. (∀v. P (Var v)) ∧ (∀n ts. (∀t. MEM t ts ⇒ P t) ⇒ P (Fn n ts)) ⇒
      ∀t. P t
Proof
  rpt strip_tac >>
  qspecl_then [‘P’, ‘λts. ∀t. MEM t ts ⇒ P t’]
    (assume_tac o SIMP_RULE bool_ss [])
    (TypeBase.induction_of “:term”) >> rfs[] >>
  fs[DISJ_IMP_THM, FORALL_AND_THM]
QED
val _ = TypeBase.update_induction term_induct

Definition tsubst_def[simp]:
  (tsubst v t1 (Var u) = if u = v then t1 else Var u) ∧
  tsubst v t1 (Fn fnm ts) = Fn fnm (MAP (tsubst v t1) ts)
Termination
  WF_REL_TAC ‘measure (λ(v,t0,t). term_size t)’ >> rw[]
End

Definition tFV_def:
  tFV (Var v) = {v} ∧
  tFV (Fn _ ts) = { v | ∃t. if MEM t ts then v IN tFV t else F }
Termination
  WF_REL_TAC ‘measure term_size’ >> rw[]
End

Theorem tFV_thm[simp] = SIMP_RULE (srw_ss()) [] tFV_def

Theorem MAP_CONG' = REWRITE_RULE [GSYM AND_IMP_INTRO] listTheory.MAP_CONG

Theorem tsubst_id[simp]:
  tsubst v (Var v) t = t
Proof
  Induct_on ‘t’ >> simp[Cong MAP_CONG', AllCaseEqs()]
QED

Theorem tsubst_absent[simp]:
  v ∉ tFV t ⇒ tsubst v t' t = t
Proof
  Induct_on ‘t’ >> simp[] >> rpt strip_tac >>
  ‘MAP (λa. tsubst v t' a) ts = MAP I ts’ suffices_by simp[] >>
  irule MAP_CONG' >> simp[] >> metis_tac[]
QED

Theorem tFV_subst_present:
  v ∈ tFV t ⇒ tFV (tsubst v t' t) = tFV t DELETE v ∪ tFV t'
Proof
  Induct_on ‘t’ >> simp[MEM_MAP, PULL_EXISTS] >> rw[] >>
  simp[EXTENSION] >> qx_gen_tac ‘u’ >> eq_tac >> rw[] >~
  [‘u ∈ tFV (tsubst v t' t0)’]
  >- (reverse (Cases_on ‘v ∈ tFV t0’) >> gs[] >> metis_tac[]) >~
  [‘u ≠ v’, ‘v ∈ tFV t’, ‘u ∈ tFV t0’]
  >- (qexists_tac ‘t0’ >> simp[] >> Cases_on ‘v ∈ tFV t0’ >> simp[]) >~
  [‘MEM t0 ts’]
  >- (qexists_tac ‘t0’ >> simp[])
QED

Datatype:
  form = IMP form form | NEG form | REL string (term list) | ALL string form
End

val _ = set_mapped_fixity{fixity = Infixr 460, term_name = "IMP", tok = "⥰"}
val _ = set_mapped_fixity{fixity = Prefix 900, term_name = "NEG", tok = "⌁"}


Definition fsubst_def[simp]:
  fsubst v t (IMP f1 f2) = IMP (fsubst v t f1) (fsubst v t f2) ∧
  fsubst v t (NEG f) = NEG (fsubst v t f) ∧
  fsubst v t (REL rnm ts) = REL rnm (MAP (tsubst v t) ts) ∧
  fsubst v t (ALL u f) = if u = v then ALL u f else ALL u (fsubst v t f)
End

Theorem fsubst_id[simp]:
  fsubst v (Var v) f = f
Proof
  Induct_on ‘f’ >> simp[Cong MAP_CONG', AllCaseEqs()]
QED

Definition fFV_def[simp]:
  fFV (IMP f1 f2) = fFV f1 ∪ fFV f2 ∧
  fFV (NEG f) = fFV f ∧
  fFV (REL _ ts) = tFV (Fn "" ts) ∧
  fFV (ALL v f) = fFV f DELETE v
End

Theorem fsubst_absent[simp]:
  v ∉ fFV f ⇒ fsubst v t f = f
Proof
  Induct_on ‘f’ >> simp[] >> rw[] >>
  ‘MAP (tsubst v t) l = MAP I l’ suffices_by simp[] >>
  irule MAP_CONG' >> simp[] >> metis_tac[tsubst_absent]
QED

(*
Note that this (dumb!) definition of acceptable allows both the
deduction theorem and consistency result to go through regardless.

Definition acceptable_def[simp]:
  acceptable v t f = T
End

Alternatively, the proofs of those results below don't depend on any
properties of acceptability.
*)

Definition acceptable_def[simp]:
  (acceptable v t (IMP f1 f2) ⇔ acceptable v t f1 ∧ acceptable v t f2) ∧
  (acceptable v t (NEG f) ⇔ acceptable v t f) ∧
  (acceptable v t (REL _ _) ⇔ T) ∧
  (acceptable v t (ALL u f) ⇔ u = v ∨ v ∉ fFV f ∨
                              acceptable v t f ∧ u ∉ tFV t)
End

Theorem acceptable_id[simp]:
  acceptable v (Var v) f
Proof
  Induct_on ‘f’ >> simp[]
QED

(* something where acceptability _is_ important *)
Theorem fFV_subst_present:
  acceptable v t f ∧ v ∈ fFV f ⇒
  fFV (fsubst v t f) = (fFV f DELETE v) ∪ tFV t
Proof
  Induct_on ‘f’ >> simp[DISJ_IMP_THM, MEM_MAP] >> rw[] >> simp[]
  >- (rename [‘fFV f1 DELETE v ∪ _ ∪ fFV (fsubst v t f2)’] >>
      Cases_on ‘v ∈ fFV f2’ >> simp[EXTENSION] >> metis_tac[])
  >- (rename [‘fFV (fsubst v t f1) ∪ (fFV f2 DELETE v ∪ tFV t)’] >>
      Cases_on ‘v ∈ fFV f1’ >> simp[EXTENSION] >> metis_tac[])
  >- (simp[EXTENSION, PULL_EXISTS] >> qx_gen_tac ‘u’ >> eq_tac >> rw[]
      >- (rename [‘u ∈ tFV (tsubst v t t0)’] >>
          Cases_on ‘v ∈ tFV t0’ >> gs[tFV_subst_present] >> metis_tac[])
      >- (rename [‘u ≠ v’, ‘u ∈ tFV t0’] >> qexists_tac ‘t0’ >>
          Cases_on ‘v ∈ tFV t0’ >> simp[tFV_subst_present]) >>
      first_assum $ irule_at Any >> simp[tFV_subst_present]) >>
  gs[] >> simp[EXTENSION] >> qx_gen_tac ‘u’ >> metis_tac[]
QED


Inductive ded:
[PL1:] (∀A B. ded Hs (A ⥰ B ⥰ A)) ∧
[PL2:] (∀A B C. ded Hs ((A ⥰ B ⥰ C) ⥰ (A ⥰ B) ⥰ (A ⥰ C))) ∧
[PL3:] (∀A B. ded Hs ((⌁A ⥰ ⌁B) ⥰ (⌁A ⥰ B) ⥰ A)) ∧
[PL4:] (∀v t f. acceptable v t f ⇒ ded Hs ((ALL v f) ⥰ fsubst v t f)) ∧
[PL5:] (∀v A B. v ∉ fFV A ⇒ ded Hs (ALL v (A ⥰ B) ⥰ A ⥰ (ALL v B))) ∧
[~MP:] (∀A B. ded Hs (A ⥰ B) ∧ ded Hs A ⇒ ded Hs B) ∧
[UG:] (∀v A. (∀h. h ∈ Hs ⇒ v ∉ fFV h) ∧ ded Hs A ⇒ ded Hs (ALL v A)) ∧
[~hyp:] (∀h. h ∈ Hs ⇒ ded Hs h)
End

val _ = set_mapped_fixity {term_name = "ded", fixity = Infix(NONASSOC, 450),
                           tok = "⊩"}

Theorem ded_I:
  ded Hs (ϕ ⥰ ϕ)
Proof
  metis_tac[ded_rules]
QED

Theorem deduction_thm:
  ded (h INSERT Hs) ϕ ⇒ ded Hs (h ⥰ ϕ)
Proof
  Induct_on ‘ded’ >> rpt strip_tac >> gvs[ded_I] >~
  [‘ϕ ∈ Hs’, ‘h ⥰ ϕ’]
  >- (Cases_on ‘h = ϕ’ >- simp[ded_I] >>
      irule ded_MP >> metis_tac[PL1, ded_hyp]) >~
  [‘ded (h INSERT Hs) (ϕ ⥰ ψ)’, ‘ded (h INSERT Hs) ϕ’]
  >- (resolve_then (Pos hd) assume_tac PL2 ded_MP >>
      pop_assum (first_assum o C (resolve_then (Pos hd) assume_tac)) >>
      irule ded_MP >> pop_assum $ irule_at (Pos last) >>
      pop_assum $ irule_at Any >> metis_tac[]) >~
  [‘ded (h INSERT Hs) ϕ’, ‘ded Hs (h ⥰ ALL v ϕ)’]
  >- (gs[DISJ_IMP_THM, FORALL_AND_THM] >>
      dxrule_all_then assume_tac UG >>
      irule ded_MP >> metis_tac[PL5])
  >- (irule ded_MP >> irule_at Any PL1 >> irule_at Any PL1)
  >- (irule ded_MP >> irule_at (Pos last) PL1 >> simp[PL2])
  >- (irule ded_MP >> irule_at (Pos last) PL1 >> simp[PL3])
  >- (irule ded_MP >> irule_at (Pos last) PL1 >> simp[PL4])
  >- (irule ded_MP >> irule_at (Pos last) PL1 >> simp[PL5])
QED

Theorem alpha_deduce:
  ∀x y P Hs.
    y ∉ fFV P ∧ (∀h. h ∈ Hs ⇒ y ∉ fFV h) ∧
    acceptable x (Var y) P ⇒
    ded Hs ((ALL x P) ⥰ ALL y (fsubst x (Var y) P))
Proof
  rpt strip_tac >> irule deduction_thm >> irule UG >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >> irule ded_MP >>
  irule_at (Pos last) PL4 >> simp[] >> irule ded_hyp >> simp[]
QED

Theorem finite_deductions0:
  ded Hs ϕ ⇒ ∃Hs0. FINITE Hs0 ∧ Hs0 ⊆ Hs ∧
                   ∀Hs'. Hs0 ⊆ Hs' ∧ Hs' ⊆ Hs ⇒ ded Hs' ϕ
Proof
  Induct_on ‘ded’ >> simp[ded_rules] >> rpt strip_tac >~
  [‘ded _ (ALL v ϕ)’] >- metis_tac[SUBSET_DEF, UG] >~
  [‘Hs1 ⊆ _ ∧ _ ⇒ ded _ ϕ₁’, ‘Hs2 ⊆ _ ∧ _ ⇒ ded _ (ϕ₁ ⥰ ϕ₂)’,
   ‘Hs1 ⊆ Hs’, ‘Hs2 ⊆ Hs’]
  >- (qexists_tac ‘Hs1 ∪ Hs2’ >> simp[] >> qx_gen_tac ‘HI’ >>
      metis_tac[ded_MP]) >~
  [‘ϕ ∈ Hs’, ‘ded _ ϕ’]
  >- (qexists_tac ‘{ϕ}’ >> simp[SUBSET_DEF, ded_rules]) >>
  qexists_tac ‘∅’ >> simp[]
QED

Theorem finite_deductions:
  ded Hs ϕ ⇒ ∃Hs0. FINITE Hs0 ∧ Hs0 ⊆ Hs ∧ ded Hs0 ϕ
Proof
  metis_tac[finite_deductions0, SUBSET_REFL]
QED

Theorem closed_weakening:
  (∀f. f ∈ Hs' ⇒ fFV f = ∅) ∧ ded Hs ϕ ⇒ ded (Hs ∪ Hs') ϕ
Proof
  Cases_on ‘∀f. f ∈ Hs' ⇒ fFV f = ∅’ >> simp[] >>
  Induct_on ‘ded’ >> simp[ded_rules] >> rpt strip_tac
  >- metis_tac[ded_rules] >>
  irule UG >> simp[DISJ_IMP_THM]
QED

Definition conmap_def:
  conmap (REL _ _) = T ∧
  conmap (IMP f1 f2) = (conmap f1 ⇒ conmap f2) ∧
  conmap (NEG f) = ¬conmap f ∧
  conmap (ALL _ f) = conmap f
End

Theorem conmap_subst:
  conmap (fsubst v t f) = conmap f
Proof
  Induct_on ‘f’ >> simp[conmap_def] >> rw[conmap_def]
QED

Theorem FOL_consistent_lemma:
  ded ∅ ϕ ⇒ conmap ϕ
Proof
  Induct_on ‘ded’ >> simp[conmap_def, conmap_subst]
QED

Theorem FOL_consistent:
  ded ∅ ϕ ⇒ ¬ded ∅ (NEG ϕ)
Proof
  rpt strip_tac >> rpt (dxrule FOL_consistent_lemma) >>
  simp[conmap_def]
QED

Theorem MODAL_ALL:
  ded ∅ (IMP (ALL x (IMP P Q)) (IMP (ALL x P) (ALL x Q)))
Proof
  irule deduction_thm >> irule deduction_thm >> irule UG >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >> irule ded_MP >> qexists_tac ‘P’ >>
  conj_tac >> qmatch_abbrev_tac ‘ded Hs _’ >~
  [‘ded _ (IMP P Q)’]
  >- (‘ded Hs (fsubst x (Var x) (IMP P Q))’ suffices_by simp[] >>
      irule ded_MP >> irule_at (Pos last) PL4 >> simp[] >>
      simp[Abbr‘Hs’] >> irule ded_hyp >> simp[]) >>
  ‘ded Hs (fsubst x (Var x) P)’ suffices_by simp[] >>
  irule ded_MP >> qexists_tac ‘ALL x P’ >> simp[PL4] >>
  simp[Abbr‘Hs’, ded_hyp]
QED

Definition disj_def:
  disj P Q = IMP(NEG P) Q
End

Theorem disj_EQ_various[simp]:
  disj p q ≠ NEG r ∧
  disj p q ≠ ALL v r ∧
  disj p q ≠ REL rnm ts
Proof
  simp[disj_def]
QED

Theorem fFV_disj[simp]:
  fFV (disj p q) = fFV p ∪ fFV q
Proof
  simp[disj_def]
QED

Theorem exFALSO:
  ϕ ∈ Γ ∧ NEG ϕ ∈ Γ ⇒ ded Γ ψ
Proof
  strip_tac >>
  ‘ded Γ (IMP (NEG ψ) (NEG ϕ)) ∧ ded Γ (IMP (NEG ψ) ϕ)’
    by metis_tac[ded_rules] >>
  metis_tac[ded_rules]
QED

Theorem negnegE:
  ded Γ (IMP (NEG (NEG p)) p)
Proof
  irule deduction_thm >>
  ‘ded (NEG (NEG p) INSERT Γ) (IMP (NEG p) (NEG(NEG p)))’
    by (irule deduction_thm >> simp[ded_hyp]) >>
  ‘ded (NEG(NEG p) INSERT Γ) (IMP (NEG p) (NEG p))’
    by (irule deduction_thm >> simp[ded_hyp]) >>
  metis_tac[PL3, ded_MP]
QED

Theorem contrI:
  ded (NEG q INSERT Γ) p ∧ ded (NEG q INSERT Γ) (NEG p) ⇒ ded Γ q
Proof
  strip_tac >>
  ‘ded Γ (IMP (NEG q) p) ∧ ded Γ (IMP (NEG q) (NEG p))’
    by (conj_tac >> irule deduction_thm >> simp[]) >>
  metis_tac[ded_rules]
QED

Theorem negnegI:
  ded Γ (IMP p (NEG (NEG p)))
Proof
  irule deduction_thm >> irule contrI >> qexists_tac ‘p’ >>
  simp[ded_hyp] >> irule ded_MP >> irule_at (Pos last) negnegE >>
  simp[ded_hyp]
QED


Theorem contrI:
  ded (NEG q INSERT Γ) p ∧ ded (NEG q INSERT Γ) (NEG p) ⇒ ded Γ q
Proof
  strip_tac >>
  ‘ded Γ (IMP (NEG q) p) ∧ ded Γ (IMP (NEG q) (NEG p))’
    by (conj_tac >> irule deduction_thm >> simp[]) >>
  metis_tac[ded_rules]
QED

Theorem cposI:
  ded Γ (IMP (IMP p q) (IMP (NEG q) (NEG p)))
Proof
  ntac 2 (irule deduction_thm) >>
  ‘ded (NEG q INSERT IMP p q INSERT Γ) (IMP (NEG (NEG p)) q)’
    by (irule deduction_thm >> irule ded_MP >>
        qexists_tac ‘p’ >> simp[ded_hyp] >>
        irule ded_MP >> irule_at (Pos last) negnegE >>
        simp[ded_hyp]) >>
  ‘ded (NEG q INSERT IMP p q INSERT Γ) (IMP (NEG (NEG p)) (NEG q))’
    by (irule deduction_thm >> simp[ded_hyp]) >>
  metis_tac[ded_rules]
QED

Theorem disjI1:
  ded Γ (IMP ϕ (disj ϕ ψ))
Proof
  simp[disj_def] >> ntac 2 (irule deduction_thm) >>
  irule exFALSO >> simp[] >> metis_tac[]
QED

Theorem disjI2:
  ded Γ (IMP ϕ (disj ψ ϕ))
Proof
  simp[disj_def, PL1]
QED

Theorem disjEth:
  ded Γ (IMP (disj p q) (IMP (IMP p r) (IMP (IMP q r) r)))
Proof
  simp[disj_def] >> ntac 3 $ irule deduction_thm >>
  qmatch_abbrev_tac ‘ded Δ r’ >>
  ‘ded Δ (IMP (NEG r) (NEG q))’
    by (irule ded_MP >> irule_at (Pos last) cposI >>
        simp[Abbr‘Δ’, ded_hyp]) >>
  ‘ded Δ (IMP (IMP (NEG r) q) r)’ by metis_tac[ded_rules] >>
  irule ded_MP >> pop_assum (irule_at (Pos last)) >>
  irule deduction_thm >>
  irule ded_MP >> qexists_tac ‘NEG p’ >>
  reverse conj_tac >- simp[ded_hyp, Abbr‘Δ’] >>
  irule ded_MP >> qexists_tac ‘NEG r’ >> conj_tac
  >- simp[ded_hyp, Abbr‘Δ’] >>
  irule ded_MP >> irule_at (Pos last) cposI >> simp[ded_hyp, Abbr‘Δ’]
QED

Theorem disjE:
  ded Γ (disj p q) ∧ ded (p INSERT Γ) r ∧ ded (q INSERT Γ) r ⇒
  ded Γ r
Proof
  strip_tac >>
  ‘ded Γ (IMP (IMP p r) (IMP (IMP q r) r))’ by metis_tac[ded_MP, disjEth] >>
  ‘ded Γ (IMP p r)’ by metis_tac[deduction_thm] >>
  ‘ded Γ (IMP (IMP q r) r)’ by metis_tac[ded_MP] >>
  metis_tac[deduction_thm, ded_MP]
QED

Definition conj_def:
  conj P Q = NEG (disj (NEG P) (NEG Q))
End

Theorem fFV_conj[simp]:
  fFV (conj p q) = fFV p ∪ fFV q
Proof
  simp[conj_def]
QED

Theorem conj_EQ_various[simp]:
  conj p q ≠ IMP r s ∧
  conj p q ≠ ALL v p ∧
  conj p q ≠ REL rn ts ∧
  conj p q ≠ disj r s
Proof
  simp[conj_def]
QED

Theorem conjIth:
  ded Γ (IMP ϕ (IMP ψ (conj ϕ ψ)))
Proof
  simp[conj_def, disj_def] >> ntac 2 (irule deduction_thm) >>
  irule contrI>> qexists_tac ‘ψ’ >> simp[ded_hyp] >>
  irule ded_MP >> qexists_tac ‘NEG (NEG ϕ)’ >> reverse conj_tac
  >- (irule ded_MP >> irule_at (Pos last) negnegE >> simp[ded_hyp]) >>
  irule ded_MP >> irule_at (Pos last) negnegI >> simp[ded_hyp]
QED

Theorem conjI:
  ded Γ p ∧ ded Γ q ⇒ ded Γ (conj p q)
Proof
  metis_tac[ded_rules, conjIth]
QED

Theorem conjE1th:
  ded Γ (IMP (conj ϕ ψ) ϕ)
Proof
  simp[conj_def, disj_def] >> irule deduction_thm >> irule contrI >>
  qexists_tac ‘IMP (NEG (NEG ϕ)) (NEG ψ)’ >> reverse conj_tac
  >- simp[ded_hyp] >>
  irule deduction_thm >> irule exFALSO >> qexists_tac ‘NEG ϕ’ >> simp[]
QED

Theorem conjE2th:
  ded Γ (IMP (conj ϕ ψ) ψ)
Proof
  simp[conj_def, disj_def] >> irule deduction_thm >> irule contrI >>
  qexists_tac ‘IMP (NEG (NEG ϕ)) (NEG ψ)’ >> simp [ded_hyp] >>
  irule deduction_thm >> simp[ded_hyp]
QED

Theorem impE:
  ded Γ (IMP p q) ∧ ded Γ p ∧ ded (q INSERT Γ) r ⇒ ded Γ r
Proof
  strip_tac >> irule ded_MP >> qexists_tac ‘q’ >> simp[deduction_thm] >>
  metis_tac[ded_MP]
QED

Theorem conjE[simp]:
  ded Γ (conj p q) ⇔ ded Γ p ∧ ded Γ q
Proof
  rw[EQ_IMP_THM, conjI]
  >- (irule impE >> first_assum $ irule_at (Pos hd) >>
      irule_at (Pos hd) conjE1th >> simp[ded_hyp])
  >- (irule impE >> first_assum $ irule_at (Pos hd) >>
      irule_at (Pos hd) conjE2th >> simp[ded_hyp])
QED

Definition IFF_def:
  IFF p q = conj (IMP p q) (IMP q p)
End
val _ = set_mapped_fixity {tok = "↔", term_name = "IFF",
                           fixity = Infix(NONASSOC, 450)}

Theorem DRULE:
  ded Γ (IMP p q) ∧ p ∈ Γ ∧ ded (q INSERT Γ) r ⇒ ded Γ r
Proof
  rpt strip_tac >> irule ded_MP >> qexists_tac ‘q’ >>
  metis_tac[deduction_thm, ded_rules]
QED

Theorem IN_INSERT1 =
        IN_INSERT |> iffRL |> SIMP_RULE bool_ss [DISJ_IMP_THM, FORALL_AND_THM]
                           |> cj 1

Theorem IMP_NEQ_SUBf[simp]:
  ∀p q. IMP p q ≠ p ∧ IMP p q ≠ q
Proof
  simp[FORALL_AND_THM] >> conj_tac
  >- (Induct_on ‘p’ >> simp[]) >>
  Induct_on ‘q’ >> simp[]
QED

Theorem conjE_H[simp]:
  ded (conj p q INSERT Γ) c ⇔ ded (p INSERT q INSERT Γ) c
Proof
  eq_tac
  >- (Induct_on ‘ded’ >> rw[PL1, PL2, PL3, PL4, PL5]
      >- metis_tac[ded_MP]
      >- (irule UG >> gs[DISJ_IMP_THM, FORALL_AND_THM])
      >- simp[ded_hyp]
      >- simp[ded_hyp]) >>
  Induct_on ‘ded’ >>
  simp[PL1,PL2,PL3,PL4,PL5,DISJ_IMP_THM,FORALL_AND_THM,ded_hyp] >> rw[]
  >- metis_tac[ded_MP]
  >- (irule UG >> simp[DISJ_IMP_THM, FORALL_AND_THM])
  >- (irule impE >> irule_at (Pos (el 2)) conjE1th >>
      irule_at Any ded_hyp >> irule_at Any IN_INSERT1 >>
      simp[ded_hyp]) >>
  irule impE >> irule_at (Pos (el 2)) conjE2th >>
  irule_at Any ded_hyp >> irule_at Any IN_INSERT1 >>
  simp[ded_hyp]
QED

Theorem conj_comm:
  ded Γ (conj p q ↔ conj q p)
Proof
  rw[IFF_def] >> irule deduction_thm >> rw[ded_hyp]
QED

Theorem disj_comm:
  ded Γ (disj p q ↔ disj q p)
Proof
  rw[IFF_def] >> irule deduction_thm >>
  irule disjE >> irule_at (Pos hd) ded_hyp >> irule_at (Pos hd) IN_INSERT1>>
  metis_tac[IN_INSERT, ded_rules, disjI1, disjI2]
QED

Overload dedeq = “λΓ p q. ded Γ (p ↔ q)”

Theorem prove_hyp:
  ded Γ ϕ ∧ ded (ϕ INSERT Γ) ψ ⇒ ded Γ ψ
Proof
  metis_tac[ded_MP, deduction_thm]
QED


val _ = Unicode.unicode_version {tmnm = "INSERT", u = "⨾"}

(*
Theorem conj_CONGL:
  ∀p1 p2 q. dedeq Γ p1 p2 ⇒
            dedeq Γ (conj p1 q) (conj p2 q)
Proof
  Induct_on ‘ded’ >> rw[IFF_def]
  strip_tac >> simp[IFF_def] >> conj_tac >>
  irule deduction_thm >> simp[]
*)

val _ = export_theory();
