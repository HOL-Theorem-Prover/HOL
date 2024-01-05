open HolKernel Parse boolLib bossLib;

local open stringTheory in end
open pred_setTheory listTheory

val _ = new_theory "ncfolLang";

val _ = Unicode.unicode_version {tmnm = "INSERT", u = "⨾"}

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
[PL1:] (∀A B. ded R Hs (A ⥰ B ⥰ A))
[PL2:] (∀A B C. ded R Hs ((A ⥰ B ⥰ C) ⥰ (A ⥰ B) ⥰ (A ⥰ C)))
[PL3:] (∀A B. ded R Hs ((⌁A ⥰ ⌁B) ⥰ (⌁A ⥰ B) ⥰ A))
[PL4:] (∀v t f. acceptable v t f ⇒ ded R Hs ((ALL v f) ⥰ fsubst v t f))
[PL5:] (∀v A B. v ∉ fFV A ⇒ ded R Hs (ALL v (A ⥰ B) ⥰ A ⥰ (ALL v B)))
[~MP:] (∀A B. ded R Hs (A ⥰ B) ∧ ded R Hs A ⇒ ded R Hs B)
[UG:] (∀v A. (∀h. h ∈ Hs ⇒ v ∉ fFV h) ∧ ded R Hs A ⇒ ded R Hs (ALL v A))
[~hyp:] (∀h. h ∈ Hs ⇒ ded R Hs h)
[~R:] (∀B s. (∀A hs. (hs,A) ∈ s ⇒ ded R hs A) ∧ R s Hs B ⇒ ded R Hs B)
End

Overload Ded = “ded R”

Overload ded0 = “ded (λs Hs B. F)”
Overload dedg = “ded (λs Hs B. ∃hs0. s = {(hs0,B)} ∧ hs0 ⊆ Hs)”

val _ = set_mapped_fixity {term_name = "Ded", fixity = Infix(NONASSOC, 450),
                           tok = "⊩"}
val _ = set_mapped_fixity {term_name = "dedg", fixity = Infix(NONASSOC, 450),
                           tok = "⊩ᵍ"}
val _ = set_mapped_fixity {term_name = "ded0", fixity = Infix(NONASSOC, 450),
                           tok = "⊩⁰"}

Theorem ded_I:
  Hs ⊩ (ϕ ⥰ ϕ)
Proof
  metis_tac[ded_rules]
QED

Theorem Gdeduction_thm:
  ∀h Hs ϕ. (h INSERT Hs) ⊩ᵍ ϕ ⇒ Hs ⊩ᵍ (h ⥰ ϕ)
Proof
  Induct_on ‘ded’ >> rpt strip_tac >> gvs[ded_I] >~
  [‘ϕ ∈ Hs’, ‘h ⥰ ϕ’]
  >- (Cases_on ‘h = ϕ’ >- simp[ded_I] >>
      irule ded_MP >> metis_tac[PL1, ded_hyp, IN_DELETE]) >~
  [‘h INSERT Hs ⊩ᵍ (ϕ ⥰ ψ)’, ‘h INSERT Hs ⊩ᵍ ϕ’]
  >- (resolve_then (Pos hd) assume_tac PL2 ded_MP >>
      pop_assum (first_assum o C (resolve_then (Pos hd) assume_tac)) >>
      irule ded_MP >> pop_assum $ irule_at (Pos last) >> simp[]) >~
  [‘Hs ⊩ᵍ IMP h (ALL v ϕ)’]
  >- (pop_assum $ C (resolve_then (Pos (el 2)) assume_tac) UG >>
      gs[DISJ_IMP_THM, FORALL_AND_THM] >>
      irule ded_MP >> metis_tac[PL5]) >~
  [‘Hs0 ⊩ᵍ ϕ’, ‘Hs0 ⊆ h INSERT Hs’]
  >- (irule ded_R >> simp[PULL_EXISTS] >>
      Cases_on ‘h ∈ Hs0’
      >- (‘∃Hs00. Hs0 = h INSERT Hs00 ∧ h ∉ Hs00’ by metis_tac[DECOMPOSITION] >>
          ‘Hs00 ⊩ᵍ IMP h ϕ’ by metis_tac[] >>
          ‘Hs00 ⊆ Hs’ suffices_by metis_tac[] >>
          gvs[]) >>
      ‘Hs0 ⊩ᵍ IMP h ϕ’ by metis_tac[ded_MP, PL1] >>
      ‘Hs0 ⊆ Hs’ by metis_tac[SUBSET_DEF, IN_INSERT] >> metis_tac[])
  >- (irule ded_MP >> irule_at Any PL1 >> irule_at Any PL1)
  >- (irule ded_MP >> irule_at (Pos last) PL1 >> simp[PL2])
  >- (irule ded_MP >> irule_at (Pos last) PL1 >> simp[PL3])
  >- (irule ded_MP >> irule_at (Pos last) PL1 >> simp[PL4])
  >- (irule ded_MP >> irule_at (Pos last) PL1 >> simp[PL5])
QED

Theorem deduction0_thm:
  ∀h Hs ϕ. (h INSERT Hs) ⊩⁰ ϕ ⇒ Hs ⊩⁰ (h ⥰ ϕ)
Proof
  Induct_on ‘ded’ >> rpt strip_tac >> gvs[ded_I] >~
  [‘ϕ ∈ Hs’, ‘h ⥰ ϕ’]
  >- (Cases_on ‘h = ϕ’ >- simp[ded_I] >>
      irule ded_MP >> metis_tac[PL1, ded_hyp]) >~
  [‘h INSERT Hs ⊩⁰ (ϕ ⥰ ψ)’, ‘h INSERT Hs ⊩⁰ ϕ’]
  >- (resolve_then (Pos hd) assume_tac PL2 ded_MP >>
      pop_assum (first_assum o C (resolve_then (Pos hd) assume_tac)) >>
      irule ded_MP >> pop_assum $ irule_at (Pos last) >> simp[]) >~
  [‘Hs ⊩⁰ IMP h (ALL v ϕ)’]
  >- (pop_assum $ C (resolve_then (Pos (el 2)) assume_tac) UG >>
      gs[DISJ_IMP_THM, FORALL_AND_THM] >>
      irule ded_MP >> metis_tac[PL5])
  >- (irule ded_MP >> irule_at Any PL1 >> irule_at Any PL1)
  >- (irule ded_MP >> irule_at (Pos last) PL1 >> simp[PL2])
  >- (irule ded_MP >> irule_at (Pos last) PL1 >> simp[PL3])
  >- (irule ded_MP >> irule_at (Pos last) PL1 >> simp[PL4])
  >- (irule ded_MP >> irule_at (Pos last) PL1 >> simp[PL5])
QED

Theorem stripimp_rwt[simp]:
  G ⊩ᵍ p ⥰ q ⇔ p INSERT G ⊩ᵍ q
Proof
  eq_tac >> simp[Gdeduction_thm] >> strip_tac >>
  ‘p INSERT G ⊩ᵍ p ⥰ q’
    by (irule ded_R>> simp[PULL_EXISTS] >> goal_assum drule >>
        simp[SUBSET_DEF]) >>
  ‘p INSERT G ⊩ᵍ p’ by simp[ded_hyp] >> metis_tac[ded_MP]
QED

Theorem alpha_deduce:
  ∀x y P Hs.
    y ∉ fFV P ∧ acceptable x (Var y) P ∧ ALL x P ∈ Γ ⇒
    Γ ⊩ᵍ ALL y (fsubst x (Var y) P)
Proof
  rpt strip_tac >> irule ded_R >> simp[PULL_EXISTS] >>
  qexists_tac ‘{ALL x P}’ >> simp[] >> irule UG >> simp[] >>
  irule ded_MP >> irule_at (Pos last) PL4 >> simp[ded_hyp]
QED

Theorem finite_deductions:
  Hs ⊩ᵍ ϕ ⇒ ∃Hs0. FINITE Hs0 ∧ Hs0 ⊆ Hs ∧ Hs0 ⊩ᵍ ϕ
Proof
  Induct_on ‘ded’ >> rpt strip_tac >>
  gvs[PL1,PL2,PL3,PL4,PL5,Excl "stripimp_rwt"] >~
  [‘_ ⊩ᵍ (ALL v ϕ)’] >- metis_tac[SUBSET_DEF, UG] >~
  [‘Hs2 ⊩ᵍ ϕ₁ ⥰ ϕ₂’, ‘FINITE Hs2’, ‘Hs1 ⊩ᵍ ϕ₁’, ‘FINITE Hs1’]
  >- (qexists_tac ‘Hs1 ∪ Hs2’ >> simp[] >> irule ded_MP >> qexists_tac ‘ϕ₁’ >>
      conj_tac >> irule ded_R >> gs[PULL_EXISTS] >> metis_tac[SUBSET_UNION]) >~
  [‘ϕ ∈ Hs’, ‘_ ⊩ᵍ ϕ’]
  >- (qexists_tac ‘{ϕ}’ >> simp[SUBSET_DEF, ded_hyp]) >~
  [‘As ⊆ Bs’, ‘Bs ⊆ Cs’] >- metis_tac[SUBSET_TRANS] >>
  qexists_tac ‘∅’ >> simp[]
QED

Theorem closed_weakening:
  (∀f. f ∈ Hs' ⇒ fFV f = ∅) ∧ Hs ⊩⁰ ϕ ⇒ Hs ∪ Hs' ⊩⁰ ϕ
Proof
  Cases_on ‘∀f. f ∈ Hs' ⇒ fFV f = ∅’ >> simp[] >>
  Induct_on ‘ded’ >> simp[ded_rules] >> rpt strip_tac
  >- metis_tac[ded_rules] >>
  irule UG >> simp[DISJ_IMP_THM]
QED

Theorem gweakening:
  Hs ⊩ᵍ ϕ ⇒ Hs ∪ Hs' ⊩ᵍ ϕ
Proof
  strip_tac >> irule ded_R >> simp[PULL_EXISTS] >> metis_tac[SUBSET_UNION]
QED

Theorem ded0_dedg:
  Hs ⊩⁰ ϕ ⇒ Hs ⊩ᵍ ϕ
Proof
  Induct_on ‘ded’ >> REWRITE_TAC[] >> rpt strip_tac >>
  metis_tac[ded_rules]
QED

Theorem closed_dedg_ded0:
  (∀h. h ∈ Hs ⇒ fFV h = ∅) ∧ Hs ⊩ᵍ ϕ ⇒ Hs ⊩⁰ ϕ
Proof
  Induct_on ‘ded’ >> rpt strip_tac >~
  [‘s = {(_,_)}’]
  >- (gvs[] >>
      ‘∃hs1. Hs = hs0 ∪ hs1’ suffices_by
        (strip_tac >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
         metis_tac[closed_weakening]) >>
      qexists_tac ‘Hs DIFF hs0’ >> simp[EXTENSION]>> metis_tac[SUBSET_DEF]) >>
  metis_tac[ded_rules]
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
  ∅ ⊩⁰ ϕ ⇒ conmap ϕ
Proof
  Induct_on ‘ded’ >> simp[conmap_def, conmap_subst]
QED

Theorem FOL_consistent:
  ∅ ⊩⁰ ϕ ⇒ ¬(∅ ⊩⁰ NEG ϕ)
Proof
  rpt strip_tac >> rpt (dxrule FOL_consistent_lemma) >>
  simp[conmap_def]
QED

Theorem MODAL_ALL:
  ∅ ⊩⁰ (IMP (ALL x (IMP P Q)) (IMP (ALL x P) (ALL x Q)))
Proof
  irule deduction0_thm >> irule deduction0_thm >> irule UG >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >> irule ded_MP >> qexists_tac ‘P’ >>
  conj_tac >> qmatch_abbrev_tac ‘Hs ⊩⁰ _’ >~
  [‘_ ⊩⁰ (IMP P Q)’]
  >- (‘Hs ⊩⁰ (fsubst x (Var x) (IMP P Q))’ suffices_by simp[] >>
      irule ded_MP >> irule_at (Pos last) PL4 >> simp[] >>
      simp[Abbr‘Hs’, ded_hyp]) >>
  ‘Hs ⊩⁰ (fsubst x (Var x) P)’ suffices_by simp[] >>
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
  ϕ ∈ Γ ∧ NEG ϕ ∈ Γ ⇒ Γ ⊩ ψ
Proof
  metis_tac[ded_rules]
QED

Theorem negnegE:
  Γ ⊩⁰ IMP (NEG (NEG p)) p
Proof
  irule deduction0_thm >>
  ‘(NEG (NEG p) INSERT Γ) ⊩⁰ (IMP (NEG p) (NEG(NEG p)))’
    by (irule deduction0_thm >> simp[ded_hyp]) >>
  ‘NEG(NEG p) INSERT Γ ⊩⁰ IMP (NEG p) (NEG p)’
    by (irule deduction0_thm >> simp[ded_hyp]) >>
  metis_tac[PL3, ded_MP]
QED

Theorem contrI:
  NEG q INSERT Γ ⊩ᵍ p ∧ NEG q INSERT Γ ⊩ᵍ NEG p ⇒ Γ ⊩ᵍ q
Proof
  strip_tac >>
  ‘Γ ⊩ᵍ IMP (NEG q) p ∧ Γ ⊩ᵍ IMP (NEG q) (NEG p)’ by simp[] >>
  metis_tac[ded_rules]
QED

Theorem negnegI:
  Γ ⊩ᵍ IMP p (NEG (NEG p))
Proof
  simp[] >> irule contrI >> qexists_tac ‘p’ >>
  simp[ded_hyp] >> irule ded_MP >> irule_at (Pos last) ded0_dedg >>
  irule_at (Pos hd) negnegE >> simp[ded_hyp]
QED

Theorem cposI:
  Γ ⊩⁰ IMP (IMP p q) (IMP (NEG q) (NEG p))
Proof
  ntac 2 (irule deduction0_thm) >>
  ‘NEG q INSERT IMP p q INSERT Γ ⊩⁰ IMP (NEG (NEG p)) q’
    by (irule deduction0_thm >> irule ded_MP >>
        qexists_tac ‘p’ >> simp[ded_hyp] >>
        irule ded_MP >> irule_at (Pos last) negnegE >>
        simp[ded_hyp]) >>
  ‘NEG q INSERT IMP p q INSERT Γ ⊩⁰ IMP (NEG (NEG p)) (NEG q)’
    by (irule deduction0_thm >> simp[ded_hyp]) >>
  metis_tac[ded_rules]
QED

Theorem impE:
  Γ ⊩ᵍ IMP p q ∧ Γ ⊩ᵍ p ∧ q INSERT Γ ⊩ᵍ r ⇒ Γ ⊩ᵍ r
Proof
  strip_tac >> irule ded_MP >> qexists_tac ‘q’ >> simp[Gdeduction_thm] >>
  metis_tac[ded_MP]
QED

Theorem cposE:
  Γ ⊩ᵍ IMP (IMP (NEG q) (NEG p)) (IMP p q)
Proof
  simp[] >> irule contrI >> qexists_tac ‘p’ >>
  simp[ded_hyp] >> irule impE >> qexistsl_tac [‘NEG q’, ‘NEG p’] >>
  simp[ded_hyp, Excl "stripimp_rwt"]
QED

Theorem disjI1:
  Γ ⊩⁰ IMP ϕ (disj ϕ ψ)
Proof
  simp[disj_def] >> ntac 2 (irule deduction0_thm) >>
  irule exFALSO >> simp[] >> metis_tac[]
QED

Theorem disjI2:
  Γ ⊩ IMP ϕ (disj ψ ϕ)
Proof
  simp[disj_def, PL1]
QED

Theorem disjEth:
  Γ ⊩ᵍ IMP (disj p q) (IMP (IMP p r) (IMP (IMP q r) r))
Proof
  simp[disj_def] >>
  qmatch_abbrev_tac ‘Δ ⊩ᵍ r’ >>
  ‘Δ ⊩ᵍ IMP (NEG r) (NEG q)’
    by (irule ded_MP >> irule_at (Pos last) ded0_dedg >>
        irule_at (Pos hd) cposI >>
        simp[Abbr‘Δ’, ded_hyp, Excl "stripimp_rwt"]) >>
  ‘Δ ⊩ᵍ IMP (IMP (NEG r) q) r’ by metis_tac[ded_rules] >>
  irule ded_MP >> pop_assum (irule_at (Pos last)) >> simp[] >>
  irule ded_MP >> qexists_tac ‘NEG p’ >>
  reverse conj_tac >- simp[ded_hyp, Abbr‘Δ’, Excl "stripimp_rwt"] >>
  irule ded_MP >> qexists_tac ‘NEG r’ >> conj_tac
  >- simp[ded_hyp, Abbr‘Δ’] >>
  irule ded_MP >> irule_at (Pos last) ded0_dedg >> irule_at (Pos hd) cposI >>
  simp[ded_hyp, Abbr‘Δ’, Excl "stripimp_rwt"]
QED

Theorem disjE:
  Γ ⊩ᵍ disj p q ∧ p INSERT Γ ⊩ᵍ r ∧ q INSERT Γ ⊩ᵍ r ⇒ Γ ⊩ᵍ r
Proof
  strip_tac >>
  ‘Γ ⊩ᵍ IMP (IMP p r) (IMP (IMP q r) r)’ by metis_tac[ded_MP, disjEth] >>
  ‘Γ ⊩ᵍ IMP p r’ by metis_tac[Gdeduction_thm] >>
  ‘Γ ⊩ᵍ IMP (IMP q r) r’ by metis_tac[ded_MP] >>
  metis_tac[Gdeduction_thm, ded_MP]
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

Theorem negnegEG = MATCH_MP ded0_dedg negnegE

Theorem conjIth:
  Γ ⊩ᵍ IMP ϕ (IMP ψ (conj ϕ ψ))
Proof
  simp[conj_def, disj_def] >>
  irule contrI >> qexists_tac ‘ψ’ >> simp[ded_hyp] >>
  irule ded_MP >> qexists_tac ‘NEG (NEG ϕ)’ >> reverse conj_tac
  >- (irule ded_MP >> irule_at (Pos last) negnegEG >> simp[ded_hyp]) >>
  irule ded_MP >> irule_at (Pos last) negnegI >> simp[ded_hyp]
QED

Theorem conjI:
  Γ ⊩ᵍ p ∧ Γ ⊩ᵍ q ⇒ Γ ⊩ᵍ (conj p q)
Proof
  strip_tac >> irule impE >> irule_at (Pos (el 2)) conjIth >>
  qexistsl_tac [‘p’, ‘q’] >> simp[] >> irule impE >>
  qexistsl_tac [‘q’, ‘conj p q’] >> simp[ded_hyp, Excl "stripimp_rwt"] >>
  irule ded_R >> simp[PULL_EXISTS] >> qexists_tac ‘Γ’ >> simp[] >>
  simp[SUBSET_DEF]
QED

Theorem conjE1th:
  Γ ⊩ᵍ IMP (conj ϕ ψ) ϕ
Proof
  simp[conj_def, disj_def] >> irule contrI >>
  qexists_tac ‘IMP (NEG (NEG ϕ)) (NEG ψ)’ >> reverse conj_tac
  >- simp[ded_hyp] >>
  simp[] >> irule exFALSO >> qexists_tac ‘NEG ϕ’ >> simp[]
QED

Theorem conjE2th:
  Γ ⊩ᵍ IMP (conj ϕ ψ) ψ
Proof
  simp[conj_def, disj_def] >> irule contrI >>
  qexists_tac ‘IMP (NEG (NEG ϕ)) (NEG ψ)’ >> simp [ded_hyp]
QED

Theorem conjE[simp]:
  Γ ⊩ᵍ conj p q ⇔ Γ ⊩ᵍ p ∧ Γ ⊩ᵍ q
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
  conj p q INSERT Γ ⊩ᵍ c ⇔ p INSERT q INSERT Γ ⊩ᵍ c
Proof
  eq_tac >>
  map_every qid_spec_tac [‘p’, ‘q’, ‘Γ’, ‘c’] >>
  Induct_on ‘ded’ >> simp[PL1, PL2, PL3, PL4, PL5, Excl "stripimp_rwt"]
  >- (rpt strip_tac >> gvs[ded_hyp, Excl "stripimp_rwt"]
      >- metis_tac[ded_MP]
      >- (irule UG >> gvs[DISJ_IMP_THM, FORALL_AND_THM])
      >- (rename [‘hs0 ⊆ _’] >> irule ded_R >> simp[PULL_EXISTS] >>
          Cases_on ‘conj p q ∈ hs0’
          >- (fs[Once DECOMPOSITION]>> first_x_assum $ irule_at (Pos hd) >>
              gvs[] >> irule_at (Pos hd) EQ_REFL >> simp[] >>
              gs[SUBSET_DEF]) >>
          last_x_assum $ irule_at (Pos hd) >> gs[SUBSET_DEF])) >>
  rpt strip_tac >> gvs[ded_hyp, Excl "stripimp_rwt"]
  >- metis_tac[ded_MP]
  >- (irule UG >> gvs[DISJ_IMP_THM, FORALL_AND_THM])
  >- (irule impE >> irule_at (Pos (el 2)) conjE1th >>
      irule_at Any ded_hyp >> irule_at Any IN_INSERT1 >>
      simp[ded_hyp])
  >- (irule impE >> irule_at (Pos (el 2)) conjE2th >>
      irule_at Any ded_hyp >> irule_at Any IN_INSERT1 >>
      simp[ded_hyp]) >>
  Cases_on ‘p ∈ hs0’
  >- (‘∃hs1. hs0 = p INSERT hs1 ∧ p ∉ hs1’ by metis_tac[DECOMPOSITION] >>
      gvs[]>> Cases_on ‘q ∈ hs1’
      >- (‘∃hs2. hs1 = q INSERT hs2 ∧ q ∉ hs2’ by metis_tac[DECOMPOSITION] >>
          gvs[] >> first_x_assum (resolve_then Any assume_tac EQ_REFL)>>
          irule ded_R >> simp[PULL_EXISTS] >> goal_assum drule >>
          gs[SUBSET_DEF]) >>
      irule ded_R >> simp[PULL_EXISTS] >> qexists_tac ‘conj p q INSERT hs1’ >>
      reverse conj_tac >- gs[SUBSET_DEF] >> irule impE >>
      qexistsl_tac [‘conj p q’, ‘p’] >>
      simp[ded_hyp, Excl "stripimp_rwt", Excl "conjE", conjE1th] >>
      irule ded_R >> simp[PULL_EXISTS] >> qexists_tac ‘p INSERT hs1’ >>
      simp[SUBSET_DEF]) >>
  Cases_on ‘q ∈ hs0’
  >- (‘∃hs1. hs0 = q INSERT hs1 ∧ q ∉ hs1’ by metis_tac[DECOMPOSITION]>>
      gvs[] >> irule ded_R >> simp[PULL_EXISTS] >>
      qexists_tac ‘conj p q INSERT hs1’ >>
      reverse conj_tac >- gs[SUBSET_DEF] >> irule impE >>
      qexistsl_tac [‘conj p q’, ‘q’] >>
      simp[ded_hyp, Excl "stripimp_rwt", Excl "conjE", conjE2th] >>
      irule ded_R >> simp[PULL_EXISTS] >> qexists_tac ‘q INSERT hs1’ >>
      simp[SUBSET_DEF]) >>
  irule ded_R >> simp[PULL_EXISTS] >> qexists_tac ‘hs0’ >> gs[SUBSET_DEF]
QED

Theorem conj_comm:
  Γ ⊩ᵍ (conj p q ↔ conj q p)
Proof
  rw[IFF_def, ded_hyp]
QED

Theorem disj_comm:
  Γ ⊩ᵍ (disj p q ↔ disj q p)
Proof
  rw[IFF_def] >> irule disjE >>
  irule_at (Pos hd) ded_hyp >> irule_at (Pos hd) IN_INSERT1>>
  metis_tac[IN_INSERT, ded_rules, disjI1, disjI2, ded0_dedg]
QED

Definition fequiv_def:
  fequiv p q ⇔ ∅ ⊩⁰ (p ↔ q)
End
val _ = set_mapped_fixity{fixity = Infix(NONASSOC, 450), term_name = "fequiv",
                          tok = "≡"};

Theorem ded0g_coincide[simp]:
  ∅ ⊩⁰ p ⇔ ∅ ⊩ᵍ p
Proof
  rw[EQ_IMP_THM, ded0_dedg] >> irule closed_dedg_ded0 >> simp[]
QED

Theorem fequiv_REFL[simp]:
  p ≡ p
Proof
  simp[fequiv_def, IFF_def, ded_hyp]
QED

Theorem fequiv_SYM:
  p ≡ q ⇔ q ≡ p
Proof
  rw[fequiv_def, IFF_def, EQ_IMP_THM]
QED

Theorem fequiv_TRANS:
  p ≡ q ∧ q ≡ r ⇒ p ≡ r
Proof
  simp[fequiv_def, IFF_def] >> rpt strip_tac >>
  irule ded_MP >> goal_assum drule >> simp[] >> irule ded_R >>
  simp[PULL_EXISTS] >> goal_assum drule >> simp[]
QED

Theorem conj_CONG:
  p1 ≡ p2 ∧ q1 ≡ q2 ⇒
  conj p1 q1 ≡ conj p2 q2
Proof
  rw[fequiv_def, IFF_def] >>
  irule ded_R >> simp[PULL_EXISTS] >> goal_assum drule >> simp[SUBSET_DEF]
QED

Definition EXISTS_def:
  EXISTS x P = NEG (ALL x (NEG P))
End

Theorem EXISTS_I:
  acceptable x t ϕ ⇒ Γ ⊩ᵍ IMP (fsubst x t ϕ) (EXISTS x ϕ)
Proof
  rw[EXISTS_def] >> irule contrI >>
  qexists_tac ‘fsubst x t ϕ’ >> simp[ded_hyp] >>
  irule impE >> irule_at (Pos (el 2)) PL4 >>
  irule_at (Pos (el 2)) ded_MP >> irule_at (Pos hd) negnegEG >>
  irule_at (Pos hd) ded_hyp >> irule_at (Pos hd) IN_INSERT1 >>
  simp[] >> metis_tac[IN_INSERT1, ded_hyp]
QED

Theorem negnegE_thm[simp]:
  Γ ⊩ᵍ NEG (NEG p) ⇔ Γ ⊩ᵍ p
Proof
  metis_tac[ded_MP, negnegI, negnegEG]
QED

Theorem EXISTS_E:
  x ∉ fFV ψ ∧ (∀f. f ∈ Γ ⇒ x ∉ fFV f) ⇒
  ((EXISTS x ϕ) INSERT (ALL x (IMP ϕ ψ)) INSERT Γ) ⊩ᵍ ψ
Proof
  strip_tac >> irule contrI >> qexists_tac ‘EXISTS x ϕ’ >> conj_tac >>
  simp[ded_hyp] >> simp[EXISTS_def] >> irule UG >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >> irule contrI >> qexists_tac ‘ψ’ >>
  simp[ded_hyp] >> irule impE >> qexistsl_tac [‘ϕ’, ‘ψ’] >>
  simp[ded_hyp, Excl "stripimp_rwt"] >>
  conj_tac
  >- (irule impE >> qexistsl_tac [‘NEG(NEG ϕ)’, ‘ϕ’] >>
      simp[ded_hyp, negnegEG, Excl "negnegE_thm", Excl "stripimp_rwt"]) >>
  irule impE >>
  qexistsl_tac [‘ALL x (IMP ϕ ψ)’, ‘fsubst x (Var x) (IMP ϕ ψ)’] >>
  simp[ded_hyp, Excl "fsubst_id", PL4, Excl "fsubst_def",
       Excl "stripimp_rwt"] >>
  simp[ded_hyp, Excl "stripimp_rwt"]
QED


val _ = export_theory();
