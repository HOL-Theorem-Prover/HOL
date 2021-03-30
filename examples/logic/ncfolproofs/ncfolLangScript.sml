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
[PL3:] (∀A B. ded Hs ((⌁A  ⥰ ⌁B) ⥰ (⌁A  ⥰ B) ⥰ A)) ∧
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
  ‘ded Hs (ϕ ⥰ (ϕ ⥰ ϕ) ⥰ ϕ)’ by metis_tac [ded_rules] >>
  ‘ded Hs ((ϕ ⥰ (ϕ ⥰ ϕ) ⥰ ϕ) ⥰ (ϕ ⥰ (ϕ ⥰ ϕ)) ⥰ (ϕ ⥰ ϕ))’
    by metis_tac [ded_rules] >>
  dxrule_all_then assume_tac ded_MP >>
  drule_then irule ded_MP >>
  irule_at Any PL1
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

val _ = export_theory();
