open HolKernel Parse boolLib bossLib;

open listTheory pred_setTheory
open folLangTheory

val _ = new_theory "folModels";

val MAP_CONG' = REWRITE_RULE [GSYM AND_IMP_INTRO] MAP_CONG

val _ = Datatype‘
  model = <| Dom : α set ; Fun : num -> α list -> α ;
             Pred : num -> α list -> bool |>
’;

Definition valuation_def:
  valuation M v ⇔ ∀n. v n ∈ M.Dom
End

Theorem upd_valuation[simp]:
  valuation M v ∧ a ∈ M.Dom ⇒ valuation M v⦇x ↦ a⦈
Proof
  simp[valuation_def, combinTheory.APPLY_UPDATE_THM] >> rw[] >> rw[]
QED

Definition termval_def[simp]:
  (termval M v (V x) = v x) ∧
  (termval M v (Fn f l) = M.Fun f (MAP (termval M v) l))
Termination
  WF_REL_TAC ‘measure (term_size o SND o SND)’ >> simp[]
End

Definition holds_def:
  (holds M v False ⇔ F) ∧
  (holds M v (Pred a l) ⇔ M.Pred a (MAP (termval M v) l)) ∧
  (holds M v (IMP f1 f2) ⇔ (holds M v f1 ⇒ holds M v f2)) ∧
  (holds M v (FALL x f) ⇔ ∀a. a ∈ M.Dom ⇒ holds M v⦇x ↦ a⦈ f)
End

Definition hold_def:
  hold M v fms ⇔ ∀p. p ∈ fms ⇒ holds M v p
End

Definition satisfies_def:
  (satisfies) M fms ⇔ ∀v p. valuation M v ∧ p ∈ fms ⇒ holds M v p
End

val _ = set_fixity "satisfies" (Infix(NONASSOC, 450))

Theorem satisfies_SING[simp]:
  M satisfies {p} ⇔ ∀v. valuation M v ⇒ holds M v p
Proof
  simp[satisfies_def]
QED

Theorem HOLDS[simp]:
  (holds M v False ⇔ F) ∧
  (holds M v True ⇔ T) ∧
  (holds M v (Pred a l) ⇔ M.Pred a (MAP (termval M v) l)) ∧
  (holds M v (Not p) ⇔ ~holds M v p) ∧
  (holds M v (Or p q) ⇔ holds M v p ∨ holds M v q) ∧
  (holds M v (And p q) ⇔ holds M v p ∧ holds M v q) ∧
  (holds M v (Iff p q) ⇔ (holds M v p ⇔ holds M v q)) ∧
  (holds M v (IMP p q) ⇔ (holds M v p ⇒ holds M v q)) ∧
  (holds M v (FALL x p) ⇔ ∀a. a ∈ M.Dom ⇒ holds M v⦇x ↦ a⦈ p) ∧
  (holds M v (Exists x p) ⇔ ∃a. a ∈ M.Dom ∧ holds M v⦇x ↦ a⦈ p)
Proof
  simp[holds_def, True_def, Not_def, Exists_def, Or_def, And_def, Iff_def] >>
  metis_tac[]
QED

Theorem termval_valuation:
  ∀t M v1 v2.
     (∀x. x ∈ FVT t ⇒ (v1 x = v2 x)) ⇒
     (termval M v1 t = termval M v2 t)
Proof
  ho_match_mp_tac term_induct >> simp[MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> AP_TERM_TAC >>
  irule MAP_CONG >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  metis_tac[]
QED

Theorem holds_valuation:
  ∀M p v1 v2.
     (∀x. x ∈ FV p ⇒ (v1 x = v2 x)) ⇒
     (holds M v1 p ⇔ holds M v2 p)
Proof
  Induct_on ‘p’ >> simp[MEM_MAP, PULL_EXISTS]
  >- (rpt strip_tac >> AP_TERM_TAC >> irule MAP_CONG >> simp[] >>
      rpt strip_tac >> irule termval_valuation >> metis_tac[])
  >- metis_tac[]
  >- (rpt strip_tac >> AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >>
      first_x_assum irule >> rpt strip_tac >>
      rename [‘var ∈ FV fm’, ‘_ ⦇ u ↦ a ⦈’] >>
      Cases_on ‘var = u’ >> simp[combinTheory.UPDATE_APPLY])
QED

Definition satisfiable_def:
  satisfiable (:α) fms ⇔ ∃M:α model. M.Dom ≠ ∅ ∧ M satisfies fms
End

Definition valid_def:
  valid (:α) fms ⇔ ∀M:α model. M satisfies fms
End

Definition entails_def:
  entails (:α) Γ p ⇔
    ∀M:α model v. hold M v Γ ⇒ holds M v p
End

Definition equivalent_def:
  equivalent (:α) p q ⇔
    ∀M:α model v. holds M v p ⇔ holds M v q
End

Definition interpretation_def:
  interpretation (fns,preds) M ⇔
    ∀f l. (f, LENGTH l) ∈ fns ∧ (∀x. MEM x l ⇒ x ∈ M.Dom) ⇒
          M.Fun f l ∈ M.Dom
End

Theorem interpretation_termval:
  ∀t M v. interpretation (term_functions t,preds) M ∧ valuation M v ⇒
          termval M v t ∈ M.Dom
Proof
  simp[interpretation_def] >> ho_match_mp_tac term_induct >> rpt strip_tac
  >- fs[valuation_def] >>
  fs[MEM_MAP, PULL_EXISTS] >>
  first_assum irule >> simp[MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >> rpt strip_tac >>
  last_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem interpretation_sublang:
  fns2 ⊆ fns1 ∧ interpretation (fns1,preds) M ⇒ interpretation (fns2,preds) M
Proof
  simp[SUBSET_DEF, interpretation_def]
QED

Theorem termsubst_termval:
  (M.Fun = Fn) ⇒ ∀t v. termsubst v t = termval M v t
Proof
  strip_tac >> ho_match_mp_tac term_induct >> simp[Cong MAP_CONG']
QED

Theorem termval_triv:
  (M.Fun = Fn) ⇒ ∀t. termval M V t = t
Proof
  strip_tac >> ho_match_mp_tac term_induct >> simp[Cong MAP_CONG']
QED

Theorem termval_termsubst:
  ∀t v i. termval M v (termsubst i t) = termval M (termval M v o i) t
Proof
  ho_match_mp_tac term_induct >>
  simp[MAP_MAP_o, combinTheory.o_ABS_R, Cong MAP_CONG']
QED

Theorem holds_formsubst :
  ∀v i. holds M v (formsubst i p) ⇔ holds M (termval M v o i) p
Proof
  Induct_on ‘p’ >> simp[MAP_MAP_o, termval_termsubst, Cong MAP_CONG'] >>
  rpt gen_tac >>
  ho_match_mp_tac
    (METIS_PROVE [] “
       (∀a. P a ⇒ (Q a ⇔ R a)) ⇒ ((∀a. P a ⇒ Q a) ⇔ (∀a. P a ⇒ R a))
     ”) >>
  qx_gen_tac ‘a’ >> strip_tac >> csimp[combinTheory.UPDATE_APPLY] >>
  reverse COND_CASES_TAC >> simp[]
  >- (irule holds_valuation >> rw[] >>
      simp[combinTheory.APPLY_UPDATE_THM] >> rw[combinTheory.UPDATE_APPLY] >>
      irule termval_valuation >> metis_tac[combinTheory.APPLY_UPDATE_THM]) >>
  fs[] >> Q.MATCH_GOALSUB_ABBREV_TAC ‘VARIANT (FV f)’ >>
  irule holds_valuation >> qx_gen_tac ‘u’ >> strip_tac >> simp[] >>
  rw[combinTheory.APPLY_UPDATE_THM] >>
  irule termval_valuation >> qx_gen_tac ‘uu’ >> strip_tac >>
  rw[combinTheory.APPLY_UPDATE_THM] >>
  rename [‘VARIANT (FV f) ∈ FVT (i u)’] >>
  ‘FVT (i u) ⊆ FV f’ suffices_by metis_tac[FV_FINITE, VARIANT_NOTIN_SUBSET] >>
  simp[formsubst_FV, Abbr‘f’, SUBSET_DEF] >>
  metis_tac[combinTheory.APPLY_UPDATE_THM]
QED

Theorem holds_formsubst1:
  holds M σ (formsubst V⦇ x ↦ t ⦈ p) ⇔ holds M σ⦇ x ↦ termval M σ t⦈ p
Proof
  simp[holds_formsubst] >> irule holds_valuation >>
  rw[combinTheory.APPLY_UPDATE_THM]
QED

Theorem holds_rename:
  holds M σ (formsubst V⦇ x ↦ V y ⦈ p) ⇔ holds M σ⦇ x ↦ σ y ⦈ p
Proof
  simp[holds_formsubst1]
QED

Theorem holds_alpha_forall:
  y ∉ FV (FALL x p) ⇒
  (holds M v (FALL y (formsubst V⦇ x ↦ V y⦈ p)) ⇔
   holds M v (FALL x p))
Proof
  simp[combinTheory.APPLY_UPDATE_ID, DISJ_IMP_THM, holds_formsubst1,
       combinTheory.UPDATE_APPLY, combinTheory.UPDATE_EQ] >> strip_tac >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >>
  irule holds_valuation >> rpt strip_tac >>
  rw[combinTheory.APPLY_UPDATE_THM] >> fs[]
QED

Theorem holds_alpha_exists:
  y ∉ FV (Exists x p) ⇒
  (holds M v (Exists y (formsubst V⦇ x ↦ V y⦈ p)) ⇔
   holds M v (Exists x p))
Proof
  simp[combinTheory.APPLY_UPDATE_ID, DISJ_IMP_THM, holds_formsubst1,
       combinTheory.UPDATE_APPLY, combinTheory.UPDATE_EQ] >> strip_tac >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >>
  irule holds_valuation >> rpt strip_tac >>
  rw[combinTheory.APPLY_UPDATE_THM] >> fs[]
QED

Theorem termval_functions:
  ∀t. (∀f zs. (f,LENGTH zs) ∈ term_functions t ⇒ (M.Fun f zs = M'.Fun f zs)) ⇒
      ∀v. termval M v t = termval M' v t
Proof
  ho_match_mp_tac term_induct >>
  simp[MEM_MAP, PULL_EXISTS, DISJ_IMP_THM, FORALL_AND_THM] >> rw[] >>
  AP_TERM_TAC >> irule MAP_CONG' >> rw[] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem holds_functions:
  (M2.Dom = M1.Dom) ∧ (∀P zs. M2.Pred P zs ⇔ M1.Pred P zs) ∧
  (∀f zs. (f,LENGTH zs) ∈ form_functions p ⇒ (M2.Fun f zs = M1.Fun f zs))
 ⇒
  ∀v. holds M2 v p ⇔ holds M1 v p
Proof
  Induct_on ‘p’ >> simp[MEM_MAP,PULL_EXISTS] >> rw[] >> AP_TERM_TAC >>
  irule MAP_CONG' >> rw[] >> metis_tac[termval_functions]
QED

Theorem holds_predicates:
  (M2.Dom = M1.Dom) ∧ (∀f zs. M2.Fun f zs = M1.Fun f zs) ∧
  (∀P zs. (P,LENGTH zs) ∈ form_predicates p ⇒ (M2.Pred P zs ⇔ M1.Pred P zs))
⇒
  ∀v. holds M2 v p ⇔ holds M1 v p
Proof
  Induct_on ‘p’ >> rw[] >> AP_TERM_TAC >> irule MAP_CONG' >> rw[] >>
  irule termval_functions >> simp[]
QED

Theorem holds_uclose:
  (∀v. valuation M v ⇒ holds M v (FALL x p)) ⇔
  (M.Dom = ∅) ∨ ∀v. valuation M v ⇒ holds M v p
Proof
  simp[] >> Cases_on ‘M.Dom = ∅’ >> simp[] >>
  metis_tac[combinTheory.APPLY_UPDATE_ID, upd_valuation, valuation_def]
QED

(* ultimate objective:
Theorem compactness:
  (∀t. FINITE t ∧ t ⊆ s ⇒
       ∃M. interpretation (language s) M ∧ M.Dom ≠ ∅ ∧ M satisfies t)
⇒
  ∃C. interpretation (language s) C ∧ C.Dom ≠ ∅ ∧ C satisfies s
Proof
  cheat
QED
*)

val _ = export_theory();
