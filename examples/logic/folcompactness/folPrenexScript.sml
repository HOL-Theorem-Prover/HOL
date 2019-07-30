open HolKernel Parse boolLib bossLib;

open pred_setTheory listTheory
open boolSimps combinTheory
open folLangTheory folModelsTheory

val _ = new_theory "folPrenex";

Definition qfree_def:
  (qfree False ⇔ T) ∧
  (qfree (Pred _ _) ⇔ T) ∧
  (qfree (IMP f1 f2) ⇔ qfree f1 ∧ qfree f2) ∧
  (qfree (FALL _ _) ⇔ F)
End

Theorem QFREE[simp]:
  (qfree False ⇔ T) ∧
  (qfree True ⇔ T) ∧
  (qfree (Pred n ts) ⇔ T) ∧
  (qfree (Not p) ⇔ qfree p) ∧
  (qfree (Or p q) ⇔ qfree p ∧ qfree q) ∧
  (qfree (And p q) ⇔ qfree p ∧ qfree q) ∧
  (qfree (Iff p q) ⇔ qfree p ∧ qfree q) ∧
  (qfree (IMP p q) ⇔ qfree p ∧ qfree q) ∧
  (qfree (FALL n p) ⇔ F) ∧
  (qfree (Exists n p) ⇔ F)
Proof
  simp[qfree_def, Exists_def, And_def, Or_def, True_def, Not_def, Iff_def] >>
  metis_tac[]
QED

Theorem qfree_formsubst[simp]:
  qfree (formsubst i p) ⇔ qfree p
Proof
  Induct_on ‘p’ >> simp[]
QED

Theorem qfree_bv_empty:
  qfree p ⇔ (BV p = ∅)
Proof
  Induct_on ‘p’ >> simp[]
QED

val (prenex_rules, prenex_ind, prenex_cases) = Hol_reln‘
  (∀p. qfree p ⇒ prenex p) ∧
  (∀x p. prenex p ⇒ prenex (FALL x p)) ∧
  (∀x p. prenex p ⇒ prenex (Exists x p))
’;

val (universal_rules, universal_ind, universal_cases) = Hol_reln‘
  (∀p. qfree p ⇒ universal p) ∧
  (∀x p. universal p ⇒ universal (FALL x p))
’;

Theorem prenex_INDUCT_NOT:
  ∀P. (∀p. qfree p ⇒ P p) ∧
      (∀x p. P p ⇒ P (FALL x p)) ∧
      (∀p. P p ⇒ P (Not p))
    ⇒
      ∀p. prenex p ⇒ P p
Proof
  ntac 2 strip_tac >> Induct_on ‘prenex’ >> simp[Exists_def]
QED

Theorem Exists_eqns[simp]:
  Exists x p ≠ Or q r ∧
  Exists x p ≠ Iff q r ∧
  Exists x p ≠ And q r ∧
  Exists x p ≠ FALL y q ∧
  Exists x p ≠ Pred n ts ∧
  ((Exists x p = IMP q r) ⇔ (q = FALL x (IMP p False)) ∧ (r = False)) ∧
  ((Exists x p = Exists y q) ⇔ (x = y) ∧ (p = q))
Proof
  simp[And_def, Or_def, Iff_def, Exists_def, Not_def] >> simp[EQ_SYM_EQ]
QED

Theorem PRENEX[simp]:
  (prenex False ⇔ T) ∧
  (prenex True ⇔ T) ∧
  (prenex (Pred n ts) ⇔ T) ∧
  (prenex (Not p) ⇔ qfree p ∨ ∃x q. (Not p = Exists x q) ∧ prenex q) ∧
  (prenex (Or p q) ⇔ qfree p ∧ qfree q) ∧
  (prenex (And p q) ⇔ qfree p ∧ qfree q) ∧
  (prenex (IMP p q) ⇔ qfree p ∧ qfree q ∨
                      ∃x r. (IMP p q = Exists x r) ∧ prenex r) ∧
  (prenex (Iff p q) ⇔ qfree p ∧ qfree q) ∧
  (prenex (FALL x p) ⇔ prenex p) ∧
  (prenex (Exists x p) ⇔ prenex p)
Proof
  rpt conj_tac >>
  simp[SimpLHS, Once prenex_cases] >>
  simp[And_def, Or_def, Iff_def, Not_def]
QED

Theorem formsubst_EQ[simp]:
  (∀i p. (formsubst i p = False) ⇔ (p = False)) ∧
  (∀i p. (False = formsubst i p) ⇔ (p = False)) ∧
  (∀i p n ts. (formsubst i p = Pred n ts) ⇔ ∃ts0. (p = Pred n ts0) ∧
                                       (ts = MAP (termsubst i) ts0)) ∧
  (∀i p q r. (formsubst i p = IMP q r) ⇔
             ∃q0 r0. (p = IMP q0 r0) ∧ (q = formsubst i q0) ∧
                     (r = formsubst i r0)) ∧
  (∀i p q. (formsubst i p = Not q) ⇔ ∃q0. (p = Not q0) ∧ (q = formsubst i q0))
Proof
  csimp[Not_def] >> rw[] >> Cases_on ‘p’ >> simp[EQ_SYM_EQ]
QED

Theorem formsubst_Not[simp]:
  formsubst i (Not p) = Not (formsubst i p)
Proof
  rw[Not_def]
QED

Theorem Not_11[simp]:
  (Not p = Not q) ⇔ (p = q)
Proof
  rw[Not_def]
QED

Theorem formsubst_EQ_FALL:
  (∃x q. formsubst i p = FALL x q) ⇔ (∃x q. p = FALL x q)
Proof
  Cases_on ‘p’ >> simp[]
QED

Theorem formsubst_EQ_Exists:
  (∃x q. formsubst i p = Exists x q) ⇔ (∃x q. p = Exists x q)
Proof
  Cases_on ‘p’ >> simp[] >>
  rename [‘subf2 = False’, ‘formsubst i subf1 = FALL _ _’] >>
  Cases_on ‘subf2 = False’ >> simp[] >>
  Cases_on ‘subf1’ >> simp[]
QED

Theorem prenex_formsubst[simp]:
  prenex (formsubst i p) ⇔ prenex p
Proof
  ‘(∀p. prenex p ⇒ ∀i. prenex (formsubst i p)) ∧
   (∀p. prenex p ⇒ ∀i q. (p = formsubst i q) ⇒ prenex q)’
    suffices_by metis_tac[] >>
  conj_tac >> Induct_on ‘prenex’ >> simp[] >> rw[]
  >- metis_tac[qfree_formsubst, prenex_rules]
  >- simp[Exists_def]
  >- metis_tac[qfree_formsubst, prenex_rules]
  >- (rename [‘FALL n p = formsubst i q’] >>
      ‘∃m r. q = FALL m r’ by metis_tac[formsubst_EQ_FALL] >> rw[] >> fs[] >>
      metis_tac[])
  >- (rename [‘Exists n p = formsubst i q’] >>
      ‘∃m r. q = Exists m r’ by metis_tac[formsubst_EQ_Exists] >> rw[] >>
      fs[Exists_def] >> metis_tac[])
QED

Definition size_def:
  (size False = 1) ∧
  (size (Pred _ _) = 1) ∧
  (size (IMP q r) = 1 + size q + size r) ∧
  (size (FALL _ q) = 1 + size q)
End

Theorem SIZE[simp]:
  (size False = 1) ∧
  (size True = 3) ∧
  (size (Pred n ts) = 1) ∧
  (size (Not p) = 2 + size p) ∧
  (size (Or p q) = size p + 2 * size q + 2) ∧
  (size (And p q) = size p + 2 * size q + 10) ∧
  (size (Iff p q) = 3 * size p + 3 * size q + 13) ∧
  (size (IMP p q) = size p + size q + 1) ∧
  (size (FALL x p) = 1 + size p) ∧
  (size (Exists x p) = 5 + size p)
Proof
  simp[And_def, Or_def, Iff_def, size_def, Exists_def, Not_def, True_def]
QED

Theorem size_formsubst[simp]:
  ∀i. size (formsubst i p) = size p
Proof
  Induct_on ‘p’ >> simp[]
QED

Definition PPAT_def:
  PPAT A B C p =
    case some (x,q). p = Exists x q of
        SOME (x,q) => B x q
      | NONE =>
        case p of
            FALL x q => A x q
          | _ => C p
End

Theorem PPAT[simp]:
  (PPAT A B C (FALL x p) = A x p) ∧
  (PPAT A B C (Exists x p) = B x p) ∧
  ((!x q. p ≠ FALL x q) ∧ (∀x q. p ≠ Exists x q) ⇒ (PPAT A B C p = C p))
Proof
  simp[PPAT_def, pairTheory.ELIM_UNCURRY]>>
  ‘∀a b. (λy. (a:num = FST y) ∧ (b:form = SND y)) = (λp. p = (a,b))’
     by simp[FUN_EQ_THM, pairTheory.FORALL_PROD, EQ_SYM_EQ] >>
  simp[] >>
  Cases_on ‘p’ >> simp[Exists_def]
QED

Theorem PPAT_CONG[defncong]:
  ∀A1 A2 B1 B2 C1 C2 q q'.
    (∀x p. size p < size q ⇒ (A1 x p = A2 x p)) ∧
    (∀x p. size p < size q ⇒ (B1 x p = B2 x p)) ∧ (∀p. C1 p = C2 p) ∧
    (q = q') ⇒
    (PPAT A1 B1 C1 q = PPAT A2 B2 C2 q')
Proof
  rw[] >>
  Cases_on ‘∃n p0. q = Exists n p0’ >> fs[] >>
  Cases_on ‘q’ >> simp[]
QED

Definition prenexR_def:
  prenexR p q =
    PPAT
      (λx q0. let y = VARIANT (FV p ∪ FV(FALL x q0))
              in
                FALL y (prenexR p (formsubst V⦇x ↦ V y⦈ q0)))
      (λx q0. let y = VARIANT (FV p ∪ FV(Exists x q0))
              in
                Exists y (prenexR p (formsubst V⦇x ↦ V y⦈ q0)))
      (λq. IMP p q)
      q
Termination
  WF_REL_TAC ‘measure (size o SND)’ >> simp[]
End

Theorem prenexR_thm[simp]:
  (prenexR p (FALL x q) = let y = VARIANT (FV p ∪ FV (FALL x q))
                          in
                            FALL y (prenexR p (formsubst V⦇x ↦ V y⦈ q))) ∧
  (prenexR p (Exists x q) = let y = VARIANT (FV p ∪ FV(Exists x q))
                            in
                              Exists y (prenexR p (formsubst V⦇x ↦ V y⦈ q))) ∧
  (qfree q ⇒ (prenexR p q = IMP p q))
Proof
  rpt conj_tac >> simp[SimpLHS, Once prenexR_def] >> simp[] >> strip_tac >>
  ‘(∀x r. q ≠ FALL x r) ∧ (∀x r. q ≠ Exists x r)’
     by (rpt strip_tac >> fs[]) >>
  simp[]
QED

Definition prenexL_def:
  prenexL p q =
    PPAT (λx p0. let y = VARIANT (FV (FALL x p0) ∪ FV q)
                 in
                   Exists y (prenexL (formsubst V⦇x ↦ V y⦈ p0) q))
         (λx p0. let y = VARIANT (FV (Exists x p0) ∪ FV q)
                 in
                   FALL y (prenexL (formsubst V⦇x ↦ V y⦈ p0) q))
         (λp. prenexR p q) p
Termination
  WF_REL_TAC ‘measure (size o FST)’ >> simp[]
End

Theorem prenexL_thm[simp]:
  (prenexL (FALL x p) q = let y = VARIANT (FV (FALL x p) ∪ FV q)
                          in
                            Exists y (prenexL (formsubst V⦇x ↦ V y⦈ p) q)) ∧
  (prenexL (Exists x p) q = let y = VARIANT (FV (Exists x p) ∪ FV q)
                            in
                              FALL y (prenexL (formsubst V⦇x ↦ V y⦈ p) q)) ∧
  (qfree p ⇒ (prenexL p q = prenexR p q))
Proof
  rpt conj_tac >> simp[Once prenexL_def, SimpLHS] >> simp[] >> strip_tac >>
  ‘(∀x r. p ≠ FALL x r) ∧ (∀x r. p ≠ Exists x r)’
     by (rpt strip_tac >> fs[]) >>
  simp[]
QED

Definition Prenex_def[simp]:
  (Prenex False = False) ∧
  (Prenex (Pred n ts) = Pred n ts) ∧
  (Prenex (IMP f1 f2) = prenexL (Prenex f1) (Prenex f2)) ∧
  (Prenex (FALL x f) = FALL x (Prenex f))
End

Theorem prenexR_language[simp]:
  ∀p. language {prenexR p q} = language {IMP p q}
Proof
  completeInduct_on ‘size q’ >> fs[PULL_FORALL, language_SING] >> rpt gen_tac >>
  disch_then SUBST_ALL_TAC >>
  Cases_on ‘∃x q0. q = Exists x q0’ >> fs[]
  >- (simp[Exists_def, Not_def, form_functions_formsubst] >>
      simp_tac (srw_ss() ++ COND_elim_ss) [combinTheory.APPLY_UPDATE_THM]) >>
  Cases_on ‘∃x q0. q = FALL x q0’ >> fs[]
  >- simp_tac (srw_ss() ++ COND_elim_ss)
       [form_functions_formsubst,combinTheory.APPLY_UPDATE_THM] >>
  conj_tac >> simp[Once prenexR_def]
QED

Theorem prenexL_language[simp]:
  ∀q. language {prenexL p q} = language {IMP p q}
Proof
  completeInduct_on ‘size p’ >> fs[PULL_FORALL] >> rpt gen_tac >>
  disch_then SUBST_ALL_TAC >>
  Cases_on ‘∃x p0. p = Exists x p0’ >> fs[] >> fs[]
  >- (fs[Exists_def, Not_def, form_functions_formsubst, language_SING] >>
      simp_tac (srw_ss() ++ COND_elim_ss) [combinTheory.APPLY_UPDATE_THM]) >>
  Cases_on ‘∃x p0. p = FALL x p0’ >> fs[]
  >- full_simp_tac (srw_ss() ++ COND_elim_ss)
       [language_SING,form_functions_formsubst,APPLY_UPDATE_THM,Exists_def,
        Not_def] >>
  simp[Once prenexL_def]
QED

Theorem prenex_lemma_forall:
  P ∧ (FV f1 = FV f2) ∧ (language {f1} = language {f2}) ∧
  (∀M:α model v. M.Dom ≠ ∅ ⇒ (holds M v f1 ⇔ holds M v f2)) ⇒
  P ∧ (FV (FALL z f1) = FV (FALL z f2)) ∧
  (language {FALL z f1} = language {FALL z f2}) ∧
  ∀M:α model v. M.Dom ≠ ∅ ⇒ (holds M v (FALL z f1) ⇔ holds M v (FALL z f2))
Proof
  rw[language_SING]
QED

Theorem prenex_lemma_exists:
  P ∧ (FV f1 = FV f2) ∧ (language {f1} = language {f2}) ∧
  (∀M:α model v. M.Dom ≠ ∅ ⇒ (holds M v f1 ⇔ holds M v f2)) ⇒
  P ∧ (FV (Exists z f1) = FV (Exists z f2)) ∧
  (language {Exists z f1} = language {Exists z f2}) ∧
  ∀M:α model v. M.Dom ≠ ∅ ⇒ (holds M v (Exists z f1) ⇔ holds M v (Exists z f2))
Proof
  rw[language_SING, Exists_def, Not_def]
QED

Theorem prenex_rename1[simp]:
  ∀f x y. prenex (formsubst V⦇x ↦ V y⦈ f) ⇔ prenex f
Proof
  completeInduct_on ‘size f’ >> fs[PULL_FORALL]
QED

Theorem tfresh_rename_inverts:
  ∀t x y. y ∉ FVT t ⇒ (termsubst V⦇y ↦ V x⦈ (termsubst V⦇x ↦ V y⦈ t) = t)
Proof
  ho_match_mp_tac term_induct >> simp[] >> rw[MEM_MAP, MAP_MAP_o]
  >- rw[combinTheory.APPLY_UPDATE_THM] >>
  irule EQ_TRANS >> qexists_tac ‘MAP I ts’ >> reverse conj_tac
  >- simp[] >>
  irule listTheory.MAP_CONG >> simp[] >> qx_gen_tac ‘t0’ >> strip_tac >>
  first_x_assum irule >> metis_tac[]
QED

Theorem holds_nonFV:
  v ∉ FV f ⇒ (holds M i⦇ v ↦ t ⦈ f ⇔ holds M i f)
Proof
  strip_tac >> irule holds_valuation >>
  simp[combinTheory.APPLY_UPDATE_THM] >> rw[] >> fs[]
QED

Theorem prenexR_FV[simp]:
  FV (prenexR p q) = FV p ∪ FV q
Proof
  completeInduct_on ‘size q’ >> fs[PULL_FORALL] >> rw[] >>
  Cases_on ‘∃v q0. q = Exists v q0’ >> fs[]
  >- (simp_tac (srw_ss() ++ COND_elim_ss)
       [EXTENSION, formsubst_FV, termsubst_fvt, APPLY_UPDATE_THM] >>
      qmatch_goalsub_abbrev_tac ‘VARIANT s’ >>
      qabbrev_tac ‘vv = VARIANT s’ >>
      ‘vv ∉ s’ by simp[Abbr‘vv’, Abbr‘s’, VARIANT_FINITE] >>
      Q.UNABBREV_TAC ‘s’ >> fs[] >> gen_tac >>
      eq_tac >> rw[] >> simp[] >> fs[] >> metis_tac[]) >>
  Cases_on ‘∃v q0. q = FALL v q0’ >> fs[]
  >- (simp_tac (srw_ss() ++ COND_elim_ss)
       [EXTENSION, formsubst_FV, termsubst_fvt, APPLY_UPDATE_THM] >>
      qmatch_goalsub_abbrev_tac ‘VARIANT s’ >>
      qabbrev_tac ‘vv = VARIANT s’ >>
      ‘vv ∉ s’ by simp[Abbr‘vv’, Abbr‘s’, VARIANT_FINITE] >>
      Q.UNABBREV_TAC ‘s’ >> fs[] >> gen_tac >>
      eq_tac >> rw[] >> simp[] >> fs[] >> metis_tac[]) >>
  simp[prenexR_def]
QED

Theorem prenexR_prenex:
  qfree p ∧ prenex q ⇒ prenex (prenexR p q)
Proof
  completeInduct_on ‘size q’ >> fs[PULL_FORALL] >> gen_tac >>
  disch_then SUBST_ALL_TAC >>
  simp[Once prenex_cases, SimpLHS] >> dsimp[]
QED

Theorem prenexR_holds:
  ∀M v. M.Dom ≠ ∅ ⇒ (holds M v (prenexR p q) ⇔ holds M v (IMP p q))
Proof
  completeInduct_on ‘size q’ >> fs[PULL_FORALL] >> rw[] >>
  Cases_on ‘∃v q0. q = Exists v q0’ >> fs[] >> fs[]
  >- (qmatch_goalsub_abbrev_tac ‘VARIANT ss’ >>
      ‘VARIANT ss ∉ ss’ by simp[VARIANT_FINITE, Abbr‘ss’] >>
      qabbrev_tac ‘vv = VARIANT ss’ >>
      rename [‘holds M vln⦇ vv ↦ _ ⦈ f1’, ‘formsubst _ f2’] >>
      ‘vv ∉ FV f1’ by fs[Abbr‘ss’] >>
      ‘∀t. holds M vln⦇vv ↦ t⦈ f1 ⇔ holds M vln f1’
          by (gen_tac >> irule holds_valuation >>
              metis_tac[combinTheory.APPLY_UPDATE_THM]) >>
      simp[] >> Cases_on ‘holds M vln f1’ >> simp[]
      >- (AP_TERM_TAC >> ABS_TAC >>
          rename [‘d ∈ M.Dom’] >> Cases_on ‘d ∈ M.Dom’ >>
          simp[holds_formsubst] >> irule holds_valuation >>
          rw[combinTheory.APPLY_UPDATE_THM] >> fs[Abbr‘ss’] >> metis_tac[]) >>
      metis_tac[MEMBER_NOT_EMPTY]) >>
  Cases_on ‘∃v q0. q = FALL v q0’ >> fs[] >> fs[]
  >- (qmatch_goalsub_abbrev_tac ‘VARIANT ss’ >>
      ‘VARIANT ss ∉ ss’ by simp[VARIANT_FINITE, Abbr‘ss’] >>
      qabbrev_tac ‘vv = VARIANT ss’ >>
      rename [‘holds M vln⦇ vv ↦ _ ⦈ f1’, ‘formsubst V⦇v₀ ↦ V vv⦈ f2’] >>
      ‘vv ∉ FV f1’ by fs[Abbr‘ss’] >>
      ‘∀d. holds M vln⦇vv ↦ d⦈ f1 ⇔ holds M vln f1’
        by (gen_tac >> irule holds_valuation >> simp[APPLY_UPDATE_THM] >>
            metis_tac[]) >>
      simp[] >> Cases_on ‘holds M vln f1’ >> simp[holds_formsubst] >>
      AP_TERM_TAC >> ABS_TAC >> rename [‘d ∈ M.Dom’] >> Cases_on ‘d ∈ M.Dom’ >>
      simp[] >> irule holds_valuation >> simp[APPLY_UPDATE_THM] >>
      rw[APPLY_UPDATE_THM] >> fs[Abbr‘ss’] >> metis_tac[]) >>
  simp[Once prenexR_def]
QED

Theorem prenexL_FV[simp]:
  FV (prenexL p q) = FV p ∪ FV q
Proof
  completeInduct_on ‘size p’ >> fs[PULL_FORALL] >> rw[] >>
  Cases_on ‘∃v p1. p = Exists v p1’ >> fs[]
  >- (qmatch_goalsub_abbrev_tac ‘VARIANT ss’ >>
      ‘VARIANT ss ∉ ss’ by fs[Abbr‘ss’, VARIANT_FINITE] >>
      simp[formsubst_FV, combinTheory.APPLY_UPDATE_THM] >>
      simp[EXTENSION] >> qx_gen_tac ‘n’ >> eq_tac >>
      asm_simp_tac(srw_ss() ++ COND_elim_ss) [] >> rw[]
      >- simp[Abbr‘ss’]
      >- simp[Abbr‘ss’]
      >- (dsimp[] >> fs[Abbr‘ss’])
      >- metis_tac[]) >>
  Cases_on ‘∃v p1. p = FALL v p1’ >> fs[]
  >- (qmatch_goalsub_abbrev_tac ‘VARIANT ss’ >>
      ‘VARIANT ss ∉ ss’ by fs[Abbr‘ss’, VARIANT_FINITE] >>
      simp[formsubst_FV, combinTheory.APPLY_UPDATE_THM] >>
      simp[EXTENSION] >> qx_gen_tac ‘n’ >> eq_tac >>
      asm_simp_tac(srw_ss() ++ COND_elim_ss) [] >> rw[]
      >- simp[Abbr‘ss’]
      >- simp[Abbr‘ss’]
      >- (dsimp[] >> fs[Abbr‘ss’])
      >- metis_tac[]) >>
  simp[prenexL_def]
QED

Theorem prenexL_prenex[simp]:
  prenex p ∧ prenex q ⇒ prenex (prenexL p q)
Proof
  completeInduct_on ‘size p’ >> fs[PULL_FORALL] >> rw[] >>
  Cases_on ‘∃v p0. p = Exists v p0’ >> fs[] >>
  Cases_on ‘∃v p0. p = FALL v p0’ >> fs[] >> fs[] >>
  simp[prenexL_def] >>
  ‘qfree p’ suffices_by metis_tac[prenexR_prenex] >>
  Q.UNDISCH_THEN ‘prenex p’ mp_tac >> simp[Once prenex_cases]
QED

Theorem prenexL_holds[simp]:
   ∀M vln. M.Dom ≠ ∅ ⇒ (holds M vln (prenexL p q) ⇔ holds M vln (IMP p q))
Proof
  completeInduct_on ‘size p’ >> fs[PULL_FORALL] >> rw[] >>
  Cases_on ‘∃v p0. p = Exists v p0’ >> fs[]
  >- (qmatch_goalsub_abbrev_tac ‘VARIANT ss’ >>
      ‘VARIANT ss ∉ ss’ by simp[VARIANT_FINITE, Abbr‘ss’] >>
      ‘∀d. holds M vln⦇ VARIANT ss ↦ d⦈ q ⇔ holds M vln q’
        by (gen_tac >> irule holds_valuation >> rw[APPLY_UPDATE_THM] >>
            fs[Abbr‘ss’]) >> simp[PULL_EXISTS] >>
      AP_TERM_TAC >> ABS_TAC >> rename [‘d ∈ M.Dom’] >> Cases_on ‘d ∈ M.Dom’ >>
      simp[] >> AP_THM_TAC >> AP_TERM_TAC >>
      simp[holds_formsubst] >> irule holds_valuation >> rw[APPLY_UPDATE_THM] >>
      fs[Abbr‘ss’] >> metis_tac[]) >>
  Cases_on ‘∃v p0. p = FALL v p0’ >> fs[]
  >- (qmatch_goalsub_abbrev_tac ‘VARIANT ss’ >>
      ‘VARIANT ss ∉ ss’ by simp[VARIANT_FINITE, Abbr‘ss’] >>
      simp[GSYM LEFT_EXISTS_IMP_THM] >>
      ‘∀d. holds M vln⦇ VARIANT ss ↦ d ⦈ q ⇔ holds M vln q’
        by (gen_tac >> irule holds_nonFV >> fs[Abbr‘ss’]) >>
      simp[] >> Cases_on ‘holds M vln q’ >> simp[]
      >- metis_tac[MEMBER_NOT_EMPTY] >>
      AP_TERM_TAC >> ABS_TAC >> rename [‘d ∈ M.Dom’] >> Cases_on ‘d ∈ M.Dom’ >>
      simp[] >> simp[holds_formsubst] >> irule holds_valuation >>
      rw[APPLY_UPDATE_THM] >> fs[Abbr‘ss’] >> metis_tac[]) >>
  simp[Once prenexL_def, prenexR_holds]
QED

Theorem prenex_Prenex[simp]:
  prenex (Prenex f)
Proof
  Induct_on ‘f’ >> simp[]
QED

Theorem FV_Prenex[simp]:
  FV (Prenex f) = FV f
Proof
  Induct_on ‘f’ >> simp[]
QED

Theorem holds_Prenex[simp]:
  ∀vln. M.Dom ≠ ∅ ⇒ (holds M vln (Prenex f) ⇔ holds M vln f)
Proof
  Induct_on ‘f’ >> simp[prenexL_holds]
QED

Theorem language_Prenex[simp]:
  language {Prenex f} = language {f}
Proof
  Induct_on ‘f’ >> simp[] >> fs[language_SING]
QED

Theorem form_functions_prenexR[simp]:
  ∀f1 f2. form_functions (prenexR f1 f2) = form_functions f1 ∪ form_functions f2
Proof
  ho_match_mp_tac prenexR_ind >> rpt strip_tac >> simp[Once prenexR_def] >>
  Cases_on‘∃x f2'. f2 = Exists x f2'’ >>
  full_simp_tac (srw_ss() ++ COND_elim_ss)
    [form_functions_formsubst, combinTheory.APPLY_UPDATE_THM] >>
  Cases_on ‘∃x f2'. f2 = FALL x f2'’ >>
  full_simp_tac (srw_ss() ++ COND_elim_ss)
    [form_functions_formsubst, combinTheory.APPLY_UPDATE_THM]
QED

Theorem form_functions_prenexL[simp]:
  ∀f1 f2. form_functions (prenexL f1 f2) = form_functions f1 ∪ form_functions f2
Proof
  ho_match_mp_tac prenexL_ind >> rpt strip_tac >>
  simp[Once prenexL_def] >>
  Cases_on‘∃x f1'. f1 = Exists x f1'’ >>
  full_simp_tac (srw_ss() ++ COND_elim_ss)
    [form_functions_formsubst, combinTheory.APPLY_UPDATE_THM] >>
  Cases_on ‘∃x f1'. f1 = FALL x f1'’ >>
  full_simp_tac (srw_ss() ++ COND_elim_ss)
    [form_functions_formsubst, combinTheory.APPLY_UPDATE_THM]
QED

Theorem form_functions_Prenex[simp]:
  form_functions (Prenex f) = form_functions f
Proof
  Induct_on ‘f’ >> simp[]
QED

Theorem form_predicates_prenexR[simp]:
  ∀f1 f2.
    form_predicates (prenexR f1 f2) = form_predicates f1 ∪ form_predicates f2
Proof
  ho_match_mp_tac prenexR_ind >> rpt strip_tac >>
  simp[Once prenexR_def] >>
  Cases_on‘∃x f2'. f2 = Exists x f2'’ >> fs [] >>
  Cases_on ‘∃x f2'. f2 = FALL x f2'’ >> fs []
QED

Theorem form_predicates_prenexL[simp]:
  ∀f1 f2.
    form_predicates (prenexL f1 f2) = form_predicates f1 ∪ form_predicates f2
Proof
  ho_match_mp_tac prenexL_ind >> rpt strip_tac >>
  simp[Once prenexL_def] >>
  Cases_on‘∃x f1'. f1 = Exists x f1'’ >> fs [] >>
  Cases_on ‘∃x f1'. f1 = FALL x f1'’ >> fs []
QED

Theorem form_predicates_Prenex[simp]:
  form_predicates (Prenex p) = form_predicates p
Proof
  Induct_on ‘p’ >> simp[]
QED


val _ = export_theory();
