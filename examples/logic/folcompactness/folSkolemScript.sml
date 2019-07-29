open HolKernel Parse boolLib bossLib;

open boolSimps pred_setTheory listTheory
open folPrenexTheory folModelsTheory folLangTheory

val _ = new_theory "folSkolem";

Theorem holds_exists_lemma:
  ∀p t x M v preds.
     interpretation (term_functions t, preds) M ∧
     valuation M v ∧
     holds M v (formsubst V⦇x ↦ t⦈ p)
    ⇒
     holds M v (Exists x p)
Proof
  rw[holds_formsubst1] >> metis_tac[interpretation_termval]
QED

Definition Skolem1_def:
  Skolem1 f x p =
    formsubst V⦇ x ↦ Fn f (MAP V (SET_TO_LIST (FV (Exists x p))))⦈ p
End

Theorem FV_Skolem1[simp]:
  FV (Skolem1 f x p) = FV (Exists x p)
Proof
  simp[Skolem1_def, formsubst_FV, combinTheory.APPLY_UPDATE_THM, EXTENSION,
       EQ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
  simp_tac (srw_ss() ++ COND_elim_ss ++ DNF_ss) [EXISTS_OR_THM, MEM_MAP]
QED

Theorem size_Skolem1[simp]:
  size (Skolem1 f x p) < size (Exists x p)
Proof
  simp[Skolem1_def]
QED

Theorem prenex_Skolem1[simp]:
  prenex (Skolem1 f x p) ⇔ prenex p
Proof
  simp[Skolem1_def]
QED

Theorem form_predicates_Skolem1[simp]:
  form_predicates (Skolem1 f x p) = form_predicates p
Proof
  simp[Skolem1_def]
QED

Theorem LIST_UNION_MAP_KEMPTY[simp]:
  LIST_UNION (MAP (λa. ∅) l) = ∅ ∧
  LIST_UNION (MAP (K ∅) l) = ∅
Proof
  Induct_on ‘l’ >> simp[]
QED

Theorem form_functions_Skolem1[simp]:
  form_functions (Skolem1 f x p) ⊆
    (f, CARD (FV (Exists x p))) INSERT form_functions p ∧
  form_functions p ⊆ form_functions (Skolem1 f x p)
Proof
  simp[Skolem1_def] >> Cases_on ‘x ∈ FV p’
  >- (simp[form_functions_formsubst1, MAP_MAP_o, combinTheory.o_ABS_L,
           SET_TO_LIST_CARD] >>
      simp[SUBSET_DEF]) >>
  simp[SUBSET_DEF]
QED

Theorem Skolem1_ID[simp]:
  x ∉ FV p ⇒ Skolem1 f x p = p
Proof
  simp[Skolem1_def]
QED

Theorem holds_exists_holds_skolem1:
  (f,CARD (FV (Exists x p))) ∉ form_functions (Exists x p)
 ⇒
  ∀M. interpretation (language {p}) M ∧ M.Dom ≠ ∅ ∧
      (∀v. valuation M v ⇒ holds M v (Exists x p))
   ⇒
      ∃M'. M'.Dom = M.Dom ∧ M'.Pred = M.Pred ∧
           (∀g zs. g ≠ f ∨ LENGTH zs ≠ CARD (FV (Exists x p)) ⇒
                   M'.Fun g zs = M.Fun g zs) ∧
           interpretation (language {Skolem1 f x p}) M' ∧
           ∀v. valuation M' v ⇒ holds M' v (Skolem1 f x p)
Proof
  reverse (Cases_on ‘x ∈ FV p’)
  >- (simp[holds_nonFV] >> metis_tac[]) >>
  qabbrev_tac ‘FF = FV (Exists x p)’ >> simp[Skolem1_def] >>
  qabbrev_tac ‘ft = Fn f (MAP V (SET_TO_LIST FF))’ >> rw[] >>
  qexists_tac ‘<|
    Dom := M.Dom ; Pred := M.Pred ;
    Fun := M.Fun ⦇ f ↦
                   λargs. if LENGTH args = CARD FF then
                             @a. a ∈ M.Dom ∧
                                 holds M (FOLDR (λ(k,v) f. f ⦇ k ↦ v ⦈)
                                             (λz. @c. c ∈ M.Dom)
                                             (ZIP(SET_TO_LIST FF, args)))
                                         ⦇ x ↦ a ⦈
                                         p
                          else M.Fun f args ⦈
  |>’ >> simp[] >> rw[]
  >- simp[combinTheory.APPLY_UPDATE_THM]
  >- rw[combinTheory.APPLY_UPDATE_THM]
  >- (fs[interpretation_def, language_def] >>
      rw[combinTheory.APPLY_UPDATE_THM]
      >- (rename [‘(f,LENGTH l) ∈ form_functions p’] >> metis_tac[])
      >- (rename [‘(f,LENGTH l) ∈ term_functions ft’] >>
          ‘FINITE FF’ by simp[Abbr‘FF’]>>
          reverse (fs[Abbr‘ft’, MAP_MAP_o, MEM_MAP, SET_TO_LIST_CARD])
          >- (rw[] >> fs[]) >>
          SELECT_ELIM_TAC >> simp[] >>
          first_x_assum irule >> simp[valuation_def] >>
          ‘∀(vars:num list) (vals:α list) n.
             (∀v. MEM v vals ⇒ v ∈ M.Dom) ∧ LENGTH vars = LENGTH vals ⇒
             FOLDR (λ(k,v) f. f ⦇k ↦ v⦈) (λz. @c. c ∈ M.Dom)
                   (ZIP (vars, vals)) n ∈ M.Dom’
            suffices_by metis_tac[SET_TO_LIST_CARD] >>
          Induct >> simp[]
          >- (SELECT_ELIM_TAC >> fs[EXTENSION] >> metis_tac[]) >>
          Cases_on ‘vals’ >>
          simp[DISJ_IMP_THM, FORALL_AND_THM, combinTheory.APPLY_UPDATE_THM] >>
          rw[])
      >- (rename [‘f ≠ g’, ‘(g,LENGTH l) ∈ form_functions p’] >> metis_tac[]) >>
      rename [‘f ≠ g’, ‘(g,LENGTH l) ∈ term_functions ft’] >>
      fs[Abbr‘ft’, MEM_MAP, SET_TO_LIST_CARD] >> rw[] >> fs[]) >>
  qmatch_abbrev_tac ‘holds <| Dom := M.Dom; Fun := CF; Pred := M.Pred |> _ _’ >>
  simp[holds_formsubst1, Abbr‘ft’, MAP_MAP_o, combinTheory.o_ABS_L] >>
  irule (holds_functions
           |> CONV_RULE (RAND_CONV (REWRITE_CONV [EQ_IMP_THM]))
           |> UNDISCH |> Q.SPEC ‘v’ |> CONJUNCT2 |> Q.GEN ‘v’ |> DISCH_ALL) >>
  qexists_tac ‘M’ >> simp[] >> conj_tac
  >- (rw[Abbr‘CF’, combinTheory.APPLY_UPDATE_THM] >> metis_tac[]) >>
  ‘FINITE FF’ by simp[Abbr‘FF’] >>
  simp[Abbr‘CF’, SET_TO_LIST_CARD, combinTheory.APPLY_UPDATE_THM] >>
  SELECT_ELIM_TAC >> conj_tac
  >- (first_x_assum irule >> fs[valuation_def] >>
      ‘∀l. (∀n. v n ∈ M.Dom) ⇒
           ∀n. FOLDR (λ(k,v) f. f ⦇ k ↦ v ⦈) (λz. @c. c ∈ M.Dom)
                     (ZIP (l,MAP (λa. v a) l)) n ∈ M.Dom’
        suffices_by metis_tac[] >> Induct >> simp[]
      >- (SELECT_ELIM_TAC >> fs[EXTENSION] >>metis_tac[]) >>
      rfs[combinTheory.APPLY_UPDATE_THM] >> rw[]) >>
  qx_gen_tac ‘a’ >>
  qmatch_abbrev_tac ‘a ∈ M.Dom ∧ holds M vv⦇ x ↦ a ⦈ p ⇒ holds M v⦇ x ↦ a ⦈ p’>>
  fs[valuation_def] >> strip_tac >>
  ‘∀var. var ∈ FV p ⇒ vv⦇ x ↦ a ⦈ var = v⦇ x ↦ a ⦈ var’
    suffices_by metis_tac[holds_valuation] >>
  rw[combinTheory.APPLY_UPDATE_THM] >> simp[Abbr‘vv’] >>
  ‘∀vars (var:num).
     MEM var vars ∧ ALL_DISTINCT vars ⇒
     FOLDR (λ(k,v) f. f ⦇ k ↦ v ⦈) (λz. @c. c ∈ M.Dom)
           (ZIP (vars,MAP (λa. v a) vars)) var = v var’
    suffices_by (disch_then irule >> simp[] >> simp[Abbr‘FF’]) >>
  Induct >> simp[] >> rw[combinTheory.APPLY_UPDATE_THM]
QED

Theorem Skolem1_holds_Exists_holds:
  (f,CARD (FV (Exists x p))) ∉ form_functions (Exists x p) ⇒
  ∀N. interpretation (language {Skolem1 f x p}) N ∧ N.Dom ≠ ∅
     ⇒
      ∀v. valuation N v ∧ holds N v (Skolem1 f x p) ⇒ holds N v (Exists x p)
Proof
  reverse (Cases_on ‘x ∈ FV p’)
  >- (simp[holds_nonFV, EXTENSION] >> metis_tac[]) >>
  qabbrev_tac ‘FF = FV (Exists x p)’ >> simp[Skolem1_def] >>
  qabbrev_tac ‘ft = Fn f (MAP V (SET_TO_LIST FF))’ >>
  ‘FINITE FF’ by simp[Abbr‘FF’] >>
  simp[holds_formsubst1] >> rw[] >>
  ‘termval N v ft ∈ N.Dom’ suffices_by metis_tac[] >>
  simp[Abbr‘ft’, MAP_MAP_o, combinTheory.o_ABS_L] >>
  rfs[interpretation_def, language_def, form_functions_formsubst1,
      MEM_MAP, MAP_MAP_o, PULL_EXISTS, DISJ_IMP_THM, FORALL_AND_THM,
      RIGHT_AND_OVER_OR] >>
  first_x_assum
    (fn th => irule th >>
              fs[MEM_MAP, PULL_EXISTS, SET_TO_LIST_CARD, valuation_def] >>
              NO_TAC)
QED

(* ------------------------------------------------------------------------- *)
(* Multiple Skolemization of a prenex formula.                               *)
(* ------------------------------------------------------------------------- *)

Definition Skolems_def:
  Skolems J r k =
    PPAT (λx q. FALL x (Skolems J q k))
         (λx q. Skolems J (Skolem1 (J *, k) x q) (k + 1))
         (λp. p) r
Termination
  WF_REL_TAC ‘measure (λ(a,b,c). size b)’ >> simp[] >>
  simp[Skolem1_def]
End

Theorem prenex_Skolems_universal[simp]:
  ∀J p k. prenex p ⇒ universal (Skolems J p k)
Proof
  ho_match_mp_tac Skolems_ind >> rw[] >>
  Cases_on ‘∃x p0. p = Exists x p0’ >> fs[]
  >- (simp[Once Skolems_def] >> first_x_assum irule >> fs[]) >>
  Cases_on ‘∃x p0. p = FALL x p0’ >> fs[]
  >- (simp[Once Skolems_def] >> fs[universal_rules]) >>
  simp[Once Skolems_def] >>
  simp[Once universal_cases] >> metis_tac[prenex_cases]
QED

Theorem FV_Skolems[simp]:
  ∀J p k. FV (Skolems J p k) = FV p
Proof
  ho_match_mp_tac Skolems_ind >> rw[] >>
  Cases_on ‘∃x p0. p = Exists x p0’ >> fs[] >- simp[Once Skolems_def] >>
  Cases_on ‘∃x p0. p = FALL x p0’ >> fs[] >- simp[Once Skolems_def] >>
  simp[Once Skolems_def]
QED

Theorem form_predicates_Skolems[simp]:
  ∀J p k. form_predicates (Skolems J p k) = form_predicates p
Proof
  ho_match_mp_tac Skolems_ind >> rw[] >>
  Cases_on ‘∃x p0. p = Exists x p0’ >> fs[]
  >- (simp[Once Skolems_def] >> simp[Exists_def, Not_def]) >>
  Cases_on ‘∃x p0. p = FALL x p0’ >> fs[] >- simp[Once Skolems_def] >>
  simp[Once Skolems_def]
QED

Theorem form_functions_Skolems_up:
  ∀J p k.
    form_functions (Skolems J p k) ⊆
      {(J ⊗ l, m) | l, m | k ≤ l} ∪ form_functions p
Proof
  ho_match_mp_tac Skolems_ind >> rw[] >>
  Cases_on ‘∃x p0. p = Exists x p0’ >> fs[]
  >- (simp[Once Skolems_def] >> fs[] >>
      first_x_assum (qspecl_then [‘p0’, ‘x’] mp_tac) >> simp[] >>
      simp[SUBSET_DEF] >> rw[] >> first_x_assum drule >> rw[] >>
      mp_tac (form_functions_Skolem1 |> CONJUNCT1 |> GEN_ALL) >>
      REWRITE_TAC[SUBSET_DEF] >> rw[] >>
      pop_assum (drule_then strip_assume_tac) >> rw[]) >>
  Cases_on ‘∃x p0. p = FALL x p0’ >> fs[] >- simp[Once Skolems_def] >>
  simp[Once Skolems_def]
QED

Theorem form_functions_Skolems_down:
  ∀J p k.
    form_functions p ⊆ form_functions (Skolems J p k)
Proof
  ho_match_mp_tac Skolems_ind >> rw[] >>
  Cases_on ‘∃x p0. p = Exists x p0’ >> fs[]
  >- (simp[Once Skolems_def] >> fs[] >>
      first_x_assum (qspecl_then [‘p0’, ‘x’] mp_tac) >> simp[] >>
      simp[SUBSET_DEF] >> rw[] >> first_x_assum irule >> rw[] >>
      metis_tac[SUBSET_DEF, form_functions_Skolem1]) >>
  Cases_on ‘∃x p0. p = FALL x p0’ >> fs[] >- simp[Once Skolems_def] >>
  simp[Once Skolems_def]
QED









val _ = export_theory();
