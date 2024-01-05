open HolKernel Parse boolLib bossLib;

open boolSimps pred_setTheory listTheory nlistTheory
open folPrenexTheory folModelsTheory folLangTheory
open mp_then

val _ = new_theory "folSkolem";

Theorem holds_exists_lemma:
  ∀p t x M v (preds : (num # num) set).
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
  size (Skolem1 f x p) = size p
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

Theorem form_functions_Skolem1:
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

Theorem termval_o_V[simp]:
  termval M v o V = v
Proof
  simp[FUN_EQ_THM]
QED

Theorem holds_Skolem1_I:
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
      ‘∀l n. FOLDR (λ(k,v) f. f ⦇k ↦ v⦈) (λz. @c. c ∈ M.Dom)
                   (ZIP (l,MAP v l)) n ∈ M.Dom’
        suffices_by metis_tac[] >> Induct >> simp[]
      >- (SELECT_ELIM_TAC >> fs[EXTENSION] >> metis_tac[]) >>
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
           (ZIP (vars,MAP v vars)) var = v var’
    suffices_by (disch_then irule >> simp[] >> simp[Abbr‘FF’]) >>
  Induct >> simp[] >> rw[combinTheory.APPLY_UPDATE_THM]
QED

Theorem holds_Skolem1_E:
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

Theorem holds_Skolems_I:
  ∀J p k M.
     interpretation (language{p}) M ∧ M.Dom ≠ ∅ ∧
     (∀v. valuation M v ⇒ holds M v p) ∧
     (∀l m. (J ⊗ l,m) ∈ form_functions p ⇒ l < k)
    ⇒
     ∃M'. M'.Dom = M.Dom ∧ M'.Pred = M.Pred ∧
          (∀g zs. M'.Fun g zs ≠ M.Fun g zs ⇒ ∃l. k ≤ l ∧ g = J ⊗ l) ∧
          interpretation (language {Skolems J p k}) M' ∧
          ∀v. valuation M' v ⇒ holds M' v (Skolems J p k)
Proof
  ho_match_mp_tac Skolems_ind >> rw[] >>
  Cases_on ‘∃x p0. p = FALL x p0’ >> fs[] >> fs[]
  >- (ONCE_REWRITE_TAC [Skolems_def] >> simp[] >>
      first_x_assum
        (first_assum o mp_then.mp_then (mp_then.Pos (el 2)) mp_tac) >>
      impl_tac
      >- (simp[] >>
          reverse conj_tac
          >- (first_x_assum ACCEPT_TAC (* freshness assumption *)) >>
          qx_gen_tac ‘valn’ >> strip_tac >>
          first_x_assum (drule_then (qspec_then ‘valn x’ mp_tac)) >>
          simp[combinTheory.APPLY_UPDATE_ID] >> disch_then irule >>
          fs[valuation_def]) >>
      disch_then (qx_choose_then ‘N’ strip_assume_tac) >> qexists_tac ‘N’ >>
      simp[] >> first_assum ACCEPT_TAC) >>
  reverse (Cases_on ‘∃x p0. p = Exists x p0’) >> fs[]
  >- (ONCE_REWRITE_TAC [Skolems_def] >> simp[] >> metis_tac[]) >>
  rw[] >> fs[] >> rw[] >> ONCE_REWRITE_TAC [Skolems_def] >> simp[] >>
  (* apply Skolem1 result: holds_Skolem1_I *)
  rename [‘Skolem1 (J ⊗ k) xv ϕ’] >>
  first_assum
    (mp_then.mp_then (mp_then.Pos (el 2)) mp_tac (GEN_ALL holds_Skolem1_I)) >>
  simp[Excl "FV_extras"] >>
  disch_then (first_assum o mp_then.mp_then (mp_then.Pos (el 2)) mp_tac) >>
  disch_then (qspec_then ‘J ⊗ k’ mp_tac) >>
  qabbrev_tac ‘FF = FV (Exists xv ϕ)’ >> ‘FINITE FF’ by simp[Abbr‘FF’] >>
  disch_then (PROVEHYP_THEN (K (qx_choose_then ‘M1’ strip_assume_tac)))
  >- (strip_tac >> first_x_assum drule >> simp[]) >>
  qpat_x_assum
    ‘∀p n. size p < size _ + _ ⇒
           ∀M. interpretation (language {Skolem1 _ _ _ }) M ∧ _ ⇒ _’
    (first_assum o mp_then.mp_then (mp_then.Pos (el 2)) mp_tac) >>
  simp[] >>
  qpat_x_assum ‘∀p. size p < size _ + _ ⇒ _’ (K ALL_TAC) >>
  impl_tac
  >- (rw[] >> rename [‘(J ⊗ n,m) ∈ form_functions (Skolem1 (J ⊗ k) _ _)’] >>
      mp_tac (form_functions_Skolem1 |> CONJUNCT1 |> GEN_ALL) >>
      simp[SUBSET_DEF, Excl "FV_extras", Excl "form_functions_Skolem1"] >>
      disch_then drule >> simp[] >> rw[] >> simp[] >>
      metis_tac[DECIDE “x < k ⇒ x < k + 1”]) >>
  disch_then (qx_choose_then ‘N’ strip_assume_tac) >> qexists_tac ‘N’ >>
  simp[] >>
  rw[] >> rename [‘N.Fun g args = M.Fun g args’] >>
  Cases_on ‘N.Fun g args = M1.Fun g args’ >> fs[]
  >- metis_tac [DECIDE “x ≤ x”] >>
  first_x_assum (pop_assum o mp_then.mp_then (mp_then.Pos hd) mp_tac) >>
  simp[PULL_EXISTS]
QED

Theorem interpretation_Skolem1_E:
  ∀N f x p. interpretation (language {Skolem1 f x p}) N ⇒
            interpretation (language {p}) N
Proof
  rpt gen_tac >> reverse (Cases_on ‘x ∈ FV p’) >> simp[Skolem1_ID] >>
  simp[Skolem1_def, language_def, form_functions_formsubst1,
       predicates_def, interpretation_def]
QED

Theorem interpretation_Skolems_E:
  ∀J p k N. interpretation (language {Skolems J p k}) N ⇒
            interpretation (language {p}) N
Proof
  ho_match_mp_tac Skolems_ind >> rpt gen_tac >> strip_tac >>
  Cases_on ‘∃x p0. p = FALL x p0’ >> fs[]
  >- (ONCE_REWRITE_TAC[Skolems_def] >> simp[]) >>
  reverse (Cases_on ‘∃x p0. p = Exists x p0’) >> fs[]
  >- (ONCE_REWRITE_TAC[Skolems_def] >> simp[]) >>
  ONCE_REWRITE_TAC[Skolems_def] >> simp[] >> rw[] >> fs[] >>
  qpat_x_assum ‘∀f:form n. _’
    (first_assum o mp_then.mp_then mp_then.Any mp_tac) >> simp[] >>
  metis_tac[interpretation_Skolem1_E]
QED

Theorem holds_Skolems_E:
  ∀J p k.
    (∀l m. (J ⊗ l, m) ∈ form_functions p ⇒ l < k) ⇒
    ∀N. interpretation (language {Skolems J p k}) N ∧ N.Dom ≠ ∅ ⇒
        ∀v. valuation N v ∧ holds N v (Skolems J p k) ⇒
            holds N v p
Proof
  ho_match_mp_tac Skolems_ind >> rpt gen_tac >> ntac 2 strip_tac >>
  Cases_on ‘∃x p0. p = FALL x p0’ >> fs[]
  >- (ONCE_REWRITE_TAC [Skolems_def] >> simp[] >> rw[] >> fs[] >>
      first_x_assum
        (first_assum o mp_then.mp_then (mp_then.Pos (el 2)) mp_tac) >>
      simp[]) >>
  reverse (Cases_on ‘∃x p0. p = Exists x p0’) >> fs[]
  >- (ONCE_REWRITE_TAC [Skolems_def] >> simp[]) >>
  ONCE_REWRITE_TAC [Skolems_def] >> simp[] >> rw[] >> fs[] >>
  qpat_x_assum ‘∀q:form n:num. _’
     (first_assum o mp_then.mp_then (mp_then.Pos (el 3)) mp_tac) >> simp[] >>
  disch_then (first_assum o mp_then.mp_then mp_then.Any mp_tac) >> simp[] >>
  impl_tac
  >- (rw[] >> rename [‘(J ⊗ n,m) ∈ form_functions _’] >>
      mp_tac (form_functions_Skolem1 |> CONJUNCT1 |> GEN_ALL) >>
      simp[SUBSET_DEF, Excl "form_functions_Skolem1", Excl "FV_extras"] >>
      disch_then drule >> rw[Excl "FV_extras"] >> simp[] >>
      first_x_assum drule >> simp[]) >>
  strip_tac >>
  first_assum (mp_then.mp_then (mp_then.Pos last) mp_tac holds_Skolem1_E) >>
  reverse impl_tac >> simp[] >> conj_tac
  >- (strip_tac >> first_x_assum drule >> simp[]) >>
  metis_tac[interpretation_Skolems_E]
QED

(* ------------------------------------------------------------------------- *)
(* Now Skolemize an arbitrary (non-prenex) formula.                          *)
(* ------------------------------------------------------------------------- *)

Definition Skopre_def:
  Skopre J p = Skolems J (Prenex p) 0
End

Theorem FV_Skopre[simp]:
  FV (Skopre i p) = FV p
Proof
  simp[Skopre_def]
QED

Theorem universal_Skopre[simp]:
  universal (Skopre i p)
Proof
  simp[Skopre_def]
QED

Theorem form_predicates_Skopre[simp]:
  form_predicates (Skopre j p) = form_predicates p
Proof
  simp[Skopre_def]
QED

Theorem form_functions_Skopre_I:
  form_functions p ⊆ form_functions (Skopre j p)
Proof
  simp[Skopre_def] >>
  metis_tac[SUBSET_TRANS,form_functions_Prenex, form_functions_Skolems_down]
QED

Theorem form_functions_Skopre_E:
  form_functions (Skopre j p) ⊆ {(j ⊗ l, m) | l,m | T } ∪ form_functions p
Proof
  simp[Skopre_def] >>
  qspecl_then [‘j’, ‘Prenex p’, ‘0’] mp_tac form_functions_Skolems_up >>
  simp[]
QED

Theorem holds_Skopre_I:
  ∀p j M.
     (∀l m. (j ⊗ l, m) ∉ form_functions p) ∧
     interpretation (language {p}) M ∧ M.Dom ≠ ∅ ∧
     (∀v. valuation M v ⇒ holds M v p)
   ⇒
     ∃M'. M'.Dom = M.Dom ∧ M'.Pred = M.Pred ∧
          (∀g zs. M'.Fun g zs ≠ M.Fun g zs ⇒ ∃l. g = j ⊗ l) ∧
          interpretation (language {Skopre j p}) M' ∧
          ∀v. valuation M' v ⇒ holds M' v (Skopre j p)
Proof
  rw[Skopre_def] >>
  qspecl_then [‘j’, ‘Prenex p’, ‘0’] mp_tac holds_Skolems_I >> simp[]
QED

Theorem holds_Skopre_E:
  ∀p j N. (∀l m. (j ⊗ l, m) ∉ form_functions p) ∧
          interpretation (language{Skopre j p}) N ∧ N.Dom ≠ ∅ ⇒
          ∀v. valuation N v ∧ holds N v (Skopre j p) ⇒ holds N v p
Proof
  rw[Skopre_def] >>
  qspecl_then [‘j’, ‘Prenex p’, ‘0’] mp_tac holds_Skolems_E >> simp[]
QED

Theorem interpretation_Skopre_E:
  ∀p j N. interpretation (language {Skopre j p}) N ⇒
          interpretation (language {p}) N
Proof
  rw[Skopre_def] >> drule interpretation_Skolems_E >> simp[]
QED

(* ------------------------------------------------------------------------- *)
(* Bumping up function indices to leave room for Skolem functions.           *)
(* ------------------------------------------------------------------------- *)

Definition bumpmod_def:
  bumpmod M = M with Fun := λk zs. M.Fun (nsnd k) zs
End

Theorem bumpmod_rwts[simp]:
  (bumpmod M).Pred = M.Pred ∧ (bumpmod M).Dom = M.Dom ∧
  (bumpmod M).Fun (m ⊗ n) = M.Fun n
Proof
  simp[bumpmod_def, FUN_EQ_THM]
QED

Theorem valuation_bumpmod[simp]:
  valuation (bumpmod M) v ⇔ valuation M v
Proof
  simp[valuation_def]
QED

Definition bumpterm_def:
  bumpterm (V x) = V x ∧
  bumpterm (Fn k l) = Fn (0 ⊗ k) (MAP bumpterm l)
Termination
  WF_REL_TAC ‘measure term_size’ >> simp[]
End

Theorem bumpterm_def[simp,allow_rebind] =
        SIMP_RULE bool_ss [SF ETA_ss] bumpterm_def

Theorem termval_bump[simp]:
  ∀M v t. termval (bumpmod M) v (bumpterm t) = termval M v t
Proof
  Induct_on ‘t’ >> simp[MAP_MAP_o, combinTheory.o_ABS_R, Cong MAP_CONG]
QED

Theorem TFV_bumpterm[simp]:
  FVT (bumpterm t) = FVT t
Proof
  Induct_on ‘t’ >> simp[MAP_MAP_o, Cong MAP_CONG]
QED

Definition bumpform_def[simp]:
  bumpform False = False ∧
  bumpform (Pred p l) = Pred p (MAP bumpterm l) ∧
  bumpform (IMP p q) = IMP (bumpform p) (bumpform q) ∧
  bumpform (FALL x p) = FALL x (bumpform p)
End

Theorem FV_bumpform[simp]:
  FV (bumpform p) = FV p
Proof
  Induct_on ‘p’ >>
  asm_simp_tac (srw_ss() ++ ETA_ss) [MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem holds_bump[simp]:
  ∀M v p. holds (bumpmod M) v (bumpform p) ⇔ holds M v p
Proof
  Induct_on ‘p’ >> simp[MAP_MAP_o, combinTheory.o_DEF, Cong MAP_CONG]
QED

Theorem term_functions_bumpterm[simp]:
  term_functions (bumpterm t) = { (0 ⊗ k, m) | (k,m) ∈ term_functions t }
Proof
  Induct_on ‘t’ >> simp[MAP_MAP_o, Cong MAP_CONG, MEM_MAP, PULL_EXISTS] >>
  simp[Once EXTENSION, MEM_MAP, PULL_EXISTS] >> metis_tac[]
QED

Theorem form_functions_bumpform:
  form_functions (bumpform p) = { (0 ⊗ k, m) | (k,m) ∈ form_functions p }
Proof
  Induct_on ‘p’ >> simp[MEM_MAP, MAP_MAP_o, PULL_EXISTS]
  >- (simp[Once EXTENSION, MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
  simp[Once EXTENSION] >> metis_tac[]
QED

Theorem form_predicates_bumpform[simp]:
  form_predicates (bumpform p) = form_predicates p
Proof
  Induct_on ‘p’ >> simp[]
QED

Theorem interpretation_bumpform[simp]:
  interpretation (language {bumpform p}) (bumpmod M) ⇔
  interpretation (language {p}) M
Proof
  simp[interpretation_def, language_def, PULL_EXISTS, form_functions_bumpform]>>
  metis_tac[]
QED

Definition unbumpterm_def[simp]:
  unbumpterm (V x) = V x ∧
  unbumpterm (Fn k l) = Fn (nsnd k) (MAP unbumpterm l)
Termination
  WF_REL_TAC ‘measure term_size’ >> simp[]
End

Definition unbumpform_def[simp]:
  unbumpform False = False ∧
  unbumpform (Pred p l) = Pred p (MAP unbumpterm l) ∧
  unbumpform (IMP f1 f2) = IMP (unbumpform f1) (unbumpform f2) ∧
  unbumpform (FALL x f) = FALL x (unbumpform f)
End

Theorem bumpterm_inv[simp]:
  unbumpterm (bumpterm t) = t
Proof
  Induct_on ‘t’ >> simp[MAP_MAP_o, Cong MAP_CONG]
QED

Theorem bumpform_inv[simp]:
  unbumpform (bumpform p) = p
Proof
  Induct_on ‘p’ >> simp[MAP_MAP_o, Cong MAP_CONG]
QED

Definition unbumpmod_def:
  unbumpmod M = M with Fun := λk zs. M.Fun (0 ⊗ k) zs
End

Theorem unbumpmod_rwts[simp]:
  (unbumpmod M).Dom = M.Dom ∧
  (unbumpmod M).Pred = M.Pred ∧
  (∀v. valuation (unbumpmod M) v ⇔ valuation M v)
Proof
  simp[unbumpmod_def, valuation_def]
QED

Theorem termval_unbumpmod:
  termval (unbumpmod M) v t = termval M v (bumpterm t)
Proof
  Induct_on ‘t’ >> simp[Cong MAP_CONG, MAP_MAP_o] >> simp[unbumpmod_def]
QED

Theorem holds_unbumpmod:
  ∀M v p. holds (unbumpmod M) v p ⇔ holds M v (bumpform p)
Proof
  Induct_on ‘p’ >> simp[MAP_MAP_o, Cong MAP_CONG, termval_unbumpmod] >>
  simp[unbumpmod_def]
QED

(* ------------------------------------------------------------------------- *)
(* Skolemization function.                                                   *)
(* ------------------------------------------------------------------------- *)

Definition SKOLEMIZE_def:
  SKOLEMIZE p = Skopre (num_of_form (bumpform p) + 1) (bumpform p)
End

Theorem SKOLEMIZE_props[simp]:
  universal (SKOLEMIZE p) ∧
  prenex (SKOLEMIZE p) ∧
  form_predicates (SKOLEMIZE p) = form_predicates p ∧
  FV (SKOLEMIZE p) = FV p
Proof
  simp[SKOLEMIZE_def, universal_prenex]
QED

Theorem form_functions_SKOLEMIZE_I =
  form_functions_Skopre_I
    |> Q.INST [‘p’ |-> ‘bumpform p’,
               ‘j’ |-> ‘num_of_form (bumpform p) + 1’]
    |> SIMP_RULE (srw_ss()) [GSYM SKOLEMIZE_def];

Theorem form_functions_SKOLEMIZE_E:
  form_functions (SKOLEMIZE p) ⊆
    {(k ⊗ l, m) | k,l,m | k = num_of_form (bumpform p) +1} ∪
    form_functions (bumpform p)
Proof
  rw[SKOLEMIZE_def, SUBSET_DEF] >>
  drule (form_functions_Skopre_E |> SIMP_RULE (srw_ss()) [SUBSET_DEF]) >>
  metis_tac[]
QED

Theorem holds_SKOLEMIZE_I:
  ∀M p. interpretation (language {bumpform p}) M ∧ M.Dom ≠ ∅ ∧
        (∀v. valuation M v ⇒ holds M v (bumpform p))
     ⇒
        ∃M'. M'.Dom = M.Dom ∧
             M'.Pred = M.Pred ∧
             (∀g zs. M'.Fun g zs ≠ M.Fun g zs ⇒
                     ∃l. g = (num_of_form (bumpform p) + 1) ⊗ l) ∧
             interpretation (language {SKOLEMIZE p}) M' ∧
             ∀v. valuation M' v ⇒ holds M' v (SKOLEMIZE p)
Proof
  simp[SKOLEMIZE_def] >> rpt strip_tac >>
  irule holds_Skopre_I >>
  simp[form_functions_bumpform]
QED

Theorem holds_SKOLEMIZE_E:
  ∀N. interpretation (language {SKOLEMIZE p}) N ∧ N.Dom ≠ ∅
        ⇒
      ∀v. valuation N v ∧ holds N v (SKOLEMIZE p) ⇒
          holds N v (bumpform p)
Proof
  simp[SKOLEMIZE_def] >> rpt strip_tac >> irule holds_Skopre_E >>
  simp[form_functions_bumpform] >>
  goal_assum (first_assum o mp_then Any mp_tac) >> simp[]
QED

Theorem interpretation_SKOLEMIZE_E:
  interpretation (language {SKOLEMIZE p}) N ⇒
  interpretation (language {bumpform p}) N
Proof
  simp[SKOLEMIZE_def] >> strip_tac >> irule interpretation_Skopre_E >>
  metis_tac[]
QED

Theorem form_functions_SKOLEMIZE_IN_E =
  SIMP_RULE (srw_ss())
            [SUBSET_DEF, form_functions_bumpform, pairTheory.FORALL_PROD]
            form_functions_SKOLEMIZE_E

(* ------------------------------------------------------------------------- *)
(* Construction of Skolem model for a formula.                               *)
(* ------------------------------------------------------------------------- *)

Definition SKOMOD1_def:
  SKOMOD1 p M =
    if (∀v. valuation M v ⇒ holds M v p) then
      @M'. M'.Dom = (bumpmod M).Dom ∧
           M'.Pred = (bumpmod M).Pred ∧
           (∀g zs. M'.Fun g zs ≠ (bumpmod M).Fun g zs ⇒
                   ∃l. g = (num_of_form (bumpform p) + 1) ⊗ l) ∧
           interpretation (language {SKOLEMIZE p}) M' ∧
           ∀v. valuation M' v ⇒ holds M' v (SKOLEMIZE p)
    else M with Fun := λg zs. @a. a ∈ M.Dom
End

Theorem SKOMOD1_rwts[simp]:
  interpretation (language{p}) M ∧ M.Dom ≠ ∅ ⇒
  (SKOMOD1 p M).Dom = M.Dom ∧
  (SKOMOD1 p M).Pred = M.Pred ∧
  interpretation (language {SKOLEMIZE p}) (SKOMOD1 p M)
Proof
  simp[SKOMOD1_def] >> reverse COND_CASES_TAC >> simp[]
  >- (simp[interpretation_def,language_def] >> rw[] >>
      fs[EXTENSION] >> SELECT_ELIM_TAC >> simp[] >> metis_tac[]) >>
  strip_tac >> SELECT_ELIM_TAC >> simp[] >>
  ‘M.Dom = (bumpmod M).Dom ∧ M.Pred = (bumpmod M).Pred’ by simp[] >>
  ASM_REWRITE_TAC[] >> irule holds_SKOLEMIZE_I >>
  ntac 2 (pop_assum (K ALL_TAC)) >> simp[]
QED

Theorem holds_SKOMOD1_I:
  interpretation (language{p}) M ∧ M.Dom ≠ ∅ ⇒
  (∀v. valuation M v ⇒ holds M v p)
    ⇒
  (∀g zs. (SKOMOD1 p M).Fun g zs ≠ (bumpmod M).Fun g zs ⇒
          ∃l. g = (num_of_form (bumpform p) + 1) ⊗ l) ∧
  ∀v. valuation M v ⇒ holds (SKOMOD1 p M) v (SKOLEMIZE p)
Proof
  strip_tac >> strip_tac >> simp[SKOMOD1_def] >> SELECT_ELIM_TAC >> simp[] >>
  rw[]
  >- (‘M.Dom = (bumpmod M).Dom ∧ M.Pred = (bumpmod M).Pred’ by simp[] >>
      ASM_REWRITE_TAC[] >> irule holds_SKOLEMIZE_I >>
      ntac 2 (pop_assum (K ALL_TAC)) >> simp[])
  >- metis_tac[] >>
  first_x_assum irule >> rfs[valuation_def]
QED

Definition SKOMOD_def:
  SKOMOD M =
    M with
      Fun := λg zs.
       if nfst g = 0 then M.Fun (nsnd g) zs
       else (SKOMOD1 (unbumpform (form_of_num (nfst g - 1))) M).Fun g zs
End

Theorem SKOMOD_rwts[simp]:
  (SKOMOD M).Dom = M.Dom ∧
  (SKOMOD M).Pred = M.Pred ∧
  (∀v. valuation (SKOMOD M) v = valuation M v)
Proof
  simp[SKOMOD_def, valuation_def]
QED

Theorem SKOMOD_INTERPRETATION:
  interpretation (language {p}) M ∧ M.Dom ≠ ∅
    ⇒
  interpretation (language {SKOLEMIZE p}) (SKOMOD M)
Proof
  strip_tac >> drule_all_then strip_assume_tac SKOMOD1_rwts >>
  fs[interpretation_def, language_def, SKOMOD_def] >> rw[] >>
  drule form_functions_SKOLEMIZE_IN_E >> rw[] >> fs[] >> rfs[]
QED

Theorem SKOMOD_WORKS:
  interpretation (language {p}) M ∧ M.Dom ≠ ∅ ⇒
  ((∀v. valuation M v ⇒ holds (SKOMOD M) v (SKOLEMIZE p)) ⇔
   (∀v. valuation M v ⇒ holds M v p))
Proof
  strip_tac >> reverse eq_tac >> strip_tac
  >- (rpt strip_tac >>
      ‘holds (SKOMOD1 p M) v (SKOLEMIZE p)’
        by metis_tac[holds_SKOMOD1_I] >>
      ‘holds (SKOMOD M) v (SKOLEMIZE p) ⇔ holds (SKOMOD1 p M) v (SKOLEMIZE p)’
        suffices_by simp[] >>
      irule holds_functions >> simp[SKOMOD_def] >> rpt strip_tac >>
      drule form_functions_SKOLEMIZE_IN_E >> rw[] >> fs[] >>
      CCONTR_TAC >>
      ‘(SKOMOD1 p M).Fun (0 ⊗ k) zs ≠ (bumpmod M).Fun (0 ⊗ k) zs’
         by simp[] >>
      drule_all_then strip_assume_tac holds_SKOMOD1_I >>
      first_x_assum (qpat_x_assum ‘_ ≠ _’ o mp_then (Pos hd) mp_tac) >>
      simp[]) >>
  rpt strip_tac >> first_x_assum (first_assum o mp_then (Pos hd) assume_tac) >>
  drule_all_then assume_tac SKOMOD_INTERPRETATION >>
  ‘valuation (SKOMOD M) v ∧ (SKOMOD M).Dom ≠ ∅’ by simp[] >>
  drule_all_then assume_tac holds_SKOLEMIZE_E >>
  ‘holds (bumpmod M) v (bumpform p)’ suffices_by simp[] >>
  ‘holds (bumpmod M) v (bumpform p) ⇔ holds (SKOMOD M) v (bumpform p)’
     suffices_by simp[] >> irule holds_functions >>
  simp[form_functions_bumpform, PULL_EXISTS, SKOMOD_def]
QED

Theorem SKOMOD_INTERPRETATION_SET:
  interpretation (language s) M ∧ M.Dom ≠ ∅
    ⇒
  interpretation (language {SKOLEMIZE p | p ∈ s}) (SKOMOD M)
Proof
  mp_tac
    (SKOMOD1_rwts |> UNDISCH |> CONJUNCTS |> last |> DISCH_ALL |> Q.GEN ‘p’) >>
  simp[interpretation_def, language_def, functions_def, Excl "SKOMOD1_rwts"] >>
  simp[PULL_EXISTS] >> rw[] >>
  rename [‘p ∈ s’, ‘(f,LENGTH zs) ∈ form_functions (SKOLEMIZE p)’] >>
  first_x_assum (qpat_assum `p ∈ s` o mp_then Any mp_tac) >> strip_tac >>
  first_x_assum (first_assum o mp_then (Pos hd) strip_assume_tac) >> rfs[] >>
  ‘(SKOMOD1 p M).Dom = M.Dom’
     by (irule (SKOMOD1_rwts |> UNDISCH |> CONJUNCT1 |> DISCH_ALL) >>
         simp[interpretation_def, language_def]) >> fs[] >>
  simp[SKOMOD_def] >> drule form_functions_SKOLEMIZE_IN_E >> rw[] >> fs[]
QED

Theorem interpretation_language_member:
  interpretation (language s) M ∧ p ∈ s ⇒
  interpretation (language {p}) M
Proof
  simp[interpretation_def, functions_def, language_def, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem SKOLEMIZE_SATISFIABLE:
  (∃M : α model. M.Dom ≠ ∅ ∧ interpretation (language s) M ∧ M satisfies s) ⇔
  (∃M : α model.
       M.Dom ≠ ∅ ∧ interpretation (language {SKOLEMIZE p | p ∈ s}) M ∧
       M satisfies {SKOLEMIZE p | p ∈ s})
Proof
  simp[satisfies_def, PULL_EXISTS] >> rw[EQ_IMP_THM]
  >- (qexists_tac ‘SKOMOD M’ >> simp[SKOMOD_INTERPRETATION_SET] >>
      metis_tac[SKOMOD_WORKS, interpretation_language_member]) >>
  qexists_tac ‘unbumpmod M’ >> simp[] >> conj_tac
  >- (fs[interpretation_def, language_def, PULL_EXISTS, functions_def,
         unbumpmod_def] >> rw[] >>
      last_x_assum irule >> simp[] >>
      goal_assum drule >>
      irule (REWRITE_RULE [SUBSET_DEF] form_functions_SKOLEMIZE_I) >>
      simp[form_functions_bumpform]) >>
  simp[holds_unbumpmod] >> rw[] >> rename [‘ϕ ∈ s’] >>
  ‘interpretation (language {SKOLEMIZE ϕ}) M’
    suffices_by metis_tac[holds_SKOLEMIZE_E] >>
  irule interpretation_language_member >>
  goal_assum (first_assum o mp_then Any mp_tac) >> simp[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------- *)
(* Skolemization right down to quantifier-free formula.                      *)
(* ------------------------------------------------------------------------- *)

Definition specialize_def[simp]:
  specialize False = False ∧
  specialize (Pred p l) = Pred p l ∧
  specialize (IMP p1 p2) = IMP p1 p2 ∧
  specialize (FALL x p) = specialize p
End

Theorem holds_specialize[simp]:
  ∀M p. M.Dom ≠ ∅ ⇒
        ((∀v. valuation M v ⇒ holds M v (specialize p)) ⇔
         (∀v. valuation M v ⇒ holds M v p))
Proof
  Induct_on ‘p’ >> simp[Excl "holds_def", Excl "HOLDS", holds_uclose]
QED

Theorem specialize_satisfies:
  M.Dom ≠ ∅ ⇒ (M satisfies {specialize p | p ∈ s} ⇔ M satisfies s)
Proof
  rw[satisfies_def, PULL_EXISTS] >> metis_tac[holds_specialize]
QED

Theorem specialize_satisfies_IMAGE:
  M.Dom ≠ ∅ ⇒ (M satisfies (IMAGE specialize s) ⇔ M satisfies s)
Proof
  ‘IMAGE specialize s = {specialize p | p ∈ s}’
    suffices_by simp[specialize_satisfies] >> simp[EXTENSION]
QED

Theorem specialize_qfree:
  ∀p. universal p ⇒ qfree(specialize p)
Proof
  Induct >> simp[Once universal_cases]
QED

Theorem form_functions_specialize[simp]:
  form_functions (specialize p) = form_functions p
Proof
  Induct_on ‘p’ >> simp[]
QED

Theorem form_predicates_specialize[simp]:
  form_predicates (specialize p) = form_predicates p
Proof
  Induct_on ‘p’ >> simp[]
QED

Theorem language_specialize[simp]:
  language {specialize p | p ∈ s} = language s
Proof
  simp[language_def, functions_def, predicates_def] >>
  ONCE_REWRITE_TAC[EXTENSION] >> simp[PULL_EXISTS]
QED

Theorem language_specialize_IMAGE[simp]:
  language (IMAGE specialize s) = language s
Proof
  simp[language_def, functions_def, predicates_def] >>
  ONCE_REWRITE_TAC[EXTENSION] >> simp[PULL_EXISTS]
QED

Definition SKOLEM_def: (* the last of them *)
  SKOLEM p = specialize (SKOLEMIZE p)
End

Theorem qfree_SKOLEM[simp]:
  qfree (SKOLEM p)
Proof
  simp[SKOLEM_def, specialize_qfree]
QED

Theorem SKOLEM_SATISFIABLE:
  (∃M:α model. M.Dom ≠ ∅ ∧ interpretation (language s) M ∧ M satisfies s) ⇔
  (∃M:α model.
     M.Dom ≠ ∅ ∧ interpretation (language {SKOLEM p | p ∈ s}) M ∧
     M satisfies {SKOLEM p | p ∈ s})
Proof
  simp[SimpLHS, Once SKOLEMIZE_SATISFIABLE] >> eq_tac >> rw[SKOLEM_def] >>
  ‘{specialize (SKOLEMIZE p) | p ∈ s} = IMAGE specialize { SKOLEMIZE p | p ∈ s}’
     by simp[EXTENSION, PULL_EXISTS] >> fs[] >>
  rfs[specialize_satisfies_IMAGE] >> csimp[specialize_satisfies_IMAGE] >>
  metis_tac[]
QED

Theorem satisfiable_SKOLEM:
  satisfiable (:α) { SKOLEM p | p ∈ s } ⇔ satisfiable (:α) s
Proof
  simp[satisfiable_def, GSYM SKOLEM_SATISFIABLE]
QED


val _ = export_theory();
