(* See:

     Wu and Goré, "Verified Decision Procedures for Modal Logics", ITP 2019

   for inspiration

*)

open HolKernel Parse boolLib bossLib;
open pairTheory pred_setTheory listTheory;
open sortingTheory;
open relationTheory modalBasicsTheory tableauBasicsTheory
val _ = new_theory "tableauK";

Definition sat_def:
  sat (tyit : α itself) Γ ⇔
    ∃M (w:α). w ∈ M.frame.world ∧ ∀f. f ∈ Γ ⇒ forces M w f
End


Theorem reljump_size_lemma[local]:
  ∀a Γ l. MEM a (MAP (λd. d :: l) (undia Γ)) ⇒
          gsize a ≤ gsize l + gsize (undia Γ)
Proof
  Induct_on ‘Γ’ >> simp[undia_def, unbox_def] >> Cases >>
  simp[undia_def, unbox_def] >> rw[] >> simp[] >>
  res_tac >> simp[]
QED

Theorem undiabox_size:
  Γ ≠ [] ⇒ gsize (undia Γ) + gsize (unbox Γ) < gsize Γ
Proof
  Induct_on ‘Γ’ >> simp[undia_def, unbox_def] >>
  Cases >> simp[undia_def, unbox_def] >>
  Cases_on ‘Γ = []’ >> fs[undia_def,unbox_def]
QED

Theorem reljump_size:
  MEM a (MAP (λd. d :: unbox Γ) (undia Γ)) ⇒ gsize a < gsize Γ
Proof
  strip_tac >>
  ‘gsize a ≤ gsize (unbox Γ) + gsize (undia Γ)’ by simp[reljump_size_lemma] >>
  ‘gsize (undia Γ) + gsize (unbox Γ) < gsize Γ’ suffices_by simp[] >>
  irule undiabox_size >> strip_tac >> fs[undia_def]
QED

Definition tableau_def:
  tableau Γ =
    case contradiction Γ of
      SOME i => NONE
    | NONE =>
        case conjsplit Γ of
          SOME Γ' => tableau Γ'
        | NONE => case disjsplit Γ of
                    SOME (Γ1, Γ2) =>
                        (case tableau Γ1 of
                            SOME m => SOME m
                          | NONE =>
                            case tableau Γ2 of SOME m => SOME m | NONE => NONE)
                  | NONE => if EVERY is_literal Γ then SOME (Nd (unvar Γ) [])
                            else
                              let
                                boxes = unbox Γ ;
                                children =
                                      scmap tableau (MAP (λd. d :: boxes)
                                                         (undia Γ))
                              in
                                case children of
                                    SOME ms => SOME (Nd (unvar Γ) ms)
                                  | NONE => NONE
Termination
  WF_REL_TAC `measure (SUM o MAP form_size)` >> reverse (rw[])
  >- metis_tac [disjsplit_size]
  >- metis_tac [disjsplit_size]
  >- metis_tac [conjsplit_size] >>
  simp[reljump_size]
End

Definition tree_model_def:
  tree_model t =
    <| frame := <| rel := tree_rel ; world := { t' | RTC tree_rel t t' } |> ;
       valt := λv t. case t of Nd vs _ => MEM v vs ;
    |>
End

Theorem tree_model_thm[simp]:
  ((tree_model t).valt = λv u. case u of Nd vs _ => MEM v vs) ∧
  (tree_model t).frame.rel = tree_rel ∧
  m ∈ (tree_model m).frame.world
Proof
  simp[tree_model_def]
QED

Theorem FINITE_tree_model_worlds[simp]:
  ∀t. FINITE (tree_model t).frame.world
Proof
  simp[tree_model_def] >> Induct >> simp[tree_rel_def] >>
  simp[Once relationTheory.RTC_CASES1] >> simp[GSPEC_OR, tree_rel_def] >>
  qmatch_abbrev_tac ‘FINITE s’ >>
  ‘s = BIGUNION (IMAGE (λt. { u | RTC tree_rel t u }) (set ts))’
    by (simp[Abbr‘s’, Once EXTENSION, PULL_EXISTS] >> metis_tac[]) >>
  simp[PULL_EXISTS]
QED

Theorem tableau_sound:
  ∀Γ t. tableau Γ = SOME t ⇒ ∀f. MEM f Γ ⇒ forces (tree_model t) t f
Proof
  ho_match_mp_tac tableau_ind >> qx_gen_tac ‘Γ’ >> strip_tac >>
  qx_gen_tac ‘t’ >> simp[Once tableau_def] >>
  simp[AllCaseEqs()] >> strip_tac
  >- ((* all literals *)
      rw[] >>
      fs[EVERY_MEM] >> first_x_assum drule >>
      rename [‘is_literal f’] >> Cases_on ‘f’ >> simp[tree_model_def] >>
      fs[contradiction_EQ_NONE] >> metis_tac[])
  >- ((* K rule *)
      Cases >> simp[]
      >- rw[tree_model_def]
      >- (rw[tree_model_def] >> fs[contradiction_EQ_NONE] >> metis_tac[])
      >- fs[conjsplit_EQ_NONE]
      >- fs[disjsplit_EQ_NONE]
      >- (rename [‘MEM (Box ϕ) Γ’] >> strip_tac >> qx_gen_tac ‘t'’ >>
          BasicProvers.VAR_EQ_TAC >>
          simp[SimpL “$==>”, tree_model_def, tree_rel_def] >>
          rw[EXISTS_MEM] >>
          rename [‘scmap _ _ = SOME submodels’, ‘MEM subm submodels’] >>
          drule_all_then (qx_choose_then ‘Γ'’ mp_tac) scmap_MEM >>
          simp[MEM_MAP, PULL_EXISTS] >> qx_gen_tac ‘diam_f’ >>
          fs[MEM_MAP, PULL_EXISTS, MEM_unbox, DISJ_IMP_THM,
             FORALL_AND_THM, IMP_CONJ_THM] >> rw[] >>
          first_x_assum drule_all >> simp[] >> strip_tac >>
          irule forces_grows_backward >> qexists_tac ‘tree_model subm’ >>
          simp[] >> simp[tree_model_def, SUBSET_DEF] >> conj_tac
          >- metis_tac[relationTheory.RTC_RULES_RIGHT1] >>
          rw[] >> simp[Once relationTheory.RTC_CASES1] >> disj2_tac >>
          simp[tree_rel_def] >> metis_tac[])
      >- (fs[MEM_MAP, PULL_EXISTS, DISJ_IMP_THM, FORALL_AND_THM, IMP_CONJ_THM,
             MEM_undia] >> rw[] >> rename [‘MEM (Dia df) Γ’] >>
          ‘MEM (df :: unbox Γ) (MAP (λd. d :: unbox Γ) (undia Γ))’
             by simp[MEM_MAP, MEM_undia] >>
          dxrule_all scmap_MEM2 >> rw[] >>
          first_x_assum (drule_all_then assume_tac) >>
          simp[tree_rel_def] >>
          goal_assum (first_assum o mp_then Any mp_tac) >>
          conj_tac
          >- (simp[tree_model_def] >>
              metis_tac[relationTheory.RTC_CASES1, tree_rel_def]) >>
          irule forces_grows_backward >>
          goal_assum (first_assum o mp_then (Pos last) mp_tac) >> simp[] >>
          simp[tree_model_def, SUBSET_DEF] >> conj_tac
          >- metis_tac[relationTheory.RTC_RULES_RIGHT1] >>
          metis_tac[relationTheory.RTC_CASES1, tree_rel_def]))
  >- ((* disjsplit 1*)rw[] >> fs[] >> drule_all MEM_disjsplit >> rw[] >> simp[])
  >- ((* disjsplit 2*)rw[] >> fs[] >> drule_all MEM_disjsplit >> rw[] >> simp[])
  >- (fs[] >> rw[] >> drule_all MEM_conjsplit >> rw[] >> simp[])
QED

Theorem tableau_complete:
  ∀Γ. tableau Γ = NONE ⇒ ∀M w. w ∈ M.frame.world ⇒ ∃f. MEM f Γ ∧ ¬forces M w f
Proof
  ho_match_mp_tac tableau_ind >> gen_tac >> strip_tac >>
  simp[Once tableau_def] >> simp[AllCaseEqs()] >> rw[] >>
  fs[MEM_MAP, PULL_EXISTS, MEM_undia, MEM_unbox]
  >- ((* K rule *)
      rw[] >>
      first_x_assum (drule_then (drule_then assume_tac)) >>
      rename [‘MEM (Dia d) Γ’] >>
      reverse (Cases_on ‘forces M w (Dia d)’) >- metis_tac[] >>
      fs[] >>
      ‘∃bf. MEM (Box bf) Γ ∧ ¬forces M v bf’ by metis_tac[] >>
      qexists_tac ‘Box bf’ >> simp[] >> metis_tac[])
  >- (rpt (first_x_assum (drule_then strip_assume_tac)) >>
      drule_all disjsplit_MEM2 >> metis_tac[forces_def])
  >- (first_x_assum (drule_then strip_assume_tac) >>
      drule_all conjsplit_MEM2 >> metis_tac[forces_def])
  >- (rename [‘contradiction Γ = SOME j’] >>
      drule_then strip_assume_tac contradiction_EQ_SOME >>
      Cases_on ‘w ∈ M.valt j’
      >- (qexists_tac ‘NVar j’ >> simp[]) >>
      qexists_tac ‘Var j’ >> simp[])
QED

Theorem tableau_unsat:
  ∀Γ. tableau Γ = NONE ⇒ ¬sat (:α) (set Γ)
Proof
  simp[sat_def] >> metis_tac[tableau_complete]
QED

Theorem PERM_leading_contradiction:
  PERM Γ₁ Γ₂ ⇒ (contradiction Γ₁ = NONE ⇔ contradiction Γ₂ = NONE)
Proof
  strip_tac >> Cases_on ‘contradiction Γ₁’ >> simp[]
  >- (fs[contradiction_EQ_NONE] >> metis_tac[PERM_MEM_EQ]) >>
  simp[contradiction_EQ_NONE] >> drule contradiction_EQ_SOME >>
  simp[] >> metis_tac[PERM_MEM_EQ]
QED


Inductive tableauR:
[~conj:]
  (∀p s f1 f2.
      tableauR (p ++ [f1;f2] ++ s) r ⇒
      tableauR (p ++ [Conj f1 f2] ++ s) r)
[~disj1:]
  (∀p s f1 f2.
      tableauR (p ++ [f1] ++ s) r ⇒ tableauR (p ++ [Disj f1 f2] ++ s) r)
[~disj2:]
  (∀p s f1 f2.
      tableauR (p ++ [f2] ++ s) r ⇒ tableauR (p ++ [Disj f1 f2] ++ s) r)
[~diam:]
  (∀G.
      (∀f. MEM f G ⇒ ¬is_conj f ∧ ¬is_disj f) ∧ (∃f. MEM f G ∧ is_dia f) ∧
      contradiction G = NONE ∧
      LIST_REL (λf r. tableauR (dest_dia f :: unbox G) r)
               (FILTER is_dia G)
               rs
     ⇒
      tableauR G (Nd (unvar G) rs))
[~open:]
  (∀G. (∀f. MEM f G ⇒ is_literal f ∨ is_box f) ∧ contradiction G = NONE ⇒
       tableauR G (Nd (unvar G) []))
End

Theorem scmap_LENGTH:
  ∀l r. scmap f l = SOME r ⇒ LENGTH l = LENGTH r
Proof
  Induct >> simp[AllCaseEqs(), PULL_EXISTS]
QED

Theorem LENGTH_undia:
  LENGTH (undia G) = LENGTH (FILTER is_dia G)
Proof
  Induct_on ‘G’ >> simp[] >> Cases >> simp[]
QED

Theorem MAP_undia:
  MAP f (undia G) = MAP (f o dest_dia) (FILTER is_dia G)
Proof
  Induct_on ‘G’ >> simp[] >> Cases >> simp[]
QED

Theorem scmap_MAP:
  scmap f (MAP g l) = scmap (f o g) l
Proof
  Induct_on ‘l’ >> simp[]
QED

Triviality FORALL_NUM:
  (∀n. P n) ⇔ P 0 ∧ ∀n. P (SUC n)
Proof
  eq_tac >> simp[] >> rw[] >> Cases_on ‘n’ >> simp[]
QED

Theorem scmap_EQ_SOME:
  ∀l r. scmap f l = SOME r ⇔
        LENGTH l = LENGTH r ∧ ∀i. i < LENGTH l ⇒ f (EL i l) = SOME (EL i r)
Proof
  Induct >> simp[AllCaseEqs(), PULL_EXISTS] >>
  rw[] >> Cases_on ‘f h’ >> simp[]
  >- (strip_tac >> qexists_tac‘0’ >> simp[]) >>
  Cases_on ‘r’ >> simp[] >> simp[Once FORALL_NUM, SimpRHS] >> simp[] >>
  metis_tac[]
QED

Theorem disj_ps_append:
¬is_disj f ⇒ (f :: G = p ++ [Disj f1 f2] ++ s ⇔
              ∃p'. p = f :: p' ∧ G = p' ++ [Disj f1 f2] ++ s)
Proof
  Induct_on ‘G’ >> simp[APPEND_EQ_CONS] >> Cases_on ‘f’ >>
  dsimp[APPEND_EQ_CONS]
QED

Theorem conj_ps_append:
¬is_conj f ⇒ (f :: G = p ++ [Conj f1 f2] ++ s ⇔
              ∃p'. p = f :: p' ∧ G = p' ++ [Conj f1 f2] ++ s)
Proof
  Induct_on ‘G’ >> simp[APPEND_EQ_CONS] >> Cases_on ‘f’ >>
  dsimp[APPEND_EQ_CONS]
QED


Theorem disjsplit_EQ_SOME:
  ∀G G1 G2.
    disjsplit G = SOME (G1, G2) ⇔
    ∃p s f1 f2. G = p ++ [Disj f1 f2] ++ s ∧ (∀f. MEM f p ⇒ ¬is_disj f) ∧
                G1 = p ++ [f1] ++ s ∧ G2 = p ++ [f2] ++ s
Proof
  Induct >> simp[] >> Cases >>
  simp[EXISTS_PROD, PULL_EXISTS, disj_ps_append, DISJ_IMP_THM, FORALL_AND_THM]>>
  TRY (metis_tac[]) >>
  rw[EQ_IMP_THM]
  >- (qexists_tac ‘[]’ >> simp[]) >> Cases_on ‘p’ >> fs[] >> rw[] >>
  fs[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem conjsplit_EQ_SOME:
  ∀G1 G2. conjsplit G1 = SOME G2 ⇔
          ∃p f1 f2 s. G1 = p ++ [Conj f1 f2] ++ s ∧
                      (∀f. MEM f p ⇒ ¬is_conj f) ∧
                      G2 = p ++ [f1;f2] ++ s
Proof
  Induct >> simp[] >> Cases >>
  simp[conj_ps_append, PULL_EXISTS, DISJ_IMP_THM, FORALL_AND_THM] >>
  TRY (metis_tac[]) >>
  rw[EQ_IMP_THM] >- (qexists_tac ‘[]’ >> simp[]) >>
  Cases_on ‘p’ >> fs[] >> rw[] >> fs[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem tableau_tableauR:
  ∀Γ r. tableau Γ = SOME r ⇒ tableauR Γ r
Proof
  ho_match_mp_tac tableau_ind >> qx_gen_tac ‘G’ >> strip_tac >>
  ONCE_REWRITE_TAC [tableau_def] >>
  simp[AllCaseEqs()] >> rw[]
  >- (irule tableauR_open >> rw[] >> fs[EVERY_MEM])
  >- (reverse (Cases_on ‘∃f. MEM (Dia f) G’)
      >- (‘undia G = []’
           by (Cases_on ‘undia G’ >> simp[] >>
               ‘∃df. MEM df (undia G)’ by simp[EXISTS_OR_THM] >>
               fs[MEM_undia] >> rfs[]) >>
          fs[] >> rw[] >>
          irule tableauR_open >> rw[] >>
          fs[conjsplit_EQ_NONE, disjsplit_EQ_NONE] >> Cases_on ‘f’ >>
          fs[] >> rfs[]) >>
      (* K rule *) irule tableauR_diam >> rw[]
      >- (fs[conjsplit_EQ_NONE] >> Cases_on ‘f’ >> rfs[])
      >- (fs[disjsplit_EQ_NONE] >> Cases_on ‘f’ >> rfs[])
      >- metis_tac[is_dia_def] >>
      simp[LIST_REL_EL_EQN] >> rw[]
      >- (drule scmap_LENGTH >> simp[LENGTH_undia]) >>
      fs[MAP_undia] >>
      fs[scmap_MAP, combinTheory.o_ABS_R, combinTheory.o_ABS_L, MEM_MAP,
         PULL_EXISTS] >>
      first_x_assum irule >> reverse conj_tac >- metis_tac[MEM_EL] >>
      fs[scmap_EQ_SOME])
  >- (fs[disjsplit_EQ_SOME] >> metis_tac[tableauR_rules])
  >- (fs[disjsplit_EQ_SOME] >> metis_tac[tableauR_rules]) >>
  fs[] >> fs[conjsplit_EQ_SOME] >> metis_tac[tableauR_rules]
QED

Theorem tableauR_tableau_EQ_NONE:
  (∀r. ¬tableauR Γ r) ⇒ (tableau Γ = NONE)
Proof
  Cases_on ‘tableau Γ’ >> simp[] >> metis_tac[tableau_tableauR]
QED


Theorem tableauR_sound:
  ∀Γ r. tableauR Γ r ⇒ ∀f. MEM f Γ ⇒ forces (tree_model r) r f
Proof
  Induct_on ‘tableauR’ >> rw[] >> simp[]
  >- (rename [‘forces _ _ ϕ’] >>
      ‘¬is_conj ϕ ∧ ¬is_disj ϕ’ by metis_tac[] >>
      Cases_on ‘ϕ’ >> fs[]
      >- (fs[contradiction_EQ_NONE] >> metis_tac[])
      >- (rename [‘MEM (Box ϕ) Γ’] >>
          fs[LIST_REL_EL_EQN] >> simp[tree_rel_def, PULL_EXISTS] >>
          qx_gen_tac ‘t'’ >> strip_tac >>
          ‘∃i. i < LENGTH rs ∧ t' = EL i rs’ by metis_tac[MEM_EL] >>
          first_x_assum (qspec_then ‘i’ mp_tac)  >> simp[] >> strip_tac >>
          first_x_assum (qspec_then ‘ϕ’ mp_tac) >> simp[MEM_unbox] >>
          strip_tac >> irule forces_grows_backward >>
          qexists_tac ‘tree_model (EL i rs)’ >> simp[] >> reverse conj_tac
          >- (simp[SUBSET_DEF, tree_model_def] >> qx_gen_tac ‘w’ >> strip_tac >>
              irule (relationTheory.RTC_RULES |> SPEC_ALL |> CONJUNCT2) >>
              simp[tree_rel_def] >> metis_tac[MEM_EL]) >>
          simp[tree_rel_def, tree_model_def, PULL_EXISTS] >> rw[] >>
          irule (relationTheory.RTC_RULES_RIGHT1 |> SPEC_ALL |> CONJUNCT2) >>
          metis_tac[tree_rel_def])
      >- (rename [‘MEM (Dia ϕ) Γ’] >>
          fs[LIST_REL_EL_EQN] >>
          ‘MEM (Dia ϕ) (FILTER is_dia Γ)’ by simp[MEM_FILTER] >>
          ‘∃i. i < LENGTH rs ∧ Dia ϕ = EL i (FILTER is_dia Γ)’
            by metis_tac[MEM_EL] >>
          first_x_assum (qspec_then ‘i’ mp_tac) >> simp[] >> strip_tac >>
          first_x_assum (qspec_then ‘ϕ’ mp_tac) >> impl_tac
          >- (first_x_assum (SUBST_ALL_TAC o SYM) >> simp[]) >>
          strip_tac >> qexists_tac ‘EL i rs’ >> rw[]
          >- (simp[tree_model_def] >> irule relationTheory.RTC_SINGLE >>
              metis_tac[tree_rel_def, MEM_EL])
          >- (metis_tac[tree_rel_def, MEM_EL]) >>
          irule forces_grows_backward >> qexists_tac ‘tree_model (EL i rs)’ >>
          simp[] >> rw[tree_model_def, SUBSET_DEF, tree_rel_def]
          >- (irule (relationTheory.RTC_RULES_RIGHT1 |> SPEC_ALL |> CONJUNCT2)>>
              metis_tac[tree_rel_def]) >>
          irule (relationTheory.RTC_RULES |> SPEC_ALL |> CONJUNCT2) >>
          metis_tac[tree_rel_def, MEM_EL])) >>
  first_x_assum drule >> rename [‘MEM ϕ Γ’] >> Cases_on ‘ϕ’ >> simp[]
  >- metis_tac[contradiction_EQ_NONE] >>
  simp[tree_model_def, tree_rel_def]
QED

Theorem tableau_EQ_NONE_tableauR:
  tableau Γ = NONE ⇒ ∀t. ¬tableauR Γ t
Proof
  rpt strip_tac >>
  map_every drule [tableau_complete |> INST_TYPE [alpha |-> “:tmodel”],
                   tableauR_sound] >>
  metis_tac[tree_model_thm]
QED

Theorem FA_NOT_SOME:
  (∀x. y ≠ SOME x) ⇔ y = NONE
Proof
  Cases_on ‘y’ >> simp[]
QED

Theorem tableau_EQ_NONE_IFF:
  tableau Γ = NONE ⇔ ∀r. ¬tableauR Γ r
Proof
  metis_tac [tableau_EQ_NONE_tableauR, tableau_tableauR, FA_NOT_SOME]
QED

Theorem tableauR_tableau:
  ∀Γ t. tableauR Γ t ⇒ ∃t'. tableau Γ = SOME t'
Proof
  CCONTR_TAC >> fs[FA_NOT_SOME] >> metis_tac[tableau_EQ_NONE_tableauR]
QED

Theorem contradiction_EQ_NONE_APPEND:
  contradiction (l1 ++ l2) = NONE ⇒
  contradiction l1 = NONE ∧ contradiction l2 = NONE
Proof
  simp[contradiction_EQ_NONE] >> metis_tac[]
QED

Theorem tableauR_weakening:
  ∀Γ Δ r. tableauR (Γ ++ Δ) r ⇒ ∃r. tableauR Γ r
Proof
  Induct_on ‘tableauR’ >> rw[]
  >- (pop_assum mp_tac >> simp[APPEND_EQ_APPEND, APPEND_EQ_CONS] >> rw[] >>
      simp[]
      >- (rename[‘tableauR (p ++ [Conj f1 f2] ++ s)’] >>
          ‘∃r. tableauR (p ++ [f1;f2] ++ s) r’
            suffices_by metis_tac[tableauR_rules] >>
          first_x_assum irule >> simp[]) >>
      rename [‘tableauR (p ++ [Conj f1 f2])’] >>
      ‘∃r. tableauR (p ++ [f1;f2]) r’
        suffices_by metis_tac[tableauR_rules, APPEND_NIL] >>
      first_x_assum irule >> simp[])
  >- (pop_assum mp_tac >> simp[APPEND_EQ_APPEND, APPEND_EQ_CONS] >> rw[] >>
      simp[]
      >- (rename [‘tableauR (p ++ [Disj f1 f2] ++ s)’] >>
          ‘∃r. tableauR (p ++ [f1] ++ s) r’
            suffices_by metis_tac[tableauR_rules] >>
          first_x_assum irule >> simp[]) >>
      rename [‘tableauR (p ++ [Disj f1 f2])’] >>
      ‘∃r. tableauR (p ++ [f1]) r’
        suffices_by metis_tac[tableauR_rules, APPEND_NIL] >>
      first_x_assum irule >> simp[])
  >- (pop_assum mp_tac >> simp[APPEND_EQ_APPEND, APPEND_EQ_CONS] >> rw[] >>
      simp[]
      >- (rename [‘tableauR (p ++ [Disj f1 f2] ++ s)’] >>
          ‘∃r. tableauR (p ++ [f2] ++ s) r’
            suffices_by metis_tac[tableauR_rules] >>
          first_x_assum irule >> simp[]) >>
      rename [‘tableauR (p ++ [Disj f1 f2])’] >>
      ‘∃r. tableauR (p ++ [f2]) r’
        suffices_by metis_tac[tableauR_rules, APPEND_NIL] >>
      first_x_assum irule >> simp[])
  >- (reverse (Cases_on ‘∃g. is_dia g ∧ MEM g Γ’)
      >- (rename [‘is_dia ϕ’, ‘MEM ϕ (Γ ++ Δ)’] >>
          ‘¬MEM ϕ Γ’ by metis_tac[] >>
          fs[FILTER_APPEND_DISTRIB] >>
          qexists_tac ‘Nd (unvar Γ) []’ >>
          irule tableauR_open >>
          fs[contradiction_EQ_NONE] >> Cases >> simp[] >>
          metis_tac[is_conj_def, is_disj_def, is_dia_def]) >>
      pop_assum strip_assume_tac >>
      qpat_x_assum ‘MEM _ (_ ++ _)’ (K ALL_TAC) >>
      fs[FILTER_APPEND_DISTRIB, DISJ_IMP_THM, FORALL_AND_THM, unbox_APPEND]>>
      drule_then strip_assume_tac contradiction_EQ_NONE_APPEND >>
      drule_then (drule_then (drule_then drule))
                 (SIMP_RULE bool_ss [PULL_EXISTS] tableauR_diam) >>
      disch_then (fn th =>
      ‘∃ts. LIST_REL (λf r. tableauR (dest_dia f :: unbox Γ) r)
            (FILTER is_dia Γ) ts’
                   suffices_by metis_tac[th]) >>
      fs[LIST_REL_SPLIT1] >>
      qpat_assum ‘LIST_REL _ (FILTER is_dia Γ) _’
                 (mp_then (Pos last) mp_tac LIST_REL_mono) >>
      disch_then (qspec_then ‘λf r0. ∃r. tableauR (dest_dia f :: unbox Γ) r’
                  mp_tac) >> impl_tac
      >- rw[] >>
      simp[LIST_REL_EL_EQN] >>
      CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss())
                           [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM])) >>
      simp[PULL_EXISTS] >> qx_gen_tac ‘ff’ >> strip_tac >>
      qexists_tac ‘GENLIST ff (LENGTH (FILTER is_dia Γ))’ >>
      simp[]) >>
  metis_tac[contradiction_EQ_NONE_APPEND, tableauR_rules, MEM_APPEND]
QED

Theorem tableau_EQ_NONE_weakening:
  ∀Γ Δ. tableau Γ = NONE ⇒ tableau (Γ ++ Δ) = NONE
Proof
  metis_tac[tableau_EQ_NONE_IFF, tableauR_weakening]
QED

Theorem CONS_EQ_APPEND:
  h::t = l1 ++ l2 ⇔
    l1 = [] ∧ l2 = h::t ∨
    ∃t1. l1 = h::t1 ∧ t = t1 ++ l2
Proof
  Cases_on ‘l1’ >> simp[EQ_SYM_EQ]
QED

Theorem PERM_MEMBER:
  ∀p1 x s1 l2. PERM (p1 ++ [x] ++ s1) l2 ⇒ ∃p2 s2. l2 = p2 ++ [x] ++ s2
Proof
  Induct_on ‘PERM’ >> simp[] >> rw[] >~
  [‘p1 ++ [y] ++ s1 = x::t’, ‘PERM t l2’]
  >- (gvs[CONS_EQ_APPEND, SF DNF_ss] >> metis_tac[]) >~
  [‘p1 ++ [y] ++ s1 = x1::x2::t’]
  >- (gvs[CONS_EQ_APPEND, SF DNF_ss] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem PERM_CONTRADICTION_NONE:
  PERM Γ₁ Γ₂ ⇒ (contradiction Γ₁ = NONE ⇔ contradiction Γ₂ = NONE)
Proof
  Induct_on ‘PERM’ >> simp[] >> rw[] >~
  [‘contradiction (x::Γ₁) = NONE’, ‘PERM Γ₁ Γ₂’]
  >- (Cases_on ‘x’ >> simp[AllCaseEqs()] >> metis_tac[MEM_PERM]) >~
  [‘contradiction (x1::x2::Γ₁)’]
  >- (Cases_on ‘x1’ >> simp[AllCaseEqs()] >> Cases_on ‘x2’ >>
      simp[AllCaseEqs()] >> metis_tac[MEM_PERM])
QED


Theorem LIST_REL_PERM1[local]:
  ∀l11 l21 l12. LIST_REL R l11 l21 ∧ PERM l11 l12 ⇒
                ∃l22. LIST_REL R l12 l22
Proof
  Induct_on ‘PERM’ >> simp[] >> rw[] >>
  first_x_assum $ drule_then strip_assume_tac >>
  metis_tac[LIST_REL_rules]
QED

Theorem PERM_unbox:
  PERM l1 l2 ⇒ PERM (unbox l1) (unbox l2)
Proof
  Induct_on ‘PERM’ >> simp[] >> rw[] >~
  [‘unbox (x::y::t)’]
  >- (map_every Cases_on [‘x’, ‘y’] >> simp[PERM_SWAP_AT_FRONT]) >~
  [‘unbox (x::t)’]
  >- (Cases_on ‘x’ >> simp[]) >>
  metis_tac[PERM_TRANS]
QED

Theorem tableauR_exchange:
  ∀Γ₁ t₁. tableauR Γ₁ t₁ ⇒ ∀Γ₂. PERM Γ₁ Γ₂ ⇒ ∃t₂. tableauR Γ₂ t₂
Proof
  Induct_on ‘tableauR’ >> rw[] >~
  [‘PERM (p1 ++ [Conj f1 f2] ++ s1) Γ₂’]
  >- (drule_then strip_assume_tac PERM_MEMBER >> gvs[] >>
      irule_at Any tableauR_conj >> first_x_assum $ irule_at Any >>
      pop_assum mp_tac >> CONV_TAC (BINOP_CONV permLib.PERM_NORMALISE_CONV) >>
      metis_tac[PERM_SYM]) >~
  [‘PERM (p1 ++ [Disj f1 f2] ++ s1) _’, ‘tableauR (p1 ++ [f1] ++ s1) _’]
  >- (drule_then strip_assume_tac PERM_MEMBER >> gvs[] >>
      irule_at Any tableauR_disj1 >> first_x_assum $ irule_at Any >>
      pop_assum mp_tac >> CONV_TAC (BINOP_CONV permLib.PERM_NORMALISE_CONV) >>
      metis_tac[PERM_SYM]) >~
  [‘PERM (p1 ++ [Disj f1 f2] ++ s1) _’, ‘tableauR (p1 ++ [f2] ++ s1) _’]
  >- (drule_then strip_assume_tac PERM_MEMBER >> gvs[] >>
      irule_at Any tableauR_disj2 >> first_x_assum $ irule_at Any >>
      pop_assum mp_tac >> CONV_TAC (BINOP_CONV permLib.PERM_NORMALISE_CONV) >>
      metis_tac[PERM_SYM]) >~
  [‘contradiction Γ₁ = NONE’, ‘is_literal _ ∨ is_box _’]
  >- metis_tac[tableauR_open, PERM_CONTRADICTION_NONE, MEM_PERM] >~
  [‘contradiction Γ₁ = NONE’, ‘is_dia f’]
  >- (irule_at Any tableauR_diam >>
      first_assum $ irule_at (Pat ‘is_dia _’) >>
      simp[RIGHT_EXISTS_AND_THM] >> reverse (rpt conj_tac)
      >- (irule LIST_REL_PERM1 >>
          irule_at Any PERM_FILTER >> first_assum $ irule_at Any >>
          rename [‘LIST_REL _ _ trees’] >>
          gvs[LIST_REL_CONJ] >>
          qpat_x_assum ‘LIST_REL _ _ _’ mp_tac >>
          simp[LIST_REL_EL_EQN, SF CONJ_ss] >>
          qabbrev_tac ‘dia_fs = FILTER is_dia Γ₁’ >>
          ‘∀n. n < LENGTH trees ⇒
               PERM (dest_dia (EL n dia_fs) :: unbox Γ₁)
                    (dest_dia (EL n dia_fs) :: unbox Γ₂)’
            by simp[PERM_unbox] >>
          strip_tac >>
          first_assum (first_assum o resolve_then (Pat ‘PERM _ _’) mp_tac) >>
          disch_then (qx_choose_then ‘mktree’ assume_tac o
                      SRULE [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]) >>
          qexists_tac ‘GENLIST mktree (LENGTH trees)’ >> simp[]) >>
      metis_tac[PERM_CONTRADICTION_NONE, MEM_PERM])
QED

Theorem tableau_EQ_NONE_PERM:
  PERM Γ₁ Γ₂ ∧ tableau Γ₁ = NONE ⇒
  tableau Γ₂ = NONE
Proof
  CCONTR_TAC >> gs[] >>
  Cases_on ‘tableau Γ₂’ >> gs[] >>
  drule_then assume_tac tableau_tableauR >>
  ‘∃tr. tableauR Γ₁ tr’ by metis_tac[PERM_SYM, tableauR_exchange] >>
  drule tableau_EQ_NONE_tableauR >> simp[SF SFY_ss]
QED

Theorem tableau_EQ_SOME_PERM:
  PERM Γ₁ Γ₂ ∧ tableau Γ₁ = SOME tm1 ⇒
  ∃tm2. tableau Γ₂ = SOME tm2
Proof
  Cases_on ‘tableau Γ₂’ >> simp[] >> rpt strip_tac >>
  ‘tableau Γ₁ = NONE’ by metis_tac[tableau_EQ_NONE_PERM, PERM_SYM] >>
  gs[]
QED

val _ = export_theory();
