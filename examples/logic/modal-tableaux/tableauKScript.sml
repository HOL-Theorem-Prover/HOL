(* See:

     Wu and Goré, "Verified Decision Procedures for Modal Logics", ITP 2019

   for inspiration

*)

open HolKernel Parse boolLib bossLib;

open pairTheory pred_setTheory listTheory
open sortingTheory
open mp_then
val _ = new_theory "tableauK";

Datatype: form = Var num | NVar num | Conj form form | Disj form form
                | Box form | Dia form
End
val _ = export_rewrites ["form_size_def"]

Datatype: model = <| rel : α -> α -> bool ; valt : α -> num -> bool ;
                     worlds : α set |>
End

Definition forces_def[simp]:
  (forces M w (Var n)      ⇔ M.valt w n) ∧
  (forces M w (NVar n)     ⇔ ¬M.valt w n) ∧
  (forces M w (Conj f1 f2) ⇔ forces M w f1 ∧ forces M w f2) ∧
  (forces M w (Disj f1 f2) ⇔ forces M w f1 ∨ forces M w f2) ∧
  (forces M w (Box f)      ⇔ ∀v. v ∈ M.worlds ∧ M.rel w v ⇒ forces M v f) ∧
  (forces M w (Dia f)      ⇔ ∃v. v ∈ M.worlds ∧ M.rel w v ∧ forces M v f)
End

Definition sat_def:
  sat (tyit : α itself) Γ ⇔ ∃M (w:α). w ∈ M.worlds ∧ ∀f. f ∈ Γ ⇒ forces M w f
End

Definition contradiction_def[simp]:
  (contradiction [] ⇔ NONE) ∧
  (contradiction (Var n :: rest) ⇔
     if MEM (NVar n) rest then SOME n
     else contradiction rest) ∧
  (contradiction (NVar n :: rest) ⇔
     if MEM (Var n) rest then SOME n else  contradiction rest) ∧
  (contradiction (_ :: rest) ⇔ contradiction rest)
End

Theorem contradiction_EQ_NONE:
  ∀Γ. contradiction Γ = NONE ⇔ ∀n. MEM (Var n) Γ ⇒ ¬MEM (NVar n) Γ
Proof
  Induct >> simp[] >> Cases >> simp[AllCaseEqs()] >> metis_tac[]
QED

Theorem contradiction_EQ_SOME:
  (contradiction Γ = SOME i) ⇒ MEM (Var i) Γ ∧ MEM (NVar i) Γ
Proof
  Induct_on ‘Γ’ >> simp[] >> Cases >> simp[AllCaseEqs()] >> metis_tac[]
QED


Definition conjsplit_def[simp]:
  (conjsplit (Conj f1 f2 :: rest) = SOME (f1 :: f2 :: rest)) ∧
  (conjsplit (f :: rest) = OPTION_MAP (CONS f) (conjsplit rest)) ∧
  (conjsplit [] = NONE)
End

Theorem conjsplit_EQ_NONE:
  ∀Γ. conjsplit Γ = NONE ⇔ ∀f1 f2. ¬(MEM (Conj f1 f2) Γ)
Proof
  Induct >> simp[] >> Cases >> simp[] >> metis_tac[]
QED

Theorem MEM_conjsplit:
  ∀Γ₀ Γ ϕ. conjsplit Γ₀ = SOME Γ ∧ MEM ϕ Γ₀ ⇒
            (∃ϕ₁ ϕ₂. ϕ = Conj ϕ₁ ϕ₂ ∧ MEM ϕ₁ Γ ∧ MEM ϕ₂ Γ) ∨
            MEM ϕ Γ
Proof
  Induct >> simp[] >> Cases >> simp[PULL_EXISTS] >> metis_tac[]
QED

Theorem conjsplit_MEM2:
  ∀Γ₀ Γ ϕ. conjsplit Γ₀ = SOME Γ ∧ MEM ϕ Γ ⇒
           MEM ϕ Γ₀ ∨ (∃ϕ'. MEM (Conj ϕ ϕ') Γ₀) ∨
           (∃ϕ'. MEM (Conj ϕ' ϕ) Γ₀)
Proof
  Induct >> simp[] >> Cases >> csimp[PULL_EXISTS] >> metis_tac[]
QED

Definition disjsplit_def[simp]:
  disjsplit (Disj f1 f2 :: rest) = SOME (f1::rest, f2::rest) ∧
  disjsplit (f :: rest) = OPTION_MAP (CONS f ## CONS f) (disjsplit rest) ∧
  disjsplit [] = NONE
End

Theorem disjsplit_EQ_NONE:
  ∀Γ. disjsplit Γ = NONE ⇔ ∀f1 f2. ¬(MEM (Disj f1 f2) Γ)
Proof
  Induct >> simp[] >> Cases >> simp[] >> metis_tac[]
QED

Theorem MEM_disjsplit:
  ∀Γ Γ1 Γ2 ϕ.
    disjsplit Γ = SOME (Γ1, Γ2) ∧ MEM ϕ Γ ⇒
      (∃ϕ₁ ϕ₂. ϕ = Disj ϕ₁ ϕ₂ ∧ MEM ϕ₁ Γ1 ∧ MEM ϕ₂ Γ2) ∨
      MEM ϕ Γ1 ∧ MEM ϕ Γ2
Proof
  Induct >> dsimp[] >> conj_tac >> Cases >> simp[EXISTS_PROD, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem disjsplit_MEM2:
  ∀Γ Γ1 Γ2 f1 f2.
     MEM f1 Γ1 ∧ MEM f2 Γ2 ∧ disjsplit Γ = SOME (Γ1,Γ2) ⇒
     MEM f1 Γ ∨ MEM f2 Γ ∨ MEM (Disj f1 f2) Γ
Proof
  Induct >> simp[] >> Cases >> simp[PULL_EXISTS, EXISTS_PROD] >> metis_tac[]
QED



Definition unbox_def[simp]:
  unbox (Box f :: rest) = f :: unbox rest ∧
  unbox (f :: rest) = unbox rest ∧
  unbox [] = []
End

Theorem MEM_unbox:
  MEM ϕ (unbox Γ) ⇔ MEM (Box ϕ) Γ
Proof
  Induct_on ‘Γ’ >> simp[] >> Cases >> simp[] >> metis_tac[]
QED

Theorem unbox_APPEND:
  unbox (Γ ++ Δ) = unbox Γ ++ unbox Δ
Proof
  Induct_on ‘Γ’ >> simp[] >> Cases >> simp[]
QED


Definition undia_def[simp]:
  undia (Dia f :: rest) = f :: undia rest ∧
  undia (f :: rest) = undia rest ∧
  undia [] = []
End

Theorem MEM_undia:
  MEM ϕ (undia Γ) ⇔ MEM (Dia ϕ) Γ
Proof
  Induct_on ‘Γ’ >> simp[] >> Cases >> simp[]
QED

Definition unvar_def[simp]:
  unvar (Var n :: rest) = n :: unvar rest ∧
  unvar (f :: rest) = unvar rest ∧
  unvar [] = []
End

Theorem MEM_unvar[simp]:
  MEM n (unvar Γ) ⇔ MEM (Var n) Γ
Proof
  Induct_on ‘Γ’ >> simp[] >> Cases >> simp[]
QED

Datatype: tmodel = Nd (num list) (tmodel list)
End

Theorem tmodel_size_def[simp] = definition "tmodel_size_def"

Theorem MEM_tmodel_size:
  MEM t ts ⇒ tmodel_size t < tmodel1_size ts
Proof
  Induct_on ‘ts’ >> rw[] >> res_tac >> simp[]
QED

Theorem tmodel_ind:
  ∀P. (∀vs ts. (∀t. MEM t ts ⇒ P t) ⇒ P (Nd vs ts)) ⇒
      (∀t. P t)
Proof
  rpt strip_tac >>
  completeInduct_on ‘tmodel_size t’ >> Cases >>
  rw[] >> fs[PULL_FORALL] >> last_x_assum irule >> rpt strip_tac >>
  first_x_assum irule >> drule MEM_tmodel_size >> simp[]
QED

val _ = TypeBase.update_induction tmodel_ind

Definition is_literal_def[simp]:
  (is_literal (Var _) ⇔ T) ∧ (is_literal (NVar _) ⇔ T) ∧ (is_literal _ ⇔ F)
End

Theorem disjsplit_size:
  ∀Γ fs1 fs2. disjsplit Γ = SOME (fs1, fs2) ⇒
                  SUM (MAP form_size fs1) < SUM (MAP form_size Γ) ∧
                  SUM (MAP form_size fs2) < SUM (MAP form_size Γ)
Proof
  Induct_on ‘Γ’ >> simp[disjsplit_def] >> Cases >>
  simp[disjsplit_def, FORALL_PROD, PULL_EXISTS]
QED

Theorem conjsplit_size:
  ∀Γ fs. conjsplit Γ = SOME fs ⇒
         SUM (MAP form_size fs) < SUM (MAP form_size Γ)
Proof
  Induct >> simp[conjsplit_def] >> Cases >>
  simp[conjsplit_def, FORALL_PROD, PULL_EXISTS]
QED

val _ = overload_on("gsize", “λl. SUM (MAP form_size l)”)
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

Definition scmap_def[simp]:
  scmap f [] = SOME [] ∧
  scmap f (h :: t) =
    case f h of
       NONE => NONE
     | SOME fh => OPTION_MAP (CONS fh) (scmap f t)
End

Theorem scmap_CONG[defncong]:
  ∀l1 l2 f1 f2. (l1 = l2) ∧ (∀e. MEM e l1 ⇒ f1 e = f2 e) ⇒
                (scmap f1 l1 = scmap f2 l2)
Proof
  rw[] >> rename [‘scmap _ l’] >> Induct_on ‘l’ >> simp[scmap_def]
QED

Theorem scmap_MEM:
  ∀l0 l e f. scmap f l0 = SOME l ∧ MEM e l ⇒ ∃e0. MEM e0 l0 ∧ f e0 = SOME e
Proof
  Induct >> dsimp[AllCaseEqs()]
QED

Theorem scmap_MEM2:
  ∀l0 l e0 f. scmap f l0 = SOME l ∧ MEM e0 l0 ⇒ ∃e. MEM e l ∧ f e0 = SOME e
Proof
  Induct >> dsimp[AllCaseEqs()]
QED

Theorem scmap_EQ_NONE[simp]:
  ∀l f. scmap f l = NONE ⇔ ∃e. MEM e l ∧ f e = NONE
Proof
  Induct >> dsimp[AllCaseEqs()] >> metis_tac[TypeBase.nchotomy_of “:α option”]
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

Definition tree_rel_def:
  tree_rel t1 t2 ⇔ ∃vs ts. t1 = Nd vs ts ∧ MEM t2 ts
End

Theorem tree_rel_size_bounds:
  tree_rel t1 t2 ⇒ tmodel_size t2 ≤ tmodel_size t1
Proof
  simp[tree_rel_def, PULL_EXISTS] >> rw[] >>
  drule MEM_tmodel_size >> simp[]
QED

Definition tree_model_def:
  tree_model t =
    <| rel := tree_rel ;
       valt := λt v. case t of Nd vs _ => MEM v vs ;
       worlds := { t' | RTC tree_rel t t' }
    |>
End

Theorem tree_model_thm[simp]:
  ((tree_model t).valt = λu v. case u of Nd vs _ => MEM v vs) ∧
  (tree_model t).rel = tree_rel ∧
  m ∈ (tree_model m).worlds
Proof
  simp[tree_model_def]
QED

Definition subtree_def:
  subtree t1 t2 ⇔ tree_rel^* t2 t1
End

Theorem FINITE_tree_model_worlds[simp]:
  ∀t. FINITE (tree_model t).worlds
Proof
  simp[tree_model_def] >> Induct >> simp[tree_rel_def] >>
  simp[Once relationTheory.RTC_CASES1] >> simp[GSPEC_OR, tree_rel_def] >>
  qmatch_abbrev_tac ‘FINITE s’ >>
  ‘s = BIGUNION (IMAGE (λt. { u | RTC tree_rel t u }) (set ts))’
    by (simp[Abbr‘s’, Once EXTENSION, PULL_EXISTS] >> metis_tac[]) >>
  simp[PULL_EXISTS]
QED

Theorem forces_grows_backward:
  ∀w. forces M1 w f ∧ M2.valt = M1.valt ∧ M2.rel = M1.rel ∧
      M1.worlds ⊆ M2.worlds ∧ w ∈ M1.worlds ∧
      (∀w1 w2. M1.rel w1 w2 ∧ w1 ∈ M1.worlds ⇒ w2 ∈ M1.worlds) ⇒
      forces M2 w f
Proof
  Induct_on ‘f’ >> simp[]
  >- metis_tac[]
  >- metis_tac[]
  >- (rw[] >> fs[] >> metis_tac[SUBSET_DEF])
  >- (rw[] >> fs[] >> metis_tac[SUBSET_DEF])
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
  ∀Γ. tableau Γ = NONE ⇒ ∀M w. w ∈ M.worlds ⇒ ∃f. MEM f Γ ∧ ¬forces M w f
Proof
  ho_match_mp_tac tableau_ind >> gen_tac >> strip_tac >>
  simp[Once tableau_def] >> simp[AllCaseEqs()] >> rw[] >>
  fs[MEM_MAP, PULL_EXISTS, MEM_undia, MEM_unbox]
  >- ((* K rule *)
      rw[] >> fs[RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
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
      Cases_on ‘M.valt w j’
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

Definition is_conj_def[simp]:
  is_conj (Conj _ _ ) = T ∧
  is_conj _ = F
End

Definition is_disj_def[simp]:
  is_disj (Disj f1 f2) = T ∧
  is_disj _ = F
End

Definition is_dia_def[simp]:
  is_dia (Dia _) = T ∧
  is_dia _ = F
End

Definition dest_dia_def[simp]:
  dest_dia (Dia f) = f
End

Definition is_box_def[simp]:
  is_box (Box _) = T ∧
  is_box _ = F
End

Inductive tableauR:
  (∀p s f1 f2.
      tableauR (p ++ [f1;f2] ++ s) r ⇒
      tableauR (p ++ [Conj f1 f2] ++ s) r) ∧
  (∀p s f1 f2.
      tableauR (p ++ [f1] ++ s) r ⇒ tableauR (p ++ [Disj f1 f2] ++ s) r) ∧
  (∀p s f1 f2.
      tableauR (p ++ [f2] ++ s) r ⇒ tableauR (p ++ [Disj f1 f2] ++ s) r) ∧
  (∀G.
      (∀f. MEM f G ⇒ ¬is_conj f ∧ ¬is_disj f) ∧ (∃f. MEM f G ∧ is_dia f) ∧
      contradiction G = NONE ∧
      LIST_REL (λf r. tableauR (dest_dia f :: unbox G) r)
               (FILTER is_dia G)
               rs
     ⇒
      tableauR G (Nd (unvar G) rs)) ∧
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
  Induct >> simp[AllCaseEqs(), PULL_EXISTS] >- metis_tac[] >>
  rw[] >> Cases_on ‘f h’ >> simp[]
  >- (disj2_tac >> qexists_tac‘0’ >> simp[]) >>
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
  >- (irule (last (CONJUNCTS tableauR_rules)) >> rw[] >> fs[EVERY_MEM])
  >- (reverse (Cases_on ‘∃f. MEM (Dia f) G’)
      >- (‘undia G = []’
           by (Cases_on ‘undia G’ >> simp[] >>
               ‘∃df. MEM df (undia G)’ by simp[EXISTS_OR_THM] >>
               fs[MEM_undia] >> rfs[]) >>
          fs[] >> rw[] >>
          irule (last (CONJUNCTS tableauR_rules)) >> rw[] >>
          fs[conjsplit_EQ_NONE, disjsplit_EQ_NONE] >> Cases_on ‘f’ >>
          fs[] >> rfs[]) >>
      (* K rule *) irule (el 4 (CONJUNCTS tableauR_rules)) >> rw[]
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
          irule (last (CONJUNCTS tableauR_rules)) >>
          fs[contradiction_EQ_NONE] >> Cases >> simp[] >>
          metis_tac[is_conj_def, is_disj_def, is_dia_def]) >>
      pop_assum strip_assume_tac >>
      qpat_x_assum ‘MEM _ (_ ++ _)’ (K ALL_TAC) >>
      fs[FILTER_APPEND_DISTRIB, DISJ_IMP_THM, FORALL_AND_THM, unbox_APPEND]>>
      drule_then strip_assume_tac contradiction_EQ_NONE_APPEND >>
      drule_then (drule_then (drule_then drule))
                 (SIMP_RULE bool_ss [PULL_EXISTS]
                    (el 4 (CONJUNCTS tableauR_rules))) >>
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
(*
Theorem tableauR_exchange:
  ∀Γ₁ t₁. tableauR Γ₁ t₁ ⇒ ∀Γ₂. PERM Γ₁ Γ₂ ⇒ ∃t₂. tableauR Γ₂ t₂
Proof
  Induct_on ‘tableauR’ >> rw[]
  >- (
  ho_match_mp_tac tableau_ind >> qx_gen_tac ‘G1’ >> strip_tac >>
  qx_gen_tac ‘G2’ >> Cases_on ‘PERM G1 G2’ >> ASM_REWRITE_TAC [] >>
  ONCE_REWRITE_TAC [tableau_def] >>
  reverse (Cases_on ‘contradiction G1’)
  >- (fs[] >> ‘∃i. contradiction G2 = SOME i’ suffices_by simp[PULL_EXISTS] >>
      CCONTR_TAC>>
      ‘contradiction G2 = NONE’ by (Cases_on ‘contradiction G2’ >> fs[]) >>
      pop_assum mp_tac >> drule contradiction_EQ_SOME >>
      simp[contradiction_EQ_NONE] >> metis_tac[PERM_MEM_EQ]) >>
  ‘contradiction G2 = NONE’ by metis_tac[PERM_leading_contradiction] >>
  ASM_REWRITE_TAC[] >> simp_tac(srw_ss()) [] >>
  RULE_ASSUM_TAC (REWRITE_RULE []) >>
  reverse (Cases_on ‘conjsplit G1’) >> fs[] >>

strip_tacrw[]recInduct_on ‘PERM’ >> simp[] >> rw[]
  >- ((* add common f to front of Γ₁ and Γ₂ that are permutations of each other
      *)
      rename [‘PERM Γ₁ Γ₂’, ‘tableau (f::Γ₁)’] >>
      ONCE_REWRITE_TAC [tableau_def] >>
      reverse (Cases_on ‘contradiction (f::Γ₁)’) >> simp[]
      >- (‘∃j. contradiction (f::Γ₂) = SOME j’ suffices_by simp[PULL_EXISTS] >>
          CCONTR_TAC >> fs[] >>
          ‘contradiction (f::Γ₂) = NONE’
            by (Cases_on ‘contradiction(f::Γ₂)’ >> fs[]) >>
          metis_tac[PERM_leading_contradiction, optionTheory.NOT_NONE_SOME])
      >- (‘contradiction (f::Γ₂) = NONE’
            by metis_tac[PERM_leading_contradiction] >> simp[]
                simp[contradiction_EQ_NONE] >>
                metis_tac[PERM_MEM_EQ]) >>
          simp[] >>
*)
val _ = export_theory();
