(* See:

     Wu and Goré, "Verified Decision Procedures for Modal Logics", ITP 2019

   for inspiration

*)

open HolKernel Parse boolLib bossLib;

open pairTheory pred_setTheory listTheory relationTheory;
open modalBasicsTheory tableauBasicsTheory

val _ = new_theory "tableauKT";

Definition trule_def[simp]:
  trule Σ (Box f :: rest) = (Box f::Σ, f::rest) ∧
  trule Σ (f :: rest) = ((\x. x) ## CONS f) (trule Σ rest) ∧
  trule Σ [] = (Σ, [])
End

Definition scmap2_def[simp]:
  scmap2 f _ [] = SOME [] ∧
  scmap2 f Σ (h :: t) =
    case f Σ h of
       NONE => NONE
     | SOME fsh => OPTION_MAP (CONS fsh) (scmap2 f Σ t)
End

Definition modal_size_def[simp]:
  modal_size (Var a) = 0 ∧
  modal_size (Box a) = 1 + modal_size a ∧
  modal_size (Dia a) = 1 + modal_size a ∧
  modal_size (NVar a) = 0 ∧
  modal_size (Conj a0 a1) = modal_size a0 + modal_size a1 ∧
  modal_size (Disj a0 a1) = modal_size a0 + modal_size a1
End

Definition max_list_def[simp]:
  max_list []     = 0 ∧
  max_list (h::t) = MAX h (max_list t)
End

Definition degree_def[simp]:
  degree ([],[])    = 0 ∧
  degree (s::Σ, Γ) = MAX (modal_size s) (degree (Σ, Γ)) ∧
  degree (Σ, g::Γ) = MAX (modal_size g) (degree (Σ, Γ))
End

Definition unbox_single_def[simp]:
  unbox_single (Box f) = f ∧
  unbox_single p = p
End

Theorem trule_all_unboxed[simp]:
  EVERY ($¬ ∘ is_box) Γ ⇒ trule Σ Γ = (Σ, Γ)
Proof
  Induct_on `Γ` >> rw[] >> Cases_on`h` >> fs[]
QED


(* Formulae from the history remains in the history after trule *)
Theorem trule_mem_left:
  ∀f l r. MEM f l ⇒ MEM f (FST (trule l r))
Proof
  Induct_on `r` >> rw[]
  >> first_x_assum drule
  >> rw[]
  >> Cases_on `h` >> rw[]
QED

(* Formulae from the formulae set either goes into history or stay in the set *)
Theorem trule_mem_right_simp[simp]:
∀f l r. MEM f r ⇒ MEM f (FST (trule l r)) ∨ MEM f (SND (trule l r))
Proof
 Induct_on `r` >> Cases_on `f` >> simp[] >> fs[]
  >> Cases_on `h` >> simp[] >> metis_tac[]
QED


(* in the right -> either stays in the right or moved to left with trule *)
Theorem trule_mem_right:
  ∀f l r. MEM f r ⇒
          is_box f ∧
            MEM f (FST (trule l r)) ∧
              MEM (HD (unbox [f])) (SND (trule l r)) ∨
          MEM f (SND (trule l r))
Proof
  Induct_on `r` >> Cases_on `f` >> simp[] >> fs[] >>
  rw[OR_INTRO_THM2] >> rw[] >>
  Cases_on `h` >> simp[] >> first_x_assum drule >> rw[] >>
  metis_tac[OR_INTRO_THM1]
QED


(* Formulae that ends up in the hisotry after trule are either
    1. from the history at the beginning or
    2. is from the formulae set and is boxed*)
Theorem trule_mem_left_rev:
   ∀f l r. MEM f (FST (trule l r)) ⇒ MEM f l ∨ is_box f ∧ MEM f r
Proof
  Induct_on `r` >> rw[] >>
  Cases_on `f` >> simp[] >> fs[] >>
  Cases_on `h` >> simp[] >> fs[] >> first_x_assum drule >>
  rw[] >> metis_tac[]
QED

(* If all formulae in the history are boxed then
   all formulae in the history after trule are still all boxed *)
Theorem trule_all_box:
  ∀f l r. (∀p. MEM p l ⇒ is_box p) ⇒
          MEM f (FST (trule l r)) ⇒
          is_box f
Proof
  Induct_on `r` >> rw[] >>
  Cases_on `f` >> simp[] >> fs[] >>
  Cases_on ‘h’ >> gs[] >> first_x_assum drule_all >> simp[]
QED

Theorem trule_result:
∀Sg p f s.
  (EVERY ($¬ ∘ is_box) p) ⇒
  (trule Sg (p ++ [Box f] ++ s) = ((Box f)::Sg, p ++ [f] ++ s))
Proof
  ho_match_mp_tac trule_ind >> fs[] >> rw[]
QED

Theorem unbox_trule_left:
  ∀l r f. MEM f (unbox l) ⇒ MEM f (unbox (FST (trule l r)))
Proof
  ho_match_mp_tac trule_ind >> rw[]
QED

Theorem scmap2_empt[simp]:
  scmap2 f s [] = SOME []
Proof
  rw[]
QED

Theorem scmap2_CONG[defncong]:
  ∀l1 l1' l2 l2' f1 f2.
     (l1 = l1') ∧ (l2 = l2') ∧ (∀e l.l = l1 ∧ MEM e l2' ⇒ f1 l e = f2 l e)
     ⇒ (scmap2 f1 l1 l2 = scmap2 f2 l1' l2')
Proof
  rw[] >> Induct_on ‘l2’ >> rw[]
QED

Theorem scmap2_MEM:
  ∀l0 l e f S.
    scmap2 f S l0 = SOME l ∧ MEM e l ⇒ ∃e0. MEM e0 l0 ∧ f S e0 = SOME e
Proof
  Induct >> dsimp[AllCaseEqs()]
QED

Theorem scmap2_MEM2:
  ∀l0 l e0 f S.
    scmap2 f S l0 = SOME l ∧ MEM e0 l0 ⇒ ∃e. MEM e l ∧ f S e0 = SOME e
Proof
  Induct >> dsimp[AllCaseEqs()]
QED

Theorem scmap2_EQ_NONE[simp]:
  ∀l f. scmap2 f s l = NONE ⇔ ∃e. MEM e l ∧ f s e = NONE
Proof
  Induct >> dsimp[AllCaseEqs()] >> metis_tac[TypeBase.nchotomy_of “:α option”]
QED

Theorem max_2_lists[simp]:
  ∀l1 l2. max_list (l1++l2) = MAX (max_list l1) (max_list l2)
Proof
  Induct_on`l1` >> simp[] >> Induct_on`l2` >> simp[]
  >> rw[] >> simp[arithmeticTheory.MAX_ASSOC]
QED

Theorem max_list_diff[simp]:
  ∀l1 l2 l3. max_list l2 < max_list l3 ⇒ max_list (l1++l2) <= max_list (l1++l3)
Proof
  rw[]
QED


Theorem degree_thm[simp]:
  degree (Σ, g::Γ) = MAX (modal_size g) (degree (Σ, Γ))
Proof
  Induct_on`Σ` >> simp[AC arithmeticTheory.MAX_COMM arithmeticTheory.MAX_ASSOC]
QED

Theorem degree_max_list:
∀Σ Γ.  degree (Σ, Γ) = max_list (MAP modal_size (Σ++Γ))
Proof
  Induct_on`Σ` >> Induct_on`Γ` >> simp[]
QED

Theorem degree_trule[simp]:
  ∀Σ Γ. degree (trule Σ Γ) = degree (Σ, Γ)
Proof
  Induct_on`Γ` >> simp[]
  >> Cases_on `h`>> rw[] >> Cases_on`trule Σ Γ` >> simp[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- (simp[arithmeticTheory.MAX_DEF] >> metis_tac[])
  >> metis_tac[]
QED

Theorem not_not_f[simp]:
  $¬ o $¬ o f = f
Proof
  simp[FUN_EQ_THM]
QED

Theorem trule_length:
  ∀Σ Γ. EXISTS is_box Γ ⇒
        degree (trule Σ Γ) = degree (Σ,Γ) ∧
        gsize (SND (trule Σ Γ)) < gsize Γ
Proof
  rw[] >>
  Induct_on `Γ`
  >- simp[]
  >> rw[]
  >> Cases_on `h` >> fs[]
QED

Theorem degree_inv[simp]:
  ∀Σ Γ Σ' Γ'.
    Σ = Σ' ∧ ((max_list $ MAP modal_size Γ) < (max_list $ MAP modal_size Γ')) ⇒
    degree (Σ, Γ) <= degree (Σ', Γ')
Proof
  rw[degree_max_list]
QED

Theorem conjsplit_degree:
  ∀Σ Γ Γ'. conjsplit Γ = SOME Γ' ⇒
           degree (Σ,Γ') < degree (Σ,Γ) ∨
           degree (Σ,Γ') = degree (Σ,Γ) ∧ gsize Γ' < gsize Γ
Proof
  Induct_on `Γ` >> simp[] >> Cases_on `h` >> rw[] >> fs[] (*  *)
  >- simp[arithmeticTheory.MAX_DEF]
  >> first_x_assum (qspec_then `Σ` assume_tac) >> drule conjsplit_size
  >> simp[arithmeticTheory.MAX_DEF]
QED

Theorem disjsplit_degree_p1:
  ∀Σ Γ p1 p2. disjsplit Γ = SOME (p1, p2) ⇒
           degree (Σ,p1) < degree (Σ,Γ) ∨
           degree (Σ,p1) = degree (Σ,Γ) ∧ gsize p1 < gsize Γ
Proof
  Induct_on `Γ` >> simp[] >> Cases_on `h` >> rw[] >>
  fs[pairTheory.PAIR_MAP, pairTheory.PAIR_FST_SND_EQ, pairTheory.PAIR]
  >- (first_x_assum (qspec_then `Σ` assume_tac) >>
      `disjsplit Γ = SOME (FST z,SND z)` by fs[] >>
      drule disjsplit_size >> simp[arithmeticTheory.MAX_DEF])
  >- (Cases_on `0 < modal_size f0` >> simp[] >>
      fs[arithmeticTheory.NOT_LESS, arithmeticTheory.MAX_DEF])
  >> first_x_assum (qspec_then `Σ` assume_tac) >>
  `disjsplit Γ = SOME (FST z,SND z)` by fs[] >>
  drule disjsplit_size >> simp[arithmeticTheory.MAX_DEF]
QED

Theorem disjsplit_degree_p2:
  ∀Σ Γ p1 p2. disjsplit Γ = SOME (p1, p2) ⇒
           degree (Σ,p2) < degree (Σ,Γ) ∨
           degree (Σ,p2) = degree (Σ,Γ) ∧ gsize p2 < gsize Γ
Proof
  Induct_on `Γ` >> simp[] >> Cases_on `h` >> rw[] >>
  fs[pairTheory.PAIR_MAP, pairTheory.PAIR_FST_SND_EQ, pairTheory.PAIR]
  >- (first_x_assum (qspec_then `Σ` assume_tac) >>
      `disjsplit Γ = SOME (FST z,SND z)` by fs[] >>
      drule disjsplit_size >> simp[arithmeticTheory.MAX_DEF])
  >- (Cases_on `0 < modal_size f0` >> simp[] >>
      fs[arithmeticTheory.NOT_LESS, arithmeticTheory.MAX_DEF])
  >> first_x_assum (qspec_then `Σ` assume_tac) >>
  `disjsplit Γ = SOME (FST z,SND z)` by fs[] >>
  drule disjsplit_size >> simp[arithmeticTheory.MAX_DEF]
QED

Theorem KT_K_degree:
  ∀a Γ Σ. MEM a (MAP (λd. d :: unbox Σ) (undia Γ)) ⇒
          degree([],a) < degree(Σ, Γ)
Proof
  Induct_on ‘Γ’ >> simp[undia_def, unbox_def] >> Cases >>
  simp[undia_def, unbox_def] >> rw[]
  >- (Induct_on `Σ` >> rw[unbox_def] >> Cases_on`h` >> simp[])
  >> Cases_on`a` >> simp[]
QED

Definition tableau_KT_def:
  tableau_KT Σ Γ =
    case contradiction Γ of
      SOME i => NONE
    | NONE =>
        case conjsplit Γ of
          SOME Γ' => tableau_KT Σ Γ'
        | NONE => case disjsplit Γ of
                    SOME (Γ1, Γ2) =>
                      (case tableau_KT Σ Γ1 of
                         SOME m => SOME m
                       | NONE =>
                           case tableau_KT Σ Γ2 of
                           | SOME m => SOME m
                           | NONE => NONE)
                  | NONE => if EXISTS is_box Γ then
                              tableau_KT (FST (trule Σ Γ)) (SND (trule Σ Γ))
                            else  if EXISTS is_dia Γ then
                              let
                                children = scmap2 tableau_KT []
                                                  (MAP (λd. d :: (unbox Σ))
                                                   (undia Γ))
                              in
                                case children of
                                  SOME ms => SOME (Nd (unvar Γ) ms)
                                | NONE => NONE
                            else SOME (Nd (unvar Γ) [])
Termination
  WF_REL_TAC ‘inv_image ((<) LEX (<))
              (λ(Σ,Γ). (degree (Σ,Γ), SUM $ MAP form_size Γ))’
  >> rw[]
  >- rw[KT_K_degree]
  >- rw[conjsplit_degree]
  >- rw[disjsplit_degree_p2]
  >- rw[disjsplit_degree_p1]
  >> metis_tac[trule_length]
End

(*
Definition tableau_KT_root_def:
  tableau_KT_root Γ = tableau_KT [] Γ
End
*)

val f1 = ``Disj (NVar 0) (Dia (Var 0))``
val KT_test_1 = EVAL ``tableau_KT [] [^f1]``
val f2 = ``Conj (NVar 0) (Dia (Var 0))``
val KT_test_2 = EVAL ``tableau_KT [] [^f2]``
val f3 = ``Conj (Var 1) (Box (NVar 1))``
val KT_test_3 = EVAL ``tableau_KT [] [^f3]``
val test = EVAL``tableau_KT [Box (Var 2); Box (NVar 2)] [Var 1]``;

Theorem mem_snd_trule:
 ∀Σ Γ. MEM f (SND (trule Σ Γ)) ⇒ MEM f Γ ∨ MEM (Box f) Γ
Proof
  ho_match_mp_tac trule_ind >> rw[] >> fs[]
QED

Theorem mem_fst_trule:
 ∀Σ Γ. MEM f (FST (trule Σ Γ)) ⇒ MEM f Σ ∨ MEM f Γ
Proof
  ho_match_mp_tac trule_ind >> rw[] >> fs[]
QED

Definition dia_decos_def:
  dia_decos (Dia d) = d ∧
  dia_decos p = p
End

Theorem dia_decos_dia[simp]:
 ∀p. is_dia p ⇒ Dia (dia_decos p) = p
Proof
 rw[] >> Cases_on `p` >> fs[is_dia_def] >>
 metis_tac[dia_decos_def]
QED

Theorem exist_dia[simp]:
 ∀Γ. EXISTS is_dia Γ ⇒ ∃f. MEM f Γ ∧ is_dia f
Proof
  rw[] >> Induct_on `Γ` >> rw[]
  >- (qexists_tac `h` >> rw[])
  >> fs[] >> qexists_tac`f` >> rw[]
QED

Theorem tableau_KT_complete:
  ∀Σ Γ. tableau_KT Σ Γ = NONE ⇒
        ∀M w. w ∈ M.frame.world ∧ reflexive_M M ⇒
              ∃f. MEM f (Γ++Σ) ∧ ¬forces M w f
Proof
  ho_match_mp_tac tableau_KT_ind >> ntac 2 gen_tac >> strip_tac >>
  simp[Once tableau_KT_def] >> simp[AllCaseEqs()] >> rw[] >>
  fs[MEM_MAP, PULL_EXISTS, MEM_undia, MEM_unbox]
  >- ((* T rule *)
      rw[] >> `∃f.
                (MEM f (SND (trule Σ Γ)) ∨ MEM f (FST (trule Σ Γ))) ∧
                ¬forces M w f` by fs[] >> simp[]
      >- (drule mem_snd_trule >> rw[]
          >- metis_tac[]
          >> qexists_tac `Box f` >> fs[reflexive_M] >> metis_tac[])
      >> drule mem_fst_trule >> rw[]
      >- metis_tac[]
      >> qexists_tac `f` >> rw[])
  >- ((* K rule *)
      rw[] >> first_x_assum (drule_then (drule_then strip_assume_tac)) >>
      reverse (Cases_on ‘forces M w (Dia d)’)
      >- metis_tac[]
      >> fs[] >> `∃f. MEM (Box f) Σ ∧ ¬forces M v f` by metis_tac[] >>
       qexists_tac ‘Box f’ >> simp[] >> metis_tac[])
  >- (rpt (first_x_assum (drule_then strip_assume_tac))
      >- (drule_all disjsplit_MEM2 >> metis_tac[forces_def])
      >> metis_tac[])
  >- (first_x_assum (drule_then (drule_then strip_assume_tac))
      >- (drule_all conjsplit_MEM2 >> metis_tac[forces_def])
      >> metis_tac[])
  >> (rename [‘contradiction Γ = SOME j’] >>
      drule_then strip_assume_tac contradiction_EQ_SOME >>
      Cases_on ‘w ∈ M.valt j’
      >- (qexists_tac ‘NVar j’ >> simp[]) >>
      qexists_tac ‘Var j’ >> simp[])
QED

Definition T_tree_model_def:
  T_tree_model t =
    <| frame := <| rel := RC tree_rel ; world := { t' | RTC tree_rel t t' } |>;
       valt := λv t. case t of Nd vs _ => MEM v vs ;

    |>
End

Theorem T_tree_model_thm[simp]:
  ((T_tree_model t).valt = λv u. case u of Nd vs _ => MEM v vs) ∧
  (T_tree_model t).frame.rel = RC tree_rel ∧
  m ∈ (T_tree_model m).frame.world
Proof
  simp[T_tree_model_def]
QED

Theorem reflexive_T_tree_model:
  reflexive_M (T_tree_model t)
Proof
   simp[reflexive_M]
QED

Definition subtree_def:
  subtree t1 t2 ⇔ tree_rel^* t2 t1
End

Theorem FINITE_T_tree_model_worlds[simp]:
  ∀t. FINITE (T_tree_model t).frame.world
Proof
  simp[T_tree_model_def] >> Induct >> simp[tree_rel_def] >>
  simp[Once relationTheory.RTC_CASES1] >> simp[GSPEC_OR, tree_rel_def] >>
  qmatch_abbrev_tac ‘FINITE s’ >>
  ‘s = BIGUNION (IMAGE (λt. { u | RTC tree_rel t u }) (set ts))’
    by (simp[Abbr‘s’, Once EXTENSION, PULL_EXISTS] >> metis_tac[]) >>
  simp[PULL_EXISTS]
QED

Theorem scmap2_MAP:
  scmap2 f l1 (MAP g l2) = scmap2 (λx y. f x (g y)) l1 l2
Proof
  Induct_on `l2` >> rw[]
QED

Definition reflexive_sequent_def:
  reflexive_sequent (Σ,Γ) ⇔
    ∀𝜑 v l. MEM (Box 𝜑) Σ ⇒
            (∀f. MEM f Γ ⇒
                 forces (T_tree_model (Nd v l)) (Nd v l) f) ∧
            (∀s. MEM s l ⇒
                 (∀𝜓. MEM (Box 𝜓) Σ ⇒ forces (T_tree_model s) s 𝜓))
            ⇒
            forces (T_tree_model (Nd v l)) (Nd v l) 𝜑
End

Theorem reflexive_sequent_trule1:
  reflexive_sequent (Σ, Box f::Γ) ⇒ reflexive_sequent (Box f::Σ, f::Γ)
Proof
  dsimp[reflexive_sequent_def, DISJ_IMP_THM, FORALL_AND_THM, RC_DEF,
        tree_rel_def] >> rw[] >>
  last_x_assum irule >> rw[] >>
  irule forces_grows_backward >>
  rename [‘forces _ wld f’, ‘MEM wld l’] >>
  qexists_tac ‘T_tree_model wld’ >> simp[] >>
  dsimp[T_tree_model_def, SUBSET_DEF, RC_DEF] >>
  conj_tac >- metis_tac[RTC_RULES_RIGHT1] >>
  rw[] >> irule (RTC_RULES |> SPEC_ALL |> CONJUNCT2) >> simp[tree_rel_def] >>
  metis_tac[]
QED

Theorem reflexive_small_Gamma:
  reflexive_sequent (Σ, Γ) ⇒ reflexive_sequent (Σ, f::Γ)
Proof
  rw[reflexive_sequent_def, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem exists_split_first:
  EXISTS P lst ⇒ ∃p s e. lst = p ++ [e] ++ s ∧ P e ∧ EVERY ($¬ o P) p
Proof
  Induct_on `lst` >> simp[] >> rw[]
  >- (qexistsl_tac [`[]`, `lst`, `h`] >> simp[])
  >> fs[] >> Cases_on `P h` >> simp[]
  >- (qexistsl_tac [`[]`, `lst`, `h`] >> simp[])
  >> qexistsl_tac [`h::p`, `s`, `e`] >> simp[]
QED

Theorem reflexive_sequent_trule:
∀Σ Γ. reflexive_sequent (Σ,Γ) ⇒ reflexive_sequent (trule Σ Γ)
Proof
  rw[] >> Cases_on `EVERY ($¬ ∘ is_box) Γ` >> simp[] >>
  `EXISTS is_box Γ` by metis_tac[EXISTS_NOT_EVERY] >>
  `∃p f s. Γ = (p ++ [Box f] ++ s) ∧ EVERY ($¬ ∘ is_box) p`
    by (drule exists_split_first >> rw[] >>
        qexistsl_tac [`p`,`unbox_single e`, `s`] >> rw[] >>
        Cases_on`e` >> fs[]) >>
  rw[trule_result] >>
  dsimp[reflexive_sequent_def, DISJ_IMP_THM, FORALL_AND_THM, RC_DEF,
     tree_rel_def] >> rw[] >>
  fs[reflexive_sequent_def, DISJ_IMP_THM, FORALL_AND_THM, RC_DEF,
     tree_rel_def] >> rw[] >>
  last_x_assum irule >> rw[] >> simp[] >>
  irule forces_grows_backward >>
  rename [‘forces _ wld f’, ‘MEM wld l’] >>
  qexists_tac ‘T_tree_model wld’ >> simp[] >>
  dsimp[T_tree_model_def, SUBSET_DEF, RC_DEF] >>
  conj_tac >- metis_tac[RTC_RULES_RIGHT1] >>
  rw[] >> irule (RTC_RULES |> SPEC_ALL |> CONJUNCT2) >> simp[tree_rel_def] >>
  metis_tac[]
QED

Theorem forces_single_step_back:
  forces (T_tree_model w) w f ∧ MEM w ws
⇒
  forces (T_tree_model (Nd root ws)) w f
Proof
  rw[] >> irule forces_grows_backward >> qexists_tac `T_tree_model w` >> rw[]
  >- (fs[T_tree_model_def, tree_rel_def, RC_DEF]
      >- metis_tac[]
      >> rw[] >> metis_tac[RTC_RULES_RIGHT1, tree_rel_def])
  >> rw[T_tree_model_def, SUBSET_DEF] >> metis_tac[tree_rel_def, RTC_RULES]
QED

Theorem forces_every_literal:
  contradiction Γ = NONE ∧
  conjsplit Γ = NONE ∧
  disjsplit Γ = NONE ∧
  EVERY ($¬ ∘ is_box) Γ ∧
  EVERY ($¬ ∘ is_dia) Γ
⇒
  ∀f. MEM f Γ ⇒ forces (T_tree_model  (Nd (unvar Γ) []))  (Nd (unvar Γ) []) f
Proof
  rw[] >>
  fs[EVERY_MEM, conjsplit_EQ_NONE, disjsplit_EQ_NONE, contradiction_EQ_NONE] >>
  first_x_assum (drule_then assume_tac) >>
  first_x_assum (drule_then assume_tac) >>
  Cases_on ‘f’ >> fs[] >>
  metis_tac[]
QED

Theorem reflexive_sequent_disj_right:
  contradiction Γ = NONE ∧
  conjsplit Γ = NONE ∧
  disjsplit Γ = SOME (Γ1,Γ2) ∧
  tableau_KT Σ Γ1 = NONE ∧
  tableau_KT Σ Γ2 = SOME t ∧
  reflexive_sequent (Σ,Γ)
⇒
  reflexive_sequent (Σ,Γ2)
Proof
  rw[reflexive_sequent_def] >> first_x_assum (drule_then strip_assume_tac) >>
  `∀f. MEM f Γ ⇒ forces (T_tree_model (Nd v l)) (Nd v l) f`
    by (rw[] >> drule_then assume_tac MEM_disjsplit >>
        first_x_assum (drule_then strip_assume_tac)
        >- (first_x_assum (drule_then assume_tac) >> rw[forces_def])
        >> first_x_assum (drule_then assume_tac) >> rw[]) >>
  fs[]
QED

Theorem reflexive_sequent_disj_left:
  contradiction Γ = NONE ∧
  conjsplit Γ = NONE ∧
  disjsplit Γ = SOME (Γ1,Γ2) ∧
  tableau_KT Σ Γ1 = SOME t ∧
  reflexive_sequent (Σ,Γ)
⇒
  reflexive_sequent (Σ,Γ1)
Proof
  rw[reflexive_sequent_def] >> first_x_assum (drule_then strip_assume_tac) >>
  `∀f. MEM f Γ ⇒ forces (T_tree_model (Nd v l)) (Nd v l) f`
    by (rw[] >> drule_then assume_tac MEM_disjsplit >>
        first_x_assum (drule_then strip_assume_tac)
        >- (first_x_assum (drule_then assume_tac) >> rw[forces_def])
        >> first_x_assum (drule_then assume_tac) >> rw[]) >>
  fs[]
QED

Theorem reflexive_sequent_conj:
  contradiction Γ = NONE ∧
  conjsplit Γ = SOME Γ' ∧
  tableau_KT Σ Γ' = SOME t ∧
  reflexive_sequent (Σ,Γ)
⇒
  reflexive_sequent (Σ,Γ')
Proof
  rw[reflexive_sequent_def] >> first_x_assum (drule_then strip_assume_tac) >>
  `∀f. MEM f Γ ⇒ forces (T_tree_model (Nd v l)) (Nd v l) f`
    by (rw[] >> drule_then assume_tac MEM_conjsplit >>
        first_x_assum (drule_then strip_assume_tac)
        >- (first_assum (drule_then assume_tac) >>
            first_assum (drule_then assume_tac) >> rw[forces_def])
        >> first_x_assum (drule_then assume_tac) >> rw[]) >>
  fs[]
QED

(* TODO: wrap it: for all Σ Γ, if tableau_KT Σ Γ closes, then there must exist
   a tree model ... *)
Theorem tableau_KT_sound:
   ∀Σ Γ t. tableau_KT Σ Γ = SOME t ⇒
            (∀f. MEM f Σ ⇒ is_box f) ⇒
            reflexive_sequent (Σ,Γ) ⇒
           ∀f. MEM f (Σ++Γ) ⇒
           forces (T_tree_model t) t f
Proof
  ho_match_mp_tac tableau_KT_ind >> qx_genl_tac [‘Σ’, ‘Γ’] >> strip_tac >>
  qx_gen_tac `t` >> simp[Once tableau_KT_def] >>
  simp[AllCaseEqs()] >> strip_tac
(* T rule *)
  >- (fs[] >> strip_tac >> strip_tac >> drule_then assume_tac trule_all_box >>
      `∀f. MEM f (FST (trule Σ Γ)) ⇒ is_box f` by metis_tac[] >>
      first_x_assum (drule_then assume_tac) >> (* strip didn't do anything *)
      simp[DISJ_IMP_THM, FORALL_AND_THM] >>
      rw[]
      >- (drule_then assume_tac trule_mem_left >>
          drule_then assume_tac reflexive_sequent_trule >>
          metis_tac[])
      >> drule_then assume_tac trule_mem_right_simp >>
         drule_then assume_tac reflexive_sequent_trule >>
         metis_tac[])
(* K rule *)
  >- (fs[MEM_MAP, PULL_EXISTS] >>
      qpat_x_assum `EXISTS _ _ ⇒ _` (fn _ => all_tac) >>
      (* removes assumption 1 *)
      fs[reflexive_sequent_def, DISJ_IMP_THM, FORALL_AND_THM, RC_DEF,
      tree_rel_def] >> rw[]
      (* MEM f history *)
      >- (first_assum (drule_then assume_tac) >> Cases_on `f` >> fs[] >>
          rw[] >> fs[RC_DEF]
          (* Current world *)
          >- (rw[] >> first_x_assum irule >> rw[]
             (* MEM f formulae (different f) *)
              >- (Cases_on `f` >> fs[] >> rw[]
                  >- (fs[contradiction_EQ_NONE] >> metis_tac[])
                  >- (fs[conjsplit_EQ_NONE] >> metis_tac[])
                  >- (fs[conjsplit_EQ_NONE] >> metis_tac[])
                  >- (fs[disjsplit_EQ_NONE] >> metis_tac[])
                  >- (fs[EVERY_MEM] >> last_x_assum drule >> rw[])
                  >> fs[MEM_undia] >> last_x_assum (drule_then assume_tac) >>
                  fs[scmap2_MAP] >> drule scmap2_MEM2 >> rw[] >>
                  fs[MEM_undia] >>
                  first_x_assum
                    (drule_then (qx_choose_then `w` strip_assume_tac)) >>
                  qexists_tac `w` >> rw[]
                  >- (rw[T_tree_model_def] >> irule RTC_SINGLE >>
                      simp[tree_rel_def])
                  >- (rw[RC_DEF, tree_rel_def])
                  >> first_x_assum (drule_then strip_assume_tac) >>
                  metis_tac[forces_single_step_back])
              (* MEM (Box psi) History *)
              >> fs[scmap2_MAP] >> drule scmap2_MEM >> rw[] >> fs[MEM_undia] >>
                 first_x_assum (drule_then strip_assume_tac) >>
                 last_x_assum (drule_then strip_assume_tac) >>
                 first_x_assum (drule_then strip_assume_tac) >>
                 fs[MEM_unbox]
              )
          (* Next world *)
          >> fs[tree_rel_def] >> fs[scmap2_MAP] >> drule scmap2_MEM >> rw[] >>
          fs[MEM_undia] >> first_x_assum (drule_then strip_assume_tac) >>
          last_x_assum (drule_then strip_assume_tac) >>
          first_x_assum (drule_then strip_assume_tac) >>
          fs[MEM_unbox] >> first_x_assum (drule_then assume_tac) >>
          metis_tac[forces_single_step_back])
      (* MEM f formulae*)
      >> Cases_on `f` >> fs[]
      >- (fs[contradiction_EQ_NONE] >> metis_tac[])
      >- (fs[conjsplit_EQ_NONE] >> metis_tac[])
      >- (fs[disjsplit_EQ_NONE] >> metis_tac[])
      >- (fs[EVERY_MEM] >> last_x_assum drule >> rw[])
      >> fs[MEM_undia] >> last_x_assum (drule_then assume_tac) >>
      fs[scmap2_MAP] >> drule scmap2_MEM2 >> rw[] >> fs[MEM_undia] >>
      first_x_assum (drule_then (qx_choose_then `w` strip_assume_tac)) >>
      qexists_tac `w` >> rw[]
      >- (rw[T_tree_model_def] >> irule RTC_SINGLE >> simp[tree_rel_def])
      >- (rw[RC_DEF, tree_rel_def])
      >> first_x_assum (drule_then strip_assume_tac) >>
      metis_tac[forces_single_step_back])
(* All Literals *)
  >- (rw[]
      >- (fs[reflexive_sequent_def, DISJ_IMP_THM, FORALL_AND_THM, RC_DEF,
            tree_rel_def] >> rw[] >>
          first_x_assum (drule_then strip_assume_tac) >> Cases_on `f` >>
          fs[] >> first_x_assum (drule_then strip_assume_tac) >>
          rw[] >> fs[tree_rel_def, RC_DEF] >> drule forces_every_literal >>
          rw[])
      >> drule forces_every_literal >> rw[])
(* Disj right *)
  >- (qpat_x_assum `∀Σ' Γ'.
       _ ∧ _ ∧ _ ∧ ¬EXISTS is_box Γ ∧ EXISTS is_dia Γ ∧ _
        ==> _ ` (fn _ => all_tac) >>
      qpat_x_assum `∀Γ'.
        _ ∧ conjsplit Γ = SOME Γ' ==> _ ` (fn _ => all_tac) >>
      qpat_x_assum `∀Σ' Γ' Γ2. _ ` (fn _ => all_tac) >> rw[]
      >- (last_x_assum (drule_then strip_assume_tac) >>
          rfs[] >> drule_then strip_assume_tac reflexive_sequent_disj_right >>
          rfs[])
      >>  last_x_assum (drule_then strip_assume_tac) >>
          rfs[] >> drule_then strip_assume_tac reflexive_sequent_disj_right >>
          rfs[] >>  first_x_assum (drule_then strip_assume_tac) >>
          first_x_assum (drule_then strip_assume_tac) >>
          first_x_assum (drule_then strip_assume_tac) >>
          drule_then assume_tac MEM_disjsplit >>
          first_x_assum (drule_then strip_assume_tac)
          >- (first_x_assum (drule_then strip_assume_tac) >>
              fs[DISJ_IMP_THM])
          >> fs[DISJ_IMP_THM, FORALL_AND_THM])
(* Disj left *)
  >- (qpat_x_assum `∀Σ' Γ'.
       _ ∧ _ ∧ _ ∧ ¬EXISTS is_box Γ ∧ EXISTS is_dia Γ ∧ _
         ==> _ ` (fn _ => all_tac) >>
      qpat_x_assum `∀Γ'.
        _ ∧ conjsplit Γ = SOME Γ' ==> _ ` (fn _ => all_tac) >>
      qpat_x_assum `∀Σ' Γ1 Γ'. _ ∧ _ ∧ disjsplit Γ = SOME Σ' ∧
        Σ' = (Γ1,Γ') ∧ tableau_KT Σ Γ1 = NONE ⇒ _ ` (fn _ => all_tac) >>
      rw[]
      >- (last_x_assum (drule_then strip_assume_tac) >>
          rfs[] >> drule_then strip_assume_tac reflexive_sequent_disj_left >>
          rfs[])
      >>  last_x_assum (drule_then strip_assume_tac) >>
          rfs[] >> drule_then strip_assume_tac reflexive_sequent_disj_left >>
          rfs[] >>  first_x_assum (drule_then strip_assume_tac) >>
          first_x_assum (drule_then strip_assume_tac) >>
          first_x_assum (drule_then strip_assume_tac) >>
          drule_then assume_tac MEM_disjsplit >>
          first_x_assum (drule_then strip_assume_tac)
          >- (first_x_assum (drule_then strip_assume_tac) >>
              fs[DISJ_IMP_THM])
          >> fs[DISJ_IMP_THM, FORALL_AND_THM])
(* Conj *)
  >> qpat_x_assum `∀Σ' Γ'.
       _ ∧ _ ∧ _ ∧ ¬EXISTS is_box Γ ∧ EXISTS is_dia Γ ∧ _
         ==> _ ` (fn _ => all_tac) >>
  qpat_x_assum `∀Σ' Γ1 Γ'. _ ∧ _ ∧ disjsplit Γ = SOME Σ' ∧
    Σ' = (Γ1,Γ') ∧ tableau_KT Σ Γ1 = NONE ⇒ _ ` (fn _ => all_tac) >>
  qpat_x_assum `∀Σ' Γ' Γ2. _ ` (fn _ => all_tac) >> rw[]
  >- (last_x_assum (drule_then strip_assume_tac) >> rfs[] >>
      drule_then strip_assume_tac reflexive_sequent_conj >> rfs[])
  >> last_x_assum (drule_then strip_assume_tac) >> rfs[] >>
  drule_then strip_assume_tac reflexive_sequent_conj >> rfs[] >>
  first_x_assum (drule_then strip_assume_tac) >>
  first_x_assum (drule_then strip_assume_tac) >>
  drule_then assume_tac MEM_conjsplit >>
  first_x_assum (drule_then strip_assume_tac)
  >- (first_x_assum (drule_then strip_assume_tac) >> fs[DISJ_IMP_THM])
  >> fs[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem tableau_KT_satisfies =
        tableau_KT_sound |> Q.SPEC ‘[]’
                         |> SRULE [reflexive_sequent_def]

val _ = export_theory();
