open HolKernel Parse boolLib bossLib;

open relationTheory pairTheory combinTheory pred_setTheory
open cardinalTheory

open ordinalTheory

val _ = new_theory "bnfAlgebra";

Overload "𝟙"[local] = “{()}”
Overload "𝟚"[local] = “{T;F}”
Overload "≉"[local] = “λa b. ¬(a ≈ b)”

val _ = set_fixity "≉" (Infix(NONASSOC, 450))
fun SRULE ths = SIMP_RULE (srw_ss()) ths

val _ = new_type ("F", 2)
val _ = new_constant ("mapF", “:(α -> β) -> (γ -> δ) -> (α,γ)F -> (β,δ)F”);
val _ = new_constant ("setAF", “:(α,β) F -> α set”)
val _ = new_constant ("setBF", “:(α,β) F -> β set”)

val mapID = new_axiom ("mapID", “∀a. mapF (λx.x) (λy.y) a = a”);
val mapO = new_axiom ("mapO",
                      “∀a f1 f2 g1 g2.
                         mapF f1 g1 (mapF f2 g2 a) =
                         mapF (f1 o f2) (g1 o g2) a”);

val setA_map = new_axiom("setA_map",
                         “∀a f g. setAF (mapF f g a) = IMAGE f (setAF a)”)
val setB_map = new_axiom("setB_map",
                         “∀a f g. setBF (mapF f g a) = IMAGE g (setBF a)”)

val map_CONG = new_axiom("map_CONG",
                         “(∀a. a ∈ setAF A ⇒ f1 a = f2 a) ∧
                          (∀b. b ∈ setBF A ⇒ g1 b = g2 b) ⇒
                          mapF f1 g1 A = mapF f2 g2 A”);

Definition relF_def:
  relF R1 R2 x y ⇔ ∃z. setAF z ⊆ UNCURRY R1 ∧ setBF z ⊆ UNCURRY R2 ∧
                       mapF FST FST z = x ∧ mapF SND SND z = y
End

val relO = new_axiom ("relO",
                      “relF R1 R2 O relF S1 S2 ⊆ᵣ relF (R1 O S1) (R2 O S2)”);

val _ = new_type ("bndop", 1)
val _ = new_constant ("bnd", “:β bndop ordinal”)
val bnd = new_axiom ("bnd",
  “∀v : (β,α)F. setBF v ≼ preds (bnd : β bndop ordinal) ∧ ω ≤ bnd”);


Theorem IN_UNCURRY[simp]:
  (x,y) ∈ UNCURRY R ⇔ R x y
Proof
  simp[IN_DEF]
QED

Theorem relO_EQ:
  relF R1 R2 O relF S1 S2 = relF (R1 O S1) (R2 O S2)
Proof
  irule RSUBSET_ANTISYM >> simp[relO] >>
  simp[relF_def, FUN_EQ_THM, RSUBSET, O_DEF, SUBSET_DEF, FORALL_PROD] >>
  rw[PULL_EXISTS] >> fs[GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] >>
  qexistsl_tac [‘mapF (λ(a,b). (a, f a b)) (λ(c,d). (c, f' c d)) z’,
                ‘mapF (λ(a,b). (f a b, b)) (λ(c,d). (f' c d, d)) z’] >>
  simp[mapO, o_UNCURRY_R, o_ABS_R, setA_map, setB_map, EXISTS_PROD,
       PULL_EXISTS, FORALL_PROD] >> conj_tac >>
  irule map_CONG >> simp[FORALL_PROD]
QED

Definition Fin_def:
  Fin As Bs = { a : (α,β) F | setAF a ⊆ As ∧ setBF a ⊆ Bs }
End

Definition alg_def:
  alg (A : α set, s : (β,α) F -> α) ⇔ ∀x. x ∈ Fin UNIV A ⇒ s x ∈ A
End

Definition minset_def:
  minset (s : (β,α)F -> α) = BIGINTER { B | alg(B,s) }
End

Theorem minset_is_alg[simp]:
  alg (minset s, s)

Proof
  simp[minset_def, alg_def, Fin_def, SUBSET_BIGINTER]
QED

Theorem IN_minset:
  x IN minset s ⇔ ∀A. alg(A,s) ⇒ x IN A
Proof
  simp[minset_def]
QED

Theorem minsub_surj:
  SURJ s (Fin UNIV (minset s)) (minset s)
Proof
  ‘alg (minset s, s)’ by simp[] >>
  simp[SURJ_DEF] >> conj_tac
  >- gs[alg_def, Fin_def, SUBSET_BIGINTER, Excl "minset_is_alg"] >>
  simp[Fin_def] >> qx_gen_tac ‘tgt’ >> strip_tac >> CCONTR_TAC >>
  gvs[SUBSET_DEF, IN_minset] >>
  ‘alg (minset s DELETE tgt, s)’ suffices_by
    (strip_tac >> first_x_assum drule >> simp[]) >>
  simp[alg_def, Fin_def, SUBSET_DEF] >> qx_gen_tac ‘src’ >>
  rpt strip_tac
  >- (irule (iffLR alg_def) >> simp[Fin_def, SUBSET_DEF]) >>
  first_x_assum drule >> simp[] >> qx_gen_tac ‘srcA’ >>
  Cases_on ‘srcA ∈ setBF src’ >> simp[] >>
  qx_gen_tac ‘A’ >> Cases_on ‘alg(A,s)’ >> simp[] >>
  ‘srcA ∈ minset s’ by simp[] >> pop_assum mp_tac >>
  metis_tac[IN_minset]
QED

Definition hom_def:
  hom h (A,s) (B,t) ⇔
    alg(A,s) ∧ alg(B,t) ∧ (∀a. a IN A ⇒ h a IN B) ∧
    ∀af. af ∈ Fin UNIV A ⇒ t (mapF I h af) = h (s af)
End

Theorem homs_on_same_domain:
  hom h (A,s) (B,t) ∧ (∀a. a ∈ A ⇒ h' a = h a) ⇒ hom h' (A,s) (B,t)
Proof
  simp[hom_def, Fin_def] >> rw[] >>
  rename [‘setBF af ⊆ A’] >>
  ‘s af ∈ A’ by gs[alg_def, Fin_def] >> simp[] >>
  ‘mapF I h' af = mapF I h af’ suffices_by simp[] >>
  irule map_CONG >> simp[] >> metis_tac[SUBSET_DEF]
QED

Definition weakly_initial_def:
  weakly_initial (A,s : (β,α) F -> α) (:γ) ⇔
    alg(A,s) ∧
    ∀(C:γ set) t. alg(C,t : (β,γ) F -> γ) ⇒ ∃h. hom h (A,s) (C,t)
End

Theorem minset_ind:
  ∀P. (∀x. setBF x ⊆ minset s ∧ (∀y. y ∈ setBF x ⇒ P y) ⇒ P (s x)) ⇒
      ∀x. x ∈ minset s ⇒ P x
Proof
  gen_tac >> strip_tac >>
  ‘minset s ⊆ P INTER minset s’ suffices_by simp[SUBSET_DEF, IN_DEF] >>
  simp[minset_def, SimpL “$SUBSET”] >> irule BIGINTER_SUBSET >>
  qexists_tac ‘P INTER minset s’ >>
  simp[alg_def, Fin_def, SUBSET_DEF] >> rw[]
  >- gs[IN_DEF, SUBSET_DEF] >>
  ntac 2 (last_x_assum (K ALL_TAC)) >>
  gs[alg_def, Fin_def, SUBSET_DEF, IN_minset]
QED

Theorem minsub_gives_unique_homs:
  hom h1 (minset s, s) (C,t) ∧ hom h2 (minset s,s) (C,t) ⇒
  ∀a. a ∈ minset s ⇒ h1 a = h2 a
Proof
  strip_tac >> ho_match_mp_tac minset_ind >> qx_gen_tac ‘af’ >> strip_tac >>
  gs[hom_def, Fin_def] >>
  ‘t (mapF I h1 af) = t (mapF I h2 af)’ suffices_by metis_tac[] >>
  ‘mapF I h1 af = mapF I h2 af’ suffices_by metis_tac[] >>
  irule map_CONG >> simp[]
QED

Definition subalg_def:
  subalg (A,s) (B,t) ⇔ alg(A,s) ∧ alg (B,t) ∧
                       (∀af. af ∈ Fin UNIV A ⇒ s af = t af) ∧ A ⊆ B
End

Theorem subalgs_preserve_homs:
  subalg A1 A2 ∧ hom f A2 C ⇒ hom f A1 C
Proof
  Cases_on ‘A1’ >> Cases_on ‘A2’ >> Cases_on ‘C’ >>
  simp[hom_def,Fin_def,subalg_def] >> metis_tac[SUBSET_DEF]
QED

Theorem minsub_subalg:
  alg(A,s) ⇒ subalg (minset s, s) (A,s)
Proof
  simp[subalg_def, minset_def] >> strip_tac >>
  irule BIGINTER_SUBSET >> simp[] >> metis_tac[SUBSET_REFL]
QED

Theorem minsub_I_subalg:
  alg(A,s) ⇒ hom I (minset s, s) (A,s)
Proof
  strip_tac >> drule minsub_subalg >>
  simp[hom_def, Fin_def, mapID, I_EQ_IDABS, subalg_def, SUBSET_DEF]
QED

Type vec[local,pp] = “:'a -> 'b option”

Definition vecdom_def:
  vecdom v = { i | v i ≠ NONE}
End

Definition validvecF_def:
  validvecF (fv : (β,('i,'a) vec) F) ⇔
    ∃I. ∀v. v ∈ setBF fv ⇒ vecdom v = I
End

Definition vecFdom_def:
  vecFdom (fv : (β,(ι,α)vec)F) = some I. ∀v. v ∈ setBF fv ⇒ vecdom v = I
End

Theorem validvecF_vecFdom:
  validvecF fv ⇔ ∃I. vecFdom fv = SOME I
Proof
  simp[validvecF_def, vecFdom_def] >> DEEP_INTRO_TAC optionTheory.some_intro >>
  simp[vecdom_def, EQ_IMP_THM, PULL_EXISTS, FORALL_AND_THM] >> rw[] >>
  metis_tac[]
QED

Definition liftvec_def:
  liftvec D (fv : (β,('i,α)vec) F) : ('i,(β,α)F) vec =
  λi. if i ∈ D then SOME (mapF I (λv. THE (v i)) fv)
      else NONE
End

Theorem liftvec_preserves_dom:
  vecdom (liftvec Is fv) = Is
Proof
  simp[liftvec_def, vecdom_def] >> rw[]
QED

Type alg[local,pp] = “:α set # ((β,α)F -> α)”

Definition bigprod_def:
  bigprod (As : (α,β)alg set) : (((α,β)alg,α)vec,β)alg =
  (BIGPRODi (λa. if a IN As then SOME (FST a) else NONE),
   λfv a. if a IN As then SOME (SND a (THE (liftvec As fv a)))
          else NONE)
End

Theorem bigprod_preserves_alg:
  (∀a. a ∈ As ⇒ alg a) ⇒ alg (bigprod As)
Proof
  simp[bigprod_def, alg_def, FORALL_PROD, Fin_def] >>
  disch_then (assume_tac o CONV_RULE (RENAME_VARS_CONV ["A", "f"])) >>
  simp[BIGPRODi_def, FORALL_PROD, liftvec_def, SUBSET_DEF] >>
  rpt gen_tac >> strip_tac >>
  qx_genl_tac [‘B’, ‘g’] >> strip_tac >>
  first_x_assum irule >> simp[] >> simp[setB_map] >>
  simp[SUBSET_DEF, PULL_EXISTS] >> rpt strip_tac >>
  first_x_assum $ drule_then strip_assume_tac >> first_x_assum drule >>
  simp[PULL_EXISTS]
QED

Theorem bigprod_proj:
  (∀A f. (A,f) ∈ As ⇒ alg (A,f)) ⇒
  ∀A f. (A,f) ∈ As ⇒ hom (λv. THE (v (A,f))) (bigprod As) (A,f)
Proof
  rpt strip_tac >> simp[hom_def, bigprod_def] >> conj_tac
  >- (simp[GSYM bigprod_def] >> simp[bigprod_preserves_alg, FORALL_PROD]) >>
  simp[Fin_def, liftvec_def] >> simp[BIGPRODi_def] >> rpt strip_tac >>
  first_assum drule >> simp[PULL_EXISTS]
QED

Theorem minbigprod_has_unique_homs:
  let s = SND (bigprod { a : (α,β) alg | alg a})
  in
    ∀A f. alg ((A, f) : (α,β) alg) ⇒
          ∃!h. (∀d. d ∉ minset s ⇒ h d = ARB) ∧ hom h (minset s, s) (A, f)
Proof
  Cases_on ‘bigprod {a : (α,β) alg| alg a}’ >> simp[] >> rpt strip_tac >>
  ‘alg (bigprod {a | alg a})’ by simp[bigprod_preserves_alg] >>
  rename [‘bigprod _ = (AA,FF)’] >> gs[] >>
  ‘alg (minset FF, FF)’ by simp[] >>
  ‘∃h0. hom h0 (bigprod {a : (α,β) alg | alg a}) (A,f)’
    by (irule_at (Pos hd) bigprod_proj >> simp[]) >>
  ‘subalg (minset FF, FF) (bigprod { a | alg a})’
    by metis_tac[minsub_subalg] >>
  ‘hom h0 (minset FF, FF) (A,f)’ by metis_tac[subalgs_preserve_homs] >>
  simp[EXISTS_UNIQUE_ALT] >>
  qexists_tac ‘λa. if a ∈ minset FF then h0 a else ARB’ >>
  simp[EQ_IMP_THM, FORALL_AND_THM] >> reverse conj_tac
  >- (irule homs_on_same_domain >> first_assum $ irule_at Any >>
      simp[]) >>
  qx_gen_tac ‘h1’ >> strip_tac >> csimp[FUN_EQ_THM, AllCaseEqs()] >>
  metis_tac[minsub_gives_unique_homs]
QED

(* there are unique homs out of the minimised product of all α-algebras into
   α-algebras, but we have to find an α that is big enough that algebras over
   other types can be injected into them.

*)

(* Traytel's K function, from MSc thesis, p 15 *)

val KK_def = new_specification(
  "KK", ["KK"],
  ord_RECURSION |> Q.ISPEC ‘∅ : γ set’
                |> Q.SPEC ‘λx r. r ∪ { s(x) | setBF x ⊆ r }’
                |> Q.SPEC ‘λx rs. BIGUNION rs’
                |> SRULE[]
                |> Q.GEN ‘s’ |> CONV_RULE SKOLEM_CONV);

Theorem KK_mono:
  ∀β α. α < β ⇒ KK s α ⊆ KK s β
Proof
  ho_match_mp_tac simple_ord_induction >>
  simp[KK_def, ordlt_SUC_DISCRETE, DISJ_IMP_THM, FORALL_AND_THM] >>
  rw[] >- metis_tac[IN_UNION, SUBSET_DEF] >>
  gs[omax_NONE] >>
  last_x_assum $ drule_then strip_assume_tac>>
  first_x_assum $ drule_all_then assume_tac >>
  irule SUBSET_BIGUNION_I >> simp[]
QED

Theorem KK_mono_LE:
  ∀α β. α ≤ β ⇒ KK s α ⊆ KK s β
Proof
  metis_tac[SUBSET_REFL, KK_mono, ordle_lteq]
QED

Theorem KK_SUB_min:
  ∀α. KK s α ⊆ minset s
Proof
  ho_match_mp_tac simple_ord_induction >> simp[KK_def] >> rw[]
  >- (simp[SUBSET_DEF, PULL_EXISTS] >> rpt strip_tac >>
      ‘alg (minset s, s)’ by simp[] >>
      gs[alg_def, Excl "minset_is_alg", Fin_def] >>
      metis_tac[SUBSET_DEF]) >>
  simp[SUBSET_DEF, PULL_EXISTS] >> metis_tac[SUBSET_DEF]
QED

Theorem KK_fixp_is_alg:
  { s x | x | setBF x ⊆ KK s ε } = KK s ε ⇒
  alg(KK s ε, s)
Proof
  rw[alg_def, Fin_def] >> gs[EXTENSION] >> metis_tac[]
QED


Theorem KK_sup:
  ords ≼ 𝕌(:num + 'a) ⇒
  KK s (sup ords : 'a ordinal) = BIGUNION (IMAGE (KK s) ords)
Proof
  strip_tac >> Cases_on ‘ords = ∅’ >> simp[KK_def] >>
  Cases_on ‘omax ords’
  >- (gs[omax_NONE] >>
      ‘islimit (sup ords)’
        by (simp[omax_NONE, sup_thm, PULL_EXISTS] >>
            metis_tac[ordlt_TRANS]) >>
      Cases_on ‘sup ords = 0’ >- gs[KK_def, sup_EQ_0] >>
      ‘0 < sup ords’ by metis_tac[IFF_ZERO_lt] >>
      simp[KK_def] >> irule SUBSET_ANTISYM >>
      simp[SUBSET_DEF, PULL_EXISTS, sup_thm] >> rw[] >> (* 2 *)
      metis_tac[SUBSET_DEF, KK_mono]) >>
  gs[omax_SOME] >> rename [‘_ ≤ mx’, ‘mx ∈ ords’] >>
  ‘sup ords = mx’ by metis_tac[sup_eq_max] >> simp[] >>
  irule SUBSET_ANTISYM >> simp[SUBSET_DEF, PULL_EXISTS] >> rw[] (* 2 *)
  >- metis_tac[] >>
  metis_tac[KK_mono_LE, SUBSET_DEF]
QED

Theorem KK_preds_subset:
  BIGUNION (IMAGE (KK s) (preds α)) ⊆ KK s α
Proof
  qid_spec_tac ‘α’ >> ho_match_mp_tac simple_ord_induction >>
  rw[] (* 2 *)
  >- (simp[KK_def, preds_ordSUC] >> irule SUBSET_TRANS >> goal_assum drule >>
      simp[]) >>
  simp[KK_def]
QED

Theorem KK_thm:
  KK s α = if α = 0 then ∅
           else BIGUNION (IMAGE (λa. { s fv | fv | setBF fv ⊆ KK s a})
                          (preds α))
Proof
  qid_spec_tac ‘α’ >> ho_match_mp_tac simple_ord_induction >>
  rw[] (* 4 *)
  >- simp[KK_def]
  >- (simp[preds_nat] >> ‘count 1 = {0}’ by simp[EXTENSION] >>
      simp[KK_def, GSYM ORD_ONE, Excl "ORD_ONE"])
  >- (qpat_x_assum ‘KK _ _ = BIGUNION _’ (assume_tac o SYM) >>
      simp[KK_def, preds_ordSUC, UNION_COMM]) >>
  pop_assum (assume_tac o GSYM) >>
  simp[KK_def] >> irule SUBSET_ANTISYM >> conj_tac >>
  simp[Once SUBSET_DEF, PULL_EXISTS]
  >- (rpt strip_tac >> rename [‘v ∈ KK s a’] >>
      ‘a ≠ 0’ by (strip_tac >> gs[KK_def]) >>
      ‘KK s a = BIGUNION (IMAGE (λa0. { s fv | fv | setBF fv ⊆ KK s a0})
                          (preds a))’ by metis_tac[] >>
      gs[PULL_EXISTS] >> metis_tac[ordlt_TRANS]) >>
  rpt strip_tac >> rename [‘a < α’, ‘setBF fv ⊆ KK s a’] >>
  qexists_tac ‘a⁺’ >> simp[KK_def] >> metis_tac[islimit_SUC_lt]
QED

Theorem SUBSET_BIGUNION_I2:
  B ⊆ A ∧ A ∈ As ⇒ B ⊆ BIGUNION As
Proof
  simp[SUBSET_DEF] >> metis_tac[]
QED

Theorem sucbnd_suffices:
  ω ≤ (bd : γ ordinal) ∧ (∀x : (α,β)F. setBF x ≼ preds bd) ⇒
  alg (KK (s:(α,β)F -> β) (csuc bd), s)
Proof
  strip_tac >>
  ‘INFINITE (preds bd)’ by (simp[FINITE_preds] >> rpt strip_tac >> gvs[]) >>
  irule KK_fixp_is_alg >> irule SUBSET_ANTISYM >> conj_tac >>
  ONCE_REWRITE_TAC [SUBSET_DEF] >> simp[PULL_EXISTS] >>
  rpt strip_tac
  >- (rename [‘s fv ∈ KK s _’] >>
      drule_then strip_assume_tac csuc_is_nonzero_limit >>
      simp[KK_def, PULL_EXISTS, lt_csuc] >>
      gs[SUBSET_DEF, KK_def, PULL_EXISTS, lt_csuc] >>
      gs[GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] >>
      rename [‘_ ∈ KK s (g _)’, ‘preds (g _) ≼ preds bd’] >>
      qabbrev_tac ‘B = sup (IMAGE g $ setBF fv)’ >>
      ‘IMAGE g $ setBF fv ≼ univ(:num + (γ + num -> bool))’
        by (irule IMAGE_cardleq_rwt >>
            first_assum (C (resolve_then (Pos hd) irule) cardleq_TRANS) >>
            resolve_then (Pos hd) irule preds_inj_univ cardleq_TRANS >>
            simp[cardleq_lteq, bumpUNIV_cardlt]) >>
      ‘∀a. a < B ⇔ ∃v. v ∈ setBF fv ∧ a < g v’
        by simp[Abbr‘B’, sup_thm, PULL_EXISTS] >>
      qexists_tac ‘B⁺’ >> simp[KK_def] >> reverse conj_tac
      >- (simp[preds_ordSUC, INFINITE_cardleq_INSERT] >>
          simp[Abbr‘B’, preds_sup, dclose_BIGUNION] >>
          irule CARD_BIGUNION >>
          simp[IMAGE_cardleq_rwt, PULL_EXISTS]) >>
      ‘KK s B = BIGUNION (IMAGE (KK s) (IMAGE g (setBF fv)))’
        by simp[KK_sup, Abbr‘B’] >> disj2_tac >>
      qexists_tac ‘fv’ >> simp[SUBSET_DEF, PULL_EXISTS] >> metis_tac[]) >>
  rename [‘v ∈ KK s (csuc bd)’] >>
  drule_then strip_assume_tac csuc_is_nonzero_limit >>
  gvs[KK_def] >>
  rename [‘v ∈ KK s a’, ‘a < csuc bd’] >>
  qpat_x_assum ‘v ∈ KK s a’ mp_tac >> simp[Once KK_thm] >> rw[] >>
  gs[] >> qexists_tac ‘fv’ >> simp[] >> irule SUBSET_BIGUNION_I2 >>
  simp[PULL_EXISTS] >> metis_tac[ordlt_TRANS]
QED

Theorem KKbnd_EQ_minset:
  ω ≤ (bd : γ ordinal) ∧ (∀x : (α,β)F. setBF x ≼ preds bd) ⇒
  KK (s : (α,β)F -> β) (csuc bd) = minset s
Proof
  strip_tac >> drule_all_then (qspec_then ‘s’ assume_tac) sucbnd_suffices >>
  irule SUBSET_ANTISYM >> simp[KK_SUB_min] >>
  drule minsub_I_subalg >> simp[hom_def, mapID, SUBSET_DEF]
QED

Theorem nontrivialBs:
  (∃x:(α,β)F. setBF x ≠ ∅) ⇒ ∀B. (B:β set) ≼ Fin 𝕌(:α) B
Proof
  rpt strip_tac >> simp[cardleq_def] >>
  qexists_tac ‘λb. mapF I (K b) x’ >> simp[INJ_IFF, Fin_def, setB_map] >>
  conj_tac >- simp[SUBSET_DEF, PULL_EXISTS] >>
  simp[EQ_IMP_THM] >> rw[] >>
  pop_assum (mp_tac o Q.AP_TERM ‘setBF’ ) >>
  simp[setB_map, EXTENSION] >> gs[GSYM MEMBER_NOT_EMPTY] >> metis_tac[]
QED

(* see Lemma 33 in ITP2014's
     "Cardinals in Isabelle/HOL" by Blanchette, Popescu and Traytel
 *)
Theorem CBDb:
  ω ≤ (bd : γ ordinal) ∧ (∀x:(α,β)F. setBF x ≼ preds bd) ∧
  (∃x:(α,γ ordinal)F. setBF x ≠ ∅)
⇒
  ∀B:β set. {T;F} ≼ B ⇒ Fin 𝕌(:α) B ≼ B ** preds(cardSUC (Fin 𝕌(:α) (preds bd)))
Proof
  rpt strip_tac >>
  qabbrev_tac ‘kA = Fin 𝕌(:α) (preds bd) CROSS (B ** preds bd)’ >>
  qmatch_abbrev_tac ‘_ ≼ B ** k’ >>
  ‘kA ≼ B ** k’
    by (simp[Abbr‘k’, Abbr‘kA’] >> irule CARD_MUL2_ABSORB_LE >>
        simp[] >> rpt strip_tac
        >- (drule_all cardleq_TRANS >> simp[cardleq_def, INJ_IFF] >>
            qexistsl_tac [‘T’, ‘F’] >> simp[])
        >- (disj2_tac >> simp[FINITE_preds, cardSUC_EQN] >>
            ‘INFINITE (preds bd)’
              by (simp[FINITE_preds] >> rpt strip_tac >> gvs[]) >>
            ‘preds bd ≼ Fin 𝕌(:α) (preds bd)’ by metis_tac[nontrivialBs] >>
            metis_tac[CARD_LE_FINITE])
        >- (resolve_then (Pos last) irule CARD_LE_EXP cardleq_TRANS >>
            simp[] >> irule (iffRL cardleq_lteq) >> simp[lt_cardSUC]) >>
        irule set_exp_cardle_cong >> simp[] >> rpt strip_tac >>
        gvs[cardleq_empty] >>
        ‘preds bd ≼ Fin 𝕌(:α) (preds bd)’ by metis_tac[nontrivialBs] >>
        first_x_assum $ C (resolve_then (Pos hd) irule) cardleq_TRANS >>
        irule (iffRL cardleq_lteq) >> simp[lt_cardSUC]) >>
  first_assum $ C (resolve_then (Pos last) irule) cardleq_TRANS >>
  qabbrev_tac ‘d = λ(y:('a,'c ordinal)F ,f). mapF I (THE o f) y’ >>
  simp[cardleq_def] >>
  irule_at Any (SRULE [PULL_EXISTS] SURJ_IMP_INJ) >> qexists_tac ‘d’ >>
  simp[SURJ_DEF] >> conj_tac
  >- (simp[FORALL_PROD,Abbr‘kA’, Abbr‘d’, Fin_def, setB_map, set_exp_def] >>
      rw[] >> simp[SUBSET_DEF, PULL_EXISTS] >> qx_gen_tac ‘b’ >> strip_tac >>
      ‘b ∈ preds bd’ by metis_tac[SUBSET_DEF] >> gs[] >> first_assum drule >>
      simp[PULL_EXISTS]) >>
  qx_gen_tac ‘vf’ >> strip_tac >>
  ‘?g. INJ g (setBF vf) (preds bd)’ by metis_tac[cardleq_def] >>
  qabbrev_tac ‘y = mapF I g vf’ >>
  ‘setBF vf ⊆ B’ by gs[Fin_def] >>
  ‘?f. (!b. b ∈ setBF vf ⇒ f (g b) = b) /\ (!bp. bp < bd ==> f bp ∈ B)’
    by (‘?be. be ∈ B’ by (simp[MEMBER_NOT_EMPTY] >>
                          strip_tac >> gvs[cardleq_empty]) >>
        qexists_tac ‘λbp. case some b. b IN setBF vf /\ g b = bp of
                            NONE => be
                          | SOME b => b
                    ’ >> conj_tac >> simp[] >> rpt strip_tac
        >- (gs[INJ_IFF, SF CONJ_ss] >> csimp[]) >>
        DEEP_INTRO_TAC optionTheory.some_intro >> simp[] >>
        gs[SUBSET_DEF]) >>
  qexists_tac ‘(y, λbp. if bp ∈ preds bd then SOME $ f bp else NONE)’ >>
  conj_tac
  >- (simp[Abbr‘kA’, Fin_def, Abbr‘y’, setB_map] >> conj_tac
      >- gs[INJ_IFF, SUBSET_DEF, PULL_EXISTS] >>
      simp[set_exp_def]) >>
  simp[Abbr‘d’, Abbr‘y’, mapO] >>
  simp[Once (GSYM mapID), SimpRHS] >> irule map_CONG >> simp[] >>
  gs[INJ_IFF]
QED

Theorem cardleq_preds_csuc:
  preds a ≼ preds b ⇒ preds (csuc a) ≼ preds (csuc b)
Proof
  simp[csuc_def] >> DEEP_INTRO_TAC oleast_intro >>
  simp[cardinality_bump_exists] >> rw[] >>
  DEEP_INTRO_TAC oleast_intro >>
  simp[cardinality_bump_exists] >> rw[] >>
  rename [‘preds a ≼ preds b’, ‘preds b ≺ preds c’, ‘preds a ≺ preds d’] >>
  CCONTR_TAC >>
  ‘∃c' : (α + num -> bool) ordinal.
     orderiso (wobound c allOrds) (wobound c' allOrds) ∧
     preds c ≈ preds c'’
    by (irule transfer_ordinals >>
        resolve_then (Pos last) irule preds_inj_univ cardleq_TRANS >>
        metis_tac[cardleq_lteq]) >>
  ‘preds c' ≺ preds d’ by metis_tac[CARD_LT_CONG, cardeq_REFL] >>
  drule_then assume_tac cardlt_preds >> first_x_assum drule >>
  metis_tac[CARD_LE_TRANS, CARD_LET_TRANS, CARD_LT_REFL, CARD_LT_CONG,
            cardeq_REFL]
QED

Theorem preds_bd_lemma[local]:
  setBF (gv  : (α,γ ordinal)F) ≠ ∅ ⇒
  preds (bd:γ ordinal) ≼
        preds (oleast a:(α,γ ordinal)F ordinal. preds a ≈ Fin 𝕌(:α) (preds bd))
Proof
  strip_tac >>
  ‘preds bd ≼ Fin 𝕌(:α) (preds bd)’
    by metis_tac[nontrivialBs] >>
  pop_assum mp_tac >>
  simp[Once cardleq_lteq, SimpL “$==>”] >> strip_tac
  >- (DEEP_INTRO_TAC oleast_intro >> conj_tac
      >- (irule cardeq_ordinals_exist >>
          simp[disjUNION_UNIV] >>
          resolve_then (Pos hd) irule CARD_LE_UNIV
                       CARD_LE_TRANS >>
          simp[CARD_LE_ADDL]) >>
      metis_tac[cardleq_lteq, CARD_LT_CONG, CARD_EQ_REFL]) >>
  DEEP_INTRO_TAC oleast_intro >> conj_tac
  >- (irule cardeq_ordinals_exist >>
      simp[disjUNION_UNIV] >>
      resolve_then (Pos hd) irule CARD_LE_UNIV CARD_LE_TRANS >>
      simp[CARD_LE_ADDL]) >>
  metis_tac[CARD_LE_REFL, CARD_LE_CONG]
QED

Theorem preds_csuc_lemma:
  preds a ≼ preds (csuc a)
Proof
  simp[csuc_def] >> DEEP_INTRO_TAC oleast_intro >>
  simp[cardinality_bump_exists] >> metis_tac[cardleq_lteq]
QED


Theorem Fin_MONO:
  s ⊆ t ⇒ Fin A s ⊆ Fin A t
Proof
  simp[Fin_def, SUBSET_DEF]
QED

Theorem Fin_cardleq:
  s ≼ t ⇒ Fin A s ≼ Fin A t
Proof
  simp[Fin_def, cardleq_def] >>
  disch_then $ qx_choose_then ‘f’ strip_assume_tac >>
  qexists_tac ‘mapF I f’ >> simp[INJ_IFF, setB_map, setA_map] >>
  rpt strip_tac >- gs[SUBSET_DEF, PULL_EXISTS, INJ_IFF] >>
  simp[EQ_IMP_THM] >> strip_tac >>
  ‘mapF I (LINV f s o f) x = mapF I I x ∧ mapF I (LINV f s o f) y = mapF I I y’
    by (conj_tac >> irule map_CONG >> drule_then assume_tac LINV_DEF >>
        gs[LINV_DEF, SUBSET_DEF]) >>
  qpat_x_assum ‘mapF I f x = _’ (mp_tac o Q.AP_TERM ‘mapF I (LINV f s)’) >>
  simp[mapO] >> simp[mapID, I_EQ_IDABS]
QED

Theorem cardADD2[local]:
  s ≼ s +_c 𝟚
Proof
  simp[CARD_LE_ADDR]
QED



Theorem CARD_12[simp]:
  {()} ≺ 𝟚 ∧ ¬({()} ≈ 𝟚) ∧ ¬(𝟚 ≈ {()}) ∧ {()} ≼ 𝟚
Proof
  conj_asm1_tac
  >- (simp[cardleq_def, INJ_IFF] >> qexistsl_tac [‘T’, ‘F’] >> simp[]) >>
  metis_tac[CARD_LT_CONG, CARD_LT_REFL, cardeq_REFL, cardleq_lteq]
QED

Theorem alg_cardinality_bound:
  ω ≤ (bd : γ ordinal) ∧ (∀x:(α,β+bool)F. setBF x ≼ preds bd) ∧
  (∃x:(α,γ ordinal)F. setBF x ≠ ∅) ⇒
  KK (s:(α,β)F -> β) (csuc bd) ≼ {T;F} ** preds (cardSUC $ Fin 𝕌(:α) (preds bd))
Proof
  strip_tac >> rename [‘setBF gv ≠ ∅’] >>
  qmatch_abbrev_tac ‘_ ≼ 𝟚 ** BD’ >>
  ‘INFINITE BD’
    by (strip_tac >> gs[Abbr‘BD’, FINITE_preds, cardSUC_EQN] >>
        ‘preds bd ≼ Fin 𝕌(:α) (preds bd)’ by metis_tac[nontrivialBs] >>
        ‘FINITE (preds bd)’ by metis_tac[CARD_LE_FINITE] >>
        gs[FINITE_preds]) >>
  ‘BD ≠ ∅’ by simp[Abbr‘BD’] >>
  ‘∀i. i < csuc bd ⇒ KK s i ≼ 𝟚 ** BD’
    suffices_by (strip_tac >> simp[csuc_is_nonzero_limit, KK_def] >>
                 irule CARD_BIGUNION >> simp[PULL_EXISTS] >>
                 rpt strip_tac >>
                 irule IMAGE_cardleq_rwt >> simp[cardSUC_def] >>
                 resolve_then Any
                              (fn th =>
                                 resolve_then (Pos hd) irule th cardleq_TRANS)
                              cardleq_REFL
                              CARD_LE_EXP >>
                 irule set_exp_cardle_cong >> simp[Abbr‘BD’, cardSUC_def] >>
                 irule cardleq_preds_csuc >> metis_tac[preds_bd_lemma]) >>
  ho_match_mp_tac ord_induction >> rw[] >>
  simp[Once KK_thm] >> rw[] >> irule CARD_BIGUNION >>
  simp[PULL_EXISTS] >> reverse (rpt conj_tac)
  >- (irule IMAGE_cardleq_rwt >> gs[lt_csuc] >> simp[cardSUC_def] >>
      resolve_then Any
                   (fn th =>
                      resolve_then (Pos hd) irule th cardleq_TRANS)
                   cardleq_REFL
                   CARD_LE_EXP >> irule set_exp_cardle_cong >> simp[] >>
      drule_then (qspec_then ‘bd’ assume_tac) preds_bd_lemma >>
      dxrule_then assume_tac cardleq_preds_csuc >>
      simp[Abbr‘BD’, cardSUC_def] >>
      pop_assum (C (resolve_then (Pos last) irule) cardleq_TRANS) >>
      first_assum (C (resolve_then (Pos hd) irule) cardleq_TRANS) >>
      simp[preds_csuc_lemma]) >>
  qx_gen_tac ‘j’ >> strip_tac >>
  ‘{ s fv | fv | setBF fv ⊆ KK s j} = IMAGE s (Fin 𝕌(:α) (KK s j))’
    by simp[EXTENSION, Fin_def] >> simp[] >>
  irule IMAGE_cardleq_rwt >>
  resolve_then (Pos hd) irule (MATCH_MP (GEN_ALL Fin_cardleq) cardADD2)
               cardleq_TRANS >>
  drule_then (drule_then $ qspec_then ‘KK s j +_c 𝟚’ mp_tac) CBDb >> impl_tac
  >- (conj_tac >- metis_tac[] >> simp[CARD_LE_ADDL]) >>
  disch_then $ C (resolve_then (Pos hd) irule) cardleq_TRANS >>
  first_x_assum $ qspec_then ‘j’ mp_tac >> simp[] >>
  impl_tac >- metis_tac[ordlt_TRANS] >>
  disch_then
    (C (resolve_then (Pos hd) (qspecl_then [‘𝟚’, ‘𝟚’] mp_tac)) CARD_LE_ADD) >>
  simp[] >> strip_tac >>
  pop_assum (
    C (resolve_then (Pos (el 2)) (resolve_then (Pos last)
                                  (qspec_then ‘BD’ mp_tac) cardleq_REFL))
    set_exp_cardle_cong) >>
  impl_tac >- simp[Abbr‘BD’] >>
  disch_then (C (resolve_then (Pos hd) irule) cardleq_TRANS) >>
  ‘𝟚 ≼ 𝟚 ** BD’ by (simp[cardleq_setexp] >> simp[Abbr‘BD’]) >>
  ‘INFINITE (𝟚 ** BD)’ by simp[] >>
  ‘𝟚 ** BD +_c 𝟚 ≈ 𝟚 ** BD’
    by metis_tac[CARD_ADD_SYM, CARD_ADD_ABSORB, cardeq_TRANS] >>
  qspecl_then [‘(𝟚 ** BD +_c 𝟚) ** BD’, ‘(𝟚 ** BD) ** BD’,
               ‘𝟚 ** BD’, ‘𝟚 ** BD’] mp_tac
              (INST_TYPE [“:γ” |-> “:'z”] CARD_LE_CONG) >>
  simp[cardeq_REFL] >> impl_tac
  >- (irule set_exp_card_cong >> simp[cardeq_REFL]) >>
  simp[] >> strip_tac >>
  resolve_then (Pos hd) (resolve_then (Pos hd) irule cardeq_REFL)
               set_exp_product (iffRL CARD_LE_CONG) >>
  irule set_exp_cardle_cong >> simp[] >> ONCE_REWRITE_TAC [cardleq_lteq] >>
  simp[CARD_SQUARE_INFINITE]
QED


val _ = export_theory();
