open HolKernel Parse boolLib bossLib;

open relationTheory pairTheory combinTheory pred_setTheory
open cardinalTheory

open ordinalTheory

val _ = new_theory "bnfAlgebra";

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

Definition Fin_def:
  Fin As Bs = { a : (α,β) F | setAF a ⊆ As ∧ setBF a ⊆ Bs }
End

val starter = new_axiom ("starter", “Fin 𝕌(:β) ∅ ≠ ∅”);

val map_CONG = new_axiom("map_CONG",
                         “(∀a. a ∈ setAF A ⇒ f1 a = f2 a) ∧
                          (∀b. b ∈ setBF A ⇒ g1 b = g2 b) ⇒
                          mapF f1 g1 A = mapF f2 g2 A”);

Theorem map_eq_id:
  (∀a. a ∈ setAF x ⇒ f a = a) ∧ (∀b. b ∈ setBF x ⇒ g b = b) ⇒ mapF f g x = x
Proof
  strip_tac >> ‘x = mapF I I x’ by simp[mapID, I_EQ_IDABS] >>
  pop_assum SUBST1_TAC >> simp[mapO] >> irule map_CONG >>
  simp[]
QED

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
val setF_exists = new_axiom("setF_exists", “∃x. setBF x ≠ ∅”);


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

Definition alg_def:
  alg (A : α set, s : (β,α) F -> α) ⇔ ∀x. x ∈ Fin UNIV A ⇒ s x ∈ A
End

Theorem alg_nonempty:
  alg(A, s : (β,α)F -> α) ⇒ A ≠ ∅
Proof
  rpt strip_tac >> gvs[alg_def] >>
  ‘Fin 𝕌(:β) ∅ = ∅’ by simp[EXTENSION] >>
  gs[starter]
QED

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

Theorem homs_compose:
  hom f (A : α set,s : (δ,α)F -> α) (B : β set,t) ∧ hom g (B,t) (C : γ set,u) ⇒
  hom (g o f) (A,s) (C,u)
Proof
  csimp[hom_def] >> rw[] >> RULE_ASSUM_TAC GSYM >> simp[] >>
  ‘mapF I f af ∈ Fin 𝕌(:δ) B ’
    by gs[Fin_def, setB_map, SUBSET_DEF, PULL_EXISTS] >>
  first_x_assum $ drule_then assume_tac >> simp[mapO]
QED

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

Theorem minset_ind':
  ∀P. (∀x. (∀y. y ∈ setBF x ⇒ y ∈ minset s ∧ P y) ⇒ P (s x)) ⇒
      ∀x. x ∈ minset s ⇒ P x
Proof
  metis_tac[minset_ind, SUBSET_DEF]
QED

Theorem minsub_gives_unique_homs:
  hom h1 (minset s, s) (C,t) ∧ hom h2 (minset s,s) (C,t) ⇒
  ∀a. a ∈ minset s ⇒ h1 a = h2 a
Proof
  strip_tac >> ho_match_mp_tac minset_ind' >> qx_gen_tac ‘af’ >> strip_tac >>
  gs[hom_def, Fin_def] >>
  ‘t (mapF I h1 af) = t (mapF I h2 af)’ suffices_by metis_tac[SUBSET_DEF] >>
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

Type alg[local,pp] = “:α set # ((β,α)F -> α)”

val idx_tydef as
              {absrep_id, newty, repabs_pseudo_id, termP, termP_exists,
               termP_term_REP, ...} =
  newtypeTools.rich_new_type{
  tyname = "idx",
  prove(“∃i : (α,β) alg. alg i”,
        simp[EXISTS_PROD] >> qexists_tac ‘UNIV’ >>
        simp[alg_def]),
  ABS = "mkIx",
  REP = "dIx"};

Definition bigprod_def:
  bigprod : ((α,β)idx -> α, β) alg =
  ({ f | ∀i. f i ∈ FST (dIx i) },
   λfv i. SND (dIx i) $ mapF I (λf. f i) fv)
End

Theorem bigprod_isalg:
  alg bigprod
Proof
  simp[bigprod_def, alg_def, FORALL_PROD, Fin_def] >> rpt strip_tac >>
  Cases_on ‘dIx i’ >> rename [‘dIx i = (A,s)’] >>
  ‘alg(A,s)’ by metis_tac[termP_term_REP] >> simp[] >> gs[alg_def] >>
  first_assum irule >>
  gs[Fin_def, setB_map, SUBSET_DEF, PULL_EXISTS] >> metis_tac[FST]
QED

Theorem bigprod_proj:
  alg (A,s) ⇒ hom (λf. f (mkIx (A,s))) bigprod (A,s)
Proof
  simp[hom_def, bigprod_def] >> rpt strip_tac
  >- metis_tac[bigprod_isalg, bigprod_def]
  >- (‘dIx (mkIx (A,s)) = (A,s)’ by metis_tac[repabs_pseudo_id] >>
      first_x_assum $ qspec_then ‘mkIx (A,s)’ mp_tac >> simp[]) >>
  ‘dIx (mkIx (A,s)) = (A,s)’ by metis_tac[repabs_pseudo_id] >>
  simp[]
QED

Theorem minbigprod_has_unique_homs:
  let s = SND (bigprod : ((α,β)idx -> α, β) alg)
  in
    ∀A f. alg ((A, f) : (α,β) alg) ⇒
          ∃!h. (∀d. d ∉ minset s ⇒ h d = ARB) ∧ hom h (minset s, s) (A, f)
Proof
  Cases_on ‘bigprod’ >> simp[] >> rpt strip_tac >>
  ‘alg bigprod’ by simp[bigprod_isalg] >>
  rename [‘bigprod = (AA,FF)’] >> gs[] >>
  ‘alg (minset FF, FF)’ by simp[] >>
  ‘∃h0 : ((α,β)idx -> α) -> α. hom h0 bigprod (A,f)’
    by (irule_at (Pos hd) bigprod_proj >> simp[]) >>
  ‘subalg (minset FF, FF) (AA,FF)’
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

Theorem minset_unique_homs:
  hom h1 (minset s, s) (B,t) ∧ hom h2 (minset s, s) (B,t) ⇒
  ∀a. a ∈ minset s ⇒ h1 a = h2 a
Proof
  strip_tac >> ho_match_mp_tac minset_ind' >> gs[hom_def, Fin_def] >>
  rpt strip_tac >> RULE_ASSUM_TAC GSYM >> simp[] >> gs[SUBSET_DEF] >>
  AP_TERM_TAC >> irule map_CONG >> simp[]
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
  gs[] >> qexists_tac ‘fv’ >> simp[] >> irule SUBSET_BIGUNION_SUBSET_I >>
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
  ∀B:β set. 𝟚 ≼ B ⇒ Fin 𝕌(:α) B ≼ B ** cardSUC (Fin 𝕌(:α) (preds bd))
Proof
  rpt strip_tac >>
  qabbrev_tac ‘kA = Fin 𝕌(:α) (preds bd) CROSS (B ** preds bd)’ >>
  qmatch_abbrev_tac ‘_ ≼ B ** k’ >>
  ‘kA ≼ B ** k’
    by (simp[Abbr‘k’, Abbr‘kA’] >> irule CARD_MUL2_ABSORB_LE >>
        simp[] >> rpt strip_tac >~
        [‘𝟚 ≼ B’, ‘B ≼ 𝟙’] >- (drule_all cardleq_TRANS >> simp[]) >~
        [‘INFINITE (Fin 𝕌(:α) (preds bd))’]
        >- (‘INFINITE (preds bd)’
              by (simp[FINITE_preds] >> rpt strip_tac >> gvs[]) >>
            ‘preds bd ≼ Fin 𝕌(:α) (preds bd)’ by metis_tac[nontrivialBs] >>
            metis_tac[CARD_LE_FINITE]) >~
        [‘Fin UNIV (preds bd) ≼ B ** cardSUC _’]
        >- (resolve_then (Pos last) irule CARD_LE_EXP cardleq_TRANS >>
            simp[]) >>
        irule set_exp_cardle_cong >> simp[] >> rpt strip_tac >>
        gvs[cardleq_empty] >>
        ‘preds bd ≼ Fin 𝕌(:α) (preds bd)’ by metis_tac[nontrivialBs] >>
        first_x_assum $ C (resolve_then (Pos hd) irule) cardleq_TRANS >>
        simp[]) >>
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

Theorem alg_cardinality_bound:
  ω ≤ (bd : γ ordinal) ∧ (∀x:(α,β+bool)F. setBF x ≼ preds bd) ∧
  (∃x:(α,γ ordinal)F. setBF x ≠ ∅) ⇒
  KK (s:(α,β)F -> β) (csuc bd) ≼ 𝟚 ** (cardSUC $ Fin 𝕌(:α) (preds bd))
Proof
  strip_tac >> rename [‘setBF gv ≠ ∅’] >>
  qmatch_abbrev_tac ‘_ ≼ 𝟚 ** BD’ >>
  ‘INFINITE BD’
    by (simp[Abbr‘BD’] >>
        ‘preds bd ≼ Fin 𝕌(:α) (preds bd)’ by metis_tac[nontrivialBs] >>
        strip_tac >>
        ‘FINITE (preds bd)’ by metis_tac[CARD_LE_FINITE] >>
        gs[FINITE_preds]) >>
  ‘BD ≠ ∅’ by (rpt strip_tac >> gs[]) >>
  ‘∀i. i < csuc bd ⇒ KK s i ≼ 𝟚 ** BD’
    suffices_by (strip_tac >> simp[KK_def, csuc_is_nonzero_limit] >>
                 irule CARD_BIGUNION >> simp[PULL_EXISTS] >>
                 irule IMAGE_cardleq_rwt >>
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
  >- (irule IMAGE_cardleq_rwt >> gs[lt_csuc] >>
      resolve_then Any
                   (fn th =>
                      resolve_then (Pos hd) irule th cardleq_TRANS)
                   cardleq_REFL
                   CARD_LE_EXP >> irule set_exp_cardle_cong >> simp[] >>
      drule_then (qspec_then ‘bd’ assume_tac) preds_bd_lemma >>
      dxrule_then assume_tac cardleq_preds_csuc >>
      simp[Abbr‘BD’, cardSUC_def] >>
      pop_assum (C (resolve_then (Pos last) irule) cardleq_TRANS) >>
      simp[lt_csuc, ordlt_preds_mono]) >>
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
  impl_tac >- simp[] >>
  disch_then (C (resolve_then (Pos hd) irule) cardleq_TRANS) >>
  ‘𝟚 ≼ 𝟚 ** BD’ by (simp[cardleq_setexp]) >>
  ‘INFINITE (𝟚 ** BD)’ by simp[] >>
  ‘𝟚 ** BD +_c 𝟚 ≈ 𝟚 ** BD’
    by metis_tac[CARD_ADD_SYM, CARD_ADD_ABSORB, cardeq_TRANS] >>
  drule_then (qspecl_then [‘BD’, ‘BD’] mp_tac) set_exp_card_cong >>
  simp[cardeq_REFL] >> strip_tac >>
  pop_assum (C (resolve_then (Pos hd)
                (resolve_then (Pos hd) irule cardeq_REFL))
             (iffRL CARD_LE_CONG)) >>
  resolve_then (Pos hd) (resolve_then (Pos hd) irule cardeq_REFL)
               set_exp_product (iffRL CARD_LE_CONG) >>
  irule set_exp_cardle_cong >> simp[] >> ONCE_REWRITE_TAC [cardleq_lteq] >>
  simp[CARD_SQUARE_INFINITE]
QED

Theorem KK_EQ_MINSET =
        KKbnd_EQ_minset |> INST_TYPE [“:γ” |-> “:α bndop”]
                        |> Q.INST [‘bd’ |-> ‘bnd’]
                        |> SRULE [bnd]

Theorem inst_bound =
        alg_cardinality_bound
          |> INST_TYPE [“:γ” |-> “:α bndop”]
          |> Q.INST [‘bd’ |-> ‘bnd’]
          |> SRULE [bnd, setF_exists, KK_EQ_MINSET]

Type algty0[pp] = (#1 $ dom_rng $ type_of $ rand $ concl inst_bound)

Theorem copy_alg_back:
  (A:α set) ≼ (B:β set) ∧ alg (A, s : (γ,α)F -> α) ⇒
  ∃(B0:β set) s' h j.
    hom h (B0,s') (A,s) ∧ hom j (A,s) (B0,s') ∧
    (∀a. a ∈ A ⇒ h (j a) = a) ∧ (∀b. b ∈ B0 ⇒ j (h b) = b)
Proof
  simp[cardleq_def] >> strip_tac >> rename [‘INJ h0 A B’] >>
  qexistsl_tac [‘IMAGE h0 A’, ‘λbv. h0 $ s $ mapF I (LINV h0 A) bv’,
                ‘LINV h0 A’, ‘h0’] >>
  csimp[hom_def, PULL_EXISTS] >>
  drule_then assume_tac LINV_DEF >> rw[]
  >- (gs[alg_def, Fin_def, SUBSET_DEF] >> rw[] >>
      irule_at Any EQ_REFL >> first_assum irule >>
      simp[setB_map, PULL_EXISTS] >> rw[] >> first_assum drule >>
      simp[PULL_EXISTS])
  >- (‘s (mapF I (LINV h0 A) bv) ∈ A’
        by (gs[alg_def, Fin_def] >> first_assum irule >>
            gs[setB_map, SUBSET_DEF, PULL_EXISTS] >> rw[] >>
            first_assum drule >> simp[PULL_EXISTS]) >>
      simp[] >> AP_TERM_TAC >> irule map_CONG >> simp[] >>
      gs[Fin_def, SUBSET_DEF])
  >- (simp[mapO] >> rename [‘av ∈ Fin UNIV A’] >>
      ‘mapF I (LINV h0 A o h0) av = mapF I I av’
        suffices_by simp[I_EQ_IDABS, mapID] >>
      irule map_CONG >> gs[Fin_def, SUBSET_DEF])
QED

Type algty[pp] = “:(α algty0,α)idx -> α algty0”
Definition IAlg_def:
  IAlg = minset (SND $ bigprod : ('a algty, 'a) alg)
End

Definition Cons_def:
  Cons = SND $ bigprod : ('a algty,'a)alg
End

Theorem IAlg_isalg:
  alg (IAlg, Cons)
Proof
  simp[IAlg_def, Cons_def]
QED

Theorem hom_arbification:
  hom h (A,s) (B,t) ⇒
  ∃j. hom j (A,s) (B,t) ∧ ∀x. x ∉ A ⇒ j x = ARB
Proof
  strip_tac >>
  qexists_tac ‘λx. if x ∈ A then h x else ARB’ >> simp[] >>
  gs[hom_def, Fin_def, alg_def] >> RULE_ASSUM_TAC GSYM >>
  simp[] >> rw[] >> AP_TERM_TAC >> irule map_CONG >> simp[] >>
  gs[SUBSET_DEF]
QED

Theorem initiality0:
  ∀(t:(α,γ)F -> γ) (G:γ set).
    alg(G,t) ⇒
    ∃!h. hom h (IAlg,Cons) (G,t) ∧ ∀x. x ∉ IAlg ⇒ h x = ARB
Proof
  rw[] >> simp[EXISTS_UNIQUE_THM] >> reverse conj_tac
  >- (rpt strip_tac >> simp[FUN_EQ_THM] >> qx_gen_tac ‘a’ >>
      Cases_on ‘a ∈ IAlg’ >> simp[] >> gs[IAlg_def, Cons_def] >>
      dxrule_then drule minset_unique_homs >> simp[]) >>
  irule hom_arbification >>
  simp[IAlg_def, Cons_def] >>
  qmatch_abbrev_tac ‘∃h. hom h (minset Is, Is) _’ >>
  ‘hom I (minset Is, Is) (FST bigprod,Is)’
    by (irule minsub_I_subalg >> simp[bigprod_isalg, Abbr‘Is’]) >>
  dxrule_then (irule_at (Pos hd)) homs_compose >>
  ‘hom I (minset t, t) (G,t)’ by (irule minsub_I_subalg >> metis_tac[]) >>
  pop_assum $ C (resolve_then (Pos last) (irule_at (Pos hd))) homs_compose >>
  ‘alg (minset t, t)’ by simp[] >>
  resolve_then (Pos hd) (drule_then strip_assume_tac)
               inst_bound copy_alg_back >>
  rename [‘hom h (A0,s) (minset t, t)’] >>
  first_assum $ C (resolve_then (Pos last) (irule_at (Pos hd))) homs_compose >>
  simp[Abbr‘Is’] >>
  irule_at (Pos hd) bigprod_proj >> gs[hom_def]
QED

Theorem inhabited:
  ∃w. IAlg w
Proof
  ‘alg (IAlg, Cons)’ by simp[IAlg_isalg] >>
  drule alg_nonempty >> simp[EXTENSION, IN_DEF]
QED

Theorem alg_Fin:
  alg (A,s) ⇒ alg (Fin 𝕌(:β) A, mapF I s)
Proof
  strip_tac >>
  simp[alg_def, Fin_def, SUBSET_DEF, setB_map, PULL_EXISTS] >> rw[] >>
  rename [‘s vf ∈ A’, ‘vf ∈ setBF vff’] >>
  first_assum $ drule_then assume_tac >>
  irule (iffLR $ SRULE [Fin_def, PULL_EXISTS] alg_def) >> simp[SUBSET_DEF]
QED

Definition arbify_def:
  arbify A f x = if x ∈ A then f x else ARB
End

Theorem hom_arbify:
  hom (arbify A f) (A,s : (γ,α)F -> α) (B,t : (γ,β)F -> β) ⇔ hom f (A,s) (B,t)
Proof
  simp[hom_def, arbify_def] >> Cases_on ‘alg (A,s)’ >> simp[] >>
  ‘∀af. af ∈ Fin 𝕌(:γ) A ⇒ s af ∈ A’ by gs[alg_def] >> simp[] >>
  rw[EQ_IMP_THM] >> RULE_ASSUM_TAC GSYM >> simp[] >> AP_TERM_TAC >>
  irule map_CONG >> gs[arbify_def, SUBSET_DEF, Fin_def]
QED

Theorem iso0:
  BIJ Cons (Fin 𝕌(:α) IAlg) IAlg
Proof
  ‘alg (IAlg, Cons : (α,α algty)F -> α algty)’ by simp[IAlg_isalg] >>
  drule_then assume_tac alg_Fin >>
  drule_then assume_tac initiality0 >>
  gs[EXISTS_UNIQUE_ALT] >>
  rename[‘hom _ (IAlg,Cons) _ ∧ _ ⇔ H = _’] >>
  ‘hom H (IAlg,Cons) (Fin 𝕌(:α) IAlg, mapF I Cons)’ by metis_tac[] >>
  ‘hom Cons (Fin 𝕌(:α) IAlg, mapF I Cons) (IAlg,Cons)’
    by (simp[hom_def] >> metis_tac[alg_def]) >>
  rev_drule_then (drule_then assume_tac) homs_compose >>
  rev_drule_then (strip_assume_tac o SRULE [EXISTS_UNIQUE_ALT]) initiality0 >>
  ‘hom (arbify IAlg (Cons o H)) (IAlg,Cons) (IAlg,Cons)’ by simp[hom_arbify] >>
  ‘∀x. x ∉ IAlg ⇒ arbify IAlg (Cons o H) x = ARB’ by simp[arbify_def] >>
  ‘hom (arbify IAlg I) (IAlg,Cons) (IAlg,Cons)’
    by (simp[hom_arbify] >> simp[hom_def, mapID, I_EQ_IDABS]) >>
  ‘∀x. x ∉ IAlg ⇒ arbify IAlg I x = ARB’ by simp[arbify_def] >>
  ‘arbify IAlg (Cons o H) = arbify IAlg I’ by metis_tac[] >>
  simp[BIJ_IFF_INV] >> conj_tac >- gs[alg_def] >>
  qexists_tac ‘H’ >> conj_tac
  >- (qpat_x_assum ‘hom H _ _’ mp_tac >> simp[hom_def, mapO]) >>
  conj_asm2_tac
  >- (qpat_x_assum ‘hom H _ _’ mp_tac >> simp[hom_def, mapO] >> strip_tac >>
      qx_gen_tac ‘a’ >> strip_tac >>
      ‘H (Cons a) = mapF I (Cons o H) a’ by simp[] >> pop_assum SUBST1_TAC >>
      ‘mapF I (Cons o H) a = mapF I I a’ suffices_by simp[I_EQ_IDABS, mapID] >>
      irule map_CONG >> gs[Fin_def, SUBSET_DEF]) >>
  pop_assum mp_tac >> simp[Once FUN_EQ_THM, arbify_def] >> metis_tac[]
QED

val itype = newtypeTools.rich_new_type("nty", inhabited)

Definition NCONS_def:
  NCONS (x : (α, α nty)F) = nty_ABS $ Cons $ mapF I nty_REP x
End

Theorem NCONS_isalg:
  alg (UNIV, NCONS)
Proof
  simp[alg_def]
QED

Theorem hom_nty_ABS:
  hom nty_ABS (IAlg,Cons) (UNIV,NCONS)
Proof
  simp[hom_def, NCONS_isalg, IAlg_isalg] >> simp[NCONS_def, mapO] >>
  rpt strip_tac >> rpt AP_TERM_TAC >> irule map_eq_id >>
  gs[Fin_def, SUBSET_DEF, #repabs_pseudo_id itype, IN_DEF]
QED

Theorem hom_nty_REP:
  hom nty_REP (UNIV, NCONS) (IAlg, Cons)
Proof
  simp[hom_def, NCONS_isalg, IAlg_isalg] >> conj_tac
  >- simp[IN_DEF, # termP_term_REP itype] >>
  simp[NCONS_def] >> rpt strip_tac >> ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
  irule (#repabs_pseudo_id itype) >>
  ‘alg (IAlg : 'a algty set,Cons)’ by simp[IAlg_isalg] >>
  gs[alg_def, Fin_def, SUBSET_DEF] >>
  ONCE_REWRITE_TAC [GSYM SPECIFICATION] >> pop_assum irule >>
  simp[setB_map, PULL_EXISTS] >> simp[IN_DEF, #termP_term_REP itype]
QED

Theorem initiality_hom:
  alg(B,t) ⇒ ∃!h. hom h (UNIV,NCONS) (B,t)
Proof
  strip_tac >>
  simp[EXISTS_UNIQUE_THM] >>
  drule_then (strip_assume_tac o SRULE[EXISTS_UNIQUE_ALT]) initiality0 >>
  rename [‘hom _ _ _ ∧ _ ⇔ H = _’] >>
  ‘hom H (IAlg,Cons) (B,t)’ by metis_tac[] >> conj_tac
  >- metis_tac[homs_compose, hom_nty_REP] >>
  qx_genl_tac [‘h1’, ‘h2’] >> strip_tac >>
  ‘hom (arbify IAlg (h1 o nty_ABS)) (IAlg,Cons) (B,t) ∧
   hom (arbify IAlg (h2 o nty_ABS)) (IAlg,Cons) (B,t)’
    by (simp[hom_arbify] >> metis_tac[homs_compose, hom_nty_ABS]) >>
  ‘arbify IAlg (h1 o nty_ABS) = arbify IAlg (h2 o nty_ABS)’
    by metis_tac[arbify_def] >>
  pop_assum mp_tac >> ONCE_REWRITE_TAC [FUN_EQ_THM] >> simp[arbify_def] >>
  strip_tac >> qx_gen_tac ‘a’ >>
  qspec_then ‘a’ (SUBST1_TAC o SYM) (#absrep_id itype) >>
  pop_assum $ qspec_then ‘nty_REP a’ mp_tac >>
  simp[#termP_term_REP itype, IN_DEF]
QED

Theorem initiality =
        initiality_hom |> Q.INST [‘B’ |-> ‘UNIV’]
                       |> SRULE [hom_def, alg_def, Fin_def]
                       |> GSYM |> Q.GEN ‘t’

Theorem UNIQUE_SKOLEM:
  (∀x. ∃!y. P x y) ⇔ ∃!f. ∀x. P x (f x)
Proof
  eq_tac >> simp[EXISTS_UNIQUE_THM] >> rw[]
  >- (qexists_tac ‘λx. @y. P x y’ >> simp[] >> gen_tac >> SELECT_ELIM_TAC >>
      metis_tac[])
  >- (simp[FUN_EQ_THM] >> metis_tac[])
  >- metis_tac[]
  >- (rename [‘P x a’, ‘P x b’, ‘a = b’] >>
      Cases_on ‘f x = a’ >> gvs[]
      >- (first_x_assum $ qspecl_then [‘f’, ‘f (| x |-> b |)’] mp_tac >>
          simp[APPLY_UPDATE_THM] >> disch_then irule >> rw[] >> rw[]) >>
      first_x_assum $ qspecl_then [‘f(|x|->a|)’, ‘f’] mp_tac >>
      simp[APPLY_UPDATE_THM, FUN_EQ_THM] >> metis_tac[])
QED

Theorem MAP_exists =
        initiality |> INST_TYPE [alpha |-> “:α nty” ]
                   |> Q.SPEC ‘NCONS o mapF f I’
                   |> SRULE [mapO]
                   |> Q.GEN ‘f’
                   |> SRULE[UNIQUE_SKOLEM]
                   |> CONV_RULE (RENAME_VARS_CONV ["MAP"])
                   |> SRULE[EXISTS_UNIQUE_THM] |> cj 1

val MAP_def = new_specification("MAP_def", ["MAP"], MAP_exists);

Theorem minset_Cons:
  minset Cons = IAlg
Proof
  simp[Cons_def, IAlg_def]
QED

Theorem ALL_Ialg:
  (∀ia. ia ∈ IAlg ⇒ P ia) ⇔ (∀n. P (nty_REP n))
Proof
  eq_tac >> rw[] >> gs[IN_DEF]
  >- (pop_assum $ qspec_then ‘nty_REP n’ mp_tac >>
      simp[#termP_term_REP itype]) >>
  first_x_assum $ qspec_then ‘nty_ABS ia’ mp_tac >>
  simp[#repabs_pseudo_id itype]
QED

Theorem ALL_Ialgv:
  (∀av. setBF av ⊆ IAlg ⇒ P av) ⇔
  (∀n. P (mapF I nty_REP n))
Proof
  rw[EQ_IMP_THM]
  >- (pop_assum irule >> simp[setB_map, SUBSET_DEF, PULL_EXISTS] >>
      simp[IN_DEF, #termP_term_REP itype]) >>
  first_x_assum $ qspec_then ‘mapF I nty_ABS av’ mp_tac >>
  simp[mapO] >>
  ‘mapF I (nty_REP o nty_ABS) av = av’ suffices_by simp[] >>
  irule map_eq_id >> gs[SUBSET_DEF, #repabs_pseudo_id itype, IN_DEF]
QED

Theorem IN_setBF:
  (∀y. y ∈ setBF x ⇒ Q (nty_ABS y)) ⇔ x ∈ Fin 𝕌(:α) (Q o nty_ABS)
Proof
  simp[Fin_def, SUBSET_DEF] >> simp[IN_DEF]
QED

Theorem Cons_NCONS:
  setBF x ⊆ IAlg ⇒
  Cons x = nty_REP (NCONS (mapF I nty_ABS x))
Proof
  simp[NCONS_def, mapO] >> strip_tac >>
  ‘mapF I (nty_REP o nty_ABS) x = x’
    by (irule map_eq_id >> gs[SUBSET_DEF, IN_DEF, #repabs_pseudo_id itype]) >>
  simp[] >>
  ‘Cons x ∈ IAlg’ suffices_by simp[IN_DEF, #repabs_pseudo_id itype] >>
  irule (iffLR alg_def) >> simp[IAlg_isalg, Fin_def]
QED

Theorem abs_o_rep:
  nty_ABS o nty_REP = I
Proof
  simp[FUN_EQ_THM, #absrep_id itype]
QED

Theorem setBF_applied:
  setBF x v ⇔ v ∈ setBF x
Proof
  simp[IN_DEF]
QED

Theorem IND =
        minset_ind |> Q.GEN ‘s’
                   |> Q.ISPEC ‘Cons’
                   |> SRULE [minset_Cons]
                   |> Q.SPEC ‘λia. Q (nty_ABS ia)’
                   |> SRULE[ALL_Ialg, #absrep_id itype, IN_setBF, Cons_NCONS]
                   |> SRULE[GSYM AND_IMP_INTRO, ALL_Ialgv, mapO, Fin_def,
                            setB_map, abs_o_rep, I_EQ_IDABS, mapID]
                   |> SRULE[SUBSET_DEF, PULL_EXISTS, IN_DEF, #absrep_id itype]
                   |> SRULE [setBF_applied]

Theorem NCONS_comp:
  NCONS = nty_ABS o Cons o mapF I nty_REP
Proof
  simp[FUN_EQ_THM, NCONS_def]
QED

Theorem iso:
  BIJ NCONS (Fin 𝕌(:α) 𝕌(:α nty)) 𝕌(:α nty)
Proof
  simp[NCONS_comp] >> irule BIJ_COMPOSE >> qexists_tac ‘IAlg’ >>
  reverse conj_tac
  >- (simp[BIJ_IFF_INV] >> qexists_tac ‘nty_REP’ >>
      simp[#repabs_pseudo_id itype, #absrep_id itype, IN_DEF,
           #termP_term_REP itype]) >>
  irule BIJ_COMPOSE >> irule_at Any iso0 >>
  simp[BIJ_IFF_INV] >> conj_tac
  >- simp[Fin_def, setB_map, SUBSET_DEF, PULL_EXISTS, IN_DEF,
          #termP_term_REP itype] >>
  qexists_tac ‘mapF I nty_ABS’ >> simp[mapO, abs_o_rep, I_EQ_IDABS, mapID] >>
  conj_tac >- simp[Fin_def] >>
  rpt strip_tac >> irule map_eq_id >> simp[] >>
  gs[Fin_def, SUBSET_DEF, #repabs_pseudo_id itype, IN_DEF]
QED

Theorem Fin_UNIV:
  Fin UNIV UNIV = UNIV
Proof
  simp[EXTENSION, Fin_def]
QED

Theorem NCONS_11:
  NCONS x = NCONS y ⇔ x = y
Proof
  assume_tac iso >> gs[BIJ_DEF, Fin_UNIV, INJ_IFF]
QED

val DEST_def = new_specification("DEST_def", ["DEST"],
                                 iso |> SRULE [BIJ_IFF_INV, Fin_UNIV])

Theorem MAP_ID:
  ∀n. MAP I n = n
Proof
  ho_match_mp_tac IND >> simp[MAP_def, NCONS_11] >> rw[] >>
  irule map_eq_id >> simp[]
QED

Theorem MAP_COMPOSE:
  ∀n. MAP f (MAP g n) = MAP (f o g) n
Proof
  ho_match_mp_tac IND >> simp[MAP_def, NCONS_11, mapO] >> rw[] >>
  irule map_CONG >> simp[]
QED

val SET_def = new_specification (
  "SET_def", ["SET"],
  initiality |> Q.ISPEC ‘λfv. setAF fv ∪ BIGUNION (setBF fv)’
             |> SRULE[setA_map, setB_map]
             |> SRULE[EXISTS_UNIQUE_THM] |> cj 1);

Theorem SET_MAP:
  ∀n. SET (MAP f n) = IMAGE f (SET n)
Proof
  ho_match_mp_tac IND >>
  simp[SET_def, MAP_def, setA_map, setB_map, IMAGE_IMAGE] >> rw[] >>
  simp[Once EXTENSION] >> qx_gen_tac ‘a’ >> eq_tac >> rw[]
  >- metis_tac[]
  >- (first_x_assum $ drule_then assume_tac >> gs[PULL_EXISTS] >> metis_tac[])
  >- metis_tac[]
  >- (simp[PULL_EXISTS] >> first_x_assum $ drule_then assume_tac >>
      metis_tac[IN_IMAGE])
QED

Theorem MAP_CONG:
  ∀n. (∀a. a ∈ SET n ⇒ f a = g a) ⇒ MAP f n = MAP g n
Proof
  ho_match_mp_tac IND >>
  simp[MAP_def, SET_def, PULL_EXISTS, NCONS_11] >> rw[] >>
  irule map_CONG >> simp[] >> metis_tac[]
QED

val _ = export_theory();
