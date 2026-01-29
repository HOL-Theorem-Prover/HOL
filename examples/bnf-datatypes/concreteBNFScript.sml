Theory concreteBNF
Ancestors
  relation pair combin pred_set cardinal ordinal ordinalBasic
  finite_map[qualified]

fun SRULE ths = SIMP_RULE (srw_ss()) ths

Type F[pp] = “:(num |-> β) + num # (α # β) list”

(* view this as

       F(X) = (num |-> X) + num * (A * X) list

       or with datatype syntax

          foo = C1 (num |-> foo)
              | C2 num (('a # foo) list)

       SUM [fmap[γ](β), PAIR [C[num], LIST [PAIR [α,β]]]]

 *)

Theorem IMAGE_equalx[simp,local]:
  IMAGE f ((=) x) = (=) (f x)
Proof
  simp[EXTENSION] >> simp[IN_DEF] >> metis_tac[]
QED

Theorem IN_equalx[simp,local]:
  x ∈ $=y ⇔ x = y
Proof
  simp[IN_DEF] >> metis_tac[]
QED

Theorem countable_equalx[simp,local]:
  countable ($= x)
Proof
  irule finite_countable >>
  ‘$= x = {x}’ suffices_by simp[] >>
  simp[FUN_EQ_THM] >> metis_tac[]
QED

Theorem equalx_NOT_EMPTY[simp,local]:
  $= x ≠ ∅
Proof
  simp[FUN_EQ_THM]
QED

Theorem BIGUNION_equalx[simp,local]:
  BIGUNION ($= x) = x
Proof
  simp[Once EXTENSION]
QED

Theorem BIGUNION_IMAGE_equal[simp,local]:
  BIGUNION (IMAGE (=) A) = A
Proof
  simp[Once EXTENSION, PULL_EXISTS]
QED

Theorem BIGUNION_IMAGE_K0[simp,local]:
  BIGUNION (IMAGE (K ∅) A) = ∅
Proof
  simp[Once EXTENSION] >> simp[Once EXTENSION] >>
  simp[EQ_IMP_THM, PULL_EXISTS] >> metis_tac[]
QED

(* ----------------------------------------------------------------------
    pairs
   ---------------------------------------------------------------------- *)

Theorem pairmapID[local]:
  ((λx.x) ## (λy.y)) = (λp.p)
Proof
  simp[FUN_EQ_THM] >> Cases_on ‘p’ >> simp[]
QED

Theorem pairmapO:
  (f1 ## f2) o (g1 ## g2) = (f1 o g1) ## (f2 o g2)
Proof
  simp[FUN_EQ_THM, pairTheory.FORALL_PROD]
QED

Definition pairsetA_def: pairsetA (x,y) = {x}
End

Definition pairsetB_def: pairsetB (x,y) = {y}
End

Definition pairset_def:
  pairset fA fB p =
  BIGUNION (IMAGE fA (pairsetA p)) ∪ BIGUNION (IMAGE fB (pairsetB p))
End

Theorem pairset_map:
  pairset sfA sfB o (##) fA fB = pairset (sfA o fA) (sfB o fB)
Proof
  simp[Once FUN_EQ_THM, PULL_EXISTS] >> Cases >>
  simp[pairset_def, pairsetA_def, pairsetB_def]
QED
Theorem pairset_map' = pairset_map |> SRULE [Once FUN_EQ_THM]

Theorem IMAGE_pairset:
  IMAGE f (pairset sfA sfB p) = pairset (IMAGE f o sfA) (IMAGE f o sfB) p
Proof
  simp[pairset_def, IMAGE_BIGUNION, IMAGE_IMAGE]
QED
Theorem pairsetA_map:
  pairsetA ((##) fA fB p) = IMAGE fA (pairsetA p)
Proof
  Cases_on ‘p’ >> simp[pairsetA_def]
QED
Theorem pairsetB_map:
  pairsetB ((##) fA fB p) = IMAGE fB (pairsetB p)
Proof
  Cases_on ‘p’ >> simp[pairsetB_def]
QED

Theorem PAIR_MAP_CONG:
  (∀a. a ∈ pairsetA p ⇒ f1 a = f2 a) ∧
  (∀b. b ∈ pairsetB p ⇒ g1 b = g2 b) ⇒
  (f1 ## g1) p = (f2 ## g2) p
Proof
  Cases_on ‘p’ >> simp[pairsetA_def, pairsetB_def]
QED

Theorem pairsetA_countable:
  countable (pairsetA p)
Proof
  Cases_on ‘p’ >> simp[pairsetA_def]
QED

Theorem pairsetB_countable:
  countable (pairsetB p)
Proof
  Cases_on ‘p’ >> simp[pairsetB_def]
QED

Theorem pairset_CONG:
  (∀a. a ∈ pairsetA p ⇒ f1 a = f2 a) ∧
  (∀b. b ∈ pairsetB p ⇒ g1 b = g2 b) ⇒
  pairset f1 g1 p = pairset f2 g2 p
Proof
  Cases_on ‘p’ >> gvs[pairset_def, pairsetA_def, pairsetB_def]
QED

(* ----------------------------------------------------------------------
    sums
   ---------------------------------------------------------------------- *)

Theorem summapID[local]:
  SUM_MAP (λx.x) (λy.y) = (λs.s)
Proof
  simp[FUN_EQ_THM] >> Cases_on ‘s’ >> simp[]
QED

Definition sumsetA_def:
  sumsetA (INL x) = {x} ∧
  sumsetA (INR y) = {}
End

Definition sumsetB_def:
  sumsetB (INL x) = ∅ ∧
  sumsetB (INR y) = {y}
End

Definition sumset_def:
  sumset sfA sfB s = BIGUNION (IMAGE sfA (sumsetA s)) ∪
                     BIGUNION (IMAGE sfB (sumsetB s))
End

Theorem sumset_map:
  sumset sfA sfB o SUM_MAP fA fB = sumset (sfA o fA) (sfB o fB)
Proof
  simp[Once FUN_EQ_THM] >> Cases >>
  simp[sumset_def, sumsetA_def, sumsetB_def]
QED
Theorem sumset_map' = sumset_map |> SRULE [Once FUN_EQ_THM]

Theorem IMAGE_sumset:
  IMAGE f (sumset sfA sfB s) =
  sumset (IMAGE f o sfA) (IMAGE f o sfB) s
Proof
  simp[sumset_def, IMAGE_BIGUNION, IMAGE_IMAGE]
QED

Theorem sumsetA_map:
  sumsetA (SUM_MAP fA fB s) = IMAGE fA (sumsetA s)
Proof
  Cases_on ‘s’ >> simp[sumsetA_def]
QED
Theorem sumsetB_map:
  sumsetB (SUM_MAP fA fB s) = IMAGE fB (sumsetB s)
Proof
  Cases_on ‘s’ >> simp[sumsetB_def]
QED

Theorem SUM_MAP_CONG:
  (∀a. a ∈ sumsetA s ⇒ f1 a = f2 a) ∧
  (∀b. b ∈ sumsetB s ⇒ g1 b = g2 b) ⇒
  SUM_MAP f1 g1 s = SUM_MAP f2 g2 s
Proof
  Cases_on ‘s’ >> simp[sumsetA_def, sumsetB_def]
QED

Theorem sumsetA_countable:
  countable (sumsetA s)
Proof
  Cases_on ‘s’ >> simp[sumsetA_def]
QED
Theorem sumsetB_countable:
  countable (sumsetB s)
Proof
  Cases_on ‘s’ >> simp[sumsetB_def]
QED

Theorem sumset_CONG:
  (∀a. a ∈ sumsetA s ⇒ f1 a = f2 a) ∧
  (∀b. b ∈ sumsetB s ⇒ g1 b = g2 b) ⇒
  sumset f1 g1 s = sumset f2 g2 s
Proof
  Cases_on ‘s’ >> simp[sumset_def, sumsetA_def, sumsetB_def]
QED

(* ----------------------------------------------------------------------
    lists
   ---------------------------------------------------------------------- *)

Theorem listmapID[local]:
  MAP (λe.e) = (λl.l)
Proof
  simp[FUN_EQ_THM]
QED

Theorem listmapO[local] = listTheory.MAP_COMPOSE
Overload listsetA[local] = “list$LIST_TO_SET”

Definition listset_def:
  listset fA l = BIGUNION (IMAGE fA (listsetA l))
End

Theorem listset_map:
  listset sfA o MAP fA = listset (sfA o fA)
Proof
  simp[Once FUN_EQ_THM,listset_def, listTheory.LIST_TO_SET_MAP, IMAGE_o]
QED
Theorem listset_map' = SRULE[Once FUN_EQ_THM] listset_map
Theorem IMAGE_listset:
  IMAGE fA (listset sfA l) = listset (IMAGE fA o sfA) l
Proof
  simp[listset_def, IMAGE_BIGUNION, IMAGE_o]
QED
Theorem listsetA_map = listTheory.LIST_TO_SET_MAP |> SPEC_ALL

Theorem LIST_MAP_CONG:
  (∀a. a ∈ listsetA l ⇒ f1 a = f2 a) ⇒
  MAP f1 l = MAP f2 l
Proof
  strip_tac >> irule listTheory.MAP_CONG >> simp[]
QED

Theorem listsetA_countable:
  countable (listsetA l)
Proof
  irule finite_countable >> simp[]
QED

Theorem listset_CONG:
  (∀a. a ∈ listsetA l ⇒ f1 a = f2 a) ⇒
  listset f1 l = listset f2 l
Proof
  simp[listset_def] >> strip_tac >>
  csimp[Once EXTENSION, PULL_EXISTS]
QED

(* ----------------------------------------------------------------------
    finite maps
   ---------------------------------------------------------------------- *)

Theorem fmapID[local]:
  (o_f) (λx.x) = (λy.y)
Proof
  simp[finite_mapTheory.fmap_EXT, FUN_EQ_THM]
QED

Theorem fmapO:
  (o_f) f o (o_f) g = (o_f) (f o g)
Proof
  simp[FUN_EQ_THM]
QED

Overload fmapsetA[local,inferior] = “FRANGE”
Definition fmapset_def:
  fmapset fA fm = BIGUNION (IMAGE fA (fmapsetA fm))
End

Theorem fmapset_map:
  fmapset sfA o (o_f) fA = fmapset (sfA o fA)
Proof
  simp[Once FUN_EQ_THM, GSYM finite_mapTheory.IMAGE_FRANGE, fmapset_def] >>
  simp[IMAGE_o]
QED
Theorem fmapset_map' = SRULE[Once FUN_EQ_THM] fmapset_map
Theorem IMAGE_fmapset:
  IMAGE fA (fmapset sfA fm) = fmapset (IMAGE fA o sfA) fm
Proof
  simp[fmapset_def, pred_setTheory.IMAGE_BIGUNION, pred_setTheory.IMAGE_o]
QED
Theorem fmapsetA_map = finite_mapTheory.IMAGE_FRANGE |> GSYM |> SPEC_ALL

Theorem FMAP_COMPOSE_CONG:
  (∀v. v ∈ fmapsetA fm ⇒ f v = g v) ⇒
  f o_f fm = g o_f fm
Proof
  metis_tac[finite_mapTheory.o_f_cong]
QED

Theorem fmapsetA_countable:
  countable (fmapsetA fm)
Proof
  irule finite_countable >> simp[]
QED

Theorem fmapset_CONG:
  (∀a. a ∈ fmapsetA fm ⇒ f1 a = f2 a) ⇒
  fmapset f1 fm = fmapset f2 fm
Proof
  simp[fmapset_def, PULL_EXISTS] >> strip_tac >>
  csimp[Once EXTENSION, PULL_EXISTS]
QED

(* ----------------------------------------------------------------------
    Can now define set and map for our new functor; establishing
    functoriality and naturalness
   ---------------------------------------------------------------------- *)

Definition FsetA_def:
  FsetA : (α,β)F -> α set =
  sumset (K ∅) (pairset (K ∅) (listset (pairset (=) (K ∅))))
End
Definition FsetB_def:
  FsetB : (α,β) F -> β set =
  sumset (fmapset (=)) (pairset (K ∅) (listset (pairset (K ∅) (=))))
End

Definition Fset_def:
  Fset sfA sfB v =
  BIGUNION (IMAGE sfA (FsetA v)) ∪ BIGUNION (IMAGE sfB (FsetB v))
End

Overload setF[local,inferior] = “Fset”
Overload setAF[local,inferior] = “FsetA”
Overload setBF[local,inferior] = “FsetB”

Theorem IMAGE_Fset:
  IMAGE f (setF sfA sfB v) = setF (IMAGE f o sfA) (IMAGE f o sfB) v
Proof
  simp_tac bool_ss
           [Fset_def, IMAGE_sumset, o_DEF, IMAGE_pairset, IMAGE_listset,
            IMAGE_fmapset, IMAGE_BIGUNION, IMAGE_IMAGE, IMAGE_UNION]
QED

Definition Fmap_def:
  Fmap f1 f2 : (α,β)F -> (γ,δ)F = SUM_MAP ((o_f) f2) (I ## MAP (f1 ## f2))
End

Theorem Fset_Fmap:
  Fset sfA sfB o Fmap f1 f2 = Fset (sfA o f1) (sfB o f2)
Proof
  ONCE_REWRITE_TAC [FUN_EQ_THM] >>
  simp_tac bool_ss [Fmap_def, Fset_def, sumset_map', pairset_map, listset_map,
                    fmapset_map, o_DEF, FsetA_def, FsetB_def, K_THM,
                    IMAGE_sumset, IMAGE_pairset, IMAGE_EMPTY,
                    IMAGE_listset, IMAGE_equalx, IMAGE_fmapset]
QED

Theorem Fset_Fmap' = SRULE[Once FUN_EQ_THM] Fset_Fmap

Theorem FsetA_map:
  FsetA (Fmap fA fB fm) = IMAGE fA (FsetA fm)
Proof
  simp_tac bool_ss
           [FsetA_def, Fmap_def, sumset_map', pairset_map, listset_map,
            fmapset_map',
            IMAGE_sumset, o_DEF, IMAGE_pairset, IMAGE_listset, SF ETA_ss,
            K_THM, IMAGE_EMPTY, IMAGE_equalx, IMAGE_fmapset]
QED

Theorem FsetB_map:
  setBF (Fmap fA fB fm) = IMAGE fB (setBF fm)
Proof
  simp_tac bool_ss
           [FsetB_def, Fmap_def, sumset_map', pairset_map, listset_map,
            fmapset_map',
            IMAGE_sumset, o_DEF, IMAGE_pairset, IMAGE_listset, SF ETA_ss,
            K_THM, IMAGE_EMPTY, IMAGE_equalx, IMAGE_fmapset]
QED

Theorem mapID0:
  Fmap (λx.x) (λy.y) = (λv.v)
Proof
  simp_tac bool_ss [Fmap_def,pairmapID,listmapID,fmapID,summapID,I_EQ_IDABS]
QED
Theorem mapID = mapID0 |> SRULE[FUN_EQ_THM]

Theorem mapO0:
  Fmap f1 f2 o Fmap g1 g2 = Fmap (f1 o g1) (f2 o g2)
Proof
  simp_tac bool_ss [Fmap_def, sumTheory.SUM_MAP_o, GSYM listTheory.MAP_o,
                    pairmapO, fmapO, I_o_ID]
QED
Theorem mapO = mapO0 |> SRULE[FUN_EQ_THM] |> GEN_ALL

Theorem sumsetA_EI:
  a ∈ sumsetA v ∧ w ∈ sfA a ⇒
  w ∈ sumset sfA sfB v
Proof
  simp[PULL_EXISTS, sumset_def] >> metis_tac[]
QED

Theorem sumsetB_EI:
  a ∈ sumsetB v ∧ w ∈ sfB a ⇒
  w ∈ sumset sfA sfB v
Proof
  simp[PULL_EXISTS, sumset_def] >> metis_tac[]
QED

Theorem pairsetA_EI:
  a ∈ pairsetA v ∧ w ∈ sfA a ⇒
  w ∈ pairset sfA sfB v
Proof
  simp[PULL_EXISTS, pairset_def] >> metis_tac[]
QED
Theorem pairsetB_EI:
  a ∈ pairsetB v ∧ w ∈ sfB a ⇒
  w ∈ pairset sfA sfB v
Proof
  simp[PULL_EXISTS, pairset_def] >> metis_tac[]
QED

Theorem fmapsetA_EI:
  a ∈ fmapsetA v ∧ w ∈ sfA a ⇒
  w ∈ fmapset sfA v
Proof
  simp[PULL_EXISTS, fmapset_def] >> metis_tac[]
QED

Theorem listsetA_EI:
  a ∈ listsetA v ∧ w ∈ sfA a ⇒
  w ∈ listset sfA v
Proof
  simp[PULL_EXISTS, listset_def] >> metis_tac[]
QED

Theorem Fmap_CONG:
  (∀a. a ∈ FsetA v ⇒ f1 a = f2 a) ∧
  (∀b. b ∈ FsetB v ⇒ g1 b = g2 b) ⇒
  Fmap f1 g1 v = Fmap f2 g2 v
Proof
  simp_tac bool_ss [Fmap_def,FsetA_def, FsetB_def] >> strip_tac >>
  irule SUM_MAP_CONG >> RW_TAC bool_ss []
  >- (irule FMAP_COMPOSE_CONG >> rw[] >> first_x_assum irule >>
      drule_then irule sumsetA_EI >>
      drule_then irule fmapsetA_EI >> simp[])
  >- (irule PAIR_MAP_CONG >> simp[] >> rw[] >> irule LIST_MAP_CONG >>
      rw[] >> irule PAIR_MAP_CONG >> rw[]
      >- (first_x_assum irule >>
          irule sumsetB_EI >> first_x_assum $ irule_at Any >>
          irule pairsetB_EI >> first_x_assum $ irule_at Any >>
          irule listsetA_EI >> first_x_assum $ irule_at Any >>
          irule pairsetA_EI >> first_x_assum $ irule_at Any >>
          simp[]) >>
      first_x_assum irule >>
      irule sumsetB_EI >> first_x_assum $ irule_at Any >>
      irule pairsetB_EI >> first_x_assum $ irule_at Any >>
      irule listsetA_EI >> first_x_assum $ irule_at Any >>
      irule pairsetB_EI >> first_x_assum $ irule_at Any >>
      simp[])
QED

Theorem Fset_CONG:
  (∀a. a ∈ FsetA v ⇒ f1 a = f2 a) ∧
  (∀b. b ∈ FsetB v ⇒ g1 b = g2 b) ⇒
  Fset f1 g1 v = Fset f2 g2 v
Proof
  simp[Fset_def] >> strip_tac >>
  simp[Once EXTENSION, PULL_EXISTS, SF CONJ_ss]
QED

(* ----------------------------------------------------------------------
    functor must also be bounded
   ---------------------------------------------------------------------- *)

Definition bnd_def: bnd = ω
End

Theorem cardleq_omega_countable:
  x ≼ preds ω ⇔ countable x
Proof
  simp[countable_def, cardleq_def, EQ_IMP_THM, INJ_IFF] >> rw[]
  >- (gs[lt_omega] >> gs[GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] >>
      rename [‘f _ : β ordinal= &(g _)’] >> qexistsl_tac [‘g’] >> simp[]) >>
  simp[lt_omega] >> rename [‘(f : α -> num) _ = f _ ⇒ _ = _ ’] >>
  qexistsl_tac [‘λa. &(f a)’] >> simp[]
QED

Theorem countable_IMAGE_K0:
  countable (IMAGE (K ∅) A)
Proof
  irule finite_countable >> irule SUBSET_FINITE >> qexists‘{∅}’ >>
  simp[SUBSET_DEF, PULL_EXISTS]
QED

Theorem FsetA_countable:
  countable (FsetA v)
Proof
  rw[FsetA_def] >> rw[sumset_def] >> irule bigunion_countable >>
  rw[PULL_EXISTS, countable_IMAGE_K0] >> TRY (irule image_countable) >>
  simp[sumsetA_countable, sumsetB_countable] >>
  rw[pairset_def] >> irule bigunion_countable >>
  rw[PULL_EXISTS, countable_IMAGE_K0] >> TRY (irule image_countable) >>
  simp[pairsetB_countable] >>
  rw[listset_def] >> irule bigunion_countable >>
  rw[PULL_EXISTS, countable_IMAGE_K0] >> TRY (irule image_countable) >>
  simp[listsetA_countable] >>
  rw[pairset_def] >> irule bigunion_countable >>
  rw[PULL_EXISTS, countable_IMAGE_K0] >> TRY (irule image_countable) >>
  simp[pairsetB_countable, pairsetA_countable]
QED

Theorem FsetB_countable:
  countable (FsetB v)
Proof
  rw[FsetB_def] >> rw[sumset_def] >> irule bigunion_countable >>
  rw[PULL_EXISTS, countable_IMAGE_K0] >> TRY (irule image_countable) >>
  simp[sumsetA_countable, sumsetB_countable] >>
  rw[pairset_def,fmapset_def] >> irule bigunion_countable >>
  rw[PULL_EXISTS, countable_IMAGE_K0] >> TRY (irule image_countable) >>
  simp[pairsetB_countable, fmapsetA_countable] >>
  rw[listset_def] >> irule bigunion_countable >>
  rw[PULL_EXISTS, countable_IMAGE_K0] >> TRY (irule image_countable) >>
  simp[listsetA_countable] >>
  rw[pairset_def] >> irule bigunion_countable >>
  rw[PULL_EXISTS, countable_IMAGE_K0] >> TRY (irule image_countable) >>
  simp[pairsetB_countable, pairsetA_countable]
QED

Theorem bnd:
  ∀v : (β,α)F. FsetB v ≼ preds bnd ∧ ω ≤ bnd
Proof
  simp[bnd_def, cardleq_omega_countable] >> gen_tac >> irule FsetB_countable >>
  rw[]
QED

(* ----------------------------------------------------------------------
    start constructing algebra-level arguments
   ---------------------------------------------------------------------- *)

Definition Fin_def:
  Fin As Bs = { a : (α,β) F | FsetA a ⊆ As ∧ FsetB a ⊆ Bs }
End

Theorem starter:
  Fin 𝕌(:β) ∅ ≠ ∅
Proof
  simp[EXTENSION, Fin_def] >> qexists_tac ‘INL FEMPTY’ >>
  simp[FsetB_def, sumset_def, fmapset_def, sumsetA_def, sumsetB_def]
QED

Theorem Fset_exists:
  ∃x. FsetB x ≠ ∅
Proof
  simp[FsetB_def, sumTheory.EXISTS_SUM, sumset_def, EXISTS_PROD, pairset_def,
       sumsetA_def, sumsetB_def, pairsetA_def, pairsetB_def, listset_def] >>
  simp[Once listTheory.EXISTS_LIST] >>
  simp[EXISTS_PROD, EXISTS_OR_THM, pairset_def, pairsetA_def, pairsetB_def,
       INSERT_EQ_SING]
QED

Theorem map_eq_id:
  (∀a. a ∈ FsetA x ⇒ f a = a) ∧ (∀b. b ∈ FsetB x ⇒ g b = b) ⇒ Fmap f g x = x
Proof
  strip_tac >> ‘x = Fmap I I x’ by simp[mapID, I_EQ_IDABS] >>
  pop_assum SUBST1_TAC >> simp[mapO] >> irule Fmap_CONG >>
  simp[]
QED

Theorem IN_UNCURRY[simp]:
  (x,y) ∈ UNCURRY R ⇔ R x y
Proof
  simp[IN_DEF]
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
    ∀af. af ∈ Fin UNIV A ⇒ t (Fmap I h af) = h (s af)
End

Theorem homs_on_same_domain:
  hom h (A,s) (B,t) ∧ (∀a. a ∈ A ⇒ h' a = h a) ⇒ hom h' (A,s) (B,t)
Proof
  simp[hom_def, Fin_def] >> rw[] >>
  rename [‘FsetB af ⊆ A’] >>
  ‘s af ∈ A’ by gs[alg_def, Fin_def] >> simp[] >>
  ‘Fmap I h' af = Fmap I h af’ suffices_by simp[] >>
  irule Fmap_CONG >> simp[] >> metis_tac[SUBSET_DEF]
QED

Theorem homs_compose:
  hom f (A : α set,s : (δ,α)F -> α) (B : β set,t) ∧ hom g (B,t) (C : γ set,u) ⇒
  hom (g o f) (A,s) (C,u)
Proof
  csimp[hom_def] >> rw[] >> RULE_ASSUM_TAC GSYM >> simp[] >>
  ‘Fmap I f af ∈ Fin 𝕌(:δ) B ’
    by gs[Fin_def, SUBSET_DEF, PULL_EXISTS, FsetB_map] >>
  first_x_assum $ drule_then assume_tac >> simp[mapO]
QED

Theorem minset_ind:
  ∀P. (∀x. FsetB x ⊆ minset s ∧ (∀y. y ∈ FsetB x ⇒ P y) ⇒ P (s x)) ⇒
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
  ‘t (Fmap I h1 af) = t (Fmap I h2 af)’ suffices_by metis_tac[] >>
  ‘Fmap I h1 af = Fmap I h2 af’ suffices_by metis_tac[] >>
  irule Fmap_CONG >> simp[]
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
  exthm = prove(“∃i : (α,β) alg. alg i”,
           simp[EXISTS_PROD] >> qexists_tac ‘UNIV’ >>
           simp[alg_def]),
  ABS = "mkIx",
  REP = "dIx"};

Definition bigprod_def:
  bigprod : ((α,β)idx -> α, β) alg =
  ({ f | ∀i. f i ∈ FST (dIx i) },
   λfv i. SND (dIx i) $ Fmap I (λf. f i) fv)
End

Theorem bigprod_isalg:
  alg bigprod
Proof
  simp[bigprod_def, alg_def, FORALL_PROD, Fin_def] >> rpt strip_tac >>
  Cases_on ‘dIx i’ >> rename [‘dIx i = (A,s)’] >>
  ‘alg(A,s)’ by metis_tac[termP_term_REP] >> simp[] >> gs[alg_def] >>
  first_assum irule >>
  gs[Fin_def, SUBSET_DEF, PULL_EXISTS, FsetB_map] >> metis_tac[FST]
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
  strip_tac >> ho_match_mp_tac minset_ind >> gs[hom_def, Fin_def] >>
  rpt strip_tac >> RULE_ASSUM_TAC GSYM >> simp[] >>
  AP_TERM_TAC >> irule Fmap_CONG >> simp[]
QED

(* there are unique homs out of the minimised product of all α-algebras into
   α-algebras, but we have to find an α that is big enough that algebras over
   other types can be injected into them.

*)

(* Traytel's K function, from MSc thesis, p 15 *)

val KK_def = new_specification(
  "KK", ["KK"],
  ord_RECURSION |> Q.ISPEC ‘∅ : γ set’
                |> Q.SPEC ‘λx r. r ∪ { s(x) | FsetB x ⊆ r }’
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
  { s x | x | FsetB x ⊆ KK s ε } = KK s ε ⇒
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
           else BIGUNION (IMAGE (λa. { s fv | fv | FsetB fv ⊆ KK s a})
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
      ‘KK s a = BIGUNION (IMAGE (λa0. { s fv | fv | FsetB fv ⊆ KK s a0})
                          (preds a))’ by metis_tac[] >>
      gs[PULL_EXISTS] >> metis_tac[ordlt_TRANS]) >>
  rpt strip_tac >> rename [‘a < α’, ‘FsetB fv ⊆ KK s a’] >>
  qexists_tac ‘a⁺’ >> simp[KK_def] >> metis_tac[islimit_SUC_lt]
QED

Theorem sucbnd_suffices:
  ω ≤ (bd : γ ordinal) ∧ (∀x : (α,β)F. FsetB x ≼ preds bd) ⇒
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
      qabbrev_tac ‘B = sup (IMAGE g $ FsetB fv)’ >>
      ‘IMAGE g $ FsetB fv ≼ univ(:num + (γ + num -> bool))’
        by (irule IMAGE_cardleq_rwt >>
            first_assum (C (resolve_then (Pos hd) irule) cardleq_TRANS) >>
            resolve_then (Pos hd) irule preds_inj_univ cardleq_TRANS >>
            simp[cardleq_lteq, bumpUNIV_cardlt]) >>
      ‘∀a. a < B ⇔ ∃v. v ∈ FsetB fv ∧ a < g v’
        by simp[Abbr‘B’, sup_thm, PULL_EXISTS] >>
      qexists_tac ‘B⁺’ >> simp[KK_def] >> reverse conj_tac
      >- (simp[preds_ordSUC, INFINITE_cardleq_INSERT] >>
          simp[Abbr‘B’, preds_sup, dclose_BIGUNION] >>
          irule CARD_BIGUNION >>
          simp[IMAGE_cardleq_rwt, PULL_EXISTS]) >>
      ‘KK s B = BIGUNION (IMAGE (KK s) (IMAGE g (FsetB fv)))’
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
  ω ≤ (bd : γ ordinal) ∧ (∀x : (α,β)F. FsetB x ≼ preds bd) ⇒
  KK (s : (α,β)F -> β) (csuc bd) = minset s
Proof
  strip_tac >> drule_all_then (qspec_then ‘s’ assume_tac) sucbnd_suffices >>
  irule SUBSET_ANTISYM >> simp[KK_SUB_min] >>
  drule minsub_I_subalg >> simp[hom_def, mapID, SUBSET_DEF]
QED

Theorem nontrivialBs:
  (∃x:(α,β)F. FsetB x ≠ ∅) ⇒ ∀B. (B:β set) ≼ Fin 𝕌(:α) B
Proof
  rpt strip_tac >> simp[cardleq_def] >>
  qexists_tac ‘λb. Fmap I (K b) x’ >>
  simp[INJ_IFF, Fin_def, FsetB_map] >>
  conj_tac >- simp[SUBSET_DEF, PULL_EXISTS] >>
  simp[EQ_IMP_THM] >> rw[] >>
  pop_assum (mp_tac o Q.AP_TERM ‘FsetB’ ) >>
  simp[FsetB_map, EXTENSION] >> gs[GSYM MEMBER_NOT_EMPTY] >> metis_tac[]
QED

(* see Lemma 33 in ITP2014's
     "Cardinals in Isabelle/HOL" by Blanchette, Popescu and Traytel
 *)
Theorem CBDb:
  ω ≤ (bd : γ ordinal) ∧ (∀x:(α,β)F. FsetB x ≼ preds bd) ∧
  (∃x:(α,γ ordinal)F. FsetB x ≠ ∅)
⇒
  ∀B:β set. 𝟚 ≼ B ⇒ Fin 𝕌(:α) B ≼ B ** cardSUC (Fin 𝕌(:α) (preds bd))
Proof
  rpt strip_tac >>
  qabbrev_tac ‘kA = Fin 𝕌(:α) (preds bd) CROSS (B ** preds bd)’ >>
  qmatch_abbrev_tac ‘_ ≼ B ** k’ >>
  ‘kA ≼ B ** k’
    by (simp[Abbr‘k’, Abbr‘kA’] >> irule CARD_MUL2_ABSORB_LE >>
        simp[] >> rpt strip_tac
        >- (drule_all cardleq_TRANS >> simp[])
        >- (‘INFINITE (preds bd)’
              by (simp[FINITE_preds] >> rpt strip_tac >> gvs[]) >>
            ‘preds bd ≼ Fin 𝕌(:α) (preds bd)’ by metis_tac[nontrivialBs] >>
            metis_tac[CARD_LE_FINITE])
        >- (resolve_then (Pos last) irule CARD_LE_EXP cardleq_TRANS >>
            simp[]) >>
        irule set_exp_cardle_cong >> simp[] >> rpt strip_tac >>
        gvs[cardleq_empty] >>
        ‘preds bd ≼ Fin 𝕌(:α) (preds bd)’ by metis_tac[nontrivialBs] >>
        first_x_assum $ C (resolve_then (Pos hd) irule) cardleq_TRANS >>
        simp[])>>
  first_assum $ C (resolve_then (Pos last) irule) cardleq_TRANS >>
  qabbrev_tac ‘d = λ(y:('a,'c ordinal)F ,f). Fmap I f y’ >>
  simp[cardleq_def] >>
  irule_at Any (SRULE [PULL_EXISTS] SURJ_IMP_INJ) >> qexists_tac ‘d’ >>
  simp[SURJ_DEF] >> conj_tac
  >- (simp[FORALL_PROD,Abbr‘kA’, Abbr‘d’, Fin_def, FsetB_map, set_exp_def] >>
      rw[] >> simp[SUBSET_DEF, PULL_EXISTS] >> qx_gen_tac ‘b’ >> strip_tac >>
      ‘b ∈ preds bd’ by metis_tac[SUBSET_DEF] >> gs[] >> first_assum drule >>
      simp[PULL_EXISTS]) >>
  qx_gen_tac ‘vf’ >> strip_tac >>
  ‘?g. INJ g (FsetB vf) (preds bd)’ by metis_tac[cardleq_def] >>
  qabbrev_tac ‘y = Fmap I g vf’ >>
  ‘FsetB vf ⊆ B’ by gs[Fin_def] >>
  ‘?f. (!b. b ∈ FsetB vf ⇒ f (g b) = b) /\ (!bp. bp < bd ==> f bp ∈ B)’
    by (‘?be. be ∈ B’ by (simp[MEMBER_NOT_EMPTY] >>
                          strip_tac >> gvs[cardleq_empty]) >>
        qexists_tac ‘λbp. case some b. b IN FsetB vf /\ g b = bp of
                            NONE => be
                          | SOME b => b
                    ’ >> conj_tac >> simp[] >> rpt strip_tac
        >- (gs[INJ_IFF, SF CONJ_ss] >> csimp[]) >>
        DEEP_INTRO_TAC optionTheory.some_intro >> simp[] >>
        gs[SUBSET_DEF]) >>
  qexists_tac ‘(y, λbp. if bp ∈ preds bd then f bp else ARB)’ >>
  conj_tac
  >- (simp[Abbr‘kA’, Fin_def, Abbr‘y’, FsetB_map] >> conj_tac
      >- gs[INJ_IFF, SUBSET_DEF, PULL_EXISTS] >>
      simp[set_exp_def]) >>
  simp[Abbr‘d’, Abbr‘y’, mapO] >>
  simp[Once (GSYM mapID), SimpRHS] >> irule Fmap_CONG >> simp[] >>
  gs[INJ_IFF]
QED

Theorem preds_bd_lemma[local]:
  FsetB (gv  : (α,γ ordinal)F) ≠ ∅ ⇒
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
          simp[Once disjUNION_UNIV] >>
          resolve_then (Pos hd) irule CARD_LE_UNIV
                       CARD_LE_TRANS >>
          simp[CARD_LE_ADDL]) >>
      metis_tac[cardleq_lteq, CARD_LT_CONG, CARD_EQ_REFL]) >>
  DEEP_INTRO_TAC oleast_intro >> conj_tac
  >- (irule cardeq_ordinals_exist >>
      simp[Once disjUNION_UNIV] >>
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
  qexists_tac ‘Fmap I f’ >> simp[INJ_IFF, FsetB_map, FsetA_map] >>
  rpt strip_tac >- gs[SUBSET_DEF, PULL_EXISTS, INJ_IFF] >>
  simp[EQ_IMP_THM] >> strip_tac >>
  ‘Fmap I (LINV f s o f) x = Fmap I I x ∧ Fmap I (LINV f s o f) y = Fmap I I y’
    by (conj_tac >> irule Fmap_CONG >> drule_then assume_tac LINV_DEF >>
        gs[LINV_DEF, SUBSET_DEF]) >>
  qpat_x_assum ‘Fmap I f x = _’ (mp_tac o Q.AP_TERM ‘Fmap I (LINV f s)’) >>
  simp[mapO] >> simp[mapID, I_EQ_IDABS]
QED

Theorem cardADD2[local]:
  s ≼ s +_c 𝟚
Proof
  simp[CARD_LE_ADDR]
QED

Theorem alg_cardinality_bound:
  ω ≤ (bd : γ ordinal) ∧ (∀x:(α,β+bool)F. FsetB x ≼ preds bd) ∧
  (∃x:(α,γ ordinal)F. FsetB x ≠ ∅) ⇒
  KK (s:(α,β)F -> β) (csuc bd) ≼ 𝟚 ** (cardSUC $ Fin 𝕌(:α) (preds bd))
Proof
  strip_tac >> rename [‘FsetB gv ≠ ∅’] >>
  qmatch_abbrev_tac ‘_ ≼ 𝟚 ** BD’ >>
  ‘INFINITE BD’
    by (strip_tac >> gs[Abbr‘BD’] >>
        ‘preds bd ≼ Fin 𝕌(:α) (preds bd)’ by metis_tac[nontrivialBs] >>
        ‘FINITE (preds bd)’ by metis_tac[CARD_LE_FINITE] >>
        gs[FINITE_preds]) >>
  ‘BD ≠ ∅’ by simp[Abbr‘BD’] >>
  ‘∀i. i < csuc bd ⇒ KK s i ≼ 𝟚 ** BD’
    suffices_by (strip_tac >> simp[csuc_is_nonzero_limit, KK_def] >>
                 irule CARD_BIGUNION >> simp[PULL_EXISTS] >>
                 rpt strip_tac >> irule IMAGE_cardleq_rwt >>
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
  ‘{ s fv | fv | FsetB fv ⊆ KK s j} = IMAGE s (Fin 𝕌(:α) (KK s j))’
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
        KKbnd_EQ_minset |> INST_TYPE [“:γ” |-> “:α”]
                        |> Q.INST [‘bd’ |-> ‘bnd’]
                        |> SRULE [bnd]

Theorem inst_bound =
        alg_cardinality_bound
          |> INST_TYPE [“:γ” |-> “:α”]
          |> Q.INST [‘bd’ |-> ‘bnd’]
          |> SRULE [bnd, Fset_exists, KK_EQ_MINSET]

Type algty0[pp] = (#1 $ dom_rng $ type_of $ rand $ concl inst_bound)

Theorem copy_alg_back:
  (A:α set) ≼ (B:β set) ∧ alg (A, s : (γ,α)F -> α) ⇒
  ∃(B0:β set) s' h j.
    hom h (B0,s') (A,s) ∧ hom j (A,s) (B0,s') ∧
    (∀a. a ∈ A ⇒ h (j a) = a) ∧ (∀b. b ∈ B0 ⇒ j (h b) = b)
Proof
  simp[cardleq_def] >> strip_tac >> rename [‘INJ h0 A B’] >>
  qexistsl_tac [‘IMAGE h0 A’, ‘λbv. h0 $ s $ Fmap I (LINV h0 A) bv’,
                ‘LINV h0 A’, ‘h0’] >>
  csimp[hom_def, PULL_EXISTS] >>
  drule_then assume_tac LINV_DEF >> rw[]
  >- (gs[alg_def, Fin_def, SUBSET_DEF] >> rw[] >>
      irule_at Any EQ_REFL >> first_assum irule >>
      simp[FsetB_map, PULL_EXISTS] >> rw[] >> first_assum drule >>
      simp[PULL_EXISTS])
  >- (‘s (Fmap I (LINV h0 A) bv) ∈ A’
        by (gs[alg_def, Fin_def] >> first_assum irule >>
            gs[FsetB_map, SUBSET_DEF, PULL_EXISTS] >> rw[] >>
            first_assum drule >> simp[PULL_EXISTS]) >>
      simp[] >> AP_TERM_TAC >> irule Fmap_CONG >> simp[] >>
      gs[Fin_def, SUBSET_DEF])
  >- (simp[mapO] >> rename [‘av ∈ Fin UNIV A’] >>
      ‘Fmap I (LINV h0 A o h0) av = Fmap I I av’
        suffices_by simp[I_EQ_IDABS, mapID] >>
      irule Fmap_CONG >> gs[Fin_def, SUBSET_DEF])
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
  simp[] >> rw[] >> AP_TERM_TAC >> irule Fmap_CONG >> simp[] >>
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
  alg (A,s) ⇒ alg (Fin 𝕌(:β) A, Fmap I s)
Proof
  strip_tac >>
  simp[alg_def, Fin_def, SUBSET_DEF, FsetB_map, PULL_EXISTS] >> rw[] >>
  rename [‘s vf ∈ A’, ‘vf ∈ FsetB vff’] >>
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
  irule Fmap_CONG >> gs[arbify_def, SUBSET_DEF, Fin_def]
QED

Theorem iso0:
  BIJ Cons (Fin 𝕌(:α) IAlg) IAlg
Proof
  ‘alg (IAlg, Cons : (α,α algty)F -> α algty)’ by simp[IAlg_isalg] >>
  drule_then assume_tac alg_Fin >>
  drule_then assume_tac initiality0 >>
  gs[EXISTS_UNIQUE_ALT] >>
  rename[‘hom _ (IAlg,Cons) _ ∧ _ ⇔ H = _’] >>
  ‘hom H (IAlg,Cons) (Fin 𝕌(:α) IAlg, Fmap I Cons)’ by metis_tac[] >>
  ‘hom Cons (Fin 𝕌(:α) IAlg, Fmap I Cons) (IAlg,Cons)’
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
      ‘H (Cons a) = Fmap I (Cons o H) a’ by simp[] >> pop_assum SUBST1_TAC >>
      ‘Fmap I (Cons o H) a = Fmap I I a’ suffices_by simp[I_EQ_IDABS, mapID] >>
      irule Fmap_CONG >> gs[Fin_def, SUBSET_DEF]) >>
  pop_assum mp_tac >> simp[Once FUN_EQ_THM, arbify_def] >> metis_tac[]
QED

val itype = newtypeTools.rich_new_type{
  tyname = "nty", exthm = inhabited,
  ABS = "nty_ABS", REP = "nty_REP"
  }

Definition NCONS_def:
  NCONS (x : (α, α nty)F) = nty_ABS $ Cons $ Fmap I nty_REP x
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
  simp[FsetB_map, PULL_EXISTS] >> simp[IN_DEF, #termP_term_REP itype]
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
                   |> Q.SPEC ‘NCONS o Fmap f I’
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
  (∀av. FsetB av ⊆ IAlg ⇒ P av) ⇔
  (∀n. P (Fmap I nty_REP n))
Proof
  rw[EQ_IMP_THM]
  >- (pop_assum irule >> simp[FsetB_map, SUBSET_DEF, PULL_EXISTS] >>
      simp[IN_DEF, #termP_term_REP itype]) >>
  first_x_assum $ qspec_then ‘Fmap I nty_ABS av’ mp_tac >>
  simp[mapO] >>
  ‘Fmap I (nty_REP o nty_ABS) av = av’ suffices_by simp[] >>
  irule map_eq_id >> gs[SUBSET_DEF, #repabs_pseudo_id itype, IN_DEF]
QED

Theorem IN_FsetB:
  (∀y. y ∈ FsetB x ⇒ Q (nty_ABS y)) ⇔ x ∈ Fin 𝕌(:α) (Q o nty_ABS)
Proof
  simp[Fin_def, SUBSET_DEF] >> simp[IN_DEF]
QED

Theorem Cons_NCONS:
  FsetB x ⊆ IAlg ⇒
  Cons x = nty_REP (NCONS (Fmap I nty_ABS x))
Proof
  simp[NCONS_def, mapO] >> strip_tac >>
  ‘Fmap I (nty_REP o nty_ABS) x = x’
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

Theorem FsetB_applied:
  FsetB x v ⇔ v ∈ FsetB x
Proof
  simp[IN_DEF]
QED

Theorem IND =
        minset_ind |> Q.GEN ‘s’
                   |> Q.ISPEC ‘Cons’
                   |> SRULE [minset_Cons]
                   |> Q.SPEC ‘λia. Q (nty_ABS ia)’
                   |> SRULE[ALL_Ialg, #absrep_id itype, IN_FsetB, Cons_NCONS]
                   |> SRULE[GSYM AND_IMP_INTRO, ALL_Ialgv, mapO, Fin_def,
                            FsetB_map, abs_o_rep, I_EQ_IDABS, mapID]
                   |> SRULE[SUBSET_DEF, PULL_EXISTS, IN_DEF, #absrep_id itype]
                   |> SRULE [FsetB_applied]

Theorem NCONS_comp:
  NCONS = nty_ABS o Cons o Fmap I nty_REP
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
  >- simp[Fin_def, FsetB_map, SUBSET_DEF, PULL_EXISTS, IN_DEF,
          #termP_term_REP itype] >>
  qexists_tac ‘Fmap I nty_ABS’ >> simp[mapO, abs_o_rep, I_EQ_IDABS, mapID] >>
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
  irule Fmap_CONG >> simp[]
QED

val SET_def = new_specification (
  "SET_def", ["SET"],
  initiality |> Q.ISPEC ‘Fset $= I : (β, β set)F -> β set’
             |> SRULE[Fset_Fmap']
             |> SRULE[EXISTS_UNIQUE_THM] |> cj 1);

Theorem SET_MAP:
  ∀n. SET (MAP f n) = IMAGE f (SET n)
Proof
  ho_match_mp_tac IND >>
  simp[SET_def, MAP_def, Fset_Fmap', IMAGE_Fset, o_DEF] >>
  rw[] >>
  irule Fset_CONG  >> simp[]
QED

Theorem MAP_CONG:
  ∀n. (∀a. a ∈ SET n ⇒ f a = g a) ⇒ MAP f n = MAP g n
Proof
  ho_match_mp_tac IND >>
  simp[MAP_def, SET_def, PULL_EXISTS, NCONS_11] >> rw[] >>
  irule Fmap_CONG >> rw[] >> gvs[Fset_def,PULL_EXISTS] >> rw[] >>
  first_x_assum irule >> metis_tac[]
QED

Definition SUMSPLITL_def:
  SUMSPLITL f x = f (INL x)
End

Theorem FORALL_SUMALG:
  (∀t : α + β -> γ. P t) ⇔
  (∀(t1: α -> γ) (t2 : β -> γ). P (λs. case s of INL x => t1 x
                                              | INR y => t2 y))
Proof
  simp[EQ_IMP_THM] >> rpt strip_tac >>
  first_x_assum $ qspecl_then [‘t o INL’, ‘t o INR’] mp_tac>>
  qmatch_abbrev_tac ‘P x ⇒ P y’ >> ‘x = y’ suffices_by simp[] >>
  simp[Abbr‘x’, Abbr‘y’, FUN_EQ_THM, sumTheory.FORALL_SUM]
QED

Theorem FORALL_PAIRALG:
  (∀t: α # β -> γ. P t) ⇔ (∀t: α -> β -> γ. P (UNCURRY t))
Proof
  simp[EQ_IMP_THM] >> disch_then $ qspec_then ‘CURRY f’ (mp_tac o Q.GEN ‘f’) >>
  simp[UNCURRY_CURRY_THM]
QED

Definition C1_def:
  C1 x = NCONS (INL x)
End

Definition C2_def:
  C2 a b = NCONS (INR(a,b))
End

Theorem better_initiality =
        initiality |> SRULE [sumTheory.FORALL_SUM, Fmap_def, FORALL_SUMALG]
                   |> SRULE [FORALL_PROD, FORALL_PAIRALG, GSYM C1_def,
                             GSYM C2_def]

Theorem better_ind =
        IND |> SRULE [sumTheory.FORALL_SUM, FsetB_def, PULL_EXISTS, sumset_def,
                      sumset_def, FORALL_PROD, pairsetB_def, sumsetA_def,
                      GSYM C1_def, GSYM C2_def, fmapset_def, sumsetB_def,
                      pairset_def, listset_def]

Theorem SET_C1 =
        SCONV[C1_def, SET_def, Fset_def, FsetA_def, FsetB_def, sumset_def,
              sumsetA_def, sumsetB_def, fmapset_def] “SET (C1 fm)”

Theorem BIGUNION_set[local,simp]:
  BIGUNION (IMAGE f (set l)) = BIGUNION { f e | MEM e l }
Proof
  simp[Once EXTENSION, PULL_EXISTS]
QED

Theorem IMAGE_GSPEC[local,simp]:
  IMAGE f (GSPEC (λx. (g x, P x))) = GSPEC (λx. (f (g x), P x))
Proof
  simp[EXTENSION, PULL_EXISTS]
QED


Theorem SET_C2:
  SET (C2 n evs) = { a | ∃v. MEM (a,v) evs } ∪
                   { a | ∃a0 v. MEM (a0,v) evs ∧ a ∈ SET v }
Proof
  simp[C2_def, SET_def, Fset_def, FsetA_def, FsetB_def, sumset_def, sumsetA_def,
       sumsetB_def, pairset_def, pairsetA_def, pairsetB_def, listset_def] >>
  ONCE_REWRITE_TAC[EXTENSION] >>
  simp[PULL_EXISTS, EXISTS_PROD, pairsetA_def, pairsetB_def] >>
  metis_tac[]
QED

(* gives bnd, but seems non-trivial to get automatically *)
Theorem FINITE_SET:
  ∀n. FINITE (SET n)
Proof
  ho_match_mp_tac better_ind>> simp[SET_C1, SET_C2, PULL_EXISTS] >> rw[] >~
  [‘FINITE {a | ∃v. MEM (a,v) l}’]
  >- (irule SUBSET_FINITE >> qexists ‘set (MAP FST l)’ >>
      simp[SUBSET_DEF, PULL_EXISTS, listTheory.MEM_MAP, EXISTS_PROD]) >>
  rename [‘FINITE {a | ∃a0 v. MEM (a0,v) l ∧ a ∈ SET v}’] >>
  irule SUBSET_FINITE >>
  qexists ‘BIGUNION (IMAGE SET (set (MAP SND l)))’ >>
  simp[SUBSET_DEF, PULL_EXISTS, listTheory.MEM_MAP, FORALL_PROD, EXISTS_PROD] >>
  metis_tac[]
QED
