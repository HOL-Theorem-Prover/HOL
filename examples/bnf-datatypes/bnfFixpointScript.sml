Theory bnfFixpoint
Ancestors
  hol bnfPrelims pred_set cardinal ordinal ordinalBasic combin pair
Libs
  HolKernel bnfBase bnfLib

(* ----------------------------------------------------------------------
    Construct the initial algebra of a functor whose BNF structure came
    out of bnfLib.deriveBNF, rather than by hand.  The functor here is
    the one behind

        Datatype: mylist = Nil | Cons 'b1 mylist

    but nothing below depends on which functor it is: once Fmap and Fset
    are constants with the BNF laws attached, the construction only ever
    appeals to those laws.  That is what makes it something an SML
    function can replay for any functor.
   ---------------------------------------------------------------------- *)

val Fty = “:one + 'b1 # 'a”
val bnf = bnfLib.deriveBNF (bnfBase.fullDB()) Fty

val fvar = mk_var("f", alpha --> beta)
fun SRULE ths = SIMP_RULE (srw_ss()) ths
val FTY = ty_antiq Fty
val BTY = #1 (dom_rng (type_of (#bnd bnf)))   (* bnd is univ(:BTY) *)

(* the functor's type with the recursion argument at ty *)
fun FatTy ty = type_subst [alpha |-> ty] Fty
fun FatTY ty = ty_antiq (FatTy ty)
val FORD = FatTY “:'g ordinal”
val FTYB = FatTY beta
val FTYC = FatTY gamma
val FSUM = FatTY “:'a + bool”

(* turn a point-free law into the pointwise form the construction wants *)
fun pointwise th =
    SPEC_ALL (PURE_REWRITE_RULE [combinTheory.o_THM, combinTheory.I_THM]
                (CONV_RULE (ONCE_REWRITE_CONV [FUN_EQ_THM]) th))

Definition Fmap_def:
  Fmap ^fvar = ^(#mkmap bnf fvar)
End

Definition Fset_def:
  Fset = ^(#set bnf)
End

(* ----------------------------------------------------------------------
    the BNF laws, restated for the constants
   ---------------------------------------------------------------------- *)

Theorem FmapID:
  Fmap I = I
Proof
  REWRITE_TAC[Fmap_def] >> MATCH_ACCEPT_TAC (#mapID bnf)
QED

Theorem FmapID' = pointwise FmapID

Theorem FmapO:
  Fmap f o Fmap g = Fmap (f o g)
Proof
  REWRITE_TAC[Fmap_def] >> MATCH_ACCEPT_TAC (#mapO bnf)
QED

Theorem FmapO' = pointwise FmapO

Theorem FsetMapo:
  Fset o Fmap f = IMAGE f o Fset
Proof
  REWRITE_TAC[Fmap_def, Fset_def] >> MATCH_ACCEPT_TAC (#mapIMAGE bnf)
QED

Theorem FsetMap = pointwise FsetMapo

Theorem FmapCONG:
  (∀a. a ∈ Fset x ⇒ f a = g a) ⇒ Fmap f x = Fmap g x
Proof
  REWRITE_TAC[Fmap_def, Fset_def] >> MATCH_ACCEPT_TAC (#mapCONG bnf)
QED

Theorem Fmap_eq_id:
  (∀a. a ∈ Fset x ⇒ f a = a) ⇒ Fmap f x = x
Proof
  strip_tac >> CONV_TAC (RAND_CONV (REWR_CONV (GSYM FmapID'))) >>
  irule FmapCONG >> simp[]
QED

Theorem Fset_bounded:
  ∀x. Fset x ≼ ^(#bnd bnf)
Proof
  REWRITE_TAC[Fset_def] >> MATCH_ACCEPT_TAC (#bndthm bnf)
QED

Theorem Fwitness:
  Fset ^(#1 (valOf (#wit bnf))) = ∅
Proof
  REWRITE_TAC[Fset_def] >> MATCH_ACCEPT_TAC (#2 (valOf (#wit bnf)))
QED

Theorem Fset_exists:
  ∃x:^FTY. Fset x ≠ ∅
Proof
  REWRITE_TAC[Fset_def] >> EXISTS_TAC (#1 (valOf (#nontrivial bnf))) >>
  ACCEPT_TAC (#2 (valOf (#nontrivial bnf)))
QED

(* ----------------------------------------------------------------------
    F-algebras.

    From here on the development is exactly bnfAlgebraScript's, with
    ‘mapF I’ read as Fmap and ‘setBF’ as Fset; the α argument of that
    file's two-argument functor is baked into F's type here, so Fin
    needs only one set argument.
   ---------------------------------------------------------------------- *)

Definition Fin_def:
  Fin As = { a : ^FTY | Fset a ⊆ As }
End

Theorem IN_Fin[simp]:
  a ∈ Fin As ⇔ Fset a ⊆ As
Proof
  simp[Fin_def]
QED

Theorem Fin_UNIV[simp]:
  Fin UNIV = UNIV
Proof
  simp[EXTENSION]
QED

Theorem starter:
  Fin ∅ ≠ ∅
Proof
  simp[GSYM MEMBER_NOT_EMPTY] >> metis_tac[Fwitness, SUBSET_REFL]
QED

Definition alg_def:
  alg (A : 'a set, s : ^FTY -> 'a) ⇔ ∀x. x ∈ Fin A ⇒ s x ∈ A
End

Theorem alg_UNIV[simp]:
  alg (UNIV, s)
Proof
  simp[alg_def]
QED

Theorem alg_nonempty:
  alg(A, s : ^FTY -> 'a) ⇒ A ≠ ∅
Proof
  rpt strip_tac >> gvs[alg_def] >>
  metis_tac[Fwitness, SUBSET_REFL, NOT_IN_EMPTY]
QED

Definition minset_def:
  minset (s : ^FTY -> 'a) = BIGINTER { B | alg(B,s) }
End

Theorem minset_is_alg[simp]:
  alg (minset s, s)
Proof
  simp[minset_def, alg_def, SUBSET_BIGINTER]
QED

Theorem IN_minset:
  x ∈ minset s ⇔ ∀A. alg(A,s) ⇒ x ∈ A
Proof
  simp[minset_def]
QED

Definition hom_def:
  hom h (A,s) (B,t) ⇔
    alg(A,s) ∧ alg(B,t) ∧ (∀a. a ∈ A ⇒ h a ∈ B) ∧
    ∀af. af ∈ Fin A ⇒ t (Fmap h af) = h (s af)
End

Theorem homs_on_same_domain:
  hom h (A,s) (B,t) ∧ (∀a. a ∈ A ⇒ h' a = h a) ⇒ hom h' (A,s) (B,t)
Proof
  simp[hom_def] >> rw[] >>
  ‘s af ∈ A’ by gs[alg_def] >> simp[] >>
  ‘Fmap h' af = Fmap h af’ suffices_by simp[] >>
  irule FmapCONG >> simp[] >> metis_tac[SUBSET_DEF]
QED

Theorem homs_compose:
  hom f (A : 'a set, s) (B : 'b set,t) ∧ hom g (B,t) (C : 'c set,u) ⇒
  hom (g o f) (A,s) (C,u)
Proof
  csimp[hom_def] >> rw[] >> RULE_ASSUM_TAC GSYM >> simp[] >>
  ‘Fmap f af ∈ Fin B’
    by gs[FsetMap, SUBSET_DEF, PULL_EXISTS] >>
  first_x_assum $ drule_then assume_tac >> gs[FmapO']
QED

Theorem minset_ind:
  ∀P. (∀x. Fset x ⊆ minset s ∧ (∀y. y ∈ Fset x ⇒ P y) ⇒ P (s x)) ⇒
      ∀x. x ∈ minset s ⇒ P x
Proof
  gen_tac >> strip_tac >>
  ‘minset s ⊆ P INTER minset s’ suffices_by simp[SUBSET_DEF, IN_DEF] >>
  simp[minset_def, SimpL “$SUBSET”] >> irule BIGINTER_SUBSET >>
  qexists_tac ‘P INTER minset s’ >>
  simp[alg_def, SUBSET_DEF] >> rw[]
  >- gs[IN_DEF, SUBSET_DEF] >>
  ntac 2 (last_x_assum (K ALL_TAC)) >>
  gs[alg_def, SUBSET_DEF, IN_minset]
QED

Theorem minset_ind':
  ∀P. (∀x. (∀y. y ∈ Fset x ⇒ y ∈ minset s ∧ P y) ⇒ P (s x)) ⇒
      ∀x. x ∈ minset s ⇒ P x
Proof
  metis_tac[minset_ind, SUBSET_DEF]
QED

Theorem minset_unique_homs:
  hom h1 (minset s, s) (B,t) ∧ hom h2 (minset s, s) (B,t) ⇒
  ∀a. a ∈ minset s ⇒ h1 a = h2 a
Proof
  strip_tac >> ho_match_mp_tac minset_ind' >> gs[hom_def] >>
  rpt strip_tac >> RULE_ASSUM_TAC GSYM >> simp[] >> gs[SUBSET_DEF] >>
  AP_TERM_TAC >> irule FmapCONG >> simp[]
QED

Definition subalg_def:
  subalg (A,s) (B,t) ⇔ alg(A,s) ∧ alg (B,t) ∧
                       (∀af. af ∈ Fin A ⇒ s af = t af) ∧ A ⊆ B
End

Theorem subalgs_preserve_homs:
  subalg A1 A2 ∧ hom f A2 C ⇒ hom f A1 C
Proof
  Cases_on ‘A1’ >> Cases_on ‘A2’ >> Cases_on ‘C’ >>
  simp[hom_def, subalg_def] >> metis_tac[SUBSET_DEF]
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
  simp[hom_def, FmapID, subalg_def, SUBSET_DEF]
QED

(* ----------------------------------------------------------------------
    The product of all algebras over a fixed carrier type.

    bnfAlgebraScript indexes this product by a new type of algebras; a
    pair that isn't an algebra is coerced to one instead, which keeps the
    construction free of type definitions other than the datatype itself.
   ---------------------------------------------------------------------- *)

Definition mkalg_def:
  mkalg (p : 'a set # (^FTY -> 'a)) = if alg p then p else (UNIV, SND p)
End

Theorem mkalg_isalg[simp]:
  alg (mkalg p)
Proof
  rw[mkalg_def] >> Cases_on ‘p’ >> simp[]
QED

Theorem mkalg_id:
  alg p ⇒ mkalg p = p
Proof
  simp[mkalg_def]
QED

(* the two components of the pair must be pinned to the same instance of
   the functor, or bigprod ends up a constant with type variables that
   nothing later can determine *)
val idxty = pairSyntax.mk_prod(alpha --> bool, Fty --> alpha)
val IDXTY = ty_antiq idxty
val carrierty = idxty --> alpha
val CARRIER = ty_antiq carrierty
val FCARRIER = FatTY carrierty

Definition bigprod_def:
  bigprod = ({ f : ^CARRIER | ∀i. f i ∈ FST (mkalg i) },
             λ(fv : ^FCARRIER) (i : ^IDXTY).
               SND (mkalg i) (Fmap (λf. f i) fv))
End

Theorem bigprod_isalg[simp]:
  alg bigprod
Proof
  simp[bigprod_def, alg_def] >> rpt strip_tac >>
  Cases_on ‘mkalg i’ >> rename [‘mkalg i = (A,s)’] >>
  ‘alg(A,s)’ by metis_tac[mkalg_isalg] >> simp[] >> gs[alg_def] >>
  first_assum irule >>
  gs[FsetMap, SUBSET_DEF, PULL_EXISTS] >> metis_tac[FST]
QED

Theorem bigprod_proj:
  alg (A,s) ⇒ hom (λf. f (A,s)) bigprod (A,s)
Proof
  simp[hom_def, bigprod_def] >> rpt strip_tac
  >- metis_tac[bigprod_isalg, bigprod_def]
  >- (‘mkalg (A,s) = (A,s)’ by metis_tac[mkalg_id] >>
      first_x_assum $ qspec_then ‘(A,s)’ mp_tac >> simp[]) >>
  ‘mkalg (A,s) = (A,s)’ by metis_tac[mkalg_id] >> simp[]
QED

(* ----------------------------------------------------------------------
    The bound as an ordinal.  bnfAlgebraScript carries ‘ω ≤ bd’ and
    ‘!x. setBF x <<= preds bd’ as hypotheses on every cardinality lemma;
    here the bound is known, so bnd is fixed once and the lemmas can
    mention it directly.
   ---------------------------------------------------------------------- *)

val bnd_def = new_specification(
  "bnd_def", ["bnd"],
  MATCH_MP cardeq_ordinals_exist
           (INST_TYPE [alpha |-> “:num”, beta |-> BTY] UNIV_CARD_LE_ADDL))

Theorem bnd_INFINITE[simp]:
  INFINITE (preds bnd)
Proof
  ‘preds bnd ≈ ^(#bnd bnf)’ by MATCH_ACCEPT_TAC bnd_def >>
  metis_tac[CARD_FINITE_CONG, #bndINFINITE bnf]
QED

Theorem omega_le_bnd[simp]:
  ω ≤ bnd
Proof
  irule omega_LEQ_INFINITE_preds >> simp[]
QED

Theorem Fset_cle_bnd:
  ∀x:^FTY. Fset x ≼ preds bnd
Proof
  gen_tac >> ‘Fset x ≈ Fset x’ by REWRITE_TAC[cardeq_REFL] >>
  ‘preds bnd ≈ ^(#bnd bnf)’ by MATCH_ACCEPT_TAC bnd_def >>
  dxrule_then (dxrule_then irule) (iffRL CARD_LE_CONG) >>
  MATCH_ACCEPT_TAC (GEN_ALL Fset_bounded)
QED

(* ----------------------------------------------------------------------
    Traytel's K function (MSc thesis, p 15): iterate the algebra's
    operation through the ordinals until it closes off.
   ---------------------------------------------------------------------- *)

val KK_def = new_specification(
  "KK", ["KK"],
  ord_RECURSION |> Q.ISPEC ‘∅ : 'c set’
                |> Q.SPEC ‘λx r. r ∪ { s(x) | Fset x ⊆ r }’
                |> Q.SPEC ‘λx rs. BIGUNION rs’
                |> SRULE[]
                |> Q.GEN ‘s’ |> CONV_RULE SKOLEM_CONV);

Theorem KK_mono:
  ∀b a. a < b ⇒ KK s a ⊆ KK s b
Proof
  ho_match_mp_tac simple_ord_induction >>
  simp[KK_def, ordlt_SUC_DISCRETE, DISJ_IMP_THM, FORALL_AND_THM] >>
  rw[] >- metis_tac[IN_UNION, SUBSET_DEF] >>
  gs[omax_NONE] >>
  last_x_assum $ drule_then strip_assume_tac >>
  first_x_assum $ drule_all_then assume_tac >>
  irule SUBSET_BIGUNION_I >> simp[]
QED

Theorem KK_mono_LE:
  ∀a b. a ≤ b ⇒ KK s a ⊆ KK s b
Proof
  metis_tac[SUBSET_REFL, KK_mono, ordle_lteq]
QED

Theorem KK_SUB_min:
  ∀a. KK s a ⊆ minset s
Proof
  ho_match_mp_tac simple_ord_induction >> simp[KK_def] >> rw[]
  >- (simp[SUBSET_DEF, PULL_EXISTS] >> rpt strip_tac >>
      ‘alg (minset s, s)’ by simp[] >>
      gs[alg_def, Excl "minset_is_alg"] >>
      metis_tac[SUBSET_DEF]) >>
  simp[SUBSET_DEF, PULL_EXISTS] >> metis_tac[SUBSET_DEF]
QED

Theorem KK_fixp_is_alg:
  { s x | x | Fset x ⊆ KK s e } = KK s e ⇒ alg(KK s e, s)
Proof
  rw[alg_def] >> gs[EXTENSION] >> metis_tac[]
QED

Theorem KK_sup:
  ords ≼ 𝕌(:num + 'g) ⇒
  KK s (sup ords : 'g ordinal) = BIGUNION (IMAGE (KK s) ords)
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
      simp[SUBSET_DEF, PULL_EXISTS, sup_thm] >> rw[] >>
      metis_tac[SUBSET_DEF, KK_mono]) >>
  gs[omax_SOME] >> rename [‘_ ≤ mx’, ‘mx ∈ ords’] >>
  ‘sup ords = mx’ by metis_tac[sup_eq_max] >> simp[] >>
  irule SUBSET_ANTISYM >> simp[SUBSET_DEF, PULL_EXISTS] >> rw[]
  >- metis_tac[] >>
  metis_tac[KK_mono_LE, SUBSET_DEF]
QED

Theorem KK_preds_subset:
  BIGUNION (IMAGE (KK s) (preds a)) ⊆ KK s a
Proof
  qid_spec_tac ‘a’ >> ho_match_mp_tac simple_ord_induction >>
  rw[]
  >- (simp[KK_def, preds_ordSUC] >> irule SUBSET_TRANS >> goal_assum drule >>
      simp[]) >>
  simp[KK_def]
QED

Theorem KK_thm:
  KK s a = if a = 0 then ∅
           else BIGUNION (IMAGE (λb. { s fv | fv | Fset fv ⊆ KK s b})
                          (preds a))
Proof
  qid_spec_tac ‘a’ >> ho_match_mp_tac simple_ord_induction >>
  rw[]
  >- simp[KK_def]
  >- (simp[preds_nat] >> ‘count 1 = {0}’ by simp[EXTENSION] >>
      simp[KK_def, GSYM ORD_ONE, Excl "ORD_ONE"])
  >- (qpat_x_assum ‘KK _ _ = BIGUNION _’ (assume_tac o SYM) >>
      simp[KK_def, preds_ordSUC, UNION_COMM]) >>
  pop_assum (assume_tac o GSYM) >>
  simp[KK_def] >> irule SUBSET_ANTISYM >> conj_tac >>
  simp[Once SUBSET_DEF, PULL_EXISTS]
  >- (rpt strip_tac >> rename [‘v ∈ KK s b’] >>
      ‘b ≠ 0’ by (strip_tac >> gs[KK_def]) >>
      ‘KK s b = BIGUNION (IMAGE (λb0. { s fv | fv | Fset fv ⊆ KK s b0})
                          (preds b))’ by metis_tac[] >>
      gs[PULL_EXISTS] >> metis_tac[ordlt_TRANS]) >>
  rpt strip_tac >> rename [‘b < a’, ‘Fset fv ⊆ KK s b’] >>
  qexists_tac ‘b⁺’ >> simp[KK_def] >> metis_tac[islimit_SUC_lt]
QED

(* ----------------------------------------------------------------------
    The cardinality argument: the iteration closes off by csuc bnd, and
    what it produces is small enough to fit inside a fixed type.
   ---------------------------------------------------------------------- *)

Theorem sucbnd_suffices:
  ω ≤ (bd : 'g ordinal) ∧ (∀x : ^FTY. Fset x ≼ preds bd) ⇒
  alg (KK (s : ^FTY -> 'a) (csuc bd), s)
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
      qabbrev_tac ‘B = sup (IMAGE g $ Fset fv)’ >>
      ‘IMAGE g $ Fset fv ≼ univ(:num + ('g + num -> bool))’
        by (irule IMAGE_cardleq_rwt >>
            first_assum (C (resolve_then (Pos hd) irule) cardleq_TRANS) >>
            resolve_then (Pos hd) irule preds_inj_univ cardleq_TRANS >>
            simp[cardleq_lteq, bumpUNIV_cardlt]) >>
      ‘∀a. a < B ⇔ ∃v. v ∈ Fset fv ∧ a < g v’
        by simp[Abbr‘B’, sup_thm, PULL_EXISTS] >>
      qexists_tac ‘B⁺’ >> simp[KK_def] >> reverse conj_tac
      >- (simp[preds_ordSUC, INFINITE_cardleq_INSERT] >>
          simp[Abbr‘B’, preds_sup, dclose_BIGUNION] >>
          irule CARD_BIGUNION >>
          simp[IMAGE_cardleq_rwt, PULL_EXISTS]) >>
      ‘KK s B = BIGUNION (IMAGE (KK s) (IMAGE g (Fset fv)))’
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
  ω ≤ (bd : 'g ordinal) ∧ (∀x : ^FTY. Fset x ≼ preds bd) ⇒
  KK (s : ^FTY -> 'a) (csuc bd) = minset s
Proof
  strip_tac >> drule_all_then (qspec_then ‘s’ assume_tac) sucbnd_suffices >>
  irule SUBSET_ANTISYM >> simp[KK_SUB_min] >>
  drule minsub_I_subalg >> simp[hom_def, FmapID, SUBSET_DEF]
QED

(* Because F is not constant, an algebra's carrier is no bigger than the
   collection of F-values over it.  Fset_exists is a theorem rather than
   a hypothesis, which keeps the functor's other type arguments from
   drifting apart in the lemmas that use this. *)
Theorem nontrivialBs:
  ∀B. (B:'a set) ≼ (Fin B : ^FTY set)
Proof
  strip_assume_tac Fset_exists >> rpt strip_tac >> simp[cardleq_def] >>
  EXISTS_TAC “λb:'a. Fmap (K b) (x : ^FTY)” >> simp[INJ_IFF, FsetMap] >>
  conj_tac >- simp[SUBSET_DEF, PULL_EXISTS] >>
  simp[EQ_IMP_THM] >> rw[] >>
  pop_assum (mp_tac o Q.AP_TERM ‘Fset’) >>
  simp[FsetMap, EXTENSION] >> gs[GSYM MEMBER_NOT_EMPTY] >> metis_tac[]
QED

Overload "𝟙" = “{()}”

(* see Lemma 33 in ITP2014's
     "Cardinals in Isabelle/HOL" by Blanchette, Popescu and Traytel *)
Theorem CBDb:
  ω ≤ (bd : 'g ordinal) ∧ (∀x:^FTY. Fset x ≼ preds bd) ⇒
  ∀B:'a set. 𝟚 ≼ B ⇒
             (Fin B : ^FTY set) ≼ B ** cardSUC (Fin (preds bd) : ^FORD set)
Proof
  rpt strip_tac >>
  qabbrev_tac ‘kA = (Fin (preds bd) : ^FORD set) CROSS (B ** preds bd)’ >>
  qmatch_abbrev_tac ‘_ ≼ B ** k’ >>
  ‘kA ≼ B ** k’
    by (simp[Abbr‘k’, Abbr‘kA’] >> irule CARD_MUL2_ABSORB_LE >>
        simp[] >> rpt strip_tac >~
        [‘𝟚 ≼ B’, ‘B ≼ 𝟙’] >- (drule_all cardleq_TRANS >> simp[]) >~
        [‘INFINITE (Fin (preds bd))’]
        >- (disj2_tac >>
            irule (ISPEC “preds (bd:'g ordinal)” CARDLEQ_INFINITE) >>
            qexists_tac ‘bd’ >> conj_tac
            >- (simp[FINITE_preds] >> rpt strip_tac >> gvs[]) >>
            MATCH_ACCEPT_TAC nontrivialBs) >~
        [‘Fin (preds bd) ≼ B ** cardSUC _’]
        >- (resolve_then (Pos last) irule CARD_LE_EXP cardleq_TRANS >>
            simp[]) >>
        irule set_exp_cardle_cong >> simp[] >> rpt strip_tac >>
        gvs[cardleq_empty] >>
        assume_tac (ISPEC “preds (bd:'g ordinal)” nontrivialBs) >>
        first_x_assum $ C (resolve_then (Pos hd) irule) cardleq_TRANS >>
        simp[]) >>
  first_assum $ C (resolve_then (Pos last) irule) cardleq_TRANS >>
  qabbrev_tac ‘d = λ(y:^FORD,f). Fmap f y’ >>
  simp[cardleq_def] >>
  irule_at Any (SRULE [PULL_EXISTS] SURJ_IMP_INJ) >> qexists_tac ‘d’ >>
  simp[SURJ_DEF] >> conj_tac
  >- (simp[FORALL_PROD,Abbr‘kA’, Abbr‘d’, FsetMap, set_exp_def] >>
      rw[] >> simp[SUBSET_DEF, PULL_EXISTS] >> qx_gen_tac ‘b’ >> strip_tac >>
      ‘b ∈ preds bd’ by metis_tac[SUBSET_DEF] >> gs[] >> first_assum drule >>
      simp[PULL_EXISTS]) >>
  qx_gen_tac ‘vf’ >> strip_tac >>
  ‘?g. INJ g (Fset vf) (preds bd)’ by metis_tac[cardleq_def] >>
  qabbrev_tac ‘y = Fmap g vf’ >>
  ‘Fset vf ⊆ B’ by gs[] >>
  ‘?f. (!b. b ∈ Fset vf ⇒ f (g b) = b) /\ (!bp. bp < bd ==> f bp ∈ B)’
    by (‘?be. be ∈ B’ by (simp[MEMBER_NOT_EMPTY] >>
                          strip_tac >> gvs[cardleq_empty]) >>
        qexists_tac ‘λbp. case some b. b IN Fset vf /\ g b = bp of
                            NONE => be
                          | SOME b => b
                    ’ >> conj_tac >> simp[] >> rpt strip_tac
        >- (gs[INJ_IFF, SF CONJ_ss] >> csimp[]) >>
        DEEP_INTRO_TAC optionTheory.some_intro >> simp[] >>
        gs[SUBSET_DEF]) >>
  qexists_tac ‘(y, λbp. if bp ∈ preds bd then f bp else ARB)’ >>
  conj_tac
  >- (simp[Abbr‘kA’, Abbr‘y’, FsetMap] >> conj_tac
      >- gs[INJ_IFF, SUBSET_DEF, PULL_EXISTS] >>
      simp[set_exp_def]) >>
  simp[Abbr‘d’, Abbr‘y’, FmapO'] >>
  simp[Once (GSYM FmapID'), SimpRHS] >> irule FmapCONG >> simp[] >>
  gs[INJ_IFF]
QED

Theorem preds_bd_lemma[local]:
  preds (bd:'g ordinal) ≼
  preds (oleast a:^FORD ordinal. preds a ≈ (Fin (preds bd) : ^FORD set))
Proof
  assume_tac (ISPEC “preds (bd:'g ordinal)” nontrivialBs) >>
  pop_assum mp_tac >>
  simp[Once cardleq_lteq, SimpL “$==>”] >> strip_tac
  >- (DEEP_INTRO_TAC oleast_intro >> conj_tac
      >- (irule cardeq_ordinals_exist >>
          simp[Once disjUNION_UNIV] >>
          resolve_then (Pos hd) irule CARD_LE_UNIV CARD_LE_TRANS >>
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
  s ⊆ t ⇒ (Fin s : ^FTY set) ⊆ Fin t
Proof
  simp[SUBSET_DEF] >> metis_tac[]
QED

Theorem Fin_cardleq:
  s ≼ t ⇒ (Fin s : ^FTY set) ≼ (Fin t : ^FTYB set)
Proof
  simp[cardleq_def] >>
  disch_then $ qx_choose_then ‘f’ strip_assume_tac >>
  EXISTS_TAC “Fmap (f:'a -> 'b) : ^FTY -> ^FTYB” >>
  simp[INJ_IFF, FsetMap] >>
  rpt strip_tac >- gs[SUBSET_DEF, PULL_EXISTS, INJ_IFF] >>
  simp[EQ_IMP_THM] >> strip_tac >>
  ‘Fmap (LINV f s o f) x = Fmap I x ∧ Fmap (LINV f s o f) y = Fmap I y’
    by (conj_tac >> irule FmapCONG >> drule_then assume_tac LINV_DEF >>
        gs[LINV_DEF, SUBSET_DEF]) >>
  qpat_x_assum ‘Fmap f x = _’ (mp_tac o Q.AP_TERM ‘Fmap (LINV f s)’) >>
  simp[FmapO'] >> simp[FmapID']
QED

Theorem cardADD2[local]:
  s ≼ s +_c 𝟚
Proof
  simp[CARD_LE_ADDR]
QED

(* ----------------------------------------------------------------------
    STILL TO PORT.  What is above is everything the construction needs
    up to and including the two hard cardinality lemmas; what follows in
    bnfAlgebraScript.sml is alg_cardinality_bound (below, not yet
    working), and then the construction proper: copy_alg_back, IAlg,
    Cons, initiality0, iso0, the type definition itself, NCONS, DEST,
    initiality, IND, MAP and SET.  See .tmp/bnf-datatypes-handoff.md.
   ---------------------------------------------------------------------- *)

Theorem alg_cardinality_bound:
  ω ≤ (bd : 'g ordinal) ∧ (∀x:^FSUM. Fset x ≼ preds bd) ⇒
  KK (s:^FTY -> 'a) (csuc bd) ≼ 𝟚 ** (cardSUC (Fin (preds bd) : ^FORD set))
Proof
  strip_tac >>
  qmatch_abbrev_tac ‘_ ≼ 𝟚 ** BD’ >>
  ‘INFINITE BD’
    by (simp[Abbr‘BD’] >>
        irule (ISPEC “preds (bd:'g ordinal)” CARDLEQ_INFINITE) >>
        qexists_tac ‘bd’ >> conj_tac
        >- (simp[FINITE_preds] >> rpt strip_tac >> gvs[]) >>
        MATCH_ACCEPT_TAC nontrivialBs) >>
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
                 irule cardleq_preds_csuc >>
                 MATCH_ACCEPT_TAC preds_bd_lemma) >>
  ho_match_mp_tac ord_induction >> rw[] >>
  simp[Once KK_thm] >> rw[] >> irule CARD_BIGUNION >>
  simp[PULL_EXISTS] >> reverse (rpt conj_tac)
  >- (irule IMAGE_cardleq_rwt >> gs[lt_csuc] >>
      resolve_then Any
                   (fn th =>
                      resolve_then (Pos hd) irule th cardleq_TRANS)
                   cardleq_REFL
                   CARD_LE_EXP >> irule set_exp_cardle_cong >> simp[] >>
      assume_tac preds_bd_lemma >>
      dxrule_then assume_tac cardleq_preds_csuc >>
      simp[Abbr‘BD’, cardSUC_def] >>
      pop_assum (C (resolve_then (Pos last) irule) cardleq_TRANS) >>
      simp[lt_csuc, ordlt_preds_mono]) >>
  qx_gen_tac ‘j’ >> strip_tac >>
  ‘{ s fv | fv | Fset fv ⊆ KK s j} = IMAGE s (Fin (KK s j))’
    by simp[EXTENSION] >> simp[] >>
  irule IMAGE_cardleq_rwt >>
  resolve_then (Pos hd) irule (MATCH_MP (GEN_ALL Fin_cardleq) cardADD2)
               cardleq_TRANS >>
  drule_then (drule_then $ qspec_then ‘KK s j +_c 𝟚’ mp_tac) CBDb >>
  impl_tac >- simp[CARD_LE_ADDL] >>
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
  ‘(𝟚 ** BD +_c 𝟚) ** BD ≼ (𝟚 ** BD) ** BD’
    by (irule CARDEQ_IMP_CARDLEQ >> irule set_exp_card_cong >> simp[]) >>
  ‘(𝟚 ** BD) ** BD ≼ 𝟚 ** (BD CROSS BD)’
    by (irule CARDEQ_IMP_CARDLEQ >> MATCH_ACCEPT_TAC set_exp_product) >>
  ‘𝟚 ** (BD CROSS BD) ≼ 𝟚 ** BD’
    by (irule set_exp_cardle_cong >> simp[] >>
        ONCE_REWRITE_TAC [cardleq_lteq] >> simp[CARD_SQUARE_INFINITE]) >>
  metis_tac[cardleq_TRANS]
QED

(* ----------------------------------------------------------------------
    Everything the algebras need is now known about the specific bound,
    so a single type is big enough to hold the initial algebra.
   ---------------------------------------------------------------------- *)

Theorem KK_EQ_MINSET =
        MATCH_MP KKbnd_EQ_minset (CONJ omega_le_bnd Fset_cle_bnd)

Theorem inst_bound =
        MATCH_MP alg_cardinality_bound
                 (CONJ omega_le_bnd
                       (INST_TYPE [alpha |-> “:'a + bool”] Fset_cle_bnd))
          |> REWRITE_RULE [KK_EQ_MINSET]

val algty0 = #1 (dom_rng (type_of (rand (concl inst_bound))))
val ALGTY0 = ty_antiq algty0
val idx0 = pairSyntax.mk_prod(algty0 --> bool, FatTy algty0 --> algty0)
val algty = idx0 --> algty0
val ALGTY = ty_antiq algty
val FALGTY = FatTY algty

Theorem copy_alg_back:
  (A:'a set) ≼ (B:'b set) ∧ alg (A, s : ^FTY -> 'a) ⇒
  ∃(B0:'b set) (s' : ^FTYB -> 'b) h j.
    hom h (B0,s') (A,s) ∧ hom j (A,s) (B0,s') ∧
    (∀a. a ∈ A ⇒ h (j a) = a) ∧ (∀b. b ∈ B0 ⇒ j (h b) = b)
Proof
  simp[cardleq_def] >> strip_tac >> rename [‘INJ h0 A B’] >>
  qexistsl_tac [‘IMAGE h0 A’, ‘λbv. h0 (s (Fmap (LINV h0 A) bv))’,
                ‘LINV h0 A’, ‘h0’] >>
  csimp[hom_def, PULL_EXISTS] >>
  drule_then assume_tac LINV_DEF >> rw[] >~
  [‘alg (IMAGE h0 A, _)’]
  >- (gs[alg_def, SUBSET_DEF] >> rw[] >>
      irule_at Any EQ_REFL >> first_assum irule >>
      simp[FsetMap, PULL_EXISTS] >> rw[] >> first_assum drule >>
      simp[PULL_EXISTS]) >~
  [‘LINV h0 A (h0 (s _))’]
  >- (‘s (Fmap (LINV h0 A) bv) ∈ A’
        by (gs[alg_def] >> first_assum irule >>
            gs[FsetMap, SUBSET_DEF, PULL_EXISTS] >> rw[] >>
            first_assum drule >> simp[PULL_EXISTS]) >>
      simp[]) >>
  simp[FmapO'] >> ntac 2 AP_TERM_TAC >> irule Fmap_eq_id >>
  gs[SUBSET_DEF]
QED

Definition IAlg_def:
  IAlg = minset (SND bigprod : ^FALGTY -> ^ALGTY)
End

Definition Cons_def:
  Cons = (SND bigprod : ^FALGTY -> ^ALGTY)
End

Theorem IAlg_isalg[simp]:
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
  gs[hom_def, alg_def] >> RULE_ASSUM_TAC GSYM >>
  simp[] >> rw[] >> AP_TERM_TAC >> irule FmapCONG >> simp[] >>
  gs[SUBSET_DEF]
QED

Theorem initiality0:
  ∀(t:^FTYC -> 'c) (G:'c set).
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
    by (irule minsub_I_subalg >> simp[Abbr‘Is’]) >>
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
  ‘alg (IAlg, Cons)’ by simp[] >>
  drule alg_nonempty >> simp[EXTENSION, IN_DEF]
QED

Theorem alg_Fin:
  alg (A,s) ⇒ alg (Fin A, Fmap s)
Proof
  strip_tac >>
  simp[alg_def, SUBSET_DEF, FsetMap, PULL_EXISTS] >> rw[] >>
  rename [‘s vf ∈ A’, ‘vf ∈ Fset vff’] >>
  first_assum $ drule_then assume_tac >>
  irule (iffLR alg_def) >> simp[SUBSET_DEF]
QED

Definition arbify_def:
  arbify A f x = if x ∈ A then f x else ARB
End

Theorem hom_arbify:
  hom (arbify A f) (A,s : ^FTY -> 'a) (B,t : ^FTYB -> 'b) ⇔ hom f (A,s) (B,t)
Proof
  simp[hom_def, arbify_def] >> Cases_on ‘alg (A,s)’ >> simp[] >>
  ‘∀af. af ∈ Fin A ⇒ s af ∈ A’ by gs[alg_def] >> simp[] >>
  rw[EQ_IMP_THM] >> RULE_ASSUM_TAC GSYM >> simp[] >> AP_TERM_TAC >>
  irule FmapCONG >> gs[arbify_def, SUBSET_DEF]
QED

Theorem iso0:
  BIJ Cons (Fin IAlg) IAlg
Proof
  ‘alg (IAlg, Cons)’ by simp[] >>
  drule_then assume_tac alg_Fin >>
  drule_then assume_tac initiality0 >>
  gs[EXISTS_UNIQUE_ALT] >>
  rename[‘hom _ (IAlg,Cons) _ ∧ _ ⇔ H = _’] >>
  ‘hom H (IAlg,Cons) (Fin IAlg, Fmap Cons)’ by metis_tac[] >>
  ‘hom Cons (Fin IAlg, Fmap Cons) (IAlg,Cons)’
    by (simp[hom_def] >> rpt strip_tac >> irule (iffLR alg_def) >>
        simp[]) >>
  rev_drule_then (drule_then assume_tac) homs_compose >>
  strip_assume_tac
    (SRULE [EXISTS_UNIQUE_ALT] (MATCH_MP initiality0 IAlg_isalg)) >>
  ‘hom (arbify IAlg (Cons o H)) (IAlg,Cons) (IAlg,Cons)’ by simp[hom_arbify] >>
  ‘∀x. x ∉ IAlg ⇒ arbify IAlg (Cons o H) x = ARB’ by simp[arbify_def] >>
  ‘hom (arbify IAlg I) (IAlg,Cons) (IAlg,Cons)’
    by (simp[hom_arbify] >> simp[hom_def, FmapID]) >>
  ‘∀x. x ∉ IAlg ⇒ arbify IAlg I x = ARB’ by simp[arbify_def] >>
  ‘arbify IAlg (Cons o H) = arbify IAlg I’ by metis_tac[] >>
  simp[BIJ_IFF_INV] >> conj_tac
  >- (rpt strip_tac >> irule (iffLR alg_def) >> simp[]) >>
  qexists_tac ‘H’ >> conj_tac
  >- (qpat_x_assum ‘hom H _ _’ mp_tac >> simp[hom_def]) >>
  conj_asm2_tac
  >- (qpat_x_assum ‘hom H _ _’ mp_tac >> simp[hom_def, FmapO'] >> strip_tac >>
      qx_gen_tac ‘a’ >> strip_tac >>
      ‘H (Cons a) = Fmap (Cons o H) a’ by simp[] >> pop_assum SUBST1_TAC >>
      ‘Fmap (Cons o H) a = Fmap I a’ suffices_by simp[FmapID'] >>
      irule FmapCONG >> gs[SUBSET_DEF]) >>
  pop_assum mp_tac >> simp[Once FUN_EQ_THM, arbify_def] >> metis_tac[]
QED

(* ----------------------------------------------------------------------
    The datatype itself: the only type this construction introduces.
   ---------------------------------------------------------------------- *)

val itype = newtypeTools.rich_new_type{
  tyname = "nty", exthm = inhabited, ABS = "nty_ABS", REP = "nty_REP"
  }

val NTY = ty_antiq “:'b1 nty”
val FNTY = FatTY “:'b1 nty”

Definition NCONS_def:
  NCONS (x : ^FNTY) = nty_ABS (Cons (Fmap nty_REP x))
End

Theorem NCONS_isalg[simp]:
  alg (UNIV, NCONS)
Proof
  simp[alg_def]
QED

Theorem hom_nty_ABS:
  hom nty_ABS (IAlg,Cons) (UNIV,NCONS)
Proof
  simp[hom_def] >> simp[NCONS_def, FmapO'] >>
  rpt strip_tac >> rpt AP_TERM_TAC >> irule Fmap_eq_id >>
  gs[SUBSET_DEF, #repabs_pseudo_id itype, IN_DEF]
QED

Theorem hom_nty_REP:
  hom nty_REP (UNIV, NCONS) (IAlg, Cons)
Proof
  simp[hom_def] >> conj_tac
  >- simp[IN_DEF, # termP_term_REP itype] >>
  simp[NCONS_def] >> rpt strip_tac >> ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
  irule (#repabs_pseudo_id itype) >>
  ONCE_REWRITE_TAC [GSYM SPECIFICATION] >>
  irule (iffLR alg_def) >>
  simp[FsetMap, SUBSET_DEF, PULL_EXISTS, IN_DEF, #termP_term_REP itype]
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
                       |> SRULE [hom_def, alg_def, SUBSET_UNIV]
                       |> GSYM |> Q.GEN ‘t’

Theorem minset_Cons:
  minset Cons = IAlg
Proof
  simp[IAlg_def, Cons_def]
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
  (∀av. Fset av ⊆ IAlg ⇒ P av) ⇔ (∀n. P (Fmap nty_REP n))
Proof
  rw[EQ_IMP_THM]
  >- (pop_assum irule >> simp[FsetMap, SUBSET_DEF, PULL_EXISTS] >>
      simp[IN_DEF, #termP_term_REP itype]) >>
  first_x_assum $ qspec_then ‘Fmap nty_ABS av’ mp_tac >>
  simp[FmapO'] >>
  ‘Fmap (nty_REP o nty_ABS) av = av’ suffices_by simp[] >>
  irule Fmap_eq_id >> gs[SUBSET_DEF, #repabs_pseudo_id itype, IN_DEF]
QED

Theorem IN_Fset:
  (∀y. y ∈ Fset x ⇒ Q (nty_ABS y)) ⇔ x ∈ Fin (Q o nty_ABS)
Proof
  simp[SUBSET_DEF] >> simp[IN_DEF]
QED

Theorem Cons_NCONS:
  Fset x ⊆ IAlg ⇒ Cons x = nty_REP (NCONS (Fmap nty_ABS x))
Proof
  simp[NCONS_def, FmapO'] >> strip_tac >>
  ‘Fmap (nty_REP o nty_ABS) x = x’
    by (irule Fmap_eq_id >>
        gs[SUBSET_DEF, #repabs_pseudo_id itype, IN_DEF]) >>
  simp[] >>
  ‘Cons x ∈ IAlg’ suffices_by simp[IN_DEF, #repabs_pseudo_id itype] >>
  irule (iffLR alg_def) >> simp[]
QED

Theorem abs_o_rep:
  nty_ABS o nty_REP = I
Proof
  simp[FUN_EQ_THM, #absrep_id itype]
QED

Theorem Fset_applied:
  Fset x v ⇔ v ∈ Fset x
Proof
  simp[IN_DEF]
QED

Theorem IND =
        minset_ind |> Q.GEN ‘s’
                   |> Q.ISPEC ‘Cons’
                   |> SRULE [minset_Cons]
                   |> Q.SPEC ‘λia. Q (nty_ABS ia)’
                   |> SRULE[ALL_Ialg, #absrep_id itype, IN_Fset, Cons_NCONS]
                   |> SRULE[GSYM AND_IMP_INTRO, ALL_Ialgv, FmapO', Fin_def,
                            FsetMap, abs_o_rep, FmapID]
                   |> SRULE[SUBSET_DEF, PULL_EXISTS, IN_DEF, #absrep_id itype]
                   |> SRULE [Fset_applied]

Theorem NCONS_comp:
  NCONS = nty_ABS o Cons o Fmap nty_REP
Proof
  simp[FUN_EQ_THM, NCONS_def]
QED

Theorem iso:
  BIJ NCONS (Fin UNIV) UNIV
Proof
  simp[NCONS_comp] >> irule BIJ_COMPOSE >> qexists_tac ‘IAlg’ >>
  reverse conj_tac
  >- (simp[BIJ_IFF_INV] >> qexists_tac ‘nty_REP’ >>
      simp[#repabs_pseudo_id itype, #absrep_id itype, IN_DEF,
           #termP_term_REP itype]) >>
  irule BIJ_COMPOSE >> irule_at Any iso0 >>
  simp[BIJ_IFF_INV] >> conj_tac
  >- simp[FsetMap, SUBSET_DEF, PULL_EXISTS, IN_DEF, #termP_term_REP itype] >>
  qexists_tac ‘Fmap nty_ABS’ >> simp[FmapO', abs_o_rep, FmapID] >>
  rpt strip_tac >> irule Fmap_eq_id >> simp[] >>
  gs[SUBSET_DEF, #repabs_pseudo_id itype, IN_DEF]
QED

Theorem NCONS_11:
  NCONS x = NCONS y ⇔ x = y
Proof
  assume_tac iso >> gs[BIJ_DEF, INJ_IFF]
QED

val DEST_def = new_specification("DEST_def", ["DEST"],
                                 iso |> SRULE [BIJ_IFF_INV])
