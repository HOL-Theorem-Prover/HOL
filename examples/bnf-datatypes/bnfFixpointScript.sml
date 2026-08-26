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
val FTY = ty_antiq Fty
val BTY = #1 (dom_rng (type_of (#bnd bnf)))   (* bnd is univ(:BTY) *)

(* the functor's type with the recursion argument at ty *)
fun FatTY ty = ty_antiq (type_subst [alpha |-> ty] Fty)
val FORD = FatTY “:'g ordinal”
val FTYB = FatTY beta
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

Definition bigprod_def:
  bigprod = ({ f : ('a set # (^FTY -> 'a)) -> 'a | ∀i. f i ∈ FST (mkalg i) },
             λfv i. SND (mkalg i) $ Fmap (λf. f i) fv)
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

(*
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
  mp_tac (Q.SPEC ‘KK s j +_c 𝟚’
            (MATCH_MP CBDb
               (CONJ (ASSUME “ω ≤ (bd:'g ordinal)”)
                     (ASSUME “∀x:^FTY.
                                Fset x ≼ preds (bd:'g ordinal)”)))) >>
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
*)
