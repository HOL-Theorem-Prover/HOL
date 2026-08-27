Theory bnfInitial
Ancestors
  pred_set cardinal ordinalBasic combin pair
Libs
  HolKernel Parse boolLib bossLib

(* ----------------------------------------------------------------------
    The initial-algebra construction, proved once.

    HOL has no type-operator variables, so a functor F cannot be
    quantified over directly.  It can, however, be *parameterised*: each
    instance F[τ] that the construction needs becomes an ordinary type
    variable, and the functor's map and set functions become ordinary
    term variables, with the BNF laws carried as hypotheses.  The
    development below never mentions a particular functor, so it is
    proved once and a datatype package only has to instantiate it — no
    parsing, no tactics, and no per-datatype proof.

    Throughout, 'f is F[α], 'g is F[β] and 'h is F[γ]; mp_ab is F's map
    from α to β, and sta its set function at α.
   ---------------------------------------------------------------------- *)

(* the elements of F[α] all of whose α-atoms lie in As *)
Definition FIN_def:
  FIN (sta : 'f -> 'a set) As = { a : 'f | sta a ⊆ As }
End

Theorem IN_FIN[simp]:
  a ∈ FIN sta As ⇔ sta a ⊆ As
Proof
  simp[FIN_def]
QED

Theorem FIN_UNIV[simp]:
  FIN sta UNIV = UNIV
Proof
  simp[EXTENSION]
QED

Definition ALG_def:
  ALG (sta : 'f -> 'a set) (A, s) ⇔ ∀x. x ∈ FIN sta A ⇒ s x ∈ A
End

Theorem ALG_UNIV[simp]:
  ALG sta (UNIV, s)
Proof
  simp[ALG_def]
QED

Definition MINSET_def:
  MINSET (sta : 'f -> 'a set) s = BIGINTER { B | ALG sta (B,s) }
End

Theorem MINSET_is_ALG[simp]:
  ALG sta (MINSET sta s, s)
Proof
  simp[MINSET_def, ALG_def, SUBSET_BIGINTER]
QED

Theorem IN_MINSET:
  x ∈ MINSET sta s ⇔ ∀A. ALG sta (A,s) ⇒ x ∈ A
Proof
  simp[MINSET_def]
QED

Definition HOM_def:
  HOM (mp : ('a -> 'b) -> 'f -> 'g) sta stb h (A,s) (B,t) ⇔
    ALG sta (A,s) ∧ ALG stb (B,t) ∧ (∀a. a ∈ A ⇒ h a ∈ B) ∧
    ∀af. af ∈ FIN sta A ⇒ t (mp h af) = h (s af)
End

(* ----------------------------------------------------------------------
    The BNF laws, as predicates over the parameters.  Each names the
    instances it relates, so a lemma can ask for exactly the ones it
    needs.
   ---------------------------------------------------------------------- *)

Definition MapId_def:
  MapId (mp : ('a -> 'a) -> 'f -> 'f) ⇔ ∀x. mp I x = x
End

Definition MapComp_def:
  MapComp (mp_ab : ('a -> 'b) -> 'f -> 'g)
          (mp_bc : ('b -> 'c) -> 'g -> 'h)
          (mp_ac : ('a -> 'c) -> 'f -> 'h) ⇔
    ∀f g x. mp_bc g (mp_ab f x) = mp_ac (g o f) x
End

Definition Natural_def:
  Natural (mp : ('a -> 'b) -> 'f -> 'g) sta stb ⇔
    ∀f x. stb (mp f x) = IMAGE f (sta x)
End

Definition MapCong_def:
  MapCong (mp : ('a -> 'b) -> 'f -> 'g) sta ⇔
    ∀f g x. (∀a. a ∈ sta x ⇒ f a = g a) ⇒ mp f x = mp g x
End

Theorem Map_eq_id:
  MapId mp ∧ MapCong mp sta ⇒
  ∀f x. (∀a. a ∈ sta x ⇒ f a = a) ⇒ mp f x = x
Proof
  simp[MapId_def, MapCong_def] >> rpt strip_tac >>
  ‘mp f x = mp I x’ by (first_x_assum irule >> simp[]) >>
  simp[]
QED

(* ----------------------------------------------------------------------
    algebras and homomorphisms
   ---------------------------------------------------------------------- *)

Theorem ALG_nonempty:
  (∃w:'f. sta w = ∅) ⇒ ALG sta (A, s) ⇒ A ≠ ∅
Proof
  rpt strip_tac >> gvs[ALG_def] >> metis_tac[SUBSET_REFL, NOT_IN_EMPTY]
QED

Theorem HOMs_on_same_domain:
  MapCong mp sta ⇒
  HOM mp sta stb h (A,s) (B,t) ∧ (∀a. a ∈ A ⇒ h' a = h a) ⇒
  HOM mp sta stb h' (A,s) (B,t)
Proof
  simp[HOM_def, MapCong_def] >> rw[] >>
  ‘s af ∈ A’ by gs[ALG_def] >> simp[] >>
  ‘mp h' af = mp h af’ suffices_by simp[] >>
  first_x_assum irule >> metis_tac[SUBSET_DEF]
QED

Theorem HOMs_compose:
  MapComp mp_ab mp_bc mp_ac ∧ Natural mp_ab sta stb ⇒
  HOM mp_ab sta stb f (A:'a set,s) (B:'b set,t) ∧
  HOM mp_bc stb stc g (B,t) (C:'c set,u) ⇒
  HOM mp_ac sta stc (g o f) (A,s) (C,u)
Proof
  simp[MapComp_def, Natural_def] >> strip_tac >>
  csimp[HOM_def] >> rw[] >>
  ‘stb (mp_ab f af) ⊆ B’ by (simp[] >> gs[SUBSET_DEF, PULL_EXISTS]) >>
  qpat_x_assum ‘∀af. stb af ⊆ B ⇒ _’ (qspec_then ‘mp_ab f af’ assume_tac) >>
  qpat_x_assum ‘∀af. sta af ⊆ A ⇒ _’ (qspec_then ‘af’ assume_tac) >>
  gs[]
QED

Theorem MINSET_ind:
  ∀P. (∀x. sta x ⊆ MINSET sta s ∧ (∀y. y ∈ sta x ⇒ P y) ⇒ P (s x)) ⇒
      ∀x. x ∈ MINSET sta s ⇒ P x
Proof
  gen_tac >> strip_tac >>
  ‘MINSET sta s ⊆ P INTER MINSET sta s’
    suffices_by simp[SUBSET_DEF, IN_DEF] >>
  simp[MINSET_def, SimpL “$SUBSET”] >> irule BIGINTER_SUBSET >>
  qexists_tac ‘P INTER MINSET sta s’ >>
  simp[ALG_def, SUBSET_DEF] >> rw[]
  >- gs[IN_DEF, SUBSET_DEF] >>
  ntac 2 (last_x_assum (K ALL_TAC)) >>
  gs[ALG_def, SUBSET_DEF, IN_MINSET]
QED

Theorem MINSET_ind':
  ∀P. (∀x. (∀y. y ∈ sta x ⇒ y ∈ MINSET sta s ∧ P y) ⇒ P (s x)) ⇒
      ∀x. x ∈ MINSET sta s ⇒ P x
Proof
  metis_tac[MINSET_ind, SUBSET_DEF]
QED

Theorem MINSET_unique_homs:
  MapCong mp sta ⇒
  HOM mp sta stb h1 (MINSET sta s, s) (B,t) ∧
  HOM mp sta stb h2 (MINSET sta s, s) (B,t) ⇒
  ∀a. a ∈ MINSET sta s ⇒ h1 a = h2 a
Proof
  simp[MapCong_def] >> strip_tac >> strip_tac >>
  ho_match_mp_tac MINSET_ind' >> gs[HOM_def] >>
  rpt strip_tac >> RULE_ASSUM_TAC GSYM >> simp[] >> gs[SUBSET_DEF] >>
  AP_TERM_TAC >> first_x_assum irule >> simp[]
QED

Definition SUBALG_def:
  SUBALG sta (A,s) (B,t) ⇔
    ALG sta (A,s) ∧ ALG sta (B,t) ∧
    (∀af. af ∈ FIN sta A ⇒ s af = t af) ∧ A ⊆ B
End

Theorem SUBALGs_preserve_homs:
  SUBALG sta A1 A2 ∧ HOM mp sta stb f A2 C ⇒ HOM mp sta stb f A1 C
Proof
  Cases_on ‘A1’ >> Cases_on ‘A2’ >> Cases_on ‘C’ >>
  simp[HOM_def, SUBALG_def] >> metis_tac[SUBSET_DEF]
QED

Theorem MINSET_SUBALG:
  ALG sta (A,s) ⇒ SUBALG sta (MINSET sta s, s) (A,s)
Proof
  simp[SUBALG_def, MINSET_def] >> strip_tac >>
  irule BIGINTER_SUBSET >> simp[] >> metis_tac[SUBSET_REFL]
QED

Theorem MINSET_I_HOM:
  MapId mp ⇒ ALG sta (A,s) ⇒ HOM mp sta sta I (MINSET sta s, s) (A,s)
Proof
  simp[MapId_def] >> rpt strip_tac >> drule MINSET_SUBALG >>
  simp[HOM_def, SUBALG_def, SUBSET_DEF]
QED

(* ----------------------------------------------------------------------
    The product of all algebras over a fixed carrier type.

    A pair that isn't an algebra is coerced to one, so the product can be
    indexed by the plain pair type and the construction needs no type
    definition of its own.  'fp is F at the product's carrier.
   ---------------------------------------------------------------------- *)

Definition MKALG_def:
  MKALG (sta : 'f -> 'a set) p = if ALG sta p then p else (UNIV, SND p)
End

Theorem MKALG_ALG[simp]:
  ALG sta (MKALG sta p)
Proof
  rw[MKALG_def] >> Cases_on ‘p’ >> simp[]
QED

Theorem MKALG_ID:
  ALG sta p ⇒ MKALG sta p = p
Proof
  simp[MKALG_def]
QED

Definition BIGPROD_def:
  BIGPROD (mp : ((('a set # ('f -> 'a)) -> 'a) -> 'a) -> 'fp -> 'f) sta =
    ({ ff : ('a set # ('f -> 'a)) -> 'a | ∀i. ff i ∈ FST (MKALG sta i) },
     λ(fv:'fp) i. SND (MKALG sta i) (mp (λff. ff i) fv))
End

Theorem BIGPROD_ALG[simp]:
  Natural mp stp sta ⇒ ALG stp (BIGPROD mp sta)
Proof
  simp[Natural_def] >> strip_tac >>
  simp[BIGPROD_def, ALG_def] >> rpt strip_tac >>
  Cases_on ‘MKALG sta i’ >> rename [‘MKALG sta i = (A,s)’] >>
  ‘ALG sta (A,s)’ by metis_tac[MKALG_ALG] >> simp[] >>
  gs[ALG_def] >> first_assum irule >>
  gs[SUBSET_DEF, PULL_EXISTS] >> metis_tac[FST]
QED

Theorem BIGPROD_proj:
  Natural mp stp sta ⇒
  ALG sta (A,s) ⇒
  HOM mp stp sta (λff. ff (A,s)) (BIGPROD mp sta) (A,s)
Proof
  strip_tac >> strip_tac >> simp[HOM_def, BIGPROD_def] >> rpt strip_tac
  >- metis_tac[BIGPROD_ALG, BIGPROD_def]
  >- (‘MKALG sta (A,s) = (A,s)’ by metis_tac[MKALG_ID] >>
      first_x_assum $ qspec_then ‘(A,s)’ mp_tac >> simp[]) >>
  ‘MKALG sta (A,s) = (A,s)’ by metis_tac[MKALG_ID] >> simp[]
QED

(* ----------------------------------------------------------------------
    Traytel's K function (MSc thesis, p 15): iterate the algebra's
    operation through the ordinals until it closes off.
   ---------------------------------------------------------------------- *)

val KK_def = new_specification(
  "KK_def", ["KK"],
  ord_RECURSION |> Q.ISPEC ‘∅ : 'c set’
                |> Q.SPEC ‘λx r. r ∪ { s(x) | sta x ⊆ r }’
                |> Q.SPEC ‘λx rs. BIGUNION rs’
                |> SRULE[]
                |> Q.GENL [‘sta’, ‘s’]
                |> CONV_RULE (BINDER_CONV SKOLEM_CONV THENC SKOLEM_CONV));

Theorem KK_mono:
  ∀b a. a < b ⇒ KK sta s a ⊆ KK sta s b
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
  ∀a b. a ≤ b ⇒ KK sta s a ⊆ KK sta s b
Proof
  metis_tac[SUBSET_REFL, KK_mono, ordle_lteq]
QED

Theorem KK_SUB_MINSET:
  ∀a. KK sta s a ⊆ MINSET sta s
Proof
  ho_match_mp_tac simple_ord_induction >> simp[KK_def] >> rw[]
  >- (simp[SUBSET_DEF, PULL_EXISTS] >> rpt strip_tac >>
      ‘ALG sta (MINSET sta s, s)’ by simp[] >>
      gs[ALG_def, Excl "MINSET_is_ALG"] >>
      metis_tac[SUBSET_DEF]) >>
  simp[SUBSET_DEF, PULL_EXISTS] >> metis_tac[SUBSET_DEF]
QED

Theorem KK_fixp_is_ALG:
  { s x | x | sta x ⊆ KK sta s e } = KK sta s e ⇒ ALG sta (KK sta s e, s)
Proof
  rw[ALG_def] >> gs[EXTENSION] >> metis_tac[]
QED

Theorem KK_sup:
  ords ≼ 𝕌(:num + 'g) ⇒
  KK sta s (sup ords : 'g ordinal) = BIGUNION (IMAGE (KK sta s) ords)
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
  BIGUNION (IMAGE (KK sta s) (preds a)) ⊆ KK sta s a
Proof
  qid_spec_tac ‘a’ >> ho_match_mp_tac simple_ord_induction >>
  rw[]
  >- (simp[KK_def, preds_ordSUC] >> irule SUBSET_TRANS >> goal_assum drule >>
      simp[]) >>
  simp[KK_def]
QED

Theorem KK_thm:
  KK sta s a = if a = 0 then ∅
               else BIGUNION (IMAGE (λb. { s fv | fv | sta fv ⊆ KK sta s b})
                              (preds a))
Proof
  qid_spec_tac ‘a’ >> ho_match_mp_tac simple_ord_induction >>
  rw[]
  >- simp[KK_def]
  >- (simp[preds_nat] >> ‘count 1 = {0}’ by simp[EXTENSION] >>
      simp[KK_def, GSYM ORD_ONE, Excl "ORD_ONE"])
  >- (qpat_x_assum ‘KK _ _ _ = BIGUNION _’ (assume_tac o SYM) >>
      simp[KK_def, preds_ordSUC, UNION_COMM]) >>
  pop_assum (assume_tac o GSYM) >>
  simp[KK_def] >> irule SUBSET_ANTISYM >> conj_tac >>
  simp[Once SUBSET_DEF, PULL_EXISTS]
  >- (rpt strip_tac >> rename [‘v ∈ KK sta s b’] >>
      ‘b ≠ 0’ by (strip_tac >> gs[KK_def]) >>
      ‘KK sta s b = BIGUNION (IMAGE (λb0. { s fv | fv | sta fv ⊆ KK sta s b0})
                              (preds b))’ by metis_tac[] >>
      gs[PULL_EXISTS] >> metis_tac[ordlt_TRANS]) >>
  rpt strip_tac >> rename [‘b < a’, ‘sta fv ⊆ KK sta s b’] >>
  qexists_tac ‘b⁺’ >> simp[KK_def] >> metis_tac[islimit_SUC_lt]
QED

(* ----------------------------------------------------------------------
    The iteration closes off by csuc of the functor's bound.
   ---------------------------------------------------------------------- *)

Theorem sucbnd_suffices:
  ω ≤ (bd : 'g ordinal) ∧ (∀x : 'f. sta x ≼ preds bd) ⇒
  ALG sta (KK sta (s : 'f -> 'a) (csuc bd), s)
Proof
  strip_tac >>
  ‘INFINITE (preds bd)’ by (simp[FINITE_preds] >> rpt strip_tac >> gvs[]) >>
  irule KK_fixp_is_ALG >> irule SUBSET_ANTISYM >> conj_tac >>
  ONCE_REWRITE_TAC [SUBSET_DEF] >> simp[PULL_EXISTS] >>
  rpt strip_tac
  >- (rename [‘s fv ∈ KK sta s _’] >>
      drule_then strip_assume_tac csuc_is_nonzero_limit >>
      simp[KK_def, PULL_EXISTS, lt_csuc] >>
      gs[SUBSET_DEF, KK_def, PULL_EXISTS, lt_csuc] >>
      gs[GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] >>
      rename [‘_ ∈ KK sta s (g _)’, ‘preds (g _) ≼ preds bd’] >>
      qabbrev_tac ‘B = sup (IMAGE g $ sta fv)’ >>
      ‘IMAGE g $ sta fv ≼ univ(:num + ('g + num -> bool))’
        by (irule IMAGE_cardleq_rwt >>
            first_assum (C (resolve_then (Pos hd) irule) cardleq_TRANS) >>
            resolve_then (Pos hd) irule preds_inj_univ cardleq_TRANS >>
            simp[cardleq_lteq, bumpUNIV_cardlt]) >>
      ‘∀a. a < B ⇔ ∃v. v ∈ sta fv ∧ a < g v’
        by simp[Abbr‘B’, sup_thm, PULL_EXISTS] >>
      qexists_tac ‘B⁺’ >> simp[KK_def] >> reverse conj_tac
      >- (simp[preds_ordSUC, INFINITE_cardleq_INSERT] >>
          simp[Abbr‘B’, preds_sup, dclose_BIGUNION] >>
          irule CARD_BIGUNION >>
          simp[IMAGE_cardleq_rwt, PULL_EXISTS]) >>
      ‘KK sta s B = BIGUNION (IMAGE (KK sta s) (IMAGE g (sta fv)))’
        by simp[KK_sup, Abbr‘B’] >> disj2_tac >>
      qexists_tac ‘fv’ >> simp[SUBSET_DEF, PULL_EXISTS] >> metis_tac[]) >>
  rename [‘v ∈ KK sta s (csuc bd)’] >>
  drule_then strip_assume_tac csuc_is_nonzero_limit >>
  gvs[KK_def] >>
  rename [‘v ∈ KK sta s a’, ‘a < csuc bd’] >>
  qpat_x_assum ‘v ∈ KK sta s a’ mp_tac >> simp[Once KK_thm] >> rw[] >>
  gs[] >> qexists_tac ‘fv’ >> simp[] >> irule SUBSET_BIGUNION_SUBSET_I >>
  simp[PULL_EXISTS] >> metis_tac[ordlt_TRANS]
QED

(* mp has to be annotated into the same instance as sta and s: the
   parameterisation makes that explicit where a real functor would have
   made it implicit *)
Theorem KKbnd_EQ_MINSET:
  MapId (mp : ('a -> 'a) -> 'f -> 'f) ⇒
  ω ≤ (bd : 'g ordinal) ∧ (∀x : 'f. (sta : 'f -> 'a set) x ≼ preds bd) ⇒
  KK sta (s : 'f -> 'a) (csuc bd) = MINSET sta s
Proof
  strip_tac >> strip_tac >>
  drule_all_then (qspec_then ‘s’ assume_tac) sucbnd_suffices >>
  irule SUBSET_ANTISYM >> simp[KK_SUB_MINSET] >>
  ‘HOM mp sta sta I (MINSET sta s, s) (KK sta s (csuc bd), s)’
    by (irule MINSET_I_HOM >> simp[]) >>
  gs[HOM_def, SUBSET_DEF]
QED

(* ----------------------------------------------------------------------
    Because F is not constant, an algebra's carrier is no bigger than the
    collection of F-values over it.
   ---------------------------------------------------------------------- *)

Theorem NontrivialBs:
  Natural (mp : ('c -> 'a) -> 'h -> 'f) stc sta ⇒
  (∃x:'h. stc x ≠ ∅) ⇒
  ∀B:'a set. B ≼ FIN sta B
Proof
  simp[Natural_def] >> strip_tac >> strip_tac >> strip_tac >>
  simp[cardleq_def] >>
  qexists_tac ‘λb. mp (K b) x’ >> simp[INJ_IFF] >>
  conj_tac >- simp[SUBSET_DEF, PULL_EXISTS] >>
  rpt strip_tac >> iff_tac >> simp[] >> strip_tac >>
  ‘IMAGE (K b) (stc x) = IMAGE (K b') (stc x)’ by metis_tac[] >>
  gs[GSYM MEMBER_NOT_EMPTY] >>
  qpat_x_assum ‘IMAGE _ _ = IMAGE _ _’ mp_tac >>
  simp[Once EXTENSION] >> metis_tac[]
QED

Theorem FIN_MONO:
  s ⊆ t ⇒ (FIN sta s : 'f set) ⊆ FIN sta t
Proof
  simp[SUBSET_DEF] >> metis_tac[]
QED

Theorem FIN_cardleq:
  MapId (mp_aa : ('a -> 'a) -> 'f -> 'f) ∧ MapCong mp_aa sta ∧
  Natural (mp_ab : ('a -> 'b) -> 'f -> 'g) sta stb ∧
  MapComp mp_ab (mp_ba : ('b -> 'a) -> 'g -> 'f) mp_aa ⇒
  s ≼ t ⇒ (FIN sta s : 'f set) ≼ (FIN stb t : 'g set)
Proof
  strip_tac >>
  qpat_assum ‘MapId _’ (fn th1 =>
    qpat_assum ‘MapCong _ _’ (fn th2 =>
      assume_tac (MATCH_MP Map_eq_id (CONJ th1 th2)))) >>
  simp[cardleq_def] >>
  disch_then $ qx_choose_then ‘f’ strip_assume_tac >>
  qexists_tac ‘mp_ab f’ >> gs[Natural_def, INJ_IFF] >>
  rpt strip_tac >- gs[SUBSET_DEF, PULL_EXISTS, INJ_IFF] >>
  iff_tac >> simp[] >> strip_tac >>
  ‘mp_ba (LINV f s) (mp_ab f x) = mp_ba (LINV f s) (mp_ab f y)’ by simp[] >>
  gs[MapComp_def] >>
  ‘INJ f s t’ by simp[INJ_IFF] >>
  drule_then assume_tac LINV_DEF >>
  ‘mp_aa (LINV f s o f) x = x ∧ mp_aa (LINV f s o f) y = y’
    by (conj_tac >> first_x_assum irule >> gs[SUBSET_DEF]) >>
  gs[]
QED
