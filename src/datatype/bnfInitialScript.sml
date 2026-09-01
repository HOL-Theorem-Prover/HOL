Theory bnfInitial[bare]
Ancestors
  pred_set cardinal ordinalBasic combin pair
Libs
  HolKernel Parse boolLib BasicProvers simpLib boolSimps metisLib numLib
  pred_setLib pairLib QLib TotalDefn[qualified]

(* ----------------------------------------------------------------------
    bossLib is not built yet — the package has to be, so that Datatype
    can use it, and so this is the part of bossLib's environment these
    proofs need.  The same emulation cardinalScript uses.
   ---------------------------------------------------------------------- *)

fun simp ths = simpLib.ASM_SIMP_TAC (srw_ss()) ths
fun csimp ths = simp (SF CONJ_ss :: ths)
fun dsimp ths = simp (SF DNF_ss :: ths)
fun gs ths = simpLib.global_simp_tac
               {elimvars = false, strip = true, droptrues = true,
                oldestfirst = true} (srw_ss()) ths
fun gvs ths = simpLib.global_simp_tac
                {elimvars = true, strip = true, droptrues = true,
                 oldestfirst = true} (srw_ss()) ths
fun rw ths = BasicProvers.SRW_TAC [] ths
val metis_tac = metisLib.METIS_TAC
fun SRULE ths th = SIMP_RULE (srw_ss()) ths th
val qexists = Q.EXISTS_TAC

(* The construction counts in ordinals, whose notation ordinalTheory
   exports and this theory must not: everything that declares a datatype
   loads this one.  So the notation is here for these proofs alone. *)
Overload "<"[local] = “ordlt”
Overload "<="[local] = “\a b. ~ordlt b a”
Overload "+"[local] = “ordADD”
Overload "ω"[local] = “omega”
Overload islimit[local] = “\a:'a ordinal. omax (preds a) = NONE”
Overload TC[local] = “ordSUC”   (* which is what writes a successor a⁺ *)
(* and the same for the sets' own exponent, which cardinalTheory keeps
   to itself for the same reason *)
Overload "**"[local] = “set_exp”
val _ = temp_add_numeral_form (#"o", SOME "fromNat")
val op >~ = Q.>~
val op >>~ = Q.>>~


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
  bnfFIN (sta : 'f -> 'a set) As = { a : 'f | sta a ⊆ As }
End

Theorem IN_FIN[simp]:
  a ∈ bnfFIN sta As ⇔ sta a ⊆ As
Proof
  simp[FIN_def]
QED

Theorem FIN_UNIV[simp]:
  bnfFIN sta UNIV = UNIV
Proof
  simp[EXTENSION]
QED

Definition ALG_def:
  bnfALG (sta : 'f -> 'a set) (A, s) ⇔ ∀x. x ∈ bnfFIN sta A ⇒ s x ∈ A
End

(* the pointwise form: ALG_def's own right-hand side has a leading
   quantifier, which no backward step can match against a goal about one
   element *)
Theorem ALG_closed:
  bnfALG sta (A,s) ∧ sta x ⊆ A ⇒ s x ∈ A
Proof
  simp[ALG_def]
QED

Theorem ALG_UNIV[simp]:
  bnfALG sta (UNIV, s)
Proof
  simp[ALG_def]
QED

Definition MINSET_def:
  bnfMINSET (sta : 'f -> 'a set) s = BIGINTER { B | bnfALG sta (B,s) }
End

Theorem MINSET_is_ALG[simp]:
  bnfALG sta (bnfMINSET sta s, s)
Proof
  simp[MINSET_def, ALG_def, SUBSET_BIGINTER]
QED

Theorem IN_MINSET:
  x ∈ bnfMINSET sta s ⇔ ∀A. bnfALG sta (A,s) ⇒ x ∈ A
Proof
  simp[MINSET_def]
QED

Definition HOM_def:
  bnfHOM (mp : ('a -> 'b) -> 'f -> 'g) sta stb h (A,s) (B,t) ⇔
    bnfALG sta (A,s) ∧ bnfALG stb (B,t) ∧ (∀a. a ∈ A ⇒ h a ∈ B) ∧
    ∀af. af ∈ bnfFIN sta A ⇒ t (mp h af) = h (s af)
End

(* ----------------------------------------------------------------------
    The BNF laws, as predicates over the parameters.  Each names the
    instances it relates, so a lemma can ask for exactly the ones it
    needs.
   ---------------------------------------------------------------------- *)

Definition MapId_def:
  bnfMapId (mp : ('a -> 'a) -> 'f -> 'f) ⇔ ∀x. mp I x = x
End

Definition MapComp_def:
  bnfMapComp (mp_ab : ('a -> 'b) -> 'f -> 'g)
          (mp_bc : ('b -> 'c) -> 'g -> 'h)
          (mp_ac : ('a -> 'c) -> 'f -> 'h) ⇔
    ∀f g x. mp_bc g (mp_ab f x) = mp_ac (g o f) x
End

Definition Natural_def:
  bnfNatural (mp : ('a -> 'b) -> 'f -> 'g) sta stb ⇔
    ∀f x. stb (mp f x) = IMAGE f (sta x)
End

Definition MapCong_def:
  bnfMapCong (mp : ('a -> 'b) -> 'f -> 'g) sta ⇔
    ∀f g x. (∀a. a ∈ sta x ⇒ f a = g a) ⇒ mp f x = mp g x
End

(* bnfMapCong comes first because it fixes both mp and sta, so drule can
   resolve it against an assumption and know what the rest means *)
Theorem Map_eq_id:
  bnfMapCong mp sta ∧ bnfMapId mp ⇒
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
  (∃w:'f. sta w = ∅) ⇒ bnfALG sta (A, s) ⇒ A ≠ ∅
Proof
  rpt strip_tac >> gvs[ALG_def] >> metis_tac[SUBSET_REFL, NOT_IN_EMPTY]
QED

Theorem HOMs_on_same_domain:
  bnfMapCong mp sta ⇒
  bnfHOM mp sta stb h (A,s) (B,t) ∧ (∀a. a ∈ A ⇒ h' a = h a) ⇒
  bnfHOM mp sta stb h' (A,s) (B,t)
Proof
  simp[HOM_def, MapCong_def] >> rw[] >>
  ‘s af ∈ A’ by gs[ALG_def] >> simp[] >>
  ‘mp h' af = mp h af’ suffices_by simp[] >>
  first_x_assum irule >> metis_tac[SUBSET_DEF]
QED

(* Combine assumptions with a rule, forward: the assumptions are named
   by pattern and MATCH_MPed into the rule in the order its antecedents
   appear.  irule cannot do these steps, because a composition's
   intermediate carrier does not appear in the conclusion, and HOL
   cannot leave a *type* existentially quantified. *)
fun byrule rule pats ttac =
    let fun recurse acc [] = ttac (MATCH_MP rule (LIST_CONJ (List.rev acc)))
          | recurse acc (p::ps) = qpat_assum p (fn th => recurse (th::acc) ps)
    in recurse [] pats end

(* the intermediate algebra and everything about it is quantified out
   in front: none of it appears in the conclusion, so irule leaves it
   existential in this order for a use site to name *)
Theorem HOMs_compose:
  ∀stb mp_ab mp_bc (B:'b set) t.
    bnfMapComp mp_ab mp_bc mp_ac ∧ bnfNatural mp_ab sta stb ∧
    bnfHOM mp_ab sta stb f (A:'a set,s) (B,t) ∧
    bnfHOM mp_bc stb stc g (B,t) (C:'c set,u) ⇒
    bnfHOM mp_ac sta stc (g o f) (A,s) (C,u)
Proof
  simp[MapComp_def, Natural_def] >> rpt gen_tac >> strip_tac >>
  gs[HOM_def] >> rw[] >>
  ‘stb (mp_ab f af) ⊆ B’ by (simp[] >> gs[SUBSET_DEF, PULL_EXISTS]) >>
  qpat_x_assum ‘∀af. stb af ⊆ B ⇒ _’ (qspec_then ‘mp_ab f af’ assume_tac) >>
  qpat_x_assum ‘∀af. sta af ⊆ A ⇒ _’ (qspec_then ‘af’ assume_tac) >>
  gs[]
QED

Theorem MINSET_ind:
  ∀P. (∀x. sta x ⊆ bnfMINSET sta s ∧ (∀y. y ∈ sta x ⇒ P y) ⇒ P (s x)) ⇒
      ∀x. x ∈ bnfMINSET sta s ⇒ P x
Proof
  gen_tac >> strip_tac >>
  ‘bnfMINSET sta s ⊆ P INTER bnfMINSET sta s’
    suffices_by simp[SUBSET_DEF, IN_DEF] >>
  simp[MINSET_def, SimpL “$SUBSET”] >> irule BIGINTER_SUBSET >>
  qexists_tac ‘P INTER bnfMINSET sta s’ >>
  simp[ALG_def, SUBSET_DEF] >> rw[]
  >- gs[IN_DEF, SUBSET_DEF] >>
  ntac 2 (last_x_assum (K ALL_TAC)) >>
  gs[ALG_def, SUBSET_DEF, IN_MINSET]
QED

Theorem MINSET_ind':
  ∀P. (∀x. (∀y. y ∈ sta x ⇒ y ∈ bnfMINSET sta s ∧ P y) ⇒ P (s x)) ⇒
      ∀x. x ∈ bnfMINSET sta s ⇒ P x
Proof
  metis_tac[MINSET_ind, SUBSET_DEF]
QED

Theorem MINSET_unique_homs:
  bnfMapCong mp sta ∧
  bnfHOM mp sta stb h1 (bnfMINSET sta s, s) (B,t) ∧
  bnfHOM mp sta stb h2 (bnfMINSET sta s, s) (B,t) ⇒
  ∀a. a ∈ bnfMINSET sta s ⇒ h1 a = h2 a
Proof
  simp[MapCong_def] >> strip_tac >>
  ho_match_mp_tac MINSET_ind' >> gs[HOM_def] >>
  rpt strip_tac >> RULE_ASSUM_TAC GSYM >> simp[] >> gs[SUBSET_DEF] >>
  AP_TERM_TAC >> first_x_assum irule >> simp[]
QED

Definition SUBALG_def:
  bnfSUBALG sta (A,s) (B,t) ⇔
    bnfALG sta (A,s) ∧ bnfALG sta (B,t) ∧
    (∀af. af ∈ bnfFIN sta A ⇒ s af = t af) ∧ A ⊆ B
End

Theorem SUBALGs_preserve_homs:
  bnfSUBALG sta A1 A2 ∧ bnfHOM mp sta stb f A2 C ⇒ bnfHOM mp sta stb f A1 C
Proof
  Cases_on ‘A1’ >> Cases_on ‘A2’ >> Cases_on ‘C’ >>
  simp[HOM_def, SUBALG_def] >> metis_tac[SUBSET_DEF]
QED

Theorem MINSET_SUBALG:
  bnfALG sta (A,s) ⇒ bnfSUBALG sta (bnfMINSET sta s, s) (A,s)
Proof
  simp[SUBALG_def, MINSET_def] >> strip_tac >>
  irule BIGINTER_SUBSET >> simp[] >> metis_tac[SUBSET_REFL]
QED

Theorem MINSET_I_HOM:
  bnfMapId mp ⇒ bnfALG sta (A,s) ⇒ bnfHOM mp sta sta I (bnfMINSET sta s, s) (A,s)
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
  bnfMKALG (sta : 'f -> 'a set) p = if bnfALG sta p then p else (UNIV, SND p)
End

Theorem MKALG_ALG[simp]:
  bnfALG sta (bnfMKALG sta p)
Proof
  rw[MKALG_def] >> Cases_on ‘p’ >> simp[]
QED

Theorem MKALG_ID:
  bnfALG sta p ⇒ bnfMKALG sta p = p
Proof
  simp[MKALG_def]
QED

Definition BIGPROD_def:
  bnfBIGPROD (mp : ((('a set # ('f -> 'a)) -> 'a) -> 'a) -> 'fp -> 'f) sta =
    ({ ff : ('a set # ('f -> 'a)) -> 'a | ∀i. ff i ∈ FST (bnfMKALG sta i) },
     λ(fv:'fp) i. SND (bnfMKALG sta i) (mp (λff. ff i) fv))
End

Theorem BIGPROD_ALG[simp]:
  bnfNatural mp stp sta ⇒ bnfALG stp (bnfBIGPROD mp sta)
Proof
  simp[Natural_def] >> strip_tac >>
  simp[BIGPROD_def, ALG_def] >> rpt strip_tac >>
  Cases_on ‘bnfMKALG sta i’ >> rename [‘bnfMKALG sta i = (A,s)’] >>
  ‘bnfALG sta (A,s)’ by metis_tac[MKALG_ALG] >> simp[] >>
  gs[ALG_def] >> first_assum irule >>
  gs[SUBSET_DEF, PULL_EXISTS] >> metis_tac[FST]
QED

Theorem BIGPROD_proj:
  bnfNatural mp stp sta ⇒
  bnfALG sta (A,s) ⇒
  bnfHOM mp stp sta (λff. ff (A,s)) (bnfBIGPROD mp sta) (A,s)
Proof
  strip_tac >> strip_tac >> simp[HOM_def, BIGPROD_def] >> rpt strip_tac
  >- metis_tac[BIGPROD_ALG, BIGPROD_def]
  >- (‘bnfMKALG sta (A,s) = (A,s)’ by metis_tac[MKALG_ID] >>
      first_x_assum $ qspec_then ‘(A,s)’ mp_tac >> simp[]) >>
  ‘bnfMKALG sta (A,s) = (A,s)’ by metis_tac[MKALG_ID] >> simp[]
QED

(* ----------------------------------------------------------------------
    Traytel's K function (MSc thesis, p 15): iterate the algebra's
    operation through the ordinals until it closes off.
   ---------------------------------------------------------------------- *)

val KK_def = new_specification(
  "KK_def", ["bnfKK"],
  ord_RECURSION |> Q.ISPEC ‘∅ : 'c set’
                |> Q.SPEC ‘λx r. r ∪ { s(x) | sta x ⊆ r }’
                |> Q.SPEC ‘λx rs. BIGUNION rs’
                |> SRULE[]
                |> Q.GENL [‘sta’, ‘s’]
                |> CONV_RULE (BINDER_CONV SKOLEM_CONV THENC SKOLEM_CONV));

Theorem KK_mono:
  ∀b a. a < b ⇒ bnfKK sta s a ⊆ bnfKK sta s b
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
  ∀a b. a ≤ b ⇒ bnfKK sta s a ⊆ bnfKK sta s b
Proof
  metis_tac[SUBSET_REFL, KK_mono, ordle_lteq]
QED

Theorem KK_SUB_MINSET:
  ∀a. bnfKK sta s a ⊆ bnfMINSET sta s
Proof
  ho_match_mp_tac simple_ord_induction >> simp[KK_def] >> rw[]
  >- (simp[SUBSET_DEF, PULL_EXISTS] >> rpt strip_tac >>
      ‘bnfALG sta (bnfMINSET sta s, s)’ by simp[] >>
      gs[ALG_def, Excl "MINSET_is_ALG"] >>
      metis_tac[SUBSET_DEF]) >>
  simp[SUBSET_DEF, PULL_EXISTS] >> metis_tac[SUBSET_DEF]
QED

Theorem KK_fixp_is_ALG:
  { s x | x | sta x ⊆ bnfKK sta s e } = bnfKK sta s e ⇒ bnfALG sta (bnfKK sta s e, s)
Proof
  rw[ALG_def] >> gs[EXTENSION] >> metis_tac[]
QED

Theorem KK_sup:
  ords ≼ 𝕌(:num + 'g) ⇒
  bnfKK sta s (sup ords : 'g ordinal) = BIGUNION (IMAGE (bnfKK sta s) ords)
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
  BIGUNION (IMAGE (bnfKK sta s) (preds a)) ⊆ bnfKK sta s a
Proof
  qid_spec_tac ‘a’ >> ho_match_mp_tac simple_ord_induction >>
  rw[]
  >- (simp[KK_def, preds_ordSUC] >> irule SUBSET_TRANS >> goal_assum drule >>
      simp[]) >>
  simp[KK_def]
QED

Theorem KK_thm:
  bnfKK sta s a = if a = 0 then ∅
               else BIGUNION (IMAGE (λb. { s fv | fv | sta fv ⊆ bnfKK sta s b})
                              (preds a))
Proof
  qid_spec_tac ‘a’ >> ho_match_mp_tac simple_ord_induction >>
  rw[]
  >- simp[KK_def]
  >- (simp[preds_nat] >> ‘count 1 = {0}’ by simp[EXTENSION] >>
      simp[KK_def, GSYM ORD_ONE, Excl "ORD_ONE"])
  >- (qpat_x_assum ‘bnfKK _ _ _ = BIGUNION _’ (assume_tac o SYM) >>
      simp[KK_def, preds_ordSUC, UNION_COMM]) >>
  pop_assum (assume_tac o GSYM) >>
  simp[KK_def] >> irule SUBSET_ANTISYM >> conj_tac >>
  simp[Once SUBSET_DEF, PULL_EXISTS]
  >- (rpt strip_tac >> rename [‘v ∈ bnfKK sta s b’] >>
      ‘b ≠ 0’ by (strip_tac >> gs[KK_def]) >>
      ‘bnfKK sta s b = BIGUNION (IMAGE (λb0. { s fv | fv | sta fv ⊆ bnfKK sta s b0})
                              (preds b))’ by metis_tac[] >>
      gs[PULL_EXISTS] >> metis_tac[ordlt_TRANS]) >>
  rpt strip_tac >> rename [‘b < a’, ‘sta fv ⊆ bnfKK sta s b’] >>
  qexists_tac ‘b⁺’ >> simp[KK_def] >> metis_tac[islimit_SUC_lt]
QED

(* ----------------------------------------------------------------------
    The iteration closes off by csuc of the functor's bound.
   ---------------------------------------------------------------------- *)

Theorem sucbnd_suffices:
  ω ≤ (bd : 'g ordinal) ∧ (∀x : 'f. sta x ≼ preds bd) ⇒
  bnfALG sta (bnfKK sta (s : 'f -> 'a) (csuc bd), s)
Proof
  strip_tac >>
  ‘INFINITE (preds bd)’ by (simp[FINITE_preds] >> rpt strip_tac >> gvs[]) >>
  irule KK_fixp_is_ALG >> irule SUBSET_ANTISYM >> conj_tac >>
  ONCE_REWRITE_TAC [SUBSET_DEF] >> simp[PULL_EXISTS] >>
  rpt strip_tac
  >- (rename [‘s fv ∈ bnfKK sta s _’] >>
      drule_then strip_assume_tac csuc_is_nonzero_limit >>
      simp[KK_def, PULL_EXISTS, lt_csuc] >>
      gs[SUBSET_DEF, KK_def, PULL_EXISTS, lt_csuc] >>
      gs[GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] >>
      rename [‘_ ∈ bnfKK sta s (g _)’, ‘preds (g _) ≼ preds bd’] >>
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
      ‘bnfKK sta s B = BIGUNION (IMAGE (bnfKK sta s) (IMAGE g (sta fv)))’
        by simp[KK_sup, Abbr‘B’] >> disj2_tac >>
      qexists_tac ‘fv’ >> simp[SUBSET_DEF, PULL_EXISTS] >> metis_tac[]) >>
  rename [‘v ∈ bnfKK sta s (csuc bd)’] >>
  drule_then strip_assume_tac csuc_is_nonzero_limit >>
  gvs[KK_def] >>
  rename [‘v ∈ bnfKK sta s a’, ‘a < csuc bd’] >>
  qpat_x_assum ‘v ∈ bnfKK sta s a’ mp_tac >> simp[Once KK_thm] >> rw[] >>
  gs[] >> qexists_tac ‘fv’ >> simp[] >> irule SUBSET_BIGUNION_SUBSET_I >>
  simp[PULL_EXISTS] >> metis_tac[ordlt_TRANS]
QED

(* mp has to be annotated into the same instance as sta and s: the
   parameterisation makes that explicit where a real functor would have
   made it implicit *)
Theorem KKbnd_EQ_MINSET:
  bnfMapId (mp : ('a -> 'a) -> 'f -> 'f) ⇒
  ω ≤ (bd : 'g ordinal) ∧ (∀x : 'f. (sta : 'f -> 'a set) x ≼ preds bd) ⇒
  bnfKK sta (s : 'f -> 'a) (csuc bd) = bnfMINSET sta s
Proof
  strip_tac >> strip_tac >>
  drule_all_then (qspec_then ‘s’ assume_tac) sucbnd_suffices >>
  irule SUBSET_ANTISYM >> simp[KK_SUB_MINSET] >>
  ‘bnfHOM mp sta sta I (bnfMINSET sta s, s) (bnfKK sta s (csuc bd), s)’
    by (irule MINSET_I_HOM >> simp[]) >>
  gs[HOM_def, SUBSET_DEF]
QED

(* ----------------------------------------------------------------------
    Because F is not constant, an algebra's carrier is no bigger than the
    collection of F-values over it.
   ---------------------------------------------------------------------- *)

Theorem NontrivialBs:
  bnfNatural (mp : ('c -> 'a) -> 'h -> 'f) stc sta ⇒
  (∃x:'h. stc x ≠ ∅) ⇒
  ∀B:'a set. B ≼ bnfFIN sta B
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
  s ⊆ t ⇒ (bnfFIN sta s : 'f set) ⊆ bnfFIN sta t
Proof
  simp[SUBSET_DEF] >> metis_tac[]
QED

Theorem FIN_cardleq:
  bnfMapId (mp_aa : ('a -> 'a) -> 'f -> 'f) ∧ bnfMapCong mp_aa sta ∧
  bnfNatural (mp_ab : ('a -> 'b) -> 'f -> 'g) sta stb ∧
  bnfMapComp mp_ab (mp_ba : ('b -> 'a) -> 'g -> 'f) mp_aa ⇒
  s ≼ t ⇒ (bnfFIN sta s : 'f set) ≼ (bnfFIN stb t : 'g set)
Proof
  strip_tac >>
  drule_then (drule_then assume_tac) Map_eq_id >>
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

(* ----------------------------------------------------------------------
    The cardinality bound.  Beyond the map and set functions this needs
    F at the ordinal carrier as well, and the facts it uses about
    nontriviality are taken as hypotheses rather than re-derived, so the
    driver discharges them once with NontrivialBs.

    See Lemma 33 of Blanchette, Popescu and Traytel, "Cardinals in
    Isabelle/HOL", ITP 2014.
   ---------------------------------------------------------------------- *)

Overload "𝟙"[local] = “{()}”

(* CARDEQ_IMP_CARDLEQ and cardleq_INFINITE duplicate cardinalTheory's
   CARDEQ_SUBSET_CARDLEQ and CARD_LE_INFINITE, which this theory already
   has as an ancestor; they should be dropped in favour of those.  The
   two below them are genuine local instantiations. *)
Theorem CARDEQ_IMP_CARDLEQ[local]:
  ∀s t. s ≈ t ⇒ s ≼ t
Proof
  metis_tac[cardleq_lteq]
QED

Theorem ordlt_preds_mono[local]:
  a < b ⇒ preds a ≼ preds b
Proof
  strip_tac >> irule CARD_LE_SUBSET >> simp[SUBSET_DEF] >>
  metis_tac[ordlt_TRANS]
QED

Theorem cardleq_INFINITE[local]:
  ∀s t. INFINITE s ∧ s ≼ t ⇒ INFINITE t
Proof
  metis_tac[CARD_LE_FINITE]
QED

Theorem CBDb:
  bnfNatural (mp_a2o : ('a -> 'g ordinal) -> 'f -> 'fo) sta sto ∧
  bnfNatural (mp_o2a : ('g ordinal -> 'a) -> 'fo -> 'f) sto sta ∧
  bnfMapComp mp_a2o mp_o2a (mp_aa : ('a -> 'a) -> 'f -> 'f) ∧
  bnfMapId mp_aa ∧ bnfMapCong mp_aa sta ∧
  (∀C : 'g ordinal set. C ≼ bnfFIN sto C) ⇒
  ω ≤ (bd : 'g ordinal) ∧ (∀x:'f. sta x ≼ preds bd) ⇒
  ∀B:'a set. 𝟚 ≼ B ⇒
             (bnfFIN sta B : 'f set) ≼ B ** cardSUC (bnfFIN sto (preds bd))
Proof
  strip_tac >>
  drule_then (drule_then assume_tac) Map_eq_id >>
  rpt strip_tac >>
  qabbrev_tac ‘kA = (bnfFIN sto (preds bd) : 'fo set) CROSS (B ** preds bd)’ >>
  qmatch_abbrev_tac ‘_ ≼ B ** k’ >>
  ‘kA ≼ B ** k’
    by (simp[Abbr‘k’, Abbr‘kA’] >> irule CARD_MUL2_ABSORB_LE >>
        simp[] >> rpt strip_tac >~
        [‘𝟚 ≼ B’, ‘B ≼ 𝟙’] >- (drule_all cardleq_TRANS >> simp[]) >~
        [‘INFINITE (bnfFIN sto (preds bd))’]
        >- (disj2_tac >>
            irule (ISPEC “preds (bd:'g ordinal)” cardleq_INFINITE) >>
            qexists_tac ‘bd’ >> conj_tac
            >- (simp[FINITE_preds] >> rpt strip_tac >> gvs[]) >>
            simp[]) >~
        [‘bnfFIN sto (preds bd) ≼ B ** cardSUC _’]
        >- (resolve_then (Pos last) irule CARD_LE_EXP cardleq_TRANS >>
            simp[]) >>
        irule set_exp_cardle_cong >> simp[] >> rpt strip_tac >>
        gvs[cardleq_empty] >>
        first_x_assum $ qspec_then ‘preds bd’ assume_tac >>
        first_x_assum $ C (resolve_then (Pos hd) irule) cardleq_TRANS >>
        simp[]) >>
  first_assum $ C (resolve_then (Pos last) irule) cardleq_TRANS >>
  qabbrev_tac ‘d = λ(y:'fo,fn). mp_o2a fn y’ >>
  simp[cardleq_def] >>
  irule_at Any (SRULE [PULL_EXISTS] SURJ_IMP_INJ) >> qexists_tac ‘d’ >>
  simp[SURJ_DEF] >> conj_tac
  >- (simp[FORALL_PROD, Abbr‘kA’, Abbr‘d’, set_exp_def] >>
      gs[Natural_def] >> rw[] >> simp[SUBSET_DEF, PULL_EXISTS] >>
      qx_gen_tac ‘b’ >> strip_tac >>
      ‘b ∈ preds bd’ by metis_tac[SUBSET_DEF] >> gs[] >>
      first_assum drule >> simp[PULL_EXISTS]) >>
  qx_gen_tac ‘vf’ >> strip_tac >>
  ‘?g. INJ g (sta vf) (preds bd)’ by metis_tac[cardleq_def] >>
  qabbrev_tac ‘y = mp_a2o g vf’ >>
  ‘sta vf ⊆ B’ by gs[] >>
  ‘?fn. (!b. b ∈ sta vf ⇒ fn (g b) = b) /\ (!bp. bp < bd ==> fn bp ∈ B)’
    by (‘?be. be ∈ B’ by (simp[MEMBER_NOT_EMPTY] >>
                          strip_tac >> gvs[cardleq_empty]) >>
        qexists_tac ‘λbp. case some b. b IN sta vf /\ g b = bp of
                            NONE => be
                          | SOME b => b
                    ’ >> conj_tac >> simp[] >> rpt strip_tac
        >- (gs[INJ_IFF, SF CONJ_ss] >> csimp[]) >>
        DEEP_INTRO_TAC optionTheory.some_intro >> simp[] >>
        gs[SUBSET_DEF]) >>
  qexists_tac ‘(y, λbp. if bp ∈ preds bd then fn bp else ARB)’ >>
  conj_tac
  >- (simp[Abbr‘kA’, Abbr‘y’] >> gs[Natural_def] >> conj_tac
      >- gs[INJ_IFF, SUBSET_DEF, PULL_EXISTS] >>
      simp[set_exp_def]) >>
  simp[Abbr‘d’, Abbr‘y’] >> gs[MapComp_def] >>
  first_x_assum irule >> simp[] >> gs[INJ_IFF]
QED

Theorem preds_bd_lemma:
  (∀C : 'g ordinal set. C ≼ bnfFIN sto C) ⇒
  preds (bd:'g ordinal) ≼
  preds (oleast a:'fo ordinal. preds a ≈ (bnfFIN sto (preds bd) : 'fo set))
Proof
  strip_tac >> first_x_assum (qspec_then ‘preds bd’ assume_tac) >>
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

(* the middle set of a cardleq_TRANS chain has a type of its own, and
   irule cannot guess it; INST_TYPE says which one is meant *)
Theorem preds_cardSUC_cardleq[local]:
  preds (i:'i ordinal) ≼ preds (bd:'bo ordinal) ∧
  preds bd ≼ preds (oleast a:'fo ordinal. preds a ≈ (Q : 'fo set)) ⇒
  preds i ≼ cardSUC Q
Proof
  simp[cardSUC_def] >> strip_tac >>
  irule (INST_TYPE [beta |-> “:'bo ordinal”] cardleq_TRANS) >>
  qexists_tac ‘preds bd’ >> simp[] >>
  irule (INST_TYPE [beta |-> “:'fo ordinal”] cardleq_TRANS) >>
  qexists_tac ‘preds (oleast a:'fo ordinal. preds a ≈ Q)’ >> simp[] >>
  MATCH_ACCEPT_TAC preds_csuc_lemma
QED

Theorem cardADD2[local]:
  s ≼ s +_c 𝟚
Proof
  simp[CARD_LE_ADDR]
QED

(* The bound on the iteration.  This asks only for the *conclusions* of
   FIN_cardleq and CBDb at the instances it uses, so the driver chains
   the lemmas rather than re-supplying their hypotheses here. *)
Theorem ALG_cardinality_bound:
  (∀C : 'g ordinal set. C ≼ bnfFIN sto C) ∧
  (∀u:'a set. ∀v:('a + bool) set.
     u ≼ v ⇒ (bnfFIN sta u : 'f set) ≼ (bnfFIN stab v : 'fab set)) ∧
  (∀B : ('a + bool) set.
     𝟚 ≼ B ⇒ (bnfFIN stab B : 'fab set) ≼ B ** cardSUC (bnfFIN sto (preds bd))) ⇒
  ω ≤ (bd : 'g ordinal) ⇒
  bnfKK sta (s : 'f -> 'a) (csuc bd) ≼ 𝟚 ** cardSUC (bnfFIN sto (preds bd))
Proof
  strip_tac >> strip_tac >>
  qmatch_abbrev_tac ‘_ ≼ 𝟚 ** BD’ >>
  ‘INFINITE BD’
    by (simp[Abbr‘BD’] >>
        irule (ISPEC “preds (bd:'g ordinal)” cardleq_INFINITE) >>
        qexists_tac ‘bd’ >> conj_tac
        >- (simp[FINITE_preds] >> rpt strip_tac >> gvs[]) >>
        simp[]) >>
  ‘BD ≠ ∅’ by (rpt strip_tac >> gs[]) >>
  qpat_assum ‘∀C. _ ≼ bnfFIN sto _’ (assume_tac o MATCH_MP preds_bd_lemma) >>
  ‘∀i. i < csuc bd ⇒ bnfKK sta s i ≼ 𝟚 ** BD’
    suffices_by (strip_tac >> simp[KK_def, csuc_is_nonzero_limit] >>
                 irule CARD_BIGUNION >> simp[PULL_EXISTS] >>
                 irule IMAGE_cardleq_rwt >>
                 resolve_then Any
                              (fn th =>
                                 resolve_then (Pos hd) irule th cardleq_TRANS)
                              cardleq_REFL
                              CARD_LE_EXP >>
                 irule set_exp_cardle_cong >> simp[Abbr‘BD’, cardSUC_def] >>
                 irule cardleq_preds_csuc >> simp[]) >>
  ho_match_mp_tac ord_induction >> rw[] >>
  simp[Once KK_thm] >> rw[] >> irule CARD_BIGUNION >>
  simp[PULL_EXISTS] >> rpt conj_tac >~
  [‘IMAGE _ (preds i) ≼ _’]
  >- (irule IMAGE_cardleq_rwt >> gs[lt_csuc] >>
      resolve_then Any
                   (fn th =>
                      resolve_then (Pos hd) irule th cardleq_TRANS)
                   cardleq_REFL
                   CARD_LE_EXP >> irule set_exp_cardle_cong >> simp[] >>
      simp[Abbr‘BD’] >>
      drule_all_then MATCH_ACCEPT_TAC preds_cardSUC_cardleq) >>
  qx_gen_tac ‘j’ >> strip_tac >>
  ‘{ s fv | fv | sta fv ⊆ bnfKK sta s j} = IMAGE s (bnfFIN sta (bnfKK sta s j))’
    by simp[EXTENSION] >> simp[] >>
  irule IMAGE_cardleq_rwt >>
  ‘(bnfFIN sta (bnfKK sta s j) : 'f set) ≼ (bnfFIN stab (bnfKK sta s j +_c 𝟚) : 'fab set)’
    by (first_x_assum irule >> simp[CARD_LE_ADDR]) >>
  pop_assum (C (resolve_then (Pos hd) irule) cardleq_TRANS) >>
  first_x_assum (qspec_then ‘bnfKK sta s j +_c 𝟚’ mp_tac) >>
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
    An algebra can be copied onto any carrier big enough to hold it.
   ---------------------------------------------------------------------- *)

(* mp_aa and B are quantified out in front because neither appears in
   the conclusion: irule then turns them into existentials in this
   order, so a use site can name them with qexistsl_tac rather than
   leaving them to be guessed *)
Theorem copy_alg_back:
  ∀(mp_aa : ('a -> 'a) -> 'f -> 'f) (B : 'b set).
    bnfNatural (mp_ba : ('b -> 'a) -> 'g -> 'f) stb sta ∧
    bnfNatural (mp_ab : ('a -> 'b) -> 'f -> 'g) sta stb ∧
    bnfMapComp mp_ab mp_ba mp_aa ∧ bnfMapId mp_aa ∧ bnfMapCong mp_aa sta ∧
    (A:'a set) ≼ B ∧ bnfALG sta (A, s : 'f -> 'a) ⇒
    ∃(B0:'b set) (s' : 'g -> 'b) h j.
      bnfHOM mp_ba stb sta h (B0,s') (A,s) ∧
      bnfHOM mp_ab sta stb j (A,s) (B0,s') ∧
      (∀a. a ∈ A ⇒ h (j a) = a) ∧ (∀b. b ∈ B0 ⇒ j (h b) = b)
Proof
  rpt gen_tac >> simp[cardleq_def] >> strip_tac >>
  drule_then (drule_then assume_tac) Map_eq_id >>
  rename [‘INJ h0 A B’] >>
  qexistsl_tac [‘IMAGE h0 A’, ‘λbv. h0 (s (mp_ba (LINV h0 A) bv))’,
                ‘LINV h0 A’, ‘h0’] >>
  csimp[HOM_def, PULL_EXISTS] >>
  drule_then assume_tac LINV_DEF >> gs[Natural_def] >> rw[] >~
  [‘bnfALG stb (IMAGE h0 A, _)’]
  >- (gs[ALG_def, SUBSET_DEF] >> rw[] >>
      irule_at Any EQ_REFL >> first_assum irule >>
      simp[PULL_EXISTS] >> rw[] >> first_assum drule >>
      simp[PULL_EXISTS]) >~
  [‘LINV h0 A (h0 (s _))’]
  >- (‘s (mp_ba (LINV h0 A) bv) ∈ A’
        by (gs[ALG_def] >> first_assum irule >>
            gs[SUBSET_DEF, PULL_EXISTS] >> rw[] >>
            first_assum drule >> simp[PULL_EXISTS]) >>
      simp[]) >>
  gs[MapComp_def] >> ntac 2 AP_TERM_TAC >>
  first_x_assum irule >> gs[SUBSET_DEF]
QED

(* ----------------------------------------------------------------------
    The whole cardinality argument, as one theorem.

    Its hypotheses are BNF laws at three instances — the carrier 'a, the
    carrier extended by a point, and the ordinals that bound F's sets —
    plus F's non-triviality and the bound itself.  A package instantiates
    it and gets the one fact the construction needs: every minimal
    algebra fits inside a set fixed by F alone.
   ---------------------------------------------------------------------- *)

(* the step from the bound to a whole type, which is the form the
   construction's hypothesis takes *)
Theorem CARDLEQ_UNIV[simp]:
  ∀s : 'a set. s ≼ 𝕌(:'a)
Proof
  gen_tac >> irule SUBSET_CARDLEQ >> simp[]
QED

(* getting from F's own bound, which is a set, to an ordinal one *)
Theorem cardeq_preds_omega:
  INFINITE B ∧ preds (bd:'g ordinal) ≈ B ⇒ ω ≤ bd
Proof
  strip_tac >> irule omega_LEQ_INFINITE_preds >>
  metis_tac[CARD_FINITE_CONG]
QED

Theorem cardeq_preds_bound:
  preds (bd:'g ordinal) ≈ (B:'b set) ∧ (s:'s set) ≼ B ⇒ s ≼ preds bd
Proof
  strip_tac >> irule (INST_TYPE [beta |-> “:'b”] cardleq_TRANS) >>
  qexists_tac ‘B’ >> simp[] >> irule CARDEQ_IMP_CARDLEQ >>
  simp[Once cardeq_SYM]
QED

Theorem MINSET_CARDLEQ:
  bnfMapId (mp_aa : ('a -> 'a) -> 'f -> 'f) ∧ bnfMapCong mp_aa sta ∧
  bnfNatural (mp_ab : ('a -> 'a + bool) -> 'f -> 'fab) sta stab ∧
  bnfMapComp mp_ab (mp_ba : ('a + bool -> 'a) -> 'fab -> 'f) mp_aa ∧
  bnfMapId (mp_bb : ('a + bool -> 'a + bool) -> 'fab -> 'fab) ∧
  bnfMapCong mp_bb stab ∧
  bnfNatural (mp_bo : ('a + bool -> 'g ordinal) -> 'fab -> 'fo) stab sto ∧
  bnfNatural (mp_ob : ('g ordinal -> 'a + bool) -> 'fo -> 'fab) sto stab ∧
  bnfMapComp mp_bo mp_ob mp_bb ∧
  bnfNatural (mp_oo : ('g ordinal -> 'g ordinal) -> 'fo -> 'fo) sto sto ∧
  (∃x : 'fo. sto x ≠ ∅) ∧
  ω ≤ (bd : 'g ordinal) ∧ (∀x. sta x ≼ preds bd) ∧
  (∀x. stab x ≼ preds bd) ⇒
  ∀s. bnfMINSET sta (s : 'f -> 'a) ≼ 𝟚 ** cardSUC (bnfFIN sto (preds bd))
Proof
  strip_tac >> gen_tac >>
  ‘∀C : 'g ordinal set. C ≼ bnfFIN sto C’
    by (byrule NontrivialBs [‘bnfNatural mp_oo sto sto’] irule >>
        qpat_assum ‘sto _ ≠ ∅’ (irule_at Any)) >>
  ‘∀u:'a set. ∀v:('a + bool) set.
     u ≼ v ⇒ (bnfFIN sta u : 'f set) ≼ (bnfFIN stab v : 'fab set)’
    by (rpt strip_tac >>
        byrule FIN_cardleq
          [‘bnfMapId mp_aa’, ‘bnfMapCong mp_aa sta’, ‘bnfNatural mp_ab sta stab’,
           ‘bnfMapComp mp_ab mp_ba mp_aa’]
          irule >> simp[]) >>
  ‘∀B : ('a + bool) set.
     𝟚 ≼ B ⇒ (bnfFIN stab B : 'fab set) ≼ B ** cardSUC (bnfFIN sto (preds bd))’
    by (byrule CBDb
          [‘bnfNatural mp_bo stab sto’, ‘bnfNatural mp_ob sto stab’,
           ‘bnfMapComp mp_bo mp_ob mp_bb’, ‘bnfMapId mp_bb’, ‘bnfMapCong mp_bb stab’,
           ‘∀C : 'g ordinal set. C ≼ bnfFIN sto C’]
          (fn th => mp_tac th >> simp[])) >>
  byrule KKbnd_EQ_MINSET [‘bnfMapId mp_aa’]
    (fn th => ‘bnfKK sta s (csuc bd) = bnfMINSET sta s’ by (irule th >> simp[])) >>
  pop_assum (SUBST1_TAC o SYM) >>
  byrule ALG_cardinality_bound
    [‘∀C : 'g ordinal set. C ≼ bnfFIN sto C’,
     ‘∀u:'a set. ∀v:('a + bool) set. u ≼ v ⇒ _’,
     ‘∀B : ('a + bool) set. 𝟚 ≼ B ⇒ _’]
    (fn th => irule th >> simp[])
QED

(* ----------------------------------------------------------------------
    The initial algebra: the minimal sub-algebra of the product of all
    algebras over the bounded carrier type.

    Both are parameterised by the same data as bnfBIGPROD, so nothing here
    is specific to a functor.
   ---------------------------------------------------------------------- *)

Definition ICONS_def:
  bnfICONS (mp : ((('a set # ('f -> 'a)) -> 'a) -> 'a) -> 'fp -> 'f) sta =
    SND (bnfBIGPROD mp sta)
End

Definition IALG_def:
  bnfIALG stp (mp : ((('a set # ('f -> 'a)) -> 'a) -> 'a) -> 'fp -> 'f) sta =
    bnfMINSET stp (bnfICONS mp sta)
End

Theorem BIGPROD_ALG'[simp]:
  bnfNatural mp stp sta ⇒ bnfALG stp (FST (bnfBIGPROD mp sta), bnfICONS mp sta)
Proof
  strip_tac >> drule BIGPROD_ALG >> simp[ICONS_def]
QED

Theorem BIGPROD_proj':
  bnfNatural mp stp sta ⇒ bnfALG sta (A,s) ⇒
  bnfHOM mp stp sta (λff. ff (A,s)) (FST (bnfBIGPROD mp sta), bnfICONS mp sta) (A,s)
Proof
  rpt strip_tac >> drule_all BIGPROD_proj >> simp[ICONS_def]
QED

Theorem IALG_ALG[simp]:
  bnfALG stp (bnfIALG stp mp sta, bnfICONS mp sta)
Proof
  simp[IALG_def]
QED

Theorem IALG_I_HOM:
  bnfMapId mp_pp ∧ bnfNatural mp_pa stp sta ⇒
  bnfHOM mp_pp stp stp I (bnfIALG stp mp_pa sta, bnfICONS mp_pa sta)
      (FST (bnfBIGPROD mp_pa sta), bnfICONS mp_pa sta)
Proof
  strip_tac >> simp[IALG_def] >> irule MINSET_I_HOM >> simp[]
QED

(* ----------------------------------------------------------------------
    Homomorphisms out of the initial algebra are unique only on its
    carrier, so pick the representative that is ARB elsewhere.
   ---------------------------------------------------------------------- *)

Definition ARBIFY_def:
  bnfARBIFY A f x = if x ∈ A then f x else ARB
End

Theorem HOM_ARBIFY:
  bnfMapCong mp sta ⇒
  (bnfHOM mp sta stb (bnfARBIFY A f) (A,s) (B,t) ⇔ bnfHOM mp sta stb f (A,s) (B,t))
Proof
  simp[MapCong_def] >> strip_tac >>
  simp[HOM_def, ARBIFY_def] >> Cases_on ‘bnfALG sta (A,s)’ >> simp[] >>
  ‘∀af. af ∈ bnfFIN sta A ⇒ s af ∈ A’ by gs[ALG_def] >> simp[] >>
  rw[EQ_IMP_THM] >> RULE_ASSUM_TAC GSYM >> simp[] >> AP_TERM_TAC >>
  first_x_assum irule >> simp[ARBIFY_def] >> gs[SUBSET_DEF]
QED

Theorem HOM_arbification:
  bnfMapCong mp sta ⇒
  bnfHOM mp sta stb h (A,s) (B,t) ⇒
  ∃j. bnfHOM mp sta stb j (A,s) (B,t) ∧ ∀x. x ∉ A ⇒ j x = ARB
Proof
  rpt strip_tac >> qexists_tac ‘bnfARBIFY A h’ >>
  simp[ARBIFY_def] >> drule (iffRL HOM_ARBIFY) >> simp[]
QED

(* ----------------------------------------------------------------------
    Existence of a homomorphism out of the initial algebra.

    The chain is
        bnfIALG --I--> bnfBIGPROD --proj--> (B0,s') --hh--> bnfMINSET stc t --I--> G
    where (B0,s') is the minimal sub-algebra of (G,t) copied onto the
    bounded carrier type 'a, which is what makes it an index of the
    product.
   ---------------------------------------------------------------------- *)

Theorem IALG_HOM_ANY:
  bnfNatural (mp_pa : ((('a set # ('f -> 'a)) -> 'a) -> 'a) -> 'fp -> 'f)
          stp sta ∧
  bnfNatural mp_pp stp stp ∧ bnfMapId mp_pp ∧ bnfMapComp mp_pp mp_pa mp_pa ∧
  bnfNatural mp_pc stp (stc : 'fc -> 'c set) ∧ bnfMapComp mp_pa mp_ac mp_pc ∧
  bnfMapComp mp_pc mp_cc mp_pc ∧
  bnfNatural mp_ac sta stc ∧ bnfNatural mp_ca stc sta ∧
  bnfMapComp mp_ca mp_ac mp_cc ∧ bnfMapId mp_cc ∧ bnfMapCong mp_cc stc ∧
  (∀t : 'fc -> 'c. bnfMINSET stc t ≼ 𝕌(:'a)) ⇒
  ∀t G. bnfALG stc (G,t) ⇒
        ∃h. bnfHOM mp_pc stp stc h (bnfIALG stp mp_pa sta, bnfICONS mp_pa sta) (G,t)
Proof
  strip_tac >> rpt strip_tac >>
  (* the minimal sub-algebra of (G,t), copied onto the bounded carrier *)
  ‘∃B0 s' hh jj.
     bnfHOM mp_ac sta stc hh (B0,s') (bnfMINSET stc t, t) ∧
     bnfHOM mp_ca stc sta jj (bnfMINSET stc t, t) (B0,s') ∧
     (∀a. a ∈ bnfMINSET stc t ⇒ hh (jj a) = a) ∧
     (∀b. b ∈ B0 ⇒ jj (hh b) = b)’
    by (irule copy_alg_back >> simp[] >> rpt conj_tac >~
        [‘bnfMINSET stc t ≼ _’] >- (qexists_tac ‘𝕌(:'a)’ >> simp[]) >>
        qexists_tac ‘mp_cc’ >> simp[]) >>
  ‘bnfALG sta (B0,s')’ by gs[HOM_def] >>
  (* being an algebra on the bounded carrier, (B0,s') indexes the
     product, so the product projects onto it *)
  ‘bnfHOM mp_pa stp sta (λff. ff (B0,s'))
       (FST (bnfBIGPROD mp_pa sta), bnfICONS mp_pa sta) (B0,s')’
    by (irule BIGPROD_proj' >> simp[]) >>
  ‘bnfHOM mp_pp stp stp I (bnfIALG stp mp_pa sta, bnfICONS mp_pa sta)
       (FST (bnfBIGPROD mp_pa sta), bnfICONS mp_pa sta)’
    by (irule IALG_I_HOM >> simp[]) >>
  byrule HOMs_compose
    [‘bnfMapComp mp_pp mp_pa mp_pa’, ‘bnfNatural mp_pp stp stp’,
     ‘bnfHOM mp_pp stp stp I _ _’, ‘bnfHOM mp_pa stp sta _ _ (B0,s')’]
    assume_tac >>
  byrule HOMs_compose
    [‘bnfMapComp mp_pa mp_ac mp_pc’, ‘bnfNatural mp_pa stp sta’,
     ‘bnfHOM mp_pa stp sta (_ o I) (bnfIALG stp mp_pa sta, _) _’,
     ‘bnfHOM mp_ac sta stc hh _ (bnfMINSET stc t, t)’]
    assume_tac >>
  ‘bnfHOM mp_cc stc stc I (bnfMINSET stc t, t) (G,t)’
    by (irule MINSET_I_HOM >> simp[]) >>
  byrule HOMs_compose
    [‘bnfMapComp mp_pc mp_cc mp_pc’, ‘bnfNatural mp_pc stp stc’,
     ‘bnfHOM mp_pc stp stc _ (bnfIALG stp mp_pa sta, _) (bnfMINSET stc t, t)’,
     ‘bnfHOM mp_cc stc stc I _ (G,t)’]
    (irule_at Any)
QED

(* ----------------------------------------------------------------------
    Initiality: the homomorphism out of the initial algebra into any
    other algebra exists and, once pinned down off the carrier, is
    unique.
   ---------------------------------------------------------------------- *)

(* the hypotheses are bnfMapCong followed by *exactly* IALG_HOM_ANY's, so
   the second conjunct of the bundle can be MATCH_MPed straight into
   that theorem with nothing left to guess *)
Theorem INITIALITY0:
  bnfMapCong mp_pc stp ∧
  (bnfNatural (mp_pa : ((('a set # ('f -> 'a)) -> 'a) -> 'a) -> 'fp -> 'f)
           stp sta ∧
   bnfNatural mp_pp stp stp ∧ bnfMapId mp_pp ∧ bnfMapComp mp_pp mp_pa mp_pa ∧
   bnfNatural mp_pc stp (stc : 'fc -> 'c set) ∧ bnfMapComp mp_pa mp_ac mp_pc ∧
   bnfMapComp mp_pc mp_cc mp_pc ∧
   bnfNatural mp_ac sta stc ∧ bnfNatural mp_ca stc sta ∧
   bnfMapComp mp_ca mp_ac mp_cc ∧ bnfMapId mp_cc ∧ bnfMapCong mp_cc stc ∧
   (∀t : 'fc -> 'c. bnfMINSET stc t ≼ 𝕌(:'a))) ⇒
  ∀t G.
    bnfALG stc (G,t) ⇒
    ∃!h. bnfHOM mp_pc stp stc h (bnfIALG stp mp_pa sta, bnfICONS mp_pa sta) (G,t) ∧
         ∀x. x ∉ bnfIALG stp mp_pa sta ⇒ h x = ARB
Proof
  (* the bundle is kept whole as well as split: the whole one is what
     applies forward to IALG_HOM_ANY *)
  disch_then (fn th => strip_assume_tac th >> assume_tac th) >>
  rpt strip_tac >> simp[EXISTS_UNIQUE_THM] >> conj_tac
  >- (irule HOM_arbification >> simp[] >>
      qpat_assum ‘bnfMapCong mp_pc stp ∧ _’
        (fn th => irule (MATCH_MP IALG_HOM_ANY (CONJUNCT2 th))) >>
      simp[]) >>
  rpt strip_tac >> simp[FUN_EQ_THM] >> qx_gen_tac ‘a’ >>
  Cases_on ‘a ∈ bnfIALG stp mp_pa sta’ >> simp[] >> gs[IALG_def] >>
  byrule MINSET_unique_homs
    [‘bnfMapCong mp_pc stp’,
     ‘bnfHOM mp_pc stp stc h _ _’, ‘bnfHOM mp_pc stp stc h' _ _’]
    (fn th => simp[th])
QED

(* ----------------------------------------------------------------------
    Lambek: an algebra with the initiality property has a bijective
    structure map.

    F's own carrier is a fourth instance: 'p is the algebra's carrier,
    'fp is F['p], and 'ffp is F['fp], the carrier of the algebra
    (bnfFIN stp A, mp_Fp s).
   ---------------------------------------------------------------------- *)

Theorem ALG_FIN:
  bnfNatural mp_Fp stF stp ⇒ bnfALG stp (A,s) ⇒ bnfALG stF (bnfFIN stp A, mp_Fp s)
Proof
  simp[Natural_def] >> rpt strip_tac >>
  simp[ALG_def, SUBSET_DEF, PULL_EXISTS] >> rw[] >>
  gs[ALG_def, SUBSET_DEF, PULL_EXISTS] >> metis_tac[]
QED

Theorem HOM_FIN:
  bnfNatural mp_Fp stF stp ⇒ bnfALG stp (A,s) ⇒
  bnfHOM mp_Fp stF stp s (bnfFIN stp A, mp_Fp s) (A,s)
Proof
  rpt strip_tac >> drule_all_then assume_tac ALG_FIN >>
  simp[HOM_def] >> gs[ALG_def]
QED

Theorem LAMBEK:
  bnfMapCong (mp_pp : ('p -> 'p) -> 'fp -> 'fp) stp ∧ bnfMapId mp_pp ∧
  bnfNatural (mp_Fp : ('fp -> 'p) -> 'ffp -> 'fp) stF stp ∧
  bnfMapComp (mp_pF : ('p -> 'fp) -> 'fp -> 'ffp) mp_Fp mp_pp ∧
  bnfMapCong mp_pF stp ∧ bnfNatural mp_pF stp stF ∧
  bnfALG stp (A,s) ∧
  (∀t G. bnfALG stF (G,t) ⇒
         ∃!h. bnfHOM mp_pF stp stF h (A,s) (G,t) ∧ ∀x. x ∉ A ⇒ h x = ARB) ∧
  (∀t G. bnfALG stp (G,t) ⇒
         ∃!h. bnfHOM mp_pp stp stp h (A,s) (G,t) ∧ ∀x. x ∉ A ⇒ h x = ARB) ⇒
  BIJ s (bnfFIN stp A) A
Proof
  strip_tac >>
  drule_all_then assume_tac ALG_FIN >>
  ‘bnfHOM mp_Fp stF stp s (bnfFIN stp A, mp_Fp s) (A,s)’
    by (irule HOM_FIN >> simp[]) >>
  (* the unique homomorphism into the algebra (bnfFIN stp A, mp_Fp s) *)
  qpat_x_assum ‘∀t G. bnfALG stF (G,t) ⇒ _’
    (qspecl_then [‘mp_Fp s’, ‘bnfFIN stp A’] mp_tac) >>
  simp[EXISTS_UNIQUE_ALT] >> disch_then (qx_choose_then ‘H’ assume_tac) >>
  ‘bnfHOM mp_pF stp stF H (A,s) (bnfFIN stp A, mp_Fp s) ∧ ∀x. x ∉ A ⇒ H x = ARB’
    by (first_assum (irule o iffRL) >> simp[]) >>
  byrule HOMs_compose
    [‘bnfMapComp mp_pF mp_Fp mp_pp’, ‘bnfNatural mp_pF stp stF’,
     ‘bnfHOM mp_pF stp stF H (A,s) _’, ‘bnfHOM mp_Fp stF stp s _ (A,s)’]
    assume_tac >>
  (* s o H and I are both endomorphisms of (A,s), so they agree on A *)
  ‘bnfHOM mp_pp stp stp (bnfARBIFY A (s o H)) (A,s) (A,s)’
    by (byrule HOM_ARBIFY [‘bnfMapCong mp_pp stp’] (fn th => simp[th])) >>
  ‘bnfHOM mp_pp stp stp (bnfARBIFY A I) (A,s) (A,s)’
    by (byrule HOM_ARBIFY [‘bnfMapCong mp_pp stp’] (fn th => simp[th]) >>
        simp[HOM_def] >> gs[MapId_def]) >>
  qpat_x_assum ‘∀t G. bnfALG stp (G,t) ⇒ _’
    (qspecl_then [‘s’, ‘A’] mp_tac) >>
  simp[EXISTS_UNIQUE_ALT] >> disch_then (qx_choose_then ‘K0’ assume_tac) >>
  ‘K0 = bnfARBIFY A (s o H) ∧ K0 = bnfARBIFY A I’
    by (conj_tac >> first_assum (irule o iffLR) >> simp[ARBIFY_def]) >>
  ‘∀a. a ∈ A ⇒ s (H a) = a’
    by (rpt strip_tac >> ‘bnfARBIFY A (s o H) a = bnfARBIFY A I a’ by metis_tac[] >>
        gs[ARBIFY_def]) >>
  simp[BIJ_IFF_INV] >> conj_tac >- gs[ALG_def] >>
  qexists_tac ‘H’ >> rpt conj_tac
  >- gs[HOM_def]
  >- (* H (s af) = af: push s o H through the map and use bnfMapId *)
     (qx_gen_tac ‘af’ >> strip_tac >>
      ‘mp_Fp s (mp_pF H af) = H (s af)’ by gs[HOM_def] >>
      pop_assum (SUBST1_TAC o SYM) >>
      ‘mp_Fp s (mp_pF H af) = mp_pp (s o H) af’ by gs[MapComp_def] >>
      pop_assum SUBST1_TAC >>
      byrule Map_eq_id [‘bnfMapCong mp_pp stp’, ‘bnfMapId mp_pp’] irule >>
      gs[SUBSET_DEF]) >>
  simp[]
QED

(* ----------------------------------------------------------------------
    What a type definition needs: the carrier is inhabited, and its
    elements are reachable, which is the induction principle.
   ---------------------------------------------------------------------- *)

Theorem IALG_NONEMPTY:
  (∃w. stp w = ∅) ⇒ bnfIALG stp mp_pa sta ≠ ∅
Proof
  strip_tac >> simp[GSYM MEMBER_NOT_EMPTY] >>
  qexists_tac ‘bnfICONS mp_pa sta w’ >> irule ALG_closed >>
  qexists_tac ‘stp’ >> simp[]
QED

(* the form new_type_definition wants: the carrier as a predicate *)
Theorem IALG_INHABITED:
  (∃w. stp w = ∅) ⇒ ∃x. bnfIALG stp mp_pa sta x
Proof
  strip_tac >>
  ‘bnfIALG stp mp_pa sta ≠ ∅’ by (irule IALG_NONEMPTY >> metis_tac[]) >>
  gs[GSYM MEMBER_NOT_EMPTY, IN_DEF] >> first_assum (irule_at Any)
QED

Theorem IALG_ind:
  ∀P. (∀x. stp x ⊆ bnfIALG stp mp_pa sta ∧ (∀y. y ∈ stp x ⇒ P y) ⇒
           P (bnfICONS mp_pa sta x)) ⇒
      ∀x. x ∈ bnfIALG stp mp_pa sta ⇒ P x
Proof
  simp[IALG_def] >> MATCH_ACCEPT_TAC MINSET_ind
QED

(* ----------------------------------------------------------------------
    Transporting the algebra to a type of its own.

    A type definition supplies abs and rep with the three facts below;
    nothing here needs to know that they came from one.  'n is the new
    type, 'fn is F['n].
   ---------------------------------------------------------------------- *)

Definition NCONS_def:
  bnfNCONS (mp_np : ('n -> 'p) -> 'fn -> 'fp) s rep abs af =
    abs (s (mp_np rep af))
End

Theorem ALG_NCONS[simp]:
  bnfALG stn (𝕌(:'n), bnfNCONS mp_np s rep abs)
Proof
  simp[ALG_def]
QED

Theorem HOM_ABS:
  bnfMapComp (mp_pn : ('p -> 'n) -> 'fp -> 'fn) mp_np mp_pp ∧
  bnfMapId mp_pp ∧ bnfMapCong mp_pp stp ∧
  (∀p. p ∈ A ⇒ rep (abs p) = p) ∧ bnfALG stp (A,s) ⇒
  bnfHOM mp_pn stp stn abs (A,s) (𝕌(:'n), bnfNCONS mp_np s rep abs)
Proof
  strip_tac >> drule_then (drule_then assume_tac) Map_eq_id >>
  simp[HOM_def, NCONS_def] >> rpt strip_tac >>
  gs[MapComp_def] >> AP_TERM_TAC >> AP_TERM_TAC >>
  first_x_assum irule >> gs[SUBSET_DEF]
QED

Theorem HOM_REP:
  bnfNatural (mp_np : ('n -> 'p) -> 'fn -> 'fp) stn stp ∧
  (∀n. rep n ∈ A) ∧ (∀p. p ∈ A ⇒ rep (abs p) = p) ∧ bnfALG stp (A,s) ⇒
  bnfHOM mp_np stn stp rep (𝕌(:'n), bnfNCONS mp_np s rep abs) (A,s)
Proof
  strip_tac >> simp[HOM_def, NCONS_def] >> rpt strip_tac >>
  irule EQ_SYM >> first_x_assum irule >> irule ALG_closed >>
  qexists_tac ‘stp’ >> gs[Natural_def, SUBSET_DEF, PULL_EXISTS]
QED

Theorem NEWTYPE_INITIALITY:
  bnfMapComp (mp_pn : ('p -> 'n) -> 'fp -> 'fn) mp_np mp_pp ∧
  bnfMapId mp_pp ∧ bnfMapCong mp_pp stp ∧
  bnfNatural mp_np stn stp ∧ bnfNatural mp_pn stp stn ∧
  bnfMapComp mp_np (mp_pc : ('p -> 'c) -> 'fp -> 'fc) mp_nc ∧
  bnfMapComp mp_pn mp_nc mp_pc ∧ bnfMapCong mp_pc stp ∧
  (∀n. abs (rep n) = n) ∧ (∀p. p ∈ A ⇒ rep (abs p) = p) ∧ (∀n. rep n ∈ A) ∧
  bnfALG stp (A,s) ∧
  (∀t G. bnfALG stc (G,t) ⇒
         ∃!h. bnfHOM mp_pc stp stc h (A,s) (G,t) ∧ ∀x. x ∉ A ⇒ h x = ARB) ⇒
  ∀t G. bnfALG stc (G,t) ⇒
        ∃!h. bnfHOM mp_nc stn stc h (𝕌(:'n), bnfNCONS mp_np s rep abs) (G,t)
Proof
  strip_tac >> rpt strip_tac >>
  ‘bnfHOM mp_np stn stp rep (𝕌(:'n), bnfNCONS mp_np s rep abs) (A,s)’
    by (irule HOM_REP >> simp[]) >>
  (* mp_pp appears only in HOM_ABS's hypotheses, so this one is forward *)
  byrule HOM_ABS
    [‘bnfMapComp mp_pn mp_np mp_pp’, ‘bnfMapId mp_pp’, ‘bnfMapCong mp_pp stp’,
     ‘∀p. p ∈ A ⇒ rep (abs p) = p’, ‘bnfALG stp (A,s)’]
    assume_tac >>
  (* the rewrite goes on the assumption: EXISTS_UNIQUE_ALT on the goal
     would put it in a shape the rest of the proof does not expect *)
  first_x_assum (qspecl_then [‘t’,‘G’] mp_tac) >> simp[] >>
  disch_then (qx_choose_then ‘H’ assume_tac o SRULE[EXISTS_UNIQUE_ALT]) >>
  simp[EXISTS_UNIQUE_THM] >> conj_tac
  >- (‘bnfHOM mp_pc stp stc H (A,s) (G,t) ∧ ∀x. x ∉ A ⇒ H x = ARB’
        by (first_assum (irule o iffRL) >> simp[]) >>
      byrule HOMs_compose
        [‘bnfMapComp mp_np mp_pc mp_nc’, ‘bnfNatural mp_np stn stp’,
         ‘bnfHOM mp_np stn stp rep _ (A,s)’, ‘bnfHOM mp_pc stp stc H (A,s) (G,t)’]
        (irule_at Any)) >>
  (* uniqueness: both give homomorphisms out of (A,s) once composed
     with abs, and those are unique *)
  qx_genl_tac [‘h1’, ‘h2’] >> strip_tac >>
  ‘∀h. bnfHOM mp_nc stn stc h (𝕌(:'n), bnfNCONS mp_np s rep abs) (G,t) ⇒
       H = bnfARBIFY A (h o abs)’
    by (rpt strip_tac >> first_assum (irule o iffLR) >>
        simp[ARBIFY_def] >>
        byrule HOM_ARBIFY [‘bnfMapCong mp_pc stp’] (fn th => simp[th]) >>
        byrule HOMs_compose
          [‘bnfMapComp mp_pn mp_nc mp_pc’, ‘bnfNatural mp_pn stp stn’,
           ‘bnfHOM mp_pn stp stn abs (A,s) _’,
           ‘bnfHOM mp_nc stn stc _ _ (G,t)’]
          (irule_at Any)) >>
  ‘bnfARBIFY A (h1 o abs) = bnfARBIFY A (h2 o abs)’ by metis_tac[] >>
  simp[FUN_EQ_THM] >> qx_gen_tac ‘n’ >>
  (* stating the instance rather than AP_TERMing a quotation: a rule's
     quotation is parsed with no goal context, so rep would come back at
     a fresh type *)
  ‘bnfARBIFY A (h1 o abs) (rep n) = bnfARBIFY A (h2 o abs) (rep n)’ by simp[] >>
  gs[ARBIFY_def]
QED

(* over the whole type every function is a homomorphism, so initiality
   collapses to the recursion equation a datatype package wants *)
Theorem NEWTYPE_RECURSION =
        NEWTYPE_INITIALITY |> UNDISCH
                           |> Q.SPECL [‘t’, ‘UNIV’]
                           |> SRULE [HOM_def, ALG_def, SUBSET_UNIV]
                           |> GSYM
                           |> Q.GEN ‘t’
                           |> DISCH_ALL

(* ----------------------------------------------------------------------
    Primitive recursion from iteration.

    The recursion theorem above is an iterator: the function only ever
    sees the results of the recursive calls.  HOL's datatype axioms are
    primitive recursive — the function sees the constructor's arguments
    as well — so the two are bridged by the standard pairing trick, which
    needs the iterator at the product carrier 'n # 'c.
   ---------------------------------------------------------------------- *)

Theorem PRIM_REC_OF_ITER:
  bnfMapComp (mp_nq : ('n -> 'n # 'c) -> 'fn -> 'fq) mp_qn mp_nn ∧
  bnfMapComp mp_nq (mp_qc : ('n # 'c -> 'c) -> 'fq -> 'fc) mp_nc ∧
  bnfMapId mp_nn ∧
  (∀t : 'fq -> 'n # 'c. ∃!h. ∀af. h (cons af) = t (mp_nq h af)) ∧
  (∀t : 'fn -> 'n. ∃!h. ∀af. h (cons af) = t (mp_nn h af)) ⇒
  ∀t : 'fn -> 'fc -> 'c. ∃!h. ∀af. h (cons af) = t af (mp_nc h af)
Proof
  strip_tac >> gen_tac >>
  (* the paired iterator: alongside the answer it rebuilds its own
     argument, and rebuilding is the identity *)
  qpat_assum ‘∀t. ∃!h. ∀af. h (cons af) = t (mp_nq h af)’
    (qspec_then ‘λv. (cons (mp_qn FST v), t (mp_qn FST v) (mp_qc SND v))’
       (strip_assume_tac o SRULE[EXISTS_UNIQUE_THM])) >>
  rename [‘k (cons _) = _’] >>
  ‘FST o k = I’
    by (qpat_assum ‘∀t. ∃!h. ∀af. h (cons af) = t (mp_nn h af)’
          (qspec_then ‘cons’ (strip_assume_tac o SRULE[EXISTS_UNIQUE_THM])) >>
        first_x_assum irule >> rpt conj_tac >~
        [‘I (cons _) = _’] >- gs[MapId_def] >>
        gen_tac >> simp[] >> gs[MapComp_def]) >>
  simp[EXISTS_UNIQUE_THM] >> conj_tac
  >- (qexists_tac ‘SND o k’ >> gen_tac >> simp[] >>
      gs[MapComp_def, MapId_def]) >>
  (* uniqueness: a solution paired with the identity solves the paired
     equation, and those solutions are unique *)
  qx_genl_tac [‘h1’, ‘h2’] >> strip_tac >>
  ‘∀h. (∀af. h (cons af) = t af (mp_nc h af)) ⇒ k = (λx. (x, h x))’
    by (rpt strip_tac >>
        qpat_assum ‘∀h h'. (∀af. h (cons af) = (cons _, _)) ∧ _ ⇒ _’ irule >>
        rpt conj_tac >~ [‘k (cons _) = _’] >- simp[] >>
        gen_tac >> simp[] >> gs[MapComp_def] >>
        simp[combinTheory.o_DEF, GSYM combinTheory.I_EQ_IDABS, ETA_AX] >>
        gs[MapId_def]) >>
  ‘(λx. (x, h1 x)) = (λx. (x, h2 x))’ by metis_tac[] >>
  gs[FUN_EQ_THM]
QED

(* ----------------------------------------------------------------------
    Induction on the new type.

    The hypothesis is "for every sub-term in the set", which is the form
    that survives a nested recursion: Prim_rec's derivation counts
    recursive arguments by their type, and under another type operator
    there are none to count.
   ---------------------------------------------------------------------- *)

Theorem NEWTYPE_IND:
  bnfMapComp (mp_pn : ('p -> 'n) -> 'fp -> 'fn) mp_np mp_pp ∧
  bnfMapId mp_pp ∧ bnfMapCong mp_pp stp ∧ bnfNatural mp_pn stp stn ∧
  (∀n. abs (rep n) = n) ∧ (∀p. p ∈ bnfMINSET stp s ⇒ rep (abs p) = p) ∧
  (∀n. rep n ∈ bnfMINSET stp s) ⇒
  ∀P. (∀af. (∀y. y ∈ stn af ⇒ P y) ⇒ P (bnfNCONS mp_np s rep abs af)) ⇒
      ∀n. P n
Proof
  strip_tac >> gen_tac >> strip_tac >>
  drule_then (drule_then assume_tac) Map_eq_id >>
  ‘∀p. p ∈ bnfMINSET stp s ⇒ P (abs p)’
    by (ho_match_mp_tac MINSET_ind' >> qx_gen_tac ‘x’ >> strip_tac >>
        first_x_assum (qspec_then ‘mp_pn abs x’ mp_tac) >>
        simp[NCONS_def] >>
        ‘mp_np rep (mp_pn abs x) = x’
          by (gs[MapComp_def] >> first_x_assum irule >> simp[] >>
              metis_tac[]) >>
        simp[] >> disch_then irule >> gs[Natural_def, PULL_EXISTS]) >>
  gen_tac >> first_x_assum (qspec_then ‘rep n’ mp_tac) >> simp[]
QED

(* ----------------------------------------------------------------------
    The degenerate fixed point.

    A specification with no recursion — an enumeration, a record, any
    sum of products the type itself does not occur in — gives a functor
    that does not use the recursive argument at all, and μα. C is C.

    The construction above cannot build it: the cardinality argument
    needs the recursive argument to be somewhere non-empty, which for a
    constant functor it never is.  It does not need to.  A type in
    bijection with C satisfies the same three principles, with the map
    an identity and the sub-term set empty, and that is all the rest of
    the package asks of a fixed point.

    The map and the set function are parameters here, as they are
    everywhere else, so that a caller instantiates them with the terms
    its own functor gives and proves the two degeneracy facts about
    those terms.
   ---------------------------------------------------------------------- *)

Theorem COPY_RECURSION:
  (∀n. abs (rep n) = n) ∧ (∀p. rep (abs p) = p) ∧
  (∀h:'n -> 'c. ∀af. mp h af = af) ⇒
  ∀t. ∃!h. ∀af. h (abs af) = t (mp h af)
Proof
  strip_tac >> gen_tac >> simp[EXISTS_UNIQUE_THM] >> conj_tac
  >- (qexists ‘t o rep’ >> simp[]) >>
  ‘∀k. (∀af. k (abs af) = t (mp k af)) ⇒ k = t o rep’
    suffices_by metis_tac[] >>
  rpt strip_tac >> simp[FUN_EQ_THM, FUN_EQ_THM] >> qx_gen_tac ‘n’ >>
  first_x_assum (qspec_then ‘rep n’ mp_tac) >> simp[]
QED

Theorem COPY_PRIM_REC:
  (∀n. abs (rep n) = n) ∧ (∀p. rep (abs p) = p) ∧
  (∀h:'n -> 'c. ∀af. mp h af = af) ⇒
  ∀t. ∃!h. ∀af. h (abs af) = t af (mp h af)
Proof
  strip_tac >> gen_tac >> simp[EXISTS_UNIQUE_THM] >> conj_tac
  >- (qexists ‘λn. t (rep n) (rep n)’ >> simp[]) >>
  ‘∀k. (∀af. k (abs af) = t af (mp k af)) ⇒ k = λn. t (rep n) (rep n)’
    suffices_by metis_tac[] >>
  rpt strip_tac >> simp[FUN_EQ_THM] >> qx_gen_tac ‘n’ >>
  first_x_assum (qspec_then ‘rep n’ mp_tac) >> simp[]
QED

Theorem COPY_IND:
  (∀n. abs (rep n) = n) ∧ (∀af. stn af = ∅) ⇒
  ∀P. (∀af. (∀y. y ∈ stn af ⇒ P y) ⇒ P (abs af)) ⇒ ∀n. P n
Proof
  rpt strip_tac >> first_x_assum (qspec_then ‘rep n’ mp_tac) >> simp[]
QED
