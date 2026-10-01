Theory bnfFixBNF
Ancestors
  bnfInitial bnfPrelims pred_set cardinal
Libs
  HolKernel Parse boolLib bossLib

(* ----------------------------------------------------------------------
    The fixed point is itself a functor, proved once.

    A datatype the package builds is μα. F(α, β⃗), and for a later
    datatype to recurse through it, it has to go into the BNF database
    with a map, a set function per parameter, the four laws, a bound and
    witnesses.  All of that is proved here, over parameters, in the way
    bnfInitialScript proves the construction itself: F's instances become
    ordinary type variables and its map and set functions ordinary term
    variables.

    Two things make the statements below shorter than they look.  First,
    the map and set functions of the new type are not defined here — the
    recursion principle defines them per datatype — so they arrive as
    parameters constrained by the equations they satisfy: FIXMAP for the
    map, FIXSET for a set function.  Second, F's map is *bundled*: a
    parameter map term stands for F's n-ary map with a particular tuple
    of functions already applied to the parameters, so that one binary
    statement covers a functor with any number of them.  Two bundles at
    different tuples are two parameters, related by whichever of the laws
    below needs them related — which is exactly how MapComp already
    relates three instances of a map.

    Throughout, 'n is the new type and 'fn is F['n]; 'm and 'fm are the
    same after a map, cn and cm the constructors, stn F's set function
    for the recursive argument, and sbn one of its parameters'.
   ---------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------
    the parameters that are not already in bnfInitialTheory
   ---------------------------------------------------------------------- *)

(* the new type's induction principle: every element is a cn of one whose
   sub-terms are covered.  This is what defineFixpoint's set_induction
   supplies. *)
Definition FIXIND_def:
  FIXIND (cn : 'fn -> 'n) stn ⇔
    ∀P. (∀af. (∀y. y ∈ stn af ⇒ P y) ⇒ P (cn af)) ⇒ ∀n. P n
End

Theorem FIXIND_thm:
  FIXIND (cn : 'fn -> 'n) stn ⇒
  ∀P. (∀af. (∀y. y ∈ stn af ⇒ P y) ⇒ P (cn af)) ⇒ ∀n. P n
Proof
  simp[FIXIND_def]
QED

(* M is the new type's map for one tuple of functions on the parameters:
   it takes a constructor apart, maps F, and puts it back together *)
Definition FIXMAP_def:
  FIXMAP (cn : 'fn -> 'n) (cm : 'fm -> 'm) mp M ⇔
    ∀af. M (cn af) = cm (mp M af)
End

(* and S is the set function for one parameter: the atoms F holds at this
   node, together with those of every sub-term *)
Definition FIXSET_def:
  FIXSET (cn : 'fn -> 'n) stn sbn S ⇔
    ∀af. S (cn af) = sbn af ∪ BIGUNION (IMAGE S (stn af))
End

(* naturality in a parameter rather than in the recursive argument: what
   the bundled map does to the parameter's atoms doesn't depend on the
   function it is given for the recursive argument *)
Definition NaturalP_def:
  NaturalP (mp : ('n -> 'm) -> 'fn -> 'fm) sbn sbm p ⇔
    ∀h af. sbm (mp h af) = IMAGE p (sbn af)
End

(* and congruence between two bundles that differ in one parameter *)
Definition MapCongP_def:
  MapCongP (mp1 : ('n -> 'm) -> 'fn -> 'fm) mp2 stn sbn p q ⇔
    ∀h1 h2 af.
      (∀y. y ∈ stn af ⇒ h1 y = h2 y) ∧ (∀b. b ∈ sbn af ⇒ p b = q b) ⇒
      mp1 h1 af = mp2 h2 af
End

(* ----------------------------------------------------------------------
    the map laws
   ---------------------------------------------------------------------- *)

(* induction on the new type, from the principle the parameters carry.
   drule would pull the induction variable out in front of P, leaving the
   conclusion in a shape ho_match_mp_tac cannot use. *)
val fix_induct =
    qpat_assum ‘FIXIND _ _’ (ho_match_mp_tac o MATCH_MP FIXIND_thm)

(* MapCong comes first in every hypothesis list below because it fixes
   both the map and the set function, so drule can resolve it and know
   what the rest means *)
Theorem FIXMAP_ID:
  MapCong mp stn ∧ MapId mp ∧ FIXIND cn stn ∧ FIXMAP cn cn mp M ⇒
  ∀n. M n = n
Proof
  strip_tac >> drule_then (drule_then assume_tac) Map_eq_id >>
  fix_induct >> rpt strip_tac >> gs[FIXMAP_def]
QED

Theorem FIXMAP_O:
  MapCong mp_np stn ∧ MapComp mp_nm mp_mp mp_np ∧ FIXIND cn stn ∧
  FIXMAP cn cm mp_nm M1 ∧ FIXMAP cm cp mp_mp M2 ∧ FIXMAP cn cp mp_np M12 ⇒
  ∀n. M2 (M1 n) = M12 n
Proof
  strip_tac >> fix_induct >> rpt strip_tac >>
  gs[FIXMAP_def, MapComp_def] >>
  (* both sides are cp of a map of af; the maps agree by congruence,
     since the induction hypothesis covers every sub-term *)
  AP_TERM_TAC >> gs[MapCong_def] >> first_x_assum irule >> simp[]
QED

(* ----------------------------------------------------------------------
    the set function
   ---------------------------------------------------------------------- *)

Theorem FIXSET_NATURAL:
  Natural mp stn stm ∧ NaturalP mp sbn sbm p ∧ FIXIND cn stn ∧
  FIXMAP cn cm mp M ∧ FIXSET cn stn sbn Sn ∧ FIXSET cm stm sbm Sm ⇒
  ∀n. Sm (M n) = IMAGE p (Sn n)
Proof
  strip_tac >> fix_induct >> rpt strip_tac >>
  gs[FIXMAP_def, FIXSET_def, Natural_def, NaturalP_def] >>
  (* the atoms of the mapped sub-terms are the images of the sub-terms'
     atoms, which is the induction hypothesis under an IMAGE *)
  ‘IMAGE Sm (IMAGE M (stn af)) = IMAGE (IMAGE p o Sn) (stn af)’
    by (simp[IMAGE_IMAGE] >> irule IMAGE_CONG >> simp[]) >>
  simp[IMAGE_BIGUNIONo]
QED

Theorem FIXMAP_CONG:
  MapCongP mp1 mp2 stn sbn p q ∧ FIXIND cn stn ∧ FIXSET cn stn sbn Sn ∧
  FIXMAP cn cm mp1 M1 ∧ FIXMAP cn cm mp2 M2 ⇒
  ∀n. (∀b. b ∈ Sn n ⇒ p b = q b) ⇒ M1 n = M2 n
Proof
  strip_tac >> fix_induct >> rpt strip_tac >>
  gs[FIXMAP_def] >> AP_TERM_TAC >>
  (* the atoms of cn af are those F holds here and those of the
     sub-terms, so agreeing on all of them is agreeing on each part *)
  qpat_x_assum ‘∀b. b ∈ Sn (cn af) ⇒ _’ mp_tac >>
  gs[FIXSET_def, MapCongP_def, PULL_EXISTS] >> strip_tac >>
  first_x_assum irule >> rpt strip_tac >>
  first_x_assum irule >> metis_tac[]
QED

(* ----------------------------------------------------------------------
    the bound.

    An atom of a term sits in one of its sub-terms, of which there are no
    more than F's own bound, and each holds no more than that many atoms;
    an infinite cardinal absorbs both, so F's bound bounds the new type
    as well.
   ---------------------------------------------------------------------- *)

Theorem FIXSET_CARDLEQ:
  FIXSET cn stn sbn Sn ∧ INFINITE B ∧ (∀af. sbn af ≼ B) ∧
  (∀af. stn af ≼ B) ∧ FIXIND cn stn ⇒
  ∀n. Sn n ≼ B
Proof
  strip_tac >> fix_induct >> rpt strip_tac >>
  gs[FIXSET_def] >> irule UNION_CARDLE >> simp[] >>
  irule CARD_BIGUNION >> simp[PULL_EXISTS] >>
  irule IMAGE_cardleq_rwt >> simp[]
QED

(* ----------------------------------------------------------------------
    Set notation.

    The set functions the component functors are registered with are
    stated as predicates — sumTheory's setL gives ‘λx. x = a’ — so
    unfolding a composite's set function at a constructor leaves those
    where set notation is wanted.
   ---------------------------------------------------------------------- *)

(* the argument's own set function, as a set: a composite over a bare
   parameter is the equality predicate at it *)
Theorem EQUAL_SING:
  (=) a = {a}
Proof
  simp[EXTENSION, bnfPrelimsTheory.IN_equal, EQ_SYM_EQ]
QED

Theorem LAM_EQ_SING:
  (λx. x = a) = {a}
Proof
  simp[EXTENSION]
QED

Theorem LAM_F_EMPTY:
  (λx. F) = ∅
Proof
  simp[EXTENSION]
QED

(* and two laws that put a set term built by nesting one functor inside
   another into a normal form: the atoms of a union are collected
   separately, and a set function applied through a collection of
   sub-terms is applied at each of them *)
Theorem BIGUNION_IMAGE_UNION:
  BIGUNION (IMAGE (λx. A x ∪ B x) X) =
  BIGUNION (IMAGE A X) ∪ BIGUNION (IMAGE B X)
Proof
  simp[Once EXTENSION, PULL_EXISTS] >> metis_tac[]
QED

Theorem BIGUNION_IMAGE_EMPTY:
  BIGUNION (IMAGE (λx. ∅) X) = ∅
Proof
  once_rewrite_tac[EXTENSION] >> simp[PULL_EXISTS]
QED

Theorem BIGUNION_IMAGE_BIGUNION:
  BIGUNION (IMAGE h (BIGUNION (IMAGE g X))) =
  BIGUNION (IMAGE (λx. BIGUNION (IMAGE h (g x))) X)
Proof
  simp[Once EXTENSION, PULL_EXISTS] >> metis_tac[]
QED

(* what a value's sets say after a map: the induction hypothesis for
   that member, without taking the set function apart *)
Theorem IMAGE_ALL:
  (∀b. b ∈ IMAGE f s ⇒ b) ⇔ ∀y. y ∈ s ⇒ f y
Proof
  simp[PULL_EXISTS]
QED

(* an equation the induction principle is read off: a clause of it says
   the hypothesis implies the conclusion, and what the recursion at the
   booleans says is that the two are the same disjunction *)
Theorem IMP_DISJ_EQ:
  (q ⇒ p) ⇒ (p ⇔ q ∨ p)
Proof
  DECIDE_TAC
QED

(* ----------------------------------------------------------------------
    witnesses and inhabitation.

    A witness for the new type is a constructor applied to a witness for
    F that doesn't need the recursive argument — a base case — and its
    atoms are then exactly the ones F holds there.  Inhabitation is the
    other half: an atom F holds at a node is an atom of the term.
   ---------------------------------------------------------------------- *)

Theorem FIXSET_EMPTY:
  FIXSET cn stn sbn Sn ∧ stn w = ∅ ⇒ Sn (cn w) = sbn w
Proof
  simp[FIXSET_def]
QED

Theorem FIXSET_IN:
  FIXSET cn stn sbn Sn ⇒ ∀af b. b ∈ sbn af ⇒ b ∈ Sn (cn af)
Proof
  simp[FIXSET_def]
QED
