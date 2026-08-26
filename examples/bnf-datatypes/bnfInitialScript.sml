Theory bnfInitial
Ancestors
  pred_set cardinal combin pair
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
