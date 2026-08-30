signature bnfFixLib =
sig

  include Abbrev

  (* ----------------------------------------------------------------------
      Instantiating a composite BNF's laws for the fixed-point
      construction.

      bnfInitialTheory states the construction over parameters: the
      functor's map and set functions are term variables and the BNF
      laws are hypotheses.  The functions here turn a derived BNF into
      those parameters at whatever instance is asked for, and prove the
      corresponding law.  Everything is forward proof over the stored
      laws; nothing here parses or runs a tactic.

      The fixed point is taken over the functor's *first* argument; any
      further argument it was derived in is a parameter, carried along by
      I and kept as an argument of the new type.  A caller that only
      wants the type can derive the functor in one argument alone.
     ---------------------------------------------------------------------- *)

  (* F[ty], for the functor underlying the derived BNF *)
  val functorAt : bnfLib.derived_bnfn -> hol_type -> hol_type

  (* the set function at ty, and the map operator from ty1 to ty2, as
     the terms bnfInitialTheory's parameters stand for *)
  val setOp : bnfLib.derived_bnfn -> hol_type -> term
  val mapOp : bnfLib.derived_bnfn -> hol_type * hol_type -> term

  (* |- MapId (mapOp bnf (ty,ty)) *)
  val MapIdThm : bnfLib.derived_bnfn -> hol_type -> thm

  (* |- MapComp (mapOp bnf (a,b)) (mapOp bnf (b,c)) (mapOp bnf (a,c)) *)
  val MapCompThm : bnfLib.derived_bnfn ->
                   hol_type * hol_type * hol_type -> thm

  (* |- Natural (mapOp bnf (a,b)) (setOp bnf a) (setOp bnf b) *)
  val NaturalThm : bnfLib.derived_bnfn -> hol_type * hol_type -> thm

  (* |- MapCong (mapOp bnf (a,b)) (setOp bnf a) *)
  val MapCongThm : bnfLib.derived_bnfn -> hol_type * hol_type -> thm

  (* An ordinal as big as the functor's own bound: the term bd, and
        |- preds bd = ~ <the bound>,  |- w <= bd
     The ordinal is a choice term, so no constant is introduced. *)
  val boundOrdinal : bnfLib.derived_bnfn -> {bd : term, cardeq : thm,
                                             omega_le : thm}

  (* |- !x. setOp bnf ty x <<= preds bd, given boundOrdinal's cardeq *)
  val setBoundThm : bnfLib.derived_bnfn -> thm -> hol_type -> thm

  (* The cardinality bound the construction runs on: a type big enough
     to hold every minimal algebra over ty, and
        |- !s. MINSET (setOp bnf ty) s <<= univ(:carrier)
     ty is normally left a type variable, so that the theorem covers
     every carrier at once. *)
  val minsetBound : bnfLib.derived_bnfn -> hol_type ->
                    {carrier : hol_type, thm : thm}

  (* ----------------------------------------------------------------------
      The initial algebra itself, before any type is defined.  carrier
      is the bounded type the algebra is built over, prodty the product
      of all algebras over it (which is where alg lives), and target the
      type variable the initiality theorem is stated at, so that
      INST_TYPE gives initiality at any carrier.

        alg   : the carrier, a prodty set
        cons  : F[prodty] -> prodty
        isALG : |- ALG st (alg,cons)
        bij   : |- BIJ cons (FIN st alg) alg
        init  : |- !t G. ALG stc (G,t) ==>
                         ?!h. HOM .. h (alg,cons) (G,t) /\ ..
        inhabited : |- ?x. alg x
        induction : the reachability principle for alg
     ---------------------------------------------------------------------- *)
  type initial_algebra = {
    carrier : hol_type, prodty : hol_type, target : hol_type,
    alg : term, cons : term,
    bij : thm, init : thm, inhabited : thm, induction : thm,
    isALG : thm
  }

  val initialAlgebra : bnfLib.derived_bnfn -> initial_algebra

  (* ----------------------------------------------------------------------
      The datatype itself.  Defines a type in bijection with the initial
      algebra's carrier and transports the construction onto it:

        newty     : the new type
        cons      : F[newty] -> newty, the constructor
        cons_def  : its definition
        recursion : |- !t. ?!h. !af. h (cons af) = t (map h af)

      tyname names the type; ABS and REP name the type definition's
      abstraction and representation functions.
     ---------------------------------------------------------------------- *)
  type fixpoint = {newty : hol_type, cons : term, cons_def : thm,
                   recursion : thm, prim_recursion : thm,
                   set_induction : thm}

  val defineFixpoint : {tyname : string, ABS : string, REP : string} ->
                       bnfLib.derived_bnfn -> fixpoint

  (* ----------------------------------------------------------------------
      The datatype's own constructors, and its axiom in the shape the
      rest of HOL expects:

        |- !f0 f1. ?!fn.
             fn C0 = f0 /\
             !a0 a1. fn (C1 a0 a1) = f1 <non-rec> <rec> <fn of rec>

      which is what Prim_rec's derivations of distinctness, injectivity,
      induction and the case constant run on.  The functor's top level
      must be a sum of products of factors that are either the recursive
      argument itself or free of it; nesting is rejected here, since
      HOL's axiom takes a different shape for it.
     ---------------------------------------------------------------------- *)
  type constructors = {
    constructors : term list, defs : thm list, axiom : thm,
    legacy_axiom : thm, existential_axiom : thm,
    induction : thm option,   (* NONE for a nested recursion *)
    set_induction : thm,      (* hypothesis: every sub-term in the set *)
    distinct : thm option list, one_one : thm option list
  }

  val defineConstructors :
      string list -> bnfLib.derived_bnfn -> fixpoint -> constructors

  (* ----------------------------------------------------------------------
      The new type as a functor.

      A datatype the package builds is a functor in whatever arguments of
      the underlying functor were not the recursive one, and everything
      the BNF database stores about it — a map, a set function per
      argument, the four laws, a bound, witnesses and inhabitation — comes
      out of the recursion principle and the laws F was derived with.  The
      map, the set functions and the relator are defined as constants
      along the way, named after the type.

      Nothing is registered: the result is a value, which a caller adds to
      a database with bnfBase.insert or names and records.  The
      intermediate type a mutual recursion goes through has no business
      being exported.
     ---------------------------------------------------------------------- *)
  type fixpoint_bnf = {
    key : KernelSig.kernelname,
    info : thm bnfBase_dtype.info,
    map_thm : thm,          (* !f.. af. MAP f.. (cons af) = cons (Fmap ..) *)
    set_thms : thm list,    (* !af. SETi (cons af) = Fseti af UNION .. *)
    relator_def : thm
  }

  val fixpointBNF : bnfLib.derived_bnfn -> fixpoint -> fixpoint_bnf

  (* ----------------------------------------------------------------------
      The map and the set functions at each constructor:

        MAP f (MyCons a l) = MyCons (f a) (MAP f l)
        SET (MyCons a l)   = a INSERT SET l

      which is the form a user reads them in, and the form a size
      definition or a TypeBase entry is written with.  One theorem for the
      map and one per argument for the sets, each a conjunction over the
      constructors.
     ---------------------------------------------------------------------- *)
  val constructorEqns : constructors -> fixpoint_bnf ->
                        {map_eqns : thm, set_eqns : thm list}

  (* ----------------------------------------------------------------------
      Mutual recursion.

      A mutually recursive pair arrives as one functor per type with the
      sibling as an extra argument, 'a1 — which is what parse_bnf's
      translation of a mutrec_var produces.  defineMutual takes the two
      functors and the parameters they are both over, and defines the
      second type as a datatype in the sibling's slot and the first as a
      recursion nested through it; the second type is then the first
      substituted into it.  The pair's recursion principle comes back
      ground and hypothesis-free.

      The database is extended in memory with the second type as a
      functor, which is what the nesting needs, and returned so that the
      caller can go on nesting through the result.
     ---------------------------------------------------------------------- *)
  type mutual = {
    ty1 : hol_type, ty2 : hol_type,
    cons1 : term, cons2 : term,
    fix1 : fixpoint, fix2 : fixpoint,
    sibling : fixpoint_bnf,
    bnf1 : bnfLib.derived_bnfn,   (* each type's functor, as the *)
    bnf2 : bnfLib.derived_bnfn,   (* construction saw it *)
    db : bnfBase.t,
    iterator : thm,        (* MUTITER cons1 cons2 .., folded *)
    recursion : thm,       (* its two equations written out *)
    prim_recursion : thm,  (* and the form that hears the arguments too *)
    induction : thm
  }

  val defineMutual : {tyname1 : string, tyname2 : string} ->
                     bnfBase.t -> hol_type list -> hol_type * hol_type ->
                     mutual

  (* ----------------------------------------------------------------------
      The pair's induction principle, one clause per constructor:

        |- !P1 P2. (!p. P1 (A p)) /\ (!x y. P1 x /\ P2 y ==> P1 (B x y)) /\
                   (!x. P1 x ==> P2 (C x)) /\ (!p y. P2 y ==> P2 (D p y)) ==>
                   (!m. P1 m) /\ !m. P2 m

      The constructors come from defineConstructors over each type's own
      functor — the second type's over the sibling at its own parameter,
      which is instantiated here.
     ---------------------------------------------------------------------- *)
  val mutualInduction : constructors * constructors -> mutual -> thm

  (* ----------------------------------------------------------------------
      A whole family of mutually recursive types.

      The pair's reduction generalises by taking the family from the last
      member back: each type is built with the slots of the members
      before it left as parameters, and nested through the ones after it.

      A caller gives a name per type and, per specification, its functor
      together with the type variable standing for each member of the
      family — the translation of a specification numbers those per
      functor, so the same 'a1 means different things in different ones,
      and a member's own variable marks where its recursion goes.

      Each type is made a functor in what is left of it, in memory, so
      that the ones before it can nest through it.
     ---------------------------------------------------------------------- *)
  type family = {
    types : hol_type list,
    cons : term list,
    fixes : fixpoint list,
    bnfs : bnfLib.derived_bnfn list,
    functors : bnfLib.derived_bnfn list,
    maps : fixpoint_bnf option list,
    raw : (hol_type * hol_type list) list,
    slots : hol_type list,
    params : hol_type list,
    db : bnfBase.t
  }

  val defineFamily : {tynames : string list} ->
                     bnfBase.t -> hol_type list ->
                     (hol_type * hol_type list) list -> family

  (* ----------------------------------------------------------------------
      The family's recursion principle, in the shape HOL's own axiom for a
      mutually recursive family takes:

        |- !t0 .. tn. ?h0 .. hn.
             (!af. h0 (cons0 af) = t0 (F0map h0 .. hn af)) /\ ..

      Solved from the last member back: at each member the ones after it
      have already been solved, as a family over its own slot, and their
      functions are what its target folds with.
     ---------------------------------------------------------------------- *)
  val familyPrinciple : family -> thm
  val familyExistence : thm -> thm
  val familyUniqueness : thm -> thm
  val familyPrimRecursion : family -> thm

  (* the same principle as an iterator: a target that ignores the
     argument its constructor was applied to hears only the results of
     the recursive calls *)
  val familyRecursion : family -> thm

  (* ----------------------------------------------------------------------
      The same principle one constructor at a time, which is the form a
      proof is written against:

        |- !f0 f1 f2. ?h0 h1.
             (!a. h0 (A a) = f0 a) /\
             (!n m. h0 (B n m) = f1 n m (h0 n) (h1 m)) /\ ..

      one constructors record per member, in the family's order, and the
      principle to state this way — familyPrimRecursion's, for the shape
      above, or familyRecursion's for one where a target hears only the
      results of the recursive calls.
     ---------------------------------------------------------------------- *)
  val familyAxiom : constructors list -> family -> thm -> thm

  (* ----------------------------------------------------------------------
      The family's induction principle, from its principle at the
      booleans: a clause per member, with the hypothesis "every sub-term
      the functor holds of a member's type satisfies that member's
      predicate", which is the set-based form a nested recursion leaves.
     ---------------------------------------------------------------------- *)
  val familySetInduction : family -> thm -> thm

  (* the same three steps over whatever types the family has been put
     on: the constructors' definitions, and the types and constructors
     themselves, rather than the record the construction produced *)
  val familyAxiomOf : thm list list -> thm -> thm
  val familyInductionOf : thm list list -> thm -> thm
  val familySetInductionOf : family -> hol_type list * term list -> thm -> thm

  (* and the same principle one clause per constructor, which is the
     form a proof is written against *)
  val familyInduction : constructors list -> family -> thm -> thm

  (* ----------------------------------------------------------------------
      The case constants, from an axiom one clause per constructor —
      one per type the axiom defines, named and stated as the old
      package's are.  Prim_rec's own version defines them by a recursive
      definition, which a nested axiom cannot be; nothing about a case
      constant is recursive, so this takes the axiom with every target
      ignoring the results of the recursive calls.
     ---------------------------------------------------------------------- *)
  val defineCases : thm -> thm list

  (* ----------------------------------------------------------------------
      Collapsing a family onto types of its own.

      A member after the first comes out of the construction as an
      instance of an operator that also takes the earlier members'
      slots; what the specification says, and what a TypeBase entry is
      keyed on, is an operator over the specification's own variables.
      This copies each member onto a type of its own, once the family is
      built, and carries the constructors and the principle across.
     ---------------------------------------------------------------------- *)
  type collapsed = {
    types : hol_type list,
    abs : term list,
    rep : term list,
    absrep : thm list,          (* |- ABS o REP = I *)
    repabs : thm list,          (* |- REP o ABS = I *)
    cons : term list,
    cons_defs : thm list,
    principle : thm
  }

  val collapseFamily : {tynames : string list} -> family -> thm -> collapsed

  (* and its constructors, one per summand of each member's functor *)
  (* ----------------------------------------------------------------------
      The BNF structure of a type defined as a copy of another: the map
      conjugated by the bijection, the set functions after the
      representation, and every law from the original's with one
      direction of the bijection undone in the middle.  A collapsed
      member of a family is such a copy — of a composite of functors
      already in the database — but nothing here is particular to one.
     ---------------------------------------------------------------------- *)
  type copied_bnf = {
    key : KernelSig.kernelname,
    info : thm bnfBase_dtype.info,
    map_def : thm,
    set_defs : thm list,
    relator_def : thm
  }

  val transportBNF : {abs : term, rep : term, absrep : thm, repabs : thm} ->
                     bnfLib.derived_bnfn -> copied_bnf

  val collapsedConstructors :
      string list list -> collapsed ->
      {constructors : term list, defs : thm list} list

  (* and its map and set functions one constructor at a time, which is
     what a TypeBase entry's simplification set wants *)
  val collapsedEqns :
      collapsed -> family -> copied_bnf list ->
      {constructors : term list, defs : thm list} list ->
      {map_eqns : thm, set_eqns : thm list} list

  (* ----------------------------------------------------------------------
      The TypeBase entries, one per type the axiom defines: the axiom,
      the induction principle and the case definitions are what
      TypeBasePure derives the rest from, and the map and set equations
      per constructor are what the entry's simplification set wants —
      one list of those per type, in the case definitions' order.

      Registering the result is the caller's separate decision, as it is
      with the BNF database: TypeBase.export writes it to the theory.
     ---------------------------------------------------------------------- *)
  (* ----------------------------------------------------------------------
      A specification as written, through the parser and parse_bnf, to
      what the construction takes: a functor per member with the
      variable standing for each member in it, the specification's own
      type variables, and the constructors' names.
     ---------------------------------------------------------------------- *)
  type spec = {
    tynames : string list,
    params : hol_type list,
    functors : (hol_type * hol_type list) list,
    constructors : string list list
  }

  val parseSpec : hol_type quotation -> spec

  (* ----------------------------------------------------------------------
      Defining a function by the axiom, which is
      Prim_rec.new_recursive_definition for an axiom whose recursive
      calls arrive under a map.  The clauses are written as the axiom
      hands the calls over — `f a` for a direct occurrence, `MAP f l`
      for one under a functor — and an axiom over a family takes the
      clauses for all of its functions at once.
     ---------------------------------------------------------------------- *)
  val defineRecursion : {name : string, axiom : thm, def : term} -> thm

  val typeBaseInfo : {axiom : thm, induction : thm, case_defs : thm list,
                      rewrites : thm list list} ->
                     TypeBasePure.tyinfo list

end
