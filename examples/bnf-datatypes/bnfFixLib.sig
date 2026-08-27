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
    recursion : thm,
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

end
