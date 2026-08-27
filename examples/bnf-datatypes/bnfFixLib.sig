signature bnfFixLib =
sig

  include Abbrev

  (* ----------------------------------------------------------------------
      Instantiating a composite BNF's laws for the fixed-point
      construction.

      bnfInitialTheory states the construction over parameters: the
      functor's map and set functions are term variables and the BNF
      laws are hypotheses.  The functions here turn a derived_bnf into
      those parameters at whatever instance is asked for, and prove the
      corresponding law.  Everything is forward proof over the stored
      laws; nothing here parses or runs a tactic.
     ---------------------------------------------------------------------- *)

  (* F[ty], for the functor underlying the derived BNF *)
  val functorAt : bnfLib.derived_bnf -> hol_type -> hol_type

  (* the set function at ty, and the map operator from ty1 to ty2, as
     the terms bnfInitialTheory's parameters stand for *)
  val setOp : bnfLib.derived_bnf -> hol_type -> term
  val mapOp : bnfLib.derived_bnf -> hol_type * hol_type -> term

  (* |- MapId (mapOp bnf (ty,ty)) *)
  val MapIdThm : bnfLib.derived_bnf -> hol_type -> thm

  (* |- MapComp (mapOp bnf (a,b)) (mapOp bnf (b,c)) (mapOp bnf (a,c)) *)
  val MapCompThm : bnfLib.derived_bnf ->
                   hol_type * hol_type * hol_type -> thm

  (* |- Natural (mapOp bnf (a,b)) (setOp bnf a) (setOp bnf b) *)
  val NaturalThm : bnfLib.derived_bnf -> hol_type * hol_type -> thm

  (* |- MapCong (mapOp bnf (a,b)) (setOp bnf a) *)
  val MapCongThm : bnfLib.derived_bnf -> hol_type * hol_type -> thm

  (* An ordinal as big as the functor's own bound: the term bd, and
        |- preds bd = ~ <the bound>,  |- w <= bd
     The ordinal is a choice term, so no constant is introduced. *)
  val boundOrdinal : bnfLib.derived_bnf -> {bd : term, cardeq : thm,
                                            omega_le : thm}

  (* |- !x. setOp bnf ty x <<= preds bd *)
  val setBoundThm : bnfLib.derived_bnf -> term -> hol_type -> thm

  (* The cardinality bound the construction runs on: a type big enough
     to hold every minimal algebra over ty, and
        |- !s. MINSET (setOp bnf ty) s <<= univ(:carrier)
     ty is normally left a type variable, so that the theorem covers
     every carrier at once. *)
  val minsetBound : bnfLib.derived_bnf -> hol_type ->
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

  val initialAlgebra : bnfLib.derived_bnf -> initial_algebra

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
  val defineFixpoint : {tyname : string, ABS : string, REP : string} ->
                       bnfLib.derived_bnf ->
                       {newty : hol_type, cons : term, cons_def : thm,
                        recursion : thm, prim_recursion : thm,
                        set_induction : thm}

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
  val defineConstructors :
      string list -> bnfLib.derived_bnf ->
      {newty : hol_type, cons : term, cons_def : thm,
       recursion : thm, prim_recursion : thm, set_induction : thm} ->
      {constructors : term list, defs : thm list, axiom : thm,
       legacy_axiom : thm, existential_axiom : thm,
       induction : thm option,   (* NONE for a nested recursion *)
       distinct : thm option list, one_one : thm option list}

end
