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

end
