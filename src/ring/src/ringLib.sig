signature ringLib =
sig

  local open HolKernel Abbrev in

  (* Given:
   *  - Name is a prefix prepended to the name of the constants of
   *    canonicalTheory and ringNormTheory when creating instantiated
   *    constants.
   *  - Theory:  |- (is_ring r)  or |- (is_semi_ring r)
   *  - Const is a predicate to recognize closed ring objets (ie those with
   *    which we can actually compute).
   *  - Rewrites is a bunch of equalities that should allow to compute the
   *    ring operations on closed terms, and decide equality of closed terms.
   *    If (Const c1) and (Const c2) then rewriting Rewrites on (c1 + c2)
   *    should simplify to a term c such that (Const c).
   * Returns:
   *  - NormConv is a conversion to simplify a ring term
   *  - EqConv is a conversion to solve an equality
   *  - Reify is a function to transform a list of ring terms into
   *    equivalent polynomial expressions sharing the same valuation.
   *    Not useful for the casual user.
   *)
  val declare_ring :
      { Name : string, Theory : thm, Const : term->bool,
        Rewrites : thm list } ->
      { NormConv : conv, EqConv : conv,
 	Reify : term list -> {Metamap : term, Poly : term list} }

  end

end;
