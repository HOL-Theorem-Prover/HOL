signature ringLib =
sig

  include Abbrev

  val mk_ring_thm   : string -> thm -> thm

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
   * Declares a ring in internal tables used in the conversions below.
   * The process is cut in two steps since store_ring is heavy and declares
   * new constants, and its only goal is to produce rewrite thms.
   * The actual declaration is then very fast.
   *)
  val store_ring   : { Name : string, Theory : thm } -> thm
  val declare_ring : { RingThm : thm, IsConst : term -> bool, 
                       Rewrites : thm list} -> unit

  (*  - RING_NORM_CONV is a conversion to simplify a ring term (i.e. its
   *    type has been declared as a ring structure).
   *  - RING_CONV is a conversion to solve (or simplify) an equality
   *  - Reify is a function to transform a list of ring terms into
   *    equivalent polynomial expressions sharing the same valuation.
   *    Not useful for the casual user.
   *)
  val RING_NORM_CONV : conv
  val RING_CONV      : conv
  val reify          : term list -> {Metamap : term, Poly : term list}


end;
