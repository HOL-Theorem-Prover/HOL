signature CSimp =
sig

  include Abbrev
  val csimp : conv -> conv

end

(*
   [csimp c t] simplifies t using contextual simplifications.   These
   include rewriting q while assuming p in p /\ q, and rewriting q while
   assuming ~p in p \/ q.

   The conversion c is used to transform a negated leaf term into an
   equation.
*)
