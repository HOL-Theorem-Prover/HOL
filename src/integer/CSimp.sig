signature CSimp =
sig

  include Abbrev
  val csimp : conv

end

(*
   [csimp c t] simplifies t using contextual simplifications.   These
   include rewriting q while assuming p in p /\ q, and rewriting q while
   assuming ~p in p \/ q.
*)
