signature CSimp =
sig

  include Abbrev
  val csimp : conv

end

(*
   [csimp t] simplifies t using "congruential simplifications".
*)
