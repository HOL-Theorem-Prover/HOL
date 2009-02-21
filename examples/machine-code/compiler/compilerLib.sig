signature compilerLib =
sig

  include Abbrev

  (* input : target ("arm", "ppc" or "x86") and term (equation defining function) *)

  val compile  : string -> term -> thm * thm * thm

end
