signature BasicProvers =
sig
  type thm      = Thm.thm
  type term     = Term.term
  type tactic   = Abbrev.tactic
  type simpset  = simpLib.simpset

  (* Various basic automated reasoners *)

  (* First order *)
  val PROVE     : thm list -> term -> thm
  val PROVE_TAC : thm list -> tactic
  val GEN_PROVE_TAC : int -> int -> int -> thm list -> tactic

  (* Simplification *)

  val bool_ss  : simpset
  val &&       : simpset * thm list -> simpset  (* infix && *)

  (* Compound automated reasoners. *)
  val STP_TAC  : simpset -> tactic -> tactic
  val RW_TAC   : simpset -> thm list -> tactic

end;
