signature BasicProvers =
sig
  include Abbrev
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
  val PRIM_STP_TAC  : simpset -> tactic -> tactic
  val STP_TAC       : simpset -> tactic -> tactic
  val RW_TAC        : simpset -> thm list -> tactic
  val SRW_TAC       : simpLib.ssdata list -> thm list -> tactic
  val get_srw_ss    : unit -> simpset
  val augment_srw_ss: simpLib.ssdata list -> unit

end;
