signature BasicProvers =
sig
  include Abbrev
  type simpset = simpLib.simpset

  (* Eliminate v = M or M = v from hypotheses *)

  val VAR_EQ_TAC      : tactic

  (* First order automatic proof *)

  val PROVE           : thm list -> term -> thm
  val PROVE_TAC       : thm list -> tactic
  val GEN_PROVE_TAC   : int -> int -> int -> thm list -> tactic

  (* Simplification *)

  val bool_ss         : simpset
  val srw_ss          : unit -> simpset
  val &&              : simpset * thm list -> simpset  (* infix && *)

  val RW_TAC          : simpset -> thm list -> tactic
  val NORM_TAC        : simpset -> thm list -> tactic
  val SRW_TAC         : simpLib.ssdata list -> thm list -> tactic
  val augment_srw_ss  : simpLib.ssdata list -> unit
  val export_rewrites : string list -> unit

  (* Compound automated reasoners. *)

  val PRIM_STP_TAC    : simpset -> tactic -> tactic
  val STP_TAC         : simpset -> tactic -> tactic

end
