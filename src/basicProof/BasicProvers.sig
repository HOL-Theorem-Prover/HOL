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
  val Abbr            : term quotation -> thm
  val LEAVE_LETS      : thm

  val RW_TAC          : simpset -> thm list -> tactic
  val NORM_TAC        : simpset -> thm list -> tactic
  val SRW_TAC         : simpLib.ssfrag list -> thm list -> tactic
  val augment_srw_ss  : simpLib.ssfrag list -> unit
  val diminish_srw_ss : string list -> simpLib.ssfrag list
  val export_rewrites : string list -> unit
  val thy_ssfrag      : string -> simpLib.ssfrag

  (* LET manoeuvres *)
  val LET_ELIM_TAC    : tactic
  val new_let_thms    : thm list -> unit

  (* Compound automated reasoners. *)

  val PRIM_STP_TAC    : simpset -> tactic -> tactic
  val STP_TAC         : simpset -> tactic -> tactic

end
