(* ===================================================================== *)
(* FILE          : tactical.sig                                          *)
(* DESCRIPTION   : Signature for functions that glue tactics together.   *)
(*                 From LCF, and added to through the years. Translated  *)
(*                 from hol88.                                           *)
(*                                                                       *)
(* AUTHORS       : (c) University of Edinburgh and                       *)
(*                     University of Cambridge                           *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Tactical =
sig

  type goal = Abbrev.goal
  type tactic = Abbrev.tactic
  type thm_tactic = Abbrev.thm_tactic

  val TAC_PROOF      : goal * tactic -> Thm.thm
  val prove          : Term.term * tactic -> Thm.thm
  val store_thm      : string * Term.term * tactic -> Thm.thm
  val THEN           : tactic * tactic -> tactic
  val THENL          : tactic * tactic list -> tactic
  val ORELSE         : tactic * tactic -> tactic
  val FAIL_TAC       : string -> tactic
  val NO_TAC         : tactic
  val ALL_TAC        : tactic
  val TRY            : tactic -> tactic
  val REPEAT         : tactic -> tactic
  val VALID          : tactic -> tactic
  val EVERY          : tactic list -> tactic
  val FIRST          : tactic list -> tactic
  val MAP_EVERY      : ('a -> tactic) -> 'a list -> tactic
  val MAP_FIRST      : ('a -> tactic) -> 'a list -> tactic
  val EVERY_ASSUM    : thm_tactic -> tactic
  val FIRST_ASSUM    : thm_tactic -> tactic
  val FIRST_X_ASSUM  : thm_tactic -> tactic
  val ASSUM_LIST     : (Thm.thm list -> tactic) -> tactic
  val POP_ASSUM      : thm_tactic -> tactic
  val PAT_ASSUM      : Term.term -> thm_tactic -> tactic
  val POP_ASSUM_LIST : (Thm.thm list -> tactic) -> tactic
  val SUBGOAL_THEN   : Term.term -> thm_tactic -> tactic
  val CHANGED_TAC    : tactic -> tactic
end;
