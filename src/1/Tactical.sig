signature Tactical =
sig
  include Abbrev

  val TAC_PROOF      : goal * tactic -> thm
  val prove          : term * tactic -> thm
  val store_thm      : string * term * tactic -> thm
  val THEN           : tactic * tactic -> tactic
  val THENL          : tactic * tactic list -> tactic
  val ORELSE         : tactic * tactic -> tactic
  val THEN1          : tactic * tactic -> tactic
  val THEN_LT : ('a -> goal list * (thm list -> 'b)) * list_tactic ->
        'a -> goal list * (thm list -> 'b)
  (* could be used as 
  val THEN_LT        : tactic * list_tactic -> tactic
  val THEN_LT        : list_tactic * list_tactic -> list_tactic
  *)
  val TACS_TO_LT     : tactic list -> list_tactic
  val NULL_OK_LT     : list_tactic -> list_tactic
  val ALLGOALS       : tactic -> list_tactic
  val NTH_GOAL       : tactic -> int -> list_tactic
  val LASTGOAL       : tactic -> list_tactic
  val HEADGOAL       : tactic -> list_tactic
  val SPLIT_LT       : int -> list_tactic * list_tactic -> list_tactic
  val ROTATE_LT      : int -> list_tactic
  val REVERSE        : tactic -> tactic
  val REVERSE_LT     : list_tactic 
  val FAIL_TAC       : string -> tactic
  val NO_TAC         : tactic
  val ALL_TAC        : tactic
  val ALL_LT         : list_tactic
  val TRY            : tactic -> tactic
  val REPEAT         : tactic -> tactic
  val VALID          : tactic -> tactic
  val EVERY          : tactic list -> tactic
  val FIRST          : tactic list -> tactic
  val MAP_EVERY      : ('a -> tactic) -> 'a list -> tactic
  val MAP_FIRST      : ('a -> tactic) -> 'a list -> tactic
  val FIRST_PROVE    : tactic list -> tactic
  val EVERY_ASSUM    : thm_tactic -> tactic
  val FIRST_ASSUM    : thm_tactic -> tactic
  val FIRST_X_ASSUM  : thm_tactic -> tactic
  val LAST_ASSUM     : thm_tactic -> tactic
  val LAST_X_ASSUM   : thm_tactic -> tactic
  val ASSUM_LIST     : (thm list -> tactic) -> tactic
  val POP_ASSUM      : thm_tactic -> tactic
  val PRED_ASSUM     : (term -> bool) -> thm_tactic -> tactic
  val PAT_ASSUM      : term -> thm_tactic -> tactic
  val POP_ASSUM_LIST : (thm list -> tactic) -> tactic
  val SUBGOAL_THEN   : term -> thm_tactic -> tactic
  val CHANGED_TAC    : tactic -> tactic
  val Q_TAC          : (term -> tactic) -> term frag list -> tactic

  val default_prover : term * tactic -> thm
  val set_prover     : (term * tactic -> thm) -> unit
  val restore_prover : unit -> unit

end;
