signature Tactical =
sig
  include Abbrev

  val TAC_PROOF      : goal * tactic -> thm
  val prove          : term * tactic -> thm
  val store_thm      : string * term * tactic -> thm
  val THEN           : ('a,'b) gentactic * tactic -> ('a,'b) gentactic
  val >>             : ('a,'b) gentactic * tactic -> ('a,'b) gentactic
  val \\             : ('a,'b) gentactic * tactic -> ('a,'b) gentactic
  (* could be used as
  val THEN           : tactic * tactic -> tactic
  val THEN           : list_tactic * tactic -> list_tactic
  *)
  val THENL          : ('a,'b) gentactic * tactic list -> ('a,'b) gentactic
  val >|             : ('a,'b) gentactic * tactic list -> ('a,'b) gentactic
  (* could be used as
  val THENL          : tactic * tactic list -> tactic
  val THENL          : list_tactic * tactic list -> list_tactic
  *)
  val ORELSE         : tactic * tactic -> tactic
  val ORELSE_LT      : list_tactic * list_tactic -> list_tactic
  val THEN1          : tactic * tactic -> tactic
  val >-             : tactic * tactic -> tactic
  val THEN_LT        : ('a,'b) gentactic * list_tactic -> ('a,'b) gentactic
  val >>>            : ('a,'b) gentactic * list_tactic -> ('a,'b) gentactic
  (* could be used as
  val THEN_LT        : tactic * list_tactic -> tactic
  val THEN_LT        : list_tactic * list_tactic -> list_tactic
  *)
  val TACS_TO_LT     : tactic list -> list_tactic
  val NULL_OK_LT     : list_tactic -> list_tactic
  val ALLGOALS       : tactic -> list_tactic
  val TRYALL         : tactic -> list_tactic
  val NTH_GOAL       : tactic -> int -> list_tactic
  val LASTGOAL       : tactic -> list_tactic
  val HEADGOAL       : tactic -> list_tactic
  val SPLIT_LT       : int -> list_tactic * list_tactic -> list_tactic
  val ROTATE_LT      : int -> list_tactic
  val REVERSE        : tactic -> tactic
  val reverse        : tactic -> tactic
  val REVERSE_LT     : list_tactic
  val FAIL_TAC       : string -> tactic
  val NO_TAC         : tactic
  val FAIL_LT        : string -> list_tactic
  val NO_LT          : list_tactic
  val ALL_TAC        : tactic
  val all_tac        : tactic
  val ALL_LT         : list_tactic
  val TRY            : tactic -> tactic
  val TRY_LT         : list_tactic -> list_tactic
  val REPEAT         : tactic -> tactic
  val rpt            : tactic -> tactic
  val REPEAT_LT      : list_tactic -> list_tactic
  val VALID          : tactic -> tactic
  val VALID_LT       : list_tactic -> list_tactic
  val VALIDATE       : tactic -> tactic
  val VALIDATE_LT    : list_tactic -> list_tactic
  val GEN_VALIDATE   : bool -> tactic -> tactic
  val GEN_VALIDATE_LT: bool -> list_tactic -> list_tactic
  val ADD_SGS_TAC    : term list -> tactic -> tactic
  val EVERY          : tactic list -> tactic
  val EVERY_LT       : list_tactic list -> list_tactic
  val FIRST          : tactic list -> tactic
  val MAP_EVERY      : ('a -> tactic) -> 'a list -> tactic
  val map_every      : ('a -> tactic) -> 'a list -> tactic
  val MAP_FIRST      : ('a -> tactic) -> 'a list -> tactic
  val FIRST_PROVE    : tactic list -> tactic
  val EVERY_ASSUM    : thm_tactic -> tactic
  val FIRST_ASSUM    : thm_tactic -> tactic
  val first_assum    : thm_tactic -> tactic
  val FIRST_X_ASSUM  : thm_tactic -> tactic
  val first_x_assum  : thm_tactic -> tactic
  val LAST_ASSUM     : thm_tactic -> tactic
  val last_assum     : thm_tactic -> tactic
  val LAST_X_ASSUM   : thm_tactic -> tactic
  val last_x_assum   : thm_tactic -> tactic
  val ASSUM_LIST     : (thm list -> tactic) -> tactic
  val POP_ASSUM      : thm_tactic -> tactic
  val pop_assum      : thm_tactic -> tactic
  val PRED_ASSUM     : (term -> bool) -> thm_tactic -> tactic
  val PAT_ASSUM      : term -> thm_tactic -> tactic
  val POP_ASSUM_LIST : (thm list -> tactic) -> tactic
  val SUBGOAL_THEN   : term -> thm_tactic -> tactic
  val USE_SG_THEN    : thm_tactic -> int -> int -> list_tactic
  val CHANGED_TAC    : tactic -> tactic
  val Q_TAC          : (term -> tactic) -> term frag list -> tactic

  val default_prover : term * tactic -> thm
  val set_prover     : (term * tactic -> thm) -> unit
  val restore_prover : unit -> unit

end
