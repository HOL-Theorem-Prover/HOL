signature jrhTactics =
  sig
    include Abbrev
    type Goal         = thm list * term
    type Goalstate    = Goal list * validation
    type Tactic       = Goal -> Goalstate
    type Thm_Tactic   = thm -> Tactic
    type Thm_Tactical = Thm_Tactic -> Thm_Tactic
    type refinement   = Goalstate -> Goalstate

    val by  : Tactic -> refinement
    val bys : Tactic list -> refinement
    val rotate : int -> refinement

    val mk_Goalstate : Goal -> Goalstate

    val THEN    : Tactic * Tactic -> Tactic
    val ORELSE  : Tactic * Tactic -> Tactic
    val THENL   : Tactic * Tactic list -> Tactic
    val convert : Tactic -> tactic

    (* some actual tactics *)
    val ALL_TAC        : Tactic
    val ACCEPT_TAC     : Thm_Tactic
    val ASSUME_TAC     : Thm_Tactic
    val CONTR_TAC      : Thm_Tactic
    val DISJ_CASES_TAC : Thm_Tactic
    val POP_ASSUM      : Thm_Tactic -> Tactic
    val POP_ASSUM_LIST : (thm list -> Tactic) -> Tactic
    val FIRST_ASSUM    : Thm_Tactic -> Tactic
    val ASSUM_LIST     : (thm list -> Tactic) -> Tactic
    val RULE_ASSUM_TAC : (thm -> thm) -> Tactic

    val REPEAT         : Tactic -> Tactic
    val EVERY          : Tactic list -> Tactic
    val MAP_EVERY      : ('a -> Tactic) -> 'a list -> Tactic
    val CHOOSE_TAC     : Thm_Tactic
    val FIRST_X_ASSUM  : Thm_Tactic -> Tactic

    (* some theorem tacticals *)

    val CONJUNCTS_THEN  : Thm_Tactical
    val DISJ_CASES_THEN : Thm_Tactical
    val ORELSE_TCL      : Thm_Tactical * Thm_Tactical -> Thm_Tactical
end
