signature schneiderUtils =
  sig
    type term = Term.term
    type thm = Thm.thm
    type goal = Abbrev.goal
    type conv = Abbrev.conv
    type tactic = Abbrev.tactic

    val ASM_LIST_TAC : int list
                       -> (thm list -> term list * 'a -> 'b)
                          -> term list * 'a -> 'b
    val ASM_TAC : int -> (thm -> term list * 'a -> 'b) -> term list * 'a -> 'b
    val BOOL_VAR_ELIM_CONV : term -> term -> thm
    val BOOL_VAR_ELIM_TAC : term -> tactic
    val COND_FUN_EXT_CONV : term -> thm
    val COND_FUN_EXT_TAC : tactic
    val COPY_ASM_NO : int -> tactic
    val FORALL_IN_CONV : conv
    val FORALL_UNFREE_CONV : term -> thm
    val LEFT_CONJ_TAC : tactic
    val LEFT_DISJ_TAC : tactic
    val LEFT_EXISTS_TAC : tactic
    val LEFT_FORALL_TAC : term -> tactic
    val LEFT_LEMMA_DISJ_CASES_TAC : thm -> tactic
    val LEFT_NO_EXISTS_TAC : int -> tactic
    val LEFT_NO_FORALL_TAC : int -> term -> tactic
    val MY_MP_TAC : term -> goal -> (term list * term) list * (thm list -> thm)
    val POP_NO_ASSUM : int -> (thm -> term list * 'a -> 'b) -> term list * 'a -> 'b
    val POP_NO_TAC : int -> tactic
    val RIGHT_CONJ_TAC : tactic
    val RIGHT_DISJ_TAC : tactic
    val RIGHT_LEMMA_DISJ_CASES_TAC : thm -> tactic
    val REWRITE1_TAC : thm -> tactic
    val UNDISCH_ALL_TAC : tactic
    val UNDISCH_HD_TAC : tactic
    val UNDISCH_NO_TAC : int -> tactic
    val delete : int -> 'a list -> 'a list
    val elem : int -> 'a list -> 'a
  end
