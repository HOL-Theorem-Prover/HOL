signature Ho_Rewrite =
sig
  include Abbrev

  val mk_rewrites                : thm -> thm list

  val implicit_rewrites          : unit -> thm list
  val set_implicit_rewrites      : thm list -> unit
  val add_implicit_rewrites      : thm list -> unit

  val GEN_REWRITE_CONV           : (conv -> conv) -> thm list -> conv
  val GEN_REWRITE_RULE           : (conv -> conv) -> thm list -> thm -> thm
  val GEN_REWRITE_TAC            : (conv -> conv) -> thm list -> tactic

  val PURE_REWRITE_CONV          : thm list -> conv
  val REWRITE_CONV               : thm list -> conv
  val HIGHER_REWRITE_CONV        : thm list -> conv
  val PURE_ONCE_REWRITE_CONV     : thm list -> conv
  val ONCE_REWRITE_CONV          : thm list -> conv
	
  val PURE_REWRITE_RULE          : thm list -> thm -> thm
  val REWRITE_RULE               : thm list -> thm -> thm
  val PURE_ONCE_REWRITE_RULE     : thm list -> thm -> thm
  val ONCE_REWRITE_RULE          : thm list -> thm -> thm
  val PURE_ASM_REWRITE_RULE      : thm list -> thm -> thm
  val ASM_REWRITE_RULE           : thm list -> thm -> thm
  val PURE_ONCE_ASM_REWRITE_RULE : thm list -> thm -> thm
  val ONCE_ASM_REWRITE_RULE      : thm list -> thm -> thm
	
  val PURE_REWRITE_TAC           : thm list -> tactic
  val REWRITE_TAC                : thm list -> tactic
  val PURE_ONCE_REWRITE_TAC      : thm list -> tactic
  val ONCE_REWRITE_TAC           : thm list -> tactic
  val PURE_ASM_REWRITE_TAC       : thm list -> tactic
  val ASM_REWRITE_TAC            : thm list -> tactic
  val PURE_ONCE_ASM_REWRITE_TAC  : thm list -> tactic
  val ONCE_ASM_REWRITE_TAC       : thm list -> tactic

  type pred = term -> bool

  val FILTER_PURE_ASM_REWRITE_RULE      : pred -> thm list -> thm -> thm
  val FILTER_ASM_REWRITE_RULE           : pred -> thm list -> thm -> thm
  val FILTER_PURE_ONCE_ASM_REWRITE_RULE : pred -> thm list -> thm -> thm
  val FILTER_ONCE_ASM_REWRITE_RULE      : pred -> thm list -> thm -> thm
  val FILTER_PURE_ASM_REWRITE_TAC       : pred -> thm list -> tactic
  val FILTER_ASM_REWRITE_TAC            : pred -> thm list -> tactic
  val FILTER_PURE_ONCE_ASM_REWRITE_TAC  : pred -> thm list -> tactic
  val FILTER_ONCE_ASM_REWRITE_TAC       : pred -> thm list -> tactic

  val SUBST_MATCH : thm -> thm -> thm
end
