signature PairRules =
sig
  include Abbrev

  val MK_PAIR                : thm * thm -> thm
  val PABS                   : term -> thm -> thm
  val PABS_CONV              : conv -> conv
  val PSUB_CONV              : conv -> conv
  val CURRY_CONV             : conv
  val UNCURRY_CONV           : conv
  val PBETA_CONV             : conv
  val PBETA_RULE             : thm -> thm
  val PBETA_TAC              : tactic
  val RIGHT_PBETA            : thm -> thm
  val LIST_PBETA_CONV        : conv
  val RIGHT_LIST_PBETA       : thm -> thm
  val LEFT_PBETA             : thm -> thm
  val LEFT_LIST_PBETA        : thm -> thm
  val UNPBETA_CONV           : term -> conv
  val PETA_CONV              : conv
  val PALPHA_CONV            : term -> conv
  val GEN_PALPHA_CONV        : term -> conv
  val PALPHA                 : term -> conv
  val paconv                 : term -> term -> bool
  val PAIR_CONV              : conv -> conv
  
  val NOT_PFORALL_CONV       : conv
  val NOT_PEXISTS_CONV       : conv
  val PEXISTS_NOT_CONV       : conv
  val PFORALL_NOT_CONV       : conv
  val PFORALL_AND_CONV       : conv
  val PEXISTS_OR_CONV        : conv
  val AND_PFORALL_CONV       : conv
  val LEFT_AND_PFORALL_CONV  : conv
  val RIGHT_AND_PFORALL_CONV : conv
  val OR_PEXISTS_CONV        : conv
  val LEFT_OR_PEXISTS_CONV   : conv
  val RIGHT_OR_PEXISTS_CONV  : conv
  val PEXISTS_AND_CONV       : conv
  val AND_PEXISTS_CONV       : conv
  val LEFT_AND_PEXISTS_CONV  : conv
  val RIGHT_AND_PEXISTS_CONV : conv
  val PFORALL_OR_CONV        : conv
  val OR_PFORALL_CONV        : conv
  val LEFT_OR_PFORALL_CONV   : conv
  val RIGHT_OR_PFORALL_CONV  : conv
  val PFORALL_IMP_CONV       : conv
  val LEFT_IMP_PEXISTS_CONV  : conv
  val RIGHT_IMP_PFORALL_CONV : conv
  val PEXISTS_IMP_CONV       : conv
  val LEFT_IMP_PFORALL_CONV  : conv
  val RIGHT_IMP_PEXISTS_CONV : conv
  
  val CURRY_FORALL_CONV      : term -> thm
  val CURRY_EXISTS_CONV      : term -> thm
  val UNCURRY_FORALL_CONV    : term -> thm
  val UNCURRY_EXISTS_CONV    : term -> thm

  val PSPEC                  : term -> thm -> thm
  val PSPECL                 : term list -> thm -> thm
  val IPSPEC                 : term -> thm -> thm
  val IPSPECL                : term list -> thm -> thm
  val PSPEC_PAIR             : thm -> term * thm
  val PSPEC_ALL              : thm -> thm
  val GPSPEC                 : thm -> thm
  val PSPEC_TAC              : term * term -> tactic
  val PGEN                   : term -> thm -> thm
  val PGENL                  : term list -> thm -> thm
  val P_PGEN_TAC             : term -> tactic
  val PGEN_TAC               : tactic
  val FILTER_PGEN_TAC        : term -> tactic
  
  val PEXISTS_CONV           : term -> thm
  val PSELECT_RULE           : thm -> thm
  val PSELECT_CONV           : term -> thm
  val PEXISTS_RULE           : thm -> thm
  val PSELECT_INTRO          : thm -> thm
  val PSELECT_ELIM           : thm -> term * thm -> thm
  val PEXISTS                : term * term -> thm -> thm
  val PCHOOSE                : term * thm -> thm -> thm
  val P_PCHOOSE_THEN         : term -> (thm -> tactic) -> thm -> tactic
  val PCHOOSE_THEN           : (thm -> tactic) -> thm -> tactic
  val P_PCHOOSE_TAC          : term -> thm -> tactic
  val PCHOOSE_TAC            : thm -> tactic
  val PEXISTS_TAC            : term -> tactic
  val PEXISTENCE             : thm -> thm
  val PEXISTS_UNIQUE_CONV    : term -> thm
  val P_PSKOLEM_CONV         : term -> conv
  val PSKOLEM_CONV           : term -> thm

  val PSTRIP_THM_THEN        : thm_tactical
  val PSTRIP_ASSUME_TAC      : thm_tactic
  val PSTRUCT_CASES_TAC      : thm_tactic
  val PSTRIP_GOAL_THEN       : thm_tactic -> tactic
  val FILTER_PSTRIP_THEN     : thm_tactic -> term -> tactic
  val PSTRIP_TAC             : tactic
  val FILTER_PSTRIP_TAC      : term -> tactic
  val PEXT                   : thm -> thm
  val P_FUN_EQ_CONV          : term -> conv
  val MK_PABS                : thm -> thm
  val HALF_MK_PABS           : thm -> thm
  val MK_PFORALL             : thm -> thm
  val MK_PEXISTS             : thm -> thm
  val MK_PSELECT             : thm -> thm
  val PFORALL_EQ             : term -> thm -> thm
  val PEXISTS_EQ             : term -> thm -> thm
  val PSELECT_EQ             : term -> thm -> thm
  val LIST_MK_PFORALL        : term list -> thm -> thm
  val LIST_MK_PEXISTS        : term list -> thm -> thm
  val PEXISTS_IMP            : term -> thm -> thm
  val SWAP_PFORALL_CONV      : conv
  val SWAP_PEXISTS_CONV      : conv
  val PART_PMATCH            : (term -> term) -> thm -> term -> thm
  val PMATCH_MP_TAC          : thm_tactic
  val PMATCH_MP              : thm -> thm -> thm

end
