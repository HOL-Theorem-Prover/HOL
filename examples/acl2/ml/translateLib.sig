signature translateLib = 
sig
	include Abbrev

	val CHOOSEP_TAC             : thm list -> tactic
	val CHOOSEP		    : thm list -> term -> thm
	val DOUBLE_MATCH            : (term -> term) -> (term -> term) -> term -> thm -> thm

	val ite_tm                  : term
	val mk_acl2_cond            : term * term * term -> term 
	val dest_acl2_cond          : term -> term * term * term
    	val is_acl2_cond            : term -> bool

	val acl2_cons_tm            : term
	val mk_acl2_cons            : term * term -> term
	val dest_acl2_cons          : term -> term * term
	val strip_cons              : term -> term list

	val acl2_true_tm            : term
	val mk_acl2_true            : term -> term
	val dest_acl2_true          : term -> term
	val is_acl2_true            : term -> bool
	
	val DISJ_CASES_UNIONL       : thm -> thm list -> thm

	val RAT_CONG_TAC            : tactic

	val EQUAL_EXISTS_TAC        : tactic
	val FIX_CI_TAC              : tactic

end
