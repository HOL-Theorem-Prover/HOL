signature armLib =
sig
    include Abbrev

    val fcp_ss       : simpLib.simpset
    val ICLASS_ss    : simpLib.ssfrag
    val PBETA_ss     : simpLib.ssfrag

    val combCases    : conv
    val tupleCases   : conv

    val RES_MP1_TAC  : (term frag list, term frag list) subst -> thm -> tactic
    val RES_MP_TAC   : (term frag list, term frag list) subst -> thm -> tactic

    val UNABBREV_RULE : term frag list -> rule
end
