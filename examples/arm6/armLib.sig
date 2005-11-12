signature armLib =
sig
    include Abbrev

    val stdi_ss      : simpLib.simpset
    val fcp_ss       : simpLib.simpset
    val ICLASS_ss    : simpLib.ssfrag
    val PBETA_ss     : simpLib.ssfrag
    val STATE_INP_ss : simpLib.ssfrag

    val combCases    : term -> thm
    val tupleCases   : term -> thm

    val RES_MP1_TAC  : (term frag list, term frag list) subst -> thm -> tactic
    val RES_MP_TAC   : (term frag list, term frag list) subst -> thm -> tactic
end
