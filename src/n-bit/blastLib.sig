signature blastLib =
sig
    val BBLAST_CONV      : Conv.conv
    val BBLAST_PROVE     : Conv.conv
    val BBLAST_PROVE_TAC : Tactic.tactic
    val BBLAST_RULE      : Conv.rule
    val BBLAST_TAC       : Tactic.tactic
    val FULL_BBLAST_TAC  : Tactic.tactic
    val MP_BLASTABLE_TAC : Tactic.tactic

    val trace                 : HOLFlags.flag
    val print_counterexamples : HOLFlags.bflag
    val multiply_limit        : HOLFlags.flag
end
