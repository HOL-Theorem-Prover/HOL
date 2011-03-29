signature blastLib =
sig
    include Abbrev

    val BIT_BLAST_CONV  : conv

    val BBLAST_CONV     : conv
    val BBLAST_PROVE    : conv
    val BBLAST_RULE     : rule
    val BBLAST_TAC      : tactic
    val FULL_BBLAST_TAC : tactic

    val EBLAST_CONV     : conv
    val EBLAST_PROVE    : conv
    val EBLAST_RULE     : rule
    val EBLAST_TAC      : tactic
end
