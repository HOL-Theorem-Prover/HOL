signature boolTools =
sig
 type tactic = Abbrev.tactic;
 type conv = Abbrev.conv;
 type term = Term.term
 type hol_type = Type.hol_type
 type thm = Thm.thm

    val TAUT_CONV : conv
    val NNF_CONV : conv
    val NNF_TAC : tactic
    val NTAC : int -> tactic -> tactic
    val Sterm: term frag list -> unit
    val WEAKEN_TAC :term list -> tactic
    val DEST_IFF : thm -> {ltor:thm, rtol:thm}
    val GAP_TAC : tactic
    val variants : term list -> term list -> term list * term list
    val GEN_CASES_TAC : thm -> tactic
    val BC_TAC : thm -> tactic
    val ASM_BC_TAC : tactic

    val PULL_LET : thm
    val LET_THM : thm
    val COND_CONG : thm
    val LET_CONG : thm
    val WIMP_CONG : thm
    val IMP_CONG : thm
end;
