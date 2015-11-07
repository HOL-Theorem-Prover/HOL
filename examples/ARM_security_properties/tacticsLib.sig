signature tacticsLib =
sig
    val UNDISCH_MATCH_TAC : Abbrev.term -> Abbrev.tactic
    val UNDISCH_ALL_TAC  : Abbrev.tactic
    val SPEC_ASSUM_TAC  : Abbrev.term * Abbrev.term list -> Abbrev.tactic
    val SPEC_AND_KEEP_ASSUM_TAC : Abbrev.term * Abbrev.term list -> Abbrev.tactic
    val THROW_AWAY_TAC  : Abbrev.term -> Abbrev.tactic
    val THROW_ONE_AWAY_TAC  : Abbrev.term -> Abbrev.tactic
    val THROW_AWAY_IMPLICATIONS_TAC  : Abbrev.tactic
    val ASSERT_ASSUM_TAC  : Abbrev.term -> Abbrev.tactic
    val PROTECTED_RW_TAC  : Abbrev.term -> Abbrev.tactic
    val PROTECTED_OR_RW_TAC  : Abbrev.thm list -> Abbrev.tactic
    val PROTECTED_OR_SIMP_TAC  : Abbrev.thm list -> Abbrev.tactic
    val CONJ_ASSUM_TAC  : Abbrev.tactic
    val FORCE_REWRITE_TAC  : Abbrev.thm -> Abbrev.tactic
    val FORCE_REV_REWRITE_TAC  : Abbrev.thm -> Abbrev.tactic
    val ASSUME_SPECL_TAC  : Abbrev.term list -> Abbrev.thm -> Abbrev.tactic
    val ASSUME_SIMP_TAC  : Abbrev.thm list -> Abbrev.thm -> Abbrev.tactic
    val IMP_RES_SIMP_TAC  : Abbrev.thm list -> Abbrev.thm -> Abbrev.tactic
    val ASSUME_SPEC_TAC  : Thm.term -> Thm.thm -> Abbrev.tactic
    val ASSUME_SPECL_SIMP_TAC
	: Abbrev.term list -> Abbrev.thm list -> Abbrev.thm -> Abbrev.tactic
    val IMP_RES_SPEC_TAC  : Thm.term -> Thm.thm -> Abbrev.tactic
    val IMP_RES_SPECL_TAC  : Abbrev.term list -> Abbrev.thm -> Abbrev.tactic
    val MP_SPEC_TAC  : Thm.term -> Thm.thm -> Abbrev.tactic
    val MP_SPECL_TAC  : Abbrev.term list -> Abbrev.thm -> Abbrev.tactic
    val ASSUME_SPECL_GEN_REWRITE_TAC
	: Abbrev.term list * Abbrev.thm * Abbrev.thm list -> Abbrev.tactic
    val ASSUME_SPECL_INST_TAC
	:
	Abbrev.term list ->
	(Thm.hol_type, Thm.hol_type) Lib.subst -> Thm.thm -> Abbrev.tactic
end
