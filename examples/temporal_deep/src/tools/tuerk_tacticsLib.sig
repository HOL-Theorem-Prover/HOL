signature tuerk_tacticsLib =
sig

  val FORALL_EQ_STRIP_TAC  : Abbrev.tactic
  val EXISTS_EQ_STRIP_TAC  : Abbrev.tactic
  val CLEAN_ASSUMPTIONS_TAC : Abbrev.tactic
  val REWRITE_ASSUMPTIONS_TAC : Abbrev.thm list -> Abbrev.tactic
  val REWRITE_ALL_TAC : Abbrev.thm list -> Abbrev.tactic
  val ONCE_REWRITE_ASSUMPTIONS_TAC : Abbrev.thm list -> Abbrev.tactic
  val ONCE_REWRITE_ALL_TAC : Abbrev.thm list -> Abbrev.tactic
  val SIMP_ASSUMPTIONS_TAC : simpLib.simpset -> Abbrev.thm list -> Abbrev.tactic
  val SIMP_ALL_TAC : simpLib.simpset -> Abbrev.thm list -> Abbrev.tactic
  val DISJ_EQ_STRIP_TAC : Abbrev.tactic
  val CONJ_EQ_STRIP_TAC : Abbrev.tactic
  val A_IMP_EQ_STRIP_TAC : Abbrev.tactic
  val C_IMP_EQ_STRIP_TAC : Abbrev.tactic
  val BOOL_EQ_STRIP_TAC : Abbrev.tactic

  val WEAKEN_HD_TAC : Abbrev.tactic
  val IMP_TAC : Abbrev.thm -> Abbrev.tactic
  val SET_INDUCT_TAC : Abbrev.tactic
  val GSYM_NO_TAC : int -> Abbrev.tactic
  val WEAKEN_NO_TAC : int -> Abbrev.tactic

  val SUBGOAL_TAC : Abbrev.term frag list -> Abbrev.tactic
  val REMAINS_TAC : Abbrev.term frag list -> Abbrev.tactic
  val SPEC_NO_ASSUM : int -> Abbrev.term -> Abbrev.tactic
  val SPECL_NO_ASSUM : int -> Abbrev.term list -> Abbrev.tactic
  val Q_SPEC_NO_ASSUM : int -> Abbrev.term frag list  -> Abbrev.tactic
  val Q_SPECL_NO_ASSUM : int -> Abbrev.term frag list list -> Abbrev.tactic

  val UNDISCH_HD_TAC : Abbrev.tactic
  val UNDISCH_ALL_TAC : Abbrev.tactic
  val UNDISCH_NO_TAC : int -> Abbrev.tactic
  val UNDISCH_KEEP_NO_TAC: int -> Abbrev.tactic
  val POP_NO_ASSUM : int -> (Abbrev.thm -> Abbrev.tactic) -> Abbrev.tactic
  val LEFT_DISJ_TAC : Abbrev.tactic
  val RIGHT_DISJ_TAC : Abbrev.tactic
  val LEFT_CONJ_TAC : Abbrev.tactic
  val RIGHT_CONJ_TAC : Abbrev.tactic
  val IMP_TO_EQ_TAC : Abbrev.tactic

  val EXISTS_LEAST_TAC___GEN : Abbrev.term -> Abbrev.tactic -> Abbrev.tactic;
  val EXISTS_LEAST_TAC : Abbrev.term -> Abbrev.tactic;
  val Q_EXISTS_LEAST_TAC : Abbrev.term frag list -> Abbrev.tactic;


  val PROVE_CONDITION_TAC : (Abbrev.thm -> Abbrev.tactic)
  val PROVE_CONDITION_NO_ASSUM : int -> Abbrev.tactic

  val MATCH_LEFT_EQ_MP_TAC : Abbrev.thm -> Abbrev.tactic;
  val MATCH_RIGHT_EQ_MP_TAC : Abbrev.thm -> Abbrev.tactic;

  val store_simp_thm: (string * Abbrev.term * Abbrev.tactic) -> Abbrev.thm
end

