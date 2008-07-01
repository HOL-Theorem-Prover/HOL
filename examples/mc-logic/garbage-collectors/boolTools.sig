signature boolTools =
sig

include Abbrev


val bool_eq_imp_CONV : conv;
val bool_neg_pair_CONV : conv;
val bool_imp_extract_CONV : conv;
val REFL_IMP_CONV : conv;
val GEN_IMP : term -> thm -> thm;


val bool_eq_imp_ss : simpLib.ssfrag;
val bool_neg_pair_ss : simpLib.ssfrag;
val bool_imp_extract_ss : simpLib.ssfrag;

val GEN_ASSUM : term -> thm -> thm;

val STRENGTHEN_CONV_WRAPPER : conv -> conv;
val DEPTH_STRENGTHEN_CONV : conv -> conv;
val UNCHANGED_STRENGTHEN_CONV : conv -> conv;
val ORELSE_STRENGTHEN_CONV : conv list -> conv;
val CONJ_ASSUMPTIONS_STRENGTHEN_CONV : conv -> term list -> conv;


val IMP_STRENGTHEN_CONV_RULE : conv -> rule;
val STRENGTHEN_CONV_TAC : conv -> tactic;
val DEPTH_STRENGTHEN_CONV_TAC : conv -> tactic;
val CONJ_ASSUMPTIONS_DEPTH_STRENGTHEN_CONV : conv -> conv;



val COND_REWR_CONV : thm -> term -> thm
val COND_REWRITE_CONV : thm list -> term -> thm
val GUARDED_COND_REWRITE_CONV : (term -> bool) -> thm list -> term -> thm

end

