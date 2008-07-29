signature ConseqConv =
sig

include Abbrev


val REFL_IMP_CONV : conv;
val GEN_IMP : term -> thm -> thm;
val GEN_ASSUM : term -> thm -> thm;



val CONSEQ_CONV_WRAPPER : conv -> conv;
val DEPTH_CONSEQ_CONV : conv -> conv;
val ONCE_DEPTH_CONSEQ_CONV : conv -> conv;
val NUM_DEPTH_CONSEQ_CONV : int -> conv -> conv;
val CHANGED_CONSEQ_CONV : conv -> conv;
val FIRST_CONSEQ_CONV : conv list -> conv;
val CONJ_ASSUMPTIONS_CONSEQ_CONV : conv -> (term -> bool) -> conv;


val IMP_CONSEQ_CONV_RULE : conv -> rule;
val CONSEQ_CONV_TAC : conv -> tactic;
val DEPTH_CONSEQ_CONV_TAC : conv -> tactic;
val ONCE_DEPTH_CONSEQ_CONV_TAC : conv -> tactic;
val CONJ_ASSUMPTIONS_DEPTH_CONSEQ_CONV : conv -> conv;



end

