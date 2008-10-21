signature ConseqConv =
sig

include Abbrev


(*Types*)
type conseq_conv = term -> thm;
type CONSEQ_CONV_direction;
type directed_conseq_conv = CONSEQ_CONV_direction -> conseq_conv;

val CONSEQ_CONV_STRENGTHEN_direction : CONSEQ_CONV_direction;
val CONSEQ_CONV_WEAKEN_direction     : CONSEQ_CONV_direction;
val CONSEQ_CONV_UNKNOWN_direction    : CONSEQ_CONV_direction;




(*Basic CONSEQ-Convs*)
val FALSE_CONSEQ_CONV       : conseq_conv;
val TRUE_CONSEQ_CONV        : conseq_conv;
val REFL_CONSEQ_CONV        : conseq_conv;
val FORALL_EQ___CONSEQ_CONV : conseq_conv;
val EXISTS_EQ___CONSEQ_CONV : conseq_conv;

val TRUE_FALSE_REFL_CONSEQ_CONV : directed_conseq_conv
val CONSEQ_TOP_REWRITE_CONV     : thm list -> directed_conseq_conv;
val CONSEQ_REWRITE_CONV         : thm list -> directed_conseq_conv;




(*Tacticals for CONSEQ-Convs*)
val CHANGED_CONSEQ_CONV    : conseq_conv -> conseq_conv;
val QCHANGED_CONSEQ_CONV   : conseq_conv -> conseq_conv;
val ORELSE_CONSEQ_CONV     : conseq_conv -> conseq_conv -> conseq_conv
val THEN_CONSEQ_CONV       : conseq_conv -> conseq_conv -> conseq_conv;
val FIRST_CONSEQ_CONV      : conseq_conv list -> conseq_conv;
val EVERY_CONSEQ_CONV      : conseq_conv list -> conseq_conv;

val FORALL_CONSEQ_CONV     : conseq_conv -> conseq_conv;
val EXISTS_CONSEQ_CONV     : conseq_conv -> conseq_conv;
val QUANT_CONSEQ_CONV      : conseq_conv -> conseq_conv;

val STRENGTHEN_CONSEQ_CONV : conseq_conv -> directed_conseq_conv;
val WEAKEN_CONSEQ_CONV     : conseq_conv -> directed_conseq_conv;


val DEPTH_CONSEQ_CONV      : directed_conseq_conv -> directed_conseq_conv;
val ONCE_DEPTH_CONSEQ_CONV : directed_conseq_conv -> directed_conseq_conv;
val NUM_DEPTH_CONSEQ_CONV  : directed_conseq_conv -> int ->
			     directed_conseq_conv;

val CONJ_ASSUMPTIONS_CONSEQ_CONV : directed_conseq_conv -> 
				   (term -> bool) -> directed_conseq_conv;
val DEPTH_STRENGTHEN_CONSEQ_CONV : conseq_conv -> conseq_conv;




(*Rules*)
val STRENGTHEN_CONSEQ_CONV_RULE  : directed_conseq_conv -> thm -> thm;
val WEAKEN_CONSEQ_CONV_RULE      : directed_conseq_conv -> thm -> thm;




(*Tactics*)
val CONSEQ_CONV_TAC              : directed_conseq_conv -> tactic;
val DEPTH_CONSEQ_CONV_TAC        : directed_conseq_conv -> tactic;
val ONCE_DEPTH_CONSEQ_CONV_TAC   : directed_conseq_conv -> tactic;
val CONJ_ASSUMPTIONS_DEPTH_CONSEQ_CONV : directed_conseq_conv -> directed_conseq_conv;


end

