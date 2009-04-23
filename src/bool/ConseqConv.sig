signature ConseqConv =
sig

include Abbrev


(*
  trace "DEPTH_CONSEQ_CONV" can be used to get debug information
  on DEPTH_CONSEQ_CONV and related conversions
*)


(* Types *)
datatype CONSEQ_CONV_direction =  
         CONSEQ_CONV_STRENGTHEN_direction
       | CONSEQ_CONV_WEAKEN_direction
       | CONSEQ_CONV_UNKNOWN_direction;

type conseq_conv = term -> thm;
type directed_conseq_conv = CONSEQ_CONV_direction -> conseq_conv;



(* General *)
val GEN_ASSUM               : term -> thm -> thm;
val GEN_IMP                 : term -> thm -> thm;
val SPEC_ALL_TAC            : tactic;

val IMP_QUANT_CANON             : thm -> thm;
val IMP_FORALL_CONCLUSION_CANON : thm -> thm;
val IMP_EXISTS_PRECOND_CANON    : thm -> thm;



(* Basic consequence conversions *)
val FALSE_CONSEQ_CONV       : conseq_conv;
val TRUE_CONSEQ_CONV        : conseq_conv;
val REFL_CONSEQ_CONV        : conseq_conv;
val FORALL_EQ___CONSEQ_CONV : conseq_conv;
val EXISTS_EQ___CONSEQ_CONV : conseq_conv;

val TRUE_FALSE_REFL_CONSEQ_CONV : directed_conseq_conv
val CONSEQ_TOP_REWRITE_CONV     : (thm list * thm list * thm list) -> directed_conseq_conv;
val CONSEQ_REWRITE_CONV         : (thm list * thm list * thm list) -> directed_conseq_conv;
val CONSEQ_HO_TOP_REWRITE_CONV  : (thm list * thm list * thm list) -> directed_conseq_conv;
val CONSEQ_HO_REWRITE_CONV      : (thm list * thm list * thm list) -> directed_conseq_conv;


(* Technical stuff that might help writing
   your own CONSEQ-CONVs *)
val CONSEQ_CONV_DIRECTION_NEGATE      : CONSEQ_CONV_direction -> CONSEQ_CONV_direction;
val CONSEQ_CONV___GET_SIMPLIFIED_TERM : thm -> term -> term;
val CONSEQ_CONV___GET_DIRECTION       : thm -> term -> CONSEQ_CONV_direction;
val THEN_CONSEQ_CONV___combine        : thm -> thm -> term -> thm;
val CONSEQ_CONV___APPLY_CONV_RULE     : thm -> term -> (term -> thm) -> thm;

(* Combinations for consequence conversions *)
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
val REDEPTH_CONSEQ_CONV    : directed_conseq_conv -> directed_conseq_conv;
val ONCE_DEPTH_CONSEQ_CONV : directed_conseq_conv -> directed_conseq_conv;
val NUM_DEPTH_CONSEQ_CONV  : directed_conseq_conv -> int ->
			     directed_conseq_conv;
val NUM_REDEPTH_CONSEQ_CONV: directed_conseq_conv -> int ->
			     directed_conseq_conv

val CONJ_ASSUMPTIONS_CONSEQ_CONV   : directed_conseq_conv -> 
				     (term -> bool) -> directed_conseq_conv;
val DEPTH_STRENGTHEN_CONSEQ_CONV   : conseq_conv -> conseq_conv;
val REDEPTH_STRENGTHEN_CONSEQ_CONV : conseq_conv -> conseq_conv;




(* Rules *)
val STRENGTHEN_CONSEQ_CONV_RULE  : directed_conseq_conv -> thm -> thm;
val WEAKEN_CONSEQ_CONV_RULE      : directed_conseq_conv -> thm -> thm;




(* Tactics *)
val CONSEQ_CONV_TAC              : directed_conseq_conv -> tactic;
val DEPTH_CONSEQ_CONV_TAC        : directed_conseq_conv -> tactic;
val REDEPTH_CONSEQ_CONV_TAC      : directed_conseq_conv -> tactic;
val ONCE_DEPTH_CONSEQ_CONV_TAC   : directed_conseq_conv -> tactic;
val CONJ_ASSUMPTIONS_DEPTH_CONSEQ_CONV : directed_conseq_conv -> directed_conseq_conv;
val CONJ_ASSUMPTIONS_REDEPTH_CONSEQ_CONV : directed_conseq_conv -> directed_conseq_conv;
val CONSEQ_REWRITE_TAC           : (thm list * thm list * thm list) -> tactic;
val CONSEQ_HO_REWRITE_TAC        : (thm list * thm list * thm list) -> tactic;
val ONCE_CONSEQ_REWRITE_TAC      : (thm list * thm list * thm list) -> tactic;
val ONCE_CONSEQ_HO_REWRITE_TAC   : (thm list * thm list * thm list) -> tactic;


end

