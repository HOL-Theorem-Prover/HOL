signature pairTools =
sig
 include Abbrev

 val let_CONV         : conv   (* from Let_conv *)
 val PAIRED_BETA_CONV : conv   (* from Let_conv *)
 val PAIRED_ETA_CONV  : conv   (* from Let_conv *)
 val GEN_BETA_CONV    : conv   (* from Let_conv *)
 val GEN_BETA_RULE    : thm -> thm
 val GEN_BETA_TAC     : tactic

 val PGEN             : term -> term -> thm -> thm
 val PGEN_TAC         : term -> tactic

 val LET_INTRO        : thm -> thm
 val LET_INTRO_TAC    : tactic
 val LET_EQ_TAC       : thm list -> tactic
 val TUPLE            : term -> thm -> thm
 val TUPLE_TAC        : term -> tactic

end;
