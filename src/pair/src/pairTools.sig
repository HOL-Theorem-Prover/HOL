signature pairTools =
sig
 type term = Term.term
 type thm  = Thm.thm
 type conv = Abbrev.conv
 type tactic = Abbrev.tactic

 val mk_aabs          : term * term -> term
 val dest_aabs        : term -> term * term
 val strip_aabs       : term -> term list * term
 val list_mk_aabs     : term list * term -> term
 val mk_fst           : term -> term
 val mk_snd           : term -> term

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
