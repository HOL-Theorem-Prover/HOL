signature pairTools =
sig
 include Abbrev

 val PGEN             : term -> term -> thm -> thm
 val PGEN_TAC         : term -> tactic
 val PFUN_EQ_RULE     : thm -> thm

 val PAIR_EX          : term -> term -> thm

 val LET_INTRO        : thm -> thm
 val LET_INTRO_TAC    : tactic
 val LET_EQ_TAC       : thm list -> tactic
 val TUPLE            : term -> thm -> thm
 val TUPLE_TAC        : term -> tactic
 val SPLIT_QUANT_CONV : term -> conv
 val ELIM_TUPLED_QUANT_CONV : conv

 val PABS_ELIM_CONV   : conv
 val PABS_INTRO_CONV  : term -> conv

end;
