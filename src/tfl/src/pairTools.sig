signature pairTools =
sig
 type term = Term.term
 type thm  = Thm.thm
 type conv = Abbrev.conv
 type tactic = Abbrev.tactic

 val dest_aabs : term -> term * term
 val strip_aabs : term -> term list * term
 val list_mk_aabs : term list * term -> term
 val betaConv : conv
 val PGEN : term -> term -> thm -> thm

 val mk_fst : term -> term
 val mk_snd : term -> term
 val LET_INTRO : thm -> thm
 val LET_INTRO_TAC : tactic
 val PULL_LET2 : thm
 val PULL_LET3X2 : thm
 val TUPLE : term -> thm -> thm
 val TUPLE_TAC : term -> tactic

end;
