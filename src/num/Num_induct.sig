signature Num_induct =
sig
   val INDUCT : Thm.thm * Thm.thm -> Thm.thm
   val INDUCT_TAC : Abbrev.tactic
end;
