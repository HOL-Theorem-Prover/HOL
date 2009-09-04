(* Subject: Mutually recursive rule induction *)
(* Author: Myra Van Inwegen *)
(* Part of the author's doctoral dissertation *)

signature ind_rel =
sig

val   check_inductive_relations :
         Term.term list ->     (* patterns *)
         Term.term ->          (* term giving rules *)
         Term.term list        (* each term corresponds to a quantified rule *)
val   define_inductive_relations :
         Term.term list ->     (* patterns *)
         Term.term ->          (* term giving rules *)
         Thm.thm * Thm.thm     (* rules_satisfied theorem, induction theorem *)
val   prove_inversion_theorems :
         Thm.thm ->            (* rules_satisfied theorem *)
         Thm.thm ->            (* induction theorem *)
         Thm.thm list          (* inversion theorems *)
val   prove_strong_induction :
         Thm.thm ->            (* rules_satisfied theorem *)
         Thm.thm ->            (* induction theorem *)
         Thm.thm               (* strong induction theorem *)
val   rule_induct :
         Thm.thm ->            (* induction theorem (strong or regular) *)
	 Abbrev.tactic         (* sets up induction *)

end;
