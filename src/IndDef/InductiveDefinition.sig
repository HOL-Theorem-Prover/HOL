signature InductiveDefinition =
sig
  include Abbrev

  type monoset = (string * tactic) list
  val bool_monoset : monoset

  val new_inductive_definition : monoset -> term -> thm * thm * thm

  (* Support functions *)

  val prove_nonschematic_inductive_relations_exist : monoset -> term -> thm
  val derive_nonschematic_inductive_relations : term -> thm
  val prove_monotonicity_hyps : monoset -> thm -> thm
  val prove_inductive_relations_exist : monoset -> term -> thm
  val MONO_TAC : monoset -> tactic
  val BACKCHAIN_TAC : thm -> tactic

end;
