(* ========================================================================= *)
(*                                                                           *)
(*     Inductive Definitions (John Harrison)                                 *)
(*                                                                           *)
(*                                                                           *)
(* ========================================================================= *)

signature InductiveDefinition =
sig
  include Abbrev

  type monoset = (string * thm) list
  val bool_monoset : monoset
  val MONO_TAC     : monoset -> tactic
  val BACKCHAIN_TAC: thm -> tactic

  val prove_inductive_relations_exist : monoset -> term -> thm
  val new_inductive_definition        : monoset -> string ->
                                        term * locn.locn list->
                                        thm * thm * thm

  val prove_nonschematic_inductive_relations_exist : monoset -> term -> thm
  val derive_nonschematic_inductive_relations : term -> thm
  val prove_monotonicity_hyps : monoset -> thm -> thm

end;
