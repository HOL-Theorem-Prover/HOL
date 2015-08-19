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

  (* tools *)
  val variants         : term list -> term list -> term list
  val HALF_BETA_EXPAND : term list -> thm -> thm
  val make_definitions : string -> thm -> thm
  val canonicalize_clauses : term list -> thm
  val unschematize_clauses : term list -> term list * term list
  val check_definition     : term list -> locn.locn list -> term -> term
  val generalize_schematic_variables :  term list -> thm -> thm

end
