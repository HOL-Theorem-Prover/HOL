signature ncLib =
sig

  include Abbrev
  exception ProofFailed of (term list * term) list

  val NEW_TAC : string -> term -> tactic
  val NEW_ELIM_TAC : tactic
  val prove_vsubst_result : thm -> tactic option -> thm
  val vsubst_tac : thm -> tactic

  val recursive_term_function_existence : term -> thm
  val prove_recursive_term_function_exists : term -> thm
  val define_recursive_term_function :
      term quotation -> thm * thm option

end;
