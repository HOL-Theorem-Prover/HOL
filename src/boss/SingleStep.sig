signature SingleStep =
sig

  type thm      = Thm.thm
  type term     = Term.term
  type tactic   = Abbrev.tactic
  type 'a quotation = 'a Portable.frag list

  val Cases             : tactic
  val Induct            : tactic
  val recInduct         : thm -> tactic

  val Cases_on          : term quotation -> tactic
  val Induct_on         : term quotation -> tactic
  val completeInduct_on : term quotation -> tactic
  val measureInduct_on  : term quotation -> tactic

  val SPOSE_NOT_THEN    : (thm -> tactic) -> tactic
  val by                : term quotation * tactic -> tactic  (* infix *)

end
