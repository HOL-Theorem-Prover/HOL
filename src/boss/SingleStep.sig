signature SingleStep =
sig

  include Abbrev

  val Cases             : tactic
  val Induct            : tactic
  val recInduct         : thm -> tactic

  val Cases_on          : term quotation -> tactic
  val Induct_on         : term quotation -> tactic
  val completeInduct_on : term quotation -> tactic
  val measureInduct_on  : term quotation -> tactic

  val SPOSE_NOT_THEN    : (thm -> tactic) -> tactic
  val by                : term quotation * tactic -> tactic  (* infix *)
  val on                : (thm -> tactic) * (term quotation * tactic) -> tactic
                          (* infix *)
end
