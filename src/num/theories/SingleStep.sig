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

  val PURE_TOP_CASE_TAC : tactic      (* The top-most case-split *)
  val PURE_CASE_TAC     : tactic      (* The smallest case-split *)
  val CASE_SIMP_CONV    : conv        (* The case rewrites in the typebase *)
  val CASE_TAC          : tactic      (* PURE_CASE_TAC THEN simplification *)

end
