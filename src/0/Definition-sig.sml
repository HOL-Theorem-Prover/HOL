signature Definition =
sig
  type term = Term.term
  type thm  = Thm.thm

  val new_type_definition : string * thm -> thm
  val new_definition      : string * term -> thm
  val new_specification   : string * string list * thm -> thm

  val new_definition_hook : ((term -> term list * term) *
                             (term list * thm -> thm)) ref
end
