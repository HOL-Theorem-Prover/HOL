signature DefinitionDoc =
sig

 type term = Term.term
 type thm = Thm.thm

  (* This signature file is for documentation purposes only,
     and is a temporary workaround for GitHub issue #238 *)

  val new_type_definition   : string * thm -> thm
  val new_definition        : string * term -> thm
  val new_specification     : string * string list * thm -> thm
  val gen_new_specification : string * thm -> thm

  val new_definition_hook   : ((term -> term list * term) * (term list * thm -> thm)) ref

end
