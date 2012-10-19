signature quantHeuristicsLibAbbrev =
sig
 include Abbrev

  type selection_fun = term -> (term * string) option

  (* The main conv and tactic *)

  val QUANT_ABBREV_CONV        : selection_fun list -> quant_param list -> conv
  val QUANT_ABBREV_TAC         : selection_fun list -> quant_param list -> tactic

  (* a simple version that does not try to instantiate the new quatifier *)
  val SIMPLE_QUANT_ABBREV_CONV : selection_fun list -> conv
  val SIMPLE_QUANT_ABBREV_TAC  : selection_fun list -> tactic

  (* Some simple selection funs (much more work needed) *)
  val select_fun_constant : term -> string -> selection_fun

  val FST_select_fun     : selection_fun
  val IS_SOME_select_fun : selection_fun
  val SND_select_fun     : selection_fun
  val THE_select_fun     : selection_fun

end
