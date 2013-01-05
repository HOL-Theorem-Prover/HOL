signature quantHeuristicsLibAbbrev =
sig
 include Abbrev

 type selection_fun = term -> (term -> int) -> term -> (term * string) list

  (* The main conv and tactic *)

  (* introduce a new variable as abbreviation for terms selected by the selection_funs
     and try to instantiate this variable using the quantifier heuristics *)
  val QUANT_ABBREV_CONV        : selection_fun list -> quantHeuristicsLibBase.quant_param list -> conv
  val QUANT_ABBREV_TAC         : selection_fun list -> quantHeuristicsLibBase.quant_param list -> tactic

  (* a simple version that does not try to instantiate the new quatifier *)
  val SIMPLE_QUANT_ABBREV_CONV : selection_fun list -> conv
  val SIMPLE_QUANT_ABBREV_TAC  : selection_fun list -> tactic


  (* Some simple selection funs *)
  val select_funs_combine : selection_fun list -> selection_fun

  val select_fun_constant : term -> int -> string -> selection_fun
  val FST_select_fun      : selection_fun
  val SND_select_fun      : selection_fun
  val select_fun_pabs     : string -> selection_fun
  val PAIR_select_fun     : selection_fun

  val THE_select_fun      : selection_fun
  val IS_SOME_select_fun  : selection_fun

  val select_fun_match_occ   : int -> term frag list -> (term -> string) -> selection_fun
  val select_fun_match       : term frag list -> string -> selection_fun
  val select_fun_pattern_occ : int -> term frag list -> selection_fun
  val select_fun_pattern     : term frag list -> selection_fun

end
