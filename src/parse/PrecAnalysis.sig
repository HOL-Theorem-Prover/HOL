signature PrecAnalysis =
sig

  type rel = HOLgrammars.rule_element
  type rell_transform = rel list -> rel list
  type mlsp = HOLgrammars.mini_lspec
  val rule_equalities : term_grammar.rule_record ->
                        (string * bool * string) list

  val mkrels_infix : rell_transform
  val mkrels_suffix : rell_transform
  val mkrels_closefix : rell_transform
  val mkrels_prefix : rell_transform


  val check_for_listreductions :
      (string * string -> 'a option) -> rel list ->
      (string * string * 'a) list
  val remove_listrels : (string * string * mlsp) list -> rel list ->
                        rel list * (mlsp * int list) list

end
