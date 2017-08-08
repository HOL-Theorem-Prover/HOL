signature PrecAnalysis =
sig

  type rell_transform = HOLgrammars.rule_element list ->
                        HOLgrammars.rule_element list
  val rule_equalities : term_grammar.rule_record ->
                        (string * bool * string) list

  val mkrels_infix : rell_transform
  val mkrels_suffix : rell_transform
  val mkrels_closefix : rell_transform
  val mkrels_prefix : rell_transform

end
