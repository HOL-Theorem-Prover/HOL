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
                        rel list * (mlsp * int * int) list

end

(* [remove_listrels lspinfo rels] returns an (rel', info) pair, where rel'
   is an adjusted rel list where internal list blocks have been removed
   and replaced with single TM values. The info is information about where
   those list blocks are and how many TMs of the original have been consumed
   to form them.

   For example,

     remove_listrels [("let","in",lsp)]
                     [TM, TOK "let", TM, TOK ";", TM, TOK "in"]

   will return

     ([TM, TOK "let", TM, TOK "in"], [(lsp, 1, 2)]

   reflecting the fact the "list" that will be injected at the 2nd TM position
   is built from two arguments starting at index 1 (indexing into the list of
   "args", that is, the list of TMs).
*)
