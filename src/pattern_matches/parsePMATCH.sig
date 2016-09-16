signature parsePMATCH =
sig

  type add_record =
       { block_style : Parse.PhraseBlockStyle * Parse.block_info,
         fixity : term_grammar.fixity,
         paren_style : Parse.ParenStyle,
         pp_elements : Parse.pp_element list,
         term_name : string }

  val add_pmatch :
    { get : 'a -> term_grammar.grammar,
      arule : add_record -> 'a -> 'a,
      rmtmtok : {term_name :string, tok : string} -> 'a -> 'a,
      add_ptmproc : string * int -> term_grammar.preterm_processor -> 'a -> 'a,
      addup : 'b -> 'a -> 'a, (* user printer *)
      up : 'b } -> 'a -> 'a

end
