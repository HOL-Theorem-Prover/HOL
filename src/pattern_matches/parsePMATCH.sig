signature parsePMATCH =
sig

  type 'a add_record =
       { block_style : Parse.PhraseBlockStyle * Parse.block_info,
         fixity : 'a,
         paren_style : Parse.ParenStyle,
         pp_elements : Parse.pp_element list,
         term_name : string }
  val ar_fixity_fupd : ('a -> 'b) -> 'a add_record -> 'b add_record

  val add_pmatch :
    { get : 'a -> term_grammar.grammar,
      arule : term_grammar.rule_fixity add_record -> 'a -> 'a,
      rmtmtok : {term_name :string, tok : string} -> 'a -> 'a,
      add_ptmproc : string * int -> term_grammar.preterm_processor -> 'a -> 'a,
      addup : 'b -> 'a -> 'a, (* user printer *)
      up : 'b } -> 'a -> 'a

end
