signature smlLexer =
sig

  val rm_comment : string -> string
  val partial_sml_lexer : string -> string list

end
