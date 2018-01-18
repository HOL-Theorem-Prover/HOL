signature hhsLexer =
sig

  val rm_comment : string -> string
  val hhs_lex : string -> string list

end
