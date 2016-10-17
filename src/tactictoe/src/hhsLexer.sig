signature hhsLexer =
sig

  val is_blank   : char -> bool
  val is_blank_string : string -> bool
  val is_tquote  : string -> bool
  val is_dtquote : string -> bool
  val rm_tquote  : string -> string
  val rm_squote  : string -> string
  val rm_blank   : string -> string

  val hhs_lex_blank : string -> string list
  val hhs_lex : string -> string list

end
