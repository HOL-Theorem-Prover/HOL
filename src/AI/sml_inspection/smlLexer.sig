signature smlLexer =
sig
  
  (* lexer *)
  val rm_comment : string -> string
  val partial_sml_lexer : string -> string list

  (* reserved tokens *)
  val is_quoted   : string -> bool
  val is_number   : string -> bool
  val is_chardef  : string -> bool
  val is_reserved : string -> bool

end
