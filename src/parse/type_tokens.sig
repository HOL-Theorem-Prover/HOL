signature type_tokens = sig

  datatype 'a type_token =
    TypeIdent of string | TypeSymbol of string | TypeVar of string |
    Comma | LParen | RParen |
    AQ of 'a

  val lex : ('a type_token, 'a frag) monadic_parse.Parser

  val token_string : 'a type_token -> string
  val dest_aq : 'a type_token -> 'a

  val is_ident : 'a type_token -> bool
  val is_typesymbol : 'a type_token -> bool
  val is_tvar : 'a type_token -> bool
  val is_aq : 'a type_token -> bool

end