local
  open monadic_parse

in
  datatype 'a type_token =
    TypeIdent of string | TypeVar of string | Comma | LParen | RParen |
    AQ of 'a

  val lex : ('a type_token, 'a frag) Parser

  val token_string : 'a type_token -> string
  val dest_aq : 'a type_token -> 'a

  val is_ident : 'a type_token -> bool
  val is_tvar : 'a type_token -> bool
  val is_aq : 'a type_token -> bool

end