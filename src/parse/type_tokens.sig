signature type_tokens = sig

  datatype 'a type_token
      = TypeIdent of string
      | QTypeIdent of string * string (* thy name * type name *)
      | TypeSymbol of string
      | TypeVar of string
      | Comma
      | LParen
      | RParen
      | LBracket 
      | RBracket
      | AQ of 'a
      | Error of 'a base_tokens.base_token

  val typetok_of : 'a qbuf.qbuf -> ((unit -> unit) * 'a type_token locn.located)

  val token_string : 'a type_token -> string
  val dest_aq : 'a type_token -> 'a

  val is_ident : 'a type_token -> bool
  val is_typesymbol : 'a type_token -> bool
  val is_tvar : 'a type_token -> bool
  val is_aq : 'a type_token -> bool

end
