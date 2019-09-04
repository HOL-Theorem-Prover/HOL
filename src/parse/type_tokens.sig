signature type_tokens =
sig

  datatype type_token = datatype type_tokens_dtype.type_token

  val typetok_of : 'a qbuf.qbuf -> ((unit -> unit) * 'a type_token locn.located)

  val lextest : string -> unit type_token list

  val token_string : ('a -> string) -> 'a type_token -> string
  val dest_aq : 'a type_token -> 'a

  val is_ident : 'a type_token -> bool
  val is_typesymbol : 'a type_token -> bool
  val is_tvar : 'a type_token -> bool
  val is_aq : 'a type_token -> bool

end
