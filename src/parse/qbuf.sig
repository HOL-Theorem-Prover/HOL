signature qbuf = sig

  (* a type of (stateful) lexing buffer designed to handle quotations *)
  type 'a qbuf

  val new_buffer : 'a frag list -> 'a qbuf

  val current : 'a qbuf -> 'a base_tokens.base_token

  val replace_current : 'a base_tokens.base_token -> 'a qbuf -> unit

  val advance : 'a qbuf -> unit

  val lex_to_toklist : 'a frag list -> 'a base_tokens.base_token list

  val toString : 'a qbuf -> string

end;

