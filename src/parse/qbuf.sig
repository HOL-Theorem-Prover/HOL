signature qbuf = sig

  (* a type of (stateful) lexing buffer designed to handle quotations *)
  type 'a qbuf

  val new_buffer : 'a Portable.frag list -> 'a qbuf

  val current : 'a qbuf -> 'a base_tokens.base_token locn.located

  val replace_current : 'a base_tokens.base_token locn.located -> 'a qbuf -> unit

  val advance : 'a qbuf -> unit

  val lex_to_toklist : 'a Portable.frag list -> 'a base_tokens.base_token locn.located list

  val toString : 'a qbuf -> string

end;
