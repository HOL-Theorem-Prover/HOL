(* Grammar.sig *)

signature GRAMMAR =
sig

  exception ParserError of string

  val lexer_definition : (unit -> Token.token) -> Syntax.lexer_definition

end (* signature GRAMMAR *)
