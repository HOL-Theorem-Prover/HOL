exception SyntaxError of string
val pretty_pos : Lexing.lexbuf -> string
val parse :
  Holparsesupp.mode ->
  (('a -> Holparse.token) -> Lexing.lexbuf -> 'b) -> Lexing.lexbuf -> 'b
val parse_chan :
  Holparsesupp.mode ->
  (('a -> Holparse.token) -> Lexing.lexbuf -> 'b) -> 'c -> 'b
