exception SyntaxError of string
val parse :
  Holparsesupp.mode ->
  (('a -> Holparse.token) -> Lexing.lexbuf -> 'b) -> Lexing.lexbuf -> 'b
val parse_chan :
  Holparsesupp.mode ->
  (('a -> Holparse.token) -> Lexing.lexbuf -> 'b) -> 'c -> 'b
