exception SyntaxError of string
val parse :
  Holparsesupp.mode ->
  (('a -> Holparse.token) -> Lexing.lexbuf -> 'b) -> Lexing.lexbuf -> 'b
val parse_chan :
  Holparsesupp.mode ->
  (('a -> Holparse.token) -> Lexing.lexbuf -> 'b) -> in_channel -> 'b
val parse_fileargs_ext :
  (string * Arg.spec * string) list ->
  (unit -> unit) ->
  string ->
  Holparsesupp.mode ->
  (('a -> Holparse.token) -> Lexing.lexbuf -> 'b) -> 'b
val parse_fileargs :
  Holparsesupp.mode ->
  (('a -> Holparse.token) -> Lexing.lexbuf -> 'b) -> 'b
