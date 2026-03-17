signature HOLSourceParser = sig

type scope = (string, int * bool) Binarymap.dict

val initialScope: scope

type result = {
  getScope: unit -> scope,
  parseDec: unit -> HOLSourceAST.dec option,
  body: DString.dstring,
  events: HOLSourceAST.events,
  parseError: int * int -> string -> unit }

val simpleParseError: int * int -> string -> unit
val filelineParseError: DString.dstring * HOLSourceAST.events ->
  int * int -> string -> unit

val parseSML: string -> (int -> string) ->
  (DString.dstring * HOLSourceAST.events -> int * int -> string -> unit) ->
  scope -> result

end
