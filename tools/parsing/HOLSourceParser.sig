signature HOLSourceParser = sig

type scope = (string, int * bool) Binarymap.dict

val initialScope: scope

type result = {
  getScope: unit -> scope,
  parseDec: unit -> HOLSourceAST.dec option,
  body: DString.dstring,
  events: HOLSourceAST.events }

val simpleParseError: int * int -> string -> unit

val parseSML: string -> (int -> string) -> (int * int -> string -> unit) ->
  scope -> result

end
