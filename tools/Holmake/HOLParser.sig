signature HOLParser = sig

type scope = (string, int * bool) Binarymap.dict

val initialScope: scope

type result = {
  getScope: unit -> scope,
  parseDec: unit -> HOLAst.dec option,
  body: DString.dstring,
  events: HOLAst.events }

val parseSML: string -> (int -> string) -> (int * int -> string -> unit) ->
  scope -> result

end
