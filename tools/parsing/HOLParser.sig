signature HOLParser = sig

type scope = (string, int * bool) Binarymap.dict

val initialScope: scope

type result = {
  getScope: unit -> scope,
  parseDec: unit -> HOLAst.dec option,
  body: DString.dstring,
  events: HOLAst.events }

(* filename -> start * stop -> message -> unit *)
val simpleParseError: string -> int * int -> string -> unit

val parseSML: string -> (int -> string) -> (string -> int * int -> string -> unit) ->
  scope -> result

end
