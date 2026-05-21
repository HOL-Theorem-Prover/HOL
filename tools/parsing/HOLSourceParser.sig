signature HOLSourceParser = sig

(* A scope represents the local state of the parser, containing the list of infixes.
  A key-value pair tok->(n, false) means that tok is a left associative infix
  operator of precedence n, and tok->(n, true) is a right associative infix.
  The scope is updated by declarations, both locally and at the top level. *)
type scope = (string, int * bool) Binarymap.dict

(* The initial scope, used by default at the beginning of a HOL file.
  This includes all of the infixes from the SML basis library, as well as
  built-in infixes from the tactic library such as >> and >- . *)
val initialScope: scope

type result = {
  getScope: unit -> scope,
  parseDec: unit -> HOLSourceAST.dec option,
  body: DString.dstring,
  events: HOLSourceAST.events,
  parseError: int * int -> string -> unit }

val simpleParseError: (string -> unit) -> int * int -> string -> unit
val filelineParseError: (string -> unit) ->
  DString.dstring * HOLSourceAST.events -> int * int -> string -> unit

(* Wrap a print sink so that every call additionally flips a "had error"
   flag.  Intended for callers that drive the parser as a build step and
   need to translate "did the parser report any errors?" into an exit
   status.  The sink in HOLSource.{file,stream,string,input}ToReader is
   used solely for error reports, so counting calls = counting errors. *)
val trackingPrint: (string -> unit) ->
  {print: string -> unit, hadError: unit -> bool}

val parseSML: string -> (int -> string) ->
  (DString.dstring * HOLSourceAST.events -> int * int -> string -> unit) ->
  scope -> result

end
