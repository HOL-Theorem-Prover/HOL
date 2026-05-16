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

val parseSML: string -> (int -> string) ->
  (DString.dstring * HOLSourceAST.events -> int * int -> string -> unit) ->
  scope -> result

end

(* ----------------------------------------------------------------------
    Overview
   ----------------------------------------------------------------------

    HOLSourceParser is the recursive-descent parser that turns a
    HOL-flavoured SML source stream into a HOLSourceAST.dec sequence.
    Lexing and parsing are interleaved: a small character-level
    scanner produces tokens on demand, and the parser pulls one
    top-level declaration at a time, growing the input buffer
    (body : DString.dstring) by 1024-byte chunks from the supplied
    read callback.

    Scope.  The infix table is a value of type

      scope = (string, int * bool) Binarymap.dict

    mapping each declared infix operator to its precedence and a
    right-associativity flag (true = right-assoc).  initialScope is
    pre-populated with both the SML-basis infixes and the HOL tactic-
    library operators -- THEN, THEN1, THENL, THEN_LT, THENC, ORELSE,
    ORELSE_LT, ORELSEC, THEN_TCL, ORELSE_TCL, >>, >-, >|, >>>, >>-,
    >~, >>~, >>~-, by, suffices_by, via, using, |->, |>, |>>, ?>, $,
    --> and friends -- so that downstream tools see the same
    associativity HOL programmers expect.  The parser updates the
    scope as it encounters infix / infixr / nonfix declarations,
    threading both inside and across local / structure / let blocks.

    parseSML : string -> (int -> string) -> errSink -> scope -> result

    where errSink is shorthand (in this Overview only, not a SML
    type) for the curried error-reporter type
      (DString.dstring * HOLSourceAST.events) -> int * int -> string
                                                              -> unit

    Inputs:
      - file : the filename used for diagnostics.
      - read : 1024-byte (or so) chunked source reader; called as
        needed when the buffer runs short.  An empty return signals
        EOF.
      - errSink : as above.  The outer (body, events) capture is
        normally pre-applied via simpleParseError or
        filelineParseError; the inner two arguments are the offending
        source span and a human-readable description.
      - scope : the starting infix table (typically initialScope).

    Result fields:
      - getScope () : the current scope after everything parsed so
        far -- useful for an interactive session that needs to know
        which infixes are visible at the prompt.
      - parseDec () : NONE at EOF, otherwise SOME dec.  Pull-style:
        each call drives the parser forward exactly one top-level
        declaration, growing `body` as input is consumed.  The
        returned dec already has all spans resolved against the
        portion of body parsed so far.
      - body : the DString backing the source.  Mutated as parseDec
        is called; queries that need to slice the source must do so
        only after the relevant offset has been seen.
      - events : the line/col event log accumulated during scanning,
        suitable for HOLSourceAST.mkFileline.
      - parseError : the same error sink, bound to (body, events) so
        callers can issue extra diagnostics in the same style.

    Error-tolerant lexing.  The scanner carries on past missing
    closers: finishString and finishComment treat EOF as an unclosed-
    literal error and recover; bracket / paren / brace mismatches
    surface as the right=NONE forms in the AST.  Synthetic separators
    (NONE entries in 'a separated.seps) and the ExpEmpty / ExpBad /
    DecBad / BadTy nodes from HOLSourceAST are produced here.

    Error reporters provided:

      - simpleParseError print : raw byte-offset diagnostics, useful
        when no line map is available.
      - filelineParseError print (body, events) : resolves spans to
        file:line:col and emits compiler-style messages
        ("foo.sml:12:34-12:40: parse error: ...").  This is what a
        Holmake-driven build feeds in.

    The parser is intentionally a single hand-written recursive-
    descent module rather than a parser-generator product.  This is
    what makes local syntax-error recovery straightforward: synthetic
    ExpBad / DecBad nodes and right=NONE closer fields carry the
    disturbance up to the consumer rather than aborting, so the rest
    of the file is still parsed.
   ---------------------------------------------------------------------- *)
