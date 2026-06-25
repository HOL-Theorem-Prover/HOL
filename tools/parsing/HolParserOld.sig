signature HolParserOld =
sig

structure Simple: sig

  datatype decl = datatype HolLex.UserDeclarations.decl
  datatype decls = datatype HolLex.UserDeclarations.decls
  datatype antiq = datatype HolLex.UserDeclarations.antiq
  datatype qdecl = datatype HolLex.UserDeclarations.qdecl
  datatype qbody = datatype HolLex.UserDeclarations.qbody

  datatype topdecl
    = TopDecl of decl
    | EOF of int

  datatype type_kind =
      OverloadKind of {by_nametype: bool, inferior: bool}
    | TypeKind of {pp: bool}

  val destAttrs: substring -> (substring * substring list) list
  val destMLThmBinding: substring ->
    {keyword: substring, name: substring, attrs: substring, name_attrs: substring}
  val destNameAttrs: substring -> substring * substring
  val fromSS: int * substring -> int * int
  val killEnvelopingSpace: substring -> substring
  val kindToName: bool -> type_kind -> string
  val parseBeginType: int * string -> (int * int -> string -> unit) ->
    {local_: bool, kind: type_kind, keyword: substring, tyname: substring}
  val parseDefinitionPfx: string ->
    {keyword: substring, name: substring, attrs: substring, name_attrs: substring}
  val parseDefnLabel: string ->
    {name: substring option, attrs: substring, name_attrs: substring, tilde: bool}
  val parseInductivePfx: string -> {isCo: bool, keyword: substring, thmname: substring}
  val parseQuoteEqnPfx: string -> {bind: substring, keyword: substring, name: substring}
  val parseQuotePfx: string -> {keyword: substring, name: substring}
  val parseTheoremPfx: string ->
    {isTriv: bool, keyword: substring, thmname: substring, attrs: substring, name_attrs: substring}

  val mkParser:
    {parseError: int * int -> string -> unit, pos: int, read: int -> string} ->
    unit -> topdecl

end

structure ToSML: sig

  type double_reader =
    {read: int -> string, readAt: int -> int -> (int * substring -> unit) -> unit}
  val mkDoubleReader: (int -> string) -> int -> double_reader

  type args = {
    read: int -> string,
    filename: string,
    parseError: int * int -> string -> unit,
    quietOpen: bool
  }

  val mkPullTranslator: args -> unit -> string

  type strcode = {
    aux: string -> unit,
    regular: int * substring -> unit,
    strcode: int * substring -> unit,
    strstr: int * substring -> unit
  }
  val strstr: (string -> unit) -> int * substring -> unit
  val strcode: (string -> unit) -> int * substring -> unit
  val mkStrcode: (string -> unit) -> strcode

  type doDecl_args = {
    aux: string -> unit,
    cat: substring list -> string,
    countlines: int * substring -> unit,
    doDecls: int -> Simple.decl list -> int -> unit,
    doQuote: Simple.qbody -> unit,
    doQuoteConj: Simple.qbody -> (bool -> int * string -> unit) -> unit,
    doThmAttrs: bool -> substring -> substring -> unit,
    filename: string ref,
    full: string -> substring,
    isTheory: bool ref,
    noSigDocs: bool ref,
    line: (int * int) ref,
    magicBind: string -> unit,
    parseError: int * int -> string -> unit,
    quietOpen: bool,
    readAt: int -> int -> (int * substring -> unit) -> unit,
    regular: int * int -> unit,
    regular': int * substring -> unit,
    ss: substring -> string,
    strstr: int * int -> unit,
    strstr': int * substring -> unit
  }
  val mkDoDecl: doDecl_args -> Simple.decl -> unit

  type ret = {
    doDecl: bool -> int -> Simple.decl -> int,
    feed: unit -> Simple.topdecl,
    finish: unit -> unit,
    regular: int * int -> unit
  }

  val mkPushTranslatorCore': (doDecl_args -> Simple.decl -> unit) ->
    args -> strcode -> ret
  val mkPushTranslatorCore: args -> strcode -> ret

  val mkPushTranslator: args -> strcode -> unit -> bool

end

type reader = {read : unit -> char option, eof : unit -> bool}
type args = {quietOpen: bool}

val inputFile : args -> string -> string
val fromString : args -> string -> string

val fileToReader : args -> string -> reader
val stringToReader : args -> string -> reader
val inputToReader : args -> string -> (int -> string) -> reader
val streamToReader : args -> string -> TextIO.instream -> reader

end

(* ----------------------------------------------------------------------
    Overview
   ----------------------------------------------------------------------

    HolParserOld is the legacy HOL-source-to-SML translator that
    predates the AST-based pipeline (HOLSourceAST / HOLSourceParser /
    HOLSourceExpand / HOLSourcePrinter / HOLSource).  It is kept in the
    tree as a fallback and a reference implementation: where the new
    pipeline parses to a structured AST and rewrites declarations
    explicitly, this module drives a HolLex-generated tokenizer
    directly and emits SML by stitching together substrings of the
    original input with synthesised prefix/suffix code.

    The design difference is important to keep in mind: HolParserOld
    is fundamentally a string-rewriter.  Most output bytes are taken
    verbatim from the source via a "regular" callback; only HOL-
    specific keywords (Theorem, Definition, Datatype, Inductive,
    Theory, Quote, Type/Overload) trigger surrogate code emission.
    There is no separable expansion step -- recognising and emitting
    happen in lockstep inside ToSML.mkDoDecl.

    Two substructures:

    Simple : the lexical front-end.  Re-exports the HolLex
    UserDeclarations datatypes (decl, decls, antiq, qdecl, qbody) and
    wraps them in topdecl = TopDecl of decl | EOF of int.  Provides
    the substring-level prefix recognisers used to peel HOL keywords
    off of declarations:

      - parseTheoremPfx    : Theorem foo[attrs]:
      - parseDefinitionPfx : Definition foo[attrs]:
      - parseInductivePfx  : [Co]Inductive foo:
      - parseQuotePfx      : Quote foo:
      - parseQuoteEqnPfx   : Quote foo = bar:
      - parseDefnLabel     : [name[attrs]:] inside a quote
      - parseBeginType     : Type foo / Overload foo (with kind = pp /
                             inferior / by_nametype variants)

    Plus the attribute-substring utilities (destAttrs, destNameAttrs,
    destMLThmBinding, killEnvelopingSpace, fromSS) that are the
    substring-flavoured cousins of AttributeSyntax.  kindToName
    converts a type_kind into the string name of the runtime helper
    (type_abbrev_pp, overload_on, inferior_overload_on_by_nametype,
    etc.).

    mkParser {parseError, pos, read} returns a unit -> topdecl pull
    function: each call advances the lexer by one declaration and
    yields it.  pos is the initial byte offset (used for diagnostics
    when the input doesn't start at zero).

    ToSML : the translator core.  Takes the same args shape as the new
    pipeline -- {read, filename, parseError, quietOpen} -- and
    produces SML via three driver shapes:

      - mkPullTranslator args : unit -> string
        Pull-mode driver: each call returns the next chunk of
        translated SML, "" at EOF.
      - mkPushTranslator args strcode : unit -> bool
        Push-mode driver, with output funneled through a strcode set
        of callbacks; returns true once EOF has been emitted.
      - mkPushTranslatorCore[']  : exposes the per-declaration handler
        for callers that want to interpose.  The primed variant lets
        the caller substitute their own mkDoDecl.

    Output discipline.  Translated text comes from one of four
    callbacks bundled into a strcode record:

      - regular : verbatim source bytes (the common case, copying
        non-HOL-keyword regions through unchanged).
      - strstr  : a literal string written as an SML string token
        (with quoting applied).
      - strcode : same idea, but for SML strings that themselves
        contain SML code intended to be executed at run time.
      - aux     : free-form auxiliary output used by the HOL-keyword
        handlers to emit synthetic code (Q.store_thm calls, magic
        bind names, etc.).

    The mkStrcode helper builds a default strcode record from a single
    output sink, doing the right encoding for each callback.  strstr
    and strcode are exposed individually for callers that only need
    one of them.

    double_reader.  Some HolLex tokens require re-reading bytes that
    have already been consumed (notably for line-pragma backtracking).
    mkDoubleReader wraps an underlying read callback into a
    {read, readAt} pair where read is forward-only and readAt offset
    count cb hands a windowed substring to the consumer.

    doDecl_args.  mkDoDecl is the per-declaration dispatch that
    actually realises HOL keywords into SML.  Its argument record
    bundles all of the side-effecting callbacks it needs: the strcode
    emission helpers, the recursive doDecls / doQuote / doQuoteConj
    walkers, magicBind for auto-saved induction theorems, mutable
    refs (filename, isTheory, noSigDocs, line) tracking translation
    state, and a few utility helpers (cat, ss, full).  The shape is
    intentionally exposed so callers can supply alternative
    implementations of a single slot (e.g. to capture per-declaration
    SML for testing) without rewriting the whole driver.

    Top-level convenience.  inputFile / fromString translate a file
    or string to an SML string in one shot; fileToReader /
    stringToReader / inputToReader / streamToReader produce a
    char-level reader (different shape from HOLSource.reader -- no
    fileline component, since the old pipeline does not track
    {file, line, col} at the reader boundary).

    When new code is being written, the recommendation is to use
    HOLSource (the AST-based pipeline) rather than HolParserOld.
    This module exists for tools that have not yet migrated and as a
    debugging reference for behaviour comparisons.
   ---------------------------------------------------------------------- *)
