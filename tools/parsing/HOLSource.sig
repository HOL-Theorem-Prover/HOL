signature HOLSource =
sig

type fileline = {file: string, line: int, col: int}

structure ToSML: sig

  type args = {
    read: int -> string,
    filename: string,
    parseError: DString.dstring * HOLSourceAST.events -> int * int -> string -> unit,
    quietOpen: bool
  }

  type printer = {str: string -> unit, startSpan: int * int -> unit, stopSpan: unit -> unit}

  val mkPushTranslator: args -> printer -> {fileline: int -> fileline, push: unit -> bool}
  val mkPullTranslator: args -> {fileline: unit -> fileline, read: unit -> string}

end

type reader = {read: unit -> char option, fileline: unit -> fileline, eof: unit -> bool}
type args = {quietOpen: bool, print: string -> unit}

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

    HOLSource is the top-level driver that ties the parse/expand/print
    stages of the HOL source preprocessor together into a single
    HOL-flavoured-SML to plain-SML translator.  The pipeline composed
    here is

      HOLSourceParser  -- parseSML, declaration-by-declaration parser
              |
              v
      HOLSourceAST     -- AST + offset->{file,line,col} reverse map
              |
              v
      HOLSourceExpand  -- expand `Theorem`, `Definition`, etc. into
                          pure SML
              |
              v
      HOLSourcePrinter -- write the expanded decls back as SML, with
                          line-directive annotations

    The fileline type {file, line, col} is the diagnostic-position
    currency shared with HOLSourceAST and surfaced from every reader
    constructor here.

    The ToSML substructure exposes two driver shapes around the same
    pipeline:

      - mkPushTranslator args printer
        Returns {fileline, push}.  Each call to push parses one top-
        level declaration, expands it, and feeds the result to the
        supplied printer (str/startSpan/stopSpan); push returns true
        when EOF has been reached and the trailing "\n" has been
        emitted.  The fileline function maps a character offset (as
        carried in spans by startSpan) back to its source location.
      - mkPullTranslator args
        Returns {fileline, read}.  Wraps mkPushTranslator with an
        internal queue and span tracking so that each call to read
        returns the next chunk of expanded SML as a string.  fileline
        () reports the source location of the most recently produced
        chunk.  This is the form most callers want.

    args = {read, filename, parseError, quietOpen}: read is the input
    callback (`int -> string`, the int being a hint at the desired
    chunk size); filename is used in diagnostics and line directives;
    parseError reports parse failures with span and message;
    quietOpen suppresses `open` warnings during expansion.

    The top-level HOLSource exposes higher-level wrappers built on
    mkPullTranslator:

      - inputFile / fromString : args -> ... -> string
        Translate an entire file or in-memory string and return the
        full expanded SML as a single string.
      - fileToReader / stringToReader / inputToReader / streamToReader
          : args -> ... -> reader
        Produce a character-level reader = {read, fileline, eof} that
        yields the expansion one char at a time.  inputToReader takes
        a custom `int -> string` chunked source; streamToReader takes
        a TextIO.instream.

    The reader-style API is what consumers like Holmake and the
    quotation filter plug into; the inputFile / fromString shortcuts
    are for one-shot use (testing, command-line tools).
   ---------------------------------------------------------------------- *)
