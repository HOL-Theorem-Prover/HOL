(** Copyright (c) 2021-2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure TCS = TerminalColorString
structure TC = TerminalColors
fun boldc c x =
  TCS.bold (TCS.foreground c (TCS.fromString x))
fun printErr m = TextIO.output (TextIO.stdErr, m)

val optionalArgDesc =
  "  [--force]                  overwrite files without interactive confirmation\n\
  \\n\
  \  [--preview]                show formatted output before writing to file\n\
  \\n\
  \  [--preview-only]           show formatted output and skip file overwrite\n\
  \                             (incompatible with --force)\n\
  \\n\
  \  [--read-only]              just parse files, without interactive confirmation,\n\
  \                             and with no overwrite.\n\
  \                             (incompatible with --force)\n\
  \\n\
  \  [--check]                  Verify if files are formatted correctly.\n\
  \                             Exits with returncode 0 on success, and\n\
  \                             otherwise fails with a nonzero returncode and\n\
  \                             reports the unformatted file.\n\
  \                             (incompatible with --force)\n\
  \\n\
  \  [-max-width W]             try to use at most <W> columns in each line\n\
  \                             (default 80)\n\
  \\n\
  \  [-ribbon-frac R]           controls how dense each line should be\n\
  \                             (default 1.0; requires 0 < R <= 1)\n\
  \\n\
  \  [-tab-width T]             parse input tab-stops as having width <T>\n\
  \                             (default 4)\n\
  \\n\
  \  [-indent-width I]          use <I> spaces for indentation in output\n\
  \                             (default 2)\n\
  \\n\
  \  [-mlb-path-var 'K V']      MLton-style path variable\n\
  \\n\
  \  [-engine E]                Select a pretty printing engine.\n\
  \                             Valid options are: prettier, pretty\n\
  \                             (default 'prettier')\n\
  \\n\
  \  [--debug-engine]           Enable debugging output (for devs)\n\
  \\n\
  \  [-allow-top-level-exps B]  Enable/disable top-level expressions.\n\
  \                             Valid options are: true, false\n\
  \                             (default 'true')\n\
  \\n\
  \  [-allow-successor-ml B]    Enable/disable all SuccessorML features.\n\
  \                             Valid options are: true, false\n\
  \                             (default 'false')\n\
  \\n\
  \  [-allow-opt-bar B]         Enable/disable SuccessorML optional bar syntax.\n\
  \                             Valid options are: true, false\n\
  \                             (default 'false')\n\
  \\n\
  \  [-allow-record-pun-exps B] Enable/disable SuccessorML record punning syntax.\n\
  \                             Valid options are: true, false\n\
  \                             (default 'false')\n\
  \\n\
  \  [-allow-or-pats B]         Enable/disable SuccessorML or-pattern syntax.\n\
  \                             Valid options are: true, false\n\
  \                             (default 'false')\n\
  \\n\
  \  [-allow-extended-text-consts B]\n\
  \                             Enable/disable SuccessorML extended text\n\
  \                             constants. Enable this to allow for UTF-8\n\
  \                             characters within strings.\n\
  \                             Valid options are: true, false\n\
  \                             (default 'false')\n\
  \\n\
  \  [-allow-sig-withtype B]    Enable/disable SuccessorML withtype in signatures\n\
  \                             syntax.\n\
  \                             Valid options are: true, false\n\
  \                             (default 'false')\n\
  \\n\
  \  [--help]                   print this message\n"


fun usage () =
  "usage: smlfmt [ARGS] [FILE ...]\n" ^ "Optional arguments:\n"
  ^ optionalArgDesc


val mlbPathVars = CommandLineArgs.parseStrings "mlb-path-var"
val ribbonFrac = CommandLineArgs.parseReal "ribbon-frac" 1.0
val maxWidth = CommandLineArgs.parseInt "max-width" 80
val tabWidth = CommandLineArgs.parseInt "tab-width" 4
val indentWidth = CommandLineArgs.parseInt "indent-width" 2
val engine = CommandLineArgs.parseString "engine" "prettier"
val inputfiles = CommandLineArgs.positional ()

val allowTopExp = CommandLineArgs.parseBool "allow-top-level-exps" true
val allowSuccessorML = CommandLineArgs.parseBool "allow-successor-ml" false
val allowOptBar = CommandLineArgs.parseBool "allow-opt-bar" allowSuccessorML
val allowRecordPun =
  CommandLineArgs.parseBool "allow-record-pun-exps" allowSuccessorML
val allowOrPat = CommandLineArgs.parseBool "allow-or-pats" allowSuccessorML
val allowExtendedText =
  CommandLineArgs.parseBool "allow-extended-text-consts" allowSuccessorML
val allowSigWithtype =
  CommandLineArgs.parseBool "allow-sig-withtype" allowSuccessorML

val doDebug = CommandLineArgs.parseFlag "debug-engine"
val doForce = CommandLineArgs.parseFlag "force"
val doReadOnly = CommandLineArgs.parseFlag "read-only"
val doHelp = CommandLineArgs.parseFlag "help"
val doSafetyCheck = CommandLineArgs.parseFlag "safety-check"
val preview = CommandLineArgs.parseFlag "preview"
val previewOnly = CommandLineArgs.parseFlag "preview-only"
val doCheck = CommandLineArgs.parseFlag "check"
val showPreview = preview orelse previewOnly

fun dbgprintln s =
  if not doDebug then () else print (s ^ "\n")

val allows = AstAllows.make
  { topExp = allowTopExp
  , optBar = allowOptBar
  , recordPun = allowRecordPun
  , orPat = allowOrPat
  , extendedText = allowExtendedText
  , sigWithtype = allowSigWithtype
  }

val _ =
  if
    doHelp
    orelse
    (List.null inputfiles andalso Posix.ProcEnv.isatty Posix.FileSys.stdin)
  then (print (usage ()); OS.Process.exit OS.Process.success)
  else ()

fun warnWithMessage msg =
  TCS.printErr (boldc Palette.yellow (msg ^ "\n"))

fun failWithMessage msg =
  ( TCS.printErr (boldc Palette.red (msg ^ "\n"))
  ; OS.Process.exit OS.Process.failure
  )

val _ =
  if previewOnly andalso doForce then
    failWithMessage "ERROR: --force incompatible with --preview-only"
  else
    ()

val _ =
  if List.null inputfiles andalso (doForce orelse preview orelse previewOnly) then
    failWithMessage
      "ERROR: --force, --preview, and --preview-only incompatible with \
      \standard input"
  else
    ()

val _ =
  if doDebug andalso not previewOnly then
    failWithMessage "ERROR: --debug-engine requires --preview-only"
  else
    ()

val _ =
  if doCheck andalso doForce then
    failWithMessage "ERROR: --check incompatible with --force"
  else
    ()

val _ =
  if doReadOnly andalso doForce then
    failWithMessage "ERROR: --read-only incompatible with --force"
  else
    ()

val prettyPrinter =
  case engine of
    "prettier" => PrettierPrintAst.pretty
  | "pretty" => PrettyPrintAst.pretty
  | other =>
      failWithMessage
        ("ERROR: unknown engine '" ^ other
         ^ "'; valid options are: prettier, pretty\n")


val pathmap = MLtonPathMap.getPathMap ()
val pathmap =
  List.concat (List.map MLtonPathMap.fromString mlbPathVars) @ pathmap

fun handleLexOrParseError exn =
  let
    val e =
      case exn of
        Error.Error e => e
      | other => raise other
    val hist = ExnHistory.history exn
  in
    TCS.print
      (Error.show {highlighter = SOME SyntaxHighlighter.fuzzyHighlight} e);
    if List.null hist then ()
    else print ("\n" ^ String.concat (List.map (fn ln => ln ^ "\n") hist));
    OS.Process.exit OS.Process.failure
  end


fun exnToString exn =
  let
    val header = "UNHANDLED EXCEPTION: " ^ exnMessage exn
    val stackTrace =
      if List.null (ExnHistory.history exn) then
        ""
      else
        "\nSTACK TRACE:\n"
        ^
        List.foldl op^ ""
          (List.map (fn s => "  " ^ s ^ "\n") (ExnHistory.history exn))
  in
    header ^ stackTrace
  end

fun mkSMLPrettied parserOutput =
  case parserOutput of
    Parser.JustComments cs =>
      TabbedTokenDoc.prettyJustComments
        { ribbonFrac = ribbonFrac
        , maxWidth = maxWidth
        , indentWidth = indentWidth
        , tabWidth = tabWidth
        , debug = doDebug
        } cs

  | Parser.Ast ast =>
      prettyPrinter
        { ribbonFrac = ribbonFrac
        , maxWidth = maxWidth
        , tabWidth = tabWidth
        , indent = indentWidth
        , debug = doDebug
        } ast

fun formatOneSML
  { path = fp: FilePath.t
  , allows: AstAllows.t
  , infdict: InfixDict.t option
  , lexerOutput: Token.t Seq.t
  , parserOutput: Parser.parser_output
  } =
  let
    val hfp = FilePath.toHostPath fp
    val prettied = mkSMLPrettied parserOutput
    val result = TCS.toString {colors = false} prettied

    fun check () =
      let
        val result = CheckOutput.check
          { origLexerOutput = lexerOutput
          , origParserOutput = parserOutput
          , origFormattedOutput = result
          , formatter = TCS.toString {colors = false} o mkSMLPrettied
          , allows = allows
          , infdict = infdict
          , tabWidth = tabWidth
          }
      in
        case result of
          CheckOutput.AllGood => print ("check " ^ hfp ^ ": success\n")

        | CheckOutput.NonIdempotentFormatting =>
            warnWithMessage
              ("WARNING: " ^ hfp
               ^
               ": non-idempotent formatting detected. Don't worry! The output \
               \is still correct; this is only an aesthetic issue. To help \
               \improve `smlfmt`, please consider submitting a bug report: \
               \https://github.com/shwestrick/smlfmt/issues")

        | CheckOutput.Error {description} =>
            failWithMessage
              ("ERROR: " ^ hfp ^ ": --safety-check failed: " ^ description
               ^ ". "
               ^
               "Output aborted. This is a bug! Please consider submitting \
               \a bug report: \
               \https://github.com/shwestrick/smlfmt/issues")
      end

    fun writeOut () =
      let
        val outstream = TextIO.openOut hfp
      in
        printErr ("formatting " ^ hfp ^ "\n");
        TextIO.output (outstream, result);
        TextIO.output (outstream, "\n");
        TextIO.closeOut outstream
      end

    fun confirm () =
      if doReadOnly then
        ()
      else
        ( print ("overwrite " ^ hfp ^ " [y/N]? ")
        ; case TextIO.inputLine TextIO.stdIn of
            NONE => printErr ("skipping " ^ hfp ^ "\n")
          | SOME line =>
              if line = "y\n" orelse line = "Y\n" then writeOut ()
              else printErr ("skipping " ^ hfp ^ "\n")
        )

    fun checkIfFormatted () =
      let
        val original = ReadFile.contents hfp
        val isFormatted = String.compare (original, result ^ "\n")
      in
        case isFormatted of
          EQUAL => (TCS.print (boldc Palette.green "PASS "); print (hfp ^ "\n"))
        | _ => failWithMessage ("ERROR: Unformatted file '" ^ hfp ^ "'");
        ()
      end
  in
    if doCheck then checkIfFormatted () else ();

    if not showPreview then
      ()
    else
      ( TCS.print (boldc Palette.lightblue ("---- " ^ hfp ^ " ----"))
      ; print "\n"
      ; TCS.print prettied
      ; print "\n"
      ; TCS.print (boldc Palette.lightblue "--------")
      ; print "\n"
      );

    if not doSafetyCheck then () else check ();

    if previewOnly orelse doCheck then ()
    else if doForce then writeOut ()
    else confirm ()
  end
  handle exn => TCS.printErr (boldc Palette.red (exnToString exn ^ "\n"))


fun doSML filepath =
  let
    val fp = FilePath.fromUnixPath filepath

    val (source, tm) = Util.getTime (fn _ => Source.loadFromFile fp)
    val _ = dbgprintln ("load source: " ^ Time.fmt 3 tm ^ "s")

    val (allTokens, tm) = Util.getTime (fn _ =>
      Lexer.tokens allows source
      handle exn => handleLexOrParseError exn)
    val _ = dbgprintln ("lex: " ^ Time.fmt 3 tm ^ "s")

    val (result, tm) = Util.getTime (fn _ =>
      Parser.parse allows allTokens
      handle exn => handleLexOrParseError exn)
    val _ = dbgprintln ("parse: " ^ Time.fmt 3 tm ^ "s")
  in
    formatOneSML
      { path = fp
      , allows = allows
      , infdict = NONE
      , lexerOutput = allTokens
      , parserOutput = result
      }
  end


fun doMLB filepath =
  let
    val fp = FilePath.fromUnixPath filepath
    val results =
      ParseAllSMLFromMLB.parse
        {skipBasis = true, pathmap = pathmap, allows = allows} fp
      handle exn => handleLexOrParseError exn
  in
    Util.for (0, Seq.length results) (fn i =>
      let
        val {path, allows, infdict, lexerOutput, parserOutput} =
          Seq.nth results i
      in
        formatOneSML
          { path = path
          , allows = allows
          , infdict = SOME infdict
          , lexerOutput = lexerOutput
          , parserOutput = parserOutput
          }
      end)
  end


datatype fileinfo =
  FileError of exn
| Unsupported of string
| MissingExtension
| MLBFile
| SMLFile

fun fileinfo filepath =
  let
    val eo = OS.Path.ext filepath
  in
    case eo of
      NONE => MissingExtension
    | SOME "mlb" => MLBFile
    | SOME e =>
        if List.exists (fn e' => e = e') ["sml", "fun", "sig"] then SMLFile
        else Unsupported e
  end
  handle exn => FileError exn

fun okayFile (_, info) =
  case info of
    SMLFile => true
  | MLBFile => true
  | _ => false

fun skipFile (filepath, info) =
  printErr
    ("skipping file " ^ filepath ^ ": "
     ^
     (case info of
        MissingExtension => "missing extension"
      | Unsupported e => "unsupported file extension: " ^ e
      | FileError exn => exnMessage exn
      | _ => raise Fail "Error! Bug! Please submit an error report...") ^ "\n")

val (filesToDo, filesToSkip) = List.partition okayFile
  (List.map (fn x => (x, fileinfo x)) inputfiles)

fun doFile (fp, info) =
  case info of
    SMLFile => doSML fp
  | MLBFile => doMLB fp
  | _ => raise Fail "Error! Bug! Please submit an error report..."

val _ = List.app skipFile filesToSkip

val _ = List.app doFile filesToDo

val _ =
  if List.null inputfiles then
    let
      val source = Source.loadFromStdin ()
      val allTokens = Lexer.tokens allows source
                      handle exn => handleLexOrParseError exn
      val parserOutput = Parser.parse allows allTokens
                         handle exn => handleLexOrParseError exn
      val prettied = mkSMLPrettied parserOutput
    in
      TCS.print prettied;
      print "\n"
    end
    handle exn =>
      ( TCS.printErr (boldc Palette.red (exnToString exn ^ "\n"))
      ; OS.Process.exit OS.Process.failure
      )
  else
    ()
