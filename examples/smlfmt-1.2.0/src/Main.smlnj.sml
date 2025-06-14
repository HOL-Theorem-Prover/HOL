(** Copyright (c) 2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure Main:
sig
  (* for a demo *)
  val showSMLFilePreview: string -> unit
end =
struct

  structure TCS = TerminalColorString
  structure TC = TerminalColors
  fun boldc c x =
    TCS.bold (TCS.foreground c (TCS.fromString x))

  fun warnWithMessage msg =
    TCS.printErr (boldc Palette.yellow (msg ^ "\n"))

  fun failWithMessage msg =
    TCS.printErr (boldc Palette.red (msg ^ "\n"))

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

      print "\n"
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


  val prettyPrinter = PrettierPrintAst.pretty
  val ribbonFrac = 1.0
  val maxWidth = 80
  val indentWidth = 2
  val tabWidth = 4
  val allows = AstAllows.make
    { topExp = true
    , optBar = false
    , recordPun = false
    , orPat = false
    , extendedText = false
    }


  fun mkSMLPrettied parserOutput =
    case parserOutput of
      Parser.JustComments cs =>
        TabbedTokenDoc.prettyJustComments
          { ribbonFrac = ribbonFrac
          , maxWidth = maxWidth
          , indentWidth = indentWidth
          , tabWidth = tabWidth
          , debug = false
          } cs

    | Parser.Ast ast =>
        prettyPrinter
          { ribbonFrac = ribbonFrac
          , maxWidth = maxWidth
          , tabWidth = tabWidth
          , indent = indentWidth
          , debug = false
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

      fun check () =
        let
          val formatted = TCS.toString {colors = false} prettied

          val result = CheckOutput.check
            { origLexerOutput = lexerOutput
            , origParserOutput = parserOutput
            , origFormattedOutput = formatted
            , formatter = TCS.toString {colors = false} o mkSMLPrettied
            , allows = allows
            , infdict = infdict
            , tabWidth = tabWidth
            }
        in
          case result of
            CheckOutput.AllGood => ()

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
                ("ERROR: " ^ hfp ^ ": --safety-check failed: " ^ description ^ ". "
                 ^
                 "Output aborted. This is a bug! Please consider submitting \
                 \a bug report: \
                 \https://github.com/shwestrick/smlfmt/issues")
        end
    in
      TCS.print (boldc Palette.lightblue ("---- " ^ hfp ^ " ----"));
      print "\n";
      TCS.print prettied;
      print "\n";
      TCS.print (boldc Palette.lightblue "--------");
      print "\n";

      check ()
    end
    handle exn => TCS.printErr (boldc Palette.red (exnToString exn ^ "\n"))


  fun showSMLFilePreview filepath =
    let
      val fp = FilePath.fromUnixPath filepath
      val source = Source.loadFromFile fp
      val allTokens = Lexer.tokens allows source
      val result = Parser.parse allows allTokens
    in
      formatOneSML
        { path = fp
        , allows = allows
        , infdict = NONE
        , lexerOutput = allTokens
        , parserOutput = result
        }
    end
    handle exn => handleLexOrParseError exn

end
