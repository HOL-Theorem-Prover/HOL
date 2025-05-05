fun doSML filepath =
  let
    val fp = FilePath.fromUnixPath filepath

    (* Setting features for the lexer and parser *)
    val ctx = ParserContext.make
      { topExp = true
      , optBar = false
      , recordPun = false
      , orPat = false
      , extendedText = false
      , sigWithtype = false }

    (* Some basic error handling *)
    fun handleError exn =
    let
      val e = case exn of Error.Error e => e | other => raise other
    in
      TextIO.output (TextIO.stdErr, Error.toString e);
      OS.Process.exit OS.Process.failure
    end

    (* Read, lex, and parse *)

    val (source, tm) = Util.getTime (fn _ => Source.loadFromFile fp)
    val _ = print ("load source: " ^ Time.fmt 3 tm ^ "s\n")

    val (allTokens, tm) = Util.getTime (fn _ =>
      Lexer.tokens ctx source
      handle exn => handleError exn)
    val _ = print ("lex: " ^ Time.fmt 3 tm ^ "s\n")

    val (result, tm) = Util.getTime (fn _ =>
      Parser.parse ctx allTokens
      handle exn => handleError exn)
    val _ = print ("parse: " ^ Time.fmt 3 tm ^ "s\n")
  in () end
