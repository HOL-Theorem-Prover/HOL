
fun parseExprReport file stream lexbuf = let
  val expr = Holmake_parse.MakefileDoc Holmake_tokens.token lexbuf
    handle
    Parsing.ParseError f => let
      val pos1 = Lexing.getLexemeStart lexbuf
      val pos2 = Lexing.getLexemeEnd lexbuf
    in
      Location.errMsg (file, stream, lexbuf)
                      (Location.Loc(pos1, pos2))
                      "Syntax error."
    end
  | Lexer.LexicalError(msg, pos1, pos2) =>
    if pos1 >= 0 andalso pos2 >= 0 then
      Location.errMsg (file, stream, lexbuf)
                      (Location.Loc(pos1, pos2))
                      ("Lexical error: " ^ msg)
    else
      (Location.errPrompt ("Lexical error: " ^ msg ^ "\n\n");
       raise Fail "Lexical error");
in
  Parsing.clearParser();
  expr
end
handle exn => (Parsing.clearParser(); raise exn);




fun parse_from_file inputfile = let
  fun createLexerStream is =
    Lexing.createLexer (fn buff => fn n => Nonstdio.buff_input is buff 0 n)
  val strm = BasicIO.open_in inputfile
  val lbf = createLexerStream strm
in
  parseExprReport inputfile strm lbf
end;


