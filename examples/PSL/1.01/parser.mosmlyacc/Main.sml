
(*****************************************************************************)
(* Main.sml : mosmllex/ mosmlyacc parser for PSL/Sugar                       *)
(*****************************************************************************)

(******************************************************************************
* Parse a string with a mosmlyacc parser entry point; doesn't report errors
******************************************************************************)
fun parseString parser s =
    let val expr = parser Lexer.Token (Lexing.createLexerString s)
    in
	Parsing.clearParser();
	expr
    end
    handle exn => (Parsing.clearParser(); raise exn);

(******************************************************************************
* Parse PSL constructs from a string (no error reporting)
******************************************************************************)

val parseBexp     = parseString Parser.MainBoolean
and parseSere     = parseString Parser.MainSERE
and parseFl       = parseString Parser.MainFL
and parseObe      = parseString Parser.MainOBE
and parseState    = parseString Parser.MainState
and parsePath     = parseString Parser.MainPath
and parsePathSere = parseString Parser.MainPathSERE
and parsePathFl   = parseString Parser.MainPathFL;

(******************************************************************************
* Write a string to a temporary file; save last file name in tmp_name
******************************************************************************)
val tmp_name = ref "undefined";

fun stringToFile s =
 let open TextIO;
     val tmp          = FileSys.tmpName()
     val tmpname      = tmp^".pslparse";
     val outstr       = TextIO.openOut tmpname
     fun out s        = output(outstr,s)
 in
 (out s;
  flushOut outstr;
  closeOut outstr;
  tmp_name := tmp;
  tmpname)
 end;

(******************************************************************************
* Auxiliary function to parse from a file without reporting error locations
******************************************************************************)
fun parseFileNoReport parser file stream lexbuf =
    let val expr = parser Lexer.Token lexbuf
    in
	Parsing.clearParser();
	expr
    end
    handle exn => (Parsing.clearParser(); raise exn);

(******************************************************************************
* Auxiliary funtion to parse from a file and report error locations
******************************************************************************)
fun parseFileReport parser file stream lexbuf =
    let val expr =
	    parser Lexer.Token lexbuf
	    handle
	       Parsing.ParseError f =>
		   let val pos1 = Lexing.getLexemeStart lexbuf
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

(******************************************************************************
* Create lexer from instream
******************************************************************************)
fun createLexerStream (is : BasicIO.instream) =
  Lexing.createLexer (fn buff => fn n => Nonstdio.buff_input is buff 0 n)

(******************************************************************************
* Parse from a file and report error locations, given a parser entry point
******************************************************************************)
fun parse parser file =
    let val is     = Nonstdio.open_in_bin file
        val lexbuf = createLexerStream is
	val expr   = parseFileReport parser file is lexbuf
	             handle exn => (BasicIO.close_in is; raise exn)
    in
        BasicIO.close_in is;
	expr
    end

(******************************************************************************
* Parse PSL constructs from a file and report error locations
******************************************************************************)
val parseFileBexp     = parse Parser.MainBoolean
and parseFileSere     = parse Parser.MainSERE
and parseFileFl       = parse Parser.MainFL
and parseFileObe      = parse Parser.MainOBE
and parseFileState    = parse Parser.MainState
and parseFilePath     = parse Parser.MainPath
and parseFilePathSere = parse Parser.MainPathSERE
and parseFilePathFl   = parse Parser.MainPathFL;
