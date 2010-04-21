structure AssembleHolindexParser :> AssembleHolindexParser =
struct

  structure HolindexLrVals =
    HolindexLrValsFun(structure Token = LrParser.Token)

  structure HolindexLex =
    HolindexLexFun(structure Tokens = HolindexLrVals.Tokens)


  structure DiskFileParser =
     Join(structure ParserData = HolindexLrVals.ParserData
          structure Lex = HolindexLex
          structure LrParser = LrParser)


  fun print_parse_error s =
     print ("Error: "^s^"\n");

  fun invoke lexstream = let
    open PPBackEnd;
    val error_count = ref 0;
    fun print_error (s,(j:int,i:int),_) =
        ((if (!error_count > 0) then () else print "\n");
        (error_count := !error_count + 1);
        print_parse_error (" "^
            " line "^(Int.toString (i+1)) ^ ": " ^ s);
       (if (!error_count > 15) then Feedback.fail() else ()));

    val r = (#1 (DiskFileParser.parse(15,lexstream,print_error,())))
        handle HolindexLex.UserDeclarations.LexicalError (tok, j, i) =>
           let
              val s = "lex error - ill formed token \""^tok^"\"";
              val _ = print_error (s, (j, i), (j,i));
           in
              Feedback.fail()
           end;
  in
    (if (!error_count > 0) then Feedback.fail() else r)
  end

  fun raw_read_stream strm = let
    val lexer = DiskFileParser.makeLexer (fn _ => Portable.input_line strm)
  in
    invoke lexer
  end

  fun raw_read_file fname = let
    val strm = TextIO.openIn fname
  in
    raw_read_stream strm before TextIO.closeIn strm
  end

  val parse_hdf_file = raw_read_file;

end;
