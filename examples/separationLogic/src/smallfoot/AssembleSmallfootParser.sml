structure AssembleSmallfootParser :> AssembleSmallfootParser =
struct

  structure SmallfootLrVals =
    SmallfootLrValsFun(structure Token = LrParser.Token)

  structure SmallfootLex =
    SmallfootLexFun(structure Tokens = SmallfootLrVals.Tokens)


  structure DiskFileParser =
     Join(structure ParserData = SmallfootLrVals.ParserData
          structure Lex = SmallfootLex
          structure LrParser = LrParser)

  fun invoke lexstream = let
    fun print_error (s,(j:int,i:int),_) =
        TextIO.output(TextIO.stdErr, Int.toString i ^ ": " ^ s ^ "\n")
  in
    #1 (DiskFileParser.parse(15,lexstream,print_error,()))
  end

  fun raw_read_stream strm = let
    val lexer = DiskFileParser.makeLexer (fn _ => TextIO.inputLine strm)
  in
    invoke lexer
  end

  fun raw_read_file fname = let
    val strm = TextIO.openIn fname
  in
    raw_read_stream strm before TextIO.closeIn strm
  end


end;
