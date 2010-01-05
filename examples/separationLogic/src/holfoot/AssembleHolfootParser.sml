structure AssembleHolfootParser :> AssembleHolfootParser =
struct

  structure HolfootLrVals =
    HolfootLrValsFun(structure Token = LrParser.Token)

  structure HolfootLex =
    HolfootLexFun(structure Tokens = HolfootLrVals.Tokens)


  structure DiskFileParser =
     Join(structure ParserData = HolfootLrVals.ParserData
          structure Lex = HolfootLex
          structure LrParser = LrParser)

  fun invoke lexstream = let
    fun print_error (s,(j:int,i:int),_) =
        TextIO.output(TextIO.stdErr, Int.toString i ^ ": " ^ s ^ "\n")
  in
    #1 (DiskFileParser.parse(15,lexstream,print_error,()))
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


end;
