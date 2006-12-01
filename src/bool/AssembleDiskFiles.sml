structure AssembleDiskFiles :> AssembleDiskFiles =
struct

  structure DiskFilesLrVals =
    DiskFilesLrValsFun(structure Token = LrParser.Token)

  structure DiskFilesLex =
    DiskFilesLexFun(structure Tokens = DiskFilesLrVals.Tokens)


  structure DiskFileParser =
     Join(structure ParserData = DiskFilesLrVals.ParserData
          structure Lex = DiskFilesLex
          structure LrParser = LrParser)

  fun invoke lexstream = let
    fun print_error (s,i:int,_) =
        TextIO.output(TextIO.stdErr, Int.toString i ^ ": " ^ s ^ "\n")
  in
    #1 (DiskFileParser.parse(15,lexstream,print_error,()))
  end

  fun raw_read_stream strm = let
    val lexer = DiskFileParser.makeLexer (fn _ => TextIO.inputLine strm)
    val _ = DiskFilesLex.UserDeclarations.pos := 1
  in
    invoke lexer
  end

  fun raw_read_file fname = let
    val strm = TextIO.openIn fname
  in
    raw_read_stream strm before TextIO.closeIn strm
  end


end;
