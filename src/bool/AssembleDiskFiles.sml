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

  fun invoke tabs lexstream = let
    fun print_error (s,i:int,_) =
        TextIO.output(TextIO.stdErr, Int.toString i ^ ": " ^ s ^ "\n")
  in
    #1 (DiskFileParser.parse(15,lexstream,print_error,tabs))
  end

  fun read_stream strm = let
    val tables = { idtable = ref [], tytable = ref [], tysize = ref 0,
                   tmtable = ref [], tmsize = ref 0}
    val lexer = DiskFileParser.makeLexer (fn _ => TextIO.inputLine strm)
    val _ = DiskFilesLex.UserDeclarations.pos := 1
  in
    invoke tables lexer
  end

  fun read_file fname = let
    val strm = TextIO.openIn fname
  in
    read_stream strm before TextIO.closeIn strm
  end


end;
