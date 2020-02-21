structure HOLsexp_parser :> HOLsexp_parser =
struct

  open HOLsexp_dtype

  structure HOLsexpLrVals =
    HOLsexpLrValsFun(structure Token = LrParser.Token)

  structure HOLsexpLex =
    HOLsexpLexFun(structure Tokens = HOLsexpLrVals.Tokens)


  structure HOLsexpParser =
     JoinWithArg(structure ParserData = HOLsexpLrVals.ParserData
                 structure Lex = HOLsexpLex
                 structure LrParser = LrParser)

  fun invoke lexstream = let
    fun print_error (s,i:int,_) =
        TextIO.output(TextIO.stdErr, Int.toString i ^ ": " ^ s ^ "\n")
  in
    #1 (HOLsexpParser.parse(15,lexstream,print_error,ref []))
  end

  fun raw_read_stream strm = let
    val lexer = HOLsexpParser.makeLexer
                  (fn _ => Portable.input_line strm)
                  (ref [] : string list ref)
    val _ = HOLsexpLex.UserDeclarations.pos := 1
  in
    invoke lexer
  end

  fun raw_read_file fname = let
    val strm = TextIO.openIn fname
  in
    raw_read_stream strm before TextIO.closeIn strm
  end

  fun scan creader cs =
      let
        val csref = ref cs
        val lexer = HOLsexpParser.makeLexer
                      (fn _ => case creader (!csref) of
                                   NONE => ""
                                 | SOME (c,cs') => (csref := cs'; str c))
                      (ref [] : string list ref)
        val _ = HOLsexpLex.UserDeclarations.pos := 1
      in
        case Exn.capture invoke lexer of
            Exn.Res r => SOME(r, !csref)
          | Exn.Exn e => NONE
      end

end (* struct *)
