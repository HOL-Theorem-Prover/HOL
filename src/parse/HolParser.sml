(* Derived from the 
 *   ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi 
 *)

structure HolParser =
struct

    exception ParseError = LRParser.ParseError

(*    type arg = HolParserData.arg
    type pos = HolParserData.pos
    type lexarg = HolUserDeclarations.arg
    type result = HolParserData.result
    type svalue = HolParserData.svalue
*)
    val makeLexer = fn s => fn arg =>
		 Stream.streamify (HolLex.makeLexer s arg)

    fun parse (lookahead,lexer,error,arg) =
      let val (a,b) = 
           LRParser.parse 
            {table = HolParserData.table,
	     lexer = lexer,
             lookahead=lookahead,
             saction = HolActions.actions,
             arg=arg,
             void = HolActions.void,
             ec = {is_keyword = HolEC.is_keyword,
                   noShift = HolEC.noShift,
                   preferred_change = HolEC.preferred_change,
                   errtermvalue = HolEC.errtermvalue,
                   error=error,
                   showTerminal = HolEC.showTerminal,
                   terms = HolEC.terms}}
      in
	(HolActions.extract a,b)
      end; 

    val sameToken = Token.sameToken
end;
