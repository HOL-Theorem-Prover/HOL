(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi 
 *
 * $Log$
 * Revision 1.1  1999/04/29 16:58:03  mn200
 * Initial revision
 *
# Revision 1.1.1.1  1997/01/14  01:38:04  george
#   Version 109.24
#
 * Revision 1.1.1.1  1996/01/31  16:01:42  george
 * Version 109
 * 
 *)

structure LRParser :> LRParser =
 struct
     val print = fn s => TextIO.output(TextIO.stdOut,s)
     val println = fn s => (print s; print "\n")

     open LRTable 
     open Token

     val DEBUG = false
     exception ParseError

      type ('a,'b) elem = (state * ('a * 'b * 'b))
      type ('a,'b) stack = ('a,'b) elem list

      val showState = fn (STATE s) => ("STATE " ^ Int.toString s)

      fun printStack(stack: ('a,'b) elem list, n: int) =
         case stack
           of (state, _) :: rest =>
                 (print("          " ^ Int.toString n ^ ": ");
                  println(showState state);
                  printStack(rest, n+1)
                 )
            | nil => ()

      val parse = fn {table : LRTable.table,
		      lexer : ('b,'c) token Stream.stream,
		      arg : 'arg,
                      saction : int*'c*(LRTable.state * ('b*'c*'c)) list *'arg 
                                -> LRTable.nonterm * ('b * 'c * 'c) 
                                   * (LRTable.state * ('b * 'c * 'c)) list,
		      void : 'b,
		      ec = {is_keyword : term -> bool,
                            preferred_change: (term list * term list) list,
			    errtermvalue: term -> 'b,
                            showTerminal: term -> string,
			    error: string * 'c * 'c -> unit,
                            terms : term list,
                            noShift: term -> bool},
		      lookahead:int} =>
 let fun prAction(stack as (state, _) :: _, 
		  next as (TOKEN (term,_),_), action) =
             (println "Parse: state stack:";
              printStack(stack, 0);
              print("       state="
                         ^ showState state	
                         ^ " next="
                         ^ showTerminal term
                         ^ " action="
                        );
              case action
                of SHIFT s => println ("SHIFT " ^ showState s)
                 | REDUCE i => println ("REDUCE " ^ (Int.toString i))
                 | ERROR => println "ERROR"
		 | ACCEPT => println "ACCEPT";
              action)
        | prAction (_,_,action) = action

      val action = LRTable.action table
      val goto = LRTable.goto table

      fun parseStep(next as (TOKEN (terminal, value as (_,leftPos,_)),lexer) :
			('b,'c) token * ('b,'c) token Stream.stream,
		    stack as (state,_) :: _ : ('b ,'c) stack) =
         case (if DEBUG then prAction(stack, next,action(state, terminal))
               else action(state, terminal))
              of SHIFT s => parseStep(Stream.get lexer, (s,value) :: stack)
               | REDUCE i =>
		    let val (nonterm,value,stack as (state,_) :: _ ) =
					 saction(i,leftPos,stack,arg)
		    in parseStep(next,(goto(state,nonterm),value)::stack)
		    end
               | ERROR => let val (_,leftPos,rightPos) = value
		          in error("syntax error\n",leftPos,rightPos);
			     raise ParseError
			  end
  	       | ACCEPT => let val (_,(topvalue,_,_)) :: _ = stack
			       val (token,restLexer) = next
			   in (topvalue,Stream.cons(token,lexer))
			   end
      val next as (TOKEN (terminal,(_,leftPos,_)),_) = Stream.get lexer
   in parseStep(next,[(initialState table,(void,leftPos,leftPos))])
   end
end;
