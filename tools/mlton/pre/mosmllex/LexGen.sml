(* The lexer generator. Command-line parsing and expansion of abbreviations *)

structure LexGen : sig
		     val main : string * string list -> OS.Process.status
		   end =
struct

local 
  open LexBuffer Syntax

  fun sayErr s = TextIO.output(TextIO.stdErr,s)
  fun flushErr () = TextIO.flushOut TextIO.stdErr
in

(* Lexer of stream *)

fun expandRe defining name ls =
    let fun expRe (Name s) =
	    (Fnlib.lookup s ls
	     handle Subscript => 
		 (sayErr(if defining andalso s = name then 
			     "Illegal recursive let-definition: "
			 else "Undefined let-name: ");
		  sayErr s;
		  sayErr("\n\n");
		  flushErr();
		  OS.Process.terminate(OS.Process.failure)))
	  | expRe (Sequence(r1,r2))     = Sequence (expRe r1, expRe r2)
	  | expRe (Alternative (r1,r2)) = Alternative (expRe r1, expRe r2)
	  | expRe (Repetition r)        = Repetition (expRe r)
	  | expRe x                     = x
    in expRe end

fun expandLet ((name, re),ls) = 
    (name, expandRe true name ls re) :: ls 

fun expandRule ls (name,rl) =
    (name, List.map (fn (r, loc) => (expandRe false name ls r, loc)) rl)

exception Exit

(* main function for use as argument to SMLofNJ.exportFn *)
fun main (name: string,args: string list) : OS.Process.status =
    let val () =
	  if length args <> 1 then
	    (sayErr( "Usage: mosmllex <input file>\n");
	     flushErr();
	     OS.Process.terminate(OS.Process.failure))
	  else ()
	val source_name = hd args
	val dest_name =
	    let val {base,ext} = OS.Path.splitBaseExt source_name
	     in case ext
		  of SOME "lex" => OS.Path.joinBaseExt{base=base,ext=SOME "sml"}
		   | _ => 
		      OS.Path.joinBaseExt{base=source_name,ext=SOME "sml"}
	    end
	val is = TextIO.openIn source_name
	val os = TextIO.openOut dest_name
	val lexbuf = LexBuffer.createLexbuf (TextIO.inputAll is)
	val Lexdef{header,footer,lexarg,lets,rules} =
	      Grammar.lexer_definition(Scanner.makeLex lexbuf)
	      handle LexError.Lexical_error s =>
			(sayErr("Lexical error around char ");
			 sayErr(Int.toString (getLexemeStart lexbuf));
			 sayErr(": ");
			 sayErr(s);
			 sayErr(".\n"); 
			 flushErr();
			raise Exit)
                   | Grammar.ParserError s =>
			(sayErr("Parse error around char ");
			 sayErr(Int.toString (getLexemeStart lexbuf));
			 sayErr(": ");
			 sayErr(s);
			 sayErr("\n"); 
			 flushErr();
			 raise Exit)
	val nlets = foldl expandLet [] lets
	val nrules = List.map (expandRule nlets) rules
	val dfa as (init, states, acts) = DFA.make_dfa nrules 
    in  Output.output_lexdef(os,header,footer,lexarg,dfa);
        TextIO.closeIn is;
        TextIO.closeOut os;
        OS.Process.success
    end
    handle Exit => OS.Process.failure

end (* local *)
end (* structure LexGen *)
