(* Grammar.sml *)

(* recursive descent parser for lexer definitions (.lex files) *)

structure Grammar: GRAMMAR =
struct

open Syntax Token Gram_aux

exception ParserError of string

datatype exprs
  = Concat
  | Or
  | Star of regular_expression
  | Maybe of regular_expression
  | Plus of regular_expression
  | Exp of regular_expression

fun infx (Exp exp::lst,e1::stack,Concat::ops) =
      infx (lst,Sequence(e1,exp)::stack,ops)
  | infx (Exp exp::lst,e1::stack,Or::ops)     = 
      infx (lst,Alternative(e1,exp)::stack,ops)
  | infx (Exp exp::lst,stack,[])              = infx (lst,exp::stack,[])
  | infx (Concat::lst,stack,ops)              = infx (lst,stack,Concat::ops)  
  | infx (Or::lst,stack,ops)                  = infx (lst,stack,Or::ops)  
  | infx ([],e::stack,ops)                    = e

fun foldit lst = infx (rev lst,[],[])

fun lexer_definition(f: unit -> token) =
    let fun header (Taction l) = (l,f ())
          | header _ = raise ParserError "Missing header declaration."
        and footer (Taction l) = (l,f ())
          | footer _ = raise ParserError "Missing footer declaration."
        and lexarg (Taction l) = (l,f ())
          | lexarg _ = raise ParserError "Missing lex argument declaration."
        and letdef_list (Tlet) = 
	      let val (bind,next) = letdef Tlet
		  val (lst,next2) = letdef_list next
	      in  (bind::lst,next2)
	      end
          | letdef_list (Trule) = ([],f ())
          | letdef_list _ = raise ParserError "Unexpected token; missing rule declarations?"
        and letdef (Tlet) =
            let val id = (f ())
                val eq = (f ())
                val (rexp,next) = regexp (f ())
            in  case (id,eq)
                  of (Tident x,Tequal) => ((x,rexp),next)
                   | _ => raise ParserError "Invalid let definition."
            end
        and definitions tok =
            let val (def,next) = definition tok
            in  case next 
                  of Tand => let val (defs,next2) = definitions (f ())
                             in  (def::defs,next2)
                             end
                   | Tend => ([def],next)
                   | _ => raise ParserError "Invalid definition separator."
            end
        and definition (Tident id) = 
	      let val eq = (f ())
		  val (ent,next) = entry (f ())
	      in  case eq
		    of Tequal => ((id,ent),next)
		     | _ => raise ParserError "Missing = in rule definition."
	      end
          | definition _ = raise ParserError "Missing name in rule definition."
        and entry Tparse =
	      let val (c,n1) = caseloc (f ())
		  val (rst,n2) = rest_of_entry n1
	      in  (c::rst,n2)
	      end            
          | entry _ = raise ParserError "Missing parse in rule definition."
        and rest_of_entry Tor = 
	      let val (c,n1) = caseloc (f ())
		  val (lst,n2) = rest_of_entry n1
	      in  (c::lst,n2) 
	      end
          | rest_of_entry tok = ([],tok)
        and caseloc tok =
            let val (rexp,next) = regexp tok
            in  case next
                  of (Taction l) => ((rexp,l),(f ()))
                   | _ => raise ParserError "Missing action in rule definition."
            end
        and regexp tok = explist ([],tok)
        and explist (lst,tok)=
            let val p = atomicexp tok
                val (a,next) = collectPostfix p
            in  case next
                  of (Tand | Trule | Tlet | Trparen) => (foldit (Exp a::lst),next)
                   | (Taction l) =>                     (foldit (Exp a::lst),next)
                   | Tor =>    explist ((Or :: Exp a :: lst), f ())
                   | (Tparse | Tequal | Tend | Tdash | Tcaret | Trbracket) => 
                     raise ParserError "Illegal end of regular expression."
                   | tok => explist ((Concat :: Exp a :: lst), tok)
            end
        and collectPostfix (a,Tstar)  = collectPostfix (Repetition a, f ())
          | collectPostfix (a,Tmaybe) =
	      collectPostfix (Alternative (a,Epsilon), f ())
          | collectPostfix (a,Tplus)  =
	      collectPostfix (Sequence (a,Repetition a), f ())
          | collectPostfix p          = p
        and atomicexp (Tunderscore) = (Characters all_chars,f ())
          | atomicexp (Teof) = (Characters [#"\000"],f ())
          | atomicexp (Tchar x) = (Characters [x],f ())
          | atomicexp (Tstring s) = (regexp_for_string s,f ())
          | atomicexp (Tident id) = (Name id,f ())
          | atomicexp (Tlbracket) = 
	      let val (c,next) = char_class' (f ())
	      in  case next
		    of Trbracket => (Characters c,f ())
		     | _ => raise ParserError "Unmatched brackets."
	      end
          | atomicexp (Tlparen) = 
	      let val (rexp,next) = regexp (f ())
	      in  case next
		    of Trparen => (rexp,f ())
		     | _ => raise ParserError "Unmatched parentheses."
	      end
          | atomicexp _ = raise ParserError "Illegal expression."
        and char_class' (Tcaret) =
	      let val (c,n) = char_class1 (f ())
	      in  (subtract(all_chars,c), n)
	      end
          | char_class' tok = char_class1 tok
        and char_class1 (Tchar c) =
	      (case (f ())
		 of Tdash => 
		    (case (f ())
		       of (Tchar c') => 
			  let val (cls,next) = char_class1 (f ())
			  in  (char_class c c' @ cls, next)
			  end)
		 | tok => let val (cls,next) = char_class1 tok
			  in  (c::cls,next)
			  end)
          | char_class1 tok = ([],tok)
        val (hd,n1) = header (f ())
        val (ft,n2) = footer n1
        val (la,n3) = lexarg n2
        val (deflst,n4) = letdef_list n3
        val (defs,_) = definitions n4
    in  Lexdef {header=hd,footer=ft,lexarg=la,lets=deflst,rules=defs}
    end


end (* structure *)
