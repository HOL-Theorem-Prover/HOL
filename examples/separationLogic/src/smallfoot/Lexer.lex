
{ (* header *)
  
(*
loadPath := 
            ("/auto/homes/tt291/Downloads/smallfoot/mosml/") :: 
            !loadPath;

	load "Lexing";
	load "parser";
*)

open Lexing
open Parser

(* association list of keywords *)
val keyword_al = [
  ("dispose",DISPOSE),
  ("else",ELSE),
  ("emp",EMPTY),
  ("if",IF),
  ("local",LOCAL),
  ("new",NEW),
  ("resource",RESOURCE),
  ("then",Parser.THEN),
  ("when",WHEN),
  ("while",WHILE),
  ("with", WITH),
  ("dlseg",DLSEG),
  ("list" ,LIST),
  ("lseg",LISTSEG),
  ("data_list" ,DATA_LIST),
  ("data_lseg",DATA_LISTSEG),
  ("tree" ,TREE),
  ("xlseg",XLSEG),
  ("true" ,TT),
  ("false",FF),
  ("NULL",NAT(0))]


fun list_to_dict l = let
	fun insert_binmap ((key,value),dict) = 
		Binarymap.insert (dict,key,value);
  	val emptyDict = Binarymap.mkDict String.compare;
	in 
		foldl insert_binmap emptyDict l
	end;

val keyword_dict = list_to_dict keyword_al;

fun handle_ident ident = 
	let
		val value = Binarymap.peek (keyword_dict, ident);
	in
		if (isSome value) then valOf(value) else IDENT(ident)
	end;

exception lexer_exp;


}


(* regular expressions *)

let newline = (`\010` | `\013` | "\013\010")
let blank = [` ` `\009` `\012`]
let letter = [`A`-`Z` `_` `a`-`z`]
let digit = [`0`-`9`]
let alphanum = digit | letter
let ident = letter alphanum* 
let qident = ("_" | "#") ident
let num = digit+
let hol_quote = "``" [^ `\``]* "``"



(* entry points *)

rule token = parse
    newline { token lexbuf }
  | blank+ { token lexbuf }
  | "/*" { comment lexbuf }
  | "|->" { POINTSTO }
  | ","  { COMMA }
  | "{"  { LBRACE }
  | "["  { LBRACKET }
  | "("  { LPAREN }
  | "->" { MINUSGREATER }
  | "}"  { RBRACE }
  | "]"  { RBRACKET }
  | ")"  { RPAREN }
  | ";"  { SEMI }
  | "&&" { AMPERAMPER }
  | "||" { BARBAR }
  | ":"  { COLON } 
  | "="  { EQUAL }
  | "==" { EQUALEQUAL }
  | "!=" { BANGEQUAL }
  | "<" | "<=" | ">" | ">=" { INFIXOP1(Lexing.getLexeme lexbuf) }
  | "+" | "-"               { INFIXOP2(Lexing.getLexeme lexbuf) }
  | "/" | "%"               { INFIXOP3(Lexing.getLexeme lexbuf) }
  | "*"     { STAR }
  | "^"     { XOR }
  | hol_quote { let val s = Lexing.getLexeme lexbuf in
		  HOL_TERM(substring (s, 2, (String.size s)-4))
                end }
  | num { NAT(valOf(Int.fromString(Lexing.getLexeme lexbuf))) }
  | ident { handle_ident (Lexing.getLexeme lexbuf)}
  | qident { QIDENT(Lexing.getLexeme lexbuf) }
  | eof { EOF }
  | _ { raise lexer_exp }

and comment = parse
    "/*" { comment lexbuf }
  | "*/" { token lexbuf }
  | eof { raise lexer_exp }
  | newline { comment lexbuf }
  | _ { comment lexbuf };

{ (* trailer *)
}
