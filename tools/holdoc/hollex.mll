(* hollex.mll  --  (approximate) HOL lexer *)
(* Keith Wansbrough 2001 *)

{
exception Eof         (* raised by relheader if no body found *)
exception BadChar     (* raised by reltoken if unrecognised char scanned *)
exception Finished    (* raised by reltoken when end of body reached *)

let comments = ref []

type token =
    Ident of string
  | Indent of int
  | White of string
  | Comment of string
  | Sep of string

let indent_width s = 
  let l = String.length s in
  let rec go n w =
    if n>=l then w else
    go (n+1) 
      (match String.get s n with
        '\n'   -> 0
      | ' '    -> w+1
      | '\t'   -> w-(w mod 8)+8  (* account for tabs *)
      | '\r'   -> 0
      | '\012' -> 0)
            in
  go 0 0

} 

(* some classes *)
let white    = [' ' '\r' '\t' '\012']
let newline  = '\n'

let backtick = '`'

(* these patterns delimit the scanned "body" area *)
let startpat = "Net_Hol_reln" (white | newline)* backtick
let stoppat  = newline backtick

(* the character classes of HOL *)
let idchar = ['A'-'Z' 'a'-'z' '0'-'9' '_' '\'']
let nonagg = ['~' '(' ')' '[' ']' '{' '}' '.' ',']
let dollar = '$'
let punctchar = ['!' '"' '#' '%' '&' '*' '+' '-' '/' ':' ';' '<' '=' '>' '?' '@' '\\' '^' '|']
  (* everything else except '`' ; I'm not sure about '\\' and '"' but hey... *)
let idorpunctchar = idchar | punctchar

let startcom = "(*"
let incomm   = [^ '(' '*'] | '(' [^ '*'] | '*' [^ ')']
let stopcom  = "*)"


(* now some rules *)

rule

(* relheader returns unit when it reaches the beginning of the body *)
  relheader = parse
    startpat { () }
  | _        { relheader lexbuf }
  | eof      { raise Eof }

and

(* reltoken returns the next token, or raises Finished|BadChar *)

  reltoken = parse
    dollar? idchar+        { Ident (Lexing.lexeme lexbuf) }
  | dollar? punctchar+     { Ident (Lexing.lexeme lexbuf) }
  | newline white*         { Indent (indent_width (Lexing.lexeme lexbuf)) }
  | white+                 { White (Lexing.lexeme lexbuf) }
  | startcom               { comments := [];
                             comment lexbuf;
                             Comment (String.concat "" !comments)}
  | nonagg                 { Sep (Lexing.lexeme lexbuf) }
  | stoppat                { raise Finished }
  | _                      { raise BadChar }

and
  comment = parse
    incomm*        { comments := (Lexing.lexeme lexbuf) :: !comments;
                     comment lexbuf }
  | startcom       { comment lexbuf }
  | stopcom        { }


{
(* trailer *)
} 
