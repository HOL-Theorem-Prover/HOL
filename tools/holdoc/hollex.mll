(* hollex.mll  --  (approximate) HOL lexer *)
(* Keith Wansbrough 2001 *)

{
exception Eof         (* raised by holtoken at end of file *)
exception BadChar     (* raised by holtoken if unrecognised char scanned *)
exception BadTerm     (* raised if HOL in TeX is ill-terminated *)
exception BadDir      (* raised if bad directive scanned *)

let comments = ref []

type token =
    Ident of string * bool  (* alphanumeric? *)
  | Indent of int
  | White of string
  | Comment of string
  | Str of string
  | DirBeg  (* delimiters for holdoc parsing directives *)
  | DirEnd  (* ditto *)
  | DirBlk of string * token list (* nonterminal: directive name and body *)
  | Sep of string
  | Backtick
  | DBacktick
  | TeXStartHol   (* [[ *)
  | TeXStartHol0  (* <[ *)
  | TeXEndHol     (* ]] *)
  | TeXEndHol0    (* ]> *)
  | TeXNormal of string
  | HolStartTeX   (* ( * : *)
  | HolEndTeX     (* : * ) *)

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
      | '\012' -> 0
      | _      -> 0)
            in
  go 0 0

let rec render_token t =
  match t with
    Ident(s,_)   -> "I:"^s
  | Indent(n)    -> "\nN:"^(String.make n '>')
  | White(s)     -> "W:"^s
  | Comment(s)   -> "C:(*"^s^"*)-C"
  | Str(s)       -> "s:\""^s^"\""
  | DirBeg       -> "D+"
  | DirEnd       -> "-D"
  | DirBlk(n,ts) -> "D:"^n^": "^(String.concat " " (List.map render_token ts))^" :D"
  | Sep(s)       -> "S:"^s
  | Backtick     -> "T:`"
  | DBacktick    -> "T:``"
  | TeXStartHol  -> "d:[["
  | TeXStartHol0 -> "d:<["
  | TeXEndHol    -> "d:]]"
  | TeXEndHol0   -> "d:]>"
  | TeXNormal(s) -> "X:"^s^":X"
  | HolStartTeX  -> "c:(*:"
  | HolEndTeX    -> ":*):c"

}

(* some classes *)
let white    = [' ' '\r' '\t' '\012']
let newline  = '\n'

let backtick = '`'

(* this pattern marks the beginning of the scanned "body" area *)
let startpat = "Net_Hol_reln" (white | newline)* backtick

(* the character classes of HOL *)
let idchar = ['A'-'Z' 'a'-'z' '0'-'9' '_' '\'']
let nonagg = ['~' '(' ')' '[' ']' '{' '}' '.' ',']
let specnonagg = "()" | "[]"  (* built of nonagg, but aggregating for tokenisation purposes;
                                 this is not HOL but our extension (I think) *)
let dollar = '$'
let punctchar = ['!' '"' '#' '%' '&' '*' '+' '-' '/' ':' ';' '<' '=' '>' '?' '@' '\\' '^' '|']
  (* everything else except '`' ; I'm not sure about '\\' and '"' but hey... *)
let idorpunctchar = idchar | punctchar

let startcom = "(*"
let incomm   = [^ '(' '*'] | '(' [^ '*'] | '*' [^ ')']
let stopcom  = "*)"

let startdir = "(*["
let enddir   = "]*)"

let starttex = "(*:"
let tendhol  = "]]"
let tendhol0 = "]>"

(* tokens for TeX *)

let tnormal    = [^ '[' '<' ':' '%'] |
                 '[' [^ '['] | '<' [^ '['] | ':' [^ '*'] | '%' [^ '('] |
                 ':' '*' [^ ')'] | '%' '(' [^ '*'] |
                 '%' '(' '*' [^ '[']

let tstarthol  = "[["
let tstarthol0 = "<["
let endtex     = ":*)"

let tstartdir  = "%(*["


(* now some rules *)

rule

(* holtoken returns the next token, or raises Finished|BadChar *)

  holtoken = parse
    '"' [^ '"']* '"'       { let s = Lexing.lexeme lexbuf in
                             Str (String.sub s 1 (String.length s - 2)) }
  | dollar? idchar+        { Ident (Lexing.lexeme lexbuf,true) }
  | dollar? (punctchar+
             | specnonagg) { Ident (Lexing.lexeme lexbuf,false) }
  | newline white*         { Indent (indent_width (Lexing.lexeme lexbuf)) }
  | white+                 { White (Lexing.lexeme lexbuf) }
  | startdir               { DirBeg }
  | enddir                 { DirEnd }
  | startcom               { comments := [];
                             comment lexbuf;
                             Comment (String.concat "" (List.rev !comments))}
  | nonagg                 { Sep (Lexing.lexeme lexbuf) }
  | backtick               { Backtick }
  | backtick backtick      { DBacktick }
  | tendhol                { TeXEndHol }
  | tendhol0               { TeXEndHol0 }
  | starttex               { HolStartTeX }
  | eof                    { raise Eof }
  | _                      { raise BadChar }

and
  comment = parse
    incomm*        { comments := (Lexing.lexeme lexbuf) :: !comments;
                     comment lexbuf }
  | startcom       { comments := "(*" :: !comments;
                     comment lexbuf;
                     comments := "*)" :: !comments;
                     comment lexbuf; }
  | stopcom        { }

and
  textoken = parse
    tnormal*       { TeXNormal (Lexing.lexeme lexbuf) }
  | tstarthol      { TeXStartHol }
  | tstarthol0     { TeXStartHol0 }
  | endtex         { HolEndTeX }
  | tstartdir      { DirBeg }
  | startdir       { DirBeg }   (* recognised also, for .mni files that may
                                   be included in either HOL or TeX. *)
  | eof            { raise Eof }

{

(* build a fast stream of tokens from lexed stdin *)
let tokstream p =
  let lexbuf = Lexing.from_channel stdin in
  let lex = ref p in
  let f _ = (* I hope it is valid to assume that *all*
               tokens are requested, in ascending order! *)
    try
      Some (let t = !lex lexbuf in
            match t with
              DirBeg       -> let n =
                                let rec go () = match holtoken lexbuf with
                                                  Ident(s,_) -> s
                                                | White(_)   -> go ()
                                                | _          -> raise BadDir
                                in go ()
                              in
                              let rec go ts =
                                match holtoken lexbuf with
                                  DirEnd -> DirBlk (n,List.rev ts)
                                | t      -> go (t::ts)
                              in
                              go []
            | DirEnd       -> raise BadDir
            | TeXStartHol  -> lex := holtoken; t
            | TeXStartHol0 -> lex := holtoken; t
            | TeXEndHol    -> lex := textoken; t
            | TeXEndHol0   -> lex := textoken; t
            | HolStartTeX  -> lex := textoken; t
            | HolEndTeX    -> lex := holtoken; t
            | t            -> t)
    with
      Eof -> None
  in
  Stream.from f

let holtokstream = tokstream holtoken

let textokstream = tokstream textoken

} 

