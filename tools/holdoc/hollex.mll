(* hollex.mll  --  (approximate) HOL lexer *)
(* Keith Wansbrough 2001 *)

{
exception Eof     of string  (* raised by holtoken at end of file *)
exception BadChar of string  (* raised by holtoken if unrecognised char scanned *)
exception BadTerm of string  (* raised if HOL in TeX is ill-terminated *)
exception BadDir  of string  (* raised if bad directive scanned *)

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

(* symbolic identifiers that contain nonaggregating characters; user-extensible *)
let nonagg_specials = ref ["()"; "[]"; ".."; "..."]

}

(* some classes *)
let white    = [' ' '\r' '\t' '\012']
let newline  = '\n'

let backtick = '`'

(* this pattern marks the beginning of the scanned "body" area *)
let startpat = "Net_Hol_reln" (white | newline)* backtick

(* the character classes of HOL *)
let idchar = ['A'-'Z' 'a'-'z' '0'-'9' '_' '\'']
let symbol = ['|' '!' '#' '%' '&' ')' '-' '=' '+' '[' ']' '{'
                 '}' ';' ':' '@' '~' '\\' ',' '.' '<' '>' '?' '/'
                 '^' (* not in HOL *) ]
let nonparen = symbol | '*'
let nonstar = symbol | '('
let anysymb = idchar* | nonparen* '(' |  ( nonparen | '(' nonstar )+

let dollar = '$'

let startcom = "(*"
let incomm   = [^ '(' '*'] | '(' [^ '*'] | '*' [^ ')']
let stopcom  = "*)"

let startdir = "(*["
let enddir   = "]*)"

let starttex = "(*:"
let tendhol  = "]]"
let tendhol0 = "]>"

(* tokens for TeX *)

let tnormal    = [^ '[' '<' ':' '(']
               | ['[' '<'] '<'* [^ '[' '<' ':' '(']
               | ('[' | '<'  '(' '*') [^ '[']
               | '(' [^ '*']
               | ':' [^ '*']
               | ':' '*' [^ ')']
  (* INCORRECT negation of tstarthol | tstarthol0 | endtex | tstartdir | startdir *)
  (* We want tnormal to accept the following language:

         State   [  <  :  *  )  (  X     where X is "anything else"
           1     2  2  4  9  9  3  9
           2     1  2  4  9  9  3  9
           3     2  2  4  2  9  3  9
           4     2  2  4  5  9  3  9
           5     2  2  4  9  1  3  9
           9(ACCEPT)

     I tried to work this out on paper but got stuck.
  *)


let tstarthol  = "[["
let tstarthol0 = "<["
let endtex     = ":*)"

let tstartdir  = "%(*["
(* also startdir = "(*[" *)

(* now some rules *)

rule

(* holtoken returns the next token, or raises Finished|BadChar *)

(* qualified identifiers are not supported *)

  holtoken = parse
    '"' ([^ '"'] | '\\' [ 'n' '"' '\\' 'r' ])* '"'
                           { let s = Lexing.lexeme lexbuf in
                             Str (String.sub s 1 (String.length s - 2)) }
  | startdir               { DirBeg }
  | enddir                 { DirEnd }
  | tendhol                { TeXEndHol }
  | tendhol0               { TeXEndHol0 }
  | starttex               { HolStartTeX }
  | startcom               { comments := [];
                             comment lexbuf;
                             Comment (String.concat "" (List.rev !comments))}
  | dollar? anysymb        { Ident (Lexing.lexeme lexbuf,true) }
  | newline white*         { Indent (indent_width (Lexing.lexeme lexbuf)) }
  | white+                 { White (Lexing.lexeme lexbuf) }
  | backtick               { Backtick }
  | backtick backtick      { DBacktick }
  | eof                    { raise (Eof "in HOL source") }
  | _                      { raise (BadChar ("didn't expect char '"^Lexing.lexeme lexbuf^"'")) }

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

(* this would be nice up front, but as the note says above, it's
   wrong; instead, we put it at the end and break up the TeX into much
   smaller fragments :-(

    tnormal+ { TeXNormal (Lexing.lexeme lexbuf) }
  |
   *)

    tstarthol      { TeXStartHol }
  | tstarthol0     { TeXStartHol0 }
  | endtex         { HolEndTeX }
  | tstartdir      { DirBeg }
  | startdir       { DirBeg }   (* recognised also, for .mni files that may
                                   be included in either HOL or TeX. *)

  (* see comment above for these three rules *)
  (* but I've added an exclusion for '%', permission for '\%',
     and a new rule in the middle, to deal with comments *)
  | ([^ '[' '<' ':' '*' '(' ')' '%'] | '\\' '%')+  { TeXNormal (Lexing.lexeme lexbuf) }
  | '%' [^ '\n']* '\n'                             { TeXNormal (Lexing.lexeme lexbuf) }
  | _                                              { TeXNormal (Lexing.lexeme lexbuf) }

  | eof            { raise (Eof "in TeX source") }


{

(* not very efficient prefix testing *)
let isPrefix str s = Str.string_match (Str.regexp_string str) s 0

let nonagg_re = Str.regexp "[]()[{}~.,;]"

let isAlphaNum c = c >= 'A' && c <= 'Z'
                || c >= 'a' && c <= 'z'
                || c >= '0' && c <= '9'
                || c = '_'

(* build a fast stream of tokens from lexed stdin, doing the
   second-pass of lexing on the way *)
let tokstream p chan =
  let lexbuf = Lexing.from_channel chan in
  let lex = ref p in
  let pending = (ref None : string option ref) in
  let next () = match !pending with
                  Some(s) -> pending := None;
                             (* Ugly hack: we *really* want to push
                                this back and re-lex it as
                                appropriate, but we can't do that.  So
                                we simply return something.  If we're
                                parsing HOL, we're fine: this Ident
                                will be resplit as we intend.  But if
                                we're parsing TeX, simply returning a
                                separate TeX fragment isn't right - if
                                the string includes something else,
                                say [[ <[ colon-star-rparen
                                paren-star-[ or similar, it will *not*
                                be processed.  Ah well. *)
                             if !lex = holtoken then
                               Ident(s,true)
                             else
                               TeXNormal(s)
                | None    -> !lex lexbuf in
  let push s  = match !pending with
                  (* failure here would be an internal error *)
                  None    -> if s = "" then
                               ()
                             else
                               pending := Some(s) in

  (* split identifier, respecting nonagg chars but modulo known
     nonagg_specs (operators containing nonagg chars *)
  (* cf HOL98 src/parse/term_tokens.sml *)
  let rec split_ident nonagg_specs s
    = match String.get s 0 with
        '"'  -> (Ident(s,true),"")
      | '_'  -> (Ident(s,true),"")
      | '\'' -> (Ident(s,true),"")  (* be liberal in what you accept *)
      | '$'  -> let rest = Str.string_after s 1 in
                (match split_ident nonagg_specs rest with
                   (Ident(s',b),r) -> (Ident("$"^s',b),r)
                 | _               -> raise (BadChar "expected ident after $"))
      | c    -> let possible_nonaggs = List.filter (function spec -> isPrefix spec s)
                                                   nonagg_specs in
                if possible_nonaggs = [] then
                  try
                    let i = Str.search_forward nonagg_re s 0 in
                    if i = 0 then
                      if isPrefix "]]" s then  (* tendhol *)
                        (TeXEndHol,Str.string_after s 2)
                      else if isPrefix "]>" s then (* tendhol0 *)
                        (TeXEndHol0,Str.string_after s 2)
                      else if isPrefix "]*)" s then (* enddir *)
                        (DirEnd,Str.string_after s 3)
                      else
                        (Sep(String.make 1 c),Str.string_after s 1)
                    else
                       (Ident(Str.string_before s i,isAlphaNum c),Str.string_after s i)
                  with
                    Not_found -> (Ident(s,isAlphaNum c),"")
                else
                  (let compare s1 s2 = String.length s2 - String.length s1 in
                   let best = List.hd (List.stable_sort compare possible_nonaggs) in
                   let sz = String.length best in
                   (Ident(best,isAlphaNum c),Str.string_after s sz)) in

  let f _ = (* I hope it is valid to assume that *all*
               tokens are requested, in ascending order! *)
    try
      Some (let t = next () in
            match t with
              DirBeg       -> let oldlex = !lex in
                              lex := holtoken;
                              let n =
                                let rec go () = match next () with
                                                  Ident(s,_) -> (match split_ident !nonagg_specials s with
                                                                   (Ident(s,_),r) -> push r; s
                                                                 | _              -> raise (BadDir "not an ident after splitting in directive"))
                                                | White(_)   -> go ()
                                                | _          -> raise (BadDir "expected ident or whitespace in directive")
                                in go ()
                              in
                              let rec go ts =
                                match next () with
                                  Ident(s,_) -> (match split_ident !nonagg_specials s with
                                                   (DirEnd,r) -> lex := oldlex; push r; DirBlk (n,List.rev ts)
                                                 | (t,r)      -> push r; go (t::ts))
                                | DirEnd -> lex := oldlex; DirBlk (n,List.rev ts)
                                | t      -> go (t::ts)
                              in
                              go []
            | DirEnd       -> raise (BadDir "directive-end symbol without directive-begin")
            | TeXStartHol  -> lex := holtoken; t
            | TeXStartHol0 -> lex := holtoken; t
            | TeXEndHol    -> lex := textoken; t
            | TeXEndHol0   -> lex := textoken; t
            | HolStartTeX  -> lex := textoken; t
            | HolEndTeX    -> lex := holtoken; t
            | Ident(s,_)   -> (let (t,r) = split_ident !nonagg_specials s in
                               match t with
                                 TeXEndHol  -> lex := textoken; push r; t
                               | TeXEndHol0 -> lex := textoken; push r; t
                               | DirEnd     -> raise (BadDir "directive-end symbol without directive-begin after split")
                               | _          -> push r; t)
            | t            -> t)
    with
      (Eof _) -> None
  in
  Stream.from f

let holtokstream = tokstream holtoken

let textokstream = tokstream textoken

}

