(* hollex.mll  --  (approximate) HOL lexer *)
(* Keith Wansbrough 2001-4 *)

{

open Holdoc_init
open Holparsesupp
open Holparse

exception Mismatch of string     (* mismatched delimiters *)
exception BadChar of string      (* bad character *)
exception EOF                    (* attempt to read past (already-reported) EOF *)


type parser_info = {
    expected : delim;   (* expected closing delimiter *)
    backtick : bool;    (* is a backtick OK here? *)
  }

let check_close pi got lexbuf =
  if pi.expected = got then
    From got
  else if !hOLDELIMUNBAL &&
          ((pi.expected = DelimHolTex && got = DelimHolTexMath) ||
           (pi.expected = DelimHolTexMath && got = DelimHolTex)) then
    From got
  else
    raise (Mismatch ("Mismatched delimiters: "^(delim_info pi.expected).sopen^" closed by "^(delim_info got).sclose ^ " at " ^ pretty_pos lexbuf))

let check_close_tex_ml pi lexbuf =
  let got = DelimText in
  if pi.expected = DelimTex then
    raise (Mismatch ("Mismatched delimiters: "^(delim_info pi.expected).sopen^" closed by "^(delim_info got).sclose ^ " at " ^ pretty_pos lexbuf))
  else
    Content ((delim_info got).sclose)

let bad_char mode lexbuf =
  raise (BadChar ("didn't expect char '"^Lexing.lexeme lexbuf^"' at " ^ pretty_pos lexbuf ^ " in " ^ render_mode mode ^ " mode (or illegal character in lexeme beginning here)."))
  
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

(* not very efficient prefix testing *)
let isPrefix str s = Str.string_match (Str.regexp_string str) s 0

let isAlphaNum c = c >= 'A' && c <= 'Z'
                || c >= 'a' && c <= 'z'
                || c >= '0' && c <= '9'
                || c = '_'
;;

let rec findfirst : ('a -> 'b option) -> 'a list -> 'b option
  = fun f xs
  -> match xs with
      []      -> None
    | (x::xs) -> match f x with
                   None         -> findfirst f xs
                 | Some(_) as y -> y


(* accept only a prefix of the most-recently-matched lexeme *)
(* WARNING: fragile dependencies on implementation of OCaml's Lexing module *)
let rewind_partial lexbuf len =
  lexbuf.Lexing.lex_curr_pos <- lexbuf.Lexing.lex_start_pos + len;
  lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p
                                with Lexing.pos_cnum = lexbuf.Lexing.lex_abs_pos + lexbuf.Lexing.lex_curr_pos }

let register_newline lexbuf =
  let pos = lexbuf.Lexing.lex_start_p in
  lexbuf.Lexing.lex_curr_p <- { pos with
                                Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
                                Lexing.pos_bol = pos.Lexing.pos_cnum + 1 }

let register_newlines lexbuf s =
  let rec count_newlines i s n =
    try
      count_newlines (String.index_from s i '\n' + 1) s (n+1)
    with
      Not_found -> (n,String.length s - i)
  in
  let (lines,off) = count_newlines 0 s 0 in
  if lines > 0 then begin
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- { pos with
                                  Lexing.pos_lnum = pos.Lexing.pos_lnum + lines;
                                  Lexing.pos_bol = pos.Lexing.pos_cnum - off }
  end
  else
    ()
  

let directive_alist =
  [
   (* normal holdoc_init directives *)
   ("CLASS_LIST"       ,CLASS_LIST       );
   ("CLASS"            ,CLASS            );
   ("TYPE_LIST"        ,TYPE_LIST        );
   ("CON_LIST"         ,CON_LIST         );
   ("FIELD_LIST"       ,FIELD_LIST       );
   ("LIB_LIST"         ,LIB_LIST         );
   ("AUX_LIST"         ,AUX_LIST         );
   ("AUX_INFIX_LIST"   ,AUX_INFIX_LIST   );
   ("VAR_PREFIX_LIST"  ,VAR_PREFIX_LIST  );
   ("VAR_PREFIX_ALIST" ,VAR_PREFIX_ALIST );
   ("AUTO_BINDERS"     ,AUTO_BINDERS     );
   ("NOAUTO_BINDERS"   ,NOAUTO_BINDERS   );
   ("HOL_OP_LIST"      ,HOL_OP_LIST      );
   ("HOL_SYM_ALIST"    ,HOL_SYM_ALIST    );
   ("HOL_SYM_BOL_ALIST",HOL_SYM_BOL_ALIST);
   ("HOL_IOPEN_LIST"   ,HOL_IOPEN_LIST   );
   ("HOL_ICLOSE_LIST"  ,HOL_ICLOSE_LIST  );
   ("HOL_ID_ALIST"     ,HOL_ID_ALIST     );
   ("HOL_CURRIED_ALIST",HOL_CURRIED_ALIST);
   ("SMART_PREFIX"     ,SMART_PREFIX     );
   ("NO_SMART_PREFIX"  ,NO_SMART_PREFIX  );
   ("INDENT"           ,INDENT           );
   ("NOINDENT"         ,NOINDENT         );
   ("RULES"            ,RULES            );
   ("NORULES"          ,NORULES          );
   ("COMMENTS"         ,COMMENTS         );
   ("NOCOMMENTS"       ,NOCOMMENTS       );
   ("ECHO"             ,ECHO             );
   ("NOECHO"           ,NOECHO           );
   ("RCSID"            ,RCSID            );
   ("HOLDELIM"         ,HOLDELIM         );
   ("HOLDELIMUNBAL"    ,HOLDELIMUNBAL    );
   ("NOHOLDELIMUNBAL"  ,NOHOLDELIMUNBAL  );
   ("NEWMODE"          ,NEWMODE          );
   ("MODE"             ,MODE             );
   ("SPECIAL"          ,SPECIAL          );
   (* special handling *)
   ("VARS"             ,VARS             );
 ]

}

(* --==================================================================-- *)

(* some classes *)
let white    = [' ' '\r' '\t' '\012']
let newline  = '\n'

let digit = ['0' - '9']
let hexdigit = [ '0' - '9' 'a' - 'f' 'A' - 'F' ]

let backtick = '`'

(* the character classes of HOL *)
let iidchar = ['A'-'Z' 'a'-'z' '\'']
let idchar = ['A'-'Z' 'a'-'z' '0'-'9' '_' '\'']
let symbol = ['|' '!' '#' '%' '&' ')' '-' '=' '+' '[' ']' '{'
                 '}' ';' ':' '@' '~' '\\' ',' '.' '<' '>' '?' '/'
                 '^' (* not in HOL *) ]
let mosmlsym = [ '!' '%' '&' '$' '#' '+' '-' '/' ':' '<' '=' '>' '?' '@' '\\' '~' '^' '|' '*' ]  (* and '`', but obviously we can't leave that in *)

let mosmlstr =
  '"' ([^ '"' '\\' '`']
      | '\\' ( [ 'a'-'z' ]
             | '^' _ 
             | digit digit digit
             | 'u' hexdigit hexdigit hexdigit hexdigit
             | '"' | '\\' | ( white | newline )* '\\'
             )
      )* '"'

let mosmlres =
  [ '(' ')' '[' ']' '{' '}' ',' ':' ';' '_' '|' '=' '#' ]
| ':' '>' | '.' '.' '.' | '=' '>' | '-' '>'


let nonparen = symbol | '*'
let nonstar = symbol | '('
let anysymb = idchar* | nonparen* '(' |  ( nonparen | '(' nonstar )+

let dollar = '$'

let startcom = "(*"
let incomm   = [^ '(' '*' '`'] | '(' [^ '*' '`'] | '*' [^ ')']
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


(* Each parser takes the expected closing token as argument, and
   either returns the next token or raises an exception.  When an
   opening token is encountered, a To() token is returned; the driver
   is expected subsequently to call the named parser rather than this
   one, passing the given closing token.  When that parser encounters
   the closing token, control is expected to return to this parser. *)

rule

  mosmltoken = parse
    mosmlstr               { let s = Lexing.lexeme lexbuf in
                             register_newlines lexbuf s;
                             fun _  -> Str (String.sub s 1 (String.length s - 2)) }
  | iidchar idchar*        { fun _  -> Ident (Lexing.lexeme lexbuf, true) }
  | mosmlsym+              { fun _  -> Ident (Lexing.lexeme lexbuf, false) }
  | '.'                    { fun _  -> Dot }
  | '~'? (digit+ | '0' 'x' hexdigit+)
                           { fun _  -> Int (Lexing.lexeme lexbuf) }
  | '~'? digit+ ('.' digit+) ([ 'e' 'E' ] '~'? digit+)
                           { fun _  -> Real (Lexing.lexeme lexbuf) }
  | '0' 'w' (digit+ | 'x' hexdigit+)
                           { fun _  -> Word (Lexing.lexeme lexbuf) }
  | '#' mosmlstr           { let s = Lexing.lexeme lexbuf in
                             register_newlines lexbuf ("#"^s);
                             fun _  -> Char (String.sub s 2 (String.length s - 3)) }
  | mosmlres               { fun _  -> Sep (Lexing.lexeme lexbuf) }
  | newline white*         { register_newline lexbuf;
                             fun _  -> Indent (indent_width (Lexing.lexeme lexbuf)) }
  | white+                 { fun _  -> White (Lexing.lexeme lexbuf) }
  | backtick               { fun _  -> ToHol(DelimHolMosml) }
  | backtick backtick      { fun _  -> ToHol(DelimHolMosmlD) }
  | starttex               { fun _  -> ToTex(DelimTex) }
  | startdir               { fun _  -> ToDir(DelimDir) }
  | startcom               { fun _  -> ToText(DelimText) }
  | eof                    { fun pi -> check_close pi DelimEOF lexbuf }
  | _                      { fun _  -> bad_char ModeMosml lexbuf }
    
and

  holtoken = parse
    '"' ([^ '"' '\\' '`'] | '\\' _ )* '"'
                           { let s = Lexing.lexeme lexbuf in
                             register_newlines lexbuf s;
                             fun _  -> Str (String.sub s 1 (String.length s - 2)) }
  | startdir               { fun _  -> ToDir(DelimDir) }
  | tendhol                { fun pi -> check_close pi DelimHolTex lexbuf }
  | tendhol0               { fun pi -> check_close pi DelimHolTexMath lexbuf }
  | starttex               { fun _  -> ToTex(DelimTex) }
  | startcom               { fun _  -> ToText(DelimText) }
  | dollar? anysymb        { fun _  -> Ident (Lexing.lexeme lexbuf,true) }
  | newline white*         { register_newline lexbuf;
                             fun _  -> Indent (indent_width (Lexing.lexeme lexbuf)) }
  | white+                 { fun _  -> White (Lexing.lexeme lexbuf) }
  | backtick               { fun pi -> check_close pi DelimHolMosml lexbuf }
  | backtick backtick      { fun pi -> check_close pi DelimHolMosmlD lexbuf }
  | eof                    { fun pi -> check_close pi DelimEOF lexbuf }
  | _                      { fun _  -> bad_char ModeHol lexbuf }

and
  texttoken = parse
    incomm+        { let s = Lexing.lexeme lexbuf in
                     register_newlines lexbuf s;
                     fun _  -> Content s }
  | startcom       { fun _  -> ToText(DelimText) }
  | stopcom        { fun pi -> check_close pi DelimText lexbuf }
  | endtex         { fun pi -> check_close pi DelimTex lexbuf }  (* always an error *)
  | eof            { fun pi -> check_close pi DelimEOF lexbuf }
  | backtick       { fun pi -> if pi.backtick then
                                 Content (Lexing.lexeme lexbuf)
                               else
                                 bad_char ModeText lexbuf }
  | _              { fun _  -> bad_char ModeText lexbuf }

and
  textoken = parse

(* this would be nice up front, but as the note says above, it's
 * wrong; instead, we put it at the end and break up the TeX into much
 * smaller fragments :-(
 *
 *  tnormal+ { TeXNormal (Lexing.lexeme lexbuf) }
 *)

    tstarthol      { fun _  -> ToHol(DelimHolTex) }
  | tstarthol0     { fun _  -> ToHol(DelimHolTexMath) }
  | endtex         { fun pi -> check_close pi DelimTex lexbuf }
  | stopcom        { fun pi -> check_close_tex_ml pi lexbuf }  (* check for ( * : closed by * ) *)
  | tstartdir      { fun _  -> ToDir(DelimDir) }  (* recognised as an alias; closedelim is the same *)
  | startdir       { fun _  -> ToDir(DelimDir) }

  (* see comment above for these three rules *)
  (* but I've added an exclusion for '%', permission for '\%',
     and a new rule in the middle, to deal with comments *)
  | ([^ '[' '<' ':' '*' '(' ')' '%' '`'] | '\\' '%')+
                   { let s = Lexing.lexeme lexbuf in
                     register_newlines lexbuf s;
                     fun _  -> Content s }
  | '%' [^ '\n' '`']* '\n'
                   { let s = Lexing.lexeme lexbuf in
                     register_newlines lexbuf s;
                     fun _  -> Content s }
  | eof            { fun pi -> check_close pi DelimEOF lexbuf }
  | backtick       { fun pi -> if pi.backtick then
                                 Content (Lexing.lexeme lexbuf)
                               else
                                 bad_char ModeTex lexbuf }
  | _              { let s = Lexing.lexeme lexbuf in
                     register_newlines lexbuf s;
                     fun _  -> Content s }

and
    dirtoken = parse
    '"' ([^ '"' '\\' '`'] | '\\' _ )* '"'
                           { let s = Lexing.lexeme lexbuf in
                             register_newlines lexbuf s;
                             fun _  -> Str (String.sub s 1 (String.length s - 2)) }
  | enddir                 { fun pi -> check_close pi DelimDir lexbuf }
  | startcom               { fun _  -> ToText(DelimText) }
  | dollar? anysymb        { fun _  ->
                             let s = Lexing.lexeme lexbuf in
                             try List.assoc s directive_alist with
                               Not_found -> Ident (s,true) }
  | white+                 { fun _  -> White (Lexing.lexeme lexbuf) }
  | newline white*         { register_newline lexbuf;
                             fun _  -> Indent (indent_width (Lexing.lexeme lexbuf)) }
  | eof                    { fun pi -> check_close pi DelimEOF lexbuf }
  | backtick               { fun _  -> bad_char ModeDir lexbuf }
  | _                      { fun _  -> bad_char ModeDir lexbuf }


(* --==================================================================-- *)

{

(* map from open-delimiter tokens to modes *)
let to_token_mode t =
  match t with
  | ToMosml _ -> ModeMosml
  | ToHol   _ -> ModeHol  
  | ToText  _ -> ModeText 
  | ToTex   _ -> ModeTex  
  | ToDir   _ -> ModeDir  
  | _         -> raise (NeverHappen "to_token_mode: not To* token")


(* is a backtick allowed in mode1, if previous mode was mode0 and
   previous allowance was backtick0? *)
let backtick_allowed backtick0 mode0 mode1 =
  backtick0  (* monotonic: once it's forbidden, it's forbidden in all descendants *)
  &&
  (not (mode0 = ModeMosml && mode1 = ModeHol))  (* forbidden in backtick-delimited HOL *)


(* eds is stack of enclosing delimiters *)
let print_token eds t =
  match t with
  | Ident(s,b) -> (s                     , eds)
  | Str(s)     -> ("\""^s^"\""           , eds)
  | Dot        -> ("."                   , eds)
  | Int(s)     -> (s                     , eds)
  | Real(s)    -> (s                     , eds)
  | Word(s)    -> (s                     , eds)
  | Char(s)    -> (s                     , eds)
  | Indent(n)  -> (make_indent n         , eds)
  | White(s)   -> (s                     , eds)
  | Sep(s)     -> (s                     , eds)
  | Content(s) -> (s                     , eds)
  | ToMosml(d) | ToHol(d) | ToText(d) | ToTex(d) | ToDir(d)
               -> ((delim_info d).sopen  , d::eds)
  | From(d)    -> (match eds with
                     (ed::eds') -> ((delim_info d).sclose, eds')
                   | []         -> ((delim_info d).sclose, []))
  | CLASS_LIST | CLASS | TYPE_LIST | CON_LIST | FIELD_LIST | LIB_LIST | AUX_LIST
  | AUX_INFIX_LIST | VAR_PREFIX_LIST | VAR_PREFIX_ALIST | AUTO_BINDERS | NOAUTO_BINDERS | HOL_OP_LIST
  | HOL_SYM_ALIST | HOL_SYM_BOL_ALIST | HOL_IOPEN_LIST | HOL_ICLOSE_LIST
  | HOL_ID_ALIST | HOL_CURRIED_ALIST | SMART_PREFIX
  | NO_SMART_PREFIX | INDENT | NOINDENT | RULES | NORULES | COMMENTS
  | NOCOMMENTS | ECHO | NOECHO | RCSID | HOLDELIM | HOLDELIMUNBAL | NOHOLDELIMUNBAL | NEWMODE | MODE
  | SPECIAL | VARS
               -> (List.assoc t (List.map (fun (x,y) -> (y,x)) directive_alist),
                   eds)


let render_token t =
  match t with
  | Ident(s,b) -> "I:"^s
  | Str(s)     -> "s:\""^s^"\""
  | Dot        -> ".:."
  | Int(s)     -> "n:"^s
  | Real(s)    -> "r:"^s
  | Word(s)    -> "w:"^s
  | Char(s)    -> "c:"^s
  | Indent(n)  -> "\n<"^string_of_int n^">"
  | White(s)   -> s
  | Sep(s)     -> "S:"^s
  | Content(s) -> "{C:"^s^":C}"
  | ToMosml(d) | ToHol(d) | ToText(d) | ToTex(d) | ToDir(d)
               -> "{D:"^render_mode (to_token_mode t)^(delim_info d).sopen
  | From(d)    -> (delim_info d).sclose^":D}"
  | CLASS_LIST | CLASS | TYPE_LIST | CON_LIST | FIELD_LIST | LIB_LIST | AUX_LIST
  | AUX_INFIX_LIST | VAR_PREFIX_LIST | VAR_PREFIX_ALIST | AUTO_BINDERS | NOAUTO_BINDERS | HOL_OP_LIST
  | HOL_SYM_ALIST | HOL_SYM_BOL_ALIST | HOL_IOPEN_LIST | HOL_ICLOSE_LIST
  | HOL_ID_ALIST | HOL_CURRIED_ALIST | SMART_PREFIX
  | NO_SMART_PREFIX | INDENT | NOINDENT | RULES | NORULES | COMMENTS
  | NOCOMMENTS | ECHO | NOECHO | RCSID | HOLDELIM | HOLDELIMUNBAL | NOHOLDELIMUNBAL | NEWMODE | MODE
  | SPECIAL | VARS
               -> "R:" ^ List.assoc t (List.map (fun (x,y) -> (y,x)) directive_alist)


(* map from mode names to parsers *)
let modeparser m =
  List.assoc m
    [
     (ModeMosml, mosmltoken);
     (ModeHol  , holtoken);
     (ModeText , texttoken);
     (ModeTex  , textoken);
     (ModeDir  , dirtoken);
     (ModeNone , fun _ _ -> raise (NeverHappen "modeparser: ModeNone"));
   ]

(* nonagg_specials is defined in Holdoc_init.  This is the set of 
   symbolic identifiers that contain nonaggregating characters; user-extensible *)

let nonagg_re = Str.regexp "[]()[{}~.,;]"

(* given a string that has matched as a HOL identifier, split an
   identifier or other token off the front, returning the token and
   the number of characters consumed.  The remaining characters should
   be pushed back and re-lexed.  Do this respecting nonaggregating
   characters but modulo known nonagg_specs (operators containing
   nonagg chars). *)
(* cf HOL98 src/parse/term_tokens.sml *)

let rec split_ident pi nonagg_specs s lexbuf (* lexbuf for error reporting only *)
    = match String.get s 0 with
        '"'  -> (Ident(s,true),String.length s)
      | '_'  -> (Ident(s,true),String.length s)
      | '\'' -> (Ident(s,true),String.length s)  (* this is a type token *)
      | '$'  -> let rest = Str.string_after s 1 in
                (if rest = "" then
                  raise (BadChar "expected ident after $")
                else
                  match split_ident pi nonagg_specs rest lexbuf with
                    (Ident(s',b),r) -> (Ident("$"^s',b),1+r)
                  | _               -> raise (BadChar "expected ident after $"))
      | c    -> let possible_nonaggs = List.filter (function spec -> isPrefix spec s)
                                                   nonagg_specs in
                if possible_nonaggs = [] then
                  try
                    let i = Str.search_forward nonagg_re s 0 in
                    if i = 0 then
                      match
                        findfirst (fun delim ->
                          let ds = (delim_info delim).sclose in
                          if isPrefix ds s then Some (check_close pi delim lexbuf, String.length ds) else None)
                          [DelimHolTex; DelimHolTexMath; DelimHolMosml; DelimHolMosmlD; DelimDir] with
                        Some x -> x
                      | None ->
                          (Sep(String.make 1 c), 1)
                    else
                       (Ident(Str.string_before s i,isAlphaNum c),i)
                  with
                    Not_found -> (Ident(s,isAlphaNum c),String.length s)
                else
                  (let compare s1 s2 = String.length s2 - String.length s1 in
                   let best = List.hd (List.stable_sort compare possible_nonaggs) in
                   let sz = String.length best in
                   (Ident(best,isAlphaNum c),sz))


(* a parser *)
type pparser = Lexing.lexbuf -> parser_info -> token

(* internal state for "token", the multiplexed parser *)
type hollexstate = {
    lexbuf : Lexing.lexbuf;
    mutable curmode : mode;
    mutable curparser : pparser;
    mutable curpi : parser_info;
    mutable stack : (mode * pparser * parser_info) list;
  }

(* create a hollexstate *)
let token_init mode lexbuf =
  { lexbuf = lexbuf;
    curmode = mode;
    curparser = modeparser mode;
    curpi = { expected = DelimEOF; backtick = true; };
    stack = [] }

(* given a hollexstate, return the next token in the stream *)
let token lst =
  let t0 = lst.curparser lst.lexbuf lst.curpi in
  let t1 =
    match t0 with
    | Ident(s,_) when (lst.curmode = ModeHol || lst.curmode = ModeDir) ->
        let (t',r) = split_ident lst.curpi !nonagg_specials s lst.lexbuf in
        rewind_partial lst.lexbuf r;
        t'
    | _ -> t0
  in
  match t1 with
  | ToMosml(delim)
  | ToHol  (delim)
  | ToText (delim)
  | ToTex  (delim)
  | ToDir  (delim) ->
      let mode = to_token_mode t1 in
      let backtick = backtick_allowed lst.curpi.backtick lst.curmode mode in
(*      print_string ("\nPUSH "^render_mode lst.curmode^" -> "^render_mode mode^"\n"); *)
      lst.stack     <- (lst.curmode,lst.curparser,lst.curpi) :: lst.stack;
      lst.curmode   <- mode;
      lst.curparser <- modeparser mode;
      lst.curpi     <- { expected = delim; backtick = backtick };
      t1
  | From (delim) ->
      (match lst.stack with
        [] ->
(*          print_string ("\nPOP - hit bottom\n");*)
          lst.curparser <- (fun _ _ -> raise EOF);
          t1
      | ((m,p,pi)::pds) ->
(*          print_string ("\nPOP "^render_mode lst.curmode^" -> "^render_mode m^"\n"); *)
          lst.curmode <- m;
          lst.curparser <- p;
          lst.curpi <- pi;
          lst.stack <- pds;
          t1)
  | _ ->
      t1


(* build a fast stream of tokens from lexed stdin, doing the
   second-pass of lexing on the way *)
let tokstream m chan =
  let lexbuf = Lexing.from_channel chan in
  let lst = token_init m lexbuf in
  (* I hope it is valid to assume that *all* tokens are requested, in ascending order! *)
  let next _ = try Some (token lst) with EOF -> None in
  Stream.from next

let holtokstream = tokstream ModeHol

let textokstream = tokstream ModeTex

}

