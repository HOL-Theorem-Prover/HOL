(* hollex.mli  --  (approximate) HOL lexer interface *)
(* Keith Wansbrough 2001 *)

exception Eof
exception BadChar
exception Finished

type token =
    Ident of string * bool  (* alphanumeric? *)
  | Indent of int
  | White of string
  | Comment of string
  | DirBeg  (* delimiters for holdoc parsing directives *)
  | DirEnd  (* ditto *)
  | DirBlk of string * token list (* nonterminal: directive name and body *)
  | Sep of string

val relheader : Lexing.lexbuf -> unit

val reltoken : Lexing.lexbuf -> token

