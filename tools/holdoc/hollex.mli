(* hollex.mli  --  (approximate) HOL lexer interface *)
(* Keith Wansbrough 2001 *)

exception Eof
exception BadChar

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

val render_token : token -> string

val holtokstream : token Stream.t

val textokstream : token Stream.t


