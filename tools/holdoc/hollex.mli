(* hollex.mli  --  (approximate) HOL lexer interface *)
(* Keith Wansbrough 2001 *)

open Holparsesupp
open Holparse

exception Mismatch of string     (* mismatched delimiters *)
exception BadChar of string      (* bad character *)
exception EOF                    (* attempt to read past (already-reported) EOF *)

type hollexstate

val token_init : mode -> Lexing.lexbuf -> hollexstate

val token : hollexstate -> token

val tokstream : mode -> in_channel -> token Stream.t

val render_token : token -> string

val print_token : delim list -> token -> string * delim list

