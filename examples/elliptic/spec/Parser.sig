(* ========================================================================= *)
(* PARSER COMBINATORS                                                        *)
(* Copyright (c) 2001-2004 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

signature Parser =
sig

(* Recommended fixities
  infixr 9 >>++
  infixr 8 ++
  infixr 7 >>
  infixr 6 ||
*)

(* ------------------------------------------------------------------------- *)
(* Generic                                                                   *)
(* ------------------------------------------------------------------------- *)

exception Noparse

val error : 'a -> 'b * 'a

val ++ : ('a -> 'b * 'a) * ('a -> 'c * 'a) -> 'a -> ('b * 'c) * 'a

val >> : ('a -> 'b * 'a) * ('b -> 'c) -> 'a -> 'c * 'a

val >>++ : ('a -> 'b * 'a) * ('b -> 'a -> 'c * 'a) -> 'a -> 'c * 'a

val || : ('a -> 'b * 'a) * ('a -> 'b * 'a) -> 'a -> 'b * 'a

val smany : ('s -> 'a -> 's * 'a) -> 's -> 'a -> 's * 'a

val many : ('a -> 'b * 'a) -> 'a -> 'b list * 'a

val atleastone : ('a -> 'b * 'a) -> 'a -> 'b list * 'a

val nothing : 'a -> unit * 'a

val optional : ('a -> 'b * 'a) -> 'a -> 'b option * 'a

(* ------------------------------------------------------------------------- *)
(* Stream-based                                                              *)
(* ------------------------------------------------------------------------- *)

type ('a,'b) parser = 'a Stream.stream -> 'b * 'a Stream.stream

val everything : ('a, 'b list) parser -> 'a Stream.stream -> 'b Stream.stream

val maybe : ('a -> 'b option) -> ('a,'b) parser

val finished : ('a,unit) parser

val some : ('a -> bool) -> ('a,'a) parser

val any : ('a,'a) parser

val exact : ''a -> (''a,''a) parser

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty-printing for infix operators                           *)
(* ------------------------------------------------------------------------- *)

type infixities = {tok : string, prec : int, left_assoc : bool} list

val infix_toks : infixities -> string list

val parse_infixes :
    infixities -> (string * 'a * 'a -> 'a) -> (string,'a) parser ->
    (string,'a) parser

val pp_infixes :
    infixities -> ('a -> (string * 'a * 'a) option) ->
    (ppstream -> 'a * bool -> unit) -> ppstream -> 'a * bool -> unit

end
