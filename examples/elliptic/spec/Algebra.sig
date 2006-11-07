(* ========================================================================= *)
(* NORMALIZING ALGEBRAIC EXPRESSIONS                                         *)
(* Copyright (c) 2006 Joe Hurd, distributed under the GNU GPL version 2      *)
(* ========================================================================= *)

signature Algebra =
sig

(* ------------------------------------------------------------------------- *)
(* A type of algebraic expressions.                                          *)
(* ------------------------------------------------------------------------- *)

datatype expression =
    Var of string
  | Sum of (expression,int) Map.map
  | Prod of (expression,int) Map.map

val compare : expression * expression -> order

val equal : expression -> expression -> bool

val fromInt : int -> expression

val toInt : expression -> int option

val negate : expression -> expression

val add : expression * expression -> expression

val subtract : expression * expression -> expression

val multiply : expression * expression -> expression

val power : expression * int -> expression

val toString : expression -> string

val pp : ppstream -> expression -> unit

(* ------------------------------------------------------------------------- *)
(* Normalization with a set of equations.                                    *)
(* ------------------------------------------------------------------------- *)

val normalize :
    {equations : (expression * expression) list} -> expression -> expression

end
