(* Stack.sml *)

open List;

type 'a t = 'a list ref;

exception Empty;

fun new() = ref [];

fun push x s = (s := x :: !s);

fun pop s =
  case !s of
      [] => raise Empty
    | x :: xs => (s := xs; x)
;

fun peek s =
  case !s of
      [] => raise Empty
    | x :: xs => x
;

fun update x s =
  case !s of
      [] => raise Empty
    | _ :: xs => (s := x :: xs)
;

fun null s = List.null (!s);

fun clear s = (s := []);
