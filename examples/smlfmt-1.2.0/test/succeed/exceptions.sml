exception Hello of string
and World of char list
and What
and Who of {name: string}
and Where = Option.Option
and Why

exception Okay = What

exception WhatIsThis = List.Empty

infix 5 !!

(** kinda strange that SML allows the use of infixed !! here, without 'op'... *)
exception !! of int * int

val _ = raise 5 !! 6

val _ = raise Hello "hello"
val _ = raise World (String.explode "world")
