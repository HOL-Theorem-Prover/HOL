(* ========================================================================= *)
(* A HEAP DATATYPE FOR ML                                                    *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

signature mlibHeap =
sig

type 'a heap

val empty     : ('a * 'a -> order) -> 'a heap
val add       : 'a -> 'a heap -> 'a heap
val is_empty  : 'a heap -> bool
val top       : 'a heap -> 'a                     (* raises Empty *)
val remove    : 'a heap -> 'a * 'a heap           (* raises Empty *)
val size      : 'a heap -> int
val app       : ('a -> unit) -> 'a heap -> unit
val to_stream : 'a heap -> 'a mlibStream.stream
val pp        : 'a mlibUseful.pp -> 'a heap mlibUseful.pp

end
