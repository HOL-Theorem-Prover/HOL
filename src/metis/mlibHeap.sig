(* ========================================================================= *)
(* A HEAP DATATYPE FOR ML                                                    *)
(* Created by Joe Hurd, October 2001                                         *)
(* Taken from Purely Functional Data Structures, by Chris Okasaki.           *)
(* ========================================================================= *)

signature mlibHeap =
sig

type 'a heap

val empty    : ('a * 'a -> order) -> 'a heap
val add      : 'a -> 'a heap -> 'a heap
val is_empty : 'a heap -> bool
val top      : 'a heap -> 'a            (* raises Empty *)
val remove   : 'a heap -> 'a * 'a heap  (* raises Empty *)
val size     : 'a heap -> int
val app      : ('a -> unit) -> 'a heap -> unit
val to_list  : 'a heap -> 'a list
val pp_heap  : 'a mlibUseful.pp -> 'a heap mlibUseful.pp

end