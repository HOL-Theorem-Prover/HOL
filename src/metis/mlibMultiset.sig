(* ========================================================================= *)
(* A MULTISET DATATYPE FOR ML                                                *)
(* Copyright (c) 2002-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

signature mlibMultiset =
sig

type 'a mset

val empty    : ('a * 'a -> order) -> 'a mset
val insert   : 'a * int -> 'a mset -> 'a mset
val count    : 'a mset -> 'a -> int
val union    : 'a mset -> 'a mset -> 'a mset
val compl    : 'a mset -> 'a mset
val subtract : 'a mset -> 'a mset -> 'a mset
val subset   : 'a mset -> 'a mset -> bool
val equal    : 'a mset -> 'a mset -> bool
val compare  : 'a mset * 'a mset -> order option
val sign     : 'a mset -> order option                (* compare to empty *)
val app      : ('a * int -> unit) -> 'a mset -> unit
val foldl    : ('a * int * 'b -> 'b) -> 'b -> 'a mset -> 'b
val foldr    : ('a * int * 'b -> 'b) -> 'b -> 'a mset -> 'b
val exists   : ('a * int -> bool) -> 'a mset -> bool
val all      : ('a * int -> bool) -> 'a mset -> bool
val map      : ('a * int -> int) -> 'a mset -> 'a mset
val nonzero  : 'a mset -> int
val to_list  : 'a mset -> ('a * int) list
val pp_mset  : 'a mlibUseful.pp -> 'a mset mlibUseful.pp

end
