(* ========================================================================= *)
(* FINITE MAPS                                                               *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

signature Map =
sig

(* ------------------------------------------------------------------------- *)
(* Finite maps                                                               *)
(* ------------------------------------------------------------------------- *)

type ('key,'a) map

val new : ('key * 'key -> order) -> ('key,'a) map

val null : ('key,'a) map -> bool

val size : ('key,'a) map -> int

val singleton : ('key * 'key -> order) -> 'key * 'a -> ('key,'a) map

val inDomain : 'key -> ('key,'a) map -> bool

val peek : ('key,'a) map -> 'key -> 'a option

val insert : ('key,'a) map -> 'key * 'a -> ('key,'a) map

val insertList : ('key,'a) map -> ('key * 'a) list -> ('key,'a) map

val get : ('key,'a) map -> 'key -> 'a  (* raises Error *)

(* Both union and intersect prefer keys in the second map *)

val union :
    ('a * 'a -> 'a option) -> ('key,'a) map -> ('key,'a) map -> ('key,'a) map

val intersect :
    ('a * 'a -> 'a option) -> ('key,'a) map -> ('key,'a) map -> ('key,'a) map

val delete : ('key,'a) map -> 'key -> ('key,'a) map  (* raises Error *)

val difference : ('key,'a) map -> ('key,'a) map -> ('key,'a) map

val subsetDomain : ('key,'a) map -> ('key,'a) map -> bool

val equalDomain : ('key,'a) map -> ('key,'a) map -> bool

val mapPartial : ('key * 'a -> 'b option) -> ('key,'a) map -> ('key,'b) map

val filter : ('key * 'a -> bool) -> ('key,'a) map -> ('key,'a) map

val map : ('key * 'a -> 'b) -> ('key,'a) map -> ('key,'b) map

val app : ('key * 'a -> unit) -> ('key,'a) map -> unit

val transform : ('a -> 'b) -> ('key,'a) map -> ('key,'b) map

val foldl : ('key * 'a * 's -> 's) -> 's -> ('key,'a) map -> 's

val foldr : ('key * 'a * 's -> 's) -> 's -> ('key,'a) map -> 's

val findl : ('key * 'a -> bool) -> ('key,'a) map -> ('key * 'a) option

val findr : ('key * 'a -> bool) -> ('key,'a) map -> ('key * 'a) option

val exists : ('key * 'a -> bool) -> ('key,'a) map -> bool

val all : ('key * 'a -> bool) -> ('key,'a) map -> bool

val domain : ('key,'a) map -> 'key list

val toList : ('key,'a) map -> ('key * 'a) list

val fromList : ('key * 'key -> order) -> ('key * 'a) list -> ('key,'a) map

val nth : ('key,'a) map -> int -> 'key * 'a  (* raises Error *)

val compare : ('a * 'a -> order) -> ('key,'a) map * ('key,'a) map -> order

(* ------------------------------------------------------------------------- *)
(* Iterators over maps                                                       *)
(* ------------------------------------------------------------------------- *)

type ('key,'a) iterator

val mkIterator : ('key,'a) map -> ('key,'a) iterator option

val mkRevIterator : ('key,'a) map -> ('key,'a) iterator option

val readIterator : ('key,'a) iterator -> 'key * 'a

val advanceIterator : ('key,'a) iterator -> ('key,'a) iterator option

end
