(* FILE:      seq.sig
 * AUTHOR:    Michael Norrish
 * COPYRIGHT: University of Cambridge 1999
 *
 * NOTE:      Implementation of a lazy list, based on Larry Paulson's
 *            example from his "ML for the working programmer" but
 *            lazier.
 *
 * $Id$
 *)


signature seq = sig
type 'a seq

val cases : 'a seq -> ('a * 'a seq) option
val fcases : 'a seq -> ('b * (('a * 'a seq) -> 'b)) -> 'b

val append : 'a seq -> 'a seq -> 'a seq

val result : 'a -> 'a seq
val fresult : (unit -> 'a option) -> 'a seq
val delay : (unit -> 'a seq) -> 'a seq

val fromList : 'a list -> 'a seq

val flatten : 'a seq seq -> 'a seq

val map : ('a -> 'b) -> 'a seq -> 'b seq
val mapPartial : ('a -> 'b option) -> 'a seq -> 'b seq
val filter : ('a -> bool) -> 'a seq -> 'a seq
val bind : 'a seq -> ('a -> 'b seq) -> 'b seq

val empty : 'a seq
val null : 'a seq -> bool
val hd : 'a seq -> 'a
val tl : 'a seq -> 'a seq
val cons : 'a -> 'a seq -> 'a seq

val take : int -> 'a seq -> 'a list
val drop : int -> 'a seq -> 'a seq
val length : 'a seq -> int

end
