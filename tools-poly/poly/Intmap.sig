(* Intmap -- Applicative maps with integer keys                  *)
(* From SML/NJ lib 0.2, copyright 1993 by AT&T Bell Laboratories *)
(* Original implementation due to Stephen Adams, Southampton, UK *)

signature Intmap =
sig

type 'a intmap

exception NotFound

val empty     : unit -> 'a intmap
val insert    : 'a intmap * int * 'a -> 'a intmap
val retrieve  : 'a intmap * int -> 'a
val peek      : 'a intmap * int -> 'a option
val remove    : 'a intmap * int -> 'a intmap * 'a
val numItems  : 'a intmap ->  int
val listItems : 'a intmap -> (int * 'a) list
val app       : (int * 'a -> unit) -> 'a intmap -> unit
val revapp    : (int * 'a -> unit) -> 'a intmap -> unit
val foldr     : (int * 'a * 'b -> 'b) -> 'b -> 'a intmap -> 'b
val foldl     : (int * 'a * 'b -> 'b) -> 'b -> 'a intmap -> 'b
val map       : (int * 'a -> 'b) -> 'a intmap -> 'b intmap
val transform : ('a -> 'b) -> 'a intmap -> 'b intmap

end

(*
   ['a intmap] is the type of applicative maps from int to 'a.

   [empty] creates a new empty map.

   [insert(m, i, v)] extends (or modifies) map m to map i to v.

   [retrieve(m, i)] returns v if m maps i to v; otherwise raises
   NotFound.

   [peek(m, i)] returns SOME v if m maps i to v; otherwise NONE.

   [remove(m, i)] removes i from the domain of m and returns the
   modified map and the element v corresponding to i.  Raises NotFound
   if i is not in the domain of m.

   [numItems m] returns the number of entries in m (that is, the size
   of the domain of m).

   [listItems m] returns a list of the entries (i, v) of integers i and
   the corresponding values v in m, in increasing order of i.

   [app f m] applies function f to the entries (i, v) in m, in
   increasing order of i.

   [revapp f m] applies function f to the entries (i, v) in m, in
   decreasing order of i.

   [foldl f e m] applies the folding function f to the entries (i, v)
   in m, in increasing order of i.

   [foldr f e m] applies the folding function f to the entries (i, v)
   in m, in decreasing order of i.

   [map f m] returns a new map whose entries have form (i, f(i,v)),
   where (i, v) is an entry in m.

   [transform f m] returns a new map whose entries have form (i, f(i,v)),
   where (i, v) is an entry in m.
*)
