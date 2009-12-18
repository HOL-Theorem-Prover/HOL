(* Intset -- applicative sets of integers                        *)
(* From SML/NJ lib 0.2, copyright 1993 by AT&T Bell Laboratories *)
(* Original implementation due to Stephen Adams, Southampton, UK *)

signature Intset =
sig

type intset

exception NotFound

val empty        : intset
val singleton    : int -> intset
val add          : intset * int -> intset
val addList      : intset * int list -> intset
val isEmpty      : intset -> bool
val equal        : intset * intset -> bool
val isSubset     : intset * intset -> bool
val member       : intset * int -> bool
val delete       : intset * int -> intset
val numItems     : intset ->  int
val union        : intset * intset -> intset
val intersection : intset * intset -> intset
val difference   : intset * intset -> intset
val listItems    : intset -> int list
val app          : (int -> unit) -> intset -> unit
val revapp       : (int -> unit) -> intset -> unit
val foldr        : (int * 'b -> 'b) -> 'b -> intset -> 'b
val foldl        : (int * 'b -> 'b) -> 'b -> intset -> 'b
val find         : (int -> bool) -> intset -> int option

end

(*
   [intset] is the type of sets of integers.

   [empty] is the empty set of integers.

   [singleton i] is the singleton set containing i.

   [add(s, i)] adds item i to set s.

   [addList(s, xs)] adds all items from the list xs to the set s.

   [isEmpty s] returns true if and only if the set is empty.

   [equal(s1, s2)] returns true if and only if the two sets have the
   same elements.

   [isSubset(s1, s2)] returns true if and only if s1 is a subset of s2.

   [member(s, i)] returns true if and only if i is in s.

   [delete(s, i)] removes item i from s.  Raises NotFound if i is not in s.

   [numItems s] returns the number of items in set s.

   [union(s1, s2)] returns the union of s1 and s2.

   [intersection(s1, s2)] returns the intersectionof s1 and s2.

   [difference(s1, s2)] returns the difference between s1 and s2 (that
   is, the set of elements in s1 but not in s2).

   [listItems s] returns a list of the items in set s, in increasing
   order.

   [app f s] applies function f to the elements of s, in increasing
   order.

   [revapp f s] applies function f to the elements of s, in decreasing
   order.

   [foldl f e s] applies the folding function f to the entries of the
   set in increasing order.

   [foldr f e s] applies the folding function f to the entries of the
   set in decreasing order.

   [find p s] returns SOME i, where i is an item in s which satisfies
   p, if one exists; otherwise returns NONE.
*)
