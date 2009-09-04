(* Binaryset -- sets implemented by ordered balanced binary trees *)
(* From SML/NJ lib 0.2, copyright 1993 by AT&T Bell Laboratories  *)
(* Original implementation due to Stephen Adams, Southampton, UK  *)

signature Binaryset =
sig

type 'item set

exception NotFound

val empty        : ('item * 'item -> order) -> 'item set
val singleton    : ('item * 'item -> order) -> 'item -> 'item set
val add          : 'item set * 'item -> 'item set
val addList      : 'item set * 'item list -> 'item set
val retrieve     : 'item set * 'item -> 'item
val peek         : 'item set * 'item -> 'item option
val isEmpty      : 'item set -> bool
val equal        : 'item set * 'item set -> bool
val isSubset     : 'item set * 'item set -> bool
val member       : 'item set * 'item -> bool
val delete       : 'item set * 'item -> 'item set
val numItems     : 'item set ->  int
val union        : 'item set * 'item set -> 'item set
val intersection : 'item set * 'item set -> 'item set
val difference   : 'item set * 'item set -> 'item set
val listItems    : 'item set -> 'item list
val app          : ('item -> unit) -> 'item set -> unit
val revapp       : ('item -> unit) -> 'item set -> unit
val foldr        : ('item * 'b -> 'b) -> 'b -> 'item set -> 'b
val foldl        : ('item * 'b -> 'b) -> 'b -> 'item set -> 'b
val find         : ('item -> bool) -> 'item set -> 'item option

end

(*
   ['item set] is the type of sets of ordered elements of type 'item.
   The ordering relation on the elements is used in the representation
   of the set.  The result of combining two sets with different
   underlying ordering relations is undefined.  The implementation
   uses ordered balanced binary trees.

   [empty ordr] creates a new empty set with the given ordering
   relation.

   [singleton ordr i] creates the singleton set containing i, with the
   given ordering relation.

   [add(s, i)] adds item i to set s.

   [addList(s, xs)] adds all items from the list xs to the set s.

   [retrieve(s, i)] returns i if it is in s; raises NotFound otherwise.

   [peek(s, i)] returns SOME i if i is in s; returns NONE otherwise.

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
