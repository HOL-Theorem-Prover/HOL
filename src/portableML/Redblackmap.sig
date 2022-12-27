(* Redblackmap -- applicative maps as Red-black trees *)
signature Redblackmap =
sig
  type ('key, 'a) dict

  exception NotFound

  val mkDict     : ('key * 'key -> order) -> ('key, 'a) dict
  val fromList   : ('key * 'key -> order) -> ('key * 'a) list -> ('key, 'a) dict
  val update     : ('key, 'a) dict * 'key * ('a option -> 'a) -> ('key, 'a) dict
  val insert     : ('key, 'a) dict * 'key * 'a -> ('key, 'a) dict
  val insertList : ('key, 'a) dict * ('key * 'a) list -> ('key, 'a) dict
  val findKey    : ('key, 'a) dict * 'key -> 'key * 'a
  val find       : ('key, 'a) dict * 'key -> 'a
  val peek       : ('key, 'a) dict * 'key -> 'a option
  val remove     : ('key, 'a) dict * 'key -> ('key, 'a) dict * 'a
  val numItems   : ('key, 'a) dict -> int
  val listItems  : ('key, 'a) dict -> ('key * 'a) list
  val isEmpty    : ('key, 'a) dict -> bool
  val app        : ('key * 'a -> unit) -> ('key,'a) dict -> unit
  val revapp     : ('key * 'a -> unit) -> ('key,'a) dict -> unit
  val foldr      : ('key * 'a * 'b -> 'b)-> 'b -> ('key,'a) dict -> 'b
  val foldl      : ('key * 'a * 'b -> 'b) -> 'b -> ('key,'a) dict -> 'b
  val map        : ('key * 'a -> 'b) -> ('key,'a) dict -> ('key, 'b) dict
  val transform  : ('a -> 'b) -> ('key,'a) dict -> ('key, 'b) dict
end

(*
   [('key, 'a) dict] is the type of applicative maps from domain type
   'key to range type 'a, or equivalently, applicative dictionaries
   with keys of type 'key and values of type 'a.  They are implemented
   as Okasaki-style red-black trees.

   [mkDict ordr] returns a new, empty map whose keys have ordering
   ordr.

   [fromList ordr xs] returns a map that contains the (index, value)
   pairs in xs, whose keys have ordering ordr.  It is equivalent to
   insertList (mkDict ordr, xs).

   [update(m, i, f)] extends m to map i to (f NONE) if i is not
   already mapped, or to (f (SOME v)) if i is already mapped to v.

   [insert(m, i, v)] extends (or modifies) map m to map i to v.

   [insertList(m, xs)] extends (or modifies) map m with the (index,
   value) pairs in xs.  (It is equivalent to foldl (fn ((i, v), m) =>
   insert (m, i, v)) m xs.)  Note that later list entries will
   overwrite earlier entries for the same index.

   [findKey (m, k)] returns (k, v) if m maps k to v;
   otherwise, raises NotFound. The returned key is the last one EQUAL in
   the order to k that was used to extend or modify the map.

   [find (m, k)] returns v if m maps k to v; otherwise raises NotFound.

   [peek(m, k)] returns SOME v if m maps k to v; otherwise returns NONE.

   [remove(m, k)] removes k from the domain of m and returns the
   modified map and the element v corresponding to k.  Raises NotFound
   if k is not in the domain of m.

   [numItems m] returns the number of entries in m (that is, the size
   of the domain of m).

   [listItems m] returns a list of the entries (k, v) of keys k and
   the corresponding values v in m, in order of increasing key values.

   [isEmpty m] returns true if the map m is empty, and false otherwise.

   [app f m] applies function f to the entries (k, v) in m, in
   increasing order of k (according to the ordering ordr used to
   create the map or dictionary).

   [revapp f m] applies function f to the entries (k, v) in m, in
   decreasing order of k.

   [foldl f e m] applies the folding function f to the entries (k, v)
   in m, in increasing order of k.

   [foldr f e m] applies the folding function f to the entries (k, v)
   in m, in decreasing order of k.

   [map f m] returns a new map whose entries have form (k, f(k,v)),
   where (k, v) is an entry in m.

   [transform f m] returns a new map whose entries have form (k, f v),
   where (k, v) is an entry in m.
*)
