(*
 * Abstract signature of an applicative-style finite maps (dictionaries)
 * structure over ordered monomorphic keys.
 *
 * COPYRIGHT (c) 1996 by AT&T Research.
 * COPYRIGHT (c) 2020 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *)

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
  val app        : ('key * 'a -> unit) -> ('key, 'a) dict -> unit
  val revapp     : ('key * 'a -> unit) -> ('key, 'a) dict -> unit
  val foldr      : ('key * 'a * 'b -> 'b)-> 'b -> ('key, 'a) dict -> 'b
  val foldl      : ('key * 'a * 'b -> 'b) -> 'b -> ('key, 'a) dict -> 'b
  val map        : ('key * 'a -> 'b) -> ('key, 'a) dict -> ('key, 'b) dict
  val transform  : ('a -> 'b) -> ('key, 'a) dict -> ('key, 'b) dict

   (* Below are API extensions of HOL's old Redblackmap structure *)
  val singleton  : ('key * 'key -> order) -> ('key * 'a) -> ('key, 'a) dict
  val insert'    : (('key * 'a) * ('key, 'a) dict) -> ('key, 'a) dict
  val insertWith : ('a * 'a -> 'a) -> ('key, 'a) dict * 'key * 'a ->
                   ('key, 'a) dict
  val insertWithi : ('key * 'a * 'a -> 'a) -> ('key, 'a) dict * 'key * 'a ->
                    ('key, 'a) dict
  val inDomain   : (('key, 'a) dict * 'key) -> bool
  val first      : ('key, 'a) dict -> 'a option
  val firsti     : ('key, 'a) dict -> ('key * 'a) option
  val listItems' : ('key, 'a) dict -> 'a list
  val listKeys   : ('key, 'a) dict -> 'key list
  val collate    : ('a * 'a -> order) -> (('key, 'a) dict * ('key, 'a) dict) -> order
  val unionWith  : ('a * 'a -> 'a) ->
                   (('key, 'a) dict * ('key, 'a) dict) -> ('key, 'a) dict
  val unionWithi : ('key * 'a * 'a -> 'a) ->
                   (('key, 'a) dict * ('key, 'a) dict) -> ('key, 'a) dict
  val intersectWith  : ('a * 'b -> 'c) ->
                       (('key, 'a) dict * ('key, 'b) dict) -> ('key, 'c) dict
  val intersectWithi : ('key * 'a * 'b -> 'c) ->
                       (('key, 'a) dict * ('key, 'b) dict) -> ('key, 'c) dict
  val mergeWith  : ('a option * 'b option -> 'c option) ->
                   (('key, 'a) dict * ('key, 'b) dict) -> ('key, 'c) dict
  val mergeWithi : ('key * 'a option * 'b option -> 'c option) ->
                   (('key, 'a) dict * ('key, 'b) dict) -> ('key, 'c) dict
  val app'       : ('a -> unit) -> ('key, 'a) dict -> unit
  val foldl'     : ('a * 'b -> 'b) -> 'b -> ('key, 'a) dict -> 'b
  val foldr'     : ('a * 'b -> 'b) -> 'b -> ('key, 'a) dict -> 'b
  val filter     : ('a -> bool) -> ('key, 'a) dict -> ('key, 'a) dict
  val filteri    : ('key * 'a -> bool) -> ('key, 'a) dict -> ('key, 'a) dict
  val mapPartial  : ('a -> 'b option) -> ('key, 'a) dict -> ('key, 'b) dict
  val mapPartiali : ('key * 'a -> 'b option) -> ('key, 'a) dict -> ('key, 'b) dict
  val exists     : ('a -> bool) -> ('key, 'a) dict -> bool
  val existsi    : ('key * 'a -> bool) -> ('key, 'a) dict -> bool
  val all        : ('a -> bool) -> ('key, 'a) dict -> bool
  val alli       : ('key * 'a -> bool) -> ('key, 'a) dict -> bool

  val fromOrderedList    : ('key * 'key -> order) -> ('key * 'a) list ->
                           ('key, 'a) dict
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

                                *  *  *

   [singleton ordr (i, v)] returns the specified singleton map.

   [insert' ((i, v), m)] extends (or modifies) map m to map i to v.
    Like insert, except that type of inputs are different. insert' is
    useful when the entry (i, v) to be inserted is given by a single
    variable.

   [insertWith comb (m, k, v)] inserts an item with a combining function
    to resolve collisions. The first argument to the combining function is
    the existing value, and the second argument is the value being inserted
    into the map.

   [insertWithi comb' (m, k, v)] is similar with insertWith, except that the
    combining function also takes the key as an argument.

   [inDomain (m, k)] returns true, if the key k is in the domain of the map m

   [first m] returns the first item in the map (or NONE if it is empty)

   [firsti m] is like first, except that the key is also returned.

   [listItems' m] returns an ordered list of the items in the map m.

   [listKeys m] returns an ordered list of the keys in the map.

   [collate ordr] is given an ordering on the map's range, it returns
    an ordering on the map (lexcographic).

   [unionWith f (m1, m2)] returns a map whose domain is the union of the
    domains of the two input maps, using the supplied function to define the
    map on elements that are in both domains.

   [unionWithi f (m1, m2)] is like unionWith, except that the supplied
    function also takes the key as an argument.

   [intersectWith f (m1, m2)] returns a map whose domain is the intersection of
    the domains of the two input maps, using the supplied function to define
    the range.

   [intersectWithi f (m1, m2)] is like intersectWith, except that the supplied
    function also takes the key as an argument.

   [mergeWith f (m1, m2)] merges two maps using the given function to control
    the merge. For each key k in the union of the two maps domains, the function
    is applied to the image of the key under the map.  If the function returns
    SOME y, then (k, y) is added to the resulting map.

   [mergeWithi f (m1, m2)] is like mergeWith, except that the function f also
    takes the key as an argument.

   [app' f m] applies the function f to the ranges of the map m in map order.

   [foldl' f e m] applies the folding function f to the ranges of the map m in
    increasing map order.

   [foldr' f e m] applies the folding function f to the ranges of the map m in
    decreasing map order.

   [filter p m] filters out those elements of the map m that do not satisfy the
    predicate p.  The filtering is done in increasing map order.

   [filteri p m] is like filter, except that the predicate p also takes the key
    as an argument.

   [mapPartial f m] maps a partial function f over the elements of a map in
    increasing map order.

   [mapPartiali f m] is like mapPartial, except that the function f also takes
    the key as an argument.

   [exists p m] checks the elements of a map with a predicate and return true
    if any element satisfies the predicate. Return false otherwise.
    Elements are checked in key order.

   [existsi p m] is like exists, except that the predicate p also takes the key
    as an argument.

   [all p m] checks the elements of a map m with a predicate p and return true
    if they all satisfy the predicate. Return false otherwise.  Elements
    are checked in key order.

   [alli p m] is like all, except that the predicate p also takes the key as an
    argument.

   [fromOrderedList ordr xs] returns a map that contains the (index, value)
    pairs in xs, whose keys have ordering ordr.  The list xs must be sorted by
    the keys w.r.t. the ordr and has no key duplications.

    NOTE: This function constructs the map in linear-time, but raises no error
    if the supplied xs is not ordered (the resulting map may lack some pairs).

*)
