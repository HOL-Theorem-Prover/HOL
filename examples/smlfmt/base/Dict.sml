(** Copyright (c) 2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

functor Dict
  (Key:
   sig
     type t
     val compare: t * t -> order
   end):
sig
  type 'a t
  type 'a dict = 'a t

  exception NotFound

  val empty: 'a dict
  val isEmpty: 'a dict -> bool
  val size: 'a dict -> int
  val singleton: Key.t * 'a -> 'a dict
  val insert: 'a dict -> (Key.t * 'a) -> 'a dict
  val lookup: 'a dict -> Key.t -> 'a
  val find: 'a dict -> Key.t -> 'a option
  val contains: 'a dict -> Key.t -> bool
  val remove: 'a dict -> Key.t -> 'a dict
  val fromList: (Key.t * 'a) list -> 'a dict
  val listKeys: 'a dict -> Key.t list

  val unionWith: ('a * 'a -> 'a) -> ('a dict * 'a dict) -> 'a dict
  val intersectWith: ('a * 'b -> 'c) -> ('a dict * 'b dict) -> 'c dict

(** below are other ORD_MAP functions that we could easily add if needed. *)
(*

  val singleton : (Key.ord_key * 'a) -> 'a map

  val insert  : 'a map * Key.ord_key * 'a -> 'a map
  val insert' : ((Key.ord_key * 'a) * 'a map) -> 'a map

  val insertWith  : ('a * 'a -> 'a) -> 'a map * Key.ord_key * 'a -> 'a map
  val insertWithi : (Key.ord_key * 'a * 'a -> 'a) -> 'a map * Key.ord_key * 'a -> 'a map

  val find : 'a map * Key.ord_key -> 'a option

  val lookup : 'a map * Key.ord_key -> 'a

  val inDomain : ('a map * Key.ord_key) -> bool

  val remove : 'a map * Key.ord_key -> 'a map * 'a

  val first : 'a map -> 'a option
  val firsti : 'a map -> (Key.ord_key * 'a) option

  val numItems : 'a map ->  int

  val listItems  : 'a map -> 'a list
  val listItemsi : 'a map -> (Key.ord_key * 'a) list

  val listKeys : 'a map -> Key.ord_key list

  val collate : ('a * 'a -> order) -> ('a map * 'a map) -> order

  val unionWith  : ('a * 'a -> 'a) -> ('a map * 'a map) -> 'a map
  val unionWithi : (Key.ord_key * 'a * 'a -> 'a) -> ('a map * 'a map) -> 'a map

  val intersectWith  : ('a * 'b -> 'c) -> ('a map * 'b map) -> 'c map
  val intersectWithi : (Key.ord_key * 'a * 'b -> 'c) -> ('a map * 'b map) -> 'c map

  val mergeWith : ('a option * 'b option -> 'c option)
        -> ('a map * 'b map) -> 'c map
  val mergeWithi : (Key.ord_key * 'a option * 'b option -> 'c option)
        -> ('a map * 'b map) -> 'c map

  val app  : ('a -> unit) -> 'a map -> unit
  val appi : ((Key.ord_key * 'a) -> unit) -> 'a map -> unit

  val map  : ('a -> 'b) -> 'a map -> 'b map
  val mapi : (Key.ord_key * 'a -> 'b) -> 'a map -> 'b map

  val foldl  : ('a * 'b -> 'b) -> 'b -> 'a map -> 'b
  val foldli : (Key.ord_key * 'a * 'b -> 'b) -> 'b -> 'a map -> 'b
  val foldr  : ('a * 'b -> 'b) -> 'b -> 'a map -> 'b
  val foldri : (Key.ord_key * 'a * 'b -> 'b) -> 'b -> 'a map -> 'b

  val filter  : ('a -> bool) -> 'a map -> 'a map
  val filteri : (Key.ord_key * 'a -> bool) -> 'a map -> 'a map

  val mapPartial  : ('a -> 'b option) -> 'a map -> 'b map
  val mapPartiali : (Key.ord_key * 'a -> 'b option) -> 'a map -> 'b map

  val exists : ('a -> bool) -> 'a map -> bool
  val existsi : (Key.ord_key * 'a -> bool) -> 'a map -> bool
  val all : ('a -> bool) -> 'a map -> bool
  val alli : (Key.ord_key * 'a -> bool) -> 'a map -> bool
*)
end =
struct
  structure M = RedBlackMapFn (struct open Key type ord_key = t end)

  exception NotFound = LibBase.NotFound

  type 'a t = 'a M.map
  type 'a dict = 'a t

  val empty = M.empty
  val isEmpty = M.isEmpty
  val size = M.numItems
  val singleton = M.singleton
  val unionWith = M.unionWith
  val intersectWith = M.intersectWith

  fun insert d (k, v) = M.insert (d, k, v)
  fun lookup d k = M.lookup (d, k)
  fun find d k = M.find (d, k)
  fun contains d k = M.inDomain (d, k)

  fun remove d k =
    #1 (M.remove (d, k))
    handle NotFound => d

  fun fromList kvs =
    List.foldl (fn ((k, v), d) => insert d (k, v)) empty kvs

  val listKeys = M.listKeys

end
