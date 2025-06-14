(** Copyright (c) 2022 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

functor Set
  (Key:
   sig
     type t
     val compare: t * t -> order
   end):
sig
  type t
  type set = t

  exception NotFound

  val empty: set
  val isEmpty: set -> bool
  val size: set -> int
  val singleton: Key.t -> set
  val insert: set -> Key.t -> set
  val contains: set -> Key.t -> bool
  val remove: set -> Key.t -> set
  val fromList: Key.t list -> set
  val listKeys: set -> Key.t list
  val union: set * set -> set
  val intersect: set * set -> set
end =
struct
  structure D = Dict(Key)
  open D

  type set = unit D.t
  type t = set

  fun insert s x = D.insert s (x, ())
  fun singleton x = D.singleton (x, ())
  fun fromList xs =
    D.fromList (List.map (fn x => (x, ())) xs)
  fun union (s, t) =
    D.unionWith (fn _ => ()) (s, t)
  fun intersect (s, t) =
    D.intersectWith (fn _ => ()) (s, t)
end
