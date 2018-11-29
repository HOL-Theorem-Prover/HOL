(*  Title:      Pure/General/alist.ML
    Author:     Florian Haftmann, TU Muenchen

Association lists -- lists of (key, value) pairs.
*)

signature AList =
sig
  exception DUP
  val lookup: ('a * 'b -> bool) -> ('b * 'c) list -> 'a -> 'c option
  val defined: ('a * 'b -> bool) -> ('b * 'c) list -> 'a -> bool
  val update: ('a * 'a -> bool) -> ('a * 'b)
    -> ('a * 'b) list -> ('a * 'b) list
  val default: ('a * 'a -> bool) -> ('a * 'b)
    -> ('a * 'b) list -> ('a * 'b) list
  val delete: ('a * 'b -> bool) -> 'a
    -> ('b * 'c) list -> ('b * 'c) list
  val map_entry: ('a * 'b -> bool) -> 'a -> ('c -> 'c)
    -> ('b * 'c) list -> ('b * 'c) list
  val map_entry_yield: ('a * 'b -> bool) -> 'a -> ('c -> 'd * 'c)
    -> ('b * 'c) list -> 'd option * ('b * 'c) list
  val map_default: ('a * 'a -> bool) -> 'a * 'b -> ('b -> 'b)
    -> ('a * 'b) list -> ('a * 'b) list
  val join: ('a * 'a -> bool) -> ('a -> 'b * 'b -> 'b) (*exception DUP*)
    -> ('a * 'b) list * ('a * 'b) list -> ('a * 'b) list    (*exception DUP*)
  val merge: ('a * 'a -> bool) -> ('b * 'b -> bool)
    -> ('a * 'b) list * ('a * 'b) list -> ('a * 'b) list    (*exception DUP*)
  val make: ('a -> 'b) -> 'a list -> ('a * 'b) list
  val find: ('a * 'b -> bool) -> ('c * 'b) list -> 'a -> 'c list
  val coalesce: ('a * 'a -> bool) -> ('a * 'b) list -> ('a * 'b list) list
    (*coalesce ranges of equal neighbour keys*)
  val group: ('a * 'a -> bool) -> ('a * 'b) list -> ('a * 'b list) list
end;
