(* Fnlib.sig *)

signature FNLIB =
sig

  val incr : int ref -> unit
  val decr : int ref -> unit
    (* increment and decrement an int ref *)

  val lookup : ''a -> (''a * 'b) list -> 'b
    (* map a key to a value using an association list.  Uses polymorphic
       equality to compare keys, which can be inefficient.
       Raises Subscript if key is not found. *)

  val for : (int -> unit) -> int -> int -> unit
    (* for f first last: if first <= last, apply f to each integer
       from first to last, for effect. *)

end (* signature FNLIB *)
