(* Dynarray -- polymorphic dynamic arrays a la SML/NJ library *)

signature Dynarray =
sig

type 'a array

val array    : int * '_a -> '_a array
val subArray : '_a array * int * int -> '_a array
val fromList : '_a list * '_a -> '_a array
val tabulate : int * (int -> '_a) * '_a -> '_a array
val sub      : 'a array * int -> 'a
val update   : '_a array * int * '_a  -> unit
val default  : 'a array -> 'a
val bound    : 'a array -> int

end

(*
   ['ty array] is the type of one-dimensional, mutable, zero-based
   unbounded arrays with elements of type 'ty.  Type 'ty array does
   not admit equality.

   [array(n, d)] returns a dynamic array, all of whose elements are
   initialized to the default d.  The parameter n is used as a hint of the
   upper bound on non-default elements.  Raises Size if n < 0.

   [subArray(a, m, n)] returns a new array with the same default
   value as a, and whose values in the range [0,n-m] equal the
   values in a in the range [m,n].  Raises the exception Size if n < m.

   [fromList (xs, d)] returns an array whose first elements are
   those of [xs], and the rest are the default d.

   [tabulate(n, f, d)] returns a new array whose first n elements
   are f 0, f 1, ..., f (n-1), created from left to right, and whose
   remaining elements are the default d.  Raises Size if n < 0.

   [sub(a, i)] returns the i'th element of a, counting from 0.
   Raises Subscript if i < 0.

   [update(a, i, x)] destructively replaces the i'th element of a by x.
   Raises Subscript if i < 0.

   [default a] returns the default value of the array a.

   [bound a] returns an upper bound on the indices of non-default values.
*)
