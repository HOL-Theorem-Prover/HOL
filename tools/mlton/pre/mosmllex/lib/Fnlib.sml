(* Fnlib.sml. Library functions *)

structure Fnlib : FNLIB =
struct

  (* increment and decrement int refs *)
  fun incr r = r := !r + 1
  fun decr r = r := !r - 1

  (* alist lookup function.  Uses polymorphic equality. *)
  fun lookup k [] = raise Subscript
    | lookup k ((a, v) :: xs) =
      if k = a then v else lookup k xs

  (* iterating a function over a range of integers *)
  fun for (f: int -> unit) i j =
      if i > j then () else (f i; for f (i+1) j)

end (* structure Fnlib *)
