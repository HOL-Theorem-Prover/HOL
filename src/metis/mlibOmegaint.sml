structure mlibOmegaint :> mlibOmegaint =
struct
  structure I = Arbint; local open Arbint in end;

  val zero = I.fromInt 0;
  val one = I.fromInt 1;
  val eq = op=

  fun hash n = I.toInt n


  open I
  fun ERR f s = raise Fail ("Function: "^f^", message: "^s)

  (*------------------------------------------------------------------------*)
  (* Function to compute the Greatest Common Divisor of two integers.       *)
  (*------------------------------------------------------------------------*)

  fun gcd' i j = let
    val r = i mod j
  in  if r = zero then j else gcd' j r
  end

  fun gcd (i,j) =
      if i < zero orelse j < zero then ERR "gcd" "negative arguments to gcd"
      else if i = zero then j else if j = zero then i
      else if i < j then gcd' j i else gcd' i j

  val fromString = Lib.total fromString

end
