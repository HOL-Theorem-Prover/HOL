(* Copyright (c) Michael Norrish *)

structure mlibOmegaint :> mlibOmegaint =
struct
   open mlibArbint
   val eq = op=
   val == = eq
   infix ==
   val fromString = SOME o fromString

   val hash = Polyhash.hash

   (*------------------------------------------------------------------------*)
   (* Function to compute the Greatest Common Divisor of two integers.       *)
   (*------------------------------------------------------------------------*)

   fun ERR f s = raise Fail ("Function: "^f^", message: "^s)

   fun gcd' i j = let
       val r = i mod j
   in  if r == zero then j else gcd' j r
   end

   fun gcd (i,j) =
       if i < zero orelse j < zero then ERR "gcd""negative arguments to gcd"
       else if i == zero then j else if j == zero then i
                                else if i < j then gcd' j i else gcd' i j
end
