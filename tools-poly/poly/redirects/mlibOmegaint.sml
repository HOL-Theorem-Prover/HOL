(* Copyright (c) Michael Norrish *)

structure mlibOmegaint :> mlibOmegaint =
struct
  structure I = IntInf; local open IntInf in end;
  structure V = Vector; local open Vector in end;
  structure W = Word; local open Word in end;

  val zero = I.fromInt 0;
  val one = I.fromInt 1;
  val eq = op=;
  val == = eq
  infix ==

  (*
  fun hash n = 
    case M.rep n of
      M.Small w => w
    | M.Big v   =>
        let val k = W.toIntX (V.foldli (fn (_,w,acc) => w + acc) 0w0 (v,1,NONE))
        in if V.sub (v,0) = 0w0 then k else ~k
        end;
        *)


   (*------------------------------------------------------------------------*)
   (* Function to compute the Greatest Common Divisor of two integers.       *)
   (*------------------------------------------------------------------------*)

   (*
  fun hash n = 
    case M.rep n of
      M.Small w => w
    | M.Big v   =>
        let val k = W.toIntX (V.foldli (fn (_,w,acc) => w + acc) 0w0 (v,1,NONE))
        in if V.sub (v,0) = 0w0 then k else ~k
        end;
        *)
   fun hash n = n


   open I
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
