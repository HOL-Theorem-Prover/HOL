(*==========================================================================*)
(* Build structure for the ML type of natural numbers                       *)
(*==========================================================================*)

structure NumType :> NumType =
struct

open Exception

fun failwith function = raise HOL_ERR{origin_structure = "NumType",
                                      origin_function = function,
                                      message = ""};
type num = arbint.int;
val num0 = arbint.zero
val num1 = arbint.one


(*--------------------------------------------------------------------------*)
(* Function to compute the Greatest Common Divisor of two integers.         *)
(*--------------------------------------------------------------------------*)

fun gcd (i,j) = let
  open arbint
  exception non_neg
  fun gcd' (i,j) = let
    val r = (i mod j)
  in
    if (r = num0) then j
    else gcd' (j,r)
  end
in
  (if ((i < num0) orelse (j < num0)) then raise non_neg
  else
     if (i < j) then gcd' (j,i) else gcd' (i,j)
       ) handle non_neg => failwith "gcd"
     | Portable_Int.Mod => failwith "gcd"
end;

(*--------------------------------------------------------------------------*)
(* Function to compute the Lowest Common Multiple of two integers.          *)
(*--------------------------------------------------------------------------*)

fun lcm (i,j) = let
  open arbint
in
  (i * j) div (gcd (i,j))
end
  handle HOL_ERR _ => failwith "lcm"
       | General.Div => failwith "lcm";

val op*    = arbint.*
val op-    = arbint.-
val op+    = arbint.+
val op div = arbint.div
val op<    = arbint.<

(*--------------------------------------------------------------------------*)
(* Make the definitions                                                     *)
(*--------------------------------------------------------------------------*)

end; (* NumType *)
