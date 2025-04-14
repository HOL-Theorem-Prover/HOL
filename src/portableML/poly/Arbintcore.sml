(* Author: Michael Norrish *)

structure Arbintcore :> Arbintcore =
struct

open IntInf

type num = Arbnumcore.num

val zero = 0
val one = 1
val two = 2

fun toString x =
   (if x < 0
       then "-" ^ (IntInf.toString (~x))
    else IntInf.toString x) ^ "i"

fun fromString s =
   let
      open Substring
      val (pfx, rest) = splitl (fn c => c = #"-" orelse c = #"~") (full s)
      val is_positive = Int.mod (size pfx, 2) = 0
      val res = Arbnumcore.toLargeInt (Arbnumcore.fromString (string rest))
   in
      if is_positive then res else ~res
   end

val fromInt = IntInf.fromInt
fun fromLargeInt x = x
fun fromNat x = Arbnumcore.toLargeInt x
val toInt = IntInf.toInt
fun toLargeInt x = x
fun toNat x =
   if x < 0
      then raise Fail "Attempt to make negative integer a nat"
   else Arbnumcore.fromLargeInt x

val divmod = divMod
val quotrem = quotRem
fun negate x = ~x
fun sgn x = x >= 0

(* NOTE: gcd is always positive *)
fun gcd (a, b) = fromNat (Arbnumcore.gcd (toNat (abs a), toNat (abs b)))

(* previous version which returns negative values if x or y is negative:
local
  fun gxd x y =
    if y = zero then x else gxd y (x mod y)
in
  fun gcd (x, y) = if x < y then gxd y x else gxd x y
end
 *)

fun lcm (x, y) = (x * y) div gcd (x, y)

end
