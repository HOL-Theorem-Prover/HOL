(* Author: Michael Norrish *)

structure mlibBigint :> mlibBigint =
struct

type num = mlibBignum.num
type int = bool * num

(* representation has first component true if the integer is >= 0 *)

infix ++ -- ** <<
infix 7 ddiv mmod

val op ++ = mlibBignum.+
val op -- = mlibBignum.-
val op ** = mlibBignum.*
val op << = mlibBignum.<
val op ddiv = mlibBignum.div
val op mmod = mlibBignum.mod
val AZ = mlibBignum.zero

val zero = (true, mlibBignum.zero)
val one = (true, mlibBignum.one)
val two = (true, mlibBignum.two)

fun norm_zeros (i as (b,n)) = if not b andalso n = AZ then (true, AZ) else i

fun ((true, n1) + (true, n2)) = (true, n1 ++ n2)
  | ((true, n1) + (false, n2)) = if n1 << n2 then (false, n2 -- n1) else (true, n1 -- n2)
  | ((false, n1) + (true, n2)) = if n2 << n1 then (false, n1 -- n2) else (true, n2 -- n1)
  | ((false, n1) + (false, n2)) = (false, n1 ++ n2)

fun negate (true, n) = if n = AZ then (true, n) else (false, n)
  | negate (false, n) = (true, n)
val op~ = negate

fun i - j = i + negate j

fun ((true, n1) * (true, n2)) = (true, n1 ** n2)
  | ((true, n1) * (false, n2)) = if n1 = AZ then (true, AZ) else (false, n1 ** n2)
  | ((false, n1) * (true, n2)) = if n2 = AZ then (true, AZ) else (false, n1 ** n2)
  | ((false, n1) * (false, n2)) = (true, n1 ** n2)

fun ((true, n1) div (true, n2)) = (true, n1 ddiv n2)
  | ((true, n1) div (false, n2)) = let val (q,r) = mlibBignum.divmod(n1, n2)
                                   in if r <> mlibBignum.zero then
                                        (false, q ++ mlibBignum.one)
                                      else norm_zeros (false, q)
                                   end
  | ((false, n1) div (true, n2)) = let val (q,r) = mlibBignum.divmod(n1, n2)
                                   in if r <> mlibBignum.zero then
                                        (false, q ++ mlibBignum.one)
                                      else norm_zeros (false, q)
                                   end
  | ((false, n1) div (false, n2)) = (true, n1 ddiv n2)

fun ((true, n1) mod (true, n2)) = (true, n1 mmod n2)
  | ((true, n1) mod (false, n2)) = let val m = n1 mmod n2
                                   in
                                     if m = AZ then zero else (false, n2 -- m)
                                   end
  | ((false, n1) mod (true, n2)) = let val m = n1 mmod n2
                                   in
                                     if m = AZ then zero else (true, n2 -- m)
                                   end
  | ((false, n1) mod (false, n2)) = norm_zeros (false, n1 mmod n2)

infix 7 quot rem

fun ((true, n1) quot (true, n2)) = (true, n1 ddiv n2)
  | ((true, n1) quot (false, n2)) = norm_zeros (false, n1 ddiv n2)
  | ((false, n1) quot (true, n2)) = norm_zeros (false, n1 ddiv n2)
  | ((false, n1) quot (false, n2)) = (true, n1 ddiv n2)

fun ((true, n1) rem (true, n2)) = (true, n1 mmod n2)
  | ((true, n1) rem (false, n2)) = norm_zeros (false, n1 mmod n2)
  | ((false, n1) rem (true, n2)) = norm_zeros (false, n1 mmod n2)
  | ((false, n1) rem (false, n2)) = (true, n1 mmod n2)

fun quotrem(i,j) = (i quot j, i rem j)

fun (true, n1) < (true, n2) = n1 << n2
  | (true, _) < (false, _) = false
  | (false, _) < (true, _) = true
  | (false, n1) < (false, n2) = n2 << n1
fun i <= j = i = j orelse i < j
fun i > j = j < i
fun i >= j = i = j orelse i > j

fun compare(i,j) = if i < j then LESS
                   else if i = j then EQUAL
                        else GREATER

fun divmod (i, j) = (i div j, i mod j)

fun toString (true, n) = mlibBignum.toString n ^ "i"
  | toString (false, n) = "-" ^ mlibBignum.toString n ^ "i"

fun fromString s = let
  open Substring
  val (pfx, rest) = splitl (fn c => c = #"-" orelse c = #"~") (all s)
  val is_positive = Int.mod(size pfx, 2) = 0
in
  (is_positive, mlibBignum.fromString (string rest))
end

fun toInt (true, n) = mlibBignum.toInt n
  | toInt (false, n) = Int.-(0, mlibBignum.toInt n)
fun toNat (true, n) = n
  | toNat (false, _) = raise Fail "Attempt to make negative integer a nat"
fun fromInt n =
  if (Int.<(n,0)) then (false, mlibBignum.fromInt(Int.-(0, n)))
  else (true, mlibBignum.fromInt n)


fun min (i,j) = if i < j then i else j
fun max (i,j) = if i < j then j else i

fun abs (_, n) = (true, n)

fun fromNat n = (true, n)

end
