(* Author: Michael Norrish *)

structure Arbintcore :> Arbintcore =
struct

type num = Arbnumcore.num
type int = bool * num

(* representation has first component true if the integer is >= 0 *)

infix ++ -- ** <<
infix 7 ddiv mmod

val op ++ = Arbnumcore.+
val op -- = Arbnumcore.-
val op ** = Arbnumcore.*
val op << = Arbnumcore.<
val op ddiv = Arbnumcore.div
val op mmod = Arbnumcore.mod
val AZ = Arbnumcore.zero

val zero = (true, Arbnumcore.zero)
val one = (true, Arbnumcore.one)
val two = (true, Arbnumcore.two)

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
  | ((true, n1) div (false, n2)) = let val (q,r) = Arbnumcore.divmod(n1, n2)
                                   in if r <> Arbnumcore.zero then
                                        (false, q ++ Arbnumcore.one)
                                      else norm_zeros (false, q)
                                   end
  | ((false, n1) div (true, n2)) = let val (q,r) = Arbnumcore.divmod(n1, n2)
                                   in if r <> Arbnumcore.zero then
                                        (false, q ++ Arbnumcore.one)
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

fun toString (true, n) = Arbnumcore.toString n ^ "i"
  | toString (false, n) = "-" ^ Arbnumcore.toString n ^ "i"

fun fromString s = let
  open Substring
  val (pfx, rest) = splitl (fn c => c = #"-" orelse c = #"~") (full s)
  val is_positive = Int.mod(size pfx, 2) = 0
in
  (is_positive, Arbnumcore.fromString (string rest))
end

fun toInt (true, n) = Arbnumcore.toInt n
  | toInt (false, n) = Int.-(0, Arbnumcore.toInt n)
fun toNat (true, n) = n
  | toNat (false, _) = raise Fail "Attempt to make negative integer a nat"
fun fromInt n =
  if (Int.<(n,0)) then (false, Arbnumcore.fromInt(Int.-(0, n)))
  else (true, Arbnumcore.fromInt n)


fun min (i,j) = if i < j then i else j
fun max (i,j) = if i < j then j else i

fun abs (_, n) = (true, n)

fun fromNat n = (true, n)

end
