type num = arbnum.num
type int = bool * num

val ++ = arbnum.+
val -- = arbnum.-
val ** = arbnum.*
val << = arbnum.<
val ddiv = arbnum.div
val mmod = arbnum.mod
val AZ = arbnum.zero

infix ++ -- ** << ddiv mmod

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
  | ((true, n1) div (false, n2)) = if n1 = AZ then (true, AZ)
                                   else (false, n1 ddiv n2)
  | ((false, n1) div (true, n2)) = (false, n1 ddiv n2)
  | ((false, n1) div (false, n2)) = (true, n1 ddiv n2)

fun ((true, n1) mod (true, n2)) = (true, n1 mmod n2)
  | ((true, n1) mod (false, n2)) = if n1 = AZ then (true, AZ)
                                   else (false, n1 mmod n2)
  | ((false, n1) mod (true, n2)) = (true, n1 mmod n2)
  | ((false, n1) mod (false, n2)) = (false, n1 mmod n2)

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

fun toString (true, n) = arbnum.toString n ^ "i"
  | toString (false, n) = "-" ^ arbnum.toString n ^ "i"

fun fromString s = let
  open Substring
  val (pfx, rest) = splitl (fn c => c = #"-") (all s)
  val neg = Int.mod(size pfx, 2) = 1
in
  (neg, arbnum.fromString (string rest))
end

fun toInt (true, n) = arbnum.toInt n
  | toInt (false, n) = Int.-(0, arbnum.toInt n)
fun toNat (true, n) = n
  | toNat (false, _) = raise Fail "Attempt to make negative integer a nat"
fun fromInt n =
  if (Int.<(n,0)) then (false, arbnum.fromInt(Int.-(0, n)))
  else (true, arbnum.fromInt n)


val zero = (true, arbnum.zero)
val one = (true, arbnum.one)
val two = (true, arbnum.two)

fun abs (_, n) = (true, n)

fun fromNat n = (true, n)

