structure Arbrat :> Arbrat =
struct

(* representation is a reduced pair of int and num *)

type num = Arbnum.num
type aint = Arbint.int
type rat = aint * num

fun norm (n,d) = let
  val n' = Arbint.toNat (Arbint.abs n)
  val g = Arbnum.gcd(n',d)
in
  if g = Arbnum.one then (n,d)
  else
    (Arbint.div (n, Arbint.fromNat g), Arbnum.div (d, g))
end

fun fromAInt i = (i, Arbnum.one)
fun fromNat n = fromAInt (Arbint.fromNat n)
fun fromInt i = fromAInt (Arbint.fromInt i)

val zero = fromInt 0
val one = fromInt 1
val two = fromInt 2

fun numerator (n,d) = n
fun denominator (n,d) = d

fun toString (n,d) = Arbint.toString n ^ "/" ^ Arbnum.toString d
fun fromString s = fromAInt (Arbint.fromString s)

fun toAInt (n,d) = if d = Arbnum.one then n
                   else raise Fail "Arbrat.toAInt: not integral"
fun toInt r = Arbint.toInt (toAInt r)
fun toNat r = Arbint.toNat (toAInt r)

fun (n1,d1) + (n2,d2) =
    norm (Arbint.+(Arbint.*(n1,Arbint.fromNat d2),
                   Arbint.*(n2,Arbint.fromNat d1)),
          Arbnum.*(d1, d2))
fun (n1,d1) * (n2,d2) =
    norm (Arbint.*(n1,n2), Arbnum.*(d1,d2))
fun ~(n,d) = (Arbint.~ n, d)
val negate = ~
fun inv (n,d) =
    if n = Arbint.zero then raise Fail "inv: arg = 0"
    else ((if Arbint.<(n,Arbint.zero) then Arbint.~ (Arbint.fromNat d)
           else Arbint.fromNat d),
          Arbint.toNat (Arbint.abs n))

fun r1 - r2 = r1 + ~r2
fun r1 / r2 = r1 * inv r2

fun abs(n,d) = (Arbint.abs n, d)

fun (n1,d1) < (n2,d2) = Arbint.<(Arbint.*(n1,Arbint.fromNat d2),
                                 Arbint.*(n2,Arbint.fromNat d1))

fun r1 <= r2 = r1 < r2 orelse r1 = r2
fun r1 > r2 = r2 < r1
fun r1 >= r2 = r2 <= r1

fun floor (n,d) = let
  val di = Arbint.fromNat d
  open Arbint
in
  if di = one then n
  else if n < zero then
    ~(abs(n) div di + one)
  else n div di
end
fun ceil r = Arbint.~ (floor (~r))



fun compare (r1, r2) =
    if r1 = r2 then EQUAL
    else if r1 < r2 then LESS
    else GREATER

fun min(r1,r2) = if r1 < r2 then r1 else r2
fun max(r1,r2) = if r1 > r2 then r1 else r2

fun pp_rat pps r = HOLPP.add_string pps (toString r)


end
