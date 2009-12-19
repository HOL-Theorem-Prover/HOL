(* Author: Michael Norrish *)

(* very simple-minded implementation of arbitrary precision natural
   numbers *)

   (* use "Arbnumcore.sig"; use "Arbnumcore.sml"; *)

structure Arbnumcore :> Arbnumcore =
struct

open IntInf

type num = int

val zero = 0
val one = 1
val two = 2

fun times2 x = 2 * x
fun div2 x = x div 2
fun mod2 x = x mod 2

fun plus1 x = x + 1
fun plus2 x = x + 2
fun less1 x =
  if x = 0 then 
    raise Fail "Can't take one off zero"
  else 
    x - 1
fun less2 x = 
  if x < 2 then
   raise Fail "Can't take one off zero"
  else
   x - 2 

fun toBinString x = fmt StringCvt.BIN x
fun toOctString x = fmt StringCvt.OCT x
fun toHexString x = fmt StringCvt.HEX x
 
(*
  val fromString  : string -> num (* decimal *)
  val genFromString : StringCvt.radix -> string -> num
  val fromHexString : string -> num
  val fromOctString : string -> num
  val fromBinString : string -> num
  *)  

fun intexp(base,exponent) = let
  fun recurse acc b n =
      if Int.<=(n,0) then acc
      else if Int.mod(n,2) = 1 then
        recurse (Int.*(acc, b)) b (Int.-(n,1))
      else recurse acc (Int.*(b,b)) (Int.div(n,2))
in
  recurse 1 base exponent
end

fun genFromString rdx = let
  open StringCvt
  val (base, chunksize, chunkshift) =
      case rdx of
        BIN => (2, 10, fromInt 1024)
      | OCT => (8, 5, fromInt 32768)
      | DEC => (10, 5, fromInt 100000)
      | HEX => (16, 5, fromInt 1048576)
  val scanner = Int.scan rdx
  fun readchunk s = StringCvt.scanString scanner s
  fun recurse acc s = let
    val sz = size s
  in
    if Int.<=(sz, chunksize) then
      fromInt (intexp(base,sz)) * acc + fromInt (valOf (readchunk s))
    else let
        val sz_less_cs = Int.-(sz, chunksize)
        val pfx = substring(s, 0, chunksize)
        val sfx = String.extract(s, chunksize, NONE)
      in
        recurse (chunkshift * acc + fromInt (valOf (readchunk pfx))) sfx
      end
  end
in
  recurse zero
end handle Option => raise Fail "String not numeric"
val fromHexString = genFromString StringCvt.HEX
val fromOctString = genFromString StringCvt.OCT
val fromBinString = genFromString StringCvt.BIN
val fromString = genFromString StringCvt.DEC

local
  fun toChar n =
      str (if Int.<(n, 10)
           then chr (Int.+(ord #"0", n))
           else chr (Int.-(Int.+(ord #"A", n), 10)))
  fun toBaseString base n =
    let val (q,r) = divMod(n, base)
        val s = toChar (toInt r)
  in
    if q = zero then s else toBaseString base q^s
  end
in
  val toBinString = toBaseString (fromInt 2)
  val toOctString = toBaseString (fromInt 8)
  val toHexString = toBaseString (fromInt 16)
end


fun fromInt n =
  if n < 0 then
    raise Overflow
  else
    n

fun toInt x = x

fun floor x =
let val y = Real.floor x in
  if y < 0 then
    raise Overflow
  else
    y
end

val toReal = Real.fromInt

fun asList x = [x]

fun (x - y) = 
  if x < y then 
    0 
  else
    IntInf.-(x, y)

val divmod = divMod

local
  fun gcd' i j = let
    val r = i mod j
  in
    if r = 0 then j else gcd' j r
  end
in
fun gcd(i,j) = if i = 0 then j
               else if j = 0 then i
               else if i < j then gcd' j i
               else gcd' i j
end

end
