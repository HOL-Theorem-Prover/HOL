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
fun less1 x = if x = 0 then raise Fail "Can't take one off zero" else x - 1
fun less2 x = if x < 2 then raise Fail "Can't take one off zero" else x - 2

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

local
   val radix = fn StringCvt.HEX => "HEX"
                | StringCvt.OCT => "OCT"
                | StringCvt.BIN => "BIN"
                | StringCvt.DEC => "DEC"
   fun err rdx = Fail ("String not " ^ radix rdx)
in
   fun genFromString rdx s =
      case Int.scan rdx Substring.getc (Substring.full s) of
         SOME (i, r) => if Substring.size r = 0 then i else raise (err rdx)
       | _ => raise (err rdx)
   val fromHexString = genFromString StringCvt.HEX
   val fromOctString = genFromString StringCvt.OCT
   val fromBinString = genFromString StringCvt.BIN
   val fromString = genFromString StringCvt.DEC
end

fun fromInt n = if n < 0 then raise Overflow else n

fun toInt x = x

fun floor x =
   let
      val y = Real.floor x
   in
      if y < 0 then raise Overflow else y
   end

val toReal = Real.fromInt

fun asList x = [x]

fun (x - y) = if x < y then 0 else IntInf.- (x, y)

val divmod = divMod

local
   fun gcd' i j =
      let
         val r = i mod j
      in
         if r = 0 then j else gcd' j r
      end
in
   fun gcd (i, j) =
      if i = 0
         then j
      else if j = 0
         then i
      else if i < j
         then gcd' j i
      else gcd' i j
end

(* Basic Integer square root *)

fun isqrt n =
   if n < two
      then n
   else let
           fun iter a =
              let
                 val a2 = a * a
              in
                 if a2 <= n andalso n <= a2 + times2 a
                    then a
                 else iter (div2 ((a2 + n) div a))
              end
        in
           iter one
        end

end
