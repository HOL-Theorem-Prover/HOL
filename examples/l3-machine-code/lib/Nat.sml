(* -------------------------------------------------------------------------
   Nat
   ------------------------------------------------------------------------- *)

structure Nat :> Nat =
struct
   val _ = IntInf.maxInt = NONE
           orelse raise Fail "Arbitrary precision arithmetic not available"

   type nat = IntInf.int

   fun fromInt i = if i < 0 then raise Domain else i
   fun toInt i = i
   val fromNativeInt = IntInf.fromInt
   val toNativeInt = IntInf.toInt
   fun from_int i = if i < 0 then NONE else SOME i
   val fromString = Option.composePartial (from_int, IntExtra.fromString)
   val fromBinString = Option.composePartial (from_int, IntExtra.fromBinString)
   val fromHexString = Option.composePartial (from_int, IntExtra.fromHexString)
   val toString = IntInf.toString
   val toBinString = IntExtra.toBinString
   val toHexString = IntExtra.toHexString
   val toWord = Word.fromLargeInt o toInt
   val fromLit = Option.map fromInt o IntExtra.fromLit

   val fromBool = fn true => 1 | false => 0: IntInf.int

   val compare = IntInf.compare

   val zero = 0: IntInf.int
   val one = 1: IntInf.int
   val two = 2: IntInf.int

   val log2 = IntInf.fromInt o IntInf.log2
   fun pow (x, y) = IntInf.pow (x, IntInf.toInt y)

   val op div = op IntInf.div
   val op mod = op IntInf.mod
   val op + = op IntInf.+
   val op * = op IntInf.*
   val op < = op IntInf.<
   val op <= = op IntInf.<=
   val op > = op IntInf.>
   val op >= = op IntInf.>=

   fun op - (x, y) =
     let
        val r = IntInf.- (x, y)
     in
        if r < 0 then 0 else r
     end

   fun suc n = n + one
   fun pred n = n - one

   fun min (a, b) = if a < b then a else b
   fun max (a, b) = if a < b then b else a
end (* structure Nat *)
