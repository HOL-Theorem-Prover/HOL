(* -------------------------------------------------------------------------
   Nat
   ------------------------------------------------------------------------- *)

structure Nat :> Nat =
struct
   val _ = Int.maxInt = NONE
           orelse raise Fail "Arbitrary precision arithmetic not available"

   type nat = int

   fun fromInt i = if i < 0 then raise Domain else i
   fun toInt i = i
   fun from_int i = if i < 0 then NONE else SOME i
   val fromString = Option.composePartial (from_int, IntExtra.fromString)
   val fromBinString = Option.composePartial (from_int, IntExtra.fromBinString)
   val fromHexString = Option.composePartial (from_int, IntExtra.fromHexString)
   val toString = Int.toString
   val toBinString = IntExtra.toBinString
   val toHexString = IntExtra.toHexString
   val toWord = Word.fromInt o toInt
   val fromLit = Option.map fromInt o IntExtra.fromLit

   val fromBool = fn true => 1 | false => 0

   val compare = Int.compare

   val zero = 0
   val one = 1
   val two = 2

   val log2 = IntInf.log2
   val pow = IntInf.pow

   val op div = op Int.div
   val op mod = op Int.mod
   val op + = op Int.+
   val op * = op Int.*
   val op < = op Int.<
   val op <= = op Int.<=
   val op > = op Int.>
   val op >= = op Int.>=

   fun op - (x, y) =
     let
        val r = Int.- (x, y)
     in
        if r < 0 then 0 else r
     end

   fun suc n = n + one
   fun pred n = n - one

   fun min (a, b) = if a < b then a else b
   fun max (a, b) = if a < b then b else a
end (* structure Nat *)
