(* -------------------------------------------------------------------------
   Floating-point
   ------------------------------------------------------------------------- *)

structure FP64 :> FP64 =
struct

   val byte = Word8.fromInt o BitsN.toNat o BitsN.bits
   fun unbyte b = BitsN.fromNat (Word8.toInt b, 8)

   fun bitsToReal w =
      ( BitsN.size w = 64 orelse raise Fail "bitsToReal: not 64-bit word"
      ; (PackRealBig.fromBytes o Word8Vector.fromList o List.rev)
          (List.tabulate
             (8, fn i => let val j = 8 * i in byte (w, j + 7, j) end))
      )

   fun realToBits r =
      let
         val v = PackRealBig.toBytes r
         val _ = Word8Vector.length v = 8 orelse
                 raise Fail "realToBits: not 64-bit real"
         val l = List.tabulate (8, fn i => unbyte (Word8Vector.sub (v, 7 - i)))
      in
         List.foldl BitsN.@@ (hd l) (tl l)
      end

    fun fpOp f (a, b) = f (bitsToReal a, bitsToReal b)
    fun fpOp1 f = realToBits o f o bitsToReal
    fun fpOp2 f (m, a) = (IEEEReal.setRoundingMode m; realToBits (fpOp f a))

    val isNan = LargeReal.isNan o bitsToReal

    val abs = fpOp1 LargeReal.abs
    val neg = fpOp1 LargeReal.~
    val add = fpOp2 LargeReal.+
    val mul = fpOp2 LargeReal.*
    val sub = fpOp2 LargeReal.-

    val equal = fpOp LargeReal.==
    val lessThan = fpOp LargeReal.<

    val fromString = Option.map realToBits o LargeReal.fromString

end (* structure FP64 *)
