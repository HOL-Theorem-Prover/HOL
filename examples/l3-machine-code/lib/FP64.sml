(* -------------------------------------------------------------------------
   Floating-point
   ------------------------------------------------------------------------- *)

structure FP64 :> FP =
struct

   structure R = Real
   structure P = PackRealLittle (* must be little-endian structure *)

   type ieee_flags = {DivideByZero: bool,
                      InvalidOp: bool,
                      Overflow: bool,
                      Precision: bool,
                      Underflow: bool}

   local
     val bytes = Word8Vector.length (P.toBytes R.posInf)
   in
     val size = 8 * bytes
     val byte = Word8.fromLargeInt o BitsN.toNat o L3.uncurry BitsN.bits
     fun unbyte b = BitsN.fromNat (Word8.toLargeInt b, 8)
     fun fromBits w =
       ( IntInf.toInt (BitsN.size w) = size orelse
         raise Fail ("fromBits: not " ^ Int.toString size ^ "-bit word")
       ; (P.fromBytes o Word8Vector.fromList)
           (List.tabulate
             (bytes, fn i => let
                                val j = 8 * IntInf.fromInt i
                             in
                                byte ((j + 7, j), w)
                             end))
       )
     fun toBits r =
       let
         val v = P.toBytes r
         val l = List.tabulate
                   (bytes, fn i => unbyte (Word8Vector.sub (v, bytes - 1 - i)))
       in
         BitsN.concat l
       end
   end

   val posInf = toBits R.posInf
   val negInf = toBits R.negInf
   val posZero = toBits (Option.valOf (R.fromString "0.0"))
   val negZero = toBits (Option.valOf (R.fromString "-0.0"))
   val qNan = BitsN.fromInt (0x7FF8000000000000, 64)
   val sNan = BitsN.fromInt (0x7FF0000000000001, 64)

   fun withMode m f x =
     let
       val m0 = IEEEReal.getRoundingMode ()
     in
        IEEEReal.setRoundingMode m
      ; f x before IEEEReal.setRoundingMode m0
     end

   fun toInt (m, w) =
     let
       val r = fromBits w
     in
       if R.isFinite r then SOME (R.toLargeInt m r) else NONE
     end

   fun fromInt (m, i) = toBits (withMode m R.fromLargeInt i)
   val fromString = Option.map toBits o R.fromString

   val isNan = R.isNan o fromBits
   val isFinite = R.isFinite o fromBits
   val isNormal = R.isNormal o fromBits
   fun isSignallingNan a = isNan a andalso not (BitsN.bit (a, 51))
   fun isSubnormal a = R.class (fromBits a) = IEEEReal.SUBNORMAL
   fun isIntegral a =
     let
       val r = fromBits a
     in
       R.isFinite r andalso R.== (R.realTrunc r, r)
     end

   local
     val dummy_flags =
       {DivideByZero = false, InvalidOp = false, Overflow = false,
        Precision = false, Underflow = false}
     fun fromBits2 (a, b) = (fromBits a, fromBits b)
     fun fpOp from f (m, a) =
       ((fn a => (dummy_flags, toBits a)) o withMode m f o from) a
     fun fpOp0 f = toBits o f o fromBits
     val fpOp1 = fpOp fromBits
     val fpOp2 = fpOp fromBits2
     val fpOp3 = fpOp (fn (a, (b, c)) => (fromBits a, fromBits b, fromBits c))
     val sign_bit = BitsN.#>> (BitsN.B (1, IntInf.fromInt size), 1)
     val comp_sign_bit = BitsN.~ sign_bit
   in
     val abs = fpOp0 R.abs
     val neg = fpOp0 R.~
     val sqrt = fpOp1 R.Math.sqrt

     val add = fpOp2 R.+
     val mul = fpOp2 R.*
     val sub = fpOp2 R.-
     val op div = fpOp2 R./

     val equal = R.== o fromBits2
     val compare = R.compareReal o fromBits2
     val greaterThan = R.> o fromBits2
     val greaterEqual = R.>= o fromBits2
     val lessThan = R.< o fromBits2
     val lessEqual = R.<= o fromBits2

     val mul_add = fpOp3 R.*+
     val mul_sub = fpOp3 R.*-

     val roundToIntegral =
       fn (IEEEReal.TO_NEGINF, a) => fpOp0 R.realFloor a
        | (IEEEReal.TO_POSINF, a) => fpOp0 R.realCeil a
        | (IEEEReal.TO_ZERO, a) => fpOp0 R.realTrunc a
        | (IEEEReal.TO_NEAREST, a) => fpOp0 R.realRound a
   end

end (* functor FP *)
