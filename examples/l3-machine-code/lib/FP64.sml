(* -------------------------------------------------------------------------
   Floating-point
   ------------------------------------------------------------------------- *)

structure FP64 :> FP =
struct

   structure R = Real
   structure P = PackRealLittle (* must be little-endian structure *)

   local
     val bytes = Word8Vector.length (P.toBytes R.posInf)
   in
     val size = 8 * bytes
     val byte = Word8.fromInt o BitsN.toNat o L3.uncurry BitsN.bits
     fun unbyte b = BitsN.fromNat (Word8.toInt b, 8)
     fun fromBits w =
       ( BitsN.size w = size orelse
         raise Fail ("fromBits: not " ^ Int.toString size ^ "-bit word")
       ; (P.fromBytes o Word8Vector.fromList)
           (List.tabulate
             (bytes, fn i => let val j = 8 * i in byte ((j + 7, j), w) end))
       )
     fun toBits r =
       let
         val v = P.toBytes r
         val l = List.tabulate
                   (bytes, fn i => unbyte (Word8Vector.sub (v, bytes - 1 - i)))
       in
         BitsN.concat l
       end
     val toLargeReal = R.toLarge o fromBits
     fun fromLargeReal m r = toBits (R.fromLarge m r)
   end

   val posInf = toBits R.posInf
   val negInf = toBits R.negInf
   val posZero = toBits (Option.valOf (R.fromString "0.0"))
   val negZero = toBits (Option.valOf (R.fromString "-0.0"))

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
       if R.isFinite r then SOME (R.toInt m r) else NONE
     end

   fun fromInt (m, i) = toBits (withMode m R.fromInt i)
   val fromString = Option.map toBits o R.fromString
   val toString = R.fmt StringCvt.EXACT o fromBits

   val isNan = R.isNan o fromBits
   val isFinite = R.isFinite o fromBits
   val isNormal = R.isNormal o fromBits
   fun isSubnormal a = R.class (fromBits a) = IEEEReal.SUBNORMAL

   local
     fun fpOp f (a, b) = f (fromBits a, fromBits b)
     fun fpOp1 f = toBits o f o fromBits
     fun fpOp2 f (m, a) = toBits (withMode m (fpOp f) a)
     val sign_bit = BitsN.#>> (BitsN.B (1, size), 1)
     val comp_sign_bit = BitsN.~ sign_bit
   in
     (* native versions - could be IEEE:1985 or IEEE:2008 *)
     val abs = fpOp1 R.abs
     val neg = fpOp1 R.~

     (* IEEE754:1985 says that the sign bit of a NaN is left unchanged *)
     fun abs1985 x =
       let
         val r = fromBits x
       in
         if R.isNan r then x else toBits (R.abs r)
       end

     (* IEEE754:2008 says that the sign bit of a NaN is cleared *)
     fun abs2008 x =
       let
         val r = fromBits x
       in
         if R.isNan r then BitsN.&& (x, comp_sign_bit) else toBits (R.abs r)
       end

     (* IEEE754:1985 says that the sign bit of a NaN is left unchanged *)
     fun neg1985 x =
       let
         val r = fromBits x
       in
         if R.isNan r then x else toBits (R.~ r)
       end

     (* IEEE754:2008 says that the sign bit of a NaN is flipped *)
     fun neg2008 x =
       let
         val r = fromBits x
       in
         if R.isNan r then BitsN.?? (x, sign_bit) else toBits (R.~ r)
       end

     val add = fpOp2 R.+
     val mul = fpOp2 R.*
     val sub = fpOp2 R.-
     val op div = fpOp2 R./

     fun sqrt (m, a) = toBits (withMode m R.Math.sqrt (fromBits a))

     val equal = fpOp R.==
     val compare = fpOp R.compareReal
     val greaterThan = fpOp R.>
     val greaterEqual = fpOp R.>=
     val lessThan = fpOp R.<
     val lessEqual = fpOp R.<=

   end

end (* structure FP64 *)
