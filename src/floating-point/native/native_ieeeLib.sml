structure native_ieeeLib :> native_ieeeLib =
struct

open HolKernel Parse boolLib bossLib
open realLib wordsLib binary_ieeeLib binary_ieeeSyntax

structure Parse =
struct
  open Parse
  val (Type, Term) =
     parse_from_grammars binary_ieeeTheory.binary_ieee_grammars
end
open Parse

val ERR = Feedback.mk_HOL_ERR "native_ieeeLib"

(* -------------------------------------------------------------------------
   numToReal
   realToNum
   ------------------------------------------------------------------------- *)

val n256 = Arbnum.fromInt 256
val irealwidth = 8 * PackRealBig.bytesPerElem
val realwidth = Arbnum.fromInt irealwidth
val native_ty =
  binary_ieeeSyntax.mk_ifloat_ty
    (Real.precision - 1, irealwidth - Real.precision)
val () = binary_ieeeLib.is_native := (fn ty => ty = native_ty)

val native_itself =
   (boolSyntax.mk_itself o pairSyntax.mk_prod o binary_ieeeSyntax.dest_float_ty)
      native_ty

val native_plus_infinity_tm =
  binary_ieeeSyntax.mk_float_plus_infinity native_itself
val native_minus_infinity_tm =
  binary_ieeeSyntax.mk_float_minus_infinity native_itself

local
   val byte =  Word8.fromInt o Arbnum.toInt
   fun loop a i x =
      if i <= 0
         then byte (Arbnum.mod (x, n256)) :: a
      else let
              val (r, q) = Arbnum.divmod (x, n256)
           in
              loop (byte q :: a) (i - 1) r
           end
in
   val numToReal = PackRealBig.fromBytes o Word8Vector.fromList o
                   loop [] (PackRealBig.bytesPerElem - 1)
end

local
   val byte = Arbnum.fromInt o Word8.toInt o Word8Vector.sub
in
   fun realToNum r =
      if Real.isNan r
         then raise ERR "realToNum" "NaN"
      else let
              val v = PackRealBig.toBytes r
              val l = List.tabulate
                        (PackRealBig.bytesPerElem, fn i => byte (v, 7 - i))
           in
              List.foldl
                 (fn (b, a) => Arbnum.+ (Arbnum.* (a, n256), b)) Arbnum.zero
                 (List.rev l)
           end
end

(* -------------------------------------------------------------------------
   wordToReal
   realToWord
   ------------------------------------------------------------------------- *)

fun wordToReal tm =
   let
      val (v, n) = wordsSyntax.dest_mod_word_literal tm
   in
      n = realwidth orelse raise ERR "wordToReal" "length mismatch"
    ; numToReal v
   end

fun realToWord r = wordsSyntax.mk_word (realToNum r, realwidth)

(* -------------------------------------------------------------------------
   floatToReal
   realToFloat
   ------------------------------------------------------------------------- *)

local
   val exponent = irealwidth - Real.precision
   val signval = Arbnum.pow (Arbnum.two, Arbnum.fromInt (irealwidth - 1))
   val expval = Arbnum.pow (Arbnum.two, Arbnum.fromInt exponent)
   val manval = Arbnum.pow (Arbnum.two, Arbnum.fromInt (Real.precision - 1))
   fun odd n = Arbnum.mod (n, Arbnum.two) = Arbnum.one
in
   fun floatToReal tm =
      let
         val ((t, w), (s, e, f)) = binary_ieeeSyntax.triple_of_float tm
         val _ = t + 1 = Real.precision andalso w = exponent orelse
                 raise ERR "floatToReal" "size mismatch"
      in
         numToReal
            (Arbnum.+ (if s then signval else Arbnum.zero,
                       Arbnum.+ (Arbnum.* (e, manval), f)))
      end
      handle e as HOL_ERR {origin_function = "dest_floating_point", ...} =>
         if Term.type_of tm = native_ty
            then if binary_ieeeSyntax.is_float_plus_infinity tm
                    then Real.posInf
                 else if binary_ieeeSyntax.is_float_minus_infinity tm
                    then Real.negInf
                 else raise e
         else raise ERR "floatToReal" "not native float type"
   fun realToFloat r =
      case Real.class r of
         IEEEReal.INF => if Real.signBit r then native_minus_infinity_tm
                         else native_plus_infinity_tm
       | IEEEReal.NAN => raise ERR "realToFloat" "NaN"
       | _ =>
           let
              val n = realToNum r
              val (e, f) = Arbnum.divmod (n, manval)
              val (s, e) = Arbnum.divmod (e, expval)
           in
              binary_ieeeSyntax.float_of_triple
                ((Real.precision - 1, exponent), (odd s, e, f))
           end
end

(* -------------------------------------------------------------------------
   liftNative
   ------------------------------------------------------------------------- *)

fun withRounding tm f x =
   let
      val mode = IEEEReal.getRoundingMode ()
   in
      IEEEReal.setRoundingMode
        (if tm = binary_ieeeSyntax.roundTiesToEven_tm
            then IEEEReal.TO_NEAREST
         else if tm = binary_ieeeSyntax.roundTowardZero_tm
            then IEEEReal.TO_ZERO
         else if tm = binary_ieeeSyntax.roundTowardNegative_tm
            then IEEEReal.TO_NEGINF
         else if tm = binary_ieeeSyntax.roundTowardPositive_tm
            then IEEEReal.TO_POSINF
         else raise ERR "setRounding" "not a valid mode")
     ; f x before IEEEReal.setRoundingMode mode
   end

fun mk_native_ieee_thm th = Thm.mk_oracle_thm "native_ieee" ([], th)

fun liftNative1 f dst (tm: term) =
   case Lib.total dst tm of
      SOME (mode, a) =>
        (case Lib.total floatToReal a of
            SOME ra =>
               withRounding mode
                 (fn ra =>
                    mk_native_ieee_thm
                       (boolSyntax.mk_eq (tm, realToFloat (f ra)))) ra
          | _ => raise ERR "liftNative1" "failed to convert to native reals")
    | NONE => raise ERR "liftNative1" ""

fun liftNative2 f dst (tm: term) =
   case Lib.total dst tm of
      SOME (mode, a, b) =>
        (case (Lib.total floatToReal a, Lib.total floatToReal b) of
            (SOME ra, SOME rb) =>
               withRounding mode
                 (fn (ra, rb) =>
                    mk_native_ieee_thm
                       (boolSyntax.mk_eq (tm, realToFloat (f (ra, rb)))))
                 (ra, rb)
          | _ => raise ERR "liftNative2" "failed to convert to native reals")
    | NONE => raise ERR "liftNative2" ""

fun liftNative3 f dst (tm: term) =
   case Lib.total dst tm of
      SOME (mode, a, b, c) =>
        (case (Lib.total floatToReal a,
               Lib.total floatToReal b,
               Lib.total floatToReal c) of
            (SOME ra, SOME rb, SOME rc) =>
               withRounding mode
                 (fn (ra, rb, rc) =>
                    mk_native_ieee_thm
                       (boolSyntax.mk_eq (tm, realToFloat (f (ra, rb, rc)))))
                 (ra, rb, rc)
          | _ => raise ERR "liftNative2" "failed to convert to native reals")
    | NONE => raise ERR "liftNative2" ""

fun liftNativeOrder f dst (tm: term) =
   case Lib.total dst tm of
      SOME (a, b) =>
        (case (Lib.total floatToReal a, Lib.total floatToReal b) of
            (SOME ra, SOME rb) =>
                mk_native_ieee_thm (boolSyntax.mk_eq (tm, f (ra, rb)))
          | _ => raise ERR "liftNativeOrder"
                           "failed to convert to native reals")
    | NONE => raise ERR "liftNativeOrder" ""

(* -------------------------------------------------------------------------
   Native conversions
   ------------------------------------------------------------------------- *)

val () = binary_ieeeLib.native_float_sqrt_CONV :=
   liftNative1 Math.sqrt binary_ieeeSyntax.dest_float_sqrt

val () = binary_ieeeLib.native_float_add_CONV :=
   liftNative2 Real.+ binary_ieeeSyntax.dest_float_add

val () = binary_ieeeLib.native_float_sub_CONV :=
   liftNative2 Real.- binary_ieeeSyntax.dest_float_sub

(**************************************************************
 NOTE: Poly/ML 5.5's multiply isn't fully IEEE compliant on 64-bit machines,
       which results in some selftest failures
 **************************************************************)
val () = binary_ieeeLib.native_float_mul_CONV :=
   liftNative2 Real.* binary_ieeeSyntax.dest_float_mul

val () = binary_ieeeLib.native_float_div_CONV :=
   liftNative2 Real./ binary_ieeeSyntax.dest_float_div

val () = binary_ieeeLib.native_float_mul_add_CONV :=
   liftNative3 Real.*+ binary_ieeeSyntax.dest_float_mul_add

val () = binary_ieeeLib.native_float_mul_sub_CONV :=
   liftNative3 Real.*- binary_ieeeSyntax.dest_float_mul_sub

fun mk_b true = boolSyntax.T
  | mk_b false = boolSyntax.F

val () = binary_ieeeLib.native_float_less_than_CONV :=
   liftNativeOrder (mk_b o Real.<) binary_ieeeSyntax.dest_float_less_than

val () = binary_ieeeLib.native_float_less_equal_CONV :=
   liftNativeOrder (mk_b o Real.<=) binary_ieeeSyntax.dest_float_less_equal

val () = binary_ieeeLib.native_float_greater_than_CONV :=
   liftNativeOrder (mk_b o Real.>) binary_ieeeSyntax.dest_float_greater_than

val () = binary_ieeeLib.native_float_greater_equal_CONV :=
   liftNativeOrder (mk_b o Real.>=) binary_ieeeSyntax.dest_float_greater_equal

val () = binary_ieeeLib.native_float_equal_CONV :=
   liftNativeOrder (mk_b o Real.==) binary_ieeeSyntax.dest_float_equal

val mk_float_compare =
   fn IEEEReal.LESS      => binary_ieeeSyntax.LT_tm
    | IEEEReal.EQUAL     => binary_ieeeSyntax.EQ_tm
    | IEEEReal.GREATER   => binary_ieeeSyntax.GT_tm
    | IEEEReal.UNORDERED => binary_ieeeSyntax.UN_tm

val () = binary_ieeeLib.native_float_compare_CONV :=
   liftNativeOrder (mk_float_compare o Real.compareReal)
      binary_ieeeSyntax.dest_float_compare

(* ------------------------------------------------------------------------ *)

end
