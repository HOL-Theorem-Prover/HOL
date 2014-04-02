structure binary_ieeeSyntax :> binary_ieeeSyntax =
struct

open Abbrev HolKernel
open fcpSyntax binary_ieeeTheory

val ERR = Feedback.mk_HOL_ERR "binary_ieeeSyntax"

(* ------------------------------------------------------------------------- *)

val float_value_ty =
   Type.mk_thy_type {Thy = "binary_ieee", Tyop = "float_value", Args = []}

val rounding_ty =
   Type.mk_thy_type {Thy = "binary_ieee", Tyop = "rounding", Args = []}

fun mk_float_ty (t, w) =
   Type.mk_thy_type {Thy = "binary_ieee", Tyop = "float", Args = [t, w]}

fun dest_float_ty ty =
   case Type.dest_thy_type ty of
      {Thy = "binary_ieee", Args = [t, w], Tyop = "float"} => (t, w)
    | _ => raise ERR "dest_float_ty" ""

val mk_ifloat_ty =
   mk_float_ty o
   (fcpSyntax.mk_int_numeric_type ## fcpSyntax.mk_int_numeric_type)

val dest_ifloat_ty =
   (fcpSyntax.dest_int_numeric_type ## fcpSyntax.dest_int_numeric_type) o
   dest_float_ty

fun mk_floating_point (s, e, f) =
   TypeBase.mk_record
      (mk_float_ty (wordsSyntax.dim_of f, wordsSyntax.dim_of e),
       [("Sign", s), ("Exponent", e), ("Significand", f)])

fun dest_floating_point tm =
   case Lib.with_exn TypeBase.dest_record tm (ERR "dest_floating_point" "") of
      (_, [("Sign", s), ("Exponent", e), ("Significand", f)]) => (s, e, f)
    | _ => raise ERR "dest_floating_point" ""

fun float_of_triple ((t, w), (s, e, f)) =
   mk_floating_point
      (wordsSyntax.mk_wordii (if s then 1 else 0, 1),
       wordsSyntax.mk_wordi (e, w),
       wordsSyntax.mk_wordi (f, t))

local
   val sz = Arbnum.toInt o wordsSyntax.size_of
in
   fun triple_of_float tm =
      let
         val (s, e, f) = dest_floating_point tm
      in
         ((sz f, sz e),
          (wordsSyntax.uint_of_word s = 1,
           wordsSyntax.dest_word_literal e,
           wordsSyntax.dest_word_literal f))
      end
end

fun mk_float_var tw = fn v => Term.mk_var (v, mk_float_ty tw)
fun mk_ifloat_var tw = fn v => Term.mk_var (v, mk_ifloat_ty tw)

fun is_pure_real_literal tm =
   case Lib.total realSyntax.dest_injected tm of
      SOME a => numSyntax.is_numeral a
    | NONE => false

fun is_ground_real tm =
   case Lib.total realSyntax.dest_div tm of
      SOME (a, b) => realSyntax.is_real_literal a andalso is_pure_real_literal b
    | NONE => realSyntax.is_real_literal tm

(* ------------------------------------------------------------------------- *)

val monop =
   HolKernel.syntax_fns "binary_ieee" 1 HolKernel.dest_monop
      (Lib.curry boolSyntax.mk_icomb)

val binop =
   HolKernel.syntax_fns "binary_ieee" 2 HolKernel.dest_binop HolKernel.mk_binop

val triop =
   HolKernel.syntax_fns "binary_ieee" 3 HolKernel.dest_triop HolKernel.mk_triop

val quadop =
   HolKernel.syntax_fns
     "binary_ieee" 4 HolKernel.dest_quadop HolKernel.mk_quadop

val tw_monop =
   HolKernel.syntax_fns "binary_ieee" 1
      (fn tm1 => fn e => fn tm2 =>
          let
             val ty = boolSyntax.dest_itself (HolKernel.dest_monop tm1 e tm2)
             val (t, w) = pairSyntax.dest_prod ty
          in
             (fcpSyntax.dest_int_numeric_type t,
              fcpSyntax.dest_int_numeric_type w)
          end)
      (fn tm1 => fn (t, w) =>
         let
            val t_ty = fcpSyntax.mk_int_numeric_type t
            val w_ty = fcpSyntax.mk_int_numeric_type w
            val p_ty = pairSyntax.mk_prod (t_ty, w_ty)
         in
            boolSyntax.mk_icomb (tm1, boolSyntax.mk_itself p_ty)
         end)

val etw_monop =
   HolKernel.syntax_fns "binary_ieee" 1
      (fn tm1 => fn e => fn tm2 =>
          let
             val (t1, t2) =
                pairSyntax.dest_pair (HolKernel.dest_monop tm1 e tm2)
             val t = boolSyntax.dest_itself t2
             val w = wordsSyntax.size_of t1
          in
             (wordsSyntax.uint_of_word t1,
              fcpSyntax.dest_int_numeric_type t,
              Arbnum.toInt w)
          end)
      (fn tm1 => fn (i, t, w) =>
         let
            val t1 = wordsSyntax.mk_wordii (i, w)
            val t2 = boolSyntax.mk_itself (fcpSyntax.mk_int_numeric_type t)
         in
            boolSyntax.mk_icomb (tm1, pairSyntax.mk_pair (t1, t2))
         end)

val tw_binop = 
   HolKernel.syntax_fns "binary_ieee" 2
      (fn tm1 => fn e => fn tm2 =>
         let
            val (a, b) = HolKernel.dest_binop tm1 e tm2
            val (ty1, ty2) = dest_float_ty (Term.type_of tm2)
         in
            (a, b, ty1, ty2)
         end)
      (fn tm1 => fn (tm2, tm3, t, w) =>
          Term.inst [``:'w`` |-> w, ``:'t`` |-> t]
             (HolKernel.mk_binop tm1 (tm2, tm3)))

val tw_triop =
   HolKernel.syntax_fns "binary_ieee" 3
      (fn tm1 => fn e => fn tm2 =>
         let
            val (a, b, c) = HolKernel.dest_triop tm1 e tm2
            val (ty1, ty2) = dest_float_ty (Term.type_of tm2)
         in
            (a, b, c, ty1, ty2)
         end)
      (fn tm1 => fn (tm2, tm3, tm4, t, w) =>
          Term.inst [``:'w`` |-> w, ``:'t`` |-> t]
             (HolKernel.mk_triop tm1 (tm2, tm3, tm4)))

(* ------------------------------------------------------------------------- *)

fun const (s, ty) = Term.mk_thy_const {Ty = ty, Thy = "binary_ieee", Name = s}

val infinity_tm = const ("Infinity", ``:binary_ieee$float_value``)
val nan_tm = const ("NaN", ``:binary_ieee$float_value``)

val (roundTiesToEven_tm, roundTowardPositive_tm, roundTowardNegative_tm,
     roundTowardZero_tm) =
   Lib.quadruple_of_list (TypeBase.constructors_of ``:binary_ieee$rounding``)

val (LT_tm, GT_tm, EQ_tm, UN_tm) =
   Lib.quadruple_of_list
      (TypeBase.constructors_of ``:binary_ieee$float_compare``)

(* ------------------------------------------------------------------------- *)

val (float_tm, mk_float, dest_float, is_float) = monop "Float"

val (float_sign_tm, mk_float_sign, dest_float_sign, is_float_sign) =
   monop "float_Sign"

val (float_exponent_tm, mk_float_exponent, dest_float_exponent,
     is_float_exponent) = monop "float_Exponent"

val (float_significand_tm, mk_float_significand, dest_float_significand,
     is_float_significand) = monop "float_Significand"

val (float_to_real_tm, mk_float_to_real, dest_float_to_real, is_float_to_real) =
   monop "float_to_real"

val (float_value_tm, mk_float_value, dest_float_value, is_float_value) =
   monop "float_value"

val (float_is_nan_tm, mk_float_is_nan, dest_float_is_nan, is_float_is_nan) =
   monop "float_is_nan"

val (float_is_infinite_tm, mk_float_is_infinite, dest_float_is_infinite,
     is_float_is_infinite) = monop "float_is_infinite"

val (float_is_normal_tm, mk_float_is_normal, dest_float_is_normal,
     is_float_is_normal) = monop "float_is_normal"

val (float_is_subnormal_tm, mk_float_is_subnormal, dest_float_is_subnormal,
     is_float_is_subnormal) = monop "float_is_subnormal"

val (float_is_zero_tm, mk_float_is_zero, dest_float_is_zero, is_float_is_zero) =
   monop "float_is_zero"

val (float_is_finite_tm, mk_float_is_finite, dest_float_is_finite,
     is_float_is_finite) = monop "float_is_finite"

val (float_is_integral_tm, mk_float_is_integral, dest_float_is_integral,
     is_float_is_integral) = monop "float_is_integral"

val (float_negate_tm, mk_float_negate, dest_float_negate, is_float_negate) =
   monop "float_negate"

val (float_abs_tm, mk_float_abs, dest_float_abs, is_float_abs) =
   monop "float_abs"

val (float_plus_infinity_tm, mk_float_plus_infinity, dest_float_plus_infinity,
     is_float_plus_infinity) = monop "float_plus_infinity"

val (float_plus_zero_tm, mk_float_plus_zero, dest_float_plus_zero,
     is_float_plus_zero) = monop "float_plus_zero"

val (float_top_tm, mk_float_top, dest_float_top, is_float_top) =
   monop "float_top"

val (float_plus_min_tm, mk_float_plus_min, dest_float_plus_min,
     is_float_plus_min) = monop "float_plus_min"

val (float_minus_infinity_tm, mk_float_minus_infinity,
     dest_float_minus_infinity, is_float_minus_infinity) =
   monop "float_minus_infinity"

val (float_minus_zero_tm, mk_float_minus_zero, dest_float_minus_zero,
     is_float_minus_zero) = monop "float_minus_zero"

val (float_bottom_tm, mk_float_bottom, dest_float_bottom, is_float_bottom) =
   monop "float_bottom"

val (float_minus_min_tm, mk_float_minus_min, dest_float_minus_min,
     is_float_minus_min) = monop "float_minus_min"

val (float_some_nan_tm, mk_float_some_nan, dest_float_some_nan,
     is_float_some_nan) = monop "float_some_nan"

val (largest_tm, mk_largest, dest_largest, is_largest) = monop "largest"

val (threshold_tm, mk_threshold, dest_threshold, is_threshold) =
   monop "threshold"

val (ulp_tm, mk_ulp, dest_ulp, is_ulp) = monop "ulp"

val (ULP_tm, mk_ULP, dest_ULP, is_ULP) = monop "ULP"

val (integral_round_tm, mk_integral_round, dest_integral_round,
     is_integral_round) = binop "integral_round"

val (float_round_to_integral_tm, mk_float_round_to_integral,
     dest_float_round_to_integral, is_float_round_to_integral) =
   binop "float_round_to_integral"

val (float_sqrt_tm, mk_float_sqrt, dest_float_sqrt, is_float_sqrt) =
   binop "float_sqrt"

val (float_add_tm, mk_float_add, dest_float_add, is_float_add) =
   triop "float_add"

val (float_sub_tm, mk_float_sub, dest_float_sub, is_float_sub) =
   triop "float_sub"

val (float_mul_tm, mk_float_mul, dest_float_mul, is_float_mul) =
   triop "float_mul"

val (float_div_tm, mk_float_div, dest_float_div, is_float_div) =
   triop "float_div"

val (float_compare_tm, mk_float_compare, dest_float_compare, is_float_compare) =
   binop "float_compare"

val (float_less_than_tm, mk_float_less_than, dest_float_less_than,
     is_float_less_than) =
   binop "float_less_than"

val (float_greater_than_tm, mk_float_greater_than, dest_float_greater_than,
     is_float_greater_than) =
   binop "float_greater_than"

val (float_less_equal_tm, mk_float_less_equal, dest_float_less_equal,
     is_float_less_equal) =
   binop "float_less_equal"

val (float_greater_equal_tm, mk_float_greater_equal, dest_float_greater_equal,
     is_float_greater_equal) =
   binop "float_greater_equal"

val (float_equal_tm, mk_float_equal, dest_float_equal, is_float_equal) =
   binop "float_equal"

val (float_mul_add_tm, mk_float_mul_add, dest_float_mul_add, is_float_mul_add) =
   quadop "float_mul_add"

(* ------------------------------------------------------------------------- *)

val (round_tm, mk_round, dest_round, is_round) = tw_binop "round"

val (float_round_tm, mk_float_round, dest_float_round, is_float_round) = 
   tw_triop "float_round"

(* ------------------------------------------------------------------------- *)

val (_, mk_int_float_plus_infinity, dest_int_float_plus_infinity,
     is_int_float_plus_infinity) = tw_monop "float_plus_infinity"

val (_, mk_int_float_plus_zero, dest_int_float_plus_zero,
     is_int_float_plus_zero) = tw_monop "float_plus_zero"

val (_, mk_int_float_top, dest_int_float_top, is_int_float_top) =
   tw_monop "float_top"

val (_, mk_int_float_plus_min, dest_int_float_plus_min, is_int_float_plus_min) =
   tw_monop "float_plus_min"

val (_, mk_int_float_minus_infinity,
     dest_int_float_minus_infinity, is_int_float_minus_infinity) =
   tw_monop "float_minus_infinity"

val (_, mk_int_float_minus_zero, dest_int_float_minus_zero,
     is_int_float_minus_zero) = tw_monop "float_minus_zero"

val (_, mk_int_float_bottom, dest_int_float_bottom, is_int_float_bottom) =
   tw_monop "float_bottom"

val (_, mk_int_float_minus_min, dest_int_float_minus_min,
     is_int_float_minus_min) = tw_monop "float_minus_min"

val (_, mk_int_float_some_nan, dest_int_float_some_nan,
     is_int_float_some_nan) = tw_monop "float_some_nan"

val (_, mk_int_largest, dest_int_largest, is_int_largest) = tw_monop "largest"

val (_, mk_int_threshold, dest_int_threshold, is_int_threshold) =
   tw_monop "threshold"

val (_, mk_int_ulp, dest_int_ulp, is_int_ulp) = tw_monop "ulp"

val (_, mk_int_ULP, dest_int_ULP, is_int_ULP) = etw_monop "ULP"

(* -------------------------------------------------------------------------
   numToReal
   realToNum
   ------------------------------------------------------------------------- *)

val n256 = Arbnum.fromInt 256
val irealwidth = 8 * PackRealBig.bytesPerElem
val realwidth = Arbnum.fromInt irealwidth
val native_ty = mk_ifloat_ty (Real.precision - 1, irealwidth - Real.precision)

val native_itself =
   (boolSyntax.mk_itself o pairSyntax.mk_prod o dest_float_ty) native_ty

val native_plus_infinity_tm = mk_float_plus_infinity native_itself
val native_minus_infinity_tm = mk_float_minus_infinity native_itself

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
         val ((t, w), (s, e, f)) = triple_of_float tm
         val _ = t + 1 = Real.precision andalso w = exponent orelse
                 raise ERR "floatToReal" "size mismatch"
      in
         numToReal
            (Arbnum.+ (if s then signval else Arbnum.zero,
                       Arbnum.+ (Arbnum.* (e, manval), f)))
      end
      handle e as HOL_ERR {origin_function = "dest_floating_point", ...} =>
         if Term.type_of tm = native_ty
            then if is_float_plus_infinity tm
                    then Real.posInf
                 else if is_float_minus_infinity tm
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
              float_of_triple ((Real.precision - 1, exponent), (odd s, e, f))
           end
end

end
