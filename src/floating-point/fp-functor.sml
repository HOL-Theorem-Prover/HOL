functor fpSyntax (val thy: string
                  val fp: string
                  val ty: Type.hol_type) :> fpSyntax =
struct
   open Abbrev HolKernel
   open machine_ieeeTheory

   val monop = HolKernel.syntax_fns thy 1 HolKernel.dest_monop
                  (Lib.curry boolSyntax.mk_icomb)

   val binop =
      HolKernel.syntax_fns thy 2 HolKernel.dest_binop HolKernel.mk_binop

   val (float_to_fp_tm, mk_float_to_fp, dest_float_to_fp, is_float_to_fp) =
      monop ("float_to_" ^ fp)

   val (real_to_fp_tm, mk_real_to_fp, dest_real_to_fp, is_real_to_fp) =
      binop ("real_to_" ^ fp)

   fun pre s = fp ^ "_" ^ s

   fun const name = Term.mk_thy_const {Ty = ty, Thy = thy, Name = pre name}
   val monop = monop o pre
   val binop = binop o pre
   val triop =
      HolKernel.syntax_fns thy 3 HolKernel.dest_triop HolKernel.mk_triop o pre

   val (fp_abs_tm, mk_fp_abs, dest_fp_abs, is_fp_abs) = monop "abs"
   val (fp_add_tm, mk_fp_add, dest_fp_add, is_fp_add) = triop "add"
   val fp_bottom_tm = const "bottom"
   val (fp_div_tm, mk_fp_div, dest_fp_div, is_fp_div) = triop "div"
   val (fp_equal_tm, mk_fp_equal, dest_fp_equal, is_fp_equal) = binop "equal"
   val (fp_greaterEqual_tm, mk_fp_greaterEqual, dest_fp_greaterEqual,
        is_fp_greaterEqual) = binop "greaterEqual"
   val (fp_greaterThan_tm, mk_fp_greaterThan, dest_fp_greaterThan,
        is_fp_greaterThan) = binop "greaterThan"
   val (fp_isFinite_tm, mk_fp_isFinite, dest_fp_isFinite, is_fp_isFinite) =
      monop "isFinite"
   val (fp_isInfinite_tm, mk_fp_isInfinite, dest_fp_isInfinite,
        is_fp_isInfinite) = monop "isInfinite"
   val (fp_isIntegral_tm, mk_fp_isIntegral, dest_fp_isIntegral,
        is_fp_isIntegral) = monop "isIntegral"
   val (fp_isNan_tm, mk_fp_isNan, dest_fp_isNan, is_fp_isNan) = monop "isNan"
   val (fp_isNormal_tm, mk_fp_isNormal, dest_fp_isNormal, is_fp_isNormal) =
      monop "isNormal"
   val (fp_isSubnormal_tm, mk_fp_isSubnormal, dest_fp_isSubnormal,
        is_fp_isSubnormal) = monop "isSubnormal"
   val (fp_isZero_tm, mk_fp_isZero, dest_fp_isZero, is_fp_isZero) =
      monop "isZero"
   val (fp_lessEqual_tm, mk_fp_lessEqual, dest_fp_lessEqual, is_fp_lessEqual) =
      binop "lessEqual"
   val (fp_lessThan_tm, mk_fp_lessThan, dest_fp_lessThan, is_fp_lessThan) =
      binop "lessThan"
   val (fp_mul_tm, mk_fp_mul, dest_fp_mul, is_fp_mul) = triop "mul"
   val fp_neginf_tm = const "negInf"
   val fp_negmin_tm = const "negMin"
   val fp_negzero_tm = const "negZero"
   val (fp_negate_tm, mk_fp_negate, dest_fp_negate, is_fp_negate) =
      monop "negate"
   val fp_posinf_tm = const "posInf"
   val fp_posmin_tm = const "posMin"
   val fp_poszero_tm = const "posZero"
   val (fp_roundToIntegral_tm, mk_fp_roundToIntegral, dest_fp_roundToIntegral,
        is_fp_roundToIntegral) = binop "roundToIntegral"
   val (fp_sub_tm, mk_fp_sub, dest_fp_sub, is_fp_sub) = triop "sub"
   val (fp_to_float_tm, mk_fp_to_float, dest_fp_to_float, is_fp_to_float) =
      monop "to_float"
   val (fp_to_real_tm, mk_fp_to_real, dest_fp_to_real, is_fp_to_real) =
      monop "to_real"
   val fp_top_tm = const "top"
end
