signature fpSyntax =
sig
    type term = Term.term

    val float_to_fp_tm : term
    val fp_abs_tm : term
    val fp_add_tm : term
    val fp_add_with_flags_tm : term
    val fp_bottom_tm : term
    val fp_compare_tm : term
    val fp_div_tm : term
    val fp_div_with_flags_tm : term
    val fp_equal_tm : term
    val fp_greaterEqual_tm : term
    val fp_greaterThan_tm : term
    val fp_isFinite_tm : term
    val fp_isInfinite_tm : term
    val fp_isIntegral_tm : term
    val fp_isNan_tm : term
    val fp_isNormal_tm : term
    val fp_isSignallingNan_tm : term
    val fp_isSubnormal_tm : term
    val fp_isZero_tm : term
    val fp_lessEqual_tm : term
    val fp_lessThan_tm : term
    val fp_mul_tm : term
    val fp_mul_with_flags_tm : term
    val fp_mul_add_tm : term
    val fp_mul_add_with_flags_tm : term
    val fp_mul_sub_tm : term
    val fp_mul_sub_with_flags_tm : term
    val fp_negate_tm : term
    val fp_neginf_tm : term
    val fp_negmin_tm : term
    val fp_negzero_tm : term
    val fp_posinf_tm : term
    val fp_posmin_tm : term
    val fp_poszero_tm : term
    val fp_roundToIntegral_tm : term
    val fp_sqrt_tm : term
    val fp_sqrt_with_flags_tm : term
    val fp_sub_tm : term
    val fp_sub_with_flags_tm : term
    val fp_to_float_tm : term
    val fp_to_int_tm : term
    val fp_to_real_tm : term
    val fp_top_tm : term
    val int_to_fp_tm : term
    val real_to_fp_tm : term
    val real_to_fp_with_flags_tm : term

    val mk_float_to_fp : term -> term
    val mk_fp_abs : term -> term
    val mk_fp_add : term * term * term -> term
    val mk_fp_add_with_flags : term * term * term -> term
    val mk_fp_compare : term * term -> term
    val mk_fp_div : term * term * term -> term
    val mk_fp_div_with_flags : term * term * term -> term
    val mk_fp_equal : term * term -> term
    val mk_fp_greaterEqual : term * term -> term
    val mk_fp_greaterThan : term * term -> term
    val mk_fp_isFinite : term -> term
    val mk_fp_isInfinite : term -> term
    val mk_fp_isIntegral : term -> term
    val mk_fp_isNan : term -> term
    val mk_fp_isSignallingNan : term -> term
    val mk_fp_isNormal : term -> term
    val mk_fp_isSubnormal : term -> term
    val mk_fp_isZero : term -> term
    val mk_fp_lessEqual : term * term -> term
    val mk_fp_lessThan : term * term -> term
    val mk_fp_mul : term * term * term -> term
    val mk_fp_mul_with_flags : term * term * term -> term
    val mk_fp_mul_add : term * term * term * term -> term
    val mk_fp_mul_add_with_flags : term * term * term * term -> term
    val mk_fp_mul_sub : term * term * term * term -> term
    val mk_fp_mul_sub_with_flags : term * term * term * term -> term
    val mk_fp_negate : term -> term
    val mk_fp_roundToIntegral : term * term -> term
    val mk_fp_sqrt : term * term -> term
    val mk_fp_sqrt_with_flags : term * term -> term
    val mk_fp_sub : term * term * term -> term
    val mk_fp_sub_with_flags : term * term * term -> term
    val mk_fp_to_float : term -> term
    val mk_fp_to_int : term * term -> term
    val mk_fp_to_real : term -> term
    val mk_int_to_fp : term * term -> term
    val mk_real_to_fp : term * term -> term
    val mk_real_to_fp_with_flags : term * term -> term

    val is_float_to_fp : term -> bool
    val is_fp_abs : term -> bool
    val is_fp_add : term -> bool
    val is_fp_add_with_flags : term -> bool
    val is_fp_compare : term -> bool
    val is_fp_div : term -> bool
    val is_fp_div_with_flags : term -> bool
    val is_fp_equal : term -> bool
    val is_fp_greaterEqual : term -> bool
    val is_fp_greaterThan : term -> bool
    val is_fp_isFinite : term -> bool
    val is_fp_isInfinite : term -> bool
    val is_fp_isIntegral : term -> bool
    val is_fp_isSignallingNan : term -> bool
    val is_fp_isNormal : term -> bool
    val is_fp_isSubnormal : term -> bool
    val is_fp_isZero : term -> bool
    val is_fp_lessEqual : term -> bool
    val is_fp_lessThan : term -> bool
    val is_fp_mul : term -> bool
    val is_fp_mul_with_flags : term -> bool
    val is_fp_mul_add : term -> bool
    val is_fp_mul_add_with_flags : term -> bool
    val is_fp_mul_sub : term -> bool
    val is_fp_mul_sub_with_flags : term -> bool
    val is_fp_negate : term -> bool
    val is_fp_roundToIntegral : term -> bool
    val is_fp_sqrt : term -> bool
    val is_fp_sqrt_with_flags : term -> bool
    val is_fp_sub : term -> bool
    val is_fp_sub_with_flags : term -> bool
    val is_fp_to_float : term -> bool
    val is_fp_to_int : term -> bool
    val is_fp_to_real : term -> bool
    val is_int_to_fp : term -> bool
    val is_real_to_fp : term -> bool
    val is_real_to_fp_with_flags : term -> bool

    val dest_float_to_fp : term -> term
    val dest_fp_abs : term -> term
    val dest_fp_add : term -> term * term * term
    val dest_fp_add_with_flags : term -> term * term * term
    val dest_fp_compare : term -> term * term
    val dest_fp_div : term -> term * term * term
    val dest_fp_div_with_flags : term -> term * term * term
    val dest_fp_equal : term -> term * term
    val dest_fp_greaterEqual : term -> term * term
    val dest_fp_greaterThan : term -> term * term
    val dest_fp_isFinite : term -> term
    val dest_fp_isInfinite : term -> term
    val dest_fp_isIntegral : term -> term
    val dest_fp_isNan : term -> term
    val dest_fp_isNormal : term -> term
    val dest_fp_isSignallingNan : term -> term
    val dest_fp_isSubnormal : term -> term
    val dest_fp_isZero : term -> term
    val dest_fp_lessEqual : term -> term * term
    val dest_fp_lessThan : term -> term * term
    val dest_fp_mul : term -> term * term * term
    val dest_fp_mul_with_flags : term -> term * term * term
    val dest_fp_mul_add : term -> term * term * term * term
    val dest_fp_mul_add_with_flags : term -> term * term * term * term
    val dest_fp_mul_sub : term -> term * term * term * term
    val dest_fp_mul_sub_with_flags : term -> term * term * term * term
    val dest_fp_negate : term -> term
    val dest_fp_roundToIntegral : term -> term * term
    val dest_fp_sqrt : term -> term * term
    val dest_fp_sqrt_with_flags : term -> term * term
    val dest_fp_sub : term -> term * term * term
    val dest_fp_sub_with_flags : term -> term * term * term
    val dest_fp_to_float : term -> term
    val dest_fp_to_int : term -> term * term
    val dest_fp_to_real : term -> term
    val dest_int_to_fp : term -> term * term
    val dest_real_to_fp : term -> term * term
    val dest_real_to_fp_with_flags : term -> term * term
end
