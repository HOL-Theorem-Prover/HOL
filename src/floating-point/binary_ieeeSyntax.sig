signature binary_ieeeSyntax =
sig
   type hol_type = Type.hol_type
   type term = Term.term

   val float_value_ty: hol_type
   val rounding_ty: hol_type

   val mk_float_ty: hol_type * hol_type -> hol_type
   val dest_float_ty: hol_type -> hol_type * hol_type

   val mk_ifloat_ty: int * int -> hol_type
   val dest_ifloat_ty: hol_type -> int * int

   val mk_floating_point: term * term * term -> term
   val dest_floating_point: term -> term * term * term

   val float_of_triple: (int * int) * (bool * Arbnum.num * Arbnum.num) -> term
   val triple_of_float: term -> (int * int) * (bool * Arbnum.num * Arbnum.num)

   val mk_float_var: hol_type * hol_type -> string -> term
   val mk_ifloat_var: int * int -> string -> term

   val floatToReal : term -> real
   val wordToReal  : term -> real
   val realToFloat : real -> term
   val realToWord  : real -> term
   val native_ty   : hol_type

   val EQ_tm: term
   val GT_tm: term
   val LT_tm: term
   val UN_tm: term
   val ULP_tm: term
   val float_abs_tm: term
   val float_add_tm: term
   val float_bottom_tm: term
   val float_compare_tm: term
   val float_div_tm: term
   val float_equal_tm: term
   val float_exponent_tm: term
   val float_greater_equal_tm: term
   val float_greater_than_tm: term
   val float_is_finite_tm: term
   val float_is_infinite_tm: term
   val float_is_integral_tm: term
   val float_is_nan_tm: term
   val float_is_normal_tm: term
   val float_is_subnormal_tm: term
   val float_is_zero_tm: term
   val float_less_equal_tm: term
   val float_less_than_tm: term
   val float_minus_infinity_tm: term
   val float_minus_min_tm: term
   val float_minus_zero_tm: term
   val float_mul_tm: term
   val float_mul_add_tm: term
   val float_negate_tm: term
   val float_plus_infinity_tm: term
   val float_plus_min_tm: term
   val float_plus_zero_tm: term
   val float_sqrt_tm: term
   val float_round_tm: term
   val float_round_to_integral_tm: term
   val float_sign_tm: term
   val float_significand_tm: term
   val float_some_nan_tm: term
   val float_sub_tm: term
   val float_tm: term
   val float_to_real_tm: term
   val float_top_tm: term
   val float_value_tm: term
   val infinity_tm: term
   val integral_round_tm: term
   val largest_tm: term
   val nan_tm: term
   val roundTiesToEven_tm: term
   val roundTowardNegative_tm: term
   val roundTowardPositive_tm: term
   val roundTowardZero_tm: term
   val round_tm: term
   val threshold_tm: term
   val ulp_tm: term

   val dest_int_ULP: term -> int * int * int
   val dest_int_float_bottom: term -> int * int
   val dest_int_float_minus_infinity: term -> int * int
   val dest_int_float_minus_min: term -> int * int
   val dest_int_float_minus_zero: term -> int * int
   val dest_int_float_plus_infinity: term -> int * int
   val dest_int_float_plus_min: term -> int * int
   val dest_int_float_plus_zero: term -> int * int
   val dest_int_float_some_nan: term -> int * int
   val dest_int_float_top: term -> int * int
   val dest_int_largest: term -> int * int
   val dest_int_threshold: term -> int * int
   val dest_int_ulp: term -> int * int

   val dest_ULP: term -> term
   val dest_float: term -> term
   val dest_float_abs: term -> term
   val dest_float_add: term -> term * term * term
   val dest_float_bottom: term -> term
   val dest_float_compare: term -> term * term
   val dest_float_div: term -> term * term * term
   val dest_float_equal: term -> term * term
   val dest_float_exponent: term -> term
   val dest_float_greater_equal: term -> term * term
   val dest_float_greater_than: term -> term * term
   val dest_float_is_finite: term -> term
   val dest_float_is_infinite: term -> term
   val dest_float_is_integral: term -> term
   val dest_float_is_nan: term -> term
   val dest_float_is_normal: term -> term
   val dest_float_is_subnormal: term -> term
   val dest_float_is_zero: term -> term
   val dest_float_less_equal: term -> term * term
   val dest_float_less_than: term -> term * term
   val dest_float_minus_infinity: term -> term
   val dest_float_minus_min: term -> term
   val dest_float_minus_zero: term -> term
   val dest_float_mul: term -> term * term * term
   val dest_float_mul_add: term -> term * term * term * term
   val dest_float_negate: term -> term
   val dest_float_plus_infinity: term -> term
   val dest_float_plus_min: term -> term
   val dest_float_plus_zero: term -> term
   val dest_float_round: term -> term * term * term * hol_type * hol_type
   val dest_float_round_to_integral: term -> term * term
   val dest_float_sign: term -> term
   val dest_float_significand: term -> term
   val dest_float_some_nan: term -> term
   val dest_float_sqrt: term -> term * term
   val dest_float_sub: term -> term * term * term
   val dest_float_to_real: term -> term
   val dest_float_top: term -> term
   val dest_float_value: term -> term
   val dest_integral_round: term -> term * term
   val dest_largest: term -> term
   val dest_round: term -> term * term * hol_type * hol_type
   val dest_threshold: term -> term
   val dest_ulp: term -> term

   val is_int_ULP: term -> bool
   val is_int_float_bottom: term -> bool
   val is_int_float_minus_infinity: term -> bool
   val is_int_float_minus_min: term -> bool
   val is_int_float_minus_zero: term -> bool
   val is_int_float_plus_infinity: term -> bool
   val is_int_float_plus_min: term -> bool
   val is_int_float_plus_zero: term -> bool
   val is_int_float_some_nan: term -> bool
   val is_int_float_top: term -> bool
   val is_int_largest: term -> bool
   val is_int_threshold: term -> bool
   val is_int_ulp: term -> bool

   val is_ULP: term -> bool
   val is_float: term -> bool
   val is_float_abs: term -> bool
   val is_float_add: term -> bool
   val is_float_bottom: term -> bool
   val is_float_compare: term -> bool
   val is_float_div: term -> bool
   val is_float_equal: term -> bool
   val is_float_exponent: term -> bool
   val is_float_greater_equal: term -> bool
   val is_float_greater_than: term -> bool
   val is_float_is_finite: term -> bool
   val is_float_is_infinite: term -> bool
   val is_float_is_integral: term -> bool
   val is_float_is_nan: term -> bool
   val is_float_is_normal: term -> bool
   val is_float_is_subnormal: term -> bool
   val is_float_is_zero: term -> bool
   val is_float_less_equal: term -> bool
   val is_float_less_than: term -> bool
   val is_float_minus_infinity: term -> bool
   val is_float_minus_min: term -> bool
   val is_float_minus_zero: term -> bool
   val is_float_mul: term -> bool
   val is_float_mul_add: term -> bool
   val is_float_negate: term -> bool
   val is_float_plus_infinity: term -> bool
   val is_float_plus_min: term -> bool
   val is_float_plus_zero: term -> bool
   val is_float_round: term -> bool
   val is_float_round_to_integral: term -> bool
   val is_float_sign: term -> bool
   val is_float_significand: term -> bool
   val is_float_some_nan: term -> bool
   val is_float_sqrt: term -> bool
   val is_float_sub: term -> bool
   val is_float_to_real: term -> bool
   val is_float_top: term -> bool
   val is_float_value: term -> bool
   val is_ground_real: term -> bool
   val is_integral_round: term -> bool
   val is_largest: term -> bool
   val is_round: term -> bool
   val is_threshold: term -> bool
   val is_ulp: term -> bool

   val mk_int_ULP: int * int * int -> term
   val mk_int_float_bottom: int * int -> term
   val mk_int_float_minus_infinity: int * int -> term
   val mk_int_float_minus_min: int * int -> term
   val mk_int_float_minus_zero: int * int -> term
   val mk_int_float_plus_infinity: int * int -> term
   val mk_int_float_plus_min: int * int -> term
   val mk_int_float_plus_zero: int * int -> term
   val mk_int_float_some_nan: int * int -> term
   val mk_int_float_top: int * int -> term
   val mk_int_largest: int * int -> term
   val mk_int_threshold: int * int -> term
   val mk_int_ulp: int * int -> term

   val mk_ULP: term -> term
   val mk_float: term -> term
   val mk_float_abs: term -> term
   val mk_float_add: term * term * term -> term
   val mk_float_bottom: term -> term
   val mk_float_compare: term * term -> term
   val mk_float_div: term * term * term -> term
   val mk_float_equal: term * term -> term
   val mk_float_exponent: term -> term
   val mk_float_greater_equal: term * term -> term
   val mk_float_greater_than: term * term -> term
   val mk_float_is_finite: term -> term
   val mk_float_is_infinite: term -> term
   val mk_float_is_integral: term -> term
   val mk_float_is_nan: term -> term
   val mk_float_is_normal: term -> term
   val mk_float_is_subnormal: term -> term
   val mk_float_is_zero: term -> term
   val mk_float_less_equal: term * term -> term
   val mk_float_less_than: term * term -> term
   val mk_float_minus_infinity: term -> term
   val mk_float_minus_min: term -> term
   val mk_float_minus_zero: term -> term
   val mk_float_mul: term * term * term -> term
   val mk_float_mul_add: term * term * term * term -> term
   val mk_float_negate: term -> term
   val mk_float_plus_infinity: term -> term
   val mk_float_plus_min: term -> term
   val mk_float_plus_zero: term -> term
   val mk_float_round: term * term * term * hol_type * hol_type -> term
   val mk_float_round_to_integral: term * term -> term
   val mk_float_sign: term -> term
   val mk_float_significand: term -> term
   val mk_float_some_nan: term -> term
   val mk_float_sqrt: term * term -> term
   val mk_float_sub: term * term * term -> term
   val mk_float_to_real: term -> term
   val mk_float_top: term -> term
   val mk_float_value: term -> term
   val mk_integral_round: term * term -> term
   val mk_largest: term -> term
   val mk_round: term * term * hol_type * hol_type -> term
   val mk_threshold: term -> term
   val mk_ulp: term -> term

end
