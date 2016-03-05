signature binary_ieeeLib =
sig

   val add_ieee_to_compset: computeLib.compset -> unit

   val is_native: (Type.hol_type -> bool) ref
   val native_float_sqrt_CONV: Conv.conv ref
   val native_float_add_CONV: Conv.conv ref
   val native_float_sub_CONV: Conv.conv ref
   val native_float_mul_CONV: Conv.conv ref
   val native_float_div_CONV: Conv.conv ref
   val native_float_mul_add_CONV: Conv.conv ref
   val native_float_mul_sub_CONV: Conv.conv ref
   val native_float_less_than_CONV: Conv.conv ref
   val native_float_less_equal_CONV: Conv.conv ref
   val native_float_greater_than_CONV: Conv.conv ref
   val native_float_greater_equal_CONV: Conv.conv ref
   val native_float_equal_CONV: Conv.conv ref
   val native_float_compare_CONV: Conv.conv ref

   val FLOAT_DATATYPE_CONV: Conv.conv
   val REAL_REDUCE_CONV: Conv.conv
   val ULP_CONV: Conv.conv
   val add_CONV: Conv.conv
   val compare_CONV: Conv.conv
   val div_CONV: Conv.conv
   val equal_CONV: Conv.conv
   val float_compare_CONV: Conv.conv
   val float_round_CONV: Conv.conv
   val greater_equal_CONV: Conv.conv
   val greater_than_CONV: Conv.conv
   val infinity_intro_CONV: Conv.conv
   val largest_CONV: Conv.conv
   val less_equal_CONV: Conv.conv
   val less_than_CONV: Conv.conv
   val mul_CONV: Conv.conv
   val mul_add_CONV: Conv.conv
   val round_CONV: Conv.conv
   val sqrt_CONV: Conv.conv
   val sub_CONV: Conv.conv
   val threshold_CONV: Conv.conv

end
