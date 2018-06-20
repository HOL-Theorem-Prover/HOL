signature SSE =
sig
  type ieee_flags = {DivideByZero: bool,
                     InvalidOp: bool,
                     Overflow: bool,
                     Precision: bool,
                     Underflow: bool}

  val ieee_flags_DivideByZero_rupd: ieee_flags * bool -> ieee_flags
  val ieee_flags_InvalidOp_rupd: ieee_flags * bool -> ieee_flags
  val ieee_flags_Overflow_rupd: ieee_flags * bool -> ieee_flags
  val ieee_flags_Precision_rupd: ieee_flags * bool -> ieee_flags
  val ieee_flags_Underflow_rupd: ieee_flags * bool -> ieee_flags
end
