structure SSE :> SSE =
struct

type ieee_flags = {DivideByZero: bool,
                   InvalidOp: bool,
                   Overflow: bool,
                   Precision: bool,
                   Underflow: bool}

fun ieee_flags_DivideByZero_rupd
  ({DivideByZero, InvalidOp, Overflow = overflow,
    Precision, Underflow} : ieee_flags, b) =
  {DivideByZero = b,
   InvalidOp = InvalidOp,
   Overflow = overflow,
   Precision = Precision,
   Underflow = Underflow} : ieee_flags

fun ieee_flags_InvalidOp_rupd
  ({DivideByZero, InvalidOp, Overflow = overflow,
    Precision, Underflow} : ieee_flags, b) =
  {DivideByZero = DivideByZero,
   InvalidOp = b,
   Overflow = overflow,
   Precision = Precision,
   Underflow = Underflow}

fun ieee_flags_Overflow_rupd
  ({DivideByZero, InvalidOp, Overflow = overflow,
    Precision, Underflow} : ieee_flags, b) =
  {DivideByZero = DivideByZero,
   InvalidOp = InvalidOp,
   Overflow = b,
   Precision = Precision,
   Underflow = Underflow}

fun ieee_flags_Precision_rupd
  ({DivideByZero, InvalidOp, Overflow = overflow,
    Precision, Underflow} : ieee_flags, b) =
  {DivideByZero = DivideByZero,
   InvalidOp = InvalidOp,
   Overflow = overflow,
   Precision = b,
   Underflow = Underflow}

fun ieee_flags_Underflow_rupd
  ({DivideByZero, InvalidOp, Overflow = overflow,
    Precision, Underflow} : ieee_flags, b) =
  {DivideByZero = DivideByZero,
   InvalidOp = InvalidOp,
   Overflow = overflow,
   Precision = Precision,
   Underflow = b}

end
