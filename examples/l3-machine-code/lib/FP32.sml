(* -------------------------------------------------------------------------
   Floating-point (for unsupported size)
   ------------------------------------------------------------------------- *)

structure FP32 :> FP =
struct

   type ieee_flags = {DivideByZero: bool,
                      InvalidOp: bool,
                      Overflow: bool,
                      Precision: bool,
                      Underflow: bool}

   val posInf = BitsN.BV (0, 0)
   val negInf = BitsN.BV (0, 0)
   val posZero = BitsN.BV (0, 0)
   val negZero = BitsN.BV (0, 0)
   val sNan = BitsN.BV (0, 0)
   val qNan = BitsN.BV (0, 0)

   fun err s = raise Fail (s ^ ": not supported")

   fun toInt _ = err "toInt"
   fun fromInt _ = err "fromInt"
   fun fromString _ = err "fromString"

   fun isFinite _ = err "isFinite"
   fun isNan _ = err "isNan"
   fun isSignallingNan _ = err "isSignallingNan"
   fun isNormal _ = err "isNormal"
   fun isSubnormal _ = err "isSubnormal"
   fun isIntegral _ = err "isIntegral"
   fun abs _ = err "abs"
   fun neg _ = err "neg"
   fun add _ = err "add"
   fun mul _ = err "mul"
   fun mul_add _ = err "mul_add"
   fun mul_sub _ = err "mul_sub"
   fun sub _ = err "sub"
   fun sqrt _ = err "sqrt"
   fun op div _ = err "div"
   fun equal _ = err "equal"
   fun compare _ = err "compare"
   fun greaterThan _ = err "greaterThan"
   fun greaterEqual _ = err "greaterEqual"
   fun lessThan _ = err "lessThan"
   fun lessEqual _ = err "lessEqual"
   fun roundToIntegral _ = err "lessEqual"

end (* structure FP32 *)
