(* -------------------------------------------------------------------------
   Floating-point
   ------------------------------------------------------------------------- *)

structure FP32 :> FP =
struct

   val size = 32

   val posInf = BitsN.B (0, 0)
   val negInf = BitsN.B (0, 0)
   val posZero = BitsN.B (0, 0)
   val negZero = BitsN.B (0, 0)

   fun err s = raise Fail (s ^ ": not supported")

   fun toLargeReal _ = err "toLargeReal"
   fun fromLargeReal _ _ = err "fromLargeReal"
   fun toInt _ = err "toInt"
   fun fromInt _ = err "fromInt"
   fun toString _ = err "toString"
   fun fromString _ = err "fromString"

   fun isFinite _ = err "isFinite"
   fun isNan _ = err "isNan"
   fun isNormal _ = err "isNormal"
   fun isSubnormal _ = err "isSubnormal"
   fun abs _ = err "abs"
   fun neg _ = err "neg"
   fun abs1985 _ = err "abs1985"
   fun abs2008 _ = err "abs2008"
   fun neg1985 _ = err "neg1985"
   fun neg2008 _ = err "neg2008"
   fun add _ = err "add"
   fun mul _ = err "mul"
   fun sub _ = err "sub"
   fun sqrt _ = err "sqrt"
   fun op div _ = err "div"
   fun equal _ = err "equal"
   fun compare _ = err "compare"
   fun greaterThan _ = err "greaterThan"
   fun greaterEqual _ = err "greaterEqual"
   fun lessThan _ = err "lessThan"
   fun lessEqual _ = err "lessEqual"

end (* structure FP32 *)
