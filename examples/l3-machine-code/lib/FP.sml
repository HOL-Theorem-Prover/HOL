(* -------------------------------------------------------------------------
   Floating-point
   ------------------------------------------------------------------------- *)

signature FP =
sig
   val abs: BitsN.nbit -> BitsN.nbit
   val add: IEEEReal.rounding_mode * (BitsN.nbit * BitsN.nbit) -> BitsN.nbit
   val compare: BitsN.nbit * BitsN.nbit -> IEEEReal.real_order
   val div: IEEEReal.rounding_mode * (BitsN.nbit * BitsN.nbit) -> BitsN.nbit
   val equal: BitsN.nbit * BitsN.nbit -> bool
   val fromInt: IEEEReal.rounding_mode * IntInf.int -> BitsN.nbit
   val fromString: string -> BitsN.nbit option
   val greaterEqual: BitsN.nbit * BitsN.nbit -> bool
   val greaterThan: BitsN.nbit * BitsN.nbit -> bool
   val isFinite: BitsN.nbit -> bool
   val isNan: BitsN.nbit -> bool
   val isNormal: BitsN.nbit -> bool
   val isSubnormal: BitsN.nbit -> bool
   val lessEqual: BitsN.nbit * BitsN.nbit -> bool
   val lessThan: BitsN.nbit * BitsN.nbit -> bool
   val mul: IEEEReal.rounding_mode * (BitsN.nbit * BitsN.nbit) -> BitsN.nbit
   val mul_add:
     IEEEReal.rounding_mode * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)) ->
     BitsN.nbit
   val mul_sub:
     IEEEReal.rounding_mode * (BitsN.nbit * (BitsN.nbit * BitsN.nbit)) ->
     BitsN.nbit
   val neg: BitsN.nbit -> BitsN.nbit
   val negInf: BitsN.nbit
   val negZero: BitsN.nbit
   val posInf: BitsN.nbit
   val posZero: BitsN.nbit
   val sqrt: IEEEReal.rounding_mode * BitsN.nbit -> BitsN.nbit
   val sub: IEEEReal.rounding_mode * (BitsN.nbit * BitsN.nbit) -> BitsN.nbit
   val toInt: IEEEReal.rounding_mode * BitsN.nbit -> IntInf.int option
end
