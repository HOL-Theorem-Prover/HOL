(* -------------------------------------------------------------------------
   Floating-point
   ------------------------------------------------------------------------- *)

signature FP64 =
sig
   val abs: BitsN.nbit -> BitsN.nbit
   val add: IEEEReal.rounding_mode * (BitsN.nbit * BitsN.nbit) -> BitsN.nbit
   val bitsToReal: BitsN.nbit -> real
   val equal: BitsN.nbit * BitsN.nbit -> bool
   val fromString: string -> BitsN.nbit option
   val isNan: BitsN.nbit -> bool
   val lessThan: BitsN.nbit * BitsN.nbit -> bool
   val mul: IEEEReal.rounding_mode * (BitsN.nbit * BitsN.nbit) -> BitsN.nbit
   val neg: BitsN.nbit -> BitsN.nbit
   val realToBits: real -> BitsN.nbit
   val sub: IEEEReal.rounding_mode * (BitsN.nbit * BitsN.nbit) -> BitsN.nbit
end
