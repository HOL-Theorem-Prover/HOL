(* -------------------------------------------------------------------------
   Bitstring
   ------------------------------------------------------------------------- *)

signature Bitstring =
sig
   type bitstring = bool list

   val compare: bitstring * bitstring -> order

   val fromBool: bool -> bitstring
   val fromInt: IntInf.int -> bitstring
   val fromNativeInt: int -> bitstring
   val fromNat: Nat.nat -> bitstring
   val fromBinString: string -> bitstring option
   val fromDecString: string -> bitstring option
   val fromHexString: string -> bitstring option
   val fromLit: string -> bitstring option

   val toInt: bitstring -> IntInf.int
   val toNativeInt: bitstring -> int
   val toNat: bitstring -> Nat.nat
   val toBinString: bitstring -> string
   val toDecString: bitstring -> string
   val toHexString: bitstring -> string

   val toList: bitstring -> bool list
   val fromList: bool list -> bitstring

   val bitFieldInsert: Nat.nat * Nat.nat -> bitstring * bitstring -> bitstring

   val zero: Nat.nat -> bitstring
   val one: Nat.nat -> bitstring

   val size: bitstring -> Nat.nat
   val setSize: int -> bitstring -> bitstring

   val replicate: bitstring * Nat.nat -> bitstring
   val bits: Nat.nat * Nat.nat -> bitstring -> bitstring
   val bit: bitstring * Nat.nat -> bool

   val << : bitstring * Nat.nat -> bitstring
   val #>> : bitstring * Nat.nat -> bitstring
   val >>+ : bitstring * Nat.nat -> bitstring
   val + : bitstring * bitstring -> bitstring
   val || : bitstring * bitstring -> bitstring
   val && : bitstring * bitstring -> bitstring
   val ?? : bitstring * bitstring -> bitstring
   val @@ : bitstring * bitstring -> bitstring
end
