signature Nat =
sig
   (* Type should be abstract when not using SMLExport, i.e.
   eqtype nat
   *)

   type nat = int

   val compare: nat * nat -> order

   val fromBool: bool -> nat
   val fromInt: int -> nat
   val fromString: string -> nat option
   val fromBinString: string -> nat option
   val fromHexString: string -> nat option
   val fromLit: string -> nat option

   val toInt: nat -> int
   val toWord: nat -> word
   val toString: nat -> string
   val toBinString: nat -> string
   val toHexString: nat -> string

   val zero: nat
   val one: nat
   val two: nat

   val suc: nat -> nat
   val pred: nat -> nat

   val log2: nat -> nat

   val < : nat * nat -> bool
   val <= : nat * nat -> bool
   val > : nat * nat -> bool
   val >= : nat * nat -> bool

   val * : nat * nat -> nat
   val + : nat * nat -> nat
   val - : nat * nat -> nat
   val pow: nat * nat -> nat
   val div: nat * nat -> nat
   val mod: nat * nat -> nat
   val min: nat * nat -> nat
   val max: nat * nat -> nat
end
