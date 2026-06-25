(* A small approximate-membership filter over terms, used by
   Cache.sml's hypinfo subset operator as a cheap pre-check.
   `maybeSubset (a, b)` returns false only when a definitely cannot
   be a subset of b (the bloom of a has a bit that b's bloom lacks);
   on false the caller can short-circuit, on true the caller must
   still consult the real set structure. *)
signature BloomApprox =
sig
  type t
  val empty       : t
  val from_term   : Term.term -> t
  val union       : t * t -> t
  val maybeSubset : t * t -> bool
end
