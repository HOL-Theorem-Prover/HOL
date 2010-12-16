(*---------------------------------------------------------------------------
       Internal interfaces to HOL kernel structures.
 ---------------------------------------------------------------------------*)

signature RawNet =
sig
  type 'a net
  type term = KernelTypes.term

  val empty     : 'a net
  val insert    : term * 'a -> 'a net -> 'a net
  val match     : term -> 'a net -> 'a list
  val index     : term -> 'a net -> 'a list
  val delete    : term * ('a -> bool) -> 'a net -> 'a net
  val filter    : ('a -> bool) -> 'a net -> 'a net
  val union     : 'a net -> 'a net -> 'a net
  val map       : ('a -> 'b) -> 'a net -> 'b net
  val itnet     : ('a -> 'b -> 'b) -> 'a net -> 'b -> 'b
  val size      : 'a net -> int
  val listItems : 'a net -> 'a list
  val enter     : term * 'a -> 'a net -> 'a net  (* for compatibility *)
  val lookup    : term -> 'a net -> 'a list      (* for compatibility *)
end
