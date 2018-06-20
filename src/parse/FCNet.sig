signature FCNet =
sig
  type 'a t
  type term = Term.term

  val empty          : 'a t
  val insert         : term * 'a -> 'a t -> 'a t
  val match          : term -> 'a t -> 'a list
  val itnet          : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val size           : 'a t -> int

  val can_match_term : term -> term -> bool
end
