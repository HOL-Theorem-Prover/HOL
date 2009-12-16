signature Arbrat =
sig

  eqtype rat

  type num = Arbnum.num
  type aint = Arbint.int

  val zero       : rat
  val one        : rat
  val two        : rat
  val numerator  : rat -> aint
  val denominator: rat -> num

  val toString   : rat -> string
  val fromString : string -> rat  (* only integral forms *)

  val fromInt    : Int.int -> rat
  val fromAInt   : aint -> rat
  val fromNat    : num -> rat

  val toAInt     : rat -> aint
  val toInt      : rat -> Int.int
  val toNat      : rat -> num

  val +          : (rat * rat) -> rat
  val -          : (rat * rat) -> rat
  val *          : (rat * rat) -> rat
  val /          : (rat * rat) -> rat
  val inv        : rat -> rat
  val negate     : rat -> rat
  val ~          : rat -> rat
  val abs        : rat -> rat

  val <          : rat * rat -> bool
  val <=         : rat * rat -> bool
  val >          : rat * rat -> bool
  val >=         : rat * rat -> bool

  val compare    : rat * rat -> order
  val min        : rat * rat -> rat
  val max        : rat * rat -> rat

  val floor      : rat -> aint
  val ceil       : rat -> aint

  val pp_rat     : HOLPP.ppstream -> rat -> unit

end
