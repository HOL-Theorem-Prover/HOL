signature Arbintcore =
sig

  eqtype int

  type num = Arbnumcore.num

  val zero       : int
  val one        : int
  val two        : int

  val toString   : int -> string
  val fromString : string -> int

  val fromInt    : Int.int -> int
  val fromNat    : num -> int
  val toInt      : int -> Int.int
  val toNat      : int -> num

  val +          : (int * int) -> int
  val -          : (int * int) -> int
  val *          : (int * int) -> int
  val div        : (int * int) -> int
  val mod        : (int * int) -> int
  val quot       : (int * int) -> int
  val rem        : (int * int) -> int
  val divmod     : (int * int) -> (int * int)
  val quotrem    : (int * int) -> (int * int)
  val negate     : int -> int
  val ~          : int -> int
  val abs        : int -> int

  val <          : int * int -> bool
  val <=         : int * int -> bool
  val >          : int * int -> bool
  val >=         : int * int -> bool

  val compare    : int * int -> order
  val min        : int * int -> int
  val max        : int * int -> int

end
