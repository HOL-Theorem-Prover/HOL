signature numML =
sig

  type num = Arbnum.num

  val zero : num
  val one  : num
  val two  : num

  val pre  : num -> num
  val +    : num -> num -> num
  val -    : num -> num -> num
  val *    : num -> num -> num
  val exp  : num -> num -> num
  val div  : num -> num -> num
  val mod  : num -> num -> num

  val <    : num -> num -> bool
  val >    : num -> num -> bool
  val <=   : num -> num -> bool
  val >=   : num -> num -> bool

  val even : num -> bool
  val odd  : num -> bool
  val fact : num -> num
  val funpow : ('a -> 'a) -> num -> 'a -> 'a
  val While : ('a -> bool) -> ('a -> 'a) -> 'a -> 'a
  val least : (num -> bool) -> num

  val toString : num -> string
  val fromString : string -> num

end
