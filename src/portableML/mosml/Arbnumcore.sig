signature Arbnumcore =
sig

  eqtype num

  val zero        : num
  val one         : num
  val two         : num

  val times2      : num -> num
  val div2        : num -> num
  val mod2        : num -> num
  val log2        : num -> num

  val plus1       : num -> num
  val plus2       : num -> num
  val less1       : num -> num
  val less2       : num -> num

  val toString    : num -> string
  val toBinString : num -> string
  val toOctString : num -> string
  val toHexString : num -> string

  val fromString  : string -> num (* decimal *)
  val genFromString : StringCvt.radix -> string -> num
  val fromHexString : string -> num
  val fromOctString : string -> num
  val fromBinString : string -> num

  val fromInt     : int -> num    (* raises Overflow if i < 0 *)
  val toInt       : num -> int    (* raises Overflow if n > maxInt *)

  val floor       : real -> num   (* raises Overflow if r < 0 *)
  val toReal      : num -> real

  val asList      : num -> int list

  val +           : num * num -> num
  val -           : num * num -> num
  val *           : num * num -> num
  val pow         : num * num -> num
  val div         : num * num -> num
  val mod         : num * num -> num
  val divmod      : num * num -> num * num
  val gcd         : num * num -> num
  val isqrt       : num -> num

  val <           : num * num -> bool
  val <=          : num * num -> bool
  val >           : num * num -> bool
  val >=          : num * num -> bool

  val compare     : num * num -> order

end
