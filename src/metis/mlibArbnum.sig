(* Copyright (c) Michael Norrish *)

signature mlibArbnum =
sig

  eqtype num

  val zero       : num
  val one        : num
  val two        : num

  val times2     : num -> num
  val div2       : num -> num
  val mod2       : num -> num

  val plus1      : num -> num
  val plus2      : num -> num
  val less1      : num -> num
  val less2      : num -> num

  val toString   : num -> string
  val fromString : string -> num
  val fromInt    : int -> num
  val toInt      : num -> int    (* may raise Overflow *)
  val asList     : num -> int list

  val +          : num * num -> num
  val -          : num * num -> num
  val *          : num * num -> num
  val div        : num * num -> num
  val mod        : num * num -> num
  val divmod     : num * num -> num * num

  val <          : num * num -> bool
  val <=         : num * num -> bool
  val >          : num * num -> bool
  val >=         : num * num -> bool

end
