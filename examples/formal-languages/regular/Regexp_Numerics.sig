signature Regexp_Numerics =
sig

  type regexp = Regexp_Type.regexp
  type word8 = Word8.word;
  type bigint = IntInf.int

  datatype endian = LSB | MSB

  val compare_endian : endian * endian -> order
  val endian2string : endian -> string
  val string2endian : string -> endian option

  datatype encoding = Unsigned | Twos_comp | Zigzag | Sign_mag

  (*---------------------------------------------------------------------------*)
  (* Width in certain encodings                                                *)
  (*---------------------------------------------------------------------------*)

  val width_of : encoding -> bigint -> int
  val interval_width : encoding -> bigint * bigint -> int

  (*---------------------------------------------------------------------------*)
  (* Encoding fns for signed numbers. And their decoders.                      *)
  (*---------------------------------------------------------------------------*)

  val zigzag        : bigint -> bigint
  val sign_mag      : bigint -> bigint
  val undo_zigzag   : bigint -> bigint
  val undo_sign_mag : bigint -> bigint

  (*---------------------------------------------------------------------------*)
  (* numbers to strings                                                        *)
  (*---------------------------------------------------------------------------*)

  val n2l : bigint -> int list
  val bytes_of : int -> bigint -> word8 list

  val iint2string : encoding -> endian -> int -> bigint -> string
  val int2string : int -> string


  (*---------------------------------------------------------------------------*)
  (* strings to numbers                                                        *)
  (*---------------------------------------------------------------------------*)

  val string2iint : encoding -> endian -> string -> bigint
  val string2int : string -> int


  (*---------------------------------------------------------------------------*)
  (* Intervals in various representations                                      *)
  (*---------------------------------------------------------------------------*)

  val num_interval       : endian -> int -> bigint * bigint -> regexp
  val twos_comp_interval : endian -> int -> bigint * bigint -> regexp
  val zigzag_interval    : endian -> int -> bigint * bigint -> regexp
  val sign_mag_interval  : endian -> int -> bigint * bigint -> regexp

  val interval_regexp : encoding -> endian -> int -> bigint * bigint -> regexp
  val test_interval   : encoding -> endian -> int -> bigint * bigint
                         -> regexp * int * (bigint->bool)

(*
  val EVEN : endian -> regexp
  val ODD  : endian -> regexp

  val unsigned_leq : endian -> int -> bigint -> regexp
  val unsigned_gtr : endian -> int -> bigint -> regexp
  val twos_comp_leq : endian -> int -> bigint -> regexp
  val twos_comp_gtr : endian -> int -> bigint  -> regexp
*)

end

