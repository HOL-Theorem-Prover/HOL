signature Regexp_Numerics =
sig

  type regexp = Regexp_Type.regexp
		      
  datatype direction = LSB | MSB

  val dir2string : direction -> string
  val string2dir : string -> direction option

  val unsigned_width  : IntInf.int -> int
  val twos_comp_width  : IntInf.int -> int
  val twos_comp_interval_width  : IntInf.int * IntInf.int -> int

  val bytes_of : int -> IntInf.int -> Word8.word list
  val int2string : int -> int -> string

  val num_interval : direction -> int -> IntInf.int -> IntInf.int -> regexp
  val twos_comp_interval : direction -> int -> IntInf.int -> IntInf.int -> regexp
(*
  val zigzag_interval : direction -> int -> IntInf.int -> IntInf.int -> regexp
  val signmag_interval : direction -> int -> IntInf.int -> IntInf.int -> regexp

  val even_lsb : regexp
  val even_msb : regexp
  val odd_lsb : regexp
  val odd_msb : regexp

  val unsigned_leq : direction -> int -> IntInf.int -> regexp
  val unsigned_gtr : direction -> int -> IntInf.int -> regexp
  val twos_comp_leq : direction -> int -> IntInf.int -> regexp
  val twos_comp_gtr : direction -> int -> IntInf.int -> regexp
*)

end
    
