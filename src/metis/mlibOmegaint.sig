(* Copyright (c) Michael Norrish *)

signature mlibOmegaint = 
sig

  type int

  val zero : int
  val one  : int

  val eq : int * int -> bool

  val toString   : int -> string
  val fromString : string -> int option

  val fromInt : Int.int -> int
  val toInt   : int -> Int.int

  val +      : (int * int) -> int
  val -      : (int * int) -> int
  val *      : (int * int) -> int
  val div    : (int * int) -> int
  val mod    : (int * int) -> int
  val quot   : (int * int) -> int
  val rem    : (int * int) -> int
  val ~      : int -> int

  val <  : int * int -> bool
  val <= : int * int -> bool
  val >  : int * int -> bool
  val >= : int * int -> bool

  val abs : int -> int

  val compare : int * int -> order
  val min : int * int -> int
  val max : int * int -> int


  
  val hash : int -> Int.int
  val gcd  : int * int -> int
end
