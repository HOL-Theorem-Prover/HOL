signature Rationals =
sig
  type int = Arbint.int

  exception Rat_form
  exception Rat_inv
  exception Rat_div
  eqtype rat

  val Rat : (int * int) -> rat
  val Numerator : rat -> int
  val Denominator : rat -> int
  val rat_inv : rat -> rat
  val rat_plus : rat -> rat -> rat
  val rat_minus : rat -> rat -> rat
  val rat_mult : rat -> rat -> rat
  val rat_div : rat -> rat -> rat
  val print_rat : rat -> unit
  val rat_of_int : int -> rat
  val lower_int_of_rat : rat -> int
  val upper_int_of_rat : rat -> int
  val rat_zero : rat
  val rat_one : rat
  val rat_less : rat -> rat -> bool
end
