signature OmegaMath =
sig
  include Abbrev
  val gcd_eq_check        : conv
  val gcd_le_check        : conv
  val gcd_check           : conv

  val INT_NORM_CONV       : conv
  val NAIVE_INT_NORM_CONV : conv
  val RLIB_INT_NORM_CONV  : conv

  val INT_EQ_CONV         : conv

end;

(*
   [gcd_eq_check tm] returns a theorem equating tm to an improved
   equivalent, or QConv.UNCHANGED, if no improvement is possible.

   tm must be of the form
       0 = r1 + .. + rn
   where rn is a numeral and all of the other ri's are of the form
       (numeral * variable)

   If all of the variables have coefficients divisible by some common
   factor, then this conversion returns an equality either with all
   the coefficients appropriately smaller, or equating it to false
   (which will happen if there the numeral term is of the wrong
   divisibility).

   [gcd_le_check tm] returns a theorem equating tm to an improved
   equivalent (as per gcd_eq_check), or QConv.UNCHANGED, if no
   improvement is possible.

   tm must be of the form
      0 <= (c1 * v1) + (c2 * v2) + .. + (cn * vn) + n

   [gcd_check tm] applies either gcd_eq_check or gcd_le_check depending
   on tm's relational operator.  Fails with HOL_ERR otherwise.

   [INT_NORM_CONV tm] normalises tm, distributing multiplications over
   sums and collecting up variable coefficients.

   [NAIVE_INT_NORM_CONV tm] does the same, and should work well over small
   problem sizes.

   [RLIB_INT_NORM_CONV tm] also normalises, but this time using ringLib's
   normalisation facilities, which tend to come into their own only with
   larger problem sizes.

   [INT_EQ_CONV tm] takes tm (of form t1 = t2), where both t1 and t2 are
   suitable for normalisation by INT_NORM_CONV and proves them equal by
   normalising both sides of the equation.  Returns the equation as
   the theorem; *not* |- (t1 = t2) = T  (which is what things like
   integerRingLib.INT_RING_CONV and AC_CONV do).

*)

