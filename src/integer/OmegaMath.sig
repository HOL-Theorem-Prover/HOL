signature OmegaMath =
sig
  include Abbrev
  val gcd_eq_check : conv
  val gcd_le_check : conv
  val gcd_check    : conv
  val INT_NORM_CONV: conv

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

*)

