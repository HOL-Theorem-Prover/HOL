signature OmegaMath =
sig
  include Abbrev
  val find_summand          : term -> term -> term
  val gcd_eq_check          : conv
  val gcd_le_check          : conv
  val gcd_check             : conv

  val addzero               : conv

  val INT_NORM_CONV         : conv
  val NAIVE_INT_NORM_CONV   : conv
  val RLIB_INT_NORM_CONV    : conv

  val INT_EQ_CONV           : conv

  val SORT_AND_GATHER1_CONV : conv
  val SORT_AND_GATHER_CONV  : conv
  val S_AND_G_MULT          : conv

  val MOVE_VCOEFF_TO_FRONT  : term -> conv
  val NEG_SUM_CONV          : conv
  val NORMALISE_MULT        : conv

  val leaf_normalise        : conv
  val sum_normalise         : conv
end;

(*

   [find_summand v tm] finds the summand involving variable v in tm.
   Raise a HOL_ERR if it's not there.  tm must be a left-associated
   sum with one numeral in the rightmost position.

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

   [addzero t] if t (of integer type and not a numeral itself) does
   not have a numeral as its 'rand, then return thm |- t = t + 0,
   otherwise ALL_CONV.

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

   [SORT_AND_GATHER1_CONV tm] performs one step of an "insertion
   sort"; modifying a term of the form x + y, with x a normalised sum,
   and y a singleton summand, so that y is inserted into x, merging
   with any appropriate other summands, and possibly cancelling others
   out.

   [SORT_AND_GATHER_CONV tm] performs all the steps of the insertion
   sort, collecting up variable coefficients and producing a left
   associated term with variables appearing in sorted order.

   [S_AND_G_MULT tm] performs a sort-and-gather step, and also copes
   with distributing multiplications over sub-summands, as long as the
   constant to be multiplied through is on the left side of the
   multiplication.

   [MOVE_VCOEFF_TO_FRONT v tm] turns
      c1 * v1 + ... + c * v + ... cn * vn + n
   into
      c * v + (c1 * v1 + ... + cn * vn + n)

   [NEG_SUM_CONV] simplifies ~(c1*v1 + c2 * v2 .. + cn * vn + n), by
   pushing the negation inwards.

   [NORMALISE_MULT tm] normalises the multiplicative term tm,
   gathering up coefficients, and turning it into the form n * (v1 *
   v2 * ... vn), where n is a numeral and the v's are the variables
   in the term, sorted into the order specified by Term.compare.
   Works over both :num and :int.

   [leaf_normalise t] normalises a "leaf term" t (a relational
   operator over integer values) to either an equality, a <= or a
   disjunction of two normalised <= leaves.  (The latter happens if
   called onto normalise ~(x = y)).

   [sum_normalise t] normalises a term of type :int into the standard
   Omega normal form, where the resulting term is of the form
       c1 * v1 + c2 * v2 + c3 * v3 + ... + cn * vn + c
   where the c is always present and maybe 0.

*)

