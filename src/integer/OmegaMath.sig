signature OmegaMath =
sig
  include Abbrev
  val find_summand               : term -> term -> term
  val gcd_eq_check               : conv
  val gcd_le_check               : conv
  val gcd_check                  : conv

  val addzero                    : conv

  val SORT_AND_GATHER1_CONV      : conv
  val SORT_AND_GATHER_CONV       : conv
  val S_AND_G_MULT               : conv

  val MOVE_VCOEFF_TO_FRONT       : term -> conv
  val NEG_SUM_CONV               : conv
  val NORMALISE_MULT             : conv

  val leaf_normalise             : conv
  val sum_normalise              : conv
  val PRENEX_CONV                : conv
  val cond_removal               : conv

  val eliminate_positive_divides : conv
  val eliminate_negative_divides : conv
  val calculate_range_disjunct   : conv

  val OmegaEq                    : conv
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

   [PRENEX_CONV t] normalises t by pulling quantifiers to the front, over
   boolean connectives such as ~ /\ \/ and also if-then-else, as long as
   the quantifier is not in the guard of the latter.

   [cond_removal t] removes those conditional expressions from t that repeat
   their guards, and introduces a case split (i.e., disjunctions) at the
   top level of the term to reflect this.   Don't use if you want to generate
   CNF.

   [eliminate_positive_divides t] where t is a term of the form
       ?x1 .. xn. body
   where body is a conjunction of leaves, possibly including
   divisibility relations (negated or positive).  This function
   writes away those (positive) divisibility relations of the form
       d | exp
   where exp includes at least one variable from x1 .. xn.

   [eliminate_negative_divides t] where t is a term of the form
       ?x1 .. xn. body
   where body is a conjunction of leaves, possibly including
   divisibility relations (negated or positive).  This function writes
   away those negated divisibility relations of the form
       ~(d | exp)
   where exp includes at least one variable from x1 .. xn.  It
   introduces case splits in the body (at least where d is not 2), and
   pushes the existential variables over the resulting disjunctions.
   It doesn't eliminate the positive divisibility terms that result.

   [calculate_range_disjunct t] where t is of the form
       ?i. (lo <= i /\ i <= hi) /\ ...
   and lo and hi are integer literal.  Transforms this into an
   appropriate number of disjuncts (or possibly false, if hi < lo, of
   the form
       P(lo) \/ P (lo + 1) \/ .. P (hi)
   but where the additions (lo + 1 etc) are reduced to literals

   [OmegaEq t] simplifies an existentially quantified Presburger term,
   (or returns QConv.UNCHANGED) by using the equality elimination
   procedure described in section 2.2 of Pugh's CACM paper.

   The term t should be of the form
      ?v1..vn. body
   If the conversion is to do anything other than return UNCHANGED,
   there should be a Omega-normalised equality in (strip_conj body).


*)

