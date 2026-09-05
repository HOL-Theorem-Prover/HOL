(* HolRefute by example, 13: machine words. *)

Theory refuteExample13
Ancestors
  words
Libs
  Refute wordsLib

(* A word of concrete width is a native carrier for the model finder:
   width w means exactly 2^w values, and every operation wraps into
   them.  Counterexamples are reported in the surface literal form. *)

Theorem incrementing_a_word_never_reaches_zero:
  (w : word3) + 1w <> 0w
Proof
  MODEL_REFUTE_TAC >> cheat
QED

Theorem multiplication_by_two_never_wraps:
  (w : word3) * 2w <> 0w
Proof
  MODEL_REFUTE_TAC >> cheat
QED

(* The signed and unsigned orders differ once the sign bit is set. *)

Theorem every_word_is_at_least_zero:
  (0w : word3) <= w
Proof
  MODEL_REFUTE_TAC >> cheat
QED

(* A shift counts in [num], not in the word, so a shift goal also asks
   the search to size the [num] carrier. *)

Theorem shifting_left_never_gives_zero:
  (w : word3) << 1 <> 0w
Proof
  MODEL_REFUTE_TAC >> cheat
QED

(* A width left as a type variable is instantiated to small numeral
   widths, so a width-polymorphic conjecture is refuted at a concrete
   one.  This needs no model finder: the instantiated goal is
   executable. *)

Theorem incrementing_a_word_of_any_width_never_reaches_zero:
  (w : 'a word) + 1w <> 0w
Proof
  REFUTE_TAC >> cheat
QED

(* Not every conjecture is false.  The carrier is exact, so a search
   that finds no model over it has covered every word of that width and
   leaves the goal for an actual proof. *)

Theorem addition_commutes:
  !w v : word3. w + v = v + w
Proof
  MODEL_REFUTE_TAC >>
  blastLib.BBLAST_TAC
QED

(* Operations that change a word's width, and the bit-permuting
   remainder, are not encoded.  The search names the operation instead
   of guessing, so an inconclusive report is never evidence that the
   conjecture holds. *)

Theorem widening_a_word_is_not_encoded:
  w2w (w : word3) = (0w : word4)
Proof
  MODEL_REFUTE_TAC >> cheat
QED
