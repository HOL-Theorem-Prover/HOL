(* HolRefute by example, 5: predicates in assumptions. *)

Theory refuteExample05
Libs
  Refute

Inductive even_rel:
  even_rel 0 /\
  (!n. even_rel n ==> even_rel (SUC (SUC n)))
End

(* An inductive predicate is not directly executable, so QuickCheck may be
   inconclusive.  The diagnostic then leaves the goal for the real proof. *)

Theorem generated_even_numbers_are_even:
  even_rel n ==> EVEN n
Proof
  QUICKCHECK_TAC >>
  Induct_on `even_rel n` >>
  simp [arithmeticTheory.EVEN]
QED

Definition small_path_def:
  small_path (x : num) y <=> x < y /\ y <= 3
End

Theorem every_path_from_zero_ends_at_one:
  small_path 0 y ==> y = 1
Proof
  QUICKCHECK_TAC >> cheat
QED

Definition sortedp_def:
  (sortedp [] = T) /\
  (sortedp [x : num] = T) /\
  (sortedp (x :: y :: xs) = (x <= y /\ sortedp (y :: xs)))
End

Theorem every_sorted_list_has_at_most_three_elements:
  sortedp xs ==> LENGTH xs <= 3
Proof
  QUICKCHECK_TAC >> cheat
QED
