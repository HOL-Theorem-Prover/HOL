(* HolRefute by example, 8: developing and repairing statements. *)

Theory refuteExample08
Ancestors
  refute
Libs
  Refute

open Refute

(* Refuting an early draft often reveals a missing hypothesis. *)

Theorem an_unrestricted_head_is_zero:
  HD (xs : num list) = 0
Proof
  REFUTE_TAC >> cheat
QED

Theorem the_repaired_head_statement:
  xs = [0] ==> HD (xs : num list) = 0
Proof
  REFUTE_TAC >>
  simp []
QED

(* Conversely, a premise may be unnecessary.  The diagnostic leaves a
   true goal alone; the proof shows that [p] is not used. *)

Theorem an_unnecessary_assumption:
  p ==> q ==> q
Proof
  REFUTE_TAC >>
  simp []
QED

Theorem a_guard_that_is_still_too_weak:
  xs <> [] ==> LENGTH (xs : num list) = 1
Proof
  QUICKCHECK_TAC >> cheat
QED

Theorem a_sufficient_length_guard:
  LENGTH (xs : num list) = 1 ==> xs <> []
Proof
  REFUTE_TAC >>
  Cases_on `xs` >>
  simp []
QED
