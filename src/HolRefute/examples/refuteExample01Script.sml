(* ===================================================================== *)
(*  HolRefute by example, 1: proof-script workflow                       *)
(* ===================================================================== *)

Theory refuteExample01
Libs
  Refute

(* HolRefute is normally used while developing a theorem.  A diagnostic
   tactic prints its result and leaves the goal unchanged.  These executable
   examples use [>> cheat] only to admit deliberately false statements after
   the diagnostic has run. *)

Theorem subtraction_does_not_cancel:
  (x : num) - y + y = x
Proof
  REFUTE_TAC >> cheat
QED

(* REFUTE_TAC uses every configured backend.  The specialized tactics are
   useful only when the search method itself matters.  QUICKCHECK_TAC
   restricts this call to executable testing and narrowing. *)

Theorem not_every_list_is_a_palindrome:
  REVERSE (xs : num list) = xs
Proof
  QUICKCHECK_TAC >> cheat
QED

(* MODEL_REFUTE_TAC uses only the finite relational model finder.  Unlike
   executable testing, it can assign a table to an uninterpreted function. *)

Theorem an_arbitrary_function_need_not_return_zero:
  (f : bool -> num) b = 0
Proof
  MODEL_REFUTE_TAC >> cheat
QED

(* Assumptions are part of the search problem. *)

Theorem tail_is_shorter:
  xs <> [] ==> LENGTH (TL (xs : num list)) < LENGTH xs
Proof
  REFUTE_TAC >>
  Cases_on `xs` >> simp []
QED

(* A diagnostic tactic never proves a goal.  If it finds no counterexample,
   it leaves the goal unchanged for the real proof tactic. *)

Theorem subtraction_is_bounded:
  (x : num) - y <= x
Proof
  REFUTE_TAC >>
  simp []
QED
