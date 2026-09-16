(* HolRefute by example, 4: assumptions and quantified conjectures. *)

Theory refuteExample04
Libs
  Refute

(* The assumptions in the current goal constrain the counterexample. *)

Theorem predecessor_is_not_the_number:
  0 < n ==> PRE n = n
Proof
  QUICKCHECK_TAC >> cheat
QED

Theorem a_nonempty_list_need_not_start_with_zero:
  xs <> [] ==> HD (xs : num list) = 0
Proof
  REFUTE_TAC >> cheat
QED

(* Explicit quantifiers are handled just like the implicit outer
   quantifiers introduced by free variables in a theorem statement. *)

Theorem adding_any_number_changes_nothing:
  !x y : num. x + y = x
Proof
  QUICKCHECK_TAC >> cheat
QED

Theorem one_witness_does_not_make_a_predicate_universal:
  (?x : num. p x) ==> !x. p x
Proof
  MODEL_REFUTE_TAC >> cheat
QED

(* Here no counterexample exists.  REFUTE_TAC leaves the assumptions and
   conclusion untouched for the proof that follows. *)

Theorem predecessor_is_smaller:
  0 < n ==> PRE n < n
Proof
  REFUTE_TAC >>
  Cases_on `n` >>
  simp []
QED
