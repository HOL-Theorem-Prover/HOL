(* HolRefute by example, 2: choosing a diagnostic tactic. *)

Theory refuteExample02
Libs
  Refute

(* In an interactive proof, inspect the report printed by the diagnostic
   tactic.  [>> cheat] only keeps these deliberately false examples
   buildable. *)

(* QUICKCHECK_TAC runs executable testing and narrowing. *)

Theorem an_even_sum_does_not_force_an_even_left_addend:
  EVEN (x + y) ==> EVEN x
Proof
  QUICKCHECK_TAC >> cheat
QED

(* MODEL_REFUTE_TAC runs the Kodkod-backed finite model finder.  It is
   useful when the conjecture contains an arbitrary function or relation
   that cannot simply be evaluated. *)

Theorem an_arbitrary_relation_need_not_be_symmetric:
  (r : num -> num -> bool) x y ==> r y x
Proof
  MODEL_REFUTE_TAC >> cheat
QED

(* NARROWING_TAC selects only symbolic narrowing.  It is useful when a
   partial counterexample is more informative than a fully generated one. *)

Theorem every_list_is_nonempty:
  (xs : num list) <> []
Proof
  NARROWING_TAC >> cheat
QED

(* REFUTE_TAC tries all configured backends, so it is the usual first choice.
   A refutation tactic is diagnostic: it never closes a true goal. *)

Theorem addition_commutes:
  x + y = y + (x : num)
Proof
  REFUTE_TAC >>
  simp [arithmeticTheory.ADD_COMM]
QED
