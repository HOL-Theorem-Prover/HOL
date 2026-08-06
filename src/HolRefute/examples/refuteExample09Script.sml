(* HolRefute by example, 9: finite model finding. *)

Theory refuteExample09
Ancestors
  refute
Libs
  Refute

open Refute

(* MODEL_REFUTE_TAC invokes only the Kodkod-backed finite model finder.
   It can assign finite interpretations to arbitrary functions, sets, and
   relations rather than requiring executable definitions. *)

Theorem an_arbitrary_function_need_not_be_constant:
  (f : bool -> bool) b = f T
Proof
  MODEL_REFUTE_TAC >> cheat
QED

Theorem an_arbitrary_set_need_not_be_universal:
  (s : bool set) = UNIV
Proof
  MODEL_REFUTE_TAC >> cheat
QED

Theorem an_arbitrary_relation_need_not_be_transitive:
  (r : bool -> bool -> bool) x y /\ r y z ==> r x z
Proof
  MODEL_REFUTE_TAC >> cheat
QED

Theorem one_member_does_not_make_a_set_universal:
  (?x : bool. x IN s) ==> !x. x IN s
Proof
  MODEL_REFUTE_TAC >> cheat
QED

(* As with every refutation tactic, a search without a countermodel leaves
   the goal for an actual proof tactic. *)

Theorem membership_in_the_universal_set:
  !x : bool. x IN UNIV
Proof
  MODEL_REFUTE_TAC >>
  simp []
QED
