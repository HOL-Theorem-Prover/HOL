(* HolRefute by example, 10: structured finite models. *)

Theory refuteExample10
Libs
  Refute

Datatype:
  node = RedNode | GreenNode | BlueNode
End

(* Datatypes become finite signatures in the relational encoding. *)

Theorem every_node_has_the_same_colour:
  n = RedNode
Proof
  MODEL_REFUTE_TAC >> cheat
QED

Inductive reaches:
  (!r x y. r x y ==> reaches r x y) /\
  (!r x y z. r x y /\ reaches r y z ==> reaches r x z)
End

Theorem reachability_need_not_be_symmetric:
  reaches r x y ==> reaches r y x
Proof
  MODEL_REFUTE_TAC >> cheat
QED

(* Nested quantifiers let the finder introduce witnesses and tables for
   predicates that have no executable definition. *)

Theorem a_nonempty_predicate_is_universal:
  (?x : node. p x) ==> !x. p x
Proof
  MODEL_REFUTE_TAC >> cheat
QED

Theorem two_arbitrary_functions_agree:
  (f : node -> bool) n = g n
Proof
  MODEL_REFUTE_TAC >> cheat
QED

Theorem relational_implication_is_valid:
  (!x : node. p x ==> q x) ==> p n ==> q n
Proof
  MODEL_REFUTE_TAC >>
  metis_tac []
QED
