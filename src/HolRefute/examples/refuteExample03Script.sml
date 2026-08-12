(* HolRefute by example, 3: user-defined datatypes and definitions. *)

Theory refuteExample03
Libs
  Refute

Datatype:
  btree = Leaf | Branch btree num btree
End

Definition insert_def:
  (insert x Leaf = Branch Leaf x Leaf) /\
  (insert x (Branch l v r) =
     if x < v then Branch (insert x l) v r
     else if v < x then Branch l v (insert x r)
     else Branch l v r)
End

Definition flatten_def:
  (flatten Leaf = []) /\
  (flatten (Branch l v r) = flatten l ++ [v] ++ flatten r)
End

(* Derived generators understand ordinary datatype declarations and
   recursive definitions. *)

Theorem inserting_twice_always_changes_a_tree:
  insert x (insert x t) <> insert x t
Proof
  QUICKCHECK_TAC >> cheat
QED

Theorem flattening_an_insert_only_appends:
  flatten (insert x t) = flatten t ++ [x]
Proof
  QUICKCHECK_TAC >> cheat
QED

Datatype:
  point = <| px : num; py : num |>
End

Theorem every_point_is_on_an_axis:
  p.px = 0 \/ p.py = 0
Proof
  QUICKCHECK_TAC >> cheat
QED

Theorem every_optional_value_is_absent:
  (v : num option) = NONE
Proof
  QUICKCHECK_TAC >> cheat
QED

(* Simplification reduces the negated pair law to a constant formula.  The
   model finder can therefore cover the whole space immediately; its
   NoCounterexample result is decisive, so REFUTE_TAC does not wait for the
   other backends before returning the unchanged goal. *)

Theorem swapping_a_pair_twice:
  (SND (SND p, FST p), FST (SND p, FST p)) = (p : num # bool)
Proof
  REFUTE_TAC >>
  Cases_on `p` >>
  simp []
QED
