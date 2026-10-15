(* HolRefute by case study: AVL-tree rebalancing, adapted from Isabelle's
   Quickcheck_Narrowing_Examples.thy. *)

Theory refuteAVL
Ancestors
  list
Libs
  Refute

Datatype:
  avl = AEmp | ANd num avl avl num
End

(* ANd stores the data, left and right subtrees, and a cached height. *)

Definition vheight_def:
  vheight AEmp = 0 /\
  vheight (ANd x l r h) = MAX (vheight l) (vheight r) + 1
End

Definition vht_def:
  vht AEmp = 0 /\
  vht (ANd x l r h) = h
End

Definition velems_def:
  velems AEmp = [] /\
  velems (ANd x l r h) = x :: (velems l ++ velems r)
End

Definition vord_def:
  vord AEmp = T /\
  vord (ANd x l r h) =
    (EVERY (\y. y < x) (velems l) /\
     EVERY (\y. x < y) (velems r) /\ vord l /\ vord r)
End

Definition vmk_def:
  vmk x l r = ANd x l r (MAX (vht l) (vht r) + 1)
End

Definition vlbal0_def:
  vlbal0 n l r =
    case l of
      AEmp => AEmp
    | ANd ln ll lr lh =>
        if vht ll < vht lr then
          case lr of
            AEmp => AEmp
          | ANd lrn lrl lrr lrh =>
              vmk lrn (vmk ln ll lrr) (vmk n lrl r)
        else vmk ln ll (vmk n lr r)
End

Definition vlbal_def:
  vlbal n l r =
    case l of
      AEmp => AEmp
    | ANd ln ll lr lh =>
        if vht ll < vht lr then
          case lr of
            AEmp => AEmp
          | ANd lrn lrl lrr lrh =>
              vmk lrn (vmk ln ll lrl) (vmk n lrr r)
        else vmk ln ll (vmk n lr r)
End

(* The diagnostic tactic is followed by cheat in deliberately false
   conjectures so that the counterexample remains visible in the build. *)

Theorem rebalancing_preserves_the_order:
  vord (ANd n l (ANd rn AEmp AEmp rh) h) /\
  vheight l = vheight (ANd rn AEmp AEmp rh) + 2 ==>
  vord (vlbal0 n l (ANd rn AEmp AEmp rh))
Proof
  NARROWING_TAC >> cheat
QED

Theorem the_fixed_rebalancing_preserves_the_order:
  vord (ANd n l r h) /\ vheight l = vheight r + 2 ==>
  vord (vlbal n l r)
Proof
  QUICKCHECK_TAC >>
  Cases_on `l`
  >- simp [vheight_def]
  >> Cases_on `vht a < vht a0`
  >- (Cases_on `a0`
      >- rw [vlbal_def, vord_def]
      >> rw [vlbal_def, vmk_def, vord_def, velems_def,
             EVERY_APPEND, EVERY_MEM]
      >> metis_tac [arithmeticTheory.LESS_TRANS])
  >> rw [vlbal_def, vmk_def, vord_def, velems_def,
         EVERY_APPEND, EVERY_MEM]
  >> metis_tac [arithmeticTheory.LESS_TRANS]
QED

(* A full insertion theorem would also track truthful cached heights and
   AVL balance.  That larger development is outside this rotation-local
   example; order preservation itself needs neither invariant. *)
