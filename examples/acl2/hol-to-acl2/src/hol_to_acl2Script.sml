(*===========================================================================*)
(* Support for translation to ACL2(zfc)                                      *)
(*===========================================================================*)

Theory hol_to_acl2
Ancestors
  pred_set arithmetic list

Definition THM_def:
  THM (x:bool) (y:bool) = T
End

Definition GOAL_def:
  GOAL (x:bool) (y:bool) = T
End

Definition SPEC_def:
  SPEC x (y:bool) = T
End

Theorem suc_thm:
  ∀m. SUC m = 1 + m
Proof
  decide_tac
QED

Definition COMMA_def:
  COMMA x y = (x,y)
End
