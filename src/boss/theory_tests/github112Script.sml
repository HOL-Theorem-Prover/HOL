Theory github112

Definition f1_def:   (f1 x y = case (x, y) of (0, _) => SOME 1 | (_,_) => NONE)
End
Definition f2_def:   (f2 x y = case (x, y) of (0, _) => SOME 1 | _ => NONE)
End
Definition f3_def:   f3 x = (case [] of _ => 1) + (case 2 of _ => 2)
End
Definition f4_def:   f4 x = (case x of [] => 0 | [_] => 1 | _ => 2)
End

val fg_def = tDefine "fg" `
  (f x = x + 1 + g (x > 4)) /\
  (g x = if x then f 0 else 1)
` (WF_REL_TAC `measure (\x. case x of INL n => n + 1 | INR T => 2 | INR F => 0)`)

Datatype: foo = C1 of num | C2 of bool
End

Definition h_def:  (h (C1 x) = (x < 2)) /\ (h (C2 x) = ~x)
End

Definition test_def:
  (test n 0 = n) /\
  (test m _ = SUC m)
End

