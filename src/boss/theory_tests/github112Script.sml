open HolKernel Parse boolLib bossLib

val _ = new_theory "github112"

val f1_def = Define `(f1 x y = case (x, y) of (0, _) => SOME 1 | (_,_) => NONE)`
val f2_def = Define `(f2 x y = case (x, y) of (0, _) => SOME 1 | _ => NONE)`
val f3_def = Define `f3 x = (case [] of _ => 1) + (case 2 of _ => 2)`
val f4_def = Define `f4 x = (case x of [] => 0 | [_] => 1 | _ => 2)`

val fg_def = tDefine "fg" `
  (f x = x + 1 + g (x > 4)) /\
  (g x = if x then f 0 else 1)
` (WF_REL_TAC `measure (\x. case x of INL n => n + 1 | INR T => 2 | INR F => 0)`)

val _ = Hol_datatype`foo = C1 of num | C2 of bool`

val h_def = Define`(h (C1 x) = x < 2) /\ (h (C2 x) = ~x)`;

val test_def = Define`
  (test n 0 = n) /\
  (test m _ = SUC m)
`;

val _ = export_theory()
