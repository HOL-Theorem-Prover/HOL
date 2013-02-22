open HolKernel Parse boolLib bossLib

val _ = new_theory "github112"

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

val _ = overload_on ("+", ``(/\)``);

val ib_def = Define`ib x <=> (x MOD 2 = 0)`;
val _ = add_numeral_form(#"b", SOME "ib")

(* something odd happening here:
val otest_def = Define`
  (otest 0 y = x + y) /\
  (otest (x:num) y = x)
`;
*)

val _ = export_theory()
