open HolKernel Parse boolLib bossLib

val _ = new_theory "theory1"

val _ = register_hook("magnus_bug",
                      (fn TheoryDelta.ExportTheory _ => delete_const "h"
                        | _ => ()))

val f_def = Define`f x = x + 1`;
val _ = export_rewrites ["f_def"]

val g_def = Define`g n m = f (n * m)`;
val _ = export_rewrites ["g_def"]

val i = EVAL ``g 3 4``
             |> concl |> rhs |> numSyntax.dest_numeral
             |> Arbnum.toInt
             |> assert (equal 13)

val _ = delete_const "g";

val h_def = Define`
  h n = n + 1
`;

val f2_def = Define`f2 n = n + 1`;
val _ = export_rewrites ["f2_def"]

val f2_SUC = store_thm(
  "f2_SUC",
  ``f2 = SUC``,
  REWRITE_TAC [arithmeticTheory.ADD1, f2_def, FUN_EQ_THM])

val _ = delete_binding "f2_def"

val f3_def = Define`f3 n = n + 1`;
val f3_def = Define`f3 n = n + 2`;
val f3_def = Define`f3 n = n + 3`;
val f3_def = Define`f3 n = n + 4`;

val g3_def = Define`g3 n = f3 (n + 1)`
val f3_def = Define`f3 n = n + 5`;


val _ = export_theory();
