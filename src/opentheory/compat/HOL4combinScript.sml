open HolKernel boolLib bossLib OpenTheoryMap OpenTheoryFunctionTheory lcsymtacs

val Thy = "HOL4combin"
val _ = new_theory Thy

val n = ref 0;
fun export (tm,tac) =
  store_thm(("th"^Int.toString(!n)),tm,tac)
  before n := !n+1

val res0 = export(``I = S K (K:'a->'a->'a)``,
  PURE_REWRITE_TAC[th18] >> REFL_TAC)
  (* DB.match["OpenTheoryFunction"]``I`` *)
val res1 = export(``$o f g = \x. f ( g x)``,
  PURE_REWRITE_TAC[th22] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  REFL_TAC)
  (* DB.match["OpenTheoryFunction"]``$o`` *)

val _ = export_theory()
