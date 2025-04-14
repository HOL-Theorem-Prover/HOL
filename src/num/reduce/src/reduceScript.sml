open HolKernel Parse boolLib;
open arithmeticTheory computeLib;

val _ = new_theory "reduce";

Theorem num_case_compute_lazy =
  lazyfy_thm arithmeticTheory.num_case_compute;

Theorem div_thm:
  !x y q r. x DIV y = if (x = q * y + r) /\ (r < y) then q else x DIV y
Proof
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN
  MATCH_MP_TAC DIV_UNIQUE THEN EXISTS_TAC (Term `r:num`) THEN
  ASM_REWRITE_TAC []
QED

Theorem mod_thm:
  !x y q r. x MOD y = if (x = q * y + r) /\ r<y then r else x MOD y
Proof
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN
  MATCH_MP_TAC MOD_UNIQUE THEN EXISTS_TAC (Term `q:num`) THEN
  ASM_REWRITE_TAC []
QED

val _ = export_theory ();
