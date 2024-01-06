open HolKernel Parse boolLib bossLib;

val _ = new_theory "fibmod3";

Definition fib_def:
  fib n = if n = 0n then 1n else if n = 1 then 1 else fib (n-1) + fib (n - 2)
End

Theorem fibmod:
  ∀n. EVEN (fib n) ⇔ n MOD 3 = 2
Proof
  recInduct fib_ind >> rw[] >>
  ONCE_REWRITE_TAC [fib_def] >> rw[] >>
  gs[arithmeticTheory.EVEN_ADD] >>
  intLib.ARITH_TAC
QED


val _ = export_theory();
