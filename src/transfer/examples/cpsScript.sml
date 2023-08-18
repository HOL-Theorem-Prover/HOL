open HolKernel Parse boolLib bossLib;

val _ = new_theory "cps";

Definition cwc_def:
  cwc v k = k v
End

Definition contify_def:
  contify k v = k v
End

Theorem contify_app:
  contify k (f x) = contify (λfk. contify (λxk. cwc (fk xk) k) x) f
Proof
  simp[contify_def, cwc_def]
QED

Theorem contify_COND:
  contify k (COND g t e) = contify (λgk. if gk then contify k t
                                         else contify k e) g
Proof
  rw[contify_def]
QED

Definition FACTk_def:
  FACTk x k = cwc (FACT x) k
End
Theorem FACT_EQN:
  FACT n = if n < 2 then 1 else n * FACT(n-1)
Proof
  Induct_on ‘n’ >> simp[arithmeticTheory.FACT]
QED
Theorem REVERSE_EQN:
  REVERSE l = case l of [] => [] | h::t => REVERSE t ++ [h]
Proof
  Cases_on ‘l’ >> simp[]
QED

val rm_cwc = SCONV[cwc_def]

Theorem contify_cwc:
  contify k x = cwc x k
Proof
  simp[contify_def, cwc_def]
QED

Definition kREVERSE_def:
  REVERSEk x k = cwc (REVERSE x) k
End

Theorem contify_list_case:
  contify k (list_CASE x n c) =
  contify (λxk. case xk of [] => contify k n | h::t => contify k (c h t)) x
Proof
  simp[contify_def] >> Cases_on ‘x’ >> simp[]
QED




val _ = export_theory();
