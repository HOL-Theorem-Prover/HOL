Theory simp_attr1

Definition fact_def:
  fact n = if n = 0 then 1 else n * fact(n - 1)
End

Theorem fact[simp]:
    (fact 0 = 1) /\ (fact (SUC n) = SUC n * fact n)
Proof
  CONJ_TAC THEN SRW_TAC[][Once fact_def]
QED

Theorem fact_SUC:
    fact (SUC n) = SUC n * fact n
Proof
  SRW_TAC [][]
QED

