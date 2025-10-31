Theory simp_attr2
Ancestors
  simp_attr1

Theorem fact_SUC:
    fact (SUC n) = SUC n * fact n
Proof
  SRW_TAC [][]
QED

