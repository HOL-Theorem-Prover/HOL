Theory EnumTypeContext[bare]
Ancestors
  arithmetic
Libs
  HolKernel Parse boolLib numLib

Theorem n_less_cases:
  !m n. n < m <=> m <> 0 /\ (let x = m - 1 in n < x \/ (n = x))
Proof
  REWRITE_TAC [LET_THM] THEN BETA_TAC THEN CONV_TAC numLib.ARITH_CONV
QED
