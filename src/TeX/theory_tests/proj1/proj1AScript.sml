Theory proj1A

Definition foo_def:  foo x = x * 2 + 1
End

Theorem Athm:
   foo = BIT1
Proof
  REWRITE_TAC [FUN_EQ_THM, arithmeticTheory.BIT1] >>
  simp[foo_def]
QED



