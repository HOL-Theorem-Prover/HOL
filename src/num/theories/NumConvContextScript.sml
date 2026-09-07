Theory NumConvContext[bare]
Ancestors
  arithmetic
Libs
  HolKernel Parse boolLib

Theorem save_zero:
  NUMERAL ZERO = 0
Proof
  REWRITE_TAC [arithmeticTheory.NUMERAL_DEF, arithmeticTheory.ALT_ZERO]
QED
