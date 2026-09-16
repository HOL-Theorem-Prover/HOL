Theory ArithconvContext[bare]
Ancestors arithmetic numeral
Libs
  HolKernel Parse boolLib

Theorem divt:
  (q * y = p) ==> (p + r = x) ==> (r < y) ==> (x DIV y = q)
Proof
  REPEAT DISCH_TAC THEN
  MATCH_MP_TAC (arithmeticTheory.DIV_UNIQUE) THEN
  EXISTS_TAC (“r:num”) THEN ASM_REWRITE_TAC[]
QED

Theorem modt:
  (q * y = p) ==> (p + r = x) ==> (r < y) ==> (x MOD y = r)
Proof
  REPEAT DISCH_TAC THEN
  MATCH_MP_TAC arithmeticTheory.MOD_UNIQUE THEN
  EXISTS_TAC “q:num” THEN ASM_REWRITE_TAC[]
QED
