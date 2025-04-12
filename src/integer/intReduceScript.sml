open HolKernel boolLib bossLib

open integerTheory intSyntax simpLib Arithconv numeralTheory
     arithmeticTheory tautLib

val _ = new_theory "intReduce";

Theorem INT_LE_CONV_tth =
  TAUT ‘(F /\ F <=> F) /\ (F /\ T <=> F) /\
        (T /\ F <=> F) /\ (T /\ T <=> T)’;
Theorem INT_LE_CONV_nth = TAUT ‘(~T <=> F) /\ (~F <=> T)’;

Theorem INT_LE_CONV_pth:
  (~(&m) <= &n <=> T) /\
  (&m <= (&n : int) <=> m <= n) /\
  (~(&m) <= ~(&n) <=> n <= m) /\
  (&m <= ~(&n) <=> (m = 0) /\ (n = 0))
Proof
  REWRITE_TAC[INT_LE_NEG]
  >> REWRITE_TAC[INT_LE_LNEG, INT_LE_RNEG]
  >> REWRITE_TAC[INT_OF_NUM_ADD, INT_OF_NUM_LE, LE_0]
  >> REWRITE_TAC[LE, ADD_EQ_0]
QED

Theorem INT_LT_CONV_pth:
  (&m < ~(&n) <=> F) /\
  (&m < (&n :int) <=> m < n) /\
  (~(&m) < ~(&n) <=> n < m) /\
  (~(&m) < &n <=> ~((m = 0) /\ (n = 0)))
Proof
  REWRITE_TAC[INT_LE_CONV_pth, GSYM NOT_LE, INT_LT2] THEN
  TAUT_TAC
QED

Theorem INT_GE_CONV_pth:
  (&m >= ~(&n) <=> T) /\
  (&m >= (&n :int) <=> n <= m) /\
  (~(&m) >= ~(&n) <=> m <= n) /\
  (~(&m) >= &n <=> (m = 0) /\ (n = 0))
Proof
  REWRITE_TAC[INT_LE_CONV_pth, INT_GE] THEN
  TAUT_TAC
QED

Theorem INT_GT_CONV_pth:
  (~(&m) > &n <=> F) /\
  (&m > (&n :int) <=> n < m) /\
  (~(&m) > ~(&n) <=> m < n) /\
  (&m > ~(&n) <=> ~((m = 0) /\ (n = 0)))
Proof
  REWRITE_TAC[INT_LT_CONV_pth, INT_GT] THEN
  TAUT_TAC
QED

Theorem INT_EQ_CONV_pth:
  ((&m = (&n :int)) <=> (m = n)) /\
  ((~(&m) = ~(&n)) <=> (m = n)) /\
  ((~(&m) = &n) <=> (m = 0) /\ (n = 0)) /\
  ((&m = ~(&n)) <=> (m = 0) /\ (n = 0))
Proof
  REWRITE_TAC[GSYM INT_LE_ANTISYM, GSYM LE_ANTISYM]
  \\ REWRITE_TAC[INT_LE_CONV_pth, LE, LE_0]
  \\ CONV_TAC tautLib.TAUT_CONV
QED

Theorem INT_NEG_CONV_pth:
  (-(&0) = &0) /\ (-(-(&x)) = &x)
Proof
  REWRITE_TAC[INT_NEG_NEG, INT_NEG_0]
QED

Theorem INT_ADD_CONV_pth0:
  (-(&m) + &m = &0) /\ (&m + -(&m) = &0)
Proof
  REWRITE_TAC[INT_ADD_LINV, INT_ADD_RINV]
QED

Theorem INT_ADD_CONV_pth1:
  (-(&m) + -(&n):int = -(&(m + n))) /\
  (-(&m) + &(m + n):int = &n) /\
  (-(&(m + n)) + (&m :int) = -(&n)) /\
  (&(m + n) + -(&m):int = &n) /\
  (&m + -(&(m + n)):int = -(&n)) /\
  (&m + &n = &(m + n):int)
Proof
  REWRITE_TAC[GSYM INT_OF_NUM_ADD, INT_NEG_ADD] THEN
  REWRITE_TAC[INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_LID] THEN
  REWRITE_TAC[INT_ADD_RINV, INT_ADD_LID] THEN
  ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
  REWRITE_TAC[INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_LID] THEN
  REWRITE_TAC[INT_ADD_RINV, INT_ADD_LID]
QED

Theorem INT_MUL_CONV_pth0:
  (&0 * &x = &0 :int) /\
  (&0 * -(&x) = &0 :int) /\
  (&x * &0 = &0 :int) /\
  (-(&x) * &0 = &0 :int)
Proof
  REWRITE_TAC[INT_MUL_LZERO, INT_MUL_RZERO]
QED

Theorem INT_MUL_CONV_pth1:
  ((&m * &n = &(m * n) :int) /\
   (-(&m) * -(&n) = &(m * n) :int)) /\
  ((-(&m) * &n = -(&(m * n)) :int) /\
   (&m * -(&n) = -(&(m * n)) :int))
Proof
  REWRITE_TAC[INT_MUL_LNEG, INT_MUL_RNEG, INT_NEG_NEG] THEN
  REWRITE_TAC[INT_OF_NUM_MUL]
QED

Theorem INT_POW_CONV_pth:
  (&x ** n = &(x ** n) :int) /\
  ((-(&x):int) ** n = if EVEN n then &(x ** n) else -(&(x ** n)))
Proof
  REWRITE_TAC[INT_OF_NUM_POW, INT_POW_NEG]
QED

Theorem INT_POW_CONV_tth:
  ((if T then (x:int) else y) = x) /\ ((if F then (x:int) else y) = y)
Proof
  REWRITE_TAC[]
QED

val _ = export_theory ();
