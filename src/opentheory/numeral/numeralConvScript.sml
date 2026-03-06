Theory numeralConv
Ancestors
  arithmetic

Definition BIT0_def:
  (BIT0 0 = 0) /\
  (!n. BIT0 (SUC n) = SUC (SUC (BIT0 n)))
End

val (BIT0_0,BIT0_SUC) = CONJ_PAIR BIT0_def
Theorem BIT0_0 = BIT0_0;
Theorem BIT0_SUC = BIT0_SUC;

val SUC_0 =
  numeralTheory.numeral_suc
  |> CONJUNCTS |> el 1
  |> REWRITE_RULE[ALT_ZERO]

Theorem BIT1_def:
   !n. BIT1 n = SUC (BIT0 n)
Proof
  Induct
  \\ REWRITE_TAC[BIT0_def,SUC_0]
  \\ pop_assum(SUBST1_TAC o SYM)
  \\ REWRITE_TAC[BIT1,ADD,ADD_SUC]
QED

