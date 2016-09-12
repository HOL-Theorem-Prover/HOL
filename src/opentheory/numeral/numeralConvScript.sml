open HolKernel bossLib boolLib arithmeticTheory

val _ = new_theory "numeralConv";

val BIT0_def = Define`
  (BIT0 0 = 0) /\
  (!n. BIT0 (SUC n) = SUC (SUC (BIT0 n)))`;

val (BIT0_0,BIT0_SUC) = CONJ_PAIR BIT0_def
val _ = save_thm("BIT0_0",BIT0_0);
val _ = save_thm("BIT0_SUC",BIT0_SUC);

val SUC_0 =
  numeralTheory.numeral_suc
  |> CONJUNCTS |> el 1
  |> REWRITE_RULE[ALT_ZERO]

val BIT1_def = Q.store_thm("BIT1_def",
  `!n. BIT1 n = SUC (BIT0 n)`,
  Induct
  \\ REWRITE_TAC[BIT0_def,SUC_0]
  \\ pop_assum(SUBST1_TAC o SYM)
  \\ REWRITE_TAC[BIT1,ADD,ADD_SUC]);

val _ = export_theory();
