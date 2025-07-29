Theory simp_attr1

val fact_def = Define`
  fact n = if n = 0 then 1 else n * fact(n - 1)
`;

val fact = store_thm(
  "fact[simp]",
  ``(fact 0 = 1) /\ (fact (SUC n) = SUC n * fact n)``,
  CONJ_TAC THEN SRW_TAC[][Once fact_def]);

val fact_SUC = store_thm(
  "fact_SUC",
  ``fact (SUC n) = SUC n * fact n``,
  SRW_TAC [][])

