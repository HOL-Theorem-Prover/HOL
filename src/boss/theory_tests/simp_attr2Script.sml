Theory simp_attr2
Ancestors
  simp_attr1

val fact_SUC = store_thm(
  "fact_SUC",
  ``fact (SUC n) = SUC n * fact n``,
  SRW_TAC [][])

