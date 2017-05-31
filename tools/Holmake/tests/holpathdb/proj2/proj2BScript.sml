open HolKernel Parse boolLib bossLib;

open proj2ATheory
val _ = new_theory "proj2B";

val thm2B = Q.store_thm(
  "thm2B",
  ‘ODD (bar n) ⇔ 0 < n’,
  simp[bar_def] >> Cases_on ‘n’ >> simp[] >>
  simp[arithmeticTheory.MULT_CLAUSES, arithmeticTheory.ODD_ADD,
       arithmeticTheory.ODD_MULT]);

val _ = export_theory();
