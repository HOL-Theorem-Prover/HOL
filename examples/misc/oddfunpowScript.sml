open HolKernel Parse boolLib bossLib;

open arithmeticTheory
val _ = new_theory "oddfunpow";

Theorem FUNPOW_ID:
  FUNPOW (λx.x) n y = y
Proof
  Induct_on ‘n’ >> simp[FUNPOW_SUC]
QED

Theorem FUNPOW_NOT:
  (EVEN n ⇒ (FUNPOW $~ n x = x)) ∧
  (ODD n ⇒ (FUNPOW $~ n x = ~x))
Proof
  Induct_on ‘n’ >> gs[EVEN, ODD, GSYM ODD_EVEN, FUNPOW_SUC, GSYM EVEN_ODD]
QED

Theorem result:
  ∀(f: bool -> bool) n. ODD n ⇒ FUNPOW f n b = f b
Proof
  Cases_on ‘f’ using BOOL_FUN_CASES_THM >>
  Cases_on ‘n’ >>
  simp[FUNPOW_SUC, FUNPOW_ID, FUNPOW_NOT, SF ETA_ss, ODD, GSYM EVEN_ODD]
QED


val _ = export_theory();
