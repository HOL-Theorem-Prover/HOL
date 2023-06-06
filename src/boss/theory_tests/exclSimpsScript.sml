open HolKernel Parse boolLib bossLib

val _ = new_theory "exclSimps";

Theorem foo:
  (!x. f x = x) ==> f p = (\x. x) p
Proof[exclude_simps = BETA_CONV]
  strip_tac >> simp[] >>
  CONV_TAC (RAND_CONV BETA_CONV) >>
  ASM_REWRITE_TAC []
QED



val _ = export_theory();
