open HolKernel Parse boolLib bossLib

val _ = new_theory "exclSimps";

Theorem foo:
  (!x. f x = x) ==> f 2 = (\x. if x < 1 then x else x + 1) (10 - 9)
Proof[exclude_simps = BETA_CONV arithmetic.LT1_EQ0,
      exclude_frags = REDUCE
]
  strip_tac >> simp[] >>
  CONV_TAC (RAND_CONV BETA_CONV) >>
  CONV_TAC (LAND_CONV $ LAND_CONV $ RAND_CONV $ LAND_CONV reduceLib.RED_CONV) >>
  CONV_TAC (LAND_CONV $ LAND_CONV $ RAND_CONV reduceLib.LT_CONV) >>
  simp[]
QED



val _ = export_theory();
