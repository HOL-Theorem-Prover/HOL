open HolKernel Parse boolLib bossLib

open logrootTheory

val _ = new_theory "exclSimps";

Theorem foo:
  (!x. f x = x) ==> f 2 = (\x. if x < 1 then x else x + 1) (10 - 9)
Proof[exclude_simps = BETA_CONV arithmetic.LT1_EQ0,
      exclude_frags = REDUCE
]
  strip_tac >> simp[ExclSF "ARITH"] >>
  CONV_TAC (RAND_CONV BETA_CONV) >>
  CONV_TAC (RHS_CONV $ RATOR_CONV $ RATOR_CONV $ RAND_CONV $
            LAND_CONV reduceLib.RED_CONV) >>
  CONV_TAC (RHS_CONV $ RATOR_CONV $ RATOR_CONV $ RAND_CONV reduceLib.LT_CONV) >>
  simp[ExclSF "ARITH"] >> CONV_TAC (RHS_CONV $ reduceLib.REDUCE_CONV) >>
  MATCH_ACCEPT_TAC EQ_REFL
QED

Theorem bar:
  2 <= n ==> 3 < 2 ** n
Proof[exclude_simps = LT_EXP_LOG_SIMP LE_EXP_LOG_SIMP]
  strip_tac >> simp[]
  >- (irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
      qexists ‘4’ >> simp[] >>
      ‘4 = 2 ** 2’ by simp[] >>
      pop_assum SUBST1_TAC >>
      simp[])
QED




val _ = export_theory();
