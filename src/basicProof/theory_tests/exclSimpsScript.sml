Theory exclSimps[bare]
Libs
  HolKernel Parse boolLib simpLib BasicProvers

fun simp ths g = simpLib.SIMP_TAC (srw_ss()) ths g

Theorem foo:
  (!x. f x = x) ==> f p = (\x. x) p
Proof[exclude_simps=BETA_CONV]
  strip_tac >> simp[]
  >- (CONV_TAC (RAND_CONV BETA_CONV) >>
      ASM_REWRITE_TAC [])
QED
