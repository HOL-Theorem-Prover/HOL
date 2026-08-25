Theory exclSimps[bare]
Libs
  HolKernel Parse boolLib simpLib BasicProvers

(* two ways to reach the stateful simpset: the ambient one, and the one
   carried by the context the tactic is run in.  exclude_simps has to
   reach both. *)
fun simp ths g = simpLib.SIMP_TAC (srw_ss()) ths g
fun csimp ths g ctxt = simpLib.SIMP_TAC (srw_ss_of ctxt) ths g ctxt

Theorem foo:
  (!x. f x = x) ==> f p = (\x. x) p
Proof[exclude_simps=BETA_CONV]
  strip_tac >> simp[]
  >- (CONV_TAC (RAND_CONV BETA_CONV) >>
      ASM_REWRITE_TAC [])
QED

Theorem foo_ctxt:
  (!x. f x = x) ==> f p = (\x. x) p
Proof[exclude_simps=BETA_CONV]
  strip_tac >> csimp[]
  >- (CONV_TAC (RAND_CONV BETA_CONV) >>
      ASM_REWRITE_TAC [])
QED
