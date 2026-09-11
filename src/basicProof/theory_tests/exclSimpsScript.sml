Theory exclSimps[bare]
Libs
  HolKernel Parse boolLib simpLib BasicProvers

(* Both reach the simpset through the context the tactic is run in.
   Neither should consult the ambient one: exclude_simps reaches a proof
   by transforming its context, and a helper reading the global simpset
   would be reading state the attribute has no business clobbering. *)
fun simp ths g ctxt = simpLib.SIMP_TAC (srw_ss_of ctxt) ths g ctxt
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
