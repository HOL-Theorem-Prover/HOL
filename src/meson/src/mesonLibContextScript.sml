Theory mesonLibContext[bare]
Libs
  HolKernel Parse boolLib tautLib

(* ------------------------------------------------------------------------- *)
(* Lemmas mesonLib.sml formerly proved as it loaded.                         *)
(* ------------------------------------------------------------------------- *)

Theorem meson_imp_conv:  a \/ b <=> ~b ==> a
Proof tautLib.TAUT_TAC
QED

Theorem meson_not_imp_p:  (~p ==> p) <=> p
Proof tautLib.TAUT_TAC
QED

Theorem meson_p_imp_not_p:  (p ==> ~p) <=> ~p
Proof tautLib.TAUT_TAC
QED

Theorem meson_eq_thms:
  (x:'a = x) /\ (~(x:'a = y) \/ ~(x = z) \/ (y = z))
Proof
  REWRITE_TAC [] THEN ASM_CASES_TAC ``x:'a = y`` THEN
  ASM_REWRITE_TAC [ONCE_REWRITE_RULE [boolTheory.DISJ_SYM]
                    (REWRITE_RULE [] boolTheory.BOOL_CASES_AX)]
QED

Theorem meson_imp_elim:  (a ==> b) <=> ~a \/ b
Proof tautLib.TAUT_TAC
QED

Theorem meson_eq_elim:  (a = b) ==> b \/ ~a
Proof tautLib.TAUT_TAC
QED
