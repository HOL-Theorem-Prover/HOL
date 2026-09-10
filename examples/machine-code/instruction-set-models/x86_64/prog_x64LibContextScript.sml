Theory prog_x64LibContext[bare]
Ancestors
  words pred_set
Libs
  HolKernel Parse boolLib bossLib wordsLib simpLib

(* ------------------------------------------------------------------------- *)
(* Lemmas prog_x64Lib.sml formerly proved as it loaded.  A library is loaded  *)
(* before its client's new_theory, so there was no current theory to prove    *)
(* against; proving them in a theory of their own removes that.               *)
(* ------------------------------------------------------------------------- *)

Theorem w2n_MOD:
  !imm32. w2n (imm32:word32) MOD 4294967296 = w2n imm32
Proof
  Cases THEN FULL_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w]
QED

Theorem SING_SUBSET:
  !x:'a y. {x} SUBSET y <=> x IN y
Proof
  REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET]
QED
