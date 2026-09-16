Theory x86_LibContext[bare]
Ancestors
  words bit
Libs
  HolKernel Parse boolLib bossLib wordsLib simpLib

(* ------------------------------------------------------------------------- *)
(* Lemmas x86_Lib.sml formerly proved as it loaded.  A library is loaded      *)
(* before its client's new_theory, so there was no current theory to prove    *)
(* against; proving them in a theory of their own removes that.               *)
(* ------------------------------------------------------------------------- *)

Theorem n2w_SIGN_EXTEND:
  !n. n < 256 ==> ((n2w (SIGN_EXTEND 8 32 n)):word32 = sw2sw ((n2w n):word8))
Proof
  SIMP_TAC (std_ss++SIZES_ss) [sw2sw_def, w2n_n2w]
QED
