Theory leakageLibContext[bare]
Ancestors
  transc
Libs
  HolKernel Parse boolLib bossLib realLib

(* ------------------------------------------------------------------------- *)
(* Lemmas leakageLib.sml formerly proved as it loaded.  A library is loaded   *)
(* before its client's new_theory, so there was no current theory to prove    *)
(* against; proving them in a theory of their own removes that.               *)
(* ------------------------------------------------------------------------- *)

Theorem lg_times_compute_simp_lem:
  !x y. x * lg (y * x) = (\x. x * lg (y * x)) x
Proof
  RW_TAC std_ss []
QED
