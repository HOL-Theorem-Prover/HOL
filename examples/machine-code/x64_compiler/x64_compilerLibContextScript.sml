Theory x64_compilerLibContext[bare]
Ancestors
  bool
Libs
  HolKernel Parse boolLib bossLib simpLib

(* ------------------------------------------------------------------------- *)
(* Lemmas this directory's libraries formerly proved as they loaded.  A       *)
(* library is loaded before its client's new_theory, so there was no current  *)
(* theory to prove against.                                                   *)
(* ------------------------------------------------------------------------- *)

Theorem COMPILER_TAC_LEMMA:
  !a b:bool. (a /\ a /\ b <=> a /\ b) /\ (a \/ a \/ b <=> a \/ b)
Proof
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC std_ss []
QED

Theorem EXPAND_IF:
  !b c s1 (s2:'a).
    ((if b \/ c then s1 else s2) = if b then s1 else if c then s1 else s2) /\
    ((if b /\ c then s1 else s2) = if b then if c then s1 else s2 else s2)
Proof
  Cases THEN Cases THEN SIMP_TAC std_ss []
QED
