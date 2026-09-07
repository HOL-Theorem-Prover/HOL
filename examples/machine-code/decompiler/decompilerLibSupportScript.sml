(* ===================================================================== *)
(* FILE          : decompilerLibSupportScript.sml                        *)
(* DESCRIPTION   : Theorems that decompilerLib.sml used to prove at      *)
(*                 load time.  Landed here so the library can just       *)
(*                 open decompilerLibSupportTheory rather than firing    *)
(*                 Tactical.prove during its own load.                    *)
(* ===================================================================== *)

Theory decompilerLibSupport
Ancestors
  prog address
Libs
  HolKernel Parse boolLib bossLib

Theorem GUARD_THM:
  !m n x. GUARD n x = GUARD m x
Proof
  REWRITE_TAC [GUARD_def]
QED

Theorem GUARD_T:
  !x. x = (x = GUARD 0 T)
Proof
  REWRITE_TAC [GUARD_def]
QED

Theorem GUARD_F:
  !x. ~x = (x = GUARD 0 F)
Proof
  REWRITE_TAC [GUARD_def]
QED

Theorem ABBBREV_CODE_LEMMA:
  !a (x :('a, 'b, 'c) processor) p c q.
    (a ==> SPEC x p c q) ==> !d. c SUBSET d ==> a ==> SPEC x p d q
Proof
  REPEAT STRIP_TAC THEN RES_TAC THEN IMP_RES_TAC SPEC_SUBSET_CODE
QED

Theorem alpha_lemma:
  !b:bool. (b = T) ==> b
Proof
  Cases THEN REWRITE_TAC []
QED
