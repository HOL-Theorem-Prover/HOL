(* ===================================================================== *)
(* FILE          : OpenTheoryReaderContextScript.sml                     *)
(* DESCRIPTION   : The OpenTheory base package's definitions of ==>, /\   *)
(*                 and ?, which boolTheory states differently.           *)
(*                 OpenTheoryReader.sml used to prove these as it        *)
(*                 loaded, making its base_thms net a function of link   *)
(*                 order rather than of its own source.                  *)
(* ===================================================================== *)

Theory OpenTheoryReaderContext[bare]
Ancestors
  bool
Libs
  HolKernel Parse boolLib BasicProvers metisLib

Theorem imp_def:
  $==> = (\p q. p /\ q <=> p)
Proof
  METIS_TAC []
QED

Theorem and_def:
  $/\ = (\p q. (\f:bool->bool->bool. f p q) = (\f. f T T))
Proof
  SRW_TAC [][FUN_EQ_THM, EQ_IMP_THM]
QED

Theorem exists_def:
  $? = (\P. !q. (!x. P x ==> q) ==> q)
Proof
  SRW_TAC [][FUN_EQ_THM] THEN
  SUBST_TAC [GSYM (ISPEC “P:'a->bool” ETA_THM)] THEN
  METIS_TAC []
QED
