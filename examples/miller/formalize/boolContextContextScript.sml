(* Tautologies consumed by boolContext.sml.  Landing them in a theory
   keeps them off ho_prover's load-time TAC_PROOF path. *)

Theory boolContextContext[bare]
Ancestors
  bool
Libs
  bossLib

Theorem EQ_NEG_SELF_F:
  !a : bool. (a = ~a) <=> F
Proof
  METIS_TAC []
QED

Theorem NEG_EQ_SELF_F:
  !a : bool. (~a = a) <=> F
Proof
  METIS_TAC []
QED

Theorem NAND_SELF_F:
  !a. (~a /\ a) <=> F
Proof
  METIS_TAC []
QED

Theorem AND_NEG_SELF_F:
  !a. (a /\ ~a) <=> F
Proof
  METIS_TAC []
QED

Theorem NEG_OR_SELF_T:
  !a. (~a \/ a) <=> T
Proof
  METIS_TAC []
QED

Theorem OR_NEG_SELF_T:
  !a. (a \/ ~a) <=> T
Proof
  METIS_TAC []
QED

Theorem NEG_EQ_EQ:
  !a b : bool. (~a = ~b) <=> (a = b)
Proof
  METIS_TAC []
QED

Theorem FORALL_TRIVIAL:
  !p. (!(x : 'a). p) = p
Proof
  METIS_TAC []
QED

Theorem EXISTS_TRIVIAL:
  !p. (?(x : 'a). p) = p
Proof
  METIS_TAC []
QED

