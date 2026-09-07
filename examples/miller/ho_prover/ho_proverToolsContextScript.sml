(* Auxiliary tautologies consumed by ho_proverTools.sml.  These used to
   be proved at load time via PROVE_TAC/RW_TAC, which fired the
   TAC_PROOF-with-no-current-theory warning ~29 times per client
   theory.  Landing them here lets ho_proverTools reference the
   theorems directly. *)

Theory ho_proverToolsContext[bare]
Ancestors
  bool
Libs
  bossLib

Theorem POS_NEG_F:
  !a. a ==> ~a ==> F
Proof
  PROVE_TAC []
QED

Theorem NNEG_F_ELIM:
  !x. (~x ==> F) ==> x
Proof
  PROVE_TAC []
QED

Theorem NEG_ELIM:
  !x. ~~x ==> x
Proof
  PROVE_TAC []
QED

Theorem NOT_T_IMP_F:
  ~T ==> F
Proof
  PROVE_TAC []
QED

Theorem OR_NEG_NEG_F:
  !a b. (a \/ b) ==> ~a ==> ~b ==> F
Proof
  PROVE_TAC []
QED

Theorem NOR_NNEG_L_F:
  !a b. ~(a \/ b) ==> ~~a ==> F
Proof
  PROVE_TAC []
QED

Theorem NOR_NNEG_R_F:
  !a b. ~(a \/ b) ==> ~~b ==> F
Proof
  PROVE_TAC []
QED

Theorem NAND_NNEG_F:
  !a b. ~(a /\ b) ==> ~~a ==> ~~b ==> F
Proof
  PROVE_TAC []
QED

Theorem AND_NEG_L_F:
  !a b. (a /\ b) ==> ~a ==> F
Proof
  PROVE_TAC []
QED

Theorem AND_NEG_R_F:
  !a b. (a /\ b) ==> ~b ==> F
Proof
  PROVE_TAC []
QED

Theorem BOOL_APP_CASES:
  (p : bool -> 'a) x = if x then p T else p F
Proof
  RW_TAC bool_ss []
QED

Theorem NEQ_REFL_F:
  !(x : 'a). ~(x = x) ==> F
Proof
  PROVE_TAC []
QED

Theorem CONJ_NEG_F:
  !x. x /\ ~x ==> F
Proof
  PROVE_TAC []
QED

Theorem EQ_NEG_EQ:
  !x y : bool. (x = y) ==> (~x = ~y)
Proof
  PROVE_TAC []
QED
