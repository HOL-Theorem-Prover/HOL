Theory extra_bool
Ancestors
  combin

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

Theorem RAND_THM:
     !f x y. (x = y) ==> (f x = f y)
Proof
   RW_TAC std_ss []
QED

Theorem K_PARTIAL:
     !x. K x = \z. x
Proof
   RW_TAC std_ss [K_DEF]
QED

Theorem SELECT_EXISTS_UNIQUE:
     !P n. $? P /\ (!m. P m ==> (m = n)) ==> ($@ P = n)
Proof
   RW_TAC std_ss [boolTheory.EXISTS_DEF]
QED

Theorem CONJ_EQ_IMP:
     !a b c. (a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)
Proof
   PROVE_TAC []
QED

(* ------------------------------------------------------------------------- *)

Definition xor_def:   xor (x:bool) y = ~(x = y)
End
val _ = set_fixity "xor" (Infixr 750);

Theorem xor_comm:
     !x y. x xor y <=> y xor x
Proof
   RW_TAC bool_ss [xor_def] THEN DECIDE_TAC
QED

Theorem xor_assoc:
     !x y z. (x xor y) xor z <=> x xor (y xor z)
Proof
   RW_TAC bool_ss [xor_def] THEN DECIDE_TAC
QED

Theorem xor_F: !x. x xor F <=> x
Proof RW_TAC bool_ss [xor_def]
QED

Theorem F_xor: !x. F xor x <=> x
Proof RW_TAC bool_ss [xor_def]
QED

Theorem xor_T:
     !x. x xor T <=> ~x
Proof
   RW_TAC bool_ss [xor_def]
QED

Theorem T_xor:
     !x. T xor x <=> ~x
Proof
   RW_TAC bool_ss [xor_def]
QED

Theorem xor_refl:
     !x. ~(x xor x)
Proof
   RW_TAC bool_ss [xor_def]
QED

Theorem xor_inv:
     !x. x xor ~x
Proof
   RW_TAC bool_ss [xor_def] THEN DECIDE_TAC
QED

Theorem inv_xor:
     !x. ~x xor x
Proof
   RW_TAC bool_ss [xor_def] THEN DECIDE_TAC
QED

