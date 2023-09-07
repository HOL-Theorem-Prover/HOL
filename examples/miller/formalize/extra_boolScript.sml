open HolKernel Parse bossLib boolLib;

open combinTheory;

val _ = new_theory "extra_bool";

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val RAND_THM = store_thm
  ("RAND_THM",
   ``!f x y. (x = y) ==> (f x = f y)``,
   RW_TAC std_ss []);

val K_PARTIAL = store_thm
  ("K_PARTIAL",
   ``!x. K x = \z. x``,
   RW_TAC std_ss [K_DEF]);

val SELECT_EXISTS_UNIQUE = store_thm
  ("SELECT_EXISTS_UNIQUE",
   ``!P n. $? P /\ (!m. P m ==> (m = n)) ==> ($@ P = n)``,
   RW_TAC std_ss [boolTheory.EXISTS_DEF]);

val CONJ_EQ_IMP = store_thm
  ("CONJ_EQ_IMP",
   ``!a b c. (a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)``,
   PROVE_TAC []);

(* ------------------------------------------------------------------------- *)

val xor_def = Define `xor (x:bool) y = ~(x = y)`;
val _ = set_fixity "xor" (Infixr 750);

val xor_comm = store_thm
  ("xor_comm",
   ``!x y. x xor y <=> y xor x``,
   RW_TAC bool_ss [xor_def] THEN DECIDE_TAC);

val xor_assoc = store_thm
  ("xor_assoc",
   ``!x y z. (x xor y) xor z <=> x xor (y xor z)``,
   RW_TAC bool_ss [xor_def] THEN DECIDE_TAC);

Theorem xor_F: !x. x xor F <=> x
Proof RW_TAC bool_ss [xor_def]
QED

Theorem F_xor: !x. F xor x <=> x
Proof RW_TAC bool_ss [xor_def]
QED

val xor_T = store_thm
  ("xor_T",
   ``!x. x xor T <=> ~x``,
   RW_TAC bool_ss [xor_def]);

val T_xor = store_thm
  ("T_xor",
   ``!x. T xor x <=> ~x``,
   RW_TAC bool_ss [xor_def]);

val xor_refl = store_thm
  ("xor_refl",
   ``!x. ~(x xor x)``,
   RW_TAC bool_ss [xor_def]);

val xor_inv = store_thm
  ("xor_inv",
   ``!x. x xor ~x``,
   RW_TAC bool_ss [xor_def] THEN DECIDE_TAC);

val inv_xor = store_thm
  ("inv_xor",
   ``!x. ~x xor x``,
   RW_TAC bool_ss [xor_def] THEN DECIDE_TAC);

val _ = export_theory ();
