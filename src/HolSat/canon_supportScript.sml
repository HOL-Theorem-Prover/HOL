open HolKernel Parse boolLib;
val _ = new_theory "canon_support";

open bossLib combinTheory;

infixr 0 THEN;

val _ = Parse.reveal "C";

(* ------------------------------------------------------------------------- *)
(* Condify theorems.                                                         *)
(* ------------------------------------------------------------------------- *)

val COND_SIMP = store_thm
  ("COND_SIMP",
   ``!a f g. (if a then f a else g a) = (if a then f T else g F)``,
   RW_TAC std_ss []);

val COND_NOT = store_thm
  ("COND_NOT",
   ``!a. ~a = if a then F else T``,
   RW_TAC std_ss []
   THEN PROVE_TAC []);

val COND_AND = store_thm
  ("COND_AND",
   ``!a b. a /\ b = (if a then b else F)``,
   RW_TAC std_ss []
   THEN PROVE_TAC []);

val COND_OR = store_thm
  ("COND_OR",
   ``!a b. a \/ b = if a then T else b``,
   RW_TAC std_ss []
   THEN PROVE_TAC []);

val COND_IMP = store_thm
  ("COND_IMP",
   ``!a b. a ==> b = if a then b else T``,
   RW_TAC std_ss []
   THEN PROVE_TAC []);

val COND_EQ = store_thm
  ("COND_EQ",
   ``!a b. (a = b) = if a then b else ~b``,
   RW_TAC std_ss []
   THEN PROVE_TAC []);

val COND_COND = store_thm
  ("COND_COND",
   ``!a b c x y.
       (if (if a then b else c) then x else y) =
       (if a then (if b then x else y) else (if c then x else y))``,
   RW_TAC std_ss []
   THEN PROVE_TAC []);

val COND_ETA = store_thm
  ("COND_ETA",
   ``!a. (if a then T else F) = a``,
   RW_TAC std_ss []);

(* ------------------------------------------------------------------------- *)
(* {S,K,I} theorems.                                                         *)
(* ------------------------------------------------------------------------- *)

val MK_I = store_thm
  ("MK_I",
   ``(\v. v) = I``,
   REPEAT STRIP_TAC
   THEN CONV_TAC (FUN_EQ_CONV)
   THEN RW_TAC std_ss [S_DEF, K_DEF, I_THM]);
   
val MK_K = store_thm
  ("MK_K",
   ``!x. (\v. x) = K x``,
   REPEAT STRIP_TAC
   THEN CONV_TAC (FUN_EQ_CONV)
   THEN RW_TAC std_ss [S_DEF, K_DEF]);

val MK_S = store_thm
  ("MK_S",
   ``!x y. (\v. (x v) (y v)) = S x y``,
   REPEAT STRIP_TAC
   THEN CONV_TAC (FUN_EQ_CONV)
   THEN RW_TAC std_ss [S_DEF, K_DEF]);

val MK_o = store_thm
  ("MK_o",
   ``!x y. (\v. x (y v)) = x o y``,
   REPEAT STRIP_TAC
   THEN CONV_TAC (FUN_EQ_CONV)
   THEN RW_TAC std_ss [S_DEF, K_DEF, o_DEF]);

val MK_C = store_thm
  ("MK_C",
   ``!x y. (\v. (x v) y) = C x y``,
   REPEAT STRIP_TAC
   THEN CONV_TAC (FUN_EQ_CONV)
   THEN RW_TAC std_ss [S_DEF, K_DEF, C_DEF]);

val LIFT_K_THRU_S = store_thm
  ("LIFT_K_THRU_S",
   ``!x y. S (K x) (K y) = K (x y)``,
   REPEAT STRIP_TAC
   THEN CONV_TAC (FUN_EQ_CONV)
   THEN RW_TAC std_ss [S_DEF, K_DEF]);

(* ------------------------------------------------------------------------- *)
(* Worker theorems for NNF.                                                  *)
(* ------------------------------------------------------------------------- *)

val IMP_DISJ_THM' = store_thm
  ("IMP_DISJ_THM'",
   ``!x y. x ==> y = y \/ ~x``,
   PROVE_TAC []);

(* ------------------------------------------------------------------------- *)
(* Worker theorems for the tautology prover.                                 *)
(* ------------------------------------------------------------------------- *)

val BOOL_CASES = store_thm
  ("BOOL_CASES",
   ``!a b. (a ==> b) /\ (~a ==> b) ==> b``,
   PROVE_TAC []);

val T_OR = store_thm
  ("T_OR",
   ``!t. T \/ t = T``,
   PROVE_TAC []);

val OR_T = store_thm
  ("OR_T",
   ``!t. t \/ T = T``,
   PROVE_TAC []);

val T_AND = store_thm
  ("T_AND",
   ``!t. T /\ t = t``,
   PROVE_TAC []);

val AND_T = store_thm
  ("AND_T",
   ``!t. t /\ T = t``,
   PROVE_TAC []);

val FORALL_T = store_thm
  ("FORALL_T",
   ``(!x. T) = T``,
   PROVE_TAC []);

val OR_F = store_thm
  ("OR_F",
   ``!t. t \/ F = t``,
   PROVE_TAC []);

val CONTRACT_DISJ = store_thm
  ("CONTRACT_DISJ",
   ``!a b b'. (~a ==> (b = b')) ==> (~a ==> (a \/ b = b'))``,
   PROVE_TAC []);

val DISJ_CONGRUENCE = store_thm
  ("DISJ_CONGRUENCE",
   ``!a b b'. (~a ==> (b = b')) ==> (a \/ b = a \/ b')``,
   PROVE_TAC []);

(* ------------------------------------------------------------------------- *)
(* Worker theorems for the lambda-elimination conversion.                    *)
(* ------------------------------------------------------------------------- *)

val LAMB_EQ_ELIM = store_thm
  ("LAMB_EQ_ELIM",
   ``!(s : 'a -> 'b) t. ((\x. s x) = t) = (!x. s x = t x)``,
   PROVE_TAC []);

val EQ_LAMB_ELIM = store_thm
  ("EQ_LAMB_ELIM",
   ``!(s : 'a -> 'b) t. (s = (\x. t x)) = (!x. s x = t x)``,
   PROVE_TAC []);

(* ------------------------------------------------------------------------- *)
(* Worker theorems for definitional CNF.                                     *)
(* ------------------------------------------------------------------------- *)

val NEG_EQ = store_thm
  ("NEG_EQ",
   ``!a b. ~(a = b) = (~a = b)``,
   PROVE_TAC []);
   
(* non-interactive mode
*)
val _ = export_theory ();
