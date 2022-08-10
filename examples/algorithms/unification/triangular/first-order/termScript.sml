open HolKernel boolLib bossLib Parse stringTheory ramanaLib bagTheory
     commonUnifTheory;

val _ = new_theory "term";

Datatype:   term = Var num | Pair term term | Const 'a
End

Definition pair_count_def[simp]:
  (pair_count (Var v) = 0) /\
  (pair_count (Const c) = 0) /\
  (pair_count (Pair t1 t2) = 1 + pair_count t1 + pair_count t2)
End

Definition vars_def[simp]:
  (vars (Var x) = {x}) /\
  (vars (Pair t1 t2) = vars t1 UNION vars t2) /\
  (vars (Const _) = {})
End

Theorem FINITE_vars[simp]: FINITE (vars t)
Proof Induct_on `t` THEN SRW_TAC [][]
QED

Definition varb_def[simp]:
  (varb (Var s) = {| s |}) /\
  (varb (Pair t1 t2) = BAG_UNION (varb t1) (varb t2)) /\
  (varb (Const c) = {||})
End

Theorem FINITE_varb[simp]: FINITE_BAG (varb t)
Proof Induct_on `t` THEN SRW_TAC [][]
QED

Theorem IN_varb_vars[simp]:   BAG_IN e (varb t) <=> e IN vars t
Proof
  Induct_on `t` THEN SRW_TAC [][]
QED

val _ = export_theory ();
