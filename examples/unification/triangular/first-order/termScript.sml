open HolKernel boolLib bossLib Parse stringTheory ramanaLib bagTheory commonUnifTheory;

val _ = new_theory "term";

val _ = Hol_datatype`
  term = Var of num
       | Pair of term => term
       | Const of 'a`;

val pair_count_def = RWDefine`
(pair_count (Var v) = 0) /\
(pair_count (Const c) = 0) /\
(pair_count (Pair t1 t2) = 1 + pair_count t1 + pair_count t2)`;

val vars_def = RWDefine`
  (vars (Var x) = {x}) /\
  (vars (Pair t1 t2) = vars t1 UNION vars t2) /\
  (vars (Const _) = {})`;

val FINITE_vars = RWstore_thm(
"FINITE_vars",
`FINITE (vars t)`,
Induct_on `t` THEN SRW_TAC [][]);

val varb_def = RWDefine`
  (varb (Var s) = {| s |}) /\
  (varb (Pair t1 t2) = BAG_UNION (varb t1) (varb t2)) /\
  (varb (Const c) = {||})`;

val FINITE_varb = RWstore_thm(
  "FINITE_varb",
  `FINITE_BAG (varb t)`,
  Induct_on `t` THEN SRW_TAC [][]);

val IN_varb_vars = RWstore_thm(
  "IN_varb_vars",
  `BAG_IN e (varb t) <=> e IN vars t`,
  Induct_on `t` THEN SRW_TAC [][]);

val _ = export_theory ();
