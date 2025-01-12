(* interactive mode
app load ["bossLib"];
quietdec := true;
*)

open HolKernel Parse boolLib
     Num_conv arithmeticTheory bossLib;

(*
quietdec := false;
*)

val _ = new_theory "power";

val ARW = RW_TAC arith_ss;

val POWER = EXP;
val power_def = save_thm ("power_def", EXP);

val POWER_0 = store_thm("POWER_0",
                        Term `!n. 0<n ==> ($EXP 0 n = 0)`,
                        Cases_on `n` THEN ARW[MULT_CLAUSES,POWER]);

val POWER_1 = store_thm("POWER_1",
                        Term `!n. $EXP 1 n = 1`,
                        Induct_on `n` THEN ARW[POWER]);
val POWER_LT_0 = store_thm("POWER_LT_0",
                        Term `!x n. 0<x ==> 0 < $EXP x n`,
                        Induct_on `n` THEN ARW[POWER,LESS_MULT2]);

val LT_MULT_RIGHT = store_thm("LT_MULT_RIGHT",
                         Term `!x y. 0<y ==> x <= x*y`,
                        Cases_on `y` THEN ARW[]
                        THEN ONCE_REWRITE_TAC[MULT_SYM]
                        THEN ARW[MULT_CLAUSES]);


val POWER_LE = store_thm("POWER_LE",
                        Term `!x n. 0<n ==> x <= $EXP x n`,
                        Cases_on `n` THEN ARW[POWER]
                        THEN Cases_on `x` THEN ARW[LT_MULT_RIGHT,POWER_LT_0]);

Theorem POWER_LE_1:
  ! a b. 1 <= $EXP (SUC a) b
Proof
  Cases_on `b` THEN ARW[] THEN
  ‘1 <= SUC a’ by ARW[] THEN
  ‘0 < SUC n’ by ARW[] THEN
  PROVE_TAC[LESS_EQ_TRANS,POWER_LE]
QED

val POWER_MULT = store_thm("POWER_MULT",
                        Term `!x n m. $EXP x n * $EXP x m = $EXP x (n+m)`,
                        Induct_on `n`
                         THEN RW_TAC std_ss [POWER, ADD_CLAUSES, GSYM MULT_ASSOC]);

val POWER_POWER = store_thm("POWER_POWER",
                        Term `!x n m. $EXP ($EXP x n)  m = $EXP x (n*m)`,
                        Induct_on `m` THEN ARW[POWER,MULT_CLAUSES,POWER_MULT]);


val _ = export_theory();
