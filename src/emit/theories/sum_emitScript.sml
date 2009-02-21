open HolKernel boolLib bossLib Parse;
open EmitML sumTheory;

val _ = new_theory "sum_emit";

val OUTL_INR = Q.prove
(`!y. OUTL(INR y:'a+'b) =
      FAIL OUTL ^(mk_var("applied to INR",bool)) (INR y:'a+'b)`,
 REWRITE_TAC [combinTheory.FAIL_THM]);

val OUTR = Q.prove
(`(!x. OUTR(INL x:'a+'b) =
      FAIL OUTR ^(mk_var("applied to INL",bool)) (INL x:'a+'b)) /\
  (!y. OUTR(INR y:'a+'b) = y)`,
 REWRITE_TAC [combinTheory.FAIL_THM,OUTR]);

val ISL_THM = Q.prove
(`(!x. ISL (INL x:'a+'b) = T) /\ !y. ISL (INR y:'a+'b) = F`,
 REWRITE_TAC[ISL]);

val ISR_THM = Q.prove
(`(!x. ISR (INL x:'a+'b) = F) /\ !y. ISR (INR y:'a+'b) = T`,
 REWRITE_TAC[ISR])

val defs =
  DATATYPE `sum = INL of 'a | INR of 'b`
  :: map DEFN [CONJ OUTL OUTL_INR, OUTR, ISL_THM, ISR_THM]

val _ = eSML "sum" defs
val _ = eCAML "sum" defs;

val _ = export_theory ();
