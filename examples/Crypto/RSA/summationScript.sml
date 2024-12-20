open HolKernel Parse boolLib

(* interactive mode
app load ["bossLib", "arithmeticTheory", "numLib"];
*)

open bossLib arithmeticTheory numLib;

val ARW = RW_TAC arith_ss;

val _ = new_theory "summation";

val SUMMATION =
 Define
     `(summation j 0 f       = 0)
   /\ (summation j (SUC i) f = f j + summation (SUC j) i f)`;


val SUMMATION_1 = store_thm("SUMMATION_1",
Term `!i j f. summation j (SUC i) f = f j + summation (SUC j) i f`,
  ARW[SUMMATION]);


val SUMMATION_2 = store_thm("SUMMATION_2",
Term `!i j f. summation j (SUC i) f = summation j i f + f (i + j)`,
  Induct_on `i`
    THEN ONCE_REWRITE_TAC[SUMMATION]
    THEN ARW[ADD_CLAUSES] THEN ARW[SUMMATION]);


val SUMMATION_EXT = store_thm("SUMMATION_EXT",
Term `!i j f g.
        (!k. k < i ==> (f (j + k) = g (j + k)))
          ==>
        (summation j i f = summation j i g)`,
Induct_on `i`
  THEN ARW[SUMMATION]
  THEN `f j:num = f (j+0)` by REWRITE_TAC[ADD_CLAUSES]
  THEN ARW[]
  THEN `!k. k < i ==> (f (SUC j + k):num = g (SUC j + k))`
     by (ARW[ADD_CLAUSES]
           THEN `f (SUC (j+k)):num = f (j + SUC k)` by REWRITE_TAC[ADD_CLAUSES]
           THEN ARW[ADD_CLAUSES])
  THEN RES_TAC);


val SUMMATION_ADD = store_thm("SUMMATION_ADD",
Term `!i j f g.
  summation j i f + summation j i g = summation j i (\n. (f n) + g n)`,
Induct_on `i` THEN ARW [SUMMATION]);


val SUMMATION_TIMES = store_thm("SUMMATION_TIMES",
Term `!i j k f. k * summation j i f = summation j i (\n.  k * f n)`,
  Induct_on `i` THEN ARW[SUMMATION,LEFT_ADD_DISTRIB]);


val INV_SUMMATION = store_thm("INV_SUMMATION",
Term `!i j f P.
       P 0 /\
       (! a b. (P a) /\ (P b) ==> P (a + b)) /\
       (!k. k < i ==> P (f (k + j)))
       ==>
          P (summation j i f)`,
Induct_on `i` THEN ARW[SUMMATION]
  THEN sg `P (f (j:num):num) : bool`
  THENL [
   `f j:num = f (j+0)` by REWRITE_TAC[ADD_CLAUSES]
     THEN ASM_REWRITE_TAC[] THEN ARW[],
   Q.PAT_ASSUM `!a b. Q a b` (fn th => MATCH_MP_TAC th THEN ASSUME_TAC th)
   THEN ARW[]
   THEN Q.PAT_ASSUM `!j f P. Q j f P` MATCH_MP_TAC
   THEN ARW[]
   THEN `SUC k < SUC i` by DECIDE_TAC
   THEN `P (f (j + SUC k))` by RES_TAC
   THEN POP_ASSUM MP_TAC
   THEN POP_ASSUM_LIST (K ALL_TAC)
   THEN PROVE_TAC [ADD_CLAUSES, ADD_COMM]]);


val SUMMATION_SHIFT = store_thm("SUMMATION_SHIFT",
Term `!i j f. summation j i f = summation (SUC j) i (\n. f (n - 1))`,
 Induct_on `i`
  THEN  REWRITE_TAC[SUMMATION]
  THEN BETA_TAC THEN REWRITE_TAC[SUC_SUB1]
  THEN POP_ASSUM (fn thm => REWRITE_TAC[GSYM thm]));

val SUMMATION_SHIFT_P = store_thm("SUMMATION_SHIFT_P",
Term `!i j f. summation (SUC j) i f = summation j i (\n. f (n + 1))`,
  Induct_on `i` THEN ARW[SUMMATION,ADD1]);


val _ = export_theory();
