structure summationScript =
struct

open HolKernel Parse boolLib bossLib
     arithmeticTheory numLib;

infix THEN THENC THENL;
infix 8 by;
val ARW = RW_TAC arith_ss;

val _ = new_theory "summation";

val SUMMATION =
 Define
     `(summation 0 j f       = f j)
   /\ (summation (SUC i) j f = f j + summation i (SUC j) f)`;


val SUMMATION_1 = store_thm("SUMMATION_1",
Term `!i j f. summation (SUC i) j f = f j + summation i (SUC j) f`,
  ARW[SUMMATION]);


val SUMMATION_2 = store_thm("SUMMATION_2",
Term `!i j f. summation (SUC i) j f = summation i j f + f (SUC (i+j))`,
  Induct_on `i`
    THEN ONCE_REWRITE_TAC[SUMMATION]
    THEN ARW[ADD_CLAUSES] THEN ARW[SUMMATION]);


val SUMMATION_EXT = store_thm("SUMMATION_EXT",
Term `!i j f g.
        (!k. k <= i ==> (f (j+k) = g (j+k)))
          ==>
        (summation i j f = summation i j g)`,
Induct_on `i`
  THEN ARW[SUMMATION]
  THEN `f j:num = f (j+0)` by REWRITE_TAC[ADD_CLAUSES]
  THEN ARW[]
  THEN `!k. k <= i ==> (f (SUC j + k):num = g (SUC j + k))`
     by ARW[ADD_CLAUSES]
  THENL [
    `f (SUC (j+k)):num = f (j + SUC k)` by REWRITE_TAC[ADD_CLAUSES]
       THEN ARW[ADD_CLAUSES],
    RES_TAC
  ]);


val SUMMATION_ADD = store_thm("SUMMATION_ADD",
Term `!i j f g.
  summation i j f + summation i j g = summation i j (\n. (f n) + g n)`,
Induct_on `i` THEN ARW [SUMMATION]);


val SUMMATION_TIMES = store_thm("SUMMATION_TIMES",
Term `!i j k f. k * summation i j f = summation i j (\n.  k * f n)`,
  Induct_on `i` THEN ARW[SUMMATION,LEFT_ADD_DISTRIB]);


val INV_SUMMATION = store_thm("INV_SUMMATION",
Term `!i j f P.
       (! a b. (P a) /\ (P b) ==> P (a+b)) /\
       (!k. k <= i ==> P (f (k+j)))
       ==>
          P (summation i j f)`,
Induct_on `i` THEN ARW[SUMMATION]
  THEN `P (f (j:num):num) : bool` by ALL_TAC
  THENL [
   `f j:num = f (j+0)` by REWRITE_TAC[ADD_CLAUSES]
     THEN ASM_REWRITE_TAC[] THEN ARW[],
   `!k. k <= i ==> P (f (k + SUC j):num)` by ARW[ADD_CLAUSES]
    THENL [
     `f (SUC (j+k)):num = f (j + SUC k)` by REWRITE_TAC[ADD_CLAUSES]
        THEN ASM_REWRITE_TAC[] THEN ARW[],
     REPEAT RES_TAC
    ]
  ]);


val SUMMATION_SHIFT = store_thm("SUMMATION_SHIFT",
Term `!i j f. summation i j f = summation i (SUC j) (\n. f (n-1))`,
 Induct_on `i`
  THEN  REWRITE_TAC[SUMMATION]
  THENL [
    ARW[],
    BETA_TAC THEN REWRITE_TAC[SUC_SUB1]
     THEN POP_ASSUM (fn thm => REWRITE_TAC[SYM (SPEC_ALL thm)])
  ]);


val SUMMATION_SHIFT_P = store_thm("SUMMATION_SHIFT_P",
Term `!i j f. summation i (SUC j) f = summation i j (\n. f (n+1))`,
  Induct_on `i` THEN ARW[SUMMATION,ADD1]);


val _ = export_theory();

end;
