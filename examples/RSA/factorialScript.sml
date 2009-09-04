structure factorialScript =

struct

open HolKernel Parse boolLib bossLib
     arithmeticTheory;

infix THEN THENC THENL;
val ARW = RW_TAC arith_ss;


val _ = new_theory "factorial";

val FACT =
 Define
     `(fact 0 = 1)
  /\  (fact (SUC n) = fact n * SUC n)`;


val FACT_GT_0 = store_thm("FACT_GT_0",
			Term `!n. 0 < fact(n)`,
			Induct_on `n` THEN ARW[FACT, LESS_MULT2]);

val _ = export_theory();

end;


