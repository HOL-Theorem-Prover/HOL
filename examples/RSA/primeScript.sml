structure primeScript =
struct

open HolKernel Parse boolLib
     Num_conv arithmeticTheory bossLib dividesTheory ;

infix THEN THENC THENL;


val ARW = RW_TAC arith_ss;

val _ = new_theory "prime";

val PRIME = Define `prime a = ~(a=1) /\ !b. divides b a ==> (b=a) \/ (b=1)`;


val NOT_PRIME_0 = store_thm("NOT_PRIME_0",
                        Term `~(prime 0)`,
                        ARW[PRIME, ALL_DIVIDES_0]);

val NOT_PRIME_1 = store_thm("NOT_PRIME_1",
			Term `~(prime 1)`,
                        ARW[PRIME, DIVIDES_LE]);

val _ = export_theory();

end;
