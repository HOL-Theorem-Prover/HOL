(*---------------------------------------------------------------------------*)
(* Challenge from Freek Wiedijk: the square root of two is not rational.     *)
(* I adapted a proof in HOL Light by John Harrison.                          *)
(*---------------------------------------------------------------------------*)
 
app load ["intLib", "transcTheory"];   open arithmeticTheory BasicProvers;

(*---------------------------------------------------------------------------*)
(* Need a predicate on reals that picks out the rational ones                *)
(*---------------------------------------------------------------------------*)

val Rational_def = Define `Rational r = ?p q. ~(q=0) /\ (abs(r) = &p / &q)`;

(*---------------------------------------------------------------------------*)
(* Trivial lemmas                                                            *)
(*---------------------------------------------------------------------------*)

val EXP_2 = Q.prove
(`!n:num. n**2 = n*n`,
 RW_TAC arith_ss [EXP,MULT_CLAUSES,TWO,ONE]);

val EXP2_LEM = Q.prove
(`!x y:num. ((2*x)**2 = 2*(y**2)) = (2*x**2 = y**2)`,
 RW_TAC arith_ss [EXP_2,TWO,GSYM MULT_ASSOC] 
 THEN PROVE_TAC [MULT_ASSOC,MULT_SYM]);

(*---------------------------------------------------------------------------*)
(* Lemma: squares are not doubles of squares.                                *)
(*---------------------------------------------------------------------------*)

val lemma = Q.prove
(`!m n:num. (m**2 = 2 * n**2) ==> (m=0) /\ (n=0)`,
 completeInduct_on `m` THEN NTAC 2 STRIP_TAC THEN
  `?k. m = 2*k` by PROVE_TAC [EVEN_DOUBLE,EXP_2,EVEN_MULT,EVEN_EXISTS] 
                THEN VAR_EQ_TAC THEN
  `?p. n = 2*p` by PROVE_TAC[EVEN_DOUBLE,EXP_2,EVEN_MULT,EVEN_EXISTS,EXP2_LEM] 
                THEN VAR_EQ_TAC THEN
  `k**2 = 2*p**2` by PROVE_TAC [EXP2_LEM] THEN 
  `(k=0) \/ k < 2*k` by intLib.COOPER_TAC 
  THENL [Q.PAT_ASSUM `k**2 = M` MP_TAC THEN ASM_REWRITE_TAC [EXP_2], ALL_TAC]
  THEN PROVE_TAC [MULT_EQ_0, MULT_0, DECIDE (Term `~(2 = 0n)`)]);

(*---------------------------------------------------------------------------*)
(* The final proof works by moving the problem from R to N, then uses lemma  *)
(*---------------------------------------------------------------------------*)

local open transcTheory realTheory
in
val SQRT_2_IRRATIONAL = Q.prove
(`~Rational (sqrt 2r)`,
 RW_TAC std_ss [Rational_def,abs,SQRT_POS_LE,REAL_POS]
  THEN Cases_on `q = 0` THEN ASM_REWRITE_TAC []
  THEN SPOSE_NOT_THEN (MP_TAC o Q.AP_TERM `\x. x pow 2`)
  THEN RW_TAC arith_ss [SQRT_POW_2,REAL_POS,REAL_POW_DIV,
                        REAL_EQ_RDIV_EQ,REAL_LT, REAL_POW_LT]
  THEN REWRITE_TAC [REAL_OF_NUM_POW,REAL_MUL,REAL_INJ]
  THEN PROVE_TAC [lemma])
end;
