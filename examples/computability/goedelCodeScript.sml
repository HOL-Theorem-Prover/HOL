(*---------------------------------------------------------------------------*)
(* Goedel's encoding : injection from num list to num. See also              *)
(* numpairTheory in src/num/extra_theories.                                  *)
(*---------------------------------------------------------------------------*)

(* Interactive
quietdec := true;
app load ["primeFactorTheory", "bagTheory"];
open arithmeticTheory dividesTheory primeFactorTheory bagTheory;
quietdec := false;
*)

open HolKernel Parse boolLib bossLib
     arithmeticTheory dividesTheory primeFactorTheory bagTheory;
 
val _ = new_theory "goedelCode";

val P_EUCLIDES =  gcdTheory.P_EUCLIDES;

(*---------------------------------------------------------------------------*)
(* Goedel coding                                                             *)
(*---------------------------------------------------------------------------*)

val GCODE_def = 
 Define
  `(GCODE n [] = 1) /\
   (GCODE n (h::t) = (PRIMES(n) ** (h+1)) * GCODE (n+1) t)`;

val GOEDEL_CODE_def = Define `GOEDEL_CODE list = GCODE 0 list`;


val GCODE_EMPTY = Q.store_thm
("GCODE_EMPTY",
 `!n. GCODE n [] = 1`, 
 GEN_TAC THEN EVAL_TAC);

val ZERO_LT_GCODE = Q.store_thm
("ZERO_LT_GCODE",
 `!list n. 0 < GCODE n list`,
 Induct THEN RW_TAC list_ss [GCODE_EMPTY] THEN
 Cases_on `h` THEN EVAL_TAC THEN 
 RW_TAC list_ss [ZERO_LT_EXP,ZERO_LESS_MULT] THEN 
 METIS_TAC [INDEX_LESS_PRIMES,primePRIMES,NOT_PRIME_0, DECIDE ``(x=0) \/ 0<x``]);

val ONE_LT_GCODE = Q.store_thm
("ONE_LT_GCODE",
 `!h t n. 1 < GCODE n (h::t)`,
 RW_TAC bool_ss [GCODE_def] THEN 
 MATCH_MP_TAC ONE_LT_MULT_IMP THEN CONJ_TAC THENL
 [RW_TAC bool_ss [GSYM ADD1,EXP] THEN
  METIS_TAC [ONE_LT_MULT_IMP,ONE_LT_PRIMES,ZERO_LT_PRIMES,ZERO_LT_EXP],
  METIS_TAC [ZERO_LT_GCODE]]);

val GCODE_EQ_1 = Q.store_thm
("GCODE_EQ_1",
 `!l n. (GCODE n l = 1) = (l=[])`,
 Cases THEN RW_TAC list_ss [GCODE_EMPTY] THEN
 MATCH_MP_TAC (DECIDE``b < a ==> a<>b``) THEN 
 RW_TAC arith_ss [GCODE_def] THEN
 MATCH_MP_TAC ONE_LT_MULT_IMP THEN 
 RW_TAC bool_ss [ZERO_LT_GCODE,GSYM ADD1,EXP] THEN 
 METIS_TAC[ONE_LT_MULT_IMP,ONE_LT_PRIMES,ZERO_LT_PRIMES,ZERO_LT_EXP]);

val lem1 = Q.prove
(`!p q x. prime p /\ prime q /\ divides p (q ** x) ==> (p=q)`,
 Induct_on `x` THEN RW_TAC arith_ss [EXP,DIVIDES_ONE] THENL
 [METIS_TAC[NOT_PRIME_1],
  METIS_TAC [prime_divides_only_self,P_EUCLIDES]]);

val lem2 = Q.prove
(`!n l x. BAG_IN x (PRIME_FACTORS (GCODE (n+1) l)) ==> PRIMES n < x`,
 Induct_on `l` THENL
 [RW_TAC arith_ss [GCODE_def] THEN 
    METIS_TAC [PRIME_FACTORS_1,NOT_IN_EMPTY_BAG],
  REPEAT STRIP_TAC THEN
  `divides x (GCODE (n + 1) (h::l))` 
    by METIS_TAC [PRIME_FACTOR_DIVIDES,ZERO_LT_GCODE] THEN
  `prime x` by METIS_TAC [PRIME_FACTORS_def,ZERO_LT_GCODE] THEN
  Q.PAT_ASSUM `divides a b` MP_TAC THEN RW_TAC arith_ss [GCODE_def] THEN
  `divides x (PRIMES (n + 1) ** (h + 1)) \/ divides x (GCODE (n + 2) l)`
    by METIS_TAC [P_EUCLIDES] THENL
  [`x = PRIMES(n+1)` by METIS_TAC [lem1,primePRIMES] THEN
     RW_TAC arith_ss [] THEN METIS_TAC [INFINITE_PRIMES,ADD1],
   `PRIMES (n+1) < x` 
     by METIS_TAC [DIVISOR_IN_PRIME_FACTORS,DECIDE``n+2 = n+1+1``,ZERO_LT_GCODE]
    THEN METIS_TAC [LESS_TRANS,INFINITE_PRIMES,ADD1]]]);

val lem3 = Q.prove
(`!d m x l. BAG_IN x (PRIME_FACTORS (GCODE (m + SUC d) l)) ==> PRIMES m < x`,
 Induct THEN RW_TAC bool_ss [ADD_CLAUSES] THENL
 [METIS_TAC [ADD1,lem2],
  `PRIMES (SUC m) < x` by METIS_TAC [DECIDE``SUC(SUC(m+d)) = SUC m + SUC d``] THEN
  METIS_TAC [LESS_TRANS,INFINITE_PRIMES,ADD1]]);

val lem4 = Q.prove
(`!m n l x. m < n /\ BAG_IN x (PRIME_FACTORS (GCODE n l)) ==> PRIMES m < x`,
 METIS_TAC[lem3,LESS_ADD_1,ADD1]);

val lem5 = Q.prove
( `!l a. PRIME_FACTORS (GCODE (a + 1) l) (PRIMES a) = 0`,
 RW_TAC arith_ss [NOT_BAG_IN] THEN STRIP_TAC THEN
 METIS_TAC [lem4,DECIDE ``~(x < x) /\ a < a+1``]);

(*---------------------------------------------------------------------------*)
(* Injectivity                                                               *)
(*---------------------------------------------------------------------------*)

val GCODE_11 = Q.store_thm
("GCODE_11",
  `!l1 l2 a. (GCODE a l1 = GCODE a l2) ==> (l1=l2)`,
 Induct THENL
 [METIS_TAC [GCODE_EQ_1, GCODE_def],
  GEN_TAC THEN Induct THENL
  [METIS_TAC [GCODE_EQ_1, GCODE_def],
   POP_ASSUM (K ALL_TAC) THEN REPEAT GEN_TAC THEN 
   SIMP_TAC list_ss [GCODE_def] THEN STRIP_TAC THEN 
   `0 < PRIMES a ** (h+1) /\ 0 < PRIMES a ** (h'+1) /\
    0 < GCODE (a+1) l1 /\ 0 < GCODE (a+1) l2`
      by METIS_TAC [primePRIMES,ZERO_LT_PRIMES,ZERO_LT_EXP,ZERO_LT_GCODE] THEN 
   `PRIME_FACTORS (PRIMES a ** (h + 1) * GCODE (a + 1) l1) =
    PRIME_FACTORS (PRIMES a ** (h' + 1) * GCODE (a + 1) l2)` 
      by METIS_TAC[] THEN 
   `BAG_UNION (PRIME_FACTORS (PRIMES a ** (h + 1)))
              (PRIME_FACTORS (GCODE (a + 1) l1))
      =
    BAG_UNION (PRIME_FACTORS (PRIMES a ** (h' + 1)))
              (PRIME_FACTORS (GCODE (a + 1) l2))` 
     by METIS_TAC [PRIME_FACTORS_MULT] THEN 
   `(BAG_UNION (PRIME_FACTORS (PRIMES a ** (h + 1)))
               (PRIME_FACTORS (GCODE (a + 1) l1))) (PRIMES a) = h+1`
      by SIMP_TAC arith_ss [BAG_UNION,PRIME_FACTORS_EXP,primePRIMES,lem5] THEN 
   `(BAG_UNION (PRIME_FACTORS (PRIMES a ** (h' + 1)))
               (PRIME_FACTORS (GCODE (a + 1) l2))) (PRIMES a) = h'+1`
     by SIMP_TAC arith_ss [BAG_UNION,PRIME_FACTORS_EXP,primePRIMES,lem5] THEN 
   `h = h'` by METIS_TAC [DECIDE ``(a+1 = b+1) = (a=b)``] THEN 
   RW_TAC arith_ss [] THEN NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN 
   `PRIME_FACTORS (GCODE (a + 1) l1) = PRIME_FACTORS (GCODE (a + 1) l2)`
     by METIS_TAC [BAG_UNION_EQ_LEFT] THEN 
   METIS_TAC [PRIME_FACTORS_def]]]);

val GOEDEL_CODE_11 = Q.store_thm
("GOEDEL_CODE_11",
  `!l1 l2. (GOEDEL_CODE l1 = GOEDEL_CODE l2) ==> (l1=l2)`,
 METIS_TAC [GCODE_11,GOEDEL_CODE_def]);

(*---------------------------------------------------------------------------*)
(* TODO ... similar development as src/num/extra_theories/numpairScript.     *)
(*---------------------------------------------------------------------------*)


val _ = export_theory();
