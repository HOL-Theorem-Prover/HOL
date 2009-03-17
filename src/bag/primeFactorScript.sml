(*---------------------------------------------------------------------------*)
(* Fundamental theorem of arithmetic for num.                                *)
(*---------------------------------------------------------------------------*)

open HolKernel Parse boolLib simpLib BasicProvers SingleStep metisLib
     bagTheory dividesTheory arithmeticTheory;

(* Interactive
quietdec := true;
app load ["dividesTheory", "gcdTheory", "bagTheory"];
open dividesTheory bagTheory arithmeticTheory;
quietdec := false;
*)

val _ = new_theory "primeFactor";

infix ++;
val std_ss =
     (boolSimps.bool_ss ++ pairSimps.PAIR_ss ++ optionSimps.OPTION_ss ++
      numSimps.REDUCE_ss ++ sumSimps.SUM_ss ++ combinSimps.COMBIN_ss ++
      numSimps.ARITH_RWTS_ss);

val arith_ss = std_ss ++ numSimps.ARITH_DP_ss
val DECIDE = numLib.ARITH_PROVE;

fun DECIDE_TAC (g as (asl,_)) =
((MAP_EVERY UNDISCH_TAC (filter numSimps.is_arith_asm asl)
      THEN numLib.ARITH_TAC)
 ORELSE
 tautLib.TAUT_TAC
 ORELSE
 NO_TAC) g;


val MULT_LEFT_CANCEL = Q.prove
(`!m n p. 0 < m ==> ((m*n = m*p) = (n=p))`,
 Cases_on `m` THEN RW_TAC arith_ss []);

val PRIME_FACTORS_EXIST = Q.store_thm
("PRIME_FACTORS_EXIST",
 `!n. 1 < n ==>
        ?b. FINITE_BAG b /\ 
            (!m. BAG_IN m b ==> prime m) /\
            (n = BAG_GEN_PROD b 1)`,
 completeInduct_on `n` THEN STRIP_TAC THEN Cases_on `prime n` THENL
 [Q.EXISTS_TAC `{|n|}` THEN 
    SRW_TAC [] [BAG_GEN_PROD_TAILREC,BAG_GEN_PROD_EMPTY],
  `?m. prime m /\ divides m n` by RW_TAC arith_ss [PRIME_FACTOR] THEN
  `?q. m * q = n` by METIS_TAC [divides_def,MULT_SYM] THEN 
  `q < n` by
     (STRIP_ASSUME_TAC (DECIDE ``q < n \/ (q=n) \/ n < q``) THENL
      [FULL_SIMP_TAC arith_ss [MULT_EQ_ID] THEN METIS_TAC [NOT_PRIME_1],
       `0 < m /\ 0 < q` by METIS_TAC [ZERO_LESS_MULT,DECIDE ``0 < 1``,LESS_TRANS] THEN
       RW_TAC arith_ss [] THEN
       `(m=1) \/ 1 < m` by DECIDE_TAC THEN METIS_TAC [NOT_PRIME_1]]) THEN
  `1 < q` by 
     (STRIP_ASSUME_TAC (DECIDE ``(q = 0) \/ (q=1) \/ 1 < q``) THEN 
      RW_TAC arith_ss [] THEN METIS_TAC [MULT_RIGHT_1]) THEN
  (* use IH *)
  `?b. FINITE_BAG b /\ (!k. BAG_IN k b ==> prime k) /\
       (q = BAG_GEN_PROD b 1)` by METIS_TAC [] THEN
  Q.EXISTS_TAC `BAG_INSERT m b` THEN SRW_TAC [][] THENL 
  [METIS_TAC [], METIS_TAC [], METIS_TAC [BAG_GEN_PROD_REC]]]);

val PRIME_FACTORS_def = new_specification
("PRIME_FACTORS_def",
 ["PRIME_FACTORS"],
 SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM] PRIME_FACTORS_EXIST);

val lem1 = Q.prove
(`!b. FINITE_BAG b
     ==> !m. prime m /\ 
             divides m (BAG_GEN_PROD b 1) /\ 
             (!x. BAG_IN x b ==> prime x)
     ==> BAG_IN m b`,
 HO_MATCH_MP_TAC STRONG_FINITE_BAG_INDUCT THEN REPEAT STRIP_TAC THENL
 [FULL_SIMP_TAC arith_ss [BAG_GEN_PROD_EMPTY] THEN 
    METIS_TAC [DIVIDES_ONE,NOT_PRIME_1],
  Q.PAT_ASSUM `divides p q` MP_TAC THEN RW_TAC arith_ss [BAG_GEN_PROD_REC] THEN
    METIS_TAC [gcdTheory.P_EUCLIDES,prime_divides_only_self,BAG_IN_BAG_INSERT]]);

(*---------------------------------------------------------------------------*)
(* Uniqueness.                                                               *)
(* Sketch of the proof. When bag b1 is non-empty it has a prime p in it. We  *)
(* can show p divides BAG_PROD b2, so p is also in b2 (because p is prime).  *)
(* Let b1' = b1-p and b2' = b2-p. Then b1' = b2', by induction hypothesis.   *)
(* Thus b1=b2. The argument uses a lemma derived from gcdTheory.P_EUCLIDES,  *)
(* which says that p divides (a*b) ==> p divides a or p divides b.           *)
(*---------------------------------------------------------------------------*)

val UNIQUE_PRIME_FACTORS = store_thm
("UNIQUE_PRIME_FACTORS",
 ``!n b1 b2. 
   (FINITE_BAG b1 /\ (!m. BAG_IN m b1 ==> prime m) /\ (n=BAG_GEN_PROD b1 1)) /\
   (FINITE_BAG b2 /\ (!m. BAG_IN m b2 ==> prime m) /\ (n=BAG_GEN_PROD b2 1)) 
    ==> (b1 = b2)``,
completeInduct_on `n` THEN 
 REPEAT STRIP_TAC THEN POP_ASSUM SUBST_ALL_TAC THEN 
 `(b1 = {||}) \/ ?b1' e. b1 = BAG_INSERT e b1'` by METIS_TAC [BAG_cases] THENL
 [RW_TAC arith_ss [] THEN 
    STRIP_ASSUME_TAC (ISPEC ``b2:num bag`` BAG_cases) THEN 
    FULL_SIMP_TAC arith_ss [] THEN RW_TAC std_ss [] THEN 
    Q.PAT_ASSUM `BAG_GEN_PROD a b = BAG_GEN_PROD c d` MP_TAC THEN 
    `FINITE_BAG b0` by METIS_TAC [FINITE_BAG_THM] THEN 
    ASM_SIMP_TAC arith_ss [BAG_GEN_PROD_EMPTY,BAG_GEN_PROD_TAILREC] THEN 
    STRIP_TAC THEN `e = 1` by METIS_TAC [BAG_GEN_PROD_EQ_1] THEN
    METIS_TAC [BAG_GEN_PROD_ALL_ONES, NOT_PRIME_1, BAG_IN_BAG_INSERT],
  `prime e` by METIS_TAC [BAG_IN_BAG_INSERT] THEN RW_TAC std_ss [] THEN 
  `FINITE_BAG b1'` by METIS_TAC [FINITE_BAG_THM] THEN 
 Q.PAT_ASSUM `p = q` MP_TAC THEN RW_TAC std_ss [BAG_GEN_PROD_REC] THEN 
 `divides e (BAG_GEN_PROD b2 1)` by METIS_TAC [divides_def,MULT_SYM] THEN 
 `BAG_IN e b2` by METIS_TAC [lem1] THEN
 `?b2'. b2 = BAG_INSERT e b2'` by METIS_TAC [BAG_DECOMPOSE] THEN 
 RW_TAC std_ss [] THEN
 `FINITE_BAG b2'` by METIS_TAC [FINITE_BAG_THM] THEN 
 Q.PAT_ASSUM `p = q` MP_TAC THEN RW_TAC arith_ss [BAG_GEN_PROD_REC] THEN 
 `0 < e` by METIS_TAC [NOT_ZERO_LT_ZERO,NOT_PRIME_0] THEN 
 FULL_SIMP_TAC arith_ss [MULT_LEFT_CANCEL] THEN POP_ASSUM (K ALL_TAC) THEN
 `BAG_GEN_PROD b2' 1 < BAG_GEN_PROD (BAG_INSERT e b2') 1` 
   by (RW_TAC arith_ss [BAG_GEN_PROD_REC] THEN
       METIS_TAC [BAG_GEN_PROD_POSITIVE,BAG_IN_BAG_INSERT,NOT_ZERO_LT_ZERO,
             NOT_PRIME_0,DECIDE``!n.(n=0) \/ (n=1) \/ 1<n``,NOT_PRIME_1]) THEN
 `b2' = b1'` by METIS_TAC[FINITE_BAG_THM,BAG_IN_BAG_INSERT] THEN
METIS_TAC [BAG_INSERT_ONE_ONE]]);


val PRIME_FACTORIZATION = store_thm
("PRIME_FACTORIZATION",
 ``!n. 1 < n ==> 
      !b. FINITE_BAG b /\ (!x. BAG_IN x b ==> prime x) /\
          (BAG_GEN_PROD b 1 = n) ==> 
      (b = PRIME_FACTORS n)``,
 METIS_TAC [PRIME_FACTORS_def,UNIQUE_PRIME_FACTORS]);

val _ = export_theory();
