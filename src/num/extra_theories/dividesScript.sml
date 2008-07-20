structure dividesScript =
struct

open HolKernel Parse boolLib BasicProvers arithmeticTheory 
     simpLib SingleStep metisLib;

val arith_ss = simpLib.++(bool_ss, numSimps.ARITH_ss)

val ARW = RW_TAC arith_ss

local open numeralTheory in end;
  (* concession to Holmake's flawed dependency analysis, which doesn't
     spot this problem *)

val _ = new_theory "divides";

val export_rewrites = export_rewrites "divides";

val divides_def = Q.new_definition
  ("divides_def",
   `divides a b = ?q. b = q*a`);

val ALL_DIVIDES_0 = store_thm("ALL_DIVIDES_0",
                        Term `!a. divides a 0`,
                        PROVE_TAC[divides_def,MULT_CLAUSES]);
val _ = export_rewrites ["ALL_DIVIDES_0"]

val ZERO_DIVIDES = store_thm(
  "ZERO_DIVIDES",
  ``divides 0 m = (m = 0)``,
  SRW_TAC [][divides_def]);
val _ = export_rewrites ["ZERO_DIVIDES"]

val DIVIDES_REFL = store_thm("DIVIDES_REFL",
			Term `!a. divides a a`,
                        PROVE_TAC[divides_def,MULT_CLAUSES]);
val _ = export_rewrites ["DIVIDES_REFL"]

val ONE_DIVIDES_ALL = store_thm("ONE_DIVIDES_ALL",
                        Term `!a. divides 1 a`,
                        PROVE_TAC[divides_def,MULT_CLAUSES]);
val _ = export_rewrites ["ONE_DIVIDES_ALL"]

val DIVIDES_ADD_1 = store_thm("DIVIDES_ADD_1",
                        Term `!a b c. divides a b /\ divides a c ==> divides a (b+c)`,
                        PROVE_TAC[divides_def,RIGHT_ADD_DISTRIB]);


val DIVIDES_ADD_2 = store_thm("DIVIDES_ADD_2",
                        Term `!a b c. divides a b /\ divides a (b+c) ==> divides a c`,
                        ARW[divides_def] THEN EXISTS_TAC (Term `q' - q`) THEN ARW[RIGHT_SUB_DISTRIB]);

val DIVIDES_SUB = store_thm("DIVIDES_SUB",
                        Term `!a b c. divides a b /\ divides a c ==> divides a (b-c)`,
                        PROVE_TAC[divides_def,RIGHT_SUB_DISTRIB]);

val DIVIDES_LE = store_thm("DIVIDES_LE",
  Term `!a b. 0<b /\ divides a b ==> a <= b`,
  Cases_on `a` THEN ARW[divides_def] THEN Cases_on `q` THENL [
    PROVE_TAC [MULT_CLAUSES,prim_recTheory.LESS_REFL],
    ARW[MULT_CLAUSES]
  ]);

val NOT_LT_DIV = store_thm("NOT_LT_DIV",
                        Term `!a b. 0<b /\ b<a ==> ~(divides a b)`,
                         PROVE_TAC[DIVIDES_LE,LESS_EQ_ANTISYM]);

val DIVIDES_ANTISYM = store_thm("DIVIDES_ANTISYM",
                        Term `!a b. divides a b /\ divides b a ==> (a = b)`,
                        REPEAT Cases
                          THEN TRY (ARW[divides_def] THEN NO_TAC)
                          THEN PROVE_TAC [LESS_EQUAL_ANTISYM,
                                    DIVIDES_LE,prim_recTheory.LESS_0]);

val DIVIDES_TRANS = store_thm(
  "DIVIDES_TRANS",
  ``!p q r. divides p q ==> divides q r ==> divides p r``,
  ARW [divides_def] THEN PROVE_TAC [MULT_ASSOC]);

val DIVIDES_MULT = store_thm("DIVIDES_MULT",
                              Term `!a b c. divides a b ==> divides a (b*c)`,
                              PROVE_TAC[divides_def,MULT_SYM,MULT_ASSOC]);

val DIVIDES_FACT = store_thm(
  "DIVIDES_FACT",
  Term `!b. 0<b ==> divides b (FACT b)`,
  Cases_on `b` THEN ARW[FACT, divides_def] THEN PROVE_TAC [MULT_COMM]);

val DIVIDES_MULT_LEFT = store_thm(
  "DIVIDES_MULT_LEFT",
  ``!n m. divides (n * m) m = (m = 0) \/ (n = 1)``,
  SIMP_TAC arith_ss [FORALL_AND_THM, EQ_IMP_THM, DISJ_IMP_THM,
                     ALL_DIVIDES_0, DIVIDES_REFL] THEN
  SIMP_TAC bool_ss [divides_def] THEN REPEAT STRIP_TAC THEN
  `m * 1 = m * (n * q)` by (POP_ASSUM (CONV_TAC o LAND_CONV o
                                       ONCE_REWRITE_CONV o C cons []) THEN
                            ASM_SIMP_TAC bool_ss [MULT_CLAUSES] THEN
                            CONV_TAC (AC_CONV(MULT_ASSOC, MULT_COMM))) THEN
  `(m = 0) \/ (n * q = 1)` by PROVE_TAC [EQ_MULT_LCANCEL] THEN
  ASM_SIMP_TAC bool_ss [] THEN
  PROVE_TAC [MULT_EQ_1]);

(*---------------------------------------------------------------------------*)
(* Definition and trivial facts about primality.                             *)
(*---------------------------------------------------------------------------*)

val prime_def = Q.new_definition
("prime_def",
 `prime a = ~(a=1) /\ !b. divides b a ==> (b=a) \/ (b=1)`);


val NOT_PRIME_0 = Q.store_thm
 ("NOT_PRIME_0",
  `~prime 0`,
  ARW[prime_def, ALL_DIVIDES_0]);
val _ = export_rewrites ["NOT_PRIME_0"]

val NOT_PRIME_1 = Q.store_thm
 ("NOT_PRIME_1",
  `~prime 1`,
  ARW[prime_def, DIVIDES_LE]);
val _ = export_rewrites ["NOT_PRIME_1"]


(*---------------------------------------------------------------------------*)
(* Directly computable version of divides                                    *)
(*---------------------------------------------------------------------------*)

val compute_divides = Q.store_thm
("compute_divides",
 `!a b. divides a b = 
        if a=0 then (b=0) else
        if a=1 then T else 
        if b=0 then T else
        (b MOD a = 0)`,
  RW_TAC arith_ss [divides_def] 
   THEN EQ_TAC 
   THEN RW_TAC arith_ss [] THENL
   [Cases_on `q` THENL 
     [RW_TAC arith_ss [],
      `0<a` by RW_TAC arith_ss [] THEN 
      METIS_TAC [MOD_MULT, MULT_SYM, ADD_CLAUSES]],
    Q.EXISTS_TAC `b` THEN RW_TAC arith_ss [],
    Q.EXISTS_TAC `0` THEN RW_TAC arith_ss [],
    `0<a` by RW_TAC arith_ss [] THEN
     let val MOD_P_inst = BETA_RULE (Q.SPECL[`\x. (x = 0)`,`b`,`a`] MOD_P)
     in METIS_TAC [MOD_P_inst,MULT_SYM, ADD_CLAUSES]
     end]);

val _ = computeLib.add_persistent_funs [("compute_divides",compute_divides)];

val _ = export_theory();

end
