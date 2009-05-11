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
  `(GCODE i [] = 1) /\
   (GCODE i (h::t) = (PRIMES(i) ** (h+1)) * GCODE (i+1) t)`;

val ENCODE_def = Define `ENCODE list = GCODE 0 list`;

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

val ENCODE_11 = Q.store_thm
("ENCODE_11",
  `!l1 l2. (ENCODE l1 = ENCODE l2) ==> (l1=l2)`,
 METIS_TAC [GCODE_11,ENCODE_def]);

(*---------------------------------------------------------------------------*)
(* Explicitly give decoder ... similar development as                        *)
(*                                                                           *)
(*       src/num/extra_theories/numpairScript.                               *)
(*---------------------------------------------------------------------------*)

val GDECODE_def = 
 tDefine
 "GDECODE"
 `GDECODE i gn = 
   if gn = 0 then NONE else
   if gn = 1 then SOME [] else
   case PRIME_FACTORS gn (PRIMES i)
     of 0 -> NONE
     || SUC n ->
          case GDECODE (i+1) (gn DIV (PRIMES i ** (n+1)))
           of NONE -> NONE
           || SOME l -> SOME (n::l)`
(WF_REL_TAC `measure SND` THEN
 RW_TAC arith_ss [DECIDE ``x <> 0 = 0 < x``] THEN
 MATCH_MP_TAC DIV_LESS THEN 
 RW_TAC arith_ss [ONE_LT_EXP,ONE_LT_PRIMES,ZERO_LT_EXP]);

val GDECODE_ind = fetch "-" "GDECODE_ind";

val lem6 = Q.prove
(`PRIME_FACTORS ((PRIMES i ** (h+1)) * GCODE (i+1) t) (PRIMES i) = h+1`,
 `0 < GCODE (i+1) t` by METIS_TAC [ZERO_LT_GCODE] THEN
 `0 < PRIMES i ** (h+1)` by RW_TAC arith_ss [ZERO_LT_EXP,ZERO_LT_PRIMES] THEN
 RW_TAC arith_ss [PRIME_FACTORS_MULT,ZERO_LT_EXP, ZERO_LT_PRIMES,
       ZERO_LT_GCODE,BAG_UNION,PRIME_FACTORS_EXP,primePRIMES,lem5]);

val lem7 = Q.prove
(`(PRIME_FACTORS (GCODE i (h::t)) (PRIMES i) = SUC n) ==> (h=n)`,
 RW_TAC arith_ss [GCODE_def] THEN FULL_SIMP_TAC arith_ss [lem6]);

val lem8 = Q.prove
(`GCODE i (h::t) DIV (PRIMES i ** (h+1)) = GCODE (i+1) t`,
 RW_TAC arith_ss [GCODE_def] THEN 
 RW_TAC bool_ss [Once MULT_SYM] THEN 
 `0 < PRIMES i ** (h+1)` by RW_TAC arith_ss [ZERO_LT_EXP,ZERO_LT_PRIMES] THEN
 RW_TAC arith_ss [MULT_DIV]);

val lem9 = Q.prove
(`!i h t. GCODE (i+1) t < GCODE i (h::t)`,
 RW_TAC arith_ss [GCODE_def,ZERO_LT_GCODE,ONE_LT_EXP,ONE_LT_PRIMES]);

val lem10 = Q.prove
(`!gn i nl. (gn = GCODE i nl) ==> (GDECODE i gn = SOME nl)`,
 completeInduct_on `gn` THEN RW_TAC arith_ss [Once GDECODE_def] THENL
 [METIS_TAC [ZERO_LT_GCODE,DECIDE ``0 < x = x <> 0``],
  FULL_SIMP_TAC list_ss [GCODE_EQ_1],
  `?h t. nl = h::t` by METIS_TAC [listTheory.list_CASES,GCODE_EQ_1] THEN
  NTAC 2 (Q.PAT_ASSUM `a <> b` (K ALL_TAC)) THEN POP_ASSUM SUBST_ALL_TAC THEN
  REPEAT CASE_TAC THENL
  [POP_ASSUM MP_TAC THEN RW_TAC arith_ss [GCODE_def] THEN 
    `0 < GCODE (i+1) t` by METIS_TAC [ZERO_LT_GCODE] THEN 
     `0 < PRIMES i ** (h + 1)` by RW_TAC arith_ss [ZERO_LT_EXP,ZERO_LT_PRIMES] THEN
     RW_TAC arith_ss 
           [PRIME_FACTORS_MULT,BAG_UNION,PRIME_FACTORS_EXP,primePRIMES],
   `h = n` by METIS_TAC [lem7] THEN RW_TAC arith_ss [] THEN 
      FULL_SIMP_TAC arith_ss [lem8] THEN 
      `GDECODE (i+1) (GCODE (i+1) t) = SOME t` by METIS_TAC [lem9] THEN
      FULL_SIMP_TAC arith_ss [],
   `h = n` by METIS_TAC [lem7] THEN RW_TAC arith_ss [] THEN 
      FULL_SIMP_TAC arith_ss [lem8] THEN 
      `GDECODE (i+1) (GCODE (i+1) t) = SOME t` by METIS_TAC [lem9] THEN
      FULL_SIMP_TAC arith_ss []]]);

val GDECODE_GCODE = Q.store_thm
("GDECODE_GCODE",
 `!nl i. GDECODE i (GCODE i nl) = SOME nl`,
 METIS_TAC [lem10]);

val DECODE_def = Define `DECODE gn = THE (GDECODE 0 gn)`;

val DECODE_ENCODE = Q.store_thm
("DECODE_ENCODE",
 `!nl. DECODE (ENCODE nl) = nl`,
 RW_TAC arith_ss [DECODE_def, ENCODE_def,GDECODE_GCODE,optionTheory.THE_DEF]);


(*---------------------------------------------------------------------------*)
(* Standard list operators lifted to gnums                                   *)
(*---------------------------------------------------------------------------*)

val gNIL_def  = Define `gNIL = ENCODE []`;
val gCONS_def = Define `gCONS n gn = ENCODE (n::DECODE gn)`;
val gHD_def   = Define `gHD gn = HD (DECODE gn)`;
val gTL_def   = Define `gTL gn = ENCODE (TL (DECODE gn))`;
val gLEN_def  = Define `gLEN gn = LENGTH (DECODE gn)`;
val gMAP_def  = Define `gMAP f gn = ENCODE (MAP f (DECODE gn))`;
val gAPPEND_def = Define`gAPPEND gn1 gn2 = ENCODE (DECODE gn1 ++ DECODE gn2)`;

val gCONS_ENCODE = Q.store_thm
("gCONS_ENCODE",
 `!nl. gCONS n (ENCODE nl) = ENCODE (n::nl)`,
 RW_TAC arith_ss [gCONS_def, DECODE_ENCODE]);

val gLEN_ENCODE = Q.store_thm
("gLEN_ENCODE",
 `!nl. gLEN (ENCODE nl) = LENGTH nl`,
 RW_TAC arith_ss [gLEN_def, DECODE_ENCODE]);

val gAPPEND_ENCODE = Q.store_thm
("gAPPEND_ENCODE",
 `!nl1 nl2. gAPPEND (ENCODE nl1) (ENCODE nl2) = ENCODE (APPEND nl1 nl2)`,
 RW_TAC arith_ss [gAPPEND_def, DECODE_ENCODE]);

val gMAP_ENCODE = Q.store_thm
("gMAP_ENCODE",
 `gMAP f (ENCODE nl) = ENCODE (MAP f nl)`,
 RW_TAC arith_ss [gMAP_def, DECODE_ENCODE]);


val _ = export_theory();
