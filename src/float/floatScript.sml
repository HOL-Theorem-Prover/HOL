
(* ========================================================================= *)
(* Useful properties of floating point numbers.                              *)
(* ========================================================================= *)

(*---------------------------------------------------------------------------*
 * First, make standard environment available.                               *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib;

(*---------------------------------------------------------------------------*
 * Next, bring in extra tools used.                                          *
 *---------------------------------------------------------------------------*)

(*app load ["Psyntax", "hol88Lib", "numTheory", "prim_recTheory", "Ho_Rewrite", "ieeeTheory", "reduceLib", "tautLib",
            "jrhUtils", "Canon_Port", "AC", "Arbint", "prim_recTheory", "realTheory", "pred_setTheory",
            "pairTheory", "mesonLib", "bossLib", "Num_conv", "Canon_Port", "RealArith",
            "numLib", "arithmeticTheory", "listTheory", "rich_listTheory", "liteLib", "res_quanTheory",
            "transcTheory", "Lib"]; *)


open Psyntax hol88Lib numTheory prim_recTheory Ho_Rewrite ieeeTheory reduceLib tautLib
     jrhUtils Canon_Port AC Arbint prim_recTheory realTheory pred_setTheory
     pairTheory mesonLib  bossLib Num_conv Canon_Port RealArith
     numLib arithmeticTheory listTheory rich_listTheory liteLib res_quanTheory
     transcTheory Lib;

(*---------------------------------------------------------------------------*
 * Create the theory.                                                        *
 *---------------------------------------------------------------------------*)

val _ = new_theory "float";

val Suff = Q_TAC SUFF_TAC ;

(* ---------------------------------------------------------------------------- *)
(* Auxiliary lemmas.                                                            *)
(* ---------------------------------------------------------------------------- *)

val REAL_OF_NUM_LT = store_thm (
  "REAL_OF_NUM_LT",
  (--`! m n. &m < &n = m < n`--),
  RW_TAC arith_ss [real_lt] THEN
  RW_TAC arith_ss [REAL_OF_NUM_LE]);

(*-----------------------*)

val TWO_EXP_GE_1 = store_thm (
  "TWO_EXP_GE_1",
  (--`!(n:num). (1 <= 2 EXP n)`--),
  REPEAT GEN_TAC THEN
  RW_TAC arith_ss [GSYM REAL_OF_NUM_LE] THEN
  RW_TAC arith_ss [GSYM REAL_OF_NUM_POW] THEN
  RW_TAC arith_ss [POW_2_LE1 ]);

(*-----------------------*)

val egtff = store_thm (
  "egtff",
  (--`(8:num) = (4:num) + (4:num)`--),
  RW_TAC arith_ss []);

(*-----------------------*)

val ftt = store_thm (
  "ftt",
  (--`(4:num) = (2:num) + (2:num)`--),
  RW_TAC arith_ss []);

(*-----------------------*)

val tpetfs = store_thm (
  "tpetfs",
  (--`(&2 pow (8:num)) = &256`--),
  REWRITE_TAC[egtff] THEN
  REWRITE_TAC[POW_ADD ] THEN
  REWRITE_TAC[ftt] THEN
  REWRITE_TAC[POW_ADD ] THEN
  REWRITE_TAC[POW_2 ] THEN
  REAL_ARITH_TAC);

(*-----------------------*)

val egt1 = store_thm (
  "egt1",
  (--`&1 < &8`--),
  REAL_ARITH_TAC);

(*-----------------------*)

val temonz = store_thm (
  "temonz",
  (--`~ ((2 EXP 8 - 1) = 0)`--),
  RW_TAC arith_ss [] THEN
  RW_TAC arith_ss [NOT_LESS_EQUAL] THEN
  REPEAT GEN_TAC THEN
  RW_TAC arith_ss [GSYM REAL_OF_NUM_LT] THEN
  RW_TAC arith_ss [GSYM REAL_OF_NUM_POW] THEN
  MP_TAC POW_2_LT THEN
  DISCH_THEN (MP_TAC o SPEC (--`8:num`--)) THEN
  MP_TAC egt1 THEN REAL_ARITH_TAC);

(*-----------------------*)

val tteettto =  store_thm (
  "tteettto",
  (--`(23:num) = (8:num) + (8:num) + (2:num) + (2:num) + (2:num) + (1:num)`--),
  RW_TAC arith_ss []);

(*-----------------------*)

val tptteteesze = store_thm (
  "tptteteesze",
  (--`(&2 pow (23:num)) = &8388608`--),
  REWRITE_TAC[tteettto] THEN
  REWRITE_TAC[POW_ADD,tpetfs,POW_2,POW_1 ] THEN
  REAL_ARITH_TAC);

(*-----------------------*)

val tfflttfs = store_thm (
  "tfflttfs",
  (--`& 255 < & 256`--),
  REAL_ARITH_TAC);

(*--------------------------------------------------------------*)

val inv23gt0 = store_thm (
  "inv23gt0",
  (--`&0 < inv (&2 pow 23)`--),
  RW_TAC arith_ss [REAL_LT_INV_EQ] THEN
  MATCH_MP_TAC REAL_POW_LT THEN
  REWRITE_TAC[num_CONV(--`2:num`--)] THEN
  RW_TAC arith_ss [SUC_NOT, REAL_NZ_IMP_LT]);

(*-----------------------*)

val v23not0 = store_thm (
  "v23not0",
  (--` ~ ((&2 pow 23) = &0)`--),
  MATCH_MP_TAC POW_NZ THEN
  REWRITE_TAC[num_CONV(--`2:num`--)] THEN
  RW_TAC arith_ss [SUC_NOT, REAL_NZ_IMP_LT] THEN
  RW_TAC arith_ss [REAL] THEN
  REAL_ARITH_TAC);

(*---------------------------*)

val v127not0 = store_thm (
  "v127not0",
  (--` ~ (((&2:real) pow (127:num)) = (&0:real))`--),
  MATCH_MP_TAC POW_NZ THEN
  REWRITE_TAC[num_CONV(--`2:num`--)] THEN
  RW_TAC arith_ss [SUC_NOT, REAL_NZ_IMP_LT] THEN
  RW_TAC arith_ss [REAL] THEN
  REAL_ARITH_TAC);

(*---------------------------*)

val noteteeszegtz = store_thm (
  "noteteeszegtz",
  (--` (&0:real) < &8388608`--),
  REAL_ARITH_TAC);

(*---------------------------*)

val lt1eqmul = store_thm (
  "lt1eqmul",
  (--`x < &1:real = x * &8388608:real < &8388608:real`--),
  REAL_ARITH_TAC);

(*---------------------------*)

val twogz = store_thm (
  "twogz",
  (--`!n. (&0:real) < (&2:real) pow n`--),
  MATCH_MP_TAC REAL_POW_LT THEN
  REAL_ARITH_TAC);

(*---------------------------*)

val not2eqz = store_thm (
  "not2eqz",
  (--`~ (&2:real = &0)`--),
  REAL_ARITH_TAC);

(*---------------------------*)

val tittfittt = store_thm (
  "tittfittt",
  (--`&2:real * inv (&2 pow 24) = inv (&2 pow 23)`--),
  REWRITE_TAC [GSYM real_div] THEN
  REWRITE_TAC[num_CONV (--`24:num`--)] THEN
  REWRITE_TAC[REAL_OF_NUM_POW,EXP,GSYM REAL_OF_NUM_MUL ] THEN
  REWRITE_TAC[REAL_INV_MUL] THEN
  RW_TAC arith_ss [not2eqz,v23not0, GSYM REAL_OF_NUM_POW,REAL_INV_MUL,real_div] THEN
  ONCE_REWRITE_TAC[REAL_ARITH (--`(a:real) * (b * c) = (a * b) * c`--)] THEN
  RW_TAC arith_ss [not2eqz,REAL_MUL_RINV,REAL_MUL_LID ]);

(*---------------------------*)

val ttpinv = store_thm (
  "ttpinv" ,
  (--`(&2:real) * (&2:real) pow 127 * inv ((&2:real) pow 127) = (&2:real)`--),
  ONCE_REWRITE_TAC[REAL_ARITH (--`(a:real) * b * c = a * (b * c)`--)] THEN
  RW_TAC arith_ss [REAL_DIV_REFL,REAL_MUL_RINV,v23not0,v127not0,REAL_MUL_RID ]);

(*--------------------------------------*)

val REAL_ARITH_ss = realSimps.REAL_ARITH_ss
val rlemma1 = prove(
  ``2 <= x /\ 2 <= y ==> x <= y * (x - 1r)``,
  STRIP_TAC THEN
  `x <= 2 * (x - 1)` by ASM_SIMP_TAC (std_ss ++ REAL_ARITH_ss) [] THEN
  `2 * (x - 1) <= y * (x - 1)`
     by ASM_SIMP_TAC (std_ss ++ REAL_ARITH_ss) [REAL_LE_RMUL_IMP] THEN
  ASM_SIMP_TAC (std_ss ++ REAL_ARITH_ss) []);

val RRRC1 = store_thm (
  "RRRC1",
  ``2 * 8388608 <= 2 pow 254 * (2 * 8388608 - 1)``,
  MATCH_MP_TAC rlemma1 THEN CONJ_TAC THENL [
    SRW_TAC [][],
    Q_TAC SUFF_TAC `2 pow 1 < 2 pow 254`
          THEN1 SIMP_TAC bool_ss [POW_1, REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_MONO_LT THEN SRW_TAC [][]
  ]);

(*-----------------------------------------------*)

val RRRC2 = store_thm (
  "RRRC2",
  (--`2 pow 103 * (2 pow 24 * 2) - 2 pow 103 <= 2 pow 128`--),
  REWRITE_TAC[REAL_ARITH (--`(a:real * b - c <= d = a * b <= c + d)`--)] THEN
  REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_MUL, REAL_OF_NUM_ADD, REAL_OF_NUM_LE] THEN
  RW_TAC arith_ss []);

(*-----------------------------------------------*)

val RRRC3 = store_thm (
  "RRRC3",
  (--`340282356779733661637539395458142568448 <= 2 pow 128` --),
  REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_LE] THEN
  RW_TAC arith_ss []);

(*-----------------------------------------------*)

val RRRC4 = store_thm (
  "RRRC4",
  (--`2 pow 128 - 2 pow 103 = 340282356779733661637539395458142568448`--),
  REWRITE_TAC[REAL_ARITH (--`((a:real - b = c) = (a = b + c))`--)] THEN
  REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_ADD, REAL_OF_NUM_EQ] THEN
  RW_TAC arith_ss []);

(*-----------------------------------------------*)

val RRRC5 = store_thm (
  "RRRC5",
  (--`inv 1 < 2 pow 103 * (2 pow 24 * 2) - 2 pow 103`--),
  RW_TAC arith_ss [REAL_MUL_SYM ,GSYM pow,ADD1,GSYM REAL_POW_ADD] THEN
  REWRITE_TAC[REAL_ARITH (--`((a:real < b - c) = (a + c < b))`--)] THEN
  REWRITE_TAC [REAL_INV1, REAL_OF_NUM_POW, REAL_OF_NUM_ADD, REAL_OF_NUM_LT] THEN
  RW_TAC arith_ss []);

(* ------------------------------------------------------------------------- *)

val RRRC6 = store_thm (
  "RRRC6",
  (--`0 < 2 pow 150`--),
  REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_LT] THEN
  RW_TAC arith_ss []);

(* ------------------------------------------------------------------------- *)

val RRRC7 = store_thm (
  "RRRC7",
  (--`2 pow 254 - 2 pow 229 < 2 pow 254`--),
  REWRITE_TAC[REAL_ARITH (--`((a:real - b < c) = (a < b + c))`--)] THEN
  REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_ADD, REAL_OF_NUM_LT] THEN
  RW_TAC arith_ss []);

(* ------------------------------------------------------------------------- *)

val RRRC8 = store_thm (
  "RRRC8",
  (--`2 pow 103 * (2 pow 24 * 2) - 2 pow 103 = 340282356779733661637539395458142568448`--),
  REWRITE_TAC[REAL_ARITH (--`((a:real - b = c) = (a = b + c))`--)] THEN
  REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_ADD, REAL_OF_NUM_MUL, REAL_OF_NUM_EQ] THEN
  RW_TAC arith_ss []);

(* ------------------------------------------------------------------------- *)

val RRRC9 = store_thm (
  "RRRC9",
  (--`2 pow 127 * 2 - 2 pow 104 < 340282356779733661637539395458142568448`--),
  REWRITE_TAC[REAL_ARITH (--`((a:real - b < c) = (a < b + c))`--)] THEN
  REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_ADD, REAL_OF_NUM_MUL, REAL_OF_NUM_LT] THEN
  RW_TAC arith_ss []);

(* ------------------------------------------------------------------------- *)

val RRRC10 = store_thm ("RRRC10", (--`1 < 2 pow 254 - 2 pow 229`--),

REWRITE_TAC[REAL_ARITH (--`((a:real < b - c) = (a + c < b))`--)] THEN
REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_ADD, REAL_OF_NUM_LT] THEN
RW_TAC arith_ss []);

(* ------------------------------------------------------------------------- *)

val RRRC11 = store_thm (
  "RRRC11",
  (--`340282356779733661637539395458142568448 * 2 pow 126 < 2 pow 254`--),
  REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_MUL, REAL_OF_NUM_LT] THEN
  RW_TAC arith_ss []);

(* ------------------------------------------------------------------------- *)

val sucminmullt = store_thm (
  "sucminmullt",
  (--`(&2:real pow SUC 127 - &2:real pow 103) * &2 pow 126 < &2 pow 255`--),
  REWRITE_TAC[REAL_SUB_RDISTRIB] THEN REWRITE_TAC[GSYM POW_ADD] THEN
  RW_TAC arith_ss [] THEN REWRITE_TAC[REAL_ARITH (--`((a:real - b < c) = (a < b + c))`--)] THEN
  REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_ADD, REAL_OF_NUM_LT] THEN RW_TAC arith_ss []);

(* ------------------------------------------------------------------------- *)
(* Useful lemmas.                                                            *)
(* ------------------------------------------------------------------------- *)

val SIGN = store_thm (
  "SIGN",
  (--`!(a:num#num#num). sign(a) = FST a`--),
  GEN_TAC THEN SUBST1_TAC(SYM(REWRITE_CONV[PAIR]
  (--`FST(a):num,FST(SND(a)):num,SND(SND(a)):num`--))) THEN
  PURE_REWRITE_TAC[sign] THEN REWRITE_TAC[FST]);

(*-------------------------------------------------------*)

val EXPONENT = store_thm (
  "EXPONENT",
  (--`!(a:num#num#num). exponent(a) = FST(SND a)`--),
  GEN_TAC THEN SUBST1_TAC(SYM(REWRITE_CONV[PAIR]
  (--`FST(a):num,FST(SND(a)):num,SND(SND(a)):num`--))) THEN
  PURE_REWRITE_TAC[exponent] THEN REWRITE_TAC[FST,SND]);

(*-------------------------------------------------------*)

val FRACTION = store_thm (
  "FRACTION",
  (--`!(a:num#num#num). fraction(a) = SND(SND a)`--),
  GEN_TAC THEN SUBST1_TAC(SYM(REWRITE_CONV[PAIR]
  (--`FST(a):num,FST(SND(a)):num,SND(SND(a)):num`--))) THEN
  PURE_REWRITE_TAC[fraction] THEN REWRITE_TAC[FST,SND]);

(*-------------------------------------------------------*)

val IS_VALID = store_thm (
  "IS_VALID",
  (--`!(X:num#num) (a:num#num#num). is_valid(X) a =
      (sign a < (2:num)) /\ (exponent a < (2:num) EXP (expwidth X)) /\
      (fraction a < (2:num) EXP (fracwidth X))`--),
  REPEAT GEN_TAC THEN SUBST1_TAC(SYM(REWRITE_CONV[PAIR]
  (--`FST(a):num,FST(SND(a)):num,SND(SND(a)):num`--))) THEN
  PURE_REWRITE_TAC[is_valid, sign, exponent, fraction] THEN
  RW_TAC arith_ss []);

(*-------------------------------------------------------*)

val VALOF = store_thm (
  "VALOF",
  (--`!(X:num#num) (a:num#num#num). valof (X:num#num) (a:num#num#num) =
      if exponent(a) = 0 then ~(&1) pow sign(a) * (&2 / &2 pow bias(X)) *
      ((&(fraction(a))) / &2 pow fracwidth(X)) else ~(&1) pow sign(a) *
      (&2 pow exponent(a) / (&2 pow bias(X))) *
      (&1 + &(fraction(a)) / &2 pow fracwidth(X))`--),
  REPEAT GEN_TAC THEN SUBST1_TAC(SYM(REWRITE_CONV[PAIR]
  (--`FST(a):num,FST(SND(a)):num,SND(SND(a)):num`--))) THEN
  PURE_REWRITE_TAC[valof, sign, exponent, fraction] THEN
  RW_TAC arith_ss []);

(*-------------------------------------------------------*)

val IS_VALID_DEFLOAT = store_thm (
  "IS_VALID_DEFLOAT",
  (--`!(a:float). is_valid(float_format) (defloat a)`--),
  REWRITE_TAC[float_tybij]);

(*-----------------------*)

val ADD_SUB2 = store_thm (
  "ADD_SUB2",
  (--`!(m:num) (n:num). (m + n) - m = n`--),
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  MATCH_ACCEPT_TAC ADD_SUB);

(*-----------------------*)

val REAL_OF_NUM_SUB = store_thm (
  "REAL_OF_NUM_SUB",
  (--`!(m:num) (n:num). m <= n ==> (&n - &m = &(n - m))`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[LESS_EQ_EXISTS] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ADD_SUB2] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[real_sub, GSYM REAL_ADD_ASSOC] THEN
  MESON_TAC[REAL_ADD_LINV, REAL_ADD_SYM, REAL_ADD_LID]);

(*-----------------------*)

val IS_FINITE_ALT1 = store_thm (
  "IS_FINITE_ALT1",
  (--`!(a:num#num#num).(is_normal float_format a \/ is_denormal float_format a \/ is_zero float_format a) = exponent a < 255`--),
  REPEAT GEN_TAC THEN Cases_on `a` THEN Cases_on `r` THEN
  REWRITE_TAC[is_normal, is_denormal, is_zero,exponent,emax,float_format,fraction,expwidth] THEN
  REWRITE_TAC[TAUT (`((a /\ ~ b)\/(a /\ b))= a`)] THEN Cases_on `q' = 0` THENL [
  RW_TAC arith_ss [], RW_TAC arith_ss [] THEN RW_TAC arith_ss [GSYM REAL_OF_NUM_LT] THEN
  RW_TAC arith_ss [GSYM REAL_OF_NUM_POW,GSYM REAL_OF_NUM_SUB,TWO_EXP_GE_1] THEN
  REWRITE_TAC [tpetfs] THEN REAL_ARITH_TAC ] );

(*-----------------------*)

val IS_FINITE_ALT = store_thm (
  "IS_FINITE_ALT",
  (--`!(a:num#num#num). is_finite(float_format) a = ((is_valid(float_format) a) /\ (exponent(a) < (255:num)))`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[is_finite] THEN RW_TAC arith_ss [IS_FINITE_ALT1]);

(*-----------------------*)

val IS_FINITE_EXPLICIT = store_thm (
  "IS_FINITE_EXPLICIT",
  (--`!(a:num#num#num). is_finite(float_format) a = sign(a) < (2:num) /\ exponent(a) < 255 /\ fraction(a) < (8388608:num)`--),
  GEN_TAC THEN REWRITE_TAC[IS_FINITE_ALT, IS_VALID] THEN REWRITE_TAC[expwidth, fracwidth, float_format] THEN
  RW_TAC arith_ss []);

(*-----------------------*)

val LT_SUC_LE = store_thm (
  "LT_SUC_LE",
  (--`!m n. (m < SUC n) = (m <= n)`--),
  RW_TAC arith_ss []);

(*-----------------------*)

val FLOAT_CASES = store_thm (
  "FLOAT_CASES",
  ``!(a:float). Isnan(a) \/ Infinity(a) \/ Isnormal(a) \/ Isdenormal(a) \/
                Iszero(a)``,
  GEN_TAC THEN REWRITE_TAC[Isnan, Infinity, Isnormal, Isdenormal, Iszero] THEN
  REWRITE_TAC[is_nan, is_infinity, is_normal, is_denormal, is_zero] THEN
  MP_TAC(SPEC (--`a:float`--) IS_VALID_DEFLOAT) THEN REWRITE_TAC[IS_VALID] THEN
  REWRITE_TAC [emax] THEN
  SUBGOAL_THEN ``!n p. n < 2 EXP p = n < (2 EXP p - 1) \/ (n = 2 EXP p - 1)``
               (fn th => REWRITE_TAC [th])
  THENL [
    REPEAT GEN_TAC THEN Q_TAC SUFF_TAC `0n < 2 ** p` THEN1 DECIDE_TAC THEN
    SRW_TAC [][],
    STRIP_TAC THEN ASM_REWRITE_TAC [] THENL [
      ASM_CASES_TAC (--`fraction (defloat a) = 0`--) THEN
      ASM_REWRITE_TAC [] THEN DISJ2_TAC THEN RW_TAC arith_ss [],
      DISJ2_TAC THEN DISJ2_TAC THEN
      ASM_CASES_TAC (--`2 EXP fracwidth(float_format) - 1 = 0`--) THEN
      RW_TAC arith_ss [],
      ASM_CASES_TAC (--`fraction (defloat a) = 0`--) THEN
      RW_TAC arith_ss [],
      ASM_CASES_TAC (--`2 EXP fracwidth(float_format) - 1 = 0`--) THEN
      RW_TAC arith_ss []
    ]
  ]);

(*-----------------------*)

val FLOAT_CASES_FINITE = store_thm (
  "FLOAT_CASES_FINITE",
  (--`!a. Isnan(a) \/ Infinity(a) \/ Finite(a)`--),
  MESON_TAC[FLOAT_CASES, Finite]);

(*-----------------------*)

val FLOAT_DISTINCT = store_thm (
  "FLOAT_DISTINCT",
  (--`!(a:float). ~(Isnan(a) /\ Infinity(a)) /\
      ~(Isnan(a) /\ Isnormal(a)) /\
      ~(Isnan(a) /\ Isdenormal(a)) /\
      ~(Isnan(a) /\ Iszero(a)) /\
      ~(Infinity(a) /\ Isnormal(a)) /\
      ~(Infinity(a) /\ Isdenormal(a)) /\
      ~(Infinity(a) /\ Iszero(a)) /\
      ~(Isnormal(a) /\ Isdenormal(a)) /\
      ~(Isnormal(a) /\ Iszero(a)) /\
      ~(Isdenormal(a) /\ Iszero(a))`--),
  GEN_TAC THEN REWRITE_TAC[Isnan, Infinity, Isnormal, Isdenormal, Iszero] THEN
  REWRITE_TAC[float_format] THEN
  REWRITE_TAC[is_nan, is_infinity, is_normal, is_denormal, is_zero] THEN
  REWRITE_TAC[emax, expwidth] THEN Cases_on `(defloat a)` THEN
  Cases_on `r` THEN REWRITE_TAC[exponent,fraction] THEN Cases_on `q' = (0:num)` THEN
  RW_TAC arith_ss [temonz]);

(*-----------------------*)

val FLOAT_DISTINCT_FINITE = store_thm (
  "FLOAT_DISTINCT_FINITE",
  (--`!(a:float). ~(Isnan(a) /\ Infinity(a)) /\
      ~(Isnan(a) /\ Finite(a)) /\
      ~(Infinity(a) /\ Finite(a))`--),
  MESON_TAC[FLOAT_DISTINCT, Finite]);

(*-----------------------*)

val FLOAT_INFINITIES_SIGNED = store_thm (
  "FLOAT_INFINITIES_SIGNED",
  (--`(sign (defloat Plus_infinity) = 0) /\ (sign (defloat Minus_infinity) = 1)`--),
  REWRITE_TAC[Plus_infinity, Minus_infinity] THEN
  SUBGOAL_THEN (--`(defloat(float(plus_infinity float_format)) =
  plus_infinity float_format) /\ (defloat(float(minus_infinity float_format)) =
  minus_infinity float_format)`--) (fn th => REWRITE_TAC[th]) THENL [
    REWRITE_TAC[GSYM float_tybij] THEN
    REWRITE_TAC[is_valid, plus_infinity, minus_infinity, float_format] THEN
    REWRITE_TAC[emax, fracwidth, expwidth] THEN RW_TAC arith_ss [],
    REWRITE_TAC[sign, plus_infinity, minus_infinity]]);

(*-----------------------*)

val INFINITY_IS_INFINITY = store_thm (
  "INFINITY_IS_INFINITY",
  (--`Infinity(Plus_infinity) /\ Infinity(Minus_infinity)`--),
  REWRITE_TAC[Infinity, Plus_infinity, Minus_infinity] THEN
  SUBGOAL_THEN (--`(defloat(float(plus_infinity float_format)) =
  plus_infinity float_format) /\ (defloat(float(minus_infinity float_format)) =
  minus_infinity float_format)`--) (fn th => REWRITE_TAC[th]) THENL [
    REWRITE_TAC[GSYM float_tybij] THEN
    REWRITE_TAC[is_valid, plus_infinity, minus_infinity, float_format] THEN
    REWRITE_TAC[emax, fracwidth, expwidth] THEN RW_TAC arith_ss [],
    REWRITE_TAC[is_infinity, plus_infinity, minus_infinity] THEN
    REWRITE_TAC[exponent, fraction]]);

(*-----------------------*)

val ZERO_IS_ZERO = store_thm (
  "ZERO_IS_ZERO",
  (--`Iszero(Plus_zero) /\ Iszero(Minus_zero)`--),
  REWRITE_TAC[Iszero, Plus_zero, Minus_zero] THEN
  SUBGOAL_THEN (--`(defloat(float(plus_zero float_format)) =
  plus_zero float_format) /\ (defloat(float(minus_zero float_format)) =
  minus_zero float_format)`--) (fn th => REWRITE_TAC[th]) THENL [
    REWRITE_TAC[GSYM float_tybij] THEN
    REWRITE_TAC[is_valid, plus_zero, minus_zero, float_format] THEN
    REWRITE_TAC[emax, fracwidth, expwidth] THEN RW_TAC arith_ss [],
    REWRITE_TAC[is_zero, plus_zero, minus_zero] THEN
    REWRITE_TAC[exponent, fraction]]);

(*-----------------------*)

val INFINITY_NOT_NAN = store_thm (
  "INFINITY_NOT_NAN",
  (--`~(Isnan(Plus_infinity)) /\ ~(Isnan(Minus_infinity))`--),
  MESON_TAC[INFINITY_IS_INFINITY, FLOAT_DISTINCT_FINITE]);

(*-----------------------*)

val ZERO_NOT_NAN = store_thm (
  "ZERO_NOT_NAN",
  (--`~(Isnan(Plus_zero)) /\ ~(Isnan(Minus_zero))`--),
  MESON_TAC[ZERO_IS_ZERO, FLOAT_DISTINCT]);;

(*-----------------------*)

val FLOAT_INFINITIES = store_thm (
  "FLOAT_INFINITIES",
  (--`!(a:float). Infinity(a) = (( a == Plus_infinity) \/ (a == Minus_infinity))`--),
  GEN_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (SPEC (--`a:float`--) FLOAT_CASES_FINITE) THENL [
    SUBGOAL_THEN (--`~(Infinity(a))`--) MP_TAC THENL [
      ASM_MESON_TAC[FLOAT_DISTINCT_FINITE], UNDISCH_TAC (--`Isnan(a)`--) THEN
      REWRITE_TAC[Isnan, Infinity] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[fcompare, feq, float_eq] THEN RW_TAC arith_ss []],
    RW_TAC arith_ss [] THEN SUBGOAL_THEN (--`~(Isnan(a))`--) MP_TAC THENL [
      ASM_MESON_TAC[FLOAT_DISTINCT_FINITE], UNDISCH_TAC (--`Infinity(a)`--) THEN
      REWRITE_TAC[Isnan, Infinity] THEN STRIP_TAC THEN ASM_REWRITE_TAC [fcompare, feq, float_eq] THEN
      REWRITE_TAC[REWRITE_RULE[Isnan] INFINITY_NOT_NAN] THEN REWRITE_TAC[REWRITE_RULE[Infinity] INFINITY_IS_INFINITY] THEN
      REWRITE_TAC[FLOAT_INFINITIES_SIGNED] THEN RW_TAC arith_ss [] THEN REPEAT (COND_CASES_TAC THEN REWRITE_TAC[]) THEN
      MP_TAC(SPEC (--`a:float`--) IS_VALID_DEFLOAT) THEN REWRITE_TAC[IS_VALID] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      REWRITE_TAC[num_CONV (--`2:num`--), num_CONV (--`1:num`--), LT_SUC_LE, LE] THEN ASM_REWRITE_TAC[SYM(num_CONV (--`1:num`--))]],
    SUBGOAL_THEN (--`~(Infinity(a)) /\ ~(Isnan(a))`--) MP_TAC THENL [
      ASM_MESON_TAC[FLOAT_DISTINCT_FINITE], REWRITE_TAC[Infinity, Isnan] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[fcompare, float_eq, feq] THEN REWRITE_TAC[REWRITE_RULE[Isnan] INFINITY_NOT_NAN] THEN
      REWRITE_TAC[REWRITE_RULE[Infinity] INFINITY_IS_INFINITY] THEN REWRITE_TAC[FLOAT_INFINITIES_SIGNED] THEN
      RW_TAC arith_ss []]]);

(*-----------------------*)

val FLOAT_INFINITES_DISTINCT = store_thm (
  "FLOAT_INFINITES_DISTINCT",
  (--`!(a:float). ~(a == Plus_infinity /\ a == Minus_infinity)`--),
  let val lemma = prove ((--`((if b then x else y) = z) = if b then x = z else y = z`--),
  BOOL_CASES_TAC (--`b:bool`--) THEN REWRITE_TAC[]) in
  GEN_TAC THEN REWRITE_TAC[Plus_infinity, Minus_infinity] THEN
  REWRITE_TAC[feq, float_eq, fcompare] THEN REWRITE_TAC[lemma] THEN
  RW_TAC arith_ss [] THEN REWRITE_TAC[REWRITE_RULE[Plus_infinity, Minus_infinity]
  FLOAT_INFINITIES_SIGNED] THEN RW_TAC arith_ss [] THEN REWRITE_TAC[lemma] THEN
  RW_TAC arith_ss [] THEN REWRITE_TAC[REWRITE_RULE[Isnan, Plus_infinity, Minus_infinity]
  INFINITY_NOT_NAN] THEN REWRITE_TAC[REWRITE_RULE[Plus_infinity, Minus_infinity]
  FLOAT_INFINITIES_SIGNED] THEN RW_TAC arith_ss [] THEN REWRITE_TAC[lemma] THEN
  RW_TAC arith_ss [] THEN REWRITE_TAC[REWRITE_RULE[Isnan, Plus_infinity, Minus_infinity]
  INFINITY_NOT_NAN] THEN REWRITE_TAC[REWRITE_RULE[Plus_infinity, Minus_infinity]
  FLOAT_INFINITIES_SIGNED] THEN RW_TAC arith_ss [] THEN
  REWRITE_TAC[REWRITE_RULE[Infinity, Plus_infinity, Minus_infinity]
  INFINITY_IS_INFINITY] end);

(* ------------------------------------------------------------------------- *)
(* Lifting of the nonexceptional comparison operations.                      *)
(* ------------------------------------------------------------------------- *)

val FLOAT_LIFT_TAC =
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN (--`~(Isnan(a)) /\ ~(Infinity(a)) /\
  ~(Isnan(b)) /\ ~(Infinity(b))`--) MP_TAC THENL [
    ASM_MESON_TAC[FLOAT_DISTINCT_FINITE],
    REWRITE_TAC[Finite, Isnan, Infinity, Isnormal, Isdenormal, Iszero] THEN
    STRIP_TAC];

val FLOAT_LT = store_thm (
  "FLOAT_LT",
  (--`!a b. Finite(a) /\ Finite(b) ==> (a < b = Val(a) < Val(b))`--),
  FLOAT_LIFT_TAC THEN ASM_REWRITE_TAC[float_lt, flt, fcompare, Val] THEN
  REPEAT COND_CASES_TAC THEN RW_TAC arith_ss []);

val FLOAT_GT = store_thm (
  "FLOAT_GT",
  (--`!a b. Finite(a) /\ Finite(b) ==> (a > b = Val(a) > Val(b))`--),
  FLOAT_LIFT_TAC THEN ASM_REWRITE_TAC[float_gt, fgt, fcompare, Val] THEN
  REPEAT COND_CASES_TAC THEN RW_TAC arith_ss [] THEN
  ASM_REWRITE_TAC[real_gt, REAL_LT_REFL] THEN ASM_MESON_TAC[REAL_LT_ANTISYM, REAL_LT_TOTAL]);

val FLOAT_LE = store_thm (
  "FLOAT_LE",
  (--`!a b. Finite(a) /\ Finite(b) ==> (a <= b = Val(a) <= Val(b))`--),
  FLOAT_LIFT_TAC THEN ASM_REWRITE_TAC[float_le, fle, fcompare, Val] THEN
  REPEAT COND_CASES_TAC THEN RW_TAC arith_ss [] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN ASM_MESON_TAC[REAL_LT_ANTISYM, REAL_LT_TOTAL]);

val FLOAT_GE = store_thm (
  "FLOAT_GE",
  (--`!a b. Finite(a) /\ Finite(b) ==> (a >= b = Val(a) >= Val(b))`--),
  FLOAT_LIFT_TAC THEN ASM_REWRITE_TAC[float_ge, fge, fcompare, Val] THEN
  REPEAT COND_CASES_TAC THEN RW_TAC arith_ss [] THEN
  REWRITE_TAC[real_ge] THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  ASM_MESON_TAC[REAL_LT_ANTISYM, REAL_LT_TOTAL]);

val FLOAT_EQ = store_thm (
  "FLOAT_EQ",
  (--`!a b. Finite(a) /\ Finite(b) ==> (a == b = (Val(a) = Val(b)))`--),
  FLOAT_LIFT_TAC THEN ASM_REWRITE_TAC[float_eq, feq, fcompare, Val] THEN
  REPEAT COND_CASES_TAC THEN RW_TAC arith_ss [] THEN ASM_MESON_TAC[REAL_LT_REFL]);

val FLOAT_EQ_REFL = store_thm (
  "FLOAT_EQ_REFL",
  (--`!a. (a == a) = ~(Isnan(a))`--),
  GEN_TAC THEN REWRITE_TAC[float_eq, feq, fcompare, Isnan] THEN
  REPEAT(COND_CASES_TAC THEN RW_TAC arith_ss []) THEN
  ASM_MESON_TAC[REAL_LT_REFL]);

(* ------------------------------------------------------------------------- *)
(* Various lemmas.                                                           *)
(* ------------------------------------------------------------------------- *)

val EXP_GT_ZERO = store_thm (
  "EXP_GT_ZERO",
  (--`!(n:num). (0 < 2 EXP n)`--),
  GEN_TAC THEN REWRITE_TAC[num_CONV(--`2:num`--)] THEN
  MP_TAC NOT_EXP_0 THEN DISCH_THEN (MP_TAC o SPEC (--`n:num`--)) THEN
  DISCH_THEN (MP_TAC o SPEC (--`1:num`--)) THEN
  RW_TAC arith_ss [NOT_ZERO_LT_ZERO]);

(*-----------------------*)

val IS_VALID_SPECIAL = store_thm (
  "IS_VALID_SPECIAL",
  (--`!(X:num#num). is_valid(X) (minus_infinity(X)) /\
      is_valid(X) (plus_infinity(X)) /\
      is_valid(X) (topfloat(X)) /\
      is_valid(X) (bottomfloat(X)) /\
      is_valid(X) (plus_zero(X)) /\
      is_valid(X) (minus_zero(X))`--),
  GEN_TAC THEN
  REWRITE_TAC[is_valid, minus_infinity, plus_infinity,
  plus_zero, minus_zero, topfloat, bottomfloat, emax] THEN
  RW_TAC arith_ss [EXP_GT_ZERO]);

(*-----------------------*)

val IS_CLOSEST_EXISTS = store_thm (
  "IS_CLOSEST_EXISTS",
  (--`!(v:(num#num#num)->real) (x:real) (s:(num#num#num)->bool). FINITE(s) ==> ~(s = EMPTY) ==> ?(a:(num#num#num)). is_closest v s x a`--),
  GEN_TAC THEN GEN_TAC THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN REWRITE_TAC[NOT_INSERT_EMPTY] THEN X_GEN_TAC (--`s:(num#num#num)->bool`--) THEN
  ASM_CASES_TAC (--`s:(num#num#num)->bool = EMPTY`--) THENL [
    ASM_REWRITE_TAC[] THEN REWRITE_TAC [FINITE_EMPTY] THEN REWRITE_TAC [NOT_IN_EMPTY] THEN X_GEN_TAC (--`e:(num#num#num) `--) THEN
    EXISTS_TAC (--`e :(num#num#num)`--) THEN REWRITE_TAC [is_closest] THEN REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THENL [
      ASM_REWRITE_TAC [REAL_LE_REFL], PROVE_TAC [NOT_IN_EMPTY]],
    ASM_CASES_TAC (--` FINITE (s: ((num#num#num) -> bool))`--) THENL [
      ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC (--`a:(num#num#num)`--)) THEN X_GEN_TAC (--`e:(num#num#num) `--) THEN
      REPEAT STRIP_TAC THEN
      ASM_CASES_TAC (--`abs (v (a :(num#num#num) ) - (x : real )) <= abs (v (e :(num#num#num) ) - (x : real ))`--) THENL [
        EXISTS_TAC (--`a:(num#num#num)`--) THEN UNDISCH_TAC (--`is_closest v s x (a:(num#num#num))`--) THEN
        REWRITE_TAC [is_closest] THEN REWRITE_TAC [IN_INSERT] THEN REPEAT STRIP_TAC THENL [
          ASM_REWRITE_TAC [], ASM_REWRITE_TAC [REAL_LE_REFL], PROVE_TAC []],
        EXISTS_TAC (--`e:(num#num#num)`--) THEN UNDISCH_TAC(--`is_closest v s x (a:(num#num#num))`--) THEN
        REWRITE_TAC [is_closest] THEN REWRITE_TAC [IN_INSERT] THEN REPEAT STRIP_TAC THENL [
          ASM_REWRITE_TAC [REAL_LE_REFL], PAT_ASSUM (--`!b:(num#num#num) . b IN s ==> abs
          (v a - x) <= abs (v b - x)`--) (MP_TAC o SPEC (--`b:(num#num#num)`--)) THEN ASM_REWRITE_TAC [] THEN
          PAT_ASSUM (--`~(abs (v a - x) <= abs (v e - x))`--) MP_TAC THEN REAL_ARITH_TAC]],
      ASM_REWRITE_TAC []]]);

(*-------------------------------------------------------*)

val CLOSEST_IS_EVERYTHING = store_thm (
  "CLOSEST_IS_EVERYTHING",
  (--`! (v:(num#num#num)->real) (p:(num#num#num)->bool) (s:(num#num#num)->bool) (x:real).
      FINITE(s) ==> ~(s = EMPTY) ==> is_closest v s x (closest v p s x) /\
      ((?(b:(num#num#num)). is_closest v s x b /\ p b) ==> p (closest v p s x))`--),
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REWRITE_TAC [closest] THEN
  CONV_TAC SELECT_CONV THEN ASM_CASES_TAC (--`?(a:(num#num#num)). is_closest v s x a /\ p a`--) THENL [
    POP_ASSUM(X_CHOOSE_TAC (--`a:(num#num#num)`--)) THEN EXISTS_TAC (--`a:(num#num#num)`--) THEN
    ASM_REWRITE_TAC[], FIRST_ASSUM(MP_TAC o MATCH_MP IS_CLOSEST_EXISTS) THEN RW_TAC arith_ss []]);

(*-------------------------------------------------------*)

val CLOSEST_IN_SET = store_thm (
  "CLOSEST_IN_SET",
  (--`! (v:(num#num#num)->real) (p:(num#num#num)->bool) (x : real) (s:(num#num#num)->bool).
      FINITE(s) ==> ~(s = EMPTY) ==> (closest v p s x) IN s`--),
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP (CLOSEST_IS_EVERYTHING)) THEN
  ASM_MESON_TAC[is_closest]);

(*-------------------------------------------------------*)

val CLOSEST_IS_CLOSEST = store_thm (
  "CLOSEST_IS_CLOSEST",
  (--`! (v:(num#num#num) ->real) (p:(num#num#num) -> bool) (x : real) (s : (num#num#num) -> bool).
      FINITE(s) ==> ~(s = EMPTY) ==> is_closest v s x (closest v p s x)`--),
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP CLOSEST_IS_EVERYTHING) THEN
  ASM_MESON_TAC[is_closest]);

(*-------------------------------------------------------*)

val FLOAT_FIRSTCROSS1 = store_thm (
  "FLOAT_FIRSTCROSS1",
  (--`! (x:num # num # num) (m:num) (n:num) (p:num) . (?x'.
      (x = (\ (x,y,z). (x,y,z)) x') /\ FST x' < m /\ FST (SND x') < n /\
       SND (SND x') < p) ==>
    FST x < m /\ FST (SND x) < n /\ SND (SND x) < p`--),
      REPEAT GEN_TAC THEN REPEAT STRIP_TAC THENL [Cases_on `x` THEN Cases_on `r` THEN Cases_on `x'` THEN Cases_on `r` THEN
      UNDISCH_TAC (--`((q :num),(q' :num),(r' :num)) = (\ ((x :num),(y :num),(z :num)). (x,y,z))
      ((q'' :num),(q''' :num),(r'' :num))`--) THEN UNDISCH_TAC (--`FST ((q'' :num),(q''' :num),(r'' :num)) < (m :num)`--) THEN
      RW_TAC arith_ss [], Cases_on `x` THEN Cases_on `r` THEN Cases_on `x'` THEN Cases_on `r` THEN
      UNDISCH_TAC (--`((q :num),(q' :num),(r' :num)) = (\ ((x :num),(y :num),(z :num)). (x,y,z)) ((q'' :num),(q''' :num),(r'' :num))`--) THEN
      UNDISCH_TAC (--`FST (SND ((q'' :num),(q''' :num),(r'' :num))) < (n :num)`--) THEN RW_TAC arith_ss [],
      Cases_on `x` THEN Cases_on `r` THEN Cases_on `x'` THEN Cases_on `r` THEN
      UNDISCH_TAC (--`((q :num),(q' :num),(r' :num)) = (\ ((x :num),(y :num),(z :num)). (x,y,z)) ((q'' :num),(q''' :num),(r'' :num))`--) THEN
      UNDISCH_TAC (--`SND (SND ((q'' :num),(q''' :num),(r'' :num))) < (p :num)`--) THEN RW_TAC arith_ss []]);

(*-------------------------------------------------------*)

val FLOAT_FIRSTCROSS2 = store_thm (
  "FLOAT_FIRSTCROSS2",
  (--`! (x:num # num # num) (m:num) (n:num) (p:num) . (FST x < m /\ FST (SND x) < n /\ SND (SND x) < p) ==>
    (? (x':num # num # num). ((x:num # num # num) = ( \ ((x:num),(y:num),(z:num)). ((x:num),(y:num),(z:num))) x') /\ FST x' < m /\ FST (SND x') < n /\ SND (SND x') < p)`--),

 REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN EXISTS_TAC (--`((FST (x:(num # num # num)) ), (FST (SND (x:(num # num # num)))) , SND(SND (x:(num # num # num))))`--) THEN
 CONJ_TAC THENL [Cases_on `x` THEN Cases_on `r` THEN RW_TAC arith_ss [], RW_TAC arith_ss []]);

(*-------------------------------------------------------*)

val FLOAT_FIRSTCROSS3 = store_thm (
  "FLOAT_FIRSTCROSS3",
  ( --` ! (x:num # num # num) (m:num) (n:num) (p:num) . FST x < m /\ FST (SND x) < n /\ SND (SND x) < p =
    ?x'. ((x:num # num # num) = ( \ ((x:num),(y:num),(z:num)). ((x:num),(y:num),(z:num))) x') /\ FST x' < m /\ FST (SND x') < n /\ SND (SND x') < p`--),

REPEAT GEN_TAC THEN
EQ_TAC THENL [MP_TAC(SPECL [(--`(x:num # num # num)`--), (--`(m:num)`--), (--`(n:num)`--), (--`(p:num)`--)] FLOAT_FIRSTCROSS2) THEN RW_TAC arith_ss []
    , MP_TAC(SPECL [(--`(x:num # num # num)`--), (--`(m:num)`--), (--`(n:num)`--), (--`(p:num)`--)] FLOAT_FIRSTCROSS1) THEN RW_TAC arith_ss []]);

(*-------------------------------------------------------*)

val FLOAT_FIRSTCROSS = store_thm (
  "FLOAT_FIRSTCROSS",
  (--`! (m:num) (n:num) (p:num). {(a: (num # num # num))| (FST (a) < m) /\ (FST(SND a) < n) /\ (SND (SND a) < p)} =
      IMAGE ( \ ((x: num), (y: num, z: num)). (x,y,z)) ({(x:num)| x < m} CROSS ({(y:num)| y < n} CROSS {(z:num) | z < p}))`--),

  REPEAT GEN_TAC THEN REWRITE_TAC [GSPECIFICATION,CROSS_DEF, IMAGE_DEF] THEN PURE_REWRITE_TAC [EXTENSION] THEN
  RW_TAC arith_ss [GSPECIFICATION] THEN
  MP_TAC(SPECL [(--`(x:num # num # num)`--), (--`(m:num)`--), (--`(n:num)`--), (--`(p:num)`--)] FLOAT_FIRSTCROSS3) THEN
  RW_TAC arith_ss []);

(*-------------------------------------------------------*)

val FLOAT_COUNTINDUCT = store_thm (
  "FLOAT_COUNTINDUCT",
  (--`! n:num. ({x:num | x < 0} = EMPTY) /\ ({x | x < SUC n} = n INSERT {x | x < n})`--),
  REPEAT GEN_TAC THEN PURE_REWRITE_TAC [EXTENSION,IN_INSERT] THEN
  RW_TAC arith_ss [GSPECIFICATION,LESS_THM,NOT_IN_EMPTY]);

(*-------------------------------------------------------*)

val FLOAT_FINITECOUNT = store_thm (
  "FLOAT_FINITECOUNT",
  (--`! n:num. FINITE {x:num | x < n}`--),
  INDUCT_TAC THENL [
    RW_TAC arith_ss [FLOAT_COUNTINDUCT,FINITE_EMPTY],RW_TAC arith_ss [FLOAT_COUNTINDUCT,FINITE_INSERT]]);

(*-------------------------------------------------------*)

val FINITE_R3 = store_thm (
  "FINITE_R3",
  (--`! m:num n:num p:num . FINITE {a: (num # num # num) | FST (a) < m /\ FST (SND a) < n /\ SND (SND a) < p }`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [FLOAT_FIRSTCROSS,FLOAT_FINITECOUNT,IMAGE_FINITE,FINITE_CROSS]);

(*-------------------------------------------------------*)

val REAL_OF_NUM_POW = store_thm (
  "REAL_OF_NUM_POW",
  (--`!(x:num) (n:num). (&x) pow n = &(x EXP n)`--),
  GEN_TAC THEN INDUCT_TAC THENL [
    ASM_REWRITE_TAC[pow, EXP, REAL_OF_NUM_MUL],
    ASM_REWRITE_TAC[pow, EXP, REAL_OF_NUM_MUL]]);

(*-----------------------*)

val IS_VALID_FINITE = store_thm (
  "IS_VALID_FINITE",
  (--`FINITE {(a:num#num#num) | is_valid(X:num#num) a}`--),
    REPEAT GEN_TAC THEN REWRITE_TAC[IS_VALID, SIGN, EXPONENT, FRACTION, FINITE_R3]) ;

(*-----------------------*)

val FLOAT_IS_FINITE_SUBSET = store_thm (
  "FLOAT_IS_FINITE_SUBSET",
  (--`! (X:num#num). {(a:num#num#num) | is_finite (X) a} SUBSET {a | is_valid (X) a}`--),
  GEN_TAC THEN REWRITE_TAC [is_finite] THEN REWRITE_TAC [SUBSET_DEF] THEN
  RW_TAC arith_ss [GSPECIFICATION]);

(*-----------------------*)

val MATCH_FLOAT_FINITE = store_thm (
  "MATCH_FLOAT_FINITE",
  (--`! (X:num#num). ({(a:num#num#num) | is_finite (X) a} SUBSET {a | is_valid (X) a}) ==> FINITE {(a:num#num#num) | is_finite (X) a}`--),
  GEN_TAC THEN MATCH_MP_TAC SUBSET_FINITE THEN REWRITE_TAC [IS_VALID_FINITE]);

(*-----------------------*)

val IS_FINITE_FINITE = store_thm (
  "IS_FINITE_FINITE",
  (--`! (X:num#num). (FINITE {(a:num#num#num) | is_finite (X) a})`--),
  REPEAT GEN_TAC THEN MATCH_MP_TAC MATCH_FLOAT_FINITE THEN
  REWRITE_TAC [FLOAT_IS_FINITE_SUBSET]);

(*-----------------------*)

val IS_VALID_NONEMPTY = store_thm (
  "IS_VALID_NONEMPTY",
  (--`~ ({(a:num#num#num)|is_valid (X:num#num) a} = EMPTY)`--),
  REWRITE_TAC[EXTENSION, NOT_FORALL_THM] THEN
  EXISTS_TAC (--`0:num,0:num,0:num`-- ) THEN
  REWRITE_TAC[NOT_IN_EMPTY] THEN
  REWRITE_TAC [GSPECIFICATION] THEN
  REWRITE_TAC[is_valid] THEN
  EXISTS_TAC (--`0:num,0:num,0:num`-- ) THEN
  REWRITE_TAC[is_valid, is_finite, is_zero, exponent, fraction] THEN
  RW_TAC arith_ss [] THEN REWRITE_TAC[num_CONV(--`2:num`--)] THEN
  REWRITE_TAC[ZERO_LESS_EXP] THEN REWRITE_TAC[num_CONV(--`2:num`--)] THEN
  REWRITE_TAC[ZERO_LESS_EXP]);

(*-----------------------*)

val IS_FINITE_NONEMPTY = store_thm (
  "IS_FINITE_NONEMPTY",
  (--`~ ({(a:num#num#num)| is_finite (X:num#num) a} = EMPTY)`--),
  REWRITE_TAC[EXTENSION, NOT_FORALL_THM] THEN
  EXISTS_TAC (--`0:num,0:num,0:num`--) THEN
  REWRITE_TAC[NOT_IN_EMPTY] THEN REWRITE_TAC [GSPECIFICATION] THEN
  EXISTS_TAC (--`0:num,0:num,0:num`-- ) THEN
  REWRITE_TAC[is_valid, is_finite, is_zero, exponent, fraction] THEN
  RW_TAC arith_ss [] THEN REWRITE_TAC[num_CONV(--`2:num`--)] THEN
  REWRITE_TAC[ZERO_LESS_EXP] THEN REWRITE_TAC[num_CONV(--`2:num`--)] THEN
  REWRITE_TAC[ZERO_LESS_EXP]);

(*-----------------------*)

val IS_FINITE_CLOSEST = store_thm (
  "IS_FINITE_CLOSEST",
  (--`! (X:num#num) (v:(num#num#num) ->real) (p:(num#num#num) -> bool) (x : real). is_finite(X)
      (closest v p {a | is_finite(X) a} x)`--),
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN (--`(closest v p {a | is_finite(X) a} x) IN {a | is_finite(X) a}`--) MP_TAC THENL [
    MATCH_MP_TAC (REWRITE_RULE[TAUT (`a ==> b ==> c = a /\ b ==> c`)] CLOSEST_IN_SET) THEN
    CONJ_TAC THENL [
      REWRITE_TAC [IS_FINITE_FINITE], RW_TAC arith_ss [EXTENSION,NOT_FORALL_THM] THEN
      EXISTS_TAC (--`((0:num),(0:num),(0:num))`--) THEN REWRITE_TAC [NOT_IN_EMPTY] THEN
      REWRITE_TAC [GSPECIFICATION] THEN EXISTS_TAC (--`((0:num),(0:num),(0:num))`--) THEN
      Cases_on `X` THEN RW_TAC arith_ss [PAIR_EQ] THEN
      RW_TAC arith_ss [is_finite,is_valid,expwidth,fracwidth,is_zero,exponent,fraction,EXP_GT_ZERO]],
    REWRITE_TAC [GSPECIFICATION] THEN RW_TAC arith_ss [PAIR_EQ]]);

(*-----------------------*)

val IS_VALID_CLOSEST = store_thm (
  "IS_VALID_CLOSEST",
  (--`!(X:num#num) (v:(num#num#num) ->real) (p:(num#num#num) -> bool) (x : real). is_valid (X) (closest v p {a | is_finite(X) a} x)`--),
  REWRITE_TAC [Ho_Rewrite.GEN_REWRITE_RULE I [is_finite] (SPEC_ALL IS_FINITE_CLOSEST)]);

(*-----------------------*)

val IS_VALID_ROUND = store_thm (
  "IS_VALID_ROUND",
  (--`!(X:num#num) (x:real). is_valid(X) (round(X) To_nearest x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[is_valid, round_def] THEN
  REPEAT COND_CASES_TAC THENL [
  ASM_REWRITE_TAC[IS_VALID_SPECIAL], ASM_REWRITE_TAC[IS_VALID_SPECIAL],
  ASM_REWRITE_TAC[IS_VALID_CLOSEST]]);

(*-----------------------*)

val DEFLOAT_FLOAT_ROUND = store_thm (
  "DEFLOAT_FLOAT_ROUND",
  (--`! (X:num#num) (x:real). defloat(float(round(float_format) To_nearest x)) =
      round(float_format) To_nearest x`--),
  REWRITE_TAC[GSYM float_tybij, IS_VALID_ROUND]);

(*-----------------------*)

val DEFLOAT_FLOAT_ZEROSIGN_ROUND = store_thm (
  "DEFLOAT_FLOAT_ZEROSIGN_ROUND",
  (--`! (x:real) (b:num). defloat(float(zerosign(float_format) b
      (round(float_format) To_nearest (x:real)))) =
      zerosign(float_format) b (round(float_format) To_nearest (x:real))`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM float_tybij] THEN
  REWRITE_TAC[zerosign] THEN REPEAT COND_CASES_TAC THENL [
    REWRITE_TAC[IS_VALID_SPECIAL], REWRITE_TAC[IS_VALID_SPECIAL],
    REWRITE_TAC[IS_VALID_SPECIAL] THEN REWRITE_TAC[IS_VALID_ROUND]]);

(*-----------------------*)

val VALOF_DEFLOAT_FLOAT_ZEROSIGN_ROUND = store_thm (
  "VALOF_DEFLOAT_FLOAT_ZEROSIGN_ROUND",
  (--`! (x:real) (b:num). valof(float_format) (defloat(float(zerosign(float_format) b
      (round(float_format) To_nearest x)))) = valof(float_format) (round(float_format) To_nearest x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[DEFLOAT_FLOAT_ZEROSIGN_ROUND] THEN REWRITE_TAC[zerosign] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[minus_zero, plus_zero] THEN
  GEN_REWRITE_TAC LAND_CONV [valof] THEN REWRITE_TAC[real_div, REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
  UNDISCH_TAC (--`is_zero float_format (round float_format To_nearest x)`--) THEN
  SPEC_TAC ((--`round float_format To_nearest x`--),(--`a:num#num#num`--)) THEN GEN_TAC THEN
  SUBST1_TAC(SYM(REWRITE_CONV[PAIR] (--`FST(a):num,FST(SND(a)):num,SND(SND(a)):num`--))) THEN
  PURE_REWRITE_TAC[is_zero, exponent, fraction, valof] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_div, REAL_MUL_LZERO, REAL_MUL_RZERO]);

(*-----------------------*)

val REAL_ABS_NUM = store_thm (
  "REAL_ABS_NUM",
  (--`abs(&n) = &n`--),
  REWRITE_TAC[REAL_POS, abs]);

(*--------------------------------------------------------------*)

val REAL_ABS_POW = store_thm (
  "REAL_ABS_POW",
  (--`!(x:real) (n:num). abs(x pow n) = abs(x) pow n`--),
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[pow, REAL_ABS_NUM, REAL_ABS_MUL] THEN
  ASM_REWRITE_TAC[pow, REAL_ABS_NUM, REAL_ABS_MUL]);

(*--------------------------------------------------------------*)

val ISFINITE = store_thm (
  "ISFINITE",
  (--`!(a:float). Finite(a) = is_finite(float_format) (defloat a)`--),
  REWRITE_TAC[Finite, is_finite, Isnormal, Isdenormal, Iszero] THEN
  GEN_TAC THEN REWRITE_TAC[float_tybij]);

(*--------------------------------------*)

val REAL_ABS_INV = store_thm (
  "REAL_ABS_INV",
  (--`!x. abs(inv x) = inv(abs x)`--),
  GEN_TAC THEN CONV_TAC SYM_CONV THEN ASM_CASES_TAC (--`x = &0`--) THENL [
    ASM_REWRITE_TAC[REAL_INV_0, REAL_ABS_0], RW_TAC arith_ss [ABS_INV]]);

(*--------------------------------------*)

val REAL_ABS_DIV = store_thm (
  "REAL_ABS_DIV",
  (--`!(x:real) y. abs(x / y) = abs(x) / abs(y)`--),
  REWRITE_TAC[real_div, REAL_ABS_INV, REAL_ABS_MUL]);

(*--------------------------------------*)

val REAL_ABS_DIV = store_thm (
  "REAL_ABS_DIV",
  (--`!(x:real) y. abs(x / y) = abs(x) / abs(y)`--),
  REWRITE_TAC[real_div, REAL_ABS_INV, REAL_ABS_MUL]);

(*--------------------------------------*)

val REAL_MUL_AC_4 = (REAL_MUL_ASSOC, REAL_MUL_SYM);

(*--------------------------------------*)

val REAL_POW_LE_1 =  store_thm (
  "REAL_POW_LE_1",
  (--`!(n:num) (x:real). (&1:real) <= x ==> (&1:real) <= x pow n`--),
  INDUCT_TAC THENL [
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[pow, REAL_LE_REFL],
    GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [pow] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_01] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);

(*--------------------------------------*)

val REAL_POW_MONO = store_thm (
  "REAL_POW_MONO",
  (--`!(m:num) n x. &1 <= x /\ m <= n ==> x pow m <= x pow n`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[LESS_EQ_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:num`--) SUBST1_TAC) THEN
  REWRITE_TAC[REAL_POW_ADD] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL_IMP THEN CONJ_TAC THENL [
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`&1`--) THEN
    RW_TAC arith_ss [REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[],
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]]);

(*--------------------------------------*)

val VAL_FINITE = store_thm (
  "VAL_FINITE",
  (--`!(a:float). Finite(a) ==> abs(Val a) <= largest(float_format)`--),
  GEN_TAC THEN REWRITE_TAC[ISFINITE, Val] THEN
  REWRITE_TAC[IS_FINITE_EXPLICIT, VALOF] THEN REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
  STRIP_TAC THEN REWRITE_TAC[float_format, fracwidth, bias, emax, expwidth, largest] THEN
  COND_CASES_TAC THENL [
    REWRITE_TAC [REAL_ABS_POW, REAL_ABS_MUL, REAL_ABS_DIV] THEN
    REWRITE_TAC[ABS_NEG, POW_ONE, REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_MUL_LID, REAL_ABS_MUL, real_div, REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[AC.AC REAL_MUL_AC_4 (--`(a:real) * b * c * d = b * (a * c * d)`--)] THEN
    ONCE_REWRITE_TAC[AC.AC REAL_MUL_AC_4 (--`(a:real) * b * c = b * (a * c)`--)] THEN
    MATCH_MP_TAC REAL_LE_LMUL_IMP THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
    CONJ_TAC THENL [
      MATCH_MP_TAC POW_POS THEN REWRITE_TAC[REAL_POS] ,
      ONCE_REWRITE_TAC[AC.AC REAL_MUL_AC_4 (--`a:real * (b * c) = (c * a) * b`--)] THEN
      REWRITE_TAC [REAL_OF_NUM_POW] THEN RW_TAC arith_ss [] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (--`(&2:real)`--) THEN CONJ_TAC THENL [
        REWRITE_TAC[REAL_ARITH (--`(a * b * c <= c) = (a * b * c <= (&1:real) * c)`--)] THEN
        MATCH_MP_TAC REAL_LE_RMUL_IMP THEN CONJ_TAC THENL [
          REAL_ARITH_TAC, ONCE_REWRITE_TAC[AC.AC REAL_MUL_AC_4 (--`a:real * b  = b * a`--)] THEN
          REWRITE_TAC[GSYM REAL_INV_1OVER,GSYM real_div] THEN MATCH_MP_TAC REAL_LE_LDIV THEN
          CONJ_TAC THENL [
            REWRITE_TAC [REAL_OF_NUM_POW,REAL_OF_NUM_LT] THEN
            RW_TAC arith_ss [] ,
            REWRITE_TAC[REAL_MUL_LID] THEN
            MATCH_MP_TAC REAL_LT_IMP_LE THEN
            ASM_REWRITE_TAC []]],
        REWRITE_TAC[REAL_MUL_RID] THEN RW_TAC arith_ss [REAL_INV_1OVER] THEN
        SUBGOAL_THEN (--`28948022309329048855892746252171976963317496166410141009864396001978282409984 = 2 pow 254`--)
        (fn th => REWRITE_TAC[th]) THENL [
          REWRITE_TAC [REAL_OF_NUM_POW,REAL_OF_NUM_EQ] THEN RW_TAC arith_ss [],
          SUBGOAL_THEN (--`(&2:real <= 2 pow 254 * (2 - 1 / 8388608)) = (&2:real * &8388608 <= 2 pow 254 *
          (2 - 1 / 8388608) * &8388608)`--) (fn th => REWRITE_TAC[th]) THENL [
            MATCH_MP_TAC (GSYM REAL_LE_RMUL) THEN REAL_ARITH_TAC, ALL_TAC] THEN
          ONCE_REWRITE_TAC[AC.AC REAL_MUL_AC_4 (--`a:real * b * c = a * (b * c)`--)] THEN REWRITE_TAC [REAL_SUB_RDISTRIB] THEN
          SUBGOAL_THEN (--`&1:real / &8388608 * &8388608  = &1 `--) (fn th => REWRITE_TAC[th]) THENL [
            REWRITE_TAC [GSYM REAL_INV_1OVER] THEN MATCH_MP_TAC REAL_MUL_LINV THEN REAL_ARITH_TAC, REWRITE_TAC [RRRC1]]]]],
    REWRITE_TAC [REAL_ABS_POW, REAL_ABS_MUL, REAL_ABS_DIV] THEN REWRITE_TAC[ABS_NEG, POW_ONE, REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_MUL_LID, REAL_ABS_MUL, real_div, REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[AC.AC REAL_MUL_AC_4 (--`(a:real) * b * c = b * a * c `--)] THEN
    ONCE_REWRITE_TAC[AC.AC REAL_MUL_AC_4 (--`(a:real) * b * c = a * (b * c) `--)] THEN
    SUBGOAL_THEN (--`(abs (&2:real)) pow (2:num ** (8 - 1) - 1) =
    ((&2:real) pow (2:num ** (8 - 1) - 1))`--) (fn th => REWRITE_TAC[th]) THENL [
      REWRITE_TAC [POW_ABS] THEN RW_TAC arith_ss [ABS_REFL] THEN MATCH_MP_TAC POW_POS THEN REAL_ARITH_TAC,
      MATCH_MP_TAC REAL_LE_LMUL_IMP THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN CONJ_TAC THENL [
        MATCH_MP_TAC POW_POS THEN REWRITE_TAC[REAL_POS], MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`((&2:real) pow (254:num)) *
        abs ((&1:real) + &(fraction (defloat a)) * inv (2 pow 23))`--) THEN CONJ_TAC THENL [
          ONCE_REWRITE_TAC[AC.AC REAL_MUL_AC_4 (--`(a:real) * (b * c) = (a * b) * c `--)] THEN MATCH_MP_TAC REAL_LE_RMUL_IMP THEN
          REWRITE_TAC[REAL_ABS_POS] THEN REWRITE_TAC[ABS_1,ABS_NEG] THEN REWRITE_TAC[POW_ONE] THEN REWRITE_TAC[REAL_MUL_LID] THEN
          SUBGOAL_THEN (--`abs (&2:real) = (&2:real)`--) (fn th => REWRITE_TAC[th]) THENL [
            RW_TAC arith_ss [ABS_REFL] THEN REAL_ARITH_TAC, MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL [
              REAL_ARITH_TAC, ASM_REWRITE_TAC[GSYM LT_SUC_LE] THEN RW_TAC arith_ss [ADD1] THEN ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LT]]],
          RW_TAC arith_ss [] THEN SUBGOAL_THEN (--`(((&2:real) pow 254) * abs (1 + & (fraction (defloat a)) * inv (2 pow 23)) <=
          ((&2:real) pow 254) * (2 - inv (2 pow 23))) = (inv ((&2:real) pow (254:num))) * ((&2:real) pow 254 *
          abs (1 + & (fraction (defloat a)) * inv (2 pow 23))) <= (inv ((&2:real) pow (254:num))) *
          ((&2:real) pow 254 * (2 - inv (2 pow 23)))`--) (fn th => REWRITE_TAC[th]) THENL [
            MATCH_MP_TAC (GSYM REAL_LE_LMUL) THEN MATCH_MP_TAC REAL_INV_POS THEN REWRITE_TAC [REAL_OF_NUM_POW] THEN
            REWRITE_TAC [REAL_OF_NUM_LT] THEN REWRITE_TAC[num_CONV(--`2:num`--),ZERO_LESS_EXP],
            ONCE_REWRITE_TAC[AC.AC REAL_MUL_AC_4 (--`(a:real) * (b * c) = (a * b) * c`--)] THEN
            SUBGOAL_THEN (--`((inv ((&2:real) pow (254:num))) * ((&2:real) pow 254) = &1 :real)`--)
            (fn th => REWRITE_TAC[th, REAL_MUL_LID]) THENL [
              MATCH_MP_TAC REAL_MUL_LINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC, REWRITE_TAC [REAL_OF_NUM_POW] THEN
              SUBGOAL_THEN (--`!(a:num) (b:num) c. abs(&a + &b * inv(&c)) = &a + &b * inv(&c)`--)
              (fn th => REWRITE_TAC[th,GSYM REAL_OF_NUM_POW]) THENL [
                REWRITE_TAC[ABS_REFL] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_ADD THEN
                REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
                REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[REAL_POS],
                SUBGOAL_THEN (--`1 + & (fraction (defloat a)) * inv (2 pow 23) <= 2 - inv (2 pow 23) =
                (&2 pow 23) * (1 + & (fraction (defloat a)) * inv (2 pow 23)) <=
                (&2 pow 23) * (2 - inv (2 pow 23))`--) (fn th => REWRITE_TAC[th]) THENL [
                  MATCH_MP_TAC (GSYM REAL_LE_LMUL) THEN REWRITE_TAC [REAL_OF_NUM_POW,REAL_OF_NUM_LT]
                  THEN REWRITE_TAC[num_CONV(--`2:num`--),ZERO_LESS_EXP],
                  REWRITE_TAC [REAL_ADD_LDISTRIB] THEN REWRITE_TAC [REAL_SUB_LDISTRIB] THEN
                  REWRITE_TAC[REAL_ARITH (--`(a * (b:real * c)) = (a * b * c)`--)] THEN
                  REWRITE_TAC[REAL_ARITH (--`(a * b:real * c) = (b * (a * c))`--)] THEN
                  SUBGOAL_THEN (--`(((&2:real) pow 23) *  (inv ((&2:real) pow (23:num))) = &1 :real)`--)
                  (fn th => REWRITE_TAC[th, REAL_MUL_RID]) THENL [
                    MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC,
                    REWRITE_TAC[REAL_ARITH (--`(a + b:real <= c - d) = (b <= c - a - d)`--)] THEN
                    REWRITE_TAC[REAL_ARITH (--`(a * &2:real - a) = (a)`--)] THEN
                    REWRITE_TAC [REAL_OF_NUM_POW] THEN RW_TAC arith_ss [] THEN
                    SUBGOAL_THEN (--`&8388608 - &1 = &8388607:real`--) (fn th => REWRITE_TAC[th, REAL_MUL_RID]) THENL [
                      SUBGOAL_THEN (--`8388607:num = 8388608 - 1`--) (fn th => REWRITE_TAC[th]) THENL [
                        RW_TAC arith_ss [], MATCH_MP_TAC REAL_OF_NUM_SUB THEN RW_TAC arith_ss []],
                      REWRITE_TAC [REAL_OF_NUM_LE] THEN UNDISCH_TAC (--`& (fraction (defloat a)) < 8388608`--) THEN
                      REWRITE_TAC [REAL_OF_NUM_LT] THEN RW_TAC arith_ss []]]]]]]]]]]);

(*---------------------------------*)

val ISFINITE_LEMMA = store_thm (
  "ISFINITE_LEMMA",
  (--`! s e f. s < 2 /\ e < 255 /\ f < 2 EXP 23
      ==> Finite(float(s,e,f)) /\ is_valid(float_format)(s,e,f)`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ISFINITE] THEN
  SUBGOAL_THEN (--`is_valid(float_format) (s,e,f)`--) ASSUME_TAC THENL [
    ASM_REWRITE_TAC[is_valid, float_format, expwidth, fracwidth] THEN
    RW_TAC arith_ss [], ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o GEN_REWRITE_RULE I [float_tybij]) THEN
    ASM_REWRITE_TAC[is_finite, is_normal, is_denormal, is_zero] THEN
    REWRITE_TAC[fraction, exponent, emax, float_format] THEN
    REWRITE_TAC[expwidth, fracwidth] THEN
    UNDISCH_TAC (--`e:num < 255`--) THEN RW_TAC arith_ss []]);

(* ------------------------------------------------------------------------- *)
(* Explicit numeric value for threshold, to save repeated recalculation.     *)
(* ------------------------------------------------------------------------- *)

val FLOAT_THRESHOLD_EXPLICIT = store_thm (
  "FLOAT_THRESHOLD_EXPLICIT",
  (--`threshold(float_format) = &340282356779733661637539395458142568448`--),
  REWRITE_TAC[threshold, float_format, emax, bias, fracwidth, expwidth] THEN
  RW_TAC arith_ss [REAL_INV_1OVER , ADD1, REAL_SUB_LDISTRIB ] THEN
  SUBGOAL_THEN (--`254:num = 127 + 127 `--) (fn th => REWRITE_TAC[th,POW_ADD,real_div ]) THENL [
    RW_TAC arith_ss [], REWRITE_TAC[REAL_ARITH (--`a:real  * b * c * d = a  * (b * c) * d`--)] THEN
    SUBGOAL_THEN (--`2 pow 127 * inv (2 pow 127) = &1:real`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID,REAL_MUL_RID]) THENL [
      MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC,
      SUBGOAL_THEN (--`127:num = 103 + 24 `--) (fn th => REWRITE_TAC[th,POW_ADD,real_div ]) THENL [
        RW_TAC arith_ss [], REWRITE_TAC[REAL_ARITH (--`a:real * b * c  = a * (b * c)`--)] THEN
        SUBGOAL_THEN (--`2 pow 24 * inv (2 pow 24) = &1:real`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID,REAL_MUL_RID]) THENL [
          MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC, REWRITE_TAC [RRRC8]]]]]);

(*-----------------------*)

val VAL_THRESHOLD = store_thm (
  "VAL_THRESHOLD",
  (--`!a. Finite(a) ==> abs(Val a) < threshold float_format`--),
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC (--`largest(float_format)`--) THEN CONJ_TAC THENL [
    MATCH_MP_TAC VAL_FINITE THEN ASM_REWRITE_TAC[], REWRITE_TAC[FLOAT_THRESHOLD_EXPLICIT] THEN
    REWRITE_TAC[largest, float_format, emax, bias, fracwidth, expwidth] THEN RW_TAC arith_ss [real_div] THEN
    SUBGOAL_THEN (--`254:num = 127 + 127 `--) (fn th => REWRITE_TAC[th,POW_ADD,real_div ]) THENL [
      RW_TAC arith_ss [], REWRITE_TAC[REAL_ARITH (--`a:real  * b * c * d = a  * (b * c) * d`--)] THEN
      SUBGOAL_THEN (--`2 pow 127 * inv (2 pow 127) = &1:real`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID,REAL_MUL_RID]) THENL [
        MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC, REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
        SUBGOAL_THEN (--`127:num = 104 + 23 `--) (fn th => REWRITE_TAC[th,POW_ADD,real_div ]) THENL [
          RW_TAC arith_ss [], REWRITE_TAC[REAL_ARITH (--`a:real  * b * c  = a  * (b * c)`--)] THEN
          SUBGOAL_THEN (--`2 pow 23 * inv (2 pow 23) = &1:real`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID,REAL_MUL_RID]) THENL [
            MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC,
            REWRITE_TAC[REAL_ARITH (--`a:real  * (b * c)  = (a  * b) * c`--)] THEN REWRITE_TAC[GSYM POW_ADD] THEN
            RW_TAC arith_ss [] THEN REWRITE_TAC [RRRC9]]]]]]);

(* ------------------------------------------------------------------------- *)
(* Lifting up of rounding (to nearest).                                      *)
(* ------------------------------------------------------------------------- *)

val error = Define `error (x:real) = Val(float(round(float_format) To_nearest x)) - x`;

(*-----------------------*)

val BOUND_AT_WORST_LEMMA = store_thm (
  "BOUND_AT_WORST_LEMMA",
  (--`! a x. abs(x) < threshold(float_format) /\ is_finite(float_format) a
      ==>  abs(valof(float_format) (round(float_format) To_nearest x) - x)
      <= abs(valof(float_format) a - x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_ARITH (--`abs(x:real) < y = ~(x <= ~y) /\ ~(x >= y)`--)] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[round_def] THEN RW_TAC arith_ss [round_def] THEN
  MP_TAC(MATCH_MP CLOSEST_IS_CLOSEST (SPEC (--`float_format`--) IS_FINITE_FINITE)) THEN
  REWRITE_TAC[IS_FINITE_NONEMPTY] THEN DISCH_THEN(MP_TAC o SPEC (--`valof(float_format)`--)) THEN
  DISCH_THEN(MP_TAC o SPEC (--`\ (a:num#num#num) . (EVEN (fraction a))`--)) THEN
  DISCH_THEN(MP_TAC o SPEC (--`x:real`--)) THEN REWRITE_TAC[is_closest] THEN
  DISCH_THEN(MATCH_MP_TAC o SPEC (--`a:num#num#num`--) o CONJUNCT2) THEN
  REWRITE_TAC [GSPECIFICATION] THEN EXISTS_TAC (--`(a:num#num#num)`-- ) THEN RW_TAC arith_ss []);

(*-----------------------*)

val ERROR_AT_WORST_LEMMA = store_thm (
  "ERROR_AT_WORST_LEMMA",
  (--`!a x. abs(x) < threshold(float_format) /\ Finite(a) ==> abs(error(x)) <= abs(Val(a) - x)`--),
  REWRITE_TAC[ISFINITE, Val, error, BOUND_AT_WORST_LEMMA, Val, DEFLOAT_FLOAT_ROUND]);

(*--------------------------------------------------------------*)

val ERROR_IS_ZERO = store_thm (
  "ERROR_IS_ZERO",
  (--`!a x. Finite(a) /\ (Val(a) = x) ==> (error(x) = &0)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN MP_TAC(SPECL [(--`a:float`--), (--`x:real`--)] ERROR_AT_WORST_LEMMA) THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL, REAL_ABS_0] THEN REWRITE_TAC[REAL_ARITH (--`abs(x) <= &0 = (x = &0)`--)] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`largest(float_format)`--) THEN CONJ_TAC THENL [
    MATCH_MP_TAC VAL_FINITE THEN ASM_REWRITE_TAC[], REWRITE_TAC[largest, threshold, float_format] THEN
    REWRITE_TAC[emax, expwidth, fracwidth, bias] THEN RW_TAC arith_ss [] THEN
    SUBGOAL_THEN (--`254:num = 127 + 127 `--) (fn th => REWRITE_TAC[th,POW_ADD,real_div ]) THENL [
      RW_TAC arith_ss [], REWRITE_TAC[REAL_ARITH (--`a:real  * b * c * d = a  * (b * c) * d`--)] THEN
      SUBGOAL_THEN (--`2 pow 127 * inv (2 pow 127) = &1:real`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID,REAL_MUL_RID]) THENL [
        MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC, MATCH_MP_TAC REAL_LT_LMUL_IMP THEN CONJ_TAC THENL [
          REWRITE_TAC[pow] THEN REWRITE_TAC[REAL_ARITH (--`(a:real - b < a - c) = (c < b)`--)] THEN
          SUBGOAL_THEN (--`inv ((&2:real) * (&2:real) pow 23) < inv ((&2:real) pow 23) = (inv ((&2:real) * (&2:real) pow 23) *
          (&2:real) pow 23 < inv ((&2:real) pow   23) * (&2:real) pow 23)`--) (fn th => REWRITE_TAC[th]) THENL [
            MATCH_MP_TAC (GSYM REAL_LT_RMUL) THEN REWRITE_TAC [REAL_OF_NUM_POW] THEN REWRITE_TAC [REAL_OF_NUM_LT] THEN
            REWRITE_TAC[num_CONV(--`2:num`--),ZERO_LESS_EXP], SUBGOAL_THEN (--`inv ((&2:real) * ((&2:real) pow 23)) =
            inv ((&2:real)) * inv ((&2:real) pow 23)`--) (fn th => REWRITE_TAC[th]) THENL [
              MATCH_MP_TAC REAL_INV_MUL THEN CONJ_TAC THENL [
                REAL_ARITH_TAC, MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC],
              REWRITE_TAC[REAL_ARITH (--`a:real  * b * c = a  * (b * c)`--)] THEN SUBGOAL_THEN (--` inv (2 pow 23) * ((&2:real) pow 23) =
              &1:real`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID,REAL_MUL_RID]) THENL [
                MATCH_MP_TAC REAL_MUL_LINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC,
                SUBGOAL_THEN (--`inv (&2:real) < (&1:real) = inv (&2:real) * (&2:real)  <
                (&1:real) * (&2:real)`--) (fn th => REWRITE_TAC[th]) THENL [
                  MATCH_MP_TAC (GSYM REAL_LT_RMUL) THEN REAL_ARITH_TAC,
                  SUBGOAL_THEN (--` inv (&2) * (&2:real) = &1:real`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID,REAL_MUL_RID]) THENL [
                    MATCH_MP_TAC REAL_MUL_LINV THEN REAL_ARITH_TAC, MATCH_MP_TAC REAL_LT_INV THEN CONJ_TAC THENL [
                      REWRITE_TAC[num_CONV(--`23:num`--)] THEN MATCH_MP_TAC POW_POS_LT THEN REAL_ARITH_TAC,
                      MATCH_MP_TAC REAL_POW_MONO_LT THEN CONJ_TAC THENL [
                        REAL_ARITH_TAC, RW_TAC arith_ss []]]]]]]],
          REWRITE_TAC [REAL_OF_NUM_POW] THEN REWRITE_TAC [REAL_OF_NUM_LT] THEN REWRITE_TAC[num_CONV(--`2:num`--),ZERO_LESS_EXP]]]]]);

(*--------------------------------------------------------------*)

val REAL_LT_LCANCEL_IMP = store_thm (
  "REAL_LT_LCANCEL_IMP",
  (--`!(x:real) (y:real) (z:real). (&0 < x) /\ ((x * y) < (x * z)) ==> (y < z)`--),
  REPEAT GEN_TAC THEN
  DISCH_THEN (fn th => ASSUME_TAC (CONJUNCT1 th) THEN MP_TAC th) THEN
  RW_TAC arith_ss [REAL_LT_LMUL]);

(*--------------------------------------------------------------*)

val REAL_OF_NUM_LT = store_thm (
  "REAL_OF_NUM_LT",
  (--`! m n. (&m:real) < (&n:real) = m < n`--),
  RW_TAC arith_ss [real_lt] THEN RW_TAC arith_ss [REAL_OF_NUM_LE]);

(*--------------------------------------------------------------*)

val ERROR_BOUND_LEMMA1 = store_thm (
  "ERROR_BOUND_LEMMA1",
  (--`! (x:real). (&0:real) <= (x:real) /\ x < (&1:real)
      ==> ?(n:num). n < (2:num) EXP (23:num) /\
      (&n:real) / (&2:real) pow 23 <= x /\ x < (&(SUC n):real) / (&2:real) pow 23`--),
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC (--`\(n:num). (&n:real) / &2 pow 23 <= x`--) (EXISTS_GREATEST)) THEN
  REWRITE_TAC[] THEN W(C SUBGOAL_THEN MP_TAC o lhs o lhand o snd) THENL [
    CONJ_TAC THENL [
      EXISTS_TAC (--`0:num`--) THEN RW_TAC arith_ss [REAL_MUL_LZERO, real_div],
      EXISTS_TAC (--`(2:num) EXP 23`--) THEN X_GEN_TAC (--`n:num`--) THEN
      DISCH_TAC THEN RW_TAC arith_ss [REAL_OF_NUM_POW] THEN
      RW_TAC arith_ss [GSYM real_lt] THEN MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
      EXISTS_TAC (--`inv((&2:real) pow 23)`--) THEN RW_TAC arith_ss [] THENL [
        RW_TAC arith_ss [inv23gt0], RW_TAC arith_ss [REAL_LT_LMUL,inv23gt0] THEN
        RW_TAC arith_ss [REAL_LT_RDIV_EQ,noteteeszegtz] THEN
        UNDISCH_TAC (--`n:num > 2 EXP 23`--) THEN
        UNDISCH_TAC (--`x:real < (&1:real)`--) THEN
        REWRITE_TAC [lt1eqmul,GREATER_DEF,GSYM REAL_OF_NUM_LT ] THEN
        REWRITE_TAC[TAUT (`(a ==> b ==> c) = (a /\ b ==> c)`)] THEN
        RW_TAC arith_ss [] THEN
        UNDISCH_TAC (--`x:real * &8388608:real < &8388608:real`--) THEN
        UNDISCH_TAC (--`&8388608 < & n:real`--) THEN
        REWRITE_TAC[TAUT (`(a ==> b ==> c) = (b /\ a ==> c)`)] THEN
        REAL_ARITH_TAC]],
    DISCH_THEN(fn th => REWRITE_TAC[th]) THEN
    DISCH_THEN(X_CHOOSE_THEN (--`n:num`--) MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC (--`SUC n`--)) THEN
    REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
    EXISTS_TAC (--`n:num`--) THEN REPEAT CONJ_TAC THENL [
      RW_TAC arith_ss [GSYM REAL_OF_NUM_POW ,GSYM REAL_OF_NUM_LT ] THEN
      UNDISCH_TAC (--`(\n. & n:real / &2:real pow 23:num <= x) n`--) THEN
      RW_TAC arith_ss [] THEN UNDISCH_TAC (--`x:real < 1`--) THEN
      UNDISCH_TAC (--`((& n):real / &2:real pow 23 <= x)`--) THEN
      RW_TAC arith_ss [REAL_LE_LDIV_EQ,twogz,lt1eqmul] THEN
      REWRITE_TAC [GSYM REAL_OF_NUM_LT] THEN
      UNDISCH_TAC (--`& n:real <= x * 2 pow 23`--) THEN
      UNDISCH_TAC (--`x * &8388608:real < &8388608`--) THEN
      REWRITE_TAC[TAUT (`(a ==> b ==> c) = (a /\ b ==> c)`)] THEN
      REWRITE_TAC[REAL_OF_NUM_POW] THEN RW_TAC arith_ss [] THEN
      UNDISCH_TAC (--`& n:real <= x * &8388608:real`--) THEN
      UNDISCH_TAC (--`x * &8388608:real < &8388608`--) THEN
      REWRITE_TAC[TAUT (`(a ==> b ==> c) = (b /\ a ==> c)`)] THEN
      REAL_ARITH_TAC, UNDISCH_TAC (--`(\n. & n / 2 pow 23 <= x) n`--) THEN
      RW_TAC arith_ss [],
      UNDISCH_TAC (--`SUC n > n ==> ~(\n. & n / 2 pow 23 <= x) (SUC n)`--) THEN
      RW_TAC arith_ss [REAL_NOT_LE]]]);

(*---------------------------*)

val ERROR_BOUND_LEMMA2 = store_thm (
  "ERROR_BOUND_LEMMA2",
  (--`! x:real. &0:real <= x /\ x < &1
      ==> ?n:num. n <= 2 EXP 23 /\ abs(x - &n / &2 pow 23) <= inv(&2 pow 24)`--),
  let val lemma = REAL_ARITH
  (--`! a:real b x d. a <= x /\ x < b
      ==> b <= a + &2:real * d ==> abs(x - a) <= d \/ abs(x - b) <= d`--) in
  GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP ERROR_BOUND_LEMMA1) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`n:num`--) MP_TAC) THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN DISCH_THEN(MP_TAC o SPEC (--`inv(&2:real pow 24)`--)) THEN
  W(C SUBGOAL_THEN MP_TAC o lhand o lhand o snd) THENL [
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC, real_div, REAL_ADD_RDISTRIB] THEN
    REWRITE_TAC[REAL_LE_LADD,REAL_MUL_LID] THEN RW_TAC arith_ss [tittfittt] THEN
    REAL_ARITH_TAC, DISCH_THEN(fn th => REWRITE_TAC[th]) THEN
    DISCH_THEN DISJ_CASES_TAC THENL [
      EXISTS_TAC (--`n:num`--) THEN ASM_REWRITE_TAC [GSYM LESS_EQ] THEN
      MATCH_MP_TAC LESS_IMP_LESS_OR_EQ  THEN ASM_REWRITE_TAC[],
      EXISTS_TAC (--`SUC n:num`--) THEN ASM_REWRITE_TAC [GSYM LESS_EQ]]] end);

(*---------------------------*)

val ERROR_BOUND_LEMMA3 = store_thm (
  "ERROR_BOUND_LEMMA3",
  (--`! x:real. &1:real <= x /\ x < &2
      ==> ?n. n <= 2 EXP 23 /\ abs((&1 + &n / &2 pow 23) - x) <= inv(&2 pow 24)`--),
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN (--`&0:real <= x - &1 /\ x - &1 < &1`--) MP_TAC THENL [
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    DISCH_THEN(MP_TAC o MATCH_MP ERROR_BOUND_LEMMA2) THEN
    DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[GSYM ABS_NEG]) THEN
    REWRITE_TAC[REAL_NEG_SUB, REAL_ARITH (--`a - (b - c) = (c + a:real) - b`--)]]);

(*---------------------------*)

val ERROR_BOUND_LEMMA4 = store_thm (
  "ERROR_BOUND_LEMMA4",
  (--`! x:real. (&1:real) <= x /\ x < (&2:real)
      ==> ?e f. abs(Val(float(0,e,f)) - x) <= inv(&2:real pow 24) /\
      f < 2 EXP 23 /\ ((e = bias(float_format)) \/
      (e = SUC(bias(float_format))) /\ (f = 0))`--),
  GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP ERROR_BOUND_LEMMA3) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`n:num`--) STRIP_ASSUME_TAC) THEN UNDISCH_TAC (--`n:num <= 2 EXP 23`--) THEN
  REWRITE_TAC[LESS_OR_EQ] THEN DISCH_THEN DISJ_CASES_TAC THENL [
    EXISTS_TAC (--`bias(float_format)`--) THEN EXISTS_TAC (--`n:num`--) THEN ASM_REWRITE_TAC[Val] THEN
    SUBGOAL_THEN (--`defloat (float (0:num,(bias float_format,n))) = (0,bias(float_format),n)`--) SUBST1_TAC THENL [
      REWRITE_TAC[GSYM float_tybij] THEN REWRITE_TAC[is_valid, float_format] THEN
      ASM_REWRITE_TAC[bias, expwidth, fracwidth] THEN RW_TAC arith_ss [],
      REWRITE_TAC[valof, bias, expwidth, fracwidth,float_format] THEN RW_TAC arith_ss [] THEN
      REWRITE_TAC[valof, bias, expwidth, fracwidth, float_format] THEN
      RW_TAC arith_ss [v127not0,real_div,REAL_MUL_RINV,pow,REAL_MUL_LID] THEN RW_TAC arith_ss [GSYM real_div]],
    EXISTS_TAC (--`SUC(bias(float_format:(num#num)))`--) THEN EXISTS_TAC (--`0:num`--) THEN
    RW_TAC arith_ss [Val] THEN SUBGOAL_THEN (--`defloat (float ((0:num),(SUC (bias float_format),(0:num)))) =
    (0:num,SUC(bias(float_format)),0)`--) SUBST1_TAC THENL [
      REWRITE_TAC[GSYM float_tybij] THEN REWRITE_TAC[is_valid, float_format] THEN
      ASM_REWRITE_TAC[bias, expwidth, fracwidth] THEN RW_TAC arith_ss [],
      REWRITE_TAC[valof, bias, expwidth, fracwidth, float_format] THEN RW_TAC arith_ss [] THEN
      REWRITE_TAC[pow, REAL_MUL_LID, real_div, REAL_MUL_LZERO] THEN REWRITE_TAC[REAL_ADD_RID, REAL_MUL_RID] THEN
      UNDISCH_TAC (--`abs(((&1:real) + &(2 EXP 23) / &2 pow 23) - x) <= inv(&2 pow 24)`--) THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN RW_TAC arith_ss [REAL_DIV_REFL,REAL_MUL_RINV,v23not0,v127not0] THEN
      RW_TAC arith_ss [ttpinv] THEN
      UNDISCH_TAC (--`abs ((&1:real) + (&1:real) - (x:real)) <= inv ((&2:real) pow (24:num))`--) THEN
      REWRITE_TAC[num_CONV(--`128:num`--)] THEN REWRITE_TAC[pow] THEN REWRITE_TAC[REAL_ARITH (--`a:real  * b * c = a  * (b * c)`--)] THEN
      SUBGOAL_THEN (--` (2 pow 127) * inv ((&2:real) pow 127) = &1:real`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID,REAL_MUL_RID]) THENL [
        MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC, REAL_ARITH_TAC]]]);

(*---------------------------*)

val ERROR_BOUND_LEMMA5 = store_thm (
  "ERROR_BOUND_LEMMA5",
  (--`! (x:real). (&1:real) <= abs(x) /\ abs(x) < (&2:real)
      ==> ?s e f. abs(Val(float(s,e,f)) - x) <= inv(&2 pow 24) /\
      s < 2 /\ f < 2 EXP 23 /\ ((e = bias(float_format)) \/
      (e = SUC(bias(float_format))) /\ (f = 0))`--),
  GEN_TAC THEN DISCH_TAC THEN SUBGOAL_THEN (--`(&1:real) <= x /\ x < (&2:real) \/
  (&1:real) <= ~x /\ ~x < (&2:real)`--) MP_TAC THENL [
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    DISCH_THEN(DISJ_CASES_THEN (MP_TAC o MATCH_MP ERROR_BOUND_LEMMA4))] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`e:num`--) (X_CHOOSE_THEN (--`f:num`--)
  (CONJUNCTS_THEN ASSUME_TAC))) THENL [
    EXISTS_TAC (--`0:num`--), EXISTS_TAC (--`1:num`--)] THEN
  EXISTS_TAC (--`e:num`--) THEN EXISTS_TAC (--`f:num`--) THEN
  RW_TAC arith_ss [] THEN ONCE_REWRITE_TAC[GSYM ABS_NEG] THENL [
    UNDISCH_TAC (--`abs(Val(float (0,(bias float_format,f))) - ~ x) <= inv (&2 pow 24)`--) THEN
    REWRITE_TAC[REAL_ARITH (--`~(x - y) = ~(x:real) - ~y`--)] THEN
    REWRITE_TAC[Val] THEN
    SUBGOAL_THEN (--`(defloat(float(0,bias float_format,f)) = (0:num,bias float_format,f)) /\
    (defloat(float(1,bias float_format,f)) = (1:num,bias float_format,f))`--)
    (CONJUNCTS_THEN SUBST1_TAC) THENL [
      REWRITE_TAC[GSYM float_tybij] THEN REWRITE_TAC[is_valid, float_format] THEN
      ASM_REWRITE_TAC[bias, expwidth, fracwidth] THEN RW_TAC arith_ss [],
      REWRITE_TAC[valof] THEN COND_CASES_TAC THENL [
        ASM_REWRITE_TAC[POW_1, pow] THEN REWRITE_TAC[REAL_MUL_LNEG, REAL_NEG_NEG],
        ASM_REWRITE_TAC[POW_1, pow] THEN REWRITE_TAC[REAL_MUL_LNEG, REAL_NEG_NEG]]],
    UNDISCH_TAC (--`abs(Val(float (0:num,SUC (bias float_format),0)) - ~ x) <= inv (&2 pow 24)`--) THEN
    REWRITE_TAC[REAL_ARITH (--`~(x - y) = ~(x:real) - ~y`--)] THEN REWRITE_TAC[Val] THEN
    SUBGOAL_THEN (--`(defloat(float(0,SUC (bias float_format),0)) = (0:num,SUC (bias float_format),0)) /\
    (defloat(float(1,SUC (bias float_format),0)) = (1:num,SUC (bias float_format),0))`--)
    (CONJUNCTS_THEN SUBST1_TAC) THENL [
      REWRITE_TAC[GSYM float_tybij] THEN REWRITE_TAC[is_valid, float_format] THEN
      ASM_REWRITE_TAC[bias, expwidth, fracwidth] THEN RW_TAC arith_ss [],
      REWRITE_TAC[valof] THEN COND_CASES_TAC THENL [
        ASM_REWRITE_TAC[POW_1, pow] THEN REWRITE_TAC[REAL_MUL_LNEG, REAL_NEG_NEG],
        ASM_REWRITE_TAC[POW_1, pow] THEN REWRITE_TAC[REAL_MUL_LNEG, REAL_NEG_NEG]]]]);

(*---------------------------*)

val REAL_MUL_AC = store_thm (
  "REAL_MUL_AC",
  (--`((m:real) * n = n * m) /\ ((m * n) * p = m * (n * p)) /\ (m * (n * p) = n * (m * p))`--),
  REWRITE_TAC[REAL_MUL_ASSOC, EQT_INTRO(SPEC_ALL REAL_MUL_SYM)] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC REAL_MUL_SYM);

(*---------------------------*)

val REAL_LE_LCANCEL_IMP = store_thm (
  "REAL_LE_LCANCEL_IMP",
  (--`!(x:real) (y:real) (z:real). &0 < x /\ x * y <= x * z ==> y <= z`--),
  REPEAT GEN_TAC THEN RW_TAC arith_ss [REAL_LE_LMUL] THEN
  UNDISCH_TAC (--`((x:real) * (y:real) <= x * (z:real))`--) THEN
  UNDISCH_TAC (--`0 < (x:real)`--) THEN RW_TAC arith_ss [REAL_LE_LMUL]);

(*---------------------------*)

val ERROR_BOUND_LEMMA6 = store_thm (
  "ERROR_BOUND_LEMMA6",
  (--`! (x:real). (&0:real) <= x /\ x < inv (&2 pow 126)
      ==> ?n. n <= 2 EXP 23 /\ abs (x - &2 / &2 pow 127 * &n / &2 pow 23) <= inv (&2 pow 150)`--),
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC (--`&2 pow 126 * x`--) ERROR_BOUND_LEMMA2) THEN
  W(C SUBGOAL_THEN MP_TAC o lhand o lhand o snd) THENL [
    CONJ_TAC THENL [
      MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC (--`inv(&2 pow 126)`--) THEN
      CONJ_TAC THENL [
        MATCH_MP_TAC REAL_INV_POS THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC,
        REWRITE_TAC[REAL_MUL_RZERO] THEN SUBGOAL_THEN (--`inv(&2 pow 126) * &2 pow 126 = &1`--)
        (fn th => REWRITE_TAC[REAL_MUL_ASSOC, th, REAL_MUL_LID]) THENL [
          MATCH_MP_TAC REAL_MUL_LINV THEN MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN
          REAL_ARITH_TAC, ASM_REWRITE_TAC[]]],
      MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC (--`inv(&2 pow 126)`--) THEN CONJ_TAC THENL [
        MATCH_MP_TAC REAL_INV_POS  THEN MATCH_MP_TAC REAL_POW_LT THEN
        REAL_ARITH_TAC, REWRITE_TAC[REAL_MUL_RZERO] THEN SUBGOAL_THEN (--`inv(&2 pow 126) * &2 pow 126 = &1`--)
        (fn th => ASM_REWRITE_TAC[REAL_MUL_ASSOC, th, REAL_MUL_LID, REAL_MUL_RID]) THEN
        MATCH_MP_TAC REAL_MUL_LINV THEN MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC]],
    DISCH_THEN(fn th => REWRITE_TAC[th]) THEN DISCH_THEN(X_CHOOSE_THEN (--`n:num`--) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (--`n:num`--) THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
    EXISTS_TAC (--`(&2:real) pow 126`--) THEN CONJ_TAC THENL [
      MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC, REWRITE_TAC [real_div] THEN
      ONCE_REWRITE_TAC[REAL_ARITH (--`(a:real) * ((b:real) * (c:real)) = (a * b) * c`--)] THEN
      SUBGOAL_THEN (--`!x. &2 pow 126 * abs(x) = abs(&2 pow 126 * x)`--) (fn th => REWRITE_TAC[th]) THENL [
        REWRITE_TAC[REAL_ABS_MUL, REAL_ABS_POW, REAL_ABS_NUM],
        ONCE_REWRITE_TAC[REAL_ARITH (--`(a:real) * ((b:real) - c) = (a * b - (a * c)) `--)] THEN
        ONCE_REWRITE_TAC[REAL_ARITH (--`(a:real) * ((b:real) * (c:real) * d * e) = (a * b * c) * d * e`--)] THEN
        UNDISCH_TAC (--`abs(&2 pow 126 * x - &n / &2 pow 23) <= inv(&2 pow 24)`--) THEN
        SUBGOAL_THEN (--`((&2:real) pow 126 * &2 * (inv (&2:real pow 127)) = &1:real) /\ (&2 pow 126 * inv (&2 pow 150) = inv (&2 pow 24))`--)
        (fn th => REWRITE_TAC[th,REAL_MUL_LID,real_div ]) THEN CONJ_TAC THENL [
          REWRITE_TAC[num_CONV (--`127:num`--)] THEN REWRITE_TAC[pow] THEN
          SUBGOAL_THEN (--`inv ((&2:real) * (&2 pow 126)) = inv (&2) * inv (&2 pow 126)`--) (fn th => REWRITE_TAC[th]) THENL [
            MATCH_MP_TAC REAL_INV_MUL THEN CONJ_TAC THENL [
              REAL_ARITH_TAC, MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC],
            ONCE_REWRITE_TAC[REAL_ARITH (--`(a:real) * (b:real) * ((c:real) * d) = (a * d) * (b * c)`--)] THEN
            SUBGOAL_THEN (--`((&2:real) pow 126 * (inv (&2:real pow 126)) = &1:real) /\ (&2  * inv (&2) = &1)`--)
            (fn th => REWRITE_TAC[th,REAL_MUL_LID ]) THEN CONJ_TAC THENL [
              MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC,
              MATCH_MP_TAC REAL_MUL_RINV THEN REAL_ARITH_TAC]],
          SUBGOAL_THEN (--`150:num = 126 + 24`--) (fn th => REWRITE_TAC[th,POW_ADD ]) THENL [
            RW_TAC arith_ss [],
            SUBGOAL_THEN (--`inv ((&2:real) pow 126 * (&2:real) pow 24) =  inv ((&2:real) pow 126) * inv ((&2:real) pow 24)`--)
            (fn th => REWRITE_TAC[th]) THENL [
              MATCH_MP_TAC REAL_INV_MUL THEN CONJ_TAC THENL [
                MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC,
                MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC],
              ONCE_REWRITE_TAC[REAL_ARITH (--`(a:real) * ((b:real) * c) = (a * b) * c`--)] THEN
              SUBGOAL_THEN (--`((&2:real) pow 126) * inv (&2 pow 126) = (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID ]) THEN
              MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC]]]]]]);

(*---------------------------*)

val EXP_LT_0 = store_thm (
  "EXP_LT_0",
  (--`!n x. 0 < x EXP n = ~(x = 0) \/ (n = 0)`--),
  REWRITE_TAC[GSYM NOT_LESS_EQUAL,LE, EXP_EQ_0, DE_MORGAN_THM]);

(*---------------------------*)

val ERROR_BOUND_LEMMA7 = store_thm (
  "ERROR_BOUND_LEMMA7",
  (--`! (x:real). (&0:real) <= x /\ x < inv(&2 pow 126)
      ==> ?e f. abs(Val(float(0,e,f)) - x) <= inv(&2 pow 150) /\
      f < 2 EXP 23 /\ ((e = 0) \/ (e = 1) /\ (f = 0))`--),
  GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP ERROR_BOUND_LEMMA6) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`n:num`--) MP_TAC) THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[LESS_OR_EQ ]) THENL [
    EXISTS_TAC (--`0:num`--) THEN EXISTS_TAC (--`n:num`--) THEN ASM_REWRITE_TAC[Val] THEN
    SUBGOAL_THEN (--`defloat(float(0,0,n)) = (0,0,n)`--) SUBST1_TAC THENL [
      REWRITE_TAC[GSYM float_tybij] THEN REWRITE_TAC[is_valid, float_format, expwidth, fracwidth] THEN
      ASM_REWRITE_TAC[] THEN RW_TAC arith_ss [], REWRITE_TAC[valof, float_format, bias, fracwidth, expwidth] THEN
      UNDISCH_TAC (--`abs(x - &2 / &2 pow 127 * &n / &2 pow 23) <= inv (&2 pow 150)`--) THEN
      RW_TAC arith_ss [] THEN UNDISCH_TAC (--`abs (x - &2:real / 2 pow 127 * & n / 2 pow 23) <= inv (2 pow 150)`--) THEN
      REWRITE_TAC [real_div] THEN ONCE_REWRITE_TAC[REAL_ARITH (--`(a:real) * (b:real) * ((c:real) * d) = (a * b * c * d)`--)] THEN
      RW_TAC arith_ss [pow, REAL_MUL_LID,ABS_SUB,real_div]],
    EXISTS_TAC (--`1:num`--) THEN EXISTS_TAC (--`0:num`--) THEN ASM_REWRITE_TAC[Val, EXP_LT_0] THEN
    SUBGOAL_THEN (--`defloat(float(0,1,0)) = (0,1,0)`--) SUBST1_TAC THENL [
      REWRITE_TAC[GSYM float_tybij] THEN REWRITE_TAC[is_valid, float_format, expwidth, fracwidth] THEN
      RW_TAC arith_ss [], REWRITE_TAC[valof, float_format, bias, fracwidth, expwidth] THEN
      RW_TAC arith_ss [pow, REAL_MUL_LID] THEN REWRITE_TAC[POW_1, real_div, REAL_MUL_LZERO] THEN
      REWRITE_TAC[REAL_ADD_RID, REAL_MUL_RID] THEN
      UNDISCH_TAC (--`abs(x - (&2:real) / &2 pow 127 * & (2 EXP 23) / (&2 pow 23)) <= inv (&2 pow 150)`--) THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_POW,real_div] THEN RW_TAC arith_ss [ABS_SUB,real_div] THEN
      UNDISCH_TAC (--`abs (x - 2 * inv (2 pow 127) * 2 pow 23 * inv (2 pow 23)) <= inv (2 pow 150)`--) THEN
      ONCE_REWRITE_TAC[REAL_ARITH (--`(a:real) * (b:real) * (c:real) * d = a * b * (c * d)`--)] THEN
      SUBGOAL_THEN (--`((&2:real) pow 23) * inv (&2 pow 23) = (&1:real)`--) (fn th => RW_TAC arith_ss [th,REAL_MUL_RID ]) THEN
      MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC]]);

(*---------------------------*)

val ERROR_BOUND_LEMMA8 = store_thm (
  "ERROR_BOUND_LEMMA8",
  (--`! (x:real). abs(x) < inv(&2 pow 126)
      ==> ?s e f. abs(Val(float(s,e,f)) - x) <= inv(&2 pow 150) /\
      s < 2 /\ f < 2 EXP 23 /\ ((e = 0) \/ (e = 1) /\ (f = 0))`--),
  GEN_TAC THEN DISCH_TAC THEN SUBGOAL_THEN (--`&0:real <= x /\ x < inv(&2 pow 126) \/
  &0 <= ~x /\ ~x < inv(&2 pow 126)`--) MP_TAC THENL [
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC, DISCH_THEN(DISJ_CASES_THEN (MP_TAC o MATCH_MP ERROR_BOUND_LEMMA7))] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`e:num`--) (X_CHOOSE_THEN (--`f:num`--) (CONJUNCTS_THEN ASSUME_TAC))) THENL [
  EXISTS_TAC (--`0:num`--), EXISTS_TAC (--`1:num`--)] THEN EXISTS_TAC (--`e:num`--) THEN EXISTS_TAC (--`f:num`--) THENL [
    RW_TAC arith_ss [], UNDISCH_TAC (--`abs(Val(float ((0:num),(e,f))) - ~x) <= inv ((&2:real) pow 150)`--) THEN REWRITE_TAC[Val] THEN
    SUBGOAL_THEN (--`(defloat(float(0,e,f)) = ((0:num),e,f)) /\ (defloat(float(1,e,f)) = (1,e,f))`--) (CONJUNCTS_THEN SUBST1_TAC) THENL [
      REWRITE_TAC[GSYM float_tybij] THEN REWRITE_TAC[is_valid, float_format] THEN ASM_REWRITE_TAC[bias, expwidth, fracwidth] THEN
      RW_TAC arith_ss [], REWRITE_TAC[valof] THEN COND_CASES_TAC THENL [
        ASM_REWRITE_TAC[POW_1, pow] THEN RW_TAC arith_ss [] THEN ASM_REWRITE_TAC[POW_1,pow] THEN
        REWRITE_TAC[REAL_MUL_LNEG, REAL_NEG_NEG] THEN RW_TAC arith_ss [REAL_MUL_LID] THEN
        UNDISCH_TAC (--`abs (1 * (2 / 2 pow bias float_format) * (& f / 2 pow fracwidth float_format) - ~x) <= inv (2 pow 150)`--) THEN
        REAL_ARITH_TAC, ASM_REWRITE_TAC[POW_1, pow] THEN RW_TAC arith_ss [] THEN ASM_REWRITE_TAC[POW_1,pow] THEN
        REWRITE_TAC[REAL_MUL_LNEG, REAL_NEG_NEG] THEN RW_TAC arith_ss [REAL_MUL_LID] THEN
        UNDISCH_TAC (--`abs (1 * (2 pow 1 / 2 pow bias float_format) * (1 + 0 / 2 pow fracwidth float_format) - ~x) <= inv (2 pow 150)`--) THEN
        REWRITE_TAC [real_div,REAL_MUL_LZERO,REAL_MUL_RZERO,REAL_ADD_RID,REAL_MUL_RID,POW_1,REAL_MUL_LID] THEN REAL_ARITH_TAC]]]);

(*---------------------------*)

val VALOF_SCALE_UP = store_thm (
  "VALOF_SCALE_UP",
  (--`!s e k f. ~(e = 0) ==> (valof(float_format) (s,e + k,f) = &2 pow k * valof(float_format) (s,e,f))`--),
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[valof, ADD_EQ_0] THEN RW_TAC arith_ss [REAL_POW_ADD, REAL_MUL_AC, real_div]);

(*---------------------------*)

val VALOF_SCALE_DOWN = store_thm (
  "VALOF_SCALE_DOWN",
  (--`! (s:num) (e:num) (k:num) (f:num). k < e ==> (valof(float_format) (s,(e - k):num,f) =
      inv(&2 pow k) * valof(float_format) (s,e,f))`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN SUBGOAL_THEN (--`e:num = (e - k) + k`--) MP_TAC THENL [
    POP_ASSUM MP_TAC THEN RW_TAC arith_ss [],
    DISCH_THEN(fn th => GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    SUBGOAL_THEN (--`~(e - k = (0:num))`--) MP_TAC THENL [
      POP_ASSUM MP_TAC THEN REWRITE_TAC [SUB_EQ_0] THEN RW_TAC arith_ss [SUB_EQ_0],
      DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP VALOF_SCALE_UP th]) THEN
      SUBGOAL_THEN (--`inv(&2 pow k) * &2 pow k = &1`--) (fn th => REWRITE_TAC[REAL_MUL_ASSOC, th, REAL_MUL_LID]) THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN RW_TAC arith_ss [POW_0, REAL_OF_NUM_EQ] THEN MATCH_MP_TAC REAL_POS_NZ THEN
      MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC]]);

(*---------------------------*)

val  REAL_LT_RCANCEL_IMP = store_thm (
  "REAL_LT_RCANCEL_IMP",
  (--`!x y z. &0 < z /\ x * z < y * z ==> x < y`--),
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[REAL_LT_LCANCEL_IMP]);

(*---------------------------*)

val REAL_LE_RCANCEL_IMP = store_thm (
  "REAL_LE_RCANCEL_IMP",
  (--`!x y z. &0 < z /\ x * z <= y * z ==> x <= y`--),
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[REAL_LE_LCANCEL_IMP]);

(*---------------------------*)

val REAL_POW_EQ_0 = store_thm (
  "REAL_POW_EQ_0",
  (--`!x n. (x pow n = &0) = (x = &0) /\ ~(n = 0)`--),
  GEN_TAC THEN INDUCT_TAC THENL [
  ASM_REWRITE_TAC[NOT_SUC, pow, REAL_ENTIRE] THEN REAL_ARITH_TAC,
  ASM_REWRITE_TAC[NOT_SUC, pow, REAL_ENTIRE] THEN REAL_ARITH_TAC]);

(*---------------------------*)

val REAL_POW_LE_1 = store_thm (
  "REAL_POW_LE_1",
  (--`!n x. (&1:real) <= x ==> (&1:real) <= x pow n`--),
  INDUCT_TAC THENL [
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[pow, REAL_LE_REFL],
    REWRITE_TAC [pow] THEN GEN_TAC THEN
    UNDISCH_TAC (--`!x. 1 <= x ==> 1 <= x pow n`--) THEN
    DISCH_THEN (MP_TAC o SPEC (--`x:real`--)) THEN
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[REAL_ARITH (--`(&1:real) = (&1:real) * (&1:real)`--)] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN UNDISCH_TAC (--`1 <= x ==> 1 <= x pow n`--) THEN
    RW_TAC arith_ss [] THEN REAL_ARITH_TAC]);

(*---------------------------*)

val REAL_POW_MONO = store_thm (
  "REAL_POW_MONO",
  (--`!(m:num) (n:num) (x:real). &1 <= x /\ m <= n ==> x pow m <= x pow n`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[LESS_EQ_EXISTS ] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:num`--) SUBST1_TAC) THEN REWRITE_TAC[REAL_POW_ADD] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL_IMP THEN
  CONJ_TAC THENL [
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`&1`--) THEN RW_TAC arith_ss [REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[], MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]]);

(*-------------------------------------------------------*)

val ERROR_BOUND_BIG1 = store_thm (
  "ERROR_BOUND_BIG1",
  (--`! x k. 2 pow k <= abs x /\ abs x < 2 pow SUC k /\ abs x < threshold float_format ==>
  ?a. Finite a /\ abs (Val a - x) <= 2 pow k / 2 pow 24`--),
  let val lemma = REAL_ARITH (--`abs(a - b) <= c:real ==> abs(a) <= abs(b) + c`--) in
  REPEAT STRIP_TAC THEN MP_TAC(SPEC (--`(x:real) / (&2:real) pow k`--) ERROR_BOUND_LEMMA5) THEN
  W(C SUBGOAL_THEN MP_TAC o lhand o lhand o snd) THENL [
    REWRITE_TAC[ABS_DIV, REAL_ABS_POW, REAL_ABS_NUM] THEN CONJ_TAC THENL [
      HO_MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC (--`(&2:real) pow (k:num)`--) THEN CONJ_TAC THENL [
        HO_MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC, REWRITE_TAC[REAL_MUL_LID, real_div, GSYM REAL_MUL_ASSOC] THEN
        UNDISCH_TAC (--`(&2:real) pow (k:num) <= abs(x:real)`--) THEN HO_MATCH_MP_TAC(TAUT (`(a = b) ==> a ==> b`)) THEN
        AP_TERM_TAC THEN RW_TAC arith_ss [ABS_MUL] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        ONCE_REWRITE_TAC[REAL_ARITH (--`(a:real) * (b:real) * (c:real) = a * (b * c)`--)] THEN AP_TERM_TAC THEN
        SUBGOAL_THEN (--`(&0:real) <= inv(&2 pow k)`--) (fn th => ASM_REWRITE_TAC [abs,th]) THENL [
          HO_MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC [REAL_OF_NUM_POW] THEN REWRITE_TAC [REAL_OF_NUM_LE] THEN
          RW_TAC arith_ss [], CONV_TAC SYM_CONV THEN HO_MATCH_MP_TAC REAL_MUL_LINV THEN
          HO_MATCH_MP_TAC REAL_POS_NZ THEN HO_MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC]],
      HO_MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC (--`(&2:real) pow k`--) THEN CONJ_TAC THENL [
        HO_MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC, REWRITE_TAC[REAL_MUL_LID, real_div, GSYM REAL_MUL_ASSOC] THEN
        UNDISCH_TAC (--`abs(x:real) < (&2:real) pow (SUC (k:num))`--) THEN REWRITE_TAC[pow] THEN
        HO_MATCH_MP_TAC(TAUT (`(a = b) ==> a ==> b`)) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN RW_TAC arith_ss [ABS_MUL] THEN
        ONCE_REWRITE_TAC[REAL_ARITH (--`(a:real) * (b:real) * (c:real) = a * (b * c)`--)] THEN AP_TERM_TAC THEN
        SUBGOAL_THEN (--`(&0:real) <= inv(&2 pow k)`--) (fn th => ASM_REWRITE_TAC [abs,th]) THENL [
          HO_MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC [REAL_OF_NUM_POW] THEN REWRITE_TAC [REAL_OF_NUM_LE] THEN
          RW_TAC arith_ss [], CONV_TAC SYM_CONV THEN HO_MATCH_MP_TAC REAL_MUL_LINV THEN
          HO_MATCH_MP_TAC REAL_POS_NZ THEN HO_MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC]]],
    DISCH_THEN(fn th => REWRITE_TAC[th]) THEN DISCH_THEN(X_CHOOSE_THEN (--`s:num`--) MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN (--`e:num`--) MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN (--`f:num`--) MP_TAC) THEN STRIP_TAC THENL [
      EXISTS_TAC (--`float(s,e + k,f)`--) THEN
      SUBGOAL_THEN (--`Finite(float(s,e + k,f)) /\ is_valid(float_format)(s,e + k,f)`--) STRIP_ASSUME_TAC THENL [
        MATCH_MP_TAC ISFINITE_LEMMA THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[bias, float_format, fracwidth, expwidth] THEN
        RW_TAC arith_ss [] THEN SUBGOAL_THEN (--`(k:num) < 128`--) (fn th => MP_TAC th) THENL [
          RW_TAC arith_ss [GSYM NOT_LESS_EQUAL] THEN DISCH_TAC THEN
          MP_TAC(SPECL [(--`128:num`--), (--`k:num`--), (--`(&2:real)`--)] REAL_POW_MONO) THEN RW_TAC arith_ss [] THENL [
            REWRITE_TAC[REAL_NOT_LE] THEN REAL_ARITH_TAC, REWRITE_TAC[REAL_NOT_LE] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
            EXISTS_TAC (--`abs(x):real`--) THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
            EXISTS_TAC (--`threshold(float_format)`--) THEN ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[threshold, float_format, bias, expwidth, fracwidth, emax] THEN
            RW_TAC arith_ss [] THEN SUBGOAL_THEN (--`254:num = 127 + 127`--) (fn th => REWRITE_TAC[th,POW_ADD ]) THENL [
              RW_TAC arith_ss [], REWRITE_TAC [real_div] THEN ONCE_REWRITE_TAC [REAL_ARITH
              (--`(a:real) * (b:real) * (c:real) * (d:real) = a * (b * c) * d`--)] THEN SUBGOAL_THEN
              (--`((&2:real) pow 127) * inv (&2 pow 127) = (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_RID ]) THENL [
                MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN
                REAL_ARITH_TAC, REWRITE_TAC [REAL_SUB_LDISTRIB] THEN RW_TAC arith_ss [ADD1] THEN
                SUBGOAL_THEN (--`127:num = 103 + 24`--) (fn th => REWRITE_TAC[th,POW_ADD ]) THENL [
                  RW_TAC arith_ss [], ONCE_REWRITE_TAC[REAL_ARITH (--`(a:real) * (b:real) * (c:real) = a * (b * c)`--)] THEN
                  REWRITE_TAC [real_div]  THEN SUBGOAL_THEN (--`((&2:real) pow 24) * inv (&2 pow 24) =
                  (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_RID ]) THENL [
                    MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN
                    REAL_ARITH_TAC, REWRITE_TAC [RRRC2]]]]]],
          RW_TAC arith_ss []],
        CONJ_TAC THENL [
          ASM_REWRITE_TAC[], REWRITE_TAC[Val] THEN FIRST_ASSUM(SUBST1_TAC o GEN_REWRITE_RULE I [float_tybij]) THEN
          SUBGOAL_THEN (--`~(e:num = 0)`--) (fn th => REWRITE_TAC[MATCH_MP VALOF_SCALE_UP th]) THENL [
            ASM_REWRITE_TAC[bias, float_format, expwidth] THEN RW_TAC arith_ss [], MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
            EXISTS_TAC (--`inv(&2 pow k)`--) THEN CONJ_TAC THENL [
              REWRITE_TAC [REAL_LT_INV_EQ] THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC,
              SUBGOAL_THEN (--`!x:real. inv(&2 pow k) * abs(x) = abs(inv(&2 pow k) * x)`--) (fn th => REWRITE_TAC[th]) THENL [
                REWRITE_TAC[REAL_ABS_MUL, REAL_ABS_INV, REAL_ABS_POW, REAL_ABS_NUM],
                REWRITE_TAC[REAL_SUB_LDISTRIB, REAL_MUL_ASSOC, real_div] THEN
                SUBGOAL_THEN (--`inv(&2 pow k) * (&2 pow k) = &1`--) (fn th => REWRITE_TAC[th]) THENL [
                  MATCH_MP_TAC REAL_MUL_LINV THEN MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN
                  REAL_ARITH_TAC, REWRITE_TAC[REAL_MUL_LID] THEN UNDISCH_TAC (--`abs (Val (float ((s:num),((e:num),(f:num)))) -
                  (x:real) / (&2:real) pow (k:num)) <= inv ((&2:real) pow (24:num))`--) THEN REWRITE_TAC[Val] THEN
                  SUBGOAL_THEN (--`defloat (float (s,e,f)) = (s,e,f)`--) SUBST1_TAC THENL [
                    REWRITE_TAC[GSYM float_tybij] THEN REWRITE_TAC[is_valid, expwidth, fracwidth, float_format] THEN
                    ASM_REWRITE_TAC[] THEN REWRITE_TAC[bias, expwidth, float_format] THEN RW_TAC arith_ss [],
                    RW_TAC arith_ss [real_div, REAL_MUL_AC]]]]]]]],
        ASM_CASES_TAC (--`(e:num) + (k:num) < 255:num`--) THENL [
          EXISTS_TAC (--`float(s,e + k,f)`--) THEN SUBGOAL_THEN (--`Finite(float(s,e + k,f)) /\
          is_valid(float_format)(s,e + k,f)`--) STRIP_ASSUME_TAC THENL [
            MATCH_MP_TAC ISFINITE_LEMMA THEN ASM_REWRITE_TAC[], CONJ_TAC THENL [
              ASM_REWRITE_TAC[], REWRITE_TAC[Val] THEN FIRST_ASSUM(SUBST1_TAC o GEN_REWRITE_RULE I [float_tybij]) THEN
              SUBGOAL_THEN (--`~(e:num = 0)`--) (fn th => REWRITE_TAC[MATCH_MP VALOF_SCALE_UP th]) THENL [
                ASM_REWRITE_TAC[bias, float_format, expwidth] THEN RW_TAC arith_ss [], MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
                EXISTS_TAC (--`inv(&2 pow k)`--) THEN CONJ_TAC THENL [
                  REWRITE_TAC [REAL_LT_INV_EQ] THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC,
                  SUBGOAL_THEN (--`!x. inv(&2 pow k) * abs(x) = abs(inv(&2 pow k) * x)`--) (fn th => REWRITE_TAC[th]) THENL [
                    REWRITE_TAC[REAL_ABS_MUL, REAL_ABS_INV, REAL_ABS_POW, REAL_ABS_NUM],
                    REWRITE_TAC[REAL_SUB_LDISTRIB, REAL_MUL_ASSOC, real_div] THEN
                    SUBGOAL_THEN (--`inv(&2 pow k) * (&2 pow k) = &1`--) (fn th => REWRITE_TAC[th]) THENL [
                    MATCH_MP_TAC REAL_MUL_LINV THEN MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN
                    REAL_ARITH_TAC, REWRITE_TAC[REAL_MUL_LID] THEN UNDISCH_TAC (--`abs (Val (float ((s:num),((e:num),(f:num)))) -
                    (x:real) / (&2:real) pow (k:num)) <= inv ((&2:real) pow (24:num))`--) THEN REWRITE_TAC[Val] THEN
                    SUBGOAL_THEN (--`defloat (float (s,e,f)) = (s,e,f)`--) SUBST1_TAC THENL [
                    REWRITE_TAC[GSYM float_tybij] THEN
                    REWRITE_TAC[is_valid, expwidth, fracwidth, float_format] THEN
                    ASM_REWRITE_TAC[] THEN
                    REWRITE_TAC[bias, expwidth, float_format] THEN
                    RW_TAC arith_ss [],
                    RW_TAC arith_ss [real_div, REAL_MUL_AC]]]]]]]],
          SUBGOAL_THEN (--`(&2:real) pow (k:num) < threshold(float_format)`--) MP_TAC THENL [
            MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`abs(x:real)`--) THEN ASM_REWRITE_TAC[],
            REWRITE_TAC[FLOAT_THRESHOLD_EXPLICIT] THEN DISCH_TAC THEN
            SUBGOAL_THEN (--`(&2:real) pow (k:num) < &2 pow (128:num)`--) ASSUME_TAC THENL [
              MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`(&340282356779733661637539395458142568448):real`--) THEN
              ASM_REWRITE_TAC[] THEN REWRITE_TAC[RRRC3],
              MP_TAC(SPECL [(--`128:num`--), (--`k:num`--), (--`&2:real`--)] REAL_POW_MONO) THEN
              ASM_REWRITE_TAC[GSYM REAL_NOT_LT,DE_MORGAN_THM,NOT_LESS_EQUAL] THEN
              DISCH_TAC THEN SUBGOAL_THEN (--`k:num = 127:num`--) ASSUME_TAC THENL [
                UNDISCH_TAC (--`(&2:real) < (&1:real) \/ (k:num) < (128:num)`--) THEN
                UNDISCH_TAC (--`~((e:num) + (k:num) < (255:num))`--) THEN ASM_REWRITE_TAC[bias, float_format, expwidth] THEN
                RW_TAC arith_ss [] THENL [
                  UNDISCH_TAC (--`(&2:real) < (&1:real)`--) THEN REAL_ARITH_TAC, UNDISCH_TAC (--` (k:num) < (128:num)`--) THEN
                  UNDISCH_TAC (--` ~((k:num) + (128:num) < (255:num))`--) THEN RW_TAC arith_ss []],
                UNDISCH_TAC (--`abs(x:real) < threshold(float_format)`--) THEN CONV_TAC CONTRAPOS_CONV THEN
                DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[FLOAT_THRESHOLD_EXPLICIT] THEN ASM_REWRITE_TAC[REAL_NOT_LT] THEN
                UNDISCH_TAC (--`abs(Val(float((s:num),(e:num),(f:num))) - (x:real) /
                (&2:real) pow (k:num)) <= inv ((&2:real) pow (24:num))`--) THEN
                ASM_REWRITE_TAC[] THEN REWRITE_TAC[bias, expwidth, float_format] THEN RW_TAC arith_ss [ADD1] THEN
                UNDISCH_TAC (--`abs (Val (float ((s:num),(128:num),(0:num))) - (x:real) /
                (&2:real) pow (127:num)) <= inv ((&2:real) pow (24:num))`--) THEN
                DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN SUBGOAL_THEN (--`Finite(float(s,128,0)) /\
                is_valid(float_format)(s,128,0)`--) STRIP_ASSUME_TAC THENL [
                  MATCH_MP_TAC ISFINITE_LEMMA THEN ASM_REWRITE_TAC[] THEN RW_TAC arith_ss [], REWRITE_TAC[Val] THEN
                  FIRST_ASSUM(SUBST1_TAC o GEN_REWRITE_RULE I [float_tybij]) THEN REWRITE_TAC[float_format, valof] THEN
                  RW_TAC arith_ss [REAL_ABS_MUL, REAL_ABS_POW, ABS_NEG,REAL_ABS_NUM, POW_ONE, REAL_MUL_LID,bias, fracwidth, expwidth,real_div,
                  REAL_MUL_LZERO,REAL_ADD_RID, REAL_ABS_NUM, REAL_MUL_RID,GSYM REAL_LE_SUB_RADD, GSYM REAL_LE_SUB_RADD] THEN
                  UNDISCH_TAC (--`(&2:real) pow (128:num) * abs (inv ((&2:real) pow (127:num))) - inv ((&2:real) pow (24:num)) <=
                  abs (x:real) * abs (inv ((&2:real) pow (127:num)))`--) THEN
                  SUBGOAL_THEN (--`abs (inv (2 pow 127)) = inv (2 pow 127)`--) (fn th => REWRITE_TAC[th]) THENL [
                    REWRITE_TAC[ABS_REFL] THEN MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC [REAL_OF_NUM_POW] THEN
                    REWRITE_TAC [REAL_OF_NUM_LE] THEN RW_TAC arith_ss [],
                    SUBGOAL_THEN (--`2 pow 128 * inv (2 pow 127) - inv (2 pow 24) <= abs x * inv (2 pow 127) =
                    (2 pow 128 * inv (2 pow 127) - inv (2 pow 24)) * (2 pow 127) <= abs x * inv (2 pow 127) *
                    (2 pow 127)`--) (fn th => REWRITE_TAC[th]) THENL [
                      MATCH_MP_TAC (GSYM REAL_LE_RMUL) THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC,
                      REWRITE_TAC [REAL_SUB_RDISTRIB] THEN ONCE_REWRITE_TAC[REAL_ARITH (--`(a:real) * (b:real) * (c:real) = a * (b * c)`--)] THEN
                      SUBGOAL_THEN (--`(inv (&2 pow 127) * (&2:real) pow 127) = (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_RID ]) THENL [
                        MATCH_MP_TAC REAL_MUL_LINV THEN MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC,
                        SUBGOAL_THEN (--`127:num = 24 +103`--) (fn th => REWRITE_TAC[th,POW_ADD ]) THENL [
                          RW_TAC arith_ss [], ONCE_REWRITE_TAC[REAL_ARITH (--`(a:real) * ((b:real) * (c:real)) = (a * b) * c`--)] THEN
                          SUBGOAL_THEN (--`inv (&2 pow 24) * ((&2:real) pow 24) = (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID ]) THENL [
                            MATCH_MP_TAC REAL_MUL_LINV THEN MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC,
                            RW_TAC arith_ss [RRRC4]]]]]]]]]]]]] end );

(*-----------------------------------------------*)

val ERROR_BOUND_BIG = store_thm (
  "ERROR_BOUND_BIG",
  (--`! (k:num) (x:real). (&2:real) pow k <= abs(x) /\ abs(x) < &2 pow (SUC k) /\
      abs(x) < threshold(float_format) ==> abs(error(x)) <= &2 pow (k:num) / (&2:real) pow (24:num)`--),
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN (--`?a. Finite(a) /\ abs(Val(a) - x) <= (&2:real) pow k / &2 pow 24`--) CHOOSE_TAC THENL [
    ALL_TAC, HO_MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`abs(Val(a) - (x:real))`--) THEN
    ASM_REWRITE_TAC[] THEN HO_MATCH_MP_TAC ERROR_AT_WORST_LEMMA THEN RW_TAC arith_ss []] THEN
  RW_TAC arith_ss [ERROR_BOUND_BIG1]);

(*-----------------------------------------------*)

val REAL_LE_INV2 = store_thm (
  "REAL_LE_INV2",
  (--`!x y. (&0:real) < x /\ x <= y ==> inv(y) <= inv(x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  ASM_CASES_TAC (--`x:real = y`--) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
  ASM_REWRITE_TAC[]);

(*-----------------------------------------------*)

val ERROR_BOUND_SMALL1 = store_thm (
  "ERROR_BOUND_SMALL1",
  (--`! x k. inv (2 pow SUC k) <= abs x /\ abs x < inv (2 pow k) /\ k < 126 ==>
      ?a. Finite a /\ abs (Val a - x) <= inv (2 pow SUC k * 2 pow 24)`--),
  REPEAT STRIP_TAC THEN MP_TAC(SPEC (--`x * &2 pow (SUC k)`--) ERROR_BOUND_LEMMA5) THEN
  W(C SUBGOAL_THEN MP_TAC o lhand o lhand o snd) THENL [
    REWRITE_TAC[ABS_DIV, REAL_ABS_POW, REAL_ABS_NUM] THEN CONJ_TAC THENL [
      MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC (--`inv(&2 pow (SUC k))`--) THEN CONJ_TAC THENL [
        REWRITE_TAC [REAL_LT_INV_EQ] THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC,
        REWRITE_TAC[REAL_MUL_LID, real_div, GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC (--`abs(x:real)`--) THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        REWRITE_TAC[REAL_ABS_MUL, REAL_ABS_POW, REAL_ABS_NUM] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC REAL_MUL_RINV THEN REWRITE_TAC[REAL_POW_EQ_0, REAL_OF_NUM_EQ] THEN RW_TAC arith_ss []],
      MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC (--`inv(&2 pow (SUC k))`--) THEN CONJ_TAC THENL [
        REWRITE_TAC [REAL_LT_INV_EQ] THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC,
        REWRITE_TAC[REAL_ABS_MUL, REAL_ABS_POW, REAL_ABS_NUM] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
        SUBGOAL_THEN (--`&2 pow SUC k * inv(&2 pow SUC k) = &1`--) SUBST1_TAC THENL [
          MATCH_MP_TAC REAL_MUL_RINV THEN REWRITE_TAC[REAL_POW_EQ_0, REAL_OF_NUM_EQ] THEN
          REWRITE_TAC[REAL_MUL_RID, pow, REAL_INV_MUL] THEN RW_TAC arith_ss [],
          REWRITE_TAC [REAL_MUL_RID] THEN RW_TAC arith_ss [pow] THEN
          SUBGOAL_THEN (--`inv (&2 * &2 pow k) = inv (&2) * inv (&2 pow k)`--) (fn th => ASM_REWRITE_TAC [th]) THENL [
            MATCH_MP_TAC REAL_INV_MUL THEN CONJ_TAC THENL [
              REAL_ARITH_TAC, MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC],
            ONCE_REWRITE_TAC[REAL_ARITH (--`(a:real) * ((b:real) * (c:real)) = ((a * b) * c)`--)] THEN
            SUBGOAL_THEN (--`(&2:real) * inv (&2) = (&1:real)`--) (fn th => ASM_REWRITE_TAC [th,REAL_MUL_LID]) THEN
            MATCH_MP_TAC REAL_MUL_RINV THEN REAL_ARITH_TAC]]]],
    DISCH_THEN(fn th => REWRITE_TAC[th]) THEN DISCH_THEN(X_CHOOSE_THEN (--`s:num`--) MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN (--`e:num`--) MP_TAC) THEN DISCH_THEN(X_CHOOSE_THEN (--`f:num`--) MP_TAC) THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN EXISTS_TAC (--`float(s,e - SUC k,f)`--) THEN
    SUBGOAL_THEN (--`Finite(float(s,e - SUC k,f)) /\ is_valid(float_format)(s,e - SUC k,f)`--) STRIP_ASSUME_TAC THENL [
      MATCH_MP_TAC ISFINITE_LEMMA THEN ASM_REWRITE_TAC[] THEN FIRST_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL [
        ASM_REWRITE_TAC[bias, float_format, expwidth] THEN RW_TAC arith_ss [],
        ASM_REWRITE_TAC[bias, float_format, expwidth] THEN RW_TAC arith_ss []],
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[Val] THEN FIRST_ASSUM(SUBST1_TAC o GEN_REWRITE_RULE I [float_tybij]) THEN
      SUBGOAL_THEN (--`SUC k < e`--) (fn th => REWRITE_TAC[MATCH_MP VALOF_SCALE_DOWN th]) THENL [
        FIRST_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL [
          ASM_REWRITE_TAC[bias, float_format, expwidth] THEN RW_TAC arith_ss [],
          UNDISCH_TAC (--`(k:num) < (126:num)`--) THEN RW_TAC arith_ss [bias, float_format, expwidth]],
        MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC (--`&2 pow (SUC k)`--) THEN CONJ_TAC THENL [
          MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC,
          SUBGOAL_THEN (--`!x. &2 pow (SUC k) * abs(x) = abs(&2 pow (SUC k) * x)`--) (fn th => REWRITE_TAC[th]) THENL [
            REWRITE_TAC[REAL_ABS_MUL, REAL_ABS_INV,REAL_ABS_POW, REAL_ABS_NUM],
            REWRITE_TAC[REAL_SUB_LDISTRIB, REAL_MUL_ASSOC, REAL_INV_MUL] THEN
            SUBGOAL_THEN (--`&2 pow (SUC k) * inv(&2 pow (SUC k)) = &1`--) SUBST1_TAC THENL [
              MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN
              REAL_ARITH_TAC, REWRITE_TAC[REAL_MUL_LID] THEN
              UNDISCH_TAC (--`abs(Val(float((s:num),(e:num),(f:num))) - (x:real) * (&2:real) pow SUC (k:num)) <= inv ((&2:real) pow (24:num))`--) THEN
              REWRITE_TAC[Val] THEN SUBGOAL_THEN (--`defloat(float(s,e,f)) = (s,e,f)`--) (fn th => RW_TAC arith_ss [th, REAL_MUL_AC]) THENL [
                REWRITE_TAC[GSYM float_tybij] THEN REWRITE_TAC[is_valid, emax, bias, expwidth, fracwidth, float_format] THEN
                ASM_REWRITE_TAC[] THEN FIRST_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL [
                  ASM_REWRITE_TAC[bias, expwidth, float_format] THEN RW_TAC arith_ss [],
                  ASM_REWRITE_TAC[bias, expwidth, float_format] THEN RW_TAC arith_ss []],
                SUBGOAL_THEN (--`inv (&2 pow SUC k * &2 pow 24) = inv (&2 pow SUC k) * inv (&2 pow 24)`--) (fn th => ASM_REWRITE_TAC [th]) THENL [
                  MATCH_MP_TAC REAL_INV_MUL THEN CONJ_TAC THENL [
                    MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC,
                    MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC],
                  ONCE_REWRITE_TAC[REAL_ARITH (--`(a:real) * ((b:real) * (c:real)) = ((a * b) * c)`--)] THEN
                  SUBGOAL_THEN (--`&2 pow SUC k * inv (2 pow SUC k) = (&1:real)`--) (fn th => ASM_REWRITE_TAC [th,REAL_MUL_LID]) THEN
                  MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC],
                SUBGOAL_THEN (--`inv (&2 pow SUC k * &2 pow 24) = inv (&2 pow SUC k) * inv (&2 pow 24)`--) (fn th => ASM_REWRITE_TAC [th]) THENL [
                  MATCH_MP_TAC REAL_INV_MUL THEN CONJ_TAC THENL [
                    MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC,
                    MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC],
                  ONCE_REWRITE_TAC[REAL_ARITH (--`(a:real) * ((b:real) * (c:real)) = ((a * b) * c)`--)] THEN
                  SUBGOAL_THEN (--`&2 pow SUC k * inv (2 pow SUC k) = (&1:real)`--) (fn th => ASM_REWRITE_TAC [th,REAL_MUL_LID]) THEN
                  MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC]]]]]]]]);

(*-------------------------------------*)

val ERROR_BOUND_SMALL = store_thm (
  "ERROR_BOUND_SMALL",
  (--`! (k:num) (x:real). inv(&2 pow (SUC k)) <= abs(x) /\ abs(x) < inv(&2 pow k) /\ k < 126
      ==> abs(error(x)) <= inv(&2 pow (SUC k) * &2 pow 24)`--),
  REPEAT STRIP_TAC THEN SUBGOAL_THEN (--`?a. Finite(a) /\ abs(Val(a) - x) <= inv(&2 pow (SUC k) * &2 pow 24)`--) CHOOSE_TAC THENL [
    RW_TAC arith_ss [ERROR_BOUND_SMALL1], MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (--`abs(Val(a) - x)`--) THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ERROR_AT_WORST_LEMMA THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (--`inv(&2 pow k)`--) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`inv(&1)`--) THEN CONJ_TAC THENL [
      MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_LT_01] THEN MATCH_MP_TAC REAL_POW_LE_1 THEN
      REAL_ARITH_TAC, REWRITE_TAC[threshold, float_format, bias, emax] THEN REWRITE_TAC[expwidth, fracwidth] THEN
      CONV_TAC REDUCE_CONV THEN SUBGOAL_THEN (--`254:num = 127 + 127 `--) (fn th => REWRITE_TAC[th,POW_ADD,real_div ]) THENL [
        RW_TAC arith_ss [], REWRITE_TAC[REAL_ARITH (--`a:real  * b * c * d = a  * (b * c) * d`--)] THEN
        SUBGOAL_THEN (--`2 pow 127 * inv (2 pow 127) = &1:real`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID,REAL_MUL_RID]) THENL [
          MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC, RW_TAC arith_ss [REAL_SUB_LDISTRIB,ADD1] THEN
          SUBGOAL_THEN (--`127:num = 103 + 24 `--) (fn th => REWRITE_TAC[th,POW_ADD,real_div ]) THENL [
            RW_TAC arith_ss [], REWRITE_TAC[REAL_ARITH (--`a:real  * b * c = a  * (b * c)`--)] THEN
            SUBGOAL_THEN (--`2 pow 24 * inv (2 pow 24) = &1:real`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID,REAL_MUL_RID]) THENL [
              MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC, REWRITE_TAC[RRRC5]]]]]]]);

(*-----------------------------------------------*)

val ERROR_BOUND_TINY = store_thm (
  "ERROR_BOUND_TINY",
  (--`! x:real. abs(x) < inv(&2 pow (126:num)) ==> abs(error(x)) <= inv(&2 pow (150:num))`--),
  REPEAT STRIP_TAC THEN SUBGOAL_THEN (--`?a. Finite(a) /\ abs(Val(a) - x) <= inv(&2 pow 150:num)`--)
  CHOOSE_TAC THENL [
    FIRST_ASSUM(MP_TAC o MATCH_MP ERROR_BOUND_LEMMA8) THEN DISCH_THEN(X_CHOOSE_THEN (--`s:num`--) MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN (--`e:num`--) MP_TAC) THEN DISCH_THEN(X_CHOOSE_THEN (--`f:num`--) MP_TAC) THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN EXISTS_TAC (--`float(s,e,f)`--) THEN
    SUBGOAL_THEN (--`Finite(float(s,e,f)) /\ is_valid(float_format)(s,e,f)`--) STRIP_ASSUME_TAC THENL [
      MATCH_MP_TAC ISFINITE_LEMMA THEN ASM_REWRITE_TAC[] THEN FIRST_ASSUM DISJ_CASES_TAC THENL [
        RW_TAC arith_ss [], RW_TAC arith_ss []],
      ASM_REWRITE_TAC[Val]],
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`abs(Val(a) - x)`--) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ERROR_AT_WORST_LEMMA THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC (--`inv(&2 pow 126)`--) THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[threshold, float_format, bias, emax] THEN
    REWRITE_TAC[expwidth, fracwidth] THEN CONV_TAC REDUCE_CONV THEN
    SUBGOAL_THEN (--`254:num = 127 + 127 `--) (fn th => REWRITE_TAC[th,POW_ADD,real_div ]) THENL [
      RW_TAC arith_ss [], REWRITE_TAC[REAL_ARITH (--`a:real  * b * c * d = a  * (b * c) * d`--)] THEN
      SUBGOAL_THEN (--`2 pow 127 * inv (2 pow 127) = &1:real`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID,REAL_MUL_RID]) THENL [
        MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC, RW_TAC arith_ss [REAL_SUB_LDISTRIB,ADD1] THEN
        SUBGOAL_THEN (--`127:num = 103 + 24 `--) (fn th => REWRITE_TAC[th,POW_ADD,real_div ]) THEN RW_TAC arith_ss [] THEN
        REWRITE_TAC[REAL_ARITH (--`a:real  * b * c = a  * (b * c)`--)] THEN
        SUBGOAL_THEN (--`2 pow 24 * inv (2 pow 24) = &1:real`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID,REAL_MUL_RID]) THENL [
          MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC,
          RW_TAC arith_ss [REAL_MUL_SYM ,GSYM pow,ADD1,GSYM REAL_POW_ADD ] THEN
          SUBGOAL_THEN (--` inv (2 pow 126) < 2 pow 128 - 2 pow 103 = 2 pow 126 * inv (2 pow 126) <
          2 pow 126 * (2 pow 128 - 2 pow 103) `--) (fn th => REWRITE_TAC[th]) THENL [
            MATCH_MP_TAC (GSYM REAL_LT_LMUL) THEN REWRITE_TAC [REAL_OF_NUM_POW] THEN REWRITE_TAC [REAL_OF_NUM_LT] THEN
            REWRITE_TAC[num_CONV(--`2:num`--),ZERO_LESS_EXP ],
            SUBGOAL_THEN (--`((&2:real) pow (126:num) * inv ((&2:real) pow 126) = &1 :real)`--) (fn th => REWRITE_TAC[th, REAL_MUL_LID]) THENL [
              MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC, REWRITE_TAC [REAL_SUB_LDISTRIB, GSYM POW_ADD] THEN
              CONV_TAC REDUCE_CONV THEN REWRITE_TAC [RRRC10]]]]]]]);

(* ------------------------------------------------------------------------- *)
(* Stronger versions not requiring exact location of the interval.           *)
(* ------------------------------------------------------------------------- *)

val ERROR_BOUND_NORM_STRONG = store_thm (
  "ERROR_BOUND_NORM_STRONG",
  (--`! (x:real) (j:num). abs(x) < threshold(float_format) /\ abs(x) < ((&2:real) pow (SUC j) / &2 pow (126:num))
      ==> abs(error(x)) <= &2 pow j / &2 pow (150:num)`--),
  GEN_TAC THEN INDUCT_TAC THENL [
    REWRITE_TAC[pow, POW_1] THEN
    REWRITE_TAC [real_div, REAL_MUL_LID, REAL_MUL_RID] THEN DISCH_TAC THEN
    ASM_CASES_TAC (--`abs(x:real) < inv(&2 pow (126:num))`--) THENL [
      MATCH_MP_TAC ERROR_BOUND_TINY THEN ASM_REWRITE_TAC[],MP_TAC(SPECL [(--`125:num`--), (--`x:real`--)] ERROR_BOUND_SMALL) THEN
      REWRITE_TAC[GSYM REAL_POW_ADD] THEN REWRITE_TAC[ADD1] THEN
      SUBGOAL_THEN (--`125 + 1 + 24 = 150 : num`--) (fn th => REWRITE_TAC[th]) THENL [
        RW_TAC arith_ss [], DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LT] THEN
        RW_TAC arith_ss [] THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LT] THEN
        UNDISCH_TAC (--`abs (x:real) < (&2:real) * inv ((&2:real) pow (126:num))`--) THEN
        SUBGOAL_THEN (--`&2 * inv (2 pow 126) = inv (2 pow 125)`--) (fn th => ASM_REWRITE_TAC [th]) THEN
        SUBGOAL_THEN (--`126 = 1 + 125 : num`--) (fn th => REWRITE_TAC[th]) THENL [
          RW_TAC arith_ss [], REWRITE_TAC[POW_ADD] THEN SUBGOAL_THEN (--`inv ((&2:real) pow 1 * (&2:real) pow 125) =
          inv ((&2:real) pow 1) * inv ((&2:real) pow 125)`--) (fn th => REWRITE_TAC[th]) THENL [
            MATCH_MP_TAC REAL_INV_MUL THEN CONJ_TAC THENL [
              MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC,
              MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC],
            ONCE_REWRITE_TAC[REAL_ARITH (--`(a:real) * ((b:real) * c) = (a * b) * c`--)] THEN
            SUBGOAL_THEN (--`((&2:real) * inv (&2 pow 1)) = (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID ]) THEN
            REWRITE_TAC [POW_1] THEN MATCH_MP_TAC REAL_MUL_RINV THEN REAL_ARITH_TAC]]]],
    STRIP_TAC THEN ASM_CASES_TAC (--`abs x < (&2:real) pow SUC (j:num) / (&2:real) pow (126:num)`--) THENL [
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`(&2:real) pow (j:num) / (&2:real) pow (150:num)`--) THEN
      CONJ_TAC THENL [
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[], REWRITE_TAC[real_div] THEN
        SUBGOAL_THEN (--`(&2:real pow (j:num)) * (inv ((&2:real) pow (150:num))) <= (&2:real pow SUC (j:num)) * (inv ((&2:real) pow (150:num))) =
        ((&2:real) pow (j:num)) <= ((&2:real) pow SUC (j:num))`--) (fn th => REWRITE_TAC[th]) THENL [
          MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [REAL_LT_INV_EQ] THEN REWRITE_TAC [RRRC6],
          MATCH_MP_TAC REAL_POW_MONO THEN RW_TAC arith_ss [] THEN REAL_ARITH_TAC]],
      ASM_CASES_TAC (--`(j:num) <= (124:num)`--) THENL [
        MP_TAC(SPECL [(--`(124:num) - (j:num)`--), (--`x:real`--)] ERROR_BOUND_SMALL) THEN REWRITE_TAC[GSYM REAL_POW_ADD] THEN
        SUBGOAL_THEN (--`inv ((&2:real) pow (SUC ((124:num) - (j:num)) + (24:num))) =
        (&2:real) pow SUC (j:num) / (&2:real) pow (150:num)`--) SUBST1_TAC THENL [
          SUBGOAL_THEN (--`SUC((124:num) - (j:num)) + (24:num) = (150:num) - SUC (j:num)`--) SUBST1_TAC THENL [
            ASM_REWRITE_TAC [SUB_LEFT_SUC] THEN UNDISCH_TAC (--`(j:num) <= (124:num)`--) THEN RW_TAC arith_ss [],
            SUBGOAL_THEN (--`(150:num) = ((150:num) - SUC (j:num)) + SUC (j:num)`--) MP_TAC THENL [
              UNDISCH_TAC (--`(j:num) <= (124:num)`--) THEN RW_TAC arith_ss [],
              DISCH_THEN(fn th => GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THEN REWRITE_TAC[REAL_POW_ADD] THEN
              REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
              SUBGOAL_THEN (--`inv ((&2:real) pow ((150:num) - SUC (j:num)) * (&2:real) pow SUC (j:num)) =
              inv ((&2:real) pow ((150:num) - SUC (j:num))) * inv ((&2:real) pow SUC (j:num))`--) (fn th => REWRITE_TAC[th]) THENL [
                MATCH_MP_TAC REAL_INV_MUL THEN CONJ_TAC THENL [
                  MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC, MATCH_MP_TAC REAL_POS_NZ THEN
                  MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC],
                REWRITE_TAC[REAL_ARITH (--`a:real  * b * c = a  * (b * c)`--)] THEN
                SUBGOAL_THEN (--`inv ((&2:real) pow SUC (j:num)) * (&2:real) pow SUC (j:num) =
                (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_RID]) THEN MATCH_MP_TAC REAL_MUL_LINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC]]],
          DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL [
            MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`(&2:real) pow SUC (j:num) / (&2:real) pow (126:num)`--) THEN
            ASM_REWRITE_TAC[] THEN SUBGOAL_THEN (--`(126:num) = ((124:num) - (j:num)) + SUC(SUC (j:num))`--) SUBST1_TAC THENL [
              UNDISCH_TAC (--`(j:num) <= (124:num)`--) THEN RW_TAC arith_ss [], REWRITE_TAC[REAL_POW_ADD, pow, REAL_INV_MUL, real_div] THEN
              ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN CONJ_TAC THENL [
                MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[REAL_ARITH (--`a:real  * (b * c) = (a  * b) * c`--)] THEN
                SUBGOAL_THEN (--`inv ((&2:real) pow ((124:num) - (j:num)) * (&2:real) * (&2:real) * (&2:real) pow (j:num)) =
                inv ((&2:real) pow ((124:num) - (j:num)) * (&2:real)) * inv ((&2:real) * (&2:real) pow (j:num))`--) (fn th => REWRITE_TAC[th]) THENL [
                  REWRITE_TAC[REAL_ARITH (--`a:real * b * c * d = (a  * b) * (c * d)`--)] THEN MATCH_MP_TAC REAL_INV_MUL THEN CONJ_TAC THENL [
                    RW_TAC arith_ss [REAL_ENTIRE] THENL [
                      MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC, REAL_ARITH_TAC],
                    RW_TAC arith_ss [REAL_ENTIRE] THENL [
                      REAL_ARITH_TAC, MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC]],
                  REWRITE_TAC[REAL_ARITH (--`a:real * b * c * d = a  * (b * (c * d))`--)] THEN
                  SUBGOAL_THEN (--`inv ((&2:real) * (&2:real) pow (j:num)) * ((&2:real) * (&2:real) pow (j:num)) =
                  (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_RID]) THEN MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC[GSYM pow] THEN
                  MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC],
                REWRITE_TAC[REAL_ARITH (--`a:real * b * c * d = (a  * b) * (c * d)`--)] THEN
                SUBGOAL_THEN (--`inv (((&2:real) pow ((124:num) - (j:num)) * (&2:real)) * ((&2:real) * (&2:real) pow (j:num))) =
                inv (((&2:real) pow ((124:num) - (j:num)) * (&2:real))) * inv ((&2:real) * (&2:real) pow (j:num))`--) (fn th => REWRITE_TAC[th]) THENL [
                  MATCH_MP_TAC REAL_INV_MUL THEN CONJ_TAC THENL [
                    RW_TAC arith_ss [REAL_ENTIRE] THENL [
                      MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC, REAL_ARITH_TAC],
                    RW_TAC arith_ss [REAL_ENTIRE] THENL [
                      REAL_ARITH_TAC, MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC]],
                  REWRITE_TAC[REAL_ARITH (--`a:real * b * c = a  * (b * c)`--)] THEN
                  SUBGOAL_THEN (--`(inv ((&2:real) * (&2:real) pow (j:num)) * ((&2:real) * (&2:real) pow (j:num))) =
                  (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_RID]) THENL [
                    MATCH_MP_TAC REAL_MUL_LINV THEN RW_TAC arith_ss [REAL_ENTIRE] THENL [
                      REAL_ARITH_TAC, MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC],
                    SUBGOAL_THEN (--`inv ((&2:real) pow ((124:num) - (j:num)) * (&2:real)) =
                    (&2:real) pow SUC (j:num) / (&2:real) pow (126:num)`--) SUBST1_TAC THENL [
                      SUBGOAL_THEN (--`(&2:real) pow ((124:num) - (j:num)) * (&2:real) =
                      (&2:real) * (&2:real) pow ((124:num) - (j:num))`--) SUBST1_TAC THENL [
                        RW_TAC arith_ss [REAL_MUL_SYM], RW_TAC arith_ss [GSYM pow] THEN SUBGOAL_THEN (--`(126:num) =
                        ((126:num) - SUC (j:num)) + SUC (j:num)`--) MP_TAC THENL [
                          UNDISCH_TAC (--`(j:num) <= (124:num)`--) THEN RW_TAC arith_ss [],
                          DISCH_THEN(fn th => GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THEN REWRITE_TAC[REAL_POW_ADD] THEN
                          REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
                          SUBGOAL_THEN (--`inv ((&2:real) pow ((126:num) - SUC (j:num)) * (&2:real) pow SUC (j:num)) =
                          inv ((&2:real) pow ((126:num) - SUC (j:num))) * inv ((&2:real) pow SUC (j:num))`--) (fn th => REWRITE_TAC[th]) THENL [
                            MATCH_MP_TAC REAL_INV_MUL THEN CONJ_TAC THENL [
                              MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC,
                              MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC],
                            REWRITE_TAC[REAL_ARITH (--`a:real  * b * c = a  * (b * c)`--)] THEN
                            SUBGOAL_THEN (--`inv ((&2:real) pow SUC (j:num)) * (&2:real) pow SUC (j:num) =
                            (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_RID]) THENL [
                              MATCH_MP_TAC REAL_MUL_LINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC,
                              SUBGOAL_THEN (--`SUC((124:num) - (j:num)) = (126:num) - SUC (j:num)`--) SUBST1_TAC THENL [
                                ASM_REWRITE_TAC [SUB_LEFT_SUC] THEN UNDISCH_TAC (--`(j:num) <= (124:num)`--) THEN
                                RW_TAC arith_ss [], RW_TAC arith_ss []]]]]],
                      ASM_REWRITE_TAC [real_lte] THEN REWRITE_TAC[REAL_ARITH (--`a:real * (b * (c * d)) = (a  * b) * (c * d)`--)] THEN
                      SUBGOAL_THEN (--`inv (((&2:real) pow ((124:num) - (j:num)) * (&2:real)) * ((&2:real) * (&2:real) pow (j:num))) =
                      inv (((&2:real) pow ((124:num) - (j:num)) * (&2:real))) * inv ((&2:real) * (&2:real) pow (j:num))`--)
                      (fn th => REWRITE_TAC[th]) THENL [
                        MATCH_MP_TAC REAL_INV_MUL THEN CONJ_TAC THENL [
                          RW_TAC arith_ss [REAL_ENTIRE] THENL [
                            MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC, REAL_ARITH_TAC],
                          RW_TAC arith_ss [REAL_ENTIRE] THENL [
                            REAL_ARITH_TAC, MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC]],
                        REWRITE_TAC[REAL_ARITH (--`a:real * b * c = a  * (b * c)`--)] THEN
                        SUBGOAL_THEN (--`(inv ((&2:real) * (&2:real) pow (j:num)) * ((&2:real) * (&2:real) pow (j:num))) =
                        (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_RID]) THENL [
                          MATCH_MP_TAC REAL_MUL_LINV THEN RW_TAC arith_ss [REAL_ENTIRE] THENL [
                            REAL_ARITH_TAC, MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC],
                          SUBGOAL_THEN (--`inv ((&2:real) pow ((124:num) - (j:num)) * (&2:real)) =
                          (&2:real) pow SUC (j:num) / (&2:real) pow (126:num)`--) SUBST1_TAC THENL [
                            SUBGOAL_THEN (--`(&2:real) pow ((124:num) - (j:num)) * (&2:real) =
                            (&2:real) * (&2:real) pow ((124:num) - (j:num))`--) SUBST1_TAC THENL [
                              RW_TAC arith_ss [REAL_MUL_SYM], RW_TAC arith_ss [GSYM pow] THEN
                              SUBGOAL_THEN (--`(126:num) = ((126:num) - SUC (j:num)) + SUC (j:num)`--) MP_TAC THENL [
                                UNDISCH_TAC (--`(j:num) <= (124:num)`--) THEN RW_TAC arith_ss [],
                                DISCH_THEN(fn th => GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
                                REWRITE_TAC[REAL_POW_ADD] THEN REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
                                SUBGOAL_THEN (--`inv ((&2:real) pow ((126:num) - SUC (j:num)) * (&2:real) pow SUC (j:num)) =
                                inv ((&2:real) pow ((126:num) - SUC (j:num))) * inv ((&2:real) pow SUC (j:num))`--) (fn th => REWRITE_TAC[th]) THENL [
                                  MATCH_MP_TAC REAL_INV_MUL THEN CONJ_TAC THENL [
                                    MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC,
                                    MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC],
                                  REWRITE_TAC[REAL_ARITH (--`a:real  * b * c = a  * (b * c)`--)] THEN
                                  SUBGOAL_THEN (--`inv ((&2:real) pow SUC (j:num)) * (&2:real) pow SUC (j:num) =
                                  (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_RID]) THENL [
                                    MATCH_MP_TAC REAL_MUL_LINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC,
                                    SUBGOAL_THEN (--`SUC((124:num) - (j:num)) = (126:num) - SUC (j:num)`--) SUBST1_TAC THENL [
                                      ASM_REWRITE_TAC [SUB_LEFT_SUC] THEN UNDISCH_TAC (--`(j:num) <= (124:num)`--) THEN
                                      RW_TAC arith_ss [],RW_TAC arith_ss []]]]]], ASM_REWRITE_TAC [real_lte]]]]]]]]],
            MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`(&2:real) pow SUC(SUC (j:num)) / (&2:real) pow (126:num)`--) THEN
            ASM_REWRITE_TAC[] THEN SUBGOAL_THEN (--`(126:num) = ((124:num) - (j:num)) + SUC(SUC (j:num))`--) SUBST1_TAC THENL [
              UNDISCH_TAC (--`(j:num) <= (124:num)`--) THEN RW_TAC arith_ss [], REWRITE_TAC[real_div, REAL_INV_MUL, REAL_POW_ADD] THEN
              MATCH_MP_TAC REAL_EQ_IMP_LE THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
              REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN SUBGOAL_THEN (--`inv ((&2:real) pow ((124:num) - (j:num)) * (&2:real) pow ( SUC (SUC (j:num)))) =
              inv ((&2:real) pow ((124:num) - (j:num))) * inv ((&2:real) pow (SUC (SUC (j:num))))`--) (fn th => REWRITE_TAC[th]) THENL [
                MATCH_MP_TAC REAL_INV_MUL THEN CONJ_TAC THENL [
                  RW_TAC arith_ss [REAL_ENTIRE] THEN MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC,
                  MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC],
                REWRITE_TAC[REAL_ARITH (--`a:real  * b * c = a  * (b * c)`--)] THEN
                SUBGOAL_THEN (--`inv ((&2:real) pow SUC (SUC (j:num))) * (&2:real) pow SUC (SUC (j:num)) =
                (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_RID]) THEN MATCH_MP_TAC REAL_MUL_LINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC]],
            RW_TAC arith_ss []]],
        MP_TAC(SPECL [(--`SUC (j:num) - (126:num)`--), (--`x:real`--)] ERROR_BOUND_BIG) THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN (--`(&2:real) pow (SUC (j:num) - (126:num)) / (&2:real) pow (24:num) =
        (&2:real) pow SUC (j:num) / (&2:real) pow (150:num)`--) SUBST1_TAC THENL [
          SUBGOAL_THEN (--`?(d:num). (j:num) = (125:num) + (d:num)`--) (CHOOSE_THEN SUBST1_TAC) THENL [
            EXISTS_TAC (--`(j:num) - (125:num)`--) THEN UNDISCH_TAC (--`~((j:num) <= (124:num))`--) THEN RW_TAC arith_ss [],
            SUBGOAL_THEN (--`SUC((125:num) + (d:num)) - (126:num) = (d:num)`--) SUBST1_TAC THENL [
              RW_TAC arith_ss [], SUBGOAL_THEN (--`SUC((125:num) + (d:num)) = (126:num) + (d:num)`--) SUBST1_TAC THENL [
                RW_TAC arith_ss [], ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[REAL_POW_ADD, real_div] THEN
                REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN SUBGOAL_THEN (--`(150:num) = (126:num) + (24:num)`--) SUBST1_TAC THENL [
                  RW_TAC arith_ss [], REWRITE_TAC[POW_ADD] THEN SUBGOAL_THEN (--`inv ((&2:real) pow ((126:num)) * (&2:real) pow (24:num)) =
                  inv ((&2:real) pow (126:num)) * inv ((&2:real) pow (24:num))`--) (fn th => REWRITE_TAC[th]) THENL [
                    MATCH_MP_TAC REAL_INV_MUL THEN CONJ_TAC THENL [
                      RW_TAC arith_ss [REAL_ENTIRE] THEN MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN
                      REAL_ARITH_TAC, MATCH_MP_TAC REAL_POS_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC],
                    REWRITE_TAC[REAL_ARITH (--`a:real  * (b * c) = (a * b) * c`--)] THEN
                    SUBGOAL_THEN (--`(&2:real) pow (126:num) * inv ((&2:real) pow (126:num)) =
                    (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID]) THEN MATCH_MP_TAC REAL_MUL_RINV THEN
                    MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC]]]]],
          DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL [
            MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`(&2:real) pow SUC (j:num) / (&2:real) pow (126:num)`--) THEN
            ASM_REWRITE_TAC[real_lte ] THEN SUBGOAL_THEN (--`?(d:num). (j:num) = (125:num) + (d:num)`--) (CHOOSE_THEN SUBST1_TAC) THENL [
              EXISTS_TAC (--`(j:num) - (125:num)`--) THEN UNDISCH_TAC (--`~((j:num) <= (124:num))`--) THEN RW_TAC arith_ss [],
              SUBGOAL_THEN (--`SUC((125:num) + (d:num)) - (126:num) = (d:num)`--) SUBST1_TAC THENL [
                RW_TAC arith_ss [], SUBGOAL_THEN (--`SUC((125:num) + (d:num)) = (126:num) + (d:num)`--) SUBST1_TAC THENL [
                  RW_TAC arith_ss [], ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[REAL_POW_ADD, real_div] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
                  SUBGOAL_THEN (--`(&2:real) pow (126:num) * inv ((&2:real) pow (126:num)) =
                  (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_RID]) THENL [
                    MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC, RW_TAC arith_ss [] THEN REAL_ARITH_TAC]]]],
            MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`(&2:real) pow SUC(SUC (j:num)) / (&2:real) pow (126:num)`--) THEN
            ASM_REWRITE_TAC[] THEN SUBGOAL_THEN (--`?(d:num). (j:num) = (125:num) + (d:num)`--) (CHOOSE_THEN SUBST1_TAC) THENL [
            EXISTS_TAC (--`(j:num) - (125:num)`--) THEN UNDISCH_TAC (--`~((j:num) <= (124:num))`--) THEN RW_TAC arith_ss [],
            SUBGOAL_THEN (--`SUC(SUC ((125:num) + (d:num)) - (126:num)) = SUC (d:num)`--) SUBST1_TAC THENL [
              RW_TAC arith_ss [], SUBGOAL_THEN (--`SUC(SUC ((125:num) + (d:num))) = SUC (d:num) + (126:num)`--) SUBST1_TAC THENL [
                RW_TAC arith_ss [], REWRITE_TAC[REAL_POW_ADD, real_div] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
                MATCH_MP_TAC REAL_EQ_IMP_LE THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN AP_TERM_TAC THEN
                MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC]]]]]]]]);

(* ------------------------------------------------------------------------- *)
(* "1 + Epsilon" property (relative error bounding).                         *)
(* ------------------------------------------------------------------------- *)

val normalizes = new_definition (
  "normalizes",
  (--`normalizes (x:real) = ((inv ((&2:real) pow (bias float_format - 1)) <= abs (x)) /\ abs (x) < threshold(float_format))`--));

(* ------------------------------------------------------------------------- *)

val THRESHOLD_MUL_LT = store_thm (
  "THRESHOLD_MUL_LT",
  (--`threshold float_format * &2 pow 126 < (&2 pow (2 EXP 126))`--),
  REWRITE_TAC [threshold,float_format] THEN RW_TAC arith_ss [emax,bias,fracwidth,expwidth] THEN
  REWRITE_TAC[real_div] THEN SUBGOAL_THEN (--`254:num = 127 + 127`--) (fn th => REWRITE_TAC[th,REAL_MUL_RID]) THENL [
    RW_TAC arith_ss [], REWRITE_TAC [REAL_POW_ADD] THEN
    REWRITE_TAC[REAL_ARITH (--`a:real  * b * c * d * e = a  * (b * c) * d * e`--)] THEN
    SUBGOAL_THEN (--`(&2:real pow 127 * inv (2 pow 127)) =  &1:real`--) (fn th => REWRITE_TAC[th,REAL_MUL_RID,REAL_MUL_LID]) THENL [
      MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC,
      REWRITE_TAC[REAL_ARITH (--`a:real * b * c = a * (b * c)`--)] THEN REWRITE_TAC[REAL_SUB_RDISTRIB] THEN
      REWRITE_TAC[REAL_SUB_LDISTRIB] THEN REWRITE_TAC[GSYM pow] THEN REWRITE_TAC[GSYM POW_ADD] THEN
      SUBGOAL_THEN (--`SUC 23 = 24`--) (fn th => REWRITE_TAC[th]) THENL [
        RW_TAC arith_ss [], SUBGOAL_THEN (--`126:num = 24 + 102`--) (fn th => REWRITE_TAC[th]) THENL [
          RW_TAC arith_ss [], REWRITE_TAC [REAL_POW_ADD] THEN REWRITE_TAC[REAL_ARITH (--`a:real * (b * (c * d)) = a * (b * c) * d`--)] THEN
          SUBGOAL_THEN (--`(inv (2 pow 24) * &2:real pow 24) =  &1:real`--) (fn th => REWRITE_TAC[th,REAL_MUL_RID,REAL_MUL_LID]) THENL [
            MATCH_MP_TAC REAL_MUL_LINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC, REWRITE_TAC [GSYM REAL_POW_ADD] THEN
            RW_TAC arith_ss [] THEN MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (--`&2 pow 254`--) THEN CONJ_TAC THENL [
              RW_TAC arith_ss [RRRC7], MATCH_MP_TAC REAL_POW_MONO_LT THEN CONJ_TAC THENL [
                REAL_ARITH_TAC, RW_TAC arith_ss []]]]]]]]);

(* ------------------------------------------------------------------------- *)

val THRESHOLD_LT_POW_INV = store_thm (
  "THRESHOLD_LT_POW_INV",
  (--`340282356779733661637539395458142568448 < 2 pow 254 * inv (2 pow 126)`--),
  SUBGOAL_THEN (--`340282356779733661637539395458142568448 < 2 pow 254 * inv (2 pow 126) =
  340282356779733661637539395458142568448 * 2 pow 126 < 2 pow 254 * inv (2 pow 126) * 2 pow 126`--) (fn th => REWRITE_TAC[th]) THENL [
    MATCH_MP_TAC (GSYM REAL_LT_RMUL) THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC,
    REWRITE_TAC[REAL_ARITH (--`a:real * b * c = a * (b * c)`--)] THEN
    SUBGOAL_THEN (--`(inv (2 pow 126) * &2:real pow 126) =  &1:real`--) (fn th => REWRITE_TAC[th,REAL_MUL_RID,REAL_MUL_LID]) THENL [
      MATCH_MP_TAC REAL_MUL_LINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC, REWRITE_TAC[RRRC11]]]);

(* ------------------------------------------------------------------------- *)

val LT_THRESHOLD_LT_POW_INV = store_thm (
  "LT_THRESHOLD_LT_POW_INV",
  (--`!x:real. x < threshold (8,23) ==> x < 2 pow (emax (8,23) - 1) / 2 pow 126`--),
  RW_TAC arith_ss [FLOAT_THRESHOLD_EXPLICIT,(GSYM float_format),emax,expwidth,real_div] THEN
  MP_TAC THRESHOLD_LT_POW_INV THEN UNDISCH_TAC (--`x < 340282356779733661637539395458142568448`--) THEN
  REWRITE_TAC[TAUT (`(a ==> b ==> c) = (a /\ b ==> c)`)] THEN REWRITE_TAC [REAL_LT_TRANS]);

(* ------------------------------------------------------------------------- *)

val REAL_POS_IN_BINADE = store_thm (
  "REAL_POS_IN_BINADE",
  (--`! (x:real). normalizes (x:real) /\ ((&0:real) <= x) ==> ?(j:num). j <= (emax float_format - 2) /\
      ((&2 pow j) / (&2 pow 126)) <= x /\ x < ((&2 pow (SUC j:num)) / (&2 pow 126))`--),
  GEN_TAC THEN REWRITE_TAC[normalizes,bias,expwidth,float_format] THEN RW_TAC arith_ss [abs] THEN
  MP_TAC(SPEC (--`\ (n:num). ((&2:real) pow n) / (&2:real) pow 126 <= (x:real)`--) (EXISTS_GREATEST)) THEN
  REWRITE_TAC[] THEN W(C SUBGOAL_THEN MP_TAC o lhs o lhand o snd) THENL [
  CONJ_TAC THENL [
    EXISTS_TAC (--`0:num`--) THEN RW_TAC arith_ss [REAL_MUL_LID , pow, real_div], EXISTS_TAC (--`(2:num) EXP 126`--) THEN
    X_GEN_TAC (--`n:num`--) THEN DISCH_TAC THEN REWRITE_TAC [REAL_OF_NUM_POW] THEN RW_TAC arith_ss [GSYM real_lt] THEN
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC (--`inv((&2:real) pow 126)`--) THEN RW_TAC arith_ss [] THENL [
      MATCH_MP_TAC REAL_INV_POS THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC,
      SUBGOAL_THEN (--`inv (&2 pow 126) * x < inv (& 2 pow 126) * (& (2 ** n) / &85070591730234615865843651857942052864) =
      x < (& (2 ** n) / &85070591730234615865843651857942052864)`--) (fn th => REWRITE_TAC[th]) THENL [
        MATCH_MP_TAC REAL_LT_LMUL THEN MATCH_MP_TAC REAL_INV_POS THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC,
        SUBGOAL_THEN (--`x < & (2 ** n) / &85070591730234615865843651857942052864 =
        x * &85070591730234615865843651857942052864 < & (2 ** n)`--) (fn th => REWRITE_TAC[th]) THENL [
          SUBGOAL_THEN (--`x < & (2 ** n) / &85070591730234615865843651857942052864 = x * &85070591730234615865843651857942052864 <
          (& (2 ** n) / &85070591730234615865843651857942052864) * &85070591730234615865843651857942052864`--) (fn th => REWRITE_TAC[th]) THENL [
            MATCH_MP_TAC (GSYM REAL_LT_RMUL) THEN REAL_ARITH_TAC, REWRITE_TAC[real_div] THEN
            REWRITE_TAC[REAL_ARITH (--`a:real  * b * c = a  * (b * c)`--)] THEN
            SUBGOAL_THEN (--`(inv (&85070591730234615865843651857942052864) * &85070591730234615865843651857942052864) = &1`--)
            (fn th => REWRITE_TAC[th,REAL_MUL_RID]) THEN MATCH_MP_TAC REAL_MUL_LINV THEN REAL_ARITH_TAC],
          MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (--`(&2 pow (2 EXP 126))`--) THEN CONJ_TAC THENL [
            SUBGOAL_THEN (--`(&85070591730234615865843651857942052864) = &2 pow 126`--) (fn th => REWRITE_TAC[th]) THENL [
              REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_EQ] THEN RW_TAC arith_ss [], UNDISCH_TAC (--`x:real < threshold (8,23)`--) THEN
              SUBGOAL_THEN (--`x < threshold (8,23) = x * &2 pow 126 < threshold (8,23) * &2 pow 126`--) (fn th => REWRITE_TAC[th]) THENL [
                MATCH_MP_TAC (GSYM REAL_LT_RMUL) THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC, MP_TAC THRESHOLD_MUL_LT THEN
                REWRITE_TAC[TAUT (`(a ==> b ==> c) = (b /\ a ==> c)`)] THEN REWRITE_TAC [float_format] THEN REAL_ARITH_TAC]],
            REWRITE_TAC [GSYM REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_POW_MONO_LT THEN CONJ_TAC THENL [
              REAL_ARITH_TAC, ASM_REWRITE_TAC [GSYM GREATER_DEF]]]]]]],
  DISCH_THEN(fn th => REWRITE_TAC[th]) THEN DISCH_THEN(X_CHOOSE_THEN (--`n:num`--) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN DISCH_THEN(MP_TAC o SPEC (--`SUC n`--)) THEN
  REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN EXISTS_TAC (--`n:num`--) THEN REPEAT CONJ_TAC THENL [
    RW_TAC arith_ss [emax,expwidth] THEN UNDISCH_TAC (--`(\n:num. 2 pow n / 2 pow 126 <= x) n`--) THEN
    RW_TAC arith_ss [] THEN UNDISCH_TAC (--`&2 pow n / &2 pow 126 <= x`--) THEN UNDISCH_TAC (--`x < threshold (8,23)`--) THEN
    DISCH_THEN(MP_TAC o MATCH_MP LT_THRESHOLD_LT_POW_INV) THEN REWRITE_TAC[TAUT (`(a ==> b ==> c) = (b /\ a ==> c)`)] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LET_TRANS) THEN SUBGOAL_THEN (--`2 pow n / 2 pow 126 < 2 pow (emax (8,23) - 1) / 2 pow 126 =
    2 pow n < 2 pow (emax (8,23) - 1)`--) (fn th => REWRITE_TAC[th,REAL_MUL_RID]) THENL [
      REWRITE_TAC [real_div] THEN SUBGOAL_THEN (--`2 pow n * inv (2 pow 126) < 2 pow (emax (8,23) - 1) * inv (2 pow 126) =
      (2 pow n * inv (2 pow 126)) * 2 pow 126 < (2 pow (emax (8,23) - 1) * inv (2 pow 126)) * 2 pow 126`--) (fn th => REWRITE_TAC[th,REAL_MUL_RID]) THENL [
        MATCH_MP_TAC (GSYM REAL_LT_RMUL) THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC,
        REWRITE_TAC[REAL_ARITH (--`a:real  * b * c = a  * (b * c)`--)] THEN
        SUBGOAL_THEN (--`(inv (2 pow 126) * 2 pow 126) = &1`--) (fn th => REWRITE_TAC[th,REAL_MUL_RID]) THEN MATCH_MP_TAC REAL_MUL_LINV THEN
        MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC],
      RW_TAC arith_ss [] THEN SUBGOAL_THEN (--`253:num = 254 - 1`--) (fn th => REWRITE_TAC[th]) THENL [
        RW_TAC arith_ss [], MATCH_MP_TAC SUB_LESS_OR THEN UNDISCH_TAC (--`2 pow n < 2 pow (emax (8,23) - 1)`--) THEN
        ASM_CASES_TAC (--`(n:num) < (254:num)`--) THENL [
          RW_TAC arith_ss [], RW_TAC arith_ss [] THEN UNDISCH_TAC (--`~((n:num) < 254)`--) THEN REWRITE_TAC [GSYM real_lte] THEN
          REWRITE_TAC [GSYM REAL_OF_NUM_LT] THEN REWRITE_TAC [GSYM real_lte] THEN REWRITE_TAC [REAL_OF_NUM_LE] THEN
          RW_TAC arith_ss [] THEN RW_TAC arith_ss [] THEN MATCH_MP_TAC REAL_POW_MONO THEN RW_TAC arith_ss [emax,expwidth] THEN
          REAL_ARITH_TAC]]],
    UNDISCH_TAC (--`(\n. 2 pow n / 2 pow 126 <= x) n`--) THEN RW_TAC arith_ss [],
    UNDISCH_TAC (--`SUC n > n ==> ~(\n. 2 pow n / 2 pow 126 <= x) (SUC n)`--) THEN RW_TAC arith_ss [REAL_NOT_LE]]]);

(* ------------------------------------------------------------------------- *)

val REAL_NEG_IN_BINADE = store_thm (
  "REAL_NEG_IN_BINADE",
  (--`! (x:real). normalizes (x:real) /\ ((&0:real) <= ~x) ==> ?(j:num). j <= (emax float_format - 2) /\
      ((&2 pow j) / (&2 pow 126)) <= ~x /\ ~x < ((&2 pow (SUC j:num)) / (&2 pow 126))`--),
  GEN_TAC THEN SUBGOAL_THEN (--`normalizes (x:real) = normalizes (~x:real)`--) (fn th => REWRITE_TAC[th]) THENL [
    RW_TAC arith_ss [normalizes,ABS_NEG ], STRIP_TAC THEN MP_TAC REAL_POS_IN_BINADE THEN
    DISCH_THEN (MP_TAC o SPEC (--`(~x:real)`--)) THEN RW_TAC arith_ss []]);

(* ------------------------------------------------------------------------- *)

val REAL_IN_BINADE = store_thm (
  "REAL_IN_BINADE",
  (--`! (x:real). normalizes (x:real) ==> ?(j:num). j <= (emax float_format - 2) /\
      ((&2 pow j) / (&2 pow 126)) <= abs x /\ abs x < ((&2 pow (SUC j:num)) / (&2 pow 126))`--),
  GEN_TAC THEN ASM_CASES_TAC (--`(&0:real) <= x`--) THENL [
    RW_TAC arith_ss [abs] THEN MP_TAC REAL_POS_IN_BINADE THEN DISCH_THEN (MP_TAC o SPEC (--`(x:real)`--)) THEN
    RW_TAC arith_ss [], RW_TAC arith_ss [abs] THEN MP_TAC REAL_NEG_IN_BINADE THEN
    DISCH_THEN (MP_TAC o SPEC (--`(x:real)`--)) THEN
    SUBGOAL_THEN (--`((&0:real) <= ~x) = ~((&0:real) <= x)`--) (fn th => REWRITE_TAC[th]) THENL [
      RW_TAC arith_ss [REAL_NEG_GE0 ] THEN UNDISCH_TAC (--`~(0 <= x)`--) THEN RW_TAC arith_ss [REAL_NOT_LE ] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN RW_TAC arith_ss [], RW_TAC arith_ss []]]);

(* ------------------------------------------------------------------------- *)

val ERROR_BOUND_NORM_STRONG_NORMALIZE = store_thm (
  "ERROR_BOUND_NORM_STRONG_NORMALIZE",
  (--`! (x:real). normalizes (x:real) ==> ?(j:num). abs(error(x)) <= &2 pow j / &2 pow (150:num)`--),
  GEN_TAC THEN STRIP_TAC THEN MP_TAC REAL_IN_BINADE THEN DISCH_THEN (MP_TAC o SPEC (--`(x:real)`--)) THEN
  RW_TAC arith_ss [] THEN EXISTS_TAC (--`j:num`--) THEN MP_TAC ERROR_BOUND_NORM_STRONG THEN
  DISCH_THEN (MP_TAC o SPECL [(--`x:real`--), (--`j:num`--)]) THEN UNDISCH_TAC (--`normalizes x`--) THEN
  REWRITE_TAC[normalizes] THEN RW_TAC arith_ss []);

(* ------------------------------------------------------------------------- *)

val RELATIVE_ERROR_POS = store_thm (
  "RELATIVE_ERROR_POS",
  (--`! (x:real). normalizes (x:real) /\ ((&0:real) < x) ==> ? (e:real). abs(e) <= ((&1:real) / &2 pow (24:num)) /\
      (Val (float (round float_format To_nearest x)) = x * ((&1:real) + e))`--),
  GEN_TAC THEN RW_TAC arith_ss [] THEN MP_TAC (SPECL [(--`x:real`--)] REAL_IN_BINADE) THEN
  RW_TAC arith_ss [] THEN UNDISCH_TAC (--`normalizes x`--) THEN RW_TAC arith_ss [normalizes] THEN
  MP_TAC (SPECL [(--`x:real`--),(--`j:num`--)] ERROR_BOUND_NORM_STRONG) THEN RW_TAC arith_ss [] THEN
  UNDISCH_TAC (--`2 pow j / 2 pow 126 <= abs x`--) THEN REWRITE_TAC [real_div] THEN
  SUBGOAL_THEN (--`2 pow j * inv (2 pow 126) <= abs x = inv (abs x) <= inv (2 pow j * inv (2 pow 126))`--) (fn th => REWRITE_TAC[th]) THENL [
  REWRITE_TAC [REAL_ARITH (--`2 pow j * inv (2 pow 126) <= abs x = (2 pow j * inv (2 pow 126)) <= (&1:real) * abs x`--)] THEN
  SUBGOAL_THEN (--`(2 pow j * inv (2 pow 126)) <= 1 * abs x = (2 pow j * inv (2 pow 126)) / abs x <= (&1:real)`--) (fn th => REWRITE_TAC[th]) THENL [
  MATCH_MP_TAC (GSYM REAL_LE_LDIV_EQ) THEN REWRITE_TAC [GSYM ABS_NZ] THEN UNDISCH_TAC (--`0 < x`--) THEN REAL_ARITH_TAC,
  REWRITE_TAC [real_div] THEN SUBGOAL_THEN (--`2 pow j * inv (2 pow 126) * inv (abs x) <= 1 = (2 pow 126 * inv (2 pow j)) *
  (2 pow j * inv (2 pow 126) * inv (abs x)) <= (2 pow 126 * inv (2 pow j)) * 1 `--) (fn th => REWRITE_TAC[th]) THENL [
    MATCH_MP_TAC (GSYM REAL_LE_LMUL) THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [
      REWRITE_TAC [REAL_OF_NUM_POW] THEN REWRITE_TAC [REAL_OF_NUM_LT] THEN SUBGOAL_THEN (--`2:num = SUC 1`--) (fn th => REWRITE_TAC[th]) THENL [
        RW_TAC arith_ss [ADD1], RW_TAC arith_ss [ZERO_LESS_EXP]],
      MATCH_MP_TAC REAL_INV_POS THEN REWRITE_TAC [REAL_OF_NUM_POW] THEN REWRITE_TAC [REAL_OF_NUM_LT] THEN
      SUBGOAL_THEN (--`2:num = SUC 1`--) (fn th => REWRITE_TAC[th]) THENL [
        RW_TAC arith_ss [ADD1], RW_TAC arith_ss [ZERO_LESS_EXP]]],
    REWRITE_TAC [REAL_ARITH (--`2 pow 126 * inv (2 pow j) * (2 pow j * inv (2 pow 126) * inv (abs x)) =
    2 pow 126 * (inv (2 pow j) * 2 pow j) * inv (2 pow 126) * inv (abs x)`--)] THEN
    SUBGOAL_THEN (--`(inv (2 pow j) * 2 pow j) = (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID,REAL_MUL_RID]) THENL [
      MATCH_MP_TAC REAL_MUL_LINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC,
      REWRITE_TAC [REAL_ARITH (--`(&2:real) pow 126 * (inv (2 pow 126) * inv (abs x)) = (2 pow 126 * inv (2 pow 126)) * inv (abs x)`--)] THEN
      SUBGOAL_THEN (--`2 pow 126 * inv (2 pow 126) = (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID,REAL_MUL_RID]) THENL [
        MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC, REWRITE_TAC [REAL_ARITH (--`2 pow j * inv (2 pow 126) =
        inv (2 pow 126) * 2 pow j`--)] THEN SUBGOAL_THEN (--`inv (inv (2 pow 126) * 2 pow j) =
        inv (inv (2 pow 126)) * inv (2 pow j)`--) (fn th => REWRITE_TAC[th]) THENL [
          MATCH_MP_TAC REAL_INV_MUL THEN CONJ_TAC THENL [
            MATCH_MP_TAC REAL_INV_NZ THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC, MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC],
          SUBGOAL_THEN (--`inv (inv (2 pow 126)) = 2 pow 126`--) (fn th => REWRITE_TAC[th]) THEN MATCH_MP_TAC REAL_INVINV THEN
          MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC]]]]],
  UNDISCH_TAC (--`abs (error x) <= 2 pow j / 2 pow 150`--) THEN REWRITE_TAC[TAUT (`(a ==> b ==> c) = (a /\ b ==> c)`)] THEN
  SUBGOAL_THEN (--`(&0:real) <= inv (abs x)`--) MP_TAC THENL [
    REWRITE_TAC [REAL_LE_INV_EQ] THEN REWRITE_TAC [ABS_POS], REWRITE_TAC[TAUT (`(a ==> (b /\ c) ==> d) = (a /\ b /\ c ==> d)`)] THEN
    MP_TAC (SPECL [(--`(error x):real`--)] ABS_POS) THEN REWRITE_TAC[TAUT (`(a ==> (b /\ c /\ d) ==> e) = (a /\ b /\ c /\ d ==> e)`)] THEN
    RW_TAC arith_ss [] THEN MP_TAC (SPECL [(--`abs (error x):real`--), (--`(2 pow j / 2 pow 150):real`--),
    (--`inv (abs x):real`--),(--`(inv (2 pow j * inv (2 pow 126))):real`--)] REAL_LE_MUL2) THEN RW_TAC arith_ss [] THEN
    EXISTS_TAC (--`((error x) * inv x):real`--) THEN CONJ_TAC THENL [
      REWRITE_TAC[REAL_MUL_LID] THEN REWRITE_TAC[ABS_MUL] THEN
      SUBGOAL_THEN (--`abs (inv x) = inv (abs x)`--) (fn th => REWRITE_TAC[th]) THENL [
        MATCH_MP_TAC ABS_INV THEN UNDISCH_TAC (--`0 < x:real`--) THEN REAL_ARITH_TAC,
        UNDISCH_TAC (--`abs (error x) * inv (abs x) <= 2 pow j / 2 pow 150 * inv (2 pow j * inv (2 pow 126))`--) THEN
        SUBGOAL_THEN (--` 2 pow j / 2 pow 150 * inv (2 pow j * inv (2 pow 126)) = inv (2 pow 24)`--) (fn th => REWRITE_TAC[th]) THEN
        REWRITE_TAC[real_div] THEN SUBGOAL_THEN (--`inv (2 pow j * inv (2 pow 126)) =
        inv (2 pow j) * inv (inv (2 pow 126))`--) (fn th => REWRITE_TAC[th]) THENL [
          MATCH_MP_TAC REAL_INV_MUL THEN CONJ_TAC THENL [
            MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC, MATCH_MP_TAC REAL_INV_NZ THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC],
          SUBGOAL_THEN (--`inv (inv (2 pow 126)) = 2 pow 126`--) (fn th => REWRITE_TAC[th]) THENL [
            MATCH_MP_TAC REAL_INVINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC,
            REWRITE_TAC [REAL_ARITH (--`2 pow j * inv (2 pow 150) * (inv (2 pow j) * 2 pow 126) =
            (2 pow j * inv (2 pow j)) * (inv (2 pow 150) * 2 pow 126)`--)] THEN
            SUBGOAL_THEN (--`2 pow j * inv (2 pow j) = (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID,REAL_MUL_RID]) THENL [
              MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC,
              SUBGOAL_THEN (--`(150:num) = 24 + 126`--) (fn th => REWRITE_TAC[th,POW_ADD]) THENL [
                RW_TAC arith_ss [],
                SUBGOAL_THEN (--`inv (2 pow 24 * 2 pow 126) = inv (2 pow 24) * inv (2 pow 126)`--) (fn th => REWRITE_TAC[th]) THENL [
                  MATCH_MP_TAC REAL_INV_MUL THEN CONJ_TAC THENL [
                    MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC, MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC],
                  REWRITE_TAC [REAL_ARITH (--`inv (2 pow 24) * inv (2 pow 126) * 2 pow 126 = inv (2 pow 24) * (inv (2 pow 126) * 2 pow 126)`--)] THEN
                  SUBGOAL_THEN (--`inv (2 pow 126) * 2 pow 126 = (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID,REAL_MUL_RID]) THEN
                  MATCH_MP_TAC REAL_MUL_LINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC]]]]]],
      REWRITE_TAC [error] THEN REWRITE_TAC [REAL_LDISTRIB] THEN REWRITE_TAC [REAL_MUL_RID] THEN REWRITE_TAC [REAL_SUB_LDISTRIB,REAL_SUB_RDISTRIB] THEN
      REWRITE_TAC [REAL_ARITH (--`(x * (Val (float (round float_format To_nearest x)) * inv x) =
      ((x * inv x) * (Val (float (round float_format To_nearest x)))))`--)] THEN
      SUBGOAL_THEN (--`x * inv (x) = (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID,REAL_MUL_RID]) THENL [
        MATCH_MP_TAC REAL_MUL_RINV THEN UNDISCH_TAC (--`0 < x:real`--) THEN REAL_ARITH_TAC, REAL_ARITH_TAC]]]]);

(* ------------------------------------------------------------------------- *)

val RELATIVE_ERROR_NEG = store_thm (
  "RELATIVE_ERROR_NEG",
  (--`! (x:real). normalizes (x:real) /\ (x < (&0:real)) ==> ? (e:real). abs(e) <= ((&1:real) / &2 pow (24:num)) /\
      (Val (float (round float_format To_nearest x)) = x * ((&1:real) + e))`--),
  GEN_TAC THEN RW_TAC arith_ss [] THEN MP_TAC (SPECL [(--`x:real`--)] REAL_IN_BINADE) THEN
  RW_TAC arith_ss [] THEN UNDISCH_TAC (--`normalizes x`--) THEN RW_TAC arith_ss [normalizes] THEN
  MP_TAC (SPECL [(--`x:real`--),(--`j:num`--)] ERROR_BOUND_NORM_STRONG) THEN RW_TAC arith_ss [] THEN
  UNDISCH_TAC (--`2 pow j / 2 pow 126 <= abs x`--) THEN REWRITE_TAC [real_div] THEN
  SUBGOAL_THEN (--`2 pow j * inv (2 pow 126) <= abs x =inv (abs x) <= inv (2 pow j * inv (2 pow 126))`--) (fn th => REWRITE_TAC[th]) THENL [
    REWRITE_TAC [REAL_ARITH (--`2 pow j * inv (2 pow 126) <= abs x = (2 pow j * inv (2 pow 126)) <= (&1:real) * abs x`--)] THEN
    SUBGOAL_THEN (--`(2 pow j * inv (2 pow 126)) <= 1 * abs x = (2 pow j * inv (2 pow 126)) / abs x <= (&1:real)`--) (fn th => REWRITE_TAC[th]) THENL [
      MATCH_MP_TAC (GSYM REAL_LE_LDIV_EQ) THEN REWRITE_TAC [GSYM ABS_NZ] THEN UNDISCH_TAC (--`x < 0`--) THEN REAL_ARITH_TAC,
      REWRITE_TAC [real_div] THEN SUBGOAL_THEN (--`2 pow j * inv (2 pow 126) * inv (abs x) <= 1 = (2 pow 126 * inv (2 pow j)) *
      (2 pow j * inv (2 pow 126) * inv (abs x)) <= (2 pow 126 * inv (2 pow j)) * 1 `--) (fn th => REWRITE_TAC[th]) THENL [
        MATCH_MP_TAC (GSYM REAL_LE_LMUL) THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [
          REWRITE_TAC [REAL_OF_NUM_POW] THEN REWRITE_TAC [REAL_OF_NUM_LT] THEN SUBGOAL_THEN (--`2:num = SUC 1`--) (fn th => REWRITE_TAC[th]) THENL [
            RW_TAC arith_ss [ADD1], RW_TAC arith_ss [ZERO_LESS_EXP]],
          MATCH_MP_TAC REAL_INV_POS THEN REWRITE_TAC [REAL_OF_NUM_POW] THEN REWRITE_TAC [REAL_OF_NUM_LT] THEN
          SUBGOAL_THEN (--`2:num = SUC 1`--) (fn th => REWRITE_TAC[th]) THENL [
            RW_TAC arith_ss [ADD1], RW_TAC arith_ss [ZERO_LESS_EXP]]],
        REWRITE_TAC [REAL_ARITH (--`2 pow 126 * inv (2 pow j) * (2 pow j * inv (2 pow 126) * inv (abs x)) =
        2 pow 126 * (inv (2 pow j) * 2 pow j) * inv (2 pow 126) * inv (abs x)`--)] THEN
        SUBGOAL_THEN (--`(inv (2 pow j) * 2 pow j) = (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID,REAL_MUL_RID]) THENL [
          MATCH_MP_TAC REAL_MUL_LINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC,
          REWRITE_TAC [REAL_ARITH (--`(&2:real) pow 126 * (inv (2 pow 126) * inv (abs x)) = (2 pow 126 * inv (2 pow 126)) * inv (abs x)`--)] THEN
          SUBGOAL_THEN (--`2 pow 126 * inv (2 pow 126) = (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID,REAL_MUL_RID]) THENL [
            MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC,
            REWRITE_TAC [REAL_ARITH (--`2 pow j * inv (2 pow 126) = inv (2 pow 126) * 2 pow j`--)] THEN
            SUBGOAL_THEN (--`inv (inv (2 pow 126) * 2 pow j) = inv (inv (2 pow 126)) * inv (2 pow j)`--) (fn th => REWRITE_TAC[th]) THENL [
              MATCH_MP_TAC REAL_INV_MUL THEN CONJ_TAC THENL [
                MATCH_MP_TAC REAL_INV_NZ THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC, MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC],
              SUBGOAL_THEN (--`inv (inv (2 pow 126)) = 2 pow 126`--) (fn th => REWRITE_TAC[th]) THEN MATCH_MP_TAC REAL_INVINV THEN
              MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC]]]]],
    UNDISCH_TAC (--`abs (error x) <= 2 pow j / 2 pow 150`--) THEN REWRITE_TAC[TAUT (`(a ==> b ==> c) = (a /\ b ==> c)`)] THEN
    SUBGOAL_THEN (--`(&0:real) <= inv (abs x)`--) MP_TAC THENL [
      REWRITE_TAC [REAL_LE_INV_EQ] THEN REWRITE_TAC [ABS_POS], REWRITE_TAC[TAUT (`(a ==> (b /\ c) ==> d) = (a /\ b /\ c ==> d)`)] THEN
      MP_TAC (SPECL [(--`(error x):real`--)] ABS_POS) THEN REWRITE_TAC[TAUT (`(a ==> (b /\ c /\ d) ==> e) = (a /\ b /\ c /\ d ==> e)`)] THEN
      RW_TAC arith_ss [] THEN MP_TAC (SPECL [(--`abs (error x):real`--), (--`(2 pow j / 2 pow 150):real`--),
      (--`inv (abs x):real`--),(--`(inv (2 pow j * inv (2 pow 126))):real`--)] REAL_LE_MUL2) THEN RW_TAC arith_ss [] THEN
      EXISTS_TAC (--`((error x) * inv x):real`--) THEN CONJ_TAC THENL [
        REWRITE_TAC[REAL_MUL_LID] THEN REWRITE_TAC[ABS_MUL] THEN
        SUBGOAL_THEN (--`abs (inv x) = inv (abs x)`--) (fn th => REWRITE_TAC[th]) THENL [
          MATCH_MP_TAC ABS_INV THEN UNDISCH_TAC (--`x < 0:real`--) THEN REAL_ARITH_TAC,
          UNDISCH_TAC (--`abs (error x) * inv (abs x) <= 2 pow j / 2 pow 150 * inv (2 pow j * inv (2 pow 126))`--) THEN
          SUBGOAL_THEN (--` 2 pow j / 2 pow 150 * inv (2 pow j * inv (2 pow 126)) = inv (2 pow 24)`--) (fn th => REWRITE_TAC[th]) THEN
          REWRITE_TAC[real_div] THEN
          SUBGOAL_THEN (--`inv (2 pow j * inv (2 pow 126)) = inv (2 pow j) * inv (inv (2 pow 126))`--) (fn th => REWRITE_TAC[th]) THENL [
            MATCH_MP_TAC REAL_INV_MUL THEN CONJ_TAC THENL [
              MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC, MATCH_MP_TAC REAL_INV_NZ THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC],
            SUBGOAL_THEN (--`inv (inv (2 pow 126)) = 2 pow 126`--) (fn th => REWRITE_TAC[th]) THENL [
              MATCH_MP_TAC REAL_INVINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC,
              REWRITE_TAC [REAL_ARITH (--`2 pow j * inv (2 pow 150) * (inv (2 pow j) * 2 pow 126) =
              (2 pow j * inv (2 pow j)) * (inv (2 pow 150) * 2 pow 126)`--)] THEN
              SUBGOAL_THEN (--`2 pow j * inv (2 pow j) = (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID,REAL_MUL_RID]) THENL [
                MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC,
                SUBGOAL_THEN (--`(150:num) = 24 + 126`--) (fn th => REWRITE_TAC[th,POW_ADD]) THENL [
                  RW_TAC arith_ss [],
                  SUBGOAL_THEN (--`inv (2 pow 24 * 2 pow 126) = inv (2 pow 24) * inv (2 pow 126)`--) (fn th => REWRITE_TAC[th]) THENL [
                    MATCH_MP_TAC REAL_INV_MUL THEN CONJ_TAC THENL [
                      MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC, MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC],
                    REWRITE_TAC [REAL_ARITH (--`inv (2 pow 24) * inv (2 pow 126) * 2 pow 126 =
                    inv (2 pow 24) * (inv (2 pow 126) * 2 pow 126)`--)] THEN
                    SUBGOAL_THEN (--`inv (2 pow 126) * 2 pow 126 = (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID,REAL_MUL_RID]) THEN
                    MATCH_MP_TAC REAL_MUL_LINV THEN MATCH_MP_TAC POW_NZ THEN REAL_ARITH_TAC]]]]]],
        REWRITE_TAC [error] THEN REWRITE_TAC [REAL_LDISTRIB] THEN REWRITE_TAC [REAL_MUL_RID] THEN
        REWRITE_TAC [REAL_SUB_LDISTRIB,REAL_SUB_RDISTRIB] THEN
        REWRITE_TAC [REAL_ARITH (--`(x * (Val (float (round float_format To_nearest x)) * inv x) =
        ((x * inv x) * (Val (float (round float_format To_nearest x)))))`--)] THEN
        SUBGOAL_THEN (--`x * inv (x) = (&1:real)`--) (fn th => REWRITE_TAC[th,REAL_MUL_LID,REAL_MUL_RID]) THENL [
          MATCH_MP_TAC REAL_MUL_RINV THEN UNDISCH_TAC (--`x < 0:real`--) THEN REAL_ARITH_TAC, REAL_ARITH_TAC]]]]);

(* ------------------------------------------------------------------------- *)

val RELATIVE_ERROR_ZERO = store_thm (
  "RELATIVE_ERROR_ZERO",
  (--`! (x:real). normalizes (x:real) /\ (x = (&0:real)) ==> ? (e:real). abs(e) <= ((&1:real) / &2 pow (24:num)) /\
      (Val (float (round float_format To_nearest x)) = x * ((&1:real) + e))`--),
  GEN_TAC THEN REWRITE_TAC [REAL_ARITH (--`(Val (float (round float_format To_nearest x)) = x * (1 + e)) =
  (Val (float (round float_format To_nearest x)) - x = x * e)`--)] THEN REWRITE_TAC [GSYM error] THEN
  RW_TAC arith_ss [] THEN EXISTS_TAC (--`&0:real`--) THEN CONJ_TAC THENL [
    RW_TAC arith_ss [real_div,REAL_MUL_LID,ABS_0,REAL_LE_INV_EQ ] THEN MATCH_MP_TAC POW_POS THEN
    REAL_ARITH_TAC, RW_TAC arith_ss [REAL_MUL_LZERO] THEN MATCH_MP_TAC ERROR_IS_ZERO THEN
    EXISTS_TAC (--`float (0:num,0:num,0:num)`--) THEN CONJ_TAC THENL [
      REWRITE_TAC [Finite] THEN SUBGOAL_THEN (--`Iszero (float (0,0,0))`--) MP_TAC THENL [
        RW_TAC arith_ss [Iszero] THEN
        SUBGOAL_THEN (--`(defloat (float (0,0,0))) = (0:num,0:num,0:num)`--) (fn th => REWRITE_TAC[th]) THENL [
          REWRITE_TAC[GSYM float_tybij] THEN REWRITE_TAC[is_valid,float_format,expwidth,fracwidth] THEN
          RW_TAC arith_ss [], RW_TAC arith_ss [is_zero,exponent,fraction]],
        RW_TAC arith_ss []],
      RW_TAC arith_ss [Val] THEN
      SUBGOAL_THEN (--`(defloat (float (0,0,0))) = (0:num,0:num,0:num)`--) (fn th => REWRITE_TAC[th]) THENL [
        REWRITE_TAC[GSYM float_tybij] THEN REWRITE_TAC[is_valid,float_format,expwidth,fracwidth] THEN
        RW_TAC arith_ss [], RW_TAC arith_ss [valof] THEN RW_TAC arith_ss [real_div] THEN
        REAL_ARITH_TAC  ]]]);

(* ------------------------------------------------------------------------- *)

val RELATIVE_ERROR = store_thm (
  "RELATIVE_ERROR",
  (--`! (x:real). normalizes (x:real) ==> ? (e:real). abs(e) <= ((&1:real) / &2 pow (24:num)) /\
      (Val (float (round float_format To_nearest x)) = x * ((&1:real) + e))`--),
  GEN_TAC THEN ASM_CASES_TAC (--`x = (&0:real)`--) THENL [
    RW_TAC arith_ss [] THEN MATCH_MP_TAC RELATIVE_ERROR_ZERO THEN
    RW_TAC arith_ss [], ASM_CASES_TAC (--`(&0:real) < x`--) THENL [
      RW_TAC arith_ss [] THEN MATCH_MP_TAC RELATIVE_ERROR_POS THEN
      RW_TAC arith_ss [], RW_TAC arith_ss [] THEN
      MATCH_MP_TAC RELATIVE_ERROR_NEG THEN RW_TAC arith_ss [] THEN
      UNDISCH_TAC (--`~(x = 0)`--) THEN UNDISCH_TAC (--`~(0 < x)`--) THEN
      REAL_ARITH_TAC  ]]);

(* ------------------------------------------------------------------------- *)
(* We also want to ensure that the result is actually finite!                *)
(* ------------------------------------------------------------------------- *)

val DEFLOAT_FLOAT_ZEROSIGN_ROUND_FINITE = store_thm (
  "DEFLOAT_FLOAT_ZEROSIGN_ROUND_FINITE",
  (--`! b x. abs(x) < threshold(float_format) ==> is_finite(float_format)
      (defloat(float(zerosign(float_format) b (round float_format To_nearest x))))`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_ARITH (--`abs(x:real) < y = ~(x <= ~y) /\ ~(x >= y)`--)] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[round_def] THEN
  SUBGOAL_THEN (--`is_finite(float_format) (zerosign float_format b
  (closest (valof float_format) (\a. EVEN (fraction a))
  {a | is_finite float_format a} x))`--) ASSUME_TAC THENL [
    REWRITE_TAC[zerosign] THEN REPEAT (COND_CASES_TAC THEN REWRITE_TAC[]) THENL [
      REWRITE_TAC[IS_FINITE_EXPLICIT, plus_zero] THEN REWRITE_TAC[float_format, sign, exponent, fraction] THEN
      RW_TAC arith_ss [], REWRITE_TAC[IS_FINITE_EXPLICIT, minus_zero] THEN
      REWRITE_TAC[float_format, sign, exponent, fraction] THEN RW_TAC arith_ss [],
      MATCH_ACCEPT_TAC IS_FINITE_CLOSEST],
    SUBGOAL_THEN (--`!X x. is_finite(X) x ==> is_valid(X) x`--) MP_TAC THENL [
      REWRITE_TAC[is_finite] THEN MESON_TAC[],
      DISCH_THEN(fn th => FIRST_ASSUM(ASSUME_TAC o MATCH_MP th)) THEN
      FIRST_ASSUM(fn th => REWRITE_TAC[GEN_REWRITE_RULE I [float_tybij] th]) THEN
      ASM_REWRITE_TAC[]]]);

(* ------------------------------------------------------------------------- *)
(* Lifting of arithmetic operations.                                         *)
(* ------------------------------------------------------------------------- *)

val FLOAT_ADD = store_thm (
  "FLOAT_ADD",
  (--`! (a:float) (b:float). Finite(a) /\ Finite(b) /\ abs(Val(a) + Val(b)) < threshold(float_format)
      ==> Finite(a float_add b) /\ ((Val(a float_add b)) = (Val(a) + Val(b)) + error(Val(a) + Val(b)))`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (--`~(Isnan(a)) /\ ~(Infinity(a)) /\ ~(Isnan(b)) /\ ~(Infinity(b))`--) MP_TAC THENL [
    ASM_MESON_TAC[FLOAT_DISTINCT_FINITE], REWRITE_TAC [ISFINITE, Isnan, Infinity, Isnormal, Isdenormal, Iszero] THEN
    STRIP_TAC THEN UNDISCH_TAC (--`abs(Val(a) + Val(b)) < threshold(float_format)`--) THEN
    ASM_REWRITE_TAC [float_add, fadd, Val] THEN REWRITE_TAC[VALOF_DEFLOAT_FLOAT_ZEROSIGN_ROUND] THEN
    REWRITE_TAC[error, Val, DEFLOAT_FLOAT_ROUND] THEN DISCH_TAC THEN CONJ_TAC THENL [
      MATCH_MP_TAC DEFLOAT_FLOAT_ZEROSIGN_ROUND_FINITE THEN ASM_REWRITE_TAC [],
      REWRITE_TAC[error, Val, DEFLOAT_FLOAT_ROUND] THEN REAL_ARITH_TAC]]);

(*-----------------------*)

val FLOAT_SUB = store_thm (
  "FLOAT_SUB",
  (--`! a b. Finite(a) /\ Finite(b) /\ abs(Val(a) - Val(b)) < threshold(float_format)
      ==> Finite(a - b) /\ (Val(a - b) = (Val(a) - Val(b)) + error(Val(a) - Val(b)))`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (--`~(Isnan(a)) /\ ~(Infinity(a)) /\ ~(Isnan(b)) /\ ~(Infinity(b))`--) MP_TAC THENL [
  ASM_MESON_TAC[FLOAT_DISTINCT_FINITE], REWRITE_TAC [ISFINITE, Isnan, Infinity, Isnormal, Isdenormal, Iszero] THEN
  STRIP_TAC THEN UNDISCH_TAC (--`abs(Val(a) - Val(b)) < threshold(float_format)`--) THEN
  ASM_REWRITE_TAC [float_sub, fsub, Val] THEN REWRITE_TAC[VALOF_DEFLOAT_FLOAT_ZEROSIGN_ROUND] THEN
  REWRITE_TAC[error, Val, DEFLOAT_FLOAT_ROUND] THEN DISCH_TAC THEN CONJ_TAC THENL [
    MATCH_MP_TAC DEFLOAT_FLOAT_ZEROSIGN_ROUND_FINITE THEN ASM_REWRITE_TAC [],
    REWRITE_TAC[error, Val, DEFLOAT_FLOAT_ROUND] THEN REAL_ARITH_TAC]]);

(*-----------------------*)

val FLOAT_MUL = store_thm (
  "FLOAT_MUL",
  (--`! (a:float) (b:float). Finite(a) /\ Finite(b) /\ abs(Val(a) * Val(b)) < threshold(float_format)
      ==> Finite(a float_mul b) /\ (Val(a float_mul b) = (Val(a) * Val(b)) + error(Val(a) * Val(b)))`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (--`~(Isnan(a)) /\ ~(Infinity(a)) /\
  ~(Isnan(b)) /\ ~(Infinity(b))`--) MP_TAC THENL [
    ASM_MESON_TAC[FLOAT_DISTINCT_FINITE], REWRITE_TAC [ISFINITE, Isnan, Infinity, Isnormal, Isdenormal, Iszero] THEN
    STRIP_TAC THEN UNDISCH_TAC (--`abs(Val(a) * Val(b)) < threshold(float_format)`--) THEN
    ASM_REWRITE_TAC[float_mul, fmul, Val] THEN REWRITE_TAC[VALOF_DEFLOAT_FLOAT_ZEROSIGN_ROUND] THEN
    REWRITE_TAC[error, Val, DEFLOAT_FLOAT_ROUND] THEN DISCH_TAC THEN CONJ_TAC THENL [
      MATCH_MP_TAC DEFLOAT_FLOAT_ZEROSIGN_ROUND_FINITE THEN ASM_REWRITE_TAC [],
      REWRITE_TAC[error, Val, DEFLOAT_FLOAT_ROUND] THEN REAL_ARITH_TAC]]);

(*-----------------------*)

val FLOAT_DIV = store_thm (
  "FLOAT_DIV",
  (--`! a b. Finite(a) /\ Finite(b) /\ ~(Iszero(b)) /\ abs(Val(a) / Val(b)) < threshold(float_format)
      ==> Finite(a / b) /\ (Val(a / b) = (Val(a) / Val(b)) + error(Val(a) / Val(b)))`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (--`~(Isnan(a)) /\ ~(Infinity(a)) /\ ~(Isnan(b)) /\ ~(Infinity(b))`--) MP_TAC THENL [
    ASM_MESON_TAC[FLOAT_DISTINCT_FINITE], REWRITE_TAC[ISFINITE, Isnan, Infinity, Isnormal, Isdenormal, Iszero] THEN
    STRIP_TAC THEN UNDISCH_TAC (--`abs(Val(a) / Val(b)) < threshold(float_format)`--) THEN
    ASM_REWRITE_TAC[float_div, fdiv, Val] THEN UNDISCH_TAC (--`~(Iszero(b))`--) THEN
    REWRITE_TAC[Iszero] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC[VALOF_DEFLOAT_FLOAT_ZEROSIGN_ROUND] THEN
    REWRITE_TAC[error, Val, DEFLOAT_FLOAT_ROUND] THEN RW_TAC arith_ss [] THENL [
      MATCH_MP_TAC DEFLOAT_FLOAT_ZEROSIGN_ROUND_FINITE THEN ASM_REWRITE_TAC[], REAL_ARITH_TAC,
      MATCH_MP_TAC DEFLOAT_FLOAT_ZEROSIGN_ROUND_FINITE THEN ASM_REWRITE_TAC[], REAL_ARITH_TAC]]);

(*-----------------------*)

val Val_FLOAT_ROUND_VALOF = store_thm (
  "Val_FLOAT_ROUND_VALOF",
  (--`!x:real. Val (float (round float_format To_nearest x)) = valof float_format (round float_format To_nearest x)`--),
  GEN_TAC THEN REWRITE_TAC[Val] THEN REWRITE_TAC[DEFLOAT_FLOAT_ROUND]);

(*-----------------------*)

val FLOAT_ADD_RELATIVE = store_thm (
  "FLOAT_ADD_RELATIVE",
  (--`! (a:float) (b:float). Finite(a) /\ Finite(b) /\ normalizes (Val(a) + Val(b))
      ==>  Finite(a + b) /\ ? (e:real). abs(e) <= ((&1:real) / &2 pow (24:num)) /\
      (Val(a + b) = (Val(a) + Val(b)) * ((&1:real) + e))`--),
  REPEAT GEN_TAC THEN REWRITE_TAC [normalizes] THEN STRIP_TAC THEN
  SUBGOAL_THEN (--`~(Isnan(a)) /\ ~(Infinity(a)) /\ ~(Isnan(b)) /\ ~(Infinity(b))`--) MP_TAC THENL [
    ASM_MESON_TAC[FLOAT_DISTINCT_FINITE], REWRITE_TAC [ISFINITE, Isnan, Infinity, Isnormal, Isdenormal, Iszero] THEN
    STRIP_TAC THEN UNDISCH_TAC (--`abs(Val(a) + Val(b)) < threshold(float_format)`--) THEN
    ASM_REWRITE_TAC [float_add, fadd, Val] THEN REWRITE_TAC[VALOF_DEFLOAT_FLOAT_ZEROSIGN_ROUND] THEN
    REWRITE_TAC[error, Val, DEFLOAT_FLOAT_ROUND] THEN DISCH_TAC THEN CONJ_TAC THENL [
      MATCH_MP_TAC DEFLOAT_FLOAT_ZEROSIGN_ROUND_FINITE THEN ASM_REWRITE_TAC [],
      REWRITE_TAC[GSYM Val] THEN REWRITE_TAC[GSYM Val_FLOAT_ROUND_VALOF] THEN
      MATCH_MP_TAC RELATIVE_ERROR THEN RW_TAC arith_ss [normalizes,Val]]]);

(*-----------------------*)

val FLOAT_SUB_RELATIVE = store_thm (
  "FLOAT_SUB_RELATIVE",
  (--`! (a:float) (b:float). Finite(a) /\ Finite(b) /\ normalizes (Val(a) - Val(b))
      ==> Finite(a - b) /\ ? (e:real). abs(e) <= ((&1:real) / &2 pow (24:num)) /\
      (Val(a - b) = (Val(a) - Val(b)) * ((&1:real) + e))`--),
  REPEAT GEN_TAC THEN REWRITE_TAC [normalizes] THEN STRIP_TAC THEN
  SUBGOAL_THEN (--`~(Isnan(a)) /\ ~(Infinity(a)) /\ ~(Isnan(b)) /\ ~(Infinity(b))`--) MP_TAC THENL [
    ASM_MESON_TAC[FLOAT_DISTINCT_FINITE], REWRITE_TAC [ISFINITE, Isnan, Infinity, Isnormal, Isdenormal, Iszero] THEN
    STRIP_TAC THEN UNDISCH_TAC (--`abs(Val(a) - Val(b)) < threshold(float_format)`--) THEN
    ASM_REWRITE_TAC [float_sub, fsub, Val] THEN REWRITE_TAC[VALOF_DEFLOAT_FLOAT_ZEROSIGN_ROUND] THEN
    REWRITE_TAC[error, Val, DEFLOAT_FLOAT_ROUND] THEN DISCH_TAC THEN CONJ_TAC THENL [
      MATCH_MP_TAC DEFLOAT_FLOAT_ZEROSIGN_ROUND_FINITE THEN ASM_REWRITE_TAC [], REWRITE_TAC[GSYM Val] THEN
      REWRITE_TAC[GSYM Val_FLOAT_ROUND_VALOF] THEN MATCH_MP_TAC RELATIVE_ERROR THEN RW_TAC arith_ss [normalizes,Val]]]);

(*-----------------------*)

val FLOAT_MUL_RELATIVE = store_thm (
  "FLOAT_MUL_RELATIVE",
  (--`! (a:float) (b:float). Finite(a) /\ Finite(b) /\ normalizes (Val(a) * Val(b))
      ==> Finite(a * b) /\ ? (e:real). abs(e) <= ((&1:real) / &2 pow (24:num)) /\
      (Val(a * b) = (Val(a) * Val(b)) * ((&1:real) + e))`--),
  REPEAT GEN_TAC THEN REWRITE_TAC [normalizes] THEN STRIP_TAC THEN
  SUBGOAL_THEN (--`~(Isnan(a)) /\ ~(Infinity(a)) /\ ~(Isnan(b)) /\ ~(Infinity(b))`--) MP_TAC THENL [
    ASM_MESON_TAC[FLOAT_DISTINCT_FINITE], REWRITE_TAC [ISFINITE, Isnan, Infinity, Isnormal, Isdenormal, Iszero] THEN
    STRIP_TAC THEN UNDISCH_TAC (--`abs(Val(a) * Val(b)) < threshold(float_format)`--) THEN
    ASM_REWRITE_TAC [float_mul, fmul, Val] THEN REWRITE_TAC[VALOF_DEFLOAT_FLOAT_ZEROSIGN_ROUND] THEN
    REWRITE_TAC[error, Val, DEFLOAT_FLOAT_ROUND] THEN DISCH_TAC THEN CONJ_TAC THENL [
      MATCH_MP_TAC DEFLOAT_FLOAT_ZEROSIGN_ROUND_FINITE THEN ASM_REWRITE_TAC [],
      REWRITE_TAC[GSYM Val] THEN REWRITE_TAC[GSYM Val_FLOAT_ROUND_VALOF] THEN MATCH_MP_TAC RELATIVE_ERROR THEN
      RW_TAC arith_ss [normalizes,Val]]]);

(*-----------------------*)

val FLOAT_DIV_RELATIVE = store_thm (
  "FLOAT_DIV_RELATIVE",
  (--`! (a:float) (b:float). Finite(a) /\ Finite(b) /\ ~(Iszero(b)) /\ normalizes (Val(a) / Val(b))
      ==>  Finite(a / b) /\ ? (e:real). abs(e) <= ((&1:real) / &2 pow (24:num)) /\
      (Val(a / b) = (Val(a) / Val(b)) * ((&1:real) + e))`--),
  REPEAT GEN_TAC THEN REWRITE_TAC [normalizes] THEN STRIP_TAC THEN
  SUBGOAL_THEN (--`~(Isnan(a)) /\ ~(Infinity(a)) /\ ~(Isnan(b)) /\ ~(Infinity(b))`--) MP_TAC THENL [
    ASM_MESON_TAC[FLOAT_DISTINCT_FINITE], REWRITE_TAC[ISFINITE, Isnan, Infinity, Isnormal, Isdenormal, Iszero] THEN
    STRIP_TAC THEN UNDISCH_TAC (--`abs(Val(a) / Val(b)) < threshold(float_format)`--) THEN
    ASM_REWRITE_TAC[float_div, fdiv, Val] THEN UNDISCH_TAC (--`~(Iszero(b))`--) THEN REWRITE_TAC[Iszero] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC[VALOF_DEFLOAT_FLOAT_ZEROSIGN_ROUND] THEN
    REWRITE_TAC[error, Val, DEFLOAT_FLOAT_ROUND] THEN STRIP_TAC THEN CONJ_TAC THENL [
      MATCH_MP_TAC DEFLOAT_FLOAT_ZEROSIGN_ROUND_FINITE THEN ASM_REWRITE_TAC[], REWRITE_TAC[GSYM Val] THEN
      REWRITE_TAC[GSYM Val_FLOAT_ROUND_VALOF] THEN MATCH_MP_TAC RELATIVE_ERROR THEN RW_TAC arith_ss [normalizes,Val]]]);

(*------------- *)

val FLOAT_ADD_FINITE = store_thm (
  "FLOAT_ADD",
  (--`! (a:float) (b:float). Finite(a) /\ Finite(b) /\ abs(Val(a) + Val(b)) < threshold(float_format)
      ==>  Finite(a float_add b)`--),
  RW_TAC arith_ss [FLOAT_ADD]);

(*------------- *)

val FLOAT_SUB_FINITE = store_thm (
  "FLOAT_SUB_FINITE",
  (--`! a b. Finite(a) /\ Finite(b) /\ abs(Val(a) - Val(b)) < threshold(float_format) ==> Finite(a - b)`--),
  RW_TAC arith_ss [FLOAT_SUB]);

(*------------- *)

val FLOAT_MUL_FINITE = store_thm (
  "FLOAT_MUL_FINITE",
  (--`! (a:float) (b:float). Finite(a) /\ Finite(b) /\ abs(Val(a) * Val(b)) < threshold(float_format) ==> Finite(a float_mul b)`--),
  RW_TAC arith_ss [FLOAT_MUL]);

(*---------------------------------------------------------------------------*
 * Write the theory to disk.                                                 *
 *---------------------------------------------------------------------------*)
val _ = export_theory();
