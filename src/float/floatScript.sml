(* =========================================================================
   Useful properties of floating point numbers.
   ========================================================================= *)

open HolKernel boolLib bossLib
open pairTheory pred_setTheory prim_recTheory numTheory arithmeticTheory
     realTheory ieeeTheory

open numLib realSimps RealArith Ho_Rewrite

val () = new_theory "float"

val _ = ParseExtras.temp_loose_equality()
val _ = diminish_srw_ss ["RMULCANON", "RMULRELNORM"]


(* Compute some constant values *)

val () = computeLib.add_funs [realTheory.REAL_INV_1OVER]
val EVAL_PROVE = EQT_ELIM o EVAL
fun EVAL' thms = SIMP_CONV (srw_ss()) thms THENC EVAL
fun eval thms = rhs o concl o EVAL' thms
val expw_tm = eval [expwidth, float_format] ``expwidth float_format``
val fracw_tm = eval [fracwidth, float_format] ``fracwidth float_format``
val bias_tm = eval [bias, expwidth, float_format] ``bias float_format``
val emax_tm = eval [emax, expwidth, float_format] ``emax float_format``
val pemax_tm = eval [] ``^emax_tm - 1``
val sfracw_tm = eval [] ``^fracw_tm + 1``
val frac_tm = eval [] ``2 EXP ^fracw_tm``
val pfrac_tm = eval [] ``&(^frac_tm - 1) : real``
val exp_pemax_tm = eval [] ``&(2 EXP ^pemax_tm) : real``
val exp_emaxmfrac_tm = eval [fracwidth, float_format]
  ``^exp_pemax_tm - &(2 EXP (^pemax_tm - ^fracw_tm))``
val sbias_tm = eval [] ``^bias_tm + 1``
val pbias_tm = eval [] ``^bias_tm - 1``
val ppbias_tm = eval [] ``^pbias_tm - 1``
val pppbias_tm = eval [] ``^ppbias_tm - 1``
val bias_frac_tm = eval [] ``^bias_tm + ^fracw_tm``

(* -------------------------------------------------------------------------
   Useful lemmas.
   ------------------------------------------------------------------------- *)

val SIGN = Q.store_thm ("SIGN",
  `!a. sign a = FST a`,
  gen_tac \\ pairLib.PairCases_on `a` \\ simp [sign])

val EXPONENT = Q.store_thm ("EXPONENT",
  `!a. exponent a = FST (SND a)`,
  gen_tac \\ pairLib.PairCases_on `a` \\ simp [exponent])

val FRACTION = Q.store_thm ("FRACTION",
  `!a. fraction a = SND (SND a)`,
  gen_tac \\ pairLib.PairCases_on `a` \\ simp [fraction])

val IS_VALID = Q.store_thm ("IS_VALID",
  `!X a. is_valid X a =
         sign a < 2 /\ exponent a < 2 EXP (expwidth X) /\
         fraction a < 2 EXP (fracwidth X)`,
  REPEAT gen_tac
  \\ pairLib.PairCases_on `a`
  \\ simp [is_valid, sign, exponent, fraction]
  )

val VALOF = Q.store_thm ("VALOF",
  `!X a.
      valof X a =
      if exponent a = 0 then
        ~1 pow sign a * (2 / 2 pow bias X) * (&fraction a / 2 pow fracwidth X)
      else
        ~1 pow sign a * (2 pow exponent a / 2 pow bias X) *
       (1 + &fraction a / 2 pow fracwidth X)`,
  REPEAT gen_tac
  \\ pairLib.PairCases_on `a`
  \\ simp [valof, sign, exponent, fraction]
  )

(*-----------------------*)

val IS_VALID_DEFLOAT = Q.store_thm ("IS_VALID_DEFLOAT",
  `!a. is_valid float_format (defloat a)`,
  REWRITE_TAC[float_tybij])

val IS_FINITE_EXPLICIT = Q.store_thm ("IS_FINITE_EXPLICIT",
  `!a. is_finite float_format a =
       sign a < 2 /\ exponent a < ^emax_tm /\ fraction a < ^frac_tm`,
  gen_tac
  \\ pairLib.PairCases_on `a`
  \\ simp [is_valid, is_finite, is_normal, is_denormal, is_zero, exponent, emax,
           float_format, fraction, expwidth, fracwidth, sign]
  )

(*-----------------------*)

val FLOAT_CASES = Q.store_thm ("FLOAT_CASES",
  `!a. Isnan a \/ Infinity a \/ Isnormal a \/ Isdenormal a \/ Iszero a`,
  gen_tac
  \\ mp_tac (Q.SPEC `a:float` IS_VALID_DEFLOAT)
  \\ rw [Isnan, Infinity, Isnormal, Isdenormal, Iszero,
         is_nan, is_infinity, is_normal, is_denormal, is_zero, IS_VALID, emax]
  )

val FLOAT_CASES_FINITE = Q.store_thm ("FLOAT_CASES_FINITE",
  `!a. Isnan a \/ Infinity a \/ Finite a`,
  rewrite_tac [FLOAT_CASES, Finite])

(*-----------------------*)

val FLOAT_DISTINCT = Q.store_thm ("FLOAT_DISTINCT",
  `!a. ~(Isnan a /\ Infinity a) /\
       ~(Isnan a /\ Isnormal a) /\
       ~(Isnan a /\ Isdenormal a) /\
       ~(Isnan a /\ Iszero a) /\
       ~(Infinity a /\ Isnormal a) /\
       ~(Infinity a /\ Isdenormal a) /\
       ~(Infinity a /\ Iszero a) /\
       ~(Isnormal a /\ Isdenormal a) /\
       ~(Isnormal a /\ Iszero a) /\
       ~(Isdenormal a /\ Iszero a)`,
  rw [Isnan, Infinity, Isnormal, Isdenormal, Iszero,
      is_nan, is_infinity, is_normal, is_denormal, is_zero,
      float_format, emax, expwidth, exponent, fraction])

val FLOAT_DISTINCT_FINITE = Q.store_thm ("FLOAT_DISTINCT_FINITE",
  `!a. ~(Isnan a /\ Infinity a) /\ ~(Isnan a /\ Finite a) /\
       ~(Infinity a /\ Finite a)`,
  prove_tac [FLOAT_DISTINCT, Finite])

(*-----------------------*)

val FLOAT_INFINITIES_SIGNED = Q.store_thm ("FLOAT_INFINITIES_SIGNED",
  `(sign (defloat Plus_infinity) = 0) /\ (sign (defloat Minus_infinity) = 1)`,
  `(defloat (float (plus_infinity float_format)) =
    plus_infinity float_format) /\
   (defloat(float(minus_infinity float_format)) =
    minus_infinity float_format)`
  by simp [GSYM float_tybij, is_valid, plus_infinity, minus_infinity,
           float_format, emax, fracwidth, expwidth]
  \\ fs [Plus_infinity, Minus_infinity, sign, plus_infinity, minus_infinity]
  )

val INFINITY_IS_INFINITY = Q.store_thm ("INFINITY_IS_INFINITY",
  `Infinity Plus_infinity /\ Infinity Minus_infinity`,
  `(defloat (float (plus_infinity float_format)) =
    plus_infinity float_format) /\
   (defloat (float (minus_infinity float_format)) =
    minus_infinity float_format)`
  by simp [GSYM float_tybij, is_valid, plus_infinity, minus_infinity,
           float_format, emax, fracwidth, expwidth]
  \\ fs [Infinity, Plus_infinity, Minus_infinity, is_infinity, plus_infinity,
         minus_infinity, exponent, fraction]
  )

val ZERO_IS_ZERO = Q.store_thm ("ZERO_IS_ZERO",
  `Iszero Plus_zero /\ Iszero Minus_zero`,
  `(defloat (float (plus_zero float_format)) = plus_zero float_format) /\
   (defloat (float (minus_zero float_format)) = minus_zero float_format)`
  by simp [GSYM float_tybij, is_valid, plus_zero, minus_zero, float_format,
           emax, fracwidth, expwidth]
  \\ fs [Iszero, Plus_zero, Minus_zero, is_zero, plus_zero, minus_zero,
          exponent, fraction]
  )

(*-----------------------*)

val INFINITY_NOT_NAN = Q.store_thm ("INFINITY_NOT_NAN",
  `~Isnan Plus_infinity /\ ~Isnan Minus_infinity`,
  PROVE_TAC [INFINITY_IS_INFINITY, FLOAT_DISTINCT_FINITE])

val ZERO_NOT_NAN = Q.store_thm ("ZERO_NOT_NAN",
  `~Isnan Plus_zero /\ ~Isnan Minus_zero`,
  PROVE_TAC [ZERO_IS_ZERO, FLOAT_DISTINCT])

(*-----------------------*)

val FLOAT_INFINITIES = Q.store_thm ("FLOAT_INFINITIES",
  `!a. Infinity a = (a == Plus_infinity) \/ (a == Minus_infinity)`,
  gen_tac
  \\ strip_assume_tac (Q.SPEC `a:float` FLOAT_CASES_FINITE)
  >- (`~Infinity a` by prove_tac [FLOAT_DISTINCT_FINITE]
      \\ fs [Isnan, Infinity, fcompare, feq, float_eq])
  >- (`~Isnan a` by prove_tac [FLOAT_DISTINCT_FINITE]
      \\ fs [Isnan, Infinity, fcompare, feq, float_eq,
             REWRITE_RULE [Isnan] INFINITY_NOT_NAN,
             REWRITE_RULE [Infinity] INFINITY_IS_INFINITY,
             FLOAT_INFINITIES_SIGNED]
      \\ rw []
      \\ metis_tac [IS_VALID_DEFLOAT, IS_VALID,
                    DECIDE ``a < 2n ==> (a = 0) \/ (a = 1)``])
  \\ `~Infinity a /\ ~Isnan a` by prove_tac [FLOAT_DISTINCT_FINITE]
  \\ fs [Isnan, Infinity, fcompare, feq, float_eq,
         REWRITE_RULE [Isnan] INFINITY_NOT_NAN,
         REWRITE_RULE [Infinity] INFINITY_IS_INFINITY,
         FLOAT_INFINITIES_SIGNED]
  )

val FLOAT_INFINITES_DISTINCT = Q.store_thm ("FLOAT_INFINITES_DISTINCT",
  `!a. ~(a == Plus_infinity /\ a == Minus_infinity)`,
  rw [Plus_infinity, Minus_infinity, feq, float_eq, fcompare]
  \\ fs [REWRITE_RULE [Plus_infinity, Minus_infinity] FLOAT_INFINITIES_SIGNED,
         REWRITE_RULE [Infinity, Plus_infinity, Minus_infinity]
           INFINITY_IS_INFINITY,
         REWRITE_RULE [Isnan, Plus_infinity, Minus_infinity] INFINITY_NOT_NAN]
  )

(* ------------------------------------------------------------------------- *)
(* Lifting of the nonexceptional comparison operations.                      *)
(* ------------------------------------------------------------------------- *)

val FLOAT_LIFT_TAC =
  REPEAT strip_tac
  \\ `~Isnan a /\ ~Infinity a /\ ~Isnan b /\ ~Infinity b`
  by prove_tac [FLOAT_DISTINCT_FINITE]
  \\ fs [Finite, Isnan, Infinity, Isnormal, Isdenormal, Iszero,
         float_lt, flt, float_gt, fgt, float_le, fle, float_ge, fge,
         float_eq, feq, fcompare, Val, real_gt, real_ge, GSYM REAL_NOT_LT]
  \\ REPEAT COND_CASES_TAC
  \\ fs []
  \\ prove_tac [REAL_LT_ANTISYM, REAL_LT_TOTAL]


val FLOAT_LT = Q.store_thm ("FLOAT_LT",
  `!a b. Finite a /\ Finite b ==> (a < b = Val a < Val b)`, FLOAT_LIFT_TAC)

val FLOAT_GT = Q.store_thm ("FLOAT_GT",
  `!a b. Finite a /\ Finite b ==> (a > b = Val a > Val b)`, FLOAT_LIFT_TAC)

val FLOAT_LE = Q.store_thm ("FLOAT_LE",
  `!a b. Finite a /\ Finite b ==> (a <= b = Val a <= Val b)`, FLOAT_LIFT_TAC)

val FLOAT_GE = Q.store_thm ("FLOAT_GE",
  `!a b. Finite a /\ Finite b ==> (a >= b = Val a >= Val b)`, FLOAT_LIFT_TAC)

val FLOAT_EQ = Q.store_thm ("FLOAT_EQ",
  `!a b. Finite a /\ Finite b ==> (a == b = (Val a = Val b))`, FLOAT_LIFT_TAC)

val FLOAT_EQ_REFL = Q.store_thm ("FLOAT_EQ_REFL",
  `!a. (a == a) = ~Isnan a`, rw [float_eq, feq, fcompare, Isnan])

(* ------------------------------------------------------------------------- *)
(* Various lemmas.                                                           *)
(* ------------------------------------------------------------------------- *)

val IS_VALID_SPECIAL = Q.store_thm ("IS_VALID_SPECIAL",
  `!X. is_valid X (minus_infinity X) /\ is_valid X (plus_infinity X) /\
       is_valid X (topfloat X)       /\ is_valid X (bottomfloat X) /\
       is_valid X (plus_zero X)      /\ is_valid X (minus_zero X)`,
  simp [is_valid, minus_infinity, plus_infinity, plus_zero, minus_zero,
        topfloat, bottomfloat, emax])

(*-------------------------------------------------------*)

val IS_CLOSEST_EXISTS = Q.store_thm ("IS_CLOSEST_EXISTS",
  `!v x s. FINITE s ==> s <> EMPTY ==> ?a:num#num#num. is_closest v s x a`,
  gen_tac
  \\ gen_tac
  \\ HO_MATCH_MP_TAC FINITE_INDUCT
  \\ simp [NOT_INSERT_EMPTY]
  \\ gen_tac
  \\ Cases_on `s = EMPTY`
  >- simp [is_closest]
  \\ Cases_on `FINITE s`
  \\ rw []
  \\ Cases_on `abs (v a - x) <= abs (v e - x)`
  \\ fs [is_closest]
  >- (qexists_tac `a` \\ rw [] \\ simp [])
  \\ qexists_tac `e`
  \\ rw []
  >- simp []
  \\ qpat_x_assum `!b:num#num#num. P` (qspec_then `b` mp_tac)
  \\ qpat_x_assum `~(abs (v a - x) <= abs (v e - x))` mp_tac
  \\ simp []
  \\ REAL_ARITH_TAC
  )

val CLOSEST_IS_EVERYTHING = Q.store_thm ("CLOSEST_IS_EVERYTHING",
  `!v p s x.
      FINITE s ==> s <> EMPTY ==>
      is_closest v s x (closest v p s x) /\
      ((?b:num#num#num. is_closest v s x b /\ p b) ==> p (closest v p s x))`,
  rw [closest]
  \\ SELECT_ELIM_TAC
  \\ prove_tac [IS_CLOSEST_EXISTS]
  )

val CLOSEST_IN_SET = Q.store_thm ("CLOSEST_IN_SET",
  `!v p x s:(num#num#num) set.
      FINITE s ==> s <> EMPTY ==> (closest v p s x) IN s`,
  prove_tac [CLOSEST_IS_EVERYTHING, is_closest])


val CLOSEST_IS_CLOSEST = Q.store_thm ("CLOSEST_IS_CLOSEST",
  `!v p x s:(num#num#num) set.
      FINITE s ==> s <> EMPTY ==> is_closest v s x (closest v p s x)`,
  prove_tac [CLOSEST_IS_EVERYTHING])

(*-------------------------------------------------------*)

val FLOAT_FIRSTCROSS = Q.prove (
  `!m n p.
      {a: num # num # num | FST a < m /\ FST (SND a) < n /\ SND (SND a) < p} =
      IMAGE (\(x,(y,z)). (x,y,z))
        ({x | x < m} CROSS ({y | y < n} CROSS {z | z < p}))`,
  rw [EXTENSION]
  \\ pairLib.PairCases_on `x`
  \\ simp []
  \\ eq_tac
  \\ rw []
  >- (qexists_tac `(x0, x1, x2)` \\ fs [])
  \\ pairLib.PairCases_on `x'`
  \\ fs []
  )

val FLOAT_COUNTINDUCT = Q.prove (
  `!n. ({x | x < 0n} = EMPTY) /\ ({x | x < SUC n} = n INSERT {x | x < n})`,
  rw [EXTENSION])

val FLOAT_FINITECOUNT = Q.prove (
  `!n:num. FINITE {x | x < n}`,
  Induct \\ rw [FLOAT_COUNTINDUCT])

val FINITE_R3 = Q.prove (
  `!m n p.
    FINITE {a: num # num # num |
            FST a < m /\ FST (SND a) < n /\ SND (SND a) < p}`,
  rw [FLOAT_FIRSTCROSS, IMAGE_FINITE, FLOAT_FIRSTCROSS, FLOAT_FINITECOUNT])

val IS_VALID_FINITE = Q.store_thm ("IS_VALID_FINITE",
  `FINITE {a:num#num#num | is_valid (X:num#num) a}`,
  rewrite_tac [IS_VALID, SIGN, EXPONENT, FRACTION, FINITE_R3])

(*-------------------------------------------------------*)

val FLOAT_IS_FINITE_SUBSET = Q.prove (
  `!X. {a | is_finite X a} SUBSET {a | is_valid X a}`,
  rw [is_finite, SUBSET_DEF])

val MATCH_FLOAT_FINITE = Q.prove (
  `!X. {a | is_finite X a} SUBSET {a | is_valid X a} ==>
       FINITE {a | is_finite X a}`,
  metis_tac [SUBSET_FINITE, IS_VALID_FINITE])

val IS_FINITE_FINITE = Q.store_thm ("IS_FINITE_FINITE",
  `!X. FINITE {a | is_finite X a}`,
  metis_tac [MATCH_FLOAT_FINITE, FLOAT_IS_FINITE_SUBSET])

(*-----------------------*)

val IS_VALID_NONEMPTY = Q.store_thm ("IS_VALID_NONEMPTY",
  `{a | is_valid X a} <> EMPTY`,
  rw [EXTENSION]
  \\ qexists_tac `(0,0,0)`
  \\ rw [is_valid]
  )

val IS_FINITE_NONEMPTY = Q.store_thm ("IS_FINITE_NONEMPTY",
  `{a | is_finite X a} <> EMPTY`,
  rw [EXTENSION]
  \\ qexists_tac `(0,0,0)`
  \\ rw [is_finite, is_valid, is_zero, exponent, fraction]
  )

(*-----------------------*)

val IS_FINITE_CLOSEST = Q.store_thm ("IS_FINITE_CLOSEST",
  `!X v p x. is_finite X (closest v p {a | is_finite X a} x)`,
  REPEAT gen_tac
  \\ `closest v p {a | is_finite X a} x IN {a | is_finite X a}`
  by metis_tac [CLOSEST_IN_SET, IS_FINITE_FINITE, IS_FINITE_NONEMPTY]
  \\ fs []
  )

val IS_VALID_CLOSEST = Q.store_thm ("IS_VALID_CLOSEST",
  `!X v p x. is_valid X (closest v p {a | is_finite X a} x)`,
  metis_tac [IS_FINITE_CLOSEST, is_finite])

(*-----------------------*)

val IS_VALID_ROUND = Q.store_thm ("IS_VALID_ROUND",
  `!X x. is_valid X (round X To_nearest x)`,
  rw [is_valid, round_def, IS_VALID_SPECIAL, IS_VALID_CLOSEST])

(*-----------------------*)

val DEFLOAT_FLOAT_ROUND = Q.store_thm ("DEFLOAT_FLOAT_ROUND",
  `!x. defloat (float (round float_format To_nearest x)) =
       round float_format To_nearest x`,
  rewrite_tac [GSYM float_tybij, IS_VALID_ROUND])

(*-----------------------*)

val DEFLOAT_FLOAT_ZEROSIGN_ROUND = Q.store_thm ("DEFLOAT_FLOAT_ZEROSIGN_ROUND",
  `!x b. defloat (float (zerosign float_format b
                           (round float_format To_nearest x))) =
         zerosign float_format b (round float_format To_nearest x)`,
  rw [GSYM float_tybij, zerosign, IS_VALID_ROUND, IS_VALID_SPECIAL])

(*-----------------------*)

val VALOF_DEFLOAT_FLOAT_ZEROSIGN_ROUND = Q.store_thm (
  "VALOF_DEFLOAT_FLOAT_ZEROSIGN_ROUND",
  `!x b. valof float_format
           (defloat (float (zerosign float_format b
              (round float_format To_nearest x)))) =
         valof float_format (round float_format To_nearest x)`,
  rw [DEFLOAT_FLOAT_ZEROSIGN_ROUND, zerosign, minus_zero, plus_zero]
  \\ `?p q r. round float_format To_nearest x = (p, q, r)`
  by metis_tac [pairTheory.pair_CASES]
  \\ fs [is_zero, exponent, fraction, valof]
  )

(*--------------------------------------------------------------*)

val ISFINITE = Q.store_thm ("ISFINITE",
  `!a. Finite a = is_finite float_format (defloat a)`,
  rewrite_tac [Finite, is_finite, Isnormal, Isdenormal, Iszero, float_tybij])

(*--------------------------------------*)

Theorem REAL_ABS_INV[local]:
  !x. abs (inv x) = inv (abs x)
Proof
  gen_tac
  \\ Cases_on `x = 0r`
  \\ simp [REAL_INV_0, REAL_ABS_0, ABS_INV]
QED

Theorem REAL_ABS_DIV[local]:
  !x y. abs (x / y) = abs x / abs y
Proof
  rewrite_tac [real_div, REAL_ABS_INV, REAL_ABS_MUL]
QED

Theorem REAL_POW_LE_1[local]:
  !n x. 1r <= x ==> 1 <= x pow n
Proof
  Induct
  \\ rw [pow]
  \\ GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID]
  \\ match_mp_tac REAL_LE_MUL2
  \\ simp []
QED

Theorem REAL_POW_MONO[local] = realTheory.REAL_POW_MONO

Theorem VAL_FINITE:
  !a. Finite a ==> abs (Val a) <= largest float_format
Proof
  rw [Val, VALOF, ISFINITE, IS_FINITE_EXPLICIT, float_format, fracwidth, bias,
      emax, expwidth, largest, GSYM POW_ABS, REAL_ABS_MUL, REAL_ABS_DIV,
      ABS_NEG, ABS_N, POW_ONE, realTheory.mult_rat]
  \\ EVAL_TAC
  >- simp [realTheory.REAL_LE_LDIV_EQ]
  \\ `exponent (defloat a) <= ^pemax_tm /\ 1r <= 2 /\
      0r <= &fraction (defloat a) / &^frac_tm /\
      &fraction (defloat a) / &^frac_tm <=
      1 + &fraction (defloat a) / &^frac_tm`
  by simp [realTheory.REAL_LE_DIV, realTheory.REAL_LE_ADDL]
  \\ `2 pow exponent (defloat a) <= 2 pow ^pemax_tm /\
      (abs (1 + &fraction (defloat a) / &^frac_tm) =
       1 + &fraction (defloat a) / &^frac_tm)`
  by prove_tac [realTheory.REAL_LE_TRANS, ABS_REFL, REAL_POW_MONO]
  \\ simp [realTheory.REAL_LE_LDIV_EQ, realTheory.REAL_LDISTRIB,
           ONCE_REWRITE_RULE [realTheory.REAL_MUL_COMM] realTheory.mult_ratr]
  \\ SUBST1_TAC (GSYM (EVAL ``^exp_pemax_tm + ^exp_emaxmfrac_tm``))
  \\ match_mp_tac realTheory.REAL_LE_ADD2
  \\ fs [realTheory.mult_ratr, realTheory.REAL_LE_LDIV_EQ]
  \\ SUBST1_TAC (GSYM (EVAL ``^exp_pemax_tm * ^pfrac_tm``))
  \\ match_mp_tac realTheory.REAL_LE_MUL2
  \\ fs [realTheory.POW_POS]
QED

(* ------------------------------------------------------------------------- *)
(* Explicit numeric value for threshold, to save repeated recalculation.     *)
(* ------------------------------------------------------------------------- *)

val FLOAT_THRESHOLD_EXPLICIT = save_thm ("FLOAT_THRESHOLD_EXPLICIT",
  EVAL' [threshold, float_format, emax, bias, fracwidth, expwidth]
    ``threshold float_format``)

val FLOAT_LARGEST_EXPLICIT = save_thm ("FLOAT_LARGEST_EXPLICIT",
  EVAL' [largest, float_format, emax, bias, fracwidth, expwidth]
    ``largest float_format``)

val VAL_THRESHOLD = Q.store_thm ("VAL_THRESHOLD",
  `!a. Finite a ==> abs (Val a) < threshold float_format`,
  REPEAT strip_tac
  \\ match_mp_tac REAL_LET_TRANS
  \\ qexists_tac `largest float_format`
  \\ simp [VAL_FINITE, FLOAT_THRESHOLD_EXPLICIT, FLOAT_LARGEST_EXPLICIT]
  )

(* ------------------------------------------------------------------------- *)
(* Lifting up of rounding (to nearest).                                      *)
(* ------------------------------------------------------------------------- *)

val error = Define`
  error x = Val (float (round float_format To_nearest x)) - x`

(*-----------------------*)

val BOUND_AT_WORST_LEMMA = Q.prove (
  `!a x. abs x < threshold float_format /\ is_finite float_format a ==>
         abs (valof float_format (round float_format To_nearest x) - x) <=
         abs (valof float_format a - x)`,
  rw [round_def, REAL_ARITH ``abs x < y = ~(x <= ~y) /\ ~(x >= y)``]
  \\ match_mp_tac
      (IS_FINITE_FINITE
       |> Q.SPEC `float_format`
       |> MATCH_MP CLOSEST_IS_CLOSEST
       |> Q.SPECL [`valof float_format`, `\a. EVEN (fraction a)`, `x`]
       |> REWRITE_RULE [IS_FINITE_NONEMPTY, is_closest]
       |> CONJUNCT2)
  \\ simp []
  )

val ERROR_AT_WORST_LEMMA = Q.prove (
  `!a x. abs x < threshold float_format /\ Finite a ==>
         abs (error x) <= abs (Val a - x)`,
  rewrite_tac [ISFINITE, Val, error, BOUND_AT_WORST_LEMMA, DEFLOAT_FLOAT_ROUND])

val ERROR_IS_ZERO = Q.store_thm ("ERROR_IS_ZERO",
  `!a x. Finite a /\ (Val a = x) ==> (error x = 0)`,
  rw []
  \\ match_mp_tac
      (ERROR_AT_WORST_LEMMA
       |> Q.SPECL [`a`, `Val a`]
       |> SIMP_RULE (srw_ss())
            [REAL_ABS_0, REAL_ARITH ``abs x <= 0 = (x = 0r)``])
  \\ simp [VAL_THRESHOLD]
  )

(*--------------------------------------------------------------*)

val ERROR_BOUND_LEMMA1 = Q.prove (
  `!x. 0r <= x /\ x < 1 ==>
       ?n. n < 2n EXP ^fracw_tm /\ &n / 2 pow ^fracw_tm <= x /\
           x < &(SUC n) / 2 pow ^fracw_tm`,
  REPEAT strip_tac
  \\ qspec_then `\n. &n / 2 pow ^fracw_tm <= x` mp_tac EXISTS_GREATEST
  \\ simp []
  \\ Lib.W (Lib.C SUBGOAL_THEN (fn th => rewrite_tac [th]) o lhs o lhand o snd)
  >- (conj_tac
      >- (qexists_tac `0n` \\ simp [])
      \\ qexists_tac `^frac_tm`
      \\ rw [REAL_LE_LDIV_EQ]
      \\ fs [realTheory.REAL_NOT_LE, realTheory.real_gt,
             REAL_ARITH ``&^frac_tm < y /\ x < 1 ==> x * &^frac_tm < y``])
  \\ disch_then (Q.X_CHOOSE_THEN `n` strip_assume_tac)
  \\ pop_assum (qspec_then `SUC n` assume_tac)
  \\ qexists_tac `n`
  \\ fs [REAL_NOT_LE]
  \\ fs [REAL_LE_LDIV_EQ]
  \\ `&n < &^frac_tm`
  by metis_tac
       [REAL_ARITH ``!n. x < 1 /\ n <= x * &^frac_tm ==> n < &^frac_tm``]
  \\ fs []
  )

(*---------------------------*)

val ERROR_BOUND_LEMMA2 = Q.prove (
  `!x. 0r <= x /\ x < 1 ==>
       ?n. n <= 2 EXP ^fracw_tm /\
           abs (x - &n / 2 pow ^fracw_tm) <= inv (2 pow ^sfracw_tm)`,
  gen_tac
  \\ disch_then
       (fn th => Q.X_CHOOSE_THEN `n` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)
                   (MATCH_MP ERROR_BOUND_LEMMA1 th)
        \\ strip_assume_tac th)
  \\ disch_then (mp_tac o Q.SPEC `inv (2 pow ^sfracw_tm)` o MATCH_MP
       (REAL_ARITH ``!a:real b x d. a <= x /\ x < b ==> b <= a + 2 * d ==>
                                    abs (x - a) <= d \/ abs (x - b) <= d``))
  \\ Lib.W (Lib.C SUBGOAL_THEN
              (fn th => rewrite_tac [th]) o lhand o lhand o snd)
  >- (simp [] \\ EVAL_TAC \\ simp [realTheory.REAL_DIV_ADD, ADD1])
  \\ rw []
  >- (qexists_tac `n` \\ fs [])
  \\ qexists_tac `SUC n`
  \\ fs []
  )

(*---------------------------*)

val ERROR_BOUND_LEMMA3 = Q.prove (
  `!x. 1r <= x /\ x < 2 ==>
       ?n. n <= 2 EXP ^fracw_tm /\
           abs ((1 + &n / 2 pow ^fracw_tm) - x) <= inv (2 pow ^sfracw_tm)`,
  REPEAT strip_tac
  \\ Q.SUBGOAL_THEN `0r <= x - 1 /\ x - 1 < 1`
       (assume_tac o MATCH_MP ERROR_BOUND_LEMMA2)
  >- (NTAC 2 (POP_ASSUM mp_tac) \\ REAL_ARITH_TAC)
  \\ metis_tac
       [ABS_NEG, REAL_NEG_SUB, REAL_ARITH ``a - (b - c) = (c + a:real) - b``]
  )

(*---------------------------*)

val ERROR_BOUND_LEMMA4 = Q.prove (
  `!x. 1r <= x /\ x < 2 ==>
       ?e f. abs (Val (float (0,e,f)) - x) <= inv (2 pow ^sfracw_tm) /\
             f < 2 EXP ^fracw_tm /\
             ((e = bias float_format) \/
              (e = SUC (bias float_format)) /\ (f = 0))`,
  gen_tac
  \\ DISCH_TAC
  \\ first_assum (Q.X_CHOOSE_THEN `n` (MP_TAC o REWRITE_RULE [LESS_OR_EQ]) o
                  MATCH_MP ERROR_BOUND_LEMMA3)
  \\ strip_tac
  >- (qexists_tac `bias float_format`
      \\ qexists_tac `n`
      \\ `defloat (float (0,bias float_format,n)) = (0,bias float_format,n)`
      by fs [GSYM float_tybij, is_valid, float_format, bias, expwidth,
             fracwidth]
      \\ fs [Val, valof, bias, expwidth, fracwidth, float_format])
  \\ qexists_tac `SUC (bias float_format)`
  \\ qexists_tac `0`
  \\ `defloat (float (0,SUC (bias float_format),0)) =
      (0,SUC (bias float_format),0)`
  by fs [GSYM float_tybij, is_valid, float_format, bias, expwidth, fracwidth]
  \\ rfs [Val, valof, bias, expwidth, fracwidth, float_format]
  )

(*---------------------------*)

val ERROR_BOUND_LEMMA5 = Q.prove (
  `!x. 1r <= abs x /\ abs x < 2 ==>
       ?s e f. abs (Val (float (s,e,f)) - x) <= inv (2 pow ^sfracw_tm) /\
               s < 2 /\ f < 2 EXP ^fracw_tm /\
               ((e = bias float_format) \/
                (e = SUC (bias float_format)) /\ (f = 0))`,
  gen_tac
  \\ DISCH_TAC
  \\ SUBGOAL_THEN ``1 <= x /\ x < 2 \/ 1 <= ~x /\ ~x < 2``
       (DISJ_CASES_THEN
          (Q.X_CHOOSE_THEN `e` (Q.X_CHOOSE_THEN `f` assume_tac) o
           MATCH_MP ERROR_BOUND_LEMMA4))
  >- (pop_assum mp_tac \\ REAL_ARITH_TAC)
  >| [qexists_tac `0`,
      qexists_tac `1`
      \\ `(defloat (float (1,bias float_format,f)) = (1,bias float_format,f)) /\
          (defloat (float (1,SUC (bias float_format),0)) =
           (1,SUC (bias float_format),0)) /\
          (defloat (float (0,bias float_format,f)) = (0,bias float_format,f)) /\
          (defloat (float (0,SUC (bias float_format),0)) =
           (0,SUC (bias float_format),0))`
      by fs [GSYM float_tybij, is_valid, float_format, bias, expwidth,
             fracwidth]
      ]
  \\ qexists_tac `e`
  \\ qexists_tac `f`
  \\ ntac 2 (fs [Val, valof, bias, expwidth, fracwidth, float_format,
                 REAL_ARITH ``abs (-2 - x) = abs (2 - -x)``,
                 REAL_ARITH ``abs (-1 * y - x) = abs (y - -x)``])
  )

(*---------------------------*)

val REAL_LE_LCANCEL_IMP =
  METIS_PROVE [REAL_LE_LMUL] ``!x y z. 0r < x /\ x * y <= x * z ==> y <= z``

val ERROR_BOUND_LEMMA6 = Q.prove (
  `!x. 0 <= x /\ x < inv (2 pow ^pbias_tm) ==>
       ?n. n <= 2 EXP ^fracw_tm /\
           abs (x - 2 / 2 pow ^bias_tm * &n / 2 pow ^fracw_tm) <=
           inv (2 pow ^bias_frac_tm)`,
  REPEAT strip_tac
  \\ Q.SPEC_THEN `2 pow ^pbias_tm * x` mp_tac ERROR_BOUND_LEMMA2
  \\ Lib.W (Lib.C SUBGOAL_THEN MP_TAC o lhand o lhand o snd)
  >- (conj_tac
      >- (match_mp_tac realTheory.REAL_LE_MUL \\ simp [])
      \\ pop_assum mp_tac
      \\ simp [realTheory.REAL_INV_1OVER, realTheory.lt_ratr])
  \\ DISCH_THEN (fn th => rewrite_tac [th])
  \\ DISCH_THEN (Q.X_CHOOSE_THEN `n` strip_assume_tac)
  \\ qexists_tac `n`
  \\ asm_rewrite_tac []
  \\ qspec_then `2 pow ^pbias_tm` match_mp_tac REAL_LE_LCANCEL_IMP
  \\ conj_tac
  >- EVAL_TAC
  \\ rewrite_tac
      [realTheory.ABS_MUL
       |> GSYM
       |> Q.SPEC `2 pow ^pbias_tm`
       |> REWRITE_RULE [EVAL_PROVE ``abs (2 pow ^pbias_tm) = 2 pow ^pbias_tm``]]
  \\ fs [realTheory.REAL_SUB_LDISTRIB, realTheory.REAL_MUL_ASSOC, real_div]
  \\ pop_assum mp_tac
  \\ EVAL_TAC
  \\ simp []
  )

(*---------------------------*)

val ERROR_BOUND_LEMMA7 = Q.prove (
  `!x. 0 <= x /\ x < inv (2 pow ^pbias_tm) ==>
       ?e f. abs (Val (float (0,e,f)) - x) <= inv (2 pow ^bias_frac_tm) /\
             f < 2 EXP ^fracw_tm /\ ((e = 0) \/ (e = 1) /\ (f = 0))`,
  gen_tac
  \\ DISCH_TAC
  \\ FIRST_ASSUM (Q.X_CHOOSE_THEN `n` MP_TAC o MATCH_MP ERROR_BOUND_LEMMA6)
  \\ DISCH_THEN (CONJUNCTS_THEN2 (strip_assume_tac o REWRITE_RULE [LESS_OR_EQ])
                   ASSUME_TAC)
  >- (qexists_tac `0`
      \\ qexists_tac `n`
      \\ `defloat (float (0,0,n)) = (0,0,n)`
      by fs [GSYM float_tybij, is_valid, float_format, bias, expwidth,
             fracwidth]
      \\ fs [Val, valof, bias, expwidth, fracwidth, float_format]
      \\ simp [Once realTheory.ABS_SUB]
      \\ fs [realTheory.mult_rat, realTheory.mult_ratl,
             Once realTheory.div_ratl])
  \\ qexists_tac `1`
  \\ qexists_tac `0`
  \\ `defloat (float (0,1,0)) = (0,1,0)`
  by fs [GSYM float_tybij, is_valid, float_format, bias, expwidth, fracwidth]
  \\ fs [Val, valof, bias, expwidth, fracwidth, float_format]
  \\ simp [Once realTheory.ABS_SUB]
  \\ rfs [realTheory.mult_rat, realTheory.mult_ratl, Once realTheory.div_ratl]
  )

(*---------------------------*)

val ERROR_BOUND_LEMMA8 = Q.prove (
  `!x. abs x < inv (2 pow ^pbias_tm) ==>
       ?s e f. abs (Val (float(s,e,f)) - x) <= inv (2 pow ^bias_frac_tm) /\
               s < 2 /\ f < 2 EXP ^fracw_tm /\ ((e = 0) \/ (e = 1) /\ (f = 0))`,
  gen_tac
  \\ DISCH_TAC
  \\ SUBGOAL_THEN ``0 <= x /\ x < inv (2 pow ^pbias_tm) \/
                    0 <= ~x /\ ~x < inv (2 pow ^pbias_tm)``
       (DISJ_CASES_THEN
          (Q.X_CHOOSE_THEN `e` (Q.X_CHOOSE_THEN `f` assume_tac) o
           MATCH_MP ERROR_BOUND_LEMMA7))
  >- (pop_assum mp_tac \\ REAL_ARITH_TAC)
  \\ `(defloat (float (0,0,f)) = (0,0,f)) /\
      (defloat (float (0,e,f)) = (0,e,f)) /\
      (defloat (float (0,1,0)) = (0,1,0)) /\
      (defloat (float (1,0,f)) = (1,0,f)) /\
      (defloat (float (1,1,0)) = (1,1,0))`
  by fs [GSYM float_tybij, is_valid, float_format, bias, expwidth, fracwidth]
  >| [qexists_tac `0`, qexists_tac `1`]
  \\ qexists_tac `e`
  \\ qexists_tac `f`
  \\ ntac 2
       (fs [Val, valof, bias, expwidth, fracwidth, float_format,
            REAL_MUL_ASSOC, REAL_ARITH ``abs (y - -x) = abs (-1 * y - x)``])
  )

(*---------------------------*)

val VALOF_SCALE_UP = Q.prove (
  `!s e k f.
      e <> 0 ==>
      (valof float_format (s,e + k,f) = 2 pow k * valof float_format (s,e,f))`,
  simp [valof, REAL_POW_ADD, real_div, AC REAL_MUL_ASSOC REAL_MUL_COMM])

val VALOF_SCALE_DOWN = Q.prove(
  `!s e k f.
      k < e ==> (valof float_format (s,e - k,f) =
                 inv (2 pow k) * valof float_format (s,e,f))`,
  REPEAT strip_tac
  \\ `e - k <> 0 /\ (e = (e - k) + k)` by decide_tac
  \\ pop_assum (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th])))
  \\ simp [VALOF_SCALE_UP, REAL_MUL_ASSOC, REAL_MUL_LINV, POW_NZ]
  )

(*---------------------------*)

val ISFINITE_LEMMA = Q.prove (
  `!s e f. s < 2 /\ e < ^emax_tm /\ f < 2 EXP ^fracw_tm ==>
           Finite (float (s,e,f)) /\ is_valid float_format (s,e,f)`,
  NTAC 4 strip_tac
  \\ `defloat (float (s,e,f)) = (s,e,f)`
  by fs [GSYM float_tybij, is_valid, float_format, expwidth, fracwidth]
  \\ fs [ISFINITE, IS_FINITE_EXPLICIT, is_valid, fraction, exponent, sign,
         float_format, expwidth, fracwidth]
  )

val ERROR_BOUND_BIG1 = Q.prove (
  `!x k. 2 pow k <= abs x /\ abs x < 2 pow SUC k /\
         abs x < threshold float_format ==>
         ?a. Finite a /\ abs (Val a - x) <= 2 pow k / 2 pow ^sfracw_tm`,
  REPEAT strip_tac
  \\ qspec_then `x / 2 pow k` mp_tac ERROR_BOUND_LEMMA5
  \\ Lib.W (Lib.C SUBGOAL_THEN mp_tac o lhand o lhand o snd)
  >- (simp [ABS_DIV, GSYM realTheory.POW_ABS, ABS_N, POW_NZ, REAL_POW_LT,
            REAL_LT_LDIV_EQ, GSYM (CONJUNCT2 pow)]
      \\ match_mp_tac realTheory.REAL_LE_RDIV
      \\ simp [realTheory.REAL_POW_LT])
  \\ DISCH_THEN (fn th => rewrite_tac [th])
  \\ `2 pow k < threshold float_format` by metis_tac [REAL_LET_TRANS]
  \\ `k < ^sbias_tm`
  by (spose_not_then (assume_tac o REWRITE_RULE [NOT_LESS])
      \\ `2r pow ^sbias_tm <= 2 pow k`
      by (match_mp_tac REAL_POW_MONO \\ simp [])
      \\ `2r pow ^sbias_tm < threshold float_format`
      by metis_tac [REAL_LET_TRANS]
      \\ pop_assum mp_tac
      \\ simp [threshold, float_format, emax, bias, expwidth, fracwidth]
      \\ EVAL_TAC)
  \\ strip_tac
  >| [all_tac,
      Cases_on `k = ^bias_tm`
      >- (`defloat (float (s,^sbias_tm,0)) = (s,^sbias_tm,0)`
          by simp [GSYM float_tybij, is_valid, expwidth, fracwidth,
                   float_format, bias]
          \\ spose_not_then kall_tac
          \\ qpat_x_assum `abs xx <= inv (2 pow ^sfracw_tm)`
               (mp_tac o (MATCH_MP (REAL_ARITH
                  ``abs (a - b) <= c ==> abs(a) <= abs(b) + c``)))
          \\ Q.UNDISCH_TAC `abs x < threshold float_format`
          \\ simp [threshold, float_format, emax, bias, expwidth, fracwidth,
                   Val, valof, REAL_ABS_MUL, GSYM POW_ABS, ABS_NEG, ABS_DIV,
                   ABS_N, POW_ONE, lt_ratl, REAL_NOT_LE, REAL_LT_ADD_SUB])
      \\ `e + k < ^emax_tm`
      by fs [threshold, float_format, emax, bias, expwidth, fracwidth]
     ]
  \\ (qexists_tac `float (s,e + k,f)`
      \\ `Finite (float (s,e + k,f)) /\ is_valid float_format (s,e + k,f)`
      by (match_mp_tac ISFINITE_LEMMA \\ simp [bias, float_format, expwidth])
      \\ conj_tac >- asm_rewrite_tac []
      \\ rewrite_tac [Val]
      \\ first_assum (SUBST1_TAC o REWRITE_RULE [float_tybij])
      \\ SUBGOAL_THEN ``e <> 0n``
           (fn th => rewrite_tac [MATCH_MP VALOF_SCALE_UP th])
      >- simp [float_format, bias, expwidth, fracwidth]
      \\ match_mp_tac REAL_LE_LCANCEL_IMP
      \\ qexists_tac `inv (2 pow k)`
      \\ conj_tac
      >- simp [REAL_LT_INV_EQ, REAL_POW_LT]
      \\ `!x. inv (2 pow k) * abs x = abs (inv (2 pow k) * x)`
      by rewrite_tac
           [REAL_ABS_MUL, REAL_ABS_INV, GSYM realTheory.POW_ABS, ABS_N]
      \\ `defloat (float (s,e,f)) = (s,e,f)`
      by fs [GSYM float_tybij, is_valid, expwidth, fracwidth, float_format,
             bias]
      \\ qpat_x_assum `zz <= inv (2 pow ^sfracw_tm)` mp_tac
      \\ simp [REAL_SUB_LDISTRIB, REAL_MUL_ASSOC, real_div, POW_NZ,
               REAL_MUL_LINV, Val]
      \\ simp [AC REAL_MUL_COMM REAL_MUL_ASSOC]
     )
  )

val ERROR_BOUND_BIG = Q.prove (
  `!k x. 2 pow k <= abs x /\ abs x < 2 pow (SUC k) /\
         abs x < threshold float_format ==>
         abs (error x) <= 2 pow k / 2 pow ^sfracw_tm`,
  prove_tac [ERROR_BOUND_BIG1, ERROR_AT_WORST_LEMMA, REAL_LE_TRANS])

(*-----------------------------------------------*)

val ERROR_BOUND_SMALL1 = Q.prove (
  `!x k. inv (2 pow SUC k) <= abs x /\ abs x < inv (2 pow k) /\
         k < ^pbias_tm ==>
         ?a. Finite a /\
             abs (Val a - x) <= inv (2 pow SUC k * 2 pow ^sfracw_tm)`,
  REPEAT strip_tac
  \\ qspec_then `x * 2 pow (SUC k)` mp_tac ERROR_BOUND_LEMMA5
  \\ Lib.W (Lib.C SUBGOAL_THEN mp_tac o lhand o lhand o snd)
  >- (fs [ABS_MUL, GSYM POW_ABS, REAL_INV_1OVER, REAL_LE_LDIV_EQ,
          REAL_LT_RDIV_EQ, REAL_POW_LT]
      \\ simp [pow, REAL_ARITH ``a * (2r * b) < 2 = a * b < 1``])
  \\ DISCH_THEN (fn th => rewrite_tac [th])
  \\ DISCH_THEN
       (Q.X_CHOOSE_THEN `s`
         (Q.X_CHOOSE_THEN `e`
           (Q.X_CHOOSE_THEN `f` (REPEAT_TCL CONJUNCTS_THEN assume_tac))))
  \\ qexists_tac `float (s,e - SUC k,f)`
  \\ `Finite (float (s,e - SUC k,f)) /\ is_valid float_format (s,e - SUC k,f)`
  by (match_mp_tac ISFINITE_LEMMA \\ fs [bias, float_format, expwidth])
  \\ `defloat (float (s,e,f)) = (s,e,f)`
  by fs [GSYM float_tybij, is_valid, expwidth, fracwidth, float_format, bias]
  \\ `SUC k < e` by fs [bias, float_format, expwidth]
  \\ NO_STRIP_FULL_SIMP_TAC std_ss
       [Val, CONJUNCT2 float_tybij, VALOF_SCALE_DOWN]
  \\ match_mp_tac REAL_LE_LCANCEL_IMP
  \\ qexists_tac `2 pow (SUC k)`
  \\ `!x. 2 pow (SUC k) * abs x = abs (2 pow (SUC k) * x)`
  by rewrite_tac [REAL_ABS_MUL, REAL_ABS_INV, GSYM POW_ABS, ABS_N]
  \\ `!a b. 0 < a ==> (a * (inv a * b) = b)`
  by simp [REAL_MUL_ASSOC, REAL_MUL_RINV, REAL_POS_NZ]
  \\ simp [REAL_POW_LT, REAL_SUB_LDISTRIB, REAL_POS_NZ, REAL_INV_MUL]
  \\ NO_STRIP_FULL_SIMP_TAC (srw_ss()) [AC REAL_MUL_ASSOC REAL_MUL_COMM]
  )

val ERROR_BOUND_SMALL = Q.prove (
  `!k x. inv (2 pow (SUC k)) <= abs x /\ abs x < inv (2 pow k) /\
         k < ^pbias_tm ==>
         abs (error x) <= inv (2 pow (SUC k) * 2 pow ^sfracw_tm)`,
  REPEAT strip_tac
  \\ `?a. Finite a /\
          abs (Val a - x) <= inv (2 pow (SUC k) * 2 pow ^sfracw_tm)`
  by simp [ERROR_BOUND_SMALL1]
  \\ match_mp_tac REAL_LE_TRANS
  \\ qexists_tac `abs (Val a - x)`
  \\ simp []
  \\ match_mp_tac ERROR_AT_WORST_LEMMA
  \\ simp []
  \\ match_mp_tac REAL_LT_TRANS
  \\ qexists_tac `inv (2 pow k)`
  \\ simp []
  \\ match_mp_tac REAL_LET_TRANS
  \\ qexists_tac `inv 1`
  \\ conj_tac
  >- (match_mp_tac REAL_LE_INV2 \\ simp [REAL_POW_LE_1])
  \\ simp [threshold, float_format, bias, fracwidth, expwidth, emax]
  \\ EVAL_TAC
  )

(*-----------------------------------------------*)

val ERROR_BOUND_TINY = Q.prove (
  `!x. abs x < inv (2 pow ^pbias_tm) ==>
       abs (error x) <= inv (2 pow ^bias_frac_tm)`,
  REPEAT strip_tac
  \\ `?a. Finite a /\ abs (Val a - x) <= inv (2 pow ^bias_frac_tm)`
  by metis_tac [ERROR_BOUND_LEMMA8, ISFINITE_LEMMA, Val,
                DECIDE ``0 < ^emax_tm /\ 1 < ^emax_tm``]
  \\ match_mp_tac REAL_LE_TRANS
  \\ qexists_tac `abs (Val a - x)`
  \\ simp []
  \\ match_mp_tac ERROR_AT_WORST_LEMMA
  \\ asm_rewrite_tac []
  \\ match_mp_tac REAL_LT_TRANS
  \\ qexists_tac `inv (2 pow ^pbias_tm)`
  \\ asm_rewrite_tac []
  \\ simp [threshold, float_format, bias, emax, expwidth, fracwidth]
  \\ EVAL_TAC
  )

(* -------------------------------------------------------------------------
   Stronger versions not requiring exact location of the interval.
   ------------------------------------------------------------------------- *)

val ERROR_BOUND_NORM_STRONG = Q.store_thm ("ERROR_BOUND_NORM_STRONG",
  `!x j.
    abs x < threshold float_format /\
    abs x < 2 pow (SUC j) / 2 pow ^pbias_tm ==>
    abs (error x) <= 2 pow j / 2 pow ^bias_frac_tm`,
  gen_tac
  \\ Induct
  >- (rw_tac std_ss
        [pow, POW_1, real_div, REAL_MUL_LID, REAL_MUL_RID,
         EVAL_PROVE ``2 * inv (2 pow ^pbias_tm) = inv (2 pow ^ppbias_tm)``]
      \\ Cases_on `abs x < inv (2 pow ^pbias_tm)`
      >- metis_tac [ERROR_BOUND_TINY]
      \\ qspecl_then [`^ppbias_tm`, `x`]
            (match_mp_tac o SIMP_RULE std_ss [GSYM REAL_POW_ADD, ADD1])
            ERROR_BOUND_SMALL
      \\ asm_rewrite_tac [GSYM REAL_NOT_LT])
  \\ strip_tac
  \\ Cases_on `abs x < 2 pow SUC j / 2 pow ^pbias_tm`
  >- (match_mp_tac REAL_LE_TRANS
      \\ qexists_tac `2 pow j / 2 pow ^bias_frac_tm`
      \\ asm_simp_tac std_ss [real_div, pow]
      \\ match_mp_tac realTheory.REAL_LE_RMUL_IMP
      \\ simp_tac std_ss [REAL_LE_INV_EQ, POW_POS, REAL_ARITH ``0 <= 2r``,
                          REAL_ARITH ``0r <= a ==> a <= 2 * a``])
  \\ Cases_on `j <= ^pppbias_tm`
  >- (`?k. ^pppbias_tm - j = k` by prove_tac []
      \\ `inv (2 pow (SUC k + ^sfracw_tm)) = 2 pow SUC j / 2 pow ^bias_frac_tm`
      by (`SUC j + (SUC k + ^sfracw_tm) = ^bias_frac_tm` by decide_tac
          \\ asm_simp_tac std_ss
              [REAL_EQ_RDIV_EQ, REAL_EQ_LDIV_EQ, REAL_POW_LT, REAL_INV_1OVER,
               POW_NZ, mult_ratl, REAL_MUL_LID, GSYM POW_ADD,
               REAL_ARITH ``0 < 2r /\ 0 <> 2r``])
      \\ pop_assum
           (fn th =>
              qspecl_then [`k`, `x`]
                (match_mp_tac o SIMP_RULE std_ss [GSYM REAL_POW_ADD, th])
                ERROR_BOUND_SMALL)
      \\ full_simp_tac arith_ss [REAL_NOT_LT]
      \\ `^pbias_tm = k + SUC (SUC j)` by decide_tac
      \\ conj_tac
      >- (match_mp_tac REAL_LE_TRANS
          \\ qexists_tac `2 pow SUC j / 2 pow ^pbias_tm`
          \\ asm_rewrite_tac []
          \\ rewrite_tac
                [REAL_POW_ADD, pow, real_div,
                 REAL_ARITH ``a * (b * (c * d)) : real = b * a * (c * d)``]
          \\ rewrite_tac [GSYM (CONJUNCT2 pow)]
          \\ simp_tac std_ss
                [REAL_INV_MUL, POW_NZ, REAL_ARITH ``2 <> 0r``, REAL_MUL_RINV,
                 REAL_ARITH ``a * (b * c) : real = a * c * b``, REAL_MUL_LID,
                 REAL_LE_REFL])
      \\ match_mp_tac REAL_LTE_TRANS
      \\ qexists_tac `2 pow SUC (SUC j) / 2 pow ^pbias_tm`
      \\ asm_simp_tac std_ss
           [REAL_LE_LDIV_EQ, REAL_POW_LT, REAL_ARITH ``0r < 2``,
            REAL_POW_ADD, REAL_MUL_ASSOC, REAL_MUL_LINV, POW_NZ,
            REAL_ARITH ``2 <> 0r``, REAL_MUL_LID, REAL_LE_REFL]
     )
  \\ `?i. j = ^ppbias_tm + i` by (qexists_tac `j - ^ppbias_tm` \\ decide_tac)
  \\ assume_tac
       (REAL_DIV_RMUL_CANCEL
        |> Q.SPECL [`2 pow ^pbias_tm`, `a`, `1`]
        |> SIMP_RULE std_ss
             [POW_NZ, REAL_ARITH ``2 <> 0r``, REAL_MUL_LID, REAL_OVER1]
        |> GEN_ALL)
  \\ full_simp_tac arith_ss
       [ADD1, POW_ADD, REAL_NOT_LT,
        POW_ADD
        |> Q.SPECL [`2`, `^pbias_tm`, `^sfracw_tm`]
        |> SIMP_RULE std_ss [],
        REAL_DIV_RMUL_CANCEL
        |> Q.SPEC `2 pow ^pbias_tm`
        |> SIMP_RULE std_ss [POW_NZ, REAL_ARITH ``2 <> 0r``]
        |> CONV_RULE (PATH_CONV "bblrr" (ONCE_REWRITE_CONV [REAL_MUL_COMM]))]
  \\ match_mp_tac ERROR_BOUND_BIG
  \\ full_simp_tac std_ss
        [POW_ADD |> Q.SPECL [`2`, `1`, `^pbias_tm`] |> SIMP_RULE std_ss [],
         REAL_MUL_ASSOC, POW_1,
         pow |> CONJUNCT2 |> ONCE_REWRITE_RULE [REAL_MUL_COMM] |> GSYM]
  )

(* -------------------------------------------------------------------------
   "1 + Epsilon" property (relative error bounding).
   ------------------------------------------------------------------------- *)

val normalizes = Define`
  normalizes x =
  inv (2 pow (bias float_format - 1)) <= abs x /\
  abs x < threshold float_format`

(* ------------------------------------------------------------------------- *)

(* 2 pow (2 EXP ^pbias_tm) is too big to EVAL directly *)
val THRESHOLD_MUL_LT = Q.prove (
  `threshold float_format * 2 pow ^pbias_tm < 2 pow (2 EXP ^pbias_tm)`,
  `2 pow ^pemax_tm * inv (2 pow ^bias_tm) = 2 pow ^bias_tm`
  by simp_tac bool_ss
       [GSYM (EVAL ``^bias_tm + ^bias_tm``), REAL_POW_ADD, REAL_MUL_RINV,
        REAL_MUL_RID, POW_NZ, REAL_ARITH ``2r <> 0``, GSYM REAL_MUL_ASSOC]
  \\ asm_simp_tac std_ss
       [threshold, float_format, emax, bias, fracwidth, expwidth, real_div]
  \\ rewrite_tac
       [GSYM REAL_MUL_ASSOC, REAL_SUB_RDISTRIB, REAL_SUB_LDISTRIB,
        GSYM pow, GSYM POW_ADD]
  \\ rewrite_tac
       [DECIDE
          ``^pbias_tm = ^sfracw_tm + ^(eval [] ``^pbias_tm - ^sfracw_tm``)``,
        REAL_POW_ADD, REAL_ARITH ``a * (b * (c * d)) = a * (b * c) * d : real``]
  \\ simp_tac std_ss
       [REAL_MUL_LINV, POW_NZ, REAL_ARITH ``2r <> 0``, REAL_MUL_RID,
        GSYM REAL_POW_ADD]
  \\ match_mp_tac REAL_LT_TRANS
  \\ qexists_tac `2 pow ^pemax_tm`
  \\ conj_tac >- EVAL_TAC
  \\ match_mp_tac REAL_POW_MONO_LT
  \\ EVAL_TAC
  )

(* ------------------------------------------------------------------------- *)

val LT_THRESHOLD_LT_POW_INV = Q.prove (
  `!x. x < threshold (^expw_tm,^fracw_tm) ==>
       x < 2 pow (emax (^expw_tm,^fracw_tm) - 1) / 2 pow ^pbias_tm`,
  simp [FLOAT_THRESHOLD_EXPLICIT, emax, expwidth, GSYM float_format]
  \\ gen_tac
  \\ match_mp_tac (REAL_ARITH ``b < c ==> (a < b ==> a < c : real)``)
  \\ EVAL_TAC
  )

val REAL_POS_IN_BINADE = Q.prove (
  `!x. normalizes x /\ 0 <= x ==>
       ?j. j <= emax float_format - 2 /\ 2 pow j / 2 pow ^pbias_tm <= x /\
           x < 2 pow (SUC j) / 2 pow ^pbias_tm`,
  rw_tac arith_ss [normalizes, bias, expwidth, float_format, abs]
  \\ qspec_then `\n. 2 pow n / 2 pow ^pbias_tm <= x` mp_tac EXISTS_GREATEST
  \\ Lib.W (Lib.C SUBGOAL_THEN mp_tac o lhs o lhand o snd)
  >- (
      conj_tac
      >- (qexists_tac `0` \\ asm_simp_tac std_ss [REAL_MUL_LID , pow, real_div])
      \\ qexists_tac `2 EXP ^pbias_tm`
      \\ Q.X_GEN_TAC `n`
      \\ rw_tac bool_ss
           [GSYM real_lt, REAL_LT_RDIV_EQ, REAL_POW_LT, REAL_ARITH ``0 < 2r``]
      \\ match_mp_tac REAL_LT_TRANS
      \\ qexists_tac `2 pow (2 EXP ^pbias_tm)`
      \\ conj_tac
      >- metis_tac [THRESHOLD_MUL_LT, REAL_LT_RMUL, REAL_LT_TRANS, float_format,
                    REAL_POW_LT, REAL_ARITH ``0 < 2r``]
      \\ match_mp_tac REAL_POW_MONO_LT
      \\ asm_simp_tac bool_ss [REAL_ARITH ``1 < 2r``, GSYM GREATER_DEF])
  \\ DISCH_THEN (fn th => rewrite_tac [th])
  \\ DISCH_THEN
       (X_CHOOSE_THEN ``n:num``
         (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o Q.SPEC `SUC n`)))
  \\ rw_tac arith_ss [REAL_NOT_LE]
  \\ qexists_tac `n`
  \\ full_simp_tac std_ss [emax, expwidth]
  \\ qpat_x_assum `x < threshold (^expw_tm,^fracw_tm)`
       (assume_tac o MATCH_MP LT_THRESHOLD_LT_POW_INV)
  \\ `2 pow n / 2 pow ^pbias_tm <
      2 pow (emax (^expw_tm,^fracw_tm) - 1) / 2 pow ^pbias_tm`
  by metis_tac [REAL_LET_TRANS]
  \\ spose_not_then assume_tac
  \\ `^pemax_tm <= n` by decide_tac
  \\ `2 pow ^pemax_tm <= 2 pow n`
  by metis_tac [REAL_POW_MONO, REAL_ARITH ``1 <= 2r``]
  \\ full_simp_tac std_ss
       [REAL_LT_RDIV, REAL_POW_LT, REAL_ARITH ``0 < 2r``, real_lte,
        emax, expwidth]
  )

val REAL_NEG_IN_BINADE = Q.prove (
  `!x. normalizes x /\ 0 <= ~x ==>
       ?j. j <= emax float_format - 2 /\ 2 pow j / 2 pow ^pbias_tm <= ~x /\
           ~x < 2 pow (SUC j) / 2 pow ^pbias_tm`,
  metis_tac [normalizes, ABS_NEG, REAL_POS_IN_BINADE])

val REAL_IN_BINADE = Q.store_thm ("REAL_IN_BINADE",
  `!x. normalizes x ==>
       ?j. j <= emax float_format - 2 /\ 2 pow j / 2 pow ^pbias_tm <= abs x /\
           abs x < 2 pow (SUC j) / 2 pow ^pbias_tm`,
  gen_tac
  \\ Cases_on `0 <= x`
  \\ asm_simp_tac arith_ss [abs, REAL_NEG_IN_BINADE, REAL_POS_IN_BINADE,
                            REAL_ARITH ``~(0r <= x) ==> 0 <= ~x``]
  )

(* ------------------------------------------------------------------------- *)

val ERROR_BOUND_NORM_STRONG_NORMALIZE = Q.store_thm (
  "ERROR_BOUND_NORM_STRONG_NORMALIZE",
  `!x. normalizes x ==> ?j. abs (error x) <= 2 pow j / 2 pow ^bias_frac_tm`,
  metis_tac [REAL_IN_BINADE, ERROR_BOUND_NORM_STRONG, normalizes])

(* ------------------------------------------------------------------------- *)

val inv_le = Q.prove(
  `!a b. 0 < a /\ 0 < b ==> (inv a <= inv b = b <= a)`,
  rw [realTheory.REAL_INV_1OVER, realTheory.REAL_LE_LDIV_EQ,
      realTheory.mult_ratl, realTheory.REAL_LE_RDIV_EQ]
  )

val relative_bound_lem = Q.prove(
  `!x j. x <> 0 ==>
         (2 pow j * inv (2 pow ^pbias_tm) <= abs x =
          inv (abs x) <= inv (2 pow j * inv (2 pow ^pbias_tm)))`,
  REPEAT strip_tac
  \\ match_mp_tac (GSYM inv_le)
  \\ asm_simp_tac std_ss [REAL_ARITH ``x <> 0 ==> 0 < abs x``]
  \\ match_mp_tac realTheory.REAL_LT_MUL
  \\ simp_tac std_ss [realTheory.REAL_POW_LT, realTheory.REAL_LT_INV_EQ,
                      REAL_ARITH ``0 < 2r``]
  )

val inv_mul = Q.prove(
  `!a b. a <> 0 /\ b <> 0 ==> (inv (a * inv b) = b / a)`,
  rw [realTheory.REAL_INV_MUL, realTheory.REAL_INV_NZ, realTheory.REAL_INV_INV]
  \\ simp [realTheory.REAL_INV_1OVER, realTheory.mult_ratl]
  )

val RELATIVE_ERROR_ZERO = Q.prove(
  `!x. normalizes  x /\ (x = 0) ==>
       ?e. abs e <= 1 / 2 pow ^sfracw_tm /\
           (Val (float (round float_format To_nearest x)) = x * (1 + e))`,
  rw []
  \\ qexists_tac `0`
  \\ qspec_then `0`
       (fn th => simp [REWRITE_RULE [realTheory.REAL_SUB_RZERO] th])
       (GSYM error)
  \\ match_mp_tac ERROR_IS_ZERO
  \\ qexists_tac `float (0, 0, 0)`
  \\ `defloat (float (0, 0, 0)) = (0, 0, 0)`
  by simp [GSYM float_tybij, is_valid, float_format, expwidth, fracwidth]
  \\ simp [Finite, Iszero, is_zero, exponent, fraction, Val, valof]
  )

val RELATIVE_ERROR = Q.store_thm ("RELATIVE_ERROR",
  `!x. normalizes x ==>
       ?e. abs e <= 1 / 2 pow ^sfracw_tm /\
           (Val (float (round float_format To_nearest x)) = x * (1 + e))`,
  REPEAT strip_tac
  \\ Cases_on `x = 0r` >- metis_tac [RELATIVE_ERROR_ZERO]
  \\ `x < 0r \/ 0 < x` by (POP_ASSUM MP_TAC \\ REAL_ARITH_TAC)
  \\ (qspec_then `x` mp_tac REAL_IN_BINADE
      \\ rw_tac std_ss []
      \\ full_simp_tac std_ss [normalizes]
      \\ qspecl_then [`x`,`j`] MP_TAC ERROR_BOUND_NORM_STRONG
      \\ rw_tac std_ss []
      \\ `2 pow j * inv (2 pow ^pbias_tm) <= abs x =
          inv (abs x) <= inv (2 pow j * inv (2 pow ^pbias_tm))`
      by metis_tac [relative_bound_lem]
      \\ Q.UNDISCH_TAC `2 pow j / 2 pow ^pbias_tm <= abs x`
      \\ asm_simp_tac std_ss [real_div]
      \\ rw_tac std_ss []
      \\ `0 <= inv (abs x)` by simp [REAL_LE_INV_EQ, ABS_POS]
      \\ qspec_then `(error x):real` assume_tac ABS_POS
      \\ qspecl_then
           [`abs (error x)`, `2 pow j / 2 pow ^bias_frac_tm`, `inv (abs x)`,
            `inv (2 pow j * inv (2 pow ^pbias_tm))`] mp_tac REAL_LE_MUL2
      \\ asm_simp_tac std_ss []
      \\ strip_tac
      \\ qexists_tac `error x * inv x`
      \\ conj_tac
      >- (simp_tac std_ss [realTheory.ABS_MUL, realTheory.REAL_MUL_LID]
          \\ match_mp_tac realTheory.REAL_LE_TRANS
          \\ qexists_tac `2 pow j / 2 pow ^bias_frac_tm *
                          inv (2 pow j * inv (2 pow ^pbias_tm))`
          \\ asm_simp_tac std_ss [realTheory.ABS_INV]
          \\ simp_tac std_ss
               [inv_mul, realTheory.POW_NZ, REAL_ARITH ``2 <> 0r``,
                realTheory.REAL_POS_NZ, realTheory.REAL_INV_NZ,
                realTheory.REAL_DIV_OUTER_CANCEL]
          \\ EVAL_TAC
         )
      \\ asm_simp_tac std_ss
           [error, REAL_LDISTRIB, REAL_MUL_RID, REAL_MUL_RINV,
            REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB, REAL_MUL_LID, REAL_SUB_ADD2,
            REAL_ARITH ``x * (Val qq * inv x) = (x * inv x) * Val qq``])
  )

(* -------------------------------------------------------------------------
   We also want to ensure that the result is actually finite!
   ------------------------------------------------------------------------- *)

val DEFLOAT_FLOAT_ZEROSIGN_ROUND_FINITE = Q.store_thm (
  "DEFLOAT_FLOAT_ZEROSIGN_ROUND_FINITE",
  `!b x. abs x < threshold float_format ==>
         is_finite float_format
           (defloat (float (zerosign float_format b
                              (round float_format To_nearest x))))`,
  rw [round_def, REAL_ARITH ``abs x < y = ~(x <= ~y) /\ ~(x >= y)``]
  \\ `is_finite float_format
         (zerosign float_format b
            (closest (valof float_format) (\a. EVEN (fraction a))
             {a | is_finite float_format a} x))`
  by (rw [zerosign, IS_FINITE_CLOSEST]
      \\ simp [IS_FINITE_EXPLICIT, plus_zero, minus_zero, float_format,
               sign, exponent, fraction])
  \\ metis_tac [is_finite, float_tybij]
  )

(* -------------------------------------------------------------------------
   Lifting of arithmetic operations.
   ------------------------------------------------------------------------- *)

val Val_FLOAT_ROUND_VALOF = Q.prove (
  `!x. Val (float (round float_format To_nearest x)) =
       valof float_format (round float_format To_nearest x)`,
  simp [Val, DEFLOAT_FLOAT_ROUND])

val lift_arith_tac =
  REPEAT gen_tac \\ strip_tac
  \\ `~Isnan a /\ ~Infinity a /\ ~Isnan b /\ ~Infinity b`
  by metis_tac [FLOAT_DISTINCT_FINITE]
  \\ imp_res_tac RELATIVE_ERROR
  \\ full_simp_tac real_ss
       [ISFINITE, Isnan, Infinity, Isnormal, Isdenormal, Iszero, Val, error,
        float_add, fadd, float_sub, fsub, float_mul, fmul, float_div, fdiv,
        VALOF_DEFLOAT_FLOAT_ZEROSIGN_ROUND, DEFLOAT_FLOAT_ROUND,
        DEFLOAT_FLOAT_ZEROSIGN_ROUND_FINITE, normalizes]
  \\ metis_tac [Val_FLOAT_ROUND_VALOF]

val FLOAT_ADD = Q.store_thm ("FLOAT_ADD",
  `!a b.
    Finite a /\ Finite b /\ abs (Val a + Val b) < threshold float_format ==>
    Finite (a + b) /\ (Val (a + b) = Val a + Val b + error (Val a + Val b))`,
  lift_arith_tac)

val FLOAT_SUB = Q.store_thm ("FLOAT_SUB",
  `!a b.
    Finite a /\ Finite b /\ abs (Val a - Val b) < threshold float_format ==>
    Finite (a - b) /\ (Val (a - b) = Val a - Val b + error (Val a - Val b))`,
  lift_arith_tac)

val FLOAT_MUL = Q.store_thm ("FLOAT_MUL",
  `!a b.
    Finite a /\ Finite b /\ abs (Val a * Val b) < threshold float_format ==>
    Finite (a * b) /\ (Val (a * b) = Val a * Val b + error (Val a * Val b))`,
  lift_arith_tac)

val FLOAT_DIV = Q.store_thm ("FLOAT_DIV",
  `!a b.
    Finite a /\ Finite b /\ ~Iszero b /\
    abs (Val a / Val b) < threshold float_format ==>
    Finite (a / b) /\ (Val (a / b) = Val a / Val b + error (Val a / Val b))`,
  lift_arith_tac)

(*-----------------------*)

val finite_rule =
   Q.GENL [`b`, `a`] o
   MATCH_MP (DECIDE ``(a /\ b /\ c ==> d /\ e) ==> (a /\ b /\ c ==> d)``) o
   Drule.SPEC_ALL

val FLOAT_ADD_FINITE = save_thm ("FLOAT_ADD_FINITE", finite_rule FLOAT_ADD)
val FLOAT_SUB_FINITE = save_thm ("FLOAT_SUB_FINITE", finite_rule FLOAT_SUB)
val FLOAT_MUL_FINITE = save_thm ("FLOAT_MUL_FINITE", finite_rule FLOAT_MUL)

(*-----------------------*)

val FLOAT_ADD_RELATIVE = Q.store_thm ("FLOAT_ADD_RELATIVE",
  `!a b.
     Finite a /\ Finite b /\ normalizes (Val a + Val b) ==>
     Finite (a + b) /\
     ?e. abs e <= 1 / 2 pow ^sfracw_tm /\
         (Val (a + b) = (Val a + Val b) * (1 + e))`,
  lift_arith_tac)

val FLOAT_SUB_RELATIVE = Q.store_thm ("FLOAT_SUB_RELATIVE",
  `!a b.
     Finite a /\ Finite b /\ normalizes (Val a - Val b) ==>
     Finite (a - b) /\
     ?e. abs e <= 1 / 2 pow ^sfracw_tm /\
         (Val (a - b) = (Val a - Val b) * (1 + e))`,
  lift_arith_tac)

val FLOAT_MUL_RELATIVE = Q.store_thm ("FLOAT_MUL_RELATIVE",
  `!a b.
     Finite a /\ Finite b /\ normalizes (Val a * Val b) ==>
     Finite (a * b) /\
     ?e. abs e <= 1 / 2 pow ^sfracw_tm /\
         (Val (a * b) = (Val a * Val b) * (1 + e))`,
  lift_arith_tac)

val FLOAT_DIV_RELATIVE = Q.store_thm ("FLOAT_DIV_RELATIVE",
  `!a b.
     Finite a /\ Finite b /\ ~Iszero b /\ normalizes (Val a / Val b) ==>
     Finite (a / b) /\
     ?e. abs e <= 1 / 2 pow ^sfracw_tm /\
         (Val (a / b) = (Val a / Val b) * (1 + e))`,
  lift_arith_tac)

(*---------------------------------------------------------------------------*)

val _ = export_theory()
