(* ------------------------------------------------------------------------
   Some basic properties of IEEE-754 (base 2) floating-point arithmetic
   ------------------------------------------------------------------------ *)

open HolKernel boolLib bossLib
open binary_ieeeTheory realTheory wordsLib realLib

val () = new_theory "lift_ieee"

val () =  Parse.temp_overload_on ("bias", ``words$INT_MAX``)

(* ------------------------------------------------------------------------ *)

val error_def = Define`
  error (:'t # 'w) x =
  float_to_real (round roundTiesToEven x : ('t, 'w) float) - x`

val normalizes_def = Define`
  normalizes (:'t # 'w) x =
  1 < bias (:'w) /\
  inv (2 pow (bias (:'w) - 1)) <= abs x /\ abs x < threshold (:'t # 'w)`

(* ------------------------------------------------------------------------
     Lifting comparison operations
   ------------------------------------------------------------------------ *)

val float_lt = Q.store_thm ("float_lt",
  `!x y. float_is_finite x /\ float_is_finite y ==>
         (float_less_than x y = float_to_real x < float_to_real y)`,
  rw [float_less_than_def, float_compare_def, float_is_finite_def,
      float_value_def]
  \\ rw []
  );

val float_le = Q.store_thm ("float_le",
  `!x y. float_is_finite x /\ float_is_finite y ==>
         (float_less_equal x y = float_to_real x <= float_to_real y)`,
  rw [float_less_equal_def, float_compare_def, float_is_finite_def,
      float_value_def]
  \\ rw [realTheory.REAL_LT_IMP_LE,
         realLib.REAL_ARITH ``~(a < b : real) /\ a <> b ==> ~(a <= b)``]
  );

val float_gt = Q.store_thm ("float_gt",
  `!x y. float_is_finite x /\ float_is_finite y ==>
         (float_greater_than x y = float_to_real x > float_to_real y)`,
  rw [float_greater_than_def, float_compare_def, float_is_finite_def,
      float_value_def]
  \\ rw [realLib.REAL_ARITH ``a < b : real ==> ~(a > b)``,
         realLib.REAL_ARITH ``~(a < b : real) /\ a <> b ==> a > b``,
         realLib.REAL_ARITH ``~(a > a : real)``]
  );

val float_ge = Q.store_thm ("float_ge",
  `!x y. float_is_finite x /\ float_is_finite y ==>
         (float_greater_equal x y = float_to_real x >= float_to_real y)`,
  rw [float_greater_equal_def, float_compare_def, float_is_finite_def,
      float_value_def]
  \\ rw [realLib.REAL_ARITH ``a < b : real ==> ~(a >= b)``,
         realLib.REAL_ARITH ``~(a < b : real) /\ a <> b ==> a >= b``,
         realLib.REAL_ARITH ``a >= a : real``]
  );

val float_eq = Q.store_thm ("float_eq",
  `!x y. float_is_finite x /\ float_is_finite y ==>
         (float_equal x y = (float_to_real x = float_to_real y))`,
  rw [float_equal_def, float_compare_def, float_is_finite_def,
      float_value_def]
  \\ rw [realLib.REAL_ARITH ``a < b : real ==> a <> b``]
  );

val float_eq_refl = Q.store_thm ("float_eq_refl",
  `!x. float_equal x x = ~float_is_nan x`,
  rw [float_equal_def, float_is_nan_def, float_compare_def, float_is_finite_def,
      float_value_def]
  );


(* ------------------------------------------------------------------------
     Closest
   ------------------------------------------------------------------------ *)

val is_closest_exits = Q.store_thm("is_closest_exits",
  `!x s. FINITE s ==> s <> EMPTY ==> ?a. is_closest s x a`,
  strip_tac
  \\ HO_MATCH_MP_TAC pred_setTheory.FINITE_INDUCT
  \\ simp [pred_setTheory.NOT_INSERT_EMPTY]
  \\ strip_tac
  \\ Cases_on `s = EMPTY`
  >- simp [is_closest_def]
  \\ Cases_on `FINITE s`
  \\ rw []
  \\ Cases_on `abs (float_to_real a - x) <= abs (float_to_real e - x)`
  \\ fs [is_closest_def]
  >- (qexists_tac `a` \\ rw [] \\ simp [])
  \\ qexists_tac `e`
  \\ rw []
  >- simp []
  \\ qpat_x_assum `!b. P` (qspec_then `b` mp_tac)
  \\ qpat_x_assum `~(abs (float_to_real a - x) <=
                     abs (float_to_real e - x))` mp_tac
  \\ simp []
  \\ REAL_ARITH_TAC
  );

val closest_is_everything = Q.store_thm("closest_is_everything",
  `!p s x. FINITE s ==> s <> EMPTY ==>
           is_closest s x (closest_such p s x) /\
           ((?b. is_closest s x b /\ p b) ==> p (closest_such p s x))`,
  rw [closest_such_def]
  \\ SELECT_ELIM_TAC
  \\ metis_tac [is_closest_exits]
  );

val closest_in_set = Q.store_thm("closest_in_set",
  `!p s x. FINITE s ==> s <> EMPTY ==> closest_such p s x IN s`,
  metis_tac [closest_is_everything, is_closest_def]
  );

val closest_is_closest = Q.store_thm("closest_is_closest",
  `!p s x. FINITE s ==> s <> EMPTY ==> is_closest s x (closest_such p s x)`,
  metis_tac [closest_is_everything]
  );

(* ------------------------------------------------------------------------

   ------------------------------------------------------------------------ *)

val finite_word_cross = Q.prove(
   `FINITE (univ (:word1) CROSS univ (:'t word) CROSS univ (:'w word))`,
   metis_tac [pred_setTheory.FINITE_CROSS, wordsTheory.WORD_FINITE]
   );

val inj_float_to_tuple = Q.prove(
  `INJ (\x. ((x.Sign, x.Significand), x.Exponent))
     (univ (:('t, 'w) float))
     (univ (:word1) CROSS univ (:'t word) CROSS univ (:'w word))`,
   rw [pred_setTheory.INJ_DEF, float_component_equality]
   );

val float_finite = Q.store_thm("float_finite",
  `FINITE (univ (:('t, 'w) float))`,
  metis_tac [pred_setTheory.FINITE_INJ, inj_float_to_tuple, finite_word_cross]
  );

val is_finite_finite = Q.store_thm("is_finite_finite",
  `FINITE {a | float_is_finite a}`,
  metis_tac [pred_setTheory.SUBSET_FINITE, float_finite,
             pred_setTheory.SUBSET_UNIV]
  );

val is_finite_nonempty = Q.store_thm("is_finite_nonempty",
  `{a | float_is_finite a} <> EMPTY`,
  rw [pred_setTheory.EXTENSION]
  \\ qexists_tac `float_plus_zero (:'a # 'b)`
  \\ simp [binary_ieeeTheory.zero_properties]
  );

val is_finite_closest = Q.store_thm("is_finite_closest",
  `!p x. float_is_finite (closest_such p {a | float_is_finite a} x)`,
  rpt strip_tac
  \\ `closest_such p {a | float_is_finite a} x IN {a | float_is_finite a}`
  by metis_tac [closest_in_set, is_finite_finite, is_finite_nonempty]
  \\ fs []
  );

(* ------------------------------------------------------------------------

   ------------------------------------------------------------------------ *)

val REAL_ABS_INV = Q.prove(
  `!x. abs (inv x) = inv (abs x)`,
  gen_tac
  \\ Cases_on `x = 0r`
  \\ simp [REAL_INV_0, REAL_ABS_0, ABS_INV]
  );

val REAL_ABS_DIV = Q.prove(
  `!x y. abs (x / y) = abs x / abs y`,
  rewrite_tac [real_div, REAL_ABS_INV, REAL_ABS_MUL])

val REAL_LE_LDIV2 = Q.prove(
  `!x y z. 0r < z ==> (x / z <= y / z <=> x <= y)`,
  simp [REAL_LE_LDIV_EQ, REAL_DIV_RMUL, REAL_POS_NZ]
  );

val REAL_POW_LE_1 = Q.prove(
  `!n x. 1r <= x ==> 1 <= x pow n`,
  Induct
  \\ rw [pow]
  \\ Ho_Rewrite.GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID]
  \\ match_mp_tac REAL_LE_MUL2
  \\ simp []
  );

val REAL_POW_MONO = Q.prove(
  `!m n x. 1r <= x /\ m <= n ==> x pow m <= x pow n`,
  rw [arithmeticTheory.LESS_EQ_EXISTS]
  \\ simp [REAL_POW_ADD]
  \\ Ho_Rewrite.GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID]
  \\ metis_tac [REAL_LE_LMUL_IMP, REAL_POW_LE_1, POW_POS, REAL_LE_TRANS,
                REAL_LE_01]
  );

val exponent_le = Q.prove(
  `!e : 'a word. e <> -1w ==> (w2n e <= UINT_MAX (:'a) - 1)`,
  simp_tac std_ss
    [wordsTheory.WORD_NEG_1, wordsTheory.UINT_MAX_def, wordsTheory.word_T_def]
  \\ Cases
  \\ simp []
  );

val float_to_real_finite = Q.store_thm("float_to_real_finite",
  `!x : ('t, 'w) float.
     float_is_finite x ==> (abs (float_to_real x) <= largest (:'t # 'w))`,
  Cases
  \\ rename [`float s e f`]
  \\ `float s e f = <| Sign := s; Exponent := e; Significand := f |>`
  by simp [float_component_equality]
  \\ `0 <= 1 + &w2n f / 2 pow dimindex (:'t)`
  by (Cases_on `w2n f = 0`
      \\ simp [REAL_ARITH ``0r < x ==> 0 <= 1 + x``, REAL_LT_RDIV_0])
  \\ `abs (1 + &w2n f / 2 pow dimindex (:'t)) =
           1 + &w2n f / 2 pow dimindex (:'t)`
  by simp [ABS_REFL]
  \\ rw [float_tests, largest, float_to_real_def, GSYM POW_ABS,
         REAL_ABS_MUL, REAL_ABS_DIV, ABS_NEG, ABS_N, POW_ONE, mult_rat,
         GSYM REAL_OF_NUM_POW, REAL_LE_LDIV2, wordsTheory.dimword_def,
         ONCE_REWRITE_RULE [REAL_MUL_COMM] mult_ratr]
  >- (
      simp [largest_def, REAL_LE_RDIV_EQ, mult_ratl]
      \\ CONV_TAC (PATH_CONV "lrr" (ONCE_REWRITE_CONV [REAL_MUL_COMM]))
      \\ simp [REAL_DIV_RMUL_CANCEL, REAL_LE_LDIV_EQ,
               REAL_ARITH ``a * (b - c) * d = a * (b * d - c * d) : real``,
               GSYM REAL_OF_NUM_POW, REAL_DIV_RMUL]
      \\ simp [REAL_SUB_LDISTRIB, REAL_LE_SUB_LADD]
      \\ qabbrev_tac `u = UINT_MAX (:'w) - 1`
      \\ `2 pow u * (2 * 2 pow dimindex (:'t)) =
          2 pow u * (2 pow dimindex (:'t) - 1) +
          2 pow u * (2 pow dimindex (:'t) - 1) +
          2 * 2 pow u`
      by (simp [REAL_SUB_LDISTRIB,
                realLib.REAL_ARITH ``a * (2r * b) = a * b + a * b``,
                realLib.REAL_ARITH ``2 * 2 pow x = 2 pow x + 2 pow x``]
          \\ REAL_ARITH_TAC)
      \\ pop_assum SUBST1_TAC
      \\ once_rewrite_tac [GSYM REAL_MUL]
      \\ simp_tac std_ss [realLib.REAL_ARITH ``2r * a = a + a``]
      \\ match_mp_tac realTheory.REAL_LE_ADD2
      \\ conj_tac
      >- (
          match_mp_tac realTheory.REAL_LE_ADD2
          \\ simp []
          \\ match_mp_tac
               (realTheory.REAL_LE_MUL2
                |> Q.SPEC `1`
                |> SIMP_RULE (srw_ss()) [])
          \\ simp
               [REAL_OF_NUM_POW, REAL_SUB, GSYM wordsTheory.dimword_def,
                DECIDE ``a <= 1n = ~(1 < a)``, wordsTheory.w2n_lt,
                DECIDE ``a < n /\ 1n < n ==> a <= n - 1``,
                REAL_POW_LE_1
                |> Q.SPECL [`n`, `2`]
                |> SIMP_RULE (srw_ss()) []]
         )
      \\ simp [REAL_ARITH ``0r < a ==> a <= a + a``]
     )
  \\ match_mp_tac REAL_LE_MUL2
  \\ simp [REAL_POW_MONO, exponent_le, REAL_LE_SUB_LADD]
  \\ simp_tac std_ss [GSYM REAL_ADD_ASSOC, REAL_DIV_ADD]
  \\ match_mp_tac (realLib.REAL_ARITH ``(x:real) <= 1 ==> (1 + x <= 2)``)
  \\ simp [REAL_LE_LDIV_EQ, REAL_OF_NUM_POW, GSYM wordsTheory.dimword_def,
           wordsTheory.w2n_lt, DECIDE ``a < n ==> a + 1n <= n``]
  );

val float_to_real_threshold = Q.store_thm("float_to_real_threshold",
  `!x : ('t, 'w) float.
     float_is_finite x ==> (abs (float_to_real x) < threshold (:'t # 'w))`,
  metis_tac [REAL_LET_TRANS, float_to_real_finite, largest_lt_threshold]
  );

(* ------------------------------------------------------------------------
     Lifting up of rounding to nearest
   ------------------------------------------------------------------------ *)

val bound_at_worst_lemma = Q.prove(
  `!a : ('t, 'w) float x.
      abs x < threshold (:'t # 'w) /\ float_is_finite a ==>
      abs (float_to_real (round roundTiesToEven x : ('t, 'w) float) - x) <=
      abs (float_to_real a - x)`,
  rw [round_def, REAL_ARITH ``abs x < y = ~(x <= ~y) /\ ~(x >= y)``]
  \\ match_mp_tac
       (is_finite_finite
        |> MATCH_MP closest_is_closest
        |> Q.SPECL [`\a. ~word_lsb a.Significand`, `x`]
        |> REWRITE_RULE [is_finite_nonempty, is_closest_def,
                         pred_setTheory.GSPEC_ETA]
        |> CONJUNCT2)
  \\ simp [pred_setTheory.SPECIFICATION]
  );

val error_at_worst_lemma = Q.store_thm("error_at_worst_lemma",
  `!a : ('t, 'w) float x.
      abs x < threshold (:'t # 'w) /\ float_is_finite a ==>
      abs (error (:'t # 'w) x) <= abs (float_to_real a - x)`,
  simp [error_def, bound_at_worst_lemma])

val error_is_zero = Q.store_thm("error_is_zero",
  `!a : ('t, 'w) float x.
     float_is_finite a /\ (float_to_real a = x) ==> (error (:'t # 'w) x = 0)`,
  rw []
  \\ match_mp_tac
       (error_at_worst_lemma
        |> Q.SPECL [`a : ('t, 'w) float`, `float_to_real (a : ('t, 'w) float)`]
        |> SIMP_RULE (srw_ss())
             [REAL_ABS_0, REAL_ARITH ``abs x <= 0 = (x = 0r)``])
  \\ simp [float_to_real_threshold]
  );

(* ------------------------------------------------------------------------ *)

val lem = Q.prove(
  `!a b. 0 < b /\ b < a ==> 1 < a / b : real`,
  simp [realTheory.REAL_LT_RDIV_EQ]
  );

val lem2 = Q.prove(
  `!n x. 0r < n /\ n <= n * x ==> 1 <= x`,
  rpt strip_tac
  \\ spose_not_then assume_tac
  \\ qpat_x_assum `n <= n * x` mp_tac
  \\ fs [realTheory.REAL_NOT_LE,
         GSYM (ONCE_REWRITE_RULE [REAL_MUL_COMM] realTheory.REAL_LT_RDIV_EQ),
         realTheory.REAL_DIV_REFL, realTheory.REAL_POS_NZ]
  );

val error_bound_lemma1 = Q.prove(
  `!fracw x.
       0r <= x /\ x < 1 /\ 0 < fracw ==>
       ?n. n < 2n EXP fracw /\ &n / 2 pow fracw <= x /\
           x < &(SUC n) / 2 pow fracw`,
  rpt strip_tac
  \\ qspec_then `\n. &n / 2 pow fracw <= x` mp_tac
       arithmeticTheory.EXISTS_GREATEST
  \\ simp []
  \\ Lib.W (Lib.C SUBGOAL_THEN (fn th => rewrite_tac [th]) o lhs o lhand o snd)
  >- (conj_tac
      >- (qexists_tac `0n` \\ simp [])
      \\ qexists_tac `2 ** fracw`
      \\ rw [REAL_LE_LDIV_EQ]
      \\ fs [realTheory.REAL_NOT_LE, realTheory.real_gt,
             GSYM realTheory.REAL_LT_RDIV_EQ]
      \\ `1 < &y / 2 pow fracw`
      by (match_mp_tac lem \\ simp [realTheory.REAL_OF_NUM_POW])
      \\ metis_tac [realTheory.REAL_LT_TRANS]
     )
  \\ disch_then (Q.X_CHOOSE_THEN `n` strip_assume_tac)
  \\ pop_assum (qspec_then `SUC n` assume_tac)
  \\ qexists_tac `n`
  \\ fs [REAL_NOT_LE]
  \\ fs [REAL_LE_LDIV_EQ]
  \\ spose_not_then assume_tac
  \\ `2 pow fracw <= &n` by simp [realTheory.REAL_OF_NUM_POW]
  \\ `2 pow fracw <= x * 2 pow fracw`
  by imp_res_tac realTheory.REAL_LE_TRANS
  \\ metis_tac [binary_ieeeTheory.zero_lt_twopow, REAL_MUL_COMM, lem2,
                realTheory.real_lt]
  );

(* ------------------------------------------------------------------------ *)

val error_bound_lemma2 = Q.prove(
  `!fracw x.
      0r <= x /\ x < 1 /\ 0 < fracw ==>
      ?n. n <= 2 EXP fracw /\
          abs (x - &n / 2 pow fracw) <= inv (2 pow (fracw + 1))`,
  ntac 2 gen_tac
  \\ disch_then
       (fn th => Q.X_CHOOSE_THEN `n` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)
                   (MATCH_MP error_bound_lemma1 th)
        \\ strip_assume_tac th)
  \\ disch_then (mp_tac o Q.SPEC `inv (2 pow (fracw + 1))` o MATCH_MP
       (REAL_ARITH ``!a:real b x d. a <= x /\ x < b ==> b <= a + 2 * d ==>
                                    abs (x - a) <= d \/ abs (x - b) <= d``))
  \\ Lib.W (Lib.C SUBGOAL_THEN
              (fn th => rewrite_tac [th]) o lhand o lhand o snd)
  >- simp [realTheory.REAL_LE_LDIV_EQ, realTheory.REAL_RDISTRIB,
           realTheory.REAL_DIV_RMUL, realTheory.REAL_MUL_LINV,
           realTheory.REAL_POW_ADD,
           REAL_ARITH ``a * inv (b * a) * b = inv (b * a) * (b * a)``]
  \\ rw []
  >- (qexists_tac `n` \\ fs [])
  \\ qexists_tac `SUC n`
  \\ fs []
  );

(* ------------------------------------------------------------------------ *)

val error_bound_lemma3 = Q.prove(
  `!fracw x.
       1r <= x /\ x < 2 /\ 0 < fracw ==>
       ?n. n <= 2 EXP fracw /\
           abs ((1 + &n / 2 pow fracw) - x) <= inv (2 pow (fracw + 1))`,
  rpt strip_tac
  \\ Q.SUBGOAL_THEN `0r <= x - 1 /\ x - 1 < 1 /\ 0 < fracw`
       (assume_tac o MATCH_MP error_bound_lemma2)
  >- (simp []
      \\ pop_assum kall_tac
      \\ ntac 2 (POP_ASSUM mp_tac)
      \\ REAL_ARITH_TAC
     )
  \\ metis_tac
       [ABS_NEG, REAL_NEG_SUB, REAL_ARITH ``a - (b - c) = (c + a:real) - b``]
  );

(* ------------------------------------------------------------------------ *)

val two_pow_over_pre = Q.prove(
   `!n. 0 < n ==> (2 pow n / 2 pow (n - 1) = 2)`,
   rpt strip_tac
   \\ imp_res_tac arithmeticTheory.LESS_ADD_1
   \\ fs [POW_ADD,
          realTheory.REAL_DIV_LMUL_CANCEL
          |> Q.SPECL [`2 pow n`, `2`, `1`]
          |> SIMP_RULE (srw_ss()) []]
   );

val error_bound_lemma4 = Q.prove(
  `!x. 1r <= x /\ x < 2 /\ 1 < dimindex (:'w) ==>
       ?e f.
         abs (float_to_real <| Sign := 0w;
                               Exponent := e : 'w word;
                               Significand := f : 't word |> - x) <=
         inv (2 pow (dimindex (:'t) + 1)) /\
         ((e = n2w (bias (:'w))) \/ (e = n2w (INT_MIN (:'w))) /\ (f = 0w))`,
  gen_tac
  \\ DISCH_TAC
  \\ Q.SUBGOAL_THEN `1 <= x /\ x < 2 /\ 0 < dimindex (:'t)` assume_tac
  >- simp []
  \\ first_assum
        (Q.X_CHOOSE_THEN `n`
           (MP_TAC o REWRITE_RULE [arithmeticTheory.LESS_OR_EQ]) o
           MATCH_MP error_bound_lemma3)
  \\ strip_tac
  >- (qexists_tac `n2w (bias (:'w))`
      \\ qexists_tac `n2w n`
      \\ fs [float_to_real_def, wordsTheory.INT_MAX_LT_DIMWORD,
             GSYM wordsTheory.dimword_def, wordsTheory.ZERO_LT_INT_MAX,
             realTheory.REAL_DIV_REFL, DECIDE ``0 < x ==> x <> 0n``]
     )
  \\ qexists_tac `n2w (INT_MIN (:'w))`
  \\ qexists_tac `0w`
  \\ rfs [float_to_real_def, GSYM realTheory.REAL_OF_NUM_POW, two_pow_over_pre,
          realTheory.REAL_DIV_REFL, wordsTheory.INT_MAX_def,
          wordsTheory.INT_MIN_LT_DIMWORD, DECIDE ``0 < x ==> x <> 0n``]
  );

(* ------------------------------------------------------------------------ *)

val error_bound_lemma5 = Q.prove(
  `!x. 1r <= abs x /\ abs x < 2 /\ 1 < dimindex (:'w) ==>
       ?s e f.
         abs (float_to_real <| Sign := s;
                               Exponent := e : 'w word;
                               Significand := f : 't word |> - x) <=
         inv (2 pow (dimindex (:'t) + 1)) /\
         ((e = n2w (bias (:'w))) \/ (e = n2w (INT_MIN (:'w))) /\ (f = 0w))`,
  gen_tac
  \\ DISCH_TAC
  \\ SUBGOAL_THEN ``1 <= (x:real) /\ x < 2 /\ 1 < dimindex (:'w) \/
                    1 <= ~x /\ ~x < 2 /\ 1 < dimindex (:'w)``
       (DISJ_CASES_THEN
          (Q.X_CHOOSE_THEN `e` (Q.X_CHOOSE_THEN `f` assume_tac) o
           MATCH_MP error_bound_lemma4))
  >- (simp [] \\ pop_assum mp_tac \\ REAL_ARITH_TAC)
  >| [qexists_tac `0w`, qexists_tac `1w`]
  \\ qexists_tac `e`
  \\ qexists_tac `f`
  \\ ntac 2 (fs [float_to_real_def, wordsTheory.INT_MAX_LT_DIMWORD,
                 wordsTheory.INT_MIN_LT_DIMWORD, realTheory.REAL_DIV_REFL,
                 DECIDE ``0 < x ==> x <> 0n``, wordsTheory.ZERO_LT_INT_MAX,
                 REAL_ARITH ``abs (-2 - x) = abs (2 - -x)``,
                 REAL_ARITH ``abs (-1 * y - x) = abs (y - -x)``])
  \\ rfs [DECIDE ``0 < x ==> x <> 0n``, wordsTheory.ZERO_LT_INT_MAX]
  );

(* ------------------------------------------------------------------------ *)

val REAL_LE_LCANCEL_IMP =
  METIS_PROVE [REAL_LE_LMUL] ``!x y z. 0r < x /\ x * y <= x * z ==> y <= z``

val lem = Q.prove(
  `!a x.
    1 < a ==> (2 pow (a - 2) * inv (2 pow (a - 1 + x)) = inv (2 pow (x + 1)))`,
  rw [realTheory.REAL_INV_1OVER, realTheory.mult_ratr, realTheory.mult_ratl,
      realTheory.REAL_EQ_RDIV_EQ, GSYM realTheory.POW_ADD,
      realTheory.REAL_DIV_REFL]
  );

val error_bound_lemma6 = Q.prove(
  `!expw fracw x.
       0 <= x /\ x < inv (2 pow (2 ** (expw - 1) - 2)) /\
       1 < expw /\ 0 < fracw ==>
       ?n. n <= 2 EXP fracw /\
           abs (x - 2 / 2 pow (2 ** (expw - 1) - 1) * &n / 2 pow fracw) <=
           inv (2 pow (2 ** (expw - 1) - 1 + fracw))`,
  rpt strip_tac
  \\ Q.SPECL_THEN [`fracw`, `2 pow (2 ** (expw - 1) - 2) * x`] mp_tac
        error_bound_lemma2
  \\ Lib.W (Lib.C SUBGOAL_THEN MP_TAC o lhand o lhand o snd)
  >- (conj_tac
      >- (match_mp_tac realTheory.REAL_LE_MUL \\ simp [])
      \\ qpat_x_assum `x < _` mp_tac
      \\ simp [realTheory.REAL_INV_1OVER, realTheory.REAL_LT_RDIV_EQ,
               realTheory.lt_ratr]
      \\ metis_tac [REAL_MUL_COMM]
      )
  \\ DISCH_THEN (fn th => rewrite_tac [th])
  \\ DISCH_THEN (Q.X_CHOOSE_THEN `n` strip_assume_tac)
  \\ qexists_tac `n`
  \\ asm_rewrite_tac []
  \\ qspec_then `2 pow (2 ** (expw - 1) - 2)` match_mp_tac REAL_LE_LCANCEL_IMP
  \\ conj_tac
  >- simp []
  \\ rewrite_tac
      [realTheory.ABS_MUL
       |> GSYM
       |> Q.SPEC `2 pow (2 ** (expw - 1) - 2)`
       |> SIMP_RULE (srw_ss()) [GSYM realTheory.POW_ABS]
      ]
  \\ `1n < 2 ** (expw - 1)`
  by metis_tac [EVAL ``2n ** 0``, bitTheory.TWOEXP_MONO,
                 DECIDE ``1n < n ==> 0 < n - 1``]
  \\ fs [realTheory.REAL_SUB_LDISTRIB, realTheory.REAL_MUL_ASSOC, real_div, lem,
         DECIDE ``1 < n ==> (SUC (n - 2) = n - 1)``, realTheory.REAL_MUL_RINV,
         realTheory.pow
         |> CONJUNCT2
         |> GSYM
         |> ONCE_REWRITE_RULE [REAL_MUL_COMM]
         ]
  );

(* ------------------------------------------------------------------------ *)

val lem = Q.prove(
  `!n. &(2 * 2 ** n) = 2 * 2 pow n`,
  simp [realTheory.REAL_OF_NUM_POW]
  );

val error_bound_lemma7 = Q.prove(
  `!x. 0 <= x /\ x < inv (2 pow (bias (:'w) - 1)) /\ 1 < dimindex (:'w) ==>
       ?e f.
         abs (float_to_real <| Sign := 0w;
                               Exponent := e : 'w word;
                               Significand := f : 't word |> - x) <=
         inv (2 pow (bias (:'w) + dimindex (:'t))) /\
         ((e = 0w) \/ (e = 1w) /\ (f = 0w))`,
  gen_tac
  \\ DISCH_TAC
  \\ Q.SUBGOAL_THEN
       `0 <= x /\ x < inv (2 pow (2 ** (dimindex (:'w) - 1) - 2)) /\
        1 < dimindex (:'w) /\ 0 < dimindex (:'t)` assume_tac
  >- fs [wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def]
  \\ FIRST_ASSUM (Q.X_CHOOSE_THEN `n` MP_TAC o MATCH_MP error_bound_lemma6)
  \\ DISCH_THEN
         (CONJUNCTS_THEN2
            (strip_assume_tac o REWRITE_RULE [arithmeticTheory.LESS_OR_EQ])
            ASSUME_TAC)
  >- (
      qexists_tac `0w`
      \\ qexists_tac `n2w n`
      \\ fs [float_to_real_def, GSYM wordsTheory.dimword_def,
             wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def]
      \\ simp [Once realTheory.ABS_SUB]
      \\ fs [realTheory.mult_rat, realTheory.mult_ratl,
             Once realTheory.div_ratl]
     )
  \\ qexists_tac `1w`
  \\ qexists_tac `0w`
  \\ fs [float_to_real_def, wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def]
  \\ simp [Once realTheory.ABS_SUB]
  \\ rfs [realTheory.mult_rat, realTheory.mult_ratl, Once realTheory.div_ratl,
          realTheory.REAL_DIV_RMUL_CANCEL, lem]
  );

(* ------------------------------------------------------------------------ *)

val error_bound_lemma8 = Q.prove(
  `!x. abs x < inv (2 pow (bias (:'w) - 1)) /\ 1 < dimindex (:'w) ==>
       ?s e f.
         abs (float_to_real <| Sign := s;
                               Exponent := e : 'w word;
                               Significand := f : 't word |> - x) <=
         inv (2 pow (bias (:'w) + dimindex (:'t))) /\
         ((e = 0w) \/ (e = 1w) /\ (f = 0w))`,
  gen_tac
  \\ DISCH_TAC
  \\ SUBGOAL_THEN
        ``0 <= x /\ x < inv (2 pow (bias (:'w) - 1)) /\ 1 < dimindex (:'w) \/
          0 <= ~x /\ ~x < inv (2 pow (bias (:'w) - 1)) /\ 1 < dimindex (:'w) ``
       (DISJ_CASES_THEN
          (Q.X_CHOOSE_THEN `e` (Q.X_CHOOSE_THEN `f` assume_tac) o
           MATCH_MP error_bound_lemma7))
  >- (simp [] \\ pop_assum mp_tac \\ REAL_ARITH_TAC)
  >| [qexists_tac `0w`, qexists_tac `1w`]
  \\ qexists_tac `e`
  \\ qexists_tac `f`
  \\ ntac 2 (fs [float_to_real_def, wordsTheory.INT_MAX_LT_DIMWORD,
                 wordsTheory.INT_MIN_LT_DIMWORD, REAL_MUL_ASSOC,
                 DECIDE ``0 < x ==> x <> 0n``, wordsTheory.ZERO_LT_INT_MAX,
                 REAL_ARITH ``abs (y - -x) = abs (-1 * y - x)``])
  \\ rfs [DECIDE ``0 < x ==> x <> 0n``, wordsTheory.ZERO_LT_INT_MAX]
  );

(* ------------------------------------------------------------------------ *)

val float_to_real_scale_up = Q.prove(
  `!s e f k.
      e <> 0w /\ (e + n2w k <> 0w) /\ (w2n (e + n2w k) = w2n e + k) ==>
      (float_to_real <| Sign := s;
                        Exponent := e + n2w k : 'w word;
                        Significand := f : 't word |> =
       2 pow k * float_to_real <| Sign := s;
                                  Exponent := e : 'w word;
                                  Significand := f : 't word |>)`,
  simp [float_to_real_def, REAL_POW_ADD, real_div,
        AC REAL_MUL_ASSOC REAL_MUL_COMM]
  );

val float_to_real_scale_down = Q.prove(
  `!s e f k.
      e <> 0w /\ n2w k <> e /\
      (w2n (e - n2w k + n2w k) = w2n (e - n2w k) + k) ==>
      (float_to_real <| Sign := s;
                        Exponent := e - n2w k : 'w word;
                        Significand := f : 't word |> =
       inv (2 pow k) *
       float_to_real <| Sign := s;
                        Exponent := e : 'w word;
                        Significand := f : 't word |>)`,
  rpt strip_tac
  \\ `e + -n2w k <> 0w /\ (e = (e - n2w k) + n2w k)`
  by metis_tac [wordsTheory.WORD_EQ_SUB_ZERO, wordsTheory.WORD_SUB_INTRO,
                wordsTheory.WORD_LESS_NOT_EQ, wordsTheory.WORD_SUB_ADD]
  \\ pop_assum (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th])))
  \\ asm_simp_tac (std_ss++simpLib.type_ssfrag ``:('a, 'b) float``)
        [float_to_real_def, POW_ADD, AC REAL_MUL_ASSOC REAL_MUL_COMM]
  \\ simp [SIMP_CONV (srw_ss()) [] ``a + b + -b : 'a word``,
           REAL_MUL_ASSOC, realTheory.mult_ratr, REAL_MUL_LINV, POW_NZ,
           REAL_ARITH ``inv a * b * c * a * d = (inv a * a) * b * c * d``]
  );

(* ------------------------------------------------------------------------ *)

val two_times_bias_lt = Q.prove(
   `bias (:'a) + bias (:'a) < dimword (:'a) - 1`,
   simp [wordsTheory.INT_MAX_def, wordsTheory.INT_MAX_def,
         GSYM wordsTheory.dimword_twice_INT_MIN,
         DECIDE ``1n < n ==> 0 < n - 1``]
  );

val int_min_bias_plus1 = Q.prove(
  `INT_MIN (:'a) = INT_MAX (:'a) + 1`,
  simp [wordsTheory.INT_MAX_def, DECIDE ``0n < n ==> (n - 1 + 1 = n)``])


val lem = Q.prove(
  `1 < dimindex (:'a) ==>
   2 pow (UINT_MAX (:'a) - 1) / 2 pow (INT_MAX (:'a)) <= 2 pow (INT_MAX (:'a))`,
  rw [GSYM POW_ADD, realTheory.REAL_LE_LDIV_EQ]
  \\ match_mp_tac REAL_POW_MONO
  \\ simp [wordsTheory.UINT_MAX_def, wordsTheory.ZERO_LT_INT_MAX,
           DECIDE ``0n < a ==> 0 < 2 * a``, wordsTheory.dimword_twice_INT_MIN]
  \\ simp [wordsTheory.INT_MAX_def]
  );

val lem2 = Q.prove(
  `!a b c d : real. 0 < b /\ 0 <= c /\ a < b * c /\ b <= d ==> a < c * d`,
  rw []
  \\ `?p. 0 <= p /\ (d = b + p)`
  by (qexists_tac `d - b`
      \\ simp [REAL_ARITH ``b <= d : real ==> (b + (d - b) = d) /\ 0 <= d - b``]
     )
  \\ simp [realTheory.REAL_LDISTRIB, AC REAL_MUL_ASSOC REAL_MUL_COMM]
  \\ `0 <= c * p`
  by  simp[
          realTheory.REAL_LE_MUL2
          |> Q.SPECL [`0`, `c`, `0`, `p`]
          |> SIMP_RULE (srw_ss()) []]
  \\ simp [REAL_ARITH ``0 <= c /\ a < b ==> a < b + c : real``]
  );

val error_bound_big1 = Q.prove(
  `!x k. 2 pow k <= abs x /\ abs x < 2 pow SUC k /\
         abs x < threshold (:'t # 'w) /\ 1 < dimindex (:'w) ==>
         ?a : ('t, 'w) float.
             float_is_finite a /\
             abs (float_to_real a - x) <= 2 pow k / 2 pow (dimindex (:'t) + 1)`,
  rpt strip_tac
  \\ qspec_then `x / 2 pow k` mp_tac error_bound_lemma5
  \\ Lib.W (Lib.C SUBGOAL_THEN mp_tac o lhand o lhand o snd)
  >- (simp [ABS_DIV, GSYM realTheory.POW_ABS, ABS_N, POW_NZ, REAL_POW_LT,
            REAL_LT_LDIV_EQ, GSYM (CONJUNCT2 pow)]
      \\ match_mp_tac realTheory.REAL_LE_RDIV
      \\ simp [realTheory.REAL_POW_LT])
  \\ DISCH_THEN (fn th => rewrite_tac [th])
  \\ `2 pow k < threshold (:'t # 'w)` by metis_tac [REAL_LET_TRANS]
  \\ `k < bias (:'w) + 1`
  by (spose_not_then (assume_tac o REWRITE_RULE [arithmeticTheory.NOT_LESS])
      \\ `2r pow (bias (:'w) + 1) <= 2 pow k`
      by (match_mp_tac REAL_POW_MONO \\ simp [])
      \\ `2r pow (bias (:'w) + 1) < threshold (:'t # 'w)`
      by metis_tac [REAL_LET_TRANS]
      \\ pop_assum mp_tac
      \\ simp [threshold, realTheory.REAL_LT_RDIV_EQ,
               GSYM realTheory.REAL_OF_NUM_POW, GSYM realTheory.POW_ADD,
               wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def,
               wordsTheory.UINT_MAX_def,
               DECIDE ``0n < n ==> (n - 1 + 1 = n) /\ (SUC (n - 1) = n)``,
               GSYM (CONJUNCT2 arithmeticTheory.EXP)]
      \\ simp [realTheory.REAL_NOT_LT, GSYM wordsTheory.dimword_def,
               realTheory.REAL_SUB_LDISTRIB, realTheory.mult_ratr,
               DECIDE ``1n < n ==> (SUC (n - 2) = n - 1)``,
               DECIDE ``1n < n ==> n <> 0``,
               GSYM
                 (ONCE_REWRITE_RULE [REAL_MUL_COMM] (CONJUNCT2 realTheory.pow))
              ]
      \\ match_mp_tac (REAL_ARITH ``0 < a /\ 0 <= b ==> (a - b <= a : real)``)
      \\ simp [realTheory.REAL_LE_RDIV_EQ, DECIDE ``1n < n ==> 0 < 2 * n``]
     )
  \\ strip_tac
  >| [all_tac,
      Cases_on `k = bias (:'w)`
      >- (
          spose_not_then kall_tac
          \\ qpat_x_assum `abs _ <= inv (2 pow _)`
               (mp_tac o (MATCH_MP (REAL_ARITH
                  ``abs (a - b) <= c ==> abs(a) <= abs(b) + c``)))
          \\ simp [realTheory.REAL_NOT_LE, REAL_ABS_MUL, GSYM POW_ABS, ABS_NEG,
                   ABS_DIV, ABS_N, float_to_real_def,
                   wordsTheory.INT_MIN_LT_DIMWORD, prim_recTheory.LESS_NOT_EQ]
          \\ simp [int_min_bias_plus1, POW_ADD, realTheory.POW_ONE,
                   realTheory.REAL_LT_ADD_SUB, realTheory.REAL_LT_LDIV_EQ,
                   realTheory.REAL_DIV_LMUL_CANCEL
                   |> Q.SPECL [`2 pow n`, `2`, `1`]
                   |> SIMP_RULE (srw_ss()) []]
          \\ match_mp_tac lem2
          \\ qexists_tac `2 pow (UINT_MAX (:'w) - 1) / 2 pow bias (:'w)`
          \\ fs [threshold_def, pow, lem, AC REAL_MUL_ASSOC REAL_MUL_COMM,
                 realTheory.REAL_LT_RDIV_0, realTheory.REAL_SUB_LE,
                 realTheory.REAL_INV_1OVER, realTheory.REAL_LE_LDIV_EQ,
                 realTheory.POW_2_LE1, REAL_ARITH ``0r < n ==> 0 < 2 * n``,
                 REAL_ARITH ``1r <= n ==> 1 <= 2 * (2 * n)``]
         )
      \\ `k < bias (:'w)` by decide_tac
     ]
  \\ (
      qexists_tac `<| Sign := s;
                      Exponent := e + n2w k;
                      Significand := f |> : ('t, 'w) float`
      \\ conj_tac
      >- simp [float_tests, wordsTheory.word_add_n2w, int_min_bias_plus1,
               wordsTheory.word_2comp_n2w, two_times_bias_lt,
               DECIDE ``k < b + 1n /\ (b + b) < w - 1 ==>
                        k + b < w /\ k + b <> w - 1``,
               DECIDE ``k < b /\ (b + b) < w - 1n ==>
                        k + (b + 1) < w /\ k + (b + 1) <> w - 1``]
      \\ Q.SUBGOAL_THEN
           `e <> 0w /\ e + n2w k <> 0w /\ (w2n (e + n2w k) = w2n e + k)`
           (fn th => rewrite_tac [MATCH_MP float_to_real_scale_up th])
      >- (
          fs [wordsTheory.INT_MAX_LT_DIMWORD, prim_recTheory.LESS_NOT_EQ,
              wordsTheory.INT_MIN_LT_DIMWORD, wordsTheory.ZERO_LT_INT_MAX,
              wordsTheory.word_add_n2w, two_times_bias_lt,
              DECIDE ``k < b + 1n /\ (b + b) < w - 1 ==>
                       k + b < w /\ k + b <> w - 1``]
          \\ simp [int_min_bias_plus1, two_times_bias_lt,
              DECIDE ``k < b /\ (b + b) < w - 1n ==>
                       k + (b + 1) < w /\ k + (b + 1) <> w - 1``]
         )
      \\ match_mp_tac REAL_LE_LCANCEL_IMP
      \\ qexists_tac `inv (2 pow k)`
      \\ conj_tac
      >- simp [REAL_LT_INV_EQ, REAL_POW_LT]
      \\ `!x. inv (2 pow k) * abs x = abs (inv (2 pow k) * x)`
      by rewrite_tac
           [REAL_ABS_MUL, REAL_ABS_INV, GSYM realTheory.POW_ABS, ABS_N]
      \\ qpat_x_assum `zz <= inv (2 pow _)` mp_tac
      \\ simp [REAL_SUB_LDISTRIB, REAL_MUL_ASSOC, real_div, POW_NZ,
               REAL_MUL_LINV, float_to_real_def]
      \\ simp [AC REAL_MUL_COMM REAL_MUL_ASSOC, wordsTheory.ZERO_LT_INT_MAX,
               wordsTheory.INT_MAX_LT_DIMWORD, prim_recTheory.LESS_NOT_EQ
               ]
     )
  );

val error_bound_big = Q.prove(
  `!k x.
      2 pow k <= abs x /\ abs x < 2 pow (SUC k) /\
      abs x < threshold (:'t # 'w) /\ 1 < dimindex (:'w) ==>
      abs (error (:'t # 'w) x) <= 2 pow k / 2 pow (dimindex (:'t) + 1)`,
  prove_tac [error_bound_big1, error_at_worst_lemma, REAL_LE_TRANS])

(* ------------------------------------------------------------------------ *)

val suc_bias_lt_dimword = Q.prove(
  `1 < dimindex (:'a) ==> bias (:'a) + 1 < dimword (:'a)`,
  simp [wordsTheory.INT_MAX_def, wordsTheory.dimword_twice_INT_MIN,
        DECIDE ``0n < n ==> (n - 1 + 1 = n)``]
  );

val error_bound_small1 = Q.prove(
  `!x k. inv (2 pow SUC k) <= abs x /\ abs x < inv (2 pow k) /\
         k < bias (:'w) - 1 /\ 1 < dimindex (:'w) ==>
         ?a : ('t, 'w) float.
           float_is_finite a /\
           abs (float_to_real a - x) <=
           inv (2 pow SUC k * 2 pow (dimindex (:'t) + 1))`,
  rpt strip_tac
  \\ qspec_then `x * 2 pow (SUC k)` mp_tac error_bound_lemma5
  \\ Lib.W (Lib.C SUBGOAL_THEN mp_tac o lhand o lhand o snd)
  >- (fs [ABS_MUL, GSYM POW_ABS, REAL_INV_1OVER, REAL_LE_LDIV_EQ,
          REAL_LT_RDIV_EQ, REAL_POW_LT]
      \\ simp [pow, REAL_ARITH ``a * (2r * b) < 2 = a * b < 1``])
  \\ DISCH_THEN (fn th => rewrite_tac [th])
  \\ DISCH_THEN
       (Q.X_CHOOSE_THEN `s`
         (Q.X_CHOOSE_THEN `e`
           (Q.X_CHOOSE_THEN `f` (REPEAT_TCL CONJUNCTS_THEN assume_tac))))
  \\ qexists_tac `<| Sign := s;
                     Exponent := e - n2w (SUC k);
                     Significand := f |> : ('t, 'w) float`
  \\ conj_tac
  >- (
      fs [float_tests, wordsTheory.WORD_LITERAL_ADD, int_min_bias_plus1]
      \\ `bias (:'w) - SUC k < dimword (:'w)`
      by (match_mp_tac arithmeticTheory.LESS_TRANS
          \\ qexists_tac `bias (:'w)`
          \\ simp [wordsTheory.INT_MAX_LT_DIMWORD]
         )
      \\ `bias (:'w) + 1 - SUC k < dimword (:'w)`
      by (match_mp_tac arithmeticTheory.LESS_TRANS
          \\ qexists_tac `bias (:'w) + 1`
          \\ simp [wordsTheory.INT_MAX_def, wordsTheory.dimword_twice_INT_MIN,
                   DECIDE ``0n < n ==> (n - 1 + 1 = n)``]
         )
      \\ simp_tac std_ss [wordsTheory.WORD_NEG_1, wordsTheory.word_T_def]
      \\ simp [wordsTheory.BOUND_ORDER, wordsTheory.INT_MAX_LT_DIMWORD]
      \\ simp [wordsTheory.INT_MAX_def, wordsTheory.UINT_MAX_def,
               wordsTheory.dimword_twice_INT_MIN,
               DECIDE ``0 < a /\ 0 < b ==> a - b <> 2 * a - 1n``
               ]
     )
  \\ `e <> 0w /\ n2w (SUC k) <> e /\
      (w2n (e - n2w (SUC k) + n2w (SUC k)) = w2n (e - n2w (SUC k)) + SUC k)`
  by (
      `SUC k < dimword (:'w)`
      by metis_tac [wordsTheory.ZERO_LT_INT_MAX, wordsTheory.INT_MAX_LT_DIMWORD,
                    arithmeticTheory.LESS_TRANS,
                    DECIDE ``0n < b /\ k < b - 1 ==> SUC k < b``]
      \\ fs [wordsTheory.INT_MAX_LT_DIMWORD, wordsTheory.INT_MIN_LT_DIMWORD,
             prim_recTheory.LESS_NOT_EQ,
             int_min_bias_plus1, suc_bias_lt_dimword,
             SIMP_CONV (srw_ss()) [] ``a + b + -b : 'a word``,
             SIMP_CONV (srw_ss()) [] ``b + a + -b : 'a word``]
      \\ simp [wordsTheory.WORD_LITERAL_ADD, wordsTheory.INT_MAX_LT_DIMWORD,
               DECIDE ``0n < a /\ a < n ==> (a - SUC k < n) /\
                                            (a + 1 - SUC k < n)``]
     )
  \\ NO_STRIP_FULL_SIMP_TAC std_ss [float_to_real_scale_down]
  \\ match_mp_tac REAL_LE_LCANCEL_IMP
  \\ qexists_tac `2 pow (SUC k)`
  \\ `!x. 2 pow (SUC k) * abs x = abs (2 pow (SUC k) * x)`
  by rewrite_tac [REAL_ABS_MUL, REAL_ABS_INV, GSYM POW_ABS, ABS_N]
  \\ `!a b. 0 < a ==> (a * (inv a * b) = b)`
  by simp [REAL_MUL_ASSOC, REAL_MUL_RINV, REAL_POS_NZ]
  \\ simp [REAL_POW_LT, REAL_SUB_LDISTRIB, REAL_POS_NZ, REAL_INV_MUL]
  \\ NO_STRIP_FULL_SIMP_TAC (srw_ss()) [AC REAL_MUL_ASSOC REAL_MUL_COMM]
  );

val REAL_LE_INV2 = Q.prove(
  `!x y. 0 < x /\ x <= y ==> inv y <= inv x`,
  metis_tac [REAL_LE_LT, REAL_LT_INV])

val lem = Q.prove(
  `!n m. 2n <= n /\ 0 < m ==>
         2 pow (n - 1) < 2 pow (2 * n - 1) - 2 pow (2 * n - 2) / &(4 * m)`,
  rw [realTheory.REAL_LT_SUB_LADD]
  \\ `1 < 4 * m /\ 0 < 4 * m` by decide_tac
  \\ `!x y:real. x < y = x * &(4 * m) < y * &(4 * m)`
  by metis_tac [realTheory.REAL_LT_RMUL,
                SIMP_CONV (srw_ss()) [] ``0r < &(4 * m)``]
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ simp [realTheory.REAL_ADD_RDISTRIB, realTheory.REAL_DIV_RMUL,
           REAL_ARITH ``!n. x * (4 * n) = 2 * x * n + 2 * x * n : real``
           |> Q.SPEC `&n`
           |> SIMP_RULE (srw_ss()) []]
  \\ CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [REAL_ADD_COMM]))
  \\ match_mp_tac realTheory.REAL_LTE_ADD2
  \\ Q.SPECL_THEN [`2`, `n`] imp_res_tac arithmeticTheory.LESS_EQUAL_ADD
  \\ fs []
  \\ rw [realTheory.REAL_DOUBLE]
  >- (
      simp [realTheory.REAL_OF_NUM_POW, DECIDE ``x + 3 = SUC (x + 2)``,
            arithmeticTheory.EXP, arithmeticTheory.RIGHT_ADD_DISTRIB,
            arithmeticTheory.LEFT_ADD_DISTRIB]
      \\ rewrite_tac [arithmeticTheory.MULT_ASSOC,
                      arithmeticTheory.LT_MULT_CANCEL_LBARE]
      \\ simp []
     )
  \\ `m <> 0` by decide_tac
  \\ asm_simp_tac std_ss
       [realTheory.REAL_NZ_IMP_LT, realTheory.REAL_LE_RMUL, REAL_MUL_ASSOC]
  \\ asm_simp_tac std_ss
       [realTheory.REAL_LE_LMUL, GSYM REAL_MUL_ASSOC, REAL_ARITH ``0 < 2r``]
  \\ simp [GSYM (CONJUNCT2 pow)]
  \\ match_mp_tac REAL_POW_MONO
  \\ simp []
  );

val threshold_gt1 = Q.prove(
  `1 < dimindex (:'w) ==> 1 < threshold (:'t # 'w)`,
  simp [threshold, realTheory.REAL_INV_1OVER, realTheory.REAL_LT_RDIV_EQ,
        realTheory.mult_ratl, realTheory.mult_ratr,
        GSYM realTheory.REAL_OF_NUM_POW, prim_recTheory.LESS_NOT_EQ,
        wordsTheory.ZERO_LT_INT_MAX, two_pow_over_pre,
        realTheory.REAL_SUB_LDISTRIB, DECIDE ``0n < n ==> (SUC (n - 1) = n)``,
        GSYM (CONJUNCT2 arithmeticTheory.EXP)]
  \\ simp [wordsTheory.UINT_MAX_def, wordsTheory.INT_MAX_def,
           wordsTheory.dimword_twice_INT_MIN]
  \\ qabbrev_tac `n = INT_MIN (:'w)`
  \\ qabbrev_tac `m = INT_MIN (:'t)`
  \\ strip_tac
  \\ `2n <= n` by simp [Abbr `n`, wordsTheory.INT_MIN_def]
  \\ `0n < m` by simp [Abbr `m`, wordsTheory.INT_MIN_def]
  \\ simp [lem]
  );

val error_bound_small = Q.prove(
  `!k x.
     inv (2 pow (SUC k)) <= abs x /\ abs x < inv (2 pow k) /\
     k < bias (:'w) - 1 /\ 1 < dimindex (:'w) ==>
     abs (error (:'t # 'w) x) <=
     inv (2 pow (SUC k) * 2 pow (dimindex (:'t) + 1))`,
  rpt strip_tac
  \\ `?a : ('t, 'w) float.
        float_is_finite a /\
        abs (float_to_real a - x) <=
        inv (2 pow (SUC k) * 2 pow (dimindex (:'t) + 1))`
  by metis_tac [error_bound_small1]
  \\ match_mp_tac REAL_LE_TRANS
  \\ qexists_tac `abs (float_to_real a - x)`
  \\ simp []
  \\ match_mp_tac error_at_worst_lemma
  \\ simp []
  \\ match_mp_tac REAL_LT_TRANS
  \\ qexists_tac `inv (2 pow k)`
  \\ simp []
  \\ match_mp_tac REAL_LET_TRANS
  \\ qexists_tac `inv 1`
  \\ conj_tac
  >- (match_mp_tac REAL_LE_INV2 \\ simp [REAL_POW_LE_1])
  \\ simp [realTheory.REAL_INV_1OVER, threshold_gt1]
  );

(* ------------------------------------------------------------------------ *)

val lem = Q.prove(
  `1 < dimindex (:'w) ==> -1w <> (1w : 'w word)`,
  srw_tac [wordsLib.WORD_BIT_EQ_ss] []
  \\ qexists_tac `1`
  \\ simp [wordsTheory.word_index]
  );

val error_bound_tiny = Q.prove(
  `!x. abs x < inv (2 pow (bias (:'w) - 1)) /\ 1 < dimindex (:'w) ==>
       abs (error (:'t # 'w) x) <= inv (2 pow (bias (:'w) + dimindex (:'t)))`,
  strip_tac
  \\ DISCH_TAC
  \\ `?a : ('t, 'w) float.
        float_is_finite a /\
        abs (float_to_real a - x) <= inv (2 pow (bias (:'w) + dimindex (:'t)))`
  by (pop_assum (fn th => mp_tac (MATCH_MP error_bound_lemma8 th)
                          \\ assume_tac th)
      \\ DISCH_THEN
           (Q.X_CHOOSE_THEN `s`
             (Q.X_CHOOSE_THEN `e`
               (Q.X_CHOOSE_THEN `f` (REPEAT_TCL CONJUNCTS_THEN assume_tac))))
      \\ qexists_tac `<|Sign := s; Exponent := e; Significand := f|>`
      \\ fs [float_tests, wordsTheory.word_T_not_zero, lem]
     )
  \\ match_mp_tac REAL_LE_TRANS
  \\ qexists_tac `abs (float_to_real a - x)`
  \\ simp []
  \\ match_mp_tac error_at_worst_lemma
  \\ asm_rewrite_tac []
  \\ match_mp_tac REAL_LT_TRANS
  \\ qexists_tac `inv (2 pow (bias (:'w) - 1))`
  \\ asm_rewrite_tac []
  \\ match_mp_tac realTheory.REAL_LET_TRANS
  \\ qexists_tac `1`
  \\ simp [realTheory.REAL_INV_1OVER, realTheory.REAL_LE_LDIV_EQ, threshold_gt1]
  \\ CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [GSYM (EVAL ``2r pow 0``)]))
  \\ match_mp_tac REAL_POW_MONO
  \\ simp []
  );

(* -------------------------------------------------------------------------
   Stronger versions not requiring exact location of the interval.
   ------------------------------------------------------------------------- *)

val lem = Q.prove(
  `!n. 1 < n ==> (2 * inv (2 pow (n - 1)) = inv (2 pow (n - 2)))`,
  rw [realTheory.REAL_INV_1OVER, realTheory.REAL_EQ_RDIV_EQ,
      REAL_ARITH ``2 * (a:real) * b = a * (2 * b)``, GSYM (CONJUNCT2 pow),
      DECIDE ``1 < n ==> (SUC (n - 2) = n - 1)``,
      realTheory.REAL_DIV_RMUL
      ]
  );

val error_bound_norm_strong = Q.prove(
  `!x j.
    abs x < threshold (:'t # 'w) /\
    abs x < 2 pow (SUC j) / 2 pow (bias (:'w) - 1) /\ 1 < bias (:'w) ==>
    abs (error (:'t # 'w) x) <= 2 pow j / 2 pow (bias (:'w) + dimindex (:'t))`,
  gen_tac
  \\ Induct
  >- (
      rw_tac std_ss [pow, POW_1, real_div, REAL_MUL_LID, REAL_MUL_RID]
      \\ fs [lem]
      \\ `1 < dimindex (:'w)`
      by (
          spose_not_then assume_tac
          \\ `(dimindex (:'w) = 0) \/ (dimindex (:'w) = 1)` by decide_tac
          \\ fs [wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def]
         )
      \\ Cases_on `abs x < inv (2 pow (bias (:'w) - 1))`
      >- metis_tac [error_bound_tiny]
      \\ qspecl_then [`bias (:'w) - 2`, `x`] mp_tac error_bound_small
      \\ fs [GSYM REAL_POW_ADD, arithmeticTheory.ADD1, GSYM REAL_NOT_LT]
     )
  \\ strip_tac
  \\ `1 < dimindex (:'w)`
  by (
      spose_not_then assume_tac
      \\ `(dimindex (:'w) = 0) \/ (dimindex (:'w) = 1)` by decide_tac
      \\ fs [wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def]
     )
  \\ Cases_on `abs x < 2 pow SUC j / 2 pow (bias (:'w) - 1)`
  >- (match_mp_tac REAL_LE_TRANS
      \\ qexists_tac `2 pow j / 2 pow (bias (:'w) + dimindex (:'t))`
      \\ asm_simp_tac std_ss [real_div, pow]
      \\ match_mp_tac realTheory.REAL_LE_RMUL_IMP
      \\ simp_tac std_ss [REAL_LE_INV_EQ, POW_POS, REAL_ARITH ``0 <= 2r``,
                          REAL_ARITH ``0r <= a ==> a <= 2 * a``]
     )
  \\ Cases_on `SUC j <= bias (:'w) - 2`
  >- (
      `2 pow SUC j / 2 pow (bias (:'w) + dimindex (:'t)) =
       inv (2 pow SUC ((bias (:'w) - 2) - SUC j) * 2 pow (dimindex (:'t) + 1))`
      by simp [GSYM POW_ADD, realTheory.REAL_EQ_LDIV_EQ,
               realTheory.REAL_EQ_RDIV_EQ,
               arithmeticTheory.ADD1, REAL_INV_1OVER, realTheory.mult_ratl]
      \\ asm_rewrite_tac []
      \\ match_mp_tac error_bound_small
      \\ `inv (2 pow (SUC (bias (:'w) - (SUC j + 2)))) =
          2 pow SUC j / 2 pow (bias (:'w) - 1)`
      by simp [GSYM POW_ADD, realTheory.REAL_EQ_LDIV_EQ,
               realTheory.REAL_EQ_RDIV_EQ,
               arithmeticTheory.ADD1, REAL_INV_1OVER, realTheory.mult_ratl]
      \\ `inv (2 pow (bias (:'w) - (SUC j + 2))) =
          2 pow SUC (SUC j) / 2 pow (bias (:'w) - 1)`
      by simp [GSYM POW_ADD, realTheory.REAL_EQ_LDIV_EQ,
               realTheory.REAL_EQ_RDIV_EQ,
               arithmeticTheory.ADD1, REAL_INV_1OVER, realTheory.mult_ratl]
      \\ fs [realTheory.REAL_NOT_LT]
     )
  \\ `?i. j = (bias (:'w) - 2) + i`
  by (qexists_tac `j - (bias (:'w) - 2)` \\ decide_tac)
  \\ asm_simp_tac std_ss
       [DECIDE ``1n < b ==> (b + i = b - 1 + SUC i) /\
                            (SUC (b - 2 + i) = b - 1 + i)``]
  \\ simp_tac std_ss [POW_ADD]
  \\ simp [realTheory.REAL_DIV_LMUL_CANCEL, arithmeticTheory.ADD1]
  \\ match_mp_tac error_bound_big
  \\ qpat_x_assum `~(_ < _)` mp_tac
  \\ full_simp_tac bool_ss
        [realTheory.REAL_NOT_LT, POW_ADD,
         DECIDE ``1n < b ==> (SUC (b - 2 + i) = i + (b - 1))``,
         DECIDE ``SUC (i + (b - 1)) = SUC i + (b - 1)``,
         realTheory.REAL_DIV_RMUL_CANCEL
         |> Q.SPECL [`2 pow n`, `a`, `1`]
         |> SIMP_RULE (srw_ss()) []
        ]
  );

(* -------------------------------------------------------------------------
   "1 + Epsilon" property (relative error bounding).
   ------------------------------------------------------------------------- *)

val bias_imp_dimindex = Q.prove(
  `1 < bias (:'a) ==> 1 < dimindex (:'a)`,
  rw [wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def]
  \\ spose_not_then assume_tac
  \\ `dimindex (:'a) = 1` by simp [DECIDE ``0n < n /\ ~(1 < n) ==> (n = 1)``]
  \\ fs []
  );

val lem = Q.prove(
  `!n : num. n + SUC (n - 1) <= 2 ** n`,
  Induct \\ rw [arithmeticTheory.EXP])

val THRESHOLD_MUL_LT = Q.prove(
  `threshold (:'t # 'w) * 2 pow (bias (:'w) - 1) < 2 pow (2 EXP (bias (:'w)))`,
  `2 pow (UINT_MAX (:'w) - 1) * inv (2 pow (bias (:'w))) = 2 pow (bias (:'w))`
  by (simp [REAL_INV_1OVER, realTheory.mult_ratr, realTheory.REAL_EQ_LDIV_EQ,
            GSYM REAL_POW_ADD]
      \\ simp [realTheory.REAL_OF_NUM_POW, wordsTheory.UINT_MAX_def,
               wordsTheory.INT_MAX_def, wordsTheory.dimword_twice_INT_MIN,
               arithmeticTheory.LEFT_SUB_DISTRIB])
  \\ asm_simp_tac std_ss [threshold_def, real_div]
  \\ rewrite_tac
         [GSYM REAL_MUL_ASSOC, REAL_SUB_RDISTRIB, REAL_SUB_LDISTRIB,
          GSYM pow, GSYM POW_ADD]
  \\ match_mp_tac REAL_LTE_TRANS
  \\ qexists_tac `2 pow (bias (:'w) + SUC (bias (:'w) - 1))`
  \\ conj_tac
  >- (
      match_mp_tac (REAL_ARITH ``0 < a /\ 0r < x ==> (a - x < a)``)
      \\ simp [realTheory.REAL_LT_RMUL_0, realTheory.REAL_LT_LMUL_0,
               realTheory.REAL_LT_INV_EQ]
     )
  \\ match_mp_tac REAL_POW_MONO
  \\ simp [lem]
  );

val lem = Q.prove(
  `!a b c:real. 0 < b ==> ((a / b) * c = a * (c / b))`,
  rw [realTheory.mult_ratl, realTheory.mult_ratr]
  );

val LT_THRESHOLD_LT_POW_INV = Q.prove(
  `!x. 1 < dimindex (:'w) ==> x < threshold (:'t # 'w) ==>
       x < 2 pow (UINT_MAX (:'w) - 1) / 2 pow (bias (:'w) - 1)`,
  gen_tac
  \\ strip_tac
  \\ simp [threshold]
  \\ match_mp_tac (REAL_ARITH ``b < c ==> (a < b ==> a < c : real)``)
  \\ simp [realTheory.REAL_LT_LDIV_EQ, GSYM realTheory.REAL_OF_NUM_POW, lem,
           two_pow_over_pre, wordsTheory.ZERO_LT_INT_MAX,
           realTheory.REAL_LT_LMUL]
  \\ match_mp_tac (REAL_ARITH ``0r < a /\ 0r < b ==> a - b < a``)
  \\ `0r < &(2 * dimword (:'t))` by simp [DECIDE ``0n < n ==> 0 < 2 * n``]
  \\ simp [realTheory.REAL_LT_RDIV_0]
  );

val real_pos_in_binade = Q.prove(
  `!x. normalizes (:'t # 'w) x /\ 0 <= x ==>
       ?j. j <= UINT_MAX (:'w) - 2 /\ 2 pow j / 2 pow (bias (:'w) - 1) <= x /\
           x < 2 pow (SUC j) / 2 pow (bias (:'w) - 1)`,
  rw_tac arith_ss [normalizes_def, abs]
  \\ imp_res_tac bias_imp_dimindex
  \\ qspec_then `\n. 2 pow n / 2 pow (bias (:'w) - 1) <= x`
       mp_tac arithmeticTheory.EXISTS_GREATEST
  \\ Lib.W (Lib.C SUBGOAL_THEN mp_tac o lhs o lhand o snd)
  >- (
      conj_tac
      >- (qexists_tac `0` \\ asm_simp_tac std_ss [REAL_MUL_LID , pow, real_div])
      \\ qexists_tac `2 EXP (bias (:'w))`
      \\ Q.X_GEN_TAC `n`
      \\ rw_tac bool_ss
           [GSYM real_lt, REAL_LT_RDIV_EQ, REAL_POW_LT, REAL_ARITH ``0 < 2r``]
      \\ match_mp_tac REAL_LT_TRANS
      \\ qexists_tac `2 pow (2 EXP (bias (:'w)))`
      \\ conj_tac
      >- (
          match_mp_tac realTheory.REAL_LT_TRANS
          \\ qexists_tac `threshold (:'t # 'w) * 2 pow (bias (:'w) - 1)`
          \\ simp [REAL_LT_RMUL, THRESHOLD_MUL_LT]
         )
      \\ match_mp_tac REAL_POW_MONO_LT
      \\ asm_simp_tac bool_ss
           [REAL_ARITH ``1 < 2r``, GSYM arithmeticTheory.GREATER_DEF]
     )
  \\ DISCH_THEN (fn th => rewrite_tac [th])
  \\ DISCH_THEN
       (X_CHOOSE_THEN ``n:num``
         (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o Q.SPEC `SUC n`)))
  \\ rw_tac arith_ss [REAL_NOT_LE]
  \\ qexists_tac `n`
  \\ full_simp_tac std_ss []
  \\ imp_res_tac LT_THRESHOLD_LT_POW_INV
  \\ `2 pow n / 2 pow (bias (:'w) - 1) <
      2 pow (UINT_MAX (:'w) - 1) / 2 pow (bias (:'w) - 1)`
  by metis_tac [REAL_LET_TRANS]
  \\ spose_not_then assume_tac
  \\ `UINT_MAX (:'w) - 1 <= n` by decide_tac
  \\ `2 pow (UINT_MAX (:'w) - 1) <= 2 pow n`
  by metis_tac [REAL_POW_MONO, REAL_ARITH ``1 <= 2r``]
  \\ full_simp_tac std_ss
       [REAL_LT_RDIV, REAL_POW_LT, REAL_ARITH ``0 < 2r``, real_lte]
  );

val real_neg_in_binade = Q.prove(
  `!x. normalizes (:'t # 'w) x /\ 0 <= ~x ==>
       ?j. j <= UINT_MAX (:'w) - 2 /\ 2 pow j / 2 pow (bias (:'w) - 1) <= ~x /\
           ~x < 2 pow (SUC j) / 2 pow (bias (:'w) - 1)`,
  metis_tac [normalizes_def, ABS_NEG, real_pos_in_binade])

val real_in_binade = Q.prove(
  `!x. normalizes (:'t # 'w) x ==>
       ?j. j <= UINT_MAX (:'w) - 2 /\
           2 pow j / 2 pow (bias (:'w) - 1) <= abs x /\
           abs x < 2 pow (SUC j) / 2 pow (bias (:'w) - 1)`,
  gen_tac
  \\ Cases_on `0 <= x`
  \\ asm_simp_tac arith_ss [abs, real_neg_in_binade, real_pos_in_binade,
                            REAL_ARITH ``~(0r <= x) ==> 0 <= ~x``]
  );

(* ------------------------------------------------------------------------- *)

val error_bound_norm_strong_normalize = Q.prove(
  `!x. normalizes (:'t # 'w) x ==>
       ?j. abs (error (:'t # 'w) x) <=
           2 pow j / 2 pow (bias (:'w) + dimindex (:'t))`,
  metis_tac [real_in_binade, error_bound_norm_strong, normalizes_def])

(* ------------------------------------------------------------------------- *)

val inv_le = Q.prove(
  `!a b. 0 < a /\ 0 < b ==> (inv a <= inv b = b <= a)`,
  rw [realTheory.REAL_INV_1OVER, realTheory.REAL_LE_LDIV_EQ,
      realTheory.mult_ratl, realTheory.REAL_LE_RDIV_EQ]
  );

val relative_bound_lem = Q.prove(
  `!x j. x <> 0 ==>
         (2 pow j * inv (2 pow (bias (:'w) - 1)) <= abs x =
          inv (abs x) <= inv (2 pow j * inv (2 pow (bias (:'w) - 1))))`,
  REPEAT strip_tac
  \\ match_mp_tac (GSYM inv_le)
  \\ asm_simp_tac std_ss [REAL_ARITH ``x <> 0 ==> 0 < abs x``]
  \\ match_mp_tac realTheory.REAL_LT_MUL
  \\ simp_tac std_ss [realTheory.REAL_POW_LT, realTheory.REAL_LT_INV_EQ,
                      REAL_ARITH ``0 < 2r``]
  );

val inv_mul = Q.prove(
  `!a b. a <> 0 /\ b <> 0 ==> (inv (a * inv b) = b / a)`,
  rw [realTheory.REAL_INV_MUL, realTheory.REAL_INV_NZ, realTheory.REAL_INV_INV]
  \\ simp [realTheory.REAL_INV_1OVER, realTheory.mult_ratl]
  );

val relative_error_zero = Q.prove(
  `!x. (x = 0) ==>
       ?e. abs e <= 1 / 2 pow (dimindex (:'t) + 1) /\
           (float_to_real (round roundTiesToEven x : ('t, 'w) float) =
            x * (1 + e))`,
  rw []
  \\ qexists_tac `0`
  \\ qspec_then `0`
       (fn th => simp [REWRITE_RULE [realTheory.REAL_SUB_RZERO] th])
       (GSYM error_def)
  \\ match_mp_tac error_is_zero
  \\ qexists_tac `float_plus_zero (:'t # 'w)`
  \\ simp [binary_ieeeTheory.zero_to_real, binary_ieeeTheory.zero_properties]
  );

val relative_error = Q.store_thm ("relative_error",
  `!x. normalizes (:'t # 'w) x ==>
       ?e. abs e <= 1 / 2 pow (dimindex (:'t) + 1) /\
           (float_to_real (round roundTiesToEven x : ('t, 'w) float) =
            x * (1 + e))`,
  rpt strip_tac
  \\ Cases_on `x = 0r`
  >- (match_mp_tac relative_error_zero \\ simp [])
  \\ imp_res_tac bias_imp_dimindex
  \\ `x < 0r \/ 0 < x` by (qpat_assum `x <> 0` MP_TAC \\ REAL_ARITH_TAC)
  \\ (qspec_then `x` mp_tac real_in_binade
      \\ rw_tac std_ss []
      \\ full_simp_tac std_ss [normalizes_def]
      \\ qspecl_then [`x`,`j`] MP_TAC error_bound_norm_strong
      \\ rw_tac std_ss []
      \\ `2 pow j * inv (2 pow (bias (:'w) - 1)) <= abs x =
          inv (abs x) <= inv (2 pow j * inv (2 pow (bias (:'w) - 1)))`
      by metis_tac [relative_bound_lem]
      \\ Q.UNDISCH_TAC `2 pow j / 2 pow (bias (:'w) - 1) <= abs x`
      \\ asm_simp_tac std_ss [real_div]
      \\ rw_tac std_ss []
      \\ `0 <= inv (abs x)` by simp [REAL_LE_INV_EQ, ABS_POS]
      \\ qspec_then `error (:'t # 'w) x` assume_tac ABS_POS
      \\ qspecl_then
           [`abs (error (:'t # 'w) x)`,
            `2 pow j / 2 pow (bias (:'w) + dimindex (:'t))`,
            `inv (abs x)`,
            `inv (2 pow j * inv (2 pow (bias (:'w) - 1)))`] mp_tac REAL_LE_MUL2
      \\ asm_simp_tac std_ss []
      \\ strip_tac
      \\ qexists_tac `error (:'t # 'w) x * inv x`
      \\ conj_tac
      >- (simp_tac std_ss [realTheory.ABS_MUL, realTheory.REAL_MUL_LID]
          \\ match_mp_tac realTheory.REAL_LE_TRANS
          \\ qexists_tac `2 pow j / 2 pow (bias (:'w) + dimindex (:'t)) *
                          inv (2 pow j * inv (2 pow (bias (:'w) - 1)))`
          \\ asm_simp_tac std_ss [realTheory.ABS_INV]
          \\ simp_tac std_ss
               [inv_mul, realTheory.POW_NZ, REAL_ARITH ``2 <> 0r``,
                realTheory.REAL_POS_NZ, realTheory.REAL_INV_NZ,
                realTheory.REAL_DIV_OUTER_CANCEL]
          \\ simp [realTheory.REAL_INV_1OVER, realTheory.mult_ratl,
                   realTheory.REAL_LE_LDIV_EQ, realTheory.REAL_LE_RDIV_EQ]
          \\ simp [GSYM POW_ADD]
          \\ EVAL_TAC
         )
      \\ asm_simp_tac std_ss
           [error_def, REAL_LDISTRIB, REAL_MUL_RID, REAL_MUL_RINV,
            REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB, REAL_MUL_LID, REAL_SUB_ADD2,
            REAL_ARITH ``x * (float_to_real qq * inv x) =
                         (x * inv x) * float_to_real qq``]
     )
  );

(* -------------------------------------------------------------------------
   Ensure that the result is actually finite.
   ------------------------------------------------------------------------- *)

val float_round_finite = Q.store_thm ("float_round_finite",
  `!b x. abs x < threshold (:'t # 'w) ==>
         float_is_finite (float_round roundTiesToEven b x : ('t, 'w) float)`,
  rw [float_round_def, round_def, binary_ieeeTheory.zero_properties,
      REAL_ARITH ``abs x < y = ~(x <= ~y) /\ ~(x >= y)``,
      REWRITE_RULE [pred_setTheory.GSPEC_ETA] is_finite_closest]
  );

val float_value_finite = Q.prove(
  `!a. float_is_finite a ==> (float_value a = Float (float_to_real a))`,
  Cases
  \\ rename [`float s e f`]
  \\ `float s e f = <| Sign := s; Exponent := e; Significand := f |>`
  by simp [float_component_equality]
  \\ simp [binary_ieeeTheory.float_tests, float_value_def]
  );

(* -------------------------------------------------------------------------
   Lifting of arithmetic operations.
   ------------------------------------------------------------------------- *)

val finite_not = Q.prove(
  `!a. float_is_finite a ==> ~float_is_infinite a /\ ~float_is_nan a`,
  strip_tac
  \\ Cases_on `float_value a`
  \\ simp [float_is_finite_def, float_is_infinite_def, float_is_nan_def]
  )

val zero_le_ulp = Q.prove(
  `0 <= ulp (:'t # 'w)`,
  simp [ulp_def, ULP_def])

val round_zero =
  binary_ieeeTheory.round_roundTiesToEven_is_zero
  |> Q.SPEC `0`
  |> SIMP_RULE (srw_ss()) [zero_le_ulp]

val lift_tac =
  rpt gen_tac
  \\ strip_tac
  \\ full_simp_tac (srw_ss()++realSimps.real_SS)
       [float_value_finite, error_def, float_round_finite, normalizes_def,
        float_add_def, float_sub_def, float_mul_def, float_div_def,
        float_sqrt_def, float_mul_add_def, float_mul_sub_def,
        binary_ieeeTheory.float_is_zero_to_real]
  \\ rw [float_round_def, finite_not,
         binary_ieeeTheory.float_is_zero_to_real,
         binary_ieeeTheory.zero_to_real, binary_ieeeTheory.zero_properties]

val lift_tac2 =
  lift_tac
  >- fs [real_to_float_def, float_round_finite]
  >- (assume_tac round_zero \\ fs [binary_ieeeTheory.zero_to_real])
  >- (assume_tac round_zero \\ fs [binary_ieeeTheory.zero_to_real])
  >- (assume_tac round_zero \\ fs [binary_ieeeTheory.zero_to_real])
  >- (assume_tac round_zero \\ fs [binary_ieeeTheory.zero_to_real])
  \\ rw [real_to_float_def, float_round_def, finite_not,
         binary_ieeeTheory.float_is_zero_to_real,
         binary_ieeeTheory.zero_to_real, binary_ieeeTheory.zero_properties]

val float_add = Q.store_thm ("float_add",
  `!a b : ('t, 'w) float.
    float_is_finite a /\ float_is_finite b /\
    abs (float_to_real a + float_to_real b) < threshold (:'t # 'w) ==>
    float_is_finite (float_add roundTiesToEven a b) /\
    (float_to_real (float_add roundTiesToEven a b) =
     float_to_real a + float_to_real b +
     error (:'t # 'w) (float_to_real a + float_to_real b))`,
  lift_tac)

val float_sub = Q.store_thm ("float_sub",
  `!a b : ('t, 'w) float.
    float_is_finite a /\ float_is_finite b /\
    abs (float_to_real a - float_to_real b) < threshold (:'t # 'w) ==>
    float_is_finite (float_sub roundTiesToEven a b) /\
    (float_to_real (float_sub roundTiesToEven a b) =
     float_to_real a - float_to_real b +
     error (:'t # 'w) (float_to_real a - float_to_real b))`,
  lift_tac
  );

val float_mul = Q.store_thm ("float_mul",
  `!a b : ('t, 'w) float.
    float_is_finite a /\ float_is_finite b /\
    abs (float_to_real a * float_to_real b) < threshold (:'t # 'w) ==>
    float_is_finite (float_mul roundTiesToEven a b) /\
    (float_to_real (float_mul roundTiesToEven a b) =
     float_to_real a * float_to_real b +
     error (:'t # 'w) (float_to_real a * float_to_real b))`,
  lift_tac)

val float_div = Q.store_thm ("float_div",
  `!a b : ('t, 'w) float.
    float_is_finite a /\ float_is_finite b /\ ~float_is_zero b /\
    abs (float_to_real a / float_to_real b) < threshold (:'t # 'w) ==>
    float_is_finite (float_div roundTiesToEven a b) /\
    (float_to_real (float_div roundTiesToEven a b) =
     float_to_real a / float_to_real b +
     error (:'t # 'w) (float_to_real a / float_to_real b))`,
  lift_tac)

val float_sqrt = Q.store_thm ("float_sqrt",
  `!a : ('t, 'w) float.
    float_is_finite a /\ (a.Sign = 0w) /\
    abs (sqrt (float_to_real a)) < threshold (:'t # 'w) ==>
    float_is_finite (float_sqrt roundTiesToEven a) /\
    (float_to_real (float_sqrt roundTiesToEven a) =
     sqrt (float_to_real a) + error (:'t # 'w) (sqrt (float_to_real a)))`,
  lift_tac)

val float_mul_add = Q.store_thm ("float_mul_add",
  `!a b c : ('t, 'w) float.
    float_is_finite a /\ float_is_finite b /\ float_is_finite c /\
    abs (float_to_real a * float_to_real b + float_to_real c) <
    threshold (:'t # 'w) ==>
    float_is_finite (float_mul_add roundTiesToEven a b c) /\
    (float_to_real (float_mul_add roundTiesToEven a b c) =
     float_to_real a * float_to_real b + float_to_real c +
     error (:'t # 'w) (float_to_real a * float_to_real b + float_to_real c))`,
  lift_tac2)

val float_mul_sub = Q.store_thm ("float_mul_add",
  `!a b c : ('t, 'w) float.
    float_is_finite a /\ float_is_finite b /\ float_is_finite c /\
    abs (float_to_real a * float_to_real b - float_to_real c) <
    threshold (:'t # 'w) ==>
    float_is_finite (float_mul_sub roundTiesToEven a b c) /\
    (float_to_real (float_mul_sub roundTiesToEven a b c) =
     float_to_real a * float_to_real b - float_to_real c +
     error (:'t # 'w) (float_to_real a * float_to_real b - float_to_real c))`,
  lift_tac2)

(*-----------------------*)

fun try_gen q th = Q.GEN q th handle HOL_ERR _ => th

val finite_rule =
   Q.GEN `a` o try_gen `b` o try_gen `c` o
   MATCH_MP (DECIDE ``(X ==> a /\ b) ==> (X ==> a)``) o
   Drule.SPEC_ALL

val float_add_finite = save_thm ("float_add_finite", finite_rule float_add)
val float_sub_finite = save_thm ("float_sub_finite", finite_rule float_sub)
val float_mul_finite = save_thm ("float_mul_finite", finite_rule float_mul)
val float_div_finite = save_thm ("float_div_finite", finite_rule float_div)
val float_sqrt_finite = save_thm ("float_sqrt_finite", finite_rule float_sqrt)

val float_mul_add_finite = save_thm ("float_mul_add_finite",
  finite_rule float_mul_add)

val float_mul_sub_finite = save_thm ("float_mul_sub_finite",
  finite_rule float_mul_sub)

(*-----------------------*)

val relative_tac =
  rpt gen_tac
  \\ strip_tac
  \\ conj_tac
  >- fs [normalizes_def, float_add_finite, float_sub_finite, float_mul_finite,
         float_div_finite, float_sqrt_finite, float_mul_add_finite,
         float_mul_sub_finite]
  \\ imp_res_tac relative_error
  \\ qexists_tac `e`
  \\ full_simp_tac (srw_ss()++realSimps.real_SS)
       [float_value_finite, error_def, float_round_finite, normalizes_def,
        float_add_def, float_sub_def, float_mul_def, float_div_def,
        float_sqrt_def, float_mul_add_def, float_mul_sub_def,
        binary_ieeeTheory.float_is_zero_to_real]
  \\ rw [float_round_def, binary_ieeeTheory.float_is_zero_to_real, finite_not,
         binary_ieeeTheory.zero_to_real, binary_ieeeTheory.zero_properties]
  \\ rw [real_to_float_def, float_round_def, finite_not,
         binary_ieeeTheory.float_is_zero_to_real,
         binary_ieeeTheory.zero_to_real, binary_ieeeTheory.zero_properties]

val float_add_relative = Q.store_thm ("float_add_relative",
  `!a b : ('t, 'w) float.
      float_is_finite a /\ float_is_finite b /\
      normalizes (:'t # 'w) (float_to_real a + float_to_real b) ==>
      float_is_finite (float_add roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:'t) + 1) /\
          (float_to_real (float_add roundTiesToEven a b) =
           (float_to_real a + float_to_real b) * (1 + e))`,
  relative_tac
  );

val float_sub_relative = Q.store_thm ("float_sub_relative",
  `!a b : ('t, 'w) float.
      float_is_finite a /\ float_is_finite b /\
      normalizes (:'t # 'w) (float_to_real a - float_to_real b) ==>
      float_is_finite (float_sub roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:'t) + 1) /\
          (float_to_real (float_sub roundTiesToEven a b) =
           (float_to_real a - float_to_real b) * (1 + e))`,
  relative_tac
  );

val float_mul_relative = Q.store_thm ("float_mul_relative",
  `!a b : ('t, 'w) float.
      float_is_finite a /\ float_is_finite b /\
      normalizes (:'t # 'w) (float_to_real a * float_to_real b) ==>
      float_is_finite (float_mul roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:'t) + 1) /\
          (float_to_real (float_mul roundTiesToEven a b) =
           (float_to_real a * float_to_real b) * (1 + e))`,
  relative_tac
  );

val float_div_relative = Q.store_thm ("float_div_relative",
  `!a b : ('t, 'w) float.
      float_is_finite a /\ float_is_finite b /\ ~float_is_zero b /\
      normalizes (:'t # 'w) (float_to_real a / float_to_real b) ==>
      float_is_finite (float_div roundTiesToEven a b) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:'t) + 1) /\
          (float_to_real (float_div roundTiesToEven a b) =
           (float_to_real a / float_to_real b) * (1 + e))`,
  relative_tac
  );

val float_sqrt_relative = Q.store_thm ("float_sqrt_relative",
  `!a : ('t, 'w) float.
      float_is_finite a /\ (a.Sign = 0w) /\
      normalizes (:'t # 'w) (sqrt (float_to_real a)) ==>
      float_is_finite (float_sqrt roundTiesToEven a) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:'t) + 1) /\
          (float_to_real (float_sqrt roundTiesToEven a) =
           (sqrt (float_to_real a) * (1 + e)))`,
  relative_tac
  );

val float_mul_add_relative = Q.store_thm ("float_mul_add_relative",
  `!a b c : ('t, 'w) float.
      float_is_finite a /\ float_is_finite b /\ float_is_finite c /\
      normalizes (:'t # 'w)
        (float_to_real a * float_to_real b + float_to_real c) ==>
      float_is_finite (float_mul_add roundTiesToEven a b c) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:'t) + 1) /\
          (float_to_real (float_mul_add roundTiesToEven a b c) =
           (float_to_real a * float_to_real b + float_to_real c) * (1 + e))`,
  relative_tac
  );

val float_mul_sub_relative = Q.store_thm ("float_mul_sub_relative",
  `!a b c : ('t, 'w) float.
      float_is_finite a /\ float_is_finite b /\ float_is_finite c /\
      normalizes (:'t # 'w)
        (float_to_real a * float_to_real b - float_to_real c) ==>
      float_is_finite (float_mul_sub roundTiesToEven a b c) /\
      ?e. abs e <= 1 / 2 pow (dimindex (:'t) + 1) /\
          (float_to_real (float_mul_sub roundTiesToEven a b c) =
           (float_to_real a * float_to_real b - float_to_real c) * (1 + e))`,
  relative_tac
  );

(* ------------------------------------------------------------------------- *)

val () = export_theory ()
