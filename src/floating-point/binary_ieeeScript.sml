(* ------------------------------------------------------------------------
   Theory of IEEE-754 (base 2) floating-point (basic) arithmetic
   ------------------------------------------------------------------------ *)

open HolKernel boolLib bossLib
open lcsymtacs realLib wordsLib

val () = new_theory "binary_ieee"

local
   open String
   val mesg_to_string = !Feedback.MESG_to_string
   fun f s = if isPrefix "mk_functional" s andalso isSubstring "completion" s
                then ""
             else mesg_to_string s
in
   val () = Feedback.set_trace "Theory.save_thm_reporting" 0
   val () = Feedback.MESG_to_string := f
end

infix \\
val op \\ = op THEN;

val Define = bossLib.zDefine

(* ------------------------------------------------------------------------
   Binary floating point representation
   ------------------------------------------------------------------------ *)

val () = Hol_datatype`
   float = <| Sign : word1; Exponent : 'w word; Significand : 't word |>`

(* ------------------------------------------------------------------------
   Maps to other representations
   ------------------------------------------------------------------------ *)

val () = Datatype `float_value = Float real | Infinity | NaN`

val () = List.app Parse.temp_overload_on
            [("precision", ``fcp$dimindex``), ("bias", ``words$INT_MAX``)]

val float_to_real_def = Define`
   float_to_real (x: ('t, 'w) float) =
      if x.Exponent = 0w
         then -1r pow (w2n x.Sign) *
              (2r / 2r pow (bias (:'w))) *
              (&(w2n x.Significand) / 2r pow (precision (:'t)))
      else -1r pow (w2n x.Sign) *
           (2r pow (w2n x.Exponent) / 2r pow (bias (:'w))) *
           (1r + &(w2n x.Significand) / 2r pow (precision (:'t)))`

val float_value_def = Define`
   float_value (x: ('t, 'w) float) =
      if x.Exponent = UINT_MAXw
         then if x.Significand = 0w then Infinity else NaN
      else Float (float_to_real x)`

(* ------------------------------------------------------------------------
   Tests
   ------------------------------------------------------------------------ *)

val float_is_nan_def = Define`
   float_is_nan (x: ('t, 'w) float) =
      case float_value x of
         NaN => T
       | _ => F`

val float_is_infinite_def = Define`
   float_is_infinite (x: ('t, 'w) float) =
      case float_value x of
         Infinity => T
       | _ => F`

val float_is_normal_def = Define`
   float_is_normal (x: ('t, 'w) float) =
      x.Exponent <> 0w /\ x.Exponent <> UINT_MAXw`

val float_is_subnormal_def = Define`
   float_is_subnormal (x: ('t, 'w) float) =
      (x.Exponent = 0w) /\ x.Significand <> 0w`

val float_is_zero_def = Define`
   float_is_zero (x: ('t, 'w) float) =
      case float_value x of
         Float r => r = 0
       | _ => F`

val float_is_finite_def = Define`
   float_is_finite (x: ('t, 'w) float) =
      case float_value x of
         Float _ => T
       | _ => F`

val float_is_integral_def = Define`
   float_is_integral (x: ('t, 'w) float) =
      case float_value x of
         Float r => ?n. abs r = &(n:num)
       | _ => F`

(* ------------------------------------------------------------------------
   Basic operations
   ------------------------------------------------------------------------ *)

val float_negate_def = Define`
   float_negate (x: ('t, 'w) float) = x with Sign := ~x.Sign`

val float_abs_def = Define`
   float_abs (x: ('t, 'w) float) = x with Sign := 0w`

(* ------------------------------------------------------------------------
   Some constants
   ------------------------------------------------------------------------ *)

val float_plus_infinity_def = Define`
   float_plus_infinity (:'t # 'w) =
      <| Sign := 0w;
         Exponent := UINT_MAXw: 'w word;
         Significand := 0w: 't word |>`

val float_plus_zero_def = Define`
   float_plus_zero (:'t # 'w) =
      <| Sign := 0w;
         Exponent := 0w: 'w word;
         Significand := 0w: 't word |>`

val float_top_def = Define`
   float_top (:'t # 'w) =
      <| Sign := 0w;
         Exponent := UINT_MAXw - 1w: 'w word;
         Significand := UINT_MAXw: 't word |>`

val float_plus_min_def = Define`
   float_plus_min (:'t # 'w) =
      <| Sign := 0w;
         Exponent := 0w: 'w word;
         Significand := 1w: 't word |>`

val float_minus_infinity_def = Define`
   float_minus_infinity (:'t # 'w) =
      float_negate (float_plus_infinity (:'t # 'w))`

val float_minus_zero_def = Define`
   float_minus_zero (:'t # 'w) = float_negate (float_plus_zero (:'t # 'w))`

val float_bottom_def = Define`
   float_bottom (:'t # 'w) = float_negate (float_top (:'t # 'w))`

val float_minus_min_def = Define`
   float_minus_min (:'t # 'w) = float_negate (float_plus_min (:'t # 'w))`

val float_some_nan_def = Define`
   float_some_nan (:'t # 'w) = @a: ('t, 'w) float. float_is_nan a`

(* ------------------------------------------------------------------------
   Rounding reals to floating-point values
   ------------------------------------------------------------------------ *)

val () = Hol_datatype`
   rounding = roundTiesToEven
            | roundTowardPositive
            | roundTowardNegative
            | roundTowardZero`

val is_closest_def = Define`
   is_closest s x a =
      a IN s /\
      !b. b IN s ==> abs (float_to_real a - x) <= abs (float_to_real b - x)`

val closest_such_def = Define`
   closest_such p s x =
      @a. is_closest s x a /\ (!b. is_closest s x b /\ p b ==> p a)`

val closest_def = Define `closest = closest_such (K T)`

val largest_def = Define`
   largest (:'t # 'w) =
      (2r pow (UINT_MAX (:'w) - 1) / 2r pow (INT_MAX (:'w))) *
      (2r - inv (2r pow dimindex(:'t)))`

val threshold_def = Define`
   threshold (:'t # 'w) =
      (2r pow (UINT_MAX (:'w) - 1) / 2r pow (INT_MAX (:'w))) *
      (2r - inv (2r pow SUC (dimindex(:'t))))`

(* Unit in the Last Place (of least precision) *)

(* For a given exponent (applies when significand is not zero) *)

val ULP_def = Define`
   ULP (e:'w word, (:'t)) =
   2 pow (if e = 0w then 1 else w2n e) / 2 pow (bias (:'w) + precision (:'t))`

(* Smallest ULP *)

val ulp_def = Define `ulp (:'t # 'w) = ULP (0w:'w word, (:'t))`

(* rounding *)

val round_def = Define`
   round mode (x: real) =
   case mode of
      roundTiesToEven =>
        let t = threshold (:'t # 'w) in
          if x <= -t
             then float_minus_infinity (:'t # 'w)
          else if x >= t
             then float_plus_infinity (:'t # 'w)
          else closest_such (\a. ~word_lsb a.Significand) float_is_finite x
    | roundTowardZero =>
        let t = largest (:'t # 'w) in
          if x < -t
             then float_bottom (:'t # 'w)
          else if x > t
             then float_top (:'t # 'w)
          else closest
                 {a | float_is_finite a /\ abs (float_to_real a) <= abs x} x
    | roundTowardPositive =>
        let t = largest (:'t # 'w) in
          if x < -t
             then float_bottom (:'t # 'w)
          else if x > t
             then float_plus_infinity (:'t # 'w)
          else closest {a | float_is_finite a /\ float_to_real a >= x} x
    | roundTowardNegative =>
        let t = largest (:'t # 'w) in
          if x < -t
             then float_minus_infinity (:'t # 'w)
          else if x > t
             then float_top (:'t # 'w)
          else closest {a | float_is_finite a /\ float_to_real a <= x} x`

val integral_round_def = Define`
   integral_round mode (x: real) =
   case mode of
      roundTiesToEven =>
        let t = threshold (:'t # 'w) in
          if x <= -t
             then float_minus_infinity (:'t # 'w)
          else if x >= t
             then float_plus_infinity (:'t # 'w)
          else closest_such (\a. ?n. EVEN n /\ (abs (float_to_real a) = &n))
                 float_is_integral x
    | roundTowardZero =>
        let t = largest (:'t # 'w) in
          if x < -t
             then float_bottom (:'t # 'w)
          else if x > t
             then float_top (:'t # 'w)
          else closest
                 {a | float_is_integral a /\ abs (float_to_real a) <= abs x} x
    | roundTowardPositive =>
        let t = largest (:'t # 'w) in
          if x < -t
             then float_bottom (:'t # 'w)
          else if x > t
             then float_plus_infinity (:'t # 'w)
          else closest {a | float_is_integral a /\ float_to_real a >= x} x
    | roundTowardNegative =>
        let t = largest (:'t # 'w) in
          if x < -t
             then float_minus_infinity (:'t # 'w)
          else if x > t
             then float_top (:'t # 'w)
          else closest {a | float_is_integral a /\ float_to_real a <= x} x`

(* ------------------------------------------------------------------------
   Some arithmetic operations
   ------------------------------------------------------------------------ *)

(* Round, choosing between -0.0 or +0.0 *)

val float_round_def = Define`
   float_round mode toneg r =
      let x = round mode r in
         if float_is_zero x
            then if toneg
                    then float_minus_zero (:'t # 'w)
                 else float_plus_zero (:'t # 'w)
         else x`

val float_round_to_integral_def = Define`
   float_round_to_integral mode (x: ('t, 'w) float) =
      case float_value x of
         Float r => integral_round mode r
       | _ => x`

val float_sqrt_def = Define`
   float_sqrt mode (x: ('t, 'w) float) =
      if x.Sign = 0w then
         case float_value x of
            NaN => float_some_nan (:'t # 'w)
          | Infinity => float_plus_infinity (:'t # 'w)
          | Float r => float_round mode (x.Sign = 1w) (sqrt r)
      else
         float_some_nan (:'t # 'w)`

val float_add_def = Define`
   float_add mode (x: ('t, 'w) float) (y: ('t, 'w) float) =
      case float_value x, float_value y of
         NaN, _ => float_some_nan (:'t # 'w)
       | _, NaN => float_some_nan (:'t # 'w)
       | Infinity, Infinity =>
            if x.Sign = y.Sign then x else float_some_nan (:'t # 'w)
       | Infinity, _ => x
       | _, Infinity => y
       | Float r1, Float r2 =>
            float_round mode (if (r1 = 0) /\ (r2 = 0) /\ (x.Sign = y.Sign) then
                                 x.Sign = 1w
                              else mode = roundTowardNegative) (r1 + r2)`

val float_sub_def = Define`
   float_sub mode (x: ('t, 'w) float) (y: ('t, 'w) float) =
      case float_value x, float_value y of
         NaN, _ => float_some_nan (:'t # 'w)
       | _, NaN => float_some_nan (:'t # 'w)
       | Infinity, Infinity =>
            if x.Sign = y.Sign then float_some_nan (:'t # 'w) else x
       | Infinity, _ => x
       | _, Infinity => float_negate y
       | Float r1, Float r2 =>
            float_round mode (if (r1 = 0) /\ (r2 = 0) /\ x.Sign <> y.Sign then
                                 x.Sign = 1w
                              else mode = roundTowardNegative) (r1 - r2)`

val float_mul_def = Define`
   float_mul mode (x: ('t, 'w) float) (y: ('t, 'w) float) =
      case float_value x, float_value y of
         NaN, _ => float_some_nan (:'t # 'w)
       | _, NaN => float_some_nan (:'t # 'w)
       | Infinity, Float r =>
            if r = 0
               then float_some_nan (:'t # 'w)
            else if x.Sign = y.Sign
               then float_plus_infinity (:'t # 'w)
            else float_minus_infinity (:'t # 'w)
       | Float r, Infinity =>
            if r = 0
               then float_some_nan (:'t # 'w)
            else if x.Sign = y.Sign
               then float_plus_infinity (:'t # 'w)
            else float_minus_infinity (:'t # 'w)
       | Infinity, Infinity =>
            if x.Sign = y.Sign
               then float_plus_infinity (:'t # 'w)
            else float_minus_infinity (:'t # 'w)
       | Float r1, Float r2 =>
            float_round mode (x.Sign <> y.Sign) (r1 * r2)`

val float_div_def = Define`
   float_div mode (x: ('t, 'w) float) (y: ('t, 'w) float) =
      case float_value x, float_value y of
         NaN, _ => float_some_nan (:'t # 'w)
       | _, NaN => float_some_nan (:'t # 'w)
       | Infinity, Infinity => float_some_nan (:'t # 'w)
       | Infinity, _ =>
            if x.Sign = y.Sign
               then float_plus_infinity (:'t # 'w)
            else float_minus_infinity (:'t # 'w)
       | _, Infinity =>
            if x.Sign = y.Sign
               then float_plus_zero (:'t # 'w)
            else float_minus_zero (:'t # 'w)
       | Float r1, Float r2 =>
            if r2 = 0
               then if r1 = 0
                       then float_some_nan (:'t # 'w)
                    else if x.Sign = y.Sign
                       then float_plus_infinity (:'t # 'w)
                    else float_minus_infinity (:'t # 'w)
            else float_round mode (x.Sign <> y.Sign) (r1 / r2)`

val float_mul_add_def = Define`
   float_mul_add mode
      (x: ('t, 'w) float) (y: ('t, 'w) float) (z: ('t, 'w) float) =
      let signP = x.Sign ?? y.Sign in
      let infP = float_is_infinite x  \/ float_is_infinite y
      in
         if float_is_nan x \/ float_is_nan y \/ float_is_nan z \/
            float_is_infinite x /\ float_is_zero y \/
            float_is_zero x /\ float_is_infinite y \/
            float_is_infinite z /\ infP /\ z.Sign <> signP
            then float_some_nan (:'t # 'w)
         else if float_is_infinite z /\ (z.Sign = 0w) \/ infP /\ (signP = 0w)
            then float_plus_infinity (:'t # 'w)
         else if float_is_infinite z /\ (z.Sign = 1w) \/ infP /\ (signP = 1w)
            then float_minus_infinity (:'t # 'w)
         else if float_is_zero z /\ (float_is_zero x \/ float_is_zero y) /\
                 (x.Sign = signP)
            then if x.Sign = 1w then
                    float_minus_zero (:'t # 'w)
                 else
                    float_plus_zero (:'t # 'w)
         else
            float_round mode (mode = roundTowardNegative)
               (float_to_real z + float_to_real x * float_to_real y)`

(* ------------------------------------------------------------------------
   Some comparison operations
   ------------------------------------------------------------------------ *)

val () = Hol_datatype `float_compare = LT | GT | EQ | UN`

val float_compare_def = Define`
   float_compare (x: ('t, 'w) float) (y: ('t, 'w) float) =
      case float_value x, float_value y of
         NaN, _ => UN
       | _, NaN => UN
       | Infinity, Infinity =>
            if x.Sign = y.Sign
               then EQ
            else if x.Sign = 1w
               then LT
            else GT
       | Infinity, _ => if x.Sign = 1w then LT else GT
       | _, Infinity => if y.Sign = 1w then GT else LT
       | Float r1, Float r2 =>
            if r1 < r2
               then LT
            else if r1 = r2
               then EQ
            else GT`

val float_less_than_def = Define`
   float_less_than (x: ('t, 'w) float) y =
      (float_compare x y = LT)`

val float_less_equal_def = Define`
   float_less_equal (x: ('t, 'w) float) y =
      case float_compare x y of
         LT => T
       | EQ => T
       | _ => F`

val float_greater_than_def = Define`
   float_greater_than (x: ('t, 'w) float) y =
      (float_compare x y = GT)`

val float_greater_equal_def = Define`
   float_greater_equal (x: ('t, 'w) float) y =
      case float_compare x y of
         GT => T
       | EQ => T
       | _ => F`

val float_equal_def = Define`
   float_equal (x: ('t, 'w) float) y =
      (float_compare x y = EQ)`

val exponent_boundary_def = Define`
   exponent_boundary (y: ('t, 'w) float) (x: ('t, 'w) float) =
      (x.Sign = y.Sign) /\ (w2n x.Exponent = w2n y.Exponent + 1) /\
      (x.Exponent <> 1w) /\ (y.Significand = -1w) /\ (x.Significand = 0w)`

(* ------------------------------------------------------------------------
   Some arithmetic theorems
   ------------------------------------------------------------------------ *)

val () = Feedback.set_trace "Theory.save_thm_reporting" 1

val rrw = SRW_TAC [boolSimps.LET_ss, realSimps.REAL_ARITH_ss]

(* |- !n. 0 < 2 pow n *)
val zero_lt_twopow = Theory.save_thm("zero_lt_twopow",
   realTheory.REAL_POW_LT
   |> Q.SPEC `2`
   |> SIMP_RULE (srw_ss()) []
   )

(* |- !n. 0 <= 2 pow n *)
val zero_le_twopow = Theory.save_thm("zero_le_twopow",
   MATCH_MP realTheory.REAL_LT_IMP_LE (Drule.SPEC_ALL zero_lt_twopow)
   |> GEN_ALL
   )

(* |- !n. 2 pow n <> 0 *)
val zero_neq_twopow = Theory.save_thm("zero_neq_twopow",
   realTheory.POW_ZERO
   |> Q.SPECL [`n`, `2`]
   |> SIMP_RULE (srw_ss()) []
   |> GEN_ALL
   )

val () = bossLib.export_rewrites
           ["zero_lt_twopow", "zero_le_twopow", "zero_neq_twopow"]

val zero_le_pos_div_twopow = Q.store_thm("zero_le_pos_div_twopow",
   `!m n. 0 <= &m / 2 pow n`,
   rw [realTheory.REAL_LE_DIV, realTheory.REAL_LT_IMP_LE])

val div_eq0 = Q.store_thm("div_eq0",
   `!a b. 0 < b ==> ((a / b = 0) = (a = 0))`,
   rw [realTheory.REAL_EQ_LDIV_EQ])

val () = bossLib.export_rewrites ["zero_le_pos_div_twopow", "div_eq0"]

(* !b. 2 <= 2 ** b <=> 1 <= b *)
val exp_ge2 = Theory.save_thm("exp_ge2",
  logrootTheory.LE_EXP_ISO
  |> Q.SPECL [`2`, `1`]
  |> reduceLib.REDUCE_RULE
  |> Conv.GSYM
  )

(* !b. 4 <= 2 ** b <=> 2 <= b *)
val exp_ge4 =
  logrootTheory.LE_EXP_ISO
  |> Q.SPECL [`2`, `2`]
  |> reduceLib.REDUCE_RULE
  |> Conv.GSYM

val exp_gt2 = Theory.save_thm("exp_gt2",
  logrootTheory.LT_EXP_ISO
  |> Q.SPECL [`2`, `1`]
  |> reduceLib.REDUCE_RULE
  |> Conv.GSYM
  )

val () = bossLib.export_rewrites ["exp_ge2", "exp_gt2"]

(* !n x u. (x / 2 pow n = u / 2 pow n) <=> (x = u) *)
val div_twopow =
   realTheory.eq_rat
   |> Q.INST [`y` |-> `2 pow n`, `v` |-> `2 pow n`]
   |> SIMP_RULE (srw_ss()) []
   |> Q.GENL [`u`, `x`, `n`]

val div_le = Q.prove(
   `!a b c. 0r < a ==> (b / a <= c / a = b <= c)`,
   metis_tac [realTheory.REAL_LE_LMUL, realTheory.REAL_DIV_RMUL,
              realTheory.REAL_POS_NZ, realTheory.REAL_MUL_COMM]
   )

val tac =
   NTAC 2 strip_tac
   \\ Cases_on `n <= 2`
   >- (`(n = 1) \/ (n = 2)` by decide_tac \\ rw [])
   \\ `2 < n` by decide_tac
   \\ lrw []

val two_mod_not_one = Q.prove(
   `!n. 0 < n ==> 2 MOD n <> 1`, tac)

val two_mod_eq_zero = Q.prove(
   `!n. 0 < n ==> ((2 MOD n = 0) = (n = 1) \/ (n = 2))`,
   tac
   )

(* |- !c a. c <> 0 ==> (c * a / c = a) *)
val mul_cancel =
   realTheory.REAL_DIV_LMUL_CANCEL
   |> Drule.SPEC_ALL
   |> Q.INST [`b` |-> `1`]
   |> SIMP_RULE (srw_ss()) []
   |> Q.GENL [`c`, `a`]

val ge2 = Q.prove(
   `dimindex(:'a) <> 1 ==> 2 <= dimindex (:'a)`,
   rw [DECIDE ``0 < a /\ a <> 1 ==> 2n <= a``])

val ge2b = Q.prove(
   `!n. 2n <= n ==> 1 <= 2 ** (n - 1) - 1`,
   REPEAT strip_tac
   \\ imp_res_tac arithmeticTheory.LESS_EQUAL_ADD
   \\ simp [arithmeticTheory.EXP_ADD, DECIDE ``0 < n ==> 1n <= 2 * n - 1``])

val ge2c = Q.prove(
   `!n m. 1r <= n /\ 2 < m ==> 2 < n * m`,
   rrw [GSYM realTheory.REAL_LT_LDIV_EQ]
   \\ `2r / m < 1` by (match_mp_tac realTheory.REAL_LT_1 \\ simp [])
   \\ METIS_TAC [realTheory.REAL_LTE_TRANS]
   )

val ge1_pow = Q.prove(
   `!a b. 1 <= a /\ 1n <= b ==> a <= a pow b`,
   Induct_on `b`
   \\ rw [realTheory.pow]
   \\ once_rewrite_tac [realTheory.REAL_MUL_COMM]
   \\ `0r < a /\ a <> 0`
   by METIS_TAC [realLib.REAL_ARITH ``1 <= a ==> 0r < a``,
                 realTheory.REAL_POS_NZ]
   \\ simp [GSYM realTheory.REAL_LE_LDIV_EQ, realTheory.REAL_DIV_REFL]
   \\ Cases_on `b = 0`
   \\ simp []
   \\ `1 <= b` by decide_tac
   \\ metis_tac [realTheory.REAL_LE_TRANS]
   )

(* |- !n x. 1 < x /\ 1 < n ==> x < x pow n *)
val gt1_pow =
   realTheory.REAL_POW_MONO_LT
   |> Q.SPEC `1`
   |> REWRITE_RULE [realTheory.POW_1]

(* |- !a b. 2 <= a /\ 1 <= b ==> 2 <= a * b *)
val prod_ge2 =
   realTheory.REAL_LE_MUL2
   |> Q.SPECL [`2`, `a`, `1`, `b`]
   |> SIMP_RULE (srw_ss()) []
   |> Q.GENL [`b`, `a`]

val le1 = Q.prove(
   `!x y. 0 < y /\ x <= y ==> x / y <= 1r`,
   REPEAT STRIP_TAC
   \\ Cases_on `x = y`
   \\ ASM_SIMP_TAC bool_ss
        [realTheory.REAL_LE_REFL, realTheory.REAL_DIV_REFL,
         realTheory.REAL_POS_NZ]
   \\ ASM_SIMP_TAC bool_ss [realTheory.REAL_LE_LDIV_EQ, realTheory.REAL_MUL_LID]
   )

val le2 = Q.store_thm("le2",
   `!n m. 2r <= n /\ 2 <= m ==> 2 <= n * m`,
   rrw [prod_ge2]
   )

val ge4 = Q.prove(
   `!n. n <> 0 ==> 4 <= 2 EXP n * 2`,
   Cases
   \\ simp [arithmeticTheory.EXP]
   )

val ge2d = Q.prove(
   `!n m. 2r <= n /\ 2 <= m ==> 2 < n * m`,
   rrw [GSYM realTheory.REAL_LT_LDIV_EQ]
   \\ `2r / m <= 1`
   by (match_mp_tac le1 \\ ASM_SIMP_TAC (srw_ss()++realSimps.REAL_ARITH_ss) [])
   \\ imp_res_tac (realLib.REAL_ARITH ``a <= 1 ==> a < 2r``)
   \\ METIS_TAC [realTheory.REAL_LTE_TRANS]
   )

(* |- !b. 0 < w2n b <=> b <> 0w *)
val word_lt0 =
   wordsTheory.WORD_LO
   |> Q.SPEC `0w`
   |> REWRITE_RULE [wordsTheory.word_0_n2w, wordsTheory.WORD_LO_word_0]
   |> GSYM

val word_ge1 = Q.prove(
   `!x. x <> 0w ==> 1 <= w2n x`,
   simp [GSYM word_lt0]
   )

val not_max_suc_lt_dimword = Q.prove(
   `!a:'a word. a <> -1w ==> w2n a + 1 < 2 ** dimindex(:'a)`,
   Cases
   \\ lrw [wordsTheory.word_eq_n2w, bitTheory.MOD_2EXP_MAX_def,
           bitTheory.MOD_2EXP_def, GSYM wordsTheory.dimword_def]
   )

(* |- !a. a <> 0w ==> 2 <= 2 pow w2n a *)
val pow_ge2 =
   ge1_pow
   |> Q.SPECL [`2`, `w2n (a:'w word)`]
   |> SIMP_RULE (srw_ss()) [DECIDE ``1n <= n = 0 < n``, word_lt0]
   |> GEN_ALL

val mult_id = Q.prove(
  `!a b. 1 < a ==> ((a * b = a) = (b = 1n))`,
  Induct_on `b`
  \\ lrw [arithmeticTheory.MULT_CLAUSES]
  )

(* |- !x y. 1 <= y /\ 0 < x ==> x <= x * y *)
val le_mult =
   realTheory.REAL_LE_LDIV_EQ
   |> Q.SPECL [`x`, `y`, `x`]
   |> Q.DISCH `1 <= y`
   |> SIMP_RULE bool_ss [boolTheory.AND_IMP_INTRO, realTheory.REAL_POS_NZ,
                         realTheory.REAL_DIV_REFL]
   |> ONCE_REWRITE_RULE [realTheory.REAL_MUL_COMM]
   |> Q.GENL [`y`, `x`]

(* |- !x y. x < 1 /\ 0 < y ==> y * x < y *)
val lt_mult =
   realTheory.REAL_LT_RDIV_EQ
   |> Q.SPECL [`x`, `y`, `y`]
   |> Q.DISCH `x < 1`
   |> SIMP_RULE bool_ss [boolTheory.AND_IMP_INTRO, realTheory.REAL_POS_NZ,
                         realTheory.REAL_DIV_REFL]
   |> ONCE_REWRITE_RULE [realTheory.REAL_MUL_COMM]
   |> Q.GENL [`y`, `x`]

(*  |- !x y. 1 < y /\ 0 < x ==> x < y * x  *)
val gt_mult =
   realTheory.REAL_LT_LDIV_EQ
   |> Q.SPECL [`x`, `y`, `x`]
   |> Q.DISCH `1 < y`
   |> SIMP_RULE bool_ss [boolTheory.AND_IMP_INTRO, realTheory.REAL_POS_NZ,
                         realTheory.REAL_DIV_REFL]
   |> Q.GENL [`y`, `x`]

val exp_id = Q.prove(
  `!a b. 1 < a ==> ((a EXP b = a) = (b = 1))`,
  REPEAT strip_tac
  \\ Cases_on `b = 0`
  >- lrw [arithmeticTheory.EXP]
  \\ Cases_on `b = 1`
  >- lrw [arithmeticTheory.EXP]
  \\ `1 < b` by decide_tac
  \\ imp_res_tac arithmeticTheory.LESS_ADD
  \\ pop_assum kall_tac
  \\ pop_assum (SUBST1_TAC o REWRITE_RULE [GSYM arithmeticTheory.ADD1] o SYM)
  \\ lrw [arithmeticTheory.EXP, mult_id])

val sub_rat_same_base = Q.prove(
   `!a b d. 0 < d ==> (a / d - b / d = (a - b) / d)`,
   rrw [realTheory.REAL_EQ_RDIV_EQ, realTheory.REAL_SUB_RDISTRIB,
        realTheory.REAL_DIV_RMUL]
   )

(* |- !x. 0 <= x ==> (abs x = x) *)
val gt0_abs =
   realTheory.ABS_REFL
   |> Q.SPEC `x`
   |> Q.DISCH `0 <= x`
   |> SIMP_RULE bool_ss []
   |> Drule.GEN_ALL

(*
(* !z x y. 0 <> z ==> ((x = y) <=> (x * z = y * z)) *)
val mul_into =
   realTheory.REAL_EQ_RMUL
   |> Drule.SPEC_ALL
   |> Q.DISCH `z <> 0`
   |> SIMP_RULE std_ss []
   |> Conv.GSYM
   |> Q.GENL [`y`, `x`, `z`]
*)

(* ------------------------------------------------------------------------
   Some basic theorems
   ------------------------------------------------------------------------ *)

val rsimp = ASM_SIMP_TAC (srw_ss()++realSimps.REAL_ARITH_ss)
val rrw = SRW_TAC [boolSimps.LET_ss, realSimps.REAL_ARITH_ss]
val rlfs = full_simp_tac (srw_ss()++realSimps.REAL_ARITH_ss)

val float_component_equality = DB.theorem "float_component_equality"

val sign_inconsistent =
   Drule.GEN_ALL (wordsLib.WORD_DECIDE ``~(x <> -1w /\ x <> 0w: word1)``)

val sign_neq = Q.prove(
   `!x. ~x <> x: word1`,
   wordsLib.Cases_word_value
   \\ simp []
   )

val some_nan_components = Q.prove(
   `((float_some_nan (:'t # 'w)).Exponent = UINT_MAXw) /\
    ((float_some_nan (:'t # 'w)).Significand <> 0w)`,
   simp [float_some_nan_def]
   \\ SELECT_ELIM_TAC
   \\ conj_tac
   >- (
       simp [float_is_nan_def]
       \\ qexists_tac `<| Sign := 0w;
                          Exponent := UINT_MAXw: 'w word;
                          Significand := 1w: 't word |>`
       \\ simp [float_value_def]
      )
   \\ strip_tac
   \\ Cases_on `float_value x`
   \\ simp [float_is_nan_def]
   \\ pop_assum mp_tac
   \\ rw [float_value_def]
   )

val float_components = Q.store_thm("float_components",
   `((float_plus_infinity (:'t # 'w)).Sign = 0w) /\
    ((float_plus_infinity (:'t # 'w)).Exponent = UINT_MAXw) /\
    ((float_plus_infinity (:'t # 'w)).Significand = 0w) /\
    ((float_minus_infinity (:'t # 'w)).Sign = 1w) /\
    ((float_minus_infinity (:'t # 'w)).Exponent = UINT_MAXw) /\
    ((float_minus_infinity (:'t # 'w)).Significand = 0w) /\
    ((float_plus_zero (:'t # 'w)).Sign = 0w) /\
    ((float_plus_zero (:'t # 'w)).Exponent = 0w) /\
    ((float_plus_zero (:'t # 'w)).Significand = 0w) /\
    ((float_minus_zero (:'t # 'w)).Sign = 1w) /\
    ((float_minus_zero (:'t # 'w)).Exponent = 0w) /\
    ((float_minus_zero (:'t # 'w)).Significand = 0w) /\
    ((float_plus_min (:'t # 'w)).Sign = 0w) /\
    ((float_plus_min (:'t # 'w)).Exponent = 0w) /\
    ((float_plus_min (:'t # 'w)).Significand = 1w) /\
    ((float_minus_min (:'t # 'w)).Sign = 1w) /\
    ((float_minus_min (:'t # 'w)).Exponent = 0w) /\
    ((float_minus_min (:'t # 'w)).Significand = 1w) /\
    ((float_top (:'t # 'w)).Sign = 0w) /\
    ((float_top (:'t # 'w)).Exponent = UINT_MAXw - 1w) /\
    ((float_top (:'t # 'w)).Significand = UINT_MAXw) /\
    ((float_bottom (:'t # 'w)).Sign = 1w) /\
    ((float_bottom (:'t # 'w)).Exponent = UINT_MAXw - 1w) /\
    ((float_bottom (:'t # 'w)).Significand = UINT_MAXw) /\
    ((float_some_nan (:'t # 'w)).Exponent = UINT_MAXw) /\
    ((float_some_nan (:'t # 'w)).Significand <> 0w) /\
    (!x. (float_negate x).Sign = ~x.Sign) /\
    (!x. (float_negate x).Exponent = x.Exponent) /\
    (!x. (float_negate x).Significand = x.Significand)`,
   rw [float_plus_infinity_def, float_minus_infinity_def,
       float_plus_zero_def, float_minus_zero_def, float_plus_min_def,
       float_minus_min_def, float_top_def, float_bottom_def,
       some_nan_components, float_negate_def]
   )

val float_distinct = Q.store_thm("float_distinct",
   `(float_plus_infinity (:'t # 'w) <> float_minus_infinity (:'t # 'w)) /\
    (float_plus_infinity (:'t # 'w) <> float_plus_zero (:'t # 'w)) /\
    (float_plus_infinity (:'t # 'w) <> float_minus_zero (:'t # 'w)) /\
    (float_plus_infinity (:'t # 'w) <> float_top (:'t # 'w)) /\
    (float_plus_infinity (:'t # 'w) <> float_bottom (:'t # 'w)) /\
    (float_plus_infinity (:'t # 'w) <> float_plus_min (:'t # 'w)) /\
    (float_plus_infinity (:'t # 'w) <> float_minus_min (:'t # 'w)) /\
    (float_plus_infinity (:'t # 'w) <> float_some_nan (:'t # 'w)) /\
    (float_minus_infinity (:'t # 'w) <> float_plus_zero (:'t # 'w)) /\
    (float_minus_infinity (:'t # 'w) <> float_minus_zero (:'t # 'w)) /\
    (float_minus_infinity (:'t # 'w) <> float_top (:'t # 'w)) /\
    (float_minus_infinity (:'t # 'w) <> float_bottom (:'t # 'w)) /\
    (float_minus_infinity (:'t # 'w) <> float_plus_min (:'t # 'w)) /\
    (float_minus_infinity (:'t # 'w) <> float_minus_min (:'t # 'w)) /\
    (float_minus_infinity (:'t # 'w) <> float_some_nan (:'t # 'w)) /\
    (float_plus_zero (:'t # 'w) <> float_minus_zero (:'t # 'w)) /\
    (float_plus_zero (:'t # 'w) <> float_top (:'t # 'w)) /\
    (float_plus_zero (:'t # 'w) <> float_bottom (:'t # 'w)) /\
    (float_plus_zero (:'t # 'w) <> float_plus_min (:'t # 'w)) /\
    (float_plus_zero (:'t # 'w) <> float_minus_min (:'t # 'w)) /\
    (float_plus_zero (:'t # 'w) <> float_some_nan (:'t # 'w)) /\
    (float_minus_zero (:'t # 'w) <> float_top (:'t # 'w)) /\
    (float_minus_zero (:'t # 'w) <> float_bottom (:'t # 'w)) /\
    (float_minus_zero (:'t # 'w) <> float_plus_min (:'t # 'w)) /\
    (float_minus_zero (:'t # 'w) <> float_minus_min (:'t # 'w)) /\
    (float_minus_zero (:'t # 'w) <> float_some_nan (:'t # 'w)) /\
    (float_top (:'t # 'w) <> float_minus_min (:'t # 'w)) /\
    (float_top (:'t # 'w) <> float_bottom (:'t # 'w)) /\
    (float_top (:'t # 'w) <> float_some_nan (:'t # 'w)) /\
    (float_bottom (:'t # 'w) <> float_plus_min (:'t # 'w)) /\
    (float_bottom (:'t # 'w) <> float_some_nan (:'t # 'w)) /\
    (float_plus_min (:'t # 'w) <> float_some_nan (:'t # 'w)) /\
    (float_plus_min (:'t # 'w) <> float_minus_min (:'t # 'w)) /\
    (float_minus_min (:'t # 'w) <> float_some_nan (:'t # 'w)) /\
    (!x. float_negate x <> x)`,
   rw [float_component_equality, float_components, two_mod_not_one, sign_neq,
       wordsTheory.word_T_not_zero, wordsTheory.WORD_EQ_NEG])

val float_values = Q.store_thm("float_values",
   `(float_value (float_plus_infinity (:'t # 'w)) = Infinity) /\
    (float_value (float_minus_infinity (:'t # 'w)) = Infinity) /\
    (float_value (float_some_nan (:'t # 'w)) = NaN) /\
    (float_value (float_plus_zero (:'t # 'w)) = Float 0) /\
    (float_value (float_minus_zero (:'t # 'w)) = Float 0) /\
    (float_value (float_plus_min (:'t # 'w)) =
        Float (2r / (2r pow (bias (:'w) + precision (:'t))))) /\
    (float_value (float_minus_min (:'t # 'w)) =
        Float (-2r / (2r pow (bias (:'w) + precision (:'t)))))`,
   rw [float_plus_infinity_def, float_minus_infinity_def,
       float_plus_zero_def, float_minus_zero_def, float_plus_min_def,
       float_minus_min_def, some_nan_components, float_negate_def,
       float_value_def, float_to_real_def, wordsTheory.word_T_not_zero,
       realTheory.mult_rat, realTheory.POW_ADD, GSYM realTheory.REAL_NEG_MINUS1,
       GSYM realTheory.REAL_MUL_LNEG, realTheory.neg_rat]
   )

val zero_to_real = Q.store_thm("zero_to_real",
   `(float_to_real (float_plus_zero (:'t # 'w)) = 0) /\
    (float_to_real (float_minus_zero (:'t # 'w)) = 0)`,
   rw [float_plus_zero_def, float_minus_zero_def,
       float_negate_def, float_to_real_def]
   )

val sign_not_zero = Q.store_thm("sign_not_zero",
   `!s: word1. -1 pow w2n s <> 0`,
   wordsLib.Cases_word_value \\ EVAL_TAC)

val float_sets = Q.store_thm("float_sets",
   `(float_is_zero = {float_minus_zero (:'t # 'w);
                      float_plus_zero (:'t # 'w)}) /\
    (float_is_infinite = {float_minus_infinity (:'t # 'w);
                          float_plus_infinity (:'t # 'w)})`,
   rw [FUN_EQ_THM, float_is_infinite_def, float_is_zero_def, float_value_def,
       float_plus_infinity_def, float_minus_infinity_def,
       float_plus_zero_def, float_minus_zero_def, float_to_real_def,
       float_negate_def, float_component_equality]
   \\ rw [sign_not_zero, realLib.REAL_ARITH ``0r <= n ==> 1 + n <> 0``]
   \\ wordsLib.Cases_on_word_value `x.Sign`
   \\ simp []
   )

val tac =
   rw [float_is_nan_def, float_is_normal_def, float_is_subnormal_def,
       float_is_finite_def, float_is_infinite_def, float_is_zero_def,
       float_is_integral_def, float_values, some_nan_components]
   \\ rw [float_plus_infinity_def, float_minus_infinity_def,
          float_plus_zero_def, float_minus_zero_def, float_top_def,
          float_bottom_def, float_some_nan_def, float_plus_min_def,
          float_minus_min_def, float_negate_def, float_value_def,
          wordsTheory.WORD_EQ_NEG, realTheory.REAL_EQ_LDIV_EQ, two_mod_not_one]

val infinity_properties = Q.store_thm("infinity_properties",
   `~float_is_zero (float_plus_infinity (:'t # 'w)) /\
    ~float_is_zero (float_minus_infinity (:'t # 'w)) /\
    ~float_is_finite (float_plus_infinity (:'t # 'w)) /\
    ~float_is_finite (float_minus_infinity (:'t # 'w)) /\
    ~float_is_integral (float_plus_infinity (:'t # 'w)) /\
    ~float_is_integral (float_minus_infinity (:'t # 'w)) /\
    ~float_is_nan (float_plus_infinity (:'t # 'w)) /\
    ~float_is_nan (float_minus_infinity (:'t # 'w)) /\
    ~float_is_normal (float_plus_infinity (:'t # 'w)) /\
    ~float_is_normal (float_minus_infinity (:'t # 'w)) /\
    ~float_is_subnormal (float_plus_infinity (:'t # 'w)) /\
    ~float_is_subnormal (float_minus_infinity (:'t # 'w)) /\
    float_is_infinite (float_plus_infinity (:'t # 'w)) /\
    float_is_infinite (float_minus_infinity (:'t # 'w))`,
   tac
   )

val zero_properties = Q.store_thm("zero_properties",
   `float_is_zero (float_plus_zero (:'t # 'w)) /\
    float_is_zero (float_minus_zero (:'t # 'w)) /\
    float_is_finite (float_plus_zero (:'t # 'w)) /\
    float_is_finite (float_minus_zero (:'t # 'w)) /\
    float_is_integral (float_plus_zero (:'t # 'w)) /\
    float_is_integral (float_minus_zero (:'t # 'w)) /\
    ~float_is_nan (float_plus_zero (:'t # 'w)) /\
    ~float_is_nan (float_minus_zero (:'t # 'w)) /\
    ~float_is_normal (float_plus_zero (:'t # 'w)) /\
    ~float_is_normal (float_minus_zero (:'t # 'w)) /\
    ~float_is_subnormal (float_plus_zero (:'t # 'w)) /\
    ~float_is_subnormal (float_minus_zero (:'t # 'w)) /\
    ~float_is_infinite (float_plus_zero (:'t # 'w)) /\
    ~float_is_infinite (float_minus_zero (:'t # 'w))`,
   tac
   )

val some_nan_properties = Q.store_thm("some_nan_properties",
   `~float_is_zero (float_some_nan (:'t # 'w)) /\
    ~float_is_finite (float_some_nan (:'t # 'w)) /\
    ~float_is_integral (float_some_nan (:'t # 'w)) /\
    float_is_nan (float_some_nan (:'t # 'w)) /\
    ~float_is_normal (float_some_nan (:'t # 'w)) /\
    ~float_is_subnormal (float_some_nan (:'t # 'w)) /\
    ~float_is_infinite (float_some_nan (:'t # 'w))`,
   tac
   )

val min_properties = Q.store_thm("min_properties",
   `~float_is_zero (float_plus_min (:'t # 'w)) /\
    float_is_finite (float_plus_min (:'t # 'w)) /\
    (float_is_integral (float_plus_min (:'t # 'w)) =
     (precision(:'w) = 1) /\ (precision(:'t) = 1)) /\
    ~float_is_nan (float_plus_min (:'t # 'w)) /\
    ~float_is_normal (float_plus_min (:'t # 'w)) /\
    float_is_subnormal (float_plus_min (:'t # 'w)) /\
    ~float_is_infinite (float_plus_min (:'t # 'w)) /\
    ~float_is_zero (float_minus_min (:'t # 'w)) /\
    float_is_finite (float_minus_min (:'t # 'w)) /\
    (float_is_integral (float_minus_min (:'t # 'w)) =
     (precision(:'w) = 1) /\ (precision(:'t) = 1)) /\
    ~float_is_nan (float_minus_min (:'t # 'w)) /\
    ~float_is_normal (float_minus_min (:'t # 'w)) /\
    float_is_subnormal (float_minus_min (:'t # 'w)) /\
    ~float_is_infinite (float_minus_min (:'t # 'w))`,
   tac (* after this the float_is_integral cases remain *)
   \\ (simp [realTheory.REAL_EQ_LDIV_EQ, realTheory.ABS_DIV,
             wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def, gt0_abs]
       \\ Cases_on `precision (:'t) = 1`
       \\ Cases_on `precision (:'w) = 1`
       \\ imp_res_tac ge2
       \\ rw []
       >- (qexists_tac `1n` \\ decide_tac)
       \\ Cases_on `n`
       \\ simp []
       \\ rewrite_tac [realTheory.REAL, realTheory.REAL_RDISTRIB]
       \\ match_mp_tac
            (realLib.REAL_ARITH ``2r < n /\ 0 <= x ==> 2 <> x + 1 * n``)
       \\ simp [realTheory.REAL_LT_IMP_LE, realTheory.REAL_LE_MUL]
       \\ imp_res_tac ge2b
       \\ match_mp_tac gt1_pow
       \\ simp [])
   )

val lem1 = Q.prove(
   `0w <+ (-2w:'a word) = (dimindex(:'a) <> 1)`,
   once_rewrite_tac [wordsTheory.WORD_LESS_NEG_RIGHT]
   \\ simp [two_mod_eq_zero, wordsTheory.dimword_def, exp_id,
            DECIDE ``0 < n ==> n <> 0n``]
   )

val lem2 = Q.prove(
   `dimindex(:'a) <> 1 ==> -2w <+ (-1w:'a word)`,
   once_rewrite_tac [wordsTheory.WORD_LESS_NEG_RIGHT]
   \\ simp [two_mod_eq_zero, wordsTheory.dimword_def, exp_id,
            DECIDE ``0 < n ==> n <> 0n``, wordsTheory.word_lo_n2w]
   \\ strip_tac
   \\ `1 < dimindex(:'a)` by simp [DECIDE ``0 < n /\ n <> 1 ==> 1n < n``]
   \\ imp_res_tac
        (bitTheory.TWOEXP_MONO
         |> Q.SPECL [`1`, `dimindex(:'a)`]
         |> numLib.REDUCE_RULE)
   \\ lrw []
   )

val tac =
   tac
   \\ rw [float_to_real_def, two_mod_eq_zero, wordsTheory.dimword_def,
          realLib.REAL_ARITH ``0r <= n ==> 1 + n <> 0``, exp_id, lem1,
          DECIDE ``0 < n ==> n <> 0n``]
   \\ Cases_on `dimindex(:'w) = 1`
   \\ lrw [lem2]

val top_properties = Q.store_thm("top_properties",
   `~float_is_zero (float_top (:'t # 'w)) /\
    float_is_finite (float_top (:'t # 'w)) /\
    (* float_is_integral (float_top (:'t # 'w)) = ?? /\ *)
    ~float_is_nan (float_top (:'t # 'w)) /\
    (float_is_normal (float_top (:'t # 'w)) = (precision(:'w) <> 1)) /\
    (float_is_subnormal (float_top (:'t # 'w)) = (precision(:'w) = 1)) /\
    ~float_is_infinite (float_top (:'t # 'w))`,
   tac
   )

val bottom_properties = Q.store_thm("bottom_properties",
   `~float_is_zero (float_bottom (:'t # 'w)) /\
    float_is_finite (float_bottom (:'t # 'w)) /\
    (* float_is_integral (float_bottom (:'t # 'w)) = ?? /\ *)
    ~float_is_nan (float_bottom (:'t # 'w)) /\
    (float_is_normal (float_bottom (:'t # 'w)) = (precision(:'w) <> 1)) /\
    (float_is_subnormal (float_bottom (:'t # 'w)) = (precision(:'w) = 1)) /\
    ~float_is_infinite (float_bottom (:'t # 'w))`,
   tac
   )

(* ------------------------------------------------------------------------ *)

val float_to_real_negate = Q.store_thm("float_to_real_negate",
   `!x. float_to_real (float_negate x) = -float_to_real x`,
   rw [float_to_real_def, float_negate_def]
   \\ wordsLib.Cases_on_word_value `x.Sign`
   \\ rsimp []
   )

val float_negate_negate = Q.store_thm("float_negate_negate",
   `!x. float_negate (float_negate x) = x`,
   simp [float_negate_def, float_component_equality]
   )

(* ------------------------------------------------------------------------
   Lemma support for rounding theorems
   ------------------------------------------------------------------------ *)

(*
val () = List.app Parse.clear_overloads_on ["bias", "precision"]
*)

local
   val cnv =
      Conv.QCONV
        (REWRITE_CONV [realTheory.REAL_LDISTRIB, realTheory.REAL_RDISTRIB])
   val dec =
      METIS_PROVE
        [realTheory.REAL_DIV_RMUL, realTheory.REAL_MUL_COMM,
         realTheory.REAL_MUL_ASSOC, zero_neq_twopow,
         realTheory.mult_ratr
         |> Q.INST [`z` |-> `2 pow n`]
         |> REWRITE_RULE [zero_neq_twopow]
         |> GEN_ALL]
in
   fun CANCEL_PROVE tm =
      let
         val thm1 = cnv tm
         val tm1 = boolSyntax.rhs (Thm.concl thm1)
         val thm2 = Drule.EQT_INTRO (dec tm1)
      in
         Drule.EQT_ELIM (Thm.TRANS thm1 thm2)
      end
end

val cancel_rwts = Q.prove(
   `(!a b. (2 pow a * b) / 2 pow a = b) /\
    (!a b c. 2 pow a * (b / 2 pow a * c) = b * c) /\
    (!a b c. a * (b / 2 pow c) * 2 pow c = a * b) /\
    (!a b c. a * (2 pow b * c) / 2 pow b = a * c) /\
    (!a b c. a / 2 pow b * (2 pow b * c) = a * c) /\
    (!a b c. a / 2 pow b * c * 2 pow b = a * c) /\
    (!a b c d. a / 2 pow b * c * (2 pow b * d) = a * c * d) /\
    (!a b c d. a * (2 pow b * c) * d / 2 pow b = a * c * d)`,
   metis_tac
     [realTheory.REAL_DIV_RMUL, realTheory.REAL_MUL_COMM,
      realTheory.REAL_MUL_ASSOC, zero_neq_twopow,
      realTheory.mult_ratr
      |> Q.INST [`z` |-> `2 pow n`]
      |> REWRITE_RULE [zero_neq_twopow]
      |> GEN_ALL]
   )

val cancel_rwt =
   CANCEL_PROVE
     ``(!a b c d. a * (b + c / 2 pow d) * 2 pow d = a * b * 2 pow d + a * c)``

val ulp = Q.store_thm("ulp",
   `ulp (:'t # 'w) = float_to_real (float_plus_min (:'t # 'w))`,
   simp [ulp_def, ULP_def, float_to_real_def, float_plus_min_def,
         realTheory.mult_rat, GSYM realTheory.POW_ADD]
   )

val neg_ulp = Q.store_thm("neg_ulp",
   `-ulp (:'t # 'w) =
    float_to_real (float_negate (float_plus_min (:'t # 'w)))`,
   simp [float_to_real_negate, ulp]
   )

val ULP_gt0 = Q.prove(
   `!e. 0 < ULP (e:'w word, (:'t))`,
   rw [ULP_def, realTheory.REAL_LT_RDIV_0])

val ulp_gt0 = (REWRITE_RULE [GSYM ulp_def] o Q.SPEC `0w`) ULP_gt0

val ULP_le_mono = Q.store_thm("ULP_le_mono",
   `!e1 e2. e2 <> 0w ==> (ULP (e1, (:'t)) <= ULP (e2, (:'t)) = e1 <=+ e2)`,
   Cases
   \\ Cases
   \\ lrw [ULP_def, wordsTheory.word_ls_n2w, div_le]
   \\ simp [realTheory.REAL_OF_NUM_POW]
   )

val ulp_lt_ULP = Q.store_thm("ulp_lt_ULP",
   `!e: 'w word. ulp (:'t # 'w) <= ULP (e,(:'t))`,
   rw [ulp_def]
   \\ Cases_on `e = 0w`
   \\ simp [wordsTheory.WORD_0_LS, ULP_le_mono]
   )

val lem = Q.prove(
   `!n. 0 < n ==> 3 < 2 pow SUC n`,
   Induct
   \\ rw [Once realTheory.pow]
   \\ Cases_on `0 < n`
   \\ simp [DECIDE ``~(0n < n) ==> (n = 0)``,
            realLib.REAL_ARITH ``3r < n ==> 3 < 2 * n``]
   )

val ulp_lt_largest = Q.store_thm("ulp_lt_largest",
   `ulp (:'t # 'w) < largest (:'t # 'w)`,
   simp [ulp_def, ULP_def, largest_def, realTheory.REAL_LT_RMUL_0, cancel_rwts,
         realTheory.REAL_LT_LDIV_EQ, realTheory.POW_ADD]
   \\ simp [realTheory.REAL_SUB_RDISTRIB, realTheory.REAL_SUB_LDISTRIB,
            realTheory.REAL_MUL_LINV, GSYM realaxTheory.REAL_MUL_ASSOC,
            GSYM (CONJUNCT2 realTheory.pow)]
   \\ simp [realLib.REAL_ARITH ``(a * b) - a = a * (b - 1): real``]
   \\ match_mp_tac ge2c
   \\ rw [GSYM realTheory.REAL_LT_ADD_SUB, realTheory.POW_2_LE1, lem]
   )

val ulp_lt_threshold = Q.store_thm("ulp_lt_threshold",
   `ulp (:'t # 'w) < threshold (:'t # 'w)`,
   simp [ulp_def, ULP_def, threshold_def, realTheory.REAL_LT_RMUL_0,
         cancel_rwts, realTheory.REAL_LT_LDIV_EQ, realTheory.POW_ADD,
         realTheory.pow]
   \\ simp [realTheory.REAL_SUB_RDISTRIB, realTheory.REAL_SUB_LDISTRIB,
            realTheory.REAL_MUL_LINV, realTheory.REAL_INV_MUL,
            GSYM realaxTheory.REAL_MUL_ASSOC]
   \\ simp [realLib.REAL_ARITH ``(a * b) - a * c = a * (b - c): real``]
   \\ match_mp_tac ge2c
   \\ rw [realTheory.POW_2_LE1, GSYM realTheory.REAL_LT_ADD_SUB,
          realTheory.REAL_INV_1OVER, GSYM (CONJUNCT2 realTheory.pow),
          realTheory.REAL_LT_LDIV_EQ, lem,
          realLib.REAL_ARITH ``3r < n ==> 5 < n * 2``]
   )

val lt_ulp_not_infinity0 =
   MATCH_MP
      (realLib.REAL_ARITH ``u < l ==> abs x < u ==> ~(x < -l) /\ ~(x > l)``)
      ulp_lt_largest
   |> Drule.GEN_ALL

val lt_ulp_not_infinity1 =
   MATCH_MP
      (realLib.REAL_ARITH
         ``u < l ==> 2 * abs x <= u ==> ~(x <= -l) /\ ~(x >= l)``)
      ulp_lt_threshold
   |> Drule.GEN_ALL

val abs_float_value = Q.store_thm("abs_float_value",
   `(!b: word1 c d. abs (-1 pow w2n b * c * d) = abs (c * d)) /\
    (!b: word1 c. abs (-1 pow w2n b * c) = abs c)`,
   conj_tac
   \\ wordsLib.Cases_word_value
   \\ simp [realTheory.ABS_MUL])

(* |- !x n. abs (1 + &n / 2 pow x) = 1 + &n / 2 pow x *)
val abs_significand =
   realLib.REAL_ARITH ``!a b. 0 <= a /\ 0 <= b ==> (abs (a + b) = a + b)``
   |> Q.SPECL [`1`, `&n / 2 pow x`]
   |> Conv.CONV_RULE
        (Conv.RATOR_CONV (SIMP_CONV (srw_ss()++realSimps.REAL_ARITH_ss)
            [realTheory.REAL_LE_DIV, realTheory.REAL_POS,
             realTheory.REAL_LT_IMP_LE]))
   |> REWRITE_RULE []
   |> GEN_ALL

val less_than_ulp = Q.store_thm("less_than_ulp",
   `!a: ('t, 'w) float.
       abs (float_to_real a) < ulp (:'t # 'w) =
       (a.Exponent = 0w) /\ (a.Significand = 0w)`,
   strip_tac
   \\ eq_tac
   \\ rw [ulp_def, ULP_def, float_to_real_def, abs_float_value, abs_significand,
          realTheory.ABS_MUL, realTheory.ABS_DIV, realTheory.ABS_N,
          gt0_abs, realTheory.mult_rat, realTheory.REAL_LT_RDIV_0]
   >| [
      SPOSE_NOT_THEN strip_assume_tac
      \\ qpat_assum `x < y: real` mp_tac
      \\ simp [realTheory.REAL_NOT_LT, GSYM realTheory.POW_ADD,
               realTheory.REAL_LE_RDIV_EQ, realTheory.REAL_DIV_RMUL]
      \\ Cases_on `a.Significand`
      \\ lfs [],
      (* -- *)
      simp [realTheory.REAL_NOT_LT, realTheory.REAL_LDISTRIB,
            realTheory.REAL_LE_LDIV_EQ, realTheory.REAL_RDISTRIB,
            realTheory.POW_ADD, cancel_rwts]
      \\ simp [GSYM realaxTheory.REAL_LDISTRIB]
      \\ match_mp_tac le2
      \\ conj_tac
      >- (match_mp_tac ge1_pow
          \\ Cases_on `a.Exponent`
          \\ lfs [])
      \\ match_mp_tac
           (realLib.REAL_ARITH ``2r <= a /\ 0 <= x ==> 2 <= a + x``)
      \\ simp [ge1_pow, DECIDE ``0n < a ==> 1 <= a``]
   ])

(* ------------------------------------------------------------------------ *)

val Float_is_finite = Q.prove(
   `!y: ('t, 'w) float r.
      (float_value y = Float r) ==> float_is_finite y`,
   rw [float_is_finite_def])

val Float_float_to_real = Q.prove(
   `!y: ('t, 'w) float r.
      (float_value y = Float r) ==> (float_to_real y = r)`,
   rw [float_value_def])

val float_is_zero_to_real = Q.store_thm("float_is_zero_to_real",
   `!x. float_is_zero x = (float_to_real x = 0)`,
   rw [float_is_zero_def, float_value_def]
   \\ simp [float_to_real_def]
   \\ wordsLib.Cases_on_word_value `x.Sign`
   \\ rsimp [realLib.REAL_ARITH ``0r <= x ==> 1 + x <> 0``]
   )

(* !x. float_is_zero x ==> (float_to_real x = 0) *)
val float_is_zero_to_real_imp =
   float_is_zero_to_real
   |> Drule.SPEC_ALL
   |> Thm.EQ_IMP_RULE
   |> fst
   |> Drule.GEN_ALL

val float_is_zero = Q.store_thm("float_is_zero",
   `!x. float_is_zero x = (x.Exponent = 0w) /\ (x.Significand = 0w)`,
   rw [float_is_zero_def, float_value_def, float_to_real_def, sign_not_zero,
       realLib.REAL_ARITH ``0 <= x ==> 1 + x <> 0r``,
       realTheory.REAL_LE_DIV, realTheory.REAL_LT_IMP_LE])

val pos_subnormal = Q.prove(
   `!a b n. 0 <= 2 / 2 pow a * (&n / 2 pow b)`,
   rrw [realTheory.REAL_LE_MUL]
   )

val pos_normal = Q.prove(
   `!a b c n. 0 <= 2 pow a / 2 pow b * (1 + &n / 2 pow c)`,
   rw [realTheory.REAL_LE_DIV, realTheory.REAL_LE_MUL,
       realLib.REAL_ARITH ``0r <= n ==> 0 <= 1 + n``]
   )

val pos_normal2 = Q.prove(
   `!a b c n. 0 <= 2 pow a / 2 pow b * (&n / 2 pow c)`,
   rw [realTheory.REAL_LE_DIV, realTheory.REAL_LE_MUL,
       realLib.REAL_ARITH ``0r <= n ==> 0 <= 1 + n``]
   )

val thms =
   List.map realLib.REAL_ARITH
      [``a <= b /\ 0 <= c ==> a <= b + c: real``,
       ``0 <= b /\ a <= c ==> a <= b + c: real``,
       ``0 <= b /\ a <= c /\ 0 <= d ==> a <= b + (c + d): real``,
       ``a <= b /\ 0 <= c /\ 0 <= d ==> a <= b + c + d: real``,
       ``a <= b /\ 0 <= c /\ 0 <= d /\ 0 <= e ==> a <= b + c + (d + e): real``]

val diff_sign_ULP = Q.prove(
   `!x: ('t, 'w) float y: ('t, 'w) float.
        ~(float_is_zero x /\ float_is_zero y) /\ x.Sign <> y.Sign ==>
        ULP (x.Exponent,(:'t)) <= abs (float_to_real x - float_to_real y)`,
   NTAC 2 strip_tac
   \\ wordsLib.Cases_on_word_value `x.Sign`
   \\ wordsLib.Cases_on_word_value `y.Sign`
   \\ rw [ULP_def, float_to_real_def, float_is_zero, realTheory.ABS_NEG,
          pos_normal, pos_subnormal,
          realLib.REAL_ARITH ``a - -1r * b * c = a + b * c``,
          realLib.REAL_ARITH ``-1r * b * c - a = -(b * c + a)``,
          realLib.REAL_ARITH ``0 <= a /\ 0 <= b ==> (abs (a + b) = a + b)``]
   \\ rw [realTheory.REAL_LDISTRIB]
   >| (List.map match_mp_tac (thms @ thms))
   \\ rrw [pos_subnormal, pos_normal2, word_lt0, realTheory.POW_ADD,
          realTheory.REAL_LE_LDIV_EQ, le2, pow_ge2, ge1_pow, le_mult,
          fcpTheory.DIMINDEX_GE_1, realTheory.REAL_LE_DIV, realTheory.POW_2_LE1,
          cancel_rwts, DECIDE ``n <> 0n ==> 1 <= 2 * n``,
          realLib.REAL_ARITH ``2 <= a ==> 1r <= a``]
   )

val diff_sign_ULP_gt = Q.prove(
   `!x: ('t, 'w) float y: ('t, 'w) float.
        ~float_is_zero x /\ ~float_is_zero y /\ x.Sign <> y.Sign ==>
        ULP (x.Exponent,(:'t)) < abs (float_to_real x - float_to_real y)`,
   NTAC 2 strip_tac
   \\ wordsLib.Cases_on_word_value `x.Sign`
   \\ wordsLib.Cases_on_word_value `y.Sign`
   \\ rw [ULP_def, float_to_real_def, float_is_zero, realTheory.ABS_NEG,
          pos_normal, pos_subnormal,
          realLib.REAL_ARITH ``a - -1r * b * c = a + b * c``,
          realLib.REAL_ARITH ``-1r * b * c - a = -(b * c + a)``,
          realLib.REAL_ARITH ``0 <= a /\ 0 <= b ==> (abs (a + b) = a + b)``]
   \\ rrw [realTheory.REAL_LDISTRIB, realTheory.REAL_RDISTRIB,
           realTheory.REAL_LT_LDIV_EQ, realTheory.REAL_LE_MUL,
           realTheory.POW_2_LE1, realTheory.POW_ADD,
           pos_subnormal, pos_normal2, word_lt0, cancel_rwts, word_lt0,
           prod_ge2, pow_ge2, le_mult,
           DECIDE ``0n < a /\ 0 < b ==> 2 < 2 * a + 2 * b``,
           DECIDE ``1n <= n = 0 < n``,
           DECIDE ``0n < x ==> 0 < 2 * x``,
           realLib.REAL_ARITH ``a <= b /\ 0r <= c /\ 1 <= d ==> a < b + c + d``,
           realLib.REAL_ARITH
              ``a <= b /\ 0 <= c /\ 2 <= d /\ 0 <= e ==> a < b + c + (d + e)``,
           realLib.REAL_ARITH
              ``1 <= a /\ 2r <= b /\ 0 <= c ==> 2 < 2 * a + (b + c)``
           |> Q.INST [`a` |-> `&n`]
           |> SIMP_RULE (srw_ss()) []
           ]
   )

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

(* |- !w. w2n w < 2 ** precision (:'a) *)
val w2n_lt_pow = REWRITE_RULE [wordsTheory.dimword_def] wordsTheory.w2n_lt

val w2n_lt_pow_sub1 = Q.prove(
   `!x:'a word. x <> -1w ==> w2n x < 2 ** dimindex(:'a) - 1`,
   REPEAT strip_tac
   \\ match_mp_tac (DECIDE ``a < b /\ a <> b - 1 ==> a < b - 1n``)
   \\ simp [w2n_lt_pow]
   \\ Cases_on `x`
   \\ fs [wordsTheory.WORD_NEG_1, wordsTheory.word_T_def, wordsTheory.w2n_n2w,
          wordsTheory.UINT_MAX_def, wordsTheory.dimword_def]
   )

val nobias_denormal_lt_1 = Q.prove(
   `!w:'t word. &w2n w / 2 pow precision (:'t) < 1`,
   rw [realTheory.REAL_LT_LDIV_EQ, realTheory.REAL_OF_NUM_POW, w2n_lt_pow])

val nobias_denormal_lt_2 = Q.prove(
   `!w:'t word. 2 * (&w2n w / 2 pow precision (:'t)) < 2`,
   rw [realLib.REAL_ARITH ``2r * n < 2 = n < 1``, nobias_denormal_lt_1])

val subnormal_lt_normal = Q.prove(
   `!x y z.
        y <> 0w ==>
        2 / 2 pow bias (:'w) * (&w2n (x:'t word) / 2 pow precision (:'t)) <
        2 pow w2n (y:'w word) / 2 pow bias (:'w) *
        (1 + &w2n (z:'t word) / 2 pow precision (:'t))`,
   REPEAT strip_tac
   \\ once_rewrite_tac
        [realTheory.REAL_LT_LMUL
         |> Q.SPEC `2 pow bias (:'w)`
         |> REWRITE_RULE [zero_lt_twopow]
         |> GSYM]
   \\ rewrite_tac [cancel_rwts, realTheory.REAL_LDISTRIB]
   \\ match_mp_tac
        (realLib.REAL_ARITH ``a < 2r /\ 2 <= b /\ 0 <= c ==> a < b + c``)
   \\ rw [nobias_denormal_lt_2, pow_ge2, realTheory.REAL_LE_MUL])

fun tac thm =
   REPEAT strip_tac
   \\ match_mp_tac (Q.SPECL [`a`, `b - c`, `x * b - c`] thm)
   \\ rsimp [realTheory.REAL_LE_SUB_CANCEL2, GSYM realTheory.REAL_LE_LDIV_EQ,
             realTheory.REAL_DIV_REFL, realTheory.REAL_SUB_ADD]

val weaken_leq = Q.prove(
    `!x a b c. 1r <= x /\ a <= b - c /\ 0 < b ==> a <= x * b - c`,
    tac realTheory.REAL_LE_TRANS
    )

val weaken_lt = Q.prove(
    `!x a b c. 1r <= x /\ a < b - c /\ 0 < b ==> a < x * b - c`,
    tac realTheory.REAL_LTE_TRANS
    )

val abs_diff1 = Q.prove(
   `!s:word1 a b.
       a < b ==> (abs (-1 pow w2n s * a - -1 pow w2n s * b) = (b - a))`,
   wordsLib.Cases_word_value \\ rrw [])

val abs_diff2 = Q.prove(
   `!s:word1 a b.
       b < a ==> (abs (-1 pow w2n s * a - -1 pow w2n s * b) = (a - b))`,
   wordsLib.Cases_word_value \\ rrw [])

val abs_diff1a =
   abs_diff1
   |> Q.SPECL [`(y:('t,'w) float).Sign`,
               `(2 / 2 pow bias (:'w)) *
                (&w2n (x:('t,'w) float).Significand / 2 pow precision (:'t))`,
               `(2 pow w2n (y:('t,'w) float).Exponent / 2 pow bias (:'w)) *
                (1 + &w2n y.Significand / 2 pow precision (:'t))`]

val abs_diff1b =
   abs_diff1
   |> Q.SPECL [`(y:('t,'w) float).Sign`,
               `(2 pow w2n (x:('t,'w) float).Exponent / 2 pow bias (:'w)) *
                (1 + &w2n x.Significand / 2 pow precision (:'t))`,
               `(2 pow (p + (w2n (x:('t,'w) float).Exponent + 1)) /
                2 pow bias (:'w)) *
                (1 + &w2n (y:('t,'w) float).Significand /
                2 pow precision (:'t))`]

val abs_diff1c =
   abs_diff1
   |> Q.SPECL [`(y:('t,'w) float).Sign`,
               `(2 / 2 pow bias (:'w)) *
                (&w2n (x:('t,'w) float).Significand / 2 pow precision (:'t))`,
               `(2 / 2 pow bias (:'w)) *
                (&w2n (y:('t,'w) float).Significand / 2 pow precision (:'t))`]

val abs_diff1d =
   abs_diff1
   |> Q.SPECL [`(y:('t,'w) float).Sign`,
               `(2 pow w2n (y:('t,'w) float).Exponent / 2 pow bias (:'w)) *
                (1 + &w2n (x:('t,'w) float).Significand /
                2 pow precision (:'t))`,
               `(2 pow w2n (y:('t,'w) float).Exponent / 2 pow bias (:'w)) *
                (1 + &w2n y.Significand / 2 pow precision (:'t))`]

val abs_diff1e =
   abs_diff1
   |> Q.SPECL [`(y:('t,'w) float).Sign`,
               `(2 / 2 pow bias (:'w))`,
               `(2 pow w2n (y:('t,'w) float).Exponent / 2 pow bias (:'w)) *
                (1 + &w2n y.Significand / 2 pow precision (:'t))`]

val abs_diff1f =
   abs_diff1
   |> Q.SPECL [`(y:('t,'w) float).Sign`,
               `(2 pow w2n (x:('t,'w) float).Exponent / 2 pow bias (:'w))`,
               `(2 pow w2n (y:('t,'w) float).Exponent / 2 pow bias (:'w)) *
                (1 + &w2n y.Significand / 2 pow precision (:'t))`]

val abs_diff2a =
   abs_diff2
   |> Q.SPECL [`(y:('t,'w) float).Sign`,
               `(2 pow w2n (x:('t,'w) float).Exponent / 2 pow bias (:'w)) *
                (1 + &w2n x.Significand / 2 pow precision (:'t))`,
               `(2 / 2 pow bias (:'w)) *
                (&w2n (y:('t,'w) float).Significand / 2 pow precision (:'t))`]

val abs_diff2b =
   abs_diff2
   |> Q.SPECL [`(y:('t,'w) float).Sign`,
               `(2 pow (p + (w2n (y:('t,'w) float).Exponent + 1)) /
                2 pow bias (:'w)) *
                (1 + &w2n (x:('t,'w) float).Significand /
                2 pow precision (:'t))`,
               `(2 pow w2n (y:('t,'w) float).Exponent / 2 pow bias (:'w)) *
                (1 + &w2n y.Significand / 2 pow precision (:'t))`]

val abs_diff2c =
   abs_diff2
   |> Q.SPECL [`(y:('t,'w) float).Sign`,
               `(2 / 2 pow bias (:'w)) *
                (&w2n (x:('t,'w) float).Significand / 2 pow precision (:'t))`,
               `(2 / 2 pow bias (:'w)) *
                (&w2n (y:('t,'w) float).Significand / 2 pow precision (:'t))`]

val abs_diff2d =
   abs_diff2
   |> Q.SPECL [`(y:('t,'w) float).Sign`,
               `(2 pow w2n (y:('t,'w) float).Exponent / 2 pow bias (:'w)) *
                (1 + &w2n (x:('t,'w) float).Significand /
                2 pow precision (:'t))`,
               `(2 pow w2n (y:('t,'w) float).Exponent / 2 pow bias (:'w)) *
                (1 + &w2n y.Significand / 2 pow precision (:'t))`]

val abs_diff2e =
   abs_diff2
   |> Q.SPECL [`(y:('t,'w) float).Sign`,
               `(2 pow (w2n (y:('t,'w) float).Exponent + 1) /
                 2 pow bias (:'w))`,
               `(2 pow w2n (y:('t,'w) float).Exponent / 2 pow bias (:'w)) *
                (1 + &w2n (-1w: 't word) / 2 pow precision (:'t))`]

fun abs_diff_tac thm =
   SUBGOAL_THEN
      (boolSyntax.rand (Thm.concl thm))
      (fn th => rewrite_tac [REWRITE_RULE [realTheory.REAL_MUL_ASSOC] th])

val diff_exponent_boundary = Q.prove(
   `!x: ('t, 'w) float y: ('t, 'w) float.
      exponent_boundary y x ==>
      (abs (float_to_real x - float_to_real y) = ULP (y.Exponent, (:'t)))`,
   rw [ULP_def, exponent_boundary_def, float_to_real_def]
   >- (Cases_on `x.Exponent` \\ fs [])
   \\ abs_diff_tac abs_diff2e
   >- (match_mp_tac abs_diff2e
       \\ simp [realTheory.REAL_LT_RDIV_EQ, realTheory.REAL_LT_LMUL,
                realLib.REAL_ARITH ``2 * a = a * 2r``,
                realLib.REAL_ARITH ``1 + n < 2 = n < 1r``, cancel_rwts,
                REWRITE_RULE [arithmeticTheory.ADD1] realTheory.pow]
       \\ simp [realTheory.REAL_LT_LDIV_EQ, realTheory.REAL_OF_NUM_POW,
                w2n_lt_pow]
      )
   \\ simp [realTheory.REAL_EQ_RDIV_EQ, realTheory.POW_ADD,
            realTheory.REAL_SUB_RDISTRIB, cancel_rwts]
   \\ simp [realLib.REAL_ARITH
              ``(a * b * c - a * d * e) = a * (b * c - d * e: real)``,
            (GSYM o ONCE_REWRITE_RULE [realTheory.REAL_MUL_COMM])
               realTheory.REAL_EQ_RDIV_EQ,
            realTheory.REAL_DIV_REFL]
   \\ simp [realTheory.REAL_DIV_RMUL, realTheory.REAL_EQ_SUB_RADD,
            realTheory.REAL_ADD_RDISTRIB, wordsTheory.w2n_minus1,
            wordsTheory.dimword_def]
   \\ rsimp [realTheory.REAL_OF_NUM_POW,
             DECIDE ``0 < n ==> (1 + (n + (n - 1)) = 2n * n)``]
   )

val not_next_tac =
   REPEAT strip_tac
   \\ imp_res_tac arithmeticTheory.LESS_EQUAL_ADD
   \\ imp_res_tac arithmeticTheory.LESS_ADD_1
   \\ pop_assum kall_tac
   \\ rfs [DECIDE ``1 < b ==> ((b - 1 = e) = (b = e + 1n))``]
   \\ simp [arithmeticTheory.LEFT_ADD_DISTRIB]

local
   val lem1 = Q.prove(
      `!a b c. a < b /\ 1n < c ==> 2 * a + 2 <= b * c`,
      REPEAT strip_tac
      \\ imp_res_tac arithmeticTheory.LESS_ADD_1
      \\ simp []
      )

   val lem1b = Q.prove(
      `!a b c. a + 1 < b /\ 1n < c ==> 2 * a + 2 < b * c`,
      REPEAT strip_tac
      \\ imp_res_tac arithmeticTheory.LESS_ADD_1
      \\ simp []
      )

   val lem2 = Q.prove(
      `!x. x <> 0w ==> 1 < 2 EXP w2n x`,
      Cases
      \\ rw []
      \\ `0 < n` by decide_tac
      \\ imp_res_tac arithmeticTheory.LESS_ADD_1
      \\ simp [GSYM arithmeticTheory.ADD1, arithmeticTheory.EXP,
               DECIDE ``0n < n ==> 1 < 2 * n``]
      )

   val lem3 = Q.prove(
      `!a b c. 2n <= b /\ 2 <= c /\ a < b ==>  2 * a + c <= b * c`,
      not_next_tac
      )

   val lem3b = Q.prove(
      `!a b c d. 0 < b /\ 2n <= d /\ 2 <= c /\ a < d ==>
                 2 * a + c < b * c + d * c`,
      not_next_tac
      )

   val lem3c = Q.prove(
      `!a b c. 2n <= b /\ 2 <= c /\ a + 1 < b ==> 2 * a + c < b * c`,
      not_next_tac
      )

   val lem4 = Q.prove(
      `!a b c d. 1n < b /\ (4 <= a /\ c < b \/
                            2 <= a /\ c < b - 1 \/
                            2 <= a /\ c < b /\ 0 < d) ==>
                 a + (b + c) <= a * (b + d)`,
      not_next_tac
      )

   val lem4b = Q.prove(
      `!a b c d. 2n <= a /\ 1n < b /\ 0 < d /\ c < b ==>
                 a + (b + c) < a * (b + d)`,
      not_next_tac
      )

   (* |- 1 < 2 ** precision (:'a) *)
   val lem5 = REWRITE_RULE [wordsTheory.dimword_def] wordsTheory.ONE_LT_dimword

   val t1 =
      simp [realTheory.REAL_LE_LDIV_EQ, realTheory.REAL_LT_LDIV_EQ,
            realTheory.POW_ADD, realTheory.REAL_SUB_RDISTRIB,
            realTheory.REAL_LE_SUB_LADD, realTheory.REAL_LT_SUB_LADD,
            GSYM realaxTheory.REAL_LDISTRIB, cancel_rwt, cancel_rwts]
      \\ simp [realTheory.REAL_LDISTRIB]
   val t2 =
      once_rewrite_tac
          [realTheory.REAL_LT_LMUL
           |> Q.SPEC `2 pow bias (:'w)`
           |> SIMP_RULE (srw_ss()) []
           |> GSYM]
      \\ rewrite_tac [cancel_rwts]
      \\ simp [realTheory.POW_ADD]
      \\ once_rewrite_tac
           [realLib.REAL_ARITH ``a * (b * c) * d = b * (a * c * d): real``]
      \\ simp [realTheory.REAL_LT_LMUL, realTheory.REAL_LDISTRIB]
      \\ match_mp_tac
           (realLib.REAL_ARITH
               ``a < 1r /\ 1 <= b /\ 0 <= c ==> 1 + a < b * 2 + c``)
      \\ simp [nobias_denormal_lt_1, realTheory.REAL_LE_MUL,
               realTheory.POW_2_LE1]
   val t3 =
      simp [realTheory.REAL_LE_LDIV_EQ, realTheory.REAL_LT_LDIV_EQ]
      \\ simp [realTheory.POW_ADD, cancel_rwts,
               realTheory.REAL_SUB_RDISTRIB, realTheory.REAL_DIV_RMUL]
      \\ simp [realTheory.REAL_DIV_RMUL,
               realLib.REAL_ARITH
                   ``a * (b + c) * d = a * (b * d + c * d): real``]
      \\ simp [realTheory.REAL_LE_SUB_LADD, realTheory.REAL_LT_SUB_LADD,
               realTheory.REAL_LDISTRIB]
   val t4 =
      match_mp_tac (realLib.REAL_ARITH ``a <= b /\ 0r <= c ==> a <= b + c``)
      \\ simp [realTheory.REAL_LE_MUL, GSYM realTheory.REAL_LE_SUB_LADD]
      \\ once_rewrite_tac
           [realLib.REAL_ARITH
               ``p * (a * 2r) * x - (a * x + a * y) =
                 a * ((p * (2 * x)) - (x + y))``]
      \\ match_mp_tac le_mult
      \\ simp []
      \\ match_mp_tac weaken_leq
      \\ simp [realTheory.POW_2_LE1, realTheory.REAL_LT_MUL,
               realLib.REAL_ARITH ``2r * a - (a + z) = a - z``]
   fun tac thm q =
      abs_diff_tac thm
      >- (match_mp_tac thm \\ t2)
      \\ Q.ABBREV_TAC `z = &w2n ^(Parse.Term q)`
      \\ t3
in
   fun tac1 thm =
      abs_diff_tac thm
      >- (match_mp_tac thm \\ simp [subnormal_lt_normal])
      \\ t1
      \\ match_mp_tac (realLib.REAL_ARITH ``0r <= c /\ a <= b ==> a <= b + c``)
      \\ simp [realTheory.REAL_LE_MUL, realTheory.REAL_OF_NUM_POW,
               fcpTheory.DIMINDEX_GE_1, lem1, lem2, lem3, lem5,
               word_ge1, w2n_lt_pow]
   val tac2 =
      tac abs_diff1b `(x: ('t, 'w) float).Significand`
      \\ t4
      \\ `?q. 1 <= q /\ (2 pow precision (:'t) = z + q)`
      by (ASSUME_TAC (Q.ISPEC `(x: ('t, 'w) float).Significand` w2n_lt_pow)
           \\ pop_assum
                (strip_assume_tac o MATCH_MP arithmeticTheory.LESS_ADD_1)
           \\ qexists_tac `&(p' + 1)`
           \\ simp [realTheory.REAL_OF_NUM_POW, Abbr `z`])
      \\ rsimp []
   val tac3 =
      tac abs_diff2b `(y: ('t, 'w) float).Significand`
      \\ once_rewrite_tac
           [div_le
            |> Q.SPEC `2 pow w2n (y:('t, 'w) float).Exponent`
            |> SIMP_RULE (srw_ss()) []
            |> GSYM]
      \\ simp [GSYM realTheory.REAL_DIV_ADD, GSYM realTheory.REAL_ADD_LDISTRIB,
               cancel_rwts]
      \\ rsimp [realTheory.REAL_OF_NUM_POW, Abbr `z`]
      \\ match_mp_tac lem4
      \\ fs [exponent_boundary_def]
      \\ rfs [w2n_lt_pow, w2n_lt_pow_sub1, word_lt0, ge4, lem5]
      \\ `p <> 0` by (strip_tac \\ fs [DECIDE ``(1 = x + 1) = (x = 0n)``])
      \\ fs [ge4]
   val tac4 =
      abs_diff_tac abs_diff1a
      >- (match_mp_tac abs_diff1a \\ simp [subnormal_lt_normal])
      \\ t1
      \\ match_mp_tac (realLib.REAL_ARITH ``0r <= c /\ a < b ==> a < b + c``)
      \\ simp [realTheory.REAL_LE_MUL, realTheory.REAL_OF_NUM_POW,
               fcpTheory.DIMINDEX_GE_1, not_max_suc_lt_dimword, lem1b, lem2]
   val tac5 =
      abs_diff_tac abs_diff2a
      >- (match_mp_tac abs_diff2a \\ simp [subnormal_lt_normal])
      \\ t1
      \\ simp [realTheory.REAL_OF_NUM_POW]
      \\ match_mp_tac lem3b
      \\ simp [realTheory.REAL_LE_MUL, realTheory.REAL_OF_NUM_POW,
               fcpTheory.DIMINDEX_GE_1, word_lt0, not_max_suc_lt_dimword,
               lem1b, lem2, word_ge1, w2n_lt_pow]
   val tac6 =
      tac abs_diff1b `(x: ('t, 'w) float).Significand`
      \\ match_mp_tac (realLib.REAL_ARITH ``a < b /\ 0r <= c ==> a < b + c``)
      \\ simp [realTheory.REAL_LE_MUL, GSYM realTheory.REAL_LT_SUB_LADD]
      \\ once_rewrite_tac
           [realLib.REAL_ARITH
               ``p * (a * 2r) * x - (a * x + a * y) =
                 a * ((p * (2 * x)) - (x + y))``]
      \\ match_mp_tac (ONCE_REWRITE_RULE [realTheory.REAL_MUL_COMM] gt_mult)
      \\ simp []
      \\ match_mp_tac weaken_lt
      \\ simp [realTheory.POW_2_LE1, realTheory.REAL_LT_MUL,
               realLib.REAL_ARITH ``2r * a - (a + z) = a - z``]
      \\ simp [GSYM realTheory.REAL_LT_ADD_SUB, not_max_suc_lt_dimword,
               realTheory.REAL_OF_NUM_POW, Abbr `z`]
   val tac7 =
      tac abs_diff2b `(y: ('t, 'w) float).Significand`
      \\ once_rewrite_tac
           [realTheory.REAL_LT_RDIV
            |> Q.SPECL [`x`, `y`, `2 pow w2n (y:('t, 'w) float).Exponent`]
            |> SIMP_RULE (srw_ss()) []
            |> GSYM]
      \\ simp [GSYM realTheory.REAL_DIV_ADD, GSYM realTheory.REAL_ADD_LDISTRIB,
               cancel_rwts]
      \\ rsimp [realTheory.REAL_OF_NUM_POW, Abbr `z`]
      \\ match_mp_tac lem4b
      \\ rfs [w2n_lt_pow, word_lt0, lem5]
end

val diff_exponent_ULP = Q.prove(
   `!x: ('t, 'w) float y: ('t, 'w) float.
      (x.Sign = y.Sign) /\ x.Exponent <> y.Exponent /\
      ~exponent_boundary y x ==>
      ULP (x.Exponent, (:'t)) <= abs (float_to_real x - float_to_real y)`,
   rw [ULP_def, float_to_real_def]
   >- tac1 abs_diff1a
   >- tac1 abs_diff2a
   \\ `w2n x.Exponent < w2n y.Exponent \/ w2n y.Exponent < w2n x.Exponent`
   by metis_tac [arithmeticTheory.LESS_LESS_CASES, wordsTheory.w2n_11]
   \\ imp_res_tac arithmeticTheory.LESS_ADD_1
   \\ simp []
   >- tac2
   \\ fs []
   \\ tac3
   )

val diff_exponent_ULP_gt = Q.prove(
   `!x: ('t, 'w) float y: ('t, 'w) float.
      (x.Sign = y.Sign) /\ x.Exponent <> y.Exponent /\
      x.Significand NOTIN {0w; -1w} ==>
      ULP (x.Exponent, (:'t)) < abs (float_to_real x - float_to_real y)`,
   rw [ULP_def, float_to_real_def]
   >- tac4
   >- tac5
   \\ `w2n x.Exponent < w2n y.Exponent \/ w2n y.Exponent < w2n x.Exponent`
   by metis_tac [arithmeticTheory.LESS_LESS_CASES, wordsTheory.w2n_11]
   \\ imp_res_tac arithmeticTheory.LESS_ADD_1
   \\ simp []
   >- tac6
   \\ fs []
   \\ tac7
   )

val lem = Q.prove(
   `!a b m. 2n <= a /\ 2 <= b /\ 1 <= m ==> a * b + b < 2 * (m * a * b)`,
   REPEAT strip_tac
   \\ imp_res_tac arithmeticTheory.LESS_EQUAL_ADD
   \\ simp [arithmeticTheory.LEFT_ADD_DISTRIB]
   )

val diff_exponent_ULP_gt0 = Q.prove(
   `!x: ('t, 'w) float y: ('t, 'w) float.
      (x.Sign = y.Sign) /\ x.Exponent <+ y.Exponent /\
      (x.Significand = 0w) /\ ~float_is_zero x ==>
      ULP (x.Exponent, (:'t)) < abs (float_to_real x - float_to_real y)`,
   rw [ULP_def, float_to_real_def, realTheory.ABS_NEG, abs_float_value,
       abs_significand, realTheory.ABS_MUL, realTheory.ABS_DIV,
       realTheory.ABS_N, gt0_abs, wordsTheory.WORD_LO]
   >- rfs [realTheory.REAL_LT_LDIV_EQ, realTheory.POW_ADD,
           realTheory.REAL_SUB_LDISTRIB, realTheory.REAL_SUB_RDISTRIB,
           realTheory.REAL_LT_SUB_LADD, cancel_rwts, cancel_rwt, float_is_zero]
   \\ abs_diff_tac abs_diff1f
   >- (match_mp_tac abs_diff1f
       \\ simp [realTheory.REAL_LT_LDIV_EQ, realTheory.REAL_ADD_LDISTRIB,
                cancel_rwts]
       \\ simp [realTheory.REAL_OF_NUM_POW, realTheory.REAL_LE_MUL,
                realLib.REAL_ARITH ``a < b /\ 0 <= c ==> a < b + c: real``])
   \\ simp [realTheory.REAL_LT_LDIV_EQ, realTheory.POW_ADD,
            realTheory.REAL_SUB_LDISTRIB, realTheory.REAL_SUB_RDISTRIB,
            realTheory.REAL_LT_SUB_LADD, cancel_rwts, cancel_rwt]
   \\ match_mp_tac (realLib.REAL_ARITH ``a < b /\ 0r <= c ==> a < b + c``)
   \\ simp [realTheory.REAL_LE_MUL, realTheory.REAL_OF_NUM_POW]
   \\ imp_res_tac arithmeticTheory.LESS_ADD_1
   \\ simp [arithmeticTheory.EXP_ADD, lem, fcpTheory.DIMINDEX_GE_1, exp_ge4,
            word_ge1]
   )

val lem = Q.prove(
   `!a b. 2 <= a /\ 4n <= b ==> 2 * a + 2 < a * b`,
   not_next_tac
   )

val diff_exponent_ULP_gt01 = Q.prove(
   `!x: ('t, 'w) float y: ('t, 'w) float.
      (x.Sign = y.Sign) /\ x.Exponent <> y.Exponent /\
      y.Significand <> -1w  /\ (x.Significand = 0w) /\ (x.Exponent = 1w) ==>
      ULP (x.Exponent, (:'t)) < abs (float_to_real x - float_to_real y)`,
   rw [ULP_def, float_to_real_def, realTheory.ABS_NEG, abs_float_value,
       abs_significand, realTheory.ABS_MUL, realTheory.ABS_DIV,
       realTheory.ABS_N, gt0_abs, nobias_denormal_lt_1,
       realLib.REAL_ARITH ``a - a * b = a * (1 - b): real``,
       realLib.REAL_ARITH ``a < 1 ==> (abs (1 - a) = 1 - a)``]
   >- (simp [realTheory.REAL_LT_LDIV_EQ, realTheory.POW_ADD, cancel_rwts,
             realTheory.REAL_SUB_LDISTRIB, realTheory.REAL_SUB_RDISTRIB,
             realTheory.REAL_LT_SUB_LADD]
       \\ rewrite_tac [simpLib.SIMP_PROVE (srw_ss()++ARITH_ss) []
                         ``&(2n * n + 2) = 2r * &(n + 1)``]
       \\ simp [realTheory.REAL_LT_LMUL, realTheory.REAL_OF_NUM_POW,
                not_max_suc_lt_dimword])
   \\ `1w <+ y.Exponent`
   by metis_tac
        [wordsLib.WORD_DECIDE ``a:'a word <> 0w /\ a <> 1w ==> 1w <+ a``]
   \\ fs [wordsTheory.WORD_LO]
   \\ abs_diff_tac abs_diff1e
   >- (match_mp_tac abs_diff1e
       \\ simp [realTheory.REAL_LT_LDIV_EQ, realTheory.REAL_LDISTRIB,
                cancel_rwts, cancel_rwt]
       \\ match_mp_tac (realLib.REAL_ARITH ``a < b /\ 0r <= c ==> a < b + c``)
       \\ simp [realTheory.REAL_LE_MUL, realTheory.REAL_OF_NUM_POW])
   \\ simp [realTheory.REAL_LT_LDIV_EQ, realTheory.POW_ADD,
            realTheory.REAL_SUB_LDISTRIB, realTheory.REAL_SUB_RDISTRIB,
            realTheory.REAL_LT_SUB_LADD, cancel_rwts, cancel_rwt]
   \\ match_mp_tac (realLib.REAL_ARITH ``a < b /\ 0r <= c ==> a < b + c``)
   \\ simp [realTheory.REAL_LE_MUL, realTheory.REAL_OF_NUM_POW, lem,
            fcpTheory.DIMINDEX_GE_1, exp_ge4]
   )

val lem = Q.prove(
   `!a b c. a < b /\ 2n <= c ==> 2 * a < b * c`,
   not_next_tac
   )

val lem2 = Q.prove(
   `!a b c. a < b /\ 1n <= c ==> a + b < 2 * (c * b)`,
   not_next_tac
   )

val float_to_real_lt_exponent_mono = Q.prove(
   `!x: ('t, 'w) float y: ('t, 'w) float.
      (x.Sign = y.Sign) /\ abs (float_to_real x) <= abs (float_to_real y) ==>
      x.Exponent <=+ y.Exponent`,
   rw [float_to_real_def, realTheory.ABS_NEG, abs_float_value,
       abs_significand, realTheory.ABS_MUL, realTheory.ABS_DIV,
       realTheory.ABS_N, gt0_abs, wordsTheory.WORD_LS]
   >| [
      Cases_on `x.Sign = y.Sign`
      \\ simp [realTheory.REAL_NOT_LE]
      \\ once_rewrite_tac
           [realTheory.REAL_LT_RMUL
            |> Q.SPECL [`x`, `y`, `2 pow bias (:'w)`]
            |> REWRITE_RULE [zero_lt_twopow]
            |> GSYM]
      \\ rewrite_tac [cancel_rwts, cancel_rwt]
      \\ simp [realTheory.REAL_LDISTRIB, realTheory.REAL_RDISTRIB,
               realTheory.REAL_OF_NUM_POW, realTheory.REAL_DIV_RMUL,
               realTheory.REAL_LT_LDIV_EQ, realTheory.mult_ratr,
               cancel_rwts, cancel_rwt, w2n_lt_pow,
               word_ge1, lem, DECIDE ``a < b ==> a < x + b: num``],
      (* --- *)
      pop_assum mp_tac
      \\ Cases_on `w2n x.Exponent <= w2n y.Exponent`
      \\ simp [realTheory.REAL_NOT_LE]
      \\ fs [arithmeticTheory.NOT_LESS_EQUAL]
      \\ once_rewrite_tac
           [realTheory.REAL_LT_RMUL
            |> Q.SPECL [`x`, `y`, `2 pow bias (:'w)`]
            |> REWRITE_RULE [zero_lt_twopow]
            |> GSYM]
      \\ rewrite_tac [cancel_rwts, cancel_rwt]
      \\ once_rewrite_tac
           [realTheory.REAL_LT_RMUL
            |> Q.SPECL [`x`, `y`, `2 pow precision (:'t)`]
            |> REWRITE_RULE [zero_lt_twopow]
            |> GSYM]
      \\ rewrite_tac [cancel_rwts, cancel_rwt]
      \\ simp [realTheory.REAL_OF_NUM_POW]
      \\ match_mp_tac (DECIDE ``a < b ==> a < x + b: num``)
      \\ imp_res_tac arithmeticTheory.LESS_ADD_1
      \\ asm_simp_tac bool_ss
             [arithmeticTheory.EXP_ADD, arithmeticTheory.LT_MULT_RCANCEL,
              GSYM arithmeticTheory.RIGHT_ADD_DISTRIB,
              DECIDE ``a * (b * (c * d)) = (a * c * d) * b: num``]
      \\ simp [lem2, w2n_lt_pow]
   ])

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

fun tac thm =
   abs_diff_tac thm
   >- (match_mp_tac thm
       \\ simp [realTheory.REAL_LT_LMUL, realTheory.REAL_LT_DIV,
                realTheory.REAL_LT_LDIV_EQ, realTheory.REAL_DIV_RMUL])
   \\ simp [realLib.REAL_ARITH ``a < b ==> (abs (a - b) = b - a)``,
            realLib.REAL_ARITH ``b < a ==> (abs (a - b) = a - b)``,
            realTheory.REAL_SUB_RDISTRIB, realTheory.REAL_LDISTRIB,
            realTheory.POW_ADD, realTheory.mult_rat]
   \\ simp [realTheory.mult_ratr]

fun tac2 thm =
   abs_diff_tac thm
   >- (match_mp_tac thm
       \\ simp [realTheory.REAL_LT_LMUL, realTheory.REAL_LT_DIV,
                realTheory.REAL_LT_LDIV_EQ, realTheory.REAL_DIV_RMUL])
   \\ simp [realLib.REAL_ARITH ``a < b ==> (abs (a - b) = b - a)``,
            realLib.REAL_ARITH ``b < a ==> (abs (a - b) = a - b)``,
            realLib.REAL_ARITH ``1 + a - (1 + b) = a - b: real``,
            GSYM realTheory.REAL_SUB_LDISTRIB, sub_rat_same_base]
   \\ simp [realTheory.POW_ADD, realTheory.mult_rat]
   \\ simp_tac (srw_ss()++realSimps.real_ac_SS) [realTheory.mult_ratr]

val diff_significand_ULP_mul = Q.prove(
   `!x: ('t, 'w) float y: ('t, 'w) float.
        (x.Sign = y.Sign) /\ (x.Exponent = y.Exponent) ==>
        (abs (float_to_real x - float_to_real y) =
         abs (&w2n x.Significand - &w2n y.Significand) *
         ULP (x.Exponent, (:'t)))`,
   rw [ULP_def, float_to_real_def]
   \\ (Cases_on `x.Significand = y.Significand`
       >- rsimp [])
   \\ `w2n x.Significand < w2n y.Significand \/
       w2n y.Significand < w2n x.Significand`
      by metis_tac [arithmeticTheory.LESS_LESS_CASES, wordsTheory.w2n_11]
   >- tac abs_diff1c
   >- tac abs_diff2c
   >- tac2 abs_diff1d
   \\ tac2 abs_diff2d
   )

val diff_ge1 = Q.prove(
   `!a b. 1 <= abs (&a - &b) = &a <> (&b: real)`,
   lrw [realTheory.REAL_SUB, realTheory.ABS_NEG, realTheory.ABS_N]
   )

val diff_significand_ULP = Q.prove(
   `!x: ('t, 'w) float y: ('t, 'w) float.
        (x.Sign = y.Sign) /\ (x.Exponent = y.Exponent) /\
        x.Significand <> y.Significand ==>
        ULP (x.Exponent, (:'t)) <= abs (float_to_real x - float_to_real y)`,
   rw [diff_significand_ULP_mul, ULP_gt0, diff_ge1,
       ONCE_REWRITE_RULE [realTheory.REAL_MUL_COMM] le_mult]
   )

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

val ULP_same = Q.prove(
   `!x y.
      (x = y) ==>
      ~(ULP (x.Exponent, (:'t)) <= abs (float_to_real x - float_to_real y))`,
   rrw [ULP_gt0, realTheory.REAL_NOT_LE])

val diff_sign_neq = Q.prove(
   `!x: ('t, 'w) float y: ('t, 'w) float.
        ~(float_is_zero x /\ float_is_zero y) /\ x.Sign <> y.Sign ==>
        float_to_real x <> float_to_real y`,
   metis_tac [diff_sign_ULP, ULP_same]
   )

val diff_exponent_neq = Q.prove(
   `!x: ('t, 'w) float y: ('t, 'w) float.
        (x.Sign = y.Sign) /\ x.Exponent <> y.Exponent ==>
        float_to_real x <> float_to_real y`,
   REPEAT strip_tac
   \\ Cases_on `exponent_boundary y x`
   >- (fs []
       \\ imp_res_tac diff_exponent_boundary
       \\ rfs [ULP_gt0, realTheory.REAL_POS_NZ])
   \\metis_tac [diff_exponent_ULP, ULP_same]
   )

val float_to_real_eq = Q.store_thm("float_to_real_eq",
   `!x: ('t, 'w) float y: ('t, 'w) float.
       (float_to_real x = float_to_real y) =
       (x = y) \/ (float_is_zero x /\ float_is_zero y)`,
   NTAC 2 strip_tac
   \\ Cases_on `x = y`
   \\ simp []
   \\ Cases_on `float_is_zero x /\ float_is_zero y`
   \\ simp [float_is_zero_to_real_imp]
   \\ Cases_on `x.Sign <> y.Sign`
   >- metis_tac [diff_sign_neq]
   \\ Cases_on `x.Exponent <> y.Exponent`
   >- metis_tac [diff_exponent_neq]
   \\ qpat_assum `~(p /\ q)` kall_tac
   \\ fs [float_component_equality]
   \\ rw [float_to_real_def, sign_not_zero, div_twopow]
   )

val diff_float_ULP = Q.store_thm("diff_float_ULP",
   `!x: ('t, 'w) float y: ('t, 'w) float.
       float_to_real x <> float_to_real y /\ ~exponent_boundary y x ==>
       ULP (x.Exponent, (:'t)) <= abs (float_to_real x - float_to_real y)`,
   rw [float_to_real_eq, float_component_equality]
   \\ metis_tac [diff_sign_ULP, diff_exponent_ULP, diff_significand_ULP])

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

(* |- !x y. ~float_is_zero y ==>
            ((float_to_real x = float_to_real y) <=> (x = y)) *)
val float_to_real_11_right =
   float_to_real_eq
   |> Drule.SPEC_ALL
   |> Q.DISCH `~float_is_zero y`
   |> SIMP_RULE bool_ss []
   |> Q.GENL [`y`, `x`]

(* |- !x y. ~float_is_zero x ==>
            ((float_to_real x = float_to_real y) <=> (x = y))
val float_to_real_11_left =
   float_to_real_eq
   |> Drule.SPEC_ALL
   |> Q.DISCH `~float_is_zero x`
   |> SIMP_RULE bool_ss []
   |> Drule.GEN_ALL
*)

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

val diff1pos = Q.prove(
   `!a. a <> 0w ==> (&w2n a - &w2n (a + -1w) = 1)`,
   Cases
   \\ Cases_on `n`
   \\ simp [wordsTheory.n2w_SUC]
   \\ rrw [realTheory.REAL_SUB, bitTheory.SUC_SUB, DECIDE ``~(SUC n <= n)``]
   )

val diff1neg = Q.prove(
   `!a. a <> -1w ==> (&w2n a - &w2n (a + 1w) = -1)`,
   rw [realTheory.REAL_SUB, bitTheory.SUC_SUB, DECIDE ``~(SUC n <= n)``,
       GSYM wordsTheory.WORD_LS,
       ONCE_REWRITE_RULE [GSYM wordsTheory.WORD_ADD_COMM]
          wordsTheory.WORD_ADD_RIGHT_LS2]
   \\ lfs [wordsTheory.WORD_NOT_LOWER, wordsTheory.WORD_LS_word_T]
   \\ `a <=+ a + 1w` by wordsLib.WORD_DECIDE_TAC
   \\ simp [GSYM wordsTheory.word_sub_w2n]
   )

val must_be_1 = Q.prove(
   `!a b: real. 0 < b ==> ((a * b = b) = (a = 1))`,
   REPEAT strip_tac
   \\ Cases_on `a = 1`
   >- simp []
   \\ Cases_on `a < 1`
   >- rsimp [realTheory.REAL_LT_IMP_NE,
             ONCE_REWRITE_RULE [realTheory.REAL_MUL_COMM] lt_mult]
   \\ `1 < a` by rsimp []
   \\ simp [realTheory.REAL_LT_IMP_NE, gt_mult]
   )

val w2n_add1 = Q.prove(
   `!a. a <> -1w ==> (w2n a + 1 = w2n (a + 1w))`,
   Cases
   \\ lrw [wordsTheory.word_eq_n2w, wordsTheory.word_add_n2w,
           bitTheory.MOD_2EXP_MAX_def, bitTheory.MOD_2EXP_def,
           GSYM wordsTheory.dimword_def]
   )

val diff_ulp_next_float = Q.prove(
   `!x y: ('t, 'w) float.
       ~float_is_zero x /\ y.Significand NOTIN {0w; -1w} ==>
       ((abs (float_to_real y - float_to_real x) = ULP (y.Exponent,(:'t))) =
        (x = y with Significand := y.Significand - 1w) \/
        (x = y with Significand := y.Significand + 1w))`,
   REPEAT strip_tac
   \\ eq_tac
   >| [
      `~float_is_zero y` by fs [float_is_zero]
      \\ Cases_on `x.Sign <> y.Sign`
      >- prove_tac [realTheory.REAL_LT_IMP_NE, diff_sign_ULP_gt]
      \\ Cases_on `x.Exponent <> y.Exponent`
      >- prove_tac [realTheory.REAL_LT_IMP_NE, diff_exponent_ULP_gt]
      \\ fs [diff_significand_ULP_mul, must_be_1, ULP_gt0,
             float_component_equality]
      \\ Cases_on `x.Significand = y.Significand + -1w`
      \\ simp []
      \\ Cases_on `x.Significand = y.Significand + 1w`
      \\ rsimp [realLib.REAL_ARITH ``(abs x = 1) = (x = 1) \/ (x = -1)``,
                realLib.REAL_ARITH ``(a = -1 + c) = (c = a + 1r)``,
                realTheory.REAL_EQ_SUB_RADD, w2n_add1]
      \\ Cases_on `x.Significand = -1w`
      \\ simp [ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM] w2n_add1,
               wordsTheory.w2n_minus1, DECIDE ``0n < n ==> (1 + (n - 1) = n)``,
               wordsTheory.w2n_lt, prim_recTheory.LESS_NOT_EQ,
               wordsLib.WORD_ARITH_PROVE
                  ``a:'a word <> b + -1w ==> b <> a + 1w``],
      (* --- *)
      rw []
      \\ rw [float_to_real_def, abs_float_value, abs_significand,
             realTheory.ABS_MUL, realTheory.ABS_DIV, realTheory.ABS_N,
             gt0_abs, GSYM realTheory.REAL_SUB_LDISTRIB, sub_rat_same_base,
             realLib.REAL_ARITH ``1r + a - (1 + b) = a - b``]
      \\ fs [diff1pos, diff1neg, realTheory.mult_rat, ULP_def,
             realTheory.POW_ADD]
   ])

val diff_ulp_next_float0 = Q.prove(
   `!x y: ('t, 'w) float.
       ~float_is_zero x /\ ~float_is_zero y /\ (y.Significand = 0w) /\
       abs (float_to_real y) <= abs (float_to_real x) ==>
       ((abs (float_to_real y - float_to_real x) = ULP (y.Exponent,(:'t))) =
        (x = y with Significand := y.Significand + 1w))`,
   REPEAT strip_tac
   \\ eq_tac
   >| [
      Cases_on `x.Sign <> y.Sign`
      >- prove_tac [realTheory.REAL_LT_IMP_NE, diff_sign_ULP_gt]
      \\ imp_res_tac float_to_real_lt_exponent_mono
      \\ Cases_on `x.Exponent <> y.Exponent`
      >- prove_tac
            [realTheory.REAL_LT_IMP_NE, diff_exponent_ULP_gt0,
             wordsLib.WORD_DECIDE ``a <> b /\ a <=+ b ==> a <+ b:'a word``]
      \\ fs [diff_significand_ULP_mul, must_be_1, ULP_gt0,
             float_component_equality, realTheory.ABS_NEG, realTheory.ABS_N]
      \\ Cases_on `x.Significand`
      \\ simp [],
      (* --- *)
      rw []
      \\ rw [float_to_real_def, abs_float_value, abs_significand,
             realTheory.ABS_MUL, realTheory.ABS_DIV, realTheory.ABS_N,
             realTheory.ABS_NEG, gt0_abs, realTheory.REAL_LDISTRIB,
             realLib.REAL_ARITH ``a - (a + c) = -c: real``]
      \\ fs [diff1pos, diff1neg, realTheory.mult_rat, ULP_def,
             realTheory.POW_ADD]
   ])

val diff_ulp_next_float01 = Q.prove(
   `!x y: ('t, 'w) float.
       ~float_is_zero x /\ ~float_is_zero y /\
       x.Significand <> -1w /\ (y.Significand = 0w) /\ (y.Exponent = 1w) ==>
       ((abs (float_to_real y - float_to_real x) = ULP (y.Exponent,(:'t))) =
        (x = y with Significand := y.Significand + 1w))`,
   REPEAT strip_tac
   \\ eq_tac
   >| [
      Cases_on `x.Sign <> y.Sign`
      >- prove_tac [realTheory.REAL_LT_IMP_NE, diff_sign_ULP_gt]
      \\ Cases_on `x.Exponent <> y.Exponent`
      >- prove_tac [realTheory.REAL_LT_IMP_NE, diff_exponent_ULP_gt01]
      \\ fs [diff_significand_ULP_mul, must_be_1, ULP_gt0,
             float_component_equality, realTheory.ABS_NEG, realTheory.ABS_N]
      \\ Cases_on `x.Significand`
      \\ simp [],
      (* --- *)
      rw []
      \\ rw [float_to_real_def, abs_float_value, abs_significand,
             realTheory.ABS_MUL, realTheory.ABS_DIV, realTheory.ABS_N,
             realTheory.ABS_NEG, gt0_abs, realTheory.REAL_LDISTRIB,
             realLib.REAL_ARITH ``a - (a + c) = -c: real``]
      \\ fs [diff1pos, diff1neg, realTheory.mult_rat, ULP_def,
             realTheory.POW_ADD]
   ])

val float_min_equiv_ULP_eq_float_to_real = Q.prove(
   `!y: ('t, 'w) float.
       (abs (float_to_real y) = ULP (y.Exponent,(:'t))) =
       y IN {float_plus_min (:'t # 'w); float_minus_min (:'t # 'w)}`,
   strip_tac
   \\ Cases_on `float_is_zero y`
   >- fs [float_sets, zero_to_real, float_components, float_distinct,
          GSYM float_distinct, ULP_gt0,
          realLib.REAL_ARITH ``0 < b ==> 0r <> b``]
   \\ Cases_on `(y = float_plus_min (:'t # 'w)) \/
                (y = float_minus_min (:'t # 'w))`
   >- rw [GSYM neg_ulp, GSYM ulp, float_minus_min_def, float_components,
          ulp_def, ULP_gt0, gt0_abs, realTheory.REAL_LT_IMP_LE,
          realTheory.ABS_NEG]
   \\ fs []
   \\ rw [float_to_real_def, ULP_def, abs_float_value, abs_significand,
          realTheory.ABS_MUL, realTheory.ABS_DIV, realTheory.ABS_N, gt0_abs,
          realTheory.REAL_EQ_RDIV_EQ]
   \\ simp [realTheory.POW_ADD, GSYM realTheory.REAL_LDISTRIB,
            cancel_rwts, cancel_rwt, realTheory.REAL_DIV_REFL,
            realTheory.REAL_EQ_RDIV_EQ
            |> ONCE_REWRITE_RULE [GSYM realTheory.REAL_MUL_COMM]
            |> GSYM]
   >| [
      strip_tac
      \\ `y.Significand = 1w`
      by metis_tac [wordsTheory.w2n_11, wordsTheory.word_1_n2w]
      \\ fs [float_plus_min_def, float_minus_min_def, float_negate_def,
             float_component_equality]
      \\ metis_tac [sign_inconsistent],
      simp [realTheory.REAL_OF_NUM_POW, GSYM wordsTheory.dimword_def,
            DECIDE ``1 < a ==> a + b <> 1n``]
   ])

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

val tac =
   REPEAT strip_tac
   \\ spose_not_then assume_tac
   \\ `float_to_real a <> float_to_real b`
   by metis_tac [float_to_real_eq]
   \\ imp_res_tac diff_float_ULP
   \\ rlfs []

val diff_lt_ulp_eq0 = Q.store_thm("diff_lt_ulp_eq0",
   `!a: ('t, 'w) float b: ('t, 'w) float x.
       ~exponent_boundary b a /\
       abs (x - float_to_real a) < ULP (a.Exponent, (:'t)) /\
       abs (x - float_to_real b) < ULP (a.Exponent, (:'t)) /\
       abs (float_to_real a) <= abs x /\ abs (float_to_real b) <= abs x /\
       ~float_is_zero a ==>
       (b = a)`,
   tac)

val diff_lt_ulp_even = Q.store_thm("diff_lt_ulp_even",
   `!a: ('t, 'w) float b: ('t, 'w) float x.
       ~exponent_boundary b a /\
       2 * abs (float_to_real a - x) < ULP (a.Exponent, (:'t)) /\
       2 * abs (float_to_real b - x) < ULP (a.Exponent, (:'t)) /\
       ~float_is_zero a ==>
       (b = a)`,
   REPEAT strip_tac
   \\ spose_not_then assume_tac
   \\ `float_to_real a <> float_to_real b`
   by metis_tac [float_to_real_eq]
   \\ imp_res_tac diff_float_ULP
   \\ rlfs []
   )

val diff_lt_ulp_even4 = Q.store_thm("diff_lt_ulp_even4",
   `!a: ('t, 'w) float b: ('t, 'w) float x.
       ~exponent_boundary b a /\
       4 * abs (float_to_real a - x) <= ULP (a.Exponent, (:'t)) /\
       4 * abs (float_to_real b - x) <= ULP (a.Exponent, (:'t)) /\
       ~float_is_zero a ==>
       (b = a)`,
   REPEAT strip_tac
   \\ spose_not_then assume_tac
   \\ `float_to_real a <> float_to_real b`
   by metis_tac [float_to_real_eq]
   \\ imp_res_tac diff_float_ULP
   \\ rlfs []
   )

(*
val diff_lt_ulp_eq_pos = Q.store_thm("diff_lt_ulp_eq_pos",
   `!a: ('t, 'w) float b: ('t, 'w) float x.
       ~exponent_boundary b a /\
       abs (x - float_to_real a) < ULP (a.Exponent, (:'t)) /\
       abs (x - float_to_real b) < ULP (a.Exponent, (:'t)) /\
       float_to_real a >= x /\ float_to_real b >= x /\
       ~float_is_zero b ==>
       (a = b)`,
   tac)

val diff_lt_ulp_eq_neg = Q.store_thm("diff_lt_ulp_eq_neg",
   `!a: ('t, 'w) float b: ('t, 'w) float x.
       ~exponent_boundary b a /\
       abs (x - float_to_real a) < ULP (a.Exponent, (:'t)) /\
       abs (x - float_to_real b) < ULP (a.Exponent, (:'t)) /\
       float_to_real a <= x /\ float_to_real b <= x /\
       ~float_is_zero b ==>
       (a = b)`,
   tac)
*)

val exponent_boundary_lt = Q.prove(
   `!a b.
      exponent_boundary a b ==> abs (float_to_real a) < abs (float_to_real b)`,
   rrw [float_to_real_def, exponent_boundary_def, abs_float_value,
        abs_significand, realTheory.ABS_MUL, realTheory.ABS_DIV,
        realTheory.ABS_N, gt0_abs]
   >- (match_mp_tac lt_mult
       \\ rsimp [nobias_denormal_lt_1, realTheory.REAL_LT_DIV])
   \\ simp [realTheory.REAL_LT_LMUL, realTheory.REAL_LT_RDIV_EQ, cancel_rwts,
            realTheory.POW_ADD, realLib.REAL_ARITH ``1 + x < 2 = x < 1r``,
            nobias_denormal_lt_1]
   )

val exponent_boundary_not_float_zero = Q.prove(
   `!x y. exponent_boundary x y ==> ~float_is_zero y`,
   rw [exponent_boundary_def, float_is_zero]
   \\ strip_tac
   \\ fs []
   )

val ULP_lt_float_to_real = Q.prove(
   `!y:('t,'w) float.
       ~float_is_zero y ==> ULP (y.Exponent,(:'t)) <= abs (float_to_real y)`,
   rw [ULP_def, float_to_real_def, abs_float_value, abs_significand,
       realTheory.ABS_MUL, realTheory.ABS_DIV, realTheory.ABS_N,
       gt0_abs, realTheory.REAL_LE_LDIV_EQ, float_is_zero, GSYM word_lt0]
   \\ simp [realTheory.POW_ADD, cancel_rwt, cancel_rwts]
   \\ simp [GSYM realTheory.REAL_LDISTRIB, realTheory.POW_2_LE1,
            le_mult, realLib.REAL_ARITH ``1r <= x /\ 0 <= n ==> 1 <= x + n``]
   )

(* |- !y. ~float_is_zero y ==> ulp (:'t # 'w) <= abs (float_to_real y) *)
val ulp_lt_float_to_real =
   diff_float_ULP
   |> Q.SPEC `float_plus_zero (:'t # 'w)`
   |> SIMP_RULE (srw_ss())
         [realTheory.ABS_NEG, float_components, zero_to_real, zero_properties,
          exponent_boundary_def, GSYM ulp_def, GSYM float_is_zero_to_real]

val abs_limits = realLib.REAL_ARITH ``!x l. abs x <= l = ~(x < -l) /\ ~(x > l)``

val abs_limits2 =
   realLib.REAL_ARITH ``!x l. abs x < l = ~(x <= -l) /\ ~(x >= l)``

(* ------------------------------------------------------------------------
   Rounding to regular value
   ------------------------------------------------------------------------ *)

val round_roundTowardZero = Q.store_thm("round_roundTowardZero",
   `!y: ('t, 'w) float x r.
      (float_value y = Float r) /\
      abs (r - x) < ULP (y.Exponent, (:'t)) /\ abs r <= abs x /\
      ulp (:'t # 'w) <= abs x /\ abs x <= largest (:'t # 'w) ==>
      (round roundTowardZero x = y)`,
   lrw [round_def, closest_def, is_closest_def, closest_such_def]
   >- imp_res_tac abs_limits
   >- imp_res_tac abs_limits
   \\ SELECT_ELIM_TAC
   \\ rw []
   >| [
      qexists_tac `y`
      \\ imp_res_tac Float_float_to_real
      \\ rw [Float_is_finite]
      \\ Cases_on `float_to_real b = float_to_real y`
      >- simp []
      \\ Cases_on `exponent_boundary b y`
      >- (`ULP (y.Exponent,(:'t)) <= abs (float_to_real y)`
          by metis_tac [ULP_lt_float_to_real, exponent_boundary_not_float_zero]
          \\ match_mp_tac
               (realLib.REAL_ARITH
                   ``abs (a - x) < abs x /\ abs b < abs a /\ abs a <= abs x ==>
                     abs (a - x) <= abs (b - x)``)
          \\ rsimp [exponent_boundary_lt])
      \\ match_mp_tac
            (realLib.REAL_ARITH
               ``ULP ((y: ('t, 'w) float).Exponent, (:'t)) <= abs (ra - rb) /\
                 abs (ra - x) < ULP (y.Exponent, (:'t)) /\
                 abs ra <= abs x /\ abs rb <= abs x ==>
                 abs (ra - x) <= abs (rb - x)``)
      \\ simp []
      \\ metis_tac [diff_float_ULP],
      (* -- *)
      Cases_on `float_is_zero y`
      >- (
          `r = 0` by (pop_assum mp_tac \\ simp [float_is_zero_def])
          \\ `y.Exponent = 0w`
          by (qpat_assum `float_is_zero y` mp_tac \\ simp [float_is_zero])
          \\ rlfs [ulp_def]
          \\ metis_tac [realLib.REAL_ARITH ``~(x < b /\ b <= x: real)``]
         )
      \\ imp_res_tac Float_float_to_real
      \\ pop_assum (SUBST_ALL_TAC o SYM)
      \\ `abs (float_to_real x' - x) <= abs (float_to_real y - x)`
      by metis_tac [Float_is_finite]
      \\ `abs (x - float_to_real x') < ULP (y.Exponent, (:'t))`
      by metis_tac [realTheory.REAL_LET_TRANS, realTheory.ABS_SUB]
      \\ Cases_on `exponent_boundary x' y`
      >- (
          `ULP (y.Exponent,(:'t)) <= abs (float_to_real y)`
          by metis_tac [ULP_lt_float_to_real, exponent_boundary_not_float_zero]
          \\ `abs (float_to_real y - x) <= abs (float_to_real x' - x)`
          by (match_mp_tac
               (realLib.REAL_ARITH
                   ``abs (a - x) < abs x /\ abs b < abs a /\ abs a <= abs x ==>
                     abs (a - x) <= abs (b - x)``)
              \\ rsimp [exponent_boundary_lt]
             )
          \\ simp [GSYM float_to_real_11_right]
          \\ match_mp_tac
               (realLib.REAL_ARITH
                   ``abs a <= abs x /\ abs b <= abs x /\
                     (abs (a - x) = abs (b - x)) ==> (a = b)``)
          \\ rsimp []
         )
      \\ match_mp_tac diff_lt_ulp_eq0
      \\ qexists_tac `x`
      \\ rsimp []
   ])

(*
val ULP01 = Q.store_thm("ULP01",
   `ULP (0w:'w word, (:'t)) = ULP (1w:'w word, (:'t))`,
   rw [ULP_def]
   )

val ULP_lt_mono = Q.store_thm("ULP_lt_mono",
   `!e1 e2. 1w <+ e2 ==> (ULP (e1, (:'t)) < ULP (e2, (:'t)) = e1 <+ e2)`,
   Cases
   \\ Cases
   \\ lrw [ULP_def, wordsTheory.word_lo_n2w, realTheory.REAL_LT_RDIV]
   \\ simp [realTheory.REAL_OF_NUM_POW]
   )

val exponent_boundary_exp_gt1 = Q.prove(
   `!b y: ('t, 'w) float.
       exponent_boundary b y ==> b.Exponent <+ y.Exponent /\ 1w <+ y.Exponent`,
   rw [exponent_boundary_def, wordsTheory.WORD_LO]
   \\ Cases_on `b.Exponent`
   \\ Cases_on `y.Exponent`
   \\ lfs []
   )
*)

val word_lsb_plus_1 = Q.prove(
   `!a. word_lsb (a + 1w) = ~word_lsb a`,
   Cases
   \\ simp [wordsTheory.word_add_n2w, arithmeticTheory.ODD,
            GSYM arithmeticTheory.ADD1]
   )

val word_lsb_minus_1 = Q.prove(
   `!a. word_lsb (a - 1w) = ~word_lsb a`,
   Cases
   \\ Cases_on `n`
   \\ simp [GSYM wordsTheory.word_add_n2w, arithmeticTheory.ODD,
            arithmeticTheory.ADD1]
   )

val tac =
   qpat_assum `!a. q \/ t` (qspec_then `y` strip_assume_tac)
   \\ fs [realTheory.REAL_NOT_LE]
   \\ qpat_assum `!b. p` (qspec_then `b` imp_res_tac)
   \\ rlfs []
   \\ rfs []

val round_roundTiesToEven = Q.store_thm("round_roundTiesToEven",
   `!y: ('t, 'w) float x r.
      (float_value y = Float r) /\
      ((y.Significand = 0w) /\ y.Exponent <> 1w ==> abs r <= abs x) /\
      2 * abs (r - x) <= ULP (y.Exponent, (:'t)) /\
      ((2 * abs (r - x) = ULP (y.Exponent, (:'t))) ==>
       ~word_lsb (y.Significand)) /\
      ulp (:'t # 'w) < 2 * abs x /\ abs x < threshold (:'t # 'w) ==>
      (round roundTiesToEven x = y)`,
   lrw [round_def, closest_def, is_closest_def, closest_such_def,
        pred_setTheory.SPECIFICATION]
   >- imp_res_tac abs_limits2
   >- imp_res_tac abs_limits2
   \\ SELECT_ELIM_TAC
   \\ rw []
   >| [
      qexists_tac `y`
      \\ imp_res_tac Float_float_to_real
      \\ `float_is_finite y` by simp [Float_is_finite]
      \\ rw []
      >| [
         Cases_on `float_to_real y = float_to_real b`
         >- simp []
         \\ Cases_on `exponent_boundary b y`
         >- (
           `ULP (y.Exponent,(:'t)) <= abs (float_to_real y)`
           by metis_tac [ULP_lt_float_to_real, exponent_boundary_not_float_zero]
           \\ imp_res_tac exponent_boundary_lt
           \\ `2 * abs (float_to_real y - x) <= abs (float_to_real y)`
           by imp_res_tac realTheory.REAL_LE_TRANS
           \\ match_mp_tac
                (realLib.REAL_ARITH
                    ``abs b < abs a /\ abs a <= abs x /\
                      2 * abs (a - x) <= abs a ==> abs (a - x) <= abs (b - x)``)
           \\ rlfs [exponent_boundary_def]
           )
         \\ metis_tac
               [diff_float_ULP,
                realLib.REAL_ARITH
                   ``2 * abs (r - x) <= u /\ u <= abs (r - b) ==>
                     abs (r - x) <= abs (b - x)``],
         (* -- *)
         strip_tac
         \\ fs []
         \\ `a' <> y` by metis_tac []
         \\ Cases_on `float_is_zero y`
         >- fs [float_is_zero]
         \\ `float_to_real y <> float_to_real a'`
         by simp [float_to_real_eq]
         \\ Cases_on `exponent_boundary a' y`
         >- fs [exponent_boundary_def]
         \\ imp_res_tac diff_float_ULP
         \\ `2 * abs (float_to_real y - x) <  ULP (y.Exponent,(:'t))`
         by rsimp []
         \\ metis_tac
              [realLib.REAL_ARITH
                  ``2 * abs (r - x) < u /\ u <= abs (r - a) ==>
                    ~(abs (a - x) <= abs (r - x))``]
      ],
      (* -- *)
      `float_is_finite y` by simp [Float_is_finite]
      \\ Cases_on `float_is_zero y`
      >- (`r = 0` by (pop_assum mp_tac \\ simp [float_is_zero_def])
          \\ `y.Exponent = 0w`
          by (qpat_assum `float_is_zero y` mp_tac \\ simp [float_is_zero])
          \\ rlfs [ulp_def]
          \\ metis_tac [ULP_gt0,
                realLib.REAL_ARITH ``~(0 < x /\ x < b /\ 2 * b <= x: real)``])
      \\ imp_res_tac Float_float_to_real
      \\ pop_assum (SUBST_ALL_TAC o SYM)
      \\ Cases_on `exponent_boundary x' y`
      >- (`abs (float_to_real y) <= abs x` by fs [exponent_boundary_def]
          \\ metis_tac
               [realTheory.REAL_LE_TRANS, exponent_boundary_lt,
                ULP_lt_float_to_real,
                realLib.REAL_ARITH
                  ``~(2 * abs (a - x) <= abs a /\ abs a <= abs x /\
                      abs b < abs a /\ abs (b - x) <= abs (a - x))``])
      \\ Cases_on `2 * abs (float_to_real y - x) < ULP (y.Exponent,(:'t))`
      >- (`2 * abs (float_to_real x' - x) <= 2 * abs (float_to_real y - x)`
          by metis_tac [Float_is_finite,
               realLib.REAL_ARITH ``2 * abs a <= 2 * abs b = abs a <= abs b``]
          \\ metis_tac [realTheory.REAL_LET_TRANS, diff_lt_ulp_even])
      \\ `2 * abs (float_to_real y - x) = ULP (y.Exponent,(:'t))` by rsimp []
      \\ fs []
      \\ Cases_on `float_to_real y = float_to_real x'`
      >- (fs [float_to_real_eq] \\ fs [])
      \\ imp_res_tac diff_float_ULP
      \\ `abs (float_to_real x' - x) <= abs (float_to_real y - x)`
      by metis_tac []
      \\ `abs (float_to_real y - float_to_real x') =
          ULP (y.Exponent,(:'t))`
      by metis_tac
           [realLib.REAL_ARITH
               ``(2 * abs (a - x) = u) /\ u <= abs (a - b) /\
                 abs (b - x) <= abs (a - x) ==> (abs (a - b) = u)``]
      \\ `y.Significand <> -1w` by (strip_tac \\ fs [])
      \\ `~float_is_zero x'`
      by (strip_tac
          \\ imp_res_tac float_is_zero_to_real
          \\ fs [float_min_equiv_ULP_eq_float_to_real]
          \\ fs [float_components])
      \\ Cases_on `y.Significand = 0w`
      >- (qpat_assum `~float_is_zero y` assume_tac
          \\ `x'.Significand <> -1w` by (strip_tac \\ fs [] \\ tac)
          \\ Cases_on `y.Exponent = 1w`
          >- (fs [diff_ulp_next_float01] \\ tac)
          \\ Cases_on `abs (float_to_real x') < abs (float_to_real y)`
          \\ fs [realTheory.REAL_NOT_LT]
          >- metis_tac
               [realTheory.REAL_LE_TRANS, ULP_lt_float_to_real,
                realLib.REAL_ARITH
                  ``~(2 * abs (a - x) <= abs a /\ abs a <= abs x /\
                      abs b < abs a /\ abs (b - x) <= abs (a - x))``]
          \\ `abs (float_to_real x' - x) = abs (float_to_real y - x)`
          by imp_res_tac
               (realLib.REAL_ARITH
                   ``(2 * abs (a - x) = u) /\ abs (b - x) <= abs (a - x) /\
                     (abs (a - b) = u) ==> (abs (b - x) = abs (a - x))``)
         \\ fs [diff_ulp_next_float0]
         \\ tac
         )
      \\ `y.Significand NOTIN {0w; -1w}` by simp []
      \\ fs [diff_ulp_next_float]
      \\ `word_lsb x'.Significand`
      by simp [word_lsb_plus_1, SIMP_RULE (srw_ss()) [] word_lsb_minus_1]
      \\ fs []
      \\ tac
   ])

val not_one_lem = wordsLib.WORD_DECIDE ``(x:'a word) <> 1w ==> w2n x <> 1``
val pow_add1 = REWRITE_RULE [arithmeticTheory.ADD1] realTheory.pow

val exponent_boundary_ULPs = Q.prove(
   `!x y. exponent_boundary x y ==>
          (ULP (y.Exponent, (:'t)) = 2 * ULP (x.Exponent, (:'t)))`,
   srw_tac [] [exponent_boundary_def, ULP_def, pow_add1, realTheory.mult_ratr]
   \\ fs [not_one_lem]
   )

val round_roundTiesToEven0 = Q.store_thm("round_roundTiesToEven0",
   `!y: ('t, 'w) float x r.
      (float_value y = Float r) /\
      ((y.Significand = 0w) /\ y.Exponent <> 1w /\ ~(abs r <= abs x)) /\
      4 * abs (r - x) <= ULP (y.Exponent, (:'t)) /\
      ulp (:'t # 'w) < 2 * abs x /\ abs x < threshold (:'t # 'w) ==>
      (round roundTiesToEven x = y)`,
   lrw [round_def, closest_def, is_closest_def, closest_such_def,
        pred_setTheory.SPECIFICATION]
   >- imp_res_tac abs_limits2
   >- imp_res_tac abs_limits2
   \\ SELECT_ELIM_TAC
   \\ rw []
   >| [
      qexists_tac `y`
      \\ imp_res_tac Float_float_to_real
      \\ `float_is_finite y` by simp [Float_is_finite]
      \\ rw []
      \\ Cases_on `float_to_real y = float_to_real b`
      >- simp []
      \\ Cases_on `exponent_boundary b y`
      >- (
        imp_res_tac diff_exponent_boundary
        \\ `2 * ULP (b.Exponent,(:'t)) = ULP (y.Exponent,(:'t))`
        by (fs [exponent_boundary_def, ULP_def]
            \\ rw [pow_add1, realTheory.mult_ratr]
            \\ fs [not_one_lem])
        \\ match_mp_tac
             (realLib.REAL_ARITH
                ``~(abs a <= abs x) /\ 4 * abs (a - x) <= 2 * abs (a - b) ==>
                  abs (a - x) <= abs (b - x)``)
        \\ simp []
        )
      \\ metis_tac
            [diff_float_ULP,
             realLib.REAL_ARITH ``4 * abs (r - x) <= u /\ u <= abs (r - b) ==>
                                  abs (r - x) <= abs (b - x)``],
      (* -- *)
      `float_is_finite y` by simp [Float_is_finite]
      \\ Cases_on `float_is_zero y`
      >- (`r = 0` by (pop_assum mp_tac \\ simp [float_is_zero_def])
          \\ `y.Exponent = 0w`
          by (qpat_assum `float_is_zero y` mp_tac \\ simp [float_is_zero])
          \\ rlfs [ulp_def])
      \\ imp_res_tac Float_float_to_real
      \\ pop_assum (SUBST_ALL_TAC o SYM)
      \\ `abs (float_to_real x' - x) <= abs (float_to_real y - x)` by res_tac
      \\ `4 * abs (float_to_real x' - x) <= 4 * abs (float_to_real y - x)`
      by rsimp []
      \\ `4 * abs (float_to_real x' - x) <= ULP (y.Exponent,(:'t))`
      by metis_tac [realTheory.REAL_LE_TRANS]
      \\ match_mp_tac diff_lt_ulp_even4
      \\ qexists_tac `x`
      \\ simp []
      \\ spose_not_then assume_tac
      \\ imp_res_tac exponent_boundary_ULPs
      \\ fs [realLib.REAL_ARITH ``4r * a <= 2 * b = 2 * a <= b``]
      \\ imp_res_tac diff_exponent_boundary
      \\ `abs (float_to_real x' - x) = abs (float_to_real y - x)`
      by metis_tac
           [realLib.REAL_ARITH
              ``2 * abs (a - x) <= u /\
                2 * abs (b - x) <= u /\
                (abs (a - b) = u) ==> (abs (a - x) = abs (b - x))``]
      \\ `~word_lsb y.Significand ==> ~word_lsb x'.Significand`
      by metis_tac []
      \\ rfs [exponent_boundary_def]
   ])

(*

val round_roundTowardPositive = Q.store_thm("round_roundTowardPositive",
   `!y: ('t, 'w) float x r.
      (float_value y = Float r) /\
      abs (x - r) < ulp (:'t # 'w) /\ r >= x /\
      ulp (:'t # 'w) <= abs x /\ abs x <= largest (:'t # 'w) ==>
      (round roundTowardPositive x = y)`,
   tac (realLib.REAL_ARITH
          ``ulp (:'t # 'w) <= abs (ra - rb) /\
            abs (x - ra) < ulp (:'t # 'w) /\
            ra >= x /\ rb >= x ==>
            abs (ra - x) <= abs (rb - x)``)
       diff_lt_ulp_eq_pos)

val round_roundTowardNegative = Q.store_thm("round_roundTowardNegative",
   `!y: ('t, 'w) float x r.
      (float_value y = Float r) /\
      abs (x - r) < ulp (:'t # 'w) /\ r <= x /\
      ulp (:'t # 'w) <= abs x /\ abs x <= largest (:'t # 'w) ==>
      (round roundTowardNegative x = y)`,
   tac (realLib.REAL_ARITH
          ``ulp (:'t # 'w) <= abs (ra - rb) /\
            abs (x - ra) < ulp (:'t # 'w) /\
            ra <= x /\ rb <= x ==>
            abs (ra - x) <= abs (rb - x)``)
       diff_lt_ulp_eq_neg)

val tac =
   REPEAT strip_tac
   \\ Cases_on `float_is_zero y`
   >- (
       `r = 0` by (pop_assum mp_tac \\ simp [float_is_zero_def])
       \\ qpat_assum `float_is_zero y` mp_tac
       \\ rw [float_is_zero]
       \\ fs [ulp_def]
       \\ prove_tac [realLib.REAL_ARITH ``~(x < b /\ b <= x: real)``,
                     realLib.REAL_ARITH ``2 * abs (-x) <= u ==> abs x <= u``]
      )
   \\ lrw [float_round_def]
   \\ metis_tac [zero_properties, round_roundTowardZero, round_roundTiesToEven
                 (*, round_roundTowardPositive, round_roundTowardNegative *)]


val float_round_roundTowardZero = Q.store_thm(
   "float_round_roundTowardZero",
   `!b y: ('t, 'w) float x r.
      (float_value y = Float r) /\
      abs (x - r) < ULP (y.Exponent, (:'t)) /\ abs r <= abs x /\
      ulp (:'t # 'w) <= abs x /\ abs x <= largest (:'t # 'w) ==>
      (float_round roundTowardZero b x = y)`,
   tac
   )

val float_round_roundTiesToEven = Q.store_thm("float_round_roundTiesToEven",
   `!b y: ('t, 'w) float x r.
      (float_value y = Float r) /\
      ((y.Significand = 0w) /\ y.Exponent <> 1w ==> abs r <= abs x) /\
      2 * abs (r - x) <= ULP (y.Exponent, (:'t)) /\
      ((2 * abs (r - x) = ULP (y.Exponent, (:'t))) ==>
       ~word_lsb (y.Significand)) /\
      ulp (:'t # 'w) < abs x /\ abs x < threshold (:'t # 'w) ==>
      (float_round roundTiesToEven b x = y)`,
   tac
   )

val float_round_roundTowardPositive = Q.store_thm(
   "float_round_roundTowardPositive",
   `!b y: ('t, 'w) float x r.
      (float_value y = Float r) /\
      abs (x - r) < ulp (:'t # 'w) /\ r >= x /\
      ulp (:'t # 'w) <= abs x /\ abs x <= largest (:'t # 'w) ==>
      (float_round roundTowardPositive b x = y)`,
   tac)

val float_round_roundTowardNegative = Q.store_thm(
   "float_round_roundTowardNegative",
   `!b y: ('t, 'w) float x r.
      (float_value y = Float r) /\
      abs (x - r) < ulp (:'t # 'w) /\ r <= x /\
      ulp (:'t # 'w) <= abs x /\ abs x <= largest (:'t # 'w) ==>
      (float_round roundTowardNegative b x = y)`,
   tac)

*)

(* ------------------------------------------------------------------------
   Rounding to +/- 0
   ------------------------------------------------------------------------ *)

val round_roundTowardZero_is_zero = Q.store_thm("round_roundTowardZero_is_zero",
   `!x. abs x < ulp (:'t # 'w) ==>
        (round roundTowardZero x = float_plus_zero (:'t # 'w)) \/
        (round roundTowardZero x = float_minus_zero (:'t # 'w))`,
   REPEAT strip_tac
   \\ qabbrev_tac `r: ('t, 'w) float = round roundTowardZero x`
   \\ pop_assum (mp_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def])
   \\ simp [round_def, lt_ulp_not_infinity0,
            closest_such_def, closest_def, is_closest_def]
   \\ SELECT_ELIM_TAC
   \\ rw []
   >| [
      qexists_tac `float_plus_zero (:'t # 'w)`
      \\ simp [zero_properties, zero_to_real, realTheory.ABS_POS,
               realTheory.ABS_NEG]
      \\ REPEAT strip_tac
      \\ imp_res_tac realTheory.REAL_LET_TRANS
      \\ imp_res_tac less_than_ulp
      \\ Cases_on `b`
      \\ lfs [float_to_real_def, realTheory.ABS_NEG],
      (* -- *)
      imp_res_tac realTheory.REAL_LET_TRANS
      \\ imp_res_tac less_than_ulp
      \\ Cases_on `r`
      \\ lfs [float_plus_zero_def, float_minus_zero_def, float_negate_def,
              float_component_equality]
      \\ wordsLib.Cases_on_word_value `c`
      \\ simp []
   ])

val float_to_real_min_pos = Q.prove(
   `!r: ('t, 'w) float.
       (abs (float_to_real r) = ulp (:'t # 'w)) =
       r IN {float_plus_min (:'t # 'w);
             float_negate (float_plus_min (:'t # 'w))}`,
   rw [float_plus_min_def, float_negate_def, ulp_def, ULP_def,
       float_to_real_def, float_component_equality, abs_float_value,
       abs_significand, realTheory.ABS_MUL, realTheory.ABS_DIV,
       realTheory.ABS_N, gt0_abs]
   >| [
      wordsLib.Cases_on_word_value `r.Sign`
      \\ Cases_on `r.Significand = 1w`
      \\ simp [realTheory.mult_rat, realTheory.POW_ADD,
               div_twopow
               |> Q.SPEC `m + n`
               |> REWRITE_RULE [realTheory.POW_ADD]
               |> Drule.GEN_ALL]
      \\ Cases_on `r.Significand`
      \\ fs [],
      simp [realTheory.REAL_EQ_RDIV_EQ]
      \\ simp [realTheory.POW_ADD, GSYM realTheory.REAL_LDISTRIB,
               cancel_rwts, cancel_rwt]
      \\ match_mp_tac (realLib.REAL_ARITH ``2r < a * b ==> b * a <> 2``)
      \\ match_mp_tac ge2d
      \\ simp [realTheory.REAL_OF_NUM_POW, pow_ge2, exp_ge2,
               DECIDE ``2n <= a ==> 2 <= b + a``,
               fcpTheory.DIMINDEX_GE_1 ]
   ])

val compare_with_zero_tac =
   qpat_assum `!b. float_is_finite b  ==> p`
      (fn th =>
         assume_tac
            (SIMP_RULE (srw_ss())
               [realTheory.ABS_NEG, zero_to_real, zero_properties]
                  (Q.SPEC `float_plus_zero (:'t # 'w)` th))
         \\ assume_tac th)

val half_ulp = Q.prove(
   `!x r: ('t, 'w) float.
       (2 * abs x = ulp (:'t # 'w)) /\
       (!b: ('t, 'w) float.
            float_is_finite b ==>
            abs (float_to_real r - x) <= abs (float_to_real b - x)) ==>
       float_is_zero r \/
       r IN {float_plus_min (:'t # 'w);
             float_negate (float_plus_min (:'t # 'w))}`,
   REPEAT strip_tac
   \\ Cases_on `float_is_zero r`
   \\ simp []
   \\ compare_with_zero_tac
   \\ `abs (float_to_real r) = ulp (:'t # 'w)`
   by metis_tac
         [ulp_lt_float_to_real,
          realLib.REAL_ARITH
           ``(2 * abs x = u) /\ u <= abs r /\ abs (r - x) <= abs x ==>
             (abs r = u)``]
   \\ fs [float_to_real_min_pos]
   )

val min_pos_odd = Q.prove(
   `!r: ('t, 'w) float.
      r IN {float_plus_min (:'t # 'w);
            float_negate (float_plus_min (:'t # 'w))} ==>
      word_lsb r.Significand`,
   rw [float_plus_min_def, float_negate_def]
   \\ simp []
   )

val round_roundTiesToEven_is_zero = Q.store_thm("round_roundTiesToEven_is_zero",
   `!x. 2 * abs x <= ulp (:'t # 'w) ==>
        (round roundTiesToEven x = float_plus_zero (:'t # 'w)) \/
        (round roundTiesToEven x = float_minus_zero (:'t # 'w))`,
   REPEAT strip_tac
   \\ qabbrev_tac `r: ('t, 'w) float = round roundTiesToEven x`
   \\ pop_assum (mp_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def])
   \\ simp [round_def, lt_ulp_not_infinity1, pred_setTheory.SPECIFICATION,
            closest_such_def, closest_def, is_closest_def]
   \\ SELECT_ELIM_TAC
   \\ rw []
   >| [
      qexists_tac `float_plus_zero (:'t # 'w)`
      \\ simp [zero_properties, zero_to_real, realTheory.ABS_POS,
               realTheory.ABS_NEG]
      \\ rw [float_plus_zero_def]
      \\ Cases_on `float_is_zero b`
      \\ rsimp [float_is_zero_to_real_imp]
      \\ metis_tac
           [ULP_lt_float_to_real, ulp_lt_ULP, realTheory.REAL_LE_TRANS,
            realLib.REAL_ARITH ``2 * abs x <= abs c ==> abs x <= abs (c - x)``],
      (* -- *)
      Cases_on `float_is_zero r`
      >- fs [float_sets]
      \\ Cases_on `2 * abs x < ulp (:'t # 'w)`
      >| [
         imp_res_tac ulp_lt_float_to_real
         \\ compare_with_zero_tac
         \\ metis_tac
               [realLib.REAL_ARITH
                  ``~(2 * abs x < u /\ u <= abs r /\ abs (r - x) <= abs x)``],
         (* -- *)
         imp_res_tac
            (realLib.REAL_ARITH ``a <= b /\ ~(a < b) ==> (a = b: real)``)
         \\ imp_res_tac half_ulp
         \\ imp_res_tac min_pos_odd
         \\ compare_with_zero_tac
         \\ fs []
         \\ qpat_assum `!a. q \/ t`
               (qspec_then `float_plus_zero (:'t # 'w)` strip_assume_tac)
         \\ rfs [realTheory.ABS_NEG, zero_properties, zero_to_real,
                 float_components, GSYM ulp, GSYM neg_ulp]
         \\ qpat_assum `!b. p` (qspec_then `b` imp_res_tac)
         \\ metis_tac
              [realLib.REAL_ARITH
                  ``~((2 * abs x = u) /\ abs (u - x) <= abs x /\
                      ~(abs x <= abs (b - x)) /\ abs (u - x) <= abs (b - x))``,
               realLib.REAL_ARITH
                  ``~((2 * abs x = u) /\ abs (-u - x) <= abs x /\
                      ~(abs x <= abs (b - x)) /\ abs (-u - x) <= abs (b - x))``]
      ]
   ])

val tac =
   lrw [float_round_def]
   \\ metis_tac [round_roundTowardZero_is_zero, round_roundTiesToEven_is_zero,
                 zero_properties]

val round_roundTowardZero_is_minus_zero = Q.store_thm(
   "round_roundTowardZero_is_minus_zero",
   `!x. abs x < ulp (:'t # 'w) ==>
        (float_round roundTowardZero T x = float_minus_zero (:'t # 'w))`,
   tac
   )

val round_roundTowardZero_is_plus_zero = Q.store_thm(
   "round_roundTowardZero_is_plus_zero",
   `!x. abs x < ulp (:'t # 'w) ==>
        (float_round roundTowardZero F x = float_plus_zero (:'t # 'w))`,
   tac
   )

val round_roundTiesToEven_is_minus_zero = Q.store_thm(
   "round_roundTiesToEven_is_minus_zero",
   `!x. 2 * abs x <= ulp (:'t # 'w) ==>
        (float_round roundTiesToEven T x = float_minus_zero (:'t # 'w))`,
   tac
   )

val round_roundTiesToEven_is_plus_zero = Q.store_thm(
   "round_roundTiesToEven_is_plus_zero",
   `!x. 2 * abs x <= ulp (:'t # 'w) ==>
        (float_round roundTiesToEven F x = float_plus_zero (:'t # 'w))`,
   tac
   )

(* ------------------------------------------------------------------------
   Rounding to limits
   ------------------------------------------------------------------------ *)

val largest_is_positive = Q.store_thm("largest_is_positive",
   `0 <= largest (:'t # 'w)`,
   simp [largest_def, realTheory.REAL_LE_MUL, realTheory.REAL_LE_DIV,
         realTheory.REAL_SUB_LE, realTheory.POW_2_LE1,
         realTheory.REAL_INV_1OVER, realTheory.REAL_LE_LDIV_EQ,
         realLib.REAL_ARITH ``1r <= n ==> 1 <= 2 * n``]
   )

val threshold_is_positive = Q.store_thm("threshold_is_positive",
   `0 < threshold (:'t # 'w)`,
   simp [threshold_def, realTheory.REAL_LT_MUL, realTheory.REAL_LT_DIV,
         realTheory.REAL_SUB_LT, realTheory.POW_2_LE1,
         realTheory.REAL_INV_1OVER, realTheory.REAL_LT_LDIV_EQ, realTheory.pow,
         realLib.REAL_ARITH ``1r <= n ==> 1 < 2 * (2 * n)``]
   )

val tac =
   rrw  [round_def]
   \\ rlfs [largest_is_positive,
           realLib.REAL_ARITH ``0 <= l /\ l < x ==> ~(x < -l: real)``]
   \\ metis_tac [threshold_is_positive,
                 realLib.REAL_ARITH ``0r < i /\ x <= -i ==> ~(i <= x)``]

val round_roundTiesToEven_plus_infinity = Q.store_thm(
   "round_roundTiesToEven_plus_infinity",
   `!y: ('t, 'w) float x.
      threshold (:'t # 'w) <= x ==>
      (round roundTiesToEven x = float_plus_infinity (:'t # 'w))`,
   tac
   )

val round_roundTiesToEven_minus_infinity = Q.store_thm(
   "round_roundTiesToEven_minus_infinity",
   `!y: ('t, 'w) float x.
      x <= -threshold (:'t # 'w) ==>
      (round roundTiesToEven x = float_minus_infinity (:'t # 'w))`,
   tac
   )

val round_roundTowardZero_top = Q.store_thm("round_roundTowardZero_top",
   `!y: ('t, 'w) float x.
      largest (:'t # 'w) < x ==>
      (round roundTowardZero x = float_top (:'t # 'w))`,
   tac
   )

val round_roundTowardZero_bottom = Q.store_thm("round_roundTowardZero_bottom",
   `!y: ('t, 'w) float x.
      x < -largest (:'t # 'w) ==>
      (round roundTowardZero x = float_bottom (:'t # 'w))`,
   tac
   )

val round_roundTowardPositive_plus_infinity = Q.store_thm(
   "round_roundTowardPositive_plus_infinity",
   `!y: ('t, 'w) float x.
      largest (:'t # 'w) < x ==>
      (round roundTowardPositive x = float_plus_infinity (:'t # 'w))`,
   tac
   )

val round_roundTowardPositive_bottom = Q.store_thm(
   "round_roundTowardPositive_bottom",
   `!y: ('t, 'w) float x.
      x < -largest (:'t # 'w) ==>
      (round roundTowardPositive x = float_bottom (:'t # 'w))`,
   tac
   )

val round_roundTowardNegative_top = Q.store_thm(
   "round_roundTowardNegative_top",
   `!y: ('t, 'w) float x.
      largest (:'t # 'w) < x ==>
      (round roundTowardNegative x = float_top (:'t # 'w))`,
   tac
   )

val round_roundTowardNegative_minus_infinity = Q.store_thm(
   "round_roundTowardNegative_minus_infinity",
   `!y: ('t, 'w) float x.
      x < -largest (:'t # 'w) ==>
      (round roundTowardNegative x = float_minus_infinity (:'t # 'w))`,
   tac
   )

val tac =
   lrw [float_round_def, round_roundTowardZero_top,
        round_roundTowardZero_bottom, round_roundTowardPositive_plus_infinity,
        round_roundTowardPositive_bottom, round_roundTowardNegative_top,
        round_roundTowardNegative_minus_infinity,
        top_properties, bottom_properties, infinity_properties]

val float_round_roundTowardZero_top = Q.store_thm(
   "float_round_roundTowardZero_top",
   `!b y: ('t, 'w) float x.
      largest (:'t # 'w) < x ==>
      (float_round roundTowardZero b x = float_top (:'t # 'w))`,
   tac
   )

val float_round_roundTowardZero_bottom = Q.store_thm(
   "float_round_roundTowardZero_bottom",
   `!b y: ('t, 'w) float x.
      x < -largest (:'t # 'w) ==>
      (float_round roundTowardZero b x = float_bottom (:'t # 'w))`,
   tac
   )

val float_round_roundTowardPositive_plus_infinity = Q.store_thm(
   "float_round_roundTowardPositive_plus_infinity",
   `!b y: ('t, 'w) float x.
      largest (:'t # 'w) < x ==>
      (float_round roundTowardPositive b x = float_plus_infinity (:'t # 'w))`,
   tac
   )

val float_round_roundTowardPositive_bottom = Q.store_thm(
   "float_round_roundTowardPositive_bottom",
   `!b y: ('t, 'w) float x.
      x < -largest (:'t # 'w) ==>
      (float_round roundTowardPositive b x = float_bottom (:'t # 'w))`,
   tac
   )

val float_round_roundTowardNegative_top = Q.store_thm(
   "float_round_roundTowardNegative_top",
   `!b y: ('t, 'w) float x.
      largest (:'t # 'w) < x ==>
      (float_round roundTowardNegative b x = float_top (:'t # 'w))`,
   tac
   )

val float_round_roundTowardNegative_minus_infinity = Q.store_thm(
   "float_round_roundTowardNegative_minus_infinity",
   `!b y: ('t, 'w) float x.
      x < -largest (:'t # 'w) ==>
      (float_round roundTowardNegative b x = float_minus_infinity (:'t # 'w))`,
   tac
   )

(* ------------------------------------------------------------------------
   Theorem support for evaluation
   ------------------------------------------------------------------------ *)

val float_minus_zero = Q.store_thm("float_minus_zero",
   `float_minus_zero (:'t # 'w) =
       <| Sign := 1w; Exponent := 0w; Significand := 0w |>`,
   simp [float_minus_zero_def, float_plus_zero_def, float_negate_def]
   )

val float_minus_infinity = Q.store_thm("float_minus_infinity",
   `float_minus_infinity (:'t # 'w) =
       <| Sign := 1w; Exponent := UINT_MAXw; Significand := 0w |>`,
   simp [float_minus_infinity_def, float_plus_infinity_def, float_negate_def]
   )

val float_round_non_zero = Q.store_thm("float_round_non_zero",
    `!mode toneg r s e f.
        (round mode r = <| Sign := s; Exponent := e; Significand := f |>) /\
        (e <> 0w \/ f <> 0w) ==>
        (float_round mode toneg r =
         <| Sign := s; Exponent := e; Significand := f |>)`,
    lrw [float_round_def, float_is_zero]
    )

val float_round_plus_infinity = Q.store_thm("float_round_plus_infinity",
    `!mode toneg r.
        (round mode r = float_plus_infinity (:'t # 'w)) ==>
        (float_round mode toneg r = float_plus_infinity (:'t # 'w))`,
    lrw [float_round_def, infinity_properties]
    )

val float_round_minus_infinity = Q.store_thm("float_round_minus_infinity",
    `!mode toneg r.
        (round mode r = float_minus_infinity (:'t # 'w)) ==>
        (float_round mode toneg r = float_minus_infinity (:'t # 'w))`,
    lrw [float_round_def, infinity_properties]
    )

val float_round_top = Q.store_thm("float_round_top",
    `!mode toneg r.
        (round mode r = float_top (:'t # 'w)) ==>
        (float_round mode toneg r = float_top (:'t # 'w))`,
    lrw [float_round_def, top_properties]
    )

val float_round_bottom = Q.store_thm("float_round_bottom",
    `!mode toneg r.
        (round mode r = float_bottom (:'t # 'w)) ==>
        (float_round mode toneg r = float_bottom (:'t # 'w))`,
    lrw [float_round_def, bottom_properties]
    )

fun tac thms =
   rrw ([largest_def, threshold_def, float_to_real_def, wordsTheory.dimword_def,
         GSYM realTheory.REAL_NEG_MINUS1, realTheory.REAL_OF_NUM_POW,
         wordsLib.WORD_DECIDE ``x <> 1w ==> (x = 0w: word1)``] @ thms)

val float_to_real = Q.store_thm("float_to_real",
   `!s e:'w word f:'t word.
      float_to_real <| Sign := s; Exponent := e; Significand := f |> =
         let r = if e = 0w
                    then 2r / &(2 EXP INT_MAX (:'w)) * (&w2n f / &dimword (:'t))
                 else &(2 EXP (w2n e)) / &(2 EXP INT_MAX (:'w)) *
                      (1r + &w2n f / &dimword (:'t))
         in
            if s = 1w then -r else r`,
   tac []
   )

val largest = Q.store_thm("largest",
   `largest (:'t # 'w) =
       &(2 EXP (UINT_MAX (:'w) - 1)) * (2 - 1 / &dimword (:'t)) /
       &(2 EXP INT_MAX (:'w))`,
   tac [realTheory.REAL_INV_1OVER, realTheory.mult_ratl]
   )

val threshold = Q.store_thm("threshold",
   `threshold (:'t # 'w) =
       &(2 EXP (UINT_MAX (:'w) - 1)) * (2 - 1 / &(2 * dimword (:'t))) /
       &(2 EXP INT_MAX (:'w))`,
   tac [realTheory.REAL_INV_1OVER, realTheory.mult_ratl, arithmeticTheory.EXP]
   )

val float_tests = Q.store_thm("float_tests",
   `(!s e f.
       float_is_nan <| Sign := s; Exponent := e; Significand := f |> =
       (e = -1w) /\ (f <> 0w)) /\
    (!s e f.
       float_is_infinite <| Sign := s; Exponent := e; Significand := f |> =
       (e = -1w) /\ (f = 0w)) /\
    (!s e f.
       float_is_normal <| Sign := s; Exponent := e; Significand := f |> =
       (e <> 0w) /\ (e <> -1w)) /\
    (!s e f.
       float_is_subnormal <| Sign := s; Exponent := e; Significand := f |> =
       (e = 0w) /\ (f <> 0w)) /\
    (!s e f.
       float_is_zero <| Sign := s; Exponent := e; Significand := f |> =
       (e = 0w) /\ (f = 0w)) /\
    (!s e f.
       float_is_finite <| Sign := s; Exponent := e; Significand := f |> =
       (e <> -1w))`,
   rw [float_is_nan_def, float_is_infinite_def, float_is_finite_def,
       float_is_normal_def, float_is_subnormal_def, float_value_def]
   \\ rw [float_sets, float_minus_zero_def, float_plus_zero_def,
          float_is_finite_def, float_negate_def]
   \\ wordsLib.Cases_on_word_value `s`
   \\ simp []
   )

val float_infinity_negate_abs = Q.store_thm("float_infinity_negate_abs",
   `(float_negate (float_plus_infinity (:'t # 'w)) =
     float_minus_infinity (:'t # 'w)) /\
    (float_negate (float_minus_infinity (:'t # 'w)) =
     float_plus_infinity (:'t # 'w)) /\
    (float_abs (float_plus_infinity (:'t # 'w)) =
     float_plus_infinity (:'t # 'w)) /\
    (float_abs (float_minus_infinity (:'t # 'w)) =
     float_plus_infinity (:'t # 'w))`,
    rw [float_plus_infinity_def, float_minus_infinity_def,
        float_negate_def, float_abs_def]
    )

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

val float_add_compute = Q.store_thm("float_add_compute",
   `(!mode x.
       float_add mode (float_some_nan (:'t # 'w)) x =
       float_some_nan (:'t # 'w)) /\
    (!mode x.
       float_add mode x (float_some_nan (:'t # 'w)) =
       float_some_nan (:'t # 'w)) /\
    (!mode.
       float_add mode (float_minus_infinity (:'t # 'w))
                      (float_minus_infinity (:'t # 'w)) =
       float_minus_infinity (:'t # 'w)) /\
    (!mode.
       float_add mode (float_minus_infinity (:'t # 'w))
                      (float_plus_infinity (:'t # 'w)) =
       float_some_nan (:'t # 'w)) /\
    (!mode.
       float_add mode (float_plus_infinity (:'t # 'w))
                      (float_plus_infinity (:'t # 'w)) =
       float_plus_infinity (:'t # 'w)) /\
    (!mode.
       float_add mode (float_plus_infinity (:'t # 'w))
                      (float_minus_infinity (:'t # 'w)) =
       float_some_nan (:'t # 'w))
   `,
   simp [float_add_def, float_values, float_components]
   \\ strip_tac
   \\ Cases_on `float_value x`
   \\ simp []
   )

val float_add_nan = Q.store_thm("float_add_nan",
   `!mode x y.
       (float_value x = NaN) \/ (float_value y = NaN) ==>
       (float_add mode x y = float_some_nan (:'t # 'w))`,
   NTAC 3 strip_tac
   \\ Cases_on `float_value x`
   \\ Cases_on `float_value y`
   \\ simp [float_add_def]
   )

val float_add_finite = Q.store_thm("float_add_finite",
   `!mode x y r1 r2.
       (float_value x = Float r1) /\ (float_value y = Float r2) ==>
       (float_add mode x y =
        float_round mode (if (r1 = 0) /\ (r2 = 0) /\ (x.Sign = y.Sign) then
                             x.Sign = 1w
                          else mode = roundTowardNegative) (r1 + r2))`,
   simp [float_add_def]
   )

val float_add_finite_plus_infinity = Q.store_thm(
   "float_add_finite_plus_infinity",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_add mode x (float_plus_infinity (:'t # 'w)) =
        float_plus_infinity (:'t # 'w))`,
   simp [float_add_def, float_values]
   )

val float_add_plus_infinity_finite = Q.store_thm(
   "float_add_plus_infinity_finite",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_add mode (float_plus_infinity (:'t # 'w)) x =
        float_plus_infinity (:'t # 'w))`,
   simp [float_add_def, float_values]
   )

val float_add_finite_minus_infinity = Q.store_thm(
   "float_add_finite_minus_infinity",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_add mode x (float_minus_infinity (:'t # 'w)) =
        float_minus_infinity (:'t # 'w))`,
   simp [float_add_def, float_values]
   )

val float_add_minus_infinity_finite = Q.store_thm(
   "float_add_minus_infinity_finite",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_add mode (float_minus_infinity (:'t # 'w)) x =
        float_minus_infinity (:'t # 'w))`,
   simp [float_add_def, float_values]
   )

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

val float_sub_compute = Q.store_thm("float_sub_compute",
   `(!mode x.
       float_sub mode (float_some_nan (:'t # 'w)) x =
       float_some_nan (:'t # 'w)) /\
    (!mode x.
       float_sub mode x (float_some_nan (:'t # 'w)) =
       float_some_nan (:'t # 'w)) /\
    (!mode.
       float_sub mode (float_minus_infinity (:'t # 'w))
                      (float_minus_infinity (:'t # 'w)) =
       float_some_nan (:'t # 'w)) /\
    (!mode.
       float_sub mode (float_minus_infinity (:'t # 'w))
                      (float_plus_infinity (:'t # 'w)) =
       float_minus_infinity (:'t # 'w)) /\
    (!mode.
       float_sub mode (float_plus_infinity (:'t # 'w))
                      (float_plus_infinity (:'t # 'w)) =
       float_some_nan (:'t # 'w)) /\
    (!mode.
       float_sub mode (float_plus_infinity (:'t # 'w))
                      (float_minus_infinity (:'t # 'w)) =
       float_plus_infinity (:'t # 'w))
   `,
   simp [float_sub_def, float_values, float_components]
   \\ strip_tac
   \\ Cases_on `float_value x`
   \\ simp []
   )

val float_sub_nan = Q.store_thm("float_sub_nan",
   `!mode x y.
       (float_value x = NaN) \/ (float_value y = NaN) ==>
       (float_sub mode x y = float_some_nan (:'t # 'w))`,
   NTAC 3 strip_tac
   \\ Cases_on `float_value x`
   \\ Cases_on `float_value y`
   \\ simp [float_sub_def]
   )

val float_sub_finite = Q.store_thm("float_sub_finite",
   `!mode x y r1 r2.
       (float_value x = Float r1) /\ (float_value y = Float r2) ==>
       (float_sub mode x y =
        float_round mode (if (r1 = 0) /\ (r2 = 0) /\ x.Sign <> y.Sign then
                             x.Sign = 1w
                          else mode = roundTowardNegative) (r1 - r2))`,
   simp [float_sub_def]
   )

val float_sub_finite_plus_infinity = Q.store_thm(
   "float_sub_finite_plus_infinity",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_sub mode x (float_plus_infinity (:'t # 'w)) =
        float_minus_infinity (:'t # 'w))`,
   simp [float_sub_def, float_values, float_minus_infinity_def]
   )

val float_sub_plus_infinity_finite = Q.store_thm(
   "float_sub_plus_infinity_finite",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_sub mode (float_plus_infinity (:'t # 'w)) x =
        float_plus_infinity (:'t # 'w))`,
   simp [float_sub_def, float_values]
   )

val float_sub_finite_minus_infinity = Q.store_thm(
   "float_sub_finite_minus_infinity",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_sub mode x (float_minus_infinity (:'t # 'w)) =
        float_plus_infinity (:'t # 'w))`,
   simp [float_sub_def, float_values, float_negate_negate,
         float_minus_infinity_def]
   )

val float_sub_minus_infinity_finite = Q.store_thm(
   "float_sub_minus_infinity_finite",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_sub mode (float_minus_infinity (:'t # 'w)) x =
        float_minus_infinity (:'t # 'w))`,
   simp [float_sub_def, float_values]
   )

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

val float_mul_compute = Q.store_thm("float_mul_compute",
   `(!mode x.
       float_mul mode (float_some_nan (:'t # 'w)) x =
       float_some_nan (:'t # 'w)) /\
    (!mode x.
       float_mul mode x (float_some_nan (:'t # 'w)) =
       float_some_nan (:'t # 'w)) /\
    (!mode.
       float_mul mode (float_minus_infinity (:'t # 'w))
                      (float_minus_infinity (:'t # 'w)) =
       float_plus_infinity (:'t # 'w)) /\
    (!mode.
       float_mul mode (float_minus_infinity (:'t # 'w))
                      (float_plus_infinity (:'t # 'w)) =
       float_minus_infinity (:'t # 'w)) /\
    (!mode.
       float_mul mode (float_plus_infinity (:'t # 'w))
                      (float_plus_infinity (:'t # 'w)) =
       float_plus_infinity (:'t # 'w)) /\
    (!mode.
       float_mul mode (float_plus_infinity (:'t # 'w))
                      (float_minus_infinity (:'t # 'w)) =
       float_minus_infinity (:'t # 'w))
   `,
   simp [float_mul_def, float_values, float_components]
   \\ strip_tac
   \\ Cases_on `float_value x`
   \\ simp []
   )

val float_mul_nan = Q.store_thm("float_mul_nan",
   `!mode x y.
       (float_value x = NaN) \/ (float_value y = NaN) ==>
       (float_mul mode x y = float_some_nan (:'t # 'w))`,
   NTAC 3 strip_tac
   \\ Cases_on `float_value x`
   \\ Cases_on `float_value y`
   \\ simp [float_mul_def]
   )

val float_mul_finite = Q.store_thm("float_mul_finite",
   `!mode x y r1 r2.
       (float_value x = Float r1) /\ (float_value y = Float r2) ==>
       (float_mul mode x y =
        float_round mode (x.Sign <> y.Sign) (r1 * r2))`,
   simp [float_mul_def]
   )

val float_mul_finite_plus_infinity = Q.store_thm(
   "float_mul_finite_plus_infinity",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_mul mode x (float_plus_infinity (:'t # 'w)) =
        if r = 0
           then float_some_nan (:'t # 'w)
        else if x.Sign = 0w
           then float_plus_infinity (:'t # 'w)
        else float_minus_infinity (:'t # 'w))`,
   rw [float_mul_def, float_values]
   \\ fs [float_plus_infinity_def]
   )

val float_mul_plus_infinity_finite = Q.store_thm(
   "float_mul_plus_infinity_finite",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_mul mode (float_plus_infinity (:'t # 'w)) x =
        if r = 0
           then float_some_nan (:'t # 'w)
        else if x.Sign = 0w
           then float_plus_infinity (:'t # 'w)
        else float_minus_infinity (:'t # 'w))`,
   rw [float_mul_def, float_values]
   \\ fs [float_plus_infinity_def]
   )

val float_mul_finite_minus_infinity = Q.store_thm(
   "float_mul_finite_minus_infinity",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_mul mode x (float_minus_infinity (:'t # 'w)) =
        if r = 0
           then float_some_nan (:'t # 'w)
        else if x.Sign = 0w
           then float_minus_infinity (:'t # 'w)
        else float_plus_infinity (:'t # 'w))`,
   rw [float_mul_def, float_values]
   \\ fs [float_minus_infinity_def, float_plus_infinity_def, float_negate_def]
   \\ metis_tac [sign_inconsistent]
   )

val float_mul_minus_infinity_finite = Q.store_thm(
   "float_mul_minus_infinity_finite",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_mul mode (float_minus_infinity (:'t # 'w)) x =
        if r = 0
           then float_some_nan (:'t # 'w)
        else if x.Sign = 0w
           then float_minus_infinity (:'t # 'w)
        else float_plus_infinity (:'t # 'w))`,
   rw [float_mul_def, float_values]
   \\ fs [float_minus_infinity_def, float_plus_infinity_def, float_negate_def]
   \\ metis_tac [sign_inconsistent]
   )

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

val float_div_compute = Q.store_thm("float_div_compute",
   `(!mode x.
       float_div mode (float_some_nan (:'t # 'w)) x =
       float_some_nan (:'t # 'w)) /\
    (!mode x.
       float_div mode x (float_some_nan (:'t # 'w)) =
       float_some_nan (:'t # 'w)) /\
    (!mode.
       float_div mode (float_minus_infinity (:'t # 'w))
                      (float_minus_infinity (:'t # 'w)) =
       float_some_nan (:'t # 'w)) /\
    (!mode.
       float_div mode (float_minus_infinity (:'t # 'w))
                      (float_plus_infinity (:'t # 'w)) =
       float_some_nan (:'t # 'w)) /\
    (!mode.
       float_div mode (float_plus_infinity (:'t # 'w))
                      (float_plus_infinity (:'t # 'w)) =
       float_some_nan (:'t # 'w)) /\
    (!mode.
       float_div mode (float_plus_infinity (:'t # 'w))
                      (float_minus_infinity (:'t # 'w)) =
       float_some_nan (:'t # 'w))
   `,
   simp [float_div_def, float_values, float_components]
   \\ strip_tac
   \\ Cases_on `float_value x`
   \\ simp []
   )

val float_div_nan = Q.store_thm("float_div_nan",
   `!mode x y.
       (float_value x = NaN) \/ (float_value y = NaN) ==>
       (float_div mode x y = float_some_nan (:'t # 'w))`,
   NTAC 3 strip_tac
   \\ Cases_on `float_value x`
   \\ Cases_on `float_value y`
   \\ simp [float_div_def]
   )

val float_div_finite = Q.store_thm("float_div_finite",
   `!mode x y r1 r2.
       (float_value x = Float r1) /\ (float_value y = Float r2) ==>
       (float_div mode x y =
        if r2 = 0
           then if r1 = 0
                   then float_some_nan (:'t # 'w)
                else if x.Sign = y.Sign
                   then float_plus_infinity (:'t # 'w)
                else float_minus_infinity (:'t # 'w)
        else float_round mode (x.Sign <> y.Sign) (r1 / r2))`,
   simp [float_div_def]
   )

val float_div_finite_plus_infinity = Q.store_thm(
   "float_div_finite_plus_infinity",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_div mode x (float_plus_infinity (:'t # 'w)) =
        if x.Sign = 0w
           then float_plus_zero (:'t # 'w)
        else float_minus_zero (:'t # 'w))`,
   rw [float_div_def, float_values]
   \\ fs [float_plus_infinity_def]
   )

val float_div_plus_infinity_finite = Q.store_thm(
   "float_div_plus_infinity_finite",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_div mode (float_plus_infinity (:'t # 'w)) x =
        if x.Sign = 0w
           then float_plus_infinity (:'t # 'w)
        else float_minus_infinity (:'t # 'w))`,
   rw [float_div_def, float_values]
   \\ fs [float_plus_infinity_def]
   )

val float_div_finite_minus_infinity = Q.store_thm(
   "float_div_finite_minus_infinity",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_div mode x (float_minus_infinity (:'t # 'w)) =
        if x.Sign = 0w
           then float_minus_zero (:'t # 'w)
        else float_plus_zero (:'t # 'w))`,
   rw [float_div_def, float_values]
   \\ fs [float_minus_infinity_def, float_plus_infinity_def, float_negate_def]
   \\ metis_tac [sign_inconsistent]
   )

val float_div_minus_infinity_finite = Q.store_thm(
   "float_div_minus_infinity_finite",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_div mode (float_minus_infinity (:'t # 'w)) x =
        if x.Sign = 0w
           then float_minus_infinity (:'t # 'w)
        else float_plus_infinity (:'t # 'w))`,
   rw [float_div_def, float_values]
   \\ fs [float_minus_infinity_def, float_plus_infinity_def, float_negate_def]
   \\ metis_tac [sign_inconsistent]
   )

(* ------------------------------------------------------------------------ *)

val () = export_theory ()
