(* ------------------------------------------------------------------------
   Theory of IEEE-754 (base 2) floating-point (basic) arithmetic
   ------------------------------------------------------------------------ *)

open HolKernel boolLib bossLib
open realTheory intrealTheory wordsLib realLib

open pred_setTheory set_relationTheory

val () = new_theory "binary_ieee"
val _ = diminish_srw_ss ["RMULCANON","RMULRELNORM","NORMEQ"]

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

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

val Define = bossLib.zDefine

Overload tc[local] = “transitive_closure”

(* ------------------------------------------------------------------------
   Binary floating point representation
   ------------------------------------------------------------------------ *)

val () = Datatype`
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

Theorem FINITE_floatsets[simp]:
  !s : ('a,'b) float set. FINITE s
Proof
  gen_tac >>
  irule SUBSET_FINITE_I >>
  irule_at Any SUBSET_UNIV >>
  qabbrev_tac ‘f = λa:('a,'b)float. (a.Sign, a.Significand, a.Exponent)’ >>
  ‘!a1 a2. (f a1 = f a2) <=> (a1 = a2)’
    by (simp[Abbr‘f’, theorem "float_component_equality"] >> metis_tac[]) >>
  drule INJECTIVE_IMAGE_FINITE >>
  disch_then (fn th => REWRITE_TAC [GSYM th]) >>
  ‘IMAGE f UNIV = UNIV’
    suffices_by (disch_then SUBST_ALL_TAC >> simp[]) >>
  simp[EXTENSION, Abbr‘f’, pairTheory.FORALL_PROD] >>
  qx_genl_tac[‘sn’, ‘m’, ‘e’] >>
  qexists_tac ‘<| Sign := sn; Significand := m; Exponent := e|>’ >>
  simp[]
QED

(* ------------------------------------------------------------------------
   Tests
   ------------------------------------------------------------------------ *)

val float_is_nan_def = Define`
   float_is_nan (x: ('t, 'w) float) =
      case float_value x of
         NaN => T
       | _ => F`

val float_is_signalling_def = Define`
   float_is_signalling (x: ('t, 'w) float) <=>
      float_is_nan x /\ ~word_msb x.Significand`

val float_is_infinite_def = Define`
   float_is_infinite (x: ('t, 'w) float) =
      case float_value x of
         Infinity => T
       | _ => F`

val float_is_normal_def = Define`
   float_is_normal (x: ('t, 'w) float) <=>
      x.Exponent <> 0w /\ x.Exponent <> UINT_MAXw`

val float_is_subnormal_def = Define`
   float_is_subnormal (x: ('t, 'w) float) <=>
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

val is_integral_def = Define `is_integral r = ?n. abs r = &(n:num)`

val float_is_integral_def = Define`
   float_is_integral (x: ('t, 'w) float) =
      case float_value x of
         Float r => is_integral r
       | _ => F`

(* ------------------------------------------------------------------------
   Abs and Negate
   (On some architectures the signalling behaviour changes from IEEE754:1985
    and IEEE754:2008)
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

Overload POS0 = “float_plus_zero(:'a#'b)”
Overload NEG0 = “float_minus_zero(:'a#'b)”

(* ------------------------------------------------------------------------
   Rounding reals to floating-point values
   ------------------------------------------------------------------------ *)

val () = Datatype`
   flags = <| DivideByZero : bool
            ; InvalidOp : bool
            ; Overflow : bool
            ; Precision : bool
            ; Underflow_BeforeRounding : bool
            ; Underflow_AfterRounding : bool
            |>`

val clear_flags_def = Define`
  clear_flags = <| DivideByZero := F
                 ; InvalidOp := F
                 ; Overflow := F
                 ; Precision := F
                 ; Underflow_BeforeRounding := F
                 ; Underflow_AfterRounding := F
                 |>`

val invalidop_flags_def = Define`
  invalidop_flags = clear_flags with InvalidOp := T`

val dividezero_flags_def = Define`
  dividezero_flags = clear_flags with DivideByZero := T`

val () = Datatype`
   rounding = roundTiesToEven
            | roundTowardPositive
            | roundTowardNegative
            | roundTowardZero`

Definition is_closest_def:
   is_closest s x a <=>
      a IN s /\
      !b. b IN s ==> abs (float_to_real a - x) <= abs (float_to_real b - x)
End

Theorem is_closest_exists:
  s <> {} ==> ?a. is_closest s r a
Proof
  simp[is_closest_def] >> rw[] >>
  qabbrev_tac ‘dists = { d | ?b. b IN s /\ (d = abs (float_to_real b - r)) }’ >>
  ‘FINITE dists’
    by (‘?f. dists = IMAGE f s’ suffices_by
          (rw[] >> irule IMAGE_FINITE >>
           irule SUBSET_FINITE_I >> qexists_tac ‘UNIV’ >>
           simp[]) >>
        qexists_tac ‘λfl. abs (float_to_real fl - r)’ >>
        simp[Abbr‘dists’, EXTENSION] >> metis_tac[]) >>
  ‘dists <> {}’ by simp[Abbr‘dists’, EXTENSION, MEMBER_NOT_EMPTY] >>
  ‘?d. d IN minimal_elements dists (UNCURRY $<)’
    by (irule finite_acyclic_has_minimal >>
        simp[acyclic_def] >>
        ‘tc (UNCURRY ($< : real -> real -> bool)) = UNCURRY $<’
          suffices_by simp[IN_DEF] >>
        irule transitive_tc >>
        simp[transitive_def, SF realSimps.REAL_ARITH_ss]) >>
  pop_assum mp_tac >> simp[minimal_elements_def, Abbr‘dists’] >>
  strip_tac >> rename [‘minfl IN s’, ‘d = abs (float_to_real minfl - r)’] >>
  qexists_tac ‘minfl’ >> rw[] >>
  metis_tac[REAL_NOT_LT, REAL_LT_REFL]
QED

Theorem zeroes_are_finite_floats[simp]:
  float_is_finite (float_plus_zero (:'w # 't)) /\
  float_is_finite (float_minus_zero (:'w # 't))
Proof
  simp[float_is_finite_def, float_plus_zero_def, float_minus_zero_def,
       float_value_def, float_negate_def]
QED

Theorem float_to_real_zeroes[simp]:
  (float_to_real (float_plus_zero (:'w # 't)) = 0) /\
  (float_to_real (float_minus_zero (:'w # 't)) = 0)
Proof
  simp[float_to_real_def, float_plus_zero_def, float_negate_def,
       float_minus_zero_def]
QED

Theorem float_to_real_EQ0:
  (float_to_real (f : ('w,'t) float) = 0) <=>
  (f = float_plus_zero (:'w # 't)) \/ (f = float_minus_zero (:'w # 't))
Proof
  simp[EQ_IMP_THM, DISJ_IMP_THM] >>
  simp[float_to_real_def, AllCaseEqs(), REAL_DIV_ZERO] >> strip_tac
  >- (simp[theorem "float_component_equality", float_plus_zero_def,
           float_minus_zero_def, float_negate_def] >>
      Cases_on ‘f.Sign’ using wordsTheory.ranged_word_nchotomy >>
      gs[wordsTheory.word_eq_n2w, bitTheory.MOD_2EXP_MAX_def,
         bitTheory.MOD_2EXP_def, bitTheory.MOD_2EXP_EQ_def]) >>
  gs[REAL_ARITH “(1r + x = 0) <=> (x = -1)”,
     SF realSimps.RMULRELNORM_ss, real_div] >>
  Cases_on ‘f.Significand’ using wordsTheory.ranged_word_nchotomy >>
  gs[REAL_OF_NUM_POW]
QED

Theorem is_closestP_finite_float_exists:
  ?a : ('w,'t) float. is_closest float_is_finite r a /\
                      !b. is_closest float_is_finite r b /\ P b ==> P a
Proof
  qabbrev_tac ‘cands = { a : ('w,'t) float | is_closest float_is_finite r a}’ >>
  qabbrev_tac ‘candsP = { a | a IN cands /\ P a }’ >>
  ‘cands <> {}’
    by (simp[Abbr‘cands’, EXTENSION] >>
        irule is_closest_exists >> simp[EXTENSION, IN_DEF] >>
        irule_at Any (cj 1 zeroes_are_finite_floats)) >>
  gs[GSYM MEMBER_NOT_EMPTY] >>
  rename [‘c IN cands’] >>
  Cases_on ‘candsP = {}’
  >- (qexists_tac ‘c’ >> fs[Abbr‘cands’, Abbr‘candsP’] >>
      fs[EXTENSION] >> metis_tac[]) >>
  gs[GSYM MEMBER_NOT_EMPTY] >>
  rename1 ‘cp IN candsP’ >> qexists_tac ‘cp’ >>
  fs[Abbr‘cands’, Abbr‘candsP’]
QED

Theorem is_closest_float_is_finite_0:
  is_closest float_is_finite 0 (f:('w,'t)float) <=>
  (f = float_plus_zero (:'w#'t)) \/ (f = float_minus_zero(:'w#'t))
Proof
  eq_tac >> simp[is_closest_def, IN_DEF, DISJ_IMP_THM] >> rw[] >>
  first_x_assum $ qspec_then ‘float_plus_zero (:'w # 't)’ mp_tac>>
  simp[REAL_ABS_LE0, float_to_real_EQ0]
QED

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

Theorem ULP_positive[simp]:
  0 < ULP (e, i) /\ 0 <= ULP (e, i) /\ ~(ULP (e,i) < 0) /\ ~(ULP (e,i) <= 0)
Proof
  csimp[REAL_LE_LT, REAL_NOT_LE, REAL_NOT_LT] >>
  Cases_on ‘i’ >>
  simp[ULP_def, REAL_LT_RDIV_0, REAL_OF_NUM_POW]
QED

Theorem ULP_nonzero[simp]:
  ULP (e : 'w word, (:'t)) <> 0
Proof
  metis_tac[ULP_positive, REAL_LT_REFL]
QED

Theorem ulp_positive[simp]:
  0 < ulp(:'t # 'w) /\ 0 <= ulp(:'t # 'w) /\ ~(ulp(:'t#'w) < 0) /\
  ~(ulp(:'t # 'w) <= 0)
Proof
  simp[ulp_def]
QED

Theorem ulp_nonzero[simp]:
  ulp (:'t # 'w) <> 0
Proof
  simp[ulp_def]
QED


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
   NaNs
   ------------------------------------------------------------------------ *)

val () = Datatype`
   fp_op =
     FP_Sqrt rounding (('t, 'w) float)
   | FP_Add rounding (('t, 'w) float) (('t, 'w) float)
   | FP_Sub rounding (('t, 'w) float) (('t, 'w) float)
   | FP_Mul rounding (('t, 'w) float) (('t, 'w) float)
   | FP_Div rounding (('t, 'w) float) (('t, 'w) float)
   | FP_MulAdd rounding (('t, 'w) float) (('t, 'w) float) (('t, 'w) float)
   | FP_MulSub rounding (('t, 'w) float) (('t, 'w) float) (('t, 'w) float)`

val float_some_qnan_def = Define`
   float_some_qnan (fp_op : ('t, 'w) fp_op) =
   (@f. let qnan = f fp_op in float_is_nan qnan /\ ~float_is_signalling qnan)
     fp_op : ('t, 'w) float`

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

val float_round_with_flags_def = Define`
  float_round_with_flags mode to_neg r =
  let x = float_round mode to_neg r : ('t, 'w) float and a = abs r in
  let inexact = (float_value x <> Float r) in
    ((clear_flags with
        <| Overflow := (float_is_infinite x \/ 2 pow (INT_MIN (:'w)) <= a)
         (* IEEE-754 permits a number of ways to detect underflow. Below
            are two possible methods. *)
         ; Underflow_BeforeRounding := (inexact /\ a < 2 / 2 pow (bias(:'w)))
         ; Underflow_AfterRounding :=
             (inexact /\
              ((float_round mode to_neg r : ('t, 'w + 1) float).Exponent <=+
               n2w (INT_MIN (:'w))))
         ; Precision := inexact
         |>), x)`

val check_for_signalling_def = Define`
  check_for_signalling l =
  clear_flags with InvalidOp := EXISTS float_is_signalling l`

val real_to_float_def = Define`
   real_to_float m = float_round m (m = roundTowardNegative)`

val real_to_float_with_flags_def = Define`
   real_to_float_with_flags m =
   float_round_with_flags m (m = roundTowardNegative)`

val float_round_to_integral_def = Define`
   float_round_to_integral mode (x: ('t, 'w) float) =
      case float_value x of
         Float r => integral_round mode r
       | _ => x`

val float_to_int_def = Define`
   float_to_int mode (x: ('t, 'w) float) =
   case float_value x of
      Float r =>
       SOME (case mode of
                roundTiesToEven =>
                  let f = INT_FLOOR r in
                  let df = abs (r - real_of_int f) in
                  if (df < 1r / 2) \/ (df = 1r / 2) /\ EVEN (Num (ABS f)) then
                    f
                  else
                    INT_CEILING r
              | roundTowardPositive => INT_CEILING r
              | roundTowardNegative => INT_FLOOR r
              | roundTowardZero =>
                  if x.Sign = 1w then INT_CEILING r else INT_FLOOR r)
    | _ => NONE`

Definition float_sqrt_def:
   float_sqrt mode (x: ('t, 'w) float) =
      if x.Sign = 0w then
         case float_value x of
            NaN => (check_for_signalling [x], float_some_qnan (FP_Sqrt mode x))
          | Infinity => (clear_flags, float_plus_infinity (:'t # 'w))
          | Float r => (float_round_with_flags mode F (sqrt r))
      else if x = float_minus_zero (:'t # 'w) then
        (clear_flags, float_minus_zero (:'t # 'w))
      else
        (invalidop_flags, float_some_qnan (FP_Sqrt mode x))
End

val float_add_def = Define`
   float_add mode (x: ('t, 'w) float) (y: ('t, 'w) float) =
      case float_value x, float_value y of
         NaN, _ => (check_for_signalling [x; y],
                    float_some_qnan (FP_Add mode x y))
       | _, NaN => (check_for_signalling [y],
                    float_some_qnan (FP_Add mode x y))
       | Infinity, Infinity =>
            if x.Sign = y.Sign then
               (clear_flags, x)
            else
               (invalidop_flags, float_some_qnan (FP_Add mode x y))
       | Infinity, _ => (clear_flags, x)
       | _, Infinity => (clear_flags, y)
       | Float r1, Float r2 =>
            float_round_with_flags mode
               (if (r1 = 0) /\ (r2 = 0) /\ (x.Sign = y.Sign) then
                  x.Sign = 1w
                else mode = roundTowardNegative) (r1 + r2)`

val float_sub_def = Define`
   float_sub mode (x: ('t, 'w) float) (y: ('t, 'w) float) =
      case float_value x, float_value y of
         NaN, _ => (check_for_signalling [x; y],
                    float_some_qnan (FP_Sub mode x y))
       | _, NaN => (check_for_signalling [y],
                    float_some_qnan (FP_Sub mode x y))
       | Infinity, Infinity =>
            if x.Sign = y.Sign then
               (invalidop_flags, float_some_qnan (FP_Sub mode x y))
            else
               (clear_flags, x)
       | Infinity, _ => (clear_flags, x)
       | _, Infinity => (clear_flags, float_negate y)
       | Float r1, Float r2 =>
            float_round_with_flags mode
               (if (r1 = 0) /\ (r2 = 0) /\ x.Sign <> y.Sign then
                  x.Sign = 1w
                else mode = roundTowardNegative) (r1 - r2)`

val float_mul_def = Define`
   float_mul mode (x: ('t, 'w) float) (y: ('t, 'w) float) =
      case float_value x, float_value y of
         NaN, _ => (check_for_signalling [x; y],
                    float_some_qnan (FP_Mul mode x y))
       | _, NaN => (check_for_signalling [y],
                    float_some_qnan (FP_Mul mode x y))
       | Infinity, Float r =>
            if r = 0 then
               (invalidop_flags, float_some_qnan (FP_Mul mode x y))
            else
               (clear_flags,
                if x.Sign = y.Sign then
                   float_plus_infinity (:'t # 'w)
                else float_minus_infinity (:'t # 'w))
       | Float r, Infinity =>
            if r = 0 then
               (invalidop_flags, float_some_qnan (FP_Mul mode x y))
            else
               (clear_flags,
                if x.Sign = y.Sign then
                   float_plus_infinity (:'t # 'w)
                else float_minus_infinity (:'t # 'w))
       | Infinity, Infinity =>
            (clear_flags,
             if x.Sign = y.Sign then
                float_plus_infinity (:'t # 'w)
             else float_minus_infinity (:'t # 'w))
       | Float r1, Float r2 =>
            float_round_with_flags mode (x.Sign <> y.Sign) (r1 * r2)`

val float_div_def = Define`
   float_div mode (x: ('t, 'w) float) (y: ('t, 'w) float) =
      case float_value x, float_value y of
         NaN, _ => (check_for_signalling [x; y],
                    float_some_qnan (FP_Div mode x y))
       | _, NaN => (check_for_signalling [y],
                    float_some_qnan (FP_Div mode x y))
       | Infinity, Infinity =>
            (invalidop_flags, float_some_qnan (FP_Div mode x y))
       | Infinity, _ =>
            (clear_flags,
             if x.Sign = y.Sign then
                float_plus_infinity (:'t # 'w)
             else float_minus_infinity (:'t # 'w))
       | _, Infinity =>
            (clear_flags,
             if x.Sign = y.Sign then
                float_plus_zero (:'t # 'w)
             else float_minus_zero (:'t # 'w))
       | Float r1, Float r2 =>
            if r2 = 0
               then if r1 = 0 then
                       (invalidop_flags, float_some_qnan (FP_Div mode x y))
                    else
                       (dividezero_flags,
                        if x.Sign = y.Sign then
                           float_plus_infinity (:'t # 'w)
                        else float_minus_infinity (:'t # 'w))
            else float_round_with_flags mode (x.Sign <> y.Sign) (r1 / r2)`

val float_mul_add_def = Define`
   float_mul_add mode
      (x: ('t, 'w) float) (y: ('t, 'w) float) (z: ('t, 'w) float) =
      let signP = x.Sign ?? y.Sign in
      let infP = (float_is_infinite x \/ float_is_infinite y)
      in
         if float_is_nan x \/ float_is_nan y \/ float_is_nan z then
            (check_for_signalling [x; y; z],
             float_some_qnan (FP_MulAdd mode x y z))
         else if float_is_infinite x /\ float_is_zero y \/
                 float_is_zero x /\ float_is_infinite y \/
                 float_is_infinite z /\ infP /\ signP <> z.Sign then
            (invalidop_flags, float_some_qnan (FP_MulAdd mode x y z))
         else if float_is_infinite z /\ (z.Sign = 0w) \/ infP /\ (signP = 0w)
            then (clear_flags, float_plus_infinity (:'t # 'w))
         else if float_is_infinite z /\ (z.Sign = 1w) \/ infP /\ (signP = 1w)
            then (clear_flags, float_minus_infinity (:'t # 'w))
         else
           let r1 = float_to_real x * float_to_real y ;
               r2 = float_to_real z ;
               r = r1 + r2 ;
           in
             float_round_with_flags
               mode
               ((r = 0) /\
                (if (r1 = 0) /\ (r2 = 0) /\ (signP = z.Sign) then
                   signP = 1w
                 else mode = roundTowardNegative) \/
                r < 0)
               r
`

val float_mul_sub_def = Define`
   float_mul_sub mode
      (x: ('t, 'w) float) (y: ('t, 'w) float) (z: ('t, 'w) float) =
      let signP = x.Sign ?? y.Sign in
      let infP = (float_is_infinite x \/ float_is_infinite y)
      in
         if float_is_nan x \/ float_is_nan y \/ float_is_nan z then
            (check_for_signalling [x; y; z],
             float_some_qnan (FP_MulSub mode x y z))
         else if float_is_infinite x /\ float_is_zero y \/
                 float_is_zero x /\ float_is_infinite y \/
                 float_is_infinite z /\ infP /\ (signP = z.Sign) then
            (invalidop_flags, float_some_qnan (FP_MulAdd mode x y z))
         else if float_is_infinite z /\ (z.Sign = 1w) \/ infP /\ (signP = 0w)
            then (clear_flags, float_plus_infinity (:'t # 'w))
         else if float_is_infinite z /\ (z.Sign = 0w) \/ infP /\ (signP = 1w)
            then (clear_flags, float_minus_infinity (:'t # 'w))
         else
            let r1 = float_to_real x * float_to_real y
            and r2 = float_to_real z
            in
              float_round_with_flags mode
                (if (r1 = 0) /\ (r2 = 0) /\ signP <> z.Sign then
                   signP = 1w
                 else mode = roundTowardNegative) (r1 - r2)`

(* ------------------------------------------------------------------------
   Some comparison operations
   ------------------------------------------------------------------------ *)

val () = Datatype `float_compare = LT | EQ | GT | UN`

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

val float_unordered_def = Define`
   float_unordered (x: ('t, 'w) float) y =
      (float_compare x y = UN)`

val exponent_boundary_def = Define`
   exponent_boundary (y: ('t, 'w) float) (x: ('t, 'w) float) <=>
      (x.Sign = y.Sign) /\ (w2n x.Exponent = w2n y.Exponent + 1) /\
      (x.Exponent <> 1w) /\ (y.Significand = -1w) /\ (x.Significand = 0w)`

(* ------------------------------------------------------------------------
   Some arithmetic theorems
   ------------------------------------------------------------------------ *)

val () = Feedback.set_trace "Theory.save_thm_reporting" 1

val rrw = SRW_TAC [boolSimps.LET_ss, realSimps.REAL_ARITH_ss]

(* |- !n. 0 < 2 pow n *)
Theorem zero_lt_twopow[simp] =
   REAL_POW_LT |> Q.SPEC `2` |> SIMP_RULE (srw_ss()) [];

(* |- !n. 0 <= 2 pow n *)
Theorem zero_le_twopow[simp] =
   MATCH_MP REAL_LT_IMP_LE (Drule.SPEC_ALL zero_lt_twopow) |> GEN_ALL;


Theorem zero_neq_twopow:   !n. 2 pow n <> 0
Proof simp[]
QED

Theorem zero_le_pos_div_twopow[simp]:
   !m n. 0 <= &m / 2 pow n
Proof
  rw [REAL_LE_DIV, REAL_LT_IMP_LE]
QED

Theorem div_eq0[simp]:
   !a b. 0r < b ==> ((a / b = 0) = (a = 0))
Proof
   rw [REAL_EQ_LDIV_EQ]
QED

(* !b. 2 <= 2 ** b <=> 1 <= b *)
Theorem exp_ge2[simp] =
  logrootTheory.LE_EXP_ISO |> Q.SPECL [`2`, `1`] |> reduceLib.REDUCE_RULE
  |> Conv.GSYM;


(* !b. 4 <= 2 ** b <=> 2 <= b *)
val exp_ge4 =
  logrootTheory.LE_EXP_ISO
  |> Q.SPECL [`2`, `2`]
  |> reduceLib.REDUCE_RULE
  |> Conv.GSYM

Theorem exp_gt2[simp] =
  logrootTheory.LT_EXP_ISO
  |> Q.SPECL [`2`, `1`]
  |> reduceLib.REDUCE_RULE
  |> Conv.GSYM
  ;

(* !n x u. (x / 2 pow n = u / 2 pow n) <=> (x = u) *)
val div_twopow =
   eq_rat
   |> Q.INST [`y` |-> `2 pow n`, `v` |-> `2 pow n`]
   |> SIMP_RULE (srw_ss()) []
   |> Q.GENL [`n`, `x`, `u`]

val div_le = Q.prove(
   `!a b c. 0r < a ==> (b / a <= c / a <=> b <= c)`,
   metis_tac [REAL_LE_LMUL, REAL_DIV_RMUL,
              REAL_POS_NZ, REAL_MUL_COMM]
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
   `!n. 0 < n ==> (2 MOD n = 0 <=> n = 1 \/ n = 2)`,
   tac
   )

(* |- !c a. c <> 0 ==> (c * a / c = a) *)
val mul_cancel =
   REAL_DIV_LMUL_CANCEL
   |> Drule.SPEC_ALL
   |> Q.INST [`b` |-> `1`]
   |> SIMP_RULE (srw_ss()) []
   |> Q.GENL [`a`, `c`]

val ge2 = Q.prove(
   `dimindex(:'a) <> 1 ==> 2 <= dimindex (:'a)`,
   rw [DECIDE ``0 < a /\ a <> 1 ==> 2n <= a``])

val ge2b = Q.prove(
   `!n. 2n <= n ==> 1 <= 2n ** (n - 1) - 1`,
   REPEAT strip_tac
   \\ imp_res_tac arithmeticTheory.LESS_EQUAL_ADD
   \\ simp [arithmeticTheory.EXP_ADD, DECIDE ``0 < n ==> 1n <= 2 * n - 1``])

val ge2c = Q.prove(
   `!n m. 1r <= n /\ 2 < m ==> 2 < n * m`,
   rrw [GSYM REAL_LT_LDIV_EQ]
   \\ `2r / m < 1` by (match_mp_tac REAL_LT_1 \\ simp [])
   \\ METIS_TAC [REAL_LTE_TRANS]
   )

val ge1_pow = Q.prove(
   `!a b. 1 <= a /\ 1n <= b ==> a <= a pow b`,
   Induct_on `b`
   \\ rw [pow]
   \\ once_rewrite_tac [REAL_MUL_COMM]
   \\ `0r < a /\ a <> 0`
   by METIS_TAC [REAL_ARITH ``1 <= a ==> 0r < a``,
                 REAL_POS_NZ]
   \\ simp [GSYM REAL_LE_LDIV_EQ, REAL_DIV_REFL]
   \\ Cases_on `b = 0`
   \\ simp []
   \\ `1 <= b` by decide_tac
   \\ metis_tac [REAL_LE_TRANS]
   )

(* |- !n x. 1 < x /\ 1 < n ==> x < x pow n *)
val gt1_pow =
   REAL_POW_MONO_LT
   |> Q.SPEC `1`
   |> REWRITE_RULE [POW_1]

(* |- !a b. 2 <= a /\ 1 <= b ==> 2 <= a * b *)
val prod_ge2 =
   REAL_LE_MUL2
   |> Q.SPECL [`2`, `a`, `1`, `b`]
   |> SIMP_RULE (srw_ss()) []
   |> Q.GENL [`a`, `b`]

val le1 = Q.prove(
   `!x y. 0 < y /\ x <= y ==> x / y <= 1r`,
   REPEAT STRIP_TAC
   \\ Cases_on `x = y`
   \\ ASM_SIMP_TAC bool_ss
        [REAL_LE_REFL, REAL_DIV_REFL,
         REAL_POS_NZ]
   \\ ASM_SIMP_TAC bool_ss [REAL_LE_LDIV_EQ, REAL_MUL_LID]
   )

Theorem le2: !n m. 2r <= n /\ 2 <= m ==> 2 <= n * m
Proof rrw [prod_ge2]
QED

val ge4 = Q.prove(
   `!n. n <> 0 ==> 4n <= 2 EXP n * 2`,
   Cases
   \\ simp [arithmeticTheory.EXP]
   )

val ge2d = Q.prove(
   `!n m. 2r <= n /\ 2 <= m ==> 2 < n * m`,
   rrw [GSYM REAL_LT_LDIV_EQ]
   \\ `2r / m <= 1`
   by (match_mp_tac le1 \\ ASM_SIMP_TAC (srw_ss()++realSimps.REAL_ARITH_ss) [])
   \\ imp_res_tac (REAL_ARITH ``a <= 1 ==> a < 2r``)
   \\ METIS_TAC [REAL_LTE_TRANS]
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
   |> SIMP_RULE (srw_ss()) [DECIDE ``1n <= n <=> 0 < n``, word_lt0]
   |> GEN_ALL

val mult_id = Q.prove(
  `!a b. 1 < a ==> ((a * b = a) = (b = 1n))`,
  Induct_on `b`
  \\ lrw [arithmeticTheory.MULT_CLAUSES]
  )

(* |- !x y. 1 <= y /\ 0 < x ==> x <= x * y *)
val le_mult =
   REAL_LE_LDIV_EQ
   |> Q.SPECL [`x`, `y`, `x`]
   |> Q.DISCH `1 <= y`
   |> SIMP_RULE bool_ss [boolTheory.AND_IMP_INTRO, REAL_POS_NZ,
                         REAL_DIV_REFL]
   |> ONCE_REWRITE_RULE [REAL_MUL_COMM]
   |> Q.GENL [`x`, `y`]

(* |- !x y. x < 1 /\ 0 < y ==> y * x < y *)
val lt_mult =
   REAL_LT_RDIV_EQ
   |> Q.SPECL [`x`, `y`, `y`]
   |> Q.DISCH `x < 1`
   |> SIMP_RULE bool_ss [boolTheory.AND_IMP_INTRO, REAL_POS_NZ,
                         REAL_DIV_REFL]
   |> ONCE_REWRITE_RULE [REAL_MUL_COMM]
   |> Q.GENL [`x`, `y`]

(*  |- !x y. 1 < y /\ 0 < x ==> x < y * x  *)
val gt_mult =
   REAL_LT_LDIV_EQ
   |> Q.SPECL [`x`, `y`, `x`]
   |> Q.DISCH `1 < y`
   |> SIMP_RULE bool_ss [boolTheory.AND_IMP_INTRO, REAL_POS_NZ,
                         REAL_DIV_REFL]
   |> Q.GENL [`x`, `y`]

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
   `!a b d. 0r < d ==> (a / d - b / d = (a - b) / d)`,
   rrw [REAL_EQ_RDIV_EQ, REAL_SUB_RDISTRIB,
        REAL_DIV_RMUL]
   )

(* |- !x. 0 <= x ==> (abs x = x) *)
val gt0_abs =
   ABS_REFL
   |> Q.SPEC `x`
   |> Q.DISCH `0 <= x`
   |> SIMP_RULE bool_ss []
   |> Drule.GEN_ALL

(*
(* !z x y. 0 <> z ==> ((x = y) <=> (x * z = y * z)) *)
val mul_into =
   REAL_EQ_RMUL
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
   Drule.GEN_ALL $ wordsLib.WORD_DECIDE “~(x <> -1w /\ x <> 0w: word1) /\
                                         ~(x <> 1w /\ x <> 0w)”


val sign_neq = Q.prove(
   `!x. ~x <> x: word1`,
   wordsLib.Cases_word_value
   \\ simp []
   )

val lem = Q.prove(
  `(1w #>> 1 <> 0w : 'a word) /\ word_msb (1w : 'a word #>> 1)`,
  simp_tac (srw_ss()++wordsLib.WORD_BIT_EQ_ss) []
  \\ conj_tac
  >| [qexists_tac `dimindex(:'a) - 1`, all_tac]
  \\ simp [DECIDE ``0n < n ==> (n - 1 + 1 = n)``, wordsTheory.word_index]
  )

Theorem some_nan_components[local]:
   !fp_op.
       ((float_some_qnan fp_op).Exponent = UINT_MAXw) /\
       ((float_some_qnan fp_op).Significand <> 0w)
Proof
   strip_tac \\ simp [float_some_qnan_def]
   \\ SELECT_ELIM_TAC
   \\ conj_tac
   >- (
       simp [float_is_nan_def, float_is_signalling_def]
       \\ EXISTS_TAC
             ``(K (<| Sign := 0w;
                      Exponent := UINT_MAXw: 'b word;
                      Significand := (1w #>> 1): 'a word |>)) :
               ('a, 'b) fp_op -> ('a, 'b) float``
       \\ simp [float_value_def, lem]
      )
   \\ strip_tac
   \\ Cases_on `float_value (x fp_op)`
   \\ simp [float_is_nan_def]
   \\ pop_assum mp_tac
   \\ rw [float_value_def]
QED

Theorem float_components[simp]:
    ((float_plus_infinity (:'t # 'w)).Sign = 0w) /\
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
    (!fp_op. (float_some_qnan fp_op).Exponent = UINT_MAXw) /\
    (!fp_op. (float_some_qnan fp_op).Significand <> 0w) /\
    (!x. (float_negate x).Sign = ~x.Sign) /\
    (!x. (float_negate x).Exponent = x.Exponent) /\
    (!x. (float_negate x).Significand = x.Significand)
Proof
   rw [float_plus_infinity_def, float_minus_infinity_def,
       float_plus_zero_def, float_minus_zero_def, float_plus_min_def,
       float_minus_min_def, float_top_def, float_bottom_def,
       some_nan_components, float_negate_def]
QED

Theorem float_distinct[simp]:
    (float_plus_infinity (:'t # 'w) <> float_minus_infinity (:'t # 'w)) /\
    (float_plus_infinity (:'t # 'w) <> float_plus_zero (:'t # 'w)) /\
    (float_plus_infinity (:'t # 'w) <> float_minus_zero (:'t # 'w)) /\
    (float_plus_infinity (:'t # 'w) <> float_top (:'t # 'w)) /\
    (float_plus_infinity (:'t # 'w) <> float_bottom (:'t # 'w)) /\
    (float_plus_infinity (:'t # 'w) <> float_plus_min (:'t # 'w)) /\
    (float_plus_infinity (:'t # 'w) <> float_minus_min (:'t # 'w)) /\
    (!fp_op. float_plus_infinity (:'t # 'w) <> float_some_qnan fp_op) /\
    (float_minus_infinity (:'t # 'w) <> float_plus_zero (:'t # 'w)) /\
    (float_minus_infinity (:'t # 'w) <> float_minus_zero (:'t # 'w)) /\
    (float_minus_infinity (:'t # 'w) <> float_top (:'t # 'w)) /\
    (float_minus_infinity (:'t # 'w) <> float_bottom (:'t # 'w)) /\
    (float_minus_infinity (:'t # 'w) <> float_plus_min (:'t # 'w)) /\
    (float_minus_infinity (:'t # 'w) <> float_minus_min (:'t # 'w)) /\
    (!fp_op. float_minus_infinity (:'t # 'w) <> float_some_qnan fp_op) /\
    (float_plus_zero (:'t # 'w) <> float_minus_zero (:'t # 'w)) /\
    (float_plus_zero (:'t # 'w) <> float_top (:'t # 'w)) /\
    (float_plus_zero (:'t # 'w) <> float_bottom (:'t # 'w)) /\
    (float_plus_zero (:'t # 'w) <> float_plus_min (:'t # 'w)) /\
    (float_plus_zero (:'t # 'w) <> float_minus_min (:'t # 'w)) /\
    (!fp_op. float_plus_zero (:'t # 'w) <> float_some_qnan fp_op) /\
    (float_minus_zero (:'t # 'w) <> float_top (:'t # 'w)) /\
    (float_minus_zero (:'t # 'w) <> float_bottom (:'t # 'w)) /\
    (float_minus_zero (:'t # 'w) <> float_plus_min (:'t # 'w)) /\
    (float_minus_zero (:'t # 'w) <> float_minus_min (:'t # 'w)) /\
    (!fp_op. float_minus_zero (:'t # 'w) <> float_some_qnan fp_op) /\
    (float_top (:'t # 'w) <> float_minus_min (:'t # 'w)) /\
    (float_top (:'t # 'w) <> float_bottom (:'t # 'w)) /\
    (!fp_op. float_top (:'t # 'w) <> float_some_qnan fp_op) /\
    (float_bottom (:'t # 'w) <> float_plus_min (:'t # 'w)) /\
    (!fp_op. float_bottom (:'t # 'w) <> float_some_qnan fp_op) /\
    (!fp_op. float_plus_min (:'t # 'w) <> float_some_qnan fp_op) /\
    (float_plus_min (:'t # 'w) <> float_minus_min (:'t # 'w)) /\
    (!fp_op. float_minus_min (:'t # 'w) <> float_some_qnan fp_op) /\
    (!x. float_negate x <> x)
Proof
   rw [float_component_equality, float_components, two_mod_not_one, sign_neq,
       wordsTheory.word_T_not_zero, wordsTheory.WORD_EQ_NEG]
QED

Theorem float_values[simp]:
    (float_value (float_plus_infinity (:'t # 'w)) = Infinity) /\
    (float_value (float_minus_infinity (:'t # 'w)) = Infinity) /\
    (!fp_op. float_value (float_some_qnan fp_op) = NaN) /\
    (float_value (float_plus_zero (:'t # 'w)) = Float 0) /\
    (float_value (float_minus_zero (:'t # 'w)) = Float 0) /\
    (float_value (float_plus_min (:'t # 'w)) =
        Float (2r / (2r pow (bias (:'w) + precision (:'t))))) /\
    (float_value (float_minus_min (:'t # 'w)) =
        Float (-2r / (2r pow (bias (:'w) + precision (:'t)))))
Proof
   rw [float_plus_infinity_def, float_minus_infinity_def,
       float_plus_zero_def, float_minus_zero_def, float_plus_min_def,
       float_minus_min_def, some_nan_components, float_negate_def,
       float_value_def, float_to_real_def, wordsTheory.word_T_not_zero,
       mult_rat, POW_ADD, GSYM REAL_NEG_MINUS1,
       GSYM REAL_MUL_LNEG, neg_rat]
QED

Theorem zero_to_real[simp]:
   (float_to_real (float_plus_zero (:'t # 'w)) = 0) /\
   (float_to_real (float_minus_zero (:'t # 'w)) = 0)
Proof
   rw [float_plus_zero_def, float_minus_zero_def,
       float_negate_def, float_to_real_def]
QED

Theorem sign_not_zero: !s: word1. -1 pow w2n s <> 0
Proof wordsLib.Cases_word_value \\ EVAL_TAC
QED

Theorem float_sets:
  (float_is_zero = {float_minus_zero (:'t # 'w);
                    float_plus_zero (:'t # 'w)}) /\
  (float_is_infinite = {float_minus_infinity (:'t # 'w);
                        float_plus_infinity (:'t # 'w)})
Proof
   rw [FUN_EQ_THM, float_is_infinite_def, float_is_zero_def, float_value_def,
       float_plus_infinity_def, float_minus_infinity_def,
       float_plus_zero_def, float_minus_zero_def, float_to_real_def,
       float_negate_def, float_component_equality]
   \\ rw [sign_not_zero, REAL_ARITH ``0r <= n ==> 1 + n <> 0``]
   \\ wordsLib.Cases_on_word_value `x.Sign`
   \\ simp []
QED

val tac =
   rw [float_is_nan_def, float_is_normal_def, float_is_subnormal_def,
       float_is_finite_def, float_is_infinite_def, float_is_zero_def,
       float_is_integral_def, is_integral_def, float_values,
       some_nan_components]
   \\ rw [float_plus_infinity_def, float_minus_infinity_def,
          float_plus_zero_def, float_minus_zero_def, float_top_def,
          float_bottom_def, float_some_qnan_def, float_plus_min_def,
          float_minus_min_def, float_negate_def, float_value_def,
          wordsTheory.WORD_EQ_NEG, REAL_EQ_LDIV_EQ, two_mod_not_one]

Theorem infinity_properties[simp]:
    ~float_is_zero (float_plus_infinity (:'t # 'w)) /\
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
    float_is_infinite (float_minus_infinity (:'t # 'w))
Proof tac
QED

Theorem zero_properties[simp]:
    float_is_zero (float_plus_zero (:'t # 'w)) /\
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
    ~float_is_infinite (float_minus_zero (:'t # 'w))
Proof tac
QED



Theorem some_nan_properties:
  !fp_op.
      ~float_is_zero (float_some_qnan fp_op) /\
      ~float_is_finite (float_some_qnan fp_op) /\
      ~float_is_integral (float_some_qnan fp_op) /\
      float_is_nan (float_some_qnan fp_op) /\
      ~float_is_signalling (float_some_qnan fp_op) /\
      ~float_is_normal (float_some_qnan fp_op) /\
      ~float_is_subnormal (float_some_qnan fp_op) /\
      ~float_is_infinite (float_some_qnan fp_op)
Proof
   tac
   \\ SELECT_ELIM_TAC
   \\ simp []
   \\ qexists_tac
        `(K (<| Sign := 0w;
                Exponent := UINT_MAXw: 'b word;
                Significand := (1w #>> 1): 'a word |>))`
   \\ simp [float_is_signalling_def]
   \\ tac
   \\ fs [lem]
QED

Theorem NMUL_EQ_2:
  ((m:num) * n = 2) <=> (m = 1) /\ (n = 2) \/ (m = 2) /\ (n = 1)
Proof
  assume_tac dividesTheory.PRIME_2 >>
  gs[dividesTheory.prime_def, dividesTheory.divides_def, Excl "PRIME_2",
     PULL_EXISTS] >>
  eq_tac >> simp[DISJ_IMP_THM] >>
  disch_then (assume_tac o SYM) >> first_x_assum drule >>
  simp[DISJ_IMP_THM] >> strip_tac >> gs[]
QED

Theorem min_properties[simp]:
    ~float_is_zero (float_plus_min (:'t # 'w)) /\
    float_is_finite (float_plus_min (:'t # 'w)) /\
    (float_is_integral (float_plus_min (:'t # 'w)) <=>
     (precision(:'w) = 1) /\ (precision(:'t) = 1)) /\
    ~float_is_nan (float_plus_min (:'t # 'w)) /\
    ~float_is_normal (float_plus_min (:'t # 'w)) /\
    float_is_subnormal (float_plus_min (:'t # 'w)) /\
    ~float_is_infinite (float_plus_min (:'t # 'w)) /\
    ~float_is_zero (float_minus_min (:'t # 'w)) /\
    float_is_finite (float_minus_min (:'t # 'w)) /\
    (float_is_integral (float_minus_min (:'t # 'w)) <=>
     (precision(:'w) = 1) /\ (precision(:'t) = 1)) /\
    ~float_is_nan (float_minus_min (:'t # 'w)) /\
    ~float_is_normal (float_minus_min (:'t # 'w)) /\
    float_is_subnormal (float_minus_min (:'t # 'w)) /\
    ~float_is_infinite (float_minus_min (:'t # 'w))
Proof
   tac (* after this the float_is_integral cases remain *) >>
   simp[ABS_DIV, iffRL ABS_REFL, real_div, REAL_POW_ADD,
        REAL_INV_MUL', SF realSimps.RMULRELNORM_ss] >>
   simp[REAL_OF_NUM_POW, wordsTheory.INT_MAX_def,
        wordsTheory.INT_MIN_def, NMUL_EQ_2] >>
   simp[DECIDE “x <= 1n <=> (x = 1) \/ (x = 0)”]
QED

val lem1 = Q.prove(
   `0w <+ (-2w:'a word) <=> (dimindex(:'a) <> 1)`,
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
   \\ srw_tac[] [float_to_real_def, two_mod_eq_zero, wordsTheory.dimword_def,
                 REAL_ARITH ``0r <= n ==> 1 + n <> 0``, exp_id, lem1,
                 DECIDE ``0 < n ==> n <> 0n``]
   \\ Cases_on `dimindex(:'w) = 1`
   \\ lrw [lem2]

Theorem top_properties[simp]:
    ~float_is_zero (float_top (:'t # 'w)) /\
    float_is_finite (float_top (:'t # 'w)) /\
    (* float_is_integral (float_top (:'t # 'w)) = ?? /\ *)
    ~float_is_nan (float_top (:'t # 'w)) /\
    (float_is_normal (float_top (:'t # 'w)) = (precision(:'w) <> 1)) /\
    (float_is_subnormal (float_top (:'t # 'w)) = (precision(:'w) = 1)) /\
    ~float_is_infinite (float_top (:'t # 'w))
Proof tac
QED

Theorem bottom_properties[simp]:
    ~float_is_zero (float_bottom (:'t # 'w)) /\
    float_is_finite (float_bottom (:'t # 'w)) /\
    (* float_is_integral (float_bottom (:'t # 'w)) = ?? /\ *)
    ~float_is_nan (float_bottom (:'t # 'w)) /\
    (float_is_normal (float_bottom (:'t # 'w)) = (precision(:'w) <> 1)) /\
    (float_is_subnormal (float_bottom (:'t # 'w)) = (precision(:'w) = 1)) /\
    ~float_is_infinite (float_bottom (:'t # 'w))
Proof tac
QED

Theorem float_is_zero:
  !x. float_is_zero x <=> (x.Exponent = 0w) /\ (x.Significand = 0w)
Proof
   rw [float_is_zero_def, float_value_def, float_to_real_def, sign_not_zero,
       REAL_ARITH ``0 <= x ==> 1 + x <> 0r``,
       REAL_LE_DIV, REAL_LT_IMP_LE]
QED

Theorem float_is_finite:
  !x. float_is_finite x <=>
      float_is_normal x \/ float_is_subnormal x \/ float_is_zero x
Proof
  rw [float_is_finite_def, float_is_normal_def, float_is_subnormal_def,
      float_is_zero, float_value_def]
  \\ Cases_on `x.Exponent = 0w`
  \\ Cases_on `x.Significand = 0w`
  \\ fs []
QED

Theorem float_cases_finite:
  !x. float_is_nan x \/ float_is_infinite x \/ float_is_finite x
Proof
  rw [float_is_nan_def, float_is_infinite_def, float_is_finite_def]
  \\ Cases_on `float_value x`
  \\ fs []
QED

Theorem float_distinct_finite:
  !x. ~(float_is_nan x /\ float_is_infinite x) /\
      ~(float_is_nan x /\ float_is_finite x) /\
      ~(float_is_infinite x /\ float_is_finite x)
Proof
  rw [float_is_nan_def, float_is_infinite_def, float_is_finite_def]
  \\ Cases_on `float_value x`
  \\ fs []
QED

Theorem float_cases:
  !x. float_is_nan x \/ float_is_infinite x \/ float_is_normal x \/
      float_is_subnormal x \/ float_is_zero x
Proof metis_tac [float_cases_finite, float_is_finite]
QED

Theorem float_is_distinct:
  !x. ~(float_is_nan x /\ float_is_infinite x) /\
      ~(float_is_nan x /\ float_is_normal x) /\
      ~(float_is_nan x /\ float_is_subnormal x) /\
      ~(float_is_nan x /\ float_is_zero x) /\
      ~(float_is_infinite x /\ float_is_normal x) /\
      ~(float_is_infinite x /\ float_is_subnormal x) /\
      ~(float_is_infinite x /\ float_is_zero x) /\
      ~(float_is_normal x /\ float_is_subnormal x) /\
      ~(float_is_normal x /\ float_is_zero x) /\
      ~(float_is_subnormal x /\ float_is_zero x)
Proof
  rw []
  \\ TRY (metis_tac [float_is_finite, float_distinct_finite])
  \\ fs [float_is_normal_def, float_is_subnormal_def, float_is_zero]
  \\ Cases_on `x.Exponent = 0w`
  \\ Cases_on `x.Exponent = -1w`
  \\ Cases_on `x.Significand = 0w`
  \\ fs []
QED

Theorem float_infinities:
  !x. float_is_infinite x <=>
       (x = float_plus_infinity (:'t # 'w)) \/
       (x = float_minus_infinity (:'t # 'w))
Proof
  strip_tac
  \\ Q.ISPEC_THEN `x : ('t, 'w) float` strip_assume_tac float_cases_finite
  \\ TRY (metis_tac [float_distinct_finite, infinity_properties])
  \\ Cases_on `float_value x`
  \\ Cases_on `x.Exponent = -1w`
  \\ Cases_on `x.Significand = 0w`
  \\ fs [float_is_infinite_def, float_value_def,
         float_plus_infinity_def, float_minus_infinity_def,
         float_negate_def, float_component_equality]
  \\ wordsLib.Cases_on_word_value `x.Sign`
  \\ simp []
QED

Theorem float_infinities_distinct:
  !x. ~((x = float_plus_infinity (:'t # 'w)) /\
        (x = float_minus_infinity (:'t # 'w)))
Proof
  simp [float_plus_infinity_def, float_minus_infinity_def,
        float_negate_def, float_component_equality]
QED
(* ------------------------------------------------------------------------ *)

Theorem float_to_real_negate:
   !x. float_to_real (float_negate x) = -float_to_real x
Proof
   rw [float_to_real_def, float_negate_def]
   \\ wordsLib.Cases_on_word_value `x.Sign`
   \\ rsimp []
QED

Theorem float_negate_negate[simp]:
   !x. float_negate (float_negate x) = x
Proof
   simp [float_negate_def, float_component_equality]
QED

(* ------------------------------------------------------------------------
   Lemma support for rounding theorems
   ------------------------------------------------------------------------ *)

(*
val () = List.app Parse.clear_overloads_on ["bias", "precision"]
*)

local
   val cnv =
      Conv.QCONV
        (REWRITE_CONV [REAL_LDISTRIB, REAL_RDISTRIB])
   val dec =
      METIS_PROVE
        [REAL_DIV_RMUL, REAL_MUL_COMM,
         REAL_MUL_ASSOC, zero_neq_twopow,
         mult_ratr
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

Theorem cancel_rwts[local] = Q.prove(
   `(!a b. (2 pow a * b) / 2 pow a = b) /\
    (!a b c. 2 pow a * (b / 2 pow a * c) = b * c) /\
    (!a b c. a * (b / 2 pow c) * 2 pow c = a * b) /\
    (!a b c. a * (2 pow b * c) / 2 pow b = a * c) /\
    (!a b c. a / 2 pow b * (2 pow b * c) = a * c) /\
    (!a b c. a / 2 pow b * c * 2 pow b = a * c) /\
    (!a b c d. a / 2 pow b * c * (2 pow b * d) = a * c * d) /\
    (!a b c d. a * (2 pow b * c) * d / 2 pow b = a * c * d)`,
   metis_tac
     [REAL_DIV_RMUL, REAL_MUL_COMM,
      REAL_MUL_ASSOC, zero_neq_twopow,
      mult_ratr
      |> Q.INST [`z` |-> `2 pow n`]
      |> REWRITE_RULE [zero_neq_twopow]
      |> GEN_ALL]
   )

val cancel_rwt =
   CANCEL_PROVE
     ``(!a b c d. a * (b + c / 2 pow d) * 2 pow d = a * b * 2 pow d + a * c)``

Theorem ulp: ulp (:'t # 'w) = float_to_real (float_plus_min (:'t # 'w))
Proof
   simp [ulp_def, ULP_def, float_to_real_def, float_plus_min_def,
         mult_rat, GSYM POW_ADD]
QED

Theorem neg_ulp:
   -ulp (:'t # 'w) = float_to_real (float_negate (float_plus_min (:'t # 'w)))
Proof simp [float_to_real_negate, ulp]
QED

val ULP_gt0 = Q.prove(
   `!e. 0 < ULP (e:'w word, (:'t))`,
   rw [ULP_def, REAL_LT_RDIV_0])

val ulp_gt0 = (REWRITE_RULE [GSYM ulp_def] o Q.SPEC `0w`) ULP_gt0

Theorem ULP_le_mono:
   !e1 e2. e2 <> 0w ==> (ULP (e1, (:'t)) <= ULP (e2, (:'t)) <=> e1 <=+ e2)
Proof
   Cases
   \\ Cases
   \\ lrw [ULP_def, wordsTheory.word_ls_n2w, div_le]
   \\ simp [REAL_OF_NUM_POW]
QED

Theorem ulp_lt_ULP: !e: 'w word. ulp (:'t # 'w) <= ULP (e,(:'t))
Proof rw [ulp_def] \\ Cases_on `e = 0w` \\ simp [ULP_le_mono]
QED

Theorem lem[local]:
   !n. 0 < n ==> 3 < 2 pow SUC n
Proof
   Induct
   \\ rw [Once pow]
   \\ Cases_on `0 < n`
   \\ simp [DECIDE ``~(0n < n) ==> (n = 0)``,
            REAL_ARITH ``3r < n ==> 3 < 2 * n``]
QED

Theorem ulp_lt_largest: ulp (:'t # 'w) < largest (:'t # 'w)
Proof
   simp [ulp_def, ULP_def, largest_def, REAL_LT_RMUL_0, cancel_rwts,
         REAL_LT_LDIV_EQ, POW_ADD]
   \\ simp [REAL_SUB_RDISTRIB, REAL_SUB_LDISTRIB,
            REAL_MUL_LINV, GSYM realaxTheory.REAL_MUL_ASSOC,
            GSYM (CONJUNCT2 pow)]
   \\ simp [REAL_ARITH ``(a * b) - a = a * (b - 1): real``]
   \\ match_mp_tac ge2c
   \\ rw [GSYM REAL_LT_ADD_SUB, POW_2_LE1, lem]
QED

Theorem ulp_lt_threshold:
   ulp (:'t # 'w) < threshold (:'t # 'w)
Proof
   simp [ulp_def, ULP_def, threshold_def, REAL_LT_RMUL_0,
         cancel_rwts, REAL_LT_LDIV_EQ, POW_ADD,
         pow]
   \\ simp [REAL_SUB_RDISTRIB, REAL_SUB_LDISTRIB,
            REAL_MUL_LINV, REAL_INV_MUL,
            GSYM realaxTheory.REAL_MUL_ASSOC]
   \\ simp [REAL_ARITH ``(a * b) - a * c = a * (b - c): real``]
   \\ match_mp_tac ge2c
   \\ rw [POW_2_LE1, GSYM REAL_LT_ADD_SUB,
          REAL_INV_1OVER, GSYM (CONJUNCT2 pow),
          REAL_LT_LDIV_EQ, lem,
          REAL_ARITH ``3r < n ==> 5 < n * 2``]
QED

Theorem lt_ulp_not_infinity0[local] =
   MATCH_MP
      (REAL_ARITH ``u < l ==> abs x < u ==> ~(x < -l) /\ ~(x > l)``)
      ulp_lt_largest
   |> Drule.GEN_ALL

Theorem lt_ulp_not_infinity1[local] =
   MATCH_MP
      (REAL_ARITH
         ``u < l ==> 2 * abs x <= u ==> ~(x <= -l) /\ ~(x >= l)``)
      ulp_lt_threshold
   |> Drule.GEN_ALL

Theorem abs_float_value:
    (!b: word1 c d. abs (-1 pow w2n b * c * d) = abs (c * d)) /\
    (!b: word1 c. abs (-1 pow w2n b * c) = abs c)
Proof
   conj_tac
   \\ wordsLib.Cases_word_value
   \\ simp [ABS_MUL]
QED

(* |- !x n. abs (1 + &n / 2 pow x) = 1 + &n / 2 pow x *)
Theorem abs_significand[local] =
   REAL_ARITH ``!a b. 0 <= a /\ 0 <= b ==> (abs (a + b) = a + b)``
   |> Q.SPECL [`1`, `&n / 2 pow x`]
   |> Conv.CONV_RULE
        (Conv.RATOR_CONV (SIMP_CONV (srw_ss()++realSimps.REAL_ARITH_ss)
            [REAL_LE_DIV, REAL_POS,
             REAL_LT_IMP_LE]))
   |> REWRITE_RULE []
   |> GEN_ALL

Theorem less_than_ulp:
    !a: ('t, 'w) float.
       abs (float_to_real a) < ulp (:'t # 'w) <=>
       (a.Exponent = 0w) /\ (a.Significand = 0w)
Proof
   strip_tac
   \\ eq_tac
   \\ rw [ulp_def, ULP_def, float_to_real_def, abs_float_value, abs_significand,
          ABS_MUL, ABS_DIV, ABS_N,
          gt0_abs, mult_rat, REAL_LT_RDIV_0]
   >| [
      SPOSE_NOT_THEN strip_assume_tac
      \\ qpat_x_assum `x < y: real` mp_tac
      \\ simp [REAL_NOT_LT, GSYM POW_ADD,
               REAL_LE_RDIV_EQ, REAL_DIV_RMUL]
      \\ Cases_on `a.Significand`
      \\ lfs [],
      (* -- *)
      simp [REAL_NOT_LT, REAL_LDISTRIB,
            REAL_LE_LDIV_EQ, REAL_RDISTRIB,
            POW_ADD, cancel_rwts]
      \\ simp [GSYM realaxTheory.REAL_LDISTRIB]
      \\ match_mp_tac le2
      \\ conj_tac
      >- (match_mp_tac ge1_pow
          \\ Cases_on `a.Exponent`
          \\ lfs [])
      \\ match_mp_tac
           (REAL_ARITH ``2r <= a /\ 0 <= x ==> 2 <= a + x``)
      \\ simp [ge1_pow, DECIDE ``0n < a ==> 1 <= a``]
   ]
QED

(* ------------------------------------------------------------------------ *)

Theorem Float_is_finite[local]:
    !y: ('t, 'w) float r.
      (float_value y = Float r) ==> float_is_finite y
Proof
   rw [float_is_finite_def]
QED

Theorem Float_float_to_real[local]:
    !y: ('t, 'w) float r.
      (float_value y = Float r) ==> (float_to_real y = r)
Proof rw [float_value_def]
QED

Theorem float_is_zero_to_real:
   !x. float_is_zero x = (float_to_real x = 0)
Proof
   rw [float_is_zero_def, float_value_def, float_to_real_EQ0] >>
   simp[theorem "float_component_equality"]
QED

(* !x. float_is_zero x ==> (float_to_real x = 0) *)
val float_is_zero_to_real_imp = iffLR float_is_zero_to_real

Theorem pos_subnormal[local]:
    !a b n. 0 <= 2 / 2 pow a * (&n / 2 pow b)
Proof rrw [REAL_LE_MUL]
QED

val pos_normal = Q.prove(
   `!a b c n. 0 <= 2 pow a / 2 pow b * (1 + &n / 2 pow c)`,
   rw [REAL_LE_DIV, REAL_LE_MUL,
       REAL_ARITH ``0r <= n ==> 0 <= 1 + n``]
   )

val pos_normal2 = Q.prove(
   `!a b c n. 0 <= 2 pow a / 2 pow b * (&n / 2 pow c)`,
   rw [REAL_LE_DIV, REAL_LE_MUL,
       REAL_ARITH ``0r <= n ==> 0 <= 1 + n``]
   )

val thms =
   List.map REAL_ARITH
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
   \\ rw [ULP_def, float_to_real_def, float_is_zero, ABS_NEG,
          pos_normal, pos_subnormal,
          REAL_ARITH ``a - -1r * b * c = a + b * c``,
          REAL_ARITH ``-1r * b * c - a = -(b * c + a)``,
          REAL_ARITH ``0 <= a /\ 0 <= b ==> (abs (a + b) = a + b)``]
   \\ rw [REAL_LDISTRIB]
   >| (List.map match_mp_tac (thms @ thms))
   \\ rrw [pos_subnormal, pos_normal2, word_lt0, POW_ADD,
          REAL_LE_LDIV_EQ, le2, pow_ge2, ge1_pow, le_mult,
          fcpTheory.DIMINDEX_GE_1, REAL_LE_DIV, POW_2_LE1,
          cancel_rwts, DECIDE ``n <> 0n ==> 1 <= 2 * n``,
          REAL_ARITH ``2 <= a ==> 1r <= a``]
   )

Theorem diff_sign_ULP_gt[local]:
   !x: ('t, 'w) float y: ('t, 'w) float.
     ~float_is_zero x /\ ~float_is_zero y /\ x.Sign <> y.Sign ==>
     ULP (x.Exponent,(:'t)) < abs (float_to_real x - float_to_real y)
Proof
   NTAC 2 strip_tac
   \\ wordsLib.Cases_on_word_value `x.Sign`
   \\ wordsLib.Cases_on_word_value `y.Sign`
   \\ rw [ULP_def, float_to_real_def, float_is_zero, ABS_NEG,
          pos_normal, pos_subnormal,
          REAL_ARITH ``a - -1r * b * c = a + b * c``,
          REAL_ARITH ``-1r * b * c - a = -(b * c + a)``,
          REAL_ARITH ``0 <= a /\ 0 <= b ==> (abs (a + b) = a + b)``]
   \\ rrw [REAL_LDISTRIB, REAL_RDISTRIB,
           REAL_LT_LDIV_EQ, REAL_LE_MUL,
           POW_2_LE1, POW_ADD,
           pos_subnormal, pos_normal2, word_lt0, cancel_rwts, word_lt0,
           prod_ge2, pow_ge2, le_mult,
           DECIDE ``0n < a /\ 0 < b ==> 2 < 2 * a + 2 * b``,
           DECIDE ``1n <= n <=> 0 < n``,
           DECIDE ``0n < x ==> 0 < 2 * x``,
           REAL_ARITH ``a <= b /\ 0r <= c /\ 1 <= d ==> a < b + c + d``,
           REAL_ARITH
              ``a <= b /\ 0r <= c /\ 2 <= d /\ 0 <= e ==> a < b + c + (d + e)``,
           REAL_ARITH
              ``1 <= a /\ 2r <= b /\ 0 <= c ==> 2 < 2 * a + (b + c)``
           |> Q.INST [`a` |-> `&n`]
           |> SIMP_RULE (srw_ss()) []
           ]
QED

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

(* |- !w. w2n w < 2 ** precision (:'a) *)
val w2n_lt_pow = REWRITE_RULE [wordsTheory.dimword_def] wordsTheory.w2n_lt

Theorem w2n_lt_pow_sub1[local]:
  !x:'a word. x <> -1w ==> w2n x < 2 ** dimindex(:'a) - 1
Proof
   REPEAT strip_tac
   \\ match_mp_tac (DECIDE ``a < b /\ a <> b - 1 ==> a < b - 1n``)
   \\ simp [w2n_lt_pow]
   \\ Cases_on `x`
   \\ fs [wordsTheory.WORD_NEG_1, wordsTheory.word_T_def, wordsTheory.w2n_n2w,
          wordsTheory.UINT_MAX_def, wordsTheory.dimword_def]
QED

Theorem nobias_denormal_lt_1[local]:
  !w:'t word. &w2n w / 2 pow precision (:'t) < 1
Proof
  rw [REAL_LT_LDIV_EQ, REAL_OF_NUM_POW, w2n_lt_pow]
QED

Theorem nobias_denormal_lt_2[local]:
  !w:'t word. 2 * (&w2n w / 2 pow precision (:'t)) < 2
Proof
  rw [REAL_ARITH ``2r * n < 2 <=> n < 1``, nobias_denormal_lt_1]
QED

Theorem subnormal_lt_normal[local]:
  !x y z.
    y <> 0w ==>
    2 / 2 pow bias (:'w) * (&w2n (x:'t word) / 2 pow precision (:'t)) <
    2 pow w2n (y:'w word) / 2 pow bias (:'w) *
    (1 + &w2n (z:'t word) / 2 pow precision (:'t))
Proof
   REPEAT strip_tac
   \\ once_rewrite_tac
        [REAL_LT_LMUL
         |> Q.SPEC `2 pow bias (:'w)`
         |> REWRITE_RULE [zero_lt_twopow]
         |> GSYM]
   \\ rewrite_tac [cancel_rwts, REAL_LDISTRIB]
   \\ match_mp_tac
        (REAL_ARITH ``a < 2r /\ 2 <= b /\ 0 <= c ==> a < b + c``)
   \\ rw [nobias_denormal_lt_2, pow_ge2, REAL_LE_MUL]
QED

fun tac thm =
   REPEAT strip_tac
   \\ match_mp_tac (Q.SPECL [`a`, `b - c`, `x * b - c`] thm)
   \\ rsimp [REAL_LE_SUB_CANCEL2, GSYM REAL_LE_LDIV_EQ,
             REAL_DIV_REFL, REAL_SUB_ADD]

Theorem weaken_leq[local]:
  !x a b c. 1r <= x /\ a <= b - c /\ 0 < b ==> a <= x * b - c
Proof tac REAL_LE_TRANS
QED

Theorem weaken_lt[local]:
  !x a b c. 1r <= x /\ a < b - c /\ 0 < b ==> a < x * b - c
Proof tac REAL_LTE_TRANS
QED

Theorem abs_diff1[local]:
    !s:word1 a b.
       a < b ==> (abs (-1 pow w2n s * a - -1 pow w2n s * b) = (b - a))
Proof
   wordsLib.Cases_word_value \\ rrw []
QED

val abs_diff2 = Q.prove(
   `!s:word1 a b.
       b < a ==> (abs (-1 pow w2n s * a - -1 pow w2n s * b) = (a - b))`,
   wordsLib.Cases_word_value \\ rrw [])

Theorem abs_diff1a[local] =
   abs_diff1
   |> Q.SPECL [`(y:('t,'w) float).Sign`,
               `(2 / 2 pow bias (:'w)) *
                (&w2n (x:('t,'w) float).Significand / 2 pow precision (:'t))`,
               `(2 pow w2n (y:('t,'w) float).Exponent / 2 pow bias (:'w)) *
                (1 + &w2n y.Significand / 2 pow precision (:'t))`]

Theorem abs_diff1b[local] =
   abs_diff1
   |> Q.SPECL [`(y:('t,'w) float).Sign`,
               `(2 pow w2n (x:('t,'w) float).Exponent / 2 pow bias (:'w)) *
                (1 + &w2n x.Significand / 2 pow precision (:'t))`,
               `(2 pow (p + (w2n (x:('t,'w) float).Exponent + 1)) /
                2 pow bias (:'w)) *
                (1 + &w2n (y:('t,'w) float).Significand /
                2 pow precision (:'t))`]

Theorem abs_diff1c[local] =
   abs_diff1
   |> Q.SPECL [`(y:('t,'w) float).Sign`,
               `(2 / 2 pow bias (:'w)) *
                (&w2n (x:('t,'w) float).Significand / 2 pow precision (:'t))`,
               `(2 / 2 pow bias (:'w)) *
                (&w2n (y:('t,'w) float).Significand / 2 pow precision (:'t))`]

Theorem abs_diff1d[local] =
   abs_diff1
   |> Q.SPECL [`(y:('t,'w) float).Sign`,
               `(2 pow w2n (y:('t,'w) float).Exponent / 2 pow bias (:'w)) *
                (1 + &w2n (x:('t,'w) float).Significand /
                2 pow precision (:'t))`,
               `(2 pow w2n (y:('t,'w) float).Exponent / 2 pow bias (:'w)) *
                (1 + &w2n y.Significand / 2 pow precision (:'t))`]

Theorem abs_diff1e[local] =
   abs_diff1
   |> Q.SPECL [`(y:('t,'w) float).Sign`,
               `(2 / 2 pow bias (:'w))`,
               `(2 pow w2n (y:('t,'w) float).Exponent / 2 pow bias (:'w)) *
                (1 + &w2n y.Significand / 2 pow precision (:'t))`]

Theorem abs_diff1f[local] =
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
      (fn th => rewrite_tac [REWRITE_RULE [REAL_MUL_ASSOC] th])

Theorem diff_exponent_boundary[local]:
  !x: ('t, 'w) float y: ('t, 'w) float.
    exponent_boundary y x ==>
    (abs (float_to_real x - float_to_real y) = ULP (y.Exponent, (:'t)))
Proof
   rw [ULP_def, exponent_boundary_def, float_to_real_def]
   >- (Cases_on `x.Exponent` \\ fs [])
   \\ abs_diff_tac abs_diff2e
   >- (match_mp_tac abs_diff2e
       \\ simp [REAL_LT_RDIV_EQ, REAL_LT_LMUL,
                REAL_ARITH ``2 * a = a * 2r``,
                REAL_ARITH ``1 + n < 2 <=> n < 1r``, cancel_rwts,
                REWRITE_RULE [arithmeticTheory.ADD1] pow]
       \\ simp [REAL_LT_LDIV_EQ, REAL_OF_NUM_POW,
                w2n_lt_pow]
      )
   \\ simp [REAL_EQ_RDIV_EQ, POW_ADD,
            REAL_SUB_RDISTRIB, cancel_rwts]
   \\ simp [REAL_ARITH
              ``(a * b * c - a * d * e) = a * (b * c - d * e: real)``,
            (GSYM o ONCE_REWRITE_RULE [REAL_MUL_COMM])
               REAL_EQ_RDIV_EQ,
            REAL_DIV_REFL]
   \\ simp [REAL_DIV_RMUL, REAL_EQ_SUB_RADD,
            REAL_ADD_RDISTRIB, wordsTheory.w2n_minus1,
            wordsTheory.dimword_def]
   \\ rsimp [REAL_OF_NUM_POW,
             DECIDE ``0 < n ==> (1 + (n + (n - 1)) = 2n * n)``]
QED

val not_next_tac =
   REPEAT strip_tac
   \\ imp_res_tac arithmeticTheory.LESS_EQUAL_ADD
   \\ imp_res_tac arithmeticTheory.LESS_ADD_1
   \\ pop_assum kall_tac
   \\ REV_FULL_SIMP_TAC (srw_ss())
        [DECIDE ``1 < b ==> ((b - 1 = e) = (b = e + 1n))``]
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
      `!x. x <> 0w ==> 1n < 2 EXP w2n x`,
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
      simp [REAL_LE_LDIV_EQ, REAL_LT_LDIV_EQ,
            POW_ADD, REAL_SUB_RDISTRIB,
            REAL_LE_SUB_LADD, REAL_LT_SUB_LADD,
            GSYM realaxTheory.REAL_LDISTRIB, cancel_rwt, cancel_rwts]
      \\ simp [REAL_LDISTRIB]
   val t2 =
      once_rewrite_tac
          [REAL_LT_LMUL
           |> Q.SPEC `2 pow bias (:'w)`
           |> SIMP_RULE (srw_ss()) []
           |> GSYM]
      \\ rewrite_tac [cancel_rwts]
      \\ simp [POW_ADD]
      \\ once_rewrite_tac
           [REAL_ARITH ``a * (b * c) * d = b * (a * c * d): real``]
      \\ simp [REAL_LT_LMUL, REAL_LDISTRIB]
      \\ match_mp_tac
           (REAL_ARITH
               ``a < 1r /\ 1 <= b /\ 0 <= c ==> 1 + a < b * 2 + c``)
      \\ simp [nobias_denormal_lt_1, REAL_LE_MUL,
               POW_2_LE1]
   val t3 =
      simp [REAL_LE_LDIV_EQ, REAL_LT_LDIV_EQ]
      \\ simp [POW_ADD, cancel_rwts,
               REAL_SUB_RDISTRIB, REAL_DIV_RMUL]
      \\ simp [REAL_DIV_RMUL,
               REAL_ARITH
                   ``a * (b + c) * d = a * (b * d + c * d): real``]
      \\ simp [REAL_LE_SUB_LADD, REAL_LT_SUB_LADD,
               REAL_LDISTRIB]
   val t4 =
      match_mp_tac (REAL_ARITH ``a <= b /\ 0r <= c ==> a <= b + c``)
      \\ simp [REAL_LE_MUL, GSYM REAL_LE_SUB_LADD]
      \\ once_rewrite_tac
           [REAL_ARITH
               ``p * (a * 2r) * x - (a * x + a * y) =
                 a * ((p * (2 * x)) - (x + y))``]
      \\ match_mp_tac le_mult
      \\ simp []
      \\ match_mp_tac weaken_leq
      \\ simp [POW_2_LE1, REAL_LT_MUL,
               REAL_ARITH ``2r * a - (a + z) = a - z``]
   fun tac thm q =
      abs_diff_tac thm
      >- (match_mp_tac thm \\ t2)
      \\ Q.ABBREV_TAC `z:real = &w2n ^(Parse.Term q)`
      \\ t3
in
   fun tac1 thm =
      abs_diff_tac thm
      >- (match_mp_tac thm \\ simp [subnormal_lt_normal])
      \\ t1
      \\ match_mp_tac (REAL_ARITH ``0r <= c /\ a <= b ==> a <= b + c``)
      \\ simp [REAL_LE_MUL, REAL_OF_NUM_POW,
               fcpTheory.DIMINDEX_GE_1, lem1, lem2, lem3, lem5,
               word_ge1, w2n_lt_pow]
   val tac2 =
      tac abs_diff1b `(x: ('t, 'w) float).Significand`
      \\ t4
      \\ `?q. 1 <= q /\ (2 pow precision (:'t) = z + q)`
      by (ASSUME_TAC (Q.ISPEC `(x: ('t, 'w) float).Significand` w2n_lt_pow)
           \\ pop_assum
                (strip_assume_tac o MATCH_MP arithmeticTheory.LESS_ADD_1)
           \\ qexists_tac `&(p' + 1n)`
           \\ simp [REAL_OF_NUM_POW, Abbr `z`])
      \\ rsimp []
   val tac3 =
      tac abs_diff2b `(y: ('t, 'w) float).Significand`
      \\ once_rewrite_tac
           [div_le
            |> Q.SPEC `2r pow w2n (y:('t, 'w) float).Exponent`
            |> SIMP_RULE (srw_ss()) []
            |> GSYM]
      \\ simp [GSYM REAL_DIV_ADD, GSYM REAL_ADD_LDISTRIB,
               cancel_rwts]
      \\ rsimp [REAL_OF_NUM_POW, Abbr `z`]
      \\ match_mp_tac lem4
      \\ full_simp_tac (srw_ss()) [exponent_boundary_def]
      \\ REV_FULL_SIMP_TAC (srw_ss())
           [w2n_lt_pow, w2n_lt_pow_sub1, word_lt0, ge4, lem5]
      \\ `p <> 0` by (strip_tac \\
                      full_simp_tac (srw_ss())
                                [DECIDE ``(1 = x + 1) = (x = 0n)``])
      \\ full_simp_tac (srw_ss()) [ge4]
   val tac4 =
      abs_diff_tac abs_diff1a
      >- (match_mp_tac abs_diff1a \\ simp [subnormal_lt_normal])
      \\ t1
      \\ match_mp_tac (REAL_ARITH ``0r <= c /\ a < b ==> a < b + c``)
      \\ simp [REAL_LE_MUL, REAL_OF_NUM_POW,
               fcpTheory.DIMINDEX_GE_1, not_max_suc_lt_dimword, lem1b, lem2]
   val tac5 =
      abs_diff_tac abs_diff2a
      >- (match_mp_tac abs_diff2a \\ simp [subnormal_lt_normal])
      \\ t1
      \\ simp [REAL_OF_NUM_POW]
      \\ match_mp_tac lem3b
      \\ simp [REAL_LE_MUL, REAL_OF_NUM_POW,
               fcpTheory.DIMINDEX_GE_1, word_lt0, not_max_suc_lt_dimword,
               lem1b, lem2, word_ge1, w2n_lt_pow]
   val tac6 =
      tac abs_diff1b `(x: ('t, 'w) float).Significand`
      \\ match_mp_tac (REAL_ARITH ``a < b /\ 0r <= c ==> a < b + c``)
      \\ simp [REAL_LE_MUL, GSYM REAL_LT_SUB_LADD]
      \\ once_rewrite_tac
           [REAL_ARITH
               ``p * (a * 2r) * x - (a * x + a * y) =
                 a * ((p * (2 * x)) - (x + y))``]
      \\ match_mp_tac (ONCE_REWRITE_RULE [REAL_MUL_COMM] gt_mult)
      \\ simp []
      \\ match_mp_tac weaken_lt
      \\ simp [POW_2_LE1, REAL_LT_MUL,
               REAL_ARITH ``2r * a - (a + z) = a - z``]
      \\ simp [GSYM REAL_LT_ADD_SUB, not_max_suc_lt_dimword,
               REAL_OF_NUM_POW, Abbr `z`]
   val tac7 =
      tac abs_diff2b `(y: ('t, 'w) float).Significand`
      \\ once_rewrite_tac
           [REAL_LT_RDIV
            |> Q.SPECL [`x`, `y`, `2 pow w2n (y:('t, 'w) float).Exponent`]
            |> SIMP_RULE (srw_ss()) []
            |> GSYM]
      \\ simp [GSYM REAL_DIV_ADD, GSYM REAL_ADD_LDISTRIB,
               cancel_rwts]
      \\ rsimp [REAL_OF_NUM_POW, Abbr `z`]
      \\ match_mp_tac lem4b
      \\ REV_FULL_SIMP_TAC (srw_ss()) [w2n_lt_pow, word_lt0, lem5]
end

Theorem diff_exponent_ULP[local]:
  !x: ('t, 'w) float y: ('t, 'w) float.
    (x.Sign = y.Sign) /\ x.Exponent <> y.Exponent /\
    ~exponent_boundary y x ==>
    ULP (x.Exponent, (:'t)) <= abs (float_to_real x - float_to_real y)
Proof
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
QED

Theorem diff_exponent_ULP_gt[local]:
  !x: ('t, 'w) float y: ('t, 'w) float.
    (x.Sign = y.Sign) /\ x.Exponent <> y.Exponent /\
    x.Significand NOTIN {0w; -1w} ==>
    ULP (x.Exponent, (:'t)) < abs (float_to_real x - float_to_real y)
Proof
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
QED

val lem = Q.prove(
   `!a b m. 2n <= a /\ 2 <= b /\ 1 <= m ==> a * b + b < 2 * (m * a * b)`,
   REPEAT strip_tac
   \\ imp_res_tac arithmeticTheory.LESS_EQUAL_ADD
   \\ simp [arithmeticTheory.LEFT_ADD_DISTRIB]
   )

Theorem diff_exponent_ULP_gt0[local]:
  !x: ('t, 'w) float y: ('t, 'w) float.
    (x.Sign = y.Sign) /\ x.Exponent <+ y.Exponent /\
    (x.Significand = 0w) /\ ~float_is_zero x ==>
    ULP (x.Exponent, (:'t)) < abs (float_to_real x - float_to_real y)
Proof
   rw [ULP_def, float_to_real_def, ABS_NEG, abs_float_value,
       abs_significand, ABS_MUL, ABS_DIV,
       ABS_N, gt0_abs, wordsTheory.WORD_LO]
   >- rfs [REAL_LT_LDIV_EQ, POW_ADD,
           REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB,
           REAL_LT_SUB_LADD, cancel_rwts, cancel_rwt, float_is_zero]
   \\ abs_diff_tac abs_diff1f
   >- (match_mp_tac abs_diff1f
       \\ simp [REAL_LT_LDIV_EQ, REAL_ADD_LDISTRIB,
                cancel_rwts]
       \\ simp [REAL_OF_NUM_POW, REAL_LE_MUL,
                REAL_ARITH ``a < b /\ 0 <= c ==> a < b + c: real``])
   \\ simp [REAL_LT_LDIV_EQ, POW_ADD,
            REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB,
            REAL_LT_SUB_LADD, cancel_rwts, cancel_rwt]
   \\ match_mp_tac (REAL_ARITH ``a < b /\ 0r <= c ==> a < b + c``)
   \\ simp [REAL_LE_MUL, REAL_OF_NUM_POW]
   \\ imp_res_tac arithmeticTheory.LESS_ADD_1
   \\ simp [arithmeticTheory.EXP_ADD, lem, fcpTheory.DIMINDEX_GE_1, exp_ge4,
            word_ge1]
QED

val lem = Q.prove(
   `!a b. 2 <= a /\ 4n <= b ==> 2 * a + 2 < a * b`,
   not_next_tac
   )

Theorem diff_exponent_ULP_gt01[local]:
  !x: ('t, 'w) float y: ('t, 'w) float.
    (x.Sign = y.Sign) /\ x.Exponent <> y.Exponent /\
    y.Significand <> -1w  /\ (x.Significand = 0w) /\ (x.Exponent = 1w) ==>
    ULP (x.Exponent, (:'t)) < abs (float_to_real x - float_to_real y)
Proof
   rw [ULP_def, float_to_real_def, ABS_NEG, abs_float_value,
       abs_significand, ABS_MUL, ABS_DIV,
       ABS_N, gt0_abs, nobias_denormal_lt_1,
       REAL_ARITH ``a - a * b = a * (1 - b): real``,
       REAL_ARITH ``a < 1 ==> (abs (1 - a) = 1 - a)``]
   >- (simp [REAL_LT_LDIV_EQ, POW_ADD, cancel_rwts,
             REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB,
             REAL_LT_SUB_LADD]
       \\ rewrite_tac [simpLib.SIMP_PROVE (srw_ss()++ARITH_ss) []
                         ``&(2n * n + 2) = 2r * &(n + 1)``]
       \\ simp [REAL_LT_LMUL, REAL_OF_NUM_POW,
                not_max_suc_lt_dimword])
   \\ `1w <+ y.Exponent`
   by metis_tac
        [wordsLib.WORD_DECIDE ``a:'a word <> 0w /\ a <> 1w ==> 1w <+ a``]
   \\ fs [wordsTheory.WORD_LO]
   \\ abs_diff_tac abs_diff1e
   >- (match_mp_tac abs_diff1e
       \\ simp [REAL_LT_LDIV_EQ, REAL_LDISTRIB,
                cancel_rwts, cancel_rwt]
       \\ match_mp_tac (REAL_ARITH ``a < b /\ 0r <= c ==> a < b + c``)
       \\ simp [REAL_LE_MUL, REAL_OF_NUM_POW])
   \\ simp [REAL_LT_LDIV_EQ, POW_ADD,
            REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB,
            REAL_LT_SUB_LADD, cancel_rwts, cancel_rwt]
   \\ match_mp_tac (REAL_ARITH ``a < b /\ 0r <= c ==> a < b + c``)
   \\ simp [REAL_LE_MUL, REAL_OF_NUM_POW, lem,
            fcpTheory.DIMINDEX_GE_1, exp_ge4]
QED

val lem = Q.prove(
   `!a b c. a < b /\ 2n <= c ==> 2 * a < b * c`,
   not_next_tac
   )

val lem2 = Q.prove(
   `!a b c. a < b /\ 1n <= c ==> a + b < 2 * (c * b)`,
   not_next_tac
   )

Theorem float_to_real_lt_exponent_mono[local]:
  !x: ('t, 'w) float y: ('t, 'w) float.
    (x.Sign = y.Sign) /\ abs (float_to_real x) <= abs (float_to_real y) ==>
    x.Exponent <=+ y.Exponent
Proof
  rw [float_to_real_def, ABS_NEG, abs_float_value,
      abs_significand, ABS_MUL, ABS_DIV,
      ABS_N, gt0_abs, wordsTheory.WORD_LS]
   >| [
      Cases_on `x.Sign = y.Sign`
      \\ simp [REAL_NOT_LE]
      \\ once_rewrite_tac
           [REAL_LT_RMUL
            |> Q.SPECL [`x`, `y`, `2 pow bias (:'w)`]
            |> REWRITE_RULE [zero_lt_twopow]
            |> GSYM]
      \\ rewrite_tac [cancel_rwts, cancel_rwt]
      \\ simp [REAL_LDISTRIB, REAL_RDISTRIB,
               REAL_OF_NUM_POW, REAL_DIV_RMUL,
               REAL_LT_LDIV_EQ, mult_ratr,
               cancel_rwts, cancel_rwt, w2n_lt_pow,
               word_ge1, lem, DECIDE ``a < b ==> a < x + b: num``],
      (* --- *)
      pop_assum mp_tac
      \\ Cases_on `w2n x.Exponent <= w2n y.Exponent`
      \\ simp [REAL_NOT_LE]
      \\ fs [arithmeticTheory.NOT_LESS_EQUAL]
      \\ once_rewrite_tac
           [REAL_LT_RMUL
            |> Q.SPECL [`x`, `y`, `2 pow bias (:'w)`]
            |> REWRITE_RULE [zero_lt_twopow]
            |> GSYM]
      \\ rewrite_tac [cancel_rwts, cancel_rwt]
      \\ once_rewrite_tac
           [REAL_LT_RMUL
            |> Q.SPECL [`x`, `y`, `2 pow precision (:'t)`]
            |> REWRITE_RULE [zero_lt_twopow]
            |> GSYM]
      \\ rewrite_tac [cancel_rwts, cancel_rwt]
      \\ simp [REAL_OF_NUM_POW]
      \\ match_mp_tac (DECIDE ``a < b ==> a < x + b: num``)
      \\ imp_res_tac arithmeticTheory.LESS_ADD_1
      \\ asm_simp_tac bool_ss
             [arithmeticTheory.EXP_ADD, arithmeticTheory.LT_MULT_RCANCEL,
              GSYM arithmeticTheory.RIGHT_ADD_DISTRIB,
              DECIDE ``a * (b * (c * d)) = (a * c * d) * b: num``]
      \\ simp [lem2, w2n_lt_pow]
   ]
QED

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

fun tac thm =
   abs_diff_tac thm
   >- (match_mp_tac thm
       \\ simp [REAL_LT_LMUL, REAL_LT_DIV,
                REAL_LT_LDIV_EQ, REAL_DIV_RMUL])
   \\ simp [REAL_ARITH ``a < b ==> (abs (a - b) = b - a)``,
            REAL_ARITH ``b < a ==> (abs (a - b) = a - b)``,
            REAL_SUB_RDISTRIB, REAL_LDISTRIB,
            POW_ADD, mult_rat]
   \\ simp [mult_ratr]

fun tac2 thm =
   abs_diff_tac thm
   >- (match_mp_tac thm
       \\ simp [REAL_LT_LMUL, REAL_LT_DIV,
                REAL_LT_LDIV_EQ, REAL_DIV_RMUL])
   \\ simp [REAL_ARITH ``a < b ==> (abs (a - b) = b - a)``,
            REAL_ARITH ``b < a ==> (abs (a - b) = a - b)``,
            REAL_ARITH ``1 + a - (1 + b) = a - b: real``,
            GSYM REAL_SUB_LDISTRIB, sub_rat_same_base]
   \\ simp [POW_ADD, mult_rat]
   \\ simp_tac (srw_ss()++realSimps.real_ac_SS) [mult_ratr]

Theorem diff_significand_ULP_mul[local]:
    !x: ('t, 'w) float y: ('t, 'w) float.
        (x.Sign = y.Sign) /\ (x.Exponent = y.Exponent) ==>
        (abs (float_to_real x - float_to_real y) =
         abs (&w2n x.Significand - &w2n y.Significand) *
         ULP (x.Exponent, (:'t)))
Proof
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
QED

val diff_ge1 = Q.prove(
   `!a b. 1 <= abs (&a - &b) <=> &a <> (&b: real)`,
   lrw [REAL_SUB, ABS_NEG, ABS_N]
   )

Theorem diff_significand_ULP[local]:
    !x: ('t, 'w) float y: ('t, 'w) float.
        (x.Sign = y.Sign) /\ (x.Exponent = y.Exponent) /\
        x.Significand <> y.Significand ==>
        ULP (x.Exponent, (:'t)) <= abs (float_to_real x - float_to_real y)
Proof
   rw [diff_significand_ULP_mul, ULP_gt0, diff_ge1,
       ONCE_REWRITE_RULE [REAL_MUL_COMM] le_mult]
QED

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

val ULP_same = Q.prove(
   `!x y.
      (x = y) ==>
      ~(ULP (x.Exponent, (:'t)) <= abs (float_to_real x - float_to_real y))`,
   rrw [ULP_gt0, REAL_NOT_LE])

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
       \\ rfs [ULP_gt0, REAL_POS_NZ])
   \\metis_tac [diff_exponent_ULP, ULP_same]
   )

Theorem float_to_real_eq:
    !x: ('t, 'w) float y: ('t, 'w) float.
       (float_to_real x = float_to_real y) <=>
       (x = y) \/ (float_is_zero x /\ float_is_zero y)
Proof
   NTAC 2 strip_tac
   \\ Cases_on `x = y`
   \\ simp []
   \\ Cases_on `float_is_zero x /\ float_is_zero y`
   \\ simp [float_is_zero_to_real_imp]
   \\ Cases_on `x.Sign <> y.Sign`
   >- metis_tac [diff_sign_neq]
   \\ Cases_on `x.Exponent <> y.Exponent`
   >- metis_tac [diff_exponent_neq]
   \\ qpat_x_assum `~(p /\ q)` kall_tac
   \\ fs [float_component_equality]
   \\ rw [float_to_real_def, sign_not_zero, div_twopow]
QED

val diff_float_ULP = Q.store_thm("diff_float_ULP",
   `!x: ('t, 'w) float y: ('t, 'w) float.
       float_to_real x <> float_to_real y /\ ~exponent_boundary y x ==>
       ULP (x.Exponent, (:'t)) <= abs (float_to_real x - float_to_real y)`,
   rw [float_to_real_eq, float_component_equality]
   \\ metis_tac [diff_sign_ULP, diff_exponent_ULP, diff_significand_ULP])

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

(* |- !x y. ~float_is_zero y ==>
            ((float_to_real x = float_to_real y) <=> (x = y)) *)
Theorem float_to_real_11_right[local] =
   float_to_real_eq
   |> Drule.SPEC_ALL
   |> Q.DISCH `~float_is_zero y`
   |> SIMP_RULE bool_ss []
   |> Q.GENL [`x`, `y`]

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

Theorem diff1pos[local]:
  !a. a <> 0w ==> (&w2n a - &w2n (a + -1w) = 1r)
Proof
   Cases
   \\ Cases_on `n`
   \\ simp [wordsTheory.n2w_SUC]
   \\ rrw [REAL_SUB, bitTheory.SUC_SUB, DECIDE ``~(SUC n <= n)``]
QED

Theorem diff1neg[local]:
  !a. a <> -1w ==> (&w2n a - &w2n (a + 1w) = -1r)
Proof
   rw [REAL_SUB, bitTheory.SUC_SUB, DECIDE ``~(SUC n <= n)``,
       GSYM wordsTheory.WORD_LS,
       ONCE_REWRITE_RULE [GSYM wordsTheory.WORD_ADD_COMM]
          wordsTheory.WORD_ADD_RIGHT_LS2]
   \\ lfs [wordsTheory.WORD_NOT_LOWER, wordsTheory.WORD_LS_word_T]
   \\ `a <=+ a + 1w` by wordsLib.WORD_DECIDE_TAC
   \\ simp [GSYM wordsTheory.word_sub_w2n]
QED

Theorem must_be_1[local]:
  !a b: real. 0 < b ==> ((a * b = b) = (a = 1))
Proof
   REPEAT strip_tac
   \\ Cases_on `a = 1`
   >- simp []
   \\ Cases_on `a < 1`
   >- rsimp [REAL_LT_IMP_NE,
             ONCE_REWRITE_RULE [REAL_MUL_COMM] lt_mult]
   \\ `1 < a` by rsimp []
   \\ simp [REAL_LT_IMP_NE, gt_mult]
QED

Theorem w2n_add1[local]:
  !a. a <> -1w ==> (w2n a + 1 = w2n (a + 1w))
Proof
   Cases
   \\ lrw [wordsTheory.word_eq_n2w, wordsTheory.word_add_n2w,
           bitTheory.MOD_2EXP_MAX_def, bitTheory.MOD_2EXP_def,
           GSYM wordsTheory.dimword_def]
QED

Theorem diff_ulp_next_float[local]:
   !x y: ('t, 'w) float.
       ~float_is_zero x /\ y.Significand NOTIN {0w; -1w} ==>
       ((abs (float_to_real y - float_to_real x) = ULP (y.Exponent,(:'t))) <=>
        (x = y with Significand := y.Significand - 1w) \/
        (x = y with Significand := y.Significand + 1w))
Proof
   REPEAT strip_tac
   \\ eq_tac
   >| [
      `~float_is_zero y` by fs [float_is_zero]
      \\ Cases_on `x.Sign <> y.Sign`
      >- prove_tac [REAL_LT_IMP_NE, diff_sign_ULP_gt]
      \\ Cases_on `x.Exponent <> y.Exponent`
      >- prove_tac [REAL_LT_IMP_NE, diff_exponent_ULP_gt]
      \\ fs [diff_significand_ULP_mul, must_be_1, ULP_gt0,
             float_component_equality]
      \\ Cases_on `x.Significand = y.Significand + -1w`
      \\ simp []
      \\ Cases_on `x.Significand = y.Significand + 1w`
      \\ rsimp [REAL_ARITH ``(abs x = 1) <=> (x = 1) \/ (x = -1)``,
                REAL_ARITH ``(a = -1 + c) = (c = a + 1r)``,
                REAL_EQ_SUB_RADD, w2n_add1]
      \\ Cases_on `x.Significand = -1w`
      \\ simp [ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM] w2n_add1,
               wordsTheory.w2n_minus1, DECIDE ``0n < n ==> (1 + (n - 1) = n)``,
               wordsTheory.w2n_lt, prim_recTheory.LESS_NOT_EQ,
               wordsLib.WORD_ARITH_PROVE
                  ``a:'a word <> b + -1w ==> b <> a + 1w``],
      (* --- *)
      rw []
      \\ rw [float_to_real_def, abs_float_value, abs_significand,
             ABS_MUL, ABS_DIV, ABS_N,
             gt0_abs, GSYM REAL_SUB_LDISTRIB, sub_rat_same_base,
             REAL_ARITH ``1r + a - (1 + b) = a - b``]
      \\ fs [diff1pos, diff1neg, mult_rat, ULP_def,
             POW_ADD]
   ]
QED

Theorem diff_ulp_next_float0[local]:
  !x y: ('t, 'w) float.
    ~float_is_zero x /\ ~float_is_zero y /\ (y.Significand = 0w) /\
    abs (float_to_real y) <= abs (float_to_real x) ==>
    ((abs (float_to_real y - float_to_real x) = ULP (y.Exponent,(:'t))) =
     (x = y with Significand := y.Significand + 1w))
Proof
   REPEAT strip_tac
   \\ eq_tac
   >| [
      Cases_on `x.Sign <> y.Sign`
      >- prove_tac [REAL_LT_IMP_NE, diff_sign_ULP_gt]
      \\ imp_res_tac float_to_real_lt_exponent_mono
      \\ Cases_on `x.Exponent <> y.Exponent`
      >- prove_tac
            [REAL_LT_IMP_NE, diff_exponent_ULP_gt0,
             wordsLib.WORD_DECIDE ``a <> b /\ a <=+ b ==> a <+ b:'a word``]
      \\ fs [diff_significand_ULP_mul, must_be_1, ULP_gt0,
             float_component_equality, ABS_NEG, ABS_N]
      \\ Cases_on `x.Significand`
      \\ simp [],
      (* --- *)
      rw []
      \\ rw [float_to_real_def, abs_float_value, abs_significand,
             ABS_MUL, ABS_DIV, ABS_N,
             ABS_NEG, gt0_abs, REAL_LDISTRIB,
             REAL_ARITH ``a - (a + c) = -c: real``]
      \\ fs [diff1pos, diff1neg, mult_rat, ULP_def,
             POW_ADD]
   ]
QED

Theorem diff_ulp_next_float01[local]:
  !x y: ('t, 'w) float.
    ~float_is_zero x /\ ~float_is_zero y /\
    x.Significand <> -1w /\ (y.Significand = 0w) /\ (y.Exponent = 1w) ==>
    ((abs (float_to_real y - float_to_real x) = ULP (y.Exponent,(:'t))) =
     (x = y with Significand := y.Significand + 1w))
Proof
   REPEAT strip_tac
   \\ eq_tac
   >| [
      Cases_on `x.Sign <> y.Sign`
      >- prove_tac [REAL_LT_IMP_NE, diff_sign_ULP_gt]
      \\ Cases_on `x.Exponent <> y.Exponent`
      >- prove_tac [REAL_LT_IMP_NE, diff_exponent_ULP_gt01]
      \\ fs [diff_significand_ULP_mul, must_be_1, ULP_gt0,
             float_component_equality, ABS_NEG, ABS_N]
      \\ Cases_on `x.Significand`
      \\ simp [],
      (* --- *)
      rw []
      \\ rw [float_to_real_def, abs_float_value, abs_significand,
             ABS_MUL, ABS_DIV, ABS_N,
             ABS_NEG, gt0_abs, REAL_LDISTRIB,
             REAL_ARITH ``a - (a + c) = -c: real``]
      \\ fs [diff1pos, diff1neg, mult_rat, ULP_def,
             POW_ADD]
   ]
QED

Theorem float_min_equiv_ULP_eq_float_to_real[local]:
  !y: ('t, 'w) float.
    (abs (float_to_real y) = ULP (y.Exponent,(:'t))) <=>
    y IN {float_plus_min (:'t # 'w); float_minus_min (:'t # 'w)}
Proof
   strip_tac
   \\ Cases_on `float_is_zero y`
   >- fs [float_sets, zero_to_real, float_components, float_distinct,
          GSYM float_distinct, ULP_gt0,
          REAL_ARITH ``0 < b ==> 0r <> b``]
   \\ Cases_on `(y = float_plus_min (:'t # 'w)) \/
                (y = float_minus_min (:'t # 'w))`
   >- rw [GSYM neg_ulp, GSYM ulp, float_minus_min_def, float_components,
          ulp_def, ULP_gt0, gt0_abs, REAL_LT_IMP_LE,
          ABS_NEG]
   \\ fs []
   \\ rw [float_to_real_def, ULP_def, abs_float_value, abs_significand,
          ABS_MUL, ABS_DIV, ABS_N, gt0_abs,
          REAL_EQ_RDIV_EQ]
   \\ simp [POW_ADD, GSYM REAL_LDISTRIB,
            cancel_rwts, cancel_rwt, REAL_DIV_REFL,
            REAL_EQ_RDIV_EQ
            |> ONCE_REWRITE_RULE [GSYM REAL_MUL_COMM]
            |> GSYM]
   >| [
      strip_tac
      \\ `y.Significand = 1w`
      by metis_tac [wordsTheory.w2n_11, wordsTheory.word_1_n2w]
      \\ fs [float_plus_min_def, float_minus_min_def, float_negate_def,
             float_component_equality]
      \\ metis_tac [sign_inconsistent],
      simp [REAL_OF_NUM_POW, GSYM wordsTheory.dimword_def,
            DECIDE ``1 < a ==> a + b <> 1n``]
   ]
QED

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

val tac =
   REPEAT strip_tac
   \\ spose_not_then assume_tac
   \\ `float_to_real a <> float_to_real b`
   by metis_tac [float_to_real_eq]
   \\ imp_res_tac diff_float_ULP
   \\ rlfs []

Theorem diff_lt_ulp_eq0:
    !a: ('t, 'w) float b: ('t, 'w) float x.
       ~exponent_boundary b a /\
       abs (x - float_to_real a) < ULP (a.Exponent, (:'t)) /\
       abs (x - float_to_real b) < ULP (a.Exponent, (:'t)) /\
       abs (float_to_real a) <= abs x /\ abs (float_to_real b) <= abs x /\
       ~float_is_zero a ==>
       (b = a)
Proof tac
QED

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

Theorem exponent_boundary_lt[local]:
    !a b.
      exponent_boundary a b ==> abs (float_to_real a) < abs (float_to_real b)
Proof
   rrw [float_to_real_def, exponent_boundary_def, abs_float_value,
        abs_significand, ABS_MUL, ABS_DIV,
        ABS_N, gt0_abs]
   >- (match_mp_tac lt_mult
       \\ rsimp [nobias_denormal_lt_1, REAL_LT_DIV])
   \\ simp [REAL_LT_LMUL, REAL_LT_RDIV_EQ, cancel_rwts,
            POW_ADD, REAL_ARITH ``1 + x < 2 <=> x < 1r``,
            nobias_denormal_lt_1]
QED

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
       ABS_MUL, ABS_DIV, ABS_N,
       gt0_abs, REAL_LE_LDIV_EQ, float_is_zero, GSYM word_lt0]
   \\ simp [POW_ADD, cancel_rwt, cancel_rwts]
   \\ simp [GSYM REAL_LDISTRIB, POW_2_LE1,
            le_mult, REAL_ARITH ``1r <= x /\ 0 <= n ==> 1 <= x + n``]
   )

(* |- !y. ~float_is_zero y ==> ulp (:'t # 'w) <= abs (float_to_real y) *)
val ulp_lt_float_to_real =
   diff_float_ULP
   |> Q.SPEC `float_plus_zero (:'t # 'w)`
   |> SIMP_RULE (srw_ss())
         [ABS_NEG, float_components, zero_to_real, zero_properties,
          exponent_boundary_def, GSYM ulp_def, GSYM float_is_zero_to_real]

val abs_limits = REAL_ARITH ``!x l. abs x <= l <=> ~(x < -l) /\ ~(x > l)``

val abs_limits2 =
   REAL_ARITH ``!x l. abs x < l <=> ~(x <= -l) /\ ~(x >= l)``

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
               (REAL_ARITH
                   ``abs (a - x) < abs x /\ abs b < abs a /\ abs a <= abs x ==>
                     abs (a - x) <= abs (b - x)``)
          \\ rsimp [exponent_boundary_lt])
      \\ match_mp_tac
            (REAL_ARITH
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
          by (qpat_x_assum `float_is_zero y` mp_tac \\ simp [float_is_zero])
          \\ rlfs [ulp_def]
          \\ metis_tac [REAL_ARITH ``~(x < b /\ b <= x: real)``]
         )
      \\ imp_res_tac Float_float_to_real
      \\ pop_assum (SUBST_ALL_TAC o SYM)
      \\ `abs (float_to_real x' - x) <= abs (float_to_real y - x)`
      by metis_tac [Float_is_finite]
      \\ `abs (x - float_to_real x') < ULP (y.Exponent, (:'t))`
      by metis_tac [REAL_LET_TRANS, ABS_SUB]
      \\ Cases_on `exponent_boundary x' y`
      >- (
          `ULP (y.Exponent,(:'t)) <= abs (float_to_real y)`
          by metis_tac [ULP_lt_float_to_real, exponent_boundary_not_float_zero]
          \\ `abs (float_to_real y - x) <= abs (float_to_real x' - x)`
          by (match_mp_tac
               (REAL_ARITH
                   ``abs (a - x) < abs x /\ abs b < abs a /\ abs a <= abs x ==>
                     abs (a - x) <= abs (b - x)``)
              \\ rsimp [exponent_boundary_lt]
             )
          \\ simp [GSYM float_to_real_11_right]
          \\ match_mp_tac
               (REAL_ARITH
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
   \\ lrw [ULP_def, wordsTheory.word_lo_n2w, REAL_LT_RDIV]
   \\ simp [REAL_OF_NUM_POW]
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
   qpat_x_assum `!a. q \/ t` (qspec_then `y` strip_assume_tac)
   \\ fs [REAL_NOT_LE]
   \\ qpat_x_assum `!b. p` (qspec_then `b` imp_res_tac)
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
        SPECIFICATION]
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
           by imp_res_tac REAL_LE_TRANS
           \\ match_mp_tac
                (REAL_ARITH
                    ``abs b < abs a /\ abs a <= abs x /\
                      2 * abs (a - x) <= abs a ==> abs (a - x) <= abs (b - x)``)
           \\ rlfs [exponent_boundary_def]
           )
         \\ metis_tac
               [diff_float_ULP,
                REAL_ARITH
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
              [REAL_ARITH
                  ``2 * abs (r - x) < u /\ u <= abs (r - a) ==>
                    ~(abs (a - x) <= abs (r - x))``]
      ],
      (* -- *)
      `float_is_finite y` by simp [Float_is_finite]
      \\ Cases_on `float_is_zero y`
      >- (`r = 0` by (pop_assum mp_tac \\ simp [float_is_zero_def])
          \\ `y.Exponent = 0w`
          by (qpat_x_assum `float_is_zero y` mp_tac \\ simp [float_is_zero])
          \\ rlfs [ulp_def]
          \\ metis_tac [ULP_gt0,
                REAL_ARITH ``~(0 < x /\ x < b /\ 2 * b <= x: real)``])
      \\ imp_res_tac Float_float_to_real
      \\ pop_assum (SUBST_ALL_TAC o SYM)
      \\ Cases_on `exponent_boundary x' y`
      >- (`abs (float_to_real y) <= abs x` by fs [exponent_boundary_def]
          \\ metis_tac
               [REAL_LE_TRANS, exponent_boundary_lt,
                ULP_lt_float_to_real,
                REAL_ARITH
                  ``~(2 * abs (a - x) <= abs a /\ abs a <= abs x /\
                      abs b < abs a /\ abs (b - x) <= abs (a - x))``])
      \\ Cases_on `2 * abs (float_to_real y - x) < ULP (y.Exponent,(:'t))`
      >- (`2 * abs (float_to_real x' - x) <= 2 * abs (float_to_real y - x)`
          by metis_tac [Float_is_finite,
               REAL_ARITH ``2 * abs a <= 2 * abs b <=> abs a <= abs b``]
          \\ metis_tac [REAL_LET_TRANS, diff_lt_ulp_even])
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
           [REAL_ARITH
               ``(2 * abs (a - x) = u) /\ u <= abs (a - b) /\
                 abs (b - x) <= abs (a - x) ==> (abs (a - b) = u)``]
      \\ `y.Significand <> -1w` by (strip_tac \\ fs [])
      \\ `~float_is_zero x'`
      by (strip_tac
          \\ imp_res_tac float_is_zero_to_real
          \\ fs [float_min_equiv_ULP_eq_float_to_real]
          \\ fs [float_components])
      \\ Cases_on `y.Significand = 0w`
      >- (qpat_x_assum `~float_is_zero y` assume_tac
          \\ `x'.Significand <> -1w` by (strip_tac \\ fs [] \\ tac)
          \\ Cases_on `y.Exponent = 1w`
          >- (fs [diff_ulp_next_float01] \\ tac)
          \\ Cases_on `abs (float_to_real x') < abs (float_to_real y)`
          \\ fs [REAL_NOT_LT]
          >- metis_tac
               [REAL_LE_TRANS, ULP_lt_float_to_real,
                REAL_ARITH
                  ``~(2 * abs (a - x) <= abs a /\ abs a <= abs x /\
                      abs b < abs a /\ abs (b - x) <= abs (a - x))``]
          \\ `abs (float_to_real x' - x) = abs (float_to_real y - x)`
          by imp_res_tac
               (REAL_ARITH
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
val pow_add1 = REWRITE_RULE [arithmeticTheory.ADD1] pow

val exponent_boundary_ULPs = Q.prove(
   `!x y. exponent_boundary x y ==>
          (ULP (y.Exponent, (:'t)) = 2 * ULP (x.Exponent, (:'t)))`,
   srw_tac [] [exponent_boundary_def, ULP_def, pow_add1, mult_ratr]
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
        SPECIFICATION]
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
            \\ rw [pow_add1, mult_ratr]
            \\ fs [not_one_lem])
        \\ match_mp_tac
             (REAL_ARITH
                ``~(abs a <= abs x) /\ 4 * abs (a - x) <= 2 * abs (a - b) ==>
                  abs (a - x) <= abs (b - x)``)
        \\ simp []
        )
      \\ metis_tac
            [diff_float_ULP,
             REAL_ARITH ``4 * abs (r - x) <= u /\ u <= abs (r - b) ==>
                                  abs (r - x) <= abs (b - x)``],
      (* -- *)
      `float_is_finite y` by simp [Float_is_finite]
      \\ Cases_on `float_is_zero y`
      >- (`r = 0` by (pop_assum mp_tac \\ simp [float_is_zero_def])
          \\ `y.Exponent = 0w`
          by (qpat_x_assum `float_is_zero y` mp_tac \\ simp [float_is_zero])
          \\ rlfs [ulp_def])
      \\ imp_res_tac Float_float_to_real
      \\ pop_assum (SUBST_ALL_TAC o SYM)
      \\ `abs (float_to_real x' - x) <= abs (float_to_real y - x)` by res_tac
      \\ `4 * abs (float_to_real x' - x) <= 4 * abs (float_to_real y - x)`
      by rsimp []
      \\ `4 * abs (float_to_real x' - x) <= ULP (y.Exponent,(:'t))`
      by metis_tac [REAL_LE_TRANS]
      \\ match_mp_tac diff_lt_ulp_even4
      \\ qexists_tac `x`
      \\ simp []
      \\ spose_not_then assume_tac
      \\ imp_res_tac exponent_boundary_ULPs
      \\ fs [REAL_ARITH ``4r * a <= 2 * b <=> 2 * a <= b``]
      \\ imp_res_tac diff_exponent_boundary
      \\ `abs (float_to_real x' - x) = abs (float_to_real y - x)`
      by metis_tac
           [REAL_ARITH
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
   tac (REAL_ARITH
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
   tac (REAL_ARITH
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
       \\ qpat_x_assum `float_is_zero y` mp_tac
       \\ rw [float_is_zero]
       \\ fs [ulp_def]
       \\ prove_tac [REAL_ARITH ``~(x < b /\ b <= x: real)``,
                     REAL_ARITH ``2 * abs (-x) <= u ==> abs x <= u``]
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
      \\ simp [zero_properties, zero_to_real, ABS_POS,
               ABS_NEG]
      \\ REPEAT strip_tac
      \\ imp_res_tac REAL_LET_TRANS
      \\ imp_res_tac less_than_ulp
      \\ Cases_on `b`
      \\ lfs [float_to_real_def, ABS_NEG],
      (* -- *)
      imp_res_tac REAL_LET_TRANS
      \\ imp_res_tac less_than_ulp
      \\ Cases_on `r`
      \\ lfs [float_plus_zero_def, float_minus_zero_def, float_negate_def,
              float_component_equality]
      \\ wordsLib.Cases_on_word_value `c`
      \\ simp []
   ])

Theorem is_closest_finite_AND:
  is_closest float_is_finite r f /\ Q f ==>
  is_closest { a | float_is_finite a /\ Q a} r f
Proof
  simp[is_closest_def, IN_DEF]
QED

Theorem float_to_real_round0[simp]:
  float_to_real (round m 0) = 0
Proof
  Cases_on ‘m’ >>
  simp[round_def,
       SRULE [ulp_positive] (Q.SPEC ‘0’ lt_ulp_not_infinity0),
       SRULE [ulp_positive] (Q.SPEC ‘0’ lt_ulp_not_infinity1),
       closest_such_def, closest_def] >>
  SELECT_ELIM_TAC >>
  dsimp[is_closestP_finite_float_exists, is_closest_float_is_finite_0] >>
  qexists_tac ‘POS0’ >>
  simp[is_closest_finite_AND, is_closest_float_is_finite_0] >>
  simp[is_closest_def] >> rpt strip_tac >>
  first_x_assum $ qspec_then ‘POS0’ mp_tac >> gs[REAL_ABS_LE0]
QED

val float_to_real_min_pos = Q.prove(
   `!r: ('t, 'w) float.
       (abs (float_to_real r) = ulp (:'t # 'w)) <=>
       r IN {float_plus_min (:'t # 'w);
             float_negate (float_plus_min (:'t # 'w))}`,
   rw [float_plus_min_def, float_negate_def, ulp_def, ULP_def,
       float_to_real_def, float_component_equality, abs_float_value,
       abs_significand, ABS_MUL, ABS_DIV,
       ABS_N, gt0_abs]
   >| [
      wordsLib.Cases_on_word_value `r.Sign`
      \\ Cases_on `r.Significand = 1w`
      \\ simp [mult_rat, POW_ADD,
               div_twopow
               |> Q.SPEC `m + n`
               |> REWRITE_RULE [POW_ADD]
               |> Drule.GEN_ALL]
      \\ Cases_on `r.Significand`
      \\ fs [],
      simp [REAL_EQ_RDIV_EQ]
      \\ simp [POW_ADD, GSYM REAL_LDISTRIB,
               cancel_rwts, cancel_rwt]
      \\ match_mp_tac (REAL_ARITH ``2r < a * b ==> b * a <> 2``)
      \\ match_mp_tac ge2d
      \\ simp [REAL_OF_NUM_POW, pow_ge2, exp_ge2,
               DECIDE ``2n <= a ==> 2 <= b + a``,
               fcpTheory.DIMINDEX_GE_1 ]
   ])

val compare_with_zero_tac =
   qpat_x_assum `!b. float_is_finite b  ==> p`
      (fn th =>
         assume_tac
            (SIMP_RULE (srw_ss())
               [ABS_NEG, zero_to_real, zero_properties]
                  (Q.SPEC `float_plus_zero (:'t # 'w)` th))
         \\ assume_tac th)

Theorem half_ulp[local]:
  !x r: ('t, 'w) float.
    (2 * abs x = ulp (:'t # 'w)) /\
    (!b: ('t, 'w) float.
       float_is_finite b ==>
       abs (float_to_real r - x) <= abs (float_to_real b - x)) ==>
    float_is_zero r \/
    r IN {float_plus_min (:'t # 'w);
          float_negate (float_plus_min (:'t # 'w))}
Proof
   REPEAT strip_tac
   \\ Cases_on `float_is_zero r`
   \\ simp []
   \\ compare_with_zero_tac
   \\ `abs (float_to_real r) = ulp (:'t # 'w)`
   by metis_tac
         [ulp_lt_float_to_real,
          REAL_ARITH
           ``(2 * abs x = u) /\ u <= abs r /\ abs (r - x) <= abs x ==>
             (abs r = u)``]
   \\ fs [float_to_real_min_pos]
QED

Theorem min_pos_odd[local]:
  !r: ('t, 'w) float.
    r IN {float_plus_min (:'t # 'w);
          float_negate (float_plus_min (:'t # 'w))} ==>
    word_lsb r.Significand
Proof rw [float_plus_min_def, float_negate_def] \\ simp []
QED

val round_roundTiesToEven_is_zero = Q.store_thm("round_roundTiesToEven_is_zero",
   `!x. 2 * abs x <= ulp (:'t # 'w) ==>
        (round roundTiesToEven x = float_plus_zero (:'t # 'w)) \/
        (round roundTiesToEven x = float_minus_zero (:'t # 'w))`,
   REPEAT strip_tac
   \\ qabbrev_tac `r: ('t, 'w) float = round roundTiesToEven x`
   \\ pop_assum (mp_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def])
   \\ simp [round_def, lt_ulp_not_infinity1, SPECIFICATION,
            closest_such_def, closest_def, is_closest_def]
   \\ SELECT_ELIM_TAC
   \\ rw []
   >| [
      qexists_tac `float_plus_zero (:'t # 'w)`
      \\ simp [zero_properties, zero_to_real, ABS_POS,
               ABS_NEG]
      \\ rw [float_plus_zero_def]
      \\ Cases_on `float_is_zero b`
      \\ rsimp [float_is_zero_to_real_imp]
      \\ metis_tac
           [ULP_lt_float_to_real, ulp_lt_ULP, REAL_LE_TRANS,
            REAL_ARITH ``2 * abs x <= abs c ==> abs x <= abs (c - x)``],
      (* -- *)
      Cases_on `float_is_zero r`
      >- fs [float_sets]
      \\ Cases_on `2 * abs x < ulp (:'t # 'w)`
      >| [
         imp_res_tac ulp_lt_float_to_real
         \\ compare_with_zero_tac
         \\ metis_tac
               [REAL_ARITH
                  ``~(2 * abs x < u /\ u <= abs r /\ abs (r - x) <= abs x)``],
         (* -- *)
         imp_res_tac
            (REAL_ARITH ``a <= b /\ ~(a < b) ==> (a = b: real)``)
         \\ imp_res_tac half_ulp
         \\ imp_res_tac min_pos_odd
         \\ compare_with_zero_tac
         \\ fs []
         \\ qpat_x_assum `!a. q \/ t`
               (qspec_then `float_plus_zero (:'t # 'w)` strip_assume_tac)
         \\ rfs [ABS_NEG, zero_properties, zero_to_real,
                 float_components, GSYM ulp, GSYM neg_ulp]
         \\ qpat_x_assum `!b. p` (qspec_then `b` imp_res_tac)
         \\ metis_tac
              [REAL_ARITH
                  ``~((2 * abs x = u) /\ abs (u - x) <= abs x /\
                      ~(abs x <= abs (b - x)) /\ abs (u - x) <= abs (b - x))``,
               REAL_ARITH
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

Theorem largest_is_positive[simp]:
   0 <= largest (:'t # 'w)
Proof
   simp [largest_def, REAL_LE_MUL, REAL_LE_DIV,
         REAL_SUB_LE, POW_2_LE1,
         REAL_INV_1OVER, REAL_LE_LDIV_EQ,
         REAL_ARITH ``1r <= n ==> 1 <= 2 * n``]
QED

Theorem threshold_is_positive[simp]:
   0 < threshold (:'t # 'w)
Proof
   simp [threshold_def, REAL_LT_MUL, REAL_LT_DIV,
         REAL_SUB_LT, POW_2_LE1,
         REAL_INV_1OVER, REAL_LT_LDIV_EQ, pow,
         REAL_ARITH ``1r <= n ==> 1 < 2 * (2 * n)``]
QED

val tac =
   rrw  [round_def]
   \\ rlfs [largest_is_positive,
           REAL_ARITH ``0 <= l /\ l < x ==> ~(x < -l: real)``]
   \\ metis_tac [threshold_is_positive, largest_is_positive,
                 REAL_ARITH “(0r < i /\ x <= -i ==> ~(i <= x)) /\
                                     (0r <= i /\ x < -i ==> ~(i < x))”]

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

Theorem round_roundTowardZero_top:
  !y: ('t, 'w) float x.
    largest (:'t # 'w) < x ==> (round roundTowardZero x = float_top (:'t # 'w))
Proof tac
QED

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

Theorem round_roundTowardNegative_minus_infinity:
   !y: ('t, 'w) float x.
     x < -largest (:'t # 'w) ==>
     (round roundTowardNegative x = float_minus_infinity (:'t # 'w))
Proof tac
QED

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
         GSYM REAL_NEG_MINUS1, REAL_OF_NUM_POW,
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
   tac [REAL_INV_1OVER, mult_ratl]
   )

val threshold = Q.store_thm("threshold",
   `threshold (:'t # 'w) =
       &(2 EXP (UINT_MAX (:'w) - 1)) * (2 - 1 / &(2 * dimword (:'t))) /
       &(2 EXP INT_MAX (:'w))`,
   tac [REAL_INV_1OVER, mult_ratl, arithmeticTheory.EXP]
   )

val largest_top_lem = Q.prove(
  `w2n (n2w (UINT_MAX (:'w)) + -1w : 'w word) = UINT_MAX (:'w) - 1`,
  simp_tac arith_ss
     [wordsTheory.WORD_LITERAL_ADD
      |> CONJUNCT2
      |> Q.SPECL [`UINT_MAX (:'w)`, `1`]
      |> SIMP_RULE std_ss [wordsTheory.ZERO_LT_UINT_MAX,
                           DECIDE ``0n < x ==> 1 <= x``],
      wordsTheory.w2n_n2w, wordsTheory.BOUND_ORDER,
      DECIDE ``a < b ==> (a - 1n < b)``]
  )

val largest_top_lem2 = Q.prove(
  `&UINT_MAX (:'t) + 1 = &dimword (:'t) : real`,
  simp [wordsTheory.UINT_MAX_def, DECIDE ``1n < n ==> (n - 1 + 1 = n)``])

val largest_is_top = Q.store_thm("largest_is_top",
  `1 < dimindex(:'w) ==>
   (largest (:'t # 'w) = float_to_real (float_top (:'t # 'w)))`,
  strip_tac
  \\ `dimword(:'w) <> 2`
  by fs [wordsTheory.dimword_def,
         arithmeticTheory.EXP_BASE_INJECTIVE
         |> Q.SPEC `2`
         |> REWRITE_RULE [DECIDE ``1n < 2``]
         |> Q.SPECL [`n`, `1`]
         |> REWRITE_RULE [arithmeticTheory.EXP_1]]
  \\ `2 < dimword(:'w)` by simp [DECIDE ``1 < n /\ n <> 2 ==> 2n < n``]
  \\ `UINT_MAXw - 1w <> 0w : 'w word` by simp []
  \\ asm_simp_tac std_ss [largest, float_top_def, float_to_real]
  \\ simp_tac std_ss [wordsTheory.word_T_def]
  \\ simp [REAL_EQ_LDIV_EQ, DECIDE ``0n < n ==> n <> 0``,
           REAL_SUB_LDISTRIB, REAL_ADD_LDISTRIB,
           REAL_EQ_SUB_RADD, REAL_DIV_REFL,
           mult_ratr, mult_ratl, wordsTheory.BOUND_ORDER,
           ONCE_REWRITE_RULE [REAL_MUL_COMM] mul_cancel,
           largest_top_lem]
  \\ simp_tac std_ss
       [GSYM REAL_ADD_ASSOC, REAL_DIV_ADD,
        GSYM REAL_MUL, largest_top_lem2,
        mul_cancel |> Q.SPECL [`a`, `&(n : num)`] |> SIMP_RULE (srw_ss()) [],
        wordsTheory.ZERO_LT_dimword, DECIDE ``0 < n ==> n <> 0n``,
        REAL_ARITH ``a * b + b = (a + 1r) * b``, REAL_DOUBLE]
  )

Theorem largest_lt_threshold:
  largest (:'t # 'w) < threshold (:'t # 'w)
Proof
  rw [largest, threshold, REAL_LT_RDIV, REAL_LT_LMUL,
      REAL_ARITH ``a - b < a - c <=> c < b : real``,
      REAL_LT_RDIV_EQ, REAL_LT_LDIV_EQ,
      mult_ratl] >>
  fs[wordsTheory.dimword_def]
QED

Theorem float_tests:
    (!s e f.
       float_is_nan <| Sign := s; Exponent := e; Significand := f |> <=>
       (e = -1w) /\ (f <> 0w)) /\
    (!s e f.
       float_is_signalling <| Sign := s; Exponent := e; Significand := f |> <=>
       (e = -1w) /\ ~word_msb f /\ (f <> 0w)) /\
    (!s e f.
       float_is_infinite <| Sign := s; Exponent := e; Significand := f |> <=>
       (e = -1w) /\ (f = 0w)) /\
    (!s e f.
       float_is_normal <| Sign := s; Exponent := e; Significand := f |> <=>
       (e <> 0w) /\ (e <> -1w)) /\
    (!s e f.
       float_is_subnormal <| Sign := s; Exponent := e; Significand := f |> <=>
       (e = 0w) /\ (f <> 0w)) /\
    (!s e f.
       float_is_zero <| Sign := s; Exponent := e; Significand := f |> <=>
       (e = 0w) /\ (f = 0w)) /\
    (!s e f.
       float_is_finite <| Sign := s; Exponent := e; Significand := f |> <=>
       (e <> -1w))
Proof
   rw [float_is_nan_def, float_is_signalling_def, float_is_infinite_def,
       float_is_finite_def, float_is_normal_def, float_is_subnormal_def,
       float_value_def]
   \\ rw [float_sets, float_minus_zero_def, float_plus_zero_def,
          float_is_finite_def, float_negate_def]
   \\ wordsLib.Cases_on_word_value `s`
   \\ simp []
QED

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

val float_round_to_integral_compute = Q.store_thm(
   "float_round_to_integral_compute",
   `(!m. float_round_to_integral m (float_minus_infinity (:'t # 'w)) =
         float_minus_infinity (:'t # 'w)) /\
    (!m. float_round_to_integral m (float_plus_infinity (:'t # 'w)) =
         float_plus_infinity (:'t # 'w)) /\
    (!m fp_op.
         float_round_to_integral m (float_some_qnan fp_op) =
         float_some_qnan fp_op)`,
   simp [float_round_to_integral_def, float_values]
   )

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

val float_add_compute = Q.store_thm("float_add_compute",
   `(!mode x fp_op.
       float_add mode (float_some_qnan fp_op) x =
       (check_for_signalling [x],
        float_some_qnan (FP_Add mode (float_some_qnan fp_op) x)))
       /\
    (!mode x fp_op.
       float_add mode x (float_some_qnan fp_op) =
       (check_for_signalling [x],
        float_some_qnan (FP_Add mode x (float_some_qnan fp_op))))
       /\
    (!mode.
       float_add mode (float_minus_infinity (:'t # 'w))
                      (float_minus_infinity (:'t # 'w)) =
       (clear_flags, float_minus_infinity (:'t # 'w))) /\
    (!mode.
       float_add mode (float_minus_infinity (:'t # 'w))
                      (float_plus_infinity (:'t # 'w)) =
       (invalidop_flags,
        float_some_qnan (FP_Add mode (float_minus_infinity (:'t # 'w))
                                     (float_plus_infinity (:'t # 'w))))) /\
    (!mode.
       float_add mode (float_plus_infinity (:'t # 'w))
                      (float_plus_infinity (:'t # 'w)) =
       (clear_flags, float_plus_infinity (:'t # 'w))) /\
    (!mode.
       float_add mode (float_plus_infinity (:'t # 'w))
                      (float_minus_infinity (:'t # 'w)) =
       (invalidop_flags,
        float_some_qnan (FP_Add mode (float_plus_infinity (:'t # 'w))
                                     (float_minus_infinity (:'t # 'w)))))
   `,
   simp [float_add_def, float_values, float_components, some_nan_properties,
         check_for_signalling_def]
   \\ strip_tac
   \\ strip_tac
   \\ Cases_on `float_value x`
   \\ simp [float_is_signalling_def, float_is_nan_def]
   )

val float_add_nan = Q.store_thm("float_add_nan",
   `!mode x y.
       (float_value x = NaN) \/ (float_value y = NaN) ==>
       (float_add mode x y =
        (check_for_signalling [x; y], float_some_qnan (FP_Add mode x y)))`,
   NTAC 3 strip_tac
   \\ Cases_on `float_value x`
   \\ Cases_on `float_value y`
   \\ simp [float_add_def, check_for_signalling_def,
            float_is_signalling_def, float_is_nan_def]
   )

val float_add_finite = Q.store_thm("float_add_finite",
   `!mode x y r1 r2.
       (float_value x = Float r1) /\ (float_value y = Float r2) ==>
       (float_add mode x y =
        float_round_with_flags mode
          (if (r1 = 0) /\ (r2 = 0) /\ (x.Sign = y.Sign) then
             x.Sign = 1w
           else mode = roundTowardNegative) (r1 + r2))`,
   simp [float_add_def]
   )

val float_add_finite_plus_infinity = Q.store_thm(
   "float_add_finite_plus_infinity",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_add mode x (float_plus_infinity (:'t # 'w)) =
        (clear_flags, float_plus_infinity (:'t # 'w)))`,
   simp [float_add_def, float_values]
   )

val float_add_plus_infinity_finite = Q.store_thm(
   "float_add_plus_infinity_finite",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_add mode (float_plus_infinity (:'t # 'w)) x =
        (clear_flags, float_plus_infinity (:'t # 'w)))`,
   simp [float_add_def, float_values]
   )

val float_add_finite_minus_infinity = Q.store_thm(
   "float_add_finite_minus_infinity",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_add mode x (float_minus_infinity (:'t # 'w)) =
        (clear_flags, float_minus_infinity (:'t # 'w)))`,
   simp [float_add_def, float_values]
   )

val float_add_minus_infinity_finite = Q.store_thm(
   "float_add_minus_infinity_finite",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_add mode (float_minus_infinity (:'t # 'w)) x =
        (clear_flags, float_minus_infinity (:'t # 'w)))`,
   simp [float_add_def, float_values]
   )

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

val float_sub_compute = Q.store_thm("float_sub_compute",
   `(!mode x fp_op.
       float_sub mode (float_some_qnan fp_op) x =
       (check_for_signalling [x],
        float_some_qnan (FP_Sub mode (float_some_qnan fp_op) x))) /\
    (!mode x fp_op.
       float_sub mode x (float_some_qnan fp_op) =
       (check_for_signalling [x],
        float_some_qnan (FP_Sub mode x (float_some_qnan fp_op)))) /\
    (!mode.
       float_sub mode (float_minus_infinity (:'t # 'w))
                      (float_minus_infinity (:'t # 'w)) =
       (invalidop_flags,
        float_some_qnan (FP_Sub mode (float_minus_infinity (:'t # 'w))
                                     (float_minus_infinity (:'t # 'w))))) /\
    (!mode.
       float_sub mode (float_minus_infinity (:'t # 'w))
                      (float_plus_infinity (:'t # 'w)) =
       (clear_flags, float_minus_infinity (:'t # 'w))) /\
    (!mode.
       float_sub mode (float_plus_infinity (:'t # 'w))
                      (float_plus_infinity (:'t # 'w)) =
       (invalidop_flags,
        float_some_qnan (FP_Sub mode (float_plus_infinity (:'t # 'w))
                                     (float_plus_infinity (:'t # 'w))))) /\
    (!mode.
       float_sub mode (float_plus_infinity (:'t # 'w))
                      (float_minus_infinity (:'t # 'w)) =
       (clear_flags, float_plus_infinity (:'t # 'w)))
   `,
   simp [float_sub_def, float_values, float_components, some_nan_properties,
         check_for_signalling_def]
   \\ strip_tac
   \\ strip_tac
   \\ Cases_on `float_value x`
   \\ simp [float_is_signalling_def, float_is_nan_def]
   )

val float_sub_nan = Q.store_thm("float_sub_nan",
   `!mode x y.
       (float_value x = NaN) \/ (float_value y = NaN) ==>
       (float_sub mode x y =
        (check_for_signalling [x; y], float_some_qnan (FP_Sub mode x y)))`,
   NTAC 3 strip_tac
   \\ Cases_on `float_value x`
   \\ Cases_on `float_value y`
   \\ simp [float_sub_def, check_for_signalling_def,
            float_is_signalling_def, float_is_nan_def]
   )

val float_sub_finite = Q.store_thm("float_sub_finite",
   `!mode x y r1 r2.
       (float_value x = Float r1) /\ (float_value y = Float r2) ==>
       (float_sub mode x y =
        float_round_with_flags mode
           (if (r1 = 0) /\ (r2 = 0) /\ x.Sign <> y.Sign then
              x.Sign = 1w
            else mode = roundTowardNegative) (r1 - r2))`,
   simp [float_sub_def]
   )

val float_sub_finite_plus_infinity = Q.store_thm(
   "float_sub_finite_plus_infinity",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_sub mode x (float_plus_infinity (:'t # 'w)) =
        (clear_flags, float_minus_infinity (:'t # 'w)))`,
   simp [float_sub_def, float_values, float_minus_infinity_def]
   )

val float_sub_plus_infinity_finite = Q.store_thm(
   "float_sub_plus_infinity_finite",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_sub mode (float_plus_infinity (:'t # 'w)) x =
        (clear_flags, float_plus_infinity (:'t # 'w)))`,
   simp [float_sub_def, float_values]
   )

val float_sub_finite_minus_infinity = Q.store_thm(
   "float_sub_finite_minus_infinity",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_sub mode x (float_minus_infinity (:'t # 'w)) =
        (clear_flags, float_plus_infinity (:'t # 'w)))`,
   simp [float_sub_def, float_values, float_negate_negate,
         float_minus_infinity_def]
   )

val float_sub_minus_infinity_finite = Q.store_thm(
   "float_sub_minus_infinity_finite",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_sub mode (float_minus_infinity (:'t # 'w)) x =
        (clear_flags, float_minus_infinity (:'t # 'w)))`,
   simp [float_sub_def, float_values]
   )

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

val float_mul_compute = Q.store_thm("float_mul_compute",
   `(!mode x fp_op.
       float_mul mode (float_some_qnan fp_op) x =
       (check_for_signalling [x],
        float_some_qnan (FP_Mul mode (float_some_qnan fp_op) x))) /\
    (!mode x fp_op.
       float_mul mode x (float_some_qnan fp_op) =
       (check_for_signalling [x],
        float_some_qnan (FP_Mul mode x (float_some_qnan fp_op)))) /\
    (!mode.
       float_mul mode (float_minus_infinity (:'t # 'w))
                      (float_minus_infinity (:'t # 'w)) =
       (clear_flags, float_plus_infinity (:'t # 'w))) /\
    (!mode.
       float_mul mode (float_minus_infinity (:'t # 'w))
                      (float_plus_infinity (:'t # 'w)) =
       (clear_flags, float_minus_infinity (:'t # 'w))) /\
    (!mode.
       float_mul mode (float_plus_infinity (:'t # 'w))
                      (float_plus_infinity (:'t # 'w)) =
       (clear_flags, float_plus_infinity (:'t # 'w))) /\
    (!mode.
       float_mul mode (float_plus_infinity (:'t # 'w))
                      (float_minus_infinity (:'t # 'w)) =
       (clear_flags, float_minus_infinity (:'t # 'w)))
   `,
   simp [float_mul_def, float_values, float_components, some_nan_properties,
         check_for_signalling_def]
   \\ strip_tac
   \\ strip_tac
   \\ Cases_on `float_value x`
   \\ simp [float_is_signalling_def, float_is_nan_def]
   )

val float_mul_nan = Q.store_thm("float_mul_nan",
   `!mode x y.
       (float_value x = NaN) \/ (float_value y = NaN) ==>
       (float_mul mode x y =
        (check_for_signalling [x; y], float_some_qnan (FP_Mul mode x y)))`,
   NTAC 3 strip_tac
   \\ Cases_on `float_value x`
   \\ Cases_on `float_value y`
   \\ simp [float_mul_def, check_for_signalling_def,
            float_is_signalling_def, float_is_nan_def]
   )

val float_mul_finite = Q.store_thm("float_mul_finite",
   `!mode x y r1 r2.
       (float_value x = Float r1) /\ (float_value y = Float r2) ==>
       (float_mul mode x y =
        float_round_with_flags mode (x.Sign <> y.Sign) (r1 * r2))`,
   simp [float_mul_def]
   )

val float_mul_finite_plus_infinity = Q.store_thm(
   "float_mul_finite_plus_infinity",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_mul mode x (float_plus_infinity (:'t # 'w)) =
        if r = 0 then
           (invalidop_flags,
            float_some_qnan (FP_Mul mode x (float_plus_infinity (:'t # 'w))))
        else (clear_flags,
              if x.Sign = 0w then
                float_plus_infinity (:'t # 'w)
              else float_minus_infinity (:'t # 'w)))`,
   rw [float_mul_def, float_values]
   \\ fs [float_plus_infinity_def]
   )

val float_mul_plus_infinity_finite = Q.store_thm(
   "float_mul_plus_infinity_finite",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_mul mode (float_plus_infinity (:'t # 'w)) x =
        if r = 0 then
           (invalidop_flags,
            float_some_qnan (FP_Mul mode (float_plus_infinity (:'t # 'w)) x))
        else (clear_flags,
              if x.Sign = 0w
                 then float_plus_infinity (:'t # 'w)
              else float_minus_infinity (:'t # 'w)))`,
   rw [float_mul_def, float_values]
   \\ fs [float_plus_infinity_def]
   )

val float_mul_finite_minus_infinity = Q.store_thm(
   "float_mul_finite_minus_infinity",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_mul mode x (float_minus_infinity (:'t # 'w)) =
        if r = 0 then
           (invalidop_flags,
            float_some_qnan (FP_Mul mode x (float_minus_infinity (:'t # 'w))))
        else (clear_flags,
              if x.Sign = 0w
                 then float_minus_infinity (:'t # 'w)
              else float_plus_infinity (:'t # 'w)))`,
   rw [float_mul_def, float_values]
   \\ fs [float_minus_infinity_def, float_plus_infinity_def, float_negate_def]
   \\ metis_tac [sign_inconsistent]
   )

val float_mul_minus_infinity_finite = Q.store_thm(
   "float_mul_minus_infinity_finite",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_mul mode (float_minus_infinity (:'t # 'w)) x =
        if r = 0 then
           (invalidop_flags,
            float_some_qnan (FP_Mul mode (float_minus_infinity (:'t # 'w)) x))
        else (clear_flags,
              if x.Sign = 0w
                 then float_minus_infinity (:'t # 'w)
              else float_plus_infinity (:'t # 'w)))`,
   rw [float_mul_def, float_values]
   \\ fs [float_minus_infinity_def, float_plus_infinity_def, float_negate_def]
   \\ metis_tac [sign_inconsistent]
   )

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

val float_div_compute = Q.store_thm("float_div_compute",
   `(!mode x fp_op.
       float_div mode (float_some_qnan fp_op) x =
       (check_for_signalling [x],
        float_some_qnan (FP_Div mode (float_some_qnan fp_op) x))) /\
    (!mode x fp_op.
       float_div mode x (float_some_qnan fp_op) =
       (check_for_signalling [x],
        float_some_qnan (FP_Div mode x (float_some_qnan fp_op)))) /\
    (!mode.
       float_div mode (float_minus_infinity (:'t # 'w))
                      (float_minus_infinity (:'t # 'w)) =
       (invalidop_flags,
        float_some_qnan (FP_Div mode (float_minus_infinity (:'t # 'w))
                                     (float_minus_infinity (:'t # 'w))))) /\
    (!mode.
       float_div mode (float_minus_infinity (:'t # 'w))
                      (float_plus_infinity (:'t # 'w)) =
       (invalidop_flags,
        float_some_qnan (FP_Div mode (float_minus_infinity (:'t # 'w))
                                     (float_plus_infinity (:'t # 'w))))) /\
    (!mode.
       float_div mode (float_plus_infinity (:'t # 'w))
                      (float_plus_infinity (:'t # 'w)) =
       (invalidop_flags,
        float_some_qnan (FP_Div mode (float_plus_infinity (:'t # 'w))
                                     (float_plus_infinity (:'t # 'w))))) /\
    (!mode.
       float_div mode (float_plus_infinity (:'t # 'w))
                      (float_minus_infinity (:'t # 'w)) =
       (invalidop_flags,
        float_some_qnan (FP_Div mode (float_plus_infinity (:'t # 'w))
                                     (float_minus_infinity (:'t # 'w)))))
   `,
   simp [float_div_def, float_values, float_components, some_nan_properties,
         check_for_signalling_def]
   \\ strip_tac
   \\ strip_tac
   \\ Cases_on `float_value x`
   \\ simp [float_is_signalling_def, float_is_nan_def]
   )

val float_div_nan = Q.store_thm("float_div_nan",
   `!mode x y.
       (float_value x = NaN) \/ (float_value y = NaN) ==>
       (float_div mode x y =
        (check_for_signalling [x; y], float_some_qnan (FP_Div mode x y)))`,
   NTAC 3 strip_tac
   \\ Cases_on `float_value x`
   \\ Cases_on `float_value y`
   \\ simp [float_div_def, check_for_signalling_def,
            float_is_signalling_def, float_is_nan_def]
   )

val float_div_finite = Q.store_thm("float_div_finite",
   `!mode x y r1 r2.
       (float_value x = Float r1) /\ (float_value y = Float r2) ==>
       (float_div mode x y =
        if r2 = 0
           then if r1 = 0 then
                  (invalidop_flags, float_some_qnan (FP_Div mode x y))
                else
                  (dividezero_flags,
                   if x.Sign = y.Sign then float_plus_infinity (:'t # 'w)
                   else float_minus_infinity (:'t # 'w))
        else float_round_with_flags mode (x.Sign <> y.Sign) (r1 / r2))`,
   simp [float_div_def]
   )

val float_div_finite_plus_infinity = Q.store_thm(
   "float_div_finite_plus_infinity",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_div mode x (float_plus_infinity (:'t # 'w)) =
        (clear_flags,
         if x.Sign = 0w then float_plus_zero (:'t # 'w)
         else float_minus_zero (:'t # 'w)))`,
   rw [float_div_def, float_values]
   \\ fs [float_plus_infinity_def]
   )

val float_div_plus_infinity_finite = Q.store_thm(
   "float_div_plus_infinity_finite",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_div mode (float_plus_infinity (:'t # 'w)) x =
        (clear_flags,
         if x.Sign = 0w then float_plus_infinity (:'t # 'w)
         else float_minus_infinity (:'t # 'w)))`,
   rw [float_div_def, float_values]
   \\ fs [float_plus_infinity_def]
   )

val float_div_finite_minus_infinity = Q.store_thm(
   "float_div_finite_minus_infinity",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_div mode x (float_minus_infinity (:'t # 'w)) =
        (clear_flags,
         if x.Sign = 0w then float_minus_zero (:'t # 'w)
         else float_plus_zero (:'t # 'w)))`,
   rw [float_div_def, float_values]
   \\ fs [float_minus_infinity_def, float_plus_infinity_def, float_negate_def]
   \\ metis_tac [sign_inconsistent]
   )

val float_div_minus_infinity_finite = Q.store_thm(
   "float_div_minus_infinity_finite",
   `!mode x r.
       (float_value x = Float r) ==>
       (float_div mode (float_minus_infinity (:'t # 'w)) x =
        (clear_flags,
         if x.Sign = 0w then float_minus_infinity (:'t # 'w)
         else float_plus_infinity (:'t # 'w)))`,
   rw [float_div_def, float_values]
   \\ fs [float_minus_infinity_def, float_plus_infinity_def, float_negate_def]
   \\ metis_tac [sign_inconsistent]
   )

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

Theorem float_is_nan_impl:
  !x. float_is_nan x <=> ~float_equal x x
Proof
   simp[float_is_nan_def, float_equal_def, float_compare_def]
   \\ strip_tac
   \\ Cases_on `float_value x`
   \\ simp[]
QED

Theorem float_is_zero_impl:
  !x. float_is_zero x <=> float_equal (float_plus_zero (:'w # 't)) x
Proof
  simp[float_is_zero_def, float_equal_def, float_compare_def, AllCaseEqs(),
       SF CONJ_ss] >> qx_gen_tac ‘x’ >>
  Cases_on `float_value x` >> simp[EQ_SYM_EQ]
QED

(* ------------------------------------------------------------------------ *)

val () = export_theory ()
