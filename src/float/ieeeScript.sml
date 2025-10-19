
(* ========================================================================= *)
(* Formalization of IEEE-754 Standard for binary floating-point arithmetic.  *)
(* ========================================================================= *)

(*---------------------------------------------------------------------------*
 * First, make standard environment available.                               *
 *---------------------------------------------------------------------------*)
Theory ieee
Ancestors
  real pred_set arithmetic
Libs
  Num_conv

(*---------------------------------------------------------------------------*
 * Next, bring in extra tools used.                                          *
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*
 * Create the theory.                                                        *
 *---------------------------------------------------------------------------*)

val _ = ParseExtras.temp_loose_equality()

(* ------------------------------------------------------------------------- *)
(* Derived parameters for floating point formats.                            *)
(* ------------------------------------------------------------------------- *)

Definition expwidth[nocompute]:
  expwidth (ew:num,fw:num) = ew
End

Definition fracwidth[nocompute]:
  fracwidth (ew:num,fw:num) = fw
End

Definition wordlength[nocompute]:
  wordlength(X: (num#num)) = (expwidth(X) + fracwidth(X) + (1:num))
End

Definition emax[nocompute]:
  emax(X: (num#num)) = (((2:num) EXP (expwidth (X))) - (1:num))
End

Definition bias[nocompute]:
  bias(X: (num#num)) = ((2:num) EXP (expwidth(X) - (1:num)) - (1:num))
End

(* ------------------------------------------------------------------------- *)
(* Predicates for the four IEEE formats.                                     *)
(* ------------------------------------------------------------------------- *)

Definition is_single[nocompute]:
  is_single (X: (num#num)) = (expwidth(X) = (8:num)) /\ (wordlength(X) = (32:num))
End

Definition is_double[nocompute]:
  is_double(X: (num#num)) = (expwidth(X) = (11:num)) /\ (wordlength(X) = (64:num))
End

Definition is_single_extended[nocompute]:
  is_single_extended(X) = expwidth(X) >= (11:num) /\ wordlength(X) >= (43:num)
End

Definition is_double_extended[nocompute]:
  is_double_extended(X) = expwidth(X) >= (15:num) /\ wordlength(X) >= (79:num)
End

(* ------------------------------------------------------------------------- *)
(* Extractors for fields.                                                    *)
(* ------------------------------------------------------------------------- *)

Definition sign[nocompute]:
  sign ((s:num),(e:num),(f:num)) = (s:num)
End

Definition exponent[nocompute]:
  exponent ((s:num),(e:num),(f:num)) = (e:num)
End

Definition fraction[nocompute]:
  fraction ((s:num),(e:num),(f:num)) = (f:num)
End

(* ------------------------------------------------------------------------- *)
(* Partition of numbers into disjoint classes.                               *)
(* ------------------------------------------------------------------------- *)

Definition is_nan[nocompute]:
  is_nan(X: (num#num)) (a:num#num#num) =
  (exponent (a:num#num#num) = emax(X)) /\ ~(fraction (a:num#num#num) = (0:num))
End

Definition is_infinity[nocompute]:
  is_infinity((X: num#num)) (a:num#num#num) = (exponent a = emax(X)) /\ (fraction a = (0:num))
End

Definition is_normal[nocompute]:
  is_normal(X: (num#num)) (a:num#num#num) = (((0:num) < exponent a) /\ (exponent a < emax(X)))
End

Definition is_denormal[nocompute]:
  is_denormal(X:num#num) (a:num#num#num) = ((exponent a = (0:num)) /\ ~(fraction a = (0:num)))
End

Definition is_zero[nocompute]:
  is_zero (X:num#num) (a:num#num#num) = ((exponent a = 0) /\ (fraction a = 0))
End

(* ------------------------------------------------------------------------- *)
(* Other useful predicates.                                                  *)
(* ------------------------------------------------------------------------- *)

Definition is_valid[nocompute]:
  is_valid(X:num#num) (s:num,e:num,f:num) =
  ((s < SUC(SUC 0)) /\ (e < 2 EXP expwidth(X)) /\ (f < 2 EXP fracwidth(X)))
End

Definition is_finite[nocompute]:
  is_finite(X:num#num) (a : num#num#num) =
  ((is_valid (X) a) /\ ((is_normal(X:num#num) a) \/ (is_denormal(X:num#num) a) \/ (is_zero (X:num#num) a)))
End

(* ------------------------------------------------------------------------- *)
(* Some special values.                                                      *)
(* ------------------------------------------------------------------------- *)

Definition plus_infinity[nocompute]:
  plus_infinity(X:num#num) = (0:num,emax(X),0:num)
End

Definition minus_infinity[nocompute]:
  minus_infinity(X:num#num) = (1:num,emax(X),0:num)
End

Definition plus_zero[nocompute]:
  plus_zero(X:num#num) = (0:num,0:num,0:num)
End

Definition minus_zero[nocompute]:
  minus_zero(X:num#num) = (1:num,0:num,0:num)
End

Definition topfloat[nocompute]:
  topfloat(X) = (0:num, (emax (X:num#num) - (1:num)) , (2 EXP fracwidth(X) - (1:num)))
End

Definition bottomfloat[nocompute]:
  bottomfloat (X:num#num) = ((1:num), (emax(X) - 1) , (2 EXP fracwidth(X) - 1))
End

(* ------------------------------------------------------------------------- *)
(* Negation operation on floating point values.                              *)
(* ------------------------------------------------------------------------- *)

Definition minus[nocompute]:
  minus(X:num#num) (a : num#num#num)= ((1 - sign(a)),exponent(a),fraction(a))
End

(* ------------------------------------------------------------------------- *)
(* Concrete encodings (at least valid for single and double).                *)
(* ------------------------------------------------------------------------- *)

Definition encoding[nocompute]:
  encoding(X:num#num) (s:num,e:num,f:num) =
  ((s * 2 EXP (wordlength(X) - 1)) + (e * 2 EXP fracwidth(X)) + f)
End

(* ------------------------------------------------------------------------- *)
(* Real number valuations.                                                   *)
(* ------------------------------------------------------------------------- *)

Definition valof[nocompute]:
  valof (X:num#num) (s:num,e:num,f:num) =
  (if (e = 0) then  ~(&1) pow s * (&2 / &2 pow bias(X)) * (&f / &2 pow (fracwidth(X)))
    else  ~(&1) pow s * (&2 pow e / &2 pow bias(X)) * (&1 + &f / &2 pow fracwidth(X)))
End

(* ------------------------------------------------------------------------- *)
(* A few handy values.                                                       *)
(* ------------------------------------------------------------------------- *)

Definition largest[nocompute]:
  largest(X:num#num) = (&2 pow (emax(X) - 1) / &2 pow bias(X)) * (&2 - inv(&2 pow fracwidth(X)))
End

Definition threshold[nocompute]:
  threshold(X:num#num) = (&2 pow (emax(X) - 1) / &2 pow bias(X)) * (&2 - inv(&2 pow SUC(fracwidth(X))))
End

Definition ulp[nocompute]:
  ulp(X:num#num) (a :num#num#num) = valof(X) (0,exponent(a),1) - valof(X) (0,exponent(a),0)
End

(* ------------------------------------------------------------------------- *)
(* Enumerated type for rounding modes.                                       *)
(* ------------------------------------------------------------------------- *)

val roundmode = Hol_datatype
  `roundmode = To_nearest
  | float_To_zero
  | To_pinfinity
  | To_ninfinity`;

(* ------------------------------------------------------------------------- *)
(* Characterization of best approximation from a set of abstract values.     *)
(* ------------------------------------------------------------------------- *)

Definition is_closest[nocompute]:
  is_closest (v) (s) (x) (a) = (a IN s) /\ (!b. (b IN s) ==> abs(v(a) - x) <= abs(v(b) - x))
End

(* ------------------------------------------------------------------------- *)
(* Best approximation with a deciding preference for multiple possibilities. *)
(* ------------------------------------------------------------------------- *)

Definition closest[nocompute]:
  closest (v) (p) (s) (x) = @(a). is_closest v s x a /\
  ((?b. is_closest v s x b /\ p(b)) ==> p(a))
End

(* ------------------------------------------------------------------------- *)
(* Rounding to floating point formats.                                       *)
(* ------------------------------------------------------------------------- *)

Definition round_def:   (round(X:num#num) (To_nearest) (x:real) =
  (if (x <= ~(threshold(X))) then (minus_infinity(X))
   else if (x >= threshold(X)) then (plus_infinity(X))
   else (closest (valof(X)) (\a. EVEN(fraction(a)))
  { a | is_finite(X) a } x))) /\

  (round(X) (float_To_zero) x =
  (if (x < ~(largest(X))) then (bottomfloat(X))
   else if (x > largest(X)) then (topfloat(X))
   else (closest (valof(X)) (\x. T)
  { a | is_finite(X) a /\ abs(valof(X) a) <= abs(x) } x))) /\

  (round(X) (To_pinfinity) x =
   if x < ~(largest(X)) then bottomfloat(X)
   else if (x > largest(X)) then plus_infinity(X)
   else closest (valof(X)) (\x. T)
  { a | is_finite(X) a /\ valof(X) a >= x } x) /\

  (round(X) (To_ninfinity) x =
   if x < ~(largest(X)) then minus_infinity(X)
   else if (x > largest(X)) then topfloat(X)
   else closest (valof(X)) (\x. T)
  { a | is_finite(X) a /\ valof(X) a <= x } x)
End

(* ------------------------------------------------------------------------- *)
(* Rounding to integer values in floating point format.                      *)
(* ------------------------------------------------------------------------- *)

Definition is_integral[nocompute]:
  is_integral(X:num#num) (a:(num#num#num)) = is_finite(X) a /\ ?n. abs(valof(X) a) = &n
End

Definition intround_def:   (intround(X:num#num) (To_nearest) (x:real) =
  (if (x <= ~(threshold(X))) then (minus_infinity(X))
   else if (x >= threshold(X)) then (plus_infinity(X))
   else (closest (valof(X)) (\a. (?n. (EVEN n) /\ (abs(valof(X) a) = &n)))
  { a | is_integral(X) a} x))) /\

  (intround(X) float_To_zero x =
  (if (x < ~(largest(X))) then (bottomfloat(X))
   else if (x > largest(X)) then (topfloat(X))
   else (closest (valof(X)) (\x. T)
  { a | is_integral(X) a /\ abs(valof(X) a) <= abs(x) } x))) /\

  (intround(X) To_pinfinity x =
  (if (x < ~(largest(X))) then (bottomfloat(X))
   else if (x > largest(X)) then (plus_infinity(X))
   else (closest (valof(X)) (\x. T)
  { a | is_integral(X) a /\ valof(X) a >= x } x))) /\

  (intround(X) To_ninfinity x =
   if (x < ~(largest(X))) then (minus_infinity(X))
   else if (x > largest(X)) then (topfloat(X))
   else (closest (valof(X)) (\x. T)
  { a | is_integral(X) a /\ valof(X) a <= x } x))
End

(* ------------------------------------------------------------------------- *)
(* A hack for our (non-standard) treatment of NaNs.                          *)
(* ------------------------------------------------------------------------- *)

Definition some_nan[nocompute]:
  some_nan(X:num#num) = @(a:num#num#num). is_nan(X) a
End

(* ------------------------------------------------------------------------- *)
(* Coercion for signs of zero results.                                       *)
(* ------------------------------------------------------------------------- *)

Definition zerosign[nocompute]:
  zerosign (X:num#num) (s:num) (a:num#num#num) = (if (is_zero(X) a) then
  (if (s = 0) then plus_zero(X) else minus_zero(X)) else a)
End

(* ------------------------------------------------------------------------- *)
(* Useful mathematical operations not already in the HOL Light core.         *)
(* ------------------------------------------------------------------------- *)

val rem = new_infixl_definition (
  "rem", Term`$rem x y = let n = closest I (\x. ?n. EVEN(n) /\ (abs(x) = &n))
  { x | ?n. abs(x) = &n } (x / y) in x - n * y`, 500);

(* ------------------------------------------------------------------------- *)
(* Definitions of the arithmetic operations.                                 *)
(* ------------------------------------------------------------------------- *)

Definition fintrnd[nocompute]:
  fintrnd(X:num#num) (m:roundmode) (a:num#num#num) =
  if is_nan(X) a then some_nan(X)
    else if is_infinity(X) a then a
      else zerosign(X) (sign(a)) (intround(X) m (valof(X) a))
End

Definition fadd[nocompute]:
  fadd(X:num#num) (m:roundmode) (a:num#num#num) (b:num#num#num) =
  if (is_nan(X) a) \/ (is_nan(X) b) \/ ((is_infinity(X) a) /\ (is_infinity(X) b) /\ (~(sign(a) = sign(b)))) then (some_nan(X))
  else if is_infinity(X) a then a
  else if is_infinity(X) b then b
  else zerosign(X) (if is_zero(X) a /\ is_zero(X) b /\ (sign(a) = sign(b)) then sign(a) else if (m = To_ninfinity) then 1 else 0) (round(X) m (valof(X) a + valof(X) b))
End

Definition fsub[nocompute]:
  fsub(X:num#num) (m:roundmode) (a:num#num#num) (b:num#num#num) =
  (if is_nan(X) a \/ is_nan(X) b \/ (is_infinity(X) a /\ is_infinity(X) b /\ (sign(a) = sign(b))) then some_nan(X)
   else if is_infinity(X) a then a
   else if is_infinity(X) b then minus(X) b
   else zerosign(X) (if is_zero(X) a /\ is_zero(X) b /\ ~(sign(a) = sign(b)) then sign(a) else if m = To_ninfinity then 1 else 0) (round(X) m (valof(X) a - valof(X) b)))
End

Definition fmul[nocompute]:
  fmul(X:num#num) (m:roundmode) (a:num#num#num) (b:num#num#num) =
  (if is_nan(X) a \/ is_nan(X) b \/ is_zero(X) a /\ is_infinity(X) b \/ is_infinity(X) a /\ is_zero(X) b then some_nan(X)
   else if is_infinity(X) a \/ is_infinity(X) b then (if sign(a) = sign(b) then plus_infinity(X) else minus_infinity(X))
   else zerosign(X) (if sign(a) = sign(b) then 0 else 1) (round(X) m (valof(X) a * valof(X) b)))
End

Definition fdiv[nocompute]:
  fdiv(X:num#num) (m:roundmode) (a:num#num#num) (b:num#num#num) =
  (if is_nan(X) a \/ is_nan(X) b \/ is_zero(X) a /\ is_zero(X) b \/ is_infinity(X) a /\ is_infinity(X) b then some_nan(X)
   else if is_infinity(X) a \/ is_zero(X) b then (if sign(a) = sign(b) then plus_infinity(X) else minus_infinity(X))
   else if is_infinity(X) b then (if sign(a) = sign(b) then plus_zero(X) else minus_zero(X))
   else zerosign(X) (if sign(a) = sign(b) then 0 else 1) (round(X) m (valof(X) a / valof(X) b)))
End

Definition fsqrt[nocompute]:
  fsqrt (X:num#num) (m:roundmode) (a:num#num#num) =
  (if is_nan(X) a then some_nan(X)
   else if is_zero(X) a \/ is_infinity(X) a /\ (sign(a) = 0) then a
   else if (sign(a) = 1) then some_nan(X)
   else zerosign(X) (sign(a)) (round(X) m (sqrt(valof(X) a))))
End


Definition frem[nocompute]:
  frem(X:num#num) (m:roundmode) (a:num#num#num) (b:num#num#num) =
  (if is_nan(X) a \/ is_nan(X) b \/ is_infinity(X) a \/ is_zero(X) b then some_nan(X)
   else if is_infinity(X) b then a
   else zerosign(X) (sign(a)) (round(X) m (valof(X) a rem valof(X) b)))
End

(* ------------------------------------------------------------------------- *)
(* Negation is specially simple.                                             *)
(* ------------------------------------------------------------------------- *)

Definition fneg[nocompute]:
  fneg(X:num#num) (m:roundmode) (a:num#num#num) = (((1:num)-sign(a)),(exponent(a)),(fraction(a)))
End

(* ------------------------------------------------------------------------- *)
(* Comparison codes.                                                         *)
(* ------------------------------------------------------------------------- *)

Datatype:
  ccode = Gt | Lt | Eq | Un
End

(* ------------------------------------------------------------------------- *)
(* Comparison operations.                                                    *)
(* ------------------------------------------------------------------------- *)

Definition fcompare[nocompute]:
  fcompare(X) a b =
  (if is_nan(X) a \/ is_nan(X) b then Un
   else if is_infinity(X) a /\ (sign(a) = 1) then (if is_infinity(X) b /\ (sign(b) = 1) then Eq else Lt)
   else if is_infinity(X) a /\ (sign(a) = 0) then (if is_infinity(X) b /\ (sign(b) = 0) then Eq else Gt)
   else if is_infinity(X) b /\ (sign(b) = 1) then Gt
   else if is_infinity(X) b /\ (sign(b) = 0) then Lt
   else if valof(X) a < valof(X) b then Lt
   else if valof(X) a = valof(X) b then Eq
   else Gt)
End

Definition flt[nocompute]:
  flt(X) a b = (fcompare(X) a b = Lt)
End

Definition fle[nocompute]:
  fle(X) a b = (fcompare(X) a b = Lt) \/ (fcompare(X) a b = Eq)
End

Definition fgt[nocompute]:
  fgt(X) a b = (fcompare(X) a b = Gt)
End

Definition fge[nocompute]:
  fge(X) a b = (fcompare(X) a b = Gt) \/ (fcompare(X) a b = Eq)
End

Definition feq[nocompute]:
  feq (X) a b = (fcompare(X) a b = Eq)
End

(* ------------------------------------------------------------------------- *)
(* Actual float type with round-to-even.                                     *)
(* ------------------------------------------------------------------------- *)

Definition float_format[nocompute]:
  float_format = ((8:num),(23:num))
End
  (* for double
  “float_format = ((11:num),(52:num))”);
  *)

val float_tybij = define_new_type_bijections {
  name="float_tybij",
  ABS="float",
  REP="defloat",
  tyax =new_type_definition ("float",
  Q.prove (`(?a. (is_valid float_format a))`,
  EXISTS_TAC (“0:num,0:num,0:num” ) THEN
  REWRITE_TAC[float_format, is_valid, GSYM NOT_LESS_EQUAL,
  LE, num_CONV“2:num”, NOT_EXP_0, GSYM SUC_NOT]))};

Definition Val[nocompute]:
  Val a = valof(float_format) (defloat a)
End

Definition Float[nocompute]:
  Float(x) = float (round(float_format) To_nearest x)
End

Definition Sign[nocompute]:
  Sign(a) = sign(defloat a)
End

Definition Exponent[nocompute]:
  Exponent(a) = exponent(defloat a)
End

Definition Fraction[nocompute]:
  Fraction(a) = fraction(defloat a)
End

Definition Ulp[nocompute]:
  Ulp(a) = ulp(float_format) (defloat a)
End

(* ------------------------------------------------------------------------- *)
(* Lifting of the discriminator functions.                                   *)
(* ------------------------------------------------------------------------- *)

Definition Isnan[nocompute]:
  Isnan(a) = is_nan(float_format) (defloat a)
End

Definition Infinity[nocompute]:
  Infinity(a) = is_infinity(float_format) (defloat a)
End

Definition Isnormal[nocompute]:
  Isnormal(a) = is_normal(float_format) (defloat a)
End

Definition Isdenormal[nocompute]:
  Isdenormal(a) = is_denormal(float_format) (defloat a)
End

Definition Iszero[nocompute]:
  Iszero(a) = is_zero(float_format) (defloat a)
End

Definition Finite[nocompute]:
  Finite(a) = Isnormal(a) \/ Isdenormal(a) \/ Iszero(a)
End

Definition Isintegral[nocompute]:
  Isintegral(a) = is_integral(float_format) (defloat a)
End

(* ------------------------------------------------------------------------- *)
(* Basic operations on floats.                                               *)
(* ------------------------------------------------------------------------- *)

Definition Plus_zero[nocompute]:
  Plus_zero = float (plus_zero(float_format))
End

Definition Minus_zero[nocompute]:
  Minus_zero = float (minus_zero(float_format))
End

Definition Minus_infinity[nocompute]:
  Minus_infinity = float (minus_infinity(float_format))
End

Definition Plus_infinity[nocompute]:
  Plus_infinity = float (plus_infinity(float_format))
End

val float_add = new_infixl_definition (
  "float_add",
  Term`$float_add a b = float (fadd(float_format) To_nearest (defloat a) (defloat b))`, 500);

Overload "+" = Term`$float_add`

val float_sub =
    new_infixl_definition
    ("float_sub",
     Term`$float_sub a b = float (fsub(float_format) To_nearest (defloat a) (defloat b))`,
     500);

Overload "-" = Term`$float_sub`

val float_mul = new_infixl_definition (
  "float_mul",
  Term`$float_mul a b = float (fmul(float_format) To_nearest (defloat a) (defloat b))`, 500);

Overload "*" = Term`$float_mul`

val float_div = new_infixl_definition (
  "float_div",
  Term`$float_div a b = float (fdiv(float_format) To_nearest (defloat a) (defloat b))`, 500);

Overload "/" = Term`$float_div`

val float_rem = new_infixl_definition (
  "float_rem",
  Term`$float_rem a b = float (frem(float_format) To_nearest (defloat a) (defloat b))`, 500);

Definition float_sqrt[nocompute]:
  float_sqrt(a) = float (fsqrt(float_format) To_nearest (defloat a))
End

Definition ROUNDFLOAT[nocompute]:
  ROUNDFLOAT(a) = float (fintrnd(float_format) To_nearest (defloat a))
End

Definition float_lt[nocompute]:
  float_lt a b = flt(float_format) (defloat a) (defloat b)
End
Overload "<" = “float_lt”

Definition float_le[nocompute]:
  float_le a b = fle(float_format) (defloat a) (defloat b)
End
Overload "<=" = “$float_le”

Definition float_gt[nocompute]:
  float_gt a b = fgt(float_format) (defloat a) (defloat b)
End

Overload ">" = “$float_gt`”

Definition float_ge[nocompute]:
  float_ge a b = fge(float_format) (defloat a) (defloat b)
End
Overload ">=" = “$float_ge”


Definition float_eq[nocompute]:
  float_eq (a:float) (b:float) = feq(float_format) (defloat a) (defloat b)
End
Overload "==" = Term`$float_eq`
val _ = set_fixity "==" (Infix(NONASSOC,450))

Definition float_neg[nocompute]:
  float_neg (a:float) = float (fneg (float_format) To_nearest (defloat (a:float)))
End

Overload "~" = Term`$float_neg`

Definition float_abs[nocompute]:
  float_abs a = (if a >= Plus_zero then a else (float_neg a))
End

(*---------------------------------------------------------------------------*
 * Write the theory to disk.                                                 *
 *---------------------------------------------------------------------------*)
