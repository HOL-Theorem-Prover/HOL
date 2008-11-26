
(* ========================================================================= *)
(* Formalization of IEEE-754 Standard for binary floating-point arithmetic.  *)
(* ========================================================================= *)

(*---------------------------------------------------------------------------*
 * First, make standard environment available.                               *
 *---------------------------------------------------------------------------*)
open HolKernel Parse boolLib;
infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;

(*---------------------------------------------------------------------------*
 * Next, bring in extra tools used.                                          *
 *---------------------------------------------------------------------------*)

(*app load ["realTheory", "bossLib", "pred_setTheory","transcTheory","arithmeticTheory","Num_conv"];
*)

open realTheory bossLib pred_setTheory transcTheory arithmeticTheory Num_conv;

(*---------------------------------------------------------------------------*
 * Create the theory.                                                        *
 *---------------------------------------------------------------------------*)

val _ = new_theory "ieee";

(* ------------------------------------------------------------------------- *)
(* Derived parameters for floating point formats.                            *)
(* ------------------------------------------------------------------------- *)

val expwidth = new_definition (
  "expwidth",
  --`expwidth (ew:num,fw:num) = ew`--);

val fracwidth = new_definition (
  "fracwidth",
  --`fracwidth (ew:num,fw:num) = fw`--);

val wordlength = new_definition (
  "wordlength",
  --`wordlength(X: (num#num)) = (expwidth(X) + fracwidth(X) + (1:num))`--);

val emax  = new_definition (
  "emax",
  --`emax(X: (num#num)) =  (((2:num) EXP (expwidth (X))) - (1:num))`--);

val bias = new_definition (
  "bias",
  --`bias(X: (num#num)) = ((2:num) EXP (expwidth(X) - (1:num)) - (1:num))`--);

(* ------------------------------------------------------------------------- *)
(* Predicates for the four IEEE formats.                                     *)
(* ------------------------------------------------------------------------- *)

val is_single = new_definition (
  "is_single",
  --`is_single (X: (num#num)) = (expwidth(X) = (8:num)) /\ (wordlength(X) = (32:num))`--);

val is_double = new_definition (
  "is_double",
  --`is_double(X: (num#num)) = (expwidth(X) = (11:num)) /\ (wordlength(X) = (64:num))`--);

val is_single_extended = new_definition (
  "is_single_extended",
  --`is_single_extended(X) = expwidth(X) >= (11:num) /\ wordlength(X) >= (43:num)`--);

val is_double_extended = new_definition (
  "is_double_extended",
  --`is_double_extended(X) = expwidth(X) >= (15:num) /\ wordlength(X) >= (79:num)`--);

(* ------------------------------------------------------------------------- *)
(* Extractors for fields.                                                    *)
(* ------------------------------------------------------------------------- *)

val sign = new_definition (
  "sign",
  --`sign ((s:num),(e:num),(f:num)) = (s:num)`--);

val exponent = new_definition (
  "exponent",
  --`exponent ((s:num),(e:num),(f:num)) = (e:num)`--);

val fraction = new_definition (
  "fraction",
  --`fraction ((s:num),(e:num),(f:num)) = (f:num)`--);

(* ------------------------------------------------------------------------- *)
(* Partition of numbers into disjoint classes.                               *)
(* ------------------------------------------------------------------------- *)

val is_nan = new_definition (
  "is_nan",
  --`is_nan(X: (num#num)) (a:num#num#num) =
  (exponent (a:num#num#num) = emax(X)) /\ ~(fraction (a:num#num#num) = (0:num))`--);

val is_infinity = new_definition (
  "is_infinity",
  --`is_infinity((X: num#num)) (a:num#num#num) = (exponent a = emax(X)) /\ (fraction a = (0:num))`--);

val is_normal = new_definition (
  "is_normal",
  --`is_normal(X: (num#num)) (a:num#num#num) = (((0:num) < exponent a) /\ (exponent a < emax(X)))`--);

val is_denormal = new_definition (
  "is_denormal",
  --`is_denormal(X:num#num) (a:num#num#num) = ((exponent a = (0:num)) /\ ~(fraction a = (0:num)))`--);

val is_zero = new_definition (
  "is_zero",
  --`is_zero (X:num#num) (a:num#num#num) = ((exponent a = 0) /\ (fraction a = 0))`--);

(* ------------------------------------------------------------------------- *)
(* Other useful predicates.                                                  *)
(* ------------------------------------------------------------------------- *)

val is_valid = new_definition (
  "is_valid",
  --`is_valid(X:num#num) (s:num,e:num,f:num) =
  ((s < SUC(SUC 0)) /\ (e < 2 EXP expwidth(X)) /\ (f < 2 EXP fracwidth(X)))`--);

val is_finite = new_definition (
  "is_finite",
  --`is_finite(X:num#num) (a : num#num#num) =
  ((is_valid (X) a) /\ ((is_normal(X:num#num) a) \/ (is_denormal(X:num#num) a) \/ (is_zero (X:num#num) a)))`--);

(* ------------------------------------------------------------------------- *)
(* Some special values.                                                      *)
(* ------------------------------------------------------------------------- *)

val plus_infinity = new_definition (
  "plus_infinity",
  --`plus_infinity(X:num#num) = (0:num,emax(X),0:num)`--);

val minus_infinity = new_definition (
  "minus_infinity",
  --`minus_infinity(X:num#num) = (1:num,emax(X),0:num)`--);

val plus_zero = new_definition (
  "plus_zero",
  --`plus_zero(X:num#num) = (0:num,0:num,0:num)`--);

val minus_zero = new_definition (
  "minus_zero",
  --`minus_zero(X:num#num) = (1:num,0:num,0:num)`--);

val topfloat = new_definition  (
  "topfloat",
  --`topfloat(X) = (0:num, (emax (X:num#num) - (1:num)) , (2 EXP fracwidth(X) - (1:num)))`--);

val bottomfloat = new_definition (
  "bottomfloat",
  --`bottomfloat (X:num#num) = ((1:num), (emax(X) - 1) , (2 EXP fracwidth(X) - 1))`--);

(* ------------------------------------------------------------------------- *)
(* Negation operation on floating point values.                              *)
(* ------------------------------------------------------------------------- *)

val minus = new_definition (
  "minus",
  --`minus(X:num#num) (a : num#num#num)= ((1 - sign(a)),exponent(a),fraction(a))`--);

(* ------------------------------------------------------------------------- *)
(* Concrete encodings (at least valid for single and double).                *)
(* ------------------------------------------------------------------------- *)

val encoding = new_definition (
  "encoding",
  --`encoding(X:num#num) (s:num,e:num,f:num) =
  ((s * 2 EXP (wordlength(X) - 1)) + (e * 2 EXP fracwidth(X)) + f)`--);

(* ------------------------------------------------------------------------- *)
(* Real number valuations.                                                   *)
(* ------------------------------------------------------------------------- *)

val valof = new_definition (
  "valof",
  --`valof (X:num#num) (s:num,e:num,f:num) =
  (if (e = 0) then  ~(&1) pow s * (&2 / &2 pow bias(X)) * (&f / &2 pow (fracwidth(X)))
    else  ~(&1) pow s * (&2 pow e / &2 pow bias(X)) * (&1 + &f / &2 pow fracwidth(X)))`--);

(* ------------------------------------------------------------------------- *)
(* A few handy values.                                                       *)
(* ------------------------------------------------------------------------- *)

val largest = new_definition
  ("largest",
  --`largest(X:num#num) = (&2 pow (emax(X) - 1) / &2 pow bias(X)) * (&2 - inv(&2 pow fracwidth(X)))`--);

val threshold = new_definition (
  "threshold",
  --`threshold(X:num#num) = (&2 pow (emax(X) - 1) / &2 pow bias(X)) * (&2 - inv(&2 pow SUC(fracwidth(X))))`--);

val ulp = new_definition (
  "ulp",
  --`ulp(X:num#num) (a :num#num#num) = valof(X) (0,exponent(a),1) - valof(X) (0,exponent(a),0)`--);

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

val is_closest = new_definition (
  "is_closest",
  --`is_closest (v) (s) (x) (a) = (a IN s) /\ (!b. (b IN s) ==> abs(v(a) - x) <= abs(v(b) - x))`--);

(* ------------------------------------------------------------------------- *)
(* Best approximation with a deciding preference for multiple possibilities. *)
(* ------------------------------------------------------------------------- *)

val closest = new_definition (
  "closest",
  --`closest (v) (p) (s) (x) = @(a). is_closest v s x a /\
  ((?b. is_closest v s x b /\ p(b)) ==> p(a))`--);

(* ------------------------------------------------------------------------- *)
(* Rounding to floating point formats.                                       *)
(* ------------------------------------------------------------------------- *)

val round = TotalDefn.Define `(round(X:num#num) (To_nearest) (x:real) =
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
  { a | is_finite(X) a /\ valof(X) a <= x } x)`;

(* ------------------------------------------------------------------------- *)
(* Rounding to integer values in floating point format.                      *)
(* ------------------------------------------------------------------------- *)

val is_integral = new_definition ("is_integral",
  --`is_integral(X:num#num) (a:(num#num#num)) = is_finite(X) a /\ ?n. abs(valof(X) a) = &n`--);

val intround = TotalDefn.Define `(intround(X:num#num) (To_nearest) (x:real) =
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
  { a | is_integral(X) a /\ valof(X) a <= x } x))`;

(* ------------------------------------------------------------------------- *)
(* A hack for our (non-standard) treatment of NaNs.                          *)
(* ------------------------------------------------------------------------- *)

val some_nan = new_definition (
  "some_nan",
  --`some_nan(X:num#num) = @(a:num#num#num). is_nan(X) a`--);

(* ------------------------------------------------------------------------- *)
(* Coercion for signs of zero results.                                       *)
(* ------------------------------------------------------------------------- *)

val zerosign = new_definition (
  "zerosign",
  --`zerosign (X:num#num) (s:num) (a:num#num#num) = (if (is_zero(X) a) then
  (if (s = 0) then plus_zero(X) else minus_zero(X)) else a)`--);

(* ------------------------------------------------------------------------- *)
(* Useful mathematical operations not already in the HOL Light core.         *)
(* ------------------------------------------------------------------------- *)

val rem = new_infixl_definition (
  "rem", Term`$rem x y = let n = closest I (\x. ?n. EVEN(n) /\ (abs(x) = &n))
  { x | ?n. abs(x) = &n } (x / y) in x - n * y`, 500);

(* ------------------------------------------------------------------------- *)
(* Definitions of the arithmetic operations.                                 *)
(* ------------------------------------------------------------------------- *)

val fintrnd = new_definition (
  "fintrnd",
  --`fintrnd(X:num#num) (m:roundmode) (a:num#num#num) =
  if is_nan(X) a then some_nan(X)
    else if is_infinity(X) a then a
      else zerosign(X) (sign(a)) (intround(X) m (valof(X) a))`--);

val fadd = new_definition (
  "fadd",
  --`fadd(X:num#num) (m:roundmode) (a:num#num#num) (b:num#num#num) =
  if (is_nan(X) a) \/ (is_nan(X) b) \/ ((is_infinity(X) a) /\ (is_infinity(X) b) /\ (~(sign(a) = sign(b)))) then (some_nan(X))
  else if is_infinity(X) a then a
  else if is_infinity(X) b then b
  else zerosign(X) (if is_zero(X) a /\ is_zero(X) b /\ (sign(a) = sign(b)) then sign(a) else if (m = To_ninfinity) then 1 else 0) (round(X) m (valof(X) a + valof(X) b))`--);

val fsub = new_definition (
  "fsub",
  --`fsub(X:num#num) (m:roundmode) (a:num#num#num) (b:num#num#num) =
  (if is_nan(X) a \/ is_nan(X) b \/ (is_infinity(X) a /\ is_infinity(X) b /\ (sign(a) = sign(b))) then some_nan(X)
   else if is_infinity(X) a then a
   else if is_infinity(X) b then minus(X) b
   else zerosign(X) (if is_zero(X) a /\ is_zero(X) b /\ ~(sign(a) = sign(b)) then sign(a) else if m = To_ninfinity then 1 else 0) (round(X) m (valof(X) a - valof(X) b)))`--);

val fmul =  new_definition (
  "fmul",
  --`fmul(X:num#num) (m:roundmode) (a:num#num#num) (b:num#num#num) =
  (if is_nan(X) a \/ is_nan(X) b \/ is_zero(X) a /\ is_infinity(X) b \/ is_infinity(X) a /\ is_zero(X) b then some_nan(X)
   else if is_infinity(X) a \/ is_infinity(X) b then (if sign(a) = sign(b) then plus_infinity(X) else minus_infinity(X))
   else zerosign(X) (if sign(a) = sign(b) then 0 else 1) (round(X) m (valof(X) a * valof(X) b)))`--);

val fdiv = new_definition (
  "fdiv",
  --`fdiv(X:num#num) (m:roundmode) (a:num#num#num) (b:num#num#num) =
  (if is_nan(X) a \/ is_nan(X) b \/ is_zero(X) a /\ is_zero(X) b \/ is_infinity(X) a /\ is_infinity(X) b then some_nan(X)
   else if is_infinity(X) a \/ is_zero(X) b then (if sign(a) = sign(b) then plus_infinity(X) else minus_infinity(X))
   else if is_infinity(X) b then (if sign(a) = sign(b) then plus_zero(X) else minus_zero(X))
   else zerosign(X) (if sign(a) = sign(b) then 0 else 1) (round(X) m (valof(X) a / valof(X) b)))`--);

val fsqrt = new_definition ("fsqrt",
  --`fsqrt (X:num#num) (m:roundmode) (a:num#num#num) =
  (if is_nan(X) a then some_nan(X)
   else if is_zero(X) a \/ is_infinity(X) a /\ (sign(a) = 0) then a
   else if (sign(a) = 1) then some_nan(X)
   else zerosign(X) (sign(a)) (round(X) m (sqrt(valof(X) a))))`--);


val frem = new_definition ("frem",
  --`frem(X:num#num) (m:roundmode) (a:num#num#num) (b:num#num#num) =
  (if is_nan(X) a \/ is_nan(X) b \/ is_infinity(X) a \/ is_zero(X) b then some_nan(X)
   else if is_infinity(X) b then a
   else zerosign(X) (sign(a)) (round(X) m (valof(X) a rem valof(X) b)))`--);

(* ------------------------------------------------------------------------- *)
(* Negation is specially simple.                                             *)
(* ------------------------------------------------------------------------- *)

val fneg = new_definition (
  "fneg",
  --`fneg(X:num#num) (m:roundmode) (a:num#num#num) = (((1:num)-sign(a)),(exponent(a)),(fraction(a)))`--);

(* ------------------------------------------------------------------------- *)
(* Comparison codes.                                                         *)
(* ------------------------------------------------------------------------- *)

val ccode =  Hol_datatype `
  ccode = Gt
    | Lt
      | Eq
        | Un`;

(* ------------------------------------------------------------------------- *)
(* Comparison operations.                                                    *)
(* ------------------------------------------------------------------------- *)

val fcompare = new_definition (
  "fcompare",
  --`fcompare(X) a b =
  (if is_nan(X) a \/ is_nan(X) b then Un
   else if is_infinity(X) a /\ (sign(a) = 1) then (if is_infinity(X) b /\ (sign(b) = 1) then Eq else Lt)
   else if is_infinity(X) a /\ (sign(a) = 0) then (if is_infinity(X) b /\ (sign(b) = 0) then Eq else Gt)
   else if is_infinity(X) b /\ (sign(b) = 1) then Gt
   else if is_infinity(X) b /\ (sign(b) = 0) then Lt
   else if valof(X) a < valof(X) b then Lt
   else if valof(X) a = valof(X) b then Eq
   else Gt)`--);

val flt = new_definition (
  "flt",
  --`flt(X) a b = (fcompare(X) a b = Lt)`--);

val fle = new_definition (
  "fle",
  --`fle(X) a b = (fcompare(X) a b = Lt) \/ (fcompare(X) a b = Eq)`--);

val fgt = new_definition (
  "fgt",
  --`fgt(X) a b = (fcompare(X) a b = Gt)`--);

val fge = new_definition (
  "fge",
  --`fge(X) a b = (fcompare(X) a b = Gt) \/ (fcompare(X) a b = Eq)`--);

val feq = new_definition (
  "feq",
  --`feq (X) a b = (fcompare(X) a b = Eq)`--);

(* ------------------------------------------------------------------------- *)
(* Actual float type with round-to-even.                                     *)
(* ------------------------------------------------------------------------- *)

val float_format = new_definition (
  "float_format",
  --`float_format = ((8:num),(23:num))`--);

val float_tybij = define_new_type_bijections {
  name="float_tybij",
  ABS="float",
  REP="defloat",
  tyax =new_type_definition ("float",
  Q.prove (`(?a. (is_valid float_format a))`,
  EXISTS_TAC (--`0:num,0:num,0:num`-- ) THEN
  REWRITE_TAC[float_format, is_valid, GSYM NOT_LESS_EQUAL,
  LE, num_CONV(--`2:num`--), NOT_EXP_0, GSYM SUC_NOT]))};

val Val = new_definition (
  "Val",
  --`Val a = valof(float_format) (defloat a)`--);

val Float = new_definition (
  "Float",
  --`Float(x) = float (round(float_format) To_nearest x)`--);

val Sign = new_definition (
  "Sign",
  --`Sign(a) = sign(defloat a)`--);

val Exponent = new_definition (
  "Exponent",
  --`Exponent(a) = exponent(defloat a)`--);

val Fraction = new_definition (
  "Fraction",
  --`Fraction(a) = fraction(defloat a)`--);

val Ulp = new_definition (
  "Ulp",
  --`Ulp(a) = ulp(float_format) (defloat a)`--);

(* ------------------------------------------------------------------------- *)
(* Lifting of the discriminator functions.                                   *)
(* ------------------------------------------------------------------------- *)

val Isnan = new_definition (
  "Isnan",
  --`Isnan(a) = is_nan(float_format) (defloat a)`--);

val Infinity = new_definition (
  "Infinity",
  --`Infinity(a) = is_infinity(float_format) (defloat a)`--);

val Isnormal = new_definition (
  "Isnormal",
  --`Isnormal(a) = is_normal(float_format) (defloat a)`--);

val Isdenormal = new_definition (
  "Isdenormal",
  --`Isdenormal(a) = is_denormal(float_format) (defloat a)`--);

val Iszero = new_definition (
  "Iszero",
  --`Iszero(a) = is_zero(float_format) (defloat a)`--);

val Finite = new_definition (
  "Finite",
  --`Finite(a) = Isnormal(a) \/ Isdenormal(a) \/ Iszero(a)`--);

val Isintegral = new_definition (
  "Isintegral",
  --`Isintegral(a) = is_integral(float_format) (defloat a)`--);

(* ------------------------------------------------------------------------- *)
(* Basic operations on floats.                                               *)
(* ------------------------------------------------------------------------- *)

val Plus_zero = new_definition (
  "Plus_zero",
  --`Plus_zero = float (plus_zero(float_format))`--);

val Minus_zero = new_definition (
  "Minus_zero",
  --`Minus_zero = float (minus_zero(float_format))`--);

val Minus_infinity = new_definition (
  "Minus_infinity",
  --`Minus_infinity = float (minus_infinity(float_format))`--);

val Plus_infinity = new_definition (
  "Plus_infinity",
  --`Plus_infinity = float (plus_infinity(float_format))`--);

val float_add = new_infixl_definition (
  "float_add",
  Term`$float_add a b = float (fadd(float_format) To_nearest (defloat a) (defloat b))`, 500);

val _ = overload_on ("+", Term`$float_add`);

val float_sub =
    new_infixl_definition
    ("float_sub",
     Term`$float_sub a b = float (fsub(float_format) To_nearest (defloat a) (defloat b))`,
     500);

val _ = overload_on ("-", Term`$float_sub`);

val float_mul = new_infixl_definition (
  "float_mul",
  Term`$float_mul a b = float (fmul(float_format) To_nearest (defloat a) (defloat b))`, 500);

val _ = overload_on ("*", Term`$float_mul`);

val float_div = new_infixl_definition (
  "float_div",
  Term`$float_div a b = float (fdiv(float_format) To_nearest (defloat a) (defloat b))`, 500);

val _ = overload_on ("/", Term`$float_div`);

val float_rem = new_infixl_definition (
  "float_rem",
  Term`$float_rem a b = float (frem(float_format) To_nearest (defloat a) (defloat b))`, 500);

val float_sqrt = new_definition (
  "float_sqrt",
  --`float_sqrt(a) = float (fsqrt(float_format) To_nearest (defloat a))`--);

val ROUNDFLOAT = new_definition (
  "ROUNDFLOAT",
  (--`ROUNDFLOAT(a) = float (fintrnd(float_format) To_nearest (defloat a))`--));

val float_lt = new_definition (
  "float_lt",
  Term `float_lt a b = flt(float_format) (defloat a) (defloat b)`);
val _ = overload_on ("<", Term`float_lt`);

val float_le = new_definition (
  "float_le",
  Term `float_le a b = fle(float_format) (defloat a) (defloat b)`);
val _ = overload_on ("<=", Term`$float_le`);

val float_gt = new_definition (
  "float_gt",
  Term `float_gt a b = fgt(float_format) (defloat a) (defloat b)`);

val _ = overload_on (">", Term`$float_gt`);

val float_ge = new_definition (
  "float_ge",
  Term `float_ge a b = fge(float_format) (defloat a) (defloat b)`);
val _ = overload_on (">=", Term`$float_ge`);


val float_eq = new_definition (
  "float_eq",
  ``float_eq (a:float) (b:float) = feq(float_format) (defloat a) (defloat b)``);
val _ = overload_on ("==", Term`$float_eq`)
val _ = set_fixity "==" (Infix(NONASSOC,450))

val float_neg = new_definition (
  "float_neg",
  --`float_neg (a:float) = float (fneg (float_format) To_nearest (defloat (a:float)))`--);

val _ = overload_on ("~", Term`$float_neg`);

val float_abs = new_definition (
  "float_abs",
  --`float_abs a = (if a >= Plus_zero then a else (float_neg a))`--);

(*---------------------------------------------------------------------------*
 * Write the theory to disk.                                                 *
 *---------------------------------------------------------------------------*)

val _ = export_theory();
