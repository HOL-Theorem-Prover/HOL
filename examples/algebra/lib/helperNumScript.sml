(* ------------------------------------------------------------------------- *)
(* Helper Theorems - a collection of useful results -- for Numbers.          *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "helperNum";

(* ------------------------------------------------------------------------- *)


(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory;

(* val _ = load "dividesTheory"; *)
(* val _ = load "gcdTheory"; *)
open arithmeticTheory dividesTheory
open gcdTheory; (* for P_EUCLIDES *)


(* ------------------------------------------------------------------------- *)
(* HelperNum Documentation                                                   *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   SQ n           = n * n
   HALF n         = n DIV 2
   TWICE n        = 2 * n
   n divides m    = divides n m
   coprime x y    = gcd x y = 1
*)
(* Definitions and Theorems (# are exported):

   Arithmetic Theorems:
   THREE             |- 3 = SUC 2
   FOUR              |- 4 = SUC 3
   FIVE              |- 5 = SUC 4
   num_nchotomy      |- !m n. m = n \/ m < n \/ n < m
   ZERO_LE_ALL       |- !n. 0 <= n
   NOT_ZERO          |- !n. n <> 0 <=> 0 < n
   ONE_NOT_0         |- 1 <> 0
   ONE_LT_POS        |- !n. 1 < n ==> 0 < n
   ONE_LT_NONZERO    |- !n. 1 < n ==> n <> 0
   NOT_LT_ONE        |- !n. ~(1 < n) <=> (n = 0) \/ (n = 1)
   NOT_ZERO_GE_ONE   |- !n. n <> 0 <=> 1 <= n
   LE_ONE            |- !n. n <= 1 <=> (n = 0) \/ (n = 1)
   LESS_SUC          |- !n. n < SUC n
   PRE_LESS          |- !n. 0 < n ==> PRE n < n
   SUC_EXISTS        |- !n. 0 < n ==> ?m. n = SUC m
   SUC_POS           |- !n. 0 < SUC n
   SUC_NOT_ZERO      |- !n. SUC n <> 0
   ONE_NOT_ZERO      |- 1 <> 0
   SUC_ADD_SUC       |- !m n. SUC m + SUC n = m + n + 2
   SUC_MULT_SUC      |- !m n. SUC m * SUC n = m * n + m + n + 1
   SUC_EQ            |- !m n. (SUC m = SUC n) <=> (m = n)
   TWICE_EQ_0        |- !n. (TWICE n = 0) <=> (n = 0)
   SQ_EQ_0           |- !n. (SQ n = 0) <=> (n = 0)
   SQ_EQ_1           |- !n. (SQ n = 1) <=> (n = 1)
   MULT3_EQ_0        |- !x y z. (x * y * z = 0) <=> ((x = 0) \/ (y = 0) \/ (z = 0))
   MULT3_EQ_1        |- !x y z. (x * y * z = 1) <=> ((x = 1) /\ (y = 1) /\ (z = 1))
   SQ_0              |- 0 ** 2 = 0
   EXP_2_EQ_0        |- !n. (n ** 2 = 0) <=> (n = 0)
   LE_MULT_LCANCEL_IMP |- !m n p. n <= p ==> m * n <= m * p

   Maximum and minimum:
   MAX_ALT           |- !m n. MAX m n = if m <= n then n else m
   MIN_ALT           |- !m n. MIN m n = if m <= n then m else n
   MAX_SWAP          |- !f. (!x y. x <= y ==> f x <= f y) ==> !x y. f (MAX x y) = MAX (f x) (f y)
   MIN_SWAP          |- !f. (!x y. x <= y ==> f x <= f y) ==> !x y. f (MIN x y) = MIN (f x) (f y)
   SUC_MAX           |- !m n. SUC (MAX m n) = MAX (SUC m) (SUC n)
   SUC_MIN           |- !m n. SUC (MIN m n) = MIN (SUC m) (SUC n)
   MAX_SUC           |- !m n. MAX (SUC m) (SUC n) = SUC (MAX m n)
   MIN_SUC           |- !m n. MIN (SUC m) (SUC n) = SUC (MIN m n)
   MAX_LESS          |- !x y n. x < n /\ y < n ==> MAX x y < n
   MAX_CASES         |- !m n. (MAX n m = n) \/ (MAX n m = m)
   MIN_CASES         |- !m n. (MIN n m = n) \/ (MIN n m = m)
   MAX_EQ_0          |- !m n. (MAX n m = 0) <=> (n = 0) /\ (m = 0)
   MIN_EQ_0          |- !m n. (MIN n m = 0) <=> (n = 0) \/ (m = 0)
   MAX_IS_MAX        |- !m n. m <= MAX m n /\ n <= MAX m n
   MIN_IS_MIN        |- !m n. MIN m n <= m /\ MIN m n <= n
   MAX_ID            |- !m n. MAX (MAX m n) n = MAX m n /\ MAX m (MAX m n) = MAX m n
   MIN_ID            |- !m n. MIN (MIN m n) n = MIN m n /\ MIN m (MIN m n) = MIN m n
   MAX_LE_PAIR       |- !a b c d. a <= b /\ c <= d ==> MAX a c <= MAX b d
   MIN_LE_PAIR       |- !a b c d. a <= b /\ c <= d ==> MIN a c <= MIN b d
   MAX_ADD           |- !a b c. MAX a (b + c) <= MAX a b + MAX a c
   MIN_ADD           |- !a b c. MIN a (b + c) <= MIN a b + MIN a c
   MAX_1_POS         |- !n. 0 < n ==> MAX 1 n = n
   MIN_1_POS         |- !n. 0 < n ==> MIN 1 n = 1
   MAX_LE_SUM        |- !m n. MAX m n <= m + n
   MIN_LE_SUM        |- !m n. MIN m n <= m + n
   MAX_1_EXP         |- !n m. MAX 1 (m ** n) = MAX 1 m ** n
   MIN_1_EXP         |- !n m. MIN 1 (m ** n) = MIN 1 m ** n

   Arithmetic Manipulations:
   MULT_POS          |- !m n. 0 < m /\ 0 < n ==> 0 < m * n
   MULT_COMM_ASSOC   |- !m n p. m * (n * p) = n * (m * p)
   MULT_RIGHT_CANCEL |- !m n p. (n * p = m * p) <=> (p = 0) \/ (n = m)
   MULT_LEFT_CANCEL  |- !m n p. (p * n = p * m) <=> (p = 0) \/ (n = m)
   MULT_TO_DIV       |- !m n. 0 < n ==> (n * m DIV n = m)
   MULT_ASSOC_COMM   |- !m n p. m * (n * p) = m * p * n
   MULT_LEFT_ID      |- !n. 0 < n ==> !m. (m * n = n) <=> (m = 1)
   MULT_RIGHT_ID     |- !n. 0 < n ==> !m. (n * m = n) <=> (m = 1)
   MULT_EQ_SELF      |- !n. 0 < n ==> !m. (n * m = n) <=> (m = 1)
   SQ_EQ_SELF        |- !n. (n * n = n) <=> (n = 0) \/ (n = 1)
   EXP_EXP_BASE_LE   |- !b c m n. m <= n /\ 0 < c ==> b ** c ** m <= b ** c ** n
   EXP_EXP_LE_MONO_IMP |- !a b n. a <= b ==> a ** n <= b ** n
   EXP_BY_ADD_SUB_LE |- !m n. m <= n ==> !p. p ** n = p ** m * p ** (n - m)
   EXP_BY_ADD_SUB_LT |- !m n. m < n ==> !p. p ** n = p ** m * p ** (n - m)
   EXP_SUC_DIV       |- !m n. 0 < m ==> m ** SUC n DIV m = m ** n
   SELF_LE_SQ        |- !n. n <= n ** 2
   LE_MONO_ADD2      |- !a b c d. a <= b /\ c <= d ==> a + c <= b + d
   LT_MONO_ADD2      |- !a b c d. a < b /\ c < d ==> a + c < b + d
   LE_MONO_MULT2     |- !a b c d. a <= b /\ c <= d ==> a * c <= b * d
   LT_MONO_MULT2     |- !a b c d. a < b /\ c < d ==> a * c < b * d
   SUM_LE_PRODUCT    |- !m n. 1 < m /\ 1 < n ==> m + n <= m * n
   MULTIPLE_SUC_LE   |- !n k. 0 < n ==> k * n + 1 <= (k + 1) * n

   Simple Theorems:
   ADD_EQ_2          |- !m n. 0 < m /\ 0 < n /\ (m + n = 2) ==> (m = 1) /\ (n = 1)
   EVEN_0            |- EVEN 0
   ODD_1             |- ODD 1
   EVEN_2            |- EVEN 2
   EVEN_SQ           |- !n. EVEN (n ** 2) <=> EVEN n
   ODD_SQ            |- !n. ODD (n ** 2) <=> ODD n
   EQ_PARITY         |- !a b. EVEN (2 * a + b) <=> EVEN b
   ODD_MOD2          |- !x. ODD x <=> (x MOD 2 = 1)
   EVEN_ODD_SUC      |- !n. (EVEN n <=> ODD (SUC n)) /\ (ODD n <=> EVEN (SUC n))
   EVEN_ODD_PRE      |- !n. 0 < n ==> (EVEN n <=> ODD (PRE n)) /\ (ODD n <=> EVEN (PRE n))
   EVEN_PARTNERS     |- !n. EVEN (n * (n + 1))
   EVEN_HALF         |- !n. EVEN n ==> (n = 2 * HALF n)
   ODD_HALF          |- !n. ODD n ==> (n = 2 * HALF n + 1)
   EVEN_SUC_HALF     |- !n. EVEN n ==> (HALF (SUC n) = HALF n)
   ODD_SUC_HALF      |- !n. ODD n ==> (HALF (SUC n) = SUC (HALF n))
   HALF_EQ_0         |- !n. (HALF n = 0) <=> (n = 0) \/ (n = 1)
   HALF_EQ_SELF      |- !n. (HALF n = n) <=> (n = 0)
   HALF_LT           |- !n. 0 < n ==> HALF n < n
   HALF_ADD1_LT      |- !n. 2 < n ==> 1 + HALF n < n
   HALF_TWICE        |- !n. HALF (TWICE n) = n
   HALF_MULT         |- !m n. n * HALF m <= HALF (n * m)
   TWO_HALF_LE_THM   |- !n. 2 * HALF n <= n /\ n <= SUC (2 * HALF n)
   TWO_HALF_TIMES_LE |- !m n. TWICE (HALF n * m) <= n * m
   HALF_ADD1_LE      |- !n. 0 < n ==> 1 + HALF n <= n
   HALF_SQ_LE        |- !n. HALF n ** 2 <= n ** 2 DIV 4
   HALF_LE           |- !n. HALF n <= n
   HALF_LE_MONO      |- !x y. x <= y ==> HALF x <= HALF y
   HALF_SUC          |- !n. HALF (SUC n) <= n
   HALF_SUC_SUC      |- !n. 0 < n ==> HALF (SUC (SUC n)) <= n
   HALF_SUC_LE       |- !n m. n < HALF (SUC m) ==> 2 * n + 1 <= m
   HALF_EVEN_LE      |- !n m. 2 * n < m ==> n <= HALF m
   HALF_ODD_LT       |- !n m. 2 * n + 1 < m ==> n < HALF m
   MULT_EVEN         |- !n. EVEN n ==> !m. m * n = TWICE m * HALF n
   MULT_ODD          |- !n. ODD n ==> !m. m * n = m + TWICE m * HALF n
   EVEN_MOD_EVEN     |- !m. EVEN m /\ m <> 0 ==> !n. EVEN n <=> EVEN (n MOD m)
   EVEN_MOD_ODD      |- !m. EVEN m /\ m <> 0 ==> !n. ODD n <=> ODD (n MOD m)

   SUB_SUB_SUB           |- !a b c. c <= a ==> (a - b - (a - c) = c - b)
   ADD_SUB_SUB           |- !a b c. c <= a ==> (a + b - (a - c) = c + b)
   SUB_EQ_ADD            |- !p. 0 < p ==> !m n. (m - n = p) <=> (m = n + p)
   MULT_EQ_LESS_TO_MORE  |- !a b c d. 0 < a /\ 0 < b /\ a < c /\ (a * b = c * d) ==> d < b
   LE_IMP_REVERSE_LT     |- !a b c d. 0 < c /\ 0 < d /\ a * b <= c * d /\ d < b ==> a < c

   Exponential Theorems:
   EXP_0             |- !n. n ** 0 = 1
   EXP_2             |- !n. n ** 2 = n * n
   EXP_NONZERO       |- !m n. m <> 0 ==> m ** n <> 0
   EXP_POS           |- !m n. 0 < m ==> 0 < m ** n
   EXP_EQ_SELF       |- !n m. 0 < m ==> (n ** m = n) <=> (m = 1) \/ (n = 0) \/ (n = 1)
   EXP_LE            |- !n b. 0 < n ==> b <= b ** n
   EXP_LT            |- !n b. 1 < b /\ 1 < n ==> b < b ** n
   EXP_LCANCEL       |- !a b c n m. 0 < a /\ n < m /\ (a ** n * b = a ** m * c) ==> ?d. 0 < d /\ (b = a ** d * c)
   EXP_RCANCEL       |- !a b c n m. 0 < a /\ n < m /\ (b * a ** n = c * a ** m) ==> ?d. 0 < d /\ (b = c * a ** d)
   ONE_LE_EXP        |- !m n. 0 < m ==> 1 <= m ** n
   EXP_EVEN          |- !n. EVEN n ==> !m. m ** n = SQ m ** HALF n
   EXP_ODD           |- !n. ODD n ==> !m. m ** n = m * SQ m ** HALF n
   EXP_THM           |- !m n. m ** n =
                              if n = 0 then 1 else if n = 1 then m
                              else if EVEN n then SQ m ** HALF n
                                   else m * SQ m ** HALF n
   EXP_EQN           |- !m n. m ** n =
                              if n = 0 then 1
                              else if EVEN n then SQ m ** HALF n
                              else m * SQ m ** HALF n
   EXP_EQN_ALT       |- !m n. m ** n =
                              if n = 0 then 1 else (if EVEN n then 1 else m) * SQ m ** HALF n
   EXP_ALT_EQN       |- !m n. m ** n =
                              if n = 0 then 1 else (if EVEN n then 1 else m) * (m ** 2) ** HALF n
   EXP_MOD_EQN       |- !b n m. 1 < m ==>
                                (b ** n MOD m =
                                 if n = 0 then 1
                                 else (let result = SQ b ** HALF n MOD m
                                        in if EVEN n then result else (b * result) MOD m))
   EXP_MOD_ALT       |- !b n m. 1 < m ==>
                                (b ** n MOD m =
                                 if n = 0 then 1
                                 else ((if EVEN n then 1 else b) * SQ b ** HALF n MOD m) MOD m)
   EXP_EXP_SUC       |- !x y n. x ** y ** SUC n = (x ** y) ** y ** n
   EXP_LOWER_LE_LOW  |- !n m. 1 + n * m <= (1 + m) ** n
   EXP_LOWER_LT_LOW  |- !n m. 0 < m /\ 1 < n ==> 1 + n * m < (1 + m) ** n
   EXP_LOWER_LE_HIGH |- !n m. n * m ** (n - 1) + m ** n <= (1 + m) ** n
   SUC_X_LT_2_EXP_X  |- !n. 1 < n ==> SUC n < 2 ** n

   DIVIDES Theorems:
   DIV_EQUAL_0       |- !m n. 0 < n ==> ((m DIV n = 0) <=> m < n)
   DIV_POS           |- !m n. 0 < m /\ m <= n ==> 0 < n DIV m
   DIV_EQ            |- !x y z. 0 < z ==> (x DIV z = y DIV z <=> x - x MOD z = y - y MOD z)
   ADD_DIV_EQ        |- !n a b. a MOD n + b < n ==> (a + b) DIV n = a DIV n
   DIV_LE            |- !x y z. 0 < y /\ x <= y * z ==> x DIV y <= z
   DIV_SOLVE         |- !n. 0 < n ==> !x y. (x * n = y) ==> (x = y DIV n)
   DIV_SOLVE_COMM    |- !n. 0 < n ==> !x y. (n * x = y) ==> (x = y DIV n)
   ONE_DIV           |- !n. 1 < n ==> (1 DIV n = 0)
   DIVIDES_ODD       |- !n. ODD n ==> !m. m divides n ==> ODD m
   DIVIDES_EVEN      |- !m. EVEN m ==> !n. m divides n ==> EVEN n
   EVEN_ALT          |- !n. EVEN n <=> 2 divides n
   ODD_ALT           |- !n. ODD n <=> ~(2 divides n)

   DIV_MULT_LE       |- !n. 0 < n ==> !q. q DIV n * n <= q
   DIV_MULT_EQ       |- !n. 0 < n ==> !q. n divides q <=> (q DIV n * n = q)
   DIV_MULT_LESS_EQ  |- !m n. 0 < m ==> m * (n DIV m) <= n /\ n < m * SUC (n DIV m)
   DIV_LE_MONOTONE_REVERSE  |- !x y. 0 < x /\ 0 < y /\ x <= y ==> !n. n DIV y <= n DIV x
   DIVIDES_EQN       |- !n. 0 < n ==> !m. n divides m <=> (m = m DIV n * n)
   DIVIDES_EQN_COMM  |- !n. 0 < n ==> !m. n divides m <=> (m = n * (m DIV n))
   SUB_DIV           |- !m n. 0 < n /\ n <= m ==> ((m - n) DIV n = m DIV n - 1)
   SUB_DIV_EQN       |- !m n. 0 < n ==> ((m - n) DIV n = if m < n then 0 else m DIV n - 1)
   SUB_MOD_EQN       |- !m n. 0 < n ==> ((m - n) MOD n = if m < n then 0 else m MOD n)
   DIV_EQ_MULT       |- !n. 0 < n ==> !k m. (m MOD n = 0) ==> ((k * n = m) <=> (k = m DIV n))
   MULT_LT_DIV       |- !n. 0 < n ==> !k m. (m MOD n = 0) ==> (k * n < m <=> k < m DIV n)
   LE_MULT_LE_DIV    |- !n. 0 < n ==> !k m. (m MOD n = 0) ==> (m <= n * k <=> m DIV n <= k)
   DIV_MOD_EQ_0      |- !m n. 0 < m ==> (n DIV m = 0 /\ n MOD m = 0 <=> n = 0)
   DIV_LT_SUC        |- !m n. 0 < m /\ 0 < n /\ n MOD m = 0 ==> n DIV SUC m < n DIV m
   DIV_LT_MONOTONE_REVERSE  |- !x y. 0 < x /\ 0 < y /\ x < y ==>
                               !n. 0 < n /\ n MOD x = 0 ==> n DIV y < n DIV x

   EXP_DIVIDES            |- !a b n. 0 < n /\ a ** n divides b ==> a divides b
   DIVIDES_EXP_BASE       |- !a b n. prime a /\ 0 < n ==> (a divides b <=> a divides (b ** n))
   DIVIDES_MULTIPLE       |- !m n. n divides m ==> !k. n divides (k * m)
   DIVIDES_MULTIPLE_IFF   |- !m n k. k <> 0 ==> (m divides n <=> k * m divides k * n)
   DIVIDES_FACTORS        |- !m n. 0 < n /\ n divides m ==> (m = n * (m DIV n))
   DIVIDES_COFACTOR       |- !m n. 0 < n /\ n divides m ==> (m DIV n) divides m
   MULTIPLY_DIV           |- !n p q. 0 < n /\ n divides q ==> (p * (q DIV n) = p * q DIV n)
   DIVIDES_MOD_MOD        |- !m n. 0 < n /\ m divides n ==> !x. x MOD n MOD m = x MOD m
   DIVIDES_CANCEL         |- !k. 0 < k ==> !m n. m divides n <=> (m * k) divides (n * k)
   DIVIDES_CANCEL_COMM    |- !a b k. a divides b ==> (k * a) divides (k * b)
   DIV_COMMON_FACTOR      |- !m n. 0 < n /\ 0 < m ==> !x. n divides x ==> (m * x DIV (m * n) = x DIV n)
   DIV_DIV_MULT           |- !m n x. 0 < n /\ 0 < m /\ 0 < m DIV n /\ n divides m /\ m divides x /\
                                     (m DIV n) divides x ==> (x DIV (m DIV n) = n * (x DIV m))

   Basic Divisibility:
   divides_iff_equal   |- !m n. 0 < n /\ n < 2 * m ==> (m divides n <=> n = m)
   dividend_divides_divisor_multiple
                       |- !m n. 0 < m /\ n divides m ==> !t. m divides t * n <=> m DIV n divides t
   divisor_pos         |- !m n. 0 < n /\ m divides n ==> 0 < m
   divides_pos         |- !m n. 0 < n /\ m divides n ==> 0 < m /\ m <= n
   divide_by_cofactor  |- !m n. 0 < n /\ m divides n ==> (n DIV (n DIV m) = m)
   divides_exp         |- !n. 0 < n ==> !a b. a divides b ==> a divides b ** n
   divides_linear      |- !a b c. c divides a /\ c divides b ==> !h k. c divides h * a + k * b
   divides_linear_sub  |- !a b c. c divides a /\ c divides b ==>
                          !h k d. (h * a = k * b + d) ==> c divides d
   power_divides_iff        |- !p. 1 < p ==> !m n. p ** m divides p ** n <=> m <= n
   prime_power_divides_iff  |- !p. prime p ==> !m n. p ** m divides p ** n <=> m <= n
   divides_self_power       |- !n p. 0 < n /\ 1 < p ==> p divides p ** n
   divides_eq_thm      |- !a b. a divides b /\ 0 < b /\ b < 2 * a ==> (b = a)
   factor_eq_cofactor  |- !m n. 0 < m /\ m divides n ==> (m = n DIV m <=> n = m ** 2)
   euclid_prime        |- !p a b. prime p /\ p divides a * b ==> p divides a \/ p divides b
   euclid_coprime      |- !a b c. coprime a b /\ b divides a * c ==> b divides c

   Modulo Theorems:
   MOD_EQN             |- !n. 0 < n ==> !a b. (a MOD n = b) <=> ?c. (a = c * n + b) /\ b < n
   MOD_MOD_EQN         |- !n a b. 0 < n /\ b <= a ==> (a MOD n = b MOD n <=> ?c. a = b + c * n)
   MOD_PLUS2           |- !n x y. 0 < n ==> (x + y) MOD n = (x + y MOD n) MOD n
   MOD_PLUS3           |- !n. 0 < n ==> !x y z. (x + y + z) MOD n = (x MOD n + y MOD n + z MOD n) MOD n
   MOD_ADD_ASSOC       |- !n x y z. 0 < n /\ x < n /\ y < n /\ z < n ==>
                          (((x + y) MOD n + z) MOD n = (x + (y + z) MOD n) MOD n)
   MOD_MULT_ASSOC      |- !n x y z. 0 < n /\ x < n /\ y < n /\ z < n ==>
                          (((x * y) MOD n * z) MOD n = (x * (y * z) MOD n) MOD n)
   MOD_ADD_INV         |- !n x. 0 < n /\ x < n ==> (((n - x) MOD n + x) MOD n = 0)
   MOD_MULITPLE_ZERO   |- !n k. 0 < n /\ (k MOD n = 0) ==> !x. (k * x) MOD n = 0
   MOD_EQ_DIFF         |- !n a b. 0 < n /\ (a MOD n = b MOD n) ==> ((a - b) MOD n = 0)
   MOD_EQ              |- !n a b. 0 < n /\ b <= a ==> (((a - b) MOD n = 0) <=> (a MOD n = b MOD n))
   MOD_EQ_0_IFF        |- !m n. n < m ==> ((n MOD m = 0) <=> (n = 0))
   MOD_EXP             |- !n. 0 < n ==> !a m. (a MOD n) ** m MOD n = a ** m MOD n
   mod_add_eq_sub      |- !n a b c d. b < n /\ c < n ==>
                                      ((a + b) MOD n = (c + d) MOD n <=>
                                       (a + (n - c)) MOD n = (d + (n - b)) MOD n)
   mod_add_eq_sub_eq   |- !n a b c d. 0 < n ==>
                                      ((a + b) MOD n = (c + d) MOD n <=>
                                       (a + (n - c MOD n)) MOD n = (d + (n - b MOD n)) MOD n)
   mod_divides         |- !n a b. 0 < n /\ b divides n /\ b divides a MOD n ==> b divides a
   mod_divides_iff     |- !n a b. 0 < n /\ b divides n ==> (b divides a MOD n <=> b divides a)
   mod_divides_divides |- !n a b c. 0 < n /\ a MOD n = b /\ c divides n /\ c divides a ==> c divides b
   mod_divides_divides_iff
                       |- !n a b c. 0 < n /\ a MOD n = b /\ c divides n ==>
                                    (c divides a <=> c divides b)
   mod_eq_divides      |- !n a b c. 0 < n /\ a MOD n = b MOD n /\ c divides n /\ c divides a ==>
                                    c divides b
   mod_eq_divides_iff  |- !n a b c. 0 < n /\ a MOD n = b MOD n /\ c divides n ==>
                                    (c divides a <=> c divides b)
   mod_mult_eq_mult    |- !m n a b. coprime m n /\ 0 < a /\ a < 2 * n /\ 0 < b /\ b < 2 * m /\
                                    (m * a) MOD (m * n) = (n * b) MOD (m * n) ==> a = n /\ b = m

   Even and Odd Parity:
   EVEN_EXP            |- !m n. 0 < n /\ EVEN m ==> EVEN (m ** n)
   ODD_EXP             |- !m n. 0 < n /\ ODD m ==> ODD (m ** n)
   power_parity        |- !n. 0 < n ==> !m. (EVEN m <=> EVEN (m ** n)) /\ (ODD m <=> ODD (m ** n))
   EXP_2_EVEN          |- !n. 0 < n ==> EVEN (2 ** n)
   EXP_2_PRE_ODD       |- !n. 0 < n ==> ODD (2 ** n - 1)

   Modulo Inverse:
   GCD_LINEAR          |- !j k. 0 < j ==> ?p q. p * j = q * k + gcd j k
   EUCLID_LEMMA        |- !p x y. prime p ==> (((x * y) MOD p = 0) <=> (x MOD p = 0) \/ (y MOD p = 0))
   MOD_MULT_LCANCEL    |- !p x y z. prime p /\ (x * y) MOD p = (x * z) MOD p /\ x MOD p <> 0 ==>
                                    y MOD p = z MOD p
   MOD_MULT_RCANCEL    |- !p x y z. prime p /\ (y * x) MOD p = (z * x) MOD p /\ x MOD p <> 0 ==>
                                    y MOD p = z MOD p
   MOD_MULT_INV_EXISTS |- !p x. prime p /\ 0 < x /\ x < p ==> ?y. 0 < y /\ y < p /\ ((y * x) MOD p = 1)
   MOD_MULT_INV_DEF    |- !p x. prime p /\ 0 < x /\ x < p ==>
                           0 < MOD_MULT_INV p x /\ MOD_MULT_INV p x < p /\ ((MOD_MULT_INV p x * x) MOD p = 1)

   FACTOR Theorems:
   PRIME_FACTOR_PROPER |- !n. 1 < n /\ ~prime n ==> ?p. prime p /\ p < n /\ (p divides n)
   FACTOR_OUT_POWER    |- !n p. 0 < n /\ 1 < p /\ p divides n ==>
                                ?m. (p ** m) divides n /\ ~(p divides (n DIV p ** m))

   Useful Theorems:
   binomial_add         |- !a b. (a + b) ** 2 = a ** 2 + b ** 2 + 2 * a * b
   binomial_sub         |- !a b. b <= a ==> ((a - b) ** 2 = a ** 2 + b ** 2 - 2 * a * b)
   binomial_means       |- !a b. 2 * a * b <= a ** 2 + b ** 2
   binomial_sub_sum     |- !a b. b <= a ==> (a - b) ** 2 + 2 * a * b = a ** 2 + b ** 2
   binomial_sub_add     |- !a b. b <= a ==> ((a - b) ** 2 + 4 * a * b = (a + b) ** 2)
   difference_of_squares|- !a b. a ** 2 - b ** 2 = (a - b) * (a + b)
   difference_of_squares_alt
                        |- !a b. a * a - b * b = (a - b) * (a + b)
   binomial_2           |- !m n. (m + n) ** 2 = m ** 2 + n ** 2 + TWICE m * n
   SUC_SQ               |- !n. SUC n ** 2 = SUC (n ** 2) + TWICE n
   SQ_LE                |- !m n. m <= n ==> SQ m <= SQ n
   EVEN_PRIME           |- !n. EVEN n /\ prime n <=> n = 2
   ODD_PRIME            |- !n. prime n /\ n <> 2 ==> ODD n
   TWO_LE_PRIME         |- !p. prime p ==> 2 <= p
   NOT_PRIME_4          |- ~prime 4
   prime_divides_prime  |- !n m. prime n /\ prime m ==> (n divides m <=> (n = m))
   ALL_PRIME_FACTORS_MOD_EQ_1  |- !m n. 0 < m /\ 1 < n /\
                                   (!p. prime p /\ p divides m ==> (p MOD n = 1)) ==> (m MOD n = 1)
   prime_divides_power         |- !p n. prime p /\ 0 < n ==> !b. p divides b ** n <=> p divides b
   prime_divides_self_power    |- !p. prime p ==> !n. 0 < n ==> p divides p ** n
   power_eq_prime_power        |- !p. prime p ==> !b n m. 0 < m /\ (b ** n = p ** m) ==>
                                  ?k. (b = p ** k) /\ (k * n = m)
   POWER_EQ_SELF        |- !n. 1 < n ==> !m. (n ** m = n) <=> (m = 1)

   LESS_HALF_IFF        |- !n k. k < HALF n <=> k + 1 < n - k
   MORE_HALF_IMP        |- !n k. HALF n < k ==> n - k <= HALF n
   MONOTONE_MAX         |- !f m. (!k. k < m ==> f k < f (k + 1)) ==> !k. k < m ==> f k < f m
   MULTIPLE_INTERVAL    |- !n m. n divides m ==> !x. m - n < x /\ x < m + n /\ n divides x ==> (x = m)
   MOD_SUC_EQN          |- !m n. 0 < m ==> (SUC (n MOD m) = SUC n MOD m + (SUC n DIV m - n DIV m) * m)
   ONE_LT_HALF_SQ       |- !n. 1 < n ==> 1 < HALF (n ** 2)
   EXP_2_HALF           |- !n. 0 < n ==> (HALF (2 ** n) = 2 ** (n - 1))
   HALF_MULT_EVEN       |- !m n. EVEN n ==> (HALF (m * n) = m * HALF n)
   MULT_LT_IMP_LT       |- !m n k. 0 < k /\ k * m < n ==> m < n
   MULT_LE_IMP_LE       |- !m n k. 0 < k /\ k * m <= n ==> m <= n
   HALF_EXP_5           |- !n. n * HALF (SQ n ** 2) <= HALF (n ** 5)
   LE_TWICE_ALT         |- !m n. n <= TWICE m <=> n <> 0 ==> HALF (n - 1) < m
   HALF_DIV_TWO_POWER   |- !m n. HALF n DIV 2 ** m = n DIV 2 ** SUC m
   fit_for_10           |- 1 + 2 + 3 + 4 = 10
   fit_for_100          |- 1 * 2 + 3 * 4 + 5 * 6 + 7 * 8 = 100
*)

(* ------------------------------------------------------------------------- *)
(* Arithmetic Theorems                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 3 = SUC 2 *)
(* Proof: by arithmetic *)
val THREE = store_thm(
  "THREE",
  ``3 = SUC 2``,
  decide_tac);

(* Theorem: 4 = SUC 3 *)
(* Proof: by arithmetic *)
val FOUR = store_thm(
  "FOUR",
  ``4 = SUC 3``,
  decide_tac);

(* Theorem: 5 = SUC 4 *)
(* Proof: by arithmetic *)
val FIVE = store_thm(
  "FIVE",
  ``5 = SUC 4``,
  decide_tac);

(* Overload squaring *)
val _ = overload_on("SQ", ``\n. n * n``); (* not n ** 2 *)

(* Overload half of a number *)
val _ = overload_on("HALF", ``\n. n DIV 2``);

(* Overload twice of a number *)
val _ = overload_on("TWICE", ``\n. 2 * n``);

(* make divides infix *)
val _ = set_fixity "divides" (Infixl 480); (* relation is 450, +/- is 500, * is 600. *)

(* Theorem alias *)
Theorem num_nchotomy = arithmeticTheory.LESS_LESS_CASES;
(* val num_nchotomy = |- !m n. m = n \/ m < n \/ n < m: thm *)

(* Theorem alias *)
Theorem ZERO_LE_ALL = arithmeticTheory.ZERO_LESS_EQ;
(* val ZERO_LE_ALL = |- !n. 0 <= n: thm *)

(* Theorem alias *)
Theorem NOT_ZERO = arithmeticTheory.NOT_ZERO_LT_ZERO;
(* val NOT_ZERO = |- !n. n <> 0 <=> 0 < n: thm *)

(* Extract theorem *)
Theorem ONE_NOT_0  = DECIDE``1 <> 0``;
(* val ONE_NOT_0 = |- 1 <> 0: thm *)

(* Theorem: !n. 1 < n ==> 0 < n *)
(* Proof: by arithmetic. *)
val ONE_LT_POS = store_thm(
  "ONE_LT_POS",
  ``!n. 1 < n ==> 0 < n``,
  decide_tac);

(* Theorem: !n. 1 < n ==> n <> 0 *)
(* Proof: by arithmetic. *)
val ONE_LT_NONZERO = store_thm(
  "ONE_LT_NONZERO",
  ``!n. 1 < n ==> n <> 0``,
  decide_tac);

(* Theorem: ~(1 < n) <=> (n = 0) \/ (n = 1) *)
(* Proof: by arithmetic. *)
val NOT_LT_ONE = store_thm(
  "NOT_LT_ONE",
  ``!n. ~(1 < n) <=> (n = 0) \/ (n = 1)``,
  decide_tac);

(* Theorem: n <> 0 <=> 1 <= n *)
(* Proof: by arithmetic. *)
val NOT_ZERO_GE_ONE = store_thm(
  "NOT_ZERO_GE_ONE",
  ``!n. n <> 0 <=> 1 <= n``,
  decide_tac);

(* Theorem: n <= 1 <=> (n = 0) \/ (n = 1) *)
(* Proof: by arithmetic *)
val LE_ONE = store_thm(
  "LE_ONE",
  ``!n. n <= 1 <=> (n = 0) \/ (n = 1)``,
  decide_tac);

(* arithmeticTheory.LESS_EQ_SUC_REFL |- !m. m <= SUC m *)

(* Theorem: n < SUC n *)
(* Proof: by arithmetic. *)
val LESS_SUC = store_thm(
  "LESS_SUC",
  ``!n. n < SUC n``,
  decide_tac);

(* Theorem: 0 < n ==> PRE n < n *)
(* Proof: by arithmetic. *)
val PRE_LESS = store_thm(
  "PRE_LESS",
  ``!n. 0 < n ==> PRE n < n``,
  decide_tac);

(* Theorem: 0 < n ==> ?m. n = SUC m *)
(* Proof: by NOT_ZERO_LT_ZERO, num_CASES. *)
val SUC_EXISTS = store_thm(
  "SUC_EXISTS",
  ``!n. 0 < n ==> ?m. n = SUC m``,
  metis_tac[NOT_ZERO_LT_ZERO, num_CASES]);

(* prim_recTheory.LESS_0 |- !n. 0 < SUC n  *)
(* Theorem: 0 < SUC n *)
(* Proof: by arithmetic. *)
val SUC_POS = store_thm(
  "SUC_POS",
  ``!n. 0 < SUC n``,
  decide_tac);

(* numTheory.NOT_SUC  |- !n. SUC n <> 0 *)
(* Theorem: 0 < SUC n *)
(* Proof: by arithmetic. *)
val SUC_NOT_ZERO = store_thm(
  "SUC_NOT_ZERO",
  ``!n. SUC n <> 0``,
  decide_tac);

(* Theorem: 1 <> 0 *)
(* Proof: by ONE, SUC_ID *)
val ONE_NOT_ZERO = store_thm(
  "ONE_NOT_ZERO",
  ``1 <> 0``,
  decide_tac);

(* Theorem: (SUC m) + (SUC n) = m + n + 2 *)
(* Proof:
     (SUC m) + (SUC n)
   = (m + 1) + (n + 1)     by ADD1
   = m + n + 2             by arithmetic
*)
val SUC_ADD_SUC = store_thm(
  "SUC_ADD_SUC",
  ``!m n. (SUC m) + (SUC n) = m + n + 2``,
  decide_tac);

(* Theorem: (SUC m) * (SUC n) = m * n + m + n + 1 *)
(* Proof:
     (SUC m) * (SUC n)
   = SUC m + (SUC m) * n   by MULT_SUC
   = SUC m + n * (SUC m)   by MULT_COMM
   = SUC m + (n + n * m)   by MULT_SUC
   = m * n + m + n + 1     by arithmetic
*)
val SUC_MULT_SUC = store_thm(
  "SUC_MULT_SUC",
  ``!m n. (SUC m) * (SUC n) = m * n + m + n + 1``,
  rw[MULT_SUC]);

(* Theorem: (SUC m = SUC n) <=> (m = n) *)
(* Proof: by prim_recTheory.INV_SUC_EQ *)
val SUC_EQ = store_thm(
  "SUC_EQ",
  ``!m n. (SUC m = SUC n) <=> (m = n)``,
  rw[]);

(* Theorem: (TWICE n = 0) <=> (n = 0) *)
(* Proof: MULT_EQ_0 *)
val TWICE_EQ_0 = store_thm(
  "TWICE_EQ_0",
  ``!n. (TWICE n = 0) <=> (n = 0)``,
  rw[]);

(* Theorem: (SQ n = 0) <=> (n = 0) *)
(* Proof: MULT_EQ_0 *)
val SQ_EQ_0 = store_thm(
  "SQ_EQ_0",
  ``!n. (SQ n = 0) <=> (n = 0)``,
  rw[]);

(* Theorem: (SQ n = 1) <=> (n = 1) *)
(* Proof: MULT_EQ_1 *)
val SQ_EQ_1 = store_thm(
  "SQ_EQ_1",
  ``!n. (SQ n = 1) <=> (n = 1)``,
  rw[]);

(* Theorem: (x * y * z = 0) <=> ((x = 0) \/ (y = 0) \/ (z = 0)) *)
(* Proof: by MULT_EQ_0 *)
val MULT3_EQ_0 = store_thm(
  "MULT3_EQ_0",
  ``!x y z. (x * y * z = 0) <=> ((x = 0) \/ (y = 0) \/ (z = 0))``,
  metis_tac[MULT_EQ_0]);

(* Theorem: (x * y * z = 1) <=> ((x = 1) /\ (y = 1) /\ (z = 1)) *)
(* Proof: by MULT_EQ_1 *)
val MULT3_EQ_1 = store_thm(
  "MULT3_EQ_1",
  ``!x y z. (x * y * z = 1) <=> ((x = 1) /\ (y = 1) /\ (z = 1))``,
  metis_tac[MULT_EQ_1]);

(* Theorem: 0 ** 2 = 0 *)
(* Proof: by ZERO_EXP *)
Theorem SQ_0:
  0 ** 2 = 0
Proof
  simp[]
QED

(* Theorem: (n ** 2 = 0) <=> (n = 0) *)
(* Proof: by EXP_2, MULT_EQ_0 *)
Theorem EXP_2_EQ_0:
  !n. (n ** 2 = 0) <=> (n = 0)
Proof
  simp[]
QED

(* LE_MULT_LCANCEL |- !m n p. m * n <= m * p <=> m = 0 \/ n <= p *)

(* Theorem: n <= p ==> m * n <= m * p *)
(* Proof:
   If m = 0, this is trivial.
   If m <> 0, this is true by LE_MULT_LCANCEL.
*)
Theorem LE_MULT_LCANCEL_IMP:
  !m n p. n <= p ==> m * n <= m * p
Proof
  simp[]
QED

(* ------------------------------------------------------------------------- *)
(* Maximum and minimum                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: MAX m n = if m <= n then n else m *)
(* Proof: by MAX_DEF *)
val MAX_ALT = store_thm(
  "MAX_ALT",
  ``!m n. MAX m n = if m <= n then n else m``,
  rw[MAX_DEF]);

(* Theorem: MIN m n = if m <= n then m else n *)
(* Proof: by MIN_DEF *)
val MIN_ALT = store_thm(
  "MIN_ALT",
  ``!m n. MIN m n = if m <= n then m else n``,
  rw[MIN_DEF]);

(* Theorem: (!x y. x <= y ==> f x <= f y) ==> !x y. f (MAX x y) = MAX (f x) (f y) *)
(* Proof: by MAX_DEF *)
val MAX_SWAP = store_thm(
  "MAX_SWAP",
  ``!f. (!x y. x <= y ==> f x <= f y) ==> !x y. f (MAX x y) = MAX (f x) (f y)``,
  rw[MAX_DEF] >>
  Cases_on `x < y` >| [
    `f x <= f y` by rw[] >>
    Cases_on `f x = f y` >-
    rw[] >>
    rw[],
    `y <= x` by decide_tac >>
    `f y <= f x` by rw[] >>
    rw[]
  ]);

(* Theorem: (!x y. x <= y ==> f x <= f y) ==> !x y. f (MIN x y) = MIN (f x) (f y) *)
(* Proof: by MIN_DEF *)
val MIN_SWAP = store_thm(
  "MIN_SWAP",
  ``!f. (!x y. x <= y ==> f x <= f y) ==> !x y. f (MIN x y) = MIN (f x) (f y)``,
  rw[MIN_DEF] >>
  Cases_on `x < y` >| [
    `f x <= f y` by rw[] >>
    Cases_on `f x = f y` >-
    rw[] >>
    rw[],
    `y <= x` by decide_tac >>
    `f y <= f x` by rw[] >>
    rw[]
  ]);

(* Theorem: SUC (MAX m n) = MAX (SUC m) (SUC n) *)
(* Proof:
   If m < n, then SUC m < SUC n    by LESS_MONO_EQ
      hence true by MAX_DEF.
   If m = n, then true by MAX_IDEM.
   If n < m, true by MAX_COMM of the case m < n.
*)
val SUC_MAX = store_thm(
  "SUC_MAX",
  ``!m n. SUC (MAX m n) = MAX (SUC m) (SUC n)``,
  rw[MAX_DEF]);

(* Theorem: SUC (MIN m n) = MIN (SUC m) (SUC n) *)
(* Proof: by MIN_DEF *)
val SUC_MIN = store_thm(
  "SUC_MIN",
  ``!m n. SUC (MIN m n) = MIN (SUC m) (SUC n)``,
  rw[MIN_DEF]);

(* Reverse theorems *)
val MAX_SUC = save_thm("MAX_SUC", GSYM SUC_MAX);
(* val MAX_SUC = |- !m n. MAX (SUC m) (SUC n) = SUC (MAX m n): thm *)
val MIN_SUC = save_thm("MIN_SUC", GSYM SUC_MIN);
(* val MIN_SUC = |- !m n. MIN (SUC m) (SUC n) = SUC (MIN m n): thm *)

(* Theorem: x < n /\ y < n ==> MAX x y < n *)
(* Proof:
        MAX x y
      = if x < y then y else x    by MAX_DEF
      = either x or y
      < n                         for either case
*)
val MAX_LESS = store_thm(
  "MAX_LESS",
  ``!x y n. x < n /\ y < n ==> MAX x y < n``,
  rw[]);

(* Theorem: (MAX n m = n) \/ (MAX n m = m) *)
(* Proof: by MAX_DEF *)
val MAX_CASES = store_thm(
  "MAX_CASES",
  ``!m n. (MAX n m = n) \/ (MAX n m = m)``,
  rw[MAX_DEF]);

(* Theorem: (MIN n m = n) \/ (MIN n m = m) *)
(* Proof: by MIN_DEF *)
val MIN_CASES = store_thm(
  "MIN_CASES",
  ``!m n. (MIN n m = n) \/ (MIN n m = m)``,
  rw[MIN_DEF]);

(* Theorem: (MAX n m = 0) <=> ((n = 0) /\ (m = 0)) *)
(* Proof:
   If part: MAX n m = 0 ==> n = 0 /\ m = 0
      If n < m, 0 = MAX n m = m, hence m = 0     by MAX_DEF
                but n < 0 is F                   by NOT_LESS_0
      If ~(n < m), 0 = MAX n m = n, hence n = 0  by MAX_DEF
                and ~(0 < m) ==> m = 0           by NOT_LESS
   Only-if part: n = 0 /\ m = 0 ==> MAX n m = 0
      True since MAX 0 0 = 0                     by MAX_0
*)
val MAX_EQ_0 = store_thm(
  "MAX_EQ_0",
  ``!m n. (MAX n m = 0) <=> ((n = 0) /\ (m = 0))``,
  rw[MAX_DEF]);

(* Theorem: (MIN n m = 0) <=> ((n = 0) \/ (m = 0)) *)
(* Proof:
   If part: MIN n m = 0 ==> n = 0 \/ m = 0
      If n < m, 0 = MIN n m = n, hence n = 0     by MIN_DEF
      If ~(n < m), 0 = MAX n m = m, hence m = 0  by MIN_DEF
   Only-if part: n = 0 \/ m = 0 ==> MIN n m = 0
      True since MIN 0 0 = 0                     by MIN_0
*)
val MIN_EQ_0 = store_thm(
  "MIN_EQ_0",
  ``!m n. (MIN n m = 0) <=> ((n = 0) \/ (m = 0))``,
  rw[MIN_DEF]);

(* Theorem: m <= MAX m n /\ n <= MAX m n *)
(* Proof: by MAX_DEF *)
val MAX_IS_MAX = store_thm(
  "MAX_IS_MAX",
  ``!m n. m <= MAX m n /\ n <= MAX m n``,
  rw_tac std_ss[MAX_DEF]);

(* Theorem: MIN m n <= m /\ MIN m n <= n *)
(* Proof: by MIN_DEF *)
val MIN_IS_MIN = store_thm(
  "MIN_IS_MIN",
  ``!m n. MIN m n <= m /\ MIN m n <= n``,
  rw_tac std_ss[MIN_DEF]);

(* Theorem: (MAX (MAX m n) n = MAX m n) /\ (MAX m (MAX m n) = MAX m n) *)
(* Proof: by MAX_DEF *)
val MAX_ID = store_thm(
  "MAX_ID",
  ``!m n. (MAX (MAX m n) n = MAX m n) /\ (MAX m (MAX m n) = MAX m n)``,
  rw[MAX_DEF]);

(* Theorem: (MIN (MIN m n) n = MIN m n) /\ (MIN m (MIN m n) = MIN m n) *)
(* Proof: by MIN_DEF *)
val MIN_ID = store_thm(
  "MIN_ID",
  ``!m n. (MIN (MIN m n) n = MIN m n) /\ (MIN m (MIN m n) = MIN m n)``,
  rw[MIN_DEF]);

(* Theorem: a <= b /\ c <= d ==> MAX a c <= MAX b d *)
(* Proof: by MAX_DEF *)
val MAX_LE_PAIR = store_thm(
  "MAX_LE_PAIR",
  ``!a b c d. a <= b /\ c <= d ==> MAX a c <= MAX b d``,
  rw[]);

(* Theorem: a <= b /\ c <= d ==> MIN a c <= MIN b d *)
(* Proof: by MIN_DEF *)
val MIN_LE_PAIR = store_thm(
  "MIN_LE_PAIR",
  ``!a b c d. a <= b /\ c <= d ==> MIN a c <= MIN b d``,
  rw[]);

(* Theorem: MAX a (b + c) <= MAX a b + MAX a c *)
(* Proof: by MAX_DEF *)
val MAX_ADD = store_thm(
  "MAX_ADD",
  ``!a b c. MAX a (b + c) <= MAX a b + MAX a c``,
  rw[MAX_DEF]);

(* Theorem: MIN a (b + c) <= MIN a b + MIN a c *)
(* Proof: by MIN_DEF *)
val MIN_ADD = store_thm(
  "MIN_ADD",
  ``!a b c. MIN a (b + c) <= MIN a b + MIN a c``,
  rw[MIN_DEF]);

(* Theorem: 0 < n ==> (MAX 1 n = n) *)
(* Proof: by MAX_DEF *)
val MAX_1_POS = store_thm(
  "MAX_1_POS",
  ``!n. 0 < n ==> (MAX 1 n = n)``,
  rw[MAX_DEF]);

(* Theorem: 0 < n ==> (MIN 1 n = 1) *)
(* Proof: by MIN_DEF *)
val MIN_1_POS = store_thm(
  "MIN_1_POS",
  ``!n. 0 < n ==> (MIN 1 n = 1)``,
  rw[MIN_DEF]);

(* Theorem: MAX m n <= m + n *)
(* Proof:
   If m < n,  MAX m n = n <= m + n  by arithmetic
   Otherwise, MAX m n = m <= m + n  by arithmetic
*)
val MAX_LE_SUM = store_thm(
  "MAX_LE_SUM",
  ``!m n. MAX m n <= m + n``,
  rw[MAX_DEF]);

(* Theorem: MIN m n <= m + n *)
(* Proof:
   If m < n,  MIN m n = m <= m + n  by arithmetic
   Otherwise, MIN m n = n <= m + n  by arithmetic
*)
val MIN_LE_SUM = store_thm(
  "MIN_LE_SUM",
  ``!m n. MIN m n <= m + n``,
  rw[MIN_DEF]);

(* Theorem: MAX 1 (m ** n) = (MAX 1 m) ** n *)
(* Proof:
   If m = 0,
      Then 0 ** n = 0 or 1          by ZERO_EXP
      Thus MAX 1 (0 ** n) = 1       by MAX_DEF
       and (MAX 1 0) ** n = 1       by MAX_DEF, EXP_1
   If m <> 0,
      Then 0 < m ** n               by EXP_POS
        so MAX 1 (m ** n) = m ** n  by MAX_DEF
       and (MAX 1 m) ** n = m ** n  by MAX_DEF, 0 < m
*)
val MAX_1_EXP = store_thm(
  "MAX_1_EXP",
  ``!n m. MAX 1 (m ** n) = (MAX 1 m) ** n``,
  rpt strip_tac >>
  Cases_on `m = 0` >-
  rw[ZERO_EXP, MAX_DEF] >>
  `0 < m /\ 0 < m ** n` by rw[] >>
  `MAX 1 (m ** n) = m ** n` by rw[MAX_DEF] >>
  `MAX 1 m = m` by rw[MAX_DEF] >>
  fs[]);

(* Theorem: MIN 1 (m ** n) = (MIN 1 m) ** n *)
(* Proof:
   If m = 0,
      Then 0 ** n = 0 or 1          by ZERO_EXP
      Thus MIN 1 (0 ** n) = 0 when n <> 0 or 1 when n = 0  by MIN_DEF
       and (MIN 1 0) ** n = 0 ** n  by MIN_DEF
   If m <> 0,
      Then 0 < m ** n               by EXP_POS
        so MIN 1 (m ** n) = 1 ** n  by MIN_DEF
       and (MIN 1 m) ** n = 1 ** n  by MIN_DEF, 0 < m
*)
val MIN_1_EXP = store_thm(
  "MIN_1_EXP",
  ``!n m. MIN 1 (m ** n) = (MIN 1 m) ** n``,
  rpt strip_tac >>
  Cases_on `m = 0` >-
  rw[ZERO_EXP, MIN_DEF] >>
  `0 < m ** n` by rw[] >>
  `MIN 1 (m ** n) = 1` by rw[MIN_DEF] >>
  `MIN 1 m = 1` by rw[MIN_DEF] >>
  fs[]);

(* ------------------------------------------------------------------------- *)
(* Arithmetic Manipulations                                                  *)
(* ------------------------------------------------------------------------- *)

(* Rename theorem *)
val MULT_POS = save_thm("MULT_POS", LESS_MULT2);
(* val MULT_POS = |- !m n. 0 < m /\ 0 < n ==> 0 < m * n: thm *)

(* Theorem: m * (n * p) = n * (m * p) *)
(* Proof:
     m * (n * p)
   = (m * n) * p       by MULT_ASSOC
   = (n * m) * p       by MULT_COMM
   = n * (m * p)       by MULT_ASSOC
*)
val MULT_COMM_ASSOC = store_thm(
  "MULT_COMM_ASSOC",
  ``!m n p. m * (n * p) = n * (m * p)``,
  metis_tac[MULT_COMM, MULT_ASSOC]);

(* Theorem: n * p = m * p <=> p = 0 \/ n = m *)
(* Proof:
       n * p = m * p
   <=> n * p - m * p = 0      by SUB_EQUAL_0
   <=>   (n - m) * p = 0      by RIGHT_SUB_DISTRIB
   <=>   n - m = 0  or p = 0  by MULT_EQ_0
   <=>    n = m  or p = 0     by SUB_EQUAL_0
*)
val MULT_RIGHT_CANCEL = store_thm(
  "MULT_RIGHT_CANCEL",
  ``!m n p. (n * p = m * p) <=> (p = 0) \/ (n = m)``,
  rw[]);

(* Theorem: p * n = p * m <=> p = 0 \/ n = m *)
(* Proof: by MULT_RIGHT_CANCEL and MULT_COMM. *)
val MULT_LEFT_CANCEL = store_thm(
  "MULT_LEFT_CANCEL",
  ``!m n p. (p * n = p * m) <=> (p = 0) \/ (n = m)``,
  rw[MULT_RIGHT_CANCEL, MULT_COMM]);

(* Theorem: 0 < n ==> ((n * m) DIV n = m) *)
(* Proof:
   Since n * m = m * n        by MULT_COMM
               = m * n + 0    by ADD_0
     and 0 < n                by given
   Hence (n * m) DIV n = m    by DIV_UNIQUE:
   |- !n k q. (?r. (k = q * n + r) /\ r < n) ==> (k DIV n = q)
*)
val MULT_TO_DIV = store_thm(
  "MULT_TO_DIV",
  ``!m n. 0 < n ==> ((n * m) DIV n = m)``,
  metis_tac[MULT_COMM, ADD_0, DIV_UNIQUE]);
(* This is commutative version of:
arithmeticTheory.MULT_DIV |- !n q. 0 < n ==> (q * n DIV n = q)
*)

(* Theorem: m * (n * p) = m * p * n *)
(* Proof: by MULT_ASSOC, MULT_COMM *)
val MULT_ASSOC_COMM = store_thm(
  "MULT_ASSOC_COMM",
  ``!m n p. m * (n * p) = m * p * n``,
  metis_tac[MULT_ASSOC, MULT_COMM]);

(* Theorem: 0 < n ==> !m. (m * n = n) <=> (m = 1) *)
(* Proof: by MULT_EQ_ID *)
val MULT_LEFT_ID = store_thm(
  "MULT_LEFT_ID",
  ``!n. 0 < n ==> !m. (m * n = n) <=> (m = 1)``,
  metis_tac[MULT_EQ_ID, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < n ==> !m. (n * m = n) <=> (m = 1) *)
(* Proof: by MULT_EQ_ID *)
val MULT_RIGHT_ID = store_thm(
  "MULT_RIGHT_ID",
  ``!n. 0 < n ==> !m. (n * m = n) <=> (m = 1)``,
  metis_tac[MULT_EQ_ID, MULT_COMM, NOT_ZERO_LT_ZERO]);

(* Theorem alias *)
Theorem MULT_EQ_SELF = MULT_RIGHT_ID;
(* val MULT_EQ_SELF = |- !n. 0 < n ==> !m. (n * m = n) <=> (m = 1): thm *)

(* Theorem: (n * n = n) <=> ((n = 0) \/ (n = 1)) *)
(* Proof:
   If part: n * n = n ==> (n = 0) \/ (n = 1)
      By contradiction, suppose n <> 0 /\ n <> 1.
      Since n * n = n = n * 1     by MULT_RIGHT_1
       then     n = 1             by MULT_LEFT_CANCEL, n <> 0
       This contradicts n <> 1.
   Only-if part: (n = 0) \/ (n = 1) ==> n * n = n
      That is, 0 * 0 = 0          by MULT
           and 1 * 1 = 1          by MULT_RIGHT_1
*)
val SQ_EQ_SELF = store_thm(
  "SQ_EQ_SELF",
  ``!n. (n * n = n) <=> ((n = 0) \/ (n = 1))``,
  rw_tac bool_ss[EQ_IMP_THM] >-
  metis_tac[MULT_RIGHT_1, MULT_LEFT_CANCEL] >-
  rw[] >>
  rw[]);

(* Theorem: m <= n /\ 0 < c ==> b ** c ** m <= b ** c ** n *)
(* Proof:
   If b = 0,
      Note 0 < c ** m /\ 0 < c ** n   by EXP_POS, by 0 < c
      Thus 0 ** c ** m = 0            by ZERO_EXP
       and 0 ** c ** n = 0            by ZERO_EXP
      Hence true.
   If b <> 0,
      Then c ** m <= c ** n           by EXP_BASE_LEQ_MONO_IMP, 0 < c
        so b ** c ** m <= b ** c ** n by EXP_BASE_LEQ_MONO_IMP, 0 < b
*)
val EXP_EXP_BASE_LE = store_thm(
  "EXP_EXP_BASE_LE",
  ``!b c m n. m <= n /\ 0 < c ==> b ** c ** m <= b ** c ** n``,
  rpt strip_tac >>
  Cases_on `b = 0` >-
  rw[ZERO_EXP] >>
  rw[EXP_BASE_LEQ_MONO_IMP]);

(* Theorem: a <= b ==> a ** n <= b ** n *)
(* Proof:
   Note a ** n <= b ** n                 by EXP_EXP_LE_MONO
   Thus size (a ** n) <= size (b ** n)   by size_monotone_le
*)
val EXP_EXP_LE_MONO_IMP = store_thm(
  "EXP_EXP_LE_MONO_IMP",
  ``!a b n. a <= b ==> a ** n <= b ** n``,
  rw[]);

(* Theorem: m <= n ==> !p. p ** n = p ** m * p ** (n - m) *)
(* Proof:
   Note n = (n - m) + m          by m <= n
        p ** n
      = p ** (n - m) * p ** m    by EXP_ADD
      = p ** m * p ** (n - m)    by MULT_COMM
*)
val EXP_BY_ADD_SUB_LE = store_thm(
  "EXP_BY_ADD_SUB_LE",
  ``!m n. m <= n ==> !p. p ** n = p ** m * p ** (n - m)``,
  rpt strip_tac >>
  `n = (n - m) + m` by decide_tac >>
  metis_tac[EXP_ADD, MULT_COMM]);

(* Theorem: m < n ==> (p ** n = p ** m * p ** (n - m)) *)
(* Proof: by EXP_BY_ADD_SUB_LE, LESS_IMP_LESS_OR_EQ *)
val EXP_BY_ADD_SUB_LT = store_thm(
  "EXP_BY_ADD_SUB_LT",
  ``!m n. m < n ==> !p. p ** n = p ** m * p ** (n - m)``,
  rw[EXP_BY_ADD_SUB_LE]);

(* Theorem: 0 < m ==> m ** (SUC n) DIV m = m ** n *)
(* Proof:
     m ** (SUC n) DIV m
   = (m * m ** n) DIV m    by EXP
   = m ** n                by MULT_TO_DIV, 0 < m
*)
val EXP_SUC_DIV = store_thm(
  "EXP_SUC_DIV",
  ``!m n. 0 < m ==> (m ** (SUC n) DIV m = m ** n)``,
  simp[EXP, MULT_TO_DIV]);

(* Theorem: n <= n ** 2 *)
(* Proof:
   If n = 0,
      Then n ** 2 = 0 >= 0       by ZERO_EXP
   If n <> 0, then 0 < n         by NOT_ZERO_LT_ZERO
      Hence n = n ** 1           by EXP_1
             <= n ** 2           by EXP_BASE_LEQ_MONO_IMP
*)
val SELF_LE_SQ = store_thm(
  "SELF_LE_SQ",
  ``!n. n <= n ** 2``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  `0 < n /\ 1 <= 2` by decide_tac >>
  metis_tac[EXP_BASE_LEQ_MONO_IMP, EXP_1]);

(* Theorem: a <= b /\ c <= d ==> a + c <= b + d *)
(* Proof: by LESS_EQ_LESS_EQ_MONO, or
   Note a <= b ==>  a + c <= b + c    by LE_ADD_RCANCEL
    and c <= d ==>  b + c <= b + d    by LE_ADD_LCANCEL
   Thus             a + c <= b + d    by LESS_EQ_TRANS
*)
val LE_MONO_ADD2 = store_thm(
  "LE_MONO_ADD2",
  ``!a b c d. a <= b /\ c <= d ==> a + c <= b + d``,
  rw[LESS_EQ_LESS_EQ_MONO]);

(* Theorem: a < b /\ c < d ==> a + c < b + d *)
(* Proof:
   Note a < b ==>  a + c < b + c    by LT_ADD_RCANCEL
    and c < d ==>  b + c < b + d    by LT_ADD_LCANCEL
   Thus            a + c < b + d    by LESS_TRANS
*)
val LT_MONO_ADD2 = store_thm(
  "LT_MONO_ADD2",
  ``!a b c d. a < b /\ c < d ==> a + c < b + d``,
  rw[LT_ADD_RCANCEL, LT_ADD_LCANCEL]);

(* Theorem: a <= b /\ c <= d ==> a * c <= b * d *)
(* Proof: by LESS_MONO_MULT2, or
   Note a <= b ==> a * c <= b * c  by LE_MULT_RCANCEL
    and c <= d ==> b * c <= b * d  by LE_MULT_LCANCEL
   Thus            a * c <= b * d  by LESS_EQ_TRANS
*)
val LE_MONO_MULT2 = store_thm(
  "LE_MONO_MULT2",
  ``!a b c d. a <= b /\ c <= d ==> a * c <= b * d``,
  rw[LESS_MONO_MULT2]);

(* Theorem: a < b /\ c < d ==> a * c < b * d *)
(* Proof:
   Note 0 < b, by a < b.
    and 0 < d, by c < d.
   If c = 0,
      Then a * c = 0 < b * d   by MULT_EQ_0
   If c <> 0, then 0 < c       by NOT_ZERO_LT_ZERO
      a < b ==> a * c < b * c  by LT_MULT_RCANCEL, 0 < c
      c < d ==> b * c < b * d  by LT_MULT_LCANCEL, 0 < b
   Thus         a * c < b * d  by LESS_TRANS
*)
val LT_MONO_MULT2 = store_thm(
  "LT_MONO_MULT2",
  ``!a b c d. a < b /\ c < d ==> a * c < b * d``,
  rpt strip_tac >>
  `0 < b /\ 0 < d` by decide_tac >>
  Cases_on `c = 0` >-
  metis_tac[MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
  metis_tac[LT_MULT_RCANCEL, LT_MULT_LCANCEL, LESS_TRANS, NOT_ZERO_LT_ZERO]);

(* Theorem: 1 < m /\ 1 < n ==> (m + n <= m * n) *)
(* Proof:
   Let m = m' + 1, n = n' + 1.
   Note m' <> 0 /\ n' <> 0.
   Thus m' * n' <> 0               by MULT_EQ_0
     or 1 <= m' * n'
       m * n
     = (m' + 1) * (n' + 1)
     = m' * n' + m' + n' + 1       by arithmetic
    >= 1 + m' + n' + 1             by 1 <= m' * n'
     = m + n
*)
val SUM_LE_PRODUCT = store_thm(
  "SUM_LE_PRODUCT",
  ``!m n. 1 < m /\ 1 < n ==> (m + n <= m * n)``,
  rpt strip_tac >>
  `m <> 0 /\ n <> 0` by decide_tac >>
  `?m' n'. (m = m' + 1) /\ (n = n' + 1)` by metis_tac[num_CASES, ADD1] >>
  `m * n = (m' + 1) * n' + (m' + 1)` by rw[LEFT_ADD_DISTRIB] >>
  `_ = m' * n' + n' + (m' + 1)` by rw[RIGHT_ADD_DISTRIB] >>
  `_ = m + (n' + m' * n')` by decide_tac >>
  `m' * n' <> 0` by fs[] >>
  decide_tac);

(* Theorem: 0 < n ==> k * n + 1 <= (k + 1) * n *)
(* Proof:
        k * n + 1
     <= k * n + n          by 1 <= n
     <= (k + 1) * n        by RIGHT_ADD_DISTRIB
*)
val MULTIPLE_SUC_LE = store_thm(
  "MULTIPLE_SUC_LE",
  ``!n k. 0 < n ==> k * n + 1 <= (k + 1) * n``,
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Simple Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < m /\ 0 < n /\ (m + n = 2) ==> m = 1 /\ n = 1 *)
(* Proof: by arithmetic. *)
val ADD_EQ_2 = store_thm(
  "ADD_EQ_2",
  ``!m n. 0 < m /\ 0 < n /\ (m + n = 2) ==> (m = 1) /\ (n = 1)``,
  rw_tac arith_ss[]);

(* Theorem: EVEN 0 *)
(* Proof: by EVEN. *)
val EVEN_0 = store_thm(
  "EVEN_0",
  ``EVEN 0``,
  simp[]);

(* Theorem: ODD 1 *)
(* Proof: by ODD. *)
val ODD_1 = store_thm(
  "ODD_1",
  ``ODD 1``,
  simp[]);

(* Theorem: EVEN 2 *)
(* Proof: by EVEN_MOD2. *)
val EVEN_2 = store_thm(
  "EVEN_2",
  ``EVEN 2``,
  EVAL_TAC);

(*
EVEN_ADD  |- !m n. EVEN (m + n) <=> (EVEN m <=> EVEN n)
ODD_ADD   |- !m n. ODD (m + n) <=> (ODD m <=/=> ODD n)
EVEN_MULT |- !m n. EVEN (m * n) <=> EVEN m \/ EVEN n
ODD_MULT  |- !m n. ODD (m * n) <=> ODD m /\ ODD n
*)

(* Derive theorems. *)
val EVEN_SQ = save_thm("EVEN_SQ",
    EVEN_MULT |> SPEC ``n:num`` |> SPEC ``n:num`` |> SIMP_RULE arith_ss[] |> GEN_ALL);
(* val EVEN_SQ = |- !n. EVEN (n ** 2) <=> EVEN n: thm *)
val ODD_SQ = save_thm("ODD_SQ",
    ODD_MULT |> SPEC ``n:num`` |> SPEC ``n:num`` |> SIMP_RULE arith_ss[] |> GEN_ALL);
(* val ODD_SQ = |- !n. ODD (n ** 2) <=> ODD n: thm *)

(* Theorem: EVEN (2 * a + b) <=> EVEN b *)
(* Proof:
       EVEN (2 * a + b)
   <=> EVEN (2 * a) /\ EVEN b      by EVEN_ADD
   <=>            T /\ EVEN b      by EVEN_DOUBLE
   <=> EVEN b
*)
Theorem EQ_PARITY:
  !a b. EVEN (2 * a + b) <=> EVEN b
Proof
  rw[EVEN_ADD, EVEN_DOUBLE]
QED

(* Theorem: ODD x <=> (x MOD 2 = 1) *)
(* Proof:
   If part: ODD x ==> x MOD 2 = 1
      Since  ODD x
         <=> ~EVEN x          by ODD_EVEN
         <=> ~(x MOD 2 = 0)   by EVEN_MOD2
         But x MOD 2 < 2      by MOD_LESS, 0 < 2
          so x MOD 2 = 1      by arithmetic
   Only-if part: x MOD 2 = 1 ==> ODD x
      By contradiction, suppose ~ODD x.
      Then EVEN x             by ODD_EVEN
       and x MOD 2 = 0        by EVEN_MOD2
      This contradicts x MOD 2 = 1.
*)
val ODD_MOD2 = store_thm(
  "ODD_MOD2",
  ``!x. ODD x <=> (x MOD 2 = 1)``,
  metis_tac[EVEN_MOD2, ODD_EVEN, MOD_LESS,
             DECIDE``0 <> 1 /\ 0 < 2 /\ !n. n < 2 /\ n <> 1 ==> (n = 0)``]);

(* Theorem: (EVEN n <=> ODD (SUC n)) /\ (ODD n <=> EVEN (SUC n)) *)
(* Proof: by EVEN, ODD, EVEN_OR_ODD *)
val EVEN_ODD_SUC = store_thm(
  "EVEN_ODD_SUC",
  ``!n. (EVEN n <=> ODD (SUC n)) /\ (ODD n <=> EVEN (SUC n))``,
  metis_tac[EVEN, ODD, EVEN_OR_ODD]);

(* Theorem: 0 < n ==> (EVEN n <=> ODD (PRE n)) /\ (ODD n <=> EVEN (PRE n)) *)
(* Proof: by EVEN, ODD, EVEN_OR_ODD, PRE_SUC_EQ *)
val EVEN_ODD_PRE = store_thm(
  "EVEN_ODD_PRE",
  ``!n. 0 < n ==> (EVEN n <=> ODD (PRE n)) /\ (ODD n <=> EVEN (PRE n))``,
  metis_tac[EVEN, ODD, EVEN_OR_ODD, PRE_SUC_EQ]);

(* Theorem: EVEN (n * (n + 1)) *)
(* Proof:
   If EVEN n, true        by EVEN_MULT
   If ~(EVEN n),
      Then EVEN (SUC n)   by EVEN
        or EVEN (n + 1)   by ADD1
      Thus true           by EVEN_MULT
*)
val EVEN_PARTNERS = store_thm(
  "EVEN_PARTNERS",
  ``!n. EVEN (n * (n + 1))``,
  metis_tac[EVEN, EVEN_MULT, ADD1]);

(* Theorem: EVEN n ==> (n = 2 * HALF n) *)
(* Proof:
   Note EVEN n ==> ?m. n = 2 * m     by EVEN_EXISTS
    and HALF n = HALF (2 * m)        by above
               = m                   by MULT_TO_DIV, 0 < 2
   Thus n = 2 * m = 2 * HALF n       by above
*)
val EVEN_HALF = store_thm(
  "EVEN_HALF",
  ``!n. EVEN n ==> (n = 2 * HALF n)``,
  metis_tac[EVEN_EXISTS, MULT_TO_DIV, DECIDE``0 < 2``]);

(* Theorem: ODD n ==> (n = 2 * HALF n + 1 *)
(* Proof:
   Since n = HALF n * 2 + n MOD 2  by DIVISION, 0 < 2
           = 2 * HALF n + n MOD 2  by MULT_COMM
           = 2 * HALF n + 1        by ODD_MOD2
*)
val ODD_HALF = store_thm(
  "ODD_HALF",
  ``!n. ODD n ==> (n = 2 * HALF n + 1)``,
  metis_tac[DIVISION, MULT_COMM, ODD_MOD2, DECIDE``0 < 2``]);

(* Theorem: EVEN n ==> (HALF (SUC n) = HALF n) *)
(* Proof:
   Note n = (HALF n) * 2 + (n MOD 2)   by DIVISION, 0 < 2
          = (HALF n) * 2               by EVEN_MOD2
    Now SUC n
      = n + 1                          by ADD1
      = (HALF n) * 2 + 1               by above
   Thus HALF (SUC n)
      = ((HALF n) * 2 + 1) DIV 2       by above
      = HALF n                         by DIV_MULT, 1 < 2
*)
val EVEN_SUC_HALF = store_thm(
  "EVEN_SUC_HALF",
  ``!n. EVEN n ==> (HALF (SUC n) = HALF n)``,
  rpt strip_tac >>
  `n MOD 2 = 0` by rw[GSYM EVEN_MOD2] >>
  `n = HALF n * 2 + n MOD 2` by rw[DIVISION] >>
  `SUC n = HALF n * 2 + 1` by rw[] >>
  metis_tac[DIV_MULT, DECIDE``1 < 2``]);

(* Theorem: ODD n ==> (HALF (SUC n) = SUC (HALF n)) *)
(* Proof:
     SUC n
   = SUC (2 * HALF n + 1)              by ODD_HALF
   = 2 * HALF n + 1 + 1                by ADD1
   = 2 * HALF n + 2                    by arithmetic
   = 2 * (HALF n + 1)                  by LEFT_ADD_DISTRIB
   = 2 * SUC (HALF n)                  by ADD1
   = SUC (HALF n) * 2 + 0              by MULT_COMM, ADD_0
   Hence HALF (SUC n) = SUC (HALF n)   by DIV_UNIQUE, 0 < 2
*)
val ODD_SUC_HALF = store_thm(
  "ODD_SUC_HALF",
  ``!n. ODD n ==> (HALF (SUC n) = SUC (HALF n))``,
  rpt strip_tac >>
  `SUC n = SUC (2 * HALF n + 1)` by rw[ODD_HALF] >>
  `_ = SUC (HALF n) * 2 + 0` by rw[] >>
  metis_tac[DIV_UNIQUE, DECIDE``0 < 2``]);

(* Theorem: (HALF n = 0) <=> ((n = 0) \/ (n = 1)) *)
(* Proof:
   If part: (HALF n = 0) ==> ((n = 0) \/ (n = 1))
      Note n = (HALF n) * 2 + (n MOD 2)    by DIVISION, 0 < 2
             = n MOD 2                     by HALF n = 0
       and n MOD 2 < 2                     by MOD_LESS, 0 < 2
        so n < 2, or n = 0 or n = 1        by arithmetic
   Only-if part: HALF 0 = 0, HALF 1 = 0.
      True since both 0 or 1 < 2           by LESS_DIV_EQ_ZERO, 0 < 2
*)
val HALF_EQ_0 = store_thm(
  "HALF_EQ_0",
  ``!n. (HALF n = 0) <=> ((n = 0) \/ (n = 1))``,
  rw[LESS_DIV_EQ_ZERO, EQ_IMP_THM] >>
  `n = (HALF n) * 2 + (n MOD 2)` by rw[DIVISION] >>
  `n MOD 2 < 2` by rw[MOD_LESS] >>
  decide_tac);

(* Theorem: (HALF n = n) <=> (n = 0) *)
(* Proof:
   If part: HALF n = n ==> n = 0
      Note n = 2 * HALF n + (n MOD 2)    by DIVISION, MULT_COMM
        so n = 2 * n + (n MOD 2)         by HALF n = n
        or 0 = n + (n MOD 2)             by arithmetic
      Thus n  = 0  and (n MOD 2 = 0)     by ADD_EQ_0
   Only-if part: HALF 0 = 0, true        by ZERO_DIV, 0 < 2
*)
val HALF_EQ_SELF = store_thm(
  "HALF_EQ_SELF",
  ``!n. (HALF n = n) <=> (n = 0)``,
  rw[EQ_IMP_THM] >>
  `n = 2 * HALF n + (n MOD 2)` by metis_tac[DIVISION, MULT_COMM, DECIDE``0 < 2``] >>
  rw[ADD_EQ_0]);

(* Theorem: 0 < n ==> HALF n < n *)
(* Proof:
   Note HALF n <= n     by DIV_LESS_EQ, 0 < 2
    and HALF n <> n     by HALF_EQ_SELF, n <> 0
     so HALF n < n      by arithmetic
*)
val HALF_LT = store_thm(
  "HALF_LT",
  ``!n. 0 < n ==> HALF n < n``,
  rpt strip_tac >>
  `HALF n <= n` by rw[DIV_LESS_EQ] >>
  `HALF n <> n` by rw[HALF_EQ_SELF] >>
  decide_tac);

(* Theorem: 2 < n ==> (1 + HALF n < n) *)
(* Proof:
   If EVEN n,
      then     2 * HALF n = n      by EVEN_HALF
        so 2 + 2 * HALF n < n + n  by 2 < n
        or     1 + HALF n < n      by arithmetic
   If ~EVEN n, then ODD n          by ODD_EVEN
      then 1 + 2 * HALF n = 2      by ODD_HALF
        so 1 + 2 * HALF n < n      by 2 < n
      also 2 + 2 * HALF n < n + n  by 1 < n
        or     1 + HALF n < n      by arithmetic
*)
Theorem HALF_ADD1_LT:
  !n. 2 < n ==> 1 + HALF n < n
Proof
  rpt strip_tac >>
  Cases_on `EVEN n` >| [
    `2 * HALF n = n` by rw[EVEN_HALF] >>
    decide_tac,
    `1 + 2 * HALF n = n` by rw[ODD_HALF, ODD_EVEN] >>
    decide_tac
  ]
QED

(* Theorem alias *)
Theorem HALF_TWICE = arithmeticTheory.MULT_DIV_2;
(* val HALF_TWICE = |- !n. HALF (2 * n) = n: thm *)

(* Theorem: n * HALF m <= HALF (n * m) *)
(* Proof:
   Let k = HALF m.
   If EVEN m,
      Then m = 2 * k           by EVEN_HALF
        HALF (n * m)
      = HALF (n * (2 * k))     by above
      = HALF (2 * (n * k))     by arithmetic
      = n * k                  by HALF_TWICE
   If ~EVEN m, then ODD m      by ODD_EVEN
      Then m = 2 * k + 1       by ODD_HALF
      so   HALF (n * m)
         = HALF (n * (2 * k + 1))        by above
         = HALF (2 * (n * k) + n)        by LEFT_ADD_DISTRIB
         = HALF (2 * (n * k)) + HALF n   by ADD_DIV_ADD_DIV
         = n * k + HALF n                by HALF_TWICE
         >= n * k                        by arithmetic
*)
Theorem HALF_MULT: !m n. n * (m DIV 2) <= (n * m) DIV 2
Proof
  rpt strip_tac >>
  qabbrev_tac `k = m DIV 2` >>
  Cases_on `EVEN m`
  >- (`m = 2 * k` by rw[EVEN_HALF, Abbr`k`] >>
      simp[]) >>
  `ODD m` by rw[ODD_EVEN] >>
  `m = 2 * k + 1` by rw[ODD_HALF, Abbr`k`] >>
  simp[LEFT_ADD_DISTRIB]
QED

(* Theorem: 2 * HALF n <= n /\ n <= SUC (2 * HALF n) *)
(* Proof:
   If EVEN n,
      Then n = 2 * HALF n         by EVEN_HALF
       and n = n < SUC n          by LESS_SUC
        or n <= n <= SUC n,
      Giving 2 * HALF n <= n /\ n <= SUC (2 * HALF n)
   If ~(EVEN n), then ODD n       by EVEN_ODD
      Then n = 2 * HALF n + 1     by ODD_HALF
             = SUC (2 * HALF n)   by ADD1
        or n - 1 < n = n
        or n - 1 <= n <= n,
      Giving 2 * HALF n <= n /\ n <= SUC (2 * HALF n)
*)
val TWO_HALF_LE_THM = store_thm(
  "TWO_HALF_LE_THM",
  ``!n. 2 * HALF n <= n /\ n <= SUC (2 * HALF n)``,
  strip_tac >>
  Cases_on `EVEN n` >-
  rw[GSYM EVEN_HALF] >>
  `ODD n` by rw[ODD_EVEN] >>
  `n <> 0` by metis_tac[ODD] >>
  `n = SUC (2 * HALF n)` by rw[ODD_HALF, ADD1] >>
  `2 * HALF n = PRE n` by rw[] >>
  rw[]);

(* Theorem: 2 * ((HALF n) * m) <= n * m *)
(* Proof:
      2 * ((HALF n) * m)
    = 2 * (m * HALF n)      by MULT_COMM
   <= 2 * (HALF (m * n))    by HALF_MULT
   <= m * n                 by TWO_HALF_LE_THM
    = n * m                 by MULT_COMM
*)
val TWO_HALF_TIMES_LE = store_thm(
  "TWO_HALF_TIMES_LE",
  ``!m n. 2 * ((HALF n) * m) <= n * m``,
  rpt strip_tac >>
  `2 * (m * HALF n) <= 2 * (HALF (m * n))` by rw[HALF_MULT] >>
  `2 * (HALF (m * n)) <= m * n` by rw[TWO_HALF_LE_THM] >>
  fs[]);

(* Theorem: 0 < n ==> 1 + HALF n <= n *)
(* Proof:
   If n = 1,
      HALF 1 = 0, hence true.
   If n <> 1,
      Then HALF n <> 0       by HALF_EQ_0, n <> 0, n <> 1
      Thus 1 + HALF n
        <= HALF n + HALF n   by 1 <= HALF n
         = 2 * HALF n
        <= n                 by TWO_HALF_LE_THM
*)
val HALF_ADD1_LE = store_thm(
  "HALF_ADD1_LE",
  ``!n. 0 < n ==> 1 + HALF n <= n``,
  rpt strip_tac >>
  (Cases_on `n = 1` >> simp[]) >>
  `HALF n <> 0` by metis_tac[HALF_EQ_0, NOT_ZERO] >>
  `1 + HALF n <= 2 * HALF n` by decide_tac >>
  `2 * HALF n <= n` by rw[TWO_HALF_LE_THM] >>
  decide_tac);

(* Theorem: (HALF n) ** 2 <= (n ** 2) DIV 4 *)
(* Proof:
   Let k = HALF n.
   Then 2 * k <= n                by TWO_HALF_LE_THM
     so (2 * k) ** 2 <= n ** 2                by EXP_EXP_LE_MONO
    and (2 * k) ** 2 DIV 4 <= n ** 2 DIV 4    by DIV_LE_MONOTONE, 0 < 4
    But (2 * k) ** 2 DIV 4
      = 4 * k ** 2 DIV 4          by EXP_BASE_MULT
      = k ** 2                    by MULT_TO_DIV, 0 < 4
   Thus k ** 2 <= n ** 2 DIV 4.
*)
val HALF_SQ_LE = store_thm(
  "HALF_SQ_LE",
  ``!n. (HALF n) ** 2 <= (n ** 2) DIV 4``,
  rpt strip_tac >>
  qabbrev_tac `k = HALF n` >>
  `2 * k <= n` by rw[TWO_HALF_LE_THM, Abbr`k`] >>
  `(2 * k) ** 2 <= n ** 2` by rw[] >>
  `(2 * k) ** 2 DIV 4 <= n ** 2 DIV 4` by rw[DIV_LE_MONOTONE] >>
  `(2 * k) ** 2 DIV 4 = 4 * k ** 2 DIV 4` by rw[EXP_BASE_MULT] >>
  `_ = k ** 2` by rw[MULT_TO_DIV] >>
  decide_tac);

(* Obtain theorems *)
val HALF_LE = save_thm("HALF_LE",
    DIV_LESS_EQ |> SPEC ``2`` |> SIMP_RULE (arith_ss) [] |> SPEC ``n:num`` |> GEN_ALL);
(* val HALF_LE = |- !n. HALF n <= n: thm *)
val HALF_LE_MONO = save_thm("HALF_LE_MONO",
    DIV_LE_MONOTONE |> SPEC ``2`` |> SIMP_RULE (arith_ss) []);
(* val HALF_LE_MONO = |- !x y. x <= y ==> HALF x <= HALF y: thm *)

(* Theorem: HALF (SUC n) <= n *)
(* Proof:
   If EVEN n,
      Then ?k. n = 2 * k                       by EVEN_EXISTS
       and SUC n = 2 * k + 1
        so HALF (SUC n) = k <= k + k = n       by ineqaulities
   Otherwise ODD n,                            by ODD_EVEN
      Then ?k. n = 2 * k + 1                   by ODD_EXISTS
       and SUC n = 2 * k + 2
        so HALF (SUC n) = k + 1 <= k + k + 1 = n
*)
Theorem HALF_SUC:
  !n. HALF (SUC n) <= n
Proof
  rpt strip_tac >>
  Cases_on `EVEN n` >| [
    `?k. n = 2 * k` by metis_tac[EVEN_EXISTS] >>
    `HALF (SUC n) = k` by simp[ADD1] >>
    decide_tac,
    `?k. n = 2 * k + 1` by metis_tac[ODD_EXISTS, ODD_EVEN, ADD1] >>
    `HALF (SUC n) = k + 1` by simp[ADD1] >>
    decide_tac
  ]
QED

(* Theorem: 0 < n ==> HALF (SUC (SUC n)) <= n *)
(* Proof:
   Note SUC (SUC n) = n + 2        by ADD1
   If EVEN n,
      then ?k. n = 2 * k           by EVEN_EXISTS
      Since n = 2 * k <> 0         by NOT_ZERO, 0 < n
        so k <> 0, or 1 <= k       by MULT_EQ_0
           HALF (n + 2)
         = k + 1                   by arithmetic
        <= k + k                   by above
         = n
   Otherwise ODD n,                by ODD_EVEN
      then ?k. n = 2 * k + 1       by ODD_EXISTS
           HALF (n + 2)
         = HALF (2 * k + 3)        by arithmetic
         = k + 1                   by arithmetic
        <= k + k + 1               by ineqaulities
         = n
*)
Theorem HALF_SUC_SUC:
  !n. 0 < n ==> HALF (SUC (SUC n)) <= n
Proof
  rpt strip_tac >>
  Cases_on `EVEN n` >| [
    `?k. n = 2 * k` by metis_tac[EVEN_EXISTS] >>
    `0 < k` by metis_tac[MULT_EQ_0, NOT_ZERO] >>
    `1 <= k` by decide_tac >>
    `HALF (SUC (SUC n)) = k + 1` by simp[ADD1] >>
    fs[],
    `?k. n = 2 * k + 1` by metis_tac[ODD_EXISTS, ODD_EVEN, ADD1] >>
    `HALF (SUC (SUC n)) = k + 1` by simp[ADD1] >>
    fs[]
  ]
QED

(* Theorem: n < HALF (SUC m) ==> 2 * n + 1 <= m *)
(* Proof:
   If EVEN m,
      Then m = 2 * HALF m                      by EVEN_HALF
       and SUC m = 2 * HALF m + 1              by ADD1
        so     n < (2 * HALF m + 1) DIV 2      by given
        or     n < HALF m                      by arithmetic
           2 * n < 2 * HALF m                  by LT_MULT_LCANCEL
           2 * n < m                           by above
       2 * n + 1 <= m                          by arithmetic
    Otherwise, ODD m                           by ODD_EVEN
       Then m = 2 * HALF m + 1                 by ODD_HALF
        and SUC m = 2 * HALF m + 2             by ADD1
         so     n < (2 * HALF m + 2) DIV 2     by given
         or     n < HALF m + 1                 by arithmetic
        2 * n + 1 < 2 * HALF m + 1             by LT_MULT_LCANCEL, LT_ADD_RCANCEL
         or 2 * n + 1 < m                      by above
    Overall, 2 * n + 1 <= m.
*)
Theorem HALF_SUC_LE:
  !n m. n < HALF (SUC m) ==> 2 * n + 1 <= m
Proof
  rpt strip_tac >>
  Cases_on `EVEN m` >| [
    `m = 2 * HALF m` by simp[EVEN_HALF] >>
    `HALF (SUC m) =  HALF (2 * HALF m + 1)` by metis_tac[ADD1] >>
    `_ = HALF m` by simp[] >>
    simp[],
    `m = 2 * HALF m + 1` by simp[ODD_HALF, ODD_EVEN] >>
    `HALF (SUC m) =  HALF (2 * HALF m + 1 + 1)` by metis_tac[ADD1] >>
    `_ = HALF m + 1` by simp[] >>
    simp[]
  ]
QED

(* Theorem: 2 * n < m ==> n <= HALF m *)
(* Proof:
   If EVEN m,
      Then m = 2 * HALF m                      by EVEN_HALF
        so 2 * n < 2 * HALF m                  by above
        or     n < HALF m                      by LT_MULT_LCANCEL
    Otherwise, ODD m                           by ODD_EVEN
       Then m = 2 * HALF m + 1                 by ODD_HALF
         so 2 * n < 2 * HALF m + 1             by above
         so 2 * n <= 2 * HALF m                by removing 1
         or     n <= HALF m                    by LE_MULT_LCANCEL
    Overall, n <= HALF m.
*)
Theorem HALF_EVEN_LE:
  !n m. 2 * n < m ==> n <= HALF m
Proof
  rpt strip_tac >>
  Cases_on `EVEN m` >| [
    `2 * n < 2 * HALF m` by metis_tac[EVEN_HALF] >>
    simp[],
    `2 * n < 2 * HALF m + 1` by metis_tac[ODD_HALF, ODD_EVEN] >>
    simp[]
  ]
QED

(* Theorem: 2 * n + 1 < m ==> n < HALF m *)
(* Proof:
   If EVEN m,
      Then m = 2 * HALF m                      by EVEN_HALF
        so 2 * n + 1 < 2 * HALF m              by above
        or     2 * n < 2 * HALF m              by removing 1
        or     n < HALF m                      by LT_MULT_LCANCEL
    Otherwise, ODD m                           by ODD_EVEN
       Then m = 2 * HALF m + 1                 by ODD_HALF
         so 2 * n + 1 < 2 * HALF m + 1         by above
         or     2 * n < 2 * HALF m             by LT_ADD_RCANCEL
         or         n < HALF m                 by LT_MULT_LCANCEL
    Overall, n < HALF m.
*)
Theorem HALF_ODD_LT:
  !n m. 2 * n + 1 < m ==> n < HALF m
Proof
  rpt strip_tac >>
  Cases_on `EVEN m` >| [
    `2 * n + 1 < 2 * HALF m` by metis_tac[EVEN_HALF] >>
    simp[],
    `2 * n + 1 < 2 * HALF m + 1` by metis_tac[ODD_HALF, ODD_EVEN] >>
    simp[]
  ]
QED

(* Theorem: EVEN n ==> !m. m * n = (TWICE m) * (HALF n) *)
(* Proof:
     (TWICE m) * (HALF n)
   = (2 * m) * (HALF n)   by notation
   = m * TWICE (HALF n)   by MULT_COMM, MULT_ASSOC
   = m * n                by EVEN_HALF
*)
val MULT_EVEN = store_thm(
  "MULT_EVEN",
  ``!n. EVEN n ==> !m. m * n = (TWICE m) * (HALF n)``,
  metis_tac[MULT_COMM, MULT_ASSOC, EVEN_HALF]);

(* Theorem: ODD n ==> !m. m * n = m + (TWICE m) * (HALF n) *)
(* Proof:
     m + (TWICE m) * (HALF n)
   = m + (2 * m) * (HALF n)     by notation
   = m + m * (TWICE (HALF n))   by MULT_COMM, MULT_ASSOC
   = m * (SUC (TWICE (HALF n))) by MULT_SUC
   = m * (TWICE (HALF n) + 1)   by ADD1
   = m * n                      by ODD_HALF
*)
val MULT_ODD = store_thm(
  "MULT_ODD",
  ``!n. ODD n ==> !m. m * n = m + (TWICE m) * (HALF n)``,
  metis_tac[MULT_COMM, MULT_ASSOC, ODD_HALF, MULT_SUC, ADD1]);

(* Theorem: EVEN m /\ m <> 0 ==> !n. EVEN n <=> EVEN (n MOD m) *)
(* Proof:
   Note ?k. m = 2 * k                by EVEN_EXISTS, EVEN m
    and k <> 0                       by MULT_EQ_0, m <> 0
    ==> (n MOD m) MOD 2 = n MOD 2    by MOD_MULT_MOD
   The result follows                by EVEN_MOD2
*)
val EVEN_MOD_EVEN = store_thm(
  "EVEN_MOD_EVEN",
  ``!m. EVEN m /\ m <> 0 ==> !n. EVEN n <=> EVEN (n MOD m)``,
  rpt strip_tac >>
  `?k. m = 2 * k` by rw[GSYM EVEN_EXISTS] >>
  `(n MOD m) MOD 2 = n MOD 2` by rw[MOD_MULT_MOD] >>
  metis_tac[EVEN_MOD2]);

(* Theorem: EVEN m /\ m <> 0 ==> !n. ODD n <=> ODD (n MOD m) *)
(* Proof: by EVEN_MOD_EVEN, ODD_EVEN *)
val EVEN_MOD_ODD = store_thm(
  "EVEN_MOD_ODD",
  ``!m. EVEN m /\ m <> 0 ==> !n. ODD n <=> ODD (n MOD m)``,
  rw_tac std_ss[EVEN_MOD_EVEN, ODD_EVEN]);

(* Theorem: c <= a ==> ((a - b) - (a - c) = c - b) *)
(* Proof:
     a - b - (a - c)
   = a - (b + (a - c))     by SUB_RIGHT_SUB, no condition
   = a - ((a - c) + b)     by ADD_COMM, no condition
   = a - (a - c) - b       by SUB_RIGHT_SUB, no condition
   = a + c - a - b         by SUB_SUB, c <= a
   = c + a - a - b         by ADD_COMM, no condition
   = c + (a - a) - b       by LESS_EQ_ADD_SUB, a <= a
   = c + 0 - b             by SUB_EQUAL_0
   = c - b
*)
val SUB_SUB_SUB = store_thm(
  "SUB_SUB_SUB",
  ``!a b c. c <= a ==> ((a - b) - (a - c) = c - b)``,
  decide_tac);

(* Theorem: c <= a ==> (a + b - (a - c) = c + b) *)
(* Proof:
     a + b - (a - c)
   = a + b + c - a      by SUB_SUB, a <= c
   = a + (b + c) - a    by ADD_ASSOC
   = (b + c) + a - a    by ADD_COMM
   = b + c - (a - a)    by SUB_SUB, a <= a
   = b + c - 0          by SUB_EQUAL_0
   = b + c              by SUB_0
*)
val ADD_SUB_SUB = store_thm(
  "ADD_SUB_SUB",
  ``!a b c. c <= a ==> (a + b - (a - c) = c + b)``,
  decide_tac);

(* Theorem: 0 < p ==> !m n. (m - n = p) <=> (m = n + p) *)
(* Proof:
   If part: m - n = p ==> m = n + p
      Note 0 < m - n          by 0 < p
        so n < m              by LESS_MONO_ADD
        or m = m - n + n      by SUB_ADD, n <= m
             = p + n          by m - n = p
             = n + p          by ADD_COMM
   Only-if part: m = n + p ==> m - n = p
        m - n
      = (n + p) - n           by m = n + p
      = p + n - n             by ADD_COMM
      = p                     by ADD_SUB
*)
val SUB_EQ_ADD = store_thm(
  "SUB_EQ_ADD",
  ``!p. 0 < p ==> !m n. (m - n = p) <=> (m = n + p)``,
  decide_tac);

(* Note: ADD_EQ_SUB |- !m n p. n <= p ==> ((m + n = p) <=> (m = p - n)) *)

(* Theorem: 0 < a /\ 0 < b /\ a < c /\ (a * b = c * d) ==> (d < b) *)
(* Proof:
   By contradiction, suppose b <= d.
   Since a * b <> 0         by MULT_EQ_0, 0 < a, 0 < b
      so d <> 0, or 0 < d   by MULT_EQ_0, a * b <> 0
     Now a * b <= a * d     by LE_MULT_LCANCEL, b <= d, a <> 0
     and a * d < c * d      by LT_MULT_LCANCEL, a < c, d <> 0
      so a * b < c * d      by LESS_EQ_LESS_TRANS
    This contradicts a * b = c * d.
*)
val MULT_EQ_LESS_TO_MORE = store_thm(
  "MULT_EQ_LESS_TO_MORE",
  ``!a b c d. 0 < a /\ 0 < b /\ a < c /\ (a * b = c * d) ==> (d < b)``,
  spose_not_then strip_assume_tac >>
  `b <= d` by decide_tac >>
  `0 < d` by decide_tac >>
  `a * b <= a * d` by rw[LE_MULT_LCANCEL] >>
  `a * d < c * d` by rw[LT_MULT_LCANCEL] >>
  decide_tac);

(* Theorem: 0 < c /\ 0 < d /\ a * b <= c * d /\ d < b ==> a < c *)
(* Proof:
   By contradiction, suppose c <= a.
   With d < b, which gives d <= b    by LESS_IMP_LESS_OR_EQ
   Thus c * d <= a * b               by LE_MONO_MULT2
     or a * b = c * d                by a * b <= c * d
   Note 0 < c /\ 0 < d               by given
    ==> a < c                        by MULT_EQ_LESS_TO_MORE
   This contradicts c <= a.

MULT_EQ_LESS_TO_MORE
|- !a b c d. 0 < a /\ 0 < b /\ a < c /\ a * b = c * d ==> d < b
             0 < d /\ 0 < c /\ d < b /\ d * c = b * a ==> a < c
*)
val LE_IMP_REVERSE_LT = store_thm(
  "LE_IMP_REVERSE_LT",
  ``!a b c d. 0 < c /\ 0 < d /\ a * b <= c * d /\ d < b ==> a < c``,
  spose_not_then strip_assume_tac >>
  `c <= a` by decide_tac >>
  `c * d <= a * b` by rw[LE_MONO_MULT2] >>
  `a * b = c * d` by decide_tac >>
  `a < c` by metis_tac[MULT_EQ_LESS_TO_MORE, MULT_COMM]);

(* ------------------------------------------------------------------------- *)
(* Exponential Theorems                                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: n ** 0 = 1 *)
(* Proof: by EXP *)
val EXP_0 = store_thm(
  "EXP_0",
  ``!n. n ** 0 = 1``,
  rw_tac std_ss[EXP]);

(* Theorem: n ** 2 = n * n *)
(* Proof:
   n ** 2 = n * (n ** 1) = n * (n * (n ** 0)) = n * (n * 1) = n * n
   or n ** 2 = n * (n ** 1) = n * n  by EXP_1:  !n. (1 ** n = 1) /\ (n ** 1 = n)
*)
val EXP_2 = store_thm(
  "EXP_2",
  ``!n. n ** 2 = n * n``,
  metis_tac[EXP, TWO, EXP_1]);

(* Theorem: m <> 0 ==> m ** n <> 0 *)
(* Proof: by EXP_EQ_0 *)
val EXP_NONZERO = store_thm(
  "EXP_NONZERO",
  ``!m n. m <> 0 ==> m ** n <> 0``,
  metis_tac[EXP_EQ_0]);

(* Theorem: 0 < m ==> 0 < m ** n *)
(* Proof: by EXP_NONZERO *)
val EXP_POS = store_thm(
  "EXP_POS",
  ``!m n. 0 < m ==> 0 < m ** n``,
  rw[EXP_NONZERO]);

(* Theorem: 0 < m ==> ((n ** m = n) <=> ((m = 1) \/ (n = 0) \/ (n = 1))) *)
(* Proof:
   If part: n ** m = n ==> n = 0 \/ n = 1
      By contradiction, assume n <> 0 /\ n <> 1.
      Then ?k. m = SUC k            by num_CASES, 0 < m
        so  n ** SUC k = n          by n ** m = n
        or  n * n ** k = n          by EXP
       ==>      n ** k = 1          by MULT_EQ_SELF, 0 < n
       ==>      n = 1 or k = 0      by EXP_EQ_1
       ==>      n = 1 or m = 1,
      These contradict n <> 1 and m <> 1.
   Only-if part: n ** 1 = n /\ 0 ** m = 0 /\ 1 ** m = 1
      These are true   by EXP_1, ZERO_EXP.
*)
val EXP_EQ_SELF = store_thm(
  "EXP_EQ_SELF",
  ``!n m. 0 < m ==> ((n ** m = n) <=> ((m = 1) \/ (n = 0) \/ (n = 1)))``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `m <> 0` by decide_tac >>
    `?k. m = SUC k` by metis_tac[num_CASES] >>
    `n * n ** k = n` by fs[EXP] >>
    `n ** k = 1` by metis_tac[MULT_EQ_SELF, NOT_ZERO_LT_ZERO] >>
    fs[EXP_EQ_1],
    rw[],
    rw[],
    rw[]
  ]);

(* Obtain a theorem *)
val EXP_LE = save_thm("EXP_LE", X_LE_X_EXP |> GEN ``x:num`` |> SPEC ``b:num`` |> GEN_ALL);
(* val EXP_LE = |- !n b. 0 < n ==> b <= b ** n: thm *)

(* Theorem: 1 < b /\ 1 < n ==> b < b ** n *)
(* Proof:
   By contradiction, assume ~(b < b ** n).
   Then b ** n <= b       by arithmetic
    But b <= b ** n       by EXP_LE, 0 < n
    ==> b ** n = b        by EQ_LESS_EQ
    ==> b = 1 or n = 0 or n = 1.
   All these contradict 1 < b and 1 < n.
*)
val EXP_LT = store_thm(
  "EXP_LT",
  ``!n b. 1 < b /\ 1 < n ==> b < b ** n``,
  spose_not_then strip_assume_tac >>
  `b <= b ** n` by rw[EXP_LE] >>
  `b ** n = b` by decide_tac >>
  rfs[EXP_EQ_SELF]);

(* Theorem: 0 < a /\ n < m /\ (a ** n * b = a ** m * c) ==> ?d. 0 < d /\ (b = a ** d * c) *)
(* Proof:
   Let d = m - n.
   Then 0 < d, and  m = n + d       by arithmetic
    and 0 < a ==> a ** n <> 0       by EXP_EQ_0
      a ** n * b
    = a ** (n + d) * c              by m = n + d
    = (a ** n * a ** d) * c         by EXP_ADD
    = a ** n * (a ** d * c)         by MULT_ASSOC
   The result follows               by MULT_LEFT_CANCEL
*)
val EXP_LCANCEL = store_thm(
  "EXP_LCANCEL",
  ``!a b c n m. 0 < a /\ n < m /\ (a ** n * b = a ** m * c) ==> ?d. 0 < d /\ (b = a ** d * c)``,
  rpt strip_tac >>
  `0 < m - n /\ (m = n + (m - n))` by decide_tac >>
  qabbrev_tac `d = m - n` >>
  `a ** n <> 0` by metis_tac[EXP_EQ_0, NOT_ZERO_LT_ZERO] >>
  metis_tac[EXP_ADD, MULT_ASSOC, MULT_LEFT_CANCEL]);

(* Theorem: 0 < a /\ n < m /\ (a ** n * b = a ** m * c) ==> ?d. 0 < d /\ (b = a ** d * c) *)
(* Proof: by EXP_LCANCEL, MULT_COMM. *)
val EXP_RCANCEL = store_thm(
  "EXP_RCANCEL",
  ``!a b c n m. 0 < a /\ n < m /\ (b * a ** n = c * a ** m) ==> ?d. 0 < d /\ (b = c * a ** d)``,
  metis_tac[EXP_LCANCEL, MULT_COMM]);

(*
EXP_POS      |- !m n. 0 < m ==> 0 < m ** n
ONE_LT_EXP   |- !x y. 1 < x ** y <=> 1 < x /\ 0 < y
ZERO_LT_EXP  |- 0 < x ** y <=> 0 < x \/ (y = 0)
*)

(* Theorem: 0 < m ==> 1 <= m ** n *)
(* Proof:
   0 < m ==>  0 < m ** n      by EXP_POS
          or 1 <= m ** n      by arithmetic
*)
val ONE_LE_EXP = store_thm(
  "ONE_LE_EXP",
  ``!m n. 0 < m ==> 1 <= m ** n``,
  metis_tac[EXP_POS, DECIDE``!x. 0 < x <=> 1 <= x``]);

(* Theorem: EVEN n ==> !m. m ** n = (SQ m) ** (HALF n) *)
(* Proof:
     (SQ m) ** (HALF n)
   = (m ** 2) ** (HALF n)   by notation
   = m ** (2 * HALF n)      by EXP_EXP_MULT
   = m ** n                 by EVEN_HALF
*)
val EXP_EVEN = store_thm(
  "EXP_EVEN",
  ``!n. EVEN n ==> !m. m ** n = (SQ m) ** (HALF n)``,
  rpt strip_tac >>
  `(SQ m) ** (HALF n) = m ** (2 * HALF n)` by rw[EXP_EXP_MULT] >>
  `_ = m ** n` by rw[GSYM EVEN_HALF] >>
  rw[]);

(* Theorem: ODD n ==> !m. m ** n = m * (SQ m) ** (HALF n) *)
(* Proof:
     m * (SQ m) ** (HALF n)
   = m * (m ** 2) ** (HALF n)   by notation
   = m * m ** (2 * HALF n)      by EXP_EXP_MULT
   = m ** (SUC (2 * HALF n))    by EXP
   = m ** (2 * HALF n + 1)      by ADD1
   = m ** n                     by ODD_HALF
*)
val EXP_ODD = store_thm(
  "EXP_ODD",
  ``!n. ODD n ==> !m. m ** n = m * (SQ m) ** (HALF n)``,
  rpt strip_tac >>
  `m * (SQ m) ** (HALF n) = m * m ** (2 * HALF n)` by rw[EXP_EXP_MULT] >>
  `_ = m ** (2 * HALF n + 1)` by rw[GSYM EXP, ADD1] >>
  `_ = m ** n` by rw[GSYM ODD_HALF] >>
  rw[]);

(* An exponentiation identity *)
(* val EXP_THM = save_thm("EXP_THM", CONJ EXP_EVEN EXP_ODD); *)
(*
val EXP_THM = |- (!n. EVEN n ==> !m. m ** n = SQ m ** HALF n) /\
                  !n. ODD n ==> !m. m ** n = m * SQ m ** HALF n: thm
*)
(* Next is better *)

(* Theorem: m ** n = if n = 0 then 1 else if n = 1 then m else
            if EVEN n then (m * m) ** HALF n else m * ((m * m) ** (HALF n)) *)
(* Proof: mainly by EXP_EVEN, EXP_ODD. *)
Theorem EXP_THM:
  !m n. m ** n = if n = 0 then 1 else if n = 1 then m
                 else if EVEN n then (m * m) ** HALF n
                 else m * ((m * m) ** (HALF n))
Proof
  metis_tac[EXP_0, EXP_1, EXP_EVEN, EXP_ODD, EVEN_ODD]
QED

(* Theorem: m ** n =
            if n = 0 then 1
            else if EVEN n then (m * m) ** (HALF n) else m * (m * m) ** (HALF n) *)
(* Proof:
   If n = 0, to show:
      m ** 0 = 1, true                      by EXP_0
   If EVEN n, to show:
      m ** n = (m * m) ** (HALF n), true    by EXP_EVEN
   If ~EVEN n, ODD n, to show:              by EVEN_ODD
      m ** n = m * (m * m) ** HALF n, true  by EXP_ODD
*)
val EXP_EQN = store_thm(
  "EXP_EQN",
  ``!m n. m ** n =
         if n = 0 then 1
         else if EVEN n then (m * m) ** (HALF n) else m * (m * m) ** (HALF n)``,
  rw[] >-
  rw[Once EXP_EVEN] >>
  `ODD n` by metis_tac[EVEN_ODD] >>
  rw[Once EXP_ODD]);

(* Theorem: m ** n = if n = 0 then 1 else (if EVEN n then 1 else m) * (m * m) ** (HALF n) *)
(* Proof: by EXP_EQN *)
val EXP_EQN_ALT = store_thm(
  "EXP_EQN_ALT",
  ``!m n. m ** n =
         if n = 0 then 1
         else (if EVEN n then 1 else m) * (m * m) ** (HALF n)``,
  rw[Once EXP_EQN]);

(* Theorem: m ** n = (if n = 0 then 1 else (if EVEN n then 1 else m) * (m ** 2) ** HALF n) *)
(* Proof: by EXP_EQN_ALT, EXP_2 *)
val EXP_ALT_EQN = store_thm(
  "EXP_ALT_EQN",
  ``!m n. m ** n = (if n = 0 then 1 else (if EVEN n then 1 else m) * (m ** 2) ** HALF n)``,
  metis_tac[EXP_EQN_ALT, EXP_2]);

(* Theorem: 1 < m ==>
      (b ** n) MOD m = if (n = 0) then 1
                       else let result = (b * b) ** (HALF n) MOD m
                             in if EVEN n then result else (b * result) MOD m *)
(* Proof:
   This is to show:
   (1) 1 < m ==> b ** 0 MOD m = 1
         b ** 0 MOD m
       = 1 MOD m            by EXP_0
       = 1                  by ONE_MOD, 1 < m
   (2) EVEN n ==> b ** n MOD m = (b ** 2) ** HALF n MOD m
         b ** n MOD m
       = (b * b) ** HALF n MOD m    by EXP_EVEN
       = (b ** 2) ** HALF n MOD m   by EXP_2
   (3) ~EVEN n ==> b ** n MOD m = (b * (b ** 2) ** HALF n) MOD m
         b ** n MOD m
       = (b * (b * b) ** HALF n) MOD m      by EXP_ODD, EVEN_ODD
       = (b * (b ** 2) ** HALF n) MOD m     by EXP_2
*)
Theorem EXP_MOD_EQN:
  !b n m. 1 < m ==>
      ((b ** n) MOD m =
       if (n = 0) then 1
       else let result = (b * b) ** (HALF n) MOD m
             in if EVEN n then result else (b * result) MOD m)
Proof
  rw[]
  >- metis_tac[EXP_EVEN, EXP_2] >>
  metis_tac[EXP_ODD, EXP_2, EVEN_ODD]
QED

(* Pretty version of EXP_MOD_EQN, same pattern as EXP_EQN_ALT. *)

(* Theorem: 1 < m ==> b ** n MOD m =
           if n = 0 then 1 else
           ((if EVEN n then 1 else b) * ((SQ b ** HALF n) MOD m)) MOD m *)
(* Proof: by EXP_MOD_EQN *)
val EXP_MOD_ALT = store_thm(
  "EXP_MOD_ALT",
  ``!b n m. 1 < m ==> b ** n MOD m =
           if n = 0 then 1 else
           ((if EVEN n then 1 else b) * ((SQ b ** HALF n) MOD m)) MOD m``,
  rpt strip_tac >>
  imp_res_tac EXP_MOD_EQN >>
  last_x_assum (qspecl_then [`n`, `b`] strip_assume_tac) >>
  rw[]);

(* Theorem: x ** (y ** SUC n) = (x ** y) ** y ** n *)
(* Proof:
      x ** (y ** SUC n)
    = x ** (y * y ** n)     by EXP
    = (x ** y) ** (y ** n)  by EXP_EXP_MULT
*)
val EXP_EXP_SUC = store_thm(
  "EXP_EXP_SUC",
  ``!x y n. x ** (y ** SUC n) = (x ** y) ** y ** n``,
  rw[EXP, EXP_EXP_MULT]);

(* Theorem: 1 + n * m <= (1 + m) ** n *)
(* Proof:
   By induction on n.
   Base: 1 + 0 * m <= (1 + m) ** 0
        LHS = 1 + 0 * m = 1            by arithmetic
        RHS = (1 + m) ** 0 = 1         by EXP_0
        Hence true.
   Step: 1 + n * m <= (1 + m) ** n ==>
         1 + SUC n * m <= (1 + m) ** SUC n
          1 + SUC n * m
        = 1 + n * m + m                     by MULT
        <= (1 + m) ** n + m                 by induction hypothesis
        <= (1 + m) ** n + m * (1 + m) ** n  by EXP_POS
        <= (1 + m) * (1 + m) ** n           by RIGHT_ADD_DISTRIB
         = (1 + m) ** SUC n                 by EXP
*)
val EXP_LOWER_LE_LOW = store_thm(
  "EXP_LOWER_LE_LOW",
  ``!n m. 1 + n * m <= (1 + m) ** n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[EXP_0] >>
  `0 < (1 + m) ** n` by rw[] >>
  `1 + SUC n * m = 1 + (n * m + m)` by rw[MULT] >>
  `_ = 1 + n * m + m` by decide_tac >>
  `m <= m * (1 + m) ** n` by rw[] >>
  `1 + SUC n * m <= (1 + m) ** n + m * (1 + m) ** n` by decide_tac >>
  `(1 + m) ** n + m * (1 + m) ** n = (1 + m) * (1 + m) ** n` by decide_tac >>
  `_ = (1 + m) ** SUC n` by rw[EXP] >>
  decide_tac);

(* Theorem: 0 < m /\ 1 < n ==> 1 + n * m < (1 + m) ** n *)
(* Proof:
   By induction on n.
   Base: 1 < 0 ==> 1 + 0 * m <= (1 + m) ** 0
        True since 1 < 0 = F.
   Step: 1 < n ==> 1 + n * m < (1 + m) ** n ==>
         1 < SUC n ==> 1 + SUC n * m < (1 + m) ** SUC n
      Note n <> 0, since SUC 0 = 1          by ONE
      If n = 1,
         Note m * m <> 0                    by MULT_EQ_0, m <> 0
           (1 + m) ** SUC 1
         = (1 + m) ** 2                     by TWO
         = 1 + 2 * m + m * m                by expansion
         > 1 + 2 * m                        by 0 < m * m
         = 1 + (SUC 1) * m
      If n <> 1, then 1 < n.
          1 + SUC n * m
        = 1 + n * m + m                     by MULT
         < (1 + m) ** n + m                 by induction hypothesis, 1 < n
        <= (1 + m) ** n + m * (1 + m) ** n  by EXP_POS
        <= (1 + m) * (1 + m) ** n           by RIGHT_ADD_DISTRIB
         = (1 + m) ** SUC n                 by EXP
*)
val EXP_LOWER_LT_LOW = store_thm(
  "EXP_LOWER_LT_LOW",
  ``!n m. 0 < m /\ 1 < n ==> 1 + n * m < (1 + m) ** n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rpt strip_tac >>
  `n <> 0` by fs[] >>
  Cases_on `n = 1` >| [
    simp[] >>
    `(m + 1) ** 2 = (m + 1) * (m + 1)` by rw[GSYM EXP_2] >>
    `_ = m * m + 2 * m + 1` by decide_tac >>
    `0 < SQ m` by metis_tac[SQ_EQ_0, NOT_ZERO_LT_ZERO] >>
    decide_tac,
    `1 < n` by decide_tac >>
    `0 < (1 + m) ** n` by rw[] >>
    `1 + SUC n * m = 1 + (n * m + m)` by rw[MULT] >>
    `_ = 1 + n * m + m` by decide_tac >>
    `m <= m * (1 + m) ** n` by rw[] >>
    `1 + SUC n * m < (1 + m) ** n + m * (1 + m) ** n` by decide_tac >>
    `(1 + m) ** n + m * (1 + m) ** n = (1 + m) * (1 + m) ** n` by decide_tac >>
    `_ = (1 + m) ** SUC n` by rw[EXP] >>
    decide_tac
  ]);

(*
Note: EXP_LOWER_LE_LOW collects the first two terms of binomial expansion.
  but EXP_LOWER_LE_HIGH collects the last two terms of binomial expansion.
*)

(* Theorem: n * m ** (n - 1) + m ** n <= (1 + m) ** n *)
(* Proof:
   By induction on n.
   Base: 0 * m ** (0 - 1) + m ** 0 <= (1 + m) ** 0
        LHS = 0 * m ** (0 - 1) + m ** 0
            = 0 + 1                      by EXP_0
            = 1
           <= 1 = (1 + m) ** 0 = RHS     by EXP_0
   Step: n * m ** (n - 1) + m ** n <= (1 + m) ** n ==>
         SUC n * m ** (SUC n - 1) + m ** SUC n <= (1 + m) ** SUC n
        If n = 0,
           LHS = 1 * m ** 0 + m ** 1
               = 1 + m                   by EXP_0, EXP_1
               = (1 + m) ** 1 = RHS      by EXP_1
        If n <> 0,
           Then SUC (n - 1) = n          by n <> 0.
           LHS = SUC n * m ** (SUC n - 1) + m ** SUC n
               = (n + 1) * m ** n + m * m ** n     by EXP, ADD1
               = (n + 1 + m) * m ** n              by arithmetic
               = n * m ** n + (1 + m) * m ** n     by arithmetic
               = n * m ** SUC (n - 1) + (1 + m) * m ** n    by SUC (n - 1) = n
               = n * m * m ** (n - 1) + (1 + m) * m ** n    by EXP
               = m * (n * m ** (n - 1)) + (1 + m) * m ** n  by arithmetic
              <= (1 + m) * (n * m ** (n - 1)) + (1 + m) * m ** n   by m < 1 + m
               = (1 + m) * (n * m ** (n - 1) + m ** n)      by LEFT_ADD_DISTRIB
              <= (1 + m) * (1 + m) ** n                     by induction hypothesis
               = (1 + m) ** SUC n                           by EXP
*)
val EXP_LOWER_LE_HIGH = store_thm(
  "EXP_LOWER_LE_HIGH",
  ``!n m. n * m ** (n - 1) + m ** n <= (1 + m) ** n``,
  rpt strip_tac >>
  Induct_on `n` >-
  simp[] >>
  Cases_on `n = 0` >-
  simp[EXP_0] >>
  `SUC (n - 1) = n` by decide_tac >>
  simp[EXP] >>
  simp[ADD1] >>
  `m * m ** n + (n + 1) * m ** n = (m + (n + 1)) * m ** n` by rw[LEFT_ADD_DISTRIB] >>
  `_ = (n + (m + 1)) * m ** n` by decide_tac >>
  `_ = n * m ** n + (m + 1) * m ** n` by rw[LEFT_ADD_DISTRIB] >>
  `_ = n * m ** SUC (n - 1) + (m + 1) * m ** n` by rw[] >>
  `_ = n * (m * m ** (n - 1)) + (m + 1) * m ** n` by rw[EXP] >>
  `_ = m * (n * m ** (n - 1)) + (m + 1) * m ** n` by decide_tac >>
  `m * (n * m ** (n - 1)) + (m + 1) * m ** n <= (m + 1) * (n * m ** (n - 1)) + (m + 1) * m ** n` by decide_tac >>
  qabbrev_tac `t = n * m ** (n - 1) + m ** n` >>
  `(m + 1) * (n * m ** (n - 1)) + (m + 1) * m ** n = (m + 1) * t` by rw[LEFT_ADD_DISTRIB, Abbr`t`] >>
  `t <= (m + 1) ** n` by metis_tac[ADD_COMM] >>
  `(m + 1) * t <= (m + 1) * (m + 1) ** n` by rw[] >>
  decide_tac);

(* Theorem: 1 < n ==> SUC n < 2 ** n *)
(* Proof:
   Note 1 + n < (1 + 1) ** n    by EXP_LOWER_LT_LOW, m = 1
     or SUC n < SUC 1 ** n      by ADD1
     or SUC n < 2 ** n          by TWO
*)
val SUC_X_LT_2_EXP_X = store_thm(
  "SUC_X_LT_2_EXP_X",
  ``!n. 1 < n ==> SUC n < 2 ** n``,
  rpt strip_tac >>
  `1 + n * 1 < (1 + 1) ** n` by rw[EXP_LOWER_LT_LOW] >>
  fs[]);

(* ------------------------------------------------------------------------- *)
(* DIVIDES Theorems                                                          *)
(* ------------------------------------------------------------------------- *)

(* arithmeticTheory.LESS_DIV_EQ_ZERO = |- !r n. r < n ==> (r DIV n = 0) *)

(* Theorem: 0 < n ==> ((m DIV n = 0) <=> m < n) *)
(* Proof:
   If part: 0 < n /\ m DIV n = 0 ==> m < n
      Since m = m DIV n * n + m MOD n) /\ (m MOD n < n)   by DIVISION, 0 < n
         so m = 0 * n + m MOD n            by m DIV n = 0
              = 0 + m MOD n                by MULT
              = m MOD n                    by ADD
      Since m MOD n < n, m < n.
   Only-if part: 0 < n /\ m < n ==> m DIV n = 0
      True by LESS_DIV_EQ_ZERO.
*)
val DIV_EQUAL_0 = store_thm(
  "DIV_EQUAL_0",
  ``!m n. 0 < n ==> ((m DIV n = 0) <=> m < n)``,
  rw[EQ_IMP_THM] >-
  metis_tac[DIVISION, MULT, ADD] >>
  rw[LESS_DIV_EQ_ZERO]);
(* This is an improvement of
   arithmeticTheory.DIV_EQ_0 = |- 1 < b ==> (n DIV b = 0 <=> n < b) *)

(* Theorem: 0 < m /\ m <= n ==> 0 < n DIV m *)
(* Proof:
   Note n = (n DIV m) * m + n MOD m /\
        n MDO m < m                            by DIVISION, 0 < m
    ==> n MOD m < n                            by m <= n
   Thus 0 < (n DIV m) * m                      by inequality
     so 0 < n DIV m                            by ZERO_LESS_MULT
*)
Theorem DIV_POS:
  !m n. 0 < m /\ m <= n ==> 0 < n DIV m
Proof
  rpt strip_tac >>
  imp_res_tac (DIVISION |> SPEC_ALL) >>
  first_x_assum (qspec_then `n` strip_assume_tac) >>
  first_x_assum (qspec_then `n` strip_assume_tac) >>
  `0 < (n DIV m) * m` by decide_tac >>
  metis_tac[ZERO_LESS_MULT]
QED

(* Theorem: 0 < z ==> (x DIV z = y DIV z <=> x - x MOD z = y - y MOD z) *)
(* Proof:
   Note x = (x DIV z) * z + x MOD z            by DIVISION
    and y = (y DIV z) * z + y MDO z            by DIVISION
        x DIV z = y DIV z
    <=> (x DIV z) * z = (y DIV z) * z          by EQ_MULT_RCANCEL
    <=> x - x MOD z = y - y MOD z              by arithmetic
*)
Theorem DIV_EQ:
  !x y z. 0 < z ==> (x DIV z = y DIV z <=> x - x MOD z = y - y MOD z)
Proof
  rpt strip_tac >>
  `x = (x DIV z) * z + x MOD z` by simp[DIVISION] >>
  `y = (y DIV z) * z + y MOD z` by simp[DIVISION] >>
  `x DIV z = y DIV z <=> (x DIV z) * z = (y DIV z) * z` by simp[] >>
  decide_tac
QED

(* Theorem: a MOD n + b < n ==> (a + b) DIV n = a DIV n *)
(* Proof:
   Note 0 < n                                  by a MOD n + b < n
     a + b
   = ((a DIV n) * n + a MOD n) + b             by DIVISION, 0 < n
   = (a DIV n) * n + (a MOD n + b)             by ADD_ASSOC

   If a MOD n + b < n,
   Then (a + b) DIV n = a DIV n /\
        (a + b) MOD n = a MOD n + b            by DIVMOD_UNIQ
*)
Theorem ADD_DIV_EQ:
  !n a b. a MOD n + b < n ==> (a + b) DIV n = a DIV n
Proof
  rpt strip_tac >>
  `0 < n` by decide_tac >>
  `a = (a DIV n) * n + a MOD n` by simp[DIVISION] >>
  `a + b = (a DIV n) * n + (a MOD n + b)` by decide_tac >>
  metis_tac[DIVMOD_UNIQ]
QED

(*
DIV_LE_MONOTONE  |- !n x y. 0 < n /\ x <= y ==> x DIV n <= y DIV n
DIV_LE_X         |- !x y z. 0 < z ==> (y DIV z <= x <=> y < (x + 1) * z)
*)

(* Theorem: 0 < y /\ x <= y * z ==> x DIV y <= z *)
(* Proof:
             x <= y * z
   ==> x DIV y <= (y * z) DIV y      by DIV_LE_MONOTONE, 0 < y
                = z                  by MULT_TO_DIV
*)
val DIV_LE = store_thm(
  "DIV_LE",
  ``!x y z. 0 < y /\ x <= y * z ==> x DIV y <= z``,
  metis_tac[DIV_LE_MONOTONE, MULT_TO_DIV]);

(* Theorem: 0 < n ==> !x y. (x * n = y) ==> (x = y DIV n) *)
(* Proof:
     x = (x * n + 0) DIV n     by DIV_MULT, 0 < n
       = (x * n) DIV n         by ADD_0
*)
val DIV_SOLVE = store_thm(
  "DIV_SOLVE",
  ``!n. 0 < n ==> !x y. (x * n = y) ==> (x = y DIV n)``,
  metis_tac[DIV_MULT, ADD_0]);

(* Theorem: 0 < n ==> !x y. (n * x = y) ==> (x = y DIV n) *)
(* Proof: by DIV_SOLVE, MULT_COMM *)
val DIV_SOLVE_COMM = store_thm(
  "DIV_SOLVE_COMM",
  ``!n. 0 < n ==> !x y. (n * x = y) ==> (x = y DIV n)``,
  rw[DIV_SOLVE]);

(* Theorem: 1 < n ==> (1 DIV n = 0) *)
(* Proof:
   Since  1 = (1 DIV n) * n + (1 MOD n)   by DIVISION, 0 < n.
     and  1 MOD n = 1                     by ONE_MOD, 1 < n.
    thus  (1 DIV n) * n = 0               by arithmetic
      or  1 DIV n = 0  since n <> 0       by MULT_EQ_0
*)
val ONE_DIV = store_thm(
  "ONE_DIV",
  ``!n. 1 < n ==> (1 DIV n = 0)``,
  rpt strip_tac >>
  `0 < n /\ n <> 0` by decide_tac >>
  `1 = (1 DIV n) * n + (1 MOD n)` by rw[DIVISION] >>
  `_ = (1 DIV n) * n + 1` by rw[ONE_MOD] >>
  `(1 DIV n) * n = 0` by decide_tac >>
  metis_tac[MULT_EQ_0]);

(* Theorem: ODD n ==> !m. m divides n ==> ODD m *)
(* Proof:
   Since m divides n
     ==> ?q. n = q * m      by divides_def
   By contradiction, suppose ~ODD m.
   Then EVEN m              by ODD_EVEN
    and EVEN (q * m) = EVEN n    by EVEN_MULT
     or ~ODD n                   by ODD_EVEN
   This contradicts with ODD n.
*)
val DIVIDES_ODD = store_thm(
  "DIVIDES_ODD",
  ``!n. ODD n ==> !m. m divides n ==> ODD m``,
  metis_tac[divides_def, EVEN_MULT, EVEN_ODD]);

(* Note: For EVEN n, m divides n cannot conclude EVEN m.
Example: EVEN 2 or ODD 3 both divides EVEN 6.
*)

(* Theorem: EVEN m ==> !n. m divides n ==> EVEN n*)
(* Proof:
   Since m divides n
     ==> ?q. n = q * m      by divides_def
   Given EVEN m
    Then EVEN (q * m) = n   by EVEN_MULT
*)
val DIVIDES_EVEN = store_thm(
  "DIVIDES_EVEN",
  ``!m. EVEN m ==> !n. m divides n ==> EVEN n``,
  metis_tac[divides_def, EVEN_MULT]);

(* Theorem: EVEN n = 2 divides n *)
(* Proof:
       EVEN n
   <=> n MOD 2 = 0     by EVEN_MOD2
   <=> 2 divides n     by DIVIDES_MOD_0, 0 < 2
*)
val EVEN_ALT = store_thm(
  "EVEN_ALT",
  ``!n. EVEN n = 2 divides n``,
  rw[EVEN_MOD2, DIVIDES_MOD_0]);

(* Theorem: ODD n = ~(2 divides n) *)
(* Proof:
   Note n MOD 2 < 2    by MOD_LESS
    and !x. x < 2 <=> (x = 0) \/ (x = 1)   by arithmetic
       ODD n
   <=> n MOD 2 = 1     by ODD_MOD2
   <=> ~(2 divides n)  by DIVIDES_MOD_0, 0 < 2
   Or,
   ODD n = ~(EVEN n)        by ODD_EVEN
         = ~(2 divides n)   by EVEN_ALT
*)
val ODD_ALT = store_thm(
  "ODD_ALT",
  ``!n. ODD n = ~(2 divides n)``,
  metis_tac[EVEN_ODD, EVEN_ALT]);

(* Theorem: 0 < n ==> !q. (q DIV n) * n <= q *)
(* Proof:
   Since q = (q DIV n) * n + q MOD n  by DIVISION
    Thus     (q DIV n) * n <= q       by discarding remainder
*)
val DIV_MULT_LE = store_thm(
  "DIV_MULT_LE",
  ``!n. 0 < n ==> !q. (q DIV n) * n <= q``,
  rpt strip_tac >>
  `q = (q DIV n) * n + q MOD n` by rw[DIVISION] >>
  decide_tac);

(* Theorem: 0 < n ==> !q. n divides q <=> ((q DIV n) * n = q) *)
(* Proof:
   If part: n divides q ==> q DIV n * n = q
     q = (q DIV n) * n + q MOD n  by DIVISION
       = (q DIV n) * n + 0        by MOD_EQ_0_DIVISOR, divides_def
       = (q DIV n) * n            by ADD_0
   Only-if part: q DIV n * n = q ==> n divides q
     True by divides_def
*)
val DIV_MULT_EQ = store_thm(
  "DIV_MULT_EQ",
  ``!n. 0 < n ==> !q. n divides q <=> ((q DIV n) * n = q)``,
  metis_tac[divides_def, DIVISION, MOD_EQ_0_DIVISOR, ADD_0]);
(* same as DIVIDES_EQN below *)

(* Theorem: 0 < m ==> m * (n DIV m) <= n /\ n < m * SUC (n DIV m) *)
(* Proof:
   Note n = n DIV m * m + n MOD m /\
        n MOD m < m                      by DIVISION
   Thus m * (n DIV m) <= n               by MULT_COMM
    and n < m * (n DIV m) + m
          = m * (n DIV m  + 1)           by LEFT_ADD_DISTRIB
          = m * SUC (n DIV m)            by ADD1
*)
val DIV_MULT_LESS_EQ = store_thm(
  "DIV_MULT_LESS_EQ",
  ``!m n. 0 < m ==> m * (n DIV m) <= n /\ n < m * SUC (n DIV m)``,
  ntac 3 strip_tac >>
  `(n = n DIV m * m + n MOD m) /\ n MOD m < m` by rw[DIVISION] >>
  `n < m * (n DIV m) + m` by decide_tac >>
  `m * (n DIV m) + m = m * (SUC (n DIV m))` by rw[ADD1] >>
  decide_tac);

(* Theorem: 0 < x /\ 0 < y /\ x <= y ==> !n. n DIV y <= n DIV x *)
(* Proof:
   If n DIV y = 0,
      Then 0 <= n DIV x is trivially true.
   If n DIV y <> 0,
     (n DIV y) * x <= (n DIV y) * y        by LE_MULT_LCANCEL, x <= y, n DIV y <> 0
                   <= n                    by DIV_MULT_LE
  Hence        (n DIV y) * x <= n          by LESS_EQ_TRANS
  Then ((n DIV y) * x) DIV x <= n DIV x    by DIV_LE_MONOTONE
  or                 n DIV y <= n DIV x    by MULT_DIV
*)
val DIV_LE_MONOTONE_REVERSE = store_thm(
  "DIV_LE_MONOTONE_REVERSE",
  ``!x y. 0 < x /\ 0 < y /\ x <= y ==> !n. n DIV y <= n DIV x``,
  rpt strip_tac >>
  Cases_on `n DIV y = 0` >-
  decide_tac >>
  `(n DIV y) * x <= (n DIV y) * y` by rw[LE_MULT_LCANCEL] >>
  `(n DIV y) * y <= n` by rw[DIV_MULT_LE] >>
  `(n DIV y) * x <= n` by decide_tac >>
  `((n DIV y) * x) DIV x <= n DIV x` by rw[DIV_LE_MONOTONE] >>
  metis_tac[MULT_DIV]);

(* Theorem: n divides m <=> (m = (m DIV n) * n) *)
(* Proof:
   Since n divides m <=> m MOD n = 0     by DIVIDES_MOD_0
     and m = (m DIV n) * n + (m MOD n)   by DIVISION
   If part: n divides m ==> m = m DIV n * n
      This is true                       by ADD_0
   Only-if part: m = m DIV n * n ==> n divides m
      Since !x y. x + y = x <=> y = 0    by ADD_INV_0
   The result follows.
*)
val DIVIDES_EQN = store_thm(
  "DIVIDES_EQN",
  ``!n. 0 < n ==> !m. n divides m <=> (m = (m DIV n) * n)``,
  metis_tac[DIVISION, DIVIDES_MOD_0, ADD_0, ADD_INV_0]);

(* Theorem: 0 < n ==> !m. n divides m <=> (m = n * (m DIV n)) *)
(* Proof: vy DIVIDES_EQN, MULT_COMM *)
val DIVIDES_EQN_COMM = store_thm(
  "DIVIDES_EQN_COMM",
  ``!n. 0 < n ==> !m. n divides m <=> (m = n * (m DIV n))``,
  rw_tac std_ss[DIVIDES_EQN, MULT_COMM]);

(* Theorem: 0 < n /\ n <= m ==> ((m - n) DIV n = m DIV n - 1) *)
(* Proof:
   Apply DIV_SUB |> GEN_ALL |> SPEC ``1`` |> REWRITE_RULE[MULT_RIGHT_1];
   val it = |- !n m. 0 < n /\ n <= m ==> ((m - n) DIV n = m DIV n - 1): thm
*)
val SUB_DIV = save_thm("SUB_DIV",
    DIV_SUB |> GEN ``n:num`` |> GEN ``m:num`` |> GEN ``q:num`` |> SPEC ``1`` |> REWRITE_RULE[MULT_RIGHT_1]);
(* val SUB_DIV = |- !m n. 0 < n /\ n <= m ==> ((m - n) DIV n = m DIV n - 1): thm *)


(* Note:
SUB_DIV    |- !m n. 0 < n /\ n <= m ==> (m - n) DIV n = m DIV n - 1
SUB_MOD    |- !m n. 0 < n /\ n <= m ==> (m - n) MOD n = m MOD n
*)

(* Theorem: 0 < n ==> (m - n) DIV n = if m < n then 0 else (m DIV n - 1) *)
(* Proof:
   If m < n, then m - n = 0, so (m - n) DIV n = 0     by ZERO_DIV
   Otherwise, n <= m, and (m - n) DIV n = m DIV n - 1 by SUB_DIV
*)
val SUB_DIV_EQN = store_thm(
  "SUB_DIV_EQN",
  ``!m n. 0 < n ==> ((m - n) DIV n = if m < n then 0 else (m DIV n - 1))``,
  rw[SUB_DIV] >>
  `m - n = 0` by decide_tac >>
  rw[ZERO_DIV]);

(* Theorem: 0 < n ==> (m - n) MOD n = if m < n then 0 else m MOD n *)
(* Proof:
   If m < n, then m - n = 0, so (m - n) MOD n = 0     by ZERO_MOD
   Otherwise, n <= m, and (m - n) MOD n = m MOD n     by SUB_MOD
*)
val SUB_MOD_EQN = store_thm(
  "SUB_MOD_EQN",
  ``!m n. 0 < n ==> ((m - n) MOD n = if m < n then 0 else m MOD n)``,
  rw[SUB_MOD]);

(*
Note: !n. 0 < n ==> !k m. (m MOD n = 0) ==> ((k * n = m) <=> (k = m DIV n))    is almost MULT_EQ_DIV,
                                  but actually DIVIDES_EQN, DIVIDES_MOD_0, EQ_MULT_RCANCEL. See below.
Note: !n. 0 < n ==> !k m. (m MOD n = 0) ==> (k * n <= m <=> k <= m DIV n)      is X_LE_DIV, no m MOD n = 0.
Note: !n. 0 < n ==> !k m. (m MOD n = 0) ==> ((k + 1) * n <= m <=> k < m DIV n) is X_LT_DIV, no m MOD n = 0.
Note: !n. 0 < n ==> !k m. (m MOD n = 0) ==> (k * n < m <=> k < m DIV n)        is below next.
*)

(* Theorem: 0 < n ==> !k m. (m MOD n = 0) ==> ((k * n = m) <=> (k = m DIV n)) *)
(* Proof:
   Note m MOD n = 0
    ==> n divides m            by DIVIDES_MOD_0, 0 < n
    ==> m = (m DIV n) * n      by DIVIDES_EQN, 0 < n
       k * n = m
   <=> k * n = (m DIV n) * n   by above
   <=>     k = (m DIV n)       by EQ_MULT_RCANCEL, n <> 0.
*)
val DIV_EQ_MULT = store_thm(
  "DIV_EQ_MULT",
  ``!n. 0 < n ==> !k m. (m MOD n = 0) ==> ((k * n = m) <=> (k = m DIV n))``,
  rpt strip_tac >>
  `n <> 0` by decide_tac >>
  `m = (m DIV n) * n` by rw[GSYM DIVIDES_EQN, DIVIDES_MOD_0] >>
  metis_tac[EQ_MULT_RCANCEL]);

(* Theorem: 0 < n ==> !k m. (m MOD n = 0) ==> (k * n < m <=> k < m DIV n) *)
(* Proof:
       k * n < m
   <=> k * n < (m DIV n) * n    by DIVIDES_EQN, DIVIDES_MOD_0, 0 < n
   <=>     k < m DIV n          by LT_MULT_RCANCEL, n <> 0
*)
val MULT_LT_DIV = store_thm(
  "MULT_LT_DIV",
  ``!n. 0 < n ==> !k m. (m MOD n = 0) ==> (k * n < m <=> k < m DIV n)``,
  metis_tac[DIVIDES_EQN, DIVIDES_MOD_0, LT_MULT_RCANCEL, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < n ==> !k m. (m MOD n = 0) ==> (m <= n * k <=> m DIV n <= k) *)
(* Proof:
       m <= n * k
   <=> (m DIV n) * n <= n * k   by DIVIDES_EQN, DIVIDES_MOD_0, 0 < n
   <=> (m DIV n) * n <= k * n   by MULT_COMM
   <=>       m DIV n <= k       by LE_MULT_RCANCEL, n <> 0
*)
val LE_MULT_LE_DIV = store_thm(
  "LE_MULT_LE_DIV",
  ``!n. 0 < n ==> !k m. (m MOD n = 0) ==> (m <= n * k <=> m DIV n <= k)``,
  metis_tac[DIVIDES_EQN, DIVIDES_MOD_0, MULT_COMM, LE_MULT_RCANCEL, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < m ==> ((n DIV m = 0) /\ (n MOD m = 0) <=> (n = 0)) *)
(* Proof:
   If part: (n DIV m = 0) /\ (n MOD m = 0) ==> (n = 0)
      Note n DIV m = 0 ==> n < m        by DIV_EQUAL_0
      Thus n MOD m = n                  by LESS_MOD
        or n = 0
   Only-if part: 0 DIV m = 0            by ZERO_DIV
                 0 MOD m = 0            by ZERO_MOD
*)
Theorem DIV_MOD_EQ_0:
  !m n. 0 < m ==> ((n DIV m = 0) /\ (n MOD m = 0) <=> (n = 0))
Proof
  rpt strip_tac >>
  rw[EQ_IMP_THM] >>
  metis_tac[DIV_EQUAL_0, LESS_MOD]
QED

(* Theorem: 0 < m /\ 0 < n /\ (n MOD m = 0) ==> n DIV (SUC m) < n DIV m *)
(* Proof:
   Note n = n DIV (SUC m) * (SUC m) + n MOD (SUC m)   by DIVISION
          = n DIV m * m + n MOD m                     by DIVISION
          = n DIV m * m                               by n MOD m = 0
   Thus n DIV SUC m * SUC m <= n DIV m * m            by arithmetic
   Note m < SUC m                                     by LESS_SUC
    and n DIV m <> 0, or 0 < n DIV m                  by DIV_MOD_EQ_0
   Thus n DIV (SUC m) < n DIV m                       by LE_IMP_REVERSE_LT
*)
val DIV_LT_SUC = store_thm(
  "DIV_LT_SUC",
  ``!m n. 0 < m /\ 0 < n /\ (n MOD m = 0) ==> n DIV (SUC m) < n DIV m``,
  rpt strip_tac >>
  `n DIV m * m = n` by metis_tac[DIVISION, ADD_0] >>
  `_ = n DIV (SUC m) * (SUC m) + n MOD (SUC m)` by metis_tac[DIVISION, SUC_POS] >>
  `n DIV SUC m * SUC m <= n DIV m * m` by decide_tac >>
  `m < SUC m` by decide_tac >>
  `0 < n DIV m` by metis_tac[DIV_MOD_EQ_0, NOT_ZERO_LT_ZERO] >>
  metis_tac[LE_IMP_REVERSE_LT]);

(* Theorem: 0 < x /\ 0 < y /\ x < y ==> !n. 0 < n /\ (n MOD x = 0) ==> n DIV y < n DIV x *)
(* Proof:
   Note x < y ==> SUC x <= y                by arithmetic
   Thus n DIV y <= n DIV (SUC x)            by DIV_LE_MONOTONE_REVERSE
    But 0 < x /\ 0 < n /\ (n MOD x = 0)     by given
    ==> n DIV (SUC x) < n DIV x             by DIV_LT_SUC
   Hence n DIV y < n DIV x                  by inequalities
*)
val DIV_LT_MONOTONE_REVERSE = store_thm(
  "DIV_LT_MONOTONE_REVERSE",
  ``!x y. 0 < x /\ 0 < y /\ x < y ==> !n. 0 < n /\ (n MOD x = 0) ==> n DIV y < n DIV x``,
  rpt strip_tac >>
  `SUC x <= y` by decide_tac >>
  `n DIV y <= n DIV (SUC x)` by rw[DIV_LE_MONOTONE_REVERSE] >>
  `n DIV (SUC x) < n DIV x` by rw[DIV_LT_SUC] >>
  decide_tac);

(* Theorem: 0 < n /\ a ** n divides b ==> a divides b *)
(* Proof:
   Note ?k. n = SUC k              by num_CASES, n <> 0
    and ?q. b = q * (a ** n)       by divides_def
              = q * (a * a ** k)   by EXP
              = (q * a ** k) * a   by arithmetic
   Thus a divides b                by divides_def
*)
val EXP_DIVIDES = store_thm(
  "EXP_DIVIDES",
  ``!a b n. 0 < n /\ a ** n divides b ==> a divides b``,
  rpt strip_tac >>
  `?k. n = SUC k` by metis_tac[num_CASES, NOT_ZERO_LT_ZERO] >>
  `?q. b = q * a ** n` by rw[GSYM divides_def] >>
  `_ = q * (a * a ** k)` by rw[EXP] >>
  `_ = (q * a ** k) * a` by decide_tac >>
  metis_tac[divides_def]);

(* Theorem: prime a ==> a divides b iff a divides b ** n for any n *)
(* Proof:
   by induction on n.
   Base case: 0 < 0 ==> (a divides b <=> a divides (b ** 0))
     True since 0 < 0 is False.
   Step case: 0 < n ==> (a divides b <=> a divides (b ** n)) ==>
              0 < SUC n ==> (a divides b <=> a divides (b ** SUC n))
     i.e. 0 < n ==> (a divides b <=> a divides (b ** n))==>
                    a divides b <=> a divides (b * b ** n)    by EXP
     If n = 0, b ** 0 = 1   by EXP
     Hence true.
     If n <> 0, 0 < n,
     If part: a divides b /\ 0 < n ==> (a divides b <=> a divides (b ** n)) ==> a divides (b ** n)
       True by DIVIDES_MULT.
     Only-if part: a divides (b * b ** n) /\ 0 < n ==> (a divides b <=> a divides (b ** n)) ==> a divides (b ** n)
       Since prime a, a divides b, or a divides (b ** n)  by P_EUCLIDES
       Either case is true.
*)
val DIVIDES_EXP_BASE = store_thm(
  "DIVIDES_EXP_BASE",
  ``!a b n. prime a /\ 0 < n ==> (a divides b <=> a divides (b ** n))``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw[EXP] >>
  Cases_on `n = 0` >-
  rw[EXP] >>
  `0 < n` by decide_tac >>
  rw[EQ_IMP_THM] >-
  metis_tac[DIVIDES_MULT] >>
  `a divides b \/ a divides (b ** n)` by rw[P_EUCLIDES] >>
  metis_tac[]);

(* Theorem: n divides m ==> !k. n divides (k * m) *)
(* Proof:
   n divides m ==> ?q. m = q * n   by divides_def
   Hence k * m = k * (q * n)
               = (k * q) * n       by MULT_ASSOC
   or n divides (k * m)            by divides_def
*)
val DIVIDES_MULTIPLE = store_thm(
  "DIVIDES_MULTIPLE",
  ``!m n. n divides m ==> !k. n divides (k * m)``,
  metis_tac[divides_def, MULT_ASSOC]);

(* Theorem: k <> 0 ==> (m divides n <=> (k * m) divides (k * n)) *)
(* Proof:
       m divides n
   <=> ?q. n = q * m             by divides_def
   <=> ?q. k * n = k * (q * m)   by EQ_MULT_LCANCEL, k <> 0
   <=> ?q. k * n = q * (k * m)   by MULT_ASSOC, MULT_COMM
   <=> (k * m) divides (k * n)   by divides_def
*)
val DIVIDES_MULTIPLE_IFF = store_thm(
  "DIVIDES_MULTIPLE_IFF",
  ``!m n k. k <> 0 ==> (m divides n <=> (k * m) divides (k * n))``,
  rpt strip_tac >>
  `m divides n <=> ?q. n = q * m` by rw[GSYM divides_def] >>
  `_ = ?q. (k * n = k * (q * m))` by rw[EQ_MULT_LCANCEL] >>
  metis_tac[divides_def, MULT_COMM, MULT_ASSOC]);

(* Theorem: 0 < n /\ n divides m ==> m = n * (m DIV n) *)
(* Proof:
   n divides m <=> m MOD n = 0    by DIVIDES_MOD_0
   m = (m DIV n) * n + (m MOD n)  by DIVISION
     = (m DIV n) * n              by above
     = n * (m DIV n)              by MULT_COMM
*)
val DIVIDES_FACTORS = store_thm(
  "DIVIDES_FACTORS",
  ``!m n. 0 < n /\ n divides m ==> (m = n * (m DIV n))``,
  metis_tac[DIVISION, DIVIDES_MOD_0, ADD_0, MULT_COMM]);

(* Theorem: 0 < n /\ n divides m ==> (m DIV n) divides m *)
(* Proof:
   By DIVIDES_FACTORS: m = (m DIV n) * n
   Hence (m DIV n) | m    by divides_def
*)
val DIVIDES_COFACTOR = store_thm(
  "DIVIDES_COFACTOR",
  ``!m n. 0 < n /\ n divides m ==> (m DIV n) divides m``,
  metis_tac[DIVIDES_FACTORS, divides_def]);

(* Theorem: n divides q ==> p * (q DIV n) = (p * q) DIV n *)
(* Proof:
   n divides q ==> q MOD n = 0               by DIVIDES_MOD_0
   p * q = p * ((q DIV n) * n + q MOD n)     by DIVISION
         = p * ((q DIV n) * n)               by ADD_0
         = p * (q DIV n) * n                 by MULT_ASSOC
         = p * (q DIV n) * n + 0             by ADD_0
   Hence (p * q) DIV n = p * (q DIV n)       by DIV_UNIQUE, 0 < n:
   |- !n k q. (?r. (k = q * n + r) /\ r < n) ==> (k DIV n = q)
*)
val MULTIPLY_DIV = store_thm(
  "MULTIPLY_DIV",
  ``!n p q. 0 < n /\ n divides q ==> (p * (q DIV n) = (p * q) DIV n)``,
  rpt strip_tac >>
  `q MOD n = 0` by rw[GSYM DIVIDES_MOD_0] >>
  `p * q = p * ((q DIV n) * n)` by metis_tac[DIVISION, ADD_0] >>
  `_ = p * (q DIV n) * n + 0` by rw[MULT_ASSOC] >>
  metis_tac[DIV_UNIQUE]);

(* Note: The condition: n divides q is important:
> EVAL ``5 * (10 DIV 3)``;
val it = |- 5 * (10 DIV 3) = 15: thm
> EVAL ``(5 * 10) DIV 3``;
val it = |- 5 * 10 DIV 3 = 16: thm
*)

(* Theorem: 0 < n /\ m divides n ==> !x. (x MOD n) MOD m = x MOD m *)
(* Proof:
   Note 0 < m                                   by ZERO_DIVIDES, 0 < n
   Given divides m n ==> ?q. n = q * m          by divides_def
   Since x = (x DIV n) * n + (x MOD n)          by DIVISION
           = (x DIV n) * (q * m) + (x MOD n)    by above
           = ((x DIV n) * q) * m + (x MOD n)    by MULT_ASSOC
   Hence     x MOD m
           = ((x DIV n) * q) * m + (x MOD n)) MOD m                by above
           = (((x DIV n) * q * m) MOD m + (x MOD n) MOD m) MOD m   by MOD_PLUS
           = (0 + (x MOD n) MOD m) MOD m                           by MOD_EQ_0
           = (x MOD n) MOD m                                       by ADD, MOD_MOD
*)
val DIVIDES_MOD_MOD = store_thm(
  "DIVIDES_MOD_MOD",
  ``!m n. 0 < n /\ m divides n ==> !x. (x MOD n) MOD m = x MOD m``,
  rpt strip_tac >>
  `0 < m` by metis_tac[ZERO_DIVIDES, NOT_ZERO] >>
  `?q. n = q * m` by rw[GSYM divides_def] >>
  `x MOD m = ((x DIV n) * n + (x MOD n)) MOD m` by rw[GSYM DIVISION] >>
  `_ = (((x DIV n) * q) * m + (x MOD n)) MOD m` by rw[MULT_ASSOC] >>
  `_ = (((x DIV n) * q * m) MOD m + (x MOD n) MOD m) MOD m` by rw[MOD_PLUS] >>
  rw[MOD_EQ_0, MOD_MOD]);

(* Theorem: m divides n <=> (m * k) divides (n * k) *)
(* Proof: by divides_def and EQ_MULT_LCANCEL. *)
val DIVIDES_CANCEL = store_thm(
  "DIVIDES_CANCEL",
  ``!k. 0 < k ==> !m n. m divides n <=> (m * k) divides (n * k)``,
  rw[divides_def] >>
  `k <> 0` by decide_tac >>
  `!q. (q * m) * k = q * (m * k)` by rw_tac arith_ss[] >>
  metis_tac[EQ_MULT_LCANCEL, MULT_COMM]);

(* Theorem: m divides n ==> (k * m) divides (k * n) *)
(* Proof:
       m divides n
   ==> ?q. n = q * m              by divides_def
   So  k * n = k * (q * m)
             = (k * q) * m        by MULT_ASSOC
             = (q * k) * m        by MULT_COMM
             = q * (k * m)        by MULT_ASSOC
   Hence (k * m) divides (k * n)  by divides_def
*)
val DIVIDES_CANCEL_COMM = store_thm(
  "DIVIDES_CANCEL_COMM",
  ``!m n k. m divides n ==> (k * m) divides (k * n)``,
  metis_tac[MULT_ASSOC, MULT_COMM, divides_def]);

(* Theorem: 0 < n /\ 0 < m ==> !x. n divides x ==> ((m * x) DIV (m * n) = x DIV n) *)
(* Proof:
    n divides x ==> x = n * (x DIV n)              by DIVIDES_FACTORS
   or           m * x = (m * n) * (x DIV n)        by MULT_ASSOC
       n divides x
   ==> divides (m * n) (m * x)                     by DIVIDES_CANCEL_COMM
   ==> m * x = (m * n) * ((m * x) DIV (m * n))     by DIVIDES_FACTORS
   Equating expressions for m * x,
       (m * n) * (x DIV n) = (m * n) * ((m * x) DIV (m * n))
   or              x DIV n = (m * x) DIV (m * n)   by MULT_LEFT_CANCEL
*)
val DIV_COMMON_FACTOR = store_thm(
  "DIV_COMMON_FACTOR",
  ``!m n. 0 < n /\ 0 < m ==> !x. n divides x ==> ((m * x) DIV (m * n) = x DIV n)``,
  rpt strip_tac >>
  `!n. n <> 0 <=> 0 < n` by decide_tac >>
  `0 < m * n` by metis_tac[MULT_EQ_0] >>
  metis_tac[DIVIDES_CANCEL_COMM, DIVIDES_FACTORS, MULT_ASSOC, MULT_LEFT_CANCEL]);

(* Theorem: 0 < n /\ 0 < m /\ 0 < m DIV n /\
           n divides m /\ m divides x /\ (m DIV n) divides x ==>
           (x DIV (m DIV n) = n * (x DIV m)) *)
(* Proof:
     x DIV (m DIV n)
   = (n * x) DIV (n * (m DIV n))   by DIV_COMMON_FACTOR, (m DIV n) divides x, 0 < m DIV n.
   = (n * x) DIV m                 by DIVIDES_FACTORS, n divides m, 0 < n.
   = n * (x DIV m)                 by MULTIPLY_DIV, m divides x, 0 < m.
*)
val DIV_DIV_MULT = store_thm(
  "DIV_DIV_MULT",
  ``!m n x. 0 < n /\ 0 < m /\ 0 < m DIV n /\
           n divides m /\ m divides x /\ (m DIV n) divides x ==>
           (x DIV (m DIV n) = n * (x DIV m))``,
  metis_tac[DIV_COMMON_FACTOR, DIVIDES_FACTORS, MULTIPLY_DIV]);

(* ------------------------------------------------------------------------- *)
(* Basic Divisibility                                                        *)
(* ------------------------------------------------------------------------- *)

(* Overload on coprime for GCD equals 1 *)
val _ = overload_on ("coprime", ``\x y. gcd x y = 1``);

(* Idea: a little trick to make divisibility to mean equality. *)

(* Theorem: 0 < n /\ n < 2 * m ==> (m divides n <=> n = m) *)
(* Proof:
   If part: 0 < n /\ n < 2 * m /\ m divides n ==> n = m
      Note ?k. n = k * m           by divides_def
       Now k * m < 2 * m           by n < 2 * m
        so 0 < m /\ k < 2          by LT_MULT_LCANCEL
       and 0 < k                   by MULT
        so 1 <= k                  by LE_MULT_LCANCEL, 0 < m
      Thus k = 1, or n = m.
   Only-if part: true              by DIVIDES_REFL
*)
Theorem divides_iff_equal:
  !m n. 0 < n /\ n < 2 * m ==> (m divides n <=> n = m)
Proof
  rw[EQ_IMP_THM] >>
  `?k. n = k * m` by rw[GSYM divides_def] >>
  `0 < m /\ k < 2` by fs[LT_MULT_LCANCEL] >>
  `0 < k` by fs[] >>
  `k = 1` by decide_tac >>
  simp[]
QED

(* Theorem: 0 < m /\ n divides m ==> !t. m divides (t * n) <=> (m DIV n) divides t *)
(* Proof:
   Let k = m DIV n.
   Since m <> 0, n divides m ==> n <> 0       by ZERO_DIVIDES
    Thus m = k * n                            by DIVIDES_EQN, 0 < n
      so 0 < k                                by MULT, NOT_ZERO_LT_ZERO
   Hence k * n divides t * n <=> k divides t  by DIVIDES_CANCEL, 0 < k
*)
val dividend_divides_divisor_multiple = store_thm(
  "dividend_divides_divisor_multiple",
  ``!m n. 0 < m /\ n divides m ==> !t. m divides (t * n) <=> (m DIV n) divides t``,
  rpt strip_tac >>
  qabbrev_tac `k = m DIV n` >>
  `0 < n` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `m = k * n` by rw[GSYM DIVIDES_EQN, Abbr`k`] >>
  `0 < k` by metis_tac[MULT, NOT_ZERO_LT_ZERO] >>
  metis_tac[DIVIDES_CANCEL]);

(* Theorem: 0 < n /\ m divides n ==> 0 < m *)
(* Proof:
   Since 0 < n means n <> 0,
    then m divides n ==> m <> 0     by ZERO_DIVIDES
      or 0 < m                      by NOT_ZERO_LT_ZERO
*)
val divisor_pos = store_thm(
  "divisor_pos",
  ``!m n. 0 < n /\ m divides n ==> 0 < m``,
  metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < n /\ m divides n ==> 0 < m /\ m <= n *)
(* Proof:
   Since 0 < n /\ m divides n,
    then 0 < m           by divisor_pos
     and m <= n          by DIVIDES_LE
*)
val divides_pos = store_thm(
  "divides_pos",
  ``!m n. 0 < n /\ m divides n ==> 0 < m /\ m <= n``,
  metis_tac[divisor_pos, DIVIDES_LE]);

(* Theorem: 0 < n /\ m divides n ==> (n DIV (n DIV m) = m) *)
(* Proof:
   Since 0 < n /\ m divides n, 0 < m       by divisor_pos
   Hence n = (n DIV m) * m                 by DIVIDES_EQN, 0 < m
    Note 0 < n DIV m, otherwise contradicts 0 < n      by MULT
     Now n = m * (n DIV m)                 by MULT_COMM
           = m * (n DIV m) + 0             by ADD_0
   Therefore n DIV (n DIV m) = m           by DIV_UNIQUE
*)
val divide_by_cofactor = store_thm(
  "divide_by_cofactor",
  ``!m n. 0 < n /\ m divides n ==> (n DIV (n DIV m) = m)``,
  rpt strip_tac >>
  `0 < m` by metis_tac[divisor_pos] >>
  `n = (n DIV m) * m` by rw[GSYM DIVIDES_EQN] >>
  `0 < n DIV m` by metis_tac[MULT, NOT_ZERO_LT_ZERO] >>
  `n = m * (n DIV m) + 0` by metis_tac[MULT_COMM, ADD_0] >>
  metis_tac[DIV_UNIQUE]);

(* Theorem: 0 < n ==> !a b. a divides b ==> a divides b ** n *)
(* Proof:
   Since 0 < n, n = SUC m for some m.
    thus b ** n = b ** (SUC m)
                = b * b ** m    by EXP
   Now a divides b means
       ?k. b = k * a            by divides_def
    so b ** n
     = k * a * b ** m
     = (k * b ** m) * a         by MULT_COMM, MULT_ASSOC
   Hence a divides (b ** n)     by divides_def
*)
val divides_exp = store_thm(
  "divides_exp",
  ``!n. 0 < n ==> !a b. a divides b ==> a divides b ** n``,
  rw_tac std_ss[divides_def] >>
  `n <> 0` by decide_tac >>
  `?m. n = SUC m` by metis_tac[num_CASES] >>
  `(q * a) ** n = q * a * (q * a) ** m` by rw[EXP] >>
  `_ = q * (q * a) ** m * a` by rw[MULT_COMM, MULT_ASSOC] >>
  metis_tac[]);

(* Note; converse need prime divisor:
DIVIDES_EXP_BASE |- !a b n. prime a /\ 0 < n ==> (a divides b <=> a divides b ** n)
Counter-example for a general base: 12 divides 36 = 6^2, but ~(12 divides 6)
*)

(* Better than: DIVIDES_ADD_1 |- !a b c. a divides b /\ a divides c ==> a divides b + c *)

(* Theorem: c divides a /\ c divides b ==> !h k. c divides (h * a + k * b) *)
(* Proof:
   Since c divides a, ?u. a = u * c     by divides_def
     and c divides b, ?v. b = v * c     by divides_def
      h * a + k * b
    = h * (u * c) + k * (v * c)         by above
    = h * u * c + k * v * c             by MULT_ASSOC
    = (h * u + k * v) * c               by RIGHT_ADD_DISTRIB
   Hence c divides (h * a + k * b)      by divides_def
*)
val divides_linear = store_thm(
  "divides_linear",
  ``!a b c. c divides a /\ c divides b ==> !h k. c divides (h * a + k * b)``,
  rw_tac std_ss[divides_def] >>
  metis_tac[RIGHT_ADD_DISTRIB, MULT_ASSOC]);

(* Theorem: c divides a /\ c divides b ==> !h k d. (h * a = k * b + d) ==> c divides d *)
(* Proof:
   If c = 0,
      0 divides a ==> a = 0     by ZERO_DIVIDES
      0 divides b ==> b = 0     by ZERO_DIVIDES
      Thus d = 0                by arithmetic
      and 0 divides 0           by ZERO_DIVIDES
   If c <> 0, 0 < c.
      c divides a ==> (a MOD c = 0)  by DIVIDES_MOD_0
      c divides b ==> (b MOD c = 0)  by DIVIDES_MOD_0
      Hence 0 = (h * a) MOD c        by MOD_TIMES2, ZERO_MOD
              = (0 + d MOD c) MOD c  by MOD_PLUS, MOD_TIMES2, ZERO_MOD
              = d MOD c              by MOD_MOD
      or c divides d                 by DIVIDES_MOD_0
*)
val divides_linear_sub = store_thm(
  "divides_linear_sub",
  ``!a b c. c divides a /\ c divides b ==> !h k d. (h * a = k * b + d) ==> c divides d``,
  rpt strip_tac >>
  Cases_on `c = 0` >| [
    `(a = 0) /\ (b = 0)` by metis_tac[ZERO_DIVIDES] >>
    `d = 0` by rw_tac arith_ss[] >>
    rw[],
    `0 < c` by decide_tac >>
    `(a MOD c = 0) /\ (b MOD c = 0)` by rw[GSYM DIVIDES_MOD_0] >>
    `0 = (h * a) MOD c` by metis_tac[MOD_TIMES2, ZERO_MOD, MULT_0] >>
    `_ = (0 + d MOD c) MOD c` by metis_tac[MOD_PLUS, MOD_TIMES2, ZERO_MOD, MULT_0] >>
    `_ = d MOD c` by rw[MOD_MOD] >>
    rw[DIVIDES_MOD_0]
  ]);

(* Theorem: 1 < p ==> !m n. p ** m divides p ** n <=> m <= n *)
(* Proof:
   Note p <> 0 /\ p <> 1                      by 1 < p

   If-part: p ** m divides p ** n ==> m <= n
      By contradiction, suppose n < m.
      Let d = m - n, then d <> 0              by n < m
      Note p ** m = p ** n * p ** d           by EXP_BY_ADD_SUB_LT
       and p ** n <> 0                        by EXP_EQ_0, p <> 0
       Now ?q. p ** n = q * p ** m            by divides_def
                      = q * p ** d * p ** n   by MULT_ASSOC_COMM
      Thus 1 * p ** n = q * p ** d * p ** n   by MULT_LEFT_1
        or          1 = q * p ** d            by MULT_RIGHT_CANCEL
       ==>     p ** d = 1                     by MULT_EQ_1
        or          d = 0                     by EXP_EQ_1, p <> 1
      This contradicts d <> 0.

  Only-if part: m <= n ==> p ** m divides p ** n
      Note p ** n = p ** m * p ** (n - m)     by EXP_BY_ADD_SUB_LE
      Thus p ** m divides p ** n              by divides_def, MULT_COMM
*)
val power_divides_iff = store_thm(
  "power_divides_iff",
  ``!p. 1 < p ==> !m n. p ** m divides p ** n <=> m <= n``,
  rpt strip_tac >>
  `p <> 0 /\ p <> 1` by decide_tac >>
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `n < m /\ m - n <> 0` by decide_tac >>
    qabbrev_tac `d = m - n` >>
    `p ** m = p ** n * p ** d` by rw[EXP_BY_ADD_SUB_LT, Abbr`d`] >>
    `p ** n <> 0` by rw[EXP_EQ_0] >>
    `?q. p ** n = q * p ** m` by rw[GSYM divides_def] >>
    `_ = q * p ** d * p ** n` by metis_tac[MULT_ASSOC_COMM] >>
    `1 = q * p ** d` by metis_tac[MULT_RIGHT_CANCEL, MULT_LEFT_1] >>
    `p ** d = 1` by metis_tac[MULT_EQ_1] >>
    metis_tac[EXP_EQ_1],
    `p ** n = p ** m * p ** (n - m)` by rw[EXP_BY_ADD_SUB_LE] >>
    metis_tac[divides_def, MULT_COMM]
  ]);

(* Theorem: prime p ==> !m n. p ** m divides p ** n <=> m <= n *)
(* Proof: by power_divides_iff, ONE_LT_PRIME *)
val prime_power_divides_iff = store_thm(
  "prime_power_divides_iff",
  ``!p. prime p ==> !m n. p ** m divides p ** n <=> m <= n``,
  rw[power_divides_iff, ONE_LT_PRIME]);

(* Theorem: 0 < n /\ 1 < p ==> p divides p ** n *)
(* Proof:
   Note 0 < n <=> 1 <= n         by arithmetic
     so p ** 1 divides p ** n    by power_divides_iff
     or      p divides p ** n    by EXP_1
*)
val divides_self_power = store_thm(
  "divides_self_power",
  ``!n p. 0 < n /\ 1 < p ==> p divides p ** n``,
  metis_tac[power_divides_iff, EXP_1, DECIDE``0 < n <=> 1 <= n``]);

(* Theorem: a divides b /\ 0 < b /\ b < 2 * a ==> (b = a) *)
(* Proof:
   Note ?k. b = k * a      by divides_def
    and 0 < k              by MULT_EQ_0, 0 < b
    and k < 2              by LT_MULT_RCANCEL, k * a < 2 * a
   Thus k = 1              by 0 < k < 2
     or b = k * a = a      by arithmetic
*)
Theorem divides_eq_thm:
  !a b. a divides b /\ 0 < b /\ b < 2 * a ==> (b = a)
Proof
  rpt strip_tac >>
  `?k. b = k * a` by rw[GSYM divides_def] >>
  `0 < k` by metis_tac[MULT_EQ_0, NOT_ZERO] >>
  `k < 2` by metis_tac[LT_MULT_RCANCEL] >>
  `k = 1` by decide_tac >>
  simp[]
QED

(* Idea: factor equals cofactor iff the number is a square of the factor. *)

(* Theorem: 0 < m /\ m divides n ==> (m = n DIV m <=> n = m ** 2) *)
(* Proof:
        n
      = n DIV m * m + n MOD m    by DIVISION, 0 < m
      = n DIV m * m + 0          by DIVIDES_MOD_0, m divides n
      = n DIV m * m              by ADD_0
   If m = n DIV m,
     then n = m * m = m ** 2     by EXP_2
   If n = m ** 2,
     then n = m * m              by EXP_2
       so m = n DIV m            by EQ_MULT_RCANCEL
*)
Theorem factor_eq_cofactor:
  !m n. 0 < m /\ m divides n ==> (m = n DIV m <=> n = m ** 2)
Proof
  rw[EQ_IMP_THM] >>
  `n = n DIV m * m + n MOD m` by rw[DIVISION] >>
  `_ = m * m + 0` by metis_tac[DIVIDES_MOD_0] >>
  simp[]
QED

(* Theorem alias *)
Theorem euclid_prime = gcdTheory.P_EUCLIDES;
(* |- !p a b. prime p /\ p divides a * b ==> p divides a \/ p divides b *)

(* Theorem alias *)
Theorem euclid_coprime = gcdTheory.L_EUCLIDES;
(* |- !a b c. coprime a b /\ b divides a * c ==> b divides c *)

(* ------------------------------------------------------------------------- *)
(* Modulo Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < n ==> !a b. (a MOD n = b) <=> ?c. (a = c * n + b) /\ (b < n) *)
(* Proof:
   If part: (a MOD n = b) ==> ?c. (a = c * n + b) /\ (b < n)
      Or to show: ?c. (a = c * n + a MOD n) /\ a MOD n < n
      Taking c = a DIV n, this is true     by DIVISION
   Only-if part: (a = c * n + b) /\ (b < n) ==> (a MOD n = b)
      Or to show: b < n ==> (c * n + b) MOD n = b
        (c * n + b) MOD n
      = ((c * n) MOD n + b MOD n) MOD n    by MOD_PLUS
      = (0 + b MOD n) MOD n                by MOD_EQ_0
      = b MOD n                            by MOD_MOD
      = b                                  by LESS_MOD, b < n
*)
val MOD_EQN = store_thm(
  "MOD_EQN",
  ``!n. 0 < n ==> !a b. (a MOD n = b) <=> ?c. (a = c * n + b) /\ (b < n)``,
  rw_tac std_ss[EQ_IMP_THM] >-
  metis_tac[DIVISION] >>
  metis_tac[MOD_PLUS, MOD_EQ_0, ADD, MOD_MOD, LESS_MOD]);

(* Idea: eliminate modulus n when a MOD n = b MOD n. *)

(* Theorem: 0 < n /\ b <= a ==> (a MOD n = b MOD n <=> ?c. a = b + c * n) *)
(* Proof:
   If part: a MOD n = b MOD n ==> ?c. a = b + c * n
      Note ?c. a = c * n + b MOD n       by MOD_EQN
       and b = (b DIV n) * n + b MOD n   by DIVISION
      Let q = b DIV n,
      Then q * n <= c * n                by LE_ADD_RCANCEL, b <= a
           a
         = c * n + (b - q * n)           by above
         = b + (c * n - q * n)           by arithmetic, q * n <= c * n
         = b + (c - q) * n               by RIGHT_SUB_DISTRIB
      Take (c - q) as c.
   Only-if part: (b + c * n) MOD n = b MOD n
      This is true                       by MOD_TIMES
*)
Theorem MOD_MOD_EQN:
  !n a b. 0 < n /\ b <= a ==> (a MOD n = b MOD n <=> ?c. a = b + c * n)
Proof
  rw[EQ_IMP_THM] >| [
    `?c. a = c * n + b MOD n` by metis_tac[MOD_EQN] >>
    `b = (b DIV n) * n + b MOD n` by rw[DIVISION] >>
    qabbrev_tac `q = b DIV n` >>
    `q * n <= c * n` by metis_tac[LE_ADD_RCANCEL] >>
    `a = b + (c * n - q * n)` by decide_tac >>
    `_ = b + (c - q) * n` by decide_tac >>
    metis_tac[],
    simp[]
  ]
QED

(* Idea: a convenient form of MOD_PLUS. *)

(* Theorem: 0 < n ==> (x + y) MOD n = (x + y MOD n) MOD n *)
(* Proof:
   Let q = y DIV n, r = y MOD n.
   Then y = q * n + r              by DIVISION, 0 < n
        (x + y) MOD n
      = (x + (q * n + r)) MOD n    by above
      = (q * n + (x + r)) MOD n    by arithmetic
      = (x + r) MOD n              by MOD_PLUS, MOD_EQ_0
*)
Theorem MOD_PLUS2:
  !n x y. 0 < n ==> (x + y) MOD n = (x + y MOD n) MOD n
Proof
  rpt strip_tac >>
  `y = (y DIV n) * n + y MOD n` by metis_tac[DIVISION] >>
  simp[]
QED

(* Theorem: (x + y + z) MOD n = (x MOD n + y MOD n + z MOD n) MOD n *)
(* Proof:
     (x + y + z) MOD n
   = ((x + y) MOD n + z MOD n) MOD n               by MOD_PLUS
   = ((x MOD n + y MOD n) MOD n + z MOD n) MOD n   by MOD_PLUS
   = (x MOD n + y MOD n + z MOD n) MOD n           by MOD_MOD
*)
val MOD_PLUS3 = store_thm(
  "MOD_PLUS3",
  ``!n. 0 < n ==> !x y z. (x + y + z) MOD n = (x MOD n + y MOD n + z MOD n) MOD n``,
  metis_tac[MOD_PLUS, MOD_MOD]);

(* Theorem: Addition is associative in MOD: if x, y, z all < n,
            ((x + y) MOD n + z) MOD n = (x + (y + z) MOD n) MOD n. *)
(* Proof:
     ((x * y) MOD n * z) MOD n
   = (((x * y) MOD n) MOD n * z MOD n) MOD n     by MOD_TIMES2
   = ((x * y) MOD n * z MOD n) MOD n             by MOD_MOD
   = (x * y * z) MOD n                           by MOD_TIMES2
   = (x * (y * z)) MOD n                         by MULT_ASSOC
   = (x MOD n * (y * z) MOD n) MOD n             by MOD_TIMES2
   = (x MOD n * ((y * z) MOD n) MOD n) MOD n     by MOD_MOD
   = (x * (y * z) MOD n) MOD n                   by MOD_TIMES2
   or
     ((x + y) MOD n + z) MOD n
   = ((x + y) MOD n + z MOD n) MOD n     by LESS_MOD, z < n
   = (x + y + z) MOD n                   by MOD_PLUS
   = (x + (y + z)) MOD n                 by ADD_ASSOC
   = (x MOD n + (y + z) MOD n) MOD n     by MOD_PLUS
   = (x + (y + z) MOD n) MOD n           by LESS_MOD, x < n
*)
val MOD_ADD_ASSOC = store_thm(
  "MOD_ADD_ASSOC",
  ``!n x y z. 0 < n /\ x < n /\ y < n /\ z < n ==> (((x + y) MOD n + z) MOD n = (x + (y + z) MOD n) MOD n)``,
  metis_tac[LESS_MOD, MOD_PLUS, ADD_ASSOC]);

(* Theorem: mutliplication is associative in MOD:
            (x*y MOD n * z) MOD n = (x * y*Z MOD n) MOD n  *)
(* Proof:
     ((x * y) MOD n * z) MOD n
   = (((x * y) MOD n) MOD n * z MOD n) MOD n     by MOD_TIMES2
   = ((x * y) MOD n * z MOD n) MOD n             by MOD_MOD
   = (x * y * z) MOD n                           by MOD_TIMES2
   = (x * (y * z)) MOD n                         by MULT_ASSOC
   = (x MOD n * (y * z) MOD n) MOD n             by MOD_TIMES2
   = (x MOD n * ((y * z) MOD n) MOD n) MOD n     by MOD_MOD
   = (x * (y * z) MOD n) MOD n                   by MOD_TIMES2
   or
     ((x * y) MOD n * z) MOD n
   = ((x * y) MOD n * z MOD n) MOD n    by LESS_MOD, z < n
   = (((x * y) * z) MOD n) MOD n        by MOD_TIMES2
   = ((x * (y * z)) MOD n) MOD n        by MULT_ASSOC
   = (x MOD n * (y * z) MOD n) MOD n    by MOD_TIMES2
   = (x * (y * z) MOD n) MOD n          by LESS_MOD, x < n
*)
val MOD_MULT_ASSOC = store_thm(
  "MOD_MULT_ASSOC",
  ``!n x y z. 0 < n /\ x < n /\ y < n /\ z < n ==> (((x * y) MOD n * z) MOD n = (x * (y * z) MOD n) MOD n)``,
  metis_tac[LESS_MOD, MOD_TIMES2, MULT_ASSOC]);

(* Theorem: If n > 0, ((n - x) MOD n + x) MOD n = 0  for x < n. *)
(* Proof:
     ((n - x) MOD n + x) MOD n
   = ((n - x) MOD n + x MOD n) MOD n    by LESS_MOD
   = (n - x + x) MOD n                  by MOD_PLUS
   = n MOD n                            by SUB_ADD and 0 <= n
   = (1*n) MOD n                        by MULT_LEFT_1
   = 0                                  by MOD_EQ_0
*)
val MOD_ADD_INV = store_thm(
  "MOD_ADD_INV",
  ``!n x. 0 < n /\ x < n ==> (((n - x) MOD n + x) MOD n = 0)``,
  metis_tac[LESS_MOD, MOD_PLUS, SUB_ADD, LESS_IMP_LESS_OR_EQ, MOD_EQ_0, MULT_LEFT_1]);

(* Theorem: If n > 0, k MOD n = 0 ==> !x. (k*x) MOD n = 0 *)
(* Proof:
   (k*x) MOD n = (k MOD n * x MOD n) MOD n    by MOD_TIMES2
               = (0 * x MOD n) MOD n          by given
               = 0 MOD n                      by MULT_0 and MULT_COMM
               = 0                            by ZERO_MOD
*)
val MOD_MULITPLE_ZERO = store_thm(
  "MOD_MULITPLE_ZERO",
  ``!n k. 0 < n /\ (k MOD n = 0) ==> !x. ((k*x) MOD n = 0)``,
  metis_tac[MOD_TIMES2, MULT_0, MULT_COMM, ZERO_MOD]);

(* Theorem: If n > 0, a MOD n = b MOD n ==> (a - b) MOD n = 0 *)
(* Proof:
   a = (a DIV n)*n + (a MOD n)   by DIVISION
   b = (b DIV n)*n + (b MOD n)   by DIVISION
   Hence  a - b = ((a DIV n) - (b DIV n))* n
                = a multiple of n
   Therefore (a - b) MOD n = 0.
*)
val MOD_EQ_DIFF = store_thm(
  "MOD_EQ_DIFF",
  ``!n a b. 0 < n /\ (a MOD n = b MOD n) ==> ((a - b) MOD n = 0)``,
  rpt strip_tac >>
  `a = a DIV n * n + a MOD n` by metis_tac[DIVISION] >>
  `b = b DIV n * n + b MOD n` by metis_tac[DIVISION] >>
  `a - b = (a DIV n - b DIV n) * n` by rw_tac arith_ss[] >>
  metis_tac[MOD_EQ_0]);
(* Note: The reverse is true only when a >= b:
         (a-b) MOD n = 0 cannot imply a MOD n = b MOD n *)

(* Theorem: if n > 0, a >= b, then (a - b) MOD n = 0 <=> a MOD n = b MOD n *)
(* Proof:
         (a-b) MOD n = 0
   ==>   n divides (a-b)   by MOD_0_DIVIDES
   ==>   (a-b) = k*n       for some k by divides_def
   ==>       a = b + k*n   need b <= a to apply arithmeticTheory.SUB_ADD
   ==> a MOD n = b MOD n   by arithmeticTheory.MOD_TIMES

   The converse is given by MOD_EQ_DIFF.
*)
val MOD_EQ = store_thm(
  "MOD_EQ",
  ``!n a b. 0 < n /\ b <= a ==> (((a - b) MOD n = 0) <=> (a MOD n = b MOD n))``,
  rw[EQ_IMP_THM] >| [
    `?k. a - b = k * n` by metis_tac[DIVIDES_MOD_0, divides_def] >>
    `a = k*n + b` by rw_tac arith_ss[] >>
    metis_tac[MOD_TIMES],
    metis_tac[MOD_EQ_DIFF]
  ]);
(* Both MOD_EQ_DIFF and MOD_EQ are required in MOD_MULT_LCANCEL *)

(* Theorem: n < m ==> ((n MOD m = 0) <=> (n = 0)) *)
(* Proof:
   Note n < m ==> (n MOD m = n)    by LESS_MOD
   Thus (n MOD m = 0) <=> (n = 0)  by above
*)
val MOD_EQ_0_IFF = store_thm(
  "MOD_EQ_0_IFF",
  ``!m n. n < m ==> ((n MOD m = 0) <=> (n = 0))``,
  rw_tac bool_ss[LESS_MOD]);

(* Theorem: ((a MOD n) ** m) MOD n = (a ** m) MOD n  *)
(* Proof: by induction on m.
   Base case: (a MOD n) ** 0 MOD n = a ** 0 MOD n
       (a MOD n) ** 0 MOD n
     = 1 MOD n              by EXP
     = a ** 0 MOD n         by EXP
   Step case: (a MOD n) ** m MOD n = a ** m MOD n ==> (a MOD n) ** SUC m MOD n = a ** SUC m MOD n
       (a MOD n) ** SUC m MOD n
     = ((a MOD n) * (a MOD n) ** m) MOD n             by EXP
     = ((a MOD n) * (((a MOD n) ** m) MOD n)) MOD n   by MOD_TIMES2, MOD_MOD
     = ((a MOD n) * (a ** m MOD n)) MOD n             by induction hypothesis
     = (a * a ** m) MOD n                             by MOD_TIMES2
     = a ** SUC m MOD n                               by EXP
*)
val MOD_EXP = store_thm(
  "MOD_EXP",
  ``!n. 0 < n ==> !a m. ((a MOD n) ** m) MOD n = (a ** m) MOD n``,
  rpt strip_tac >>
  Induct_on `m` >-
  rw[EXP] >>
  `(a MOD n) ** SUC m MOD n = ((a MOD n) * (a MOD n) ** m) MOD n` by rw[EXP] >>
  `_ = ((a MOD n) * (((a MOD n) ** m) MOD n)) MOD n` by metis_tac[MOD_TIMES2, MOD_MOD] >>
  `_ = ((a MOD n) * (a ** m MOD n)) MOD n` by rw[] >>
  `_ = (a * a ** m) MOD n` by rw[MOD_TIMES2] >>
  rw[EXP]);


(* Idea: equality exchange for MOD without negative. *)

(* Theorem: b < n /\ c < n ==>
              ((a + b) MOD n = (c + d) MOD n <=>
               (a + (n - c)) MOD n = (d + (n - b)) MOD n) *)
(* Proof:
   Note 0 < n                  by b < n or c < n
   Let x = n - b, y = n - c.
   The goal is: (a + b) MOD n = (c + d) MOD n <=>
                (a + y) MOD n = (d + x) MOD n
   Note n = b + x, n = c + y   by arithmetic
       (a + b) MOD n = (c + d) MOD n
   <=> (a + b + x + y) MOD n = (c + d + x + y) MOD n   by ADD_MOD
   <=> (a + y + n) MOD n = (d + x + n) MOD n           by above
   <=> (a + y) MOD n = (d + x) MOD n                   by ADD_MOD

   For integers, this is simply: a + b = c + d <=> a - c = b - d.
*)
Theorem mod_add_eq_sub:
  !n a b c d. b < n /\ c < n ==>
              ((a + b) MOD n = (c + d) MOD n <=>
               (a + (n - c)) MOD n = (d + (n - b)) MOD n)
Proof
  rpt strip_tac >>
  `0 < n` by decide_tac >>
  `n = b + (n - b)` by decide_tac >>
  `n = c + (n - c)` by decide_tac >>
  qabbrev_tac `x = n - b` >>
  qabbrev_tac `y = n - c` >>
  `a + b + x + y = a + y + n` by decide_tac >>
  `c + d + x + y = d + x + n` by decide_tac >>
  `(a + b) MOD n = (c + d) MOD n <=>
    (a + b + x + y) MOD n = (c + d + x + y) MOD n` by simp[ADD_MOD] >>
  fs[ADD_MOD]
QED

(* Idea: generalise above equality exchange for MOD. *)

(* Theorem: 0 < n ==>
            ((a + b) MOD n = (c + d) MOD n <=>
             (a + (n - c MOD n)) MOD n = (d + (n - b MOD n)) MOD n) *)
(* Proof:
   Let b' = b MOD n, c' = c MOD n.
   Note b' < n            by MOD_LESS, 0 < n
    and c' < n            by MOD_LESS, 0 < n
        (a + b) MOD n = (c + d) MOD n
    <=> (a + b') MOD n = (d + c') MOD n              by MOD_PLUS2
    <=> (a + (n - c')) MOD n = (d + (n - b')) MOD n  by mod_add_eq_sub
*)
Theorem mod_add_eq_sub_eq:
  !n a b c d. 0 < n ==>
              ((a + b) MOD n = (c + d) MOD n <=>
               (a + (n - c MOD n)) MOD n = (d + (n - b MOD n)) MOD n)
Proof
  rpt strip_tac >>
  `b MOD n < n /\ c MOD n < n` by rw[] >>
  `(a + b) MOD n = (a + b MOD n) MOD n` by simp[Once MOD_PLUS2] >>
  `(c + d) MOD n = (d + c MOD n) MOD n` by simp[Once MOD_PLUS2] >>
  prove_tac[mod_add_eq_sub]
QED

(*
MOD_EQN is a trick to eliminate MOD:
|- !n. 0 < n ==> !a b. a MOD n = b <=> ?c. a = c * n + b /\ b < n
*)

(* Idea: remove MOD for divides: need b divides (a MOD n) ==> b divides a. *)

(* Theorem: 0 < n /\ b divides n /\ b divides (a MOD n) ==> b divides a *)
(* Proof:
   Note ?k. n = k * b                    by divides_def, b divides n
    and ?h. a MOD n = h * b              by divides_def, b divides (a MOD n)
    and ?c. a = c * n + h * b            by MOD_EQN, 0 < n
              = c * (k * b) + h * b      by above
              = (c * k + h) * b          by RIGHT_ADD_DISTRIB
   Thus b divides a                      by divides_def
*)
Theorem mod_divides:
  !n a b. 0 < n /\ b divides n /\ b divides (a MOD n) ==> b divides a
Proof
  rpt strip_tac >>
  `?k. n = k * b` by rw[GSYM divides_def] >>
  `?h. a MOD n = h * b` by rw[GSYM divides_def] >>
  `?c. a = c * n + h * b` by metis_tac[MOD_EQN] >>
  `_ = (c * k + h) * b` by simp[] >>
  metis_tac[divides_def]
QED

(* Idea: include converse of mod_divides. *)

(* Theorem: 0 < n /\ b divides n ==> (b divides (a MOD n) <=> b divides a) *)
(* Proof:
   If part: b divides n /\ b divides a MOD n ==> b divides a
      This is true                       by mod_divides
   Only-if part: b divides n /\ b divides a ==> b divides a MOD n
   Note ?c. a = c * n + a MOD n          by MOD_EQN, 0 < n
              = c * n + 1 * a MOD n      by MULT_LEFT_1
   Thus b divides (a MOD n)              by divides_linear_sub
*)
Theorem mod_divides_iff:
  !n a b. 0 < n /\ b divides n ==> (b divides (a MOD n) <=> b divides a)
Proof
  rw[EQ_IMP_THM] >-
  metis_tac[mod_divides] >>
  `?c. a = c * n + a MOD n` by metis_tac[MOD_EQN] >>
  metis_tac[divides_linear_sub, MULT_LEFT_1]
QED

(* An application of
DIVIDES_MOD_MOD:
|- !m n. 0 < n /\ m divides n ==> !x. x MOD n MOD m = x MOD m
Let x = a linear combination.
(linear) MOD n MOD m = linear MOD m
change n to a product m * n, for z = linear MOD (m * n).
(linear) MOD (m * n) MOD g = linear MOD g
z MOD g = linear MOD g
requires: g divides (m * n)
*)

(* Idea: generalise for MOD equation: a MOD n = b. Need c divides a ==> c divides b. *)

(* Theorem: 0 < n /\ a MOD n = b /\ c divides n /\ c divides a ==> c divides b *)
(* Proof:
   Note 0 < c                      by ZERO_DIVIDES, c divides n, 0 < n.
       a MOD n = b
   ==> (a MOD n) MOD c = b MOD c
   ==>         a MOD c = b MOD c   by DIVIDES_MOD_MOD, 0 < n, c divides n
   But a MOD c = 0                 by DIVIDES_MOD_0, c divides a
    so b MOD c = 0, or c divides b by DIVIDES_MOD_0, 0 < c
*)
Theorem mod_divides_divides:
  !n a b c. 0 < n /\ a MOD n = b /\ c divides n /\ c divides a ==> c divides b
Proof
  simp[mod_divides_iff]
QED

(* Idea: include converse of mod_divides_divides. *)

(* Theorem: 0 < n /\ a MOD n = b /\ c divides n ==> (c divides a <=> c divides b) *)
(* Proof:
   If part: c divides a ==> c divides b, true  by mod_divides_divides
   Only-if part: c divides b ==> c divides a
      Note b = a MOD n, so this is true        by mod_divides
*)
Theorem mod_divides_divides_iff:
  !n a b c. 0 < n /\ a MOD n = b /\ c divides n ==> (c divides a <=> c divides b)
Proof
  simp[mod_divides_iff]
QED

(* Idea: divides across MOD: from a MOD n = b MOD n to c divides a ==> c divides b. *)

(* Theorem: 0 < n /\ a MOD n = b MOD n /\ c divides n /\ c divides a ==> c divides b *)
(* Proof:
   Note c divides (b MOD n)        by mod_divides_divides
     so c divides b                by mod_divides
   Or, simply have both            by mod_divides_iff
*)
Theorem mod_eq_divides:
  !n a b c. 0 < n /\ a MOD n = b MOD n /\ c divides n /\ c divides a ==> c divides b
Proof
  metis_tac[mod_divides_iff]
QED

(* Idea: include converse of mod_eq_divides. *)

(* Theorem: 0 < n /\ a MOD n = b MOD n /\ c divides n ==> (c divides a <=> c divides b) *)
(* Proof:
   If part: c divides a ==> c divides b, true  by mod_eq_divides, a MOD n = b MOD n
   Only-if: c divides b ==> c divides a, true  by mod_eq_divides, b MOD n = a MOD n
*)
Theorem mod_eq_divides_iff:
  !n a b c. 0 < n /\ a MOD n = b MOD n /\ c divides n ==> (c divides a <=> c divides b)
Proof
  metis_tac[mod_eq_divides]
QED

(* Idea: special cross-multiply equality of MOD (m * n) implies pair equality:
         from (m * a) MOD (m * n) = (n * b) MOD (m * n) to a = n /\ b = m. *)

(* Theorem: coprime m n /\ 0 < a /\ a < 2 * n /\ 0 < b /\ b < 2 * m /\
            (m * a) MOD (m * n) = (n * b) MOD (m * n) ==> (a = n /\ b = m) *)
(* Proof:
   Given (m * a) MOD (m * n) = (n * b) MOD (m * n)
   Note n divides (n * b)      by factor_divides
    and n divides (m * n)      by factor_divides
     so n divides (m * a)      by mod_eq_divides
    ==> n divides a            by euclid_coprime, MULT_COMM
   Thus a = n                  by divides_iff_equal
   Also m divides (m * a)      by factor_divides
    and m divides (m * n)      by factor_divides
     so m divides (n * b)      by mod_eq_divides
    ==> m divides b            by euclid_coprime, GCD_SYM
   Thus b = m                  by divides_iff_equal
*)
Theorem mod_mult_eq_mult:
  !m n a b. coprime m n /\ 0 < a /\ a < 2 * n /\ 0 < b /\ b < 2 * m /\
            (m * a) MOD (m * n) = (n * b) MOD (m * n) ==> (a = n /\ b = m)
Proof
  ntac 5 strip_tac >>
  `0 < m /\ 0 < n` by decide_tac >>
  `0 < m * n` by rw[] >>
  strip_tac >| [
    `n divides (n * b)` by rw[DIVIDES_MULTIPLE] >>
    `n divides (m * n)` by rw[DIVIDES_MULTIPLE] >>
    `n divides (m * a)` by metis_tac[mod_eq_divides] >>
    `n divides a` by metis_tac[euclid_coprime, MULT_COMM] >>
    metis_tac[divides_iff_equal],
    `m divides (m * a)` by rw[DIVIDES_MULTIPLE] >>
    `m divides (m * n)` by metis_tac[DIVIDES_REFL, DIVIDES_MULTIPLE, MULT_COMM] >>
    `m divides (n * b)` by metis_tac[mod_eq_divides] >>
    `m divides b` by metis_tac[euclid_coprime, GCD_SYM] >>
    metis_tac[divides_iff_equal]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* Even and Odd Parity.                                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < n /\ EVEN m ==> EVEN (m ** n) *)
(* Proof:
   Since EVEN m, m MOD 2 = 0       by EVEN_MOD2
       EVEN (m ** n)
   <=> (m ** n) MOD 2 = 0          by EVEN_MOD2
   <=> (m MOD 2) ** n MOD 2 = 0    by EXP_MOD, 0 < 2
   ==> 0 ** n MOD 2 = 0            by above
   <=> 0 MOD 2 = 0                 by ZERO_EXP, n <> 0
   <=> 0 = 0                       by ZERO_MOD
   <=> T
*)
(* Note: arithmeticTheory.EVEN_EXP  |- !m n. 0 < n /\ EVEN m ==> EVEN (m ** n) *)

(* Theorem: !m n. 0 < n /\ ODD m ==> ODD (m ** n) *)
(* Proof:
   Since ODD m, m MOD 2 = 1        by ODD_MOD2
       ODD (m ** n)
   <=> (m ** n) MOD 2 = 1          by ODD_MOD2
   <=> (m MOD 2) ** n MOD 2 = 1    by EXP_MOD, 0 < 2
   ==> 1 ** n MOD 2 = 1            by above
   <=> 1 MOD 2 = 1                 by EXP_1, n <> 0
   <=> 1 = 1                       by ONE_MOD, 1 < 2
   <=> T
*)
val ODD_EXP = store_thm(
  "ODD_EXP",
  ``!m n. 0 < n /\ ODD m ==> ODD (m ** n)``,
  rw[ODD_MOD2] >>
  `n <> 0 /\ 0 < 2` by decide_tac >>
  metis_tac[EXP_MOD, EXP_1, ONE_MOD]);

(* Theorem: 0 < n ==> !m. (EVEN m <=> EVEN (m ** n)) /\ (ODD m <=> ODD (m ** n)) *)
(* Proof:
   First goal: EVEN m <=> EVEN (m ** n)
     If part: EVEN m ==> EVEN (m ** n), true by EVEN_EXP
     Only-if part: EVEN (m ** n) ==> EVEN m.
        By contradiction, suppose ~EVEN m.
        Then ODD m                           by EVEN_ODD
         and ODD (m ** n)                    by ODD_EXP
          or ~EVEN (m ** n)                  by EVEN_ODD
        This contradicts EVEN (m ** n).
   Second goal: ODD m <=> ODD (m ** n)
     Just mirror the reasoning of first goal.
*)
val power_parity = store_thm(
  "power_parity",
  ``!n. 0 < n ==> !m. (EVEN m <=> EVEN (m ** n)) /\ (ODD m <=> ODD (m ** n))``,
  metis_tac[EVEN_EXP, ODD_EXP, ODD_EVEN]);

(* Theorem: 0 < n ==> EVEN (2 ** n) *)
(* Proof:
       EVEN (2 ** n)
   <=> (2 ** n) MOD 2 = 0          by EVEN_MOD2
   <=> (2 MOD 2) ** n MOD 2 = 0    by EXP_MOD
   <=> 0 ** n MOD 2 = 0            by DIVMOD_ID, 0 < 2
   <=> 0 MOD 2 = 0                 by ZERO_EXP, n <> 0
   <=> 0 = 0                       by ZERO_MOD
   <=> T
*)
Theorem EXP_2_EVEN:  !n. 0 < n ==> EVEN (2 ** n)
Proof rw[EVEN_MOD2, ZERO_EXP]
QED
(* Michael's proof by induction
val EXP_2_EVEN = store_thm(
  "EXP_2_EVEN",
  ``!n. 0 < n ==> EVEN (2 ** n)``,
  Induct >> rw[EXP, EVEN_DOUBLE]);
 *)

(* Theorem: 0 < n ==> ODD (2 ** n - 1) *)
(* Proof:
   Since 0 < 2 ** n                  by EXP_POS, 0 < 2
      so 1 <= 2 ** n                 by LESS_EQ
    thus SUC (2 ** n - 1)
       = 2 ** n - 1 + 1              by ADD1
       = 2 ** n                      by SUB_ADD, 1 <= 2 ** n
     and EVEN (2 ** n)               by EXP_2_EVEN
   Hence ODD (2 ** n - 1)            by EVEN_ODD_SUC
*)
val EXP_2_PRE_ODD = store_thm(
  "EXP_2_PRE_ODD",
  ``!n. 0 < n ==> ODD (2 ** n - 1)``,
  rpt strip_tac >>
  `0 < 2 ** n` by rw[EXP_POS] >>
  `SUC (2 ** n - 1) = 2 ** n` by decide_tac >>
  metis_tac[EXP_2_EVEN, EVEN_ODD_SUC]);

(* ------------------------------------------------------------------------- *)
(* Modulo Inverse                                                            *)
(* ------------------------------------------------------------------------- *)

(*
> LINEAR_GCD |> SPEC ``j:num`` |> SPEC ``k:num``;
val it = |- j <> 0 ==> ?p q. p * j = q * k + gcd k j: thm
*)

(* Theorem: 0 < j ==> ?p q. p * j = q * k + gcd j k *)
(* Proof: by LINEAR_GCD, GCD_SYM *)
val GCD_LINEAR = store_thm(
  "GCD_LINEAR",
  ``!j k. 0 < j ==> ?p q. p * j = q * k + gcd j k``,
  metis_tac[LINEAR_GCD, GCD_SYM, NOT_ZERO]);

(* Theorem: [Euclid's Lemma] A prime a divides product iff the prime a divides factor.
            [in MOD notation] For prime p, x*y MOD p = 0 <=> x MOD p = 0 or y MOD p = 0 *)
(* Proof:
   The if part is already in P_EUCLIDES:
   !p a b. prime p /\ divides p (a * b) ==> p divides a \/ p divides b
   Convert the divides to MOD by DIVIDES_MOD_0.
   The only-if part is:
   (1) divides p x ==> divides p (x * y)
   (2) divides p y ==> divides p (x * y)
   Both are true by DIVIDES_MULT: !a b c. a divides b ==> a divides (b * c).
   The symmetry of x and y can be taken care of by MULT_COMM.
*)
val EUCLID_LEMMA = store_thm(
  "EUCLID_LEMMA",
  ``!p x y. prime p ==> (((x * y) MOD p = 0) <=> (x MOD p = 0) \/ (y MOD p = 0))``,
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  rw[GSYM DIVIDES_MOD_0, EQ_IMP_THM] >>
  metis_tac[P_EUCLIDES, DIVIDES_MULT, MULT_COMM]);

(* Theorem: [Cancellation Law for MOD p]
   For prime p, if x MOD p <> 0,
      (x*y) MOD p = (x*z) MOD p ==> y MOD p = z MOD p *)
(* Proof:
       (x*y) MOD p = (x*z) MOD p
   ==> ((x*y) - (x*z)) MOD p = 0   by MOD_EQ_DIFF
   ==>       (x*(y-z)) MOD p = 0   by arithmetic LEFT_SUB_DISTRIB
   ==>           (y-z) MOD p = 0   by EUCLID_LEMMA, x MOD p <> 0
   ==>               y MOD p = z MOD p    if z <= y

   Since this theorem is symmetric in y, z,
   First prove the theorem assuming z <= y,
   then use the same proof for y <= z.
*)
Theorem MOD_MULT_LCANCEL:
  !p x y z. prime p /\ (x * y) MOD p = (x * z) MOD p /\ x MOD p <> 0 ==> y MOD p = z MOD p
Proof
  rpt strip_tac >>
  `!a b c. c <= b /\ (a * b) MOD p = (a * c) MOD p /\ a MOD p <> 0 ==> b MOD p = c MOD p` by
  (rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  `(a * b - a * c) MOD p = 0` by rw[MOD_EQ_DIFF] >>
  `(a * (b - c)) MOD p = 0` by rw[LEFT_SUB_DISTRIB] >>
  metis_tac[EUCLID_LEMMA, MOD_EQ]) >>
  Cases_on `z <= y` >-
  metis_tac[] >>
  `y <= z` by decide_tac >>
  metis_tac[]
QED

(* Theorem: prime p /\ (y * x) MOD p = (z * x) MOD p /\ x MOD p <> 0 ==>
            y MOD p = z MOD p *)
(* Proof: by MOD_MULT_LCANCEL, MULT_COMM *)
Theorem MOD_MULT_RCANCEL:
  !p x y z. prime p /\ (y * x) MOD p = (z * x) MOD p /\ x MOD p <> 0 ==>
            y MOD p = z MOD p
Proof
  metis_tac[MOD_MULT_LCANCEL, MULT_COMM]
QED

(* Theorem: For prime p, 0 < x < p ==> ?y. 0 < y /\ y < p /\ (y*x) MOD p = 1 *)
(* Proof:
       0 < x < p
   ==> ~ divides p x                    by NOT_LT_DIVIDES
   ==> gcd p x = 1                      by gcdTheory.PRIME_GCD
   ==> ?k q. k * x = q * p + 1          by gcdTheory.LINEAR_GCD
   ==> k*x MOD p = (q*p + 1) MOD p      by arithmetic
   ==> k*x MOD p = 1                    by MOD_MULT, 1 < p.
   ==> (k MOD p)*(x MOD p) MOD p = 1    by MOD_TIMES2
   ==> ((k MOD p) * x) MOD p = 1        by LESS_MOD, x < p.
   Now   k MOD p < p                    by MOD_LESS
   and   0 < k MOD p since (k*x) MOD p <> 0  (by 1 <> 0)
                       and x MOD p <> 0      (by ~ divides p x)
                                        by EUCLID_LEMMA
   Hence take y = k MOD p, then 0 < y < p.
*)
val MOD_MULT_INV_EXISTS = store_thm(
  "MOD_MULT_INV_EXISTS",
  ``!p x. prime p /\ 0 < x /\ x < p ==> ?y. 0 < y /\ y < p /\ ((y * x) MOD p = 1)``,
  rpt strip_tac >>
  `0 < p /\ 1 < p` by metis_tac[PRIME_POS, ONE_LT_PRIME] >>
  `gcd p x = 1` by metis_tac[PRIME_GCD, NOT_LT_DIVIDES] >>
  `?k q. k * x = q * p + 1` by metis_tac[LINEAR_GCD, NOT_ZERO_LT_ZERO] >>
  `1 = (k * x) MOD p` by metis_tac[MOD_MULT] >>
  `_ = ((k MOD p) * (x MOD p)) MOD p` by metis_tac[MOD_TIMES2] >>
  `0 < k MOD p` by
  (`1 <> 0` by decide_tac >>
  `x MOD p <> 0` by metis_tac[DIVIDES_MOD_0, NOT_LT_DIVIDES] >>
  `k MOD p <> 0` by metis_tac[EUCLID_LEMMA, MOD_MOD] >>
  decide_tac) >>
  metis_tac[MOD_LESS, LESS_MOD]);

(* Convert this theorem into MUL_INV_DEF *)

(* Step 1: move ?y forward by collecting quantifiers *)
val lemma = prove(
  ``!p x. ?y. prime p /\ 0 < x /\ x < p ==> 0 < y /\ y < p /\ ((y * x) MOD p = 1)``,
  metis_tac[MOD_MULT_INV_EXISTS]);

(* Step 2: apply SKOLEM_THM *)
(*
- SKOLEM_THM;
> val it = |- !P. (!x. ?y. P x y) <=> ?f. !x. P x (f x) : thm
*)
val MOD_MULT_INV_DEF = new_specification(
  "MOD_MULT_INV_DEF",
  ["MOD_MULT_INV"], (* avoid MOD_MULT_INV_EXISTS: thm *)
  SIMP_RULE (srw_ss()) [SKOLEM_THM] lemma);
(*
> val MOD_MULT_INV_DEF =
    |- !p x.
         prime p /\ 0 < x /\ x < p ==>
         0 < MOD_MULT_INV p x /\ MOD_MULT_INV p x < p /\
         ((MOD_MULT_INV p x * x) MOD p = 1) : thm
*)

(* ------------------------------------------------------------------------- *)
(* FACTOR Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: ~ prime n ==> n has a proper prime factor p *)
(* Proof: apply PRIME_FACTOR:
   !n. n <> 1 ==> ?p. prime p /\ p divides n : thm
*)
val PRIME_FACTOR_PROPER = store_thm(
  "PRIME_FACTOR_PROPER",
  ``!n. 1 < n /\ ~prime n ==> ?p. prime p /\ p < n /\ (p divides n)``,
  rpt strip_tac >>
  `0 < n /\ n <> 1` by decide_tac >>
  `?p. prime p /\ p divides n` by metis_tac[PRIME_FACTOR] >>
  `~(n < p)` by metis_tac[NOT_LT_DIVIDES] >>
  Cases_on `n = p` >-
  full_simp_tac std_ss[] >>
  `p < n` by decide_tac >>
  metis_tac[]);

(* Theorem: If p divides n, then there is a (p ** m) that maximally divides n. *)
(* Proof:
   Consider the set s = {k | p ** k divides n}
   Since p IN s, s <> {}           by MEMBER_NOT_EMPTY
   For k IN s, p ** k n divides ==> p ** k <= n    by DIVIDES_LE
   Since ?z. n <= p ** z           by EXP_ALWAYS_BIG_ENOUGH
   p ** k <= p ** z
        k <= z                     by EXP_BASE_LE_MONO
     or k < SUC z
   Hence s SUBSET count (SUC z)    by SUBSET_DEF
   and FINITE s                    by FINITE_COUNT, SUBSET_FINITE
   Let m = MAX_SET s
   Then p ** m n divides           by MAX_SET_DEF
   Let q = n DIV (p ** m)
   i.e.  n = q * (p ** m)
   If p divides q, then q = t * p
   or n = t * p * (p ** m)
        = t * (p * p ** m)         by MULT_ASSOC
        = t * p ** SUC m           by EXP
   i.e. p ** SUC m  divides n, or SUC m IN s.
   Since m < SUC m                 by LESS_SUC
   This contradicts the maximal property of m.
*)
val FACTOR_OUT_POWER = store_thm(
  "FACTOR_OUT_POWER",
  ``!n p. 0 < n /\ 1 < p /\ p divides n ==> ?m. (p ** m) divides n /\ ~(p divides (n DIV (p ** m)))``,
  rpt strip_tac >>
  `p <= n` by rw[DIVIDES_LE] >>
  `1 < n` by decide_tac >>
  qabbrev_tac `s = {k | (p ** k) divides n }` >>
  qexists_tac `MAX_SET s` >>
  qabbrev_tac `m = MAX_SET s` >>
  `!k. k IN s <=> (p ** k) divides n` by rw[Abbr`s`] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY, EXP_1] >>
  `?z. n <= p ** z` by rw[EXP_ALWAYS_BIG_ENOUGH] >>
  `!k. k IN s ==> k <= z` by metis_tac[DIVIDES_LE, EXP_BASE_LE_MONO, LESS_EQ_TRANS] >>
  `!k. k <= z ==> k < SUC z` by decide_tac >>
  `s SUBSET (count (SUC z))` by metis_tac[IN_COUNT, SUBSET_DEF, LESS_EQ_TRANS] >>
  `FINITE s` by metis_tac[FINITE_COUNT, SUBSET_FINITE] >>
  `m IN s /\ !y. y IN s ==> y <= m` by metis_tac[MAX_SET_DEF] >>
  `(p ** m) divides n` by metis_tac[] >>
  rw[] >>
  spose_not_then strip_assume_tac >>
  `0 < p` by decide_tac >>
  `0 < p ** m` by rw[EXP_POS] >>
  `n = (p ** m) * (n DIV (p ** m))` by rw[DIVIDES_FACTORS] >>
  `?q. n DIV (p ** m) = q * p` by rw[GSYM divides_def] >>
  `n = q * p ** SUC m` by metis_tac[MULT_COMM, MULT_ASSOC, EXP] >>
  `SUC m <= m` by metis_tac[divides_def] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Useful Theorems.                                                          *)
(* ------------------------------------------------------------------------- *)

(* binomial_add: same as SUM_SQUARED *)

(* Theorem: (a + b) ** 2 = a ** 2 + b ** 2 + 2 * a * b *)
(* Proof:
     (a + b) ** 2
   = (a + b) * (a + b)                   by EXP_2
   = a * (a + b) + b * (a + b)           by RIGHT_ADD_DISTRIB
   = (a * a + a * b) + (b * a + b * b)   by LEFT_ADD_DISTRIB
   = a * a + b * b + 2 * a * b           by arithmetic
   = a ** 2 + b ** 2 + 2 * a * b         by EXP_2
*)
Theorem binomial_add:
  !a b. (a + b) ** 2 = a ** 2 + b ** 2 + 2 * a * b
Proof
  rpt strip_tac >>
  `(a + b) ** 2 = (a + b) * (a + b)` by simp[] >>
  `_ = a * a + b * b + 2 * a * b` by decide_tac >>
  simp[]
QED

(* Theorem: b <= a ==> ((a - b) ** 2 = a ** 2 + b ** 2 - 2 * a * b) *)
(* Proof:
   If b = 0,
      RHS = a ** 2 + 0 ** 2 - 2 * a * 0
          = a ** 2 + 0 - 0
          = a ** 2
          = (a - 0) ** 2
          = LHS
   If b <> 0,
      Then b * b <= a * b                      by LE_MULT_RCANCEL, b <> 0
       and b * b <= 2 * a * b

      LHS = (a - b) ** 2
          = (a - b) * (a - b)                  by EXP_2
          = a * (a - b) - b * (a - b)          by RIGHT_SUB_DISTRIB
          = (a * a - a * b) - (b * a - b * b)  by LEFT_SUB_DISTRIB
          = a * a - (a * b + (a * b - b * b))  by SUB_PLUS
          = a * a - (a * b + a * b - b * b)    by LESS_EQ_ADD_SUB, b * b <= a * b
          = a * a - (2 * a * b - b * b)
          = a * a + b * b - 2 * a * b          by SUB_SUB, b * b <= 2 * a * b
          = a ** 2 + b ** 2 - 2 * a * b        by EXP_2
          = RHS
*)
Theorem binomial_sub:
  !a b. b <= a ==> ((a - b) ** 2 = a ** 2 + b ** 2 - 2 * a * b)
Proof
  rpt strip_tac >>
  Cases_on `b = 0` >-
  simp[] >>
  `b * b <= a * b` by rw[] >>
  `b * b <= 2 * a * b` by decide_tac >>
  `(a - b) ** 2 = (a - b) * (a - b)` by simp[] >>
  `_ = a * a + b * b - 2 * a * b` by decide_tac >>
  rw[]
QED

(* Theorem: 2 * a * b <= a ** 2 + b ** 2 *)
(* Proof:
   If a = b,
      LHS = 2 * a * a
          = a * a + a * a
          = a ** 2 + a ** 2        by EXP_2
          = RHS
   If a < b, then 0 < b - a.
      Thus 0 < (b - a) * (b - a)   by MULT_EQ_0
        or 0 < (b - a) ** 2        by EXP_2
        so 0 < b ** 2 + a ** 2 - 2 * b * a   by binomial_sub, a <= b
       ==> 2 * a * b < a ** 2 + b ** 2       due to 0 < RHS.
   If b < a, then 0 < a - b.
      Thus 0 < (a - b) * (a - b)   by MULT_EQ_0
        or 0 < (a - b) ** 2        by EXP_2
        so 0 < a ** 2 + b ** 2 - 2 * a * b   by binomial_sub, b <= a
       ==> 2 * a * b < a ** 2 + b ** 2       due to 0 < RHS.
*)
Theorem binomial_means:
  !a b. 2 * a * b <= a ** 2 + b ** 2
Proof
  rpt strip_tac >>
  Cases_on `a = b` >-
  simp[] >>
  Cases_on `a < b` >| [
    `b - a <> 0` by decide_tac >>
    `(b - a) * (b - a) <> 0` by metis_tac[MULT_EQ_0] >>
    `(b - a) * (b - a) = (b - a) ** 2` by simp[] >>
    `_ = b ** 2 + a ** 2 - 2 * b * a` by rw[binomial_sub] >>
    decide_tac,
    `a - b <> 0` by decide_tac >>
    `(a - b) * (a - b) <> 0` by metis_tac[MULT_EQ_0] >>
    `(a - b) * (a - b) = (a - b) ** 2` by simp[] >>
    `_ = a ** 2 + b ** 2 - 2 * a * b` by rw[binomial_sub] >>
    decide_tac
  ]
QED

(* Theorem: b <= a ==> (a - b) ** 2 + 2 * a * b = a ** 2 + b ** 2 *)
(* Proof:
   Note (a - b) ** 2 = a ** 2 + b ** 2 - 2 * a * b     by binomial_sub
    and 2 * a * b <= a ** 2 + b ** 2                   by binomial_means
   Thus (a - b) ** 2 + 2 * a * b = a ** 2 + b ** 2
*)
Theorem binomial_sub_sum:
  !a b. b <= a ==> (a - b) ** 2 + 2 * a * b = a ** 2 + b ** 2
Proof
  rpt strip_tac >>
  imp_res_tac binomial_sub >>
  assume_tac (binomial_means |> SPEC_ALL) >>
  decide_tac
QED

(* Theorem: b <= a ==> ((a - b) ** 2 + 4 * a * b = (a + b) ** 2) *)
(* Proof:
   Note: 2 * a * b <= a ** 2 + b ** 2          by binomial_means, as [1]
     (a - b) ** 2 + 4 * a * b
   = a ** 2 + b ** 2 - 2 * a * b + 4 * a * b   by binomial_sub, b <= a
   = a ** 2 + b ** 2 + 4 * a * b - 2 * a * b   by SUB_ADD, [1]
   = a ** 2 + b ** 2 + 2 * a * b
   = (a + b) ** 2                              by binomial_add
*)
Theorem binomial_sub_add:
  !a b. b <= a ==> ((a - b) ** 2 + 4 * a * b = (a + b) ** 2)
Proof
  rpt strip_tac >>
  `2 * a * b <= a ** 2 + b ** 2` by rw[binomial_means] >>
  `(a - b) ** 2 + 4 * a * b = a ** 2 + b ** 2 - 2 * a * b + 4 * a * b` by rw[binomial_sub] >>
  `_ = a ** 2 + b ** 2 + 4 * a * b - 2 * a * b` by decide_tac >>
  `_ = a ** 2 + b ** 2 + 2 * a * b` by decide_tac >>
  `_ = (a + b) ** 2` by rw[binomial_add] >>
  decide_tac
QED

(* Theorem: a ** 2 - b ** 2 = (a - b) * (a + b) *)
(* Proof:
     a ** 2 - b ** 2
   = a * a - b * b                       by EXP_2
   = a * a + a * b - a * b - b * b       by ADD_SUB
   = a * a + a * b - (b * a + b * b)     by SUB_PLUS
   = a * (a + b) - b * (a + b)           by LEFT_ADD_DISTRIB
   = (a - b) * (a + b)                   by RIGHT_SUB_DISTRIB
*)
Theorem difference_of_squares:
  !a b. a ** 2 - b ** 2 = (a - b) * (a + b)
Proof
  rpt strip_tac >>
  `a ** 2 - b ** 2 = a * a - b * b` by simp[] >>
  `_ = a * a + a * b - a * b - b * b` by decide_tac >>
  decide_tac
QED

(* Theorem: a * a - b * b = (a - b) * (a + b) *)
(* Proof:
     a * a - b * b
   = a ** 2 - b ** 2       by EXP_2
   = (a + b) * (a - b)     by difference_of_squares
*)
Theorem difference_of_squares_alt:
  !a b. a * a - b * b = (a - b) * (a + b)
Proof
  rw[difference_of_squares]
QED

(* binomial_2: same as binomial_add, or SUM_SQUARED *)

(* Theorem: (m + n) ** 2 = m ** 2 + n ** 2 + 2 * m * n *)
(* Proof:
     (m + n) ** 2
   = (m + n) * (m + n)                 by EXP_2
   = m * m + n * m + m * n + n * n     by LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB
   = m ** 2 + n ** 2 + 2 * m * n       by EXP_2
*)
val binomial_2 = store_thm(
  "binomial_2",
  ``!m n. (m + n) ** 2 = m ** 2 + n ** 2 + 2 * m * n``,
  rpt strip_tac >>
  `(m + n) ** 2 = (m + n) * (m + n)` by rw[] >>
  `_ = m * m + n * m + m * n + n * n` by decide_tac >>
  `_ = m ** 2 + n ** 2 + 2 * m * n` by rw[] >>
  decide_tac);

(* Obtain a corollary *)
val SUC_SQ = save_thm("SUC_SQ",
    binomial_2 |> SPEC ``1`` |> SIMP_RULE (srw_ss()) [GSYM SUC_ONE_ADD]);
(* val SUC_SQ = |- !n. SUC n ** 2 = SUC (n ** 2) + TWICE n: thm *)

(* Theorem: m <= n ==> SQ m <= SQ n *)
(* Proof:
   Since m * m <= n * n    by LE_MONO_MULT2
      so  SQ m <= SQ n     by notation
*)
val SQ_LE = store_thm(
  "SQ_LE",
  ``!m n. m <= n ==> SQ m <= SQ n``,
  rw[]);

(* Theorem: EVEN n /\ prime n <=> n = 2 *)
(* Proof:
   If part: EVEN n /\ prime n ==> n = 2
      EVEN n ==> n MOD 2 = 0       by EVEN_MOD2
             ==> 2 divides n       by DIVIDES_MOD_0, 0 < 2
             ==> n = 2             by prime_def, 2 <> 1
   Only-if part: n = 2 ==> EVEN n /\ prime n
      Note EVEN 2                  by EVEN_2
       and prime 2                 by prime_2
*)
(* Proof:
   EVEN n ==> n MOD 2 = 0    by EVEN_MOD2
          ==> 2 divides n    by DIVIDES_MOD_0, 0 < 2
          ==> n = 2          by prime_def, 2 <> 1
*)
Theorem EVEN_PRIME:
  !n. EVEN n /\ prime n <=> n = 2
Proof
  rw[EQ_IMP_THM] >>
  `0 < 2 /\ 2 <> 1` by decide_tac >>
  `2 divides n` by rw[DIVIDES_MOD_0, GSYM EVEN_MOD2] >>
  metis_tac[prime_def]
QED

(* Theorem: prime n /\ n <> 2 ==> ODD n *)
(* Proof:
   By contradiction, suppose ~ODD n.
   Then EVEN n                        by EVEN_ODD
    but EVEN n /\ prime n ==> n = 2   by EVEN_PRIME
   This contradicts n <> 2.
*)
val ODD_PRIME = store_thm(
  "ODD_PRIME",
  ``!n. prime n /\ n <> 2 ==> ODD n``,
  metis_tac[EVEN_PRIME, EVEN_ODD]);

(* Theorem: prime p ==> 2 <= p *)
(* Proof: by ONE_LT_PRIME *)
val TWO_LE_PRIME = store_thm(
  "TWO_LE_PRIME",
  ``!p. prime p ==> 2 <= p``,
  metis_tac[ONE_LT_PRIME, DECIDE``1 < n <=> 2 <= n``]);

(* Theorem: ~prime 4 *)
(* Proof:
   Note 4 = 2 * 2      by arithmetic
     so 2 divides 4    by divides_def
   thus ~prime 4       by primes_def
*)
Theorem NOT_PRIME_4:
  ~prime 4
Proof
  rpt strip_tac >>
  `4 = 2 * 2` by decide_tac >>
  `4 <> 2 /\ 4 <> 1 /\ 2 <> 1` by decide_tac >>
  metis_tac[prime_def, divides_def]
QED

(* Theorem: prime n /\ prime m ==> (n divides m <=> (n = m)) *)
(* Proof:
   If part: prime n /\ prime m /\ n divides m ==> (n = m)
      Note prime n
       ==> n <> 1           by NOT_PRIME_1
      With n divides m      by given
       and prime m          by given
      Thus n = m            by prime_def
   Only-if part; prime n /\ prime m /\ (n = m) ==> n divides m
      True as m divides m   by DIVIDES_REFL
*)
val prime_divides_prime = store_thm(
  "prime_divides_prime",
  ``!n m. prime n /\ prime m ==> (n divides m <=> (n = m))``,
  rw[EQ_IMP_THM] >>
  `n <> 1` by metis_tac[NOT_PRIME_1] >>
  metis_tac[prime_def]);
(* This is: dividesTheory.prime_divides_only_self;
|- !m n. prime m /\ prime n /\ m divides n ==> (m = n)
*)

(* Theorem: 0 < m /\ 1 < n /\ (!p. prime p /\ p divides m ==> (p MOD n = 1)) ==> (m MOD n = 1) *)
(* Proof:
   By complete induction on m.
   If m = 1, trivially true               by ONE_MOD
   If m <> 1,
      Then ?p. prime p /\ p divides m     by PRIME_FACTOR, m <> 1
       and ?q. m = q * p                  by divides_def
       and q divides m                    by divides_def, MULT_COMM
      In order to apply induction hypothesis,
      Show: q < m
            Note q <= m                   by DIVIDES_LE, 0 < m
             But p <> 1                   by NOT_PRIME_1
            Thus q <> m                   by MULT_RIGHT_1, EQ_MULT_LCANCEL, m <> 0
             ==> q < m
      Show: 0 < q
            Since m = q * p  and m <> 0   by above
            Thus q <> 0, or 0 < q         by MULT
      Show: !p. prime p /\ p divides q ==> (p MOD n = 1)
            If p divides q, and q divides m,
            Then p divides m              by DIVIDES_TRANS
             ==> p MOD n = 1              by implication

      Hence q MOD n = 1                   by induction hypothesis
        and p MOD n = 1                   by implication
        Now 0 < n                         by 1 < n
            m MDO n
          = (q * p) MOD n                 by m = q * p
          = (q MOD n * p MOD n) MOD n     by MOD_TIMES2, 0 < n
          = (1 * 1) MOD n                 by above
          = 1                             by MULT_RIGHT_1, ONE_MOD
*)
val ALL_PRIME_FACTORS_MOD_EQ_1 = store_thm(
  "ALL_PRIME_FACTORS_MOD_EQ_1",
  ``!m n. 0 < m /\ 1 < n /\ (!p. prime p /\ p divides m ==> (p MOD n = 1)) ==> (m MOD n = 1)``,
  completeInduct_on `m` >>
  rpt strip_tac >>
  Cases_on `m = 1` >-
  rw[] >>
  `?p. prime p /\ p divides m` by rw[PRIME_FACTOR] >>
  `?q. m = q * p` by rw[GSYM divides_def] >>
  `q divides m` by metis_tac[divides_def, MULT_COMM] >>
  `p <> 1` by metis_tac[NOT_PRIME_1] >>
  `m <> 0` by decide_tac >>
  `q <> m` by metis_tac[MULT_RIGHT_1, EQ_MULT_LCANCEL] >>
  `q <= m` by metis_tac[DIVIDES_LE] >>
  `q < m` by decide_tac >>
  `q <> 0` by metis_tac[MULT] >>
  `0 < q` by decide_tac >>
  `!p. prime p /\ p divides q ==> (p MOD n = 1)` by metis_tac[DIVIDES_TRANS] >>
  `q MOD n = 1` by rw[] >>
  `p MOD n = 1` by rw[] >>
  `0 < n` by decide_tac >>
  metis_tac[MOD_TIMES2, MULT_RIGHT_1, ONE_MOD]);

(* Theorem: prime p /\ 0 < n ==> !b. p divides (b ** n) <=> p divides b *)
(* Proof:
   If part: p divides b ** n ==> p divides b
      By induction on n.
      Base: 0 < 0 ==> p divides b ** 0 ==> p divides b
         True by 0 < 0 = F.
      Step: 0 < n ==> p divides b ** n ==> p divides b ==>
            0 < SUC n ==> p divides b ** SUC n ==> p divides b
         If n = 0,
              b ** SUC 0
            = b ** 1                  by ONE
            = b                       by EXP_1
            so p divides b.
         If n <> 0, 0 < n.
              b ** SUC n
            = b * b ** n              by EXP
            Thus p divides b,
              or p divides (b ** n)   by P_EUCLIDES
            For the latter case,
                 p divides b          by induction hypothesis, 0 < n

   Only-if part: p divides b ==> p divides b ** n
      Since n <> 0, ?m. n = SUC m     by num_CASES
        and b ** n
          = b ** SUC m
          = b * b ** m                by EXP
       Thus p divides b ** n          by DIVIDES_MULTIPLE, MULT_COMM
*)
val prime_divides_power = store_thm(
  "prime_divides_power",
  ``!p n. prime p /\ 0 < n ==> !b. p divides (b ** n) <=> p divides b``,
  rw[EQ_IMP_THM] >| [
    Induct_on `n` >-
    rw[] >>
    rpt strip_tac >>
    Cases_on `n = 0` >-
    metis_tac[ONE, EXP_1] >>
    `0 < n` by decide_tac >>
    `b ** SUC n = b * b ** n` by rw[EXP] >>
    metis_tac[P_EUCLIDES],
    `n <> 0` by decide_tac >>
    `?m. n = SUC m` by metis_tac[num_CASES] >>
    `b ** SUC m = b * b ** m` by rw[EXP] >>
    metis_tac[DIVIDES_MULTIPLE, MULT_COMM]
  ]);

(* Theorem: prime p ==> !n. 0 < n ==> p divides p ** n *)
(* Proof:
   Since p divides p        by DIVIDES_REFL
      so p divides p ** n   by prime_divides_power, 0 < n
*)
val prime_divides_self_power = store_thm(
  "prime_divides_self_power",
  ``!p. prime p ==> !n. 0 < n ==> p divides p ** n``,
  rw[prime_divides_power, DIVIDES_REFL]);

(* Theorem: prime p ==> !b n m. 0 < m /\ (b ** n = p ** m) ==> ?k. (b = p ** k) /\ (k * n = m) *)
(* Proof:
   Note 1 < p                    by ONE_LT_PRIME
     so p <> 0, 0 < p, p <> 1    by arithmetic
   also m <> 0                   by 0 < m
   Thus p ** m <> 0              by EXP_EQ_0, p <> 0
    and p ** m <> 1              by EXP_EQ_1, p <> 1, m <> 0
    ==> n <> 0, 0 < n            by EXP, b ** n = p ** m <> 1
   also b <> 0, 0 < b            by EXP_EQ_0, b ** n = p ** m <> 0, 0 < n

   Step 1: show p divides b.
   Note p divides (p ** m)       by prime_divides_self_power, 0 < m
     so p divides (b ** n)       by given, b ** n = p ** m
     or p divides b              by prime_divides_power, 0 < b

   Step 2: express b = q * p ** u  where ~(p divides q).
   Note 1 < p /\ 0 < b /\ p divides b
    ==> ?u. p ** u divides b /\ ~(p divides b DIV p ** u)  by FACTOR_OUT_POWER
    Let q = b DIV p ** u, v = u * n.
   Since p ** u <> 0             by EXP_EQ_0, p <> 0
      so b = q * p ** u          by DIVIDES_EQN, 0 < p ** u
         p ** m
       = (q * p ** u) ** n       by b = q * p ** u
       = q ** n * (p ** u) ** n  by EXP_BASE_MULT
       = q ** n * p ** (u * n)   by EXP_EXP_MULT
       = q ** n * p ** v         by v = u * n

   Step 3: split cases
   If v = m,
      Then q ** n * p ** m = 1 * p ** m     by above
        or          q ** n = 1              by EQ_MULT_RCANCEL, p ** m <> 0
      giving             q = 1              by EXP_EQ_1, 0 < n
      Thus b = p ** u                       by b = q * p ** u
      Take k = u, the result follows.

   If v < m,
      Let d = m - v.
      Then 0 < d /\ (m = d + v)             by arithmetic
       and p ** m = p ** d * p ** v         by EXP_ADD
      Note p ** v <> 0                      by EXP_EQ_0, p <> 0
           q ** n * p ** v = p ** d * p ** v
       ==>          q ** n = p ** d         by EQ_MULT_RCANCEL, p ** v <> 0
      Now p divides p ** d                  by prime_divides_self_power, 0 < d
       so p divides q ** n                  by above, q ** n = p ** d
      ==> p divides q                       by prime_divides_power, 0 < n
      This contradicts ~(p divides q)

   If m < v,
      Let d = v - m.
      Then 0 < d /\ (v = d + m)             by arithmetic
       and q ** n * p ** v
         = q ** n * (p ** d * p ** m)       by EXP_ADD
         = q ** n * p ** d * p ** m         by MULT_ASSOC
         = 1 * p ** m                       by arithmetic, b ** n = p ** m
      Hence q ** n * p ** d = 1             by EQ_MULT_RCANCEL, p ** m <> 0
        ==> (q ** n = 1) /\ (p ** d = 1)    by MULT_EQ_1
        But p ** d <> 1                     by EXP_EQ_1, 0 < d
       This contradicts p ** d = 1.
*)
Theorem power_eq_prime_power:
  !p. prime p ==>
      !b n m. 0 < m /\ (b ** n = p ** m) ==> ?k. (b = p ** k) /\ (k * n = m)
Proof
  rpt strip_tac >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `m <> 0 /\ 0 < p /\ p <> 0 /\ p <> 1` by decide_tac >>
  `p ** m <> 0` by rw[EXP_EQ_0] >>
  `p ** m <> 1` by rw[EXP_EQ_1] >>
  `n <> 0` by metis_tac[EXP] >>
  `0 < n /\ 0 < p ** m` by decide_tac >>
  `b <> 0` by metis_tac[EXP_EQ_0] >>
  `0 < b` by decide_tac >>
  `p divides (p ** m)` by rw[prime_divides_self_power] >>
  `p divides b` by metis_tac[prime_divides_power] >>
  `?u. p ** u divides b /\ ~(p divides b DIV p ** u)` by metis_tac[FACTOR_OUT_POWER] >>
  qabbrev_tac `q = b DIV p ** u` >>
  `p ** u <> 0` by rw[EXP_EQ_0] >>
  `0 < p ** u` by decide_tac >>
  `b = q * p ** u` by rw[GSYM DIVIDES_EQN, Abbr`q`] >>
  `q ** n * p ** (u * n) = p ** m` by metis_tac[EXP_BASE_MULT, EXP_EXP_MULT] >>
  qabbrev_tac `v = u * n` >>
  Cases_on `v = m` >| [
    `p ** m = 1 * p ** m` by simp[] >>
    `q ** n = 1` by metis_tac[EQ_MULT_RCANCEL] >>
    `q = 1` by metis_tac[EXP_EQ_1] >>
    `b = p ** u` by simp[] >>
    metis_tac[],
    Cases_on `v < m` >| [
      `?d. d = m - v` by rw[] >>
      `0 < d /\ (m = d + v)` by rw[] >>
      `p ** m = p ** d * p ** v` by rw[EXP_ADD] >>
      `p ** v <> 0` by metis_tac[EXP_EQ_0] >>
      `q ** n = p ** d` by metis_tac[EQ_MULT_RCANCEL] >>
      `p divides p ** d` by metis_tac[prime_divides_self_power] >>
      metis_tac[prime_divides_power],
      `m < v` by decide_tac >>
      `?d. d = v - m` by rw[] >>
      `0 < d /\ (v = d + m)` by rw[] >>
      `d <> 0` by decide_tac >>
      `q ** n * p ** d * p ** m = p ** m` by metis_tac[EXP_ADD, MULT_ASSOC] >>
      `_ = 1 * p ** m` by rw[] >>
      `q ** n * p ** d = 1` by metis_tac[EQ_MULT_RCANCEL] >>
      `(q ** n = 1) /\ (p ** d = 1)` by metis_tac[MULT_EQ_1] >>
      metis_tac[EXP_EQ_1]
    ]
  ]
QED

(* Theorem: 1 < n ==> !m. (n ** m = n) <=> (m = 1) *)
(* Proof:
   If part: n ** m = n ==> m = 1
      Note n = n ** 1           by EXP_1
        so n ** m = n ** 1      by given
        or      m = 1           by EXP_BASE_INJECTIVE, 1 < n
   Only-if part: m = 1 ==> n ** m = n
      This is true              by EXP_1
*)
val POWER_EQ_SELF = store_thm(
  "POWER_EQ_SELF",
  ``!n. 1 < n ==> !m. (n ** m = n) <=> (m = 1)``,
  metis_tac[EXP_BASE_INJECTIVE, EXP_1]);

(* Theorem: k < HALF n <=> k + 1 < n - k *)
(* Proof:
   If part: k < HALF n ==> k + 1 < n - k
      Claim: 1 < n - 2 * k.
      Proof: If EVEN n,
                Claim: n - 2 * k <> 0
                Proof: By contradiction, assume n - 2 * k = 0.
                       Then 2 * k = n = 2 * HALF n      by EVEN_HALF
                         or     k = HALF n              by MULT_LEFT_CANCEL, 2 <> 0
                         but this contradicts k < HALF n.
                Claim: n - 2 * k <> 1
                Proof: By contradiction, assume n - 2 * k = 1.
                       Then n = 2 * k + 1               by SUB_EQ_ADD, 0 < 1
                         or ODD n                       by ODD_EXISTS, ADD1
                        but this contradicts EVEN n     by EVEN_ODD
                Thus n - 2 * k <> 1, or 1 < n - 2 * k   by above claims.
      Since 1 < n - 2 * k         by above
         so 2 * k + 1 < n         by arithmetic
         or k + k + 1 < n         by TIMES2
         or     k + 1 < n - k     by arithmetic

   Only-if part: k + 1 < n - k ==> k < HALF n
      Since     k + 1 < n - k
         so 2 * k + 1 < n                by arithmetic
        But n = 2 * HALF n + (n MOD 2)   by DIVISION, MULT_COMM, 0 < 2
        and n MOD 2 < 2                  by MOD_LESS, 0 < 2
         so n <= 2 * HALF n + 1          by arithmetic
       Thus 2 * k + 1 < 2 * HALF n + 1   by LESS_LESS_EQ_TRANS
         or         k < HALF             by LT_MULT_LCANCEL
*)
val LESS_HALF_IFF = store_thm(
  "LESS_HALF_IFF",
  ``!n k. k < HALF n <=> k + 1 < n - k``,
  rw[EQ_IMP_THM] >| [
    `1 < n - 2 * k` by
  (Cases_on `EVEN n` >| [
      `n - 2 * k <> 0` by
  (spose_not_then strip_assume_tac >>
      `2 * HALF n = n` by metis_tac[EVEN_HALF] >>
      decide_tac) >>
      `n - 2 * k <> 1` by
    (spose_not_then strip_assume_tac >>
      `n = 2 * k + 1` by decide_tac >>
      `ODD n` by metis_tac[ODD_EXISTS, ADD1] >>
      metis_tac[EVEN_ODD]) >>
      decide_tac,
      `n MOD 2 = 1` by metis_tac[EVEN_ODD, ODD_MOD2] >>
      `n = 2 * HALF n + (n MOD 2)` by metis_tac[DIVISION, MULT_COMM, DECIDE``0 < 2``] >>
      decide_tac
    ]) >>
    decide_tac,
    `2 * k + 1 < n` by decide_tac >>
    `n = 2 * HALF n + (n MOD 2)` by metis_tac[DIVISION, MULT_COMM, DECIDE``0 < 2``] >>
    `n MOD 2 < 2` by rw[] >>
    decide_tac
  ]);

(* Theorem: HALF n < k ==> n - k <= HALF n *)
(* Proof:
   If k < n,
      If EVEN n,
         Note HALF n + HALF n < k + HALF n   by HALF n < k
           or      2 * HALF n < k + HALF n   by TIMES2
           or               n < k + HALF n   by EVEN_HALF, EVEN n
           or           n - k < HALF n       by LESS_EQ_SUB_LESS, k <= n
         Hence true.
      If ~EVEN n, then ODD n                 by EVEN_ODD
         Note HALF n + HALF n + 1 < k + HALF n + 1   by HALF n < k
           or      2 * HALF n + 1 < k + HALF n + 1   by TIMES2
           or         n < k + HALF n + 1     by ODD_HALF
           or         n <= k + HALF n        by arithmetic
           so     n - k <= HALF n            by SUB_LESS_EQ_ADD, k <= n
   If ~(k < n), then n <= k.
      Thus n - k = 0, hence n - k <= HALF n  by arithmetic
*)
val MORE_HALF_IMP = store_thm(
  "MORE_HALF_IMP",
  ``!n k. HALF n < k ==> n - k <= HALF n``,
  rpt strip_tac >>
  Cases_on `k < n` >| [
    Cases_on `EVEN n` >| [
      `n = 2 * HALF n` by rw[EVEN_HALF] >>
      `n < k + HALF n` by decide_tac >>
      `n - k < HALF n` by decide_tac >>
      decide_tac,
      `ODD n` by rw[ODD_EVEN] >>
      `n = 2 * HALF n + 1` by rw[ODD_HALF] >>
      decide_tac
    ],
    decide_tac
  ]);

(* Theorem: (!k. k < m ==> f k < f (k + 1)) ==> !k. k < m ==> f k < f m *)
(* Proof:
   By induction on the difference (m - k):
   Base: 0 = m - k /\ k < m ==> f k < f m
      Note m = k and k < m contradicts, hence true.
   Step: !m k. (v = m - k) ==> k < m ==> f k < f m ==>
         SUC v = m - k /\ k < m ==> f k < f m
      Note v + 1 = m - k        by ADD1
        so v = m - (k + 1)      by arithmetic
      If v = 0,
         Then m = k + 1
           so f k < f (k + 1)   by implication
           or f k < f m         by m = k + 1
      If v <> 0, then 0 < v.
         Then 0 < m - (k + 1)   by v = m - (k + 1)
           or k + 1 < m         by arithmetic
          Now f k < f (k + 1)   by implication, k < m
          and f (k + 1) < f m   by induction hypothesis, put k = k + 1
           so f k < f m         by LESS_TRANS
*)
val MONOTONE_MAX = store_thm(
  "MONOTONE_MAX",
  ``!f m. (!k. k < m ==> f k < f (k + 1)) ==> !k. k < m ==> f k < f m``,
  rpt strip_tac >>
  Induct_on `m - k` >| [
    rpt strip_tac >>
    decide_tac,
    rpt strip_tac >>
    `v + 1 = m - k` by rw[] >>
    `v = m - (k + 1)` by decide_tac >>
    Cases_on `v = 0` >| [
      `m = k + 1` by decide_tac >>
      rw[],
      `k + 1 < m` by decide_tac >>
      `f k < f (k + 1)` by rw[] >>
      `f (k + 1) < f m` by rw[] >>
      decide_tac
    ]
  ]);

(* Theorem: (multiple gap)
   If n divides m, n cannot divide any x: m - n < x < m, or m < x < m + n
   n divides m ==> !x. m - n < x /\ x < m + n /\ n divides x ==> (x = m) *)
(* Proof:
   All these x, when divided by n, have non-zero remainders.
   Since n divides m and n divides x
     ==> ?h. m = h * n, and ?k. x = k * n  by divides_def
   Hence m - n < x
     ==> (h-1) * n < k * n                 by RIGHT_SUB_DISTRIB, MULT_LEFT_1
     and x < m + n
     ==>     k * n < (h+1) * n             by RIGHT_ADD_DISTRIB, MULT_LEFT_1
      so 0 < n, and h-1 < k, and k < h+1   by LT_MULT_RCANCEL
     that is, h <= k, and k <= h
   Therefore  h = k, or m = h * n = k * n = x.
*)
val MULTIPLE_INTERVAL = store_thm(
  "MULTIPLE_INTERVAL",
  ``!n m. n divides m ==> !x. m - n < x /\ x < m + n /\ n divides x ==> (x = m)``,
  rpt strip_tac >>
  `(?h. m = h*n) /\ (?k. x = k * n)` by metis_tac[divides_def] >>
  `(h-1) * n < k * n` by metis_tac[RIGHT_SUB_DISTRIB, MULT_LEFT_1] >>
  `k * n < (h+1) * n` by metis_tac[RIGHT_ADD_DISTRIB, MULT_LEFT_1] >>
  `0 < n /\ h-1 < k /\ k < h+1` by metis_tac[LT_MULT_RCANCEL] >>
  `h = k` by decide_tac >>
  metis_tac[]);

(* Theorem: 0 < m ==> (SUC (n MOD m) = SUC n MOD m + (SUC n DIV m - n DIV m) * m) *)
(* Proof:
   Let x = n DIV m, y = (SUC n) DIV m.
   Let a = SUC (n MOD m), b = (SUC n) MOD m.
   Note SUC n = y * m + b                 by DIVISION, 0 < m, for (SUC n), [1]
    and     n = x * m + (n MOD m)         by DIVISION, 0 < m, for n
     so SUC n = SUC (x * m + (n MOD m))   by above
              = x * m + a                 by ADD_SUC, [2]
   Equating, x * m + a = y * m + b        by [1], [2]
   Now n < SUC n                          by SUC_POS
    so n DIV m <= (SUC n) DIV m           by DIV_LE_MONOTONE, n <= SUC n
    or       x <= y
    so   x * m <= y * m                   by LE_MULT_RCANCEL, m <> 0

   Thus a = b + (y * m - x * m)           by arithmetic
          = b + (y - x) * m               by RIGHT_SUB_DISTRIB
*)
val MOD_SUC_EQN = store_thm(
  "MOD_SUC_EQN",
  ``!m n. 0 < m ==> (SUC (n MOD m) = SUC n MOD m + (SUC n DIV m - n DIV m) * m)``,
  rpt strip_tac >>
  qabbrev_tac `x = n DIV m` >>
  qabbrev_tac `y = (SUC n) DIV m` >>
  qabbrev_tac `a = SUC (n MOD m)` >>
  qabbrev_tac `b = (SUC n) MOD m` >>
  `SUC n = y * m + b` by rw[DIVISION, Abbr`y`, Abbr`b`] >>
  `n = x * m + (n MOD m)` by rw[DIVISION, Abbr`x`] >>
  `SUC n = x * m + a` by rw[Abbr`a`] >>
  `n < SUC n` by rw[] >>
  `x <= y` by rw[DIV_LE_MONOTONE, Abbr`x`, Abbr`y`] >>
  `x * m <= y * m` by rw[] >>
  `a = b + (y * m - x * m)` by decide_tac >>
  `_ = b + (y - x) * m` by rw[] >>
  rw[]);

(* Note: Compare this result with these in arithmeticTheory:
MOD_SUC      |- 0 < y /\ SUC x <> SUC (x DIV y) * y ==> (SUC x MOD y = SUC (x MOD y))
MOD_SUC_IFF  |- 0 < y ==> ((SUC x MOD y = SUC (x MOD y)) <=> SUC x <> SUC (x DIV y) * y)
*)

(* Theorem: 1 < n ==> 1 < HALF (n ** 2) *)
(* Proof:
       1 < n
   ==> 2 <= n                            by arithmetic
   ==> 2 ** 2 <= n ** 2                  by EXP_EXP_LE_MONO
   ==> (2 ** 2) DIV 2 <= (n ** 2) DIV 2  by DIV_LE_MONOTONE
   ==> 2 <= (n ** 2) DIV 2               by arithmetic
   ==> 1 < (n ** 2) DIV 2                by arithmetic
*)
val ONE_LT_HALF_SQ = store_thm(
  "ONE_LT_HALF_SQ",
  ``!n. 1 < n ==> 1 < HALF (n ** 2)``,
  rpt strip_tac >>
  `2 <= n` by decide_tac >>
  `2 ** 2 <= n ** 2` by rw[] >>
  `(2 ** 2) DIV 2 <= (n ** 2) DIV 2` by rw[DIV_LE_MONOTONE] >>
  `(2 ** 2) DIV 2 = 2` by EVAL_TAC >>
  decide_tac);

(* Theorem: 0 < n ==> (HALF (2 ** n) = 2 ** (n - 1)) *)
(* Proof
   By induction on n.
   Base: 0 < 0 ==> 2 ** 0 DIV 2 = 2 ** (0 - 1)
      This is trivially true as 0 < 0 = F.
   Step:  0 < n ==> HALF (2 ** n) = 2 ** (n - 1)
      ==> 0 < SUC n ==> HALF (2 ** SUC n) = 2 ** (SUC n - 1)
        HALF (2 ** SUC n)
      = HALF (2 * 2 ** n)          by EXP
      = 2 ** n                     by MULT_TO_DIV
      = 2 ** (SUC n - 1)           by SUC_SUB1
*)
Theorem EXP_2_HALF:
  !n. 0 < n ==> (HALF (2 ** n) = 2 ** (n - 1))
Proof
  Induct >> simp[EXP, MULT_TO_DIV]
QED

(*
There is EVEN_MULT    |- !m n. EVEN (m * n) <=> EVEN m \/ EVEN n
There is EVEN_DOUBLE  |- !n. EVEN (TWICE n)
*)

(* Theorem: EVEN n ==> (HALF (m * n) = m * HALF n) *)
(* Proof:
   Note n = TWICE (HALF n)  by EVEN_HALF
   Let k = HALF n.
     HALF (m * n)
   = HALF (m * (2 * k))  by above
   = HALF (2 * (m * k))  by MULT_COMM_ASSOC
   = m * k               by HALF_TWICE
   = m * HALF n          by notation
*)
val HALF_MULT_EVEN = store_thm(
  "HALF_MULT_EVEN",
  ``!m n. EVEN n ==> (HALF (m * n) = m * HALF n)``,
  metis_tac[EVEN_HALF, MULT_COMM_ASSOC, HALF_TWICE]);

(* Theorem: 0 < k /\ k * m < n ==> m < n *)
(* Proof:
   Note ?h. k = SUC h     by num_CASES, k <> 0
        k * m
      = SUC h * m         by above
      = (h + 1) * m       by ADD1
      = h * m + 1 * m     by LEFT_ADD_DISTRIB
      = h * m + m         by MULT_LEFT_1
   Since 0 <= h * m,
      so k * m < n ==> m < n.
*)
val MULT_LT_IMP_LT = store_thm(
  "MULT_LT_IMP_LT",
  ``!m n k. 0 < k /\ k * m < n ==> m < n``,
  rpt strip_tac >>
  `k <> 0` by decide_tac >>
  `?h. k = SUC h` by metis_tac[num_CASES] >>
  `k * m = h * m + m` by rw[ADD1] >>
  decide_tac);

(* Theorem: 0 < k /\ k * m <= n ==> m <= n *)
(* Proof:
   Note     1 <= k                 by 0 < k
     so 1 * m <= k * m             by LE_MULT_RCANCEL
     or     m <= k * m <= n        by inequalities
*)
Theorem MULT_LE_IMP_LE:
  !m n k. 0 < k /\ k * m <= n ==> m <= n
Proof
  rpt strip_tac >>
  `1 <= k` by decide_tac >>
  `1 * m <= k * m` by simp[] >>
  decide_tac
QED

(* Theorem: n * HALF ((SQ n) ** 2) <= HALF (n ** 5) *)
(* Proof:
      n * HALF ((SQ n) ** 2)
   <= HALF (n * (SQ n) ** 2)     by HALF_MULT
    = HALF (n * (n ** 2) ** 2)   by EXP_2
    = HALF (n * n ** 4)          by EXP_EXP_MULT
    = HALF (n ** 5)              by EXP
*)
val HALF_EXP_5 = store_thm(
  "HALF_EXP_5",
  ``!n. n * HALF ((SQ n) ** 2) <= HALF (n ** 5)``,
  rpt strip_tac >>
  `n * ((SQ n) ** 2) = n * n ** 4` by rw[EXP_2, EXP_EXP_MULT] >>
  `_ = n ** 5` by rw[EXP] >>
  metis_tac[HALF_MULT]);

(* Theorem: n <= 2 * m <=> (n <> 0 ==> HALF (n - 1) < m) *)
(* Proof:
   Let k = n - 1, then n = SUC k.
   If part: n <= TWICE m /\ n <> 0 ==> HALF k < m
      Note HALF (SUC k) <= m                by DIV_LE_MONOTONE, HALF_TWICE
      If EVEN n,
         Then ODD k                         by EVEN_ODD_SUC
          ==> HALF (SUC k) = SUC (HALF k)   by ODD_SUC_HALF
         Thus SUC (HALF k) <= m             by above
           or        HALF k < m             by LESS_EQ
      If ~EVEN n, then ODD n                by EVEN_ODD
         Thus EVEN k                        by EVEN_ODD_SUC
          ==> HALF (SUC k) = HALF k         by EVEN_SUC_HALF
          But k <> TWICE m                  by k = n - 1, n <= TWICE m
          ==> HALF k <> m                   by EVEN_HALF
         Thus  HALF k < m                   by HALF k <= m, HALF k <> m

   Only-if part: n <> 0 ==> HALF k < m ==> n <= TWICE m
      If n = 0, trivially true.
      If n <> 0, has HALF k < m.
         If EVEN n,
            Then ODD k                        by EVEN_ODD_SUC
             ==> HALF (SUC k) = SUC (HALF k)  by ODD_SUC_HALF
             But SUC (HALF k) <= m            by HALF k < m
            Thus HALF n <= m                  by n = SUC k
             ==> TWICE (HALF n) <= TWICE m    by LE_MULT_LCANCEL
              or              n <= TWICE m    by EVEN_HALF
         If ~EVEN n, then ODD n               by EVEN_ODD
            Then EVEN k                       by EVEN_ODD_SUC
             ==> TWICE (HALF k) < TWICE m     by LT_MULT_LCANCEL
              or              k < TWICE m     by EVEN_HALF
              or             n <= TWICE m     by n = k + 1
*)
val LE_TWICE_ALT = store_thm(
  "LE_TWICE_ALT",
  ``!m n. n <= 2 * m <=> (n <> 0 ==> HALF (n - 1) < m)``,
  rw[EQ_IMP_THM] >| [
    `n = SUC (n - 1)` by decide_tac >>
    qabbrev_tac `k = n - 1` >>
    `HALF (SUC k) <= m` by metis_tac[DIV_LE_MONOTONE, HALF_TWICE, DECIDE``0 < 2``] >>
    Cases_on `EVEN n` >| [
      `ODD k` by rw[EVEN_ODD_SUC] >>
      `HALF (SUC k) = SUC (HALF k)` by rw[ODD_SUC_HALF] >>
      decide_tac,
      `ODD n` by metis_tac[EVEN_ODD] >>
      `EVEN k` by rw[EVEN_ODD_SUC] >>
      `HALF (SUC k) = HALF k` by rw[EVEN_SUC_HALF] >>
      `k <> TWICE m` by rw[Abbr`k`] >>
      `HALF k <> m` by metis_tac[EVEN_HALF] >>
      decide_tac
    ],
    Cases_on `n = 0` >-
    rw[] >>
    `n = SUC (n - 1)` by decide_tac >>
    qabbrev_tac `k = n - 1` >>
    Cases_on `EVEN n` >| [
      `ODD k` by rw[EVEN_ODD_SUC] >>
      `HALF (SUC k) = SUC (HALF k)` by rw[ODD_SUC_HALF] >>
      `HALF n <= m` by rw[] >>
      metis_tac[LE_MULT_LCANCEL, EVEN_HALF, DECIDE``2 <> 0``],
      `ODD n` by metis_tac[EVEN_ODD] >>
      `EVEN k` by rw[EVEN_ODD_SUC] >>
      `k < TWICE m` by metis_tac[LT_MULT_LCANCEL, EVEN_HALF, DECIDE``0 < 2``] >>
      rw[Abbr`k`]
    ]
  ]);

(* Theorem: (HALF n) DIV 2 ** m = n DIV (2 ** SUC m) *)
(* Proof:
     (HALF n) DIV 2 ** m
   = (n DIV 2) DIV (2 ** m)    by notation
   = n DIV (2 * 2 ** m)        by DIV_DIV_DIV_MULT, 0 < 2, 0 < 2 ** m
   = n DIV (2 ** (SUC m))      by EXP
*)
val HALF_DIV_TWO_POWER = store_thm(
  "HALF_DIV_TWO_POWER",
  ``!m n. (HALF n) DIV 2 ** m = n DIV (2 ** SUC m)``,
  rw[DIV_DIV_DIV_MULT, EXP]);

(* Theorem: 1 + 2 + 3 + 4 = 10 *)
(* Proof: by calculation. *)
Theorem fit_for_10:
  1 + 2 + 3 + 4 = 10
Proof
  decide_tac
QED

(* Theorem: 1 * 2 + 3 * 4 + 5 * 6 + 7 * 8 = 100 *)
(* Proof: by calculation. *)
Theorem fit_for_100:
  1 * 2 + 3 * 4 + 5 * 6 + 7 * 8 = 100
Proof
  decide_tac
QED

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
