(* ------------------------------------------------------------------------- *)
(* Integer Functions Computation (logPower)                                  *)
(* Prime Power (primePower)                                                  *)
(* Primality Tests (primes)                                                  *)
(* Gauss' Little Theorem                                                     *)
(* Mobius Function and Inversion.                                            *)
(* ------------------------------------------------------------------------- *)
(* Author: (Joseph) Hing-Lun Chan (Australian National University, 2019)     *)
(* ------------------------------------------------------------------------- *)

open HolKernel boolLib bossLib Parse;

open arithmeticTheory pred_setTheory dividesTheory gcdTheory logrootTheory
     listTheory rich_listTheory listRangeTheory gcdsetTheory optionTheory
     numberTheory combinatoricsTheory prim_recTheory;

val _ = new_theory "prime";

val _ = temp_overload_on("SQ", ``\n. n * n``);
val _ = temp_overload_on("HALF", ``\n. n DIV 2``);
val _ = temp_overload_on("TWICE", ``\n. 2 * n``);

(* ------------------------------------------------------------------------- *)
(* Integer Functions Computation Documentation                               *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   SQRT n       = ROOT 2 n
   LOG2 n       = LOG 2 n
   n power_of b = perfect_power n b
*)

(* Definitions and Theorems (# are exported):

   ROOT computation:
   ROOT_POWER       |- !a n. 1 < a /\ 0 < n ==> (ROOT n (a ** n) = a)
   ROOT_FROM_POWER  |- !m n b. 0 < m /\ (b ** m = n) ==> (b = ROOT m n)
#  ROOT_OF_0        |- !m. 0 < m ==> (ROOT m 0 = 0)
#  ROOT_OF_1        |- !m. 0 < m ==> (ROOT m 1 = 1)
   ROOT_EQ_0        |- !m. 0 < m ==> !n. (ROOT m n = 0) <=> (n = 0)
#  ROOT_1           |- !n. ROOT 1 n = n
   ROOT_THM         |- !r. 0 < r ==> !n p. (ROOT r n = p) <=> p ** r <= n /\ n < SUC p ** r
   ROOT_EQN         |- !r n. 0 < r ==> (ROOT r n =
                             (let m = TWICE (ROOT r (n DIV 2 ** r))
                               in m + if (m + 1) ** r <= n then 1 else 0))
   ROOT_SUC         |- !r n. 0 < r ==>
                             ROOT r (SUC n) = ROOT r n +
                                              if SUC n = SUC (ROOT r n) ** r then 1 else 0
   ROOT_EQ_1        |- !m. 0 < m ==> !n. (ROOT m n = 1) <=> 0 < n /\ n < 2 ** m
   ROOT_LE_SELF     |- !m n. 0 < m ==> ROOT m n <= n
   ROOT_EQ_SELF     |- !m n. 0 < m ==> (ROOT m n = n) <=> (m = 1) \/ (n = 0) \/ (n = 1))
   ROOT_GE_SELF     |- !m n. 0 < m ==> (n <= ROOT m n) <=> (m = 1) \/ (n = 0) \/ (n = 1))
   ROOT_LE_REVERSE  |- !a b n. 0 < a /\ a <= b ==> ROOT b n <= ROOT a n

   Square Root:
   SQRT_PROPERTY    |- !n. 0 < n ==> SQRT n ** 2 <= n /\ n < SUC (SQRT n) ** 2
   SQRT_UNIQUE      |- !n p. p ** 2 <= n /\ n < SUC p ** 2 ==> SQRT n = p
   SQRT_THM         |- !n p. (SQRT n = p) <=> p ** 2 <= n /\ n < SUC p ** 2
   SQ_SQRT_LE       |- !n. SQ (SQRT n) <= n
   SQ_SQRT_LE_alt   |- !n. SQRT n ** 2 <= n
   SQRT_LE          |- !n m. n <= m ==> SQRT n <= SQRT m
   SQRT_LT          |- !n m. n < m ==> SQRT n <= SQRT m
#  SQRT_0           |- SQRT 0 = 0
#  SQRT_1           |- SQRT 1 = 1
   SQRT_EQ_0        |- !n. (SQRT n = 0) <=> (n = 0)
   SQRT_EQ_1        |- !n. (SQRT n = 1) <=> (n = 1) \/ (n = 2) \/ (n = 3)
   SQRT_EXP_2       |- !n. SQRT (n ** 2) = n
   SQRT_OF_SQ       |- !n. SQRT (n ** 2) = n
   SQRT_SQ          |- !n. SQRT (SQ n) = n
   SQRT_LE_SELF     |- !n. SQRT n <= n
   SQRT_GE_SELF     |- !n. n <= SQRT n <=> (n = 0) \/ (n = 1)
   SQRT_EQ_SELF     |- !n. (SQRT n = n) <=> (n = 0) \/ (n = 1)
   SQRT_LE_IMP      |- !n m. SQRT n <= m ==> n <= 3 * m ** 2
   SQRT_MULT_LE     |- !n m. SQRT n * SQRT m <= SQRT (n * m)
   SQRT_LT_IMP      |- !n m. SQRT n < m ==> n < m ** 2
   LT_SQRT_IMP      |- !n m. n < SQRT m ==> n ** 2 < m
   SQRT_LT_SQRT     |- !n m. SQRT n < SQRT m ==> n < m

   Square predicate:
   square_def       |- !n. square n <=> ?k. n = k * k
   square_alt       |- !n. square n <=> ?k. n = k ** 2
!  square_eqn       |- !n. square n <=> SQRT n ** 2 = n
   square_0         |- square 0
   square_1         |- square 1
   prime_non_square |- !p. prime p ==> ~square p
   SQ_SQRT_LT       |- !n. ~square n ==> SQRT n * SQRT n < n
   SQ_SQRT_LT_alt   |- !n. ~square n ==> SQRT n ** 2 < n
   odd_square_lt    |- !n m. ~square n ==> ((2 * m + 1) ** 2 < n <=> m < HALF (1 + SQRT n))

   Logarithm:
   LOG_EXACT_EXP    |- !a. 1 < a ==> !n. LOG a (a ** n) = n
   EXP_TO_LOG       |- !a b n. 1 < a /\ 0 < b /\ b <= a ** n ==> LOG a b <= n
   LOG_THM          |- !a n. 1 < a /\ 0 < n ==>
                       !p. (LOG a n = p) <=> a ** p <= n /\ n < a ** SUC p
   LOG_EVAL         |- !m n. LOG m n = if m <= 1 \/ n = 0 then LOG m n
                             else if n < m then 0 else SUC (LOG m (n DIV m))
   LOG_TEST         |- !a n. 1 < a /\ 0 < n ==>
                       !p. (LOG a n = p) <=> SUC n <= a ** SUC p /\ a ** SUC p <= a * n
   LOG_POWER        |- !b x n. 1 < b /\ 0 < x /\ 0 < n ==>
                          n * LOG b x <= LOG b (x ** n) /\
                          LOG b (x ** n) < n * SUC (LOG b x)
   LOG_LE_REVERSE   |- !a b n. 1 < a /\ 0 < n /\ a <= b ==> LOG b n <= LOG a n

#  LOG2_1              |- LOG2 1 = 0
#  LOG2_2              |- LOG2 2 = 1
   LOG2_THM            |- !n. 0 < n ==> !p. (LOG2 n = p) <=> 2 ** p <= n /\ n < 2 ** SUC p
   LOG2_PROPERTY       |- !n. 0 < n ==> 2 ** LOG2 n <= n /\ n < 2 ** SUC (LOG2 n)
   TWO_EXP_LOG2_LE     |- !n. 0 < n ==> 2 ** LOG2 n <= n
   LOG2_UNIQUE         |- !n m. 2 ** m <= n /\ n < 2 ** SUC m ==> (LOG2 n = m)
   LOG2_EQ_0           |- !n. 0 < n ==> (LOG2 n = 0 <=> n = 1)
   LOG2_EQ_1           |- !n. 0 < n ==> ((LOG2 n = 1) <=> (n = 2) \/ (n = 3))
   LOG2_LE_MONO        |- !n m. 0 < n ==> n <= m ==> LOG2 n <= LOG2 m
   LOG2_LE             |- !n m. 0 < n /\ n <= m ==> LOG2 n <= LOG2 m
   LOG2_LT             |- !n m. 0 < n /\ n < m ==> LOG2 n <= LOG2 m
   LOG2_LT_SELF        |- !n. 0 < n ==> LOG2 n < n
   LOG2_NEQ_SELF       |- !n. 0 < n ==> LOG2 n <> n
   LOG2_EQ_SELF        |- !n. (LOG2 n = n) ==> (n = 0)
#  LOG2_POS            |- !n. 1 < n ==> 0 < LOG2 n
   LOG2_TWICE_LT       |- !n. 1 < n ==> 1 < 2 * LOG2 n
   LOG2_TWICE_SQ       |- !n. 1 < n ==> 4 <= (2 * LOG2 n) ** 2
   LOG2_SUC_TWICE_SQ   |- !n. 0 < n ==> 4 <= (2 * SUC (LOG2 n)) ** 2
   LOG2_SUC_SQ         |- !n. 1 < n ==> 1 < SUC (LOG2 n) ** 2
   LOG2_SUC_TIMES_SQ_DIV_2_POS  |- !n m. 1 < m ==> 0 < SUC (LOG2 n) * (m ** 2 DIV 2)
   LOG2_2_EXP          |- !n. LOG2 (2 ** n) = n
   LOG2_EXACT_EXP      |- !n. (2 ** LOG2 n = n) <=> ?k. n = 2 ** k
   LOG2_MULT_EXP       |- !n m. 0 < n ==> (LOG2 (n * 2 ** m) = LOG2 n + m)
   LOG2_TWICE          |- !n. 0 < n ==> (LOG2 (TWICE n) = 1 + LOG2 n)
   LOG2_HALF           |- !n. 1 < n ==> (LOG2 (HALF n) = LOG2 n - 1)
   LOG2_BY_HALF        |- !n. 1 < n ==> (LOG2 n = 1 + LOG2 (HALF n))
   LOG2_DIV_EXP        |- !n m. 2 ** m < n ==> (LOG2 (n DIV 2 ** m) = LOG2 n - m)

   LOG2 Computation:
   halves_def          |- !n. halves n = if n = 0 then 0 else SUC (halves (HALF n))
   halves_alt          |- !n. halves n = if n = 0 then 0 else 1 + halves (HALF n)
#  halves_0            |- halves 0 = 0
#  halves_1            |- halves 1 = 1
#  halves_2            |- halves 2 = 2
#  halves_pos          |- !n. 0 < n ==> 0 < halves n
   halves_by_LOG2      |- !n. 0 < n ==> (halves n = 1 + LOG2 n)
   LOG2_compute        |- !n. LOG2 n = if n = 0 then LOG2 0 else halves n - 1
   halves_le           |- !m n. m <= n ==> halves m <= halves n
   halves_eq_0         |- !n. (halves n = 0) <=> (n = 0)
   halves_eq_1         |- !n. (halves n = 1) <=> (n = 1)

   Perfect Power and Power Free:
   perfect_power_def        |- !n m. perfect_power n m <=> ?e. n = m ** e
   perfect_power_self       |- !n. perfect_power n n
   perfect_power_0_m        |- !m. perfect_power 0 m <=> (m = 0)
   perfect_power_1_m        |- !m. perfect_power 1 m
   perfect_power_n_0        |- !n. perfect_power n 0 <=> (n = 0) \/ (n = 1)
   perfect_power_n_1        |- !n. perfect_power n 1 <=> (n = 1)
   perfect_power_mod_eq_0   |- !n m. 0 < m /\ 1 < n /\ n MOD m = 0 ==>
                                     (perfect_power n m <=> perfect_power (n DIV m) m)
   perfect_power_mod_ne_0   |- !n m. 0 < m /\ 1 < n /\ n MOD m <> 0 ==> ~perfect_power n m
   perfect_power_test       |- !n m. perfect_power n m <=>
                                     if n = 0 then m = 0
                                     else if n = 1 then T
                                     else if m = 0 then n <= 1
                                     else if m = 1 then n = 1
                                     else if n MOD m = 0 then perfect_power (n DIV m) m
                                     else F
   perfect_power_suc        |- !m n. 1 < m /\ perfect_power n m /\ perfect_power (SUC n) m ==>
                                     (m = 2) /\ (n = 1)
   perfect_power_not_suc    |- !m n. 1 < m /\ 1 < n /\ perfect_power n m ==> ~perfect_power (SUC n) m
   LOG_SUC                  |- !b n. 1 < b /\ 0 < n ==>
                                     LOG b (SUC n) = LOG b n +
                                         if perfect_power (SUC n) b then 1 else 0
   perfect_power_bound_LOG2 |- !n. 0 < n ==> !m. perfect_power n m <=> ?k. k <= LOG2 n /\ (n = m ** k)
   perfect_power_condition  |- !p q. prime p /\ (?x y. 0 < x /\ (p ** x = q ** y)) ==> perfect_power q p
   perfect_power_cofactor   |- !n p. 0 < p /\ p divides n ==> (perfect_power n p <=> perfect_power (n DIV p) p)
   perfect_power_cofactor_alt
                            |- !n p. 0 < n /\ p divides n ==> (perfect_power n p <=> perfect_power (n DIV p) p)
   perfect_power_2_odd      |- !n. perfect_power n 2 ==> (ODD n <=> (n = 1))

   Power Free:
   power_free_def           |- !n. power_free n <=> !m e. (n = m ** e) ==> (m = n) /\ (e = 1)
   power_free_0             |- power_free 0 <=> F
   power_free_1             |- power_free 1 <=> F
   power_free_gt_1          |- !n. power_free n ==> 1 < n
   power_free_alt           |- !n. power_free n <=> 1 < n /\ !m. perfect_power n m ==> (n = m)
   prime_is_power_free      |- !n. prime n ==> power_free n
   power_free_perfect_power |- !m n. power_free n /\ perfect_power n m ==> (n = m)
   power_free_property      |- !n. power_free n ==> !j. 1 < j ==> ROOT j n ** j <> n
   power_free_check_all     |- !n. power_free n <=> 1 < n /\ !j. 1 < j ==> ROOT j n ** j <> n

   Upper Logarithm:
   count_up_def   |- !n m k. count_up n m k = if m = 0 then 0
                                else if n <= m then k
                                else count_up n (2 * m) (SUC k)
   ulog_def       |- !n. ulog n = count_up n 1 0
#  ulog_0         |- ulog 0 = 0
#  ulog_1         |- ulog 1 = 0
#  ulog_2         |- ulog 2 = 1

   count_up_exit       |- !m n. m <> 0 /\ n <= m ==> !k. count_up n m k = k
   count_up_suc        |- !m n. m <> 0 /\ m < n ==> !k. count_up n m k = count_up n (2 * m) (SUC k)
   count_up_suc_eqn    |- !m. m <> 0 ==> !n t. 2 ** t * m < n ==>
                          !k. count_up n m k = count_up n (2 ** SUC t * m) (SUC k + t)
   count_up_exit_eqn   |- !m. m <> 0 ==> !n t. 2 ** t * m < 2 * n /\ n <= 2 ** t * m ==>
                          !k. count_up n m k = k + t
   ulog_unique         |- !m n. 2 ** m < 2 * n /\ n <= 2 ** m ==> (ulog n = m)
   ulog_eqn            |- !n. ulog n = if 1 < n then SUC (LOG2 (n - 1)) else 0
   ulog_suc            |- !n. 0 < n ==> (ulog (SUC n) = SUC (LOG2 n))
   ulog_property       |- !n. 0 < n ==> 2 ** ulog n < 2 * n /\ n <= 2 ** ulog n
   ulog_thm            |- !n. 0 < n ==> !m. (ulog n = m) <=> 2 ** m < 2 * n /\ n <= 2 ** m
   ulog_def_alt        |- (ulog 0 = 0) /\
                          !n. 0 < n ==> !m. (ulog n = m) <=> n <= 2 ** m /\ 2 ** m < TWICE n
   ulog_eq_0           |- !n. (ulog n = 0) <=> (n = 0) \/ (n = 1)
   ulog_eq_1           |- !n. (ulog n = 1) <=> (n = 2)
   ulog_le_1           |- !n. ulog n <= 1 <=> n <= 2
   ulog_le             |- !m n. n <= m ==> ulog n <= ulog m
   ulog_lt             |- !m n. n < m ==> ulog n <= ulog m
   ulog_2_exp          |- !n. ulog (2 ** n) = n
   ulog_le_self        |- !n. ulog n <= n
   ulog_eq_self        |- !n. (ulog n = n) <=> (n = 0)
   ulog_lt_self        |- !n. 0 < n ==> ulog n < n
   ulog_exp_exact      |- !n. (2 ** ulog n = n) <=> perfect_power n 2
   ulog_exp_not_exact  |- !n. ~perfect_power n 2 ==> 2 ** ulog n <> n
   ulog_property_not_exact   |- !n. 0 < n /\ ~perfect_power n 2 ==> n < 2 ** ulog n
   ulog_property_odd         |- !n. 1 < n /\ ODD n ==> n < 2 ** ulog n
   exp_to_ulog         |- !m n. n <= 2 ** m ==> ulog n <= m
#  ulog_pos            |- !n. 1 < n ==> 0 < ulog n
   ulog_ge_1           |- !n. 1 < n ==> 1 <= ulog n
   ulog_sq_gt_1        |- !n. 2 < n ==> 1 < ulog n ** 2
   ulog_twice_sq       |- !n. 1 < n ==> 4 <= TWICE (ulog n) ** 2
   ulog_alt            |- !n. ulog n = if n = 0 then 0
                              else if perfect_power n 2 then LOG2 n else SUC (LOG2 n)
   ulog_LOG2           |- !n. 0 < n ==> LOG2 n <= ulog n /\ ulog n <= 1 + LOG2 n
   perfect_power_bound_ulog
                       |- !n. 0 < n ==> !m. perfect_power n m <=> ?k. k <= ulog n /\ (n = m ** k)

   Upper Log Theorems:
   ulog_mult      |- !m n. ulog (m * n) <= ulog m + ulog n
   ulog_exp       |- !m n. ulog (m ** n) <= n * ulog m
   ulog_even      |- !n. 0 < n /\ EVEN n ==> (ulog n = 1 + ulog (HALF n))
   ulog_odd       |- !n. 1 < n /\ ODD n ==> ulog (HALF n) + 1 <= ulog n
   ulog_half      |- !n. 1 < n ==> ulog (HALF n) + 1 <= ulog n
   sqrt_upper     |- !n. SQRT n <= 2 ** ulog n

   Power Free up to a limit:
   power_free_upto_def |- !n k. n power_free_upto k <=> !j. 1 < j /\ j <= k ==> ROOT j n ** j <> n
   power_free_upto_0   |- !n. n power_free_upto 0 <=> T
   power_free_upto_1   |- !n. n power_free_upto 1 <=> T
   power_free_upto_suc |- !n k. 0 < k /\ n power_free_upto k ==>
                               (n power_free_upto k + 1 <=> ROOT (k + 1) n ** (k + 1) <> n)
   power_free_check_upto       |- !n b. LOG2 n <= b ==> (power_free n <=> 1 < n /\ n power_free_upto b)
   power_free_check_upto_LOG2  |- !n. power_free n <=> 1 < n /\ n power_free_upto LOG2 n
   power_free_check_upto_ulog  |- !n. power_free n <=> 1 < n /\ n power_free_upto ulog n
   power_free_2        |- power_free 2
   power_free_3        |- power_free 3
   power_free_test_def |- !n. power_free_test n <=> 1 < n /\ n power_free_upto ulog n
   power_free_test_eqn |- !n. power_free_test n <=> power_free n
   power_free_test_upto_LOG2   |- !n. power_free n <=>
                                      1 < n /\ !j. 1 < j /\ j <= LOG2 n ==> ROOT j n ** j <> n
   power_free_test_upto_ulog   |- !n. power_free n <=>
                                      1 < n /\ !j. 1 < j /\ j <= ulog n ==> ROOT j n ** j <> n

   Another Characterisation of Power Free:
   power_index_def      |- !n k. power_index n k =
                                      if k <= 1 then 1
                                 else if ROOT k n ** k = n then k
                                 else power_index n (k - 1)
   power_index_0        |- !n. power_index n 0 = 1
   power_index_1        |- !n. power_index n 1 = 1
   power_index_eqn      |- !n k. ROOT (power_index n k) n ** power_index n k = n
   power_index_root     |- !n k. perfect_power n (ROOT (power_index n k) n)
   power_index_of_1     |- !k. power_index 1 k = if k = 0 then 1 else k
   power_index_exact_root      |- !n k. 0 < k /\ (ROOT k n ** k = n) ==> (power_index n k = k)
   power_index_not_exact_root  |- !n k. ROOT k n ** k <> n ==> (power_index n k = power_index n (k - 1))
   power_index_no_exact_roots  |- !m n k. k <= m /\ (!j. k < j /\ j <= m ==> ROOT j n ** j <> n) ==>
                                          (power_index n m = power_index n k)
   power_index_lower    |- !m n k. k <= m /\ (ROOT k n ** k = n) ==> k <= power_index n m
   power_index_pos      |- !n k. 0 < power_index n k
   power_index_upper    |- !n k. 0 < k ==> power_index n k <= k
   power_index_equal    |- !m n k. 0 < k /\ k <= m ==>
                           ((power_index n m = power_index n k) <=> !j. k < j /\ j <= m ==> ROOT j n ** j <> n)
   power_index_property |- !m n k. (power_index n m = k) ==> !j. k < j /\ j <= m ==> ROOT j n ** j <> n

   power_free_by_power_index_LOG2
                        |- !n. power_free n <=> 1 < n /\ (power_index n (LOG2 n) = 1)
   power_free_by_power_index_ulog
                        |- !n. power_free n <=> 1 < n /\ (power_index n (ulog n) = 1)

*)

(* Rework proof of ROOT_COMPUTE in logroot theory. *)
(* ./num/extra_theories/logrootScript.sml *)

(* ROOT r n = r-th root of n.

Make use of indentity:
n ^ (1/r) = 2 (n/ 2^r) ^(1/r)

if n = 0 then 0
else (* precompute *) let x = 2 * r-th root of (n DIV (2 ** r))
     (* apply *) in if n < (SUC x) ** r then x else (SUC x)
*)

(* Theorem: 0 < r ==> (ROOT r n =
            let m = 2 * ROOT r (n DIV 2 ** r) in m + if (m + 1) ** r <= n then 1 else 0) *)
(* Proof:
     ROOT k n
   = if n < SUC m ** k then m else SUC m               by ROOT_COMPUTE
   = if SUC m ** k <= n then SUC m else m              by logic
   = if (m + 1) ** k <= n then (m + 1) else m          by ADD1
   = m + if (m + 1) ** k <= n then 1 else 0            by arithmetic
*)
val ROOT_EQN = store_thm(
  "ROOT_EQN",
  ``!r n. 0 < r ==> (ROOT r n =
         let m = 2 * ROOT r (n DIV 2 ** r) in m + if (m + 1) ** r <= n then 1 else 0)``,
  rw_tac std_ss[] >>
  Cases_on `(m + 1) ** r <= n` >-
  rw[ROOT_COMPUTE, ADD1] >>
  rw[ROOT_COMPUTE, ADD1]);

(* ------------------------------------------------------------------------- *)
(* Square Root                                                               *)
(* ------------------------------------------------------------------------- *)

(*
> EVAL ``SQRT 4``;
val it = |- SQRT 4 = 2: thm
> EVAL ``(SQRT 4) ** 2``;
val it = |- SQRT 4 ** 2 = 4: thm
> EVAL ``(SQRT 5) ** 2``;
val it = |- SQRT 5 ** 2 = 4: thm
> EVAL ``(SQRT 8) ** 2``;
val it = |- SQRT 8 ** 2 = 4: thm
> EVAL ``(SQRT 9) ** 2``;
val it = |- SQRT 9 ** 2 = 9: thm

> EVAL ``LOG2 4``;
val it = |- LOG2 4 = 2: thm
> EVAL ``2 ** (LOG2 4)``;
val it = |- 2 ** LOG2 4 = 4: thm
> EVAL ``2 ** (LOG2 5)``;
val it = |- 2 ** LOG2 5 = 4: thm
> EVAL ``2 ** (LOG2 6)``;
val it = |- 2 ** LOG2 6 = 4: thm
> EVAL ``2 ** (LOG2 7)``;
val it = |- 2 ** LOG2 7 = 4: thm
> EVAL ``2 ** (LOG2 8)``;
val it = |- 2 ** LOG2 8 = 8: thm

> EVAL ``SQRT 9``;
val it = |- SQRT 9 = 3: thm
> EVAL ``SQRT 8``;
val it = |- SQRT 8 = 2: thm
> EVAL ``SQRT 7``;
val it = |- SQRT 7 = 2: thm
> EVAL ``SQRT 6``;
val it = |- SQRT 6 = 2: thm
> EVAL ``SQRT 5``;
val it = |- SQRT 5 = 2: thm
> EVAL ``SQRT 4``;
val it = |- SQRT 4 = 2: thm
> EVAL ``SQRT 3``;
val it = |- SQRT 3 = 1: thm
*)

(*
EXP_BASE_LT_MONO |- !b. 1 < b ==> !n m. b ** m < b ** n <=> m < n
LT_EXP_ISO       |- !e a b. 1 < e ==> (a < b <=> e ** a < e ** b)

ROOT_exists      |- !r n. 0 < r ==> ?rt. rt ** r <= n /\ n < SUC rt ** r
ROOT_UNIQUE      |- !r n p. p ** r <= n /\ n < SUC p ** r ==> (ROOT r n = p)
ROOT_LE_MONO     |- !r x y. 0 < r ==> x <= y ==> ROOT r x <= ROOT r y

LOG_exists       |- ?f. !a n. 1 < a /\ 0 < n ==> a ** f a n <= n /\ n < a ** SUC (f a n)
LOG_UNIQUE       |- !a n p. a ** p <= n /\ n < a ** SUC p ==> (LOG a n = p)
LOG_LE_MONO      |- !a x y. 1 < a /\ 0 < x ==> x <= y ==> LOG a x <= LOG a y

LOG_EXP    |- !n a b. 1 < a /\ 0 < b ==> (LOG a (a ** n * b) = n + LOG a b)
LOG        |- !a n. 1 < a /\ 0 < n ==> a ** LOG a n <= n /\ n < a ** SUC (LOG a n)
*)

(* Theorem: SQ (SQRT n) <= n *)
(* Proof: by SQRT_PROPERTY, EXP_2 *)
val SQ_SQRT_LE = store_thm(
  "SQ_SQRT_LE",
  ``!n. SQ (SQRT n) <= n``,
  metis_tac[SQRT_PROPERTY, EXP_2]);

(* Extract theorem *)
Theorem SQ_SQRT_LE_alt = SQRT_PROPERTY |> SPEC_ALL |> CONJUNCT1 |> GEN_ALL;
(* val SQ_SQRT_LE_alt = |- !n. SQRT n ** 2 <= n: thm *)

(* Theorem: SQRT (SQ n) = n *)
(* Proof:
     SQRT (SQ n)
   = SQRT (n ** 2)     by EXP_2
   = n                 by SQRT_EXP_2
*)
val SQRT_SQ = store_thm(
  "SQRT_SQ",
  ``!n. SQRT (SQ n) = n``,
  metis_tac[SQRT_EXP_2, EXP_2]);

(* Theorem: SQRT n <= n *)
(* Proof:
   Note      n <= n ** 2          by SELF_LE_SQ
   Thus SQRT n <= SQRT (n ** 2)   by SQRT_LE
     or SQRT n <= n               by SQRT_EXP_2
*)
val SQRT_LE_SELF = store_thm(
  "SQRT_LE_SELF",
  ``!n. SQRT n <= n``,
  metis_tac[SELF_LE_SQ, SQRT_LE, SQRT_EXP_2]);

(* Theorem: SQRT n <= m ==> n <= 3 * (m ** 2) *)
(* Proof:
   Note n < (SUC (SQRT n)) ** 2                by SQRT_PROPERTY
          = SUC ((SQRT n) ** 2) + 2 * SQRT n   by SUC_SQ
   Thus n <= m ** 2 + 2 * m                    by SQRT n <= m
          <= m ** 2 + 2 * m ** 2               by arithmetic
           = 3 * m ** 2
*)
val SQRT_LE_IMP = store_thm(
  "SQRT_LE_IMP",
  ``!n m. SQRT n <= m ==> n <= 3 * (m ** 2)``,
  rpt strip_tac >>
  `n < (SUC (SQRT n)) ** 2` by rw[SQRT_PROPERTY] >>
  `SUC (SQRT n) ** 2 = SUC ((SQRT n) ** 2) + 2 * SQRT n` by rw[SUC_SQ] >>
  `SQRT n ** 2 <= m ** 2` by rw[] >>
  `2 * SQRT n <= 2 * m` by rw[] >>
  `2 * m <= 2 * m * m` by rw[] >>
  `2 * m * m = 2 * m ** 2` by rw[] >>
  decide_tac);

(* Theorem: (SQRT n) * (SQRT m) <= SQRT (n * m) *)
(* Proof:
   Note (SQRT n) ** 2 <= n                         by SQRT_PROPERTY
    and (SQRT m) ** 2 <= m                         by SQRT_PROPERTY
     so (SQRT n) ** 2 * (SQRT m) ** 2 <= n * m     by LE_MONO_MULT2
     or    ((SQRT n) * (SQRT m)) ** 2 <= n * m     by EXP_BASE_MULT
    ==>     (SQRT n) * (SQRT m) <= SQRT (n * m)    by SQRT_LE, SQRT_OF_SQ
*)
Theorem SQRT_MULT_LE:
  !n m. (SQRT n) * (SQRT m) <= SQRT (n * m)
Proof
  rpt strip_tac >>
  qabbrev_tac `h = SQRT n` >>
  qabbrev_tac `k = SQRT m` >>
  `h ** 2 <= n` by simp[SQRT_PROPERTY, Abbr`h`] >>
  `k ** 2 <= m` by simp[SQRT_PROPERTY, Abbr`k`] >>
  `(h * k) ** 2 <= n * m` by metis_tac[LE_MONO_MULT2, EXP_BASE_MULT] >>
  metis_tac[SQRT_LE, SQRT_OF_SQ]
QED

(* ------------------------------------------------------------------------- *)
(* Square predicate                                                          *)
(* ------------------------------------------------------------------------- *)

(* Define square predicate. *)

Definition square_def[nocompute]:
    square (n:num) = ?k. n = k * k
End
(* use [nocompute] as this is not effective. *)

(* Theorem: square n = ?k. n = k ** 2 *)
(* Proof: by square_def. *)
Theorem square_alt:
  !n. square n = ?k. n = k ** 2
Proof
  simp[square_def]
QED

(* Theorem: square n <=> (SQRT n) ** 2 = n *)
(* Proof:
   If part: square n ==> (SQRT n) ** 2 = n
      This is true         by SQRT_SQ, EXP_2
   Only-if part: (SQRT n) ** 2 = n ==> square n
      Take k = SQRT n for n = k ** 2.
*)
Theorem square_eqn[compute]:
  !n. square n <=> (SQRT n) ** 2 = n
Proof
  metis_tac[square_def, SQRT_SQ, EXP_2]
QED

(*
EVAL ``square 10``; F
EVAL ``square 16``; T
*)

(* Theorem: square 0 *)
(* Proof: by 0 = 0 * 0. *)
Theorem square_0:
  square 0
Proof
  simp[square_def]
QED

(* Theorem: square 1 *)
(* Proof: by 1 = 1 * 1. *)
Theorem square_1:
  square 1
Proof
  simp[square_def]
QED

(* Theorem: prime p ==> ~square p *)
(* Proof:
   By contradiction, suppose (square p).
   Then    p = k * k                 by square_def
   thus    k divides p               by divides_def
   so      k = 1  or  k = p          by prime_def
   If k = 1,
      then p = 1 * 1 = 1             by arithmetic
       but p <> 1                    by NOT_PRIME_1
   If k = p,
      then p * 1 = p * p             by arithmetic
        or     1 = p                 by EQ_MULT_LCANCEL, NOT_PRIME_0
       but     p <> 1                by NOT_PRIME_1
*)
Theorem prime_non_square:
  !p. prime p ==> ~square p
Proof
  rpt strip_tac >>
  `?k. p = k * k` by rw[GSYM square_def] >>
  `k divides p` by metis_tac[divides_def] >>
  `(k = 1) \/ (k = p)` by metis_tac[prime_def] >-
  fs[NOT_PRIME_1] >>
  `p * 1 = p * p` by metis_tac[MULT_RIGHT_1] >>
  `1 = p` by metis_tac[EQ_MULT_LCANCEL, NOT_PRIME_0] >>
  metis_tac[NOT_PRIME_1]
QED

(* Theorem: ~square n ==> (SQRT n) * (SQRT n) < n *)
(* Proof:
   Note (SQRT n) * (SQRT n) <= n   by SQ_SQRT_LE
    but (SQRT n) * (SQRT n) <> n   by square_def
     so (SQRT n) * (SQRT n)  < n   by inequality
*)
Theorem SQ_SQRT_LT:
  !n. ~square n ==> (SQRT n) * (SQRT n) < n
Proof
  rpt strip_tac >>
  `(SQRT n) * (SQRT n) <= n` by simp[SQ_SQRT_LE] >>
  `(SQRT n) * (SQRT n) <> n` by metis_tac[square_def] >>
  decide_tac
QED

(* Theorem: ~square n ==> SQRT n ** 2 < n *)
(* Proof: by SQ_SQRT_LT, EXP_2. *)
Theorem SQ_SQRT_LT_alt:
  !n. ~square n ==> SQRT n ** 2 < n
Proof
  metis_tac[SQ_SQRT_LT, EXP_2]
QED

(* Theorem: ~square n ==> ((2 * m + 1) ** 2 < n <=> m < HALF (1 + SQRT n)) *)
(* Proof:
   If part: (2 * m + 1) ** 2 < n ==> m < HALF (1 + SQRT n)
          (2 * m + 1) ** 2 < n
      ==> 2 * m + 1 <= SQRT n                  by SQRT_LT, SQRT_OF_SQ
      ==> 2 * (m + 1) <= 1 + SQRT n            by arithmetic
      ==>           m < HALF (1 + SQRT n)      by X_LT_DIV
   Only-if part: m < HALF (1 + SQRT n) ==> (2 * m + 1) ** 2 < n
        m < HALF (1 + SQRT n)
    <=> 2 * (m + 1) <= 1 + SQRT n              by X_LT_DIV
    <=>   2 * m + 1 <= SQRT n                  by arithmetic
    <=>  (2 * m + 1) ** 2 <= (SQRT n) ** 2     by EXP_EXP_LE_MONO
    ==>  (2 * m + 1) ** 2 <= n                 by SQ_SQRT_LE_alt
    But  n <> (2 * m + 1) ** 2                 by ~square n
     so  (2 * m + 1) ** 2 < n
*)
Theorem odd_square_lt:
  !n m. ~square n ==> ((2 * m + 1) ** 2 < n <=> m < HALF (1 + SQRT n))
Proof
  rw[EQ_IMP_THM] >| [
    `2 * m + 1 <= SQRT n` by metis_tac[SQRT_LT, SQRT_OF_SQ] >>
    `2 * (m + 1) <= 1 + SQRT n` by decide_tac >>
    fs[X_LT_DIV],
    `2 * (m + 1) <= 1 + SQRT n` by fs[X_LT_DIV] >>
    `2 * m + 1 <= SQRT n` by decide_tac >>
    `(2 * m + 1) ** 2 <= (SQRT n) ** 2` by simp[] >>
    `(SQRT n) ** 2 <= n` by fs[SQ_SQRT_LE_alt] >>
    `n <> (2 * m + 1) ** 2` by metis_tac[square_alt] >>
    decide_tac
  ]
QED

(* Theorem: 1 < m ==> 0 < SUC (LOG2 n) * (m ** 2 DIV 2) *)
(* Proof:
   Since 1 < m ==> 1 < m ** 2 DIV 2             by ONE_LT_HALF_SQ
   Hence           0 < m ** 2 DIV 2
     and           0 < 0 < SUC (LOG2 n)         by prim_recTheory.LESS_0
   Therefore 0 < SUC (LOG2 n) * (m ** 2 DIV 2)  by ZERO_LESS_MULT
*)
val LOG2_SUC_TIMES_SQ_DIV_2_POS = store_thm(
  "LOG2_SUC_TIMES_SQ_DIV_2_POS",
  ``!n m. 1 < m ==> 0 < SUC (LOG2 n) * (m ** 2 DIV 2)``,
  rpt strip_tac >>
  `1 < m ** 2 DIV 2` by rw[ONE_LT_HALF_SQ] >>
  `0 < m ** 2 DIV 2 /\ 0 < SUC (LOG2 n)` by decide_tac >>
  rw[ZERO_LESS_MULT]);

(* Theorem: 1 < n ==> LOG2 (HALF n) = (LOG2 n) - 1 *)
(* Proof:
   Note: > LOG_DIV |> SPEC ``2`` |> SPEC ``n:num``;
   val it = |- 1 < 2 /\ 2 <= n ==> LOG2 n = 1 + LOG2 (HALF n): thm
   Hence the result.
*)
val LOG2_HALF = store_thm(
  "LOG2_HALF",
  ``!n. 1 < n ==> (LOG2 (HALF n) = (LOG2 n) - 1)``,
  rpt strip_tac >>
  `LOG2 n = 1 + LOG2 (HALF n)` by rw[LOG_DIV] >>
  decide_tac);

(* Theorem: 1 < n ==> (LOG2 n = 1 + LOG2 (HALF n)) *)
(* Proof: by LOG_DIV:
> LOG_DIV |> SPEC ``2``;
val it = |- !x. 1 < 2 /\ 2 <= x ==> (LOG2 x = 1 + LOG2 (HALF x)): thm
*)
val LOG2_BY_HALF = store_thm(
  "LOG2_BY_HALF",
  ``!n. 1 < n ==> (LOG2 n = 1 + LOG2 (HALF n))``,
  rw[LOG_DIV]);

(* Theorem: 2 ** m < n ==> LOG2 (n DIV 2 ** m) = (LOG2 n) - m *)
(* Proof:
   By induction on m.
   Base: !n. 2 ** 0 < n ==> LOG2 (n DIV 2 ** 0) = LOG2 n - 0
         LOG2 (n DIV 2 ** 0)
       = LOG2 (n DIV 1)                by EXP_0
       = LOG2 n                        by DIV_1
       = LOG2 n - 0                    by SUB_0
   Step: !n. 2 ** m < n ==> LOG2 (n DIV 2 ** m) = LOG2 n - m ==>
         !n. 2 ** SUC m < n ==> LOG2 (n DIV 2 ** SUC m) = LOG2 n - SUC m
       Note 2 ** SUC m = 2 * 2 ** m       by EXP, [1]
       Thus HALF (2 * 2 ** m) <= HALF n   by DIV_LE_MONOTONE
         or            2 ** m <= HALF n   by HALF_TWICE
       If 2 ** m < HALF n,
            LOG2 (n DIV 2 ** SUC m)
          = LOG2 (n DIV (2 * 2 ** m))     by [1]
          = LOG2 ((HALF n) DIV 2 ** m)    by DIV_DIV_DIV_MULT
          = LOG2 (HALF n) - m             by induction hypothesis, 2 ** m < HALF n
          = (LOG2 n - 1) - m              by LOG2_HALF, 1 < n
          = LOG2 n - (1 + m)              by arithmetic
          = LOG2 n - SUC m                by ADD1
       Otherwise 2 ** m = HALF n,
            LOG2 (n DIV 2 ** SUC m)
          = LOG2 (n DIV (2 * 2 ** m))     by [1]
          = LOG2 ((HALF n) DIV 2 ** m)    by DIV_DIV_DIV_MULT
          = LOG2 ((HALF n) DIV (HALF n))  by 2 ** m = HALF n
          = LOG2 1                        by DIVMOD_ID, 0 < HALF n
          = 0                             by LOG2_1
            LOG2 n
          = 1 + LOG2 (HALF n)             by LOG_DIV
          = 1 + LOG2 (2 ** m)             by 2 ** m = HALF n
          = 1 + m                         by LOG2_2_EXP
          = SUC m                         by SUC_ONE_ADD
       Thus RHS = LOG2 n - SUC m = 0 = LHS.
*)

Theorem LOG2_DIV_EXP:
  !n m. 2 ** m < n ==> LOG2 (n DIV 2 ** m) = LOG2 n - m
Proof
  Induct_on ‘m’ >- rw[] >>
  rpt strip_tac >>
  ‘1 < 2 ** SUC m’ by rw[ONE_LT_EXP] >>
  ‘1 < n’ by decide_tac >>
  fs[EXP] >>
  ‘2 ** m <= HALF n’
    by metis_tac[DIV_LE_MONOTONE, HALF_TWICE, LESS_IMP_LESS_OR_EQ,
                 DECIDE “0 < 2”] >>
  ‘LOG2 (n DIV (TWICE (2 ** m))) = LOG2 ((HALF n) DIV 2 ** m)’
    by rw[DIV_DIV_DIV_MULT] >>
  fs[LESS_OR_EQ] >- rw[LOG2_HALF] >>
  ‘LOG2 n = 1 + LOG2 (HALF n)’  by rw[LOG_DIV] >>
  ‘_ = 1 + m’ by metis_tac[LOG2_2_EXP] >>
  ‘_ = SUC m’ by rw[] >>
  ‘0 < HALF n’ suffices_by rw[] >>
  metis_tac[DECIDE “0 < 2”, ZERO_LT_EXP]
QED

(* ------------------------------------------------------------------------- *)
(* LOG2 Computation                                                          *)
(* ------------------------------------------------------------------------- *)

(* Define halves n = count of HALFs of n to 0, recursively. *)
val halves_def = Define`
    halves n = if n = 0 then 0 else SUC (halves (HALF n))
`;

(* Theorem: halves n = if n = 0 then 0 else 1 + (halves (HALF n)) *)
(* Proof: by halves_def, ADD1 *)
val halves_alt = store_thm(
  "halves_alt",
  ``!n. halves n = if n = 0 then 0 else 1 + (halves (HALF n))``,
  rw[Once halves_def, ADD1]);

(* Extract theorems from definition *)
val halves_0 = save_thm("halves_0[simp]", halves_def |> SPEC ``0`` |> SIMP_RULE arith_ss[]);
(* val halves_0 = |- halves 0 = 0: thm *)
val halves_1 = save_thm("halves_1[simp]", halves_def |> SPEC ``1`` |> SIMP_RULE arith_ss[]);
(* val halves_1 = |- halves 1 = 1: thm *)
val halves_2 = save_thm("halves_2[simp]", halves_def |> SPEC ``2`` |> SIMP_RULE arith_ss[halves_1]);
(* val halves_2 = |- halves 2 = 2: thm *)

(* Theorem: 0 < n ==> 0 < halves n *)
(* Proof: by halves_def *)
val halves_pos = store_thm(
  "halves_pos[simp]",
  ``!n. 0 < n ==> 0 < halves n``,
  rw[Once halves_def]);

(* Theorem: 0 < n ==> (halves n = 1 + LOG2 n) *)
(* Proof:
   By complete induction on n.
    Assume: !m. m < n ==> 0 < m ==> (halves m = 1 + LOG2 m)
   To show: 0 < n ==> (halves n = 1 + LOG2 n)
   Note HALF n < n            by HALF_LT, 0 < n
   Need 0 < HALF n to apply induction hypothesis.
   If HALF n = 0,
      Then n = 1              by HALF_EQ_0
           halves 1
         = SUC (halves 0)     by halves_def
         = 1                  by halves_def
         = 1 + LOG2 1         by LOG2_1
   If HALF n <> 0,
      Then n <> 1                  by HALF_EQ_0
        so 1 < n                   by n <> 0, n <> 1.
           halves n
         = SUC (halves (HALF n))   by halves_def
         = SUC (1 + LOG2 (HALF n)) by induction hypothesis
         = SUC (LOG2 n)            by LOG2_BY_HALF
         = 1 + LOG2 n              by ADD1
*)
val halves_by_LOG2 = store_thm(
  "halves_by_LOG2",
  ``!n. 0 < n ==> (halves n = 1 + LOG2 n)``,
  completeInduct_on `n` >>
  strip_tac >>
  rw[Once halves_def] >>
  Cases_on `n = 1` >-
  simp[Once halves_def] >>
  `HALF n < n` by rw[HALF_LT] >>
  `HALF n <> 0` by fs[HALF_EQ_0] >>
  simp[LOG2_BY_HALF]);

(* Theorem: LOG2 n = if n = 0 then LOG2 0 else (halves n - 1) *)
(* Proof:
   If 0 < n,
      Note 0 < halves n            by halves_pos
       and halves n = 1 + LOG2 n   by halves_by_LOG2
        or LOG2 n = halves - 1.
   If n = 0, make it an infinite loop.
*)
val LOG2_compute = store_thm(
  "LOG2_compute[compute]",
  ``!n. LOG2 n = if n = 0 then LOG2 0 else (halves n - 1)``,
  rpt strip_tac >>
  (Cases_on `n = 0` >> simp[]) >>
  `0 < halves n` by rw[] >>
  `halves n = 1 + LOG2 n` by rw[halves_by_LOG2] >>
  decide_tac);

(* Put this to computeLib *)
(* val _ = computeLib.add_persistent_funs ["LOG2_compute"]; *)

(*
EVAL ``LOG2 16``; --> 4
EVAL ``LOG2 17``; --> 4
EVAL ``LOG2 32``; --> 5
EVAL ``LOG2 1024``; --> 10
EVAL ``LOG2 1023``; --> 9
*)

(* Michael's method *)
(*
Define `count_divs n = if 2 <= n then 1 + count_divs (n DIV 2) else 0`;

g `0 < n ==> (LOG2 n = count_divs n)`;
e (completeInduct_on `n`);
e strip_tac;
e (ONCE_REWRITE_TAC [theorm "count_divs_def"]);
e (Cases_on `2 <= n`);
e (mp_tac (Q.SPECL [`2`, `n`] LOG_DIV));
e (simp[]);
(* prove on-the-fly *)
e (`0 < n DIV 2` suffices_by simp[]);
(* DB.match [] ``x < k DIV n``; *)
e (simp[arithmeticTheory.X_LT_DIV]);
e (`n = 1` by simp[]);
LOG_1;
e (simp[it]);
val foo = top_thm();

g `!n. LOG2 n = if 0 < n then count_divs n else LOG2 n`;

e (rw[]);
e (simp[foo]);
e (lfs[]); ???

val bar = top_thm();
var bar = save_thm("bar", bar);
computeLib.add_persistent_funs ["bar"];
EVAL ``LOG2 16``;
EVAL ``LOG2 17``;
EVAL ``LOG2 32``;
EVAL ``LOG2 1024``;
EVAL ``LOG2 1023``;
EVAL ``LOG2 0``; -- loops!

So for n = 97,
EVAL ``LOG2 97``; --> 6
EVAL ``4 * LOG2 97 * LOG2 97``; --> 4 * 6 * 6 = 4 * 36 = 144

Need ord_r (97) > 144, r < 97, not possible ???

val count_divs_def = Define `count_divs n = if 1 < n then 1 + count_divs (n DIV 2) else 0`;

val LOG2_by_count_divs = store_thm(
  "LOG2_by_count_divs",
  ``!n. 0 < n ==> (LOG2 n = count_divs n)``,
  completeInduct_on `n` >>
  strip_tac >>
  ONCE_REWRITE_TAC[count_divs_def] >>
  rw[] >| [
    mp_tac (Q.SPECL [`2`, `n`] LOG_DIV) >>
    `2 <= n` by decide_tac >>
    `0 < n DIV 2` by rw[X_LT_DIV] >>
    simp[],
    `n = 1` by decide_tac >>
    simp[LOG_1]
  ]);

val LOG2_compute = store_thm(
  "LOG2_compute[compute]",
  ``!n. LOG2 n = if 0 < n then count_divs n else LOG2 n``,
  rw_tac std_ss[LOG2_by_count_divs]);

*)

(* Theorem: m <= n ==> halves m <= halves n *)
(* Proof:
   If m = 0,
      Then halves m = 0            by halves_0
      Thus halves m <= halves n    by 0 <= halves n
   If m <> 0,
      Then 0 < m and 0 < n   by m <= n
        so halves m = 1 + LOG2 m   by halves_by_LOG2
       and halves n = 1 + LOG2 n   by halves_by_LOG2
       and LOG2 m <= LOG2 n        by LOG2_LE
       ==> halves m <= halves n    by arithmetic
*)
val halves_le = store_thm(
  "halves_le",
  ``!m n. m <= n ==> halves m <= halves n``,
  rpt strip_tac >>
  Cases_on `m = 0` >-
  rw[] >>
  `0 < m /\ 0 < n` by decide_tac >>
  `LOG2 m <= LOG2 n` by rw[LOG2_LE] >>
  rw[halves_by_LOG2]);

(* Theorem: (halves n = 0) <=> (n = 0) *)
(* Proof: by halves_pos, halves_0 *)
val halves_eq_0 = store_thm(
  "halves_eq_0",
  ``!n. (halves n = 0) <=> (n = 0)``,
  metis_tac[halves_pos, halves_0, NOT_ZERO_LT_ZERO]);

(* Theorem: (halves n = 1) <=> (n = 1) *)
(* Proof:
   If part: halves n = 1 ==> n = 1
      By contradiction, assume n <> 1.
      Note n <> 0                   by halves_eq_0
        so 2 <= n                   by n <> 0, n <> 1
        or halves 2 <= halves n     by halves_le
       But halves 2 = 2             by halves_2
      This gives 2 <= 1, a contradiction.
   Only-if part: halves 1 = 1, true by halves_1
*)
val halves_eq_1 = store_thm(
  "halves_eq_1",
  ``!n. (halves n = 1) <=> (n = 1)``,
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  `n <> 0` by metis_tac[halves_eq_0, DECIDE``1 <> 0``] >>
  `2 <= n` by decide_tac >>
  `halves 2 <= halves n` by rw[halves_le] >>
  fs[]);

(* ------------------------------------------------------------------------- *)
(* Perfect Power                                                             *)
(* ------------------------------------------------------------------------- *)

(* Define a PerfectPower number *)
val perfect_power_def = Define`
  perfect_power (n:num) (m:num) <=> ?e. (n = m ** e)
`;

(* Overload perfect_power *)
val _ = overload_on("power_of", ``perfect_power``);
val _ = set_fixity "power_of" (Infix(NONASSOC, 450)); (* same as relation *)
(* from pretty-printing, a good idea. *)

(* Theorem: perfect_power n n *)
(* Proof:
   True since n = n ** 1   by EXP_1
*)
val perfect_power_self = store_thm(
  "perfect_power_self",
  ``!n. perfect_power n n``,
  metis_tac[perfect_power_def, EXP_1]);

(* Theorem: perfect_power 0 m <=> (m = 0) *)
(* Proof: by perfect_power_def, EXP_EQ_0 *)
val perfect_power_0_m = store_thm(
  "perfect_power_0_m",
  ``!m. perfect_power 0 m <=> (m = 0)``,
  rw[perfect_power_def, EQ_IMP_THM]);

(* Theorem: perfect_power 1 m *)
(* Proof: by perfect_power_def, take e = 0 *)
val perfect_power_1_m = store_thm(
  "perfect_power_1_m",
  ``!m. perfect_power 1 m``,
  rw[perfect_power_def] >>
  metis_tac[]);

(* Theorem: perfect_power n 0 <=> ((n = 0) \/ (n = 1)) *)
(* Proof: by perfect_power_def, ZERO_EXP. *)
val perfect_power_n_0 = store_thm(
  "perfect_power_n_0",
  ``!n. perfect_power n 0 <=> ((n = 0) \/ (n = 1))``,
  rw[perfect_power_def] >>
  metis_tac[ZERO_EXP]);

(* Theorem: perfect_power n 1 <=> (n = 1) *)
(* Proof: by perfect_power_def, EXP_1 *)
val perfect_power_n_1 = store_thm(
  "perfect_power_n_1",
  ``!n. perfect_power n 1 <=> (n = 1)``,
  rw[perfect_power_def]);

(* Theorem: 0 < m /\ 1 < n /\ (n MOD m = 0) ==>
            (perfect_power n m) <=> (perfect_power (n DIV m) m) *)
(* Proof:
   If part: perfect_power n m ==> perfect_power (n DIV m) m
      Note ?e. n = m ** e              by perfect_power_def
       and e <> 0                      by EXP_0, n <> 1
        so ?k. e = SUC k               by num_CASES
        or n = m ** SUC k
       ==> n DIV m = m ** k            by EXP_SUC_DIV
      Thus perfect_power (n DIV m) m   by perfect_power_def
   Only-if part: perfect_power (n DIV m) m ==> perfect_power n m
      Note ?e. n DIV m = m ** e        by perfect_power_def
       Now m divides n                 by DIVIDES_MOD_0, n MOD m = 0, 0 < m
       ==> n = m * (n DIV m)           by DIVIDES_EQN_COMM, 0 < m
             = m * m ** e              by above
             = m ** (SUC e)            by EXP
      Thus perfect_power n m           by perfect_power_def
*)
val perfect_power_mod_eq_0 = store_thm(
  "perfect_power_mod_eq_0",
  ``!n m. 0 < m /\ 1 < n /\ (n MOD m = 0) ==>
     ((perfect_power n m) <=> (perfect_power (n DIV m) m))``,
  rw[perfect_power_def] >>
  rw[EQ_IMP_THM] >| [
    `m ** e <> 1` by decide_tac >>
    `e <> 0` by metis_tac[EXP_0] >>
    `?k. e = SUC k` by metis_tac[num_CASES] >>
    qexists_tac `k` >>
    rw[EXP_SUC_DIV],
    `m divides n` by rw[DIVIDES_MOD_0] >>
    `n = m * (n DIV m)` by rw[GSYM DIVIDES_EQN_COMM] >>
    metis_tac[EXP]
  ]);

(* Theorem: 0 < m /\ 1 < n /\ (n MOD m <> 0) ==> ~(perfect_power n m) *)
(* Proof:
   By contradiction, assume perfect_power n m.
   Then ?e. n = m ** e      by perfect_power_def
    Now e <> 0              by EXP_0, n <> 1
     so ?k. e = SUC k       by num_CASES
        n = m ** SUC k
          = m * (m ** k)    by EXP
          = (m ** k) * m    by MULT_COMM
   Thus m divides n         by divides_def
    ==> n MOD m = 0         by DIVIDES_MOD_0
   This contradicts n MOD m <> 0.
*)
val perfect_power_mod_ne_0 = store_thm(
  "perfect_power_mod_ne_0",
  ``!n m. 0 < m /\ 1 < n /\ (n MOD m <> 0) ==> ~(perfect_power n m)``,
  rpt strip_tac >>
  fs[perfect_power_def] >>
  `n <> 1` by decide_tac >>
  `e <> 0` by metis_tac[EXP_0] >>
  `?k. e = SUC k` by metis_tac[num_CASES] >>
  `n = m * m ** k` by fs[EXP] >>
  `m divides n` by metis_tac[divides_def, MULT_COMM] >>
  metis_tac[DIVIDES_MOD_0]);

(* Theorem: perfect_power n m =
         if n = 0 then (m = 0)
         else if n = 1 then T
         else if m = 0 then (n <= 1)
         else if m = 1 then (n = 1)
         else if n MOD m = 0 then perfect_power (n DIV m) m else F *)
(* Proof:
   If n = 0, to show:
      perfect_power 0 m <=> (m = 0), true   by perfect_power_0_m
   If n = 1, to show:
      perfect_power 1 m = T, true           by perfect_power_1_m
   If m = 0, to show:
      perfect_power n 0 <=> (n <= 1), true  by perfect_power_n_0
   If m = 1, to show:
      perfect_power n 1 <=> (n = 1), true   by perfect_power_n_1
   Otherwise,
      If n MOD m = 0, to show:
      perfect_power (n DIV m) m <=> perfect_power n m, true
                                            by perfect_power_mod_eq_0
      If n MOD m <> 0, to show:
      ~perfect_power n m, true              by perfect_power_mod_ne_0
*)
val perfect_power_test = store_thm(
  "perfect_power_test",
  ``!n m. perfect_power n m =
         if n = 0 then (m = 0)
         else if n = 1 then T
         else if m = 0 then (n <= 1)
         else if m = 1 then (n = 1)
         else if n MOD m = 0 then perfect_power (n DIV m) m else F``,
  rpt strip_tac >>
  (Cases_on `n = 0` >> simp[perfect_power_0_m]) >>
  (Cases_on `n = 1` >> simp[perfect_power_1_m]) >>
  `1 < n` by decide_tac >>
  (Cases_on `m = 0` >> simp[perfect_power_n_0]) >>
  `0 < m` by decide_tac >>
  (Cases_on `m = 1` >> simp[perfect_power_n_1]) >>
  (Cases_on `n MOD m = 0` >> simp[]) >-
  rw[perfect_power_mod_eq_0] >>
  rw[perfect_power_mod_ne_0]);

(* Theorem: 1 < m /\ perfect_power n m /\ perfect_power (SUC n) m ==> (m = 2) /\ (n = 1) *)
(* Proof:
   Note ?x. n = m ** x                by perfect_power_def
    and ?y. SUC n = m ** y            by perfect_power_def
   Since n < SUC n                    by LESS_SUC
    ==>  x < y                        by EXP_BASE_LT_MONO
   Let d = y - x.
   Then 0 < d /\ (y = x + d).
   Let v = m ** d
   Note 1 < v                         by ONE_LT_EXP, 1 < m
    and m ** y = n * v                by EXP_ADD
   Let z = v - 1.
   Then 0 < z /\ (v = z + 1).
    and SUC n = n * v
              = n * (z + 1)
              = n * z + n * 1         by LEFT_ADD_DISTRIB
              = n * z + n
    ==> n * z = 1                     by ADD1
    ==> n = 1 /\ z = 1                by MULT_EQ_1
     so v = 2                         by v = z + 1

   To show: m = 2.
   By contradiction, suppose m <> 2.
   Then      2 < m                    by 1 < m, m <> 2
    ==> 2 ** y < m ** y               by EXP_EXP_LT_MONO
               = n * v = 2 = 2 ** 1   by EXP_1
    ==>      y < 1                    by EXP_BASE_LT_MONO
   Thus y = 0, but y <> 0 by x < y,
   leading to a contradiction.
*)

Theorem perfect_power_suc:
  !m n. 1 < m /\ perfect_power n m /\ perfect_power (SUC n) m ==>
        m = 2 /\ n = 1
Proof
  ntac 3 strip_tac >>
  `?x. n = m ** x` by fs[perfect_power_def] >>
  `?y. SUC n = m ** y` by fs[GSYM perfect_power_def] >>
  `n < SUC n` by decide_tac >>
  `x < y` by metis_tac[EXP_BASE_LT_MONO] >>
  qabbrev_tac `d = y - x` >>
  `0 < d /\ (y = x + d)` by fs[Abbr`d`] >>
  qabbrev_tac `v = m ** d` >>
  `m ** y = n * v` by fs[EXP_ADD, Abbr`v`] >>
  `1 < v` by rw[ONE_LT_EXP, Abbr`v`] >>
  qabbrev_tac `z = v - 1` >>
  `0 < z /\ (v = z + 1)` by fs[Abbr`z`] >>
  `n * v = n * z + n * 1` by rw[] >>
  `n * z = 1` by decide_tac >>
  `n = 1 /\ z = 1` by metis_tac[MULT_EQ_1] >>
  `v = 2` by decide_tac >>
  simp[] >>
  spose_not_then strip_assume_tac >>
  `2 < m` by decide_tac >>
  `2 ** y < m ** y` by simp[EXP_EXP_LT_MONO] >>
  `m ** y = 2` by decide_tac >>
  `2 ** y < 2 ** 1` by metis_tac[EXP_1] >>
  `y < 1` by fs[EXP_BASE_LT_MONO] >>
  decide_tac
QED

(* Theorem: 1 < m /\ 1 < n /\ perfect_power n m ==> ~perfect_power (SUC n) m *)
(* Proof:
   By contradiction, suppose perfect_power (SUC n) m.
   Then n = 1        by perfect_power_suc
   This contradicts 1 < n.
*)
val perfect_power_not_suc = store_thm(
  "perfect_power_not_suc",
  ``!m n. 1 < m /\ 1 < n /\ perfect_power n m ==> ~perfect_power (SUC n) m``,
  spose_not_then strip_assume_tac >>
  `n = 1` by metis_tac[perfect_power_suc] >>
  decide_tac);

(* Theorem: 1 < b /\ 0 < n ==>
           (LOG b (SUC n) = LOG b n + if perfect_power (SUC n) b then 1 else 0) *)
(* Proof:
   Let x = LOG b n, y = LOG b (SUC n).  x <= y
   Note SUC n <= b ** SUC x /\ b ** SUC x <= b * n            by LOG_TEST
    and SUC (SUC n) <= b ** SUC y /\ b ** SUC y <= b * SUC n  by LOG_TEST, 0 < SUC n

   If SUC n = b ** SUC x,
      Then perfect_power (SUC n) b       by perfect_power_def
       and y = LOG b (SUC n)
             = LOG b (b ** SUC x)
             = SUC x                     by LOG_EXACT_EXP
             = x + 1                     by ADD1
      hence true.
   Otherwise, SUC n < b ** SUC x,
      Then SUC (SUC n) <= b ** SUC x     by SUC n < b ** SUC x
       and b * n < b * SUC n             by LT_MULT_LCANCEL, n < SUC n
      Thus b ** SUC x <= b * n < b * SUC n
        or y = x                         by LOG_TEST
      Claim: ~perfect_power (SUC n) b
      Proof: By contradiction, suppose perfect_power (SUC n) b.
             Then ?e. SUC n = b ** e.
             Thus y = LOG b (SUC n)
                    = LOG b (b ** e)     by LOG_EXACT_EXP
                    = e
              ==> b * n < b * SUC n
                        = b * b ** e     by SUC n = b ** e
                        = b ** SUC e     by EXP
                        = b ** SUC x     by e = y = x
              This contradicts b ** SUC x <= b * n
      With ~perfect_power (SUC n) b, hence true.
*)

Theorem LOG_SUC:
  !b n. 1 < b /\ 0 < n ==>
    (LOG b (SUC n) = LOG b n + if perfect_power (SUC n) b then 1 else 0)
Proof
  rpt strip_tac >>
  qabbrev_tac ‘x = LOG b n’ >>
  qabbrev_tac ‘y = LOG b (SUC n)’ >>
  ‘0 < SUC n’ by decide_tac >>
  ‘SUC n <= b ** SUC x /\ b ** SUC x <= b * n’ by metis_tac[LOG_TEST] >>
  ‘SUC (SUC n) <= b ** SUC y /\ b ** SUC y <= b * SUC n’
    by metis_tac[LOG_TEST] >>
  ‘(SUC n = b ** SUC x) \/ (SUC n < b ** SUC x)’ by decide_tac >| [
    ‘perfect_power (SUC n) b’ by metis_tac[perfect_power_def] >>
    ‘y = SUC x’ by rw[LOG_EXACT_EXP, Abbr‘y’] >>
    simp[],
    ‘SUC (SUC n) <= b ** SUC x’ by decide_tac >>
    ‘b * n < b * SUC n’ by rw[] >>
    ‘b ** SUC x <= b * SUC n’ by decide_tac >>
    ‘y = x’ by metis_tac[LOG_TEST] >>
    ‘~perfect_power (SUC n) b’
      by (spose_not_then strip_assume_tac >>
          `?e. SUC n = b ** e` by fs[perfect_power_def] >>
          `y = e` by (simp[Abbr`y`] >> fs[] >> rfs[LOG_EXACT_EXP]) >>
          `b * n < b ** SUC x` by metis_tac[EXP] >>
          decide_tac) >>
    simp[]
  ]
QED

(*
LOG_SUC;
|- !b n. 1 < b /\ 0 < n ==> LOG b (SUC n) = LOG b n + if perfect_power (SUC n) b then 1 else 0
Let v = LOG b n.

   v       v+1.      v+2.     v+3.
   -----------------------------------------------
   b       b ** 2        b ** 3             b ** 4

> EVAL ``MAP (LOG 2) [1 .. 20]``;
val it = |- MAP (LOG 2) [1 .. 20] =
      [0; 1; 1; 2; 2; 2; 2; 3; 3; 3; 3; 3; 3; 3; 3; 4; 4; 4; 4; 4]: thm
       1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 20
*)

(* Theorem: 0 < n ==> !m. perfect_power n m <=> ?k. k <= LOG2 n /\ (n = m ** k) *)
(* Proof:
   If part: perfect_power n m ==> ?k. k <= LOG2 n /\ (n = m ** k)
      Given perfect_power n m, ?e. (n = m ** e)    by perfect_power_def
      If n = 1,
         Then LOG2 1 = 0                           by LOG2_1
         Take k = 0, then 1 = m ** 0               by EXP_0
      If n <> 1, so e <> 0                         by EXP
                and m <> 1                         by EXP_1
       also n <> 0, so m <> 0                      by ZERO_EXP
      Therefore 2 <= m
            ==> 2 ** e <= m ** e                   by EXP_BASE_LE_MONO, 1 < 2
            But n < 2 ** (SUC (LOG2 n))            by LOG2_PROPERTY, 0 < n
        or 2 ** e < 2 ** (SUC (LOG2 n))
        hence   e < SUC (LOG2 n)                   by EXP_BASE_LT_MONO, 1 < 2
        i.e.    e <= LOG2 n
   Only-if part: ?k. k <= LOG2 n /\ (n = m ** k) ==> perfect_power n m
      True by perfect_power_def.
*)
val perfect_power_bound_LOG2 = store_thm(
  "perfect_power_bound_LOG2",
  ``!n. 0 < n ==> !m. perfect_power n m <=> ?k. k <= LOG2 n /\ (n = m ** k)``,
  rw[EQ_IMP_THM] >| [
    Cases_on `n = 1` >-
    simp[] >>
    `?e. (n = m ** e)` by rw[GSYM perfect_power_def] >>
    `n <> 0 /\ 1 < n /\ 1 < 2` by decide_tac >>
    `e <> 0` by metis_tac[EXP] >>
    `m <> 1` by metis_tac[EXP_1] >>
    `m <> 0` by metis_tac[ZERO_EXP] >>
    `2 <= m` by decide_tac >>
    `2 ** e <= n` by rw[EXP_BASE_LE_MONO] >>
    `n < 2 ** (SUC (LOG2 n))` by rw[LOG2_PROPERTY] >>
    `e < SUC (LOG2 n)` by metis_tac[EXP_BASE_LT_MONO, LESS_EQ_LESS_TRANS] >>
    `e <= LOG2 n` by decide_tac >>
    metis_tac[],
    metis_tac[perfect_power_def]
  ]);

(* Theorem: prime p /\ (?x y. 0 < x /\ (p ** x = q ** y)) ==> perfect_power q p *)
(* Proof:
   Note ?k. (q = p ** k)     by power_eq_prime_power, prime p, 0 < x
   Thus perfect_power q p    by perfect_power_def
*)
val perfect_power_condition = store_thm(
  "perfect_power_condition",
  ``!p q. prime p /\ (?x y. 0 < x /\ (p ** x = q ** y)) ==> perfect_power q p``,
  metis_tac[power_eq_prime_power, perfect_power_def]);

(* Theorem: 0 < p /\ p divides n ==> (perfect_power n p <=> perfect_power (n DIV p) p) *)
(* Proof:
   Let q = n DIV p.
   Then n = p * q                   by DIVIDES_EQN_COMM, 0 < p
   If part: perfect_power n p ==> perfect_power q p
      Note ?k. n = p ** k           by perfect_power_def
      If k = 0,
         Then p * q = p ** 0 = 1    by EXP
          ==> p = 1 and q = 1       by MULT_EQ_1
           so perfect_power q p     by perfect_power_self
      If k <> 0, k = SUC h for some h.
         Then p * q = p ** SUC h
                    = p * p ** h    by EXP
           or     q = p ** h        by MULT_LEFT_CANCEL, p <> 0
           so perfect_power q p     by perfect_power_self

   Only-if part: perfect_power q p ==> perfect_power n p
      Note ?k. q = p ** k           by perfect_power_def
         so n = p * q = p ** SUC k  by EXP
       thus perfect_power n p       by perfect_power_def
*)
val perfect_power_cofactor = store_thm(
  "perfect_power_cofactor",
  ``!n p. 0 < p /\ p divides n ==> (perfect_power n p <=> perfect_power (n DIV p) p)``,
  rpt strip_tac >>
  qabbrev_tac `q = n DIV p` >>
  `n = p * q` by rw[GSYM DIVIDES_EQN_COMM, Abbr`q`] >>
  simp[EQ_IMP_THM] >>
  rpt strip_tac >| [
    `?k. p * q = p ** k` by rw[GSYM perfect_power_def] >>
    Cases_on `k` >| [
      `(p = 1) /\ (q = 1)` by metis_tac[MULT_EQ_1, EXP] >>
      metis_tac[perfect_power_self],
      `q = p ** n'` by metis_tac[EXP, MULT_LEFT_CANCEL, NOT_ZERO_LT_ZERO] >>
      metis_tac[perfect_power_def]
    ],
    `?k. q = p ** k` by rw[GSYM perfect_power_def] >>
    `p * q = p ** SUC k` by rw[EXP] >>
    metis_tac[perfect_power_def]
  ]);

(* Theorem: 0 < n /\ p divides n ==> (perfect_power n p <=> perfect_power (n DIV p) p) *)
(* Proof:
   Note 0 < p           by ZERO_DIVIDES, 0 < n
   The result follows   by perfect_power_cofactor
*)
val perfect_power_cofactor_alt = store_thm(
  "perfect_power_cofactor_alt",
  ``!n p. 0 < n /\ p divides n ==> (perfect_power n p <=> perfect_power (n DIV p) p)``,
  rpt strip_tac >>
  `0 < p` by metis_tac[ZERO_DIVIDES, NOT_ZERO] >>
  qabbrev_tac `q = n DIV p` >>
  rw[perfect_power_cofactor]);

(* Theorem: perfect_power n 2 ==> (ODD n <=> (n = 1)) *)
(* Proof:
   If part: perfect_power n 2 /\ ODD n ==> n = 1
      By contradiction, suppose n <> 1.
      Note ?k. n = 2 ** k     by perfect_power_def
      Thus k <> 0             by EXP
        so ?h. k = SUC h      by num_CASES
           n = 2 ** (SUC h)   by above
             = 2 * 2 ** h     by EXP
       ==> EVEN n             by EVEN_DOUBLE
      This contradicts ODD n  by EVEN_ODD
   Only-if part: perfect_power n 2 /\ n = 1 ==> ODD n
      This is true              by ODD_1
*)
val perfect_power_2_odd = store_thm(
  "perfect_power_2_odd",
  ``!n. perfect_power n 2 ==> (ODD n <=> (n = 1))``,
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  `?k. n = 2 ** k` by rw[GSYM perfect_power_def] >>
  `k <> 0` by metis_tac[EXP] >>
  `?h. k = SUC h` by metis_tac[num_CASES] >>
  `n = 2 * 2 ** h` by rw[EXP] >>
  metis_tac[EVEN_DOUBLE, EVEN_ODD]);

(* ------------------------------------------------------------------------- *)
(* Power Free                                                                *)
(* ------------------------------------------------------------------------- *)

(* Define a PowerFree number: a trivial perfect power *)
val power_free_def = zDefine`
   power_free (n:num) <=> !m e. (n = m ** e) ==> (m = n) /\ (e = 1)
`;
(* Use zDefine as this is not computationally effective. *)

(* Theorem: power_free 0 = F *)
(* Proof:
   Note 0 ** 2 = 0         by ZERO_EXP
   Thus power_free 0 = F   by power_free_def
*)
val power_free_0 = store_thm(
  "power_free_0",
  ``power_free 0 = F``,
  rw[power_free_def]);

(* Theorem: power_free 1 = F *)
(* Proof:
   Note 0 ** 0 = 1         by ZERO_EXP
   Thus power_free 1 = F   by power_free_def
*)
val power_free_1 = store_thm(
  "power_free_1",
  ``power_free 1 = F``,
  rw[power_free_def]);

(* Theorem: power_free n ==> 1 < n *)
(* Proof:
   By contradiction, suppose n = 0 or n = 1.
   Then power_free 0 = F     by power_free_0
    and power_free 1 = F     by power_free_1
*)
val power_free_gt_1 = store_thm(
  "power_free_gt_1",
  ``!n. power_free n ==> 1 < n``,
  metis_tac[power_free_0, power_free_1, DECIDE``1 < n <=> (n <> 0 /\ n <> 1)``]);

(* Theorem: power_free n <=> 1 < n /\ (!m. perfect_power n m ==> (n = m)) *)
(* Proof:
   If part: power_free n ==> 1 < n /\ (!m. perfect_power n m ==> (n = m))
      Note power_free n
       ==> 1 < n                by power_free_gt_1
       Now ?e. n = m ** e       by perfect_power_def
       ==> n = m                by power_free_def

   Only-if part: 1 < n /\ (!m. perfect_power n m ==> (n = m)) ==> power_free n
      By power_free_def, this is to show:
         (n = m ** e) ==> (m = n) /\ (e = 1)
      Note perfect_power n m    by perfect_power_def, ?e.
       ==> m = n                by implication
        so n = n ** e           by given, m = n
       ==> e = 1                by POWER_EQ_SELF
*)
Theorem power_free_alt:
  power_free n <=> 1 < n /\ !m. perfect_power n m ==> n = m
Proof
  rw[EQ_IMP_THM]
  >- rw[power_free_gt_1]
  >- fs[power_free_def, perfect_power_def] >>
  fs[power_free_def, perfect_power_def, PULL_EXISTS] >>
  rpt strip_tac >>
  first_x_assum $ drule_then strip_assume_tac >> gs[]
QED

(* Theorem: prime n ==> power_free n *)
(* Proof:
   Let n = m ** e. To show that n is power_free,
   (1) show m = n, by squeezing m as a factor of prime n.
   (2) show e = 1, by applying prime_powers_eq
   This is a typical detective-style proof.

   Note prime n ==> n <> 1               by NOT_PRIME_1

   Claim: !m e. n = m ** e ==> m = n
   Proof: Note m <> 1                    by EXP_1, n <> 1
           and e <> 0                    by EXP, n <> 1
          Thus e = SUC k for some k      by num_CASES
               n = m ** SUC k
                 = m * (m ** k)          by EXP
                 = (m ** k) * m          by MULT_COMM
          Thus m divides n,              by divides_def
           But m <> 1, so m = n          by prime_def

   The claim satisfies half of the power_free_def.
   With m = n, prime m,
    and e <> 0                           by EXP, n <> 1
   Thus n = n ** 1 = m ** e              by EXP_1
    ==> e = 1                            by prime_powers_eq, 0 < e.
*)
val prime_is_power_free = store_thm(
  "prime_is_power_free",
  ``!n. prime n ==> power_free n``,
  rpt strip_tac >>
  `n <> 1` by metis_tac[NOT_PRIME_1] >>
  `!m e. (n = m ** e) ==> (m = n)` by
  (rpt strip_tac >>
  `m <> 1` by metis_tac[EXP_1] >>
  metis_tac[EXP, num_CASES, MULT_COMM, divides_def, prime_def]) >>
  `!m e. (n = m ** e) ==> (e = 1)` by metis_tac[EXP, EXP_1, prime_powers_eq, NOT_ZERO_LT_ZERO] >>
  metis_tac[power_free_def]);

(* Theorem: power_free n /\ perfect_power n m ==> (n = m) *)
(* Proof:
   Note ?e. n = m ** e        by perfect_power_def
    ==> n = m                 by power_free_def
*)
val power_free_perfect_power = store_thm(
  "power_free_perfect_power",
  ``!m n. power_free n /\ perfect_power n m ==> (n = m)``,
  metis_tac[perfect_power_def, power_free_def]);

(* Theorem: power_free n ==> (!j. 1 < j ==> (ROOT j n) ** j <> n) *)
(* Proof:
   By contradiction, suppose (ROOT j n) ** j = n.
   Then j = 1                 by power_free_def
   This contradicts 1 < j.
*)
val power_free_property = store_thm(
  "power_free_property",
  ``!n. power_free n ==> (!j. 1 < j ==> (ROOT j n) ** j <> n)``,
  spose_not_then strip_assume_tac >>
  `j = 1` by metis_tac[power_free_def] >>
  decide_tac);

(* We have:
power_free_0   |- power_free 0 <=> F
power_free_1   |- power_free 1 <=> F
So, given 1 < n, how to check power_free n ?
*)

(* Theorem: power_free n <=> 1 < n /\ (!j. 1 < j ==> (ROOT j n) ** j <> n) *)
(* Proof:
   If part: power_free n ==> 1 < n /\ (!j. 1 < j ==> (ROOT j n) ** j <> n)
      Note 1 < n                       by power_free_gt_1
      The rest is true                 by power_free_property.
   Only-if part: 1 < n /\ (!j. 1 < j ==> (ROOT j n) ** j <> n) ==> power_free n
      By contradiction, assume ~(power_free n).
      That is, ?m e. n = m ** e /\ (m = m ** e ==> e <> 1)   by power_free_def
      Note 1 < m /\ 0 < e             by ONE_LT_EXP, 1 < n
      Thus ROOT e n = m               by ROOT_POWER, 1 < m, 0 < e
      By the implication, ~(1 < e), or e <= 1.
      Since 0 < e, this shows e = 1.
      Then m = m ** e                 by EXP_1
      This gives e <> 1, a contradiction.
*)
val power_free_check_all = store_thm(
  "power_free_check_all",
  ``!n. power_free n <=> 1 < n /\ (!j. 1 < j ==> (ROOT j n) ** j <> n)``,
  rw[EQ_IMP_THM] >-
  rw[power_free_gt_1] >-
  rw[power_free_property] >>
  simp[power_free_def] >>
  spose_not_then strip_assume_tac >>
  `1 < m /\ 0 < e` by metis_tac[ONE_LT_EXP] >>
  `ROOT e n = m` by rw[ROOT_POWER] >>
  `~(1 < e)` by metis_tac[] >>
  `e = 1` by decide_tac >>
  rw[]);

(* However, there is no need to check all the exponents:
  just up to (LOG2 n) or (ulog n) is sufficient.
  See earlier part with power_free_upto_def. *)

(* ------------------------------------------------------------------------- *)
(* Upper Logarithm                                                           *)
(* ------------------------------------------------------------------------- *)

(* Find the power of 2 more or equal to n *)
Definition count_up_def:
  count_up n m k =
       if m = 0 then 0 (* just to provide m <> 0 for the next one *)
  else if n <= m then k else count_up n (2 * m) (SUC k)
Termination WF_REL_TAC `measure (λ(n, m, k). n - m)`
End

(* Define upper LOG2 n by count_up *)
val ulog_def = Define`
    ulog n = count_up n 1 0
`;

(*
> EVAL ``ulog 1``; --> 0
> EVAL ``ulog 2``; --> 1
> EVAL ``ulog 3``; --> 2
> EVAL ``ulog 4``; --> 2
> EVAL ``ulog 5``; --> 3
> EVAL ``ulog 6``; --> 3
> EVAL ``ulog 7``; --> 3
> EVAL ``ulog 8``; --> 3
> EVAL ``ulog 9``; --> 4
*)

(* Theorem: ulog 0 = 0 *)
(* Proof:
     ulog 0
   = count_up 0 1 0    by ulog_def
   = 0                 by count_up_def, 0 <= 1
*)
val ulog_0 = store_thm(
  "ulog_0[simp]",
  ``ulog 0 = 0``,
  rw[ulog_def, Once count_up_def]);

(* Theorem: ulog 1 = 0 *)
(* Proof:
     ulog 1
   = count_up 1 1 0    by ulog_def
   = 0                 by count_up_def, 1 <= 1
*)
val ulog_1 = store_thm(
  "ulog_1[simp]",
  ``ulog 1 = 0``,
  rw[ulog_def, Once count_up_def]);

(* Theorem: ulog 2 = 1 *)
(* Proof:
     ulog 2
   = count_up 2 1 0    by ulog_def
   = count_up 2 2 1    by count_up_def, ~(1 < 2)
   = 1                 by count_up_def, 2 <= 2
*)
val ulog_2 = store_thm(
  "ulog_2[simp]",
  ``ulog 2 = 1``,
  rw[ulog_def, Once count_up_def] >>
  rw[Once count_up_def]);

(* Theorem: m <> 0 /\ n <= m ==> !k. count_up n m k = k *)
(* Proof: by count_up_def *)
val count_up_exit = store_thm(
  "count_up_exit",
  ``!m n. m <> 0 /\ n <= m ==> !k. count_up n m k = k``,
  rw[Once count_up_def]);

(* Theorem: m <> 0 /\ m < n ==> !k. count_up n m k = count_up n (2 * m) (SUC k) *)
(* Proof: by count_up_def *)
val count_up_suc = store_thm(
  "count_up_suc",
  ``!m n. m <> 0 /\ m < n ==> !k. count_up n m k = count_up n (2 * m) (SUC k)``,
  rw[Once count_up_def]);

(* Theorem: m <> 0 ==>
            !t. 2 ** t * m < n ==> !k. count_up n m k = count_up n (2 ** (SUC t) * m) ((SUC k) + t) *)
(* Proof:
   By induction on t.
   Base: 2 ** 0 * m < n ==> !k. count_up n m k = count_up n (2 ** SUC 0 * m) (SUC k + 0)
      Simplifying, this is to show:
          m < n ==> !k. count_up n m k = count_up n (2 * m) (SUC k)
      which is true by count_up_suc.
   Step: 2 ** t * m < n ==> !k. count_up n m k = count_up n (2 ** SUC t * m) (SUC k + t) ==>
         2 ** SUC t * m < n ==> !k. count_up n m k = count_up n (2 ** SUC (SUC t) * m) (SUC k + SUC t)
      Note 2 ** SUC t <> 0        by EXP_EQ_0, 2 <> 0
        so 2 ** SUC t * m <> 0    by MULT_EQ_0, m <> 0
       and 2 ** SUC t * m
         = 2 * 2 ** t * m         by EXP
         = 2 * (2 ** t * m)       by MULT_ASSOC
      Thus (2 ** t * m) < n       by MULT_LT_IMP_LT, 0 < 2
         count_up n m k
       = count_up n (2 ** SUC t * m) (SUC k + t)             by induction hypothesis
       = count_up n (2 * (2 ** SUC t * m)) (SUC (SUC k + t)) by count_up_suc
       = count_up n (2 ** SUC (SUC t) * m) (SUC k + SUC t)   by EXP, ADD1
*)
val count_up_suc_eqn = store_thm(
  "count_up_suc_eqn",
  ``!m. m <> 0 ==>
   !n t. 2 ** t * m < n ==> !k. count_up n m k = count_up n (2 ** (SUC t) * m) ((SUC k) + t)``,
  ntac 3 strip_tac >>
  Induct >-
  rw[count_up_suc] >>
  rpt strip_tac >>
  qabbrev_tac `q = 2 ** t * m` >>
  `2 ** SUC t <> 0` by metis_tac[EXP_EQ_0, DECIDE``2 <> 0``] >>
  `2 ** SUC t * m <> 0` by metis_tac[MULT_EQ_0] >>
  `2 ** SUC t * m = 2 * q` by rw_tac std_ss[EXP, MULT_ASSOC, Abbr`q`] >>
  `q < n` by rw[MULT_LT_IMP_LT] >>
  rw[count_up_suc, EXP, ADD1]);

(* Theorem: m <> 0 ==> !n t. 2 ** t * m < 2 * n /\ n <= 2 ** t * m ==> !k. count_up n m k = k + t *)
(* Proof:
   If t = 0,
      Then n <= m           by EXP
        so count_up n m k
         = k                by count_up_exit
         = k + 0            by ADD_0
   If t <> 0,
      Then ?s. t = SUC s            by num_CASES
      Note 2 ** t * m
         = 2 ** SUC s * m           by above
         = 2 * 2 ** s * m           by EXP
         = 2 * (2 ** s * m)         by MULT_ASSOC
      Note 2 ** SUC s * m < 2 * n   by given
        so   (2 ** s * m) < n       by LT_MULT_RCANCEL, 2 <> 0

        count_up n m k
      = count_up n (2 ** t * m) ((SUC k) + t)   by count_up_suc_eqn
      = (SUC k) + t                             by count_up_exit
*)
val count_up_exit_eqn = store_thm(
  "count_up_exit_eqn",
  ``!m. m <> 0 ==> !n t. 2 ** t * m < 2 * n /\ n <= 2 ** t * m ==> !k. count_up n m k = k + t``,
  rpt strip_tac >>
  Cases_on `t` >-
  fs[count_up_exit] >>
  qabbrev_tac `q = 2 ** n' * m` >>
  `2 ** SUC n' * m = 2 * q` by rw_tac std_ss[EXP, MULT_ASSOC, Abbr`q`] >>
  `q < n` by decide_tac >>
  `count_up n m k = count_up n (2 ** (SUC n') * m) ((SUC k) + n')` by rw[count_up_suc_eqn, Abbr`q`] >>
  `_ = (SUC k) + n'` by rw[count_up_exit] >>
  rw[]);

(* Theorem: 2 ** m < 2 * n /\ n <= 2 ** m ==> (ulog n = m) *)
(* Proof:
   Put m = 1 in count_up_exit_eqn:
       2 ** t * 1 < 2 * n /\ n <= 2 ** t * 1 ==> !k. count_up n 1 k = k + t
   Put k = 0, and apply MULT_RIGHT_1, ADD:
       2 ** t * 1 < 2 * n /\ n <= 2 ** t * 1 ==> count_up n 1 0 = t
   Then apply ulog_def to get the result, and rename t by m.
*)
val ulog_unique = store_thm(
  "ulog_unique",
  ``!m n. 2 ** m < 2 * n /\ n <= 2 ** m ==> (ulog n = m)``,
  metis_tac[ulog_def, count_up_exit_eqn, MULT_RIGHT_1, ADD, DECIDE``1 <> 0``]);

(* Theorem: ulog n = if 1 < n then SUC (LOG2 (n - 1)) else 0 *)
(* Proof:
   If 1 < n,
      Then 0 < n - 1      by 1 < n
       ==> 2 ** LOG2 (n - 1) <= (n - 1) /\
           (n - 1) < 2 ** SUC (LOG2 (n - 1))      by LOG2_PROPERTY
        or 2 ** LOG2 (n - 1) < n /\
           n <= 2 ** SUC (LOG2 (n - 1))           by shifting inequalities
       Let t = SUC (LOG2 (n - 1)).
       Then 2 ** t = 2 * 2 ** (LOG2 (n - 1))      by EXP
                   < 2 * n                        by LT_MULT_LCANCEL, 2 ** LOG2 (n - 1) < n
       Thus ulog n = t                            by ulog_unique.
   If ~(1 < n),
      Then n <= 1, or n = 0 or n = 1.
      If n = 0, ulog n = 0                        by ulog_0
      If n = 1, ulog n = 0                        by ulog_1
*)
val ulog_eqn = store_thm(
  "ulog_eqn",
  ``!n. ulog n = if 1 < n then SUC (LOG2 (n - 1)) else 0``,
  rw[] >| [
    `0 < n - 1` by decide_tac >>
    `2 ** LOG2 (n - 1) <= (n - 1) /\ (n - 1) < 2 ** SUC (LOG2 (n - 1))` by metis_tac[LOG2_PROPERTY] >>
    `2 * 2 ** LOG2 (n - 1) < 2 * n /\ n <= 2 ** SUC (LOG2 (n - 1))` by decide_tac >>
    rw[EXP, ulog_unique],
    metis_tac[ulog_0, ulog_1, DECIDE``~(1 < n) <=> (n = 0) \/ (n = 1)``]
  ]);

(* Theorem: 0 < n ==> (ulog (SUC n) = SUC (LOG2 n)) *)
(* Proof:
   Note 0 < n ==> 1 < SUC n      by LT_ADD_RCANCEL, ADD1
   Thus ulog (SUC n)
      = SUC (LOG2 (SUC n - 1))   by ulog_eqn
      = SUC (LOG2 n)             by SUC_SUB1
*)
val ulog_suc = store_thm(
  "ulog_suc",
  ``!n. 0 < n ==> (ulog (SUC n) = SUC (LOG2 n))``,
  rpt strip_tac >>
  `1 < SUC n` by decide_tac >>
  rw[ulog_eqn]);

(* Theorem: 0 < n ==> 2 ** (ulog n) < 2 * n /\ n <= 2 ** (ulog n) *)
(* Proof:
   Apply ulog_eqn, this is to show:
   (1) 1 < n ==> 2 ** SUC (LOG2 (n - 1)) < 2 * n
       Let m = n - 1.
       Note 0 < m                   by 1 < n
        ==> 2 ** LOG2 m <= m        by TWO_EXP_LOG2_LE, 0 < m
         or             <= n - 1    by notation
       Thus 2 ** LOG2 m < n         by inequality [1]
        and 2 ** SUC (LOG2 m)
          = 2 * 2 ** (LOG2 m)       by EXP
          < 2 * n                   by LT_MULT_LCANCEL, [1]
   (2) 1 < n ==> n <= 2 ** SUC (LOG2 (n - 1))
       Let m = n - 1.
       Note 0 < m                          by 1 < n
        ==> m < 2 ** SUC (LOG2 m)          by LOG2_PROPERTY, 0 < m
        n - 1 < 2 ** SUC (LOG2 m)          by notation
            n <= 2 ** SUC (LOG2 m)         by inequality [2]
         or n <= 2 ** SUC (LOG2 (n - 1))   by notation
*)
val ulog_property = store_thm(
  "ulog_property",
  ``!n. 0 < n ==> 2 ** (ulog n) < 2 * n /\ n <= 2 ** (ulog n)``,
  rw[ulog_eqn] >| [
    `0 < n - 1` by decide_tac >>
    qabbrev_tac `m = n - 1` >>
    `2 ** SUC (LOG2 m) = 2 * 2 ** (LOG2 m)` by rw[EXP] >>
    `2 ** LOG2 m <= n - 1` by rw[TWO_EXP_LOG2_LE, Abbr`m`] >>
    decide_tac,
    `0 < n - 1` by decide_tac >>
    qabbrev_tac `m = n - 1` >>
    `2 ** SUC (LOG2 m) = 2 * 2 ** (LOG2 m)` by rw[EXP] >>
    `n - 1 < 2 ** SUC (LOG2 m)` by metis_tac[LOG2_PROPERTY] >>
    decide_tac
  ]);

(* Theorem: 0 < n ==> !m. (ulog n = m) <=> 2 ** m < 2 * n /\ n <= 2 ** m *)
(* Proof:
   If part: 0 < n ==> 2 ** (ulog n) < 2 * n /\ n <= 2 ** (ulog n)
      True by ulog_property, 0 < n
   Only-if part: 2 ** m < 2 * n /\ n <= 2 ** m ==> ulog n = m
      True by ulog_unique
*)
val ulog_thm = store_thm(
  "ulog_thm",
  ``!n. 0 < n ==> !m. (ulog n = m) <=> (2 ** m < 2 * n /\ n <= 2 ** m)``,
  metis_tac[ulog_property, ulog_unique]);

(* Theorem: (ulog 0 = 0) /\ !n. 0 < n ==> !m. (ulog n = m) <=> (n <= 2 ** m /\ 2 ** m < 2 * n) *)
(* Proof: by ulog_0 ulog_thm *)
Theorem ulog_def_alt:
  (ulog 0 = 0) /\
  !n. 0 < n ==> !m. (ulog n = m) <=> (n <= 2 ** m /\ 2 ** m < 2 * n)
Proof rw[ulog_0, ulog_thm]
QED

(* Theorem: (ulog n = 0) <=> ((n = 0) \/ (n = 1)) *)
(* Proof:
   Note !n. SUC n <> 0                   by NOT_SUC
     so if 1 < n, ulog n <> 0            by ulog_eqn
   Thus ulog n = 0 <=> ~(1 < n)          by above
     or            <=> n <= 1            by negation
     or            <=> n = 0 or n = 1    by range
*)
val ulog_eq_0 = store_thm(
  "ulog_eq_0",
  ``!n. (ulog n = 0) <=> ((n = 0) \/ (n = 1))``,
  rw[ulog_eqn]);

(* Theorem: (ulog n = 1) <=> (n = 2) *)
(* Proof:
   If part: ulog n = 1 ==> n = 2
      Note n <> 0 and n <> 1             by ulog_eq_0
      Thus 1 < n, or 0 < n - 1           by arithmetic
       ==> SUC (LOG2 (n - 1)) = 1        by ulog_eqn, 1 < n
        or      LOG2 (n - 1) = 0         by SUC_EQ, ONE
       ==>            n - 1 < 2          by LOG_EQ_0, 0 < n - 1
        or                n <= 2         by inequality
      Combine with 1 < n, n = 2.
   Only-if part: ulog 2 = 1
         ulog 2
       = ulog (SUC 1)                    by TWO
       = SUC (LOG2 1)                    by ulog_suc
       = SUC 0                           by LOG_1, 0 < 2
       = 1                               by ONE
*)
val ulog_eq_1 = store_thm(
  "ulog_eq_1",
  ``!n. (ulog n = 1) <=> (n = 2)``,
  rw[EQ_IMP_THM] >>
  `n <> 0 /\ n <> 1` by metis_tac[ulog_eq_0, DECIDE``1 <> 0``] >>
  `1 < n /\ 0 < n - 1` by decide_tac >>
  `SUC (LOG2 (n - 1)) = 1` by metis_tac[ulog_eqn] >>
  `LOG2 (n - 1) = 0` by decide_tac >>
  `n - 1 < 2` by metis_tac[LOG_EQ_0, DECIDE``1 < 2``] >>
  decide_tac);

(* Theorem: ulog n <= 1 <=> n <= 2 *)
(* Proof:
       ulog n <= 1
   <=> ulog n = 0 \/ ulog n = 1   by arithmetic
   <=> n = 0 \/ n = 1 \/ n = 2    by ulog_eq_0, ulog_eq_1
   <=> n <= 2                     by arithmetic

*)
val ulog_le_1 = store_thm(
  "ulog_le_1",
  ``!n. ulog n <= 1 <=> n <= 2``,
  rpt strip_tac >>
  `ulog n <= 1 <=> ((ulog n = 0) \/ (ulog n = 1))` by decide_tac >>
  rw[ulog_eq_0, ulog_eq_1]);

(* Theorem: n <= m ==> ulog n <= ulog m *)
(* Proof:
   If n = 0,
      Note ulog 0 = 0      by ulog_0
      and 0 <= ulog m      for anything
   If n = 1,
      Note ulog 1 = 0      by ulog_1
      Thus 0 <= ulog m     by arithmetic
   If n <> 1, then 1 < n
      Note n <= m, so 1 < m
      Thus 0 < n - 1       by arithmetic
       and n - 1 <= m - 1  by arithmetic
       ==> LOG2 (n - 1) <= LOG2 (m - 1)              by LOG2_LE
       ==> SUC (LOG2 (n - 1)) <= SUC (LOG2 (m - 1))  by LESS_EQ_MONO
        or          ulog n <= ulog m                 by ulog_eqn, 1 < n, 1 < m
*)
val ulog_le = store_thm(
  "ulog_le",
  ``!m n. n <= m ==> ulog n <= ulog m``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  Cases_on `n = 1` >-
  rw[] >>
  rw[ulog_eqn, LOG2_LE]);

(* Theorem: n < m ==> ulog n <= ulog m *)
(* Proof: by ulog_le *)
val ulog_lt = store_thm(
  "ulog_lt",
  ``!m n. n < m ==> ulog n <= ulog m``,
  rw[ulog_le]);

(* Theorem: ulog (2 ** n) = n *)
(* Proof:
   Note 0 < 2 ** n             by EXP_POS, 0 < 2
   From 1 < 2                  by arithmetic
    ==> 2 ** n < 2 * 2 ** n    by LT_MULT_RCANCEL, 0 < 2 ** n
    Now 2 ** n <= 2 ** n       by LESS_EQ_REFL
   Thus ulog (2 ** n) = n      by ulog_unique
*)
val ulog_2_exp = store_thm(
  "ulog_2_exp",
  ``!n. ulog (2 ** n) = n``,
  rpt strip_tac >>
  `0 < 2 ** n` by rw[EXP_POS] >>
  `2 ** n < 2 * 2 ** n` by decide_tac >>
  `2 ** n <= 2 ** n` by decide_tac >>
  rw[ulog_unique]);

(* Theorem: ulog n <= n *)
(* Proof:
   Note      n < 2 ** n          by X_LT_EXP_X
   Thus ulog n <= ulog (2 ** n)  by ulog_lt
     or ulog n <= n              by ulog_2_exp
*)
val ulog_le_self = store_thm(
  "ulog_le_self",
  ``!n. ulog n <= n``,
  metis_tac[X_LT_EXP_X, ulog_lt, ulog_2_exp, DECIDE``1 < 2n``]);

(* Theorem: ulog n = n <=> n = 0 *)
(* Proof:
   If part: ulog n = n ==> n = 0
      By contradiction, assume n <> 0
      Then ?k. n = SUC k            by num_CASES, n < 0
        so  2 ** SUC k < 2 * SUC k  by ulog_property
        or  2 * 2 ** k < 2 * SUC k  by EXP
       ==>      2 ** k < SUC k      by arithmetic
        or      2 ** k <= k         by arithmetic
      This contradicts k < 2 ** k   by X_LT_EXP_X, 0 < 2
   Only-if part: ulog 0 = 0
      This is true                  by ulog_0
*)
val ulog_eq_self = store_thm(
  "ulog_eq_self",
  ``!n. (ulog n = n) <=> (n = 0)``,
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  `?k. n = SUC k` by metis_tac[num_CASES] >>
  `2 * (2 ** k) = 2 ** SUC k` by rw[EXP] >>
  `0 < n` by decide_tac >>
  `2 ** SUC k < 2 * SUC k` by metis_tac[ulog_property] >>
  `2 ** k <= k` by decide_tac >>
  `k < 2 ** k` by rw[X_LT_EXP_X] >>
  decide_tac);

(* Theorem: 0 < n ==> ulog n < n *)
(* Proof:
   By contradiction, assume ~(ulog n < n).
   Then n <= ulog n      by ~(ulog n < n)
    But ulog n <= n      by ulog_le_self
    ==> ulog n = n       by arithmetic
     so n = 0            by ulog_eq_self
   This contradicts 0 < n.
*)
val ulog_lt_self = store_thm(
  "ulog_lt_self",
  ``!n. 0 < n ==> ulog n < n``,
  rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  `ulog n <= n` by rw[ulog_le_self] >>
  `ulog n = n` by decide_tac >>
  `n = 0` by rw[GSYM ulog_eq_self] >>
  decide_tac);

(* Theorem: (2 ** (ulog n) = n) <=> perfect_power n 2 *)
(* Proof:
   Using perfect_power_def,
   If part: 2 ** (ulog n) = n ==> ?e. n = 2 ** e
      True by taking e = ulog n.
   Only-if part: 2 ** ulog (2 ** e) = 2 ** e
      This is true by ulog_2_exp
*)
val ulog_exp_exact = store_thm(
  "ulog_exp_exact",
  ``!n. (2 ** (ulog n) = n) <=> perfect_power n 2``,
  rw[perfect_power_def, EQ_IMP_THM] >-
  metis_tac[] >>
  rw[ulog_2_exp]);

(* Theorem: ~(perfect_power n 2) ==> 2 ** ulog n <> n *)
(* Proof: by ulog_exp_exact. *)
val ulog_exp_not_exact = store_thm(
  "ulog_exp_not_exact",
  ``!n. ~(perfect_power n 2) ==> 2 ** ulog n <> n``,
  rw[ulog_exp_exact]);

(* Theorem: 0 < n /\ ~(perfect_power n 2) ==> n < 2 ** ulog n *)
(* Proof:
   Note n <= 2 ** ulog n    by ulog_property, 0 < n
    But n <> 2 ** ulog n    by ulog_exp_not_exact, ~(perfect_power n 2)
   Thus  n < 2 ** ulog n    by LESS_OR_EQ
*)
val ulog_property_not_exact = store_thm(
  "ulog_property_not_exact",
  ``!n. 0 < n /\ ~(perfect_power n 2) ==> n < 2 ** ulog n``,
  metis_tac[ulog_property, ulog_exp_not_exact, LESS_OR_EQ]);

(* Theorem: 1 < n /\ ODD n ==> n < 2 ** ulog n *)
(* Proof:
   Note 0 < n /\ n <> 1        by 1 < n
   Thus n <= 2 ** ulog n       by ulog_property, 0 < n
    But ~(perfect_power n 2)   by perfect_power_2_odd, n <> 1
    ==> n <> 2 ** ulog n       by ulog_exp_not_exact, ~(perfect_power n 2)
   Thus n < 2 ** ulog n        by LESS_OR_EQ
*)
val ulog_property_odd = store_thm(
  "ulog_property_odd",
  ``!n. 1 < n /\ ODD n ==> n < 2 ** ulog n``,
  rpt strip_tac >>
  `0 < n /\ n <> 1` by decide_tac >>
  `n <= 2 ** ulog n` by metis_tac[ulog_property] >>
  `~(perfect_power n 2)` by metis_tac[perfect_power_2_odd] >>
  `2 ** ulog n <> n` by rw[ulog_exp_not_exact] >>
  decide_tac);

(* Theorem: n <= 2 ** m ==> ulog n <= m *)
(* Proof:
      n <= 2 ** m
   ==> ulog n <= ulog (2 ** m)    by ulog_le
   ==> ulog n <= m                by ulog_2_exp
*)
val exp_to_ulog = store_thm(
  "exp_to_ulog",
  ``!m n. n <= 2 ** m ==> ulog n <= m``,
  metis_tac[ulog_le, ulog_2_exp]);

(* Theorem: 1 < n ==> 0 < ulog n *)
(* Proof:
   Note 1 < n ==> n <> 0 /\ n <> 1     by arithmetic
     so ulog n <> 0                    by ulog_eq_0
     or 0 < ulog n                     by NOT_ZERO_LT_ZERO
*)
val ulog_pos = store_thm(
  "ulog_pos[simp]",
  ``!n. 1 < n ==> 0 < ulog n``,
  metis_tac[ulog_eq_0, NOT_ZERO, DECIDE``1 < n <=> n <> 0 /\ n <> 1``]);

(* Theorem: 1 < n ==> 1 <= ulog n *)
(* Proof:
   Note  0 < ulog n      by ulog_pos
   Thus  1 <= ulog n     by arithmetic
*)
val ulog_ge_1 = store_thm(
  "ulog_ge_1",
  ``!n. 1 < n ==> 1 <= ulog n``,
  metis_tac[ulog_pos, DECIDE``0 < n ==> 1 <= n``]);

(* Theorem: 2 < n ==> 1 < (ulog n) ** 2 *)
(* Proof:
   Note 1 < n /\ n <> 2      by 2 < n
     so 0 < ulog n           by ulog_pos, 1 < n
    and ulog n <> 1          by ulog_eq_1, n <> 2
   Thus 1 < ulog n           by ulog n <> 0, ulog n <> 1
     so 1 < (ulog n) ** 2    by ONE_LT_EXP, 0 < 2
*)
val ulog_sq_gt_1 = store_thm(
  "ulog_sq_gt_1",
  ``!n. 2 < n ==> 1 < (ulog n) ** 2``,
  rpt strip_tac >>
  `1 < n /\ n <> 2` by decide_tac >>
  `0 < ulog n` by rw[] >>
  `ulog n <> 1` by rw[ulog_eq_1] >>
  `1 < ulog n` by decide_tac >>
  rw[ONE_LT_EXP]);

(* Theorem: 1 < n ==> 4 <= (2 * ulog n) ** 2 *)
(* Proof:
   Note  0 < ulog n               by ulog_pos, 1 < n
   Thus  2 <= 2 * ulog n          by arithmetic
     or  4 <= (2 * ulog n) ** 2   by EXP_BASE_LE_MONO
*)
val ulog_twice_sq = store_thm(
  "ulog_twice_sq",
  ``!n. 1 < n ==> 4 <= (2 * ulog n) ** 2``,
  rpt strip_tac >>
  `0 < ulog n` by rw[ulog_pos] >>
  `2 <= 2 * ulog n` by decide_tac >>
  `2 ** 2 <= (2 * ulog n) ** 2` by rw[EXP_BASE_LE_MONO] >>
  `2 ** 2 = 4` by rw[] >>
  decide_tac);

(* Theorem: ulog n = if n = 0 then 0
                else if (perfect_power n 2) then (LOG2 n) else SUC (LOG2 n) *)
(* Proof:
   This is to show:
   (1) ulog 0 = 0, true            by ulog_0
   (2) perfect_power n 2 ==> ulog n = LOG2 n
       Note ?k. n = 2 ** k         by perfect_power_def
       Thus ulog n = k             by ulog_exp_exact
        and LOG2 n = k             by LOG_EXACT_EXP, 1 < 2
   (3) ~(perfect_power n 2) ==> ulog n = SUC (LOG2 n)
       Let m = SUC (LOG2 n).
       Then 2 ** m
          = 2 * 2 ** (LOG2 n)      by EXP
          <= 2 * n                 by TWO_EXP_LOG2_LE
       But n <> LOG2 n             by LOG2_EXACT_EXP, ~(perfect_power n 2)
       Thus 2 ** m < 2 * n         [1]

       Also n < 2 ** m             by LOG2_PROPERTY
       Thus n <= 2 ** m,           [2]
       giving ulog n = m           by ulog_unique, [1] [2]
*)
val ulog_alt = store_thm(
  "ulog_alt",
  ``!n. ulog n = if n = 0 then 0
                else if (perfect_power n 2) then (LOG2 n) else SUC (LOG2 n)``,
  rw[] >-
  metis_tac[perfect_power_def, ulog_exp_exact, LOG_EXACT_EXP, DECIDE``1 < 2``] >>
  qabbrev_tac `m = SUC (LOG2 n)` >>
  (irule ulog_unique >> rpt conj_tac) >| [
    `2 ** m = 2 * 2 ** (LOG2 n)` by rw[EXP, Abbr`m`] >>
    `2 ** (LOG2 n) <= n` by rw[TWO_EXP_LOG2_LE] >>
    `2 ** (LOG2 n) <> n` by rw[LOG2_EXACT_EXP, GSYM perfect_power_def] >>
    decide_tac,
    `n < 2 ** m` by rw[LOG2_PROPERTY, Abbr`m`] >>
    decide_tac
  ]);

(*
Thus, for 0 < n, (ulog n) and SUC (LOG2 n) differ only for (perfect_power n 2).
This means that replacing AKS bounds of SUC (LOG2 n) by (ulog n)
only affect calculations involving (perfect_power n 2),
which are irrelevant for primality testing !
However, in display, (ulog n) is better, while SUC (LOG2 n) is a bit ugly.
*)

(* Theorem: 0 < n ==> (LOG2 n <= ulog n /\ ulog n <= 1 + LOG2 n) *)
(* Proof: by ulog_alt *)
val ulog_LOG2 = store_thm(
  "ulog_LOG2",
  ``!n. 0 < n ==> (LOG2 n <= ulog n /\ ulog n <= 1 + LOG2 n)``,
  rw[ulog_alt]);

(* Theorem: 0 < n ==> !m. perfect_power n m <=> ?k. k <= ulog n /\ (n = m ** k) *)
(* Proof: by perfect_power_bound_LOG2, ulog_LOG2 *)
val perfect_power_bound_ulog = store_thm(
  "perfect_power_bound_ulog",
  ``!n. 0 < n ==> !m. perfect_power n m <=> ?k. k <= ulog n /\ (n = m ** k)``,
  rw[EQ_IMP_THM] >| [
    `LOG2 n <= ulog n` by rw[ulog_LOG2] >>
    metis_tac[perfect_power_bound_LOG2, LESS_EQ_TRANS],
    metis_tac[perfect_power_def]
  ]);

(* ------------------------------------------------------------------------- *)
(* Upper Log Theorems                                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: ulog (m * n) <= ulog m + ulog n *)
(* Proof:
   Let x = ulog (m * n), y = ulog m + ulog n.
   Note    m * n <= 2 ** x      < 2 * m * n      by ulog_thm
    and        m <= 2 ** ulog m < 2 * m          by ulog_thm
    and        n <= 2 ** ulog n < 2 * n          by ulog_thm
   Note that 2 ** ulog m * 2 ** ulog n = 2 ** y  by EXP_ADD
   Multiplying inequalities,
           m * n <= 2 ** y                 by LE_MONO_MULT2
                    2 ** y < 4 * m * n     by LT_MONO_MULT2
    The picture is:
           m * n  ....... 2 * m * n ....... 4 * m * n
                   2 ** x somewhere
                          2 ** y somewhere
    If 2 ** y < 2 * m * n,
       Then x = y                          by ulog_unique
    Otherwise,
       2 ** y is in the second range.
    Then    2 ** x < 2 ** y                since 2 ** x in the first
      or         x < y                     by EXP_BASE_LT_MONO
    Combining these two cases: x <= y.
*)
val ulog_mult = store_thm(
  "ulog_mult",
  ``!m n. ulog (m * n) <= ulog m + ulog n``,
  rpt strip_tac >>
  Cases_on `(m = 0) \/ (n = 0)` >-
  fs[] >>
  `m * n <> 0` by rw[] >>
  `0 < m /\ 0 < n /\ 0 < m * n` by decide_tac >>
  qabbrev_tac `x = ulog (m * n)` >>
  qabbrev_tac `y = ulog m + ulog n` >>
  `m * n <= 2 ** x /\ 2 ** x < TWICE (m * n)` by metis_tac[ulog_thm] >>
  `m * n <= 2 ** y /\ 2 ** y < (TWICE m) * (TWICE n)` by metis_tac[ulog_thm, LE_MONO_MULT2, LT_MONO_MULT2, EXP_ADD] >>
  Cases_on `2 ** y < TWICE (m * n)` >| [
    `y = x` by metis_tac[ulog_unique] >>
    decide_tac,
    `2 ** x < 2 ** y /\ 1 < 2` by decide_tac >>
    `x < y` by metis_tac[EXP_BASE_LT_MONO] >>
    decide_tac
  ]);

(* Theorem: ulog (m ** n) <= n * ulog m *)
(* Proof:
   By induction on n.
   Base: ulog (m ** 0) <= 0 * ulog m
      LHS = ulog (m ** 0)
          = ulog 1            by EXP_0
          = 0                 by ulog_1
          <= 0 * ulog m       by MULT
          = RHS
   Step: ulog (m ** n) <= n * ulog m ==> ulog (m ** SUC n) <= SUC n * ulog m
      LHS = ulog (m ** SUC n)
          = ulog (m * m ** n)          by EXP
          <= ulog m + ulog (m ** n)    by ulog_mult
          <= ulog m + n * ulog m       by induction hypothesis
           = (1 + n) * ulog m          by RIGHT_ADD_DISTRIB
           = SUC n * ulog m            by ADD1, ADD_COMM
           = RHS
*)
val ulog_exp = store_thm(
  "ulog_exp",
  ``!m n. ulog (m ** n) <= n * ulog m``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[EXP_0] >>
  `ulog (m ** SUC n) <= ulog m + ulog (m ** n)` by rw[EXP, ulog_mult] >>
  `ulog m + ulog (m ** n) <= ulog m + n * ulog m` by rw[] >>
  `ulog m + n * ulog m = SUC n * ulog m` by rw[ADD1] >>
  decide_tac);

(* Theorem: 0 < n /\ EVEN n ==> (ulog n = 1 + ulog (HALF n)) *)
(* Proof:
   Let k = HALF n.
   Then 0 < k                                      by HALF_EQ_0, EVEN n
    and EVEN n ==> n = TWICE k                     by EVEN_HALF
   Note        n <= 2 ** ulog n < 2 * n            by ulog_thm, by 0 < n
    and        k <= 2 ** ulog k < 2 * k            by ulog_thm, by 0 < k
    so     2 * k <= 2 * 2 ** ulog k < 2 * 2 * k    by multiplying 2
    or         n <= 2 ** (1 + ulog k) < 2 * n      by EXP
  Thus     ulog n = 1 + ulog k                     by ulog_unique
*)
val ulog_even = store_thm(
  "ulog_even",
  ``!n. 0 < n /\ EVEN n ==> (ulog n = 1 + ulog (HALF n))``,
  rpt strip_tac >>
  qabbrev_tac `k = HALF n` >>
  `n = TWICE k` by rw[EVEN_HALF, Abbr`k`] >>
  `0 < k` by rw[Abbr`k`] >>
  `n <= 2 ** ulog n /\ 2 ** ulog n < 2 * n` by metis_tac[ulog_thm] >>
  `k <= 2 ** ulog k /\ 2 ** ulog k < 2 * k` by metis_tac[ulog_thm] >>
  `2 <> 0` by decide_tac >>
  `n <= 2 * 2 ** ulog k` by rw[LE_MULT_LCANCEL] >>
  `2 * 2 ** ulog k < 2 * n` by rw[LT_MULT_LCANCEL] >>
  `2 * 2 ** ulog k = 2 ** (1 + ulog k)` by metis_tac[EXP, ADD1, ADD_COMM] >>
  metis_tac[ulog_unique]);

(* Theorem: 1 < n /\ ODD n ==> ulog (HALF n) + 1 <= ulog n *)
(* Proof:
   Let k = HALF n.
   Then 0 < k                                      by HALF_EQ_0, 1 < n
    and ODD n ==> n = TWICE k + 1                  by ODD_HALF
   Note        n <= 2 ** ulog n < 2 * n            by ulog_thm, by 0 < n
    and        k <= 2 ** ulog k < 2 * k            by ulog_thm, by 0 < k
    so     2 * k <= 2 * 2 ** ulog k < 2 * 2 * k    by multiplying 2
    or     (2 * k) <= 2 ** (1 + ulog k) < 2 * (2 * k)  by EXP
  Since    2 * k < n, so 2 * (2 * k) < 2 * n,
  the picture is:
           2 * k ... n ...... 2 * (2 * k) ... 2 * n
                       <---  2 ** ulog n ---->
                 <--- 2 ** (1 + ulog k) -->
  If n <= 2 ** (1 + ulog k), then ulog n = 1 + ulog k    by ulog_unique
  Otherwise, 2 ** (1 + ulog k) < 2 ** ulog n
         so         1 + ulog k < ulog n            by EXP_BASE_LT_MONO, 1 < 2
  Combining, 1 + ulog k <= ulog n.
*)
val ulog_odd = store_thm(
  "ulog_odd",
  ``!n. 1 < n /\ ODD n ==> ulog (HALF n) + 1 <= ulog n``,
  rpt strip_tac >>
  qabbrev_tac `k = HALF n` >>
  `(n <> 0) /\ (n <> 1)` by decide_tac >>
  `0 < n /\ 0 < k` by metis_tac[HALF_EQ_0, NOT_ZERO_LT_ZERO] >>
  `n = TWICE k + 1` by rw[ODD_HALF, Abbr`k`] >>
  `n <= 2 ** ulog n /\ 2 ** ulog n < 2 * n` by metis_tac[ulog_thm] >>
  `k <= 2 ** ulog k /\ 2 ** ulog k < 2 * k` by metis_tac[ulog_thm] >>
  `2 <> 0 /\ 1 < 2` by decide_tac >>
  `2 * k <= 2 * 2 ** ulog k` by rw[LE_MULT_LCANCEL] >>
  `2 * 2 ** ulog k < 2 * (2 * k)` by rw[LT_MULT_LCANCEL] >>
  `2 * 2 ** ulog k = 2 ** (1 + ulog k)` by metis_tac[EXP, ADD1, ADD_COMM] >>
  Cases_on `n <= 2 ** (1 + ulog k)` >| [
    `2 * k < n` by decide_tac >>
    `2 * (2 * k) < 2 * n` by rw[LT_MULT_LCANCEL] >>
    `2 ** (1 + ulog k) < TWICE n` by decide_tac >>
    `1 + ulog k = ulog n` by metis_tac[ulog_unique] >>
    decide_tac,
    `2 ** (1 + ulog k) < 2 ** ulog n` by decide_tac >>
    `1 + ulog k < ulog n` by metis_tac[EXP_BASE_LT_MONO] >>
    decide_tac
  ]);

(*
EVAL ``let n = 13 in [ulog (HALF n) + 1; ulog n]``;
|- (let n = 13 in [ulog (HALF n) + 1; ulog n]) = [4; 4]:
|- (let n = 17 in [ulog (HALF n) + 1; ulog n]) = [4; 5]:
*)

(* Theorem: 1 < n ==> ulog (HALF n) + 1 <= ulog n *)
(* Proof:
   Note 1 < n ==> 0 < n   by arithmetic
   If EVEN n, true        by ulog_even, 0 < n
   If ODD n, true         by ulog_odd, 1 < n, ODD_EVEN.
*)
val ulog_half = store_thm(
  "ulog_half",
  ``!n. 1 < n ==> ulog (HALF n) + 1 <= ulog n``,
  rpt strip_tac >>
  Cases_on `EVEN n` >-
  rw[ulog_even] >>
  rw[ODD_EVEN, ulog_odd]);

(* Theorem: SQRT n <= 2 ** (ulog n) *)
(* Proof:
   Note      n <= 2 ** ulog n     by ulog_property
    and SQRT n <= n               by SQRT_LE_SELF
   Thus SQRT n <= 2 ** ulog n     by LESS_EQ_TRANS
     or SQRT n <=
*)
val sqrt_upper = store_thm(
  "sqrt_upper",
  ``!n. SQRT n <= 2 ** (ulog n)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  `n <= 2 ** ulog n` by rw[ulog_property] >>
  `SQRT n <= n` by rw[SQRT_LE_SELF] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Power Free up to a limit                                                  *)
(* ------------------------------------------------------------------------- *)

(* Define a power free property of a number *)
val power_free_upto_def = Define`
    power_free_upto n k <=> !j. 1 < j /\ j <= k ==> (ROOT j n) ** j <> n
`;
(* make this an infix relation. *)
val _ = set_fixity "power_free_upto" (Infix(NONASSOC, 450)); (* same as relation *)

(* Theorem: (n power_free_upto 0) = T *)
(* Proof: by power_free_upto_def, no counter-example. *)
val power_free_upto_0 = store_thm(
  "power_free_upto_0",
  ``!n. (n power_free_upto 0) = T``,
  rw[power_free_upto_def]);

(* Theorem: (n power_free_upto 1) = T *)
(* Proof: by power_free_upto_def, no counter-example. *)
val power_free_upto_1 = store_thm(
  "power_free_upto_1",
  ``!n. (n power_free_upto 1) = T``,
  rw[power_free_upto_def]);

(* Theorem: 0 < k /\ (n power_free_upto k) ==>
            ((n power_free_upto (k + 1)) <=> ROOT (k + 1) n ** (k + 1) <> n) *)
(* Proof: by power_free_upto_def *)
val power_free_upto_suc = store_thm(
  "power_free_upto_suc",
  ``!n k. 0 < k /\ (n power_free_upto k) ==>
         ((n power_free_upto (k + 1)) <=> ROOT (k + 1) n ** (k + 1) <> n)``,
  rw[power_free_upto_def] >>
  rw[EQ_IMP_THM] >>
  metis_tac[LESS_OR_EQ, DECIDE``k < n + 1 ==> k <= n``]);

(* Theorem: LOG2 n <= b ==> (power_free n <=> (1 < n /\ n power_free_upto b)) *)
(* Proof:
   If part: LOG2 n <= b /\ power_free n ==> 1 < n /\ n power_free_upto b
      (1) 1 < n,
          By contradiction, suppose n <= 1.
          Then n = 0, but power_free 0 = F      by power_free_0
            or n = 1, but power_free 1 = F      by power_free_1
      (2) n power_free_upto b,
          By power_free_upto_def, this is to show:
             1 < j /\ j <= b ==> ROOT j n ** j <> n
          By contradiction, suppose ROOT j n ** j = n.
          Then n = m ** j   where m = ROOT j n, with j <> 1.
          This contradicts power_free n         by power_free_def

   Only-if part: 1 < n /\ LOG2 n <= b /\ n power_free_upto b ==> power_free n
      By contradiction, suppose ~(power_free n).
      Then ?e. n = m ** e  with n = m ==> e <> 1   by power_free_def
       ==> perfect_power n m                    by perfect_power_def
      Thus ?k. k <= LOG2 n /\ (n = m ** k)      by perfect_power_bound_LOG2, 0 < n
       Now k <> 0                               by EXP_0, n <> 1
        so m = ROOT k n                         by ROOT_FROM_POWER, k <> 0

      Claim: k <> 1
      Proof: Note m <> 0                        by ROOT_EQ_0, n <> 0
              and m <> 1                        by EXP_1, k <> 0, n <> 1
              ==> 1 < m                         by m <> 0, m <> 1
             Thus n = m ** e = m ** k ==> k = e by EXP_BASE_INJECTIVE
              But e <> 1
                  since e = 1 ==> n <> m,       by n = m ==> e <> 1
                    yet n = m ** 1 ==> n = m    by EXP_1
             Since k = e, k <> 1.

      Therefore 1 < k                           by k <> 0, k <> 1
      and k <= LOG2 n /\ LOG2 n <= b ==> k <= b by arithmetic
      With 1 < k /\ k <= b /\ m = ROOT k n /\ m ** k = n,
      These will give a contradiction           by power_free_upto_def
*)
val power_free_check_upto = store_thm(
  "power_free_check_upto",
  ``!n b. LOG2 n <= b ==> (power_free n <=> (1 < n /\ n power_free_upto b))``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `(n = 0) \/ (n = 1)` by decide_tac >-
    fs[power_free_0] >>
    fs[power_free_1],
    rw[power_free_upto_def] >>
    spose_not_then strip_assume_tac >>
    `j <> 1` by decide_tac >>
    metis_tac[power_free_def],
    simp[power_free_def] >>
    spose_not_then strip_assume_tac >>
    `perfect_power n m` by metis_tac[perfect_power_def] >>
    `0 < n /\ n <> 1` by decide_tac >>
    `?k. k <= LOG2 n /\ (n = m ** k)` by rw[GSYM perfect_power_bound_LOG2] >>
    `k <> 0` by metis_tac[EXP_0] >>
    `m = ROOT k n` by rw[ROOT_FROM_POWER] >>
    `k <> 1` by
  (`m <> 0` by rw[ROOT_EQ_0] >>
    `m <> 1 /\ e <> 1` by metis_tac[EXP_1] >>
    `1 < m` by decide_tac >>
    metis_tac[EXP_BASE_INJECTIVE]) >>
    `1 < k` by decide_tac >>
    `k <= b` by decide_tac >>
    metis_tac[power_free_upto_def]
  ]);

(* Theorem: power_free n <=> (1 < n /\ n power_free_upto LOG2 n) *)
(* Proof: by power_free_check_upto, LOG2 n <= LOG2 n *)
val power_free_check_upto_LOG2 = store_thm(
  "power_free_check_upto_LOG2",
  ``!n. power_free n <=> (1 < n /\ n power_free_upto LOG2 n)``,
  rw[power_free_check_upto]);

(* Theorem: power_free n <=> (1 < n /\ n power_free_upto ulog n) *)
(* Proof:
   If n = 0,
      LHS = power_free 0 = F        by power_free_0
          = RHS, as 1 < 0 = F
   If n <> 0,
      Then LOG2 n <= ulog n         by ulog_LOG2, 0 < n
      The result follows            by power_free_check_upto
*)
val power_free_check_upto_ulog = store_thm(
  "power_free_check_upto_ulog",
  ``!n. power_free n <=> (1 < n /\ n power_free_upto ulog n)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[power_free_0] >>
  rw[power_free_check_upto, ulog_LOG2]);

(* Theorem: power_free 2 *)
(* Proof:
       power_free 2
   <=> 2 power_free_upto (LOG2 2)   by power_free_check_upto_LOG2
   <=> 2 power_free_upto 1          by LOG2_2
   <=> T                            by power_free_upto_1
*)
val power_free_2 = store_thm(
  "power_free_2",
  ``power_free 2``,
  rw[power_free_check_upto_LOG2, power_free_upto_1]);

(* Theorem: power_free 3 *)
(* Proof:
   Note 3 power_free_upto 1         by power_free_upto_1
       power_free 3
   <=> 3 power_free_upto (ulog 3)   by power_free_check_upto_ulog
   <=> 3 power_free_upto 2          by evaluation
   <=> ROOT 2 3 ** 2 <> 3           by power_free_upto_suc, 0 < 1
   <=> T                            by evaluation
*)
val power_free_3 = store_thm(
  "power_free_3",
  ``power_free 3``,
  `3 power_free_upto 1` by rw[power_free_upto_1] >>
  `ulog 3 = 2` by EVAL_TAC >>
  `ROOT 2 3 ** 2 <> 3` by EVAL_TAC >>
  `power_free 3 <=> 3 power_free_upto 2` by rw[power_free_check_upto_ulog] >>
  metis_tac[power_free_upto_suc, DECIDE``0 < 1 /\ (1 + 1 = 2)``]);

(* Define a power free test, based on (ulog n), for computation. *)
val power_free_test_def = Define`
    power_free_test n <=>(1 < n /\ n power_free_upto (ulog n))
`;

(* Theorem: power_free_test n = power_free n *)
(* Proof: by power_free_test_def, power_free_check_upto_ulog *)
val power_free_test_eqn = store_thm(
  "power_free_test_eqn",
  ``!n. power_free_test n = power_free n``,
  rw[power_free_test_def, power_free_check_upto_ulog]);

(* Theorem: power_free n <=>
       (1 < n /\ !j. 1 < j /\ j <= (LOG2 n) ==> ROOT j n ** j <> n) *)
(* Proof: by power_free_check_upto_ulog, power_free_upto_def *)
val power_free_test_upto_LOG2 = store_thm(
  "power_free_test_upto_LOG2",
  ``!n. power_free n <=>
       (1 < n /\ !j. 1 < j /\ j <= (LOG2 n) ==> ROOT j n ** j <> n)``,
  rw[power_free_check_upto_LOG2, power_free_upto_def]);

(* Theorem: power_free n <=>
       (1 < n /\ !j. 1 < j /\ j <= (ulog n) ==> ROOT j n ** j <> n) *)
(* Proof: by power_free_check_upto_ulog, power_free_upto_def *)
val power_free_test_upto_ulog = store_thm(
  "power_free_test_upto_ulog",
  ``!n. power_free n <=>
       (1 < n /\ !j. 1 < j /\ j <= (ulog n) ==> ROOT j n ** j <> n)``,
  rw[power_free_check_upto_ulog, power_free_upto_def]);

(* ------------------------------------------------------------------------- *)
(* Another Characterisation of Power Free                                    *)
(* ------------------------------------------------------------------------- *)

(* Define power index of n, the highest index of n in power form by descending from k *)
val power_index_def = Define `
    power_index n k <=>
        if k <= 1 then 1
        else if (ROOT k n) ** k = n then k
        else power_index n (k - 1)
`;

(* Theorem: power_index n 0 = 1 *)
(* Proof: by power_index_def *)
val power_index_0 = store_thm(
  "power_index_0",
  ``!n. power_index n 0 = 1``,
  rw[Once power_index_def]);

(* Theorem: power_index n 1 = 1 *)
(* Proof: by power_index_def *)
val power_index_1 = store_thm(
  "power_index_1",
  ``!n. power_index n 1 = 1``,
  rw[Once power_index_def]);

(* Theorem: (ROOT (power_index n k) n) ** (power_index n k) = n *)
(* Proof:
   By induction on k.
   Base: ROOT (power_index n 0) n ** power_index n 0 = n
        ROOT (power_index n 0) n ** power_index n 0
      = (ROOT 1 n) ** 1          by power_index_0
      = n ** 1                   by ROOT_1
      = n                        by EXP_1
   Step: ROOT (power_index n k) n ** power_index n k = n ==>
         ROOT (power_index n (SUC k)) n ** power_index n (SUC k) = n
      If k = 0,
        ROOT (power_index n (SUC 0)) n ** power_index n (SUC 0)
      = ROOT (power_index n 1) n ** power_index n 1     by ONE
      = (ROOT 1 n) ** 1                                 by power_index_1
      = n ** 1                                          by ROOT_1
      = n                                               by EXP_1
      If k <> 0,
         Then ~(SUC k <= 1)                                     by 0 < k
         If ROOT (SUC k) n ** SUC k = n,
            Then power_index n (SUC k) = SUC k                  by power_index_def
              so ROOT (power_index n (SUC k)) n ** power_index n (SUC k)
               = ROOT (SUC k) n ** SUC k                        by above
               = n                                              by condition
         If ROOT (SUC k) n ** SUC k <> n,
            Then power_index n (SUC k) = power_index n k        by power_index_def
              so ROOT (power_index n (SUC k)) n ** power_index n (SUC k)
               = ROOT (power_index n k) n ** power_index n k    by above
               = n                                              by induction hypothesis
*)
val power_index_eqn = store_thm(
  "power_index_eqn",
  ``!n k. (ROOT (power_index n k) n) ** (power_index n k) = n``,
  rpt strip_tac >>
  Induct_on `k` >-
  rw[power_index_0] >>
  Cases_on `k = 0` >-
  rw[power_index_1] >>
  `~(SUC k <= 1)` by decide_tac >>
  rw_tac std_ss[Once power_index_def] >-
  rw[Once power_index_def] >>
  `power_index n (SUC k) = power_index n k` by rw[Once power_index_def] >>
  rw[]);

(* Theorem: perfect_power n (ROOT (power_index n k) n) *)
(* Proof:
   Let m = ROOT (power_index n k) n.
   By perfect_power_def, this is to show:
      ?e. n = m ** e
   Take e = power_index n k.
     m ** e
   = (ROOT (power_index n k) n) ** (power_index n k)     by root_compute_eqn
   = n                                                   by power_index_eqn
*)
val power_index_root = store_thm(
  "power_index_root",
  ``!n k. perfect_power n (ROOT (power_index n k) n)``,
  metis_tac[perfect_power_def, power_index_eqn]);

(* Theorem: power_index 1 k = if k = 0 then 1 else k *)
(* Proof:
   If k = 0,
      power_index 1 0 = 1               by power_index_0
   If k <> 0, then 0 < k.
      If k = 1,
         Then power_index 1 1 = 1 = k   by power_index_1
      If k <> 1, 1 < k.
         Note ROOT k 1 = 1              by ROOT_OF_1, 0 < k.
           so power_index 1 k = k       by power_index_def
*)
val power_index_of_1 = store_thm(
  "power_index_of_1",
  ``!k. power_index 1 k = if k = 0 then 1 else k``,
  rw[Once power_index_def]);

(* Theorem: 0 < k /\ ((ROOT k n) ** k = n) ==> (power_index n k = k) *)
(* Proof:
   If k = 1,
      True since power_index n 1 = 1      by power_index_1
   If k <> 1, then 1 < k                  by 0 < k
      True                                by power_index_def
*)
val power_index_exact_root = store_thm(
  "power_index_exact_root",
  ``!n k. 0 < k /\ ((ROOT k n) ** k = n) ==> (power_index n k = k)``,
  rpt strip_tac >>
  Cases_on `k = 1` >-
  rw[power_index_1] >>
  `1 < k` by decide_tac >>
  rw[Once power_index_def]);

(* Theorem: (ROOT k n) ** k <> n ==> (power_index n k = power_index n (k - 1)) *)
(* Proof:
   If k = 0,
      Then k = k - 1                  by k = 0
      Thus true trivially.
   If k = 1,
      Note power_index n 1 = 1        by power_index_1
       and power_index n 0 = 1        by power_index_0
      Thus true.
   If k <> 0 /\ k <> 1, then 1 < k    by arithmetic
      True                            by power_index_def
*)
val power_index_not_exact_root = store_thm(
  "power_index_not_exact_root",
  ``!n k. (ROOT k n) ** k <> n ==> (power_index n k = power_index n (k - 1))``,
  rpt strip_tac >>
  Cases_on `k = 0` >| [
    `k = k - 1` by decide_tac >>
    rw[],
    Cases_on `k = 1` >-
    rw[power_index_0, power_index_1] >>
    `1 < k` by decide_tac >>
    rw[Once power_index_def]
  ]);

(* Theorem: k <= m /\ (!j. k < j /\ j <= m ==> (ROOT j n) ** j <> n) ==> (power_index n m = power_index n k) *)
(* Proof:
   By induction on (m - k).
   Base: k <= m /\ 0 = m - k ==> power_index n m = power_index n k
      Note m <= k            by 0 = m - k
        so m = k             by k <= m
      Thus true trivially.
   Step: !m'. v = m' - k /\ k <= m' /\ ... ==> power_index n m' = power_index n k ==>
         SUC v = m - k ==> power_index n m = power_index n k
      If m = k, true trivially.
      If m <> k, then k < m.
         Thus k <= (m - 1), and v = (m - 1) - k.
         Note ROOT m n ** m <> n          by j = m in implication
         Thus power_index n m
            = power_index n (m - 1)       by power_index_not_exact_root
            = power_index n k             by induction hypothesis, m' = m - 1.
*)
val power_index_no_exact_roots = store_thm(
  "power_index_no_exact_roots",
  ``!m n k. k <= m /\ (!j. k < j /\ j <= m ==> (ROOT j n) ** j <> n) ==> (power_index n m = power_index n k)``,
  rpt strip_tac >>
  Induct_on `m - k` >| [
    rpt strip_tac >>
    `m = k` by decide_tac >>
    rw[],
    rpt strip_tac >>
    Cases_on `m = k` >-
    rw[] >>
    `ROOT m n ** m <> n` by rw[] >>
    `k <= m - 1` by decide_tac >>
    `power_index n (m - 1) = power_index n k` by rw[] >>
    rw[power_index_not_exact_root]
  ]);

(* The theorem power_index_equal requires a detective-style proof, based on these lemma. *)

(* Theorem: k <= m /\ ((ROOT k n) ** k = n) ==> k <= power_index n m *)
(* Proof:
   If k = 0,
      Then n = 1                          by EXP
      If m = 0,
         Then power_index 1 0 = 1         by power_index_of_1
          But k <= 0, so k = 0            by arithmetic
         Hence k <= power_index n m
      If m <> 0,
         Then power_index 1 m = m         by power_index_of_1
         Hence k <= power_index 1 m = m   by given

   If k <> 0, then 0 < k.
      Let s = {j | j <= m /\ ((ROOT j n) ** j = n)}
      Then s SUBSET (count (SUC m))       by SUBSET_DEF
       ==> FINITE s                       by SUBSET_FINITE, FINITE_COUNT
      Note k IN s                         by given
       ==> s <> {}                        by MEMBER_NOT_EMPTY
      Let t = MAX_SET s.

      Claim: !x. t < x /\ x <= m ==> (ROOT x n) ** x <> n
      Proof: By contradiction, suppose (ROOT x n) ** x = n
             Then x IN s, so x <= t       by MAX_SET_PROPERTY
             This contradicts t < x.

      Note t IN s                              by MAX_SET_IN_SET
        so t <= m /\ (ROOT t n) ** t = n       by above
      Thus power_index n m = power_index n t   by power_index_no_exact_roots, t <= m
       and power_index n t = t                 by power_index_exact_root, (ROOT t n) ** t = n
       But k <= t                              by MAX_SET_PROPERTY
      Thus k <= t = power_index n m
*)
val power_index_lower = store_thm(
  "power_index_lower",
  ``!m n k. k <= m /\ ((ROOT k n) ** k = n) ==> k <= power_index n m``,
  rpt strip_tac >>
  Cases_on `k = 0` >| [
    `n = 1` by fs[EXP] >>
    rw[power_index_of_1],
    `0 < k` by decide_tac >>
    qabbrev_tac `s = {j | j <= m /\ ((ROOT j n) ** j = n)}` >>
    `!j. j IN s <=> j <= m /\ ((ROOT j n) ** j = n)` by rw[Abbr`s`] >>
    `s SUBSET (count (SUC m))` by rw[SUBSET_DEF] >>
    `FINITE s` by metis_tac[SUBSET_FINITE, FINITE_COUNT] >>
    `k IN s` by rw[] >>
    `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
    qabbrev_tac `t = MAX_SET s` >>
    `!x. t < x /\ x <= m ==> (ROOT x n) ** x <> n` by
  (spose_not_then strip_assume_tac >>
    `x IN s` by rw[] >>
    `x <= t` by rw[MAX_SET_PROPERTY, Abbr`t`] >>
    decide_tac) >>
    `t IN s` by rw[MAX_SET_IN_SET, Abbr`t`] >>
    `power_index n m = power_index n t` by metis_tac[power_index_no_exact_roots] >>
    `k <= t` by rw[MAX_SET_PROPERTY, Abbr`t`] >>
    `(ROOT t n) ** t = n` by metis_tac[] >>
    `power_index n t = t` by rw[power_index_exact_root] >>
    decide_tac
  ]);

(* Theorem: 0 < power_index n k *)
(* Proof:
   If k = 0,
      True since power_index n 0 = 1         by power_index_0
   If k <> 0,
      Then 1 <= k.
      Note (ROOT 1 n) ** 1 = n ** 1 = n      by ROOT_1, EXP_1
      Thus 1 <= power_index n k              by power_index_lower
        or 0 < power_index n k
*)
val power_index_pos = store_thm(
  "power_index_pos",
  ``!n k. 0 < power_index n k``,
  rpt strip_tac >>
  Cases_on `k = 0` >-
  rw[power_index_0] >>
  `1 <= power_index n k` by rw[power_index_lower, EXP_1] >>
  decide_tac);

(* Theorem: 0 < k ==> power_index n k <= k *)
(* Proof:
   By induction on k.
   Base: 0 < 0 ==> power_index n 0 <= 0
      True by 0 < 0 = F.
   Step: 0 < k ==> power_index n k <= k ==>
         0 < SUC k ==> power_index n (SUC k) <= SUC k
      If k = 0,
         Then SUC k = 1                   by ONE
         True since power_index n 1 = 1   by power_index_1
      If k <> 0,
         Let m = SUC k, or k = m - 1.
         Then 1 < m                       by arithmetic
         If (ROOT m n) ** m = n,
            Then power_index n m
               = m <= m                   by power_index_exact_root
         If (ROOT m n) ** m <> n,
            Then power_index n m
               = power_index n (m - 1)    by power_index_not_exact_root
               = power_index n k          by m - 1 = k
               <= k                       by induction hypothesis
             But k < SUC k = m            by LESS_SUC
            Thus power_index n m < m      by LESS_EQ_LESS_TRANS
              or power_index n m <= m     by LESS_IMP_LESS_OR_EQ
*)
val power_index_upper = store_thm(
  "power_index_upper",
  ``!n k. 0 < k ==> power_index n k <= k``,
  strip_tac >>
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `k = 0` >-
  rw[power_index_1] >>
  `1 < SUC k` by decide_tac >>
  qabbrev_tac `m = SUC k` >>
  Cases_on `(ROOT m n) ** m = n` >-
  rw[power_index_exact_root] >>
  rw[power_index_not_exact_root, Abbr`m`]);

(* Theorem: 0 < k /\ k <= m ==>
            ((power_index n m = power_index n k) <=> (!j. k < j /\ j <= m ==> (ROOT j n) ** j <> n)) *)
(* Proof:
   If part: 0 < k /\ k <= m /\ power_index n m = power_index n k /\ k < j /\ j <= m ==> ROOT j n ** j <> n
      By contradiction, suppose ROOT j n ** j = n.
      Then j <= power_index n m      by power_index_lower
      But       power_index n k <= k by power_index_upper, 0 < k
      Thus j <= k                    by LESS_EQ_TRANS
      This contradicts k < j.
   Only-if part: 0 < k /\ k <= m /\ !j. k < j /\ j <= m ==> ROOT j n ** j <> n ==>
                 power_index n m = power_index n k
      True by power_index_no_exact_roots
*)
val power_index_equal = store_thm(
  "power_index_equal",
  ``!m n k. 0 < k /\ k <= m ==>
    ((power_index n m = power_index n k) <=> (!j. k < j /\ j <= m ==> (ROOT j n) ** j <> n))``,
  rpt strip_tac >>
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `j <= power_index n m` by rw[power_index_lower] >>
    `power_index n k <= k` by rw[power_index_upper] >>
    decide_tac,
    rw[power_index_no_exact_roots]
  ]);

(* Theorem: (power_index n m = k) ==> !j. k < j /\ j <= m ==> (ROOT j n) ** j <> n *)
(* Proof:
   By contradiction, suppose k < j /\ j <= m /\ (ROOT j n) ** j = n.
   Then j <= power_index n m                   by power_index_lower
   This contradicts power_index n m = k < j    by given
*)
val power_index_property = store_thm(
  "power_index_property",
  ``!m n k. (power_index n m = k) ==> !j. k < j /\ j <= m ==> (ROOT j n) ** j <> n``,
  spose_not_then strip_assume_tac >>
  `j <= power_index n m` by rw[power_index_lower] >>
  decide_tac);

(* Theorem: power_free n <=> (1 < n) /\ (power_index n (LOG2 n) = 1) *)
(* Proof:
   By power_free_check_upto_LOG2, power_free_upto_def, this is to show:
      1 < n /\ (!j. 1 < j /\ j <= LOG2 n ==> ROOT j n ** j <> n) <=>
      1 < n /\ (power_index n (LOG2 n) = 1)
   If part:
      Note 0 < LOG2 n              by LOG2_POS, 1 < n
           power_index n (LOG2 n)
         = power_index n 1         by power_index_no_exact_roots, 1 <= LOG2 n
         = 1                       by power_index_1
   Only-if part, true              by power_index_property
*)
val power_free_by_power_index_LOG2 = store_thm(
  "power_free_by_power_index_LOG2",
  ``!n. power_free n <=> (1 < n) /\ (power_index n (LOG2 n) = 1)``,
  rw[power_free_check_upto_LOG2, power_free_upto_def] >>
  rw[EQ_IMP_THM] >| [
    `0 < LOG2 n` by rw[] >>
    `1 <= LOG2 n` by decide_tac >>
    `power_index n (LOG2 n) = power_index n 1` by rw[power_index_no_exact_roots] >>
    rw[power_index_1],
    metis_tac[power_index_property]
  ]);

(* Theorem: power_free n <=> (1 < n) /\ (power_index n (ulog n) = 1) *)
(* Proof:
   By power_free_check_upto_ulog, power_free_upto_def, this is to show:
      1 < n /\ (!j. 1 < j /\ j <= ulog n ==> ROOT j n ** j <> n) <=>
      1 < n /\ (power_index n (ulog n) = 1)
   If part:
      Note 0 < ulog n              by ulog_POS, 1 < n
           power_index n (ulog n)
         = power_index n 1         by power_index_no_exact_roots, 1 <= ulog n
         = 1                       by power_index_1
   Only-if part, true              by power_index_property
*)
val power_free_by_power_index_ulog = store_thm(
  "power_free_by_power_index_ulog",
  ``!n. power_free n <=> (1 < n) /\ (power_index n (ulog n) = 1)``,
  rw[power_free_check_upto_ulog, power_free_upto_def] >>
  rw[EQ_IMP_THM] >| [
    `0 < ulog n` by rw[] >>
    `1 <= ulog n` by decide_tac >>
    `power_index n (ulog n) = power_index n 1` by rw[power_index_no_exact_roots] >>
    rw[power_index_1],
    metis_tac[power_index_property]
  ]);

(* ------------------------------------------------------------------------- *)
(* Prime Power Documentation                                                 *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   ppidx n                     = prime_power_index p n
   common_prime_divisors m n   = (prime_divisors m) INTER (prime_divisors n)
   total_prime_divisors m n    = (prime_divisors m) UNION (prime_divisors n)
   park_on m n                 = {p | p IN common_prime_divisors m n /\ ppidx m <= ppidx n}
   park_off m n                = {p | p IN common_prime_divisors m n /\ ppidx n < ppidx m}
   park m n                    = PROD_SET (IMAGE (\p. p ** ppidx m) (park_on m n))
*)
(* Definitions and Theorems (# are exported):

   Helper Theorem:
   self_to_log_index_member       |- !n x. MEM x [1 .. n] ==> MEM (x ** LOG x n) [1 .. n]

   Prime Power or Coprime Factors:
   prime_power_or_coprime_factors    |- !n. 1 < n ==> (?p k. 0 < k /\ prime p /\ (n = p ** k)) \/
                                        ?a b. (n = a * b) /\ coprime a b /\ 1 < a /\ 1 < b /\ a < n /\ b < n
   non_prime_power_coprime_factors   |- !n. 1 < n /\ ~(?p k. 0 < k /\ prime p /\ (n = p ** k)) ==>
                                        ?a b. (n = a * b) /\ coprime a b /\ 1 < a /\ a < n /\ 1 < b /\ b < n
   pairwise_coprime_for_prime_powers |- !s f. s SUBSET prime ==> PAIRWISE_COPRIME (IMAGE (\p. p ** f p) s)

   Prime Power Index:
   prime_power_index_exists       |- !n p. 0 < n /\ prime p ==> ?m. p ** m divides n /\ coprime p (n DIV p ** m)
   prime_power_index_def          |- !p n. 0 < n /\ prime p ==>
                                           p ** ppidx n divides n /\ coprime p (n DIV p ** ppidx n)
   prime_power_factor_divides     |- !n p. prime p ==> p ** ppidx n divides n
   prime_power_cofactor_coprime   |- !n p. 0 < n /\ prime p ==> coprime p (n DIV p ** ppidx n)
   prime_power_eqn                |- !n p. 0 < n /\ prime p ==> (n = p ** ppidx n * (n DIV p ** ppidx n))
   prime_power_divisibility       |- !n p. 0 < n /\ prime p ==> !k. p ** k divides n <=> k <= ppidx n
   prime_power_index_maximal      |- !n p. 0 < n /\ prime p ==> !k. k > ppidx n ==> ~(p ** k divides n)
   prime_power_index_of_divisor   |- !m n. 0 < n /\ m divides n ==> !p. prime p ==> ppidx m <= ppidx n
   prime_power_index_test         |- !n p. 0 < n /\ prime p ==>
                                     !k. (k = ppidx n) <=> ?q. (n = p ** k * q) /\ coprime p q:
   prime_power_index_1            |- !p. prime p ==> (ppidx 1 = 0)
   prime_power_index_eq_0         |- !n p. 0 < n /\ prime p /\ ~(p divides n) ==> (ppidx n = 0)
   prime_power_index_prime_power  |- !p. prime p ==> !k. ppidx (p ** k) = k
   prime_power_index_prime        |- !p. prime p ==> (ppidx p = 1)
   prime_power_index_eqn          |- !n p. 0 < n /\ prime p ==> (let q = n DIV p ** ppidx n in
                                                         (n = p ** ppidx n * q) /\ coprime p q)
   prime_power_index_pos          |- !n p. 0 < n /\ prime p /\ p divides n ==> 0 < ppidx n

   Prime Power and GCD, LCM:
   gcd_prime_power_factor       |- !a b p. 0 < a /\ 0 < b /\ prime p ==>
                        (gcd a b = p ** MIN (ppidx a) (ppidx b) * gcd (a DIV p ** ppidx a) (b DIV p ** ppidx b))
   gcd_prime_power_factor_divides_gcd
                                |- !a b p. 0 < a /\ 0 < b /\ prime p ==>
                                           p ** MIN (ppidx a) (ppidx b) divides gcd a b
   gcd_prime_power_cofactor_coprime
                                |- !a b p. 0 < a /\ 0 < b /\ prime p ==>
                                           coprime p (gcd (a DIV p ** ppidx a) (b DIV p ** ppidx b))
   gcd_prime_power_index        |- !a b p. 0 < a /\ 0 < b /\ prime p ==>
                                           (ppidx (gcd a b) = MIN (ppidx a) (ppidx b))
   gcd_prime_power_divisibility |- !a b p. 0 < a /\ 0 < b /\ prime p ==>
                                   !k. p ** k divides gcd a b ==> k <= MIN (ppidx a) (ppidx b)

   lcm_prime_power_factor       |- !a b p. 0 < a /\ 0 < b /\ prime p ==>
       (lcm a b = p ** MAX (ppidx a) (ppidx b) * lcm (a DIV p ** ppidx a) (b DIV p ** ppidx b))
   lcm_prime_power_factor_divides_lcm
                                |- !a b p. 0 < a /\ 0 < b /\ prime p ==>
                                           p ** MAX (ppidx a) (ppidx b) divides lcm a b
   lcm_prime_power_cofactor_coprime
                                |- !a b p. 0 < a /\ 0 < b /\ prime p ==>
                                           coprime p (lcm (a DIV p ** ppidx a) (b DIV p ** ppidx b))
   lcm_prime_power_index        |- !a b p. 0 < a /\ 0 < b /\ prime p ==>
                                           (ppidx (lcm a b) = MAX (ppidx a) (ppidx b))
   lcm_prime_power_divisibility |- !a b p. 0 < a /\ 0 < b /\ prime p ==>
                                   !k. p ** k divides lcm a b ==> k <= MAX (ppidx a) (ppidx b)

   Prime Powers and List LCM:
   list_lcm_prime_power_factor_divides   |- !l p. prime p ==> p ** MAX_LIST (MAP ppidx l) divides list_lcm l
   list_lcm_prime_power_index            |- !l p. prime p /\ POSITIVE l ==>
                                                  (ppidx (list_lcm l) = MAX_LIST (MAP ppidx l))
   list_lcm_prime_power_divisibility     |- !l p. prime p /\ POSITIVE l ==>
                                            !k. p ** k divides list_lcm l ==> k <= MAX_LIST (MAP ppidx l)
   list_lcm_prime_power_factor_member    |- !l p. prime p /\ l <> [] /\ POSITIVE l ==>
                                            !k. p ** k divides list_lcm l ==> ?x. MEM x l /\ p ** k divides x
   lcm_special_for_prime_power       |- !p. prime p ==> !m n. (n = p ** SUC (ppidx m)) ==> (lcm n m = p * m)
   lcm_special_for_coprime_factors   |- !n a b. (n = a * b) /\ coprime a b ==>
                                        !m. a divides m /\ b divides m ==> (lcm n m = m)

   Prime Divisors:
   prime_divisors_def            |- !n. prime_divisors n = {p | prime p /\ p divides n}
   prime_divisors_element        |- !n p. p IN prime_divisors n <=> prime p /\ p divides n
   prime_divisors_subset_natural |- !n. 0 < n ==> prime_divisors n SUBSET natural n
   prime_divisors_finite         |- !n. 0 < n ==> FINITE (prime_divisors n)
   prime_divisors_0              |- prime_divisors 0 = prime
   prime_divisors_1              |- prime_divisors 1 = {}
   prime_divisors_subset_prime   |- !n. prime_divisors n SUBSET prime
   prime_divisors_nonempty       |- !n. 1 < n ==> prime_divisors n <> {}
   prime_divisors_empty_iff      |- !n. (prime_divisors n = {}) <=> (n = 1)
   prime_divisors_0_not_sing     |- ~SING (prime_divisors 0)
   prime_divisors_prime          |- !n. prime n ==> (prime_divisors n = {n})
   prime_divisors_prime_power    |- !n. prime n ==> !k. 0 < k ==> (prime_divisors (n ** k) = {n})
   prime_divisors_sing           |- !n. SING (prime_divisors n) <=> ?p k. prime p /\ 0 < k /\ (n = p ** k)
   prime_divisors_sing_alt       |- !n p. (prime_divisors n = {p}) <=> ?k. prime p /\ 0 < k /\ (n = p ** k)
   prime_divisors_sing_property  |- !n. SING (prime_divisors n) ==> (let p = CHOICE (prime_divisors n) in
                                        prime p /\ (n = p ** ppidx n))
   prime_divisors_divisor_subset     |- !m n. m divides n ==> prime_divisors m SUBSET prime_divisors n
   prime_divisors_common_divisor     |- !n m x. x divides m /\ x divides n ==>
                                         prime_divisors x SUBSET prime_divisors m INTER prime_divisors n
   prime_divisors_common_multiple    |- !n m x. m divides x /\ n divides x ==>
                                         prime_divisors m UNION prime_divisors n SUBSET prime_divisors x
   prime_power_index_common_divisor  |- !n m x. 0 < m /\ 0 < n /\ x divides m /\ x divides n ==>
                                        !p. prime p ==> ppidx x <= MIN (ppidx m) (ppidx n)
   prime_power_index_common_multiple |- !n m x. 0 < x /\ m divides x /\ n divides x ==>
                                        !p. prime p ==> MAX (ppidx m) (ppidx n) <= ppidx x
   prime_power_index_le_log_index    |- !n p. 0 < n /\ prime p ==> ppidx n <= LOG p n

   Prime-related Sets:
   primes_upto_def                |- !n. primes_upto n = {p | prime p /\ p <= n}
   prime_powers_upto_def          |- !n. prime_powers_upto n = IMAGE (\p. p ** LOG p n) (primes_upto n)
   prime_power_divisors_def       |- !n. prime_power_divisors n = IMAGE (\p. p ** ppidx n) (prime_divisors n)

   primes_upto_element            |- !n p. p IN primes_upto n <=> prime p /\ p <= n
   primes_upto_subset_natural     |- !n. primes_upto n SUBSET natural n
   primes_upto_finite             |- !n. FINITE (primes_upto n)
   primes_upto_pairwise_coprime   |- !n. PAIRWISE_COPRIME (primes_upto n)
   primes_upto_0                  |- primes_upto 0 = {}
   primes_count_0                 |- primes_count 0 = 0
   primes_upto_1                  |- primes_upto 1 = {}
   primes_count_1                 |- primes_count 1 = 0

   prime_powers_upto_element      |- !n x. x IN prime_powers_upto n <=>
                                           ?p. (x = p ** LOG p n) /\ prime p /\ p <= n
   prime_powers_upto_element_alt  |- !p n. prime p /\ p <= n ==> p ** LOG p n IN prime_powers_upto n
   prime_powers_upto_finite       |- !n. FINITE (prime_powers_upto n)
   prime_powers_upto_pairwise_coprime  |- !n. PAIRWISE_COPRIME (prime_powers_upto n)
   prime_powers_upto_0            |- prime_powers_upto 0 = {}
   prime_powers_upto_1            |- prime_powers_upto 1 = {}

   prime_power_divisors_element   |- !n x. x IN prime_power_divisors n <=>
                                           ?p. (x = p ** ppidx n) /\ prime p /\ p divides n
   prime_power_divisors_element_alt |- !p n. prime p /\ p divides n ==>
                                             p ** ppidx n IN prime_power_divisors n
   prime_power_divisors_finite      |- !n. 0 < n ==> FINITE (prime_power_divisors n)
   prime_power_divisors_pairwise_coprime  |- !n. PAIRWISE_COPRIME (prime_power_divisors n)
   prime_power_divisors_1         |- prime_power_divisors 1 = {}

   Factorisations:
   prime_factorisation          |- !n. 0 < n ==> (n = PROD_SET (prime_power_divisors n))
   basic_prime_factorisation    |- !n. 0 < n ==>
                                       (n = PROD_SET (IMAGE (\p. p ** ppidx n) (prime_divisors n)))
   divisor_prime_factorisation  |- !m n. 0 < n /\ m divides n ==>
                                         (m = PROD_SET (IMAGE (\p. p ** ppidx m) (prime_divisors n)))
   gcd_prime_factorisation      |- !m n. 0 < m /\ 0 < n ==>
                                         (gcd m n = PROD_SET (IMAGE (\p. p ** MIN (ppidx m) (ppidx n))
                                                           (prime_divisors m INTER prime_divisors n)))
   lcm_prime_factorisation      |- !m n. 0 < m /\ 0 < n ==>
                                         (lcm m n = PROD_SET (IMAGE (\p. p ** MAX (ppidx m) (ppidx n))
                                                           (prime_divisors m UNION prime_divisors n)))

   GCD and LCM special coprime decompositions:
   common_prime_divisors_element     |- !m n p. p IN common_prime_divisors m n <=>
                                                p IN prime_divisors m /\ p IN prime_divisors n
   common_prime_divisors_finite      |- !m n. 0 < m /\ 0 < n ==> FINITE (common_prime_divisors m n)
   common_prime_divisors_pairwise_coprime     |- !m n. PAIRWISE_COPRIME (common_prime_divisors m n)
   common_prime_divisors_min_image_pairwise_coprime
   |- !m n. PAIRWISE_COPRIME (IMAGE (\p. p ** MIN (ppidx m) (ppidx n)) (common_prime_divisors m n))
   total_prime_divisors_element      |- !m n p. p IN total_prime_divisors m n <=>
                                                p IN prime_divisors m \/ p IN prime_divisors n
   total_prime_divisors_finite       |- !m n. 0 < m /\ 0 < n ==> FINITE (total_prime_divisors m n)
   total_prime_divisors_pairwise_coprime      |- !m n. PAIRWISE_COPRIME (total_prime_divisors m n)
   total_prime_divisors_max_image_pairwise_coprime
   |- !m n. PAIRWISE_COPRIME (IMAGE (\p. p ** MAX (ppidx m) (ppidx n)) (total_prime_divisors m n))

   park_on_element   |- !m n p. p IN park_on m n <=>
                                p IN prime_divisors m /\ p IN prime_divisors n /\ ppidx m <= ppidx n
   park_off_element  |- !m n p. p IN park_off m n <=>
                                p IN prime_divisors m /\ p IN prime_divisors n /\ ppidx n < ppidx m
   park_off_alt      |- !m n. park_off m n = common_prime_divisors m n DIFF park_on m n
   park_on_subset_common    |- !m n. park_on m n SUBSET common_prime_divisors m n
   park_off_subset_common   |- !m n. park_off m n SUBSET common_prime_divisors m n
   park_on_subset_total     |- !m n. park_on m n SUBSET total_prime_divisors m n
   park_off_subset_total    |- !m n. park_off m n SUBSET total_prime_divisors m n
   park_on_off_partition    |- !m n. common_prime_divisors m n =|= park_on m n # park_off m n
   park_off_image_has_not_1 |- !m n. 1 NOTIN IMAGE (\p. p ** ppidx m) (park_off m n)

   park_on_off_common_image_partition
         |- !m n. (let s = IMAGE (\p. p ** MIN (ppidx m) (ppidx n)) (common_prime_divisors m n) in
                   let u = IMAGE (\p. p ** ppidx m) (park_on m n) in
                   let v = IMAGE (\p. p ** ppidx n) (park_off m n) in
                   0 < m ==> s =|= u # v)
   gcd_park_decomposition  |- !m n. 0 < m /\ 0 < n ==>
                                    (let a = mypark m n in let b = gcd m n DIV a in
                                     (b = PROD_SET (IMAGE (\p. p ** ppidx n) (park_off m n))) /\
                                     (gcd m n = a * b) /\ coprime a b)
   gcd_park_decompose      |- !m n. 0 < m /\ 0 < n ==>
                                    (let a = mypark m n in let b = gcd m n DIV a in
                                     (gcd m n = a * b) /\ coprime a b)

   park_on_off_total_image_partition
         |- !m n. (let s = IMAGE (\p. p ** MAX (ppidx m) (ppidx n)) (total_prime_divisors m n) in
                   let u = IMAGE (\p. p ** ppidx m) (prime_divisors m DIFF park_on m n) in
                   let v = IMAGE (\p. p ** ppidx n) (prime_divisors n DIFF park_off m n) in
                   0 < m /\ 0 < n ==> s =|= u # v)
   lcm_park_decomposition  |- !m n. 0 < m /\ 0 < n ==>
                               (let a = park m n in let b = gcd m n DIV a in
                                let p = m DIV a in let q = a * n DIV gcd m n in
                                (b = PROD_SET (IMAGE (\p. p ** ppidx n) (park_off m n))) /\
           (p = PROD_SET (IMAGE (\p. p ** ppidx m) (prime_divisors m DIFF park_on m n))) /\
           (q = PROD_SET (IMAGE (\p. p ** ppidx n) (prime_divisors n DIFF park_off m n))) /\
            (lcm m n = p * q) /\ coprime p q /\ (gcd m n = a * b) /\ (m = a * p) /\ (n = b * q))
   lcm_park_decompose      |- !m n. 0 < m /\ 0 < n ==>
                              (let a = park m n in let p = m DIV a in let q = a * n DIV gcd m n in
                               (lcm m n = p * q) /\ coprime p q)
   lcm_gcd_park_decompose  |- !m n. 0 < m /\ 0 < n ==>
                               (let a = park m n in let b = gcd m n DIV a in
                                let p = m DIV a in let q = a * n DIV gcd m n in
                                (lcm m n = p * q) /\ coprime p q /\
                                (gcd m n = a * b) /\ (m = a * p) /\ (n = b * q))

   Consecutive LCM Recurrence:
   lcm_fun_def        |- (lcm_fun 0 = 1) /\
                          !n. lcm_fun (SUC n) = if n = 0 then 1 else
                              case some p. ?k. 0 < k /\ prime p /\ (SUC n = p ** k) of
                                NONE => lcm_fun n
                              | SOME p => p * lcm_fun n
   lcm_fun_0          |- lcm_fun 0 = 1
   lcm_fun_SUC        |- !n. lcm_fun (SUC n) = if n = 0 then 1 else
                             case some p. ?k. 0 < k /\ prime p /\ (SUC n = p ** k) of
                               NONE => lcm_fun n
                             | SOME p => p * lcm_fun n
   lcm_fun_1          |- lcm_fun 1 = 1
   lcm_fun_2          |- lcm_fun 2 = 2
   lcm_fun_suc_some   |- !n p. prime p /\ (?k. 0 < k /\ (SUC n = p ** k)) ==> (lcm_fun (SUC n) = p * lcm_fun n)
   lcm_fun_suc_none   |- !n. ~(?p k. 0 < k /\ prime p /\ (SUC n = p ** k)) ==> (lcm_fun (SUC n) = lcm_fun n)
   list_lcm_prime_power_index_lower   |- !l p. prime p /\ l <> [] /\ POSITIVE l ==>
                                         !x. MEM x l ==> ppidx x <= ppidx (list_lcm l)
   list_lcm_with_last_prime_power     |- !n p k. prime p /\ (n + 2 = p ** k) ==>
                                          (list_lcm [1 .. n + 2] = p * list_lcm (leibniz_vertical n))
   list_lcm_with_last_non_prime_power |- !n. (!p k. (k = 0) \/ ~prime p \/ n + 2 <> p ** k) ==>
                                          (list_lcm [1 .. n + 2] = list_lcm (leibniz_vertical n))
   list_lcm_eq_lcm_fun                |- !n. list_lcm (leibniz_vertical n) = lcm_fun (n + 1)
   lcm_fun_lower_bound                |- !n. 2 ** n <= lcm_fun (n + 1)
   lcm_fun_lower_bound_alt            |- !n. 0 < n ==> 2 ** (n - 1) <= lcm_fun n
   prime_power_index_suc_special      |- !n p. 0 < n /\ prime p /\ (SUC n = p ** ppidx (SUC n)) ==>
                                               (ppidx (SUC n) = SUC (ppidx (list_lcm [1 .. n])))
   prime_power_index_suc_property     |- !n p. 0 < n /\ prime p /\ (n + 1 = p ** ppidx (n + 1)) ==>
                                               (ppidx (n + 1) = 1 + ppidx (list_lcm [1 .. n]))

   Consecutive LCM Recurrence - Rework:
   list_lcm_by_last_prime_power      |- !n. SING (prime_divisors (n + 1)) ==>
                         (list_lcm [1 .. (n + 1)] = CHOICE (prime_divisors (n + 1)) * list_lcm [1 .. n])
   list_lcm_by_last_non_prime_power  |- !n. ~SING (prime_divisors (n + 1)) ==>
                         (list_lcm (leibniz_vertical n) = list_lcm [1 .. n])
   list_lcm_recurrence               |- !n. list_lcm (leibniz_vertical n) = (let s = prime_divisors (n + 1) in
                                            if SING s then CHOICE s * list_lcm [1 .. n] else list_lcm [1 .. n])
   list_lcm_option_last_prime_power     |- !n p. (prime_divisors (n + 1) = {p}) ==>
                                                 (list_lcm (leibniz_vertical n) = p * list_lcm [1 .. n])
   list_lcm_option_last_non_prime_power |- !n. (!p. prime_divisors (n + 1) <> {p}) ==>
                                               (list_lcm (leibniz_vertical n) = list_lcm [1 .. n])
   list_lcm_option_recurrence           |- !n. list_lcm (leibniz_vertical n) =
                                               case some p. prime_divisors (n + 1) = {p} of
                                                 NONE => list_lcm [1 .. n]
                                               | SOME p => p * list_lcm [1 .. n]

   Relating Consecutive LCM to Prime Functions:
   Theorems on Prime-related Sets:
   prime_powers_upto_list_mem     |- !n x. MEM x (SET_TO_LIST (prime_powers_upto n)) <=>
                                           ?p. (x = p ** LOG p n) /\ prime p /\ p <= n
   prime_powers_upto_lcm_prime_to_log_divisor
                                  |- !n p. prime p /\ p <= n ==>
                                           p ** LOG p n divides set_lcm (prime_powers_upto n)
   prime_powers_upto_lcm_prime_divisor
                                  |- !n p. prime p /\ p <= n ==> p divides set_lcm (prime_powers_upto n)
   prime_powers_upto_lcm_prime_to_power_divisor
                                  |- !n p. prime p /\ p <= n ==>
                                           p ** ppidx n divides set_lcm (prime_powers_upto n)
   prime_powers_upto_lcm_divisor  |- !n x. 0 < x /\ x <= n ==> x divides set_lcm (prime_powers_upto n)

   Consecutive LCM and Prime-related Sets:
   lcm_run_eq_set_lcm_prime_powers   |- !n. lcm_run n = set_lcm (prime_powers_upto n)
   set_lcm_prime_powers_upto_eqn     |- !n. set_lcm (prime_powers_upto n) = PROD_SET (prime_powers_upto n)
   lcm_run_eq_prod_set_prime_powers  |- !n. lcm_run n = PROD_SET (prime_powers_upto n)
   prime_powers_upto_prod_set_le     |- !n. PROD_SET (prime_powers_upto n) <= n ** primes_count n
   lcm_run_upper_by_primes_count     |- !n. lcm_run n <= n ** primes_count n
   prime_powers_upto_prod_set_ge     |- !n. PROD_SET (primes_upto n) <= PROD_SET (prime_powers_upto n)
   lcm_run_lower_by_primes_product   |- !n. PROD_SET (primes_upto n) <= lcm_run n
   prime_powers_upto_prod_set_mix_ge |- !n. n ** primes_count n <=
                                            PROD_SET (primes_upto n) * PROD_SET (prime_powers_upto n)
   primes_count_upper_by_product     |- !n. n ** primes_count n <= PROD_SET (primes_upto n) * lcm_run n
   primes_count_upper_by_lcm_run     |- !n. n ** primes_count n <= lcm_run n ** 2
   lcm_run_lower_by_primes_count     |- !n. SQRT (n ** primes_count n) <= lcm_run n
*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: MEM x [1 .. n] ==> MEM (x ** LOG x n) [1 .. n] *)
(* Proof:
   By listRangeINC_MEM, this is to show:
   (1) 1 <= x /\ x <= n ==> 1 <= x ** LOG x n
       Note 0 < x               by 1 <= x
         so 0 < x ** LOG x n    by EXP_POS, 0 < x
         or 1 <= x ** LOG x n   by arithmetic
   (2) 1 <= x /\ x <= n ==> x ** LOG x n <= n
       Note 1 <= n /\ 0 < n     by arithmetic
       If x = 1,
          Then true             by EXP_1
       If x <> 1,
          Then 1 < x, so true   by LOG
*)
Theorem self_to_log_index_member:
  !n x. MEM x [1 .. n] ==> MEM (x ** LOG x n) [1 .. n]
Proof
  rw[listRangeINC_MEM] >>
  ‘0 < n /\ 1 <= n’ by decide_tac >>
  Cases_on ‘x = 1’ >-
  rw[EXP_1] >> rw[LOG]
QED

(* ------------------------------------------------------------------------- *)
(* Prime Power or Coprime Factors                                            *)
(* ------------------------------------------------------------------------- *)

(*
The concept of a prime number goes like this:
* Given a number n > 1, it has factors n = a * b.
  Either there are several possibilities, or there is just the trivial: 1 * n and n * 1.
  A number with only trivial factors is a prime, otherwise it is a composite.
The concept of a prime power number goes like this:
* Given a number n > 1, it has factors n = a * b.
  Either a and b can be chosen to be coprime, or this choice is impossible.
  A number that cannot have coprime factors is a prime power, otherwise a coprime product.
*)

(* Theorem: 1 < n ==> (?p k. 0 < k /\ prime p /\ (n = p ** k)) \/
                      (?a b. (n = a * b) /\ coprime a b /\ 1 < a /\ 1 < b /\ a < n /\ b < n) *)
(* Proof:
   Note 1 < n ==> 0 < n /\ n <> 0 /\ n <> 1        by arithmetic
    Now ?p. prime p /\ p divides n                 by PRIME_FACTOR, n <> 1
     so ?k. 0 < k /\ p ** k divides n /\
            coprime p (n DIV p ** k)               by FACTOR_OUT_PRIME, EXP_1, 0 < n
   Note 0 < p                by PRIME_POS
     so 0 < p ** k           by EXP_POS
    Let b = n DIV p ** k.
   Then n = (p ** k) * b     by DIVIDES_EQN_COMM, 0 < p ** m

   If b = 1,
      Then n = p ** k        by MULT_RIGHT_1
      Take k for the first assertion.
   If b <> 1,
      Let a = p ** k.
       Then coprime a b      by coprime_exp, coprime p b
      Since p <> 1           by NOT_PRIME_1
         so a <> 1           by EXP_EQ_1
        and b <> 0           by MULT_0
        Now a divides n /\ b divides n        by divides_def, MULT_COMM
         so a <= n /\ b <= n                  by DIVIDES_LE, 0 < n
        but a <> n /\ b <> n                  by MULT_LEFT_ID, MULT_RIGHT_ID
       Thus 1 < a /\ 1 < b /\ a < n /\ b < n  by arithmetic
      Take a, b for the second assertion.
*)
val prime_power_or_coprime_factors = store_thm(
  "prime_power_or_coprime_factors",
  ``!n. 1 < n ==> (?p k. 0 < k /\ prime p /\ (n = p ** k)) \/
                 (?a b. (n = a * b) /\ coprime a b /\ 1 < a /\ 1 < b /\ a < n /\ b < n)``,
  rpt strip_tac >>
  `0 < n /\ n <> 0 /\ n <> 1` by decide_tac >>
  `?p. prime p /\ p divides n` by rw[PRIME_FACTOR] >>
  `?k. 0 < k /\ p ** k divides n /\ coprime p (n DIV p ** k)` by metis_tac[FACTOR_OUT_PRIME, EXP_1] >>
  `0 < p ** k` by rw[PRIME_POS, EXP_POS] >>
  qabbrev_tac `b = n DIV p ** k` >>
  `n = (p ** k) * b` by rw[GSYM DIVIDES_EQN_COMM, Abbr`b`] >>
  Cases_on `b = 1` >-
  metis_tac[MULT_RIGHT_1] >>
  qabbrev_tac `a = p ** k` >>
  `coprime a b` by rw[coprime_exp, Abbr`a`] >>
  `a <> 1` by metis_tac[EXP_EQ_1, NOT_PRIME_1, NOT_ZERO_LT_ZERO] >>
  `b <> 0` by metis_tac[MULT_0] >>
  `a divides n /\ b divides n` by metis_tac[divides_def, MULT_COMM] >>
  `a <= n /\ b <= n` by rw[DIVIDES_LE] >>
  `a <> n /\ b <> n` by metis_tac[MULT_LEFT_ID, MULT_RIGHT_ID] >>
  `1 < a /\ 1 < b /\ a < n /\ b < n` by decide_tac >>
  metis_tac[]);

(* The following is the more powerful version of this:
   Simple theorem: If n is not a prime, then ?a b. (n = a * b) /\ 1 < a /\ a < n /\ 1 < b /\ b < n
   Powerful theorem: If n is not a prime power, then ?a b. (n = a * b) /\ 1 < a /\ a < n /\ 1 < b /\ b < n
*)

(* Theorem: 1 < n /\ ~(?p k. 0 < k /\ prime p /\ (n = p ** k)) ==>
            ?a b. (n = a * b) /\ coprime a b /\ 1 < a /\ a < n /\ 1 < b /\ b < n *)
(* Proof:
   Since 1 < n, n <> 1 and 0 < n                by arithmetic
    Note ?p. prime p /\ p divides n             by PRIME_FACTOR, n <> 1
     and ?m. 0 < m /\ p ** m divides n /\
         !k. coprime (p ** k) (n DIV p ** m)    by FACTOR_OUT_PRIME, 0 < n

   Let a = p ** m, b = n DIV a.
   Since 0 < p                                  by PRIME_POS
      so 0 < a                                  by EXP_POS, 0 < p
    Thus n = a * b                              by DIVIDES_EQN_COMM, 0 < a

    Also 1 < p                                  by ONE_LT_PRIME
      so 1 < a                                  by ONE_LT_EXP, 1 < p, 0 < m
     and b < n                                  by DIV_LESS, Abbr, 0 < n
     Now b <> 1                                 by MULT_RIGHT_1, n not perfect power of any prime
     and b <> 0                                 by MULT_0, n = a * b, 0 < n
     ==> 1 < b                                  by b <> 0 /\ b <> 1
    Also a <= n                                 by DIVIDES_LE
     and a <> n                                 by MULT_RIGHT_1
     ==> a < n                                  by arithmetic
    Take these a and b, the result follows.
*)
val non_prime_power_coprime_factors = store_thm(
  "non_prime_power_coprime_factors",
  ``!n. 1 < n /\ ~(?p k. 0 < k /\ prime p /\ (n = p ** k)) ==>
   ?a b. (n = a * b) /\ coprime a b /\ 1 < a /\ a < n /\ 1 < b /\ b < n``,
  rpt strip_tac >>
  `0 < n` by decide_tac >>
  `?p. prime p /\ p divides n` by rw[PRIME_FACTOR] >>
  `?m. 0 < m /\ p ** m divides n /\ !k. coprime (p ** k) (n DIV p ** m)` by rw[FACTOR_OUT_PRIME] >>
  qabbrev_tac `a = p ** m` >>
  qabbrev_tac `b = n DIV a` >>
  `0 < a` by rw[PRIME_POS, EXP_POS, Abbr`a`] >>
  `n = a * b` by metis_tac[DIVIDES_EQN_COMM] >>
  `1 < a` by rw[ONE_LT_EXP, ONE_LT_PRIME, Abbr`a`] >>
  `b < n` by rw[DIV_LESS, Abbr`b`] >>
  `b <> 1` by metis_tac[MULT_RIGHT_1] >>
  `b <> 0` by metis_tac[MULT_0, NOT_ZERO_LT_ZERO] >>
  `1 < b` by decide_tac >>
  `a <= n` by rw[DIVIDES_LE] >>
  `a <> n` by metis_tac[MULT_RIGHT_1] >>
  `a < n` by decide_tac >>
  metis_tac[]);

(* Theorem: s SUBSET prime ==> PAIRWISE_COPRIME (IMAGE (\p. p ** f p) s) *)
(* Proof:
   By SUBSET_DEF, this is to show:
      (!x. x IN s ==> prime x) /\ p IN s /\ p' IN s /\ p ** f <> p' ** f ==> coprime (p ** f) (p' ** f)
   Note prime p /\ prime p'          by in_prime
    and p <> p'                      by p ** f <> p' ** f
   Thus coprime (p ** f) (p' ** f)   by prime_powers_coprime
*)
val pairwise_coprime_for_prime_powers = store_thm(
  "pairwise_coprime_for_prime_powers",
  ``!s f. s SUBSET prime ==> PAIRWISE_COPRIME (IMAGE (\p. p ** f p) s)``,
  rw[SUBSET_DEF] >>
  `prime p /\ prime p' /\ p <> p'` by metis_tac[in_prime] >>
  rw[prime_powers_coprime]);

(* ------------------------------------------------------------------------- *)
(* Prime Power Index                                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < n /\ prime p ==> ?m. (p ** m) divides n /\ coprime p (n DIV (p ** m)) *)
(* Proof:
   Note ?q m. (n = (p ** m) * q) /\ coprime p q     by prime_power_factor
   Let t = p ** m.
   Then t divides n                                 by divides_def, MULT_COMM
    Now 0 < p                                       by PRIME_POS
     so 0 < t                                       by EXP_POS
    ==> n = t * (n DIV t)                           by DIVIDES_EQN_COMM
   Thus q = n DIV t                                 by MULT_LEFT_CANCEL
   Take this m, and the result follows.
*)
val prime_power_index_exists = store_thm(
  "prime_power_index_exists",
  ``!n p. 0 < n /\ prime p ==> ?m. (p ** m) divides n /\ coprime p (n DIV (p ** m))``,
  rpt strip_tac >>
  `?q m. (n = (p ** m) * q) /\ coprime p q` by rw[prime_power_factor] >>
  qabbrev_tac `t = p ** m` >>
  `t divides n` by metis_tac[divides_def, MULT_COMM] >>
  `0 < t` by rw[PRIME_POS, EXP_POS, Abbr`t`] >>
  metis_tac[DIVIDES_EQN_COMM, MULT_LEFT_CANCEL, NOT_ZERO_LT_ZERO]);

(* Apply Skolemization *)
val lemma = prove(
  ``!p n. ?m. 0 < n /\ prime p ==> (p ** m) divides n /\ coprime p (n DIV (p ** m))``,
  metis_tac[prime_power_index_exists]);
(* Note !p n, for first parameter p, second parameter n. *)
(*
- SKOLEM_THM;
> val it = |- !P. (!x. ?y. P x y) <=> ?f. !x. P x (f x) : thm
*)
(* Define prime power index *)
(*
- SIMP_RULE bool_ss [SKOLEM_THM] lemma;
> val it = |- ?f. !p n. 0 < n /\ prime p ==> p ** f p n divides n /\ coprime p (n DIV p ** f p n): thm
*)
val prime_power_index_def = new_specification(
    "prime_power_index_def",
    ["prime_power_index"],
    SIMP_RULE bool_ss [SKOLEM_THM] lemma);
(*
> val prime_power_index_def = |- !p n. 0 < n /\ prime p ==>
  p ** prime_power_index p n divides n /\ coprime p (n DIV p ** prime_power_index p n): thm
*)

(* Overload on prime_power_index of prime p *)
val _ = overload_on("ppidx", ``prime_power_index p``);

(*
> prime_power_index_def;
val it = |- !p n. 0 < n /\ prime p ==> p ** ppidx n divides n /\ coprime p (n DIV p ** ppidx n): thm
*)

(* Theorem: prime p ==> (p ** (ppidx n)) divides n *)
(* Proof: by prime_power_index_def, and ALL_DIVIDES_0 *)
val prime_power_factor_divides = store_thm(
  "prime_power_factor_divides",
  ``!n p. prime p ==> (p ** (ppidx n)) divides n``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  rw[prime_power_index_def]);

(* Theorem: 0 < n /\ prime p ==> coprime p (n DIV p ** ppidx n) *)
(* Proof: by prime_power_index_def *)
val prime_power_cofactor_coprime = store_thm(
  "prime_power_cofactor_coprime",
  ``!n p. 0 < n /\ prime p ==> coprime p (n DIV p ** ppidx n)``,
  rw[prime_power_index_def]);

(* Theorem: 0 < n /\ prime p ==> (n = p ** (ppidx n) * (n DIV p ** (ppidx n))) *)
(* Proof:
   Let q = p ** (ppidx n).
   Then q divides n             by prime_power_factor_divides
    But 0 < n ==> n <> 0,
     so q <> 0, or 0 < q        by ZERO_DIVIDES
   Thus n = q * (n DIV q)       by DIVIDES_EQN_COMM, 0 < q
*)
val prime_power_eqn = store_thm(
  "prime_power_eqn",
  ``!n p. 0 < n /\ prime p ==> (n = p ** (ppidx n) * (n DIV p ** (ppidx n)))``,
  rpt strip_tac >>
  qabbrev_tac `q = p ** (ppidx n)` >>
  `q divides n` by rw[prime_power_factor_divides, Abbr`q`] >>
  `0 < q` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  rw[GSYM DIVIDES_EQN_COMM]);

(* Theorem: 0 < n /\ prime p ==> !k. (p ** k) divides n <=> k <= (ppidx n) *)
(* Proof:
   Let m = ppidx n.
   Then p ** m divides n                      by prime_power_factor_divides
   If part: p ** k divides n ==> k <= m
      By contradiction, suppose m < k.
      Let q = n DIV p ** m.
      Then n = p ** m * q                     by prime_power_eqn
       ==> ?t. n = p ** k * t                 by divides_def, MULT_COMM
      Let d = k - m.
      Then 0 < d                              by m < k
       ==> p ** k = p ** m * p ** d           by EXP_BY_ADD_SUB_LT
       But 0 < p ** m                         by PRIME_POS, EXP_POS
        so p ** m <> 0                        by arithmetic
      Thus q = p ** d * t                     by MULT_LEFT_CANCEL, MULT_ASSOC
     Since p divides p ** d                   by prime_divides_self_power, 0 < d
        so p divides q                        by DIVIDES_MULT
        or gcd p q = p                        by divides_iff_gcd_fix
       But coprime p q                        by prime_power_cofactor_coprime
      This is a contradiction since p <> 1    by NOT_PRIME_1

   Only-if part: k <= m ==> p ** k divides n
     Note p ** m = p ** d * p ** k            by EXP_BY_ADD_SUB_LE, MULT_COMM
     Thus p ** k divides p ** m               by divides_def
      ==> p ** k divides n                    by DIVIDES_TRANS
*)

Theorem prime_power_divisibility:
  !n p. 0 < n /\ prime p ==> !k. (p ** k) divides n <=> k <= (ppidx n)
Proof
  rpt strip_tac >>
  qabbrev_tac `m = ppidx n` >>
  `p ** m divides n` by rw[prime_power_factor_divides, Abbr`m`] >>
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `m < k` by decide_tac >>
    qabbrev_tac `q = n DIV p ** m` >>
    `n = p ** m * q` by rw[prime_power_eqn, Abbr`m`, Abbr`q`] >>
    `?t. n = p ** k * t` by metis_tac[divides_def, MULT_COMM] >>
    `p ** k = p ** m * p ** (k - m)` by rw[EXP_BY_ADD_SUB_LT] >>
    `0 < k - m` by decide_tac >>
    qabbrev_tac `d = k - m` >>
    `0 < p ** m` by rw[PRIME_POS, EXP_POS] >>
    `p ** m <> 0` by decide_tac >>
    `q = p ** d * t` by metis_tac[MULT_LEFT_CANCEL, MULT_ASSOC] >>
    `p divides p ** d` by rw[prime_divides_self_power] >>
    `p divides q` by simp[DIVIDES_MULTIPLE] >>
    `gcd p q = p` by rw[GSYM divides_iff_gcd_fix] >>
    `coprime p q` by rw[GSYM prime_power_cofactor_coprime, Abbr`m`, Abbr`q`] >>
    metis_tac[NOT_PRIME_1],
    `p ** m = p ** (m - k) * p ** k` by rw[EXP_BY_ADD_SUB_LE, MULT_COMM] >>
    `p ** k divides p ** m` by metis_tac[divides_def] >>
    metis_tac[DIVIDES_TRANS]
  ]
QED

(* Theorem: 0 < n /\ prime p ==> !k. k > ppidx n ==> ~(p ** k divides n) *)
(* Proof: by prime_power_divisibility *)
val prime_power_index_maximal = store_thm(
  "prime_power_index_maximal",
  ``!n p. 0 < n /\ prime p ==> !k. k > ppidx n ==> ~(p ** k divides n)``,
  rw[prime_power_divisibility]);

(* Theorem: 0 < n /\ m divides n ==> !p. prime p ==> ppidx m <= ppidx n *)
(* Proof:
   Note 0 < m                      by ZERO_DIVIDES, 0 < n
   Thus p ** ppidx m divides m     by prime_power_factor_divides, 0 < m
    ==> p ** ppidx m divides n     by DIVIDES_TRANS
     or ppidx m <= ppidx n         by prime_power_divisibility, 0 < n
*)
val prime_power_index_of_divisor = store_thm(
  "prime_power_index_of_divisor",
  ``!m n. 0 < n /\ m divides n ==> !p. prime p ==> ppidx m <= ppidx n``,
  rpt strip_tac >>
  `0 < m` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `p ** ppidx m divides m` by rw[prime_power_factor_divides] >>
  `p ** ppidx m divides n` by metis_tac[DIVIDES_TRANS] >>
  rw[GSYM prime_power_divisibility]);

(* Theorem: 0 < n /\ prime p ==> !k. (k = ppidx n) <=> (?q. (n = p ** k * q) /\ coprime p q) *)
(* Proof:
   If part: k = ppidx n ==> ?q. (n = p ** k * q) /\ coprime p q
      Let q = n DIV p ** k, where k = ppidx n.
      Then n = p ** k * q           by prime_power_eqn
       and coprime p q              by prime_power_cofactor_coprime
   Only-if part: n = p ** k * q /\ coprime p q ==> k = ppidx n
      Note n = p ** (ppidx n) * q   by prime_power_eqn

      Thus p ** k divides n         by divides_def, MULT_COMM
       ==> k <= ppidx n             by prime_power_divisibility

      Claim: ppidx n <= k
      Proof: By contradiction, suppose k < ppidx n.
             Let d = ppidx n - k, then 0 < d.
             Let nq = n DIV p ** (ppidx n).
             Then n = p ** (ppidx n) * nq              by prime_power_eqn
             Note p ** ppidx n = p ** k * p ** d       by EXP_BY_ADD_SUB_LT
              Now 0 < p ** k                           by PRIME_POS, EXP_POS
               so q = p ** d * nq                      by MULT_LEFT_CANCEL, MULT_ASSOC, p ** k <> 0
              But p divides p ** d                     by prime_divides_self_power, 0 < d
              and p ** d divides q                     by divides_def, MULT_COMM
              ==> p divides q                          by DIVIDES_TRANS
               or gcd p q = p                          by divides_iff_gcd_fix
              This contradicts coprime p q as p <> 1   by NOT_PRIME_1

      With k <= ppidx n and ppidx n <= k, k = ppidx n  by LESS_EQUAL_ANTISYM
*)
val prime_power_index_test = store_thm(
  "prime_power_index_test",
  ``!n p. 0 < n /\ prime p ==> !k. (k = ppidx n) <=> (?q. (n = p ** k * q) /\ coprime p q)``,
  rw_tac std_ss[EQ_IMP_THM] >-
  metis_tac[prime_power_eqn, prime_power_cofactor_coprime] >>
  qabbrev_tac `n = p ** k * q` >>
  `p ** k divides n` by metis_tac[divides_def, MULT_COMM] >>
  `k <= ppidx n` by rw[GSYM prime_power_divisibility] >>
  `ppidx n <= k` by
  (spose_not_then strip_assume_tac >>
  `k < ppidx n /\ 0 < ppidx n - k` by decide_tac >>
  `p ** ppidx n = p ** k * p ** (ppidx n - k)` by rw[EXP_BY_ADD_SUB_LT] >>
  qabbrev_tac `d = ppidx n - k` >>
  qabbrev_tac `nq = n DIV p ** (ppidx n)` >>
  `n = p ** (ppidx n) * nq` by rw[prime_power_eqn, Abbr`nq`] >>
  `0 < p ** k` by rw[PRIME_POS, EXP_POS] >>
  `q = p ** d * nq` by metis_tac[MULT_LEFT_CANCEL, MULT_ASSOC, NOT_ZERO_LT_ZERO] >>
  `p divides p ** d` by rw[prime_divides_self_power] >>
  `p ** d divides q` by metis_tac[divides_def, MULT_COMM] >>
  `p divides q` by metis_tac[DIVIDES_TRANS] >>
  `gcd p q = p` by rw[GSYM divides_iff_gcd_fix] >>
  metis_tac[NOT_PRIME_1]) >>
  decide_tac);

(* Theorem: prime p ==> (ppidx 1 = 0) *)
(* Proof:
   Note 1 = p ** 0 * 1      by EXP, MULT_RIGHT_1
    and coprime p 1         by GCD_1
     so ppidx 1 = 0         by prime_power_index_test, 0 < 1
*)
val prime_power_index_1 = store_thm(
  "prime_power_index_1",
  ``!p. prime p ==> (ppidx 1 = 0)``,
  rpt strip_tac >>
  `1 = p ** 0 * 1` by rw[] >>
  `coprime p 1` by rw[GCD_1] >>
  metis_tac[prime_power_index_test, DECIDE``0 < 1``]);

(* Theorem: 0 < n /\ prime p /\ ~(p divides n) ==> (ppidx n = 0) *)
(* Proof:
   By contradiction, suppose ppidx n <> 0.
   Then 0 < ppidx n              by NOT_ZERO_LT_ZERO
   Note p ** ppidx n divides n   by prime_power_index_def, 0 < n
    and 1 < p                    by ONE_LT_PRIME
     so p divides p ** ppidx n   by divides_self_power, 0 < n, 1 < p
    ==> p divides n              by DIVIDES_TRANS
   This contradicts ~(p divides n).
*)
val prime_power_index_eq_0 = store_thm(
  "prime_power_index_eq_0",
  ``!n p. 0 < n /\ prime p /\ ~(p divides n) ==> (ppidx n = 0)``,
  spose_not_then strip_assume_tac >>
  `p ** ppidx n divides n` by rw[prime_power_index_def] >>
  `p divides p ** ppidx n` by rw[divides_self_power, ONE_LT_PRIME] >>
  metis_tac[DIVIDES_TRANS]);

(* Theorem: prime p ==> (ppidx (p ** k) = k) *)
(* Proof:
   Note p ** k = p ** k * 1   by EXP, MULT_RIGHT_1
    and coprime p 1           by GCD_1
    Now 0 < p ** k            by PRIME_POS, EXP_POS
     so ppidx (p ** k) = k    by prime_power_index_test, 0 < p ** k
*)
val prime_power_index_prime_power = store_thm(
  "prime_power_index_prime_power",
  ``!p. prime p ==> !k. ppidx (p ** k) = k``,
  rpt strip_tac >>
  `p ** k = p ** k * 1` by rw[] >>
  `coprime p 1` by rw[GCD_1] >>
  `0 < p ** k` by rw[PRIME_POS, EXP_POS] >>
  metis_tac[prime_power_index_test]);

(* Theorem: prime p ==> (ppidx p = 1) *)
(* Proof:
   Note 0 < p             by PRIME_POS
    and p = p ** 1 * 1    by EXP_1, MULT_RIGHT_1
    and coprime p 1       by GCD_1
     so ppidx p = 1       by prime_power_index_test
*)
val prime_power_index_prime = store_thm(
  "prime_power_index_prime",
  ``!p. prime p ==> (ppidx p = 1)``,
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  `p = p ** 1 * 1` by rw[] >>
  metis_tac[prime_power_index_test, GCD_1]);

(* Theorem: 0 < n /\ prime p ==> let q = n DIV (p ** ppidx n) in (n = p ** ppidx n * q) /\ (coprime p q) *)
(* Proof:
   This is to show:
   (1) n = p ** ppidx n * q
       Note p ** ppidx n divides n      by prime_power_index_def
        Now 0 < p                       by PRIME_POS
         so 0 < p ** ppidx n            by EXP_POS
        ==> n = p ** ppidx n * q        by DIVIDES_EQN_COMM, 0 < p ** ppidx n
   (2) coprime p q, true                by prime_power_index_def
*)
val prime_power_index_eqn = store_thm(
  "prime_power_index_eqn",
  ``!n p. 0 < n /\ prime p ==> let q = n DIV (p ** ppidx n) in (n = p ** ppidx n * q) /\ (coprime p q)``,
  metis_tac[prime_power_index_def, PRIME_POS, EXP_POS, DIVIDES_EQN_COMM]);

(* Theorem: 0 < n /\ prime p /\ p divides n ==> 0 < ppidx n *)
(* Proof:
   By contradiction, suppose ~(0 < ppidx n).
   Then ppidx n = 0                       by NOT_ZERO_LT_ZERO
   Note ?q. coprime p q /\
            n = p ** ppidx n * q          by prime_power_index_eqn
              = p ** 0 * q                by ppidx n = 0
              = 1 * q                     by EXP_0
              = q                         by MULT_LEFT_1
    But 1 < p                             by ONE_LT_PRIME
    and coprime p q ==> ~(p divides q)    by coprime_not_divides
    This contradicts p divides q          by p divides n, n = q
*)
val prime_power_index_pos = store_thm(
  "prime_power_index_pos",
  ``!n p. 0 < n /\ prime p /\ p divides n ==> 0 < ppidx n``,
  spose_not_then strip_assume_tac >>
  `ppidx n = 0` by decide_tac >>
  `?q. coprime p q /\ (n = p ** ppidx n * q)` by metis_tac[prime_power_index_eqn] >>
  `_ = q` by rw[] >>
  metis_tac[coprime_not_divides, ONE_LT_PRIME]);

(* ------------------------------------------------------------------------- *)
(* Prime Power and GCD, LCM                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < a /\ 0 < b /\ prime p ==>
            (gcd a b = p ** MIN (ppidx a) (ppidx b) * gcd (a DIV p ** (ppidx a)) (b DIV p ** (ppidx b))) *)
(* Proof:
   Let ma = ppidx a, qa = a DIV p ** ma.
   Let mb = ppidx b, qb = b DIV p ** mb.
   Then coprime p qa                       by prime_power_cofactor_coprime
    and coprime p qb                       by prime_power_cofactor_coprime
   Also a = p ** ma * qa                   by prime_power_eqn
    and b = p ** mb * qb                   by prime_power_eqn

   If ma < mb, let d = mb - ma.
      Then p ** mb = p ** ma * p ** d      by EXP_BY_ADD_SUB_LT
       and coprime (p ** d) qa             by coprime_exp
           gcd a b
         = p ** ma * gcd qa (p ** d * qb)  by GCD_COMMON_FACTOR, MULT_ASSOC
         = p ** ma * gcd qa qb             by gcd_coprime_cancel, GCD_SYM, coprime (p ** d) qa
         = p ** (MIN ma mb) * gcd qa qb    by MIN_DEF

   If ~(ma < mb), let d = ma - mb.
      Then p ** ma = p ** mb * p ** d      by EXP_BY_ADD_SUB_LE
       and coprime (p ** d) qb             by coprime_exp
           gcd a b
         = p ** mb * gcd (p ** d * qa) qb  by GCD_COMMON_FACTOR, MULT_ASSOC
         = p ** mb * gcd qa qb             by gcd_coprime_cancel, coprime (p ** d) qb
         = p ** (MIN ma mb) * gcd qa qb    by MIN_DEF
*)
val gcd_prime_power_factor = store_thm(
  "gcd_prime_power_factor",
  ``!a b p. 0 < a /\ 0 < b /\ prime p ==>
    (gcd a b = p ** MIN (ppidx a) (ppidx b) * gcd (a DIV p ** (ppidx a)) (b DIV p ** (ppidx b)))``,
  rpt strip_tac >>
  qabbrev_tac `ma = ppidx a` >>
  qabbrev_tac `qa = a DIV p ** ma` >>
  qabbrev_tac `mb = ppidx b` >>
  qabbrev_tac `qb = b DIV p ** mb` >>
  `coprime p qa` by rw[prime_power_cofactor_coprime, Abbr`ma`, Abbr`qa`] >>
  `coprime p qb` by rw[prime_power_cofactor_coprime, Abbr`mb`, Abbr`qb`] >>
  `a = p ** ma * qa` by rw[prime_power_eqn, Abbr`ma`, Abbr`qa`] >>
  `b = p ** mb * qb` by rw[prime_power_eqn, Abbr`mb`, Abbr`qb`] >>
  Cases_on `ma < mb` >| [
    `p ** mb = p ** ma * p ** (mb - ma)` by rw[EXP_BY_ADD_SUB_LT] >>
    qabbrev_tac `d = mb - ma` >>
    `coprime (p ** d) qa` by rw[coprime_exp] >>
    `gcd a b = p ** ma * gcd qa (p ** d * qb)` by metis_tac[GCD_COMMON_FACTOR, MULT_ASSOC] >>
    `_ = p ** ma * gcd qa qb` by metis_tac[gcd_coprime_cancel, GCD_SYM] >>
    rw[MIN_DEF],
    `p ** ma = p ** mb * p ** (ma - mb)` by rw[EXP_BY_ADD_SUB_LE] >>
    qabbrev_tac `d = ma - mb` >>
    `coprime (p ** d) qb` by rw[coprime_exp] >>
    `gcd a b = p ** mb * gcd (p ** d * qa) qb` by metis_tac[GCD_COMMON_FACTOR, MULT_ASSOC] >>
    `_ = p ** mb * gcd qa qb` by rw[gcd_coprime_cancel] >>
    rw[MIN_DEF]
  ]);

(* Theorem: 0 < a /\ 0 < b /\ prime p ==> (p ** MIN (ppidx a) (ppidx b)) divides (gcd a b) *)
(* Proof: by gcd_prime_power_factor, divides_def *)
val gcd_prime_power_factor_divides_gcd = store_thm(
  "gcd_prime_power_factor_divides_gcd",
  ``!a b p. 0 < a /\ 0 < b /\ prime p ==> (p ** MIN (ppidx a) (ppidx b)) divides (gcd a b)``,
  prove_tac[gcd_prime_power_factor, divides_def, MULT_COMM]);

(* Theorem: 0 < a /\ 0 < b /\ prime p ==> coprime p (gcd (a DIV p ** (ppidx a)) (b DIV p ** (ppidx b))) *)
(* Proof:
   Let ma = ppidx a, qa = a DIV p ** ma.
   Let mb = ppidx b, qb = b DIV p ** mb.
   Then coprime p qa             by prime_power_cofactor_coprime
       gcd p (gcd qa qb)
     = gcd (gcd p qa) qb         by GCD_ASSOC
     = gcd 1 qb                  by coprime p qa
     = 1                         by GCD_1
*)
val gcd_prime_power_cofactor_coprime = store_thm(
  "gcd_prime_power_cofactor_coprime",
  ``!a b p. 0 < a /\ 0 < b /\ prime p ==> coprime p (gcd (a DIV p ** (ppidx a)) (b DIV p ** (ppidx b)))``,
  rw[prime_power_cofactor_coprime, GCD_ASSOC, GCD_1]);

(* Theorem: 0 < a /\ 0 < b /\ prime p ==> (ppidx (gcd a b) = MIN (ppidx a) (ppidx b)) *)
(* Proof:
   Let ma = ppidx a, qa = a DIV p ** ma.
   Let mb = ppidx b, qb = b DIV p ** mb.
   Let m = MIN ma mb.
   Then gcd a b = p ** m * (gcd qa qb)     by gcd_prime_power_factor
   Note 0 < gcd a b                        by GCD_POS
    and coprime p (gcd qa qb)              by gcd_prime_power_cofactor_coprime
   Thus ppidx (gcd a b) = m                by prime_power_index_test
*)
val gcd_prime_power_index = store_thm(
  "gcd_prime_power_index",
  ``!a b p. 0 < a /\ 0 < b /\ prime p ==> (ppidx (gcd a b) = MIN (ppidx a) (ppidx b))``,
  metis_tac[gcd_prime_power_factor, GCD_POS, prime_power_index_test, gcd_prime_power_cofactor_coprime]);

(* Theorem: 0 < a /\ 0 < b /\ prime p ==> !k. p ** k divides gcd a b ==> k <= MIN (ppidx a) (ppidx b) *)
(* Proof:
   Note 0 < gcd a b                     by GCD_POS
   Thus k <= ppidx (gcd a b)            by prime_power_divisibility
     or k <= MIN (ppidx a) (ppidx b)    by gcd_prime_power_index
*)
val gcd_prime_power_divisibility = store_thm(
  "gcd_prime_power_divisibility",
  ``!a b p. 0 < a /\ 0 < b /\ prime p ==> !k. p ** k divides gcd a b ==> k <= MIN (ppidx a) (ppidx b)``,
  metis_tac[GCD_POS, prime_power_divisibility, gcd_prime_power_index]);

(* Theorem: 0 < a /\ 0 < b /\ prime p ==>
            (lcm a b = p ** MAX (ppidx a) (ppidx b) * lcm (a DIV p ** (ppidx a)) (b DIV p ** (ppidx b))) *)
(* Proof:
   Let ma = ppidx a, qa = a DIV p ** ma.
   Let mb = ppidx b, qb = b DIV p ** mb.
   Then coprime p qa                       by prime_power_cofactor_coprime
    and coprime p qb                       by prime_power_cofactor_coprime
   Also a = p ** ma * qa                   by prime_power_eqn
    and b = p ** mb * qb                   by prime_power_eqn
   Note (gcd a b) * (lcm a b) = a * b      by GCD_LCM
    and gcd qa qb <> 0                     by GCD_EQ_0, MULT_0, 0 < a, 0 < b.

   If ma < mb,
      Then gcd a b = p ** ma * gcd qa qb              by gcd_prime_power_factor, MIN_DEF
       and a * b = (p ** ma * qa) * (p ** mb * qb)    by above
      Note p ** ma <> 0                               by MULT, 0 < a = p ** ma * qa
           gcd qa qb * lcm a b
         = qa * (p ** mb * qb)                        by MULT_LEFT_CANCEL, MULT_ASSOC
         = qa * qb * (p ** mb)                        by MULT_ASSOC_COMM
         = gcd qa qb * lcm qa qb * (p ** mb)          by GCD_LCM
      Thus lcm a b = lcm qa qb * p ** mb              by MULT_LEFT_CANCEL, MULT_ASSOC
                   = p ** mb * lcm qa qb              by MULT_COMM
                   = p ** (MAX ma mb) * lcm qa qb     by MAX_DEF

   If ~(ma < mb),
      Then gcd a b = p ** mb * gcd qa qb              by gcd_prime_power_factor, MIN_DEF
       and a * b = (p ** mb * qb) * (p ** ma * qa)    by MULT_COMM
      Note p ** mb <> 0                               by MULT, 0 < b = p ** mb * qb
           gcd qa qb * lcm a b
         = qb * (p ** ma * qa)                        by MULT_LEFT_CANCEL, MULT_ASSOC
         = qa * qb * (p ** ma)                        by MULT_ASSOC_COMM, MULT_COMM
         = gcd qa qb * lcm qa qb * (p ** ma)          by GCD_LCM
      Thus lcm a b = lcm qa qb * p ** ma              by MULT_LEFT_CANCEL, MULT_ASSOC
                   = p ** ma * lcm qa qb              by MULT_COMM
                   = p ** (MAX ma mb) * lcm qa qb     by MAX_DEF
*)
val lcm_prime_power_factor = store_thm(
  "lcm_prime_power_factor",
  ``!a b p. 0 < a /\ 0 < b /\ prime p ==>
    (lcm a b = p ** MAX (ppidx a) (ppidx b) * lcm (a DIV p ** (ppidx a)) (b DIV p ** (ppidx b)))``,
  rpt strip_tac >>
  qabbrev_tac `ma = ppidx a` >>
  qabbrev_tac `qa = a DIV p ** ma` >>
  qabbrev_tac `mb = ppidx b` >>
  qabbrev_tac `qb = b DIV p ** mb` >>
  `coprime p qa` by rw[prime_power_cofactor_coprime, Abbr`ma`, Abbr`qa`] >>
  `coprime p qb` by rw[prime_power_cofactor_coprime, Abbr`mb`, Abbr`qb`] >>
  `a = p ** ma * qa` by rw[prime_power_eqn, Abbr`ma`, Abbr`qa`] >>
  `b = p ** mb * qb` by rw[prime_power_eqn, Abbr`mb`, Abbr`qb`] >>
  `(gcd a b) * (lcm a b) = a * b` by rw[GCD_LCM] >>
  `gcd qa qb <> 0` by metis_tac[GCD_EQ_0, MULT_0, NOT_ZERO_LT_ZERO] >>
  Cases_on `ma < mb` >| [
    `gcd a b = p ** ma * gcd qa qb` by metis_tac[gcd_prime_power_factor, MIN_DEF] >>
    `a * b = (p ** ma * qa) * (p ** mb * qb)` by rw[] >>
    `p ** ma <> 0` by metis_tac[MULT, NOT_ZERO_LT_ZERO] >>
    `gcd qa qb * lcm a b = qa * (p ** mb * qb)` by metis_tac[MULT_LEFT_CANCEL, MULT_ASSOC] >>
    `_ = qa * qb * (p ** mb)` by rw[MULT_ASSOC_COMM] >>
    `_ = gcd qa qb * lcm qa qb * (p ** mb)` by metis_tac[GCD_LCM] >>
    `lcm a b = lcm qa qb * p ** mb` by metis_tac[MULT_LEFT_CANCEL, MULT_ASSOC] >>
    rw[MAX_DEF, Once MULT_COMM],
    `gcd a b = p ** mb * gcd qa qb` by metis_tac[gcd_prime_power_factor, MIN_DEF] >>
    `a * b = (p ** mb * qb) * (p ** ma * qa)` by rw[Once MULT_COMM] >>
    `p ** mb <> 0` by metis_tac[MULT, NOT_ZERO_LT_ZERO] >>
    `gcd qa qb * lcm a b = qb * (p ** ma * qa)` by metis_tac[MULT_LEFT_CANCEL, MULT_ASSOC] >>
    `_ = qa * qb * (p ** ma)` by rw[MULT_ASSOC_COMM, Once MULT_COMM] >>
    `_ = gcd qa qb * lcm qa qb * (p ** ma)` by metis_tac[GCD_LCM] >>
    `lcm a b = lcm qa qb * p ** ma` by metis_tac[MULT_LEFT_CANCEL, MULT_ASSOC] >>
    rw[MAX_DEF, Once MULT_COMM]
  ]);

(* The following is the two-number version of prime_power_factor_divides *)

(* Theorem: 0 < a /\ 0 < b /\ prime p ==> (p ** MAX (ppidx a) (ppidx b)) divides (lcm a b) *)
(* Proof: by lcm_prime_power_factor, divides_def *)
val lcm_prime_power_factor_divides_lcm = store_thm(
  "lcm_prime_power_factor_divides_lcm",
  ``!a b p. 0 < a /\ 0 < b /\ prime p ==> (p ** MAX (ppidx a) (ppidx b)) divides (lcm a b)``,
  prove_tac[lcm_prime_power_factor, divides_def, MULT_COMM]);

(* Theorem: 0 < a /\ 0 < b /\ prime p ==> coprime p (lcm (a DIV p ** ppidx a) (b DIV p ** ppidx b)) *)
(* Proof:
   Let ma = ppidx a, qa = a DIV p ** ma.
   Let mb = ppidx b, qb = b DIV p ** mb.
   Then coprime p qa                   by prime_power_cofactor_coprime
    and coprime p qb                   by prime_power_cofactor_coprime

   Simple if we have: gcd_over_lcm: gcd x (lcm y z) = lcm (gcd x y) (gcd x z)
   But we don't, so use another approach.

   Note 1 < p                          by ONE_LT_PRIME
   Let d = gcd p (lcm qa qb).
   By contradiction, assume d <> 1.
   Note d divides p                    by GCD_IS_GREATEST_COMMON_DIVISOR
     so d = p                          by prime_def, d <> 1
     or p divides lcm qa qb            by divides_iff_gcd_fix, gcd p (lcm qa qb) = d = p
    But (lcm qa qb) divides (qa * qb)  by GCD_LCM, divides_def
     so p divides qa * qb              by DIVIDES_TRANS
    ==> p divides qa or p divides qb   by P_EUCLIDES
    This contradicts coprime p qa
                 and coprime p qb      by coprime_not_divides, 1 < p
*)
val lcm_prime_power_cofactor_coprime = store_thm(
  "lcm_prime_power_cofactor_coprime",
  ``!a b p. 0 < a /\ 0 < b /\ prime p ==> coprime p (lcm (a DIV p ** ppidx a) (b DIV p ** ppidx b))``,
  rpt strip_tac >>
  qabbrev_tac `ma = ppidx a` >>
  qabbrev_tac `mb = ppidx b` >>
  qabbrev_tac `qa = a DIV p ** ma` >>
  qabbrev_tac `qb = b DIV p ** mb` >>
  `coprime p qa` by rw[prime_power_cofactor_coprime, Abbr`ma`, Abbr`qa`] >>
  `coprime p qb` by rw[prime_power_cofactor_coprime, Abbr`mb`, Abbr`qb`] >>
  spose_not_then strip_assume_tac >>
  qabbrev_tac `d = gcd p (lcm qa qb)` >>
  `d divides p` by rw[GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
  `d = p` by metis_tac[prime_def] >>
  `p divides lcm qa qb` by rw[divides_iff_gcd_fix, Abbr`d`] >>
  `(lcm qa qb) divides (qa * qb)` by metis_tac[GCD_LCM, divides_def] >>
  `p divides qa * qb` by metis_tac[DIVIDES_TRANS] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  metis_tac[P_EUCLIDES, coprime_not_divides]);

(* Theorem: 0 < a /\ 0 < b /\ prime p ==> (ppidx (lcm a b) = MAX (ppidx a) (ppidx b)) *)
(* Proof:
   Let ma = ppidx a, qa = a DIV p ** ma.
   Let mb = ppidx b, qb = b DIV p ** mb.
   Let m = MAX ma mb.
   Then lcm a b = p ** m * (lcm qa qb)     by lcm_prime_power_factor
   Note 0 < lcm a b                        by LCM_POS
    and coprime p (lcm qa qb)              by lcm_prime_power_cofactor_coprime
     so ppidx (lcm a b) = m                by prime_power_index_test
*)
val lcm_prime_power_index = store_thm(
  "lcm_prime_power_index",
  ``!a b p. 0 < a /\ 0 < b /\ prime p ==> (ppidx (lcm a b) = MAX (ppidx a) (ppidx b))``,
  metis_tac[lcm_prime_power_factor, LCM_POS, lcm_prime_power_cofactor_coprime, prime_power_index_test]);

(* Theorem: 0 < a /\ 0 < b /\ prime p ==> !k. p ** k divides lcm a b ==> k <= MAX (ppidx a) (ppidx b) *)
(* Proof:
   Note 0 < lcm a b                     by LCM_POS
     so k <= ppidx (lcm a b)            by prime_power_divisibility
     or k <= MAX (ppidx a) (ppidx b)    by lcm_prime_power_index
*)
val lcm_prime_power_divisibility = store_thm(
  "lcm_prime_power_divisibility",
  ``!a b p. 0 < a /\ 0 < b /\ prime p ==> !k. p ** k divides lcm a b ==> k <= MAX (ppidx a) (ppidx b)``,
  metis_tac[LCM_POS, prime_power_divisibility, lcm_prime_power_index]);

(* ------------------------------------------------------------------------- *)
(* Prime Powers and List LCM                                                 *)
(* ------------------------------------------------------------------------- *)

(*
If a prime-power divides a list_lcm, the prime-power must divides some element in the list for list_lcm.
Note: this is not true for non-prime-power.
*)

(* Theorem: prime p ==> p ** (MAX_LIST (MAP (ppidx) l)) divides list_lcm l *)
(* Proof:
   If l = [],
         p ** MAX_LIST (MAP ppidx [])
       = p ** MAX_LIST []              by MAP
       = p ** 0                        by MAX_LIST_NIL
       = 1
       Hence true                      by ONE_DIVIDES_ALL
       In fact, list_lcm [] = 1        by list_lcm_nil
   If l <> [],
      Let ml = MAP ppidx l.
      Then ml <> []                                 by MAP_EQ_NIL
       ==> MEM (MAX_LIST ml) ml                     by MAX_LIST_MEM, ml <> []
        so ?x. (MAX_LIST ml = ppidx x) /\ MEM x l   by MEM_MAP
      Thus p ** ppidx x divides x                   by prime_power_factor_divides
       Now x divides list_lcm l                     by list_lcm_is_common_multiple
        so p ** (ppidx x)
         = p ** (MAX_LIST ml) divides list_lcm l    by DIVIDES_TRANS
*)
val list_lcm_prime_power_factor_divides = store_thm(
  "list_lcm_prime_power_factor_divides",
  ``!l p. prime p ==> p ** (MAX_LIST (MAP (ppidx) l)) divides list_lcm l``,
  rpt strip_tac >>
  Cases_on `l = []` >-
  rw[MAX_LIST_NIL] >>
  qabbrev_tac `ml = MAP ppidx l` >>
  `ml <> []` by rw[Abbr`ml`] >>
  `MEM (MAX_LIST ml) ml` by rw[MAX_LIST_MEM] >>
  `?x. (MAX_LIST ml = ppidx x) /\ MEM x l` by metis_tac[MEM_MAP] >>
  `p ** ppidx x divides x` by rw[prime_power_factor_divides] >>
  `x divides list_lcm l` by rw[list_lcm_is_common_multiple] >>
  metis_tac[DIVIDES_TRANS]);

(* Theorem: prime p /\ POSITIVE l ==> (ppidx (list_lcm l) = MAX_LIST (MAP ppidx l)) *)
(* Proof:
   By induction on l.
   Base: ppidx (list_lcm []) = MAX_LIST (MAP ppidx [])
         ppidx (list_lcm [])
       = ppidx 1                      by list_lcm_nil
       = 0                            by prime_power_index_1
       = MAX_LIST []                  by MAX_LIST_NIL
       = MAX_LIST (MAP ppidx [])      by MAP

   Step: ppidx (list_lcm l) = MAX_LIST (MAP ppidx l) ==>
         ppidx (list_lcm (h::l)) = MAX_LIST (MAP ppidx (h::l))
       Note 0 < list_lcm l                           by list_lcm_pos, EVERY_MEM
         ppidx (list_lcm (h::l))
       = ppidx (lcm h (list_lcm l))                  by list_lcm_cons
       = MAX (ppidx h) (ppidx (list_lcm l))          by lcm_prime_power_index, 0 < list_lcm l
       = MAX (ppidx h) (MAX_LIST (MAP ppidx l))      by induction hypothesis
       = MAX_LIST (ppidx h :: MAP ppidx l)           by MAX_LIST_CONS
       = MAX_LIST (MAP ppidx (h::l))                 by MAP
*)
val list_lcm_prime_power_index = store_thm(
  "list_lcm_prime_power_index",
  ``!l p. prime p /\ POSITIVE l ==> (ppidx (list_lcm l) = MAX_LIST (MAP ppidx l))``,
  Induct >-
  rw[prime_power_index_1] >>
  rpt strip_tac >>
  `0 < list_lcm l` by rw[list_lcm_pos, EVERY_MEM] >>
  `ppidx (list_lcm (h::l)) = ppidx (lcm h (list_lcm l))` by rw[list_lcm_cons] >>
  `_ = MAX (ppidx h) (ppidx (list_lcm l))` by rw[lcm_prime_power_index] >>
  `_ = MAX (ppidx h) (MAX_LIST (MAP ppidx l))` by rw[] >>
  `_ = MAX_LIST (ppidx h :: MAP ppidx l)` by rw[MAX_LIST_CONS] >>
  `_ = MAX_LIST (MAP ppidx (h::l))` by rw[] >>
  rw[]);

(* Theorem: prime p /\ POSITIVE l ==>
            !k. p ** k divides list_lcm l ==> k <= MAX_LIST (MAP ppidx l) *)
(* Proof:
   Note 0 < list_lcm l                by list_lcm_pos, EVERY_MEM
     so k <= ppidx (list_lcm l)       by prime_power_divisibility
     or k <= MAX_LIST (MAP ppidx l)   by list_lcm_prime_power_index
*)
val list_lcm_prime_power_divisibility = store_thm(
  "list_lcm_prime_power_divisibility",
  ``!l p. prime p /\ POSITIVE l ==>
   !k. p ** k divides list_lcm l ==> k <= MAX_LIST (MAP ppidx l)``,
  rpt strip_tac >>
  `0 < list_lcm l` by rw[list_lcm_pos, EVERY_MEM] >>
  metis_tac[prime_power_divisibility, list_lcm_prime_power_index]);

(* Theorem: prime p /\ l <> [] /\ POSITIVE l ==>
            !k. p ** k divides list_lcm l ==> ?x. MEM x l /\ p ** k divides x *)
(* Proof:
   Let ml = MAP ppidx l.

   Step 1: Get member x that attains ppidx x = MAX_LIST ml
   Note ml <> []                                  by MAP_EQ_NIL
   Then MEM (MAX_LIST ml) ml                      by MAX_LIST_MEM, ml <> []
    ==> ?x. (MAX_LIST ml = ppidx x) /\ MEM x l    by MEM_MAP

   Step 2: Show that this is a suitable x
   Note p ** k divides list_lcm l                 by given
    ==> k <= MAX_LIST ml                          by list_lcm_prime_power_divisibility
    Now 1 < p                                     by ONE_LT_PRIME
     so p ** k divides p ** (MAX_LIST ml)         by power_divides_iff, 1 < p
    and p ** (ppidx x) divides x                  by prime_power_factor_divides
   Thus p ** k divides x                          by DIVIDES_TRANS

   Take this x, and the result follows.
*)
val list_lcm_prime_power_factor_member = store_thm(
  "list_lcm_prime_power_factor_member",
  ``!l p. prime p /\ l <> [] /\ POSITIVE l ==>
   !k. p ** k divides list_lcm l ==> ?x. MEM x l /\ p ** k divides x``,
  rpt strip_tac >>
  qabbrev_tac `ml = MAP ppidx l` >>
  `ml <> []` by rw[Abbr`ml`] >>
  `MEM (MAX_LIST ml) ml` by rw[MAX_LIST_MEM] >>
  `?x. (MAX_LIST ml = ppidx x) /\ MEM x l` by metis_tac[MEM_MAP] >>
  `k <= MAX_LIST ml` by rw[list_lcm_prime_power_divisibility, Abbr`ml`] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `p ** k divides p ** (MAX_LIST ml)` by rw[power_divides_iff] >>
  `p ** (ppidx x) divides x` by rw[prime_power_factor_divides] >>
  metis_tac[DIVIDES_TRANS]);

(* Theorem: prime p ==> !m n. (n = p ** SUC (ppidx m)) ==> (lcm n m = p * m) *)
(* Proof:
   If m = 0,
      lcm n 0 = 0           by LCM_0
              = p * 0       by MULT_0
   If m <> 0, then 0 < m.
      Note 0 < n            by PRIME_POS, EXP_POS
      Let nq = n DIV p ** (ppidx n), mq = m DIV p ** (ppidx m).
      Let k = ppidx m.
      Note ppidx n = SUC k  by prime_power_index_prime_power
       and nq = 1           by DIVMOD_ID
       Now MAX (ppidx n) (ppidx m)
         = MAX (SUC k) k              by above
         = SUC k                      by MAX_DEF

           lcm n m
         = p ** MAX (ppidx n) (ppidx m) * (lcm nq mq)    by lcm_prime_power_factor
         = p ** (SUC k) * (lcm 1 mq)                     by above
         = p ** (SUC k) * mq                             by LCM_1
         = p * p ** k * mq                               by EXP
         = p * (p ** k * mq)                             by MULT_ASSOC
         = p * m                                         by prime_power_eqn
*)
val lcm_special_for_prime_power = store_thm(
  "lcm_special_for_prime_power",
  ``!p. prime p ==> !m n. (n = p ** SUC (ppidx m)) ==> (lcm n m = p * m)``,
  rpt strip_tac >>
  Cases_on `m = 0` >-
  rw[] >>
  `0 < m` by decide_tac >>
  `0 < n` by rw[PRIME_POS, EXP_POS] >>
  qabbrev_tac `k = ppidx m` >>
  `ppidx n = SUC k` by rw[prime_power_index_prime_power] >>
  `MAX (SUC k) k = SUC k` by rw[MAX_DEF] >>
  qabbrev_tac `mq = m DIV p ** (ppidx m)` >>
  qabbrev_tac `nq = n DIV p ** (ppidx n)` >>
  `nq = 1` by rw[DIVMOD_ID, Abbr`nq`] >>
  `lcm n m = p ** (SUC k) * (lcm nq mq)` by metis_tac[lcm_prime_power_factor] >>
  metis_tac[LCM_1, EXP, MULT_ASSOC, prime_power_eqn]);

(* Theorem: (n = a * b) /\ coprime a b ==> !m. a divides m /\ b divides m ==> (lcm n m = m) *)
(* Proof:
   If n = 0,
      Then a * b = 0 ==> a = 0 or b = 0           by MULT_EQ_0
        so a divides m /\ b divides m ==> m = 0   by ZERO_DIVIDES
      Since lcm 0 m = 0                           by LCM_0
         so lcm n m = m                           by above
   If n <> 0,
      Note (a * b) divides m                      by coprime_product_divides
        or       n divides m                      by n = a * b
        so    lcm n m = m                         by divides_iff_lcm_fix
*)
Theorem lcm_special_for_coprime_factors:
  !n a b. n = a * b /\ coprime a b ==>
          !m. a divides m /\ b divides m ==> lcm n m = m
Proof
  rpt strip_tac >> Cases_on `n = 0` >| [
    `m = 0` by metis_tac[MULT_EQ_0, ZERO_DIVIDES] >>
    simp[LCM_0],
    `n divides m` by rw[coprime_product_divides] >>
    rw[GSYM divides_iff_lcm_fix]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* Prime Divisors                                                            *)
(* ------------------------------------------------------------------------- *)

(* Define the prime divisors of a number *)
val prime_divisors_def = zDefine`
    prime_divisors n = {p | prime p /\ p divides n}
`;
(* use zDefine as this is not effective. *)

(* Theorem: p IN prime_divisors n <=> prime p /\ p divides n *)
(* Proof: by prime_divisors_def *)
val prime_divisors_element = store_thm(
  "prime_divisors_element",
  ``!n p. p IN prime_divisors n <=> prime p /\ p divides n``,
  rw[prime_divisors_def]);

(* Theorem: 0 < n ==> (prime_divisors n) SUBSET (natural n) *)
(* Proof:
   By prime_divisors_element, SUBSET_DEF,
   this is to show: ?x'. (x = SUC x') /\ x' < n
   Note prime x /\ x divides n
    ==> 0 < x /\ x <= n            by PRIME_POS, DIVIDES_LE, 0 < n
    ==> 0 < x /\ PRE x < n         by arithmetic
   Take x' = PRE x,
   Then SUC x' = SUC (PRE x) = x   by SUC_PRE, 0 < x
*)
val prime_divisors_subset_natural = store_thm(
  "prime_divisors_subset_natural",
  ``!n. 0 < n ==> (prime_divisors n) SUBSET (natural n)``,
  rw[prime_divisors_element, SUBSET_DEF] >>
  `x <= n` by rw[DIVIDES_LE] >>
  `PRE x < n` by decide_tac >>
  `0 < x` by rw[PRIME_POS] >>
  metis_tac[SUC_PRE]);

(* Theorem: 0 < n ==> FINITE (prime_divisors n) *)
(* Proof:
   Note (prime_divisors n) SUBSET (natural n)  by prime_divisors_subset_natural, 0 < n
    and FINITE (natural n)                     by natural_finite
     so FINITE (prime_divisors n)              by SUBSET_FINITE
*)
val prime_divisors_finite = store_thm(
  "prime_divisors_finite",
  ``!n. 0 < n ==> FINITE (prime_divisors n)``,
  metis_tac[prime_divisors_subset_natural, natural_finite, SUBSET_FINITE]);

(* Theorem: prime_divisors 0 = {p | prime p} *)
(* Proof: by prime_divisors_def, ALL_DIVIDES_0 *)
Theorem prime_divisors_0: prime_divisors 0 = {p | prime p}
Proof rw[prime_divisors_def]
QED

(* Note: prime: num -> bool is also a set, so prime = {p | prime p} *)

(* Theorem: prime_divisors n = {} *)
(* Proof: by prime_divisors_def, DIVIDES_ONE, NOT_PRIME_1 *)
val prime_divisors_1 = store_thm(
  "prime_divisors_1",
  ``prime_divisors 1 = {}``,
  rw[prime_divisors_def, EXTENSION]);

(* Theorem: (prime_divisors n) SUBSET prime *)
(* Proof: by prime_divisors_element, SUBSET_DEF, IN_DEF *)
val prime_divisors_subset_prime = store_thm(
  "prime_divisors_subset_prime",
  ``!n. (prime_divisors n) SUBSET prime``,
  rw[prime_divisors_element, SUBSET_DEF, IN_DEF]);

(* Theorem: 1 < n ==> prime_divisors n <> {} *)
(* Proof:
   Note n <> 1                       by 1 < n
     so ?p. prime p /\ p divides n   by PRIME_FACTOR
     or p IN prime_divisors n        by prime_divisors_element
    ==> prime_divisors n <> {}       by MEMBER_NOT_EMPTY
*)
val prime_divisors_nonempty = store_thm(
  "prime_divisors_nonempty",
  ``!n. 1 < n ==> prime_divisors n <> {}``,
  metis_tac[PRIME_FACTOR, prime_divisors_element, MEMBER_NOT_EMPTY, DECIDE``1 < n ==> n <> 1``]);

(* Theorem: (prime_divisors n = {}) <=> (n = 1) *)
(* Proof: by prime_divisors_def, DIVIDES_ONE, NOT_PRIME_1, PRIME_FACTOR *)
val prime_divisors_empty_iff = store_thm(
  "prime_divisors_empty_iff",
  ``!n. (prime_divisors n = {}) <=> (n = 1)``,
  rw[prime_divisors_def, EXTENSION] >>
  metis_tac[DIVIDES_ONE, NOT_PRIME_1, PRIME_FACTOR]);

(* Theorem: ~ SING (prime_divisors 0) *)
(* Proof:
   Let s = prime_divisors 0.
   By contradiction, suppose SING s.
   Note prime 2                  by PRIME_2
    and prime 3                  by PRIME_3
     so 2 IN s /\ 3 IN s         by prime_divisors_0
   This contradicts SING s       by SING_ELEMENT
*)
val prime_divisors_0_not_sing = store_thm(
  "prime_divisors_0_not_sing",
  ``~ SING (prime_divisors 0)``,
  rpt strip_tac >>
  qabbrev_tac `s = prime_divisors 0` >>
  `2 IN s /\ 3 IN s` by rw[PRIME_2, PRIME_3, prime_divisors_0, Abbr`s`] >>
  metis_tac[SING_ELEMENT, DECIDE``2 <> 3``]);

(* Theorem: prime n ==> (prime_divisors n = {n}) *)
(* Proof:
   By prime_divisors_def, EXTENSION, this is to show:
      prime x /\ x divides n <=> (x = n)
   This is true                      by prime_divides_prime
*)
val prime_divisors_prime = store_thm(
  "prime_divisors_prime",
  ``!n. prime n ==> (prime_divisors n = {n})``,
  rw[prime_divisors_def, EXTENSION] >>
  metis_tac[prime_divides_prime]);

(* Theorem: prime n ==> (prime_divisors n = {n}) *)
(* Proof:
   By prime_divisors_def, EXTENSION, this is to show:
     prime x /\ x divides n ** k <=> (x = n)
   If part: prime x /\ x divides n ** k ==> (x = n)
      This is true                   by prime_divides_prime_power
   Only-if part: prime n /\ 0 < k ==> n divides n ** k
      This is true                   by prime_divides_power, DIVIDES_REFL
*)
val prime_divisors_prime_power = store_thm(
  "prime_divisors_prime_power",
  ``!n. prime n ==> !k. 0 < k ==> (prime_divisors (n ** k) = {n})``,
  rw[prime_divisors_def, EXTENSION] >>
  rw[EQ_IMP_THM] >-
  metis_tac[prime_divides_prime_power] >>
  metis_tac[prime_divides_power, DIVIDES_REFL]);

(* Theorem: SING (prime_divisors n) <=> ?p k. prime p /\ 0 < k /\ (n = p ** k) *)
(* Proof:
   If part: SING (prime_divisors n) ==> ?p k. prime p /\ 0 < k /\ (n = p ** k)
      Note n <> 0                                       by prime_divisors_0_not_sing
      Claim: n <> 1
      Proof: By contradiction, suppose n = 1.
             Then prime_divisors 1 = {}                 by prime_divisors_1
              but SING {} = F                           by SING_EMPTY

        Thus 1 < n                                      by n <> 0, n <> 1
         ==> ?p. prime p /\ p divides n                 by PRIME_FACTOR
        also ?q m. (n = p ** m * q) /\ (coprime p q)    by prime_power_factor, 0 < n
        Note q <> 0                                     by MULT_EQ_0
      Claim: q = 1
      Proof: By contradiction, suppose q <> 1.
             Then 1 < q                                 by q <> 0, q <> 1
              ==> ?z. prime z /\ z divides q            by PRIME_FACTOR
              Now 1 < p                                 by ONE_LT_PRIME
               so ~(p divides q)                        by coprime_not_divides, 1 < p, coprime p q
               or p <> z                                by z divides q, but ~(p divides q)
              But q divides n                           by divides_def, n = p ** m * q
             Thus z divides n                           by DIVIDES_TRANS
               so p IN (prime_divisors n)               by prime_divisors_element
              and z IN (prime_divisors n)               by prime_divisors_element
             This contradicts SING (prime_divisors n)   by SING_ELEMENT

      Thus q = 1,
       ==> n = p ** m                                   by MULT_RIGHT_1
       and m <> 0                                       by EXP_0, n <> 1
      Thus take this prime p, and exponent m, and 0 < m by NOT_ZERO_LT_ZERO

   Only-if part: ?p k. prime p /\ 0 < k /\ (n = p ** k) ==> SING (prime_divisors n)
      Note (prime_divisors p ** k) = {p}                by prime_divisors_prime_power
        so SING (prime_divisors n)                      by SING_DEF
*)
val prime_divisors_sing = store_thm(
  "prime_divisors_sing",
  ``!n. SING (prime_divisors n) <=> ?p k. prime p /\ 0 < k /\ (n = p ** k)``,
  rw[EQ_IMP_THM] >| [
    `n <> 0` by metis_tac[prime_divisors_0_not_sing] >>
    `n <> 1` by metis_tac[prime_divisors_1, SING_EMPTY] >>
    `0 < n /\ 1 < n` by decide_tac >>
    `?p. prime p /\ p divides n` by rw[PRIME_FACTOR] >>
    `?q m. (n = p ** m * q) /\ (coprime p q)` by rw[prime_power_factor] >>
    `q <> 0` by metis_tac[MULT_EQ_0] >>
    Cases_on `q = 1` >-
    metis_tac[MULT_RIGHT_1, EXP_0, NOT_ZERO_LT_ZERO] >>
    `?z. prime z /\ z divides q` by rw[PRIME_FACTOR] >>
    `1 < p` by rw[ONE_LT_PRIME] >>
    `p <> z` by metis_tac[coprime_not_divides] >>
    `z divides n` by metis_tac[divides_def, DIVIDES_TRANS] >>
    metis_tac[prime_divisors_element, SING_ELEMENT],
    metis_tac[prime_divisors_prime_power, SING_DEF]
  ]);

(* Theorem: (prime_divisors n = {p}) <=> ?k. prime p /\ 0 < k /\ (n = p ** k) *)
(* Proof:
   If part: prime_divisors n = {p} ==> ?k. prime p /\ 0 < k /\ (n = p ** k)
      Note prime p                                     by prime_divisors_element, IN_SING
       and SING (prime_divisors n)                     by SING_DEF
       ==> ?q k. prime q /\ 0 < k /\ (n = q ** k)      by prime_divisors_sing
      Take this k, then q = p                          by prime_divisors_prime_power, IN_SING
   Only-if part: prime p ==> prime_divisors (p ** k) = {p}
      This is true                                     by prime_divisors_prime_power
*)
val prime_divisors_sing_alt = store_thm(
  "prime_divisors_sing_alt",
  ``!n p. (prime_divisors n = {p}) <=> ?k. prime p /\ 0 < k /\ (n = p ** k)``,
  metis_tac[prime_divisors_sing, SING_DEF, IN_SING, prime_divisors_element, prime_divisors_prime_power]);

(* Theorem: SING (prime_divisors n) ==>
            let p = CHOICE (prime_divisors n) in prime p /\ (n = p ** ppidx n) *)
(* Proof:
   Let s = prime_divisors n.
   Note n <> 0                    by prime_divisors_0_not_sing
    and n <> 1                    by prime_divisors_1, SING_EMPTY
    ==> s <> {}                   by prime_divisors_empty_iff, n <> 1
   Note p = CHOICE s IN s         by CHOICE_DEF
     so prime p /\ p divides n    by prime_divisors_element
   Thus need only to show: n = p ** ppidx n
   Note ?q. (n = p ** ppidx n * q) /\
            coprime p q           by prime_power_factor, prime_power_index_test, 0 < n
   Claim: q = 1
   Proof: By contradiction, suppose q <> 1.
          Note 1 < p                        by ONE_LT_PRIME, prime p
           and q <> 0                       by MULT_EQ_0
           ==> ?z. prime z /\ z divides q   by PRIME_FACTOR, 1 < q
          Note ~(p divides q)               by coprime_not_divides, 1 < p
           ==> z <> p                       by z divides q
          Also q divides n                  by divides_def, n = p ** ppidx n * q
           ==> z divides n                  by DIVIDES_TRANS
          Thus p IN s /\ z IN s             by prime_divisors_element
            or p = z, contradicts z <> p    by SING_ELEMENT

   Thus q = 1, and n = p ** ppidx n         by MULT_RIGHT_1
*)
val prime_divisors_sing_property = store_thm(
  "prime_divisors_sing_property",
  ``!n. SING (prime_divisors n) ==>
       let p = CHOICE (prime_divisors n) in prime p /\ (n = p ** ppidx n)``,
  ntac 2 strip_tac >>
  qabbrev_tac `s = prime_divisors n` >>
  `n <> 0` by metis_tac[prime_divisors_0_not_sing] >>
  `n <> 1` by metis_tac[prime_divisors_1, SING_EMPTY] >>
  `s <> {}` by rw[prime_divisors_empty_iff, Abbr`s`] >>
  `prime (CHOICE s) /\ (CHOICE s) divides n` by metis_tac[CHOICE_DEF, prime_divisors_element] >>
  rw_tac std_ss[] >>
  rw[] >>
  `0 < n` by decide_tac >>
  `?q. (n = p ** ppidx n * q) /\ coprime p q` by metis_tac[prime_power_factor, prime_power_index_test] >>
  reverse (Cases_on `q = 1`) >| [
    `q <> 0` by metis_tac[MULT_EQ_0] >>
    `?z. prime z /\ z divides q` by rw[PRIME_FACTOR] >>
    `z <> p` by metis_tac[coprime_not_divides, ONE_LT_PRIME] >>
    `z divides n` by metis_tac[divides_def, DIVIDES_TRANS] >>
    metis_tac[prime_divisors_element, SING_ELEMENT],
    rw[]
  ]);

(* Theorem: m divides n ==> (prime_divisors m) SUBSET (prime_divisors n) *)
(* Proof:
   Note !x. x IN prime_divisors m
    ==>     prime x /\ x divides m    by prime_divisors_element
    ==>     primx x /\ x divides n    by DIVIDES_TRANS
    ==>     x IN prime_divisors n     by prime_divisors_element
     or (prime_divisors m) SUBSET (prime_divisors n)   by SUBSET_DEF
*)
val prime_divisors_divisor_subset = store_thm(
  "prime_divisors_divisor_subset",
  ``!m n. m divides n ==> (prime_divisors m) SUBSET (prime_divisors n)``,
  rw[prime_divisors_element, SUBSET_DEF] >>
  metis_tac[DIVIDES_TRANS]);

(* Theorem: x divides m /\ x divides n ==>
            (prime_divisors x SUBSET (prime_divisors m) INTER (prime_divisors n)) *)
(* Proof:
   By prime_divisors_element, SUBSET_DEF, this is to show:
   (1) x' divides x /\ x divides m ==> x' divides m, true   by DIVIDES_TRANS
   (2) x' divides x /\ x divides n ==> x' divides n, true   by DIVIDES_TRANS
*)
val prime_divisors_common_divisor = store_thm(
  "prime_divisors_common_divisor",
  ``!n m x. x divides m /\ x divides n ==>
           (prime_divisors x SUBSET (prime_divisors m) INTER (prime_divisors n))``,
  rw[prime_divisors_element, SUBSET_DEF] >>
  metis_tac[DIVIDES_TRANS]);

(* Theorem: m divides x /\ n divides x ==>
            (prime_divisors m UNION prime_divisors n) SUBSET prime_divisors x *)
(* Proof:
   By prime_divisors_element, SUBSET_DEF, this is to show:
   (1) x' divides m /\ m divides x ==> x' divides x, true   by DIVIDES_TRANS
   (2) x' divides n /\ n divides x ==> x' divides x, true   by DIVIDES_TRANS
*)
val prime_divisors_common_multiple = store_thm(
  "prime_divisors_common_multiple",
  ``!n m x. m divides x /\ n divides x ==>
           (prime_divisors m UNION prime_divisors n) SUBSET prime_divisors x``,
  rw[prime_divisors_element, SUBSET_DEF] >>
  metis_tac[DIVIDES_TRANS]);

(* Theorem: 0 < m /\ 0 < n /\ x divides m /\ x divides n ==>
            !p. prime p ==> ppidx x <= MIN (ppidx m) (ppidx n) *)
(* Proof:
   Note ppidx x <= ppidx m                    by prime_power_index_of_divisor, 0 < m
    and ppidx x <= ppidx n                    by prime_power_index_of_divisor, 0 < n
    ==> ppidx x <= MIN (ppidx m) (ppidx n)    by MIN_LE
*)
val prime_power_index_common_divisor = store_thm(
  "prime_power_index_common_divisor",
  ``!n m x. 0 < m /\ 0 < n /\ x divides m /\ x divides n ==>
   !p. prime p ==> ppidx x <= MIN (ppidx m) (ppidx n)``,
  rw[MIN_LE, prime_power_index_of_divisor]);

(* Theorem: 0 < x /\ m divides x /\ n divides x ==>
            !p. prime p ==> MAX (ppidx m) (ppidx n) <= ppidx x *)
(* Proof:
   Note ppidx m <= ppidx x                    by prime_power_index_of_divisor, 0 < x
    and ppidx n <= ppidx x                    by prime_power_index_of_divisor, 0 < x
    ==> MAX (ppidx m) (ppidx n) <= ppidx x    by MAX_LE
*)
val prime_power_index_common_multiple = store_thm(
  "prime_power_index_common_multiple",
  ``!n m x. 0 < x /\ m divides x /\ n divides x ==>
   !p. prime p ==> MAX (ppidx m) (ppidx n) <= ppidx x``,
  rw[MAX_LE, prime_power_index_of_divisor]);

(*
prime p = 2,    n = 10,   LOG 2 10 = 3, but ppidx 10 = 1, since 4 cannot divide 10.
10 = 2^1 * 5^1
*)

(* Theorem: 0 < n /\ prime p ==> ppidx n <= LOG p n *)
(* Proof:
   By contradiction, suppose LOG p n < ppidx n.
   Then SUC (LOG p n) <= ppidx n                    by arithmetic
   Note 1 < p                                       by ONE_LT_PRIME
     so p ** (SUC (LOG p n)) divides p ** ppidx n   by power_divides_iff, 1 < p
    But p ** ppidx n divides n                      by prime_power_index_def
    ==> p ** SUC (LOG p n) divides n                by DIVIDES_TRANS
     or p ** SUC (LOG p n) <= n                     by DIVIDES_LE, 0 < n
   This contradicts n < p ** SUC (LOG p n)          by LOG, 0 < n, 1 < p
*)
val prime_power_index_le_log_index = store_thm(
  "prime_power_index_le_log_index",
  ``!n p. 0 < n /\ prime p ==> ppidx n <= LOG p n``,
  spose_not_then strip_assume_tac >>
  `SUC (LOG p n) <= ppidx n` by decide_tac >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `p ** (SUC (LOG p n)) divides p ** ppidx n` by rw[power_divides_iff] >>
  `p ** ppidx n divides n` by rw[prime_power_index_def] >>
  `p ** SUC (LOG p n) divides n` by metis_tac[DIVIDES_TRANS] >>
  `p ** SUC (LOG p n) <= n` by rw[DIVIDES_LE] >>
  `n < p ** SUC (LOG p n)` by rw[LOG] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Prime-related Sets                                                        *)
(* ------------------------------------------------------------------------- *)

(*
Example: Take n = 10.
primes_upto 10 = {2; 3; 5; 7}
prime_powers_upto 10 = {8; 9; 5; 7}
SET_TO_LIST (prime_powers_upto 10) = [8; 9; 5; 7]
set_lcm (prime_powers_upto 10) = 2520
lcm_run 10 = 2520

Given n,
First get (primes_upto n) = {p | prime p /\ p <= n}
For each prime p, map to p ** LOG p n.

logroot.LOG  |- !a n. 1 < a /\ 0 < n ==> a ** LOG a n <= n /\ n < a ** SUC (LOG a n)
*)

(* val _ = clear_overloads_on "pd"; in Mobius theory *)
(* open primePowerTheory; *)

(*
> prime_power_index_def;
val it = |- !p n. 0 < n /\ prime p ==> p ** ppidx n divides n /\ coprime p (n DIV p ** ppidx n): thm
*)

(* Define the set of primes up to n *)
val primes_upto_def = Define`
    primes_upto n = {p | prime p /\ p <= n}
`;

(* Overload the counts of primes up to n *)
val _ = overload_on("primes_count", ``\n. CARD (primes_upto n)``);

(* Define the prime powers up to n *)
val prime_powers_upto_def = Define`
    prime_powers_upto n = IMAGE (\p. p ** LOG p n) (primes_upto n)
`;

(* Define the prime power divisors of n *)
val prime_power_divisors_def = Define`
    prime_power_divisors n = IMAGE (\p. p ** ppidx n) (prime_divisors n)
`;

(* Theorem: p IN primes_upto n <=> prime p /\ p <= n *)
(* Proof: by primes_upto_def *)
val primes_upto_element = store_thm(
  "primes_upto_element",
  ``!n p. p IN primes_upto n <=> prime p /\ p <= n``,
  rw[primes_upto_def]);

(* Theorem: (primes_upto n) SUBSET (natural n) *)
(* Proof:
   By primes_upto_def, SUBSET_DEF,
   this is to show: prime x /\ x <= n ==> ?x'. (x = SUC x') /\ x' < n
   Note 0 < x            by PRIME_POS, prime x
     so PRE x < n        by x <= n
    and SUC (PRE x) = x  by SUC_PRE, 0 < x
   Take x' = PRE x, and the result follows.
*)
val primes_upto_subset_natural = store_thm(
  "primes_upto_subset_natural",
  ``!n. (primes_upto n) SUBSET (natural n)``,
  rw[primes_upto_def, SUBSET_DEF] >>
  `0 < x` by rw[PRIME_POS] >>
  `PRE x < n` by decide_tac >>
  metis_tac[SUC_PRE]);

(* Theorem: FINITE (primes_upto n) *)
(* Proof:
   Note (primes_upto n) SUBSET (natural n)   by primes_upto_subset_natural
    and FINITE (natural n)                   by natural_finite
    ==> FINITE (primes_upto n)               by SUBSET_FINITE
*)
val primes_upto_finite = store_thm(
  "primes_upto_finite",
  ``!n. FINITE (primes_upto n)``,
  metis_tac[primes_upto_subset_natural, natural_finite, SUBSET_FINITE]);

(* Theorem: PAIRWISE_COPRIME (primes_upto n) *)
(* Proof:
   Let s = prime_power_divisors n
   This is to show: prime x /\ prime y /\ x <> y ==> coprime x y
   This is true                by primes_coprime
*)
val primes_upto_pairwise_coprime = store_thm(
  "primes_upto_pairwise_coprime",
  ``!n. PAIRWISE_COPRIME (primes_upto n)``,
  metis_tac[primes_upto_element, primes_coprime]);

(* Theorem: primes_upto 0 = {} *)
(* Proof:
       p IN primes_upto 0
   <=> prime p /\ p <= 0     by primes_upto_element
   <=> prime 0               by p <= 0
   <=> F                     by NOT_PRIME_0
*)
val primes_upto_0 = store_thm(
  "primes_upto_0",
  ``primes_upto 0 = {}``,
  rw[primes_upto_element, EXTENSION]);

(* Theorem: primes_count 0 = 0 *)
(* Proof:
     primes_count 0
   = CARD (primes_upto 0)     by notation
   = CARD {}                  by primes_upto_0
   = 0                        by CARD_EMPTY
*)
val primes_count_0 = store_thm(
  "primes_count_0",
  ``primes_count 0 = 0``,
  rw[primes_upto_0]);

(* Theorem: primes_upto 1 = {} *)
(* Proof:
       p IN primes_upto 1
   <=> prime p /\ p <= 1     by primes_upto_element
   <=> prime 0 or prime 1    by p <= 1
   <=> F                     by NOT_PRIME_0, NOT_PRIME_1
*)
val primes_upto_1 = store_thm(
  "primes_upto_1",
  ``primes_upto 1 = {}``,
  rw[primes_upto_element, EXTENSION, DECIDE``x <= 1 <=> (x = 0) \/ (x = 1)``] >>
  metis_tac[NOT_PRIME_0, NOT_PRIME_1]);

(* Theorem: primes_count 1 = 0 *)
(* Proof:
     primes_count 1
   = CARD (primes_upto 1)     by notation
   = CARD {}                  by primes_upto_1
   = 0                        by CARD_EMPTY
*)
val primes_count_1 = store_thm(
  "primes_count_1",
  ``primes_count 1 = 0``,
  rw[primes_upto_1]);

(* Theorem: x IN prime_powers_upto n <=> ?p. (x = p ** LOG p n) /\ prime p /\ p <= n *)
(* Proof: by prime_powers_upto_def, primes_upto_element *)
val prime_powers_upto_element = store_thm(
  "prime_powers_upto_element",
  ``!n x. x IN prime_powers_upto n <=> ?p. (x = p ** LOG p n) /\ prime p /\ p <= n``,
  rw[prime_powers_upto_def, primes_upto_element]);

(* Theorem: prime p /\ p <= n ==> (p ** LOG p n) IN (prime_powers_upto n) *)
(* Proof: by prime_powers_upto_element *)
val prime_powers_upto_element_alt = store_thm(
  "prime_powers_upto_element_alt",
  ``!p n. prime p /\ p <= n ==> (p ** LOG p n) IN (prime_powers_upto n)``,
  metis_tac[prime_powers_upto_element]);

(* Theorem: FINITE (prime_powers_upto n) *)
(* Proof:
   Note prime_powers_upto n =
        IMAGE (\p. p ** LOG p n) (primes_upto n)   by prime_powers_upto_def
    and FINITE (primes_upto n)                     by primes_upto_finite
    ==> FINITE (prime_powers_upto n)               by IMAGE_FINITE
*)
val prime_powers_upto_finite = store_thm(
  "prime_powers_upto_finite",
  ``!n. FINITE (prime_powers_upto n)``,
  rw[prime_powers_upto_def, primes_upto_finite]);

(* Theorem: PAIRWISE_COPRIME (prime_powers_upto n) *)
(* Proof:
   Let s = prime_power_divisors n
   This is to show: x IN s /\ y IN s /\ x <> y ==> coprime x y
   Note ?p1. prime p1 /\ (x = p1 ** LOG p1 n) /\ p1 <= n   by prime_powers_upto_element
    and ?p2. prime p2 /\ (y = p2 ** LOG p2 n) /\ p2 <= n   by prime_powers_upto_element
    and p1 <> p2                                           by prime_powers_eq
   Thus coprime x y                                        by prime_powers_coprime
*)
val prime_powers_upto_pairwise_coprime = store_thm(
  "prime_powers_upto_pairwise_coprime",
  ``!n. PAIRWISE_COPRIME (prime_powers_upto n)``,
  metis_tac[prime_powers_upto_element, prime_powers_eq, prime_powers_coprime]);

(* Theorem: prime_powers_upto 0 = {} *)
(* Proof:
       x IN prime_powers_upto 0
   <=> ?p. (x = p ** LOG p n) /\ prime p /\ p <= 0     by prime_powers_upto_element
   <=> ?p. (x = p ** LOG p n) /\ prime 0               by p <= 0
   <=> F                                               by NOT_PRIME_0
*)
val prime_powers_upto_0 = store_thm(
  "prime_powers_upto_0",
  ``prime_powers_upto 0 = {}``,
  rw[prime_powers_upto_element, EXTENSION]);

(* Theorem: prime_powers_upto 1 = {} *)
(* Proof:
       x IN prime_powers_upto 1
   <=> ?p. (x = p ** LOG p n) /\ prime p /\ p <= 1     by prime_powers_upto_element
   <=> ?p. (x = p ** LOG p n) /\ prime 0 or prime 1    by p <= 0
   <=> F                                               by NOT_PRIME_0, NOT_PRIME_1
*)
val prime_powers_upto_1 = store_thm(
  "prime_powers_upto_1",
  ``prime_powers_upto 1 = {}``,
  rw[prime_powers_upto_element, EXTENSION, DECIDE``x <= 1 <=> (x = 0) \/ (x = 1)``] >>
  metis_tac[NOT_PRIME_0, NOT_PRIME_1]);

(* Theorem: x IN prime_power_divisors n <=> ?p. (x = p ** ppidx n) /\ prime p /\ p divides n *)
(* Proof: by prime_power_divisors_def, prime_divisors_element *)
val prime_power_divisors_element = store_thm(
  "prime_power_divisors_element",
  ``!n x. x IN prime_power_divisors n <=> ?p. (x = p ** ppidx n) /\ prime p /\ p divides n``,
  rw[prime_power_divisors_def, prime_divisors_element]);

(* Theorem: prime p /\ p divides n ==> (p ** ppidx n) IN (prime_power_divisors n) *)
(* Proof: by prime_power_divisors_element *)
val prime_power_divisors_element_alt = store_thm(
  "prime_power_divisors_element_alt",
  ``!p n. prime p /\ p divides n ==> (p ** ppidx n) IN (prime_power_divisors n)``,
  metis_tac[prime_power_divisors_element]);

(* Theorem: 0 < n ==> FINITE (prime_power_divisors n) *)
(* Proof:
   Note prime_power_divisors n =
        IMAGE (\p. p ** ppidx n) (prime_divisors n)   by prime_power_divisors_def
    and FINITE (prime_divisors n)                     by prime_divisors_finite, 0 < n
    ==> FINITE (prime_power_divisors n)               by IMAGE_FINITE
*)
val prime_power_divisors_finite = store_thm(
  "prime_power_divisors_finite",
  ``!n. 0 < n ==> FINITE (prime_power_divisors n)``,
  rw[prime_power_divisors_def, prime_divisors_finite]);

(* Theorem: PAIRWISE_COPRIME (prime_power_divisors n) *)
(* Proof:
   Let s = prime_power_divisors n
   This is to show: x IN s /\ y IN s /\ x <> y ==> coprime x y
   Note ?p1. prime p1 /\
             (x = p1 ** prime_power_index p1 n) /\ p1 divides n   by prime_power_divisors_element
    and ?p2. prime p2 /\
             (y = p2 ** prime_power_index p2 n) /\ p2 divides n   by prime_power_divisors_element
    and p1 <> p2                                                  by prime_powers_eq
   Thus coprime x y                                               by prime_powers_coprime
*)
val prime_power_divisors_pairwise_coprime = store_thm(
  "prime_power_divisors_pairwise_coprime",
  ``!n. PAIRWISE_COPRIME (prime_power_divisors n)``,
  metis_tac[prime_power_divisors_element, prime_powers_eq, prime_powers_coprime]);

(* Theorem: prime_power_divisors 1 = {} *)
(* Proof:
       x IN prime_power_divisors 1
   <=> ?p. (x = p ** ppidx n) /\ prime p /\ p divides 1     by prime_power_divisors_element
   <=> ?p. (x = p ** ppidx n) /\ prime 1                    by DIVIDES_ONE
   <=> F                                                    by NOT_PRIME_1
*)
val prime_power_divisors_1 = store_thm(
  "prime_power_divisors_1",
  ``prime_power_divisors 1 = {}``,
  rw[prime_power_divisors_element, EXTENSION]);

(* ------------------------------------------------------------------------- *)
(* Factorisations                                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < n ==> (n = PROD_SET (prime_power_divisors n)) *)
(* Proof:
   Let s = prime_power_divisors n.
   The goal becomes: n = PROD_SET s
   Note FINITE s                       by prime_power_divisors_finite

   Claim: (PROD_SET s) divides n
   Proof: Note !z. z IN s <=>
               ?p. (z = p ** ppidx n) /\ prime p /\ p divides n     by prime_power_divisors_element
           ==> !z. z IN s ==> z divides n       by prime_power_index_def

          Note PAIRWISE_COPRIME s               by prime_power_divisors_pairwise_coprime
          Thus set_lcm s = PROD_SET s           by pairwise_coprime_prod_set_eq_set_lcm
           But (set_lcm s) divides n            by set_lcm_is_least_common_multiple
           ==> PROD_SET s divides n             by above

   Therefore, ?q. n = q * PROD_SET s            by divides_def, Claim.
   Claim: q = 1
   Proof: By contradiction, suppose q <> 1.
          Then ?p. prime p /\ p divides q       by PRIME_FACTOR
          Let u = p ** ppidx n, v = n DIV u.
          Then u divides n /\ coprime p v       by prime_power_index_def, 0 < n, prime p
          Note 0 < p                            by PRIME_POS
           ==> 0 < u                            by EXP_POS, 0 < p
          Thus n = v * u                        by DIVIDES_EQN, 0 < u

          Claim: u divides (PROD_SET s)
          Proof: Note q divides n               by divides_def, MULT_COMM
                  ==> p divides n               by DIVIDES_TRANS
                  ==> p IN (prime_divisors n)   by prime_divisors_element
                  ==> u IN s                    by prime_power_divisors_element_alt
                 Thus u divides (PROD_SET s)    by PROD_SET_ELEMENT_DIVIDES, FINITE s

          Hence ?t. PROD_SET s = t * u          by divides_def, u divides (PROD_SET s)
             or v * u = n = q * (t * u)         by above
                          = (q * t) * u         by MULT_ASSOC
           ==> v = q * t                        by MULT_RIGHT_CANCEL, NOT_ZERO_LT_ZERO
           But p divideq q                      by above
           ==> p divides v                      by DIVIDES_MULT
          Note 1 < p                            by ONE_LT_PRIME
           ==> ~(coprime p v)                   by coprime_not_divides
          This contradicts coprime p v.

   Thus n = q * PROD_SET s, and q = 1           by Claim
     or n = PROD_SET s                          by MULT_LEFT_1
*)
val prime_factorisation = store_thm(
  "prime_factorisation",
  ``!n. 0 < n ==> (n = PROD_SET (prime_power_divisors n))``,
  rpt strip_tac >>
  qabbrev_tac `s = prime_power_divisors n` >>
  `FINITE s` by rw[prime_power_divisors_finite, Abbr`s`] >>
  `(PROD_SET s) divides n` by
  (`!z. z IN s ==> z divides n` by metis_tac[prime_power_divisors_element, prime_power_index_def] >>
  `PAIRWISE_COPRIME s` by metis_tac[prime_power_divisors_pairwise_coprime, Abbr`s`] >>
  metis_tac[pairwise_coprime_prod_set_eq_set_lcm, set_lcm_is_least_common_multiple]) >>
  `?q. n = q * PROD_SET s` by rw[GSYM divides_def] >>
  `q = 1` by
    (spose_not_then strip_assume_tac >>
  `?p. prime p /\ p divides q` by rw[PRIME_FACTOR] >>
  qabbrev_tac `u = p ** ppidx n` >>
  qabbrev_tac `v = n DIV u` >>
  `u divides n /\ coprime p v` by rw[prime_power_index_def, Abbr`u`, Abbr`v`] >>
  `0 < u` by rw[EXP_POS, PRIME_POS, Abbr`u`] >>
  `n = v * u` by rw[GSYM DIVIDES_EQN, Abbr`v`] >>
  `u divides (PROD_SET s)` by
      (`p divides n` by metis_tac[divides_def, MULT_COMM, DIVIDES_TRANS] >>
  `p IN (prime_divisors n)` by rw[prime_divisors_element] >>
  `u IN s` by metis_tac[prime_power_divisors_element_alt] >>
  rw[PROD_SET_ELEMENT_DIVIDES]) >>
  `?t. PROD_SET s = t * u` by rw[GSYM divides_def] >>
  `v = q * t` by metis_tac[MULT_RIGHT_CANCEL, MULT_ASSOC, NOT_ZERO_LT_ZERO] >>
  `p divides v` by rw[DIVIDES_MULT] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  metis_tac[coprime_not_divides]) >>
  rw[]);

(* This is a little milestone theorem. *)

(* Theorem: 0 < n ==> (n = PROD_SET (IMAGE (\p. p ** ppidx n) (prime_divisors n))) *)
(* Proof: by prime_factorisation, prime_power_divisors_def *)
val basic_prime_factorisation = store_thm(
  "basic_prime_factorisation",
  ``!n. 0 < n ==> (n = PROD_SET (IMAGE (\p. p ** ppidx n) (prime_divisors n)))``,
  rw[prime_factorisation, GSYM prime_power_divisors_def]);

(* Theorem: 0 < n /\ m divides n ==> (m = PROD_SET (IMAGE (\p. p ** ppidx m) (prime_divisors n))) *)
(* Proof:
   Note 0 < m                 by ZERO_DIVIDES, 0 < n
   Let s = prime_divisors n, t = IMAGE (\p. p ** ppidx m) s.
   The goal is: m = PROD_SET t

   Note FINITE s              by prime_divisors_finite
    ==> FINITE t              by IMAGE_FINITE
    and PAIRWISE_COPRIME t    by prime_divisors_element, prime_powers_coprime

   By DIVIDES_ANTISYM, this is to show:
   (1) m divides PROD_SET t
       Let r = prime_divisors m
       Then m = PROD_SET (IMAGE (\p. p ** ppidx m) r)  by basic_prime_factorisation
        and r SUBSET s                                 by prime_divisors_divisor_subset
        ==> (IMAGE (\p. p ** ppidx m) r) SUBSET t      by IMAGE_SUBSET
        ==> m divides PROD_SET t                       by pairwise_coprime_prod_set_subset_divides
   (2) PROD_SET t divides m
       Claim: !x. x IN t ==> x divides m
       Proof: Note ?p. p IN s /\ (x = p ** (ppidx m))  by IN_IMAGE
               and prime p                             by prime_divisors_element
                so 1 < p                               by ONE_LT_PRIME
               Now p ** ppidx m divides m              by prime_power_factor_divides
                or x divides m                         by above
       Hence PROD_SET t divides m                      by pairwise_coprime_prod_set_divides
*)
val divisor_prime_factorisation = store_thm(
  "divisor_prime_factorisation",
  ``!m n. 0 < n /\ m divides n ==> (m = PROD_SET (IMAGE (\p. p ** ppidx m) (prime_divisors n)))``,
  rpt strip_tac >>
  `0 < m` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  qabbrev_tac `s = prime_divisors n` >>
  qabbrev_tac `t = IMAGE (\p. p ** ppidx m) s` >>
  `FINITE s` by rw[prime_divisors_finite, Abbr`s`] >>
  `FINITE t` by rw[Abbr`t`] >>
  `PAIRWISE_COPRIME t` by
  (rw[Abbr`t`] >>
  `prime p /\ prime p' /\ p <> p'` by metis_tac[prime_divisors_element] >>
  rw[prime_powers_coprime]) >>
  (irule DIVIDES_ANTISYM >> rpt conj_tac) >| [
    qabbrev_tac `r = prime_divisors m` >>
    `m = PROD_SET (IMAGE (\p. p ** ppidx m) r)` by rw[basic_prime_factorisation, Abbr`r`] >>
    `r SUBSET s` by rw[prime_divisors_divisor_subset, Abbr`r`, Abbr`s`] >>
    metis_tac[pairwise_coprime_prod_set_subset_divides, IMAGE_SUBSET],
    `!x. x IN t ==> x divides m` by
  (rpt strip_tac >>
    qabbrev_tac `f = \p:num. p ** (ppidx m)` >>
    `?p. p IN s /\ (x = p ** (ppidx m))` by metis_tac[IN_IMAGE] >>
    `prime p` by metis_tac[prime_divisors_element] >>
    rw[prime_power_factor_divides]) >>
    rw[pairwise_coprime_prod_set_divides]
  ]);

(* Theorem: 0 < m /\ 0 < n ==>
           (gcd m n = PROD_SET (IMAGE (\p. p ** (MIN (ppidx m) (ppidx n)))
                               ((prime_divisors m) INTER (prime_divisors n)))) *)
(* Proof:
   Let sm = prime_divisors m, sn = prime_divisors n, s = sm INTER sn.
   Let tm = IMAGE (\p. p ** ppidx m) sm, tn = IMAGE (\p. p ** ppidx m) sn,
        t = IMAGE (\p. p ** MIN (ppidx m) (ppidx n)) s.
   The goal is: gcd m n = PROD_SET t

   By GCD_PROPERTY, this is to show:
   (1) PROD_SET t divides m /\ PROD_SET t divides n
       Note FINITE sm /\ FINITE sn              by prime_divisors_finite
        ==> FINITE s                            by FINITE_INTER
        and FINITE tm /\ FINITE tn /\ FINITE t  by IMAGE_FINITE
       Also PAIRWISE_COPRIME t                  by IN_INTER, prime_divisors_element, prime_powers_coprime

       Claim: !x. x IN t ==> x divides m /\ x divides n
       Prood: Note x IN t
               ==> ?p. p IN s /\ x = p ** MIN (ppidx m) (ppidx n)   by IN_IMAGE
               ==> p IN sm /\ p IN sn                               by IN_INTER
              Note prime p                      by prime_divisors_element
               ==> p ** ppidx m divides m       by prime_power_factor_divides
               and p ** ppidx n divides n       by prime_power_factor_divides
              Note MIN (ppidx m) (ppidx n) <= ppidx m   by MIN_DEF
               and MIN (ppidx m) (ppidx n) <= ppidx n   by MIN_DEF
               ==> x divides p ** ppidx m       by prime_power_divides_iff
               and x divides p ** ppidx n       by prime_power_divides_iff
                or x divides m /\ x divides n   by DIVIDES_TRANS

      Therefore, PROD_SET t divides m           by pairwise_coprime_prod_set_divides, Claim
             and PROD_SET t divides n           by pairwise_coprime_prod_set_divides, Claim

   (2) !x. x divides m /\ x divides n ==> x divides PROD_SET t
       Let k = PROD_SET t, sx = prime_divisors x, tx = IMAGE (\p. p ** ppidx x) sx.
       Note 0 < x                    by ZERO_DIVIDES, 0 < m
        and x = PROD_SET tx          by basic_prime_factorisation, 0 < x
       The aim is to show: PROD_SET tx divides k

       Note FINITE sx                by prime_divisors_finite
        ==> FINITE tx                by IMAGE_FINITE
        and PAIRWISE_COPRIME tx      by prime_divisors_element, prime_powers_coprime

       Claim: !z. z IN tx ==> z divides k
       Proof: Note z IN tx
               ==> ?p. p IN sx /\ (z = p ** ppidx x)       by IN_IMAGE
              Note prime p                                 by prime_divisors_element
               and sx SUBSET sm /\ sx SUBSET sn            by prime_divisors_divisor_subset, x | m, x | n
               ==> p IN sm /\ p IN sn                      by SUBSET_DEF
                or p IN s                                  by IN_INTER
              Also ppidx x <= MIN (ppidx m) (ppidx n)      by prime_power_index_common_divisor
               ==> z divides p ** MIN (ppidx m) (ppidx n)  by prime_power_divides_iff
               But p ** MIN (ppidx m) (ppidx n) IN t       by IN_IMAGE
               ==> p ** MIN (ppidx m) (ppidx n) divides k  by PROD_SET_ELEMENT_DIVIDES
                or z divides k                             by DIVIDES_TRANS

       Therefore, PROD_SET tx divides k                    by pairwise_coprime_prod_set_divides
*)
val gcd_prime_factorisation = store_thm(
  "gcd_prime_factorisation",
  ``!m n. 0 < m /\ 0 < n ==>
         (gcd m n = PROD_SET (IMAGE (\p. p ** (MIN (ppidx m) (ppidx n)))
                             ((prime_divisors m) INTER (prime_divisors n))))``,
  rpt strip_tac >>
  qabbrev_tac `sm = prime_divisors m` >>
  qabbrev_tac `sn = prime_divisors n` >>
  qabbrev_tac `s = sm INTER sn` >>
  qabbrev_tac `tm = IMAGE (\p. p ** ppidx m) sm` >>
  qabbrev_tac `tn = IMAGE (\p. p ** ppidx m) sn` >>
  qabbrev_tac `t = IMAGE (\p. p ** MIN (ppidx m) (ppidx n)) s` >>
  `FINITE sm /\ FINITE sn /\ FINITE s` by rw[prime_divisors_finite, Abbr`sm`, Abbr`sn`, Abbr`s`] >>
  `FINITE tm /\ FINITE tn /\ FINITE t` by rw[Abbr`tm`, Abbr`tn`, Abbr`t`] >>
  `PAIRWISE_COPRIME t` by
  (rw[Abbr`t`] >>
  `prime p /\ prime p' /\ p <> p'` by metis_tac[prime_divisors_element, IN_INTER] >>
  rw[prime_powers_coprime]) >>
  `!x. x IN t ==> x divides m /\ x divides n` by
    (ntac 2 strip_tac >>
  qabbrev_tac `f = \p:num. p ** MIN (ppidx m) (ppidx n)` >>
  `?p. p IN s /\ p IN sm /\ p IN sn /\ (x = p ** MIN (ppidx m) (ppidx n))` by metis_tac[IN_IMAGE, IN_INTER] >>
  `prime p` by metis_tac[prime_divisors_element] >>
  `p ** ppidx m divides m /\ p ** ppidx n divides n` by rw[prime_power_factor_divides] >>
  `MIN (ppidx m) (ppidx n) <= ppidx m /\ MIN (ppidx m) (ppidx n) <= ppidx n` by rw[] >>
  metis_tac[prime_power_divides_iff, DIVIDES_TRANS]) >>
  rw[GCD_PROPERTY] >-
  rw[pairwise_coprime_prod_set_divides] >-
  rw[pairwise_coprime_prod_set_divides] >>
  qabbrev_tac `k = PROD_SET t` >>
  qabbrev_tac `sx = prime_divisors x` >>
  qabbrev_tac `tx = IMAGE (\p. p ** ppidx x) sx` >>
  `0 < x` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `x = PROD_SET tx` by rw[basic_prime_factorisation, Abbr`tx`, Abbr`sx`] >>
  `FINITE sx` by rw[prime_divisors_finite, Abbr`sx`] >>
  `FINITE tx` by rw[Abbr`tx`] >>
  `PAIRWISE_COPRIME tx` by
  (rw[Abbr`tx`] >>
  `prime p /\ prime p' /\ p <> p'` by metis_tac[prime_divisors_element] >>
  rw[prime_powers_coprime]) >>
  `!z. z IN tx ==> z divides k` by
    (rw[Abbr`tx`] >>
  `prime p` by metis_tac[prime_divisors_element] >>
  `p IN sm /\ p IN sn` by metis_tac[prime_divisors_divisor_subset, SUBSET_DEF] >>
  `p IN s` by metis_tac[IN_INTER] >>
  `ppidx x <= MIN (ppidx m) (ppidx n)` by rw[prime_power_index_common_divisor] >>
  `(p ** ppidx x) divides p ** MIN (ppidx m) (ppidx n)` by rw[prime_power_divides_iff] >>
  qabbrev_tac `f = \p:num. p ** MIN (ppidx m) (ppidx n)` >>
  `p ** MIN (ppidx m) (ppidx n) IN t` by metis_tac[IN_IMAGE] >>
  metis_tac[PROD_SET_ELEMENT_DIVIDES, DIVIDES_TRANS]) >>
  rw[pairwise_coprime_prod_set_divides]);

(* This is a major milestone theorem. *)

(* Theorem: 0 < m /\ 0 < n ==>
           (lcm m n = PROD_SET (IMAGE (\p. p ** (MAX (ppidx m) (ppidx n)))
                               ((prime_divisors m) UNION (prime_divisors n)))) *)
(* Proof:
   Let sm = prime_divisors m, sn = prime_divisors n, s = sm UNION sn.
   Let tm = IMAGE (\p. p ** ppidx m) sm, tn = IMAGE (\p. p ** ppidx m) sn,
        t = IMAGE (\p. p ** MAX (ppidx m) (ppidx n)) s.
   The goal is: lcm m n = PROD_SET t

   By LCM_PROPERTY, this is to show:
   (1) m divides PROD_SET t /\ n divides PROD_SET t
       Let k = PROD_SET t.
       Note m = PROD_SET tm      by basic_prime_factorisation, 0 < m
        and n = PROD_SET tn      by basic_prime_factorisation, 0 < n
      Also PAIRWISE_COPRIME tm   by prime_divisors_element, prime_powers_coprime
       and PAIRWISE_COPRIME tn   by prime_divisors_element, prime_powers_coprime

      Claim: !z. z IN tm ==> z divides k
      Proof: Note z IN tm
              ==> ?p. p IN sm /\ (z = p ** ppidx m)       by IN_IMAGE
              ==> p IN s                                  by IN_UNION
              and prime p                                 by prime_divisors_element
             Note ppidx m <= MAX (ppidx m) (ppidx n)      by MAX_DEF
              ==> z divides p ** MAX (ppidx m) (ppidx n)  by prime_power_divides_iff
              But p ** MAX (ppidx m) (ppidx n) IN t       by IN_IMAGE
              and p ** MAX (ppidx m) (ppidx n) divides k  by PROD_SET_ELEMENT_DIVIDES
             Thus z divides k                             by DIVIDES_TRANS

      Similarly, !z. z IN tn ==> z divides k
      Hence (PROD_SET tm) divides k /\ (PROD_SET tn) divides k    by pairwise_coprime_prod_set_divides
         or             m divides k /\ n divides k                by above

   (2) m divides x /\ n divides x ==> PROD_SET t divides x
       If x = 0, trivially true      by ALL_DIVIDES_ZERO
       If x <> 0, then 0 < x.
       Note PAIRWISE_COPRIME t       by prime_divisors_element, prime_powers_coprimem IN_UNION

       Claim: !z. z IN t ==> z divides x
       Proof: Note z IN t
               ==> ?p. p IN s /\ (z = p ** MAX (ppidx m) (ppidx n))   by IN_IMAGE
                or prime p                               by prime_divisors_element, IN_UNION
              Note MAX (ppidx m) (ppidx n) <= ppidx x    by prime_power_index_common_multiple, 0 < x
                so z divides p ** ppidx x                by prime_power_divides_iff
               But p ** ppidx x divides x                by prime_power_factor_divides
              Thus z divides x                           by DIVIDES_TRANS
       Hence PROD_SET t divides x                        by pairwise_coprime_prod_set_divides
*)
val lcm_prime_factorisation = store_thm(
  "lcm_prime_factorisation",
  ``!m n. 0 < m /\ 0 < n ==>
         (lcm m n = PROD_SET (IMAGE (\p. p ** (MAX (ppidx m) (ppidx n)))
                             ((prime_divisors m) UNION (prime_divisors n))))``,
  rpt strip_tac >>
  qabbrev_tac `sm = prime_divisors m` >>
  qabbrev_tac `sn = prime_divisors n` >>
  qabbrev_tac `s = sm UNION sn` >>
  qabbrev_tac `tm = IMAGE (\p. p ** ppidx m) sm` >>
  qabbrev_tac `tn = IMAGE (\p. p ** ppidx n) sn` >>
  qabbrev_tac `t = IMAGE (\p. p ** MAX (ppidx m) (ppidx n)) s` >>
  `FINITE sm /\ FINITE sn /\ FINITE s` by rw[prime_divisors_finite, Abbr`sm`, Abbr`sn`, Abbr`s`] >>
  `FINITE tm /\ FINITE tn /\ FINITE t` by rw[Abbr`tm`, Abbr`tn`, Abbr`t`] >>
  rw[LCM_PROPERTY] >| [
    qabbrev_tac `k = PROD_SET t` >>
    `m = PROD_SET tm` by rw[basic_prime_factorisation, Abbr`tm`, Abbr`sm`] >>
    `PAIRWISE_COPRIME tm` by
  (rw[Abbr`tm`] >>
    `prime p /\ prime p' /\ p <> p'` by metis_tac[prime_divisors_element] >>
    rw[prime_powers_coprime]) >>
    `!z. z IN tm ==> z divides k` by
    (rw[Abbr`tm`] >>
    `prime p` by metis_tac[prime_divisors_element] >>
    `p IN s` by metis_tac[IN_UNION] >>
    `ppidx m <= MAX (ppidx m) (ppidx n)` by rw[] >>
    `(p ** ppidx m) divides p ** MAX (ppidx m) (ppidx n)` by rw[prime_power_divides_iff] >>
    qabbrev_tac `f = \p:num. p ** MAX (ppidx m) (ppidx n)` >>
    `p ** MAX (ppidx m) (ppidx n) IN t` by metis_tac[IN_IMAGE] >>
    metis_tac[PROD_SET_ELEMENT_DIVIDES, DIVIDES_TRANS]) >>
    rw[pairwise_coprime_prod_set_divides],
    qabbrev_tac `k = PROD_SET t` >>
    `n = PROD_SET tn` by rw[basic_prime_factorisation, Abbr`tn`, Abbr`sn`] >>
    `PAIRWISE_COPRIME tn` by
  (rw[Abbr`tn`] >>
    `prime p /\ prime p' /\ p <> p'` by metis_tac[prime_divisors_element] >>
    rw[prime_powers_coprime]) >>
    `!z. z IN tn ==> z divides k` by
    (rw[Abbr`tn`] >>
    `prime p` by metis_tac[prime_divisors_element] >>
    `p IN s` by metis_tac[IN_UNION] >>
    `ppidx n <= MAX (ppidx m) (ppidx n)` by rw[] >>
    `(p ** ppidx n) divides p ** MAX (ppidx m) (ppidx n)` by rw[prime_power_divides_iff] >>
    qabbrev_tac `f = \p:num. p ** MAX (ppidx m) (ppidx n)` >>
    `p ** MAX (ppidx m) (ppidx n) IN t` by metis_tac[IN_IMAGE] >>
    metis_tac[PROD_SET_ELEMENT_DIVIDES, DIVIDES_TRANS]) >>
    rw[pairwise_coprime_prod_set_divides],
    Cases_on `x = 0` >-
    rw[] >>
    `0 < x` by decide_tac >>
    `PAIRWISE_COPRIME t` by
  (rw[Abbr`t`] >>
    `prime p /\ prime p' /\ p <> p'` by metis_tac[prime_divisors_element, IN_UNION] >>
    rw[prime_powers_coprime]) >>
    `!z. z IN t ==> z divides x` by
    (rw[Abbr`t`] >>
    `prime p` by metis_tac[prime_divisors_element, IN_UNION] >>
    `MAX (ppidx m) (ppidx n) <= ppidx x` by rw[prime_power_index_common_multiple] >>
    `p ** MAX (ppidx m) (ppidx n) divides p ** ppidx x` by rw[prime_power_divides_iff] >>
    `p ** ppidx x divides x` by rw[prime_power_factor_divides] >>
    metis_tac[DIVIDES_TRANS]) >>
    rw[pairwise_coprime_prod_set_divides]
  ]);

(* Another major milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* GCD and LCM special coprime decompositions                                *)
(* ------------------------------------------------------------------------- *)

(*
Notes
=|===
Given two numbers m and n, with d = gcd m n, and cofactors a = m/d, b = n/d.
Is it true that gcd a n = 1 ?

Take m = 2^3 * 3^2 = 8 * 9 = 72,  n = 2^2 * 3^3 = 4 * 27 = 108
Then gcd m n = d = 2^2 * 3^2 = 4 * 9 = 36, with cofactors a = 2, b = 3.
In this case, gcd a n = gcd 2 108 <> 1.
But lcm m n = 2^3 * 3^3 = 8 * 27 = 216

Ryan Vinroot's method:
Take m = 2^7 * 3^5 * 5^4 * 7^4    n = 2^6 * 3*7 * 5^4 * 11^4
Then m = a b c d = (7^4) (5^4) (2^7) (3^5)
 and n = x y z t = (11^4) (5^4) (3^7) (2^6)
Note b = y always, and lcm m n = a b c x z, gcd m n = d y z
Define P = a b c, Q = x z, then coprime P Q, and lcm P Q = a b c x z = lcm m n = P * Q

a = PROD (all prime factors of m which are not prime factors of n) = 7^4
b = PROD (all prime factors of m common with m and equal powers in both) = 5^4
c = PROD (all prime factors of m common with m but more powers in m) = 2^7
d = PROD (all prime factors of m common with m but more powers in n) = 3^5

x = PROD (all prime factors of n which are not prime factors of m) = 11^4
y = PROD (all prime factors of n common with n and equal powers in both) = 5^4
z = PROD (all prime factors of n common with n but more powers in n) = 3^7
t = PROD (all prime factors of n common with n but more powers in m) = 2^6

Let d = gcd m n. If d <> 1, then it consists of prime powers, e.g. 2^3 * 3^2 * 5
Since d is to take the minimal of prime powers common to both m n,
each prime power in d must occur fully in either m or n.
e.g. it may be the case that:   m = 2^3 * 3 * 5 * a,   n = 2 * 3^2 * 5 * b
where a, b don't have prime factors 2, 3, 5, and coprime a b.
and lcm m n = a * b * 2^3 * 3^2 * 5, taking the maximal of prime powers common to both.
            = (a * 2^3) * (b * 3^2 * 5) = P * Q with coprime P Q.

Ryan Vinroot's method (again):
Take m = 2^7 * 3^5 * 5^4 * 7^4    n = 2^6 * 3*7 * 5^4 * 11^4
Then gcd m n = 2^6 * 3^5 * 5^4, lcm m n = 2^7 * 3^7 * 5^4 * 7^4 * 11^4
Take d = 3^5 * 5^4  (compare m to gcd n m, take the full factors of gcd in m )
     e = gcd n m / d = 2^6        (take what is left over)
Then P = m / d = 2^7 * 7^4
     Q = n / e = 3^7 * 5^4 * 11^4
 so P | m, there is ord p = P.
and Q | n, there is ord q = Q.
and coprime P Q, so ord (p * q) = P * Q = lcm m n.

d = PROD {p ** ppidx m | p | prime p /\ p | (gcd m n) /\ (ppidx (gcd n m) = ppidx m)}
e = gcd n m / d

prime_factorisation  |- !n. 0 < n ==> (n = PROD_SET (prime_power_divisors n)

This is because:   m = 2^7 * 3^5 * 5^4 * 7^4 * 11^0
                   n = 2^6 * 3^7 * 5^4 * 7^0 * 11^4
we know that gcd m n = 2^6 * 3^5 * 5^4 * 7^0 * 11^0   taking minimum
             lcm m n = 2^7 * 3^7 * 5^4 * 7^4 * 11^4   taking maximum
Thus, using gcd m n as a guide,
pick               d = 2^0 * 3^5 * 5^4 , taking common minimum,
Then   P = m / d  will remove these common minimum from m,
but    Q = n / e = n / (gcd m n / d) = n * d / gcd m n   will include their common maximum
This separation of prime factors keep coprime P Q, but P * Q = lcm m n.

*)

(* Overload the park sets *)
val _ = overload_on ("common_prime_divisors",
        ``\m n. (prime_divisors m) INTER (prime_divisors n)``);
val _ = overload_on ("total_prime_divisors",
        ``\m n. (prime_divisors m) UNION (prime_divisors n)``);
val _ = overload_on ("park_on",
        ``\m n. {p | p IN common_prime_divisors m n /\ ppidx m <= ppidx n}``);
val _ = overload_on ("park_off",
        ``\m n. {p | p IN common_prime_divisors m n /\ ppidx n < ppidx m}``);
(* Overload the parking divisor of GCD *)
val _ = overload_on("park", ``\m n. PROD_SET (IMAGE (\p. p ** ppidx m) (park_on m n))``);

(* Note:
The basic one is park_on m n, defined only for 0 < m and 0 < n.
*)

(* Theorem: p IN common_prime_divisors m n <=> p IN prime_divisors m /\ p IN prime_divisors n *)
(* Proof: by IN_INTER *)
val common_prime_divisors_element = store_thm(
  "common_prime_divisors_element",
  ``!m n p. p IN common_prime_divisors m n <=> p IN prime_divisors m /\ p IN prime_divisors n``,
  rw[]);

(* Theorem: 0 < m /\ 0 < n ==> FINITE (common_prime_divisors m n) *)
(* Proof: by prime_divisors_finite, FINITE_INTER *)
val common_prime_divisors_finite = store_thm(
  "common_prime_divisors_finite",
  ``!m n. 0 < m /\ 0 < n ==> FINITE (common_prime_divisors m n)``,
  rw[prime_divisors_finite]);

(* Theorem: PAIRWISE_COPRIME (common_prime_divisors m n) *)
(* Proof:
   Note x IN prime_divisors m ==> prime x    by prime_divisors_element
    and y IN prime_divisors n ==> prime y    by prime_divisors_element
    and x <> y ==> coprime x y               by primes_coprime
*)
val common_prime_divisors_pairwise_coprime = store_thm(
  "common_prime_divisors_pairwise_coprime",
  ``!m n. PAIRWISE_COPRIME (common_prime_divisors m n)``,
  metis_tac[prime_divisors_element, primes_coprime, IN_INTER]);

(* Theorem: PAIRWISE_COPRIME (IMAGE (\p. p ** MIN (ppidx m) (ppidx n)) (common_prime_divisors m n)) *)
(* Proof:
   Note (prime_divisors m) SUBSET prime            by prime_divisors_subset_prime
     so (common_prime_divisors m n) SUBSET prime   by SUBSET_INTER_SUBSET
   Thus true                                       by pairwise_coprime_for_prime_powers
*)
val common_prime_divisors_min_image_pairwise_coprime = store_thm(
  "common_prime_divisors_min_image_pairwise_coprime",
  ``!m n. PAIRWISE_COPRIME (IMAGE (\p. p ** MIN (ppidx m) (ppidx n)) (common_prime_divisors m n))``,
  metis_tac[prime_divisors_subset_prime, SUBSET_INTER_SUBSET, pairwise_coprime_for_prime_powers]);

(* Theorem: p IN total_prime_divisors m n <=> p IN prime_divisors m \/ p IN prime_divisors n *)
(* Proof: by IN_UNION *)
val total_prime_divisors_element = store_thm(
  "total_prime_divisors_element",
  ``!m n p. p IN total_prime_divisors m n <=> p IN prime_divisors m \/ p IN prime_divisors n``,
  rw[]);

(* Theorem: 0 < m /\ 0 < n ==> FINITE (total_prime_divisors m n) *)
(* Proof: by prime_divisors_finite, FINITE_UNION *)
val total_prime_divisors_finite = store_thm(
  "total_prime_divisors_finite",
  ``!m n. 0 < m /\ 0 < n ==> FINITE (total_prime_divisors m n)``,
  rw[prime_divisors_finite]);

(* Theorem: PAIRWISE_COPRIME (total_prime_divisors m n) *)
(* Proof:
   Note x IN prime_divisors m ==> prime x    by prime_divisors_element
    and y IN prime_divisors n ==> prime y    by prime_divisors_element
    and x <> y ==> coprime x y               by primes_coprime
*)
val total_prime_divisors_pairwise_coprime = store_thm(
  "total_prime_divisors_pairwise_coprime",
  ``!m n. PAIRWISE_COPRIME (total_prime_divisors m n)``,
  metis_tac[prime_divisors_element, primes_coprime, IN_UNION]);

(* Theorem: PAIRWISE_COPRIME (IMAGE (\p. p ** MAX (ppidx m) (ppidx n)) (total_prime_divisors m n)) *)
(* Proof:
   Note prime_divisors m SUBSET prime      by prime_divisors_subset_prime
    and prime_divisors n SUBSET prime      by prime_divisors_subset_prime
     so (total_prime_divisors m n) SUBSET prime    by UNION_SUBSET
   Thus true                                       by pairwise_coprime_for_prime_powers
*)
val total_prime_divisors_max_image_pairwise_coprime = store_thm(
  "total_prime_divisors_max_image_pairwise_coprime",
  ``!m n. PAIRWISE_COPRIME (IMAGE (\p. p ** MAX (ppidx m) (ppidx n)) (total_prime_divisors m n))``,
  metis_tac[prime_divisors_subset_prime, UNION_SUBSET, pairwise_coprime_for_prime_powers]);

(* Theorem: p IN park_on m n <=> p IN prime_divisors m /\ p IN prime_divisors n /\ ppidx m <= ppidx n *)
(* Proof: by IN_INTER *)
val park_on_element = store_thm(
  "park_on_element",
  ``!m n p. p IN park_on m n <=> p IN prime_divisors m /\ p IN prime_divisors n /\ ppidx m <= ppidx n``,
  rw[] >>
  metis_tac[]);

(* Theorem: p IN park_off m n <=> p IN prime_divisors m /\ p IN prime_divisors n /\ ppidx n < ppidx m *)
(* Proof: by IN_INTER *)
val park_off_element = store_thm(
  "park_off_element",
  ``!m n p. p IN park_off m n <=> p IN prime_divisors m /\ p IN prime_divisors n /\ ppidx n < ppidx m``,
  rw[] >>
  metis_tac[]);

(* Theorem: park_off m n = (common_prime_divisors m n) DIFF (park_on m n) *)
(* Proof: by EXTENSION, NOT_LESS_EQUAL *)
val park_off_alt = store_thm(
  "park_off_alt",
  ``!m n. park_off m n = (common_prime_divisors m n) DIFF (park_on m n)``,
  rw[EXTENSION] >>
  metis_tac[NOT_LESS_EQUAL]);

(* Theorem: park_on m n SUBSET common_prime_divisors m n *)
(* Proof: by SUBSET_DEF *)
val park_on_subset_common = store_thm(
  "park_on_subset_common",
  ``!m n. park_on m n SUBSET common_prime_divisors m n``,
  rw[SUBSET_DEF]);

(* Theorem: park_off m n SUBSET common_prime_divisors m n *)
(* Proof: by SUBSET_DEF *)
val park_off_subset_common = store_thm(
  "park_off_subset_common",
  ``!m n. park_off m n SUBSET common_prime_divisors m n``,
  rw[SUBSET_DEF]);

(* Theorem: park_on m n SUBSET total_prime_divisors m n *)
(* Proof: by SUBSET_DEF *)
val park_on_subset_total = store_thm(
  "park_on_subset_total",
  ``!m n. park_on m n SUBSET total_prime_divisors m n``,
  rw[SUBSET_DEF]);

(* Theorem: park_off m n SUBSET total_prime_divisors m n *)
(* Proof: by SUBSET_DEF *)
val park_off_subset_total = store_thm(
  "park_off_subset_total",
  ``!m n. park_off m n SUBSET total_prime_divisors m n``,
  rw[SUBSET_DEF]);

(* Theorem: common_prime_divisors m n =|= park_on m n # park_off m n *)
(* Proof:
   Let s = common_prime_divisors m n.
   Note park_on m n SUBSET s                     by park_on_subset_common
    and park_off m n = s DIFF (park_on m n)      by park_off_alt
     so s = park_on m n UNION park_off m n /\
        DISJOINT (park_on m n) (park_off m n)    by partition_by_subset
*)
val park_on_off_partition = store_thm(
  "park_on_off_partition",
  ``!m n. common_prime_divisors m n =|= park_on m n # park_off m n``,
  metis_tac[partition_by_subset, park_on_subset_common, park_off_alt]);

(* Theorem: 1 NOTIN (IMAGE (\p. p ** ppidx m) (park_off m n)) *)
(* Proof:
   By contradiction, suppse 1 IN (IMAGE (\p. p ** ppidx m) (park_off m n)).
   Then ?p. p IN park_off m n /\ (1 = p ** ppidx m)   by IN_IMAGE
     or p IN prime_divisors m /\
        p IN prime_divisors n /\ ppidx n < ppidx m    by park_off_element
    But prime p                     by prime_divisors_element
    and p <> 1                      by NOT_PRIME_1
   Thus ppidx m = 0                 by EXP_EQ_1
     or ppidx n < 0, which is F     by NOT_LESS_0
*)
val park_off_image_has_not_1 = store_thm(
  "park_off_image_has_not_1",
  ``!m n. 1 NOTIN (IMAGE (\p. p ** ppidx m) (park_off m n))``,
  rw[] >>
  spose_not_then strip_assume_tac >>
  `prime p` by metis_tac[prime_divisors_element] >>
  `p <> 1` by metis_tac[NOT_PRIME_1] >>
  decide_tac);

(*
For the example,
This is because:   m = 2^7 * 3^5 * 5^4 * 7^4 * 11^0
                   n = 2^6 * 3^7 * 5^4 * 7^0 * 11^4
we know that gcd m n = 2^6 * 3^5 * 5^4 * 7^0 * 11^0   taking minimum
             lcm m n = 2^7 * 3^7 * 5^4 * 7^4 * 11^4   taking maximum
Thus, using gcd m n as a guide,
pick               d = 2^0 * 3^5 * 5^4 , taking common minimum,
Then   P = m / d  will remove these common minimum from m,
but    Q = n / e = n / (gcd m n / d) = n * d / gcd m n   will include their common maximum
This separation of prime factors keep coprime P Q, but P * Q = lcm m n.
common_prime_divisors m n = {2; 3; 5}  s = {2^6; 3^5; 5^4} with MIN
park_on m n = {3; 5}  u = IMAGE (\p. p ** ppidx m) (park_on m n) = {3^5; 5^4}
park_off m n = {2}    v = IMAGE (\p. p ** ppidx n) (park_off m n) = {2^6}
Note                      IMAGE (\p. p ** ppidx m) (park_off m n) = {2^7}
and                       IMAGE (\p. p ** ppidx n) (park_on m n) = {3^7; 5^4}

total_prime_divisors m n = {2; 3; 5; 7; 11}  s = {2^7; 3^7; 5^4; 7^4; 11^4} with MAX
sm = (prime_divisors m) DIFF (park_on m n) = {2; 7}, u = IMAGE (\p. p ** ppidx m) sm = {2^7; 7^4}
sn = (prime_divisors n) DIFF (park_off m n) = {3; 5; 11}, v = IMAGE (\p. p ** ppidx n) sn = {3^7; 5^4; 11^4}

park_on_element
|- !m n p. p IN park_on m n <=> p IN prime_divisors m /\ p IN prime_divisors n /\ ppidx m <= ppidx n
park_off_element
|- !m n p. p IN park_off m n <=> p IN prime_divisors m /\ p IN prime_divisors n /\ ppidx n < ppidx m
*)

(* Theorem: let s = IMAGE (\p. p ** MIN (ppidx m) (ppidx n)) (common_prime_divisors m n) in
            let u = IMAGE (\p. p ** ppidx m) (park_on m n) in
            let v = IMAGE (\p. p ** ppidx n) (park_off m n) in
            0 < m ==> s =|= u # v *)
(* Proof:
   This is to show:
   (1) s = u UNION v
       By EXTENSION, this is to show:
       (a) !x. x IN s ==> x IN u \/ x IN v            by IN_UNION
           Note x IN s
            ==> ?p. (x = p ** MIN (ppidx m) (ppidx n)) /\
                 p IN common_prime_divisors m n       by IN_IMAGE
          If ppidx m <= ppidx n
             Then MIN (ppidx m) (ppidx n) = ppidx m   by MIN_DEF
              and p IN park_on m n                    by common_prime_divisors_element, park_on_element
              ==> x IN u                              by IN_IMAGE
          If ~(ppidx m <= ppidx n),
            so ppidx n < ppidx m                      by NOT_LESS_EQUAL
             Then MIN (ppidx m) (ppidx n) = ppidx n   by MIN_DEF
              and p IN park_off m n                   by common_prime_divisors_element, park_off_element
              ==> x IN v                              by IN_IMAGE
       (b) x IN u ==> x IN s
           Note x IN u
            ==> ?p. (x = p ** ppidx m) /\
                    p IN park_on m n                  by IN_IMAGE
            ==> ppidx m <= ppidx n                    by park_on_element
           Thus MIN (ppidx m) (ppidx n) = ppidx m     by MIN_DEF
             so p IN common_prime_divisors m n        by park_on_subset_common, SUBSET_DEF
            ==> x IN s                                by IN_IMAGE
       (c) x IN v ==> x IN s
           Note x IN v
            ==> ?p. (x = p ** ppidx n) /\
                    p IN park_off m n                 by IN_IMAGE
            ==> ppidx n < ppidx m                     by park_off_element
           Thus MIN (ppidx m) (ppidx n) = ppidx n     by MIN_DEF
             so p IN common_prime_divisors m n        by park_off_subset_common, SUBSET_DEF
            ==> x IN s                                by IN_IMAGE
   (2) DISJOINT u v
       This is to show: u INTER v = {}                by DISJOINT_DEF
       By contradiction, suppse u INTER v <> {}.
       Then ?x. x IN u /\ x IN v                      by MEMBER_NOT_EMPTY, IN_INTER
       Thus ?p. p IN park_on m n /\ (x = p ** ppidx m)                  by IN_IMAGE
        and ?q. q IN park_off m n /\ (x = q ** prime_power_index q n)   by IN_IMAGE
        ==> prime p /\ prime q /\ p divides m         by park_on_element, park_off_element
                                                         prime_divisors_element
       Also 0 < ppidx m                               by prime_power_index_pos, p divides m, 0 < m
        ==> p = q                                     by prime_powers_eq
       Thus p IN (park_on m n) INTER (park_off m n)   by IN_INTER
        But DISJOINT (park_on m n) (park_off m n)     by park_on_off_partition
         so there is a contradiction                  by IN_DISJOINT
*)
val park_on_off_common_image_partition = store_thm(
  "park_on_off_common_image_partition",
  ``!m n. let s = IMAGE (\p. p ** MIN (ppidx m) (ppidx n)) (common_prime_divisors m n) in
         let u = IMAGE (\p. p ** ppidx m) (park_on m n) in
         let v = IMAGE (\p. p ** ppidx n) (park_off m n) in
         0 < m ==> s =|= u # v``,
  rpt strip_tac >>
  qabbrev_tac `f = \p:num. p ** MIN (ppidx m) (ppidx n)` >>
  qabbrev_tac `f1 = \p:num. p ** ppidx m` >>
  qabbrev_tac `f2 = \p:num. p ** ppidx n` >>
  rw_tac std_ss[] >| [
    rw[EXTENSION, EQ_IMP_THM] >| [
      `?p. (x = p ** MIN (ppidx m) (ppidx n)) /\ p IN common_prime_divisors m n` by metis_tac[IN_IMAGE] >>
      Cases_on `ppidx m <= ppidx n` >| [
        `MIN (ppidx m) (ppidx n) = ppidx m` by rw[MIN_DEF] >>
        `p IN park_on m n` by metis_tac[common_prime_divisors_element, park_on_element] >>
        metis_tac[IN_IMAGE],
        `MIN (ppidx m) (ppidx n) = ppidx n` by rw[MIN_DEF] >>
        `p IN park_off m n` by metis_tac[common_prime_divisors_element, park_off_element, NOT_LESS_EQUAL] >>
        metis_tac[IN_IMAGE]
      ],
      `?p. (x = p ** ppidx m) /\ p IN park_on m n` by metis_tac[IN_IMAGE] >>
      `ppidx m <= ppidx n` by metis_tac[park_on_element] >>
      `MIN (ppidx m) (ppidx n) = ppidx m` by rw[MIN_DEF] >>
      `p IN common_prime_divisors m n` by metis_tac[park_on_subset_common, SUBSET_DEF] >>
      metis_tac[IN_IMAGE],
      `?p. (x = p ** ppidx n) /\ p IN park_off m n` by metis_tac[IN_IMAGE] >>
      `ppidx n < ppidx m` by metis_tac[park_off_element] >>
      `MIN (ppidx m) (ppidx n) = ppidx n` by rw[MIN_DEF] >>
      `p IN common_prime_divisors m n` by metis_tac[park_off_subset_common, SUBSET_DEF] >>
      metis_tac[IN_IMAGE]
    ],
    rw[DISJOINT_DEF] >>
    spose_not_then strip_assume_tac >>
    `?x. x IN u /\ x IN v` by metis_tac[MEMBER_NOT_EMPTY, IN_INTER] >>
    `?p. p IN park_on m n /\ (x = p ** ppidx m)` by prove_tac[IN_IMAGE] >>
    `?q. q IN park_off m n /\ (x = q ** prime_power_index q n)` by prove_tac[IN_IMAGE] >>
    `prime p /\ prime q /\ p divides m` by metis_tac[park_on_element, park_off_element, prime_divisors_element] >>
    `0 < ppidx m` by rw[prime_power_index_pos] >>
    `p = q` by metis_tac[prime_powers_eq] >>
    metis_tac[park_on_off_partition, IN_DISJOINT]
  ]);

(* Theorem: 0 < m /\ 0 < n ==> let a = park m n in let b = gcd m n DIV a in
           (b = PROD_SET (IMAGE (\p. p ** ppidx n) (park_off m n))) /\ (gcd m n = a * b) /\ coprime a b *)
(* Proof:
   Let s = IMAGE (\p. p ** MIN (ppidx m) (ppidx n)) (common_prime_divisors m n),
       u = IMAGE (\p. p ** ppidx m) (park_on m n),
       v = IMAGE (\p. p ** ppidx n) (park_off m n).
   Then s =|= u # v                         by park_on_off_common_image_partition
   Let a = PROD_SET u, b = PROD_SET v, c = PROD_SET s.
   Then FINITE s                            by common_prime_divisors_finite, IMAGE_FINITE, 0 < m, 0 < n
    and PAIRWISE_COPRIME s                  by common_prime_divisors_min_image_pairwise_coprime
    ==> (c = a * b) /\ coprime a b          by pairwise_coprime_prod_set_partition
   Note c = gcd m n                         by gcd_prime_factorisation
    and a = park m n                        by notation
   Note c <> 0                              by GCD_EQ_0, 0 < m, 0 < n
   Thus a <> 0, or 0 < a                    by MULT_EQ_0
     so b = c DIV a                         by DIV_SOLVE_COMM, 0 < a
   Therefore,
        b = PROD_SET (IMAGE (\p. p ** ppidx n) (park_off m n)) /\
        gcd m n = a * b /\ coprime a b      by above
*)

Theorem gcd_park_decomposition:
  !m n. 0 < m /\ 0 < n ==> let a = park m n in let b = gcd m n DIV a in
        b = PROD_SET (IMAGE (\p. p ** ppidx n) (park_off m n)) /\
        gcd m n = a * b /\ coprime a b
Proof
  rpt strip_tac >>
  qabbrev_tac `s = IMAGE (\p. p ** MIN (ppidx m) (ppidx n)) (common_prime_divisors m n)` >>
  qabbrev_tac `u = IMAGE (\p. p ** ppidx m) (park_on m n)` >>
  qabbrev_tac `v = IMAGE (\p. p ** ppidx n) (park_off m n)` >>
  `s =|= u # v` by metis_tac[park_on_off_common_image_partition] >>
  qabbrev_tac `a = PROD_SET u` >>
  qabbrev_tac `b = PROD_SET v` >>
  qabbrev_tac `c = PROD_SET s` >>
  `FINITE s` by rw[common_prime_divisors_finite, Abbr`s`] >>
  `PAIRWISE_COPRIME s` by metis_tac[common_prime_divisors_min_image_pairwise_coprime] >>
  `(c = a * b) /\ coprime a b`
    by (simp[Abbr`a`, Abbr`b`, Abbr`c`] >>
        metis_tac[pairwise_coprime_prod_set_partition]) >>
  metis_tac[gcd_prime_factorisation, GCD_EQ_0, MULT_EQ_0, DIV_SOLVE_COMM,
            NOT_ZERO_LT_ZERO]
QED

(* Theorem: 0 < m /\ 0 < n ==> let a = park m n in let b = gcd m n DIV a in
            (gcd m n = a * b) /\ coprime a b *)
(* Proof: by gcd_park_decomposition *)
val gcd_park_decompose = store_thm(
  "gcd_park_decompose",
  ``!m n. 0 < m /\ 0 < n ==> let a = park m n in let b = gcd m n DIV a in
         (gcd m n = a * b) /\ coprime a b``,
  metis_tac[gcd_park_decomposition]);

(*
For the example:
total_prime_divisors m n = {2; 3; 5; 7; 11}  s = {2^7; 3^7; 5^4; 7^4; 11^4} with MAX
sm = (prime_divisors m) DIFF (park_on m n) = {2; 7}, u = IMAGE (\p. p ** ppidx m) sm = {2^7; 7^4}
sn = (prime_divisors n) DIFF (park_off m n) = {3; 5; 11}, v = IMAGE (\p. p ** ppidx n) sn = {3^7; 5^4; 11^4}
*)

(* Theorem: let s = IMAGE (\p. p ** MAX (ppidx m) (ppidx n)) (total_prime_divisors m n) in
            let u = IMAGE (\p. p ** ppidx m) ((prime_divisors m) DIFF (park_on m n)) in
            let v = IMAGE (\p. p ** ppidx n) ((prime_divisors n) DIFF (park_off m n)) in
            0 < m /\ 0 < n ==> s =|= u # v *)
(* Proof:
   This is to show:
   (1) s = u UNION v
       By EXTENSION, this is to show:
       (a) x IN s ==> x IN u \/ x IN v
           Note x IN s
            ==> ?p. p IN total_prime_divisors m n /\
                    (x = p ** MAX (ppidx m) (ppidx n))         by IN_IMAGE
           By total_prime_divisors_element,

           If p IN prime_divisors m,
              Then prime p /\ p divides m                      by prime_divisors_element
              If p IN park_on m n,
                 Then p IN prime_divisors n /\
                      ppidx m <= ppidx n                       by park_on_element
                  ==> MAX (ppidx m) (ppidx n) = ppidx n        by MAX_DEF
                 Note DISJOINT (park_on m n) (park_off m n)    by park_on_off_partition
                 Thus p NOTIN park_off m n                     by IN_DISJOINT
                  ==> p IN prime_divisors n DIFF park_off m n  by IN_DIFF
                 Therefore x IN v                              by IN_IMAGE
              If p NOTIN park_on m n,
                 Then p IN prime_divisors m DIFF park_on m n   by IN_DIFF
                 By park_on_element, either [1] or [2]:
                 [1] p NOTIN prime_divisors n
                     Then ppidx n = 0   by prime_divisors_element, prime_power_index_eq_0, 0 < n
                      ==> MAX (ppidx m) (ppidx n) = ppidx m    by MAX_DEF
                     Therefore x IN u                          by IN_IMAGE
                 [2] ~(ppidx m <= ppidx n)
                     Then MAX (ppidx m) (ppidx n) = ppidx m    by MAX_DEF
                     Therefore x IN u                          by IN_IMAGE

           If p IN prime_divisors n,
              Then prime p /\ p divides n                      by prime_divisors_element
              If p IN park_off m n,
                 Then p IN prime_divisors m /\
                      ppidx n < ppidx m                        by park_off_element
                  ==> MAX (ppidx m) (ppidx n) = ppidx m        by MAX_DEF
                 Note DISJOINT (park_on m n) (park_off m n)    by park_on_off_partition
                 Thus p NOTIN park_on m n                      by IN_DISJOINT
                  ==> p IN prime_divisors m DIFF park_on m n   by IN_DIFF
                 Therefore x IN u                              by IN_IMAGE
              If p NOTIN park_off m n,
                 Then p IN prime_divisors n DIFF park_off m n  by IN_DIFF
                 By park_off_element, either [1] or [2]:
                 [1] p NOTIN prime_divisors m
                     Then ppidx m = 0   by prime_divisors_element, prime_power_index_eq_0, 0 < m
                      ==> MAX (ppidx m) (ppidx n) = ppidx n    by MAX_DEF
                     Therefore x IN v                          by IN_IMAGE
                 [2] ~(ppidx n < ppidx m)
                     Then MAX (ppidx m) (ppidx n) = ppidx n    by MAX_DEF
                     Therefore x IN v                          by IN_IMAGE

       (b) x IN u ==> x IN s
           Note x IN u
            ==> ?p. p IN prime_divisors m DIFF park_on m n /\
                    (x = p ** ppidx m)                        by IN_IMAGE
           Thus p IN prime_divisors m /\ p NOTIN park_on m n  by IN_DIFF
           Note p IN total_prime_divisors m n                 by total_prime_divisors_element
           By park_on_element, either [1] or [2]:
           [1] p NOTIN prime_divisors n
               Then ppidx n = 0  by prime_divisors_element, prime_power_index_eq_0, 0 < n
                ==> MAX (ppidx m) (ppidx n) = ppidx m         by MAX_DEF
               Therefore x IN u                               by IN_IMAGE
           [2] ~(ppidx m <= ppidx n)
               Then MAX (ppidx m) (ppidx n) = ppidx m         by MAX_DEF
               Therefore x IN u                               by IN_IMAGE

       (c) x IN v ==> x IN s
           Note x IN v
            ==> ?p. p IN prime_divisors n DIFF park_off m n /\
                    (x = p ** ppidx n)                        by IN_IMAGE
           Thus p IN prime_divisors n /\ p NOTIN park_off m n by IN_DIFF
           Note p IN total_prime_divisors m n                 by total_prime_divisors_element
           By park_off_element, either [1] or [2]:
           [1] p NOTIN prime_divisors m
               Then ppidx m = 0  by prime_divisors_element, prime_power_index_eq_0, 0 < m
                ==> MAX (ppidx m) (ppidx n) = ppidx n         by MAX_DEF
               Therefore x IN v                               by IN_IMAGE
           [2] ~(ppidx n < ppidx m)
               Then MAX (ppidx m) (ppidx n) = ppidx n         by MAX_DEF
               Therefore x IN v                               by IN_IMAGE

   (2) DISJOINT u v
       This is to show: u INTER v = {}          by DISJOINT_DEF
       By contradiction, suppse u INTER v <> {}.
       Then ?x. x IN u /\ x IN v                by MEMBER_NOT_EMPTY, IN_INTER
       Note x IN u
        ==> ?p. p IN prime_divisors m DIFF park_on m n /\
                (x = p ** ppidx m)              by IN_IMAGE
        and x IN v
        ==> ?q. q IN prime_divisors n DIFF park_off m n /\
               (x = q ** prime_power_index q n)   by IN_IMAGE
       Thus p IN prime_divisors m /\ p NOTIN park_on m n   by IN_DIFF
        and q IN prime_divisors n /\ q NOTIN park_off m n  by IN_DIFF [1]
        Now prime p /\ prime q /\ p divides m     by prime_divisors_element
        and 0 < ppidx m                           by prime_power_index_pos, p divides m, 0 < m
        ==> p = q                                 by prime_powers_eq
       Thus p IN common_prime_divisors m n        by common_prime_divisors_element, [1]
        ==> p IN park_on m n \/ p IN park_off m n by park_on_off_partition, IN_UNION
       This is a contradiction with [1].
*)
val park_on_off_total_image_partition = store_thm(
  "park_on_off_total_image_partition",
  ``!m n. let s = IMAGE (\p. p ** MAX (ppidx m) (ppidx n)) (total_prime_divisors m n) in
         let u = IMAGE (\p. p ** ppidx m) ((prime_divisors m) DIFF (park_on m n)) in
         let v = IMAGE (\p. p ** ppidx n) ((prime_divisors n) DIFF (park_off m n)) in
         0 < m /\ 0 < n ==> s =|= u # v``,
  rpt strip_tac >>
  qabbrev_tac `f = \p:num. p ** MAX (ppidx m) (ppidx n)` >>
  qabbrev_tac `f1 = \p:num. p ** ppidx m` >>
  qabbrev_tac `f2 = \p:num. p ** ppidx n` >>
  rw_tac std_ss[] >| [
    rw[EXTENSION, EQ_IMP_THM] >| [
      `?p. p IN total_prime_divisors m n /\ (x = p ** MAX (ppidx m) (ppidx n))` by metis_tac[IN_IMAGE] >>
      `p IN prime_divisors m \/ p IN prime_divisors n` by rw[GSYM total_prime_divisors_element] >| [
        `prime p /\ p divides m` by metis_tac[prime_divisors_element] >>
        Cases_on `p IN park_on m n` >| [
          `p IN prime_divisors n /\ ppidx m <= ppidx n` by metis_tac[park_on_element] >>
          `MAX (ppidx m) (ppidx n) = ppidx n` by rw[MAX_DEF] >>
          `p NOTIN park_off m n` by metis_tac[park_on_off_partition, IN_DISJOINT] >>
          `p IN prime_divisors n DIFF park_off m n` by rw[] >>
          metis_tac[IN_IMAGE],
          `p IN prime_divisors m DIFF park_on m n` by rw[] >>
          `p NOTIN prime_divisors n \/ ~(ppidx m <= ppidx n)` by metis_tac[park_on_element] >| [
            `ppidx n = 0` by metis_tac[prime_divisors_element, prime_power_index_eq_0] >>
            `MAX (ppidx m) (ppidx n) = ppidx m` by rw[MAX_DEF] >>
            metis_tac[IN_IMAGE],
            `MAX (ppidx m) (ppidx n) = ppidx m` by rw[MAX_DEF] >>
            metis_tac[IN_IMAGE]
          ]
        ],
        `prime p /\ p divides n` by metis_tac[prime_divisors_element] >>
        Cases_on `p IN park_off m n` >| [
          `p IN prime_divisors m /\ ppidx n < ppidx m` by metis_tac[park_off_element] >>
          `MAX (ppidx m) (ppidx n) = ppidx m` by rw[MAX_DEF] >>
          `p NOTIN park_on m n` by metis_tac[park_on_off_partition, IN_DISJOINT] >>
          `p IN prime_divisors m DIFF park_on m n` by rw[] >>
          metis_tac[IN_IMAGE],
          `p IN prime_divisors n DIFF park_off m n` by rw[] >>
          `p NOTIN prime_divisors m \/ ~(ppidx n < ppidx m)` by metis_tac[park_off_element] >| [
            `ppidx m = 0` by metis_tac[prime_divisors_element, prime_power_index_eq_0] >>
            `MAX (ppidx m) (ppidx n) = ppidx n` by rw[MAX_DEF] >>
            metis_tac[IN_IMAGE],
            `MAX (ppidx m) (ppidx n) = ppidx n` by rw[MAX_DEF] >>
            metis_tac[IN_IMAGE]
          ]
        ]
      ],
      `?p. p IN prime_divisors m DIFF park_on m n /\ (x = p ** ppidx m)` by prove_tac[IN_IMAGE] >>
      `p IN prime_divisors m /\ p NOTIN park_on m n` by metis_tac[IN_DIFF] >>
      `p IN total_prime_divisors m n` by rw[total_prime_divisors_element] >>
      `p NOTIN prime_divisors n \/ ~(ppidx m <= ppidx n)` by metis_tac[park_on_element] >| [
        `ppidx n = 0` by metis_tac[prime_divisors_element, prime_power_index_eq_0] >>
        `MAX (ppidx m) (ppidx n) = ppidx m` by rw[MAX_DEF] >>
        metis_tac[IN_IMAGE],
        `MAX (ppidx m) (ppidx n) = ppidx m` by rw[MAX_DEF] >>
        metis_tac[IN_IMAGE]
      ],
      `?p. p IN prime_divisors n DIFF park_off m n /\ (x = p ** ppidx n)` by prove_tac[IN_IMAGE] >>
      `p IN prime_divisors n /\ p NOTIN park_off m n` by metis_tac[IN_DIFF] >>
      `p IN total_prime_divisors m n` by rw[total_prime_divisors_element] >>
      `p NOTIN prime_divisors m \/ ~(ppidx n < ppidx m)` by metis_tac[park_off_element] >| [
        `ppidx m = 0` by metis_tac[prime_divisors_element, prime_power_index_eq_0] >>
        `MAX (ppidx m) (ppidx n) = ppidx n` by rw[MAX_DEF] >>
        metis_tac[IN_IMAGE],
        `MAX (ppidx m) (ppidx n) = ppidx n` by rw[MAX_DEF] >>
        metis_tac[IN_IMAGE]
      ]
    ],
    rw[DISJOINT_DEF] >>
    spose_not_then strip_assume_tac >>
    `?x. x IN u /\ x IN v` by metis_tac[MEMBER_NOT_EMPTY, IN_INTER] >>
    `?p. p IN prime_divisors m DIFF park_on m n /\ (x = p ** ppidx m)` by prove_tac[IN_IMAGE] >>
    `?q. q IN prime_divisors n DIFF park_off m n /\ (x = q ** prime_power_index q n)` by prove_tac[IN_IMAGE] >>
    `p IN prime_divisors m /\ p NOTIN park_on m n` by metis_tac[IN_DIFF] >>
    `q IN prime_divisors n /\ q NOTIN park_off m n` by metis_tac[IN_DIFF] >>
    `prime p /\ prime q /\ p divides m` by metis_tac[prime_divisors_element] >>
    `0 < ppidx m` by rw[prime_power_index_pos] >>
    `p = q` by metis_tac[prime_powers_eq] >>
    `p IN common_prime_divisors m n` by rw[common_prime_divisors_element] >>
    metis_tac[park_on_off_partition, IN_UNION]
  ]);

(* Theorem: 0 < m /\ 0 < n ==>
           let a = park m n in let b = gcd m n DIV a in
           let p = m DIV a in let q = (a * n) DIV (gcd m n) in
           (b = PROD_SET (IMAGE (\p. p ** ppidx n) (park_off m n))) /\
           (p = PROD_SET (IMAGE (\p. p ** ppidx m) ((prime_divisors m) DIFF (park_on m n)))) /\
           (q = PROD_SET (IMAGE (\p. p ** ppidx n) ((prime_divisors n) DIFF (park_off m n)))) /\
           (lcm m n = p * q) /\ coprime p q /\ (gcd m n = a * b) /\ (m = a * p) /\ (n = b * q) *)
(* Proof:
   Let s = IMAGE (\p. p ** MAX (ppidx m) (ppidx n)) (total_prime_divisors m n),
       u = IMAGE (\p. p ** ppidx m) (park_on m n),
       v = IMAGE (\p. p ** ppidx n) (park_off m n),
       h = IMAGE (\p. p ** ppidx m) ((prime_divisors m) DIFF (park_on m n)),
       k = IMAGE (\p. p ** ppidx n) ((prime_divisors n) DIFF (park_off m n)),
       a = PROD_SET u, b = PROD_SET v, c = PROD_SET s, p = PROD_SET h, q = PROD_SET k
       x = IMAGE (\p. p ** ppidx m) (prime_divisors m),
       y = IMAGE (\p. p ** ppidx n) (prime_divisors n),
   Let g = gcd m n.

   Step 1: GCD
   Note a = park m n                       by notation
    and g = a * b                          by gcd_park_decomposition

   Step 2: LCM
   Note c = lcm m n                        by lcm_prime_factorisation
   Note s =|= h # k                        by park_on_off_total_image_partition
    and FINITE (total_prime_divisors m n)  by total_prime_divisors_finite, 0 < m, 0 < n
    ==> FINITE s                           by IMAGE_FINITE
   also PAIRWISE_COPRIME s                 by total_prime_divisors_max_image_pairwise_coprime
   Thus (c = p * q) /\ coprime p q         by pairwise_coprime_prod_set_partition

   Step 3: Identities
   Note m = PROD_SET x                     by basic_prime_factorisation
        n = PROD_SET y                     by basic_prime_factorisation

   For the identity:  m = a * p
   We need:  PROD_SET x = PROD_SET u * PROD_SET h
   This requires:     x = u UNION h /\ DISJOINT u h, i.e. x =|= u # h
   or partition: (prime_divisors m) --> (park_on m n) and (prime_divisors m) DIFF (park_on m n)

   Claim: m = a * p
   Proof: Claim: h = x DIFF u
          Proof: Let pk = park_on m n, pm = prime_divisors m, f = \p. p ** ppidx m.
                 Note pk SUBSET pm                by park_on_element, prime_divisors_element, SUBSET_DEF
                  ==> INJ f pm UNIV               by INJ_DEF, prime_divisors_element,
                                                     prime_power_index_pos, prime_powers_eq
                   x DIFF u
                 = (IMAGE f pm) DIFF (IMAGE f pk) by notation
                 = IMAGE f (pm DIFF pk)           by IMAGE_DIFF
                 = h                              by notation
          Note FINITE x                           by prime_divisors_finite, IMAGE_FINITE
           and u SUBSET x                         by SUBSET_DEF, IMAGE_SUBSET
          Thus x =|= u # h                        by partition_by_subset
           ==> m = a * p                          by PROD_SET_PRODUCT_BY_PARTITION

   For the identity:  n = b * q
   We need:  PROD_SET y = PROD_SET v * PROD_SET k
   This requires:     y = v UNION k /\ DISJOINT v k, i.e y =|= v # k
   or partition: (prime_divisors n) --> (park_off m n) and (prime_divisors n) DIFF (park_off m n)

   Claim: n = b * q
   Proof: Claim: k = y DIFF v
          Proof: Let pk = park_off m n, pn = prime_divisors n, f = \p. p ** ppidx n.
                 Note pk SUBSET pn                by park_off_element, prime_divisors_element, SUBSET_DEF
                  ==> INJ f pn UNIV               by INJ_DEF, prime_divisors_element,
                                                     prime_power_index_pos, prime_powers_eq
                   y DIFF v
                 = (IMAGE f pn) DIFF (IMAGE f pk) by notation
                 = IMAGE f (pn DIFF pk)           by IMAGE_DIFF
                 = k                              by notation
          Note FINITE y                           by prime_divisors_finite, IMAGE_FINITE
           and v SUBSET y                         by SUBSET_DEF, IMAGE_SUBSET
          Thus y =|= v # k                        by partition_by_subset
           ==> n = b * q                          by PROD_SET_PRODUCT_BY_PARTITION

   Proof better:
         Note m * n = g * c                       by GCD_LCM
                    = (a * b) * (p * q)           by above
                    = (a * p) * (b * q)           by MULT_COMM, MULT_ASSOC
                    = m * (b * q)                 by m = a * p
         Thus     n = b * q                       by MULT_LEFT_CANCEL, 0 < m

   Thus g <> 0 /\ c <> 0     by GCD_EQ_0, LCM_EQ_0, m <> 0, n <> 0
    ==> p <> 0 /\ a <> 0     by MULT_EQ_0
    ==> b = g DIV a          by DIV_SOLVE_COMM, 0 < a
    ==> p = m DIV a          by DIV_SOLVE_COMM, 0 < a
    and q = c DIV p          by DIV_SOLVE_COMM, 0 < p
   Note g divides n          by GCD_IS_GREATEST_COMMON_DIVISOR
     so g divides a * n      by DIVIDES_MULTIPLE
     or a * n = a * (b * q)  by n = b * q from Claim 2
              = (a * b) * q  by MULT_ASSOC
              = g * q        by g = a * b
              = q * g        by MULT_COMM
     so g divides a * n      by divides_def
   Thus q = c DIV p                      by above
          = ((m * n) DIV g) DIV p        by lcm_def, m <> 0, n <> 0
          = (m * n) DIV (g * p)          by DIV_DIV_DIV_MULT, 0 < g, 0 < p
          = ((a * p) * n) DIV (g * p)    by m = a * p, Claim 1
          = (p * (a * n)) DIV (p * g)    by MULT_COMM, MULT_ASSOC
          = (a * n) DIV g                by DIV_COMMON_FACTOR, 0 < p, g divides a * n

   This gives all the assertions:
        (lcm m n = p * q) /\ coprime p q /\ (gcd m n = a * b) /\
        (m = a * p) /\ (n = b * q)       by MULT_COMM
*)

Theorem lcm_park_decomposition:
  !m n.
    0 < m /\ 0 < n ==>
    let a = park m n ; b = gcd m n DIV a ;
        p = m DIV a  ; q = (a * n) DIV (gcd m n)
    in
        b = PROD_SET (IMAGE (\p. p ** ppidx n) (park_off m n)) /\
        p = PROD_SET (IMAGE (\p. p ** ppidx m)
                      ((prime_divisors m) DIFF (park_on m n))) /\
        q = PROD_SET (IMAGE (\p. p ** ppidx n)
                      ((prime_divisors n) DIFF (park_off m n))) /\
        lcm m n = p * q /\ coprime p q /\ gcd m n = a * b /\ m = a * p /\
        n = b * q
Proof
  rpt strip_tac >>
  qabbrev_tac ‘s = IMAGE (\p. p ** MAX (ppidx m) (ppidx n)) (total_prime_divisors m n)’ >>
  qabbrev_tac ‘u = IMAGE (\p. p ** ppidx m) (park_on m n)’ >>
  qabbrev_tac ‘v = IMAGE (\p. p ** ppidx n) (park_off m n)’ >>
  qabbrev_tac ‘h = IMAGE (\p. p ** ppidx m) ((prime_divisors m) DIFF (park_on m n))’ >>
  qabbrev_tac ‘k = IMAGE (\p. p ** ppidx n) ((prime_divisors n) DIFF (park_off m n))’ >>
  qabbrev_tac ‘a = PROD_SET u’ >>
  qabbrev_tac ‘b = PROD_SET v’ >>
  qabbrev_tac ‘c = PROD_SET s’ >>
  qabbrev_tac ‘p = PROD_SET h’ >>
  qabbrev_tac ‘q = PROD_SET k’ >>
  qabbrev_tac ‘x = IMAGE (\p. p ** ppidx m) (prime_divisors m)’ >>
  qabbrev_tac ‘y = IMAGE (\p. p ** ppidx n) (prime_divisors n)’ >>
  qabbrev_tac ‘g = gcd m n’ >>
  ‘a = park m n’ by rw[Abbr‘a’] >>
  ‘g = a * b’ by metis_tac[gcd_park_decomposition] >>
  ‘c = lcm m n’ by rw[lcm_prime_factorisation, Abbr‘c’, Abbr‘s’] >>
  ‘s =|= h # k’ by metis_tac[park_on_off_total_image_partition] >>
  ‘FINITE s’ by rw[total_prime_divisors_finite, Abbr‘s’] >>
  ‘PAIRWISE_COPRIME s’
    by metis_tac[total_prime_divisors_max_image_pairwise_coprime] >>
  ‘(c = p * q) /\ coprime p q’
    by (simp[Abbr‘p’, Abbr‘q’, Abbr‘c’] >>
        metis_tac[pairwise_coprime_prod_set_partition]) >>
  ‘m = PROD_SET x’ by rw[basic_prime_factorisation, Abbr‘x’] >>
  ‘n = PROD_SET y’ by rw[basic_prime_factorisation, Abbr‘y’] >>
  ‘m = a * p’
    by (‘h = x DIFF u’
         by (‘park_on m n SUBSET prime_divisors m’
              by metis_tac[park_on_element,prime_divisors_element,SUBSET_DEF] >>
             ‘INJ (\p. p ** ppidx m) (prime_divisors m) UNIV’
               by (rw[INJ_DEF] >>
                   metis_tac[prime_divisors_element, prime_power_index_pos,
                             prime_powers_eq]) >>
             metis_tac[IMAGE_DIFF]) >>
        ‘FINITE x’ by rw[prime_divisors_finite, Abbr‘x’] >>
        ‘u SUBSET x’ by rw[SUBSET_DEF, Abbr‘u’, Abbr‘x’] >>
        ‘x =|= u # h’ by metis_tac[partition_by_subset] >>
        metis_tac[PROD_SET_PRODUCT_BY_PARTITION]) >>
  ‘n = b * q’
    by (‘m * n = g * c’ by metis_tac[GCD_LCM] >>
        ‘_ = (a * p) * (b * q)’ by rw[] >>
        ‘_ = m * (b * q)’ by rw[] >>
        metis_tac[MULT_LEFT_CANCEL, NOT_ZERO_LT_ZERO]) >>
  ‘m <> 0 /\ n <> 0’ by decide_tac >>
  ‘g <> 0 /\ c <> 0’ by metis_tac[GCD_EQ_0, LCM_EQ_0] >>
  ‘p <> 0 /\ a <> 0’ by metis_tac[MULT_EQ_0] >>
  ‘b = g DIV a’ by metis_tac[DIV_SOLVE_COMM, NOT_ZERO_LT_ZERO] >>
  ‘p = m DIV a’ by metis_tac[DIV_SOLVE_COMM, NOT_ZERO_LT_ZERO] >>
  ‘q = c DIV p’ by metis_tac[DIV_SOLVE_COMM, NOT_ZERO_LT_ZERO] >>
  ‘g divides a * n’ by metis_tac[divides_def, MULT_ASSOC, MULT_COMM] >>
  ‘c = (m * n) DIV g’ by metis_tac[lcm_def] >>
  ‘q = (m * n) DIV (g * p)’ by metis_tac[DIV_DIV_DIV_MULT, NOT_ZERO_LT_ZERO] >>
  ‘_ = (p * (a * n)) DIV (p * g)’ by metis_tac[MULT_COMM, MULT_ASSOC] >>
  ‘_ = (a * n) DIV g’ by metis_tac[DIV_COMMON_FACTOR, NOT_ZERO_LT_ZERO] >>
  metis_tac[]
QED

(* Theorem: 0 < m /\ 0 < n ==> let a = park m n in let p = m DIV a in let q = (a * n) DIV (gcd m n) in
            (lcm m n = p * q) /\ coprime p q *)
(* Proof: by lcm_park_decomposition *)
val lcm_park_decompose = store_thm(
  "lcm_park_decompose",
  ``!m n. 0 < m /\ 0 < n ==> let a = park m n in let p = m DIV a in let q = (a * n) DIV (gcd m n) in
         (lcm m n = p * q) /\ coprime p q``,
  metis_tac[lcm_park_decomposition]);

(* Theorem: 0 < m /\ 0 < n ==>
            let a = park m n in let b = gcd m n DIV a in
            let p = m DIV a in let q = (a * n) DIV (gcd m n) in
            (lcm m n = p * q) /\ coprime p q /\ (gcd m n = a * b) /\ (m = a * p) /\ (n = b * q) *)
(* Proof: by lcm_park_decomposition *)
val lcm_gcd_park_decompose = store_thm(
  "lcm_gcd_park_decompose",
  ``!m n. 0 < m /\ 0 < n ==>
        let a = park m n in let b = gcd m n DIV a in
        let p = m DIV a in let q = (a * n) DIV (gcd m n) in
         (lcm m n = p * q) /\ coprime p q /\ (gcd m n = a * b) /\ (m = a * p) /\ (n = b * q)``,
  metis_tac[lcm_park_decomposition]);

(* ------------------------------------------------------------------------- *)
(* Consecutive LCM Recurrence                                                *)
(* ------------------------------------------------------------------------- *)

(*
> optionTheory.some_def;
val it = |- !P. $some P = if ?x. P x then SOME (@x. P x) else NONE: thm
*)

(*
Cannot do this: Definition is schematic in the following variables: p

val lcm_fun_def = Define`
  lcm_fun n = if n = 0 then 1
      else if n = 1 then 1
    else if ?p k. 0 < k /\ prime p /\ (n = p ** k) then p * lcm_fun (n - 1)
  else lcm_fun (n - 1)
`;
*)

(* NOT this:
val lcm_fun_def = Define`
  (lcm_fun 1 = 1) /\
  (lcm_fun (SUC n) = case some p. ?k. (SUC n = p ** k) of
                    SOME p => p * (lcm_fun n)
                  | NONE   => lcm_fun n)
`;
*)

(*
Question: don't know how to prove termination
(* Define the B(n) function *)
val lcm_fun_def = Define`
  (lcm_fun 1 = 1) /\
  (lcm_fun n = case some p. ?k. 0 < k /\ prime p /\ (n = p ** k) of
                    SOME p => p * (lcm_fun (n - 1))
                  | NONE   => lcm_fun (n - 1))
`;

(* use a measure that is decreasing *)
e (WF_REL_TAC `measure (\n k. k * n)`);
e (rpt strip_tac);
*)

(* Define the Consecutive LCM Function *)
val lcm_fun_def = Define`
  (lcm_fun 0 = 1) /\
  (lcm_fun (SUC n) = if n = 0 then 1 else
      case some p. ?k. 0 < k /\ prime p /\ (SUC n = p ** k) of
        SOME p => p * (lcm_fun n)
      | NONE   => lcm_fun n)
`;

(* Another possible definition -- but need to work with pairs:

val lcm_fun_def = Define`
  (lcm_fun 0 = 1) /\
  (lcm_fun (SUC n) = if n = 0 then 1 else
      case some (p, k). 0 < k /\ prime p /\ (SUC n = p ** k) of
        SOME (p, k) => p * (lcm_fun n)
      | NONE        => lcm_fun n)
`;

By prime_powers_eq, when SOME, such (p, k) exists uniquely, or NONE.
*)

(* Get components of definition *)
val lcm_fun_0 = save_thm("lcm_fun_0", lcm_fun_def |> CONJUNCT1);
(* val lcm_fun_0 = |- lcm_fun 0 = 1: thm *)
val lcm_fun_SUC = save_thm("lcm_fun_SUC", lcm_fun_def |> CONJUNCT2);
(* val lcm_fun_SUC = |- !n. lcm_fun (SUC n) = if n = 0 then 1 else
                            case some p. ?k. SUC n = p ** k of
                            NONE => lcm_fun n | SOME p => p * lcm_fun n: thm *)

(* Theorem: lcm_fun 1 = 1 *)
(* Proof:
     lcm_fun 1
   = lcm_fun (SUC 0)   by ONE
   = 1                 by lcm_fun_def
*)
val lcm_fun_1 = store_thm(
  "lcm_fun_1",
  ``lcm_fun 1 = 1``,
  rw_tac bool_ss[lcm_fun_def, ONE]);

(* Theorem: lcm_fun 2 = 2 *)
(* Proof:
   Note 2 = 2 ** 1                by EXP_1
    and prime 2                   by PRIME_2
    and 0 < k /\ prime p /\ (2 ** 1 = p ** k)
    ==> (p = 2) /\ (k = 1)        by prime_powers_eq

     lcm_fun 2
   = lcm_fun (SUC 1)              by TWO
   = case some p. ?k. 0 < k /\ prime p /\ (SUC 1 = p ** k) of
       SOME p => p * (lcm_fun 1)
     | NONE   => lcm_fun 1)       by lcm_fun_def
   = SOME 2                       by some_intro, above
   = 2 * (lcm_fun 1)              by definition
   = 2 * 1                        by lcm_fun_1
   = 2                            by arithmetic
*)
Theorem lcm_fun_2:
  lcm_fun 2 = 2
Proof
  simp_tac bool_ss[lcm_fun_def, lcm_fun_1, TWO] >>
  `prime 2 /\ (2 = 2 ** 1)` by rw[PRIME_2] >>
  DEEP_INTRO_TAC some_intro >>
  rw_tac std_ss[]
  >- metis_tac[prime_powers_eq] >>
  metis_tac[DECIDE``0 <> 1``]
QED

(* Theorem: prime p /\ (?k. 0 < k /\ (SUC n = p ** k)) ==> (lcm_fun (SUC n) = p * lcm_fun n) *)
(* Proof: by lcm_fun_def, prime_powers_eq *)
Theorem lcm_fun_suc_some:
  !n p. prime p /\ (?k. 0 < k /\ (SUC n = p ** k)) ==>
        lcm_fun (SUC n) = p * lcm_fun n
Proof
  rw[lcm_fun_def] >>
  DEEP_INTRO_TAC some_intro >>
  rw_tac std_ss[] >>
  metis_tac[prime_powers_eq, DECIDE “~(0 < 0)”]
QED

(* Theorem: ~(?p k. 0 < k /\ prime p /\ (SUC n = p ** k)) ==> (lcm_fun (SUC n) = lcm_fun n) *)
(* Proof: by lcm_fun_def *)
val lcm_fun_suc_none = store_thm(
  "lcm_fun_suc_none",
  ``!n. ~(?p k. 0 < k /\ prime p /\ (SUC n = p ** k)) ==> (lcm_fun (SUC n) = lcm_fun n)``,
  rw[lcm_fun_def] >>
  DEEP_INTRO_TAC some_intro >>
  rw_tac std_ss[] >>
  `k <> 0` by decide_tac >>
  metis_tac[]);

(* Theorem: prime p /\ l <> [] /\ POSITIVE l ==> !x. MEM x l ==> ppidx x <= ppidx (list_lcm l) *)
(* Proof:
   Note ppidx (list_lcm l) = MAX_LIST (MAP ppidx l)   by list_lcm_prime_power_index
    and MEM (ppidx x) (MAP ppidx l)                   by MEM_MAP, MEM x l
   Thus ppidx x <= ppidx (list_lcm l)                 by MAX_LIST_PROPERTY
*)
val list_lcm_prime_power_index_lower = store_thm(
  "list_lcm_prime_power_index_lower",
  ``!l p. prime p /\ l <> [] /\ POSITIVE l ==> !x. MEM x l ==> ppidx x <= ppidx (list_lcm l)``,
  rpt strip_tac >>
  `ppidx (list_lcm l) = MAX_LIST (MAP ppidx l)` by rw[list_lcm_prime_power_index] >>
  `MEM (ppidx x) (MAP ppidx l)` by metis_tac[MEM_MAP] >>
  rw[MAX_LIST_PROPERTY]);

(*
The keys to show list_lcm_eq_lcm_fun are:
(1) Given a number n and a prime p that divides n, you can extract all the p's in n,
    giving n = (p ** k) * q for some k, and coprime p q. This is FACTOR_OUT_PRIME, or FACTOR_OUT_POWER.
(2) To figure out the LCM, use the GCD_LCM identity, i.e. figure out first the GCD.

Therefore, let m = consecutive LCM.
Consider given two number m, n; and a prime p with p divides n.
By (1), n = (p ** k) * q, with coprime p q.
If q > 1, then n = a * b where a, b are both less than n, and coprime a b: take a = p ** k, b = q.
          Now, if a divides m, and b divides m --- which is the case when m = consecutive LCM,
          By coprime a b, (a * b) divides m, or n divides m,
          or gcd m n = n       by divides_iff_gcd_fix
          or lcm m n = (m * n) DIV (gcd m n) = (m * n) DIV n = m (or directly by divides_iff_lcm_fix)
If q = 1, then n is a pure prime p power: n = p ** k, with k > 0.
          Now, m = (p ** j) * t  with coprime p t, although it may be that j = 0.
          For list LCM, j <= k, since the numbers are consecutive. In fact, j = k - 1
          Thus n = (p ** j) * p, and gcd m n = (p ** j) gcd p t = (p ** j)  by GCD_COMMON_FACTOR
          or lcm m n = (m * n) DIV (gcd m n)
                     = m * (n DIV (p ** j))
                     = m * ((p ** j) * p) DIV (p ** j)
                     = m * p = p * m
*)

(* Theorem: prime p /\ (n + 2 = p ** k) ==> (list_lcm [1 .. (n + 2)] = p * list_lcm [1 .. (n + 1)]) *)
(* Proof:
   Note n + 2 = SUC (SUC n) <> 1         by ADD1, TWO
   Thus p ** k <> 1, or k <> 0           by EXP_EQ_1
    ==> ?h. k = SUC h                    by num_CASES
    and n + 2 = x ** SUC h               by above

    Let l = [1 .. (n + 1)], m = list_lcm l.
    Note POSITIVE l                      by leibniz_vertical_pos, EVERY_MEM
     Now h < SUC h = k                   by LESS_SUC
      so p ** h < p ** k = n + 2         by EXP_BASE_LT_MONO, 1 < p
     ==> MEM (p ** h) l                  by leibniz_vertical_mem
    Note l <> []                         by leibniz_vertical_not_nil
      so ppidx (p ** h) <= ppidx m       by list_lcm_prime_power_index_lower
      or              h <= ppidx m       by prime_power_index_prime_power

    Claim: ppidx m <= h
    Proof: By contradiction, suppose h < ppidx m.
           Then k <= ppidx m                       by k = SUC h
            and p ** k divides p ** (ppidx m)      by power_divides_iff
            But p ** (ppidx m) divides m           by prime_power_factor_divides
             so p ** k divides m                   by DIVIDES_TRANS
            ==> ?z. MEM z l /\ (n + 2) divides z   by list_lcm_prime_power_factor_member
             or (n + 2) <= z                       by DIVIDES_LE, 0 < z, all members are positive
            Now z <= n + 1                         by leibniz_vertical_mem
           This leads to a contradiction: n + 2 <= n + 1.

    Therefore ppidx m = h                          by h <= ppidx m /\ ppidx m <= h, by Claim.

       list_lcm [1 .. (n + 2)]
     = list_lcm (SNOC (n + 2) l)                   by leibniz_vertical_snoc, n + 2 = SUC (n + 1)
     = lcm (n + 2) m                               by list_lcm_snoc
     = p * m                                       by lcm_special_for_prime_power
*)
val list_lcm_with_last_prime_power = store_thm(
  "list_lcm_with_last_prime_power",
  ``!n p k. prime p /\ (n + 2 = p ** k) ==> (list_lcm [1 .. (n + 2)] = p * list_lcm [1 .. (n + 1)])``,
  rpt strip_tac >>
  `n + 2 <> 1` by decide_tac >>
  `0 <> k` by metis_tac[EXP_EQ_1] >>
  `?h. k = SUC h` by metis_tac[num_CASES] >>
  qabbrev_tac `l = leibniz_vertical n` >>
  qabbrev_tac `m = list_lcm l` >>
  `POSITIVE l` by rw[leibniz_vertical_pos, EVERY_MEM, Abbr`l`] >>
  `h < k` by rw[] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `p ** h < p ** k` by rw[EXP_BASE_LT_MONO] >>
  `0 < p ** h` by rw[PRIME_POS, EXP_POS] >>
  `p ** h <= n + 1` by decide_tac >>
  `MEM (p ** h) l` by rw[leibniz_vertical_mem, Abbr`l`] >>
  `ppidx (p ** h) = h` by rw[prime_power_index_prime_power] >>
  `l <> []` by rw[leibniz_vertical_not_nil, Abbr`l`] >>
  `h <= ppidx m` by metis_tac[list_lcm_prime_power_index_lower] >>
  `ppidx m <= h` by
  (spose_not_then strip_assume_tac >>
  `k <= ppidx m` by decide_tac >>
  `p ** k divides p ** (ppidx m)` by rw[power_divides_iff] >>
  `p ** (ppidx m) divides m` by rw[prime_power_factor_divides] >>
  `p ** k divides m` by metis_tac[DIVIDES_TRANS] >>
  `?z. MEM z l /\ (n + 2) divides z` by metis_tac[list_lcm_prime_power_factor_member] >>
  `(n + 2) <= z` by rw[DIVIDES_LE] >>
  `z <= n + 1` by metis_tac[leibniz_vertical_mem, Abbr`l`] >>
  decide_tac) >>
  `h = ppidx m` by decide_tac >>
  `list_lcm [1 .. (n + 2)] = list_lcm (SNOC (n + 2) l)` by rw[GSYM leibniz_vertical_snoc, Abbr`l`] >>
  `_ = lcm (n + 2) m` by rw[list_lcm_snoc, Abbr`m`] >>
  `_ = p * m` by rw[lcm_special_for_prime_power] >>
  rw[]);

(* Theorem: (!p k. (k = 0) \/ ~prime p \/ n + 2 <> p ** k) ==>
            (list_lcm [1 .. (n + 2)] = list_lcm [1 .. (n + 1)]) *)
(* Proof:
   Note 1 < n + 2,
    ==> ?a b. (n + 2 = a * b) /\ coprime a b /\
              1 < a /\ 1 < b /\ a < n + 2 /\ b < n + 2    by prime_power_or_coprime_factors
     or 0 < a /\ 0 < b /\ a <= n + 1 /\ b <= n + 1        by arithmetic
    Let l = leibniz_vertical n, m = list_lcm l.
    Then MEM a l and MEM b l                              by leibniz_vertical_mem
     and a divides m /\ b divides m                       by list_lcm_is_common_multiple
     ==> (n + 2) divides m                                by coprime_product_divides, coprime a b

      list_lcm (leibniz_vertical (n + 1))
    = list_lcm (SNOC (n + 2) l)                           by leibniz_vertical_snoc
    = lcm (n + 2) m                                       by list_lcm_snoc
    = m                                                   by divides_iff_lcm_fix
*)
val list_lcm_with_last_non_prime_power = store_thm(
  "list_lcm_with_last_non_prime_power",
  ``!n. (!p k. (k = 0) \/ ~prime p \/ n + 2 <> p ** k) ==>
       (list_lcm [1 .. (n + 2)] = list_lcm [1 .. (n + 1)])``,
  rpt strip_tac >>
  `1 < n + 2` by decide_tac >>
  `!k. ~(0 < k) = (k = 0)` by decide_tac >>
  `?a b. (n + 2 = a * b) /\ coprime a b /\ 1 < a /\ 1 < b /\ a < n + 2 /\ b < n + 2` by metis_tac[prime_power_or_coprime_factors] >>
  `0 < a /\ 0 < b /\ a <= n + 1 /\ b <= n + 1` by decide_tac >>
  qabbrev_tac `l = leibniz_vertical n` >>
  qabbrev_tac `m = list_lcm l` >>
  `MEM a l /\ MEM b l` by rw[leibniz_vertical_mem, Abbr`l`] >>
  `a divides m /\ b divides m` by rw[list_lcm_is_common_multiple, Abbr`m`] >>
  `(n + 2) divides m` by rw[coprime_product_divides] >>
  `list_lcm [1 .. (n + 2)] = list_lcm (SNOC (n + 2) l)` by rw[GSYM leibniz_vertical_snoc, Abbr`l`] >>
  `_ = lcm (n + 2) m` by rw[list_lcm_snoc, Abbr`m`] >>
  `_ = m` by rw[GSYM divides_iff_lcm_fix] >>
  rw[]);

(* Theorem: list_lcm [1 .. (n + 1)] = lcm_fun (n + 1) *)
(* Proof:
   By induction on n.
   Base: list_lcm [1 .. 0 + 1] = lcm_fun (0 + 1)
      LHS = list_lcm [1 .. 0 + 1]
          = list_lcm [1]                by leibniz_vertical_0
          = 1                           by list_lcm_sing
      RHS = lcm_fun (0 + 1)
          = lcm_fun 1                   by ADD
          = 1 = LHS                     by lcm_fun_1
   Step: list_lcm [1 .. n + 1] = lcm_fun (n + 1) ==>
         list_lcm [1 .. SUC n + 1] = lcm_fun (SUC n + 1)
      Note (SUC n) <> 0                 by SUC_NOT_ZERO
       and n + 2 = SUC (SUC n)          by ADD1, TWO
      By lcm_fun_def, this is to show:
         list_lcm [1 .. SUC n + 1] = case some p. ?k. 0 < k /\ prime p /\ (SUC (SUC n) = p ** k) of
                                       NONE => lcm_fun (SUC n)
                                     | SOME p => p * lcm_fun (SUC n)

      If SOME,
         Then 0 < k /\ prime p /\ SUC (SUC n) = p ** k
         This is the case of perfect prime power.
            list_lcm (leibniz_vertical (SUC n))
          = list_lcm (leibniz_vertical (n + 1))    by ADD1
          = p * list_lcm (leibniz_vertical n)      by list_lcm_with_last_prime_power
          = p * lcm_fun (SUC n)                    by induction hypothesis
      If NONE,
         Then !x k. ~(0 < k) \/ ~prime x \/ SUC (SUC n) <> x ** k
         This is the case of non-perfect prime power.
             list_lcm (leibniz_vertical (SUC n))
           = list_lcm (leibniz_vertical (n + 1))   by ADD1
           = list_lcm (leibniz_vertical n)         by list_lcm_with_last_non_prime_power
           = lcm_fun (SUC n)                       by induction hypothesis
*)
val list_lcm_eq_lcm_fun = store_thm(
  "list_lcm_eq_lcm_fun",
  ``!n. list_lcm [1 .. (n + 1)] = lcm_fun (n + 1)``,
  Induct >-
  rw[leibniz_vertical_0, list_lcm_sing, lcm_fun_1] >>
  `(SUC n) + 1 = SUC (SUC n)` by rw[] >>
  `list_lcm [1 .. SUC n + 1] = case some p. ?k. 0 < k /\ prime p /\ ((SUC n) + 1 = p ** k) of
                                       NONE => lcm_fun (SUC n)
                                     | SOME p => p * lcm_fun (SUC n)` suffices_by rw[lcm_fun_def] >>
  `n + 2 = (SUC n) + 1` by rw[] >>
  DEEP_INTRO_TAC some_intro >>
  rw[] >-
  metis_tac[list_lcm_with_last_prime_power, ADD1] >>
  metis_tac[list_lcm_with_last_non_prime_power, ADD1]);

(* This is a major milestone theorem! *)

(* Theorem: 2 ** n <= lcm_fun (SUC n) *)
(* Proof:
   Note 2 ** n <= list_lcm (leibniz_vertical n)          by lcm_lower_bound
    and list_lcm (leibniz_vertical n) = lcm_fun (SUC n)  by list_lcm_eq_lcm_fun\
     so 2 ** n <= lcm_fun (SUC n)
*)
val lcm_fun_lower_bound = store_thm(
  "lcm_fun_lower_bound",
  ``!n. 2 ** n <= lcm_fun (n + 1)``,
  rw[GSYM list_lcm_eq_lcm_fun, lcm_lower_bound]);

(* Theorem: 0 < n ==> 2 ** (n - 1) <= lcm_fun n *)
(* Proof:
   Note 0 < n ==> ?m. n = SUC m      by num_CASES
     or m = n - 1                    by SUC_SUB1
   Apply lcm_fun_lower_bound,
     put n = SUC m, and the result follows.
*)
val lcm_fun_lower_bound_alt = store_thm(
  "lcm_fun_lower_bound_alt",
  ``!n. 0 < n ==> 2 ** (n - 1) <= lcm_fun n``,
  rpt strip_tac >>
  `n <> 0` by decide_tac >>
  `?m. n = SUC m` by metis_tac[num_CASES] >>
  `(n - 1 = m) /\ (n = m + 1)` by decide_tac >>
  metis_tac[lcm_fun_lower_bound]);

(* Theorem: 0 < n /\ prime p /\ (SUC n = p ** ppidx (SUC n)) ==>
            (ppidx (SUC n) = SUC (ppidx (list_lcm [1 .. n]))) *)
(* Proof:
   Let z = SUC n,
   Then z = p ** ppidx z              by given
   Note n <> 0 /\ z <> 1              by 0 < n
    ==> ppidx z <> 0                  by EXP_EQ_1, z <> 1
    ==> ?h. ppidx z = SUC h           by num_CASES

   Let l = [1 .. n], m = list_lcm l, j = ppidx m.
   Current goal is to show: SUC h = SUC j
   which only need to show:     h = j    by INV_SUC_EQ
   Note l <> []                          by listRangeINC_NIL
    and POSITIVE l                       by listRangeINC_MEM, [1]
   Also 1 < p                            by ONE_LT_PRIME

   Claim: h <= j
   Proof: Note h < SUC h                 by LESS_SUC
          Thus p ** h < z = p ** SUC h   by EXP_BASE_LT_MONO, 1 < p
           ==> p ** h <= n               by z = SUC n
          Also 0 < p ** h                by EXP_POS, 0 < p
           ==> MEM (p ** h) l            by listRangeINC_MEM, 0 < p ** h /\ p ** h <= n
          Note ppidx (p ** h) = h        by prime_power_index_prime_power
          Thus h <= j = ppidx m          by list_lcm_prime_power_index_lower, l <> []

   Claim: j <= h
   Proof: By contradiction, suppose h < j.
          Then SUC h <= j                by arithmetic
           ==> z divides p ** j          by power_divides_iff, 1 < p, z = p ** SUC h, SUC h <= j
           But p ** j divides m          by prime_power_factor_divides
           ==> z divides m               by DIVIDES_TRANS
          Thus ?y. MEM y l /\ z divides y    by list_lcm_prime_power_factor_member, l <> []
          Note 0 < y                     by all members of l, [1]
            so z <= y                    by DIVIDES_LE, 0 < y
            or SUC n <= y                by z = SUC n
           But ?u. n = u + 1             by num_CASES, ADD1, n <> 0
            so y <= n                    by listRangeINC_MEM, MEM y l
          This leads to SUC n <= n, a contradiction.

   By these two claims, h = j.
*)
val prime_power_index_suc_special = store_thm(
  "prime_power_index_suc_special",
  ``!n p. 0 < n /\ prime p /\ (SUC n = p ** ppidx (SUC n)) ==>
         (ppidx (SUC n) = SUC (ppidx (list_lcm [1 .. n])))``,
  rpt strip_tac >>
  qabbrev_tac `z = SUC n` >>
  `n <> 0 /\ z <> 1` by rw[Abbr`z`] >>
  `?h. ppidx z = SUC h` by metis_tac[EXP_EQ_1, num_CASES] >>
  qabbrev_tac `l = [1 .. n]` >>
  qabbrev_tac `m = list_lcm l` >>
  qabbrev_tac `j = ppidx m` >>
  `h <= j /\ j <= h` suffices_by rw[] >>
  `l <> []` by rw[listRangeINC_NIL, Abbr`l`] >>
  `POSITIVE l` by rw[Abbr`l`] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  rpt strip_tac >| [
    `h < SUC h` by rw[] >>
    `p ** h < z` by metis_tac[EXP_BASE_LT_MONO] >>
    `p ** h <= n` by rw[Abbr`z`] >>
    `0 < p ** h` by rw[EXP_POS] >>
    `MEM (p ** h) l` by rw[Abbr`l`] >>
    metis_tac[prime_power_index_prime_power, list_lcm_prime_power_index_lower],
    spose_not_then strip_assume_tac >>
    `SUC h <= j` by decide_tac >>
    `z divides p ** j` by metis_tac[power_divides_iff] >>
    `p ** j divides m` by rw[prime_power_factor_divides, Abbr`j`] >>
    `z divides m` by metis_tac[DIVIDES_TRANS] >>
    `?y. MEM y l /\ z divides y` by metis_tac[list_lcm_prime_power_factor_member] >>
    `SUC n <= y` by rw[DIVIDES_LE, Abbr`z`] >>
    `y <= n` by metis_tac[listRangeINC_MEM] >>
    decide_tac
  ]);

(* Theorem: 0 < n /\ prime p /\ (n + 1 = p ** ppidx (n + 1)) ==>
            (ppidx (n + 1) = 1 + (ppidx (list_lcm [1 .. n]))) *)
(* Proof: by prime_power_index_suc_special, ADD1, ADD_COMM *)
val prime_power_index_suc_property = store_thm(
  "prime_power_index_suc_property",
  ``!n p. 0 < n /\ prime p /\ (n + 1 = p ** ppidx (n + 1)) ==>
         (ppidx (n + 1) = 1 + (ppidx (list_lcm [1 .. n])))``,
  metis_tac[prime_power_index_suc_special, ADD1, ADD_COMM]);

(* ------------------------------------------------------------------------- *)
(* Consecutive LCM Recurrence - Rework                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: SING (prime_divisors (n + 1)) ==>
            (list_lcm [1 .. (n + 1)] = CHOICE (prime_divisors (n + 1)) * list_lcm [1 .. n]) *)
(* Proof:
   Let z = n + 1.
   Then ?p. prime_divisors z = {p}      by SING_DEF
   By CHOICE_SING, this is to show: list_lcm [1 .. z] = p * list_lcm [1 .. n]

   Note prime p /\ (z = p ** ppidx z)   by prime_divisors_sing_property, CHOICE_SING
    and z <> 1 /\ n <> 0                by prime_divisors_1, NOT_SING_EMPTY, ADD
   Note ppidx z <> 0                    by EXP_EQ_1, z <> 1
    ==> ?h. ppidx z = SUC h             by num_CASES, EXP
   Thus z = p ** SUC h = p ** h * p     by EXP, MULT_COMM

   Let m = list_lcm [1 .. n], j = ppidx m.
   Note EVERY_POSITIVE l                by listRangeINC_MEM, EVERY_MEM
     so 0 < m                           by list_lcm_pos
    ==> ?q. (m = p ** j * q) /\
            coprime p q                 by prime_power_index_eqn
   Note 0 < n                           by n <> 0
   Thus SUC h = SUC j                   by prime_power_index_suc_special, ADD1, 0 < n
     or     h = j                       by INV_SUC_EQ

        list_lcm [1 .. z]
      = lcm z m                         by list_lcm_suc
      = p * m                           by lcm_special_for_prime_power
*)
Theorem list_lcm_by_last_prime_power:
  !n.
    SING (prime_divisors (n + 1)) ==>
    list_lcm [1 .. (n + 1)] =
    CHOICE (prime_divisors (n + 1)) * list_lcm [1 .. n]
Proof
  rpt strip_tac >>
  qabbrev_tac ‘z = n + 1’ >>
  ‘?p. prime_divisors z = {p}’ by rw[GSYM SING_DEF] >>
  rw[] >>
  ‘prime p /\ (z = p ** ppidx z)’ by metis_tac[prime_divisors_sing_property, CHOICE_SING] >>
  ‘z <> 1 /\ n <> 0’ by metis_tac[prime_divisors_1, NOT_SING_EMPTY, ADD] >>
  ‘?h. ppidx z = SUC h’ by metis_tac[EXP_EQ_1, num_CASES] >>
  qabbrev_tac ‘m = list_lcm [1 .. n]’ >>
  qabbrev_tac ‘j = ppidx m’ >>
  ‘0 < m’ by rw[list_lcm_pos, EVERY_MEM, Abbr‘m’] >>
  ‘?q. (m = p ** j * q) /\ coprime p q’ by metis_tac[prime_power_index_eqn] >>
  ‘0 < n’ by decide_tac >>
  ‘SUC h = SUC j’ by metis_tac[prime_power_index_suc_special, ADD1] >>
  ‘h = j’ by decide_tac >>
  ‘list_lcm [1 .. z] = lcm z m’ by rw[list_lcm_suc, Abbr‘z’, Abbr‘m’] >>
  ‘_ = p * m’ by metis_tac[lcm_special_for_prime_power] >>
  rw[]
QED

(* Theorem: ~ SING (prime_divisors (n + 1)) ==> (list_lcm [1 .. (n + 1)] = list_lcm [1 .. n]) *)
(* Proof:
   Let z = n + 1, l = [1 .. n], m = list_lcm l.
   The goal is to show: list_lcm [1 .. z] = m.

   If z = 1,
      Then n = 0               by 1 = n + 1
      LHS = list_lcm [1 .. z]
          = list_lcm [1 .. 1]    by z = 1
          = list_lcm [1]         by listRangeINC_SING
          = 1                    by list_lcm_sing
      RHS = list_lcm [1 .. n]
          = list_lcm [1 .. 0]    by n = 0
          = list_lcm []          by listRangeINC_EMPTY
          = 1 = LHS              by list_lcm_nil
   If z <> 1,
      Note z <> 0, or 0 < z      by z = n + 1
       ==> ?p. prime p /\ p divides z       by PRIME_FACTOR, z <> 1
       and 0 < ppidx z                      by prime_power_index_pos, 0 < z
       Let t = p ** ppidx z.
      Then ?q. (z = t * q) /\ coprime p q   by prime_power_index_eqn, 0 < z
       ==> coprime t q                      by coprime_exp
      Thus t <> 0 /\ q <> 0                 by MULT_EQ_0, z <> 0
       and q <> 1                           by prime_divisors_sing, MULT_RIGHT_1, ~SING (prime_divisors z)
      Note p <> 1                           by NOT_PRIME_1
       and t <> 1                           by EXP_EQ_1, ppidx z <> 0
      Thus 0 < q /\ q < n + 1               by z = t * q = n + 1
       and 0 < t /\ t < n + 1               by z = t * q = n + 1

      Then MEM q l                          by listRangeINC_MEM, 1 <= q <= n
       and MEM t l                          by listRangeINC_MEM, 1 <= t <= n
       ==> q divides m /\ t divides m       by list_lcm_is_common_multiple
       ==> q * t = z divides m              by coprime_product_divides, coprime t q

         list_lcm [1 .. z]
       = lcm z m                 by list_lcm_suc
       = m                       by divides_iff_lcm_fix
*)

Theorem list_lcm_by_last_non_prime_power:
  !n. ~ SING (prime_divisors (n + 1)) ==>
      list_lcm [1 .. (n + 1)] = list_lcm [1 .. n]
Proof
  rpt strip_tac >>
  qabbrev_tac `z = n + 1` >>
  Cases_on `z = 1` >| [
    `n = 0` by rw[Abbr`z`] >>
    `([1 .. z] = [1]) /\ ([1 .. n] = [])` by rw[listRangeINC_EMPTY] >>
    rw[list_lcm_sing, list_lcm_nil],
    `z <> 0 /\ 0 < z` by rw[Abbr`z`] >>
    `?p. prime p /\ p divides z` by rw[PRIME_FACTOR] >>
    `0 < ppidx z` by rw[prime_power_index_pos] >>
    qabbrev_tac `t = p ** ppidx z` >>
    `?q. (z = t * q) /\ coprime p q /\ coprime t q`
      by metis_tac[prime_power_index_eqn, coprime_exp] >>
    `t <> 0 /\ q <> 0` by metis_tac[MULT_EQ_0] >>
    `q <> 1` by metis_tac[prime_divisors_sing, MULT_RIGHT_1] >>
    `t <> 1` by metis_tac[EXP_EQ_1, NOT_PRIME_1, NOT_ZERO_LT_ZERO] >>
    `0 < q /\ q < n + 1` by rw[Abbr`z`] >>
    `0 < t /\ t < n + 1` by rw[Abbr`z`] >>
    qabbrev_tac `l = [1 .. n]` >>
    qabbrev_tac `m = list_lcm l` >>
    `MEM q l /\ MEM t l` by rw[Abbr`l`] >>
    `q divides m /\ t divides m`
      by simp[list_lcm_is_common_multiple, Abbr`m`] >>
    `z divides m`
      by (simp[] >> metis_tac[coprime_sym, coprime_product_divides]) >>
    `list_lcm [1 .. z] = lcm z m` by rw[list_lcm_suc, Abbr`z`, Abbr`m`] >>
    `_ = m` by rw[GSYM divides_iff_lcm_fix] >>
    rw[]
  ]
QED

(* Theorem: list_lcm [1 .. (n + 1)] = let s = prime_divisors (n + 1) in
            if SING s then CHOICE s * list_lcm [1 .. n] else list_lcm [1 .. n] *)
(* Proof: by list_lcm_with_last_prime_power, list_lcm_with_last_non_prime_power *)
val list_lcm_recurrence = store_thm(
  "list_lcm_recurrence",
  ``!n. list_lcm [1 .. (n + 1)] = let s = prime_divisors (n + 1) in
       if SING s then CHOICE s * list_lcm [1 .. n] else list_lcm [1 .. n]``,
  rw[list_lcm_by_last_prime_power, list_lcm_by_last_non_prime_power]);

(* Theorem: (prime_divisors (n + 1) = {p}) ==> (list_lcm [1 .. (n + 1)] = p * list_lcm [1 .. n]) *)
(* Proof: by list_lcm_by_last_prime_power, SING_DEF *)
val list_lcm_option_last_prime_power = store_thm(
  "list_lcm_option_last_prime_power",
  ``!n p. (prime_divisors (n + 1) = {p}) ==> (list_lcm [1 .. (n + 1)] = p * list_lcm [1 .. n])``,
  rw[list_lcm_by_last_prime_power, SING_DEF]);

(* Theorem:  (!p. prime_divisors (n + 1) <> {p}) ==> (list_lcm [1 .. (n + 1)] = list_lcm [1 .. n]) *)
(* Proof: by ist_lcm_by_last_non_prime_power, SING_DEF *)
val list_lcm_option_last_non_prime_power = store_thm(
  "list_lcm_option_last_non_prime_power",
  ``!n. (!p. prime_divisors (n + 1) <> {p}) ==> (list_lcm [1 .. (n + 1)] = list_lcm [1 .. n])``,
  rw[list_lcm_by_last_non_prime_power, SING_DEF]);

(* Theorem: list_lcm [1 .. (n + 1)] = case some p. (prime_divisors (n + 1)) = {p} of
              NONE => list_lcm [1 .. n]
            | SOME p => p * list_lcm [1 .. n] *)
(* Proof:
   For SOME p, true by list_lcm_option_last_prime_power
   For NONE, true   by list_lcm_option_last_non_prime_power
*)
val list_lcm_option_recurrence = store_thm(
  "list_lcm_option_recurrence",
  ``!n. list_lcm [1 .. (n + 1)] = case some p. (prime_divisors (n + 1)) = {p} of
              NONE => list_lcm [1 .. n]
            | SOME p => p * list_lcm [1 .. n]``,
  rpt strip_tac >>
  DEEP_INTRO_TAC optionTheory.some_intro >>
  rw[list_lcm_option_last_prime_power, list_lcm_option_last_non_prime_power]);

(* ------------------------------------------------------------------------- *)
(* Relating Consecutive LCM to Prime Functions                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: MEM x (SET_TO_LIST (prime_powers_upto n)) <=> ?p. (x = p ** LOG p n) /\ prime p /\ p <= n *)
(* Proof:
   Let s = prime_powers_upto n.
   Then FINITE s                             by prime_powers_upto_finite
    and !x. x IN s <=> MEM x (SET_TO_LIST s) by MEM_SET_TO_LIST
    The result follows                       by prime_powers_upto_element
*)
val prime_powers_upto_list_mem = store_thm(
  "prime_powers_upto_list_mem",
  ``!n x. MEM x (SET_TO_LIST (prime_powers_upto n)) <=> ?p. (x = p ** LOG p n) /\ prime p /\ p <= n``,
  rw[MEM_SET_TO_LIST, prime_powers_upto_element, prime_powers_upto_finite]);

(*
LOG_EQ_0  |- !a b. 1 < a /\ 0 < b ==> ((LOG a b = 0) <=> b < a)
*)

(* Theorem: prime p /\ p <= n ==> p ** LOG p n divides set_lcm (prime_powers_upto n) *)
(* Proof:
   Let s = prime_powers_upto n.
   Note FINITE s                        by prime_powers_upto_finite
    and p ** LOG p n IN s               by prime_powers_upto_element_alt
    ==> p ** LOG p n divides set_lcm s  by set_lcm_is_common_multiple
*)
val prime_powers_upto_lcm_prime_to_log_divisor = store_thm(
  "prime_powers_upto_lcm_prime_to_log_divisor",
  ``!n p. prime p /\ p <= n ==> p ** LOG p n divides set_lcm (prime_powers_upto n)``,
  rpt strip_tac >>
  `FINITE (prime_powers_upto n)` by rw[prime_powers_upto_finite] >>
  `p ** LOG p n IN prime_powers_upto n` by rw[prime_powers_upto_element_alt] >>
  rw[set_lcm_is_common_multiple]);

(* Theorem: prime p /\ p <= n ==> p divides set_lcm (prime_powers_upto n) *)
(* Proof:
   Note 1 < p                           by ONE_LT_PRIME
     so LOG p n <> 0                    by LOG_EQ_0, 1 < p
    ==> p divides p ** LOG p n          by divides_self_power, 1 < p

   Note p ** LOG p n divides set_lcm s  by prime_powers_upto_lcm_prime_to_log_divisor
   Thus p divides set_lcm s             by DIVIDES_TRANS
*)
val prime_powers_upto_lcm_prime_divisor = store_thm(
  "prime_powers_upto_lcm_prime_divisor",
  ``!n p. prime p /\ p <= n ==> p divides set_lcm (prime_powers_upto n)``,
  rpt strip_tac >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `LOG p n <> 0` by rw[LOG_EQ_0] >>
  `p divides p ** LOG p n` by rw[divides_self_power] >>
  `p ** LOG p n divides set_lcm (prime_powers_upto n)` by rw[prime_powers_upto_lcm_prime_to_log_divisor] >>
  metis_tac[DIVIDES_TRANS]);

(* Theorem: prime p /\ p <= n ==> p ** ppidx n divides set_lcm (prime_powers_upto n) *)
(* Proof:
   Note 1 < p                by ONE_LT_PRIME
    and 0 < n                by p <= n
    ==> ppidx n <= LOG p n   by prime_power_index_le_log_index, 0 < n
   Thus p ** ppidx n divides p ** LOG p n                   by power_divides_iff, 1 < p
    and p ** LOG p n divides set_lcm (prime_powers_upto n)  by prime_powers_upto_lcm_prime_to_log_divisor
     or p ** ppidx n divides set_lcm (prime_powers_upto n)  by DIVIDES_TRANS
*)
val prime_powers_upto_lcm_prime_to_power_divisor = store_thm(
  "prime_powers_upto_lcm_prime_to_power_divisor",
  ``!n p. prime p /\ p <= n ==> p ** ppidx n divides set_lcm (prime_powers_upto n)``,
  rpt strip_tac >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `0 < n` by decide_tac >>
  `ppidx n <= LOG p n` by rw[prime_power_index_le_log_index] >>
  `p ** ppidx n divides p ** LOG p n` by rw[power_divides_iff] >>
  `p ** LOG p n divides set_lcm (prime_powers_upto n)` by rw[prime_powers_upto_lcm_prime_to_log_divisor] >>
  metis_tac[DIVIDES_TRANS]);

(* The next theorem is based on this example:
Take n = 10,
prime_powers_upto 10 = {2^3; 3^2; 5^1; 7^1} = {8; 9; 5; 7}
set_lcm (prime_powers_upto 10) = 2520
For any 1 <= x <= 10, e.g. x = 6.
6 <= 10, 6 divides set_lcm (prime_powers_upto 10).

The reason is that:
6 = PROD_SET (IMAGE (\p. p ** ppidx 6) (prime_divisors 6))   by prime_factorisation
prime_divisors 6 = {2; 3}
Because 2, 3 <= 6, 6 <= 10, the divisors 2,3 <= 10           by DIVIDES_LE
Thus 2^(LOG 2 10) = 2^3, 3^(LOG 3 10) = 3^2 IN prime_powers_upto 10)    by prime_powers_upto_element_alt
But  2^(ppidx 6) = 2^1 = 2 divides 6, 3^(ppidx 6) = 3^1 = 3 divides 6   by prime_power_index_def
 so  2^(ppidx 6) <= 10   and 3^(ppidx 6) <= 10.

In this example, 2^1 < 2^3    3^1 < 3^2  how to compare (ppidx x) with (LOG p n) in general? ##
Due to this,  2^(ppidx 6) divides 2^(LOG 2 10),    by prime_powers_divide
       and    3^(ppidx 6) divides 3^(LOG 3 10),
And 2^(LOG 2 10) divides set_lcm (prime_powers_upto 10)    by prime_powers_upto_lcm_prime_to_log_divisor
and 3^(LOG 3 10) divides set_lcm (prime_powers_upto 10)    by prime_powers_upto_lcm_prime_to_log_divisor
or !z. z IN (IMAGE (\p. p ** ppidx 6) (prime_divisors 6))
   ==> z divides set_lcm (prime_powers_upto 10)            by verification
Hence set_lcm (IMAGE (\p. p ** ppidx 6) (prime_divisors 6))  divides set_lcm (prime_powers_upto 10)
                                                           by set_lcm_is_least_common_multiple
But PAIRWISE_COPRIME (IMAGE (\p. p ** ppidx 6) (prime_divisors 6)),
Thus set_lcm (IMAGE (\p. p ** ppidx 6) (prime_divisors 6))
   = PROD_SET (IMAGE (\p. p ** ppidx 6) (prime_divisors 6))    by pairwise_coprime_prod_set_eq_set_lcm
   = 6                                                         by above
Hence x divides set_lcm (prime_powers_upto 10)

## maybe:
   ppidx x <= LOG p x       by prime_power_index_le_log_index
   LOG p x <= LOG p n       by LOG_LE_MONO
*)

(* Theorem: 0 < x /\ x <= n ==> x divides set_lcm (prime_powers_upto n) *)
(* Proof:
   Note 0 < n                  by 0 < x /\ x <= n
   Let m = set_lcm (prime_powers_upto n).
   The goal becomes: x divides m.

   Let s = prime_power_divisors x.
   Then x = PROD_SET s         by prime_factorisation, 0 < x

   Claim: !z. z IN s ==> z divides m
   Proof: By prime_power_divisors_element, this is to show:
             prime p /\ p divides x ==> p ** ppidx x divides m
          Note p <= x                     by DIVIDES_LE, 0 < x
          Thus p <= n                     by p <= x, x <= n
           ==> p ** LOG p n IN prime_powers_upto n   by prime_powers_upto_element_alt, b <= n
           ==> p ** LOG p n divides m     by prime_powers_upto_lcm_prime_to_log_divisor
          Note 1 < p                      by ONE_LT_PRIME
           and ppidx x <= LOG p x         by prime_power_index_le_log_index, 0 < n
          also LOG p x <= LOG p n         by LOG_LE_MONO, 1 < p
           ==> ppidx x <= LOG p n         by arithmetic
           ==> p ** ppidx x divides p ** LOG p n   by power_divides_iff, 1 < p
          Thus p ** ppidx x divides m     by DIVIDES_TRANS

   Note FINITE s                by prime_power_divisors_finite
    and set_lcm s divides m     by set_lcm_is_least_common_multiple, FINITE s
   Also PAIRWISE_COPRIME s      by prime_power_divisors_pairwise_coprime
    ==> PROD_SET s = set_lcm s  by pairwise_coprime_prod_set_eq_set_lcm
   Thus x divides m             by set_lcm s divides m
*)
val prime_powers_upto_lcm_divisor = store_thm(
  "prime_powers_upto_lcm_divisor",
  ``!n x. 0 < x /\ x <=  n ==> x divides set_lcm (prime_powers_upto n)``,
  rpt strip_tac >>
  `0 < n` by decide_tac >>
  qabbrev_tac `m = set_lcm (prime_powers_upto n)` >>
  qabbrev_tac `s = prime_power_divisors x` >>
  `x = PROD_SET s` by rw[prime_factorisation, Abbr`s`] >>
  `!z. z IN s ==> z divides m` by
  (rw[prime_power_divisors_element, Abbr`s`] >>
  `p <= x` by rw[DIVIDES_LE] >>
  `p <= n` by decide_tac >>
  `p ** LOG p n IN prime_powers_upto n` by rw[prime_powers_upto_element_alt] >>
  `p ** LOG p n divides m` by rw[prime_powers_upto_lcm_prime_to_log_divisor, Abbr`m`] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `ppidx x <= LOG p x` by rw[prime_power_index_le_log_index] >>
  `LOG p x <= LOG p n` by rw[LOG_LE_MONO] >>
  `ppidx x <= LOG p n` by decide_tac >>
  `p ** ppidx x divides p ** LOG p n` by rw[power_divides_iff] >>
  metis_tac[DIVIDES_TRANS]) >>
  `FINITE s` by rw[prime_power_divisors_finite, Abbr`s`] >>
  `set_lcm s divides m` by rw[set_lcm_is_least_common_multiple] >>
  metis_tac[prime_power_divisors_pairwise_coprime, pairwise_coprime_prod_set_eq_set_lcm]);

(* This is a key result. *)

(* ------------------------------------------------------------------------- *)
(* Consecutive LCM and Prime-related Sets                                    *)
(* ------------------------------------------------------------------------- *)

(*
Useful:
list_lcm_is_common_multiple  |- !x l. MEM x l ==> x divides list_lcm l
list_lcm_prime_factor        |- !p l. prime p /\ p divides list_lcm l ==> p divides PROD_SET (set l)
list_lcm_prime_factor_member |- !p l. prime p /\ p divides list_lcm l ==> ?x. MEM x l /\ p divides x
prime_power_index_pos        |- !n p. 0 < n /\ prime p /\ p divides n ==> 0 < ppidx n
*)

(* Theorem: lcm_run n = set_lcm (prime_powers_upto n) *)
(* Proof:
   By DIVIDES_ANTISYM, this is to show:
   (1) lcm_run n divides set_lcm (prime_powers_upto n)
       Let m = set_lcm (prime_powers_upto n)
       Note !x. MEM x [1 .. n] <=> 0 < x /\ x <= n   by listRangeINC_MEM
        and !x. 0 < x /\ x <= n ==> x divides m      by prime_powers_upto_lcm_divisor
       Thus lcm_run n divides m                      by list_lcm_is_least_common_multiple
   (2) set_lcm (prime_powers_upto n) divides lcm_run n
       Let s = prime_powers_upto n, m = lcm_run n
       Claim: !z. z IN s ==> z divides m
       Proof: Note ?p. (z = p ** LOG p n) /\
                       prime p /\ p <= n             by prime_powers_upto_element
               Now 0 < p                             by PRIME_POS
                so MEM p [1 .. n]                    by listRangeINC_MEM
               ==> MEM z [1 .. n]                    by self_to_log_index_member
              Thus z divides m                       by list_lcm_is_common_multiple

       Note FINITE s                   by prime_powers_upto_finite
       Thus set_lcm s divides m        by set_lcm_is_least_common_multiple, Claim
*)
val lcm_run_eq_set_lcm_prime_powers = store_thm(
  "lcm_run_eq_set_lcm_prime_powers",
  ``!n. lcm_run n = set_lcm (prime_powers_upto n)``,
  rpt strip_tac >>
  (irule DIVIDES_ANTISYM >> rpt conj_tac) >| [
    `!x. MEM x [1 .. n] <=> 0 < x /\ x <= n` by rw[listRangeINC_MEM] >>
    `!x. 0 < x /\ x <= n ==> x divides set_lcm (prime_powers_upto n)` by rw[prime_powers_upto_lcm_divisor] >>
    rw[list_lcm_is_least_common_multiple],
    qabbrev_tac `s = prime_powers_upto n` >>
    qabbrev_tac `m = lcm_run n` >>
    `!z. z IN s ==> z divides m` by
  (rw[prime_powers_upto_element, Abbr`s`] >>
    `0 < p` by rw[PRIME_POS] >>
    `MEM p [1 .. n]` by rw[listRangeINC_MEM] >>
    `MEM (p ** LOG p n) [1 .. n]` by rw[self_to_log_index_member] >>
    rw[list_lcm_is_common_multiple, Abbr`m`]) >>
    `FINITE s` by rw[prime_powers_upto_finite, Abbr`s`] >>
    rw[set_lcm_is_least_common_multiple]
  ]);

(* Theorem: set_lcm (prime_powers_upto n) = PROD_SET (prime_powers_upto n) *)
(* Proof:
   Let s = prime_powers_upto n.
   Note FINITE s                  by prime_powers_upto_finite
    and PAIRWISE_COPRIME s        by prime_powers_upto_pairwise_coprime
   Thus set_lcm s = PROD_SET s    by pairwise_coprime_prod_set_eq_set_lcm
*)
val set_lcm_prime_powers_upto_eqn = store_thm(
  "set_lcm_prime_powers_upto_eqn",
  ``!n. set_lcm (prime_powers_upto n) = PROD_SET (prime_powers_upto n)``,
  metis_tac[prime_powers_upto_finite, prime_powers_upto_pairwise_coprime, pairwise_coprime_prod_set_eq_set_lcm]);

(* Theorem: lcm_run n = PROD_SET (prime_powers_upto n) *)
(* Proof:
     lcm_run n
   = set_lcm (prime_powers_upto n)
   = PROD_SET (prime_powers_upto n)
*)
val lcm_run_eq_prod_set_prime_powers = store_thm(
  "lcm_run_eq_prod_set_prime_powers",
  ``!n. lcm_run n = PROD_SET (prime_powers_upto n)``,
  rw[lcm_run_eq_set_lcm_prime_powers, set_lcm_prime_powers_upto_eqn]);

(* Theorem: PROD_SET (prime_powers_upto n) <= n ** (primes_count n) *)
(* Proof:
   Let s = (primes_upto n), f = \p. p ** LOG p n, t = prime_powers_upto n.
   Then IMAGE f s = t              by prime_powers_upto_def
    and FINITE s                   by primes_upto_finite
    and FINITE t                   by IMAGE_FINITE

   Claim: !x. x IN t ==> x <= n
   Proof: Note x IN t ==>
               ?p. (x = p ** LOG p n) /\ prime p /\ p <= n   by prime_powers_upto_element
           Now 1 < p               by ONE_LT_PRIME
            so 0 < n               by 1 < p, p <= n
           and p ** LOG p n <= n   by LOG
            or x <= n

   Thus PROD_SET t <= n ** CARD t  by PROD_SET_LE_CONSTANT, Claim

   Claim: INJ f s t
   Proof: By prime_powers_upto_element_alt, primes_upto_element, INJ_DEF,
          This is to show: prime p /\ prime p' /\ p ** LOG p n = p' ** LOG p' n ==> p = p'
          Note 1 < p               by ONE_LT_PRIME
            so 0 < n               by 1 < p, p <= n
           and LOG p n <> 0        by LOG_EQ_0, p <= n
            or 0 < LOG p n         by NOT_ZERO_LT_ZERO
           ==> p = p'              by prime_powers_eq

   Thus CARD (IMAGE f s) = CARD s  by INJ_CARD_IMAGE, Claim
     or PROD_SET t <= n ** CARD s  by above
*)

Theorem prime_powers_upto_prod_set_le:
  !n. PROD_SET (prime_powers_upto n) <= n ** (primes_count n)
Proof
  rpt strip_tac >>
  qabbrev_tac ‘s = (primes_upto n)’ >>
  qabbrev_tac ‘f = \p. p ** LOG p n’ >>
  qabbrev_tac ‘t = prime_powers_upto n’ >>
  ‘IMAGE f s = t’ by simp[prime_powers_upto_def, Abbr‘f’, Abbr‘s’, Abbr‘t’] >>
  ‘FINITE s’ by rw[primes_upto_finite, Abbr‘s’] >>
  ‘FINITE t’ by metis_tac[IMAGE_FINITE] >>
  ‘!x. x IN t ==> x <= n’
    by (rw[prime_powers_upto_element, Abbr‘t’, Abbr‘f’] >>
        ‘1 < p’ by rw[ONE_LT_PRIME] >>
        rw[LOG]) >>
  ‘PROD_SET t <= n ** CARD t’ by rw[PROD_SET_LE_CONSTANT] >>
  ‘INJ f s t’
    by (rw[prime_powers_upto_element_alt, primes_upto_element, INJ_DEF, Abbr‘f’,
           Abbr‘s’, Abbr‘t’] >>
        ‘1 < p’ by rw[ONE_LT_PRIME] >>
        ‘0 < n’ by decide_tac >>
        ‘LOG p n <> 0’ by rw[LOG_EQ_0] >>
        metis_tac[prime_powers_eq, NOT_ZERO_LT_ZERO]) >>
  metis_tac[INJ_CARD_IMAGE]
QED

(* Theorem: lcm_run n <= n ** (primes_count n) *)
(* Proof:
      lcm_run n
    = PROD_SET (prime_powers_upto n)   by lcm_run_eq_prod_set_prime_powers
   <= n ** (primes_count n)            by prime_powers_upto_prod_set_le
*)
val lcm_run_upper_by_primes_count = store_thm(
  "lcm_run_upper_by_primes_count",
  ``!n. lcm_run n <= n ** (primes_count n)``,
  rw[lcm_run_eq_prod_set_prime_powers, prime_powers_upto_prod_set_le]);

(* This is a significant result. *)

(* Theorem: PROD_SET (primes_upto n) <= PROD_SET (prime_powers_upto n) *)
(* Proof:
   Let s = primes_upto n, f = \p. p ** LOG p n, t = prime_powers_upto n.
   The goal becomes: PROD_SET s <= PROD_SET t
   Note IMAGE f s = t           by prime_powers_upto_def
    and FINITE s                by primes_upto_finite

   Claim: INJ f s univ(:num)
   Proof: By primes_upto_element, INJ_DEF,
          This is to show: prime p /\ prime p' /\ p ** LOG p n = p' ** LOG p' n ==> p = p'
          Note 1 < p            by ONE_LT_PRIME
            so 0 < n            by 1 < p, p <= n
          Thus LOG p n <> 0     by LOG_EQ_0, p <= n
            or 0 < LOG p n      by NOT_ZERO_LT_ZERO
           ==> p = p'           by prime_powers_eq

   Also INJ I s univ(:num)      by primes_upto_element, INJ_DEF
    and IMAGE I s = s           by IMAGE_I

   Claim: !x. x IN s ==> I x <= f x
   Proof: By primes_upto_element,
          This is to show: prime x /\ x <= n ==> x <= x ** LOG x n
          Note 1 < x            by ONE_LT_PRIME
            so 0 < n            by 1 < x, x <= n
          Thus LOG x n <> 0     by LOG_EQ_0
            or 1 <= LOG x n     by LOG x n <> 0
           ==> x ** 1 <= x ** LOG x n   by EXP_BASE_LE_MONO
            or      x <= x ** LOG x n   by EXP_1

   Hence PROD_SET s <= PROD_SET t       by PROD_SET_LESS_EQ
*)
val prime_powers_upto_prod_set_ge = store_thm(
  "prime_powers_upto_prod_set_ge",
  ``!n. PROD_SET (primes_upto n) <= PROD_SET (prime_powers_upto n)``,
  rpt strip_tac >>
  qabbrev_tac `s = primes_upto n` >>
  qabbrev_tac `f = \p. p ** LOG p n` >>
  qabbrev_tac `t = prime_powers_upto n` >>
  `IMAGE f s = t` by rw[prime_powers_upto_def, Abbr`f`, Abbr`s`, Abbr`t`] >>
  `FINITE s` by rw[primes_upto_finite, Abbr`s`] >>
  `INJ f s univ(:num)` by
  (rw[primes_upto_element, INJ_DEF, Abbr`f`, Abbr`s`] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `LOG p n <> 0` by rw[LOG_EQ_0] >>
  metis_tac[prime_powers_eq, NOT_ZERO_LT_ZERO]) >>
  `INJ I s univ(:num)` by rw[primes_upto_element, INJ_DEF, Abbr`s`] >>
  `IMAGE I s = s` by rw[] >>
  `!x. x IN s ==> I x <= f x` by
    (rw[primes_upto_element, Abbr`f`, Abbr`s`] >>
  `1 < x` by rw[ONE_LT_PRIME] >>
  `LOG x n <> 0` by rw[LOG_EQ_0] >>
  `1 <= LOG x n` by decide_tac >>
  metis_tac[EXP_BASE_LE_MONO, EXP_1]) >>
  metis_tac[PROD_SET_LESS_EQ]);

(* Theorem: PROD_SET (primes_upto n) <= lcm_run n *)
(* Proof:
      lcm_run n
    = set_lcm (prime_powers_upto n)    by lcm_run_eq_set_lcm_prime_powers
    = PROD_SET (prime_powers_upto n)   by set_lcm_prime_powers_upto_eqn
   >= PROD_SET (primes_upto n)         by prime_powers_upto_prod_set_ge
*)
val lcm_run_lower_by_primes_product = store_thm(
  "lcm_run_lower_by_primes_product",
  ``!n. PROD_SET (primes_upto n) <= lcm_run n``,
  rpt strip_tac >>
  `lcm_run n = set_lcm (prime_powers_upto n)` by rw[lcm_run_eq_set_lcm_prime_powers] >>
  `_ = PROD_SET (prime_powers_upto n)` by rw[set_lcm_prime_powers_upto_eqn] >>
  rw[prime_powers_upto_prod_set_ge]);

(* This is another significant result. *)

(* These are essentially Chebyshev functions. *)

(* Theorem: n ** primes_count n <= PROD_SET (primes_upto n) * (PROD_SET (prime_powers_upto n)) *)
(* Proof:
   Let s = (primes_upto n), f = \p. p ** LOG p n, t = prime_powers_upto n.
   The goal becomes: n ** CARD s <= PROD_SET s * PROD_SET t

   Note IMAGE f s = t                 by prime_powers_upto_def
    and FINITE s                      by primes_upto_finite
    and FINITE t                      by IMAGE_FINITE

   Claim: !p. p IN s ==> n <= I p * f p
   Proof: By primes_upto_element,
          This is to show: prime p /\ p <= n ==> n < p * p ** LOG p n
          Note 1 < p                  by ONE_LT_PRIME
            so 0 < n                  by 1 < p, p <= n
           ==> n < p ** (SUC (LOG p n))   by LOG
                 = p * p ** (LOG p n)     by EXP
            or n <= p * p ** (LOG p n)    by LESS_IMP_LESS_OR_EQ

   Note INJ I s univ(:num)            by primes_upto_element, INJ_DEF,
    and IMAGE I s = s                 by IMAGE_I

   Claim: INJ f s univ(:num)
   Proof: By primes_upto_element, INJ_DEF,
          This is to show: prime p /\ prime p' /\ p ** LOG p n = p' ** LOG p' n ==> p = p'
          Note 1 < p                  by ONE_LT_PRIME
            so 0 < n                  by 1 < p, p <= n
           ==> LOG p n <> 0           by LOG_EQ_0
            or 0 < LOG p n            by NOT_ZERO_LT_ZERO
          Thus p = p'                 by prime_powers_eq

   Therefore,
          n ** CARD s <= PROD_SET (IMAGE I s) * PROD_SET (IMAGE f s)
                                                     by PROD_SET_PRODUCT_GE_CONSTANT
      or  n ** CARD s <= PROD_SET s * PROD_SET t     by above
*)

Theorem prime_powers_upto_prod_set_mix_ge:
  !n. n ** primes_count n <=
        PROD_SET (primes_upto n) * (PROD_SET (prime_powers_upto n))
Proof
  rpt strip_tac >>
  qabbrev_tac ‘s = (primes_upto n)’ >>
  qabbrev_tac ‘f = \p. p ** LOG p n’ >>
  qabbrev_tac ‘t = prime_powers_upto n’ >>
  ‘IMAGE f s = t’ by rw[prime_powers_upto_def, Abbr‘f’, Abbr‘s’, Abbr‘t’] >>
  ‘FINITE s’ by rw[primes_upto_finite, Abbr‘s’] >>
  ‘FINITE t’ by rw[] >>
  ‘!p. p IN s ==> n <= I p * f p’ by
  (rw[primes_upto_element, Abbr‘s’, Abbr‘f’] >>
  ‘1 < p’ by rw[ONE_LT_PRIME] >>
  rw[LOG, GSYM EXP, LESS_IMP_LESS_OR_EQ]) >>
  ‘INJ I s univ(:num)’ by rw[primes_upto_element, INJ_DEF, Abbr‘s’] >>
  ‘IMAGE I s = s’ by rw[] >>
  ‘INJ f s univ(:num)’ by
    (rw[primes_upto_element, INJ_DEF, Abbr‘f’, Abbr‘s’] >>
  ‘1 < p’ by rw[ONE_LT_PRIME] >>
  ‘LOG p n <> 0’ by rw[LOG_EQ_0] >>
  metis_tac[prime_powers_eq, NOT_ZERO_LT_ZERO]) >>
  metis_tac[PROD_SET_PRODUCT_GE_CONSTANT]
QED

(* Another significant result. *)

(* Theorem: n ** primes_count n <= PROD_SET (primes_upto n) * lcm_run n *)
(* Proof:
      n ** primes_count n
   <= PROD_SET (primes_upto n) * (PROD_SET (prime_powers_upto n))  by prime_powers_upto_prod_set_mix_ge
    = PROD_SET (primes_upto n) * lcm_run n                         by lcm_run_eq_prod_set_prime_powers
*)
val primes_count_upper_by_product = store_thm(
  "primes_count_upper_by_product",
  ``!n. n ** primes_count n <= PROD_SET (primes_upto n) * lcm_run n``,
  metis_tac[prime_powers_upto_prod_set_mix_ge, lcm_run_eq_prod_set_prime_powers]);

(* Theorem: n ** primes_count n <= (lcm_run n) ** 2 *)
(* Proof:
      n ** primes_count n
   <= PROD_SET (primes_upto n) * lcm_run n     by primes_count_upper_by_product
   <= lcm_run n * lcm_run n                    by lcm_run_lower_by_primes_product
    = (lcm_run n) ** 2                         by EXP_2
*)
val primes_count_upper_by_lcm_run = store_thm(
  "primes_count_upper_by_lcm_run",
  ``!n. n ** primes_count n <= (lcm_run n) ** 2``,
  rpt strip_tac >>
  `n ** primes_count n <= PROD_SET (primes_upto n) * lcm_run n` by rw[primes_count_upper_by_product] >>
  `PROD_SET (primes_upto n) <= lcm_run n` by rw[lcm_run_lower_by_primes_product] >>
  metis_tac[LESS_MONO_MULT, LESS_EQ_TRANS, EXP_2]);

(* Theorem: SQRT (n ** (primes_count n)) <= lcm_run n *)
(* Proof:
   Note          n ** primes_count n <= (lcm_run n) ** 2         by primes_count_upper_by_lcm_run
    ==>   SQRT (n ** primes_count n) <= SQRT ((lcm_run n) ** 2)  by ROOT_LE_MONO, 0 < 2
    But   SQRT ((lcm_run n) ** 2) = lcm_run n                    by ROOT_UNIQUE
   Thus SQRT (n ** (primes_count n)) <= lcm_run n
*)
val lcm_run_lower_by_primes_count = store_thm(
  "lcm_run_lower_by_primes_count",
  ``!n. SQRT (n ** (primes_count n)) <= lcm_run n``,
  rpt strip_tac >>
  `n ** primes_count n <= (lcm_run n) ** 2` by rw[primes_count_upper_by_lcm_run] >>
  `SQRT (n ** primes_count n) <= SQRT ((lcm_run n) ** 2)` by rw[ROOT_LE_MONO] >>
  `SQRT ((lcm_run n) ** 2) = lcm_run n` by rw[ROOT_UNIQUE] >>
  decide_tac);

(* Therefore:
   L(n) <= n ** pi(n)            by lcm_run_upper_by_primes_count
   PI(n) <= L(n)                 by lcm_run_lower_by_primes_product
   n ** pi(n) <= PI(n) * L(n)    by primes_count_upper_by_product

   giving:               L(n) <= n ** pi(n) <= L(n) ** 2      by primes_count_upper_by_lcm_run
      and:  SQRT (n ** pi(n)) <=       L(n) <= (n ** pi(n))   by lcm_run_lower_by_primes_count
*)

(* ------------------------------------------------------------------------- *)
(* Primality Tests Documentation                                             *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(*

   Two Factors Properties:
   two_factors_property_1  |- !n a b. (n = a * b) /\ a < SQRT n ==> SQRT n <= b
   two_factors_property_2  |- !n a b. (n = a * b) /\ SQRT n < a ==> b <= SQRT n
   two_factors_property    |- !n a b. (n = a * b) ==> a <= SQRT n \/ b <= SQRT n

   Primality or Compositeness based on SQRT:
   prime_by_sqrt_factors  |- !p. prime p <=>
                                 1 < p /\ !q. 1 < q /\ q <= SQRT p ==> ~(q divides p)
   prime_factor_estimate  |- !n. 1 < n ==>
                                 (~prime n <=> ?p. prime p /\ p divides n /\ p <= SQRT n)

   Primality Testing Algorithm:
   factor_seek_def     |- !q n c. factor_seek n c q =
                                  if c <= q then n
                                  else if 1 < q /\ (n MOD q = 0) then q
                                  else factor_seek n c (q + 1)
   prime_test_def      |- !n. prime_test n <=>
                              if n <= 1 then F else factor_seek n (1 + SQRT n) 2 = n
   factor_seek_bound   |- !n c q. 0 < n ==> factor_seek n c q <= n
   factor_seek_thm     |- !n c q. 1 < q /\ q <= c /\ c <= n ==>
                          (factor_seek n c q = n <=> !p. q <= p /\ p < c ==> ~(p divides n))
   prime_test_thm      |- !n. prime n <=> prime_test n

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Two Factors Properties                                                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (n = a * b) /\ a < SQRT n ==> SQRT n <= b *)
(* Proof:
   If n = 0, then a = 0 or b = 0          by MULT_EQ_0
   But SQRT 0 = 0                         by SQRT_0
   so a <> 0, making b = 0, and SQRT n <= b true.
   If n <> 0, a <> 0 and b <> 0           by MULT_EQ_0
   By contradiction, suppose b < SQRT n.
   Then  n = a * b < a * SQRT n           by LT_MULT_LCANCEL, 0 < a.
    and a * SQRT n < SQRT n * SQRT n      by LT_MULT_RCANCEL, 0 < SQRT n.
   making  n < (SQRT n) ** 2              by LESS_TRANS, EXP_2
   This contradicts (SQRT n) ** 2 <= n    by SQRT_PROPERTY
*)
val two_factors_property_1 = store_thm(
  "two_factors_property_1",
  ``!n a b. (n = a * b) /\ a < SQRT n ==> SQRT n <= b``,
  rpt strip_tac >>
  Cases_on `n = 0` >| [
    `a <> 0 /\ (b = 0) /\ (SQRT n = 0)` by metis_tac[MULT_EQ_0, SQRT_0, DECIDE``~(0 < 0)``] >>
    decide_tac,
    `a <> 0 /\ b <> 0` by metis_tac[MULT_EQ_0] >>
    spose_not_then strip_assume_tac >>
    `b < SQRT n` by decide_tac >>
    `0 < a /\ 0 < b /\ 0 < SQRT n` by decide_tac >>
    `n < a * SQRT n` by rw[] >>
    `a * SQRT n < SQRT n * SQRT n` by rw[] >>
    `n < (SQRT n) ** 2` by metis_tac[LESS_TRANS, EXP_2] >>
    `(SQRT n) ** 2 <= n` by rw[SQRT_PROPERTY] >>
    decide_tac
  ]);

(* Theorem: (n = a * b) /\ SQRT n < a ==> b <= SQRT n *)
(* Proof:
   If n = 0, then a = 0 or b = 0             by MULT_EQ_0
   But SQRT 0 = 0                            by SQRT_0
   so a <> 0, making b = 0, and b <= SQRT n true.
   If n <> 0, a <> 0 and b <> 0              by MULT_EQ_0
   By contradiction, suppose SQRT n < b.
   Then SUC (SQRT n) ** 2
      = SUC (SQRT n) * SUC (SQRT n)          by EXP_2
      <= a * SUC (SQRT n)                    by LT_MULT_RCANCEL, 0 < SUC (SQRT n).
      <= a * b = n                           by LT_MULT_LCANCEL, 0 < a.
   Giving (SUC (SQRT n)) ** 2 <= n           by LESS_EQ_TRANS
   or SQRT ((SUC (SQRT n)) ** 2) <= SQRT n   by SQRT_LE
   or       SUC (SQRT n) <= SQRT n           by SQRT_OF_SQ
   which is a contradiction to !m. SUC m > m by LESS_SUC_REFL
 *)
val two_factors_property_2 = store_thm(
  "two_factors_property_2",
  ``!n a b. (n = a * b) /\ SQRT n < a ==> b <= SQRT n``,
  rpt strip_tac >>
  Cases_on `n = 0` >| [
    `a <> 0 /\ (b = 0) /\ (SQRT 0 = 0)` by metis_tac[MULT_EQ_0, SQRT_0, DECIDE``~(0 < 0)``] >>
    decide_tac,
    `a <> 0 /\ b <> 0` by metis_tac[MULT_EQ_0] >>
    spose_not_then strip_assume_tac >>
    `SQRT n < b` by decide_tac >>
    `SUC (SQRT n) <= a /\ SUC (SQRT n) <= b` by decide_tac >>
    `SUC (SQRT n) * SUC (SQRT n) <= a * SUC (SQRT n)` by rw[] >>
    `a * SUC (SQRT n) <= n` by rw[] >>
    `SUC (SQRT n) ** 2  <= n` by metis_tac[LESS_EQ_TRANS, EXP_2] >>
    `SUC (SQRT n) <= SQRT n` by metis_tac[SQRT_LE, SQRT_OF_SQ] >>
    decide_tac
  ]);

(* Theorem: (n = a * b) ==> a <= SQRT n \/ b <= SQRT n *)
(* Proof:
   By contradiction, suppose SQRT n < a /\ SQRT n < b.
   Then (n = a * b) /\ SQRT n < a ==> b <= SQRT n  by two_factors_property_2
   which contradicts SQRT n < b.
 *)
val two_factors_property = store_thm(
  "two_factors_property",
  ``!n a b. (n = a * b) ==> a <= SQRT n \/ b <= SQRT n``,
  rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  `SQRT n < a` by decide_tac >>
  metis_tac[two_factors_property_2]);

(* ------------------------------------------------------------------------- *)
(* Primality or Compositeness based on SQRT                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: prime p <=> 1 < p /\ !q. 1 < q /\ q <= SQRT p ==> ~(q divides p) *)
(* Proof:
   If part: prime p ==> 1 < p /\ !q. 1 < q /\ q <= SQRT p ==> ~(q divides p)
     First one: prime p ==> 1 < p  is true    by ONE_LT_PRIME
     Second one: by contradiction, suppose q divides p.
     But prime p /\ q divides p ==> (q = p) or (q = 1)  by prime_def
     Given 1 < q, q <> 1, hence q = p.
     This means p <= SQRT p, giving p = 0 or p = 1      by SQRT_GE_SELF
     which contradicts p <> 0 and p <> 1                by PRIME_POS, prime_def
   Only-if part: 1 < p /\ !q. 1 < q /\ q <= SQRT p ==> ~(q divides p) ==> prime p
     By prime_def, this is to show:
     (1) p <> 1, true since 1 < p.
     (2) b divides p ==> (b = p) \/ (b = 1)
         By contradiction, suppose b <> p /\ b <> 1.
         b divides p ==> ?a. p = a * b     by divides_def
         which means a <= SQRT p \/ b <= SQRT p   by two_factors_property
         If a <= SQRT p,
         1 < p ==> p <> 0, so a <> 0  by MULT
         also b <> p ==> a <> 1       by MULT_LEFT_1
         so 1 < a, and a divides p    by prime_def, MULT_COMM
         The implication gives ~(a divides p), a contradiction.
         If b <= SQRT p,
         1 < p ==> p <> 0, so b <> 0  by MULT_0
         also b <> 1, so 1 < b, and b divides p.
         The implication gives ~(b divides p), a contradiction.
 *)
val prime_by_sqrt_factors = store_thm(
  "prime_by_sqrt_factors",
  ``!p. prime p <=> 1 < p /\ !q. 1 < q /\ q <= SQRT p ==> ~(q divides p)``,
  rw[EQ_IMP_THM] >-
  rw[ONE_LT_PRIME] >-
 (spose_not_then strip_assume_tac >>
  `0 < p` by rw[PRIME_POS] >>
  `p <> 0 /\ q <> 1` by decide_tac >>
  `(q = p) /\ p <> 1` by metis_tac[prime_def] >>
  metis_tac[SQRT_GE_SELF]) >>
  rw[prime_def] >>
  spose_not_then strip_assume_tac >>
  `?a. p = a * b` by rw[GSYM divides_def] >>
  `a <= SQRT p \/ b <= SQRT p` by rw[two_factors_property] >| [
    `a <> 1` by metis_tac[MULT_LEFT_1] >>
    `p <> 0` by decide_tac >>
    `a <> 0` by metis_tac[MULT] >>
    `1 < a` by decide_tac >>
    metis_tac[divides_def, MULT_COMM],
    `p <> 0` by decide_tac >>
    `b <> 0` by metis_tac[MULT_0] >>
    `1 < b` by decide_tac >>
    metis_tac[]
  ]);

(* Theorem: 1 < n ==> (~prime n <=> ?p. prime p /\ p divides n /\ p <= SQRT n) *)
(* Proof:
   If part ~prime n ==> ?p. prime p /\ p divides n /\ p <= SQRT n
   Given n <> 1, ?p. prime p /\ p divides n  by PRIME_FACTOR
   If p <= SQRT n, take this p.
   If ~(p <= SQRT n), SQRT n < p.
      Since p divides n, ?q. n = p * q       by divides_def, MULT_COMM
      Hence q <= SQRT n                      by two_factors_property_2
      Since prime p but ~prime n, q <> 1     by MULT_RIGHT_1
         so ?t. prime t /\ t divides q       by PRIME_FACTOR
      Since 1 < n, n <> 0, so q <> 0         by MULT_0
         so t divides q ==> t <= q           by DIVIDES_LE, 0 < q.
      Take t, then t divides n               by DIVIDES_TRANS
               and t <= SQRT n               by LESS_EQ_TRANS
    Only-if part: ?p. prime p /\ p divides n /\ p <= SQRT n ==> ~prime n
      By contradiction, assume prime n.
      Then p divides n ==> p = 1 or p = n    by prime_def
      But prime p ==> p <> 1, so p = n       by ONE_LT_PRIME
      Giving p <= SQRT p,
      thus forcing p = 0 or p = 1            by SQRT_GE_SELF
      Both are impossible for prime p.
*)
val prime_factor_estimate = store_thm(
  "prime_factor_estimate",
  ``!n. 1 < n ==> (~prime n <=> ?p. prime p /\ p divides n /\ p <= SQRT n)``,
  rpt strip_tac >>
  `n <> 1` by decide_tac >>
  rw[EQ_IMP_THM] >| [
    `?p. prime p /\ p divides n` by rw[PRIME_FACTOR] >>
    Cases_on `p <= SQRT n` >-
    metis_tac[] >>
    `SQRT n < p` by decide_tac >>
    `?q. n = q * p` by rw[GSYM divides_def] >>
    `_ = p * q` by rw[MULT_COMM] >>
    `q <= SQRT n` by metis_tac[two_factors_property_2] >>
    `q <> 1` by metis_tac[MULT_RIGHT_1] >>
    `?t. prime t /\ t divides q` by rw[PRIME_FACTOR] >>
    `n <> 0` by decide_tac >>
    `q <> 0` by metis_tac[MULT_0] >>
    `0 < q ` by decide_tac >>
    `t <= q` by rw[DIVIDES_LE] >>
    `q divides n` by metis_tac[divides_def] >>
    metis_tac[DIVIDES_TRANS, LESS_EQ_TRANS],
    spose_not_then strip_assume_tac >>
    `1 < p` by rw[ONE_LT_PRIME] >>
    `p <> 1 /\ p <> 0` by decide_tac >>
    `p = n` by metis_tac[prime_def] >>
    metis_tac[SQRT_GE_SELF]
  ]);

(* ------------------------------------------------------------------------- *)
(* Primality Testing Algorithm                                               *)
(* ------------------------------------------------------------------------- *)

(* Seek the prime factor of number n, starting with q, up to cutoff c. *)
Definition factor_seek_def:
  factor_seek n c q =
    if c <= q then n
    else if 1 < q /\ (n MOD q = 0) then q
    else factor_seek n c (q + 1)
Termination
  WF_REL_TAC ‘measure (λ(n,c,q). c - q)’ >> simp[]
End
(* Use 1 < q so that, for prime n, it gives a result n for any initial q, including q = 1. *)

(* Primality test by seeking a factor exceeding (SQRT n). *)
val prime_test_def = Define`
    prime_test n =
       if n <= 1 then F
       else factor_seek n (1 + SQRT n) 2 = n
`;

(*
EVAL ``MAP prime_test [1 .. 15]``; = [F; T; T; F; T; F; T; F; F; F; T; F; T; F; F]: thm
*)

(* Theorem: 0 < n ==> factor_seek n c q <= n *)
(* Proof:
   By induction from factor_seek_def.
   If c <= q,
      Then factor_seek n c q = n, hence true    by factor_seek_def
   If q = 0,
      Then factor_seek n c 0 = 0, hence true    by factor_seek_def
   If n MOD q = 0,
      Then factor_seek n c q = q                by factor_seek_def
      Thus q divides n                          by DIVIDES_MOD_0, q <> 0
      hence q <= n                              by DIVIDES_LE, 0 < n
   Otherwise,
         factor_seek n c q
       = factor_seek n c (q + 1)                by factor_seek_def
      <= n                                      by induction hypothesis
*)
val factor_seek_bound = store_thm(
  "factor_seek_bound",
  ``!n c q. 0 < n ==> factor_seek n c q <= n``,
  ho_match_mp_tac (theorem "factor_seek_ind") >>
  rw[] >>
  rw[Once factor_seek_def] >>
  `q divides n` by rw[DIVIDES_MOD_0] >>
  rw[DIVIDES_LE]);

(* Theorem: 1 < q /\ q <= c /\ c <= n ==>
   ((factor_seek n c q = n) <=> (!p. q <= p /\ p < c ==> ~(p divides n))) *)
(* Proof:
   By induction from factor_seek_def, this is to show:
   (1) n MOD q = 0 ==> ?p. (q <= p /\ p < c) /\ p divides n
       Take p = q, then n MOD q = 0 ==> q divides n       by DIVIDES_MOD_0, 0 < q
   (2) n MOD q <> 0 ==> factor_seek n c (q + 1) = n <=>
                        !p. q <= p /\ p < c ==> ~(p divides n)
            factor_seek n c (q + 1) = n
        <=> !p. q + 1 <= p /\ p < c ==> ~(p divides n))   by induction hypothesis
         or !p.      q < p /\ p < c ==> ~(p divides n))
        But n MOD q <> 0 gives ~(q divides n)             by DIVIDES_MOD_0, 0 < q
       Thus !p.     q <= p /\ p < c ==> ~(p divides n))
*)
val factor_seek_thm = store_thm(
  "factor_seek_thm",
  ``!n c q. 1 < q /\ q <= c /\ c <= n ==>
   ((factor_seek n c q = n) <=> (!p. q <= p /\ p < c ==> ~(p divides n)))``,
  ho_match_mp_tac (theorem "factor_seek_ind") >>
  rw[] >>
  rw[Once factor_seek_def] >| [
    qexists_tac `q` >>
    rw[DIVIDES_MOD_0],
    rw[EQ_IMP_THM] >>
    spose_not_then strip_assume_tac >>
    `0 < q` by decide_tac >>
    `p <> q` by metis_tac[DIVIDES_MOD_0] >>
    `q + 1 <= p` by decide_tac >>
    metis_tac[]
  ]);

(* Theorem: prime n = prime_test n *)
(* Proof:
       prime n
   <=> 1 < n /\ !q. 1 < q /\ n <= SQRT n ==> ~(n divides p)     by prime_by_sqrt_factors
   <=> 1 < n /\ !q. 2 <= q /\ n < c ==> ~(n divides p)          where c = 1 + SQRT n
   Under 1 < n,
   Note SQRT n <> 0         by SQRT_EQ_0, n <> 0
     so 1 < 1 + SQRT n = c, or 2 <= c.
   Also SQRT n <= n         by SQRT_LE_SELF
    but SQRT n <> n         by SQRT_EQ_SELF, 1 < n
     so SQRT n < n, or c <= n.
   Thus 1 < n /\ !q. 2 <= q /\ n < c ==> ~(n divides p)
    <=> factor_seek n c q = n                              by factor_seek_thm
    <=> prime_test n                                       by prime_test_def
*)
val prime_test_thm = store_thm(
  "prime_test_thm",
  ``!n. prime n = prime_test n``,
  rw[prime_test_def, prime_by_sqrt_factors] >>
  rw[EQ_IMP_THM] >| [
    qabbrev_tac `c = SQRT n + 1` >>
    `0 < 2` by decide_tac >>
    `SQRT n <> 0` by rw[SQRT_EQ_0] >>
    `2 <= c` by rw[Abbr`c`] >>
    `SQRT n <= n` by rw[SQRT_LE_SELF] >>
    `SQRT n <> n` by rw[SQRT_EQ_SELF] >>
    `c <= n` by rw[Abbr`c`] >>
    `!q. 2 <= q /\ q < c ==> ~(q divides n)` by fs[Abbr`c`] >>
    rw[factor_seek_thm],
    qabbrev_tac `c = SQRT n + 1` >>
    `0 < 2` by decide_tac >>
    `SQRT n <> 0` by rw[SQRT_EQ_0] >>
    `2 <= c` by rw[Abbr`c`] >>
    `SQRT n <= n` by rw[SQRT_LE_SELF] >>
    `SQRT n <> n` by rw[SQRT_EQ_SELF] >>
    `c <= n` by rw[Abbr`c`] >>
    fs[factor_seek_thm] >>
    `!p. 1 < p /\ p <= SQRT n ==> ~(p divides n)` by fs[Abbr`c`] >>
    rw[]
  ]);

(* ------------------------------------------------------------------------- *)
(* Gauss' Little Theorem                                                     *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported, ! in computeLib):

   GCD Equivalence Class:
   gcd_matches_def       |- !n d. gcd_matches n d = {j | j IN natural n /\ (gcd j n = d)}
!  gcd_matches_alt       |- !n d. gcd_matches n d = natural n INTER {j | gcd j n = d}
   gcd_matches_element   |- !n d j. j IN gcd_matches n d <=> 0 < j /\ j <= n /\ (gcd j n = d)
   gcd_matches_subset    |- !n d. gcd_matches n d SUBSET natural n
   gcd_matches_finite    |- !n d. FINITE (gcd_matches n d)
   gcd_matches_0         |- !d. gcd_matches 0 d = {}
   gcd_matches_with_0    |- !n. gcd_matches n 0 = {}
   gcd_matches_1         |- !d. gcd_matches 1 d = if d = 1 then {1} else {}
   gcd_matches_has_divisor     |- !n d. 0 < n /\ d divides n ==> d IN gcd_matches n d
   gcd_matches_element_divides |- !n d j. j IN gcd_matches n d ==> d divides j /\ d divides n
   gcd_matches_eq_empty        |- !n d. 0 < n ==> ((gcd_matches n d = {}) <=> ~(d divides n))

   Phi Function:
   phi_def           |- !n. phi n = CARD (coprimes n)
   phi_thm           |- !n. phi n = LENGTH (FILTER (\j. coprime j n) (GENLIST SUC n))
   phi_fun           |- phi = CARD o coprimes
   phi_pos           |- !n. 0 < n ==> 0 < phi n
   phi_0             |- phi 0 = 0
   phi_eq_0          |- !n. (phi n = 0) <=> (n = 0)
   phi_1             |- phi 1 = 1
   phi_eq_totient    |- !n. 1 < n ==> (phi n = totient n)
   phi_prime         |- !n. prime n ==> (phi n = n - 1)
   phi_2             |- phi 2 = 1
   phi_gt_1          |- !n. 2 < n ==> 1 < phi n
   phi_le            |- !n. phi n <= n
   phi_lt            |- !n. 1 < n ==> phi n < n

   Divisors:
   divisors_def            |- !n. divisors n = {d | 0 < d /\ d <= n /\ d divides n}
   divisors_element        |- !n d. d IN divisors n <=> 0 < d /\ d <= n /\ d divides n
   divisors_element_alt    |- !n. 0 < n ==> !d. d IN divisors n <=> d divides n
   divisors_has_element    |- !n d. d IN divisors n ==> 0 < n
   divisors_has_1          |- !n. 0 < n ==> 1 IN divisors n
   divisors_has_last       |- !n. 0 < n ==> n IN divisors n
   divisors_not_empty      |- !n. 0 < n ==> divisors n <> {}
   divisors_0              |- divisors 0 = {}
   divisors_1              |- divisors 1 = {1}
   divisors_eq_empty       |- !n. divisors n = {} <=> n = 0
!  divisors_eqn            |- !n. divisors n =
                                  IMAGE (\j. if j + 1 divides n then j + 1 else 1) (count n)
   divisors_has_factor     |- !n p q. 0 < n /\ n = p * q ==> p IN divisors n /\ q IN divisors n
   divisors_has_cofactor   |- !n d. d IN divisors n ==> n DIV d IN divisors n
   divisors_delete_last    |- !n. divisors n DELETE n = {m | 0 < m /\ m < n /\ m divides n}
   divisors_nonzero        |- !n d. d IN divisors n ==> 0 < d
   divisors_subset_natural |- !n. divisors n SUBSET natural n
   divisors_finite         |- !n. FINITE (divisors n)
   divisors_divisors_bij   |- !n. (\d. n DIV d) PERMUTES divisors n

   An upper bound for divisors:
   divisor_le_cofactor_ge  |- !n p. 0 < p /\ p divides n /\ p <= SQRT n ==> SQRT n <= n DIV p
   divisor_gt_cofactor_le  |- !n p. 0 < p /\ p divides n /\ SQRT n < p ==> n DIV p <= SQRT n
   divisors_cofactor_inj   |- !n. INJ (\j. n DIV j) (divisors n) univ(:num)
   divisors_card_upper     |- !n. CARD (divisors n) <= TWICE (SQRT n)

   Gauss' Little Theorem:
   gcd_matches_divisor_element  |- !n d. d divides n ==>
                                   !j. j IN gcd_matches n d ==> j DIV d IN coprimes_by n d
   gcd_matches_bij_coprimes_by  |- !n d. d divides n ==>
                                   BIJ (\j. j DIV d) (gcd_matches n d) (coprimes_by n d)
   gcd_matches_bij_coprimes     |- !n d. 0 < n /\ d divides n ==>
                                   BIJ (\j. j DIV d) (gcd_matches n d) (coprimes (n DIV d))
   divisors_eq_gcd_image        |- !n. divisors n = IMAGE (gcd n) (natural n)
   gcd_eq_equiv_class           |- !n d. feq_class (gcd n) (natural n) d = gcd_matches n d
   gcd_eq_equiv_class_fun       |- !n. feq_class (gcd n) (natural n) = gcd_matches n
   gcd_eq_partition_by_divisors |- !n. partition (feq (gcd n)) (natural n) =
                                       IMAGE (gcd_matches n) (divisors n)
   gcd_eq_equiv_on_natural      |- !n. feq (gcd n) equiv_on natural n
   sum_over_natural_by_gcd_partition
                                |- !f n. SIGMA f (natural n) =
                                         SIGMA (SIGMA f) (partition (feq (gcd n)) (natural n))
   sum_over_natural_by_divisors |- !f n. SIGMA f (natural n) =
                                         SIGMA (SIGMA f) (IMAGE (gcd_matches n) (divisors n))
   gcd_matches_from_divisors_inj         |- !n. INJ (gcd_matches n) (divisors n) univ(:num -> bool)
   gcd_matches_and_coprimes_by_same_size |- !n. CARD o gcd_matches n = CARD o coprimes_by n
   coprimes_by_with_card      |- !n. 0 < n ==> CARD o coprimes_by n =
                                               (\d. phi (if d IN divisors n then n DIV d else 0))
   coprimes_by_divisors_card  |- !n x. x IN divisors n ==>
                                       (CARD o coprimes_by n) x = (\d. phi (n DIV d)) x
   Gauss_little_thm           |- !n. SIGMA phi (divisors n) = n

   Euler phi function is multiplicative for coprimes:
   coprimes_mult_by_image
                       |- !m n. coprime m n ==>
                                coprimes (m * n) =
                                IMAGE (\(x,y). if m * n = 1 then 1 else (x * n + y * m) MOD (m * n))
                                      (coprimes m CROSS coprimes n)
   coprimes_map_cross_inj
                       |- !m n. coprime m n ==>
                                INJ (\(x,y). if m * n = 1 then 1 else (x * n + y * m) MOD (m * n))
                                    (coprimes m CROSS coprimes n) univ(:num)
   phi_mult            |- !m n. coprime m n ==> phi (m * n) = phi m * phi n
   phi_primes_distinct |- !p q. prime p /\ prime q /\ p <> q ==> phi (p * q) = (p - 1) * (q - 1)

   Euler phi function for prime powers:
   multiples_upto_def  |- !m n. m multiples_upto n = {x | m divides x /\ 0 < x /\ x <= n}
   multiples_upto_element
                       |- !m n x. x IN m multiples_upto n <=> m divides x /\ 0 < x /\ x <= n
   multiples_upto_alt  |- !m n. m multiples_upto n = {x | ?k. x = k * m /\ 0 < x /\ x <= n}
   multiples_upto_element_alt
                       |- !m n x. x IN m multiples_upto n <=> ?k. x = k * m /\ 0 < x /\ x <= n
   multiples_upto_eqn  |- !m n. m multiples_upto n = {x | m divides x /\ x IN natural n}
   multiples_upto_0_n  |- !n. 0 multiples_upto n = {}
   multiples_upto_1_n  |- !n. 1 multiples_upto n = natural n
   multiples_upto_m_0  |- !m. m multiples_upto 0 = {}
   multiples_upto_m_1  |- !m. m multiples_upto 1 = if m = 1 then {1} else {}
   multiples_upto_thm  |- !m n. m multiples_upto n =
                                if m = 0 then {} else IMAGE ($* m) (natural (n DIV m))
   multiples_upto_subset
                       |- !m n. m multiples_upto n SUBSET natural n
   multiples_upto_finite
                       |- !m n. FINITE (m multiples_upto n)
   multiples_upto_card |- !m n. CARD (m multiples_upto n) = if m = 0 then 0 else n DIV m
   coprimes_prime_power|- !p n. prime p ==>
                                coprimes (p ** n) = natural (p ** n) DIFF p multiples_upto p ** n
   phi_prime_power     |- !p n. prime p ==> phi (p ** SUC n) = (p - 1) * p ** n
   phi_prime_sq        |- !p. prime p ==> phi (p * p) = p * (p - 1)
   phi_primes          |- !p q. prime p /\ prime q ==>
                                phi (p * q) = if p = q then p * (p - 1) else (p - 1) * (q - 1)

   Recursive definition of phi:
   rec_phi_def      |- !n. rec_phi n = if n = 0 then 0
                                  else if n = 1 then 1
                                  else n - SIGMA (\a. rec_phi a) {m | m < n /\ m divides n}
   rec_phi_0        |- rec_phi 0 = 0
   rec_phi_1        |- rec_phi 1 = 1
   rec_phi_eq_phi   |- !n. rec_phi n = phi n

   Useful Theorems:
   coprimes_from_not_1_inj     |- INJ coprimes (univ(:num) DIFF {1}) univ(:num -> bool)
   divisors_eq_image_gcd_upto  |- !n. 0 < n ==> divisors n = IMAGE (gcd n) (upto n)
   gcd_eq_equiv_on_upto        |- !n. feq (gcd n) equiv_on upto n
   gcd_eq_upto_partition_by_divisors
                               |- !n. 0 < n ==>
                                      partition (feq (gcd n)) (upto n) =
                                      IMAGE (preimage (gcd n) (upto n)) (divisors n)
   sum_over_upto_by_gcd_partition
                               |- !f n. SIGMA f (upto n) =
                                        SIGMA (SIGMA f) (partition (feq (gcd n)) (upto n))
   sum_over_upto_by_divisors   |- !f n. 0 < n ==>
                                        SIGMA f (upto n) =
                                        SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (upto n)) (divisors n))

   divisors_eq_image_gcd_count |- !n. divisors n = IMAGE (gcd n) (count n)
   gcd_eq_equiv_on_count       |- !n. feq (gcd n) equiv_on count n
   gcd_eq_count_partition_by_divisors
                               |- !n. partition (feq (gcd n)) (count n) =
                                      IMAGE (preimage (gcd n) (count n)) (divisors n)
   sum_over_count_by_gcd_partition
                               |- !f n. SIGMA f (count n) =
                                        SIGMA (SIGMA f) (partition (feq (gcd n)) (count n))
   sum_over_count_by_divisors  |- !f n. SIGMA f (count n) =
                                        SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (count n)) (divisors n))

   divisors_eq_image_gcd_natural
                               |- !n. divisors n = IMAGE (gcd n) (natural n)
   gcd_eq_natural_partition_by_divisors
                               |- !n. partition (feq (gcd n)) (natural n) =
                                      IMAGE (preimage (gcd n) (natural n)) (divisors n)
   sum_over_natural_by_preimage_divisors
                               |- !f n. SIGMA f (natural n) =
                                        SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (natural n)) (divisors n))
   sum_image_divisors_cong     |- !f g. f 0 = g 0 /\ (!n. SIGMA f (divisors n) = SIGMA g (divisors n)) ==> f = g
*)

(* Theory:

Given the set natural 6 = {1, 2, 3, 4, 5, 6}
Every element has a gcd with 6: IMAGE (gcd 6) (natural 6) = {1, 2, 3, 2, 1, 6} = {1, 2, 3, 6}.
Thus the original set is partitioned by gcd: {{1, 5}, {2, 4}, {3}, {6}}
Since (gcd 6) j is a divisor of 6, and they run through all possible divisors of 6,
  SIGMA f (natural 6)
= f 1 + f 2 + f 3 + f 4 + f 5 + f 6
= (f 1 + f 5) + (f 2 + f 4) + f 3 + f 6
= (SIGMA f {1, 5}) + (SIGMA f {2, 4}) + (SIGMA f {3}) + (SIGMA f {6})
= SIGMA (SIGMA f) {{1, 5}, {2, 4}, {3}, {6}}
= SIGMA (SIGMA f) (partition (feq (natural 6) (gcd 6)) (natural 6))

SIGMA:('a -> num) -> ('a -> bool) -> num
SIGMA (f:num -> num):(num -> bool) -> num
SIGMA (SIGMA (f:num -> num)) (s:(num -> bool) -> bool):num

How to relate this to (divisors n) ?
First, observe   IMAGE (gcd 6) (natural 6) = divisors 6
and partition {{1, 5}, {2, 4}, {3}, {6}} = IMAGE (preimage (gcd 6) (natural 6)) (divisors 6)

  SIGMA f (natural 6)
= SIGMA (SIGMA f) (partition (feq (natural 6) (gcd 6)) (natural 6))
= SIGMA (SIGMA f) (IMAGE (preimage (gcd 6) (natural 6)) (divisors 6))

divisors n:num -> bool
preimage (gcd n):(num -> bool) -> num -> num -> bool
preimage (gcd n) (natural n):num -> num -> bool
IMAGE (preimage (gcd n) (natural n)) (divisors n):(num -> bool) -> bool

How to relate this to (coprimes d), where d divides n ?
Note {1, 5} with (gcd 6) j = 1, equals to (coprimes (6 DIV 1)) = coprimes 6
     {2, 4} with (gcd 6) j = 2, BIJ to {2/2, 4/2} with gcd (6/2) (j/2) = 1, i.e {1, 2} = coprimes 3
     {3} with (gcd 6) j = 3, BIJ to {3/3} with gcd (6/3) (j/3) = 1, i.e. {1} = coprimes 2
     {6} with (gcd 6) j = 6, BIJ to {6/6} with gcd (6/6) (j/6) = 1, i.e. {1} = coprimes 1
Hence CARD {{1, 5}, {2, 4}, {3}, {6}} = CARD (partition)
    = CARD {{1, 5}/1, {2,4}/2, {3}/3, {6}/6} = CARD (reduced-partition)
    = CARD {(coprimes 6/1) (coprimes 6/2) (coprimes 6/3) (coprimes 6/6)}
    = CARD {(coprimes 6) (coprimes 3) (coprimes 2) (coprimes 1)}
    = SIGMA (CARD (coprimes d)), over d divides 6)
    = SIGMA (phi d), over d divides 6.
*)

(* Theorem: coprimes n = set (FILTER (\j. coprime j n) (GENLIST SUC n)) *)
(* Proof:
     coprimes n
   = (natural n) INTER {j | coprime j n}             by coprimes_alt
   = (set (GENLIST SUC n)) INTER {j | coprime j n}   by natural_thm
   = {j | coprime j n} INTER (set (GENLIST SUC n))   by INTER_COMM
   = set (FILTER (\j. coprime j n) (GENLIST SUC n))  by LIST_TO_SET_FILTER
*)
val coprimes_thm = store_thm(
  "coprimes_thm",
  ``!n. coprimes n = set (FILTER (\j. coprime j n) (GENLIST SUC n))``,
  rw[coprimes_alt, natural_thm, INTER_COMM, LIST_TO_SET_FILTER]);

(* Relate coprimes to Euler totient *)

(* Theorem: 1 < n ==> (coprimes n = Euler n) *)
(* Proof:
   By Euler_def, this is to show:
   (1) x IN coprimes n ==> 0 < x, true by coprimes_element
   (2) x IN coprimes n ==> x < n, true by coprimes_element_less
   (3) x IN coprimes n ==> coprime n x, true by coprimes_element, GCD_SYM
   (4) 0 < x /\ x < n /\ coprime n x ==> x IN coprimes n
       That is, to show: 0 < x /\ x <= n /\ coprime x n.
       Since x < n ==> x <= n   by LESS_IMP_LESS_OR_EQ
       Hence true by GCD_SYM
*)
val coprimes_eq_Euler = store_thm(
  "coprimes_eq_Euler",
  ``!n. 1 < n ==> (coprimes n = Euler n)``,
  rw[Euler_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[coprimes_element] >-
  rw[coprimes_element_less] >-
  metis_tac[coprimes_element, GCD_SYM] >>
  metis_tac[coprimes_element, GCD_SYM, LESS_IMP_LESS_OR_EQ]);

(* Theorem: prime n ==> (coprimes n = residue n) *)
(* Proof:
   Since prime n ==> 1 < n     by ONE_LT_PRIME
   Hence   coprimes n
         = Euler n             by coprimes_eq_Euler
         = residue n           by Euler_prime
*)
val coprimes_prime = store_thm(
  "coprimes_prime",
  ``!n. prime n ==> (coprimes n = residue n)``,
  rw[ONE_LT_PRIME, coprimes_eq_Euler, Euler_prime]);

(* ------------------------------------------------------------------------- *)
(* Coprimes by a divisor                                                     *)
(* ------------------------------------------------------------------------- *)

(* Define the set of coprimes by a divisor of n *)
val coprimes_by_def = Define `
    coprimes_by n d = if (0 < n /\ d divides n) then coprimes (n DIV d) else {}
`;

(*
EVAL ``coprimes_by 10 2``; = {4; 3; 2; 1}
EVAL ``coprimes_by 10 5``; = {1}
*)

(* Theorem: j IN (coprimes_by n d) <=> (0 < n /\ d divides n /\ j IN coprimes (n DIV d)) *)
(* Proof: by coprimes_by_def, MEMBER_NOT_EMPTY *)
val coprimes_by_element = store_thm(
  "coprimes_by_element",
  ``!n d j. j IN (coprimes_by n d) <=> (0 < n /\ d divides n /\ j IN coprimes (n DIV d))``,
  metis_tac[coprimes_by_def, MEMBER_NOT_EMPTY]);

(* Theorem: FINITE (coprimes_by n d) *)
(* Proof:
   From coprimes_by_def, this follows by:
   (1) !k. FINITE (coprimes k)  by coprimes_finite
   (2) FINITE {}                by FINITE_EMPTY
*)
val coprimes_by_finite = store_thm(
  "coprimes_by_finite",
  ``!n d. FINITE (coprimes_by n d)``,
  rw[coprimes_by_def, coprimes_finite]);

(* Theorem: coprimes_by 0 d = {} *)
(* Proof: by coprimes_by_def *)
val coprimes_by_0 = store_thm(
  "coprimes_by_0",
  ``!d. coprimes_by 0 d = {}``,
  rw[coprimes_by_def]);

(* Theorem: coprimes_by n 0 = {} *)
(* Proof:
     coprimes_by n 0
   = if 0 < n /\ 0 divides n then coprimes (n DIV 0) else {}
   = 0 < 0 then coprimes (n DIV 0) else {}    by ZERO_DIVIDES
   = {}                                       by prim_recTheory.LESS_REFL
*)
val coprimes_by_by_0 = store_thm(
  "coprimes_by_by_0",
  ``!n. coprimes_by n 0 = {}``,
  rw[coprimes_by_def]);

(* Theorem: 0 < n ==> (coprimes_by n 1 = coprimes n) *)
(* Proof:
   Since 1 divides n       by ONE_DIVIDES_ALL
       coprimes_by n 1
     = coprimes (n DIV 1)  by coprimes_by_def
     = coprimes n          by DIV_ONE, ONE
*)
val coprimes_by_by_1 = store_thm(
  "coprimes_by_by_1",
  ``!n. 0 < n ==> (coprimes_by n 1 = coprimes n)``,
  rw[coprimes_by_def]);

(* Theorem: 0 < n ==> (coprimes_by n n = {1}) *)
(* Proof:
   Since n divides n       by DIVIDES_REFL
       coprimes_by n n
     = coprimes (n DIV n)  by coprimes_by_def
     = coprimes 1          by DIVMOD_ID, 0 < n
     = {1}                 by coprimes_1
*)
val coprimes_by_by_last = store_thm(
  "coprimes_by_by_last",
  ``!n. 0 < n ==> (coprimes_by n n = {1})``,
  rw[coprimes_by_def, coprimes_1]);

(* Theorem: 0 < n /\ d divides n ==> (coprimes_by n d = coprimes (n DIV d)) *)
(* Proof: by coprimes_by_def *)
val coprimes_by_by_divisor = store_thm(
  "coprimes_by_by_divisor",
  ``!n d. 0 < n /\ d divides n ==> (coprimes_by n d = coprimes (n DIV d))``,
  rw[coprimes_by_def]);

(* Theorem: 0 < n ==> ((coprimes_by n d = {}) <=> ~(d divides n)) *)
(* Proof:
   If part: 0 < n /\ coprimes_by n d = {} ==> ~(d divides n)
      By contradiction. Suppose d divides n.
      Then d divides n and 0 < n means
           0 < d /\ d <= n                           by divides_pos, 0 < n
      Also coprimes_by n d = coprimes (n DIV d)      by coprimes_by_def
        so coprimes (n DIV d) = {} <=> n DIV d = 0   by coprimes_eq_empty
      Thus n < d                                     by DIV_EQUAL_0
      which contradicts d <= n.
   Only-if part: 0 < n /\ ~(d divides n) ==> coprimes n d = {}
      This follows by coprimes_by_def
*)
val coprimes_by_eq_empty = store_thm(
  "coprimes_by_eq_empty",
  ``!n d. 0 < n ==> ((coprimes_by n d = {}) <=> ~(d divides n))``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `0 < d /\ d <= n` by metis_tac[divides_pos] >>
    `n DIV d = 0` by metis_tac[coprimes_by_def, coprimes_eq_empty] >>
    `n < d` by rw[GSYM DIV_EQUAL_0] >>
    decide_tac,
    rw[coprimes_by_def]
  ]);

(* ------------------------------------------------------------------------- *)
(* GCD Equivalence Class                                                     *)
(* ------------------------------------------------------------------------- *)

(* Define the set of values with the same gcd *)
val gcd_matches_def = zDefine `
    gcd_matches n d = {j| j IN (natural n) /\ (gcd j n = d)}
`;
(* use zDefine as this is not computationally effective. *)

(* Theorem: gcd_matches n d = (natural n) INTER {j | gcd j n = d} *)
(* Proof: by gcd_matches_def *)
Theorem gcd_matches_alt[compute]:
  !n d. gcd_matches n d = (natural n) INTER {j | gcd j n = d}
Proof
  simp[gcd_matches_def, EXTENSION]
QED

(*
EVAL ``gcd_matches 10 2``; = {8; 6; 4; 2}
EVAL ``gcd_matches 10 5``; = {5}
*)

(* Theorem: j IN gcd_matches n d <=> 0 < j /\ j <= n /\ (gcd j n = d) *)
(* Proof: by gcd_matches_def *)
val gcd_matches_element = store_thm(
  "gcd_matches_element",
  ``!n d j. j IN gcd_matches n d <=> 0 < j /\ j <= n /\ (gcd j n = d)``,
  rw[gcd_matches_def, natural_element]);

(* Theorem: (gcd_matches n d) SUBSET (natural n) *)
(* Proof: by gcd_matches_def, SUBSET_DEF *)
val gcd_matches_subset = store_thm(
  "gcd_matches_subset",
  ``!n d. (gcd_matches n d) SUBSET (natural n)``,
  rw[gcd_matches_def, SUBSET_DEF]);

(* Theorem: FINITE (gcd_matches n d) *)
(* Proof:
   Since (gcd_matches n d) SUBSET (natural n)   by coprimes_subset
     and !n. FINITE (natural n)                 by natural_finite
      so FINITE (gcd_matches n d)               by SUBSET_FINITE
*)
val gcd_matches_finite = store_thm(
  "gcd_matches_finite",
  ``!n d. FINITE (gcd_matches n d)``,
  metis_tac[gcd_matches_subset, natural_finite, SUBSET_FINITE]);

(* Theorem: gcd_matches 0 d = {} *)
(* Proof:
       j IN gcd_matches 0 d
   <=> 0 < j /\ j <= 0 /\ (gcd j 0 = d)   by gcd_matches_element
   Since no j can satisfy this, the set is empty.
*)
val gcd_matches_0 = store_thm(
  "gcd_matches_0",
  ``!d. gcd_matches 0 d = {}``,
  rw[gcd_matches_element, EXTENSION]);

(* Theorem: gcd_matches n 0 = {} *)
(* Proof:
       x IN gcd_matches n 0
   <=> 0 < x /\ x <= n /\ (gcd x n = 0)        by gcd_matches_element
   <=> 0 < x /\ x <= n /\ (x = 0) /\ (n = 0)   by GCD_EQ_0
   <=> F                                       by 0 < x, x = 0
   Hence gcd_matches n 0 = {}                  by EXTENSION
*)
val gcd_matches_with_0 = store_thm(
  "gcd_matches_with_0",
  ``!n. gcd_matches n 0 = {}``,
  rw[EXTENSION, gcd_matches_element]);

(* Theorem: gcd_matches 1 d = if d = 1 then {1} else {} *)
(* Proof:
       j IN gcd_matches 1 d
   <=> 0 < j /\ j <= 1 /\ (gcd j 1 = d)   by gcd_matches_element
   Only j to satisfy this is j = 1.
   and d = gcd 1 1 = 1                    by GCD_REF
   If d = 1, j = 1 is the only element.
   If d <> 1, the only element is taken out, set is empty.
*)
val gcd_matches_1 = store_thm(
  "gcd_matches_1",
  ``!d. gcd_matches 1 d = if d = 1 then {1} else {}``,
  rw[gcd_matches_element, EXTENSION]);

(* Theorem: 0 < n /\ d divides n ==> d IN (gcd_matches n d) *)
(* Proof:
   Note  0 < n /\ d divides n
     ==> 0 < d, and d <= n           by divides_pos
     and gcd d n = d                 by divides_iff_gcd_fix
   Hence d IN (gcd_matches n d)      by gcd_matches_element
*)
val gcd_matches_has_divisor = store_thm(
  "gcd_matches_has_divisor",
  ``!n d. 0 < n /\ d divides n ==> d IN (gcd_matches n d)``,
  rw[gcd_matches_element] >-
  metis_tac[divisor_pos] >-
  rw[DIVIDES_LE] >>
  rw[GSYM divides_iff_gcd_fix]);

(* Theorem: j IN (gcd_matches n d) ==> d divides j /\ d divides n *)
(* Proof:
   If j IN (gcd_matches n d), gcd j n = d    by gcd_matches_element
   This means d divides j /\ d divides n     by GCD_IS_GREATEST_COMMON_DIVISOR
*)
val gcd_matches_element_divides = store_thm(
  "gcd_matches_element_divides",
  ``!n d j. j IN (gcd_matches n d) ==> d divides j /\ d divides n``,
  metis_tac[gcd_matches_element, GCD_IS_GREATEST_COMMON_DIVISOR]);

(* Theorem: 0 < n ==> ((gcd_matches n d = {}) <=> ~(d divides n)) *)
(* Proof:
   If part: 0 < n /\ (gcd_matches n d = {}) ==> ~(d divides n)
      By contradiction, suppose d divides n.
      Then d IN gcd_matches n d               by gcd_matches_has_divisor
      This contradicts gcd_matches n d = {}   by MEMBER_NOT_EMPTY
   Only-if part: 0 < n /\ ~(d divides n) ==> (gcd_matches n d = {})
      By contradiction, suppose gcd_matches n d <> {}.
      Then ?j. j IN (gcd_matches n d)         by MEMBER_NOT_EMPTY
      Giving d divides j /\ d divides n       by gcd_matches_element_divides
      This contradicts ~(d divides n).
*)
val gcd_matches_eq_empty = store_thm(
  "gcd_matches_eq_empty",
  ``!n d. 0 < n ==> ((gcd_matches n d = {}) <=> ~(d divides n))``,
  rw[EQ_IMP_THM] >-
  metis_tac[gcd_matches_has_divisor, MEMBER_NOT_EMPTY] >>
  metis_tac[gcd_matches_element_divides, MEMBER_NOT_EMPTY]);

(* ------------------------------------------------------------------------- *)
(* Phi Function                                                              *)
(* ------------------------------------------------------------------------- *)

(* Define the Euler phi function from coprime set *)
val phi_def = Define `
   phi n = CARD (coprimes n)
`;
(* Since (coprimes n) is computable, phi n is now computable *)

(*
> EVAL ``phi 10``;
val it = |- phi 10 = 4: thm
*)

(* Theorem: phi n = LENGTH (FILTER (\j. coprime j n) (GENLIST SUC n)) *)
(* Proof:
   Let ls = FILTER (\j. coprime j n) (GENLIST SUC n).
   Note ALL_DISTINCT (GENLIST SUC n)       by ALL_DISTINCT_GENLIST, SUC_EQ
   Thus ALL_DISTINCT ls                    by FILTER_ALL_DISTINCT
     phi n = CARD (coprimes n)             by phi_def
           = CARD (set ls)                 by coprimes_thm
           = LENGTH ls                     by ALL_DISTINCT_CARD_LIST_TO_SET
*)
val phi_thm = store_thm(
  "phi_thm",
  ``!n. phi n = LENGTH (FILTER (\j. coprime j n) (GENLIST SUC n))``,
  rpt strip_tac >>
  qabbrev_tac `ls = FILTER (\j. coprime j n) (GENLIST SUC n)` >>
  `ALL_DISTINCT ls` by rw[ALL_DISTINCT_GENLIST, FILTER_ALL_DISTINCT, Abbr`ls`] >>
  `phi n = CARD (coprimes n)` by rw[phi_def] >>
  `_ = CARD (set ls)` by rw[coprimes_thm, Abbr`ls`] >>
  `_ = LENGTH ls` by rw[ALL_DISTINCT_CARD_LIST_TO_SET] >>
  decide_tac);

(* Theorem: phi = CARD o coprimes *)
(* Proof: by phi_def, FUN_EQ_THM *)
val phi_fun = store_thm(
  "phi_fun",
  ``phi = CARD o coprimes``,
  rw[phi_def, FUN_EQ_THM]);

(* Theorem: 0 < n ==> 0 < phi n *)
(* Proof:
   Since 1 IN coprimes n       by coprimes_has_1
      so coprimes n <> {}      by MEMBER_NOT_EMPTY
     and FINITE (coprimes n)   by coprimes_finite
   hence phi n <> 0            by CARD_EQ_0
      or 0 < phi n
*)
val phi_pos = store_thm(
  "phi_pos",
  ``!n. 0 < n ==> 0 < phi n``,
  rpt strip_tac >>
  `coprimes n <> {}` by metis_tac[coprimes_has_1, MEMBER_NOT_EMPTY] >>
  `FINITE (coprimes n)` by rw[coprimes_finite] >>
  `phi n <> 0` by rw[phi_def, CARD_EQ_0] >>
  decide_tac);

(* Theorem: phi 0 = 0 *)
(* Proof:
     phi 0
   = CARD (coprimes 0)   by phi_def
   = CARD {}             by coprimes_0
   = 0                   by CARD_EMPTY
*)
val phi_0 = store_thm(
  "phi_0",
  ``phi 0 = 0``,
  rw[phi_def, coprimes_0]);

(* Theorem: (phi n = 0) <=> (n = 0) *)
(* Proof:
   If part: (phi n = 0) ==> (n = 0)    by phi_pos, NOT_ZERO_LT_ZERO
   Only-if part: phi 0 = 0             by phi_0
*)
val phi_eq_0 = store_thm(
  "phi_eq_0",
  ``!n. (phi n = 0) <=> (n = 0)``,
  metis_tac[phi_0, phi_pos, NOT_ZERO_LT_ZERO]);

(* Theorem: phi 1 = 1 *)
(* Proof:
     phi 1
   = CARD (coprimes 1)    by phi_def
   = CARD {1}             by coprimes_1
   = 1                    by CARD_SING
*)
val phi_1 = store_thm(
  "phi_1",
  ``phi 1 = 1``,
  rw[phi_def, coprimes_1]);

(* Theorem: 1 < n ==> (phi n = totient n) *)
(* Proof:
      phi n
    = CARD (coprimes n)     by phi_def
    = CARD (Euler n )       by coprimes_eq_Euler
    = totient n             by totient_def
*)
val phi_eq_totient = store_thm(
  "phi_eq_totient",
  ``!n. 1 < n ==> (phi n = totient n)``,
  rw[phi_def, totient_def, coprimes_eq_Euler]);

(* Theorem: prime n ==> (phi n = n - 1) *)
(* Proof:
   Since prime n ==> 1 < n   by ONE_LT_PRIME
   Hence   phi n
         = totient n         by phi_eq_totient
         = n - 1             by Euler_card_prime
*)
val phi_prime = store_thm(
  "phi_prime",
  ``!n. prime n ==> (phi n = n - 1)``,
  rw[ONE_LT_PRIME, phi_eq_totient, Euler_card_prime]);

(* Theorem: phi 2 = 1 *)
(* Proof:
   Since prime 2               by PRIME_2
      so phi 2 = 2 - 1 = 1     by phi_prime
*)
val phi_2 = store_thm(
  "phi_2",
  ``phi 2 = 1``,
  rw[phi_prime, PRIME_2]);

(* Theorem: 2 < n ==> 1 < phi n *)
(* Proof:
   Note 1 IN (coprimes n)        by coprimes_has_1, 0 < n
    and (n - 1) IN (coprimes n)  by coprimes_has_last_but_1, 1 < n
    and n - 1 <> 1               by 2 < n
    Now FINITE (coprimes n)      by coprimes_finite]
    and {1; (n-1)} SUBSET (coprimes n)   by SUBSET_DEF, above
   Note CARD {1; (n-1)} = 2      by CARD_INSERT, CARD_EMPTY, TWO
   thus 2 <= CARD (coprimes n)   by CARD_SUBSET
     or 1 < phi n                by phi_def
*)
val phi_gt_1 = store_thm(
  "phi_gt_1",
  ``!n. 2 < n ==> 1 < phi n``,
  rw[phi_def] >>
  `0 < n /\ 1 < n /\ n - 1 <> 1` by decide_tac >>
  `1 IN (coprimes n)` by rw[coprimes_has_1] >>
  `(n - 1) IN (coprimes n)` by rw[coprimes_has_last_but_1] >>
  `FINITE (coprimes n)` by rw[coprimes_finite] >>
  `{1; (n-1)} SUBSET (coprimes n)` by rw[SUBSET_DEF] >>
  `CARD {1; (n-1)} = 2` by rw[] >>
  `2 <= CARD (coprimes n)` by metis_tac[CARD_SUBSET] >>
  decide_tac);

(* Theorem: phi n <= n *)
(* Proof:
   Note phi n = CARD (coprimes n)    by phi_def
    and coprimes n SUBSET natural n  by coprimes_subset
    Now FINITE (natural n)           by natural_finite
    and CARD (natural n) = n         by natural_card
     so CARD (coprimes n) <= n       by CARD_SUBSET
*)
val phi_le = store_thm(
  "phi_le",
  ``!n. phi n <= n``,
  metis_tac[phi_def, coprimes_subset, natural_finite, natural_card, CARD_SUBSET]);

(* Theorem: 1 < n ==> phi n < n *)
(* Proof:
   Note phi n = CARD (coprimes n)    by phi_def
    and 1 < n ==> !j. j IN coprimes n ==> j < n     by coprimes_element_less
    but 0 NOTIN coprimes n           by coprimes_no_0
     or coprimes n SUBSET (count n) DIFF {0}  by SUBSET_DEF, IN_DIFF
    Let s = (count n) DIFF {0}.
   Note {0} SUBSET count n           by SUBSET_DEF]);
     so count n INTER {0} = {0}      by SUBSET_INTER_ABSORPTION
    Now FINITE s                     by FINITE_COUNT, FINITE_DIFF
    and CARD s = n - 1               by CARD_COUNT, CARD_DIFF, CARD_SING
     so CARD (coprimes n) <= n - 1   by CARD_SUBSET
     or phi n < n                    by arithmetic
*)
val phi_lt = store_thm(
  "phi_lt",
  ``!n. 1 < n ==> phi n < n``,
  rw[phi_def] >>
  `!j. j IN coprimes n ==> j < n` by rw[coprimes_element_less] >>
  `!j. j IN coprimes n ==> j <> 0` by metis_tac[coprimes_no_0] >>
  qabbrev_tac `s = (count n) DIFF {0}` >>
  `coprimes n SUBSET s` by rw[SUBSET_DEF, Abbr`s`] >>
  `{0} SUBSET count n` by rw[SUBSET_DEF] >>
  `count n INTER {0} = {0}` by metis_tac[SUBSET_INTER_ABSORPTION, INTER_COMM] >>
  `FINITE s` by rw[Abbr`s`] >>
  `CARD s = n - 1` by rw[Abbr`s`] >>
  `CARD (coprimes n) <= n - 1` by metis_tac[CARD_SUBSET] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Divisors                                                                  *)
(* ------------------------------------------------------------------------- *)

(* Define the set of divisors of a number. *)
Definition divisors_def[nocompute]:
   divisors n = {d | 0 < d /\ d <= n /\ d divides n}
End
(* use [nocompute] as this is not computationally effective. *)
(* Note: use of 0 < d to have positive divisors, as only 0 divides 0. *)
(* Note: use of d <= n to give divisors_0 = {}, since ALL_DIVIDES_0. *)
(* Note: for 0 < n, d <= n is redundant, as DIVIDES_LE implies it. *)

(* Theorem: d IN divisors n <=> 0 < d /\ d <= n /\ d divides n *)
(* Proof: by divisors_def *)
Theorem divisors_element:
  !n d. d IN divisors n <=> 0 < d /\ d <= n /\ d divides n
Proof
  rw[divisors_def]
QED

(* Theorem: 0 < n ==> !d. d IN divisors n <=> d divides n *)
(* Proof:
   If part: d IN divisors n ==> d divides n
      This is true                 by divisors_element
   Only-if part: 0 < n /\ d divides n ==> d IN divisors n
      Since 0 < n /\ d divides n
        ==> 0 < d /\ d <= n        by divides_pos
      Hence d IN divisors n        by divisors_element
*)
Theorem divisors_element_alt:
  !n. 0 < n ==> !d. d IN divisors n <=> d divides n
Proof
  metis_tac[divisors_element, divides_pos]
QED

(* Theorem: d IN divisors n ==> 0 < n *)
(* Proof:
   Note 0 < d /\ d <= n /\ d divides n         by divisors_def
     so 0 < n                                  by inequality
*)
Theorem divisors_has_element:
  !n d. d IN divisors n ==> 0 < n
Proof
  simp[divisors_def]
QED

(* Theorem: 0 < n ==> 1 IN (divisors n) *)
(* Proof:
    Note 1 divides n         by ONE_DIVIDES_ALL
   Hence 1 IN (divisors n)   by divisors_element_alt
*)
Theorem divisors_has_1:
  !n. 0 < n ==> 1 IN (divisors n)
Proof
  simp[divisors_element_alt]
QED

(* Theorem: 0 < n ==> n IN (divisors n) *)
(* Proof:
    Note n divides n         by DIVIDES_REFL
   Hence n IN (divisors n)   by divisors_element_alt
*)
Theorem divisors_has_last:
  !n. 0 < n ==> n IN (divisors n)
Proof
  simp[divisors_element_alt]
QED

(* Theorem: 0 < n ==> divisors n <> {} *)
(* Proof: by divisors_has_last, MEMBER_NOT_EMPTY *)
Theorem divisors_not_empty:
  !n. 0 < n ==> divisors n <> {}
Proof
  metis_tac[divisors_has_last, MEMBER_NOT_EMPTY]
QED

(* Theorem: divisors 0 = {} *)
(* Proof: by divisors_def, 0 < d /\ d <= 0 is impossible. *)
Theorem divisors_0:
  divisors 0 = {}
Proof
  simp[divisors_def]
QED

(* Theorem: divisors 1 = {1} *)
(* Proof: by divisors_def, 0 < d /\ d <= 1 ==> d = 1. *)
Theorem divisors_1:
  divisors 1 = {1}
Proof
  rw[divisors_def, EXTENSION]
QED

(* Theorem: divisors n = {} <=> n = 0 *)
(* Proof:
   By EXTENSION, this is to show:
   (1) divisors n = {} ==> n = 0
       By contradiction, suppose n <> 0.
       Then 1 IN (divisors n)                  by divisors_has_1
       This contradicts divisors n = {}        by MEMBER_NOT_EMPTY
   (2) n = 0 ==> divisors n = {}
       This is true                            by divisors_0
*)
Theorem divisors_eq_empty:
  !n. divisors n = {} <=> n = 0
Proof
  rw[EQ_IMP_THM] >-
  metis_tac[divisors_has_1, MEMBER_NOT_EMPTY, NOT_ZERO] >>
  simp[divisors_0]
QED

(* Idea: a method to evaluate divisors. *)

(* Theorem: divisors n = IMAGE (\j. if (j + 1) divides n then j + 1 else 1) (count n) *)
(* Proof:
   Let f = \j. if (j + 1) divides n then j + 1 else 1.
   If n = 0,
        divisors 0
      = {d | 0 < d /\ d <= 0 /\ d divides 0}   by divisors_def
      = {}                                     by 0 < d /\ d <= 0
      = IMAGE f {}                             by IMAGE_EMPTY
      = IMAGE f (count 0)                      by COUNT_0
   If n <> 0,
        divisors n
      = {d | 0 < d /\ d <= n /\ d divides n}   by divisors_def
      = {d | d <> 0 /\ d <= n /\ d divides n}  by 0 < d
      = {k + 1 | (k + 1) <= n /\ (k + 1) divides n}
                                               by num_CASES, d <> 0
      = {k + 1 | k < n /\ (k + 1) divides n}   by arithmetic
      = IMAGE f {k | k < n}                    by IMAGE_DEF
      = IMAGE f (count n)                      by count_def
*)
Theorem divisors_eqn[compute]:
  !n. divisors n = IMAGE (\j. if (j + 1) divides n then j + 1 else 1) (count n)
Proof
  (rw[divisors_def, EXTENSION, EQ_IMP_THM] >> rw[]) >>
  `?k. x = SUC k` by metis_tac[num_CASES, NOT_ZERO] >>
  qexists_tac `k` >>
  fs[ADD1]
QED

(*
> EVAL ``divisors 3``; = {3; 1}: thm
> EVAL ``divisors 4``; = {4; 2; 1}: thm
> EVAL ``divisors 5``; = {5; 1}: thm
> EVAL ``divisors 6``; = {6; 3; 2; 1}: thm
> EVAL ``divisors 7``; = {7; 1}: thm
> EVAL ``divisors 8``; = {8; 4; 2; 1}: thm
> EVAL ``divisors 9``; = {9; 3; 1}: thm
*)

(* Idea: each factor of a product divides the product. *)

(* Theorem: 0 < n /\ n = p * q ==> p IN divisors n /\ q IN divisors n *)
(* Proof:
   Note 0 < p /\ 0 < q             by MULT_EQ_0
     so p <= n /\ q <= n           by arithmetic
    and p divides n                by divides_def
    and q divides n                by divides_def, MULT_COMM
    ==> p IN divisors n /\
        q IN divisors n            by divisors_element_alt, 0 < n
*)
Theorem divisors_has_factor:
  !n p q. 0 < n /\ n = p * q ==> p IN divisors n /\ q IN divisors n
Proof
  (rw[divisors_element_alt] >> metis_tac[MULT_EQ_0, NOT_ZERO])
QED

(* Idea: when factor divides, its cofactor also divides. *)

(* Theorem: d IN divisors n ==> (n DIV d) IN divisors n *)
(* Proof:
   Note 0 < d /\ d <= n /\ d divides n         by divisors_def
    and 0 < n                                  by 0 < d /\ d <= n
     so 0 < n DIV d                            by DIV_POS, 0 < n
    and n DIV d <= n                           by DIV_LESS_EQ, 0 < d
    and n DIV d divides n                      by DIVIDES_COFACTOR, 0 < d
     so (n DIV d) IN divisors n                by divisors_def
*)
Theorem divisors_has_cofactor:
  !n d. d IN divisors n ==> (n DIV d) IN divisors n
Proof
  simp [divisors_def] >>
  ntac 3 strip_tac >>
  `0 < n` by decide_tac >>
  rw[DIV_POS, DIV_LESS_EQ, DIVIDES_COFACTOR]
QED

(* Theorem: (divisors n) DELETE n = {m | 0 < m /\ m < n /\ m divides n} *)
(* Proof:
     (divisors n) DELETE n
   = {m | 0 < m /\ m <= n /\ m divides n} DELETE n     by divisors_def
   = {m | 0 < m /\ m <= n /\ m divides n} DIFF {n}     by DELETE_DEF
   = {m | 0 < m /\ m <> n /\ m <= n /\ m divides n}    by IN_DIFF
   = {m | 0 < m /\ m < n /\ m divides n}               by LESS_OR_EQ
*)
Theorem divisors_delete_last:
  !n. (divisors n) DELETE n = {m | 0 < m /\ m < n /\ m divides n}
Proof
  rw[divisors_def, EXTENSION, EQ_IMP_THM]
QED

(* Theorem: d IN (divisors n) ==> 0 < d *)
(* Proof: by divisors_def. *)
Theorem divisors_nonzero:
  !n d. d IN (divisors n) ==> 0 < d
Proof
  simp[divisors_def]
QED

(* Theorem: (divisors n) SUBSET (natural n) *)
(* Proof:
   By SUBSET_DEF, this is to show:
       x IN (divisors n) ==> x IN (natural n)
       x IN (divisors n)
   ==> 0 < x /\ x <= n /\ x divides n          by divisors_element
   ==> 0 < x /\ x <= n
   ==> x IN (natural n)                        by natural_element
*)
Theorem divisors_subset_natural:
  !n. (divisors n) SUBSET (natural n)
Proof
  rw[divisors_element, natural_element, SUBSET_DEF]
QED

(* Theorem: FINITE (divisors n) *)
(* Proof:
   Since (divisors n) SUBSET (natural n)       by divisors_subset_natural
     and FINITE (naturnal n)                   by natural_finite
      so FINITE (divisors n)                   by SUBSET_FINITE
*)
Theorem divisors_finite:
  !n. FINITE (divisors n)
Proof
  metis_tac[divisors_subset_natural, natural_finite, SUBSET_FINITE]
QED

(* Theorem: BIJ (\d. n DIV d) (divisors n) (divisors n) *)
(* Proof:
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) d IN divisors n ==> n DIV d IN divisors n
       This is true                                       by divisors_has_cofactor
   (2) d IN divisors n /\ d' IN divisors n /\ n DIV d = n DIV d' ==> d = d'
       d IN divisors n ==> d divides n /\ 0 < d           by divisors_element
       d' IN divisors n ==> d' divides n /\ 0 < d'        by divisors_element
       Also d IN divisors n ==> 0 < n                     by divisors_has_element
       Hence n = (n DIV d) * d  and n = (n DIV d') * d'   by DIVIDES_EQN
       giving   (n DIV d) * d = (n DIV d') * d'
       Now (n DIV d) <> 0, otherwise contradicts n <> 0   by MULT
       Hence                d = d'                        by EQ_MULT_LCANCEL
   (3) same as (1), true                                  by divisors_has_cofactor
   (4) x IN divisors n ==> ?d. d IN divisors n /\ (n DIV d = x)
       Note x IN divisors n ==> x divides n               by divisors_element
        and 0 < n                                         by divisors_has_element
       Let d = n DIV x.
       Then d IN divisors n                               by divisors_has_cofactor
       and  n DIV d = n DIV (n DIV x) = x                 by divide_by_cofactor, 0 < n
*)
Theorem divisors_divisors_bij:
  !n. (\d. n DIV d) PERMUTES divisors n
Proof
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >-
  rw[divisors_has_cofactor] >-
 (`n = (n DIV d) * d` by metis_tac[DIVIDES_EQN, divisors_element] >>
  `n = (n DIV d') * d'` by metis_tac[DIVIDES_EQN, divisors_element] >>
  `0 < n` by metis_tac[divisors_has_element] >>
  `n DIV d <> 0` by metis_tac[MULT, NOT_ZERO] >>
  metis_tac[EQ_MULT_LCANCEL]) >-
  rw[divisors_has_cofactor] >>
  `0 < n` by metis_tac[divisors_has_element] >>
  metis_tac[divisors_element, divisors_has_cofactor, divide_by_cofactor]
QED

(* ------------------------------------------------------------------------- *)
(* An upper bound for divisors.                                              *)
(* ------------------------------------------------------------------------- *)

(* Idea: if a divisor of n is less or equal to (SQRT n), its cofactor is more or equal to (SQRT n) *)

(* Theorem: 0 < p /\ p divides n /\ p <= SQRT n ==> SQRT n <= (n DIV p) *)
(* Proof:
   Let m = SQRT n, then p <= m.
   By contradiction, suppose (n DIV p) < m.
   Then  n = (n DIV p) * p         by DIVIDES_EQN, 0 < p
          <= (n DIV p) * m         by p <= m
           < m * m                 by (n DIV p) < m
          <= n                     by SQ_SQRT_LE
   giving n < n, which is a contradiction.
*)
Theorem divisor_le_cofactor_ge:
  !n p. 0 < p /\ p divides n /\ p <= SQRT n ==> SQRT n <= (n DIV p)
Proof
  rpt strip_tac >>
  qabbrev_tac `m = SQRT n` >>
  spose_not_then strip_assume_tac >>
  `n = (n DIV p) * p` by rfs[DIVIDES_EQN] >>
  `(n DIV p) * p <= (n DIV p) * m` by fs[] >>
  `(n DIV p) * m < m * m` by fs[] >>
  `m * m <= n` by simp[SQ_SQRT_LE, Abbr`m`] >>
  decide_tac
QED

(* Idea: if a divisor of n is greater than (SQRT n), its cofactor is less or equal to (SQRT n) *)

(* Theorem: 0 < p /\ p divides n /\ SQRT n < p ==> (n DIV p) <= SQRT n *)
(* Proof:
   Let m = SQRT n, then m < p.
   By contradiction, suppose m < (n DIV p).
   Let q = (n DIV p).
   Then SUC m <= p, SUC m <= q     by m < p, m < q
   and   n = q * p                 by DIVIDES_EQN, 0 < p
          >= (SUC m) * (SUC m)     by LESS_MONO_MULT2
           = (SUC m) ** 2          by EXP_2
           > n                     by SQRT_PROPERTY
   which is a contradiction.
*)
Theorem divisor_gt_cofactor_le:
  !n p. 0 < p /\ p divides n /\ SQRT n < p ==> (n DIV p) <= SQRT n
Proof
  rpt strip_tac >>
  qabbrev_tac `m = SQRT n` >>
  spose_not_then strip_assume_tac >>
  `n = (n DIV p) * p` by rfs[DIVIDES_EQN] >>
  qabbrev_tac `q = n DIV p` >>
  `SUC m <= p /\ SUC m <= q` by decide_tac >>
  `(SUC m) * (SUC m) <= q * p` by simp[LESS_MONO_MULT2] >>
  `n < (SUC m) * (SUC m)` by metis_tac[SQRT_PROPERTY, EXP_2] >>
  decide_tac
QED

(* Idea: for (divisors n), the map (\j. n DIV j) is injective. *)

(* Theorem: INJ (\j. n DIV j) (divisors n) univ(:num) *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) !x. x IN (divisors n) ==> (\j. n DIV j) x IN univ(:num)
       True by types, n DIV j is a number, with type :num.
   (2) !x y. x IN (divisors n) /\ y IN (divisors n) /\ n DIV x = n DIV y ==> x = y
       Note x divides n /\ 0 < x /\ x <= n     by divisors_def
        and y divides n /\ 0 < y /\ x <= n     by divisors_def
        Let p = n DIV x, q = n DIV y.
       Note 0 < n                              by divisors_has_element
       then 0 < p, 0 < q                       by DIV_POS, 0 < n
       Then  n = p * x = q * y                 by DIVIDES_EQN, 0 < x, 0 < y
        But          p = q                     by given
         so          x = y                     by EQ_MULT_LCANCEL
*)
Theorem divisors_cofactor_inj:
  !n. INJ (\j. n DIV j) (divisors n) univ(:num)
Proof
  rw[INJ_DEF, divisors_def] >>
  `n = n DIV j * j` by fs[GSYM DIVIDES_EQN] >>
  `n = n DIV j' * j'` by fs[GSYM DIVIDES_EQN] >>
  `0 < n` by fs[GSYM divisors_has_element] >>
  metis_tac[EQ_MULT_LCANCEL, DIV_POS, NOT_ZERO]
QED

(* Idea: an upper bound for CARD (divisors n).

To prove: 0 < n ==> CARD (divisors n) <= 2 * SQRT n
Idea of proof:
   Consider the two sets,
      s = {x | x IN divisors n /\ x <= SQRT n}
      t = {x | x IN divisors n /\ SQRT n <= x}
   Note s SUBSET (natural (SQRT n)), so CARD s <= SQRT n.
   Also t SUBSET (natural (SQRT n)), so CARD t <= SQRT n.
   There is a bijection between the two parts:
      BIJ (\j. n DIV j) s t
   Now divisors n = s UNION t
      CARD (divisors n)
    = CARD s + CARD t - CARD (s INTER t)
   <= CARD s + CARD t
   <= SQRT n + SQRT n
    = 2 * SQRT n

   The BIJ part will be quite difficult.
   So the actual proof is a bit different.
*)

(* Theorem: CARD (divisors n) <= 2 * SQRT n *)
(* Proof:
   Let m = SQRT n,
       d = divisors n,
       s = {x | x IN d /\ x <= m},
       f = \j. n DIV j,
       t = IMAGE f s.

   Claim: s SUBSET natural m
   Proof: By SUBSET_DEF, this is to show:
             x IN d /\ x <= m ==> ?y. x = SUC y /\ y < m
          Note 0 < x               by divisors_nonzero
          Let y = PRE x.
          Then x = SUC (PRE x)     by SUC_PRE
           and PRE x < x           by PRE_LESS
            so PRE x < m           by inequality, x <= m

   Claim: BIJ f s t
   Proof: Note s SUBSET d          by SUBSET_DEF
           and INJ f d univ(:num)  by divisors_cofactor_inj
            so INJ f s univ(:num)  by INJ_SUBSET, SUBSET_REFL
           ==> BIJ f s t           by INJ_IMAGE_BIJ_ALT

   Claim: d = s UNION t
   Proof: By EXTENSION, EQ_IMP_THM, this is to show:
          (1) x IN divisors n ==> x <= m \/ ?j. x = n DIV j /\ j IN divisors n /\ j <= m
              If x <= m, this is trivial.
              Otherwise, m < x.
              Let j = n DIV x.
              Then x = n DIV (n DIV x)         by divide_by_cofactor
               and (n DIV j) IN divisors n     by divisors_has_cofactor
               and (n DIV j) <= m              by divisor_gt_cofactor_le
          (2) j IN divisors n ==> n DIV j IN divisors n
              This is true                     by divisors_has_cofactor

    Now FINITE (natural m)         by natural_finite
     so FINITE s                   by SUBSET_FINITE
    and FINITE t                   by IMAGE_FINITE
     so CARD s <= m                by CARD_SUBSET, natural_card
   Also CARD t = CARD s            by FINITE_BIJ_CARD

        CARD d <= CARD s + CARD t  by CARD_UNION_LE, d = s UNION t
               <= m + m            by above
                = 2 * m            by arithmetic
*)
Theorem divisors_card_upper:
  !n. CARD (divisors n) <= 2 * SQRT n
Proof
  rpt strip_tac >>
  qabbrev_tac `m = SQRT n` >>
  qabbrev_tac `d = divisors n` >>
  qabbrev_tac `s = {x | x IN d /\ x <= m}` >>
  qabbrev_tac `f = \j. n DIV j` >>
  qabbrev_tac `t = (IMAGE f s)` >>
  `s SUBSET (natural m)` by
  (rw[SUBSET_DEF, Abbr`s`] >>
  `0 < x` by metis_tac[divisors_nonzero] >>
  qexists_tac `PRE x` >>
  simp[]) >>
  `BIJ f s t` by
    (simp[Abbr`t`] >>
  irule INJ_IMAGE_BIJ_ALT >>
  `s SUBSET d` by rw[SUBSET_DEF, Abbr`s`] >>
  `INJ f d univ(:num)` by metis_tac[divisors_cofactor_inj] >>
  metis_tac[INJ_SUBSET, SUBSET_REFL]) >>
  `d = s UNION t` by
      (rw[EXTENSION, Abbr`d`, Abbr`s`, Abbr`t`, Abbr`f`, EQ_IMP_THM] >| [
    (Cases_on `x <= m` >> simp[]) >>
    qexists_tac `n DIV x` >>
    `0 < x /\ x <= n /\ x divides n` by fs[divisors_element] >>
    simp[divide_by_cofactor, divisors_has_cofactor] >>
    `m < x` by decide_tac >>
    simp[divisor_gt_cofactor_le, Abbr`m`],
    simp[divisors_has_cofactor]
  ]) >>
  `FINITE (natural m)` by simp[natural_finite] >>
  `FINITE s /\ FINITE t` by metis_tac[SUBSET_FINITE, IMAGE_FINITE] >>
  `CARD s <= m` by metis_tac[CARD_SUBSET, natural_card] >>
  `CARD t = CARD s` by metis_tac[FINITE_BIJ_CARD] >>
  `CARD d <= CARD s + CARD t` by metis_tac[CARD_UNION_LE] >>
  decide_tac
QED

(* This is a remarkable result! *)


(* ------------------------------------------------------------------------- *)
(* Gauss' Little Theorem                                                     *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* Gauss' Little Theorem: sum of phi over divisors                           *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* Gauss' Little Theorem: A general theory on sum over divisors              *)
(* ------------------------------------------------------------------------- *)

(*
Let n = 6. (divisors 6) = {1, 2, 3, 6}
  IMAGE coprimes (divisors 6)
= {coprimes 1, coprimes 2, coprimes 3, coprimes 6}
= {{1}, {1}, {1, 2}, {1, 5}}   <-- will collapse
  IMAGE (preimage (gcd 6) (count 6)) (divisors 6)
= {{preimage in count 6 of those gcd 6 j = 1},
   {preimage in count 6 of those gcd 6 j = 2},
   {preimage in count 6 of those gcd 6 j = 3},
   {preimage in count 6 of those gcd 6 j = 6}}
= {{1, 5}, {2, 4}, {3}, {6}}
= {1x{1, 5}, 2x{1, 2}, 3x{1}, 6x{1}}
!s. s IN (IMAGE (preimage (gcd n) (count n)) (divisors n))
==> ?d. d divides n /\ d < n /\ s = preimage (gcd n) (count n) d
==> ?d. d divides n /\ d < n /\ s = IMAGE (TIMES d) (coprimes ((gcd n d) DIV d))

  IMAGE (feq_class (count 6) (gcd 6)) (divisors 6)
= {{feq_class in count 6 of those gcd 6 j = 1},
   {feq_class in count 6 of those gcd 6 j = 2},
   {feq_class in count 6 of those gcd 6 j = 3},
   {feq_class in count 6 of those gcd 6 j = 6}}
= {{1, 5}, {2, 4}, {3}, {6}}
= {1x{1, 5}, 2x{1, 2}, 3x{1}, 6x{1}}
That is:  CARD {1, 5} = CARD (coprime 6) = CARD (coprime (6 DIV 1))
          CARD {2, 4} = CARD (coprime 3) = CARD (coprime (6 DIV 2))
          CARD {3} = CARD (coprime 2) = CARD (coprime (6 DIV 3)))
          CARD {6} = CARD (coprime 1) = CARD (coprime (6 DIV 6)))

*)
(* Note:
   In general, what is the condition for:  SIGMA f s = SIGMA g t ?
   Conceptually,
       SIGMA f s = f s1 + f s2 + f s3 + ... + f sn
   and SIGMA g t = g t1 + g t2 + g t3 + ... + g tm

SUM_IMAGE_eq_SUM_MAP_SET_TO_LIST

Use disjoint_bigunion_card
|- !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==> (CARD (BIGUNION P) = SIGMA CARD P)
If a partition P = {s | condition on s} the element s = IMAGE g t
e.g.  P = {{1, 5} {2, 4} {3} {6}}
        = {IMAGE (TIMES 1) (coprimes 6/1),
           IMAGE (TIMES 2) (coprimes 6/2),
           IMAGE (TIMES 3) (coprimes 6/3),
           IMAGE (TIMES 6) (coprimes 6/6)}
        =  IMAGE (\d. TIMES d o coprimes (6/d)) {1, 2, 3, 6}

*)

(* Theorem: d divides n ==> !j. j IN gcd_matches n d ==> j DIV d IN coprimes_by n d *)
(* Proof:
   When n = 0, gcd_matches 0 d = {}       by gcd_matches_0, hence trivially true.
   Otherwise,
   By coprimes_by_def, this is to show:
      0 < n /\ d divides n ==> !j. j IN gcd_matches n d ==> j DIV d IN coprimes (n DIV d)
   Note j IN gcd_matches n d
    ==> d divides j               by gcd_matches_element_divides
   Also d IN gcd_matches n d      by gcd_matches_has_divisor
     so 0 < d /\ (d = gcd j n)    by gcd_matches_element
     or d <> 0 /\ (d = gcd n j)   by GCD_SYM
   With the given d divides n,
        j = d * (j DIV d)         by DIVIDES_EQN, MULT_COMM, 0 < d
        n = d * (n DIV d)         by DIVIDES_EQN, MULT_COMM, 0 < d
  Hence d = d * gcd (n DIV d) (j DIV d)        by GCD_COMMON_FACTOR
     or d * 1 = d * gcd (n DIV d) (j DIV d)    by MULT_RIGHT_1
  giving    1 = gcd (n DIV d) (j DIV d)        by EQ_MULT_LCANCEL, d <> 0
      or    coprime (j DIV d) (n DIV d)        by GCD_SYM
   Also j IN natural n            by gcd_matches_subset, SUBSET_DEF
  Hence 0 < j DIV d /\ j DIV d <= n DIV d      by natural_cofactor_natural_reduced
     or j DIV d IN coprimes (n DIV d)          by coprimes_element
*)
val gcd_matches_divisor_element = store_thm(
  "gcd_matches_divisor_element",
  ``!n d. d divides n ==> !j. j IN gcd_matches n d ==> j DIV d IN coprimes_by n d``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  metis_tac[gcd_matches_0, NOT_IN_EMPTY] >>
  `0 < n` by decide_tac >>
  rw[coprimes_by_def] >>
  `d divides j` by metis_tac[gcd_matches_element_divides] >>
  `0 < d /\ 0 < j /\ j <= n /\ (d = gcd n j)` by metis_tac[gcd_matches_has_divisor, gcd_matches_element, GCD_SYM] >>
  `d <> 0` by decide_tac >>
  `(j = d * (j DIV d)) /\ (n = d * (n DIV d))` by metis_tac[DIVIDES_EQN, MULT_COMM] >>
  `coprime (n DIV d) (j DIV d)` by metis_tac[GCD_COMMON_FACTOR, MULT_RIGHT_1, EQ_MULT_LCANCEL] >>
  `0 < j DIV d /\ j DIV d <= n DIV d` by metis_tac[natural_cofactor_natural_reduced, natural_element] >>
  metis_tac[coprimes_element, GCD_SYM]);

(* Theorem: d divides n ==> BIJ (\j. j DIV d) (gcd_matches n d) (coprimes_by n d) *)
(* Proof:
   When n = 0, gcd_matches 0 d = {}       by gcd_matches_0
           and coprimes_by 0 d = {}       by coprimes_by_0, hence trivially true.
   Otherwise,
   By definitions, this is to show:
   (1) j IN gcd_matches n d ==> j DIV d IN coprimes_by n d
       True by gcd_matches_divisor_element.
   (2) j IN gcd_matches n d /\ j' IN gcd_matches n d /\ j DIV d = j' DIV d ==> j = j'
      Note j IN gcd_matches n d /\ j' IN gcd_matches n d
       ==> d divides j /\ d divides j'             by gcd_matches_element_divides
      Also d IN (gcd_matches n d)                  by gcd_matches_has_divisor
        so 0 < d                                   by gcd_matches_element
      Thus j = (j DIV d) * d                       by DIVIDES_EQN, 0 < d
       and j' = (j' DIV d) * d                     by DIVIDES_EQN, 0 < d
      Since j DIV d = j' DIV d, j = j'.
   (3) same as (1), true by gcd_matches_divisor_element,
   (4) d divides n /\ x IN coprimes_by n d ==> ?j. j IN gcd_matches n d /\ (j DIV d = x)
       Note x IN coprimes (n DIV d)                by coprimes_by_def
        ==> 0 < x /\ x <= n DIV d /\ (coprime x (n DIV d))  by coprimes_element
        And d divides n /\ 0 < n
        ==> 0 < d /\ d <> 0                        by ZERO_DIVIDES, 0 < n
       Giving (x * d) DIV d = x                    by MULT_DIV, 0 < d
        Let j = x * d. so j DIV d = x              by above
       Then d divides j                            by divides_def
        ==> j = (j DIV d) * d                      by DIVIDES_EQN, 0 < d
       Note d divides n
        ==> n = (n DIV d) * d                      by DIVIDES_EQN, 0 < d
      Hence gcd j n
          = gcd (d * (j DIV d)) (d * (n DIV d))    by MULT_COMM
          = d * gcd (j DIV d) (n DIV d)            by GCD_COMMON_FACTOR
          = d * gcd x (n DIV d)                    by x = j DIV d
          = d * 1                                  by coprime x (n DIV d)
          = d                                      by MULT_RIGHT_1
      Since j = x * d, 0 < j                       by MULT_EQ_0, 0 < x, 0 < d
       Also x <= n DIV d
       means j DIV d <= n DIV d                    by x = j DIV d
          so (j DIV d) * d <= (n DIV d) * d        by LE_MULT_RCANCEL, d <> 0
          or             j <= n                    by above
      Hence j IN gcd_matches n d                   by gcd_matches_element
*)
val gcd_matches_bij_coprimes_by = store_thm(
  "gcd_matches_bij_coprimes_by",
  ``!n d. d divides n ==> BIJ (\j. j DIV d) (gcd_matches n d) (coprimes_by n d)``,
  rpt strip_tac >>
  Cases_on `n = 0` >| [
    `gcd_matches n d = {}` by rw[gcd_matches_0] >>
    `coprimes_by n d = {}` by rw[coprimes_by_0] >>
    rw[],
    `0 < n` by decide_tac >>
    rw[BIJ_DEF, INJ_DEF, SURJ_DEF, EQ_IMP_THM] >-
    rw[GSYM gcd_matches_divisor_element] >-
    metis_tac[gcd_matches_element_divides, gcd_matches_has_divisor, gcd_matches_element, DIVIDES_EQN] >-
    rw[GSYM gcd_matches_divisor_element] >>
    `0 < x /\ x <= n DIV d /\ (coprime x (n DIV d))` by metis_tac[coprimes_by_def, coprimes_element] >>
    `0 < d /\ d <> 0` by metis_tac[ZERO_DIVIDES, NOT_ZERO] >>
    `(x * d) DIV d = x` by rw[MULT_DIV] >>
    qabbrev_tac `j = x * d` >>
    `d divides j` by metis_tac[divides_def] >>
    `(n = (n DIV d) * d) /\ (j = (j DIV d) * d)` by rw[GSYM DIVIDES_EQN] >>
    `gcd j n = d` by metis_tac[GCD_COMMON_FACTOR, MULT_COMM, MULT_RIGHT_1] >>
    `0 < j` by metis_tac[MULT_EQ_0, NOT_ZERO] >>
    `j <= n` by metis_tac[LE_MULT_RCANCEL] >>
    metis_tac[gcd_matches_element]
  ]);

(* Theorem: 0 < n /\ d divides n ==> BIJ (\j. j DIV d) (gcd_matches n d) (coprimes (n DIV d)) *)
(* Proof: by gcd_matches_bij_coprimes_by, coprimes_by_by_divisor *)
val gcd_matches_bij_coprimes = store_thm(
  "gcd_matches_bij_coprimes",
  ``!n d. 0 < n /\ d divides n ==> BIJ (\j. j DIV d) (gcd_matches n d) (coprimes (n DIV d))``,
  metis_tac[gcd_matches_bij_coprimes_by, coprimes_by_by_divisor]);

(* Note: it is not useful to show:
         CARD o (gcd_matches n) = CARD o coprimes,
   as FUN_EQ_THM will demand:  CARD (gcd_matches n x) = CARD (coprimes x),
   which is not possible.
*)

(* Theorem: divisors n = IMAGE (gcd n) (natural n) *)
(* Proof:
     divisors n
   = {d | 0 < d /\ d <= n /\ d divides n}       by divisors_def
   = {d | d IN (natural n) /\ d divides n}      by natural_element
   = {d | d IN (natural n) /\ (gcd d n = d)}    by divides_iff_gcd_fix
   = {d | d IN (natural n) /\ (gcd n d = d)}    by GCD_SYM
   = {gcd n d | d | d IN (natural n)}           by replacemnt
   = IMAGE (gcd n) (natural n)                  by IMAGE_DEF
   The replacemnt requires:
       d IN (natural n) ==> gcd n d IN (natural n)
       d IN (natural n) ==> gcd n (gcd n d) = gcd n d
   which are given below.

   Or, by divisors_def, natuarl_elemnt, IN_IMAGE, this is to show:
   (1) 0 < x /\ x <= n /\ x divides n ==> ?y. (x = gcd n y) /\ 0 < y /\ y <= n
       Note x divides n ==> gcd x n = x         by divides_iff_gcd_fix
         or                 gcd n x = x         by GCD_SYM
       Take this x, and the result follows.
   (2) 0 < y /\ y <= n ==> 0 < gcd n y /\ gcd n y <= n /\ gcd n y divides n
       Note 0 < n                               by arithmetic
        and gcd n y divides n                   by GCD_IS_GREATEST_COMMON_DIVISOR, 0 < n
        and 0 < gcd n y                         by GCD_EQ_0, n <> 0
        and gcd n y <= n                        by DIVIDES_LE, 0 < n
*)
Theorem divisors_eq_gcd_image:
  !n. divisors n = IMAGE (gcd n) (natural n)
Proof
  rw_tac std_ss[divisors_def, GSPECIFICATION, EXTENSION, IN_IMAGE, natural_element, EQ_IMP_THM] >| [
    `0 < n` by decide_tac >>
    metis_tac[divides_iff_gcd_fix, GCD_SYM],
    metis_tac[GCD_EQ_0, NOT_ZERO],
    `0 < n` by decide_tac >>
    metis_tac[GCD_IS_GREATEST_COMMON_DIVISOR, DIVIDES_LE],
    metis_tac[GCD_IS_GREATEST_COMMON_DIVISOR]
  ]
QED

(* Theorem: feq_class (gcd n) (natural n) d = gcd_matches n d *)
(* Proof:
     feq_class (gcd n) (natural n) d
   = {x | x IN natural n /\ (gcd n x = d)}   by feq_class_def
   = {j | j IN natural n /\ (gcd j n = d)}   by GCD_SYM
   = gcd_matches n d                         by gcd_matches_def
*)
val gcd_eq_equiv_class = store_thm(
  "gcd_eq_equiv_class",
  ``!n d. feq_class (gcd n) (natural n) d = gcd_matches n d``,
  rewrite_tac[gcd_matches_def] >>
  rw[EXTENSION, GCD_SYM, in_preimage]);

(* Theorem: feq_class (gcd n) (natural n) = gcd_matches n *)
(* Proof: by FUN_EQ_THM, gcd_eq_equiv_class *)
val gcd_eq_equiv_class_fun = store_thm(
  "gcd_eq_equiv_class_fun",
  ``!n. feq_class (gcd n) (natural n) = gcd_matches n``,
  rw[FUN_EQ_THM, gcd_eq_equiv_class]);

(* Theorem: partition (feq (gcd n)) (natural n) = IMAGE (gcd_matches n) (divisors n) *)
(* Proof:
     partition (feq (gcd n)) (natural n)
   = IMAGE (equiv_class (feq (gcd n)) (natural n)) (natural n)      by partition_elements
   = IMAGE ((feq_class (gcd n) (natural n)) o (gcd n)) (natural n)  by feq_class_fun
   = IMAGE ((gcd_matches n) o (gcd n)) (natural n)       by gcd_eq_equiv_class_fun
   = IMAGE (gcd_matches n) (IMAGE (gcd n) (natural n))   by IMAGE_COMPOSE
   = IMAGE (gcd_matches n) (divisors n)                  by divisors_eq_gcd_image, 0 < n
*)
Theorem gcd_eq_partition_by_divisors:
  !n. partition (feq (gcd n)) (natural n) = IMAGE (gcd_matches n) (divisors n)
Proof
  rpt strip_tac >>
  qabbrev_tac `f = gcd n` >>
  qabbrev_tac `s = natural n` >>
  `partition (feq f) s = IMAGE (equiv_class (feq f) s) s` by rw[partition_elements] >>
  `_ = IMAGE ((feq_class f s) o f) s` by rw[feq_class_fun] >>
  `_ = IMAGE ((gcd_matches n) o f) s` by rw[gcd_eq_equiv_class_fun, Abbr`f`, Abbr`s`] >>
  `_ = IMAGE (gcd_matches n) (IMAGE f s)` by rw[IMAGE_COMPOSE] >>
  `_ = IMAGE (gcd_matches n) (divisors n)` by rw[divisors_eq_gcd_image, Abbr`f`, Abbr`s`] >>
  simp[]
QED

(* Theorem: (feq (gcd n)) equiv_on (natural n) *)
(* Proof:
   By feq_equiv |- !s f. feq f equiv_on s
   Taking s = upto n, f = natural n.
*)
val gcd_eq_equiv_on_natural = store_thm(
  "gcd_eq_equiv_on_natural",
  ``!n. (feq (gcd n)) equiv_on (natural n)``,
  rw[feq_equiv]);

(* Theorem: SIGMA f (natural n) = SIGMA (SIGMA f) (partition (feq (gcd n)) (natural n)) *)
(* Proof:
   Let g = gcd n, s = natural n.
   Since FINITE s               by natural_finite
     and (feq g) equiv_on s     by feq_equiv
   The result follows           by set_sigma_by_partition
*)
val sum_over_natural_by_gcd_partition = store_thm(
  "sum_over_natural_by_gcd_partition",
  ``!f n. SIGMA f (natural n) = SIGMA (SIGMA f) (partition (feq (gcd n)) (natural n))``,
  rw[feq_equiv, natural_finite, set_sigma_by_partition]);

(* Theorem: SIGMA f (natural n) = SIGMA (SIGMA f) (IMAGE (gcd_matches n) (divisors n)) *)
(* Proof:
     SIGMA f (natural n)
   = SIGMA (SIGMA f) (partition (feq (gcd n)) (natural n)) by sum_over_natural_by_gcd_partition
   = SIGMA (SIGMA f) (IMAGE (gcd_matches n) (divisors n))  by gcd_eq_partition_by_divisors
*)
Theorem sum_over_natural_by_divisors:
  !f n. SIGMA f (natural n) = SIGMA (SIGMA f) (IMAGE (gcd_matches n) (divisors n))
Proof
  simp[sum_over_natural_by_gcd_partition, gcd_eq_partition_by_divisors]
QED

(* Theorem: INJ (gcd_matches n) (divisors n) univ(num) *)
(* Proof:
   By INJ_DEF, this is to show:
      x IN divisors n /\ y IN divisors n /\ gcd_matches n x = gcd_matches n y ==> x = y
    Note 0 < x /\ x <= n /\ x divides n        by divisors_def
    also 0 < y /\ y <= n /\ y divides n        by divisors_def
   Hence (gcd x n = x) /\ (gcd y n = y)        by divides_iff_gcd_fix
     ==> x IN gcd_matches n x                  by gcd_matches_element
      so x IN gcd_matches n y                  by gcd_matches n x = gcd_matches n y
    with gcd x n = y                           by gcd_matches_element
    Therefore y = gcd x n = x.
*)
Theorem gcd_matches_from_divisors_inj:
  !n. INJ (gcd_matches n) (divisors n) univ(:num -> bool)
Proof
  rw[INJ_DEF] >>
  fs[divisors_def] >>
  `(gcd x n = x) /\ (gcd y n = y)` by rw[GSYM divides_iff_gcd_fix] >>
  metis_tac[gcd_matches_element]
QED

(* Theorem: CARD o (gcd_matches n) = CARD o (coprimes_by n) *)
(* Proof:
   By composition and FUN_EQ_THM, this is to show:
      !x. CARD (gcd_matches n x) = CARD (coprimes_by n x)
   If x divides n,
      Then BIJ (\j. j DIV x) (gcd_matches n x) (coprimes_by n x)  by gcd_matches_bij_coprimes_by
      Also FINITE (gcd_matches n x)                               by gcd_matches_finite
       and FINITE (coprimes_by n x)                               by coprimes_by_finite
      Hence CARD (gcd_matches n x) = CARD (coprimes_by n x)       by FINITE_BIJ_CARD_EQ
   If ~(x divides n),
      If n = 0,
         then gcd_matches 0 x = {}      by gcd_matches_0
          and coprimes_by 0 x = {}      by coprimes_by_0
         Hence true.
      If n <> 0,
         then gcd_matches n x = {}      by gcd_matches_eq_empty, 0 < n
          and coprimes_by n x = {}      by coprimes_by_eq_empty, 0 < n
         Hence CARD {} = CARD {}.
*)
val gcd_matches_and_coprimes_by_same_size = store_thm(
  "gcd_matches_and_coprimes_by_same_size",
  ``!n. CARD o (gcd_matches n) = CARD o (coprimes_by n)``,
  rw[FUN_EQ_THM] >>
  Cases_on `x divides n` >| [
    `BIJ (\j. j DIV x) (gcd_matches n x) (coprimes_by n x)` by rw[gcd_matches_bij_coprimes_by] >>
    `FINITE (gcd_matches n x)` by rw[gcd_matches_finite] >>
    `FINITE (coprimes_by n x)` by rw[coprimes_by_finite] >>
    metis_tac[FINITE_BIJ_CARD_EQ],
    Cases_on `n = 0` >-
    rw[gcd_matches_0, coprimes_by_0] >>
    `gcd_matches n x = {}` by rw[gcd_matches_eq_empty] >>
    `coprimes_by n x = {}` by rw[coprimes_by_eq_empty] >>
    rw[]
  ]);

(* Theorem: 0 < n ==> (CARD o (coprimes_by n) = \d. phi (if d IN (divisors n) then n DIV d else 0)) *)
(* Proof:
   By FUN_EQ_THM,
      CARD o (coprimes_by n) x
    = CARD (coprimes_by n x)       by composition, combinTheory.o_THM
    = CARD (if x divides n then coprimes (n DIV x) else {})    by coprimes_by_def, 0 < n
    If x divides n,
       then x <= n                 by DIVIDES_LE
        and 0 < x                  by divisor_pos, 0 < n
         so x IN (divisors n)      by divisors_element
       CARD o (coprimes_by n) x
     = CARD (coprimes (n DIV x))
     = phi (n DIV x)               by phi_def
    If ~(x divides n),
       x NOTIN (divisors n)        by divisors_element
       CARD o (coprimes_by n) x
     = CARD {}
     = 0                           by CARD_EMPTY
     = phi 0                       by phi_0
    Hence the same function as:
    \d. phi (if d IN (divisors n) then n DIV d else 0)
*)
Theorem coprimes_by_with_card:
  !n. 0 < n ==> (CARD o (coprimes_by n) = \d. phi (if d IN (divisors n) then n DIV d else 0))
Proof
  rw[coprimes_by_def, phi_def, divisors_def, FUN_EQ_THM] >>
  metis_tac[DIVIDES_LE, divisor_pos, coprimes_0]
QED

(* Theorem: x IN (divisors n) ==> (CARD o (coprimes_by n)) x = (\d. phi (n DIV d)) x *)
(* Proof:
   Since x IN (divisors n) ==> x divides n     by divisors_element
       CARD o (coprimes_by n) x
     = CARD (coprimes (n DIV x))               by coprimes_by_def
     = phi (n DIV x)                           by phi_def
*)
Theorem coprimes_by_divisors_card:
  !n x. x IN (divisors n) ==> (CARD o (coprimes_by n)) x = (\d. phi (n DIV d)) x
Proof
  rw[coprimes_by_def, phi_def, divisors_def]
QED

(*
SUM_IMAGE_CONG |- (s1 = s2) /\ (!x. x IN s2 ==> (f1 x = f2 x)) ==> (SIGMA f1 s1 = SIGMA f2 s2)
*)

(* Theorem: SIGMA phi (divisors n) = n *)
(* Proof:
   Note INJ (gcd_matches n) (divisors n) univ(:num -> bool)  by gcd_matches_from_divisors_inj
    and (\d. n DIV d) PERMUTES (divisors n)              by divisors_divisors_bij
   n = CARD (natural n)                                  by natural_card
     = SIGMA CARD (partition (feq (gcd n)) (natural n))  by partition_CARD
     = SIGMA CARD (IMAGE (gcd_matches n) (divisors n))   by gcd_eq_partition_by_divisors
     = SIGMA (CARD o (gcd_matches n)) (divisors n)       by sum_image_by_composition
     = SIGMA (CARD o (coprimes_by n)) (divisors n)       by gcd_matches_and_coprimes_by_same_size
     = SIGMA (\d. phi (n DIV d)) (divisors n)            by SUM_IMAGE_CONG, coprimes_by_divisors_card
     = SIGMA phi (divisors n)                            by sum_image_by_permutation
*)
Theorem Gauss_little_thm:
  !n. SIGMA phi (divisors n) = n
Proof
  rpt strip_tac >>
  `FINITE (natural n)` by rw[natural_finite] >>
  `(feq (gcd n)) equiv_on (natural n)` by rw[gcd_eq_equiv_on_natural] >>
  `INJ (gcd_matches n) (divisors n) univ(:num -> bool)` by rw[gcd_matches_from_divisors_inj] >>
  `(\d. n DIV d) PERMUTES (divisors n)` by rw[divisors_divisors_bij] >>
  `FINITE (divisors n)` by rw[divisors_finite] >>
  `n = CARD (natural n)` by rw[natural_card] >>
  `_ = SIGMA CARD (partition (feq (gcd n)) (natural n))` by rw[partition_CARD] >>
  `_ = SIGMA CARD (IMAGE (gcd_matches n) (divisors n))` by rw[gcd_eq_partition_by_divisors] >>
  `_ = SIGMA (CARD o (gcd_matches n)) (divisors n)` by prove_tac[sum_image_by_composition] >>
  `_ = SIGMA (CARD o (coprimes_by n)) (divisors n)` by rw[gcd_matches_and_coprimes_by_same_size] >>
  `_ = SIGMA (\d. phi (n DIV d)) (divisors n)` by rw[SUM_IMAGE_CONG, coprimes_by_divisors_card] >>
  `_ = SIGMA phi (divisors n)` by metis_tac[sum_image_by_permutation] >>
  decide_tac
QED

(* This is a milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* Euler phi function is multiplicative for coprimes.                        *)
(* ------------------------------------------------------------------------- *)

(*
EVAL ``coprimes 2``; = {1}
EVAL ``coprimes 3``; = {2; 1}
EVAL ``coprimes 6``; = {5; 1}

Let phi(n) = the set of remainders coprime to n and not exceeding n.
Then phi(2) = {1}, phi(3) = {1,2}
We shall show phi(6) = {z = (3 * x + 2 * y) mod 6 | x IN phi(2), y IN phi(3)}.
(1,1) corresponds to z = (3 * 1 + 2 * 1) mod 6 = 5, right!
(1,2) corresponds to z = (3 * 1 + 2 * 2) mod 6 = 1, right!
*)

(* Idea: give an expression for coprimes (m * n). *)

(* Theorem: coprime m n ==>
            coprimes (m * n) =
            IMAGE (\(x,y). if (m * n = 1) then 1 else (x * n + y * m) MOD (m * n))
                  ((coprimes m) CROSS (coprimes n)) *)
(* Proof:
   Let f = \(x,y). if (m * n = 1) then 1 else (x * n + y * m) MOD (m * n).
   If m = 0 or n = 0,
      When m = 0, to show:
           coprimes 0 = IMAGE f ((coprimes 0) CROSS (coprimes n))
           RHS
         = IMAGE f ({} CROSS (coprimes n))     by coprimes_0
         = IMAGE f {}                          by CROSS_EMPTY
         = {}                                  by IMAGE_EMPTY
         = LHS                                 by coprimes_0
      When n = 0, to show:
           coprimes 0 = IMAGE f ((coprimes m) CROSS (coprimes 0))
           RHS
         = IMAGE f ((coprimes n) CROSS {})     by coprimes_0
         = IMAGE f {}                          by CROSS_EMPTY
         = {}                                  by IMAGE_EMPTY
         = LHS                                 by coprimes_0

   If m = 1, or n = 1,
      When m = 1, to show:
           coprimes n = IMAGE f ((coprimes 1) CROSS (coprimes n))
           RHS
         = IMAGE f ({1} CROSS (coprimes n))    by coprimes_1
         = IMAGE f {(1,y) | y IN coprimes n}   by IN_CROSS
         = {if n = 1 then 1 else (n + y) MOD n | y IN coprimes n}
                                               by IN_IMAGE
         = {1} if n = 1, or {y MOD n | y IN coprimes n} if 1 < n
         = {1} if n = 1, or {y | y IN coprimes n} if 1 < n
                                               by coprimes_element_alt, LESS_MOD, y < n
         = LHS                                 by coprimes_1
      When n = 1, to show:
           coprimes m = IMAGE f ((coprimes m) CROSS (coprimes 1))
           RHS
         = IMAGE f ((coprimes m) CROSS {1})    by coprimes_1
         = IMAGE f {(x,1) | x IN coprimes m}   by IN_CROSS
         = {if m = 1 then 1 else (x + m) MOD m | x IN coprimes m}
                                               by IN_IMAGE
         = {1} if m = 1, or {x MOD m | x IN coprimes m} if 1 < m
         = {1} if m = 1, or {x | x IN coprimes m} if 1 < m
                                               by coprimes_element_alt, LESS_MOD, x < m
         = LHS                                 by coprimes_1

   Now, 1 < m, 1 < n, and 0 < m, 0 < n.
   Therefore 1 < m * n, and 0 < m * n.         by MULT_EQ_1, MULT_EQ_0
   and function f = \(x,y). (x * n + y * m) MOD (m * n).
   If part: z IN coprimes (m * n) ==>
            ?x y. z = (x * n + y * m) MOD (m * n) /\ x IN coprimes m /\ y IN coprimes n
      Note z < m * n /\ coprime z (m * n)      by coprimes_element_alt, 1 < m * n
       for x < m /\ coprime x m, and y < n /\ coprime y n
                                               by coprimes_element_alt, 1 < m, 1 < n
       Now ?p q. (p * m + q * n) MOD (m * n)
               = z MOD (m * n)                 by coprime_multiple_linear_mod_prod
               = z                             by LESS_MOD, z < m * n
      Note ?h x. p = h * n + x /\ x < n        by DA, 0 < n
       and ?k y. q = k * m + y /\ y < m        by DA, 0 < m
           z
         = (p * m + q * n) MOD (m * n)         by above
         = (h * n * m + x * m + k * m * n + y * n) MOD (m * n)
         = ((x * m + y * n) + (h + k) * (m * n)) MOD (m * n)
         = (x * m + y * n) MOD (m * n)         by MOD_PLUS2, MOD_EQ_0
      Take these x and y, but need to show:
      (1) coprime x n
          Let g = gcd x n,
          Then g divides x /\ g divides n      by GCD_PROPERTY
            so g divides (m * n)               by DIVIDES_MULTIPLE
            so g divides z                     by divides_linear, mod_divides_divides
           ==> g = 1, or coprime x n           by coprime_common_factor
      (2) coprime y m
          Let g = gcd y m,
          Then g divides y /\ g divides m      by GCD_PROPERTY
            so g divides (m * n)               by DIVIDES_MULTIPLE
            so g divides z                     by divides_linear, mod_divides_divides
           ==> g = 1, or coprime y m           by coprime_common_factor

   Only-if part: coprime m n /\ x IN coprimes m /\ y IN coprimes n ==>
                 (x * n + y * m) MOD (m * n) IN coprimes (m * n)
       Note x < m /\ coprime x m               by coprimes_element_alt, 1 < m
        and y < n /\ coprime y n               by coprimes_element_alt, 1 < n
       Let z = x * m + y * n.
       Then coprime z (m * n)                  by coprime_linear_mult
         so coprime (z MOD (m * n)) (m * n)    by GCD_MOD_COMM
        and z MOD (m * n) < m * n              by MOD_LESS, 0 < m * n
*)
Theorem coprimes_mult_by_image:
  !m n. coprime m n ==>
        coprimes (m * n) =
        IMAGE (\(x,y). if (m * n = 1) then 1 else (x * n + y * m) MOD (m * n))
              ((coprimes m) CROSS (coprimes n))
Proof
  rpt strip_tac >>
  Cases_on `m = 0 \/ n = 0` >-
  fs[coprimes_0] >>
  Cases_on `m = 1 \/ n = 1` >| [
    fs[coprimes_1] >| [
      rw[EXTENSION, pairTheory.EXISTS_PROD] >>
      Cases_on `n = 1` >-
      simp[coprimes_1] >>
      fs[coprimes_element_alt] >>
      metis_tac[LESS_MOD],
      rw[EXTENSION, pairTheory.EXISTS_PROD] >>
      Cases_on `m = 1` >-
      simp[coprimes_1] >>
      fs[coprimes_element_alt] >>
      metis_tac[LESS_MOD]
    ],
    `m * n <> 0 /\ m * n <> 1` by rw[] >>
    `1 < m /\ 1 < n /\ 1 < m * n` by decide_tac >>
    rw[EXTENSION, pairTheory.EXISTS_PROD] >>
    rw[EQ_IMP_THM] >| [
      rfs[coprimes_element_alt] >>
      `1 < m /\ 1 < n /\ 0 < m /\ 0 < n /\ 0 < m * n` by decide_tac >>
      `?p q. (p * m + q * n) MOD (m * n) = x MOD (m * n)` by rw[coprime_multiple_linear_mod_prod] >>
      `?h u. p = h * n + u /\ u < n` by metis_tac[DA] >>
      `?k v. q = k * m + v /\ v < m` by metis_tac[DA] >>
      `p * m + q * n = h * n * m + u * m + k * m * n + v * n` by simp[] >>
      `_ = (u * m + v * n) + (h + k) * (m * n)` by simp[] >>
      `(u * m + v * n) MOD (m * n) = x MOD (m * n)` by metis_tac[MOD_PLUS2, MOD_EQ_0, ADD_0] >>
      `_ = x` by rw[] >>
      `coprime u n` by
  (qabbrev_tac `g = gcd u n` >>
      `0 < g` by rw[GCD_POS, Abbr`g`] >>
      `g divides u /\ g divides n` by metis_tac[GCD_PROPERTY] >>
      `g divides (m * n)` by rw[DIVIDES_MULTIPLE] >>
      `g divides x` by metis_tac[divides_linear, MULT_COMM, mod_divides_divides] >>
      metis_tac[coprime_common_factor]) >>
      `coprime v m` by
    (qabbrev_tac `g = gcd v m` >>
      `0 < g` by rw[GCD_POS, Abbr`g`] >>
      `g divides v /\ g divides m` by metis_tac[GCD_PROPERTY] >>
      `g divides (m * n)` by metis_tac[DIVIDES_MULTIPLE, MULT_COMM] >>
      `g divides x` by metis_tac[divides_linear, MULT_COMM, mod_divides_divides] >>
      metis_tac[coprime_common_factor]) >>
      metis_tac[MULT_COMM],
      rfs[coprimes_element_alt] >>
      `0 < m * n` by decide_tac >>
      `coprime (m * p_2 + n * p_1) (m * n)` by metis_tac[coprime_linear_mult, MULT_COMM] >>
      metis_tac[GCD_MOD_COMM]
    ]
  ]
QED

(* Yes! a milestone theorem. *)

(* Idea: in coprimes (m * n), the image map is injective. *)

(* Theorem: coprime m n ==>
            INJ (\(x,y). if (m * n = 1) then 1 else (x * n + y * m) MOD (m * n))
                ((coprimes m) CROSS (coprimes n)) univ(:num) *)
(* Proof:
   Let f = \(x,y). if m * n = 1 then 1 else (x * n + y * m) MOD (m * n).
   To show: coprime m n ==> INJ f ((coprimes m) CROSS (coprimes n)) univ(:num)
   If m = 0, or n = 0,
      When m = 0,
           INJ f ((coprimes 0) CROSS (coprimes n)) univ(:num)
       <=> INJ f ({} CROSS (coprimes n)) univ(:num)      by coprimes_0
       <=> INJ f {} univ(:num)                           by CROSS_EMPTY
       <=> T                                             by INJ_EMPTY
      When n = 0,
           INJ f ((coprimes m) CROSS (coprimes 0)) univ(:num)
       <=> INJ f ((coprimes m) CROSS {}) univ(:num)      by coprimes_0
       <=> INJ f {} univ(:num)                           by CROSS_EMPTY
       <=> T                                             by INJ_EMPTY

   If m = 1, or n = 1,
      When m = 1,
           INJ f ((coprimes 1) CROSS (coprimes n)) univ(:num)
       <=> INJ f ({1} CROSS (coprimes n)) univ(:num)     by coprimes_1
       If n = 1, this is
           INJ f ({1} CROSS {1}) univ(:num)              by coprimes_1
       <=> INJ f {(1,1)} univ(:num)                      by CROSS_SINGS
       <=> T                                             by INJ_DEF
       If n <> 1, this is by INJ_DEF:
       to show: !p q. p IN coprimes n /\ q IN coprimes n ==> p MOD n = q MOD n ==> p = q
       Now p < n /\ q < n                                by coprimes_element_alt, 1 < n
       With p MOD n = q MOD n, so p = q                  by LESS_MOD
      When n = 1,
           INJ f ((coprimes m) CROSS (coprimes 1)) univ(:num)
       <=> INJ f ((coprimes m) CROSS {1}) univ(:num)     by coprimes_1
       If m = 1, this is
           INJ f ({1} CROSS {1}) univ(:num)              by coprimes_1
       <=> INJ f {(1,1)} univ(:num)                      by CROSS_SINGS
       <=> T                                             by INJ_DEF
       If m <> 1, this is by INJ_DEF:
       to show: !p q. p IN coprimes m /\ q IN coprimes m ==> p MOD m = q MOD m ==> p = q
       Now p < m /\ q < m                                by coprimes_element_alt, 1 < m
       With p MOD m = q MOD m, so p = q                  by LESS_MOD

   Now 1 < m and 1 < n, so 1 < m * n           by MULT_EQ_1, MULT_EQ_0
   By INJ_DEF, coprimes_element_alt, this is to show:
      !x y u v. x < m /\ coprime x m /\ y < n /\ coprime y n /\
                u < m /\ coprime u m /\ v < n /\ coprime v n /\
                (x * n + y * m) MOD (m * n) = (u * n + v * m) MOD (m * n)
            ==> x = u /\ y = v
   Note x * n < n * m                          by LT_MULT_RCANCEL, 0 < n, x < m
    and v * m < n * m                          by LT_MULT_RCANCEL, 0 < m, v < n
   Thus (y * m + (n * m - v * m)) MOD (n * m)
      = (u * n + (n * m - x * n)) MOD (n * m)      by mod_add_eq_sub
    Now y * m + (n * m - v * m) = m * (n + y - v)  by arithmetic
    and u * n + (n * m - x * n) = n * (m + u - x)  by arithmetic
    and 0 < n + y - v /\ n + y - v < 2 * n         by y < n, v < n
    and 0 < m + u - x /\ m + u - x < 2 * m         by x < m, u < m
    ==> n + y - v = n /\ m + u - x = m             by mod_mult_eq_mult
    ==> n + y = n + v /\ m + u = m + x             by arithmetic
    ==> y = v /\ x = u                             by EQ_ADD_LCANCEL
*)
Theorem coprimes_map_cross_inj:
  !m n. coprime m n ==>
        INJ (\(x,y). if (m * n = 1) then 1 else (x * n + y * m) MOD (m * n))
            ((coprimes m) CROSS (coprimes n)) univ(:num)
Proof
  rpt strip_tac >>
  qabbrev_tac `f = \(x,y). if m * n = 1 then 1 else (x * n + y * m) MOD (m * n)` >>
  Cases_on `m = 0 \/ n = 0` >-
  fs[coprimes_0] >>
  Cases_on `m = 1 \/ n = 1` >| [
    fs[coprimes_1, INJ_DEF, pairTheory.FORALL_PROD, Abbr`f`] >| [
      (Cases_on `n = 1` >> simp[coprimes_1]) >>
      fs[coprimes_element_alt],
      (Cases_on `m = 1` >> simp[coprimes_1]) >>
      fs[coprimes_element_alt]
    ],
    `m * n <> 0 /\ m * n <> 1` by rw[] >>
    `1 < m /\ 1 < n /\ 1 < m * n` by decide_tac >>
    simp[INJ_DEF, pairTheory.FORALL_PROD] >>
    ntac 6 strip_tac >>
    rfs[coprimes_element_alt, Abbr`f`] >>
    `0 < m /\ 0 < n /\ 0 < m * n` by decide_tac >>
    `n * p_1 < n * m /\ m * p_2' < n * m` by simp[] >>
    `(m * p_2 + (n * m - m * p_2')) MOD (n * m) =
    (n * p_1' + (n * m - n * p_1)) MOD (n * m)` by simp[GSYM mod_add_eq_sub] >>
    `m * p_2 + (n * m - m * p_2') = m * (n + p_2 - p_2')` by decide_tac >>
    `n * p_1' + (n * m - n * p_1) = n * (m + p_1' - p_1)` by decide_tac >>
    `0 < n + p_2 - p_2' /\ n + p_2 - p_2' < 2 * n` by decide_tac >>
    `0 < m + p_1' - p_1 /\ m + p_1' - p_1 < 2 * m` by decide_tac >>
    `n + p_2 - p_2' = n /\ m + p_1' - p_1 = m` by metis_tac[mod_mult_eq_mult, MULT_COMM] >>
    simp[]
  ]
QED

(* Another milestone theorem! *)

(* Idea: Euler phi function is multiplicative for coprimes. *)

(* Theorem: coprime m n ==> phi (m * n) = phi m * phi n *)
(* Proof:
   Let f = \(x,y). if m * n = 1 then 1 else (x * n + y * m) MOD (m * n),
       u = coprimes m,
       v = coprimes n.
   Then coprimes (m * n) = IMAGE f (u CROSS v) by coprimes_mult_by_image
    and INJ f (u CROSS v) univ(:num)           by coprimes_map_cross_inj
   Note FINITE u /\ FINITE v                   by coprimes_finite
     so FINITE (u CROSS v)                     by FINITE_CROSS
        phi (m * n)
      = CARD (coprimes (m * n))                by phi_def
      = CARD (IMAGE f (u CROSS v))             by above
      = CARD (u CROSS v)                       by INJ_CARD_IMAGE
      = (CARD u) * (CARD v)                    by CARD_CROSS
      = phi m * phi n                          by phi_def
*)
Theorem phi_mult:
  !m n. coprime m n ==> phi (m * n) = phi m * phi n
Proof
  rw[phi_def] >>
  imp_res_tac coprimes_mult_by_image >>
  imp_res_tac coprimes_map_cross_inj >>
  qabbrev_tac `f = \(x,y). if m * n = 1 then 1 else (x * n + y * m) MOD (m * n)` >>
  qabbrev_tac `u = coprimes m` >>
  qabbrev_tac `v = coprimes n` >>
  `FINITE u /\ FINITE v` by rw[coprimes_finite, Abbr`u`, Abbr`v`] >>
  `FINITE (u CROSS v)` by rw[] >>
  metis_tac[INJ_CARD_IMAGE, CARD_CROSS]
QED

(* This is the ultimate goal! *)

(* Idea: an expression for phi (p * q) with distinct primes p and q. *)

(* Theorem: prime p /\ prime q /\ p <> q ==> phi (p * q) = (p - 1) * (q - 1) *)
(* Proof:
   Note coprime p q        by primes_coprime
        phi (p * q)
      = phi p * phi q      by phi_mult
      = (p - 1) * (q - 1)  by phi_prime
*)
Theorem phi_primes_distinct:
  !p q. prime p /\ prime q /\ p <> q ==> phi (p * q) = (p - 1) * (q - 1)
Proof
  simp[primes_coprime, phi_mult, phi_prime]
QED

(* ------------------------------------------------------------------------- *)
(* Euler phi function for prime powers.                                      *)
(* ------------------------------------------------------------------------- *)

(*
EVAL ``coprimes 9``; = {8; 7; 5; 4; 2; 1}
EVAL ``divisors 9``; = {9; 3; 1}
EVAL ``IMAGE (\x. 3 * x) (natural 3)``; = {9; 6; 3}
EVAL ``IMAGE (\x. 3 * x) (natural 9)``; = {27; 24; 21; 18; 15; 12; 9; 6; 3}

> EVAL ``IMAGE ($* 3) (natural (8 DIV 3))``; = {6; 3}
> EVAL ``IMAGE ($* 3) (natural (9 DIV 3))``; = {9; 6; 3}
> EVAL ``IMAGE ($* 3) (natural (10 DIV 3))``; = {9; 6; 3}
> EVAL ``IMAGE ($* 3) (natural (12 DIV 3))``; = {12; 9; 6; 3}
*)

(* Idea: develop a special set in anticipation for counting. *)

(* Define the set of positive multiples of m, up to n *)
val multiples_upto_def = zDefine`
    multiples_upto m n = {x | m divides x /\ 0 < x /\ x <= n}
`;
(* use zDefine as this is not effective for evalutaion. *)
(* make this an infix operator *)
val _ = set_fixity "multiples_upto" (Infix(NONASSOC, 550)); (* higher than arithmetic op 500. *)

(*
> multiples_upto_def;
val it = |- !m n. m multiples_upto n = {x | m divides x /\ 0 < x /\ x <= n}: thm
*)

(* Theorem: x IN m multiples_upto n <=> m divides x /\ 0 < x /\ x <= n *)
(* Proof: by multiples_upto_def. *)
Theorem multiples_upto_element:
  !m n x. x IN m multiples_upto n <=> m divides x /\ 0 < x /\ x <= n
Proof
  simp[multiples_upto_def]
QED

(* Theorem: m multiples_upto n = {x | ?k. x = k * m /\ 0 < x /\ x <= n} *)
(* Proof:
     m multiples_upto n
   = {x | m divides x /\ 0 < x /\ x <= n}      by multiples_upto_def
   = {x | ?k. x = k * m /\ 0 < x /\ x <= n}    by divides_def
*)
Theorem multiples_upto_alt:
  !m n. m multiples_upto n = {x | ?k. x = k * m /\ 0 < x /\ x <= n}
Proof
  rw[multiples_upto_def, EXTENSION] >>
  metis_tac[divides_def]
QED

(* Theorem: x IN m multiples_upto n <=> ?k. x = k * m /\ 0 < x /\ x <= n *)
(* Proof: by multiples_upto_alt. *)
Theorem multiples_upto_element_alt:
  !m n x. x IN m multiples_upto n <=> ?k. x = k * m /\ 0 < x /\ x <= n
Proof
  simp[multiples_upto_alt]
QED

(* Theorem: m multiples_upto n = {x | m divides x /\ x IN natural n} *)
(* Proof:
     m multiples_upto n
   = {x | m divides x /\ 0 < x /\ x <= n}      by multiples_upto_def
   = {x | m divides x /\ x IN natural n}       by natural_element
*)
Theorem multiples_upto_eqn:
  !m n. m multiples_upto n = {x | m divides x /\ x IN natural n}
Proof
  simp[multiples_upto_def, natural_element, EXTENSION]
QED

(* Theorem: 0 multiples_upto n = {} *)
(* Proof:
     0 multiples_upto n
   = {x | 0 divides x /\ 0 < x /\ x <= n}      by multiples_upto_def
   = {x | x = 0 /\ 0 < x /\ x <= n}            by ZERO_DIVIDES
   = {}                                        by contradiction
*)
Theorem multiples_upto_0_n:
  !n. 0 multiples_upto n = {}
Proof
  simp[multiples_upto_def, EXTENSION]
QED

(* Theorem: 1 multiples_upto n = natural n *)
(* Proof:
     1 multiples_upto n
   = {x | 1 divides x /\ x IN natural n}       by multiples_upto_eqn
   = {x | T /\ x IN natural n}                 by ONE_DIVIDES_ALL
   = natural n                                 by EXTENSION
*)
Theorem multiples_upto_1_n:
  !n. 1 multiples_upto n = natural n
Proof
  simp[multiples_upto_eqn, EXTENSION]
QED

(* Theorem: m multiples_upto 0 = {} *)
(* Proof:
     m multiples_upto 0
   = {x | m divides x /\ 0 < x /\ x <= 0}      by multiples_upto_def
   = {x | m divides x /\ F}                    by arithmetic
   = {}                                        by contradiction
*)
Theorem multiples_upto_m_0:
  !m. m multiples_upto 0 = {}
Proof
  simp[multiples_upto_def, EXTENSION]
QED

(* Theorem: m multiples_upto 1 = if m = 1 then {1} else {} *)
(* Proof:
     m multiples_upto 1
   = {x | m divides x /\ 0 < x /\ x <= 1}      by multiples_upto_def
   = {x | m divides x /\ x = 1}                by arithmetic
   = {1} if m = 1, {} otherwise                by DIVIDES_ONE
*)
Theorem multiples_upto_m_1:
  !m. m multiples_upto 1 = if m = 1 then {1} else {}
Proof
  rw[multiples_upto_def, EXTENSION] >>
  spose_not_then strip_assume_tac >>
  `x = 1` by decide_tac >>
  fs[]
QED

(* Idea: an expression for (m multiples_upto n), for direct evaluation. *)

(* Theorem: m multiples_upto n =
            if m = 0 then {}
            else IMAGE ($* m) (natural (n DIV m)) *)
(* Proof:
   If m = 0,
      Then 0 multiples_upto n = {} by multiples_upto_0_n
   If m <> 0.
      By multiples_upto_alt, EXTENSION, this is to show:
      (1) 0 < k * m /\ k * m <= n ==>
          ?y. k * m = m * y /\ ?x. y = SUC x /\ x < n DIV m
          Note k <> 0              by MULT_EQ_0
           and k <= n DIV m        by X_LE_DIV, 0 < m
            so k - 1 < n DIV m     by arithmetic
          Let y = k, x = k - 1.
          Note SUC x = SUC (k - 1) = k = y.
      (2) x < n DIV m ==> ?k. m * SUC x = k * m /\ 0 < m * SUC x /\ m * SUC x <= n
          Note SUC x <= n DIV m    by arithmetic
            so m * SUC x <= n      by X_LE_DIV, 0 < m
           and 0 < m * SUC x       by MULT_EQ_0
          Take k = SUC x, true     by MULT_COMM
*)
Theorem multiples_upto_thm[compute]:
  !m n. m multiples_upto n =
        if m = 0 then {}
        else IMAGE ($* m) (natural (n DIV m))
Proof
  rpt strip_tac >>
  Cases_on `m = 0` >-
  fs[multiples_upto_0_n] >>
  fs[multiples_upto_alt, EXTENSION] >>
  rw[EQ_IMP_THM] >| [
    qexists_tac `k` >>
    simp[] >>
    `0 < k /\ 0 < m` by metis_tac[MULT_EQ_0, NOT_ZERO] >>
    `k <= n DIV m` by rw[X_LE_DIV] >>
    `k - 1 < n DIV m` by decide_tac >>
    qexists_tac `k - 1` >>
    simp[],
    `SUC x'' <= n DIV m` by decide_tac >>
    `m * SUC x'' <= n` by rfs[X_LE_DIV] >>
    simp[] >>
    metis_tac[MULT_COMM]
  ]
QED

(*
EVAL ``3 multiples_upto 9``; = {9; 6; 3}
EVAL ``3 multiples_upto 11``; = {9; 6; 3}
EVAL ``3 multiples_upto 12``; = {12; 9; 6; 3}
EVAL ``3 multiples_upto 13``; = {12; 9; 6; 3}
*)

(* Theorem: m multiples_upto n SUBSET natural n *)
(* Proof: by multiples_upto_eqn, SUBSET_DEF. *)
Theorem multiples_upto_subset:
  !m n. m multiples_upto n SUBSET natural n
Proof
  simp[multiples_upto_eqn, SUBSET_DEF]
QED

(* Theorem: FINITE (m multiples_upto n) *)
(* Proof:
   Let s = m multiples_upto n
   Note s SUBSET natural n     by multiples_upto_subset
    and FINITE natural n       by natural_finite
     so FINITE s               by SUBSET_FINITE
*)
Theorem multiples_upto_finite:
  !m n. FINITE (m multiples_upto n)
Proof
  metis_tac[multiples_upto_subset, natural_finite, SUBSET_FINITE]
QED

(* Theorem: CARD (m multiples_upto n) = if m = 0 then 0 else n DIV m *)
(* Proof:
   If m = 0,
        CARD (0 multiples_upto n)
      = CARD {}                    by multiples_upto_0_n
      = 0                          by CARD_EMPTY
   If m <> 0,
      Claim: INJ ($* m) (natural (n DIV m)) univ(:num)
      Proof: By INJ_DEF, this is to show:
             !x. x IN (natural (n DIV m)) /\
                 m * x = m * y ==> x = y, true     by EQ_MULT_LCANCEL, m <> 0
      Note FINITE (natural (n DIV m))              by natural_finite
        CARD (m multiples_upto n)
      = CARD (IMAGE ($* m) (natural (n DIV m)))    by multiples_upto_thm, m <> 0
      = CARD (natural (n DIV m))                   by INJ_CARD_IMAGE
      = n DIV m                                    by natural_card
*)
Theorem multiples_upto_card:
  !m n. CARD (m multiples_upto n) = if m = 0 then 0 else n DIV m
Proof
  rpt strip_tac >>
  Cases_on `m = 0` >-
  simp[multiples_upto_0_n] >>
  simp[multiples_upto_thm] >>
  `INJ ($* m) (natural (n DIV m)) univ(:num)` by rw[INJ_DEF] >>
  metis_tac[INJ_CARD_IMAGE, natural_finite, natural_card]
QED

(* Idea: an expression for the set of coprimes of a prime power. *)

(* Theorem: prime p ==>
            coprimes (p ** n) = natural (p ** n) DIFF p multiples_upto (p ** n) *)
(* Proof:
   If n = 0,
      LHS = coprimes (p ** 0)
          = coprimes 1             by EXP_0
          = {1}                    by coprimes_1
      RHS = natural (p ** 0) DIFF p multiples_upto (p ** 0)
          = natural 1 DIFF p multiples_upto 1
          = natural 1 DIFF {}      by multiples_upto_m_1, NOT_PRIME_1
          = {1} DIFF {}            by natural_1
          = {1} = LHS              by DIFF_EMPTY
   If n <> 0,
      By coprimes_def, multiples_upto_def, EXTENSION, this is to show:
         coprime (SUC x) (p ** n) <=> ~(p divides SUC x)
      This is true                 by coprime_prime_power
*)
Theorem coprimes_prime_power:
  !p n. prime p ==>
        coprimes (p ** n) = natural (p ** n) DIFF p multiples_upto (p ** n)
Proof
  rpt strip_tac >>
  Cases_on `n = 0` >| [
    `p <> 1` by metis_tac[NOT_PRIME_1] >>
    simp[coprimes_1, multiples_upto_m_1, natural_1, EXP_0],
    rw[coprimes_def, multiples_upto_def, EXTENSION] >>
    (rw[EQ_IMP_THM] >> rfs[coprime_prime_power])
  ]
QED

(* Idea: an expression for phi of a prime power. *)

(* Theorem: prime p ==> phi (p ** SUC n) = (p - 1) * p ** n *)
(* Proof:
   Let m = SUC n,
       u = natural (p ** m),
       v = p multiples_upto (p ** m).
   Note 0 < p                      by PRIME_POS
    and FINITE u                   by natural_finite
    and v SUBSET u                 by multiples_upto_subset

     phi (p ** m)
   = CARD (coprimes (p ** m))      by phi_def
   = CARD (u DIFF v)               by coprimes_prime_power
   = CARD u - CARD v               by SUBSET_DIFF_CARD
   = p ** m - CARD v               by natural_card
   = p ** m - (p ** m DIV p)       by multiples_upto_card, p <> 0
   = p ** m - p ** n               by EXP_SUC_DIV, 0 < p
   = p * p ** n - p ** n           by EXP
   = (p - 1) * p ** n              by RIGHT_SUB_DISTRIB
*)
Theorem phi_prime_power:
  !p n. prime p ==> phi (p ** SUC n) = (p - 1) * p ** n
Proof
  rpt strip_tac >>
  qabbrev_tac `m = SUC n` >>
  qabbrev_tac `u = natural (p ** m)` >>
  qabbrev_tac `v = p multiples_upto (p ** m)` >>
  `0 < p` by rw[PRIME_POS] >>
  `FINITE u` by rw[natural_finite, Abbr`u`] >>
  `v SUBSET u` by rw[multiples_upto_subset, Abbr`v`, Abbr`u`] >>
  `phi (p ** m) = CARD (coprimes (p ** m))` by rw[phi_def] >>
  `_ = CARD (u DIFF v)` by rw[coprimes_prime_power, Abbr`u`, Abbr`v`] >>
  `_ = CARD u - CARD v` by rw[SUBSET_DIFF_CARD] >>
  `_ = p ** m - (p ** m DIV p)` by rw[natural_card, multiples_upto_card, Abbr`u`, Abbr`v`] >>
  `_ = p ** m - p ** n` by rw[EXP_SUC_DIV, Abbr`m`] >>
  `_ = p * p ** n - p ** n` by rw[GSYM EXP] >>
  `_ = (p - 1) * p ** n` by decide_tac >>
  simp[]
QED

(* Yes, a spectacular theorem! *)

(* Idea: specialise phi_prime_power for prime squared. *)

(* Theorem: prime p ==> phi (p * p) = p * (p - 1) *)
(* Proof:
     phi (p * p)
   = phi (p ** 2)          by EXP_2
   = phi (p ** SUC 1)      by TWO
   = (p - 1) * p ** 1      by phi_prime_power
   = p * (p - 1)           by EXP_1
*)
Theorem phi_prime_sq:
  !p. prime p ==> phi (p * p) = p * (p - 1)
Proof
  rpt strip_tac >>
  `phi (p * p) = phi (p ** SUC 1)` by rw[] >>
  simp[phi_prime_power]
QED

(* Idea: Euler phi function for a product of primes. *)

(* Theorem: prime p /\ prime q ==>
            phi (p * q) = if p = q then p * (p - 1) else (p - 1) * (q - 1) *)
(* Proof:
   If p = q, phi (p * p) = p * (p - 1)         by phi_prime_sq
   If p <> q, phi (p * q) = (p - 1) * (q - 1)  by phi_primes_distinct
*)
Theorem phi_primes:
  !p q. prime p /\ prime q ==>
        phi (p * q) = if p = q then p * (p - 1) else (p - 1) * (q - 1)
Proof
  metis_tac[phi_prime_sq, phi_primes_distinct]
QED

(* Finally, another nice result. *)

(* ------------------------------------------------------------------------- *)
(* Recursive definition of phi                                               *)
(* ------------------------------------------------------------------------- *)

(* Define phi by recursion *)
Definition rec_phi_def:
  rec_phi n = if n = 0 then 0
         else if n = 1 then 1
         else n - SIGMA rec_phi { m | m < n /\ m divides n}
Termination
  WF_REL_TAC `$< : num -> num -> bool` >> srw_tac[][]
End
(* This is the recursive form of Gauss' Little Theorem:  n = SUM phi m, m divides n *)

(* Just using Define without any condition will trigger:

Initial goal:

?R. WF R /\ !n a. n <> 0 /\ n <> 1 /\ a IN {m | m < n /\ m divides n} ==> R a n

Unable to prove termination!

Try using "TotalDefn.tDefine <name> <quotation> <tac>".

The termination goal has been set up using Defn.tgoal <defn>.

So one can set up:
g `?R. WF R /\ !n a. n <> 0 /\ n <> 1 /\ a IN {m | m < n /\ m divides n} ==> R a n`;
e (WF_REL_TAC `$< : num -> num -> bool`);
e (srw[][]);

which gives the tDefine solution.
*)

(* Theorem: rec_phi 0 = 0 *)
(* Proof: by rec_phi_def *)
val rec_phi_0 = store_thm(
  "rec_phi_0",
  ``rec_phi 0 = 0``,
  rw[rec_phi_def]);

(* Theorem: rec_phi 1 = 1 *)
(* Proof: by rec_phi_def *)
val rec_phi_1 = store_thm(
  "rec_phi_1",
  ``rec_phi 1 = 1``,
  rw[Once rec_phi_def]);

(* Theorem: rec_phi n = phi n *)
(* Proof:
   By complete induction on n.
   If n = 0,
      rec_phi 0 = 0      by rec_phi_0
                = phi 0  by phi_0
   If n = 1,
      rec_phi 1 = 1      by rec_phi_1
                = phi 1  by phi_1
   Othewise, 0 < n, 1 < n.
      Let s = {m | m < n /\ m divides n}.
      Note s SUBSET (count n)       by SUBSET_DEF
      thus FINITE s                 by SUBSET_FINITE, FINITE_COUNT
     Hence !m. m IN s
       ==> (rec_phi m = phi m)      by induction hypothesis
      Also n NOTIN s                by EXTENSION
       and n INSERT s
         = {m | m <= n /\ m divides n}
         = {m | 0 < m /\ m <= n /\ m divides n}      by divisor_pos, 0 < n
         = divisors n               by divisors_def, EXTENSION, LESS_OR_EQ

        rec_phi n
      = n - (SIGMA rec_phi s)       by rec_phi_def
      = n - (SIGMA phi s)           by SUM_IMAGE_CONG, rec_phi m = phi m
      = (SIGMA phi (divisors n)) - (SIGMA phi s)           by Gauss' Little Theorem
      = (SIGMA phi (n INSERT s)) - (SIGMA phi s)           by divisors n = n INSERT s
      = (phi n + SIGMA phi (s DELETE n)) - (SIGMA phi s)   by SUM_IMAGE_THM
      = (phi n + SIGMA phi s) - (SIGMA phi s)              by DELETE_NON_ELEMENT
      = phi n                                              by ADD_SUB
*)
Theorem rec_phi_eq_phi:
  !n. rec_phi n = phi n
Proof
  completeInduct_on `n` >>
  Cases_on `n = 0` >-
  rw[rec_phi_0, phi_0] >>
  Cases_on `n = 1` >-
  rw[rec_phi_1, phi_1] >>
  `0 < n /\ 1 < n` by decide_tac >>
  qabbrev_tac `s = {m | m < n /\ m divides n}` >>
  qabbrev_tac `t = SIGMA rec_phi s` >>
  `!m. m IN s <=> m < n /\ m divides n` by rw[Abbr`s`] >>
  `!m. m IN s ==> (rec_phi m = phi m)` by rw[] >>
  `t = SIGMA phi s` by rw[SUM_IMAGE_CONG, Abbr`t`] >>
  `s SUBSET (count n)` by rw[SUBSET_DEF] >>
  `FINITE s` by metis_tac[SUBSET_FINITE, FINITE_COUNT] >>
  `n NOTIN s` by rw[] >>
  (`n INSERT s = divisors n` by (rw[divisors_def, EXTENSION] >> metis_tac[divisor_pos, LESS_OR_EQ, DIVIDES_REFL])) >>
  `n = SIGMA phi (divisors n)` by rw[Gauss_little_thm] >>
  `_ = phi n + SIGMA phi (s DELETE n)` by rw[GSYM SUM_IMAGE_THM] >>
  `_ = phi n + t` by metis_tac[DELETE_NON_ELEMENT] >>
  `rec_phi n = n - t` by metis_tac[rec_phi_def] >>
  decide_tac
QED


(* ------------------------------------------------------------------------- *)
(* Useful Theorems (not used).                                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: INJ (coprimes) (univ(:num) DIFF {1}) univ(:num -> bool) *)
(* Proof:
   By INJ_DEF, this is to show:
      x <> 1 /\ y <> 1 /\ coprimes x = coprimes y ==> x = y
   If x = 0, then y = 0              by coprimes_eq_empty
   If y = 0, then x = 0              by coprimes_eq_empty
   If x <> 0 and y <> 0,
      with x <> 1 and y <> 1         by given
      then 1 < x and 1 < y.
      Since MAX_SET (coprimes x) = x - 1    by coprimes_max, 1 < x
        and MAX_SET (coprimes y) = y - 1    by coprimes_max, 1 < y
         If coprimes x = coprimes y,
                 x - 1 = y - 1       by above
      Hence          x = y           by CANCEL_SUB
*)
val coprimes_from_not_1_inj = store_thm(
  "coprimes_from_not_1_inj",
  ``INJ (coprimes) (univ(:num) DIFF {1}) univ(:num -> bool)``,
  rw[INJ_DEF] >>
  Cases_on `x = 0` >-
  metis_tac[coprimes_eq_empty] >>
  Cases_on `y = 0` >-
  metis_tac[coprimes_eq_empty] >>
  `1 < x /\ 1 < y` by decide_tac >>
  `x - 1 = y - 1` by metis_tac[coprimes_max] >>
  decide_tac);
(* Not very useful. *)

(* Here is group of related theorems for (divisors n):
   divisors_eq_image_gcd_upto
   divisors_eq_image_gcd_count
   divisors_eq_image_gcd_natural

   This first one is proved independently, then the second and third are derived.
   Of course, the best is the third one, which is now divisors_eq_gcd_image (above)
   Here, I rework all proofs of these three from divisors_eq_gcd_image,
   so divisors_eq_image_gcd_natural = divisors_eq_gcd_image.
*)

(* Theorem: 0 < n ==> divisors n = IMAGE (gcd n) (upto n) *)
(* Proof:
   Note gcd n 0 = n                                by GCD_0
    and n IN divisors n                            by divisors_has_last, 0 < n
     divisors n
   = (gcd n 0) INSERT (divisors n)                 by ABSORPTION
   = (gcd n 0) INSERT (IMAGE (gcd n) (natural n))  by divisors_eq_gcd_image
   = IMAGE (gcd n) (0 INSERT (natural n))          by IMAGE_INSERT
   = IMAGE (gcd n) (upto n)                        by upto_by_natural
*)
Theorem divisors_eq_image_gcd_upto:
  !n. 0 < n ==> divisors n = IMAGE (gcd n) (upto n)
Proof
  rpt strip_tac >>
  `IMAGE (gcd n) (upto n) = IMAGE (gcd n) (0 INSERT natural n)` by simp[upto_by_natural] >>
  `_ = (gcd n 0) INSERT (IMAGE (gcd n) (natural n))` by fs[] >>
  `_ = n INSERT (divisors n)` by fs[divisors_eq_gcd_image] >>
  metis_tac[divisors_has_last, ABSORPTION]
QED

(* Theorem: (feq (gcd n)) equiv_on (upto n) *)
(* Proof:
   By feq_equiv |- !s f. feq f equiv_on s
   Taking s = upto n, f = gcd n.
*)
val gcd_eq_equiv_on_upto = store_thm(
  "gcd_eq_equiv_on_upto",
  ``!n. (feq (gcd n)) equiv_on (upto n)``,
  rw[feq_equiv]);

(* Theorem: 0 < n ==> partition (feq (gcd n)) (upto n) = IMAGE (preimage (gcd n) (upto n)) (divisors n) *)
(* Proof:
   Let f = gcd n, s = upto n.
     partition (feq f) s
   = IMAGE (preimage f s o f) s                      by feq_partition
   = IMAGE (preimage f s) (IMAGE f s)                by IMAGE_COMPOSE
   = IMAGE (preimage f s) (IMAGE (gcd n) (upto n))   by expansion
   = IMAGE (preimage f s) (divisors n)               by divisors_eq_image_gcd_upto, 0 < n
*)
val gcd_eq_upto_partition_by_divisors = store_thm(
  "gcd_eq_upto_partition_by_divisors",
  ``!n. 0 < n ==> partition (feq (gcd n)) (upto n) = IMAGE (preimage (gcd n) (upto n)) (divisors n)``,
  rpt strip_tac >>
  qabbrev_tac `f = gcd n` >>
  qabbrev_tac `s = upto n` >>
  `partition (feq f) s = IMAGE (preimage f s o f) s` by rw[feq_partition] >>
  `_ = IMAGE (preimage f s) (IMAGE f s)` by rw[IMAGE_COMPOSE] >>
  rw[divisors_eq_image_gcd_upto, Abbr`f`, Abbr`s`]);

(* Theorem: SIGMA f (upto n) = SIGMA (SIGMA f) (partition (feq (gcd n)) (upto n)) *)
(* Proof:
   Let g = gcd n, s = upto n.
   Since FINITE s               by upto_finite
     and (feq g) equiv_on s     by feq_equiv
   The result follows           by set_sigma_by_partition
*)
val sum_over_upto_by_gcd_partition = store_thm(
  "sum_over_upto_by_gcd_partition",
  ``!f n. SIGMA f (upto n) = SIGMA (SIGMA f) (partition (feq (gcd n)) (upto n))``,
  rw[feq_equiv, set_sigma_by_partition]);

(* Theorem: 0 < n ==> SIGMA f (upto n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (upto n)) (divisors n)) *)
(* Proof:
     SIGMA f (upto n)
   = SIGMA (SIGMA f) (partition (feq (gcd n)) (upto n))                by sum_over_upto_by_gcd_partition
   = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (upto n)) (divisors n))  by gcd_eq_upto_partition_by_divisors, 0 < n
*)
val sum_over_upto_by_divisors = store_thm(
  "sum_over_upto_by_divisors",
  ``!f n. 0 < n ==> SIGMA f (upto n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (upto n)) (divisors n))``,
  rw[sum_over_upto_by_gcd_partition, gcd_eq_upto_partition_by_divisors]);

(* Similar results based on count *)

(* Theorem: divisors n = IMAGE (gcd n) (count n) *)
(* Proof:
   If n = 0,
      LHS = divisors 0 = {}                      by divisors_0
      RHS = IMAGE (gcd 0) (count 0)
          = IMAGE (gcd 0) {}                     by COUNT_0
          = {} = LHS                             by IMAGE_EMPTY
  If n <> 0, 0 < n.
     divisors n
   = IMAGE (gcd n) (upto n)                      by divisors_eq_image_gcd_upto, 0 < n
   = IMAGE (gcd n) (n INSERT (count n))          by upto_by_count
   = (gcd n n) INSERT (IMAGE (gcd n) (count n))  by IMAGE_INSERT
   = n INSERT (IMAGE (gcd n) (count n))          by GCD_REF
   = (gcd n 0) INSERT (IMAGE (gcd n) (count n))  by GCD_0R
   = IMAGE (gcd n) (0 INSERT (count n))          by IMAGE_INSERT
   = IMAGE (gcd n) (count n)                     by IN_COUNT, ABSORPTION, 0 < n.
*)
Theorem divisors_eq_image_gcd_count:
  !n. divisors n = IMAGE (gcd n) (count n)
Proof
  rpt strip_tac >>
  Cases_on `n = 0` >-
  simp[divisors_0] >>
  `0 < n` by decide_tac >>
  `divisors n = IMAGE (gcd n) (upto n)` by rw[divisors_eq_image_gcd_upto] >>
  `_ = IMAGE (gcd n) (n INSERT (count n))` by rw[upto_by_count] >>
  `_ = n INSERT (IMAGE (gcd n) (count n))` by rw[GCD_REF] >>
  `_ = (gcd n 0) INSERT (IMAGE (gcd n) (count n))` by rw[GCD_0R] >>
  `_ = IMAGE (gcd n) (0 INSERT (count n))` by rw[] >>
  metis_tac[IN_COUNT, ABSORPTION]
QED

(* Theorem: (feq (gcd n)) equiv_on (count n) *)
(* Proof:
   By feq_equiv |- !s f. feq f equiv_on s
   Taking s = upto n, f = count n.
*)
val gcd_eq_equiv_on_count = store_thm(
  "gcd_eq_equiv_on_count",
  ``!n. (feq (gcd n)) equiv_on (count n)``,
  rw[feq_equiv]);

(* Theorem: partition (feq (gcd n)) (count n) = IMAGE (preimage (gcd n) (count n)) (divisors n) *)
(* Proof:
   Let f = gcd n, s = count n.
     partition (feq f) s
   = IMAGE (preimage f s o f) s                      by feq_partition
   = IMAGE (preimage f s) (IMAGE f s)                by IMAGE_COMPOSE
   = IMAGE (preimage f s) (IMAGE (gcd n) (count n))  by expansion
   = IMAGE (preimage f s) (divisors n)               by divisors_eq_image_gcd_count
*)
Theorem gcd_eq_count_partition_by_divisors:
  !n. partition (feq (gcd n)) (count n) = IMAGE (preimage (gcd n) (count n)) (divisors n)
Proof
  rpt strip_tac >>
  qabbrev_tac `f = gcd n` >>
  qabbrev_tac `s = count n` >>
  `partition (feq f) s = IMAGE (preimage f s o f) s` by rw[feq_partition] >>
  `_ = IMAGE (preimage f s) (IMAGE f s)` by rw[IMAGE_COMPOSE] >>
  rw[divisors_eq_image_gcd_count, Abbr`f`, Abbr`s`]
QED

(* Theorem: SIGMA f (count n) = SIGMA (SIGMA f) (partition (feq (gcd n)) (count n)) *)
(* Proof:
   Let g = gcd n, s = count n.
   Since FINITE s               by FINITE_COUNT
     and (feq g) equiv_on s     by feq_equiv
   The result follows           by set_sigma_by_partition
*)
val sum_over_count_by_gcd_partition = store_thm(
  "sum_over_count_by_gcd_partition",
  ``!f n. SIGMA f (count n) = SIGMA (SIGMA f) (partition (feq (gcd n)) (count n))``,
  rw[feq_equiv, set_sigma_by_partition]);

(* Theorem: SIGMA f (count n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (count n)) (divisors n)) *)
(* Proof:
     SIGMA f (count n)
   = SIGMA (SIGMA f) (partition (feq (gcd n)) (count n))                by sum_over_count_by_gcd_partition
   = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (count n)) (divisors n))  by gcd_eq_count_partition_by_divisors
*)
Theorem sum_over_count_by_divisors:
  !f n. SIGMA f (count n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (count n)) (divisors n))
Proof
  rw[sum_over_count_by_gcd_partition, gcd_eq_count_partition_by_divisors]
QED

(* Similar results based on natural *)

(* Theorem: divisors n = IMAGE (gcd n) (natural n) *)
(* Proof:
   If n = 0,
      LHS = divisors 0 = {}                      by divisors_0
      RHS = IMAGE (gcd 0) (natural 0)
          = IMAGE (gcd 0) {}                     by natural_0
          = {} = LHS                             by IMAGE_EMPTY
  If n <> 0, 0 < n.
     divisors n
   = IMAGE (gcd n) (upto n)                        by divisors_eq_image_gcd_upto, 0 < n
   = IMAGE (gcd n) (0 INSERT natural n)            by upto_by_natural
   = (gcd 0 n) INSERT (IMAGE (gcd n) (natural n))  by IMAGE_INSERT
   = n INSERT (IMAGE (gcd n) (natural n))          by GCD_0L
   = (gcd n n) INSERT (IMAGE (gcd n) (natural n))  by GCD_REF
   = IMAGE (gcd n) (n INSERT (natural n))          by IMAGE_INSERT
   = IMAGE (gcd n) (natural n)                     by natural_has_last, ABSORPTION, 0 < n.
*)
Theorem divisors_eq_image_gcd_natural:
  !n. divisors n = IMAGE (gcd n) (natural n)
Proof
  rpt strip_tac >>
  Cases_on `n = 0` >-
  simp[divisors_0, natural_0] >>
  `0 < n` by decide_tac >>
  `divisors n = IMAGE (gcd n) (upto n)` by rw[divisors_eq_image_gcd_upto] >>
  `_ = IMAGE (gcd n) (0 INSERT (natural n))` by rw[upto_by_natural] >>
  `_ = n INSERT (IMAGE (gcd n) (natural n))` by rw[GCD_0L] >>
  `_ = (gcd n n) INSERT (IMAGE (gcd n) (natural n))` by rw[GCD_REF] >>
  `_ = IMAGE (gcd n) (n INSERT (natural n))` by rw[] >>
  metis_tac[natural_has_last, ABSORPTION]
QED
(* This is the same as divisors_eq_gcd_image *)

(* Theorem: partition (feq (gcd n)) (natural n) = IMAGE (preimage (gcd n) (natural n)) (divisors n) *)
(* Proof:
   Let f = gcd n, s = natural n.
     partition (feq f) s
   = IMAGE (preimage f s o f) s                        by feq_partition
   = IMAGE (preimage f s) (IMAGE f s)                  by IMAGE_COMPOSE
   = IMAGE (preimage f s) (IMAGE (gcd n) (natural n))  by expansion
   = IMAGE (preimage f s) (divisors n)                 by divisors_eq_image_gcd_natural
*)
Theorem gcd_eq_natural_partition_by_divisors:
  !n. partition (feq (gcd n)) (natural n) = IMAGE (preimage (gcd n) (natural n)) (divisors n)
Proof
  rpt strip_tac >>
  qabbrev_tac `f = gcd n` >>
  qabbrev_tac `s = natural n` >>
  `partition (feq f) s = IMAGE (preimage f s o f) s` by rw[feq_partition] >>
  `_ = IMAGE (preimage f s) (IMAGE f s)` by rw[IMAGE_COMPOSE] >>
  rw[divisors_eq_image_gcd_natural, Abbr`f`, Abbr`s`]
QED

(* Theorem: SIGMA f (natural n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (natural n)) (divisors n)) *)
(* Proof:
     SIGMA f (natural n)
   = SIGMA (SIGMA f) (partition (feq (gcd n)) (natural n))                by sum_over_natural_by_gcd_partition
   = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (natural n)) (divisors n))  by gcd_eq_natural_partition_by_divisors
*)
Theorem sum_over_natural_by_preimage_divisors:
  !f n. SIGMA f (natural n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (natural n)) (divisors n))
Proof
  rw[sum_over_natural_by_gcd_partition, gcd_eq_natural_partition_by_divisors]
QED

(* Theorem: (f 0 = g 0) /\ (!n. SIGMA f (divisors n) = SIGMA g (divisors n)) ==> (f = g) *)
(* Proof:
   By FUN_EQ_THM, this is to show: !x. f x = g x.
   By complete induction on x.
   Let s = divisors x, t = s DELETE x.
   If x = 0, f 0 = g 0 is true            by given
   Otherwise x <> 0.
   Then x IN s                            by divisors_has_last, 0 < x
    and s = x INSERT t /\ x NOTIN t       by INSERT_DELETE, IN_DELETE
   Note FINITE s                          by divisors_finite
     so FINITE t                          by FINITE_DELETE

   Claim: SIGMA f t = SIGMA g t
   Proof: By SUM_IMAGE_CONG, this is to show:
             !z. z IN t ==> (f z = g z)
          But z IN s <=> 0 < z /\ z <= x /\ z divides x     by divisors_element
           so z IN t <=> 0 < z /\ z < x /\ z divides x      by IN_DELETE
          ==> f z = g z                                     by induction hypothesis, [1]

   Now      SIGMA f s = SIGMA g s         by implication
   or f x + SIGMA f t = g x + SIGMA g t   by SUM_IMAGE_INSERT
   or             f x = g x               by [1], SIGMA f t = SIGMA g t
*)
Theorem sum_image_divisors_cong:
  !f g. (f 0 = g 0) /\ (!n. SIGMA f (divisors n) = SIGMA g (divisors n)) ==> (f = g)
Proof
  rw[FUN_EQ_THM] >>
  completeInduct_on `x` >>
  qabbrev_tac `s = divisors x` >>
  qabbrev_tac `t = s DELETE x` >>
  (Cases_on `x = 0` >> simp[]) >>
  `x IN s` by rw[divisors_has_last, Abbr`s`] >>
  `s = x INSERT t /\ x NOTIN t` by rw[Abbr`t`] >>
  `SIGMA f t = SIGMA g t` by
  ((irule SUM_IMAGE_CONG >> simp[]) >>
  rw[divisors_element, Abbr`t`, Abbr`s`]) >>
  `FINITE t` by rw[divisors_finite, Abbr`t`, Abbr`s`] >>
  `SIGMA f s = f x + SIGMA f t` by rw[SUM_IMAGE_INSERT] >>
  `SIGMA g s = g x + SIGMA g t` by rw[SUM_IMAGE_INSERT] >>
  `SIGMA f s = SIGMA g s` by metis_tac[] >>
  decide_tac
QED
(* But this is not very useful! *)

(* ------------------------------------------------------------------------- *)
(* Mobius Function and Inversion Documentation                               *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   sq_free s          = {n | n IN s /\ square_free n}
   non_sq_free s      = {n | n IN s /\ ~(square_free n)}
   even_sq_free s     = {n | n IN (sq_free s) /\ EVEN (CARD (prime_factors n))}
   odd_sq_free s      = {n | n IN (sq_free s) /\ ODD (CARD (prime_factors n))}
   less_divisors n    = {x | x IN (divisors n) /\ x <> n}
   proper_divisors n  = {x | x IN (divisors n) /\ x <> 1 /\ x <> n}
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Square-free Number and Square-free Sets:
   square_free_def     |- !n. square_free n <=> !p. prime p /\ p divides n ==> ~(p * p divides n)
   square_free_1       |- square_free 1
   square_free_prime   |- !n. prime n ==> square_free n

   sq_free_element     |- !s n. n IN sq_free s <=> n IN s /\ square_free n
   sq_free_subset      |- !s. sq_free s SUBSET s
   sq_free_finite      |- !s. FINITE s ==> FINITE (sq_free s)
   non_sq_free_element |- !s n. n IN non_sq_free s <=> n IN s /\ ~square_free n
   non_sq_free_subset  |- !s. non_sq_free s SUBSET s
   non_sq_free_finite  |- !s. FINITE s ==> FINITE (non_sq_free s)
   sq_free_split       |- !s. (s = sq_free s UNION non_sq_free s) /\
                              (sq_free s INTER non_sq_free s = {})
   sq_free_union       |- !s. s = sq_free s UNION non_sq_free s
   sq_free_inter       |- !s. sq_free s INTER non_sq_free s = {}
   sq_free_disjoint    |- !s. DISJOINT (sq_free s) (non_sq_free s)

   Prime Divisors of a Number and Partitions of Square-free Set:
   prime_factors_def      |- !n. prime_factors n = {p | prime p /\ p IN divisors n}
   prime_factors_element  |- !n p. p IN prime_factors n <=> prime p /\ p <= n /\ p divides n
   prime_factors_subset   |- !n. prime_factors n SUBSET divisors n
   prime_factors_finite   |- !n. FINITE (prime_factors n)

   even_sq_free_element    |- !s n. n IN even_sq_free s <=> n IN s /\ square_free n /\ EVEN (CARD (prime_factors n))
   even_sq_free_subset     |- !s. even_sq_free s SUBSET s
   even_sq_free_finite     |- !s. FINITE s ==> FINITE (even_sq_free s)
   odd_sq_free_element     |- !s n. n IN odd_sq_free s <=> n IN s /\ square_free n /\ ODD (CARD (prime_factors n))
   odd_sq_free_subset      |- !s. odd_sq_free s SUBSET s
   odd_sq_free_finite      |- !s. FINITE s ==> FINITE (odd_sq_free s)
   sq_free_split_even_odd  |- !s. (sq_free s = even_sq_free s UNION odd_sq_free s) /\
                                  (even_sq_free s INTER odd_sq_free s = {})
   sq_free_union_even_odd  |- !s. sq_free s = even_sq_free s UNION odd_sq_free s
   sq_free_inter_even_odd  |- !s. even_sq_free s INTER odd_sq_free s = {}
   sq_free_disjoint_even_odd  |- !s. DISJOINT (even_sq_free s) (odd_sq_free s)

   Less Divisors of a number:
   less_divisors_element       |- !n x. x IN less_divisors n <=> 0 < x /\ x < n /\ x divides n
   less_divisors_0             |- less_divisors 0 = {}
   less_divisors_1             |- less_divisors 1 = {}
   less_divisors_subset_divisors
                               |- !n. less_divisors n SUBSET divisors n
   less_divisors_finite        |- !n. FINITE (less_divisors n)
   less_divisors_prime         |- !n. prime n ==> (less_divisors n = {1})
   less_divisors_has_1         |- !n. 1 < n ==> 1 IN less_divisors n
   less_divisors_nonzero       |- !n x. x IN less_divisors n ==> 0 < x
   less_divisors_has_cofactor  |- !n d. 1 < d /\ d IN less_divisors n ==> n DIV d IN less_divisors n

   Proper Divisors of a number:
   proper_divisors_element     |- !n x. x IN proper_divisors n <=> 1 < x /\ x < n /\ x divides n
   proper_divisors_0           |- proper_divisors 0 = {}
   proper_divisors_1           |- proper_divisors 1 = {}
   proper_divisors_subset      |- !n. proper_divisors n SUBSET less_divisors n
   proper_divisors_finite      |- !n. FINITE (proper_divisors n)
   proper_divisors_not_1       |- !n. 1 NOTIN proper_divisors n
   proper_divisors_by_less_divisors
                               |- !n. proper_divisors n = less_divisors n DELETE 1
   proper_divisors_prime       |- !n. prime n ==> (proper_divisors n = {})
   proper_divisors_has_cofactor|- !n d. d IN proper_divisors n ==> n DIV d IN proper_divisors n
   proper_divisors_min_gt_1    |- !n. proper_divisors n <> {} ==> 1 < MIN_SET (proper_divisors n)
   proper_divisors_max_min     |- !n. proper_divisors n <> {} ==>
                                      (MAX_SET (proper_divisors n) = n DIV MIN_SET (proper_divisors n)) /\
                                      (MIN_SET (proper_divisors n) = n DIV MAX_SET (proper_divisors n))

   Useful Properties of Less Divisors:
   less_divisors_min             |- !n. 1 < n ==> (MIN_SET (less_divisors n) = 1)
   less_divisors_max             |- !n. MAX_SET (less_divisors n) <= n DIV 2
   less_divisors_subset_natural  |- !n. less_divisors n SUBSET natural (n DIV 2)

   Properties of Summation equals Perfect Power:
   perfect_power_special_inequality  |- !p. 1 < p ==> !n. p * (p ** n - 1) < (p - 1) * (2 * p ** n)
   perfect_power_half_inequality_1   |- !p n. 1 < p /\ 0 < n ==> 2 * p ** (n DIV 2) <= p ** n
   perfect_power_half_inequality_2   |- !p n. 1 < p /\ 0 < n ==>
                                        (p ** (n DIV 2) - 2) * p ** (n DIV 2) <= p ** n - 2 * p ** (n DIV 2)
   sigma_eq_perfect_power_bounds_1   |- !p. 1 < p ==>
                          !f. (!n. 0 < n ==> (p ** n = SIGMA (\d. d * f d) (divisors n))) ==>
                              (!n. 0 < n ==> n * f n <= p ** n) /\
                               !n. 0 < n ==> p ** n - 2 * p ** (n DIV 2) < n * f n
   sigma_eq_perfect_power_bounds_2   |- !p. 1 < p ==>
                          !f. (!n. 0 < n ==> (p ** n = SIGMA (\d. d * f d) (divisors n))) ==>
                              (!n. 0 < n ==> n * f n <= p ** n) /\
                               !n. 0 < n ==> (p ** (n DIV 2) - 2) * p ** (n DIV 2) < n * f n

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Mobius Function and Inversion                                             *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Square-free Number and Square-free Sets                                   *)
(* ------------------------------------------------------------------------- *)

(* Define square-free number *)
val square_free_def = Define`
    square_free n = !p. prime p /\ p divides n ==> ~(p * p divides n)
`;

(* Theorem: square_free 1 *)
(* Proof:
       square_free 1
   <=> !p. prime p /\ p divides 1 ==> ~(p * p divides 1)    by square_free_def
   <=> prime 1 ==> ~(1 * 1 divides 1)                       by DIVIDES_ONE
   <=> F ==> ~(1 * 1 divides 1)                             by NOT_PRIME_1
   <=> T                                                    by false assumption
*)
val square_free_1 = store_thm(
  "square_free_1",
  ``square_free 1``,
  rw[square_free_def]);

(* Theorem: prime n ==> square_free n *)
(* Proof:
       square_free n
   <=> !p. prime p /\ p divides n ==> ~(p * p divides n)   by square_free_def
   By contradiction, suppose (p * p divides n).
   Since p divides n ==> (p = n) \/ (p = 1)                by prime_def
     and p * p divides  ==> (p * p = n) \/ (p * p = 1)     by prime_def
     but p <> 1                                            by prime_def
      so p * p <> 1              by MULT_EQ_1
    Thus p * p = n = p,
      or p = 0 \/ p = 1          by SQ_EQ_SELF
     But p <> 0                  by NOT_PRIME_0
     and p <> 1                  by NOT_PRIME_1
    Thus there is a contradiction.
*)
val square_free_prime = store_thm(
  "square_free_prime",
  ``!n. prime n ==> square_free n``,
  rw_tac std_ss[square_free_def] >>
  spose_not_then strip_assume_tac >>
  `p * p = p` by metis_tac[prime_def, MULT_EQ_1] >>
  metis_tac[SQ_EQ_SELF, NOT_PRIME_0, NOT_PRIME_1]);

(* Overload square-free filter of a set *)
val _ = overload_on("sq_free", ``\s. {n | n IN s /\ square_free n}``);

(* Overload non-square-free filter of a set *)
val _ = overload_on("non_sq_free", ``\s. {n | n IN s /\ ~(square_free n)}``);

(* Theorem: n IN sq_free s <=> n IN s /\ square_free n *)
(* Proof: by notation. *)
val sq_free_element = store_thm(
  "sq_free_element",
  ``!s n. n IN sq_free s <=> n IN s /\ square_free n``,
  rw[]);

(* Theorem: sq_free s SUBSET s *)
(* Proof: by SUBSET_DEF *)
val sq_free_subset = store_thm(
  "sq_free_subset",
  ``!s. sq_free s SUBSET s``,
  rw[SUBSET_DEF]);

(* Theorem: FINITE s ==> FINITE (sq_free s) *)
(* Proof: by sq_free_subset, SUBSET_FINITE *)
val sq_free_finite = store_thm(
  "sq_free_finite",
  ``!s. FINITE s ==> FINITE (sq_free s)``,
  metis_tac[sq_free_subset, SUBSET_FINITE]);

(* Theorem: n IN non_sq_free s <=> n IN s /\ ~(square_free n) *)
(* Proof: by notation. *)
val non_sq_free_element = store_thm(
  "non_sq_free_element",
  ``!s n. n IN non_sq_free s <=> n IN s /\ ~(square_free n)``,
  rw[]);

(* Theorem: non_sq_free s SUBSET s *)
(* Proof: by SUBSET_DEF *)
val non_sq_free_subset = store_thm(
  "non_sq_free_subset",
  ``!s. non_sq_free s SUBSET s``,
  rw[SUBSET_DEF]);

(* Theorem: FINITE s ==> FINITE (non_sq_free s) *)
(* Proof: by non_sq_free_subset, SUBSET_FINITE *)
val non_sq_free_finite = store_thm(
  "non_sq_free_finite",
  ``!s. FINITE s ==> FINITE (non_sq_free s)``,
  metis_tac[non_sq_free_subset, SUBSET_FINITE]);

(* Theorem: (s = (sq_free s) UNION (non_sq_free s)) /\ ((sq_free s) INTER (non_sq_free s) = {}) *)
(* Proof:
   This is to show:
   (1) s = (sq_free s) UNION (non_sq_free s)
       True by EXTENSION, IN_UNION.
   (2) (sq_free s) INTER (non_sq_free s) = {}
       True by EXTENSION, IN_INTER
*)
val sq_free_split = store_thm(
  "sq_free_split",
  ``!s. (s = (sq_free s) UNION (non_sq_free s)) /\ ((sq_free s) INTER (non_sq_free s) = {})``,
  (rw[EXTENSION] >> metis_tac[]));

(* Theorem: s = (sq_free s) UNION (non_sq_free s) *)
(* Proof: extract from sq_free_split. *)
val sq_free_union = save_thm("sq_free_union", sq_free_split |> SPEC_ALL |> CONJUNCT1 |> GEN_ALL);
(* val sq_free_union = |- !s. s = sq_free s UNION non_sq_free s: thm *)

(* Theorem: (sq_free s) INTER (non_sq_free s) = {} *)
(* Proof: extract from sq_free_split. *)
val sq_free_inter = save_thm("sq_free_inter", sq_free_split |> SPEC_ALL |> CONJUNCT2 |> GEN_ALL);
(* val sq_free_inter = |- !s. sq_free s INTER non_sq_free s = {}: thm *)

(* Theorem: DISJOINT (sq_free s) (non_sq_free s) *)
(* Proof: by DISJOINT_DEF, sq_free_inter. *)
val sq_free_disjoint = store_thm(
  "sq_free_disjoint",
  ``!s. DISJOINT (sq_free s) (non_sq_free s)``,
  rw_tac std_ss[DISJOINT_DEF, sq_free_inter]);

(* ------------------------------------------------------------------------- *)
(* Prime Divisors of a Number and Partitions of Square-free Set              *)
(* ------------------------------------------------------------------------- *)

(* Define the prime divisors of a number *)
val prime_factors_def = zDefine`
    prime_factors n = {p | prime p /\ p IN (divisors n)}
`;
(* use zDefine as this cannot be computed. *)
(* prime_divisors is used in triangle.hol *)

(* Theorem: p IN prime_factors n <=> prime p /\ p <= n /\ p divides n *)
(* Proof:
       p IN prime_factors n
   <=> prime p /\ p IN (divisors n)                by prime_factors_def
   <=> prime p /\ 0 < p /\ p <= n /\ p divides n   by divisors_def
   <=> prime p /\ p <= n /\ p divides n            by PRIME_POS
*)
Theorem prime_factors_element:
  !n p. p IN prime_factors n <=> prime p /\ p <= n /\ p divides n
Proof
  rw[prime_factors_def, divisors_def] >>
  metis_tac[PRIME_POS]
QED

(* Theorem: (prime_factors n) SUBSET (divisors n) *)
(* Proof:
       p IN (prime_factors n)
   ==> p IN (divisors n)                         by prime_factors_def
   Hence (prime_factors n) SUBSET (divisors n)   by SUBSET_DEF
*)
val prime_factors_subset = store_thm(
  "prime_factors_subset",
  ``!n. (prime_factors n) SUBSET (divisors n)``,
  rw[prime_factors_def, SUBSET_DEF]);

(* Theorem: FINITE (prime_factors n) *)
(* Proof:
   Since (prime_factors n) SUBSET (divisors n)   by prime_factors_subset
     and FINITE (divisors n)                     by divisors_finite
    Thus FINITE (prime_factors n)                by SUBSET_FINITE
*)
val prime_factors_finite = store_thm(
  "prime_factors_finite",
  ``!n. FINITE (prime_factors n)``,
  metis_tac[prime_factors_subset, divisors_finite, SUBSET_FINITE]);

(* Overload even square-free filter of a set *)
val _ = overload_on("even_sq_free", ``\s. {n | n IN (sq_free s) /\ EVEN (CARD (prime_factors n))}``);

(* Overload odd square-free filter of a set *)
val _ = overload_on("odd_sq_free", ``\s. {n | n IN (sq_free s) /\ ODD (CARD (prime_factors n))}``);

(* Theorem: n IN even_sq_free s <=> n IN s /\ square_free n /\ EVEN (CARD (prime_factors n)) *)
(* Proof: by notation. *)
val even_sq_free_element = store_thm(
  "even_sq_free_element",
  ``!s n. n IN even_sq_free s <=> n IN s /\ square_free n /\ EVEN (CARD (prime_factors n))``,
  (rw[] >> metis_tac[]));

(* Theorem: even_sq_free s SUBSET s *)
(* Proof: by SUBSET_DEF *)
val even_sq_free_subset = store_thm(
  "even_sq_free_subset",
  ``!s. even_sq_free s SUBSET s``,
  rw[SUBSET_DEF]);

(* Theorem: FINITE s ==> FINITE (even_sq_free s) *)
(* Proof: by even_sq_free_subset, SUBSET_FINITE *)
val even_sq_free_finite = store_thm(
  "even_sq_free_finite",
  ``!s. FINITE s ==> FINITE (even_sq_free s)``,
  metis_tac[even_sq_free_subset, SUBSET_FINITE]);

(* Theorem: n IN odd_sq_free s <=> n IN s /\ square_free n /\ ODD (CARD (prime_factors n)) *)
(* Proof: by notation. *)
val odd_sq_free_element = store_thm(
  "odd_sq_free_element",
  ``!s n. n IN odd_sq_free s <=> n IN s /\ square_free n /\ ODD (CARD (prime_factors n))``,
  (rw[] >> metis_tac[]));

(* Theorem: odd_sq_free s SUBSET s *)
(* Proof: by SUBSET_DEF *)
val odd_sq_free_subset = store_thm(
  "odd_sq_free_subset",
  ``!s. odd_sq_free s SUBSET s``,
  rw[SUBSET_DEF]);

(* Theorem: FINITE s ==> FINITE (odd_sq_free s) *)
(* Proof: by odd_sq_free_subset, SUBSET_FINITE *)
val odd_sq_free_finite = store_thm(
  "odd_sq_free_finite",
  ``!s. FINITE s ==> FINITE (odd_sq_free s)``,
  metis_tac[odd_sq_free_subset, SUBSET_FINITE]);

(* Theorem: (sq_free s = (even_sq_free s) UNION (odd_sq_free s)) /\
            ((even_sq_free s) INTER (odd_sq_free s) = {}) *)
(* Proof:
   This is to show:
   (1) sq_free s = even_sq_free s UNION odd_sq_free s
       True by EXTENSION, IN_UNION, EVEN_ODD.
   (2) even_sq_free s INTER odd_sq_free s = {}
       True by EXTENSION, IN_INTER, EVEN_ODD.
*)
val sq_free_split_even_odd = store_thm(
  "sq_free_split_even_odd",
  ``!s. (sq_free s = (even_sq_free s) UNION (odd_sq_free s)) /\
       ((even_sq_free s) INTER (odd_sq_free s) = {})``,
  (rw[EXTENSION] >> metis_tac[EVEN_ODD]));

(* Theorem: sq_free s = (even_sq_free s) UNION (odd_sq_free s) *)
(* Proof: extract from sq_free_split_even_odd. *)
val sq_free_union_even_odd =
    save_thm("sq_free_union_even_odd", sq_free_split_even_odd |> SPEC_ALL |> CONJUNCT1 |> GEN_ALL);
(* val sq_free_union_even_odd =
   |- !s. sq_free s = even_sq_free s UNION odd_sq_free s: thm *)

(* Theorem: (even_sq_free s) INTER (odd_sq_free s) = {} *)
(* Proof: extract from sq_free_split_even_odd. *)
val sq_free_inter_even_odd =
    save_thm("sq_free_inter_even_odd", sq_free_split_even_odd |> SPEC_ALL |> CONJUNCT2 |> GEN_ALL);
(* val sq_free_inter_even_odd =
   |- !s. even_sq_free s INTER odd_sq_free s = {}: thm *)

(* Theorem: DISJOINT (even_sq_free s) (odd_sq_free s) *)
(* Proof: by DISJOINT_DEF, sq_free_inter_even_odd. *)
val sq_free_disjoint_even_odd = store_thm(
  "sq_free_disjoint_even_odd",
  ``!s. DISJOINT (even_sq_free s) (odd_sq_free s)``,
  rw_tac std_ss[DISJOINT_DEF, sq_free_inter_even_odd]);

(* ------------------------------------------------------------------------- *)
(* Less Divisors of a number.                                                *)
(* ------------------------------------------------------------------------- *)

(* Overload the set of divisors less than n *)
val _ = overload_on("less_divisors", ``\n. {x | x IN (divisors n) /\ x <> n}``);

(* Theorem: x IN (less_divisors n) <=> (0 < x /\ x < n /\ x divides n) *)
(* Proof: by divisors_element. *)
val less_divisors_element = store_thm(
  "less_divisors_element",
  ``!n x. x IN (less_divisors n) <=> (0 < x /\ x < n /\ x divides n)``,
  rw[divisors_element, EQ_IMP_THM]);

(* Theorem: less_divisors 0 = {} *)
(* Proof: by divisors_element. *)
val less_divisors_0 = store_thm(
  "less_divisors_0",
  ``less_divisors 0 = {}``,
  rw[divisors_element]);

(* Theorem: less_divisors 1 = {} *)
(* Proof: by divisors_element. *)
val less_divisors_1 = store_thm(
  "less_divisors_1",
  ``less_divisors 1 = {}``,
  rw[divisors_element]);

(* Theorem: (less_divisors n) SUBSET (divisors n) *)
(* Proof: by SUBSET_DEF *)
val less_divisors_subset_divisors = store_thm(
  "less_divisors_subset_divisors",
  ``!n. (less_divisors n) SUBSET (divisors n)``,
  rw[SUBSET_DEF]);

(* Theorem: FINITE (less_divisors n) *)
(* Proof:
   Since (less_divisors n) SUBSET (divisors n)   by less_divisors_subset_divisors
     and FINITE (divisors n)                     by divisors_finite
      so FINITE (proper_divisors n)              by SUBSET_FINITE
*)
val less_divisors_finite = store_thm(
  "less_divisors_finite",
  ``!n. FINITE (less_divisors n)``,
  metis_tac[divisors_finite, less_divisors_subset_divisors, SUBSET_FINITE]);

(* Theorem: prime n ==> (less_divisors n = {1}) *)
(* Proof:
   Since prime n
     ==> !b. b divides n ==> (b = n) \/ (b = 1)   by prime_def
   But (less_divisors n) excludes n               by less_divisors_element
   and 1 < n                                      by ONE_LT_PRIME
   Hence less_divisors n = {1}
*)
val less_divisors_prime = store_thm(
  "less_divisors_prime",
  ``!n. prime n ==> (less_divisors n = {1})``,
  rpt strip_tac >>
  `!b. b divides n ==> (b = n) \/ (b = 1)` by metis_tac[prime_def] >>
  rw[less_divisors_element, EXTENSION, EQ_IMP_THM] >| [
    `x <> n` by decide_tac >>
    metis_tac[],
    rw[ONE_LT_PRIME]
  ]);

(* Theorem: 1 < n ==> 1 IN (less_divisors n) *)
(* Proof:
       1 IN (less_divisors n)
   <=> 1 < n /\ 1 divides n     by less_divisors_element
   <=> T                        by ONE_DIVIDES_ALL
*)
val less_divisors_has_1 = store_thm(
  "less_divisors_has_1",
  ``!n. 1 < n ==> 1 IN (less_divisors n)``,
  rw[less_divisors_element]);

(* Theorem: x IN (less_divisors n) ==> 0 < x *)
(* Proof: by less_divisors_element. *)
val less_divisors_nonzero = store_thm(
  "less_divisors_nonzero",
  ``!n x. x IN (less_divisors n) ==> 0 < x``,
  rw[less_divisors_element]);

(* Theorem: 1 < d /\ d IN (less_divisors n) ==> (n DIV d) IN (less_divisors n) *)
(* Proof:
      d IN (less_divisors n)
  ==> d IN (divisors n)                   by less_divisors_subset_divisors
  ==> (n DIV d) IN (divisors n)           by divisors_has_cofactor
   Note 0 < d /\ d <= n ==> 0 < n         by divisors_element
   Also n DIV d < n                       by DIV_LESS, 0 < n /\ 1 < d
   thus n DIV d <> n                      by LESS_NOT_EQ
  Hence (n DIV d) IN (less_divisors n)    by notation
*)
val less_divisors_has_cofactor = store_thm(
  "less_divisors_has_cofactor",
  ``!n d. 1 < d /\ d IN (less_divisors n) ==> (n DIV d) IN (less_divisors n)``,
  rw[divisors_has_cofactor, divisors_element, DIV_LESS, LESS_NOT_EQ]);

(* ------------------------------------------------------------------------- *)
(* Proper Divisors of a number.                                              *)
(* ------------------------------------------------------------------------- *)

(* Overload the set of proper divisors of n *)
val _ = overload_on("proper_divisors", ``\n. {x | x IN (divisors n) /\ x <> 1 /\ x <> n}``);

(* Theorem: x IN (proper_divisors n) <=> (1 < x /\ x < n /\ x divides n) *)
(* Proof:
   Since x IN (divisors n)
     ==> 0 < x /\ x <= n /\ x divides n  by divisors_element
   Since x <= n but x <> n, x < n.
   With x <> 0 /\ x <> 1 ==> 1 < x.
*)
val proper_divisors_element = store_thm(
  "proper_divisors_element",
  ``!n x. x IN (proper_divisors n) <=> (1 < x /\ x < n /\ x divides n)``,
  rw[divisors_element, EQ_IMP_THM]);

(* Theorem: proper_divisors 0 = {} *)
(* Proof: by proper_divisors_element. *)
val proper_divisors_0 = store_thm(
  "proper_divisors_0",
  ``proper_divisors 0 = {}``,
  rw[proper_divisors_element, EXTENSION]);

(* Theorem: proper_divisors 1 = {} *)
(* Proof: by proper_divisors_element. *)
val proper_divisors_1 = store_thm(
  "proper_divisors_1",
  ``proper_divisors 1 = {}``,
  rw[proper_divisors_element, EXTENSION]);

(* Theorem: (proper_divisors n) SUBSET (less_divisors n) *)
(* Proof: by SUBSET_DEF *)
val proper_divisors_subset = store_thm(
  "proper_divisors_subset",
  ``!n. (proper_divisors n) SUBSET (less_divisors n)``,
  rw[SUBSET_DEF]);

(* Theorem: FINITE (proper_divisors n) *)
(* Proof:
   Since (proper_divisors n) SUBSET (less_divisors n) by proper_divisors_subset
     and FINITE (less_divisors n)                     by less_divisors_finite
      so FINITE (proper_divisors n)                   by SUBSET_FINITE
*)
val proper_divisors_finite = store_thm(
  "proper_divisors_finite",
  ``!n. FINITE (proper_divisors n)``,
  metis_tac[less_divisors_finite, proper_divisors_subset, SUBSET_FINITE]);

(* Theorem: 1 NOTIN (proper_divisors n) *)
(* Proof: proper_divisors_element *)
val proper_divisors_not_1 = store_thm(
  "proper_divisors_not_1",
  ``!n. 1 NOTIN (proper_divisors n)``,
  rw[proper_divisors_element]);

(* Theorem: proper_divisors n = (less_divisors n) DELETE 1 *)
(* Proof:
      proper_divisors n
    = {x | x IN (divisors n) /\ x <> 1 /\ x <> n}   by notation
    = {x | x IN (divisors n) /\ x <> n} DELETE 1    by IN_DELETE
    = (less_divisors n) DELETE 1
*)
val proper_divisors_by_less_divisors = store_thm(
  "proper_divisors_by_less_divisors",
  ``!n. proper_divisors n = (less_divisors n) DELETE 1``,
  rw[divisors_element, EXTENSION, EQ_IMP_THM]);

(* Theorem: prime n ==> (proper_divisors n = {}) *)
(* Proof:
      proper_divisors n
    = (less_divisors n) DELETE 1  by proper_divisors_by_less_divisors
    = {1} DELETE 1                by less_divisors_prime, prime n
    = {}                          by SING_DELETE
*)
val proper_divisors_prime = store_thm(
  "proper_divisors_prime",
  ``!n. prime n ==> (proper_divisors n = {})``,
  rw[proper_divisors_by_less_divisors, less_divisors_prime]);

(* Theorem: d IN (proper_divisors n) ==> (n DIV d) IN (proper_divisors n) *)
(* Proof:
   Let e = n DIV d.
   Since d IN (proper_divisors n)
     ==> 1 < d /\ d < n                   by proper_divisors_element
     and d IN (less_divisors n)           by proper_divisors_subset
      so e IN (less_divisors n)           by less_divisors_has_cofactor
     and 0 < e                            by less_divisors_nonzero
   Since d divides n                      by less_divisors_element
      so n = e * d                        by DIV_MULT_EQ, 0 < d
    thus e <> 1 since n <> d              by MULT_LEFT_1
    With 0 < e /\ e <> 1
     ==> e IN (proper_divisors n)         by proper_divisors_by_less_divisors, IN_DELETE
*)
val proper_divisors_has_cofactor = store_thm(
  "proper_divisors_has_cofactor",
  ``!n d. d IN (proper_divisors n) ==> (n DIV d) IN (proper_divisors n)``,
  rpt strip_tac >>
  qabbrev_tac `e = n DIV d` >>
  `1 < d /\ d < n` by metis_tac[proper_divisors_element] >>
  `d IN (less_divisors n)` by metis_tac[proper_divisors_subset, SUBSET_DEF] >>
  `e IN (less_divisors n)` by rw[less_divisors_has_cofactor, Abbr`e`] >>
  `0 < e` by metis_tac[less_divisors_nonzero] >>
  `0 < d /\ n <> d` by decide_tac >>
  `e <> 1` by metis_tac[less_divisors_element, DIV_MULT_EQ, MULT_LEFT_1] >>
  metis_tac[proper_divisors_by_less_divisors, IN_DELETE]);

(* Theorem: (proper_divisors n) <> {} ==> 1 < MIN_SET (proper_divisors n) *)
(* Proof:
   Let s = proper_divisors n.
   Since !x. x IN s ==> 1 < x        by proper_divisors_element
     But MIN_SET s IN s              by MIN_SET_IN_SET
   Hence 1 < MIN_SET s               by above
*)
val proper_divisors_min_gt_1 = store_thm(
  "proper_divisors_min_gt_1",
  ``!n. (proper_divisors n) <> {} ==> 1 < MIN_SET (proper_divisors n)``,
  metis_tac[MIN_SET_IN_SET, proper_divisors_element]);

(* Theorem: (proper_divisors n) <> {} ==>
            (MAX_SET (proper_divisors n) = n DIV (MIN_SET (proper_divisors n))) /\
            (MIN_SET (proper_divisors n) = n DIV (MAX_SET (proper_divisors n)))     *)
(* Proof:
   Let s = proper_divisors n, b = MIN_SET s.
   By MAX_SET_ELIM, this is to show:
   (1) FINITE s, true                     by proper_divisors_finite
   (2) s <> {} /\ x IN s /\ !y. y IN s ==> y <= x ==> x = n DIV b /\ b = n DIV x
       Note s <> {} ==> n <> 0            by proper_divisors_0
        Let m = n DIV b.
       Note n DIV x IN s                  by proper_divisors_has_cofactor, 0 < n, 1 < b.
       Also b IN s /\ b <= x              by MIN_SET_IN_SET, s <> {}
       thus 1 < b                         by proper_divisors_min_gt_1
         so m IN s                        by proper_divisors_has_cofactor, 0 < n, 1 < x.
         or 1 < m                         by proper_divisors_nonzero
        and m <= x                        by implication, x = MAX_SET s.
       Thus n DIV x <= n DIV m            by DIV_LE_MONOTONE_REVERSE [1], 0 < x, 0 < m.
        But n DIV m
          = n DIV (n DIV b) = b           by divide_by_cofactor, b divides n.
         so n DIV x <= b                  by [1]
      Since b <= n DIV x                  by MIN_SET_PROPERTY, b = MIN_SET s, n DIV x IN s.
         so n DIV x = b                   by LESS_EQUAL_ANTISYM (gives second subgoal)
      Hence m = n DIV b
              = n DIV (n DIV x) = x       by divide_by_cofactor, x divides n (gives first subgoal)
*)
val proper_divisors_max_min = store_thm(
  "proper_divisors_max_min",
  ``!n. (proper_divisors n) <> {} ==>
       (MAX_SET (proper_divisors n) = n DIV (MIN_SET (proper_divisors n))) /\
       (MIN_SET (proper_divisors n) = n DIV (MAX_SET (proper_divisors n)))``,
  ntac 2 strip_tac >>
  qabbrev_tac `s = proper_divisors n` >>
  qabbrev_tac `b = MIN_SET s` >>
  DEEP_INTRO_TAC MAX_SET_ELIM >>
  strip_tac >-
  rw[proper_divisors_finite, Abbr`s`] >>
  ntac 3 strip_tac >>
  `n <> 0` by metis_tac[proper_divisors_0] >>
  `b IN s /\ b <= x` by rw[MIN_SET_IN_SET, Abbr`b`] >>
  `1 < b` by rw[proper_divisors_min_gt_1, Abbr`s`, Abbr`b`] >>
  `0 < n /\ 1 < x` by decide_tac >>
  qabbrev_tac `m = n DIV b` >>
  `m IN s /\ (n DIV x) IN s` by rw[proper_divisors_has_cofactor, Abbr`m`, Abbr`s`] >>
  `1 < m` by metis_tac[proper_divisors_element] >>
  `0 < x /\ 0 < m` by decide_tac >>
  `n DIV x <= n DIV m` by rw[DIV_LE_MONOTONE_REVERSE] >>
  `b divides n /\ x divides n` by metis_tac[proper_divisors_element] >>
  `n DIV m = b` by rw[divide_by_cofactor, Abbr`m`] >>
  `b <= n DIV x` by rw[MIN_SET_PROPERTY, Abbr`b`] >>
  `b = n DIV x` by rw[LESS_EQUAL_ANTISYM] >>
  `m = x` by rw[divide_by_cofactor, Abbr`m`] >>
  decide_tac);

(* This is a milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* Useful Properties of Less Divisors                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < n ==> (MIN_SET (less_divisors n) = 1) *)
(* Proof:
   Let s = less_divisors n.
   Since 1 < n ==> 1 IN s         by less_divisors_has_1
      so s <> {}                  by MEMBER_NOT_EMPTY
     and !y. y IN s ==> 0 < y     by less_divisors_nonzero
      or !y. y IN s ==> 1 <= y    by LESS_EQ
   Hence 1 = MIN_SET s            by MIN_SET_TEST
*)
val less_divisors_min = store_thm(
  "less_divisors_min",
  ``!n. 1 < n ==> (MIN_SET (less_divisors n) = 1)``,
  metis_tac[less_divisors_has_1, MEMBER_NOT_EMPTY,
             MIN_SET_TEST, less_divisors_nonzero, LESS_EQ, ONE]);

(* Theorem: MAX_SET (less_divisors n) <= n DIV 2 *)
(* Proof:
   Let s = less_divisors n, m = MAX_SET s.
   If s = {},
      Then m = MAX_SET {} = 0          by MAX_SET_EMPTY
       and 0 <= n DIV 2 is trivial.
   If s <> {},
      Then n <> 0 /\ n <> 1            by less_divisors_0, less_divisors_1
   Note 1 IN s                         by less_divisors_has_1
   Consider t = s DELETE 1.
   Then t = proper_divisors n          by proper_divisors_by_less_divisors
   If t = {},
      Then s = {1}                     by DELETE_EQ_SING
       and m = 1                       by SING_DEF, IN_SING (same as MAX_SET_SING)
     Since 2 <= n                      by 1 < n
      thus n DIV n <= n DIV 2          by DIV_LE_MONOTONE_REVERSE
        or n DIV n = 1 = m <= n DIV 2  by DIVMOD_ID, 0 < n
   If t <> {},
      Let b = MIN_SET t
      Then MAX_SET t = n DIV b         by proper_divisors_max_min, t <> {}
     Since MIN_SET s = 1               by less_divisors_min, 1 < n
       and FINITE s                    by less_divisors_finite
       and s <> {1}                    by DELETE_EQ_SING
      thus m = MAX_SET t               by MAX_SET_DELETE, s <> {1}

       Now 1 < b                       by proper_divisors_min_gt_1
        so 2 <= b                      by LESS_EQ, 1 < b
     Hence n DIV b <= n DIV 2          by DIV_LE_MONOTONE_REVERSE
       or        m <= n DIV 2          by m = MAX_SET t = n DIV b
*)

Theorem less_divisors_max:
  !n. MAX_SET (less_divisors n) <= n DIV 2
Proof
  rpt strip_tac >>
  qabbrev_tac `s = less_divisors n` >>
  qabbrev_tac `m = MAX_SET s` >>
  Cases_on `s = {}` >- rw[MAX_SET_EMPTY, Abbr`m`] >>
  `n <> 0 /\ n <> 1` by metis_tac[less_divisors_0, less_divisors_1] >>
  `1 < n` by decide_tac >>
  `1 IN s` by rw[less_divisors_has_1, Abbr`s`] >>
  qabbrev_tac `t = proper_divisors n` >>
  `t = s DELETE 1`  by rw[proper_divisors_by_less_divisors, Abbr`t`, Abbr`s`] >>
  Cases_on `t = {}` >| [
    `s = {1}` by rfs[] >>
    `m = 1` by rw[MAX_SET_SING, Abbr`m`] >>
    `(2 <= n) /\ (0 < 2) /\ (0 < n) /\ (n DIV n = 1)` by rw[] >>
    metis_tac[DIV_LE_MONOTONE_REVERSE],
    qabbrev_tac `b = MIN_SET t` >>
    `MAX_SET t = n DIV b` by metis_tac[proper_divisors_max_min] >>
    `MIN_SET s = 1` by rw[less_divisors_min, Abbr`s`] >>
    `FINITE s` by rw[less_divisors_finite, Abbr`s`] >>
    `s <> {1}` by metis_tac[DELETE_EQ_SING] >>
    `m = MAX_SET t` by metis_tac[MAX_SET_DELETE] >>
    `1 < b` by rw[proper_divisors_min_gt_1, Abbr`b`, Abbr`t`] >>
    `2 <= b /\ (0 < b) /\ (0 < 2)` by decide_tac >>
    `n DIV b <= n DIV 2` by rw[DIV_LE_MONOTONE_REVERSE] >>
    decide_tac
  ]
QED

(* Theorem: (less_divisors n) SUBSET (natural (n DIV 2)) *)
(* Proof:
   Let s = less_divisors n
   If n = 0 or n - 1,
   Then s = {}                        by less_divisors_0, less_divisors_1
    and {} SUBSET t, for any t.       by EMPTY_SUBSET
   If n <> 0 and n <> 1, 1 < n.
   Note FINITE s                      by less_divisors_finite
    and x IN s ==> x <= MAX_SET s     by MAX_SET_PROPERTY, FINITE s
    But MAX_SET s <= n DIV 2          by less_divisors_max
   Thus x IN s ==> x <= n DIV 2       by LESS_EQ_TRANS
   Note s <> {}                       by MEMBER_NOT_EMPTY, x IN s
    and x IN s ==> MIN_SET s <= x     by MIN_SET_PROPERTY, s <> {}
  Since 1 = MIN_SET s, 1 <= x         by less_divisors_min, 1 < n
   Thus 0 < x <= n DIV 2              by LESS_EQ
     or x IN (natural (n DIV 2))      by natural_element
*)
val less_divisors_subset_natural = store_thm(
  "less_divisors_subset_natural",
  ``!n. (less_divisors n) SUBSET (natural (n DIV 2))``,
  rpt strip_tac >>
  qabbrev_tac `s = less_divisors n` >>
  qabbrev_tac `m = n DIV 2` >>
  Cases_on `(n = 0) \/ (n = 1)` >-
  metis_tac[less_divisors_0, less_divisors_1, EMPTY_SUBSET] >>
  `1 < n` by decide_tac >>
  rw_tac std_ss[SUBSET_DEF] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `FINITE s` by rw[less_divisors_finite, Abbr`s`] >>
  `x <= MAX_SET s` by rw[MAX_SET_PROPERTY] >>
  `MIN_SET s <= x` by rw[MIN_SET_PROPERTY] >>
  `MAX_SET s <= m` by rw[less_divisors_max, Abbr`s`, Abbr`m`] >>
  `MIN_SET s = 1` by rw[less_divisors_min, Abbr`s`] >>
  `0 < x /\ x <= m` by decide_tac >>
  rw[natural_element]);

(* ------------------------------------------------------------------------- *)
(* Properties of Summation equals Perfect Power                              *)
(* ------------------------------------------------------------------------- *)

(* Idea for the theorem below (for m = n DIV 2 when applied in bounds):
      p * (p ** m - 1) / (p - 1)
   <  p * p ** m / (p - 1)        discard subtraction
   <= p * p ** m / (p / 2)        replace by smaller denominator
    = 2 * p ** m                  double division and cancel p
   or p * (p ** m - 1) < (p - 1) * 2 * p ** m
*)

(* Theorem: 1 < p ==> !n. p * (p ** n - 1) < (p - 1) * (2 * p ** n) *)
(* Proof:
   Let q = p ** n
   Then 1 <= q                       by ONE_LE_EXP, 0 < p
     so p <= p * q                   by LE_MULT_LCANCEL, p <> 0
   Also 1 < p ==> 2 <= p             by LESS_EQ
     so 2 * q <= p * q               by LE_MULT_RCANCEL, q <> 0
   Thus   LHS
        = p * (q - 1)
        = p * q - p                  by LEFT_SUB_DISTRIB
    And   RHS
        = (p - 1) * (2 * q)
        = p * (2 * q) - 2 * q        by RIGHT_SUB_DISTRIB
        = 2 * (p * q) - 2 * q        by MULT_ASSOC, MULT_COMM
        = (p * q + p * q) - 2 * q    by TIMES2
        = (p * q - p + p + p * q) - 2 * q  by SUB_ADD, p <= p * q
        = LHS + p + p * q - 2 * q    by above
        = LHS + p + (p * q - 2 * q)  by LESS_EQ_ADD_SUB, 2 * q <= p * q
        = LHS + p + (p - 2) * q      by RIGHT_SUB_DISTRIB

    Since 0 < p                      by 1 < p
      and 0 <= (p - 2) * q           by 2 <= p
    Hence LHS < RHS                  by discarding positive terms
*)
val perfect_power_special_inequality = store_thm(
  "perfect_power_special_inequality",
  ``!p. 1 < p ==> !n. p * (p ** n - 1) < (p - 1) * (2 * p ** n)``,
  rpt strip_tac >>
  qabbrev_tac `q = p ** n` >>
  `p <> 0 /\ 2 <= p` by decide_tac >>
  `1 <= q` by rw[ONE_LE_EXP, Abbr`q`] >>
  `p <= p * q` by rw[] >>
  `2 * q <= p * q` by rw[] >>
  qabbrev_tac `l = p * (q - 1)` >>
  qabbrev_tac `r = (p - 1) * (2 * q)` >>
  `l = p * q - p` by rw[Abbr`l`] >>
  `r = p * (2 * q) - 2 * q` by rw[Abbr`r`] >>
  `_ = 2 * (p * q) - 2 * q` by rw[] >>
  `_ = (p * q + p * q) - 2 * q` by rw[] >>
  `_ = (p * q - p + p + p * q) - 2 * q` by rw[] >>
  `_ = l + p + p * q - 2 * q` by rw[] >>
  `_ = l + p + (p * q - 2 * q)` by rw[] >>
  `_ = l + p + (p - 2) * q` by rw[] >>
  decide_tac);

(* Theorem: 1 < p /\ 1 < n ==>
            p ** (n DIV 2) * p ** (n DIV 2) <= p ** n /\
            2 * p ** (n DIV 2) <= p ** (n DIV 2) * p ** (n DIV 2) *)
(* Proof:
   Let m = n DIV 2, q = p ** m.
   The goal becomes: q * q <= p ** n /\ 2 * q <= q * q.
      Note 1 < p ==> 0 < p.
   First goal: q * q <= p ** n
      Then 0 < q                    by EXP_POS, 0 < p
       and 2 * m <= n               by DIV_MULT_LE, 0 < 2.
      thus p ** (2 * m) <= p ** n   by EXP_BASE_LE_MONO, 1 < p.
     Since p ** (2 * m)
         = p ** (m + m)             by TIMES2
         = q * q                    by EXP_ADD
      Thus q * q <= p ** n          by above

   Second goal: 2 * q <= q * q
     Since 1 < n, so 2 <= n         by LESS_EQ
        so 2 DIV 2 <= n DIV 2       by DIV_LE_MONOTONE, 0 < 2.
        or 1 <= m, i.e. 0 < m       by DIVMOD_ID, 0 < 2.
      Thus 1 < q                    by ONE_LT_EXP, 1 < p, 0 < m.
        so 2 <= q                   by LESS_EQ
       and 2 * q <= q * q           by MULT_RIGHT_CANCEL, q <> 0.
     Hence 2 * q <= p ** n          by LESS_EQ_TRANS
*)
val perfect_power_half_inequality_lemma = prove(
  ``!p n. 1 < p /\ 1 < n ==>
         p ** (n DIV 2) * p ** (n DIV 2) <= p ** n /\
         2 * p ** (n DIV 2) <= p ** (n DIV 2) * p ** (n DIV 2)``,
  ntac 3 strip_tac >>
  qabbrev_tac `m = n DIV 2` >>
  qabbrev_tac `q = p ** m` >>
  strip_tac >| [
    `0 < p /\ 0 < 2` by decide_tac >>
    `0 < q /\ q <> 0` by rw[EXP_POS, Abbr`q`] >>
    `2 * m <= n` by metis_tac[DIV_MULT_LE, MULT_COMM] >>
    `p ** (2 * m) <= p ** n` by rw[EXP_BASE_LE_MONO] >>
    `p ** (2 * m) = p ** (m + m)` by rw[] >>
    `_ = q * q` by rw[EXP_ADD, Abbr`q`] >>
    decide_tac,
    `2 <= n /\ 0 < 2` by decide_tac >>
    `1 <= m` by metis_tac[DIV_LE_MONOTONE, DIVMOD_ID] >>
    `0 < m` by decide_tac >>
    `1 < q` by rw[ONE_LT_EXP, Abbr`q`] >>
    rw[]
  ]);

(* Theorem: 1 < p /\ 0 < n ==> 2 * p ** (n DIV 2) <= p ** n *)
(* Proof:
   Let m = n DIV 2, q = p ** m.
   The goal becomes: 2 * q <= p ** n
   If n = 1,
      Then m = 0                    by ONE_DIV, 0 < 2.
       and q = 1                    by EXP
       and p ** n = p               by EXP_1
     Since 1 < p ==> 2 <= p         by LESS_EQ
     Hence 2 * q <= p = p ** n      by MULT_RIGHT_1
   If n <> 1, 1 < n.
      Then q * q <= p ** n /\
           2 * q <= q * q           by perfect_power_half_inequality_lemma
     Hence 2 * q <= p ** n          by LESS_EQ_TRANS
*)
val perfect_power_half_inequality_1 = store_thm(
  "perfect_power_half_inequality_1",
  ``!p n. 1 < p /\ 0 < n ==> 2 * p ** (n DIV 2) <= p ** n``,
  rpt strip_tac >>
  qabbrev_tac `m = n DIV 2` >>
  qabbrev_tac `q = p ** m` >>
  Cases_on `n = 1` >| [
    `m = 0` by rw[Abbr`m`] >>
    `(q = 1) /\ (p ** n = p)` by rw[Abbr`q`] >>
    `2 <= p` by decide_tac >>
    rw[],
    `1 < n` by decide_tac >>
    `q * q <= p ** n /\ 2 * q <= q * q` by rw[perfect_power_half_inequality_lemma, Abbr`q`, Abbr`m`] >>
    decide_tac
  ]);

(* Theorem: 1 < p /\ 0 < n ==> (p ** (n DIV 2) - 2) * p ** (n DIV 2) <= p ** n - 2 * p ** (n DIV 2) *)
(* Proof:
   Let m = n DIV 2, q = p ** m.
   The goal becomes: (q - 2) * q <= p ** n - 2 * q
   If n = 1,
      Then m = 0                    by ONE_DIV, 0 < 2.
       and q = 1                    by EXP
       and p ** n = p               by EXP_1
     Since 1 < p ==> 2 <= p         by LESS_EQ
        or 0 <= p - 2               by SUB_LEFT_LESS_EQ
     Hence (q - 2) * q = 0 <= p - 2
   If n <> 1, 1 < n.
      Then q * q <= p ** n /\ 2 * q <= q * q   by perfect_power_half_inequality_lemma
      Thus q * q - 2 * q <= p ** n - 2 * q     by LE_SUB_RCANCEL, 2 * q <= q * q
        or   (q - 2) * q <= p ** n - 2 * q     by RIGHT_SUB_DISTRIB
*)
val perfect_power_half_inequality_2 = store_thm(
  "perfect_power_half_inequality_2",
  ``!p n. 1 < p /\ 0 < n ==> (p ** (n DIV 2) - 2) * p ** (n DIV 2) <= p ** n - 2 * p ** (n DIV 2)``,
  rpt strip_tac >>
  qabbrev_tac `m = n DIV 2` >>
  qabbrev_tac `q = p ** m` >>
  Cases_on `n = 1` >| [
    `m = 0` by rw[Abbr`m`] >>
    `(q = 1) /\ (p ** n = p)` by rw[Abbr`q`] >>
    `0 <= p - 2 /\ (1 - 2 = 0)` by decide_tac >>
    rw[],
    `1 < n` by decide_tac >>
    `q * q <= p ** n /\ 2 * q <= q * q` by rw[perfect_power_half_inequality_lemma, Abbr`q`, Abbr`m`] >>
    decide_tac
  ]);

(* Already in pred_setTheory:
SUM_IMAGE_SUBSET_LE;
!f s t. FINITE s /\ t SUBSET s ==> SIGMA f t <= SIGMA f s: thm
SUM_IMAGE_MONO_LESS_EQ;
|- !s. FINITE s ==> (!x. x IN s ==> f x <= g x) ==> SIGMA f s <= SIGMA g s: thm
*)

(* Theorem: 1 < p ==> !f. (!n. 0 < n ==> (p ** n = SIGMA (\d. d * f d) (divisors n))) ==>
            (!n. 0 < n ==> n * (f n) <= p ** n) /\
            (!n. 0 < n ==> p ** n - 2 * p ** (n DIV 2) < n * (f n)) *)
(* Proof:
   Step 1: prove a specific lemma for sum decomposition
   Claim: !n. 0 < n ==> (divisors n DIFF {n}) SUBSET (natural (n DIV 2)) /\
          (p ** n = SIGMA (\d. d * f d) (divisors n)) ==>
          (p ** n = n * f n + SIGMA (\d. d * f d) (divisors n DIFF {n}))
   Proof: Let s = divisors n, a = {n}, b = s DIFF a, m = n DIV 2.
          Then b = less_divisors n        by EXTENSION,IN_DIFF
           and b SUBSET (natural m)       by less_divisors_subset_natural
          This gives the first part.
          For the second part:
          Note a SUBSET s                 by divisors_has_last, SUBSET_DEF
           and b SUBSET s                 by DIFF_SUBSET
          Thus s = b UNION a              by UNION_DIFF, a SUBSET s
           and DISJOINT b a               by DISJOINT_DEF, EXTENSION
           Now FINITE s                   by divisors_finite
            so FINITE a /\ FINITE b       by SUBSET_FINITE, by a SUBSEt s /\ b SUBSET s

               p ** n
             = SIGMA (\d. d * f d) s              by implication
             = SIGMA (\d. d * f d) (b UNION a)    by above, s = b UNION a
             = SIGMA (\d. d * f d) b + SIGMA (\d. d * f d) a   by SUM_IMAGE_DISJOINT, FINITE a /\ FINITE b
             = SIGMA (\d. d * f d) b + n * f n    by SUM_IMAGE_SING
             = n * f n + SIGMA (\d. d * f d) b    by ADD_COMM
          This gives the second part.

   Step 2: Upper bound, to show: !n. 0 < n ==> n * f n <= p ** n
           Let b = divisors n DIFF {n}
           Since n * f n + SIGMA (\d. d * f d) b = p ** n    by lemma
           Hence n * f n <= p ** n                           by 0 <= SIGMA (\d. d * f d) b

   Step 3: Lower bound, to show: !n. 0 < n ==> p ** n - p ** (n DIV 2) <= n * f n
           Let s = divisors n, a = {n}, b = s DIFF a, m = n DIV 2.
            Note b SUBSET (natural m) /\
                 (p ** n = n * f n + SIGMA (\d. d * f d) b)  by lemma
           Since FINITE (natural m)                          by natural_finite
            thus SIGMA (\d. d * f d) b
              <= SIGMA (\d. d * f d) (natural m)             by SUM_IMAGE_SUBSET_LE [1]
            Also !d. d IN (natural m) ==> 0 < d              by natural_element
             and !d. 0 < d ==> d * f d <= p ** d             by upper bound (Step 2)
            thus !d. d IN (natural m) ==> d * f d <= p ** d  by implication
           Hence SIGMA (\d. d * f d) (natural m)
              <= SIGMA (\d. p ** d) (natural m)              by SUM_IMAGE_MONO_LESS_EQ [2]
             Now 1 < p ==> 0 < p /\ (p - 1) <> 0             by arithmetic

             (p - 1) * SIGMA (\d. d * f d) b
          <= (p - 1) * SIGMA (\d. d * f d) (natural m)       by LE_MULT_LCANCEL, [1]
          <= (p - 1) * SIGMA (\d. p ** d) (natural m)        by LE_MULT_LCANCEL, [2]
           = p * (p ** m - 1)                                by sigma_geometric_natural_eqn
           < (p - 1) * (2 * p ** m)                          by perfect_power_special_inequality

             (p - 1) * SIGMA (\d. d * f d) b < (p - 1) * (2 * p ** m)   by LESS_EQ_LESS_TRANS
             or        SIGMA (\d. d * f d) b < 2 * p ** m               by LT_MULT_LCANCEL, (p - 1) <> 0

            But 2 * p ** m <= p ** n                         by perfect_power_half_inequality_1, 1 < p, 0 < n
           Thus p ** n = p ** n - 2 * p ** m + 2 * p ** m    by SUB_ADD, 2 * p ** m <= p ** n
       Combinig with lemma,
           p ** n - 2 * p ** m + 2 * p ** m < n * f n + 2 * p ** m
             or         p ** n - 2 * p ** m < n * f n        by LESS_MONO_ADD_EQ, no condition
*)
Theorem sigma_eq_perfect_power_bounds_1:
  !p.
    1 < p ==>
    !f. (!n. 0 < n ==> (p ** n = SIGMA (\d. d * f d) (divisors n))) ==>
        (!n. 0 < n ==> n * (f n) <= p ** n) /\
        (!n. 0 < n ==> p ** n - 2 * p ** (n DIV 2) < n * (f n))
Proof
  ntac 4 strip_tac >>
  ‘!n. 0 < n ==>
       (divisors n DIFF {n}) SUBSET (natural (n DIV 2)) /\
       (p ** n = SIGMA (\d. d * f d) (divisors n) ==>
        p ** n = n * f n + SIGMA (\d. d * f d) (divisors n DIFF {n}))’
    by (ntac 2 strip_tac >>
        qabbrev_tac `s = divisors n` >>
        qabbrev_tac `a = {n}` >>
        qabbrev_tac `b = s DIFF a` >>
        qabbrev_tac `m = n DIV 2` >>
        `b = less_divisors n` by rw[EXTENSION, Abbr`b`, Abbr`a`, Abbr`s`] >>
        `b SUBSET (natural m)` by metis_tac[less_divisors_subset_natural] >>
        strip_tac >- rw[] >>
        `a SUBSET s` by rw[divisors_has_last, SUBSET_DEF, Abbr`s`, Abbr`a`] >>
        `b SUBSET s` by rw[Abbr`b`] >>
        `s = b UNION a` by rw[UNION_DIFF, Abbr`b`] >>
        `DISJOINT b a`
          by (rw[DISJOINT_DEF, Abbr`b`, EXTENSION] >> metis_tac[]) >>
        `FINITE s` by rw[divisors_finite, Abbr`s`] >>
        `FINITE a /\ FINITE b` by metis_tac[SUBSET_FINITE] >>
        strip_tac >>
        `_ = SIGMA (\d. d * f d) (b UNION a)` by metis_tac[Abbr`s`] >>
        `_ = SIGMA (\d. d * f d) b + SIGMA (\d. d * f d) a`
          by rw[SUM_IMAGE_DISJOINT] >>
        `_ = SIGMA (\d. d * f d) b + n * f n` by rw[SUM_IMAGE_SING, Abbr`a`] >>
        rw[]) >>
  conj_asm1_tac >| [
    rpt strip_tac >>
    `p ** n = n * f n + SIGMA (\d. d * f d) (divisors n DIFF {n})` by rw[] >>
    decide_tac,
    rpt strip_tac >>
    qabbrev_tac `s = divisors n` >>
    qabbrev_tac `a = {n}` >>
    qabbrev_tac `b = s DIFF a` >>
    qabbrev_tac `m = n DIV 2` >>
    `b SUBSET (natural m) /\ (p ** n = n * f n + SIGMA (\d. d * f d) b)`
      by rw[Abbr`s`, Abbr`a`, Abbr`b`, Abbr`m`] >>
    `FINITE (natural m)` by rw[natural_finite] >>
    `SIGMA (\d. d * f d) b <= SIGMA (\d. d * f d) (natural m)`
      by rw[SUM_IMAGE_SUBSET_LE] >>
    `!d. d IN (natural m) ==> 0 < d` by rw[natural_element] >>
    `SIGMA (\d. d * f d) (natural m) <= SIGMA (\d. p ** d) (natural m)`
      by rw[SUM_IMAGE_MONO_LESS_EQ] >>
    `0 < p /\ (p - 1) <> 0` by decide_tac >>
    `(p - 1) * SIGMA (\d. p ** d) (natural m) = p * (p ** m - 1)`
      by rw[sigma_geometric_natural_eqn] >>
    `p * (p ** m - 1) < (p - 1) * (2 * p ** m)`
      by rw[perfect_power_special_inequality] >>
    `SIGMA (\d. d * f d) b < 2 * p ** m`
      by metis_tac[LE_MULT_LCANCEL, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS,
                   LT_MULT_LCANCEL] >>
    `p ** n < n * f n + 2 * p ** m` by decide_tac >>
    `2 * p ** m <= p ** n` by rw[perfect_power_half_inequality_1, Abbr`m`] >>
    decide_tac
  ]
QED

(* Theorem: 1 < p ==> !f. (!n. 0 < n ==> (p ** n = SIGMA (\d. d * f d) (divisors n))) ==>
            (!n. 0 < n ==> n * (f n) <= p ** n) /\
            (!n. 0 < n ==> (p ** (n DIV 2) - 2) * p ** (n DIV 2) < n * (f n)) *)
(* Proof:
   For the first goal: (!n. 0 < n ==> n * (f n) <= p ** n)
       True by sigma_eq_perfect_power_bounds_1.
   For the second goal: (!n. 0 < n ==> (p ** (n DIV 2) - 2) * p ** (n DIV 2) < n * (f n))
       Let m = n DIV 2.
       Then p ** n - 2 * p ** m < n * (f n)                     by sigma_eq_perfect_power_bounds_1
        and (p ** m - 2) * p ** m <= p ** n - 2 * p ** m        by perfect_power_half_inequality_2
      Hence (p ** (n DIV 2) - 2) * p ** (n DIV 2) < n * (f n)   by LESS_EQ_LESS_TRANS
*)
val sigma_eq_perfect_power_bounds_2 = store_thm(
  "sigma_eq_perfect_power_bounds_2",
  ``!p. 1 < p ==> !f. (!n. 0 < n ==> (p ** n = SIGMA (\d. d * f d) (divisors n))) ==>
   (!n. 0 < n ==> n * (f n) <= p ** n) /\
   (!n. 0 < n ==> (p ** (n DIV 2) - 2) * p ** (n DIV 2) < n * (f n))``,
  rpt strip_tac >-
  rw[sigma_eq_perfect_power_bounds_1] >>
  qabbrev_tac `m = n DIV 2` >>
  `p ** n - 2 * p ** m < n * (f n)` by rw[sigma_eq_perfect_power_bounds_1, Abbr`m`] >>
  `(p ** m - 2) * p ** m <= p ** n - 2 * p ** m` by rw[perfect_power_half_inequality_2, Abbr`m`] >>
  decide_tac);

(* This is a milestone theorem. *)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
