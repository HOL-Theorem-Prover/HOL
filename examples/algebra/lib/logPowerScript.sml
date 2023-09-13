(* ------------------------------------------------------------------------- *)
(* Integer Functions Computation.                                            *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "logPower";

(* ------------------------------------------------------------------------- *)



(* val _ = load "jcLib"; *)
open jcLib;

(* val _ = load "SatisfySimps"; (* for SatisfySimps.SATISFY_ss *) *)

(* Get dependent theories local *)

(* Get dependent theories in lib *)
(* val _ = load "helperNumTheory"; *)
open helperNumTheory;

(* val _ = load "helperFunctionTheory"; *)
open helperFunctionTheory;
open pred_setTheory;
open helperSetTheory;

(* open dependent theories *)
open arithmeticTheory;
open dividesTheory gcdTheory;

(* val _ = load "logrootTheory"; *)
open logrootTheory; (* for ROOT *)


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
   power_free_check_upto_LOG2  |- !n. power_free n <=> 1 < n /\ n power_free_upto LOG2 n
   power_free_check_upto_ulog  |- !n. power_free n <=> 1 < n /\ n power_free_upto ulog n
   power_free_check_upto       |- !n b. LOG2 n <= b ==> (power_free n <=> 1 < n /\ n power_free_upto b)
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

(* ------------------------------------------------------------------------- *)
(* ROOT Computation                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: ROOT n (a ** n) = a *)
(* Proof:
   Since   a < SUC a         by LESS_SUC
      a ** n < (SUC a) ** n  by EXP_BASE_LT_MONO
   Let b = a ** n,
   Then  a ** n <= b         by LESS_EQ_REFL
    and  b < (SUC a) ** n    by above
   Hence a = ROOT n b        by ROOT_UNIQUE
*)
val ROOT_POWER = store_thm(
  "ROOT_POWER",
  ``!a n. 1 < a /\ 0 < n ==> (ROOT n (a ** n) = a)``,
  rw[EXP_BASE_LT_MONO, ROOT_UNIQUE]);

(* Theorem: 0 < m /\ (b ** m = n) ==> (b = ROOT m n) *)
(* Proof:
   Note n <= n                  by LESS_EQ_REFL
     so b ** m <= n             by b ** m = n
   Also b < SUC b               by LESS_SUC
     so b ** m < (SUC b) ** m   by EXP_EXP_LT_MONO, 0 < m
     so n < (SUC b) ** m        by b ** m = n
   Thus b = ROOT m n            by ROOT_UNIQUE
*)
val ROOT_FROM_POWER = store_thm(
  "ROOT_FROM_POWER",
  ``!m n b. 0 < m /\ (b ** m = n) ==> (b = ROOT m n)``,
  rpt strip_tac >>
  rw[ROOT_UNIQUE]);

(* Theorem: 0 < m ==> (ROOT m 0 = 0) *)
(* Proof:
   Note 0 ** m = 0    by EXP_0
   Thus 0 = ROOT m 0  by ROOT_FROM_POWER
*)
val ROOT_OF_0 = store_thm(
  "ROOT_OF_0[simp]",
  ``!m. 0 < m ==> (ROOT m 0 = 0)``,
  rw[ROOT_FROM_POWER]);

(* Theorem: 0 < m ==> (ROOT m 1 = 1) *)
(* Proof:
   Note 1 ** m = 1    by EXP_1
   Thus 1 = ROOT m 1  by ROOT_FROM_POWER
*)
val ROOT_OF_1 = store_thm(
  "ROOT_OF_1[simp]",
  ``!m. 0 < m ==> (ROOT m 1 = 1)``,
  rw[ROOT_FROM_POWER]);

(* Theorem: 0 < r ==> !n p. (ROOT r n = p) <=> (p ** r <= n /\ n < SUC p ** r) *)
(* Proof:
   If part: 0 < r ==> ROOT r n ** r <= n /\ n < SUC (ROOT r n) ** r
      This is true             by ROOT, 0 < r
   Only-if part: p ** r <= n /\ n < SUC p ** r ==> ROOT r n = p
      This is true             by ROOT_UNIQUE
*)
val ROOT_THM = store_thm(
  "ROOT_THM",
  ``!r. 0 < r ==> !n p. (ROOT r n = p) <=> (p ** r <= n /\ n < SUC p ** r)``,
  metis_tac[ROOT, ROOT_UNIQUE]);

(* Rework proof of ROOT_COMPUTE in logroot theory. *)
(* ./num/extra_theories/logrootScript.sml *)

(* ROOT r n = r-th root of n.

Make use of indentity:
n ^ (1/r) = 2 (n/ 2^r) ^(1/r)

if n = 0 then 0
else (* precompute *) let x = 2 * r-th root of (n DIV (2 ** r))
     (* apply *) in if n < (SUC x) ** r then x else (SUC x)
*)

(*

val lem = prove(``0 < r ==> (0 ** r = 0)``, RW_TAC arith_ss [EXP_EQ_0]);

val ROOT_COMPUTE = Q.store_thm("ROOT_COMPUTE",
   `!r n.
       0 < r ==>
       (ROOT r 0 = 0) /\
       (ROOT r n = let x = 2 * ROOT r (n DIV 2 ** r) in
                      if n < SUC x ** r then x else SUC x)`,
   RW_TAC (arith_ss ++ boolSimps.LET_ss) []
   THEN MATCH_MP_TAC ROOT_UNIQUE
   THEN CONJ_TAC
   THEN FULL_SIMP_TAC arith_ss [NOT_LESS, EXP_1, lem]
   THEN MAP_FIRST MATCH_MP_TAC
          [LESS_EQ_TRANS, DECIDE ``!a b c. a < b /\ b <= c ==> a < c``]
   THENL [
      Q.EXISTS_TAC `ROOT r n ** r`,
      Q.EXISTS_TAC `SUC (ROOT r n) ** r`]
   THEN RW_TAC arith_ss
           [ROOT, GSYM EXP_LE_ISO, GSYM ROOT_DIV, DECIDE ``0 < 2n``]
   THEN METIS_TAC
           [DIVISION, MULT_COMM, DECIDE ``0 < 2n``,
            DECIDE ``(a = b + c) ==> b <= a:num``, ADD1, LE_ADD_LCANCEL,
            DECIDE ``a <= 1 = a < 2n``]);

> ROOT_COMPUTE;
val it =
   |- !r n.
     0 < r ==>
     (ROOT r 0 = 0) /\
     (ROOT r n =
      (let x = 2 * ROOT r (n DIV 2 ** r)
       in
         if n < SUC x ** r then x else SUC x)):
   thm
*)

(* Theorem: 0 < m ==> !n. (ROOT m n = 0) <=> (n = 0) *)
(* Proof:
   If part: ROOT m n = 0 ==> n = 0
      Note n < SUC (ROOT m n) ** r      by ROOT
        or n < SUC 0 ** m               by ROOT m n = 0
        so n < 1                        by ONE, EXP_1
        or n = 0                        by arithmetic
   Only-if part: ROOT m 0 = 0, true     by ROOT_OF_0
*)
val ROOT_EQ_0 = store_thm(
  "ROOT_EQ_0",
  ``!m. 0 < m ==> !n. (ROOT m n = 0) <=> (n = 0)``,
  rw[EQ_IMP_THM] >>
  `n < 1` by metis_tac[ROOT, EXP_1, ONE] >>
  decide_tac);

(* Theorem: ROOT 1 n = n *)
(* Proof:
   Note n ** 1 = n      by EXP_1
     so n ** 1 <= n
   Also n < SUC n       by LESS_SUC
     so n < SUC n ** 1  by EXP_1
   Thus ROOT 1 n = n    by ROOT_UNIQUE
*)
val ROOT_1 = store_thm(
  "ROOT_1[simp]",
  ``!n. ROOT 1 n = n``,
  rw[ROOT_UNIQUE]);


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


(* Theorem: 0 < r ==>
            (ROOT r (SUC n) = ROOT r n + if SUC n = (SUC (ROOT r n)) ** r then 1 else 0) *)
(* Proof:
   Let x = ROOT r n, y = ROOT r (SUC n).  x <= y.
   Note n < (SUC x) ** r /\ x ** r <= n          by ROOT_THM
    and SUC n < (SUC y) ** r /\ y ** r <= SUC n  by ROOT_THM
   Since n < (SUC x) ** r,
    SUC n <= (SUC x) ** r.
   If SUC n = (SUC x) ** r,
      Then y = ROOT r (SUC n)
             = ROOT r ((SUC x) ** r)
             = SUC x                             by ROOT_POWER
   If SUC n < (SUC x) ** r,
      Then x ** r <= n < SUC n                   by LESS_SUC
      Thus x = y                                 by ROOT_THM
*)
val ROOT_SUC = store_thm(
  "ROOT_SUC",
  ``!r n. 0 < r ==>
   (ROOT r (SUC n) = ROOT r n + if SUC n = (SUC (ROOT r n)) ** r then 1 else 0)``,
  rpt strip_tac >>
  qabbrev_tac `x = ROOT r n` >>
  qabbrev_tac `y = ROOT r (SUC n)` >>
  Cases_on `n = 0` >| [
    `x = 0` by rw[ROOT_OF_0, Abbr`x`] >>
    `y = 1` by rw[ROOT_OF_1, Abbr`y`] >>
    simp[],
    `x <> 0` by rw[ROOT_EQ_0, Abbr`x`] >>
    `n < (SUC x) ** r /\ x ** r <= n` by metis_tac[ROOT_THM] >>
    `SUC n < (SUC y) ** r /\ y ** r <= SUC n` by metis_tac[ROOT_THM] >>
    `(SUC n = (SUC x) ** r) \/ SUC n < (SUC x) ** r` by decide_tac >| [
      `1 < SUC x` by decide_tac >>
      `y = SUC x` by metis_tac[ROOT_POWER] >>
      simp[],
      `x ** r <= SUC n` by decide_tac >>
      `x = y` by metis_tac[ROOT_THM] >>
      simp[]
    ]
  ]);

(*
ROOT_SUC;
|- !r n. 0 < r ==> ROOT r (SUC n) = ROOT r n + if SUC n = SUC (ROOT r n) ** r then 1 else 0
Let z = ROOT r n.

   z(n)
   -------------------------------------------------
                      n   (n+1=(z+1)**r)

> EVAL ``MAP (ROOT 2) [1 .. 20]``;
val it = |- MAP (ROOT 2) [1 .. 20] =
      [1; 1; 1; 2; 2; 2; 2; 2; 3; 3; 3; 3; 3; 3; 3; 4; 4; 4; 4; 4]: thm
       1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 20
*)

(* Theorem: 0 < m ==> !n. (ROOT m n = 1) <=> (0 < n /\ n < 2 ** m) *)
(* Proof:
       ROOT m n = 1
   <=> 1 ** m <= n /\ n < (SUC 1) ** m    by ROOT_THM, 0 < m
   <=> 1 <= n /\ n < 2 ** m               by TWO, EXP_1
   <=> 0 < n /\ n < 2 ** m                by arithmetic
*)
val ROOT_EQ_1 = store_thm(
  "ROOT_EQ_1",
  ``!m. 0 < m ==> !n. (ROOT m n = 1) <=> (0 < n /\ n < 2 ** m)``,
  rpt strip_tac >>
  `!n. 0 < n <=> 1 <= n` by decide_tac >>
  metis_tac[ROOT_THM, TWO, EXP_1]);

(* Theorem: 0 < m ==> ROOT m n <= n *)
(* Proof:
   Let r = ROOT m n.
   Note r <= r ** m   by X_LE_X_EXP, 0 < m
          <= n        by ROOT
*)
val ROOT_LE_SELF = store_thm(
  "ROOT_LE_SELF",
  ``!m n. 0 < m ==> ROOT m n <= n``,
  metis_tac[X_LE_X_EXP, ROOT, LESS_EQ_TRANS]);

(* Theorem: 0 < m ==> ((ROOT m n = n) <=> ((m = 1) \/ (n = 0) \/ (n = 1))) *)
(* Proof:
   If part: ROOT m n = n ==> m = 1 \/ n = 0 \/ n = 1
      Note n ** m <= n               by ROOT, 0 < r
       But n <= n ** m               by X_LE_X_EXP, 0 < m
        so n ** m = n                by EQ_LESS_EQ
       ==> m = 1 or n = 0 or n = 1   by EXP_EQ_SELF
   Only-if part: ROOT 1 n = n /\ ROOT m 0 = 0 /\ ROOT m 1 = 1
      True by ROOT_1, ROOT_OF_0, ROOT_OF_1.
*)
Theorem ROOT_EQ_SELF:
  !m n. 0 < m ==> (ROOT m n = n <=> m = 1 \/ n = 0 \/ n = 1)
Proof
  rw_tac std_ss[EQ_IMP_THM] >> rw[] >>
  `n ** m <= n` by metis_tac[ROOT] >>
  `n <= n ** m` by rw[X_LE_X_EXP] >>
  `n ** m = n` by decide_tac >>
  gs[]
QED

(* Theorem: 0 < m ==> (n <= ROOT m n <=> ((m = 1) \/ (n = 0) \/ (n = 1))) *)
(* Proof:
   Note ROOT m n <= n                     by ROOT_LE_SELF
   Thus n <= ROOT m n <=> ROOT m n = n    by EQ_LESS_EQ
   The result follows                     by ROOT_EQ_SELF
*)
val ROOT_GE_SELF = store_thm(
  "ROOT_GE_SELF",
  ``!m n. 0 < m ==> (n <= ROOT m n <=> ((m = 1) \/ (n = 0) \/ (n = 1)))``,
  metis_tac[ROOT_LE_SELF, ROOT_EQ_SELF, EQ_LESS_EQ]);

(*
EVAL ``MAP (\k. ROOT k 100)  [1 .. 10]``; = [100; 10; 4; 3; 2; 2; 1; 1; 1; 1]: thm

This shows (ROOT k) is a decreasing function of k,
but this is very hard to prove without some real number theory.
Even this is hard to prove: ROOT 3 n <= ROOT 2 n

No! -- this can be proved, see below.
*)

(* Theorem: 0 < a /\ a <= b ==> ROOT b n <= ROOT a n *)
(* Proof:
   Let x = ROOT a n, y = ROOT b n. To show: y <= x.
   By contradiction, suppose x < y.
   Then SUC x <= y.
   Note x ** a <= n /\ n < (SUC x) ** a     by ROOT
    and y ** b <= n /\ n < (SUC y) ** b     by ROOT
    But a <= b
        (SUC x) ** a
     <= (SUC x) ** b       by EXP_BASE_LEQ_MONO_IMP, 0 < SUC x, a <= b
     <=       y ** b       by EXP_EXP_LE_MONO, 0 < b
   This leads to n < (SUC x) ** a <= y ** b <= n, a contradiction.
*)
val ROOT_LE_REVERSE = store_thm(
  "ROOT_LE_REVERSE",
  ``!a b n. 0 < a /\ a <= b ==> ROOT b n <= ROOT a n``,
  rpt strip_tac >>
  qabbrev_tac `x = ROOT a n` >>
  qabbrev_tac `y = ROOT b n` >>
  spose_not_then strip_assume_tac >>
  `0 < b /\ SUC x <= y` by decide_tac >>
  `x ** a <= n /\ n < (SUC x) ** a` by rw[ROOT, Abbr`x`] >>
  `y ** b <= n /\ n < (SUC y) ** b` by rw[ROOT, Abbr`y`] >>
  `(SUC x) ** a <= (SUC x) ** b` by rw[EXP_BASE_LEQ_MONO_IMP] >>
  `(SUC x) ** b <= y ** b` by rw[EXP_EXP_LE_MONO] >>
  decide_tac);


(* ------------------------------------------------------------------------- *)
(* Square Root                                                               *)
(* ------------------------------------------------------------------------- *)
(* Use overload for SQRT *)
val _ = overload_on ("SQRT", ``\n. ROOT 2 n``);

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

(* Theorem: 0 < n ==> (SQRT n) ** 2 <= n /\ n < SUC (SQRT n) ** 2 *)
(* Proof: by ROOT:
   |- !r n. 0 < r ==> ROOT r n ** r <= n /\ n < SUC (ROOT r n) ** r
*)
val SQRT_PROPERTY = store_thm(
  "SQRT_PROPERTY",
  ``!n. (SQRT n) ** 2 <= n /\ n < SUC (SQRT n) ** 2``,
  rw[ROOT]);

(* Get a useful theorem *)
Theorem SQRT_UNIQUE = logrootTheory.ROOT_UNIQUE |> SPEC ``2``;
(* val SQRT_UNIQUE = |- !n p. p ** 2 <= n /\ n < SUC p ** 2 ==> SQRT n = p: thm *)

(* Obtain a theorem *)
val SQRT_THM = save_thm("SQRT_THM",
    ROOT_THM |> SPEC ``2`` |> SIMP_RULE (srw_ss())[]);
(* val SQRT_THM = |- !n p. (SQRT n = p) <=> p ** 2 <= n /\ n < SUC p ** 2: thm *)

(* Theorem: SQ (SQRT n) <= n *)
(* Proof: by SQRT_PROPERTY, EXP_2 *)
val SQ_SQRT_LE = store_thm(
  "SQ_SQRT_LE",
  ``!n. SQ (SQRT n) <= n``,
  metis_tac[SQRT_PROPERTY, EXP_2]);

(* Theorem: n <= m ==> SQRT n <= SQRT m *)
(* Proof: by ROOT_LE_MONO *)
val SQRT_LE = store_thm(
  "SQRT_LE",
  ``!n m. n <= m ==> SQRT n <= SQRT m``,
  rw[ROOT_LE_MONO]);

(* Theorem: n < m ==> SQRT n <= SQRT m *)
(* Proof:
   Since n < m ==> n <= m   by LESS_IMP_LESS_OR_EQ
   This is true             by ROOT_LE_MONO
*)
val SQRT_LT = store_thm(
  "SQRT_LT",
  ``!n m. n < m ==> SQRT n <= SQRT m``,
  rw[ROOT_LE_MONO, LESS_IMP_LESS_OR_EQ]);

(* Extract theorem *)
Theorem SQ_SQRT_LE_alt = SQRT_PROPERTY |> SPEC_ALL |> CONJUNCT1 |> GEN_ALL;
(* val SQ_SQRT_LE_alt = |- !n. SQRT n ** 2 <= n: thm *)

(* Theorem: SQRT 0 = 0 *)
(* Proof: by ROOT_OF_0 *)
val SQRT_0 = store_thm(
  "SQRT_0[simp]",
  ``SQRT 0 = 0``,
  rw[]);

(* Theorem: SQRT 1 = 1 *)
(* Proof: by ROOT_OF_1 *)
val SQRT_1 = store_thm(
  "SQRT_1[simp]",
  ``SQRT 1 = 1``,
  rw[]);

(* Theorem: SQRT n = 0 <=> n = 0 *)
(* Proof:
   If part: SQRT n = 0 ==> n = 0.
   By contradiction, suppose n <> 0.
      This means 1 <= n
      Hence  SQRT 1 <= SQRT n   by SQRT_LE
         so       1 <= SQRT n   by SQRT_1
      This contradicts SQRT n = 0.
   Only-if part: n = 0 ==> SQRT n = 0
      True since SQRT 0 = 0     by SQRT_0
*)
val SQRT_EQ_0 = store_thm(
  "SQRT_EQ_0",
  ``!n. (SQRT n = 0) <=> (n = 0)``,
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  `1 <= n` by decide_tac >>
  `SQRT 1 <= SQRT n` by rw[SQRT_LE] >>
  `SQRT 1 = 1` by rw[] >>
  decide_tac);

(* Theorem: SQRT n = 1 <=> n = 1 \/ n = 2 \/ n = 3 *)
(* Proof:
   If part: SQRT n = 1 ==> (n = 1) \/ (n = 2) \/ (n = 3).
   By contradiction, suppose n <> 1 /\ n <> 2 /\ n <> 3.
      Note n <> 0    by SQRT_EQ_0
      This means 4 <= n
      Hence  SQRT 4 <= SQRT n   by SQRT_LE
         so       2 <= SQRT n   by EVAL_TAC, SQRT 4 = 2
      This contradicts SQRT n = 1.
   Only-if part: n = 1 \/ n = 2 \/ n = 3 ==> SQRT n = 1
      All these are true        by EVAL_TAC
*)
val SQRT_EQ_1 = store_thm(
  "SQRT_EQ_1",
  ``!n. (SQRT n = 1) <=> ((n = 1) \/ (n = 2) \/ (n = 3))``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `n <> 0` by metis_tac[SQRT_EQ_0] >>
    `4 <= n` by decide_tac >>
    `SQRT 4 <= SQRT n` by rw[SQRT_LE] >>
    `SQRT 4 = 2` by EVAL_TAC >>
    decide_tac,
    EVAL_TAC,
    EVAL_TAC,
    EVAL_TAC
  ]);

(* Theorem: SQRT (n ** 2) = n *)
(* Proof:
   If 1 < n, true                       by ROOT_POWER, 0 < 2
   Otherwise, n = 0 or n = 1.
      When n = 0,
           SQRT (0 ** 2) = SQRT 0 = 0   by SQRT_0
      When n = 1,
           SQRT (1 ** 2) = SQRT 1 = 1   by SQRT_1
*)
val SQRT_EXP_2 = store_thm(
  "SQRT_EXP_2",
  ``!n. SQRT (n ** 2) = n``,
  rpt strip_tac >>
  Cases_on `1 < n` >-
  fs[ROOT_POWER] >>
  `(n = 0) \/ (n = 1)` by decide_tac >>
  rw[]);

(* Theorem alias *)
val SQRT_OF_SQ = save_thm("SQRT_OF_SQ", SQRT_EXP_2);
(* val SQRT_OF_SQ = |- !n. SQRT (n ** 2) = n: thm *)

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

(* Theorem: (n <= SQRT n) <=> ((n = 0) \/ (n = 1)) *)
(* Proof:
   If part: (n <= SQRT n) ==> ((n = 0) \/ (n = 1))
     By contradiction, suppose n <> 0 /\ n <> 1.
     Then 1 < n, implying n ** 2 <= SQRT n ** 2   by EXP_BASE_LE_MONO
      but SQRT n ** 2 <= n                        by SQRT_PROPERTY
       so n ** 2 <= n                             by LESS_EQ_TRANS
       or n * n <= n * 1                          by EXP_2
       or     n <= 1                              by LE_MULT_LCANCEL, n <> 0.
     This contradicts 1 < n.
   Only-if part: ((n = 0) \/ (n = 1)) ==> (n <= SQRT n)
     This is to show:
     (1) 0 <= SQRT 0, true by SQRT 0 = 0          by SQRT_0
     (2) 1 <= SQRT 1, true by SQRT 1 = 1          by SQRT_1
*)
val SQRT_GE_SELF = store_thm(
  "SQRT_GE_SELF",
  ``!n. (n <= SQRT n) <=> ((n = 0) \/ (n = 1))``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `1 < n` by decide_tac >>
    `n ** 2 <= SQRT n ** 2` by rw[EXP_BASE_LE_MONO] >>
    `SQRT n ** 2 <= n` by rw[SQRT_PROPERTY] >>
    `n ** 2 <= n` by metis_tac[LESS_EQ_TRANS] >>
    `n * n <= n * 1` by metis_tac[EXP_2, MULT_RIGHT_1] >>
    `n <= 1` by metis_tac[LE_MULT_LCANCEL] >>
    decide_tac,
    rw[],
    rw[]
  ]);

(* Theorem: (SQRT n = n) <=> ((n = 0) \/ (n = 1)) *)
(* Proof: by ROOT_EQ_SELF, 0 < 2 *)
val SQRT_EQ_SELF = store_thm(
  "SQRT_EQ_SELF",
  ``!n. (SQRT n = n) <=> ((n = 0) \/ (n = 1))``,
  rw[ROOT_EQ_SELF]);

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

(* Theorem: SQRT n < m ==> n < m ** 2 *)
(* Proof:
                     SQRT n < m
   ==>        SUC (SQRT n) <= m                by arithmetic
   ==> (SUC (SQRT m)) ** 2 <= m ** 2           by EXP_EXP_LE_MONO
   But n < (SUC (SQRT n)) ** 2                 by SQRT_PROPERTY
   Thus n < m ** 2                             by inequality
*)
Theorem SQRT_LT_IMP:
  !n m. SQRT n < m ==> n < m ** 2
Proof
  rpt strip_tac >>
  `SUC (SQRT n) <= m` by decide_tac >>
  `SUC (SQRT n) ** 2 <= m ** 2` by simp[EXP_EXP_LE_MONO] >>
  `n < SUC (SQRT n) ** 2` by simp[SQRT_PROPERTY] >>
  decide_tac
QED

(* Theorem: n < SQRT m ==> n ** 2 < m *)
(* Proof:
                   n < SQRT m
   ==>        n ** 2 < (SQRT m) ** 2           by EXP_EXP_LT_MONO
   But        (SQRT m) ** 2 <= m               by SQRT_PROPERTY
   Thus       n ** 2 < m                       by inequality
*)
Theorem LT_SQRT_IMP:
  !n m. n < SQRT m ==> n ** 2 < m
Proof
  rpt strip_tac >>
  `n ** 2 < (SQRT m) ** 2` by simp[EXP_EXP_LT_MONO] >>
  `(SQRT m) ** 2 <= m` by simp[SQRT_PROPERTY] >>
  decide_tac
QED

(* Theorem: SQRT n < SQRT m ==> n < m *)
(* Proof:
       SQRT n < SQRT m
   ==>      n < (SQRT m) ** 2      by SQRT_LT_IMP
   and (SQRT m) ** 2 <= m          by SQRT_PROPERTY
    so      n < m                  by inequality
*)
Theorem SQRT_LT_SQRT:
  !n m. SQRT n < SQRT m ==> n < m
Proof
  rpt strip_tac >>
  imp_res_tac SQRT_LT_IMP >>
  `(SQRT m) ** 2 <= m` by simp[SQRT_PROPERTY] >>
  decide_tac
QED

(* Non-theorems:
   SQRT n <= SQRT m ==> n <= m
   counter-example: SQRT 5 = 2 = SQRT 4, but 5 > 4.

   n < m ==> SQRT n < SQRT m
   counter-example: 4 < 5, but SQRT 4 = 2 = SQRT 5.
*)

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

(* ------------------------------------------------------------------------- *)
(* Logarithm                                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < a ==> LOG a (a ** n) = n *)
(* Proof:
     LOG a (a ** n)
   = LOG a ((a ** n) * 1)     by MULT_RIGHT_1
   = n + LOG a 1              by LOG_EXP
   = n + 0                    by LOG_1
   = n                        by ADD_0
*)
val LOG_EXACT_EXP = store_thm(
  "LOG_EXACT_EXP",
  ``!a. 1 < a ==> !n. LOG a (a ** n) = n``,
  metis_tac[MULT_RIGHT_1, LOG_EXP, LOG_1, ADD_0, DECIDE``0 < 1``]);

(* Theorem: 1 < a /\ 0 < b /\ b <= a ** n ==> LOG a b <= n *)
(* Proof:
   Given     b <= a ** n
       LOG a b <= LOG a (a ** n)   by LOG_LE_MONO
                = n                by LOG_EXACT_EXP
*)
val EXP_TO_LOG = store_thm(
  "EXP_TO_LOG",
  ``!a b n. 1 < a /\ 0 < b /\ b <= a ** n ==> LOG a b <= n``,
  metis_tac[LOG_LE_MONO, LOG_EXACT_EXP]);

(* Theorem: 1 < a /\ 0 < n ==> !p. (LOG a n = p) <=> (a ** p <= n /\ n < a ** SUC p) *)
(* Proof:
   If part: 1 < a /\ 0 < n ==> a ** LOG a n <= n /\ n < a ** SUC (LOG a n)
      This is true by LOG.
   Only-if part: a ** p <= n /\ n < a ** SUC p ==> LOG a n = p
      This is true by LOG_UNIQUE
*)
val LOG_THM = store_thm(
  "LOG_THM",
  ``!a n. 1 < a /\ 0 < n ==> !p. (LOG a n = p) <=> (a ** p <= n /\ n < a ** SUC p)``,
  metis_tac[LOG, LOG_UNIQUE]);

(* Theorem: LOG m n = if m <= 1 \/ (n = 0) then LOG m n
            else if n < m then 0 else SUC (LOG m (n DIV m)) *)
(* Proof: by LOG_RWT *)
val LOG_EVAL = store_thm(
  "LOG_EVAL[compute]",
  ``!m n. LOG m n = if m <= 1 \/ (n = 0) then LOG m n
         else if n < m then 0 else SUC (LOG m (n DIV m))``,
  rw[LOG_RWT]);
(* Put to computeLib for LOG evaluation of any base *)

(*
> EVAL ``MAP (LOG 3) [1 .. 20]``; =
      [0; 0; 1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2]: thm
> EVAL ``MAP (LOG 3) [1 .. 30]``; =
      [0; 0; 1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 3; 3; 3; 3]: thm
*)

(* Theorem: 1 < a /\ 0 < n ==>
           !p. (LOG a n = p) <=> SUC n <= a ** SUC p /\ a ** SUC p <= a * n *)
(* Proof:
   Note !p. LOG a n = p
        <=> n < a ** SUC p /\ a ** p <= n                by LOG_THM
        <=> n < a ** SUC p /\ a * a ** p <= a * n        by LE_MULT_LCANCEL
        <=> n < a ** SUC p /\ a ** SUC p <= a * n        by EXP
        <=> SUC n <= a ** SUC p /\ a ** SUC p <= a * n   by arithmetic
*)
val LOG_TEST = store_thm(
  "LOG_TEST",
  ``!a n. 1 < a /\ 0 < n ==>
   !p. (LOG a n = p) <=> SUC n <= a ** SUC p /\ a ** SUC p <= a * n``,
  rw[EQ_IMP_THM] >| [
    `n < a ** SUC (LOG a n)` by metis_tac[LOG_THM] >>
    decide_tac,
    `a ** (LOG a n) <= n` by metis_tac[LOG_THM] >>
    rw[EXP],
    `a * a ** p <= a * n` by fs[EXP] >>
    `a ** p <= n` by fs[] >>
    `n < a ** SUC p` by decide_tac >>
    metis_tac[LOG_THM]
  ]);

(* For continuous functions, log_b (x ** y) = y * log_b x. *)

(* Theorem: 1 < b /\ 0 < x /\ 0 < n ==>
           n * LOG b x <= LOG b (x ** n) /\ LOG b (x ** n) < n * SUC (LOG b x) *)
(* Proof:
   Note:
> LOG_THM |> SPEC ``b:num`` |> SPEC ``x:num``;
val it = |- 1 < b /\ 0 < x ==> !p. LOG b x = p <=> b ** p <= x /\ x < b ** SUC p: thm
> LOG_THM |> SPEC ``b:num`` |> SPEC ``(x:num) ** n``;
val it = |- 1 < b /\ 0 < x ** n ==>
   !p. LOG b (x ** n) = p <=> b ** p <= x ** n /\ x ** n < b ** SUC p: thm

   Let y = LOG b x, z = LOG b (x ** n).
   Then b ** y <= x /\ x < b ** SUC y              by LOG_THM, (1)
    and b ** z <= x ** n /\ x ** n < b ** SUC z    by LOG_THM, (2)
   From (1),
        b ** (n * y) <= x ** n /\                  by EXP_EXP_LE_MONO, EXP_EXP_MULT
        x ** n < b ** (n * SUC y)                  by EXP_EXP_LT_MONO, EXP_EXP_MULT, 0 < n
   Cross combine with (2),
        b ** (n * y) <= x ** n < b ** SUC z
    and b ** z <= x ** n < b ** (n * y)
    ==> n * y < SUC z /\ z < n * SUC y             by EXP_BASE_LT_MONO
     or    n * y <= z /\ z < n * SUC y
*)
val LOG_POWER = store_thm(
  "LOG_POWER",
  ``!b x n. 1 < b /\ 0 < x /\ 0 < n ==>
           n * LOG b x <= LOG b (x ** n) /\ LOG b (x ** n) < n * SUC (LOG b x)``,
  ntac 4 strip_tac >>
  `0 < x ** n` by rw[] >>
  qabbrev_tac `y = LOG b x` >>
  qabbrev_tac `z = LOG b (x ** n)` >>
  `b ** y <= x /\ x < b ** SUC y` by metis_tac[LOG_THM] >>
  `b ** z <= x ** n /\ x ** n < b ** SUC z` by metis_tac[LOG_THM] >>
  `b ** (y * n) <= x ** n` by rw[EXP_EXP_MULT] >>
  `x ** n < b ** ((SUC y) * n)` by rw[EXP_EXP_MULT] >>
  `b ** (y * n) < b ** SUC z` by decide_tac >>
  `b ** z < b ** (SUC y * n)` by decide_tac >>
  `y * n < SUC z` by metis_tac[EXP_BASE_LT_MONO] >>
  `z < SUC y * n` by metis_tac[EXP_BASE_LT_MONO] >>
  decide_tac);

(* Theorem: 1 < a /\ 0 < n /\ a <= b ==> LOG b n <= LOG a n *)
(* Proof:
   Let x = LOG a n, y = LOG b n. To show: y <= x.
   By contradiction, suppose x < y.
   Then SUC x <= y.
   Note a ** x <= n /\ n < a ** SUC x     by LOG_THM
    and b ** y <= n /\ n < b ** SUC y     by LOG_THM
    But a <= b
        a ** SUC x
     <= b ** SUC x         by EXP_EXP_LE_MONO, 0 < SUC x
     <= b ** y             by EXP_BASE_LEQ_MONO_IMP, SUC x <= y
   This leads to n < a ** SUC x <= b ** y <= n, a contradiction.
*)
val LOG_LE_REVERSE = store_thm(
  "LOG_LE_REVERSE",
  ``!a b n. 1 < a /\ 0 < n /\ a <= b ==> LOG b n <= LOG a n``,
  rpt strip_tac >>
  qabbrev_tac `x = LOG a n` >>
  qabbrev_tac `y = LOG b n` >>
  spose_not_then strip_assume_tac >>
  `1 < b /\ SUC x <= y` by decide_tac >>
  `a ** x <= n /\ n < a ** SUC x` by metis_tac[LOG_THM] >>
  `b ** y <= n /\ n < b ** SUC y` by metis_tac[LOG_THM] >>
  `a ** SUC x <= b ** SUC x` by rw[EXP_EXP_LE_MONO] >>
  `b ** SUC x <= b ** y` by rw[EXP_BASE_LEQ_MONO_IMP] >>
  decide_tac);

(* Overload LOG base 2 *)
val _ = overload_on ("LOG2", ``\n. LOG 2 n``);

(* Theorem: LOG2 1 = 0 *)
(* Proof:
   LOG_1 |> SPEC ``2``;
   val it = |- 1 < 2 ==> LOG2 1 = 0: thm
*)
val LOG2_1 = store_thm(
  "LOG2_1[simp]",
  ``LOG2 1 = 0``,
  rw[LOG_1]);

(* Theorem: LOG2 2 = 1 *)
(* Proof:
   LOG_BASE |> SPEC ``2``;
   val it = |- 1 < 2 ==> LOG2 2 = 1: thm
*)
val LOG2_2 = store_thm(
  "LOG2_2[simp]",
  ``LOG2 2 = 1``,
  rw[LOG_BASE]);

(* Obtain a theorem *)
val LOG2_THM = save_thm("LOG2_THM",
    LOG_THM |> SPEC ``2`` |> SIMP_RULE (srw_ss())[]);
(* val LOG2_THM = |- !n. 0 < n ==> !p. (LOG2 n = p) <=> 2 ** p <= n /\ n < 2 ** SUC p: thm *)

(* Theorem: 0 < n ==> 2 ** LOG2 n <= n /\ n < 2 ** SUC (LOG2 n) *)
(* Proof:
   LOG |> SPEC ``2``;
   val it = |- !n. 1 < 2 /\ 0 < n ==> 2 ** LOG2 n <= n /\ n < 2 ** SUC (LOG2 n): thm
*)
val LOG2_PROPERTY = store_thm(
  "LOG2_PROPERTY",
  ``!n. 0 < n ==> 2 ** LOG2 n <= n /\ n < 2 ** SUC (LOG2 n)``,
  rw[LOG]);

(* Theorem: 0 < n ==> 2 ** LOG2 n <= n) *)
(* Proof: by LOG2_PROPERTY *)
val TWO_EXP_LOG2_LE = store_thm(
  "TWO_EXP_LOG2_LE",
  ``!n. 0 < n ==> 2 ** LOG2 n <= n``,
  rw[LOG2_PROPERTY]);

(* Obtain a theorem *)
val LOG2_UNIQUE = save_thm("LOG2_UNIQUE",
    LOG_UNIQUE |> SPEC ``2`` |> SPEC ``n:num`` |> SPEC ``m:num`` |> GEN_ALL);
(* val LOG2_UNIQUE = |- !n m. 2 ** m <= n /\ n < 2 ** SUC m ==> LOG2 n = m: thm *)

(* Theorem: 0 < n ==> ((LOG2 n = 0) <=> (n = 1)) *)
(* Proof:
   LOG_EQ_0 |> SPEC ``2``;
   |- !b. 1 < 2 /\ 0 < b ==> (LOG2 b = 0 <=> b < 2)
*)
val LOG2_EQ_0 = store_thm(
  "LOG2_EQ_0",
  ``!n. 0 < n ==> ((LOG2 n = 0) <=> (n = 1))``,
  rw[LOG_EQ_0]);

(* Theorem: 0 < n ==> LOG2 n = 1 <=> (n = 2) \/ (n = 3) *)
(* Proof:
   If part: LOG2 n = 1 ==> n = 2 \/ n = 3
      Note  2 ** 1 <= n /\ n < 2 ** SUC 1  by LOG2_PROPERTY
        or       2 <= n /\ n < 4           by arithmetic
      Thus  n = 2 or n = 3.
   Only-if part: LOG2 2 = 1 /\ LOG2 3 = 1
      Note LOG2 2 = 1                      by LOG2_2
       and LOG2 3 = 1                      by LOG2_UNIQUE
     since 2 ** 1 <= 3 /\ 3 < 2 ** SUC 1 ==> (LOG2 3 = 1)
*)
val LOG2_EQ_1 = store_thm(
  "LOG2_EQ_1",
  ``!n. 0 < n ==> ((LOG2 n = 1) <=> ((n = 2) \/ (n = 3)))``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    imp_res_tac LOG2_PROPERTY >>
    rfs[],
    rw[],
    irule LOG2_UNIQUE >>
    simp[]
  ]);

(* Obtain theorem *)
val LOG2_LE_MONO = save_thm("LOG2_LE_MONO",
    LOG_LE_MONO |> SPEC ``2`` |> SPEC ``n:num`` |> SPEC ``m:num``
                |> SIMP_RULE (srw_ss())[] |> GEN_ALL);
(* val LOG2_LE_MONO = |- !n m. 0 < n ==> n <= m ==> LOG2 n <= LOG2 m: thm *)

(* Theorem: 0 < n /\ n <= m ==> LOG2 n <= LOG2 m *)
(* Proof: by LOG_LE_MONO *)
val LOG2_LE = store_thm(
  "LOG2_LE",
  ``!n m. 0 < n /\ n <= m ==> LOG2 n <= LOG2 m``,
  rw[LOG_LE_MONO, DECIDE``1 < 2``]);

(* Note: next is not LOG2_LT_MONO! *)

(* Theorem: 0 < n /\ n < m ==> LOG2 n <= LOG2 m *)
(* Proof:
   Since n < m ==> n <= m   by LESS_IMP_LESS_OR_EQ
   This is true             by LOG_LE_MONO
*)
val LOG2_LT = store_thm(
  "LOG2_LT",
  ``!n m. 0 < n /\ n < m ==> LOG2 n <= LOG2 m``,
  rw[LOG_LE_MONO, LESS_IMP_LESS_OR_EQ, DECIDE``1 < 2``]);

(* Theorem: 0 < n ==> LOG2 n < n *)
(* Proof:
       LOG2 n
     < 2 ** (LOG2 n)     by X_LT_EXP_X, 1 < 2
    <= n                 by LOG2_PROPERTY, 0 < n
*)
val LOG2_LT_SELF = store_thm(
  "LOG2_LT_SELF",
  ``!n. 0 < n ==> LOG2 n < n``,
  rpt strip_tac >>
  `LOG2 n < 2 ** (LOG2 n)` by rw[X_LT_EXP_X] >>
  `2 ** LOG2 n <= n` by rw[LOG2_PROPERTY] >>
  decide_tac);

(* Theorem: 0 < n ==> LOG2 n <> n *)
(* Proof:
   Note n < LOG2 n     by LOG2_LT_SELF
   Thus n <> LOG2 n    by arithmetic
*)
val LOG2_NEQ_SELF = store_thm(
  "LOG2_NEQ_SELF",
  ``!n. 0 < n ==> LOG2 n <> n``,
  rpt strip_tac >>
  `LOG2 n < n` by rw[LOG2_LT_SELF] >>
  decide_tac);

(* Theorem: LOG2 n = n ==> n = 0 *)
(* Proof: by LOG2_NEQ_SELF *)
val LOG2_EQ_SELF = store_thm(
  "LOG2_EQ_SELF",
  ``!n. (LOG2 n = n) ==> (n = 0)``,
  metis_tac[LOG2_NEQ_SELF, DECIDE``~(0 < n) <=> (n = 0)``]);

(* Theorem: 1 < n ==> 0 < LOG2 n *)
(* Proof:
       1 < n
   ==> 2 <= n
   ==> LOG2 2 <= LOG2 n     by LOG2_LE
   ==>      1 <= LOG2 n     by LOG_BASE, LOG2 2 = 1
    or      0 < LOG2 n
*)
val LOG2_POS = store_thm(
  "LOG2_POS[simp]",
  ``!n. 1 < n ==> 0 < LOG2 n``,
  rpt strip_tac >>
  `LOG2 2 = 1` by rw[LOG_BASE, DECIDE``1 < 2``] >>
  `2 <= n` by decide_tac >>
  `LOG2 2 <= LOG2 n` by rw[LOG2_LE] >>
  decide_tac);

(* Theorem: 1 < n ==> 1 < 2 * LOG2 n *)
(* Proof:
       1 < n
   ==> 2 <= n
   ==> LOG2 2 <= LOG2 n        by LOG2_LE
   ==>      1 <= LOG2 n        by LOG_BASE, LOG2 2 = 1
   ==>  2 * 1 <= 2 * LOG2 n    by LE_MULT_LCANCEL
    or      1 < 2 * LOG2 n
*)
val LOG2_TWICE_LT = store_thm(
  "LOG2_TWICE_LT",
  ``!n. 1 < n ==> 1 < 2 * (LOG2 n)``,
  rpt strip_tac >>
  `LOG2 2 = 1` by rw[LOG_BASE, DECIDE``1 < 2``] >>
  `2 <= n` by decide_tac >>
  `LOG2 2 <= LOG2 n` by rw[LOG2_LE] >>
  `1 <= LOG2 n` by decide_tac >>
  `2 <= 2 * LOG2 n` by rw_tac arith_ss[LE_MULT_LCANCEL, DECIDE``0 < 2``] >>
  decide_tac);

(* Theorem: 1 < n ==> 4 <= (2 * (LOG2 n)) ** 2 *)
(* Proof:
       1 < n
   ==> 2 <= n
   ==> LOG2 2 <= LOG2 n              by LOG2_LE
   ==>      1 <= LOG2 n              by LOG2_2, or LOG_BASE, LOG2 2 = 1
   ==>  2 * 1 <= 2 * LOG2 n          by LE_MULT_LCANCEL
   ==> 2 ** 2 <= (2 * LOG2 n) ** 2   by EXP_EXP_LE_MONO
   ==>      4 <= (2 * LOG2 n) ** 2
*)
val LOG2_TWICE_SQ = store_thm(
  "LOG2_TWICE_SQ",
  ``!n. 1 < n ==> 4 <= (2 * (LOG2 n)) ** 2``,
  rpt strip_tac >>
  `LOG2 2 = 1` by rw[] >>
  `2 <= n` by decide_tac >>
  `LOG2 2 <= LOG2 n` by rw[LOG2_LE] >>
  `1 <= LOG2 n` by decide_tac >>
  `2 <= 2 * LOG2 n` by rw_tac arith_ss[LE_MULT_LCANCEL, DECIDE``0 < 2``] >>
  `2 ** 2 <= (2 * LOG2 n) ** 2` by rw[EXP_EXP_LE_MONO, DECIDE``0 < 2``] >>
  `2 ** 2 = 4` by rw_tac arith_ss[] >>
  decide_tac);

(* Theorem: 0 < n ==> 4 <= (2 * SUC (LOG2 n)) ** 2 *)
(* Proof:
       0 < n
   ==> 1 <= n
   ==> LOG2 1 <= LOG2 n                    by LOG2_LE
   ==>      0 <= LOG2 n                    by LOG2_1, or LOG_BASE, LOG2 1 = 0
   ==>      1 <= SUC (LOG2 n)              by LESS_EQ_MONO
   ==>  2 * 1 <= 2 * SUC (LOG2 n)          by LE_MULT_LCANCEL
   ==> 2 ** 2 <= (2 * SUC (LOG2 n)) ** 2   by EXP_EXP_LE_MONO
   ==>      4 <= (2 * SUC (LOG2 n)) ** 2
*)
val LOG2_SUC_TWICE_SQ = store_thm(
  "LOG2_SUC_TWICE_SQ",
  ``!n. 0 < n ==> 4 <= (2 * SUC (LOG2 n)) ** 2``,
  rpt strip_tac >>
  `LOG2 1 = 0` by rw[] >>
  `1 <= n` by decide_tac >>
  `LOG2 1 <= LOG2 n` by rw[LOG2_LE] >>
  `1 <= SUC (LOG2 n)` by decide_tac >>
  `2 <= 2 * SUC (LOG2 n)` by rw_tac arith_ss[LE_MULT_LCANCEL, DECIDE``0 < 2``] >>
  `2 ** 2 <= (2 * SUC (LOG2 n)) ** 2` by rw[EXP_EXP_LE_MONO, DECIDE``0 < 2``] >>
  `2 ** 2 = 4` by rw_tac arith_ss[] >>
  decide_tac);

(* Theorem: 1 < n ==> 1 < (SUC (LOG2 n)) ** 2 *)
(* Proof:
   Note 0 < LOG2 n                 by LOG2_POS, 1 < n
     so 1 < SUC (LOG2 n)           by arithmetic
    ==> 1 < (SUC (LOG2 n)) ** 2    by ONE_LT_EXP, 0 < 2
*)
val LOG2_SUC_SQ = store_thm(
  "LOG2_SUC_SQ",
  ``!n. 1 < n ==> 1 < (SUC (LOG2 n)) ** 2``,
  rpt strip_tac >>
  `0 < LOG2 n` by rw[] >>
  `1 < SUC (LOG2 n)` by decide_tac >>
  rw[ONE_LT_EXP]);

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

(* Theorem: LOG2 (2 ** n) = n *)
(* Proof: by LOG_EXACT_EXP *)
val LOG2_2_EXP = store_thm(
  "LOG2_2_EXP",
  ``!n. LOG2 (2 ** n) = n``,
  rw[LOG_EXACT_EXP]);

(* Theorem: (2 ** (LOG2 n) = n) <=> ?k. n = 2 ** k *)
(* Proof:
   If part: 2 ** LOG2 n = n ==> ?k. n = 2 ** k
      True by taking k = LOG2 n.
   Only-if part: 2 ** LOG2 (2 ** k) = 2 ** k
      Note LOG2 n = k               by LOG_EXACT_EXP, 1 < 2
        or n = 2 ** k = 2 ** LOG2 n.
*)
val LOG2_EXACT_EXP = store_thm(
  "LOG2_EXACT_EXP",
  ``!n. (2 ** (LOG2 n) = n) <=> ?k. n = 2 ** k``,
  metis_tac[LOG2_2_EXP]);

(* Theorem: 0 < n ==> LOG2 (n * 2 ** m) = (LOG2 n) + m *)
(* Proof:
   LOG_EXP |> SPEC ``m:num`` |> SPEC ``2`` |> SPEC ``n:num``;
   val it = |- 1 < 2 /\ 0 < n ==> LOG2 (2 ** m * n) = m + LOG2 n: thm
*)
val LOG2_MULT_EXP = store_thm(
  "LOG2_MULT_EXP",
  ``!n m. 0 < n ==> (LOG2 (n * 2 ** m) = (LOG2 n) + m)``,
  rw[GSYM LOG_EXP]);

(* Theorem: 0 < n ==> (LOG2 (2 * n) = 1 + LOG2 n) *)
(* Proof:
   LOG_MULT |> SPEC ``2`` |> SPEC ``n:num``;
   val it = |- 1 < 2 /\ 0 < n ==> LOG2 (TWICE n) = SUC (LOG2 n): thm
*)
val LOG2_TWICE = store_thm(
  "LOG2_TWICE",
  ``!n. 0 < n ==> (LOG2 (2 * n) = 1 + LOG2 n)``,
  rw[LOG_MULT]);

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

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
