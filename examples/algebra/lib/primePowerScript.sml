(* ------------------------------------------------------------------------- *)
(* Prime Power                                                               *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "primePower";

(* ------------------------------------------------------------------------- *)



(* val _ = load "jcLib"; *)
open jcLib;

(* val _ = load "SatisfySimps"; (* for SatisfySimps.SATISFY_ss *) *)

(* Get dependent theories in lib *)
(* val _ = load "logPowerTheory"; *)
open helperNumTheory;
open helperSetTheory;
open helperFunctionTheory;
open logPowerTheory;

(* val _ = load "triangleTheory"; *)
open triangleTheory; (* for list_lcm, set_lcm *)
open helperListTheory;
open listRangeTheory;
open rich_listTheory;

(* open dependent theories *)
open arithmeticTheory pred_setTheory listTheory;

(* open dependent theories *)
(* (* val _ = load "dividesTheory"; -- in helperNumTheory *) *)
(* (* val _ = load "gcdTheory"; -- in helperNumTheory *) *)
open dividesTheory gcdTheory;

open EulerTheory; (* for natural_finite *)
open logrootTheory; (* for LOG *)
open optionTheory; (* for Consecutive LCM Function *)


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


(* Note: prime: num -> bool is also a set, so prime = {p | prime p} *)

(* Theorem: prime_divisors 0 = prime *)
(* Proof: by prime_divisors_def, ALL_DIVIDES_0 *)
val prime_divisors_0 = store_thm(
  "prime_divisors_0",
  ``prime_divisors 0 = prime``,
  rw[prime_divisors_def, EXTENSION, IN_DEF]);

(* Theorem: prime_divisors 0 = {p | prime p} *)
(* Proof: by prime_divisors_def, ALL_DIVIDES_0 *)
val prime_divisors_0 = store_thm(
  "prime_divisors_0",
  ``prime_divisors 0 = {p | prime p}``,
  rw[prime_divisors_def]);

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

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
